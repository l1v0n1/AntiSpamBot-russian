#!/usr/bin/env python3
# -*- coding: utf-8 -*-
from typing import List, Any, Callable, Tuple, Set

from config import (SALT, WORKERS, AT_ADMINS_RATELIMIT, STORE_CHAT_MESSAGES,
                    GARBAGE_COLLECTION_INTERVAL, PICKLE_FILE, PERMIT_RELOAD,
                    USER_BOT_BACKEND, DEBUG)
from chatsettings import CHAT_SETTINGS as CHAT_SETTINGS_DEFAULT, CHAT_SETTINGS_HELP
from importlib import reload
import userfilter
assert not [k for k in CHAT_SETTINGS_DEFAULT if k not in CHAT_SETTINGS_HELP]

import logging
from ratelimited import mqbot
from telegram import Update, User, Bot, Message
from telegram.ext import CallbackContext, Job, PicklePersistence

from telegram import InlineKeyboardMarkup, InlineKeyboardButton
from telegram.ext import (Updater, CommandHandler, MessageHandler, Filters,
                          CallbackQueryHandler, run_async)
from telegram.ext.filters import InvertedFilter

from datetime import datetime, timedelta
from time import time
from telegram.error import (TelegramError, Unauthorized, BadRequest,
                            TimedOut, ChatMigrated, NetworkError)

from mwt import MWT
from utils import print_traceback, find_cjk_letters
from random import choice, randint, shuffle
from hashlib import md5, sha256
from threading import Lock


logging.basicConfig(level=logging.INFO,format='%(asctime)s - %(name)s - %(levelname)s - %(message)s')
logger = logging.getLogger('antispambot')

import subprocess
def get_gitver() -> str:
    try:
        p = subprocess.run(['git', 'describe', '--tags'],
                        env={"LANG": "C"},
                        stdin=subprocess.DEVNULL,
                        stdout=subprocess.PIPE,
                        stderr=subprocess.DEVNULL,
                        encoding='utf-8')
        assert p.returncode == 0
        ver: str = p.stdout.strip()
    except Exception:
        ver: str = "Unknown"
    return ver
VER: str = get_gitver()

def error_callback(update: Update, context:CallbackContext) -> None:
    error: Exception = context.error
    try:
        raise error
    except Exception:
        print_traceback(debug=DEBUG)

def collect_error(func: Callable) -> Callable:
    '''
        designed to fix a bug in the telegram library
    '''
    def wrapped(*args, **kwargs):
        try:
            return func(*args, **kwargs)
        except Exception:
            print_traceback(debug=DEBUG)
    return wrapped

def filter_old_updates(func: Callable[[Update, CallbackContext], Callable]) -> Callable:
    '''
        do not process very old updates
    '''
    def wrapped(update: Update, context: CallbackContext, *args, **kwargs) -> Any:
        msg: Message = update.effective_message
        sent_time: datetime = msg.edit_date if msg.edit_date else msg.date
        seconds_from_now: float = (datetime.now(tz=sent_time.tzinfo) - sent_time).total_seconds()
        if int(seconds_from_now) > 5*60:
            logger.warning(f'Not processing update {update.update_id} since it\'s too old ({int(seconds_from_now)}).')
            return
        else:
            return func(update, context, *args, **kwargs)
    return wrapped


def fName(user: User, atuser: bool = True, markdown: bool = True) -> str:
    name: str = user.full_name
    if markdown:
        mdtext: str = user.mention_markdown(name=user.full_name)
        return mdtext
    elif user.username:
        if atuser:
            name += " (@{})".format(user.username)
        else:
            name += " ({})".format(user.username)
    return name

@MWT(timeout=60*60)
def getAdminIds(bot: Bot, chat_id: int) -> List[int]:
    admin_ids = list()
    for chat_member in bot.get_chat_administrators(chat_id):
        admin_ids.append(chat_member.user.id)
    return admin_ids

@MWT(timeout=60*60)
def getAdminUsernames(bot: Bot, chat_id: int, markdown: bool = False) -> List[str]:
    admins = list()
    for chat_member in bot.get_chat_administrators(chat_id):
        if markdown:
            if chat_member.user.id != bot.id:
                admins.append(chat_member.user.mention_markdown(name=chat_member.user.name))
        else:
            if chat_member.user.username and chat_member.user.username != bot.username:
                admins.append(chat_member.user.username)
    return admins

@run_async
@collect_error
@filter_old_updates
def start(update: Update, context: CallbackContext) -> None:
    logger.debug(f"Start from {update.message.from_user.id}")
    if update.message.chat.type == 'private' and update.effective_user.id in PERMIT_RELOAD:
        reload(userfilter)
        logger.info(f'[!] userfilter module reloaded by {update.effective_user.id}')
        update.message.reply_text('reloaded')
        return
    update.message.reply_text((f'Привет, {update.message.from_user.first_name}'
                                ', функции бота:\n'
                                '1. Новые пользователи должны пройти проверку за определенное время, '
                                'иначе они будут заблокированы.\n'
                                'Если пользователь был приглашен другим участником, то пригласивший '
                                'также может помочь с проверкой.\n'
                                '2. Новые боты должны быть подтверждены пользователем или администратором.\n'
                                '3. Защита от флуда: когда много пользователей присоединяются за короткое время, '
                                'бот отправляет минимум сообщений, чтобы не мешать общению.\n'
                                'Для работы бота добавьте его в группу, сделайте администратором '
                                'и предоставьте права на блокировку пользователей.\n\n'
                                'Администраторы могут использовать /settings для настройки.\n'
                                'Используйте /ban для блокировки пользователей.'))

@run_async
@collect_error
@filter_old_updates
def source(update: Update, context: CallbackContext) -> None:
    logger.debug(f"Source from {update.message.from_user.id}")
    update.message.reply_text(f'Исходный код: https://github.com/l1v0n1/AntiSpamBot-russian\nВерсия: {VER}')

class chatSettings:
    def __init__(self, datadict):
        self.__data = dict()
        for k in CHAT_SETTINGS_DEFAULT:
            d = datadict.get(k, None)
            self.__data[k] = d
    def get(self, name):
        if name in CHAT_SETTINGS_DEFAULT:
            ret = self.__data.get(name, None)
            if ret is None:
                return CHAT_SETTINGS_DEFAULT[name]
            else:
                return ret
    def choice(self, name):
        data = self.get(name)
        if type(data) is list:
            return choice(data)
    def get_clg_accecpt_deny(self):
        l = self.choice('CLG_QUESTIONS')
        if l is None:
            # Возвращаем значение по умолчанию, если нет вопросов
            default_question = CHAT_SETTINGS_DEFAULT['CLG_QUESTIONS'][0]
            return (default_question[0], default_question[1], default_question[2:])
        return (l[0], l[1], l[2:])
    def __process(self, name: str, inputstr: str) -> str:
        if name == 'WELCOME_WORDS':
            uinput = [l[:4000] for l in inputstr.split('\n') if l]
            self.__data[name] = uinput
        elif name == 'CLG_QUESTIONS':
            uinput = [l for l in inputstr.split('\n') if l]
            if len(uinput) < 3 or len(self.get(name)) >= 10:
                return False
            uinput[0] = uinput[0][:4000]
            uinput = uinput[:50+1]
            for i in range(1, len(uinput)):
                uinput[i] = uinput[i][:200]
            if not self.__data.get(name, None):
                self.__data[name] = CHAT_SETTINGS_DEFAULT[name].copy()
            self.__data[name].append(uinput)
        elif name in ('CHALLENGE_SUCCESS', 'PERMISSION_DENY'):
            uinput = [l[:30] for l in inputstr.split('\n') if l]
            self.__data[name] = uinput
        elif name in ('CHALLENGE_TIMEOUT', 'MIN_CLG_TIME', 'UNBAN_TIMEOUT', 'FLOOD_LIMIT'):
            try:
                seconds = int(inputstr)
                if name == 'CHALLENGE_TIMEOUT':
                    if seconds > 3600 or seconds < 1:
                        raise ValueError
                elif name == 'MIN_CLG_TIME':
                    if seconds < 0 or seconds > self.get('CHALLENGE_TIMEOUT'):
                        raise ValueError
                elif name == 'UNBAN_TIMEOUT':
                    if seconds > 86400 or seconds < 0:
                        seconds = 0
                elif name == 'FLOOD_LIMIT':
                    if seconds < 0 or seconds > 1000:
                        seconds = 1
                else:
                    raise NotImplementedError(f"{name} is unknown")
            except ValueError:
                return False
            else:
                self.__data[name] = seconds
        elif name in ('DEL_LEAVE_MSG', 'DEL_SERVICE_MSG'):
            self.__data[name] = not self.get(name)
        else:
            raise NotImplementedError(f"{name} is unknown")
        return name
    def delete_clg_question(self, index: int) -> Any:
        name = 'CLG_QUESTIONS'
        if not self.__data.get(name, None):
            self.__data[name] = CHAT_SETTINGS_DEFAULT[name].copy()
        if index >= 0 and len(self.__data[name]) > index and len(self.__data[name]) >= 2:
            return self.__data[name].pop(index)
        else:
            return False
    def put(self, name: str, inputstr: str) -> Any:
        if not inputstr:
            self.__data[name] = None
            return True
        elif name in CHAT_SETTINGS_DEFAULT:
            return self.__process(name, inputstr)
    def to_dict(self) -> dict:
        return self.__data

FLD_LOCKS = dict()
class restUser:
    def __init__(self, user_id: int, join_msgid: int, clg_msgid: int, uinvite_id: int, flooding: bool = False):
        self.user_id = user_id
        self.join_msgid = join_msgid
        self.clg_msgid = clg_msgid
        self.uinvite_id = uinvite_id
        self.flooding = flooding
        self.time = int(time())
class UserManager:
    def __init__(self, chat_id: int) -> None:
        self._cver = self.ver
        self._chat_id = chat_id
        self._nfusers = dict()
        self._fldusers = dict()

        self.fldmsg_id = None
        self.fldmsg_callbacks = [None, ]
    @property
    def ver(self):
        return '0.0.2'
    def add(self, ruser: restUser) -> None:
        if self._nfusers.pop(ruser.user_id, None):
            logger.debug(f'User {ruser.user_id} is already in nfusers, chat {self._chat_id}')
        if self._fldusers.pop(ruser.user_id, None):
            logger.debug(f'User {ruser.user_id} is already in fldusers, chat {self._chat_id}')
        if ruser.flooding:
            self._fldusers[ruser.user_id] = ruser
        else:
            self._nfusers[ruser.user_id] = ruser
    def get(self, user_id: int) -> restUser:
        return self.__get_pop(0, user_id)
    def pop(self, user_id: int) -> restUser:
        return self.__get_pop(1, user_id)
    def __len__(self):
        return len(self._nfusers) + len(self._fldusers)
    def __get_pop(self, action: int, user_id: int) -> restUser:
        us = (self._fldusers, self._nfusers)
        if action == 0:
            for u in us:
                if (ret := u.get(user_id, None)):
                    return ret
        elif action == 1:
            for u in us:
                if (ret := u.pop(user_id, None)):
                    return ret
        return None

def challenge_gen_pw(user_id: int, join_msgid: int, real: bool = True) -> str:
    if real:
        action = 'pass'
    else:
        action = str(time())
    pw = "{}{}{}{}".format(SALT, user_id, join_msgid, action)
    pw_sha256 = sha256(pw.encode('utf-8', errors='ignore')).hexdigest()
    pw_sha256_md5 = md5(pw_sha256.encode('utf-8', errors='ignore')).hexdigest()
    # telegram limits callback_data to 64 bytes max, we need to be brief
    callback = pw_sha256_md5[:8]
    return callback

def challange_hash(user_id: int, chat_id: int, join_msgid: int) -> str:
    hashes = [str(hash(str(i))) for i in (user_id, chat_id, join_msgid)]
    identity = hash(''.join(hashes))
    return str(identity)

@run_async
@collect_error
def ban_user(update: Update, context: CallbackContext) -> None:
    if not update.message:
        return
    if update.effective_chat.type in ('private', 'channel'):
        return
    if update.message.from_user.id not in getAdminIds(context.bot, update.message.chat.id):
        return
    if not (repl_msg := update.message.reply_to_message):
        update.message.reply_text("Пожалуйста, ответьте на сообщение пользователя.")
        return
    if repl_msg.new_chat_members:
        user_ids = [user.id for user in repl_msg.new_chat_members]
    else:
        if repl_msg.from_user.id == context.bot.id:
            # trying to be user friendly but reqiures a lot more code :(
            try:
                assert (rmarkup := repl_msg.reply_markup) and (kbd := rmarkup.inline_keyboard) \
                    and type((btn := kbd[0][0])) is InlineKeyboardButton and (data := btn.callback_data)
                assert data.startswith('clg ')
                data = data.split(' ')
                if not len(data) in (3,4):
                    raise RuntimeError
                user_ids = [int(data[1]),]
            except AssertionError:
                user_ids = list()
            except Exception:
                user_ids = list()
                print_traceback(debug=DEBUG)
        else:
            user_ids = [repl_msg.from_user.id,]
    chat_id: int = update.message.chat.id
    user_ids: List[int] = [uid for uid in user_ids if uid not in getAdminIds(context.bot, chat_id)]
    if not user_ids:
        update.message.reply_text("Невозможно заблокировать администратора.")
        return
    u_mgr: UserManager = context.chat_data.setdefault('u_mgr', UserManager(chat_id))
    fldlock: Lock = FLD_LOCKS.setdefault(chat_id, Lock())
    for user_id in user_ids:
        rest_user = u_mgr.get(user_id)
        if not rest_user:
            # The user has no pending challenge
            kick_user(context, chat_id, user_id, reason="explicitly kicked")
            sto_msgs: List[Tuple[int, int, int]] = context.chat_data.get('stored_messages', list())
            msgids_to_delete: Set[int] = set([u_m_t[1] for u_m_t in sto_msgs if u_m_t[0] == user_id])
            msgids_to_delete.add(repl_msg.message_id)
            for _mid in msgids_to_delete:
                delete_message(context, chat_id, _mid)
        else:
            # Remove old job first, then take action
            mjobs: tuple = context.job_queue.get_jobs_by_name(challange_hash(rest_user.user_id, chat_id, rest_user.join_msgid))
            if len(mjobs) == 1:
                mjob: Job = mjobs[0]
                mjob.schedule_removal()
            else:
                for mjob in mjobs:
                    mjob.schedule_removal()
                logger.error(f'There is {len(mjobs)} pending job(s) for {rest_user.user_id} in the group {chat_id}')
                if DEBUG:
                    try:
                        raise Exception
                    except Exception:
                        print_traceback(debug=DEBUG)
            # ban user
            kick_user(context, chat_id, user_id, reason="explicitly kicked before challenge")
            # delete join msg and challenge message
            u_mgr.pop(rest_user.user_id)
            if rest_user.flooding:
                fldlock.acquire()
                try:
                    if len(u_mgr._fldusers) == 0 and u_mgr.fldmsg_id:
                        delete_message(context, chat_id=chat_id, message_id=u_mgr.fldmsg_id)
                        u_mgr.fldmsg_id = None
                finally:
                    fldlock.release()
            else:
                delete_message(context, chat_id=chat_id, message_id=rest_user.clg_msgid)
            delete_message(context, chat_id=chat_id, message_id=rest_user.join_msgid)
    def delete_notice(_: CallbackContext) -> None:
        delete_message(context, chat_id=chat_id, message_id=update.message.message_id)
    context.job_queue.run_once(delete_notice, 2)

@run_async
@collect_error
def challenge_verification(update: Update, context: CallbackContext) -> None:
    bot: Bot = context.bot
    chat_id: int = update.callback_query.message.chat.id
    user: User = update.callback_query.from_user
    message_id: int = update.callback_query.message.message_id
    data: str = update.callback_query.data
    fldlock: Lock = FLD_LOCKS.setdefault(chat_id, Lock())
    u_mgr: UserManager = context.chat_data.setdefault('u_mgr', UserManager(chat_id))
    settings = chatSettings(context.chat_data.get('chat_settings', dict()))
    if not data:
        logger.error('Empty Inline challenge data.')
        return
    args: List[str] = data.split()
    if args and len(args) == 3:
        args.append('')
    if not (args and len(args) == 4):
        logger.error(f'Wrong Inline challenge data length. {data}')
        return
    (btn_callback, invite_ruid) = args[2:] # args: ['clg', r_user_id, btn_callback, invite_ruid]
    # invite_ruid is '' if the restricted user is not a bot
    if invite_ruid:
        try:
            r_user_id = int(invite_ruid)
        except ValueError:
            logger.error(f'Bad invite_uid, {data}')
            bot.answer_callback_query(callback_query_id=update.callback_query.id, text="Fail")
            return
    else:
        r_user_id = user.id
    rest_user: restUser = u_mgr.get(r_user_id)

    naughty_user: bool = False
    flooding: bool = False
    wrong_captcha: bool = False

    if not rest_user:
        naughty_user = True
    else:
        if invite_ruid:
            if not rest_user.flooding:
                flooding = False
            else:
                wrong_captcha = True # ??
        else:
            if rest_user.flooding:
                flooding = True
            else:
                wrong_captcha = True

        if wrong_captcha:
            bot.answer_callback_query(callback_query_id=update.callback_query.id, text="Not your captcha")
            return

        if flooding:
            naughty_user = False
        else:
            if user.id in (rest_user.uinvite_id, rest_user.user_id, *(adminids := getAdminIds(bot, chat_id))):
                naughty_user = False
            else:
                naughty_user = True

    if not naughty_user:
        # Remove old job first, then take action
        if settings.get('CHALLENGE_TIMEOUT') > 0:
            mjobs: tuple = context.job_queue.get_jobs_by_name(challange_hash(rest_user.user_id, chat_id, rest_user.join_msgid))
            if len(mjobs) == 1:
                mjob: Job = mjobs[0]
                mjob.schedule_removal()
            else:
                for mjob in mjobs:
                    mjob.schedule_removal()
                logger.error(f'There is {len(mjobs)} pending job(s) for {rest_user.user_id} in the group {chat_id}')
                if DEBUG:
                    try:
                        raise Exception
                    except Exception:
                        print_traceback(debug=DEBUG)

        # whether the captcha is correct or not
        if data == u_mgr.fldmsg_callbacks[0]:
            captcha_corrent = True
        elif not flooding and btn_callback == challenge_gen_pw(rest_user.user_id, rest_user.join_msgid):
            captcha_corrent = True
        else:
            captcha_corrent = False

        if not captcha_corrent:
            if (kick_by_admin := not flooding and user.id in adminids):
                bot.answer_callback_query(callback_query_id=update.callback_query.id,
                                          text=f'Banned for {UNBAN_TIMEOUT} seconds' \
                                            if (UNBAN_TIMEOUT := settings.get('UNBAN_TIMEOUT')) > 0 else \
                                            'Banned permanently',
                                          show_alert=True)
            kick_user(context, chat_id, r_user_id, 'Kicked by admin' if kick_by_admin else 'Challange failed')
            def then_unban(_: CallbackContext) -> None:
                unban_user(context, chat_id, r_user_id, reason='Unban timeout reached.')
            if (UNBAN_TIMEOUT := settings.get('UNBAN_TIMEOUT')) > 0:
                context.job_queue.run_once(then_unban, UNBAN_TIMEOUT, name='unban_job')
        else:
            unban_user(context, chat_id, r_user_id, reason='Challenge passed.')
            bot.answer_callback_query(callback_query_id=update.callback_query.id,
                                      text=settings.choice('CHALLENGE_SUCCESS'),
                                      show_alert=True)
        # delete messages
        u_mgr.pop(rest_user.user_id)
        if flooding:
            fldlock.acquire()
            try:
                if len(u_mgr._fldusers) == 0 and u_mgr.fldmsg_id:
                    delete_message(context, chat_id=chat_id, message_id=u_mgr.fldmsg_id)
                    u_mgr.fldmsg_id = None
            finally:
                fldlock.release()
        else:
            delete_message(context, chat_id=chat_id, message_id=message_id)
        if not captcha_corrent:
            delete_message(context, chat_id=chat_id, message_id=rest_user.join_msgid)

    else:
        logger.info((f"Naughty user {fName(user, markdown=False)} {user.id=} clicked a button"
                     f" from the group {chat_id}"))
        bot.answer_callback_query(callback_query_id=update.callback_query.id,
                                  text=settings.choice('PERMISSION_DENY'),
                                  show_alert=True)

def simple_challenge(context, chat_id, user, invite_user, join_msgid) -> None:
    bot: Bot = context.bot
    fldlock: Lock = FLD_LOCKS.setdefault(chat_id, Lock())
    u_mgr: UserManager = context.chat_data.setdefault('u_mgr', UserManager(chat_id))
    settings = chatSettings(context.chat_data.get('chat_settings', dict()))
    MIN_CLG_TIME = settings.get('MIN_CLG_TIME')
    CLG_TIMEOUT  = settings.get('CHALLENGE_TIMEOUT')
    try:
        RCLG_TIMEOUT = (lambda score: \
                        (userfilter.MAX_SCORE-score)/userfilter.MAX_SCORE*(CLG_TIMEOUT-MIN_CLG_TIME)+MIN_CLG_TIME) \
                       (userfilter.spam_score(user.full_name))
        RCLG_TIMEOUT = int(RCLG_TIMEOUT)
    except Exception:
        RCLG_TIMEOUT = CLG_TIMEOUT
        print_traceback(debug=DEBUG)
    (CLG_QUESTION, CLG_ACCEPT, CLG_DENY) = settings.get_clg_accecpt_deny()
    # flooding protection
    FLOOD_LIMIT = settings.get('FLOOD_LIMIT')
    if FLOOD_LIMIT == 0:
        flag_flooding = False
    elif FLOOD_LIMIT == 1:
        flag_flooding = True
    else:
        if len(u_mgr) + 1 >= FLOOD_LIMIT:
            flag_flooding = True
        else:
            flag_flooding = False
    flag_flooding = flag_flooding and not user.is_bot
    def organize_btns(buttons: List[InlineKeyboardButton]) -> List[List[InlineKeyboardButton]]:
        '''
            Shuffle buttons and put them into a 2d array
        '''
        shuffle(buttons)
        output = [list(),]
        LENGTH_PER_LINE = 20
        MAXIMUM_PER_LINE = 4
        clength = LENGTH_PER_LINE
        for btn in buttons:
            l = len(btn.text) + len(find_cjk_letters(btn.text)) # cjk letters has a length of 2
            clength -= l
            if clength < 0 or len(output[-1]) >= MAXIMUM_PER_LINE:
                clength = LENGTH_PER_LINE - l
                output.append([btn])
            else:
                output[-1].append(btn)
        return output
    try:
        if restrict_user(context, chat_id=chat_id, user_id=user.id, extra=((' [flooding]' if flag_flooding else '') + \
                                                                           (' [bot]' if user.is_bot else ''))):
            if flag_flooding:
                fldlock.acquire()
            try:
                if u_mgr.fldmsg_id and flag_flooding:
                    logger.debug(f'Deleting flooding captcha {u_mgr.fldmsg_id} in {chat_id}')
                    delete_message(context, chat_id, u_mgr.fldmsg_id)
                buttons = [
                    InlineKeyboardButton(text=CLG_ACCEPT, callback_data = (\
                        f"clg {user.id} {challenge_gen_pw(user.id, join_msgid)}" + \
                    (f" {user.id}" if not flag_flooding else ''))),
                    *[InlineKeyboardButton(text=fake_btn_text, callback_data = (\
                        f"clg {user.id} {challenge_gen_pw(user.id, join_msgid, real=False)}" + \
                    (f" {user.id}" if not flag_flooding else '')))
                    for fake_btn_text in CLG_DENY]
                ]
                callback_datalist = [btn.callback_data for btn in buttons]
                buttons = organize_btns(buttons)
                for _ in range(3):
                    try:
                        msg: Message = bot.send_message(chat_id=chat_id,
                                        reply_to_message_id=join_msgid,
                                        text=('' if not flag_flooding else \
                                                    f'Ожидающих проверки пользователей: {len(u_mgr)+1}\n') + \
                                                settings.choice('WELCOME_WORDS').replace(
                                                '%time%', f"{RCLG_TIMEOUT}") + \
                                                f"\n{CLG_QUESTION}",
                                        reply_markup=InlineKeyboardMarkup(buttons),
                                        disable_notification=True) # These messages are essential and should not be delayed.
                    except TelegramError:
                        pass
                    else:
                        break
                else:
                    raise TelegramError(f'Send challenge message failed 3 times for {user.id}')
                if flag_flooding:
                    u_mgr.fldmsg_id = msg.message_id
                    u_mgr.fldmsg_callbacks = callback_datalist
                bot_invite_uid = None if flag_flooding else invite_user.id
                u_mgr.add(restUser(user.id, join_msgid, msg.message_id, bot_invite_uid, flooding=flag_flooding))
            finally:
                if flag_flooding:
                    fldlock.release()
            # User restricted and buttons sent, now search for this user's previous messages and delete them
            sto_msgs: List[Tuple[int, int, int]] = context.chat_data.get('stored_messages', list())
            msgids_to_delete: Set[int] = set([u_m_t[1] for u_m_t in sto_msgs if u_m_t[0] == user.id and int(u_m_t[1]) > int(join_msgid)])
            for _mid in msgids_to_delete:
                delete_message(context, chat_id, _mid)
            # kick them after timeout
            def kick_then_unban(_: CallbackContext) -> None:
                def then_unban(_: CallbackContext) -> None:
                    unban_user(context, chat_id, user.id, reason='Unban timeout reached.')
                if kick_user(context, chat_id, user.id, reason='Challange timeout.'):
                    if (UNBAN_TIMEOUT := settings.get('UNBAN_TIMEOUT')) > 0:
                        context.job_queue.run_once(then_unban, UNBAN_TIMEOUT, name='unban_job')
                u_mgr.pop(user.id)
                # delete messages
                if flag_flooding:
                    fldlock.acquire()
                    try:
                        if len(u_mgr) == 0 and u_mgr.fldmsg_id:
                            delete_message(context, chat_id=chat_id, message_id=u_mgr.fldmsg_id)
                            u_mgr.fldmsg_id = None
                    finally:
                        fldlock.release()
                else:
                    delete_message(context, chat_id=chat_id, message_id=msg.message_id)
                delete_message(context, chat_id=chat_id, message_id=join_msgid)
            context.job_queue.run_once(kick_then_unban, RCLG_TIMEOUT if RCLG_TIMEOUT > 0 else 0,
                                       name=challange_hash(user.id, chat_id, join_msgid))
        else:
            raise TelegramError('')
    except TelegramError:
        bot.send_message(chat_id=chat_id,
                text="Обнаружен новый участник: {0}, но бот не является администратором и не может выполнить необходимые действия. "
                     "Пожалуйста, назначьте бота администратором и предоставьте права на блокировку пользователей.".format(fName(user, markdown=True)),
                parse_mode="Markdown")
        logger.error((f"Cannot restrict {user.id} and {invite_user.id} in "
                      f"the group {chat_id}{' [bot]' if user.is_bot else ''}"))


@run_async
@collect_error
@filter_old_updates
def at_admins(update: Update, context: CallbackContext) -> None:
    chat_type: str = update.message.chat.type
    if chat_type in ('private', 'channel'):
        return
    bot: Bot = context.bot
    chat_id: int = update.message.chat.id
    last_at_admins: float = context.chat_data.setdefault('last_at_admins', 0.0)
    if time() - last_at_admins < AT_ADMINS_RATELIMIT:
        notice: Message = update.message.reply_text(f"Пожалуйста, подождите {AT_ADMINS_RATELIMIT - (time() - last_at_admins): .3f} секунд")
        def delete_notice(_: CallbackContext) -> None:
            for _msg_id in (update.message.message_id, notice.message_id):
                delete_message(context, chat_id=chat_id, message_id=_msg_id)
            logger.debug((f"Deleted at_admin spam messages {update.message.message_id} and "
                          f"{notice.message_id} from {update.message.from_user.id}"))
        context.job_queue.run_once(delete_notice, 5)
    else:
        admins: List[str] = getAdminUsernames(bot, chat_id, markdown=True)
        if admins:
            update.message.reply_text("  ".join(admins), parse_mode='Markdown')
        context.chat_data["last_at_admins"]: float = time()
        logger.debug(f"At_admin sent from {update.message.from_user.id} {chat_id}")

def write_settings(update: Update, context: CallbackContext) -> None:
    settings_call = context.chat_data.get('settings_call', None)
    if settings_call is None:
        return
    if update.message.from_user.id not in getAdminIds(context.bot, update.message.chat_id):
        return
    try:
        lasttime = float(settings_call[0])
        caller_uid = int(settings_call[1])
        item = str(settings_call[2])
    except Exception:
        context.chat_data['settings_call'] = None
        return
    if caller_uid != update.message.from_user.id:
        return
    if time() - lasttime > 120.0:
        context.chat_data['settings_call'] = None
        return
    params = [line.strip() for line in update.message.text.split('\n') if line]
    if len(params) == 0:
        return
    if item not in CHAT_SETTINGS_DEFAULT:
        return
    settings = chatSettings(context.chat_data.get('chat_settings', dict()))
    ret = settings.put(item, '\n'.join(params))
    context.chat_data['settings_call'] = None
    if ret:
        settings_menu(update, context, additional_text="Настройки успешно сохранены\n\n")
        context.chat_data['chat_settings'] = settings.to_dict()
        ppersistence.flush()
    else:
        settings_menu(update, context, additional_text="Ваш ввод некорректен, попробуйте еще раз\n\n")

@run_async
@collect_error
@filter_old_updates
def settings_menu(update: Update, context: CallbackContext, additional_text: str = '') -> None:
    chat_type: str = update.message.chat.type
    if chat_type == 'channel':
        return
    elif chat_type == 'private':
        update.message.reply_text('Настройки доступны только в группах')
        return
    if update.message.from_user.id in getAdminIds(context.bot, update.message.chat.id):
        buttons = [
            [InlineKeyboardButton(text=CHAT_SETTINGS_HELP[item][0], callback_data = f"settings {item}")]
        for item in CHAT_SETTINGS_DEFAULT]
        update.message.reply_text(text=f"{additional_text}Выберите настройку",
                                  reply_markup=InlineKeyboardMarkup(buttons))

@run_async
@collect_error
@filter_old_updates
def settings_cancel(update: Update, context: CallbackContext) -> None:
    if update.message.from_user.id in getAdminIds(context.bot, update.message.chat.id):
        settings_call = context.chat_data.get('settings_call', None)
        if settings_call:
            context.chat_data['settings_call'] = None
            update.message.reply_text('Настройка отменена')
        else:
            update.message.reply_text('Нет активных настроек для отмены')

@run_async
@collect_error
def settings_callback(update: Update, context: CallbackContext) -> None:
    user: User = update.callback_query.from_user
    chat_id: int = update.callback_query.message.chat.id
    callback_answered: bool = False
    if user.id in getAdminIds(context.bot, chat_id):
        message: int = update.callback_query.message
        data: str = update.callback_query.data

        args: List[str] = data.split()
        if not args:
            return
        elif len(args) == 1:
            # show menu
            update.callback_query.answer()
            buttons = [
                [InlineKeyboardButton(text=CHAT_SETTINGS_HELP[item][0], callback_data = f"settings {item}")]
            for item in CHAT_SETTINGS_DEFAULT]
            message.edit_text(text="Выберите настройку",
                              reply_markup=InlineKeyboardMarkup(buttons))
            return
        elif len(args) not in (2, 3):
            logger.error(f'Wrong Inline settings data length. {data=}')
            update.callback_query.answer()
            return
        else:
            if args[1] not in CHAT_SETTINGS_DEFAULT:
                update.callback_query.answer(f'Unexpected {args[1]}')
                return
            item = args[1]
            setting_type: str = CHAT_SETTINGS_HELP.get(item)[2]
            settings = chatSettings(context.chat_data.get('chat_settings', dict()))
            helptext = f"Настройка: {CHAT_SETTINGS_HELP.get(item)[0]}\n"
            helptext += "Текущее значение: "
            current_value = settings.get(item)
            buttons = [[InlineKeyboardButton(text="Восстановить значение по умолчанию", callback_data = f"{' '.join(args[:2])} default")]]
            # handle default
            if len(args) == 3 and args[2] == 'default':
                callback_answered = True
                if settings.put(item, ''):
                    context.chat_data['chat_settings'] = settings.to_dict()
                    ppersistence.flush()
                    update.callback_query.answer('Успешно', show_alert=True)
                    # refresh
                    settings = chatSettings(context.chat_data.get('chat_settings', dict()))
                    current_value = settings.get(item)
                else:
                    update.callback_query.answer('Ошибка', show_alert=True)
            if setting_type == "array":
                assert item == 'CLG_QUESTIONS'
                # handle delete
                if len(args) == 3 and args[2] not in ('set', 'default'):
                    try:
                        index = int(args[2])
                    except ValueError:
                        logger.error(f'Unexpected CLG_QUESTIONS index {data=}')
                        return
                    callback_answered = True
                    if settings.delete_clg_question(index):
                        context.chat_data['chat_settings'] = settings.to_dict()
                        ppersistence.flush()
                        update.callback_query.answer('Успешно', show_alert=True)
                        # refresh
                        settings = chatSettings(context.chat_data.get('chat_settings', dict()))
                        current_value = settings.get(item)
                    else:
                        update.callback_query.answer('Ошибка', show_alert=True)
                if len(current_value) < 30:
                    buttons += [[InlineKeyboardButton(text="Добавить новый", callback_data = f"{' '.join(args[:2])} set")]]
                for i in range(len(current_value)):
                    name = current_value[i][0]
                    corr_answ = current_value[i][1]
                    fals_answ = current_value[i][2:]
                    if len(current_value) > 1:
                        buttons.append([InlineKeyboardButton(text=f"Удалить {i+1}:{name[:20]}",
                                                             callback_data = f"{' '.join(args[:2])} {i}")])
                    helptext += f"\nВопрос{i+1: >2d} :{name}\nПравильный ответ: {corr_answ}"
                    for f in fals_answ:
                        helptext += f"\nНеправильный ответ: {f}"
            elif setting_type == "bool":
                buttons += [[InlineKeyboardButton(text="Переключить", callback_data = f"{' '.join(args[:2])} set")]]
                helptext += f"\nСостояние: {'Включено' if current_value else 'Выключено'}"
            elif setting_type in ("str", "int"):
                buttons += [[InlineKeyboardButton(text="Изменить", callback_data = f"{' '.join(args[:2])} set")]]
                if type(current_value) is list:
                    current_value = '\n'.join([f"Вариант: {x}" for x in current_value])
                    helptext += '\n'
                helptext += str(current_value)
            else:
                raise RuntimeError("should not reach here")
            buttons.append(
                [InlineKeyboardButton(text='Назад', callback_data='settings')]
            )
            helptext += '\n\n'
            helptext += f"Описание:\n{CHAT_SETTINGS_HELP.get(item, [None, None])[1]}"
            if len(args) == 3 and args[2] == 'set':
                if setting_type == "bool":
                    callback_answered = True
                    if settings.put(item, 'dummy'):
                        context.chat_data['chat_settings'] = settings.to_dict()
                        ppersistence.flush()
                        update.callback_query.answer('Успешно', show_alert=True)
                        # refresh
                        settings = chatSettings(context.chat_data.get('chat_settings', dict()))
                        current_value = settings.get(item)
                        newhelptext = f"Состояние: {'Включено' if current_value else 'Выключено'}"
                        l_helptext = [newhelptext if line.startswith('Состояние:') else line for line in helptext.split('\n')]
                        helptext = '\n'.join(l_helptext)
                    else:
                        update.callback_query.answer('Ошибка', show_alert=True)
                    reply_markup = InlineKeyboardMarkup(buttons)
                else:
                    helptext += "\n\nВы настраиваете новое значение\nПожалуйста, введите корректное значение в течение 120 секунд. Для отмены введите /cancel."
                    context.chat_data['settings_call'] = [time(), user.id, item]
                    reply_markup = None
            else:
                reply_markup = InlineKeyboardMarkup(buttons)
            if not callback_answered:
                update.callback_query.answer()
            helptext = helptext[:4096]
            if message.text == helptext and message.reply_markup is not None and reply_markup is not None:
                if len(message.reply_markup.inline_keyboard) == len(reply_markup.inline_keyboard):
                    return
            message.edit_text(helptext, reply_markup=reply_markup)
    else:
        update.callback_query.answer()

@run_async
@collect_error
@filter_old_updates
def new_messages(update: Update, context: CallbackContext) -> None:
    if not (update.effective_user and update.effective_message and update.effective_message.chat):
        return
    chat_type: str = update.effective_message.chat.type
    if chat_type in ('private', 'channel'):
        return
    sto_msgs: List[Tuple[int, int, int]] = context.chat_data.setdefault('stored_messages', list())
    sto_msgs.append((update.effective_user.id, update.effective_message.message_id, int(time())))
    while len(sto_msgs) > STORE_CHAT_MESSAGES:
        sto_msgs.pop(0)
    if update.message and update.message.text:
        write_settings(update, context)

@run_async
@collect_error
@filter_old_updates
def left_member(update: Update, context: CallbackContext) -> None:
    if not (update.message and update.message.chat):
        return
    chat_type: str = update.message.chat.type
    if chat_type in ('private', 'channel'):
        return
    chat_id: int = update.message.chat_id
    msg_id: int = update.message.message_id
    settings = chatSettings(context.chat_data.get('chat_settings', dict()))
    DEL_LEAVE_MSG = settings.get('DEL_LEAVE_MSG')
    if DEL_LEAVE_MSG:
        logger.debug(f'Deleted left_member message {msg_id} for {chat_id}')
        delete_message(context, chat_id, msg_id)
    else:
        logger.debug(f'Not deleting left_member message {msg_id} for {chat_id}')

@run_async
@collect_error
@filter_old_updates
def new_members(update: Update, context: CallbackContext) -> None:
    if not (update.message and update.message.chat):
        return
    chat_type: str = update.message.chat.type
    if chat_type in ('private', 'channel'):
        return
    bot: Bot = context.bot
    chat_id: int = update.message.chat_id
    assert update.message.new_chat_members
    users: List[User] = update.message.new_chat_members
    invite_user: User = update.message.from_user
    for user in users:
        if user.id == bot.id:
            logger.info(f"Myself joined the group {chat_id}")
        else:
            logger.debug(f"{user.id} joined the group {chat_id}")
            if invite_user.id != user.id and invite_user.id in getAdminIds(bot, chat_id):
                # An admin invited him.
                logger.info((f"{'bot ' if user.is_bot else ''}{user.id} invited by admin "
                                f"{invite_user.id} into the group {chat_id}"))
            else:
                simple_challenge(context, chat_id, user, invite_user, update.effective_message.message_id)

def do_garbage_collection(context: CallbackContext) -> None:
    u_freed:   int = 0
    m_freed:   int = 0
    u_checked: int = 0
    m_checked: int = 0
    all_chat_data = updater.dispatcher.chat_data
    logger.debug('gc: check for abandoned keys')
    for chat_id in all_chat_data:
        for key in [k for k in all_chat_data[chat_id]]:
            if key in ('my_msg', 'rest_users'):
                d = all_chat_data[chat_id].pop(key, None)
                logger.warning(f'Update pickle: Removed {{{key}: {d}}} for {chat_id}')
    logger.debug('gc: reinit old versions of u_mgr')
    for chat_id in all_chat_data:
        u_mgr: UserManager = all_chat_data[chat_id].get('u_mgr', None)
        if u_mgr and u_mgr._cver != u_mgr.ver:
            all_chat_data[chat_id].pop('u_mgr', None)
            logger.warning(f'Update u_mgr: reinit {u_mgr._cver} to {u_mgr.ver} for {chat_id}')
            del u_mgr
    logger.debug('gc: check for outdated rest_users and sto_msgs')
    for chat_id in all_chat_data:
        u_mgr: UserManager = all_chat_data[chat_id].get('u_mgr', None)
        if u_mgr:
            for _ulist in (u_mgr._nfusers, u_mgr._fldusers):
                for k in (_culist := _ulist.copy()):
                    u_checked += 1
                    _u = _culist.get(k, None)
                    t = _u.time if _u else 0
                    if int(time()) - t > 7200:
                        _ulist.pop(k, None)
                        u_freed += 1
        sto_msgs: list = all_chat_data[chat_id].get('stored_messages', None)
        if type(sto_msgs) is list:
            to_rm = list()
            try:
                for item in sto_msgs:
                    m_checked += 1
                    if len(item) == 3:
                        stime = item[2]
                        if int(time()) - stime > 7200:
                            to_rm.append(item)
            except Exception:
                print_traceback(debug=DEBUG)
            for item in to_rm:
                m_freed += 1
                try:
                    sto_msgs.remove(item)
                except Exception:
                    print_traceback(debug=DEBUG)
    logger.info((f'Scheduled garbage collection checked {u_checked} users, {m_checked} messages, '
                 f'freed {u_freed} users, {m_freed} messages.'))

@run_async
@collect_error
@filter_old_updates
def service_message(update: Update, context: CallbackContext) -> None:
    """Обработчик всех системных сообщений."""
    if not (update.message and update.message.chat):
        return
    chat_type: str = update.message.chat.type
    if chat_type in ('private', 'channel'):
        return
    
    chat_id: int = update.message.chat_id
    msg_id: int = update.message.message_id
    settings = chatSettings(context.chat_data.get('chat_settings', dict()))
    
    # Проверяем настройку DEL_SERVICE_MSG
    if settings.get('DEL_SERVICE_MSG'):
        logger.debug(f'Deleted service message {msg_id} for {chat_id}')
        delete_message(context, chat_id, msg_id)
    else:
        logger.debug(f'Not deleting service message {msg_id} for {chat_id}')

if __name__ == '__main__':
    ppersistence = PicklePersistence(filename=PICKLE_FILE, store_user_data=False, on_flush=True)
    updater = Updater(bot=mqbot, workers=WORKERS, persistence=ppersistence, use_context=True)

    if USER_BOT_BACKEND:
        from userbot_backend import (kick_user, restrict_user, unban_user, delete_message,
                                     userbot_updater)
    else:
        from bot_backend import kick_user, restrict_user, unban_user, delete_message
    updater.job_queue.start()
    updater.job_queue.run_repeating(do_garbage_collection, GARBAGE_COLLECTION_INTERVAL, first=5)
    updater.dispatcher.add_error_handler(error_callback)
    updater.dispatcher.add_handler(CommandHandler('start', start))
    updater.dispatcher.add_handler(CommandHandler('source', source))
    updater.dispatcher.add_handler(CommandHandler('admins', at_admins))
    updater.dispatcher.add_handler(CommandHandler('admin', at_admins))
    updater.dispatcher.add_handler(CommandHandler('settings', settings_menu))
    updater.dispatcher.add_handler(CommandHandler('cancel', settings_cancel))
    updater.dispatcher.add_handler(CommandHandler('ban', ban_user))
    updater.dispatcher.add_handler(CallbackQueryHandler(challenge_verification, pattern=r'clg'))
    updater.dispatcher.add_handler(CallbackQueryHandler(settings_callback, pattern=r'settings'))
    
    # Обработчики системных сообщений
    updater.dispatcher.add_handler(MessageHandler(Filters.status_update.new_chat_members, new_members))
    updater.dispatcher.add_handler(MessageHandler(Filters.status_update.left_chat_member, left_member))
    
    # Новые обработчики для других системных сообщений
    updater.dispatcher.add_handler(MessageHandler(Filters.status_update.new_chat_title, service_message))
    updater.dispatcher.add_handler(MessageHandler(Filters.status_update.new_chat_photo, service_message))
    updater.dispatcher.add_handler(MessageHandler(Filters.status_update.delete_chat_photo, service_message))
    updater.dispatcher.add_handler(MessageHandler(Filters.status_update.pinned_message, service_message))
    updater.dispatcher.add_handler(MessageHandler(Filters.status_update.chat_created, service_message))
    updater.dispatcher.add_handler(MessageHandler(Filters.status_update.message_auto_delete_timer_changed, service_message))
    updater.dispatcher.add_handler(MessageHandler(Filters.status_update.connected_website, service_message))
    updater.dispatcher.add_handler(MessageHandler(Filters.status_update.proximity_alert_triggered, service_message))
    updater.dispatcher.add_handler(MessageHandler(Filters.status_update.migrate, service_message))
    updater.dispatcher.add_handler(MessageHandler(Filters.status_update.voice_chat_scheduled, service_message))
    updater.dispatcher.add_handler(MessageHandler(Filters.status_update.voice_chat_started, service_message))
    updater.dispatcher.add_handler(MessageHandler(Filters.status_update.voice_chat_ended, service_message))
    updater.dispatcher.add_handler(MessageHandler(Filters.status_update.voice_chat_participants_invited, service_message))
    
    # Обработчик обычных сообщений должен быть последним
    updater.dispatcher.add_handler(MessageHandler(InvertedFilter(Filters.status_update & \
                                                  Filters.update.channel_posts), new_messages))
    if USER_BOT_BACKEND:
        logger.info('Antispambot started with userbot backend.')
        try:
            userbot_updater.start()
            updater.start_polling()
            updater.idle()
        finally:
            userbot_updater.stop()
    else:
        logger.info('Antispambot started.')
        updater.start_polling()
        updater.idle()
