# These options can be changed per group
CHAT_SETTINGS = {
    'WELCOME_WORDS': [
        'Новый пользователь, пожалуйста, ответьте на следующий вопрос в течение %time% секунд',
    ],

    'CLG_QUESTIONS': [
        ['Какого цвета небо в ясный день?', 'голубое', 'красное', 'зеленое', 'черное', 'фиолетовое', 'желтое'],
        ['Сколько дней в неделе?', '7', '5', '8', '10', '6', '3'],
        ['Какое время года следует после весны?', 'лето', 'осень', 'зима', 'апрель', 'май', 'сентябрь'],
        ['Сколько будет 2+2?', '4', '3', '5', '22', '1', '6'],
        ['Какова цель вашего присоединения к группе', 'обучение и общение', 'реклама', 'спам', 'разрушение группы'],
    ],

    'CHALLENGE_SUCCESS': [
        "Проверка пройдена.",
    ],

    'PERMISSION_DENY': [
        "Вам не нужно проходить проверку",
        "Что вы нажимаете, это не для вас!",
        "Неправильная кнопка! Хотите получить ограничение?",
    ],

    'CHALLENGE_TIMEOUT': 5*60,
    'MIN_CLG_TIME': 15,
    'UNBAN_TIMEOUT': 5*60,
    'FLOOD_LIMIT': 5,
    'DEL_LEAVE_MSG': True,
    'DEL_SERVICE_MSG': True,
}

CHAT_SETTINGS_HELP = {
    'WELCOME_WORDS': ("Приветствие", "Установить приветственное сообщение, %time% обозначает время для проверки (в секундах), для нескольких вариантов вводите по одному на строку", "str"),
    'CLG_QUESTIONS': ("Вопросы проверки", "Установить вопросы проверки в формате:\nВопрос\nПравильный ответ\nНеправильный ответ\n(несколько неправильных ответов)", "array"),
    'CHALLENGE_SUCCESS': ("Сообщение успешной проверки", "Всплывающее сообщение при успешной проверке, должно быть текстом, для нескольких вариантов вводите по одному на строку", "str"),
    'PERMISSION_DENY': ("Сообщение при отсутствии необходимости в проверке", "Всплывающее сообщение при отсутствии необходимости в проверке, должно быть текстом, для нескольких вариантов вводите по одному на строку", "str"),
    'CHALLENGE_TIMEOUT': ("Время ожидания проверки", "Время ожидания проверки в секундах, диапазон от 1 до 3600", "int"),
    'MIN_CLG_TIME': ("Минимальное динамическое время проверки", "Минимальное значение динамического времени проверки в секундах, диапазон от 0 до времени ожидания проверки", "int"),
    'UNBAN_TIMEOUT': ("Время разбана", "Время разбана после истечения времени ожидания или неудачной проверки, в секундах. Установите 0 или более 86400 для постоянного бана", "int"),
    'FLOOD_LIMIT': ("Защита от флуда", "При большом количестве новых участников за короткое время активируется защита от флуда. Установите 0 для отключения, 1 для постоянного включения", "int"),
    'DEL_LEAVE_MSG': ("Удаление сообщений о выходе", "Удалять сообщения о выходе или удалении пользователей", "bool"),
    'DEL_SERVICE_MSG': ("Удаление системных сообщений", "Удалять все системные сообщения Telegram (изменения названия, фото группы, закрепленные сообщения и т.д.)", "bool"),
}
