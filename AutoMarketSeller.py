import pyautogui
import pytesseract
from PIL import Image, ImageEnhance, ImageGrab
import time
import keyboard
import numpy as np
import cv2
import re
import threading
import tkinter as tk
from tkinter import scrolledtext, messagebox
import datetime
import json
import os
import logging
import random

# Настройка логирования для отладки
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
# Укажите путь к tesseract.exe, если он не в PATH
pytesseract.pytesseract.tesseract_cmd = r'C:\Program Files\Tesseract-OCR\tesseract.exe'
# Глобальные переменные
CONFIG_FILE = "auto_config.json"
screen_width, screen_height = pyautogui.size()
# Конфигурация по умолчанию
CONFIG = {
    "regions": {
        "sell_button": {"x": 83.3, "y": 56.5},  # Кнопка "Продать"
        "order_button": {"x": 49.5, "y": 63.9},  # Кнопка "Заказ на продажу"
        "price_input": {"x": 50.5, "y": 74.9},  # Область для ввода цены
        "submit_button": {"x": 62.5, "y": 84.0},  # Кнопка "Сделать заказ"
        "price_value": {"x1": 69.5, "y1": 50.0, "x2": 73.7, "y2": 52.0},  # Область "Цена"
        "average_price": {"x1": 89.8, "y1": 81.5, "x2": 93.2, "y2": 85.2}  # Область "Средняя цена"
    },
    "logic": {
        "fallback_ratio": 0.90,
        "max_difference_percent": 30,
        "robust_attempts": 12,
        "min_majority_count": 4
    },
    "ocr": {
        "whitelist_digits": "0123456789.,MTKmtk",
        "whitelist_text": "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789.,"
    },
    "sleep": {
        "between_clicks": {"min": 0.04, "max": 0.06},
        "after_recognition": {"min": 0.04, "max": 0.06},
        "before_input": {"min": 0.04, "max": 0.06},
        "before_input": {"min": 0.04, "max": 0.06},
        "after_input": {"min": 0.14, "max": 0.16},
        "between_cycles": {"min": 0.4, "max": 0.6},
        "robust_recognition": {"min": 0.02, "max": 0.03}
    }
}
# Глобальная очередь для передачи логов в GUI
log_queue = []
log_lock = threading.Lock()
# Глобальные переменные для калибровки
calibration_active = False
calibration_step = 0
calibration_regions = []
drag_start_point = None  # Начальная точка выделения при зажатом Shift
current_drag_box = None  # Текущая конечная точка выделения
shift_pressed = False  # Состояние клавиши Shift
# Переменные для управления основным циклом
main_loop_running = False
main_loop_thread = None
# Переменная для остановки текущего цикла (а не всего приложения)
current_loop_stop_flag = threading.Event()
# Переменные для визуализации
visualization_queue = []
visualization_lock = threading.Lock()
visualization_active = False
last_drag_time = 0
DRAG_UPDATE_INTERVAL = 0.05  # Интервал обновления в секундах (50 мс)


# Загрузка конфигурации из файла, если существует
def load_config():
    global CONFIG
    if os.path.exists(CONFIG_FILE):
        try:
            with open(CONFIG_FILE, 'r') as f:
                loaded_config = json.load(f)
                # Проверяем структуру конфига
                if "regions" in loaded_config and "logic" in loaded_config and "ocr" in loaded_config and "sleep" in loaded_config:
                    CONFIG = loaded_config
                    log_message("CONFIG", "✅ Конфигурация загружена из файла")
                    return True
                else:
                    # Если в конфиге нет раздела sleep, добавляем его
                    if "sleep" not in loaded_config:
                        loaded_config["sleep"] = CONFIG["sleep"]
                        CONFIG = loaded_config
                        save_config()
                        log_message("CONFIG", "🔄 Добавлен раздел sleep в конфигурацию")
                    return True
        except Exception as e:
            log_message("ERROR", f"❌ Ошибка загрузки конфигурации: {str(e)}")
    return False


# Сохранение конфигурации в файл
def save_config():
    try:
        with open(CONFIG_FILE, 'w') as f:
            json.dump(CONFIG, f, indent=4)
        log_message("CONFIG", "💾 Конфигурация сохранена")
        return True
    except Exception as e:
        log_message("ERROR", f"❌ Не удалось сохранить конфигурацию: {str(e)}")
        return False


# Функция для добавления сообщения в лог
def log_message(level, message):
    with log_lock:
        timestamp = datetime.datetime.now().strftime("%H:%M:%S")
        log_queue.append(f"[{timestamp}] {level.upper()}: {message}")


# Конвертация относительных координат в абсолютные
def get_absolute_coords(region_name):
    """Возвращает абсолютные координаты для указанной области."""
    region = CONFIG["regions"][region_name]
    if "x2" in region:  # Это прямоугольная область
        x1 = int(screen_width * region["x1"] / 100)
        y1 = int(screen_height * region["y1"] / 100)
        x2 = int(screen_width * region["x2"] / 100)
        y2 = int(screen_height * region["y2"] / 100)
        return (x1, y1, x2, y2)
    else:  # Это точка (клик)
        x = int(screen_width * region["x"] / 100)
        y = int(screen_height * region["y"] / 100)
        return (x, y)


# Функция для получения случайного времени ожидания
def get_random_sleep(action):
    """Возвращает случайное время ожидания для указанного действия из конфига."""
    try:
        sleep_config = CONFIG["sleep"].get(action, {"min": 0.05, "max": 0.05})
        min_time = sleep_config["min"]
        max_time = sleep_config["max"]
        return random.uniform(min_time, max_time)
    except Exception as e:
        log_message("ERROR", f"Ошибка получения времени ожидания для {action}: {str(e)}")
        return 0.05  # значение по умолчанию


# Функция для предварительной обработки изображения
def preprocess_image(image, scale_percent=200):
    image = image.convert('L')
    enhancer = ImageEnhance.Contrast(image)
    image = enhancer.enhance(2.0)
    image_np = np.array(image)
    _, image_np = cv2.threshold(image_np, 0, 255, cv2.THRESH_BINARY + cv2.THRESH_OTSU)
    width = int(image_np.shape[1] * scale_percent / 100)
    height = int(image_np.shape[0] * scale_percent / 100)
    image_np = cv2.resize(image_np, (width, height), interpolation=cv2.INTER_CUBIC)
    return Image.fromarray(image_np)


# Универсальная функция захвата области
def capture_region(region_name):
    """Захватывает указанную область экрана."""
    x1, y1, x2, y2 = get_absolute_coords(region_name)
    return ImageGrab.grab(bbox=(x1, y1, x2, y2))


# Улучшенная обработка чисел с суффиксами (игнорирование лишних символов)
def parse_number_with_suffix(text):
    """Распознает число с суффиксами M/T, игнорируя лишние символы и русские буквы."""
    if not text:
        return None
    # Удаляем пробелы и очищаем текст от русских букв и других ненужных символов
    text = re.sub(r'[а-яА-Я]', '', text)  # Удаляем русские буквы
    text = text.replace(" ", "").upper().rstrip('.')
    # Улучшенное регулярное выражение для поиска чисел и суффиксов
    match = re.search(r'([\d.,]+)\s*([MTK])?\b', text)  # Добавлен K
    if not match:
        return None
    number_str, suffix = match.groups()
    # Удаляем все нецифровые символы из числа, кроме запятых и точек
    number_str = re.sub(r'[^\d.,]', '', number_str)
    try:
        # Определяем, является ли запятая разделителем тысяч или десятичной точкой
        if ',' in number_str and '.' in number_str:
            # Если есть и запятая, и точка, предполагаем, что последняя - десятичная
            if number_str.rfind(',') < number_str.rfind('.'):
                # Формат: 1,234.56
                number_str = number_str.replace(',', '')
            else:
                # Формат: 1.234,56
                number_str = number_str.replace('.', '').replace(',', '.')
        elif ',' in number_str:
            # Если только запятая, предполагаем, что это разделитель тысяч
            number_str = number_str.replace(',', '')
        elif '.' in number_str and number_str.count('.') > 1:
            # Если несколько точек, удаляем все, кроме последней
            last_dot = number_str.rfind('.')
            number_str = number_str[:last_dot].replace('.', '') + number_str[last_dot:]
        # Преобразуем в число
        number = float(number_str)
        # Применяем суффиксы
        if suffix == 'M':
            number *= 1_000_000
        elif suffix in ['T', 'K']:  # Теперь K и T работают одинаково
            number *= 1_000
        return int(number)
    except (ValueError, TypeError) as e:
        log_message("DEBUG", f"Ошибка парсинга числа '{text}': {str(e)}")
        return None


# Универсальная функция распознавания числа
def recognize_number(region_name, use_robust=False, attempts=12):
    """Распознает число в указанной области."""
    if use_robust:
        return robust_recognize_number(region_name, attempts)
    try:
        img = capture_region(region_name)
        processed = preprocess_image(img)
        # Распознаем с расширенным whitelist
        text = pytesseract.image_to_string(
            processed,
            config=f'--psm 7 --oem 1 -c tessedit_char_whitelist={CONFIG["ocr"]["whitelist_digits"]}'
        ).strip()
        log_message("DEBUG", f"Raw OCR result from {region_name}: '{text}'")
        return parse_number_with_suffix(text)
    except Exception as e:
        log_message("ERROR", f"Ошибка распознавания в области {region_name}: {str(e)}")
        return None


# Улучшенное многократное распознавание числа
def robust_recognize_number(region_name, attempts=12):
    """
    Многократное распознавание числа с разными настройками.
    Возвращает наиболее частое достоверное число или None.
    """
    results = []
    configs = [
        '--psm 6 --oem 1',
        '--psm 7 --oem 1',
        '--psm 8 --oem 1',
        '--psm 13 --oem 1'
    ]
    contrasts = [1.5, 2.0, 2.5]
    thresholds = [True, False]
    scales = [150, 200, 250]
    log_message("INFO", f"🔍 Запуск многократного распознавания ({attempts} попыток)...")
    for i in range(attempts):
        try:
            img = capture_region(region_name)
            image = img.convert('L')
            contrast = contrasts[i % len(contrasts)]
            enhancer = ImageEnhance.Contrast(image)
            image = enhancer.enhance(contrast)
            image_np = np.array(image)
            use_otsu = thresholds[i % len(thresholds)]
            if use_otsu:
                _, image_np = cv2.threshold(image_np, 0, 255, cv2.THRESH_BINARY + cv2.THRESH_OTSU)
            else:
                _, image_np = cv2.threshold(image_np, 127, 255, cv2.THRESH_BINARY)
            scale = scales[i % len(scales)]
            width = int(image_np.shape[1] * scale / 100)
            height = int(image_np.shape[0] * scale / 100)
            image_np = cv2.resize(image_np, (width, height), interpolation=cv2.INTER_CUBIC)
            processed = Image.fromarray(image_np)
            config = configs[i % len(configs)]
            text = pytesseract.image_to_string(
                processed,
                config=f'{config} -c tessedit_char_whitelist={CONFIG["ocr"]["whitelist_digits"]}'
            ).strip().rstrip('.').upper()
            log_message("DEBUG", f"Robust OCR attempt {i + 1}: '{text}'")
            number = parse_number_with_suffix(text)
            results.append(number)
        except Exception as e:
            log_message("DEBUG", f"Ошибка в попытке {i + 1}: {e}")
            results.append(None)
        # Добавляем случайную задержку между попытками
        time.sleep(get_random_sleep("robust_recognition"))

    # Анализ: мажоритарное голосование
    valid_results = [r for r in results if r is not None]
    if not valid_results:
        log_message("ERROR", "❌ Все попытки распознавания провалились.")
        return None
    from collections import Counter
    counter = Counter(valid_results)
    most_common, count = counter.most_common(1)[0]
    # Проверяем, достаточно ли совпадений
    if count >= CONFIG["logic"]["min_majority_count"]:
        log_message("SUCCESS", f"✅ Достаточно совпадений: {most_common:,} (найдено {count} раз)")
        return most_common
    else:
        log_message("WARNING",
                    f"⚠️ Недостаточно совпадений: {most_common:,} ({count} раз), нужно ≥ {CONFIG['logic']['min_majority_count']}")
        return None


# Сравнение двух чисел (разница ≤ заданного процента)
def compare_numbers(number1, number2):
    if number1 is None or number2 is None:
        return False
    diff_percent = abs(number1 - number2) / max(number1, number2) * 100
    return diff_percent <= CONFIG["logic"]["max_difference_percent"]


# === КАЛИБРОВКА ===
def start_calibration():
    """Запускает режим калибровки. Выделение с помощью Shift, сохранение ПКМ."""
    global calibration_active, calibration_step, calibration_regions
    calibration_regions = [
        "sell_button",  # Кнопка "Продать"
        "order_button",  # Кнопка "Заказ на продажу"
        "price_input",  # Область для ввода цены
        "submit_button",  # Кнопка "Сделать заказ"
        "price_value",  # Область "Цена" (число)
        "average_price"  # Область "Средняя цена" (число)
    ]
    calibration_step = 0
    calibration_active = True
    log_message("CALIBRATE", "🔧 Режим калибровки запущен")
    log_message("CALIBRATE", "1. Нажмите ПКМ на первой кнопке: 'Продать'")
    log_message("HINT", "ℹ️ Подсказка: Нажмите Esc для отмены калибровки")


def handle_calibration_click(x, y, button, pressed):
    """Обработчик кликов во время калибровки."""
    global calibration_active, calibration_step, calibration_regions, drag_start_point, current_drag_box
    if not (calibration_active and pressed):
        return True
    # Esc отменяет калибровку (обрабатывается в основном цикле)
    current_region = calibration_regions[calibration_step]
    # Словарь для отображения технических названий на русские
    region_names_rus = {
        "sell_button": "Кнопка 'Продать'",
        "order_button": "Кнопка 'Заказ на продажу'",
        "price_input": "Область для ввода цены",
        "submit_button": "Кнопка 'Сделать заказ'",
        "price_value": "Область 'Цена'",
        "average_price": "Область 'Средняя цена'"
    }
    # Для кнопок и полей ввода: используем ПКМ для фиксации точки
    if current_region in ["sell_button", "order_button", "price_input", "submit_button"]:
        if button == 'right':  # ПКМ — фиксируем точку
            rel_x = (x / screen_width) * 100
            rel_y = (y / screen_height) * 100
            CONFIG["regions"][current_region] = {"x": rel_x, "y": rel_y}
            log_message("CALIBRATE", f"📍 {region_names_rus[current_region]} сохранена: ({rel_x:.2f}%, {rel_y:.2f}%)")
            calibration_step += 1
            if calibration_step >= len(calibration_regions):
                save_config()
                calibration_active = False
                log_message("CALIBRATE", "✅ Калибровка завершена! Конфигурация сохранена.")
            else:
                next_region = calibration_regions[calibration_step]
                if next_region in ["sell_button", "order_button", "price_input", "submit_button"]:
                    log_message("CALIBRATE", f"Нажмите ПКМ на: {region_names_rus[next_region]}")
                else:
                    log_message("CALIBRATE", f"Зажмите Shift и выделите область для: {region_names_rus[next_region]}")
        return True
    # Для областей чисел: обработка ПКМ для сохранения выделенной области
    if current_region in ["price_value", "average_price"]:
        if button == 'right' and drag_start_point is not None and current_drag_box is not None:
            # ПКМ — сохраняем текущую выделенную область
            x1, y1 = drag_start_point
            x2, y2 = current_drag_box
            # Убедимся, что координаты в правильном порядке
            x1, x2 = min(x1, x2), max(x1, x2)
            y1, y2 = min(y1, y2), max(y1, y2)
            # Преобразуем в относительные координаты
            rel_x1 = (x1 / screen_width) * 100
            rel_y1 = (y1 / screen_height) * 100
            rel_x2 = (x2 / screen_width) * 100
            rel_y2 = (y2 / screen_height) * 100
            CONFIG["regions"][current_region] = {
                "x1": rel_x1, "y1": rel_y1,
                "x2": rel_x2, "y2": rel_y2
            }
            log_message("CALIBRATE",
                        f"✅ {region_names_rus[current_region]} сохранена: {rel_x1:.2f}%, {rel_y1:.2f}% - {rel_x2:.2f}%, {rel_y2:.2f}%")
            # Переходим к следующей области
            calibration_step += 1
            if calibration_step >= len(calibration_regions):
                save_config()
                calibration_active = False
                log_message("CALIBRATE", "✅ Калибровка завершена! Конфигурация сохранена.")
            else:
                next_region = calibration_regions[calibration_step]
                if next_region in ["sell_button", "order_button", "price_input", "submit_button"]:
                    log_message("CALIBRATE", f"Нажмите ПКМ на: {region_names_rus[next_region]}")
                else:
                    log_message("CALIBRATE", f"Зажмите Shift и выделите область для: {region_names_rus[next_region]}")
            # Сбрасываем состояние выделения
            drag_start_point = None
            current_drag_box = None
            return True
        elif button == 'left':
            # ЛКМ — игнорируем, чтобы пользователь мог повторить выделение
            log_message("CALIBRATE",
                        f"ЛКМ нажата. Вы можете повторить выделение области для '{region_names_rus[current_region]}'")
            return True
    return True


def visualization_worker():
    """Рабочий поток для визуализации выделенных областей с высокой частотой кадров."""
    global visualization_active
    visualization_active = True
    target_fps = 60  # Целевая частота кадров
    frame_delay = 1.0 / target_fps  # Задержка между кадрами (примерно 16.67 мс)
    while visualization_active:
        start_time = time.time()
        with visualization_lock:
            if visualization_queue:
                # Получаем последнюю задачу (самую актуальную)
                x1, y1, x2, y2 = visualization_queue[-1]
                try:
                    # Создаем оверлей
                    overlay = tk.Toplevel()
                    overlay.attributes("-topmost", True)
                    overlay.attributes("-transparentcolor", "black")
                    overlay.attributes("-alpha", 0.4)  # Немного повысили прозрачность
                    overlay.overrideredirect(True)
                    overlay.geometry(f"{screen_width}x{screen_height}+0+0")
                    canvas = tk.Canvas(overlay, width=screen_width, height=screen_height,
                                       bg="black", highlightthickness=0)
                    canvas.pack()
                    # Рисуем прямоугольник с более тонкой зеленой рамкой
                    canvas.create_rectangle(x1, y1, x2, y2, outline="lime", width=2)  # lime - ярче, чем green
                    # Плавно исчезает через 170 мс (вместо резкого исчезновения)
                    overlay.after(170, overlay.destroy)
                except Exception as e:
                    log_message("DEBUG", f"Ошибка визуализации: {str(e)}")
        # Рассчитываем время выполнения итерации
        elapsed = time.time() - start_time
        # Спим оставшееся время до достижения целевой частоты кадров
        if elapsed < frame_delay:
            time.sleep(frame_delay - elapsed)


def start_visualization_worker():
    """Запускает рабочий поток для визуализации."""
    worker_thread = threading.Thread(target=visualization_worker, daemon=True)
    worker_thread.start()
    return worker_thread


def draw_calibration_box(x1, y1, x2, y2):
    """Добавляет задачу визуализации в очередь."""
    with visualization_lock:
        # Удаляем предыдущие задачи для этой области
        visualization_queue[:] = [box for box in visualization_queue
                                  if not (abs(box[0] - x1) < 10 and abs(box[1] - y1) < 10)]
        # Добавляем новую задачу
        visualization_queue.append((x1, y1, x2, y2))


def handle_shift_drag(x, y):
    """Обработчик движения мыши при зажатом Shift для визуализации выделения."""
    global calibration_active, calibration_step, drag_start_point, current_drag_box, shift_pressed
    shift_held = keyboard.is_pressed('shift')
    # Обрабатываем только если активна калибровка
    if not calibration_active:
        return
    current_region = calibration_regions[calibration_step] if calibration_step < len(calibration_regions) else None
    # Проверяем, что мы на этапе выделения области числа
    if not current_region or current_region not in ["price_value", "average_price"]:
        return
    # Если Shift только что нажат (начало выделения)
    if shift_held and not shift_pressed:
        shift_pressed = True
        drag_start_point = (x, y)
        log_message("CALIBRATE", f"📌 Новая начальная точка выделения установлена: ({x}, {y})")
        return  # Не визуализируем, пока мышь не двинется
    # Если Shift удерживается
    if shift_held and shift_pressed:
        current_drag_box = (x, y)
        # Визуализируем прямоугольник
        x1, y1 = drag_start_point
        x2, y2 = x, y
        # Убедимся, что координаты в правильном порядке для отображения
        x1, x2 = min(x1, x2), max(x1, x2)
        y1, y2 = min(y1, y2), max(y1, y2)
        # Отправляем задачу визуализации
        draw_calibration_box(x1, y1, x2, y2)
        return
    # Если Shift только что отпущен (конец выделения)
    if not shift_held and shift_pressed:
        shift_pressed = False
        log_message("CALIBRATE", f"📏 Выделение завершено. Конечная точка: ({x}, {y}). Нажмите ПКМ для сохранения.")


def calibration_mouse_listener():
    """Прослушиватель мыши для калибровки."""
    from pynput import mouse
    def on_click(x, y, button, pressed):
        if calibration_active:
            handle_calibration_click(x, y, button.name, pressed)
        return True

    def on_move(x, y):
        # Передаем координаты мыши в обработчик выделения
        if calibration_active:
            handle_shift_drag(x, y)

    listener = mouse.Listener(on_click=on_click, on_move=on_move)
    listener.start()
    return listener

    def on_move(x, y):
        # Обрабатываем перемещение только если зажат Shift и активна калибровка
        if calibration_active and keyboard.is_pressed('shift'):
            # Добавляем в очередь с задержкой
            threading.Thread(target=lambda: handle_shift_drag(x, y), daemon=True).start()

    listener = mouse.Listener(on_click=on_click, on_move=on_move)
    listener.start()
    return listener


# === GUI ===
def start_log_window():
    root = tk.Tk()
    root.title("🤖AlbionOnline-AutoMarketSeller")
    root.geometry("650x450")
    root.attributes("-topmost", True)
    root.attributes("-alpha", 0.95)
    root.resizable(True, True)
    root.configure(bg="#1e1e1e")
    # Создаем меню
    menu_bar = tk.Menu(root)
    # Меню "Файл"
    file_menu = tk.Menu(menu_bar, tearoff=0)
    file_menu.add_command(label="Калибровка", command=lambda: start_calibration())
    file_menu.add_command(label="Сохранить конфиг", command=lambda: save_config())
    file_menu.add_separator()
    file_menu.add_command(label="Выход", command=root.destroy)
    menu_bar.add_cascade(label="Файл", menu=file_menu)
    # Меню "Помощь"
    help_menu = tk.Menu(menu_bar, tearoff=0)
    help_menu.add_command(label="Справка", command=lambda: messagebox.showinfo(
        "Справка",
        "F1: Режим калибровки (ПКМ для выбора)\n"
        "F2: Тест распознавания цены\n"
        "F3: Тест распознавания средней цены\n"
        "F4: Запуск/остановка основного цикла\n"
        "F5: Остановка цикла\n"
        "Esc: Остановка"
    ))
    menu_bar.add_cascade(label="Помощь", menu=help_menu)
    root.config(menu=menu_bar)
    # Заголовок
    title_label = tk.Label(
        root,
        text="📋 Лог работы алгоритма",
        font=("Consolas", 12, "bold"),
        bg="#1e1e1e",
        fg="#00cc99"
    )
    title_label.pack(pady=5)
    # Текстовая область с прокруткой
    text_area = scrolledtext.ScrolledText(
        root,
        wrap=tk.WORD,
        width=80,
        height=22,
        font=("Consolas", 9),
        bg="#111",
        fg="#f0f0f0",
        insertbackground="white",
        highlightthickness=0,
        bd=0
    )
    text_area.pack(padx=10, pady=5, fill=tk.BOTH, expand=True)
    # Статус-бар
    status_frame = tk.Frame(root, bg="#1e1e1e")
    status_frame.pack(fill=tk.X, padx=10, pady=5)

    tk.Label(
        status_frame,
        text="Статус: Готов",
        font=("Consolas", 9),
        bg="#1e1e1e",
        fg="#cccccc",
        name="status_label"
    ).pack(side=tk.LEFT)

    # Имя автора
    tk.Label(
        status_frame,
        text="Автор: Vortales",
        font=("Consolas", 9),
        bg="#1e1e1e",
        fg="#666666"
    ).pack(side=tk.RIGHT, padx=(40, 10))

    # Разрешение
    tk.Label(
        status_frame,
        text=f"Разрешение: {screen_width}x{screen_height}",
        font=("Consolas", 9),
        bg="#1e1e1e",
        fg="#666666",
        name="resolution_label"
    ).pack(side=tk.RIGHT)
    MAX_LINES = 200

    def update_log():
        with log_lock:
            while log_queue:
                msg = log_queue.pop(0)
                text_area.insert(tk.END, msg + "\n")
                # Раскрашиваем строки по уровню логирования
                if "ERROR" in msg:
                    text_area.tag_add("error", "end-2c linestart", "end-1c")
                elif "WARNING" in msg:
                    text_area.tag_add("warning", "end-2c linestart", "end-1c")
                elif "SUCCESS" in msg:
                    text_area.tag_add("success", "end-2c linestart", "end-1c")
                elif "CALIBRATE" in msg:
                    text_area.tag_add("calibrate", "end-2c linestart", "end-1c")
        # Применяем теги
        text_area.tag_config("error", foreground="#ff6666")
        text_area.tag_config("warning", foreground="#ffff66")
        text_area.tag_config("success", foreground="#66ff66")
        text_area.tag_config("calibrate", foreground="#66aaff")
        # Ограничиваем количество строк
        lines = text_area.get(1.0, tk.END).splitlines()
        if len(lines) > MAX_LINES:
            text_area.delete(1.0, f"{len(lines) - MAX_LINES + 1}.0")
        text_area.see(tk.END)
        root.after(200, update_log)

    def on_closing():
        log_message("INFO", "Программа завершена пользователем (закрытие окна)")
        # Полная остановка всех процессов
        global visualization_active, main_loop_running, calibration_active
        visualization_active = False
        main_loop_running = False
        calibration_active = False
        # Останавливаем все слушатели
        try:
            mouse_listener.stop()
            keyboard.unhook_all()
        except:
            pass
        # Убиваем процесс
        os._exit(0)  # Полное завершение

    root.protocol("WM_DELETE_WINDOW", on_closing)
    update_log()
    root.mainloop()


# === ОСНОВНОЙ ЦИКЛ ===
def main_loop():
    """
    Основной цикл алгоритма.
    Запускается в отдельном потоке через toggle_main_loop().
    Останавливается по флагу current_loop_stop_flag.
    """
    log_message("INFO", "Алгоритм запущен. Нажмите F5 для остановки.")

    while not current_loop_stop_flag.is_set():
        try:
            # Шаг 1: Кликаем по кнопкам
            x, y = get_absolute_coords("sell_button")
            pyautogui.click(x=x, y=y)
            time.sleep(get_random_sleep("between_clicks"))

            x, y = get_absolute_coords("order_button")
            pyautogui.click(x=x, y=y)
            time.sleep(get_random_sleep("between_clicks"))

            # Шаг 2: Распознаём числа
            number1 = recognize_number("price_value")
            if number1 is not None:
                log_message("SUCCESS", f"Первое число: {number1:,}")
            else:
                log_message("WARNING", "❌ Не удалось распознать первое число.")

            number2 = recognize_number("average_price")
            if number2 is None:
                log_message("ERROR", "❌ Не удалось распознать второе число. Пропуск итерации.")
                time.sleep(get_random_sleep("between_cycles"))
                continue  # Переходим к следующей итерации

            log_message("INFO", f"Второе число: {number2:,}")

            # Шаг 3: Логика сравнения и вычисления
            if number1 is None:
                # Если первое число не распознано, используем 90% от второго
                result = int(number2 * CONFIG["logic"]["fallback_ratio"])
                log_message("FALLBACK",
                            f"→ Fallback: {CONFIG['logic']['fallback_ratio'] * 100:.0f}% от второго числа → {result:,}")
            else:
                if not compare_numbers(number1, number2):
                    # Если числа сильно отличаются, запускаем уточнённое распознавание
                    log_message("INFO",
                                f"Числа отличаются >{CONFIG['logic']['max_difference_percent']}%. Запуск точного уточнения...")
                    refined_number1 = robust_recognize_number("price_value")
                    refined_number2 = robust_recognize_number("average_price")
                    if refined_number1 is not None:
                        log_message("INFO", f"🔍 Уточнено первое число: {refined_number1:,}")
                        used_number = refined_number1
                    else:
                        log_message("WARNING", "⚠️ Не удалось уточнить первое число. Используем исходное.")
                        used_number = number1
                    if refined_number2 is not None:
                        log_message("INFO", f"🔍 Уточнено второе число: {refined_number2:,}")
                    result = int(used_number * CONFIG["logic"]["fallback_ratio"])
                    log_message("SUCCESS",
                                f"→ Результат: {CONFIG['logic']['fallback_ratio'] * 100:.0f}% от выбранного первого числа = {result:,}")
                else:
                    # Числа близки, используем 90% от первого
                    result = int(number1 * CONFIG["logic"]["fallback_ratio"])
                    log_message("SUCCESS",
                                f"→ Числа близки. Результат: {CONFIG['logic']['fallback_ratio'] * 100:.0f}% от первого = {result:,}")

            # Шаг 4: Ввод результата
            x, y = get_absolute_coords("price_input")
            pyautogui.click(x=x, y=y)
            time.sleep(get_random_sleep("before_input"))

            pyautogui.write(str(result))
            time.sleep(get_random_sleep("between_clicks"))

            x, y = get_absolute_coords("submit_button")
            pyautogui.click(x=x, y=y)
            time.sleep(get_random_sleep("after_input"))

            log_message("ACTION", f"✅ Введено значение: {result:,}")
            # Пауза между циклами
            time.sleep(get_random_sleep("between_cycles"))
        except Exception as e:
            log_message("ERROR", f"Критическая ошибка в основном цикле: {str(e)}")
            time.sleep(get_random_sleep("between_cycles"))

    log_message("INFO", "Цикл распознавания и нажатий завершён.")
    # Сбрасываем флаг для будущих запусков
    current_loop_stop_flag.clear()


# Функция для переключения основного цикла
def toggle_main_loop():
    """
    Переключает состояние основного цикла.
    При повторном нажатии F4 останавливает цикл.
    """
    global main_loop_running, main_loop_thread
    if main_loop_running:
        # Цикл уже запущен, останавливаем его
        current_loop_stop_flag.set()
        log_message("STOP", "🛑 Цикл распознавания и нажатий остановлен по команде пользователя (F4).")
    else:
        # Цикл остановлен, запускаем его
        def run_loop():
            """Целевая функция для потока."""
            try:
                main_loop()  # Запускаем основной цикл
            except Exception as e:
                log_message("ERROR", f"Ошибка в основном цикле: {str(e)}")
            finally:
                # Гарантируем, что флаг сбросится, даже если цикл завершится с ошибкой
                global main_loop_running
                main_loop_running = False

        # Создаём и запускаем поток
        main_loop_thread = threading.Thread(target=run_loop, daemon=True)
        main_loop_running = True
        main_loop_thread.start()
        log_message("START", "🚀 Цикл распознавания и нажатий запущен.")


# Обработчик для F5
def handle_f5(event):
    if event.scan_code == 63:  # F5
        if main_loop_running:
            current_loop_stop_flag.set()
            log_message("STOP", "🛑 Цикл распознавания и нажатий остановлен по F5.")
        else:
            log_message("INFO", "ℹ️ Нет активного цикла для остановки по F5.")


# === ЗАПУСК ПРОГРАММЫ ===
if __name__ == "__main__":
    # Загружаем конфигурацию
    load_config()
    # Запускаем окно лога в фоне
    log_thread = threading.Thread(target=start_log_window, daemon=True)
    log_thread.start()
    # Запускаем слушатель мыши для калибровки
    mouse_listener = calibration_mouse_listener()
    # Запускаем рабочий поток визуализации
    viz_worker = start_visualization_worker()
    time.sleep(1)  # Даем время GUI загрузиться
    log_message("READY", "🎯 Готов к работе.")
    log_message("HINT", "F1 — калибровка (ПКМ для выбора) | F2/F3 — тест OCR | F4 — запуск/остановка | F5 — стоп цикла")


    # Обработчики клавиш
    def handle_f1(event):
        if event.scan_code == 59:  # F1
            start_calibration()


    def handle_f2(event):
        if event.scan_code == 60:  # F2
            number = recognize_number("price_value")
            if number is not None:
                log_message("TEST", f"Тест 'Цена': {number:,}")
            else:
                log_message("TEST", "❌ Не удалось распознать 'Цену'")


    def handle_f3(event):
        if event.scan_code == 61:  # F3
            number = recognize_number("average_price")
            if number is not None:
                log_message("TEST", f"Тест 'Средняя цена': {number:,}")
            else:
                log_message("TEST", "❌ Не удалось распознать 'Среднюю цену'")


    def handle_f4(event):
        if event.scan_code == 62:  # F4
            toggle_main_loop()


    # Регистрируем обработчики
    keyboard.on_press_key(59, handle_f1)  # F1
    keyboard.on_press_key(60, handle_f2)  # F2
    keyboard.on_press_key(61, handle_f3)  # F3
    keyboard.on_press_key(62, handle_f4)  # F4
    keyboard.on_press_key(63, handle_f5)  # F5
    log_message("INFO", "Нажмите F1 для калибровки, F4 для запуска цикла, F5 для его остановки")
    # Основной цикл ожидания
    try:
        while True:
            time.sleep(0.1)
    except KeyboardInterrupt:
        log_message("INFO", "Программа завершена пользователем")
        visualization_active = False
        mouse_listener.stop()