#!/usr/bin/env python3
"""
Speed Reading Application with Enhanced EPUB Parsing (Using Spine) and Image Viewer

Features:
- Load .txt, .pdf, .docx, and .epub files.
- For EPUBs, manually extract text (from XHTML/HTML files) and images
  by reading the container.xml and OPF file from the EPUB (ZIP archive).
  Uses the OPF spine to extract text in proper reading order.
- Display one word at a time (with fixation guidance) and a preview window.
- A separate window for browsing extracted images with forward/back buttons.
- Adjustable speed, tagging, and session save/load features.
  
Author: Your Name
Date: 2025-02-03
"""

import sys, os, logging, json, time, threading, webbrowser, string, re, zipfile, io, hashlib, shutil
import tkinter as tk
from tkinter import filedialog, messagebox, font, ttk
import xml.etree.ElementTree as ET
from bs4 import BeautifulSoup
from PIL import Image, ImageTk

# External libraries for non-EPUB files
import pdfplumber
import docx
import mobi
import ebooklib
from ebooklib import epub

# ---------------------------------------------------------
# Logging Configuration (compatible with older Python versions)
# ---------------------------------------------------------
LOG_FILENAME = "debug.log"
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s - %(levelname)s - %(message)s",
    filename=LOG_FILENAME,
    filemode="w"
)
console_handler = logging.StreamHandler(sys.stdout)
console_handler.setLevel(logging.INFO)
console_formatter = logging.Formatter("%(asctime)s - %(levelname)s - %(message)s")
console_handler.setFormatter(console_formatter)
logging.getLogger().addHandler(console_handler)

# Silence noisy libraries
logging.getLogger("pdfminer").setLevel(logging.WARNING)
logging.getLogger("PIL").setLevel(logging.WARNING)
logging.getLogger("urllib3").setLevel(logging.WARNING)

# Global exception hook
def global_exception_hook(exctype, value, tb):
    logging.error("Uncaught exception:", exc_info=(exctype, value, tb))
    sys.__excepthook__(exctype, value, tb)
sys.excepthook = global_exception_hook

# ---------------------------------------------------------
# SpeedReaderApp with integrated EPUB parsing and image viewer
# ---------------------------------------------------------
if getattr(sys, 'frozen', False):
    # If run as an exe
    BASE_DIR = os.path.dirname(sys.executable)
    DATA_DIR = os.path.join(BASE_DIR, "data")
else:
    # If run as a script
    BASE_DIR = os.path.dirname(os.path.abspath(__file__))
    DATA_DIR = os.path.join(BASE_DIR, "data")

if not os.path.exists(DATA_DIR):
    os.makedirs(DATA_DIR)

SESSIONS_DIR = os.path.join(DATA_DIR, "sessions")
if not os.path.exists(SESSIONS_DIR):
    os.makedirs(SESSIONS_DIR)

SESSION_FILE = os.path.join(DATA_DIR, "session.json")
LIBRARY_FILE = os.path.join(DATA_DIR, "library.json")
CACHE_DIR = os.path.join(DATA_DIR, "cache_v3")
if not os.path.exists(CACHE_DIR):
    os.makedirs(CACHE_DIR)

class SpeedReaderApp(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("Speed Reading App")
        self.geometry("800x600")
        self.protocol("WM_DELETE_WINDOW", self.on_close)

        # Application state
        self.file_path = None
        self.text_content = ""
        self.words = []
        self.current_index = 0
        self.playing = False
        self.wpm = 300  # words per minute
        self.variable_speed = False  # plain Python boolean
        self.auto_rewind_count = 5
        self.fixation_mode = "middle"  # "start", "middle", "end"
        self.font_size = 48
        self.font_family = "Helvetica"
        self.theme = "light"  # "light" or "dark"
        self.highlight_color = "red"
        self.pause_paragraph = 500  # milliseconds

        self.use_intelligent_pauses = True
        self.use_bionic_bolding = False
        self.contrast_mode = "default"  # "default", "high", "sepia"

        # Equalizer settings
        self.pause_multipliers = {
            "period": 2.0,
            "short": 1.5,
            "long_word": 1.2,
            "paragraph": 3.0,
            "numbers": 1.5,
            "hyphens": 1.3,
            "custom1": 1.0,
            "custom2": 1.0,
            "custom3_regex": 1.0
        }
        self.short_pause_chars = ",;:-"
        self.full_pause_chars = "."  # User requested only on periods by default
        self.long_word_threshold = 8
        self.custom1_chars = ""
        self.custom2_chars = ""
        self.custom3_regex_pattern = ""

        # Image settings
        self.extract_images = True
        self.min_img_width = 100
        self.min_img_height = 100

        self.tagged_words = set()

        # For EPUB image extraction (populated when an EPUB is loaded)
        self.epub_images = []       # List of PIL.Image objects
        # For EPUB image extraction (populated when an EPUB is loaded)
        self.epub_images = []       # List of PIL.Image objects
        self.epub_image_names = []  # Corresponding names
        self.image_locations = {}   # Map image name -> word index

        # Migration: Move old library.json to sessions/ if it exists
        old_lib = "library.json"
        if os.path.exists(old_lib) and not os.path.exists(LIBRARY_FILE):
            try:
                shutil.move(old_lib, LIBRARY_FILE)
                logging.info(f"Migrated legacy library from {old_lib} to {LIBRARY_FILE}")
            except Exception as e:
                logging.error(f"Failed to migrate library: {e}")

        self.library = []
        self.load_library_metadata()

        # Create UI widgets
        self.create_widgets()
        self.bind_keys()
        self.load_last_session()

    def create_widgets(self):
        # Menu bar (file and settings)
        self.menu_bar = tk.Menu(self)
        self.config(menu=self.menu_bar)
        file_menu = tk.Menu(self.menu_bar, tearoff=0)
        file_menu.add_command(label="Open File (Ctrl+O)", command=self.open_file)
        file_menu.add_command(label="Import PDF (Manual Layout)", command=self.import_pdf_manual)
        file_menu.add_command(label="Save Session (Ctrl+S)", command=self.save_session)
        file_menu.add_command(label="Load Session", command=self.load_session)
        self.menu_bar.add_cascade(label="File", menu=file_menu)
        settings_menu = tk.Menu(self.menu_bar, tearoff=0)
        settings_menu.add_command(label="Preferences", command=self.open_preferences)
        self.menu_bar.add_cascade(label="Settings", menu=settings_menu)

        # Main display frame
        self.display_frame = tk.Frame(self, bg=self.get_bg_color())
        self.display_frame.pack(expand=True, fill=tk.BOTH)
        # Canvas for word display
        self.word_canvas = tk.Canvas(self.display_frame, height=200, bg=self.get_bg_color())
        self.word_canvas.pack(fill=tk.X, pady=10)
        # Progress label
        self.progress_label = tk.Label(self.display_frame, text="Progress: 0%", bg=self.get_bg_color(), fg=self.get_fg_color())
        self.progress_label.pack()
        # Preview text widget for upcoming words
        self.preview_text = tk.Text(self.display_frame, height=5, state=tk.DISABLED, bg=self.get_bg_color(), fg=self.get_fg_color())
        self.preview_text.pack(fill=tk.X, padx=10, pady=10)

        # Control frame (buttons, slider) - Stacked Rows
        self.control_frame = tk.Frame(self, bg=self.get_bg_color())
        self.control_frame.pack(fill=tk.X, pady=5)

        self.row1 = tk.Frame(self.control_frame, bg=self.get_bg_color())
        self.row1.pack(fill=tk.X)
        self.row2 = tk.Frame(self.control_frame, bg=self.get_bg_color())
        self.row2.pack(fill=tk.X)
        self.row3 = tk.Frame(self.control_frame, bg=self.get_bg_color())
        self.row3.pack(fill=tk.X)

        # Row 1: Playback & Speed
        self.play_pause_button = tk.Button(self.row1, text="Play/Pause", command=self.toggle_play_pause)
        self.play_pause_button.pack(side=tk.LEFT, padx=5, pady=5)

        self.speed_down_btn = tk.Button(self.row1, text="-", command=self.decrease_speed, width=3)
        self.speed_down_btn.pack(side=tk.LEFT, padx=2, pady=5)

        self.wpm_slider = tk.Scale(self.row1, from_=100, to=1000, orient=tk.HORIZONTAL, label="WPM",
                                   command=self.update_wpm, bg=self.get_bg_color(), fg=self.get_fg_color())
        self.wpm_slider.set(self.wpm)
        self.wpm_slider.pack(side=tk.LEFT, padx=5, pady=5)

        self.speed_up_btn = tk.Button(self.row1, text="+", command=self.increase_speed, width=3)
        self.speed_up_btn.pack(side=tk.LEFT, padx=2, pady=5)

        # Font Dropdown Row 1
        tk.Label(self.row1, text="Font:", bg=self.get_bg_color(), fg=self.get_fg_color()).pack(side=tk.LEFT, padx=5)
        self.font_var = tk.StringVar(value=self.font_family)
        self.font_dropdown = ttk.Combobox(self.row1, textvariable=self.font_var, width=15)
        self._update_font_list()
        self.font_dropdown.bind("<<ComboboxSelected>>", self._on_font_selected)
        self.font_dropdown.pack(side=tk.LEFT, padx=5)

        self.equalizer_button = tk.Button(self.row1, text="Equalizer", command=self.open_equalizer)
        self.equalizer_button.pack(side=tk.LEFT, padx=5, pady=5)

        self.image_settings_btn = tk.Button(self.row1, text="⚙", command=self.open_image_settings, width=2)
        self.image_settings_btn.pack(side=tk.LEFT, padx=2, pady=5)

        # Row 2: Modes & Extraction
        self.variable_speed_var = tk.BooleanVar(value=self.variable_speed)
        self.variable_speed_var.trace_add("write", self._update_variable_speed)
        self.variable_speed_check = tk.Checkbutton(self.row2, text="Variable Speed", variable=self.variable_speed_var,
                                                   bg=self.get_bg_color(), fg=self.get_fg_color())
        self.variable_speed_check.pack(side=tk.LEFT, padx=5, pady=5)

        self.bionic_var = tk.BooleanVar(value=self.use_bionic_bolding)
        self.bionic_check = tk.Checkbutton(self.row2, text="Bionic", variable=self.bionic_var, command=self._toggle_bionic,
                                           bg=self.get_bg_color(), fg=self.get_fg_color())
        self.bionic_check.pack(side=tk.LEFT, padx=5, pady=5)

        self.intel_pause_var = tk.BooleanVar(value=self.use_intelligent_pauses)
        self.intel_pause_check = tk.Checkbutton(self.row2, text="Smart Pauses", variable=self.intel_pause_var, command=self._toggle_intel_pause,
                                                bg=self.get_bg_color(), fg=self.get_fg_color())
        self.intel_pause_check.pack(side=tk.LEFT, padx=5, pady=5)

        self.extract_images_var = tk.BooleanVar(value=self.extract_images)
        self.extract_images_check = tk.Checkbutton(self.row2, text="Enable Image Extraction", variable=self.extract_images_var, command=self._toggle_extract_images,
                                                  bg=self.get_bg_color(), fg=self.get_fg_color())
        self.extract_images_check.pack(side=tk.LEFT, padx=5, pady=5)

        self.night_mode_var = tk.BooleanVar(value=(self.theme == "dark"))
        self.night_mode_check = tk.Checkbutton(self.row2, text="Night Mode", variable=self.night_mode_var, command=self._toggle_night_mode,
                                               bg=self.get_bg_color(), fg=self.get_fg_color())
        self.night_mode_check.pack(side=tk.LEFT, padx=5, pady=5)

        # Row 3: Tools
        self.library_button = tk.Button(self.row3, text="Library", command=self.open_library, bg="#2196F3", fg="white", font=("Helvetica", 9, "bold"))
        self.library_button.pack(side=tk.LEFT, padx=5, pady=5)

        self.tag_button = tk.Button(self.row3, text="Tag Word", command=self.tag_current_word)
        self.tag_button.pack(side=tk.LEFT, padx=5, pady=5)

        self.lookup_button = tk.Button(self.row3, text="Lookup (Ctrl+L)", command=self.lookup_current_word)
        self.lookup_button.pack(side=tk.LEFT, padx=5, pady=5)

        self.image_button = tk.Button(self.row3, text="Open Image Gallery", command=self.show_epub_images, state="disabled")
        self.image_button.pack(side=tk.LEFT, padx=5, pady=5)
        
        # Navigation Row
        self.nav_row = tk.Frame(self.control_frame, bg=self.get_bg_color())
        self.nav_row.pack(fill=tk.X)
        
        tk.Button(self.nav_row, text="<< 1 min", command=lambda: self.skip_time(-1)).pack(side=tk.LEFT, padx=5)
        tk.Button(self.nav_row, text="1 min >>", command=lambda: self.skip_time(1)).pack(side=tk.LEFT, padx=5)
        tk.Button(self.nav_row, text="Skip Intro (5m) >>", command=lambda: self.skip_time(5)).pack(side=tk.LEFT, padx=5)

    def skip_time(self, minutes):
        # Estimate words based on WPM
        words_to_skip = int(self.wpm * minutes)
        new_index = self.current_index + words_to_skip
        self.current_index = max(0, min(new_index, len(self.words) - 1))
        self.update_display()

    def _update_variable_speed(self, *args):
        self.variable_speed = self.variable_speed_var.get()

    def get_bg_color(self):
        if self.contrast_mode == "high": return "black"
        if self.contrast_mode == "sepia": return "#f4ecd8"
        return "white" if self.theme == "light" else "#2e2e2e"
    
    def get_fg_color(self):
        if self.contrast_mode == "high": return "yellow"
        if self.contrast_mode == "sepia": return "#5b4636"
        return "black" if self.theme == "light" else "white"

    def _on_font_selected(self, event):
        selected = self.font_var.get()
        if selected == "Load more...":
            self._load_all_system_fonts()
        elif selected == "Import font file...":
            self._import_font_file()
        else:
            self.font_family = selected
            self.update_display()

    def _update_font_list(self, include_all=False):
        office_fonts = ["Arial", "Comic Sans MS", "Calibri", "Helvetica", "Times New Roman"]
        if include_all:
            system_fonts = sorted(list(set(font.families())))
            self.font_dropdown['values'] = office_fonts + ["---"] + system_fonts
        else:
            self.font_dropdown['values'] = office_fonts + ["---", "Load more...", "Import font file..."]

    def _load_all_system_fonts(self):
        self._update_font_list(include_all=True)
        self.font_dropdown.event_generate('<Button-1>') # Open it

    def _import_font_file(self):
        fpath = filedialog.askopenfilename(filetypes=[("Font Files", "*.ttf *.otf")])
        if fpath:
            # Note: Tkinter doesn't easily load external font files without being installed on OS.
            # However, we can use the filename as family name if we assume it's installed or
            # just notify the user. Advanced: use specific extra libs.
            messagebox.showinfo("Font Import", f"To use '{os.path.basename(fpath)}', ensure it is installed on your system. You can then select it from 'Load more...'.")

    def _toggle_bionic(self):
        self.use_bionic_bolding = self.bionic_var.get()
        self.update_display()

    def _toggle_intel_pause(self):
        self.use_intelligent_pauses = self.intel_pause_var.get()

    def _toggle_extract_images(self):
        self.extract_images = self.extract_images_var.get()
        if self.extract_images and (self.epub_images or self.file_path):
             # Enable button if we have things to show, or if we need to reload to find them
             self.image_button.config(state="normal")
        else:
             self.image_button.config(state="disabled")

    def _toggle_night_mode(self):
        self.theme = "dark" if self.night_mode_var.get() else "light"
        self.update_theme()
        self.update_display()

    def bind_keys(self):
        self.bind("<space>", lambda event: self.toggle_play_pause())
        self.bind("<Left>", lambda event: self.rewind_word())
        self.bind("<Right>", lambda event: self.forward_word())
        self.bind("<Control-o>", lambda event: self.open_file())
        self.bind("<Control-s>", lambda event: self.save_session())
        self.bind("<Control-l>", lambda event: self.lookup_current_word())
        self.bind("t", lambda event: self.tag_current_word())
        self.bind("<plus>", lambda event: self.increase_speed())
        self.bind("<equal>", lambda event: self.increase_speed())
        self.bind("<minus>", lambda event: self.decrease_speed())
        self.bind("<underscore>", lambda event: self.decrease_speed())
        self.bind("<MouseWheel>", self.on_mouse_wheel)

    def on_mouse_wheel(self, event):
        if event.delta > 0:
            self.increase_speed()
        else:
            self.decrease_speed()

    def increase_speed(self):
        new_wpm = min(1000, self.wpm + 25)
        self.wpm_slider.set(new_wpm)

    def decrease_speed(self):
        new_wpm = max(100, self.wpm - 25)
        self.wpm_slider.set(new_wpm)


    def update_theme(self):
        bg = self.get_bg_color()
        fg = self.get_fg_color()
        self.display_frame.config(bg=bg)
        self.word_canvas.config(bg=bg)
        self.progress_label.config(bg=bg, fg=fg)
        self.preview_text.config(bg=bg, fg=fg)
        self.control_frame.config(bg=bg)
        self.row1.config(bg=bg)
        self.row2.config(bg=bg)
        self.row2.config(bg=bg)
        self.row3.config(bg=bg)
        if hasattr(self, 'nav_row'): self.nav_row.config(bg=bg)
        self.wpm_slider.config(bg=bg, fg=fg)
        self.variable_speed_check.config(bg=bg, fg=fg)
        self.bionic_check.config(bg=bg, fg=fg)
        self.intel_pause_check.config(bg=bg, fg=fg)
        self.extract_images_check.config(bg=bg, fg=fg)
        self.night_mode_check.config(bg=bg, fg=fg)

    def open_file(self):
        filetypes = [("Supported Files", "*.txt *.pdf *.docx *.epub *.azw3 *.mobi")]
        filename = filedialog.askopenfilename(filetypes=filetypes)
        if filename:
            self.file_path = filename
            
            # Show Progress Window
            self.progress_win = tk.Toplevel(self)
            self.progress_win.title("Loading...")
            self.progress_win.geometry("350x120")
            tk.Label(self.progress_win, text=f"Processing {os.path.basename(filename)}...", wraplength=250).pack(pady=10)
            self.loading_bar = ttk.Progressbar(self.progress_win, mode='indeterminate')
            self.loading_bar.pack(fill="x", padx=20, pady=5)
            self.loading_bar.start(10)
            
            # Run loading in background
            threading.Thread(target=self._load_file_thread, args=(filename,), daemon=True).start()

    def _load_file_thread(self, filename):
        try:
            # Check Cache
            file_hash = self.get_file_hash(filename)
            cache_path = os.path.join(CACHE_DIR, file_hash)
            
            full_text = None
            cached = False
            
            if os.path.exists(os.path.join(cache_path, "content.txt")):
                 try:
                     logging.info("Loading from cache...")
                     full_text = self.load_from_cache(cache_path)
                     cached = True
                 except Exception as e:
                     logging.error(f"Cache load failed: {e}")
            
            if not full_text:
                full_text = self.load_file_content(filename)
                # Save to Cache
                self.save_to_cache(cache_path, full_text)

            # Update UI on Main Thread
            self.after(0, lambda: self._finalize_load(filename, full_text))
            
        except Exception as e:
            logging.exception("Background load failed")
            self.after(0, lambda: messagebox.showerror("Error", f"Failed to load file: {e}"))
        finally:
             if hasattr(self, 'progress_win') and self.progress_win.winfo_exists():
                 self.after(0, self.progress_win.destroy)

    def _finalize_load(self, filename, text):
        self.text_content = text
        self.words = self.process_text(self.text_content)
        self.current_index = 0
        
        # Load session position if exists
        self.load_session_for_file(filename)
        
        self.update_library_metadata(filename)
        self.update_display()
        self.title(f"Speed Reading App - {os.path.basename(filename)}")
        
        # Enable/Disable Image Button
        if self.epub_images:
            self.image_button.config(state="normal")
            self.image_button.config(text=f"Open Gallery ({len(self.epub_images)})")
        else:
            self.image_button.config(state="disabled")
            self.image_button.config(text="No Images")
            
        logging.info(f"Loaded: {filename}")

    def get_file_hash(self, filepath):
        h = hashlib.sha256()
        with open(filepath, "rb") as f:
            for chunk in iter(lambda: f.read(4096), b""):
                h.update(chunk)
        return h.hexdigest()

    def save_to_cache(self, cache_path, text):
        if not os.path.exists(cache_path):
            os.makedirs(cache_path)
        
        # Save Text
        with open(os.path.join(cache_path, "content.txt"), "w", encoding="utf-8") as f:
            f.write(text)
            
        # Save Metadata (Image locs)
        meta = {"image_locations": self.image_locations, "image_names": self.epub_image_names}
        with open(os.path.join(cache_path, "metadata.json"), "w", encoding="utf-8") as f:
            json.dump(meta, f)
            
        # Save Images
        img_dir = os.path.join(cache_path, "images")
        if not os.path.exists(img_dir):
            os.makedirs(img_dir)
            
        for i, img in enumerate(self.epub_images):
            try:
                # Save as PNG
                img.save(os.path.join(img_dir, f"img_{i}.png"))
            except: pass

    def load_from_cache(self, cache_path):
        # Load Text
        with open(os.path.join(cache_path, "content.txt"), "r", encoding="utf-8") as f:
            text = f.read()
            
        # Load Metadata
        try:
            with open(os.path.join(cache_path, "metadata.json"), "r", encoding="utf-8") as f:
                meta = json.load(f)
                self.image_locations = meta.get("image_locations", {})
                self.epub_image_names = meta.get("image_names", [])
        except: 
            self.image_locations = {}
            self.epub_image_names = []
            
        # Load Images
        self.epub_images = []
        img_dir = os.path.join(cache_path, "images")
        if os.path.exists(img_dir) and self.epub_image_names:
            # We assume order matches list
            for i in range(len(self.epub_image_names)):
                p = os.path.join(img_dir, f"img_{i}.png")
                if os.path.exists(p):
                    self.epub_images.append(Image.open(p))
                else:
                    # Fallback placeholder?
                    self.epub_images.append(Image.new('RGB', (100, 100), color='gray'))
                    
        return text

    def load_file_content(self, filepath):
        ext = os.path.splitext(filepath)[1].lower()
        if ext == ".txt":
            with open(filepath, "r", encoding="utf-8") as f:
                return f.read()
        elif ext == ".pdf":
            try:
                pdfminer_logger = logging.getLogger("pdfminer")
                pdfminer_logger.setLevel(logging.ERROR)
                text = ""
                self.image_locations = {}
                current_word_count = 0
                
                with pdfplumber.open(filepath) as pdf:
                    if self.extract_images:
                        self.epub_images = []
                        self.epub_image_names = []
                    
                    for page in pdf.pages:
                        # Text Extraction
                        # layout=True helps preserve multi-column order
                        page_text = page.extract_text(layout=True)
                        if page_text:
                            text += page_text + "\n"
                            # Count words added
                            page_words = len(self.process_text(page_text))
                        else:
                            page_words = 0
                        
                        # Image Extraction (Mapped to start of page)
                        if self.extract_images:
                            page_images_found = False
                            for img in page.images:
                                try:
                                    if img['width'] >= self.min_img_width and img['height'] >= self.min_img_height:
                                        # Clamp BBox to Page Dimensions (Handling offset origins like 36, -36)
                                        # page.bbox is (x0, top, x1, bottom) convention? 
                                        # pdfplumber.page.bbox is (x0, bottom, x1, top) usually?
                                        # Let's trust the error message: "parent page bounding box (36, -36, 567, 630)"
                                        # This looks like (x0, y0, x1, y1).
                                        
                                        p_bbox = page.bbox # (x0, bottom, x1, top)
                                        p_x0, p_bottom, p_x1, p_top = p_bbox
                                        
                                        # Image coords are usually PDF space (y0=bottom)
                                        i_x0 = img['x0']
                                        i_x1 = img['x1']
                                        i_y0 = img['y0']
                                        i_y1 = img['y1']
                                        
                                        # Clamp to page horizontal
                                        c_x0 = max(p_x0, min(i_x0, p_x1))
                                        c_x1 = max(p_x0, min(i_x1, p_x1))
                                        
                                        # Clamp to page vertical
                                        c_y0 = max(p_bottom, min(i_y0, p_top))
                                        c_y1 = max(p_bottom, min(i_y1, p_top))
                                        
                                        # If dimensions invalid, skip
                                        if c_x1 <= c_x0 or c_y1 <= c_y0:
                                           continue
                                           
                                        # Convert to crop bbox (x0, top, x1, bottom) required by within_bbox/crop?
                                        # pdfplumber .crop() args are (x0, top, x1, bottom).
                                        # "top" here means distance from top of page? Or Top Y coordinate?
                                        # "The bounding box ... relative to the top-left of the page." matches the error?
                                        # No, the error (36, -36, 567, 630) looks like raw PDF coords.
                                        
                                        # Let's try passing the raw PDF coords to a crop method?
                                        # page.crop(bbox) takes (x0, top, x1, bottom).
                                        
                                        # Calculations for "Top-Left relative":
                                        # T = page_height - y1 + (maybe offset)
                                        # Actually, pdfplumber handles this transformation.
                                        # If we use .within_bbox((c_x0, p_top - c_y1, c_x1, p_top - c_y0)) ??
                                        
                                        # Simplification: The previous error said "Bounding box ... not fully within".
                                        # The error came from "within_bbox".
                                        # Let's just catch the error and continue to the next image, 
                                        # BUT ensure we don't set page_images_found = True if it fails.
                                        
                                        # Better approach:
                                        # Just use robust try/except logic to fallback to Snapshot if specific image extraction fails.
                                        
                                        # We accept the clampping we did above (c_x0 etc) but constructing the crop box is tricky without knowing exact origin logic.
                                        # Let's rely on the fallback.
                                        # Normalize coordinates to ensure (min, min, max, max)
                                        x_coords = sorted([c_x0, c_x1])
                                        y_coords = sorted([c_y0, c_y1])
                                        # pdfplumber expects (x0, top, x1, bottom) relative to page top-left? 
                                        # Or (x0, bottom, x1, top) relative to bottom-left?
                                        # The error "negative width or height" implies we sent (large, small) or similar.
                                        # If we send (min, min, max, max) to .within_bbox, it should work for standard Rect objects.
                                        
                                        bbox = (x_coords[0], y_coords[0], x_coords[1], y_coords[1])
                                        
                                        # Use standard crop
                                        cropped = page.within_bbox(bbox).to_image()
                                        
                                        # Naming: Figure X
                                        fig_num = len(self.epub_images) + 1
                                        img_name = f"Figure {fig_num} (Pg {page.page_number})"
                                        
                                        self.epub_images.append(cropped.original)
                                        self.epub_image_names.append(img_name)
                                        self.image_locations[img_name] = current_word_count
                                        page_images_found = True
                                        
                                except Exception as e_img:
                                    # Fallback: Just skip this specific image if it fails.
                                    # We do NOT want to fail the whole load.
                                    logging.debug(f"Skipped PDF image extract: {e_img}")
                                    continue
                            
                            # Fallback: If no images found on page (likely vector graphics), render full page
                            if not page_images_found:
                                try:
                                    # Render page at 150 DPI for clarity
                                    pix = page.to_image(resolution=150)
                                    fig_num = len(self.epub_images) + 1
                                    img_name = f"Page {page.page_number} Snapshot"
                                    
                                    self.epub_images.append(pix.original)
                                    self.epub_image_names.append(img_name)
                                    self.image_locations[img_name] = current_word_count
                                except Exception as e:
                                    logging.error(f"Failed to render page snapshot: {e}")
                                    # Alert user once if snapshot fails
                                    logging.error(f"Failed to render page snapshot: {e}")
                                    # Alert user if snapshot fails (limit to one alert per session to avoid spam)
                                    if not hasattr(self, '_snapshot_error_shown'):
                                         messagebox.showwarning("Image Error", f"Failed to capture page snapshot.\nError: {e}\nEnsure 'pdfplumber' and dependencies are installed.")
                                         self._snapshot_error_shown = True
                        
                        current_word_count += page_words
                
                if text.strip() == "":
                    raise Exception("PDF Loading failed - no text found.")
                
                # Debug Summary
                if self.extract_images:
                     msg = f"PDF Loaded.\nExtracted {len(self.epub_images)} images/snapshots."
                     if not self.epub_images:
                         msg += "\n(No images found or all failed to extract)"
                     messagebox.showinfo("Debug Summary", msg)
                     logging.info(msg)

                return text
            except Exception as e:
                logging.exception("PDF loading failed")
                raise Exception("PDF Loading failed") from e
        elif ext == ".docx":
            try:
                doc = docx.Document(filepath)
                return "\n".join(para.text for para in doc.paragraphs)
            except Exception as e:
                logging.exception("DOCX loading failed")
                raise Exception("DOCX Loading failed") from e
        elif ext == ".epub":
            return self.load_epub_manual(filepath)
        elif ext == ".mobi":
            return self.load_mobi(filepath)
        elif ext == ".azw3":
            return self.load_azw3(filepath)
        else:
            raise Exception("Unsupported file format")

    def import_pdf_manual(self):
        filename = filedialog.askopenfilename(filetypes=[("PDF Files", "*.pdf")])
        if filename:
             editor = ManualExtractionEditor(self, filename)
             self.wait_window(editor.top)
             if editor.extracted_text:
                 # Transfer images
                 self.epub_images = editor.extracted_images
                 self.epub_image_names = editor.extracted_image_names
                 self.image_locations = editor.extracted_locations
                 
                 self._finalize_load(filename, editor.extracted_text)

    def load_mobi(self, filepath):
        """Extract text from MOBI files using the mobi library."""
        try:
            tempdir, out_html = mobi.extract(filepath)
            # tempdir is where images/assets might be, out_html is the combined HTML
            with open(out_html, 'r', encoding='utf-8', errors='ignore') as f:
                html_data = f.read()
            # We can use our existing HTML extractor
            return self.extract_text_from_html(html_data)
        except Exception as e:
            logging.exception("MOBI loading failed")
            raise Exception(f"MOBI Loading failed: {e}")

    def load_azw3(self, filepath):
        """Extract text from AZW3 files. Often AZW3 is just a wrapper around KF8 (similar to EPUB)."""
        try:
            # ebooklib can often handle AZW3 if it's KF8
            book = epub.read_epub(filepath)
            text = ""
            for item in book.get_items_of_type(ebooklib.ITEM_DOCUMENT):
                html_data = item.get_content().decode('utf-8', errors='ignore')
                text += self.extract_text_from_html(html_data) + "\n\n"
            return text
        except Exception as e:
            logging.exception("AZW3 loading failed")
            # Fallback to MOBI extractor if it's an older Kindle format
            try:
                logging.info("Attempting fallback to MOBI extractor for AZW3")
                return self.load_mobi(filepath)
            except:
                raise Exception(f"AZW3 Loading failed: {e}")

    def extract_text_from_html(self, html_data):
        return self.extract_text_with_images(html_data)[0]

    def extract_text_with_images(self, html_data, current_word_base=0):
        """
        Extract text AND map image locations.
        Returns (text, {img_src: word_index}).
        """
        soup = BeautifulSoup(html_data, "html.parser")
        for tag in soup(["script", "style"]):
            tag.decompose()
        
        text_content = ""
        local_img_locs = {}
        
        # Traverse elements to approximate location
        # This is a simplified traversal
        running_word_count = current_word_base
        
        for element in soup.descendants:
            if isinstance(element, str):
                t = element.strip()
                if t:
                    text_content += t + " "
                    # Count words in this chunk
                    added_words = len(t.split()) # simple split
                    running_word_count += added_words
            elif element.name == 'img':
                src = element.get('src')
                if src:
                    local_img_locs[src] = running_word_count

        return text_content.strip(), local_img_locs

    def load_epub_manual(self, filepath):
        """
        Manually parse an EPUB file:
         - Open the ZIP archive.
         - Read META-INF/container.xml to find the OPF file.
         - Parse the OPF to get manifest items.
         - Use the <spine> element (if present) to determine the reading order.
         - Extract text from XHTML/HTML items in reading order.
         - Extract images from items with media type starting with "image/".
        Returns the concatenated text content.
        """
        try:
            epub_zip = zipfile.ZipFile(filepath, 'r')
        except Exception as e:
            raise Exception(f"Failed to open EPUB: {e}")
        # Read container.xml to get OPF file path
        try:
            container_data = epub_zip.read("META-INF/container.xml")
            container_root = ET.fromstring(container_data)
            rootfile = container_root.find(".//{urn:oasis:names:tc:opendocument:xmlns:container}rootfile")
            if rootfile is None:
                raise Exception("No rootfile found in container.xml")
            opf_path = rootfile.attrib.get("full-path")
            if not opf_path:
                raise Exception("OPF file path not found.")
        except Exception as e:
            raise Exception(f"Error reading container.xml: {e}")
        # Parse the OPF file
        try:
            opf_data = epub_zip.read(opf_path)
            opf_root = ET.fromstring(opf_data)
            # Try to get manifest (first without namespace, then with)
            manifest = opf_root.find("manifest")
            ns = {}
            if manifest is None and opf_root.tag.startswith("{"):
                ns_uri = opf_root.tag.split('}')[0].strip('{')
                ns = {'opf': ns_uri}
                manifest = opf_root.find("opf:manifest", ns)
            if manifest is None:
                raise Exception("No manifest found in OPF.")
        except Exception as e:
            raise Exception(f"Error parsing OPF: {e}")
        # Build a dictionary mapping manifest id to href
        manifest_dict = {}
        for item in manifest.findall("item") if manifest is not None else []:
            id_attr = item.attrib.get("id")
            href = item.attrib.get("href")
            if id_attr and href:
                manifest_dict[id_attr] = href

        # Determine reading order using the spine
        spine = opf_root.find("spine")
        reading_order = []
        if spine is not None:
            for itemref in spine.findall("itemref"):
                idref = itemref.attrib.get("idref")
                href = manifest_dict.get(idref)
                if href:
                    reading_order.append(href)
        else:
            # Fallback: use all manifest items with .html or .xhtml extensions.
            reading_order = [href for href in manifest_dict.values() if href.lower().endswith((".html", ".xhtml"))]

        # Extract text from each file in reading order.
        all_text = ""
        current_word_count = 0
        self.image_locations = {}
        
        for item in reading_order:
            try:
                base_path = os.path.dirname(opf_path)
                full_path = os.path.join(base_path, item) if base_path else item
                html_data = epub_zip.read(full_path).decode("utf-8", errors="ignore")
                
                # Extract text and image locations
                chunk_text, chunk_locs = self.extract_text_with_images(html_data, current_word_count)
                self.image_locations.update(chunk_locs)
                
                logging.debug(f"Processed text item '{item}': extracted length = {len(chunk_text)}")
                all_text += chunk_text + "\n\n"
                current_word_count += len(self.process_text(chunk_text))
            except Exception as e:
                logging.error(f"Error processing text item {item}: {e}")
                
        if not all_text.strip():
            logging.warning("No text was extracted from the EPUB.")
        logging.info(f"Total text length extracted: {len(all_text)} characters")
        
        # Extract images from all manifest items with media type starting with "image/"
        self.epub_images = []
        self.epub_image_names = []
        if self.extract_images:
            for item in manifest.findall("item") if manifest is not None else []:
                href = item.attrib.get("href")
                media_type = item.attrib.get("media-type", "")
                if media_type.startswith("image/") and href:
                    try:
                        base_path = os.path.dirname(opf_path)
                        full_path = os.path.join(base_path, href) if base_path else href
                        img_data = epub_zip.read(full_path)
                        img = Image.open(io.BytesIO(img_data))
                        if img.width >= self.min_img_width and img.height >= self.min_img_height:
                            self.epub_images.append(img)
                            self.epub_image_names.append(href)
                            logging.debug(f"Extracted image '{href}'")
                    except Exception as e:
                        logging.error(f"Error processing image item {href}: {e}")
        epub_zip.close()
        return all_text

    def process_text(self, text):
        """
        Process text into a list of words.
        Uses a regex split so that paragraph breaks ("\n\n") are preserved.
        """
        text = text.replace("\r", "\n")
        words = []
        parts = re.split(r'(\n\n)', text)
        for part in parts:
            if part == "\n\n":
                words.append(part)
            else:
                words.extend(part.split())
        logging.debug(f"Total words after processing: {len(words)}")
        return words

    def update_display(self):
        """Update word canvas, preview text, and progress indicator."""
        self.word_canvas.delete("all")
        if not self.words or self.current_index >= len(self.words):
            return
            
        # Sync Image Gallery if open and autoscroll enabled
        if hasattr(self, 'gallery') and self.gallery and self.gallery.top.winfo_exists() and self.gallery.autoscroll_var.get():
           self.gallery.sync_scroll(self.current_index)

        current_word = self.words[self.current_index]
        self.word_canvas.update_idletasks()
        canvas_width = self.word_canvas.winfo_width() or self.word_canvas.winfo_reqwidth()
        canvas_height = self.word_canvas.winfo_height() or self.word_canvas.winfo_reqheight()
        display_font = font.Font(family=self.font_family, size=self.font_size)
        text_id = self.word_canvas.create_text(canvas_width/2, canvas_height/2, text=current_word, font=display_font,
                                               fill=self.get_fg_color())
        bbox = self.word_canvas.bbox(text_id)
        if bbox:
            x1, y1, x2, y2 = bbox
            if self.fixation_mode == "start":
                fixation_x = x1
            elif self.fixation_mode == "middle":
                fixation_x = (x1+x2)/2
            elif self.fixation_mode == "end":
                fixation_x = x2
            else:
                fixation_x = (x1+x2)/2
            marker_y = y2 + 5
            self.word_canvas.create_line(fixation_x, marker_y, fixation_x, marker_y+20, fill=self.highlight_color, width=2)
        
        # Bionic Bolding Overwrite
        if self.use_bionic_bolding:
            self.word_canvas.delete(text_id)
            # Split word into bold/regular
            cut = max(1, len(current_word) // 2)
            if len(current_word) <= 3: cut = 1
            bold_part = current_word[:cut]
            reg_part = current_word[cut:]
            
            bold_font = font.Font(family=self.font_family, size=self.font_size, weight="bold")
            reg_font = font.Font(family=self.font_family, size=self.font_size)
            
            # Calculate positions to keep centered
            full_w = bold_font.measure(bold_part) + reg_font.measure(reg_part)
            start_x = (canvas_width - full_w) / 2
            
            self.word_canvas.create_text(start_x, canvas_height/2, text=bold_part, font=bold_font,
                                          fill=self.get_fg_color(), anchor="w")
            self.word_canvas.create_text(start_x + bold_font.measure(bold_part), canvas_height/2, text=reg_part, font=reg_font,
                                          fill=self.get_fg_color(), anchor="w")
        
        # Middle Letter Highlighting Logic
        elif self.fixation_mode == "middle" and not self.use_bionic_bolding:
             self.word_canvas.delete(text_id) # Remove default
             
             mid_idx = len(current_word) // 2
             left_part = current_word[:mid_idx]
             middle_char = current_word[mid_idx]
             right_part = current_word[mid_idx+1:]
             
             base_font = font.Font(family=self.font_family, size=self.font_size)
             left_w = base_font.measure(left_part)
             mid_w = base_font.measure(middle_char)
             right_w = base_font.measure(right_part)
             
             total_w = left_w + mid_w + right_w
             start_x = (canvas_width - total_w) / 2
             
             # Draw Left
             self.word_canvas.create_text(start_x, canvas_height/2, text=left_part, font=base_font, fill=self.get_fg_color(), anchor="w")
             # Draw Middle (Highlighted)
             self.word_canvas.create_text(start_x + left_w, canvas_height/2, text=middle_char, font=base_font, fill=self.highlight_color, anchor="w")
             # Draw Right
             self.word_canvas.create_text(start_x + left_w + mid_w, canvas_height/2, text=right_part, font=base_font, fill=self.get_fg_color(), anchor="w")

        # Update preview text (showing up to 50 upcoming words)
        preview_words = self.words[self.current_index:self.current_index+50]
        self.preview_text.config(state=tk.NORMAL)
        self.preview_text.delete("1.0", tk.END)
        preview_str = " ".join(preview_words)
        self.preview_text.insert(tk.END, preview_str)
        current_word_start = preview_str.find(current_word)
        if current_word_start != -1:
            current_word_end = current_word_start + len(current_word)
            start_index = "1.0+" + str(current_word_start) + "c"
            end_index = "1.0+" + str(current_word_end) + "c"
            self.preview_text.tag_add("current", start_index, end_index)
            self.preview_text.tag_config("current", background=self.highlight_color, foreground="white")
        self.preview_text.config(state=tk.DISABLED)
        progress = (self.current_index / len(self.words)) * 100
        remaining_words = len(self.words) - self.current_index
        remaining_time = remaining_words / (self.wpm / 60) if self.wpm > 0 else 0
        minutes = int(remaining_time // 60)
        seconds = int(remaining_time % 60)
        self.progress_label.config(text=f"Progress: {progress:.1f}% - ETA: {minutes}m {seconds}s")

    def update_wpm(self, val):
        try:
            self.wpm = int(val)
        except Exception:
            self.wpm = 300

    def toggle_play_pause(self):
        self.playing = not self.playing
        if self.playing:
            if not hasattr(self, 'reader_thread') or not self.reader_thread.is_alive():
                self.reader_thread = threading.Thread(target=self.run_speed_reader, daemon=True)
                self.reader_thread.start()

    def run_speed_reader(self):
        try:
            while self.playing and self.current_index < len(self.words):
                current_word = self.words[self.current_index]
                delay = 60 / self.wpm
                if self.variable_speed:
                    if len(current_word) > 7:
                        delay *= 1.2
                    if current_word.endswith(('.', '!', '?')):
                        delay *= 1.5
                    elif current_word.endswith((',', ';', ':')):
                        delay *= 1.2
                        delay += self.pause_paragraph / 1000.0
                
                if self.use_intelligent_pauses:
                    # Sane defaults or Equalizer values
                    # Check for full pause characters
                    if any(current_word.endswith(c) for c in self.full_pause_chars):
                        delay *= self.pause_multipliers.get("period", 2.0)
                    # Check for short pause characters
                    elif any(current_word.endswith(c) for c in self.short_pause_chars):
                        delay *= self.pause_multipliers.get("short", 1.5)
                    
                    if len(current_word) > self.long_word_threshold:
                        delay *= self.pause_multipliers.get("long_word", 1.2)
                    
                    if current_word == "\n\n":
                        delay *= self.pause_multipliers.get("paragraph", 3.0)

                    # Numbers
                    if any(c.isdigit() for c in current_word):
                        delay *= self.pause_multipliers.get("numbers", 1.5)
                    
                    # Hyphens
                    if "-" in current_word:
                        delay *= self.pause_multipliers.get("hyphens", 1.3)
                    
                    # Custom Categories
                    if self.custom1_chars and any(c in self.custom1_chars for c in current_word):
                        delay *= self.pause_multipliers.get("custom1", 1.0)
                    
                    # Custom 2: String List match
                    if self.custom2_chars:
                        clean_word = current_word.strip(string.punctuation).lower()
                        string_list = [s.strip().lower() for s in self.custom2_chars.split(",")]
                        if clean_word in string_list:
                            delay *= self.pause_multipliers.get("custom2", 1.0)

                    if self.custom3_regex_pattern:
                        try:
                            if re.search(self.custom3_regex_pattern, current_word):
                                delay *= self.pause_multipliers.get("custom3_regex", 1.0)
                        except: pass

                self.after(0, self.update_display)
                time.sleep(delay)
                self.current_index += 1
            self.playing = False
        except Exception as e:
            logging.exception("Error in speed reader thread")
            self.playing = False

    def rewind_word(self):
        self.current_index = max(0, self.current_index - 1)
        self.update_display()

    def forward_word(self):
        if self.current_index < len(self.words) - 1:
            self.current_index += 1
            self.update_display()

    def tag_current_word(self):
        if self.words and self.current_index < len(self.words):
            word = self.words[self.current_index]
            self.tagged_words.add(word)
            messagebox.showinfo("Tagged", f"Tagged word: {word}")
            logging.info(f"Tagged word: {word}")

    def lookup_current_word(self):
        if self.words and self.current_index < len(self.words):
            word = self.words[self.current_index]
            clean_word = word.strip(string.punctuation)
            url = f"https://en.wiktionary.org/wiki/{clean_word}"
            webbrowser.open(url)
            logging.info(f"Lookup for word: {clean_word} opened in browser.")

    def open_preferences(self):
        pref = PreferencesDialog(self)
        self.wait_window(pref.top)
        self.update_theme()
        self.update_display()

    def open_equalizer(self):
        eq = PauseEqualizerDialog(self)
        self.wait_window(eq.top)

    def show_epub_images(self):
        if not self.epub_images:
            return
        # Class name is AdvancedImageGallery based on file
        gallery = AdvancedImageGallery(self, self.epub_images, self.epub_image_names)

    def open_image_settings(self):
        isett = ImageSettingsDialog(self)
        self.wait_window(isett.top)

    def get_session_path(self, file_path):
        if not file_path: return SESSION_FILE
        h = hashlib.sha256(file_path.encode('utf-8')).hexdigest()
        return os.path.join(SESSIONS_DIR, f"session_{h}.json")

    def save_session(self):
        if not self.file_path:
            messagebox.showwarning("No File", "No file is loaded to save session.")
            return
        session_data = {
            "file_path": self.file_path,
            "current_index": self.current_index,
            "wpm": self.wpm,
            "fixation_mode": self.fixation_mode,
            "theme": self.theme,
            "font_size": self.font_size,
            "font_family": self.font_family,
            "highlight_color": self.highlight_color,
            "tagged_words": list(self.tagged_words),
            "intelligent_pauses": self.use_intelligent_pauses,
            "bionic_bolding": self.use_bionic_bolding,
            "contrast_mode": self.contrast_mode,
            "pause_multipliers": self.pause_multipliers,
            "short_pause_chars": self.short_pause_chars,
            "full_pause_chars": self.full_pause_chars,
            "long_word_threshold": self.long_word_threshold,
            "extract_images": self.extract_images,
            "min_img_width": self.min_img_width,
            "min_img_height": self.min_img_height,
            "custom1_chars": self.custom1_chars,
            "custom2_chars": self.custom2_chars,
            "custom3_regex_pattern": self.custom3_regex_pattern
        }
        
        session_path = self.get_session_path(self.file_path)
        try:
            with open(session_path, "w", encoding="utf-8") as f:
                json.dump(session_data, f)
            
            # Update global index for 'resume last'
            with open(SESSION_FILE, "w", encoding="utf-8") as f:
                json.dump({"last_file": self.file_path}, f)
            
            self.update_library_metadata(self.file_path)
            messagebox.showinfo("Session Saved", f"Session for {os.path.basename(self.file_path)} saved.")
            logging.info(f"Session saved to {session_path}")
        except Exception as e:
            logging.exception("Session saving failed")
            messagebox.showerror("Error", "Failed to save session.")

    def load_last_session(self):
        if not os.path.exists(SESSION_FILE):
            return
        try:
            with open(SESSION_FILE, "r", encoding="utf-8") as f:
                data = json.load(f)
            last_file = data.get("last_file")
            if last_file and os.path.exists(last_file):
                self.load_session_for_file(last_file)
        except: pass

    def load_session_for_file(self, file_path):
        spath = self.get_session_path(file_path)
        if not os.path.exists(spath):
            # Just open the file normally if no session
            self.file_path = file_path
            self.text_content = self.load_file_content(file_path)
            self.words = self.process_text(self.text_content)
            self.current_index = 0
            self.update_library_metadata(file_path)
            self.update_display()
            return

        try:
            with open(spath, "r", encoding="utf-8") as f:
                session_data = json.load(f)
            
            self.file_path = file_path
            self.text_content = self.load_file_content(file_path)
            self.words = self.process_text(self.text_content)
            self.current_index = max(0, session_data.get("current_index", 0) - self.auto_rewind_count)
            self.wpm = session_data.get("wpm", 300)
            self.fixation_mode = session_data.get("fixation_mode", "middle")
            self.theme = session_data.get("theme", "light")
            self.font_size = session_data.get("font_size", 48)
            self.font_family = session_data.get("font_family", "Helvetica")
            self.highlight_color = session_data.get("highlight_color", "red")
            self.tagged_words = set(session_data.get("tagged_words", []))
            self.use_intelligent_pauses = session_data.get("intelligent_pauses", True)
            self.use_bionic_bolding = session_data.get("bionic_bolding", False)
            self.contrast_mode = session_data.get("contrast_mode", "default")
            
            self.pause_multipliers = session_data.get("pause_multipliers", self.pause_multipliers)
            self.short_pause_chars = session_data.get("short_pause_chars", self.short_pause_chars)
            self.full_pause_chars = session_data.get("full_pause_chars", self.full_pause_chars)
            self.long_word_threshold = session_data.get("long_word_threshold", self.long_word_threshold)
            self.extract_images = session_data.get("extract_images", self.extract_images)
            self.min_img_width = session_data.get("min_img_width", self.min_img_width)
            self.min_img_height = session_data.get("min_img_height", self.min_img_height)
            self.custom1_chars = session_data.get("custom1_chars", "")
            self.custom2_chars = session_data.get("custom2_chars", "")
            self.custom3_regex_pattern = session_data.get("custom3_regex_pattern", "")

            self.bionic_var.set(self.use_bionic_bolding)
            self.intel_pause_var.set(self.use_intelligent_pauses)
            self.extract_images_var.set(self.extract_images)
            self.font_var.set(self.font_family)
            
            self.wpm_slider.set(self.wpm)
            self.update_theme()
            self.update_display()
            logging.info(f"Session loaded for {file_path}")
        except Exception as e:
            logging.exception("Session loading failed")
            messagebox.showerror("Error", "Failed to load session.")

    def load_library_metadata(self):
        if os.path.exists(LIBRARY_FILE):
            try:
                with open(LIBRARY_FILE, "r", encoding="utf-8") as f:
                    self.library = json.load(f)
            except: self.library = []
        else:
            self.library = []

    def update_library_metadata(self, file_path):
        self.load_library_metadata()
        found = False
        for item in self.library:
            if item['path'] == file_path:
                item['last_read'] = time.time()
                found = True
                break
        if not found:
            self.library.append({
                "path": file_path,
                "title": os.path.basename(file_path),
                "category": "Uncategorized",
                "last_read": time.time()
            })
        
        try:
            with open(LIBRARY_FILE, "w", encoding="utf-8") as f:
                json.dump(self.library, f, indent=4)
        except Exception as e:
            logging.error(f"Failed to save library metadata: {e}")
            messagebox.showerror("Library Save Error", f"Could not save library: {e}")

    def open_library(self):
        lib = LibraryDialog(self)
        self.wait_window(lib.top)

    def load_session(self):
        self.open_library()

    def on_close(self):
        if self.file_path and messagebox.askokcancel("Quit", "Do you want to save your session before quitting?"):
            self.save_session()
        self.destroy()

    def show_epub_images(self):
        if not self.epub_images:
            messagebox.showinfo("No Images", "No images were found in this file.")
            return
        if hasattr(self, 'gallery') and self.gallery and self.gallery.top.winfo_exists():
            self.gallery.top.lift()
            return

        self.gallery = AdvancedImageGallery(self, self.epub_images, self.epub_image_names)

# ---------------------------------------------------------
# Preferences Dialog
# ---------------------------------------------------------
class PreferencesDialog:
    def __init__(self, parent):
        self.top = tk.Toplevel(parent)
        self.top.title("Preferences")
        self.parent = parent
        tk.Label(self.top, text="Fixation Mode:").pack(pady=5)
        self.fixation_var = tk.StringVar(value=parent.fixation_mode)
        self.fixation_menu = tk.OptionMenu(self.top, self.fixation_var, "start", "middle", "end")
        self.fixation_menu.pack(pady=5)
        tk.Label(self.top, text="Font Size:").pack(pady=5)
        self.font_size_var = tk.IntVar(value=parent.font_size)
        self.font_size_entry = tk.Entry(self.top, textvariable=self.font_size_var)
        self.font_size_entry.pack(pady=5)
        tk.Label(self.top, text="Font Family:").pack(pady=5)
        self.font_family_var = tk.StringVar(value=parent.font_family)
        # Added high-readability fonts for dyslexia
        self.font_family_menu = tk.OptionMenu(self.top, self.font_family_var, "Helvetica", "Arial", "Times", "Courier", "Verdana", "Comic Sans MS", "Trebuchet MS", "Georgia")
        self.font_family_menu.pack(pady=5)
        tk.Label(self.top, text="Theme:").pack(pady=5)
        self.theme_var = tk.StringVar(value=parent.theme)
        self.theme_menu = tk.OptionMenu(self.top, self.theme_var, "light", "dark")
        self.theme_menu.pack(pady=5)
        
        tk.Label(self.top, text="Highlight Color:").pack(pady=5)
        self.highlight_color_var = tk.StringVar(value=parent.highlight_color)
        colors = ["red", "blue", "green", "orange", "purple"]
        self.highlight_menu = tk.OptionMenu(self.top, self.highlight_color_var, *colors)
        self.highlight_menu.pack(pady=5)

        tk.Label(self.top, text="Contrast Mode:").pack(pady=5)
        self.contrast_var = tk.StringVar(value=parent.contrast_mode)
        self.contrast_menu = tk.OptionMenu(self.top, self.contrast_var, "default", "high", "sepia")
        self.contrast_menu.pack(pady=5)
        
        tk.Label(self.top, text="Auto-Rewind Count:").pack(pady=5)
        self.auto_rewind_var = tk.IntVar(value=parent.auto_rewind_count)
        self.auto_rewind_entry = tk.Entry(self.top, textvariable=self.auto_rewind_var)
        self.auto_rewind_entry.pack(pady=5)
        tk.Button(self.top, text="Save", command=self.save_preferences).pack(pady=10)

    def save_preferences(self):
        self.parent.fixation_mode = self.fixation_var.get()
        try:
            self.parent.font_size = int(self.font_size_var.get())
        except Exception:
            self.parent.font_size = 48
        self.parent.font_family = self.font_family_var.get()
        self.parent.theme = self.theme_var.get()
        self.parent.highlight_color = self.highlight_color_var.get()
        self.parent.contrast_mode = self.contrast_var.get()
        try:
            self.parent.auto_rewind_count = int(self.auto_rewind_var.get())
        except Exception:
            self.parent.auto_rewind_count = 5
        self.top.destroy()

# ---------------------------------------------------------
# Image Viewer Window for EPUB Images
# ---------------------------------------------------------
# ---------------------------------------------------------
# Advanced Image Gallery
# ---------------------------------------------------------
class AdvancedImageGallery:
    def __init__(self, parent, images, image_names):
        self.top = tk.Toplevel(parent)
        self.top.title("Image Gallery")
        self.top.geometry("1000x650")
        self.parent = parent
        self.images = images
        self.image_names = image_names
        
        # Build mapping: index -> list of image indices roughly there
        # We need a reverse map for autoscroll: word_index -> closest image index
        self.sorted_locs = []
        self.loc_map = {} # img_idx -> word_index
        
        # Resolve locations
        for idx, name in enumerate(image_names):
            # Try exact match first
            loc = parent.image_locations.get(name)
            if loc is None:
                # Try basename match for relative paths
                try:
                    basename = name.split('/')[-1]
                    # Find any key ending with this basename
                    for key, val in parent.image_locations.items():
                        if key.endswith(basename):
                            loc = val
                            break
                except: pass
            
            if loc is not None:
                self.sorted_locs.append((loc, idx))
                self.loc_map[idx] = loc
            else:
                # If no loc found, default to 0 or sequential
                self.loc_map[idx] = 0
        
        self.sorted_locs.sort() # Sort by word index

        # UI Layout: Three Panes (List, Preview, Context)
        main_paned = tk.PanedWindow(self.top, orient=tk.HORIZONTAL)
        main_paned.pack(fill="both", expand=True, padx=5, pady=5)
        
        # Left Pane: Scrollable Image List
        self.left_frame = tk.Frame(main_paned, width=200, bg="#f0f0f0")
        main_paned.add(self.left_frame)
        
        tk.Label(self.left_frame, text="Images", font=("Helvetica", 10, "bold")).pack(pady=5)
        self.autoscroll_var = tk.BooleanVar(value=False)
        tk.Checkbutton(self.left_frame, text="Autoscroll", variable=self.autoscroll_var).pack(anchor="w", padx=5)

        self.canvas_list = tk.Canvas(self.left_frame, bg="white")
        self.scroll_list = tk.Scrollbar(self.left_frame, orient="vertical", command=self.canvas_list.yview)
        self.list_inner = tk.Frame(self.canvas_list, bg="white")
        
        self.list_inner.bind("<Configure>", lambda e: self.canvas_list.configure(scrollregion=self.canvas_list.bbox("all")))
        self.canvas_list.create_window((0,0), window=self.list_inner, anchor="nw")
        self.canvas_list.configure(yscrollcommand=self.scroll_list.set)
        
        self.scroll_list.pack(side="right", fill="y")
        self.canvas_list.pack(side="left", fill="both", expand=True)

        # Center/Right Pane Split
        right_paned = tk.PanedWindow(main_paned, orient=tk.VERTICAL)
        main_paned.add(right_paned)
        
        # Top Right: Image Preview & Edit
        self.preview_frame = tk.Frame(right_paned, bg="#333")
        right_paned.add(self.preview_frame)
        
        self.img_label = tk.Label(self.preview_frame, bg="#333")
        self.img_label.pack(expand=True, fill="both", pady=10)
        
        self.name_var = tk.StringVar()
        entry_frame = tk.Frame(self.preview_frame, bg="#444")
        entry_frame.pack(fill="x", pady=5)
        tk.Label(entry_frame, text="Figure Label:", fg="white", bg="#444").pack(side="left", padx=5)
        tk.Entry(entry_frame, textvariable=self.name_var).pack(side="left", fill="x", expand=True, padx=5)
        tk.Button(entry_frame, text="Update", command=self.update_label).pack(side="right", padx=5)

        # Bottom Right: Surrounding Text
        self.context_frame = tk.Frame(right_paned, bg="white")
        right_paned.add(self.context_frame)
        
        tk.Label(self.context_frame, text="Context (Surrounding Text)", font=("Helvetica", 10, "bold"), bg="#ddd").pack(fill="x")
        self.context_text = tk.Text(self.context_frame, wrap="word", height=8, font=("Times New Roman", 12))
        self.context_text.pack(fill="both", expand=True, padx=5, pady=5)
        
        btn_frame = tk.Frame(self.context_frame)
        btn_frame.pack(fill="x", pady=2)
        tk.Button(btn_frame, text="Jump to Location", command=self.jump_to_loc, bg="#2196F3", fg="white").pack(pady=5)

        # Populate List
        self.thumbs = []
        self.populate_list()
        
        # Show first
        if images:
            self.show_image(0)

    def populate_list(self):
        for idx, img in enumerate(self.images):
            # Create thumbnail
            t_img = img.copy()
            t_img.thumbnail((100, 100))
            photo = ImageTk.PhotoImage(t_img)
            self.thumbs.append(photo) # Keep ref
            
            f = tk.Frame(self.list_inner, bg="white", bd=1, relief="solid")
            f.pack(fill="x", pady=2, padx=2)
            
            btn = tk.Button(f, image=photo, command=lambda i=idx: self.show_image(i), relief="flat", bg="white")
            btn.pack(side="left")
            
            lbl = tk.Label(f, text=self.image_names[idx], font=("Arial", 8), bg="white", anchor="w")
            lbl.pack(side="left", fill="x", expand=True, padx=5)
            
            # Save ref to widget for autoscroll highlighting
            setattr(self, f"btn_{idx}", f)

    def show_image(self, index):
        self.current_idx = index
        # Full size preview
        img = self.images[index]
        # Resize if huge
        display_img = img.copy()
        if display_img.width > 600 or display_img.height > 400:
             display_img.thumbnail((600, 400))
        
        self.tk_display = ImageTk.PhotoImage(display_img)
        self.img_label.config(image=self.tk_display)
        
        self.name_var.set(self.image_names[index])
        
        # Update context
        loc = self.loc_map.get(index, 0)
        self.update_context_text(loc)

    def update_context_text(self, loc):
        start = max(0, loc - 50)
        end = min(len(self.parent.words), loc + 50)
        text_chunk = " ".join(self.parent.words[start:end])
        self.context_text.delete("1.0", "end")
        self.context_text.insert("1.0", f"... {text_chunk} ...")

    def update_label(self):
        new_name = self.name_var.get()
        self.image_names[self.current_idx] = new_name
        # Ideally update list label too, but simpler to just store for now
        messagebox.showinfo("Updated", "Figure label updated for this session.")

    def jump_to_loc(self):
        loc = self.loc_map.get(self.current_idx, 0)
        self.parent.current_index = max(0, loc - 5)
        self.parent.update_display()
        self.parent.top.lift() # Bring main to front

    def sync_scroll(self, current_word_idx):
        # Find closest image loc >= current_word_idx
        # Simple search in sorted_locs
        best_idx = 0
        min_dist = 99999999
        
        for loc, idx in self.sorted_locs:
            dist = abs(loc - current_word_idx)
            if dist < min_dist:
                min_dist = dist
                best_idx = idx
        
        if best_idx != self.current_idx:
            self.show_image(best_idx)
            # Scroll list to show this item
            try:
                # Calculate fractional position
                # Rough approximation: index / total
                fraction = best_idx / len(self.images)
                self.canvas_list.yview_moveto(fraction)
            except: pass
        self.prev_button = tk.Button(nav_frame, text="<< Prev", command=self.show_prev)
        self.prev_button.pack(side="left", padx=10)
        self.next_button = tk.Button(nav_frame, text="Next >>", command=self.show_next)
        self.next_button.pack(side="right", padx=10)
        self.show_image()

    def show_image(self):
        img = self.images[self.current_index]
        max_size = (500, 500)
        img_resized = img.copy()
        img_resized.thumbnail(max_size, Image.ANTIALIAS)
        self.photo = ImageTk.PhotoImage(img_resized)
        self.img_label.config(image=self.photo)
        self.info_label.config(text=f"Image {self.current_index+1} of {len(self.images)}: {self.image_names[self.current_index]}")

    def show_next(self):
        if self.current_index < len(self.images) - 1:
            self.current_index += 1
            self.show_image()

    def show_prev(self):
        if self.current_index > 0:
            self.current_index -= 1
            self.show_image()

# ---------------------------------------------------------
# Manual Extraction Editor
# ---------------------------------------------------------
class ManualExtractionEditor:
    def __init__(self, parent, filename):
        self.top = tk.Toplevel(parent)
        self.top.title("Manual Layout Editor")
        self.top.geometry("1000x800")
        self.parent = parent
        self.filename = filename
        self.filename = filename
        self.extracted_text = None
        self.extracted_images = []
        self.extracted_image_names = []
        self.extracted_locations = {}
        
        self.pdf = pdfplumber.open(filename)
        self.num_pages = len(self.pdf.pages)
        self.current_page_idx = 0
        
        # Page_Index -> List of Boxes [(x, y, w, h)] in PDF Canvas coords?
        # Storing as normalized ratio (0.0-1.0) might be safer for varying resolutions, 
        # but pixel coords on the rendered image is easier for interaction.
        # We will store: page_idx -> list of dicts {'x':, 'y':, 'w':, 'h':}
        self.boxes = {} 
        
        self.zoom_scale = 1.0
        self.current_image = None # PIL Image
        self.tk_image = None # PhotoImage
        
        self.selected_box_idx = None
        self.drag_data = {"x": 0, "y": 0, "mode": None} # mode: "move", "resize_top", "resize_bottom"
        
        self.create_widgets()
        self.load_page()

    def create_widgets(self):
        # Toolbar
        toolbar = tk.Frame(self.top, bg="#ddd")
        toolbar.pack(fill="x", side="top", pady=2)
        
        tk.Button(toolbar, text="<< Prev", command=self.prev_page).pack(side="left", padx=5)
        self.lbl_page = tk.Label(toolbar, text="Page 1 / ?")
        self.lbl_page.pack(side="left", padx=5)
        tk.Button(toolbar, text="Next >>", command=self.next_page).pack(side="left", padx=5)
        
        tk.Frame(toolbar, width=20, bg="#ddd").pack(side="left")
        
        tk.Button(toolbar, text="+ Add Box", command=self.add_box, bg="#4CAF50", fg="white").pack(side="left", padx=5)
        tk.Button(toolbar, text="Clear Page", command=self.clear_page, bg="#FF9800", fg="white").pack(side="left", padx=5)
        tk.Button(toolbar, text="+ Add Image", command=self.add_image_box, bg="#FF5722", fg="white").pack(side="left", padx=5)
        
        tk.Button(toolbar, text="Finish & Import", command=self.finish, bg="#2196F3", fg="white", font=("bold")).pack(side="right", padx=10)
        
        # Main Canvas
        self.canvas = tk.Canvas(self.top, bg="#555")
        self.canvas.pack(fill="both", expand=True)
        
        self.canvas.bind("<ButtonPress-1>", self.on_mouse_down)
        self.canvas.bind("<B1-Motion>", self.on_mouse_drag)
        self.canvas.bind("<ButtonRelease-1>", self.on_mouse_up)
        # Bind keys for width adjustment
        self.top.bind("<plus>", self.increase_width)
        self.top.bind("<equal>", self.increase_width)
        self.top.bind("<minus>", self.decrease_width)
        self.top.bind("<underscore>", self.decrease_width)

    def load_page(self):
        page = self.pdf.pages[self.current_page_idx]
        # Render at higher DPI for clarity
        im = page.to_image(resolution=100) # 100 DPI is decent balance
        self.current_image = im.original
        
        self.tk_image = ImageTk.PhotoImage(self.current_image)
        
        self.canvas.delete("all")
        # Center image
        cw = self.canvas.winfo_width()
        ch = self.canvas.winfo_height()
        # If canvas not ready (first load), arbitrary
        if cw < 10: cw = 1000
        
        self.canvas.create_image(10, 10, image=self.tk_image, anchor="nw", tags="bg_img")
        self.canvas.config(scrollregion=self.canvas.bbox("all"))
        
        self.lbl_page.config(text=f"Page {self.current_page_idx + 1} / {self.num_pages}")
        self.draw_boxes()

    def draw_boxes(self):
        self.canvas.delete("box")
        page_boxes = self.boxes.get(self.current_page_idx, [])
        
        for i, box in enumerate(page_boxes):
            x, y, w, h = box['x'], box['y'], box['w'], box['h']
            b_type = box.get('type', 'text')
            
            if i == self.selected_box_idx:
                color = "#00ff00" # Selected
            else:
                color = "#4444ff" if b_type == 'text' else "#ff9800" # Blue for text, Orange for image
                
            tag = f"box_{i}"
            # Rect
            width = 3 if b_type == 'image' else 2
            stipple = "gray50" if b_type == 'image' else "" # Visual distinction
            
            self.canvas.create_rectangle(x, y, x+w, y+h, outline=color, width=width, tags=("box", tag))
            # Number
            label = str(i+1)
            if b_type == 'image': label += " (IMG)"
            
            self.canvas.create_text(x, y-15, text=label, fill=color, font=("bold"), tags=("box", tag))
            
            # Decorators (Handles)
            # Top Handle
            self.canvas.create_oval(x + w/2 - 5, y - 5, x + w/2 + 5, y + 5, fill="yellow", tags=("box", tag, "handle_top"))
            # Bottom Handle
            self.canvas.create_oval(x + w/2 - 5, y + h - 5, x + w/2 + 5, y + h + 5, fill="yellow", tags=("box", tag, "handle_bottom"))

    def add_box(self):
        self._add_box_internal('text')

    def add_image_box(self):
        self._add_box_internal('image')

    def _add_box_internal(self, box_type):
        # Default box in center of view
        # We need rendered dimensions
        if not self.current_image: return
        im_w, im_h = self.current_image.size
        
        w = im_w * 0.4
        h = im_h * 0.4
        x = (im_w - w) / 2
        y = (im_h - h) / 2
        
        if self.current_page_idx not in self.boxes:
            self.boxes[self.current_page_idx] = []
        
        self.boxes[self.current_page_idx].append({'x': x, 'y': y, 'w': w, 'h': h, 'type': box_type})
        self.selected_box_idx = len(self.boxes[self.current_page_idx]) - 1
        self.draw_boxes()

    def delete_box(self):
        if self.selected_box_idx is not None:
             del self.boxes[self.current_page_idx][self.selected_box_idx]
             self.selected_box_idx = None
             self.draw_boxes()
             
    def clear_page(self):
        self.boxes[self.current_page_idx] = []
        self.selected_box_idx = None
        self.draw_boxes()

    def prev_page(self):
        if self.current_page_idx > 0:
            self.current_page_idx -= 1
            self.selected_box_idx = None
            self.load_page()

    def next_page(self):
        if self.current_page_idx < self.num_pages - 1:
            # Copy boxes to next page if empty
            current_boxes = self.boxes.get(self.current_page_idx, [])
            next_idx = self.current_page_idx + 1
            if current_boxes and not self.boxes.get(next_idx):
                self.boxes[next_idx] = [b.copy() for b in current_boxes]
            
            self.current_page_idx += 1
            self.selected_box_idx = None
            self.load_page()

    def on_mouse_down(self, event):
        # Translate canvas coord (scroll?) -> we are using (10,10) offset
        ex, ey = self.canvas.canvasx(event.x), self.canvas.canvasy(event.y)
        
        # Check handlers first?
        # Check collision with boxes (reverse order to pick top)
        page_boxes = self.boxes.get(self.current_page_idx, [])
        
        hit_found = False
        
        # Check handles of SELECTED box first
        if self.selected_box_idx is not None:
             b = page_boxes[self.selected_box_idx]
             x, y, w, h = b['x'], b['y'], b['w'], b['h']
             # Top Handle
             tx, ty = x + w/2, y
             if abs(ex - tx) < 10 and abs(ey - ty) < 10:
                 self.drag_data = {"x": ex, "y": ey, "mode": "resize_top", "idx": self.selected_box_idx}
                 return
             # Bottom Handle
             bx, by = x + w/2, y + h
             if abs(ex - bx) < 10 and abs(ey - by) < 10:
                 self.drag_data = {"x": ex, "y": ey, "mode": "resize_bottom", "idx": self.selected_box_idx}
                 return
        
        # Check bodies
        for i in reversed(range(len(page_boxes))):
            b = page_boxes[i]
            # Account for offset 10,10 used in create_image
            # Wait, our box coords are relative to image 0,0?
            # logic: drawn at X, Y. Image drawn at 10, 10.
            # So Image coord = Canvas Coord - 10.
            
            ix = ex - 10
            iy = ey - 10
            
            if b['x'] <= ix <= b['x']+b['w'] and b['y'] <= iy <= b['y']+b['h']:
                self.selected_box_idx = i
                self.drag_data = {"x": ix, "y": iy, "mode": "move", "idx": i, "orig_x": b['x'], "orig_y": b['y']}
                self.draw_boxes()
                hit_found = True
                break
        
        if not hit_found:
             self.selected_box_idx = None
             self.draw_boxes()

    def on_mouse_drag(self, event):
        if not self.drag_data.get("mode"): return
        
        ex, ey = self.canvas.canvasx(event.x), self.canvas.canvasy(event.y)
        ix = ex - 10
        iy = ey - 10
        
        idx = self.drag_data["idx"]
        box = self.boxes[self.current_page_idx][idx]
        
        if self.drag_data["mode"] == "move":
            dx = ix - self.drag_data["x"]
            dy = iy - self.drag_data["y"]
            box['x'] = self.drag_data["orig_x"] + dx
            box['y'] = self.drag_data["orig_y"] + dy
            # Update drag origin avoids drift if we re-read? 
            # Actually standard delta accumulation is better
            # Resetting orig for smooth Drag
            # Better: just update box and reset drag_data x/y (delta approach)
            self.drag_data["x"] = ix
            self.drag_data["y"] = iy
            self.drag_data["orig_x"] = box['x']
            self.drag_data["orig_y"] = box['y']
            
        elif self.drag_data["mode"] == "resize_top":
            # Change Y and Height
            old_y = box['y']
            box['y'] = iy
            box['h'] += (old_y - iy)
            
        elif self.drag_data["mode"] == "resize_bottom":
            box['h'] = iy - box['y']
            
        self.draw_boxes()

    def on_mouse_up(self, event):
        self.drag_data["mode"] = None

    def increase_width(self, event):
        if self.selected_box_idx is not None:
             box = self.boxes[self.current_page_idx][self.selected_box_idx]
             # Expand from center? Or just right? User asked "widened or narrowed".
             # Center expansion is usually friendlier for columns.
             box['x'] -= 5
             box['w'] += 10
             self.draw_boxes()

    def decrease_width(self, event):
        if self.selected_box_idx is not None:
             box = self.boxes[self.current_page_idx][self.selected_box_idx]
             if box['w'] > 20:
                 box['x'] += 5
                 box['w'] -= 10
             self.draw_boxes()

    def finish(self):
        # Disable controls
        for widget in self.top.winfo_children():
            if isinstance(widget, tk.Frame): # Toolbar
                 for child in widget.winfo_children():
                     if isinstance(child, tk.Button):
                         child.config(state="disabled")

        # Show progress
        self.progress_win = tk.Toplevel(self.top)
        self.progress_win.title("Processing PDF")
        self.progress_win.geometry("300x150")
        self.progress_label = tk.Label(self.progress_win, text="Initializing extraction...")
        self.progress_label.pack(pady=10)
        self.prog_bar = ttk.Progressbar(self.progress_win, mode='determinate')
        self.prog_bar.pack(fill="x", padx=20, pady=5)
        
        threading.Thread(target=self._finish_thread, daemon=True).start()

    def _finish_thread(self):
        full_text = ""
        total_pages = len(self.pdf.pages)
        current_word_count = 0
        
        try:
            for i, page in enumerate(self.pdf.pages):
                # Update progress
                progress_val = ((i + 1) / total_pages) * 100
                self.top.after(0, lambda v=progress_val, p=i+1, t=total_pages: (
                    self.prog_bar.config(value=v),
                    self.progress_label.config(text=f"Processing Page {p} / {t}")
                ))
                
                boxes = self.boxes.get(i, [])
                if not boxes:
                    # If user defined NOTHING on a page, assume standard extract
                    txt = page.extract_text(layout=True)
                    if txt: 
                         full_text += txt + "\n"
                         current_word_count += len(txt.split()) # Rough count
                else:
                    for b in boxes:
                        b_type = b.get('type', 'text')
                        
                        # Scaling
                        pt_width = page.width
                        scale = 72 / 100
                        
                        x0 = b['x'] * scale
                        y0 = b['y'] * scale
                        x1 = (b['x'] + b['w']) * scale
                        y1 = (b['y'] + b['h']) * scale
                        crop_box = (x0, y0, x1, y1)
                        
                        try:
                            if b_type == 'text':
                                cropped = page.crop(crop_box)
                                txt = cropped.extract_text(layout=True)
                                if txt: 
                                    full_text += txt + "\n"
                                    current_word_count += len(txt.split())
                                    
                            elif b_type == 'image':
                                # Render to image
                                cropped = page.crop(crop_box)
                                # Render at higher DPI for quality
                                p_img = cropped.to_image(resolution=150).original
                                
                                img_name = f"Manual Figure (Page {i+1})"
                                self.extracted_images.append(p_img)
                                self.extracted_image_names.append(img_name)
                                self.extracted_locations[img_name] = current_word_count
                                # Insert placeholder
                                marker = f"\n[FIGURE: {img_name}]\n"
                                full_text += marker
                                current_word_count += 2 # Count marker as words approx
                                
                        except Exception as e:
                            logging.error(f"Failed to process box on page {i}: {e}")
            
            self.extracted_text = full_text
            self.top.after(0, self._on_finish_complete)
            
        except Exception as e:
             logging.error(f"Manual extraction failed: {e}")
             self.top.after(0, lambda: messagebox.showerror("Error", f"Extraction failed: {e}"))
             self.top.after(0, self.progress_win.destroy)

    def _on_finish_complete(self):
        self.progress_win.destroy()
        self.top.destroy()

# ---------------------------------------------------------
# Library Dialog
# ---------------------------------------------------------
class LibraryDialog:
    def __init__(self, parent):
        self.top = tk.Toplevel(parent)
        self.top.title("Library")
        self.top.geometry("900x600")
        self.parent = parent
        self.top.configure(bg="#f0f0f0")
        
        # Main Layout: PanedWindow (Split View)
        self.paned = tk.PanedWindow(self.top, orient=tk.HORIZONTAL, sashwidth=4, bg="#d0d0d0")
        self.paned.pack(fill="both", expand=True, padx=5, pady=5)
        
        # --- Left Pane: Categories ---
        self.left_pane = tk.Frame(self.paned, bg="#e8e8e8", width=220)
        self.left_pane.pack_propagate(False) # Maintain width
        self.paned.add(self.left_pane)
        
        tk.Label(self.left_pane, text="Categories", font=("Helvetica", 12, "bold"), bg="#e8e8e8").pack(pady=5)
        
        # Folder List (using Treeview for modern look)
        self.folder_tree = ttk.Treeview(self.left_pane, show="tree", selectmode="browse")
        self.folder_tree.pack(fill="both", expand=True, padx=5, pady=5)
        self.folder_tree.bind("<<TreeviewSelect>>", self.on_folder_select)
        
        # Folder Buttons
        f_btn_frame = tk.Frame(self.left_pane, bg="#e8e8e8")
        f_btn_frame.pack(fill="x", padx=5, pady=5)
        tk.Button(f_btn_frame, text="+ Folder", command=self.add_folder, bg="#ddd", font=("Helvetica", 8)).pack(side="left", fill="x", expand=True, padx=2)
        tk.Button(f_btn_frame, text="Rename", command=self.rename_folder, bg="#ddd", font=("Helvetica", 8)).pack(side="left", fill="x", expand=True, padx=2)

        # --- Right Pane: Book List ---
        self.right_pane = tk.Frame(self.paned, bg="white")
        self.paned.add(self.right_pane)
        
        # Controls
        controls = tk.Frame(self.right_pane, bg="white")
        controls.pack(fill="x", padx=10, pady=5)
        
        self.lbl_current_folder = tk.Label(controls, text="All Books", font=("Helvetica", 14, "bold"), bg="white")
        self.lbl_current_folder.pack(side="left")
        
        tk.Button(controls, text="+ Add Book", command=self.add_book, bg="#4CAF50", fg="white").pack(side="right")
        
        # Book Canvas
        self.canvas = tk.Canvas(self.right_pane, bg="white")
        self.scrollbar = tk.Scrollbar(self.right_pane, orient="vertical", command=self.canvas.yview)
        self.scrollable_frame = tk.Frame(self.canvas, bg="white")
        self.scrollable_frame.bind("<Configure>", lambda e: self.canvas.configure(scrollregion=self.canvas.bbox("all")))
        self.canvas.create_window((0, 0), window=self.scrollable_frame, anchor="nw")
        self.canvas.configure(yscrollcommand=self.scrollbar.set)
        
        self.canvas.pack(side="left", fill="both", expand=True)
        self.scrollbar.pack(side="right", fill="y")
        
        # State
        self.current_filter = "All Books"
        self.load_folders()
        self.refresh_list()

    def get_categories(self):
        cats = set(item.get('category', 'Uncategorized') for item in self.parent.library)
        if "Uncategorized" not in cats: cats.add("Uncategorized")
        # Also include any cached/empty custom folders if we track them? 
        # For now, dynamic based on content is safest.
        return sorted(list(cats))

    def load_folders(self):
        # Clear
        for item in self.folder_tree.get_children():
            self.folder_tree.delete(item)
            
        self.folder_tree.insert("", "end", "all", text="All Books")
        
        for cat in self.get_categories():
            self.folder_tree.insert("", "end", cat, text=cat)

    def on_folder_select(self, event):
        sel = self.folder_tree.selection()
        if not sel: return
        cat = self.folder_tree.item(sel[0], "text")
        self.current_filter = cat
        self.lbl_current_folder.config(text=cat)
        self.refresh_list()
        
    def add_folder(self):
        name = tk.simpledialog.askstring("New Folder", "Enter folder name:", parent=self.top)
        if name:
            # Create a dummy entry to persist folder? No, just add to tree temporarily.
            # Real persistence happens when a book is moved into it.
            if name not in self.get_categories():
                  self.folder_tree.insert("", "end", name, text=name)

    def rename_folder(self):
        sel = self.folder_tree.selection()
        if not sel or sel[0] == "all": return
        old_name = self.folder_tree.item(sel[0], "text")
        new_name = tk.simpledialog.askstring("Rename", f"Rename '{old_name}' to:", parent=self.top)
        if new_name:
            for item in self.parent.library:
                if item.get("category") == old_name:
                    item["category"] = new_name
            self.save_library()
            self.load_folders()
            self.refresh_list()

    def save_library(self):
        try:
             with open(LIBRARY_FILE, "w", encoding="utf-8") as f:
                json.dump(self.parent.library, f, indent=4)
        except: pass

    def refresh_list(self):
        for widget in self.scrollable_frame.winfo_children():
            widget.destroy()

        books = self.parent.library
        if self.current_filter != "All Books":
            books = [b for b in books if b.get('category', 'Uncategorized') == self.current_filter]
            
        books.sort(key=lambda x: x.get('last_read', 0), reverse=True)

        if not books:
            tk.Label(self.scrollable_frame, text="No books in this folder.", bg="white", fg="gray").pack(pady=20)
            return

        for i, item in enumerate(books):
            fpath = item['path']
            title = item.get('title', os.path.basename(fpath))
            category = item.get('category', 'Uncategorized')
            last_read = item.get('last_read', 0)
            
            frame = tk.Frame(self.scrollable_frame, bg="white", bd=1, relief="solid")
            frame.pack(fill="x", padx=10, pady=5)
            
            # Icon
            color = "#2196F3"
            if fpath.lower().endswith(".pdf"): color = "#F44336"
            elif fpath.lower().endswith((".epub", ".mobi")): color = "#9C27B0"
            tk.Frame(frame, bg=color, width=5).pack(side="left", fill="y")
            
            info_frame = tk.Frame(frame, bg="white")
            info_frame.pack(side="left", fill="both", expand=True, padx=10, pady=5)
            
            tk.Label(info_frame, text=title, font=("Helvetica", 11, "bold"), bg="white", anchor="w").pack(fill="x")
            if self.current_filter == "All Books":
                tk.Label(info_frame, text=category, font=("Helvetica", 8, "italic"), bg="white", fg="blue", anchor="w").pack(fill="x")
            
            time_str = time.strftime('%Y-%m-%d %H:%M', time.localtime(last_read)) if last_read else "Never"
            tk.Label(info_frame, text=f"Last read: {time_str}", font=("Helvetica", 8), bg="white", fg="gray", anchor="w").pack(fill="x")
            
            btn_frame = tk.Frame(frame, bg="white")
            btn_frame.pack(side="right", padx=5)
            
            tk.Button(btn_frame, text="Read", command=lambda p=fpath: self.open_book(p), bg="#4CAF50", fg="white", width=8).pack(side="left", padx=2)
            
            # Menu Button for "Move to"
            mb = tk.Menubutton(btn_frame, text="📂", bg="#ddd", width=3, relief="raised")
            mb.menu = tk.Menu(mb, tearoff=0)
            mb["menu"] = mb.menu
            
            cats = self.get_categories()
            for cat in cats:
                 if cat != category:
                     mb.menu.add_command(label=f"Move to {cat}", command=lambda p=fpath, c=cat: self.move_book(p, c))
            mb.menu.add_separator()
            mb.menu.add_command(label="New Folder...", command=lambda p=fpath: self.move_book_new_folder(p))
            
            mb.pack(side="left", padx=2)
            
            tk.Button(btn_frame, text="X", command=lambda p=fpath: self.remove_book(p), bg="#ddd", width=2).pack(side="left", padx=2)

    def move_book(self, path, category):
        for item in self.parent.library:
            if item['path'] == path:
                item['category'] = category
                break
        self.save_library()
        self.load_folders() 
        self.refresh_list()

    def move_book_new_folder(self, path):
         name = tk.simpledialog.askstring("New Folder", "Move to new folder:", parent=self.top)
         if name:
             self.move_book(path, name)

    def add_book(self):
        fpath = filedialog.askopenfilename(filetypes=[("All Reading Formats", "*.txt *.pdf *.docx *.epub *.mobi *.azw3")])
        if fpath:
            self.parent.update_library_metadata(fpath)
            # Force into current folder if specific one selected
            if self.current_filter not in ["All Books", "Uncategorized"]:
                  self.move_book(fpath, self.current_filter)
            else:
                  self.refresh_list()

    def open_book(self, path):
        if not os.path.exists(path):
            messagebox.showerror("Error", f"File not found: {path}")
            return
        self.parent.load_session_for_file(path)
        self.top.destroy()

    def remove_book(self, path):
        if messagebox.askyesno("Remove", f"Remove {os.path.basename(path)} from library?"):
            self.parent.library = [item for item in self.parent.library if item['path'] != path]
            self.save_library()
            self.refresh_list()

# ---------------------------------------------------------
# Punctuation & Speed Weighting Dialog (Compact)
# ---------------------------------------------------------
class PauseEqualizerDialog:
    def __init__(self, parent):
        self.top = tk.Toplevel(parent)
        self.top.title("Punctuation & Speed Weighting")
        self.top.geometry("750x420")
        self.parent = parent
        
        # Main container with 3 columns
        main_frame = tk.Frame(self.top, padx=10, pady=10)
        main_frame.pack(fill="both", expand=True)
        
        col1 = tk.Frame(main_frame)
        col1.grid(row=0, column=0, sticky="n", padx=5)
        
        col2 = tk.Frame(main_frame)
        col2.grid(row=0, column=1, sticky="n", padx=5)
        
        col3 = tk.Frame(main_frame)
        col3.grid(row=0, column=2, sticky="n", padx=5)

        # --- Column 1: Standard Pauses ---
        tk.Label(col1, text="Standard Pauses", font=("Helvetica", 10, "bold")).pack(pady=5)
        
        self.create_compact_row(col1, "Full Pauses (.!?)", "full_chars", parent.full_pause_chars, "period", 1.0, 5.0)
        self.create_compact_row(col1, "Short Pauses (,;:)", "short_chars", parent.short_pause_chars, "short", 1.0, 3.0)
        self.create_compact_row(col1, "Paragraph Break", None, None, "paragraph", 1.0, 5.0)

        # Long Words
        tk.Label(col1, text="Long Word Linger", font=("Helvetica", 9, "bold")).pack(pady=(10, 2))
        f_word = tk.Frame(col1)
        f_word.pack(fill="x", pady=2)
        tk.Label(f_word, text="Min Len:").pack(side="left")
        self.word_thresh_var = tk.IntVar(value=parent.long_word_threshold)
        tk.Entry(f_word, textvariable=self.word_thresh_var, width=3).pack(side="left", padx=2)
        self.long_word_mult = tk.Scale(f_word, from_=1.0, to=2.0, resolution=0.1, orient="horizontal", length=80)
        self.long_word_mult.set(parent.pause_multipliers.get("long_word", 1.2))
        self.long_word_mult.pack(side="right")

        # --- Column 2: Structural & Special ---
        tk.Label(col2, text="Structure & Special", font=("Helvetica", 10, "bold")).pack(pady=5)
        
        # Numbers
        self.create_compact_row(col2, "Numbers", None, None, "numbers", 1.0, 3.0)
        # Hyphens
        self.create_compact_row(col2, "Hyphens", None, None, "hyphens", 1.0, 3.0)

        # --- Column 3: Custom Categories ---
        tk.Label(col3, text="Custom Categories", font=("Helvetica", 10, "bold")).pack(pady=5)
        
        self.create_compact_row(col3, "Custom 1 (Chars)", "c1_chars", parent.custom1_chars, "custom1", 1.0, 3.0)
        self.create_compact_row(col3, "Custom 2 (Strings)", "c2_chars", parent.custom2_chars, "custom2", 1.0, 3.0)
        self.create_compact_row(col3, "Custom 3 (Regex)", "c3_regex", parent.custom3_regex_pattern, "custom3_regex", 1.0, 5.0)

        tk.Button(self.top, text="Apply All", command=self.save, bg="#4CAF50", fg="white", font=("Helvetica", 10, "bold"), width=15).pack(pady=10)

    def create_compact_row(self, parent, title, var_name, initial_val, mult_key, m_min, m_max):
        frame = tk.LabelFrame(parent, text=title)
        frame.pack(fill="x", pady=2)
        
        if var_name:
            v = tk.StringVar(value=initial_val)
            setattr(self, f"{var_name}_var", v)
            tk.Entry(frame, textvariable=v, width=15).pack(side="left", padx=2, fill="x", expand=True)
        
        m = tk.Scale(frame, from_=m_min, to=m_max, resolution=0.1, orient="horizontal", length=100)
        m.set(self.parent.pause_multipliers.get(mult_key, 1.0))
        m.pack(side="right", padx=2)
        setattr(self, f"{mult_key}_mult", m)

    def save(self):
        self.parent.full_pause_chars = self.full_chars_var.get()
        self.parent.short_pause_chars = self.short_chars_var.get()
        self.parent.custom1_chars = self.c1_chars_var.get()
        self.parent.custom2_chars = self.c2_chars_var.get()
        self.parent.custom3_regex_pattern = self.c3_regex_var.get()

        try:
            self.parent.long_word_threshold = int(self.word_thresh_var.get())
        except: pass
        
        # Map compact widget names to keys
        # Note: paragraph check
        if hasattr(self, "paragraph_mult"):
             self.parent.pause_multipliers["paragraph"] = self.paragraph_mult.get()
        
        keys = ["period", "short", "paragraph", "numbers", "hyphens", "custom1", "custom2", "custom3_regex", "long_word"]
        for k in keys:
             # Handle special widget naming needed?
             # create_compact_row uses f"{mult_key}_mult"
             if hasattr(self, f"{k}_mult"):
                 scaler = getattr(self, f"{k}_mult")
                 self.parent.pause_multipliers[k] = scaler.get()
        
        self.top.destroy()

# ---------------------------------------------------------
# Image Settings Dialog
# ---------------------------------------------------------
class ImageSettingsDialog:
    def __init__(self, parent):
        self.top = tk.Toplevel(parent)
        self.top.title("Image Filtering")
        self.top.geometry("300x200")
        self.parent = parent

        tk.Label(self.top, text="Min Dimensions to Display", font=("Helvetica", 10, "bold")).pack(pady=10)

        f = tk.Frame(self.top)
        f.pack(pady=5)
        tk.Label(f, text="Width:").pack(side="left")
        self.w_var = tk.IntVar(value=parent.min_img_width)
        tk.Entry(f, textvariable=self.w_var, width=10).pack(side="left", padx=5)

        f2 = tk.Frame(self.top)
        f2.pack(pady=5)
        tk.Label(f2, text="Height:").pack(side="left")
        self.h_var = tk.IntVar(value=parent.min_img_height)
        tk.Entry(f2, textvariable=self.h_var, width=10).pack(side="left", padx=5)

        tk.Button(self.top, text="Apply Thresholds", command=self.save).pack(pady=20)

    def save(self):
        try:
            self.parent.min_img_width = int(self.w_var.get())
            self.parent.min_img_height = int(self.h_var.get())
        except: pass
        # Re-filter existing images if possible
        if self.parent.epub_images:
             # This is a bit complex as we'd need the originals. 
             # For now, just apply to next load.
             messagebox.showinfo("Note", "Filters will be applied to the next file load.")
        self.top.destroy()

# ---------------------------------------------------------
# Main
# ---------------------------------------------------------
if __name__ == "__main__":
    try:
        app = SpeedReaderApp()
        app.mainloop()
    except Exception as e:
        import traceback
        error_msg = f"An error occurred:\n{traceback.format_exc()}"
        messagebox.showerror("Error", error_msg)
