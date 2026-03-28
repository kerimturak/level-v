#!/usr/bin/env python3
"""
Level-V — UART programmer GUI (wraps uart_send_data.py)

  • Lists every *.mem under <repo>/build/tests (same tree as uart_send_data.py)
  • Port + baud, then Gönder loads the selected image over UART

Requires: pyserial, tkinter (python3-tk on Debian/Ubuntu)

  python3 script/python/fpga/uart_send_data_gui.py

Windows: native Python + tkinter; default port **COM8** if ``FPGA_PORT`` is unset.

**Windows trap:** bare ``import uart_send_data`` can resolve to a **different**
installed package, not this repo’s ``uart_send_data.py``. This GUI always loads
the programmer from the sibling file path via ``importlib`` (unless you merged
everything into one ``uart_send_data.py``, then ``__main__`` is used).

WSL: install python3-tk and set DISPLAY if using an X server.
"""
from __future__ import annotations

import io
import importlib.util
import os
import sys
import glob
import threading
from contextlib import redirect_stdout

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
if SCRIPT_DIR not in sys.path:
    sys.path.insert(0, SCRIPT_DIR)

# Mirror uart_send_data.py layout (fpga → repo root)
_PROJECT_ROOT_FALLBACK = os.path.abspath(os.path.join(SCRIPT_DIR, "..", "..", ".."))
_BUILD_DIR_FALLBACK = os.path.join(_PROJECT_ROOT_FALLBACK, "build", "tests")
_FALLBACK_BAUD = 115200
_FALLBACK_PORT_POSIX = "/dev/ttyS8"
_CORE_FILE = os.path.abspath(os.path.join(SCRIPT_DIR, "uart_send_data.py"))
_CORE_IMPORT_NAME = "levelv_fpga_uart_programmer_core"

_cached_prog = None

try:
    import tkinter as tk
    from tkinter import ttk, messagebox, scrolledtext
except ImportError:
    print("ERROR: tkinter gerekli (örn. Debian: sudo apt install python3-tk)", file=sys.stderr)
    sys.exit(1)


def _programmer_complete(m) -> bool:
    return m is not None and hasattr(m, "program_fpga") and hasattr(m, "load_mem_file")


def _exec_uart_send_data_py(path: str):
    """
    Run ``uart_send_data.py`` as a normal module (``__name__`` is not ``__main__``).
    Needed when GUI lives in the same file but runs before ``__main__`` has seen
    ``program_fpga``/``load_mem_file``, or when those names live only in a second
    pass. Skips ``if __name__ == "__main__"`` in that file.
    """
    spec = importlib.util.spec_from_file_location(_CORE_IMPORT_NAME, path)
    if spec is None or spec.loader is None:
        raise ImportError(f"Yüklenemedi: {path}")
    mod = importlib.util.module_from_spec(spec)
    sys.modules[_CORE_IMPORT_NAME] = mod
    spec.loader.exec_module(mod)
    if not _programmer_complete(mod):
        raise ImportError(
            f"Bu dosyada program_fpga / load_mem_file yok (veya tam yüklenmedi): {path}\n"
            "Protokol kodunu silmediğinizden ve ``uart_send_data.py`` ile birleştirirken "
            "MAGIC/load/program_fpga bölümünün dosyada kaldığından emin olun."
        )
    return mod


def _programmer_module():
    """
    Programmer implementation: repo ``uart_send_data.py`` by file path (Windows-safe).

    * Ayrı ``uart_send_data_gui.py``: disko ``uart_send_data.py`` yüklenir.
    * Hepsi tek ``uart_send_data.py`` içindeyse: önce ``__main__``; yetmezse aynı dosya
      importlib ile tekrar çalıştırılır (``__main__`` dallanımı çalışmaz → çift GUI açılmaz).
    """
    global _cached_prog
    if _cached_prog is not None:
        return _cached_prog

    this_path = os.path.abspath(__file__)
    main = sys.modules.get("__main__")

    if this_path == _CORE_FILE:
        if main is not None and _programmer_complete(main):
            _cached_prog = main
            return main
        if not os.path.isfile(_CORE_FILE):
            raise FileNotFoundError(_CORE_FILE)
        mod = _exec_uart_send_data_py(_CORE_FILE)
        _cached_prog = mod
        return mod

    if main is not None and _programmer_complete(main) and getattr(main, "__file__", None):
        try:
            if os.path.abspath(main.__file__) == _CORE_FILE:
                _cached_prog = main
                return main
        except (TypeError, ValueError):
            pass

    existing = sys.modules.get(_CORE_IMPORT_NAME)
    if existing is not None and _programmer_complete(existing):
        _cached_prog = existing
        return existing

    if not os.path.isfile(_CORE_FILE):
        raise FileNotFoundError(
            f"uart_send_data.py bulunamadı: {_CORE_FILE}\n"
            "GUI ile aynı klasörde (script/python/fpga/) olmalı."
        )

    mod = _exec_uart_send_data_py(_CORE_FILE)
    _cached_prog = mod
    return mod


def _project_root(prog) -> str:
    return getattr(prog, "PROJECT_ROOT", _PROJECT_ROOT_FALLBACK)


def _default_serial_port(prog) -> str:
    if os.environ.get("FPGA_PORT"):
        return os.environ["FPGA_PORT"]
    if os.name == "nt":
        return "COM8"
    return getattr(prog, "DEFAULT_PORT", _FALLBACK_PORT_POSIX)


def _default_baud_str(prog) -> str:
    b = getattr(prog, "DEFAULT_BAUD", _FALLBACK_BAUD)
    return os.environ.get("FPGA_BAUD", str(b))


def scan_mem_files() -> list[str]:
    """Absolute paths, sorted for stable UI."""
    prog = _programmer_module()
    build = getattr(prog, "BUILD_DIR", _BUILD_DIR_FALLBACK)
    if not os.path.isdir(build):
        return []
    paths = glob.glob(os.path.join(build, "**", "*.mem"), recursive=True)
    paths = [os.path.abspath(p) for p in paths if os.path.isfile(p)]
    paths.sort(key=lambda p: (os.path.dirname(p).lower(), os.path.basename(p).lower()))
    return paths


class UartProgrammerGui:
    def __init__(self) -> None:
        self._root = tk.Tk()
        self._root.title("Level-V — FPGA UART Programmer")
        self._root.minsize(720, 520)

        self._prog = _programmer_module()
        self._all_paths: list[str] = []
        self._busy = False

        top = ttk.Frame(self._root, padding=8)
        top.pack(fill=tk.X)

        ttk.Label(top, text="Port:").grid(row=0, column=0, sticky=tk.W, padx=(0, 6))
        self._port_var = tk.StringVar(
            value=_default_serial_port(self._prog)
        )
        ttk.Entry(top, textvariable=self._port_var, width=28).grid(
            row=0, column=1, sticky=tk.W
        )

        ttk.Label(top, text="Baud:").grid(row=0, column=2, sticky=tk.W, padx=(16, 6))
        self._baud_var = tk.StringVar(
            value=_default_baud_str(self._prog)
        )
        ttk.Entry(top, textvariable=self._baud_var, width=10).grid(
            row=0, column=3, sticky=tk.W
        )

        ttk.Button(top, text="Listeyi yenile", command=self._refresh_list).grid(
            row=0, column=4, padx=(16, 0)
        )

        mid = ttk.Frame(self._root, padding=(8, 0, 8, 8))
        mid.pack(fill=tk.BOTH, expand=True)

        ttk.Label(mid, text="Ara (isim veya yol):").pack(anchor=tk.W)
        self._filter_var = tk.StringVar()
        self._filter_var.trace("w", lambda *_: self._apply_filter())
        ttk.Entry(mid, textvariable=self._filter_var).pack(fill=tk.X, pady=(0, 6))

        paned = ttk.PanedWindow(mid, orient=tk.HORIZONTAL)
        paned.pack(fill=tk.BOTH, expand=True)

        left = ttk.Frame(paned)
        paned.add(left, weight=2)
        self._listbox = tk.Listbox(left, exportselection=False, font=("TkFixedFont", 10))
        sb = ttk.Scrollbar(left, orient=tk.VERTICAL, command=self._listbox.yview)
        self._listbox.configure(yscrollcommand=sb.set)
        self._listbox.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        sb.pack(side=tk.RIGHT, fill=tk.Y)
        self._listbox.bind("<Double-Button-1>", lambda e: self._send())

        right = ttk.Frame(paned)
        paned.add(right, weight=3)
        ttk.Label(right, text="Günlük").pack(anchor=tk.W)
        self._log = scrolledtext.ScrolledText(right, height=20, state=tk.DISABLED, font=("TkFixedFont", 9))
        self._log.pack(fill=tk.BOTH, expand=True)

        bot = ttk.Frame(self._root, padding=8)
        bot.pack(fill=tk.X)

        self._status_var = tk.StringVar(value="Hazır.")
        ttk.Label(bot, textvariable=self._status_var).pack(side=tk.LEFT)

        self._btn_send = ttk.Button(bot, text="Seçili .mem → UART gönder", command=self._send)
        self._btn_send.pack(side=tk.RIGHT)

        self._refresh_list()

    def _append_log(self, text: str) -> None:
        self._log.configure(state=tk.NORMAL)
        self._log.insert(tk.END, text)
        if not text.endswith("\n"):
            self._log.insert(tk.END, "\n")
        self._log.see(tk.END)
        self._log.configure(state=tk.DISABLED)

    def _refresh_list(self) -> None:
        self._all_paths = scan_mem_files()
        self._apply_filter()
        self._status_var.set(f"{len(self._all_paths)} .mem dosyası (build/tests).")

    def _apply_filter(self) -> None:
        needle = self._filter_var.get().strip().lower()
        self._listbox.delete(0, tk.END)
        proj = _project_root(self._prog)
        for p in self._all_paths:
            rel = os.path.relpath(p, proj)
            if needle and needle not in rel.lower() and needle not in os.path.basename(p).lower():
                continue
            self._listbox.insert(tk.END, rel)

    def _selected_path(self) -> str | None:
        sel = self._listbox.curselection()
        if not sel:
            return None
        line = self._listbox.get(sel[0])
        proj = _project_root(self._prog)
        full = os.path.join(proj, line)
        if os.path.isfile(full):
            return full
        for p in self._all_paths:
            if os.path.relpath(p, proj) == line:
                return p
        return None

    def _send(self) -> None:
        if self._busy:
            return
        path = self._selected_path()
        if not path:
            messagebox.showwarning("Seçim yok", "Listeden bir .mem seçin.")
            return
        try:
            baud = int(self._baud_var.get().strip())
        except ValueError:
            messagebox.showerror("Baud", "Geçerli bir baud sayısı girin.")
            return
        port = self._port_var.get().strip()
        if not port:
            messagebox.showerror("Port", "Seri port girin.")
            return

        self._busy = True
        self._btn_send.state(["disabled"])
        self._status_var.set("Gönderiliyor…")
        self._log.configure(state=tk.NORMAL)
        self._log.delete(1.0, tk.END)
        self._log.configure(state=tk.DISABLED)
        self._append_log(f"=== {path}\n=== port={port!r} baud={baud}\n")

        def work() -> None:
            buf = io.StringIO()
            ok = False
            err: str | None = None
            prog = self._prog
            try:
                words = prog.load_mem_file(path)
                if not words:
                    err = "✗ .mem boş veya okunamadı."
                else:
                    with redirect_stdout(buf):
                        ok = prog.program_fpga(
                            port,
                            baud,
                            words,
                            verbose=False,
                            inter_byte_delay_s=float(
                                os.environ.get("FPGA_UART_INTER_BYTE_DELAY", "0") or 0
                            ),
                            quiet=False,
                            show_payload_hex=False,
                            full_payload_hex=False,
                        )
            except Exception as e:
                err = f"✗ Hata: {e}"
            out = buf.getvalue()
            self._root.after(0, lambda: self._send_done(ok, err, out))

        threading.Thread(target=work, daemon=True).start()

    def _send_done(self, ok: bool, err: str | None, captured: str) -> None:
        if captured.strip():
            self._append_log(captured)
        if err:
            self._append_log(err)
            self._status_var.set("Hata.")
            messagebox.showerror("Gönderim", err)
        elif ok:
            self._status_var.set("Tamam — gönderim bitti.")
            messagebox.showinfo("Gönderim", "Tamamlandı (konsol çıktısı günlükte).")
        else:
            self._status_var.set("Başarısız veya port hatası.")
            messagebox.showwarning("Gönderim", "Gönderim başarısız oldu; günlüğe bakın.")

        self._busy = False
        self._btn_send.state(["!disabled"])

    def run(self) -> None:
        self._root.mainloop()


def main() -> None:
    UartProgrammerGui().run()


if __name__ == "__main__":
    main()
