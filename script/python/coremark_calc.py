import tkinter as tk
from tkinter import ttk

# CoreMark calculation function

def calculate_coremark():
    try:
        ticks = float(entry_ticks.get())
        freq_mhz = float(entry_freq.get())
        iterations = float(entry_iter.get())

        freq_hz = freq_mhz * 1_000_000
        time_sec = ticks / freq_hz
        coremark = iterations / time_sec
        coremark_per_mhz = coremark / freq_mhz

        result_var.set(
            f"Time (s): {time_sec:.6f}\n"
            f"CoreMark: {coremark:.2f}\n"
            f"CoreMark/MHz: {coremark_per_mhz:.2f}"
        )
    except Exception as e:
        result_var.set("Error: Invalid input")

# GUI setup
root = tk.Tk()
root.title("CoreMark Calculator")
root.geometry("350x250")

frame = ttk.Frame(root, padding=10)
frame.pack(fill="both", expand=True)

# Inputs

ttk.Label(frame, text="Total Ticks:").grid(row=0, column=0, sticky="w")
entry_ticks = ttk.Entry(frame)
entry_ticks.grid(row=0, column=1)
entry_ticks.insert(0, "432344")


ttk.Label(frame, text="Frequency (MHz):").grid(row=1, column=0, sticky="w")
entry_freq = ttk.Entry(frame)
entry_freq.grid(row=1, column=1)
entry_freq.insert(0, "25")


ttk.Label(frame, text="Iterations:").grid(row=2, column=0, sticky="w")
entry_iter = ttk.Entry(frame)
entry_iter.grid(row=2, column=1)
entry_iter.insert(0, "1")

# Button
calc_button = ttk.Button(frame, text="Calculate", command=calculate_coremark)
calc_button.grid(row=3, column=0, columnspan=2, pady=10)

# Result
result_var = tk.StringVar()
result_label = ttk.Label(frame, textvariable=result_var, foreground="blue")
result_label.grid(row=4, column=0, columnspan=2)

root.mainloop()