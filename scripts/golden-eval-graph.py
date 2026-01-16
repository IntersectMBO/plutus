#!/usr/bin/env python3
import csv
import matplotlib.pyplot as plt
import numpy as np

CSV_FILE = "golden_eval_diff.csv"  # change as needed


def percent_change(old, new):
    if old == 0:
        return 0.0
    return (new - old) / old * 100.0


files = []
cpu_changes = []
mem_changes = []
ast_changes = []
flat_changes = []

with open(CSV_FILE, newline="") as f:
    reader = csv.DictReader(f)
    for row in reader:
        files.append(row["file"])

        cpu_changes.append(
            percent_change(float(row["cpu old"]), float(row["cpu new"]))
        )
        mem_changes.append(
            percent_change(float(row["mem old"]), float(row["mem new"]))
        )
        ast_changes.append(
            percent_change(float(row["ast old"]), float(row["ast new"]))
        )
        flat_changes.append(
            percent_change(float(row["flat old"]), float(row["flat new"]))
        )


def plot_and_save(title, output_file, files, changes):
    # Filter out zero changes
    filtered = [(f, c) for f, c in zip(files, changes) if c != 0]
    if not filtered:
        return

    # Sort by absolute value (descending)
    filtered.sort(key=lambda x: abs(x[1]))
    files_sorted, changes_sorted = zip(*filtered)

    y = np.arange(len(files_sorted))
    colors = ["green" if c < 0 else "red" for c in changes_sorted]

    plt.figure(figsize=(10, max(4, len(files_sorted) * 0.4)))
    bars = plt.barh(y, changes_sorted, color=colors)
    plt.axvline(0, color="black", linewidth=0.8)

    plt.yticks(y, files_sorted)
    plt.xlabel("Percent change (%)")
    plt.title(title)

    # --- Expand x-axis to fit labels ---
    max_abs = max(abs(c) for c in changes_sorted)
    padding = max_abs * 0.4  # 15% extra space
    plt.xlim(-max_abs - padding, max_abs + padding)

    # Add percentage labels
    for bar, value in zip(bars, changes_sorted):
        label = f"{value:+.2f}%"
        x = bar.get_width()
        y_pos = bar.get_y() + bar.get_height() / 2

        offset = padding * 0.05
        plt.text(
            x + offset if value > 0 else x - offset,
            y_pos,
            label,
            va="center",
            ha="left" if value > 0 else "right"
        )

    plt.tight_layout()
    plt.savefig(output_file, dpi=150)
    plt.close()


plot_and_save("CPU Changes", "cpu_changes.png", files, cpu_changes)
plot_and_save("Memory Changes", "mem_changes.png", files, mem_changes)
plot_and_save("AST Changes", "ast_changes.png", files, ast_changes)
plot_and_save("Flat Changes", "flat_changes.png", files, flat_changes)
