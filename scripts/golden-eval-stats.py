#!/usr/bin/env python3

import pandas as pd

df = pd.read_csv("golden_eval_diff.csv")

metrics = ["cpu", "mem", "ast", "flat"]

print("\n=== Summary statistics (new - old) ===\n")

for m in metrics:
    diff = df[f"{m} new"] - df[f"{m} old"]
    pct = diff / df[f"{m} old"] * 100

    print(f"--- {m.upper()} ---")
    print(f"Mean pct:        {pct.mean():+.2}%")
    print(f"Std deviation:   {pct.std():.2}%")
    print(f"Min / Max pct:   {pct.min():+.2f}% / {pct.max():+.2f}%")

    improvements = (diff < 0).sum()
    regressions = (diff > 0).sum()
    unchanged = (diff == 0).sum()

    print(f"Improvements:    {improvements}")
    print(f"Regressions:     {regressions}")
    print(f"Unchanged:       {unchanged}")
    print()

