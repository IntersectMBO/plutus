#!/usr/bin/env python3
"""Improvement of the second Criterion run over the first.

    ./bench-compare.py before.csv after.csv
"""
import csv, sys

def load(path):
    return {r["Name"]: float(r["Mean"]) for r in csv.DictReader(open(path))}

def show(label, x, y):
    print(f"{label:35s} {x*1e6:9.1f}us {y*1e6:9.1f}us {(y/x-1)*100:+7.1f}%")

a, b = load(sys.argv[1]), load(sys.argv[2])
shared = sorted(a.keys() & b.keys())

for name in shared:
    show(name, a[name], b[name])
show("TOTAL", sum(a[k] for k in shared), sum(b[k] for k in shared))
