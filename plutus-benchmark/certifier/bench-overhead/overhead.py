#!/usr/bin/env python3
"""Compute the certifier-annotation-generation overhead of the UPLC inliner
from the criterion CSV produced by certifier-overhead-bench.

The benchmark measures each inline instance of each corpus script twice, as
<script>/instance-NN/hints-discarded and <script>/instance-NN/hints-forced.
This script reports, per script, the geometric mean of the per-instance
overheads and the range across instances, then the same over the whole corpus.

Usage:
    cabal run certifier-overhead-bench -- --time-limit 1 --csv overhead.csv
    python3 overhead.py overhead.csv [-v] [--latex]

    -v, --instances   also list the individual instances
    --latex           print the per-script column of the paper table
"""

import csv
import math
import sys
from collections import defaultdict


def geomean(xs):
    return math.exp(sum(map(math.log, xs)) / len(xs))


def pct(ratio):
    """A ratio of forced to discarded time, as an overhead percentage."""
    return (ratio - 1) * 100


def fmt(ratio):
    return f"{pct(ratio):.1f}%"


def fmt_tex(ratio):
    p = pct(ratio)
    return f"$-${abs(p):.1f}\\%" if p < 0 else f"{p:.1f}\\%"


def read_means(path):
    # Criterion *appends* to an existing CSV file, so a file can contain the
    # output of several runs, including repeated header lines (e.g. from an
    # aborted earlier run). Skip lines that don't parse, and let the most
    # recent occurrence of each benchmark win.
    means = {}
    with open(path, newline="") as f:
        for row in csv.DictReader(f):
            name, mean = row.get("Name"), row.get("Mean")
            if name is None or mean is None:
                continue
            try:
                means[name] = float(mean)
            except ValueError:
                continue  # a repeated header line
    return means


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("-")]
    flags = {a for a in sys.argv[1:] if a.startswith("-")}
    if len(args) != 1:
        sys.exit(__doc__)
    verbose = bool(flags & {"-v", "--instances"})
    latex = "--latex" in flags

    # Benchmark names are "<script>/<instance>/<variant>".
    variants = defaultdict(dict)
    for name, mean in read_means(args[0]).items():
        instance, _, variant = name.rpartition("/")
        variants[instance][variant] = mean

    per_script = defaultdict(list)
    for instance in sorted(variants):
        v = variants[instance]
        if {"hints-discarded", "hints-forced"} <= v.keys():
            script, _, label = instance.rpartition("/")
            per_script[script or instance].append(
                (label or instance, v["hints-forced"] / v["hints-discarded"])
            )
        else:
            print(f"{instance}: incomplete measurements, skipping", file=sys.stderr)

    if not per_script:
        sys.exit("no complete measurements found")

    everything = []
    for script in sorted(per_script):
        rows = per_script[script]
        ratios = [r for _, r in rows]
        everything += ratios
        summary = f"{fmt(geomean(ratios))} ({fmt(min(ratios))} - {fmt(max(ratios))})"
        if latex:
            g, lo, hi = geomean(ratios), min(ratios), max(ratios)
            name = script[:-5] if script.endswith(".uplc") else script
            print(
                f"{name:<23} & {fmt_tex(g)} ({fmt_tex(lo)} -- {fmt_tex(hi)}) \\\\"
            )
        else:
            print(f"{script:<30} {summary:<28} [{len(ratios)} instances]")
        if verbose and not latex:
            for label, r in rows:
                print(f"    {label:<14} {fmt(r)}")

    g, lo, hi = geomean(everything), min(everything), max(everything)
    if latex:
        print(f"{'total':<23} & {fmt_tex(g)} ({fmt_tex(lo)} -- {fmt_tex(hi)}) \\\\")
    else:
        print(
            f"\n{'CORPUS':<30} {fmt(g)} ({fmt(lo)} - {fmt(hi)})"
            f"   [{len(everything)} instances]"
        )


if __name__ == "__main__":
    main()
