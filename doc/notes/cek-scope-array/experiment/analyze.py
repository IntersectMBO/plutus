#!/usr/bin/env python3
"""Summarize a fixed corpus with paired process-level bootstrap intervals."""
import argparse
import csv
import json
import math
import pathlib
import random
import statistics

p = argparse.ArgumentParser()
p.add_argument('--prefix', default='matrix-cek')
p.add_argument('--baseline', default='baseline')
p.add_argument('--group', default='cek/')
p.add_argument('--output', default='summary')
a = p.parse_args()
results = pathlib.Path(__file__).resolve().parent.parent/'results'
runs = {}
for path in sorted(results.glob(a.prefix+'-*-r*.csv')):
    variant, r = path.stem[len(a.prefix)+1:].rsplit('-r',1)
    rows = {row['name']: row for row in csv.DictReader(path.open())
            if row['name'].startswith(a.group)}
    runs.setdefault(variant,{})[int(r)] = rows
base = runs[a.baseline]
geo = lambda xs: math.exp(statistics.mean(math.log(x) for x in xs))
summary = {}
per_script = []
for variant, vruns in runs.items():
    rounds = sorted(set(base)&set(vruns))
    if not rounds:
        continue
    names = sorted(set.intersection(*[set(base[r])&set(vruns[r]) for r in rounds]))
    if not names:
        continue
    ratios, weights, allocations = [], [], []
    for r in rounds:
        bs = [float(base[r][n]['seconds']) for n in names]
        vs = [float(vruns[r][n]['seconds']) for n in names]
        ratios.append(geo(v/b for b,v in zip(bs,vs)))
        weights.append(sum(vs)/sum(bs))
        allocations.append(sum(float(vruns[r][n]['allocated_bytes']) for n in names)/
                           sum(float(base[r][n]['allocated_bytes']) for n in names))
    rng = random.Random(205)
    boots = sorted(geo(rng.choices(ratios,k=len(ratios))) for _ in range(20000))
    summary[variant] = dict(scripts=len(names), processes=len(rounds),
        time_ratio=geo(ratios), process_bootstrap_95=[boots[500],boots[19499]],
        time_weighted_ratio=geo(weights), allocation_ratio=geo(allocations),
        round_time_ratios=ratios)
    for n in names:
        bs = [float(base[r][n]['seconds']) for r in rounds]
        vs = [float(vruns[r][n]['seconds']) for r in rounds]
        per_script.append(dict(variant=variant,name=n,baseline_seconds=geo(bs),
            candidate_seconds=geo(vs),time_ratio=geo(v/b for b,v in zip(bs,vs)),
            allocation_ratio=geo(float(vruns[r][n]['allocated_bytes'])/
                float(base[r][n]['allocated_bytes']) for r in rounds)))
(results/(a.output+'.json')).write_text(json.dumps(summary,indent=2)+'\n')
if per_script:
    with (results/(a.output+'-per-script.csv')).open('w') as f:
        writer=csv.DictWriter(f,fieldnames=list(per_script[0]),lineterminator="\n")
        writer.writeheader()
        writer.writerows(per_script)
print('variant,time_change_percent,process_95_percent,weighted_change_percent,allocation_change_percent')
for v,d in summary.items():
    lo,hi=d['process_bootstrap_95']
    print(f"{v},{100*(d['time_ratio']-1):+.2f},[{100*(lo-1):+.2f};{100*(hi-1):+.2f}],"
          f"{100*(d['time_weighted_ratio']-1):+.2f},{100*(d['allocation_ratio']-1):+.2f}")
