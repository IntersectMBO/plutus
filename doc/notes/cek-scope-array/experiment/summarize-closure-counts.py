#!/usr/bin/env python3
"""Recompute deterministic counters and the canonical benchmark comparison."""
import csv
import json
import math
import pathlib
import statistics

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parents[3]
RESULTS = HERE.parent / 'results'
corpus = {p.stem for p in (ROOT/'plutus-benchmark/validation/data').glob('*.flat')}
summary = {}
for path in sorted(RESULTS.glob('fixed-*-stats.csv')):
    rows = [r for r in csv.DictReader(path.open()) if r['name'] in corpus]
    assert len(rows) == len(corpus)
    summary[path.stem.removesuffix('-stats')] = {
        k: sum(int(r[k]) for r in rows) for k in rows[0] if k != 'name'}
base = summary['fixed-cow-checked']
events = summary['fixed-reuse-checked']['seals']
for variant, counters in summary.items():
    counters['copies_vs_cow'] = counters['copies'] / base['copies']
    counters['slots_vs_cow'] = counters['copied_slots'] / base['copied_slots']
    assert counters['extensions'] == base['extensions']
    if variant != 'fixed-cow-checked':
        assert counters['seals'] + counters['erased_closures'] == events
(RESULTS/'closure-copy-summary.json').write_text(json.dumps(summary, indent=2)+'\n')

def read_criterion(path):
    return {r['Name']: float(r['Mean']) for r in csv.DictReader(path.open())}

geo = lambda xs: math.exp(statistics.mean(math.log(x) for x in xs))
rounds = []
per_script = []
for r in range(1, 4):
    baseline = read_criterion(RESULTS/f'closure-criterion-baseline-r{r}.csv')
    candidate = read_criterion(RESULTS/f'closure-criterion-ra-erased-context-r{r}.csv')
    assert baseline.keys() == candidate.keys()
    rounds.append(geo(candidate[n]/baseline[n] for n in baseline))
    for n in baseline:
        per_script.append(dict(round=r, name=n, baseline_seconds=baseline[n],
                               candidate_seconds=candidate[n], ratio=candidate[n]/baseline[n]))
result = dict(scripts=len(baseline), processes=3, time_ratio=geo(rounds),
              round_time_ratios=rounds,
              time_weighted_ratio=geo(
                  sum(x['candidate_seconds'] for x in per_script if x['round']==r) /
                  sum(x['baseline_seconds'] for x in per_script if x['round']==r)
                  for r in range(1,4)))
(RESULTS/'closure-criterion-summary.json').write_text(json.dumps(result, indent=2)+'\n')
with (RESULTS/'closure-criterion-per-script.csv').open('w') as f:
    writer = csv.DictWriter(f, fieldnames=list(per_script[0]), lineterminator='\n')
    writer.writeheader()
    writer.writerows(per_script)
print(json.dumps(result, indent=2))
