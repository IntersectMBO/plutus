#!/usr/bin/env python3
"""Analyze paired rounds on a fixed corpus; requires numpy and matplotlib."""
import argparse
import csv
import json
import re
from collections import defaultdict
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
OUT = HERE.parent / 'results' / 'comprehensive'
p = argparse.ArgumentParser()
p.add_argument('--prefix', default='paired')
p.add_argument('--skip-plots', action='store_true')
a = p.parse_args()
rows = list(csv.DictReader((OUT / f'{a.prefix}.csv').open()))
rounds = sorted({int(r['round']) for r in rows})
variants = ['baseline', 'ra-erased-context']
metrics = ['seconds', 'cpu_seconds', 'allocated_bytes', 'gc_cpu_seconds', 'gc_wall_seconds', 'gcs']
keys = sorted({(r['name'], r['mode'], r['suite']) for r in rows})
if a.prefix == 'paired':
    expected = json.loads((OUT / 'correctness.json').read_text())
    expected_keys = {(r['name'], 'cek', r['suite']) for r in expected}
    expected_keys.update((r['name'], 'full', r['suite']) for r in expected
                         if r.get('full_status') == 'ok')
    assert set(keys) == expected_keys
lookup = {(r['name'], r['mode'], int(r['round']), r['variant']): r for r in rows}
assert len(lookup) == len(rows) == len(keys) * len(rounds) * 2
# case, round, variant, metric
data = np.array([[[[float(lookup[(name, mode, r, v)][m]) for m in metrics]
                    for v in variants] for r in rounds] for name, mode, _ in keys])
assert np.isfinite(data).all() and (data[:, :, :, :3] > 0).all()
rng = np.random.default_rng(1278)
resamples = rng.integers(0, len(rounds), size=(10000, len(rounds)))


def family(name, suite):
    short = name.split('/', 1)[1]
    if suite == 'validation':
        if short.startswith('guardrail-'):
            return 'guardrail'
        return re.sub(r'(?:[_-]\d+)+$', '', short)
    if suite == 'force-delay':
        return '-'.join(short.split('-')[:2])
    if suite == 'nofib':
        return short.split('/')[0]
    return suite


def summarize(indices):
    d = data[indices]
    logs = np.log(d[:, :, 1, 0] / d[:, :, 0, 0]).mean(axis=0)
    boot = np.exp(logs[resamples].mean(axis=1))
    low, high = np.quantile(boot, [.025, .975])
    means = d.mean(axis=1).sum(axis=0)  # each script executed once
    return dict(count=len(indices), rounds=len(rounds),
                ratio=float(np.exp(logs.mean())), low=float(low), high=float(high),
                cpu_ratio=float(np.exp(np.log(d[:, :, 1, 1] / d[:, :, 0, 1]).mean())),
                summed_time_ratio=float(means[1, 0] / means[0, 0]),
                allocation_ratio=float(means[1, 2] / means[0, 2]),
                baseline_sum_ms=float(means[0, 0] * 1000),
                candidate_sum_ms=float(means[1, 0] * 1000),
                baseline_cpu_ms=float(means[0, 1] * 1000), candidate_cpu_ms=float(means[1, 1] * 1000),
                baseline_gc_cpu_ms=float(means[0, 3] * 1000), candidate_gc_cpu_ms=float(means[1, 3] * 1000),
                baseline_gc_wall_ms=float(means[0, 4] * 1000), candidate_gc_wall_ms=float(means[1, 4] * 1000),
                baseline_sum_bytes=float(means[0, 2]), candidate_sum_bytes=float(means[1, 2]),
                baseline_gc_cpu_share=float(means[0, 3] / means[0, 1]),
                candidate_gc_cpu_share=float(means[1, 3] / means[1, 1]),
                baseline_gc_wall_share=float(means[0, 4] / means[0, 0]),
                candidate_gc_wall_share=float(means[1, 4] / means[1, 0]),
                round_ratios=np.exp(logs).tolist())


cases = []
for i, (name, mode, suite) in enumerate(keys):
    row = dict(name=name, mode=mode, suite=suite, family=family(name, suite), **summarize([i]))
    row['classification'] = ('faster' if row['high'] < 1 else
                             'slower' if row['low'] > 1 else 'inconclusive')
    cases.append(row)

groups = {}
families = {}
for i, (name, mode, suite) in enumerate(keys):
    groups.setdefault(f'{suite}/{mode}', []).append(i)
    families.setdefault(f'{suite}/{mode}/{family(name, suite)}', []).append(i)
groups['all/cek'] = [i for i, (_, mode, _) in enumerate(keys) if mode == 'cek']
aggregates = {k: summarize(v) for k, v in groups.items()}
family_results = {k: summarize(v) for k, v in families.items()}
for name, indices in groups.items():
    aggregates[name]['point_faster'] = sum(cases[i]['ratio'] < 1 for i in indices)
    aggregates[name]['nominal_faster'] = sum(cases[i]['classification'] == 'faster' for i in indices)
    aggregates[name]['nominal_slower'] = sum(cases[i]['classification'] == 'slower' for i in indices)

# Check order effects: five AB and five BA samples per workload in a ten-round run.
orders = defaultdict(list)
for name, mode, _ in keys:
    for r in rounds:
        b = lookup[(name, mode, r, 'baseline')]
        c = lookup[(name, mode, r, 'ra-erased-context')]
        assert b['reps'] == c['reps']
        orders['baseline-first' if b['order'] == '0' else 'candidate-first'].append(
            np.log(float(c['seconds']) / float(b['seconds'])))
order_ratios = {k: float(np.exp(np.mean(v))) for k, v in orders.items()}

canonical = {}
native_rows = []
for target in ['validation', 'validation-full', 'marlowe', 'nofib', 'force-delay']:
    native_rounds = []
    for basepath in sorted(OUT.glob(f'canonical-{target}-baseline-r*.csv')):
        candidatepath = basepath.with_name(basepath.name.replace('-baseline-', '-ra-erased-context-'))
        if not candidatepath.exists():
            continue
        b = {r['Name']: r for r in csv.DictReader(basepath.open())}
        c = {r['Name']: r for r in csv.DictReader(candidatepath.open())}
        expected = {'validation': 89, 'validation-full': 89, 'marlowe': 200, 'nofib': 22, 'force-delay': 16}[target]
        if len(b) != expected or set(b) != set(c):
            continue  # a still-running native process is not evidence of a full round
        number = int(re.search(r'-r(\d+)\.csv$', basepath.name).group(1))
        ratios = []
        for name in b:
            ratio = float(c[name]['Mean']) / float(b[name]['Mean'])
            ratios.append(ratio)
            native_rows.append(dict(target=target, round=number, name=name,
                                    baseline_seconds=float(b[name]['Mean']),
                                    candidate_seconds=float(c[name]['Mean']), ratio=ratio,
                                    baseline_mean_low=float(b[name]['MeanLB']),
                                    baseline_mean_high=float(b[name]['MeanUB']),
                                    candidate_mean_low=float(c[name]['MeanLB']),
                                    candidate_mean_high=float(c[name]['MeanUB']),
                                    baseline_cv=float(b[name]['Stddev'])/float(b[name]['Mean']),
                                    candidate_cv=float(c[name]['Stddev'])/float(c[name]['Mean'])))
        native_rounds.append(dict(round=number, count=len(b), ratio=float(np.exp(np.log(ratios).mean()))))
    if native_rounds:
        canonical[target] = dict(rounds=native_rounds,
                                 ratio=float(np.exp(np.log([r['ratio'] for r in native_rounds]).mean())))

native_by_case = defaultdict(list)
native_by_group_round = defaultdict(list)
for row in native_rows:
    target, name = row['target'], row['name']
    mode = 'full' if target == 'validation-full' else 'cek'
    if target == 'marlowe':
        name = name.replace('role-payout/', 'rolepayout/')
        suite = 'marlowe-' + name.split('/')[0]
        name = 'marlowe/' + name
    else:
        suite = 'validation' if target == 'validation-full' else target
        name = suite + '/' + name
    native_by_case[(name, mode)].append(row['ratio'])
    native_by_group_round[(suite + '/' + mode, row['round'])].append(row['ratio'])
native_by_group = defaultdict(list)
for (group, rn), ratios in native_by_group_round.items():
    native_by_group[group].append(dict(round=rn, ratio=float(np.exp(np.log(ratios).mean()))))
for row in cases:
    native = native_by_case.get((row['name'], row['mode']), [])
    row['canonical_ratio'] = float(np.exp(np.log(native).mean())) if native else None
    row['canonical_rounds'] = len(native)

summary = dict(rounds=rounds, samples=len(rows), aggregates=aggregates, families=family_results,
               order_ratios=order_ratios, canonical=canonical, canonical_by_suite=native_by_group)
host = {}
for path in OUT.glob('*-host.jsonl'):
    observations = [json.loads(line) for line in path.read_text().splitlines()]
    if len(observations) < 2:
        continue
    busy = {}
    for core in observations[0]['cpu_ticks']:
        delta = [b-a for a, b in zip(observations[0]['cpu_ticks'][core], observations[-1]['cpu_ticks'][core])]
        total = sum(delta[:8])
        busy[core] = (total-delta[3]-delta[4])/total
    loads = [float(r['loadavg'].split()[0]) for r in observations]
    host[path.stem] = dict(observed_seconds=observations[-1]['time']-observations[0]['time'],
                          load_min=min(loads), load_max=max(loads), busy_fraction=busy,
                          median_cpu15_mhz=float(np.median([float(r['frequency_khz']['15'])/1000 for r in observations])))
summary['host_observations'] = host
(OUT / f'{a.prefix}-summary.json').write_text(json.dumps(summary, indent=2) + '\n')


def write_csv(path, records):
    if records:
        with path.open('w') as f:
            writer = csv.DictWriter(f, fieldnames=list(records[0]), lineterminator='\n')
            writer.writeheader()
            writer.writerows(records)


write_csv(OUT / f'{a.prefix}-per-script.csv', [{k: v for k, v in r.items() if k != 'round_ratios'} for r in cases])
write_csv(OUT / 'canonical-per-script.csv', native_rows)


def pct(ratio):
    return f'{100 * (ratio - 1):+.2f}%'


lines = ['# Comprehensive performance tables', '',
         'Candidate: `ra-erased-context`; baseline: recorded origin/master `5d9feef021f9`.', '',
         f'{len(rounds)} adjacent paired rounds, {len(keys)} workload/mode combinations, {len(rows)} measurements.', '',
         'Negative changes mean less time or allocation. Time changes are equal-workload geometric means; allocation and summed time count one execution of each workload. Intervals bootstrap paired rounds on this fixed corpus. Per-script intervals are nominal, without a multiple-comparison correction.', '',
         '## By suite', '',
         '| Suite / mode | N | Time change [95% interval] | CPU time | Sum of times | Allocated bytes | Faster point estimates |',
         '| --- | ---: | ---: | ---: | ---: | ---: | ---: |']
for k, r in aggregates.items():
    lines.append(f'| {k} | {r["count"]} | {pct(r["ratio"])} [{pct(r["low"])}, {pct(r["high"])}] | {pct(r["cpu_ratio"])} | {pct(r["summed_time_ratio"])} | {pct(r["allocation_ratio"])} | {r["point_faster"]}/{r["count"]} |')
lines += ['', '## Absolute totals and GC', '',
          'Sum of mean per-evaluation times/bytes across the suite. GC shares include ordinary collections inside evaluation; forced collections between samples are excluded.', '',
          '| Suite / mode | Master total ms | Candidate total ms | Master total MB | Candidate total MB | Master GC CPU share | Candidate GC CPU share |',
          '| --- | ---: | ---: | ---: | ---: | ---: | ---: |']
for k, r in aggregates.items():
    lines.append(f'| {k} | {r["baseline_sum_ms"]:.3f} | {r["candidate_sum_ms"]:.3f} | {r["baseline_sum_bytes"]/1e6:.3f} | {r["candidate_sum_bytes"]/1e6:.3f} | {r["baseline_gc_cpu_share"]:.2%} | {r["candidate_gc_cpu_share"]:.2%} |')
lines += ['', '## By family', '',
          '| Family / mode | N | Time change [95% interval] | Allocation |',
          '| --- | ---: | ---: | ---: |']
for k, r in sorted(family_results.items()):
    lines.append(f'| {k} | {r["count"]} | {pct(r["ratio"])} [{pct(r["low"])}, {pct(r["high"])}] | {pct(r["allocation_ratio"])} |')
if canonical:
    lines += ['', '## Independent repository Criterion benchmarks', '',
              'Every benchmark runs without `--quick`. These use separate complete processes, so process drift is less controlled than in the adjacent-pair harness.', '',
              '| Target | Workloads | Change across paired process rounds | Each process-pair change |',
              '| --- | ---: | ---: | --- |']
    for k, r in canonical.items():
        lines.append(f'| {k} | {r["rounds"][0]["count"]} | {pct(r["ratio"])} | {", ".join(pct(x["ratio"]) for x in r["rounds"])} |')
lines += ['', '## Every workload', '',
          'Absolute time and allocation are arithmetic means across rounds, per evaluation. Time ratio and interval use paired log ratios. `full` means deserialization plus ledger evaluation, with the repository’s V1/semantics A configuration; `cek` validation uses V3/semantics E.', '',
          '| Workload | Mode | Master µs | Candidate µs | Time change [95% interval] | Master bytes | Candidate bytes | Nominal interval | Native Criterion change |',
          '| --- | --- | ---: | ---: | ---: | ---: | ---: | --- | ---: |']
for r in cases:
    native = pct(r['canonical_ratio']) if r['canonical_ratio'] is not None else '—'
    lines.append(f'| {r["name"]} | {r["mode"]} | {r["baseline_sum_ms"]*1000:.2f} | {r["candidate_sum_ms"]*1000:.2f} | {pct(r["ratio"])} [{pct(r["low"])}, {pct(r["high"])}] | {r["baseline_sum_bytes"]:.0f} | {r["candidate_sum_bytes"]:.0f} | {r["classification"]} | {native} |')
(OUT / f'{a.prefix}-tables.md').write_text('\n'.join(lines) + '\n')

if a.skip_plots:
    print(json.dumps(dict(aggregates=aggregates, order_ratios=order_ratios, canonical=canonical), indent=2))
    raise SystemExit(0)

# Standard static plots, suitable for export; SVG and PNG share the same data.
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

plt.rcParams.update({'font.family': 'DejaVu Sans', 'font.size': 10, 'axes.spines.top': False,
                     'axes.spines.right': False})
plot_groups = [k for k in ['validation/cek', 'validation/full', 'marlowe-semantics/cek',
                         'marlowe-rolepayout/cek', 'nofib/cek', 'force-delay/cek'] if k in aggregates]
fig, ax = plt.subplots(figsize=(10, 4.85))
for y, k in enumerate(plot_groups):
    r = aggregates[k]
    ax.errorbar(100*(r['ratio']-1), y-.1,
                xerr=[[100*max(0, r['ratio']-r['low'])], [100*max(0, r['high']-r['ratio'])]],
                fmt='o', capsize=4, color='#126e82', label='Elapsed time (95% interval)' if y == 0 else None)
    ax.plot(100*(r['allocation_ratio']-1), y+.15, 's', color='#bb6b14',
            label='Allocated bytes' if y == 0 else None)
ax.set_yticks(range(len(plot_groups)), [f'{k} (n={aggregates[k]["count"]})' for k in plot_groups])
ax.invert_yaxis()
ax.axvline(0, color='#666', linewidth=1)
ax.grid(axis='x', alpha=.2)
ax.set_xlabel('Change from master (%) — negative is better')
ax.set_title('Paired harness: RAList with closure erasure')
ax.legend(loc='best', fontsize=9)
caption = f'{len(rounds)} paired rounds'
if 'validation' in canonical:
    caption += '; native validation process-pair changes: ' + ', '.join(pct(r['ratio']) for r in canonical['validation']['rounds'])
fig.text(.99, .012, caption, ha='right', fontsize=8)
fig.tight_layout(rect=(0, .04, 1, 1))
for ext in ['svg', 'png']:
    fig.savefig(OUT / f'{a.prefix}-suites.{ext}', dpi=180)
plt.close(fig)

validation = sorted([r for r in cases if r['suite'] == 'validation' and r['mode'] == 'cek'], key=lambda r: r['ratio'])
if validation:
    fig, ax = plt.subplots(figsize=(11, max(7, len(validation)*.18)))
    for y, r in enumerate(validation):
        color = '#126e82' if r['ratio'] < 1 else '#b14436'
        ax.plot([100*(r['low']-1), 100*(r['high']-1)], [y, y], color=color, linewidth=.8)
        ax.plot(100*(r['ratio']-1), y, 'o', color=color, markersize=3)
    ax.set_yticks(range(len(validation)), [r['name'].split('/', 1)[1] for r in validation], fontsize=8)
    ax.invert_yaxis()
    ax.axvline(0, color='#666', linewidth=1)
    ax.grid(axis='x', alpha=.2)
    ax.set_xlabel('Elapsed-time change from master (%) — negative is better')
    ax.set_title('Paired harness: validation scripts and nominal 95% intervals')
    fig.tight_layout()
    for ext in ['svg', 'png']:
        fig.savefig(OUT / f'{a.prefix}-validation.{ext}', dpi=180)
    plt.close(fig)

print(json.dumps(dict(aggregates=aggregates, order_ratios=order_ratios, canonical=canonical), indent=2))
