#!/usr/bin/env python3
"""Join already-analyzed main, confirmation, and nursery-size measurements."""
import csv
from pathlib import Path

OUT = Path(__file__).resolve().parent.parent / 'results' / 'comprehensive'
data = {}
for prefix in ['paired', 'confirmation', 'nursery4m', 'nursery16m']:
    data[prefix] = {(r['name'], r['mode']): r for r in
                    csv.DictReader((OUT / f'{prefix}-per-script.csv').open())}
keys = sorted(data['confirmation'])
assert set(keys) == set(data['nursery4m']) == set(data['nursery16m'])


def pct(value):
    return f'{100*(float(value)-1):+.2f}%'


def interval(row):
    return f'{pct(row["ratio"])} [{pct(row["low"])}, {pct(row["high"])}]'


rows = []
lines = ['# Confirmation and GC sensitivity', '',
         'Nine workloads were selected after the main experiment: representative regressions and a vesting improvement as a control. Selection is recorded in `followup-selection.json`.', '',
         'Fresh confirmation uses 12 paired process rounds with a 100 ms sample target. Separate 4 MiB and 16 MiB nursery experiments each use eight rounds at the same target. The candidate code is identical throughout. These runs cover the selected subset, with its corresponding live input set; they do not replace the full-corpus results or establish a production GC configuration.', '',
         'Changes are candidate/master elapsed time. Negative means faster. Intervals are nominal 95% paired-round bootstrap intervals. The native column pools the two complete native Criterion process pairs under their default runtime.', '',
         '| Workload | Mode | Main run | Fresh confirmation [95% interval] | Native Criterion | 4 MiB nursery [95% interval] | 16 MiB nursery [95% interval] |',
         '| --- | --- | ---: | ---: | ---: | ---: | ---: |']
for key in keys:
    main, confirm, n4, n16 = [data[p][key] for p in data]
    lines.append(f'| {key[0]} | {key[1]} | {pct(main["ratio"])} | {interval(confirm)} | {pct(main["canonical_ratio"])} | {interval(n4)} | {interval(n16)} |')
    row = dict(name=key[0], mode=key[1], native_ratio=float(main['canonical_ratio']))
    for prefix in data:
        for metric in ['ratio', 'low', 'high', 'allocation_ratio', 'baseline_sum_ms', 'candidate_sum_ms',
                       'baseline_gc_wall_ms', 'candidate_gc_wall_ms', 'baseline_gc_cpu_ms', 'candidate_gc_cpu_ms']:
            row[f'{prefix}_{metric}'] = float(data[prefix][key][metric])
    rows.append(row)
lines += ['', '## GC time in the fresh confirmation', '',
          '| Workload | Mode | Master µs | Candidate µs | Master GC µs | Candidate GC µs | Allocation change |',
          '| --- | --- | ---: | ---: | ---: | ---: | ---: |']
for key in keys:
    r = data['confirmation'][key]
    lines.append(f'| {key[0]} | {key[1]} | {float(r["baseline_sum_ms"])*1000:.2f} | {float(r["candidate_sum_ms"])*1000:.2f} | {float(r["baseline_gc_wall_ms"])*1000:.2f} | {float(r["candidate_gc_wall_ms"])*1000:.2f} | {pct(r["allocation_ratio"])} |')
(OUT / 'followup-tables.md').write_text('\n'.join(lines) + '\n')
with (OUT / 'followup-comparison.csv').open('w') as f:
    writer = csv.DictWriter(f, fieldnames=list(rows[0]), lineterminator='\n')
    writer.writeheader()
    writer.writerows(rows)
print('\n'.join(lines))
