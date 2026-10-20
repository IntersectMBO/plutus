#!/usr/bin/env python3
"""Balanced process repetitions. Run only after all builds/tests have stopped."""
import argparse
import json
import pathlib
import subprocess
import time

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parents[3]
RESULTS = HERE.parent / 'results'
VARIANTS = ['baseline', 'compact-checked', 'compact-unchecked', 'fixed-checked',
            'fixed-unchecked', 'fixed-cow-checked', 'fixed-cow-unchecked']
p = argparse.ArgumentParser()
p.add_argument('--rounds', type=int, default=5)
p.add_argument('--seconds', type=float, default=.05)
p.add_argument('--cpu', type=int, default=15)
p.add_argument('--variants', nargs='+', default=VARIANTS)
p.add_argument('--group', choices=['cek', 'full', 'prep'], default='cek')
p.add_argument('--prefix', default='matrix')
a = p.parse_args()
RESULTS.mkdir(exist_ok=True)
commands = []
for r in range(a.rounds):
    # Rotate and reverse to reduce order/frequency drift; every process recalibrates.
    order = a.variants[r % len(a.variants):] + a.variants[:r % len(a.variants)]
    if r % 2:
        order = order[::-1]
    for variant in order:
        cmd = ['taskset', '-c', str(a.cpu), str(HERE/'bin'/variant), 'sample',
               str(ROOT/'plutus-benchmark/validation/data'), str(a.seconds), a.group,
               '+RTS', '-N1', '-T', '-s', '-RTS']
        out = RESULTS/f'{a.prefix}-{a.group}-{variant}-r{r+1}.csv'
        start = time.time()
        print(f'round {r+1} {a.group} {variant}', flush=True)
        with out.open('w') as f, out.with_suffix('.rts.txt').open('w') as err:
            subprocess.run(cmd, stdout=f, stderr=err, check=True, cwd=ROOT)
        commands.append(dict(round=r+1, variant=variant, command=cmd,
                             output=out.name, elapsed=time.time()-start))
        (RESULTS/f'{a.prefix}-{a.group}-commands.json').write_text(json.dumps(commands, indent=2)+'\n')
