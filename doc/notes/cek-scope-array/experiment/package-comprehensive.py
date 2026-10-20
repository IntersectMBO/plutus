#!/usr/bin/env python3
"""Validate coverage and preserve build/runtime provenance after all runs finish."""
import csv
import datetime
import gzip
import hashlib
import json
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
OUT = HERE.parent / 'results' / 'comprehensive'
expected_sizes = {'validation': 89, 'validation-full': 89, 'marlowe': 200, 'nofib': 22, 'force-delay': 16}
inventory = json.loads((OUT / 'canonical-inventory.json').read_text())
commands = json.loads((OUT / 'canonical-commands.json').read_text())
assert len(commands) == 20 and all(c['exit_code'] == 0 for c in commands)
native_count = 0
for target, size in expected_sizes.items():
    for variant in ['baseline', 'ra-erased-context']:
        for rn in [1, 2]:
            path = OUT / f'canonical-{target}-{variant}-r{rn}.csv'
            rows = list(csv.DictReader(path.open()))
            assert len(rows) == size
            assert {r['Name'] for r in rows} == set(inventory[target])
            native_count += len(rows)
for prefix, count in [('paired', 8320), ('confirmation', 360), ('nursery4m', 240), ('nursery16m', 240)]:
    rows = list(csv.DictReader((OUT / f'{prefix}.csv').open()))
    assert len(rows) == count, (prefix, len(rows))
checks = json.loads((OUT / 'correctness.json').read_text())
assert len(checks) == 327 and sum(r.get('full_status') == 'ok' for r in checks) == 89
for name, expected in json.loads((OUT / 'binaries.json').read_text()).items():
    assert hashlib.sha256((HERE / 'bin' / 'comprehensive' / name).read_bytes()).hexdigest() == expected
assert hashlib.sha256((HERE / 'Comprehensive.hs').read_bytes()).hexdigest() == json.loads(
    (OUT / 'environment.json').read_text())['source_hashes']['Comprehensive.hs']
subprocess.run(['git', 'diff', '--exit-code', 'HEAD', '--', 'plutus-core'], cwd=ROOT, check=True)
assert (HERE / '.selected').read_text().strip() == 'baseline'

# Preserve values while normalizing text evidence to LF and trimming trailing whitespace.
for path in OUT.iterdir():
    if path.suffix in ['.csv', '.log', '.md', '.svg']:
        path.write_text('\n'.join(line.rstrip() for line in path.read_text().splitlines()).rstrip() + '\n')
logs = [HERE / 'logs' / f'{name}.log' for name in [
    'comprehensive-build-baseline', 'comprehensive-save-baseline-final',
    'comprehensive-save-ra-erased-context', 'comprehensive-check', 'comprehensive-paired',
    'comprehensive-canonical', 'comprehensive-confirmation', 'comprehensive-nursery4m', 'comprehensive-nursery16m']]
for pattern in ['paired-*.stderr', 'confirmation-*.stderr', 'nursery4m-*.stderr', 'nursery16m-*.stderr']:
    logs.extend((HERE / 'logs').glob(pattern))
for path in logs:
    assert path.exists(), path
    text = '\n'.join(line.rstrip() for line in path.read_text().splitlines()).rstrip() + '\n'
    (OUT / (path.name + '.gz')).write_bytes(gzip.compress(text.encode(), mtime=0))
(OUT / 'cabal-plan.json.gz').write_bytes(gzip.compress((ROOT / 'dist-newstyle/cache/plan.json').read_bytes(), mtime=0))
sources = ['Comprehensive.hs', 'build-comprehensive.sh', 'run-comprehensive.py',
           'analyze-comprehensive.py', 'run-comprehensive-followup.py',
           'summarize-comprehensive-followup.py', 'package-comprehensive.py',
           'requirements-analysis.txt', 'select-variant.py', 'closure-variants.py']
provenance = dict(finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                  native_estimates=native_count, paired_measurements=8320,
                  confirmation_measurements=360, nursery_measurements=480,
                  exact_cek_checks=327, exact_full_checks=89,
                  production_source='baseline, unchanged from recorded master',
                  source_sha256={name: hashlib.sha256((HERE / name).read_bytes()).hexdigest() for name in sources})
(OUT / 'completion.json').write_text(json.dumps(provenance, indent=2) + '\n')
print(json.dumps(provenance, indent=2))
