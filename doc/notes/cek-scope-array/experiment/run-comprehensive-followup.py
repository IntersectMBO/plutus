#!/usr/bin/env python3
"""Fresh confirmation of selected exceptions, then two separate GC sensitivity runs."""
import json
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
OUT = HERE.parent / 'results' / 'comprehensive'
selection = {
    'selection_basis': 'Selected after the ten-round paired run, before native full-validation results: two representative futures regressions, three cooperative cases, two primality sizes, one Marlowe semantics regression, and a vesting improvement as a control.',
    'names': [
        'validation/future-settle-early-2',
        'validation/future-increase-margin-2',
        'validation/coop-1',
        'validation/coop-2',
        'validation/coop-7',
        'nofib/primetest/05digits',
        'nofib/primetest/30digits',
        'marlowe/semantics/f339f59bdf92495ed2b14e2e4d3705972b4dda59aa929cffe0f1ff5355db8d79',
        'validation/vesting-1',
    ],
}
(OUT / 'followup-selection.json').write_text(json.dumps(selection, indent=2) + '\n')
for prefix, rounds, nursery in [('confirmation', 12, None), ('nursery4m', 8, '4m'), ('nursery16m', 8, '16m')]:
    command = [sys.executable, str(HERE / 'run-comprehensive.py'), 'paired', '--rounds', str(rounds),
               '--seconds', '.1', '--prefix', prefix, '--only', *selection['names']]
    if nursery:
        command += ['--nursery', nursery]
    print(prefix, flush=True)
    with (HERE / 'logs' / f'comprehensive-{prefix}.log').open('w') as log:
        subprocess.run(command, stdout=log, stderr=subprocess.STDOUT, check=True)
