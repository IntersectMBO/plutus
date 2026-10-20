#!/usr/bin/env python3
"""Select an experiment without overwriting changes unrelated to this runner."""
import pathlib
import subprocess
import sys
import runpy

closure_transform = runpy.run_path(str(pathlib.Path(__file__).with_name('closure-variants.py')))['transform']
instrument = runpy.run_path(str(pathlib.Path(__file__).with_name('instrument-env.py')))['instrument']
snapshot_on_escape = runpy.run_path(str(pathlib.Path(__file__).with_name('escape-env.py')))['snapshot_on_escape']

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parents[3]
BASE = '5d9feef021f94c0162c8ddcd6b4ec4780d37a5e5'
INTERNAL = pathlib.Path('plutus-core/untyped-plutus-core/src/UntypedPlutusCore/Evaluation/Machine/Cek/Internal.hs')
STEPPABLE = pathlib.Path('plutus-core/untyped-plutus-core/src/UntypedPlutusCore/Evaluation/Machine/SteppableCek/Internal.hs')
CABAL = pathlib.Path('plutus-core/plutus-core.cabal')
MODULE = INTERNAL.with_name('ArrayEnv.hs')
VARIANTS = ['baseline', 'compact-checked', 'compact-unchecked', 'fixed-checked',
            'fixed-unchecked', 'fixed-cow-checked', 'fixed-cow-unchecked',
            'ra-erased', 'fixed-reuse-checked', 'fixed-reuse-erased',
            'ra-erased-context', 'fixed-reuse-erased-context', 'fixed-escape-erased-context']
VARIANTS += [v+'-stats' for v in ['fixed-cow-checked', 'fixed-reuse-checked',
                               'fixed-reuse-erased', 'fixed-reuse-erased-context',
                               'fixed-escape-erased-context']]
def original(path):
    return subprocess.check_output(['git', 'show', f'{BASE}:{path}'], cwd=ROOT, text=True)

def render(name):
    stats = name.endswith('-stats')
    name = name.removesuffix('-stats')
    files = {path: original(path) for path in [INTERNAL, STEPPABLE, CABAL]}
    files[MODULE] = None
    if name == 'baseline':
        return files
    if name.startswith('ra-erased'):
        files[INTERNAL] = closure_transform(files[INTERNAL], False, True, 'context' in name)
        return files
    for path in [INTERNAL, STEPPABLE]:
        files[path] = files[path].replace('import Data.RandomAccessList.Class qualified as Env\n', '')
        files[path] = files[path].replace('import Data.RandomAccessList.SkewBinary qualified as Env',
            'import UntypedPlutusCore.Evaluation.Machine.Cek.ArrayEnv qualified as Env')
    if name.startswith('fixed'):
        files[INTERNAL] = files[INTERNAL].replace('enterComputeCek NoFrame Env.empty term',
            'enterComputeCek NoFrame (Env.emptyFor term) term')
    if 'cow' in name:
        files[INTERNAL] = files[INTERNAL].replace(
            '      computeCek ctx (Env.cons arg env) body',
            '      do\n        extended <- CekM $ unsafeIOToST $ Env.consM arg env\n        computeCek ctx extended body')
    if 'reuse' in name or 'escape' in name:
        files[INTERNAL] = closure_transform(files[INTERNAL], True, 'erased' in name, 'context' in name)
    if name.endswith('unchecked'):
        files[INTERNAL] = files[INTERNAL].replace('      Env.contIndexOne\n', '      Env.uncheckedIndexOne\n')
    anchor = '    UntypedPlutusCore.Evaluation.Machine.Cek.Internal\n'
    assert anchor in files[CABAL]
    files[CABAL] = files[CABAL].replace(anchor,
        anchor + '    UntypedPlutusCore.Evaluation.Machine.Cek.ArrayEnv\n')
    template = 'ReuseEnv.hs' if 'reuse' in name or 'escape' in name else ('CowEnv.hs' if 'cow' in name else ('CompactEnv.hs' if name.startswith('compact') else 'ArrayEnv.hs'))
    files[MODULE] = (HERE/template).read_text()
    if 'escape' in name:
        files[MODULE] = snapshot_on_escape(files[MODULE])
    if stats:
        files[MODULE], files[INTERNAL] = instrument(files[MODULE], files[INTERNAL])
    return files

def main():
    if len(sys.argv) != 2 or sys.argv[1] not in VARIANTS:
        raise SystemExit('Usage: select-variant.py {' + ','.join(VARIANTS) + '}')
    variant = sys.argv[1]
    selected = HERE/'.selected'
    # Recognize both the baseline and the previously applied RAList experiment.
    if selected.exists():
        previous = selected.read_text().strip()
    else:
        previous = ('ra-erased-context'
                    if (ROOT/INTERNAL).read_text() == render('ra-erased-context')[INTERNAL]
                    else 'baseline')
    if previous not in VARIANTS:
        raise SystemExit('Invalid .selected state')
    for path, expected in render(previous).items():
        actual = (ROOT/path).read_text() if (ROOT/path).exists() else None
        if actual != expected:
            raise SystemExit(f'Refusing to overwrite unrelated changes in {path}')
    for path, contents in render(variant).items():
        if contents is None:
            (ROOT/path).unlink(missing_ok=True)
        else:
            (ROOT/path).write_text(contents)
    selected.write_text(variant+'\n')
    print(variant)


if __name__ == '__main__':
    main()
