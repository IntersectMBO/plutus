#!/usr/bin/env python3
"""Export independent array experiment patches and verify their resulting source."""
import argparse
import difflib
import gzip
import hashlib
import json
import pathlib
import runpy
import subprocess
import tempfile

HERE = pathlib.Path(__file__).resolve().parent
OUT = HERE.parent / 'patches'
selector = runpy.run_path(str(HERE / 'select-variant.py'))
render = selector['render']
BASE = selector['BASE']
VARIANTS = [
    'compact-checked', 'compact-unchecked',
    'fixed-checked', 'fixed-unchecked',
    'fixed-cow-checked', 'fixed-cow-unchecked',
    'fixed-reuse-checked', 'fixed-reuse-erased',
    'fixed-reuse-erased-context', 'fixed-escape-erased-context',
]


def verify_patch(patch, baseline, expected):
    with tempfile.TemporaryDirectory(prefix='cek-array-patch-') as directory:
        root = pathlib.Path(directory)
        for path, contents in baseline.items():
            if contents is not None:
                target = root / path
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_text(contents)
        for command in [['git', 'apply', '--check'], ['git', 'apply']]:
            subprocess.run(command, input=patch, cwd=root, check=True, capture_output=True)
        for path, contents in expected.items():
            target = root / path
            actual = target.read_text() if target.exists() else None
            if actual != contents:
                raise AssertionError(f'Patch produces unexpected source: {path}')
        subprocess.run(['git', 'apply', '--reverse', '--check'],
                       input=patch, cwd=root, check=True, capture_output=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true', help='Verify saved exports without rewriting them')
    args = parser.parse_args()
    baseline = render('baseline')
    manifest = {
        'base_commit': BASE,
        'application': 'Each patch applies independently to the base commit; do not stack patches.',
        'experimental_only': True,
        'variants': {},
    }
    artifacts = {}
    for name in VARIANTS:
        expected = render(name)
        chunks = []
        for path in sorted(baseline):
            before, after = baseline[path], expected[path]
            if before == after:
                continue
            chunks.append(f'diff --git a/{path} b/{path}\n')
            if before is None:
                chunks.append('new file mode 100644\n')
            chunks.extend(difflib.unified_diff(
                (before or '').splitlines(keepends=True),
                (after or '').splitlines(keepends=True),
                fromfile=f'a/{path}' if before is not None else '/dev/null',
                tofile=f'b/{path}' if after is not None else '/dev/null'))
        patch = ''.join(chunks).encode()
        verify_patch(patch, baseline, expected)
        # Previously archived patches must produce the same source as these exports.
        archived = HERE.parent / 'results' / f'{name}.patch.gz'
        if archived.exists():
            verify_patch(gzip.decompress(archived.read_bytes()), baseline, expected)
        artifacts[f'{name}.patch'] = patch
        manifest['variants'][name] = {
            'patch_sha256': hashlib.sha256(patch).hexdigest(),
            'scope_information': (
                'maximum lexical lambda depth' if name.startswith('fixed') else
                'full closedness proof for unchecked lookup' if name.endswith('unchecked') else
                'none; checked exact-length array control'),
            'unchecked_lookup': name.endswith('unchecked'),
            'closure_erasure': 'context' if 'erased-context' in name else
                               'syntactic' if 'erased' in name else 'none',
            'source_sha256': {str(path): hashlib.sha256(text.encode()).hexdigest()
                              for path, text in expected.items() if text is not None},
        }
    artifacts['manifest.json'] = (json.dumps(manifest, indent=2) + '\n').encode()
    if not args.check:
        OUT.mkdir(exist_ok=True)
    for name, contents in artifacts.items():
        path = OUT / name
        if args.check:
            if path.read_bytes() != contents:
                raise AssertionError(f'Stale export: {path}')
        else:
            path.write_bytes(contents)
    print(f'PASS: {len(VARIANTS)} independent patches apply, match generated source, and reverse cleanly')


if __name__ == '__main__':
    main()
