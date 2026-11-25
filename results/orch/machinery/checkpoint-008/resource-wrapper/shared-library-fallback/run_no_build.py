import argparse
import json
import subprocess
from pathlib import Path

BASE = Path('/tmp/oec/pequalnp-pilot-45')
parser = argparse.ArgumentParser()
parser.add_argument('label', choices=('post-switch', 'post-smoke', 'post-checker008'))
args = parser.parse_args()
lake = str(BASE / 'toolchain/lean-4.36.0-linux/bin/lake')
for name, targets in [('verifier', ['checklemma']),
                      ('proof', ['+PEqualNP.Outside.R_meta_1768_45', '+PEqualNP.Defs'])]:
    prefix = BASE / 'resource-wrapper/shared-library-fallback' / f'{args.label}-{name}'
    with prefix.with_suffix('.stdout').open('wb') as stdout, prefix.with_suffix('.stderr').open('wb') as stderr:
        result = subprocess.run([lake, 'build', '--no-build', *targets],
                                cwd='/workspace/pequalnp-proofs/lean', stdout=stdout, stderr=stderr)
    print(json.dumps({'target': name, 'exit_code': result.returncode,
                      'stdout': str(prefix.with_suffix('.stdout')),
                      'stderr': str(prefix.with_suffix('.stderr'))}), flush=True)
    if result.returncode:
        raise SystemExit(result.returncode)
