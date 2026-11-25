import hashlib
import json
import subprocess
import tarfile
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent
ARCHIVE = ROOT.parent / 'counterexample-evidence.tar.gz'
SOLVER = Path('/tmp/oec/pequalnp-pilot-46/toolchain/lean-4.36.0-linux/bin/cadical')


def record(name):
    data = (ROOT / name).read_bytes()
    result = {'path': name, 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}
    if name.endswith('.cnf'):
        result['header'] = data.splitlines()[0].decode('ascii')
    return result


if __name__ == '__main__':
    result = subprocess.run(['rg', '--files', '-g', '*.py', '-g', '*.md', '-g', '*.json',
                             '-g', '*.log', '-g', '*.cnf'], cwd=ROOT,
                            text=True, capture_output=True, check=True)
    discovered = sorted(result.stdout.splitlines())
    small_cnfs = {'c6-macro-and2.cnf', 'c6-macro-or4.cnf', 'theta-macro-and3.cnf',
                  'cycle12-macro-topo-and5.cnf', 'cycle8-macro-private-or6.cnf'}
    for directory in ['variable-4x4-and3-46', 'variable-4x4-and3-47',
                      'variable-fooling-4x4-and3-46']:
        rows = json.loads((ROOT / directory / 'summary-000.json').read_text())
        assert rows[-1]['status'] == 20
        small_cnfs.add(f"{directory}/iteration-{rows[-1]['iteration']:03d}.cnf")
    assert small_cnfs <= set(discovered)
    included = [name for name in discovered if name != 'ARTIFACT_INVENTORY.json'
                and (not name.endswith('.cnf') or name in small_cnfs)]
    omitted = [name for name in discovered if name.endswith('.cnf') and name not in small_cnfs]
    inventory = {'frozen_utc': datetime.now(timezone.utc).isoformat(),
                 'status': 'No full-function witness. External finite SAT/Python evidence only.',
                 'solver_path': str(SOLVER),
                 'solver_sha256': hashlib.sha256(SOLVER.read_bytes()).hexdigest(),
                 'included': [record(name) for name in included],
                 'omitted_regenerable_cnfs': [record(name) for name in omitted]}
    (ROOT / 'ARTIFACT_INVENTORY.json').write_text(json.dumps(inventory, indent=2))
    with tarfile.open(ARCHIVE, 'w:gz') as tar:
        for name in included + ['ARTIFACT_INVENTORY.json']:
            tar.add(ROOT / name, arcname='counterexample/' + name, recursive=False)
    data = ARCHIVE.read_bytes()
    print(json.dumps({'archive': str(ARCHIVE), 'bytes': len(data),
                      'sha256': hashlib.sha256(data).hexdigest(),
                      'included_files': len(included) + 1,
                      'included_bytes': sum(row['bytes'] for row in inventory['included']),
                      'omitted_cnf_files': len(omitted),
                      'omitted_cnf_bytes': sum(row['bytes'] for row in inventory['omitted_regenerable_cnfs'])}))
