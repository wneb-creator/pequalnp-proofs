import hashlib
import json
from pathlib import Path
import subprocess


ROOT = Path('/tmp/oec/pequalnp-pilot-66')
SOLVER = ROOT / 'cadical-rel-3.1.0/build/cadical'


def check(label, model_name, two_pivots, expected):
    model = json.loads((ROOT / model_name).read_text())
    command = ['python3', str(ROOT / 'circuit-sat-two-pivots.py'), '--graph', 'cycle5',
               '--name', label, '--gates', '8', '--pivotal-gates', '--emit-only']
    if two_pivots:
        command.append('--unowned-two-pivots')
    with (ROOT / (label + '-emit.log')).open('w') as log:
        subprocess.run(command, check=True, stdout=log, stderr=subprocess.STDOUT)
    tag = 'sat-' + label + '-8-pivotal' + ('-twopivots' if two_pivots else '')
    meta = json.loads((ROOT / (tag + '-encoding.json')).read_text())
    base = (ROOT / (tag + '.cnf')).read_text()
    header, body = base.split('\n', 1)
    _, _, variables, clauses = header.split()
    pins = []
    for j, (op, a, b) in enumerate(model['gates']):
        pins.extend([meta['op'][j] if op == 'and' else -meta['op'][j],
                     meta['ports'][j][0][a], meta['ports'][j][1][b]])
    text = f'p cnf {variables} {int(clauses) + len(pins)}\n' + body
    text += ''.join(f'{literal} 0\n' for literal in pins)
    cnf = ROOT / (tag + '-pinned.cnf')
    cnf.write_text(text)
    logfile = ROOT / (tag + '-pinned-solver.log')
    with logfile.open('w') as log:
        result = subprocess.run([str(SOLVER), '-t', '30', str(cnf)],
                                stdout=log, stderr=subprocess.STDOUT)
    assert result.returncode == expected, (label, result.returncode, expected)
    if result.returncode == 10:
        assignment = {int(x) for line in logfile.read_text().splitlines()
                      if line.startswith('v ') for x in line[2:].split()}
        for line in text.splitlines()[1:]:
            assert any(int(x) in assignment for x in line.split()[:-1])
    return {'label': label, 'model': model_name, 'two_pivots': two_pivots,
            'expected_returncode': expected, 'actual_returncode': result.returncode,
            'cnf_sha256': hashlib.sha256(cnf.read_bytes()).hexdigest(), 'verdict': 'PASS'}


def main():
    safe = 'sat-repairdiagsafec5-8-singletonsafe-unowned-minimal.json'
    unsafe = 'sat-repairdiagc5-8-unowned-minimal.json'
    rows = [check('onepivotcontrol', safe, False, 10),
            check('onepivotexcluded', safe, True, 20),
            check('threepivotallowed', unsafe, True, 10)]
    (ROOT / 'two-pivots-validation.json').write_text(json.dumps(rows, indent=2) + '\n')
    print(json.dumps(rows))


if __name__ == '__main__':
    main()
