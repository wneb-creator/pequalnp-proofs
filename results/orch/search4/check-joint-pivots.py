import hashlib
import json
from pathlib import Path
import subprocess


ROOT = Path('/tmp/oec/pequalnp-pilot-66')
SOLVER = ROOT / 'cadical-rel-3.1.0/build/cadical'
GATES = [('or', 0, 1), ('or', 0, 2), ('or', 1, 2),
         ('and', 3, 4), ('or', 0, 6), ('and', 5, 7)]
EDGES = [(0, 1), (0, 2), (1, 2)]


def evaluate(x, disabled=None):
    wire = [bool(x & (1 << i)) for i in range(3)]
    for j, (op, a, b) in enumerate(GATES):
        wire.append(False if j == disabled else
                    (wire[a] and wire[b] if op == 'and' else wire[a] or wire[b]))
    return wire


def check(label, joint, expected):
    command = ['python3', str(ROOT / 'circuit-sat-joint-pivots.py'), '--graph', 'cycle3',
               '--name', label, '--gates', '6', '--unowned-two-pivots', '--emit-only']
    if joint:
        command.append('--defective-two-pivots')
    with (ROOT / (label + '-emit.log')).open('w') as log:
        subprocess.run(command, check=True, stdout=log, stderr=subprocess.STDOUT)
    tag = 'sat-' + label + '-6-pivotal-twopivots' + ('-jointpivots' if joint else '')
    meta = json.loads((ROOT / (tag + '-encoding.json')).read_text())
    base = (ROOT / (tag + '.cnf')).read_text()
    header, body = base.split('\n', 1)
    _, _, variables, clauses = header.split()
    pins = []
    for j, (op, a, b) in enumerate(GATES):
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
    assert result.returncode == expected
    if expected == 10:
        assignment = {int(x) for line in logfile.read_text().splitlines()
                      if line.startswith('v ') for x in line[2:].split()}
        assert all(any(int(x) in assignment for x in line.split()[:-1])
                   for line in text.splitlines()[1:])
    return {'label': label, 'joint': joint, 'expected_returncode': expected,
            'actual_returncode': result.returncode,
            'cnf_sha256': hashlib.sha256(cnf.read_bytes()).hexdigest(), 'verdict': 'PASS'}


def main():
    assert all(evaluate(x)[-1] == any(x & (1 << a) and x & (1 << b) for a, b in EDGES)
               for x in range(8))
    pivotal = [[list(edge) for edge in EDGES
                if not evaluate((1 << edge[0]) | (1 << edge[1]), j)[-1]] for j in range(6)]
    assert all(pivotal) and pivotal[3] == [[1, 2]] and len(pivotal[5]) == 3
    assert evaluate(1)[6]
    rows = [check('dirtyonepivotcontrol', False, 10), check('dirtyonepivotexcluded', True, 20)]
    report = {'note': 'A nonminimum triangle diagnostic, outside the target graph class. '
                      'Gate3 is owned and unsound, with exactly one pivotal edge; '
                      'gate5 is unowned with three pivotal edges. Every gate is pivotal.',
              'n': 3, 'edges': EDGES, 'gates': GATES, 'all_inputs_checked': 8,
              'pivotal_edges': pivotal, 'results': rows}
    (ROOT / 'joint-pivots-validation.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(rows))


if __name__ == '__main__':
    main()
