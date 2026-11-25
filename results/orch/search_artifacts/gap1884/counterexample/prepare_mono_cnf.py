import hashlib
import json
from pathlib import Path
import enc2_base

P = Path(__file__).resolve().parent
rows10 = [r for r in range(1024) if all(bool(r >> j & 1) != enc2_base.target(r) or enc2_base.target(r ^ (1 << j)) != enc2_base.target(r) for j in range(1, 10))]
assert len(rows10) == 38
rows = [r | (int(not (r & 1)) << 10) for r in rows10]
assert rows10 == json.loads((P / 'cofactor-boundary10.json').read_text())
assert rows == json.loads((P / 'cofactor-boundary11.json').read_text())
old = json.loads(Path('/tmp/oec/pequalnp-pilot-99/gap2590/counterexample/upper20-lex.json').read_text())
def ren(x):
    return x if x < 10 else x + 1
control = {'physical_inputs': 11, 'input_map': list(range(10)), 'free_unary': 'not',
           'gates': [[op, ren(a), ren(b)] for op, a, b in old['gates']], 'output': ren(old['output'])}
(P / 'mono20-control.circuit.json').write_text(json.dumps(control, indent=2) + '\n')

for size in (18, 20):
    clauses, ix, sections = enc2_base.make(11, size, rows, True)
    base = P / ('mono' + str(size) + '-enc2')
    mx = max(abs(lit) for clause in clauses for lit in clause)
    with base.with_suffix('.cnf').open('w') as f:
        f.write(f'p cnf {mx} {len(clauses)}\n')
        for clause in clauses:
            f.write(' '.join(map(str, clause)) + ' 0\n')
    meta = {'physical_inputs': 11, 'gates': size, 'rows10': rows10, 'rows11': rows,
            'op_codes': {'AND': 0, 'OR': 1, 'TRUE': 2}, 'no_internal_NOT': True,
            'normalized_enc2': True, 'clauses': len(clauses), 'max_var': mx, 'sections': sections,
            'cnf_sha256': hashlib.sha256(base.with_suffix('.cnf').read_bytes()).hexdigest()}
    base.with_suffix('.meta.json').write_text(json.dumps(meta, indent=2) + '\n')
    print(base.name, 'clauses', len(clauses), 'vars', mx, 'SHA', meta['cnf_sha256'])
    if size != 20:
        continue
    # A concrete assignment for every variable of the positive-control formula.
    positive = set()
    for j, (op, a, b) in enumerate(control['gates']):
        positive.update((ix(0, j, op), ix(1, j, a), ix(2, j, b)))
    positive.add(ix(6, 0, control['output']))
    for r in rows:
        w = [bool(r >> i & 1) for i in range(11)]
        for j, (op, a, b) in enumerate(control['gates']):
            if w[a]: positive.add(ix(4, j, r))
            if w[b]: positive.add(ix(5, j, r))
            w.append(w[a] and w[b] if op == 0 else w[a] or w[b])
            if w[-1]: positive.add(ix(3, j, r))
    failed = [k for k, clause in enumerate(clauses) if not any((lit in positive) if lit > 0 else (-lit not in positive) for lit in clause)]
    assert not failed, failed[:10]
    (P / 'mono20-control.model.json').write_text(json.dumps(sorted(positive)) + '\n')
    (P / 'mono20-control-clause-check.json').write_text(json.dumps({'clauses_checked': len(clauses), 'failed_clauses': failed, 'all_unlisted_variables_false': True}, indent=2) + '\n')
    print('CONTROL assignment satisfies every', len(clauses), 'CNF clauses')
