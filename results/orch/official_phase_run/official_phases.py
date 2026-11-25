"""Phase preferences for the unchanged official LinkN2 formula."""
import argparse
import hashlib
import json
from pathlib import Path


def normalize(gates, n):
    gs = [[3 if op == 2 else op, a, a if op == 2 else b] for op, a, b in gates]
    for op, a, b in gs:
        assert op in (0, 1, 3) and a >= 0 and b >= 0
    for g in gs:
        if g[0] < 2:
            g[1:] = sorted(g[1:])
            assert g[1] != g[2]
    swaps = 0
    while True:
        j = next((j for j in range(len(gs) - 1)
                  if n + j not in gs[j + 1][1:]
                  and (gs[j][1], gs[j][2], gs[j][0]) >
                      (gs[j + 1][1], gs[j + 1][2], gs[j + 1][0])), None)
        if j is None:
            break
        gs[j], gs[j + 1] = gs[j + 1], gs[j]
        for g in gs[j + 2:]:
            g[1:] = [n + j + 1 if w == n + j else n + j if w == n + j + 1 else w
                     for w in g[1:]]
            if g[0] < 2:
                g[1:] = sorted(g[1:])
        swaps += 1
        assert swaps < 100000
    return gs, swaps


def truth(gs, n, official=False):
    count = 1 << n
    mask = (1 << count) - 1
    vals = [sum(1 << x for x in range(count) if x >> i & 1) for i in range(n)]
    for op, a, b in gs:
        av = vals[a] if a >= 0 else 0
        bv = vals[b] if b >= 0 else 0
        vals.append(av & bv if op == 0 else av | bv if op == 1 else mask ^ av)
    return vals[-1]


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--directory', type=Path, required=True)
    p.add_argument('--seed', type=Path, required=True)
    p.add_argument('--out', type=Path, required=True)
    args = p.parse_args()
    meta = json.loads((args.directory / 'metadata.json').read_text())
    rows = json.loads((args.directory / 'rows.json').read_text())
    n, s = meta['n'], meta['gates']
    original = json.loads(args.seed.read_text())['gates']
    assert len(original) == s
    gates, swaps = normalize(original, n)
    assert truth(gates, n, True) == truth(original, n)
    width = 2**n + n + s + 2
    ix = lambda k, j, a: (k * (s + 1) + j) * width + a + 1
    values = {}
    for j, (op, a, b) in enumerate(gates):
        assert 0 <= a < n + j and 0 <= b < n + j
        for t in range(4):
            values[ix(0, j, t)] = t == op
        for t in range(n + j + 1):
            values[ix(1, j, t)] = t == a
            values[ix(2, j, t)] = t == b
        values[ix(7, j, 0)] = False
    for t in range(n + s + 1):
        values[ix(6, 0, t)] = t == n + s - 1
    for x in rows:
        ws = [bool(x >> i & 1) for i in range(n)]
        for j, (op, a, b) in enumerate(gates):
            av, bv = ws[a], ws[b]
            z = av and bv if op == 0 else av or bv if op == 1 else not av
            values[ix(4, j, x)] = av
            values[ix(5, j, x)] = bv
            values[ix(3, j, x)] = z
            ws.append(z)
    # Check every original clause. Preferences need not satisfy target rows,
    # but any violated structural clause would make this a poor control.
    violated = []
    used = set()
    count = 0
    with (args.directory / 'official.cnf').open() as f:
        for line in f:
            if line.startswith(('c', 'p')):
                continue
            clause = list(map(int, line.split()))
            assert clause.pop() == 0
            count += 1
            used.update(map(abs, clause))
            assert all(abs(v) in values for v in clause)
            if not any(values[abs(v)] == (v > 0) for v in clause):
                violated.append({'clause': count, 'literals': clause})
    assert used == set(values) and count == meta['clauses']
    # The chosen last-output selector is the only permitted source of error.
    output_selector = ix(6, 0, n + s - 1)
    assert all(len(c['literals']) == 2 and c['literals'][0] == -output_selector
               for c in violated), violated[:10]
    args.out.mkdir(parents=True, exist_ok=True)
    phase_path = args.out / 'phases.txt'
    phase_path.write_text(' '.join(str(v if values[v] else -v) for v in sorted(values)) + '\n')
    native = [[2 if op == 3 else op, a, -1 if op == 3 else b] for op, a, b in gates]
    (args.out / 'normalized-seed.json').write_text(json.dumps({'gates': native}, indent=2))
    result = {'source': str(args.seed), 'source_sha256': hashlib.sha256(args.seed.read_bytes()).hexdigest(),
              'gates': s, 'normalization_swaps': swaps, 'all_input_function_preserved': True,
              'phase_variables': len(values), 'clauses_checked': count,
              'violated_output_clauses': violated, 'violated_structural_clauses': 0,
              'cnf_sha256': meta['sha256'],
              'scope': 'Preferences only for unchanged official CNF; seed is not a counterexample'}
    (args.out / 'metadata.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in ['normalization_swaps', 'phase_variables',
          'clauses_checked', 'violated_structural_clauses']}), flush=True)
    print('Violated target output clauses', len(violated), flush=True)


if __name__ == '__main__':
    main()
