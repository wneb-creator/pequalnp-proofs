from pathlib import Path
import json
import hashlib

BASE = Path('/tmp/oec/pequalnp-pilot-99/gap4675/counterexample')
OUT = BASE.parent / 'status_review'
manifest = json.loads((BASE / 'presearch-manifest.json').read_text())
for entry in manifest['files']:
    data = Path(entry['path']).read_bytes()
    assert len(data) == entry['size']
    assert hashlib.sha256(data).hexdigest() == entry['sha256']

raw_cache = {}
records = json.loads((BASE / 'control-validation.json').read_text())
results = []
for record in records:
    graph = json.loads(Path(record['graph']).read_text())
    circuit = json.loads(Path(record['circuit']).read_text())
    n, p = graph['n'], graph['p']
    edges = {tuple(edge) for edge in graph['edges']}
    assert len(edges) == len(graph['edges'])
    assert all(0 <= a < p <= b < n for a, b in edges)
    neighbours = [{b for a, b in edges if a == i} for i in range(p)]
    assert all(len(neighbours[a] & neighbours[b]) <= 1
               for a in range(p) for b in range(a))
    matching = [tuple(edge) for edge in record['matching']]
    cover = set(record['cover'])
    assert set(matching) <= edges
    assert len({a for a, b in matching}) == len(matching)
    assert len({b for a, b in matching}) == len(matching)
    assert all(a in cover or b in cover for a, b in edges)
    assert all(0 <= a < n for a in cover)
    assert len(cover) == len(matching) == graph['tau'] == record['tau']
    if n not in raw_cache:
        # Build each truth table by repeated blocks rather than the engine's row loop.
        rows = 1 << n
        raw_cache[n] = [sum(((1 << (1 << i)) - 1) << start
                            for start in range(1 << i, rows, 2 << i))
                        for i in range(n)]
    wires = raw_cache[n].copy()
    reach = [{i} for i in range(n)]
    mixed = 0
    for op, a, b in circuit['gates']:
        assert op in (0, 1) and 0 <= a < len(wires) and 0 <= b < len(wires)
        wires.append((wires[a] | wires[b]) if op else (wires[a] & wires[b]))
        reach.append((reach[a] | reach[b]) if op else set())
        if op and any(i < p for i in reach[-1]) and any(i >= p for i in reach[-1]):
            mixed += 1
    target = 0
    for a, b in edges:
        target |= wires[a] & wires[b]
    assert 0 <= circuit['output'] < len(wires)
    wrong = (wires[circuit['output']] ^ target).bit_count()
    margin = len(circuit['gates']) - len(edges) - len(cover) + 1
    assert wrong == record['wrong_rows'] == 0
    assert mixed == record['tCount']
    assert margin == record['margin'] >= 0
    results.append({'circuit': record['circuit'], 'rows': 1 << n,
                    'wrong': wrong, 'tCount': mixed, 'margin': margin})

assert len(results) == 72
assert sum(result['tCount'] == 0 for result in results) == 71
summary = {'status': 'PASS preservation-only source/control review; no search launched',
           'manifest_files': len(manifest['files']), 'full_control_replays': len(results),
           'truth_rows_checked': sum(result['rows'] for result in results),
           't0_controls': 71, 'deliberately_dead_mixed_OR_input_controls': 1,
           'all_matching_and_cover_certificates_valid': True,
           'all_margins_nonnegative': True, 'results': results}
(OUT / 'presearch-controls-audit.json').write_text(json.dumps(summary, indent=2) + '\n')
print(json.dumps({key: value for key, value in summary.items() if key != 'results'}, indent=2))
