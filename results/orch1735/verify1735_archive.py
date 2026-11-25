from pathlib import Path
import hashlib
import json

base = Path('/workspace/pequalnp-proofs/results/orch1735/finite')
manifest = json.loads((base / 'MANIFEST.json').read_text())
files = manifest['files']
assert len({e['path'] for e in files}) == len(files)
for entry in files:
    data = (base / entry['path']).read_bytes()
    assert len(data) == entry['bytes']
    assert hashlib.sha256(data).hexdigest() == entry['sha256']
    data.decode('utf-8')
assert {p.relative_to(base).as_posix() for p in base.rglob('*') if p.is_file()} == {
    e['path'] for e in files
} | {'MANIFEST.json'}


def minimal(terms):
    result = []
    for term in sorted(set(terms), key=lambda a: (a.bit_count(), a)):
        if not any(old & term == old for old in result):
            result.append(term)
    return result


def implies(a, b):
    return all(any(v & u == v for v in b) for u in a)


checks = []
for path in sorted(base.glob('*.witness.json')):
    data = json.loads(path.read_text())
    n = data['n']
    gates = data['gates']
    assert len(gates) == data['size']
    edges = {tuple(sorted(e)) for e in data['graph_edges']}
    assert all(0 <= a < b < n for a, b in edges)
    target = {1 << a | 1 << b for a, b in edges}
    terms = [[1 << i] for i in range(n)]
    raw = [{i} for i in range(n)]
    ancestors = [set() for i in range(n)]
    clean = []
    incomparable = []
    for j, (op, a, b) in enumerate(gates):
        assert op in ('and', 'or') and 0 <= a < n+j and 0 <= b < n+j
        incomparable.append(not implies(terms[a], terms[b]) and not implies(terms[b], terms[a]))
        terms.append(minimal([x | y for x in terms[a] for y in terms[b]]) if op == 'and'
                     else minimal(terms[a] + terms[b]))
        raw.append(set() if op == 'and' else raw[a] | raw[b])
        ancestors.append(ancestors[a] | ancestors[b] | {j})
        clean.append(all(any(e & t == e for e in target) for t in terms[-1]))
    output = data.get('output', n+len(gates)-1)
    assert set(terms[output]) == target
    tops = [j for j, (op, _, _) in enumerate(gates) if op == 'and' and clean[j]]
    junk = [j for j, (op, _, _) in enumerate(gates) if op == 'and' and not clean[j]]
    topform = all(not set(tops).intersection(ancestors[n+j] - {j})
                  for j, (op, _, _) in enumerate(gates) if op == 'and')
    assert topform
    assert tops == data['tops'] and junk == data['junk']
    nested = {(i, j) for i in junk for j in junk if i != j and i in ancestors[n+j]}
    assert nested == {tuple(pair) for pair in data['nested_junk_pairs']}
    stars = set()
    for j in tops:
        _, a, b = gates[j]
        for u in raw[a]:
            for v in raw[b]:
                assert u != v
                stars.add(tuple(sorted((u, v))))
    assert stars <= edges
    ustar = edges - stars
    assert ustar == {tuple(sorted(pair)) for pair in data['Ustar']}
    if 'star_edges' in data:
        assert stars == {tuple(sorted(pair)) for pair in data['star_edges']}
    if n == 5:
        assert len(edges) == 5 and all(sum(i in e for e in edges) == 2 for i in range(n))
    if 'incomparable' in path.name or 'reduced-nested9' in path.name:
        assert all(incomparable)
    if n == 26:
        assert edges == {(p, 13+l) for p in range(13) for l in range(13)
                         if (p-l) % 13 in (0, 1, 3, 9)}
        maximal_negatives = 0
        for leftmask in range(1 << 13):
            left = {p for p in range(13) if leftmask >> p & 1}
            right = {q for q in range(13,26) if all((p,q) not in edges for p in left)}
            closure = {p for p in range(13) if all((p,q) not in edges for q in right)}
            maximal_negatives += closure == left
        assert maximal_negatives == data['maximal_negative_rows'] == 704
    checks.append({'file': path.name, 'size': len(gates), 'edges': len(edges),
                   'junk': len(junk), 'nested_pairs': len(nested), 'tops': len(tops),
                   'Ustar': len(ustar), 'TopForm': topform,
                   'all_fanins_incomparable': all(incomparable),
                   'maximum_intermediate_antichain': max(map(len, terms)),
                   'full_semantics_via_minimal_monomials': True})

census = json.loads((base/'cnf-family-census.json').read_text())
for record in census:
    n, kind = record['n'], record['kind']
    edges = ([(0,i) for i in range(1,n)] if kind == 'star'
             else [(i,i+1) for i in range(n-1)])
    if kind == 'cycle':
        edges.append((n-1,0))
    covers = [m for m in range(1 << n) if all((m >> a & 1) or (m >> b & 1) for a,b in edges)]
    minimal_covers = [m for m in covers if all(m ^ (1 << i) not in covers
                                            for i in range(n) if m >> i & 1)]
    sizes = [m.bit_count() for m in minimal_covers]
    assert sorted(sizes) == sorted(record['minimal_covers'])
    assert min(sizes) == record['cover']
    assert len(edges) == record['edges']
    assert sum(sizes)-1 == record['CNF_gates']
    assert len(edges)+min(sizes)-1 == record['star_gates']
    assert record['CNF_gates']-record['star_gates'] == record['overhead']
    assert max(0,len(sizes)-2) == record['junk_chain_length']

result = {'manifest_files': len(files), 'manifest_bytes': sum(e['bytes'] for e in files),
          'manifest_all_hashes_and_census_match': True, 'witnesses': checks,
          'cnf_family_census_records_verified': len(census)}
print(json.dumps(result, indent=2))
