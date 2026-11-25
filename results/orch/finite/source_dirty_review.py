from pathlib import Path
from collections import Counter
import hashlib, itertools, json, re

base = Path('/tmp/oec/pequalnp-pilot-75/finite')
expected = {
    'synth_sat_sources_dirty.py': '1fc86038dc91c1d981d3779872dbce905d396af195659ab7cb5f5f6fb5494f2d',
    'source_tree7_census.py': '4b23c7ca48c9678fb6b9182e36d9954e7cb8021893f1a4cd73a7e6fe51fa2d48',
}
for name, digest in expected.items():
    assert hashlib.sha256((base/name).read_bytes()).hexdigest() == digest
print('SOURCE_HASHES PASS')

def validate(prefix):
    meta = json.loads(prefix.with_suffix('.json').read_text())
    n, K, edges = meta['n'], meta['K'], meta['edges']
    m = len(edges)
    independent = [x for x in range(1 << n)
                   if all(not ((x >> a & 1) and (x >> b & 1)) for a,b in edges)]
    maximal = [x for x in independent if all((x | (1 << a)) not in independent
               for a in range(n) if not (x >> a & 1))]
    rows = [(1 << a) | (1 << b) for a,b in edges] + maximal
    assert rows == meta['rows']
    names = [tuple(x) for x in meta['variables']]
    assert len(set(names)) == len(names)
    ids = {name: i+1 for i,name in enumerate(names)}
    v = lambda *name: ids[name]
    R = len(rows)
    ops = [v('op',j) for j in range(K)]
    A = [[v('asel',j,a) for a in range(n+j)] for j in range(K)]
    B = [[v('bsel',j,a) for a in range(n+j)] for j in range(K)]
    assert ops == meta['ops'] and A == meta['asel'] and B == meta['bsel']
    assert [v('pure_or',j) for j in range(K)] == meta['pure']
    assert [v('operand_a_pure',j) for j in range(K)] == meta['pa']
    assert [v('operand_b_pure',j) for j in range(K)] == meta['pb']
    assert meta['goal'] == 'every source AND true on some maximal independent set'
    clauses = []
    add = lambda *xs: clauses.append(tuple(xs))
    for j in range(K):
        for selectors in (A[j],B[j]):
            add(*selectors)
            for a,b in itertools.combinations(selectors,2): add(-a,-b)
        for a in range(n+j):
            for b in range(n+j):
                if a >= b: add(-A[j][a],-B[j][b])
        for selectors, kind in ((A[j],'aval'),(B[j],'bval')):
            for a,s in enumerate(selectors):
                for t,point in enumerate(rows):
                    value = v(kind,j,t)
                    if a < n: add(-s,value if point >> a & 1 else -value)
                    else:
                        previous = v('val',a-n,t)
                        add(-s,-value,previous)
                        add(-s,value,-previous)
        for t in range(R):
            a,b,z,o = v('aval',j,t),v('bval',j,t),v('val',j,t),ops[j]
            add(o,-z,a); add(o,-z,b); add(o,z,-a,-b)
            add(-o,z,-a); add(-o,z,-b); add(-o,-z,a,b)
    for t in range(R): add(v('val',K-1,t) * (1 if t < m else -1))
    for a in range(n): add(*(xs[j][a] for xs in (A,B) for j in range(K)))
    if meta['ordered']:
        for j in range(K-1):
            for b in range(n+j):
                for c in range(b): add(-B[j][b],-B[j+1][c])
    for j in range(K-1):
        add(*(xs[k][n+j] for xs in (A,B) for k in range(j+1,K)))
    for j in range(K):
        for selectors, kind in ((A[j],'operand_a_pure'),(B[j],'operand_b_pure')):
            f = v(kind,j)
            for a,s in enumerate(selectors):
                if a < n: add(-s,f)
                else:
                    p = v('pure_or',a-n)
                    add(-s,-f,p); add(-s,f,-p)
        p,o,a,b = v('pure_or',j),ops[j],v('operand_a_pure',j),v('operand_b_pure',j)
        add(-p,o); add(-p,a); add(-p,b); add(p,-o,-a,-b)
        add(o,-a,-b,*(v('val',j,t) for t in range(m,R)))
    cnf = prefix.with_suffix('.cnf').read_bytes()
    assert hashlib.sha256(cnf).hexdigest() == meta['cnf_sha256']
    lines = cnf.decode().splitlines()
    assert lines[0] == f'p cnf {len(names)} {len(clauses)}'
    actual = [tuple(map(int,line.split()[:-1])) for line in lines[1:]]
    assert all(line.endswith(' 0') for line in lines[1:])
    assert len(actual) == meta['clauses'] == len(clauses)
    normalize = lambda cs: Counter(tuple(sorted(c)) for c in cs)
    assert normalize(actual) == normalize(clauses)
    log = prefix.with_suffix('.solver.log').read_text()
    statuses = re.findall(r'^s (.+)$',log,re.M)
    wrapper = prefix.with_suffix('.log').read_text()
    if statuses == ['SATISFIABLE']:
        assert re.search(r'^RESULT 10 ',wrapper,re.M)
        values = {abs(x): x > 0 for line in log.splitlines() if line.startswith('v ')
                  for x in map(int,line[2:].split()) if x}
        assert all(any(values[abs(x)] == (x>0) for x in c) for c in actual)
        gates = []
        for j in range(K):
            aa = [a for a,s in enumerate(A[j]) if values[s]]
            bb = [a for a,s in enumerate(B[j]) if values[s]]
            assert len(aa) == len(bb) == 1
            gates.append((int(values[ops[j]]),aa[0],bb[0]))
        witness = json.loads(prefix.with_suffix('.witness.json').read_text())
        assert witness['gates'] == [list(g) for g in gates]
        assert witness['n'] == n and witness['edges'] == edges and witness['failed'] == []
        cone = {K-1}
        for j in range(K-1,-1,-1):
            if j in cone: cone.update(x-n for x in gates[j][1:] if x>=n)
        assert cone == set(range(K))
        pure = [True]*n
        sources = []
        for j,(op,a,b) in enumerate(gates):
            assert 0 <= a < b < n+j
            if not op and pure[a] and pure[b]: sources.append(j)
            assert values[v('operand_a_pure',j)] == pure[a]
            assert values[v('operand_b_pure',j)] == pure[b]
            pure.append(bool(op) and pure[a] and pure[b])
            assert values[v('pure_or',j)] == pure[-1]
        assert sources == witness['source_ands'] and sources
        dirty = []
        for point in range(1<<n):
            wires = [bool(point>>a & 1) for a in range(n)]
            for op,a,b in gates: wires.append(wires[a] or wires[b] if op else wires[a] and wires[b])
            wanted = any((point>>a&1) and (point>>b&1) for a,b in edges)
            assert bool(wanted) == wires[-1]
            if not wanted:
                dirty.extend([j,point] for j,(op,a,b) in enumerate(gates) if not op and wires[n+j])
        assert dirty == witness['dirty']
        assert all(any(j == gate for gate,point in dirty) for j in sources)
        outcome = 'SAT full_truth_and_CNF_PASS'
    elif statuses == ['UNSATISFIABLE']:
        assert re.search(r'^RESULT 20 ',wrapper,re.M)
        outcome = 'UNSAT solver_report_only'
    else:
        assert statuses in ([],['UNKNOWN'])
        outcome = 'UNKNOWN no_proof_claim'
    print(prefix.name, 'CNF_PASS', outcome)
    return outcome.split()[0]

outcomes = Counter()
for path in sorted(base.glob('*-sources-dirty.json')):
    outcomes[validate(path.with_suffix(''))] += 1
print('OUTCOMES',dict(outcomes))

# Independent unlabelled-tree census: attach a leaf to every vertex of
# every previous-size tree, then canonicalize adjacency matrices using
# all degree-preserving vertex permutations. No Pruefer or rooted codes.
def canonical(n,edges):
    E = {tuple(sorted(e)) for e in edges}
    degrees = [sum(i in e for e in E) for i in range(n)]
    groups = [[i for i in range(n) if degrees[i] == d] for d in sorted(set(degrees))]
    best = None
    for parts in itertools.product(*(itertools.permutations(g) for g in groups)):
        order = tuple(itertools.chain.from_iterable(parts))
        code = tuple(int(tuple(sorted((order[a],order[b]))) in E)
                     for a in range(n) for b in range(a+1,n))
        if best is None or code < best: best = code
    return tuple(sorted(degrees)),best

trees = {canonical(1,[]): []}
counts = [1]
for n in range(2,8):
    following = {}
    for edges in trees.values():
        for attach in range(n-1):
            candidate = edges + [(attach,n-1)]
            following.setdefault(canonical(n,candidate),candidate)
    trees = following
    counts.append(len(trees))
assert counts == [1,1,1,2,3,6,11]
spec = json.loads((base/'source-tree7-specifications.json').read_text())
assert spec['tree_count'] == 11 and spec['prufer_sequences'] == 7**5
codes = set()
for record in spec['graphs']:
    n, edges = record['n'], record['edges']
    assert n == 7 and len(edges) == 6 and len({tuple(sorted(e)) for e in edges}) == 6
    seen = {0}
    while True:
        added = {v for a,b in edges for v in (a,b) if a in seen or b in seen}
        if added <= seen: break
        seen |= added
    assert seen == set(range(n))
    covers = [mask for mask in range(1<<n) if all((mask>>a&1) or (mask>>b&1) for a,b in edges)]
    assert record['cover_mask'] in covers
    assert record['tau'] == min(mask.bit_count() for mask in covers) == record['cover_mask'].bit_count()
    assert record['K'] == 6+record['tau']-1
    code = canonical(n,edges)
    assert code not in codes
    codes.add(code)
assert codes == set(trees)
print('TREE_CENSUS PASS independent_leaf_extension_counts',counts,'coverage=11/11')
print('REVIEW PASS; bounded computational evidence, not a Lean proof or universal conjecture proof')
