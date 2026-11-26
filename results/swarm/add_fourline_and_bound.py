import itertools
import json
import hashlib
from pathlib import Path

root = Path(__file__).resolve().parent
prefix = root / 'q3fourline18-all'
meta = json.loads(prefix.with_suffix('.json').read_text())
assert meta['n'] == 14 and meta['gates'] == 18 and meta['at_most']
assert meta['line_ids'] == [0, 1, 4, 8] and len(meta['edges']) == 16
edges = [tuple(e) for e in meta['edges']]
def target(x):
    return any((x >> a) & 1 and (x >> b) & 1 for a, b in edges)
false_rows = [x for x, label in zip(meta['rows'], meta['labels']) if not label]
assert len(false_rows) == len(set(false_rows)) == 16
for x in false_rows:
    assert not target(x)
    assert all(target(x | (1 << i)) for i in range(14) if not (x >> i) & 1)
assert all(target(x | y) for x, y in itertools.combinations(false_rows, 2))
neighbors = [set() for _ in range(14)]
for a,b in edges:
    neighbors[a].add(b); neighbors[b].add(a)
assert all(len(neighbors[a] & neighbors[b]) <= 1 for a,b in itertools.combinations(range(14),2))
matching = [(a, next(iter(neighbors[a]))) for a in range(10) if len(neighbors[a]) == 1]
assert len(matching) == 4 and len({v for e in matching for v in e}) == 8
source = prefix.with_suffix('.cnf').read_text().splitlines()
assert source[0].startswith('p cnf ')
_,_,nv,nc = source[0].split(); nv,nc = int(nv),int(nc)
assert len(source) == nc + 1
names = {tuple(k):v for k,v in meta['names']}
new_clauses = []
ands = []
for j in range(18):
    value = nv + j + 1
    active, op = names[('active',j)], names[('op',j)]
    # value iff active and not op; op=false denotes AND.
    clauses = [[-value,active],[-value,-op],[value,-active,op]]
    new_clauses.extend(clauses); ands.append(value)
    for a,o,v in itertools.product([False,True],repeat=3):
        assignment={active:a,op:o,value:v}
        holds=all(any(assignment[abs(lit)] == (lit>0) for lit in c) for c in clauses)
        assert holds == (v == (a and not o))
    meta['names'].append([['derived_active_and',j],value])
# At least five true: every fourteen-element subset contains a true value.
subsets = list(itertools.combinations(ands,14))
assert len(subsets) == 3060 and len(set(subsets)) == 3060
assert all(len(set(s)) == 14 for s in subsets)
new_clauses.extend(map(list,subsets))
# Exhaustively validate the same symmetric cardinality scheme on all sizes<=9.
for n in range(1,10):
    for k in range(1,n+1):
        cs=list(itertools.combinations(range(n),n-k+1))
        for mask in range(1<<n):
            assert all(any(mask>>i&1 for i in c) for c in cs) == (mask.bit_count()>=k)
out=root/'q3fourline18-and5'
cnf='p cnf %d %d\n'%(nv+18,nc+len(new_clauses))+'\n'.join(source[1:])+'\n'+''.join(' '.join(map(str,c))+' 0\n' for c in new_clauses)
out.with_suffix('.cnf').write_text(cnf)
meta['derived_active_and_lower_bound']=5
meta['derived_bound_scope']='exact four-line function with at most 18 gates; saturation plus all-clean No4 edge-cover lower bound'
out.with_suffix('.json').write_text(json.dumps(meta))
audit={'false_rows':16,'join_pairs_checked':120,'maximality_checked':True,'no_four_cycle':True,'disjoint_matching':matching,'active_and_equivalences_checked':18*8,'cardinality_subsets':3060,'new_clauses':len(new_clauses),'variables':nv+18,'clauses':nc+len(new_clauses),'cnf_sha256':hashlib.sha256(cnf.encode()).hexdigest(),'original_cnf_sha256':hashlib.sha256(prefix.with_suffix('.cnf').read_bytes()).hexdigest()}
(root/'fourline-and5-audit.json').write_text(json.dumps(audit,indent=2)+'\n')
print(json.dumps(audit,indent=2))
