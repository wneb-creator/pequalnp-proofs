from pathlib import Path
import gzip,hashlib,itertools,json

root=Path(__file__).resolve().parent
manifest=json.loads((root/'manifest.json').read_text())
for r in manifest['files']:
    if not r['retained']:continue
    raw=(root/r['file']).read_bytes()
    assert len(raw)==r['bytes'] and hashlib.sha256(raw).hexdigest()==r['sha256']
    if r.get('encoding')=='gzip':
        raw=gzip.decompress(raw)
        assert len(raw)==r['original_bytes'] and hashlib.sha256(raw).hexdigest()==r['original_sha256']
edges={(0,4),(0,5),(0,6),(0,7),(1,4),(2,4),(3,4)}
pos=manifest['boundary_basis']['positive_masks'];neg=manifest['boundary_basis']['negative_masks']
def target(mask):return any(mask>>a&1 and mask>>b&1 for a,b in edges)
for mask in range(256):
    assert target(mask)==any(mask&p==p for p in pos)
    assert (not target(mask))==any(mask&n==mask for n in neg)
group=[]
for left in itertools.permutations([1,2,3]):
    for right in itertools.permutations([5,6,7]):
        for swap in [False,True]:
            perm=[0,*left,4,*right]
            if swap:perm=[(x+4)%8 for x in perm]
            assert {tuple(sorted((perm[a],perm[b]))) for a,b in edges}==edges
            assert {perm[0],perm[4]}=={0,4}
            group.append(perm)
reps={min(tuple(sorted((p[a],p[b]))) for p in group) for a,b in itertools.combinations(range(8),2)}
assert len(group)==72 and len(reps)==5
count_runs=manifest['complete_and_count_coverage'];assert {r['and_count'] for r in count_runs}==set(range(10))
number=0
for r in count_runs:
    if 'cases' in r:
        cases=r['cases'];assert {tuple(c['result']['first_gate']) for c in cases}=={(op,a,b) for op in [0,1] for a,b in reps}
    else:cases=[r]
    for c in cases:
        assert c['result']['solver_code']==20
        output=gzip.decompress((root/c['solver_stdout']).read_bytes()).decode()
        assert '\ns UNSATISFIABLE\n' in output
        assert not c['result'].get('all_gates_used',False)
        assert not c['result'].get('ordered_larger_operands',False)
        number+=1
assert number==37
witness=json.loads((root/'double-star-10-defect-basis-control.witness.json').read_text())
gates=witness['gates_list'];assert len(gates)==10
assert all(op in [0,1] and 0<=a<b<8+j for j,(op,a,b) in enumerate(gates))
def eval_w(mask):
    v=[bool(mask>>i&1) for i in range(8)]
    for op,a,b in gates:v.append(v[a] and v[b] if op else v[a] or v[b])
    return v
assert all(eval_w(mask)[-1]==target(mask) for mask in range(256))
for base,seed in [(0,4),(4,0)]:
    v=eval_w(1<<base);d=[i==seed for i in range(8)]
    for op,a,b in gates:d.append((v[a] and d[b]) or (d[a] and v[b]) if op else d[a] or d[b])
    assert not d[-1]
print('PASS: archive hashes, exact boundary basis, 72 automorphisms, 37 UNSAT logs, ten-gate witness')
