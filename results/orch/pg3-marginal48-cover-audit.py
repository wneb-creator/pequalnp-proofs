import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
data = json.loads((ROOT/'pg3-marginal48-cover-audit-data.json').read_text())
report = data['report']
flags = data['positive_samples']
inc = lambda p,l: (p-l) % 13 in {0,1,3,9}
expected = {(1<<p)|(1<<(13+l)) for p in range(13) for l in range(13) if inc(p,l)}
assert len(flags)==52 and len(set(flags))==52 and set(flags)==expected
negatives = [report[key]['input_mask'] for key in
             ['first_bad_triple_extension_obstruction','first_bad_row_extension_obstruction']]
for v in negatives:
    P=[p for p in range(13) if v>>p&1]
    L=[l for l in range(13) if v>>(13+l)&1]
    assert not any(inc(p,l) for p in P for l in L)
    print(json.dumps({'negative_input':v,'points':P,'lines':L}))
P=[p for p in range(13) if negatives[1]>>p&1]
L=[l for l in range(13) if negatives[1]>>(13+l)&1]
assert L==[l for l in range(13) if not any(inc(p,l) for p in P)]
assert P==[p for p in range(13) if not any(inc(p,l) for l in L)]
assert not any(all(inc(p,l) for p in P) for l in range(13))
assert not any(all(inc(p,l) for l in L) for p in range(13))

pt=report['affine_point_labels']
ln=report['affine_line_labels']
qq=report['infinity_point_labels']
vv=report['vertical_line_labels']
zz=report['infinity_line_label']
assert len(set(sum(pt,[])+qq))==13
assert len(set(sum(ln,[])+vv+[zz]))==13
for x in range(3):
    for y in range(3):
        for s in range(3):
            for t in range(3):
                assert inc(pt[x][y],ln[s][t]) == (y==(s*x+t)%3)
        assert all(inc(pt[x][y],vv[a])==(x==a) for a in range(3))
        assert not inc(pt[x][y],zz)
for s in range(3):
    for u in range(3):
        for t in range(3):
            assert inc(qq[s],ln[u][t])==(s==u)
    assert not any(inc(qq[s],v) for v in vv)
    assert inc(qq[s],zz)
assert all(inc(qq[3],v) for v in vv) and inc(qq[3],zz)
assert not any(inc(qq[3],l) for row in ln for l in row)

samples=flags+negatives
values=[sum(1<<j for j,v in enumerate(samples) if v>>i&1) for i in range(26)]
ops=[]
def gate(op,a,b):
    assert 0<=a<len(values) and 0<=b<len(values)
    values.append(values[a]|values[b] if op=='or' else values[a]&values[b])
    ops.append(op)
    return len(values)-1

def OR(wires):
    answer=wires[0]
    for wire in wires[1:]: answer=gate('or',answer,wire)
    return answer

def AND(a,b): return gate('and',a,b)
A=[OR(row) for row in pt]
B=[OR([pt[x][y] for x in range(3)]) for y in range(3)]
S=[OR([13+l for l in row]) for row in ln]
T=[OR([13+ln[s][t] for s in range(3)]) for t in range(3)]
W=[gate('or',A[0],S[0]),
   OR([AND(A[1],S[1]),AND(A[2],S[2])]),
   OR([AND(A[1],S[2]),AND(A[2],S[1])])]
E=[OR([AND(B[(r+t)%3],T[t]) for t in range(3)]) for r in range(3)]
affine=OR([AND(W[r],E[r]) for r in range(3)])
vertical=OR([AND(A[x],13+vv[x]) for x in range(3)])
slopes=OR([AND(qq[s],S[s]) for s in range(3)])
v_inf=AND(qq[3],OR([13+v for v in vv]))
line_inf=AND(13+zz,OR([qq[3]]+qq[:3]))
out=OR([affine,vertical,slopes,v_inf,line_inf])
assert ops.count('or')==48 and ops.count('and')==24
assert values[out]==(1<<54)-1
full=(1<<52)-1
for j,key in enumerate(['first_bad_triple_extension_obstruction','first_bad_row_extension_obstruction']):
    supports={v&full for v in values if not (v>>(52+j)&1)}-{0}
    maximal=sorted(s for s in supports if not any(s!=t and s&t==s for t in supports))
    assert maximal==report[key]['maximal_support_masks']
    assert all(any(s&t==s for t in maximal) for s in supports)
    unions=[0]*(1<<len(maximal))
    maxima=[0]*(len(maximal)+1)
    best=len(maximal)+1
    witness=None
    for mask in range(1,1<<len(maximal)):
        bit=mask&-mask
        i=bit.bit_length()-1
        unions[mask]=unions[mask^bit]|maximal[i]
        k=mask.bit_count()
        maxima[k]=max(maxima[k],unions[mask].bit_count())
        if unions[mask]==full and k<best:
            best=k
            witness=[i for i in range(len(maximal)) if mask>>i&1]
    assert best==report[key]['minimum_false_wire_cover']
    assert all(maxima[int(k)]==v for k,v in report[key]['maximum_flags_covered_by_k_false_wires'].items())
    witness_mask=0
    for m in report[key]['minimum_cover_witness']: witness_mask |= m
    assert witness_mask==full and len(report[key]['minimum_cover_witness'])==best
    print(json.dumps({'audit':key,'available_old_wires':len(values),'distinct_nonempty_false_supports':len(supports),
                      'maximal_false_supports':len(maximal),'enumerated_subsets':len(unions),
                      'maximum_coverage_by_cardinality':maxima,'minimum_cover':best,
                      'independent_minimum_cover_indices':witness,'minimum_append_OR_for_this_negative':best-1},sort_keys=True))
