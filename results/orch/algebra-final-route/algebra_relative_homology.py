from pathlib import Path
import json
import time

base=Path('/tmp/oec/pequalnp-pilot-62')
data=json.loads((base/'geometry-data.json').read_text())
def generated_faces(rows):
    out=set()
    for row in rows:
        mask=row['S']|(row['D']<<13)
        sub=mask
        while True:
            out.add(sub)
            if not sub:break
            sub=(sub-1)&mask
    return out
large=generated_faces(data['maximal'])
small=generated_faces(data['generic'])
assert small<=large
relative=large-small
levels=[sorted(x for x in relative if x.bit_count()==k) for k in range(14)]
started=time.monotonic();ranks={0:0,13:0};finished=True
for cardinality in range(2,14):
    lower_index={mask:i for i,mask in enumerate(levels[cardinality-1])}
    pivots={}
    for column,mask in enumerate(levels[cardinality]):
        boundary=0;rest=mask
        while rest:
            bit=rest&-rest;rest-=bit
            face=mask^bit
            if face in lower_index:boundary^=1<<lower_index[face]
            else:assert face in small
        while boundary:
            pivot=boundary.bit_length()-1
            if pivot not in pivots:pivots[pivot]=boundary;break
            boundary^=pivots[pivot]
        if column%100==0 and time.monotonic()-started>10:finished=False;break
    if not finished:break
    ranks[cardinality-1]=len(pivots)
    print('relative_boundary_dimension',cardinality-1,'columns',len(levels[cardinality]),'rank_F2',len(pivots),flush=True)
betti={}
if finished:
    for dimension in range(13):
        betti[dimension]=len(levels[dimension+1])-ranks[dimension]-ranks[dimension+1]
result={'relative_face_counts_by_cardinality':[len(x) for x in levels],
        'relative_boundary_ranks_F2':ranks,'relative_betti_numbers_F2':betti,
        'total_relative_betti':sum(betti.values()),'exhaustive':finished,
        'elapsed_seconds':time.monotonic()-started,
        'scope':'Finite relative homology control; no circuit-complexity implication established and no Lean proof.'}
print(json.dumps(result,indent=2))
(base/'algebra-relative-complex-homology.json').write_text(json.dumps(result,indent=2)+'\n')
