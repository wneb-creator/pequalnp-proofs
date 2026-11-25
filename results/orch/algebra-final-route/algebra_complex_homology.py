from collections import Counter
import json
from pathlib import Path
import time

base=Path('/tmp/oec/pequalnp-pilot-62')
data=json.loads((base/'geometry-data.json').read_text())
faces=set()
for row in data['generic']:
    mask=row['S']|(row['D']<<13)
    sub=mask
    while True:
        faces.add(sub)
        if not sub:break
        sub=(sub-1)&mask
levels=[sorted(x for x in faces if x.bit_count()==k) for k in range(8)]
started=time.monotonic();ranks={};finished=True
for cardinality in range(2,8):
    lower_index={mask:i for i,mask in enumerate(levels[cardinality-1])}
    pivots={}
    for column,mask in enumerate(levels[cardinality]):
        boundary=0
        rest=mask
        while rest:
            bit=rest&-rest;rest-=bit
            boundary^=1<<lower_index[mask^bit]
        while boundary:
            pivot=boundary.bit_length()-1
            if pivot not in pivots:
                pivots[pivot]=boundary
                break
            boundary^=pivots[pivot]
        if column%100==0 and time.monotonic()-started>10:
            finished=False
            break
    if not finished:break
    ranks[cardinality-1]=len(pivots)
    print('boundary_dimension',cardinality-1,'columns',len(levels[cardinality]),'rank_F2',len(pivots),flush=True)
betti={}
if finished:
    ranks[0]=0;ranks[7]=0
    for dimension in range(7):
        betti[dimension]=len(levels[dimension+1])-ranks[dimension]-ranks[dimension+1]
result={
    'complex':'All subsets of the468generic negative rows.',
    'face_count':len(faces),'face_counts_by_cardinality':[len(x) for x in levels],
    'reduced_euler_characteristic':-sum((-1)**k*len(xs) for k,xs in enumerate(levels)),
    'boundary_ranks_F2':ranks,'betti_numbers_F2':betti,'exhaustive':finished,
    'elapsed_seconds':time.monotonic()-started,
    'scope':'Finite homology control only; no Lean certificate and no circuit lower-bound implication established.',
}
print(json.dumps(result,indent=2))
(base/'algebra-allowed-complex-homology.json').write_text(json.dumps(result,indent=2)+'\n')
