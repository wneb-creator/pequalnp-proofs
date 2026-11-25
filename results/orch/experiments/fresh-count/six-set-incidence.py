import itertools
import json
from pathlib import Path
D={0,1,3,9}
lines=[sum(1<<p for p in range(13) if (p-l)%13 in D) for l in range(13)]
minimum=52
examples=[]
count=0
for points in itertools.combinations(range(13),6):
    mask=sum(1<<p for p in points)
    counts=[(mask&line).bit_count() for line in lines]
    assert sum(counts)==24
    assert sum(k*(k-1) for k in counts)==30
    chosen=sorted(range(13),key=lambda l:counts[l])[:6]
    lower=sum(counts[l] for l in chosen)
    if lower<minimum:
        minimum=lower
        examples=[{'points':points,'lines':chosen,'incidences':lower,'column_counts':counts}]
    count+=1
answer={'status':'computational geometry illustration, not Lean checked','point_sets':count,'minimum_incidence_between_six_points_and_six_lines':minimum,'example':examples[0],'analytic_argument':'For six points, line-intersection counts sum to24 and k*(k-1) sums to30. For every natural k, k*(k-1)+6>=4*k. If six lines had atmost5 incidences, the otherseven would have atleast19 and hence pair-sum atleast34, contradiction.'}
Path('/tmp/oec/pequalnp-pilot-73/fresh-count/six-set-incidence.json').write_text(json.dumps(answer,indent=2)+'\n')
print(json.dumps(answer,indent=2))
