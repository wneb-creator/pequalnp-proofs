from itertools import permutations
from pathlib import Path
import json,time
start=time.monotonic();perms=list(permutations(range(4)));orbits={};valid=0
for mask in range(1<<16):
 if mask.bit_count()<8:continue
 rows=[mask>>(4*i)&15 for i in range(4)]
 if any((rows[i]&rows[j]).bit_count()>1 for i in range(4) for j in range(i)):continue
 valid+=1
 variants=[]
 for p in perms:
  r=sorted(sum(((x>>p[j])&1)<<j for j in range(4)) for x in rows)
  variants.append(sum(x<<(4*i) for i,x in enumerate(r)))
 canonical=min(variants)
 if canonical not in orbits:
  edges=[(i,4+j) for i in range(4) for j in range(4) if canonical>>(4*i+j)&1]
  orbits[canonical]={'mask':canonical,'edges':edges,'edge_count':len(edges),'labelled_count':0}
 orbits[canonical]['labelled_count']+=1
result={'labelled_valid_graphs':valid,'orbits_under_side_permutations':list(orbits.values()),'seconds':time.monotonic()-start}
Path(__file__).with_name('census-4by4.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
