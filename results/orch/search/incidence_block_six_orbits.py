from itertools import combinations,permutations
from collections import defaultdict
from pathlib import Path
import json

D={0,1,3,9}
groups=defaultdict(list)
perms=list(permutations(range(6)))
maps=[{mask:sum(1<<perm[i] for i in range(6) if (mask>>i)&1) for mask in range(64)} for perm in perms]
for ls in combinations(range(13),6):
    raw=tuple(sorted(sum(1<<j for j,l in enumerate(ls) if (p-l)%13 in D) for p in range(13)))
    key=min(tuple(sorted(f[x] for x in raw)) for f in maps)
    groups[key].append(ls)
out=[]
for key,ls in sorted(groups.items()):
    representative=ls[0]
    row={'lines':representative,'orbit_size':len(ls),'nonisolated_points':sum(x!=0 for x in key),'degree_pattern':sorted(x.bit_count() for x in key if x),'signature':key}
    out.append(row)
    print(json.dumps(row),flush=True)
Path('/tmp/oec/pequalnp-pilot-131/plane3-six-line-orbits.json').write_text(json.dumps(out,indent=2))
