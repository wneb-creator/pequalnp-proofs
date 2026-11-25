import json
from pathlib import Path
import sys
vertices=[int(v) for v in sys.argv[1].split(',')]
lines=[sum(1<<((l+d)%13) for d in(0,1,3,9)) for l in range(13)]
pencils=[sum(1<<l for l in range(13) if lines[l]>>p&1) for p in range(13)]
negative=[]
for points in range(8192):
    dual=sum(1<<l for l in range(13) if lines[l]&points==0)
    closure=8191
    for l in range(13):
        if dual>>l&1:closure&=8191^lines[l]
    if points==closure and not any(points&~l==0 for l in lines) and not any(dual&~p==0 for p in pencils):
        assignment=points|(dual<<13)
        negative.append(sum((assignment>>v&1)<<i for i,v in enumerate(vertices)))
negative=set(negative)
negative=sorted(v for v in negative if not any(v!=w and v&~w==0 for w in negative))
positive=[(1<<i)|(1<<j) for i in range(len(vertices)) for j in range(i+1,len(vertices))
    if (vertices[i]<13<=vertices[j] and lines[vertices[j]-13]>>vertices[i]&1) or
       (vertices[j]<13<=vertices[i] and lines[vertices[i]-13]>>vertices[j]&1)]
data={'vertices':vertices,'positive_edges':positive,'maximal_negative_masks':negative}
path=Path('/tmp/oec/pequalnp-pilot-62')/sys.argv[2]
path.write_text(json.dumps(data,indent=2)+'\n')
print(path,len(positive),len(negative))
