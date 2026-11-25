"""All |E|+tau(E)=9 classes on3+4 inputs, with exact support/forest checks."""
from itertools import permutations
import json

p,l=3,4
pairs=[(a,p+b) for a in range(p) for b in range(l)]
perms=[(a,b) for a in permutations(range(p)) for b in permutations(range(l))]
def c4free(mask):
    return all(not all(mask>>(u*l+v)&1 for u in (a,aa) for v in (b,bb))
               for a in range(p) for aa in range(a+1,p)
               for b in range(l) for bb in range(b+1,l))
def cover(mask):
    return min(s.bit_count() for s in range(128)
               if all(not(mask>>e&1) or s>>a&1 or s>>b&1 for e,(a,b) in enumerate(pairs)))
def canonical(mask):
    return min(sum(1<<(aa[a]*l+bb[b]) for a in range(p) for b in range(l) if mask>>(a*l+b)&1)
               for aa,bb in perms)
def analyse(mask):
    es=[e for k,e in enumerate(pairs) if mask>>k&1]
    support=sorted(set(v for e in es for v in e))
    parent=list(range(7));cycle=False
    def find(a):
        while parent[a]!=a:a=parent[a]
        return a
    for a,b in es:
        aa,bb=find(a),find(b)
        if aa==bb:cycle=True
        parent[aa]=bb
    return dict(mask=mask,edges=es,edge_count=len(es),tau=cover(mask),support=support,
                active_inputs=len(support),forest=not cycle,
                components=len({find(i) for i in range(7)}))
classes={};labelled=0
for mask in range(4096):
    if not c4free(mask):continue
    if mask.bit_count()+cover(mask)!=9:continue
    labelled+=1;c=canonical(mask);classes[c]=classes.get(c,0)+1
records=[]
for c,count in sorted(classes.items()):
    record=analyse(c);record['labelled_count']=count;records.append(record)
active=[r for r in records if r['active_inputs']==7]
assert all(r['edge_count']==6 and r['tau']==3 and r['forest'] and r['components']==1 for r in active)
print(json.dumps(dict(all_masks=4096,target='|E|+tau(E)=9',labelled=labelled,
                     classes=len(records),genuinely_seven_active_classes=len(active),
                     genuinely_seven_active_labelled=sum(r['labelled_count'] for r in active),
                     records=records,scope='Finite exhaustive computation, not Lean verification.'),indent=2))
