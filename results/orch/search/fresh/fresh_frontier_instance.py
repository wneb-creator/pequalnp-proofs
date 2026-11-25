import argparse, json
from itertools import permutations
from pathlib import Path
from fresh_gadget_frontier import inputs

def write_instance(r,path):
    k=r['k']
    groups=[tuple(g) for g in r['groups']]
    n,edge,pos,neg=inputs(k,False,False,groups)
    obs=pos+neg
    masks=[(sum(1<<j for j,m in enumerate(pos) if m>>i&1),sum(1<<j for j,m in enumerate(neg) if not m>>i&1)) for i in range(n)]
    ids=sorted(range(n),key=lambda i:masks[i])
    syms=[]
    for per in permutations(range(k)):
        gs=[tuple(sorted(per[j] for j in g)) for g in groups]
        if set(gs)!=set(groups):continue
        pn=list(per)+[k+groups.index(g) for g in gs]
        syms.append([ids.index(pn[i]) for i in ids])
    row=[[n,len(pos),len(neg),r['canonical'],len(syms)]]
    row.extend([masks[i] for i in ids]);row.extend(syms)
    path.write_text(''.join(' '.join(map(str,x))+'\n' for x in row))
    return ids,pos,neg
if __name__=='__main__':
    cat=json.loads(Path('fresh-module-catalog.json').read_text())
    for r in cat: write_instance(r,Path('fresh-module-'+r['id']+'.txt'))
