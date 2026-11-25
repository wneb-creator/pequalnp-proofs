import argparse,json
from pathlib import Path
from fresh_gadget_frontier import inputs

def check(r, path, fmt):
    k=r['k'];groups=[tuple(g) for g in r['groups']]
    n,edges,pos,neg=inputs(k,False,False,groups)
    tests=pos+neg; p=len(pos)
    a=[sum(1<<j for j,v in enumerate(tests) if v>>i&1) for i in range(n)]
    if fmt=='cpp':
        am=[(v&((1<<p)-1),((1<<len(neg))-1)^(v>>p)) for v in a]
        path=[(g[0],(g[1],g[2]),(g[3],g[4]),(g[5],g[6])) for g in path]
    else:am=a
    nobs=1<<n;full=(1<<nobs)-1
    vals=[]
    for i in range(n):
        step=1<<i
        base=((1<<step)-1)<<step
        vals.append(base*(full//((1<<(2*step))-1)))
    goal=0
    for i,j in edges:goal|=vals[i]&vals[j]
    inds={m:i for i,m in enumerate(am)};gates=[]
    for op,lh,rh,h in path:
        u,v=inds[lh],inds[rh]
        val=vals[u]&vals[v] if op=='&' else vals[u]|vals[v]
        vals.append(val);gates.append([op,u,v]);idx=len(vals)-1
        af=sum(1<<j for j,t in enumerate(tests) if val>>t&1)
        actual=(af&((1<<p)-1), ((1<<len(neg))-1)^(af>>p)) if fmt=='cpp' else af
        assert actual==h
        inds[h]=idx
    assert vals[-1]==goal
    return dict(module=r['id'],input_count=n,gates=len(gates),truth_assignments=nobs,full_truth_table_matches=True,circuit=gates)
if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('--module',required=True);ap.add_argument('--path',required=True);ap.add_argument('--fmt',choices=['cpp','py'],default='cpp')
    args=ap.parse_args()
    r=next(r for r in json.loads(Path('fresh-module-catalog.json').read_text()) if r['id']==args.module)
    data=json.loads(Path(args.path).read_text())
    assert data['status']=='SAT'
    print(json.dumps(check(r,data['path'],args.fmt)))
