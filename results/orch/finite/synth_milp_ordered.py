import sys,time,json
import numpy as np
from scipy.optimize import milp,Bounds,LinearConstraint
from scipy.sparse import coo_array
from pathlib import Path

path=Path(sys.argv[1]);K=int(sys.argv[2]);limit=float(sys.argv[3]);force='seed' in sys.argv[4:]
data=list(map(int,path.read_text().split()));n,m=data[:2];edges=list(zip(data[2::2],data[3::2]))
ind=[s for s in range(1<<n) if not any((s>>a&1) and (s>>b&1) for a,b in edges)]
maxi=[s for s in ind if not any((s|1<<i) in ind for i in range(n) if not(s>>i&1))]
rows=[(1<<a)|(1<<b) for a,b in edges]+maxi;R=len(rows);target=[1]*m+[0]*len(maxi)
variables=[]
def var(name):
    variables.append(name)
    return len(variables)-1
ops=[var(('op',j)) for j in range(K)]
vals=[[var(('val',j,t)) for t in range(R)] for j in range(K)]
av=[[var(('aval',j,t)) for t in range(R)] for j in range(K)]
bv=[[var(('bval',j,t)) for t in range(R)] for j in range(K)]
asel=[[var(('asel',j,i)) for i in range(n+j)] for j in range(K)]
bsel=[[var(('bsel',j,i)) for i in range(n+j)] for j in range(K)]
ri=[];ci=[];vv=[];low=[];high=[]
def con(terms,lo=-np.inf,hi=np.inf):
    row=len(low);low.append(lo);high.append(hi)
    for c,v in terms.items():
        if v:ri.append(row);ci.append(c);vv.append(v)
def fix(v,x):con({v:1},x,x)
for j in range(K):
    con(dict.fromkeys(asel[j],1),1,1);con(dict.fromkeys(bsel[j],1),1,1)
    con({**{v:i for i,v in enumerate(asel[j])},**{v:-i for i,v in enumerate(bsel[j])}},hi=-1)
    for selected,signals in [(asel[j],av[j]),(bsel[j],bv[j])]:
        for i,s in enumerate(selected):
            for t,point in enumerate(rows):
                v=signals[t]
                if i<n:
                    if point>>i&1:con({v:1,s:-1},lo=0)
                    else:con({v:1,s:1},hi=1)
                else:
                    other=vals[i-n][t]
                    con({v:1,other:-1,s:1},hi=1)
                    con({v:-1,other:1,s:1},hi=1)
    for t in range(R):
        z,a,b,o=vals[j][t],av[j][t],bv[j][t],ops[j]
        con({z:1,a:-1,o:-1},hi=0)
        con({z:1,b:-1,o:-1},hi=0)
        con({z:1,a:-1,b:-1,o:1},lo=-1)
        con({z:1,a:-1,o:-1},lo=-1)
        con({z:1,b:-1,o:-1},lo=-1)
        con({z:1,a:-1,b:-1,o:1},hi=1)
# Breadth-first topological order permits sorting gates lexicographically by
# larger input index, smaller input index, and operation within each depth.
for j in range(K-1):
    terms={ops[j]:1,ops[j+1]:-1}
    for sign,k in [(1,j),(-1,j+1)]:
        terms.update({v:sign*2*i for i,v in enumerate(asel[k])})
        terms.update({v:sign*2*(n+K)*i for i,v in enumerate(bsel[k])})
    con(terms,hi=0)
for t,want in enumerate(target):fix(vals[-1][t],want)
for i in range(n):con({s[i]:1 for side in [asel,bsel] for s in side},lo=1)
if force:
    alpha=max(s.bit_count() for s in ind);cover=((1<<n)-1)^next(s for s in ind if s.bit_count()==alpha)
    groups=[[] for _ in range(n)]
    for a,b in edges:
        if cover>>a&1:groups[a].append(b)
        else:groups[b].append(a)
    gates=[];outs=[]
    def add(op,a,b):
        a,b=sorted([a,b]);gates.append((op,a,b));return n+len(gates)-1
    for a,others in enumerate(groups):
        if not others:continue
        u=others[0]
        for b in others[1:]:u=add(1,u,b)
        outs.append(add(0,a,u))
    u=outs[0]
    for b in outs[1:]:u=add(1,u,b)
    assert len(gates)==K
    depths=[0]*n
    for op,a,b in gates:depths.append(1+max(depths[a],depths[b]))
    mapping={i:i for i in range(n)};ordered=[]
    for depth in range(1,max(depths)+1):
        candidates=[]
        for j,(op,a,b) in enumerate(gates):
            if depths[n+j]!=depth:continue
            a,b=sorted([mapping[a],mapping[b]])
            candidates.append((b,a,op,j))
        for b,a,op,j in sorted(candidates):
            mapping[n+j]=n+len(ordered);ordered.append((op,a,b))
    gates=ordered
    for j,(op,a,b) in enumerate(gates):fix(ops[j],op);fix(asel[j][a],1);fix(bsel[j][b],1)
A=coo_array((np.array(vv,float),(np.array(ri,dtype=np.int32),np.array(ci,dtype=np.int32))),shape=(len(low),len(variables))).tocsc()
print(json.dumps({'graph':path.name,'n':n,'edges':edges,'K':K,'rows':rows,'variables':len(variables),'constraints':len(low),'force_seed':force}),flush=True)
started=time.monotonic()
res=milp(np.zeros(len(variables)),integrality=np.ones(len(variables)),bounds=Bounds(0,1),constraints=LinearConstraint(A,np.array(low),np.array(high)),options={'time_limit':limit,'mip_rel_gap':0,'disp':True,'threads':1,'parallel':False})
print('RESULT',res.status,res.message,'SECONDS',time.monotonic()-started,flush=True)
if res.x is not None:
    gates=[]
    for j in range(K):
        op=round(res.x[ops[j]]);a=max(range(n+j),key=lambda i:res.x[asel[j][i]]);b=max(range(n+j),key=lambda i:res.x[bsel[j][i]])
        gates.append((op,a,b));print(j,'or' if op else 'and',a,b,flush=True)
    failed=[]
    for point in range(1<<n):
        v=[point>>i&1 for i in range(n)]
        for op,a,b in gates:v.append((v[a]|v[b]) if op else (v[a]&v[b]))
        want=int(any((point>>a&1) and (point>>b&1) for a,b in edges))
        if v[-1]!=want:failed.append(point)
    print('FULL_TRUTH_FAILED',failed,flush=True)
