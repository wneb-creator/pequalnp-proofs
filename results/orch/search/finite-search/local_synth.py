import sys,json,time
from pathlib import Path
import numpy as np
from scipy.optimize import milp,LinearConstraint,Bounds
from scipy.sparse import coo_matrix
selected=[int(x) for x in sys.argv[1].split(',')]; deadline=float(sys.argv[2]); extras=int(sys.argv[3]); graph='local_plane';outfile=sys.argv[4]
base=Path('/tmp/oec/pequalnp-pilot-65/finite-search')
prefix=[]
def gate(op,a,b):
    prefix.append((op,a,b));return 26+len(prefix)-1
roots=[];As={};partials={};cross={}
for line in [l for l in range(13) if l!=1 and l not in selected]+selected:
    xs=[(line+d)%13 for d in [0,1,3,9]]
    if extras>=3 and line not in selected:
        aa=[x for x in xs if x in [0,3,9]];bb=[x for x in xs if x in [2,4,10]]
        if aa and bb:xs=[aa[0],bb[0]]+[x for x in xs if x not in [aa[0],bb[0]]]
    if extras>=2 and line in selected:
        As[line]=xs;partials[line]=[];continue
    a=xs[0];inner=[]
    for b in xs[1:]:a=gate('or',a,b);inner.append(a)
    As[line]=a;partials[line]=inner[:-1]
    if extras>=3 and xs[0] in [0,3,9] and xs[1] in [2,4,10]:cross[(xs[0],xs[1])]=inner[0]
    if line not in selected:roots.append(gate('and',13+line,a))
f=roots[0]
for b in roots[1:]:f=gate('or',f,b)
preds=([f]+[13+l for l in selected]+[i for l in selected for i in As[l]]+[1,2,4,10,14]) if extras>=2 else ([f]+[As[l] for l in selected]+[13+l for l in selected]+[1,2,4,10,14])
if extras==1:preds+=[i for l in selected for i in partials[l]]
if extras==3:preds += [cross[p] for p in [(0,2),(3,4),(9,10)]]
if extras==4:preds += list(cross.values())
preds=list(dict.fromkeys(preds));n=len(preds);gates=(5 if extras>=2 else 2)*len(selected)+5
adj=[sum(1<<j for j in range(13) if (i-j)%13 in [0,1,3,9]) for i in range(13)]
pos=[(1<<i)|(1<<(13+j)) for i in range(13) for j in range(13) if adj[i]>>j&1]
neg=json.loads((base/'plane-maxind.json').read_text())
def evaluate(s):
    w=[int(s>>i&1) for i in range(26)]
    for op,a,b in prefix:w.append(w[a]|w[b] if op=='or' else w[a]&w[b])
    return w
def derivative(baseinput,variable):
    w=evaluate(baseinput);d=[int(i==variable) for i in range(26)]
    for op,a,b in prefix:d.append(d[a]|d[b] if op=='or' else(w[a]&d[b])|(d[a]&w[b]))
    return d
dx=derivative(1,13);dy=derivative(1<<13,0)
rows=[];targets=[];rowidx={}
for ass,target in [(1,0),(1<<13,0)]+[(s,1) for s in pos]+[(s,0) for s in neg]:
    w=evaluate(ass);key=tuple(w[i] for i in preds)
    if key in rowidx:assert targets[rowidx[key]]==target
    else:rowidx[key]=len(rows);rows.append(key);targets.append(target)
basekeys={tuple(evaluate(1)[i] for i in preds),tuple(evaluate(1<<13)[i] for i in preds)}
def subset(a,b):return all(x<=y for x,y in zip(a,b))
keep=[]
for j,r in enumerate(rows):
    if r in basekeys or not any(j!=k and targets[j]==targets[k] and (subset(q,r) if targets[j] else subset(r,q)) for k,q in enumerate(rows)):
        keep.append(j)
rows=[rows[i] for i in keep];targets=[targets[i] for i in keep];rowidx={r:i for i,r in enumerate(rows)}
c0=rowidx[tuple(evaluate(1)[i] for i in preds)];c1=rowidx[tuple(evaluate(1<<13)[i] for i in preds)];ch=len(rows)+2
print('PREFIX',json.dumps({'gates':len(prefix),'window_budget':gates,'c0':c0,'c1':c1,'rows':len(rows)}),flush=True)
Path(outfile+'.profile.json').write_text(json.dumps({'preds':preds,'values':rows,'targets':targets,'dx':[dx[i] for i in preds],'dy':[dy[i] for i in preds],'base_channels':[c0,c1],'window_budget':gates,'prefix':prefix},indent=2)+'\n')
if deadline < 0: sys.exit(0)
lo=[];hi=[];ints=[]
def var(lower=0,upper=1,integer=False):
    i=len(lo);lo.append(lower);hi.append(upper);ints.append(int(integer));return i
A=[];B=[];L=[];U=[]
def con(d,l=-np.inf,u=np.inf):
    A.append(d);L.append(l);U.append(u)
def eq(d,r): con(d,r,r)
wire=[]
for i in range(n):
    wire.append([var(bits[i],bits[i]) for bits in rows]+[var(dx[preds[i]],dx[preds[i]]),var(dy[preds[i]],dy[preds[i]])])
choose=[];ops=[]
for g in range(gates):
    z=var(integer=True); ops.append(z)
    sel=[[var(integer=True) for i in range(n+g)] for p in range(2)]
    choose.append(sel)
    for ss in sel:eq({i:1 for i in ss},1)
    con({**{j:i for i,j in enumerate(sel[0])},**{j:-i for i,j in enumerate(sel[1])}},u=-1)
    taps=[[var() for _ in range(ch)] for _ in range(2)]
    for p in range(2):
        for i,ss in enumerate(sel[p]):
            for c in range(ch):
                con({taps[p][c]:1,wire[i][c]:-1,ss:1},u=1)
                con({taps[p][c]:-1,wire[i][c]:1,ss:1},u=1)
    out=[var() for _ in range(ch)]
    wire.append(out)
    for c in range(len(rows)):
        a,b,y=taps[0][c],taps[1][c],out[c]
        con({y:1,a:-1,z:1},u=1);con({y:1,b:-1,z:1},u=1)
        con({y:1,a:-1,b:-1,z:-1},l=-2)
        con({y:1,a:-1,z:1},l=0);con({y:1,b:-1,z:1},l=0)
        con({y:1,a:-1,b:-1,z:-1},u=0)
    def conj(a,b):
        p=var();con({p:1,a:-1},u=0);con({p:1,b:-1},u=0);con({p:1,a:-1,b:-1},l=-1);return p
    for dc,bc in [(len(rows),c0),(len(rows)+1,c1)]:
        a,b=taps[0][dc],taps[1][dc];y=out[dc]
        p=conj(taps[0][bc],b);q=conj(a,taps[1][bc])
        # z=1 gives OR(p,q); z=0 gives OR(a,b)
        con({y:1,p:-1,z:-1},l=-1);con({y:1,q:-1,z:-1},l=-1)
        con({y:1,p:-1,q:-1,z:1},u=1)
        con({y:1,a:-1,z:1},l=0);con({y:1,b:-1,z:1},l=0)
        con({y:1,a:-1,b:-1,z:-1},u=0)
for c,s in enumerate(rows):eq({wire[-1][c]:1},targets[c])
for c in [len(rows),len(rows)+1]:eq({wire[-1][c]:1},0)
# Every intermediate gate must be used at least once, valid for minimal circuits.
for g in range(gates-1):
    con({choose[j][p][n+g]:1 for j in range(g+1,gates) for p in range(2)},l=1)
rr=[];cc=[];vv=[]
for r,d in enumerate(A):
    for c,v in d.items():
        if v:rr.append(r);cc.append(c);vv.append(v)
mat=coo_matrix((vv,(rr,cc)),shape=(len(A),len(lo))).tocsc()
print(json.dumps({'graph':graph,'n':n,'gates':gates,'truth_rows':len(rows),'selected_lines':selected,'preds':preds,'vars':len(lo),'integer_vars':sum(ints),'constraints':len(A)}),flush=True)
res=milp(np.zeros(len(lo)),integrality=np.array(ints),bounds=Bounds(np.array(lo),np.array(hi)),constraints=LinearConstraint(mat,np.array(L),np.array(U)),options={'time_limit':deadline,'disp':True})
print(res,flush=True)
if res.x is not None:
    prog=[]
    for g in range(gates):
        a=[int(np.argmax(res.x[ss])) for ss in choose[g]]
        prog.append(('and' if res.x[ops[g]]>.5 else 'or',a))
    print('PROGRAM',json.dumps(prog),flush=True)
    Path(outfile).write_text(json.dumps({'prefix':prefix,'preds':preds,'window':prog,'selected':selected},indent=2)+'\n')
