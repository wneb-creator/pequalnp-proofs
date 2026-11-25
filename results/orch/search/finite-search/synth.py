import sys,json,time
import numpy as np
from scipy.optimize import milp,LinearConstraint,Bounds
from scipy.sparse import coo_matrix
n=int(sys.argv[1]); gates=int(sys.argv[2]); graph=sys.argv[3]; deadline=float(sys.argv[4])
if graph=='path': edges=[(0,1),(0,3),(2,1)]
elif graph=='double': edges=[(0,1),(0,2),(0,3),(1,4)]
elif graph=='cycle': edges=[(0,1),(0,5),(2,1),(2,3),(4,3),(4,5)]
else: raise ValueError(graph)
pos=[(1<<i)|(1<<j) for i,j in edges]
neg=[]
def fn(s): return any(s>>i&1 and s>>j&1 for i,j in edges)
for s in range(1<<n):
    if not fn(s) and all(fn(s|(1<<i)) for i in range(n) if not(s>>i&1)): neg.append(s)
rows=list(dict.fromkeys(pos+neg+[1,2])); c0=rows.index(1); c1=rows.index(2); ch=len(rows)+2
lo=[];hi=[];ints=[]
def var(lower=0,upper=1,integer=False):
    i=len(lo);lo.append(lower);hi.append(upper);ints.append(int(integer));return i
A=[];B=[];L=[];U=[]
def con(d,l=-np.inf,u=np.inf):
    A.append(d);L.append(l);U.append(u)
def eq(d,r): con(d,r,r)
wire=[]
for i in range(n):
    wire.append([var((s>>i)&1,(s>>i)&1) for s in rows]+[var(int(i==1),int(i==1)),var(int(i==0),int(i==0))])
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
for c,s in enumerate(rows):eq({wire[-1][c]:1},int(fn(s)))
for c in [len(rows),len(rows)+1]:eq({wire[-1][c]:1},0)
# Every intermediate gate must be used at least once, valid for minimal circuits.
for g in range(gates-1):
    con({choose[j][p][n+g]:1 for j in range(g+1,gates) for p in range(2)},l=1)
rr=[];cc=[];vv=[]
for r,d in enumerate(A):
    for c,v in d.items():
        if v:rr.append(r);cc.append(c);vv.append(v)
mat=coo_matrix((vv,(rr,cc)),shape=(len(A),len(lo))).tocsc()
print(json.dumps({'graph':graph,'n':n,'gates':gates,'truth_rows':rows,'vars':len(lo),'integer_vars':sum(ints),'constraints':len(A)}),flush=True)
res=milp(np.zeros(len(lo)),integrality=np.array(ints),bounds=Bounds(np.array(lo),np.array(hi)),constraints=LinearConstraint(mat,np.array(L),np.array(U)),options={'time_limit':deadline,'disp':True})
print(res,flush=True)
if res.x is not None:
    prog=[]
    for g in range(gates):
        a=[int(np.argmax(res.x[ss])) for ss in choose[g]]
        prog.append(('and' if res.x[ops[g]]>.5 else 'or',a))
    print('PROGRAM',json.dumps(prog),flush=True)
