import json,sys,itertools
from pathlib import Path
n=int(sys.argv[1]);k=int(sys.argv[2]);output=Path(sys.argv[3]);mode=sys.argv[4] if len(sys.argv)>4 else 'ustar';edges=[tuple(sorted((i,(i+1)%n))) for i in range(n)];positive=[(1<<a)|(1<<b) for a,b in edges];negative=[m for m in range(1<<n) if not any(m>>a&1 and m>>b&1 for a,b in edges)];maxind=[m for m in negative if all(m>>i&1 or m|(1<<i) not in negative for i in range(n))];rows=positive+maxind;nr=len(rows);ch=nr+n+1;count=0;clauses=[]
def var():
 global count
 count+=1;return count
def add(*xs):clauses.append(list(xs))
def andgate(y,xs):
 for x in xs:add(-y,x)
 add(y,*(-x for x in xs))
def orgate(y,xs):
 for x in xs:add(y,-x)
 add(-y,*xs)
def exactlyone(xs):
 add(*xs)
 for a,b in itertools.combinations(xs,2):add(-a,-b)
def ca(y,a,b,s):add(-s,-y,a);add(-s,-y,b);add(-s,y,-a,-b)
def co(y,a,b,s):add(-s,y,-a);add(-s,y,-b);add(-s,-y,a,b)
wire=[];ops=[];choice=[];clean=[];junk=[]
for i in range(n):
 vs=[var() for _ in range(ch)];wire.append(vs);data=[int(m>>i&1) for m in rows]+[int(i==j) for j in range(n)]+[0]
 for v,b in zip(vs,data):add(v if b else -v)
for g in range(k):
 z=var();ops.append(z);sels=[[var() for _ in range(n+g)] for _ in range(2)];choice.append(sels)
 for ss in sels:exactlyone(ss)
 for a in range(n+g):
  for b in range(a+1):add(-sels[0][a],-sels[1][b])
 taps=[[var() for _ in range(ch)] for _ in range(2)]
 for p in range(2):
  for i,s in enumerate(sels[p]):
   for c in range(ch):add(-s,-taps[p][c],wire[i][c]);add(-s,taps[p][c],-wire[i][c])
 out=[var() for _ in range(ch)];wire.append(out)
 for c in range(nr):ca(out[c],taps[0][c],taps[1][c],z);co(out[c],taps[0][c],taps[1][c],-z)
 for c in range(nr,nr+n):add(-z,-out[c]);co(out[c],taps[0][c],taps[1][c],-z)
 cl=var();clean.append(cl);andgate(cl,[-out[c] for c in range(len(positive),nr)])
 top=var();andgate(top,[z,cl]);dirty=var();andgate(dirty,[z,-cl]);junk.append(dirty)
 orgate(out[-1],[taps[0][-1],taps[1][-1],top])
 if mode!='ordinary':
  add(-z,-taps[0][-1]);add(-z,-taps[1][-1])
 if mode=='ustar':
  add(-top,-taps[0][nr],-taps[1][nr+1]);add(-top,-taps[0][nr+1],-taps[1][nr])
for c in range(nr):add(wire[-1][c] if c<len(positive) else -wire[-1][c])
for g in range(k-1):add(*(choice[j][p][n+g] for j in range(g+1,k) for p in range(2)))
# Canonical topological order by sorted predecessor-wire pair.
for g in range(k-1):
 for b in range(n+g):
  for c in range(b):add(-choice[g][1][b],-choice[g+1][1][c])
 for b in range(n+g):
  for a in range(b):
   for c in range(a):add(-choice[g][1][b],-choice[g+1][1][b],-choice[g][0][a],-choice[g+1][0][c])
if mode in ['ustar','junk']:add(*junk)
output.write_text('p cnf '+str(count)+' '+str(len(clauses))+'\n'+'\n'.join(' '.join(map(str,c))+' 0' for c in clauses)+'\n')
Path(str(output)+'.meta.json').write_text(json.dumps({'n':n,'k':k,'edges':edges,'rows':rows,'mode':mode,'ops':ops,'choice':choice,'clean':clean,'junk':junk},indent=2)+'\n')
print(json.dumps({'n':n,'gates':k,'mode':mode,'truth_rows':nr,'variables':count,'clauses':len(clauses)}))
