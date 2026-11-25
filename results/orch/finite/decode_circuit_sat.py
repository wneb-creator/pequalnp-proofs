import json,sys
from pathlib import Path
base=Path(sys.argv[1]);log=Path(sys.argv[2]).read_text();d=json.loads(base.with_suffix('.json').read_text())
assert 's SATISFIABLE' in log
sat=set(int(w) for l in log.splitlines() if l.startswith('v ') for w in l.split()[1:] if int(w)>0)
n,p=d['n'],d['p'];m=d['m'];E=set(map(tuple,d['E']));gates=[]
for i in range(m):
 ps=[(a,b) for a,b,s in d['pairs'][i] if s in sat];assert len(ps)==1
 gates.append(('or' if d['ops'][i] in sat else 'and',*ps[0]))
values=[sum(1<<x for x in range(1<<n) if x>>i&1) for i in range(n)];reach=[1<<i for i in range(n)]
for op,a,b in gates:
 values.append((values[a]|values[b]) if op=='or' else (values[a]&values[b]));reach.append((reach[a]|reach[b]) if op=='or' else 0)
target=sum(1<<x for x in range(1<<n) if any((x>>a&1) and (x>>(p+b)&1) for a,b in E))
assert values[-1]==target
T=sum(bool(reach[n+i]&((1<<p)-1)) and bool(reach[n+i]&(((1<<(n-p))-1)<<p)) for i,(op,a,b) in enumerate(gates) if op=='or')
def ortt(S):return sum(1<<x for x in range(1<<n) if x&S)
served={}
for a,b in E:
 for j,(op,_,_) in enumerate(gates):
  if op!='or':continue
  for S in range(1<<n):
   if S.bit_count()<2 or values[n+j]!=ortt(S):continue
   if S&((1<<p)-1)==0 and S>>(p+b)&1 and all((a,k-p) in E for k in range(p,n) if S>>k&1):served[a,b]=j
   if S>>p==0 and S>>a&1 and all((k,b) in E for k in range(p) if S>>k&1):served[a,b]=j
print('Validated all',1<<n,'input assignments; size',m,'OR count',sum(op=='or' for op,_,_ in gates),'T',T,'star-served',len(served),'/',len(E))
for i,g in enumerate(gates):print(n+i,g)
