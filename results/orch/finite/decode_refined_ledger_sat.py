import json,sys
from pathlib import Path
base=Path(sys.argv[1]); log=Path(sys.argv[2]).read_text(); d=json.loads(base.with_suffix('.json').read_text())
assert 's SATISFIABLE' in log
sat=set(int(w) for row in log.splitlines() if row.startswith('v ') for w in row.split()[1:] if int(w)>0)
def lit(v): return v if isinstance(v,bool) else (v in sat if v>0 else -v not in sat)
n,p,m,mode=d['n'],d['p'],d['m'],d['mode'];l=n-p;E=set(map(tuple,d['E']))
gates=[]
for i in range(m):
 ps=[(a,b) for a,b,s in d['pairs'][i] if lit(s)]; assert len(ps)==1
 gates.append(('or' if lit(d['ops'][i]) else 'and',*ps[0]))
outs=[i for i,s in enumerate(d['outputs']) if lit(s)]; assert len(outs)==1
output=n+outs[0]
values=[sum(1<<x for x in range(1<<n) if x>>i&1) for i in range(n)]
reach=[1<<i for i in range(n)]
for i,(op,a,b) in enumerate(gates):
 assert 0<=a<=b<n+i
 values.append(values[a]|values[b] if op=='or' else values[a]&values[b])
 reach.append(reach[a]|reach[b] if op=='or' else 0)
 for x,v in enumerate(d['vals'][i]):assert lit(v)==bool(values[n+i]>>x&1)
 for j,v in enumerate(d['reaches'][i]):assert lit(v)==bool(reach[n+i]>>j&1)
 assert not ((reach[n+i]&((1<<p)-1)) and (reach[n+i]>>p))
target=sum(1<<x for x in range(1<<n) if any((x>>a&1) and (x>>(p+b)&1) for a,b in E))
assert values[output]==target
neigh=[0]*n
for a,b in E:neigh[a]|=1<<(p+b);neigh[p+b]|=1<<a
def ortt(S):return sum(1<<x for x in range(1<<n) if x&S)
exact=[];family=[]
for i,(op,a,b) in enumerate(gates):
 ex=[];fa=[];single=sum(1<<a for a in range(n) if values[n+i]>>(1<<a)&1)
 for t,(c,S) in enumerate(d['specs']):
  e=op=='or' and values[n+i]==ortt(S)
  f=e if mode==0 else op=='or' and single==S and not(values[n+i]>>(((1<<n)-1)^neigh[c])&1)
  assert lit(d['exact'][i][t])==e
  assert lit(d['family'][i][t])==f
  ex.append(e);fa.append(f)
 exact.append(ex);family.append(fa)
star=[any(row) for row in family]
active=[any(family[i][t] for i in range(m) for t,(cc,S) in enumerate(d['specs']) if cc==c) for c in range(n)]
coverage=[]
for a,b in d['E']:
 ts=[[t for t,(c,S) in enumerate(d['specs']) if c==a and S>>(p+b)&1],
     [t for t,(c,S) in enumerate(d['specs']) if c==p+b and S>>a&1]]
 assert any(exact[i][t] for i in range(m) for side in ts for t in side)
 coverage.extend(any(family[i][t] for i in range(m) for t in side) for side in ts)
assert all(lit(v)==x for v,x in zip(d['star'],star))
assert all(lit(v)==x for v,x in zip(d['active'],active))
assert all(lit(v)==x for v,x in zip(d['coverage'],coverage))
tau=min(s.bit_count() for s in range(1<<n) if all((s>>a&1) or (s>>(p+b)&1) for a,b in E))
q=sum(active);L=sum(coverage);nonStar=m-sum(star)
print('Validated all',1<<n,'assignments; output',output,'T0; every edge pure-star served')
print('mode',mode,'gates',m,'starGates',sum(star),'nonStar',nonStar,'q',q,'L',L,'E',len(E),'tau',tau,'ledgerSlack',nonStar+L+1-q-tau-len(E))
for i,g in enumerate(gates):print(n+i,g)
