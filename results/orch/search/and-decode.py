import argparse,itertools,json
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('metadata');p.add_argument('log');p.add_argument('--out');a=p.parse_args()
d=json.loads(Path(a.metadata).read_text());vs=set()
for ln in Path(a.log).read_text().splitlines():
 if ln.startswith('v '):vs.update(int(x)for x in ln[2:].split()if int(x)>0)
if not vs:print('No SAT model');raise SystemExit
n=d['n'];skeleton=[]
for left,right in d['gates']:skeleton.append(([i for i,v in enumerate(left)if v in vs],[i for i,v in enumerate(right)if v in vs]))
outs=[i for i,v in enumerate(d['outs'])if v in vs];es=d['edges']
for x in range(1<<n):
 w=[bool(x>>i&1)for i in range(n)]
 for left,right in skeleton:w.append(any(w[i]for i in left)and any(w[i]for i in right))
 assert any(w[n+i]for i in outs)==any((x>>i&1)and(x>>j&1)for i,j in es)
# Expand into binary circuit; reuse identical OR pairs.
wiremap=list(range(n));gs=[];cache={}
def gate(op,a,b):
 if a==b:return a
 a,b=sorted((a,b));key=(op,a,b)
 if key in cache:return cache[key]
 v=n+len(gs);gs.append([op,a,b]);cache[key]=v;return v
def orgroup(group):
 assert group
 q=group[0]
 for x in group[1:]:q=gate('or',q,x)
 return q
for left,right in skeleton:wiremap.append(gate('and',orgroup([wiremap[i]for i in left]),orgroup([wiremap[i]for i in right])))
output=orgroup([wiremap[n+i]for i in outs])
hood=[0]*n
for i,j in es:assert i!=j;hood[i]|=1<<j;hood[j]|=1<<i
assert all((hood[i]&hood[j]).bit_count()<2 for i,j in itertools.combinations(range(n),2))
for x in range(1<<n):
 w=[bool(x>>i&1)for i in range(n)]
 for z,(op,i,j)in enumerate(gs):
  assert 0<=i<n+z and 0<=j<n+z
  w.append((w[i]or w[j])if op=='or'else(w[i]and w[j]))
 assert w[output]==any((x>>i&1)and(x>>j&1)for i,j in es)
alpha=max(x.bit_count()for x in range(1<<n)if not any((x>>i&1)and(x>>j&1)for i,j in es));tau=n-alpha
r={'n':n,'edges':es,'tau':tau,'ands':skeleton,'outs':outs,'gates':gs,'output':output,'size':len(gs),'bound':len(es)+tau-1,'truth_table_verified':True,'is_counterexample':len(gs)<len(es)+tau-1}
print(json.dumps(r,indent=2))
if a.out:Path(a.out).write_text(json.dumps(r,indent=2))
