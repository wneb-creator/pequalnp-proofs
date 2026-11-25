import json
import sys
from pathlib import Path

k=int(sys.argv[1])
folder=Path(sys.argv[2])
normalize=(len(sys.argv)>3 and sys.argv[3]=='normalize')
source=folder/'library-gate-petersen.txt'
ls=source.read_text().splitlines()
n,_,rows,want=map(int,ls[0].split())
full=(1<<rows)-1
xs=[full^int(x) for x in ls[1].split()]
want^=full

clauses=[[1]]
labels={'true':1}
nextid=2

def new(label):
 global nextid
 labels[label]=nextid;nextid+=1
 return nextid-1

def clause(*ls):
 if 1 in ls:return
 ss=set(x for x in ls if x!=-1)
 if any(-x in ss for x in ss):return
 clauses.append(sorted(ss,key=lambda x:abs(x)))

def band(a,b,label):
 if a==1:return b
 if b==1:return a
 if a==-1 or b==-1:return -1
 c=new(label)
 clause(-c,a);clause(-c,b);clause(c,-a,-b)
 return c

def bor(items,label):
 items=list(dict.fromkeys(v for v in items if v!=-1))
 if 1 in items:return 1
 if not items:return -1
 if len(items)==1:return items[0]
 c=new(label)
 for v in items:clause(-v,c)
 clause(-c,*items)
 return c

signals=[[1 if xs[i]>>t&1 else -1 for t in range(rows)] for i in range(n)]
selector=[]
for j in range(k):
 sides=[];sels=[]
 for b in range(2):
  sel=[new(f'sel_{j}_{b}_{w}') for w in range(n+j)]
  sels.append(sel)
  vals=[]
  for t in range(rows):
   vals.append(bor((band(sel[w],signals[w][t],f'v_{j}_{b}_{t}_{w}') for w in range(n+j)),f'side_{j}_{b}_{t}'))
  sides.append(vals)
 if normalize:
  false_rows=[t for t in range(rows) if not (want>>t&1)]
  leftw=[band(-sides[0][t],sides[1][t],f'left_witness_{j}_{t}') for t in false_rows]
  rightw=[band(sides[0][t],-sides[1][t],f'right_witness_{j}_{t}') for t in false_rows]
  clause(*leftw);clause(*rightw)
  for sel in sels:
   for a in range(n):
    for b in range(a+1,n):
     if not any(not(xs[a]>>t&1) and not(xs[b]>>t&1) for t in false_rows):clause(-sel[a],-sel[b])
 selector.append(sels)
 signals.append([band(sides[0][t],sides[1][t],f'gate_{j}_{t}') for t in range(rows)])
 # Numeric ordering of operand selector bit-vectors removes AND commutativity.
 prefix=1
 for w in reversed(range(n+j)):
  a,b=sels[0][w],sels[1][w]
  clause(-prefix,-a,b)
  eq=new(f'eq_{j}_{w}')
  clause(-eq,-a,b);clause(-eq,a,-b);clause(eq,a,b);clause(eq,-a,-b)
  prefix=band(prefix,eq,f'prefix_{j}_{w}')

outsel=[new(f'out_{w}') for w in range(n+k)]
for t in range(rows):
 out=bor((band(outsel[w],signals[w][t],f'ov_{t}_{w}') for w in range(n+k)),f'outval_{t}')
 clause(out if want>>t&1 else -out)

stem=folder/f'gatecount-dual-and{k}{"-normalized" if normalize else ""}'
with stem.with_suffix('.cnf').open('w') as f:
 f.write(f'p cnf {nextid-1} {len(clauses)}\n')
 for c in clauses:f.write(' '.join(map(str,c))+' 0\n')
stem.with_suffix('.json').write_text(json.dumps({'n':n,'k':k,'rows':rows,'want':want,'inputs':xs,'labels':labels,'selector':selector,'outsel':outsel},sort_keys=True))
print('CNF variables',nextid-1,'clauses',len(clauses),'rows',rows,'file',stem.with_suffix('.cnf'))
