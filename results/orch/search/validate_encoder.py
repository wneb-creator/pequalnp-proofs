import json,subprocess
from pathlib import Path
p=Path('/tmp/oec/pequalnp-pilot-111/counterexample');seed=json.loads((p.parent/'negation-cover-seed.json').read_text());edges='01,12,23,34,40,05,16,27,38,49,57,79,96,68,85';masks={'and':8,'or':14}
def reorder(gs):
 known={i:i for i in range(10)};pending=[(10+j,*g) for j,g in enumerate(gs)];out=[]
 while pending:
  ready=[g for g in pending if g[2] in known and g[3] in known]
  def key(g):return tuple(sorted([known[g[2]],known[g[3]]]))+(g[1],)
  g=min(ready,key=key);pending.remove(g);idx,mask,a,b=g;a,b=known[a],known[b]
  if a>b:
   a,b=b,a;mask=sum(((mask>>(2*y+x))&1)<<(2*x+y) for x in range(2) for y in range(2))
  known[idx]=10+len(out);out.append((mask,a,b))
 return out
base=[(masks[op],a,b) for op,a,b in seed['gates']]
cases=[]
for kind in ['plain','flipped','diff_a','diff_b']:
 gs=[];mapping={i:i for i in range(10)};flags=[];phases=[]
 for j,(mask,a,b) in enumerate(base):
  a,b=mapping[a],mapping[b]
  if j==0 and kind in ['diff_a','diff_b']:
   gs.append((2 if kind=='diff_a' else 4,a,b));tmp=9+len(gs)
   gs.append((14,a if kind=='diff_a' else b,tmp));flags=[a if kind=='diff_a' else b]
  else:gs.append((mask,a,b))
  mapping[10+j]=9+len(gs)
 gs=reorder(gs)
 if kind=='flipped':phases=[10];flags=[gs[0][1],gs[0][2],10]
 cases.append((kind,gs,phases,flags))
for kind,gs,phases,flags in cases:
 stem=p/('validation-'+kind);cnf=stem.with_suffix('.cnf');signed=p/('validation-'+kind+'-signed.cnf')
 with stem.with_suffix('.generator.stdout').open('w') as out,stem.with_suffix('.generator.stderr').open('w') as err:
  subprocess.run(['python3',str(p/'synth_binary.py'),'10',str(len(gs)),edges,str(signed)],stdout=out,stderr=err,check=True)
  subprocess.run(['python3',str(p/'add_inversion_budget.py'),str(signed),str(len(flags)),str(cnf)],stdout=out,stderr=err,check=True)
 meta=json.loads(cnf.with_suffix('.meta.json').read_text());s,A=meta['s'],meta['A'];ix=lambda kd,j,a:(kd*(s+1)+j)*A+a+1;val=set()
 for j,(mask,a,b) in enumerate(gs):val.update([ix(0,j,meta['ops'].index(mask)),ix(1,j,a),ix(2,j,b)])
 for i in phases:val.add(ix(6,0,i))
 for i in flags:val.add(ix(7,0,i))
 for r in meta['rows']:
  w=[bool(r>>i&1) for i in range(10)]
  for j,(mask,a,b) in enumerate(gs):
   if w[a]:val.add(ix(4,j,r))
   if w[b]:val.add(ix(5,j,r))
   w.append(bool(mask>>(2*w[a]+w[b])&1))
   if w[-1]:val.add(ix(3,j,r))
 count=0
 for line in cnf.read_text().splitlines()[1:]:
  clause=[int(x) for x in line.split()[:-1]];count+=1
  assert any((x>0 and x in val) or (x<0 and -x not in val) for x in clause),(kind,count,clause)
 print(kind,'passed',count,'clauses','binary',len(gs),'charged inversions',len(flags),flush=True)
