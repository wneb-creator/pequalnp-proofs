from pathlib import Path
import argparse,importlib.util,json,hashlib
BASE=Path('/tmp/oec/pequalnp-pilot-152/gap-1884')
spec=importlib.util.spec_from_file_location('petersen_enc2',BASE/'petersen-enc2.py');mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
def extra(n,s,rows,budget):
 width=2**n+n+s+2
 def v(kd,j,a):return (kd*(s+1)+j)*width+a+1
 clauses=[]
 if budget==1:
  for j in range(s):
   for i in range(j):clauses.append([-v(0,i,3),-v(0,j,3)])
 elif budget==2:
  for k in range(s):
   for j in range(k):
    for i in range(j):clauses.append([-v(0,i,3),-v(0,j,3),-v(0,k,3)])
 else:raise ValueError('budget must be1 or2')
 for j in range(s):
  clauses.append([v(7,j,0)]+[v(3,j,r) for r in rows]);clauses.append([v(7,j,0)]+[-v(3,j,r) for r in rows])
 for j in range(s):
  for a in range(n+j):clauses.append([v(7,j,0)]+[v(8+a,j,r) for r in rows])
 for j in range(s):
  for a in range(n+j):
   for r in rows:
    d=v(8+a,j,r);w=v(3,j,r)
    if a<n:clauses.append([-d,-w if r>>a&1 else w])
    else:
     old=v(3,a-n,r);clauses.append([-d,w,old]);clauses.append([-d,-w,-old])
 return clauses
parser=argparse.ArgumentParser();parser.add_argument('--gates',type=int,default=18);parser.add_argument('--budget',type=int,default=1);parser.add_argument('--out',type=Path,required=True);parser.add_argument('--control',type=Path)
args=parser.parse_args();n=11;s=args.gates;samples=mod.seed_samples();rows=[r+1024*(1-(r&1)) for r in samples]
clauses,width=mod.encode(n,s,rows);base_count=len(clauses);extra_clauses=extra(n,s,rows,args.budget);clauses.extend(extra_clauses)
def v(kd,j,a):return (kd*(s+1)+j)*width+a+1
if args.control:
 data=json.loads(args.control.read_text());gates=data['gates'];assert len(gates)==s
 assignment={};units=[];opindex={'and':0,'or':1,'true':2,'not':3}
 def fix(atom,value):assignment[atom]=value;units.append([atom if value else -atom])
 for j,(op,a,b) in enumerate(gates):
  for o in range(4):fix(v(0,j,o),o==opindex[op])
  for e,k in [(1,a),(2,b)]:
   for t in range(n+j+1):fix(v(e,j,t),t==k)
  fix(v(7,j,0),False)
 for k in range(n+s+1):fix(v(6,0,k),k==data['output'])
 for r in rows:
  values=[bool(r>>i&1) for i in range(n)]
  for j,(op,a,b) in enumerate(gates):
   va,vb=values[a],values[b];w=va and vb if op=='and' else va or vb if op=='or' else not va
   assignment[v(3,j,r)]=w;assignment[v(4,j,r)]=va;assignment[v(5,j,r)]=vb
   for a in range(n+j):assignment[v(8+a,j,r)]=w!=values[a]
   values.append(w)
  assert values[data['output']]==mod.target(r)
 assert all(any(assignment.get(abs(l),False)==(l>0) for l in c) for c in clauses)
 print('ALL_BASE_BUDGET_SEMANTIC_CLAUSES_VERIFIED',len(clauses),'control_units',len(units),flush=True);clauses.extend(units)
maxvar=max(abs(l) for c in clauses for l in c)
with args.out.open('w') as f:
 f.write(f'p cnf {maxvar} {len(clauses)}\n')
 for c in clauses:f.write(' '.join(map(str,c))+' 0\n')
metadata=dict(n=n,s=s,width=width,samples=samples,rows=rows,variables=maxvar,clauses=len(clauses),base_clauses=base_count,extra_clauses=len(extra_clauses),budget=args.budget,source='Exact LinkN2.enc2 then canonical fNotOne/fNotTwo then fNonconstant,fDifferentReq,fDifferentDef.',dependency='Semantic irredundancy/sample-minimality proof in progress at generation; not a completed Lean certificate.',control=str(args.control) if args.control else None)
args.out.with_suffix('.json').write_text(json.dumps(metadata,indent=2)+'\n')
print('CNF',args.out.name,'variables',maxvar,'clauses',len(clauses),'bytes',args.out.stat().st_size,'sha256',hashlib.sha256(args.out.read_bytes()).hexdigest(),flush=True)
