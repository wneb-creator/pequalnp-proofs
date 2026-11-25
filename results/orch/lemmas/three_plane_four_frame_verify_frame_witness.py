from pathlib import Path
import json,sys,resource,sympy as s
job=Path('/tmp/oec/pequalnp-pilot-79');base='four-frame-power-triangle-d7-n2';metadata=json.loads((job/(base+'-metadata.json')).read_text());prime=1000000007;label=sys.argv[1];assert label in ('triangle','path');resource.setrlimit(resource.RLIMIT_CORE,(0,0))
target=tuple(metadata['target']) if label=='triangle' else (0,0,3,0,3,0,0,0,0,0);column=metadata['columns'].index(list(target));witness_path=job/(base+('-p1000000007-witness.json' if label=='triangle' else '-path-p1000000007-witness.json'));data=json.loads(witness_path.read_text())
def verify_original(data,target):
 source=(job/'four-frame-cubic-triangle-0.msolve').read_text().splitlines();names=source[0].split(',');assert names[-1]=='v' and names[:-1]==metadata['variables'];vs=s.symbols(' '.join(names));body='\n'.join(source[2:]);assert all(c.isalnum() or c in ' _+-*^,()\n' for c in body);local=dict(zip(names,vs));raw=[s.Poly(s.sympify(q.strip().replace('^','**'),locals=local),*vs,domain=s.ZZ) for q in body.split(',') if q.strip()];assert len(raw)==17;polys=[]
 for p in raw[:-1]:
  assert all(m[-1]==0 for m,c in p.terms());polys.append({m[:-1]:int(c) for m,c in p.terms()})
 weights=data['witness'];origins=metadata['row_origins'];assert len(weights)==len(origins) and data['prime']==prime;out={}
 for w,(i,mult) in zip(weights,origins):
  if not w:continue
  assert 0<=i<len(polys) and len(mult)==10 and all(isinstance(e,int) and e>=0 for e in mult)
  for mon,c in polys[i].items():
   key=tuple(a+b for a,b in zip(mon,mult));out[key]=(out.get(key,0)+w*c)%prime
 out={m:c for m,c in out.items() if c};assert out=={target:1};return sum(w!=0 for w in weights)
with (job/(base+'.matrix')).open() as f:
 cols,rows=map(int,next(f).split());weights=data['witness'];assert len(weights)==rows;result=[0]*cols;count=0
 for weight,line in zip(weights,f):
  count+=1;terms=list(map(int,line.split()));assert len(terms)==1+2*terms[0]
  if weight:
   for j in range(terms[0]):
    index,coeff=terms[1+2*j:3+2*j];assert 0<=index<cols;result[index]=(result[index]+weight*coeff)%prime
 assert count==rows and not f.read().strip()
assert result==[int(j==column) for j in range(cols)]
support=verify_original(data,target)
summary={'classification':'Finite-field polynomial identity verified independently; not a characteristic-zero or Lean proof','label':label,'prime':prime,'target':list(target),'support':support,'matrix_identity_verified':True,'original_polynomial_identity_verified':True}
(job/(base+'-'+label+'-witness-verification.json')).write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary))
