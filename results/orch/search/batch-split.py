from pathlib import Path
from itertools import permutations
import json, subprocess, time
pdir=Path('/tmp/oec/pequalnp-pilot-161')
allresults=[]
for p,l in [(2,3),(2,4),(3,3)]:
 reps={}
 for mask in range(1,1<<(p*l)):
  if any(sum(bool(mask>>(a*l+b)&1) and bool(mask>>(aa*l+b)&1) for b in range(l))>1 for a in range(p) for aa in range(a+1,p)):continue
  canon=min(sum(((mask>>(a*l+b))&1)<<(ap[a]*l+bp[b]) for a in range(p) for b in range(l)) for ap in permutations(range(p)) for bp in permutations(range(l)))
  if canon in reps:continue
  es=[(a,b) for a in range(p) for b in range(l) if canon>>(a*l+b)&1]
  tau=min(s.bit_count() for s in range(1<<(p+l)) if all((s>>a&1) or (s>>(p+b)&1) for a,b in es))
  reps[canon]=(es,tau)
 print('DIM',p,l,'reps',len(reps),flush=True)
 for mask,(es,tau) in sorted(reps.items()):
  edges=';'.join(f'{a},{b}' for a,b in es)
  for kind,k in [('and',tau-1),('or',len(es)-2)]:
   if k<0:continue
   out=pdir/f'free-batch-{p}x{l}-{mask}-{kind}{k}'
   with Path(str(out)+'.stdout').open('w') as f:
    r=subprocess.run(['python3',str(pdir/'freegate-synth.py'),'--p',str(p),'--l',str(l),'--edges',edges,'--gates',str(k),'--kind',kind,'--limit','30','--out',str(out)],stdout=f,stderr=f)
   if r.returncode: verdict='ERROR'
   else: verdict=Path(str(out)+'.log').read_text().splitlines()[0]
   result=dict(p=p,l=l,mask=mask,edges=es,tau=tau,kind=kind,gates=k,verdict=verdict)
   allresults.append(result);print(json.dumps(result),flush=True)
   if verdict=='sat': print('SPLIT COUNTEREXAMPLE FOUND',flush=True)
 (pdir/'batch-split-results.json').write_text(json.dumps(allresults,indent=2))
print('DONE',len(allresults),flush=True)
