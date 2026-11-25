from pathlib import Path
from fractions import Fraction as Q
import hashlib,json,resource
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CORE,(0,0))
out=Path(__file__).parent;data=json.loads((out/'star-r-flat-certificate.json').read_text())
gens=[{tuple(mon):Q(c) for mon,c in terms} for terms in data['generators']]
degrees=[max(map(sum,g),default=0) for g in gens]
tags=[(i,tuple(mon)) for i,terms in enumerate(data['multipliers']) for mon,c in terms]
tags.sort(key=lambda z:(sum(z[1])+degrees[z[0]],sum(z[1]),z[0],z[1]))
rows={}
for column,(i,mult) in enumerate(tags):
 for mon,c in gens[i].items():
  exponent=tuple(a+b for a,b in zip(mon,mult));rows.setdefault(exponent,{})[column]=c
target=(0,0,1,0,0);rows[target][len(tags)]=Q(-1)
ordered=sorted(rows,key=lambda m:(sum(m),m));n=len(tags);lengths=[len(rows[m]) for m in ordered]
path=out/'star-linear-compress.in'
with path.open('w') as f:
 f.write(f'{n} {len(rows)} 0 {sum(lengths)}\n'+' '.join(map(str,lengths))+'\n')
 for mon in ordered:
  for column,c in sorted(rows[mon].items()):
   exponents=['0']*n
   if column<n:exponents[column]='1'
   f.write(str(c.numerator)+' '+str(c.denominator)+' '+' '.join(exponents)+'\n')
metadata={'tags':[[i,list(mon)] for i,mon in tags],'rows':[list(m) for m in ordered],
          'source_sha256':hashlib.sha256((out/'star-r-flat-certificate.json').read_bytes()).hexdigest(),
          'input_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
          'shape':[len(rows),n],'nonzero_terms':sum(lengths),
          'scope':'Linear equations for existing multiplier supports; only a proposed rational solution, to be checked by direct polynomial multiplication.'}
(out/'star-linear-compress.json').write_text(json.dumps(metadata,indent=2)+'\n')
print('LINEAR SYSTEM',metadata['shape'],'terms',metadata['nonzero_terms'],'bytes',path.stat().st_size)
