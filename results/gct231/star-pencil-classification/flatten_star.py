from pathlib import Path
from fractions import Fraction as Q
from collections import defaultdict
import json,resource,time
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CORE,(0,0))
out=Path(__file__).parent;d=json.loads((out/'star-lowdegree-certificate.json').read_text())
steps={z['index']:z for z in d['steps']};n=len(d['variables']);zero=(0,)*n
cache={}
def add(dst,src,c,shift):
 for mon,v in src.items():
  key=tuple(x+y for x,y in zip(mon,shift));dst[key]=dst.get(key,Q(0))+c*v
  if not dst[key]:del dst[key]
def representation(index):
 if index in cache:return cache[index]
 step=steps[index]
 if 'generator' in step['kind']:ans={step['kind']['generator']:{zero:Q(1)}}
 else:
  ans={}
  for parent,shift,c in step['parents']:
   for generator,poly in representation(parent).items():add(ans.setdefault(generator,{}),poly,Q(c),shift)
  ans={i:p for i,p in ans.items() if p}
 cache[index]=ans
 return ans
start=time.monotonic();answer=representation(98)
generators={step['kind']['generator']:{tuple(mon):Q(c) for mon,c in step['polynomial']} for step in steps.values() if 'generator' in step['kind']}
total={}
for g,mult in answer.items():
 for shift,c in mult.items():add(total,generators[g],c,shift)
assert total=={(0,0,1,0,0):Q(1)}
result={'variables':['p','q','r','a','b'],'target':[[[0,0,1,0,0],'1']],
 'generators':[[[list(mon),str(c)] for mon,c in sorted(generators[g].items())] for g in sorted(generators)],
 'multipliers':[[[list(mon),str(c)] for mon,c in sorted(answer.get(g,{}).items())] for g in sorted(generators)],
 'identity':'sum multiplier_i * generator_i = r','seconds':time.monotonic()-start}
(out/'star-r-flat-certificate.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS',result['identity'],'seconds',result['seconds'],'term_counts',[len(p) for p in result['multipliers']],flush=True)
