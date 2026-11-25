from pathlib import Path
import subprocess,resource,json,time,re
from sympy.polys.rings import ring
from sympy.polys.domains import QQ
import sympy as s
base=Path('/tmp/oec/pequalnp-pilot-78');job=base/'geometry_search/tracezero_Bzero_generic';data=json.loads((job/'systems.json').read_text());R,*vs=ring(','.join(data['variables']),QQ)
def limits():
 resource.setrlimit(resource.RLIMIT_AS,(256*2**20,256*2**20));resource.setrlimit(resource.RLIMIT_CPU,(60,65));resource.setrlimit(resource.RLIMIT_FSIZE,(16*2**20,16*2**20));resource.setrlimit(resource.RLIMIT_CORE,(0,0))
env={'LD_LIBRARY_PATH':str(base/'numeric/singular/lib')+':'+str(base/'numeric/cas/lib'),'OMP_NUM_THREADS':'1','OPENBLAS_NUM_THREADS':'1'}
for case in data['cases']:
 name=case['name'];source=(job/(name+'.sing')).read_text().split('ideal G=std(I);')[0]
 script=source+'matrix T;ideal G=liftstd(I,T);\nshort=0;print("SIZE");size(G);print("BASIS");G;\nint i;for(i=1;i<=nrows(T);i++){print("COEFF");i;print(string(T[i,1]));}\nprint("IDENTITY_VALID");(matrix(I)*T==matrix(G));print("COMPLETED_CERTIFICATE");quit;\n'
 (job/(name+'-lift.sing')).write_text(script);start=time.monotonic()
 with (job/(name+'-lift.stdout')).open('wb') as out,(job/(name+'-lift.stderr')).open('wb') as err:
  try:p=subprocess.run([str(base/'numeric/singular/bin/Singular'),'--quiet','--no-tty','--no-rc','--no-shell','--cpus=1','--threads=1','--flint-threads=1',str(job/(name+'-lift.sing'))],stdin=subprocess.DEVNULL,stdout=out,stderr=err,env=env,preexec_fn=limits,timeout=75);code=p.returncode
  except subprocess.TimeoutExpired:code='timeout'
 text=(job/(name+'-lift.stdout')).read_text();r={'case':name,'exit':code,'seconds':time.monotonic()-start,'complete':'COMPLETED_CERTIFICATE' in text}
 if r['complete']:
  assert 'IDENTITY_VALID\n1' in text
  target=QQ(re.search(r'G\[1\]=([^\n]+)',text).group(1));assert target
  parts=text.split('COEFF\n')[1:];multipliers=[]
  for i,part in enumerate(parts):
   if 'IDENTITY_VALID' in part:part=part.split('IDENTITY_VALID')[0]
   lines=part.strip().splitlines();assert int(lines[0])==i+1
   expr=''.join(lines[1:]);multipliers.append(R.from_expr(s.sympify(expr.replace('^','**'))))
  polys=[R.from_expr(s.sympify(f)) for f in case['generators']]
  assert len(multipliers)==len(polys)==9
  residual=sum(f*g for f,g in zip(polys,multipliers))-target;assert residual==0
  r.update({'nonzero_constant':str(target),'independent_exact_residual':'0','multiplier_terms':sum(len(x) for x in multipliers),'multipliers':list(map(str,multipliers)),'source_generators':case['generators']})
 (job/(name+'-certificate.json')).write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({k:v for k,v in r.items() if k not in ('multipliers','source_generators')}),flush=True)
