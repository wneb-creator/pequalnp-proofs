from pathlib import Path
from itertools import permutations
import sympy as S
import json,subprocess,resource,time,random,hashlib
base=Path('/tmp/oec/pequalnp-pilot-78/geometry_search/rowzero')
source=Path('/tmp/oec/pequalnp-pilot-78/geometry_search/tracezero_rankdrop/shifted-matrix.json')
raw=source.read_bytes();data=json.loads(raw)
names=[x for x in data['variables'] if not x.startswith('b')]
variables=S.symbols(' '.join(names));zero={S.Symbol('b'+str(i)):0 for i in range(4)}
polys=[S.expand(S.sympify(x).subs(zero)) for x in data['flat_generators']]
assert len(polys)==12 and all(p.free_symbols<=set(variables) for p in polys)
p0,p1,p2,p3,p4,p5,k,l=variables;s,t=S.symbols('s t')
Q=S.Matrix([[1,1,1,1],[1,1,-1,-1],[1,-1,1,-1],[1,-1,-1,1]])/2
exponents=[(degree-j,j) for degree in (2,3,4) for j in range(degree+1)]
scales=[set() for _ in polys];rng=random.Random(78231)
for _ in range(4):
 point={v:rng.randrange(-2,3) for v in variables}
 D=[s,t,point[k]*s+point[l]*t]
 R=[point[p0]*s+point[p1]*t,point[p2]*s+point[p3]*t,point[p4]*s+point[p5]*t]
 v=[(R[i]+2*D[i])/2 for i in range(3)]
 Tp=S.Matrix([[0,v[0],v[1],v[2]],[v[0],0,-R[2]/2,-R[1]/2],[v[1],-R[2]/2,0,-R[0]/2],[v[2],-R[1]/2,-R[0]/2,0]])
 M=S.ones(4)+Q*Tp*Q.T
 per=S.Poly(S.expand(sum(S.prod(M[i,j] for i,j in enumerate(perm)) for perm in permutations(range(4)))-24),s,t)
 assert per.coeff_monomial(s)==per.coeff_monomial(t)==0
 for i,(g,exp) in enumerate(zip(polys,exponents)):
  expected=g.subs(point);actual=per.coeff_monomial(s**exp[0]*t**exp[1])
  if expected:scales[i].add(actual/expected)
  else:assert actual==0
assert all(len(x)==1 and next(iter(x))!=0 for x in scales)
manifest={'scope':'Exact B-projection-rank-zero branch of tracezero D-rank-two planes in the normalized D=(s,t,ks+lt) chart. No nonemptiness or coverage conclusion assumed.','source_sha256':hashlib.sha256(raw).hexdigest(),'variables':names,'generators':list(map(str,polys)),'direct_permanent_audit_comparisons':48,'actual_coefficient_scales':[str(next(iter(x))) for x in scales]}
(base/'trace-Bzero-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
script='ring r=0,('+','.join(names)+'),dp;\noption(redSB);\nideal I='+','.join(str(x).replace('**','^') for x in polys)+';\nideal G=slimgb(I);\nprint("BASIS_SIZE");size(G);print("DIMENSION");dim(G);print("BASIS");G;quit;\n'
path=base/'trace-Bzero.sing';path.write_text(script)
native=Path('/tmp/oec/pequalnp-pilot-78/numeric')
env={'LD_LIBRARY_PATH':str(native/'singular/lib')+':'+str(native/'cas/lib'),'OPENBLAS_NUM_THREADS':'1','OMP_NUM_THREADS':'1'}
def limits():
 resource.setrlimit(resource.RLIMIT_AS,(256*2**20,256*2**20))
 resource.setrlimit(resource.RLIMIT_CPU,(60,65))
 resource.setrlimit(resource.RLIMIT_FSIZE,(16*2**20,16*2**20))
 resource.setrlimit(resource.RLIMIT_CORE,(0,0))
start=time.monotonic()
with (base/'trace-Bzero-singular.stdout').open('w') as out,(base/'trace-Bzero-singular.stderr').open('w') as err:
 try:
  process=subprocess.run([str(native/'singular/bin/Singular'),'--quiet','--no-tty','--no-rc','--no-shell','--cpus=1','--threads=1','--flint-threads=1',str(path)],stdin=subprocess.DEVNULL,stdout=out,stderr=err,env=env,preexec_fn=limits,timeout=75)
  exit_code=process.returncode
 except subprocess.TimeoutExpired:exit_code='wall_timeout'
report={'exit_code':exit_code,'seconds':time.monotonic()-start,'memory_limit_mib':256,'cpu_limit_seconds':60,'scope':manifest['scope']}
(base/'trace-Bzero-result.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report),flush=True)
