from pathlib import Path
import hashlib
import json
import resource
import re
import subprocess
import sys
import time
import sympy as S

base=Path('/tmp/oec/pequalnp-pilot-78/geometry_search/rowzero')
numeric=Path('/tmp/oec/pequalnp-pilot-78/numeric')
which=int(sys.argv[1]) if len(sys.argv)>1 else 7
mode=sys.argv[2] if len(sys.argv)>2 else 'std'
assert mode in ['std','lift']
attempt=sys.argv[3] if len(sys.argv)>3 else ''
assert not attempt or attempt.isdecimal()
source=base/f'trace-Bone-equal-D-linear-{which}.json'
data=json.loads(source.read_text())
x,y,a,u,v,tau=S.symbols('x y a u v tau')
s=S.Rational(data['sum_R']);e2=s*s/2+3*s+9;e3=2*s+6
f=x**3-s*x*x+e2*x-e3
g=y*y+(x-s)*y+x*x-s*x+e2
A=a*a-2*s*a+4*e2
h=3*x*x-2*s*x+A
m=S.Poly(S.resultant(f,h,x),a).monic().as_expr()
assert S.Poly(m,a).degree()==6 and S.Poly(m,a).is_irreducible
den=-2*s*s-3*A+9*e2
xp=S.rem((9*e3-s*A)*S.invert(den,m,a),m,a)
yp=S.rem((a-xp)/2,m,a)
assert S.rem(f.subs(x,xp),m,a)==0
assert S.rem(g.subs({x:xp,y:yp},simultaneous=True),m,a)==0
assert S.expand(xp+2*yp-a)==0
basis_values={(i,j):S.rem(xp**i*yp**j,m,a) for i in range(3) for j in range(2)}
polys=[]
for entry in data['residuals']:
    p=S.Poly(S.sympify(entry['polynomial']),u,v,tau)
    transformed=0
    for monomial,coefficient in p.terms():
        c=S.Poly(coefficient,x,y)
        cc=S.rem(sum(k*basis_values[ij] for ij,k in c.terms()),m,a)
        transformed+=cc*u**monomial[0]*v**monomial[1]*tau**monomial[2]
    polys.append(S.expand(transformed))

def native(e):
    return re.sub(r'\*\*(\d+)',r'^(\1)',str(e))

prefix=f'trace-Bone-equal-D-{which}-{mode}{attempt}'
text='ring r=(0,a),(u,v,tau),dp;\nminpoly='+native(m)+';\noption(redSB);\nshort=0;\n'
text+='ideal I='+','.join(map(native,polys))+';\n'
if mode=='std':
    text+='ideal G=std(I);\nprint("BASIS_SIZE");size(G);print("DIMENSION");dim(G);print("BASIS");G;\n'
else:
    text+='matrix T;ideal G=liftstd(I,T);\nprint("BASIS_SIZE");size(G);print("BASIS");G;\n'
    text+='int unitIndex=0;int ii;for(ii=1;ii<=size(G);ii++){if(G[ii]!=0 && deg(G[ii])==0){unitIndex=ii;break;}}\n'
    text+='print("UNIT_INDEX");unitIndex;\n'
    text+='if(unitIndex!=0){print("TARGET");G[unitIndex];print("CERTIFICATE");for(ii=1;ii<=size(I);ii++){print(T[ii,unitIndex]);}print("RESIDUAL");print(matrix(I)*T-matrix(G));}\n'
text+='quit;\n'
(base/f'{prefix}.sing').write_text(text)
field={'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
       'primitive_element':'a=x+2*y','minpoly':str(m),'x':str(xp),'y':str(yp),
       'residual_indices':[r['index'] for r in data['residuals']],
       'residuals':list(map(str,polys)),
       'scope':'Exact primitive-element conversion of six equal-D residuals; '
               'native output requires independent exact certificate verification.'}
(base/f'{prefix}-input.json').write_text(json.dumps(field,indent=2)+'\n')
env={'LD_LIBRARY_PATH':str(numeric/'singular/lib')+':'+str(numeric/'cas/lib'),
     'OPENBLAS_NUM_THREADS':'1','OMP_NUM_THREADS':'1'}
def limits():
    resource.setrlimit(resource.RLIMIT_AS,(256*2**20,256*2**20))
    resource.setrlimit(resource.RLIMIT_CPU,(60,65))
    resource.setrlimit(resource.RLIMIT_FSIZE,(16*2**20,16*2**20))
    resource.setrlimit(resource.RLIMIT_CORE,(0,0))
start=time.monotonic()
with (base/f'{prefix}.stdout').open('w') as out,(base/f'{prefix}.stderr').open('w') as err:
    try:
        result=subprocess.run([str(numeric/'singular/bin/Singular'),'--quiet','--no-tty',
            '--no-rc','--no-shell','--cpus=1','--threads=1','--flint-threads=1',
            str(base/f'{prefix}.sing')],stdin=subprocess.DEVNULL,stdout=out,stderr=err,
            env=env,preexec_fn=limits,timeout=75)
        code=result.returncode
    except subprocess.TimeoutExpired:
        code='wall_timeout'
report={'exit':code,'algorithm':mode,'memory_mib':256,'cpu_cap':60,'wall_cap':75,
        'seconds':time.monotonic()-start,
        'native_peak_rss_kib':resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,
        'driver_peak_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
(base/f'{prefix}-run.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report),flush=True)
