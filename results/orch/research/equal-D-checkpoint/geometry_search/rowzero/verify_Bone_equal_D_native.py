from pathlib import Path
import hashlib
import json
import resource
import sys
import time
import sympy as S
from sympy.polys.rings import ring
from sympy.polys.domains import QQ

resource.setrlimit(resource.RLIMIT_AS,(256*2**20,256*2**20))
resource.setrlimit(resource.RLIMIT_CPU,(60,65))
start=time.monotonic()
base=Path('/tmp/oec/pequalnp-pilot-78/geometry_search/rowzero')
which=int(sys.argv[1]) if len(sys.argv)>1 else 7
prefix=f'trace-Bone-equal-D-{which}-lift'
data=json.loads((base/f'{prefix}-input.json').read_text())
raw=(base/f'{prefix}.stdout').read_bytes()
lines=raw.decode().splitlines()
assert lines[:2]==['BASIS_SIZE','1']
assert lines[4:7]==['UNIT_INDEX','1','TARGET']
assert lines[8]=='CERTIFICATE' and lines[15:] == ['RESIDUAL','0']
R,a,u,v,tau=ring('a,u,v,tau',QQ)
def parse(s):
    return R.from_expr(S.sympify(s.replace('^','**')))
target=parse(lines[7])
assert target.is_ground and target!=0
inverse=QQ.one/target[(0,0,0,0)]
mult=[parse(line)*inverse for line in lines[9:15]]
gens=[parse(p) for p in data['residuals']]
minpoly=parse(data['minpoly'])
comb=sum(c*f for c,f in zip(mult,gens))-1
quotient,remainder=divmod(comb,minpoly)
assert remainder==0
field_multiplier=-quotient
assert sum(c*f for c,f in zip(mult,gens))+field_multiplier*minpoly==1
certificate={'status':'PASS exact QQ polynomial identity',
             'scope':'Equal-D B-rank-one boundary with sum(R)=-'+str(which)+'/2 only. '
                     'The other cubic branch and generic B-rank-one case are separate.',
             'source_input_sha256':hashlib.sha256((base/f'{prefix}-input.json').read_bytes()).hexdigest(),
             'native_stdout_sha256':hashlib.sha256(raw).hexdigest(),
             'variables':['a','u','v','tau'],'target':1,
             'field_relation':str(minpoly),'residual_generators':list(map(str,gens)),
             'multipliers':list(map(str,mult)),'field_multiplier':str(field_multiplier),
             'multiplier_terms':[len(c) for c in mult],
             'field_multiplier_terms':len(field_multiplier),
             'seconds':time.monotonic()-start}
out=base/f'trace-Bone-equal-D-{which}-certificate.json'
out.write_text(json.dumps(certificate,indent=2)+'\n')
print(json.dumps({'status':certificate['status'],'seconds':certificate['seconds'],
                  'bytes':out.stat().st_size,'multiplier_terms':certificate['multiplier_terms'],
                  'field_multiplier_terms':len(field_multiplier)}),flush=True)
