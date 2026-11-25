from pathlib import Path
import hashlib
import json
import resource
import time
import sympy as S
from sympy.polys.rings import ring
from sympy.polys.domains import QQ

resource.setrlimit(resource.RLIMIT_AS,(256*2**20,256*2**20))
resource.setrlimit(resource.RLIMIT_CPU,(30,35))
start=time.monotonic()
base=Path('/tmp/oec/pequalnp-pilot-78/geometry_search/rowzero')
a,x,y,u,v,tau=S.symbols('a x y u v tau')
R,yr,xr,ur,vr,tr=ring('y,x,u,v,tau',QQ)
report={'status':'PASS','scope':'Independent exact comparison of each primitive-element field map and all six residuals against the original ordered-root quotient. No generic B-rank-one conclusion.',
        'branches':{}}
for which in [7,9]:
    lp=base/f'trace-Bone-equal-D-linear-{which}.json'
    np=base/f'trace-Bone-equal-D-{which}-lift-input.json'
    cp=base/f'trace-Bone-equal-D-{which}-certificate.json'
    linear=json.loads(lp.read_text());native=json.loads(np.read_text());certificate=json.loads(cp.read_text())
    assert native['source_sha256']==hashlib.sha256(lp.read_bytes()).hexdigest()
    assert certificate['source_input_sha256']==hashlib.sha256(np.read_bytes()).hexdigest()
    relations=[R.from_expr(S.sympify(linear['field_relations'][i])) for i in [1,0]]
    def red(p):return p.div(relations)[1]
    powers=[R.one]
    for i in range(6):powers.append(red(powers[-1]*(xr+2*yr)))
    def evaluate(expression):
        result=R.zero
        for monomial,c in S.Poly(S.sympify(expression),a,u,v,tau).terms():
            result+=QQ(int(c.p),int(c.q))*powers[monomial[0]]*ur**monomial[1]*vr**monomial[2]*tr**monomial[3]
        return red(result)
    assert evaluate(native['minpoly'])==0
    assert evaluate(native['x'])==xr
    assert evaluate(native['y'])==yr
    assert native['residual_indices']==[r['index'] for r in linear['residuals']]
    for new,old in zip(native['residuals'],linear['residuals']):
        assert evaluate(new)==red(R.from_expr(S.sympify(old['polynomial'])))
    report['branches'][str(which)]={
        'ordered_root_source_sha256':hashlib.sha256(lp.read_bytes()).hexdigest(),
        'primitive_input_sha256':hashlib.sha256(np.read_bytes()).hexdigest(),
        'certificate_sha256':hashlib.sha256(cp.read_bytes()).hexdigest(),
        'primitive_minpoly_vanishes_in_ordered_root_quotient':True,
        'inverse_x_and_y_maps_exact':True,'all_six_residuals_match':True}
report['seconds']=time.monotonic()-start
(base/'equal-D-field-maps-independent-audit.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report),flush=True)
