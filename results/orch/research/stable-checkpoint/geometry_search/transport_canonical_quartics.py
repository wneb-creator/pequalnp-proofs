from pathlib import Path
from fractions import Fraction
from math import factorial
import hashlib,json,resource,time
import sympy as S
from sympy.polys.rings import ring
from sympy.polys.domains import QQ

resource.setrlimit(resource.RLIMIT_AS,(512*2**20,512*2**20))
resource.setrlimit(resource.RLIMIT_CPU,(120,125))
start=time.monotonic()
base=Path('/tmp/oec/pequalnp-pilot-78')
out=base/'geometry_search/transported_quartics'
out.mkdir(exist_ok=True)
paths={'chart':base/'numeric/s4-hadamard/chart.json',
       'rowmap':base/'numeric/s4-structure/rational-id-rowmap.json',
       'certificates':base/'numeric/s4-augmented/reduced-certificates.jsonl',
       'full31':base/'geometry_search/tracezero_rankdrop/full31-shifted.json'}
chart=json.loads(paths['chart'].read_text())
rm=json.loads(paths['rowmap'].read_text())
certs=[json.loads(x) for x in paths['certificates'].read_text().splitlines() if x]
full=json.loads(paths['full31'].read_text())
R,*vs=ring(','.join(full['variables']),QQ)
p0,p1,p2,p3,p4,p5,b0,b1,b2,b3,k,l,w0,w1,w2,w3,w4,w5=vs
subs=[p0-k*w0+3,p1-l*w0,w0,
      p2-k*w1,p3-l*w1+3,w1,
      p4-k*w2,p5-l*w2,w2+3,
      b0-k*w3,b1-l*w3,w3,
      b2-k*w4,b3-l*w4,w4,
      -b0-b2-k*w5,-b1-b3-l*w5,w5]
locals={str(v):S.Symbol(str(v)) for v in vs}
actual=[R.from_expr(S.sympify(x,locals=locals))*QQ(str(c))
        for x,c in zip(full['generators'],full['scales_to_actual_permanent_coefficients'])]
cache={():R.one}
def monomial(indices):
    indices=tuple(indices)
    if indices not in cache:
        cache[indices]=monomial(indices[:-1])*subs[indices[-1]]
    return cache[indices]
def transport(encoded):
    answer=R.zero
    for indices,c in encoded:
        answer+=QQ(str(c))*monomial(indices)
    return answer
sourcegens=[{tuple(m):Fraction(c) for m,c in g} for g in chart['polynomials']]
transgens=[transport(g) for g in chart['polynomials']]
relations=[]
for i,a in enumerate(chart['parameter_exponents']):
    expected=R.zero
    row=[]
    degree=sum(a)
    factor=QQ(8**degree,int(chart['degree_divisors'][str(degree)]))
    for j,b in enumerate(full['parameter_exponents']):
        ds,dt=a[0]-b[0],a[1]-b[1]
        if sum(b)!=degree or ds<0 or dt<0 or a[2]>b[2] or ds+dt+a[2]!=b[2]:continue
        mult=factor*QQ(factorial(b[2]),factorial(ds)*factorial(dt)*factorial(a[2]))*(-k)**ds*(-l)**dt
        expected+=mult*actual[j]
        row.append([j,str(mult)])
    assert expected==transgens[i],i
    relations.append(row)
results=[]
for ci,c in enumerate(certs):
    target={tuple(rm['columns'][col]):Fraction(a) for col,a in c['polynomial']}
    rebuilt={}
    for oi,a in c['certificate']:
        gi,m=rm['rows'][rm['order'][oi]]
        for n,b in sourcegens[gi].items():
            key=tuple(sorted(tuple(m)+n))
            rebuilt[key]=rebuilt.get(key,Fraction(0))+Fraction(a)*b
            if not rebuilt[key]:del rebuilt[key]
    assert rebuilt==target,ci
    mapped=transport(list(target.items()))
    # Independent multiplication after substitution checks the certificate
    # against the transported original generators, not only canonical data.
    direct=R.zero
    for oi,a in c['certificate']:
        gi,m=rm['rows'][rm['order'][oi]]
        direct+=QQ(str(a))*monomial(m)*transgens[gi]
    assert direct==mapped,ci
    degree=max((sum(m) for m in mapped),default=0)
    results.append({'index':ci,'canonical_terms':len(target),'degree':degree,
                    'terms':len(mapped),'polynomial':str(mapped),
                    'encoded_terms':[[list(m),str(a)] for m,a in sorted(mapped.items())]})
    print(json.dumps({'index':ci,'degree':degree,'terms':len(mapped),
                      'seconds':time.monotonic()-start}),flush=True)
report={'status':'PASS','variables':full['variables'],
        'canonical_variable_substitutions':list(map(str,subs)),
        'basis_change':'U=A-k*W,V=B-l*W,W=W; hence old parameters (s,t,z) map to (s,t,z-k*s-l*t)',
        'all31_generator_basis_change_relations_verified':True,
        'all24_original_and_transported_certificates_verified':True,
        'relations_to_actual_full31_coefficients':relations,
        'sources':{key:{'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for key,p in paths.items()},
        'polynomials':results,'seconds':time.monotonic()-start,
        'scope':'Exact necessary polynomial consequences in the shifted tracezero chart. These identities do not establish infeasibility; no Lean theorem or full-gap result is claimed.'}
(out/'transported.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'status':'PASS','polynomials':len(results),'total_terms':sum(x['terms'] for x in results),'seconds':report['seconds']}),flush=True)
