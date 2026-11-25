import collections
import itertools
import json
import resource
import sys
import time
from pathlib import Path

resource.setrlimit(resource.RLIMIT_AS, (512 * 2**20, 512 * 2**20))
resource.setrlimit(resource.RLIMIT_CPU, (45, 47))
from sympy import QQ
from sympy.polys.rings import ring

started = time.monotonic()
out = Path('/tmp/oec/pequalnp-pilot-78/numeric/artifact-analysis')
R,b,c,d,e,v0,k0,l0,v1,k1,l1 = ring('b,c,d,e,v0,k0,l0,v1,k1,l1',QQ,order='grevlex')
f = -1-b-c-d-e
q = f+b*e+c*d
H,J = c*(f-b)+d*(1-e), b*(f-c)+e*(1-d)
K,L = e*(f-d)+b*(1-c), d*(f-e)+c*(1-b)
rho = [1+b+c,1+d+e,b+d+f,c+e+f]
kap = (b+d)*(c+e)+f
delta = (e-1)*J-(d-1)*H
D = 4*b*d*delta
coords = [(i,j) for i in range(4) for j in range(i,4)]
lookup = {p:k for k,p in enumerate(coords)}

def normal(p):
    return p.rem([q])

def extension(r,u,v,k,l):
    W = -(d*e*f*r+b*c*f*u+c*e*v)
    diags = [b*d*r,b*d*u,b*d*v,W]
    C1 = b*d*(4*(c-1)*k+4*(b-1)*l)-2*sum(((2*ri+1)*di for ri,di in zip(rho,diags)),R.zero)
    C2 = b*d*(2*K*k+2*L*l)+sum(((ri**2-kap)*di for ri,di in zip(rho,diags)),R.zero)
    hn = 2*(d-1)*C2-J*C1
    jn = H*C1-2*(e-1)*C2
    wn = 4*delta*W
    mn = -(D*(r+u+v)+wn)/2-hn-jn-D*(k+l)
    return [normal(p) for p in [D*r,R.zero,hn,jn,D*u,D*k,D*l,D*v,mn,wn]]

C = [R.zero,R.one,b,c,R.zero,d,e,R.zero,f,R.zero]
A,B = extension(R.one,R.zero,v0,k0,l0), extension(R.zero,R.one,v1,k1,l1)
factors = {(kind,k):p for kind,values in enumerate([A,B,C],1) for k,p in enumerate(values)}
templates = collections.defaultdict(collections.Counter)
for pi in itertools.permutations(range(4)):
    cs = [lookup[tuple(sorted((i,pi[i])))] for i in range(4)]
    for choices in itertools.product(range(4),repeat=4):
        degree = tuple(choices.count(k) for k in range(1,4))
        if sum(degree)<2: continue
        key = tuple(sorted((kind,cs[i]) for i,kind in enumerate(choices) if kind))
        if all(factors[keyi] for keyi in key): templates[degree][key] += 1

def info(p):
    return {'terms':len(p),'degree':max((sum(exp) for exp in p),default=-1)}

print(json.dumps({'phase':'setup','seconds':time.monotonic()-started,'q':str(q),'delta':str(delta),'A_entries':[info(p) for p in A],'B_entries':[info(p) for p in B]},sort_keys=True),flush=True)
reports=[]
polynomials=[q]
exponents=sorted(templates,key=lambda x:(sum(x),x[0]+x[1],x))
with (out/'generic10-coefficients.jsonl').open('w') as handle:
    for exp in exponents:
        value=R.zero
        for key,multiplicity in templates[exp].items():
            product=R.one
            for factor in sorted((factors[keyi] for keyi in key),key=len):
                product=normal(product*factor)
            value += multiplicity*product
        value=normal(value)
        if value:
            denominator,integer_poly=value.clear_denoms()
            content,primitive=integer_poly.primitive()
            value=primitive
            polynomials.append(value)
        entry={'exponent':exp,'denominator_power':exp[0]+exp[1],**info(value),'seconds':time.monotonic()-started}
        reports.append(entry)
        handle.write(json.dumps({**entry,'polynomial':str(value)})+'\n')
        handle.flush()
        print(json.dumps(entry,sort_keys=True),flush=True)
    (out/'generic10-unsaturated.ms').write_text(','.join(str(x) for x in R.gens)+'\n0\n'+',\n'.join(str(p).replace('**','^') for p in polynomials)+'\n')
print(json.dumps({'phase':'complete','equations':len(polynomials),'total_terms':sum(len(p) for p in polynomials),'maximum_degree':max(info(p)['degree'] for p in polynomials),'rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'seconds':time.monotonic()-started,'scope':'q retained; equivalence only on b*d*delta != 0; no exceptional branch removed; no Groebner solve'},sort_keys=True),flush=True)
