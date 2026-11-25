from pathlib import Path
from fractions import Fraction
from functools import reduce
from math import gcd,lcm
import hashlib,json

base=Path('/tmp/oec/pequalnp-pilot-78')
out=base/'geometry_search/canonical55'
out.mkdir(exist_ok=True)
cp=base/'numeric/s4-hadamard/chart.json'
rp=base/'numeric/s4-structure/rational-id-rowmap.json'
xp=base/'numeric/s4-augmented/reduced-certificates.jsonl'
chart=json.loads(cp.read_text());rowmap=json.loads(rp.read_text())
certs=[json.loads(x) for x in xp.read_text().splitlines() if x]
variables=chart['variables']
polys=[{tuple(m):Fraction(c) for m,c in g} for g in chart['polynomials']]
normalizations=[]
for cert in certs:
    g={tuple(rowmap['columns'][i]):Fraction(c) for i,c in cert['polynomial']}
    denominator=lcm(*(v.denominator for v in g.values()))
    common=reduce(gcd,(abs(v.numerator*(denominator//v.denominator)) for v in g.values()))
    factor=Fraction(denominator,common)
    polys.append({m:v*factor for m,v in g.items()})
    normalizations.append(str(factor))
def expr(poly):
    terms=[]
    for mon,c in sorted(poly.items()):
        assert c.denominator==1
        monomial='*'.join(variables[i] for i in mon)
        terms.append('('+str(c.numerator)+')'+('*'+monomial if monomial else ''))
    return '+'.join(terms) if terms else '0'
prefix='LIB "modstd.lib";\nring R=0,('+','.join(variables)+'),dp;\noption(redSB);\noption(prot);\n'
suffix='''
print("BEGIN_MODULAR_CANONICAL55");
ideal G=modGB("slimgb",I,1);
print("MODULAR_BASIS_COMPLETE");print("BASIS_SIZE");size(G);print("DIMENSION");dim(G);print("BASIS");short=0;G;
int unitIndex=0;int j;for(j=1;j<=size(G);j++){if(G[j]!=0 && deg(G[j])==0){unitIndex=j;break;}}
print("MODULAR_UNIT_CANDIDATE");(unitIndex!=0);
if(unitIndex!=0){print("EXACT_LIFT_BEGIN");ideal U=1;matrix C=lift(I,U);print("EXACT_IDENTITY_VALID");(matrix(I)*C==matrix(U));int i;for(i=1;i<=nrows(C);i++){print("CERTIFICATE_COEFF");i;print(string(C[i,1]));}print("EXACT_LIFT_COMPLETE");}
print("COMPLETED_EXACT_RUN");quit;
'''
source=out/'canonical55-modGB.sing'
source.write_text(prefix+'ideal I='+','.join(map(expr,polys))+';\n'+suffix)
report={'variables':variables,'generator_count':len(polys),
        'term_counts':list(map(len,polys)),'total_terms':sum(map(len,polys)),
        'degree_counts':{str(d):sum(max(map(len,p))==d for p in polys) for d in [2,3,4]},
        'extra_quartic_scales':normalizations,
        'encoded_generators':[[[list(m),str(c)] for m,c in sorted(p.items())] for p in polys],
        'sources':{str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in [cp,rp,xp]},
        'singular_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
        'scope':'Canonical Hadamard D=identity full-rank-three chart with31 coefficient equations and24 exactly certified degree4 consequences. Modular candidate requires exact rational identity and Lean verification; no conclusion from failure or timeout.'}
(out/'input.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:report[k] for k in ['generator_count','total_terms','degree_counts','singular_sha256']}))
