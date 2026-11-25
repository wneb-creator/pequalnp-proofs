import itertools
import json
import math
import resource
import time
from pathlib import Path

resource.setrlimit(resource.RLIMIT_AS, (512 * 2**20, 512 * 2**20))
resource.setrlimit(resource.RLIMIT_CPU, (45, 47))
from sympy import QQ
from sympy.polys.rings import ring

start=time.monotonic()
base=Path('/tmp/oec/pequalnp-pilot-78/numeric')
out=base/'artifact-analysis'
R,*xs=ring(','.join('x'+str(i) for i in range(18)),QQ,order='grevlex')
coords=[(i,j) for i in range(4) for j in range(i,4)]
lookup={pair:i for i,pair in enumerate(coords)}
edges=[(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]
edge_index={pair:i for i,pair in enumerate(edges)}
U=[[R.zero for _ in range(3)] for _ in range(10)]
for i in range(3): U[lookup[(i,i)]][i]=R.one
for i,edge in enumerate(edges): U[lookup[edge]]=xs[3*i:3*i+3]
for j in range(3): U[lookup[(3,3)]][j]=-R.one-2*sum((U[lookup[edge]][j] for edge in edges),R.zero)

# Independent convolution expansion over the four matrix rows.
raw={}
for pi in itertools.permutations(range(4)):
    product={(0,0,0):R.one}
    for i in range(4):
        row=U[lookup[tuple(sorted((i,pi[i])))]]
        next_product={}
        for exp,p in product.items():
            next_product[exp]=next_product.get(exp,R.zero)+p
            for j,factor in enumerate(row):
                shifted=tuple(value+(k==j) for k,value in enumerate(exp))
                next_product[shifted]=next_product.get(shifted,R.zero)+p*factor
        product=next_product
    for exp,p in product.items(): raw[exp]=raw.get(exp,R.zero)+p
assert raw[(0,0,0)]==R(24)
assert all(raw[exp]==0 for exp in raw if sum(exp)==1)
exps=[exp for degree in range(2,5) for exp in itertools.product(range(degree+1),repeat=3) if sum(exp)==degree]
coeff=[raw[exp] for exp in exps]
assert len(coeff)==31 and all(coeff)

# Check the actual source's generation prefix without running its solver.
source=(base/'groebner_probe.py').read_text()
source=source[:source.index("print(json.dumps({'stage':'generated'")]
source=source.replace('resource.setrlimit(resource.RLIMIT_AS,(1536*2**20,1536*2**20))','')
source=source.replace('resource.setrlimit(resource.RLIMIT_CPU,(30,35))','')
import sys
sys.argv=['audit','0,4,7','0']
ns={}
exec(compile(source,'groebner_probe_generation_only','exec'),ns)
assert all(dict(raw[e])==dict(ns['coeff'][e]) for e in raw)

def exponent_action(exp,mapping):
    result=[0]*len(exp)
    for i,target in enumerate(mapping): result[target]=exp[i]
    return tuple(result)

def cycles(mapping):
    unseen=set(range(len(mapping)))
    lengths=[]
    while unseen:
        first=min(unseen)
        j=first
        n=0
        while j in unseen:
            unseen.remove(j)
            n+=1
            j=mapping[j]
        assert j==first
        lengths.append(n)
    return sorted(lengths)

def invariant_monomials(lengths,maximum):
    counts=[1]+[0]*maximum
    for length in lengths:
        for degree in range(length,maximum+1): counts[degree]+=counts[degree-length]
    return [sum(counts[:i+1]) for i in range(maximum+1)]

maps=[]
for pi in itertools.permutations(range(3)):
    vertex=pi+(3,)
    variable=[]
    for edge in edges:
        target_edge=tuple(sorted(vertex[i] for i in edge))
        variable.extend(3*edge_index[target_edge]+pi[j] for j in range(3))
    generators=[exps.index(exponent_action(exp,pi)) for exp in exps]
    monic_scalars=[]
    for index,p in enumerate(coeff):
        transformed={exponent_action(mon,variable):value for mon,value in p.items()}
        target=coeff[generators[index]]
        assert transformed==dict(target)
        factor=target.LC/p.LC
        transformed_monic={mon:value/p.LC for mon,value in transformed.items()}
        assert transformed_monic=={mon:value*factor/target.LC for mon,value in target.items()}
        monic_scalars.append(str(factor))
    lengths=cycles(variable)
    fixed_generators={str(degree):sum(generators[i]==i for i,exp in enumerate(exps) if sum(exp)==degree) for degree in range(2,5)}
    maps.append({'vertex_permutation':pi,'variable_map':variable,'generator_map':generators,'monic_scalars':monic_scalars,'variable_cycle_lengths':lengths,'fixed_generators_by_degree':fixed_generators,'fixed_monomials_up_to_degree':invariant_monomials(lengths,6)})

degree_counts=[]
for maximum in [5,6]:
    fixed_rows=[]
    fixed_columns=[]
    for mapping in maps:
        fixed_rows.append(sum(mapping['fixed_generators_by_degree'][str(degree)]*mapping['fixed_monomials_up_to_degree'][maximum-degree] for degree in range(2,5)))
        fixed_columns.append(mapping['fixed_monomials_up_to_degree'][maximum])
    assert sum(fixed_rows)%6==sum(fixed_columns)%6==0
    degree_counts.append({'degree_bound':maximum,'raw_rows':sum(math.comb(degree+2,2)*math.comb(18+maximum-degree,maximum-degree) for degree in range(2,5)),'row_orbits':sum(fixed_rows)//6,'fixed_rows':fixed_rows,'raw_columns':math.comb(18+maximum,maximum),'column_orbits':sum(fixed_columns)//6,'fixed_columns':fixed_columns})

report={'status':'PASS','chart':[0,4,7],'variable_order':[{'name':'x'+str(3*i+j),'edge':edge,'parameter':j} for i,edge in enumerate(edges) for j in range(3)],'generator_order':[{'index':i,'parameter_exponent':exp,'degree':max(sum(mon) for mon in p),'terms':len(p)} for i,(exp,p) in enumerate(zip(exps,coeff))],'exact_polynomial_equalities':6*31,'source_coefficients_compared':len(raw),'maps':maps,'counts':degree_counts,'seconds':time.monotonic()-start,'peak_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'scope':'combinatorial orbit counts only; no matrix elimination, certificate, or ideal-emptiness conclusion; Reynolds averaging requires characteristic not 2 or 3'}
(out/'chart047-s3-audit.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({key:report[key] for key in ['status','exact_polynomial_equalities','source_coefficients_compared','counts','seconds','peak_rss_kib']},sort_keys=True))
print('monic scalar values:',sorted({factor for mapping in maps for factor in mapping['monic_scalars']}))
