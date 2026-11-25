from pathlib import Path
import itertools,json,hashlib,sys
source=Path(sys.argv[1]);data=json.loads(source.read_text())
edges={(0,1),(1,2),(2,3),(3,4),(0,4),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(6,9),(6,8),(5,8)}
def adjacent(a,b):return tuple(sorted((a,b)))in edges
def graph(r):return any((r&(1<<a))and(r&(1<<b))for a,b in edges)
# Independently enumerate every adjacency-preserving bijection, pruning fixed prefixes.
autos=[]
def extend(p,unused):
    if not unused:autos.append(tuple(p));return
    i=len(p)
    for j in sorted(unused):
        if all(adjacent(i,k)==adjacent(j,p[k])for k in range(i)):
            extend(p+[j],unused-{j})
extend([],set(range(10)))
assert len(autos)==120
pairs=list(itertools.combinations(range(10),2));allcases=set(itertools.combinations(pairs,2));covered=set()
positive=[r for r in range(1024)if graph(r)];negative=[r for r in range(1024)if not graph(r)]
assert(len(positive),len(negative))==(948,76)
checks=0;witnesses=0;bank_records=0;summary=[]
for item in data['cases']:
    rep=tuple(tuple(v)for v in item['pairs'])
    orbit={tuple(sorted(tuple(sorted((g[a],g[b])))for a,b in rep))for g in autos}
    assert len(orbit)==item['orbit_size']and not(orbit&covered)and rep==min(orbit)
    covered|=orbit
    sig=[]
    for r in range(1024):
        hs=[int(bool(r&(1<<a)or r&(1<<b)))for a,b in rep]
        sig.append(r+(hs[0]<<10)+(hs[1]<<11)+((1-hs[0])<<12)+((1-hs[1])<<13))
    for mode,pat in enumerate(item['patterns']):
        assert pat['negatives_retained']==[j for j in range(2)if(mode>>j)&1]
        fixed=mode<<12
        clauses=[]
        for w in pat['minimal_clauses']:
            p,n=w['positive'],w['negative'];diff=sig[p]&~sig[n]
            assert p in positive and n in negative and not(diff&fixed)
            assert(diff&4095)==w['mask']and w['mask']>0
            clauses.append(w['mask']);witnesses+=1
        possible=[m for m in range(4096)if all(m&c for c in clauses)]
        minima=[m for m in possible if all((m^(1<<j))not in possible for j in range(12)if(m>>j)&1)]
        assert minima==[b['optional_mask']for b in pat['minimal_banks']]
        assert len(possible)==pat['valid_optional_banks']
        forced=4095
        for b in pat['minimal_banks']:
            m=b['optional_mask'];full=m|fixed;forced&=m
            assert b['root_count']==full.bit_count()
            assert b['inputs']==[i for i in range(10)if(m>>i)&1]
            assert b['positive_sources']==[i for i in range(2)if(m>>(10+i))&1]
            for p in positive:
                for n in negative:
                    assert(sig[p]&~sig[n])&full
                    checks+=1
            bank_records+=1
        assert pat['forced_inputs']==[j for j in range(10)if(forced>>j)&1]
    summary.append(dict(index=item['index'],pairs=item['pairs'],orbit_size=len(orbit),overlap=len(set(rep[0])&set(rep[1])),both_negative_minima=[b['optional_mask']for b in item['patterns'][3]['minimal_banks']]))
assert covered==allcases and len(covered)==990 and len(data['cases'])==17
print(json.dumps(dict(verdict='PASS_EXACT_FINITE_CENSUS',census_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),automorphisms=len(autos),pair_pair_orbits=17,pair_pair_cases=990,negative_patterns=68,witness_clauses=witnesses,minimal_bank_records=bank_records,all_row_checks=checks,cases=summary,scope='Exact orbit and full-row order-separation census, not a gate-bound or circuit-existence result.'),indent=2))
