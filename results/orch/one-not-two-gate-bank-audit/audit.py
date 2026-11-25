from pathlib import Path
import itertools,json,hashlib,sys
directory=Path(sys.argv[1]);source=directory/'census.json';data=json.loads(source.read_text())
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
positive=[r for r in range(1024)if graph(r)];negative=[r for r in range(1024)if not graph(r)]
full=(1<<1024)-1;inputs=[sum(((r>>i)&1)<<r for r in range(1024))for i in range(10)]
allcases={(a,b,c)for a,b in itertools.combinations(range(10),2)for c in range(10)if c not in(a,b)}
covered={k:set()for k in ['OR_OR','AND_OR']};expected={};checks=0;witnesses=0;minimum_count=0
for item in data['cases']:
    kind=item['kind'];a,b,c=item['variables'];rep=(a,b,c)
    orbit={tuple(sorted((g[a],g[b])))+(g[c],)for g in autos}
    assert len(orbit)==item['orbit_size']and not(orbit&covered[kind])and rep==min(orbit)
    covered[kind]|=orbit
    g=inputs[a]|inputs[b]if kind=='OR_OR'else inputs[a]&inputs[b];h=g|inputs[c]
    words=inputs+[g,h,full^h]
    rows=[sum(((v>>r)&1)<<j for j,v in enumerate(words))for r in range(1024)]
    clauses=[]
    for w in item['minimal_clauses']:
        p,n=w['positive'],w['negative'];diff=rows[p]&~rows[n]
        assert p in positive and n in negative and not(diff&4096)
        assert(diff&4095)==w['mask']and w['mask']>0
        clauses.append(w['mask']);witnesses+=1
    possible=[m for m in range(4096)if all(m&c for c in clauses)]
    minima=[m for m in possible if all((m^(1<<j))not in possible for j in range(12)if(m>>j)&1)]
    assert minima==[b['optional_mask']for b in item['minima']]and len(possible)==item['valid_banks']
    forced=4095
    for record in item['minima']:
        m=record['optional_mask'];bank=m|4096;forced&=m
        assert record['root_count']==bank.bit_count()
        assert record['inputs']==[i for i in range(10)if(m>>i)&1]
        assert record['intermediate']==bool(m&1024)and record['source']==bool(m&2048)
        for p in positive:
            for n in negative:
                assert(rows[p]&~rows[n])&bank
                checks+=1
        minimum_count+=1
    assert item['forced_inputs']==[i for i in range(10)if(forced>>i)&1]
    for m in possible:expected[(kind,item['orbit'],m)]=(rep,words)
assert all(v==allcases for v in covered.values())and len(allcases)==360
starts=json.loads((directory/'starts.json').read_text())['starts'];seen=set()
for st in starts:
    key=(st['kind'],st['orbit'],st['optional_mask']);assert key not in seen;seen.add(key)
    rep,words=expected[key];a,b,c=rep
    assert tuple(st['variables'])==rep and st['suffix_positive_budget']==16
    mask=st['optional_mask']|4096
    assert st['root_positions']==[j for j in range(13)if(mask>>j)&1]
    assert [int(v,16)for v in st['bank']]==[words[j]for j in st['root_positions']]
    assert st['negative_seed_values']==[hex(words[12])]
    assert st['prefix']==[dict(kind='OR'if key[0]=='OR_OR'else'AND',left=a,right=b,output=10),dict(kind='OR',left=10,right=c,output=11),dict(kind='NOT',input=11,output=12)]
    hist=st['positive_supply_history']
    assert hist==[dict(op=1 if key[0]=='OR_OR'else 0,left=hex(words[a]),right=hex(words[b]),output=hex(words[10])),dict(op=1,left=hex(words[10]),right=hex(words[c]),output=hex(words[11]))]
assert seen==set(expected)and len(seen)==52
priority=json.loads((directory/'priority-starts.json').read_text())['starts']
assert len(priority)==8 and all(st in starts for st in priority)
assert all(not(st['optional_mask']&1024)for st in priority if st['kind']=='AND_OR')
print(json.dumps(dict(verdict='PASS_EXACT_TWO_GATE_PREFIX_CENSUS',hashes={n:hashlib.sha256((directory/n).read_bytes()).hexdigest()for n in ['census.json','starts.json','priority-starts.json']},automorphisms=120,orbits_per_family=6,configurations_per_family=360,clause_witnesses=witnesses,minimal_banks=minimum_count,full_row_checks=checks,all_valid_starts=52,selected_starts=8,scope='Exact row-order bank census and physical prefix/root truth-table validation only. Eight starts are selected, not exhaustive; no circuit search or gate-bound claim.'),indent=2))
