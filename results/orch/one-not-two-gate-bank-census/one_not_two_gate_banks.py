from pathlib import Path
import json, itertools, time, hashlib

base = Path('/tmp/oec/pequalnp-pilot-87/status_review/one-not-two-gate-banks')
base.mkdir(exist_ok=True)
source = Path('/workspace/pequalnp-proofs/results/orch/weak20369-generation/complete-fixture-20369.json')
autos = json.loads(source.read_text())['header']['automorphisms']
edges = [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
edge_set = {tuple(sorted(e)) for e in edges}
def graph(r): return any((r >> a) & (r >> b) & 1 for a,b in edges)
assert len(autos) == len(set(map(tuple,autos))) == 120
for p in autos:
    assert sorted(p)==list(range(10))
    assert {tuple(sorted((p[a],p[b]))) for a,b in edges} == edge_set
remaining = {(a,b,c) for a,b in itertools.combinations(range(10),2) for c in range(10) if c not in (a,b)}
orbits=[]
while remaining:
    a,b,c = min(remaining)
    orb={tuple(sorted((p[a],p[b])))+(p[c],) for p in autos}
    assert orb <= remaining
    remaining -= orb
    orbits.append(((a,b,c),len(orb)))
positive=[r for r in range(1024) if graph(r)]
negative=[r for r in range(1024) if not graph(r)]
full=(1<<1024)-1
inputs=[sum(((r>>j)&1)<<r for r in range(1024)) for j in range(10)]
cases=[]; starts=[]; started=time.monotonic()
for kind in ['OR_OR','AND_OR']:
    for orbit,(abc,size) in enumerate(orbits):
        a,b,c=abc
        g=(inputs[a]|inputs[b]) if kind=='OR_OR' else(inputs[a]&inputs[b])
        h=g|inputs[c]
        words=inputs+[g,h,full^h]
        rows=[sum(((v>>r)&1)<<j for j,v in enumerate(words)) for r in range(1024)]
        raw_clauses={}
        for p in positive:
            for n in negative:
                diff=rows[p]&~rows[n]
                if diff & (1<<12): continue
                mask=diff&4095
                assert mask
                raw_clauses.setdefault(mask,(p,n))
        clauses=[]
        for mask in sorted(raw_clauses,key=lambda m:(m.bit_count(),m)):
            if not any((c&mask)==c for c in clauses):clauses.append(mask)
        valid=[all(m&c for c in clauses) for m in range(4096)]
        minima=[m for m in range(4096) if valid[m] and all(not valid[m^(1<<j)] for j in range(12) if m>>j&1)]
        forced=4095
        for m in minima:forced&=m
        case=dict(kind=kind,orbit=orbit,variables=abc,orbit_size=size,first_pair_edge=(a,b)in edge_set,
                  minimal_clauses=[dict(mask=m,positive=raw_clauses[m][0],negative=raw_clauses[m][1]) for m in clauses],
                  minima=[dict(optional_mask=m,inputs=[j for j in range(10)if m>>j&1],intermediate=bool(m>>10&1),source=bool(m>>11&1),root_count=m.bit_count()+1)for m in minima],
                  forced_inputs=[j for j in range(10)if forced>>j&1],valid_banks=sum(valid))
        cases.append(case)
        for m in range(4096):
            if not valid[m]:continue
            selected=m|(1<<12)
            starts.append(dict(kind=kind,orbit=orbit,variables=abc,optional_mask=m,
                bank=[hex(words[j])for j in range(13)if selected>>j&1],
                root_positions=[j for j in range(13)if selected>>j&1],suffix_positive_budget=16,
                prefix=[dict(kind='OR'if kind=='OR_OR'else'AND',left=a,right=b,output=10),dict(kind='OR',left=10,right=c,output=11),dict(kind='NOT',input=11,output=12)],
                positive_supply_history=[dict(op=1 if kind=='OR_OR' else 0,left=hex(inputs[a]),right=hex(inputs[b]),output=hex(g)),dict(op=1,left=hex(g),right=hex(inputs[c]),output=hex(h))],
                negative_seed_values=[hex(full^h)]))
        print(kind,orbit,abc,size,'pair_edge',(a,b)in edge_set,'forced',case['forced_inputs'],'minima',[(x['inputs'],x['intermediate'],x['source'])for x in case['minima']],'banks',sum(valid),flush=True)
scope='Exhaustive row-order separation of positive suffix inputs, with the negative source retained. Distinct original a,b,c only. No bounded-gate feasibility or family exclusion is claimed; all valid supersets remain separate Live banks.'
result=dict(scope=scope,fixture_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),root_positions='0..9 original inputs;10 intermediate g;11 source h;12 NOT h',positive_rows=len(positive),negative_rows=len(negative),orbits_per_family=len(orbits),cases_per_family=sum(n for _,n in orbits),cases=cases,seconds=time.monotonic()-started)
(base/'census.json').write_text(json.dumps(result,indent=2)+'\n')
(base/'starts.json').write_text(json.dumps(dict(scope=scope,starts=starts),indent=2)+'\n')
print('DONE',len(cases),'orbit-families',len(starts),'valid banks',result['seconds'],flush=True)
