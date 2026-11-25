from pathlib import Path
import ast, hashlib, json, re
from collections import Counter

b=Path('/tmp/oec/pequalnp-pilot-75/finite')
summary=json.loads((b/'conjecture-run-outcomes.json').read_text())
cases=summary['cases']
assert len(cases)==50 and len({r['prefix'] for r in cases})==50
counts=Counter()
for r in cases:
    prefix=r['prefix'];meta=json.loads((b/(prefix+'.json')).read_text())
    wrapper=(b/(prefix+'.log')).read_text()
    solver=(b/(prefix+'.solver.log')).read_text()
    assert re.findall(r'^s .+$',solver,re.M)==r['solver_status']
    outcomes=re.findall(r'^RESULT (\d+) SECONDS ([0-9.]+)$',wrapper,re.M)
    assert len(outcomes)==1 and int(outcomes[0][0])==r['exit'] and float(outcomes[0][1])==r['wrapper_seconds']
    statuses=re.findall(r'^STATUS (.+)$',wrapper,re.M)
    assert len(statuses)==1 and ast.literal_eval(statuses[0])==r['solver_status']
    limits=re.findall(r"setting time limit to (\d+) seconds real time \(due to '-t (\d+)'\)",solver)
    assert limits==[(str(r['native_limit_seconds']),str(r['native_limit_seconds']))]
    for key in ['graph','K','n','edges','rows','ordered','cnf_sha256']: assert meta[key]==r[key]
    digest=lambda name:hashlib.sha256((b/name).read_bytes()).hexdigest()
    assert digest(prefix+'.cnf')==r['cnf_sha256'] and digest(r['source'])==r['source_sha256']
    graph=list(map(int,(b/r['graph']).read_text().split()))
    assert graph[:2]==[r['n'],len(r['edges'])]
    assert list(map(list,zip(graph[2::2],graph[3::2])))==r['edges']
    if r['status']=='SAT':
        assert r['exit']==10 and r['solver_status']==['s SATISFIABLE']
    elif r['status']=='UNSAT':
        assert r['exit']==20 and r['solver_status']==['s UNSATISFIABLE']
    else:
        assert r['status']=='UNKNOWN_TIME_LIMIT' and r['exit']==0 and r['solver_status']==[]
        assert r['wrapper_seconds']>=r['native_limit_seconds']-1
        elapsed=re.findall(r'^c total real time since initialization:\s+([0-9.]+)\s+seconds$',solver,re.M)
        assert len(elapsed)==1 and float(elapsed[0])>=r['native_limit_seconds']-1
        assert solver.rstrip().endswith('c exit 0') and re.search(r'^c UNKNOWN$',solver,re.M)
    counts[r['kind'],r['status']]+=1
    print(prefix,r['status'],'RECORD_PASS')
for kind in ('source','oracle'):
    observed={status:counts[kind,status] for status in ('SAT','UNSAT','UNKNOWN_TIME_LIMIT')}
    assert observed==summary[kind+'_counts']
    print(kind,observed)
specs=json.loads((b/'source-unicycle7-specifications.json').read_text())
assert len(specs)==5
for r in specs:
    n,E=r['n'],r['edges']
    covers=[s for s in range(1<<n) if all((s>>a&1) or (s>>c&1) for a,c in E)]
    assert r['cover_mask'] in covers
    assert r['tau']==r['cover_mask'].bit_count()==min(s.bit_count() for s in covers)
    assert r['K']==len(E)+r['tau']-1
print('ALL_50_RECORDS_PASS; source batch/CNF review separate from oracle encoding review')
