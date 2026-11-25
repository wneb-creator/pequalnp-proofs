from pathlib import Path
from datetime import datetime
import json,hashlib,re,difflib

base=Path(__file__).resolve().parents[1]/'search/not-or-witness'
expected='2481b2a743d4098e12c087bd607876201a1bad463dc6f5e341312f2f978aa648'
assert hashlib.sha256((base/'manifest.json').read_bytes()).hexdigest()==expected
manifest=json.loads((base/'manifest.json').read_text());assert len(manifest)==60
assert {p.relative_to(base).as_posix() for p in base.rglob('*') if p.is_file()}==set(manifest)|{'manifest.json'}
for name,record in manifest.items():
    data=(base/name).read_bytes();assert len(data)==record['bytes'] and hashlib.sha256(data).hexdigest()==record['sha256']
assert manifest['copy_search_first_prooftrace.cpp']['sha256']=='b66739a56db722c470d02767c15b3e812f727546268d706df4a14c4442e8c021'
for old,new,patch,a,b in [('copy_search_first_prooftrace.cpp','notor_search.cpp','adapter.patch','reviewed-copy-search','isolated-notor-witness'),('notor_search.cpp','notor_search_full.cpp','full-coverage.patch','reviewed-notor-witness','full-positive-row-coverage')]:
    generated=''.join(difflib.unified_diff((base/old).read_text().splitlines(True),(base/new).read_text().splitlines(True),fromfile=a,tofile=b,n=1))
    assert generated==(base/patch).read_text()
summary=json.loads((base/'summary.json').read_text());assert len(summary)==7
case_report=[]
for rec in summary:
    folder=base/rec['case'];cmd=json.loads((folder/'command.json').read_text());status=json.loads((folder/'status.json').read_text())
    assert all(status[k]==v for k,v in cmd.items()) and status['exit_code']==rec['exit_code']==0
    assert status['wall_seconds']==rec['wall_seconds'] and abs((datetime.fromisoformat(status['ended_utc'])-datetime.fromisoformat(status['started_utc'])).total_seconds()-status['wall_seconds'])<0.1
    full=rec['case'].startswith('full-');source='notor_search_full.cpp' if full else 'notor_search.cpp'
    assert cmd['source_sha256']==manifest[source]['sha256'] and cmd['matrix_sha256']==manifest['rectangles-v3.txt']['sha256']
    args=cmd['command'];assert args[args.index('--cap')+1]=='19' and args[args.index('--seconds')+1]==('180' if full else '120')
    assert '--memo-in' not in args and '--memo-out' not in args and '--proof-trace' not in args
    retained=rec['case'].endswith('retained');assert ('--consume-or' in args)==(not retained)
    assert cmd['cpu']==4 and cmd['address_limit']==1000000000
    text=(folder/'stdout.txt').read_text();assert not (folder/'stderr.txt').read_bytes()
    assert bool('limit reached' in text)==rec['limit']
    assert bool('heuristic finished found=0' in text)==rec['heuristic_tree_finished']
    assert 'CANDIDATE' not in text and 'found=1' not in text and not (folder/'candidate.json').exists()
    assert not rec['candidate'] and 'independent_replay' not in status
    assert int(re.findall(r'(?:^|\s)nodes=(\d+)',text)[-1])==rec['nodes']
    assert f'keep_or={int(retained)} total_cap=19 remaining=17 root_count={12 if retained else 11}' in text
    assert 'prefix_shortcut=disabled' in text and 'prefix_formula_cuts=0' in text
    case_report.append(rec)
assert sum(r['limit'] for r in summary)==6 and sum(r['heuristic_tree_finished'] for r in summary)==1
for name,cases in [('cases-status.json',summary[:4]),('full-cases-status.json',summary[4:])]:
    stored=json.loads((base/name).read_text());assert stored==[json.loads((base/r['case']/'status.json').read_text()) for r in cases]
edges=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
inputs=[sum(1<<r for r in range(1024) if r>>i&1) for i in range(10)];target=0;fullmask=(1<<1024)-1
for a,b in edges:target|=inputs[a]&inputs[b]
controls=[]
for name in ['selftest-oredge','selftest-ornonedge','selftest-full-oredge','selftest-full-ornonedge']:
    e=json.loads((base/(name+'.json')).read_text());gates=e['gates'];values=inputs.copy()
    assert gates[:2]==[[1,0,e['first_b']],[2,10,10]] and sum(d==2 for d,a,b in gates)==1
    for d,a,b in gates:
        assert d in (0,1,2) and 0<=a<len(values) and 0<=b<len(values)
        values.append(values[a]&values[b] if d==0 else values[a]|values[b] if d==1 else fullmask^values[a])
    assert values==[int(x,16) for x in e['values']] and values[e['output']]==target
    assert 19<len(gates)<=e['cap']==22
    d,a,b=gates[e['output']-10];assert d==1
    assert (values[a]|values[b])&~target==0 and values[a]&~values[b] and values[b]&~values[a]
    assert all(e[k]==1 for k in ['exact1024','final_or','sound_operands','incomparable'])
    text=(base/(name+'.stdout.txt')).read_text();assert not (base/(name+'.stderr.txt')).read_bytes()
    assert f'CANDIDATE gates={len(gates)} output={e["output"]} exact1024=1 bounded=1' in text
    assert f'CANDIDATE gates={len(gates)} output={e["output"]} exact1024=1 bounded=0' in text
    assert 'CANDIDATE SELFTEST PASS' in text
    controls.append(dict(name=name,physical_gates=len(gates),not_gates=1,all_1024_rows=True,rejected_at_cap19=True))
for name in ['compile.stdout.txt','compile.stderr.txt','compile-full.stdout.txt','compile-full.stderr.txt','cases-supervisor.stderr.txt','full-cases-supervisor.stderr.txt']:assert not (base/name).read_bytes()
print(json.dumps(dict(verdict='PASS',manifest_sha256=expected,files=len(manifest),exact_source_deltas=True,runs=case_report,controls=controls,scope='Bounded heuristic witness-search preservation only. No accepted19gate candidate; six limits and one completed heuristic tree do not prove UNSAT. Full decoded controls have21/22gates and are not counterexamples.'),indent=2))
