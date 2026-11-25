from pathlib import Path
import ast,datetime,hashlib,json,re,shutil,sys

base=Path(__file__).parent
repo=Path('/workspace/pequalnp-proofs/results/orch/finite')
cases=[]
def add(kind,graph,k,limit):
    suffix='sources-dirty' if kind=='source' else 'packing-oracle'
    cases.append({'kind':kind,'graph':graph+'.graph','K':k,'native_limit_seconds':limit,'prefix':graph+'-k'+str(k)+'-'+suffix})
for graph,k,limit in [('p4',4,60),('p4',5,60),('p5',5,90),('p6',7,90),('double_star6',6,90),('fork6',7,90),('c5leaf',8,300),('c7',10,300),('theta233',11,300),('theta333',12,300)]:add('source',graph,k,limit)
trees=json.loads((base/'source-tree7-specifications.json').read_text())['graphs']
unicycles=json.loads((base/'source-unicycle7-specifications.json').read_text())
for r in trees:add('source',Path(r['graph']).stem,r['K'],60)
for r in unicycles:add('source',r['name'],r['K'],120)
for graph,k in [('matching2',2),('matching3',4),('p4',3),('p6',6),('c5leaf',7),('c6',7)]:add('oracle',graph,k,120)
for r in trees:add('oracle',Path(r['graph']).stem,r['K']-1,60)
for graph,k in [('c7',9),('theta233',10)]:add('oracle',graph,k,300)
for r in unicycles:add('oracle',r['name'],r['K']-1,90)
assert len(cases)==50
filenames=set()
for r in cases:
    prefix=r['prefix']
    meta=json.loads((base/(prefix+'.json')).read_text())
    log=(base/(prefix+'.log')).read_text()
    result=re.findall(r'^RESULT (\d+) SECONDS ([0-9.]+)$',log,re.M)
    statuses=re.findall(r'^STATUS (.*)$',log,re.M)
    assert len(result)==len(statuses)==1,('unfinished or malformed',prefix)
    r['exit']=int(result[0][0]);r['wrapper_seconds']=float(result[0][1]);r['solver_status']=ast.literal_eval(statuses[0])
    if r['exit']==10:
        assert r['solver_status']==['s SATISFIABLE'];r['status']='SAT'
        witness=json.loads((base/(prefix+'.witness.json')).read_text());assert not witness['failed']
        filenames.add(prefix+'.witness.json')
    elif r['exit']==20:
        assert r['solver_status']==['s UNSATISFIABLE'];r['status']='UNSAT'
    else:
        assert r['exit']==0 and not r['solver_status'];r['status']='UNKNOWN_TIME_LIMIT'
        assert r['wrapper_seconds']>=r['native_limit_seconds']-1
    assert meta['graph']==r['graph'] and meta['K']==r['K']
    assert hashlib.sha256((base/(prefix+'.cnf')).read_bytes()).hexdigest()==meta['cnf_sha256']
    r['n']=meta['n'];r['edges']=meta['edges'];r['rows']=meta['rows'];r['cnf_sha256']=meta['cnf_sha256']
    r['ordered']=meta['ordered']
    if r['kind']=='oracle':r['nontrivial_free_or_count']=len(meta['free_supports'])-meta['n']
    source='synth_sat_sources_dirty.py' if r['kind']=='source' else 'synth_sat_packing_oracle.py'
    r['source']=source;r['source_sha256']=hashlib.sha256((base/source).read_bytes()).hexdigest()
    filenames.add(source);filenames.add(r['graph'])
    filenames.update(prefix+ext for ext in ('.cnf','.json','.log','.solver.log'))
summary={'recorded_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'Normalized binary AO2 circuits; solver results and finite verification, not Lean proofs. UNKNOWN means native time limit, never a lower bound. Source queries forbid every clean source AND; oracle queries supply all primary OR supports at pairwise graph distance at least three for free.','cases':cases}
for kind in ('source','oracle'):
    summary[kind+'_counts']={status:sum(r['kind']==kind and r['status']==status for r in cases) for status in ('SAT','UNSAT','UNKNOWN_TIME_LIMIT')}
(base/'conjecture-run-outcomes.json').write_text(json.dumps(summary,indent=2)+'\n')
filenames.update(['source_tree7_census.py','source_unicycle7_batch.py','source-tree7-specifications.json','source-unicycle7-specifications.json','source-forest-batch.log','source-tree7-census.log','source-unicycle7-batch.log','packing-oracle-batch.log','packing-oracle-tree7-batch.log','packing-oracle-unicycle7-batch.log','packing_matching2_witness.py','packing-matching2-witness.log','conjecture-run-outcomes.json','collect_conjecture_runs.py'])
# Review artifacts are added only after the independent reviewer finishes.
if '--copy' in sys.argv:
    for name in sorted(filenames):
        src=base/name;dst=repo/name
        if dst.exists(): assert src.read_bytes()==dst.read_bytes(),('unexpected overwrite',name)
        else: shutil.copyfile(src,dst)
    manifest=json.loads((repo/'sha256.json').read_text())
    for name in sorted(filenames): manifest[name]=hashlib.sha256((repo/name).read_bytes()).hexdigest()
    (repo/'sha256.json').write_text(json.dumps(manifest,indent=2)+'\n')
    print('COPIED',len(filenames),'files; manifest',len(manifest))
print('SOURCE_COUNTS',summary['source_counts'])
print('ORACLE_COUNTS',summary['oracle_counts'])
print('FILE_COUNT',len(filenames))
