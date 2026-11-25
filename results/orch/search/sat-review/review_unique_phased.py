from pathlib import Path
import hashlib,json,importlib.util,re
p=Path('/tmp/oec/pequalnp-pilot-70/constructive');q=Path('/tmp/oec/pequalnp-pilot-70/circuit-search');scratch=Path('.')
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
def load(name,path):
 spec=importlib.util.spec_from_file_location(name,path);module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);return module
raw=load('reviewed_raw_verify',p/'raw_verify.py');wrapper=load('reviewed_unique_wrapper',p/'unique_phased_run.py')
assert sha(p/'unique_phased_run.py')=='7891b60028bdaec206fd8d53120ed48dace7ef162a2aa8374134be73da0e7250'
assert sha(p/'raw_verify.py')==wrapper.VERIFIER_SHA and sha(q/'phased')==wrapper.HELPER_SHA and sha(q/'phased.cpp')==wrapper.DRIVER_SHA
assert sha(q/'unique0-26-permissive-final.cnf')==wrapper.CNF_SHA and sha(q/'unique0-26-permissive-final.map.json')==wrapper.MAP_SHA and sha(q/'unique0-26-near.phases')==wrapper.PHASE_SHA
pm=json.loads((q/'unique0-26-permissive-final.map.json').read_text());assert pm['gates']==26 and pm['ninputs']==14
preferences={}
for word in (q/'unique0-26-near.phases').read_text().split():
 assert word.isascii() and re.fullmatch(r'-?[0-9]+',word);v=int(word);assert v and 1<=abs(v)<=pm['nv'];assert abs(v) not in preferences or preferences[abs(v)]==(v>0);preferences[abs(v)]=v>0
assert len(preferences)==5928 and wrapper.read_phases(q/'unique0-26-near.phases',pm['nv'])==(5928,5928)
result=json.loads((p/'unique-phased-baseline-smoke-v1-result.json').read_text());assert result['status']=='SAT' and result['full_truth_table_verified'] and result['gate_count']==27
for pin in result['pins'].values():assert sha(Path(pin['path']))==pin['sha256']
for pathkey,hashkey in [('solve_log','solve_log_sha256'),('verification_log','verification_log_sha256'),('verified_file','verified_sha256'),('witness_file','witness_sha256')]:assert sha(Path(result[pathkey]))==result[hashkey]
m=json.loads((p/'anchored-tail27-smoke.map.json').read_text());lines=(p/'anchored-tail27-smoke.cnf').read_text().splitlines();assert lines[0]==f'p cnf {m["nv"]} {m["clauses"]}'
model={};statuses=[]
for line in (p/'unique-phased-baseline-smoke-v1-solve.log').read_text().splitlines():
 if line.startswith('s '):statuses.append(line)
 if line.startswith('v '):
  for v in map(int,line.split()[1:]):
   if v:assert abs(v) not in model or model[abs(v)]==(v>0);model[abs(v)]=v>0
assert statuses==['s SATISFIABLE'] and set(model)==set(range(1,m['nv']+1))
assert len(lines)-1==m['clauses']
for line in lines[1:]:
 c=list(map(int,line.split()));assert c[-1]==0 and any(model[abs(v)]==(v>0) for v in c[:-1])
gates=[]
for i,g in enumerate(m['structure']):
 left=[i for i,v in enumerate(g['left']) if model[v]];right=[i for i,v in enumerate(g['right']) if model[v]];assert len(left)==len(right)==1 and 0<=left[0]<=right[0]<14+i
 gates.append(['or' if model[g['op']] else 'and',left[0],right[0]])
def variable(i,n):
 block=(1<<(1<<i))-1;return sum(block<<(j+(1<<i)) for j in range(0,1<<n,1<<(i+1)))
values=[variable(i,14) for i in range(14)]
for op,u,v in gates:values.append(values[u]|values[v] if op=='or' else values[u]&values[v])
H={(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)}
target=0
for u,v in H:target|=values[u]&values[v]
assert values[-1]==target and gates==json.loads((p/'unique-phased-baseline-smoke-v1-witness.json').read_text())
for i,g in enumerate(m['structure']):
 for r,mask in enumerate(m['rows']):assert model[g['out'][r]]==bool(values[14+i]>>mask&1)
verified=json.loads((p/'unique-phased-baseline-smoke-v1-verified.json').read_text());assert verified['gates']==gates and verified['gate_count']==27 and verified['checked_clauses']==211180 and verified['checked_assignments']==16384
provenance=json.loads((p/'unique-phased-baseline-model.provenance.json').read_text());assert sha(Path(provenance['source_model']))==provenance['source_model_sha256'] and sha(Path(provenance['source_map']))==provenance['source_map_sha256'] and sha(p/'unique-phased-baseline-model.phases')==provenance['phase_sha256']
pre=json.loads((scratch/'unique-phased-independent-preflight-result.json').read_text());assert pre['all_passed'] and len(pre['cases'])==9
for case in pre['cases']:
 assert case['exit_code']!=0 and case['rejected_before_launch']
 stem=scratch/('unique-phased-independent-preflight-'+case['name']);log=Path(str(stem)+'.log');assert sha(log)==case['log_sha256'] and case['expected_error'] in log.read_text()
 for suffix in ['-run.json','-result.json','-solve.log','-verify.log','-verified.json','-witness.json']:assert not Path(str(stem)+suffix).exists()
parserdir=scratch/'unique-phased-parser-tests';parserdir.mkdir(exist_ok=True);checks=[]
def test(name,text,kind,want):
 path=parserdir/name;assert not path.exists();path.write_text(text)
 try:
  got=raw.read_cnf(path) if kind=='cnf' else raw.read_model(path,2)
 except (AssertionError,ValueError):
  assert want=='reject';checks.append({'name':name,'status':'rejected'});return
 assert want!='reject' and got==want;checks.append({'name':name,'status':'accepted'})
test('valid-multiline.cnf','c test\np cnf 2 2\n1\n-2 0 2 0\n','cnf',(2,[[1,-2],[2]]))
test('missing-terminator.cnf','p cnf 2 1\n1\n','cnf','reject')
test('duplicate-header.cnf','p cnf 2 1\np cnf 2 1\n1 0\n','cnf','reject')
test('out-of-range.cnf','p cnf 2 1\n3 0\n','cnf','reject')
test('wrong-count.cnf','p cnf 2 2\n1 0\n','cnf','reject')
test('valid.model','s SATISFIABLE\nv 1 -2 0\n','model',{1:True,2:False})
test('duplicate-status.model','s SATISFIABLE\ns SATISFIABLE\nv 1 -2 0\n','model','reject')
test('conflict.model','s SATISFIABLE\nv 1 -1 -2 0\n','model','reject')
test('incomplete.model','s SATISFIABLE\nv 1 0\n','model','reject')
test('outside.model','s SATISFIABLE\nv 1 -2 3 0\n','model','reject')
test('wrong-status.model','s UNKNOWN\nv 1 -2 0\n','model','reject')
report={'status':'PASS','wrapper_sha256':sha(p/'unique_phased_run.py'),'verifier_sha256':sha(p/'raw_verify.py'),'preflight_source_sha256':sha(p/'unique_phased_preflight_smoke.py'),'default_production':{'variables':pm['nv'],'clauses':pm['clauses'],'gate_count':pm['gates'],'phase_preferences':len(preferences),'cnf_sha256':wrapper.CNF_SHA,'map_sha256':wrapper.MAP_SHA,'phase_sha256':wrapper.PHASE_SHA},'baseline':{'clauses_independently_verified':len(lines)-1,'full_inputs':16384,'gate_count':len(gates)},'preflight_rejections':9,'parser_checks':checks,'scope':'Pinned soft phase preferences only; no added clauses/assumptions. SAT witness exported only after exact full model and raw target verification. No production solver launched by reviewer.'}
Path('unique-phased-review.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
