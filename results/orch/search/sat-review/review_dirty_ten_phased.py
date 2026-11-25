from pathlib import Path
import json,hashlib,re,subprocess,sys
q=Path('/tmp/oec/pequalnp-pilot-70/circuit-search');p=Path('/tmp/oec/pequalnp-pilot-70/constructive');scratch=Path('.').resolve()
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
pre=json.loads((q/'dirty-ten-phased-preflight.json').read_text());cnf=Path(pre['cnf']);mapping=cnf.with_suffix('.map.json');phases=Path(pre['phases']);wrapper=Path(pre['wrapper'])
checks=[(cnf,'cnf_sha256'),(mapping,'map_sha256'),(phases,'phase_sha256'),(wrapper,'wrapper_sha256'),(p/'joint_decode.py','decoder_sha256'),(q/'phased','helper_sha256'),(q/'phased.cpp','helper_source_sha256')]
for path,key in checks:assert sha(path)==pre[key]
old=json.loads((p/'joint-ten10.map.json').read_text());m=json.loads(mapping.read_text());assert old['nv']==1423 and m['nv']==1503 and m['clauses']==25019
for field in pre['same_id_fields']:assert old[field]==m[field]
assert m['cnf_file']==str(cnf) and m['cnf_sha256']==sha(cnf)
assert cnf.read_text().splitlines()[0]=='p cnf 1503 25019'
text=phases.read_text();assert text.isascii();prefs={}
for word in text.split():
 assert re.fullmatch(r'-?[0-9]+',word);v=int(word);assert v and 1<=abs(v)<=1423
 assert abs(v) not in prefs or prefs[abs(v)]==(v>0);prefs[abs(v)]=v>0
assert len(prefs)==len(text.split())==991
assert not(set(prefs)&set(range(1424,1504))) and 1503-len(prefs)==512
seed=json.loads((p/'joint-ten10-branch3-near.json').read_text());assert seed['branch']==3 and seed['metadata_sha256']==sha(p/'joint-ten10.map.json') and seed['seed_sha256']==sha(Path(seed['seed']))
gs=seed['normalized_gates'];d=m['variants'][3]['data'];expected={m['truth']:True}
for i,s in enumerate(m['variant_selectors']):expected[s]=i==3
for c in m['varying_cells']:expected[c['variable']]=bool(c['bits'][3])
rows=m['variants'][3]['ordered_rows'];values=[]
for row in rows:
 w=list(map(bool,row['cuts']))
 for op,u,v in gs:
  assert 0<=u<=v<len(w);w.append(w[u] or w[v] if op=='or' else w[u] and w[v])
 values.append(w)
for i,((op,u,v),gate) in enumerate(zip(gs,m['structure'])):
 for j,s in enumerate(gate['left']):expected[s]=j==u
 for j,s in enumerate(gate['right']):expected[s]=j==v
 expected[gate['op']]=op=='or'
 for r,w in enumerate(values):
  expected[gate['lv'][r]]=w[u];expected[gate['rv'][r]]=w[v];expected[gate['out'][r]]=w[m['ninputs']+i]
assert expected==prefs
assert all(not values[r][m['ninputs']+i] for i,(op,_,_) in enumerate(gs) if op=='and' for r,t in enumerate(m['targets']) if not t)
assert [r['mask'] for r,w in zip(rows,values) if bool(r['value'])!=w[-1]]==[513]
def variable(i,n):
 block=(1<<(1<<i))-1;return sum(block<<(j+(1<<i)) for j in range(0,1<<n,1<<(i+1)))
def sumvec(w,s):
 t=0
 for i in s:t|=w[i]
 return t
def target(w,e):
 t=0
 for u,v in e:t|=w[u]&w[v]
 return t
def run(w,gates):
 w=list(w)
 for op,u,v in gates:w.append(w[u]|w[v] if op=='or' else w[u]&w[v])
 return w
real=d['real_inputs'];rv=[variable(i,real) for i in range(real)];signals=rv+[sumvec(rv,s) for s in d['free_or_supports']];truth=target(rv,d['edges']);near=run(signals,gs)[-1];assert (truth^near).bit_count()==16 and not(near&~truth)
fv=[variable(i,14) for i in range(14)];full=[['or' if op else 'and',u,v] for op,u,v in d['fixed_gates']];names=d['original_variables']+d['fixed_cut_wires']
for op,u,v in gs:full.append([op,names[u],names[v]]);names.append(13+len(full))
full.append(['or',d['fixed_output'],names[-1]])
H={(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)}
assert len(full)==26 and run(fv,full)[-1]==target(fv,H-{(1,13)}) and (target(fv,H)^run(fv,full)[-1]).bit_count()==47
cmd=pre['command'];assert pre['workdir']==str(p) and cmd==['python3','joint_phased_run.py','--cnf',str(cnf),'--phases',str(phases),'--prefix',str(q/'joint-ten10-live-dirty-phased15'),'--seconds','900']
for suffix in ['-run.json','-result.json','-solve.log','-verified.json','-witness.json']:assert not Path(str(q/'joint-ten10-live-dirty-phased15')+suffix).exists()
rejects=[]
for name,content,wanted in [('zero','0\n','Zero phase literal'),('outside','1504\n','Phase variable outside CNF range'),('conflict','1\n-1\n','Conflicting phase duplicates')]:
 prefix=scratch/('dirty-ten-phased-reject-'+name);pf=Path(str(prefix)+'.phases');log=Path(str(prefix)+'.log');assert not pf.exists() and not log.exists();pf.write_text(content)
 command=[sys.executable,str(wrapper),'--cnf',str(cnf),'--phases',str(pf),'--prefix',str(prefix),'--seconds','1']
 with log.open('w') as stream:result=subprocess.run(command,stdout=stream,stderr=subprocess.STDOUT)
 assert result.returncode!=0 and wanted in log.read_text()
 for suffix in ['-run.json','-result.json','-solve.log','-verified.json','-witness.json']:assert not Path(str(prefix)+suffix).exists()
 rejects.append({'case':name,'exit_code':result.returncode,'rejected_before_launch':True,'log_sha256':sha(log)})
report={'status':'PASS','preflight_sha256':sha(q/'dirty-ten-phased-preflight.json'),'hashes':{key:sha(path) for path,key in checks},'variables':1503,'clauses':25019,'phase_preferences':991,'new_dirty_variables_unphased':80,'all_unphased_variables':512,'all_preferences_reconstructed_from_branch3_seed':True,'near_seed':{'residual_misses':16,'full_misses':47,'dirty_and_rows':0,'is_satisfying_witness':False},'rejection_checks':rejects,'approved_command':cmd,'scope':'Exact frozen inputs and soft preferences only. Joint decoder retains complete model/clause validation and all1024 residual/all16384 full assignments; runtime wrapper records source hashes rather than enforcing external preflight pins. No production solver launched.'}
Path('dirty-ten-phased-review.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
