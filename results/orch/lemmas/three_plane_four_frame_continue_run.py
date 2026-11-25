from pathlib import Path
import subprocess,resource,time,json,hashlib,os,signal,sys,fcntl,datetime,shutil,sympy as s
job=Path('/tmp/oec/pequalnp-pilot-79');base='four-frame-power-triangle-d7-n2';prime=1000000007
matrix=job/(base+'.matrix');metafile=job/(base+'-metadata.json');metadata=json.loads(metafile.read_text())
original_checkpoint=job/(base+'-final-replay-checkpoint.bin.final');checkpoint=job/(base+'-path-continue-checkpoint.bin');output=job/(base+'-path-continue-progress.json');binding_path=job/(base+'-path-continue-binding.json')
lock=(job/(base+'-checkpoint.lock')).open('a+');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
ordinary_env={'PATH':'/usr/bin:/bin','LANG':'C','LC_ALL':'C','OMP_NUM_THREADS':'1'};resource.setrlimit(resource.RLIMIT_CORE,(0,0))
started=time.monotonic();runid=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ');limit=2*1024**3;records=[];reason='budget_exhausted';peak=0;target=(0,0,3,0,3,0,0,0,0,0);column=metadata['columns'].index(list(target))
def sha(path):
 h=hashlib.sha256()
 with path.open('rb') as f:
  for block in iter(lambda:f.read(1048576),b''):h.update(block)
 return h.hexdigest()
def atomic_json(path,data):
 tmp=Path(str(path)+'.tmp');tmp.write_text(json.dumps(data,indent=2)+'\n');tmp.replace(path)
def atomic_copy(source,dest):
 expected=sha(source);tmp=Path(str(dest)+'.tmp')
 with source.open('rb') as src,tmp.open('wb') as dst:shutil.copyfileobj(src,dst,1048576)
 assert sha(tmp)==expected;tmp.replace(dest)
def limits():
 resource.setrlimit(resource.RLIMIT_CORE,(0,0));resource.setrlimit(resource.RLIMIT_AS,(limit,limit));resource.setrlimit(resource.RLIMIT_CPU,(90,90))
def rss(pid):
 try:
  for line in (Path('/proc')/str(pid)/'status').read_text().splitlines():
   if line.startswith('VmRSS:'):return int(line.split()[1])*1024
 except FileNotFoundError:pass
 return 0
def verify_matrix(data):
 assert data['prime']==prime and data['member'];weights=data['witness']
 with matrix.open() as f:
  cols,rows=map(int,next(f).split());assert len(weights)==rows;values=[0]*cols;count=0
  for weight,line in zip(weights,f):
   count+=1;terms=list(map(int,line.split()));assert len(terms)==1+2*terms[0]
   if weight:
    for j in range(terms[0]):
     index,coeff=terms[1+2*j:3+2*j];assert 0<=index<cols;values[index]=(values[index]+weight*coeff)%prime
  assert count==rows and not f.read().strip()
 assert values==[int(i==column) for i in range(cols)]
 return sum(w!=0 for w in weights)
def verify_original(data,target):
 source=(job/'four-frame-cubic-triangle-0.msolve').read_text().splitlines();names=source[0].split(',');assert names[-1]=='v' and names[:-1]==metadata['variables'];vs=s.symbols(' '.join(names));body='\n'.join(source[2:]);assert all(c.isalnum() or c in ' _+-*^,()\n' for c in body);local=dict(zip(names,vs));raw=[s.Poly(s.sympify(q.strip().replace('^','**'),locals=local),*vs,domain=s.ZZ) for q in body.split(',') if q.strip()];assert len(raw)==17;polys=[]
 for p in raw[:-1]:
  assert all(m[-1]==0 for m,c in p.terms());polys.append({m[:-1]:int(c) for m,c in p.terms()})
 weights=data['witness'];origins=metadata['row_origins'];assert len(weights)==len(origins) and data['prime']==prime;out={}
 for w,(i,mult) in zip(weights,origins):
  if not w:continue
  assert 0<=i<len(polys) and len(mult)==10 and all(isinstance(e,int) and e>=0 for e in mult)
  for mon,c in polys[i].items():
   key=tuple(a+b for a,b in zip(mon,mult));out[key]=(out.get(key,0)+w*c)%prime
 out={m:c for m,c in out.items() if c};assert out=={target:1};return sum(w!=0 for w in weights)
original_checkpoint_sha=sha(original_checkpoint);matrix_sha=sha(matrix);metadata_sha=sha(metafile)
binding={'matrix_sha256':matrix_sha,'metadata_sha256':metadata_sha,'original_checkpoint_sha256':original_checkpoint_sha,'prime':prime,'target':list(target),'column':column}
if checkpoint.exists():
 assert binding_path.exists() and json.loads(binding_path.read_text())==binding
else:
 assert not binding_path.exists();atomic_copy(original_checkpoint,checkpoint);atomic_json(binding_path,binding)
assert sha(original_checkpoint)==original_checkpoint_sha
previous=-1
for chunk in range(1,21):
 remaining=300-(time.monotonic()-started)
 if remaining<=45:break
 budget=min(45,remaining-40);wall=min(75,remaining-35);logpath=job/(base+'-continue-'+runid+'-chunk-'+str(chunk)+'.log');chunk_start=time.monotonic();status='finished'
 with logpath.open('w') as log:
  proc=subprocess.Popen([str(job/'four_frame_macaulay_continue'),str(matrix),str(output),str(prime),str(checkpoint),str(budget),matrix_sha,metadata_sha],stdout=log,stderr=subprocess.STDOUT,env=ordinary_env,preexec_fn=limits,start_new_session=True)
  while proc.poll() is None:
   peak=max(peak,rss(proc.pid))
   if peak>limit:status='memory_limit'
   elif time.monotonic()-chunk_start>wall:status='chunk_timeout'
   if status!='finished':os.killpg(proc.pid,signal.SIGKILL);break
   time.sleep(.2)
  code=proc.wait()
 record={'chunk':chunk,'status':status,'exit':code,'seconds':time.monotonic()-chunk_start,'peak_rss_bytes':peak,'log':str(logpath)}
 if code==0 and status=='finished':
  assert sha(matrix)==matrix_sha and sha(metafile)==metadata_sha,'input changed during chunk'
  data=json.loads(output.read_text());record.update({k:v for k,v in data.items() if k!='witness'});assert data['next_row']>previous or data.get('complete');previous=data['next_row']
  query_output=job/(base+'-path-continue-query-'+runid+'-'+str(chunk)+'.json');query_log=job/(base+'-path-continue-query-'+runid+'-'+str(chunk)+'.log');checkpoint_sha=sha(checkpoint)
  with query_log.open('w') as log:
   subprocess.run([str(job/'four_frame_checkpoint_query'),str(matrix),str(query_output),str(prime),str(checkpoint),matrix_sha,metadata_sha,str(column)],stdout=log,stderr=subprocess.STDOUT,env=ordinary_env,preexec_fn=limits,timeout=30,check=True)
  assert sha(checkpoint)==checkpoint_sha;query=json.loads(query_output.read_text());assert query['target_column']==column and query['next_row']==data['next_row'];record['path_query']={k:v for k,v in query.items() if k!='witness'}
  if query['member']:
   record['verified_matrix_support']=verify_matrix(query);record['verified_original_support']=verify_original(query,target)
   atomic_copy(checkpoint,job/(base+'-path-final-checkpoint.bin'));atomic_copy(query_output,job/(base+'-path-p'+str(prime)+'-witness.json'));reason='verified_modular_path_witness'
  elif data.get('complete'):reason='completed_without_path_witness'
 else:reason=status if status!='finished' else 'process_failure'
 assert sha(original_checkpoint)==original_checkpoint_sha;record['original_checkpoint_unchanged']=True
 records.append(record);print(json.dumps(record),flush=True)
 summary={'classification':'Finite-field certificate extraction; not Lean checked','base':base,'prime':prime,'records':records,'reason':reason,'elapsed_seconds':time.monotonic()-started,'peak_rss_bytes':peak,'binding':binding};atomic_json(job/(base+'-path-continue-run.json'),summary)
 if reason!='budget_exhausted':break
assert sha(original_checkpoint)==original_checkpoint_sha
summary={'classification':'Finite-field certificate extraction; not Lean checked','base':base,'prime':prime,'records':records,'reason':reason,'elapsed_seconds':time.monotonic()-started,'peak_rss_bytes':peak,'binding':binding};atomic_json(job/(base+'-path-continue-run.json'),summary);atomic_json(job/(base+'-path-continue-run-'+runid+'.json'),summary);print(json.dumps({'final':True,'reason':reason,'elapsed_seconds':time.monotonic()-started,'peak_rss_bytes':peak}),flush=True)
