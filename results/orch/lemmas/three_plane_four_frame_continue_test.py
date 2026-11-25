from pathlib import Path
import json,hashlib,subprocess,resource,shutil
job=Path('/tmp/oec/pequalnp-pilot-79');env={'PATH':'/usr/bin:/bin','LANG':'C','LC_ALL':'C','OMP_NUM_THREADS':'1'};resource.setrlimit(resource.RLIMIT_CORE,(0,0))
def limits():resource.setrlimit(resource.RLIMIT_CORE,(0,0))
def sha(path):
 h=hashlib.sha256()
 with path.open('rb') as f:
  for block in iter(lambda:f.read(1048576),b''):h.update(block)
 return h.hexdigest()
def call(args,log):return subprocess.run(args,stdout=log,stderr=subprocess.STDOUT,env=env,preexec_fn=limits,check=True,timeout=5)
results=[]
for case in ['restored_unit','no_unit']:
 cols=5;matrix=([[0,0,0,0,1],[2,0,0,0,3],[1,3,0,0,4],[0,2,5,0,7],[3,0,1,7,9],[4,5,6,7,8]] if case=='restored_unit' else [[2,0,0,0,0],[1,3,0,0,0],[0,2,5,0,0],[3,0,1,7,0],[4,5,6,7,0],[0,0,0,0,0]])
 base='four-frame-continue-test-'+case;inp=job/(base+'.matrix');meta=job/(base+'-metadata.json');meta.write_text(json.dumps({'columns':list(range(cols)),'origins':list(range(len(matrix)))})+'\n')
 with inp.open('w') as f:
  f.write(str(cols)+' '+str(len(matrix))+'\n')
  for row in matrix:
   terms=[(i,c) for i,c in enumerate(row) if c];f.write(str(len(terms))+' '+' '.join(str(i)+' '+str(c) for i,c in terms)+'\n')
 initial=None
 with (job/(base+'.log')).open('w') as log:
  if case=='restored_unit':
   root=job/(base+'-seed.checkpoint');out=job/(base+'-seed.json')
   for q in [root,Path(str(root)+'.final')]:
    if q.exists():q.unlink()
   call([str(job/'four_frame_macaulay_finalsave'),str(inp),str(out),'97',str(root),'5',sha(inp),sha(meta)],log);initial=Path(str(root)+'.final');assert initial.exists();initial_sha=sha(initial)
  outputs=[]
  for label,budget in [('one',100),('chunked',2)]:
   checkpoint=job/(base+'-'+label+'.checkpoint');output=job/(base+'-'+label+'.json')
   if checkpoint.exists():checkpoint.unlink()
   if initial:shutil.copyfile(initial,checkpoint)
   chunks=0
   while True:
    chunks+=1;call([str(job/'four_frame_macaulay_continue'),str(inp),str(output),'97',str(checkpoint),'5',sha(inp),sha(meta),str(budget)],log);data=json.loads(output.read_text())
    if data.get('complete'):break
    assert data['checkpointed'] and chunks<=10
   assert data['next_row']==len(matrix) and data['rank']==(5 if case=='restored_unit' else 4) and data['unit']==(case=='restored_unit')
   outputs.append({k:v for k,v in data.items() if k!='seconds'})
   for target in range(cols):
    query=job/(base+'-'+label+'-q'+str(target)+'.json');call([str(job/'four_frame_checkpoint_query'),str(inp),str(query),'97',str(checkpoint),sha(inp),sha(meta),str(target)],log);qdata=json.loads(query.read_text());expected=case=='restored_unit' or target<4;assert qdata['member']==expected
    if expected:assert [sum(w*row[i] for w,row in zip(qdata['witness'],matrix))%97 for i in range(cols)]==[int(i==target) for i in range(cols)]
   # A completed state must be resumable without changing its result.
   call([str(job/'four_frame_macaulay_continue'),str(inp),str(output),'97',str(checkpoint),'5',sha(inp),sha(meta)],log);again=json.loads(output.read_text());assert {k:v for k,v in again.items() if k!='seconds'}==outputs[-1]
  assert outputs[0]==outputs[1]
  if initial:assert sha(initial)==initial_sha
 results.append({'case':case,'uninterrupted_equals_chunked':True,'complete_state_resumes':True,'all_coordinate_queries_verified':True,'immutable_seed_preserved':True})
(job/'four-frame-continue-validation.json').write_text(json.dumps(results,indent=2)+'\n');print(json.dumps(results))
