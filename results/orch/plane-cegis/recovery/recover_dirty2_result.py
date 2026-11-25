import argparse,datetime,hashlib,json,os
from pathlib import Path
ap=argparse.ArgumentParser();ap.add_argument('--prefix',required=True);ap.add_argument('--native-pid',required=True,type=int);a=ap.parse_args()
b=Path(a.prefix);s=Path('direct_cnf_warm_dirty2.py')
assert hashlib.sha256(s.read_bytes()).hexdigest()=='73bd56fbce94cc902f163a69da9f217d065a5ee3186d79a5b47a7fe6b50c5226'
stat=Path(f'/proc/{a.native_pid}/stat');exit_code=None
if stat.exists():
 fields=stat.read_text().rsplit(')',1)[1].split();assert fields[0]=='Z','Native solver is still active'
 exit_code=os.waitstatus_to_exitcode(int(fields[49]))
stdout=b.with_suffix('.stdout').read_text();solfile=b.with_suffix('.sol');soltext=solfile.read_text() if solfile.exists() else '';verdicts=sorted({x for x in stdout.splitlines()+soltext.splitlines() if x in ('s SATISFIABLE','s UNSATISFIABLE','s UNKNOWN')})
assert len(verdicts)<=1
verdict=verdicts[0] if verdicts else None
log_exit=[int(x.split()[2]) for x in stdout.splitlines() if x.startswith('c exit ')];assert len(log_exit)<=1
if exit_code is not None and log_exit:assert exit_code==log_exit[0]
mapping_path=b.with_suffix('.mapping.json');m=json.loads(mapping_path.read_text())
assert m['n']==26 and m['size'] in (63,69);size=m['size']
cnf=b.with_suffix('.cnf');digest=hashlib.sha256()
with cnf.open('rb') as f:
 for block in iter(lambda:f.read(1048576),b''):digest.update(block)
expected={'bc3c04d5e26d21bf8b62770e405115f34bff91687d9d5f6b64e710e33cf6a347':'warm-dirty2-near63-query.mapping.json','e429b42998d21b924eea58d52c1471db23ff1ad71251183cf4349118d89bdf05':'warm-dirty2-nested63-query.mapping.json','48e533d29f69940b42f330e7d3ed7ec5871894ee4de4069a8c1b9381f287f25a':'warm-dirty2-control69-free3.mapping.json'}
assert digest.hexdigest() in expected
assert mapping_path.read_bytes()==Path(expected[digest.hexdigest()]).read_bytes()
r={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'Posthoc recovery after original wrapper was lost in environment transition','native_pid':a.native_pid,'native_exit_code':exit_code,'native_log_exit_code':log_exit[0] if log_exit else None,'native_verdict':verdict,'cnf_sha256':digest.hexdigest(),'mapping_sha256':hashlib.sha256(mapping_path.read_bytes()).hexdigest(),'source_sha256':hashlib.sha256(s.read_bytes()).hexdigest()}
if verdict=='s SATISFIABLE':
 assert exit_code in (None,10) and log_exit in ([],[10])
 assignment={};sol=b.with_suffix('.sol')
 for line in sol.read_text().splitlines():
  if line.startswith('v '):
   for value in map(int,line[2:].split()):
    if value:
     assert abs(value) not in assignment or assignment[abs(value)]==(value>0)
     assignment[abs(value)]=value>0
 flipped=set(m['flipped_variables']);original={i:(not v if i in flipped else v) for i,v in assignment.items()}
 count=0
 for line in cnf.open():
  if line.startswith('p '):
   _,kind,nv,nc=line.split();assert kind=='cnf';nv=int(nv);nc=int(nc)
   assert set(assignment)==set(range(1,nv+1));assert flipped<=set(assignment);continue
  if line.startswith('c ') or not line.strip():continue
  clause=list(map(int,line.split()));assert clause.pop()==0;count+=1
  assert all(1<=abs(x)<=nv for x in clause)
  assert any(assignment[abs(x)]==(x>0) for x in clause)
  old=[-x if abs(x) in flipped else x for x in clause]
  assert any(original[abs(x)]==(x>0) for x in old)
 assert count==nc==(8860275 if size==63 else 10339293)
 gates=[]
 for j in range(size):
  left=[i for i,v in enumerate(m['left'][j]) if original[v]];right=[i for i,v in enumerate(m['right'][j]) if original[v]]
  assert len(left)==len(right)==1
  op=int(original[m['ops'][j]]);u=left[0];v=right[0]
  assert 0<=u<=v<26+j and (u!=v or op==1)
  gates.append([op,u,v])
 edges={(p,13+l) for p in range(13) for l in range(13) if (p+l)%13 in (0,1,3,9)}
 positives={1<<p|1<<l for p,l in edges};negatives=set();neighbors=[sum(1<<l for l in range(13) if (p,13+l) in edges) for p in range(13)]
 for points in range(8192):
  lines=8191
  for p in range(13):
   if points>>p&1:lines&=~neighbors[p]
  if points==sum(1<<p for p in range(13) if not neighbors[p]&lines):negatives.add(points|(lines<<13))
 assert len(positives)==52 and len(negatives)==704 and len(m['rows'])==756 and set(m['rows'])==positives|negatives
 rows=m['rows'];values=[sum(bool(row>>i&1)<<k for k,row in enumerate(rows)) for i in range(26)]
 for op,u,v in gates:values.append(values[u]|values[v] if op else values[u]&values[v])
 misses=[row for k,row in enumerate(rows) if bool(values[-1]>>k&1)!=(row in positives)];assert not misses
 negmask=sum(1<<k for k,row in enumerate(rows) if row in negatives)
 dirty=[26+j for j,g in enumerate(gates) if g[0]==0 and values[26+j]&negmask]
 assert len(dirty)>=2 and sum(g[0]==0 for g in gates)>=13
 assert all(original[flag]==(not bool(values[26+j]&negmask)) for j,flag in enumerate(m['clean_flags']))
 chosen=[edge for edge,var in zip(m['joint_edges'],m['joint_edge_selectors']) if original[var]];assert len(chosen)==1 and tuple(chosen[0]) in edges
 p,l=chosen[0];joint=[(i==p,i==l,False) for i in range(26)]
 for op,u,v in gates:
  x=joint[u];y=joint[v];joint.append(tuple(x[k] or y[k] for k in range(3)) if op else (False,False,(x[0] and y[1]) or (x[1] and y[0])))
 assert not joint[-1][2]
 assert all(tuple(v if type(v) is bool else original[v] for v in ids)==value for ids,value in zip(m['joint_profiles'],joint))
 r.update({'status':'SAT; recovered complete clause checks and full boundary passed; Lean verification required','n':26,'size':size,'output':26+size-1,'gates':gates,'full_boundary_rows':756,'full_boundary_mismatches':[],'cnf_clauses_verified_in_both_signs':count,'model_dirty_AND_wires':dirty,'model_non_read1_edge':chosen[0],'model_sha256':hashlib.sha256(sol.read_bytes()).hexdigest()})
elif verdict=='s UNSATISFIABLE':
 assert exit_code in (None,20) and log_exit in ([],[20]);r['status']='UNSAT; external solver only, not Lean checked'
elif verdict=='s UNKNOWN' or exit_code==0 or log_exit==[0]:r['status']='UNKNOWN/no completed SAT or UNSAT verdict; no target result'
else:r['status']='Interrupted or unclassified; no target result'
r['native_time_limit_log_lines']=[line for line in stdout.splitlines() if 'time limit' in line.lower()]
r['recovery_method']='Standalone persisted-CNF/model verifier; no automatic wrapper validation claimed'
loss=b.with_suffix('.wrapper-loss.json');r['original_wrapper_exit_code']=json.loads(loss.read_text()).get('decoded_wrapper_exit') if loss.exists() else None
r['recovery_completed_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
if size==69:r['scope']='Recovery-code control on known69 circuit; not a63-gate witness'
b.with_suffix('.recovered.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({k:v for k,v in r.items() if k!='gates'}))
