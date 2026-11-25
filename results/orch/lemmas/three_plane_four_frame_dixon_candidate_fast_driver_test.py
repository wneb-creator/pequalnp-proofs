from pathlib import Path
import json,hashlib,subprocess,resource,shutil,sys
job=Path('/tmp/oec/pequalnp-pilot-79');test=job/'four-frame-dixon-candidate-fast-driver-test';test.mkdir(exist_ok=True);base='four-frame-power-triangle-d7-n2';env={'PATH':'/usr/bin:/bin','LANG':'C','LC_ALL':'C','OMP_NUM_THREADS':'1'};resource.setrlimit(resource.RLIMIT_CORE,(0,0))
def limits():resource.setrlimit(resource.RLIMIT_CORE,(0,0));resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3))
def sha(path):
 h=hashlib.sha256()
 with path.open('rb') as f:
  for block in iter(lambda:f.read(1048576),b''):h.update(block)
 return h.hexdigest()
variables=['u02','u03','u12','u13','u23','a','b','g','h','k'];columns=[[int(i==j) for i in range(10)] for j in range(3)];rows=[[2,1,0],[0,3,1],[1,0,-2],[4,5,6]];matrix=test/(base+'.matrix');meta=test/(base+'-metadata.json');checkpoint=test/(base+'-path-final-checkpoint.bin')
with matrix.open('w') as f:
 f.write('3 4\n')
 for row in rows:
  terms=[(i,c) for i,c in enumerate(row) if c];f.write(str(len(terms))+' '+' '.join(str(i)+' '+str(c) for i,c in terms)+'\n')
meta.write_text(json.dumps({'variables':variables,'columns':columns,'target':columns[0],'row_origins':[[i,[0]*10] for i in range(4)]})+'\n');source=test/'four-frame-cubic-triangle-0.msolve';source.write_text(','.join(variables+['v'])+'\n0\n'+',\n'.join(['2*u02+u03','3*u03+u12','u02-2*u12','4*u02+5*u03+6*u12']+['0']*12+['v-1'])+'\n')
if checkpoint.exists():checkpoint.unlink()
with (test/'setup.log').open('w') as log:subprocess.run([str(job/'four_frame_macaulay_continue'),str(matrix),str(test/'initial.json'),'1000000007',str(checkpoint),'5',sha(matrix),sha(meta)],stdout=log,stderr=subprocess.STDOUT,env=env,preexec_fn=limits,timeout=5,check=True)
(test/'four-frame-dixon-candidates.json').write_text(json.dumps({'variables':variables,'candidates':{'cross':{'terms':[{'exponents':columns[0],'coefficient':2},{'exponents':columns[1],'coefficient':-3}]}}})+'\n')
checkpoint_sha=sha(checkpoint);shutil.copyfile(job/'four_frame_dixon_step',test/'four_frame_dixon_step');(test/'four_frame_dixon_step').chmod(0o755);shutil.copyfile(job/'four_frame_rational_reconstruct',test/'four_frame_rational_reconstruct');(test/'four_frame_rational_reconstruct').chmod(0o755)
text=(job/'four_frame_dixon_candidate_fast_run.py').read_text();assert text.count("job=Path('/tmp/oec/pequalnp-pilot-79')")==1;text=text.replace("job=Path('/tmp/oec/pequalnp-pilot-79')",'job=Path('+repr(str(test))+')');driver=test/'driver.py';driver.write_text(text)
state=test/(base+'-cross-candidate-dixon-state.json');certificate=test/(base+'-cross-candidate-dixon-exact-certificate.json')
if state.exists():state.unlink()
if certificate.exists():certificate.unlink()
with (test/'run.log').open('w') as log:
 for trial in range(2):
  subprocess.run([sys.executable,str(driver),'cross','1','30'],stdout=log,stderr=subprocess.STDOUT,env=env,preexec_fn=limits,timeout=30,check=True)
  data=json.loads(certificate.read_text());denominator=int(data['denominator_hex'],16);coefficients=[int(h,16) for h in data['coefficients_hex']];assert [sum(w*r[j] for w,r in zip(coefficients,rows)) for j in range(3)]==[2*denominator,-3*denominator,0]
 before_iteration=json.loads(state.read_text())['iteration']
 subprocess.run([sys.executable,str(driver),'cross','1','30','1'],stdout=log,stderr=subprocess.STDOUT,env=env,preexec_fn=limits,timeout=30,check=True)
 assert json.loads(state.read_text())['iteration']==before_iteration+1
 assert sha(checkpoint)==checkpoint_sha
 before=state.read_bytes();bad=json.loads(before);bad['carry'][0]+=1;state.write_text(json.dumps(bad)+'\n');poison=state.read_bytes();result=subprocess.run([sys.executable,str(driver),'cross','1','30'],stdout=log,stderr=subprocess.STDOUT,env=env,preexec_fn=limits,timeout=30);assert result.returncode!=0 and state.read_bytes()==poison;state.write_bytes(before)
 bad=json.loads(before);bad['binding']['prime']=97;state.write_text(json.dumps(bad)+'\n');poison=state.read_bytes();result=subprocess.run([sys.executable,str(driver),'cross','1','30'],stdout=log,stderr=subprocess.STDOUT,env=env,preexec_fn=limits,timeout=30);assert result.returncode!=0 and state.read_bytes()==poison;state.write_bytes(before)
result={'single_batch_limit_verified':True,'exact_matrix_and_original_polynomial_identity':True,'resumed_state_verified':True,'immutable_checkpoint':True,'invalid_carry_rejected_without_state_write':True,'wrong_binding_rejected_without_state_write':True};(job/'four-frame-dixon-candidate-fast-driver-validation.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
