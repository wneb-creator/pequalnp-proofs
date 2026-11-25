from pathlib import Path
import json,hashlib,subprocess,resource,math,sympy as s
job=Path('/tmp/oec/pequalnp-pilot-79');env={'PATH':'/usr/bin:/bin','LANG':'C','LC_ALL':'C','OMP_NUM_THREADS':'1'};resource.setrlimit(resource.RLIMIT_CORE,(0,0))
def limits():
 resource.setrlimit(resource.RLIMIT_CORE,(0,0));resource.setrlimit(resource.RLIMIT_AS,(256*1024**2,256*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(5,5))
def sha(path):
 h=hashlib.sha256()
 with path.open('rb') as f:
  for block in iter(lambda:f.read(1048576),b''):h.update(block)
 return h.hexdigest()
def call(args,log,code=0):
 result=subprocess.run(args,stdout=log,stderr=subprocess.STDOUT,env=env,preexec_fn=limits,timeout=5);assert result.returncode==code,(result.returncode,code)
def reconstruct(a,m):
 if a==0:return (0,1)
 bound=math.isqrt(m//2);r0,r1=m,a;t0,t1=0,1
 while abs(r1)>bound:
  q=r0//r1;r0,r1=r1,r0-q*r1;t0,t1=t1,t0-q*t1
 if t1<0:r1,t1=-r1,-t1
 if 0<t1<=bound and math.gcd(r1,t1)==1 and (r1-a*t1)%m==0:return(r1,t1)
 return None
results=[]
cases=[('square',[[2,1,0],[0,3,1],[1,0,-2],[4,5,6]],[1,0,0]),('rectangular',[[2,1,0,4],[0,3,1,6],[1,0,-2,1],[4,5,6,14],[0,0,0,0]],[1,0,0,1])]
for label,rows,rhs in cases:
 base='four-frame-dixon-test-'+label;inp=job/(base+'.matrix');meta=job/(base+'-metadata.json');checkpoint=job/(base+'.checkpoint');summary=job/(base+'-checkpoint.json');cols=len(rhs);nrows=len(rows);prime=97
 with inp.open('w') as f:
  f.write(str(cols)+' '+str(nrows)+'\n')
  for row in rows:
   terms=[(j,c) for j,c in enumerate(row) if c];f.write(str(len(terms))+' '+' '.join(str(j)+' '+str(c) for j,c in terms)+'\n')
 meta.write_text(json.dumps({'cols':cols,'rows':nrows})+'\n')
 if checkpoint.exists():checkpoint.unlink()
 with (job/(base+'.log')).open('w') as log:
  call([str(job/'four_frame_macaulay_continue'),str(inp),str(summary),str(prime),str(checkpoint),'5',sha(inp),sha(meta)],log);checkpoint_sha=sha(checkpoint);runs=[]
  for partition in [[5],[2,3]]:
   carry=rhs.copy();residues=[0]*nrows;power=1;iteration=0;all_digits=[]
   for steps in partition:
    residual=job/(base+'-residual.txt');out=job/(base+'-step.json');residual.write_text(str(cols)+' '+str(nrows)+' '+str(iteration)+'\n'+' '.join(map(str,carry))+'\n')
    call([str(job/'four_frame_dixon_step'),str(inp),str(out),str(prime),str(checkpoint),sha(inp),sha(meta),str(residual),str(steps)],log);data=json.loads(out.read_text());assert data['consistent'] and data['start_iteration']==iteration and data['end_iteration']==iteration+steps
    for delta in data['digits']:
     assert len(delta)==nrows and all(0<=d<prime for d in delta)
     raw=[carry[j]-sum(delta[i]*rows[i][j] for i in range(nrows)) for j in range(cols)];assert all(v%prime==0 for v in raw);carry=[v//prime for v in raw]
     residues=[a+power*d for a,d in zip(residues,delta)];power*=prime;iteration+=1
     assert [rhs[j]-sum(residues[i]*rows[i][j] for i in range(nrows)) for j in range(cols)]==[power*v for v in carry]
     all_digits.append(delta)
    assert carry==data['carry']
   rational=[reconstruct(a,power) for a in residues];assert all(r is not None for r in rational)
   rational=[s.Rational(n,d) for n,d in rational];assert list(s.Matrix(rows).T*s.Matrix(rational))==rhs
   expected=list(s.Matrix(rows[:3]).T.gauss_jordan_solve(s.Matrix(rhs))[0])+[s.Integer(0)]*(nrows-3);assert rational==expected
   runs.append((all_digits,carry,residues))
  assert runs[0]==runs[1] and sha(checkpoint)==checkpoint_sha
  if label=='rectangular':
   residual.write_text(str(cols)+' '+str(nrows)+' 0\n0 0 0 1\n');call([str(job/'four_frame_dixon_step'),str(inp),str(out),str(prime),str(checkpoint),sha(inp),sha(meta),str(residual),'1'],log);data=json.loads(out.read_text());assert not data['consistent'] and data['failed_iteration']==0
  residual.write_text(str(cols)+' '+str(nrows)+' 0\n'+' '.join(['9223372036854775807']+['0']*(cols-1))+'\n');call([str(job/'four_frame_dixon_step'),str(inp),str(out),str(prime),str(checkpoint),sha(inp),sha(meta),str(residual),'1'],log,10)
 results.append({'case':label,'integer_carry_identity_every_digit':True,'chunked_equals_uninterrupted':True,'independent_exact_rational_solution':True,'checkpoint_unchanged':True,'out_of_bound_carry_rejected':True,'inconsistent_rhs_rejected':label=='rectangular'})
# A coefficient magnitude that makes the carry arithmetic unsafe must be rejected before stepping.
base='four-frame-dixon-test-overflow';inp=job/(base+'.matrix');meta=job/(base+'-metadata.json');checkpoint=job/(base+'.checkpoint');summary=job/(base+'-checkpoint.json');residual=job/(base+'-residual.txt');out=job/(base+'-step.json');inp.write_text('2 2\n1 0 9223372036854775807\n1 1 1\n');meta.write_text('{}\n');residual.write_text('2 2 0\n1 0\n')
if checkpoint.exists():checkpoint.unlink()
with (job/(base+'.log')).open('w') as log:
 call([str(job/'four_frame_macaulay_continue'),str(inp),str(summary),'97',str(checkpoint),'5',sha(inp),sha(meta)],log)
 call([str(job/'four_frame_dixon_step'),str(inp),str(out),'97',str(checkpoint),sha(inp),sha(meta),str(residual),'1'],log,8)
results.append({'case':'overflow','unsafe_arithmetic_bound_rejected':True})
(job/'four-frame-dixon-validation.json').write_text(json.dumps(results,indent=2)+'\n');print(json.dumps(results))
