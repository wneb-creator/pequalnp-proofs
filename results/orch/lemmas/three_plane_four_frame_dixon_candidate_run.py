from pathlib import Path
import subprocess,resource,time,json,hashlib,os,signal,sys,fcntl,math,datetime,sympy as s
job=Path('/tmp/oec/pequalnp-pilot-79');base='four-frame-power-triangle-d7-n2';label=sys.argv[1];assert label in ('cross','square');prime=1000000007
batch_steps=int(sys.argv[2]);time_budget=float(sys.argv[3]);max_batches=int(sys.argv[4]) if len(sys.argv)>4 else 10000;assert 1<=batch_steps<=20 and 1<=time_budget<=600 and 1<=max_batches<=10000
matrix=job/(base+'.matrix');metafile=job/(base+'-metadata.json');metadata=json.loads(metafile.read_text());source=job/'four-frame-cubic-triangle-0.msolve'
checkpoint=job/(base+'-path-final-checkpoint.bin');prefix=base+'-'+label+'-candidate-dixon';statepath=job/(prefix+'-state.json');outpath=job/(prefix+'-step.json');residualpath=job/(prefix+'-residual.txt')
lock=(job/(prefix+'.lock')).open('a+');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
ordinary_env={'PATH':'/usr/bin:/bin','LANG':'C','LC_ALL':'C','OMP_NUM_THREADS':'1'};resource.setrlimit(resource.RLIMIT_CORE,(0,0));limit=2*1024**3;started=time.monotonic();runid=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ');peak=0;records=[];reason='budget_exhausted'
def sha(path):
 h=hashlib.sha256()
 with path.open('rb') as f:
  for block in iter(lambda:f.read(1048576),b''):h.update(block)
 return h.hexdigest()
specpath=job/'four-frame-dixon-candidates.json';spec_hash=sha(specpath);spec=json.loads(specpath.read_text());assert spec['variables']==metadata['variables'];target_terms=spec['candidates'][label]['terms'];target={}
for term in target_terms:
 mon=tuple(term['exponents']);coefficient=term['coefficient'];assert len(mon)==10 and all(isinstance(e,int) and e>=0 for e in mon) and isinstance(coefficient,int) and coefficient!=0 and mon not in target;target[mon]=coefficient
assert target;rhs=[target.get(tuple(m),0) for m in metadata['columns']];assert sum(c!=0 for c in rhs)==len(target)
assert sha(specpath)==spec_hash
def atomic_json(path,data):
 tmp=Path(str(path)+'.tmp');tmp.write_text(json.dumps(data,separators=(',',':'))+'\n');tmp.replace(path)
def limits():
 resource.setrlimit(resource.RLIMIT_CORE,(0,0));resource.setrlimit(resource.RLIMIT_AS,(limit,limit));resource.setrlimit(resource.RLIMIT_CPU,(120,120))
def rss(pid):
 try:
  for line in (Path('/proc')/str(pid)/'status').read_text().splitlines():
   if line.startswith('VmRSS:'):return int(line.split()[1])*1024
 except FileNotFoundError:pass
 return 0
def reconstruct(a,m):
 if a==0:return (0,1)
 bound=math.isqrt(m//2);r0,r1=m,a;t0,t1=0,1
 while abs(r1)>bound:
  q=r0//r1;r0,r1=r1,r0-q*r1;t0,t1=t1,t0-q*t1
 if t1<0:r1,t1=-r1,-t1
 if 0<t1<=bound and math.gcd(r1,t1)==1 and (r1-a*t1)%m==0:return(r1,t1)
 return None

def matrix_product(weights):
 with matrix.open() as f:
  cols,rows=map(int,next(f).split());assert len(weights)==rows;result=[0]*cols;count=0
  for weight,line in zip(weights,f):
   count+=1;terms=list(map(int,line.split()));assert len(terms)==1+2*terms[0]
   if weight:
    for j in range(terms[0]):
     index,coeff=terms[1+2*j:3+2*j];assert 0<=index<cols;result[index]+=weight*coeff
  assert count==rows and not f.read().strip()
 return result

def verify_original(weights,denominator):
 lines=source.read_text().splitlines();names=lines[0].split(',');assert names[-1]=='v' and names[:-1]==metadata['variables'];vs=s.symbols(' '.join(names));body='\n'.join(lines[2:]);assert all(c.isalnum() or c in ' _+-*^,()\n' for c in body);local=dict(zip(names,vs));raw=[s.Poly(s.sympify(q.strip().replace('^','**'),locals=local),*vs,domain=s.ZZ) for q in body.split(',') if q.strip()];assert len(raw)==17;polys=[]
 for p in raw[:-1]:
  assert all(m[-1]==0 for m,c in p.terms());polys.append({m[:-1]:int(c) for m,c in p.terms()})
 origins=metadata['row_origins'];assert len(weights)==len(origins);out={}
 for w,(i,mult) in zip(weights,origins):
  if not w:continue
  assert 0<=i<len(polys) and len(mult)==10 and all(isinstance(e,int) and e>=0 for e in mult)
  for mon,c in polys[i].items():
   key=tuple(a+b for a,b in zip(mon,mult));out[key]=out.get(key,0)+w*c
 assert {m:c for m,c in out.items() if c}=={m:c*denominator for m,c in target.items()}

def exact_candidate(fractions,modulus):
 denominator=1
 for n,d in fractions:
  denominator=math.lcm(denominator,d)
  if denominator.bit_length()>modulus.bit_length():return None
 integers=[n*(denominator//d) for n,d in fractions]
 wanted=[denominator*c for c in rhs]
 if matrix_product(integers)!=wanted:return None
 verify_original(integers,denominator)
 # Hex stores arbitrary-size integers without decimal string limits.
 certificate={'classification':'Exact rational certificate verified against matrix and original polynomials; not Lean checked','binding':binding,'iterations':state['iteration'],'target_terms':target_terms,'denominator_hex':hex(denominator),'coefficients_hex':[hex(n) for n in integers]}
 atomic_json(job/(prefix+'-exact-certificate.json'),certificate)
 return {'support':sum(n!=0 for n in integers),'denominator_bits':denominator.bit_length(),'max_coefficient_bits':max(abs(n).bit_length() for n in integers)}

binding={'matrix_sha256':sha(matrix),'metadata_sha256':sha(metafile),'source_sha256':sha(source),'checkpoint_sha256':sha(checkpoint),'prime':prime,'target_terms':target_terms,'spec_sha256':spec_hash}
with matrix.open() as f:cols,rows=map(int,next(f).split())
if statepath.exists():
 state=json.loads(statepath.read_text());assert state['binding']==binding;iteration=state['iteration'];assert isinstance(iteration,int) and 0<=iteration<=1000000;residues=[int(h,16) for h in state['residues_hex']];carry=state['carry'];assert len(residues)==rows and len(carry)==cols and all(isinstance(c,int) for c in carry);power=pow(prime,iteration);assert all(0<=x<power for x in residues)
 # Every resumed state is checked against the original integer system.
 actual=matrix_product(residues);assert [rhs[j]-actual[j] for j in range(cols)]==[power*c for c in carry]
else:
 iteration=0;residues=[0]*rows;carry=rhs.copy();power=1;state={'binding':binding,'iteration':iteration,'residues_hex':[hex(v) for v in residues],'carry':carry};atomic_json(statepath,state)
previous_candidates=None
for batch in range(1,max_batches+1):
 remaining=time_budget-(time.monotonic()-started)
 if remaining<15:break
 residualpath.write_text(str(cols)+' '+str(rows)+' '+str(iteration)+'\n'+' '.join(map(str,carry))+'\n');logpath=job/(prefix+'-'+runid+'-'+str(batch)+'.log');start=time.monotonic();status='finished';wall=min(120,remaining-5)
 with logpath.open('w') as log:
  proc=subprocess.Popen([str(job/'four_frame_dixon_step'),str(matrix),str(outpath),str(prime),str(checkpoint),binding['matrix_sha256'],binding['metadata_sha256'],str(residualpath),str(batch_steps)],stdout=log,stderr=subprocess.STDOUT,env=ordinary_env,preexec_fn=limits,start_new_session=True)
  while proc.poll() is None:
   peak=max(peak,rss(proc.pid))
   if peak>limit:status='memory_limit'
   elif time.monotonic()-start>wall:status='batch_timeout'
   if status!='finished':os.killpg(proc.pid,signal.SIGKILL);break
   time.sleep(.2)
  code=proc.wait()
 record={'batch':batch,'status':status,'exit':code,'seconds':time.monotonic()-start,'peak_rss_bytes':peak,'log':str(logpath)}
 if code!=0 or status!='finished':reason=status if status!='finished' else 'process_failure'
 else:
  data=json.loads(outpath.read_text())
  if not data['consistent']:reason='residual_not_in_modular_row_span';record['failed_iteration']=data['failed_iteration']
  else:
   assert data['prime']==prime and data['start_iteration']==iteration and data['end_iteration']==iteration+batch_steps and len(data['digits'])==batch_steps
   delta=[0]*rows;factor=1
   for digit in data['digits']:
    assert len(digit)==rows and all(isinstance(d,int) and 0<=d<prime for d in digit);delta=[a+factor*d for a,d in zip(delta,digit)];factor*=prime
   newcarry=data['carry'];assert len(newcarry)==cols and all(isinstance(c,int) for c in newcarry)
   product=matrix_product(delta);assert [carry[j]-product[j] for j in range(cols)]==[factor*c for c in newcarry]
   residues=[a+power*d for a,d in zip(residues,delta)];power*=factor;carry=newcarry;iteration+=batch_steps
   assert sha(matrix)==binding['matrix_sha256'] and sha(metafile)==binding['metadata_sha256'] and sha(source)==binding['source_sha256'] and sha(checkpoint)==binding['checkpoint_sha256'] and sha(specpath)==binding['spec_sha256']
   state={'binding':binding,'iteration':iteration,'residues_hex':[hex(v) for v in residues],'carry':carry};atomic_json(statepath,state)
   candidates=[reconstruct(a,power) for a in residues];failed=sum(c is None for c in candidates);stable=sum(c is not None and c[0]!=0 and previous_candidates is not None and c==previous_candidates[i] for i,c in enumerate(candidates));nonzero=sum(c is not None and c[0]!=0 for c in candidates)
   record.update({'iteration':iteration,'modulus_bits':power.bit_length(),'unreconstructed':failed,'reconstructed_nonzero':nonzero,'stable_nonzero':stable,'integer_batch_identity_verified':True})
   if failed==0 and previous_candidates==candidates:
    exact=exact_candidate(candidates,power)
    if exact is not None:record['exact_certificate']=exact;reason='exact_certificate_verified'
   previous_candidates=candidates
 records.append(record);print(json.dumps(record),flush=True)
 summary={'classification':'Dixon lifting with exact batch verification; rational proof only if exact_certificate_verified','binding':binding,'records':records,'reason':reason,'elapsed_seconds':time.monotonic()-started,'peak_rss_bytes':peak};atomic_json(job/(prefix+'-run.json'),summary)
 if reason!='budget_exhausted':break
summary={'classification':'Dixon lifting with exact batch verification; rational proof only if exact_certificate_verified','binding':binding,'records':records,'reason':reason,'elapsed_seconds':time.monotonic()-started,'peak_rss_bytes':peak};atomic_json(job/(prefix+'-run.json'),summary);atomic_json(job/(prefix+'-run-'+runid+'.json'),summary);print(json.dumps({'final':True,'reason':reason,'iteration':iteration,'elapsed_seconds':time.monotonic()-started,'peak_rss_bytes':peak}),flush=True)
