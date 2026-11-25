from pathlib import Path
import json,sys,subprocess,resource,time,math,sympy as s
job=Path('/tmp/oec/pequalnp-pilot-79');chart=int(sys.argv[1]);count=int(sys.argv[2]);base='centered-two-macaulay-'+str(chart)+'-d9';statepath=job/(base+'-crt-state.json')
state=json.loads(statepath.read_text()) if statepath.exists() else {'modulus':1,'residues':None,'primes':[],'fingerprint':None,'next_prime':1000000007}
def limits():resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3));resource.setrlimit(resource.RLIMIT_CPU,(120,120))
def reconstruct(a,m):
 if a==0:return (0,1)
 bound=math.isqrt(m//2);r0,r1=m,a;t0,t1=0,1
 while abs(r1)>bound:
  q=r0//r1;r0,r1=r1,r0-q*r1;t0,t1=t1,t0-q*t1
 if t1<0:r1,t1=-r1,-t1
 if 0<t1<=bound and math.gcd(r1,t1)==1 and (r1-a*t1)%m==0:return(r1,t1)
 return None

def verify_exact(coeffs):
 denominator=1
 for _,d in coeffs:denominator=math.lcm(denominator,d)
 integers=[n*(denominator//d) for n,d in coeffs]
 with (job/(base+'.matrix')).open() as f:
  cols,rows=map(int,next(f).split());assert len(integers)==rows;out=[0]*cols
  for weight,line in zip(integers,f):
   if not weight:continue
   vals=list(map(int,line.split()))
   for j in range(vals[0]):out[vals[1+2*j]]+=weight*vals[2+2*j]
 if out!=[0]*(cols-1)+[denominator]:return False
 (job/(base+'-exact-certificate.json')).write_text(json.dumps({'classification':'Exact integer polynomial certificate verified by standalone arithmetic; not Lean checked','denominator':denominator,'coefficients':integers,'primes':state['primes'],'fingerprint':state['fingerprint']},separators=(',',':'))+'\n')
 print(json.dumps({'stage':'EXACT_CERTIFICATE_VERIFIED','chart':chart,'support':sum(n!=0 for n in integers),'denominator_bits':denominator.bit_length(),'max_coefficient_bits':max(abs(n).bit_length() for n in integers)}),flush=True)
 return True
previous_reconstructed={}
for trial in range(count):
 prime=int(state['next_prime']);state['next_prime']=int(s.nextprime(prime));name=base+'-p'+str(prime);start=time.monotonic()
 with (job/(name+'.log')).open('w') as log:
  proc=subprocess.Popen([str(job/'macaulay_witness'),str(job/(base+'.matrix')),str(job/(name+'-witness.json')),str(prime)],stdout=log,stderr=subprocess.STDOUT,preexec_fn=limits)
  try:code=proc.wait(timeout=120)
  except subprocess.TimeoutExpired:proc.kill();code=proc.wait();print(json.dumps({'stage':'timeout','prime':prime}),flush=True);break
 if code!=0:print(json.dumps({'stage':'failed','prime':prime,'exit':code}),flush=True);break
 result=json.loads((job/(name+'-witness.json')).read_text());assert isinstance(result,dict)
 if not result['unit']:print(json.dumps({'stage':'no_unit','prime':prime}),flush=True);continue
 if state['fingerprint'] is None:state['fingerprint']=result['fingerprint']
 if state['fingerprint']!=result['fingerprint']:print(json.dumps({'stage':'bad_pattern','prime':prime}),flush=True);continue
 witness=result['witness'];m=state['modulus'];residues=state['residues']
 if residues is None:residues=[0]*len(witness)
 assert len(residues)==len(witness)
 inverse=pow(m,-1,prime);residues=[a+m*((b-a)*inverse%prime) for a,b in zip(residues,witness)]
 state['modulus']=m*prime;state['residues']=residues;state['primes'].append(prime);temporary=statepath.with_suffix('.tmp');temporary.write_text(json.dumps(state,separators=(',',':'))+'\n');temporary.replace(statepath)
 reconstructed=[];failed=0
 for a in residues:
  r=reconstruct(a,state['modulus'])
  if r is None:failed+=1
  reconstructed.append(r)
 accepted={k:r for k,r in enumerate(reconstructed) if r is not None and r[0]!=0};stable=sum(previous_reconstructed.get(k)==r for k,r in accepted.items());previous_reconstructed=accepted
 heights=sorted((max(abs(n).bit_length(),d.bit_length()) for n,d in accepted.values()))
 print(json.dumps({'stage':'crt','chart':chart,'primes':len(state['primes']),'modulus_bits':state['modulus'].bit_length(),'unreconstructed':failed,'accepted_nonzero':len(accepted),'stable_nonzero':stable,'accepted_height_range':([heights[0],heights[len(heights)//2],heights[-1]] if heights else []),'seconds':time.monotonic()-start}),flush=True)
 if failed==0 and verify_exact(reconstructed):break
