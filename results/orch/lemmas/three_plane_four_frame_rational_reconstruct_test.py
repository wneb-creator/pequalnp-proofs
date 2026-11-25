from pathlib import Path
import random,json,subprocess,resource,math
job=Path('/tmp/oec/pequalnp-pilot-79');env={'PATH':'/usr/bin:/bin','LANG':'C','LC_ALL':'C','OMP_NUM_THREADS':'1'};resource.setrlimit(resource.RLIMIT_CORE,(0,0));rng=random.Random(790231)
def limits():resource.setrlimit(resource.RLIMIT_CORE,(0,0));resource.setrlimit(resource.RLIMIT_AS,(256*1024**2,256*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(10,10))
def reconstruct(a,m):
 if a==0:return(0,1)
 bound=math.isqrt(m//2);r0,r1=m,a;t0,t1=0,1
 while abs(r1)>bound:
  q=r0//r1;r0,r1=r1,r0-q*r1;t0,t1=t1,t0-q*t1
 if t1<0:r1,t1=-r1,-t1
 if 0<t1<=bound and math.gcd(r1,t1)==1 and (r1-a*t1)%m==0:return(r1,t1)
 return None
results=[]
with (job/'four-frame-rational-reconstruct-test-child.log').open('w') as log:
 for power in [1,4,16,64,128]:
  modulus=1000000007**power;bound=math.isqrt(modulus//2);values=[0,1,modulus-1]+[rng.randrange(modulus) for _ in range(100)];known={}
  for _ in range(100):
   n=rng.randrange(-bound//4,bound//4);d=rng.randrange(1,max(2,bound//4));g=math.gcd(n,d);n//=g;d//=g
   if math.gcd(d,modulus)!=1:continue
   a=n*pow(d,-1,modulus)%modulus;known[len(values)]=(n,d);values.append(a)
  inp=job/'four-frame-rational-reconstruct-test-input.txt';out=job/'four-frame-rational-reconstruct-test-output.json';inp.write_text(str(len(values))+' '+hex(modulus)+'\n'+'\n'.join(hex(a) for a in values)+'\n');subprocess.run([str(job/'four_frame_rational_reconstruct'),str(inp),str(out)],stdout=log,stderr=subprocess.STDOUT,env=env,preexec_fn=limits,timeout=10,check=True);raw=json.loads(out.read_text())['fractions'];got=[None if r is None else tuple(int(h,16) for h in r) for r in raw];expected=[reconstruct(a,modulus) for a in values];assert got==expected
  for i,r in known.items():assert got[i]==r
  results.append({'modulus_bits':modulus.bit_length(),'cases':len(values),'matches_python_euclid':True,'known_rationals_recovered':len(known)})
 # Reject an out-of-range residue instead of silently reducing it.
 inp.write_text('1 0x61\n0x61\n');p=subprocess.run([str(job/'four_frame_rational_reconstruct'),str(inp),str(out)],stdout=log,stderr=subprocess.STDOUT,env=env,preexec_fn=limits,timeout=10);assert p.returncode==6
(job/'four-frame-rational-reconstruct-validation.json').write_text(json.dumps({'cases':results,'out_of_range_rejected':True},indent=2)+'\n');print(json.dumps(results))
