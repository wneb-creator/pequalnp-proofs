from pathlib import Path
import subprocess,resource,time,json,sys,hashlib
base=Path('/tmp/oec/pequalnp-pilot-78/geometry_search/rowzero')
native=Path('/tmp/oec/pequalnp-pilot-78/numeric')
env={'LD_LIBRARY_PATH':str(native/'singular/lib')+':'+str(native/'cas/lib'),'OPENBLAS_NUM_THREADS':'1','OMP_NUM_THREADS':'1'}
algorithm=sys.argv[1] if len(sys.argv)>1 else 'std'
assert algorithm in ['std','lift','lift2']
def limits():
 resource.setrlimit(resource.RLIMIT_AS,(256*2**20,256*2**20))
 resource.setrlimit(resource.RLIMIT_CPU,(60,65))
 resource.setrlimit(resource.RLIMIT_FSIZE,(16*2**20,16*2**20))
 resource.setrlimit(resource.RLIMIT_CORE,(0,0))
results=[]
for name in ['same','different01','different02','different12']:
 source=(base/f'Bzero-boundary-{name}.sing').read_text()
 if algorithm.startswith('lift'):
  source=source.split('ideal G=std(I);',1)[0]
  source+='matrix T;ideal G=liftstd(I,T);print("BASIS_SIZE");size(G);print("BASIS");G;\n'
  if algorithm=='lift':
   source+='if(size(G)==1 && G[1]==1){print("CERTIFICATE_START");int j;for(j=1;j<=nrows(T);j++){print(string(T[j,1]));}print("CERTIFICATE_END");print("VERIFIED");matrix(I)*T==matrix(G);}\nquit;\n'
  else:
   source+='short=0;if(size(G)==1 && deg(G[1])==0 && G[1]!=0){print("CERTIFICATE_TARGET");print(string(G[1]));print("CERTIFICATE_START");int j;for(j=1;j<=nrows(T);j++){print(string(T[j,1]));}print("CERTIFICATE_END");print("VERIFIED");matrix(I)*T==matrix(G);}\nquit;\n'
  path=base/f'Bzero-boundary-{name}-{algorithm}.sing';path.write_text(source)
 else:path=base/f'Bzero-boundary-{name}.sing'
 prefix=f'Bzero-boundary-{name}-{algorithm}'
 start=time.monotonic()
 with (base/f'{prefix}.stdout').open('w') as out,(base/f'{prefix}.stderr').open('w') as err:
  try:
   p=subprocess.run([str(native/'singular/bin/Singular'),'--quiet','--no-tty','--no-rc','--no-shell','--cpus=1','--threads=1','--flint-threads=1',str(path)],stdin=subprocess.DEVNULL,stdout=out,stderr=err,env=env,preexec_fn=limits,timeout=75)
   exit_code=p.returncode
  except subprocess.TimeoutExpired:exit_code='wall_timeout'
 result={'case':name,'algorithm':algorithm,'exit_code':exit_code,'seconds':time.monotonic()-start,'input_sha256':hashlib.sha256(source.encode()).hexdigest(),'memory_limit_mib':256,'cpu_limit_seconds':60}
 (base/f'{prefix}.result.json').write_text(json.dumps(result,indent=2)+'\n')
 results.append(result);print(json.dumps(result),flush=True)
(base/f'Bzero-boundaries-{algorithm}-results.json').write_text(json.dumps(results,indent=2)+'\n')
