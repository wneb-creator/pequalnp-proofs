from pathlib import Path
import subprocess,resource,time,json,hashlib
base=Path('/tmp/oec/pequalnp-pilot-78/geometry_search/rowzero')
source=(base/'trace-Bzero.sing').read_text()
assert source.count('ideal G=slimgb(I);')==1
script=source.replace('ideal G=slimgb(I);','ideal G=std(I);')
path=base/'trace-Bzero-std.sing';path.write_text(script)
native=Path('/tmp/oec/pequalnp-pilot-78/numeric')
env={'LD_LIBRARY_PATH':str(native/'singular/lib')+':'+str(native/'cas/lib'),'OPENBLAS_NUM_THREADS':'1','OMP_NUM_THREADS':'1'}
def limits():
 resource.setrlimit(resource.RLIMIT_AS,(256*2**20,256*2**20))
 resource.setrlimit(resource.RLIMIT_CPU,(60,65))
 resource.setrlimit(resource.RLIMIT_FSIZE,(16*2**20,16*2**20))
 resource.setrlimit(resource.RLIMIT_CORE,(0,0))
start=time.monotonic()
with (base/'trace-Bzero-std.stdout').open('w') as out,(base/'trace-Bzero-std.stderr').open('w') as err:
 try:
  result=subprocess.run([str(native/'singular/bin/Singular'),'--quiet','--no-tty','--no-rc','--no-shell','--cpus=1','--threads=1','--flint-threads=1',str(path)],stdin=subprocess.DEVNULL,stdout=out,stderr=err,env=env,preexec_fn=limits,timeout=75)
  exit_code=result.returncode
 except subprocess.TimeoutExpired:exit_code='wall_timeout'
report={'exit_code':exit_code,'seconds':time.monotonic()-start,'memory_limit_mib':256,'cpu_limit_seconds':60,'algorithm':'exact QQ std','input_sha256':hashlib.sha256(script.encode()).hexdigest()}
(base/'trace-Bzero-std-result.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report),flush=True)
