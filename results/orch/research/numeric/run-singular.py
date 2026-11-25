from pathlib import Path
import json,os,resource,subprocess,time,sys

base=Path('/tmp/oec/pequalnp-pilot-78/numeric')
chart=sys.argv[1]
budget=int(sys.argv[2]) if len(sys.argv)>2 else 120
kind=sys.argv[3] if len(sys.argv)>3 else 'std'
source=(base/f'chart-{chart}-p0.ms').read_text().splitlines()
assert source[1]=='0'
name=f'singular-{chart}-{kind}'
script='ring r=0,('+source[0]+'),dp;\noption(redSB);\nideal I='+''.join(source[2:])+';\n'
if kind=='lift':
    script+='matrix T; ideal G=liftstd(I,T);\nprint("BASIS_SIZE");size(G);\n'
    script+='if(size(G)==1 && G[1]==1){matrix C=lift(G,ideal(1));matrix W=T*C;print("CERTIFICATE");print(W);print("RESIDUAL");print(matrix(I)*W-matrix(ideal(1)));}\n'
else:
    script+='ideal G=std(I);\nprint("BASIS_SIZE");size(G);\nprint("DIMENSION");dim(G);\nprint("UNIT_IDEAL");(size(G)==1 && G[1]==1);\n'
script+='quit;\n'
(base/f'{name}.sing').write_text(script)
env=os.environ.copy()
env['LD_LIBRARY_PATH']=str(base/'singular/lib')+':'+str(base/'cas/lib')
env['OPENBLAS_NUM_THREADS']='1';env['OMP_NUM_THREADS']='1'
def limits():
    resource.setrlimit(resource.RLIMIT_AS,(3072*2**20,3072*2**20))
    resource.setrlimit(resource.RLIMIT_CPU,(budget,budget+5))
    resource.setrlimit(resource.RLIMIT_FSIZE,(16*2**20,16*2**20))
    resource.setrlimit(resource.RLIMIT_CORE,(0,0))
start=time.monotonic()
with (base/f'{name}.stdout').open('w') as out,(base/f'{name}.stderr').open('w') as err:
    try:
        p=subprocess.run([str(base/'singular/bin/Singular'),'--quiet','--no-tty','--no-rc','--no-shell','--cpus=1','--threads=1','--flint-threads=1',str(base/f'{name}.sing')],stdin=subprocess.DEVNULL,stdout=out,stderr=err,env=env,preexec_fn=limits,timeout=budget+30)
        code=p.returncode
    except subprocess.TimeoutExpired:
        code='timeout'
result={'chart':chart,'algorithm':kind,'memory_mib':3072,'budget_seconds':budget,'seconds':time.monotonic()-start,'exit':code}
(base/f'{name}.result.json').write_text(json.dumps(result,indent=2))
print(json.dumps(result),flush=True)
