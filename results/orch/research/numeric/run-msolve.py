from pathlib import Path
import json,os,resource,subprocess,time,sys

base=Path('/tmp/oec/pequalnp-pilot-78/numeric')
chart=sys.argv[1] if len(sys.argv)>1 else '047'
prime=sys.argv[2] if len(sys.argv)>2 else '101'
budget=int(sys.argv[3]) if len(sys.argv)>3 else 60
variant=sys.argv[4] if len(sys.argv)>4 else 'batch'
memory_mib=int(sys.argv[5]) if len(sys.argv)>5 else 3072
architecture=sys.argv[6] if len(sys.argv)>6 else 'baseline'
name=f'chart-{chart}-p{prime}-{variant}'+('' if architecture=='baseline' else '-'+architecture)
env=os.environ.copy();env['OPENBLAS_NUM_THREADS']='1';env['OMP_NUM_THREADS']='1'
executable=base/'cas/bin/msolve'
if architecture=='avx2':
    executable=base/'cas-avx2/bin/msolve'
    env['LD_LIBRARY_PATH']=str(base/'cas-avx2/lib')+':'+str(base/'cas/lib')
def limits():
    resource.setrlimit(resource.RLIMIT_AS,(memory_mib*2**20,memory_mib*2**20))
    resource.setrlimit(resource.RLIMIT_CPU,(budget,budget+5))
start=time.monotonic()
with (base/f'{name}.stdout').open('w') as out,(base/f'{name}.stderr').open('w') as err:
    try:
        command=[str(executable),'-f',str(base/f'chart-{chart}-p{prime}.ms'),'-o',str(base/f'{name}.out'),'-l','2','-t','1','-v','2','-m','512']
        if variant=='signature':command+=['-q','1']
        if prime=='0':command+=['-P','1']
        else:command+=['-g','2']
        p=subprocess.run(command,stdout=out,stderr=err,env=env,preexec_fn=limits,timeout=budget+30)
        code=p.returncode
    except subprocess.TimeoutExpired:
        code='timeout'
result={'chart':chart,'characteristic':int(prime),'variant':variant,'architecture':architecture,'memory_mib':memory_mib,'budget_seconds':budget,'seconds':time.monotonic()-start,'exit':code}
(base/f'{name}.result.json').write_text(json.dumps(result,indent=2));print(json.dumps(result),flush=True)
