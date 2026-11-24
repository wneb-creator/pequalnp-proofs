from pathlib import Path
import hashlib,json,subprocess,resource,time,os
H=Path('/tmp/oec/pequalnp-pilot-18/orch/S05');R=H/'allnegative-best4-direct21-v1';B=H.parent/'MAIN/all-negative-engine-v1/circuit_anneal_allnegative'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(B)=='7d802a63b218449bd58178785a917a363edecedace5f65201344804dec3a3870'
assert sha(R/'direct-seeds.txt')=='f1316079fdd1c50eab3387c00ed7460130da5c6b862937241fa41b9ff13742a6'
cmd=[str(B),'--pack',str(R/'direct-seeds.txt'),'--output',str(R/'selftest.json'),'--seed','134230','--self-test']
def limits():
 resource.setrlimit(resource.RLIMIT_CPU,(3,3));resource.setrlimit(resource.RLIMIT_AS,(256*1024*1024,256*1024*1024));os.nice(10)
t=time.monotonic()
with (R/'selftest.stdout').open('x') as out,(R/'selftest.stderr').open('x') as err:p=subprocess.run(cmd,stdout=out,stderr=err,timeout=8,preexec_fn=limits)
result=dict(command=cmd,exit_code=p.returncode,elapsed_seconds=time.monotonic()-t,limits=dict(cpu_seconds=3,address_space_MiB=256,wall_seconds=8),binary_sha256=sha(B),pack_sha256=sha(R/'direct-seeds.txt'),script_sha256=sha(Path(__file__)),production_search=False)
(R/'selftest-result.json').write_text(json.dumps(result,indent=2)+'\n');assert p.returncode==0
assert json.load(open(R/'selftest.json'))['status']=='SELF_TEST_DIRECT21_PASS'
print(json.dumps(result));print((R/'selftest.json').read_text())
