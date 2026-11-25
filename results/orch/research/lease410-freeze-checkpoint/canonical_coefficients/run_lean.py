from pathlib import Path
import sys,subprocess,resource,time,json,datetime

source=Path(sys.argv[1]).resolve()
prefix=Path(sys.argv[2]).resolve()
assert source.is_relative_to('/tmp/oec/pequalnp-pilot-78/canonical_coefficients')
assert prefix.is_relative_to('/tmp/oec/pequalnp-pilot-78/canonical_coefficients')
started=datetime.datetime.now(datetime.timezone.utc).isoformat()
wall=time.monotonic()
extra=[]
def disable_core():resource.setrlimit(resource.RLIMIT_CORE,(0,0))
preexec=disable_core
if len(sys.argv)>3:
    memory=int(sys.argv[3]);assert 512<=memory<=4096
    output=source.with_suffix('.olean')
    extra=[str(memory),str(output),str(source.parent)]
    def cap_output():
        disable_core()
        resource.setrlimit(resource.RLIMIT_FSIZE,(12*1024*1024,12*1024*1024))
    preexec=cap_output
command='source /tmp/oec/pequalnp-pilot-78/toolchain/env.sh && exec nice -n 5 lake env lean "$1"'
if extra:
    command='source /tmp/oec/pequalnp-pilot-78/toolchain/env.sh && exec nice -n 5 lake env lean -M "$2" -R "$4" -o "$3" "$1"'
with Path(str(prefix)+'.stdout').open('wb') as out,Path(str(prefix)+'.stderr').open('wb') as err:
    proc=subprocess.run(['/bin/bash','-c',command,'canonical-lean',str(source),*extra],
        cwd='/workspace/pequalnp-proofs/lean',stdout=out,stderr=err,preexec_fn=preexec)
usage=resource.getrusage(resource.RUSAGE_CHILDREN)
result={'source':str(source),'utc_started':started,'exit_code':proc.returncode,
        'seconds':time.monotonic()-wall,'peak_rss_kib':usage.ru_maxrss,
        'user_seconds':usage.ru_utime,'system_seconds':usage.ru_stime,
        'stdout_bytes':Path(str(prefix)+'.stdout').stat().st_size,
        'stderr_bytes':Path(str(prefix)+'.stderr').stat().st_size}
Path(str(prefix)+'.result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
sys.exit(proc.returncode)
