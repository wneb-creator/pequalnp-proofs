from pathlib import Path
import subprocess,sys,time,json,resource
root=Path('/tmp/oec/pequalnp-pilot-87')
src=Path(sys.argv[1]).resolve();log=Path(sys.argv[2]).resolve()
r=subprocess.run(['rg','--files','-g','*.olean','-g','!elan/**'],cwd=root,text=True,capture_output=True,check=True)
dirs=sorted({str((root/x).parent) for x in r.stdout.splitlines()})
paths=':'.join([str(src.parent)]+dirs)
cmd=[str(root/'lean-env.sh'),'lake','env','bash','-c','export LEAN_PATH="${LEAN_PATH}:$1"; exec lean -R "$2" -o "$3" "$4"','--',paths,str(src.parent),str(src.with_suffix('.olean')),str(src)]
t=time.monotonic()
with log.open('w') as f:
 p=subprocess.run(cmd,cwd='/workspace/pequalnp-proofs/lean',stdout=f,stderr=subprocess.STDOUT)
status=dict(source=str(src),log=str(log),exit=p.returncode,seconds=time.monotonic()-t,maxrss_kb=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss)
log.with_suffix('.status.json').write_text(json.dumps(status,indent=2));print(json.dumps(status));sys.exit(p.returncode)
