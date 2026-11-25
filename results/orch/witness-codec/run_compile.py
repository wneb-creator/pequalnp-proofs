import json,os,subprocess,sys,time
from pathlib import Path
root=Path(__file__).resolve().parent
name=sys.argv[1]
start=time.monotonic()
with (root/(name+".compile.txt")).open("w") as output:
 result=subprocess.run(["/tmp/oec/pequalnp-pilot-87/lean-env.sh","lake","env","lean","-R",str(root),"-o",str(root/(name+".olean")),str(root/(name+".lean"))],cwd="/workspace/pequalnp-proofs/lean",stdout=output,stderr=subprocess.STDOUT,env=dict(os.environ,LEAN_PATH=str(root)))
status=dict(module=name,exit_code=result.returncode,elapsed_seconds=time.monotonic()-start)
(root/(name+".status.json")).write_text(json.dumps(status,indent=2)+"\n")
print(json.dumps(status))
sys.exit(result.returncode)
