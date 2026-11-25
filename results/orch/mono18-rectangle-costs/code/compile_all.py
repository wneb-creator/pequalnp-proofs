from pathlib import Path
import subprocess,json,shutil,hashlib,time,sys
p=Path(__file__).resolve().parent;archive=Path('/workspace/pequalnp-proofs/results/orch/lemmas');plan=json.loads((p/'compile-plan.json').read_text());status=[]
for name in plan:
 src=p/name;log=p/(src.stem+'-attempt1.txt')
 if name=='Mono18RectangleCost14.lean':log=p/'cost14-attempt1.txt';code=0
 else:
  result=subprocess.run([sys.executable,str(p/'compile_one.py'),str(src),str(log)],cwd=p);code=result.returncode
 if code:print(json.dumps(dict(stopped=name,exit=code)),flush=True);sys.exit(code)
 shutil.copyfile(src,archive/name);shutil.copyfile(log,archive/(src.stem+'.compile.txt'))
 stat=json.loads(log.with_suffix('.status.json').read_text());stat['sha256']=hashlib.sha256(src.read_bytes()).hexdigest();status.append(stat)
 (p/'compile-completed.json').write_text(json.dumps(status,indent=2));print(json.dumps(dict(preserved=name,completed=len(status),total=len(plan))),flush=True)
