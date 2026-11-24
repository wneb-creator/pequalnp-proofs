from pathlib import Path
import argparse,json,subprocess,time,os,hashlib
ap=argparse.ArgumentParser()
ap.add_argument('--outdir',required=True)
ap.add_argument('--resume',action='store_true')
a=ap.parse_args();out=Path(a.outdir);cases=json.loads((out/'signed-cases-manifest.json').read_text());results=[]
resultpath=out/'signed-cases-build-results.json'
if a.resume and resultpath.exists():results=json.loads(resultpath.read_text())
completed={r['module']:r for r in results if r['exit_code']==0}
os.environ['LEAN_PATH']=str(out)+':/tmp/oec/pequalnp-pilot-14/toolchain:/tmp/oec/pequalnp-pilot-14/force-context:/tmp/oec/pequalnp-pilot-14/assembly:'+os.environ.get('LEAN_PATH','')
for case in cases:
 for module in case['modules']:
  src=out/(module+'.lean');ole=out/(module+'.olean')
  if module in completed and ole.exists() and completed[module]['source_sha256']==hashlib.sha256(src.read_bytes()).hexdigest():continue
  log=out/(module+'.log');start=time.monotonic()
  with log.open('w')as f:
   r=subprocess.run(['lake','env','/tmp/oec/pequalnp-pilot-14/sat-proof/lean-scratch.sh','--profile','-M','10000','-R',str(out),'-o',str(ole),str(src)],cwd='/workspace/pequalnp-proofs/lean',stdout=f,stderr=subprocess.STDOUT)
   elapsed=time.monotonic()-start;f.write(f'\nrunner_seconds {elapsed:.3f}\nrunner_exit {r.returncode}\n')
  results.append({'module':module,'exit_code':r.returncode,'seconds':elapsed,'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'log':str(log)})
  resultpath.write_text(json.dumps(results,indent=2)+'\n')
  print(('PASS'if r.returncode==0 else'FAIL')+' '+module+f' seconds={elapsed:.3f}',flush=True)
  if r.returncode:raise SystemExit(r.returncode)
 print('CLOSED '+case['namespace']+'.excluded',flush=True)
