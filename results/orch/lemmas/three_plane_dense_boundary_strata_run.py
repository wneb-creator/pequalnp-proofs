from pathlib import Path
import subprocess,resource,json,time
job=Path('/tmp/oec/pequalnp-pilot-79')
def limits():
 resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3));resource.setrlimit(resource.RLIMIT_CPU,(120,120))
results=[]
for k in range(1,6):
 output=job/f'dense-boundary-stratum-{k}-result.json';log=job/f'dense-boundary-stratum-{k}.log'
 args=['python3',str(job/'neogb-run-rational.py'),'-f',str(job/f'dense-boundary-stratum-{k}.msolve'),'-o',str(output),'-t','1','--info','2','--max-pairs','128','--hash-size','15']
 with log.open('w') as f:
  try:r=subprocess.run(args,stdout=f,stderr=subprocess.STDOUT,preexec_fn=limits,timeout=120)
  except subprocess.TimeoutExpired:
   results.append({'stratum':k,'timeout':True});print(results[-1],flush=True);break
 res={'stratum':k,'exit':r.returncode}
 if r.returncode==0 and output.exists():
  data=json.loads(output.read_text());res.update({'basis_size':len(data['basis']),'unit':any(len(p)==1 and not any(p[0]['exponents']) and p[0]['coefficient']!=0 for p in data['basis']),'seconds':data['seconds']})
 results.append(res);print(res,flush=True)
 if r.returncode!=0:break
(job/'dense-boundary-strata-summary.json').write_text(json.dumps(results,indent=2))
