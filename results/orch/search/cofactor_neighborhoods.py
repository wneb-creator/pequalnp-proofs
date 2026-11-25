from pathlib import Path
import itertools,subprocess,time,json
root=Path('/tmp/oec/pequalnp-pilot-103/counterexample')
logs=root/'cofactor-neighborhood-logs';logs.mkdir(exist_ok=True)
start=time.monotonic();counts={};total=0
triples=[(0,a,b)for a,b in itertools.combinations(range(1,16),2)]
for seed in [1,3,4,6,7,8,9,10,11,0,2,5]:
 for t in triples:
  if time.monotonic()-start>600:break
  name=f'{seed:02d}-'+ '-'.join(map(str,t))
  cmd=['python3',str(root/'cofactor.py'),'--case','any','--gates','16','--not-count','1','--allow-unused','--eager-sat','--brief','--local',str(root/'cofactor-seeds'/f'cofactor-missing-edge-{seed}.json'),'--mutable',','.join(map(str,t)),'--timeout-ms','1000']
  try:
   p=subprocess.run(cmd,capture_output=True,text=True,timeout=8)
   out,err=p.stdout,p.stderr
  except subprocess.TimeoutExpired as ex:
   out=(ex.stdout or b'').decode()if isinstance(ex.stdout,bytes)else ex.stdout or ''
   err=(ex.stderr or b'').decode()if isinstance(ex.stderr,bytes)else ex.stderr or ''
   err+='\nExternal timeout after8seconds\n'
  (logs/f'{name}.stdout').write_text(out);(logs/f'{name}.stderr').write_text(err)
  verdict='witness'if'WITNESS'in out else'unsat'if'result unsat'in out else'unknown'
  counts[verdict]=counts.get(verdict,0)+1;total+=1
  print(total,'seed',seed,'mutable',t,verdict,'elapsed',round(time.monotonic()-start,2),flush=True)
  if verdict=='witness':
   print(out,flush=True);break
 if counts.get('witness')or time.monotonic()-start>600:break
print('TOTAL',json.dumps(counts),'elapsed',time.monotonic()-start,flush=True)
