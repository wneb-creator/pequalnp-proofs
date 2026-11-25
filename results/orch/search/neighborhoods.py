from pathlib import Path
import itertools,subprocess,time,json
root=Path('/tmp/oec/pequalnp-pilot-103/counterexample')
logs=root/'neighborhood-logs';logs.mkdir(exist_ok=True)
start=time.monotonic();counts={}
triples=list(itertools.combinations(range(19),3))
triples.sort(key=lambda t:(0 not in t,t))
for k,t in enumerate(triples):
 if time.monotonic()-start>300:break
 cmd=['python3',str(root/'search.py'),'--case','any','--allow-unused','--eager-sat','--brief','--local',str(root/'near19.json'),'--mutable',','.join(map(str,t)),'--timeout-ms','1000']
 try:
  p=subprocess.run(cmd,capture_output=True,text=True,timeout=8)
  out,err=p.stdout,p.stderr
 except subprocess.TimeoutExpired as ex:
  out=(ex.stdout or b'').decode() if isinstance(ex.stdout,bytes) else ex.stdout or ''
  err=(ex.stderr or b'').decode() if isinstance(ex.stderr,bytes) else ex.stderr or ''
  err+='\nExternal timeout after8seconds\n'
 (logs/f'{k:03d}.stdout').write_text(out)
 (logs/f'{k:03d}.stderr').write_text(err)
 verdict='witness' if 'WITNESS' in out else 'unsat' if 'result unsat' in out else 'unknown'
 counts[verdict]=counts.get(verdict,0)+1
 print(k,t,verdict,'elapsed',round(time.monotonic()-start,2),flush=True)
 if verdict=='witness':
  print(out,flush=True);break
print('TOTAL',json.dumps(counts),'elapsed',time.monotonic()-start,flush=True)
