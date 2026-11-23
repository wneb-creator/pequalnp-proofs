from pathlib import Path
import concurrent.futures,json,subprocess,sys,time
p=Path(__file__).resolve().parent
root=Path('/tmp/oec/pequalnp-pilot-10/root984')
started=time.monotonic()
def one(i):
 prefix=f'all{i}'; out=p/f'pool_all{i}'; out.mkdir(exist_ok=True)
 meta=json.loads((root/(prefix+'.meta.json')).read_text())
 assert all((root/f'{prefix}.layer{s}.jsonl').exists() for s in range(meta['budget']+1))
 commands=[([sys.executable,str(p/'prepare_score_states_batch.py'),prefix,str(out)],'prepare.log'),([str(p/'score_pool'),str(out/'score_states.txt'),str(out/'score_pool_indices.txt')],'score_pool.log'),([sys.executable,str(p/'finalize_score_pool_batch.py'),prefix,str(out)],'validation.log')]
 for cmd,log in commands:
  with (out/log).open('w') as f:
   r=subprocess.run(cmd,cwd='/workspace/pequalnp-proofs',stdout=f,stderr=subprocess.STDOUT)
  if r.returncode: raise RuntimeError(f'{prefix} failed {log} exit{r.returncode}')
 report=json.loads((out/'score_pool.json').read_text())
 temporary=p/f'score_pool_{i}.json.tmp'; temporary.write_text(json.dumps(report,indent=2)+'\n'); temporary.replace(p/f'score_pool_{i}.json')
 summary={'graph':i,'codes':len(report['codes']),'tight_states':report['tight_states'],'covered':report['covered'],'uncovered':report['uncovered'],'uncovered_by_layer':report['uncovered_by_layer'],'elapsed_seconds':round(time.monotonic()-started,3)}
 print(json.dumps(summary),flush=True);return summary
results=[]
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as executor:
 futures={executor.submit(one,i):i for i in range(31)}
 for f in concurrent.futures.as_completed(futures):
  try:results.append(f.result())
  except Exception as e:
   print(json.dumps({'graph':futures[f],'error':str(e)}),flush=True);raise
(p/'score_pools_batch_summary.json').write_text(json.dumps(sorted(results,key=lambda r:r['graph']),indent=2)+'\n')
print('DONE_ALL_31',flush=True)
