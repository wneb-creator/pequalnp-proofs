from pathlib import Path
import sys,json,time,hashlib
p=Path('/tmp/oec/pequalnp-pilot-65/status-review')
source=Path('/tmp/oec/pequalnp-pilot-65/finite-search/theta_extend_virtual.py').read_text()
prefix=source.split('baseval=evaluate(())',1)[0]
(p/'theta-rank-source-snapshot.py').write_text(prefix)
print('source_sha256',hashlib.sha256(source.encode()).hexdigest(),flush=True)
seedpaths=sorted((p/'rank-seed-files.txt').read_text().splitlines())
old=sys.argv;sys.argv=['theta_rank',str(p/'polarized-225.json'),'0','0'];ns={}
exec(compile(prefix,'theta-rank-source-snapshot.py','exec'),ns)
sys.argv=old
fixed=ns['fixed'];sources=ns['sources'];evaluate=ns['evaluate'];start=time.monotonic();records=[]
def rank(r):return (-r['max_gain'],-r['covered_count'],-r['safe_actions'],r['seed'])
with (p/'theta-rank-records.jsonl').open('w') as log:
 for no,path in enumerate(seedpaths):
  seed=json.loads(Path(path).read_text());ns['seed']=seed;ns['theta']=seed['gates'];baseval=evaluate(())
  assert baseval is not None
  bmask=baseval[0];covered=0;best=0;safe=0;best_actions=[]
  for port,old in enumerate(baseval[2]):
   for src in sources:
    sv=fixed[src]
    if (sv[0]|old[0])==old[0] and (sv[1]|old[1])==old[1] and (sv[2]|old[2])==old[2]:continue
    v=evaluate(((port,src),))
    if v is None:continue
    safe+=1;gained=bmask&~v[0];count=gained.bit_count();covered|=gained
    if count>best:best=count;best_actions=[]
    if count==best and count:best_actions.append([port,src,gained])
  rec=dict(seed=path,missing=bmask.bit_count(),safe_actions=safe,max_gain=best,covered_count=covered.bit_count(),covered_mask=covered,best_actions=best_actions)
  records.append(rec);log.write(json.dumps(rec)+'\n');log.flush()
  if best>=2 or covered.bit_count()==8:print('PROMISING',json.dumps(rec),flush=True)
  if (no+1)%25==0:
   ordered=sorted(records,key=rank);(p/'theta-ranking.json').write_text(json.dumps(ordered,indent=2)+'\n')
   print('progress',no+1,'seconds',round(time.monotonic()-start,1),'best',[(r['max_gain'],r['covered_count'],Path(r['seed']).name) for r in ordered[:3]],flush=True)
ordered=sorted(records,key=rank);(p/'theta-ranking.json').write_text(json.dumps(ordered,indent=2)+'\n')
print('done',len(records),'seconds',round(time.monotonic()-start,1),'max_gain',max(r['max_gain'] for r in records),'max_covered',max(r['covered_count'] for r in records),flush=True)
