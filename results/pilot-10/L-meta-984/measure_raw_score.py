from pathlib import Path
import json,time,collections
R=Path('/tmp/oec/pequalnp-pilot-10/independent-search/984');out=[];start=time.monotonic()
for graph in [26,28]+[i for i in range(31) if i not in [26,28]]:
 m=json.loads((R/f'compact/compact{graph}.meta.json').read_text());p=m['negative_count'];e=m['positive_count'];goalcoverage=(1<<(p*e))-1
 f=json.loads((R/f'compact/fast_pool_{graph}.json').read_text());coords=f['coordinate_array'];bw=f['rank_width'];pool=[[((code>>(bw*j))&((1<<bw)-1)) for j in range(6)] for code in f['rank_codes']]
 covercache={};scorecache={};c=collections.Counter();bylayer={}
 def cov(w):
  if w not in covercache:
   positives=w>>p;covercache[w]=sum(positives<<(e*i) for i in range(p) if not((w>>i)&1))
  return covercache[w]
 def score(ws,t):
  if len(ws)!=t or len(ws)>12:return False
  key=tuple(sorted(ws))
  if key in scorecache:return scorecache[key]
  masks=[sum(((w>>j)&1)<<i for i,w in enumerate(ws)) for j in coords]
  for a,b,cc,d,ee,ff in pool:
   a,b,cc,d,ee,ff=[masks[j] for j in [a,b,cc,d,ee,ff]]
   val=(b&~d).bit_count()+(cc&~d).bit_count()+(a&~ee).bit_count()+(a&~ff).bit_count()-(a&~d&(b|cc)&~(ee&ff)).bit_count()
   if val<3:scorecache[key]=True;return True
  scorecache[key]=False;return False
 for s in range(m['budget'],-1,-1):
  path=R/f'direct_v4/C{graph}.layer{s}.jsonl'
  if not path.exists():continue
  lc=collections.Counter()
  for line in path.read_text().splitlines():
   ws=[int(w,16) for w in json.loads(line)];lc['states']+=1
   if s==0:continue
   slack=s+1-len(ws)
   def visit(child,cover):
    lc['raw_children']+=1
    if cover!=goalcoverage:return
    lc['covered_children']+=1
    if len(child)==s:lc['tight_covered']+=1
    if score(child,s):lc['raw_score_pruned']+=1
    else:lc['orientation_needed']+=1
   wc=0
   for w in ws:wc|=cov(w)
   for a in ws:
    ra=ws.copy();ra.remove(a)
    if slack>=1:visit([a]+ra,wc)
    if slack>=2:visit([a,a]+ra,wc)
    for b in ra:
     if a>b:continue
     rest=ra.copy();rest.remove(b);rc=0
     for w in rest:rc|=cov(w)
     for w in [a|b,a&b]:
      base=rc|cov(w)
      visit([w]+rest,base)
      if slack>=1:
       visit([w,a]+rest,base|cov(a));visit([w,b]+rest,base|cov(b))
      if slack>=2:visit([w,a,b]+rest,base|cov(a)|cov(b))
  bylayer[s]=dict(lc);c.update(lc)
 record={'graph':graph,'group':m['group'],**dict(c),'pruned_orientation_fraction':c['raw_score_pruned']/c['covered_children'] if c['covered_children'] else 0,'old_action_calls_proxy':c['covered_children']*(m['group']-1),'new_action_calls_proxy':c['orientation_needed']*(m['group']-1),'layers':bylayer}
 out.append(record);print(json.dumps({k:v for k,v in record.items() if k!='layers'}),flush=True)
(R/'raw-score-measurement.json').write_text(json.dumps({'scope':'Exact untrusted CPU-light count of enumerated candidate occurrences and raw-score early exclusions over all31 frozen compact grouped frontiers; duplicates retained, no frontier regeneration or Lean compilation.','graphs':out,'seconds':time.monotonic()-start},indent=2)+'\n')
print(json.dumps({'status':'PASS','seconds':time.monotonic()-start,'raw_children':sum(x['raw_children'] for x in out),'covered_children':sum(x['covered_children'] for x in out),'raw_score_pruned':sum(x['raw_score_pruned'] for x in out),'old_action_calls_proxy':sum(x['old_action_calls_proxy'] for x in out),'new_action_calls_proxy':sum(x['new_action_calls_proxy'] for x in out)}),flush=True)
