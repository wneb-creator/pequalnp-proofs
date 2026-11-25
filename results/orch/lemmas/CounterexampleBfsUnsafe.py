from itertools import combinations
from pathlib import Path
import json,argparse

p=argparse.ArgumentParser();p.add_argument('--five',action='store_true');args=p.parse_args()

base=json.loads(Path('/tmp/oec/pequalnp-pilot-54/counterexample-small-results.json').read_text())
if args.five:
 base.append(json.loads(Path('/tmp/oec/pequalnp-pilot-54/counterexample-five-forest-results.json').read_text()))
results=[]
for entry in base:
 n=entry['n'];width=1<<n
 inp=tuple(sum(1<<a for a in range(width) if (a>>i)&1) for i in range(n))
 targets=[]
 for t in entry['targets']:
  f=0
  for a,b in t['edges']:f|=inp[a]&inp[b]
  targets.append((f,t))
 ti={f:i for i,(f,_) in enumerate(targets)}
 maxg=max(t['min'] for _,t in targets)
 states={tuple(sorted(inp)):0};unsafe=set();badcache={}
 for k in range(1,maxg+1):
  nxt={}
  for state,flag in states.items():
   for a,b in combinations(state,2):
    for op,c in [('and',a&b),('or',a|b)]:
     if c in state:continue
     newflag=flag
     if op=='and':
      if c not in badcache:
       badcache[c]=sum(1<<i for i,(f,t) in enumerate(targets) if c&~f)
      newflag|=badcache[c]
     if c in ti:
      i=ti[c]
      if targets[i][1]['min']==k and (newflag>>i)&1:unsafe.add(i)
     if k<maxg:
      ns=tuple(sorted(state+(c,)));nxt[ns]=nxt.get(ns,0)|newflag
  states=nxt
 results.append({'n':n,'unsafe_minimum_targets':[targets[i][1] for i in sorted(unsafe)]})
 print(n,'unsafe minimal targets',len(unsafe),flush=True)
Path('/tmp/oec/pequalnp-pilot-54/counterexample-unsafe-small-results.json').write_text(json.dumps(results,indent=2)+'\n')
