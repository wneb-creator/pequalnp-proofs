import json,time
from pathlib import Path
b=Path(__file__).resolve().parent;d=json.loads((b/'six-data.json').read_text());n=17;rows=d['rows'];goal=(1<<24)-1;inputs=[sum(((r>>i)&1)<<k for k,r in enumerate(rows)) for i in range(n)]
def ev(gs):
 vs=inputs[:]
 for op,a,c in gs:vs.append(vs[a]|vs[c] if op else vs[a]&vs[c])
 return vs
def dead(gs):
 needed={n+len(gs)-1}
 for j in reversed(range(len(gs))):
  if n+j in needed:needed.update(gs[j][1:])
 mp={i:i for i in range(n)};out=[]
 for j,(op,a,c) in enumerate(gs):
  if n+j in needed:mp[n+j]=n+len(out);out.append([op,mp[a],mp[c]])
 return out
def compact(gs):
 gs=dead(gs)
 while True:
  target=ev(gs)[-1];found=False
  for j in range(len(gs)-1):
   for sub in gs[j][1:]:
    trial=[g[:] for g in gs]
    for k in range(j+1,len(trial)):trial[k][1:]=[sub if x==n+j else x for x in trial[k][1:]]
    if ev(trial)[-1]==target:gs=dead(trial);found=True;break
   if found:break
  if not found:return gs
seen=set();nets=[]
for fn in ['six-local.stdout','hybrid-local.stdout','structured-local.stdout']:
 for line in (b/fn).read_text().splitlines():
  r=json.loads(line);key=tuple(map(tuple,r['gates']))
  if key not in seen:seen.add(key);gs=compact(r['gates']);nets.append((gs,ev(gs)[-1]))
def merge(a,c,op):
 gs=[];vs=inputs[:];have={v:i for i,v in enumerate(vs)};outs=[]
 for net in [a,c]:
  mp={i:i for i in range(n)}
  for j,(o,x,y) in enumerate(net):
   x,y=mp[x],mp[y];v=vs[x]|vs[y] if o else vs[x]&vs[y]
   if v not in have:have[v]=n+len(gs);gs.append([o,x,y]);vs.append(v)
   mp[n+j]=have[v]
  outs.append(mp[n+len(net)-1])
 x,y=outs;gs.append([op,x,y]);return dead(gs)
start=time.monotonic();pairs=0;best=None;hit=None
for i,(a,av) in enumerate(nets):
 for j in range(i,len(nets)):
  c,cv=nets[j]
  for op in [0,1]:
   if (av|cv if op else av&cv)!=goal:continue
   pairs+=1;gs=merge(a,c,op);assert ev(gs)[-1]==goal
   item={'gates':gs,'size':len(gs),'left':i,'right':j,'operation':op}
   if best is None or len(gs)<best['size']:best=item
   if len(gs)<=28:hit=item;break
  if hit:break
 if hit:break
report={'seconds':time.monotonic()-start,'networks':len(nets),'correct_pairs':pairs,'best_size':None if best is None else best['size'],'hit':hit is not None}
(b/'combine-report.json').write_text(json.dumps(report,indent=2)+'\n')
if best is not None:(b/'combine-best.json').write_text(json.dumps(best,indent=2)+'\n')
print(json.dumps(report),flush=True)
