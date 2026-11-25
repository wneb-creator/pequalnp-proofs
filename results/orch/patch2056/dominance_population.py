from pathlib import Path
import json,time
b=Path(__file__).resolve().parent;data=json.loads((b/'six-data.json').read_text());rows=data['rows'];n=17;goal=(1<<24)-1;mask=(1<<len(rows))-1;neg=mask^goal;inputs=[sum(((r>>i)&1)<<k for k,r in enumerate(rows)) for i in range(n)]
def ev(gs,out=None):
 vs=inputs[:]
 for op,a,c in gs:vs.append(vs[a]|vs[c] if op else vs[a]&vs[c])
 return vs,vs[-1] if out is None else vs[out]
def prune(gs,out):
 need={out}
 for j in reversed(range(len(gs))):
  if n+j in need:need.update(gs[j][1:])
 mp={i:i for i in range(n)};res=[]
 for j,(op,a,c) in enumerate(gs):
  if n+j in need:mp[n+j]=n+len(res);res.append([op,mp[a],mp[c]])
 return res,mp[out]
def norm(gs):
 gs,out=prune(gs,n+len(gs)-1);steps=0
 while gs:
  vs,old=ev(gs,out);found=False
  for j in range(len(gs)):
   bv=vs[n+j]
   for a,av in enumerate(vs[:n+j]):
    if (bv&goal&~av) or (av&neg&~bv):continue
    trial=[g[:] for g in gs]
    for k in range(j+1,len(trial)):trial[k][1:]=[a if x==n+j else x for x in trial[k][1:]]
    newout=a if out==n+j else out;trial,newout=prune(trial,newout);_,new=ev(trial,newout)
    assert old&goal&~new==0 and new&neg&~old==0
    gs,out=trial,newout;steps+=1;found=True;break
   if found:break
  if not found:break
 return gs,out,steps
seen=set();nets=[]
for fn in ['six-local.stdout','hybrid-local.stdout','structured-local.stdout']:
 for line in (b/fn).read_text().splitlines():
  r=json.loads(line);key=tuple(map(tuple,r['gates']))
  if key not in seen:seen.add(key);nets.append(r['gates'])
start=time.monotonic();reports=[];normalized=[];hit=None
for i,gs in enumerate(nets):
 _,old=ev(gs);outgs,out,steps=norm(gs);vs,value=ev(outgs,out);done=value==goal
 if not done and len(outgs)<28:
  for a,av in enumerate(vs):
   for c in range(a,len(vs)):
    cv=vs[c]
    for op,new in [(0,av&cv),(1,av|cv)]:
     if new==goal:
      outgs=outgs+[[op,a,c]];out=n+len(outgs)-1;done=True;break
    if done:break
   if done:break
 info={'candidate':i,'steps':steps,'gates':len(outgs),'old_errors':(old^goal).bit_count(),'errors':(ev(outgs,out)[1]^goal).bit_count(),'hit':done};reports.append(info)
 normalized.append({'gates':outgs,'output':out,'analysis':info})
 if done:hit=normalized[-1];break
(b/'six-dominance-report.json').write_text(json.dumps({'seconds':time.monotonic()-start,'results':reports},indent=2)+'\n');(b/'six-dominance-candidates.json').write_text(json.dumps(normalized,indent=2)+'\n')
if hit:(b/'six-dominance-hit.json').write_text(json.dumps(hit,indent=2)+'\n')
print(json.dumps({'seconds':time.monotonic()-start,'networks':len(reports),'improved':sum(r['errors']<r['old_errors'] for r in reports),'gate_reductions':sum(r['steps'] for r in reports),'hit':bool(hit)}),flush=True)
