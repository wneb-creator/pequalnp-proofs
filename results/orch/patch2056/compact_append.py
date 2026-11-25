import argparse,json,time
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('data');p.add_argument('candidates');p.add_argument('output');p.add_argument('--budget',type=int,default=28);args=p.parse_args()
data=json.loads(Path(args.data).read_text());candidates=json.loads(Path(args.candidates).read_text());rows=data['rows'];n=len(data['points'])+len(data['lines']);goal=(1<<len(data['edges']))-1
inputs=[sum(((r>>i)&1)<<k for k,r in enumerate(rows)) for i in range(n)]
def ev(gs):
 vs=inputs[:]
 for op,a,b in gs:vs.append(vs[a]|vs[b] if op else vs[a]&vs[b])
 return vs
def dead(gs):
 needed={n+len(gs)-1}
 for j in reversed(range(len(gs))):
  if n+j in needed:needed.update(gs[j][1:])
 mapping={i:i for i in range(n)};out=[]
 for j,g in enumerate(gs):
  if n+j in needed:
   op,a,b=g;mapping[n+j]=n+len(out);out.append([op,mapping[a],mapping[b]])
 return out
def compact(gs):
 gs=dead(gs)
 while True:
  vs=ev(gs);target=vs[-1];found=False
  for j in range(len(gs)-1):
   for sub in gs[j][1:]:
    trial=[g[:] for g in gs]
    for k in range(j+1,len(trial)):
     trial[k][1:]=[sub if x==n+j else x for x in trial[k][1:]]
    if ev(trial)[-1]==target:
     gs=dead(trial);found=True;break
   if found:break
  if not found:return gs
def append(gs,budget):
 vs=ev(gs);f0={v:('wire',i) for i,v in enumerate(vs)}
 if goal in f0:return gs,f0[goal]
 if budget<1:return None
 f1={}
 items=list(f0.items())
 for j,(a,e) in enumerate(items):
  for b,f in items[j:]:
   for op,v in [(0,a&b),(1,a|b)]:
    ex=(op,e,f)
    if v==goal:return gs,ex
    if v not in f0:f1.setdefault(v,ex)
 if budget<2:return None
 f2={}
 for a,e in f1.items():
  for b,f in items:
   for op,v in [(0,a&b),(1,a|b)]:
    ex=(op,e,f)
    if v==goal:return gs,ex
    if v not in f0 and v not in f1:f2.setdefault(v,ex)
 if budget<3:return None
 for a,e in f2.items():
  for b,f in items:
   for op,v in [(0,a&b),(1,a|b)]:
    if v==goal:return gs,(op,e,f)
 oi=[(v,e) for v,e in f1.items() if v&~goal==0];ai=[(v,e) for v,e in f1.items() if v&goal==goal]
 for op,es in [(0,ai),(1,oi)]:
  for i,(a,e) in enumerate(es):
   for b,f in es[i:]:
    if (a&b if op==0 else a|b)==goal:return gs,(op,e,f)
 return None
def materialize(gs,expr):
 out=[g[:] for g in gs];memo={}
 def emit(e):
  if e[0]=='wire':return e[1]
  if e in memo:return memo[e]
  op,ea,eb=e;a=emit(ea);b=emit(eb);i=n+len(out);out.append([op,a,b]);memo[e]=i;return i
 idx=emit(expr)
 if idx!=n+len(out)-1:
  assert idx>=n
  return dead(out[:idx-n+1])
 return out
start=time.monotonic();reports=[]
for i,r in enumerate(candidates):
 gs=compact(r['gates']);remaining=args.budget-len(gs);hit=append(gs,min(remaining,3));report={'candidate':i,'original':len(r['gates']),'compacted':len(gs),'remaining':remaining,'searched_append_depth':min(remaining,3),'hit':bool(hit)};reports.append(report)
 if hit:
  out=materialize(*hit)
  assert out is not None and len(out)<=args.budget and ev(out)[-1]==goal
  Path(args.output+'.hit.json').write_text(json.dumps({'gates':out,'output':n+len(out)-1,'source':i},indent=2)+'\n')
  print('HIT',report,flush=True);break
Path(args.output+'.report.json').write_text(json.dumps({'seconds':time.monotonic()-start,'candidates':reports},indent=2)+'\n')
print(json.dumps({'seconds':time.monotonic()-start,'candidates':len(reports),'compacted_sizes':sorted(set(r['compacted'] for r in reports)),'hit':any(r['hit'] for r in reports)}),flush=True)
