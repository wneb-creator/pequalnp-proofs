import argparse,json,time
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('data');p.add_argument('log');p.add_argument('prefix');p.add_argument('--target',type=int,required=True);args=p.parse_args();d=json.loads(Path(args.data).read_text());rows=d['rows'];n=d.get('inputs',d.get('ninputs'));E=len(d['edges']) if 'edges' in d else len(d['positive']);goal=(1<<E)-1;negative=((1<<len(rows))-1)^goal;inputs=[sum(((r>>i)&1)<<k for k,r in enumerate(rows)) for i in range(n)]
def ev(gs,out=None):
 vs=inputs[:]
 for j,(op,a,c) in enumerate(gs):
  assert op in (0,1) and 0<=a<n+j and 0<=c<n+j
  vs.append(vs[a]|vs[c] if op else vs[a]&vs[c])
 return vs,vs[n+len(gs)-1 if out is None else out]
def prune(gs,out):
 need={out}
 for j in reversed(range(len(gs))):
  if n+j in need:need.update(gs[j][1:])
 mp={i:i for i in range(n)};new=[]
 for j,(op,a,c) in enumerate(gs):
  if n+j in need:mp[n+j]=n+len(new);new.append([op,mp[a],mp[c]])
 return new,mp[out]
def norm(gs,out):
 gs,out=prune(gs,out);steps=0
 while gs:
  vs,old=ev(gs,out);assert old==goal;found=False
  for j in range(len(gs)):
   bv=vs[n+j]
   for a,av in enumerate(vs[:n+j]):
    if (bv&goal&~av) or (av&negative&~bv):continue
    trial=[g[:] for g in gs]
    for k in range(j+1,len(trial)):trial[k][1:]=[a if x==n+j else x for x in trial[k][1:]]
    trial,no=prune(trial,a if out==n+j else out);assert ev(trial,no)[1]==goal;gs,out=trial,no;steps+=1;found=True;break
   if found:break
  if not found:break
 return gs,out,steps
text=Path(args.log).read_text();lines=text.splitlines();records=[]
for i,line in enumerate(lines):
 if i==len(lines)-1 and not text.endswith('\n'):break
 records.append(json.loads(line))
seen=set();results=[];best=None;start=time.monotonic()
for i,r in enumerate(records):
 gs=r['gates'];out=r.get('output',n+len(gs)-1);key=(tuple(map(tuple,gs)),out)
 if key in seen:continue
 seen.add(key)
 if ev(gs,out)[1]!=goal:continue
 new,no,steps=norm(gs,out);record={'source_record':i,'original':len(gs),'size':len(new),'output':no,'steps':steps};results.append(record)
 if best is None or len(new)<best['size']:best={**record,'gates':new}
 if len(new)<=args.target:break
report={'seconds':time.monotonic()-start,'exact_networks':len(results),'best_size':None if best is None else best['size'],'hit':best is not None and best['size']<=args.target,'results':results};Path(args.prefix+'.report.json').write_text(json.dumps(report,indent=2)+'\n')
if best:Path(args.prefix+'.best.json').write_text(json.dumps(best,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k!='results'}),flush=True)
