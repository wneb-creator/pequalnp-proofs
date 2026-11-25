import json,subprocess,hashlib,collections
from pathlib import Path
base=Path('/tmp/oec/pequalnp-pilot-81')
args=['rg','--files',str(base),'-g','constructive-internal28-*.json','-g','constructive-fano-28.json','-g','stochastic-verified-*.json','-g','stochastic28-compact.json','-g','stochastic-global-cse-best.json','-g','stochastic-global-cse-near-*.json','-g','stochastic-negativebest-*.json']
files=subprocess.check_output(args,text=True).splitlines();tests=[int(x) for x in (base/'stochastic-tests.txt').read_text().split()];pos=(1<<21)-1;neg=((1<<58)-1)^pos
rows=[];seen=set()
for filename in sorted(files):
 try:d=json.loads(Path(filename).read_text())
 except json.JSONDecodeError:continue
 if not isinstance(d,dict) or 'gates' not in d or d.get('inputs',d.get('n_inputs',14))!=14:continue
 g=d['gates'];out=d['output'];ident=json.dumps([g,out]);digest=hashlib.sha256(ident.encode()).hexdigest()[:12]
 if digest in seen:continue
 seen.add(digest);use=set()
 def visit(i):
  if i in use:return
  use.add(i)
  if i>=14:
   _,a,b=g[i-14];visit(a);visit(b)
 visit(out);fan=[0]*(14+len(g));supp=[1<<i for i in range(14)];v=[sum(1<<j for j,x in enumerate(tests) if x>>i&1) for i in range(14)]
 for j,(op,a,b) in enumerate(g):
  assert a!=b and a<14+j and b<14+j
  supp.append(supp[a]&supp[b] if op=='and' else supp[a]|supp[b]);v.append(v[a]&v[b] if op=='and' else v[a]|v[b])
  if 14+j in use:fan[a]+=1;fan[b]+=1
 bplus=bzero=elig=0;branches=[];comparable=[]
 for i in sorted(use):
  if i==out or fan[i]<2:continue
  surplus=fan[i]-1
  if supp[i]:bplus+=surplus;elig|=supp[i]
  else:bzero+=surplus
  branches.append({'wire':i,'fanout':fan[i],'surplus':surplus,'singleton_support':[k for k in range(14) if supp[i]>>k&1]})
 for j,(op,a,b) in enumerate(g):
  if 14+j not in use:continue
  mask=neg if op=='and' else pos;aa=v[a]&mask;bb=v[b]&mask
  if aa&~bb==0 or bb&~aa==0:comparable.append({'wire':14+j,'op':op,'left_subset_right':aa&~bb==0,'right_subset_left':bb&~aa==0})
 n=sum(i>=14 for i in use);usedinputs=[i for i in range(14) if i in use]
 assert bplus+bzero==n+1-len(usedinputs)
 rows.append({'source':filename,'id':digest,'live_gates':n,'used_inputs':usedinputs,'eligible_inputs':[i for i in range(14) if elig>>i&1],'eligible_points':[i for i in range(7) if elig>>i&1],'eligible_lines':[i for i in range(7) if elig>>(7+i)&1],'eligible_count':elig.bit_count(),'Bplus':bplus,'Bzero':bzero,'total_surplus':bplus+bzero,'boundary_correct':v[out]==pos,'positive_failures':(pos&~v[out]).bit_count(),'negative_failures':(neg&v[out]).bit_count(),'branches':branches,'comparable_gates':comparable})
(base/'stochastic-branching-summary.json').write_text(json.dumps(rows,indent=2)+'\n')
for category,pred in [('correct28',lambda r:r['boundary_correct'] and r['live_gates']==28),('near27',lambda r:r['live_gates']==27 and r['positive_failures']+r['negative_failures']==1),('other',lambda r:not(r['boundary_correct'] and r['live_gates']==28) and not(r['live_gates']==27 and r['positive_failures']+r['negative_failures']==1))]:
 selected=[r for r in rows if pred(r)];hist=collections.Counter((r['eligible_count'],r['Bplus'],r['Bzero'],len(r['comparable_gates'])) for r in selected)
 print(category,len(selected),'histogram(p,Bplus,Bzero,comparable):',dict(hist))
print('Fewer than14 used inputs:',sum(len(r['used_inputs'])<14 for r in rows))
