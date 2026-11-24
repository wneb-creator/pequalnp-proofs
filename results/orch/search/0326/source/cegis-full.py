import argparse, json, pathlib, random, subprocess, time, importlib.util
spec=importlib.util.spec_from_file_location('cegisbase','/tmp/oec/pequalnp-pilot-21/search/cegis.py')
b=importlib.util.module_from_spec(spec);spec.loader.exec_module(b)
ROWS,INPUTS,TARGETS,LINES,CNF,SOLVER=b.ROWS,b.INPUTS,b.TARGETS,b.LINES,b.CNF,b.SOLVER
def encode(base,meta,goals,ng,samples,order=False):
 c=CNF();ops=[c.var() for _ in range(ng)]
 av=[None if i<13 else c.var() for i in range(len(base))]
 for i in range(13,len(base)):
  for j in range(i+1,len(base)):
   if meta[i][0]==meta[j][0] and not compatible(meta[i][1],meta[j][1]):c.add(-av[i],-av[j])
 aa=[];bb=[]
 for j in range(ng):
  a=[c.var() for _ in range(len(base)+j)];d=[c.var() for _ in a];c.one(a);c.one(d)
  for x in range(len(a)):
   for y in range(x+1):c.add(-a[x],-d[y])
  for k in range(13,len(base)):c.add(-a[k],av[k]);c.add(-d[k],av[k])
  aa.append(a);bb.append(d)
 if order:
  for j in range(ng-len(goals)-1):
   for x,d in enumerate(bb[j]):
    for y in range(x):c.add(-d,-bb[j+1][y])
 for r in sorted(samples):
  vs=[c.var() for _ in range(ng)]
  for j in range(ng):
   a=c.var();d=c.var();v=vs[j];op=ops[j]
   for sels,dest in ((aa[j],a),(bb[j],d)):
    for k,sel in enumerate(sels):
     if k<len(base):c.add(-sel,dest if base[k]>>r&1 else -dest)
     else:
      src=vs[k-len(base)];c.add(-sel,-src,dest);c.add(-sel,src,-dest)
   c.add(-op,-a,-d,v);c.add(-op,a,-v);c.add(-op,d,-v)
   c.add(op,a,d,-v);c.add(op,-a,v);c.add(op,-d,v)
  for i,goal in enumerate(goals):c.add(vs[ng-len(goals)+i] if TARGETS[goal]>>r&1 else -vs[ng-len(goals)+i])
 return c,ops,aa,bb

def main():
 parser=argparse.ArgumentParser(description='Full38-gate monotone circuit CEGIS over all3003 band inputs.')
 parser.add_argument('--seconds',type=int,default=3600)
 parser.add_argument('--solve-seconds',type=int,default=300)
 parser.add_argument('--order',action='store_true',help='Order internal gates by maximal predecessor index.')
 args=parser.parse_args()
 root=pathlib.Path('/tmp/oec/pequalnp-pilot-21/search/full-ordered' if args.order else '/tmp/oec/pequalnp-pilot-21/search/full-unordered')
 root.mkdir(exist_ok=True)
 started=time.monotonic();deadline=started+args.seconds;rng=random.Random(102438)
 goals=list(range(13));ng=38;base=list(INPUTS);meta=[None]*13
 samples={r for r,x in enumerate(ROWS) if x.bit_count()==8 and any(not(TARGETS[g]>>r&1) for g in goals)}
 samples.update(rng.sample(range(len(ROWS)),100))
 for it in range(100):
  if time.monotonic()>deadline:break
  c,ops,aa,bb=encode(base,meta,goals,ng,samples,args.order)
  stem=f'full-{it:03d}';cnf=root/(stem+'.cnf');log=root/(stem+'.log')
  c.save(cnf);(root/(stem+'-rows.json')).write_text(json.dumps(sorted(samples))+'\n')
  print('solve',it,'rows',len(samples),'vars',c.n,'clauses',len(c.cs),'ordered',args.order,'elapsed',round(time.monotonic()-started),flush=True)
  limit=min(args.solve_seconds,max(1,int(deadline-time.monotonic())))
  with log.open('w') as f:result=subprocess.run([SOLVER,'-q','--sat','--lrat','--no-binary','-t',str(limit),str(cnf),str(root/(stem+'.lrat'))],stdout=f,stderr=subprocess.STDOUT)
  status,gates,_=b.extract(log,ops,aa,bb,[])
  print('result',status,'exit',result.returncode,'elapsed',round(time.monotonic()-started),flush=True)
  if status=='unsat':
   print('UNSAT_ENCODING',str(cnf),flush=True);break
  if status!='sat':
   samples.update(rng.sample(range(len(ROWS)),min(1000,200*(it+1))));continue
  vals=list(base)
  for a,d,op in gates:vals.append(vals[a]&vals[d] if op else vals[a]|vals[d])
  outs=list(range(ng-len(goals),ng));bad=[]
  for goal,o in zip(goals,outs):
   diff=vals[len(base)+o]^TARGETS[goal];bad.append([r for r in range(len(ROWS)) if diff>>r&1])
  print('errors',[len(x) for x in bad],flush=True)
  if not any(bad):
   candidate={'gates':gates,'out':[13+o for o in outs],'rows':len(ROWS),'ordered':args.order}
   for x in ROWS:
    ws=[bool(x>>i&1) for i in range(13)]
    for a,d,op in gates:ws.append((ws[a] and ws[d]) if op else (ws[a] or ws[d]))
    assert all(ws[candidate['out'][w]]==any(bool(x>>p&1) for p in LINES[w]) for w in range(13))
   (root/'counterexample.json').write_text(json.dumps(candidate,indent=2)+'\n')
   print('FOUND',it,flush=True);return
  for rows in bad:rng.shuffle(rows);samples.update(rows[:16])
 print('FINISHED elapsed',round(time.monotonic()-started),flush=True)
if __name__=='__main__':main()
