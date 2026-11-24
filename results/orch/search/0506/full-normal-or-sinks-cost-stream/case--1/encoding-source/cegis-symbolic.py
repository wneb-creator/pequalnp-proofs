import itertools, json, pathlib, random, subprocess, time
import importlib.util
spec=importlib.util.spec_from_file_location('cegisbase','/tmp/oec/pequalnp-pilot-21/search/cegis.py')
b=importlib.util.module_from_spec(spec);spec.loader.exec_module(b)
ROOT=pathlib.Path('/tmp/oec/pequalnp-pilot-21/search/symbolic');ROOT.mkdir(exist_ok=True)
ROWS,INPUTS,TARGETS,LINES,CNF,SOLVER=b.ROWS,b.INPUTS,b.TARGETS,b.LINES,b.CNF,b.SOLVER

def compatible(s,t):
 return (len(s)==len(t)==2 and not(s&t)) or (len(s)<len(t) and s<t) or (len(t)<len(s) and t<s)
def bases(goals):
 vals=list(INPUTS);meta=[None]*13;index={}
 for line in range(13):
  if line in goals:continue
  for size in (2,3):
   for points in itertools.combinations(sorted(LINES[line]),size):
    s=frozenset(points);index[line,s]=len(vals);meta.append((line,s))
    v=0
    for p in s:v|=INPUTS[p]
    vals.append(v)
 return vals,meta,index

def encode(base,meta,goals,ng,samples):
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

def reconstruct(meta,index,goals,gates,outs):
 used={a for g in gates for a in g[:2] if 13<=a<len(meta)}
 net=[];wiremap=list(range(13))+[None]*(len(meta)-13);out={}
 for line in range(13):
  if line in goals:continue
  need={meta[k][1] for k in used if meta[k][0]==line};L=frozenset(LINES[line]);options=[]
  for pair in itertools.combinations(sorted(L),2):
   p=frozenset(pair);q=L-p
   if tuple(sorted(p))<tuple(sorted(q)):options.append((p,q))
  for triple in itertools.combinations(sorted(L),3):
   t=frozenset(triple)
   for pair in itertools.combinations(sorted(t),2):options.append((frozenset(pair),t))
  s,t=next((s,t) for s,t in options if need<={s,t})
  a,d=sorted(s);net.append((a,d,False));wiremap[index[line,s]]=13+len(net)-1
  if len(t)==2:
   a,d=sorted(t);net.append((a,d,False));wiremap[index[line,t]]=13+len(net)-1
   net.append((wiremap[index[line,s]],wiremap[index[line,t]],False))
  else:
   net.append((wiremap[index[line,s]],next(iter(t-s)),False));wiremap[index[line,t]]=13+len(net)-1
   net.append((wiremap[index[line,t]],next(iter(L-t)),False))
  out[line]=13+len(net)-1
 for a,d,op in gates:
  assert wiremap[a] is not None and wiremap[d] is not None
  net.append((wiremap[a],wiremap[d],op));wiremap.append(13+len(net)-1)
 for goal,o in zip(goals,outs):out[goal]=wiremap[len(meta)+o]
 return {'gates':net,'out':[out[w] for w in range(13)],'rows':len(ROWS)}

def main():
 started=time.monotonic();deadline=started+1200
 for kind in range(2):
  goals=[0,1,2] if kind==0 else [0,1,5];ng=8;rng=random.Random(1024+kind)
  base,meta,index=bases(goals)
  samples={r for r,x in enumerate(ROWS) if x.bit_count()==8 and any(not(TARGETS[g]>>r&1) for g in goals)}
  samples.update(rng.sample(range(len(ROWS)),50))
  for it in range(30):
   if time.monotonic()>deadline:break
   c,ops,aa,bb=encode(base,meta,goals,ng,samples)
   stem=f'symbolic-{kind}-{it:02d}';cnf=ROOT/(stem+'.cnf');log=ROOT/(stem+'.log');c.save(cnf)
   print('solve',kind,it,'rows',len(samples),'vars',c.n,'clauses',len(c.cs),'elapsed',round(time.monotonic()-started),flush=True)
   with log.open('w') as f:result=subprocess.run([SOLVER,'-q','--sat','-t','180',str(cnf)],stdout=f,stderr=subprocess.STDOUT)
   status,gates,_=b.extract(log,ops,aa,bb,[])
   print('result',status,'exit',result.returncode,flush=True)
   if status=='unsat':break
   if status!='sat':
    samples.update(rng.sample(range(len(ROWS)),min(500,100*(it+1))));continue
   vals=list(base)
   for a,d,op in gates:vals.append(vals[a]&vals[d] if op else vals[a]|vals[d])
   outs=list(range(ng-len(goals),ng));bad=[]
   for goal,o in zip(goals,outs):
    diff=vals[len(base)+o]^TARGETS[goal];bad.append([r for r in range(len(ROWS)) if diff>>r&1])
   print('errors',[len(x) for x in bad],flush=True)
   if not any(bad):
    candidate=reconstruct(meta,index,goals,gates,outs)
    (ROOT/'counterexample.json').write_text(json.dumps(candidate,indent=2)+'\n')
    print('FOUND',kind,it,flush=True);return
   for rows in bad:rng.shuffle(rows);samples.update(rows[:32])
 print('FINISHED elapsed',round(time.monotonic()-started),flush=True)
if __name__=='__main__':main()
