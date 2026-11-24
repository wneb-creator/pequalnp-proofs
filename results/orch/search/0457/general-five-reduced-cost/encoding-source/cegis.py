import itertools, json, pathlib, random, subprocess, time
ROOT=pathlib.Path('/tmp/oec/pequalnp-pilot-21/search')
SOLVER='/tmp/oec/pequalnp-pilot-21/setup/lean-4.36.0-linux/bin/cadical'
ROWS=[x for x in range(1<<13) if x.bit_count() in (7,8)]
MASK=(1<<len(ROWS))-1
INPUTS=[sum(1<<r for r,x in enumerate(ROWS) if x>>i&1) for i in range(13)]
LINES=[[(w+i)%13 for i in (0,1,3,9)] for w in range(13)]
TARGETS=[sum(1<<r for r,x in enumerate(ROWS) if any(x>>i&1 for i in L)) for L in LINES]
class CNF:
 def __init__(self): self.n=0;self.cs=[]
 def var(self): self.n+=1;return self.n
 def add(self,*xs): self.cs.append(xs)
 def one(self,xs):
  self.add(*xs)
  if len(xs)==1:return
  aux=[self.var() for _ in xs[:-1]]
  self.add(-xs[0],aux[0])
  for i in range(1,len(xs)-1):
   self.add(-xs[i],aux[i]);self.add(-aux[i-1],aux[i]);self.add(-xs[i],-aux[i-1])
  self.add(-xs[-1],-aux[-1])
 def save(self,path):
  with path.open('w') as f:
   f.write(f'p cnf {self.n} {len(self.cs)}\n')
   for c in self.cs:f.write(' '.join(map(str,c))+' 0\n')
def fixed(goals,rng):
 net=[];vals=list(INPUTS);base=list(INPUTS);real=list(range(13));out={}
 others=[w for w in range(13) if w not in goals];rng.shuffle(others)
 for w in others:
  a=LINES[w].copy();rng.shuffle(a);k=13+len(net)
  gates=[(a[0],a[1],False)]
  if rng.randrange(2):gates.extend([(a[2],a[3],False),(k,k+1,False)])
  else:gates.extend([(k,a[2],False),(k+1,a[3],False)])
  for j,(x,y,op) in enumerate(gates):
   v=vals[x]|vals[y];net.append((x,y,op));vals.append(v)
   if j<2:base.append(v);real.append(13+len(net)-1)
  out[w]=13+len(net)-1
 return net,base,real,out
def encode(base,goals,ng,samples):
 c=CNF();ops=[c.var() for _ in range(ng)]
 aa=[];bb=[]
 for j in range(ng):
  a=[c.var() for _ in range(len(base)+j)];b=[c.var() for _ in a]
  c.one(a);c.one(b)
  for x in range(len(a)):
   for y in range(x+1):c.add(-a[x],-b[y])
  aa.append(a);bb.append(b)
 outs=[[c.var() for _ in range(ng)] for _ in goals]
 for out in outs:c.one(out)
 for r in sorted(samples):
  vs=[c.var() for _ in range(ng)]
  for j in range(ng):
   a=c.var();b=c.var();v=vs[j];op=ops[j]
   for selections,dest in ((aa[j],a),(bb[j],b)):
    for k,sel in enumerate(selections):
     if k<len(base):c.add(-sel,dest if base[k]>>r&1 else -dest)
     else:
      src=vs[k-len(base)];c.add(-sel,-src,dest);c.add(-sel,src,-dest)
   c.add(-op,-a,-b,v);c.add(-op,a,-v);c.add(-op,b,-v)
   c.add(op,a,b,-v);c.add(op,-a,v);c.add(op,-b,v)
  for goal,out in zip(goals,outs):
   for j,sel in enumerate(out):c.add(-sel,vs[j] if TARGETS[goal]>>r&1 else -vs[j])
 return c,ops,aa,bb,outs
def extract(path,ops,aa,bb,outs):
 pos=set();status='unknown'
 for l in path.read_text().splitlines():
  if l=='s SATISFIABLE':status='sat'
  if l=='s UNSATISFIABLE':status='unsat'
  if l.startswith('v '):pos.update(int(x) for x in l[2:].split() if int(x)>0)
 if status!='sat':return status,None,None
 gates=[]
 for op,a,b in zip(ops,aa,bb):
  gates.append((next(i for i,v in enumerate(a) if v in pos),next(i for i,v in enumerate(b) if v in pos),op in pos))
 output=[next(i for i,v in enumerate(out) if v in pos) for out in outs]
 return status,gates,output
def main():
 started=time.monotonic();deadline=started+900
 for seed in range(1000):
  if time.monotonic()>deadline:break
  rng=random.Random(102400+seed);goals=[0,1,2] if seed%2==0 else [0,1,5];ng=8
  net,base,real,fixedouts=fixed(goals,rng)
  samples={r for r in range(len(ROWS)) if any(not(TARGETS[g]>>r&1) for g in goals)}
  samples.update(rng.sample(range(len(ROWS)),80))
  for it in range(40):
   if time.monotonic()>deadline:break
   c,ops,aa,bb,outs=encode(base,goals,ng,samples)
   stem=f'cegis-{seed:03d}-{it:02d}';cnf=ROOT/(stem+'.cnf');log=ROOT/(stem+'.log')
   c.save(cnf)
   print('solve',seed,it,'rows',len(samples),'vars',c.n,'clauses',len(c.cs),'elapsed',round(time.monotonic()-started),flush=True)
   with log.open('w') as f:
    result=subprocess.run([SOLVER,'-q','-t','45',str(cnf)],stdout=f,stderr=subprocess.STDOUT)
   status,gates,out=extract(log,ops,aa,bb,outs)
   print('result',status,'exit',result.returncode,flush=True)
   if status!='sat':break
   vals=list(base)
   for a,b,op in gates:vals.append(vals[a]&vals[b] if op else vals[a]|vals[b])
   bad=[]
   for goal,o in zip(goals,out):
    diff=vals[len(base)+o]^TARGETS[goal]
    bad.append([r for r in range(len(ROWS)) if diff>>r&1])
   print('errors',[len(x) for x in bad],flush=True)
   if not any(bad):
    actual=list(net);wiremap=list(real)
    for a,b,op in gates:
     actual.append((wiremap[a],wiremap[b],op));wiremap.append(13+len(actual)-1)
    for goal,o in zip(goals,out):fixedouts[goal]=wiremap[len(base)+o]
    candidate={'seed':seed,'gates':actual,'out':[fixedouts[w] for w in range(13)],'rows':len(ROWS)}
    (ROOT/'counterexample.json').write_text(json.dumps(candidate,indent=2)+'\n')
    print('FOUND',seed,it,flush=True);return
   for rows in bad:
    rng.shuffle(rows);samples.update(rows[:24])
 print('FINISHED elapsed',round(time.monotonic()-started),flush=True)
if __name__=='__main__':main()
