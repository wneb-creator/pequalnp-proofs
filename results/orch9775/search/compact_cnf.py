#!/usr/bin/env python3
"""Emit exactly the Compact.Scheme clauses from upstream L9774 for a graph.

No extra symmetry or synthesis restrictions. SAT is only a necessary-layout
model, never a circuit witness. UNSAT needs the Lean layout hypotheses.
"""
import argparse,itertools,json,pathlib,subprocess,time,hashlib

NEW=[(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)]
OLD=[(0,8),(0,10),(1,7),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)]
SOLVER='/tmp/oec/pequalnp-pilot-103/setup/lean-4.36.0-linux/bin/cadical'

class Encoder:
 def __init__(self,I,k,old=False,all_independent=False,no_exact=False,paired=False):
  self.I,self.k,self.edges,self.no_exact=I,k,OLD if old else NEW,no_exact
  self.paired=paired
  self.adj=[[False]*14 for _ in range(14)]
  for u,v in self.edges:self.adj[u][v]=self.adj[v][u]=True
  inds=[m for m in range(1<<14) if all(not(m>>u&1 and m>>v&1) for u,v in self.edges)]
  self.masks=inds if all_independent else [m for m in inds if all(m>>x&1 or any(m>>y&1 and self.adj[x][y] for y in range(14)) for x in range(14))]
  self.facts=[];self.ids={};self.clauses=[];self.schemes=[]
 def cap(self,x):return 1 if self.I>>x&1 else 2+self.k
 def var(self,f):
  f=tuple(f)
  if f not in self.ids:self.ids[f]=len(self.facts)+1;self.facts.append(f)
  return self.ids[f]
 def add(self,s,*ls):
  c=[self.var(f) if p else -self.var(f) for f,p in ls]
  self.schemes.append(s);self.clauses.append(c)
 def build(self):
  p=lambda f:(f,True);n=lambda f:(f,False)
  common=lambda x,c:('common',min(x,c),max(x,c))
  for x in range(14):
   for j in range(self.cap(x)):
    self.add(('self',x,j),p(('lab',x,j,x)))
    if j+1<self.cap(x):self.add(('earlier',x,j),n(('live',x,j+1)),p(('live',x,j)))
    for c in range(14):self.add(('labCommon',x,c,j),n(('live',x,j)),n(('lab',x,j,c)),p(common(x,c)))
   self.add(('someRes',x),n(('live',x,2)),*[p(('res',t,x)) for t in range(self.k)])
   for t in range(self.k):self.add(('allRes',x,t),n(('live',x,1+self.k)),p(('res',t,x)))
   for a in self.masks:
    if not any(a>>v&1 and self.adj[x][v] for v in range(14)):continue
    self.add(('exposure',x,a),*[p(('avoid',x,a,j)) for j in range(self.cap(x))])
    for j in range(self.cap(x)):
     self.add(('avoidLive',x,a,j),n(('avoid',x,a,j)),p(('live',x,j)))
     for c in range(14):
      if a>>c&1:self.add(('avoidNot',x,c,a,j),n(('avoid',x,a,j)),n(('lab',x,j,c)))
   for i in range(14):
    if (self.no_exact and not self.paired) or not(self.I>>i&1 and self.adj[i][x]):continue
    for a in self.masks:
     if not a>>x&1:continue
     if not self.no_exact:self.add(('exactAt',x,i,a),*[p(('see',x,i,a,j)) for j in range(self.cap(x))])
     for j in range(self.cap(x)):
      self.add(('seeLive',x,i,a,j),n(('see',x,i,a,j)),p(('live',x,j)))
      for c in range(14):
       if a>>c&1:self.add(('seeLab',x,i,c,a,j),n(('see',x,i,a,j)),(('lab',x,j,c),self.adj[i][c]))
   for c in range(14):
    for t in range(self.k):
     self.add(('diffX',t,x,c),n(('diff',t,x,c)),p(('res',t,x)))
     self.add(('diffC',t,x,c),n(('diff',t,x,c)),n(('res',t,c)))
     self.add(('resCommon',x,c,t),n(('res',t,x)),n(('res',t,c)),p(common(x,c)))
    for i in range(14):
     if self.I>>i&1 and self.adj[i][x] and self.adj[i][c]:self.add(('adjacentCommon',x,c,i),p(common(x,c)))
    if x!=c and not self.I>>x&1:
     for j,l in itertools.combinations(range(self.cap(x)),2):
      self.add(('residual',x,c,j,l),n(common(x,c)),n(('live',x,l)),p(('lab',x,j,c)),p(('lab',x,l,c)),*[p(('diff',t,x,c)) for t in range(self.k)])
  if self.paired:
   for a in self.masks:
    for i,j in itertools.permutations([v for v in range(14) if self.I>>v&1],2):
     if not any(a>>v&1 and self.adj[j][v] and not self.adj[i][v] for v in range(14)):continue
     for x in range(14):
      if not(a>>x&1 and self.adj[i][x]):continue
      for y in range(14):
       if a>>y&1 and self.adj[j][y]:self.add(('pairedExact',x,i,y,j,a),*[p(('see',x,i,a,l)) for l in range(self.cap(x))],*[p(('see',y,j,a,l)) for l in range(self.cap(y))])
  for s in [False,True]:
   for e,edge in enumerate(self.edges):
    x=edge[int(s)]
    self.add(('readerAny',s,e),*[p(('reader',s,e,j)) for j in range(self.cap(x))])
    for j in range(self.cap(x)):
     self.add(('readerLive',s,e,j),n(('reader',s,e,j)),p(('live',x,j)))
     for c in range(14):
      for d in [False,True]:self.add(('readerLab',s,e,j,c,d),n(('reader',s,e,j)),(('lab',x,j,c),not d),(('es',s,e,c),d))
  for e,f in itertools.combinations(range(len(self.edges)),2):
   for s in [False,True]:
    if self.edges[e][int(s)]==self.edges[f][int(s)]:
     for j in range(self.cap(self.edges[e][int(s)])):
      self.add(('gateEq',s,e,f,j),n(('reader',s,e,j)),n(('reader',s,f,j)),p(('gate',e,f)))
    for c in range(14):
     for d in [False,True]:self.add(('eqLab',s,e,f,c,d),n(('gate',e,f)),(('es',s,e,c),not d),(('es',s,f,c),d))
  return self
 def save(self,path):
  path=pathlib.Path(path);path.parent.mkdir(parents=True,exist_ok=True)
  cnf=path.with_suffix('.cnf')
  cnf.write_text(f'p cnf {len(self.facts)} {len(self.clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in self.clauses))
  data={'I':self.I,'k':self.k,'no_exact':self.no_exact,'paired':self.paired,'edges':self.edges,'masks':self.masks,'facts':self.facts,'schemes':self.schemes,'clauses':self.clauses,'cnf_sha256':hashlib.sha256(cnf.read_bytes()).hexdigest()}
  path.with_suffix('.json').write_text(json.dumps(data,separators=(',',':'))+'\n')
  return cnf

def main():
 ap=argparse.ArgumentParser();ap.add_argument('I',type=int);ap.add_argument('output');ap.add_argument('--k',type=int);ap.add_argument('--old',action='store_true');ap.add_argument('--all-independent',action='store_true');ap.add_argument('--no-exact',action='store_true');ap.add_argument('--paired',action='store_true');ap.add_argument('--seconds',type=int,default=0);a=ap.parse_args()
 k=a.I.bit_count()-3 if a.k is None else a.k
 assert k>=0
 en=Encoder(a.I,k,a.old,a.all_independent,a.no_exact,a.paired).build();cnf=en.save(a.output)
 print(json.dumps({'I':a.I,'k':k,'vars':len(en.facts),'clauses':len(en.clauses),'cnf':str(cnf)}),flush=True)
 if a.seconds:
  stem=pathlib.Path(a.output);start=time.time()
  with stem.with_suffix('.stdout').open('w') as out,stem.with_suffix('.stderr').open('w') as err:
   r=subprocess.run([SOLVER,'--lrat','--no-binary','-t',str(a.seconds),str(cnf),str(stem.with_suffix('.lrat'))],stdout=out,stderr=err)
  record={'I':a.I,'k':k,'exit_code':r.returncode,'seconds':time.time()-start,'verdict':{10:'SAT',20:'UNSAT',0:'UNKNOWN'}.get(r.returncode,'ERROR')}
  stem.with_suffix('.result.json').write_text(json.dumps(record)+'\n');print(json.dumps(record),flush=True)
if __name__=='__main__':main()
