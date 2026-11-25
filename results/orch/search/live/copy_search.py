"""Experimental first-sharing-wire recurrence; decomposition needs Lean proof.

A root multiset of size m and budget k has deficit k-m+1. A first shared
read-once subformula on s leaves costs s-1; replacing those leaves by two
copies of its output decreases deficit by one. Search is not a Lean proof.
"""
import argparse,importlib.util,json,time
from collections import Counter
from functools import lru_cache
from pathlib import Path
BASE=Path(__file__).resolve().parent.parent
def module(name,path):
 s=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
live=module('live',BASE/'live/live_search.py')
cof=module('cof',BASE/'cofactor/cofactor_prune.py')
exact=module('exact',BASE/'live/exact_cover.py')
class Limit(Exception):pass
class CopySearch:
 def __init__(self,mode=False,cap=19,seconds=60,maxnodes=10000,maxentries=3000):
  self.mode,self.cap,self.seconds,self.maxnodes,self.maxentries=mode,cap,seconds,maxnodes,maxentries
  self.sr=live.Search(mode=mode);self.start=time.monotonic();self.last=self.start
  self.nodes=self.cuts=self.forms=self.entries=self.combines=0;self.seen=set();self.levels={};self.hist=[]
  profiles=[(live.FULL^x,15 if mode else 16)for x in live.INPUTS]
  profiles += [(m,l)for m,l,_ in cof._extra_cofactors(mode)]
  profiles += [(m,l)for m,l,_ in cof.supplemental_cofactors(mode)]
  extras=json.loads((BASE/'cofactor/extra-profile-cuts.json').read_text())['profiles']
  for p in extras:
   m=live.FULL
   for v in p['zeroes']:m &=live.FULL^live.INPUTS[v]
   for v in p['ones']:m &=live.INPUTS[v]
   profiles.append((m,p['lower']))
  self.profiles=tuple(profiles)
  self.inputindex={v:i for i,v in enumerate(live.INPUTS)}
 def checklimit(self):
  now=time.monotonic()
  if now-self.start>self.seconds or self.nodes>=self.maxnodes:raise Limit('time/node limit')
  if now-self.last>10:self.report();self.last=now
 def report(self):
  print(json.dumps(dict(nodes=self.nodes,cuts=self.cuts,forms=self.forms,entries=self.entries,combines=self.combines,seen=len(self.seen),levels=self.levels,seconds=round(time.monotonic()-self.start,3))),flush=True)
 @lru_cache(20000)
 def canon(self,state):
  if all(x in self.inputindex for x in state):
   counts=Counter(state)
   return min(tuple(counts.get(live.INPUTS[p[i]],0)for i in range(10))for p in live.AUTOS)
  return self.sr.canonical(state)
 def prune(self,state,k):
  for mask,lower in self.profiles:
   mass=sum((x&mask)in(0,mask)for x in state)
   if lower+mass<=k:continue
   paid=cof.paid_pool(state,mask,self.mode,self.hist)
   if paid is not None and lower+mass>k+paid[0]:return True
  return False
 def closure(self,state):
  roots=tuple(sorted(set(state)));total=tuple(state.count(x)for x in roots);q=len(roots)
  cols=tuple(self.sr.col(x)for x in roots);entries=[];known=set();required={}
  for i,x in enumerate(roots):
   mult=tuple(int(i==j)for j in range(q));entries.append((mult,x,-1,-1,-1));known.add((mult,x))
  def need(a):
   if a not in required:
    cov=0
    for i,c in enumerate(cols):
     if a[i]<total[i]:cov |=c
    required[a]=self.sr.allcov&~cov
   return required[a]
  j=0
  while j<len(entries):
   if len(entries)>self.maxentries:raise Limit('closure entry cap')
   self.checklimit();aj,b,_,_,_=entries[j]
   for i in range(j+1):
    ai,a,_,_,_=entries[i]
    mask=tuple(x+y for x,y in zip(ai,aj))
    if any(x>t for x,t in zip(mask,total)):continue
    needed=need(mask)
    for op in range(4 if self.mode else 2):
     self.combines+=1
     z=live.opval(op,a,b)
     if z in(0,live.FULL)or(mask,z)in known:continue
     if needed&~self.sr.col(z):continue
     if self.mode:
      outside=[x for h,x in enumerate(roots)if mask[h]<total[h]]+[z]
      if exact.bad_pair(outside,True)is not None:continue
     known.add((mask,z));entries.append((mask,z,i,j,op))
     if mask==total and z==live.TARGET:return roots,entries,len(entries)-1
   j+=1
  self.entries+=len(entries)
  return roots,entries,None
 def replay(self,entries,index):
  mask,z,i,j,op=entries[index]
  if i<0:return
  self.replay(entries,i);self.replay(entries,j)
  self.hist.append((op,entries[i][1],entries[j][1]))
 def dfs(self,state,k):
  self.checklimit()
  key=(k,self.canon(state))
  if key in self.seen:return False
  self.seen.add(key);self.nodes+=1
  deficit=k-len(state)+1;self.levels[deficit]=self.levels.get(deficit,0)+1
  if deficit<0:return False
  if self.prune(state,k):self.cuts+=1;return False
  roots,es,target=self.closure(state);self.forms+=1
  if target is not None:self.replay(es,target);return True
  if deficit==0:return False
  total=Counter(state)
  children=set()
  for index,(mask,z,_,_,_)in enumerate(es):
   used=sum(mask);child=[]
   for r,n in zip(roots,mask):child.extend([r]*(total[r]-n))
   child.extend((z,z));child=tuple(sorted(child));newk=k-used+1
   childkey=(newk,self.canon(child))
   if childkey in children:continue
   children.add(childkey)
   nh=len(self.hist);self.replay(es,index)
   if self.dfs(child,newk):return True
   del self.hist[nh:]
  return False
 def run(self):
  try:print('finished',self.dfs(tuple(sorted(live.INPUTS)),self.cap),flush=True)
  except Limit as e:print('unfinished',str(e),flush=True)
  self.report()
def main():
 p=argparse.ArgumentParser();p.add_argument('--signed',action='store_true');p.add_argument('--cap',type=int,default=19);p.add_argument('--seconds',type=float,default=60);p.add_argument('--nodes',type=int,default=10000);p.add_argument('--entries',type=int,default=3000);a=p.parse_args()
 CopySearch(a.signed,a.cap,a.seconds,a.nodes,a.entries).run()
if __name__=='__main__':main()
