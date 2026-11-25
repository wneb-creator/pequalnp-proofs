import json
from itertools import product,combinations_with_replacement
from collections import Counter
from pathlib import Path

def candidate(groups,features):
 k=1+max(i for g in groups for i in g);b=len(groups)
 points=set(i for a,l in features for i in groups[l] if i!=a)
 lines=set(j for a,l in features for j,g in enumerate(groups) if a in g and j!=l)
 es=[(p,k+j) for j in lines for p in groups[j] if p in points]
 par={};v=0
 def root(x):
  while par[x]!=x:x=par[x]
  return x
 for p,j in es:
  par.setdefault(p,p);par.setdefault(j,j);u,w=root(p),root(j)
  if u==w:v+=1
  else:par[u]=w
 return v
if __name__=='__main__':
 for name in ['fresh-singer-q3k7o3.json','fresh-singer-q3k8o2.json','affine','q3']:
  if name=='q3':k=13;g=[[i for i in range(13) if (i-j)%13 in (0,1,3,9)] for j in range(13)]
  elif name=='affine':
   k=9;from fresh_affine_charge import affine
   gm,_,_=affine();g=[[i for i in range(9) if m>>i&1] for m in gm]
  else:
   r=json.loads(Path(name).read_text());k=len(r['points']);g=r['groups']
  f=list(product(range(k),range(len(g))))
  d=Counter();ex=None
  for ass in combinations_with_replacement(f,2):
   n=candidate(g,ass);d[n]+=1
   if n==max(d):ex=ass
  print(name,sorted(d.items()),'maxex',ex)
