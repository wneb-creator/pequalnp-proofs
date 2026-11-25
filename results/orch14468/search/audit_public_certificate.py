#!/usr/bin/env python3
"""Independent scalar replay of PR18915's complete signed five-input atlas."""
import itertools,json,re,hashlib,pathlib
SRC=pathlib.Path('/tmp/oec/pequalnp-pilot-103/14468-pr18915-source.lean')
s=SRC.read_text();M=(1<<512)-1;B=(1<<152)-1
def block(name):return s.split('def '+name,1)[1].split('\ndef ',1)[0]
def cols(name):return [int(h,16)for h in re.findall(r'=> (0x[0-9a-f]+)',block(name))]
pos,neg=cols('gbPos'),cols('gbNeg');assert len(pos)==len(neg)==5
P=[sum(((v>>i)&1)<<j for j,v in enumerate(pos))for i in range(152)]
Q=[sum(((v>>i)&1)<<j for j,v in enumerate(neg))for i in range(152)]
G=int(re.search(r'def gbAtlas.*?, (0x[0-9a-f]+), gbN',s).group(1),16)
F=int(re.search(r'def fullWord : Sig := (0x[0-9a-f]+)',s).group(1),16)
inp=[sum(((r>>j)&1)<<r for r in range(512))for j in range(9)]
declared_inputs=[int(h,16)for h in re.findall(r'0x[0-9a-f]+',block('inputs'))];assert declared_inputs==inp
mapping=[5,1,3,6,7,2,4,0];E=[(0,4),(1,5),(0,6),(2,6),(0,7),(1,7),(2,7),(3,7),(5,7)]
assert all(bool(F>>r&1)==any(r>>mapping[u]&1 and r>>mapping[v]&1 for u,v in E)for r in range(512))
assert all((G>>r&1)==(F>>(r&~224)&1)for r in range(512))
assert all(G>>p&1 and not(G>>q&1)for p,q in zip(P,Q))
def essential(roots,T,triples):
 for j,r,t in triples:
  assert bool(T>>r&1)!=bool(T>>t&1)
  assert all((r>>i&1)==(t>>i&1)for i in roots if i!=j)
essential(range(5),G,[(0,2,3),(1,1,3),(2,1,5),(3,1,9),(4,8,24)])
essential(mapping,F,[(5,1,33),(6,1,65),(7,32,160)])
words={k:int(re.search(r'\| 0 => (0x[0-9a-f]+)',block('gbK'+str(k))).group(1),16)for k in range(2,7)}
counts={int(k):int(n)for k,n in re.findall(r'\| (\d+) => (\d+)',block('gbN'))}
assert counts=={6:1,5:44,4:91,3:25,2:5}
def at(k,pos,n):return(words.get(k,0)>>pos)&((1<<n)-1)
def binary(op,a,b):return a&b if op==0 else a|b if op==1 else a&(~b&M)if op==2 else(~a&M)&b
def record(k,i):
 d=6-k;width=5+11*d;return at(k,i*width,width)
def decode(k,i):
 v=record(k,i);d=6-k;w=inp[:5]
 for j in range(d):
  op=(v>>(10*j+8))&3;a=(v>>(10*j))&15;b=(v>>(10*j+4))&15
  assert a<len(w)and b<len(w),(k,i,j,a,b)
  w.append(binary(op,w[a],w[b]))
 live=v>>(10*d);return[w[j]for j in range(len(w))if live>>j&1]
rows={k:[decode(k,i)for i in range(n)]for k,n in counts.items()}
assert rows[6][0]==inp[:5]
lookup={6:(6,1,5,1,2,1),5:(788,14,704,6,53,7),4:(2667,30,2457,7,110,8),3:(1006,8,950,7,81,6),2:(249,1,245,4,12,4)}
def locate(k,h):
 if k not in lookup:return 0
 base,mod,offset,shiftwidth,slots,width=lookup[k]
 j=(h//mod+at(k,offset+(h%mod)*shiftwidth,shiftwidth))%slots
 return at(k,base+j*width,width)
def keyword(v):
 m=(1<<61)-1;n=v%m;return((n*n%m)*(n+7)+971*n)%m
cache={}
def separation(v):
 if v not in cache:cache[v]=sum((((v>>p)^(v>>q))&1)<<i for i,(p,q)in enumerate(zip(P,Q)))
 return cache[v]
stats={'nodes':0,'moves':0,'length_pruned':0,'separation_pruned':0,'constant_or_redundant_pruned':0,'linked':0}
for k in sorted(rows):
 for i,ws in enumerate(rows[k]):
  assert len(set(ws))==len(ws)and G not in ws
  stats['nodes']+=1
  for a,b in itertools.combinations(ws,2):
   for op in range(4):
    z=binary(op,a,b)
    for ka,kb in itertools.product([False,True],repeat=2):
     stats['moves']+=1;rest=[w for w in ws if(w!=a or ka)and(w!=b or kb)];child=[z]+rest
     if len(child)>k:stats['length_pruned']+=1;continue
     sep=0
     for w in child:sep|=separation(w)
     if sep!=B:stats['separation_pruned']+=1;continue
     if z in(0,M)or z in ws:stats['constant_or_redundant_pruned']+=1;continue
     h=sum(keyword(w)for w in child);code=locate(k-1,h);j=code//2
     assert j<counts.get(k-1,0),(k,i,op,ka,kb,'badlookup',j)
     assert set(rows[k-1][j])==set(child),(k,i,op,ka,kb,'different child',j)
     stats['linked']+=1
mono=[(1,1,3),(1,8,5),(0,9,7),(1,0,2),(1,6,7),(0,11,12),(0,1,5),(0,0,4),(1,10,13),(1,16,14),(1,17,15)]
for x in range(256):
 w=[bool(x>>j&1)for j in range(8)]
 for op,a,b in mono:w.append(w[a]or w[b]if op else w[a]and w[b])
 assert w[-1]==any(x>>u&1 and x>>v&1 for u,v in E)
result={'verdict':'PASS','source':str(SRC),'sha256':hashlib.sha256(SRC.read_bytes()).hexdigest(),'scope':'Independent full scalar replay of all166 atlas nodes and all binary/retention children; numeric truth and slice data; not a substitute for Lean semantic proof','input_signatures_checked':9,'full_truth_rows_checked':512,'separator_pairs_checked':152,'core_essential_witnesses_checked':5,'lift_essential_witnesses_checked':3,'monotone_witness_rows_checked':256,'counts':counts,**stats}
out=pathlib.Path('results/orch14468/search/public-certificate-audit.json');out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
