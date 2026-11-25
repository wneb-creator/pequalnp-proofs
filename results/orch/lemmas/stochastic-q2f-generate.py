from pathlib import Path
from itertools import combinations,product
from collections import Counter
import json,time,hashlib
D=Path('results/orch/lemmas');start=time.monotonic();N=[11,69,49];S=[m for m in range(128) if m!=98 and (m&98)==98]
parent=[]
for t in N:
 pairs=[[m,m] for m in range(128) if m.bit_count()==2 and m&t==m]
 fours=[[m,m] for m in range(128) if m.bit_count()==4 and m&t==t]
 fives=[[a,b] for a,b in combinations([m for m in range(128) if m.bit_count()==5],2) if a&b==t]
 assert len(pairs)==3 and len(fours)==4 and len(fives)==3
 parent.append(pairs+fours+fives)
outside=[m for m in range(128) if m.bit_count()==2 and all(m&t!=m for t in N)]
free={0}|{1<<i for i in range(7)}|set(outside)
packs=[];hist=Counter();cases=[]
for si,s in enumerate(S):
 packs_s=[]
 for a in range(10):
  packs_a=[]
  for b in range(10):
   packs_b=[]
   for c in range(10):
    raw=N+[s]+parent[0][a]+parent[1][b]+parent[2][c];Y=set(raw);assert len(Y)>=7
    shape=all(m.bit_count()<=2 or m in N or m==s for m in Y)
    pack=1330
    if len(Y)==7 and not shape:
     allowed=free|Y;known=free|{m for m in Y if m.bit_count()<=2}
     while True:
      new={z for x in known for y in known for z in [x|y,x&y] if z in allowed}-known
      if not new:break
      known|=new
     large=sorted(m for m in known if m.bit_count()>=3);assert len(large)<=3
     missing=next(i for i,m in enumerate(raw) if m not in known)
     inds=[raw.index(m) for m in large]+[10]*(3-len(large))
     pack=sum(i*11**j for j,i in enumerate(inds))+missing*1331
     hist[len(large)]+=1
     cases.append(dict(s=si,a=a,b=b,c=c,S=s,raw=raw,known_large=large,missing_index=missing,pack=pack))
    packs_b.append(pack)
   packs_a.append(packs_b)
  packs_s.append(packs_a)
 packs.append(packs_s)

def vec(x):return '!['+','.join(vec(y) if isinstance(y,list) else str(y) for y in x)+']'
def ors(xs):return ' || '.join(xs) if xs else 'false'
def ands(xs):return ' &&\n    '.join(xs) if xs else 'true'
cut=[]
for m in range(128):
 row=[]
 if m.bit_count()==3:
  row=[[p,m^p] for p in range(128) if p.bit_count()==2 and p&m==p]
 elif m.bit_count()==4:
  row=[[p,m^p] for p in range(128) if p.bit_count()==2 and p&m==p and p<m^p]
 else:row=[[0,0]]*3
 assert len(row)==3;cut.append(row)
core=[];add=core.append
add('def q2f_tripleCode (i : Fin 3) : Fin 128 := ![11,69,49] i\n')
add('def q2f_parentCode (i : Fin 3) (k : Fin 10) (side : Fin 2) : Fin 128 :=\n  '+vec(parent)+' i k side\n')
add('def q2f_superCode (s : Fin 15) : Fin 128 := '+vec(S)+' s\n')
add('def q2f_raw (s : Fin 15) (a b c : Fin 10) (i : Fin 10) : Fin 128 :=\n  ![11,69,49,q2f_superCode s,q2f_parentCode 0 a 0,q2f_parentCode 0 a 1,\n    q2f_parentCode 1 b 0,q2f_parentCode 1 b 1,q2f_parentCode 2 c 0,q2f_parentCode 2 c 1] i\n')
add('def q2f_codes (s : Fin 15) (a b c : Fin 10) : Finset (Fin 128) :=\n  {'+','.join(f'q2f_raw s a b c {i}' for i in range(10))+'}\n')
add('def q2f_mem (s : Fin 15) (a b c : Fin 10) (m : Fin 128) : Bool :=\n  '+ors([f'decide (m = q2f_raw s a b c {i})' for i in range(10)])+'\n')
for name,expr in [('union','a.val ||| b.val'),('inter','a.val &&& b.val'),('diff','a.val ^^^ (a.val &&& b.val)')]:
 add(f'def q2f_{name} (a b : Fin 128) : Fin 128 :=\n  ⟨({expr}) % 128, Nat.mod_lt _ (by decide)⟩\n')
add('def q2f_sub (a b : Fin 128) : Bool := decide ((a.val &&& b.val) = a.val)\n')
add('def q2f_outside (m : Fin 128) : Bool :=\n  '+ors([f'decide (m = {m})' for m in outside])+'\n')
add('def q2f_small (s : Fin 15) (a b c : Fin 10) (m : Fin 128) : Bool :=\n  decide (cap7_card m ≤ 1) || (decide (cap7_card m = 2) && (q2f_outside m || q2f_mem s a b c m))\n')
add('def q2f_allowed (s : Fin 15) (a b c : Fin 10) (m : Fin 128) : Bool :=\n  q2f_small s a b c m || q2f_mem s a b c m\n')
for si,row in enumerate(packs):add(f'def q2f_pack{si} (a b c : Fin 10) : ℕ :=\n  {vec(row)} a b c\n')
add('def q2f_pack (s : Fin 15) (a b c : Fin 10) : ℕ :=\n  '+vec([f'q2f_pack{i} a b c' for i in range(15)])+' s\n')
add('def q2f_known (s : Fin 15) (a b c : Fin 10) (j : Fin 3) : Fin 128 :=\n  let k := q2f_pack s a b c / 11^j.val % 11\n  if h : k < 10 then q2f_raw s a b c ⟨k,h⟩ else 0\n')
add('def q2f_missing (s : Fin 15) (a b c : Fin 10) : Fin 128 :=\n  q2f_raw s a b c ⟨q2f_pack s a b c / 1331 % 10,Nat.mod_lt _ (by decide)⟩\n')
add('def q2f_closed (s : Fin 15) (a b c : Fin 10) (m : Fin 128) : Bool :=\n  q2f_small s a b c m || '+ors([f'decide (m = q2f_known s a b c {i})' for i in range(3)])+'\n')
add('def q2f_cut (m : Fin 128) (j : Fin 3) (side : Fin 2) : Fin 128 :=\n  '+vec(cut)+' m j side\n')
add('def q2f_seed (s : Fin 15) (a b c : Fin 10) (m : Fin 128) : Bool :=\n  decide (cap7_card m = 3 ∨ cap7_card m = 4) &&\n    ('+ors([f'(q2f_small s a b c (q2f_cut m {i} 0) && q2f_small s a b c (q2f_cut m {i} 1))' for i in range(3)])+')\n')
add('def q2f_grow (s : Fin 15) (a b c : Fin 10) (x m : Fin 128) : Bool :=\n  q2f_sub x m && q2f_small s a b c (q2f_diff m x)\n')
add('def q2f_node (s : Fin 15) (a b c : Fin 10) (i : Fin 10) : Bool :=\n  let m := q2f_raw s a b c i\n  q2f_closed s a b c m ||\n    (!q2f_seed s a b c m && '+ands([f'!q2f_grow s a b c (q2f_known s a b c {j}) m' for j in range(3)])+')\n')
add('def q2f_pair (s : Fin 15) (a b c : Fin 10) (i j : Fin 3) : Bool :=\n  let u := q2f_union (q2f_known s a b c i) (q2f_known s a b c j)\n  let v := q2f_inter (q2f_known s a b c i) (q2f_known s a b c j)\n  (!q2f_allowed s a b c u || q2f_closed s a b c u) &&\n    (!q2f_allowed s a b c v || q2f_closed s a b c v)\n')
add('def q2f_generators (s : Fin 15) (a b c : Fin 10) : Bool :=\n  '+ands([f'q2f_node s a b c {i}' for i in range(10)]+[f'q2f_pair s a b c {i} {j}' for i,j in combinations(range(3),2)])+'\n')
add('def q2f_shape (s : Fin 15) (a b c : Fin 10) : Bool :=\n  '+ands([f'(decide (cap7_card (q2f_raw s a b c {i}) ≤ 2) || decide (q2f_raw s a b c {i} = 11) || decide (q2f_raw s a b c {i} = 69) || decide (q2f_raw s a b c {i} = 49) || decide (q2f_raw s a b c {i} = q2f_superCode s))' for i in range(10)])+'\n')
add('def q2f_certificate (s : Fin 15) (a b c : Fin 10) : Bool :=\n  decide (7 ≤ (q2f_codes s a b c).card) &&\n    (decide (8 ≤ (q2f_codes s a b c).card) || q2f_shape s a b c ||\n      (q2f_generators s a b c && !q2f_closed s a b c (q2f_missing s a b c)))\n')
tail='\n'.join(core);primitive=(D/'formalization-cap-seven-core.lean').read_text().split('def cap7_tripleCode',1)[0]
(D/'stochastic-q2f-core-tail.lean').write_text(tail)
(D/'stochastic-q2f-core.lean').write_text(primitive+tail+'\nend PEqualNP.Outside.L_meta_6659_aux\n')
# Independent Python evaluation of the compressed generator certificate.
def cutfn(m):return cut[m]
for row in cases:
 s,a,b,c=row['s'],row['a'],row['b'],row['c'];raw=row['raw'];Y=set(raw);K=row['known_large']+[0]*(3-len(row['known_large']))
 small=lambda m:m.bit_count()<=1 or (m.bit_count()==2 and (m in outside or m in Y))
 closed=lambda m:small(m) or m in K
 allowed=lambda m:small(m) or m in Y
 for m in raw:
  if closed(m):continue
  seed=m.bit_count() in [3,4] and any(small(x) and small(y) for x,y in cutfn(m))
  assert not seed
  assert all(not(x&m==x and small(m^x)) for x in K)
 for x,y in combinations(K,2):
  for z in [x|y,x&y]:assert not allowed(z) or closed(z)
 assert not closed(raw[row['missing_index']])
report={'scope':'Generated q2 family-shape closed-witness Boolean core; no Lean compilation yet. All4,902 bad-shape size7 families have valid independently evaluated compressed closure witnesses.','required':N,'super_codes':S,'parent_codes':parent,'bad_shape_family_count':len(cases),'known_large_histogram':dict(hist),'core_sha256':hashlib.sha256((D/'stochastic-q2f-core.lean').read_bytes()).hexdigest(),'tail_sha256':hashlib.sha256((D/'stochastic-q2f-core-tail.lean').read_bytes()).hexdigest(),'seconds':time.monotonic()-start,'cases':cases}
(D/'stochastic-q2f-generator-data.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k!='cases'}))
