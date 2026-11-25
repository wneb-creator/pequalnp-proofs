import argparse,hashlib,itertools,json,re
from pathlib import Path
ap=argparse.ArgumentParser();ap.add_argument('--input',required=True);ap.add_argument('--p',type=int,required=True);ap.add_argument('--l',type=int,required=True);ap.add_argument('--edges',required=True);ap.add_argument('--out',required=True);a=ap.parse_args();p,l,n=a.p,a.l,a.p+a.l;E={tuple(map(int,e.split(','))) for e in a.edges.split(';')};src=Path(a.input).read_text()
assert p==l and len(E)>=2 and '(bvnot b0)' in src
rowsets=[frozenset(b for aa,b in E if aa==i) for i in range(p)];colsets=[frozenset(aa for aa,b in E if b==j) for j in range(l)]
assert len(set(rowsets))==p and len(set(colsets))==l
rowdict={s:i for i,s in enumerate(rowsets)};coldict={s:i for i,s in enumerate(colsets)};autos=[]
for perm in itertools.permutations(range(p)):
 transformed=[frozenset(perm[i] for i in s) for s in colsets]
 if all(s in coldict for s in transformed):autos.append(tuple(perm)+tuple(p+coldict[s] for s in transformed))
 if all(s in rowdict for s in transformed):autos.append(tuple(p+perm[i] for i in range(p))+tuple(rowdict[s] for s in transformed))
autos=sorted(set(autos));graph={frozenset((u,p+v)) for u,v in E}
for perm in autos:
 assert len(set(perm))==n
 assert {frozenset((perm[u],perm[p+v])) for u,v in E}==graph
raw={int(i):(int(w),int(v)) for i,w,v in re.findall(r'\(define-fun f(\d+) \(\) \(_ BitVec (\d+)\) \(_ bv(\d+) \d+\)\)',src)}
assert set(raw)==set(range(n));W=raw[0][0];assert all(w==W for w,v in raw.values());vals=[raw[i][1] for i in range(n)];ones=(1<<W)-1
assert f'(define-fun f{n} () (_ BitVec {W}) (bvor a0 b0))' in src
rows=[sum(((vals[i]>>j)&1)<<i for i in range(n)) for j in range(W)]
def f(x):return any((x>>u&1) and (x>>(p+v)&1) for u,v in E)
positive=sum(1<<j for j,x in enumerate(rows) if f(x));mt=re.search(r'\(assert \(= out \(_ bv(\d+) (\d+)\)\)\)',src);assert mt and int(mt.group(1))==positive and int(mt.group(2))==W
expected={1<<u|1<<(p+v) for u,v in E}|{x for x in range(1<<n) if not f(x) and all((x>>i&1) or f(x|(1<<i)) for i in range(n))};assert set(rows)==expected
terms=[1<<i for i in range(n)]+sorted(1<<u|1<<(p+v) for u,v in E)
def tv(mask):
 r=ones
 for i in range(n):
  if mask>>i&1:r&=vals[i]
 return r
truth={m:tv(m) for m in terms}
def move(mask,perm):return sum(1<<perm[i] for i in range(n) if mask>>i&1)
allowed=[];candidates=0
for ma in terms:
 for mb in terms:
  va,vb=truth[ma],truth[mb]
  if va>vb or not(va&~vb&positive) or not(vb&~va&positive):continue
  candidates+=1;v=va|vb
  least=min(truth[move(ma,perm)]|truth[move(mb,perm)] for perm in autos)
  if v==least:allowed.append((ma,mb))
assert allowed
assert 'symcase' not in src
parts=[]
for q,(ma,mb) in enumerate(allowed):
 name=f'symcase{q}'
 parts.append(f'(declare-const {name} Bool)')
 lits=[f'{side}0s{i}' if mask>>i&1 else f'(not {side}0s{i})' for side,mask in [('a',ma),('b',mb)] for i in range(n)]
 parts += [f'(assert (or (not {name}) {lit}))' for lit in lits]
parts.append('(assert (or '+' '.join(f'symcase{q}' for q in range(len(allowed)))+'))')
constraint='\n'.join(parts)+'\n';out=src.replace('(check-sat',constraint+'(check-sat',1);Path(a.out).write_text(out)
meta={'input':a.input,'input_sha256':hashlib.sha256(src.encode()).hexdigest(),'output':a.out,'output_sha256':hashlib.sha256(out.encode()).hexdigest(),'p':p,'l':l,'edges':sorted(E),'boundary_rows':rows,'automorphisms':autos,'first_or_candidates':candidates,'allowed_first_or_pairs':allowed}
Path(a.out+'.json').write_text(json.dumps(meta,indent=2));print(json.dumps({k:v for k,v in meta.items() if k not in ['automorphisms','boundary_rows','edges','allowed_first_or_pairs']}));print('Verified graph automorphisms:',len(autos),'first-OR candidates:',candidates,'canonical pairs:',len(allowed))
