import argparse,ast,hashlib,itertools,json,time
from fractions import Fraction
from pathlib import Path

class Ring:
 def __init__(self,names):
  self.names=names; self.n=len(names); self.zero=(0,)*self.n
 def c(self,x):
  x=Fraction(x); return {self.zero:x} if x else {}
 def x(self,k):
  e=list(self.zero);e[k]=1;return {tuple(e):Fraction(1)}
 def add(self,a,b):
  c=dict(a)
  for e,v in b.items():
   c[e]=c.get(e,0)+v
   if not c[e]:del c[e]
  return c
 def neg(self,a):return {e:-v for e,v in a.items()}
 def mul(self,a,b):
  c={}
  for e,v in a.items():
   for f,w in b.items():
    g=tuple(x+y for x,y in zip(e,f));c[g]=c.get(g,0)+v*w
  return {e:v for e,v in c.items() if v}
 def power(self,a,n):
  assert isinstance(n,int) and n>=0
  b=self.c(1)
  for _ in range(n):b=self.mul(b,a)
  return b
 def parse(self,s):
  def node(t):
   if isinstance(t,ast.Constant) and isinstance(t.value,int):return self.c(t.value)
   if isinstance(t,ast.Name):return self.x(self.names.index(t.id))
   if isinstance(t,ast.UnaryOp) and isinstance(t.op,ast.USub):return self.neg(node(t.operand))
   if isinstance(t,ast.BinOp):
    if isinstance(t.op,ast.Add):return self.add(node(t.left),node(t.right))
    if isinstance(t.op,ast.Sub):return self.add(node(t.left),self.neg(node(t.right)))
    if isinstance(t.op,ast.Mult):return self.mul(node(t.left),node(t.right))
    if isinstance(t.op,ast.Pow):
     assert isinstance(t.right,ast.Constant);return self.power(node(t.left),t.right.value)
    if isinstance(t.op,ast.Div):
     b=node(t.right);assert len(b)==1 and self.zero in b
     return self.mul(node(t.left),self.c(1/b[self.zero]))
   raise ValueError(ast.dump(t))
  return node(ast.parse(s.replace('^','**'),mode='eval').body)
 def terms(self,ts):
  d={}
  for c,e in ts:
   assert len(e)==self.n and all(type(x)==int and x>=0 for x in e)
   k=tuple(e);assert k not in d;d[k]=Fraction(c)
  return {e:v for e,v in d.items() if v}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('conventions');ap.add_argument('--certificate');ap.add_argument('--output',required=True);a=ap.parse_args()
 start=time.monotonic(); cp=Path(a.conventions);j=json.loads(cp.read_text());names=j['variable_order'];R=Ring(names);S=Ring(names+['aa','bb']);n=len(names)
 G=[R.terms(g['terms']) for g in j['generators']]
 assert all(g['index_1based']==k+1 and R.parse(g['polynomial'])==G[k] for k,g in enumerate(j['generators']))
 H=[[None]*4 for _ in range(4)];V=[[None]*4 for _ in range(4)]
 for ix,h,v in zip(j['basis_upper_coordinate_order'],j['H_upper'],j['V_upper']):
  r,c=map(int,ix);H[r][c]=H[c][r]=S.parse(h);V[r][c]=V[c][r]=S.parse(v)
 A=[[S.add(S.c(1),S.add(S.mul(S.x(n),H[r][c]),S.mul(S.x(n+1),V[r][c]))) for c in range(4)] for r in range(4)]
 P=S.c(-24)
 for perm in itertools.permutations(range(4)):
  q=S.c(1)
  for r,c in enumerate(perm):q=S.mul(q,A[r][c])
  P=S.add(P,q)
 coeffs={}
 for e,c in P.items():coeffs.setdefault(e[-2:],{})[e[:n]]=c
 expected=j['coefficient_parameter_order'];assert set(coeffs)==set(map(tuple,expected))
 assert all(coeffs[tuple(ij)]==G[k] for k,ij in enumerate(expected))
 h23=R.parse(j['H_upper'][8]);assert G[12]==R.add(R.mul(R.x(names.index('zz')),h23),R.c(-1))
 assert G[7]==R.mul(R.c(Fraction(1,16)),R.power(G[0],2))
 result={'status':'PASS','scope':'Independent sparse Fraction polynomial arithmetic; all12 generators checked by direct24-permutation permanent, inverse guard and redundant generator identity checked. No inconsistency certificate unless explicitly reported below.','conventions_sha256':hashlib.sha256(cp.read_bytes()).hexdigest(),'generators':13,'generator_terms':[len(g) for g in G],'certificate':None}
 if a.certificate:
  p=Path(a.certificate);c=json.loads(p.read_text());assert c['variable_order']==names
  C=[R.terms(x['terms']) for x in c['cofactors']];assert len(C)==13
  residual=R.c(-1)
  for g,f in zip(G,C):residual=R.add(residual,R.mul(g,f))
  assert not residual, 'Exact rational identity failed'
  result['certificate']={'status':'PASS','identity':'sum(generator_i * cofactor_i) = 1 over QQ','sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'cofactor_terms':[len(x) for x in C]}
 result['seconds']=time.monotonic()-start;Path(a.output).write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
