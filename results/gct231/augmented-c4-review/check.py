from pathlib import Path
import hashlib,json,itertools
import sympy as S
base=Path(__file__).resolve().parents[1]
alpha,beta,gamma,u,v,P,B,A,U,V,sat,lam=S.symbols('alpha beta gamma u v P B A U V sat lam')
loc={str(x):x for x in (alpha,beta,gamma,u,v,P,B,A,U,V,sat,lam)}
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
hashes={}
def read(name):
 p=base/name;hashes[name]=digest(p);return json.loads(p.read_text())
for case in (2,3):
 full=read(f'fresh/c4-nonzero-square-{case}.json')
 old=read(f'fresh/c4-nonzero-reduced-{case}.json')
 new=read(f'c4-nonzero-augmented-{case}.json')
 assert new['square_source_sha256']==hashes[f'fresh/c4-nonzero-square-{case}.json']
 assert new['reduced_source_sha256']==hashes[f'fresh/c4-nonzero-reduced-{case}.json']
 assert len(old['equations'])==6 and len(new['equations'])==7
 assert new['equations'][:6]==old['equations']
 for key,value in old.items():
  if key not in ('equations','scope'):assert new[key]==value
 assert full['equation_labels'][4]=='square_cubic' and new['square_source_index']==4
 source=S.sympify(full['equations'][4],locals=loc)
 square=S.sympify(new['equations'][6],locals=loc)
 if case==2:
  substitution={alpha:P/beta,gamma:1/P,u:U,v:V/beta};pullback={B:beta**2};den=216*beta**8
  rootpoint={P:-2,B:1,U:0,V:6,sat:-S.Rational(1,26)}
 else:
  substitution={gamma:1/(alpha*beta),u:U,v:V/alpha};pullback={A:alpha**2};den=27*alpha**2
  rootpoint={A:4,beta:S.Rational(1,2),U:0,V:-12,sat:S.Rational(1,13)}
 # Check a rational-function identity directly, not even-power conversion code.
 assert S.cancel(source.subs(substitution,simultaneous=True)-square.subs(pullback)/den)==0
 assert S.sympify(new['square_discarded_denominator'],locals=loc)==den
 variables=[loc[x] for x in new['variables']];poly=S.Poly(square,*variables,domain=S.QQ)
 assert poly.primitive()[0]==1 and new['square_primitive_content']=='1'
 assert poly.total_degree()==14 and len(poly.terms())==(258 if case==2 else 292)
 assert square.subs(rootpoint)==S.sympify(new['square_at_known_rational_point'])
 # Recompute the omitted pencil condition directly from the frozen matrices.
 GW=S.Matrix([[S.sympify(x,locals=loc) for x in row] for row in full['gram_W']])
 GR=S.Matrix([[S.sympify(x,locals=loc) for x in row] for row in full['gram_R']])
 matrix=GR-lam*GW
 determinant=S.expand(sum((-1)**sum(p[i]>p[j] for i in range(4) for j in range(i+1,4))*S.prod(matrix[i,p[i]] for i in range(4)) for p in itertools.permutations(range(4))))
 dp=S.Poly(determinant,lam)
 d1,d2,d3,d4=[dp.nth(i) for i in (1,2,3,4)]
 assert S.expand(8*d1*d4*d4-4*d3*d2*d4+d3**3-source)==0
 print('PASS original pencil identity and augmented pullback',case,len(poly.terms()),poly.total_degree(),str(den),flush=True)
 normalized=read(f'c4-nonzero-augmented-{case}-normalized.json')
 assert normalized['unknowns']==new['variables']
 assert [r['coefficient'] for r in normalized['equations']]==new['equations']
 for field in ['qq','p1009']:
  path=base/f'neogb-c4-augmented{case}-{field}.in';hashes[path.name]=digest(path)
  lines=path.read_text().splitlines();n,m,p,terms=map(int,lines[0].split());lengths=list(map(int,lines[1].split()))
  assert (n,m,p)==(5,7,0 if field=='qq' else 1009)
  assert len(lengths)==m and sum(lengths)==terms and len(lines)==terms+2
  offset=2
  for text,count in zip(new['equations'],lengths):
   original=S.Poly(S.sympify(text,locals=loc),*variables,domain=S.QQ)
   content,primitive=original.clear_denoms()[1].primitive();assert content!=0
   expected={e:int(c)%p if p else S.Rational(c) for e,c in primitive.terms()}
   expected={e:c for e,c in expected.items() if c}
   actual={}
   for line in lines[offset:offset+count]:
    num,den,*exps=map(int,line.split());assert len(exps)==n and min(exps)>=0 and den>0 and tuple(exps) not in actual
    actual[tuple(exps)]=num*pow(den,-1,p)%p if p else S.Rational(num,den)
   assert actual==expected
   if p:assert int(content)%p!=0
   offset+=count
  print('PASS actual sparse input',case,field,terms,flush=True)
(Path(__file__).parent/'source-hashes.json').write_text(json.dumps(hashes,indent=2)+'\n')
print('PASS augmented constraints and all four actual inputs',flush=True)
