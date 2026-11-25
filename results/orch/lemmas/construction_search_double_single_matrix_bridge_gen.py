from pathlib import Path
import sympy as s,itertools,json,importlib.util
job=Path('/tmp/oec/pequalnp-pilot-79');repo=Path('/workspace/pequalnp-proofs')
x,y,z,rr=s.symbols('x y z rr');a,b,c,d,e,f,g,k,i,j=s.symbols('a b c d e f g k i j');pars=(a,b,c,d,e,f,g,k,i,j,rr);pnames=list(map(str,pars));args=' '.join(pnames)
l=-b-k-2*d-2*e-2*i;o=-a-g-2*c-2*f-2*j
M=s.Matrix([[a*y+b*z,c*y+d*z,e*z,f*y],[c*y+d*z,g*y+k*z,i*z,j*y],[e*z,i*z,(rr-1)*x+l*z,x],[f*y,j*y,x,(-rr-1)*x+o*y]])
raw=s.expand(sum(s.prod(1+M[r,p[r]] for r in range(4)) for p in itertools.permutations(range(4)))-24)
def red(v):return s.Poly(v,rr).rem(s.Poly(rr**2-2,rr)).as_expr().expand()
terms=[(m,red(v)) for m,v in s.Poly(raw,x,y,z).terms() if red(v)!=0]
assert len(terms)==19 and max(m[0] for m,v in terms)==1
reduced=sum(v*x**m[0]*y**m[1]*z**m[2] for m,v in terms)
Q=-x*x*((1+a*y+b*z)*(1+g*y+k*z)+(1+c*y+d*z)**2)
assert s.expand(raw-reduced-(rr*rr-2)*Q)==0
points=list(itertools.product([0,1],[0,1,-1,2,-2],[0,1,-1,2,-2]))
V=s.Matrix([[s.prod(t**power for t,power in zip(pt,m)) for m,v in terms] for pt in points]);pivots=V.T.rref()[1];assert len(pivots)==19;points=[points[n] for n in pivots];VI=V[list(pivots),:].inv()
def combine(op,items):
 if not items:return 'cz 0'
 if len(items)==1:return items[0]
 mid=len(items)//2;return op+' ('+combine(op,items[:mid])+') ('+combine(op,items[mid:])+')'
def leanpoly(expr,variables=pars):
 out=[]
 for m,v in s.Poly(expr,*variables,domain=s.ZZ).terms():
  if not v:continue
  factors=['cz ('+str(v)+')']+[('cp '+str(t)+' '+str(n) if n>1 else str(t)) for t,n in zip(variables,m) if n]
  out.append(combine('cm',factors))
 return combine('ca',out)
def leanrat(q):return '('+str(q.p)+' / '+str(q.q)+' : ℂ)' if q.q!=1 else '('+str(q.p)+' : ℂ)'
def literal(n):return str(n) if n>=0 else '('+str(n)+')'
ns='PEqualNP.Outside.L_gct_231_aux.DoubleSingleMatrixBridge'
imports=['import Mathlib.Basic.Complex.Basic','import Mathlib.Tactic.LinearCombination','import Mathlib.Tactic.FinCases','import Mathlib.LinearAlgebra.Matrix.Permanent','import Mathlib.LinearAlgebra.Matrix.Notation','import Mathlib.GroupTheory.Perm.Fin']
lines=imports+['','namespace '+ns,'','def ca (x y : ℂ) : ℂ := x + y','def cm (x y : ℂ) : ℂ := x * y','def cp (x : ℂ) (n : ℕ) : ℂ := x ^ n','def cz (z : ℤ) : ℂ := z','']
old=(repo/'results/orch/lemmas/TwoBlockMatrixCompact.lean').read_text();lines.append(old[old.index('lemma sum_perm_succ'):old.index('def blockA')].strip());lines+=['','def model ('+args+' x y z : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=','  !['+', '.join('!['+', '.join(leanpoly(M[r,c],pars+(x,y,z)) for c in range(4))+']' for r in range(4))+']','']
lines+=['def coefficients ('+args+' : ℂ) : Fin 19 → ℂ :=','  !['+',\n    '.join(leanpoly(v) for m,v in terms)+']','']
polynomial=combine('ca',[combine('cm',['p '+str(n)]+[('cp '+str(t)+' '+str(power) if power>1 else str(t)) for t,power in zip((x,y,z),m) if power]) for n,(m,v) in enumerate(terms)])
lines+=['def polynomial (p : Fin 19 → ℂ) (x y z : ℂ) : ℂ :=','  '+polynomial,'','set_option maxHeartbeats 10000000 in','set_option maxRecDepth 100000 in','lemma extract_coefficients (p : Fin 19 → ℂ)','    (hp : ∀ x y z, polynomial p x y z = 0) : ∀ n, p n = 0 := by']
for index,pt in enumerate(points):lines+=['  have h'+str(index)+' := hp '+' '.join(literal(n) for n in pt)]
lines+=['  simp only [polynomial, ca, cm, cp, cz] at '+ ' '.join('h'+str(n) for n in range(19)), '  intro n','  fin_cases n']
for nrow,row in enumerate(VI.tolist()):lines+=['  · change p '+str(nrow)+' = 0','    linear_combination '+' + '.join(leanrat(weight)+' * h'+str(n) for n,weight in enumerate(row) if weight)]
lines+=['','set_option maxHeartbeats 100000000 in','set_option maxRecDepth 100000 in','lemma permanent_expansion ('+args+' x y z : ℂ) (hr : rr ^ 2 = 2) :','    Matrix.permanent (Matrix.of fun r s => (1 : ℂ) + model '+args+' x y z r s) - 24 =','      polynomial (coefficients '+args+') x y z := by','  simp [perm4, Matrix.of_apply, model, polynomial, coefficients, ca, cm, cp, cz,','    Matrix.cons_val_zero, Matrix.cons_val_succ]','  linear_combination ('+leanpoly(Q,pars+(x,y,z))+') * hr','', 'lemma coefficients_zero ('+args+' : ℂ) (hr : rr ^ 2 = 2)','    (hp : ∀ x y z, Matrix.permanent (Matrix.of fun r s => (1 : ℂ) +','      model '+args+' x y z r s) = 24) : ∀ n, coefficients '+args+' n = 0 := by','  apply extract_coefficients','  intro x y z','  rw [← permanent_expansion '+args+' x y z hr, hp x y z]','  ring','']
# The expansion correction uses typed arithmetic, which must be unfolded before normalization.
pos=lines.index('  linear_combination ('+leanpoly(Q,pars+(x,y,z))+') * hr');lines[pos]='  linear_combination (norm := skip) ('+leanpoly(Q,pars+(x,y,z))+') * hr';lines[pos+1:pos+1]=['  simp only [ca, cm, cp, cz]','  ring']
base=lines+['end '+ns,''];(job/'DoubleSingleMatrixBridge.lean').write_text('\n'.join(base))
spec=importlib.util.spec_from_file_location('ng',job/'neogb-run-rational.py');ng=importlib.util.module_from_spec(spec);spec.loader.exec_module(ng)
wrappers=[];mapping={}
for branch,sub in [('same',{e:1,f:1}),('cross',{i:1,f:1})]:
 names,prime,eqs=ng.parse_input(job/('root-double-single-kernels-'+branch+'-0.msolve'));assert prime==0;vars_=tuple(s.Symbol(v) for v in names)
 modelargs=' '.join('1' if p in sub else str(p) for p in pars);maps=[]
 for index,poly in enumerate(eqs[:-1]):
  q=sum(s.Integer(v)*s.prod(t**power for t,power in zip(vars_,m)) for m,v in poly.items());found=[]
  for n,(m,coeff) in enumerate(terms):
   ratio=s.cancel(coeff.subs(sub)/q)
   if ratio.is_Integer and ratio!=0:found.append((n,int(ratio)))
  assert len(found)==1,(branch,index,found);maps.append(found[0])
 cname='PEqualNP.Outside.L_gct_231_aux.DoubleSingle'+branch.capitalize()+'Certificate';wrappers+=['set_option maxHeartbeats 100000000 in','set_option maxRecDepth 100000 in','lemma '+branch+'_matrix_obstruction ('+' '.join(names)+' : ℂ) (hr : rr ^ 2 = 2)','    (hp : ∀ x y z, Matrix.permanent (Matrix.of fun r s => (1 : ℂ) +','      model '+modelargs+' x y z r s) = 24) : False := by','  have hz := coefficients_zero '+modelargs+' hr hp','  apply '+cname+'.normalized_'+branch+'_obstruction '+' '.join(names)]
 for n,content in maps:
  wrappers+=['  · have h := hz '+str(n),'    simp [coefficients, ca, cm, cp, cz, Matrix.cons_val_zero,','      Matrix.cons_val_succ] at h','    simp only ['+cname+'.ca, '+cname+'.cm, '+cname+'.cp, '+cname+'.cz]','    linear_combination '+leanrat(s.Rational(1,content))+' * h']
 wrappers+=['  · simp only ['+cname+'.ca, '+cname+'.cm, '+cname+'.cp, '+cname+'.cz]','    linear_combination hr',''];mapping[branch]=maps
(job/'DoubleSingleMatrixWrappers.lean.txt').write_text('\n'.join(wrappers))
full=imports+['']
for name in ['DoubleSingleSameCertificate.lean','DoubleSingleCrossCertificate.lean']:
 text=(job/name).read_text();full += [line for line in text.splitlines() if not line.startswith('import ')]+['']
full+=lines[len(imports):]+wrappers+[(job/'double_single_matrix_scaling.lean.txt').read_text(),'end '+ns,''];(job/'DoubleSingleMatrixFull.lean').write_text('\n'.join(full))
(job/'double-single-matrix-bridge-model.json').write_text(json.dumps({'monomials':[m for m,v in terms],'interpolation_points':points,'interpolation_weights':[[str(q) for q in row] for row in VI.tolist()],'equation_mapping':mapping,'scope':'Actual normalized repeated-zero-row matrices; not a global kernel-cover proof'},indent=2))
print(json.dumps({'source_bytes':(job/'DoubleSingleMatrixBridge.lean').stat().st_size,'combined_bytes':(job/'DoubleSingleMatrixFull.lean').stat().st_size,'coefficient_terms':sum(len(s.Poly(v,*pars).terms()) for m,v in terms),'points':len(points)}))
