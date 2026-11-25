from pathlib import Path
import json,sympy as s,ast,itertools
out=Path('/tmp/oec/pequalnp-pilot-79');repo=Path('/workspace/pequalnp-proofs/results/orch/lemmas');raw=json.loads((out/'geometry-exceptional-raw.json').read_text());r,t,x=s.symbols('r t x');b=s.symbols('b0:6');Q=s.sympify(raw['root_polynomial']);vs=(*b,r)
def bal(v,n):
 if not v:return '0'
 if len(v)==1:return v[0]
 k=len(v)//2;return '('+n+' '+bal(v[:k],n)+' '+bal(v[k:],n)+')'
def lean(e):
 terms=[]
 for m,c in s.Poly(e,*vs).terms():
  f='('+str(c.p)+'/'+str(c.q)+':ℂ)' if c.q!=1 else (str(c) if c>=0 else '('+str(c)+')');fac=[f]
  for v,a in zip(vs,m):
   if a:fac.append(str(v) if a==1 else '(ep '+str(v)+' '+str(a)+')')
  terms.append(bal(fac,'em'))
 return bal(terms,'ea')
red=(repo/'ExceptionalRawReduction.lean').read_text();defs=[l for l in red.splitlines() if l.startswith('abbrev ') or l.startswith('noncomputable def raw')]
per=(repo/'OverlapBlocks.lean').read_text();per=per[per.index('lemma sum_perm_succ'):per.index('lemma block_root')]
lines=['import Mathlib.Basic.Complex.Basic','import Mathlib.Tactic.LinearCombination','import Mathlib.Tactic.NormNum','import Mathlib.LinearAlgebra.Matrix.Permanent','import Mathlib.LinearAlgebra.Matrix.Notation','import Mathlib.GroupTheory.Perm.Fin','','namespace PEqualNP.Outside.L_gct_231.ExceptionalReduction','']+defs+['',per]
T=list(map(s.sympify,raw['T']));lines+=['noncomputable def fixedT (r : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=','  !['+','.join('!['+','.join(lean(T[4*i+j]) for j in range(4))+']' for i in range(4))+']',
'noncomputable def partner (b0 b1 b2 b3 b4 b5 : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=',
'  let a : ℂ := (b0+b3+b5+2*(b1+b2+b4)+2)/16',
'  ![![-a,-a,1-a,-a],![-a,b0-a,b1-a,b2-a],![1-a,b1-a,b3-a,b4-a],![-a,b2-a,b4-a,b5-a]]','']
monoms=[ast.literal_eval(m) for m in raw['coefficients']] # internally generated integer tuple keys only
terms=['raw'+str(i)+' r b0 b1 b2 b3 b4 b5*t^'+str(m[0])+'*x^'+str(m[1]) for i,m in enumerate(monoms)];poly='('+'+'.join(terms)+')'
lines+=['set_option maxRecDepth 4096 in','set_option maxHeartbeats 0 in','lemma fixed_permanent_expansion (r b0 b1 b2 b3 b4 b5 t x : ℂ)',
'  (hQ : '+lean(Q)+'=0) :',
'  Matrix.permanent (Matrix.of fun (i j : Fin 4) => (1:ℂ)+t*fixedT r i j+x*partner b0 b1 b2 b3 b4 b5 i j)=',
'    24+'+poly+' := by']
TT=s.Matrix(4,4,T);NN=s.Matrix(4,4,list(map(s.sympify,raw['N'])));BB=NN-sum(NN)*s.ones(4)/16;MM=s.ones(4)+t*TT+x*BB
PP=s.expand(sum(s.prod(MM[i,p[i]] for i in range(4)) for p in itertools.permutations(range(4)))-24)
RR=sum(s.sympify(f)*t**m[0]*x**m[1] for m,f in zip(monoms,raw['coefficients'].values()))
correction,remainder=s.div(PP-RR,Q,r);assert s.expand(remainder)==0
oldvs=vs;vs=(*b,r,t,x);corrlean=lean(correction);vs=oldvs
print('Expansion correction terms',len(s.Poly(correction,*b,r,t,x).terms()),flush=True)
(out/'geometry-exceptional-permanent-correction.json').write_text(json.dumps({'variables':[str(v) for v in (*b,r,t,x)],'quotient':str(correction)},separators=(',',':'))+'\n')
lines+=['  simp [perm4,Matrix.of_apply,fixedT,partner,'+','.join('raw'+str(i) for i in range(8))+']','  linear_combination '+corrlean+'*hQ','',
'set_option maxRecDepth 4096 in','set_option maxHeartbeats 0 in','lemma fixed_coefficients (r b0 b1 b2 b3 b4 b5 : ℂ)',
'  (hQ : '+lean(Q)+'=0)',
'  (hp : ∀ t x : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 4) => (1:ℂ)+t*fixedT r i j+x*partner b0 b1 b2 b3 b4 b5 i j)=24) :',
'  '+' ∧ '.join('raw'+str(i)+' r b0 b1 b2 b3 b4 b5=0' for i in range(8))+' := by',
'  have he (t x : ℂ) : '+poly+'=0 := by',
'    have h := hp t x','    rw [fixed_permanent_expansion r b0 b1 b2 b3 b4 b5 t x hQ] at h','    linear_combination h']
ts=[-1,0,1];xs=[-2,-1,0,1,2];Vt=s.Matrix([[s.Integer(ti)**j for j in range(3)] for ti in ts]);Vx=s.Matrix([[s.Integer(xi)**j for j in range(5)] for xi in xs]);It=Vt.inv();Ix=Vx.inv();names={}
for ti in ts:
 for xi in xs:
  if xi==0:continue
  name='h'+str(ti+1)+str(xi+2);names[ti,xi]=name;lines.append('  have '+name+' := he ('+str(ti)+') ('+str(xi)+')')
lines.append('  refine ⟨'+','.join('?_' for _ in range(8))+'⟩')
for i,j in monoms:
 combos=[]
 for ti in ts:
  for xi in xs:
   w=It[i,ts.index(ti)]*Ix[j,xs.index(xi)]
   if w!=0 and xi!=0:combos.append(lean(w)+'*'+names[ti,xi])
 lines.append('  · linear_combination '+' + '.join(combos))
lines+=['','end PEqualNP.Outside.L_gct_231.ExceptionalReduction','']
p=repo/'ExceptionalCoefficientBridgeFlat.lean';p.write_text('\n'.join(lines));print('Generated',p,'bytes',p.stat().st_size)
