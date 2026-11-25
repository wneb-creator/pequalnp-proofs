from pathlib import Path
import importlib.util,json,itertools,collections,math
job=Path('/tmp/oec/pequalnp-pilot-79');spec=importlib.util.spec_from_file_location('ng',job/'neogb-run-rational.py');ng=importlib.util.module_from_spec(spec);spec.loader.exec_module(ng)
names,_,polys=ng.parse_input(job/'fresh_top_allzero_0.msolve');meta=json.loads((job/'root-allzero-d8-metadata.json').read_text());im=json.loads((job/'root-allzero-d8-invariant-metadata.json').read_text());cert=json.loads((job/'root-allzero-d8-invariant-exact-certificate.json').read_text());split=json.loads((job/'root-allzero-split-model.json').read_text())
weights=[w for w in cert['coefficients'] if w];rows=[j for j,w in enumerate(cert['coefficients']) if w];zero=(0,)*7
# Coefficients are exact short integer linear combinations of the378 certificate weights.
mult=[{} for p in polys];full={}
def accum(target,m,k,c):
 d=target.setdefault(m,{});d[k]=d.get(k,0)+c
 if d[k]==0:del d[k]
 if not d:del target[m]
for k,j in enumerate(rows):
 i,m=meta['row_origins'][im['source_rows'][j]];m=tuple(m);accum(mult[i],m,k,1)
 for e,c in polys[i].items():accum(full,tuple(a+b for a,b in zip(m,e)),k,int(c))
quot={};red={m:dict(c) for m,c in full.items()}
while any(m[-1]>=2 for m in red):
 m=max(red,key=lambda e:e[-1]);co=red.pop(m);e=m[:-1]+(m[-1]-2,)
 for k,c in co.items():accum(quot,e,k,c);accum(red,e,k,24*c)
def numeric(poly):return {m:sum(weights[k]*c for k,c in v.items()) for m,v in poly.items() if sum(weights[k]*c for k,c in v.items())}
assert numeric(red)=={tuple(m):c for m,c in split['F']}
assert numeric(quot)=={tuple(m):c for m,c in split['root_quotient']}
def balanced(op,x):
 if not x:return '0'
 if len(x)==1:return x[0]
 k=len(x)//2;return '('+balanced(op,x[:k])+op+balanced(op,x[k:])+')'
def cv(v):
 terms=[]
 for k,c in sorted(v.items()):
  s='k'+str(k)
  if c==-1:s='(-'+s+')'
  elif c!=1:s='('+str(c)+'*'+s+')'
  terms.append(s)
 expr=balanced('+',terms);value=sum(weights[k]*c for k,c in v.items());literal=str(value)
 # Use the shorter exact expression; all are integer-typed by cz.
 if len(literal)<len(expr):expr=literal
 return '(cz ('+expr+'))'
def hp(poly,variables,coef):
 poly={m:c for m,c in poly.items() if c}
 if not poly:return '(0:ℂ)'
 if not variables:return coef(poly.get((),{}))
 groups={}
 for m,c in poly.items():groups.setdefault(m[0],{})[m[1:]]=c
 exps=sorted(groups,reverse=True);last=exps[0];out=hp(groups[last],variables[1:],coef)
 for ex in exps[1:]:
  d=last-ex;factor=variables[0] if d==1 else '(cp '+variables[0]+' '+str(d)+')'
  out='ca (cm ('+out+') '+factor+') ('+hp(groups[ex],variables[1:],coef)+')';last=ex
 if last:
  factor=variables[0] if last==1 else '(cp '+variables[0]+' '+str(last)+')';out='cm ('+out+') '+factor
 return out
ntext=' '.join(names);ns='PEqualNP.Outside.L_gct_231_aux.TopAllZeroSplit'
lines=['import Mathlib.Basic.Complex.Basic','import Mathlib.Tactic.LinearCombination','','namespace '+ns,'','def ca (x y : ℂ) : ℂ := x+y','def cm (x y : ℂ) : ℂ := x*y','def cp (x : ℂ) (n : ℕ) : ℂ := x^n','def cz (z : ℤ) : ℂ := z','']
for k,w in enumerate(weights):lines.append('def k'+str(k)+' : ℤ := '+str(w))
for i,p in enumerate(polys):lines += ['','def p'+str(i)+' ('+ntext+' : ℂ) : ℂ :=', '  '+hp(p,names,lambda c:'(cz ('+str(int(c))+'))')]
for i,p in enumerate(mult):
 if p:lines += ['','def m'+str(i)+' ('+ntext+' : ℂ) : ℂ :=','  '+hp(p,names,cv)]
for name,p in [('fp',red),('qp',quot)]:lines += ['','def '+name+' ('+ntext+' : ℂ) : ℂ :=','  '+hp(p,names,cv)]
allnames=['p'+str(i) for i in range(len(polys))]+['m'+str(i) for i,p in enumerate(mult) if p]+['fp','qp']+['k'+str(k) for k in range(len(weights))]+['ca','cm','cp','cz']
lines += ['','set_option maxHeartbeats 0 in','set_option maxRecDepth 100000 in','lemma subcertificate ('+ntext+' : ℂ)']
for i in range(len(polys)):lines.append('    (e'+str(i)+' : p'+str(i)+' '+ntext+' = 0)')
lines += ['    : fp '+ntext+' = 0 := by','  linear_combination (norm := skip) '+' + '.join('(m'+str(i)+' '+ntext+')*e'+str(i) for i,p in enumerate(mult) if p)+' - (qp '+ntext+')*e0','  simp only ['+', '.join(allnames)+']','  ring','']
# All six permutations of a,b,c and the induced signed permutation of l,m,n.
pairs=[(0,1),(0,2),(1,2)];perms=list(itertools.permutations(range(3)))
def args(p):
 vals=[names[p[i]] for i in range(3)]
 for i,j in pairs:
  ii,jj=p[i],p[j];sign=''
  if ii>jj:ii,jj=jj,ii;sign='-'
  x=names[3+pairs.index((ii,jj))];vals.append('('+sign+x+')' if sign else x)
 return vals+['h']
def action(m,p):
 out=[0]*7;sg=1;out[-1]=m[-1]
 for i in range(3):out[p[i]]=m[i]
 for k,(i,j) in enumerate(pairs):
  ii,jj=p[i],p[j]
  if ii>jj:ii,jj=jj,ii;sg*=(-1)**m[k+3]
  out[3+pairs.index((ii,jj))]=m[k+3]
 return tuple(out),sg
maps=[]
for p in perms:
 mp=[]
 for poly in polys:
  image={}
  for m,c in poly.items():
   e,s=action(m,p);image[e]=s*c
  mp.append(next(j for j,q in enumerate(polys) if q==image))
 maps.append(mp)
lines += ['set_option maxHeartbeats 0 in','set_option maxRecDepth 100000 in','lemma invariant_identity ('+ntext+' : ℂ) :','    '+' + '.join('(fp '+' '.join(args(p))+')' for p in perms)+' = cz ('+str(cert['denominator'])+') := by','  simp only ['+', '.join(['fp']+['k'+str(k) for k in range(len(weights))]+['ca','cm','cp','cz'])+']','  ring','', 'set_option maxHeartbeats 0 in','set_option maxRecDepth 100000 in','lemma obstruction ('+ntext+' : ℂ)']
for i in range(len(polys)):lines.append('    (e'+str(i)+' : p'+str(i)+' '+ntext+' = 0)')
lines += ['    : False := by']
for k,(p,mp) in enumerate(zip(perms,maps)):
 if k==0:
  lines.append('  have f0 := subcertificate '+ntext+' '+' '.join('e'+str(i) for i in range(len(polys))))
  continue
 lines += ['  have f'+str(k)+' : fp '+' '.join(args(p))+' = 0 := by','    apply subcertificate']
 for i,j in enumerate(mp):
  if i==0:lines.append('    · exact e0')
  else:lines += ['    · linear_combination (norm := skip) e'+str(j),'      simp only [p'+str(i)+', p'+str(j)+', ca, cm, cp, cz]','      ring']
lines += ['  have he := invariant_identity '+ntext,'  rw ['+', '.join('f'+str(k) for k in range(6))+'] at he','  norm_num [cz] at he','','end '+ns,'']
p=job/'TopAllZeroSplit.lean';p.write_text('\n'.join(lines));print(json.dumps({'bytes':p.stat().st_size,'lines':len(lines),'weights':len(weights),'F_terms':len(red),'q_terms':len(quot)}),flush=True)
