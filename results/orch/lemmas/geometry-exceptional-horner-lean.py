from pathlib import Path
import sympy as s,json,math,resource
resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3));resource.setrlimit(resource.RLIMIT_CPU,(120,120))
out=Path('/tmp/oec/pequalnp-pilot-79');repo=Path('/workspace/pequalnp-proofs/results/orch/lemmas');raw=json.loads((out/'geometry-exceptional-raw.json').read_text());branches=json.loads((out/'geometry-exceptional-branches.json').read_text());oldproof=json.loads((out/'geometry-exceptional-reduction-proof-data.json').read_text());b=s.symbols('b0:6');r=s.symbols('r');vs=(*b,r);Q=s.sympify(raw['root_polynomial']);fs=[s.sympify(f) for f in raw['coefficients'].values()]
def bal(items,name):
 if not items:return '0'
 if len(items)==1:return items[0]
 k=len(items)//2;return '('+name+' '+bal(items[:k],name)+' '+bal(items[k:],name)+')'
def lean(e):
 terms=s.Poly(e,*vs).terms()
 def leaf(c):return '('+str(c.p)+'/'+str(c.q)+':ℂ)' if c.q!=1 else (str(c) if c>=0 else '('+str(c)+')')
 def rec(ts,i):
  if not ts:return '0'
  if i==len(vs):
   assert len(ts)==1
   return leaf(ts[0][1])
  groups={}
  for m,c in ts:groups.setdefault(m[i],[]).append((m,c))
  powers=sorted(groups,reverse=True);prev=powers[0];ans=rec(groups[prev],i+1)
  def power(n):return str(vs[i]) if n==1 else '(ep '+str(vs[i])+' '+str(n)+')'
  for n in powers[1:]:
   ans='(em '+ans+' '+power(prev-n)+')'
   term=rec(groups[n],i+1)
   if term!='0':ans='(ea '+ans+' '+term+')'
   prev=n
  if prev:ans='(em '+ans+' '+power(prev)+')'
  return ans
 return rec(terms,0)
def clear_mult(ws):
 D=1
 for w in ws:
  for c in s.Poly(w,*vs).coeffs():D=math.lcm(D,int(c.q))
 return D,[s.expand(D*w) for w in ws]
base=(repo/'ExceptionalRawReductionFlat.lean').read_text();lines=base[:base.index('set_option maxRecDepth')].splitlines()
lines=[line for line in lines if not line.startswith('noncomputable def ')]
for i,f in enumerate(fs):lines.append('noncomputable def raw'+str(i)+' (r b0 b1 b2 b3 b4 b5 : ℂ) : ℂ := '+lean(f))
for branch in branches:
 tag='plus' if branch['sign']==1 else 'minus'
 for j,f in enumerate(branch['equations']):lines.append('noncomputable def '+tag+str(j)+' (b3 b4 b5 r : ℂ) : ℂ := '+lean(s.sympify(f)))
helpers=[];branchbody=[];identities=[]
for bi,branch in enumerate(branches):
 tag='plus' if branch['sign']==1 else 'minus';subs={s.Symbol(k):s.sympify(v) for k,v in branch['substitutions'].items()};gs=[];scales=[];pivotproof=[]
 for j in [0,1,2]:
  f=b[j]-subs[b[j]];g=s.Poly(f,*vs).clear_denoms()[1].primitive()[1].as_expr();gs.append(g);scales.append(s.cancel(g/f));lines.append('noncomputable def '+tag+'G'+str(j)+' (r b0 b1 b2 b3 b4 b5 : ℂ) : ℂ := '+lean(g))
 for j,pr in enumerate(oldproof[bi]['pivot_certificates']):
  ws=[s.sympify(v)*scales[j] for v in pr['multipliers']]+[s.sympify(pr['root_multiplier'])*scales[j]];D,ws=clear_mult(ws);Le=[fs[4],fs[1],r*b[2]+b[4]-(1-branch['sign'])*(r+1)*b[5],Q];assert s.Poly(D*gs[j]-sum(w*f for w,f in zip(ws,Le)),*vs).is_zero;pivotproof.append((D,ws))
 for ji,fi in enumerate([2,3,5,6,7]):
  cur=fs[fi];ls=[]
  for j in [0,1,2]:
   nex=s.expand(cur.subs(b[j],subs[b[j]]));L,rem=s.div(cur-nex,b[j]-subs[b[j]],*vs);assert rem==0;ls.append(L);cur=nex
  target=s.sympify(branch['equations'][ji]);R=s.rem(cur,Q,r);scale=s.cancel(target/R);assert scale.is_Rational;H,rem=s.div(target-scale*cur,Q,*vs);assert rem==0
  ws=[scale]+[-scale*ls[j]/scales[j] for j in range(3)]+[H];D,ws=clear_mult(ws);hs=[fs[fi],*gs,Q];assert s.Poly(D*target-sum(w*f for w,f in zip(ws,hs)),*vs).is_zero
  print(tag,ji,'integer identity terms',[len(s.Poly(w,*vs).terms()) for w in ws],'multiplier',D,flush=True)
  name=tag+'_direct'+str(ji);helpers+=['set_option maxRecDepth 4096 in','set_option maxHeartbeats 0 in','lemma '+name+' (r b0 b1 b2 b3 b4 b5 : ℂ) (hQ : '+lean(Q)+'=0)',
 '    (he : raw'+str(fi)+' r b0 b1 b2 b3 b4 b5=0)']
  for j in range(3):helpers.append('    (hG'+str(j)+' : '+tag+'G'+str(j)+' r b0 b1 b2 b3 b4 b5=0)')
  helpers+=['    : '+tag+str(ji)+' b3 b4 b5 r=0 := by','  dsimp [raw'+str(fi)+','+','.join(tag+'G'+str(j) for j in range(3))+'] at he hG0 hG1 hG2',
 '  have hh : ('+str(D)+':ℂ)*'+tag+str(ji)+' b3 b4 b5 r=0 := by','    dsimp ['+tag+str(ji)+']','    linear_combination '+ ' + '.join(lean(w)+'*'+h for w,h in zip(ws,['he','hG0','hG1','hG2','hQ'])),
 '  exact (mul_eq_zero.mp hh).resolve_left (by norm_num)','']
  identities.append({'branch':tag,'index':ji,'multiplier':D,'polynomials':list(map(str,hs)),'multipliers':list(map(str,ws)),'target':str(target)})
 branchbody+=['  · have he4 := h4','    have he1 := h1','    dsimp [raw4,raw1] at he4 he1']
 for j,(D,ws) in enumerate(pivotproof):
  branchbody+=['    have hG'+str(j)+' : '+tag+'G'+str(j)+' r b0 b1 b2 b3 b4 b5=0 := by',
 '      have hh : ('+str(D)+':ℂ)*'+tag+'G'+str(j)+' r b0 b1 b2 b3 b4 b5=0 := by','        dsimp ['+tag+'G'+str(j)+']','        linear_combination '+ ' + '.join(lean(w)+'*'+h for w,h in zip(ws,['he4','he1','hbranch','hQ'])),
 '      exact (mul_eq_zero.mp hh).resolve_left (by norm_num)']
 for ji,fi in enumerate([2,3,5,6,7]):branchbody.append('    have hg'+str(ji)+' := '+tag+'_direct'+str(ji)+' r b0 b1 b2 b3 b4 b5 hQ h'+str(fi)+' hG0 hG1 hG2')
 branchbody.append('    exact h'+tag+' b3 b4 b5 r hg0 hg1 hg2 hg3 hg4 hQ')
lines+=['']+helpers+['set_option maxRecDepth 4096 in','set_option maxHeartbeats 0 in','lemma raw_equations_impossible',
 '(hplus : ∀ b3 b4 b5 r : ℂ, '+' → '.join('plus'+str(i)+' b3 b4 b5 r=0' for i in range(5))+' → '+lean(Q)+'=0 → False)',
 '(hminus : ∀ b3 b4 b5 r : ℂ, '+' → '.join('minus'+str(i)+' b3 b4 b5 r=0' for i in range(5))+' → '+lean(Q)+'=0 → False)',
 '(r b0 b1 b2 b3 b4 b5 : ℂ) (hQ : '+lean(Q)+'=0)']
for i in range(8):lines.append(' (h'+str(i)+' : raw'+str(i)+' r b0 b1 b2 b3 b4 b5=0)')
lines+=[' : False := by','  have hfac : (r*b2+b4)*(r*b2+b4-2*(r+1)*b5)=0 := by','    have he0 := h0','    have he1 := h1','    dsimp [raw0,raw1] at he0 he1','    linear_combination he0-(b5-(b0+b3+b5+2*(b1+b2+b4)+2)/16)*he1','  rcases mul_eq_zero.mp hfac with hbranch | hbranch']+branchbody+['','end PEqualNP.Outside.L_gct_231.ExceptionalReduction','']
p=repo/'ExceptionalRawReductionHorner.lean';p.write_text('\n'.join(lines));(out/'geometry-exceptional-horner-identities.json').write_text(json.dumps({'variables':list(map(str,vs)),'identities':identities},separators=(',',':'))+'\n');print('Generated',p,p.stat().st_size,flush=True)
