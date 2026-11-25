from pathlib import Path
import sympy as s,json,math,resource
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(90,90))
job=Path('/tmp/oec/pequalnp-pilot-79');data=json.loads((job/'geometry-exceptional-horner-identities.json').read_text());vs=s.symbols(' '.join(data['variables']))
def lean(e):
 terms=s.Poly(e,*vs).terms()
 def leaf(c):
  assert c.q==1
  return str(c) if c>=0 else '('+str(c)+')'
 def rec(ts,i):
  if not ts:return '0'
  if i==len(vs):return leaf(ts[0][1])
  groups={}
  for m,c in ts:groups.setdefault(m[i],[]).append((m,c))
  powers=sorted(groups,reverse=True);prev=powers[0];ans=rec(groups[prev],i+1)
  def power(n):return str(vs[i]) if n==1 else '(gp '+str(vs[i])+' '+str(n)+')'
  for n in powers[1:]:
   ans='(gm '+ans+' '+power(prev-n)+')';term=rec(groups[n],i+1)
   if term!='0':ans='(ga '+ans+' '+term+')'
   prev=n
  if prev:ans='(gm '+ans+' '+power(prev)+')'
  return ans
 return rec(terms,0)
lines=['import Mathlib.Algebra.Ring.Defs','import Mathlib.Tactic.LinearCombination','','namespace PEqualNP.Outside.L_gct_231.ExceptionalInteger','','abbrev ga {R : Type*} [CommRing R] (x y : R) : R := x+y','abbrev gm {R : Type*} [CommRing R] (x y : R) : R := x*y','abbrev gp {R : Type*} [CommRing R] (x : R) (n : ℕ) : R := x^n','']
proofs=[];defined={};metadata=[]
def define(name,expr):
 if name in defined:assert s.expand(defined[name]-expr)==0;return
 defined[name]=expr;lines.append('noncomputable def '+name+' {R : Type*} [CommRing R] (r b0 b1 b2 b3 b4 b5 : R) : R := '+lean(expr))
for item in data['identities']:
 tag=item['branch'];idx=item['index'];ps=list(map(s.sympify,item['polynomials']));ws=list(map(s.sympify,item['multipliers']));target=s.sympify(item['target']);den=math.lcm(*[int(c.q) for c in s.Poly(ps[0],*vs).coeffs()]);ps[0]=s.expand(den*ps[0]);D=item['multiplier']*den;ws=[ws[0]]+[s.expand(den*w) for w in ws[1:]]
 common=math.gcd(D,*[int(c) for w in ws for c in s.Poly(w,*vs).coeffs()]);D//=common;ws=[s.expand(w/common) for w in ws]
 assert s.Poly(D*target-sum(w*p for w,p in zip(ws,ps)),*vs).is_zero
 names=['raw'+str([2,3,5,6,7][idx])]+[tag+'G'+str(j) for j in range(3)]+['quartic']
 for name,p in zip(names,ps):define(name,p)
 tn=tag+str(idx);define(tn,target)
 proofs+=['','set_option maxRecDepth 4096 in','set_option maxHeartbeats 0 in','lemma '+tag+'_integer'+str(idx)+' {R : Type*} [CommRing R] (r b0 b1 b2 b3 b4 b5 : R)']
 for j,n in enumerate(names):proofs.append('    (h'+str(j)+' : '+n+' r b0 b1 b2 b3 b4 b5=0)')
 proofs+=['    : ('+str(D)+':R)*'+tn+' r b0 b1 b2 b3 b4 b5=0 := by','  dsimp ['+','.join(names)+'] at h0 h1 h2 h3 h4','  dsimp ['+tn+']','  linear_combination '+' + '.join(lean(w)+'*h'+str(j) for j,w in enumerate(ws))]
 metadata.append({'branch':tag,'index':idx,'raw_denominator':den,'integer_goal_multiplier':D,'multiplier_gcd_removed':common})
text='\n'.join(lines+proofs+['','end PEqualNP.Outside.L_gct_231.ExceptionalInteger','']);(job/'ExceptionalIntegerIdentities.lean').write_text(text);cut=text.index('set_option maxRecDepth 4096 in\nset_option maxHeartbeats 0 in\nlemma plus_integer1');(job/'ExceptionalOneIntegerIdentity.lean').write_text(text[:cut]+'\nend PEqualNP.Outside.L_gct_231.ExceptionalInteger\n');(job/'geometry-exceptional-integer-metadata.json').write_text(json.dumps(metadata,indent=2)+'\n');print('Generated exact abstract-CommRing integer identities',len(text.encode()),flush=True)
