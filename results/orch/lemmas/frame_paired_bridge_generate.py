from pathlib import Path
import sympy as s,json,itertools
job=Path('/tmp/oec/pequalnp-pilot-79');repo=Path('/workspace/pequalnp-proofs');root=repo/'results/orch/lemmas';data=json.loads((job/'frame-paired-exact-certificates.json').read_text());integer=json.loads((job/'frame-paired-integer-certificates.json').read_text());model=json.loads((job/'four-frame-short-net.json').read_text());vv=s.symbols(' '.join(model['variables']));u01,u02,u03,u12,u13,u23,a,b,g,h,k=vv;r=s.Symbol('r');scope=dict(zip(model['variables'],vv));scope['r']=r;params=[u02,u03,u12,u13,u23,a,b,g,h,k]
quads=[s.sympify(e,locals=scope).subs(u01,1) for e in model['equations'] if s.Poly(s.sympify(e,locals=scope),*vv).total_degree()==2]
def lean(expr):return str(s.expand(expr)).replace('**',' ^ ')
sources=[(root/'FramePairedCases.lean').read_text(),(root/'FramePairedRoots.lean').read_text()];imports=[];bodies=[]
for source in sources:
 lines=source.splitlines()
 for line in lines:
  if line.startswith('import ') and line not in imports:imports.append(line)
 bodies.append('\n'.join(line for line in lines if not line.startswith('import ')))
text=imports+['']+bodies+['','namespace PEqualNP.Outside.L_gct_231_aux.FramePairedTriangle','']
dd=-b+h+k-2+2*u03+2*u13;cc=-g-h-2*u12-2*u13-2*u23;ee=-a-k-2*u02-2*u03+2*u23;ss=u02+u03;tt=1-u03;vvv=u12+u13;ww=1-u13;pp=u12+u23;qq=u02-u23
for caseindex,entry in enumerate(data['cases']):
 case=entry['case'];sgn=case['signs'];la=lambda sig:-4+2*sig*r
 equalities=[('ha',a,la(1)*ss),('hg',g,la(-1)*vvv),('hb',b,la(sgn[1])*tt),('hc',cc,la(-sgn[1])*pp),('hd',dd,la(sgn[2])*ww),('he',ee,la(-sgn[2])*qq)]
 substitutions={scope[name]:s.sympify(expr,locals=scope) for name,expr in case['substitutions'].items()};elim=scope[case['eliminated']];E=s.sympify(case['elimination'],locals=scope);L=s.sympify(case['linear'],locals=scope);alpha=s.expand(L).coeff(elim);inv=s.invert(alpha,r*r-2,r);R,rem=s.div(s.expand(elim-E-inv*L),r*r-2,r);assert rem==0
 text.extend(['set_option maxRecDepth 2048 in','set_option maxHeartbeats 0 in','lemma relative_case'+str(caseindex)+' (r '+' '.join(str(p) for p in params)+' : ℂ)','    (hr : r ^ 2 = 2)'])
 for name,lhs,rhs in equalities:text.append('    ('+name+' : '+lean(lhs)+' = '+lean(rhs)+')')
 for i,q in enumerate(quads):text.append('    (q'+str(i)+' : '+lean(q)+' = 0)')
 text.extend(['    : False := by','  have hh : h = '+lean(substitutions[h])+' := by','    linear_combination -hc - hg','  have hk : k = '+lean(substitutions[k])+' := by','    linear_combination -he - ha','  have hL : '+lean(L)+' = 0 := by','    linear_combination -hd - hb + hh + hk','  have helim : '+str(elim)+' = '+lean(E)+' := by','    linear_combination ('+lean(inv)+') * hL + ('+lean(R)+') * hr','  simp only [ha, hb, hg, hh, hk, helim] at q0 q1 q2 q3 q4 q5'])
 for i,q in enumerate(quads):
  reduced=s.sympify(integer[caseindex]['quadratics'][i],locals=scope);caseq=s.sympify(case['quadratics'][i],locals=scope);scale=s.cancel(reduced/caseq);assert scale.is_Integer
  substituted=s.expand(q.subs(substitutions,simultaneous=True).subs(elim,E));Q,rem=s.div(s.expand(reduced-scale*substituted),r*r-2,r);assert rem==0
  text.extend(['  have hq'+str(i)+' : '+lean(reduced)+' = 0 := by','    linear_combination '+str(scale)+' * q'+str(i)+' + ('+lean(Q)+') * hr'])
 text.extend(['  exact FramePairedCases.case'+str(caseindex)+' r '+' '.join(case['variables'])+' hr hq0 hq1 hq2 hq3 hq4 hq5',''])
text.extend(['set_option maxRecDepth 2048 in','set_option maxHeartbeats 0 in','theorem norms_and_cross_impossible (r '+' '.join(str(p) for p in params)+' : ℂ)','    (hr : r ^ 2 = 2)'])
norms=[('na',a,ss),('ng',g,vvv),('nb',b,tt),('nc',cc,pp),('nd',dd,ww),('ne',ee,qq)]
for name,A,S in norms:text.append('    ('+name+' : ('+lean(A)+') ^ 2 + 8 * ('+lean(A)+') * ('+lean(S)+') + 8 * ('+lean(S)+') ^ 2 = 0)')
text.extend(['    (cag : a * g = 8 * ('+lean(ss)+') * ('+lean(vvv)+'))','    (cbc : b * ('+lean(cc)+') = 8 * ('+lean(tt)+') * ('+lean(pp)+'))','    (cde : ('+lean(dd)+') * ('+lean(ee)+') = 8 * ('+lean(ww)+') * ('+lean(qq)+'))'])
for i,q in enumerate(quads):text.append('    (q'+str(i)+' : '+lean(q)+' = 0)')
text.extend(['    : False := by','  have hrneg : (-r) ^ 2 = 2 := by linear_combination hr','  rcases FramePairedRoots.opposite_pairs a g ('+lean(ss)+') ('+lean(vvv)+') r hr na ng cag with ⟨ha, hg⟩ | ⟨ha, hg⟩ <;>','    rcases FramePairedRoots.opposite_pairs b ('+lean(cc)+') ('+lean(tt)+') ('+lean(pp)+') r hr nb nc cbc with ⟨hb, hc⟩ | ⟨hb, hc⟩ <;>','    rcases FramePairedRoots.opposite_pairs ('+lean(dd)+') ('+lean(ee)+') ('+lean(ww)+') ('+lean(qq)+') r hr nd ne cde with ⟨hd, he⟩ | ⟨hd, he⟩'])
for sign1,sign2,sign3 in itertools.product([1,-1],repeat=3):
 relative=[1,sign1*sign2,sign1*sign3];which=next(i for i,c in enumerate(data['cases']) if c['case']['signs']==relative);rootarg='r' if sign1==1 else '(-r)';hrarg='hr' if sign1==1 else 'hrneg'
 text.append('  · apply relative_case'+str(which)+' '+rootarg+' '+' '.join(str(p) for p in params)+' '+hrarg)
 for hname in ['ha','hg','hb','hc','hd','he']:
  text.extend(['    · convert '+hname+' using 1 <;> ring'])
 for i in range(6):text.append('    · exact q'+str(i))
text.extend(['','end PEqualNP.Outside.L_gct_231_aux.FramePairedTriangle','']);out=root/'FramePairedTriangle.lean';out.write_text('\n'.join(text));print(json.dumps({'source':str(out),'bytes':out.stat().st_size,'lines':len(out.read_text().splitlines())}))
