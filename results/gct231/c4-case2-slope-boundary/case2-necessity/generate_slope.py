from pathlib import Path
import json,re,sympy as s,hashlib
base=Path(__file__).resolve().parent.parent
out=Path(__file__).resolve().parent
D=json.loads((base/'c4-case2-slope-review-certificates.json').read_text())
P,B=s.symbols('P B');loc={'P':P,'B':B}
parse=lambda z:s.sympify(z,locals=loc)
lean=lambda z:str(s.expand(z)).replace('**','^')
old=(out/'Case2NecessaryElimination.lean').read_text()
names=['scaleCurve','chartDet','curveLeading','rA','rB'];defs=[]
for name in names:
 m=re.search(r'^def '+name+r'\b.*?(?=\n\ndef |\n\nset_option)',old,re.S|re.M);assert m;defs.append(m.group())
lines=['import Mathlib.Basic.Complex.Basic','import Mathlib.Tactic.LinearCombination','import Mathlib.Tactic.NormNum','','namespace PEqualNP.Outside.L_gct_231_aux.Case2SlopeBoundary','']+defs+['']
Q=P**4-2*P**3+4*P+2;R=parse(D['norm_coprime']['R']);S=parse(D['norm_coprime']['S']);A=parse(D['a_affine']['multiplier'])
for name,params,expr in [('boundaryQuartic','P',Q),('normA','P',R),('normB','P',S),('affineMultiplier','P',A),('affineRelation','P B',3*B+P**3-2*P**2)]:
 lines.extend([f'def {name} ({params} : ℂ) : ℂ :=',f'  {lean(expr)}',''])
for name,section,ks,definitions,hypotheses in [('norms_inconsistent','norm_coprime',['bezout_R','bezout_S'],['normA','normB'],['hR','hS']),('affine_multiplier_nonzero','a_affine',['bezout_multiplier','bezout_Q'],['affineMultiplier','boundaryQuartic'],['hA','hQ'])]:
 hs=[parse(D[section][k]) for k in ks];den=s.ilcm(*[v.q for h in hs for v in s.Poly(h,P).all_coeffs()]);hh=[s.expand(den*h) for h in hs]
 assert s.expand(hh[0]*(R if name=='norms_inconsistent' else A)+hh[1]*(S if name=='norms_inconsistent' else Q))==den
 if name=='norms_inconsistent':lines.extend(['set_option maxHeartbeats 800000 in',f'theorem {name} (P : ℂ) (hR : normA P = 0) (hS : normB P = 0) : False := by','  unfold normA at hR','  unfold normB at hS'])
 else:lines.extend(['set_option maxHeartbeats 800000 in',f'theorem {name} (P : ℂ) (hQ : boundaryQuartic P = 0) : affineMultiplier P ≠ 0 := by','  intro hA','  unfold affineMultiplier at hA','  unfold boundaryQuartic at hQ'])
 lines.extend([f'  have h : ({den} : ℂ) = 0 := by',f'    linear_combination ({lean(hh[0])}) * {hypotheses[0]} +',f'      ({lean(hh[1])}) * {hypotheses[1]}','  norm_num at h',''])
for lab,rd,norm,powp,const in [('rU','rA','normA',4,256),('rV','rB','normB',3,64)]:
 mF=parse(D[lab]['multiplier_F']);mg=parse(D[lab]['multiplier_g'])
 # Keep a square unexpanded to shorten the proof source.
 a=parse(D[lab]['slope']);a1=s.expand(a).coeff(B,1);a0=a.subs(B,0)
 F=parse(json.loads((base/'c4-case2-resultants.json').read_text())['scale_curve']);f2=s.expand(F).coeff(B,2);f1=s.expand(F).coeff(B,1)
 lines.extend(['set_option maxHeartbeats 1000000 in',f'theorem {rd}_norm_vanishes (P B : ℂ)',f'    (hF : scaleCurve P B = 0) (ha : {rd} P B = 0) :',f'    {const} * P^{powp} * curveLeading P^3 * boundaryQuartic P^2 * {norm} P = 0 := by',f'  unfold scaleCurve at hF',f'  unfold {rd} at ha',f'  unfold curveLeading boundaryQuartic {norm}',f'  linear_combination ({lean(a1)})^2 * hF +',f'    ({lean(mg)}) * ha',''])
lines.extend(['set_option maxHeartbeats 800000 in','theorem slopes_nonzero (P B : ℂ)','    (hF : scaleCurve P B = 0) (hn : P * B * chartDet P B ≠ 0) :','    rA P B ≠ 0 ∨ rB P B ≠ 0 := by','  have hP : P ≠ 0 := by','    intro h','    exact hn (by simp [h])','  have hB : B ≠ 0 := by','    intro h','    exact hn (by simp [h])','  have hW : chartDet P B ≠ 0 := by','    intro h','    exact hn (by simp [h])','  have hK : curveLeading P ≠ 0 := by','    intro hK','    have hpb : (3 : ℂ) * P * B = 0 := by','      unfold scaleCurve at hF','      unfold curveLeading at hK','      linear_combination -hF + (-6*B^2 + (5*P^2-P+10)*B - 8*P^2) * hK','    exact mul_ne_zero (mul_ne_zero (by norm_num) hP) hB hpb','  by_cases ha : rA P B = 0','  · right','    intro hb','    have hna := rA_norm_vanishes P B hF ha','    have hnb := rB_norm_vanishes P B hF hb','    have hQ : boundaryQuartic P = 0 := by','      by_contra hQ','      have hfa : (256 : ℂ) * P^4 * curveLeading P^3 * boundaryQuartic P^2 ≠ 0 :=','        mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 4 hP))','          (pow_ne_zero 3 hK)) (pow_ne_zero 2 hQ)','      have hfb : (64 : ℂ) * P^3 * curveLeading P^3 * boundaryQuartic P^2 ≠ 0 :=','        mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 3 hP))','          (pow_ne_zero 3 hK)) (pow_ne_zero 2 hQ)','      exact norms_inconsistent P ((mul_eq_zero.mp hna).resolve_left hfa)','        ((mul_eq_zero.mp hnb).resolve_left hfb)','    have hprod : affineMultiplier P * affineRelation P B = 0 := by','      unfold rA at ha','      unfold boundaryQuartic at hQ','      unfold affineMultiplier affineRelation',f"      linear_combination ha - ({lean(parse(D['a_affine']['quotient_by_Q']))}) * hQ",'    have hrel : affineRelation P B = 0 :=','      (mul_eq_zero.mp hprod).resolve_left (affine_multiplier_nonzero P hQ)','    apply hW','    unfold chartDet','    unfold affineRelation at hrel','    unfold boundaryQuartic at hQ','    linear_combination (3*B-P^3-4) * hrel + P^2 * hQ','  · exact Or.inl ha','','end PEqualNP.Outside.L_gct_231_aux.Case2SlopeBoundary',''])
path=out/'Case2SlopeBoundary.lean';path.write_text('\n'.join(lines))
print('Generated',len(lines),'source fragments',path.stat().st_size,'bytes',hashlib.sha256(path.read_bytes()).hexdigest(),flush=True)
print('All generator-side certificate identities already independently expanded; source is uncompiled.',flush=True)
