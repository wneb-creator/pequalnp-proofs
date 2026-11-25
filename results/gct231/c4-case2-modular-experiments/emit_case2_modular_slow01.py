from pathlib import Path
import json,sympy as S,hashlib
p=Path(__file__).parent;d=json.loads((p/'c4-case2-modular-coprime.json').read_text());P=S.Symbol('P')
def expr(key):
 f=S.Poly(S.sympify(d[key],locals={'P':P}),P,domain=S.ZZ);cs=list(map(int,f.all_coeffs()));v=str(cs[0])
 for c in cs[1:]:v='('+v+' * Polynomial.X '+(' + ' if c>=0 else ' - ')+str(abs(c))+')'
 return v
text='import PEqualNP.Defs\nimport Mathlib.Tactic.ComputeDegree\nimport Mathlib.Algebra.Field.ZMod\n\nnamespace PEqualNP.Outside.L_gct_231.trace\n\n'
for name,key,typ in [('case2CofactorLeft','original_f','ℤ'),('case2CofactorRight','original_g','ℤ'),('case2ModLeft','mod_f','ZMod 1009'),('case2ModRight','mod_g','ZMod 1009')]:
 text+='def '+name+' : Polynomial ('+typ+') := '+expr(key)+'\n\n'
text+='''set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
theorem case2_cofactor_degree_bounds :
    case2CofactorLeft.natDegree ≤ 54 ∧ case2CofactorRight.natDegree ≤ 82 := by
  constructor
  · unfold case2CofactorLeft
    compute_degree!
  · unfold case2CofactorRight
    compute_degree!

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
theorem case2_left_map :
    case2CofactorLeft.map (Int.castRingHom (ZMod 1009)) = case2ModLeft := by
  norm_num [case2CofactorLeft, case2ModLeft, Polynomial.map_add, Polynomial.map_mul]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
theorem case2_right_map :
    case2CofactorRight.map (Int.castRingHom (ZMod 1009)) = case2ModRight := by
  norm_num [case2CofactorRight, case2ModRight, Polynomial.map_add, Polynomial.map_mul]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
theorem case2_modular_degrees :
    (case2CofactorLeft.map (Int.castRingHom (ZMod 1009))).natDegree = 54 ∧
    (case2CofactorRight.map (Int.castRingHom (ZMod 1009))).natDegree = 82 := by
  letI : Fact (Nat.Prime 1009) := ⟨by norm_num⟩
  rw [case2_left_map, case2_right_map]
  constructor
  · unfold case2ModLeft
    compute_degree!
  · unfold case2ModRight
    compute_degree!

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in
theorem case2_modular_coprime :
    IsCoprime (case2CofactorLeft.map (Int.castRingHom (ZMod 1009)))
      (case2CofactorRight.map (Int.castRingHom (ZMod 1009))) := by
  rw [case2_left_map, case2_right_map]
  refine ⟨'''+expr('mod_a')+', '+expr('mod_b')+''', ?_⟩
  have hp : (1009 : Polynomial (ZMod 1009)) = 0 := by
    have h : (1009 : ZMod 1009) = 0 := by norm_num
    simpa using congrArg (fun x : ZMod 1009 => Polynomial.C x) h
  unfold case2ModLeft case2ModRight
  linear_combination ('''+expr('integer_quotient')+''') * hp

end PEqualNP.Outside.L_gct_231.trace
'''
out=p/'C4Case2ModularCoprime.lean';out.write_text(text);print({'bytes':out.stat().st_size,'lines':len(text.splitlines()),'sha256':hashlib.sha256(out.read_bytes()).hexdigest()})
