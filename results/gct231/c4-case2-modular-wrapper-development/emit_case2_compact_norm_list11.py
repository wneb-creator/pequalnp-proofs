from pathlib import Path
import re,hashlib
p=Path(__file__).parent
transfer=(p/'ModularResultantTransfer.lean').read_text();concrete=(p/'C4Case2ModularCoprimeList11.lean').read_text();big=(p/'C4Case2ProjectiveNorm.lean').read_text()
imports=[]
for source in[transfer,concrete]:
 for line in source.splitlines():
  if line.startswith('import ') and line not in imports:imports.append(line)
def body(source):return '\n'.join(line for line in source.splitlines() if not line.startswith('import ')).strip()
statement=big.split('theorem case2_projective_norm_obstruction ',1)[1].split(' := by',1)[0]
proof=''' := by
  letI : Fact (Nat.Prime 11) := ⟨by decide⟩
  by_contra h
  have hp : P + 2 ≠ 0 := fun hz => h (Or.inl hz)
  have hq : P^4 - 2*P^3 + 4*P + 2 ≠ 0 := fun hz => h (Or.inr hz)
  have hn : (P+2)^2 * (P^4 - 2*P^3 + 4*P + 2)^14 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hp) (pow_ne_zero _ hq)
  have hlp : (case2CofactorLeft.map (Int.castRingHom ℂ)).eval P *
      ((P+2)^2 * (P^4 - 2*P^3 + 4*P + 2)^14) = 0 := by
    norm_num only [case2CofactorLeft, polynomialOfCoeffs_map, polynomialOfCoeffs_eval, List.map, List.foldr]
    linear_combination h0
  have hrp : (case2CofactorRight.map (Int.castRingHom ℂ)).eval P *
      ((P+2)^2 * (P^4 - 2*P^3 + 4*P + 2)^14) = 0 := by
    norm_num only [case2CofactorRight, polynomialOfCoeffs_map, polynomialOfCoeffs_eval, List.map, List.foldr]
    linear_combination h1
  exact PEqualNP.Outside.L_gct_231_aux.no_common_complex_zero_of_modular_coprime
    case2CofactorLeft case2CofactorRight 11 54 82
    case2_cofactor_degree_bounds.1 case2_cofactor_degree_bounds.2 (by norm_num)
    case2_modular_degrees.1 case2_modular_degrees.2 case2_modular_coprime P
    ((mul_eq_zero.mp hlp).resolve_right hn) ((mul_eq_zero.mp hrp).resolve_right hn)
'''
s='\n'.join(imports)+'\n\n'+body(transfer)+'\n\n'+body(concrete)+'\n\nnamespace PEqualNP.Outside.L_gct_231.trace\nopen PEqualNP.Outside.L_gct_231_aux\n\nset_option maxHeartbeats 4000000 in\nset_option maxRecDepth 4096 in\ntheorem case2_projective_norm_obstruction_compact '+statement+proof+'\nend PEqualNP.Outside.L_gct_231.trace\n'
out=p/'C4Case2NormCompactList11.lean';out.write_text(s);print({'bytes':out.stat().st_size,'lines':len(s.splitlines()),'sha256':hashlib.sha256(out.read_bytes()).hexdigest()})
