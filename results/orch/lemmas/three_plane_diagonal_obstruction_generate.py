from pathlib import Path
import itertools
import json
import sys

job = Path('/tmp/oec/pequalnp-pilot-79')
repo = Path('/workspace/pequalnp-proofs')
data = json.loads((job / 'three-plane-diagonal-anchor-integer-moment.json').read_text())
matrix = data['integer_matrix']
pairs = list(itertools.combinations_with_replacement(range(5), 2))
triples = list(itertools.combinations_with_replacement(range(5), 3))
indices = {x: i for i, x in enumerate(triples)}

def term(coefficient, variables):
    if coefficient == 0:
        return None
    return '(' + str(coefficient) + ') * ' + ' * '.join(variables)

quadratics = []
for k in range(7):
    terms = []
    for i, j in pairs:
        coefficient = matrix[5 * k][indices[(0, i, j)]]
        value = term(coefficient, ['v ' + str(i), 'v ' + str(j)])
        if value is not None:
            terms.append(value)
    quadratics.append(' + '.join(terms))

source = (repo / 'results/orch/lemmas/DiagonalAnchorMoment.lean').read_text()
assert source.endswith('end PEqualNP.Outside.L_gct_231_aux.DiagonalAnchorMoment\n')
source = source.removesuffix('end PEqualNP.Outside.L_gct_231_aux.DiagonalAnchorMoment\n')
source = source.replace('import Mathlib.Data.ZMod.Basic\n',
    'import Mathlib.Data.ZMod.Basic\nimport Mathlib.Basic.Complex.Basic\n'
    'import Mathlib.LinearAlgebra.Matrix.NonsingularInverse\n'
    'import Mathlib.Tactic.FinCases\nimport Mathlib.Tactic.Ring\n')
source += '\n'
source += 'def complexMatrix : Matrix (Fin 35) (Fin 35) ℂ :=\n'
source += '  (Int.castRingHom ℂ).mapMatrix integerMatrix\n\n'
source += '''lemma complex_det_ne_zero : Matrix.det complexMatrix ≠ 0 := by
  intro h
  have hz : ((Matrix.det integerMatrix : ℤ) : ℂ) = 0 := by
    calc
      ((Matrix.det integerMatrix : ℤ) : ℂ) =
          Matrix.det complexMatrix :=
        (Int.castRingHom ℂ).map_det integerMatrix
      _ = 0 := h
  exact integer_det_ne_zero (Int.cast_eq_zero.mp hz)

'''
source += 'def quadratics (v : Fin 5 → ℂ) : Fin 7 → ℂ :=\n  !['
source += ',\n    '.join(quadratics) + ']\n\n'
source += 'def cubics (v : Fin 5 → ℂ) : Fin 35 → ℂ :=\n  !['
source += ', '.join(' * '.join('v ' + str(i) for i in t) for t in triples) + ']\n\n'
source += 'def products (v : Fin 5 → ℂ) : Fin 35 → ℂ :=\n  !['
source += ', '.join('v ' + str(i) + ' * quadratics v ' + str(k) for k in range(7) for i in range(5))
source += ']\n\n'
source += '''set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma row_products (v : Fin 5 → ℂ) :
    complexMatrix *ᵥ cubics v = products v := by
  ext i
  fin_cases i <;>
    simp [complexMatrix, integerMatrix, cubics, products, quadratics, Matrix.mulVec] <;>
    ring

lemma quadratics_zero (v : Fin 5 → ℂ) (h : ∀ k, quadratics v k = 0) : v = 0 := by
  have hp : products v = 0 := by
    ext i
    fin_cases i <;> simp [products, h]
  have hm : complexMatrix *ᵥ cubics v = complexMatrix *ᵥ 0 := by
    rw [row_products, hp, Matrix.mulVec_zero]
  have hc : cubics v = 0 := by
    exact (Matrix.mulVec_injective_iff_isUnit.mpr
      (complexMatrix.isUnit_iff_isUnit_det.mpr
        (isUnit_iff_ne_zero.mpr complex_det_ne_zero))) hm
  ext i
  fin_cases i
'''
for i in range(5):
    column = indices[(i, i, i)]
    source += '  · have hcube := congrFun hc ' + str(column) + '\n'
    source += '    have hz : v ' + str(i) + ' ^ 3 = 0 := by\n'
    source += '      simpa [cubics, pow_succ] using hcube\n'
    source += '    exact pow_eq_zero hz\n'
source += '\nend PEqualNP.Outside.L_gct_231_aux.DiagonalAnchorMoment\n'
source = source.replace('namespace PEqualNP.Outside.L_gct_231_aux.DiagonalAnchorMoment',
    'open scoped Matrix\n\nnamespace PEqualNP.Outside.L_gct_231_aux.DiagonalAnchorMoment', 1)
if '--standalone' in sys.argv:
    start = source.index('def modularInverse')
    stop = source.index('def complexMatrix')
    source = source[:start] + source[stop:]
    start = source.index('lemma complex_det_ne_zero')
    stop = source.index('def quadratics')
    source = source[:start] + source[stop:]
    source = source.replace('lemma quadratics_zero (v : Fin 5 → ℂ)',
        'lemma quadratics_zero (complex_det_ne_zero : Matrix.det complexMatrix ≠ 0)\n    (v : Fin 5 → ℂ)')
(job / ('DiagonalAnchorObstructionBody.lean' if '--standalone' in sys.argv else 'DiagonalAnchorObstruction.lean')).write_text(source)
if '--probe' in sys.argv:
    source = source[:source.index('lemma row_products')]
    source += '''lemma row_zero (v : Fin 5 → ℂ) :
    (complexMatrix *ᵥ cubics v) 0 = products v 0 := by
  simp [complexMatrix, integerMatrix, cubics, products, quadratics, Matrix.mulVec]
  ring

end PEqualNP.Outside.L_gct_231_aux.DiagonalAnchorMoment
'''
    (job / 'DiagonalAnchorRowProbe.lean').write_text(source)
print(json.dumps({'bytes': len(source.encode()), 'lines': source.count('\n')}))
