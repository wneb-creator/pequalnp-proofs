from pathlib import Path
from fractions import Fraction
import json

job = Path('/tmp/oec/pequalnp-pilot-79')
data = json.loads((job / 'three-plane-diagonal-anchor-exact.json').read_text())
matrices = []
for encoded in data['Q_j2_j1_j0'][::-1]:
    assert all(den == 1 for row in encoded for num, den in row)
    matrices.append([[num for num, den in row] for row in encoded])
operator = [[384 * Fraction(num, den) for num, den in row] for row in data['P']]
assert all(x.denominator == 1 for row in operator for x in row)
operator = [[int(x) for x in row] for row in operator]

def matrix(name, values, coefficient='ℂ'):
    return 'def ' + name + ' : Matrix (Fin 5) (Fin 5) ' + coefficient + ' :=\n  !![' + \
        ';\n    '.join(', '.join(map(str, row)) for row in values) + ']\n\n'

source = (job / 'DiagonalAnchorObstructionBody.lean').read_text()
source = source.removesuffix('end PEqualNP.Outside.L_gct_231_aux.DiagonalAnchorMoment\n')
for k, values in enumerate(matrices):
    source += matrix('hessian' + str(k), values)
source += matrix('integerOperator', operator)
source += '''def bilinear (H : Matrix (Fin 5) (Fin 5) ℂ) (v w : Fin 5 → ℂ) : ℂ :=
  v ⬝ᵥ (H *ᵥ w)

def transform (v : Fin 5 → ℂ) : Fin 5 → ℂ := integerOperator *ᵥ v

'''
arguments = [('hessian0', 'v', 'v'), ('hessian1', 'v', 'v'),
    ('hessian1', 'v', '(transform v)'), ('hessian1', '(transform v)', '(transform v)'),
    ('hessian2', 'v', 'v'), ('hessian2', 'v', '(transform v)'),
    ('hessian2', '(transform v)', '(transform v)')]
scales = [1, 1, 384, 147456, 1, 384, 147456]
for k, ((H, v, w), scale) in enumerate(zip(arguments, scales)):
    source += 'set_option maxRecDepth 100000 in\nset_option maxHeartbeats 20000000 in\n'
    source += 'lemma form_' + str(k) + ' (v : Fin 5 → ℂ) :\n'
    source += '    bilinear ' + H + ' ' + v + ' ' + w + ' = ' + str(scale) + ' * quadratics v ' + str(k) + ' := by\n'
    source += '  simp [bilinear, transform, integerOperator, hessian0, hessian1, hessian2, quadratics,\n'
    source += '    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]\n  ring\n\n'
source += '''set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma operator_pairing (v w : Fin 5 → ℂ) :
    bilinear hessian0 v (transform w) = 384 * bilinear hessian1 v w := by
  simp [bilinear, transform, integerOperator, hessian0, hessian1,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

lemma net_obstruction
    (hdet : Matrix.det complexMatrix ≠ 0) (v : Fin 5 → ℂ)
    (h00 : bilinear hessian0 v v = 0)
    (h10 : bilinear hessian1 v v = 0)
    (h11 : bilinear hessian1 v (transform v) = 0)
    (h12 : bilinear hessian1 (transform v) (transform v) = 0)
    (h20 : bilinear hessian2 v v = 0)
    (h21 : bilinear hessian2 v (transform v) = 0)
    (h22 : bilinear hessian2 (transform v) (transform v) = 0) : v = 0 := by
  apply quadratics_zero hdet v
  intro k
  fin_cases k
'''
for k, hypothesis in enumerate(['h00', 'h10', 'h11', 'h12', 'h20', 'h21', 'h22']):
    source += '  · rw [form_' + str(k) + '] at ' + hypothesis + '\n'
    source += '    exact (mul_eq_zero.mp ' + hypothesis + ').resolve_left (by norm_num)\n'
source += '\nend PEqualNP.Outside.L_gct_231_aux.DiagonalAnchorMoment\n'
source = source.replace('import Mathlib.Tactic.Ring\n',
    'import Mathlib.Tactic.Ring\nimport Mathlib.Tactic.NormNum\n')
(job / 'DiagonalAnchorHessian.lean').write_text(source)
print(json.dumps({'bytes': len(source.encode()), 'lines': source.count('\n')}))
