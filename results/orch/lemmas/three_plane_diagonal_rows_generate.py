from pathlib import Path
import json
import sys

job = Path('/tmp/oec/pequalnp-pilot-79')
base = (job / 'DiagonalAnchorMoment.lean').read_text()
data = json.loads((job / 'three-plane-diagonal-anchor-modular-inverse-5.json').read_text())
prefix = base[:base.index('def integerMatrix')]
source = prefix
for name, matrix, coefficient in [
    ('integer', data['integer_matrix'], 'ℤ'),
    ('reduced', [[x % 5 for x in row] for row in data['integer_matrix']], '(ZMod 461)'),
    ('inverse', data['modular_inverse'], '(ZMod 461)')]:
    for i, row in enumerate(matrix):
        source += 'def ' + name + 'Row' + str(i) + ' : Fin 35 → ' + coefficient + ' :=\n'
        source += '  ![' + ', '.join(map(str, row)) + ']\n\n'
    matrix_name = {'integer': 'integerMatrix', 'reduced': 'reducedMatrix', 'inverse': 'modularInverse'}[name]
    source += 'def ' + matrix_name + ' : Matrix (Fin 35) (Fin 35) ' + coefficient + ' :=\n'
    source += '  ![' + ', '.join(name + 'Row' + str(i) for i in range(35)) + ']\n\n'
source += '''def modularMatrix : Matrix (Fin 35) (Fin 35) (ZMod 461) :=
  (Int.castRingHom (ZMod 461)).mapMatrix integerMatrix

'''
for i in range(35):
    source += 'set_option maxRecDepth 100000 in\nset_option maxHeartbeats 20000000 in\n'
    source += 'lemma reduced_row_' + str(i) + ' : ∀ j,\n'
    source += '    modularMatrix ' + str(i) + ' j = reducedMatrix ' + str(i) + ' j := by\n'
    source += '  decide\n\n'
source += 'lemma reduced_matrix : modularMatrix = reducedMatrix := by\n'
source += '  ext i j\n  fin_cases i\n'
for i in range(35):
    source += '  · exact reduced_row_' + str(i) + ' j\n'
source += '\n'
for i in range(35):
    source += 'set_option maxRecDepth 100000 in\nset_option maxHeartbeats 20000000 in\n'
    source += 'lemma inverse_row_' + str(i) + ' : ∀ j,\n'
    source += '    (reducedMatrix * modularInverse) ' + str(i) + ' j = (1 : Matrix (Fin 35) (Fin 35) (ZMod 461)) ' + str(i) + ' j := by\n'
    source += '  decide\n\n'
    if '--progress' in sys.argv:
        source += '#check inverse_row_' + str(i) + '\n\n'
source += 'lemma inverse_certificate : modularMatrix * modularInverse = 1 := by\n'
source += '  rw [reduced_matrix]\n  ext i j\n  fin_cases i\n'
for i in range(35):
    source += '  · exact inverse_row_' + str(i) + ' j\n'
source += '\n' + base[base.index('lemma modular_det_ne_zero'):]
source = source.replace('import Mathlib.Data.ZMod.Basic\n',
    'import Mathlib.Data.ZMod.Basic\nimport Mathlib.Tactic.FinCases\n')
source = source.replace('ZMod 461', 'ZMod 5')
if '--kernel' in sys.argv:
    source = source.replace('  decide\n', '  decide +kernel\n')
(job / ('DiagonalAnchorMomentKernel.lean' if '--kernel' in sys.argv else 'DiagonalAnchorMomentReducedFive.lean')).write_text(source)
print(json.dumps({'bytes': len(source.encode()), 'lines': source.count('\n')}))
