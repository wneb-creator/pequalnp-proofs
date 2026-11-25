import hashlib
import json
from pathlib import Path

base = Path(__file__).resolve().parent
program = json.loads((base / 'pg3-marginal48-canonical-invalid.json').read_text())
assert program['input_count'] == 26 and program['or_count'] == 48
bad_row = 3735587
samples = [(1 << a) | (1 << b) for a in range(26) for b in range(26)] + [0, bad_row]
truth = (1 << len(samples)) - 1
inputs = [sum(1 << r for r, sample in enumerate(samples) if sample >> i & 1) for i in range(26)]
values = inputs[:]
certificates = []

def conjunction(refs):
    value = truth
    for ref in refs:
        value &= values[ref]
    return value

for g, operands in enumerate(program['operand_wire_lists']):
    assert all(type(i) is int and 0 <= i < 26 + g for refs in operands for i in refs)
    value = conjunction(operands[0]) | conjunction(operands[1])
    certificates.append(value)
    values.append(value)
result = conjunction(program['output_wire_list'])

def incidence(a, b):
    if a < 13 <= b:
        return (a + 26 - b) % 13 in (0, 1, 3, 9)
    if b < 13 <= a:
        return (b + 26 - a) % 13 in (0, 1, 3, 9)
    return False

assert all(bool(result >> (26 * a + b) & 1) == incidence(a, b) for a in range(26) for b in range(26))
assert not (result >> 676 & 1) and result >> 677 & 1
lines = [
    'import MarginalSeed48',
    'import CanonicalCompilerStructure',
    'import CanonicalCompilerSamples',
    'import GeometryRowsDefs',
    '',
    'namespace PEqualNP.Outside.L_meta_1896_aux.MarginalShadowControl',
    '',
    'open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity',
    'open PEqualNP.Outside.L_meta_1896_aux.CanonicalCompiler',
    '',
    'def badInput (i : Fin 26) : Bool := decide (i.val ∈ ({0, 1, 5, 16, 19, 20, 21} : Finset Nat))',
    '',
    'def pairInput (a b i : Fin 26) : Bool := decide (i = a ∨ i = b)',
    '',
    'def samples (r : Fin 678) (i : Fin 26) : Bool :=',
    '  if r.val < 676 then decide (i.val = r.val / 26 ∨ i.val = r.val % 26)',
    '  else if r.val = 676 then false else badInput i',
    '',
    'def pairIndex (a b : Fin 26) : Fin 678 := ⟨26 * a.val + b.val, by omega⟩',
    '',
    'def pairedIncidence (a b : Fin 26) : Bool :=',
    '  decide ((a.val < 13 ∧ 13 ≤ b.val ∧ (a.val + 26 - b.val) % 13 ∈',
    '      ({0, 1, 3, 9} : Finset Nat)) ∨',
    '    (b.val < 13 ∧ 13 ≤ a.val ∧ (b.val + 26 - a.val) % 13 ∈',
    '      ({0, 1, 3, 9} : Finset Nat)))',
    '',
    f'def truthMask : Nat := {truth}',
    '',
    'def inputMasks : Fin 26 → Nat := ![' + ', '.join(map(str, inputs)) + ']',
    '',
    'def certificates : List Nat := [' + ', '.join(map(str, certificates)) + ']',
    '',
    f'def result : Nat := {result}',
    '',
    'set_option maxRecDepth 100000 in',
    'set_option maxHeartbeats 0 in',
    'lemma masks_checked : checkMasks 48 marginalSeed48 truthMask inputMasks certificates result = true := by',
    '  decide +kernel',
    '',
    'set_option maxRecDepth 100000 in',
    'set_option maxHeartbeats 0 in',
    'lemma truth_bits : ∀ r : Fin 678, truthMask.testBit r.val = true := by',
    '  decide +kernel',
    '',
]
for i in range(26):
    lines.extend([
        'set_option maxRecDepth 100000 in',
        'set_option maxHeartbeats 0 in',
        f'lemma input_bits_{i} : ∀ r : Fin 678, (inputMasks {i}).testBit r.val = samples r {i} := by',
        '  decide +kernel',
        '',
    ])
selector = '(fun i => Fin.elim0 i)'
for i in reversed(range(26)):
    selector = f'(Fin.cases input_bits_{i} {selector})'
lines.extend([
    'lemma input_bits (r : Fin 678) (i : Fin 26) :',
    '    (inputMasks i).testBit r.val = samples r i := by',
    '  have h : ∀ i : Fin 26, ∀ r : Fin 678, (inputMasks i).testBit r.val = samples r i := by',
    f'    exact {selector}',
    '  exact h i r',
    '',
    'set_option maxRecDepth 100000 in',
    'set_option maxHeartbeats 0 in',
    'lemma result_pairs : ∀ a b : Fin 26, result.testBit (pairIndex a b).val = pairedIncidence a b := by',
    '  decide +kernel',
    '',
    'lemma result_empty : result.testBit 676 = false := by decide +kernel',
    'lemma result_bad : result.testBit 677 = true := by decide +kernel',
    '',
    'lemma samples_pair (a b : Fin 26) : samples (pairIndex a b) = pairInput a b := by',
    '  have hlt : 26 * a.val + b.val < 676 := by omega',
    '  have hdiv : (26 * a.val + b.val) / 26 = a.val := by omega',
    '  have hmod : (26 * a.val + b.val) % 26 = b.val := by omega',
    '  funext i',
    '  simp [samples, pairIndex, pairInput, hlt, hdiv, hmod, Fin.ext_iff]',
    '',
    'def circuit : Circuit := compile 48 marginalSeed48 26 Fin.val',
    '',
    'lemma sample_value (r : Fin 678) : circuitFun 26 circuit (samples r) = result.testBit r.val :=',
    '  compile_mask_at 48 marginalSeed48 truthMask inputMasks certificates result r.val',
    '    (samples r) (truth_bits r) (input_bits r) masks_checked',
    '',
    'lemma legal : Monotone2 circuit := compile_monotone2 48 marginalSeed48 26 Fin.val',
    '',
    'lemma count : {i : Fin circuit.gates.length | (circuit.gates[i]).op = GateOp.or}.ncard = 48 :=',
    '  compile_or_ncard_getElem 48 marginalSeed48 26 Fin.val',
    '',
    'lemma empty_value : circuitFun 26 circuit (fun _ => false) = false := by',
    '  simpa [samples, result_empty] using sample_value (676 : Fin 678)',
    '',
    'lemma pair_value (a b : Fin 26) : circuitFun 26 circuit (pairInput a b) = pairedIncidence a b := by',
    '  rw [← samples_pair]',
    '  exact (sample_value (pairIndex a b)).trans (result_pairs a b)',
    '',
    'lemma bad_value : circuitFun 26 circuit badInput = true := by',
    '  simpa [samples, result_bad] using sample_value (677 : Fin 678)',
    '',
    'set_option maxRecDepth 100000 in',
    'set_option maxHeartbeats 0 in',
    'lemma generic_bad : AllRows.admissible ({0, 1, 5} : Finset (Fin 13)) := by',
    '  decide +kernel',
    '',
    'set_option maxRecDepth 100000 in',
    'set_option maxHeartbeats 0 in',
    'lemma bad_is_row : badInput = AllRows.rowInput ({0, 1, 5} : Finset (Fin 13)) := by',
    '  funext i',
    '  have h : ∀ i : Fin 26, badInput i = AllRows.rowInput ({0, 1, 5} : Finset (Fin 13)) i := by',
    '    decide +kernel',
    '  exact h i',
    '',
    'lemma shadow_only_counterexample : ∃ C : Circuit, Monotone2 C ∧',
    '    {i : Fin C.gates.length | (C.gates[i]).op = GateOp.or}.ncard = 48 ∧',
    '    circuitFun 26 C (fun _ => false) = false ∧',
    '    (∀ a b : Fin 26, circuitFun 26 C (pairInput a b) = pairedIncidence a b) ∧',
    '    AllRows.admissible ({0, 1, 5} : Finset (Fin 13)) ∧',
    '    circuitFun 26 C (AllRows.rowInput ({0, 1, 5} : Finset (Fin 13))) = true := by',
    '  refine ⟨circuit, legal, count, empty_value, pair_value, generic_bad, ?_⟩',
    '  rw [← bad_is_row]',
    '  exact bad_value',
    '',
    'end PEqualNP.Outside.L_meta_1896_aux.MarginalShadowControl',
])
source = '\n'.join(lines) + '\n'
(base / 'MarginalShadowControl.lean').write_text(source)
report = {
    'status': 'SOURCE ONLY; not Lean compiled',
    'scope': '48OR exact behavior on empty and all ordered pairs, plus one admissible negative wrongly accepted',
    'is_refutation_of_posted_statement': False,
    'sample_count': 678,
    'distinct_weight_at_most_two_samples': len(set(samples[:-1])),
    'false_generic_row_mask': bad_row,
    'source_sha256': hashlib.sha256(source.encode()).hexdigest(),
}
(base / 'shadow-certificate-source.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
