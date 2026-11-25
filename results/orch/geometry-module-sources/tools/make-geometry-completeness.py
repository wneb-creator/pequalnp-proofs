import json
from pathlib import Path

p = Path('/tmp/oec/pequalnp-pilot-62')
m = p / 'lean-modules'
rows = json.loads((p / 'geometry-data.json').read_text())['generic']
indices = {row['S']: i for i, row in enumerate(rows)}
assert len(indices) == 468
packed = sum(index << (9*mask) for mask, index in indices.items())
for mask, index in indices.items():
    assert (packed >> (9*mask)) & 511 == index
source = '''import GeometryMaskCore

namespace PEqualNP.Outside.L_meta_1896_aux.GeometryComplete

'''
source += 'def indexTable : Nat := ' + hex(packed) + '\n\n'
source += '''def rowFor (m : Fin 8192) : AllRows.R :=
  let k : Fin 468 := ⟨((indexTable >>> (9 * m.val)) &&& 511) % 468,
    Nat.mod_lt _ (by decide)⟩
  (⟨k.val / 13, by omega⟩, ⟨k.val % 13, Nat.mod_lt _ (by decide)⟩)

'''
ending = 'end PEqualNP.Outside.L_meta_1896_aux.GeometryComplete\n'
(m / 'GeometryMaskData.lean').write_text(source + ending)
certs = ''
for g in range(64):
    certs += f'''set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma classified_{g} : ∀ i : Fin 128,
    let m : Fin 8192 := ⟨128 * {g} + i.val, by omega⟩
    AllRows.admissible (decode m) → AllRows.points (rowFor m) = decode m := by
  unfold AllRows.admissible
  decide +kernel

'''
cases = '(fun i => Fin.elim0 i)'
for g in reversed(range(64)):
    cases = f'(Fin.cases classified_{g} {cases})'
certs += '''set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma masks_classified : ∀ m : Fin 8192,
    AllRows.admissible (decode m) → AllRows.points (rowFor m) = decode m := by
  apply classified_of_chunks rowFor
  exact ''' + cases + '''

lemma admissible_complete (X : Finset (Fin 13)) (hX : AllRows.admissible X) :
    ∃ r : AllRows.R, AllRows.points r = X := by
  exact complete_of_classified rowFor masks_classified X hX

'''
prefix = 'import GeometryMaskData\nimport GeometryCompletenessProofs\n\nnamespace PEqualNP.Outside.L_meta_1896_aux.GeometryComplete\n\n'
(m / 'GeometryCompleteness.lean').write_text(prefix + certs + ending)
first = certs[:certs.index('set_option maxRecDepth 100000 in', 1)]
(m / 'GeometryCompletenessBench.lean').write_text(prefix + first + ending)
(p / 'geometry-completeness-index.json').write_text(json.dumps({'rows': len(rows), 'indices': indices, 'packed_bits': packed.bit_length()}))
print('INDEX_BITS', packed.bit_length(), 'CHUNKS', 64, 'CASES_PER_CHUNK', 128)
