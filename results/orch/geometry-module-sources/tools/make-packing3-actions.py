import json
from pathlib import Path

p = Path('/tmp/oec/pequalnp-pilot-62')
repo = Path('/workspace/pequalnp-proofs')
d = json.loads((p / 'packing3-finite-actions.json').read_text())
allrows = (repo / 'results/orch/lemmas/AllRows.lean').read_text()
rowdef = allrows[allrows.index('def row ('):allrows.index('def rowInput')]
flags = (p / 'flags-addition.txt').read_text()
flagdefs = flags[flags.index('def flag'):flags.index('def shared')]
s = 'import PEqualNP.Defs\n\nnamespace PEqualNP.Outside.L_meta_1896_aux\n\nnamespace AllRows\n\nabbrev R := Fin 36 × Fin 13\n\n' + rowdef + 'end AllRows\n\nnamespace FourRows\n\ndef pairInput (p l : Fin 13) (v : Fin 26) : Bool :=\n  decide (v = Fin.castAdd 13 p ∨ v = Fin.natAdd 13 l)\n\nend FourRows\n\nnamespace Flags\n\nopen FourRows\n\n' + flagdefs + 'end Flags\n\nnamespace PackingOrbits\n\n'
orbits = (repo / 'results/orch/lemmas/PackingThreeOrbits.lean').read_text()
s += orbits[orbits.index('def pairEnds'):orbits.index('def labelWord')]

def nested(values, size, render):
    return '[\n    ' + ',\n    '.join('[' + ', '.join(render(v) for v in values[i:i+size]) + ']' for i in range(0, len(values), size)) + ']'

for name, key in [('rowPerm', 'row_permutations'), ('rowInverse', 'row_inverse_permutations')]:
    table = '[\n  ' + ',\n  '.join(nested(vals, 13, lambda v: '(' + str(v//13) + ', ' + str(v%13) + ')') for vals in d[key]) + ']'
    s += f'def {name} (g : Fin 4) (r : AllRows.R) : AllRows.R :=\n  ((({table} : List (List (List AllRows.R))).getD g.val []).getD r.1.val []).getD r.2.val (0, 0)\n\n'
for name, key in [('flagPerm', 'flag_permutations'), ('flagInverse', 'flag_inverse_permutations')]:
    table = str(d[key])
    s += f'def {name} (g : Fin 4) (a : Fin 52) : Fin 52 :=\n  (({table} : List (List (Fin 52))).getD g.val []).getD a.val 0\n\n'
table = '[\n  ' + ',\n  '.join(nested(vals, 25, str) for vals in d['pair_inverse_permutations']) + ']'
s += f'def pairInverse (g : Fin 4) (i : Fin 325) : Fin 325 :=\n  ((({table} : List (List (List (Fin 325)))).getD g.val []).getD (i.val / 25) []).getD (i.val % 25) 0\n\n'

def cert(name, statement):
    return 'set_option maxRecDepth 100000 in\nset_option maxHeartbeats 0 in\nlemma ' + name + ' : ' + statement + ' := by\n  decide +kernel\n\n'

s += cert('vertexPerm_bijective', '∀ g : Fin 4, Function.Bijective (vertexPerm g)')
for stem, ty, param in [('row', 'AllRows.R', 'r'), ('flag', 'Fin 52', 'a'), ('pair', 'Fin 325', 'i')]:
    s += cert(stem + '_inverse_identities', f'∀ g : Fin 4, ∀ {param} : {ty},\n    {stem}Inverse g ({stem}Perm g {param}) = {param} ∧\n    {stem}Perm g ({stem}Inverse g {param}) = {param}')
    s += f'''lemma {stem}Perm_bijective (g : Fin 4) : Function.Bijective ({stem}Perm g) := by
  constructor
  · intro x y h
    have hx := ({stem}_inverse_identities g x).1
    have hy := ({stem}_inverse_identities g y).1
    rw [h] at hx
    exact hx.symm.trans hy
  · intro y
    exact ⟨{stem}Inverse g y, ({stem}_inverse_identities g y).2⟩

'''
s += cert('pairPerm_ends', '∀ g : Fin 4, ∀ i : Fin 325,\n    ({(pairEnds (pairPerm g i)).1, (pairEnds (pairPerm g i)).2} : Finset (Fin 26)) =\n    {vertexPerm g (pairEnds i).1, vertexPerm g (pairEnds i).2}')
for g in range(4):
    s += cert('row_preserved_' + str(g), f'∀ r : AllRows.R, ∀ v : Fin 26,\n    AllRows.row (rowPerm {g} r) (vertexPerm {g} v) = AllRows.row r v')
s += '''lemma row_preserved : ∀ g : Fin 4, ∀ r : AllRows.R, ∀ v : Fin 26,
    AllRows.row (rowPerm g r) (vertexPerm g v) = AllRows.row r v := by
  exact Fin.cases row_preserved_0 (Fin.cases row_preserved_1
    (Fin.cases row_preserved_2 (Fin.cases row_preserved_3 (fun i => Fin.elim0 i))))

'''
s += cert('flag_preserved', '∀ g : Fin 4, ∀ a : Fin 52, ∀ v : Fin 26,\n    Flags.input (flagPerm g a) (vertexPerm g v) = Flags.input a v')
s += 'end PackingOrbits\nend PEqualNP.Outside.L_meta_1896_aux\n'
(repo / 'results/orch/lemmas/PackingThreeActions.lean').write_text(s)
print('SOURCE_BYTES', len(s.encode()))
