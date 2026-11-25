from pathlib import Path
p=Path('/tmp/oec/pequalnp-pilot-62')
repo=Path('/workspace/pequalnp-proofs')
allrows=(repo/'results/orch/lemmas/AllRows.lean').read_text()
rowdef=allrows[allrows.index('def row ('):allrows.index('def rowInput')]
flagtext=(p/'flags-addition.txt').read_text()
flagdefs=flagtext[flagtext.index('def flag'):flagtext.index('def shared')]
minimal='namespace AllRows\n\nabbrev R := Fin 36 × Fin 13\n\n'+rowdef+'end AllRows\n\nnamespace FourRows\n\ndef pairInput (p l : Fin 13) (v : Fin 26) : Bool :=\n  decide (v = Fin.castAdd 13 p ∨ v = Fin.natAdd 13 l)\n\nend FourRows\n\nnamespace Flags\n\nopen FourRows\n\n'+flagdefs+'end Flags\n\n'
base=(repo/'results/orch/lemmas/PackingThreeCheck.lean').read_text()
base=base[:base.index('set_option maxRecDepth 100000 in\nset_option maxHeartbeats 0 in\nlemma root_check_21')]
base=base.replace('namespace PackingThree\n',minimal+'namespace PackingThree\n',1)
cert=''
for v in range(26):
 cert+=f"""set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma singleton_active_{v} : ∀ r : AllRows.R,
    (block {v}).active.testBit (13 * r.1.val + r.2.val) = AllRows.row r {v} := by
  decide +kernel

"""
cases='(fun i => Fin.elim0 i)'
for v in reversed(range(26)):cases=f'(Fin.cases singleton_active_{v} {cases})'
cert+='lemma singleton_active : ∀ v : Fin 26, ∀ r : AllRows.R,\n    (block ⟨v.val, by omega⟩).active.testBit (13 * r.1.val + r.2.val) = AllRows.row r v := by\n  exact '+cases+'\n\n'
cert+="""set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma singleton_edges : ∀ v : Fin 26, ∀ a : Fin 52,
    (block ⟨v.val, by omega⟩).edges.testBit a.val = Flags.input a v := by
  decide +kernel

"""
(p/'packing3-mask-data-certificates.txt').write_text(cert)
(repo/'results/orch/lemmas/PackingThreeData.lean').write_text(base+cert+'end PackingThree\nend PEqualNP.Outside.L_meta_1896_aux\n')
