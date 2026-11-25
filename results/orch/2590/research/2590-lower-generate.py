from pathlib import Path
base=Path('results/orch/lemmas/existing_binary17_base.lean').read_text()
newns='PEqualNP.Outside.L_meta_2590_aux.MonoNine'
oldns='PEqualNP.Outside.L_meta_2592_aux.Binary16'
ext=base[base.index('namespace Extended\n'):base.index('end Extended\n')+len('end Extended\n')]
a=ext.index('theorem realize (C : Circuit)')
b=ext.index('\ntheorem first_needed',a)
real='''theorem realize (C : Circuit) (mono : PEqualNP.MetaComplexity.Monotone2 C)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = f10 x) :
    ∃ k S, k ≤ C.size ∧ Live false target k S ∧ ∀ a ∈ S, a ∈ initial := by
  have legal : PEqualNP.MetaComplexity.FanInTwo C := by
    intro g hg
    obtain ⟨ho, hl⟩ := mono g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ho ⊢
    exact ⟨ho.imp id Or.inl, hl⟩
  have nonot : ∀ g ∈ C.gates, isNot g = false := by
    intro g hg
    have ho := (mono g hg).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ho
    rcases ho with ho | ho <;> simp [isNot, ho]
  have he : (execute C.gates initial).getD C.output zero = target := by
    apply bit_ext
    intro r
    rw [←b_read,execute_bits _ _ _ (fun g hg => (legal g hg).1)]
    change (C.wires (initial.map (bit r))).getD C.output false = _
    rw [rowInputs]
    exact (computes _).trans (rowTarget r).symm
  have hp : proper target := by unfold proper; decide +kernel
  have out := get_rep (u:=false) (execute C.gates initial) C.output
  rw [he] at out
  unfold Repr at out
  rw [nrm_id (show bit 0 target=false by decide +kernel)] at out
  obtain ⟨k,S,hk,run,hs⟩ := extract C.gates initial legal (u:=false) (fun _ => nonot) hp
    (out.resolve_right (fun h => h hp))
  have ns : initial.all plainWord = true := by decide +kernel
  rw [nrm_map ns] at hs
  refine ⟨k,S,?_,run,hs⟩
  exact hk.trans (List.countP_le_length)
'''
ext=ext[:a]+real+ext[b:]
ext=ext.replace('run : Live true target','run : Live false target')
orbit=base[base.index('def orbitWire'):base.index('namespace Extended\n')]
proj=base[base.index('def embed (r : Row)'):base.index('theorem nineFloor :')]
canon=base[base.index('def canonicalExtra'):]
canon=canon[:canon.rfind('end '+oldns)]
canon=canon.replace('Live true','Live false').replace('supply true','supply false').replace('suffixSixteen','suffixSeventeen').replace('16 ≤ k','17 ≤ k').replace('(L := 15)','(L := 16)').replace('nineFloor','monoNineFloor')
floor='''theorem graph_proper : proper graph := by unfold proper; decide +kernel

theorem monoNineFloor : Lower false inputs graph 16 := by
  intro k bank path hit
  have plain : plainWord graph = true := by decide +kernel
  have init : inputs.all plainWord = true := by decide +kernel
  obtain ⟨j,S,hj,run,raw⟩ := reach_live graph_proper plain init path hit
  rw [orbitAllInputs run raw] at run
  by_contra! small
  exact monoRoot j (by omega) run

'''
text='import Mathlib.Tactic\nimport ExistingMonoNine\n\nnamespace '+newns+'\nopen PEqualNP.CircuitLowerBounds\n\n'+orbit+ext+proj+floor+canon+'\nend '+newns+'\n'
Path('results/orch/2590/lemmas/lower_mono18_base.lean').write_text(text)
print('Generated monochrome projection bridge',len(text.splitlines()),'lines')
