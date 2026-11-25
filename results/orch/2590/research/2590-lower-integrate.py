from pathlib import Path
ns='PEqualNP.Outside.L_meta_2590_aux.MonoNine'
def without_imports(s):return '\n'.join(l for l in s.splitlines() if not l.startswith('import '))+'\n'
base=Path('results/orch/2590/lemmas/lower_mono18_base.lean').read_text()
pair=without_imports(Path('results/orch/lemmas/lower_bound_pair_symmetry.lean').read_text()).replace('L_meta_2592_aux','L_meta_2590_aux')
row=without_imports(Path('results/orch/lemmas/lower_bound_row_encoding.lean').read_text()).replace('L_meta_2592_aux','L_meta_2590_aux')
maplive=Path('results/orch/lemmas/semantics_live_map_fragment.lean').read_text()
first='''lemma first_binary_split (C : Circuit) (legal : PEqualNP.MetaComplexity.Monotone2 C)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = Extended.f10 x) :
    ∃ (k : ℕ) (U : Finset Extended.Sig) (a b : Extended.Sig) (d : ℕ),
      k + 1 ≤ C.size ∧ d < 2 ∧ a ∈ Extended.initial ∧ b ∈ Extended.initial ∧ a ≠ b ∧
      Extended.Live false Extended.target k (insert (Extended.bin d a b) U) ∧
      ∀ v ∈ U, v ∈ Extended.initial := by
  obtain ⟨k, S, hk, run, raw⟩ := Extended.realize C legal computes
  cases k with
  | zero =>
      obtain ⟨rfl, hp⟩ := run
      have hmem := raw Extended.target (by simp)
      have hn : Extended.target ∉ Extended.initial := by decide +kernel
      exact False.elim (hn hmem)
  | succ k =>
      obtain ⟨U, a, b, d, hd, rfl, ha, hb, hab, hfresh, tail⟩ := run
      have hd2 : d < 2 := by
        rcases hd with hd | ⟨hu, hd⟩
        · exact hd
        · exact Bool.noConfusion hu
      exact ⟨k, U, a, b, d, hk, hd2, raw a (by simp), raw b (by simp), hab,
        tail, fun v hv => raw v (by simp [hv])⟩

lemma binary_floor18_of_suffix
    (suffix : ∀ (k : ℕ) (S : Finset Extended.Sig) (a b : Extended.Sig) (d : ℕ),
      d < 2 → a ∈ Extended.initial → b ∈ Extended.initial → a ≠ b →
      Extended.Live false Extended.target k S →
      (∀ v ∈ S, v ∈ Extended.initial ++ [Extended.bin d a b]) → 17 ≤ k)
    (C : Circuit) (legal : PEqualNP.MetaComplexity.Monotone2 C)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = Extended.f10 x) :
    18 ≤ C.size := by
  obtain ⟨k, U, a, b, d, hk, hd, ha, hb, hab, tail, raw⟩ := first_binary_split C legal computes
  have floor : 17 ≤ k := by
    apply suffix k (insert (Extended.bin d a b) U) a b d hd ha hb hab tail
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · simp
    · exact List.mem_append_left _ (raw v hv)
  omega
'''
trans=Path('results/orch/lemmas/lower_bound_transport_fragment.lean').read_text()
trans=trans.replace('PEqualNP.Outside.L_meta_2592_aux.Binary16',ns).replace('L_meta_2592_aux','L_meta_2590_aux')
trans=trans.replace('Live true','Live false').replace('16 ≤ k','17 ≤ k')
trans=trans[:trans.index('lemma binary_floor17_of_canonical')]
# trans leaves the namespace open.
finish='''lemma monotone_eighteen (C : Circuit) (legal : PEqualNP.MetaComplexity.Monotone2 C)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = Extended.f10 x) :
    18 ≤ C.size := by
  apply binary_floor18_of_suffix _ C legal computes
  intro k S a b d hd ha hb hab run raw
  obtain ⟨ia,rfl⟩ := member_pin ha
  obtain ⟨ib,rfl⟩ := member_pin hb
  have hne : ia ≠ ib := fun he => hab (congrArg inputPin he)
  exact suffix_of_canonical (fun j d k S run raw => suffixSeventeen j d run raw)
    ia ib hne ⟨d,by omega⟩ k S run raw

end '''+ns+'\n'
text=base+'\n'+pair+'\n'+row+'\nnamespace '+ns+'\nopen PEqualNP.CircuitLowerBounds\n'+maplive+'\n'+first+'\nend '+ns+'\n'+trans+finish
Path('results/orch/2590/lemmas/lower_mono18_integration.lean').write_text(text)
print('Generated integrated18-gate bridge',len(text.splitlines()),'lines')
