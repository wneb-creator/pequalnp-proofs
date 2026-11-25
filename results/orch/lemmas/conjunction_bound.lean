import PEqualNP.Outside.L_meta_2592

namespace PEqualNP.Outside.L_meta_2592_aux.Stronger.Extended
open PEqualNP.Outside.L_meta_2592_aux.Subgraphs

lemma canonicalize_first_used (d : Fin 4) (a b : Fin 10) (hab : a ≠ b) {k S}
    (run : Live true target k S)
    (used : bin d.val (pins.getD a.val zero) (pins.getD b.val zero) ∈ S)
    (raw : ∀ v ∈ S, v ∈ pins ++ [bin d.val (pins.getD a.val zero) (pins.getD b.val zero)]) :
    ∃ (j : Fin 2) (U : Finset Sig), Live true target k U ∧
      bin d.val (pins.getD 0 zero) (pins.getD (j.val + 1) zero) ∈ U ∧
      ∀ v ∈ U, v ∈ pins ++ [bin d.val (pins.getD 0 zero) (pins.getD (j.val + 1) zero)] := by
  classical
  obtain ⟨p, hzero, hsecond, hp⟩ := normalize_pair a b hab
  let j : Fin 2 := if adjacent a b then 0 else 1
  let q := p.symm
  have hqa : q a = 0 := by
    dsimp [q]
    rw [← hzero, Equiv.symm_apply_apply]
  have hqb : (q b).val = j.val + 1 := by
    dsimp [q]
    rw [← hsecond, Equiv.symm_apply_apply]
    cases h : adjacent a b <;> simp [j, h]
  have hq : ∀ u v, adjacent (q u) (q v) = adjacent u v := by
    intro u v
    simpa only [q, Equiv.apply_symm_apply] using (hp (p.symm u) (p.symm v)).symm
  refine ⟨j, S.image (renameVertices q), ?_, ?_, ?_⟩
  · simpa only [renameVertices_target q hq] using live_renameVertices run q
  · apply Finset.mem_image.mpr
    refine ⟨bin d.val (pins.getD a.val zero) (pins.getD b.val zero), used, ?_⟩
    rw [renameVertices_bin, renameVertices_pin, renameVertices_pin, hqa, hqb]
    rfl
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    have hw' := raw w hw
    simp only [List.mem_append, List.mem_singleton] at hw' ⊢
    rcases hw' with hpin | rfl
    · exact Or.inl (renameVertices_mem_pins q hpin)
    · right
      rw [renameVertices_bin, renameVertices_pin, renameVertices_pin, hqa, hqb]
      rfl

end PEqualNP.Outside.L_meta_2592_aux.Stronger.Extended

namespace PEqualNP.Outside.L_meta_2592_aux.Stronger.Extended

lemma first_proper_binary_used {k S} (run : Live true target k S)
    (raw : ∀ a ∈ S, a ∈ pins) :
    ∃ j a b d T, k = j + 1 ∧ a ∈ pins ∧ b ∈ pins ∧ a ≠ b ∧ d < 4 ∧
      Live true target j T ∧ bin d a b ∈ T ∧ ∀ c ∈ T, c ∈ pins ++ [bin d a b] := by
  cases k with
  | zero =>
    obtain ⟨rfl, _⟩ := run
    have hm := raw target (by simp)
    have hn : target ∉ pins := by decide +kernel
    exact (hn hm).elim
  | succ j =>
    obtain ⟨U,a,b,d,hd,rfl,_,_,hab,_,tail⟩ := run
    refine ⟨j,a,b,d,insert (bin d a b) U,rfl,raw a (by simp),raw b (by simp),hab,?_,tail,by simp,?_⟩
    · rcases hd with h | ⟨_,h⟩ <;> omega
    · intro c hc
      rcases Finset.mem_insert.mp hc with rfl | hc
      · exact List.mem_append_right _ (by simp)
      · exact List.mem_append_left _ (raw c (by simp [hc]))

end PEqualNP.Outside.L_meta_2592_aux.Stronger.Extended

namespace PEqualNP.Outside.L_meta_2592_aux.Stronger.Extended

lemma conjunction_tail_lower (d : Fin 4) (hd : d.val ≠ 1)
    (a b : Fin 10) (hab : a ≠ b) {k S}
    (run : Live true target k S)
    (used : bin d.val (pins.getD a.val zero) (pins.getD b.val zero) ∈ S)
    (raw : ∀ v ∈ S, v ∈ pins ++ [bin d.val (pins.getD a.val zero) (pins.getD b.val zero)]) :
    17 ≤ k := by
  by_cases hthree : d.val = 3
  · have swap : bin d.val (pins.getD a.val zero) (pins.getD b.val zero) =
        bin 2 (pins.getD b.val zero) (pins.getD a.val zero) := by
      apply bit_ext
      intro r
      simp [transport_bit_bin, hthree, Bool.and_comm]
    have used' : bin 2 (pins.getD b.val zero) (pins.getD a.val zero) ∈ S := by
      simpa only [swap] using used
    have raw' : ∀ v ∈ S, v ∈ pins ++ [bin 2 (pins.getD b.val zero) (pins.getD a.val zero)] := by
      simpa only [swap] using raw
    obtain ⟨j,U,hu,he,hr⟩ := canonicalize_first_used 2 b a hab.symm run used' raw'
    exact CanonicalBank.conjunction_lower 2 j (Or.inr rfl) hu hr he
  · have hd' : d = 0 ∨ d = 2 := by
      have bound := d.isLt
      have possibilities : d.val = 0 ∨ d.val = 2 := by omega
      rcases possibilities with h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Fin.ext h)
    obtain ⟨j,U,hu,he,hr⟩ := canonicalize_first_used d a b hab run used raw
    exact CanonicalBank.conjunction_lower d j hd' hu hr he

lemma first_binary_or_eighteen {k S} (run : Live true target k S)
    (raw : ∀ a ∈ S, a ∈ pins) :
    18 ≤ k ∨ ∃ (j : Nat) (a b : Fin 10) (T : Finset Sig),
      k = j + 1 ∧ a ≠ b ∧ Live true target j T ∧
      bin 1 (pins.getD a.val zero) (pins.getD b.val zero) ∈ T ∧
      ∀ v ∈ T, v ∈ pins ++ [bin 1 (pins.getD a.val zero) (pins.getD b.val zero)] := by
  by_cases large : 18 ≤ k
  · exact Or.inl large
  · right
    obtain ⟨j,a,b,d,T,hk,ha,hb,hab,hd,ht,he,hr⟩ := first_proper_binary_used run raw
    have hlist : List.ofFn (fun i : Fin 10 => pins.getD i.val zero) = pins := rfl
    have ha' : a ∈ List.ofFn (fun i : Fin 10 => pins.getD i.val zero) := hlist.symm ▸ ha
    have hb' : b ∈ List.ofFn (fun i : Fin 10 => pins.getD i.val zero) := hlist.symm ▸ hb
    obtain ⟨ia,rfl⟩ := List.mem_ofFn.mp ha'
    obtain ⟨ib,rfl⟩ := List.mem_ofFn.mp hb'
    have indices : ia ≠ ib := fun eq => hab (congrArg (fun i : Fin 10 => pins.getD i.val zero) eq)
    have hone : d = 1 := by
      by_contra hne
      have lower := conjunction_tail_lower ⟨d,hd⟩ hne ia ib indices ht he hr
      omega
    subst d
    exact ⟨j,ia,ib,T,hk,indices,ht,he,hr⟩

end PEqualNP.Outside.L_meta_2592_aux.Stronger.Extended
