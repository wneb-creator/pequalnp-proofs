namespace PEqualNP.Outside.L_meta_1886_aux.ModeFloor

open PEqualNP.Outside.L_meta_2592_aux.Stronger
open Extended

lemma raw_lower {u : Bool} {L : Nat} (floor : Lower u inputs graph L) {k S}
    (run : Live u target k S) (raw : ∀ a ∈ S, a ∈ pins) : L + 2 ≤ k := by
  obtain ⟨n,a,b,d,T,eqk,ha,hb,hab,hd,tail,used,bank⟩ := first_proper_binary_mode run raw
  have dlt : d < 4 := by rcases hd with h | ⟨_,h⟩ <;> omega
  have hlist : List.ofFn (fun i : Fin 10 => pins.getD i.val zero) = pins := rfl
  rw [←hlist] at ha hb
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hb
  have hij : i ≠ j := fun eq => hab (congrArg (fun v : Fin 10 => pins.getD v.val zero) eq)
  obtain ⟨v,U,tail',_,bank'⟩ := canonicalize_first_mode ⟨d,dlt⟩ i j hij tail used bank
  have lower := MonoBank.lower floor ⟨d,dlt⟩ v tail' bank'
  omega

lemma and_bank_lower {u : Bool} {L : Nat} (floor : Lower u inputs graph L)
    (a b : Fin 10) (hab : a ≠ b) {k S}
    (run : Live u target k S)
    (raw : ∀ v ∈ S, v ∈ pins ++ [bin 0 (pins.getD a.val zero) (pins.getD b.val zero)]) :
    L + 2 ≤ k := by
  by_cases used : bin 0 (pins.getD a.val zero) (pins.getD b.val zero) ∈ S
  · obtain ⟨j,U,run',used',raw'⟩ := canonicalize_first_mode 0 a b hab run used raw
    exact MonoBank.conjunction_lower floor 0 j (Or.inl rfl) run' raw' used'
  · apply raw_lower floor run
    intro v hv
    have hm := raw v hv
    simp only [List.mem_append,List.mem_singleton] at hm
    exact hm.resolve_right (fun eq => used (eq ▸ hv))

lemma or_bank_lower {u : Bool} {L : Nat} (floor : Lower u inputs graph L)
    (a b : Fin 10) (hab : a ≠ b) {k S}
    (run : Live u target k S)
    (raw : ∀ v ∈ S, v ∈ pins ++ [bin 1 (pins.getD a.val zero) (pins.getD b.val zero)]) :
    L + 1 ≤ k := by
  by_cases used : bin 1 (pins.getD a.val zero) (pins.getD b.val zero) ∈ S
  · obtain ⟨j,U,run',_,raw'⟩ := canonicalize_first_mode 1 a b hab run used raw
    exact MonoBank.lower floor 1 j run' raw'
  · have h : L + 2 ≤ k := raw_lower floor run (by
      intro v hv
      have hm := raw v hv
      simp only [List.mem_append,List.mem_singleton] at hm
      exact hm.resolve_right (fun eq => used (eq ▸ hv)))
    omega

lemma monotone_first_or_or_extra {L : Nat} (floor : Lower false inputs graph L) {k S}
    (run : Live false target k S) (raw : ∀ a ∈ S, a ∈ pins) :
    L + 3 ≤ k ∨ ∃ (j : Nat) (a b : Fin 10) (T : Finset Extended.Sig),
      k = j + 1 ∧ a ≠ b ∧ Live false target j T ∧
      bin 1 (pins.getD a.val zero) (pins.getD b.val zero) ∈ T ∧
      ∀ v ∈ T, v ∈ pins ++ [bin 1 (pins.getD a.val zero) (pins.getD b.val zero)] := by
  by_cases large : L + 3 ≤ k
  · exact Or.inl large
  · right
    obtain ⟨j,a,b,d,T,hk,ha,hb,hab,hd,ht,he,hr⟩ := first_proper_binary_mode run raw
    have hlist : List.ofFn (fun i : Fin 10 => pins.getD i.val zero) = pins := rfl
    rw [←hlist] at ha hb
    obtain ⟨ia,rfl⟩ := List.mem_ofFn.mp ha
    obtain ⟨ib,rfl⟩ := List.mem_ofFn.mp hb
    have indices : ia ≠ ib := fun eq => hab (congrArg (fun i : Fin 10 => pins.getD i.val zero) eq)
    have dlt : d < 2 := by simpa [Extended.allowed] using hd
    have hone : d = 1 := by
      by_contra hne
      have hz : d = 0 := by omega
      subst d
      have lower := and_bank_lower floor ia ib indices ht hr
      omega
    subst d
    exact ⟨j,ia,ib,T,hk,indices,ht,he,hr⟩

end PEqualNP.Outside.L_meta_1886_aux.ModeFloor
