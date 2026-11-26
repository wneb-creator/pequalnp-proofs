import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_9012_347 :
(∀ (n k o : ℕ) (f : ℕ → (Fin n → Bool) → Bool), o < n+k →
  (∀ i < n, ∃ j : Fin n, ∀ x, f i x = x j) →
  (∀ i < k, ∃ a < n+i, ∃ b < n+i,
    (∀ x, f (n+i) x = (f a x && f b x)) ∨ (∀ x, f (n+i) x = (f a x || f b x))) →
  ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ k ∧ ∀ x, C.eval (List.ofFn x) = f o x) →
(∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C →
  let read := fun (V : Finset (Fin 13 ⊕ Fin 13)) =>
    C.eval (List.ofFn fun i : Fin (13+13) => decide (finSumFinEquiv.symm i ∉ V))
  (∀ Q ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3, read (PEqualNP.HeptadCover.supp PEqualNP.HeptadCover.singerLines3 Q) = true) →
  (∀ p ∈ PEqualNP.HeptadCover.incidences PEqualNP.HeptadCover.singerLines3, read {Sum.inl p.1, Sum.inr p.2} = false) →
  64 ≤ C.size) →
(∀ (x1 x2 : ℕ) (x3 : ℕ → Finset (Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ)))), x2 < (26 : ℕ) + x1 → (∀ x5 < (26 : ℕ), ∃ (x7 : Fin (13 : ℕ) ⊕ Fin (13 : ℕ)), x3 x5 = {Finset.univ.erase x7}) → (∀ x6 < x1, ∃ x8 < (26 : ℕ) + x6, ∃ x9 < (26 : ℕ) + x6, x3 ((26 : ℕ) + x6) = x3 x8 ∪ x3 x9 ∨ x3 ((26 : ℕ) + x6) = Finset.image₂ (fun (x10 x11 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))) => x10 ∩ x11) (x3 x8) (x3 x9)) → (∀ x7 ∈ x3 x2, PEqualNP.HeptadCover.IsFree (PEqualNP.HeptadCover.incidences PEqualNP.HeptadCover.singerLines3) x7) → (∀ x8 ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3, PEqualNP.HeptadCover.supp PEqualNP.HeptadCover.singerLines3 x8 ∈ x3 x2) → (64 : ℕ) ≤ x1) := by
  classical
  intro compile bound k o A ho init step safe full
  let e : Fin 13 ⊕ Fin 13 ≃ Fin (13+13) := finSumFinEquiv
  let missing (x : Fin (13+13) → Bool) := Finset.univ.filter (fun v : Fin 13 ⊕ Fin 13 => x (e v) = false)
  let f (i : ℕ) (x : Fin (13+13) → Bool) := decide (∃ U ∈ A i, missing x ⊆ U)
  have start : ∀ i < 26, ∃ j : Fin 26, ∀ x, f i x = x j := by
    intro i hi
    obtain ⟨v,hv⟩ := init i hi
    refine ⟨e v, fun x => ?_⟩
    apply Bool.eq_iff_iff.mpr
    simp [f,hv,Finset.subset_erase,missing]
  have run : ∀ i < k, ∃ a < 26+i, ∃ b < 26+i,
      (∀ x, f (26+i) x = (f a x && f b x)) ∨ (∀ x, f (26+i) x = (f a x || f b x)) := by
    intro i hi
    obtain ⟨a,ha,b,hb,hop⟩ := step i hi
    refine ⟨a,ha,b,hb,?_⟩
    rcases hop with hor | hand
    · right
      intro x
      apply Bool.eq_iff_iff.mpr
      simp only [f, hor, Bool.or_eq_true, decide_eq_true_eq, Finset.mem_union]
      constructor
      · rintro ⟨U,hu,h⟩
        rcases hu with hua | hub
        · exact Or.inl ⟨U,hua,h⟩
        · exact Or.inr ⟨U,hub,h⟩
      · rintro (⟨U,hu,h⟩ | ⟨U,hu,h⟩)
        · exact ⟨U,Or.inl hu,h⟩
        · exact ⟨U,Or.inr hu,h⟩
    · left
      intro x
      apply Bool.eq_iff_iff.mpr
      simp only [f, hand, Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨U,mem,h⟩
        obtain ⟨V,hv,W,hw,rfl⟩ := Finset.mem_image₂.mp mem
        exact ⟨⟨V,hv,h.trans Finset.inter_subset_left⟩,⟨W,hw,h.trans Finset.inter_subset_right⟩⟩
      · rintro ⟨⟨V,hv,sv⟩,⟨W,hw,sw⟩⟩
        exact ⟨V ∩ W,Finset.mem_image₂_of_mem hv hw,Finset.subset_inter sv sw⟩
  obtain ⟨C,mono,sz,real⟩ := compile 26 k o f ho start run
  have probe (V : Finset (Fin 13 ⊕ Fin 13)) :
      missing (fun i => decide (e.symm i ∉ V)) = V := by
    ext v
    simp [missing]
  apply Nat.le_trans (bound C mono ?_ ?_) sz
  · intro Q hQ
    dsimp only
    rw [real]
    change decide (∃ U ∈ A o, missing (fun i => decide (e.symm i ∉ _)) ⊆ U) = true
    rw [probe, decide_eq_true_eq]
    exact ⟨_,full Q hQ,Finset.Subset.rfl⟩
  · intro p hp
    dsimp only
    rw [real]
    change decide (∃ U ∈ A o, missing (fun i => decide (e.symm i ∉ _)) ⊆ U) = false
    rw [probe, decide_eq_false_iff_not]
    rintro ⟨U,hu,sub⟩
    exact safe U hu p hp ⟨sub (by simp),sub (by simp)⟩
