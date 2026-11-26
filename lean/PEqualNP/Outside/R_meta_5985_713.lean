import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.BicliqueBlockCost in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_5985_713
    (extractBlocks :
      let G := PEqualNP.EdgeOwnership.edgeGraph 26 [(1, 14), (1, 18), (1, 24), (2, 14), (2, 15), (2, 19), (2, 25), (3, 15), (3, 16), (3, 20), (4, 14), (4, 16), (4, 17), (4, 21), (5, 15), (5, 17), (5, 18), (5, 22), (6, 16), (6, 18), (6, 19), (6, 23), (7, 17), (7, 19), (7, 20), (7, 24), (8, 18), (8, 20), (8, 21), (8, 25), (9, 19), (9, 21), (9, 22), (10, 14), (10, 20), (10, 22), (10, 23), (11, 15), (11, 21), (11, 23), (11, 24), (12, 16), (12, 22), (12, 24), (12, 25)]
      ∀ (C : Circuit), Monotone2 C →
        (∀ x : Fin 26 → Bool, x 0 = false → x 13 = false →
          (C.eval (List.ofFn x) = true ↔
            ∃ u v : Fin 26, G.Adj u v ∧ x u = true ∧ x v = true)) →
        HasBlockCost G C.size)
    (countStars :
      let G := PEqualNP.EdgeOwnership.edgeGraph 26 [(1, 14), (1, 18), (1, 24), (2, 14), (2, 15), (2, 19), (2, 25), (3, 15), (3, 16), (3, 20), (4, 14), (4, 16), (4, 17), (4, 21), (5, 15), (5, 17), (5, 18), (5, 22), (6, 16), (6, 18), (6, 19), (6, 23), (7, 17), (7, 19), (7, 20), (7, 24), (8, 18), (8, 20), (8, 21), (8, 25), (9, 19), (9, 21), (9, 22), (10, 14), (10, 20), (10, 22), (10, 23), (11, 15), (11, 21), (11, 23), (11, 24), (12, 16), (12, 22), (12, 24), (12, 25)]
      ∀ (F : Finset (Block 26)), IsBlockCover G F →
        (∀ p ∈ F, p.1.card ≤ 1 ∨ p.2.card ≤ 1) →
        ∃ S : Finset (Fin 26), CoverPromise.IsVertexCover G S ∧
          G.edgeFinset.card + S.card ≤ familyCost F + 1) :
    (have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → (∀ (x4 : Fin (26 : ℕ) → Bool), x4 (0 : Fin (26 : ℕ)) = Bool.false → x4 (13 : Fin (26 : ℕ)) = Bool.false → (x2.eval (List.ofFn x4) = Bool.true ↔ ∃ (x7 : Fin (13 : ℕ)) (x8 : Fin (13 : ℕ)), x1 x7 x8 ∧ x4 (Fin.castAdd (13 : ℕ) x7) = Bool.true ∧ x4 (Fin.natAdd (13 : ℕ) x8) = Bool.true)) → (56 : ℕ) ≤ x2.size) := by
  let incidence := fun p l : Fin 13 => p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
  change ∀ C : Circuit, Monotone2 C → (∀ x : Fin 26 → Bool, x 0 = false → x 13 = false →
    (C.eval (List.ofFn x) = true ↔ ∃ p l : Fin 13, incidence p l ∧
      x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true)) → 56 ≤ C.size
  intro C mono specified
  let G := PEqualNP.EdgeOwnership.edgeGraph 26 [(1, 14), (1, 18), (1, 24), (2, 14), (2, 15), (2, 19), (2, 25), (3, 15), (3, 16), (3, 20), (4, 14), (4, 16), (4, 17), (4, 21), (5, 15), (5, 17), (5, 18), (5, 22), (6, 16), (6, 18), (6, 19), (6, 23), (7, 17), (7, 19), (7, 20), (7, 24), (8, 18), (8, 20), (8, 21), (8, 25), (9, 19), (9, 21), (9, 22), (10, 14), (10, 20), (10, 22), (10, 23), (11, 15), (11, 21), (11, 23), (11, 24), (12, 16), (12, 22), (12, 24), (12, 25)]
  have square : ∀ p l : Fin 13, G.Adj (Fin.castAdd 13 p) (Fin.natAdd 13 l) ↔
      p ≠ 0 ∧ l ≠ 0 ∧ incidence p l := by
    decide +kernel
  have noLeft : ∀ p q : Fin 13, ¬ G.Adj (Fin.castAdd 13 p) (Fin.castAdd 13 q) := by
    decide +kernel
  have noRight : ∀ p q : Fin 13, ¬ G.Adj (Fin.natAdd 13 p) (Fin.natAdd 13 q) := by
    decide +kernel
  have port : ∀ u v : Fin 26, G.Adj u v →
      ∃ p l : Fin 13, incidence p l ∧
        ((u = Fin.castAdd 13 p ∧ v = Fin.natAdd 13 l) ∨
         (u = Fin.natAdd 13 l ∧ v = Fin.castAdd 13 p)) := by
    intro u v
    refine Fin.addCases (m := 13) (n := 13) (fun p => ?_) (fun l => ?_) u <;>
      refine Fin.addCases (m := 13) (n := 13) (fun p' => ?_) (fun l' => ?_) v <;> intro e
    · exact False.elim (noLeft p p' e)
    · exact ⟨p, l', ((square p l').mp e).2.2, Or.inl ⟨rfl,rfl⟩⟩
    · exact ⟨p', l, ((square p' l).mp e.symm).2.2, Or.inr ⟨rfl,rfl⟩⟩
    · exact False.elim (noRight l l' e)
  have graphCorrect : ∀ x : Fin 26 → Bool, x 0 = false → x 13 = false →
      (C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin 26, G.Adj u v ∧ x u = true ∧ x v = true) := by
    intro x pinLeft pinRight
    rw [specified x pinLeft pinRight]
    constructor
    · rintro ⟨p, l, e, hp, hl⟩
      have pNot : p ≠ 0 := by rintro rfl; exact Bool.noConfusion (pinLeft.symm.trans hp)
      have lNot : l ≠ 0 := by rintro rfl; exact Bool.noConfusion (pinRight.symm.trans hl)
      exact ⟨_, _, (square p l).mpr ⟨pNot,lNot,e⟩, hp, hl⟩
    · rintro ⟨u,v,e,hu,hv⟩
      obtain ⟨p,l,edge,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ := port u v e
      · exact ⟨p,l,edge,hu,hv⟩
      · exact ⟨p,l,edge,hv,hu⟩
  obtain ⟨F, fc, cost⟩ := extractBlocks C mono graphCorrect
  have c4 : PEqualNP.TopForm.NoFourCycle G := by
    intro a
    fin_cases a <;> decide +kernel
  have stars : ∀ p ∈ F, p.1.card ≤ 1 ∨ p.2.card ≤ 1 := by
    intro p hp
    by_contra! wide
    obtain ⟨a,b,ha,hb,ab⟩ := Finset.one_lt_card_iff.mp wide.1
    obtain ⟨c,d,hc,hd,cd⟩ := Finset.one_lt_card_iff.mp wide.2
    have edges := (fc.1 p hp).2.2.2
    have allC : c ∈ (Finset.univ.filter fun w => G.Adj a w ∧ G.Adj b w) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,edges a ha c hc,edges b hb c hc⟩
    have allD : d ∈ (Finset.univ.filter fun w => G.Adj a w ∧ G.Adj b w) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,edges a ha d hd,edges b hb d hd⟩
    exact cd (Finset.card_le_one.mp (c4 a b ab) c allC d allD)
  obtain ⟨S, cover, accounted⟩ := countStars F fc stars
  let lhs : Fin 12 → Fin 26 := fun i =>
    ⟨i.val + 1, Nat.lt_trans (Nat.add_lt_add_right i.isLt 1) (by decide : 12 + 1 < 26)⟩
  let rhs : Fin 12 → Fin 26 := fun i => ⟨i.val + 14, Nat.add_lt_add_right i.isLt 14⟩
  have matched : ∀ i : Fin 12, G.Adj (lhs i) (rhs i) := by decide +kernel
  let pick : Fin 12 → Fin 26 := fun i => if lhs i ∈ S then lhs i else rhs i
  have each (i : Fin 12) : pick i ∈ S := by
    by_cases left : lhs i ∈ S
    · simp [pick,left]
    · have right := (cover _ _ (matched i)).resolve_left left
      simpa [pick,left] using right
  have oneToOne : Function.Injective pick := by
    intro i j eq
    have value := congrArg Fin.val eq
    have ib := i.isLt
    have jb := j.isLt
    apply Fin.ext
    by_cases h : lhs i ∈ S <;> by_cases k : lhs j ∈ S <;>
      simp [pick,h,k,lhs,rhs] at value <;> omega
  have bound : 12 ≤ S.card := by
    have inS : Finset.univ.image pick ⊆ S := by
      intro u hit
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hit
      exact each i
    have count := Finset.card_le_card inS
    rw [Finset.card_image_of_injective _ oneToOne] at count
    simpa using count
  have graphSize : G.edgeFinset.card = 45 := by decide +kernel
  rw [graphSize] at accounted
  omega
