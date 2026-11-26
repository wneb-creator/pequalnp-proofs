import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_5968_73
    (smallU : ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (C : Circuit) (d e : ℕ) (S : Finset (Fin 11)),
      G = edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] →
      IsLeastAO G C → TopForm G C → C.size < 22 → junk G C = {d, e} →
      (Ustar G C).card = 2 →
      IsMinCover (G.deleteEdges ↑(Ustar G C)) S →
      5 ≤ S.card →
      centreless G C = ∅ →
      S.card + (orN G C \ lam G C).card ≤ 6 →
      False)
    (dirtyLarge : ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (C : Circuit) (d e : ℕ) (S : Finset (Fin 11)),
      G = edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] →
      IsLeastAO G C → TopForm G C → C.size < 22 → junk G C = {d, e} →
      let A := fun k => (gammaE G C k).filter fun h => ∃ z ∈ wmax G C k, z ∈ h
      let U := Ustar G C
      3 ≤ U.card →
      IsMinCover (G.deleteEdges ↑U) S →
      7 ≤ S.card + U.card →
      S.card + 2 * (centreless G C).card + (orN G C \ lam G C).card ≤ 4 + U.card →
      (∃ x : Fin 11 → Bool, gateVal 11 C d x = true ∧ gateVal 11 C e x = true ∧ graphFun G ∅ x = false) →
      (wmax G C d ∩ wmax G C e).Nonempty →
      (A d).card ≤ 7 → (A e).card ≤ 7 →
      (∀ h ∈ U, h ∈ A d ∨ h ∈ A e) →
      False)
    (safeLarge : ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (C : Circuit) (d e : ℕ) (S : Finset (Fin 11)),
      G = edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] →
      IsLeastAO G C → TopForm G C → C.size < 22 → junk G C = {d, e} → d ≠ e →
      let A := fun k => (gammaE G C k).filter fun h => ∃ z ∈ wmax G C k, z ∈ h
      let both := gammaE G C d ∩ gammaE G C e
      let U := Ustar G C
      3 ≤ U.card →
      IsMinCover (G.deleteEdges ↑U) S →
      7 ≤ S.card + U.card →
      S.card + 2 * (centreless G C).card + (orN G C \ lam G C).card ≤ 4 + U.card →
      (∀ x : Fin 11 → Bool, gateVal 11 C d x = true → gateVal 11 C e x = true → graphFun G ∅ x = true) →
      (A d).card ≤ 7 → (A e).card ≤ 7 → both.card ≤ 8 →
      (∀ h ∈ U, h ∈ A d ∨ h ∈ A e ∨ h ∈ both) →
      False) :
    (∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),   x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         x3.size < (22 : ℕ) →           PEqualNP.TopForm.junk x1 x3 = {x4, x5} →             have x11 : ℕ → Finset (Sym2 (Fin (11 : ℕ))) := fun (x11 : ℕ) => {x12 ∈ PEqualNP.TopForm.gammaE x1 x3 x11 | ∃ x13 ∈ PEqualNP.TopForm.wmax x1 x3 x11, x13 ∈ x12};             have x12 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.gammaE x1 x3 x4 ∩ PEqualNP.TopForm.gammaE x1 x3 x5;             have x13 : Prop := ∀ (x13 : Fin (11 : ℕ) → Bool), PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x4 x13 = Bool.true → PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x5 x13 = Bool.true → PEqualNP.MetaComplexity.NestedCover.graphFun x1 ∅ x13 = Bool.true;             have x14 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;             (x11 x4).card ≤ (7 : ℕ) ∧ (x11 x5).card ≤ (7 : ℕ) ∧ (x13 → x12.card ≤ (8 : ℕ)) ∧ (x13 ∨ (PEqualNP.TopForm.wmax x1 x3 x4 ∩ PEqualNP.TopForm.wmax x1 x3 x5).Nonempty) → (∀ x16 ∈ x14, x16 ∈ x11 x4 ∨ x16 ∈ x11 x5 ∨ x13 ∧ x16 ∈ x12) → ∃ (x17 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x14) x17 ∧ (5 : ℕ) + x14.card ≤ x17.card + (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x3).card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card) := by
  intro G inst C d e hG hLeast hTop hSize hJunk
  dsimp only
  intro hProf hU
  classical
  let U := Ustar G C
  have hex : ∃ k : ℕ, ∃ T : Finset (Fin 11), (G.deleteEdges ↑U).IsVertexCover (T : Set (Fin 11)) ∧ T.card = k :=
    ⟨11, Finset.univ, fun _ _ _ => Or.inl (Finset.mem_coe.mpr (Finset.mem_univ _)),
      Finset.card_fin 11⟩
  obtain ⟨S, hScov, hScard⟩ := Nat.find_spec hex
  have hSmin : IsMinCover (G.deleteEdges ↑U) S :=
    ⟨hScov, fun T' hT' => hScard.symm ▸ Nat.find_min' hex ⟨T', hT', rfl⟩⟩
  refine ⟨S, hSmin, ?_⟩
  let T : Finset (Fin 11) := S ∪ U.image (fun f => (Quot.out f).1)
  have hTcov : G.IsVertexCover (T : Set (Fin 11)) := by
    intro u v huv
    by_cases hmem : s(u, v) ∈ U
    · have hmem1 : (Quot.out s(u, v)).1 ∈ s((Quot.out s(u, v)).1, (Quot.out s(u, v)).2) :=
        Sym2.mem_mk_left _ _
      rw [show s((Quot.out s(u, v)).1, (Quot.out s(u, v)).2) = s(u, v) from Quot.out_eq s(u, v)] at hmem1
      have hinc : (Quot.out s(u, v)).1 = u ∨ (Quot.out s(u, v)).1 = v := Sym2.mem_iff.mp hmem1
      have hinT : (Quot.out s(u, v)).1 ∈ T :=
        Finset.mem_union_right _ (Finset.mem_image.mpr ⟨s(u, v), hmem, rfl⟩)
      exact hinc.elim (fun h => Or.inl (h ▸ hinT)) (fun h => Or.inr (h ▸ hinT))
    · have hadj : (G.deleteEdges ↑U).Adj u v := SimpleGraph.deleteEdges_adj.mpr ⟨huv, hmem⟩
      exact (hScov hadj).elim (fun h => Or.inl (Finset.mem_union_left _ h))
        (fun h => Or.inr (Finset.mem_union_left _ h))
  let c : Fin 11 → ℕ := fun v => if v ∈ T then 1 else 0
  have hEdge : ∀ u v : Fin 11, G.Adj u v → 1 ≤ c u + c v := by
    intro u v huv
    rcases hTcov huv with hu | hv
    · have hcu : c u = 1 := ite_eq_left hu
      rw [hcu]
      exact Nat.le_add_right 1 (c v)
    · have hcv : c v = 1 := ite_eq_left hv
      rw [hcv]
      exact Nat.le_add_left 1 (c u)
  have hAdj : ∀ u v : Fin 11, u ≠ v →
      (u.val, v.val) ∈ ([(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] : List (ℕ × ℕ)) →
      G.Adj u v := by
    intro u v hne hmem
    rw [hG]
    exact ⟨hne, Or.inl hmem⟩
  have h09 := hEdge 0 9 (hAdj 0 9 (fun h => Nat.noConfusion (congrArg Fin.val h))
    (List.Mem.head _))
  have h010 := hEdge 0 10 (hAdj 0 10 (fun h => Nat.noConfusion (congrArg Fin.val h))
    (List.Mem.tail _ (List.Mem.head _)))
  have h14 := hEdge 1 4 (hAdj 1 4 (fun h => Nat.noConfusion (Nat.succ.inj (congrArg Fin.val h)))
    (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
  have h18 := hEdge 1 8 (hAdj 1 8 (fun h => Nat.noConfusion (Nat.succ.inj (congrArg Fin.val h)))
    (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
  have h25 := hEdge 2 5 (hAdj 2 5 (fun h => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj (congrArg Fin.val h))))
    (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
  have h210 := hEdge 2 10 (hAdj 2 10 (fun h => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj (congrArg Fin.val h))))
    (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
  have h36 := hEdge 3 6 (hAdj 3 6 (fun h => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj (congrArg Fin.val h)))))
    (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
  have h37 := hEdge 3 7 (hAdj 3 7 (fun h => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj (congrArg Fin.val h)))))
    (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))
  have h48 := hEdge 4 8 (hAdj 4 8 (fun h => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj (congrArg Fin.val h))))))
    (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))
  have h59 := hEdge 5 9 (hAdj 5 9 (fun h => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj (congrArg Fin.val h)))))))
    (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))
  have h67 := hEdge 6 7 (hAdj 6 7 (fun h => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj (congrArg Fin.val h))))))))
    (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))
  have hTri : ∀ a b d : ℕ, 1 ≤ a + b → 1 ≤ a + d → 1 ≤ b + d → 2 ≤ a + b + d := by
    intro a b d h1 h2 h3
    apply Nat.le_of_not_lt
    intro hlt
    have hle1 : a + b + d ≤ 1 := Nat.le_of_lt_succ hlt
    have hsum : 3 ≤ (a + b) + (a + d) + (b + d) :=
      Nat.add_le_add (Nat.add_le_add h1 h2) h3
    have heq : (a + b) + (a + d) + (b + d) = (a + b + d) + (a + b + d) := by
      ac_rfl
    have hle2 : (a + b + d) + (a + b + d) ≤ 2 := Nat.add_le_add hle1 hle1
    exact Nat.not_le_of_gt (Nat.lt_succ_self 2) (hsum.trans (heq ▸ hle2))
  have hCyc : ∀ a b d f g : ℕ, 1 ≤ a + g → 1 ≤ a + b → 1 ≤ d + b → 1 ≤ d + f → 1 ≤ f + g →
      3 ≤ a + b + d + f + g := by
    intro a b d f g h1 h2 h3 h4 h5
    apply Nat.le_of_not_lt
    intro hlt
    have hle2 : a + b + d + f + g ≤ 2 := Nat.le_of_lt_succ hlt
    have hsum : 5 ≤ (a + g) + (a + b) + (d + b) + (d + f) + (f + g) :=
      Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add h1 h2) h3) h4) h5
    have heq : (a + g) + (a + b) + (d + b) + (d + f) + (f + g) =
        (a + b + d + f + g) + (a + b + d + f + g) := by
      ac_rfl
    have hle4 : (a + b + d + f + g) + (a + b + d + f + g) ≤ 4 := Nat.add_le_add hle2 hle2
    exact Nat.not_le_of_gt (Nat.lt_succ_self 4) (hsum.trans (heq ▸ hle4))
  have hA : 2 ≤ c 1 + c 4 + c 8 := hTri (c 1) (c 4) (c 8) h14 h18 h48
  have hB : 2 ≤ c 3 + c 6 + c 7 := hTri (c 3) (c 6) (c 7) h36 h37 h67
  have hC : 3 ≤ c 0 + c 10 + c 2 + c 5 + c 9 := hCyc (c 0) (c 10) (c 2) (c 5) (c 9) h09 h010 h210 h25 h59
  have hTsum : T.card = ∑ v : Fin 11, c v := by
    rw [Finset.sum_ite, Finset.sum_const, smul_eq_mul, mul_one, Finset.sum_const, smul_eq_mul,
      mul_zero, Nat.add_zero, Finset.filter_mem_eq_inter, Finset.univ_inter]
  have hTcard : 7 ≤ T.card := by
    rw [hTsum, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
      Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
      Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_one]
    change 7 ≤ c 0 + (c 1 + (c 2 + (c 3 + (c 4 + (c 5 + (c 6 + (c 7 + (c 8 + (c 9 + c 10)))))))))
    have h7 : 7 ≤ (c 1 + c 4 + c 8) + (c 3 + c 6 + c 7) + (c 0 + c 10 + c 2 + c 5 + c 9) :=
      Nat.add_le_add (Nat.add_le_add hA hB) hC
    have hre : (c 1 + c 4 + c 8) + (c 3 + c 6 + c 7) + (c 0 + c 10 + c 2 + c 5 + c 9) =
        c 0 + (c 1 + (c 2 + (c 3 + (c 4 + (c 5 + (c 6 + (c 7 + (c 8 + (c 9 + c 10))))))))) := by
      ac_rfl
    exact hre ▸ h7
  have hTU : T.card ≤ S.card + U.card :=
    (Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_image_le _)
  have hSU : 7 ≤ S.card + U.card := hTcard.trans hTU
  by_contra hlt
  change ¬ (5 + U.card ≤ S.card + 2 * (centreless G C).card + (orN G C \ lam G C).card) at hlt
  have hDef : S.card + 2 * (centreless G C).card + (orN G C \ lam G C).card ≤ 4 + U.card :=
    Nat.le_of_lt_succ ((Nat.succ_add 4 U.card) ▸ Nat.lt_of_not_ge hlt)
  by_cases hU2 : U.card = 2
  · have h5S : 5 ≤ S.card := by
      have hSU2 : 5 + 2 ≤ S.card + 2 := by
        have h := hSU
        rw [hU2] at h
        exact h
      exact Nat.le_of_add_le_add_right hSU2
    have h6 : S.card + 2 * (centreless G C).card + (orN G C \ lam G C).card ≤ 6 := by
      have hDef2 := hDef
      rw [hU2] at hDef2
      exact hDef2
    have hZcard : (centreless G C).card = 0 := by
      apply Nat.eq_zero_of_le_zero
      apply Nat.le_of_not_lt
      intro hpos
      have h2Z : 2 ≤ 2 * (centreless G C).card := Nat.mul_le_mul_left 2 hpos
      have h7le : 7 ≤ S.card + 2 * (centreless G C).card + (orN G C \ lam G C).card :=
        (Nat.add_le_add h5S h2Z).trans (Nat.le_add_right _ _)
      exact Nat.not_le_of_gt (Nat.lt_succ_self 6) (h7le.trans h6)
    have hZ0 : centreless G C = ∅ := Finset.card_eq_zero.mp hZcard
    have hSM : S.card + (orN G C \ lam G C).card ≤ 6 := by
      rw [hZcard, Nat.mul_zero, Nat.add_zero] at h6
      exact h6
    exact smallU G C d e S hG hLeast hTop hSize hJunk hU2 hSmin h5S hZ0 hSM
  · have hU3 : 3 ≤ U.card := by
      apply Nat.le_of_not_lt
      intro hlt3
      have hle1 : U.card ≤ 1 := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hlt3) hU2)
      have hS6 : 6 ≤ S.card :=
        Nat.le_of_add_le_add_right (b := 1) (hSU.trans (Nat.add_le_add_left hle1 S.card))
      have hS5 : S.card ≤ 5 :=
        ((Nat.le_add_right S.card _).trans (Nat.le_add_right _ _)).trans
          (hDef.trans (Nat.add_le_add_left hle1 4))
      exact Nat.not_le_of_gt (Nat.lt_succ_self 5) (hS6.trans hS5)
    by_cases hSafe : ∀ x : Fin 11 → Bool, gateVal 11 C d x = true → gateVal 11 C e x = true → graphFun G ∅ x = true
    · have hde : d ≠ e := by
        intro heq
        have hd : d ∈ junk G C := by rw [hJunk]; exact Finset.mem_insert_self d {e}
        obtain ⟨_, _, _, x, hxd, hxf⟩ := Finset.mem_filter.mp hd
        have hxt : graphFun G ∅ x = true := hSafe x hxd (heq ▸ hxd)
        rw [hxt] at hxf
        exact Bool.noConfusion hxf
      exact safeLarge G C d e S hG hLeast hTop hSize hJunk hde hU3 hSmin hSU hDef hSafe
        hProf.1 hProf.2.1 (hProf.2.2.1 hSafe) (fun h hh => by
          rcases hU h hh with h1 | h2 | ⟨_, h3⟩
          · exact Or.inl h1
          · exact Or.inr (Or.inl h2)
          · exact Or.inr (Or.inr h3))
    · have hWit : ∃ x : Fin 11 → Bool, gateVal 11 C d x = true ∧ gateVal 11 C e x = true ∧ graphFun G ∅ x = false := by
        obtain ⟨x, hx⟩ := Classical.not_forall.mp hSafe
        obtain ⟨hxd, hx⟩ := Classical.not_imp.mp hx
        obtain ⟨hxe, hxf⟩ := Classical.not_imp.mp hx
        exact ⟨x, hxd, hxe, Bool.eq_false_iff.mpr hxf⟩
      have hWne : (wmax G C d ∩ wmax G C e).Nonempty := hProf.2.2.2.resolve_left hSafe
      exact dirtyLarge G C d e S hG hLeast hTop hSize hJunk hU3 hSmin hSU hDef hWit hWne
        hProf.1 hProf.2.1 (fun h hh => by
          rcases hU h hh with h1 | h2 | ⟨hs, _⟩
          · exact Or.inl h1
          · exact Or.inr h2
          · exact (hSafe hs).elim)
