namespace PEqualNP.Outside.L_meta_1477.SingleCommonFilter

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
  PEqualNP.EdgeOwnership OneJunk Structural StructuralMasks MaskGrouping GeneralDirtyPairs

lemma actual_joint_cover_one {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (color : Fin n → Fin 2)
    (hcolor : ∀ u v, G.Adj u v → color u ≠ color v)
    (C : Circuit) (hAO : P2.AO n C) (g : Fin 2 → ℕ)
    (hgj : ∀ i, g i ∈ junk G C)
    (hpure : ∀ i, ∀ b : Fin 2, ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ P2.OrR n C (opnd C (g i) b) (n+k))
    (hdis : ∀ i, Disjoint (side (n := n) C (g i) 0) (side C (g i) 1))
    (htwo : ∀ i, (cleanCenters G (side (n := n) C (g i) 0) (side C (g i) 1)).card = 2) :
    ∃ J : Finset (Fin n), J.card ≤ 1 ∧ ∀ u v : Fin n,
      gateVal n C (g 0) (pairInput u v)=true → gateVal n C (g 1) (pairInput u v)=true →
      JointClean G C (g 0) (g 1) → ∃ c ∈ J, c ∈ s(u,v) := by
  classical
  let A := fun i => side (n := n) C (g i) 0
  let B := fun i => side (n := n) C (g i) 1
  have hprod (i : Fin 2) := ActualCommonMasks.pure_product_value C hAO (g i)
    ((P1.junk_iff G C (g i)).mp (hgj i)).1 ((P1.junk_iff G C (g i)).mp (hgj i)).2.1 (hpure i)
  by_cases hjoint : JointClean G C (g 0) (g 1)
  · let col : Fin n → Bool := fun v => decide (color v = 0)
    have hcol : ∀ u v, G.Adj u v → col u ≠ col v := by
      intro u v huv heq
      have hne := hcolor u v huv
      dsimp only [col] at heq
      generalize hu : color u = cu at *
      generalize hv : color v = cv at *
      fin_cases cu <;> fin_cases cv <;> simp_all
    have hc (i : Fin 2) : (cleanCenters G (A i) (B i)).Nonempty :=
      Finset.card_pos.mp (by rw [htwo i]; omega)
    have hclean : ∀ u v, productValue (A 0) (B 0) (pairInput u v)=true →
        productValue (A 1) (B 1) (pairInput u v)=true → G.Adj u v := by
      intro u v h0 h1
      have hf := hjoint (pairInput u v) ((hprod 0 _).trans h0) ((hprod 1 _).trans h1)
      exact (P2.graphFun_pair G u v).mp hf
    obtain ⟨J,hJ,hcover⟩ := ProductJointCover.product_joint_cover_one G hG col hcol
      (A 0) (B 0) (A 1) (B 1) (hdis 0) (hdis 1) (hc 0) (hc 1) hclean
    refine ⟨J,hJ,?_⟩
    intro u v h0 h1 _
    exact hcover u v ((hprod 0 _).symm.trans h0) ((hprod 1 _).symm.trans h1)
  · exact ⟨∅,by simp,fun _ _ _ _ h => (hjoint h).elim⟩

lemma single_common_filter_lower_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (color : Fin n → Fin 2)
    (hcolor : ∀ u v, G.Adj u v → color u ≠ color v)
    (C : Circuit) (hL : IsLeastAO G C) (hTF : TopForm G C)
    (hne : G.edgeFinset.Nonempty) (tau : ℕ)
    (hmin : ∀ K : Finset (Fin n), G.IsVertexCover (K : Set (Fin n)) → tau ≤ K.card)
    (g : Fin 2 → ℕ) (hjunk : junk G C = {g 0,g 1}) (hneq : g 0 ≠ g 1)
    (hpure : ∀ i, ∀ b : Fin 2, ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ P2.OrR n C (opnd C (g i) b) (n+k))
    (hdis : ∀ i, Disjoint (side (n := n) C (g i) 0) (side C (g i) 1))
    (hA : ∀ i, 2 ≤ (side (n := n) C (g i) 0).card)
    (hB : ∀ i, 2 ≤ (side (n := n) C (g i) 1).card)
    (htwo : ∀ i, (cleanCenters G (side (n := n) C (g i) 0) (side C (g i) 1)).card = 2)
    (hmask : ∀ u v : Fin n, s(u,v) ∈ Ustar G C →
      ∃ i : Fin 2, ∃ c ∈ wmax G C (g i), (c=u ∨ c=v) ∧ gateVal n C (g i) (pairInput u v)=true)
    (a : ℕ) (b : Fin 2) (hcent : centreless G C = {a})
    (hempty : side (n := n) C a b = ∅)
    (hall : ∀ i : Fin 2, P2.OrR n C (opnd C a b) (n+g i)) :
    G.edgeFinset.card + tau ≤ C.size + 1 := by
  classical
  let A := fun i => side (n := n) C (g i) 0
  let B := fun i => side (n := n) C (g i) 1
  let S := Finset.univ.filter (OrdinaryFilterBudget.OrdinaryActive G C)
  have hreader : ∀ c ∈ S, OrdinaryFilterBudget.OrdinaryActive G C c :=
    fun _ hc => (Finset.mem_filter.mp hc).2
  have hAO := P2.ao_of n C hL.1
  have hgj (i : Fin 2) : g i ∈ junk G C := by fin_cases i <;> rw [hjunk] <;> simp
  have hroots (i : Fin 2) (b : Fin 2) : opnd C (g i) b < n + C.gates.length := by
    have hg := (P1.junk_iff G C (g i)).mp (hgj i)
    have hh := P2.opnd_lt n C hAO (g i) hg.1 (opnd C (g i)) (P2.opnd_eq n C hAO (g i) hg.1) b
    omega
  have hcover := MaskedFamilyLowerBound.masked_ustar_cover G C hAO g hgj hpure hdis hmask
  have hsub : Ustar G C ⊆ MaskAllCenters.allStars G A B \ PEqualNP.TopForm.starEdges G C := by
    intro e he
    obtain ⟨hnot,i,c,hc,hstar⟩ := hcover e he
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,
      Finset.mem_biUnion.mpr ⟨c,hc,hstar⟩⟩,hnot⟩
  have hUcard := Finset.card_le_card hsub
  have hac : a ∈ centreless G C := by rw [hcent]; simp
  have hatop : a ∈ tops G C := (Finset.mem_filter.mp hac).1
  let f := opnd C a (1-b)
  have hfilter : f < n+C.gates.length := by
    have halen := Finset.mem_range.mp ((P2.mem_filter' _ _ _ _).mp hatop).1
    have hlt := P2.opnd_lt n C hAO a halen (opnd C a) (P2.opnd_eq n C hAO a halen) (1-b)
    dsimp [f]
    omega
  have hcommon : ∀ i, ∀ q ∈ orIn n C f, CleanMask G (A i) (B i) q := by
    intro i q hq
    have hg := (P1.junk_iff G C (g i)).mp (hgj i)
    exact ActualCommonMasks.top_common_masks G C hAO (g i) hg.1 hg.2.1 (hpure i) a hatop b (hall i) q hq
  let R := EligibleFamilyBudget.activeCenters G C A B f
  have hbudget := EligibleFamilyBudget.common_all_centers_ordinary_budget G hG color hcolor C hL
    A B hdis hA hB (fun i => opnd C (g i) 0) (fun i => opnd C (g i) 1)
    (fun i => hroots i 0) (fun i => hroots i 1) (fun i => hpure i 0) (fun i => hpure i 1)
    (fun _ => rfl) (fun _ => rfl) htwo f hfilter hcommon S hreader
  obtain ⟨T,hST,hTcard,hTcover⟩ := OrdinaryJointCoverage.eligible_cover_including_centers G C A B (S ∪ R)
  obtain ⟨J,hJcard,hJcover⟩ := actual_joint_cover_one G hG color hcolor C hAO g hgj hpure hdis htwo
  have htotal : ∀ e ∈ Ustar G C, ∃ c ∈ T ∪ J, c ∈ e := by
    intro e
    induction e using Sym2.inductionOn with
    | _ u v =>
      intro he
      have hnot := (Finset.mem_sdiff.mp he).2
      rcases OrdinaryJointCoverage.eligible_or_centreless_or_joint G hG C hL hTF g hjunk hneq
        hpure hdis hA hB htwo u v he with hm | hj
      · obtain ⟨i,c,hc,hstar,hcase⟩ := hm
        have hgood : i ∈ EligibleFamilyBudget.boundaryProducts G C A B ∨ c ∈ S ∪ R := by
          rcases hcase with hi | hactive | ⟨ac,hac,d,hcd,hr⟩
          · exact Or.inl hi
          · exact Or.inr (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hactive⟩))
          · have heq : ac=a := by simpa only [hcent,Finset.mem_singleton] using hac
            subst ac
            have hdb : d=b := by
              fin_cases b <;> fin_cases d
              · rfl
              · have hc0 : c ∈ side (n := n) C a 0 := by simpa using hcd
                have he0 : side (n := n) C a 0 = ∅ := by simpa using hempty
                rw [he0] at hc0
                exact (Finset.notMem_empty c hc0).elim
              · have hc1 : c ∈ side (n := n) C a 1 := by simpa using hcd
                have he1 : side (n := n) C a 1 = ∅ := by simpa using hempty
                rw [he1] at hc1
                exact (Finset.notMem_empty c hc1).elim
              · rfl
            subst d
            by_cases hi : i ∈ EligibleFamilyBudget.boundaryProducts G C A B
            · exact Or.inl hi
            · right
              apply Finset.mem_union_right
              change c ∈ Finset.univ.biUnion (fun j : Fin 2 =>
                if j ∈ EligibleFamilyBudget.boundaryProducts G C A B then ∅
                else cleanCenters G (A j) (B j) ∩ orIn n C f)
              apply Finset.mem_biUnion.mpr
              refine ⟨i,Finset.mem_univ _,?_⟩
              rw [if_neg hi]
              exact Finset.mem_inter.mpr ⟨hc,hcd⟩
        obtain ⟨v,hv,hve⟩ := hTcover _ hnot ⟨i,c,hc,hstar,hgood⟩
        exact ⟨v,Finset.mem_union_left _ hv,hve⟩
      · obtain ⟨ac,hac,d,h0,h1,hjoint,_,_⟩ := hj
        obtain ⟨c,hc,hce⟩ := hJcover u v h0 h1 hjoint
        exact ⟨c,Finset.mem_union_right _ hc,hce⟩
  have hSR := Finset.card_union_le S R
  have hTJ := Finset.card_union_le T J
  have hpaid : (Ustar G C).card + (T ∪ J).card ≤ (orN G C \ lam G C).card + 4 := by
    change (MaskAllCenters.allStars G A B \ PEqualNP.TopForm.starEdges G C).card +
      (EligibleFamilyBudget.boundaryProducts G C A B).card + R.card + S.card ≤
      (orN G C \ lam G C).card + 2 + 1 at hbudget
    omega
  have hfinal := CommonFamilyAccounting.accounting_paid_cover_general G hG C hL hTF hne tau 4 hmin
    (T ∪ J) htotal hpaid
  have hc : (centreless G C).card=1 := by rw [hcent];simp
  have hj : (junk G C).card=2 := by rw [hjunk];simp[hneq]
  omega

end PEqualNP.Outside.L_meta_1477.SingleCommonFilter
