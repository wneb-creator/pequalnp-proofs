import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
set_option maxHeartbeats 3000000 in
set_option maxRecDepth 4000 in
theorem PEqualNP.Outside.R_meta_8071_427
    (disjointCharge :
      let G := edgeGraph 11 (([9,10,15,19,27,32,39,40,52,54,63,64,73,76,86,97] : List ℕ).map (fun k => (k/11,k%11)))
      ∀ (C : Circuit) (T : Finset (Sym2 (Fin 11))) (K : Finset ℕ),
      let U := Ustar G C
      let J := junk G C
      let F := fun a => T ∩ gammaE G C a
      let pay := 2 * (centreless G C).card + (orN G C \ lam G C).card
      C.size ≤ 21 → IsLeastAO G C → TopForm G C →
      (∃ a ∈ J, ∃ b ∈ J, a ≠ b ∧ ¬ InCone 11 C a b ∧ ¬ InCone 11 C b a) →
      U ⊆ J.biUnion (gammaE G C) → T ⊆ U → K ⊆ J →
      T.card + J.card = U.card + K.card → T = K.biUnion F →
      (∀ a ∈ K, 2 ≤ (F a).card) →
      (∀ a ∈ K, ∀ b ∈ K, a ≠ b → Disjoint (F a) (F b)) →
      ∑ a ∈ K, ((F a).card - 1) ≤ pay)
    (sharedCharge :
      let G := edgeGraph 11 (([9,10,15,19,27,32,39,40,52,54,63,64,73,76,86,97] : List ℕ).map (fun k => (k/11,k%11)))
      ∀ (C : Circuit) (T : Finset (Sym2 (Fin 11))) (K : Finset ℕ),
      let U := Ustar G C
      let J := junk G C
      let F := fun a => T ∩ gammaE G C a
      let pay := 2 * (centreless G C).card + (orN G C \ lam G C).card
      C.size ≤ 21 → IsLeastAO G C → TopForm G C →
      (∃ a ∈ J, ∃ b ∈ J, a ≠ b ∧ ¬ InCone 11 C a b ∧ ¬ InCone 11 C b a) →
      U ⊆ J.biUnion (gammaE G C) → T ⊆ U → K ⊆ J →
      T.card + J.card = U.card + K.card → T = K.biUnion F →
      (∀ e ∈ T, ∃ f : K ↪ Sym2 (Fin 11), ∀ a : K, f a ∈ (F a.val).erase e) →
      (∃ a ∈ K, ∃ b ∈ K, a ≠ b ∧ (F a ∩ F b).Nonempty) →
      T.card ≤ K.card + pay) :
    (let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), x2.size ≤ (21 : ℕ) → PEqualNP.TopForm.IsLeastAO x1 x2 → PEqualNP.TopForm.TopForm x1 x2 → (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card → (∃ (x7 : ℕ) (x8 : ℕ), x7 ∈ PEqualNP.TopForm.junk x1 x2 ∧ x8 ∈ PEqualNP.TopForm.junk x1 x2 ∧ x7 ≠ x8 ∧ ¬PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 x7 x8 ∧ ¬PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 x8 x7) → (∀ (x8 x9 : Fin (11 : ℕ)), s(x8, x9) ∈ PEqualNP.TopForm.Ustar x1 x2 → ∃ x11 ∈ PEqualNP.TopForm.junk x1 x2, PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x2 x11 (PEqualNP.EdgeOwnership.pairInput x8 x9) = Bool.true) → (3 : ℕ) ≤ (PEqualNP.TopForm.Ustar x1 x2).card → (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card → (PEqualNP.TopForm.Ustar x1 x2).card ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card) := by
  classical
  intro G C size least top many pair covered three _tight
  obtain ⟨a,b,ha,hb,ne,h1,h2⟩ := pair
  let U := Ustar G C
  let J := junk G C
  let pay := 2 * (centreless G C).card + (orN G C \ lam G C).card
  have inc : ∃ a ∈ J, ∃ b ∈ J, a ≠ b ∧ ¬ InCone 11 C a b ∧ ¬ InCone 11 C b a :=
    ⟨a,ha,b,hb,ne,h1,h2⟩
  have cov : U ⊆ J.biUnion (gammaE G C) := by
    intro e he
    induction e using Sym2.ind with
    | _ x y =>
      obtain ⟨g,hg,hit⟩ := covered x y he
      exact Finset.mem_biUnion.mpr ⟨g,hg,Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp he).1,x,y,rfl,hit⟩⟩
  suffices U.card ≤ J.card + pay by
    dsimp [U,J,pay] at this
    omega
  by_contra! bad
  let feat (T : Finset (Sym2 (Fin 11))) (K : Finset ℕ) :=
    T ⊆ U ∧ K ⊆ J ∧ T.card + J.card = U.card + K.card ∧ T ⊆ K.biUnion (gammaE G C)
  let sizes (n : ℕ) := ∃ T K, feat T K ∧ T.card = n
  have anySize : ∃ n, sizes n := ⟨U.card,U,J,⟨Finset.Subset.rfl,Finset.Subset.rfl,rfl,cov⟩,rfl⟩
  obtain ⟨T,K,⟨tu,kj,bal,covers⟩,minT⟩ := Nat.find_spec anySize
  let F (g : ℕ) := T ∩ gammaE G C g
  have lives (g : ℕ) : F g ⊆ T := Finset.inter_subset_left
  have eq : T = K.biUnion F := by
    apply Finset.Subset.antisymm
    · intro e he
      obtain ⟨g,hg,hit⟩ := Finset.mem_biUnion.mp (covers he)
      exact Finset.mem_biUnion.mpr ⟨g,hg,Finset.mem_inter.mpr ⟨he,hit⟩⟩
    · intro e he
      obtain ⟨g,_,hit⟩ := Finset.mem_biUnion.mp he
      exact lives g hit
  have excess : K.card + pay < T.card := by omega
  have tight (S : Finset ℕ) (hS : S ⊆ K) (hn : S.Nonempty) : S.card < (S.biUnion F).card := by
    by_contra! small
    let D := S.biUnion F
    have dt : D ⊆ T := by
      intro e he
      obtain ⟨g,_,hf⟩ := Finset.mem_biUnion.mp he
      exact lives g hf
    have enlarged : ∃ X : Finset (Sym2 (Fin 11)), D ⊆ X ∧ X ⊆ T ∧ X.Nonempty ∧ X.card ≤ S.card := by
      by_cases nz : D.Nonempty
      · exact ⟨D,Finset.Subset.rfl,dt,nz,small⟩
      · have emp := Finset.not_nonempty_iff_eq_empty.mp nz
        obtain ⟨e,he⟩ := Finset.card_pos.mp (show 0 < T.card by omega)
        refine ⟨{e},by simp [emp],Finset.singleton_subset_iff.mpr he,Finset.singleton_nonempty _,?_⟩
        simpa using Finset.card_pos.mpr hn
    obtain ⟨X,dx,xt,xn,xc⟩ := enlarged
    obtain ⟨H,hs,hnc⟩ := Finset.exists_subset_card_eq xc
    have hk := hs.trans hS
    have shrunk : feat (T \ X) (K \ H) := by
      refine ⟨Finset.sdiff_subset.trans tu,Finset.sdiff_subset.trans kj,?_,?_⟩
      · rw [Finset.card_sdiff_of_subset xt,Finset.card_sdiff_of_subset hk]
        have := Finset.card_le_card xt
        have := Finset.card_le_card hk
        omega
      · intro e he
        obtain ⟨et,ex⟩ := Finset.mem_sdiff.mp he
        obtain ⟨g,gk,hit⟩ := Finset.mem_biUnion.mp (covers et)
        refine Finset.mem_biUnion.mpr ⟨g,Finset.mem_sdiff.mpr ⟨gk,?_⟩,hit⟩
        intro gh
        exact ex (dx (Finset.mem_biUnion.mpr ⟨g,hs gh,Finset.mem_inter.mpr ⟨et,hit⟩⟩))
    have h := Nat.find_min' anySize (show sizes (T \ X).card from ⟨_,_,shrunk,rfl⟩)
    rw [Finset.card_sdiff_of_subset xt] at h
    have := Finset.card_pos.mpr xn
    have := Finset.card_le_card xt
    omega
  have two (g : ℕ) (hg : g ∈ K) : 2 ≤ (F g).card := by
    have h : 1 < (F g).card := by simpa using tight {g} (Finset.singleton_subset_iff.mpr hg) (Finset.singleton_nonempty _)
    omega
  have robust (e : Sym2 (Fin 11)) (_he : e ∈ T) :
      ∃ f : K ↪ Sym2 (Fin 11), ∀ a : K, f a ∈ (F a.val).erase e := by
    obtain ⟨f,inj,hit⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' (fun a : K => (F a).erase e)).mp (by
      intro S
      by_cases sn : S.Nonempty
      · let V := S.image (fun a : K => a.val)
        have vs : V ⊆ K := by
          intro g hg
          obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hg
          exact x.property
        have vn : V.Nonempty := sn.image _
        have vc : V.card = S.card := Finset.card_image_of_injective _ Subtype.val_injective
        have lt := tight V vs vn
        have cut : S.biUnion (fun a : K => (F a).erase e) = (V.biUnion F).erase e := by
          ext x
          constructor
          · intro hx
            obtain ⟨v,hv,hx⟩ := Finset.mem_biUnion.mp hx
            obtain ⟨ne,hit⟩ := Finset.mem_erase.mp hx
            exact Finset.mem_erase.mpr ⟨ne, Finset.mem_biUnion.mpr ⟨v.val, Finset.mem_image_of_mem _ hv,hit⟩⟩
          · intro hx
            obtain ⟨ne,hx⟩ := Finset.mem_erase.mp hx
            obtain ⟨g,hg,hit⟩ := Finset.mem_biUnion.mp hx
            obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hg
            exact Finset.mem_biUnion.mpr ⟨v,hv,Finset.mem_erase.mpr ⟨ne,hit⟩⟩
        rw [cut]
        by_cases h : e ∈ V.biUnion F
        · rw [Finset.card_erase_of_mem h]
          omega
        · rw [Finset.erase_eq_of_notMem h]; omega
      · simp [Finset.not_nonempty_iff_eq_empty.mp sn])
    exact ⟨⟨f,inj⟩,hit⟩
  by_cases ov : ∃ a ∈ K, ∃ b ∈ K, a ≠ b ∧ (F a ∩ F b).Nonempty
  · have h := sharedCharge C T K size least top inc cov tu kj bal eq robust ov
    exact (Nat.not_le.mpr excess) h
  · have dis (a : ℕ) (ha : a ∈ K) (b : ℕ) (hb : b ∈ K) (ne : a ≠ b) : Disjoint (F a) (F b) := by
      apply Finset.disjoint_left.mpr
      intro e hea heb
      exact ov ⟨a,ha,b,hb,ne,e,Finset.mem_inter.mpr ⟨hea,heb⟩⟩
    have charge := disjointCharge C T K size least top inc cov tu kj bal eq two dis
    have exactSum : T.card = ∑ g ∈ K, (F g).card := by
      rw [eq,Finset.card_biUnion (fun i hi j hj hne => dis i hi j hj hne)]
    have split : (∑ g ∈ K, (F g).card) = (∑ g ∈ K, ((F g).card-1)) + K.card := by
      calc
        _ = ∑ g ∈ K, (((F g).card-1) + 1) := by
          apply Finset.sum_congr rfl; intro g hg; have := two g hg; omega
        _ = _ := by simp [Finset.sum_add_distrib]
    change (∑ g ∈ K, ((F g).card-1)) ≤ pay at charge
    omega
