import PEqualNP.Outside.L_meta_1024


namespace PEqualNP.Outside.L_meta_1024_aux.FourOrSinks

open PEqualNP.CircuitLowerBounds

lemma three_triples_labels (A B C : Finset (Fin 13))
    (hAcard : A.card = 3) (hBcard : B.card = 3) (hCcard : C.card = 3)
    (hAB : Disjoint A B) (hAC : (A ∩ C).card ≤ 1) (hBC : (B ∩ C).card ≤ 1)
    (label : Fin 13 → ℕ) (a b c : ℕ)
    (hA : ∀ p ∈ A, label p = a) (hB : ∀ p ∈ B, label p = b)
    (hC : ∀ p ∈ C, label p = c) :
    6 + (((A ∪ B) ∪ C).image label).card ≤ ((A ∪ B) ∪ C).card := by
  have hABcard : (A ∪ B).card = 6 := by
    rw [Finset.card_union_of_disjoint hAB, hAcard, hBcard]
  have hdisj : Disjoint (A ∩ C) (B ∩ C) :=
    hAB.mono Finset.inter_subset_left Finset.inter_subset_left
  have hinter : ((A ∪ B) ∩ C).card = (A ∩ C).card + (B ∩ C).card := by
    have he : (A ∪ B) ∩ C = (A ∩ C) ∪ (B ∩ C) := by
      ext p
      simp only [Finset.mem_inter, Finset.mem_union]
      tauto
    rw [he, Finset.card_union_of_disjoint hdisj]
  have hsum := Finset.card_union_add_card_inter (A ∪ B) C
  rw [hABcard, hCcard, hinter] at hsum
  have himage (K : Finset ℕ) (ha : a ∈ K) (hb : b ∈ K) (hc : c ∈ K) :
      (((A ∪ B) ∪ C).image label) ⊆ K := by
    intro v hv
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
    rcases Finset.mem_union.mp hp with hp | hp
    · rcases Finset.mem_union.mp hp with hp | hp
      · exact (hA p hp) ▸ ha
      · exact (hB p hp) ▸ hb
    · exact (hC p hp) ▸ hc
  by_cases ha : (A ∩ C).Nonempty
  · obtain ⟨p, hp⟩ := ha
    have hac : a = c := (hA p (Finset.mem_inter.mp hp).1).symm.trans
      (hC p (Finset.mem_inter.mp hp).2)
    by_cases hb : (B ∩ C).Nonempty
    · obtain ⟨q, hq⟩ := hb
      have hbc : b = c := (hB q (Finset.mem_inter.mp hq).1).symm.trans
        (hC q (Finset.mem_inter.mp hq).2)
      have hi := Finset.card_le_card (himage {c} (by simp [hac]) (by simp [hbc]) (by simp))
      simp only [Finset.card_singleton] at hi
      omega
    · have hb0 : (B ∩ C).card = 0 := by
        have hn : ¬ 0 < (B ∩ C).card := fun h => hb (Finset.card_pos.mp h)
        omega
      have hi := Finset.card_le_card (himage {b, c} (by simp [hac]) (by simp) (by simp))
      have hk : ({b, c} : Finset ℕ).card ≤ 2 := by
        simpa using List.toFinset_card_le [b, c]
      omega
  · have ha0 : (A ∩ C).card = 0 := by
      have hn : ¬ 0 < (A ∩ C).card := fun h => ha (Finset.card_pos.mp h)
      omega
    by_cases hb : (B ∩ C).Nonempty
    · obtain ⟨q, hq⟩ := hb
      have hbc : b = c := (hB q (Finset.mem_inter.mp hq).1).symm.trans
        (hC q (Finset.mem_inter.mp hq).2)
      have hi := Finset.card_le_card (himage {a, c} (by simp) (by simp [hbc]) (by simp))
      have hk : ({a, c} : Finset ℕ).card ≤ 2 := by
        simpa using List.toFinset_card_le [a, c]
      omega
    · have hb0 : (B ∩ C).card = 0 := by
        have hn : ¬ 0 < (B ∩ C).card := fun h => hb (Finset.card_pos.mp h)
        omega
      have hi := Finset.card_le_card (himage {a, b, c} (by simp) (by simp) (by simp))
      have hk : ({a, b, c} : Finset ℕ).card ≤ 3 := by
        simpa using List.toFinset_card_le [a, b, c]
      omega

lemma three_triples_lower (gs : List Gate) (o₁ o₂ o₃ : ℕ)
    (hg : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (A B C : Finset (Fin 13))
    (hAcard : A.card = 3) (hBcard : B.card = 3) (hCcard : C.card = 3)
    (hAB : Disjoint A B) (hAC : (A ∩ C).card ≤ 1) (hBC : (B ∩ C).card ≤ 1)
    (hA : ∀ p ∈ A, Cut.Depends 13 ∅ gs o₁ p)
    (hB : ∀ p ∈ B, Cut.Depends 13 ∅ gs o₂ p)
    (hC : ∀ p ∈ C, Cut.Depends 13 ∅ gs o₃ p) : 6 ≤ gs.length := by
  obtain ⟨label, wire, hcount, hdepends⟩ := Cut.components 13 ∅ ((A ∪ B) ∪ C) gs hg
  have hlabels := three_triples_labels A B C hAcard hBcard hCcard hAB hAC hBC
    label (wire o₁) (wire o₂) (wire o₃)
    (fun p hp => hdepends o₁ p (hA p hp))
    (fun p hp => hdepends o₂ p (hB p hp))
    (fun p hp => hdepends o₃ p (hC p hp))
  have hunpaid : Cut.unpaid 13 ∅ gs = gs.length := by
    rw [Cut.unpaid_eq_sub 13 ∅ gs (Finset.empty_subset _)]
    simp
  rw [hunpaid] at hcount
  omega

end PEqualNP.Outside.L_meta_1024_aux.FourOrSinks


namespace PEqualNP.Outside.L_meta_1024_aux.FourOrSinks

lemma four_two_ownership : ∀ (which : Fin 4 → Fin 2) (both : Fin 4 → Bool),
    (∀ a b, both a = true → both b = true → a = b) →
    ∃ a b c d : Fin 4,
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      both a = false ∧ both b = false ∧ both c = false ∧
      which a = which b ∧ d ≠ c ∧
      (both d = true ∨ which d = which c) := by
  letI (which : Fin 4 → Fin 2) (both : Fin 4 → Bool) : Decidable
      (∃ a b c d : Fin 4,
        a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
        both a = false ∧ both b = false ∧ both c = false ∧
        which a = which b ∧ d ≠ c ∧
        (both d = true ∨ which d = which c)) := by infer_instance
  decide

end PEqualNP.Outside.L_meta_1024_aux.FourOrSinks


namespace PEqualNP.Outside.L_meta_1024_aux.FourOrSinks

open PEqualNP.CircuitLowerBounds

lemma shared_parent_essential_band (a b : Fin 13) (hab : a ≠ b)
    (h k : (Fin 13 → Bool) → Bool)
    (hcorrect : ∀ x, Support.Band x → (h x || k x) = Support.target a x)
    (hupperh : ∀ x, Support.Band x → h x = true → Support.target b x = true)
    (hmono : ∀ x y, (∀ q, x q = true → y q = true) → k x = true → k y = true)
    (p : Fin 13) (hp : p ∈ Support.line a \ Support.line b) :
    ∃ x y : Fin 13 → Bool, (∀ q, q ≠ p → x q = y q) ∧ k x ≠ k y := by
  obtain ⟨hpa, hpb⟩ := Finset.mem_sdiff.mp hp
  obtain ⟨hcard, hpX, hBX, hAX⟩ := OneAnd.separating_row a b hab p hpa hpb
  let X := OneAnd.separatingRow a b p
  let x : Fin 13 → Bool := fun q => decide (q ∈ X)
  let y : Fin 13 → Bool := Function.update x p false
  have hzero : Support.zeroSet x = Finset.univ \ X := by
    ext q
    simp [Support.zeroSet, x]
  have hxband : Support.Band x := by
    apply Or.inr
    rw [hzero]
    simp [Finset.card_sdiff, show X.card = 7 from hcard]
  have hax : Support.target a x = true := by
    apply decide_eq_true
    exact ⟨p, hpa, by simp [x, X, hpX]⟩
  have hbx : Support.target b x = false := by
    simp only [Support.target, decide_eq_false_iff_not]
    rintro ⟨q, hqb, hqx⟩
    have hqX : q ∈ X := by simpa [x] using hqx
    exact Finset.disjoint_left.mp hBX hqb hqX
  have hhx : h x = false := by
    cases he : h x with
    | false => rfl
    | true =>
      have ht := hupperh x hxband he
      rw [hbx] at ht
      cases ht
  have hkx : k x = true := by
    have he := hcorrect x hxband
    simpa only [hhx, Bool.false_or, hax] using he
  let T := X.erase p
  have hTsub : T ⊆ Finset.univ \ Support.line a := by
    intro q hq
    obtain ⟨hqp, hqX⟩ := Finset.mem_erase.mp hq
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ q, fun hqa => hqp (hAX q hqa hqX)⟩
  have hTcard : T.card ≤ 8 := by
    have hle := Finset.card_le_card (Finset.erase_subset p X)
    change T.card ≤ X.card at hle
    have hc : X.card = 7 := hcard
    omega
  obtain ⟨Y, hTY, hYsub, hYcard⟩ := Clamp.extend_eight a T hTsub hTcard
  have hyY : ∀ q, y q = true → Clamp.fromTrue Y q = true := by
    intro q hyq
    apply decide_eq_true
    apply hTY
    apply Finset.mem_erase.mpr
    by_cases hqp : q = p
    · simp [y, hqp] at hyq
    · refine ⟨hqp, ?_⟩
      simpa [y, Function.update_of_ne hqp, x] using hyq
  have hky : k y = false := by
    cases he : k y with
    | false => rfl
    | true =>
      have hkY := hmono y (Clamp.fromTrue Y) hyY he
      have ht := hcorrect (Clamp.fromTrue Y) (Clamp.fromTrue_band Y hYcard)
      rw [hkY, Bool.or_true, Clamp.fromTrue_misses a Y hYsub] at ht
      cases ht
  refine ⟨x, y, ?_, ?_⟩
  · intro q hqp
    simp [y, Function.update_of_ne hqp]
  · rw [hkx, hky]
    decide

lemma shared_parent_cut_depends_band (gs : List Gate) (o : ℕ)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (a b : Fin 13) (hab : a ≠ b) (h : (Fin 13 → Bool) → Bool)
    (hcorrect : ∀ x, Support.Band x →
      (h x || Cut.cutVal 13 ∅ gs x o) = Support.target a x)
    (hupperh : ∀ x, Support.Band x → h x = true → Support.target b x = true)
    (p : Fin 13) (hp : p ∈ Support.line a \ Support.line b) :
    Cut.Depends 13 ∅ gs o p := by
  exact shared_parent_essential_band a b hab h (fun x => Cut.cutVal 13 ∅ gs x o)
    hcorrect hupperh (fun x y hxy => Cut.cutVal_mono 13 ∅ gs hg x y hxy o) p hp

end PEqualNP.Outside.L_meta_1024_aux.FourOrSinks

namespace PEqualNP.Outside.L_meta_1024_aux.FourOrSinks

open PEqualNP.CircuitLowerBounds

lemma high_network_lower_band (gs : List Gate) (out : Fin 4 → ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (lineId : Fin 4 → Fin 13) (hinj : Function.Injective lineId)
    (which : Fin 4 → Fin 2) (both : Fin 4 → Bool)
    (high : Fin 2 → (Fin 13 → Bool) → Bool)
    (f : Fin 4 → (Fin 13 → Bool) → Bool)
    (hsingle : ∀ w, both w = false → ∀ x,
      f w x = (high (which w) x || Cut.cutVal 13 ∅ gs x (out w)))
    (hdouble : ∀ w, both w = true → ∀ x,
      f w x = (high 0 x || high 1 x))
    (hcorrect : ∀ w x, Support.Band x → f w x = Support.target (lineId w) x) :
    6 ≤ gs.length := by
  have hboth_unique : ∀ a b, both a = true → both b = true → a = b := by
    intro a b ha hb
    by_contra hab
    have hne : lineId a ≠ lineId b := fun h => hab (hinj h)
    let x := Support.row (lineId a)
    have hx : Support.Band x := Or.inr (Support.row_spec (lineId a)).1
    have hae := hcorrect a x hx
    have hbe := hcorrect b x hx
    rw [hdouble a ha] at hae
    rw [hdouble b hb] at hbe
    have he := hae.symm.trans hbe
    rw [(Support.row_spec (lineId a)).2, Bridge.row_targets (lineId a) (lineId b) hne] at he
    cases he
  obtain ⟨a, b, c, d, hab, hac, hbc, ha, hb, hc, habhigh, hdc, hcdhigh⟩ :=
    four_two_ownership which both hboth_unique
  have high_upper (w u : Fin 4)
      (huse : both u = true ∨ which u = which w) :
      ∀ x, Support.Band x → high (which w) x = true →
        Support.target (lineId u) x = true := by
    intro x hxband hx
    rw [← hcorrect u x hxband]
    cases hu : both u with
    | false =>
      have he : which u = which w := huse.resolve_left (by simp [hu])
      rw [hsingle u hu, he, hx]
      simp
    | true =>
      rw [hdouble u hu]
      have he := (which w).isLt
      have hi : which w = 0 ∨ which w = 1 := by omega
      rcases hi with hi | hi
      · simp [← hi, hx]
      · simp [← hi, hx]
  have low_dep (w u : Fin 4) (hwu : w ≠ u) (hw : both w = false)
      (huse : both u = true ∨ which u = which w) :
      ∀ p ∈ Support.line (lineId w) \ Support.line (lineId u),
        Cut.Depends 13 ∅ gs (out w) p := by
    intro p hp
    apply shared_parent_cut_depends_band gs (out w) (fun g hm => (hg g hm).1)
      (lineId w) (lineId u)
      (fun he => hwu (hinj he)) (high (which w))
    · intro x hx
      rw [← hsingle w hw]
      exact hcorrect w x hx
    · exact high_upper w u huse
    · exact hp
  let A := Support.line (lineId a) \ Support.line (lineId b)
  let B := Support.line (lineId b) \ Support.line (lineId a)
  let C := Support.line (lineId c) \ Support.line (lineId d)
  have hline_card (w u : Fin 4) (hwu : w ≠ u) :
      (Support.line (lineId w) \ Support.line (lineId u)).card = 3 := by
    have hne : lineId w ≠ lineId u := fun h => hwu (hinj h)
    have hl := OneAnd.line_card (lineId w)
    have hm := OneAnd.line_meet (lineId w) (lineId u) hne
    change (Support.line (lineId w)).card = 4 at hl
    change (Support.line (lineId w) ∩ Support.line (lineId u)).card = 1 at hm
    rw [Finset.card_sdiff, hl, Finset.inter_comm, hm]
  have hAB : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro p hpA hpB
    exact (Finset.mem_sdiff.mp hpA).2 (Finset.mem_sdiff.mp hpB).1
  have hAC : (A ∩ C).card ≤ 1 := by
    have hsub : A ∩ C ⊆ Support.line (lineId a) ∩ Support.line (lineId c) := by
      intro p hp
      exact Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp (Finset.mem_inter.mp hp).1).1,
        (Finset.mem_sdiff.mp (Finset.mem_inter.mp hp).2).1⟩
    have hsmall := Global.line_intersection (lineId a) (lineId c)
      (fun he => hac (hinj he))
    exact (Finset.card_le_card hsub).trans hsmall
  have hBC : (B ∩ C).card ≤ 1 := by
    have hsub : B ∩ C ⊆ Support.line (lineId b) ∩ Support.line (lineId c) := by
      intro p hp
      exact Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp (Finset.mem_inter.mp hp).1).1,
        (Finset.mem_sdiff.mp (Finset.mem_inter.mp hp).2).1⟩
    have hsmall := Global.line_intersection (lineId b) (lineId c)
      (fun he => hbc (hinj he))
    exact (Finset.card_le_card hsub).trans hsmall
  exact three_triples_lower gs (out a) (out b) (out c) (fun g hm => (hg g hm).2) A B C
    (hline_card a b hab) (hline_card b a hab.symm) (hline_card c d hdc.symm)
    hAB hAC hBC (low_dep a b hab ha (Or.inr habhigh.symm))
    (low_dep b a hab.symm hb (Or.inr habhigh)) (low_dep c d hdc.symm hc hcdhigh)

end PEqualNP.Outside.L_meta_1024_aux.FourOrSinks

namespace PEqualNP.Outside.L_meta_1024_aux.FourOrSinks

open PEqualNP.CircuitLowerBounds

lemma cut_ge_false (gs : List Gate) (x : Fin 13 → Bool) (i : ℕ)
    (hi : 13 + gs.length ≤ i) : Cut.cutVal 13 ∅ gs x i = false := by
  unfold Cut.cutVal
  apply List.getD_eq_default
  rw [Cut.run_length]
  exact hi

lemma low_prefix_value (gs : List Gate) (hsize : gs.length ≤ 7)
    (i : ℕ) (hi0 : i ≠ 18) (hi1 : i ≠ 19) (x : Fin 13 → Bool) :
    Cut.cutVal 13 ∅ gs x i = Cut.cutVal 13 ∅ (gs.take 5) x i := by
  by_cases hs : 5 ≤ gs.length
  · by_cases hi : i < 18
    · exact Cut.cutVal_take 13 ∅ gs x 5 i hs hi
    · have hi20 : 20 ≤ i := by omega
      rw [cut_ge_false gs x i (by omega),
        cut_ge_false (gs.take 5) x i (by simp only [List.length_take]; omega)]
  · have hs5 : gs.length ≤ 5 := by omega
    rw [List.take_of_length_le hs5]

lemma low_pair_exact (gs : List Gate) (hsize : gs.length ≤ 7)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : Fin 13) (i j : ℕ)
    (hi0 : i ≠ 18) (hi1 : i ≠ 19) (hj0 : j ≠ 18) (hj1 : j ≠ 19)
    (hcorrect : ∀ x, Support.Band x →
      (Cut.cutVal 13 ∅ gs x i || Cut.cutVal 13 ∅ gs x j) = Support.target w x) :
    ∀ x, (Cut.cutVal 13 ∅ gs x i || Cut.cutVal 13 ∅ gs x j) = Support.target w x := by
  let pre := gs.take 5
  let g : Gate := ⟨GateOp.or, [i, j]⟩
  let code := pre ++ [g]
  let o := 13 + pre.length
  have hval (x : Fin 13 → Bool) :
      Cut.cutVal 13 ∅ code x o =
        (Cut.cutVal 13 ∅ gs x i || Cut.cutVal 13 ∅ gs x j) := by
    rw [low_prefix_value gs hsize i hi0 hi1 x, low_prefix_value gs hsize j hj0 hj1 x]
    change Cut.cutVal 13 ∅ (pre ++ [g]) x (13 + pre.length) = _
    rw [Cut.cutVal_snoc]
    simp [g, GateOp.eval, pre]
  have hcode : ∀ q ∈ code, (q.op = GateOp.and ∨ q.op = GateOp.or) ∧ q.inputs.length ≤ 2 := by
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hg q (List.mem_of_mem_take hq)
    · have he : q = g := by simpa using hq
      subst q
      simp [g]
  let E := Cut.essential (M := 13) 13 ∅ code o
  have hE : E.card ≤ 7 := by
    have he := Cut.essential_bound (M := 13) 13 ∅ code o (fun q hq => (hcode q hq).2)
      (Finset.empty_subset _)
    have hlen : code.length ≤ 6 := by
      simp only [code, List.length_append, List.length_singleton, pre, List.length_take]
      omega
    simp only [Finset.card_empty, Nat.sub_zero] at he
    exact he.trans (by omega)
  have hband : ∀ x, Support.Band x → Circuit.eval ⟨code, o⟩ (List.ofFn x) = Support.target w x := by
    intro x hx
    rw [← Cut.cut_empty, hval]
    exact hcorrect x hx
  have hsupp : Support.Supports (fun x => Circuit.eval ⟨code, o⟩ (List.ofFn x)) E := by
    intro x y hxy
    simpa only [Cut.cut_empty] using Cut.essential_supports 13 ∅ code o x y hxy
  have he : ∀ x, Cut.cutVal 13 ∅ code x o = Support.target w x := by
    simpa only [Cut.cut_empty] using Support.circuit_support_exact code o w
      (fun q hq => (hcode q hq).1) hband E hE hsupp
  intro x
  rw [← hval, he]

end PEqualNP.Outside.L_meta_1024_aux.FourOrSinks

namespace PEqualNP.Outside.L_meta_1024_aux.FourOrSinks

open PEqualNP.CircuitLowerBounds

lemma pair_representation (gs : List Gate) (hsize : gs.length ≤ 7) (i j : ℕ)
    (hhigh : i = 18 ∨ i = 19 ∨ j = 18 ∨ j = 19) :
    ∃ (both : Bool) (which : Fin 2) (o : ℕ),
      (both = false → ∀ x : Fin 13 → Bool,
        (Cut.cutVal 13 ∅ gs x i || Cut.cutVal 13 ∅ gs x j) =
          (Cut.cutVal 13 ∅ gs x (18 + which.val) || Cut.cutVal 13 ∅ (gs.take 5) x o)) ∧
      (both = true → ∀ x : Fin 13 → Bool,
        (Cut.cutVal 13 ∅ gs x i || Cut.cutVal 13 ∅ gs x j) =
          (Cut.cutVal 13 ∅ gs x 18 || Cut.cutVal 13 ∅ gs x 19)) := by
  have hfalse (x : Fin 13 → Bool) : Cut.cutVal 13 ∅ (gs.take 5) x 20 = false :=
    cut_ge_false (gs.take 5) x 20 (by simp only [List.length_take]; omega)
  by_cases hi0 : i = 18
  · subst i
    by_cases hj1 : j = 19
    · refine ⟨true, 0, 20, by simp, ?_⟩
      intro _ x
      rw [hj1]
    · by_cases hj0 : j = 18
      · refine ⟨false, 0, 20, ?_, by simp⟩
        intro _ x
        simp [hj0, hfalse]
      · refine ⟨false, 0, j, ?_, by simp⟩
        intro _ x
        simpa using congrArg (fun z => Cut.cutVal 13 ∅ gs x 18 || z)
          (low_prefix_value gs hsize j hj0 hj1 x)
  · by_cases hi1 : i = 19
    · subst i
      by_cases hj0 : j = 18
      · refine ⟨true, 0, 20, by simp, ?_⟩
        intro _ x
        simp [hj0, Bool.or_comm]
      · by_cases hj1 : j = 19
        · refine ⟨false, 1, 20, ?_, by simp⟩
          intro _ x
          simp [hj1, hfalse]
        · refine ⟨false, 1, j, ?_, by simp⟩
          intro _ x
          simpa using congrArg (fun z => Cut.cutVal 13 ∅ gs x 19 || z)
            (low_prefix_value gs hsize j hj0 hj1 x)
    · have hj : j = 18 ∨ j = 19 := by tauto
      rcases hj with hj | hj
      · refine ⟨false, 0, i, ?_, by simp⟩
        intro _ x
        rw [hj, low_prefix_value gs hsize i hi0 hi1 x]
        simp [Bool.or_comm]
      · refine ⟨false, 1, i, ?_, by simp⟩
        intro _ x
        rw [hj, low_prefix_value gs hsize i hi0 hi1 x]
        simp [Bool.or_comm]

lemma four_pairs_impossible (gs : List Gate) (hsize : gs.length ≤ 7)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (lineId : Fin 4 → Fin 13) (hinj : Function.Injective lineId)
    (left right : Fin 4 → ℕ)
    (hcorrect : ∀ w x, Support.Band x →
      (Cut.cutVal 13 ∅ gs x (left w) || Cut.cutVal 13 ∅ gs x (right w)) =
        Support.target (lineId w) x)
    (hnotexact : ∀ w, ¬ ∀ x : Fin 13 → Bool,
      (Cut.cutVal 13 ∅ gs x (left w) || Cut.cutVal 13 ∅ gs x (right w)) =
        Support.target (lineId w) x) : False := by
  have hhigh (w : Fin 4) : left w = 18 ∨ left w = 19 ∨ right w = 18 ∨ right w = 19 := by
    by_contra h
    push Not at h
    exact hnotexact w (low_pair_exact gs hsize hg (lineId w) (left w) (right w)
      h.1 h.2.1 h.2.2.1 h.2.2.2 (hcorrect w))
  have hrep (w : Fin 4) := pair_representation gs hsize (left w) (right w) (hhigh w)
  choose both which out hsingle hdouble using hrep
  have hcount := high_network_lower_band (gs.take 5) out
    (fun g hgmem => hg g (List.mem_of_mem_take hgmem)) lineId hinj which both
    (fun u x => Cut.cutVal 13 ∅ gs x (18 + u.val))
    (fun w x => Cut.cutVal 13 ∅ gs x (left w) || Cut.cutVal 13 ∅ gs x (right w))
    hsingle hdouble hcorrect
  simp only [List.length_take] at hcount
  omega

end PEqualNP.Outside.L_meta_1024_aux.FourOrSinks


namespace PEqualNP.Outside.L_meta_1024_aux.Ancestry

open PEqualNP.CircuitLowerBounds

def step (w : List (Finset ℕ)) (g : Gate) : List (Finset ℕ) :=
  w ++ [insert w.length (g.inputs.toFinset.biUnion fun i => w.getD i ∅)]

def run (gs : List Gate) : List (Finset ℕ) :=
  gs.foldl step (List.ofFn fun i : Fin 13 => ({i.val} : Finset ℕ))

def anc (gs : List Gate) (i : ℕ) : Finset ℕ := (run gs).getD i ∅

lemma fold_length (gs : List Gate) (w : List (Finset ℕ)) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp only [List.foldl_cons, ih, List.length_cons, step,
      List.length_append, List.length_cons, List.length_nil]; omega

lemma run_length (gs : List Gate) : (run gs).length = 13 + gs.length := by
  simp [run, fold_length]

lemma anc_nil (i : ℕ) : anc [] i = if i < 13 then {i} else ∅ := by
  have hgen {n : ℕ} (k : ℕ) :
      (List.ofFn fun p : Fin n => ({p.val} : Finset ℕ)).getD k ∅ =
        if k < n then {k} else ∅ := by
    by_cases hk : k < n <;> simp [List.getD_eq_getElem?_getD, hk]
  exact hgen i

lemma anc_snoc (gs : List Gate) (g : Gate) (i : ℕ) :
    anc (gs ++ [g]) i = if i = 13 + gs.length then
      insert i (g.inputs.toFinset.biUnion fun j => anc gs j) else anc gs i := by
  unfold anc run
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, step]
  have hl : (gs.foldl step (List.ofFn fun i : Fin 13 => ({i.val} : Finset ℕ))).length =
      13 + gs.length := by rw [fold_length]; simp
  rcases lt_trichotomy i (13 + gs.length) with h | h | h
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]
  · rw [if_pos h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp only [hl, h, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by rw [List.length_append, hl]; simp only [List.length_singleton]; omega),
      List.getElem?_eq_none (by omega)]

lemma anc_invalid (gs : List Gate) (i : ℕ) (hi : 13 + gs.length ≤ i) : anc gs i = ∅ := by
  exact List.getD_eq_default _ _ (by simpa only [run_length] using hi)

lemma anc_input (gs : List Gate) (i : ℕ) (hi : i < 13) : anc gs i = {i} := by
  induction gs using List.reverseRecOn with
  | nil => simp [anc_nil, hi]
  | append_singleton gs g ih => rw [anc_snoc, if_neg (by omega), ih]

lemma anc_bound (gs : List Gate) (i j : ℕ) (hj : j ∈ anc gs i) :
    j ≤ i ∧ j < 13 + gs.length := by
  induction gs using List.reverseRecOn generalizing i j with
  | nil =>
    rw [anc_nil] at hj
    split_ifs at hj with hi
    · have he : j = i := by simpa using hj
      subst j
      exact ⟨le_rfl, by simpa using hi⟩
    · simp at hj
  | append_singleton gs g ih =>
    rw [anc_snoc] at hj
    by_cases hi : i = 13 + gs.length
    · rw [if_pos hi] at hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · simp only [List.length_append, List.length_singleton]; omega
      · obtain ⟨k, hk, hj⟩ := Finset.mem_biUnion.mp hj
        have hb := ih k j hj
        simp only [List.length_append, List.length_singleton]
        omega
    · rw [if_neg hi] at hj
      have hb := ih i j hj
      simp only [List.length_append, List.length_singleton]
      omega

lemma ancestor_trans (gs : List Gate) (i j : ℕ) (hj : j ∈ anc gs i) :
    anc gs j ⊆ anc gs i := by
  induction gs using List.reverseRecOn generalizing i j with
  | nil =>
    have hb := anc_bound [] i j hj
    rw [anc_input [] j (by simpa using hb.2)]
    exact Finset.singleton_subset_iff.mpr hj
  | append_singleton gs g ih =>
    have hb := anc_bound (gs ++ [g]) i j hj
    by_cases hij : j = i
    · subst j; exact Finset.Subset.refl _
    by_cases hi : i = 13 + gs.length
    · rw [anc_snoc gs g i, if_pos hi] at hj ⊢
      have hjold : j < 13 + gs.length := by omega
      rw [anc_snoc, if_neg (by omega)]
      obtain ⟨k, hk, hjk⟩ := Finset.mem_biUnion.mp ((Finset.mem_insert.mp hj).resolve_left hij)
      intro p hp
      exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨k, hk, ih k j hjk hp⟩)
    · rw [anc_snoc gs g i, if_neg hi] at hj ⊢
      have hjold := (anc_bound gs i j hj).2
      rw [anc_snoc, if_neg (by omega)]
      exact ih i j hj

lemma depends_mem {M : ℕ} (P : Finset ℕ) (gs : List Gate) (i : ℕ) (t : Fin M)
    (ht : Cut.Depends 13 P gs i t) : t.val ∈ anc gs i := by
  induction gs using List.reverseRecOn generalizing i t with
  | nil =>
    obtain ⟨x, y, hxy, hne⟩ := ht
    rw [Cut.cutVal_nil, Cut.cutVal_nil] at hne
    by_cases hi : i < 13
    · simp only [hi, ite_true] at hne
      have he := Cut.source_dep x y i t hxy hne
      simp [anc_nil, hi, he]
    · simp [hi] at hne
  | append_singleton gs g ih =>
    obtain ⟨x, y, hxy, hne⟩ := ht
    rw [Cut.cutVal_snoc, Cut.cutVal_snoc] at hne
    by_cases hi : i = 13 + gs.length
    · rw [if_pos hi, if_pos hi] at hne
      rw [anc_snoc, if_pos hi]
      by_cases hp : i ∈ P
      · simp only [← hi, hp, ite_true] at hne
        have he := Cut.source_dep x y i t hxy hne
        simpa only [he] using Finset.mem_insert_self i (g.inputs.toFinset.biUnion fun j => anc gs j)
      · simp only [← hi, hp, ite_false] at hne
        have hex : ∃ j ∈ g.inputs,
            Cut.cutVal 13 P gs x j ≠ Cut.cutVal 13 P gs y j := by
          by_contra! hh
          apply hne
          congr 1
          exact List.map_congr_left hh
        obtain ⟨j, hj, hne⟩ := hex
        exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr
          ⟨j, by simpa using hj, ih j t ⟨x, y, hxy, hne⟩⟩)
    · rw [if_neg hi, if_neg hi] at hne
      rw [anc_snoc, if_neg hi]
      exact ih i t ⟨x, y, hxy, hne⟩

lemma components (S : Finset (Fin 13)) (gs : List Gate)
    (hg : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    ∃ (label : Fin 13 → ℕ) (wire : ℕ → ℕ),
      S.card ≤ (S.image label).card + gs.length ∧
      (∀ p : Fin 13, wire p.val = label p) ∧
      ∀ i j, j ∈ anc gs i → wire j = wire i := by
  classical
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨Fin.val, id, ?_, fun _ => rfl, ?_⟩
    · simp [Finset.card_image_of_injective _ Fin.val_injective]
    · intro i j hj
      rw [anc_nil] at hj
      split_ifs at hj with hi
      · simpa using hj
      · simp at hj
  | append_singleton gs g ih =>
    obtain ⟨label, wire, hc, hr, ha⟩ := ih (fun q hq => hg q (by simp [hq]))
    obtain ⟨a, b, hins⟩ := Cut.two_inputs g.inputs (hg g (by simp))
    let merge (k : ℕ) := if k = wire b then wire a else k
    have hma : merge (wire a) = wire a := by simp [merge]
    have hmb : merge (wire b) = wire a := by simp [merge]
    refine ⟨merge ∘ label, fun i => if i = 13 + gs.length then wire a else merge (wire i),
      ?_, ?_, ?_⟩
    · have hsub : S.image label ⊆ insert (wire b) (S.image (merge ∘ label)) := by
        intro v hv
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hv
        by_cases he : label t = wire b
        · simp [he]
        · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨t, ht, by simp [merge, he]⟩)
      have hcard := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
      simp only [List.length_append, List.length_singleton]
      omega
    · intro p
      change (if p.val = 13 + gs.length then wire a else merge (wire p.val)) = merge (label p)
      rw [if_neg (by omega), hr]
    · intro i j hj
      change (if j = 13 + gs.length then wire a else merge (wire j)) =
        (if i = 13 + gs.length then wire a else merge (wire i))
      rw [anc_snoc] at hj
      by_cases hi : i = 13 + gs.length
      · rw [if_pos hi] at hj ⊢
        rcases Finset.mem_insert.mp hj with rfl | hj
        · simp [hi]
        · obtain ⟨k, hk, hjk⟩ := Finset.mem_biUnion.mp hj
          have hjold := (anc_bound gs k j hjk).2
          rw [if_neg (by omega), ha k j hjk]
          rcases hins k (by simpa using hk) with rfl | rfl
          · exact hma
          · exact hmb
      · rw [if_neg hi] at hj ⊢
        have hjold := (anc_bound gs i j hj).2
        rw [if_neg (by omega), ha i j hj]

end PEqualNP.Outside.L_meta_1024_aux.Ancestry

namespace PEqualNP.Outside.L_meta_1024_aux.TwoPairs

open PEqualNP.CircuitLowerBounds

lemma pair_zero (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w : Fin 13) (i j : ℕ)
    (hc : ∀ x, Support.Band x →
      (Cut.cutVal 13 ∅ gs x i || Cut.cutVal 13 ∅ gs x j) = Support.target w x) :
    (Cut.cutVal 13 ∅ gs (fun _ : Fin 13 => false) i || Cut.cutVal 13 ∅ gs (fun _ : Fin 13 => false) j) = false := by
  have hr := Support.row_spec w
  have he := hc (Support.row w) (Or.inr hr.1)
  rw [hr.2] at he
  apply Bool.eq_false_iff.mpr
  intro ht
  rcases Bool.or_eq_true_iff.mp ht with ht | ht
  · have h := Cut.cutVal_mono 13 ∅ gs hg (fun _ : Fin 13 => false) (Support.row w)
      (by simp) i ht
    simp [h] at he
  · have h := Cut.cutVal_mono 13 ∅ gs hg (fun _ : Fin 13 => false) (Support.row w)
      (by simp) j ht
    simp [h] at he

lemma missing_gate_exact (gs : List Gate) (hlen : gs.length ≤ 6)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : Fin 13) (i j k : ℕ) (hk : 13 ≤ k ∧ k < 13 + gs.length)
    (hki : k ∉ Ancestry.anc gs i) (hkj : k ∉ Ancestry.anc gs j)
    (hc : ∀ x, Support.Band x →
      (Cut.cutVal 13 ∅ gs x i || Cut.cutVal 13 ∅ gs x j) = Support.target w x) :
    ∀ x, (Cut.cutVal 13 ∅ gs x i || Cut.cutVal 13 ∅ gs x j) = Support.target w x := by
  classical
  let g : Gate := ⟨GateOp.or, [i, j]⟩
  let code := gs ++ [g]
  let o := 13 + gs.length
  have hval (x : Fin 13 → Bool) : Cut.cutVal 13 ∅ code x o =
      (Cut.cutVal 13 ∅ gs x i || Cut.cutVal 13 ∅ gs x j) := by
    rw [Cut.cutVal_snoc]
    simp [o, g, GateOp.eval]
  have hcode : ∀ q ∈ code, (q.op = GateOp.and ∨ q.op = GateOp.or) ∧ q.inputs.length ≤ 2 := by
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hg q hq
    · have he : q = g := by simpa using hq
      subst q
      simp [g]
  let E := Cut.essential (M := 13 + code.length) 13 {k} code o
  have hraw : ∀ t ∈ E, t.val < 13 := by
    intro t ht
    rcases Cut.essential_sources 13 {k} code o t ht with h | h
    · exact h
    · have he : t.val = k := by simpa using h
      have ha := Ancestry.depends_mem {k} code o t (Finset.mem_filter.mp ht).2
      rw [he, Ancestry.anc_snoc, if_pos rfl] at ha
      simp [g, o, ne_of_lt hk.2, hki, hkj] at ha
  have hcard : E.card ≤ 7 := by
    have hb := Cut.essential_bound (M := 13 + code.length) 13 {k} code o
      (fun q hq => (hcode q hq).2) (by
        intro a ha
        have he : a = k := by simpa using ha
        subst a
        exact Finset.mem_Ico.mpr ⟨hk.1, by simp [code]; omega⟩)
    simp only [Finset.card_singleton] at hb
    have hl : code.length ≤ 7 := by simp [code]; omega
    change (Cut.essential (M := 13 + code.length) 13 {k} code o).card ≤ 7
    omega
  obtain ⟨S, hS, hs⟩ := Cut.raw_support_exists {k} code o 7 hraw hcard
  have hb : ∀ x, Support.Band x → Circuit.eval ⟨code, o⟩ (List.ofFn x) = Support.target w x := by
    intro x hx
    rw [← Cut.cut_empty, hval]
    exact hc x hx
  have he := Support.circuit_support_exact code o w (fun q hq => (hcode q hq).1) hb S hS hs
  intro x
  rw [← hval, Cut.cut_empty, he]

lemma all_ancestors (gs : List Gate) (hlen : gs.length ≤ 6)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : Fin 13) (i j : ℕ)
    (hc : ∀ x, Support.Band x →
      (Cut.cutVal 13 ∅ gs x i || Cut.cutVal 13 ∅ gs x j) = Support.target w x)
    (hne : ¬ ∀ x, (Cut.cutVal 13 ∅ gs x i || Cut.cutVal 13 ∅ gs x j) = Support.target w x)
    (k : ℕ) (hk : 13 ≤ k ∧ k < 13 + gs.length) :
    k ∈ Ancestry.anc gs i ∪ Ancestry.anc gs j := by
  by_contra hm
  simp only [Finset.mem_union, not_or] at hm
  exact hne (missing_gate_exact gs hlen hg w i j k hk hm.1 hm.2 hc)

lemma ancestor_pair_exact (gs : List Gate) (hlen : gs.length ≤ 6)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : Fin 13) (i j : ℕ) (hij : j ∈ Ancestry.anc gs i)
    (hc : ∀ x, Support.Band x →
      (Cut.cutVal 13 ∅ gs x i || Cut.cutVal 13 ∅ gs x j) = Support.target w x) :
    ∀ x, (Cut.cutVal 13 ∅ gs x i || Cut.cutVal 13 ∅ gs x j) = Support.target w x := by
  classical
  let E := Cut.essential (M := 13) 13 ∅ gs i ∪ Cut.essential (M := 13) 13 ∅ gs j
  obtain ⟨label, wire, hcard, hraw, ha⟩ := Ancestry.components E gs (fun q hq => (hg q hq).2)
  have heq : wire j = wire i := ha i j hij
  have hlabel : ∀ p ∈ E, label p = wire i := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact (hraw p).symm.trans (ha i p.val
        (Ancestry.depends_mem ∅ gs i p (Finset.mem_filter.mp hp).2))
    · exact (hraw p).symm.trans ((ha j p.val
        (Ancestry.depends_mem ∅ gs j p (Finset.mem_filter.mp hp).2)).trans heq)
  have himage : (E.image label).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hb
    exact (hlabel p hp).trans (hlabel q hq).symm
  have hE : E.card ≤ 7 := by omega
  apply Support.small_support_exact w _ hc (pair_zero gs (fun q hq => (hg q hq).1) w i j hc) E hE
  intro x y hxy
  have hi := Cut.essential_supports 13 ∅ gs i x y
    (fun p hp => hxy p (Finset.mem_union_left _ hp))
  have hj := Cut.essential_supports 13 ∅ gs j x y
    (fun p hp => hxy p (Finset.mem_union_right _ hp))
  change (Cut.cutVal 13 ∅ gs x i || Cut.cutVal 13 ∅ gs x j) =
    (Cut.cutVal 13 ∅ gs y i || Cut.cutVal 13 ∅ gs y j)
  rw [hi, hj]

lemma small_pair_exact (gs : List Gate) (hlen : gs.length ≤ 5)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : Fin 13) (i j : ℕ)
    (hc : ∀ x, Support.Band x →
      (Cut.cutVal 13 ∅ gs x i || Cut.cutVal 13 ∅ gs x j) = Support.target w x) :
    ∀ x, (Cut.cutVal 13 ∅ gs x i || Cut.cutVal 13 ∅ gs x j) = Support.target w x := by
  let ii := if i < 18 then i else 20
  let jj := if j < 18 then j else 20
  have hv (x : Fin 13 → Bool) (k : ℕ) :
      Cut.cutVal 13 ∅ gs x (if k < 18 then k else 20) = Cut.cutVal 13 ∅ gs x k := by
    split_ifs with hk
    · rfl
    · rw [FourOrSinks.cut_ge_false gs x 20 (by omega),
        FourOrSinks.cut_ge_false gs x k (by omega)]
  have hsmall := FourOrSinks.low_pair_exact gs (by omega) hg w ii jj
    (by dsimp [ii]; split_ifs <;> omega) (by dsimp [ii]; split_ifs <;> omega)
    (by dsimp [jj]; split_ifs <;> omega) (by dsimp [jj]; split_ifs <;> omega)
    (by intro x hx; simpa only [ii, jj, hv] using hc x hx)
  intro x
  simpa only [ii, jj, hv] using hsmall x

lemma last_member (gs : List Gate) (hlen : gs.length = 6) (i : ℕ)
    (hi : 18 ∈ Ancestry.anc gs i) : i = 18 := by
  have hle := (Ancestry.anc_bound gs i 18 hi).1
  by_contra hn
  have hbig : 13 + gs.length ≤ i := by omega
  rw [Ancestry.anc_invalid gs i hbig] at hi
  simp at hi

lemma two_pairs_impossible (gs : List Gate) (hlen : gs.length ≤ 6)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (u v : Fin 13) (huv : u ≠ v) (i j k l : ℕ)
    (hu : ∀ x, Support.Band x →
      (Cut.cutVal 13 ∅ gs x i || Cut.cutVal 13 ∅ gs x j) = Support.target u x)
    (hv : ∀ x, Support.Band x →
      (Cut.cutVal 13 ∅ gs x k || Cut.cutVal 13 ∅ gs x l) = Support.target v x)
    (hnu : ¬ ∀ x, (Cut.cutVal 13 ∅ gs x i || Cut.cutVal 13 ∅ gs x j) = Support.target u x)
    (hnv : ¬ ∀ x, (Cut.cutVal 13 ∅ gs x k || Cut.cutVal 13 ∅ gs x l) = Support.target v x) : False := by
  have hs : gs.length = 6 := by
    by_contra hn
    exact hnu (small_pair_exact gs (by omega) hg u i j hu)
  have hp (w : Fin 13) (a b : ℕ)
      (hc : ∀ x, Support.Band x →
        (Cut.cutVal 13 ∅ gs x a || Cut.cutVal 13 ∅ gs x b) = Support.target w x)
      (hn : ¬ ∀ x, (Cut.cutVal 13 ∅ gs x a || Cut.cutVal 13 ∅ gs x b) = Support.target w x) :
      ∃ r, (∀ x, Support.Band x →
        (Cut.cutVal 13 ∅ gs x 18 || Cut.cutVal 13 ∅ gs x r) = Support.target w x) ∧
        (¬ ∀ x, (Cut.cutVal 13 ∅ gs x 18 || Cut.cutVal 13 ∅ gs x r) = Support.target w x) := by
    have hh := all_ancestors gs hlen hg w a b hc hn 18 (by omega)
    rcases Finset.mem_union.mp hh with hh | hh
    · have he := last_member gs hs a hh
      subst a
      exact ⟨b, hc, hn⟩
    · have he := last_member gs hs b hh
      subst b
      exact ⟨a, by simpa only [Bool.or_comm] using hc, by simpa only [Bool.or_comm] using hn⟩
  obtain ⟨a, hua, hnua⟩ := hp u i j hu hnu
  obtain ⟨b, hvb, hnvb⟩ := hp v k l hv hnv
  have hna : a ∉ Ancestry.anc gs 18 := fun h => hnua (ancestor_pair_exact gs hlen hg u 18 a h hua)
  have hnb : b ∉ Ancestry.anc gs 18 := fun h => hnvb (ancestor_pair_exact gs hlen hg v 18 b h hvb)
  have hvalid (w z : Fin 13) (hwz : w ≠ z) (r s : ℕ)
      (hc : ∀ x, Support.Band x →
        (Cut.cutVal 13 ∅ gs x 18 || Cut.cutVal 13 ∅ gs x r) = Support.target w x)
      (hd : ∀ x, Support.Band x →
        (Cut.cutVal 13 ∅ gs x 18 || Cut.cutVal 13 ∅ gs x s) = Support.target z x) :
      13 ≤ r ∧ r < 13 + gs.length := by
    have hdep : ∀ p ∈ Support.line w \ Support.line z, p.val ∈ Ancestry.anc gs r := by
      intro p hp
      apply Ancestry.depends_mem ∅ gs r p
      apply FourOrSinks.shared_parent_cut_depends_band gs r (fun q hq => (hg q hq).1)
        w z hwz (fun x => Cut.cutVal 13 ∅ gs x 18) hc
      · intro x hx ht
        rw [← hd x hx, ht]
        simp
      · exact hp
    have hc3 : (Support.line w \ Support.line z).card = 3 := by
      have h := Bridge.pair_geometry w z hwz
      have hi := Global.line_intersection w z hwz
      have hw := Global.line_card w
      have hz := Global.line_card z
      have hu := Finset.card_union_add_card_inter (Global.line w) (Global.line z)
      have he : (Global.line w ∩ Global.line z).card = 1 := by omega
      simpa only [Global.line, Support.line] using (show (Global.line w \ Global.line z).card = 3 by
        rw [Finset.card_sdiff, Finset.inter_comm]; omega)
    have hsub : (Support.line w \ Support.line z).image Fin.val ⊆ Ancestry.anc gs r := by
      intro q hq
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
      exact hdep p hp
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ Fin.val_injective, hc3] at hcard
    constructor
    · by_contra hn
      rw [Ancestry.anc_input gs r (by omega)] at hcard
      simp at hcard
    · by_contra hn
      rw [Ancestry.anc_invalid gs r (by omega)] at hcard
      simp at hcard
  have ha := hvalid u v huv a b hua hvb
  have hb := hvalid v u huv.symm b a hvb hua
  have hba := all_ancestors gs hlen hg u 18 a hua hnua b hb
  have hab := all_ancestors gs hlen hg v 18 b hvb hnvb a ha
  have hleba := (Ancestry.anc_bound gs a b ((Finset.mem_union.mp hba).resolve_left hnb)).1
  have hleab := (Ancestry.anc_bound gs b a ((Finset.mem_union.mp hab).resolve_left hna)).1
  have he : a = b := by omega
  subst b
  have heq := (hua (Support.row u) (Or.inr (Support.row_spec u).1)).symm.trans
    (hvb (Support.row u) (Or.inr (Support.row_spec u).1))
  rw [(Support.row_spec u).2, Bridge.row_targets u v huv] at heq
  cases heq

end PEqualNP.Outside.L_meta_1024_aux.TwoPairs

namespace PEqualNP.Outside.L_meta_1024_aux.TwoPairs

open PEqualNP.CircuitLowerBounds

lemma low_prefix_value (gs : List Gate) (hlen : gs.length ≤ 9) (i : ℕ)
    (hi : i ∉ ({19, 20, 21} : Finset ℕ)) (x : Fin 13 → Bool) :
    Cut.cutVal 13 ∅ gs x i = Cut.cutVal 13 ∅ (gs.take 6) x i := by
  by_cases hs : 6 ≤ gs.length
  · by_cases hil : i < 19
    · exact Cut.cutVal_take 13 ∅ gs x 6 i hs hil
    · have hbig : 22 ≤ i := by simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi; omega
      rw [FourOrSinks.cut_ge_false gs x i (by omega),
        FourOrSinks.cut_ge_false (gs.take 6) x i (by simp only [List.length_take]; omega)]
  · rw [List.take_of_length_le (show gs.length ≤ 6 by omega)]

lemma low_pair_unique (gs : List Gate) (hlen : gs.length ≤ 9)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    {m : ℕ} (lineId : Fin m → Fin 13) (hinj : Function.Injective lineId)
    (left right : Fin m → ℕ)
    (hc : ∀ w x, Support.Band x →
      (Cut.cutVal 13 ∅ gs x (left w) || Cut.cutVal 13 ∅ gs x (right w)) = Support.target (lineId w) x)
    (hn : ∀ w, ¬ ∀ x,
      (Cut.cutVal 13 ∅ gs x (left w) || Cut.cutVal 13 ∅ gs x (right w)) = Support.target (lineId w) x)
    (u v : Fin m)
    (hul : left u ∉ ({19, 20, 21} : Finset ℕ))
    (hur : right u ∉ ({19, 20, 21} : Finset ℕ))
    (hvl : left v ∉ ({19, 20, 21} : Finset ℕ))
    (hvr : right v ∉ ({19, 20, 21} : Finset ℕ)) : u = v := by
  by_contra huv
  have hvu (x : Fin 13 → Bool) :
      (Cut.cutVal 13 ∅ (gs.take 6) x (left u) || Cut.cutVal 13 ∅ (gs.take 6) x (right u)) =
      (Cut.cutVal 13 ∅ gs x (left u) || Cut.cutVal 13 ∅ gs x (right u)) := by
    rw [← low_prefix_value gs hlen (left u) hul x, ← low_prefix_value gs hlen (right u) hur x]
  have hvv (x : Fin 13 → Bool) :
      (Cut.cutVal 13 ∅ (gs.take 6) x (left v) || Cut.cutVal 13 ∅ (gs.take 6) x (right v)) =
      (Cut.cutVal 13 ∅ gs x (left v) || Cut.cutVal 13 ∅ gs x (right v)) := by
    rw [← low_prefix_value gs hlen (left v) hvl x, ← low_prefix_value gs hlen (right v) hvr x]
  exact two_pairs_impossible (gs.take 6) (by simp)
    (fun g hgm => hg g (List.mem_of_mem_take hgm)) (lineId u) (lineId v)
    (fun h => huv (hinj h)) (left u) (right u) (left v) (right v)
    (by intro x hx; rw [hvu]; exact hc u x hx)
    (by intro x hx; rw [hvv]; exact hc v x hx)
    (by intro h; apply hn u; intro x; rw [← hvu]; exact h x)
    (by intro h; apply hn v; intro x; rw [← hvv]; exact h x)

lemma four_use_last_three (gs : List Gate) (hlen : gs.length ≤ 9)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (lineId : Fin 5 → Fin 13) (hinj : Function.Injective lineId)
    (left right : Fin 5 → ℕ)
    (hc : ∀ w x, Support.Band x →
      (Cut.cutVal 13 ∅ gs x (left w) || Cut.cutVal 13 ∅ gs x (right w)) = Support.target (lineId w) x)
    (hn : ∀ w, ¬ ∀ x,
      (Cut.cutVal 13 ∅ gs x (left w) || Cut.cutVal 13 ∅ gs x (right w)) = Support.target (lineId w) x) :
    4 ≤ (Finset.univ.filter fun w : Fin 5 =>
      left w ∈ ({19, 20, 21} : Finset ℕ) ∨ right w ∈ ({19, 20, 21} : Finset ℕ)).card := by
  classical
  let low := Finset.univ.filter fun w : Fin 5 =>
    left w ∉ ({19, 20, 21} : Finset ℕ) ∧ right w ∉ ({19, 20, 21} : Finset ℕ)
  have hlow : low.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro u hu v hv
    exact low_pair_unique gs hlen hg lineId hinj left right hc hn u v
      (Finset.mem_filter.mp hu).2.1 (Finset.mem_filter.mp hu).2.2
      (Finset.mem_filter.mp hv).2.1 (Finset.mem_filter.mp hv).2.2
  have he : (Finset.univ.filter fun w : Fin 5 =>
      left w ∈ ({19, 20, 21} : Finset ℕ) ∨ right w ∈ ({19, 20, 21} : Finset ℕ)) =
      Finset.univ \ low := by
    ext w
    simp [low]
    tauto
  rw [he, Finset.card_sdiff, Finset.inter_univ]
  simp only [Finset.card_univ, Fintype.card_fin]
  omega

end PEqualNP.Outside.L_meta_1024_aux.TwoPairs

namespace PEqualNP.Outside.L_meta_1024_aux.EarlyCommon

open PEqualNP.CircuitLowerBounds

lemma pair_card_le {α : Type} [DecidableEq α] (a b : α) : ({a, b} : Finset α).card ≤ 2 := by
  have h := Finset.card_insert_le a ({b} : Finset α)
  simpa using h

def op (a : Bool) (x y : Bool) : Bool := if a then x && y else x || y

def output (gs : List Gate) (a : Bool) (c d e : ℕ) (x : Fin 13 → Bool) : Bool :=
  Cut.cutVal 13 ∅ gs x c || op a (Cut.cutVal 13 ∅ gs x d) (Cut.cutVal 13 ∅ gs x e)

lemma op_comm (a x y : Bool) : op a x y = op a y x := by
  cases a <;> simp [op, Bool.and_comm, Bool.or_comm]

lemma subset_rank {M : ℕ} (label : Fin M → ℕ) (s : ℕ)
    (h : M ≤ ((Finset.univ : Finset (Fin M)).image label).card + s)
    (S : Finset (Fin M)) : S.card ≤ (S.image label).card + s := by
  classical
  let T := Finset.univ \ S
  have hST : S ∪ T = Finset.univ := by ext p; simp [T]
  have htotal : S.card + T.card = M := by
    have hle : S.card ≤ M := by simpa using Finset.card_le_card (Finset.subset_univ S)
    dsimp [T]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  have himage : ((Finset.univ : Finset (Fin M)).image label).card ≤
      (S.image label).card + T.card := by
    calc
      _ = (S.image label ∪ T.image label).card := by rw [← Finset.image_union, hST]
      _ ≤ (S.image label).card + (T.image label).card := Finset.card_union_le _ _
      _ ≤ (S.image label).card + T.card := Nat.add_le_add_left Finset.card_image_le _
  omega

lemma difference_card (u v : Fin 13) (huv : u ≠ v) :
    (Support.line u \ Support.line v).card = 3 := by
  have h := Bridge.pair_geometry u v huv
  have hw := Global.line_card u
  have hz := Global.line_card v
  have hu := Finset.card_union_add_card_inter (Global.line u) (Global.line v)
  have he : (Global.line u ∩ Global.line v).card = 1 := by omega
  simpa only [Global.line, Support.line] using
    (show (Global.line u \ Global.line v).card = 3 by
      rw [Finset.card_sdiff, Finset.inter_comm]; omega)

lemma separating_raw (u v : Fin 13) (huv : u ≠ v) (q : Fin 13) :
    ∃ x : Fin 13 → Bool, Support.Band x ∧ Support.target u x = true ∧
      Support.target v x = false ∧ x q = false := by
  classical
  have hthree := difference_card u v huv
  have hex : ∃ p ∈ Support.line u \ Support.line v, p ≠ q := by
    by_contra! h
    have hs : Support.line u \ Support.line v ⊆ {q} := by
      intro p hp
      simpa using h p hp
    have hc := Finset.card_le_card hs
    simp only [Finset.card_singleton] at hc
    omega
  obtain ⟨p, hp, hpq⟩ := hex
  let Q := insert q (Support.line v)
  let U := Finset.univ.erase p
  have hQU : Q ⊆ U := by
    intro a ha
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_univ _⟩
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact hpq.symm
    · intro he
      subst a
      exact (Finset.mem_sdiff.mp hp).2 ha
  have hQ : Q.card ≤ 5 := by
    have h := Finset.card_insert_le q (Support.line v)
    rw [Clamp.line_card] at h
    exact h
  have hU : U.card = 12 := by simp [U]
  have havail : 6 - Q.card ≤ (U \ Q).card := by
    rw [Finset.card_sdiff_of_subset hQU, hU]
    omega
  obtain ⟨B, hB, hBc⟩ := Finset.exists_subset_card_eq havail
  have hd : Disjoint Q B := by
    rw [Finset.disjoint_left]
    intro a ha hb
    exact (Finset.mem_sdiff.mp (hB hb)).2 ha
  let Z := Q ∪ B
  have hZ : Z.card = 6 := by
    dsimp [Z]
    rw [Finset.card_union_of_disjoint hd, hBc]
    omega
  have hZU : Z ⊆ U := by
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · exact hQU ha
    · exact (Finset.mem_sdiff.mp (hB ha)).1
  refine ⟨Support.fromZeros Z, ?_, ?_, ?_, ?_⟩
  · exact Or.inr ((congrArg Finset.card (Support.zeroSet_fromZeros Z)).trans hZ)
  · apply decide_eq_true
    refine ⟨p, (Finset.mem_sdiff.mp hp).1, ?_⟩
    have hn : p ∉ Z := fun h => (Finset.mem_erase.mp (hZU h)).1 rfl
    simp [Support.fromZeros, hn]
  · apply decide_eq_false_iff_not.mpr
    rintro ⟨a, ha, hx⟩
    have hz : a ∈ Z := Finset.mem_union_left _ (Finset.mem_insert_of_mem ha)
    simp [Support.fromZeros, hz] at hx
  · have hz : q ∈ Z := Finset.mem_union_left _ (Finset.mem_insert_self _ _)
    simp [Support.fromZeros, hz]

lemma target_not_le (u v : Fin 13) (huv : u ≠ v) :
    ¬ ∀ x, Support.Band x → Support.target u x = true → Support.target v x = true := by
  intro h
  have he := h (Support.row v) (Or.inr (Support.row_spec v).1)
    (Bridge.row_targets v u huv.symm)
  rw [(Support.row_spec v).2] at he
  cases he

lemma output_zero (gs : List Gate) (a : Bool) (c d e : ℕ) (w : Fin 13)
    (hu : ∀ x, Support.target w x = false → output gs a c d e x = false) :
    output gs a c d e (fun _ => false) = false := by
  exact hu _ (by simp [Support.target])

lemma distinct_labels (gs : List Gate) (hlen : gs.length ≤ 5)
    (label : Fin 13 → ℕ) (wire : ℕ → ℕ)
    (hcount : 13 ≤ ((Finset.univ : Finset (Fin 13)).image label).card + gs.length)
    (hraw : ∀ p : Fin 13, wire p.val = label p)
    (ha : ∀ i j, j ∈ Ancestry.anc gs i → wire j = wire i)
    (a : Bool) (c d e : ℕ) (w : Fin 13)
    (hc : ∀ x, Support.Band x → output gs a c d e x = Support.target w x)
    (hu : ∀ x, Support.target w x = false → output gs a c d e x = false)
    (hn : ¬ ∀ x, output gs a c d e x = Support.target w x) :
    wire c ≠ wire d ∧ wire c ≠ wire e ∧ wire d ≠ wire e := by
  classical
  let E := (Cut.essential (M := 13) 13 ∅ gs c ∪ Cut.essential (M := 13) 13 ∅ gs d) ∪
    Cut.essential (M := 13) 13 ∅ gs e
  have hlabel (i : ℕ) (p : Fin 13) (hp : p ∈ Cut.essential (M := 13) 13 ∅ gs i) :
      label p = wire i :=
    (hraw p).symm.trans (ha i p.val (Ancestry.depends_mem ∅ gs i p (Finset.mem_filter.mp hp).2))
  have him : E.image label ⊆ {wire c, wire d, wire e} := by
    intro z hz
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
    rcases Finset.mem_union.mp hp with hp | hp
    · rcases Finset.mem_union.mp hp with hp | hp
      · simp [hlabel c p hp]
      · simp [hlabel d p hp]
    · simp [hlabel e p hp]
  have hnot : ¬ (wire c = wire d ∨ wire c = wire e ∨ wire d = wire e) := by
    intro he
    have htwo : (E.image label).card ≤ 2 := by
      have hset : ({wire c, wire d, wire e} : Finset ℕ).card ≤ 2 := by
        rcases he with he | he | he
        · simpa [he] using pair_card_le (wire d) (wire e)
        · simpa [he, Finset.insert_comm] using pair_card_le (wire d) (wire e)
        · simpa [he] using pair_card_le (wire c) (wire e)
      exact (Finset.card_le_card him).trans hset
    have hE : E.card ≤ 7 := by
      have hr := subset_rank label gs.length hcount E
      omega
    apply hn
    apply Support.small_support_exact w _ hc (output_zero gs a c d e w hu) E hE
    intro x y hxy
    have hc' := Cut.essential_supports 13 ∅ gs c x y
      (fun p hp => hxy p (Finset.mem_union_left _ (Finset.mem_union_left _ hp)))
    have hd' := Cut.essential_supports 13 ∅ gs d x y
      (fun p hp => hxy p (Finset.mem_union_left _ (Finset.mem_union_right _ hp)))
    have he' := Cut.essential_supports 13 ∅ gs e x y
      (fun p hp => hxy p (Finset.mem_union_right _ hp))
    simp only [output, hc', hd', he']
  simpa only [not_or] using hnot

lemma fork_other_inputs (gs : List Gate) (wire : ℕ → ℕ)
    (ha : ∀ i j, j ∈ Ancestry.anc gs i → wire j = wire i)
    (c d a b : ℕ) (hav : a < 13 + gs.length) (hbv : b < 13 + gs.length)
    (hac : wire a ≠ wire c) (had : wire a ≠ wire d)
    (hbc : wire b ≠ wire c) (hbd : wire b ≠ wire d)
    (hca : ∀ k, 13 ≤ k → k < 13 + gs.length →
      k ∈ (Ancestry.anc gs c ∪ Ancestry.anc gs d) ∪ Ancestry.anc gs a)
    (hcb : ∀ k, 13 ≤ k → k < 13 + gs.length →
      k ∈ (Ancestry.anc gs c ∪ Ancestry.anc gs d) ∪ Ancestry.anc gs b) :
    a = b ∨ (a < 13 ∧ b < 13) := by
  have hab : 13 ≤ a → a ≤ b := by
    intro hal
    rcases Finset.mem_union.mp (hcb a hal hav) with hh | hh
    · rcases Finset.mem_union.mp hh with hh | hh
      · exact (hac (ha c a hh)).elim
      · exact (had (ha d a hh)).elim
    · exact (Ancestry.anc_bound gs b a hh).1
  have hba : 13 ≤ b → b ≤ a := by
    intro hbl
    rcases Finset.mem_union.mp (hca b hbl hbv) with hh | hh
    · rcases Finset.mem_union.mp hh with hh | hh
      · exact (hbc (ha c b hh)).elim
      · exact (hbd (ha d b hh)).elim
    · exact (Ancestry.anc_bound gs a b hh).1
  by_cases hal : 13 ≤ a
  · left; have h₁ := hab hal; have h₂ := hba (by omega); omega
  · by_cases hbl : 13 ≤ b
    · have hh := hba hbl; omega
    · exact Or.inr ⟨by omega, by omega⟩

end PEqualNP.Outside.L_meta_1024_aux.EarlyCommon

namespace PEqualNP.Outside.L_meta_1024_aux.EarlyCommon

open PEqualNP.CircuitLowerBounds

lemma raw_value (gs : List Gate) (x : Fin 13 → Bool) (i : ℕ) (hi : i < 13) :
    Cut.cutVal 13 ∅ gs x i = x ⟨i, hi⟩ := by
  have h := Cut.cutVal_append_old 13 ∅ [] gs x i (by simpa using hi)
  simpa [Cut.cutVal_nil, Cut.source_eq, hi] using h

lemma raw_and_impossible (gs : List Gate) (c d a b e : ℕ) (ha : a < 13)
    (ob : Bool) (u v : Fin 13) (huv : u ≠ v)
    (hu : ∀ x, Support.Band x → output gs true c d a x = Support.target u x)
    (hv : ∀ x, Support.Band x → output gs ob c b e x = Support.target v x) : False := by
  obtain ⟨x, hx, hux, hvx, hax⟩ := separating_raw u v huv ⟨a, ha⟩
  have hcv : Cut.cutVal 13 ∅ gs x c = false := by
    have he := hv x hx
    rw [hvx] at he
    exact (Bool.or_eq_false_iff.mp he).1
  have he := hu x hx
  simp [output, op, hcv, raw_value gs x a ha, hax, hux] at he

lemma same_private_impossible (gs : List Gate) (oa ob : Bool) (c d a : ℕ)
    (u v : Fin 13) (huv : u ≠ v)
    (hu : ∀ x, Support.Band x → output gs oa c d a x = Support.target u x)
    (hv : ∀ x, Support.Band x → output gs ob c d a x = Support.target v x) : False := by
  cases oa <;> cases ob
  · apply target_not_le u v huv
    intro x hx ht
    exact (hv x hx).symm.trans ((hu x hx).trans ht)
  · apply target_not_le v u huv.symm
    intro x hx ht
    rw [← hv x hx] at ht
    rw [← hu x hx]
    cases hc : Cut.cutVal 13 ∅ gs x c <;>
      cases hd : Cut.cutVal 13 ∅ gs x d <;>
      cases he : Cut.cutVal 13 ∅ gs x a <;> simp_all [output, op]
  · apply target_not_le u v huv
    intro x hx ht
    rw [← hu x hx] at ht
    rw [← hv x hx]
    cases hc : Cut.cutVal 13 ∅ gs x c <;>
      cases hd : Cut.cutVal 13 ∅ gs x d <;>
      cases he : Cut.cutVal 13 ∅ gs x a <;> simp_all [output, op]
  · apply target_not_le u v huv
    intro x hx ht
    exact (hv x hx).symm.trans ((hu x hx).trans ht)

lemma raw_or_impossible (gs : List Gate) (c d a b : ℕ) (ha : a < 13) (hb : b < 13)
    (u v : Fin 13) (huv : u ≠ v)
    (hu : ∀ x, Support.Band x → output gs false c d a x = Support.target u x)
    (hv : ∀ x, Support.Band x → output gs false c d b x = Support.target v x) : False := by
  classical
  let H (x : Fin 13 → Bool) := Cut.cutVal 13 ∅ gs x c || Cut.cutVal 13 ∅ gs x d
  have hcu : ∀ x, Support.Band x → (H x || x ⟨a, ha⟩) = Support.target u x := by
    intro x hx
    simpa [output, op, H, raw_value gs x a ha, Bool.or_assoc] using hu x hx
  have hcv : ∀ x, Support.Band x → (H x || x ⟨b, hb⟩) = Support.target v x := by
    intro x hx
    simpa [output, op, H, raw_value gs x b hb, Bool.or_assoc] using hv x hx
  have hsub : Support.line u \ Support.line v ⊆ {⟨a, ha⟩} := by
    intro p hp
    obtain ⟨x, y, hxy, hne⟩ := FourOrSinks.shared_parent_essential_band u v huv H
      (fun x => x ⟨a, ha⟩) hcu (by
        intro x hx ht
        rw [← hcv x hx, ht]
        simp) (by intro x y hxy ht; exact hxy _ ht) p hp
    have he : p = ⟨a, ha⟩ := by
      by_contra hn
      exact hne (hxy _ (Ne.symm hn))
    simpa using he
  have hcard := Finset.card_le_card hsub
  rw [difference_card u v huv, Finset.card_singleton] at hcard
  omega

lemma shared_generated_impossible (gs : List Gate) (wire : ℕ → ℕ)
    (ha : ∀ i j, j ∈ Ancestry.anc gs i → wire j = wire i)
    (oa ob : Bool) (c d a b : ℕ)
    (hav : a < 13 + gs.length) (hbv : b < 13 + gs.length)
    (hac : wire a ≠ wire c) (had : wire a ≠ wire d)
    (hbc : wire b ≠ wire c) (hbd : wire b ≠ wire d)
    (hca : ∀ k, 13 ≤ k → k < 13 + gs.length →
      k ∈ (Ancestry.anc gs c ∪ Ancestry.anc gs d) ∪ Ancestry.anc gs a)
    (hcb : ∀ k, 13 ≤ k → k < 13 + gs.length →
      k ∈ (Ancestry.anc gs c ∪ Ancestry.anc gs d) ∪ Ancestry.anc gs b)
    (u v : Fin 13) (huv : u ≠ v)
    (hu : ∀ x, Support.Band x → output gs oa c d a x = Support.target u x)
    (hv : ∀ x, Support.Band x → output gs ob c d b x = Support.target v x) : False := by
  rcases fork_other_inputs gs wire ha c d a b hav hbv hac had hbc hbd hca hcb with he | hh
  · subst b
    exact same_private_impossible gs oa ob c d a u v huv hu hv
  · cases oa with
    | true => exact raw_and_impossible gs c d a d b hh.1 ob u v huv hu hv
    | false =>
      cases ob with
      | true => exact raw_and_impossible gs c d b d a hh.2 false v u huv.symm hv hu
      | false => exact raw_or_impossible gs c d a b hh.1 hh.2 u v huv hu hv

end PEqualNP.Outside.L_meta_1024_aux.EarlyCommon

namespace PEqualNP.Outside.L_meta_1024_aux.EarlyCommon

open PEqualNP.CircuitLowerBounds

lemma private_not_raw (gs : List Gate) (oa ob : Bool) (c r s t z : ℕ)
    (u v : Fin 13) (huv : u ≠ v)
    (hu : ∀ x, Support.Band x → output gs oa c r s x = Support.target u x)
    (hv : ∀ x, Support.Band x → output gs ob c t z x = Support.target v x) :
    13 ≤ r ∨ 13 ≤ s := by
  classical
  by_contra! hh
  have hcu : ∀ x, Support.Band x →
      (Cut.cutVal 13 ∅ gs x c || op oa (x ⟨r, hh.1⟩) (x ⟨s, hh.2⟩)) = Support.target u x := by
    intro x hx
    simpa only [output, raw_value gs x r hh.1, raw_value gs x s hh.2] using hu x hx
  have hmono : ∀ x y : Fin 13 → Bool, (∀ p, x p = true → y p = true) →
      op oa (x ⟨r, hh.1⟩) (x ⟨s, hh.2⟩) = true →
      op oa (y ⟨r, hh.1⟩) (y ⟨s, hh.2⟩) = true := by
    intro x y hxy ht
    cases oa with
    | false =>
      rcases Bool.or_eq_true_iff.mp ht with h | h
      · exact Bool.or_eq_true_iff.mpr (Or.inl (hxy _ h))
      · exact Bool.or_eq_true_iff.mpr (Or.inr (hxy _ h))
    | true =>
      obtain ⟨hr, hs⟩ := Bool.and_eq_true_iff.mp ht
      exact Bool.and_eq_true_iff.mpr ⟨hxy _ hr, hxy _ hs⟩
  have hsub : Support.line u \ Support.line v ⊆ {⟨r, hh.1⟩, ⟨s, hh.2⟩} := by
    intro p hp
    obtain ⟨x, y, hxy, hne⟩ := FourOrSinks.shared_parent_essential_band u v huv
      (fun x => Cut.cutVal 13 ∅ gs x c) (fun x => op oa (x ⟨r, hh.1⟩) (x ⟨s, hh.2⟩))
      hcu (by intro x hx ht; rw [← hv x hx]; simp [output, ht]) hmono p hp
    by_contra hm
    have hpr : (⟨r, hh.1⟩ : Fin 13) ≠ p := by
      intro he; apply hm; simp [← he]
    have hps : (⟨s, hh.2⟩ : Fin 13) ≠ p := by
      intro he; apply hm; simp [← he]
    exact hne (by rw [hxy _ hpr, hxy _ hps])
  have hcard := (Finset.card_le_card hsub).trans (pair_card_le _ _)
  rw [difference_card u v huv] at hcard
  omega

lemma full_prefix_ancestors (gs : List Gate) (hlen : gs.length ≤ 5)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (oa : Bool) (c r s : ℕ) (w : Fin 13)
    (hc : ∀ x, Support.Band x → output gs oa c r s x = Support.target w x)
    (hn : ¬ ∀ x, output gs oa c r s x = Support.target w x) :
    ∀ k, 13 ≤ k → k < 13 + gs.length →
      k ∈ (Ancestry.anc gs c ∪ Ancestry.anc gs r) ∪ Ancestry.anc gs s := by
  let g : Gate := ⟨if oa then GateOp.and else GateOp.or, [r, s]⟩
  let code := gs ++ [g]
  let n := 13 + gs.length
  let cc := if c < n then c else n + 1
  have hcc : cc ≠ n := by dsimp [cc]; split_ifs <;> omega
  have hread (x : Fin 13 → Bool) : Cut.cutVal 13 ∅ code x cc = Cut.cutVal 13 ∅ gs x c := by
    rw [Cut.cutVal_snoc, if_neg hcc]
    dsimp [cc]
    split_ifs with hc'
    · rfl
    · rw [FourOrSinks.cut_ge_false gs x (n + 1) (by omega),
        FourOrSinks.cut_ge_false gs x c (by omega)]
  have hval (x : Fin 13 → Bool) :
      (Cut.cutVal 13 ∅ code x cc || Cut.cutVal 13 ∅ code x n) = output gs oa c r s x := by
    rw [hread, Cut.cutVal_snoc]
    cases oa <;> simp [g, n, op, output, GateOp.eval]
  have hcode : ∀ q ∈ code, (q.op = GateOp.and ∨ q.op = GateOp.or) ∧ q.inputs.length ≤ 2 := by
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hg q hq
    · have he : q = g := by simpa using hq
      subst q
      cases oa <;> simp [g]
  have hac : Ancestry.anc code cc = Ancestry.anc gs c := by
    rw [Ancestry.anc_snoc, if_neg hcc]
    dsimp [cc]
    split_ifs with hc'
    · rfl
    · rw [Ancestry.anc_invalid gs (n + 1) (by omega), Ancestry.anc_invalid gs c (by omega)]
  intro k hkl hku
  have he := TwoPairs.all_ancestors code (by simp [code]; omega) hcode w cc n
    (by intro x hx; rw [hval]; exact hc x hx)
    (by intro he; apply hn; intro x; rw [← hval]; exact he x)
    k ⟨hkl, by simp [code]; omega⟩
  rw [hac, Ancestry.anc_snoc, if_pos rfl] at he
  have hkn : k ≠ n := by omega
  simpa [g, hkn, Finset.mem_union, or_assoc] using he

lemma parallel_binary_impossible (gs : List Gate) (hlen : gs.length ≤ 5)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (oa ob : Bool) (c r s t z : ℕ)
    (hr : r < 13 + gs.length) (hs : s < 13 + gs.length)
    (ht : t < 13 + gs.length) (hz : z < 13 + gs.length)
    (u v : Fin 13) (huv : u ≠ v)
    (hu : ∀ x, Support.Band x → output gs oa c r s x = Support.target u x)
    (hv : ∀ x, Support.Band x → output gs ob c t z x = Support.target v x)
    (hupperu : ∀ x, Support.target u x = false → output gs oa c r s x = false)
    (hupperv : ∀ x, Support.target v x = false → output gs ob c t z x = false)
    (hnu : ¬ ∀ x, output gs oa c r s x = Support.target u x)
    (hnv : ¬ ∀ x, output gs ob c t z x = Support.target v x) : False := by
  classical
  obtain ⟨label, wire, hcard, hraw, ha⟩ := Ancestry.components Finset.univ gs
    (fun q hq => (hg q hq).2)
  simp only [Finset.card_univ, Fintype.card_fin] at hcard
  have hdu := distinct_labels gs hlen label wire hcard hraw ha oa c r s u hu hupperu hnu
  have hdv := distinct_labels gs hlen label wire hcard hraw ha ob c t z v hv hupperv hnv
  have hfu := full_prefix_ancestors gs hlen hg oa c r s u hu hnu
  have hfv := full_prefix_ancestors gs hlen hg ob c t z v hv hnv
  let d := max (max r s) (max t z)
  have hrd : r ≤ d := le_trans (Nat.le_max_left r s) (Nat.le_max_left _ _)
  have hsd : s ≤ d := le_trans (Nat.le_max_right r s) (Nat.le_max_left _ _)
  have htd : t ≤ d := le_trans (Nat.le_max_left t z) (Nat.le_max_right _ _)
  have hzd : z ≤ d := le_trans (Nat.le_max_right t z) (Nat.le_max_right _ _)
  have hd : d = r ∨ d = s ∨ d = t ∨ d = z := by dsimp [d]; omega
  have hdlo : 13 ≤ d := by
    rcases private_not_raw gs oa ob c r s t z u v huv hu hv with h | h <;> omega
  have hdhi : d < 13 + gs.length := by dsimp [d]; omega
  have hdnot : d ∉ Ancestry.anc gs c := by
    intro hm
    have he := ha c d hm
    rcases hd with heq | heq | heq | heq
    · rw [heq] at he; exact hdu.1 he.symm
    · rw [heq] at he; exact hdu.2.1 he.symm
    · rw [heq] at he; exact hdv.1 he.symm
    · rw [heq] at he; exact hdv.2.1 he.symm
  have hdu' : d = r ∨ d = s := by
    rcases Finset.mem_union.mp (hfu d hdlo hdhi) with hm | hm
    · rcases Finset.mem_union.mp hm with hm | hm
      · exact (hdnot hm).elim
      · have hh := (Ancestry.anc_bound gs r d hm).1; exact Or.inl (by omega)
    · have hh := (Ancestry.anc_bound gs s d hm).1; exact Or.inr (by omega)
  have hdv' : d = t ∨ d = z := by
    rcases Finset.mem_union.mp (hfv d hdlo hdhi) with hm | hm
    · rcases Finset.mem_union.mp hm with hm | hm
      · exact (hdnot hm).elim
      · have hh := (Ancestry.anc_bound gs t d hm).1; exact Or.inl (by omega)
    · have hh := (Ancestry.anc_bound gs z d hm).1; exact Or.inr (by omega)
  have reorient (o : Bool) (i j : ℕ) (w : Fin 13)
      (hi : i < 13 + gs.length) (hj : j < 13 + gs.length)
      (hdi : d = i ∨ d = j)
      (hlabels : wire c ≠ wire i ∧ wire c ≠ wire j ∧ wire i ≠ wire j)
      (hfull : ∀ k, 13 ≤ k → k < 13 + gs.length →
        k ∈ (Ancestry.anc gs c ∪ Ancestry.anc gs i) ∪ Ancestry.anc gs j)
      (hcorrect : ∀ x, Support.Band x → output gs o c i j x = Support.target w x) :
      ∃ a, a < 13 + gs.length ∧ wire a ≠ wire c ∧ wire a ≠ wire d ∧
        (∀ k, 13 ≤ k → k < 13 + gs.length →
          k ∈ (Ancestry.anc gs c ∪ Ancestry.anc gs d) ∪ Ancestry.anc gs a) ∧
        (∀ x, Support.Band x → output gs o c d a x = Support.target w x) := by
    rcases hdi with he | he
    · subst i
      exact ⟨j, hj, hlabels.2.1.symm, hlabels.2.2.symm, hfull, hcorrect⟩
    · subst j
      refine ⟨i, hi, hlabels.1.symm, hlabels.2.2, ?_, ?_⟩
      · intro k hkl hku
        simpa only [Finset.union_assoc, Finset.union_comm, Finset.union_left_comm] using hfull k hkl hku
      · intro x hx
        simpa only [output, op_comm] using hcorrect x hx
  obtain ⟨a, hav, hac, had, hca, hua⟩ := reorient oa r s u hr hs hdu' hdu hfu hu
  obtain ⟨b, hbv, hbc, hbd, hcb, hvb⟩ := reorient ob t z v ht hz hdv' hdv hfv hv
  exact shared_generated_impossible gs wire ha oa ob c d a b hav hbv hac had hbc hbd hca hcb
    u v huv hua hvb

end PEqualNP.Outside.L_meta_1024_aux.EarlyCommon

namespace PEqualNP.Outside.L_meta_1024_aux.EarlyCommon

open PEqualNP.CircuitLowerBounds

def gateOutput (gs : List Gate) (g : Gate) (c : ℕ) (x : Fin 13 → Bool) : Bool :=
  Cut.cutVal 13 ∅ gs x c || g.op.eval (g.inputs.map fun i => Cut.cutVal 13 ∅ gs x i)

lemma private_binary (gs : List Gate) (hlen : gs.length ≤ 5)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hfanin : g.inputs.length ≤ 2)
    (c : ℕ) (w : Fin 13)
    (hc : ∀ x, Support.Band x → gateOutput gs g c x = Support.target w x)
    (hn : ¬ ∀ x, gateOutput gs g c x = Support.target w x) :
    ∃ a r s, r < 13 + gs.length ∧ s < 13 + gs.length ∧
      ∀ x, gateOutput gs g c x = output gs a c r s x := by
  have hsmall (i j : ℕ) (he : ∀ x, gateOutput gs g c x =
      (Cut.cutVal 13 ∅ gs x i || Cut.cutVal 13 ∅ gs x j)) : False := by
    apply hn
    have hh := TwoPairs.small_pair_exact gs hlen hg w i j
      (by intro x hx; rw [← he]; exact hc x hx)
    intro x
    rw [he, hh]
  cases hins : g.inputs with
  | nil =>
    rcases hop with hop | hop
    · have hh := hc (Support.row w) (Or.inr (Support.row_spec w).1)
      simp [gateOutput, hop, hins, GateOp.eval, (Support.row_spec w).2] at hh
    · exact (hsmall c c (by intro x; simp [gateOutput, hop, hins, GateOp.eval])).elim
  | cons r tail =>
    cases htail : tail with
    | nil =>
      apply False.elim
      apply hsmall c r
      intro x
      rcases hop with hop | hop <;> simp [gateOutput, hop, hins, htail, GateOp.eval]
    | cons s rest =>
      have hrest : rest = [] := by
        simp only [hins, htail, List.length_cons] at hfanin
        exact List.length_eq_zero_iff.mp (by omega)
      have hvalid (i j : ℕ) (hins' : g.inputs = [i, j]) : i < 13 + gs.length := by
        by_contra! hbad
        have hz (x : Fin 13 → Bool) : Cut.cutVal 13 ∅ gs x i = false :=
          FourOrSinks.cut_ge_false gs x i hbad
        rcases hop with hop | hop
        · apply hsmall c c
          intro x
          simp [gateOutput, hins', hop, GateOp.eval, hz]
        · apply hsmall c j
          intro x
          simp [gateOutput, hins', hop, GateOp.eval, hz]
      have hr := hvalid r s (by simp [hins, htail, hrest])
      have hs : s < 13 + gs.length := by
        by_contra! hbad
        have hz (x : Fin 13 → Bool) : Cut.cutVal 13 ∅ gs x s = false :=
          FourOrSinks.cut_ge_false gs x s hbad
        rcases hop with hop | hop
        · apply hsmall c c
          intro x
          simp [gateOutput, hins, htail, hrest, hop, GateOp.eval, hz]
        · apply hsmall c r
          intro x
          simp [gateOutput, hins, htail, hrest, hop, GateOp.eval, hz]
      rcases hop with hop | hop
      · refine ⟨true, r, s, hr, hs, ?_⟩
        intro x
        simp [gateOutput, output, op, hins, htail, hrest, hop, GateOp.eval]
      · refine ⟨false, r, s, hr, hs, ?_⟩
        intro x
        simp [gateOutput, output, op, hins, htail, hrest, hop, GateOp.eval]

lemma parallel_gates_impossible (gs : List Gate) (hlen : gs.length ≤ 5)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (ga gb : Gate)
    (hga : (ga.op = GateOp.and ∨ ga.op = GateOp.or) ∧ ga.inputs.length ≤ 2)
    (hgb : (gb.op = GateOp.and ∨ gb.op = GateOp.or) ∧ gb.inputs.length ≤ 2)
    (c : ℕ) (u v : Fin 13) (huv : u ≠ v)
    (hu : ∀ x, Support.Band x → gateOutput gs ga c x = Support.target u x)
    (hv : ∀ x, Support.Band x → gateOutput gs gb c x = Support.target v x)
    (hupperu : ∀ x, Support.target u x = false → gateOutput gs ga c x = false)
    (hupperv : ∀ x, Support.target v x = false → gateOutput gs gb c x = false)
    (hnu : ¬ ∀ x, gateOutput gs ga c x = Support.target u x)
    (hnv : ¬ ∀ x, gateOutput gs gb c x = Support.target v x) : False := by
  obtain ⟨oa, r, s, hr, hs, hea⟩ := private_binary gs hlen hg ga hga.1 hga.2 c u hu hnu
  obtain ⟨ob, t, z, ht, hz, heb⟩ := private_binary gs hlen hg gb hgb.1 hgb.2 c v hv hnv
  exact parallel_binary_impossible gs hlen hg oa ob c r s t z hr hs ht hz u v huv
    (by intro x hx; rw [← hea]; exact hu x hx)
    (by intro x hx; rw [← heb]; exact hv x hx)
    (by intro x hx; rw [← hea]; exact hupperu x hx)
    (by intro x hx; rw [← heb]; exact hupperv x hx)
    (by intro h; apply hnu; intro x; rw [hea]; exact h x)
    (by intro h; apply hnv; intro x; rw [heb]; exact h x)

lemma early_common_impossible (gs : List Gate) (hlen : gs.length = 5)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (ga gb : Gate)
    (hga : (ga.op = GateOp.and ∨ ga.op = GateOp.or) ∧ ga.inputs.length ≤ 2)
    (hgb : (gb.op = GateOp.and ∨ gb.op = GateOp.or) ∧ gb.inputs.length ≤ 2)
    (c : ℕ) (hc18 : c ≠ 18) (hc19 : c ≠ 19) (u v : Fin 13) (huv : u ≠ v)
    (hu : ∀ x, Support.Band x →
      (Cut.cutVal 13 ∅ ((gs ++ [ga]) ++ [gb]) x c ||
        Cut.cutVal 13 ∅ ((gs ++ [ga]) ++ [gb]) x 18) = Support.target u x)
    (hv : ∀ x, Support.Band x →
      (Cut.cutVal 13 ∅ ((gs ++ [ga]) ++ [gb]) x c ||
        Cut.cutVal 13 ∅ ((gs ++ [ga]) ++ [gb]) x 19) = Support.target v x)
    (hupperu : ∀ x, Support.target u x = false →
      (Cut.cutVal 13 ∅ ((gs ++ [ga]) ++ [gb]) x c ||
        Cut.cutVal 13 ∅ ((gs ++ [ga]) ++ [gb]) x 18) = false)
    (hupperv : ∀ x, Support.target v x = false →
      (Cut.cutVal 13 ∅ ((gs ++ [ga]) ++ [gb]) x c ||
        Cut.cutVal 13 ∅ ((gs ++ [ga]) ++ [gb]) x 19) = false)
    (hnu : ¬ ∀ x,
      (Cut.cutVal 13 ∅ ((gs ++ [ga]) ++ [gb]) x c ||
        Cut.cutVal 13 ∅ ((gs ++ [ga]) ++ [gb]) x 18) = Support.target u x)
    (hnv : ¬ ∀ x,
      (Cut.cutVal 13 ∅ ((gs ++ [ga]) ++ [gb]) x c ||
        Cut.cutVal 13 ∅ ((gs ++ [ga]) ++ [gb]) x 19) = Support.target v x) : False := by
  have hcommon (x : Fin 13 → Bool) : Cut.cutVal 13 ∅ ((gs ++ [ga]) ++ [gb]) x c =
      Cut.cutVal 13 ∅ gs x c := by
    rw [Cut.cutVal_snoc, if_neg (by simpa [hlen] using hc19),
      Cut.cutVal_snoc, if_neg (by simpa [hlen] using hc18)]
  have hfirst (x : Fin 13 → Bool) : Cut.cutVal 13 ∅ ((gs ++ [ga]) ++ [gb]) x 18 =
      Cut.cutVal 13 ∅ (gs ++ [ga]) x 18 := by
    rw [Cut.cutVal_snoc, if_neg (by simp [hlen])]
  have hsecond (x : Fin 13 → Bool) : Cut.cutVal 13 ∅ ((gs ++ [ga]) ++ [gb]) x 19 =
      gb.op.eval (gb.inputs.map fun i => Cut.cutVal 13 ∅ (gs ++ [ga]) x i) := by
    rw [Cut.cutVal_snoc]
    simp [hlen]
  have hnread : 18 ∉ gb.inputs := by
    intro hmem
    rcases hgb.1 with hop | hop
    · apply target_not_le v u huv.symm
      intro x hx htv
      rw [← hv x hx] at htv
      rw [← hu x hx]
      rcases Bool.or_eq_true_iff.mp htv with h | h
      · exact Bool.or_eq_true_iff.mpr (Or.inl h)
      · rw [hsecond, hop] at h
        have hall : ∀ i ∈ gb.inputs, Cut.cutVal 13 ∅ (gs ++ [ga]) x i = true := by
          simpa [GateOp.eval, List.all_eq_true, List.mem_map] using h
        exact Bool.or_eq_true_iff.mpr (Or.inr ((hfirst x).trans (hall 18 hmem)))
    · apply target_not_le u v huv
      intro x hx htu
      rw [← hu x hx] at htu
      rw [← hv x hx]
      rcases Bool.or_eq_true_iff.mp htu with h | h
      · exact Bool.or_eq_true_iff.mpr (Or.inl h)
      · apply Bool.or_eq_true_iff.mpr
        right
        rw [hsecond, hop]
        simp only [GateOp.eval, List.any_eq_true, List.mem_map, exists_exists_and_eq_and, id_eq]
        exact ⟨18, hmem, (hfirst x).symm.trans h⟩
  have hA (x : Fin 13 → Bool) :
      (Cut.cutVal 13 ∅ ((gs ++ [ga]) ++ [gb]) x c ||
        Cut.cutVal 13 ∅ ((gs ++ [ga]) ++ [gb]) x 18) = gateOutput gs ga c x := by
    rw [hcommon, hfirst, Cut.cutVal_snoc]
    simp [hlen, gateOutput]
  have hB (x : Fin 13 → Bool) :
      (Cut.cutVal 13 ∅ ((gs ++ [ga]) ++ [gb]) x c ||
        Cut.cutVal 13 ∅ ((gs ++ [ga]) ++ [gb]) x 19) = gateOutput gs gb c x := by
    rw [hcommon, hsecond]
    unfold gateOutput
    congr 2
    apply List.map_congr_left
    intro i hi
    rw [Cut.cutVal_snoc, if_neg (by
      intro he
      apply hnread
      have he' : i = 18 := by omega
      exact he' ▸ hi)]
  exact parallel_gates_impossible gs (by omega) hg ga gb hga hgb c u v huv
    (by intro x hx; rw [← hA]; exact hu x hx)
    (by intro x hx; rw [← hB]; exact hv x hx)
    (by intro x hx; rw [← hA]; exact hupperu x hx)
    (by intro x hx; rw [← hB]; exact hupperv x hx)
    (by intro h; apply hnu; intro x; rw [hA]; exact h x)
    (by intro h; apply hnv; intro x; rw [hB]; exact h x)

end PEqualNP.Outside.L_meta_1024_aux.EarlyCommon

namespace PEqualNP.Outside.L_meta_1024_aux.EarlyCommon

open PEqualNP.CircuitLowerBounds

lemma prefix_value (gs : List Gate) (hlen : gs.length ≤ 9) (hseven : 7 ≤ gs.length)
    (i : ℕ) (hi20 : i ≠ 20) (hi21 : i ≠ 21) (x : Fin 13 → Bool) :
    Cut.cutVal 13 ∅ gs x i = Cut.cutVal 13 ∅ (gs.take 7) x i := by
  by_cases hi : i < 20
  · exact Cut.cutVal_take 13 ∅ gs x 7 i hseven hi
  · rw [FourOrSinks.cut_ge_false gs x i (by omega),
      FourOrSinks.cut_ge_false (gs.take 7) x i (by simp only [List.length_take]; omega)]

lemma early_common_prefix_impossible (gs : List Gate) (hlen : gs.length ≤ 9)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (c : ℕ) (hc : c ∉ ({18, 19, 20, 21} : Finset ℕ))
    (u v : Fin 13) (huv : u ≠ v)
    (hu : ∀ x, Support.Band x →
      (Cut.cutVal 13 ∅ gs x c || Cut.cutVal 13 ∅ gs x 18) = Support.target u x)
    (hv : ∀ x, Support.Band x →
      (Cut.cutVal 13 ∅ gs x c || Cut.cutVal 13 ∅ gs x 19) = Support.target v x)
    (hupperu : ∀ x, Support.target u x = false →
      (Cut.cutVal 13 ∅ gs x c || Cut.cutVal 13 ∅ gs x 18) = false)
    (hupperv : ∀ x, Support.target v x = false →
      (Cut.cutVal 13 ∅ gs x c || Cut.cutVal 13 ∅ gs x 19) = false)
    (hnu : ¬ ∀ x, (Cut.cutVal 13 ∅ gs x c || Cut.cutVal 13 ∅ gs x 18) = Support.target u x)
    (hnv : ¬ ∀ x, (Cut.cutVal 13 ∅ gs x c || Cut.cutVal 13 ∅ gs x 19) = Support.target v x) : False := by
  have hs : 7 ≤ gs.length := by
    by_contra! hn
    exact TwoPairs.two_pairs_impossible gs (by omega) hg u v huv c 18 c 19 hu hv hnu hnv
  have h5 : 5 < gs.length := by omega
  have h6 : 6 < gs.length := by omega
  have heq : ((gs.take 5 ++ [gs[5]]) ++ [gs[6]]) = gs.take 7 := by
    rw [List.take_concat_get' gs 5 h5, List.take_concat_get' gs 6 h6]
  have hc' : c ≠ 18 ∧ c ≠ 19 ∧ c ≠ 20 ∧ c ≠ 21 := by simpa using hc
  have hp (x : Fin 13 → Bool) (i : ℕ) (hi20 : i ≠ 20) (hi21 : i ≠ 21) :
      Cut.cutVal 13 ∅ ((gs.take 5 ++ [gs[5]]) ++ [gs[6]]) x i = Cut.cutVal 13 ∅ gs x i := by
    rw [heq, ← prefix_value gs hlen hs i hi20 hi21 x]
  exact early_common_impossible (gs.take 5) (by simp only [List.length_take]; omega)
    (fun q hq => hg q (List.mem_of_mem_take hq)) gs[5] gs[6]
    (hg gs[5] (List.getElem_mem h5)) (hg gs[6] (List.getElem_mem h6)) c hc'.1 hc'.2.1 u v huv
    (by intro x hx; rw [hp x c hc'.2.2.1 hc'.2.2.2, hp x 18 (by decide) (by decide)]; exact hu x hx)
    (by intro x hx; rw [hp x c hc'.2.2.1 hc'.2.2.2, hp x 19 (by decide) (by decide)]; exact hv x hx)
    (by intro x hx; rw [hp x c hc'.2.2.1 hc'.2.2.2, hp x 18 (by decide) (by decide)]; exact hupperu x hx)
    (by intro x hx; rw [hp x c hc'.2.2.1 hc'.2.2.2, hp x 19 (by decide) (by decide)]; exact hupperv x hx)
    (by intro h; apply hnu; intro x; rw [← hp x c hc'.2.2.1 hc'.2.2.2, ← hp x 18 (by decide) (by decide)]; exact h x)
    (by intro h; apply hnv; intro x; rw [← hp x c hc'.2.2.1 hc'.2.2.2, ← hp x 19 (by decide) (by decide)]; exact h x)

end PEqualNP.Outside.L_meta_1024_aux.EarlyCommon
