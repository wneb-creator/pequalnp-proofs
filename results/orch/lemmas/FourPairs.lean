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

