import PEqualNP.MetaComplexity.Helpers.Guard965

/-!
# The guard lemma (L-meta-965): the count; conjecture until checked

The guard circuit of `Guard965` (the original gates, a copy with every line fixed to the set
`Wz`, one AND per product and an OR chain) has line-degree at most 1 and is true only where a
point off the lines of `Wz` and an incident line are on. It is pruned (card 07) and transposed
(recorded L-meta-738); the coefficient of each line, with the points on lines of `Wz` fixed off
(recorded L-meta-669), is counted by the recorded L-meta-782 with `k` the number of points.
-/

namespace PEqualNP.MetaComplexity.Guard965

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Deg3

/-- The recorded statement of L-meta-782 (checked by an outside proof; not imported). -/
def H782 : Prop := ∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true → p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) → ∑ i : Fin m, c i ≤ C.size

theorem castAdd_ne_natAdd {Np Nl : ℕ} (a : Fin Np) (b : Fin Nl) :
    Fin.castAdd Nl a ≠ Fin.natAdd Np b := by
  intro h
  have := congrArg Fin.val h
  simp at this
  omega

theorem natAdd_eq_iff {Np Nl : ℕ} (a b : Fin Nl) : Fin.natAdd Np a = Fin.natAdd Np b ↔ a = b := by
  constructor
  · intro h; apply Fin.ext; have := congrArg Fin.val h; simp at this; exact this
  · rintro rfl; rfl

theorem castAdd_eq_iff {Np Nl : ℕ} (a b : Fin Np) : Fin.castAdd Nl a = Fin.castAdd Nl b ↔ a = b := by
  constructor
  · intro h; apply Fin.ext; have := congrArg Fin.val h; simp at this; exact this
  · rintro rfl; rfl

theorem guard_count (Np Nl Jn : ℕ) (Inc : Fin Np → Fin Nl → Prop) [DecidableRel Inc]
    (Ckt : Circuit) (fa fb : Fin Jn → ℕ) (Wz : Finset (Fin Nl))
    (h669 : H669) (h738 : H738) (h782 : H782)
    (hI : ∀ (pt pt' : Fin Np) (ln ln' : Fin Nl), pt ≠ pt' → ln ≠ ln' →
      ¬ (Inc pt ln ∧ Inc pt ln' ∧ Inc pt' ln ∧ Inc pt' ln'))
    (hmono : Monotone2 Ckt)
    (hdeg : ∀ jd : Fin Jn, (Ckt.lineDegrees (Np + Nl) (Finset.Ico Np (Np + Nl))).getD (fb jd) 0 ≤ 1)
    (hbelow : ∀ (jb : Fin Jn) (zz : Fin (Np + Nl) → Bool),
      (Ckt.wires (List.ofFn zz)).getD (fa jb) false = true →
      (Ckt.wires (List.ofFn zz)).getD (fb jb) false = true →
      ∃ (pa : Fin Np) (lb : Fin Nl), Inc pa lb ∧ zz (Fin.castAdd Nl pa) = true ∧
        zz (Fin.natAdd Np lb) = true)
    (E : Finset (Fin Np × Fin Nl)) (L : Finset (Fin Nl))
    (hE : ∀ e2 ∈ E, Inc e2.1 e2.2 ∧ e2.2 ∉ Wz ∧ (∀ uu ∈ Wz, ¬ Inc e2.1 uu) ∧ ∃ jc : Fin Jn,
      (Ckt.wires (List.ofFn (fun vv : Fin (Np + Nl) => if vv = Fin.castAdd Nl e2.1 then true
        else decide (∃ ww ∈ Wz, vv = Fin.natAdd Np ww)))).getD (fa jc) false = true ∧
      (Ckt.wires (List.ofFn (fun vq : Fin (Np + Nl) => if vq = Fin.castAdd Nl e2.1 then true
        else if vq = Fin.natAdd Np e2.2 then true else false))).getD (fb jc) false = true)
    (hL : ∀ w, w ∈ L ↔ w ∉ Wz) :
    E.card ≤ L.card + 2 * Ckt.size + 2 * Jn := by
  classical
  rcases Nat.eq_zero_or_pos Jn with hJ0 | hJpos
  · subst hJ0
    have : E = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro e he
      obtain ⟨_, _, _, jc, _⟩ := hE e he
      exact jc.elim0
    rw [this, Finset.card_empty]; exact Nat.zero_le _
  have hops : ∀ g ∈ Ckt.gates, g.op = GateOp.and ∨ g.op = GateOp.or := fun g hg => by
    have := (hmono g hg).1; simpa using this
  have hmC : IsMonotoneCircuit Ckt := hops
  set fx : Fin (Np + Nl) → Option Bool := Fin.addCases (motive := fun _ => Option Bool)
    (fun _ => none) (fun l => some (decide (l ∈ Wz))) with hfx
  set fa' : ℕ → ℕ := fun k => if h : k < Jn then fa ⟨k, h⟩ else 0 with hfa'
  set fb' : ℕ → ℕ := fun k => if h : k < Jn then fb ⟨k, h⟩ else 0 with hfb'
  set Hc := guardCkt (Np + Nl) Ckt (d3sFv (Np + Nl) fx) fa' fb' Jn with hHc
  have hHval := guardCkt_val (Np + Nl) Ckt hops fx fa' fb' Jn hJpos
  have hHmono : Monotone2 Hc := guardCkt_mono _ _ _ _ _ _ hmono
  have hHdeg : HasLineDegree (Np + Nl) (Finset.Ico Np (Np + Nl)) Hc 1 := by
    apply guardCkt_deg (Np + Nl) Ckt hops fx fa' fb' Jn hJpos
    · intro i hi hnone
      simp only [Finset.mem_Ico, not_and, not_lt]
      intro hNp
      exfalso
      unfold d3sFv at hnone
      rw [dif_pos hi] at hnone
      have he : (⟨i, hi⟩ : Fin (Np + Nl)) = Fin.natAdd Np ⟨i - Np, by omega⟩ :=
        Fin.ext (by simp; omega)
      rw [he, hfx, Fin.addCases_right] at hnone
      exact absurd hnone (by simp)
    · intro j hj; simp only [hfb', dif_pos hj]; exact hdeg ⟨j, hj⟩
  -- the guard circuit on points and lines
  set hh : (Fin Np → Bool) → (Fin Nl → Bool) → Bool := fun x y =>
    Hc.eval (List.ofFn (Fin.addCases (motive := fun _ => Bool) x y)) with hhdef
  -- the key property: below the incidence function on the points off the lines of Wz
  have hK : ∀ x y, (∀ p, x p = true → ∀ u ∈ Wz, ¬ Inc p u) → hh x y = true →
      ∃ p w, Inc p w ∧ x p = true ∧ y w = true := by
    intro x y hx h
    rw [hhdef] at h
    simp only at h
    rw [hHval] at h
    simp only [decide_eq_true_eq] at h
    obtain ⟨j, hj, hA, hB⟩ := h
    set z := Fin.addCases (motive := fun _ => Bool) x y with hz
    let zz : Fin (Np + Nl) → Bool := fun i => (fx i).getD (z i) || z i
    have hA' := card02_mono (Np + Nl) Ckt (fa' j) hmC _ zz (fun i h => by simp [zz, h]) hA
    have hB' := card02_mono (Np + Nl) Ckt (fb' j) hmC _ zz (fun i h => by simp [zz, h]) hB
    simp only [hfa', hfb', dif_pos hj] at hA' hB'
    obtain ⟨pa, lb, hIn, hpa, hlb⟩ := hbelow ⟨j, hj⟩ zz hA' hB'
    have hpa' : x pa = true := by simpa [zz, hz, hfx] using hpa
    have hlb' : lb ∈ Wz ∨ y lb = true := by simpa [zz, hz, hfx] using hlb
    refine ⟨pa, lb, hIn, hpa', ?_⟩
    rcases hlb' with h | h
    · exact absurd hIn (hx pa hpa' lb h)
    · exact h
  -- prune and transpose
  have hHm : IsMonotoneCircuit Hc := fun g hg => by have := (hHmono g hg).1; simpa using this
  have hHf : ∀ g ∈ Hc.gates, g.inputs.length ≤ 2 := fun g hg => (hHmono g hg).2
  obtain ⟨H, hm', hf', hs', hd', hfun', hreach'⟩ :=
    card07_prune (Np + Nl) (Finset.Ico Np (Np + Nl)) Hc Hc.output hHm hHf
  have hd1 : HasLineDegree (Np + Nl) (Finset.Ico Np (Np + Nl)) H 1 := le_trans hd' hHdeg
  set N1 := Finset.univ.filter (fun w1 : Fin Nl => Relation.ReflTransGen (fun r1 s1 : ℕ =>
      r1 < s1 ∧ ∃ k1 : Fin H.gates.length, s1 = Np + Nl + k1.val ∧ r1 ∈ (H.gates.get k1).inputs)
      (Np + w1.val) H.output) with hN1
  obtain ⟨D1, T1, o1, hDm, hDf, hDs, hDid⟩ := h738 Np Nl H N1 hm' hf' hd1 hreach' (fun w1 => by simp [hN1])
  set phi : Fin Nl → (Fin Np → Bool) → Bool :=
    fun u x => (D1.wires (List.ofFn x)).getD (o1 u) false with hphi
  have hHH : ∀ z : Fin (Np + Nl) → Bool, circuitFun (Np + Nl) H z = Hc.eval (List.ofFn z) :=
    fun z => hfun' z
  have hid : ∀ x y, hh x y = (hh x (fun _ => false) ||
      decide (∃ u1 : Fin Nl, y u1 = true ∧ (u1 ∈ T1 ∨ phi u1 x = true))) := by
    intro x y
    have e1 : ∀ y', hh x y' = H.eval (List.ofFn x ++ List.ofFn y') := by
      intro y'
      rw [← List.ofFn_fin_append, hhdef]
      exact (hHH _).symm
    rw [e1, e1]
    exact hDid x y
  have hid1 : ∀ x w, hh x (fun l => decide (l = w)) =
      (hh x (fun _ => false) || decide (w ∈ T1 ∨ phi w x = true)) := by
    intro x w
    have hiff : (∃ u1 : Fin Nl, decide (u1 = w) = true ∧ (u1 ∈ T1 ∨ phi u1 x = true)) ↔
        (w ∈ T1 ∨ phi w x = true) := by
      constructor
      · rintro ⟨u, hu, h⟩
        simp only [decide_eq_true_eq] at hu
        subst hu
        exact h
      · intro h
        exact ⟨w, by simp, h⟩
    rw [hid x]
    simp only [hiff]
  have hh0 : ∀ y, hh (fun _ => false) y = false := by
    intro y
    cases h : hh (fun _ => false) y
    · rfl
    · obtain ⟨p, w, _, hp, _⟩ := hK _ y (fun p hp => by simp at hp) h
      simp at hp
  have hT1 : ∀ w, w ∉ T1 := by
    intro w hw
    have := hid1 (fun _ => false) w
    rw [hh0, hh0] at this
    simp [hw] at this
  have hphi0 : ∀ w, phi w (fun _ => false) = false := by
    intro w
    have := hid1 (fun _ => false) w
    rw [hh0, hh0] at this
    cases h : phi w (fun _ => false)
    · rfl
    · rw [h] at this; simp at this
  have hphiP : ∀ w x, (∀ p, x p = true → ∀ u ∈ Wz, ¬ Inc p u) → phi w x = true →
      ∃ p, x p = true ∧ Inc p w := by
    intro w x hx h
    have h1 : hh x (fun l => decide (l = w)) = true := by rw [hid1]; simp [h]
    obtain ⟨p, w', hI', hp, hw'⟩ := hK x _ hx h1
    simp only [decide_eq_true_eq] at hw'
    subst hw'
    exact ⟨p, hp, hI'⟩
  have hepP : ∀ p : Fin Np, (∀ u ∈ Wz, ¬ Inc p u) →
      ∀ q, decide (q = p) = true → ∀ u ∈ Wz, ¬ Inc q u := by
    intro p hp q hq
    simp only [decide_eq_true_eq] at hq
    subst hq; exact hp
  have hpt0 : ∀ p : Fin Np, (∀ u ∈ Wz, ¬ Inc p u) →
      hh (fun q => decide (q = p)) (fun _ => false) = false := by
    intro p hp
    cases h : hh (fun q => decide (q = p)) (fun _ => false)
    · rfl
    · obtain ⟨_, w, _, _, hw⟩ := hK _ _ (hepP p hp) h
      simp at hw
  have hpt : ∀ (p : Fin Np) (w : Fin Nl), (∀ u ∈ Wz, ¬ Inc p u) →
      hh (fun q => decide (q = p)) (fun l => decide (l = w)) = phi w (fun q => decide (q = p)) := by
    intro p w hp
    rw [hid1, hpt0 p hp]
    simp [hT1 w]
  -- the pairs of E are accepted at their single point and line
  have hEacc : ∀ e2 ∈ E, hh (fun q => decide (q = e2.1)) (fun l => decide (l = e2.2)) = true := by
    intro e2 he
    obtain ⟨_, _, _, jc, hA, hB⟩ := hE e2 he
    rw [hhdef]
    simp only
    rw [hHval]
    simp only [decide_eq_true_eq]
    refine ⟨jc.val, jc.2, ?_, ?_⟩
    · simp only [hfa', dif_pos jc.2]
      convert hA using 4
      funext i
      induction i using Fin.addCases with
      | left a =>
        simp only [hfx, Fin.addCases_left, Option.getD_none, castAdd_eq_iff]
        by_cases hap : a = e2.1
        · simp [hap]
        · simp only [hap, decide_false, if_false]
          symm
          simp only [decide_eq_false_iff_not, not_exists, not_and]
          intro ww _ h
          exact castAdd_ne_natAdd _ _ h
      | right b =>
        simp only [hfx, Fin.addCases_right, Option.getD_some]
        rw [if_neg (fun h => castAdd_ne_natAdd _ _ h.symm)]
        congr 1
        apply propext
        constructor
        · intro hb; exact ⟨b, hb, rfl⟩
        · rintro ⟨ww, hww, h⟩; rw [natAdd_eq_iff] at h; subst h; exact hww
    · simp only [hfb', dif_pos jc.2]
      convert hB using 4
      funext i
      induction i using Fin.addCases with
      | left a =>
        simp only [Fin.addCases_left, castAdd_eq_iff]
        rw [if_neg (castAdd_ne_natAdd _ _)]
        by_cases hap : a = e2.1 <;> simp [hap]
      | right b =>
        simp only [Fin.addCases_right, natAdd_eq_iff]
        rw [if_neg (fun h => castAdd_ne_natAdd _ _ h.symm)]
        by_cases hbw : b = e2.2 <;> simp [hbw]
  -- the coefficients with the points on lines of Wz fixed off (L-meta-669)
  set Zp : Finset (Fin Np) := Finset.univ.filter (fun p => ¬ ∀ u ∈ Wz, ¬ Inc p u) with hZp
  obtain ⟨gates', r, hg', hlen, heq⟩ := h669 Np D1.gates ∅ Zp (fun g hg => ⟨hDm g hg, hDf g hg⟩)
  set rs : (Fin Np → Bool) → (Fin Np → Bool) := fun x i =>
    if i ∈ (∅ : Finset (Fin Np)) then true else if i ∈ Zp then false else x i with hrs
  have hrsP : ∀ x p, rs x p = true → (∀ u ∈ Wz, ¬ Inc p u) ∧ x p = true := by
    intro x p h
    simp only [hrs, Finset.notMem_empty, if_false] at h
    split_ifs at h with hp
    simp only [hZp, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hp
    exact ⟨hp, h⟩
  have hrs_ep : ∀ p, (∀ u ∈ Wz, ¬ Inc p u) → rs (fun q => decide (q = p)) = fun q => decide (q = p) := by
    intro p hp
    funext q
    simp only [hrs, Finset.notMem_empty, if_false]
    split_ifs with hq
    · simp only [hZp, Finset.mem_filter, Finset.mem_univ, true_and] at hq
      have hqp : q ≠ p := by rintro rfl; exact hq hp
      simp [hqp]
    · rfl
  have hrs_out : ∀ p, ¬ (∀ u ∈ Wz, ¬ Inc p u) → rs (fun q => decide (q = p)) = fun _ => false := by
    intro p hp
    funext q
    simp only [hrs, Finset.notMem_empty, if_false]
    split_ifs with hq
    · rfl
    · simp only [hZp, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hq
      have hqp : q ≠ p := by rintro rfl; exact hp hq
      simp [hqp]
  have hrs0 : rs (fun _ => false) = fun _ => false := by
    funext q; simp only [hrs, Finset.notMem_empty, if_false]; split_ifs <;> rfl
  have hψ : ∀ w, (∃ p, (∀ u ∈ Wz, ¬ Inc p u) ∧ phi w (fun q => decide (q = p)) = true) →
      ∀ x, Circuit.eval ⟨gates', r (o1 w)⟩ (List.ofFn x) = phi w (rs x) := by
    rintro w ⟨p, hp, hph⟩ x
    exact heq (o1 w) ⟨fun q => decide (q = p), fun _ => false, by
      change phi w (rs (fun q => decide (q = p))) ≠ phi w (rs (fun _ => false))
      rw [hrs_ep p hp, hrs0, hph, hphi0]; simp⟩ x
  -- the accepted points of each line
  set A : Fin Nl → Finset (Fin Np) := fun w => Finset.univ.filter (fun p =>
    (∀ u ∈ Wz, ¬ Inc p u) ∧ phi w (fun q => decide (q = p)) = true) with hA
  set W2 := L.filter (fun w => 2 ≤ (A w).card) with hW2
  have hAne : ∀ w ∈ W2, ∃ p, (∀ u ∈ Wz, ¬ Inc p u) ∧ phi w (fun q => decide (q = p)) = true := by
    intro w hw
    have h2 := (Finset.mem_filter.1 hw).2
    obtain ⟨p, hp⟩ := Finset.card_pos.1 (by omega : 0 < (A w).card)
    exact ⟨p, (Finset.mem_filter.1 hp).2⟩
  have hacc : ∀ w ∈ W2, Finset.univ.filter (fun a : Fin Np => ((⟨gates', 0⟩ : Circuit).wires
      (List.ofFn (fun b : Fin Np => decide (b = a)))).getD (r (o1 w)) false = true) = A w := by
    intro w hw
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hA]
    rw [show ((⟨gates', 0⟩ : Circuit).wires (List.ofFn (fun b : Fin Np => decide (b = a)))).getD
        (r (o1 w)) false = Circuit.eval ⟨gates', r (o1 w)⟩ (List.ofFn (fun b => decide (b = a)))
        from rfl, hψ w (hAne w hw)]
    by_cases ha : ∀ u ∈ Wz, ¬ Inc a u
    · rw [hrs_ep a ha]; exact ⟨fun h => ⟨ha, h⟩, fun h => h.2⟩
    · rw [hrs_out a ha, hphi0]; exact ⟨fun h => absurd h (by simp), fun h => absurd h.1 ha⟩
  have hAsub : ∀ w p, p ∈ A w → Inc p w := by
    intro w p hp
    obtain ⟨hpP, hph⟩ := (Finset.mem_filter.1 hp).2
    obtain ⟨p', hp', hI'⟩ := hphiP w _ (hepP p hpP) hph
    simp only [decide_eq_true_eq] at hp'
    subst hp'
    exact hI'
  -- L-meta-782 on the lines of W2
  set m := W2.card with hm
  set ew : Fin m → Fin Nl := fun i => (W2.equivFin.symm i).val with hew
  have hewm : ∀ i, ew i ∈ W2 := fun i => (W2.equivFin.symm i).2
  have hewinj : Function.Injective ew := fun i j h =>
    W2.equivFin.symm.injective (Subtype.ext h)
  have h2 := h782 Np m Np (fun i => Finset.univ.filter (fun p => Inc p (ew i))) ⟨gates', 0⟩
    (fun i => r (o1 (ew i))) (fun i => (A (ew i)).card - 1)
    (by
      intro i j hij
      rw [Finset.card_le_one]
      intro a ha b hb
      simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      by_contra hab
      exact hI a b (ew i) (ew j) hab (fun h => hij (hewinj h)) ⟨ha.1, ha.2, hb.1, hb.2⟩)
    (by
      intro i
      rw [hacc _ (hewm i)]
      exact (Finset.mem_filter.1 (hewm i)).2)
    hg'
    (by
      intro i p hp
      have hp' : p ∈ Finset.univ.filter (fun a : Fin Np => ((⟨gates', 0⟩ : Circuit).wires
          (List.ofFn (fun b : Fin Np => decide (b = a)))).getD (r (o1 (ew i))) false = true) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hp
      rw [hacc _ (hewm i)] at hp'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hAsub _ _ hp')
    (by
      intro i x _ hoff
      change Circuit.eval ⟨gates', r (o1 (ew i))⟩ (List.ofFn x) = false
      rw [hψ _ (hAne _ (hewm i))]
      cases h : phi (ew i) (rs x)
      · rfl
      · obtain ⟨p, hp, hI'⟩ := hphiP _ _ (fun p hp => (hrsP x p hp).1) h
        have hxp := (hrsP x p hp).2
        have := hoff p (by simp [hI'])
        rw [this] at hxp
        exact absurd hxp (by simp))
    (by
      intro i
      have : (A (ew i)).card ≤ Np := by
        calc (A (ew i)).card ≤ (Finset.univ : Finset (Fin Np)).card := Finset.card_le_univ _
          _ = Np := by simp
      omega)
    (by
      intro i
      rw [hacc _ (hewm i)]
      have := (Finset.mem_filter.1 (hewm i)).2
      omega)
  have hsum : ∑ i : Fin m, ((A (ew i)).card - 1) = ∑ w ∈ W2, ((A w).card - 1) := by
    rw [← Finset.sum_coe_sort W2]
    exact Equiv.sum_comp W2.equivFin.symm (fun x => (A x.val).card - 1)
  rw [hsum] at h2
  have h2' : ∑ w ∈ W2, ((A w).card - 1) ≤ D1.size := by
    refine le_trans h2 ?_
    show gates'.length ≤ D1.gates.length
    exact hlen
  -- the count
  have hEsub : E ⊆ L.biUnion (fun w => (A w).image (fun p => (p, w))) := by
    intro e he
    obtain ⟨_, hw, hP, _⟩ := hE e he
    rw [Finset.mem_biUnion]
    refine ⟨e.2, (hL e.2).2 hw, ?_⟩
    rw [Finset.mem_image]
    refine ⟨e.1, ?_, rfl⟩
    simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hP, ?_⟩
    rw [← hpt e.1 e.2 hP]
    exact hEacc e he
  have hEc : E.card ≤ ∑ w ∈ L, (A w).card := by
    refine le_trans (Finset.card_le_card hEsub) (le_trans Finset.card_biUnion_le ?_)
    exact Finset.sum_le_sum (fun w _ => Finset.card_image_le)
  have hsplit : ∑ w ∈ L, (A w).card ≤ L.card + ∑ w ∈ W2, ((A w).card - 1) := by
    calc ∑ w ∈ L, (A w).card ≤ ∑ w ∈ L, (1 + if 2 ≤ (A w).card then (A w).card - 1 else 0) :=
          Finset.sum_le_sum (fun w _ => by split_ifs <;> omega)
      _ = L.card + ∑ w ∈ W2, ((A w).card - 1) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one, hW2,
            Finset.sum_filter]
  -- some line reaches the output when E is not empty
  have hN1 : E.card ≠ 0 → 1 ≤ N1.card := by
    intro hne
    obtain ⟨e, he⟩ := Finset.card_pos.1 (Nat.pos_of_ne_zero hne)
    obtain ⟨_, _, hP, _⟩ := hE e he
    apply Finset.card_pos.2
    refine ⟨e.2, ?_⟩
    simp only [hN1, Finset.mem_filter, Finset.mem_univ, true_and]
    by_contra hnr
    have h8 := card08_unreached (Np + Nl) H (Np + e.2.val)
      (Fin.addCases (motive := fun _ => Bool) (fun q => decide (q = e.1)) (fun l => decide (l = e.2)))
      (Fin.addCases (motive := fun _ => Bool) (fun q => decide (q = e.1)) (fun _ => false)) (by
        intro i hi
        induction i using Fin.addCases with
        | left a => simp
        | right b =>
          have hb : b ≠ e.2 := by
            intro h; apply hi; subst h; rfl
          rw [Fin.addCases_right, Fin.addCases_right]
          exact decide_eq_false hb) hnr
    rw [hHH, hHH] at h8
    have h1 := hEacc e he
    have h0 := hpt0 e.1 hP
    rw [hhdef] at h1 h0
    simp only at h1 h0
    rw [h8] at h1
    rw [h1] at h0
    exact Bool.noConfusion h0
  have hsz := guardCkt_size (Np + Nl) Ckt (d3sFv (Np + Nl) fx) fa' fb' Jn
  rw [← hHc] at hsz
  by_cases hE0 : E.card = 0
  · omega
  · have := hN1 hE0
    omega

/-- The guard lemma, in the recorded statement of L-meta-965. -/
theorem guard_main : ∀ (Np Nl Jn : ℕ) (Inc : Fin Np → Fin Nl → Prop) [DecidableRel Inc] (Ckt : PEqualNP.CircuitLowerBounds.Circuit) (fa fb : Fin Jn → ℕ) (Wz : Finset (Fin Nl)), (∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (T Z : Finset (Fin n)), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (r : ℕ → ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ gates'.length ≤ gates.length ∧ ∀ o : ℕ, (∃ x y : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else y i))) → ∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', r o⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i))) → (∀ (P1 L1 : ℕ) (C1 : PEqualNP.CircuitLowerBounds.Circuit) (N1 : Finset (Fin L1)), PEqualNP.CircuitLowerBounds.IsMonotoneCircuit C1 → (∀ g1 ∈ C1.gates, g1.inputs.length ≤ 2) → PEqualNP.CircuitLowerBounds.HasLineDegree (P1 + L1) (Finset.Ico P1 (P1 + L1)) C1 1 → (∀ j1 : Fin C1.gates.length, Relation.ReflTransGen (fun a1 b1 : ℕ => a1 < b1 ∧ ∃ i1 : Fin C1.gates.length, b1 = P1 + L1 + i1.val ∧ a1 ∈ (C1.gates.get i1).inputs) (P1 + L1 + j1.val) C1.output) → (∀ w1 : Fin L1, w1 ∈ N1 ↔ Relation.ReflTransGen (fun r1 s1 : ℕ => r1 < s1 ∧ ∃ k1 : Fin C1.gates.length, s1 = P1 + L1 + k1.val ∧ r1 ∈ (C1.gates.get k1).inputs) (P1 + w1.val) C1.output) → ∃ (D1 : PEqualNP.CircuitLowerBounds.Circuit) (T1 : Finset (Fin L1)) (o1 : Fin L1 → ℕ), PEqualNP.CircuitLowerBounds.IsMonotoneCircuit D1 ∧ (∀ h1 ∈ D1.gates, h1.inputs.length ≤ 2) ∧ D1.size + N1.card ≤ C1.size + 1 ∧ ∀ (x1 : Fin P1 → Bool) (y1 : Fin L1 → Bool), C1.eval (List.ofFn x1 ++ List.ofFn y1) = (C1.eval (List.ofFn x1 ++ List.ofFn (fun v1 : Fin L1 => false)) || decide (∃ u1 : Fin L1, y1 u1 = true ∧ (u1 ∈ T1 ∨ (D1.wires (List.ofFn x1)).getD (o1 u1) false = true)))) → (∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true → p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) → ∑ i : Fin m, c i ≤ C.size) → (∀ (pt pt' : Fin Np) (ln ln' : Fin Nl), pt ≠ pt' → ln ≠ ln' → ¬ (Inc pt ln ∧ Inc pt ln' ∧ Inc pt' ln ∧ Inc pt' ln')) → PEqualNP.MetaComplexity.Monotone2 Ckt → (∀ jd : Fin Jn, (Ckt.lineDegrees (Np + Nl) (Finset.Ico Np (Np + Nl))).getD (fb jd) 0 ≤ 1) → (∀ (jb : Fin Jn) (zz : Fin (Np + Nl) → Bool), (Ckt.wires (List.ofFn zz)).getD (fa jb) false = true → (Ckt.wires (List.ofFn zz)).getD (fb jb) false = true → ∃ (pa : Fin Np) (lb : Fin Nl), Inc pa lb ∧ zz (Fin.castAdd Nl pa) = true ∧ zz (Fin.natAdd Np lb) = true) → (Finset.univ.filter (fun e2 : Fin Np × Fin Nl => Inc e2.1 e2.2 ∧ e2.2 ∉ Wz ∧ (∀ uu ∈ Wz, ¬ Inc e2.1 uu) ∧ ∃ jc : Fin Jn, (Ckt.wires (List.ofFn (fun vv : Fin (Np + Nl) => if vv = Fin.castAdd Nl e2.1 then true else decide (∃ ww ∈ Wz, vv = Fin.natAdd Np ww)))).getD (fa jc) false = true ∧ (Ckt.wires (List.ofFn (fun vq : Fin (Np + Nl) => if vq = Fin.castAdd Nl e2.1 then true else if vq = Fin.natAdd Np e2.2 then true else false))).getD (fb jc) false = true)).card ≤ (Finset.univ.filter (fun lc : Fin Nl => lc ∉ Wz)).card + 2 * Ckt.size + 2 * Jn := by
  intro Np Nl Jn Inc _ Ckt fa fb Wz h669 h738 h782 hI hmono hdeg hbelow
  exact guard_count Np Nl Jn Inc Ckt fa fb Wz h669 h738 h782 hI hmono hdeg hbelow _ _
    (fun e2 he => (Finset.mem_filter.1 he).2) (fun w => by simp)

end PEqualNP.MetaComplexity.Guard965
