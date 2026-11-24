import PEqualNP.MetaComplexity.Helpers.PlaneAsmLightHyps

/-!
# The conditional assembly for the plane of order 2 with at most one NOT gate: the steps

Conjecture until checked. `restrict_step`: a list for the plane less a point (any point, with
the point still an input) has at least 11 two-wire AND/OR gates (renaming, L-meta-1351, 1352;
restriction, L-meta-1354; L-meta-1046). `good_step`: a reduced list for the plane loses at least
two two-wire gates when its good input is set false (L-meta-1350, then 1332, 1333 or 1347).
Bridges proved here from the definitions: an output of the restricted list is a gate wire;
an AND gate reading an input is no output; a NOT may be replaced by NOT of its first wire.
The facts about the lines are proved by `simp` on the literals, with no `decide` (leg light).
-/

namespace PEqualNP.MetaComplexity.PlaneAsmLight

open PEqualNP.CircuitLowerBounds

/-- The lines of the plane of order 2. -/
abbrev P : Fin 7 → Finset (Fin 7) :=
  ![{0, 1, 3}, {1, 2, 4}, {2, 3, 5}, {3, 4, 6}, {0, 4, 5}, {1, 5, 6}, {0, 2, 6}]

/-- The plane less a point. -/
abbrev Q : Fin 7 → Finset (Fin 6) :=
  ![{0, 2}, {3, 4}, {1, 5}, {0, 1, 3}, {1, 2, 4}, {2, 3, 5}, {0, 4, 5}]

/-- Every line has three points (per line, by `simp` on the literal). -/
theorem P_card : ∀ ic : Fin 7, (P ic).card = 3 := by
  intro ic; fin_cases ic <;> simp [P]
theorem P_sz : ∀ ic : Fin 7, 2 ≤ (P ic).card := fun ic => by rw [P_card ic]; omega
theorem P_pair : ∀ i j : Fin 7, i ≠ j → (P i ∩ P j).card ≤ 1 := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [P] at hij ⊢
theorem P_two : ∀ u : Fin 7, ∃ i1 j1 : Fin 7, i1 ≠ j1 ∧ u ∈ P i1 ∧ u ∈ P j1 := by
  intro u; fin_cases u
  · exact ⟨0, 4, by simp, by simp [P], by simp [P]⟩
  · exact ⟨0, 1, by simp, by simp [P], by simp [P]⟩
  · exact ⟨1, 2, by simp, by simp [P], by simp [P]⟩
  · exact ⟨0, 2, by simp, by simp [P], by simp [P]⟩
  · exact ⟨1, 3, by simp, by simp [P], by simp [P]⟩
  · exact ⟨2, 4, by simp, by simp [P], by simp [P]⟩
  · exact ⟨3, 5, by simp, by simp [P], by simp [P]⟩
theorem P_in : ∀ p : Fin 7, ∃ i0 : Fin 7, p ∈ P i0 ∧ ∃ v0 ∈ P i0, v0 ≠ p := by
  intro p
  obtain ⟨i1, j1, -, h1, -⟩ := P_two p
  exact ⟨i1, h1, Finset.exists_mem_ne (by rw [P_card i1]; omega) p⟩
theorem P_erase : ∀ i p : Fin 7, 2 ≤ ((P i).erase p).card := by
  intro i p
  have h := Finset.pred_card_le_card_erase (s := P i) (a := p)
  rw [P_card i] at h
  omega
theorem P_sum1 : ∑ w : Fin 7, ((P w).card - 1) = 14 := by
  simp only [P_card, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
theorem P_sum : ∑ w : Fin 7, (P w).card = 21 := by
  simp only [P_card, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- The reduced form, as in L-meta-1346, 1347 and 1350. -/
abbrev Red (n m : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ) : Prop :=
  (∀ jr : Fin gates.length, ∃ xr yr : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + jr.val⟩ (List.ofFn xr) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + jr.val⟩ (List.ofFn yr)) ∧ (∀ jr2 : Fin gates.length, ∀ wr : ℕ, wr < n + jr2.val → ∃ xr2 : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + jr2.val⟩ (List.ofFn xr2) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, wr⟩ (List.ofFn xr2)) ∧ (∀ jr3 : Fin gates.length, (∃ oq : Fin m, out oq = n + jr3.val) ∨ ∃ kr : Fin gates.length, ((gates.get kr).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (gates.get kr).inputs.head? = some (n + jr3.val)) ∨ (((gates.get kr).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gates.get kr).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ n + jr3.val ∈ (gates.get kr).inputs)) ∧ (∀ jr4 : Fin gates.length, ((gates.get jr4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gates.get jr4).op = PEqualNP.CircuitLowerBounds.GateOp.or) → ∃ ar br : ℕ, ar ≠ br ∧ (gates.get jr4).inputs = [ar, br])

theorem restrict_step (h1046 : H1046) (h1351 : H1351) (h1352 : H1352) (h1354 : H1354)
    (gl2 : List Gate) (ol2 : Fin 7 → ℕ) (κ2 : Fin 1 → Fin gl2.length)
    (hops2 : ∀ h ∈ gl2, (h.op = GateOp.and ∨ h.op = GateOp.or ∨ h.op = GateOp.not) ∧
      h.inputs.length ≤ 2)
    (hcov2 : ∀ q3 : Fin gl2.length, (gl2.get q3).op = GateOp.not → ∃ r2 : Fin 1, κ2 r2 = q3)
    (p : Fin 7)
    (hout2 : ∀ (o2 : Fin 7) (x2 : Fin 7 → Bool), Circuit.eval ⟨gl2, ol2 o2⟩ (List.ofFn x2) =
      decide (∃ v2 ∈ P o2, v2 ≠ p ∧ x2 v2 = true)) :
    11 ≤ (twoSet gl2).card := by
  obtain ⟨σ, τ, -, hστ⟩ := h1352 p
  obtain ⟨gl3, hop3, hlen3, hev3⟩ := h1351 7 gl2 σ
  obtain ⟨gl4, hop4, hlen4, hev4⟩ := h1354 6 gl3
  have hL3 : gl3.length = gl2.length := len_of_map hop3
  have hL4 : gl4.length = gl3.length := len_of_map hop4
  have hwire : ∀ i : Fin 7, 7 ≤ ol2 i ∧ ol2 i < 7 + gl2.length := by
    intro i
    constructor
    · by_contra hlt
      push_neg at hlt
      obtain ⟨v, hv, hne⟩ := Finset.exists_mem_ne
        (by have := P_erase i p; omega : 1 < ((P i).erase p).card) ⟨ol2 i, hlt⟩
      have h1 := hout2 i (fun u => decide (u = v))
      rw [eval_input _ _ hlt] at h1
      rw [Finset.mem_erase] at hv
      have ht : decide (∃ v2 ∈ P i, v2 ≠ p ∧ decide (v2 = v) = true) = true := by
        simp only [decide_eq_true_eq]
        exact ⟨v, hv.2, hv.1, by simp⟩
      rw [ht] at h1
      simp only [decide_eq_true_eq] at h1
      exact hne h1.symm
    · by_contra hge
      push_neg at hge
      obtain ⟨v, hv⟩ := Finset.card_pos.mp
        (by have := P_erase i p; omega : 0 < ((P i).erase p).card)
      have h1 := hout2 i (fun u => decide (u = v))
      rw [eval_past _ _ (by omega)] at h1
      rw [Finset.mem_erase] at hv
      have ht : decide (∃ v2 ∈ P i, v2 ≠ p ∧ decide (v2 = v) = true) = true := by
        simp only [decide_eq_true_eq]
        exact ⟨v, hv.2, hv.1, by simp⟩
      rw [ht] at h1
      exact Bool.false_ne_true h1
  have hkey : ∀ (q : ℕ) (h4 : q < gl4.length) (h2 : q < gl2.length),
      (gl4[q]).op = (gl2[q]).op ∧ (gl4[q]).inputs.length = (gl2[q]).inputs.length := by
    intro q h4 h2
    have a := get_key hop4 hlen4 q h4 (by omega)
    have b := get_key hop3 hlen3 q (by omega) h2
    exact ⟨a.1.trans b.1, a.2.trans b.2⟩
  have hops4 : ∀ g ∈ gl4, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hg
    have hk := hkey q hq (by omega)
    have := hops2 (gl2[q]'(by omega)) (List.getElem_mem _)
    rw [hk.1, hk.2]
    exact this
  have hcov4 : ∃ ι : Fin 1 → Fin gl4.length, ∀ i : Fin gl4.length,
      (gl4.get i).op = GateOp.not → ∃ j : Fin 1, ι j = i := by
    refine ⟨fun _ => ⟨(κ2 0).val, by have := (κ2 0).isLt; omega⟩, ?_⟩
    intro i hi
    have hk := hkey i.val i.isLt (by omega)
    have hn : (gl2.get ⟨i.val, by omega⟩).op = GateOp.not := by
      simp only [List.get_eq_getElem] at hi ⊢
      rw [← hk.1]
      exact hi
    obtain ⟨r, hr⟩ := hcov2 _ hn
    refine ⟨0, Fin.ext ?_⟩
    rw [Subsingleton.elim r 0] at hr
    simp [hr]
  let out4 : Fin 7 → ℕ := fun o => 6 + (ol2 (τ.symm o) - 7)
  have hout4 : ∀ (o : Fin 7) (x : Fin 6 → Bool), Circuit.eval ⟨gl4, out4 o⟩ (List.ofFn x) =
      decide (∃ v ∈ Q o, x v = true) := by
    intro o x
    obtain ⟨hw1, hw2⟩ := hwire (τ.symm o)
    have hj : ol2 (τ.symm o) - 7 < gl3.length := by omega
    have e1 := hev4 (ol2 (τ.symm o) - 7) x hj
    show Circuit.eval ⟨gl4, 6 + (ol2 (τ.symm o) - 7)⟩ (List.ofFn x) = _
    rw [e1]
    let x7 : Fin 7 → Bool := fun u => if h : u.val < 6 then x ⟨u.val, h⟩ else false
    have hx7 : List.ofFn x ++ [false] = List.ofFn x7 := by
      rw [List.ofFn_succ' x7]
      simp [x7]
    rw [hx7, show 6 + 1 + (ol2 (τ.symm o) - 7) = 7 + (ol2 (τ.symm o) - 7) by omega, hev3,
      show 7 + (ol2 (τ.symm o) - 7) = ol2 (τ.symm o) by omega, hout2]
    have hm := hστ (τ.symm o)
    rw [Equiv.apply_symm_apply] at hm
    have hiff : (∃ v2 ∈ P (τ.symm o), v2 ≠ p ∧ (x7 ∘ σ) v2 = true) ↔ (∃ v ∈ Q o, x v = true) := by
      constructor
      · rintro ⟨v2, hv2, hne, hx⟩
        have hmem : σ v2 ∈ ((P (τ.symm o)).erase p).map σ.toEmbedding :=
          Finset.mem_map_of_mem _ (Finset.mem_erase.mpr ⟨hne, hv2⟩)
        rw [hm, Finset.mem_map] at hmem
        obtain ⟨u, hu, hue⟩ := hmem
        refine ⟨u, hu, ?_⟩
        simp only [Function.comp_apply] at hx
        rw [← hue] at hx
        simpa [x7] using hx
      · rintro ⟨u, hu, hx⟩
        have hmem : Fin.castSuccEmb u ∈ (Q o).map Fin.castSuccEmb := Finset.mem_map_of_mem _ hu
        rw [← hm, Finset.mem_map] at hmem
        obtain ⟨v2, hv2, hve⟩ := hmem
        rw [Finset.mem_erase] at hv2
        refine ⟨v2, hv2.2, hv2.1, ?_⟩
        simp only [Function.comp_apply, Equiv.toEmbedding_apply] at hve ⊢
        rw [hve]
        simpa [x7] using hx
    simp only [hiff]
  have h11 := h1046 gl4 out4 hops4 hcov4 hout4 (twoSet gl4) (twoSet_cov gl4)
  have heq : (twoSet gl4).card = (twoSet gl2).card :=
    twoSet_card_eq gl4 gl2 (by omega) (fun q h1 h2 => by
      have hk := hkey q h1 h2
      unfold Two
      rw [hk.1, hk.2])
  omega

/-- The conclusion shape of L-meta-1332, 1333 and 1347 at the plane, with the point named. -/
abbrev Cut (gl : List Gate) (J : Finset (Fin gl.length)) : Prop :=
  ∃ (p : Fin 7) (gl2 : List Gate) (ol2 : Fin 7 → ℕ) (κ2 : Fin 1 → Fin gl2.length)
    (J2 : Finset (Fin gl2.length)),
    (∀ h ∈ gl2, (h.op = GateOp.and ∨ h.op = GateOp.or ∨ h.op = GateOp.not) ∧
      h.inputs.length ≤ 2) ∧
    (∀ q3 : Fin gl2.length, (gl2.get q3).op = GateOp.not → ∃ r2 : Fin 1, κ2 r2 = q3) ∧
    (∀ q4 : Fin gl2.length, ((gl2.get q4).op = GateOp.and ∨ (gl2.get q4).op = GateOp.or) ∧
      (gl2.get q4).inputs.length = 2 → q4 ∈ J2) ∧
    J2.card + 2 ≤ J.card ∧
    ∀ (o2 : Fin 7) (x2 : Fin 7 → Bool), Circuit.eval ⟨gl2, ol2 o2⟩ (List.ofFn x2) =
      decide (∃ v2 ∈ P o2, v2 ≠ p ∧ x2 v2 = true)

theorem good_step (h1332 : H1332) (h1333 : H1333) (h1347 : H1347) (h1350 : H1350)
    (gl : List Gate) (ol : Fin 7 → ℕ) (κ : Fin 1 → Fin gl.length) (J : Finset (Fin gl.length))
    (hglops : ∀ h ∈ gl, (h.op = GateOp.and ∨ h.op = GateOp.or ∨ h.op = GateOp.not) ∧
      h.inputs.length ≤ 2)
    (hκ : ∀ q3 : Fin gl.length, (gl.get q3).op = GateOp.not → ∃ r2 : Fin 1, κ r2 = q3)
    (hJ : ∀ q4 : Fin gl.length, ((gl.get q4).op = GateOp.and ∨ (gl.get q4).op = GateOp.or) ∧
      (gl.get q4).inputs.length = 2 → q4 ∈ J)
    (hglout : ∀ (o2 : Fin 7) (x2 : Fin 7 → Bool), Circuit.eval ⟨gl, ol o2⟩ (List.ofFn x2) =
      decide (∃ v2 ∈ P o2, x2 v2 = true))
    (hred : Red 7 7 gl ol) : Cut gl J := by
  obtain ⟨p, hcase⟩ := h1350 7 7 P P_sz P_pair P_two gl ol hglops hglout κ hκ hred
  have hlen2 : ∀ a : Fin gl.length, ((gl.get a).op = GateOp.and ∨ (gl.get a).op = GateOp.or) →
      (gl.get a).inputs.length = 2 := by
    intro a ha
    obtain ⟨ar, br, _, h⟩ := hred.2.2.2 a ha
    rw [h]
    rfl
  have caseA : ∀ a b : Fin gl.length, a ≠ b →
      ((gl.get a).op = GateOp.and ∨ (gl.get a).op = GateOp.or) → p.val ∈ (gl.get a).inputs →
      ((gl.get b).op = GateOp.and ∨ (gl.get b).op = GateOp.or) → p.val ∈ (gl.get b).inputs →
      Cut gl J := by
    intro a b hab ha hap hb hbp
    obtain ⟨gl2, ol2, κ2, J2, h1, h2, h3, h4, h5⟩ := h1332 7 7 P P_pair gl ol hglops hglout p
      (P_in p) a b hab ha (hlen2 a ha) hap hb (hlen2 b hb) hbp 1 κ hκ J hJ
    exact ⟨p, gl2, ol2, κ2, J2, h1, h2, h3, h4, h5⟩
  have caseC : ∀ a : Fin gl.length, (gl.get (κ 0)).op = GateOp.not →
      (gl.get (κ 0)).inputs.head? = some p.val →
      ((gl.get a).op = GateOp.and ∨ (gl.get a).op = GateOp.or) → p.val ∈ (gl.get a).inputs →
      Cut gl J := by
    intro a hn hh ha hap
    obtain ⟨gl2, ol2, κ2, J2, h1, h2, h3, h4, h5⟩ := h1347 7 7 P gl ol hglops hglout κ hκ hred p
      hn hh a ha (hlen2 a ha) hap J hJ
    exact ⟨p, gl2, ol2, κ2, J2, h1, h2, h3, h4, h5⟩
  rcases hcase with ⟨a, b, hab, ha, hap, hb, hbp⟩ | ⟨a2, ha2, ha2p⟩ |
      ⟨k, a3, hk, hkp, ha3, ha3p⟩
  · exact caseA a b hab ha hap hb hbp
  · by_cases hoth : ∃ b : Fin gl.length, b ≠ a2 ∧
        ((gl.get b).op = GateOp.and ∨ (gl.get b).op = GateOp.or) ∧ p.val ∈ (gl.get b).inputs
    · obtain ⟨b, hb, hbo, hbp⟩ := hoth
      exact caseA a2 b (Ne.symm hb) (Or.inl ha2) ha2p hbo hbp
    by_cases hN : (gl.get (κ 0)).op = GateOp.not ∧ (gl.get (κ 0)).inputs.head? = some p.val
    · exact caseC a2 hN.1 hN.2 (Or.inl ha2) ha2p
    -- the bridge: the NOT made to list its first wire only, then L-meta-1333
    obtain ⟨g0, hg0⟩ : ∃ g0, g0 = gl.get (κ 0) := ⟨_, rfl⟩
    obtain ⟨gl', hgl'⟩ : ∃ l, l = gl.set (κ 0).val (normNot g0) := ⟨_, rfl⟩
    have hL : gl'.length = gl.length := by rw [hgl', List.length_set]
    have hget : ∀ (j : ℕ) (hj' : j < gl'.length) (hj : j < gl.length),
        gl'[j] = if (κ 0).val = j then normNot g0 else gl[j] := by
      intro j hj' hj
      subst hgl'
      rw [List.getElem_set]
    have hg0j : ∀ (j : ℕ) (hj : j < gl.length), (κ 0).val = j → g0 = gl[j] := by
      intro j hj h
      subst h
      rw [hg0]
      rfl
    have hopsame : ∀ (j : ℕ) (hj' : j < gl'.length) (hj : j < gl.length),
        (gl'[j]).op = (gl[j]).op := by
      intro j hj' hj
      rw [hget j hj' hj]
      split_ifs with h
      · rw [normNot_op, hg0j j hj h]
      · rfl
    have hsameAO : ∀ (j : ℕ) (hj' : j < gl'.length) (hj : j < gl.length),
        (gl[j]).op ≠ GateOp.not → gl'[j] = gl[j] := by
      intro j hj' hj hn
      rw [hget j hj' hj]
      split_ifs with h
      · rw [hg0j j hj h]
        unfold normNot
        rw [if_neg hn]
      · rfl
    have hwires : ∀ (o : ℕ) (x : List Bool), Circuit.eval ⟨gl', o⟩ x = Circuit.eval ⟨gl, o⟩ x := by
      intro o x
      rw [eval_def, eval_def, hgl', foldl_set_same]
      intro hi
      rw [hg0]
      exact same_normNot _
    have hops' : ∀ h ∈ gl', (h.op = GateOp.and ∨ h.op = GateOp.or ∨ h.op = GateOp.not) ∧
        h.inputs.length ≤ 2 := by
      intro h hh
      obtain ⟨j, hj', rfl⟩ := List.getElem_of_mem hh
      have hj : j < gl.length := by omega
      rw [hget j hj' hj]
      split_ifs with hc
      · have hg := hglops g0 (by rw [hg0j j hj hc]; exact List.getElem_mem _)
        unfold normNot
        split_ifs with hn
        · refine ⟨Or.inr (Or.inr rfl), ?_⟩
          show (g0.inputs.take 1).length ≤ 2
          rw [List.length_take]
          omega
        · exact hg
      · exact hglops _ (List.getElem_mem _)
    have hout' : ∀ (o : Fin 7) (x : Fin 7 → Bool), Circuit.eval ⟨gl', ol o⟩ (List.ofFn x) =
        decide (∃ v ∈ P o, x v = true) := by
      intro o x
      rw [hwires]
      exact hglout o x
    have ha2' : a2.val < gl'.length := by have := a2.isLt; omega
    have ha2n : (gl[a2.val]).op ≠ GateOp.not := by
      intro h
      have : (gl.get a2).op = GateOp.not := h
      rw [ha2] at this
      exact GateOp.noConfusion this
    have hk'eq : gl'[a2.val] = gl[a2.val] := hsameAO a2.val ha2' a2.isLt ha2n
    have hk'and : (gl'.get ⟨a2.val, ha2'⟩).op = GateOp.and := by
      simp only [List.get_eq_getElem]
      rw [hk'eq]
      exact ha2
    have hk'len : (gl'.get ⟨a2.val, ha2'⟩).inputs.length = 2 := by
      simp only [List.get_eq_getElem]
      rw [hk'eq]
      exact hlen2 a2 (Or.inl ha2)
    have hk'p : p.val ∈ (gl'.get ⟨a2.val, ha2'⟩).inputs := by
      simp only [List.get_eq_getElem]
      rw [hk'eq]
      exact ha2p
    have honly : ∀ j : Fin gl'.length, p.val ∈ (gl'.get j).inputs → j = ⟨a2.val, ha2'⟩ := by
      intro j hjp
      apply Fin.ext
      show j.val = a2.val
      by_contra hne
      have hj : j.val < gl.length := by omega
      by_cases hjn : (gl[j.val]).op = GateOp.not
      · obtain ⟨r, hr⟩ := hκ ⟨j.val, hj⟩ hjn
        rw [Subsingleton.elim r 0] at hr
        have hr0 : (κ 0).val = j.val := by rw [hr]
        have hgj : gl'.get j = normNot g0 := by
          simp only [List.get_eq_getElem]
          rw [hget _ _ hj, if_pos hr0]
        rw [hgj] at hjp
        have hg0n : g0.op = GateOp.not := by rw [hg0j j.val hj hr0]; exact hjn
        unfold normNot at hjp
        rw [if_pos hg0n] at hjp
        apply hN
        refine ⟨by rw [← hg0]; exact hg0n, ?_⟩
        rw [← hg0]
        revert hjp
        cases g0.inputs with
        | nil => simp
        | cons a t =>
          intro h
          simp at h
          simp [h]
      · have hs := hsameAO j.val j.isLt hj hjn
        simp only [List.get_eq_getElem] at hjp
        rw [hs] at hjp
        have hao := (hglops _ (List.getElem_mem hj)).1
        rcases hao with h | h | h
        · exact hoth ⟨⟨j.val, hj⟩, fun e => hne (congrArg Fin.val e), Or.inl h, hjp⟩
        · exact hoth ⟨⟨j.val, hj⟩, fun e => hne (congrArg Fin.val e), Or.inr h, hjp⟩
        · exact hjn h
    have hnotout : ∀ o1 : Fin 7, ol o1 ≠ 7 + (⟨a2.val, ha2'⟩ : Fin gl'.length).val := by
      intro o1 heq
      obtain ⟨v0, hv0, hv0p⟩ := Finset.exists_mem_ne
        (by have := P_sz o1; omega : 1 < (P o1).card) p
      have h1 := hglout o1 (fun u => decide (u = v0))
      rw [heq] at h1
      have hx : (fun u : Fin 7 => decide (u = v0)) ⟨p.val, p.isLt⟩ = false := by
        simp only [Fin.eta, decide_eq_false_iff_not]
        exact fun h => hv0p h.symm
      rw [eval_and_input_false gl a2.val a2.isLt ha2 p.val p.isLt ha2p _ hx] at h1
      have ht : decide (∃ v ∈ P o1, decide (v = v0) = true) = true := by
        simp only [decide_eq_true_eq]
        exact ⟨v0, hv0, by simp⟩
      rw [ht] at h1
      exact Bool.false_ne_true h1
    let ι' : Fin 1 → Fin gl'.length := fun r => ⟨(κ r).val, by have := (κ r).isLt; omega⟩
    have hcov' : ∀ q : Fin gl'.length, (gl'.get q).op = GateOp.not → ∃ r : Fin 1, ι' r = q := by
      intro q hq
      have hqg : q.val < gl.length := by omega
      have hq' : (gl.get ⟨q.val, hqg⟩).op = GateOp.not := by
        simp only [List.get_eq_getElem] at hq ⊢
        rw [← hopsame q.val q.isLt hqg]
        exact hq
      obtain ⟨r, hr⟩ := hκ _ hq'
      exact ⟨r, Fin.ext (by simp [ι', hr])⟩
    obtain ⟨gl2, ol2, κ2, J2, h1, h2, h3, h4, h5⟩ := h1333 7 7 P P_pair gl' ol hops' hout' p
      (P_in p) ⟨a2.val, ha2'⟩ hk'and hk'len hk'p honly hnotout 1 ι' hcov' (twoSet gl')
      (twoSet_cov gl')
    have hc1 : (twoSet gl').card = (twoSet gl).card :=
      twoSet_card_eq gl' gl hL (fun q h1 h2 => by
        by_cases hqn : (gl[q]).op = GateOp.not
        · unfold Two
          rw [hopsame q h1 h2, hqn]
          constructor
          · rintro ⟨h | h, _⟩ <;> exact GateOp.noConfusion h
          · rintro ⟨h | h, _⟩ <;> exact GateOp.noConfusion h
        · rw [hsameAO q h1 h2 hqn])
    have hc2 := twoSet_sub gl J hJ
    exact ⟨p, gl2, ol2, κ2, J2, h1, h2, h3, by omega, h5⟩
  · obtain ⟨r, hr⟩ := hκ k hk
    rw [Subsingleton.elim r 0] at hr
    exact caseC a3 (by rw [hr]; exact hk) (by rw [hr]; exact hkp) ha3 ha3p

theorem main (h529 : H529) (h1046 : H1046) (h1330 : H1330) (h1332 : H1332) (h1333 : H1333)
    (h1346 : H1346) (h1347 : H1347) (h1350 : H1350) (h1351 : H1351) (h1352 : H1352)
    (h1354 : H1354) : Goal := by
  intro gates out hops hι hout
  obtain ⟨ι, hι⟩ := hι
  by_cases hn : ∃ q : Fin gates.length, (gates.get q).op = GateOp.not
  · obtain ⟨q, hq⟩ := hn
    have hI := twoSet_card_lt gates q hq
    rcases h1346 7 7 P P_sz gates out hops hout ι hι (twoSet gates) (twoSet_cov gates) with
      ⟨c, hc, hdead⟩ | ⟨gl, ol, κ, J, hglops, hκ, hJ, hJI, hglout, hr1, hr2, hr3, hr4⟩
    · have := h1330 h529 7 7 P P_sz P_pair gates out hops hout ι hι c hc hdead
      rw [P_sum] at this
      omega
    · obtain ⟨p, gl2, ol2, κ2, J2, h1, h2, h3, h4, h5⟩ :=
        good_step h1332 h1333 h1347 h1350 gl ol κ J hglops hκ hJ hglout ⟨hr1, hr2, hr3, hr4⟩
      have h11 := restrict_step h1046 h1351 h1352 h1354 gl2 ol2 κ2 h1 h2 p h5
      have := twoSet_sub gl2 J2 h3
      omega
  · have := h529 7 7 P P_pair gates out ?_ hout
    · rw [P_sum1] at this
      exact this
    · intro g hg
      obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hg
      obtain ⟨h | h | h, hl⟩ := hops _ hg
      · exact ⟨Or.inl h, hl⟩
      · exact ⟨Or.inr h, hl⟩
      · exact absurd ⟨⟨q, hq⟩, h⟩ hn

end PEqualNP.MetaComplexity.PlaneAsmLight
