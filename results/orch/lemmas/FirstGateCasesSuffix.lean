namespace PEqualNP.Outside.L_meta_2592_aux.FirstGateCases

open PEqualNP.Outside.L_meta_2592.Signed
open PEqualNP.Outside.L_meta_2592_aux.PairSeparation
open PEqualNP.Outside.L_meta_2592_aux.FirstGate

lemma zero_cofactor_nonconstant (v : Fin 10) :
    ∃ x y : Fin 10 → Bool, pet (Function.update x v false) ≠
      pet (Function.update y v false) := by
  obtain ⟨u, hu⟩ : ∃ u : Fin 10, u ≠ v := by
    by_cases hv : v = 0
    · exact ⟨1, by simp [hv]⟩
    · exact ⟨0, Ne.symm hv⟩
  obtain ⟨x, hx⟩ := cofactorKeepsOtherInput u v hu false
  let x0 := Function.update (Function.update x v false) u false
  let x1 := Function.update (Function.update x v false) u true
  have h0 : Function.update x0 v false = x0 := by
    funext i
    by_cases hi : i = v
    · subst i
      simp [x0, hu.symm]
    · simp [hi]
  have h1 : Function.update x1 v false = x1 := by
    funext i
    by_cases hi : i = v
    · subst i
      simp [x1, hu.symm]
    · simp [hi]
  exact ⟨x0, x1, by simpa [h0, h1, x0, x1] using hx⟩

lemma source_second_reader (D : U2Circuit) (hmin : IsMinU2 pet D)
    (h0 : 0 < D.gates.length) (v u : Fin 10) (pv pu : Bool) (hne : v ≠ u)
    (hg0 : ∀ x : Fin 10 → Bool,
      u2Val D.gates x 10 = ((u2Val D.gates x v.val != pv) &&
        (u2Val D.gates x u.val != pu))) :
    ∃ k, ∃ hk : k < D.gates.length, 0 < k ∧
      (D.gates[k].a = v.val ∨ D.gates[k].b = v.val) := by
  classical
  by_contra hn
  have hno : ∀ k (hk : k < D.gates.length), 0 < k →
      D.gates[k].a ≠ v.val ∧ D.gates[k].b ≠ v.val := by
    intro k hk hpos
    constructor
    · intro he
      exact hn ⟨k, hk, hpos, Or.inl he⟩
    · intro he
      exact hn ⟨k, hk, hpos, Or.inr he⟩
  have hc := single_fanout_first_gate hmin h0 v u pv pu hne hg0
    (output_not_input D hmin v) hno
  obtain ⟨x, hx⟩ := cofactorKeepsOtherInput v u hne pu
  exact hx (hc x)

def ZeroFloor : Prop :=
  ∀ (v : Fin 10) (s : ℕ), HasU2Size (fun x => pet (Function.update x v false)) s → 15 ≤ s

lemma opposite_impossible (floor : ZeroFloor) (D : U2Circuit) (hmin : IsMinU2 pet D)
    (small : D.gates.length ≤ 17) (h0 : 0 < D.gates.length) (v : Fin 10) (p : Bool)
    (hr0 : (D.gates[0].a = v.val ∧ D.gates[0].pa = p) ∨
      (D.gates[0].b = v.val ∧ D.gates[0].pb = p))
    (j : ℕ) (hj : j < D.gates.length) (hpos : 0 < j)
    (hr1 : (D.gates[j].a = v.val ∧ D.gates[j].pa = !p) ∨
      (D.gates[j].b = v.val ∧ D.gates[j].pb = !p)) : False := by
  obtain ⟨s, hs, hc⟩ := elim_ge_3_opp hmin h0 v p hr0 j hj hpos hr1 false
    (zero_cofactor_nonconstant v)
  have hf := floor v s hc
  omega

lemma same_positive_impossible (floor : ZeroFloor) (D : U2Circuit)
    (hmin : IsMinU2 pet D) (small : D.gates.length ≤ 17)
    (h0 : 0 < D.gates.length) (v : Fin 10)
    (hr0 : (D.gates[0].a = v.val ∧ D.gates[0].pa = false) ∨
      (D.gates[0].b = v.val ∧ D.gates[0].pb = false))
    (j : ℕ) (hj : j < D.gates.length) (hpos : 0 < j)
    (hr1 : (D.gates[j].a = v.val ∧ D.gates[j].pa = false) ∨
      (D.gates[j].b = v.val ∧ D.gates[j].pb = false)) : False := by
  obtain ⟨s, hs, hc⟩ := elim_ge_4_same hmin h0 v false hr0 j hj hpos hr1
    (zero_cofactor_nonconstant v)
  have hf := floor v s hc
  omega

lemma source_negative (floor : ZeroFloor) (D : U2Circuit) (hmin : IsMinU2 pet D)
    (small : D.gates.length ≤ 17) (h0 : 0 < D.gates.length)
    (v u : Fin 10) (pv pu : Bool) (hne : v ≠ u)
    (hr0 : (D.gates[0].a = v.val ∧ D.gates[0].pa = pv) ∨
      (D.gates[0].b = v.val ∧ D.gates[0].pb = pv))
    (hg0 : ∀ x : Fin 10 → Bool,
      u2Val D.gates x 10 = ((u2Val D.gates x v.val != pv) &&
        (u2Val D.gates x u.val != pu))) : pv = true := by
  cases pv
  · obtain ⟨j, hj, hpos, hr⟩ := source_second_reader D hmin h0 v u false pu hne hg0
    exfalso
    rcases hr with ha | hb
    · cases hp : D.gates[j].pa
      · exact same_positive_impossible floor D hmin small h0 v hr0 j hj hpos
          (Or.inl ⟨ha, hp⟩)
      · exact opposite_impossible floor D hmin small h0 v false hr0 j hj hpos
          (Or.inl ⟨ha, hp⟩)
    · cases hp : D.gates[j].pb
      · exact same_positive_impossible floor D hmin small h0 v hr0 j hj hpos
          (Or.inr ⟨hb, hp⟩)
      · exact opposite_impossible floor D hmin small h0 v false hr0 j hj hpos
          (Or.inr ⟨hb, hp⟩)
  · rfl

lemma first_gate_negative (floor : ZeroFloor) (D : U2Circuit) (hmin : IsMinU2 pet D)
    (small : D.gates.length ≤ 17) (h0 : 0 < D.gates.length) :
    D.gates[0].pa = true ∧ D.gates[0].pb = true := by
  let v : Fin 10 := ⟨D.gates[0].a, by have := (hmin.1.1 0 h0).1; omega⟩
  let u : Fin 10 := ⟨D.gates[0].b, by have := (hmin.1.1 0 h0).2; omega⟩
  have hne : v ≠ u := by
    intro he
    exact min_no_self hmin 0 h0 (congrArg Fin.val he)
  have hg0 : ∀ x : Fin 10 → Bool,
      u2Val D.gates x 10 = ((u2Val D.gates x v.val != D.gates[0].pa) &&
        (u2Val D.gates x u.val != D.gates[0].pb)) := by
    intro x
    have h := u2Val_gate D.gates x 0 h0 (hmin.1.1 0 h0).1 (hmin.1.1 0 h0).2
    simpa [v, u] using h
  constructor
  · exact source_negative floor D hmin small h0 v u D.gates[0].pa D.gates[0].pb hne
      (Or.inl ⟨rfl, rfl⟩) hg0
  · apply source_negative floor D hmin small h0 u v D.gates[0].pb D.gates[0].pa hne.symm
      (Or.inr ⟨rfl, rfl⟩)
    intro x
    rw [hg0 x, Bool.and_comm]

lemma later_source_negative (floor : ZeroFloor) (D : U2Circuit) (hmin : IsMinU2 pet D)
    (small : D.gates.length ≤ 17) (h0 : 0 < D.gates.length) (v : Fin 10)
    (hr0 : (D.gates[0].a = v.val ∧ D.gates[0].pa = true) ∨
      (D.gates[0].b = v.val ∧ D.gates[0].pb = true))
    (j : ℕ) (hj : j < D.gates.length) (hpos : 0 < j) :
    (D.gates[j].a = v.val → D.gates[j].pa = true) ∧
    (D.gates[j].b = v.val → D.gates[j].pb = true) := by
  constructor
  · intro ha
    cases hp : D.gates[j].pa
    · exact False.elim (opposite_impossible floor D hmin small h0 v true hr0 j hj hpos
        (Or.inl ⟨ha, hp⟩))
    · rfl
  · intro hb
    cases hp : D.gates[j].pb
    · exact False.elim (opposite_impossible floor D hmin small h0 v true hr0 j hj hpos
        (Or.inr ⟨hb, hp⟩))
    · rfl

lemma first_sources_negative_everywhere (floor : ZeroFloor) (D : U2Circuit)
    (hmin : IsMinU2 pet D) (small : D.gates.length ≤ 17) (h0 : 0 < D.gates.length) :
    D.gates[0].pa = true ∧ D.gates[0].pb = true ∧
    ∀ j (hj : j < D.gates.length),
      (D.gates[j].a = D.gates[0].a → D.gates[j].pa = true) ∧
      (D.gates[j].b = D.gates[0].a → D.gates[j].pb = true) ∧
      (D.gates[j].a = D.gates[0].b → D.gates[j].pa = true) ∧
      (D.gates[j].b = D.gates[0].b → D.gates[j].pb = true) := by
  obtain ⟨ha, hb⟩ := first_gate_negative floor D hmin small h0
  refine ⟨ha, hb, ?_⟩
  intro j hj
  by_cases hz : j = 0
  · subst j
    exact ⟨fun _ => ha, fun _ => hb, fun _ => ha, fun _ => hb⟩
  · let v : Fin 10 := ⟨D.gates[0].a, by have := (hmin.1.1 0 h0).1; omega⟩
    let u : Fin 10 := ⟨D.gates[0].b, by have := (hmin.1.1 0 h0).2; omega⟩
    have hv := later_source_negative floor D hmin small h0 v (Or.inl ⟨rfl, ha⟩) j hj
      (by omega)
    have hu := later_source_negative floor D hmin small h0 u (Or.inr ⟨rfl, hb⟩) j hj
      (by omega)
    exact ⟨hv.1, hv.2, hu.1, hu.2⟩

end PEqualNP.Outside.L_meta_2592_aux.FirstGateCases
