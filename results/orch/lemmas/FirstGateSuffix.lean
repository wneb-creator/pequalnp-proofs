namespace PEqualNP.Outside.L_meta_2592_aux.FirstGate

open PEqualNP.Outside.L_meta_2592.Signed
open PEqualNP.Outside.L_meta_2592_aux.PairSeparation

lemma output_not_input (D : U2Circuit) (hmin : IsMinU2 pet D) (v : Fin 10) (fl : Bool) :
    D.out ≠ Sum.inr (v.val, fl) := by
  intro hout
  obtain ⟨u, hu⟩ : ∃ u : Fin 10, u ≠ v := by
    by_cases hv : v = 0
    · exact ⟨1, by simp [hv]⟩
    · exact ⟨0, Ne.symm hv⟩
  have proj (x : Fin 10 → Bool) : pet x = (x v != fl) := by
    rw [← hmin.2.1 x]
    unfold u2Eval
    rw [hout]
    change (u2Val D.gates x v.val != fl) = _
    rw [u2Val_input D.gates x v.val v.isLt]
  obtain ⟨x, hx⟩ := cofactorKeepsOtherInput u v hu false
  rw [proj, proj] at hx
  simp [Function.update_of_ne hu.symm] at hx

lemma gates_pos (D : U2Circuit) (hmin : IsMinU2 pet D) : 0 < D.gates.length := by
  by_contra hn
  have hnil : D.gates = [] := by
    cases hg : D.gates with
    | nil => rfl
    | cons g gs => simp [hg] at hn
  rcases ho : D.out with c | ⟨w, fl⟩
  · have hz := hmin.2.1 (fun _ => false)
    have ht := hmin.2.1 (fun _ => true)
    simp [u2Eval, ho, refEval, pet] at hz ht
    exact Bool.noConfusion (hz.symm.trans ht)
  · have hw : w < 10 := by
      have h := hmin.1.2
      simpa [refWf, ho, hnil] using h
    exact output_not_input D hmin ⟨w, hw⟩ fl ho

lemma first_input_second_reader (D : U2Circuit) (hmin : IsMinU2 pet D)
    (h0 : 0 < D.gates.length) :
    ∃ k, ∃ hk : k < D.gates.length, 0 < k ∧
      (D.gates[k].a = D.gates[0].a ∨ D.gates[k].b = D.gates[0].a) := by
  classical
  let v : Fin 10 := ⟨D.gates[0].a, by have := (hmin.1.1 0 h0).1; omega⟩
  let u : Fin 10 := ⟨D.gates[0].b, by have := (hmin.1.1 0 h0).2; omega⟩
  have hvu : v ≠ u := by
    intro he
    have hv := congrArg Fin.val he
    exact min_no_self hmin 0 h0 hv
  have hg0 : ∀ x : Fin 10 → Bool,
      u2Val D.gates x 10 =
        ((u2Val D.gates x v.val != D.gates[0].pa) &&
         (u2Val D.gates x u.val != D.gates[0].pb)) := by
    intro x
    have h := u2Val_gate D.gates x 0 h0 (hmin.1.1 0 h0).1 (hmin.1.1 0 h0).2
    simpa [v, u] using h
  by_contra hn
  have hno : ∀ k (hk : k < D.gates.length), 0 < k →
      D.gates[k].a ≠ v.val ∧ D.gates[k].b ≠ v.val := by
    intro k hk hpos
    constructor
    · intro he
      exact hn ⟨k, hk, hpos, Or.inl he⟩
    · intro he
      exact hn ⟨k, hk, hpos, Or.inr he⟩
  have hc := single_fanout_first_gate hmin h0 v u D.gates[0].pa D.gates[0].pb
    hvu hg0 (output_not_input D hmin v) hno
  obtain ⟨x, hx⟩ := cofactorKeepsOtherInput v u hvu D.gates[0].pb
  exact hx (hc x)

lemma zero_restriction_saves_two (D : U2Circuit) (hmin : IsMinU2 pet D) :
    ∃ (v : Fin 10) (s : ℕ), s + 2 ≤ D.gates.length ∧
      HasU2Size (fun x => pet (Function.update x v false)) s := by
  have h0 := gates_pos D hmin
  obtain ⟨k, hk, hkpos, hread⟩ := first_input_second_reader D hmin h0
  let v : Fin 10 := ⟨D.gates[0].a, by have := (hmin.1.1 0 h0).1; omega⟩
  obtain ⟨s, hs, hsize⟩ := elim_ge_2_two hmin v false 0 k h0 hk (by omega)
    (Or.inl rfl) hread
  exact ⟨v, s, hs, hsize⟩

end PEqualNP.Outside.L_meta_2592_aux.FirstGate
