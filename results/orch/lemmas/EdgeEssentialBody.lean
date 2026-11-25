import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2585.EdgeEssential

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2585.EdgeInvisible
open PEqualNP.Outside.L_meta_2585.CircuitMonotone

lemma offGate_incidence_of_edges (P L : ℕ) (I : Fin P → Fin L → Prop) [DecidableRel I]
    (pre post : List Gate) (g : Gate) (out : ℕ)
    (hpre : ∀ h ∈ pre, h.op = GateOp.and ∨ h.op = GateOp.or)
    (hpost : ∀ h ∈ post, h.op = GateOp.and ∨ h.op = GateOp.or)
    (hfun : ∀ x : Fin (P + L) → Bool,
      circuitFun (P + L) (atGate pre post g out) x =
        decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
          x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true))
    (hkeep : ∀ p : Fin P, ∀ l : Fin L, I p l →
      circuitFun (P + L) (offGate pre post out)
        (fun i => decide (i = Fin.castAdd L p ∨ i = Fin.natAdd P l)) = true) :
    ∀ x : Fin (P + L) → Bool,
      circuitFun (P + L) (offGate pre post out) x =
        decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
          x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true) := by
  intro x
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · intro hx
    have hc := offGate_eval_le pre post g out (List.ofFn x) hpost hx
    change circuitFun (P + L) (atGate pre post g out) x = true at hc
    rw [hfun] at hc
    exact of_decide_eq_true hc
  · rintro ⟨p, l, hi, hp, hl⟩
    let e : Fin (P + L) → Bool := fun i =>
      decide (i = Fin.castAdd L p ∨ i = Fin.natAdd P l)
    have he : circuitFun (P + L) (offGate pre post out) e = true := hkeep p l hi
    apply circuitFun_mono (P + L) (offGate pre post out) (offGate_ao pre post out hpre hpost) e x ?_ he
    intro i hei
    rcases of_decide_eq_true hei with rfl | rfl
    · exact hp
    · exact hl


lemma drop_gate_of_function (P L : ℕ) (I : Fin P → Fin L → Prop) [DecidableRel I]
    (pre post : List Gate) (g : Gate) (out : ℕ)
    (hAO : PEqualNP.TopForm.IsAO2 (P + L) (atGate pre post g out))
    (hne : ∃ p l, I p l)
    (hfun : ∀ x : Fin (P + L) → Bool,
      circuitFun (P + L) (atGate pre post g out) x =
        decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
          x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true))
    (hoff : ∀ x : Fin (P + L) → Bool,
      circuitFun (P + L) (offGate pre post out) x =
        decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
          x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true)) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 (P + L) D ∧
      D.size < (atGate pre post g out).size ∧
      (∀ x : Fin (P + L) → Bool,
        circuitFun (P + L) D x =
          decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
            x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true)) := by
  have hpre : ∀ h ∈ pre, h.op = GateOp.and ∨ h.op = GateOp.or := by
    intro h hh
    exact hAO.1 h (List.mem_append_left _ hh)
  have hpost : ∀ h ∈ post, h.op = GateOp.and ∨ h.op = GateOp.or := by
    intro h hh
    exact hAO.1 h (List.mem_append_right _ (List.mem_cons_of_mem _ hh))
  have hf := hoff
  have hfan : ∀ h ∈ (offGate pre post out).gates, h.inputs.length ≤ 2 := by
    intro h hh
    change h ∈ pre ++ ⟨GateOp.or, []⟩ :: post at hh
    rcases List.mem_append.mp hh with hh | hh
    · exact (hAO.2.2 h (List.mem_append_left _ hh)).le
    · rcases List.mem_cons.mp hh with rfl | hh
      · simp
      · exact (hAO.2.2 h (List.mem_append_right _ (List.mem_cons_of_mem _ hh))).le
  have hfalse : circuitFun (P + L) (offGate pre post out) (fun _ => false) = false := by
    rw [hf]
    simp
  have htrue : circuitFun (P + L) (offGate pre post out) (fun _ => true) = true := by
    rw [hf, decide_eq_true_eq]
    obtain ⟨p, l, hi⟩ := hne
    exact ⟨p, l, hi, rfl, rfl⟩
  have hnc : ∃ x y : Fin (P + L) → Bool,
      circuitFun (P + L) (offGate pre post out) x ≠
        circuitFun (P + L) (offGate pre post out) y :=
    ⟨(fun _ => false), (fun _ => true), by rw [hfalse, htrue]; decide⟩
  obtain ⟨D, hD, hsize, hDfun⟩ :=
    PEqualNP.Outside.L_meta_2585.ConstantCleanup.cleanup_withZero (P + L) pre post out
      (offGate_ao pre post out hpre hpost) hfan hnc
  refine ⟨D, hD, ?_, ?_⟩
  · have hs : (PEqualNP.Outside.L_meta_2585.ConstantCleanup.withZero pre post out).size =
        (atGate pre post g out).size := offGate_size pre post g out
    rw [hs] at hsize
    omega
  · intro x
    rw [hDfun]
    exact hf x


lemma least_gate_output_essential (P L : ℕ) (I : Fin P → Fin L → Prop) [DecidableRel I]
    (pre post : List Gate) (g : Gate) (out : ℕ)
    (hAO : PEqualNP.TopForm.IsAO2 (P + L) (atGate pre post g out))
    (hne : ∃ p l, I p l)
    (hfun : ∀ x : Fin (P + L) → Bool,
      circuitFun (P + L) (atGate pre post g out) x =
        decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
          x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true))
    (hmin : ∀ D : Circuit, PEqualNP.TopForm.IsAO2 (P + L) D →
      (∀ x : Fin (P + L) → Bool,
        circuitFun (P + L) D x =
          decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
            x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true)) →
      (atGate pre post g out).size ≤ D.size) :
    ∃ p : Fin P, ∃ l : Fin L, I p l ∧
      circuitFun (P + L) (offGate pre post out)
        (fun i => decide (i = Fin.castAdd L p ∨ i = Fin.natAdd P l)) = false := by
  by_contra h
  have hkeep : ∀ p : Fin P, ∀ l : Fin L, I p l →
      circuitFun (P + L) (offGate pre post out)
        (fun i => decide (i = Fin.castAdd L p ∨ i = Fin.natAdd P l)) = true := by
    intro p l hi
    cases hv : circuitFun (P + L) (offGate pre post out)
        (fun i => decide (i = Fin.castAdd L p ∨ i = Fin.natAdd P l)) with
    | true => rfl
    | false => exact False.elim (h ⟨p, l, hi, hv⟩)
  have hpre : ∀ q ∈ pre, q.op = GateOp.and ∨ q.op = GateOp.or := by
    intro q hq
    exact hAO.1 q (List.mem_append_left _ hq)
  have hpost : ∀ q ∈ post, q.op = GateOp.and ∨ q.op = GateOp.or := by
    intro q hq
    exact hAO.1 q (List.mem_append_right _ (List.mem_cons_of_mem _ hq))
  have hf := offGate_incidence_of_edges P L I pre post g out hpre hpost hfun hkeep
  obtain ⟨D, hD, hsmall, hDf⟩ := drop_gate_of_function P L I pre post g out hAO hne hfun hf
  have hle := hmin D hD hDf
  omega

end PEqualNP.Outside.L_meta_2585.EdgeEssential
