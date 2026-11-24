import AllFiveCost

namespace PEqualNP.Outside.L_meta_1024_aux.PrivateSurgery
open PEqualNP.CircuitLowerBounds

lemma rebuild_normal (k : ℕ) (gs : List Gate) (out : Fin k → ℕ)
    (lineId : Fin k → Fin 13) (u₀ : Fin k)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorrect : ∀ u (x : Fin 13 → Bool), Support.Band x →
      Global.val gs x (out u) = Support.target (lineId u) x)
    (hnormal : ∀ u, Global.val gs (Global.Zof (Global.line (lineId u))) (out u) = false)
    (P : Finset ℕ) (hP : P ⊆ Finset.Ico 13 (13 + gs.length)) (hcard : 3 ≤ P.card)
    (hprivate : ∀ i ∈ P, ∀ u, u ≠ u₀ →
      Global.val gs (Global.Zof (Global.line (lineId u))) i = true) :
    ∃ (cs : List Gate) (co : Fin k → ℕ),
      cs.length ≤ gs.length ∧
      (∀ g ∈ cs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      (∀ u (x : Fin 13 → Bool), Support.Band x →
        Global.val cs x (co u) = Support.target (lineId u) x) ∧
      (∀ u, Global.val cs (Global.Zof (Global.line (lineId u))) (co u) = false) ∧
      (∀ x : Fin 13 → Bool, Global.val cs x (co u₀) = Support.target (lineId u₀) x) ∧
      (∀ u, (∀ x : Fin 13 → Bool, Global.val gs x (out u) = Support.target (lineId u) x) →
        ∀ x : Fin 13 → Bool, Global.val cs x (co u) = Support.target (lineId u) x) := by
  classical
  let T := Sink.transform 13 P gs
  let U := Dead.paidCode 13 P gs
  let cs := AppendLine.appendLine U (lineId u₀)
  let co : Fin k → ℕ := fun u => if u = u₀ then 15 + U.length else Dead.paidIndex 13 P gs (out u)
  have hkept (u : Fin k) (hu : u ≠ u₀) : out u ∉ P := by
    intro hp
    have hh := hprivate (out u) hp u hu
    rw [hnormal u] at hh
    exact Bool.noConfusion hh
  have heval (u : Fin k) (hu : u ≠ u₀) (x : Fin 13 → Bool) :
      Global.val U x (Dead.paidIndex 13 P gs (out u)) = Global.val T x (out u) := by
    apply Dead.eval P T (Dead.transform_noReads 13 P gs) x (out u)
      (by simpa [T, Sink.transform_length] using (Bridge.output_index gs (out u) (lineId u) (hcorrect u)).2)
      (hkept u hu)
  have hvalid (u : Fin k) (hu : u ≠ u₀) : Dead.paidIndex 13 P gs (out u) < 13 + U.length :=
    Dead.mapped_valid 13 P T (out u)
      (by simpa [T, Sink.transform_length] using (Bridge.output_index gs (out u) (lineId u) (hcorrect u)).2)
      (hkept u hu)
  refine ⟨cs, co, ?_, AppendLine.allowed U (lineId u₀) (Dead.paid_allowed 13 P gs hg), ?_, ?_, ?_, ?_⟩
  · have hpbound : P.card ≤ gs.length := by simpa using Finset.card_le_card hP
    change (AppendLine.appendLine U (lineId u₀)).length ≤ gs.length
    rw [AppendLine.length]
    have hu : U.length = gs.length - P.card := by
      exact (Dead.paid_length 13 P gs).trans (Cut.unpaid_eq_sub 13 P gs hP)
    rw [hu]
    omega
  · intro u x hx
    by_cases hu : u = u₀
    · subst u
      simpa only [co, if_pos rfl] using AppendLine.eval U (lineId u₀) x
    · change Global.val cs x (if u = u₀ then _ else _) = _
      rw [if_neg hu, AppendLine.old U (lineId u₀) x _ (hvalid u hu), heval u hu x]
      exact (normal_clamp gs (out u) (lineId u) P hg (hcorrect u) (hnormal u)
        (fun i hi => hprivate i hi u hu)).2 x hx
  · intro u
    by_cases hu : u = u₀
    · subst u
      change Global.val cs (Global.Zof (Global.line (lineId u₀)))
        (if u₀ = u₀ then _ else _) = false
      rw [if_pos rfl, AppendLine.eval]
      change Support.target (lineId u₀) (Global.Zof (Support.line (lineId u₀))) = false
      simp [Support.target, Global.Zof]
    · change Global.val cs (Global.Zof (Global.line (lineId u)))
        (if u = u₀ then _ else _) = false
      rw [if_neg hu, AppendLine.old U (lineId u₀) _ _ (hvalid u hu), heval u hu]
      exact (normal_clamp gs (out u) (lineId u) P hg (hcorrect u) (hnormal u)
        (fun i hi => hprivate i hi u hu)).1
  · intro x
    simpa only [co, if_pos rfl] using AppendLine.eval U (lineId u₀) x
  · intro u hu
    exact rebuild_ordinary k gs out lineId u₀ hg hcorrect P hprivate u hu

lemma every_cost_large_of_no_improvement (k : ℕ) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (lineId : Fin k → Fin 13) (hinj : Function.Injective lineId) (out : Fin k → ℕ)
    (hcorrect : ∀ u (x : Fin 13 → Bool), Support.Band x →
      Global.val gs x (out u) = Support.target (lineId u) x)
    (hnormal : ∀ u, Global.val gs (Global.Zof (Global.line (lineId u))) (out u) = false)
    (hno : ∀ (ds : List Gate) (dest : Fin k → ℕ), ds.length ≤ gs.length →
      (∀ g ∈ ds, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
      (∀ u (x : Fin 13 → Bool), Support.Band x →
        Global.val ds x (dest u) = Support.target (lineId u) x) →
      (∀ u, Global.val ds (Global.Zof (Global.line (lineId u))) (dest u) = false) →
      ∀ u, ¬ ∀ x : Fin 13 → Bool, Global.val ds x (dest u) = Support.target (lineId u) x) :
    ∀ u, 5 ≤ FalsePruning.cost gs (out u) := by
  intro u₀
  by_contra hcost
  have hc : FalsePruning.cost gs (out u₀) ≤ 4 := by omega
  obtain ⟨P, hcard, hP, hcontexts⟩ := Certificate.three_contexts gs hg (lineId u₀)
    (out u₀) (hcorrect u₀) hc
  have hprivate : ∀ i ∈ P, ∀ u, u ≠ u₀ →
      Global.val gs (Global.Zof (Global.line (lineId u))) i = true := by
    intro i hi u hu
    obtain ⟨C, hC, hc, hcontext⟩ := hcontexts i hi
    apply context_private gs (out u₀) i (lineId u₀) (fun g hm => (hg g hm).1)
      (hcorrect u₀) C hC hc (fun x hx hf => hcontext x hf hx) (lineId u)
    exact fun he => hu (hinj he)
  obtain ⟨ds, dest, hlen, hdg, hdc, hdn, hdo, _⟩ :=
    rebuild_normal k gs out lineId u₀ hg hcorrect hnormal P hP hcard hprivate
  exact hno ds dest hlen hdg hdc hdn u₀ hdo

end PEqualNP.Outside.L_meta_1024_aux.PrivateSurgery
