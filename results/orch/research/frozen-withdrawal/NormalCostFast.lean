import NormalResidualFast

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

namespace PEqualNP.Outside.L_meta_1024_aux.NormalResidual
open PEqualNP.CircuitLowerBounds

lemma maximal_exists (budget : ℕ) (gs : List Gate) (out : Fin 13 → ℕ)
    (hg : Allowed gs) (hlen : gs.length ≤ budget)
    (hcorrect : Correct gs out id) (hnormal : Normal gs out id) :
    ∃ (cs : List Gate) (co : Fin 13 → ℕ) (W : Finset (Fin 13)),
      Allowed cs ∧ cs.length ≤ budget ∧ Correct cs co id ∧ Normal cs co id ∧
      (∀ w ∈ W, Ordinary cs (co w) w) ∧ Maximal budget W := by
  classical
  let Realizable : Finset (Fin 13) → Prop := fun W =>
    ∃ (cs : List Gate) (co : Fin 13 → ℕ), Allowed cs ∧ cs.length ≤ budget ∧
      Correct cs co id ∧ Normal cs co id ∧ ∀ w ∈ W, Ordinary cs (co w) w
  let choices : Finset (Finset (Fin 13)) := Finset.univ.filter Realizable
  have hempty : (∅ : Finset (Fin 13)) ∈ choices := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, gs, out, hg, hlen, hcorrect, hnormal, by simp⟩
  obtain ⟨W, hW, hgreatest⟩ := Finset.exists_max_image choices Finset.card ⟨∅, hempty⟩
  obtain ⟨cs, co, hcg, hclen, hcc, hcn, hcW⟩ := (Finset.mem_filter.mp hW).2
  refine ⟨cs, co, W, hcg, hclen, hcc, hcn, hcW, ?_⟩
  intro ds dout hdg hdlen hdc hdn hdW w hw hwexact
  have hm : insert w W ∈ choices := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ds, dout, hdg, hdlen, hdc, hdn, ?_⟩
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact hwexact
    · exact hdW v hv
  have hh := hgreatest (insert w W) hm
  rw [Finset.card_insert_of_notMem hw] at hh
  omega

lemma complement_enumeration (W : Finset (Fin 13)) :
    ∃ lineId : Fin (13 - W.card) → Fin 13,
      Function.Injective lineId ∧ Finset.univ.image lineId = Finset.univ \ W := by
  classical
  let V : Finset (Fin 13) := Finset.univ \ W
  have hc : Fintype.card {w // w ∈ V} = 13 - W.card := by
    rw [Fintype.card_coe, Finset.card_sdiff_of_subset (Finset.subset_univ W)]
    rfl
  let e : {w // w ∈ V} ≃ Fin (13 - W.card) := Fintype.equivFinOfCardEq hc
  let lineId : Fin (13 - W.card) → Fin 13 := fun u => (e.symm u).val
  have hinj : Function.Injective lineId := by
    intro a b hab
    exact e.symm.injective (Subtype.ext hab)
  refine ⟨lineId, hinj, ?_⟩
  ext w
  constructor
  · intro hw
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hw
    exact (e.symm u).property
  · intro hw
    refine Finset.mem_image.mpr ⟨e ⟨w, hw⟩, Finset.mem_univ _, ?_⟩
    change (e.symm (e ⟨w, hw⟩)).val = w
    rw [e.symm_apply_apply]

lemma counterexample_has_extremal_residual (gs : List Gate) (out : Fin 13 → ℕ)
    (hg : Allowed gs) (hcorrect : Correct gs out id) (hnormal : Normal gs out id)
    (hsmall : gs.length < 39) :
    ∃ (k : ℕ) (cs : List Gate) (co : Fin k → ℕ) (lineId : Fin k → Fin 13),
      5 ≤ k ∧ k ≤ 13 ∧ Function.Injective lineId ∧ cs.length < 3 * k ∧
      Allowed cs ∧ Correct cs co lineId ∧ Normal cs co lineId ∧
      (∀ (ds : List Gate) (dout : Fin k → ℕ), ds.length ≤ cs.length →
        Allowed ds → Correct ds dout lineId → Normal ds dout lineId →
        ∀ u, ¬ Ordinary ds (dout u) (lineId u)) := by
  obtain ⟨bs, bo, W, hbg, hblen, hbc, hbn, hbW, hmax⟩ :=
    maximal_exists gs.length gs out hg (Nat.le_refl _) hcorrect hnormal
  have hWsmall : W.card ≤ 8 := by
    by_contra hh
    have hbound := FourReduction.nine_ordinary_bound bs bo hbg hbc W (by omega) hbW
    omega
  obtain ⟨lineId, hinj, himage⟩ := complement_enumeration W
  have hmax' : Maximal bs.length W := by
    intro ds dout hdg hdlen hdc hdn hdW
    exact hmax ds dout hdg (hdlen.trans hblen) hdc hdn hdW
  obtain ⟨cs, co, hcslen, hcg, hcc, hcn, hno⟩ :=
    maximal_normal_residual bs bo hbg hbc hbn (by omega) W hbW hmax' lineId hinj himage
  exact ⟨13 - W.card, cs, co, lineId, by omega, by omega, hinj, hcslen, hcg, hcc, hcn, hno⟩

end PEqualNP.Outside.L_meta_1024_aux.NormalResidual

namespace PEqualNP.Outside.L_meta_1024_aux.NormalResidual
open PEqualNP.CircuitLowerBounds

lemma maximal_exotic_cost (gs : List Gate) (out : Fin 13 → ℕ)
    (hg : Allowed gs) (hcorrect : Correct gs out id) (hnormal : Normal gs out id)
    (W : Finset (Fin 13)) (hW : ∀ w ∈ W, Ordinary gs (out w) w)
    (hmax : Maximal gs.length W) :
    ∀ w ∉ W, 5 ≤ FalsePruning.cost gs (out w) := by
  intro w hw
  by_contra hh
  have hc : FalsePruning.cost gs (out w) ≤ 4 := by omega
  obtain ⟨P, hcard, hP, hcontexts⟩ := Certificate.three_contexts gs hg w (out w) (hcorrect w) hc
  have hprivate : ∀ i ∈ P, ∀ v : Fin 13, v ≠ w →
      Global.val gs (Global.Zof (Global.line v)) i = true := by
    intro i hi v hv
    obtain ⟨C, hC, hCc, hctx⟩ := hcontexts i hi
    exact PrivateSurgery.context_private gs (out w) i w (fun g hm => (hg g hm).1)
      (hcorrect w) C hC hCc (fun x hx hf => hctx x hf hx) v hv
  obtain ⟨cs, co, hlen, hcg, hcc, hcn, hcw, hpreserve⟩ :=
    PrivateSurgery.rebuild_normal 13 gs out id w hg hcorrect hnormal P hP hcard hprivate
  exact hmax cs co hcg hlen hcc hcn (fun v hv => hpreserve v (hW v hv)) w hw hcw

lemma counterexample_has_cost_normal_form (gs : List Gate) (out : Fin 13 → ℕ)
    (hg : Allowed gs) (hcorrect : Correct gs out id) (hnormal : Normal gs out id)
    (hsmall : gs.length < 39) :
    ∃ (cs : List Gate) (co : Fin 13 → ℕ) (W : Finset (Fin 13)),
      cs.length ≤ gs.length ∧ Allowed cs ∧ Correct cs co id ∧ Normal cs co id ∧
      W.card ≤ 8 ∧ (∀ w ∈ W, Ordinary cs (co w) w) ∧
      (∀ w ∉ W, ¬ Ordinary cs (co w) w) ∧
      (∀ w ∉ W, 5 ≤ FalsePruning.cost cs (co w)) := by
  obtain ⟨cs, co, W, hcg, hlen, hcc, hcn, hW, hmax⟩ :=
    maximal_exists gs.length gs out hg (Nat.le_refl _) hcorrect hnormal
  have hmax' : Maximal cs.length W := by
    intro ds dout hdg hdlen hdc hdn hdW
    exact hmax ds dout hdg (hdlen.trans hlen) hdc hdn hdW
  have hcard : W.card ≤ 8 := by
    by_contra hh
    have hb := FourReduction.nine_ordinary_bound cs co hcg hcc W (by omega) hW
    omega
  exact ⟨cs, co, W, hlen, hcg, hcc, hcn, hcard, hW,
    hmax' cs co hcg (Nat.le_refl _) hcc hcn hW,
    maximal_exotic_cost cs co hcg hcc hcn W hW hmax'⟩

lemma counterexample_has_cost_residual (gs : List Gate) (out : Fin 13 → ℕ)
    (hg : Allowed gs) (hcorrect : Correct gs out id) (hnormal : Normal gs out id)
    (hsmall : gs.length < 39) :
    ∃ (k : ℕ) (cs : List Gate) (co : Fin k → ℕ) (lineId : Fin k → Fin 13),
      5 ≤ k ∧ k ≤ 13 ∧ Function.Injective lineId ∧ cs.length < 3 * k ∧
      Allowed cs ∧ Correct cs co lineId ∧ Normal cs co lineId ∧
      (∀ u, ¬ Ordinary cs (co u) (lineId u)) ∧
      (∀ u, 5 ≤ FalsePruning.cost cs (co u)) := by
  obtain ⟨k, cs, co, lineId, hklo, hkhi, hinj, hlen, hcg, hcc, hcn, hno⟩ :=
    counterexample_has_extremal_residual gs out hg hcorrect hnormal hsmall
  refine ⟨k, cs, co, lineId, hklo, hkhi, hinj, hlen, hcg, hcc, hcn,
    hno cs co (Nat.le_refl _) hcg hcc hcn, ?_⟩
  exact PrivateSurgery.every_cost_large_of_no_improvement k cs hcg lineId hinj co hcc hcn hno

end PEqualNP.Outside.L_meta_1024_aux.NormalResidual
