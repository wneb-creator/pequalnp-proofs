import AllFiveCost

namespace PEqualNP.Outside.L_meta_1024_aux.NormalResidual
open PEqualNP.CircuitLowerBounds

def Allowed (gs : List Gate) : Prop :=
  ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

def Correct {k : ℕ} (gs : List Gate) (out : Fin k → ℕ) (lineId : Fin k → Fin 13) : Prop :=
  ∀ u (x : Fin 13 → Bool), Support.Band x →
    Global.val gs x (out u) = Support.target (lineId u) x

def Normal {k : ℕ} (gs : List Gate) (out : Fin k → ℕ) (lineId : Fin k → Fin 13) : Prop :=
  ∀ u, Global.val gs (Global.Zof (Global.line (lineId u))) (out u) = false

def Ordinary (gs : List Gate) (o : ℕ) (w : Fin 13) : Prop :=
  ∀ x : Fin 13 → Bool, Global.val gs x o = Support.target w x

def Maximal (budget : ℕ) (W : Finset (Fin 13)) : Prop :=
  ∀ (gs : List Gate) (out : Fin 13 → ℕ), Allowed gs → gs.length ≤ budget →
    Correct gs out id → Normal gs out id →
    (∀ w ∈ W, Ordinary gs (out w) w) →
    ∀ w ∉ W, ¬ Ordinary gs (out w) w

lemma target_complement (w : Fin 13) :
    Support.target w (Global.Zof (Global.line w)) = false := by
  simp only [Support.target, Global.Zof, decide_eq_false_iff_not, decide_eq_true_eq]
  rintro ⟨p, hp, hn⟩
  exact hn hp

lemma paid_family {k : ℕ} (gs : List Gate) (out : Fin 13 → ℕ)
    (hg : Allowed gs) (hcorrect : Correct gs out id) (hnormal : Normal gs out id)
    (W : Finset (Fin 13)) (hW : ∀ w ∈ W, Ordinary gs (out w) w)
    (lineId : Fin k → Fin 13) (hout : ∀ u, lineId u ∉ W) :
    ∃ (cs : List Gate) (co : Fin k → ℕ), cs.length + 3 * W.card ≤ gs.length ∧
      Allowed cs ∧ Correct cs co lineId ∧ Normal cs co lineId := by
  obtain ⟨P, hP, hcount, hwitness⟩ := Charges.ordinary_charge_family gs out W hg hW
  have hop := fun g hm => (hg g hm).1
  have htrue (u : Fin k) (i : ℕ) (hi : i ∈ P) :
      Global.val gs (Global.Zof (Global.line (lineId u))) i = true := by
    obtain ⟨q, hq, hqi⟩ := hwitness (lineId u) (hout u) i hi
    apply Bridge.val_mono gs hop (Global.eof q) (Global.Zof (Global.line (lineId u))) ?_ i hqi
    intro p hp
    have he : p = q := by simpa [Global.eof] using hp
    subst p
    simpa [Global.Zof] using hq
  have hkeep (u : Fin k) : out (lineId u) ∉ P := by
    intro hm
    have hh := htrue u (out (lineId u)) hm
    have hn : Global.val gs (Global.Zof (Global.line (lineId u))) (out (lineId u)) = false :=
      hnormal (lineId u)
    rw [hn] at hh
    exact Bool.noConfusion hh
  let cs := Dead.paidCode 13 P gs
  let co : Fin k → ℕ := fun u => Dead.paidIndex 13 P gs (out (lineId u))
  have heval (u : Fin k) (x : Fin 13 → Bool) :
      Global.val cs x (co u) = Global.val (Sink.transform 13 P gs) x (out (lineId u)) := by
    exact Dead.eval P (Sink.transform 13 P gs) (Dead.transform_noReads 13 P gs) x
      (out (lineId u))
      (by simpa only [Sink.transform_length] using
        (Bridge.output_index gs (out (lineId u)) (lineId u) (hcorrect (lineId u))).2)
      (hkeep u)
  refine ⟨cs, co, ?_, Dead.paid_allowed 13 P gs hg, ?_, ?_⟩
  · have hpbound : P.card ≤ gs.length := by simpa using Finset.card_le_card hP
    have hlen : cs.length = gs.length - P.card :=
      (Dead.paid_length 13 P gs).trans (Cut.unpaid_eq_sub 13 P gs hP)
    rw [hlen]
    omega
  · intro u x hx
    rw [heval u x]
    exact (PrivateSurgery.normal_clamp gs (out (lineId u)) (lineId u) P hg
      (hcorrect (lineId u)) (hnormal (lineId u)) (htrue u)).2 x hx
  · intro u
    rw [heval u]
    exact (PrivateSurgery.normal_clamp gs (out (lineId u)) (lineId u) P hg
      (hcorrect (lineId u)) (hnormal (lineId u)) (htrue u)).1

lemma complement_outside {k : ℕ} (W : Finset (Fin 13)) (lineId : Fin k → Fin 13)
    (himage : Finset.univ.image lineId = Finset.univ \ W) : ∀ u, lineId u ∉ W := by
  intro u
  have hm : lineId u ∈ Finset.univ \ W := by
    rw [← himage]
    exact Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩
  exact (Finset.mem_sdiff.mp hm).2

lemma complete_family {k : ℕ} (cs : List Gate) (co : Fin k → ℕ)
    (lineId : Fin k → Fin 13) (hinj : Function.Injective lineId)
    (W : Finset (Fin 13)) (himage : Finset.univ.image lineId = Finset.univ \ W)
    (hg : Allowed cs) (hcorrect : Correct cs co lineId) (hnormal : Normal cs co lineId)
    (u₀ : Fin k) (hordinary : Ordinary cs (co u₀) (lineId u₀)) :
    ∃ (ds : List Gate) (dout : Fin 13 → ℕ),
      ds.length = cs.length + 3 * W.card ∧ Allowed ds ∧ Correct ds dout id ∧
      Normal ds dout id ∧ (∀ w ∈ W, Ordinary ds (dout w) w) ∧
      Ordinary ds (dout (lineId u₀)) (lineId u₀) := by
  classical
  let ds := AppendLine.appendLines cs W.toList
  have hwitness : ∀ w : Fin 13, ∃ i : ℕ,
      (∀ x : Fin 13 → Bool, Support.Band x → Global.val ds x i = Support.target w x) ∧
      Global.val ds (Global.Zof (Global.line w)) i = false ∧
      ((w ∈ W ∨ w = lineId u₀) → Ordinary ds i w) := by
    intro w
    by_cases hw : w ∈ W
    · obtain ⟨i, _, _, he⟩ := AppendLine.lines_generated cs W.toList w (by simpa using hw)
      exact ⟨i, fun x _ => he x, (he _).trans (target_complement w), fun _ => he⟩
    · have hm : w ∈ Finset.univ.image lineId := by
        rw [himage]
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hw⟩
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hm
      have hv := (Bridge.output_index cs (co u) (lineId u) (hcorrect u)).2
      have heval (x : Fin 13 → Bool) : Global.val ds x (co u) = Global.val cs x (co u) :=
        AppendLine.lines_old cs W.toList x (co u) hv
      refine ⟨co u, fun x hx => (heval x).trans (hcorrect u x hx),
        (heval _).trans (hnormal u), ?_⟩
      rintro (hh | he)
      · exact False.elim (hw hh)
      · have hu : u = u₀ := hinj he
        subst u
        intro x
        exact (heval x).trans (hordinary x)
  choose dout hb hn ho using hwitness
  refine ⟨ds, dout, ?_, AppendLine.lines_allowed cs W.toList hg, hb, hn,
    fun w hw => ho w (Or.inl hw), ho (lineId u₀) (Or.inr rfl)⟩
  rw [AppendLine.lines_length, Finset.length_toList]

lemma residual_no_improvement {k : ℕ} (budget : ℕ) (W : Finset (Fin 13))
    (hmax : Maximal budget W) (lineId : Fin k → Fin 13) (hinj : Function.Injective lineId)
    (himage : Finset.univ.image lineId = Finset.univ \ W)
    (cs : List Gate) (hbudget : cs.length + 3 * W.card ≤ budget) :
    ∀ (ds : List Gate) (dout : Fin k → ℕ), ds.length ≤ cs.length →
      Allowed ds → Correct ds dout lineId → Normal ds dout lineId →
      ∀ u, ¬ Ordinary ds (dout u) (lineId u) := by
  intro ds dout hlen hg hc hn u hu
  obtain ⟨es, eout, helen, heg, hec, hen, heW, heu⟩ :=
    complete_family ds dout lineId hinj W himage hg hc hn u hu
  have hbound : es.length ≤ budget := by omega
  exact hmax es eout heg hbound hec hen heW (lineId u)
    (complement_outside W lineId himage u) heu

lemma maximal_normal_residual {k : ℕ} (gs : List Gate) (out : Fin 13 → ℕ)
    (hg : Allowed gs) (hcorrect : Correct gs out id) (hnormal : Normal gs out id)
    (hsmall : gs.length < 39) (W : Finset (Fin 13))
    (hW : ∀ w ∈ W, Ordinary gs (out w) w) (hmax : Maximal gs.length W)
    (lineId : Fin k → Fin 13) (hinj : Function.Injective lineId)
    (himage : Finset.univ.image lineId = Finset.univ \ W) :
    ∃ (cs : List Gate) (co : Fin k → ℕ), cs.length < 3 * k ∧ Allowed cs ∧
      Correct cs co lineId ∧ Normal cs co lineId ∧
      (∀ (ds : List Gate) (dout : Fin k → ℕ), ds.length ≤ cs.length →
        Allowed ds → Correct ds dout lineId → Normal ds dout lineId →
        ∀ u, ¬ Ordinary ds (dout u) (lineId u)) := by
  obtain ⟨cs, co, hbudget, hcg, hcc, hcn⟩ :=
    paid_family gs out hg hcorrect hnormal W hW lineId (complement_outside W lineId himage)
  have hWcard : W.card ≤ 13 := by simpa using Finset.card_le_univ W
  have hk : k = 13 - W.card := by
    have hh := congrArg Finset.card himage
    rw [Finset.card_image_of_injective _ hinj,
      Finset.card_sdiff_of_subset (Finset.subset_univ W)] at hh
    simpa using hh
  refine ⟨cs, co, by omega, hcg, hcc, hcn, ?_⟩
  exact residual_no_improvement gs.length W hmax lineId hinj himage cs hbudget

end PEqualNP.Outside.L_meta_1024_aux.NormalResidual
