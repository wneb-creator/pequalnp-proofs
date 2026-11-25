import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2585.CircuitMonotone

open PEqualNP.CircuitLowerBounds

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l : List ℕ) (f g : ℕ → Bool) (hfg : ∀ u ∈ l, f u = true → g u = true) :
    op.eval (l.map f) = true → op.eval (l.map g) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
    intro hf b hb
    rcases hb with ⟨u, hu, rfl⟩
    exact hfg u hu (hf (f u) ⟨u, hu, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
    rintro ⟨b, ⟨u, hu, rfl⟩, hfu⟩
    exact ⟨g u, ⟨u, hu, rfl⟩, hfg u hu hfu⟩

lemma append_mono (w v : List Bool) (a b : Bool) (hlen : w.length = v.length)
    (h : ∀ i, w.getD i false = true → v.getD i false = true)
    (hab : a = true → b = true) :
    ∀ i, (w ++ [a]).getD i false = true → (v ++ [b]).getD i false = true := by
  intro i hi
  by_cases hlt : i < w.length
  · rw [List.getD_append _ _ _ _ hlt] at hi
    rw [List.getD_append _ _ _ _ (by omega)]
    exact h i hi
  · by_cases heq : i = w.length
    · subst i
      have ha : a = true := by simpa using hi
      simpa [hlen] using hab ha
    · have hle : (w ++ [a]).length ≤ i := by simp; omega
      rw [List.getD_eq_default _ _ hle] at hi
      cases hi

lemma run_mono (gs : List Gate)
    (hao : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w v : List Bool) (hlen : w.length = v.length)
    (h : ∀ i, w.getD i false = true → v.getD i false = true) :
    ∀ i, (run gs w).getD i false = true → (run gs v).getD i false = true := by
  induction gs generalizing w v with
  | nil => exact h
  | cons g gs ih =>
    change ∀ i,
      (run gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD i false = true →
      (run gs (v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)])).getD i false = true
    apply ih (fun g' hg' => hao g' (List.mem_cons_of_mem _ hg'))
    · simpa using hlen
    · apply append_mono w v _ _ hlen h
      apply eval_mono g.op (hao g (by simp))
      intro i _
      exact h i

lemma circuitFun_mono (n : ℕ) (C : Circuit)
    (hao : PEqualNP.EdgeOwnership.AndOrOnly C)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true) :
    PEqualNP.MetaComplexity.circuitFun n C x = true →
      PEqualNP.MetaComplexity.circuitFun n C y = true := by
  apply run_mono C.gates hao (List.ofFn x) (List.ofFn y) (by simp) _ C.output
  intro i hi
  by_cases hin : i < n
  · have hx : i < (List.ofFn x).length := by simpa
    have hy : i < (List.ofFn y).length := by simpa
    rw [List.getD_eq_getElem _ _ hx, List.getElem_ofFn] at hi
    rw [List.getD_eq_getElem _ _ hy, List.getElem_ofFn]
    exact hxy ⟨i, hin⟩ hi
  · have hle : (List.ofFn x).length ≤ i := by simp; omega
    rw [List.getD_eq_default _ _ hle] at hi
    cases hi

lemma ao2_mono (n : ℕ) (C : Circuit) (hao : PEqualNP.TopForm.IsAO2 n C)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true) :
    PEqualNP.MetaComplexity.circuitFun n C x = true →
      PEqualNP.MetaComplexity.circuitFun n C y = true :=
  circuitFun_mono n C hao.1 x y hxy

end PEqualNP.Outside.L_meta_2585.CircuitMonotone

namespace PEqualNP.Outside.L_meta_2585.EdgeInvisible

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2585.CircuitMonotone

def atGate (pre post : List Gate) (g : Gate) (out : ℕ) : Circuit :=
  ⟨pre ++ g :: post, out⟩

def offGate (pre post : List Gate) (out : ℕ) : Circuit :=
  atGate pre post ⟨GateOp.or, []⟩ out

def gateValue (pre : List Gate) (g : Gate) (x : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => (run pre x).getD i false)

lemma run_append (a b : List Gate) (w : List Bool) :
    run (a ++ b) w = run b (run a w) := by
  simp [run, List.foldl_append]

lemma run_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    run (g :: gs) w = run gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

lemma offGate_size (pre post : List Gate) (g : Gate) (out : ℕ) :
    (offGate pre post out).size = (atGate pre post g out).size := by
  simp [offGate, atGate, Circuit.size]

lemma offGate_eval_eq (pre post : List Gate) (g : Gate) (out : ℕ) (x : List Bool)
    (hfalse : gateValue pre g x = false) :
    (offGate pre post out).eval x = (atGate pre post g out).eval x := by
  change (run (pre ++ ⟨GateOp.or, []⟩ :: post) x).getD out false =
    (run (pre ++ g :: post) x).getD out false
  rw [run_append, run_append, run_cons, run_cons]
  change (run post (run pre x ++ [false])).getD out false =
    (run post (run pre x ++ [gateValue pre g x])).getD out false
  rw [hfalse]

lemma offGate_eval_le (pre post : List Gate) (g : Gate) (out : ℕ) (x : List Bool)
    (hpost : ∀ h ∈ post, h.op = GateOp.and ∨ h.op = GateOp.or) :
    (offGate pre post out).eval x = true → (atGate pre post g out).eval x = true := by
  change (run (pre ++ ⟨GateOp.or, []⟩ :: post) x).getD out false = true →
    (run (pre ++ g :: post) x).getD out false = true
  rw [run_append, run_append, run_cons, run_cons]
  change (run post (run pre x ++ [false])).getD out false = true →
    (run post (run pre x ++ [gateValue pre g x])).getD out false = true
  apply run_mono post hpost _ _ (by simp) _ out
  apply append_mono _ _ false _ rfl (fun _ h => h)
  intro h
  cases h

lemma offGate_ao (pre post : List Gate) (out : ℕ)
    (hpre : ∀ h ∈ pre, h.op = GateOp.and ∨ h.op = GateOp.or)
    (hpost : ∀ h ∈ post, h.op = GateOp.and ∨ h.op = GateOp.or) :
    PEqualNP.EdgeOwnership.AndOrOnly (offGate pre post out) := by
  intro h hh
  change h ∈ pre ++ ⟨GateOp.or, []⟩ :: post at hh
  rcases List.mem_append.mp hh with hh | hh
  · exact hpre h hh
  · rcases List.mem_cons.mp hh with rfl | hh
    · exact Or.inr rfl
    · exact hpost h hh

lemma offGate_incidence (P L : ℕ) (I : Fin P → Fin L → Prop) [DecidableRel I]
    (pre post : List Gate) (g : Gate) (out : ℕ)
    (hpre : ∀ h ∈ pre, h.op = GateOp.and ∨ h.op = GateOp.or)
    (hpost : ∀ h ∈ post, h.op = GateOp.and ∨ h.op = GateOp.or)
    (hfun : ∀ x : Fin (P + L) → Bool,
      circuitFun (P + L) (atGate pre post g out) x =
        decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
          x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true))
    (hinvisible : ∀ p : Fin P, ∀ l : Fin L, I p l →
      gateValue pre g (List.ofFn fun i : Fin (P + L) =>
        decide (i = Fin.castAdd L p ∨ i = Fin.natAdd P l)) = false) :
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
    have he : circuitFun (P + L) (offGate pre post out) e = true := by
      change (offGate pre post out).eval (List.ofFn e) = true
      rw [offGate_eval_eq pre post g out (List.ofFn e) (hinvisible p l hi)]
      change circuitFun (P + L) (atGate pre post g out) e = true
      rw [hfun, decide_eq_true_eq]
      exact ⟨p, l, hi, by simp [e], by simp [e]⟩
    apply circuitFun_mono (P + L) (offGate pre post out) (offGate_ao pre post out hpre hpost) e x ?_ he
    intro i hei
    rcases of_decide_eq_true hei with rfl | rfl
    · exact hp
    · exact hl

end PEqualNP.Outside.L_meta_2585.EdgeInvisible
