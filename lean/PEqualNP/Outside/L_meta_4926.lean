import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4926

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.MetaComplexity.SingleLevel PEqualNP.EdgeOwnership PEqualNP.TopForm

def stepG {α : Type} (F : (ℕ → α) → Gate → α) (d : α) (w : List α) (g : Gate) : List α :=
  w ++ [F (fun i => w.getD i d) g]

def Loc {α : Type} (F : (ℕ → α) → Gate → α) : Prop :=
  ∀ V V' : ℕ → α, ∀ g : Gate, (∀ i ∈ g.inputs, V i = V' i) → F V g = F V' g

lemma gfoldl_length {α : Type} (F : (ℕ → α) → Gate → α) (d : α) (gs : List Gate) (w : List α) :
    (gs.foldl (stepG F d) w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepG]
    omega

lemma gfoldl_getD_lt {α : Type} (F : (ℕ → α) → Gate → α) (d : α) (gs : List Gate) (w : List α)
    (i : ℕ) (hi : i < w.length) :
    (gs.foldl (stepG F d) w).getD i d = w.getD i d := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepG F d w g).length := by simp [stepG]; omega
    rw [ih (stepG F d w g) hlt]
    simp [stepG, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma ggetD_ge {α : Type} (w : List α) (d : α) (i : ℕ) (hi : w.length ≤ i) : w.getD i d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma gfoldl_getD_gate {α : Type} (F : (ℕ → α) → Gate → α) (d : α) (hF : Loc F)
    (gs : List Gate) (w : List α) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl (stepG F d) w).getD (w.length + j) d =
      F (fun i => if i < w.length + j then (gs.foldl (stepG F d) w).getD i d else d) gs[j] := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepG F d w g).length := by simp [stepG]
      rw [Nat.add_zero, gfoldl_getD_lt F d gs (stepG F d w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepG F d w g).getD w.length d = F (fun i => w.getD i d) g := by
        simp [stepG, List.getD_eq_getElem?_getD]
      rw [h2]
      apply hF
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, gfoldl_getD_lt F d gs (stepG F d w g) i (by simp [stepG]; omega)]
        simp [stepG, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact ggetD_ge w d i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepG F d w g) j hj'
      have hl : (stepG F d w g).length = w.length + 1 := by simp [stepG]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gate_val {α : Type} (F : (ℕ → α) → Gate → α) (d : α) (hF : Loc F) (n : ℕ) (C : Circuit)
    (hRB : ReadsBack n C) (w : List α) (hw : w.length = n) (j : ℕ) (hj : j < C.gates.length) :
    (C.gates.foldl (stepG F d) w).getD (n + j) d =
      F (fun i => (C.gates.foldl (stepG F d) w).getD i d) C.gates[j] := by
  subst hw
  rw [gfoldl_getD_gate F d hF C.gates w j hj]
  apply hF
  intro i hi
  have : i < w.length + j := hRB j hj i (by rw [gateAt_eq hj]; exact hi)
  rw [ite_eq_left this]

def Fw (V : ℕ → Bool) (g : Gate) : Bool := g.op.eval (g.inputs.map V)

def comb : GateOp → List ℕ → ℕ
  | GateOp.and, l => l.sum
  | _, l => l.foldr max 0

def Fd (V : ℕ → ℕ) (g : Gate) : ℕ := comb g.op (g.inputs.map V)

def Fa (V : ℕ → ℕ) (g : Gate) : ℕ := (g.inputs.map V).foldr max 0 + andLevel g

lemma loc_w : Loc Fw := by
  intro V V' g h; unfold Fw; rw [List.map_congr_left h]

lemma loc_d : Loc Fd := by
  intro V V' g h; unfold Fd; rw [List.map_congr_left h]

lemma loc_a : Loc Fa := by
  intro V V' g h; unfold Fa; rw [List.map_congr_left h]

lemma lineDegrees_eq (C : Circuit) (n : ℕ) (m : Finset ℕ) :
    C.lineDegrees n m = C.gates.foldl (stepG Fd 0)
      ((List.range n).map fun i => if i ∈ m then 1 else 0) := by
  unfold Circuit.lineDegrees
  congr 1
  funext w g
  obtain ⟨op, l⟩ := g
  cases op <;> simp [stepG, Fd, comb, Gate.lineDegree]

def Wv (n : ℕ) (C : Circuit) (v : Fin n) (u : ℕ) : Bool :=
  (C.wires (List.ofFn fun x5 : Fin n => decide (x5 = v))).getD u false

def Dv (n : ℕ) (C : Circuit) (v : Fin n) (u : ℕ) : ℕ :=
  (C.lineDegrees n {↑v}).getD u 0

def Av (n : ℕ) (C : Circuit) (u : ℕ) : ℕ := (andDepths C n).getD u 0

lemma input_case (n : ℕ) (C : Circuit) (v : Fin n) (u : ℕ) (hu : u < n) :
    Dv n C v u ≤ 1 ∧ (Dv n C v u = 1 → Wv n C v u = true) ∧ Av n C u = 0 := by
  have hW : Wv n C v u = decide (u = v.val) := by
    unfold Wv
    show (C.gates.foldl (stepG Fw false) _).getD u false = _
    rw [gfoldl_getD_lt _ _ _ _ _ (by simpa using hu)]
    simp [List.getD_eq_getElem?_getD, hu, Fin.ext_iff]
  have hD : Dv n C v u = if u = v.val then 1 else 0 := by
    unfold Dv
    rw [lineDegrees_eq, gfoldl_getD_lt _ _ _ _ _ (by simpa using hu)]
    simp [List.getD_eq_getElem?_getD, hu]
  have hA : Av n C u = 0 := by
    unfold Av andDepths
    show (C.gates.foldl (stepG Fa 0) _).getD u 0 = 0
    rw [gfoldl_getD_lt _ _ _ _ _ (by simpa using hu)]
    simp [List.getD_eq_getElem?_getD, hu]
  rw [hW, hD, hA]
  by_cases h : u = v.val <;> simp [h]

lemma beyond_case (n : ℕ) (C : Circuit) (v : Fin n) (u : ℕ) (hu : n + C.gates.length ≤ u) :
    Dv n C v u = 0 ∧ Av n C u = 0 := by
  constructor
  · unfold Dv
    rw [lineDegrees_eq]
    apply ggetD_ge
    rw [gfoldl_length]; simp; omega
  · unfold Av andDepths
    show (C.gates.foldl (stepG Fa 0) _).getD u 0 = 0
    apply ggetD_ge
    rw [gfoldl_length]; simp; omega

lemma gate_case (n : ℕ) (C : Circuit) (v : Fin n) (hAO : IsAO2 n C) (j : ℕ)
    (hj : j < C.gates.length) :
    ∃ a b, a < n + j ∧ b < n + j ∧
      ((Wv n C v (n + j) = (Wv n C v a && Wv n C v b) ∧
        Dv n C v (n + j) = Dv n C v a + Dv n C v b ∧
        Av n C (n + j) = max (Av n C a) (Av n C b) + 1) ∨
      (Wv n C v (n + j) = (Wv n C v a || Wv n C v b) ∧
        Dv n C v (n + j) = max (Dv n C v a) (Dv n C v b) ∧
        Av n C (n + j) = max (Av n C a) (Av n C b))) := by
  obtain ⟨hAnd, hRB, hL⟩ := hAO
  have hmem := List.getElem_mem hj
  have hop := hAnd _ hmem
  have hl := hL _ hmem
  have hrb : ∀ i ∈ C.gates[j].inputs, i < n + j := by
    intro i hi; exact hRB j hj i (by rw [gateAt_eq hj]; exact hi)
  have eW : Wv n C v (n + j) = Fw (Wv n C v) C.gates[j] := by
    unfold Wv
    exact gate_val Fw false loc_w n C hRB _ (by simp) j hj
  have eD : Dv n C v (n + j) = Fd (Dv n C v) C.gates[j] := by
    unfold Dv
    rw [lineDegrees_eq]
    exact gate_val Fd 0 loc_d n C hRB _ (by simp) j hj
  have eA : Av n C (n + j) = Fa (Av n C) C.gates[j] := by
    unfold Av andDepths
    exact gate_val Fa 0 loc_a n C hRB _ (by simp) j hj
  rw [eW, eD, eA]
  generalize C.gates[j] = g at hop hl hrb
  obtain ⟨op, l⟩ := g
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · simp at hl
  · simp at hl
  · refine ⟨a, b, hrb a (by simp), hrb b (by simp), ?_⟩
    rcases hop with h | h <;> simp only at h <;> subst h
    · left
      refine ⟨?_, ?_, ?_⟩
      · simp [Fw, GateOp.eval]
      · simp [Fd, comb]
      · simp [Fa, andLevel]
    · right
      refine ⟨?_, ?_, ?_⟩
      · simp [Fw, GateOp.eval]
      · simp [Fd, comb]
      · simp [Fa, andLevel]
  · simp at hl

lemma lemA (n : ℕ) (C : Circuit) (v : Fin n) (hAO : IsAO2 n C) :
    ∀ u, Av n C u = 0 → Dv n C v u ≤ 1 ∧ (Dv n C v u = 1 → Wv n C v u = true) := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
  intro hA
  by_cases hun : u < n
  · have := input_case n C v u hun
    exact ⟨this.1, this.2.1⟩
  by_cases hub : n + C.gates.length ≤ u
  · have := beyond_case n C v u hub
    refine ⟨by omega, fun h => by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, u = n + j := ⟨u - n, by omega⟩
  obtain ⟨a, b, ha, hb, h⟩ := gate_case n C v hAO j (by omega)
  rcases h with ⟨_, _, h3⟩ | ⟨h1, h2, h3⟩
  · omega
  · have iha := ih a ha (by omega)
    have ihb := ih b hb (by omega)
    refine ⟨by omega, fun hD => ?_⟩
    rw [h1]
    by_cases hDa : Dv n C v a = 1
    · simp [iha.2 hDa]
    · have : Dv n C v b = 1 := by omega
      simp [ihb.2 this]

lemma lemB (n : ℕ) (C : Circuit) (v : Fin n) (hAO : IsAO2 n C) :
    ∀ u, Av n C u ≤ 1 → 2 ≤ Dv n C v u → Wv n C v u = true := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
  intro hA hD
  by_cases hun : u < n
  · have := input_case n C v u hun
    omega
  by_cases hub : n + C.gates.length ≤ u
  · have := beyond_case n C v u hub
    omega
  obtain ⟨j, rfl⟩ : ∃ j, u = n + j := ⟨u - n, by omega⟩
  obtain ⟨a, b, ha, hb, h⟩ := gate_case n C v hAO j (by omega)
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · have iha := lemA n C v hAO a (by omega)
    have ihb := lemA n C v hAO b (by omega)
    rw [h1, iha.2 (by omega), ihb.2 (by omega)]
    rfl
  · rw [h1]
    by_cases hDa : 2 ≤ Dv n C v a
    · simp [ih a ha (by omega) hDa]
    · simp [ih b hb (by omega) (by omega)]

end PEqualNP.Outside.L_meta_4926

theorem PEqualNP.Outside.L_meta_4926 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin x1), PEqualNP.TopForm.IsAO2 x1 x2 → x2.eval (List.ofFn fun (x5 : Fin x1) => Decidable.decide (x5 = x3)) = Bool.false → (2 : ℕ) ≤ x2.lineDeg x1 {↑x3} → (2 : ℕ) ≤ (PEqualNP.MetaComplexity.SingleLevel.andDepths x2 x1).getD x2.output (0 : ℕ) := by
  intro n C v hAO hev hdeg
  by_contra hlt
  have hA : PEqualNP.Outside.L_meta_4926.Av n C C.output ≤ 1 := by
    unfold PEqualNP.Outside.L_meta_4926.Av; omega
  have hB := PEqualNP.Outside.L_meta_4926.lemB n C v hAO C.output hA hdeg
  unfold PEqualNP.Outside.L_meta_4926.Wv at hB
  unfold PEqualNP.CircuitLowerBounds.Circuit.eval at hev
  rw [hB] at hev
  exact absurd hev (by simp)
