import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2373_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Code := Fin 3 × Fin 29 × Fin 29

def decode (g : Code) : Gate :=
  ⟨if g.1 = 0 then .and else if g.1 = 1 then .or else .not,
    [g.2.1.val, g.2.2.val]⟩

def clip (i : ℕ) : Fin 29 := ⟨min i 28, by omega⟩

lemma clipped (w : List Bool) (hw : w.length ≤ 28) (i : ℕ) :
    w.getD (clip i).val false = w.getD i false := by
  by_cases hi : i ≤ 28
  · simp [clip, Nat.min_eq_left hi]
  · have hwi : w.length ≤ i := by omega
    have hw28 : w.getD 28 false = false := List.getD_eq_default _ _ hw
    rw [show (clip i).val = 28 by simp [clip, Nat.min_eq_right (by omega : 28 ≤ i)],
      hw28, List.getD_eq_default _ _ hwi]

def encode (g : Gate) : Code :=
  match g.op, g.inputs with
  | .and, [] => (2, 28, 28)
  | .and, [a] => (0, clip a, clip a)
  | .and, a :: b :: _ => (0, clip a, clip b)
  | .or, [] => (1, 28, 28)
  | .or, [a] => (1, clip a, 28)
  | .or, a :: b :: _ => (1, clip a, clip b)
  | .not, [] => (2, 28, 28)
  | .not, a :: _ => (2, clip a, 28)
  | _, _ => (1, 28, 28)

lemma gate_same (g : Gate)
    (hg : g.op = .and ∨ g.op = .or ∨ g.op = .not)
    (hn : g.inputs.length ≤ 2) (w : List Bool) (hw : w.length ≤ 28) :
    (decode (encode g)).op.eval ((decode (encode g)).inputs.map fun i => w.getD i false) =
      g.op.eval (g.inputs.map fun i => w.getD i false) := by
  obtain ⟨op, ins⟩ := g
  have hz : w.getD 28 false = false := List.getD_eq_default _ _ hw
  have hc (i : ℕ) : w[(clip i).val]?.getD false = w[i]?.getD false := clipped w hw i
  change w[28]?.getD false = false at hz
  rcases hg with rfl | rfl | rfl
  all_goals cases ins with
  | nil => simp [encode, decode, GateOp.eval, hz]
  | cons a ins =>
    cases ins with
    | nil => simp [encode, decode, GateOp.eval, hc, hz]
    | cons b ins =>
      have he : ins = [] := by
        apply List.length_eq_zero_iff.mp
        simp only [List.length_cons] at hn
        omega
      subst ins
      simp [encode, decode, GateOp.eval, hc, hz]

lemma decode_fan (g : Code) :
    (decode g).op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      (decode g).inputs.length ≤ 2 := by
  simp only [decode]
  split_ifs <;> simp

lemma wires_length (gs : List Gate) (w : List Bool) :
    (Circuit.wires ⟨gs, 0⟩ w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [Circuit.wires]
  | cons g gs ih =>
    change (Circuit.wires ⟨gs, 0⟩ (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).length = _
    rw [ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

lemma wires_same (gs : List Gate)
    (hf : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2)
    (w : List Bool) (hw : w.length + gs.length ≤ 28) :
    Circuit.wires ⟨gs.map (decode ∘ encode), 0⟩ w = Circuit.wires ⟨gs, 0⟩ w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    have hg := hf g (by simp)
    have hs := gate_same g (by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hg.1)
      hg.2 w (by simp only [List.length_cons] at hw; omega)
    change Circuit.wires ⟨gs.map (decode ∘ encode), 0⟩
      (w ++ [(decode (encode g)).op.eval ((decode (encode g)).inputs.map fun i => w.getD i false)]) = _
    rw [hs]
    apply ih
    · intro a ha
      exact hf a (by simp [ha])
    · simp only [List.length_append, List.length_cons, List.length_nil]
      simp only [List.length_cons] at hw
      omega


lemma wires_input (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (Circuit.wires ⟨gs, 0⟩ w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (Circuit.wires ⟨gs, 0⟩ (w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)])).getD i false = _
    rw [ih _ (by simp; omega), List.getD_append _ _ _ _ hi]

lemma finite_model (gs : List Gate)
    (hf : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2)
    (hs : gs.length ≤ 18) :
    ∃ model : Fin 18 → Code, ∀ (x : Fin 10 → Bool) (i : ℕ),
      i < 10 + gs.length →
      (Circuit.wires ⟨(List.ofFn model).map decode, 0⟩ (List.ofFn x)).getD i false =
        (Circuit.wires ⟨gs, 0⟩ (List.ofFn x)).getD i false := by
  let codes := gs.map encode ++ List.replicate (18 - gs.length) (1, 28, 28)
  have hlen : codes.length = 18 := by simp [codes]; omega
  let model : Fin 18 → Code := fun i => codes[ i.val ]'(by rw [hlen]; exact i.isLt)
  have hm : List.ofFn model = codes := by
    apply List.ext_getElem
    · simp [hlen]
    · intro i h₁ h₂
      simp only [List.getElem_ofFn, model]
  refine ⟨model, ?_⟩
  intro x i hi
  rw [hm]
  have same := wires_same gs hf (List.ofFn x) (by simp; omega)
  have append_wires :
      Circuit.wires ⟨codes.map decode, 0⟩ (List.ofFn x) =
        Circuit.wires ⟨(List.replicate (18 - gs.length) (1, 28, 28)).map decode, 0⟩
          (Circuit.wires ⟨gs, 0⟩ (List.ofFn x)) := by
    simp only [codes, List.map_append, List.map_map]
    simp only [Circuit.wires, List.foldl_append] at same ⊢
    rw [same]
  rw [append_wires, wires_input _ _ _]
  rw [wires_length, List.length_ofFn]
  exact hi


def target : (Fin 10 → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ))

def modelWires (m : Fin 18 → Code) (x : Fin 10 → Bool) (i : ℕ) : Bool :=
  (Circuit.wires ⟨(List.ofFn m).map decode, 0⟩ (List.ofFn x)).getD i false

def FiniteClaim : Prop :=
  ∀ (m : Fin 18 → Code) (a b : Fin 18),
    (∃ x, modelWires m x (10 + a.val) = true ∧ modelWires m x (10 + b.val) = false) →
    (∃ x, modelWires m x (10 + a.val) = false ∧ modelWires m x (10 + b.val) = true) →
    (∀ x, target x = false → modelWires m x (10 + a.val) = false ∧ modelWires m x (10 + b.val) = false) →
    ∃ x, target x = true ∧ modelWires m x (10 + a.val) = false ∧ modelWires m x (10 + b.val) = false

lemma finite_suffices (h : FiniteClaim) : ∀ (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo { gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →     PEqualNP.MetaComplexity.FanInTwo x2 →       x2.size ≤ (17 : ℕ) →         have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ));         have x9 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x9 : Fin (10 : ℕ) → Bool) (x10 : ℕ) => (x2.wires ({ gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9))).getD x10 Bool.false;         (∃ (x10 : Fin (10 : ℕ) → Bool), x9 x10 x3 = Bool.true ∧ x9 x10 x4 = Bool.false) → (∃ (x11 : Fin (10 : ℕ) → Bool), x9 x11 x3 = Bool.false ∧ x9 x11 x4 = Bool.true) → (∀ (x12 : Fin (10 : ℕ) → Bool), x8 x12 = Bool.false → x9 x12 x3 = Bool.false ∧ x9 x12 x4 = Bool.false) → ∃ (x13 : Fin (10 : ℕ) → Bool), x8 x13 = Bool.true ∧ x9 x13 x3 = Bool.false ∧ x9 x13 x4 = Bool.false := by
  intro g C a b hg hC hs
  let gs := g :: C.gates
  let W (x : Fin 10 → Bool) (i : ℕ) := (Circuit.wires ⟨gs, 0⟩ (List.ofFn x)).getD i false
  change (∃ x, W x a = true ∧ W x b = false) → (∃ x, W x a = false ∧ W x b = true) →
    (∀ x, target x = false → W x a = false ∧ W x b = false) →
    ∃ x, target x = true ∧ W x a = false ∧ W x b = false
  intro ha hb off
  have hf : ∀ q ∈ gs, q.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ q.inputs.length ≤ 2 := by
    intro q hq
    simp only [gs, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact hg q (by simp)
    · exact hC q hq
  have size : gs.length ≤ 18 := by simp only [gs, List.length_cons]; change C.size + 1 ≤ 18; omega
  obtain ⟨model, same⟩ := finite_model gs hf size
  have length (x : Fin 10 → Bool) : (Circuit.wires ⟨gs, 0⟩ (List.ofFn x)).length = 10 + gs.length := by
    rw [wires_length, List.length_ofFn]
  have upper (i : ℕ) (hi : ∃ x, W x i = true) : i < 10 + gs.length := by
    obtain ⟨x, hx⟩ := hi
    by_contra hn
    have hh : (Circuit.wires ⟨gs, 0⟩ (List.ofFn x)).length ≤ i := by rw [length]; omega
    have hv := List.getD_eq_default (Circuit.wires ⟨gs, 0⟩ (List.ofFn x)) false hh
    change W x i = false at hv
    exact Bool.noConfusion (hx.symm.trans hv)
  have input (x : Fin 10 → Bool) (j : Fin 10) : W x j.val = x j := by
    unfold W
    rw [wires_input _ _ _ (by simp)]
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  have single (j : Fin 10) : target (fun k => decide (k = j)) = false := by
    fin_cases j <;> decide
  have lower (i : ℕ) (hi : ∀ x, target x = false → W x i = false) : 10 ≤ i := by
    by_contra hn
    have hil : i < 10 := by omega
    let j : Fin 10 := ⟨i, hil⟩
    have hv := hi (fun k => decide (k = j)) (single j)
    change W (fun k => decide (k = j)) j.val = false at hv
    rw [input] at hv
    simp at hv
  have alo : 10 ≤ a := lower a (fun x hx => (off x hx).1)
  have blo : 10 ≤ b := lower b (fun x hx => (off x hx).2)
  have ahi : a < 10 + gs.length := upper a (ha.imp fun _ hx => hx.1)
  have bhi : b < 10 + gs.length := upper b (hb.imp fun _ hx => hx.2)
  let aa : Fin 18 := ⟨a - 10, by omega⟩
  let bb : Fin 18 := ⟨b - 10, by omega⟩
  have aval : 10 + aa.val = a := Nat.add_sub_of_le alo
  have bval : 10 + bb.val = b := Nat.add_sub_of_le blo
  have hma (x) : modelWires model x (10 + aa.val) = W x a := by
    rw [aval]
    exact same x a ahi
  have hmb (x) : modelWires model x (10 + bb.val) = W x b := by
    rw [bval]
    exact same x b bhi
  simpa only [hma, hmb] using h model aa bb (by simpa only [hma, hmb] using ha)
    (by simpa only [hma, hmb] using hb) (by simpa only [hma, hmb] using off)

end PEqualNP.Outside.L_meta_2373_aux
