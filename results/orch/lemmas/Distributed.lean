import PEqualNP.Defs.ReadK

namespace PEqualNP.Outside.L_meta_2602_aux.Distributed

open PEqualNP.CircuitLowerBounds

def addGate (n : ℕ) (C : Circuit) (op : GateOp) (ins : List ℕ) : Circuit :=
  ⟨C.gates ++ [⟨op, ins⟩], n + C.size⟩

lemma addGate_size (n : ℕ) (C : Circuit) (op : GateOp) (ins : List ℕ) :
    (addGate n C op ins).size = C.size + 1 := by
  simp [addGate, Circuit.size]

lemma foldLength {α β : Type} (f : List α → β → α) (gs : List β) (xs : List α) :
    (gs.foldl (fun s g => s ++ [f s g]) xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
    omega

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.size := by
  exact foldLength _ C.gates x

lemma addGate_wires (n : ℕ) (C : Circuit) (op : GateOp) (ins : List ℕ) (x : List Bool) :
    (addGate n C op ins).wires x = C.wires x ++
      [op.eval (ins.map fun i => (C.wires x).getD i false)] := by
  simp [addGate, Circuit.wires, List.foldl_append]

lemma addGate_old (n : ℕ) (C : Circuit) (op : GateOp) (ins : List ℕ)
    (x : List Bool) (hx : x.length = n) (i : ℕ) (hi : i < n + C.size) :
    ((addGate n C op ins).wires x).getD i false = (C.wires x).getD i false := by
  rw [addGate_wires]
  exact List.getD_append _ _ _ _ (by simpa [wires_length, hx] using hi)

lemma addGate_eval (n : ℕ) (C : Circuit) (op : GateOp) (ins : List ℕ)
    (x : List Bool) (hx : x.length = n) :
    (addGate n C op ins).eval x = op.eval (ins.map fun i => (C.wires x).getD i false) := by
  change ((addGate n C op ins).wires x).getD (n + C.size) false = _
  rw [addGate_wires, List.getD_append_right _ _ _ _ (by simp [wires_length, hx])]
  simp [wires_length, hx]

def orAndWrap (n : ℕ) (C : Circuit) (z t : ℕ) : Circuit :=
  let A := addGate n C .and [z, t]
  addGate n A .or [C.output, A.output]

def distributeWrap (n : ℕ) (C : Circuit) (z t : ℕ) : Circuit :=
  let A := addGate n C .or [C.output, z]
  let B := addGate n A .or [C.output, t]
  addGate n B .and [A.output, B.output]

lemma orAndWrap_size (n : ℕ) (C : Circuit) (z t : ℕ) :
    (orAndWrap n C z t).size = C.size + 2 := by
  simp [orAndWrap, addGate_size, Nat.add_assoc]

lemma distributeWrap_size (n : ℕ) (C : Circuit) (z t : ℕ) :
    (distributeWrap n C z t).size = C.size + 3 := by
  simp [distributeWrap, addGate_size, Nat.add_assoc]

lemma orAndWrap_eval (n : ℕ) (C : Circuit) (z t : ℕ) (x : List Bool)
    (hx : x.length = n) (ho : C.output < n + C.size) :
    (orAndWrap n C z t).eval x =
      (C.eval x || ((C.wires x).getD z false && (C.wires x).getD t false)) := by
  let A := addGate n C .and [z, t]
  have ha : A.eval x = ((C.wires x).getD z false && (C.wires x).getD t false) := by
    simpa [A, GateOp.eval] using addGate_eval n C .and [z, t] x hx
  have old : (A.wires x).getD C.output false = (C.wires x).getD C.output false :=
    addGate_old n C .and [z, t] x hx C.output ho
  change (addGate n A .or [C.output, A.output]).eval x = _
  rw [addGate_eval n A .or [C.output, A.output] x hx]
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
    id_eq, Bool.or_false]
  rw [old]
  change (C.eval x || A.eval x) = _
  rw [ha]

lemma distributeWrap_eval (n : ℕ) (C : Circuit) (z t : ℕ) (x : List Bool)
    (hx : x.length = n) (ho : C.output < n + C.size) (ht : t < n + C.size) :
    (distributeWrap n C z t).eval x =
      ((C.eval x || (C.wires x).getD z false) &&
        (C.eval x || (C.wires x).getD t false)) := by
  let A := addGate n C .or [C.output, z]
  let B := addGate n A .or [C.output, t]
  have ha : A.eval x = (C.eval x || (C.wires x).getD z false) := by
    simpa [A, GateOp.eval, Circuit.eval] using addGate_eval n C .or [C.output, z] x hx
  have oldo : (A.wires x).getD C.output false = (C.wires x).getD C.output false :=
    addGate_old n C .or [C.output, z] x hx C.output ho
  have oldt : (A.wires x).getD t false = (C.wires x).getD t false :=
    addGate_old n C .or [C.output, z] x hx t ht
  have hb : B.eval x = (C.eval x || (C.wires x).getD t false) := by
    change (addGate n A .or [C.output, t]).eval x = _
    rw [addGate_eval n A .or [C.output, t] x hx]
    simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
      id_eq, Bool.or_false, oldo, oldt]
    rfl
  have olda : (B.wires x).getD A.output false = A.eval x := by
    exact addGate_old n A .or [C.output, t] x hx A.output (by simp [A, addGate, Circuit.size])
  change (addGate n B .and [A.output, B.output]).eval x = _
  rw [addGate_eval n B .and [A.output, B.output] x hx]
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
    id_eq, Bool.and_true, olda]
  change (A.eval x && B.eval x) = _
  rw [ha, hb]

lemma distributeWrap_eq (n : ℕ) (C : Circuit) (z t : ℕ) (x : List Bool)
    (hx : x.length = n) (ho : C.output < n + C.size) (ht : t < n + C.size) :
    (distributeWrap n C z t).eval x = (orAndWrap n C z t).eval x := by
  rw [distributeWrap_eval n C z t x hx ho ht, orAndWrap_eval n C z t x hx ho]
  cases C.eval x <;> rfl

def linearOp (op : GateOp) (ps : List (Bool × Bool)) : Bool × Bool :=
  match op with
  | .or => (ps.any (·.1), ps.any (·.2))
  | .and => ps.foldl (fun a b => (a.1 && b.1, a.1 && b.2 || a.2 && b.1)) (true, false)
  | _ => (false, false)

lemma linearParts_length (C : Circuit) (s : ℕ → Bool) (x : List Bool) :
    (PEqualNP.ReadK.linearParts C s x).length = x.length + C.size := by
  unfold PEqualNP.ReadK.linearParts Circuit.size
  rw [foldLength]
  simp

lemma addGate_linear (n : ℕ) (C : Circuit) (op : GateOp) (ins : List ℕ)
    (s : ℕ → Bool) (x : List Bool) :
    PEqualNP.ReadK.linearParts (addGate n C op ins) s x =
      PEqualNP.ReadK.linearParts C s x ++
        [linearOp op (ins.map fun i => (PEqualNP.ReadK.linearParts C s x).getD i (false, false))] := by
  cases op <;> simp [addGate, PEqualNP.ReadK.linearParts, linearOp, List.foldl_append]

lemma addGate_linear_old (n : ℕ) (C : Circuit) (op : GateOp) (ins : List ℕ)
    (s : ℕ → Bool) (x : List Bool) (hx : x.length = n) (i : ℕ) (hi : i < n + C.size) :
    (PEqualNP.ReadK.linearParts (addGate n C op ins) s x).getD i (false, false) =
      (PEqualNP.ReadK.linearParts C s x).getD i (false, false) := by
  rw [addGate_linear]
  exact List.getD_append _ _ _ _ (by simpa [linearParts_length, hx] using hi)

lemma addGate_linear_value (n : ℕ) (C : Circuit) (op : GateOp) (ins : List ℕ)
    (s : ℕ → Bool) (x : List Bool) (hx : x.length = n) :
    (PEqualNP.ReadK.linearParts (addGate n C op ins) s x).getD
        (addGate n C op ins).output (false, false) =
      linearOp op (ins.map fun i => (PEqualNP.ReadK.linearParts C s x).getD i (false, false)) := by
  change (PEqualNP.ReadK.linearParts (addGate n C op ins) s x).getD (n + C.size) (false, false) = _
  rw [addGate_linear, List.getD_append_right _ _ _ _ (by simp [linearParts_length, hx])]
  simp [linearParts_length, hx]

lemma distributeWrap_linear_zero (n : ℕ) (C : Circuit) (z t : ℕ)
    (s : ℕ → Bool) (x : List Bool) (hx : x.length = n)
    (ho : C.output < n + C.size) (ht : t < n + C.size)
    (hC : ((PEqualNP.ReadK.linearParts C s x).getD C.output (false, false)).1 = false)
    (hz : ((PEqualNP.ReadK.linearParts C s x).getD z (false, false)).1 = false)
    (ht0 : ((PEqualNP.ReadK.linearParts C s x).getD t (false, false)).1 = false) :
    ((PEqualNP.ReadK.linearParts (distributeWrap n C z t) s x).getD
      (distributeWrap n C z t).output (false, false)).2 = false := by
  let A := addGate n C .or [C.output, z]
  let B := addGate n A .or [C.output, t]
  have hA : ((PEqualNP.ReadK.linearParts A s x).getD A.output (false, false)).1 = false := by
    change ((PEqualNP.ReadK.linearParts (addGate n C .or [C.output, z]) s x).getD
      (addGate n C .or [C.output, z]).output (false, false)).1 = false
    rw [addGate_linear_value n C .or [C.output, z] s x hx]
    simp only [linearOp, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      Bool.or_false, hC, hz, Bool.false_or]
  have oldo := addGate_linear_old n C .or [C.output, z] s x hx C.output ho
  have oldt := addGate_linear_old n C .or [C.output, z] s x hx t ht
  have hB : ((PEqualNP.ReadK.linearParts B s x).getD B.output (false, false)).1 = false := by
    change ((PEqualNP.ReadK.linearParts (addGate n A .or [C.output, t]) s x).getD
      (addGate n A .or [C.output, t]).output (false, false)).1 = false
    rw [addGate_linear_value n A .or [C.output, t] s x hx]
    simp only [linearOp, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      Bool.or_false]
    rw [oldo, oldt, hC, ht0]
    rfl
  have olda : (PEqualNP.ReadK.linearParts B s x).getD A.output (false, false) =
      (PEqualNP.ReadK.linearParts A s x).getD A.output (false, false) := by
    exact addGate_linear_old n A .or [C.output, t] s x hx A.output
      (by simp [A, addGate, Circuit.size])
  change ((PEqualNP.ReadK.linearParts (addGate n B .and [A.output, B.output]) s x).getD
    (addGate n B .and [A.output, B.output]).output (false, false)).2 = false
  rw [addGate_linear_value n B .and [A.output, B.output] s x hx]
  simp only [linearOp, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
    Bool.true_and, Bool.false_and, Bool.or_false]
  rw [olda, hA, hB]
  simp

def Legal (n : ℕ) (C : Circuit) : Prop :=
  ∀ j g, C.gates[j]? = some g → (g.op = .and ∨ g.op = .or) ∧
    ∃ a b, g.inputs = [a, b] ∧ a ≠ b ∧ a < n + j ∧ b < n + j

lemma addGate_legal (n : ℕ) (C : Circuit) (op : GateOp) (a b : ℕ)
    (hC : Legal n C) (hop : op = .and ∨ op = .or)
    (ha : a < n + C.size) (hb : b < n + C.size) (hne : a ≠ b) :
    Legal n (addGate n C op [a, b]) := by
  intro j g hg
  change (C.gates ++ [⟨op, [a, b]⟩])[j]? = some g at hg
  by_cases hj : j < C.gates.length
  · rw [List.getElem?_append_left hj] at hg
    exact hC j g hg
  · rw [List.getElem?_append_right (Nat.le_of_not_gt hj)] at hg
    by_cases heq : j = C.size
    · subst j
      simp only [Circuit.size, Nat.sub_self, List.getElem?_cons_zero] at hg
      cases hg
      exact ⟨hop, a, b, rfl, hne, ha, hb⟩
    · have hfar : 1 ≤ j - C.gates.length := by dsimp [Circuit.size] at heq; omega
      rw [List.getElem?_eq_none (by simpa using hfar)] at hg
      contradiction

lemma distributeWrap_legal (n : ℕ) (C : Circuit) (z t : ℕ)
    (hC : Legal n C) (ho : C.output < n + C.size)
    (hz : z < n + C.size) (ht : t < n + C.size)
    (hoz : C.output ≠ z) (hot : C.output ≠ t) : Legal n (distributeWrap n C z t) := by
  let A := addGate n C .or [C.output, z]
  let B := addGate n A .or [C.output, t]
  have ha : Legal n A := addGate_legal n C .or C.output z hC (Or.inr rfl) ho hz hoz
  have hb : Legal n B := addGate_legal n A .or C.output t ha (Or.inr rfl)
    (by simp only [A, addGate_size]; omega) (by simp only [A, addGate_size]; omega) hot
  change Legal n (addGate n B .and [A.output, B.output])
  apply addGate_legal n B .and A.output B.output hb (Or.inl rfl)
  · simp [A, B, addGate, Circuit.size]
  · simp [B, addGate, Circuit.size]
  · simp [A, B, addGate, Circuit.size]

end PEqualNP.Outside.L_meta_2602_aux.Distributed
