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

end PEqualNP.Outside.L_meta_2602_aux.Distributed
