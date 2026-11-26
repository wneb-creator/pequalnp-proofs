import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.BitVec
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_2583
namespace Repair
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadK
def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl
lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega
lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key
def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false
lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]
lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj
lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)
lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega
lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj
lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [ite_eq_right hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [ite_eq_left hlt]; exact h⟩
lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h'; exact ⟨hlt, h'⟩
    · rw [ite_eq_right hlt] at h'; cases h'
  · intro h i hi
    rw [ite_eq_left (h i hi).1]; exact (h i hi).2
lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]
lemma gate_op {C : Circuit} (hm : Monotone2 C) {k : ℕ} (hk : k < C.gates.length) :
    (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or := by
  simpa using (hm _ (gateAt_mem hk)).1
lemma pair_mono {n : ℕ} {C : Circuit} (hm : Monotone2 C)
    {x y : Fin n → Bool} (hxy : ∀ u, x u = true → y u = true) :
    ∀ w, val C (List.ofFn x) w = true → val C (List.ofFn y) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hinput : w < n
    · let u : Fin n := ⟨w, hinput⟩
      change val C (List.ofFn x) u.val = true at hw
      change val C (List.ofFn y) u.val = true
      rw [val_ofFn] at *
      exact hxy u hw
    · have hwlt : w < n + C.gates.length := by
        by_contra! h
        rw [val_ge (by simp : (List.ofFn x).length = n) h] at hw
        cases hw
      obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < C.gates.length := by omega
      rcases gate_op hm hk with hop | hop
      · apply (val_and (by simp) hk hop).2
        intro i hi
        obtain ⟨hlt, ht⟩ := (val_and (by simp) hk hop).1 hw i hi
        exact ⟨hlt, ih i hlt ht⟩
      · obtain ⟨i, hi, hlt, ht⟩ := (val_or (by simp) hk hop).1 hw
        exact (val_or (by simp) hk hop).2 ⟨i, hi, hlt, ih i hlt ht⟩
lemma foldl_append_length {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β) :
    (l.foldl (fun w g => w ++ [f w g]) acc).length = acc.length + l.length := by
  induction l generalizing acc with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, List.length_append, List.length_singleton]
    omega
lemma foldl_append_getD_lt {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β)
    (d : β) (k : ℕ) (hk : k < acc.length) :
    (l.foldl (fun w g => w ++ [f w g]) acc).getD k d = acc.getD k d := by
  induction l generalizing acc with
  | nil => rfl
  | cons a t ih =>
    simp only [List.foldl_cons]
    have hk' : k < (acc ++ [f acc a]).length := by
      rw [List.length_append, List.length_singleton]
      omega
    rw [ih (acc ++ [f acc a]) hk']
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left hk]
lemma foldl_append_getD_gate {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β)
    (d : β) (j : ℕ) (hj : j < l.length) (defaultA : α) :
    (l.foldl (fun w g => w ++ [f w g]) acc).getD (acc.length + j) d =
      f ((l.take j).foldl (fun w g => w ++ [f w g]) acc) (l.getD j defaultA) := by
  have hsplit : l = l.take j ++ l[j] :: l.drop (j + 1) := by
    have h1 := (List.take_append_drop j l).symm
    have h2 : l.drop j = l[j] :: l.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [← h2]
    exact h1
  have hget : l.getD j defaultA = l[j] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    rfl
  rw [hget]
  conv_lhs => rw [hsplit]
  rw [List.foldl_append, List.foldl_cons]
  set pre := (l.take j).foldl (fun w g => w ++ [f w g]) acc
  have hprelen : pre.length = acc.length + j := by
    rw [foldl_append_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have hlt : acc.length + j < (pre ++ [f pre l[j]]).length := by
    rw [List.length_append, List.length_singleton, hprelen]
    omega
  rw [foldl_append_getD_lt f (l.drop (j + 1)) (pre ++ [f pre l[j]]) d (acc.length + j) hlt]
  rw [List.getD_eq_getElem?_getD, ← hprelen]
  simp
lemma foldl_append_take_getD {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β)
    (d : β) (j i : ℕ) (hj : j ≤ l.length) (hi : i < acc.length + j) :
    ((l.take j).foldl (fun w g => w ++ [f w g]) acc).getD i d =
      (l.foldl (fun w g => w ++ [f w g]) acc).getD i d := by
  have hsplit : l = l.take j ++ l.drop j := (List.take_append_drop j l).symm
  conv_rhs => rw [hsplit, List.foldl_append]
  have hprelen : ((l.take j).foldl (fun w g => w ++ [f w g]) acc).length = acc.length + j := by
    rw [foldl_append_length, List.length_take, Nat.min_eq_left hj]
  rw [foldl_append_getD_lt f (l.drop j) _ d i (hprelen ▸ hi)]
lemma readVectors_getD_gate {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (S : List ℕ) (k : ℕ) {j : ℕ} (hj : j < C.gates.length) :
    (readVectors C n S k).getD (n + j) [] =
      let ins := (gateAt C j).inputs.map fun i => (readVectors C n S k).getD i []
      match (gateAt C j).op with
      | GateOp.or => ins.foldl (fun acc A => A.foldl insertNew acc) []
      | GateOp.and => ins.foldl (andStep k) [S.map fun _ => 0]
      | _ => [] := by
  let step : List (List (List ℕ)) → Gate → List (List ℕ) := fun R g =>
    match g.op with
    | GateOp.or => (g.inputs.map fun i => R.getD i []).foldl (fun acc A => A.foldl insertNew acc) []
    | GateOp.and => (g.inputs.map fun i => R.getD i []).foldl (andStep k) [S.map fun _ => 0]
    | _ => []
  have hrv : readVectors C n S k =
      C.gates.foldl (fun R g => R ++ [step R g]) ((List.range n).map (leafVectors S k)) := rfl
  rw [hrv]
  have hgate := foldl_append_getD_gate step
    C.gates ((List.range n).map (leafVectors S k)) [] j hj ⟨GateOp.or, []⟩
  rw [List.length_map, List.length_range] at hgate
  rw [hgate]
  have hmap :
      (gateAt C j).inputs.map (fun i =>
        ((C.gates.take j).foldl (fun R g => R ++ [step R g])
          ((List.range n).map (leafVectors S k))).getD i []) =
      (gateAt C j).inputs.map (fun i =>
        (C.gates.foldl (fun R g => R ++ [step R g])
          ((List.range n).map (leafVectors S k))).getD i []) := by
    apply List.map_congr_left
    intro i hi
    have hilt : i < ((List.range n).map (leafVectors S k)).length + j := by
      rw [List.length_map, List.length_range]
      exact hAO.2.1 j hj i hi
    exact foldl_append_take_getD step C.gates ((List.range n).map (leafVectors S k)) [] j i
      (Nat.le_of_lt hj) hilt
  change (match (gateAt C j).op with
    | GateOp.or =>
      ((gateAt C j).inputs.map fun i => _).foldl (fun acc (A : List (List ℕ)) => A.foldl insertNew acc) []
    | GateOp.and =>
      ((gateAt C j).inputs.map fun i => _).foldl (andStep k) [S.map fun _ => 0]
    | _ => []) = _
  rw [hmap]
end Repair
namespace StructuralAbsorption
open PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
end StructuralAbsorption
namespace ReducedCheck
def avoidingRight {n m : ℕ} (I : Fin n → Fin m → Prop) [DecidableRel I]
    (P : Finset (Fin n)) : Finset (Fin m) :=
  Finset.univ.filter fun l => ∀ p ∈ P, ¬ I p l
def closureLeft {n m : ℕ} (I : Fin n → Fin m → Prop) [DecidableRel I]
    (P : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun p => ∀ l ∈ avoidingRight I P, ¬ I p l
lemma mem_avoidingRight {n m : ℕ} (I : Fin n → Fin m → Prop) [DecidableRel I]
    (P : Finset (Fin n)) (l : Fin m) :
    l ∈ avoidingRight I P ↔ ∀ p ∈ P, ¬ I p l := by
  simp [avoidingRight]
lemma mem_closureLeft {n m : ℕ} (I : Fin n → Fin m → Prop) [DecidableRel I]
    (P : Finset (Fin n)) (p : Fin n) :
    p ∈ closureLeft I P ↔ ∀ l ∈ avoidingRight I P, ¬ I p l := by
  simp [closureLeft]
lemma subset_closureLeft {n m : ℕ} (I : Fin n → Fin m → Prop) [DecidableRel I]
    (P : Finset (Fin n)) : P ⊆ closureLeft I P := by
  intro p hp
  apply (mem_closureLeft I P p).2
  intro l hl
  exact (mem_avoidingRight I P l).1 hl p hp
lemma avoidingRight_closureLeft {n m : ℕ} (I : Fin n → Fin m → Prop)
    [DecidableRel I] (P : Finset (Fin n)) :
    avoidingRight I (closureLeft I P) = avoidingRight I P := by
  ext l
  constructor
  · intro hl
    apply (mem_avoidingRight I P l).2
    intro p hp
    exact (mem_avoidingRight I (closureLeft I P) l).1 hl p
      (subset_closureLeft I P hp)
  · intro hl
    apply (mem_avoidingRight I (closureLeft I P) l).2
    intro p hp
    exact (mem_closureLeft I P p).1 hp l hl
lemma closureLeft_idem {n m : ℕ} (I : Fin n → Fin m → Prop) [DecidableRel I]
    (P : Finset (Fin n)) : closureLeft I (closureLeft I P) = closureLeft I P := by
  ext p
  simp only [mem_closureLeft, avoidingRight_closureLeft]
def independentInput {n m : ℕ} (I : Fin n → Fin m → Prop) [DecidableRel I]
    (P : Finset (Fin n)) : Sum (Fin n) (Fin m) → Bool :=
  Sum.elim (fun p => decide (p ∈ P)) (fun l => decide (l ∈ avoidingRight I P))
def edgeInput {n m : ℕ} (p : Fin n) (l : Fin m) : Sum (Fin n) (Fin m) → Bool :=
  Sum.elim (fun a => decide (a = p)) (fun b => decide (b = l))
lemma exact_certificate {n m : ℕ} (I : Fin n → Fin m → Prop) [DecidableRel I]
    (f : (Sum (Fin n) (Fin m) → Bool) → Bool)
    (hmono : ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true)
    (hpos : ∀ p l, I p l → f (edgeInput p l) = true)
    (hneg : ∀ P : Finset (Fin n), closureLeft I P = P →
      f (independentInput I P) = false) :
    ∀ z, f z = decide (∃ p l, I p l ∧ z (Sum.inl p) = true ∧
      z (Sum.inr l) = true) := by
  intro z
  by_cases h : ∃ p l, I p l ∧ z (Sum.inl p) = true ∧ z (Sum.inr l) = true
  · rw [decide_eq_true h]
    obtain ⟨p, l, hI, hp, hl⟩ := h
    apply hmono (edgeInput p l) z _ (hpos p l hI)
    intro i hi
    cases i with
    | inl a =>
      have ha : a = p := by simpa [edgeInput] using hi
      simpa [ha] using hp
    | inr b =>
      have hb : b = l := by simpa [edgeInput] using hi
      simpa [hb] using hl
  · rw [decide_eq_false h]
    let P := Finset.univ.filter fun p : Fin n => z (Sum.inl p) = true
    have hext : ∀ i, z i = true → independentInput I (closureLeft I P) i = true := by
      intro i hi
      cases i with
      | inl p =>
        apply decide_eq_true
        exact subset_closureLeft I P (by simp [P, hi])
      | inr l =>
        apply decide_eq_true
        rw [avoidingRight_closureLeft]
        apply (mem_avoidingRight I P l).2
        intro p hp hI
        have hp' : z (Sum.inl p) = true := (Finset.mem_filter.1 hp).2
        exact h ⟨p, l, hI, hp', hi⟩
    cases hf : f z with
    | false => rfl
    | true =>
      have ht := hmono z (independentInput I (closureLeft I P)) hext hf
      rw [hneg _ (closureLeft_idem I P)] at ht
      cases ht
end ReducedCheck
namespace CircuitCheckWrapper
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.Outside.L_meta_2583.ReducedCheck
def liftInput {n m : ℕ} (z : Sum (Fin n) (Fin m) → Bool) : Fin (n + m) → Bool :=
  Fin.addCases (fun p => z (Sum.inl p)) (fun l => z (Sum.inr l))
def lowerInput {n m : ℕ} (z : Fin (n + m) → Bool) : Sum (Fin n) (Fin m) → Bool :=
  Sum.elim (fun p => z (Fin.castAdd m p)) (fun l => z (Fin.natAdd n l))
lemma lift_lower {n m : ℕ} (z : Fin (n + m) → Bool) :
    liftInput (lowerInput z) = z := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro p
    simp [liftInput, lowerInput]
  · intro l
    simp [liftInput, lowerInput]
lemma ao2_monotone2 {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) : Monotone2 C := by
  intro g hg
  refine ⟨?_, (hAO.2.2 g hg).le⟩
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hAO.1 g hg
lemma circuitFun_lift_mono {n m : ℕ} {C : Circuit} (hAO : IsAO2 (n + m) C)
    {x y : Sum (Fin n) (Fin m) → Bool}
    (hxy : ∀ i, x i = true → y i = true)
    (hx : circuitFun (n + m) C (liftInput x) = true) :
    circuitFun (n + m) C (liftInput y) = true := by
  apply PEqualNP.Outside.L_meta_2583.Repair.pair_mono (ao2_monotone2 hAO) ?_ C.output hx
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro p hp
    simpa [liftInput] using hxy (Sum.inl p) (by simpa [liftInput] using hp)
  · intro l hl
    simpa [liftInput] using hxy (Sum.inr l) (by simpa [liftInput] using hl)
lemma ao2_exact_certificate {n m : ℕ} (I : Fin n → Fin m → Prop) [DecidableRel I]
    (C : Circuit) (hAO : IsAO2 (n + m) C)
    (hpos : ∀ p l, I p l → circuitFun (n + m) C (liftInput (edgeInput p l)) = true)
    (hneg : ∀ P : Finset (Fin n), closureLeft I P = P →
      circuitFun (n + m) C (liftInput (independentInput I P)) = false) :
    ∀ z : Fin (n + m) → Bool,
      circuitFun (n + m) C z = decide (∃ p l, I p l ∧
        z (Fin.castAdd m p) = true ∧ z (Fin.natAdd n l) = true) := by
  have hcert := exact_certificate I
    (fun v => circuitFun (n + m) C (liftInput v))
    (fun x y hxy hx => circuitFun_lift_mono hAO hxy hx) hpos hneg
  intro z
  have hz := hcert (lowerInput z)
  rw [lift_lower] at hz
  exact hz.trans (Bool.decide_congr (by rfl))
end CircuitCheckWrapper
namespace PurePointBudget
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_2583.Repair
end PurePointBudget
namespace Repair
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadK
end Repair
namespace ProjectedBudget
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_2583.Repair
open PEqualNP.Outside.L_meta_2583.PurePointBudget
end ProjectedBudget
namespace PlaneMatching
end PlaneMatching
namespace PathDegreeObstruction
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm
end PathDegreeObstruction
namespace PartialPointBudget
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_2583.Repair
open PEqualNP.Outside.L_meta_2583.PurePointBudget
end PartialPointBudget
namespace PackedEval
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
def gate (w : List ℕ) (g : Gate) : ℕ :=
  match g.op with
  | .and => (w.getD (g.inputs.getD 0 0) 0) &&& (w.getD (g.inputs.getD 1 0) 0)
  | .or => (w.getD (g.inputs.getD 0 0) 0) ||| (w.getD (g.inputs.getD 1 0) 0)
  | _ => 0
def wires (C : Circuit) (w : List ℕ) : List ℕ :=
  C.gates.foldl (fun w g => w ++ [gate w g]) w
def eval (C : Circuit) (w : List ℕ) : ℕ :=
  (wires C w).getD C.output 0
lemma testBit_getD (w : List ℕ) (r i : ℕ) :
    (w.getD i 0).testBit r = (w.map fun a => a.testBit r).getD i false := by
  induction w generalizing i with
  | nil => simp
  | cons a w ih =>
    cases i with
    | zero => simp
    | succ i => simpa using ih i
lemma gate_testBit (w : List ℕ) (g : Gate) (r : ℕ)
    (hop : g.op = .and ∨ g.op = .or) (hlen : g.inputs.length = 2) :
    (gate w g).testBit r =
      g.op.eval (g.inputs.map fun i => (w.map fun a => a.testBit r).getD i false) := by
  obtain ⟨a, b, hi⟩ := List.length_eq_two.mp hlen
  have ha := testBit_getD w r a
  have hb := testBit_getD w r b
  rcases hop with hop | hop
  · simpa [gate, hop, hi, GateOp.eval] using congrArg₂ (fun a b : Bool => a && b) ha hb
  · simpa [gate, hop, hi, GateOp.eval] using congrArg₂ (fun a b : Bool => a || b) ha hb
lemma fold_testBit (gs : List Gate) (w : List ℕ) (r : ℕ)
    (hgs : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) :
    (gs.foldl (fun w g => w ++ [gate w g]) w).map (fun a => a.testBit r) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (w.map fun a => a.testBit r) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    have hg := hgs g (by simp)
    have hs : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 :=
      fun g h => hgs g (by simp [h])
    simp only [List.foldl_cons]
    rw [ih _ hs]
    simp only [List.map_append, List.map_cons, List.map_nil, gate_testBit w g r hg.1 hg.2]
lemma wires_testBit (C : Circuit) (w : List ℕ) (r : ℕ)
    (hC : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) :
    (wires C w).map (fun a => a.testBit r) = C.wires (w.map fun a => a.testBit r) :=
  fold_testBit C.gates w r hC
lemma eval_testBit (C : Circuit) (w : List ℕ) (r : ℕ)
    (hC : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) :
    (eval C w).testBit r = C.eval (w.map fun a => a.testBit r) := by
  rw [eval, testBit_getD, wires_testBit C w r hC]
  rfl
lemma eval_testBit_of_isAO2 (n : ℕ) (C : Circuit) (w : List ℕ) (r : ℕ)
    (hC : IsAO2 n C) :
    (eval C w).testBit r = C.eval (w.map fun a => a.testBit r) :=
  eval_testBit C w r (fun g hg => ⟨hC.1 g hg, hC.2.2 g hg⟩)
end PackedEval
namespace PackedColumns
def col : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, j =>
    if j < n then
      let v := col n j
      v ||| (v <<< (2 ^ n))
    else if j = n then
      ((2 ^ (2 ^ n) - 1) <<< (2 ^ n))
    else 0
lemma col_testBit (n j : ℕ) (hj : j < n) (r : ℕ) :
    (col n j).testBit r = (decide (r < 2 ^ n) && r.testBit j) := by
  induction n generalizing j r with
  | zero => omega
  | succ n ih =>
    have hp : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [pow_succ]; omega
    by_cases hjn : j < n
    · rw [col, ite_eq_left hjn]
      simp only [Nat.testBit_lor, Nat.testBit_shiftLeft, ih j hjn]
      by_cases hr : r < 2 ^ n
      · have hn : ¬ 2 ^ n ≤ r := by omega
        have hr' : r < 2 ^ (n + 1) := by omega
        simp [hr, hn, hr']
      · have hn : 2 ^ n ≤ r := by omega
        have he : r.testBit j = (r - 2 ^ n).testBit j := by
          have h := Nat.testBit_two_pow_add_gt hjn (r - 2 ^ n)
          rw [Nat.add_sub_of_le hn] at h
          exact h
        by_cases hr' : r < 2 ^ (n + 1)
        · have hd : r - 2 ^ n < 2 ^ n := by omega
          simp [hr, hn, hr', hd, he]
        · have hd : ¬ r - 2 ^ n < 2 ^ n := by omega
          simp [hr, hn, hr', hd]
    · have he : j = n := by omega
      subst j
      simp only [col, Nat.lt_irrefl, ite_false, ite_true,
        Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
      by_cases hr : r < 2 ^ n
      · have hn : ¬ 2 ^ n ≤ r := by omega
        have hb := Nat.testBit_lt_two_pow hr
        simp [hn, hb]
      · have hn : 2 ^ n ≤ r := by omega
        by_cases hr' : r < 2 ^ (n + 1)
        · have hd : r - 2 ^ n < 2 ^ n := by omega
          have hb := Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt hn hr'
          simp [hn, hr', hd, hb]
        · have hd : ¬ r - 2 ^ n < 2 ^ n := by omega
          simp [hn, hr', hd]
lemma col_testBit_lt (n j r : ℕ) (hj : j < n) (hr : r < 2 ^ n) :
    (col n j).testBit r = r.testBit j := by
  simp [col_testBit n j hj r, hr]
end PackedColumns
namespace PackedLineColumns
def joinWords (ws : List Nat) : Nat := ws.foldr (· ||| ·) 0
lemma joinWords_bit (ws : List Nat) (r : Nat) :
    (joinWords ws).testBit r = ws.any (fun w => w.testBit r) := by
  induction ws with
  | nil => simp [joinWords]
  | cons w ws ih => simpa [joinWords, Nat.testBit_lor] using congrArg (fun b => w.testBit r || b) ih
end PackedLineColumns
namespace PackedInputCode
def code {n : Nat} (x : Fin n → Bool) : Fin (2 ^ n) :=
  ⟨(BitVec.ofBoolListLE (List.ofFn x)).toNat, by
    simpa using (BitVec.ofBoolListLE (List.ofFn x)).isLt⟩
lemma code_bit {n : Nat} (x : Fin n → Bool) (i : Fin n) :
    (code x).val.testBit i.val = x i := by
  unfold code
  rw [BitVec.testBit_toNat, BitVec.getLsbD_ofBoolListLE]
  simp [List.getD_eq_getElem?_getD]
end PackedInputCode

namespace Q3PackedColumnCache
lemma power_0 : (2 : Nat) ^ (2 ^ 0) = 2 := by
  decide
lemma power_1 : (2 : Nat) ^ (2 ^ 1) = 4 := by
  rw [show (2 : Nat) ^ 1 = 2 ^ 0 * 2 by decide, pow_mul, power_0]
  decide
lemma power_2 : (2 : Nat) ^ (2 ^ 2) = 16 := by
  rw [show (2 : Nat) ^ 2 = 2 ^ 1 * 2 by decide, pow_mul, power_1]
  decide
lemma power_3 : (2 : Nat) ^ (2 ^ 3) = 256 := by
  rw [show (2 : Nat) ^ 3 = 2 ^ 2 * 2 by decide, pow_mul, power_2]
  decide
lemma power_4 : (2 : Nat) ^ (2 ^ 4) = 65536 := by
  rw [show (2 : Nat) ^ 4 = 2 ^ 3 * 2 by decide, pow_mul, power_3]
  decide
lemma power_5 : (2 : Nat) ^ (2 ^ 5) = 4294967296 := by
  rw [show (2 : Nat) ^ 5 = 2 ^ 4 * 2 by decide, pow_mul, power_4]
  decide
lemma power_6 : (2 : Nat) ^ (2 ^ 6) = 18446744073709551616 := by
  rw [show (2 : Nat) ^ 6 = 2 ^ 5 * 2 by decide, pow_mul, power_5]
  decide
lemma power_7 : (2 : Nat) ^ (2 ^ 7) = 340282366920938463463374607431768211456 := by
  rw [show (2 : Nat) ^ 7 = 2 ^ 6 * 2 by decide, pow_mul, power_6]
  decide
lemma power_8 : (2 : Nat) ^ (2 ^ 8) = 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
  rw [show (2 : Nat) ^ 8 = 2 ^ 7 * 2 by decide, pow_mul, power_7]
  decide
lemma power_9 : (2 : Nat) ^ (2 ^ 9) = 13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096 := by
  rw [show (2 : Nat) ^ 9 = 2 ^ 8 * 2 by decide, pow_mul, power_8]
  decide
lemma power_10 : (2 : Nat) ^ (2 ^ 10) = 179769313486231590772930519078902473361797697894230657273430081157732675805500963132708477322407536021120113879871393357658789768814416622492847430639474124377767893424865485276302219601246094119453082952085005768838150682342462881473913110540827237163350510684586298239947245938479716304835356329624224137216 := by
  rw [show (2 : Nat) ^ 10 = 2 ^ 9 * 2 by decide, pow_mul, power_9]
  decide
lemma power_11 : (2 : Nat) ^ (2 ^ 11) = 32317006071311007300714876688669951960444102669715484032130345427524655138867890893197201411522913463688717960921898019494119559150490921095088152386448283120630877367300996091750197750389652106796057638384067568276792218642619756161838094338476170470581645852036305042887575891541065808607552399123930385521914333389668342420684974786564569494856176035326322058077805659331026192708460314150258592864177116725943603718461857357598351152301645904403697613233287231227125684710820209725157101726931323469678542580656697935045997268352998638215525166389437335543602135433229604645318478604952148193555853611059596230656 := by
  rw [show (2 : Nat) ^ 11 = 2 ^ 10 * 2 by decide, pow_mul, power_10]
  decide
lemma power_12 : (2 : Nat) ^ (2 ^ 12) = 1044388881413152506691752710716624382579964249047383780384233483283953907971557456848826811934997558340890106714439262837987573438185793607263236087851365277945956976543709998340361590134383718314428070011855946226376318839397712745672334684344586617496807908705803704071284048740118609114467977783598029006686938976881787785946905630190260940599579453432823469303026696443059025015972399867714215541693835559885291486318237914434496734087811872639496475100189041349008417061675093668333850551032972088269550769983616369411933015213796825837188091833656751221318492846368125550225998300412344784862595674492194617023806505913245610825731835380087608622102834270197698202313169017678006675195485079921636419370285375124784014907159135459982790513399611551794271106831134090584272884279791554849782954323534517065223269061394905987693002122963395687782878948440616007412945674919823050571642377154816321380631045902916136926708342856440730447899971901781465763473223850267253059899795996090799469201774624817718449867455659250178329070473119433165550807568221846571746373296884912819520317457002440926616910874148385078411929804522981857338977648103126085903001302413467189726673216491511131602920781738033436090243804708340403154190336 := by
  rw [show (2 : Nat) ^ 12 = 2 ^ 11 * 2 by decide, pow_mul, power_11]
  decide
lemma power_13 : (2 : Nat) ^ (2 ^ 13) = 1090748135619415929462984244733782862448264161996232692431832786189721331849119295216264234525201987223957291796157025273109870820177184063610979765077554799078906298842192989538609825228048205159696851613591638196771886542609324560121290553901886301017900252535799917200010079600026535836800905297805880952350501630195475653911005312364560014847426035293551245843928918752768696279344088055617515694349945406677825140814900616105920256438504578013326493565836047242407382442812245131517757519164899226365743722432277368075027627883045206501792761700945699168497257879683851737049996900961120515655050115561271491492515342105748966629547032786321505730828430221664970324396138635251626409516168005427623435996308921691446181187406395310665404885739434832877428167407495370993511868756359970390117021823616749458620969857006263612082706715408157066575137281027022310927564910276759160520878304632411049364568754920967322982459184763427383790272448438018526977764941072715611580434690827459339991961414242741410599117426060556483763756314527611362658628383368621157993638020878537675545336789915694234433955666315070087213535470255670312004130725495834508357439653828936077080978550578912967907352780054935621561090795845172954115972927479877527738560008204118558930004777748727761853813510493840581861598652211605960308356405941821189714037868726219481498727603653616298856174822413033485438785324024751419417183012281078209729303537372804574372095228703622776363945290869806258422355148507571039619387449629866808188769662815778153079393179093143648340761738581819563002994422790754955061288818308430079648693232179158765918035565216157115402992120276155607873107937477466841528362987708699450152031231862594203085693838944657061346236704234026821102958954951197087076546186622796294536451620756509351018906023773821539532776208676978589731966330308893304665169436185078350641568336944530051437491311298834367265238595404904273455928723949525227184617404367854754610474377019768025576605881038077270707717942221977090385438585844095492116099852538903974655703943973086090930596963360767529964938414598185705963754561497355827813623833288906309004288017321424808663962671333528009232758350873059614118723781422101460198615747386855096896089189180441339558524822867541113212638793675567650340362970031930023397828465318547238244232028015189689660418822976000815437610652254270163595650875433851147123214227266605403581781469090806576468950587661997186505665475715792896 := by
  rw [show (2 : Nat) ^ 13 = 2 ^ 12 * 2 by decide, pow_mul, power_12]
  decide
lemma col_1_0 : PackedColumns.col 1 0 = 2 := by
  rw [PackedColumns.col]
  simp only [Nat.lt_irrefl, ↓reduceIte]
  rw [power_0]
  decide
lemma col_2_0 : PackedColumns.col 2 0 = 10 := by
  rw [PackedColumns.col]
  simp only [show 0 < 1 by decide, ↓reduceIte]
  simp only [col_1_0]
  decide
lemma col_2_1 : PackedColumns.col 2 1 = 12 := by
  rw [PackedColumns.col]
  simp only [Nat.lt_irrefl, ↓reduceIte]
  rw [power_1]
  decide
lemma col_3_0 : PackedColumns.col 3 0 = 170 := by
  rw [PackedColumns.col]
  simp only [show 0 < 2 by decide, ↓reduceIte]
  simp only [col_2_0]
  decide
lemma col_3_1 : PackedColumns.col 3 1 = 204 := by
  rw [PackedColumns.col]
  simp only [show 1 < 2 by decide, ↓reduceIte]
  simp only [col_2_1]
  decide
lemma col_3_2 : PackedColumns.col 3 2 = 240 := by
  rw [PackedColumns.col]
  simp only [Nat.lt_irrefl, ↓reduceIte]
  rw [power_2]
  decide
lemma col_4_0 : PackedColumns.col 4 0 = 43690 := by
  rw [PackedColumns.col]
  simp only [show 0 < 3 by decide, ↓reduceIte]
  simp only [col_3_0]
  decide
lemma col_4_1 : PackedColumns.col 4 1 = 52428 := by
  rw [PackedColumns.col]
  simp only [show 1 < 3 by decide, ↓reduceIte]
  simp only [col_3_1]
  decide
lemma col_4_2 : PackedColumns.col 4 2 = 61680 := by
  rw [PackedColumns.col]
  simp only [show 2 < 3 by decide, ↓reduceIte]
  simp only [col_3_2]
  decide
lemma col_4_3 : PackedColumns.col 4 3 = 65280 := by
  rw [PackedColumns.col]
  simp only [Nat.lt_irrefl, ↓reduceIte]
  rw [power_3]
  decide
lemma col_5_0 : PackedColumns.col 5 0 = 2863311530 := by
  rw [PackedColumns.col]
  simp only [show 0 < 4 by decide, ↓reduceIte]
  simp only [col_4_0]
  decide
lemma col_5_1 : PackedColumns.col 5 1 = 3435973836 := by
  rw [PackedColumns.col]
  simp only [show 1 < 4 by decide, ↓reduceIte]
  simp only [col_4_1]
  decide
lemma col_5_2 : PackedColumns.col 5 2 = 4042322160 := by
  rw [PackedColumns.col]
  simp only [show 2 < 4 by decide, ↓reduceIte]
  simp only [col_4_2]
  decide
lemma col_5_3 : PackedColumns.col 5 3 = 4278255360 := by
  rw [PackedColumns.col]
  simp only [show 3 < 4 by decide, ↓reduceIte]
  simp only [col_4_3]
  decide
lemma col_5_4 : PackedColumns.col 5 4 = 4294901760 := by
  rw [PackedColumns.col]
  simp only [Nat.lt_irrefl, ↓reduceIte]
  rw [power_4]
  decide
lemma col_6_0 : PackedColumns.col 6 0 = 12297829382473034410 := by
  rw [PackedColumns.col]
  simp only [show 0 < 5 by decide, ↓reduceIte]
  simp only [col_5_0]
  decide
lemma col_6_1 : PackedColumns.col 6 1 = 14757395258967641292 := by
  rw [PackedColumns.col]
  simp only [show 1 < 5 by decide, ↓reduceIte]
  simp only [col_5_1]
  decide
lemma col_6_2 : PackedColumns.col 6 2 = 17361641481138401520 := by
  rw [PackedColumns.col]
  simp only [show 2 < 5 by decide, ↓reduceIte]
  simp only [col_5_2]
  decide
lemma col_6_3 : PackedColumns.col 6 3 = 18374966859414961920 := by
  rw [PackedColumns.col]
  simp only [show 3 < 5 by decide, ↓reduceIte]
  simp only [col_5_3]
  decide
lemma col_6_4 : PackedColumns.col 6 4 = 18446462603027742720 := by
  rw [PackedColumns.col]
  simp only [show 4 < 5 by decide, ↓reduceIte]
  simp only [col_5_4]
  decide
lemma col_6_5 : PackedColumns.col 6 5 = 18446744069414584320 := by
  rw [PackedColumns.col]
  simp only [Nat.lt_irrefl, ↓reduceIte]
  rw [power_5]
  decide
lemma col_7_0 : PackedColumns.col 7 0 = 226854911280625642308916404954512140970 := by
  rw [PackedColumns.col]
  simp only [show 0 < 6 by decide, ↓reduceIte]
  simp only [col_6_0]
  decide
lemma col_7_1 : PackedColumns.col 7 1 = 272225893536750770770699685945414569164 := by
  rw [PackedColumns.col]
  simp only [show 1 < 6 by decide, ↓reduceIte]
  simp only [col_6_1]
  decide
lemma col_7_2 : PackedColumns.col 7 2 = 320265757102059730318470218759311257840 := by
  rw [PackedColumns.col]
  simp only [show 2 < 6 by decide, ↓reduceIte]
  simp only [col_6_2]
  decide
lemma col_7_3 : PackedColumns.col 7 3 = 338958311018522360492699998064329424640 := by
  rw [PackedColumns.col]
  simp only [show 3 < 6 by decide, ↓reduceIte]
  simp only [col_6_3]
  decide
lemma col_7_4 : PackedColumns.col 7 4 = 340277174703306882242637262502835978240 := by
  rw [PackedColumns.col]
  simp only [show 4 < 6 by decide, ↓reduceIte]
  simp only [col_6_4]
  decide
lemma col_7_5 : PackedColumns.col 7 5 = 340282366841710300967557013907638845440 := by
  rw [PackedColumns.col]
  simp only [show 5 < 6 by decide, ↓reduceIte]
  simp only [col_6_5]
  decide
lemma col_7_6 : PackedColumns.col 7 6 = 340282366920938463444927863358058659840 := by
  rw [PackedColumns.col]
  simp only [Nat.lt_irrefl, ↓reduceIte]
  rw [power_6]
  decide
lemma col_8_0 : PackedColumns.col 8 0 = 77194726158210796949047323339125271902179989777093709359638389338608753093290 := by
  rw [PackedColumns.col]
  simp only [show 0 < 7 by decide, ↓reduceIte]
  simp only [col_7_0]
  decide
lemma col_8_1 : PackedColumns.col 8 1 = 92633671389852956338856788006950326282615987732512451231566067206330503711948 := by
  rw [PackedColumns.col]
  simp only [show 1 < 7 by decide, ↓reduceIte]
  simp only [col_7_1]
  decide
lemma col_8_2 : PackedColumns.col 8 2 = 108980789870415242751596221184647442685430573802955824978313020242741769072880 := by
  rw [PackedColumns.col]
  simp only [show 2 < 7 by decide, ↓reduceIte]
  simp only [col_7_2]
  decide
lemma col_8_3 : PackedColumns.col 8 3 = 115341536360906404779899502576747487978354537254490211650198994186870666100480 := by
  rw [PackedColumns.col]
  simp only [show 3 < 7 by decide, ↓reduceIte]
  simp only [col_7_3]
  decide
lemma col_8_4 : PackedColumns.col 8 4 = 115790322417210952336529717160220497262186272106556906860092653394915770695680 := by
  rw [PackedColumns.col]
  simp only [show 4 < 7 by decide, ↓reduceIte]
  simp only [col_7_4]
  decide
lemma col_8_5 : PackedColumns.col 8 5 = 115792089210356248762697446947946071893095522863849111501270640965525260206080 := by
  rw [PackedColumns.col]
  simp only [show 5 < 7 by decide, ↓reduceIte]
  simp only [col_7_5]
  decide
lemma col_8_6 : PackedColumns.col 8 6 = 115792089237316195417293883273301227089774477609353836086800156426807153786880 := by
  rw [PackedColumns.col]
  simp only [show 6 < 7 by decide, ↓reduceIte]
  simp only [col_7_6]
  decide
lemma col_8_7 : PackedColumns.col 8 7 = 115792089237316195423570985008687907852929702298719625575994209400481361428480 := by
  rw [PackedColumns.col]
  simp only [Nat.lt_irrefl, ↓reduceIte]
  rw [power_7]
  decide
lemma col_9_0 : PackedColumns.col 9 0 = 8938538619961731399716016665470564084986243880394928918482374295814509353382364651201249532111268951793354572124324033902502588541297713297622432670722730 := by
  rw [PackedColumns.col]
  simp only [show 0 < 8 by decide, ↓reduceIte]
  simp only [col_8_0]
  decide
lemma col_9_1 : PackedColumns.col 9 1 = 10726246343954077679659219998564676901983492656473914702178849154977411224058837581441499438533522742152025486549188840683003106249557255957146919204867276 := by
  rw [PackedColumns.col]
  simp only [show 1 < 8 by decide, ↓reduceIte]
  simp only [col_8_1]
  decide
lemma col_9_2 : PackedColumns.col 9 2 = 12619113345828326681952023527723149296451167831145782002563351947032248498892750095813528751215909108414147631234339812568238948528890889361349316711608560 := by
  rw [PackedColumns.col]
  simp only [show 2 < 8 by decide, ↓reduceIte]
  simp only [col_8_2]
  decide
lemma col_9_3 : PackedColumns.col 9 3 = 13355637471071225126423931515722554897411352724014212858744092333045803858750303603351283347590378511628981150567083381395178964979993470452478654262869760 := by
  rw [PackedColumns.col]
  simp only [show 3 < 8 by decide, ↓reduceIte]
  simp only [col_8_3]
  decide
lemma col_9_4 : PackedColumns.col 9 4 = 13407603346151304507647333602124270744930157291580986197148043437687863763597662002711256755796972443613438635551055889478487182262900810351549134401372160 := by
  rw [PackedColumns.col]
  simp only [show 4 < 8 by decide, ↓reduceIte]
  simp only [col_8_4]
  decide
lemma col_9_5 : PackedColumns.col 9 5 = 13407807926820848549984871490950625460264621687587329935306297008442977448960781863686381587396241115434734742314166555940848600484775015044616064818216960 := by
  rw [PackedColumns.col]
  simp only [show 5 < 8 by decide, ↓reduceIte]
  simp only [col_8_5]
  decide
lemma col_9_6 : PackedColumns.col 9 6 = 13407807929942597098847186273910239236969444018900783322580063136098668673514857287274768220802268387129003177701362428774192761570871467260109520434626560 := by
  rw [PackedColumns.col]
  simp only [show 6 < 8 by decide, ↓reduceIte]
  simp only [col_8_6]
  decide
lemma col_9_7 : PackedColumns.col 9 7 = 13407807929942597099574024998205846127439963814395998898511282403621620416268583029620646167694378705270794824322841769944638336182637648515027502377205760 := by
  rw [PackedColumns.col]
  simp only [show 7 < 8 by decide, ↓reduceIte]
  simp only [col_8_7]
  decide
lemma col_9_8 : PackedColumns.col 9 8 = 13407807929942597099574024998205846127479365820592393377723561443721764030073431184712636981971479856705023170278632780869088242247907112362425735876444160 := by
  rw [PackedColumns.col]
  simp only [Nat.lt_irrefl, ↓reduceIte]
  rw [power_8]
  decide
lemma col_10_0 : PackedColumns.col 10 0 = 119846208990821060515287012719268315574531798596153771515620054105155117203667308755138984881605024014080075919914262238439193179209611081661898287092982749585178595616576990184201479734164062746302055301390003845892100454894975254315942073693884824775567007123057532159964830625653144203223570886416149424810 := by
  rw [PackedColumns.col]
  simp only [show 0 < 9 by decide, ↓reduceIte]
  simp only [col_9_0]
  decide
lemma col_10_1 : PackedColumns.col 10 1 = 143815450788985272618344415263121978689438158315384525818744064926186140644400770506166781857926028816896091103897114686127031815051533297994277944511579299502214314739892388221041775680996875295562466361668004615070520545873970305179130488432661789730680408547669038591957796750783773043868285063699379309772 := by
  rw [PackedColumns.col]
  simp only [show 1 < 9 by decide, ↓reduceIte]
  simp only [col_9_1]
  decide
lemma col_10_2 : PackedColumns.col 10 2 = 169194647987041497198052253250731739634633127429864148022051841089630753699295024124902096303442386843407166004584840807208272723590039174110915228837152117061428605576343986142402089036466912112426431013727064253024141818675259182563682927567837399683153421820787104225832702059745615345727394192587505070320 := by
  rw [PackedColumns.col]
  simp only [show 2 < 9 by decide, ↓reduceIte]
  simp only [col_9_2]
  decide
lemma col_10_3 : PackedColumns.col 10 3 = 179069821994067265517004719393770557123035839147560499073922571114317373565012632536861362624654977515201358572945823733699027940920197102560968646862666832065013932750060561209079253766221790251284004808302573839776523636885877422791135238515376547524582609864801915756523326693582908070186191519003118206720 := by
  rw [PackedColumns.col]
  simp only [show 3 < 9 by decide, ↓reduceIte]
  simp only [col_9_3]
  decide
lemma col_10_4 : PackedColumns.col 10 4 = 179766570466052360237648572536963127610949142151705149077185617265867657072940646045213890928808158455225716514812268414598264282604049739409665520460023745597470080465874001603182053859457467143941243028332742390810947146161643764595180884270010128854499581430719252352917935056902309958553029775825154539520 := by
  rw [PackedColumns.col]
  simp only [show 4 < 9 by decide, ↓reduceIte]
  simp only [col_9_4]
  decide
lemma col_10_5 : PackedColumns.col 10 5 = 179769313444375785814462265863485611229889718115776549548420631039577310219318555512504201030636628662239812719543346771400604958784932998973090366819193438631844709885019339289485527600645229101680144570744617427323613239093066544488844122372018577072445227788470567772585250041087614243742592599359351685120 := by
  rw [PackedColumns.col]
  simp only [show 5 < 9 by decide, ↓reduceIte]
  simp only [col_9_5]
  decide
lemma col_10_6 : PackedColumns.col 10 6 = 179769313486231590763185205067502474281972610037491134208877555181135709923949037735690276024213413705823039792595812100825199281213020878487102478859428781160318831728534053767098825058678708531551206723464342007537350133167915838047987720003371153224504147359993809275143228500884134199151686065190149816320 := by
  rw [PackedColumns.col]
  simp only [show 6 < 9 by decide, ↓reduceIte]
  simp only [col_9_6]
  decide
lemma col_10_7 : PackedColumns.col 10 7 = 179769313486231590772930519078902473361269403363094992027077741372816159198983668324764656509214724291581902479869920821760871587342679845464593386307578492764517105656857966598509267284159204378328176331317696638943488431251920295735812264550083217605459765810970935573515804682568218669795142748890432798720 := by
  rw [PackedColumns.col]
  simp only [show 7 < 9 by decide, ↓reduceIte]
  simp only [col_9_7]
  decide
lemma col_10_8 : PackedColumns.col 10 8 = 179769313486231590772930519078902473361797697894230657273430081157732675805499410614616176613472387041631651377316136471641673072203277570454821379686787760899244944958633938372376730076395090525612731964434268678008150116831451773765893368201788358737656950422124978427902852027528247743196825908506284523520 := by
  rw [PackedColumns.col]
  simp only [show 8 < 9 by decide, ↓reduceIte]
  simp only [col_9_8]
  decide
lemma col_10_9 : PackedColumns.col 10 9 = 179769313486231590772930519078902473361797697894230657273430081157732675805500963132708477322407536021120113879871393357658789768814416622492847430639474110969959963482268385702277221395399966640087262359691628045276706960578432807926936308666529070259922820652728111753896392184596904358265409895975218053120 := by
  rw [PackedColumns.col]
  simp only [Nat.lt_irrefl, ↓reduceIte]
  rw [power_9]
  decide
lemma col_11_0 : PackedColumns.col 11 0 = 21544670714207338200476584459113301306962735113143656021420230285016436759245260595464800941015275642459145307281265346329413039433660614063392101590965522080420584911533997394500131833593101404530705092256045045517861479095079837441225396225650780313721097234690870028591717261027377205738368266082620257014609555593112228280456649857709712996570784023550881372051870439554017461805640209433505728576118077817295735812307904905065567434867763936269131742155524820818083789807213473150104734484620882313119028387104465290030664845568665758810350110926291557029068090288819736430212319069968098795703902407373064153770 := by
  rw [PackedColumns.col]
  simp only [show 0 < 10 by decide, ↓reduceIte]
  simp only [col_10_0]
  decide
lemma col_11_1 : PackedColumns.col 11 1 = 25853604857048805840571901350935961568355282135772387225704276342019724111094312714557761129218330770950974368737518415595295647320392736876070521909158626496504701893840796873400158200311721685436846110707254054621433774914095804929470475470780936376465316681629044034310060713232852646886041919299144308417531466711734673936547979829251655595884940828261057646462244527464820954166768251320206874291341693380754882974769485886078680921841316723522958090586629784981700547768656167780125681381545058775742834064525358348036797814682398910572420133111549868434881708346583683716254782883961718554844682888847676984524 := by
  rw [PackedColumns.col]
  simp only [show 1 < 10 by decide, ↓reduceIte]
  simp only [col_10_1]
  decide
lemma col_11_2 : PackedColumns.col 11 2 = 30416005714175065694790472177571719492182684865614573206710913343552616601287426723009130740256859730530558080867668724229759585082814984560082966951951325290005531639812702204000186118013790218160995424361475358378157382251877417564082912318565807501723901978387110628600071427332767819865931669763699186373566431425570204631232917446178418348099930386189479584073228855840965828431492060376713969754519639271476332911493512807151389319813313792379950694807799747037294762080771962094265507507700069147932745958265127468278585664332234012438141333072411609923390245113627863195593862216425551240993744575114914099440 := by
  rw [PackedColumns.col]
  simp only [show 2 < 10 by decide, ↓reduceIte]
  simp only [col_10_2]
  decide
lemma col_11_3 : PackedColumns.col 11 3 = 32191258965975166805381355767702364598730312386953945183756297390841679827043502212678924363229049987176310498038933435760679405223835314398220105100897900696036982902836789881276461572372571748403855079479849406532524544640119290184554677628987936344236970187242389459063110615698493568107133907298545442387587818473755236029943009904126575061024050836745285785478281123691605857328271752616599999117623898372924367906327764527413143560269343780262048984388021522156203016676925967663969720008149489526216758368280601834131421403495593974253597052901540692214638702999637271553313348338006809095526453402456251498240 := by
  rw [PackedColumns.col]
  simp only [show 3 < 10 by decide, ↓reduceIte]
  simp only [col_10_3]
  decide
lemma col_11_4 : PackedColumns.col 11 4 = 32316512960456508147453349385365121560029673505996215291052295923497502161845157660200677353335759292556934560431168784130592175847026458411091401113848279332188918918220823044523566226246795557791574734716850819454473882554323944334074207708109530615683335254269363676864674514061298027570754749667911282871724029983449112545310443072040154819642253271451940772360453967833714276902233168258408946731567076945106428632575740174062980318251379617483264824158211574922576695198259201131389838088044481970625035728915228891636395882917773452463381865274549723395723172372127735020455495580422417626880638757562929315840 := by
  rw [PackedColumns.col]
  simp only [show 4 < 10 by decide, ↓reduceIte]
  simp only [col_10_4]
  decide
lemma col_11_5 : PackedColumns.col 11 5 = 32317006063786617977917430647786889867906369439928774745874403061933612682200576450810216481426203250827948543126557362463291876111646222960360790085163651852238641429717120847798370265322261673906889097924268663692940257295126353200399956021066277899174676540581348497257723324380162489733907944315511759482739072698058393384635692285896212301876001058488500506831120565403102471120452564365415396618005887063102909747528554645081362840155633503159179847489820241277356288078525972093195870585301724764277428214574822136154041715694457110709920357539707654728889907475699213364849177130473778351627777064507057111040 := by
  rw [PackedColumns.col]
  simp only [show 5 < 10 by decide, ↓reduceIte]
  simp only [col_10_5]
  decide
lemma col_11_6 : PackedColumns.col 11 6 = 32317006071311007298962968279132820423318564169544585575840362784271006144270719271112334871465990491032121249854708136351097131222229533897039842809000575024469795858601452903608286950487291036173656424642694699111215656720330692156806652878176294560992911131049744850351554674082581482982160517647675979048835286736621524221873911053756802868040397366267058518789526418606983189736261563041441886139662520217871559010598356884184331324030205339382405674779699808810844071987274263786247133048684130104820097246644482379610721840409187043258179179795737779347699068638486420172878212978512006155262375419323025981440 := by
  rw [PackedColumns.col]
  simp only [show 6 < 10 by decide, ↓reduceIte]
  simp only [col_10_6]
  decide
lemma col_11_7 : PackedColumns.col 11 7 = 32317006071311007300714876688669951960349131524534694890724875563828770168877477517674144147156520330032050859708107053367541780354298485118594865664828671846811824087147165337278333530998363043786544832224103197459486604404605511324149101655290064231896878300552753692653117794267740933710191915457110569482353408144600202632326067708533016730171645788373932339760925266412651919717201339056200596183833289262707915216292923080049316321410249206727677420171938451885976792643871821700059247191423513203065085185628574928209860250798213758159017512799345696238071622024309939738578610163879497403419196726710621962240 := by
  rw [PackedColumns.col]
  simp only [show 7 < 10 by decide, ↓reduceIte]
  simp only [col_10_7]
  decide
lemma col_11_8 : PackedColumns.col 11 8 = 32317006071311007300714876688669951960444102669715484032130345427524655138867611798085573559146505641014799895848992131558773898897874931575600122725169680536153603186965708812344954253910382450831936435667181350651846563501034918154134916228896586215374039929970959986026631115266885080258995661844475996688216120407152368914262326688954297921116905358475567711539686747169438627081137712541397537050050280114428159335126130122919957080213913170378129944336867880090300295888143939010064438356220959263775585323618856951444769654532129484978655322733173025761463008789789037153537230130181217227468995996591943843840 := by
  rw [PackedColumns.col]
  simp only [show 8 < 10 by decide, ↓reduceIte]
  simp only [col_10_8]
  decide
lemma col_11_9 : PackedColumns.col 11 9 = 32317006071311007300714876688669951960444102669715484032130345427524655138867890893197201411522913463688717960921898019494119559150490921095088152386448280710318450446268407511633591722075539194702809692695116208601753153385228164358637425253452063124531982403270024154882788029124087013649227429510942494747442647489815192386233134523565554286718296887677415327531178143142900963914851815895844970678619654931422375297655621241901859303687650732732577258002390973227976426601145541195422760363881209530177954039354611088039227582300249931078656601680784145297277963248059010428202344946224651318834406502274474967040 := by
  rw [PackedColumns.col]
  simp only [show 9 < 10 by decide, ↓reduceIte]
  simp only [col_10_9]
  decide
lemma col_11_10 : PackedColumns.col 11 10 = 32317006071311007300714876688669951960444102669715484032130345427524655138867890893197201411522913463688717960921898019494119559150490921095088152386448283120630877367300996091750197750389652106796057638384067568276792218642619756161838094338476170470581645852036305042887575891541065808607552399123930385521734564076182110829912044267485667021494378337432091400804375578173293516902959351017550115541769580704823489838590463999939561383487229281910850182593813106849357791285954724448854882125685229350225459628571692166207846586010535756741612055848610098380251624748643306405371232666472431888720497281435372093440 := by
  rw [PackedColumns.col]
  simp only [Nat.lt_irrefl, ↓reduceIte]
  rw [power_10]
  decide
lemma col_12_0 : PackedColumns.col 12 0 = 696259254275435004461168473811082921719976166031589186922822322189302605314371637899217874623331705560593404476292841891991715625457195738175490725234243518630637984362473332226907726756255812209618713341237297484250879226265141830448223122896391078331205272470535802714189365826745739409645318522398686004457959317921191857297937086793507293733052968955215646202017797628706016677314933245142810361129223706590194324212158609622997822725207915092997650066792694232672278041116729112222567034021981392179700513322410912941288676809197883891458727889104500814212328564245417033483998866941563189908397116328129744682537670608830407217154556920058405748068556180131798801542112678452004450130323386614424279580190250083189343271439423639988527008933074367862847404554089393722848589519861036566521969549023011376815512707596603991795334748642263791855252632293744004941963783279882033714428251436544214253754030601944091284472228570960486965266647934520977175648815900178168706599863997393866312801183083211812299911637106166785552713648746288777033871712147897714497582197923275213013544971334960617744607249432256718941286536348654571559318432068750723935334201608978126484448810994340754401947187825355624060162536472226935436126890 := by
  rw [PackedColumns.col]
  simp only [show 0 < 11 by decide, ↓reduceIte]
  simp only [col_11_0]
  decide
lemma col_12_1 : PackedColumns.col 12 1 = 835511105130522005353402168573299506063971399237907024307386786627163126377245965479061449547998046672712085371551410270390058750548634885810588870281092222356765581234967998672289272107506974651542456009484756981101055071518170196537867747475669293997446326964642963257027238992094887291574382226878423205349551181505430228757524504152208752479663562746258775442421357154447220012777919894171372433355068447908233189054590331547597387270249498111597180080151233079206733649340074934667080440826377670615640615986893095529546412171037460669750473466925400977054794277094500440180798640329875827890076539593755693619045204730596488660585468304070086897682267416158158561850535214142405340156388063937309135496228300099827211925727308367986232410719689241435416885464907272467418307423833243879826363458827613652178615249115924790154401698370716550226303158752492805930356539935858440457313901723853057104504836722332909541366674285152584358319977521425172610778579080213802447919836796872639575361419699854174759893964527400142663256378495546532440646054577477257397098637507930255616253965601952741293528699318708062729543843618385485871182118482500868722401041930773751781338573193208905282336625390426748872195043766672322523352268 := by
  rw [PackedColumns.col]
  simp only [show 1 < 11 by decide, ↓reduceIte]
  simp only [col_11_1]
  decide
lemma col_12_2 : PackedColumns.col 12 2 = 982954241330025888651061374792117065957613410868125910949866807796662501620289371151836999468232996085543629848884012082811833824174864571541869259154226143949135977923491763143869731891184676060638183540570302330707123613550788466515138526441963875291113325840756427361208516461288102695969861443386380241587707272359329680891205299002598532329015956172069147579319243711114376485621082228436908745123609938715568457711282742997173396788528821307761388329589685975537333705105970511373035812736914906606636018808109524152407543730632306670294674666971059973005640325993529929624468988623383326929501811286771404257700240859525280777159374475376572820802667548421363013941806134285182753125162428161540159407327411882149661089090951021160273424376104989924019865252832085255786244028039110446854545245679545473151312057783440929593413762789078294383886069120579771682772399924539341714486943204533008358240984379215187695725499159003040421552914731088438365621857741428002879905690349261928912189905529240205599875252385176638427360445288878273459583593620561479290704279421094418372063488943473813286504352139656544387698639551041748083743668802942198496942402271498531507457144933186947390984265165207939849641227960790967674532080 := by
  rw [PackedColumns.col]
  simp only [show 2 < 11 by decide, ↓reduceIte]
  simp only [col_11_2]
  decide
lemma col_12_3 : PackedColumns.col 12 3 = 1040325111446564364642368458923952692375372948467432870732932963893743970586454120440854723172604571732559795015161289052625754086286237990114351900739103156241887105039648869942150066437362769994138466626595806357791196976209394797245594082459977331047403986882045713004858818978483906355267713278603484146738740770746060985223376814508586773515534397193785245687061612021101596903069783525816494858652225304788461558355910140448370287651672526831560691150382858308739901820189976572348115723986151185202354074380567278480369073520357927682179577857650304718511806103775253466372978851772608034726943551245143276101534885267668779655203695942811003141082978883932337508918954352239570851556592141867466627855225898956983298895847232209165736853814399055483787561668367031866046141539403260862040608197762009216720454784891423863227270597193110101449093427240457968473595691748928797456577620823474623632068279187340587755787298720812556399464563450801771344160098465635862970172559435794726319516164606822318767183146493260878024288097737645487863839445388298530611173400788084364969654743161964502777934567245083969157408676878923562174234544414008863778865110575282492490382659228898247822364669746834862408958809359280712869543680 := by
  rw [PackedColumns.col]
  simp only [show 3 < 11 by decide, ↓reduceIte]
  simp only [col_11_3]
  decide
lemma col_12_4 : PackedColumns.col 12 4 = 1044372945546673828197059762417026954800502571456876931065827327471461972821825678502902390206631368287052718825052894233034066448646477102180500179340327980460903556994805658654408001145108432846397576884767250437032492049663068228640037320493871073809768575078864634481524503993658744936841378031125630239135682634068157595553907065934494117874392161071967268630592757954931050604189499026969785460738929265188251870658590413970416374951231195893953659645177365668990274509878983454352918652249826186380720497759224291404556847049016414820116251680890624350219398922434372584335734388449630404515847080634152714058809270664364623816701429169315371754247697433994176562656146066230462875407957492679621654635564983813385495231023408174091462213500113564221574854773413548995695679450698374027425358111405131610944537607879160761240956820277539402086435979141617874815978878367113591440913603448709010757297957250003996973141247805662445803646376223433329878923069384486850123343958838515748874889108470208492856409563667617066496390779656608815440708680455115994414915549760435273816066113220195745407416742423189412069582551371258052742225599983009157662680521765857237071078259853024604738224458732986851207870637736939387843706880 := by
  rw [PackedColumns.col]
  simp only [show 4 < 11 by decide, ↓reduceIte]
  simp only [col_11_4]
  decide
lemma col_12_5 : PackedColumns.col 12 5 = 1044388881169986771263999928297300478070936649208137728716943272393150591271948624420606938378920325202647294538519193960583205430494401530480726046945869627125087576581441327184118791310492792158585976224097806280786892334766443875874066521728508219835242054530032570439342984842587365877130096578662750128451040500682764243793544319987273001483203699431458496061689471587577966752850769161623090706823127685972966430520428544916906687945372820189637536712212655530164534640139529398430844193326157970231116707311043062974574041904731135129602518839900824182031247902924614891437360369084692512773049940085501258098285770563207273639006194329011676441358313778892352118743746625795899402033165894235998571329265373996173471467022665683468183571100746705885850316405201516404038307610261005853895790796714546886639039188218465580120113917176202211286567528963263244593849404764230833283608612046582861144620238070068732151016953715065309433503193260162865354888677237019030264347447682156758356038253494239532670303481845396141046688302205997576446382970422445081164582128534982238690352916408567003808683045489108822658780334520875388558807595660704043381189270580666647121408487807204873312099823339727666234219348909033811901153280 := by
  rw [PackedColumns.col]
  simp only [show 5 < 11 by decide, ↓reduceIte]
  simp only [col_11_5]
  decide
lemma col_12_6 : PackedColumns.col 12 6 = 1044388881413152506635136276009232092089202823436447410265032820226910016431650373821674532042254867838139147378579230266491649995086065497860958814445672983098674523922997302141987634666555615082983722320304956269495278966036628895198106523331321502350737542153318103393882108000571554757684726905909324459997731583883472732858966036228952156530271920897101714520128973521712735784643100820956652071166631477054434832397108876846187098344767158469121788585996206841660890750835750693609949169201177900602307658491760075332453005821036069979320207117722662159235830901138134661393429664477233482343753829841470905483136731221333733877769217174834552514251616968573563993492617495295314148382180608135581157273932514282997974199539452706406993951290912724329624341760460719763633771633144874653690249377653301500883009114539659231880768729006104695088072439311612787369829426929753368862093420031376900651804074900837670263910502048479989177994719261381762582742114295637847119814372497857489551334050635355850952294274817187604959104441222319544162008246019080907519047450074089096679813611777251441599542273895187986028643056257369619265109472987219292553483853374985528466622647542440199749314968114021310984993945131021102041006080 := by
  rw [PackedColumns.col]
  simp only [show 6 < 11 by decide, ↓reduceIte]
  simp only [col_11_6]
  decide
lemma col_12_7 : PackedColumns.col 12 7 = 1044388881413152506691752710716624382576895065971976858589353558325762581703586392634626505372588775243352352872105555185162748037255922495907952398447320058874700219096305073257981830242798435018035019686250651065418447415300338976514028339919790540980387792506834595479320761864581409260493792716549666612049159545942355726765079667777658031392208221100212494804933965627458645374255563389838434653801141053202689771772723357135216290338695574272496666981821274149184005607430785375049614222602832045450996628806886507199929541770466891583529548235274898663973127724463951951808300980838223831519578183355159780297410327421594977202888369167777179438592323739958538795846107460850234988177201145750964409766625686468495075918326548817949557684257813730076538763495642113203681518969810948925707607978938570829087460191619207747778301032821196208427179851985730907623422392806420997835744218954081402941621610986598423511742048440577277941329354904592254225541145045407068107116812699371822895596907372297376022604084695037964149568827092433282418334219228004804244213575376376596603956419390270373352068036894356733923812512845494539668164417753658652817480459690527778339054327242899088717363700792681812630673715267993584984391680 := by
  rw [PackedColumns.col]
  simp only [show 7 < 11 by decide, ↓reduceIte]
  simp only [col_11_7]
  decide
lemma col_12_8 : PackedColumns.col 12 8 = 1044388881413152506691752710716624382579964249047383780384233483283953907971548437330409861406439184862803595481780311363145047917784297492335081783587410389201085291003814724679247064006671965573116422575979128538114100332241674615061933189180684714263835399074900879577540164624257737073754377690779747879247076068708297591543861086689922251656106269806526857140849097848020246865224175226804081438728633403210458335090491660415105742009535386950924884328661026761230353637743702090864583446899967829903677272414380179127411591801030617544226984469391350202964315137212226053642808605295196669336567154773082816496671483611706639790862104308694690915303767542225100781954758506791181210226942698767971330918318987522521788982684753862563089534063043478107744494626356398106199729676496226503074872846326045491459111066027723006347168934171097334117299464743656642561004725739279259315461208549110360886408197976252866883289138591398644610234775266782248621442697914105954021224136874892190232353067578327032607013349675284007976635788833539884684616422541182911816223459033073906897174276429338970188739690807348257688010677971263071629760560585335781557762874848132251630064790978167461342051030462977170181956787177465479828602880 := by
  rw [PackedColumns.col]
  simp only [show 8 < 11 by decide, ↓reduceIte]
  simp only [col_11_8]
  decide
lemma col_12_9 : PackedColumns.col 12 9 = 1044388881413152506691752710716624382579964249047383780384233483283953907971557456848826811934997558340890106714439262837987573438185793607263236087851365200051875641980331233831654138225785083950552277465749725235095346794307599601916087333516532942974033504539897429691338256245201060803893914535756384924762851404239611614608500917109405562380204866454265949087291595759606743764877742468162792104667105495459173531264931375171503341077321717949680998881907145818504688483711045395643582170427950798206975128373353831495314746178286730941650689781849877290214668035731179963609644181307854096174130583818979052166921580848728037242695212949929951551042190561929025086448680160504932230311456540897613584640906445984196552467049924272345293647753175864255808082351549504606730041888017823936400114385158144513058535899526249634545253015374794054599883356218175227331452924722558549936960733419533892684504472716145406068552393021232726327979635228876199079965686627072767760143813112977632709390627732330807247612718081853317533368977597841535037065250244845293595869833157234580037901524982220379728456454033998120376310912300218496266262777387344074565011593368670327711483761631037639070577436688718671720575540186699288312545280 := by
  rw [PackedColumns.col]
  simp only [show 9 < 11 by decide, ↓reduceIte]
  simp only [col_11_9]
  decide
lemma col_12_10 : PackedColumns.col 12 10 = 1044388881413152506691752710716624382579964249047383780384233483283953907971557456848826811934997558340890106714439262837987573438185793607263236087851365277945956976543709998340361590134383718314428070011855946226376318839397712745672334684344586617496807908705803704071284048740118609114467977783598029006681129370886417827884046127656956366228892478256460574066365210290771821284975289641976879497160717152633965328563257396990506204493271825517833589428002008947976305421968653169489800700043920461069306004176574557017203334673772721009211507464275228928957284067323355657482772548674267805293784364913069105690745579399763137016726168676614418373815785804419263443829994913528343726197924232233843448230234354442216902501675118478607266340496883906056813968109678650873269623047506144251207192348736722002959785894766663346330782590857255426849356308544146420467254325915846046997571423088052709552219416707951538967168791556618640795272589062502312550940406613158238821101345989328956470661586832993202111821078441535291621023613008604897804903434271160062834068634843945666266783530255900254990723856788556496635177956672584474648141783972986500343820889912556558586040315196548818440919773527784966907775417291159271196590080 := by
  rw [PackedColumns.col]
  simp only [show 10 < 11 by decide, ↓reduceIte]
  simp only [col_11_10]
  decide
lemma col_12_11 : PackedColumns.col 12 11 = 1044388881413152506691752710716624382579964249047383780384233483283953907971557456848826811934997558340890106714439262837987573438185793607263236087851365277945956976543709998340361590134383718314428070011855946226376318839397712745672334684344586617496807908705803704071284048740118609114467977783598029006686938976881787785946905630190260940599579453432823469303026696443059025015972399867714215541693835559885291486318237914434496734087811872639496475100189041349008417061675093668333850551032972088269550769983616369411933015213796825837188091833656751221318492846368125550225998300412344784862595674492194617023774188907174299818431120503398938670142390167527982718281038672250482020056617189028439217958762461661095296946237237440488670954249120630699182954444685807463642006912490558758032756573144864958427211423010838419416209904320775931621040854102139836942364029067786745528754801263275255572023493503792206541186428523051062105479286926994901193978367674231926737841718190431468443009066164503568191274591482133452385466754657575807952456415920200667342675683651625588293191772291620716891753772421453754942251261942325159403931650834773087264785777247077752391129614356077901998275463259428483942050248854729343557959680 := by
  rw [PackedColumns.col]
  simp only [Nat.lt_irrefl, ↓reduceIte]
  rw [power_11]
  decide
lemma col_13_0 : PackedColumns.col 13 0 = 727165423746277286308656163155855241632176107997488461621221857459814221232746196810842823016801324815971527864104683515406580546784789375740653176718369866052604199228128659692406550152032136773131234409061092131181257695072883040080860369267924200678600168357199944800006719733351023891200603531870587301567001086796983769274003541576373343231617356862367497229285945835179130852896058703745010462899963604451883427209933744070613504292336385342217662377224031494938254961874830087678505012776599484243829148288184912050018418588696804334528507800630466112331505253122567824699997933974080343770033410374180994328343561403832644419698021857547670487218953481109980216264092423501084273010778670285082290664205947794297454124937596873776936590492956555251618778271663580662341245837573313593411347882411166305747313238004175741388471143605438044383424854018014873951709940184506107013918869754940699576379169947311548654972789842284922526848298958679017985176627381810407720289793884972893327974276161827607066078284040370989175837543018407575105752255579080771995758680585691783696891193277129489622637110876713391475690313503780208002753816997223005571626435885957384720652367052608645271568520036623747707393863896781969410648618319918351825706672136079039286669851832485174569209006995893721241065768141070640205570937294547459809358579150812987665818402435744199237449881608688990292523549349834279611455341520718806486202358248536382914730152469081850909296860579870838948236765671714026412924966419911205459179775210518768719595452728762432227174492387879708668662948527169970040859212205620053099128821452772510612023710144104743601994746850770405248738624984977894352241991805799633434687487908396135390462559296438040897491136156017880735305969967464724717697457748530863024301080504339567345937349182547693021850805784652393154644220205928869776779624123385567094378891296353367624994207532556244843492396936602848970619149299683484789744936245236503073649584679845350384403920692051513805145294814651393590292390562730328077399901692602649770469295982057393953731308907178353309958943065457137309169707664903885209082555525937539336192011547616539109308447555685339488505567248706409412482520948067640132410498257903397930726126120294226372349881911694075475092529117045100226908646687953348931885643545698158829488018676793126440279215317333876958407101502846775730433916955900764748809484844403602387854312727204384312633725107998124337110317143861930 := by
  rw [PackedColumns.col]
  simp only [show 0 < 12 by decide, ↓reduceIte]
  simp only [col_12_0]
  decide
lemma col_13_1 : PackedColumns.col 13 1 = 872598508495532743570387395787026289958611329596986153945466228951777065479295436173011387620161589779165833436925620218487896656141747250888783812062043839263125039073754391630887860182438564127757481290873310557417509234087459648097032443121509040814320202028639933760008063680021228669440724238244704761880401304156380523128804249891648011877940828234840996675143135002214957023475270444494012555479956325342260112651920492884736205150803662410661194852668837793925905954249796105214206015331919381092594977945821894460022102306436165201434209360756559334797806303747081389639997520768896412524040092449017193194012273684599173303637626229057204584662744177331976259516910908201301127612934404342098748797047137353156944949925116248532323908591547866301942533925996296794809495005087976312093617458893399566896775885605010889666165372326525653260109824821617848742051928221407328416702643705928839491655003936773858385967347810741907032217958750414821582211952858172489264347752661967471993569131394193128479293940848445187011005051622089090126902706694896926394910416702830140436269431932555387547164533052056069770828376204536249603304580396667606685951723063148861664782840463130374325882224043948497248872636676138363292778341983902022190848006563294847144003822198982209483050808395072465489278921769284768246685124753456951771230294980975585198982082922893039084939857930426788351028259219801135533746409824862567783442829898243659497676182962898221091156232695845006737884118806056831695509959703893446551015730252622522463514543274514918672609390865455650402395538232603964049031054646744063718954585743327012734428452172925692322393696220924486298486349981973473222690390166959560121624985490075362468555071155725649076989363387221456882367163960957669661236949298237035629161296605207480815124819019057231626220966941582871785573064247114643732135548948062680513254669555624041149993049039067493812190876323923418764742979159620181747693923494283803688379501615814420461284704830461816566174353777581672308350868675276393692879882031123179724563155178468872744477570688614023971950731678548564771003649197884662250899066631125047203430413857139846931170137066822407386206680698447691294979025137681168158892597909484077516871351344353071646819858294032890570111034940454120272290376025544018718262772254837790595385622412151751728335058380800652350088521803416130876520700347080917698571381813284322865425175272645261175160470129597749204532380572634316 := by
  rw [PackedColumns.col]
  simp only [show 1 < 12 by decide, ↓reduceIte]
  simp only [col_12_1]
  decide
lemma col_13_2 : PackedColumns.col 13 2 = 1026586480582979698318102818572972105833660387761160181112313210531502429975641689615307514847248929151959804043441906139397525477813820295163275073014169222662500045969122813683397482567574781326773507401027424185197069687161717233055332286025304753899200237680752863247068310211789680787577322633229064425741648593125153556622122646931350602209342150864518819617815452943782302380559141699404720653505830970990894250178729991629101417824474896953719052767845691522265771710882113064957889429802258095403052915230378699364731885066395488472275540424419481570350360357349507517223526495022231073557694226410608462581190910217175498004279560269479064217250287267449383834725777539060354267779922828637763233878878985121361111705794254410038028127754762195649344157559995643288011170594221148602463079363403999490466795159535306929019018085090030180306011558613668057343590503789890974607885463183445693519594122278557480454079232718519890626138775000488025390837591597849987369820885484667614110081331051991915857992871586406102365888296025987164855179654935172854582247549062153106395611096391241632408428862414183611495092207299454411298005388701961890218766733015469249017391577015447499206920263581115879116320749030751015638562755275178849636291772427405702522357437881155540568295068700085253516798731493276197937276617357008178554388582330559511998802450497521222452870421094619751001209716729177806510289893911603020921697446939110187644324921132821436577830861995111772632804845654184507877070540828109937118842035591320614662958286205311669026599283371124294591053574391298781234154181937345957316417159698031779687562884909324343908698466142264101527630999978792321438459282549364188378382335870676897021829495477324293031752192220260537508667251718773729013219940350867100740189760712008800958970375316537919560259961107744555041850663820134874978982998762426682956770199477204754294109469457726463308459854498733433840874093128964919703169321757980945515740590136252259366217299800543313607263945620684320362765727853266345521035155330733152617133123739375144405267730221898851731706743151233605612945469644570190883410666624852996709918133949576290507258984784496949866125506704056107405857676632566080186932468128804797078672178052180084290376303875332812435424746988769553261518089441816492609720908535103283053394849896649119680394186330353708647162966827548389266494941584801079645378096250922732782853147379582660206071141328938528475920447732510960 := by
  rw [PackedColumns.col]
  simp only [show 2 < 12 by decide, ↓reduceIte]
  simp only [col_12_2]
  decide
lemma col_13_3 : PackedColumns.col 13 3 = 1086503979449690575651844228217308999170255352027375755885405421262913077639589648153165930110707037857327107781385986264265085330604510195659186069493595441884046741259149437050132744196032453388647447521709958670714408384855980884790079306610439272609270290463676182113628717422594525969731641074857219936971705904007944620238199844223063672377202587685405132046870829574742358939735745300537291897873875580192697416531574154564652084234463704168916662851572093751191789515019201376142202042436631135990779739076509751856836858902955536437583451344132680883794933919062513792547856835198625883298415679313951368957525010035298581545385371180149048510085907146872499622744791792312904127767077857546582099669475034836615651299517654472880714594355234697340940120063497334530502094947969464668754698781501509188353962192193009668066820697060265404837490832462714831118508237474125856394337922124113730106340860932947994877469071204036615759960104280672151386411770095778974959499147283383622715728101346855257250482727904678832075959597350461123893419712616214071775763942976286556185238203184504762704640663722404444850836888659344746587772240182621144511690861401586131255760735207010582818219111650052603578362816094802631337311554221200961482767945915386580101483358380055669395238360647561046523615778078486870968635174790296593645111651338179716979277301693874601195255854232438024405949583464343826345520821571813313971601967188474595483487854272869380346964958998717518117209797735168039465226408969828415939007913155016370382586201742586669164338541155431160034111176009467970800349951311121013190916215711535580058432313989635103280801489457960449865819579744091484168330446900494393925758736796980996069796197547985243986912826007435277051974678861892818255236668386909927631640524955900365217276039245518731985956067787184898721336111124812007759857492853618901806387137189882074583648932655648241322572297368309315193454293117036802176116947541520689417437511739535465165801967104076970043485576688039436337246217805791618605920475680775943625915212673579919370555730040297617396981455786519613722650458145226038600341250280000058774699347993325879447371376892541518924459680247094401612425245307618575139477164712198073172758102841217832400709551183231614717647981248814468821528872872272708131689054947657949379468479268048873747343263353526104093495435708533703815123051015820597912618062958175032361618895281114722085802920005724823912258217055420160 := by
  rw [PackedColumns.col]
  simp only [show 3 < 12 by decide, ↓reduceIte]
  simp only [col_12_3]
  decide
lemma col_13_4 : PackedColumns.col 13 4 = 1090731492377649913076371140926090508772288022347454197342151662049370236722216185228086315727659756087542381786669313644178532646766436284737006116912929052480815466086667985449476379848717017461066159075763944044793663983039270860309579287128095894281232142914478590317223256735391291218709799496421963380887780564207862618897899570488789617056638427895664654281211004766489910727727759201869928567754368100035673717570919126251088544271996521425780323822125382487425579684333175106262840178463933895343170737038950968066359623128053628535048757661064396306004795648304940834022134014394738759997701517820826227420441665932867910905808846005834356158743488457009559411929525941069176013153662608964473953666693646214666782585377199491581365863433169067968554135514558442306342887694230846994624550135534847376599232197823557564146242081587332064559992017476950946319619359444248109371748486692855799489698611814707943283617576829210629477688865539069261394552743917809639143313973756326583543848257378462564429616241730696091062171503561065325895232765192882741203763695870971284992282098111218660418751522767664574753593551408755505554155839084715661988085587581566973581015461353733620165345862546046674315694133031863752093388494672036462729057916866275750767303860636596466131368879010701380485553645594699302909325196756079672385052501103827150151831976334641466070132492510498840375913377104324412513915893203117957074929225098251683568818116610778983960015236926371712955543693067918514007296273844438273669212942647585898655890739354078797284894964671836167065386613546773833634383996775276160029552156249040219772103984039642838626279683147201335391793975777396995993145807139132507822505131625600404251400452096938297028960261358945050090842090295278274847010557189245433247492155849346122470894688100480162577170477926277810346432479715635924966607323646570559953092490196327592825540237991980241590165503279915261077067074366481305045563364399525904422723786141683588265993912136830065659108641858179205570900455649154556530215297251775499077409916111817294890330692445660632067110242139656963639480277435505310459643431014873489279414979373131151267245336657370517617194123667803452567018352064922735181294255470115135422465189162296162920296668926670039756221615001022346654653517921366037709997197050769974298091004898049521668450005074312059455258124511891747278706315095791213785601531930729995714415221299954221210448230969019753953267507156418560 := by
  rw [PackedColumns.col]
  simp only [show 4 < 12 by decide, ↓reduceIte]
  simp only [col_12_4]
  decide
lemma col_13_5 : PackedColumns.col 13 5 = 1090748135365456339041586926824709096400964067164273332347272707540109023476350483456643682700482416018057609895981362120404606980048375087448667425214590816869671144547395038055582970986878455636444962424714107236239490619974692554770930709212877821728916669614260327992795699918566977659395175021578144334544566109855586642133164142480791907459073081590624358274300179425040837504737754591061664838562273108983506886107634298866042884653729319819199997516446804694739144110610717674156946529148702714412442293984696868969709907445224692898230111221050144866923794893547112852427041007695329043678419482870554145720540889865230465166845682064128327460786411382323751884924288490359559578197608978570342104424944587739380487102228316436132266546300897104300298367464939913764498334082754312722554117819014494666733843304428703937824198941703283915032685136815704633686814941668193778404358975865825028806933982931557049500470592340750507523610764520132237088741246609468819349337613959440828784317324935031505062497594936585663442849809668662650964255879591527000676094851237579633838846544771148541303921518249715058663926914944350215064247014897203907073996515109866185678977480329325325801747949437443546148220516763024497923624659148936397529559134468581007943125037851605844897637030937792984208879998260560834990466014491803030020045397864796326702999835042686266982263606726267146269373602788359121917286258255297088099245591502185867918926029084430605200919372173516522535733737890028181875115540306551779084866614357067231533631720626002919587235295062368071686593937750462360071885117835669805146321374038164582655652795571977548739307436252124465110216812285016292939828102403759493188093620266844902118992158588255074301105296020131705096904108125908453231286645621791511653515435611337191921902927077389109450451989403004404527133421488734171726166453908082112971477795474787089400560567367842496129965928562701168456383421601224547224975507428722506692020725843928961435818309035149891715365798426895257374225068707636935783558936310339766210019945402769632483047091147946123851035813219440350036499475353738431721176746185131364175201392263406813394131677632259165477572009757420066823456072165146952257899881163435108097311824032068432359543340248227743649736365547338111070004318372011931585654645314294836757658558013694582114506887325604913720922722968365137005114262182509113579006044876988892546771973980841489093151046977170736321405274931855360 := by
  rw [PackedColumns.col]
  simp only [show 5 < 12 by decide, ↓reduceIte]
  simp only [col_12_5]
  decide
lemma col_13_6 : PackedColumns.col 13 6 = 1090748135619415929403854669820128643835281822143174671095392721590677921920417072578689030872885679376536174029528239896742254073353278082923030058229357091300030393146888777261730166167240147960083923101996823490514355455651568890737193309875090994887952495597058554419219395583801974058669822774425700320602000555580027419219660782965643544761919466940595449891933698401109894205870007440326040697196084961016514337994471542752611988248099510093894277317118938299181052534179992180611763502713740568706813166286568129787497207891105101070642977075903571570054027644364590446601280785149886722456526311428692503745869033851011170379573239871025633307907777362710306567563441148121858767949811499260469124776695938902641931594003381934561985005343743685083799012958615340497526215585095341939983925335426324943931358772634914039415810241181336029872642177025788124259913276625707191883433362498148979089190612769477364849156296598604956531440099537350932558545961732221916191503815951153776287037593938459242959091504280127175810734425619861520616741230751469122342495262459811324635237600645624320878844480106463393239977750409859338365102275402708239345773880027238141707183621557733481314949378274404868584905321709416744565607290993339377141986944120719563564133545054356921532678282631495561640293652704448981407979637281048067370092943735415862513219631905132205243835345916182893926006276981822640099165954635101713781042208879607159383576070856276803186793994557281304652875534793746532044826511343908913238927973380729497620328575369613527557267407888667221403469768087071709689761333129469855333306317190610121128804688744301302209854694241778786633133327396692416385648538584937903813623713078893779055091594531543783419179722909182516033055000345688034320365228169710990474860995658072338681123651241223172931351929918827568679587283744611196323840052692029991663662335786495300388236002058368899453352397682826240056654577137531924806502740465564271415492629087478374350216697724571799736835532009208639156739698175298800515035510452484116660223014932861307476880632787267150057929595142785268236485943223275300709970934124908318484485834183562070916059435823162768771276983699787719886834170973112315811783258262042268793707899620037982010519892205757909218844019984162560417654567467164875084760799557738260877398316200197677337735993893876640054030862480179650557345729971470059927578032767319931222828570259113571184368826210270342110464355294248960 := by
  rw [PackedColumns.col]
  simp only [show 6 < 12 by decide, ↓reduceIte]
  simp only [col_12_6]
  decide
lemma col_13_7 : PackedColumns.col 13 7 = 1090748135619415929462984244733782862445058741317256278077723357411872937927833784244419600432340383621359132078539296421583922726078535288895631126147893430149380770045156693316471592314481596094990093519266467060963746463149021913517350803079950400440665964304739215704920738623747423257015752366908264085893021118110308974552597077954159980749712419298225792610335570650809591039390908475045801933904902676564396390725443722970902476505668943463129909442136980589661502329916207474552401367763852856835262959009067319505910523234201508849530123021140590765937850147753368424740552323470408182285922748805210520738945273624250073532547213864411288330003393740150912580166278929704842831018825970092592589997564992748701241134099098189591461277259179911627931227354401824729735222739283906940258565844609867958833251463899830750255317198113101160530620734317932567900498223532817667589142046943165554232191512001478956898687683520250475974324734315380150309747612208712500051022967476984319077129296386777374636865231087169447708549517544139233017684215770290488418789440168334816327372623519038609022141979462139722689427219151234633118646875003741836690327166568052540560892638150017862105394046379266526690121410209850772135746339395758587591648792223654974745634225736271050568271311740257450712934213663479668020824855253157533409992242243185229562856090869187134982573538569852483225539869705077626849803583477586364785204481055628574836838979480433938208897652545831398860133527896735028968302348255129557764568722621963320682441686446392311846397899383114863434253848663932279264188564128386706056453584844520974679854641137384660894775927042925383218566634937141648684602149056050732108371054310349389279475071554719181040574555552962971974792722792653974763290140871652286270098969576677480222940290795746088405409748159994478121367758864292622252744789474675449474741606852764070764063110576030660846709793102667506631035454077016208694602827335899556351637399344567778304083178028820294133459605355876156179714463545661793044235280409193608501261558804583167350441282704397497970403108257267112393653696672675910688099839367469282734578305725116229359673050529813789252273363198230132949795533051518858815503461348243733779388689730783814640911372667854894579549420746122021822981211980082448791461461735149685581518666731366228054655612843460369296145991464644624232666058546546775071466057342070960016482455402459983974533531512623447503628532879196160 := by
  rw [PackedColumns.col]
  simp only [show 7 < 12 by decide, ↓reduceIte]
  simp only [col_12_7]
  decide
lemma col_13_8 : PackedColumns.col 13 8 = 1090748135619415929462984244733782862448264161996232692431832786189721331849109875331513870234605433463932241694048131051358947830205980188196448074959461356758486573232462591433156779577237490627406123547618423722668866652339479999293626021839890161927470072222416275310966999593803517697609822714708579884205550840414698745794222115405131762724689518277473450666725768294443700706103254859716733899036477127355717020008787842924414391583891235738543020558099725138939596081148014590965124539186821561529914566658849262988504621375111628343614858679068075902419555944729073976404444565343555827377610000620947577410278627011740831480055497987845581365988527549373552036103980380460119398337457819050480022405702325635582620236066168807184261870584892432597683277669260204163001806232850994074559052885958077900805983585439963419680319621217850405971289333030803245070840561728370555174569443676693629170452149296065798196661572238035681751946495873207469100150493032277188951439284275065790528306049503847529562489086229780168252138484384622224460015690956455991882709903488025930330456108229822033526376707136090265975193250434767826227728688689631822571110448349847083887734391639427413322727296020796085661840741564416933944834885347677704020625164362236290082483231096646670146316488035415210816619742524561606952935611302947966659440338951555748352481673455328318110092907812432976349828140055049776760942184789064042974347999533186945347522493599199813729152746600124370793863684351800627532861582603373243844541669894180917405990955855670211102417040532303109059148651080538307108200472206951864724440163912445823502524921620535906589683568560322180265439851314707032130422408981737587067461745778054108010454979688805716669890106223718629918609636282362876953861912714996254991032203811132391157099002202347885731138448079694323323449229027719621743895573011766662593894349081522104383894908548239240269319053774558041228754281281816861897527545504098214377454609550129806936928314745701910920161391616609369496032529549582045082542643910019366151847658440920119593061651167368561688293227455295170854030179178723762426736301386023622466277453636011514339531108046811378554467570571147700293987047007133169604516470460363030434395212791168390261169656611459540138630944243057585634982081359365277395087425491626723439059966600654655183801562224994052115182662706659658702893140791266483454391692605083442515414863001025232435847470731267136086799620306370560 := by
  rw [PackedColumns.col]
  simp only [show 8 < 12 by decide, ↓reduceIte]
  simp only [col_12_8]
  decide
lemma col_13_9 : PackedColumns.col 13 9 = 1090748135619415929462984244733782862448264161996232692431832786189721331849119295216264234525201987223957291796157025273109870820177184063610979765077554717727193825132424258268072070423477350441019325238935081369672808088954075376607323183064685826513719267367765025669297838401423262150842341357600244555889201894556085847866483922724148646867108659100934137092282466892797007055681424336981376513709740535026193493673249209257320971410979203369564857482654510028075971351626483674957465557609650341383284243352703413714646767970869719760282612297099758526022496503350912508240831354915423886988443810272342344732317150627439462977141579914873924393499344568782246440509166066283446893682365040319921619212785451204784909812620149202475072920645750021639932387054565814599265491865025466591172979897528545547657398713095194110513475640015533832552892834462456004562452971528736770337713855531343214788202807563614479213467081621550379582167079624431075961285990652132534019881887236124261807921871717536754538527881569172145267614894322853623609813920928459120198997814593256579843388566344082288016681611654470716138650900737275301237931416801181903989453821932064570156865659395968836640923032250896569702084633936822519618352768176774084397451792927718879958100081887861393908320621408161687515022883010853676704976685223953947630891854814753738450680771222651381548932686869654811143303224385700414066978115266169823947267240120243654344301634559922544942816043553794364709175132165894258852632905428043741747989065584385717223677332433400389608789558933209058517367950612903452919800029473576992005403338790727107551494317528931418468321870206715879080915763252955490226179218331260318126443739420462473525613282748278965996483750636045783491802222016697761633212650864259383149056931239290285624805626122759894380826805436467577805724137767574570906567601847329444596436887515074101490955904440736746378578909097694701009073306364306371857928229086986807866811037349498795349771504573858928341772320617473445645992985275412333509090804871751065163475735116124159825908647121640421907667647356208564338125924147715960797202874727558317522397417637853954101630500329587808124225607721416501990667502342789749660037118355919877562034711995165307625661050344070739613757088494470672876611099532221420366583803436275263239830405586791170387133117796852392016463145034898659808641129024904249424733643211466577601264042611135606503976088487910839773519358050959360 := by
  rw [PackedColumns.col]
  simp only [show 9 < 12 by decide, ↓reduceIte]
  simp only [col_12_9]
  decide
lemma col_13_10 : PackedColumns.col 13 10 = 1090748135619415929462984244733782862448264161996232692431832786189721331849119295216264234525201987223957291796157025273109870820177184063610979765077554799078906298842192989538609825228048205159696851613591638196771886542609324560121290553901886301017900252535799917200010079600026535836800905297805880952344434142288520078948840015587307354938660586662128298270350249817014271693665765110592008613298778505422237692146259873858659415573867216038413367887863225808775353059030740090896360912642226573857037049962736349533220384817969976483149973107413139227644176078619320341055567499174066505299371568329139777241183089138566334553194650577629094056611619967969653726624148744303488035402293152604489486492100208017863024726771025350917773611238726097375366394777344426511988513556879991178832915713510549481697173215445101845957529458649240419039109240935740910191672068265273719092589036748465496772589128171977093240953165534992672018013618814995161462309538660641385783569275376409313809965475889555022982121273477969648053452876833585167683334003690463172464081216829623878909681066796095037273252169666759578152053991219528513242729480885311699333643283995611022633415058770494955457423321606395672379513094283755488117583208734138564299317466532948220527445976808475956204587074983904100207162912865380688486391072610835612762060729181212793646168221753156439697858063620473480211440842709029593612453629476963272918555621144668718781463666529288238422362202825387580631554852164914519052059660040464663126781487560119934326441860936571324105415002310162950779332518014848112844743427605942506544050522057943770995582957029023526909557365112077631459260712531564908022807631888258826691914906113986248716550085419858013381711311649991056871703624067763554136461504317273126870747233315465647396625310067987550217403326963292546153158772672740041967708838522805761174003091611777775043411335156923698959839678510230832295163313316789267444620224432518792403169045198033711681799380593647401842461843648423716417664365528718045683794601856283379413891052412969460121927658025990683597601528175797008376299141662638078090891860989403913605461823884961828737140171022361679405979038786444181270716007518309822554612689912150227475032388745809549109277022071797772295031123798251651255599727407916691739326020171853970956314931166813991316312725113081108713697206841284865031993483234062808071776305097470274820616405375977422257119466656882704639478857686056960 := by
  rw [PackedColumns.col]
  simp only [show 10 < 12 by decide, ↓reduceIte]
  simp only [col_12_10]
  decide
lemma col_13_11 : PackedColumns.col 13 11 = 1090748135619415929462984244733782862448264161996232692431832786189721331849119295216264234525201987223957291796157025273109870820177184063610979765077554799078906298842192989538609825228048205159696851613591638196771886542609324560121290553901886301017900252535799917200010079600026535836800905297805880952350501630195475653911005312364560014847426035293551245843928918752768696279344088055617515694349945406677825140814900616105920256438504578013326493565836047242407382442812245131517757519164899226365743722432277368075027627883045206501792761700945699168497257879683851737049996900961120515655050115561271491492481590583927528068362121611832823090350947768974356780606151520143159909137700592185973126172549006476832634892320043175548198813118732027663641737580234180498216659031323755528672469578345747574178638520542422428423677558820978627530386229456967934723788568179648262880758976714398711940255399001607683329891312982140614519561421728861174053416163557141099001227260702498594974247602767107850237371185829184296776123032637607387534110972932388406207584762847633426555552446542114214004891266591088458003495784055858294944168684601688858744297754455478086944868426545830699462053020840665064540392958400443325645527374926882973919246656771539390355706463348469275233864897316857752844929570354333768590343841311070850781091725431885844774325016901949773780261558722409401181833978850211680880235006737620395003207721429913359698783128999341087064869360477360260946612352621282830392338045342868360685801099549739965616135919539306625022788065057280252729962269737132309764754628744321772059641657719823547449320592935611616099240742902136329711517410404030324521840342033994485065200736874265167184988389293259882587602113424959054628993094268364393026247954669688793470940786540624498332650203138482502473546445070830271563685172304095213304349600298515635788989580172037008658825732196098316200861698353829406714272630544531590748563008319858775677970324879375646607814716537093794936528532510075217655406621358266156154358999433998158724863016801311862884415003624026624271858216959376261551815071325789099581359312420237157949795754513740566131017746235944565634476856040075065074597078314422621893894702231993235077806982696786165968173125570545073461288474360408005636640266535246648614607443110206856314723120840607763815821602035459921424929857198102394553285216706183381968298312489240849692137274288006245419386744015437915115941622091612160 := by
  rw [PackedColumns.col]
  simp only [show 11 < 12 by decide, ↓reduceIte]
  simp only [col_12_11]
  decide
lemma col_13_12 : PackedColumns.col 13 12 = 1090748135619415929462984244733782862448264161996232692431832786189721331849119295216264234525201987223957291796157025273109870820177184063610979765077554799078906298842192989538609825228048205159696851613591638196771886542609324560121290553901886301017900252535799917200010079600026535836800905297805880952350501630195475653911005312364560014847426035293551245843928918752768696279344088055617515694349945406677825140814900616105920256438504578013326493565836047242407382442812245131517757519164899226365743722432277368075027627883045206501792761700945699168497257879683851737049996900961120515655050115561271491492515342105748966629547032786321505730828430221664970324396138635251626409516168005427623435996308921691446181187406395310665404885739434832877428167407495370993511868756359970390117021823616749458620969857006263612082706715408157066575137281027022310927564910276759160520878304632411049364568754920967322982459184763427383790272448438018526977764941072715611580434690827459339991961414242741410599117426060556483763756314527611362658628383368621157993638020878537675545336789915694234433955666315070087213535470255670312004130725495834508357439653828936077080978550578912967907352780054935621561090795845172954115972926435488646325407501512365848213380395168763512806429730109607098577644744240048503459529594006823631373147762011780218660740030215430505248911586325182120160839367048207709418842650690943826010989109302792718425868852384783378651199618535121913835737651699662333815683378345818068070160548347800369481364172406204671458973952634913932812733482191175501628465349005403383205634207163186366050321349674463279843106828789837369958673440743379029655723491233599261110682223445532527992025505094106028374148434683256837486589543018181873279720349434704460879700399438016504650780473547823239120431423814382915239771713285086798751923825359346515261480728322427217167293613096521198247560588729708788376007087530154941809492620352947595475014394229254625965054086766970439573627357949092810593883736061141168581582787315634913260797956280083967967201275577888581524322407185240031043931510925713450658807511908275263101371880394716465807521940885628037330976885109586390268456528362201664202524947917653322271271470730573883899274644538470640093205628124760082118516398285556726512915645798229781241791101398278815512033744564071010914628794915292515492524789530849844709747037539932187090270337487885794730917151571753381797325072561602560 := by
  rw [PackedColumns.col]
  simp only [Nat.lt_irrefl, ↓reduceIte]
  rw [power_12]
  decide
end Q3PackedColumnCache
namespace PackedLineArithmetic
open PackedLineColumns
lemma complement_bit {k a b : Nat} (h : a + b + 1 = 2 ^ k) (r : Nat) :
    a.testBit r = (decide (r < k) && !b.testBit r) := by
  have ha : a = 2 ^ k - (b + 1) := by omega
  rw [ha]
  exact Nat.testBit_two_pow_sub_succ (by omega) r
lemma line_bits {n m : Nat} (I : Fin n → Fin m → Prop) [DecidableRel I]
    (cols : Fin n → Nat) (r : Fin (2 ^ n)) (l : Fin m) (a : Nat)
    (hcomp : a + joinWords (List.ofFn (fun p => if I p l then cols p else 0)) + 1 =
      2 ^ (2 ^ n))
    (hc : ∀ p : Fin n, (cols p).testBit r.val = r.val.testBit p.val) :
    a.testBit r.val = decide (∀ p : Fin n, I p l → r.val.testBit p.val = false) := by
  rw [complement_bit hcomp]
  have hnot (b : Bool) : (!b) = true ↔ b = false := by cases b <;> decide
  apply Bool.eq_iff_iff.mpr
  simp only [r.isLt, decide_true, Bool.true_and, joinWords_bit, hnot,
    decide_eq_true_eq, List.any_eq_false, List.forall_mem_ofFn_iff]
  constructor
  · intro h p hp
    simpa [hp, hc] using h p
  · intro h p
    by_cases hp : I p l
    · simp [hp, hc, h p hp]
    · simp [hp]
end PackedLineArithmetic

namespace ChunkedBoundary

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.Outside.L_meta_2583.ReducedCheck
open PEqualNP.Outside.L_meta_2583.CircuitCheckWrapper

def lowCode {a b : ℕ} (P : Finset (Fin (a + b))) : Fin (2 ^ a) :=
  PackedInputCode.code (fun p : Fin a => decide (Fin.castAdd b p ∈ P))

def highCode {a b : ℕ} (P : Finset (Fin (a + b))) : Fin (2 ^ b) :=
  PackedInputCode.code (fun p : Fin b => decide (Fin.natAdd a p ∈ P))

lemma input_bits {a b m : ℕ} (I : Fin (a + b) → Fin m → Prop) [DecidableRel I]
    (w : Fin (2 ^ b) → List ℕ) (hlen : ∀ h, (w h).length = a + b + m)
    (hlow : ∀ (h : Fin (2 ^ b)) (r : Fin (2 ^ a)) (p : Fin a),
      ((w h).getD p.val 0).testBit r.val = r.val.testBit p.val)
    (hhigh : ∀ (h : Fin (2 ^ b)) (r : Fin (2 ^ a)) (p : Fin b),
      ((w h).getD (a + p.val) 0).testBit r.val = h.val.testBit p.val)
    (hline : ∀ (h : Fin (2 ^ b)) (r : Fin (2 ^ a)) (l : Fin m),
      ((w h).getD (a + b + l.val) 0).testBit r.val = decide
        ((∀ p : Fin a, I (Fin.castAdd b p) l → r.val.testBit p.val = false) ∧
          (∀ p : Fin b, I (Fin.natAdd a p) l → h.val.testBit p.val = false)))
    (P : Finset (Fin (a + b))) :
    (w (highCode P)).map (fun v => v.testBit (lowCode P).val) =
      List.ofFn (liftInput (independentInput I P)) := by
  let high := highCode P
  let low := lowCode P
  have hwire : ∀ i : Fin (a + b + m), ((w high).getD i.val 0).testBit low.val =
      liftInput (independentInput I P) i := by
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro p
      refine Fin.addCases ?_ ?_ p
      · intro p
        simpa [low, lowCode, liftInput, independentInput] using
          (hlow high low p).trans
            (PackedInputCode.code_bit (fun p : Fin a => decide (Fin.castAdd b p ∈ P)) p)
      · intro p
        simpa [high, highCode, liftInput, independentInput] using
          (hhigh high low p).trans
            (PackedInputCode.code_bit (fun p : Fin b => decide (Fin.natAdd a p ∈ P)) p)
    · intro l
      have hwline : ((w high).getD (a + b + l.val) 0).testBit low.val =
          decide (l ∈ avoidingRight I P) := by
        rw [hline high low l]
        congr 1
        apply propext
        rw [mem_avoidingRight]
        constructor
        · intro h p
          refine Fin.addCases ?_ ?_ p
          · intro p hp hI
            have hf := h.1 p hI
            simp [low, lowCode, PackedInputCode.code_bit, hp] at hf
          · intro p hp hI
            have hf := h.2 p hI
            simp [high, highCode, PackedInputCode.code_bit, hp] at hf
        · intro h
          constructor
          · intro p hI
            have hp : Fin.castAdd b p ∉ P := fun hp => h _ hp hI
            simp [low, lowCode, PackedInputCode.code_bit, hp]
          · intro p hI
            have hp : Fin.natAdd a p ∉ P := fun hp => h _ hp hI
            simp [high, highCode, PackedInputCode.code_bit, hp]
      simpa [liftInput, independentInput] using hwline
  apply List.ext_getElem
  · simpa using hlen high
  · intro i hi hj
    have hwi : i < (w high).length := by simpa using hi
    have hib : i < a + b + m := by simpa [hlen high] using hwi
    simpa [List.getD_eq_getElem?_getD, hwi] using hwire ⟨i, hib⟩

lemma independent_false_of_chunks {a b m : ℕ} (I : Fin (a + b) → Fin m → Prop)
    [DecidableRel I] (C : Circuit) (hAO : IsAO2 (a + b + m) C)
    (w : Fin (2 ^ b) → List ℕ) (hlen : ∀ h, (w h).length = a + b + m)
    (hlow : ∀ (h : Fin (2 ^ b)) (r : Fin (2 ^ a)) (p : Fin a),
      ((w h).getD p.val 0).testBit r.val = r.val.testBit p.val)
    (hhigh : ∀ (h : Fin (2 ^ b)) (r : Fin (2 ^ a)) (p : Fin b),
      ((w h).getD (a + p.val) 0).testBit r.val = h.val.testBit p.val)
    (hline : ∀ (h : Fin (2 ^ b)) (r : Fin (2 ^ a)) (l : Fin m),
      ((w h).getD (a + b + l.val) 0).testBit r.val = decide
        ((∀ p : Fin a, I (Fin.castAdd b p) l → r.val.testBit p.val = false) ∧
          (∀ p : Fin b, I (Fin.natAdd a p) l → h.val.testBit p.val = false)))
    (hzero : ∀ h, PackedEval.eval C (w h) = 0) :
    ∀ P : Finset (Fin (a + b)),
      circuitFun (a + b + m) C (liftInput (independentInput I P)) = false := by
  intro P
  have h := PackedEval.eval_testBit_of_isAO2 (a + b + m) C (w (highCode P))
    (lowCode P).val hAO
  rw [hzero, input_bits I w hlen hlow hhigh hline P] at h
  simpa [circuitFun] using h.symm

end ChunkedBoundary

namespace Q4BackendBench
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity
open ReducedCheck CircuitCheckWrapper
open PEqualNP.Outside.L_meta_2583

def canonicalC : Circuit := ⟨[
  { op := GateOp.or, inputs := [1, 5] },
  { op := GateOp.or, inputs := [42, 9] },
  { op := GateOp.or, inputs := [43, 13] },
  { op := GateOp.or, inputs := [44, 17] },
  { op := GateOp.and, inputs := [45, 21] },
  { op := GateOp.or, inputs := [0, 5] },
  { op := GateOp.or, inputs := [47, 6] },
  { op := GateOp.or, inputs := [48, 7] },
  { op := GateOp.or, inputs := [49, 8] },
  { op := GateOp.and, inputs := [50, 22] },
  { op := GateOp.or, inputs := [2, 5] },
  { op := GateOp.or, inputs := [52, 10] },
  { op := GateOp.or, inputs := [53, 15] },
  { op := GateOp.or, inputs := [54, 20] },
  { op := GateOp.and, inputs := [55, 23] },
  { op := GateOp.or, inputs := [4, 5] },
  { op := GateOp.or, inputs := [57, 12] },
  { op := GateOp.or, inputs := [58, 14] },
  { op := GateOp.or, inputs := [59, 19] },
  { op := GateOp.and, inputs := [60, 24] },
  { op := GateOp.or, inputs := [3, 5] },
  { op := GateOp.or, inputs := [62, 11] },
  { op := GateOp.or, inputs := [63, 16] },
  { op := GateOp.or, inputs := [64, 18] },
  { op := GateOp.and, inputs := [65, 25] },
  { op := GateOp.or, inputs := [0, 1] },
  { op := GateOp.or, inputs := [67, 2] },
  { op := GateOp.or, inputs := [68, 3] },
  { op := GateOp.or, inputs := [69, 4] },
  { op := GateOp.and, inputs := [70, 26] },
  { op := GateOp.or, inputs := [1, 6] },
  { op := GateOp.or, inputs := [72, 10] },
  { op := GateOp.or, inputs := [73, 14] },
  { op := GateOp.or, inputs := [74, 18] },
  { op := GateOp.and, inputs := [75, 27] },
  { op := GateOp.or, inputs := [1, 8] },
  { op := GateOp.or, inputs := [77, 12] },
  { op := GateOp.or, inputs := [78, 16] },
  { op := GateOp.or, inputs := [79, 20] },
  { op := GateOp.and, inputs := [80, 28] },
  { op := GateOp.or, inputs := [1, 7] },
  { op := GateOp.or, inputs := [82, 11] },
  { op := GateOp.or, inputs := [83, 15] },
  { op := GateOp.or, inputs := [84, 19] },
  { op := GateOp.and, inputs := [85, 29] },
  { op := GateOp.or, inputs := [0, 9] },
  { op := GateOp.or, inputs := [87, 10] },
  { op := GateOp.or, inputs := [88, 11] },
  { op := GateOp.or, inputs := [89, 12] },
  { op := GateOp.and, inputs := [90, 30] },
  { op := GateOp.or, inputs := [2, 6] },
  { op := GateOp.or, inputs := [92, 9] },
  { op := GateOp.or, inputs := [93, 16] },
  { op := GateOp.or, inputs := [94, 19] },
  { op := GateOp.and, inputs := [95, 31] },
  { op := GateOp.or, inputs := [4, 8] },
  { op := GateOp.or, inputs := [97, 9] },
  { op := GateOp.or, inputs := [98, 15] },
  { op := GateOp.or, inputs := [99, 18] },
  { op := GateOp.and, inputs := [100, 32] },
  { op := GateOp.or, inputs := [3, 7] },
  { op := GateOp.or, inputs := [102, 9] },
  { op := GateOp.or, inputs := [103, 14] },
  { op := GateOp.or, inputs := [104, 20] },
  { op := GateOp.and, inputs := [105, 33] },
  { op := GateOp.or, inputs := [0, 17] },
  { op := GateOp.or, inputs := [107, 18] },
  { op := GateOp.or, inputs := [108, 19] },
  { op := GateOp.or, inputs := [109, 20] },
  { op := GateOp.and, inputs := [110, 34] },
  { op := GateOp.or, inputs := [3, 6] },
  { op := GateOp.or, inputs := [112, 12] },
  { op := GateOp.or, inputs := [113, 15] },
  { op := GateOp.or, inputs := [114, 17] },
  { op := GateOp.and, inputs := [115, 35] },
  { op := GateOp.or, inputs := [2, 8] },
  { op := GateOp.or, inputs := [117, 11] },
  { op := GateOp.or, inputs := [118, 14] },
  { op := GateOp.or, inputs := [119, 17] },
  { op := GateOp.and, inputs := [120, 36] },
  { op := GateOp.or, inputs := [4, 7] },
  { op := GateOp.or, inputs := [122, 10] },
  { op := GateOp.or, inputs := [123, 16] },
  { op := GateOp.or, inputs := [124, 17] },
  { op := GateOp.and, inputs := [125, 37] },
  { op := GateOp.or, inputs := [0, 13] },
  { op := GateOp.or, inputs := [127, 14] },
  { op := GateOp.or, inputs := [128, 15] },
  { op := GateOp.or, inputs := [129, 16] },
  { op := GateOp.and, inputs := [130, 38] },
  { op := GateOp.or, inputs := [4, 6] },
  { op := GateOp.or, inputs := [132, 11] },
  { op := GateOp.or, inputs := [133, 13] },
  { op := GateOp.or, inputs := [134, 20] },
  { op := GateOp.and, inputs := [135, 39] },
  { op := GateOp.or, inputs := [3, 8] },
  { op := GateOp.or, inputs := [137, 10] },
  { op := GateOp.or, inputs := [138, 13] },
  { op := GateOp.or, inputs := [139, 19] },
  { op := GateOp.and, inputs := [140, 40] },
  { op := GateOp.or, inputs := [2, 7] },
  { op := GateOp.or, inputs := [142, 12] },
  { op := GateOp.or, inputs := [143, 13] },
  { op := GateOp.or, inputs := [144, 18] },
  { op := GateOp.and, inputs := [145, 41] },
  { op := GateOp.or, inputs := [46, 51] },
  { op := GateOp.or, inputs := [147, 56] },
  { op := GateOp.or, inputs := [148, 61] },
  { op := GateOp.or, inputs := [149, 66] },
  { op := GateOp.or, inputs := [150, 71] },
  { op := GateOp.or, inputs := [151, 76] },
  { op := GateOp.or, inputs := [152, 81] },
  { op := GateOp.or, inputs := [153, 86] },
  { op := GateOp.or, inputs := [154, 91] },
  { op := GateOp.or, inputs := [155, 96] },
  { op := GateOp.or, inputs := [156, 101] },
  { op := GateOp.or, inputs := [157, 106] },
  { op := GateOp.or, inputs := [158, 111] },
  { op := GateOp.or, inputs := [159, 116] },
  { op := GateOp.or, inputs := [160, 121] },
  { op := GateOp.or, inputs := [161, 126] },
  { op := GateOp.or, inputs := [162, 131] },
  { op := GateOp.or, inputs := [163, 136] },
  { op := GateOp.or, inputs := [164, 141] },
  { op := GateOp.or, inputs := [165, 146] }
], 166⟩

def masks : List Nat := [139810, 481, 1082404, 544816, 329768, 31, 279618, 1118466, 559234, 7681, 590404, 295696, 1065608, 1966081, 168008, 149764, 197776, 122881, 1058896, 533768, 274564]
abbrev I (p l : Fin 21) : Prop := (masks.getD l.val 0).testBit p.val = true

def pairWords : List Nat := [2097151, 4398044413952, 9223367638808264704, 19342803890462029940523008, 40564799864490227013827707273216, 85070551165415408562502803963439480832, 178405876517653254897669880337535034105790464, 374144240750749558815158184889622271845026683158528, 784637342778915938768326617757641126644341398639273312256, 1645503772683489118819873703083672604024433852839149305344294912, 3450871527890724572511335776169330168875049503349327644001398763290624, 7237002126459088818691292845665063102316647816048049167272821419232458702848, 15177093483507931034296082173872178415149562600720798407244531984986189233595088896, 31828671953125624584436097323100386707687735507226823821349684741377756723612407868424192, 66749563043841309848499330373334622184800749894451748030591134054749845268437208386081531101184, 139983979636517890631400067691099449584099262242649272285850257965186747504393628441287655111910227968, 293567682862682767373421914758524592894192936010696406672815440192207317902334106672903288493252758403547136, 615656053250840890962706515379669367037242504140703990646708246029967961153515776477292477270202008791515683356672, 1291124323387107476164221894141504372420887192043685655392725491578239369669017917670906873292158683141144698382811398144, 2707683957039919217852750273742644177631208416568799459578165050114287850580120264079377691138397166666817886502909689240485888, 5678424825874180667558330942079933722407643993224090924253267991177278994419800372054595083726271894869650464315350060610063460990976, 2707686539290412961401726556230350329870296955426515470726305440618603256697262751220998194074378934060283308187610007627366401, 5415373078580825922803453112460700659740593910853030941452610881237206513394525502441996388148757868120566616375220015254732802, 10830746157161651845606906224921401319481187821706061882905221762474413026789051004883992776297515736241133232750440030509465604, 21661492314323303691213812449842802638962375643412123765810443524948826053578102009767985552595031472482266465500880061018931208, 43322984628646607382427624899685605277924751286824247531620887049897652107156204019535971105190062944964532931001760122037862416, 86645969257293214764855249799371210555849502573648495063241774099795304214312408039071942210380125889929065862003520244075724832, 173291938514586429529710499598742421111699005147296990126483548199590608428624816078143884420760251779858131724007040488151449664, 346583877029172859059420999197484842223398010294593980252967096399181216857249632156287768841520503559716263448014080976302899328, 693167754058345718118841998394969684446796020589187960505934192798362433714499264312575537683041007119432526896028161952605798656, 1386335508116691436237683996789939368893592041178375921011868385596724867428998528625151075366082014238865053792056323905211597312, 2772671016233382872475367993579878737787184082356751842023736771193449734857997057250302150732164028477730107584112647810423194624, 5545342032466765744950735987159757475574368164713503684047473542386899469715994114500604301464328056955460215168225295620846389248, 11090684064933531489901471974319514951148736329427007368094947084773798939431988229001208602928656113910920430336450591241692778496, 22181368129867062979802943948639029902297472658854014736189894169547597878863976458002417205857312227821840860672901182483385556992, 44362736259734125959605887897278059804594945317708029472379788339095195757727952916004834411714624455643681721345802364966771113984, 88725472519468251919211775794556119609189890635416058944759576678190391515455905832009668823429248911287363442691604729933542227968, 177450945038936503838423551589112239218379781270832117889519153356380783030911811664019337646858497822574726885383209459867084455936, 354901890077873007676847103178224478436759562541664235779038306712761566061823623328038675293716995645149453770766418919734168911872, 709803780155746015353694206356448956873519125083328471558076613425523132123647246656077350587433991290298907541532837839468337823744, 1419607560311492030707388412712897913747038250166656943116153226851046264247294493312154701174867982580597815083065675678936675647488, 2839215120622984061414776825425795827494076500333313886232306453702092528494588986624309402349735965161195630166131351357873351294976]
def incidenceMask : Nat := 743433581638964523083114404116014067405696957261370170794049635077385643021907255755610188632280998956555709889665995677887627403810

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma checks : IsAO2 42 canonicalC ∧ canonicalC.size = 125 ∧ PackedEval.eval canonicalC pairWords = incidenceMask := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma plane_geometry : (∀ l : Fin 21, (Finset.univ.filter (fun p : Fin 21 => I p l)).card = 5) ∧ (∀ p q : Fin 21, p ≠ q → ∃! l : Fin 21, I p l ∧ I q l) := by
  unfold I ExistsUnique
  decide +kernel


set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma pair_rows : ∀ p l : Fin 21,
    pairWords.map (fun a => a.testBit (p.val * 21 + l.val)) =
      List.ofFn (liftInput (edgeInput p l)) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma mask_true : ∀ p l : Fin 21, I p l → incidenceMask.testBit (p.val * 21 + l.val) = true := by
  decide +kernel

lemma positive_of_packed (C : Circuit) (hAO : IsAO2 42 C)
    (hpos : PackedEval.eval C pairWords = incidenceMask) :
    ∀ p l : Fin 21, I p l → circuitFun 42 C (liftInput (edgeInput p l)) = true := by
  intro p l hI
  have h := PackedEval.eval_testBit_of_isAO2 42 C pairWords (p.val * 21 + l.val) hAO
  rw [hpos, pair_rows p l] at h
  simpa [circuitFun] using h.symm.trans (mask_true p l hI)


end Q4BackendBench

namespace Q4ChunkedBackend
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity
open ReducedCheck CircuitCheckWrapper
open Q4BackendBench (I pairWords incidenceMask canonicalC)

def lowPointWords : List Nat := [727165423746277286308656163155855241632176107997488461621221857459814221232746196810842823016801324815971527864104683515406580546784789375740653176718369866052604199228128659692406550152032136773131234409061092131181257695072883040080860369267924200678600168357199944800006719733351023891200603531870587301567001086796983769274003541576373343231617356862367497229285945835179130852896058703745010462899963604451883427209933744070613504292336385342217662377224031494938254961874830087678505012776599484243829148288184912050018418588696804334528507800630466112331505253122567824699997933974080343770033410374180994328343561403832644419698021857547670487218953481109980216264092423501084273010778670285082290664205947794297454124937596873776936590492956555251618778271663580662341245837573313593411347882411166305747313238004175741388471143605438044383424854018014873951709940184506107013918869754940699576379169947311548654972789842284922526848298958679017985176627381810407720289793884972893327974276161827607066078284040370989175837543018407575105752255579080771995758680585691783696891193277129489622637110876713391475690313503780208002753816997223005571626435885957384720652367052608645271568520036623747707393863896781969410648618319918351825706672136079039286669851832485174569209006995893721241065768141070640205570937294547459809358579150812987665818402435744199237449881608688990292523549349834279611455341520718806486202358248536382914730152469081850909296860579870838948236765671714026412924966419911205459179775210518768719595452728762432227174492387879708668662948527169970040859212205620053099128821452772510612023710144104743601994746850770405248738624984977894352241991805799633434687487908396135390462559296438040897491136156017880735305969967464724717697457748530863024301080504339567345937349182547693021850805784652393154644220205928869776779624123385567094378891296353367624994207532556244843492396936602848970619149299683484789744936245236503073649584679845350384403920692051513805145294814651393590292390562730328077399901692602649770469295982057393953731308907178353309958943065457137309169707664903885209082555525937539336192011547616539109308447555685339488505567248706409412482520948067640132410498257903397930726126120294226372349881911694075475092529117045100226908646687953348931885643545698158829488018676793126440279215317333876958407101502846775730433916955900764748809484844403602387854312727204384312633725107998124337110317143861930, 872598508495532743570387395787026289958611329596986153945466228951777065479295436173011387620161589779165833436925620218487896656141747250888783812062043839263125039073754391630887860182438564127757481290873310557417509234087459648097032443121509040814320202028639933760008063680021228669440724238244704761880401304156380523128804249891648011877940828234840996675143135002214957023475270444494012555479956325342260112651920492884736205150803662410661194852668837793925905954249796105214206015331919381092594977945821894460022102306436165201434209360756559334797806303747081389639997520768896412524040092449017193194012273684599173303637626229057204584662744177331976259516910908201301127612934404342098748797047137353156944949925116248532323908591547866301942533925996296794809495005087976312093617458893399566896775885605010889666165372326525653260109824821617848742051928221407328416702643705928839491655003936773858385967347810741907032217958750414821582211952858172489264347752661967471993569131394193128479293940848445187011005051622089090126902706694896926394910416702830140436269431932555387547164533052056069770828376204536249603304580396667606685951723063148861664782840463130374325882224043948497248872636676138363292778341983902022190848006563294847144003822198982209483050808395072465489278921769284768246685124753456951771230294980975585198982082922893039084939857930426788351028259219801135533746409824862567783442829898243659497676182962898221091156232695845006737884118806056831695509959703893446551015730252622522463514543274514918672609390865455650402395538232603964049031054646744063718954585743327012734428452172925692322393696220924486298486349981973473222690390166959560121624985490075362468555071155725649076989363387221456882367163960957669661236949298237035629161296605207480815124819019057231626220966941582871785573064247114643732135548948062680513254669555624041149993049039067493812190876323923418764742979159620181747693923494283803688379501615814420461284704830461816566174353777581672308350868675276393692879882031123179724563155178468872744477570688614023971950731678548564771003649197884662250899066631125047203430413857139846931170137066822407386206680698447691294979025137681168158892597909484077516871351344353071646819858294032890570111034940454120272290376025544018718262772254837790595385622412151751728335058380800652350088521803416130876520700347080917698571381813284322865425175272645261175160470129597749204532380572634316, 1026586480582979698318102818572972105833660387761160181112313210531502429975641689615307514847248929151959804043441906139397525477813820295163275073014169222662500045969122813683397482567574781326773507401027424185197069687161717233055332286025304753899200237680752863247068310211789680787577322633229064425741648593125153556622122646931350602209342150864518819617815452943782302380559141699404720653505830970990894250178729991629101417824474896953719052767845691522265771710882113064957889429802258095403052915230378699364731885066395488472275540424419481570350360357349507517223526495022231073557694226410608462581190910217175498004279560269479064217250287267449383834725777539060354267779922828637763233878878985121361111705794254410038028127754762195649344157559995643288011170594221148602463079363403999490466795159535306929019018085090030180306011558613668057343590503789890974607885463183445693519594122278557480454079232718519890626138775000488025390837591597849987369820885484667614110081331051991915857992871586406102365888296025987164855179654935172854582247549062153106395611096391241632408428862414183611495092207299454411298005388701961890218766733015469249017391577015447499206920263581115879116320749030751015638562755275178849636291772427405702522357437881155540568295068700085253516798731493276197937276617357008178554388582330559511998802450497521222452870421094619751001209716729177806510289893911603020921697446939110187644324921132821436577830861995111772632804845654184507877070540828109937118842035591320614662958286205311669026599283371124294591053574391298781234154181937345957316417159698031779687562884909324343908698466142264101527630999978792321438459282549364188378382335870676897021829495477324293031752192220260537508667251718773729013219940350867100740189760712008800958970375316537919560259961107744555041850663820134874978982998762426682956770199477204754294109469457726463308459854498733433840874093128964919703169321757980945515740590136252259366217299800543313607263945620684320362765727853266345521035155330733152617133123739375144405267730221898851731706743151233605612945469644570190883410666624852996709918133949576290507258984784496949866125506704056107405857676632566080186932468128804797078672178052180084290376303875332812435424746988769553261518089441816492609720908535103283053394849896649119680394186330353708647162966827548389266494941584801079645378096250922732782853147379582660206071141328938528475920447732510960, 1086503979449690575651844228217308999170255352027375755885405421262913077639589648153165930110707037857327107781385986264265085330604510195659186069493595441884046741259149437050132744196032453388647447521709958670714408384855980884790079306610439272609270290463676182113628717422594525969731641074857219936971705904007944620238199844223063672377202587685405132046870829574742358939735745300537291897873875580192697416531574154564652084234463704168916662851572093751191789515019201376142202042436631135990779739076509751856836858902955536437583451344132680883794933919062513792547856835198625883298415679313951368957525010035298581545385371180149048510085907146872499622744791792312904127767077857546582099669475034836615651299517654472880714594355234697340940120063497334530502094947969464668754698781501509188353962192193009668066820697060265404837490832462714831118508237474125856394337922124113730106340860932947994877469071204036615759960104280672151386411770095778974959499147283383622715728101346855257250482727904678832075959597350461123893419712616214071775763942976286556185238203184504762704640663722404444850836888659344746587772240182621144511690861401586131255760735207010582818219111650052603578362816094802631337311554221200961482767945915386580101483358380055669395238360647561046523615778078486870968635174790296593645111651338179716979277301693874601195255854232438024405949583464343826345520821571813313971601967188474595483487854272869380346964958998717518117209797735168039465226408969828415939007913155016370382586201742586669164338541155431160034111176009467970800349951311121013190916215711535580058432313989635103280801489457960449865819579744091484168330446900494393925758736796980996069796197547985243986912826007435277051974678861892818255236668386909927631640524955900365217276039245518731985956067787184898721336111124812007759857492853618901806387137189882074583648932655648241322572297368309315193454293117036802176116947541520689417437511739535465165801967104076970043485576688039436337246217805791618605920475680775943625915212673579919370555730040297617396981455786519613722650458145226038600341250280000058774699347993325879447371376892541518924459680247094401612425245307618575139477164712198073172758102841217832400709551183231614717647981248814468821528872872272708131689054947657949379468479268048873747343263353526104093495435708533703815123051015820597912618062958175032361618895281114722085802920005724823912258217055420160, 1090731492377649913076371140926090508772288022347454197342151662049370236722216185228086315727659756087542381786669313644178532646766436284737006116912929052480815466086667985449476379848717017461066159075763944044793663983039270860309579287128095894281232142914478590317223256735391291218709799496421963380887780564207862618897899570488789617056638427895664654281211004766489910727727759201869928567754368100035673717570919126251088544271996521425780323822125382487425579684333175106262840178463933895343170737038950968066359623128053628535048757661064396306004795648304940834022134014394738759997701517820826227420441665932867910905808846005834356158743488457009559411929525941069176013153662608964473953666693646214666782585377199491581365863433169067968554135514558442306342887694230846994624550135534847376599232197823557564146242081587332064559992017476950946319619359444248109371748486692855799489698611814707943283617576829210629477688865539069261394552743917809639143313973756326583543848257378462564429616241730696091062171503561065325895232765192882741203763695870971284992282098111218660418751522767664574753593551408755505554155839084715661988085587581566973581015461353733620165345862546046674315694133031863752093388494672036462729057916866275750767303860636596466131368879010701380485553645594699302909325196756079672385052501103827150151831976334641466070132492510498840375913377104324412513915893203117957074929225098251683568818116610778983960015236926371712955543693067918514007296273844438273669212942647585898655890739354078797284894964671836167065386613546773833634383996775276160029552156249040219772103984039642838626279683147201335391793975777396995993145807139132507822505131625600404251400452096938297028960261358945050090842090295278274847010557189245433247492155849346122470894688100480162577170477926277810346432479715635924966607323646570559953092490196327592825540237991980241590165503279915261077067074366481305045563364399525904422723786141683588265993912136830065659108641858179205570900455649154556530215297251775499077409916111817294890330692445660632067110242139656963639480277435505310459643431014873489279414979373131151267245336657370517617194123667803452567018352064922735181294255470115135422465189162296162920296668926670039756221615001022346654653517921366037709997197050769974298091004898049521668450005074312059455258124511891747278706315095791213785601531930729995714415221299954221210448230969019753953267507156418560, 1090748135365456339041586926824709096400964067164273332347272707540109023476350483456643682700482416018057609895981362120404606980048375087448667425214590816869671144547395038055582970986878455636444962424714107236239490619974692554770930709212877821728916669614260327992795699918566977659395175021578144334544566109855586642133164142480791907459073081590624358274300179425040837504737754591061664838562273108983506886107634298866042884653729319819199997516446804694739144110610717674156946529148702714412442293984696868969709907445224692898230111221050144866923794893547112852427041007695329043678419482870554145720540889865230465166845682064128327460786411382323751884924288490359559578197608978570342104424944587739380487102228316436132266546300897104300298367464939913764498334082754312722554117819014494666733843304428703937824198941703283915032685136815704633686814941668193778404358975865825028806933982931557049500470592340750507523610764520132237088741246609468819349337613959440828784317324935031505062497594936585663442849809668662650964255879591527000676094851237579633838846544771148541303921518249715058663926914944350215064247014897203907073996515109866185678977480329325325801747949437443546148220516763024497923624659148936397529559134468581007943125037851605844897637030937792984208879998260560834990466014491803030020045397864796326702999835042686266982263606726267146269373602788359121917286258255297088099245591502185867918926029084430605200919372173516522535733737890028181875115540306551779084866614357067231533631720626002919587235295062368071686593937750462360071885117835669805146321374038164582655652795571977548739307436252124465110216812285016292939828102403759493188093620266844902118992158588255074301105296020131705096904108125908453231286645621791511653515435611337191921902927077389109450451989403004404527133421488734171726166453908082112971477795474787089400560567367842496129965928562701168456383421601224547224975507428722506692020725843928961435818309035149891715365798426895257374225068707636935783558936310339766210019945402769632483047091147946123851035813219440350036499475353738431721176746185131364175201392263406813394131677632259165477572009757420066823456072165146952257899881163435108097311824032068432359543340248227743649736365547338111070004318372011931585654645314294836757658558013694582114506887325604913720922722968365137005114262182509113579006044876988892546771973980841489093151046977170736321405274931855360, 1090748135619415929403854669820128643835281822143174671095392721590677921920417072578689030872885679376536174029528239896742254073353278082923030058229357091300030393146888777261730166167240147960083923101996823490514355455651568890737193309875090994887952495597058554419219395583801974058669822774425700320602000555580027419219660782965643544761919466940595449891933698401109894205870007440326040697196084961016514337994471542752611988248099510093894277317118938299181052534179992180611763502713740568706813166286568129787497207891105101070642977075903571570054027644364590446601280785149886722456526311428692503745869033851011170379573239871025633307907777362710306567563441148121858767949811499260469124776695938902641931594003381934561985005343743685083799012958615340497526215585095341939983925335426324943931358772634914039415810241181336029872642177025788124259913276625707191883433362498148979089190612769477364849156296598604956531440099537350932558545961732221916191503815951153776287037593938459242959091504280127175810734425619861520616741230751469122342495262459811324635237600645624320878844480106463393239977750409859338365102275402708239345773880027238141707183621557733481314949378274404868584905321709416744565607290993339377141986944120719563564133545054356921532678282631495561640293652704448981407979637281048067370092943735415862513219631905132205243835345916182893926006276981822640099165954635101713781042208879607159383576070856276803186793994557281304652875534793746532044826511343908913238927973380729497620328575369613527557267407888667221403469768087071709689761333129469855333306317190610121128804688744301302209854694241778786633133327396692416385648538584937903813623713078893779055091594531543783419179722909182516033055000345688034320365228169710990474860995658072338681123651241223172931351929918827568679587283744611196323840052692029991663662335786495300388236002058368899453352397682826240056654577137531924806502740465564271415492629087478374350216697724571799736835532009208639156739698175298800515035510452484116660223014932861307476880632787267150057929595142785268236485943223275300709970934124908318484485834183562070916059435823162768771276983699787719886834170973112315811783258262042268793707899620037982010519892205757909218844019984162560417654567467164875084760799557738260877398316200197677337735993893876640054030862480179650557345729971470059927578032767319931222828570259113571184368826210270342110464355294248960, 1090748135619415929462984244733782862445058741317256278077723357411872937927833784244419600432340383621359132078539296421583922726078535288895631126147893430149380770045156693316471592314481596094990093519266467060963746463149021913517350803079950400440665964304739215704920738623747423257015752366908264085893021118110308974552597077954159980749712419298225792610335570650809591039390908475045801933904902676564396390725443722970902476505668943463129909442136980589661502329916207474552401367763852856835262959009067319505910523234201508849530123021140590765937850147753368424740552323470408182285922748805210520738945273624250073532547213864411288330003393740150912580166278929704842831018825970092592589997564992748701241134099098189591461277259179911627931227354401824729735222739283906940258565844609867958833251463899830750255317198113101160530620734317932567900498223532817667589142046943165554232191512001478956898687683520250475974324734315380150309747612208712500051022967476984319077129296386777374636865231087169447708549517544139233017684215770290488418789440168334816327372623519038609022141979462139722689427219151234633118646875003741836690327166568052540560892638150017862105394046379266526690121410209850772135746339395758587591648792223654974745634225736271050568271311740257450712934213663479668020824855253157533409992242243185229562856090869187134982573538569852483225539869705077626849803583477586364785204481055628574836838979480433938208897652545831398860133527896735028968302348255129557764568722621963320682441686446392311846397899383114863434253848663932279264188564128386706056453584844520974679854641137384660894775927042925383218566634937141648684602149056050732108371054310349389279475071554719181040574555552962971974792722792653974763290140871652286270098969576677480222940290795746088405409748159994478121367758864292622252744789474675449474741606852764070764063110576030660846709793102667506631035454077016208694602827335899556351637399344567778304083178028820294133459605355876156179714463545661793044235280409193608501261558804583167350441282704397497970403108257267112393653696672675910688099839367469282734578305725116229359673050529813789252273363198230132949795533051518858815503461348243733779388689730783814640911372667854894579549420746122021822981211980082448791461461735149685581518666731366228054655612843460369296145991464644624232666058546546775071466057342070960016482455402459983974533531512623447503628532879196160, 1090748135619415929462984244733782862448264161996232692431832786189721331849109875331513870234605433463932241694048131051358947830205980188196448074959461356758486573232462591433156779577237490627406123547618423722668866652339479999293626021839890161927470072222416275310966999593803517697609822714708579884205550840414698745794222115405131762724689518277473450666725768294443700706103254859716733899036477127355717020008787842924414391583891235738543020558099725138939596081148014590965124539186821561529914566658849262988504621375111628343614858679068075902419555944729073976404444565343555827377610000620947577410278627011740831480055497987845581365988527549373552036103980380460119398337457819050480022405702325635582620236066168807184261870584892432597683277669260204163001806232850994074559052885958077900805983585439963419680319621217850405971289333030803245070840561728370555174569443676693629170452149296065798196661572238035681751946495873207469100150493032277188951439284275065790528306049503847529562489086229780168252138484384622224460015690956455991882709903488025930330456108229822033526376707136090265975193250434767826227728688689631822571110448349847083887734391639427413322727296020796085661840741564416933944834885347677704020625164362236290082483231096646670146316488035415210816619742524561606952935611302947966659440338951555748352481673455328318110092907812432976349828140055049776760942184789064042974347999533186945347522493599199813729152746600124370793863684351800627532861582603373243844541669894180917405990955855670211102417040532303109059148651080538307108200472206951864724440163912445823502524921620535906589683568560322180265439851314707032130422408981737587067461745778054108010454979688805716669890106223718629918609636282362876953861912714996254991032203811132391157099002202347885731138448079694323323449229027719621743895573011766662593894349081522104383894908548239240269319053774558041228754281281816861897527545504098214377454609550129806936928314745701910920161391616609369496032529549582045082542643910019366151847658440920119593061651167368561688293227455295170854030179178723762426736301386023622466277453636011514339531108046811378554467570571147700293987047007133169604516470460363030434395212791168390261169656611459540138630944243057585634982081359365277395087425491626723439059966600654655183801562224994052115182662706659658702893140791266483454391692605083442515414863001025232435847470731267136086799620306370560, 1090748135619415929462984244733782862448264161996232692431832786189721331849119295216264234525201987223957291796157025273109870820177184063610979765077554717727193825132424258268072070423477350441019325238935081369672808088954075376607323183064685826513719267367765025669297838401423262150842341357600244555889201894556085847866483922724148646867108659100934137092282466892797007055681424336981376513709740535026193493673249209257320971410979203369564857482654510028075971351626483674957465557609650341383284243352703413714646767970869719760282612297099758526022496503350912508240831354915423886988443810272342344732317150627439462977141579914873924393499344568782246440509166066283446893682365040319921619212785451204784909812620149202475072920645750021639932387054565814599265491865025466591172979897528545547657398713095194110513475640015533832552892834462456004562452971528736770337713855531343214788202807563614479213467081621550379582167079624431075961285990652132534019881887236124261807921871717536754538527881569172145267614894322853623609813920928459120198997814593256579843388566344082288016681611654470716138650900737275301237931416801181903989453821932064570156865659395968836640923032250896569702084633936822519618352768176774084397451792927718879958100081887861393908320621408161687515022883010853676704976685223953947630891854814753738450680771222651381548932686869654811143303224385700414066978115266169823947267240120243654344301634559922544942816043553794364709175132165894258852632905428043741747989065584385717223677332433400389608789558933209058517367950612903452919800029473576992005403338790727107551494317528931418468321870206715879080915763252955490226179218331260318126443739420462473525613282748278965996483750636045783491802222016697761633212650864259383149056931239290285624805626122759894380826805436467577805724137767574570906567601847329444596436887515074101490955904440736746378578909097694701009073306364306371857928229086986807866811037349498795349771504573858928341772320617473445645992985275412333509090804871751065163475735116124159825908647121640421907667647356208564338125924147715960797202874727558317522397417637853954101630500329587808124225607721416501990667502342789749660037118355919877562034711995165307625661050344070739613757088494470672876611099532221420366583803436275263239830405586791170387133117796852392016463145034898659808641129024904249424733643211466577601264042611135606503976088487910839773519358050959360, 1090748135619415929462984244733782862448264161996232692431832786189721331849119295216264234525201987223957291796157025273109870820177184063610979765077554799078906298842192989538609825228048205159696851613591638196771886542609324560121290553901886301017900252535799917200010079600026535836800905297805880952344434142288520078948840015587307354938660586662128298270350249817014271693665765110592008613298778505422237692146259873858659415573867216038413367887863225808775353059030740090896360912642226573857037049962736349533220384817969976483149973107413139227644176078619320341055567499174066505299371568329139777241183089138566334553194650577629094056611619967969653726624148744303488035402293152604489486492100208017863024726771025350917773611238726097375366394777344426511988513556879991178832915713510549481697173215445101845957529458649240419039109240935740910191672068265273719092589036748465496772589128171977093240953165534992672018013618814995161462309538660641385783569275376409313809965475889555022982121273477969648053452876833585167683334003690463172464081216829623878909681066796095037273252169666759578152053991219528513242729480885311699333643283995611022633415058770494955457423321606395672379513094283755488117583208734138564299317466532948220527445976808475956204587074983904100207162912865380688486391072610835612762060729181212793646168221753156439697858063620473480211440842709029593612453629476963272918555621144668718781463666529288238422362202825387580631554852164914519052059660040464663126781487560119934326441860936571324105415002310162950779332518014848112844743427605942506544050522057943770995582957029023526909557365112077631459260712531564908022807631888258826691914906113986248716550085419858013381711311649991056871703624067763554136461504317273126870747233315465647396625310067987550217403326963292546153158772672740041967708838522805761174003091611777775043411335156923698959839678510230832295163313316789267444620224432518792403169045198033711681799380593647401842461843648423716417664365528718045683794601856283379413891052412969460121927658025990683597601528175797008376299141662638078090891860989403913605461823884961828737140171022361679405979038786444181270716007518309822554612689912150227475032388745809549109277022071797772295031123798251651255599727407916691739326020171853970956314931166813991316312725113081108713697206841284865031993483234062808071776305097470274820616405375977422257119466656882704639478857686056960, 1090748135619415929462984244733782862448264161996232692431832786189721331849119295216264234525201987223957291796157025273109870820177184063610979765077554799078906298842192989538609825228048205159696851613591638196771886542609324560121290553901886301017900252535799917200010079600026535836800905297805880952350501630195475653911005312364560014847426035293551245843928918752768696279344088055617515694349945406677825140814900616105920256438504578013326493565836047242407382442812245131517757519164899226365743722432277368075027627883045206501792761700945699168497257879683851737049996900961120515655050115561271491492481590583927528068362121611832823090350947768974356780606151520143159909137700592185973126172549006476832634892320043175548198813118732027663641737580234180498216659031323755528672469578345747574178638520542422428423677558820978627530386229456967934723788568179648262880758976714398711940255399001607683329891312982140614519561421728861174053416163557141099001227260702498594974247602767107850237371185829184296776123032637607387534110972932388406207584762847633426555552446542114214004891266591088458003495784055858294944168684601688858744297754455478086944868426545830699462053020840665064540392958400443325645527374926882973919246656771539390355706463348469275233864897316857752844929570354333768590343841311070850781091725431885844774325016901949773780261558722409401181833978850211680880235006737620395003207721429913359698783128999341087064869360477360260946612352621282830392338045342868360685801099549739965616135919539306625022788065057280252729962269737132309764754628744321772059641657719823547449320592935611616099240742902136329711517410404030324521840342033994485065200736874265167184988389293259882587602113424959054628993094268364393026247954669688793470940786540624498332650203138482502473546445070830271563685172304095213304349600298515635788989580172037008658825732196098316200861698353829406714272630544531590748563008319858775677970324879375646607814716537093794936528532510075217655406621358266156154358999433998158724863016801311862884415003624026624271858216959376261551815071325789099581359312420237157949795754513740566131017746235944565634476856040075065074597078314422621893894702231993235077806982696786165968173125570545073461288474360408005636640266535246648614607443110206856314723120840607763815821602035459921424929857198102394553285216706183381968298312489240849692137274288006245419386744015437915115941622091612160, 1090748135619415929462984244733782862448264161996232692431832786189721331849119295216264234525201987223957291796157025273109870820177184063610979765077554799078906298842192989538609825228048205159696851613591638196771886542609324560121290553901886301017900252535799917200010079600026535836800905297805880952350501630195475653911005312364560014847426035293551245843928918752768696279344088055617515694349945406677825140814900616105920256438504578013326493565836047242407382442812245131517757519164899226365743722432277368075027627883045206501792761700945699168497257879683851737049996900961120515655050115561271491492515342105748966629547032786321505730828430221664970324396138635251626409516168005427623435996308921691446181187406395310665404885739434832877428167407495370993511868756359970390117021823616749458620969857006263612082706715408157066575137281027022310927564910276759160520878304632411049364568754920967322982459184763427383790272448438018526977764941072715611580434690827459339991961414242741410599117426060556483763756314527611362658628383368621157993638020878537675545336789915694234433955666315070087213535470255670312004130725495834508357439653828936077080978550578912967907352780054935621561090795845172954115972926435488646325407501512365848213380395168763512806429730109607098577644744240048503459529594006823631373147762011780218660740030215430505248911586325182120160839367048207709418842650690943826010989109302792718425868852384783378651199618535121913835737651699662333815683378345818068070160548347800369481364172406204671458973952634913932812733482191175501628465349005403383205634207163186366050321349674463279843106828789837369958673440743379029655723491233599261110682223445532527992025505094106028374148434683256837486589543018181873279720349434704460879700399438016504650780473547823239120431423814382915239771713285086798751923825359346515261480728322427217167293613096521198247560588729708788376007087530154941809492620352947595475014394229254625965054086766970439573627357949092810593883736061141168581582787315634913260797956280083967967201275577888581524322407185240031043931510925713450658807511908275263101371880394716465807521940885628037330976885109586390268456528362201664202524947917653322271271470730573883899274644538470640093205628124760082118516398285556726512915645798229781241791101398278815512033744564071010914628794915292515492524789530849844709747037539932187090270337487885794730917151571753381797325072561602560]
def lowLineWords : List Nat := [3788234314637658985242352021326907479580684570990094621753162982393421248403210552658642848822348282526872429170513924508757376146032431993343776355948186457156888540090136314785990809902456880913298028173961746766327472303881603346406976664771593961911913092345352107178423929186207609225232420280106415978478372633396616326387667966076322617870912392163859569147930598590535073659106443722446990540642641580578085269608459566603589237835757453792099918247492080878187804720956523988772594725595524323064613207642027220426072928932750092740233858959545112618839419362003807417866268811870075279169756039042564701956863083717998858350971930301145950178531054997746303495055532630337296494820506301258878459223172292850114710542355180333243923548998159738367728616666530678971168753195193670822196598020638151109097167943374578090126728067798814838110030715821282514942713357574672131654078997231277984287852788027419817873462876890828329471769033461586082973118902184952749287255435239664815294289975031948742536444366510522987246118315039163279758916956382411398293374921481743673593491547421587516520719108604877270657661445075859402320328975793631948613753722063775738121399813915556987835464911017078341724328957433835172849218288028426850163790914201454373258217885892149425256074075657558802767304582860913332631221369375656801033695077597446218777254007146429605579948417275031310197343220048838460276197278138505564404603760664619972534942803001738124220770213074860937048280250720160492502102923099028859707350237464859066070748339185200200705124463725599175214306426871634156611881536808671674246711985771543152149729227025343262687900526479859604437944811291977725180383925342013729485155321246760791703830570290437740180816559383241648840783752615366482368332335493236589606510120381443979170207253089747550190449341939861409110903522017928957679029551849255934797082046653313442780000263747210034086642830365109354597589060863611378597984310828089518262977685085780459266113545073197780093404728074797772037154633940522092484892423526934206563841528527411696887489447817999401417841898546300969586654973726180862284548261776991616507230556975515051623545575248258866004516600783128392660654217835712997717454042212221594428913189393282779872995432519933642683145671689825636131559431156531, 116467648155609001340940201151316120312508972133810216609476566503894362822816089314344480970935784646224019196646181093854668050886720375377616116514632505018474003229841892818102172685594780494635287810080275939922172921914778533241887596857164576376403600638537982993194939497725149746214104078491086397513932009324821161414458763702325002972244538823277773139317702586611794665875714946081731241616401707543148447626026517141460743568884455764965215657727530467053397479158665077172297838156005165232120679792204086945863038420206338914412064251656941831793294726056275292519643302959091798378258379829029413460709158461502732726942747665803465840108286789094059879730762898141223599062108028221321640386680656462021090651819926774042812944076514731160753113267464910539881561729443751900142268450944339191101557392475345085644618143315836812020875474434257479502450246400252554334147861172117078020116533976466464080223938107039862316744623384498366488606876421224988973198854379818236190451840194813767793624863244430739662292602664031415202398199950078768541439100589431064650701327208900037838168839434189706940000254361686451873404306985804679386648006742915877167404637696783430109689540364557219949900431807147559396971643021077777921552834178953918443207926015176014441336858380280581200548544743735858071019266719505178114284985947698095178659262651692252991018508672833316636735611908052713666378218035957372804658041633836752661136121474726936879611081744386670513282853502441380187500984413667734392650487660694620187731069646603496853835316632798607320034750644743158278715128971563663464286896705367550378493244105992564981052066166260541044814890390638700032787037758677340875334299929255266966538056625841055457702516499442476320830385859248156034786524519447117904012313368211240487682287441681695135069629887951950476842580687488333630978241271675184829278767851635571735746740757335538455722437616014811102448215443047645915450737111842486171808483764260887767743341762692408996202143242723556653318280289406178012641164217076399386267973999068667219976399783511317335929702345273791046321710570121216624361514988172332635067313932233812595340128980058711820750336802224113303371721799580928384842364501823987074231735611222101938608300020587116591249901160946319306811581131322281974740263334401365, 83099830259389269326699557970261083796278110744845501351502989867741485262272080948451447696801552910713274157695295310612669606093508721046087789790120427869260066106752272213297074042926575245924004919071420683656888896748808688839035230350036407230619983174344958655735657285235326908455914951811341350659008329706533462347973813970858900050580733741078143996538011507939111475324778074489204134105817625652235231753265745663113037428706159859211691587061569033046481495910622642167399051123413970965477900020066504445913722754762663570411595891096742475668957510704409711094604679045558757096708805332428447722166114009559152238294537493799626526762577446496196040157504247821273197022440745180337475175679572431276902612654638555830104042756294355819118931713183848153245502542080161188363984507208947153089915586219295664795526718460555555544998022742187166873397277826583817257128622426278376956346624930219031412592639978494174115690412427183697976619526670605734426557497623828571109411438671834730769783462615509162595515903371480971454864660739887176050567298246936011910802426052747959405740770870399821685943742385063046070219652934613525890672060390896722183440264992882060194508481635102630677679971821081047110601114050157933776623670743860657998200089478118025963706680150381557069365806919190816318648652416223350615938552978599512692253724810689525894788283967429753292543977151607146234175300428562576516036009734594428388172125126544808159930474930228522922439699983802633942872791616864500483582689337338401170020222010076140810808156842815782891769633568059004177927930769317365447614255444311027609744864726470578457053259091315582870573776622557022283169154209468202058652349289674914905606204232723355736322613804205468789255227218372363076120384400200972998260984435818060192313932915716882126252239561202926647325425510930879331038763014417126001437098015086097831116198187675632136662596513210484653002174290811334658633371192558909702473161363727075398131031847683604876398819221984695877980619154679148217944652160063271427093865332422433599147765248066513446060932961129486188646713403521435499235886335749176364815, 3710358048548953757714327853106300255416727217713508566013142449297478255462103446237655570719483836243954848061467079782281643602583426780375904463446135770057657066332648714831178207056198693680793138922889764631143764130159576462396484392962232848250166068510018217152619790917159485556788972309319902897584929767205720588415520074406453667414818701517268487350367857288579439188414557194725237253953111308082600203207196639187620007779711283518873091823609295841060229639791359960126556266512566377352843530179272369944698272847179043803590750862676731364626251717177135531495983522125604382359481803035243226727472072061974778385887852369570173967458780285478773698553599846839482821698244473213909717085166294461700562682371895910689608097844283235819957797583572282367678547933032691865968386996417746817468611739519480687049963783760492843391561451074908374743918966202813145371827520881499120082509189857506281053075682658601685179648143927621749748206704541745095349711477686856602080934217000533649905458554440730746195822041051995022649823619967211931426989041762127356971999371473027887441845915332552146148076182616995780130644407309032025158315800315313924718956593845018209535159831179706971623763542015, 30577387346900750079121268262264498627313811838773530516032678323227221894000060072592961867451816375695688525472590250501922286671579791475006251826194364823918508747419674081167706261590896296809067765004301219066927259584057269237095118090909832217361418553219453210560069005329755908515718032521782876164284210522151994796913405712319026205333150734579523522192274745326883395364140759174898240639420940419927590561038300990168405711211416772516653734862786510366816191619961731960930157251719996721186293762397502627834238052897469138367153918785198503755808530340052406389075771529115652606477129285586026880546723088616758461382919210927158736462672642565974747785386524898978794731782925001423306624800952977974762520367652602694808940206662185913032531324236544764689978996688940282185344426773275810774991973250750793088532591486792191594738353063861298622505076662823396907984038105625518963140884567113962781386588908673018231713048916034679008941457021013320883697185680949129464607154065212588286372160151192848292082298105116037573542398589149177340089724106128907120344373269886652470722864936597824975352792352971405540236956466052000369594498559690590981381128142270517143461744943495418364802951287220744778810077471826344117471973745605835247299326651224891619102994572492275390461036764692514416902507952922233571076492029017788778934853061019627386887504122214256504964279101575292008058907057612372137438293229801487432064565993174559688334990065395905112056687818193151534218387879781043210810772020069612374131452995307828278982897433819214520790493562152499863216467939150233804378318595044588825306677871088180381916712184881585203332902380192952950802051660654290822267597214216581144299033097778748738180652205681537991830742928707295812192558376183468273398399384093022425571028973892098399206562256436265215, 253959590539656467736382203286086457253981060173877922959092703915390660000152409825571031391334957120775303085551673629940847039715859830222753713675846465107694446097567546096671691938471025111658469942689432795034097353379107525921519398648153454918892520352893610846461656141674190754647156235867421419410482759030060473117294205697685065806170716206478411809170462787602832323626363738263929130652424538817780483428547414842636247929451248129545185178374227234344372916304650261956827664077684024917759873752956567757759288801067624078798197624213969519527449132690974713708500288117123023553791721145404319427423100344178282416827351600664867398211103309848362960443948767077078851077995928122107722824070752718373419229355597528633894960948575705714990355335754744319540125568374082436433784724224948832496516101412190989007916698329167851457443351970162629824533951492349876093964134512090865493905642166471333510459055722199017068480948337004397836227281696382652334127887888249761397068196823776142537336230417222882197466491890390835364586491774117492550927101035943435640372388427161290976478941107995116226731470432691691079368446156196984116369075594773784437159154335053666085565100922365841102659850601999276484821970566338742688507482151646642266225866045559204160089770949895110170239061671738750762328309170936583281721559355021696736512077131804166358890707784314684854610825162232444756528236213514219490535966321672438805403110456891797208422116953467106301296096017786100422305415862279996287787719420987617340958862666530187941922789095840964489345296118431783090280508948189809126053713565974607943559571439334351299872266029945545341599146560548336265820852474896307714965087263276635284761542973438884206040666541100360370254915980960243162118464192588524597007815109919096838875003301700703528355088132744114348830293085827398521592103575046745645025531432953566049794870742743191776792934905201478014031937803038667186083288759444384688958237345499513419835221594644825044638190247727390526134049606097289762039934820715316915050908198612043431310217546317201925268307450100316995255387968526039221824582785072478416692580966771903827491815937920432810364007876120419705948839226749329693933268329312178591592555812567913758357226994330608334152354395417497664638903852684639219779778397252554223287054858747111754297729285969060082822039801881695957279897153175213438549414441258371347337924046009895511660837375944951521607681, 65783835702507605632453485653084460360890341409462420388021375443724387098727320085852069142068617551019183558954767678972395202723495413700757215514880637891820814907782565289791912874377449228907275116680242322905301305680761765312889529691312518023232839166694269483653882581875533489266390049644167557307917838782375410790429556034915224317385467576153580640801745154975832269283088523609951587371391559968195999984234619005861057054258298192319379196062303195336497894443397198322339050590586823436327057604974503240107571764759164212402915762823206584644883292464013357850076623894243637904774868263048756208772475843367171901242179122058108177582917311907581818969694564580491014160419219663666661665203210922955878412352026741963640486613915887367791340866291018971023384204591632761303092616457601212321434913154309325571318895243571097481260344343734203060064590840498040200168440651983523378638509992452419364918918132802804262848921876904533285292242992954093038122652641700579637076200972223987163732369304113445971829581020749479709560617169849560008636166844983295677306303644436286259885479187122169500353151274602575637325727768884318310805890831006843217659080339545871361853974142787010027530745115250133165140868595151014633197558621495732567376545679882532074094934265112368619417059573491462959961315854473043231284057090193836239643570287479122349394628475657439366766031702228982291457243662852531210359059685443038146098778892553539966489002612528256737876239693965720767627726758539776717539776950775470042716489692685291647788062782525994612816908013292940360631573719918164595959846606690263009983978076644427310099668000921815662024506288237555960526848415936927688831267881983397135246989257182264889940983332454080423912078995334327508284603034090044888125639417481790199239504819665787626028680735785033084889032563465677027367697680233190830656232731056487645135733749894961571080503783712945553069252913754827379158135504113179245921300475899192985200547856650595485253291566500234433964040029084074803422911904038517123212543847710271423878512174192612574163286593647840424964055707682806397221911868211, 1803903683390105711674695617302246531790294968505104080299222985630860852790977748974337107979054732222905225542350548262329487175363537652443701431207626122080299032780380646594501926180564898748776823172174408142720018563656225487972581634698038880608908700067737788694636725259322432435519719007755630149644928182026820593040431334966630245549250803878198415655297137714318154305602917555612684786278315493853420826600851673174699513847238056904284682553241658592221472853080203670835541831179899316637939023429623105205703943822360105427004460307794206973946214278583541359813345594519484071682102177365092993708476230733017690393277520452445184894876319483940195867313614737305322440955538495614630920659065669341616295441694314752831599073436596269166637758459670733115896739391872970388189836108758251236233721141192098844569585332654008683840853008417167533039326999843428406105187232259807735131824239721847369741409298137168570821196793234070486936857178656173238229136132731986029967570367782524628636114620391285634236668207364144783825310343757141843417503558060869047685513066987619321685102668734052173950255011253181657403506174984665117491, 19837361616378096156847768434499806238068371178428715988459479667716709757061884296659370485404905783871719712275218040882860577377196576341021165247353050501241685116858504807573758234926973055269497213977894075830497221387454831956094474371640967927111114247131068009456933768325812627638036121814527688003870334312694573746278135750922733974843784039446905034435184626166644664259439592550656790724436375849612000880466287225280256944238449689631517605864088983930853837029784642826356327364457296300583760047903943111828713862432158781909341220038257151561160314520678805442550159661096649679050145424834435369210336029735612493539539753419739953042467379479082245799619123574810766990944230771527883569408037788689270525778543939594862849814332321669417237837394346086105468279602510686284453949371202741282179596274461481076630266551875805274661819515468365197827505582568057265570438370575490264771308614945683796378734541114108126479671676949809941215026036373823598412432867392441749824065815279056441847134998221599436360860404996784576410328341349647208166948584120992163546092757482322517700722333309600288028614502393368525820318157087681145642419031763228546533178747953142823461958479854873139080593530719286374485766249292675218238720993238440743536006050356712549127580552834654960156129563029288600466486919061082556931655821912246079803357700837967452169547122114265868993296551107196110002933888257799260421771799045468835423700963706368619825915506574750891883237422691448844457056419424199176574723174702716258586842770085139267747655162652360460744290285833583198300332178410467081861211173883927922674250043678867759485973683709174267600676974969845959679331163890637873021363248068761214228330867372391963444687409910834579142819052659974603003646164734570953370175527369927859247461171, 4469269309980865699858008332735282042493121940197464459241187147907254676691182325600624766055634475896677286062162016951251294270648856648811216335361365, 259416774704153650798133166743766438679623879945676329182120512042142809653887939887302011713246874869533847705443496004115874239041149883225393021559445625640993941259103111052499486254390990038509659685497316952457351816515792114486364808262983733988583955574960557025089334611433881596583396043460441186665270917912637226300998607301696421963627991670351563039281660337488846985289151971565690969094300433612680183742422060557198325998036165968990682695060222745351526535553482857133303920759116383700621208602805961517941180435266276987900682535157119706203297238832015929635104155389415155128563898785461167893373179183275161568454515599366059805664917604941079691330512112087606877024337781006847460553789355491951232731321270108204509886191313197808355537046689835924812382648479951485149353987329059795706620059961517061731030470150488422087267848606107443136801336971038679936764025480029265343171265073465123044501258109110188440329163780761934061242505708178367847404626369933687188965529385274025591446138936457751490506838253604747898518707286068970332446437937979793146180214822145842146224551394322460201661974884490861743889739395306567015763647632762586797268645674944180522446451717585676114711506185814163871949268435750534799162695438165962394366278707651672153733048858571345370493133145721888557501767530578987539001909664052385753963437123699314231892150715346948195790317653171954480550727645360489010919500580897481882283821433400308777000338274161139024439272227675637936039025180475504851022769655283226899702467999334221240169408196518569068571646860351741442387633186128467261206422762746624658762601435646028070702051098738310469915459610363365041590059738650140866869163724943419980401288457203469655495132786197320547248158642820581816049904766147930752560217971603684944681097353446951606270803760149489743072598083500621739131883141064719742981339780548081996529469948664664060960658919336720773267225052194142368632284417018880949935541372799443654560066792119065605607850444577837039026096515185101549341782738990390414273618555328829856253702085479619331025772573369728687304292520149455310230235673876728030855450554094538183776626775113172443767574993362346851779491086863331378334151782014783723895908883207201700670270973721377440337545900085656620815, 10720159622328406868218542052258500963852739700015501725429130298497009486484561331980033096382950114627464330593795062496356515661297587172508597576681353500030741370315425257008952695421264527863372286674330509458734797186642363802087277901453185166307951168532732876030039114805501199950125268801070894793620508174444139872153055704643801745145123555964443249045335603600967681852241533503422681773166320802702111475249380280659649323454651918998910202705742487515138269240347977830638889375190791367808145955280154092021372788486652038647041700929193302193906459077805885812860432593973751419025961865561193589298232286349959689644588293616712432887746019555767243207638262690956625825182790303010322684624189828249704041284354873454760648438543781126477912143230272567720009609088538316666703562962985544949514787822562702268103546755862338668594803511028950971258898709228118563071539038585180944459740250612595755182144654009843976757371853332766005990021834972713540333945688333017065186463426899387649069465048126773407153759043898381246432946023163065208284821714618925050664720692507899819183076497259658675890815259960631819036940858387753665935837128683349803970377477134760733555226401244817287738952949168183218484727990156981021361901762075606510092487711168108319085971989399990442195209806254079307602225828788514167828652774054203961721025872790038241024761717323274122726163598382989302947118882045947062740331469108811211927737208672282195135617657147699908246221927309148221055766165634835875524532402403884306753636273102108313533103901643130111318501043759179752902952502054847964432926500234867533936520561915744653719788987481359349776598875858267504991314666559537791579791383506967927499249983585455540582896776228899632194587044900483538380471096611272098807280696592569091094670814721820481249675242175922231758944224740888319367127812551644378752619560413553447578274177783160409878387359176339556391062189428088580488177251672570551855259975026851810162033222658140513233403130116830607545216941336396614241083069267099283790352267788419971239314849904815442051732375695868363482367331003003104327838681236167631923181331795179759619027440535946241087403900462828697932161326960272096709084425814015, 930238117145572505860030841076836898937682868347797885654176703251691923410713730923791356341144150194428300762277307455703491407000680267186244556947967007443987577934042623309851286099426298490897152749458272834242805617007758886771576390478847300716345497997101545057546198473358364065094566920450201809203300799191462689357774823148974437017975419632556895158441091158901491003064647891596801876776541575602486094397351425104991977405255418475018012352843556323290403366388391914810486480706499354033749020459389837959696927180557014541721805490060043992558664608511492290662263140688545951699572149292102842966269457415750626061738586011448271057393331307466144804823889079595447405204127779490070090906603448732787024150126574264879401100336961091921530084101992200084198247205605697760432071076330308290759671782214716492348568690207311657131526513123908163372849590399527121405325015636742469648516743685951649984807461952241569434538618775655237579203628501478399760052360563720829661066596275116303098197216220325398908352453555544505274021094783938492338735463533447631350799033642597090324220825920095707984673824276084009560056495729039106546833828897609416065545482606147874965585763413321262463890778335323527776129784828914059508162255530445246108502180386038802531038766984511667104225543022002957693174759292393947076744970387939641353385593895963776509923960458130917367450665107667349767529575238198834715307724048565350114171080284837493426731208343281725825914680728092218497937980866554955982812209588625725650096282931043823565293865815519050263300826200897839364992785399297527443104842006529089982342747877963233455624800051091828003223753520757897220268755886103972539455391545966069187040408846618333036772350635923780777824253570578079054029190457081621416624188263976953189165603435266007255125550561071393453639440144675273066397714698511862675243417201735469365944463766733777478678873158185356729953608566036155424201531618444600028830852318516638183101762261726261228573299613009248152250645739270975327642964020471541956069160626299870141530864476281622912607103919350029295356817819155939857931861261148280634273514736800846502405159209478237676587091241194656798977433417075082627387423278445294847692079364526817344177981237804073215, 363582711873138643154328081577927620816088053998744230810610928729907110616373098405421411508400662407985763932052341757703290273392394687870326588359184933026302099614064329846203275076016068386565617204530546065590628847536441520040430184633962100339300084178599972400003359866675511945600301765935293650783500543398491884637001770788186671615808678431183748614642972917589565426448029351872505231449981802225941713604966872035306752146168192671108831188612015747469127480937415043839252506388299742121914574144092456025009209294348402167264253900315233056165752626561283912349998966987040171885016705187090497164171780701916322209849010928773835243609476740554990108132046211750542136505389335142541145332102973897148727062468798436888468295246478277625809389135831790331170622918786656796705673941205583152873656619002087870694235571802719022191712427009007436975854970092253053506959434877470349788189584973655774327486394921142461263424149479339508992588313690905203860144896942486446663987138080913803533039142020185494587918771509203787552876127789540385997879340292845891848445596638564744811318555438356695737845156751890104001376908498611502785813217942978692360326183526304322635784260018311873853696931948390984705324309159959175912853336068039519643334925916242587284604503497946860620532884070535320102785468647273729904679289575406493832909201217872099618724940804344495146261774674917139805727670760359403243101179124268191457365076234540925454648430289935419474118382835857013206462483209955602729589887605259384359797726364381216113587246193939854334331474263584985020429606102810026549564410726386255306011855072052371800997373425385202624369312492488947176120995902899816717343743954198067695231279648219020448745568078008940367652984983732362358848728874265431512150540252169783672968674591273846510925402892326196577322110102964434888389812061692783547189445648176683812497103766278122421746198468301424485309574649841742394872468122618251536824792339922675192201960346025756902572647407325696795146195281365164038699950846301324885234647991028696976865654453589176654979471532728568654584853832451942604541277762968769668096005773808269554654223777842669744252783624353204706241260474033820066205249128951698965363063060147113186174940955847037737546264558522550113454323343976674465942821772849079414744009338396563220139607658666938479203550751423387865216958477950382374404742422201801193927156363602192156316862553999062168555158571930965, 220297411312810468835647570470569533537745770649976231672790206331331828376430702345334472123968998332668962813617619102732596394574678190067246897356858740071493990147191063157371002690859883100704435304906941052428903350246167763214281581916286383958762415328976865201491248551317916524082519038903949622910270793623769587818317247220707217054076742884615911405950579948473009612946319388446913050276766683222994691607177876149317846358726982518861970081086937644840083197789082442284992651719285190970739336158602162871081263486124860163745766323852104625807660062004324134314559706812154519613501068840124034816975168113825121042222635414879899645216153783590243294993402613953522420608376890434965138940154407601462243432329567422041427101442308835877973200959714708934212859711600060561635252711499014614055382855864945496866951397389117587716405634202605765406805280635951053419560198451667185458357357229419226731148842958753708874440114998557999766869352133203540536450287896738784037249730902967211556288061856473234975872849037998693491540259964294641402738697374278151818554864798432266082827814263082638419720525742827989686838323106932534085799879179264326278621842894988813639104511974005062697215, 17146107731817157459071674752175813989510614858234885313061650757993758366997029971485870329945488749385558463143252190207439219509978332219480843760688734338679152081739437393979305492532354158151407760950044528790494803544949213065105639710056047382667339489514730183813871388997188435707978117753185079631300859162452628719402694510981878083297213544680739601427428158739419461220212524354821188421315462462856153522825448270076839589281500826411331312213949547429848244621351037350327968466589260102353598258037162562952926853949234705530568189848802087575914831086334977555080507845787691195398463618697053013322034645509443643307307743231077353462268700550542231674321425224230408978528519375041598268744417026353653635590178265651159549419035095285565735391689042270744755594065878832605718628989606915674789397752786901719540447031551836563046887841074423716484843370016259759194971887938994208751181398619837518086346504455318362801578777718951195118965565717435018583837534109793750439590335785937142011138624566959581793315775980707679260814996876700176385138216769929958084143766431841583833045779834929642755296072657241916015623777951876761213444855979617813682993423443236840540765196948114486355747762874453587669339964597397570076100661589869103674608020242007818527168617838316342017864127629223323366569016394517186708219621399272155601762609216072728075406168277907561265856912655173143672647584168060180812339570291129238397749074026493369309979919153877393787127980247829813347164552649324777256461985801902746363946785204442715558797266485564752505145491084834517661171553312677803759898482105491258533515185308692579680205690581575602901030930204986596161211656949684682389940475330062955766771537795658869631514965401869186394896837199033344659215, 272071416082091932025715055912928052791414703952030187687460020310815270083222860557086779343816731748382834963676083138454623666608156183104582747247823498307153716448531550071307373906170447121710631105366272692298052872958843680381599830973001003204335381523160432691995263671835410923723580279068578092978069450146177042436205235993217759202079935988615556192398235890739173265536871285039121618622382522681183739733194709580575601932598735114234987686095943277214210276318855051838105061255784618238923023303836126297813925648972792003870076706948733403578817392144312774185661421053061373358504424465041285872452262820052791039356477082547074207771710850182693278994640425988353805447092983840404722099195039066646824818964081673818790629176562119676198853705968337842350951405806618361206561544056886174548908843889244881263231827114922828918175998129278404701512549497513315495971827937060130465740140020498504324669687576577928611353260812825067022328986936842202751878789909034527092070564796554566626957311731710455981190585474260079370586676361577898357088475332056941141046737434435769351828399015581657280532116739434647791625584741235397729282342375337454408416420657125091330009618970174083841556652180265842967940395632076002718521405613163755506373898611589740806383519938892672406186856815758376355181533247281228724559102066967922960465676481855180183702879374199867416232977876716651081128216526449658312016913051469302075699451166218954605778602524141293770177319810386950904145014361503445229640053611049307522200514403214393164649415287920157545745441096522286897789600196957905027377787791558133606887111715236068826229645002587939877612199030008207684253800032638071365210595826853319989654847134147595518457068141365125825797149000814847223052282396451509117199070397527592379967718158470384382762630798822170585795010925692060327545499154406790611136074746713079956107050021878694817476898727216117497477452722922715724920448602668707608778563925407668997298860372395113126225991363769820946149604102758531196126371793492110948288319341176761618043807864273766096867189041400334967177215, 363582711873138643154328081577927620816088053998744230810610928729907110616373098405421411508400662407985763932052341757703290273392394687870326588359184933026302099614064329846203275076016068386565617204530546065590628847536441520040430184633962100339300084178599972400003359866675511945600301765935293650783500543398491884637001770788186671615808678431183748614642972917589565426448029351872505231449981802225941713604966872035306752146168192671108831188612015747469127480937415043839252506388299742121914574144092456025009209294348402167264253900315233056165752626561283912349998966987040171885016705187090497164171780701916322209849010928773835243609476740554990108132046211750542136505389335142541145332102973897148727062468798436888468295246478277625809389135831790331170622918786656796705673941205583152873656619002087870694235571802719022191712427009007436975854970092253053506959434877470349788189584973655774327486394921142461263424149479339508992588313690905203860144896942486446663987138080913803533039142020185494587918771509203787552876127789540385997879340292845891848445596638564744811318555438356695737845156751890104001376908498611502785813217942978692360326183526304322635784260018311873853696931948390984705324309159959175912853336068039519643334925916242587284604503497946860620532884070535320102785468647273729904679289575406493832909201217872099618724940804344495146261774674917139805727670760359403243101179124268191457365076234540925454648430289935419474118382835857013206462483209955602729589887605259384359797726364381216113587246193939854334331474263584985020429606102810026549564410726386255306011855072052371800997373425385202624369312492488947176120995902899816717343743954198067695231279648219020448745568078008940367652984983732362358848728874265431512150540252169783672968674591273846510925402892326196577322110102964434888389812061692783547189445648176683812497103766278122421746198468301424485309574649841742394872468122618251536824792339922675192201960346025756902572647407325696795146195281365164038699950846301324885234647991028696976865654453589176654979471532728568654584853832451942604541277762968769668096005773808269554654223777842669744252783624353204706241260474033820066205249128951698965363063060147113186174940955847037737546264558522550113454323343976674465942821772849079414744009338396563220139607658666938479203550751423387865216958477950382374404742422201801193927156363602192156316862553999062168555158571930965, 27918178497257730517157921426911700020273454941020965128713261211421515389182921934361783203236897534625018034441370570707767155195892959542083963829220460179443608234893280765072804932463156832333366483706187776470388206226427365588208720769975526714120237679758768784031444177536933947436206195975231804244552186326552489850346956704019681075686321519597408749758435326140934015023151510900202175546735138547278566672560971596466947095201316942056497394374366582364044587462151970116227074091982192493110686408436593219617659239041011852289049099690948781293621057781655041625768135745282734759985248826539529281165338339560118404304950097816401040944314212432364706748205824723335037233062860762184871475634772638953849968193472955063245414680225279585135516454475736395046653392955962187815428396930262293991689657436098004457353767809702747596415596306981246402057467164939306330002821926567931659300686338989690752885806320864629670425301170184720615673342647720004482478893920329674655081841889717547489112810316589975188619854065943397153804592263480320809883150346366717000590777359269724119601127889214168704457332841614517461619818983943368652186851620359993902967972227494134944293497769143934283005762955244447797150549633120787408114832099915734435902326241624149943214814888739775260897140216147683219896454849304324547554370498274456192243000285550934168327343163953361061502271858875492168453146651289919936496626595398877967579504063282844306729147852281379174738129304331403285776185571910450691008672447573539924324102015714288280504058800491061099590849065660418999474703974093224497588623649982008144771248445135204688340893554380306776317110646795344513814887625413588124287599529732553508399103173735447679001034093448048952398265605380803846486541497745082391256645273726865797352966435948790997385215, 203890460196363984017921751612002082851060603978084504965804499152506974976782673650437707224821204584511499267540531825880332249778693059962007973351025723587987313881003907110414181427697119358647789292597361993463449746298662841270169954815208175913416195719043616028884274231634782525002946064774440629335409776950964454475913716635800035589293923668490502168220857341657470912798571051147015400919402824058261320382138070912577362245631253970581352725612270852244267954319891386925195334848264148929536970856255257468957759514272590397531850721821894547011198744452897139021455542487623337546504429697096535189008673238114520242073642107954429951108835063809329613975519845831782410130168865506772613268453528847269329894799539948533574501670334326530726760676669418619586086337029051734066600613635099478058366322717751405960066853199481579243147707891653496734836100073436898679427692935992604189341369593207976241711481156716007819211471709876463929884073388920218427840764923413331425258167619184509899489393175178474247032720332387822521510977826375105466900167396624588182448350030718484760571416074108553559497241475108154848791989374295735303053221292040234957183700043475692921442467340647923120759554666258600684875022417077508136300490693905320884946111488558368729088776300630820048767465205543854315528215868628900042817907836596689147443135556502890376320762466103862211741446039925128242289805946672148875863626420828649459554878784855190751922445221633419823576015704453049713511677680334326952644589757048819249939386091214307852061913091824750975031576676395243212332485442622233911579192687409114653622862826893932767509499664188893511503946135054869132453927827698192222477538310522985956963783826714121929091541172690978466981839476224939662039964177969165265335162935985460827361041049657940924308136119462221415364054422900537867590994813530168745593368638467908488910802255575599838152711724578014221466439543627624222105537343790357911491325304361094803094548251500268496435057871738611087216274835076017956776795794810775966633434908238623849513215, 180540180906289517345877938717136839292415542011782738965222535149279637784335744283813258878227712432663746435532071710073926908670877946022338817152075488023120607388546774173992436711610221715194490848517416265671771541115829917174310992678658814939657945120491905566928201819966591716577997788976641718080660725447704382240748871505904684806872733992692993405452618040153042032089091605840026102889194021588224006962809835283788909073194605487308019319420002518738478892748815424235498437842937309038737858728344268079139124817892564612805724680830644314295146537472637454493892852450037271931968600724142893147677090014068200380415385695751275706957878480627765270803511097428761116990152155413719578184811636571631314313852469257681845018234153289651490961446820366831518168810335190583217711184835263491511711556169711752324898947847179572699891658866759908177025583312806671468605553874320735680624529246424208113651694403540291340175488042292739623815720736490731015492409659542010558920354529404890145491117284809853068218912266836642138884565421797250873108073766373205183370098675724568871366491145143122677696630761141846330522896977178993268063585020683732915887614138048127635215]
def allOnes : Nat := 1090748135619415929462984244733782862448264161996232692431832786189721331849119295216264234525201987223957291796157025273109870820177184063610979765077554799078906298842192989538609825228048205159696851613591638196771886542609324560121290553901886301017900252535799917200010079600026535836800905297805880952350501630195475653911005312364560014847426035293551245843928918752768696279344088055617515694349945406677825140814900616105920256438504578013326493565836047242407382442812245131517757519164899226365743722432277368075027627883045206501792761700945699168497257879683851737049996900961120515655050115561271491492515342105748966629547032786321505730828430221664970324396138635251626409516168005427623435996308921691446181187406395310665404885739434832877428167407495370993511868756359970390117021823616749458620969857006263612082706715408157066575137281027022310927564910276759160520878304632411049364568754920967322982459184763427383790272448438018526977764941072715611580434690827459339991961414242741410599117426060556483763756314527611362658628383368621157993638020878537675545336789915694234433955666315070087213535470255670312004130725495834508357439653828936077080978550578912967907352780054935621561090795845172954115972927479877527738560008204118558930004777748727761853813510493840581861598652211605960308356405941821189714037868726219481498727603653616298856174822413033485438785324024751419417183012281078209729303537372804574372095228703622776363945290869806258422355148507571039619387449629866808188769662815778153079393179093143648340761738581819563002994422790754955061288818308430079648693232179158765918035565216157115402992120276155607873107937477466841528362987708699450152031231862594203085693838944657061346236704234026821102958954951197087076546186622796294536451620756509351018906023773821539532776208676978589731966330308893304665169436185078350641568336944530051437491311298834367265238595404904273455928723949525227184617404367854754610474377019768025576605881038077270707717942221977090385438585844095492116099852538903974655703943973086090930596963360767529964938414598185705963754561497355827813623833288906309004288017321424808663962671333528009232758350873059614118723781422101460198615747386855096896089189180441339558524822867541113212638793675567650340362970031930023397828465318547238244232028015189689660418822976000815437610652254270163595650875433851147123214227266605403581781469090806576468950587661997186505665475715792895

lemma lowPointWords_spec (p : Fin 13) :
    lowPointWords.getD p.val 0 = PackedColumns.col 13 p.val := by
  fin_cases p
  · exact Q3PackedColumnCache.col_13_0.symm
  · exact Q3PackedColumnCache.col_13_1.symm
  · exact Q3PackedColumnCache.col_13_2.symm
  · exact Q3PackedColumnCache.col_13_3.symm
  · exact Q3PackedColumnCache.col_13_4.symm
  · exact Q3PackedColumnCache.col_13_5.symm
  · exact Q3PackedColumnCache.col_13_6.symm
  · exact Q3PackedColumnCache.col_13_7.symm
  · exact Q3PackedColumnCache.col_13_8.symm
  · exact Q3PackedColumnCache.col_13_9.symm
  · exact Q3PackedColumnCache.col_13_10.symm
  · exact Q3PackedColumnCache.col_13_11.symm
  · exact Q3PackedColumnCache.col_13_12.symm

lemma low_point_bits (r : Fin 8192) (p : Fin 13) :
    (lowPointWords.getD p.val 0).testBit r.val = r.val.testBit p.val := by
  rw [lowPointWords_spec]
  exact PackedColumns.col_testBit_lt 13 p.val r.val p.isLt r.isLt

lemma allOnes_spec : allOnes = 2 ^ (2 ^ 13) - 1 := by
  rw [Q3PackedColumnCache.power_13]
  rfl

lemma allOnes_bits (r : Fin 8192) : allOnes.testBit r.val = true := by
  rw [allOnes_spec, Nat.testBit_two_pow_sub_one]
  simp [r.isLt]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma low_line_complement : ∀ l : Fin 21,
    lowLineWords.getD l.val 0 + PackedLineColumns.joinWords
      (List.ofFn (fun p : Fin 13 => if I (Fin.castAdd 8 p) l
        then lowPointWords.getD p.val 0 else 0)) + 1 = 2 ^ (2 ^ 13) := by
  rw [Q3PackedColumnCache.power_13]
  decide +kernel

lemma low_line_bits (r : Fin 8192) (l : Fin 21) :
    (lowLineWords.getD l.val 0).testBit r.val =
      decide (∀ p : Fin 13, I (Fin.castAdd 8 p) l → r.val.testBit p.val = false) := by
  exact PackedLineArithmetic.line_bits (fun p : Fin 13 => I (Fin.castAdd 8 p))
    (fun p => lowPointWords.getD p.val 0) r l _ (low_line_complement l) (low_point_bits r)

def data (h : Fin 256) (i : Fin 42) : Nat :=
  Fin.addCases (motive := fun _ => Nat)
    (fun p : Fin 21 => Fin.addCases (motive := fun _ => Nat)
      (fun p : Fin 13 => lowPointWords.getD p.val 0)
      (fun p : Fin 8 => if h.val.testBit p.val then allOnes else 0) p)
    (fun l : Fin 21 => if ∀ p : Fin 8,
        I (Fin.natAdd 13 p) l → h.val.testBit p.val = false
      then lowLineWords.getD l.val 0 else 0) i

def words (h : Fin 256) : List Nat := List.ofFn (data h)

lemma words_length (h : Fin 256) : (words h).length = 42 := by simp [words]

lemma words_getD (h : Fin 256) (i : Fin 42) : (words h).getD i.val 0 = data h i := by
  simp only [words, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
    i.isLt, dite_eq_left, Option.getD_some]

lemma low_lookup (h : Fin 256) (p : Fin 13) :
    (words h).getD p.val 0 = lowPointWords.getD p.val 0 := by
  simpa [data] using words_getD h (Fin.castAdd 21 (Fin.castAdd 8 p))

lemma high_lookup (h : Fin 256) (p : Fin 8) :
    (words h).getD (13 + p.val) 0 = if h.val.testBit p.val then allOnes else 0 := by
  simpa [data] using words_getD h (Fin.castAdd 21 (Fin.natAdd 13 p))

lemma line_lookup (h : Fin 256) (l : Fin 21) :
    (words h).getD (21 + l.val) 0 = if ∀ p : Fin 8,
        I (Fin.natAdd 13 p) l → h.val.testBit p.val = false
      then lowLineWords.getD l.val 0 else 0 := by
  have hw := words_getD h (Fin.natAdd 21 l)
  simp only [data, Fin.addCases_right] at hw
  exact hw

lemma low_bits (h : Fin 256) (r : Fin 8192) (p : Fin 13) :
    ((words h).getD p.val 0).testBit r.val = r.val.testBit p.val := by
  rw [low_lookup]
  exact low_point_bits r p

lemma high_bits (h : Fin 256) (r : Fin 8192) (p : Fin 8) :
    ((words h).getD (13 + p.val) 0).testBit r.val = h.val.testBit p.val := by
  rw [high_lookup]
  cases h.val.testBit p.val <;> simp [allOnes_bits r]

lemma line_bits (h : Fin 256) (r : Fin 8192) (l : Fin 21) :
    ((words h).getD (21 + l.val) 0).testBit r.val = decide
      ((∀ p : Fin 13, I (Fin.castAdd 8 p) l → r.val.testBit p.val = false) ∧
        (∀ p : Fin 8, I (Fin.natAdd 13 p) l → h.val.testBit p.val = false)) := by
  rw [line_lookup]
  split
  · rename_i hh
    rw [low_line_bits r l]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact (and_iff_left hh).symm
  · rename_i hh
    simp [hh]

lemma negative_of_chunks (C : Circuit) (hAO : IsAO2 42 C)
    (hneg : ∀ h : Fin 256, PackedEval.eval C (words h) = 0) :
    ∀ P : Finset (Fin 21), circuitFun 42 C (liftInput (independentInput I P)) = false := by
  exact ChunkedBoundary.independent_false_of_chunks (a := 13) (b := 8)
    I C hAO words words_length low_bits high_bits line_bits hneg

lemma exact_of_chunks (C : Circuit) (hAO : IsAO2 42 C)
    (hpos : PackedEval.eval C pairWords = incidenceMask)
    (hneg : ∀ h : Fin 256, PackedEval.eval C (words h) = 0) :
    ∀ z : Fin 42 → Bool, circuitFun 42 C z = decide (∃ p l : Fin 21,
      I p l ∧ z (Fin.castAdd 21 p) = true ∧ z (Fin.natAdd 21 l) = true) := by
  exact ao2_exact_certificate I C hAO (Q4BackendBench.positive_of_packed C hAO hpos)
    (fun P _ => negative_of_chunks C hAO hneg P)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_0 : PackedEval.eval canonicalC (words 0) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_1 : PackedEval.eval canonicalC (words 1) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_2 : PackedEval.eval canonicalC (words 2) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_3 : PackedEval.eval canonicalC (words 3) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_4 : PackedEval.eval canonicalC (words 4) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_5 : PackedEval.eval canonicalC (words 5) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_6 : PackedEval.eval canonicalC (words 6) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_7 : PackedEval.eval canonicalC (words 7) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_8 : PackedEval.eval canonicalC (words 8) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_9 : PackedEval.eval canonicalC (words 9) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_10 : PackedEval.eval canonicalC (words 10) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_11 : PackedEval.eval canonicalC (words 11) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_12 : PackedEval.eval canonicalC (words 12) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_13 : PackedEval.eval canonicalC (words 13) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_14 : PackedEval.eval canonicalC (words 14) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_15 : PackedEval.eval canonicalC (words 15) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_16 : PackedEval.eval canonicalC (words 16) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_17 : PackedEval.eval canonicalC (words 17) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_18 : PackedEval.eval canonicalC (words 18) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_19 : PackedEval.eval canonicalC (words 19) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_20 : PackedEval.eval canonicalC (words 20) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_21 : PackedEval.eval canonicalC (words 21) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_22 : PackedEval.eval canonicalC (words 22) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_23 : PackedEval.eval canonicalC (words 23) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_24 : PackedEval.eval canonicalC (words 24) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_25 : PackedEval.eval canonicalC (words 25) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_26 : PackedEval.eval canonicalC (words 26) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_27 : PackedEval.eval canonicalC (words 27) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_28 : PackedEval.eval canonicalC (words 28) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_29 : PackedEval.eval canonicalC (words 29) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_30 : PackedEval.eval canonicalC (words 30) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_31 : PackedEval.eval canonicalC (words 31) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_32 : PackedEval.eval canonicalC (words 32) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_33 : PackedEval.eval canonicalC (words 33) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_34 : PackedEval.eval canonicalC (words 34) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_35 : PackedEval.eval canonicalC (words 35) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_36 : PackedEval.eval canonicalC (words 36) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_37 : PackedEval.eval canonicalC (words 37) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_38 : PackedEval.eval canonicalC (words 38) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_39 : PackedEval.eval canonicalC (words 39) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_40 : PackedEval.eval canonicalC (words 40) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_41 : PackedEval.eval canonicalC (words 41) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_42 : PackedEval.eval canonicalC (words 42) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_43 : PackedEval.eval canonicalC (words 43) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_44 : PackedEval.eval canonicalC (words 44) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_45 : PackedEval.eval canonicalC (words 45) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_46 : PackedEval.eval canonicalC (words 46) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_47 : PackedEval.eval canonicalC (words 47) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_48 : PackedEval.eval canonicalC (words 48) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_49 : PackedEval.eval canonicalC (words 49) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_50 : PackedEval.eval canonicalC (words 50) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_51 : PackedEval.eval canonicalC (words 51) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_52 : PackedEval.eval canonicalC (words 52) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_53 : PackedEval.eval canonicalC (words 53) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_54 : PackedEval.eval canonicalC (words 54) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_55 : PackedEval.eval canonicalC (words 55) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_56 : PackedEval.eval canonicalC (words 56) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_57 : PackedEval.eval canonicalC (words 57) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_58 : PackedEval.eval canonicalC (words 58) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_59 : PackedEval.eval canonicalC (words 59) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_60 : PackedEval.eval canonicalC (words 60) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_61 : PackedEval.eval canonicalC (words 61) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_62 : PackedEval.eval canonicalC (words 62) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_63 : PackedEval.eval canonicalC (words 63) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_64 : PackedEval.eval canonicalC (words 64) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_65 : PackedEval.eval canonicalC (words 65) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_66 : PackedEval.eval canonicalC (words 66) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_67 : PackedEval.eval canonicalC (words 67) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_68 : PackedEval.eval canonicalC (words 68) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_69 : PackedEval.eval canonicalC (words 69) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_70 : PackedEval.eval canonicalC (words 70) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_71 : PackedEval.eval canonicalC (words 71) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_72 : PackedEval.eval canonicalC (words 72) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_73 : PackedEval.eval canonicalC (words 73) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_74 : PackedEval.eval canonicalC (words 74) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_75 : PackedEval.eval canonicalC (words 75) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_76 : PackedEval.eval canonicalC (words 76) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_77 : PackedEval.eval canonicalC (words 77) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_78 : PackedEval.eval canonicalC (words 78) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_79 : PackedEval.eval canonicalC (words 79) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_80 : PackedEval.eval canonicalC (words 80) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_81 : PackedEval.eval canonicalC (words 81) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_82 : PackedEval.eval canonicalC (words 82) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_83 : PackedEval.eval canonicalC (words 83) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_84 : PackedEval.eval canonicalC (words 84) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_85 : PackedEval.eval canonicalC (words 85) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_86 : PackedEval.eval canonicalC (words 86) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_87 : PackedEval.eval canonicalC (words 87) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_88 : PackedEval.eval canonicalC (words 88) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_89 : PackedEval.eval canonicalC (words 89) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_90 : PackedEval.eval canonicalC (words 90) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_91 : PackedEval.eval canonicalC (words 91) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_92 : PackedEval.eval canonicalC (words 92) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_93 : PackedEval.eval canonicalC (words 93) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_94 : PackedEval.eval canonicalC (words 94) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_95 : PackedEval.eval canonicalC (words 95) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_96 : PackedEval.eval canonicalC (words 96) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_97 : PackedEval.eval canonicalC (words 97) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_98 : PackedEval.eval canonicalC (words 98) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_99 : PackedEval.eval canonicalC (words 99) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_100 : PackedEval.eval canonicalC (words 100) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_101 : PackedEval.eval canonicalC (words 101) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_102 : PackedEval.eval canonicalC (words 102) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_103 : PackedEval.eval canonicalC (words 103) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_104 : PackedEval.eval canonicalC (words 104) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_105 : PackedEval.eval canonicalC (words 105) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_106 : PackedEval.eval canonicalC (words 106) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_107 : PackedEval.eval canonicalC (words 107) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_108 : PackedEval.eval canonicalC (words 108) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_109 : PackedEval.eval canonicalC (words 109) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_110 : PackedEval.eval canonicalC (words 110) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_111 : PackedEval.eval canonicalC (words 111) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_112 : PackedEval.eval canonicalC (words 112) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_113 : PackedEval.eval canonicalC (words 113) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_114 : PackedEval.eval canonicalC (words 114) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_115 : PackedEval.eval canonicalC (words 115) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_116 : PackedEval.eval canonicalC (words 116) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_117 : PackedEval.eval canonicalC (words 117) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_118 : PackedEval.eval canonicalC (words 118) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_119 : PackedEval.eval canonicalC (words 119) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_120 : PackedEval.eval canonicalC (words 120) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_121 : PackedEval.eval canonicalC (words 121) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_122 : PackedEval.eval canonicalC (words 122) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_123 : PackedEval.eval canonicalC (words 123) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_124 : PackedEval.eval canonicalC (words 124) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_125 : PackedEval.eval canonicalC (words 125) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_126 : PackedEval.eval canonicalC (words 126) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_127 : PackedEval.eval canonicalC (words 127) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_128 : PackedEval.eval canonicalC (words 128) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_129 : PackedEval.eval canonicalC (words 129) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_130 : PackedEval.eval canonicalC (words 130) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_131 : PackedEval.eval canonicalC (words 131) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_132 : PackedEval.eval canonicalC (words 132) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_133 : PackedEval.eval canonicalC (words 133) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_134 : PackedEval.eval canonicalC (words 134) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_135 : PackedEval.eval canonicalC (words 135) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_136 : PackedEval.eval canonicalC (words 136) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_137 : PackedEval.eval canonicalC (words 137) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_138 : PackedEval.eval canonicalC (words 138) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_139 : PackedEval.eval canonicalC (words 139) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_140 : PackedEval.eval canonicalC (words 140) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_141 : PackedEval.eval canonicalC (words 141) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_142 : PackedEval.eval canonicalC (words 142) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_143 : PackedEval.eval canonicalC (words 143) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_144 : PackedEval.eval canonicalC (words 144) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_145 : PackedEval.eval canonicalC (words 145) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_146 : PackedEval.eval canonicalC (words 146) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_147 : PackedEval.eval canonicalC (words 147) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_148 : PackedEval.eval canonicalC (words 148) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_149 : PackedEval.eval canonicalC (words 149) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_150 : PackedEval.eval canonicalC (words 150) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_151 : PackedEval.eval canonicalC (words 151) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_152 : PackedEval.eval canonicalC (words 152) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_153 : PackedEval.eval canonicalC (words 153) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_154 : PackedEval.eval canonicalC (words 154) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_155 : PackedEval.eval canonicalC (words 155) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_156 : PackedEval.eval canonicalC (words 156) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_157 : PackedEval.eval canonicalC (words 157) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_158 : PackedEval.eval canonicalC (words 158) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_159 : PackedEval.eval canonicalC (words 159) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_160 : PackedEval.eval canonicalC (words 160) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_161 : PackedEval.eval canonicalC (words 161) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_162 : PackedEval.eval canonicalC (words 162) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_163 : PackedEval.eval canonicalC (words 163) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_164 : PackedEval.eval canonicalC (words 164) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_165 : PackedEval.eval canonicalC (words 165) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_166 : PackedEval.eval canonicalC (words 166) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_167 : PackedEval.eval canonicalC (words 167) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_168 : PackedEval.eval canonicalC (words 168) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_169 : PackedEval.eval canonicalC (words 169) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_170 : PackedEval.eval canonicalC (words 170) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_171 : PackedEval.eval canonicalC (words 171) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_172 : PackedEval.eval canonicalC (words 172) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_173 : PackedEval.eval canonicalC (words 173) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_174 : PackedEval.eval canonicalC (words 174) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_175 : PackedEval.eval canonicalC (words 175) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_176 : PackedEval.eval canonicalC (words 176) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_177 : PackedEval.eval canonicalC (words 177) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_178 : PackedEval.eval canonicalC (words 178) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_179 : PackedEval.eval canonicalC (words 179) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_180 : PackedEval.eval canonicalC (words 180) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_181 : PackedEval.eval canonicalC (words 181) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_182 : PackedEval.eval canonicalC (words 182) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_183 : PackedEval.eval canonicalC (words 183) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_184 : PackedEval.eval canonicalC (words 184) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_185 : PackedEval.eval canonicalC (words 185) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_186 : PackedEval.eval canonicalC (words 186) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_187 : PackedEval.eval canonicalC (words 187) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_188 : PackedEval.eval canonicalC (words 188) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_189 : PackedEval.eval canonicalC (words 189) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_190 : PackedEval.eval canonicalC (words 190) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_191 : PackedEval.eval canonicalC (words 191) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_192 : PackedEval.eval canonicalC (words 192) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_193 : PackedEval.eval canonicalC (words 193) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_194 : PackedEval.eval canonicalC (words 194) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_195 : PackedEval.eval canonicalC (words 195) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_196 : PackedEval.eval canonicalC (words 196) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_197 : PackedEval.eval canonicalC (words 197) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_198 : PackedEval.eval canonicalC (words 198) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_199 : PackedEval.eval canonicalC (words 199) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_200 : PackedEval.eval canonicalC (words 200) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_201 : PackedEval.eval canonicalC (words 201) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_202 : PackedEval.eval canonicalC (words 202) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_203 : PackedEval.eval canonicalC (words 203) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_204 : PackedEval.eval canonicalC (words 204) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_205 : PackedEval.eval canonicalC (words 205) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_206 : PackedEval.eval canonicalC (words 206) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_207 : PackedEval.eval canonicalC (words 207) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_208 : PackedEval.eval canonicalC (words 208) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_209 : PackedEval.eval canonicalC (words 209) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_210 : PackedEval.eval canonicalC (words 210) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_211 : PackedEval.eval canonicalC (words 211) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_212 : PackedEval.eval canonicalC (words 212) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_213 : PackedEval.eval canonicalC (words 213) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_214 : PackedEval.eval canonicalC (words 214) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_215 : PackedEval.eval canonicalC (words 215) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_216 : PackedEval.eval canonicalC (words 216) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_217 : PackedEval.eval canonicalC (words 217) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_218 : PackedEval.eval canonicalC (words 218) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_219 : PackedEval.eval canonicalC (words 219) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_220 : PackedEval.eval canonicalC (words 220) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_221 : PackedEval.eval canonicalC (words 221) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_222 : PackedEval.eval canonicalC (words 222) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_223 : PackedEval.eval canonicalC (words 223) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_224 : PackedEval.eval canonicalC (words 224) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_225 : PackedEval.eval canonicalC (words 225) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_226 : PackedEval.eval canonicalC (words 226) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_227 : PackedEval.eval canonicalC (words 227) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_228 : PackedEval.eval canonicalC (words 228) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_229 : PackedEval.eval canonicalC (words 229) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_230 : PackedEval.eval canonicalC (words 230) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_231 : PackedEval.eval canonicalC (words 231) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_232 : PackedEval.eval canonicalC (words 232) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_233 : PackedEval.eval canonicalC (words 233) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_234 : PackedEval.eval canonicalC (words 234) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_235 : PackedEval.eval canonicalC (words 235) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_236 : PackedEval.eval canonicalC (words 236) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_237 : PackedEval.eval canonicalC (words 237) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_238 : PackedEval.eval canonicalC (words 238) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_239 : PackedEval.eval canonicalC (words 239) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_240 : PackedEval.eval canonicalC (words 240) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_241 : PackedEval.eval canonicalC (words 241) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_242 : PackedEval.eval canonicalC (words 242) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_243 : PackedEval.eval canonicalC (words 243) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_244 : PackedEval.eval canonicalC (words 244) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_245 : PackedEval.eval canonicalC (words 245) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_246 : PackedEval.eval canonicalC (words 246) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_247 : PackedEval.eval canonicalC (words 247) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_248 : PackedEval.eval canonicalC (words 248) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_249 : PackedEval.eval canonicalC (words 249) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_250 : PackedEval.eval canonicalC (words 250) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_251 : PackedEval.eval canonicalC (words 251) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_252 : PackedEval.eval canonicalC (words 252) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_253 : PackedEval.eval canonicalC (words 253) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_254 : PackedEval.eval canonicalC (words 254) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma chunk_zero_255 : PackedEval.eval canonicalC (words 255) = 0 := by decide +kernel

lemma all_chunks_zero : ∀ h : Fin 256, PackedEval.eval canonicalC (words h) = 0 := by
  intro h
  fin_cases h
  · exact chunk_zero_0
  · exact chunk_zero_1
  · exact chunk_zero_2
  · exact chunk_zero_3
  · exact chunk_zero_4
  · exact chunk_zero_5
  · exact chunk_zero_6
  · exact chunk_zero_7
  · exact chunk_zero_8
  · exact chunk_zero_9
  · exact chunk_zero_10
  · exact chunk_zero_11
  · exact chunk_zero_12
  · exact chunk_zero_13
  · exact chunk_zero_14
  · exact chunk_zero_15
  · exact chunk_zero_16
  · exact chunk_zero_17
  · exact chunk_zero_18
  · exact chunk_zero_19
  · exact chunk_zero_20
  · exact chunk_zero_21
  · exact chunk_zero_22
  · exact chunk_zero_23
  · exact chunk_zero_24
  · exact chunk_zero_25
  · exact chunk_zero_26
  · exact chunk_zero_27
  · exact chunk_zero_28
  · exact chunk_zero_29
  · exact chunk_zero_30
  · exact chunk_zero_31
  · exact chunk_zero_32
  · exact chunk_zero_33
  · exact chunk_zero_34
  · exact chunk_zero_35
  · exact chunk_zero_36
  · exact chunk_zero_37
  · exact chunk_zero_38
  · exact chunk_zero_39
  · exact chunk_zero_40
  · exact chunk_zero_41
  · exact chunk_zero_42
  · exact chunk_zero_43
  · exact chunk_zero_44
  · exact chunk_zero_45
  · exact chunk_zero_46
  · exact chunk_zero_47
  · exact chunk_zero_48
  · exact chunk_zero_49
  · exact chunk_zero_50
  · exact chunk_zero_51
  · exact chunk_zero_52
  · exact chunk_zero_53
  · exact chunk_zero_54
  · exact chunk_zero_55
  · exact chunk_zero_56
  · exact chunk_zero_57
  · exact chunk_zero_58
  · exact chunk_zero_59
  · exact chunk_zero_60
  · exact chunk_zero_61
  · exact chunk_zero_62
  · exact chunk_zero_63
  · exact chunk_zero_64
  · exact chunk_zero_65
  · exact chunk_zero_66
  · exact chunk_zero_67
  · exact chunk_zero_68
  · exact chunk_zero_69
  · exact chunk_zero_70
  · exact chunk_zero_71
  · exact chunk_zero_72
  · exact chunk_zero_73
  · exact chunk_zero_74
  · exact chunk_zero_75
  · exact chunk_zero_76
  · exact chunk_zero_77
  · exact chunk_zero_78
  · exact chunk_zero_79
  · exact chunk_zero_80
  · exact chunk_zero_81
  · exact chunk_zero_82
  · exact chunk_zero_83
  · exact chunk_zero_84
  · exact chunk_zero_85
  · exact chunk_zero_86
  · exact chunk_zero_87
  · exact chunk_zero_88
  · exact chunk_zero_89
  · exact chunk_zero_90
  · exact chunk_zero_91
  · exact chunk_zero_92
  · exact chunk_zero_93
  · exact chunk_zero_94
  · exact chunk_zero_95
  · exact chunk_zero_96
  · exact chunk_zero_97
  · exact chunk_zero_98
  · exact chunk_zero_99
  · exact chunk_zero_100
  · exact chunk_zero_101
  · exact chunk_zero_102
  · exact chunk_zero_103
  · exact chunk_zero_104
  · exact chunk_zero_105
  · exact chunk_zero_106
  · exact chunk_zero_107
  · exact chunk_zero_108
  · exact chunk_zero_109
  · exact chunk_zero_110
  · exact chunk_zero_111
  · exact chunk_zero_112
  · exact chunk_zero_113
  · exact chunk_zero_114
  · exact chunk_zero_115
  · exact chunk_zero_116
  · exact chunk_zero_117
  · exact chunk_zero_118
  · exact chunk_zero_119
  · exact chunk_zero_120
  · exact chunk_zero_121
  · exact chunk_zero_122
  · exact chunk_zero_123
  · exact chunk_zero_124
  · exact chunk_zero_125
  · exact chunk_zero_126
  · exact chunk_zero_127
  · exact chunk_zero_128
  · exact chunk_zero_129
  · exact chunk_zero_130
  · exact chunk_zero_131
  · exact chunk_zero_132
  · exact chunk_zero_133
  · exact chunk_zero_134
  · exact chunk_zero_135
  · exact chunk_zero_136
  · exact chunk_zero_137
  · exact chunk_zero_138
  · exact chunk_zero_139
  · exact chunk_zero_140
  · exact chunk_zero_141
  · exact chunk_zero_142
  · exact chunk_zero_143
  · exact chunk_zero_144
  · exact chunk_zero_145
  · exact chunk_zero_146
  · exact chunk_zero_147
  · exact chunk_zero_148
  · exact chunk_zero_149
  · exact chunk_zero_150
  · exact chunk_zero_151
  · exact chunk_zero_152
  · exact chunk_zero_153
  · exact chunk_zero_154
  · exact chunk_zero_155
  · exact chunk_zero_156
  · exact chunk_zero_157
  · exact chunk_zero_158
  · exact chunk_zero_159
  · exact chunk_zero_160
  · exact chunk_zero_161
  · exact chunk_zero_162
  · exact chunk_zero_163
  · exact chunk_zero_164
  · exact chunk_zero_165
  · exact chunk_zero_166
  · exact chunk_zero_167
  · exact chunk_zero_168
  · exact chunk_zero_169
  · exact chunk_zero_170
  · exact chunk_zero_171
  · exact chunk_zero_172
  · exact chunk_zero_173
  · exact chunk_zero_174
  · exact chunk_zero_175
  · exact chunk_zero_176
  · exact chunk_zero_177
  · exact chunk_zero_178
  · exact chunk_zero_179
  · exact chunk_zero_180
  · exact chunk_zero_181
  · exact chunk_zero_182
  · exact chunk_zero_183
  · exact chunk_zero_184
  · exact chunk_zero_185
  · exact chunk_zero_186
  · exact chunk_zero_187
  · exact chunk_zero_188
  · exact chunk_zero_189
  · exact chunk_zero_190
  · exact chunk_zero_191
  · exact chunk_zero_192
  · exact chunk_zero_193
  · exact chunk_zero_194
  · exact chunk_zero_195
  · exact chunk_zero_196
  · exact chunk_zero_197
  · exact chunk_zero_198
  · exact chunk_zero_199
  · exact chunk_zero_200
  · exact chunk_zero_201
  · exact chunk_zero_202
  · exact chunk_zero_203
  · exact chunk_zero_204
  · exact chunk_zero_205
  · exact chunk_zero_206
  · exact chunk_zero_207
  · exact chunk_zero_208
  · exact chunk_zero_209
  · exact chunk_zero_210
  · exact chunk_zero_211
  · exact chunk_zero_212
  · exact chunk_zero_213
  · exact chunk_zero_214
  · exact chunk_zero_215
  · exact chunk_zero_216
  · exact chunk_zero_217
  · exact chunk_zero_218
  · exact chunk_zero_219
  · exact chunk_zero_220
  · exact chunk_zero_221
  · exact chunk_zero_222
  · exact chunk_zero_223
  · exact chunk_zero_224
  · exact chunk_zero_225
  · exact chunk_zero_226
  · exact chunk_zero_227
  · exact chunk_zero_228
  · exact chunk_zero_229
  · exact chunk_zero_230
  · exact chunk_zero_231
  · exact chunk_zero_232
  · exact chunk_zero_233
  · exact chunk_zero_234
  · exact chunk_zero_235
  · exact chunk_zero_236
  · exact chunk_zero_237
  · exact chunk_zero_238
  · exact chunk_zero_239
  · exact chunk_zero_240
  · exact chunk_zero_241
  · exact chunk_zero_242
  · exact chunk_zero_243
  · exact chunk_zero_244
  · exact chunk_zero_245
  · exact chunk_zero_246
  · exact chunk_zero_247
  · exact chunk_zero_248
  · exact chunk_zero_249
  · exact chunk_zero_250
  · exact chunk_zero_251
  · exact chunk_zero_252
  · exact chunk_zero_253
  · exact chunk_zero_254
  · exact chunk_zero_255

lemma canonical_exact : ∀ z : Fin 42 → Bool, circuitFun 42 canonicalC z =
    decide (∃ p l : Fin 21, I p l ∧ z (Fin.castAdd 21 p) = true ∧ z (Fin.natAdd 21 l) = true) :=
  exact_of_chunks canonicalC Q4BackendBench.checks.1 Q4BackendBench.checks.2.2 all_chunks_zero

end Q4ChunkedBackend

end PEqualNP.Outside.L_meta_2583
