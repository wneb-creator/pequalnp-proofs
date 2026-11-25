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
namespace PackedBoundary
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.Outside.L_meta_2583.ReducedCheck
open PEqualNP.Outside.L_meta_2583.CircuitCheckWrapper
lemma input_bits {n m : ℕ} (I : Fin n → Fin m → Prop) [DecidableRel I]
    (w : List ℕ) (hlen : w.length = n + m)
    (hpoint : ∀ (r : Fin (2 ^ n)) (p : Fin n),
      (w.getD p.val 0).testBit r.val = r.val.testBit p.val)
    (hline : ∀ (r : Fin (2 ^ n)) (l : Fin m),
      (w.getD (n + l.val) 0).testBit r.val =
        decide (∀ p : Fin n, I p l → r.val.testBit p.val = false))
    (P : Finset (Fin n)) :
    w.map (fun a => a.testBit (PackedInputCode.code (fun p => decide (p ∈ P))).val) =
      List.ofFn (liftInput (independentInput I P)) := by
  let r := PackedInputCode.code (fun p => decide (p ∈ P))
  have hwire : ∀ i : Fin (n + m), (w.getD i.val 0).testBit r.val =
      liftInput (independentInput I P) i := by
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro p
      simpa [r, liftInput, independentInput] using
        (hpoint r p).trans (PackedInputCode.code_bit (fun p => decide (p ∈ P)) p)
    · intro l
      have hwline : (w.getD (n + l.val) 0).testBit r.val =
          decide (l ∈ avoidingRight I P) := by
        rw [hline r l]
        congr 1
        apply propext
        rw [mem_avoidingRight]
        constructor
        · intro h p hp hI
          have hf := h p hI
          simpa [r, PackedInputCode.code_bit, hp] using hf
        · intro h p hI
          have hp : p ∉ P := fun hp => h p hp hI
          simp [r, PackedInputCode.code_bit, hp]
      simpa [liftInput, independentInput] using hwline
  apply List.ext_getElem
  · simpa using hlen
  · intro i hi hj
    have hwi : i < w.length := by simpa using hi
    have hib : i < n + m := by simpa [hlen] using hwi
    simpa [List.getD_eq_getElem?_getD, hwi] using hwire ⟨i, hib⟩
lemma independent_false_of_packed_zero {n m : ℕ} (I : Fin n → Fin m → Prop)
    [DecidableRel I] (C : Circuit) (hAO : IsAO2 (n + m) C)
    (w : List ℕ) (hlen : w.length = n + m)
    (hpoint : ∀ (r : Fin (2 ^ n)) (p : Fin n),
      (w.getD p.val 0).testBit r.val = r.val.testBit p.val)
    (hline : ∀ (r : Fin (2 ^ n)) (l : Fin m),
      (w.getD (n + l.val) 0).testBit r.val =
        decide (∀ p : Fin n, I p l → r.val.testBit p.val = false))
    (hzero : PackedEval.eval C w = 0) :
    ∀ P : Finset (Fin n), circuitFun (n + m) C (liftInput (independentInput I P)) = false := by
  intro P
  have h := PackedEval.eval_testBit_of_isAO2 (n + m) C w
    (PackedInputCode.code (fun p => decide (p ∈ P))).val hAO
  rw [hzero, input_bits I w hlen hpoint hline P] at h
  simpa [circuitFun] using h.symm
end PackedBoundary
namespace Q3PackedColumnCache
def pointWords : List Nat := [727165423746277286308656163155855241632176107997488461621221857459814221232746196810842823016801324815971527864104683515406580546784789375740653176718369866052604199228128659692406550152032136773131234409061092131181257695072883040080860369267924200678600168357199944800006719733351023891200603531870587301567001086796983769274003541576373343231617356862367497229285945835179130852896058703745010462899963604451883427209933744070613504292336385342217662377224031494938254961874830087678505012776599484243829148288184912050018418588696804334528507800630466112331505253122567824699997933974080343770033410374180994328343561403832644419698021857547670487218953481109980216264092423501084273010778670285082290664205947794297454124937596873776936590492956555251618778271663580662341245837573313593411347882411166305747313238004175741388471143605438044383424854018014873951709940184506107013918869754940699576379169947311548654972789842284922526848298958679017985176627381810407720289793884972893327974276161827607066078284040370989175837543018407575105752255579080771995758680585691783696891193277129489622637110876713391475690313503780208002753816997223005571626435885957384720652367052608645271568520036623747707393863896781969410648618319918351825706672136079039286669851832485174569209006995893721241065768141070640205570937294547459809358579150812987665818402435744199237449881608688990292523549349834279611455341520718806486202358248536382914730152469081850909296860579870838948236765671714026412924966419911205459179775210518768719595452728762432227174492387879708668662948527169970040859212205620053099128821452772510612023710144104743601994746850770405248738624984977894352241991805799633434687487908396135390462559296438040897491136156017880735305969967464724717697457748530863024301080504339567345937349182547693021850805784652393154644220205928869776779624123385567094378891296353367624994207532556244843492396936602848970619149299683484789744936245236503073649584679845350384403920692051513805145294814651393590292390562730328077399901692602649770469295982057393953731308907178353309958943065457137309169707664903885209082555525937539336192011547616539109308447555685339488505567248706409412482520948067640132410498257903397930726126120294226372349881911694075475092529117045100226908646687953348931885643545698158829488018676793126440279215317333876958407101502846775730433916955900764748809484844403602387854312727204384312633725107998124337110317143861930, 872598508495532743570387395787026289958611329596986153945466228951777065479295436173011387620161589779165833436925620218487896656141747250888783812062043839263125039073754391630887860182438564127757481290873310557417509234087459648097032443121509040814320202028639933760008063680021228669440724238244704761880401304156380523128804249891648011877940828234840996675143135002214957023475270444494012555479956325342260112651920492884736205150803662410661194852668837793925905954249796105214206015331919381092594977945821894460022102306436165201434209360756559334797806303747081389639997520768896412524040092449017193194012273684599173303637626229057204584662744177331976259516910908201301127612934404342098748797047137353156944949925116248532323908591547866301942533925996296794809495005087976312093617458893399566896775885605010889666165372326525653260109824821617848742051928221407328416702643705928839491655003936773858385967347810741907032217958750414821582211952858172489264347752661967471993569131394193128479293940848445187011005051622089090126902706694896926394910416702830140436269431932555387547164533052056069770828376204536249603304580396667606685951723063148861664782840463130374325882224043948497248872636676138363292778341983902022190848006563294847144003822198982209483050808395072465489278921769284768246685124753456951771230294980975585198982082922893039084939857930426788351028259219801135533746409824862567783442829898243659497676182962898221091156232695845006737884118806056831695509959703893446551015730252622522463514543274514918672609390865455650402395538232603964049031054646744063718954585743327012734428452172925692322393696220924486298486349981973473222690390166959560121624985490075362468555071155725649076989363387221456882367163960957669661236949298237035629161296605207480815124819019057231626220966941582871785573064247114643732135548948062680513254669555624041149993049039067493812190876323923418764742979159620181747693923494283803688379501615814420461284704830461816566174353777581672308350868675276393692879882031123179724563155178468872744477570688614023971950731678548564771003649197884662250899066631125047203430413857139846931170137066822407386206680698447691294979025137681168158892597909484077516871351344353071646819858294032890570111034940454120272290376025544018718262772254837790595385622412151751728335058380800652350088521803416130876520700347080917698571381813284322865425175272645261175160470129597749204532380572634316, 1026586480582979698318102818572972105833660387761160181112313210531502429975641689615307514847248929151959804043441906139397525477813820295163275073014169222662500045969122813683397482567574781326773507401027424185197069687161717233055332286025304753899200237680752863247068310211789680787577322633229064425741648593125153556622122646931350602209342150864518819617815452943782302380559141699404720653505830970990894250178729991629101417824474896953719052767845691522265771710882113064957889429802258095403052915230378699364731885066395488472275540424419481570350360357349507517223526495022231073557694226410608462581190910217175498004279560269479064217250287267449383834725777539060354267779922828637763233878878985121361111705794254410038028127754762195649344157559995643288011170594221148602463079363403999490466795159535306929019018085090030180306011558613668057343590503789890974607885463183445693519594122278557480454079232718519890626138775000488025390837591597849987369820885484667614110081331051991915857992871586406102365888296025987164855179654935172854582247549062153106395611096391241632408428862414183611495092207299454411298005388701961890218766733015469249017391577015447499206920263581115879116320749030751015638562755275178849636291772427405702522357437881155540568295068700085253516798731493276197937276617357008178554388582330559511998802450497521222452870421094619751001209716729177806510289893911603020921697446939110187644324921132821436577830861995111772632804845654184507877070540828109937118842035591320614662958286205311669026599283371124294591053574391298781234154181937345957316417159698031779687562884909324343908698466142264101527630999978792321438459282549364188378382335870676897021829495477324293031752192220260537508667251718773729013219940350867100740189760712008800958970375316537919560259961107744555041850663820134874978982998762426682956770199477204754294109469457726463308459854498733433840874093128964919703169321757980945515740590136252259366217299800543313607263945620684320362765727853266345521035155330733152617133123739375144405267730221898851731706743151233605612945469644570190883410666624852996709918133949576290507258984784496949866125506704056107405857676632566080186932468128804797078672178052180084290376303875332812435424746988769553261518089441816492609720908535103283053394849896649119680394186330353708647162966827548389266494941584801079645378096250922732782853147379582660206071141328938528475920447732510960, 1086503979449690575651844228217308999170255352027375755885405421262913077639589648153165930110707037857327107781385986264265085330604510195659186069493595441884046741259149437050132744196032453388647447521709958670714408384855980884790079306610439272609270290463676182113628717422594525969731641074857219936971705904007944620238199844223063672377202587685405132046870829574742358939735745300537291897873875580192697416531574154564652084234463704168916662851572093751191789515019201376142202042436631135990779739076509751856836858902955536437583451344132680883794933919062513792547856835198625883298415679313951368957525010035298581545385371180149048510085907146872499622744791792312904127767077857546582099669475034836615651299517654472880714594355234697340940120063497334530502094947969464668754698781501509188353962192193009668066820697060265404837490832462714831118508237474125856394337922124113730106340860932947994877469071204036615759960104280672151386411770095778974959499147283383622715728101346855257250482727904678832075959597350461123893419712616214071775763942976286556185238203184504762704640663722404444850836888659344746587772240182621144511690861401586131255760735207010582818219111650052603578362816094802631337311554221200961482767945915386580101483358380055669395238360647561046523615778078486870968635174790296593645111651338179716979277301693874601195255854232438024405949583464343826345520821571813313971601967188474595483487854272869380346964958998717518117209797735168039465226408969828415939007913155016370382586201742586669164338541155431160034111176009467970800349951311121013190916215711535580058432313989635103280801489457960449865819579744091484168330446900494393925758736796980996069796197547985243986912826007435277051974678861892818255236668386909927631640524955900365217276039245518731985956067787184898721336111124812007759857492853618901806387137189882074583648932655648241322572297368309315193454293117036802176116947541520689417437511739535465165801967104076970043485576688039436337246217805791618605920475680775943625915212673579919370555730040297617396981455786519613722650458145226038600341250280000058774699347993325879447371376892541518924459680247094401612425245307618575139477164712198073172758102841217832400709551183231614717647981248814468821528872872272708131689054947657949379468479268048873747343263353526104093495435708533703815123051015820597912618062958175032361618895281114722085802920005724823912258217055420160, 1090731492377649913076371140926090508772288022347454197342151662049370236722216185228086315727659756087542381786669313644178532646766436284737006116912929052480815466086667985449476379848717017461066159075763944044793663983039270860309579287128095894281232142914478590317223256735391291218709799496421963380887780564207862618897899570488789617056638427895664654281211004766489910727727759201869928567754368100035673717570919126251088544271996521425780323822125382487425579684333175106262840178463933895343170737038950968066359623128053628535048757661064396306004795648304940834022134014394738759997701517820826227420441665932867910905808846005834356158743488457009559411929525941069176013153662608964473953666693646214666782585377199491581365863433169067968554135514558442306342887694230846994624550135534847376599232197823557564146242081587332064559992017476950946319619359444248109371748486692855799489698611814707943283617576829210629477688865539069261394552743917809639143313973756326583543848257378462564429616241730696091062171503561065325895232765192882741203763695870971284992282098111218660418751522767664574753593551408755505554155839084715661988085587581566973581015461353733620165345862546046674315694133031863752093388494672036462729057916866275750767303860636596466131368879010701380485553645594699302909325196756079672385052501103827150151831976334641466070132492510498840375913377104324412513915893203117957074929225098251683568818116610778983960015236926371712955543693067918514007296273844438273669212942647585898655890739354078797284894964671836167065386613546773833634383996775276160029552156249040219772103984039642838626279683147201335391793975777396995993145807139132507822505131625600404251400452096938297028960261358945050090842090295278274847010557189245433247492155849346122470894688100480162577170477926277810346432479715635924966607323646570559953092490196327592825540237991980241590165503279915261077067074366481305045563364399525904422723786141683588265993912136830065659108641858179205570900455649154556530215297251775499077409916111817294890330692445660632067110242139656963639480277435505310459643431014873489279414979373131151267245336657370517617194123667803452567018352064922735181294255470115135422465189162296162920296668926670039756221615001022346654653517921366037709997197050769974298091004898049521668450005074312059455258124511891747278706315095791213785601531930729995714415221299954221210448230969019753953267507156418560, 1090748135365456339041586926824709096400964067164273332347272707540109023476350483456643682700482416018057609895981362120404606980048375087448667425214590816869671144547395038055582970986878455636444962424714107236239490619974692554770930709212877821728916669614260327992795699918566977659395175021578144334544566109855586642133164142480791907459073081590624358274300179425040837504737754591061664838562273108983506886107634298866042884653729319819199997516446804694739144110610717674156946529148702714412442293984696868969709907445224692898230111221050144866923794893547112852427041007695329043678419482870554145720540889865230465166845682064128327460786411382323751884924288490359559578197608978570342104424944587739380487102228316436132266546300897104300298367464939913764498334082754312722554117819014494666733843304428703937824198941703283915032685136815704633686814941668193778404358975865825028806933982931557049500470592340750507523610764520132237088741246609468819349337613959440828784317324935031505062497594936585663442849809668662650964255879591527000676094851237579633838846544771148541303921518249715058663926914944350215064247014897203907073996515109866185678977480329325325801747949437443546148220516763024497923624659148936397529559134468581007943125037851605844897637030937792984208879998260560834990466014491803030020045397864796326702999835042686266982263606726267146269373602788359121917286258255297088099245591502185867918926029084430605200919372173516522535733737890028181875115540306551779084866614357067231533631720626002919587235295062368071686593937750462360071885117835669805146321374038164582655652795571977548739307436252124465110216812285016292939828102403759493188093620266844902118992158588255074301105296020131705096904108125908453231286645621791511653515435611337191921902927077389109450451989403004404527133421488734171726166453908082112971477795474787089400560567367842496129965928562701168456383421601224547224975507428722506692020725843928961435818309035149891715365798426895257374225068707636935783558936310339766210019945402769632483047091147946123851035813219440350036499475353738431721176746185131364175201392263406813394131677632259165477572009757420066823456072165146952257899881163435108097311824032068432359543340248227743649736365547338111070004318372011931585654645314294836757658558013694582114506887325604913720922722968365137005114262182509113579006044876988892546771973980841489093151046977170736321405274931855360, 1090748135619415929403854669820128643835281822143174671095392721590677921920417072578689030872885679376536174029528239896742254073353278082923030058229357091300030393146888777261730166167240147960083923101996823490514355455651568890737193309875090994887952495597058554419219395583801974058669822774425700320602000555580027419219660782965643544761919466940595449891933698401109894205870007440326040697196084961016514337994471542752611988248099510093894277317118938299181052534179992180611763502713740568706813166286568129787497207891105101070642977075903571570054027644364590446601280785149886722456526311428692503745869033851011170379573239871025633307907777362710306567563441148121858767949811499260469124776695938902641931594003381934561985005343743685083799012958615340497526215585095341939983925335426324943931358772634914039415810241181336029872642177025788124259913276625707191883433362498148979089190612769477364849156296598604956531440099537350932558545961732221916191503815951153776287037593938459242959091504280127175810734425619861520616741230751469122342495262459811324635237600645624320878844480106463393239977750409859338365102275402708239345773880027238141707183621557733481314949378274404868584905321709416744565607290993339377141986944120719563564133545054356921532678282631495561640293652704448981407979637281048067370092943735415862513219631905132205243835345916182893926006276981822640099165954635101713781042208879607159383576070856276803186793994557281304652875534793746532044826511343908913238927973380729497620328575369613527557267407888667221403469768087071709689761333129469855333306317190610121128804688744301302209854694241778786633133327396692416385648538584937903813623713078893779055091594531543783419179722909182516033055000345688034320365228169710990474860995658072338681123651241223172931351929918827568679587283744611196323840052692029991663662335786495300388236002058368899453352397682826240056654577137531924806502740465564271415492629087478374350216697724571799736835532009208639156739698175298800515035510452484116660223014932861307476880632787267150057929595142785268236485943223275300709970934124908318484485834183562070916059435823162768771276983699787719886834170973112315811783258262042268793707899620037982010519892205757909218844019984162560417654567467164875084760799557738260877398316200197677337735993893876640054030862480179650557345729971470059927578032767319931222828570259113571184368826210270342110464355294248960, 1090748135619415929462984244733782862445058741317256278077723357411872937927833784244419600432340383621359132078539296421583922726078535288895631126147893430149380770045156693316471592314481596094990093519266467060963746463149021913517350803079950400440665964304739215704920738623747423257015752366908264085893021118110308974552597077954159980749712419298225792610335570650809591039390908475045801933904902676564396390725443722970902476505668943463129909442136980589661502329916207474552401367763852856835262959009067319505910523234201508849530123021140590765937850147753368424740552323470408182285922748805210520738945273624250073532547213864411288330003393740150912580166278929704842831018825970092592589997564992748701241134099098189591461277259179911627931227354401824729735222739283906940258565844609867958833251463899830750255317198113101160530620734317932567900498223532817667589142046943165554232191512001478956898687683520250475974324734315380150309747612208712500051022967476984319077129296386777374636865231087169447708549517544139233017684215770290488418789440168334816327372623519038609022141979462139722689427219151234633118646875003741836690327166568052540560892638150017862105394046379266526690121410209850772135746339395758587591648792223654974745634225736271050568271311740257450712934213663479668020824855253157533409992242243185229562856090869187134982573538569852483225539869705077626849803583477586364785204481055628574836838979480433938208897652545831398860133527896735028968302348255129557764568722621963320682441686446392311846397899383114863434253848663932279264188564128386706056453584844520974679854641137384660894775927042925383218566634937141648684602149056050732108371054310349389279475071554719181040574555552962971974792722792653974763290140871652286270098969576677480222940290795746088405409748159994478121367758864292622252744789474675449474741606852764070764063110576030660846709793102667506631035454077016208694602827335899556351637399344567778304083178028820294133459605355876156179714463545661793044235280409193608501261558804583167350441282704397497970403108257267112393653696672675910688099839367469282734578305725116229359673050529813789252273363198230132949795533051518858815503461348243733779388689730783814640911372667854894579549420746122021822981211980082448791461461735149685581518666731366228054655612843460369296145991464644624232666058546546775071466057342070960016482455402459983974533531512623447503628532879196160, 1090748135619415929462984244733782862448264161996232692431832786189721331849109875331513870234605433463932241694048131051358947830205980188196448074959461356758486573232462591433156779577237490627406123547618423722668866652339479999293626021839890161927470072222416275310966999593803517697609822714708579884205550840414698745794222115405131762724689518277473450666725768294443700706103254859716733899036477127355717020008787842924414391583891235738543020558099725138939596081148014590965124539186821561529914566658849262988504621375111628343614858679068075902419555944729073976404444565343555827377610000620947577410278627011740831480055497987845581365988527549373552036103980380460119398337457819050480022405702325635582620236066168807184261870584892432597683277669260204163001806232850994074559052885958077900805983585439963419680319621217850405971289333030803245070840561728370555174569443676693629170452149296065798196661572238035681751946495873207469100150493032277188951439284275065790528306049503847529562489086229780168252138484384622224460015690956455991882709903488025930330456108229822033526376707136090265975193250434767826227728688689631822571110448349847083887734391639427413322727296020796085661840741564416933944834885347677704020625164362236290082483231096646670146316488035415210816619742524561606952935611302947966659440338951555748352481673455328318110092907812432976349828140055049776760942184789064042974347999533186945347522493599199813729152746600124370793863684351800627532861582603373243844541669894180917405990955855670211102417040532303109059148651080538307108200472206951864724440163912445823502524921620535906589683568560322180265439851314707032130422408981737587067461745778054108010454979688805716669890106223718629918609636282362876953861912714996254991032203811132391157099002202347885731138448079694323323449229027719621743895573011766662593894349081522104383894908548239240269319053774558041228754281281816861897527545504098214377454609550129806936928314745701910920161391616609369496032529549582045082542643910019366151847658440920119593061651167368561688293227455295170854030179178723762426736301386023622466277453636011514339531108046811378554467570571147700293987047007133169604516470460363030434395212791168390261169656611459540138630944243057585634982081359365277395087425491626723439059966600654655183801562224994052115182662706659658702893140791266483454391692605083442515414863001025232435847470731267136086799620306370560, 1090748135619415929462984244733782862448264161996232692431832786189721331849119295216264234525201987223957291796157025273109870820177184063610979765077554717727193825132424258268072070423477350441019325238935081369672808088954075376607323183064685826513719267367765025669297838401423262150842341357600244555889201894556085847866483922724148646867108659100934137092282466892797007055681424336981376513709740535026193493673249209257320971410979203369564857482654510028075971351626483674957465557609650341383284243352703413714646767970869719760282612297099758526022496503350912508240831354915423886988443810272342344732317150627439462977141579914873924393499344568782246440509166066283446893682365040319921619212785451204784909812620149202475072920645750021639932387054565814599265491865025466591172979897528545547657398713095194110513475640015533832552892834462456004562452971528736770337713855531343214788202807563614479213467081621550379582167079624431075961285990652132534019881887236124261807921871717536754538527881569172145267614894322853623609813920928459120198997814593256579843388566344082288016681611654470716138650900737275301237931416801181903989453821932064570156865659395968836640923032250896569702084633936822519618352768176774084397451792927718879958100081887861393908320621408161687515022883010853676704976685223953947630891854814753738450680771222651381548932686869654811143303224385700414066978115266169823947267240120243654344301634559922544942816043553794364709175132165894258852632905428043741747989065584385717223677332433400389608789558933209058517367950612903452919800029473576992005403338790727107551494317528931418468321870206715879080915763252955490226179218331260318126443739420462473525613282748278965996483750636045783491802222016697761633212650864259383149056931239290285624805626122759894380826805436467577805724137767574570906567601847329444596436887515074101490955904440736746378578909097694701009073306364306371857928229086986807866811037349498795349771504573858928341772320617473445645992985275412333509090804871751065163475735116124159825908647121640421907667647356208564338125924147715960797202874727558317522397417637853954101630500329587808124225607721416501990667502342789749660037118355919877562034711995165307625661050344070739613757088494470672876611099532221420366583803436275263239830405586791170387133117796852392016463145034898659808641129024904249424733643211466577601264042611135606503976088487910839773519358050959360, 1090748135619415929462984244733782862448264161996232692431832786189721331849119295216264234525201987223957291796157025273109870820177184063610979765077554799078906298842192989538609825228048205159696851613591638196771886542609324560121290553901886301017900252535799917200010079600026535836800905297805880952344434142288520078948840015587307354938660586662128298270350249817014271693665765110592008613298778505422237692146259873858659415573867216038413367887863225808775353059030740090896360912642226573857037049962736349533220384817969976483149973107413139227644176078619320341055567499174066505299371568329139777241183089138566334553194650577629094056611619967969653726624148744303488035402293152604489486492100208017863024726771025350917773611238726097375366394777344426511988513556879991178832915713510549481697173215445101845957529458649240419039109240935740910191672068265273719092589036748465496772589128171977093240953165534992672018013618814995161462309538660641385783569275376409313809965475889555022982121273477969648053452876833585167683334003690463172464081216829623878909681066796095037273252169666759578152053991219528513242729480885311699333643283995611022633415058770494955457423321606395672379513094283755488117583208734138564299317466532948220527445976808475956204587074983904100207162912865380688486391072610835612762060729181212793646168221753156439697858063620473480211440842709029593612453629476963272918555621144668718781463666529288238422362202825387580631554852164914519052059660040464663126781487560119934326441860936571324105415002310162950779332518014848112844743427605942506544050522057943770995582957029023526909557365112077631459260712531564908022807631888258826691914906113986248716550085419858013381711311649991056871703624067763554136461504317273126870747233315465647396625310067987550217403326963292546153158772672740041967708838522805761174003091611777775043411335156923698959839678510230832295163313316789267444620224432518792403169045198033711681799380593647401842461843648423716417664365528718045683794601856283379413891052412969460121927658025990683597601528175797008376299141662638078090891860989403913605461823884961828737140171022361679405979038786444181270716007518309822554612689912150227475032388745809549109277022071797772295031123798251651255599727407916691739326020171853970956314931166813991316312725113081108713697206841284865031993483234062808071776305097470274820616405375977422257119466656882704639478857686056960, 1090748135619415929462984244733782862448264161996232692431832786189721331849119295216264234525201987223957291796157025273109870820177184063610979765077554799078906298842192989538609825228048205159696851613591638196771886542609324560121290553901886301017900252535799917200010079600026535836800905297805880952350501630195475653911005312364560014847426035293551245843928918752768696279344088055617515694349945406677825140814900616105920256438504578013326493565836047242407382442812245131517757519164899226365743722432277368075027627883045206501792761700945699168497257879683851737049996900961120515655050115561271491492481590583927528068362121611832823090350947768974356780606151520143159909137700592185973126172549006476832634892320043175548198813118732027663641737580234180498216659031323755528672469578345747574178638520542422428423677558820978627530386229456967934723788568179648262880758976714398711940255399001607683329891312982140614519561421728861174053416163557141099001227260702498594974247602767107850237371185829184296776123032637607387534110972932388406207584762847633426555552446542114214004891266591088458003495784055858294944168684601688858744297754455478086944868426545830699462053020840665064540392958400443325645527374926882973919246656771539390355706463348469275233864897316857752844929570354333768590343841311070850781091725431885844774325016901949773780261558722409401181833978850211680880235006737620395003207721429913359698783128999341087064869360477360260946612352621282830392338045342868360685801099549739965616135919539306625022788065057280252729962269737132309764754628744321772059641657719823547449320592935611616099240742902136329711517410404030324521840342033994485065200736874265167184988389293259882587602113424959054628993094268364393026247954669688793470940786540624498332650203138482502473546445070830271563685172304095213304349600298515635788989580172037008658825732196098316200861698353829406714272630544531590748563008319858775677970324879375646607814716537093794936528532510075217655406621358266156154358999433998158724863016801311862884415003624026624271858216959376261551815071325789099581359312420237157949795754513740566131017746235944565634476856040075065074597078314422621893894702231993235077806982696786165968173125570545073461288474360408005636640266535246648614607443110206856314723120840607763815821602035459921424929857198102394553285216706183381968298312489240849692137274288006245419386744015437915115941622091612160, 1090748135619415929462984244733782862448264161996232692431832786189721331849119295216264234525201987223957291796157025273109870820177184063610979765077554799078906298842192989538609825228048205159696851613591638196771886542609324560121290553901886301017900252535799917200010079600026535836800905297805880952350501630195475653911005312364560014847426035293551245843928918752768696279344088055617515694349945406677825140814900616105920256438504578013326493565836047242407382442812245131517757519164899226365743722432277368075027627883045206501792761700945699168497257879683851737049996900961120515655050115561271491492515342105748966629547032786321505730828430221664970324396138635251626409516168005427623435996308921691446181187406395310665404885739434832877428167407495370993511868756359970390117021823616749458620969857006263612082706715408157066575137281027022310927564910276759160520878304632411049364568754920967322982459184763427383790272448438018526977764941072715611580434690827459339991961414242741410599117426060556483763756314527611362658628383368621157993638020878537675545336789915694234433955666315070087213535470255670312004130725495834508357439653828936077080978550578912967907352780054935621561090795845172954115972926435488646325407501512365848213380395168763512806429730109607098577644744240048503459529594006823631373147762011780218660740030215430505248911586325182120160839367048207709418842650690943826010989109302792718425868852384783378651199618535121913835737651699662333815683378345818068070160548347800369481364172406204671458973952634913932812733482191175501628465349005403383205634207163186366050321349674463279843106828789837369958673440743379029655723491233599261110682223445532527992025505094106028374148434683256837486589543018181873279720349434704460879700399438016504650780473547823239120431423814382915239771713285086798751923825359346515261480728322427217167293613096521198247560588729708788376007087530154941809492620352947595475014394229254625965054086766970439573627357949092810593883736061141168581582787315634913260797956280083967967201275577888581524322407185240031043931510925713450658807511908275263101371880394716465807521940885628037330976885109586390268456528362201664202524947917653322271271470730573883899274644538470640093205628124760082118516398285556726512915645798229781241791101398278815512033744564071010914628794915292515492524789530849844709747037539932187090270337487885794730917151571753381797325072561602560]
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
lemma pointWords_spec (p : Fin 13) : pointWords.getD p.val 0 = PackedColumns.col 13 p.val := by
  fin_cases p
  · exact col_13_0.symm
  · exact col_13_1.symm
  · exact col_13_2.symm
  · exact col_13_3.symm
  · exact col_13_4.symm
  · exact col_13_5.symm
  · exact col_13_6.symm
  · exact col_13_7.symm
  · exact col_13_8.symm
  · exact col_13_9.symm
  · exact col_13_10.symm
  · exact col_13_11.symm
  · exact col_13_12.symm
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
namespace Q3PackedCertificate
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity
open ReducedCheck CircuitCheckWrapper
abbrev I (p l : Fin 13) : Prop := (([1170,113,2584,4372,15,4674,2338,7169,1352,1572,897,2244,4264] : List Nat).getD p.val 0).testBit l.val = true
abbrev pointWords := Q3PackedColumnCache.pointWords
def lineWords : List Nat := [54414283216418386405143011182585610558282940790406037537492004062163054016644572111417355868763346349676566992735216627690924733321631236620916549449564699661430743289706310014261474781234089424342126221073254538459610574591768736076319966194600200640867076304632086538399052734367082184744716055813715618595613890029235408487241047198643551840415987197723111238479647178147834653107374257007824323724476504536236747946638941916115120386519747022846997537219188655442842055263771010367621012251156923647784604660767225259562785129794558400774015341389746680715763478428862554837132284210612274671700884893008257174490452564010558207871295416509414841554342170036538655798928085197670761089418596768080944419839007813329364963792816334763758125835312423935239770741193667568470190281161323672241312308811377234909781768777848976252646365422984565783635199625855680940302509899502663099194365587412026093148028004099700864933937515315585722270652162565013404465797387368440550375757981806905418414112959310913325391462346342091196238117094852015874117335272315579671417695066411388228209347486887153870365679803116331456106423347886929558325116948247079545856468475067490881683284131425018266001923794034816768311330436053168593588079126415200543704281122632751101274779722317948161276703987778534481237371363151675271036306649456245744911820413393584592093135296371036036740575874839973483246595575343330216225643305289931662403382610293860415139890233243790921155720504828258754035463962077390180829002872300689045928010722209861504440102880642878632929883057584031509149088219304457379557920039391581005475557558311626721377422343047213765245929000517587975522439806001641536850760006527614273042119165370663997930969426829519103691413628273025165159429800162969444610456479290301823439814079505518475993543631694076876552526159764434117159002185138412065509099830881358122227214949342615991221410004375738963495379745443223499495490544584543144984089720533741521755712785081533799459772074479022625245198272753964189229920820551706239225274358698422189657663868235352323608761572854753219373437808280066993435443, 70022414732239771565520471652098165210893541944689447614725164474251237992496875309882161547426879800517680558677962207757258941219970722619442277304183978252343294390393039387207234322095493833074196126248378527145912088282141160246154455032654931485724380926148032438865286878812046758764972047424429259882894504388680677857327479548285155518456483873577702823010416911256790700292408936396364713340043975842043920321139019259553493464791831906386322579197991441259615455471257954598866642564049834475640514499984422151774284060205384897335366008194542415936387818962870938845399560262109161101127140100001712562513200840195843864338592310757828156652687451414634626116524527966523210276593638912284551603371208123512644513431817954193037134415721708576726301818580031081282654857161335080338875719831293796505948382744423437238579927512093222061262196130166262250955583001776264517130573785377465816956929801143278405115314449147310206693368177842313829927299424485992243799275059502729771626234145082577392992688921349402151359742163529957447417841792994908885733677859868852533304410783420003915309337258257882031407523826954470552504873123041978857551296752166661181346796836720653905837903756168789510442144368481509689854706459003438556791878417361835552001064410150782873089096597059375029222590743302133530233143553017432183889944821288622299809668733606342094889478865114402524016213839824370244762813418058100191189995050829158554169974763649188538087527710986142094540253477226723144445725979381539574674872231264923877161277390158816470395659327739330282409705854733787160116678648643931478973209549706504448578273432279122053359888505825300727967055266099331437916958000273846655189324741492965733491366668774479584208940973557858439615236193659209141109541790608843790263139898333178670444935095084044993674652012978471737263772403627363778538522117328809430971409679631388768692920800477986672293195038393569095672501608088369143997235321324448732307779925176247412447790486933423627584468520773411709999339868325816429771661877914121900970406733087187928047033889863425843587386135930533834588396331755828085945455564870867892426325317751695599367594810486362170672389912572532887873614693277633172865041904776220775163733505223879420945095729634202306758132168362831864204931407011017667717904847932550185586321757159409739570381614945732740134863897539246886713637862185554044342010841562839144004107161787454805, 149456875514836934519504679603006855376571507731929646456592648340128321926408918190791542838695449039486855607878950332353000851246928509443993630108626591537143064195981135092244999853248328911398574396157611442432122676880823710266845825934774112256218950150616595246156840084680971350714255054996382634976614487931436635195670471767420868508577226585925243767833414120403462828110360869296083481723194267896426618198467556701579249141685638259954890885026537594986845297218211668677818393941754868613243801937711734470994886408233874852791633668907351637363684223899964280719450762998559758301062459026669605678238436208651511812349558253847814306178330085031231822086800592271504302827473067742883853353551337691519977578443960609059093038951960474821689033447842285368678280620628322121941861826025471393922102128688290435231781498251382727681358619397732907577385391858080343648031099774110516989028391872125454009070244541738146412895273346568294727523167930895000074255162716864804702400192504502497349605821082878527139682821015546616608688233601595534083627276949109529012403918543530273475440943418300711979287735122737524445053368511501101607977326267552661311544401960007728222900149065453479771482526881682345185434857493447393610570625198523498009888792093912951454737900260460470917714272764023496402851592859261046951723317673129331506643467141102282292690069530653812392169421769018428305218725595368942362819736501234572979808260511758072979190720817234968310139408888636320699994217796143219115866479428869488881231463768754947418593368323573864364249738793747249025310706502488627422471675608957827729041418363173649174883495010759286719889390585119840437309737533695, 8095578175373344162456482226484754152303256483338572464675199126990056146061083361865354496557646072505541214448015213060289639599021018447790612358208188289149187539236392942803310595903009879236501442706250389958074956148059270910157538465913906202104552973972214118358990409814852824204018201697270379595383156627404997953739788368163068394904229240412009810602260320458035623817362789926537612728321026980957415284050822091403686260061617895702762797455418800660522582452661243315789921235242504757698341141060070715355690157164745309685882246615042813596747837452321685190015454200184557047173631497632199654207350453731200293652160209690463065295294887234513220045944476525183898996236245962606802805864786166330901966655990081726764131772158323987467509410757958607647304483555642885106616182276730303386024962734082403584188120642466037073987181952974779101160309981355069323683286371056707684351741314164909852186817227346063924470132243367107789748122428624392858587901996680752542872371008126189286142424352975668141824996061336455580212481426105692623643687391948639016153035541609720784958935045825268770269219324033310583440096142298895, 16643749685197465926039280456760248149054156740615437436970058536502957684429988482738448684293919084824251038317800034685433292441858305693308610133173949783762970913896284268537572674571575572742761144634037357088149638248406569926318616829204032975019459106367588574044557558556901439487310678230043197563904808578553073226688110358809186157739010228023975674737604619711126821993501000314603123435567947000500879542456711926541851780552446448666002801035111730257227167815857864217864614620659177941035228846147514581140270510155568879252197477698110920401270433809168409812313983382331891594644848028706362882315027727256412094751614141852773414676561077617532163338615070347930516663098619141338573830721124920904038776034277795234079574055686806025443322917639358678469701209374532240636560949471530471635324175738250760846611836658398673480966464958068548270810481578954133829570127483518899051874094070664031784274955134865756981617035911162257220992827360535829886021739388532224612679658415239817053469404532853536030575361479020544177288904911400338109310109420592624941563085220350869526725500363394675932151300377747315358268569855738681748034480107254689510658099497656412114249680019149090128345018628903226582985777485006142179576714857772465994201644583027813563039803318743275835226957384780742508710710398135670858534185835450056939020791998987049650662620316060631501316629648657227732008591016725081402751255624823446621989703650013317713648360278779373745668042244717647663376630039366244116712743767693265477674420982576388927149793828974129289738222671713663768387713714937515520694182225973277880797063633419655381139728698804541205052383268138656313853101208647279318715666923973360846657417241850264154211287163104094317585396428644191456115757787789674136514101178858767849529351091383559007137807410955651022079290917965870216909581691997838569338038253521477858205406443867160559475678574882189264605611107797745131374340495427706639360256000912001610995740917648237898950453074265309992911247209034798079134811208345219724661691370612437490357777727332990462576309065357224474918052361293291032480717681985295017994781678819330261142331141123491405092825984177303946268769076403470820151304606498132248357201330288263363981457585527445078395342850012476544447439841793393200546707336820740646131563714277709463041410284214554290647908022495920707952252619727643963122212974236749882990485528203350522147716299107304287871602589697, 844529322066961957944285014250322997859622900868205603790998624343014357527883606445480915476119531945875456960235830458455656013834428653388602531165683471677209343858149058029735559411076683107125507703377007696357580310681109367165705934812376577227763159394385009000853067498481754949210114128200377024154477080884318047378356469553461753634204195851181679633919680255369010715588684418101108830785472508169779062063339703536853793649574988855622444369980363636652313533622143280976685987949604663368756502789863964625819722434151841864942492453266857585551234299934520900444712599029848720956752545139766376453289713570246696267099411291472489660799018209309367526825270297547937163503760539744327693291765430630907590128372304955520008743742107102558976529069760925494927325342941123284700546610887318685689228745539721868333096928880248110438056501047030596315038354491106371976614258326597507092728377271658717422959305630714571892279466783018905788751805294252316517974511747954552910810344397277326085877951233406261337704413942436347687386263794483, 13573273614655496027830102976776581394383569509632662067836371834702418794177352243306722230861880704073472430606741694756446325121792034344850767972294923099506225897559863804366852825098473418647496255250334540064760435369812624773836357109331107696457264611472566149545506707635925610962137577449598278220934943047213366860234130750667363110124869957051622841461010486412098557161312556277280553326753903889785757774445406706960836401348064283013917081643247832455261656841573275194862349329409453789375904083240416047815125262274470351759684619895704667517544179730116097246566235420552993808826846651440284586012045202944442439894285958048742507519892201375204926896255444471288459854132613637719494401479960300056837047671379767251797649258030968418552664088362380776593877990550852855739321206422835194242989820920975330501203934989420769113334512698072597370011701734746708871451252034758526895892687574824029576654906510024605301092556338559807679812581102276849085676530033884748983571738507156364567503683910710732142298142774039009431248475228932757249748500224032733038406203446784535874204668164540569442516993080386340020705661928358189542723708545697618280729409157991780922712483617223590993412293354133341657915714714144225470748384664453838553288911635878941730389704827745577957275128009883740751436584141176374231845040917608999742995247507546888610327032478949486564228876246791033177100114666174931905369046757375074702589137514378163018560914487243226881053533463689751900194819918557276093427719235955446516555261926990897233111088507096243941090360919152869945600422410215875628070854398209558772110471701700958206600449313730212798373143273481123883618739375381308734590301495402099693707405481207611662228484456459495885596413482185523, 59923104495410530257643506359634157787265899298076885757810027052577558601833654377569492440802512007040037959957131119219596589604805540830949143546491374792589297808288495092100739867082031373151027650695001922946050227447487627157971036846942412387783503561528766079982415312826572101611785443208074712405, 11052923994698355021998761286706923307358485839185703291560957377342461448460582812300089014716351615254264235955950684105992795333504688594200006239872423926324819111094014625727003802563725957427584721821155072176771885115526893359220814285820144867407778653860666920667987234853659448955329648997231876764997360315923967145669101997875137415843070082960859342790734420315429938704619881028960458488004324084766440025234256868487908927515064454600475713446045174109756185089523974463131389105800522855557699360328130598390888663878150273289701952512158898273350549672479469677819978848167744215653227559234940271244286703654682292045254986934758729872034644860102799380069935973542098454799525224084590070567301495944387139924824668072246740710673455811894305394929179510687206324030496333196357235714279724151060432747841078785866910231944503019575103351077569834030021440156534411091352663744769685029283432391384459248515543536892924423521676957126575470140019198048535857863882315862258203241992206888250748958835968410144262367202713630698321758755851529851459971853136762241851300706765562403676584494384199086647663797396869858556349039201987987415336345787395009111176861966925801251172881594470678569686277558429513505764131484027113925981697851427515325686584609490696832518735792776323492657206785454832109595616246671660109065280102356385176480713344726396248176450386393663828246474363998812883095694391318175358009087002411981583066855855909908385423200701236341822648212126774538754396139952709149600320726280789919152701046314462496675626445485554121947151676029360747995324149386317674693257041516219345274937466127192124071328940634585961187134352463948704616848895019212191981929333380202610657433008803174655754659114414810894799853409180568013195795666483718072916750443886057845212900349313128987551121461640270153494517843261220623715520616285782876124307081375909958195036902537066439333522206345215181305062628735461226431686298450385172120944072643981957670836787139509023337287910322901985330325167961274802400955750788109409648895, 6197868487794264289879165981166817031873262771625116840299434536780248425800838822626226553449670121775591528506689897332590326277465390260823321880150146621077640283532863015493773364688572693661794676359188727139780879655312193001771555456857509528195778915937415283785871749485710642956254740267551504980540324777036246669968771986628817159532405411275002773761390942581788146915078208929581668847004625225993835430365800681313837890018602424336428533025426718651685191035032085877402127801948740800021650124203388018620928183650406932669328977356098756155011646410184371609357504302634390226057666378026099908352813831913986489532489505535026239000460309738361825872614674242108192117072114073217269525818942554153783334135707884978249293823728248758158160686915656347752014462959465299024747663955195552141892905446726254529181402309667094472374185367773426468996871276946996422844071274896522689759692752242061895578753058140801306651432348245386256567536750385826854318598789638070561658480925140667217414766580524886667139511180522025445967389135644007824368755887058426293983644494653961229182157633999134376738469721525380998640395837750125178425009038211059172462534919115882178169706788917879062767012732480594809844737973041140149871114206543691841763910457650825307275886186903331428541872330471300067942502792311164813530400213013120738401211888491967734190017238516506830337982259288260835741825434992533593430455756497225328044617815948263025576948485141304563957798865985413684198162751148328020798179429101460032756798062776868984271802813762858447874317690091990573469285356564237967140190790290613414899391107906136021516254823344967722600966342912446687830732605126002045219736338837832646526376650154691608305870308093826217434994397268437811506546306656162642540769124969450993403941893329326656635111955644215995444896625869764337786017220820891761247994743074089023170964112612048290705796122309682814941244821528646216241783398865433084368502204085406364438889434895, 688219715414337965043413904125347391897801099048447448557304502047891262547165952401994222109785251590101197582338396138499724096574505236935672475963810905718635022069053917335509642083375007422456457865722836444589945010481214211314547129924412828322434434708914655551959025859754223361973568437022533082777626930067352795763174619001869577286809667368361780658521821703434533875664690353157415021872149789167398656355308914109177140055310888235771934577406049879655739648987747439070323138118121608363997344507670834001172533481646842796931132821523326469000608392596261648110454876783229459742639747797973489533414233834300372007786061237220749161657315648195862275624451772922678771940239966808398634143969968807140277263427229213887251046862239104338116355166184241562729310236783506277144072859330895448749005403411091753766750333511592972597990856424402783150216027913192640401836500905118499738579186909317574200514153214305528602567399341468401541518820722199693308915969243988096860693501654479526758002396968979204518144090578592987800197702768021667646850957910401133271074149431827745498751378384826787457382452276419058103815693871477252333327380694424247956120533612899792715431234276374983801706277016140854344230586464524482310648025296250153937861740192732595433958790753392056069738419978392045576315754469220981657725795745528055148455977447706540974339571523238885130279412166607405162333833070020499917127162749990076419451332763915139263118257406826272298327049765305249474840499668376435260689854825231929010144263695388242026346810931242593289435258435531514042202344612929478911428880329420872329394011406550408712053776598844760897367913391115760844808893994252020026922098740476956064936683996043875412289119758019228891295813485991990348317832250783518751476110107118442417454560585714995090725057619301427454091907872788251075539750207664114524750882568520311873732002370657784969734322935532995249720340374009533079640712618889323912531829933321092493547034900043867416579768975646262057420138971859983252419576119379196844191801083616395451921441810216576108568472043614450774734312172860882980500243704387813036222110525558420607025496620487985319497540887205205, 316289861189083671309913007276676543786116492386926955722858314526839994417302529909439835531017470504333065556723299696080615448494949291378476077734452306145747876539088140668222630472913385894280754194596816334744941414725633309368057654447774437142825599640550963428444144857068327439537903533240583682174870988727368450959093693312395510804389690460518933429237877552342311435834444324435351581153316651910748540394080435539060287733981847085954956549596728212188432461412178075087982776015677478448649456407886362625455323559499504401390494917080639844090595240113570013895307085477973418495566956877951183189763588496039414610820462837147038738892949185032737010684280571552121728831570242377398774651641697593719326756937540967719918292046881456516441157619286926245413086501655598978028767751096719334268201749367996903274255592439035327876505332893134757099804504365453110764078593465314087942466967042802124006252286466690748662600101068912438723163475314976887356411333706984944549246295726283847304154429642263551218064030162110698277236555507389467143853107191585539903928217996506238510187929429686648353736474066208899582756513999368599517557984607226575312341731764438374434665517720653178245166467138508198128658617396585633916113246104522631928914594523086946590071127012847447908129905621728288590270834587755874589124523859177384650266319157800386312567156369528584893416179522445590252802278307596145267621346515231100311812455139663859413634585727162496106950026315011401060282069081686148516220314017792181611726322935587351731421765355029797644206992425072671314536865696312902485969476172579671498330644279444242243586787683905127423925175167874854235709425357399003902000383864021866545055902084243289806176634620153469970902442657464264402173625169230129057959695, 2780544244249711824309012909995940928929129698289783176799595433084621989279622865771905881836948144190901260166178572684269935019078334516657773579985609515748349732340644421514621779750340415043854986095066578299564528275365467253226592788409323488946464973046274848997033765339486806006205102658008154438401910003424781228966998327519720238637320806516926402807573114888763787234946962152353232860501331536159982848237224785519934767021617364891830724548921303049434156056538169958481191650236174028957348585922232936628676770819021008674295344031965840135699433588172865624060984797191368135073976520199257287790489132343051893005039967195624100987477434799881707134118551818549277140829072925316656435371830564647423661720819481672368297310065841841671261602387962874012515828667956574659660714456205169076388419140359738376400014340887724101472773834396573656540765806274061503231123728972114720639797639638779395489044331850807040706318465443303315717207199372985499030886597512177836661810775589855383410067931963982469722036110862041946657716619024335959130440531091798335729358479718413651067080513562580767655907736609073025401251768435965046704262937463171211750828605695]
def negativeWords : List Nat := pointWords ++ lineWords
def pairWords : List Nat := [
  8191,
  67100672,
  549688705024,
  4503049871556608,
  36888984547791732736,
  302194561415509874573312,
  2475577847115856892504571904,
  20279933723573099663397453037568,
  166133217063510832442551935283757056,
  1360963314184280739369385453844537802752,
  11149011469797627816914005637894453680144384,
  91332701960582167076159534185631364547742793728,
  748197494461089112687898904048692138375108966219776,
  91355004067076339167413824240109498970069278721,
  182710008134152678334827648480218997940138557442,
  365420016268305356669655296960437995880277114884,
  730840032536610713339310593920875991760554229768,
  1461680065073221426678621187841751983521108459536,
  2923360130146442853357242375683503967042216919072,
  5846720260292885706714484751367007934084433838144,
  11693440520585771413428969502734015868168867676288,
  23386881041171542826857939005468031736337735352576,
  46773762082343085653715878010936063472675470705152,
  93547524164686171307431756021872126945350941410304,
  187095048329372342614863512043744253890701882820608,
  374190096658744685229727024087488507781403765641216
]
def incidenceMask : Nat := 389515209005992732313513829080319019620122288333970
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma pair_rows : ∀ p l : Fin 13,
    pairWords.map (fun a => a.testBit (p.val * 13 + l.val)) =
      List.ofFn (liftInput (edgeInput p l)) := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma mask_true : ∀ p l : Fin 13, I p l → incidenceMask.testBit (p.val * 13 + l.val) = true := by
  decide +kernel
lemma pointWords_length : pointWords.length = 13 := rfl
lemma lineWords_length : lineWords.length = 13 := rfl
lemma negativeWords_length : negativeWords.length = 26 := by simp [negativeWords, pointWords_length, lineWords_length]
lemma negative_point_lookup (p : Fin 13) : negativeWords.getD p.val 0 = pointWords.getD p.val 0 := by
  simp only [negativeWords, List.getD_eq_getElem?_getD,
    List.getElem?_append_left (l₁ := pointWords) (l₂ := lineWords) (i := p.val) (by simpa only [pointWords_length] using p.isLt)]
lemma negative_line_lookup (l : Fin 13) : negativeWords.getD (13 + l.val) 0 = lineWords.getD l.val 0 := by
  simp only [negativeWords, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (l₁ := pointWords) (l₂ := lineWords) (i := 13 + l.val) (by simp only [pointWords_length]; omega),
    pointWords_length, Nat.add_sub_cancel_left]
lemma point_bits (r : Fin 8192) (p : Fin 13) :
    (pointWords.getD p.val 0).testBit r.val = r.val.testBit p.val := by
  rw [Q3PackedColumnCache.pointWords_spec]
  exact PackedColumns.col_testBit_lt 13 p.val r.val p.isLt r.isLt
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma line_complement : ∀ l : Fin 13,
    lineWords.getD l.val 0 + PackedLineColumns.joinWords
      (List.ofFn (fun p => if I p l then pointWords.getD p.val 0 else 0)) + 1 =
        2 ^ (2 ^ 13) := by
  rw [Q3PackedColumnCache.power_13]
  decide +kernel
lemma negative_point_bits (r : Fin 8192) (p : Fin 13) :
    (negativeWords.getD p.val 0).testBit r.val = r.val.testBit p.val := by
  rw [negative_point_lookup]
  exact point_bits r p
lemma negative_line_bits (r : Fin 8192) (l : Fin 13) :
    (negativeWords.getD (13 + l.val) 0).testBit r.val =
      decide (∀ p : Fin 13, I p l → r.val.testBit p.val = false) := by
  rw [negative_line_lookup]
  exact PackedLineArithmetic.line_bits I (fun p => pointWords.getD p.val 0)
    r l _ (line_complement l) (point_bits r)
lemma positive_of_packed (C : Circuit) (hAO : IsAO2 26 C)
    (hpos : PackedEval.eval C pairWords = incidenceMask) :
    ∀ p l : Fin 13, I p l → circuitFun 26 C (liftInput (edgeInput p l)) = true := by
  intro p l hI
  have h := PackedEval.eval_testBit_of_isAO2 26 C pairWords (p.val * 13 + l.val) hAO
  rw [hpos, pair_rows p l] at h
  simpa [circuitFun] using h.symm.trans (mask_true p l hI)
lemma negative_of_packed (C : Circuit) (hAO : IsAO2 26 C)
    (hneg : PackedEval.eval C negativeWords = 0) :
    ∀ P : Finset (Fin 13), circuitFun 26 C (liftInput (independentInput I P)) = false := by
  exact PackedBoundary.independent_false_of_packed_zero I C hAO negativeWords
    negativeWords_length negative_point_bits negative_line_bits hneg
lemma exact_of_packed (C : Circuit) (hAO : IsAO2 26 C)
    (hpos : PackedEval.eval C pairWords = incidenceMask)
    (hneg : PackedEval.eval C negativeWords = 0) :
    ∀ z : Fin 26 → Bool, circuitFun 26 C z = decide (∃ p l : Fin 13,
      I p l ∧ z (Fin.castAdd 13 p) = true ∧ z (Fin.natAdd 13 l) = true) := by
  exact ao2_exact_certificate I C hAO (positive_of_packed C hAO hpos)
    (fun P _ => negative_of_packed C hAO hneg P)
def canonicalC : Circuit := ⟨[
  { op := GateOp.or, inputs := [1, 4] },
  { op := GateOp.or, inputs := [26, 7] },
  { op := GateOp.or, inputs := [27, 10] },
  { op := GateOp.and, inputs := [28, 13] },
  { op := GateOp.or, inputs := [0, 4] },
  { op := GateOp.or, inputs := [30, 5] },
  { op := GateOp.or, inputs := [31, 6] },
  { op := GateOp.and, inputs := [32, 14] },
  { op := GateOp.or, inputs := [3, 4] },
  { op := GateOp.or, inputs := [34, 9] },
  { op := GateOp.or, inputs := [35, 11] },
  { op := GateOp.and, inputs := [36, 15] },
  { op := GateOp.or, inputs := [2, 4] },
  { op := GateOp.or, inputs := [38, 8] },
  { op := GateOp.or, inputs := [39, 12] },
  { op := GateOp.and, inputs := [40, 16] },
  { op := GateOp.or, inputs := [0, 1] },
  { op := GateOp.or, inputs := [42, 2] },
  { op := GateOp.or, inputs := [43, 3] },
  { op := GateOp.and, inputs := [44, 17] },
  { op := GateOp.or, inputs := [1, 6] },
  { op := GateOp.or, inputs := [46, 9] },
  { op := GateOp.or, inputs := [47, 12] },
  { op := GateOp.and, inputs := [48, 18] },
  { op := GateOp.or, inputs := [1, 5] },
  { op := GateOp.or, inputs := [50, 8] },
  { op := GateOp.or, inputs := [51, 11] },
  { op := GateOp.and, inputs := [52, 19] },
  { op := GateOp.or, inputs := [0, 10] },
  { op := GateOp.or, inputs := [54, 11] },
  { op := GateOp.or, inputs := [55, 12] },
  { op := GateOp.and, inputs := [56, 20] },
  { op := GateOp.or, inputs := [3, 6] },
  { op := GateOp.or, inputs := [58, 8] },
  { op := GateOp.or, inputs := [59, 10] },
  { op := GateOp.and, inputs := [60, 21] },
  { op := GateOp.or, inputs := [2, 5] },
  { op := GateOp.or, inputs := [62, 9] },
  { op := GateOp.or, inputs := [63, 10] },
  { op := GateOp.and, inputs := [64, 22] },
  { op := GateOp.or, inputs := [0, 7] },
  { op := GateOp.or, inputs := [66, 8] },
  { op := GateOp.or, inputs := [67, 9] },
  { op := GateOp.and, inputs := [68, 23] },
  { op := GateOp.or, inputs := [2, 6] },
  { op := GateOp.or, inputs := [70, 7] },
  { op := GateOp.or, inputs := [71, 11] },
  { op := GateOp.and, inputs := [72, 24] },
  { op := GateOp.or, inputs := [3, 5] },
  { op := GateOp.or, inputs := [74, 7] },
  { op := GateOp.or, inputs := [75, 12] },
  { op := GateOp.and, inputs := [76, 25] },
  { op := GateOp.or, inputs := [29, 33] },
  { op := GateOp.or, inputs := [78, 37] },
  { op := GateOp.or, inputs := [79, 41] },
  { op := GateOp.or, inputs := [80, 45] },
  { op := GateOp.or, inputs := [81, 49] },
  { op := GateOp.or, inputs := [82, 53] },
  { op := GateOp.or, inputs := [83, 57] },
  { op := GateOp.or, inputs := [84, 61] },
  { op := GateOp.or, inputs := [85, 65] },
  { op := GateOp.or, inputs := [86, 69] },
  { op := GateOp.or, inputs := [87, 73] },
  { op := GateOp.or, inputs := [88, 77] }
], 89⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma canonical_checks : IsAO2 26 canonicalC ∧ canonicalC.size = 64 ∧
    PackedEval.eval canonicalC pairWords = incidenceMask ∧
    PackedEval.eval canonicalC negativeWords = 0 := by decide +kernel
lemma canonical_exact : ∀ z : Fin 26 → Bool, circuitFun 26 canonicalC z =
    decide (∃ p l : Fin 13, I p l ∧ z (Fin.castAdd 13 p) = true ∧ z (Fin.natAdd 13 l) = true) :=
  exact_of_packed canonicalC canonical_checks.1 canonical_checks.2.2.1 canonical_checks.2.2.2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma plane_geometry :
    (∀ l : Fin 13, (Finset.univ.filter (fun p => I p l)).card = 4) ∧
    (∀ p p' : Fin 13, p ≠ p' → ∃! l : Fin 13, I p l ∧ I p' l) := by
  unfold I ExistsUnique
  decide +kernel
end Q3PackedCertificate
end PEqualNP.Outside.L_meta_2583
