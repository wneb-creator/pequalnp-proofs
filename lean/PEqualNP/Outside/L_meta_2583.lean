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
end PackedBoundary
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
lemma positive_of_packed (C : Circuit) (hAO : IsAO2 26 C)
    (hpos : PackedEval.eval C pairWords = incidenceMask) :
    ∀ p l : Fin 13, I p l → circuitFun 26 C (liftInput (edgeInput p l)) = true := by
  intro p l hI
  have h := PackedEval.eval_testBit_of_isAO2 26 C pairWords (p.val * 13 + l.val) hAO
  rw [hpos, pair_rows p l] at h
  simpa [circuitFun] using h.symm.trans (mask_true p l hI)
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
lemma plane_geometry :
    (∀ l : Fin 13, (Finset.univ.filter (fun p => I p l)).card = 4) ∧
    (∀ p p' : Fin 13, p ≠ p' → ∃! l : Fin 13, I p l ∧ I p' l) := by
  unfold I ExistsUnique
  decide +kernel
end Q3PackedCertificate
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
namespace Q3ChunkedCertificate
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity
open ReducedCheck CircuitCheckWrapper
open Q3PackedCertificate (I pairWords incidenceMask canonicalC)
def lowPointWords : List Nat := [
  119846208990821060515287012719268315574531798596153771515620054105155117203667308755138984881605024014080075919914262238439193179209611081661898287092982749585178595616576990184201479734164062746302055301390003845892100454894975254315942073693884824775567007123057532159964830625653144203223570886416149424810,
  143815450788985272618344415263121978689438158315384525818744064926186140644400770506166781857926028816896091103897114686127031815051533297994277944511579299502214314739892388221041775680996875295562466361668004615070520545873970305179130488432661789730680408547669038591957796750783773043868285063699379309772,
  169194647987041497198052253250731739634633127429864148022051841089630753699295024124902096303442386843407166004584840807208272723590039174110915228837152117061428605576343986142402089036466912112426431013727064253024141818675259182563682927567837399683153421820787104225832702059745615345727394192587505070320,
  179069821994067265517004719393770557123035839147560499073922571114317373565012632536861362624654977515201358572945823733699027940920197102560968646862666832065013932750060561209079253766221790251284004808302573839776523636885877422791135238515376547524582609864801915756523326693582908070186191519003118206720,
  179766570466052360237648572536963127610949142151705149077185617265867657072940646045213890928808158455225716514812268414598264282604049739409665520460023745597470080465874001603182053859457467143941243028332742390810947146161643764595180884270010128854499581430719252352917935056902309958553029775825154539520,
  179769313444375785814462265863485611229889718115776549548420631039577310219318555512504201030636628662239812719543346771400604958784932998973090366819193438631844709885019339289485527600645229101680144570744617427323613239093066544488844122372018577072445227788470567772585250041087614243742592599359351685120,
  179769313486231590763185205067502474281972610037491134208877555181135709923949037735690276024213413705823039792595812100825199281213020878487102478859428781160318831728534053767098825058678708531551206723464342007537350133167915838047987720003371153224504147359993809275143228500884134199151686065190149816320,
  179769313486231590772930519078902473361269403363094992027077741372816159198983668324764656509214724291581902479869920821760871587342679845464593386307578492764517105656857966598509267284159204378328176331317696638943488431251920295735812264550083217605459765810970935573515804682568218669795142748890432798720,
  179769313486231590772930519078902473361797697894230657273430081157732675805499410614616176613472387041631651377316136471641673072203277570454821379686787760899244944958633938372376730076395090525612731964434268678008150116831451773765893368201788358737656950422124978427902852027528247743196825908506284523520,
  179769313486231590772930519078902473361797697894230657273430081157732675805500963132708477322407536021120113879871393357658789768814416622492847430639474110969959963482268385702277221395399966640087262359691628045276706960578432807926936308666529070259922820652728111753896392184596904358265409895975218053120
]
def lowLineWords : List Nat := [
  1612202362438516399445625478482434675121823726883503404772301843350203396559111756406055148913550443347281823494806389103104468523147286808346284746286493861864005434387625707294085024003364773297834340878416831890049116906832362379820380108676007858279181472248627,
  11540594032658607306566862601501305269438134594985383637573631145613154769671340896777851149190755077723567764553128464542387995665915090527196023934338072556743923144455916925710573989989925907747028471236585529682186524614830995187538005219136435186722779142022605140153685,
  796045880515921893740840784340009919099334674736111188786015696109986287490171558823122061988264889467792355759382783138912642201399201885270835455,
  1393481448109428024177612725692000257830902900038233105088416187017886575689496888172687782322825188039705927097314219305260869837098837594210872808275440014594128991381499292894772743965303669543108482905900987801709156765455,
  2743103890840491199709018373066338191222975477137875292186313895746283296032669003322018422559052964387275713433606368469654227036154980125014838340420754167662590881587937518521434647154132816349326054048752662986772727280727288952070086374316429955952552234448558758525173509399247979016332590671003649,
  145367744859121378101984360338322011028699661524619071311737937905421215472927008112205736097024724415912224248215020537264825714291507,
  72294757326097933040861497784880691502824544888109615384531391835929546202845673426460479344206140712111202128718028925208414114298998390254824122401745389029896603612666735780901582145914989584815640143462939230781780787,
  59923104495410530257643506359634157787265899298076885757810027052577558601833654377569492440802512007040037959957131119219596589604805540830949143546491374792589297808288495092100739867082031373151027650695001922946050227447487627157971036846942412387783503561528766079982415312826572101611785443208074712405,
  327479277917408467359118278243034488056076247630130719693098679591209568603539525136273912089569344449019920319495285561697522348095392811331331240221415944707369595257330459289632194594578979695157867955814655,
  183632267622891382779718862777337890176768437789250849134046269477221477242087806515921312485605712698371734994876781313363032641283387305168655,
  113427455640312821154458202477256070485,
  1684641406969115364874486225963184091504279981394597057304974334423198082012594085395335671627782269635974753234311105849883066826689934540267397107598739745340130446522310749429691706754229252102351376690654656563612029603792517803755816029321629455,
  478611500756798850801714011323471660170568768659788346620398081151254972618377633362909867462188365193808315833746849196845099826791196907804893604951762174510088758215373707240627875944495525099088412524971307892190284093278822273880968004004958098409062655
]
def allOnes : Nat := 179769313486231590772930519078902473361797697894230657273430081157732675805500963132708477322407536021120113879871393357658789768814416622492847430639474124377767893424865485276302219601246094119453082952085005768838150682342462881473913110540827237163350510684586298239947245938479716304835356329624224137215
lemma lowPointWords_spec (p : Fin 10) :
    lowPointWords.getD p.val 0 = PackedColumns.col 10 p.val := by
  fin_cases p
  · exact Q3PackedColumnCache.col_10_0.symm
  · exact Q3PackedColumnCache.col_10_1.symm
  · exact Q3PackedColumnCache.col_10_2.symm
  · exact Q3PackedColumnCache.col_10_3.symm
  · exact Q3PackedColumnCache.col_10_4.symm
  · exact Q3PackedColumnCache.col_10_5.symm
  · exact Q3PackedColumnCache.col_10_6.symm
  · exact Q3PackedColumnCache.col_10_7.symm
  · exact Q3PackedColumnCache.col_10_8.symm
  · exact Q3PackedColumnCache.col_10_9.symm
lemma low_point_bits (r : Fin 1024) (p : Fin 10) :
    (lowPointWords.getD p.val 0).testBit r.val = r.val.testBit p.val := by
  rw [lowPointWords_spec]
  exact PackedColumns.col_testBit_lt 10 p.val r.val p.isLt r.isLt
lemma allOnes_spec : allOnes = 2 ^ (2 ^ 10) - 1 := by
  rw [Q3PackedColumnCache.power_10]
  rfl
lemma allOnes_bits (r : Fin 1024) : allOnes.testBit r.val = true := by
  rw [allOnes_spec, Nat.testBit_two_pow_sub_one]
  simp [r.isLt]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma low_line_complement : ∀ l : Fin 13,
    lowLineWords.getD l.val 0 + PackedLineColumns.joinWords
      (List.ofFn (fun p : Fin 10 => if I (Fin.castAdd 3 p) l
        then lowPointWords.getD p.val 0 else 0)) + 1 = 2 ^ (2 ^ 10) := by
  rw [Q3PackedColumnCache.power_10]
  decide +kernel
lemma low_line_bits (r : Fin 1024) (l : Fin 13) :
    (lowLineWords.getD l.val 0).testBit r.val =
      decide (∀ p : Fin 10, I (Fin.castAdd 3 p) l → r.val.testBit p.val = false) := by
  exact PackedLineArithmetic.line_bits (fun p : Fin 10 => I (Fin.castAdd 3 p))
    (fun p => lowPointWords.getD p.val 0) r l _ (low_line_complement l) (low_point_bits r)
def data (h : Fin 8) (i : Fin 26) : Nat :=
  Fin.addCases (motive := fun _ => Nat)
    (fun p : Fin 13 => Fin.addCases (motive := fun _ => Nat)
      (fun p : Fin 10 => lowPointWords.getD p.val 0)
      (fun p : Fin 3 => if h.val.testBit p.val then allOnes else 0) p)
    (fun l : Fin 13 => if ∀ p : Fin 3,
        I (Fin.natAdd 10 p) l → h.val.testBit p.val = false
      then lowLineWords.getD l.val 0 else 0) i
def words (h : Fin 8) : List Nat := List.ofFn (data h)
lemma words_length (h : Fin 8) : (words h).length = 26 := by simp [words]
lemma words_getD (h : Fin 8) (i : Fin 26) : (words h).getD i.val 0 = data h i := by
  simp only [words, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
    i.isLt, dite_eq_left, Option.getD_some]
lemma low_lookup (h : Fin 8) (p : Fin 10) :
    (words h).getD p.val 0 = lowPointWords.getD p.val 0 := by
  simpa [data] using words_getD h (Fin.castAdd 13 (Fin.castAdd 3 p))
lemma high_lookup (h : Fin 8) (p : Fin 3) :
    (words h).getD (10 + p.val) 0 = if h.val.testBit p.val then allOnes else 0 := by
  simpa [data] using words_getD h (Fin.castAdd 13 (Fin.natAdd 10 p))
lemma line_lookup (h : Fin 8) (l : Fin 13) :
    (words h).getD (13 + l.val) 0 = if ∀ p : Fin 3,
        I (Fin.natAdd 10 p) l → h.val.testBit p.val = false
      then lowLineWords.getD l.val 0 else 0 := by
  have hw := words_getD h (Fin.natAdd 13 l)
  simp only [data, Fin.addCases_right] at hw
  exact hw
lemma low_bits (h : Fin 8) (r : Fin 1024) (p : Fin 10) :
    ((words h).getD p.val 0).testBit r.val = r.val.testBit p.val := by
  rw [low_lookup]
  exact low_point_bits r p
lemma high_bits (h : Fin 8) (r : Fin 1024) (p : Fin 3) :
    ((words h).getD (10 + p.val) 0).testBit r.val = h.val.testBit p.val := by
  rw [high_lookup]
  cases h.val.testBit p.val <;> simp [allOnes_bits r]
lemma line_bits (h : Fin 8) (r : Fin 1024) (l : Fin 13) :
    ((words h).getD (13 + l.val) 0).testBit r.val = decide
      ((∀ p : Fin 10, I (Fin.castAdd 3 p) l → r.val.testBit p.val = false) ∧
        (∀ p : Fin 3, I (Fin.natAdd 10 p) l → h.val.testBit p.val = false)) := by
  rw [line_lookup]
  split
  · rename_i hh
    rw [low_line_bits r l]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact (and_iff_left hh).symm
  · rename_i hh
    simp [hh]
lemma negative_of_chunks (C : Circuit) (hAO : IsAO2 26 C)
    (hneg : ∀ h : Fin 8, PackedEval.eval C (words h) = 0) :
    ∀ P : Finset (Fin 13), circuitFun 26 C (liftInput (independentInput I P)) = false := by
  exact ChunkedBoundary.independent_false_of_chunks (a := 10) (b := 3)
    I C hAO words words_length low_bits high_bits line_bits hneg
lemma exact_of_chunks (C : Circuit) (hAO : IsAO2 26 C)
    (hpos : PackedEval.eval C pairWords = incidenceMask)
    (hneg : ∀ h : Fin 8, PackedEval.eval C (words h) = 0) :
    ∀ z : Fin 26 → Bool, circuitFun 26 C z = decide (∃ p l : Fin 13,
      I p l ∧ z (Fin.castAdd 13 p) = true ∧ z (Fin.natAdd 13 l) = true) := by
  exact ao2_exact_certificate I C hAO (Q3PackedCertificate.positive_of_packed C hAO hpos)
    (fun P _ => negative_of_chunks C hAO hneg P)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma canonical_checks : IsAO2 26 canonicalC ∧ canonicalC.size = 64 ∧
    PackedEval.eval canonicalC pairWords = incidenceMask ∧
    (∀ h : Fin 8, PackedEval.eval canonicalC (words h) = 0) := by decide +kernel
lemma canonical_exact : ∀ z : Fin 26 → Bool, circuitFun 26 canonicalC z =
    decide (∃ p l : Fin 13, I p l ∧ z (Fin.castAdd 13 p) = true ∧ z (Fin.natAdd 13 l) = true) :=
  exact_of_chunks canonicalC canonical_checks.1 canonical_checks.2.2.1 canonical_checks.2.2.2
end Q3ChunkedCertificate
end PEqualNP.Outside.L_meta_2583
