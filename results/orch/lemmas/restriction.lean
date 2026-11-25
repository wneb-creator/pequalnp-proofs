import PEqualNP.Defs
import Mathlib.Tactic

namespace PEqualNP.Outside.L_meta_3451.Restriction

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma any_filterMap {α β : Type} (f : α → Option β) (g : β → Bool) (xs : List α) :
    (xs.filterMap f).any g = xs.any (fun x => ((f x).map g).getD false) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases ha : f a <;> simp [ha, ih]

lemma all_filterMap {α β : Type} (f : α → Option β) (g : β → Bool) (xs : List α) :
    xs.all (fun x => ((f x).map g).getD false) =
      if xs.any (fun x => (f x).isNone) then false else (xs.filterMap f).all g := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases ha : f a with
    | none => simp [ha]
    | some b =>
      simp only [List.all_cons, ha, Option.map_some, Option.getD_some, List.any_cons,
        Option.isNone_some, Bool.false_or, List.filterMap_cons]
      rw [ih]
      split <;> simp_all

def wireMap {m n : ℕ} (ρ : Fin m → Option (Fin n)) (w : ℕ) : Option ℕ :=
  if h : w < m then (ρ ⟨w, h⟩).map Fin.val else some (n + (w - m))

def gate {m n : ℕ} (ρ : Fin m → Option (Fin n)) (g : Gate) : Gate :=
  match g.op with
  | .and =>
    if g.inputs.any (fun w => (wireMap ρ w).isNone) then ⟨.or, []⟩
    else ⟨.and, g.inputs.filterMap (wireMap ρ)⟩
  | op => ⟨op, g.inputs.filterMap (wireMap ρ)⟩

def circuit {m n : ℕ} (ρ : Fin m → Option (Fin n)) (C : Circuit) : Circuit :=
  ⟨C.gates.map (gate ρ), (wireMap ρ C.output).getD (n + C.size)⟩

def input {m n : ℕ} (ρ : Fin m → Option (Fin n)) (z : Fin n → Bool) : Fin m → Bool :=
  fun i => ((ρ i).map z).getD false

lemma wireMap_last {m n : ℕ} (ρ : Fin m → Option (Fin n)) (i t : ℕ) :
    wireMap ρ i = some (n + t) ↔ i = m + t := by
  unfold wireMap
  split_ifs with hi
  · cases hρ : ρ ⟨i, hi⟩ with
    | none => simp; omega
    | some k => simp only [Option.map_some, Option.some.injEq]; omega
  · simp only [Option.some.injEq]
    omega

lemma gate_value {m n : ℕ} (ρ : Fin m → Option (Fin n)) (g : Gate)
    (xs ys : List Bool) (hop : g.op = .and ∨ g.op = .or)
    (hxy : ∀ i, xs.getD i false = ((wireMap ρ i).map (fun j => ys.getD j false)).getD false) :
    g.op.eval (g.inputs.map (fun i => xs.getD i false)) =
      (gate ρ g).op.eval ((gate ρ g).inputs.map (fun i => ys.getD i false)) := by
  rcases g with ⟨op, ins⟩
  simp only at hop
  rcases hop with rfl | rfl
  · simp only [gate]
    split_ifs with hnone
    · simp only [GateOp.eval, List.all_map, List.map_nil, List.any_nil]
      simp only [Function.id_comp]
      simp_rw [hxy]
      rw [all_filterMap]
      simp [hnone]
    · simp only [GateOp.eval, List.all_map]
      simp only [Function.id_comp]
      simp_rw [hxy]
      rw [all_filterMap]
      simp [hnone]
  · simp only [gate, GateOp.eval, List.any_map]
    simp_rw [hxy]
    exact (any_filterMap _ _ _).symm

lemma getD_snoc {α : Type} (xs : List α) (a d : α) (i : ℕ) :
    (xs ++ [a]).getD i d = if i = xs.length then a else xs.getD i d := by
  by_cases hi : i < xs.length
  · rw [List.getD_append _ _ _ _ hi]
    simp [Nat.ne_of_lt hi]
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    by_cases he : i = xs.length
    · simp [he]
    · rw [List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by omega)]
      simp [he]

lemma extend_values {m n t : ℕ} (ρ : Fin m → Option (Fin n)) (xs ys : List Bool)
    (hx : xs.length = m + t) (hy : ys.length = n + t)
    (hxy : ∀ i, xs.getD i false = ((wireMap ρ i).map (fun j => ys.getD j false)).getD false)
    (b : Bool) :
    ∀ i, (xs ++ [b]).getD i false =
      ((wireMap ρ i).map (fun j => (ys ++ [b]).getD j false)).getD false := by
  intro i
  rw [getD_snoc]
  by_cases hi : i = m + t
  · have hm := (wireMap_last ρ i t).mpr hi
    rw [ite_eq_left (hi.trans hx.symm), hm]
    simp only [Option.map_some, Option.getD_some]
    rw [getD_snoc, hy, ite_eq_left rfl]
  · simp only [hx, hi, ↓reduceIte]
    rw [hxy]
    cases hm : wireMap ρ i with
    | none => rfl
    | some j =>
      have hj : j ≠ n + t := by
        intro he
        apply hi
        apply (wireMap_last ρ i t).mp
        simpa [he] using hm
      simp only [Option.map_some, Option.getD_some]
      rw [getD_snoc, hy, ite_eq_right hj]

def run (gs : List Gate) (xs : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]) xs

lemma run_length (gs : List Gate) (xs : List Bool) :
    (run gs xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp [run]
  | cons g gs ih =>
    simp only [run, List.foldl_cons] at *
    rw [ih]
    simp
    omega

lemma initial_values {m n : ℕ} (ρ : Fin m → Option (Fin n)) (z : Fin n → Bool) :
    ∀ i, (List.ofFn (input ρ z)).getD i false =
      ((wireMap ρ i).map (fun j => (List.ofFn z).getD j false)).getD false := by
  intro i
  by_cases hi : i < m
  · cases hr : ρ ⟨i, hi⟩ with
    | none => simp [input, wireMap, hi, hr, List.getD_eq_getElem?_getD]
    | some j => simp [input, wireMap, hi, hr, List.getD_eq_getElem?_getD]
  · have hni : ¬ n + (i - m) < n := by omega
    simp [wireMap, hi, hni, List.getD_eq_getElem?_getD]

lemma run_values {m n : ℕ} (ρ : Fin m → Option (Fin n)) (gs : List Gate)
    (hop : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    (t : ℕ) (xs ys : List Bool) (hx : xs.length = m + t) (hy : ys.length = n + t)
    (hxy : ∀ i, xs.getD i false = ((wireMap ρ i).map (fun j => ys.getD j false)).getD false) :
    ∀ i, (run gs xs).getD i false =
      ((wireMap ρ i).map (fun j => (run (gs.map (gate ρ)) ys).getD j false)).getD false := by
  induction gs generalizing t xs ys with
  | nil => exact hxy
  | cons g gs ih =>
    have hv := gate_value ρ g xs ys (hop g (by simp)) hxy
    change ∀ i, (run gs (xs ++ [g.op.eval (g.inputs.map (fun j => xs.getD j false))])).getD i false = _
    apply ih (fun g hg => hop g (by simp [hg])) (t + 1)
    · simp [hx]
      omega
    · simp [hy]
      omega
    · dsimp only
      rw [← hv]
      exact extend_values ρ xs ys hx hy hxy _

lemma wires {m n : ℕ} (ρ : Fin m → Option (Fin n)) (C : Circuit)
    (hmono : Monotone2 C) (z : Fin n → Bool) :
    ∀ i, (C.wires (List.ofFn (input ρ z))).getD i false =
      ((wireMap ρ i).map (fun j => ((circuit ρ C).wires (List.ofFn z)).getD j false)).getD false := by
  apply run_values ρ C.gates _ 0 (List.ofFn (input ρ z)) (List.ofFn z)
    (by simp) (by simp) (initial_values ρ z)
  intro g hg
  simpa using (hmono g hg).1

lemma size {m n : ℕ} (ρ : Fin m → Option (Fin n)) (C : Circuit) :
    (circuit ρ C).size = C.size := by
  simp [circuit, Circuit.size]

lemma mono {m n : ℕ} (ρ : Fin m → Option (Fin n)) (C : Circuit)
    (hmono : Monotone2 C) : Monotone2 (circuit ρ C) := by
  intro g hg
  obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
  have hm := hmono g0 hg0
  have hop : g0.op = .and ∨ g0.op = .or := by simpa using hm.1
  have hlen := List.length_filterMap_le (f := wireMap ρ) (l := g0.inputs)
  rcases g0 with ⟨op, ins⟩
  simp only at hop hm hlen
  rcases hop with rfl | rfl
  · simp only [gate]
    split_ifs <;> simp_all
    omega
  · simp only [gate]
    simp_all
    omega

lemma eval {m n : ℕ} (ρ : Fin m → Option (Fin n)) (C : Circuit)
    (hmono : Monotone2 C) (z : Fin n → Bool) :
    circuitFun n (circuit ρ C) z = circuitFun m C (input ρ z) := by
  have hv := wires ρ C hmono z C.output
  change ((circuit ρ C).wires (List.ofFn z)).getD (wireMap ρ C.output |>.getD (n + C.size)) false = _
  cases ho : wireMap ρ C.output with
  | some j => simpa only [ho, Option.map_some, Option.getD_some, circuitFun, Circuit.eval] using hv.symm
  | none =>
    have hl : ((circuit ρ C).wires (List.ofFn z)).length = n + C.size := by
      change (run (C.gates.map (gate ρ)) (List.ofFn z)).length = _
      simp [run_length, Circuit.size]
    simp only [Option.getD_none]
    rw [List.getD_eq_default _ _ hl.le]
    simpa only [ho, Option.map_none, Option.getD_none, circuitFun, Circuit.eval] using hv.symm

lemma gate_value_at {m n : ℕ} (ρ : Fin m → Option (Fin n)) (C : Circuit)
    (hmono : Monotone2 C) (z : Fin n → Bool) (j : ℕ) :
    PEqualNP.EdgeOwnership.gateVal n (circuit ρ C) j z =
      PEqualNP.EdgeOwnership.gateVal m C j (input ρ z) := by
  have hv := wires ρ C hmono z (m + j)
  have hm := (wireMap_last ρ (m + j) j).mpr rfl
  simpa only [hm, Option.map_some, Option.getD_some, PEqualNP.EdgeOwnership.gateVal] using hv.symm

lemma input_mem {m n : ℕ} (ρ : Fin m → Option (Fin n)) (g : Gate) (i : ℕ)
    (hi : i ∈ (gate ρ g).inputs) : ∃ w ∈ g.inputs, wireMap ρ w = some i := by
  rcases g with ⟨op, ins⟩
  cases op <;> simp only [gate] at hi
  · split_ifs at hi with hnone
    · simp at hi
    · exact List.mem_filterMap.mp hi
  all_goals exact List.mem_filterMap.mp hi

lemma mapped_lt {m n : ℕ} (ρ : Fin m → Option (Fin n)) (w i t : ℕ)
    (hw : w < m + t) (hi : wireMap ρ w = some i) : i < n + t := by
  unfold wireMap at hi
  split_ifs at hi with hm
  · cases hρ : ρ ⟨w, hm⟩ with
    | none => simp [hρ] at hi
    | some k => simp only [hρ, Option.map_some, Option.some.injEq] at hi; omega
  · simp only [Option.some.injEq] at hi
    omega

lemma gate_at {m n : ℕ} (ρ : Fin m → Option (Fin n)) (C : Circuit) (j : ℕ) :
    NestedCover.gateAt (circuit ρ C) j = gate ρ (NestedCover.gateAt C j) := by
  exact List.getD_map C.gates ⟨.or, []⟩ (gate ρ)

lemma readsBack {m n : ℕ} (ρ : Fin m → Option (Fin n)) (C : Circuit)
    (hback : NestedCover.ReadsBack m C) : NestedCover.ReadsBack n (circuit ρ C) := by
  intro j hj i hi
  rw [gate_at] at hi
  obtain ⟨w, hw, hmap⟩ := input_mem ρ _ i hi
  have hj' : j < C.gates.length := by simpa [circuit] using hj
  exact mapped_lt ρ w i j (hback j hj' w hw) hmap

lemma gate_and_origin {m n : ℕ} (ρ : Fin m → Option (Fin n)) (g : Gate)
    (h : (gate ρ g).op = .and) : g.op = .and := by
  rcases g with ⟨op, ins⟩
  cases op <;> simp_all [gate]

lemma and_origin {m n : ℕ} (ρ : Fin m → Option (Fin n)) (C : Circuit) (j : ℕ)
    (h : (NestedCover.gateAt (circuit ρ C) j).op = .and) :
    (NestedCover.gateAt C j).op = .and := by
  rw [gate_at] at h
  exact gate_and_origin ρ _ h

lemma rejects {m n : ℕ} (ρ : Fin m → Option (Fin n)) (C : Circuit)
    (hmono : Monotone2 C) (z : Fin n → Bool)
    (h : ∀ j < C.gates.length, (NestedCover.gateAt C j).op = .and →
      PEqualNP.EdgeOwnership.gateVal m C j (input ρ z) = false) :
    ∀ j < (circuit ρ C).gates.length, (NestedCover.gateAt (circuit ρ C) j).op = .and →
      PEqualNP.EdgeOwnership.gateVal n (circuit ρ C) j z = false := by
  intro j hj hand
  rw [gate_value_at ρ C hmono z j]
  exact h j (by simpa [circuit] using hj) (and_origin ρ C j hand)

end PEqualNP.Outside.L_meta_3451.Restriction
