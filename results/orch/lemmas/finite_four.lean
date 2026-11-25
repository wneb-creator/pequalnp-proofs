import PEqualNP.Defs
import Mathlib.Tactic

namespace PEqualNP.Outside.L_meta_3451.Four

abbrev Mask := BitVec 16

def inputs : List Mask := [43690, 52428, 61680, 65280]

def choices (xs : List Mask) : List Mask :=
  (0 :: 65535 :: xs ++ xs.flatMap (fun a => xs.flatMap (fun b => [a &&& b, a ||| b]))).eraseDups

def possible : ℕ → List Mask → Mask → Bool
  | 0, xs, t => t == 0 || xs.contains t
  | k + 1, xs, t => (t == 0 || xs.contains t) ||
    (choices xs).any (fun a => possible k (xs ++ [a]) t)

def target (r : Fin 16) : Mask :=
  ([0, 41120, 43520, 43680, 49344, 57568, 60096, 60128,
    52224, 60576, 60928, 61088, 52416, 60640, 61120, 61152] : List Mask).getD r.val 0

def bound (r : Fin 16) : ℕ :=
  [0, 1, 1, 2, 1, 2, 3, 4, 1, 3, 2, 4, 2, 4, 4, 3].getD r.val 0

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma mem_choices_zero (xs : List Mask) : (0 : Mask) ∈ choices xs := by
  simp [choices]

lemma mem_choices_top (xs : List Mask) : BitVec.allOnes 16 ∈ choices xs := by
  have ht : BitVec.allOnes 16 = (65535 : Mask) := rfl
  simp [choices, ht]

lemma mem_choices_of_mem (xs : List Mask) (a : Mask) (ha : a ∈ xs) : a ∈ choices xs := by
  simp [choices, ha]

lemma mem_choices_and (xs : List Mask) (a b : Mask) (ha : a ∈ xs) (hb : b ∈ xs) :
    a &&& b ∈ choices xs := by
  simp only [choices, List.mem_eraseDups, List.mem_cons, List.mem_append, List.mem_flatMap,
    List.not_mem_nil, or_false]
  exact Or.inr ⟨a, ha, b, hb, Or.inl rfl⟩

lemma mem_choices_or (xs : List Mask) (a b : Mask) (ha : a ∈ xs) (hb : b ∈ xs) :
    a ||| b ∈ choices xs := by
  simp only [choices, List.mem_eraseDups, List.mem_cons, List.mem_append, List.mem_flatMap,
    List.not_mem_nil, or_false]
  exact Or.inr ⟨a, ha, b, hb, Or.inr rfl⟩

lemma possible_now (k : ℕ) (xs : List Mask) (t : Mask) (h : t = 0 ∨ t ∈ xs) :
    possible k xs t = true := by
  cases k <;> simp_all [possible]

lemma possible_step (k : ℕ) (xs : List Mask) (a t : Mask)
    (ha : a ∈ choices xs) (h : possible k (xs ++ [a]) t = true) :
    possible (k + 1) xs t = true := by
  simp only [possible, Bool.or_eq_true, List.any_eq_true]
  exact Or.inr ⟨a, ha, h⟩

lemma possible_mono (k l : ℕ) (hkl : k ≤ l) (xs : List Mask) (t : Mask)
    (h : possible k xs t = true) : possible l xs t = true := by
  induction k generalizing l xs with
  | zero =>
    apply possible_now
    simpa [possible] using h
  | succ k ih =>
    cases l with
    | zero => omega
    | succ l =>
      simp only [possible, Bool.or_eq_true, List.any_eq_true] at h ⊢
      rcases h with h | ⟨a, ha, ht⟩
      · exact Or.inl h
      · exact Or.inr ⟨a, ha, ih l (by omega) _ ht⟩

def opTable (op : GateOp) (xs : List Mask) : Mask :=
  match op with
  | .and => xs.foldr (· &&& ·) (BitVec.allOnes 16)
  | .or => xs.foldr (· ||| ·) 0
  | _ => 0

def gateTable (g : Gate) (xs : List Mask) : Mask :=
  opTable g.op (g.inputs.map (fun i => xs.getD i 0))

def runTable (gs : List Gate) (xs : List Mask) : List Mask :=
  gs.foldl (fun w g => w ++ [gateTable g w]) xs

lemma lookup_mem (xs : List Mask) (i : ℕ) (hi : i < xs.length) : xs.getD i 0 ∈ xs := by
  rw [List.getD_eq_getElem xs 0 hi]
  exact List.getElem_mem hi

lemma or_bottom (a : Mask) : a ||| (0 : Mask) = a := BitVec.or_zero

lemma gateTable_mem (g : Gate) (xs : List Mask)
    (hop : g.op = .and ∨ g.op = .or) (hlen : g.inputs.length ≤ 2)
    (hback : ∀ i ∈ g.inputs, i < xs.length) : gateTable g xs ∈ choices xs := by
  rcases g with ⟨op, ins⟩
  simp only at hop hlen hback
  cases ins with
  | nil =>
    rcases hop with rfl | rfl
    · exact mem_choices_top xs
    · exact mem_choices_zero xs
  | cons a rest =>
    have ha := lookup_mem xs a (hback a (by simp))
    cases rest with
    | nil =>
      rcases hop with rfl | rfl <;>
        simpa only [gateTable, opTable, List.map_cons, List.map_nil, List.foldr_cons,
          List.foldr_nil, BitVec.and_allOnes, or_bottom] using mem_choices_of_mem xs _ ha
    | cons b rest =>
      have hb := lookup_mem xs b (hback b (by simp))
      have hr : rest = [] := by simpa using hlen
      subst rest
      rcases hop with rfl | rfl
      · simpa only [gateTable, opTable, List.map_cons, List.map_nil, List.foldr_cons,
          List.foldr_nil, BitVec.and_allOnes, or_bottom] using mem_choices_and xs _ _ ha hb
      · simpa only [gateTable, opTable, List.map_cons, List.map_nil, List.foldr_cons,
          List.foldr_nil, BitVec.and_allOnes, or_bottom] using mem_choices_or xs _ _ ha hb

lemma runTable_possible (gs : List Gate) (xs : List Mask)
    (hop : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    (hlen : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (hback : ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨.or, []⟩).inputs, i < xs.length + j)
    (out : ℕ) : possible gs.length xs ((runTable gs xs).getD out 0) = true := by
  induction gs generalizing xs with
  | nil =>
    apply possible_now
    by_cases ho : out < xs.length
    · exact Or.inr (lookup_mem xs out ho)
    · exact Or.inl (List.getD_eq_default xs 0 (by omega))
  | cons g gs ih =>
    have hg := gateTable_mem g xs (hop g (by simp)) (hlen g (by simp)) (by
      simpa using hback 0 (by simp))
    apply possible_step gs.length xs (gateTable g xs) _ hg
    apply ih
    · intro g hg; exact hop g (by simp [hg])
    · intro g hg; exact hlen g (by simp [hg])
    · intro j hj i hi
      have hb := hback (j + 1) (by simp; omega) i (by simpa using hi)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb

def outputTable (C : Circuit) : Mask := (runTable C.gates inputs).getD C.output 0

lemma output_possible (C : Circuit) (hm : Monotone2 C) (hb : NestedCover.ReadsBack 4 C) :
    possible C.size inputs (outputTable C) = true := by
  apply runTable_possible C.gates inputs
  · intro g hg; simpa using (hm g hg).1
  · intro g hg; exact (hm g hg).2
  · exact hb

lemma getD_bits (xs : List Mask) (a : Fin 16) (i : ℕ) :
    (xs.map (fun v => v.getLsbD a.val)).getD i false = (xs.getD i 0).getLsbD a.val := by
  simpa using List.getD_map xs (0 : Mask) (fun v => v.getLsbD a.val) (n := i)

lemma and_bits (xs : List Mask) (a : Fin 16) :
    (xs.foldr (· &&& ·) (BitVec.allOnes 16)).getLsbD a.val =
      (xs.map (fun v => v.getLsbD a.val)).all id := by
  induction xs with
  | nil => simp only [List.foldr_nil, BitVec.getLsbD_allOnes, a.isLt, decide_true,
      List.map_nil, List.all_nil]
  | cons x xs ih =>
    simp only [List.foldr_cons, BitVec.getLsbD_and, ih, List.map_cons, List.all_cons, id_eq]

lemma or_bits (xs : List Mask) (a : Fin 16) :
    (xs.foldr (· ||| ·) 0).getLsbD a.val =
      (xs.map (fun v => v.getLsbD a.val)).any id := by
  induction xs with
  | nil => exact BitVec.getLsbD_zero
  | cons x xs ih =>
    simp only [List.foldr_cons, BitVec.getLsbD_or, ih, List.map_cons, List.any_cons, id_eq]

lemma gate_bits (g : Gate) (xs : List Mask) (a : Fin 16)
    (hop : g.op = .and ∨ g.op = .or) :
    (gateTable g xs).getLsbD a.val =
      g.op.eval (g.inputs.map (fun i => (xs.map (fun v => v.getLsbD a.val)).getD i false)) := by
  rcases g with ⟨op, ins⟩
  rcases hop with rfl | rfl
  · simp only [gateTable, opTable, and_bits, List.map_map, getD_bits, GateOp.eval,
      Function.comp_def]
  · simp only [gateTable, opTable, or_bits, List.map_map, getD_bits, GateOp.eval,
      Function.comp_def]

def runBool (gs : List Gate) (xs : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]) xs

lemma run_bits (gs : List Gate) (xs : List Mask) (a : Fin 16)
    (hop : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) :
    (runTable gs xs).map (fun v => v.getLsbD a.val) =
      runBool gs (xs.map (fun v => v.getLsbD a.val)) := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    change (runTable gs (xs ++ [gateTable g xs])).map (fun v => v.getLsbD a.val) = _
    rw [ih _ (fun g hg => hop g (by simp [hg]))]
    simp only [List.map_append, List.map_singleton, gate_bits g xs a (hop g (by simp))]
    rfl

def assignment (a : Fin 16) (i : Fin 4) : Bool :=
  (inputs.getD i.val 0).getLsbD a.val

lemma input_bits (a : Fin 16) : inputs.map (fun v => v.getLsbD a.val) =
    List.ofFn (assignment a) := by
  simp [inputs, assignment, List.ofFn_succ]

lemma output_bits (C : Circuit) (hm : Monotone2 C) (a : Fin 16) :
    (outputTable C).getLsbD a.val = circuitFun 4 C (assignment a) := by
  have hr := run_bits C.gates inputs a (fun g hg => by simpa using (hm g hg).1)
  rw [input_bits] at hr
  have hg := congrArg (fun xs : List Bool => xs.getD C.output false) hr
  rw [getD_bits] at hg
  exact hg

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma target_bits : ∀ r a : Fin 16,
    (target r).getLsbD a.val =
      ((r.val.testBit 0 && assignment a 0 && assignment a 2) ||
       (r.val.testBit 1 && assignment a 0 && assignment a 3) ||
       (r.val.testBit 2 && assignment a 1 && assignment a 2) ||
       (r.val.testBit 3 && assignment a 1 && assignment a 3)) := by
  decide +kernel

set_option maxHeartbeats 2000000 in
lemma lower_bound_with_certificate
    (cert : ∀ r : Fin 16, 0 < bound r → possible (bound r - 1) inputs (target r) = false)
    (r : Fin 16) (C : Circuit) (hm : Monotone2 C) (hb : NestedCover.ReadsBack 4 C)
    (hs : ∀ a : Fin 16, circuitFun 4 C (assignment a) = (target r).getLsbD a.val) :
    bound r ≤ C.size := by
  by_contra hbound
  have hp : 0 < bound r := by omega
  have ho : outputTable C = target r := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    exact (output_bits C hm ⟨i, hi⟩).trans (hs ⟨i, hi⟩)
  have hpossible : possible C.size inputs (target r) = true := ho ▸ output_possible C hm hb
  have hsmall := possible_mono C.size (bound r - 1) (by omega) inputs (target r) hpossible
  exact Bool.false_ne_true ((cert r hp).symm.trans hsmall)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma certificate : ∀ r : Fin 16, 0 < bound r →
    possible (bound r - 1) inputs (target r) = false := by
  decide +kernel

lemma lower_bound (r : Fin 16) (C : Circuit)
    (hm : Monotone2 C) (hb : NestedCover.ReadsBack 4 C)
    (hs : ∀ a : Fin 16, circuitFun 4 C (assignment a) = (target r).getLsbD a.val) :
    bound r ≤ C.size :=
  lower_bound_with_certificate certificate r C hm hb hs

end PEqualNP.Outside.L_meta_3451.Four
