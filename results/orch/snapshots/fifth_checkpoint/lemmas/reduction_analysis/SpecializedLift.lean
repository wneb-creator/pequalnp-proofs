import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_650

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def liftRun (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

def liftIndex (n m : ℕ) (f : Fin n → Fin m) (i : ℕ) : ℕ :=
  if h : i < n then (f ⟨i, h⟩).val else m + (i - n)

def liftedGate (n m : ℕ) (f : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (liftIndex n m f)⟩

lemma lift_snoc_read (w : List Bool) (v : Bool) (i : ℕ) :
    (w ++ [v]).getD i false = if i = w.length then v else w.getD i false := by
  induction w generalizing i with
  | nil => cases i <;> rfl
  | cons b w ih =>
    cases i with
    | zero => rfl
    | succ i => simpa using ih i

lemma liftIndex_level (n m : ℕ) (f : Fin n → Fin m) (k i : ℕ) :
    liftIndex n m f i = m + k ↔ i = n + k := by
  unfold liftIndex
  split <;> rename_i h
  · have bound := (f ⟨i, h⟩).isLt
    omega
  · omega

lemma liftRun_equiv (n m : ℕ) (f : Fin n → Fin m) (gs : List Gate)
    (k : ℕ) (old new : List Bool)
    (oldlen : old.length = n + k) (newlen : new.length = m + k)
    (reads : ∀ i, new.getD (liftIndex n m f i) false = old.getD i false) :
    ∀ i, (liftRun (gs.map (liftedGate n m f)) new).getD (liftIndex n m f i) false =
      (liftRun gs old).getD i false := by
  induction gs generalizing k old new with
  | nil => exact reads
  | cons g gs ih =>
    let value := g.op.eval (g.inputs.map fun i => old.getD i false)
    have same : g.op.eval (g.inputs.map fun i => new.getD (liftIndex n m f i) false) = value := by
      congr 1
      apply List.map_congr_left
      intro i _
      exact reads i
    have next : ∀ i,
        (new ++ [value]).getD (liftIndex n m f i) false = (old ++ [value]).getD i false := by
      intro i
      simp only [lift_snoc_read, oldlen, newlen, liftIndex_level, reads]
    have proof := ih (k + 1) (old ++ [value]) (new ++ [value])
      (by simp [oldlen]; omega) (by simp [newlen]; omega) next
    simpa only [liftRun, List.map_cons, List.foldl_cons, liftedGate,
      List.map_map, Function.comp_def, same] using proof

def liftedCircuit (n m : ℕ) (f : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (liftedGate n m f), liftIndex n m f C.output⟩

lemma liftedCircuit_size (n m : ℕ) (f : Fin n → Fin m) (C : Circuit) :
    (liftedCircuit n m f C).size = C.size := by
  simp [liftedCircuit, Circuit.size]

lemma liftedCircuit_monotone (n m : ℕ) (f : Fin n → Fin m) (C : Circuit)
    (hm : Monotone2 C) : Monotone2 (liftedCircuit n m f C) := by
  intro g hg
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
  obtain ⟨op, arity⟩ := hm a ha
  exact ⟨op, by simpa [liftedGate] using arity⟩

lemma liftedCircuit_eval (n m : ℕ) (f : Fin n → Fin m) (C : Circuit)
    (x : Fin m → Bool) :
    (liftedCircuit n m f C).eval (List.ofFn x) =
      C.eval (List.ofFn fun i : Fin n => x (f i)) := by
  apply liftRun_equiv n m f C.gates 0 _ _ (by simp) (by simp)
  intro i
  by_cases h : i < n
  · simp [liftIndex, h, List.getD_eq_getElem?_getD]
  · have hm : m ≤ liftIndex n m f i := by simp [liftIndex, h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simpa using hm),
      List.getElem?_eq_none (by simp only [List.length_ofFn]; omega)]

lemma liftRun_length (gs : List Gate) (x : List Bool) :
    (liftRun gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    simp only [liftRun, List.foldl_cons] at *
    rw [ih]
    simp
    omega

lemma liftRun_preserve (gs : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length) : (liftRun gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [liftRun, List.foldl_cons] at *
    rw [ih _ (by simp; omega)]
    exact List.getD_append _ _ _ _ hi

def starTail (start p a b c d out : ℕ) : List Gate :=
  [⟨.or, [a, b]⟩, ⟨.or, [start, c]⟩, ⟨.or, [start + 1, d]⟩,
    ⟨.and, [p, start + 2]⟩, ⟨.or, [out, start + 3]⟩]

lemma starTail_eval (w : List Bool) (p a b c d out : ℕ)
    (hp : p < w.length) (ha : a < w.length) (hb : b < w.length)
    (hc : c < w.length) (hd : d < w.length) (hout : out < w.length) :
    (liftRun (starTail w.length p a b c d out) w).getD (w.length + 4) false =
      (w.getD out false || (w.getD p false &&
        (w.getD a false || w.getD b false || w.getD c false || w.getD d false))) := by
  simp only [liftRun, starTail, List.foldl_cons, List.foldl_nil,
    List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
    List.any_cons, List.any_nil, id_eq, Bool.and_true, Bool.or_false]
  simp (disch := omega) only [lift_snoc_read, List.length_append, List.length_cons,
    List.length_nil, Nat.add_assoc, Nat.reduceAdd, Nat.add_left_cancel_iff,
    ite_eq_left, ite_eq_right, ite_true]

def appendStar (n : ℕ) (C : Circuit) (p a b c d : Fin n) : Circuit :=
  ⟨C.gates ++ starTail (n + C.size) p.val a.val b.val c.val d.val C.output,
    n + C.size + 4⟩

lemma appendStar_size (n : ℕ) (C : Circuit) (p a b c d : Fin n) :
    (appendStar n C p a b c d).size = C.size + 5 := by
  simp [appendStar, starTail, Circuit.size]

lemma appendStar_monotone (n : ℕ) (C : Circuit) (p a b c d : Fin n)
    (hm : Monotone2 C) : Monotone2 (appendStar n C p a b c d) := by
  intro g hg
  rcases List.mem_append.mp hg with old | fresh
  · exact hm g old
  · simp only [starTail, List.mem_cons, List.not_mem_nil, or_false] at fresh
    rcases fresh with rfl | rfl | rfl | rfl | rfl <;> simp

lemma appendStar_valid (n : ℕ) (C : Circuit) (p a b c d : Fin n) :
    (appendStar n C p a b c d).output < n + (appendStar n C p a b c d).size := by
  rw [appendStar_size]
  change n + C.size + 4 < _
  omega

lemma appendStar_eval (n : ℕ) (C : Circuit) (p a b c d : Fin n)
    (hout : C.output < n + C.size) (x : Fin n → Bool) :
    (appendStar n C p a b c d).eval (List.ofFn x) =
      (C.eval (List.ofFn x) || (x p && (x a || x b || x c || x d))) := by
  let w := C.wires (List.ofFn x)
  have len : w.length = n + C.size := by
    simpa only [w, Circuit.wires, Circuit.size, liftRun, List.length_ofFn]
      using liftRun_length C.gates (List.ofFn x)
  have input (i : Fin n) : w.getD i.val false = x i := by
    change (liftRun C.gates (List.ofFn x)).getD i.val false = _
    rw [liftRun_preserve _ _ _ (by simp)]
    simp
  change (liftRun (C.gates ++ starTail (n + C.size) p.val a.val b.val c.val d.val C.output)
    (List.ofFn x)).getD (n + C.size + 4) false = _
  have appendRun (gs hs : List Gate) (z : List Bool) :
      liftRun (gs ++ hs) z = liftRun hs (liftRun gs z) := by
    exact List.foldl_append
  rw [appendRun]
  change (liftRun (starTail (n + C.size) p.val a.val b.val c.val d.val C.output) w).getD
    (n + C.size + 4) false = _
  rw [← len, starTail_eval]
  · rw [input, input, input, input, input]
    rfl
  all_goals rw [len]
  · have := p.isLt; omega
  · have := a.isLt; omega
  · have := b.isLt; omega
  · have := c.isLt; omega
  · have := d.isLt; omega
  · exact hout

lemma liftedCircuit_valid (n m : ℕ) (f : Fin n → Fin m) (C : Circuit)
    (hout : C.output < n + C.size) :
    (liftedCircuit n m f C).output < m + (liftedCircuit n m f C).size := by
  rw [liftedCircuit_size]
  change liftIndex n m f C.output < m + C.size
  unfold liftIndex
  split <;> rename_i h
  · have := (f ⟨C.output, h⟩).isLt
    omega
  · omega

def rowValue {n : ℕ} (x : Fin n → Bool)
    (r : Fin n × Fin n × Fin n × Fin n × Fin n) : Bool :=
  x r.1 && (x r.2.1 || x r.2.2.1 || x r.2.2.2.1 || x r.2.2.2.2)

def appendRows (n : ℕ) (C : Circuit)
    (rows : List (Fin n × Fin n × Fin n × Fin n × Fin n)) : Circuit :=
  rows.foldl (fun D r => appendStar n D r.1 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2) C

lemma appendRows_size (n : ℕ) (C : Circuit)
    (rows : List (Fin n × Fin n × Fin n × Fin n × Fin n)) :
    (appendRows n C rows).size = C.size + 5 * rows.length := by
  induction rows generalizing C with
  | nil => simp [appendRows]
  | cons r rows ih =>
    simp only [appendRows, List.foldl_cons] at *
    rw [ih, appendStar_size]
    simp [List.length_cons]
    omega

lemma appendRows_monotone (n : ℕ) (C : Circuit)
    (rows : List (Fin n × Fin n × Fin n × Fin n × Fin n))
    (hm : Monotone2 C) : Monotone2 (appendRows n C rows) := by
  induction rows generalizing C with
  | nil => exact hm
  | cons r rows ih =>
    exact ih _ (appendStar_monotone _ _ _ _ _ _ _ hm)

lemma appendRows_valid (n : ℕ) (C : Circuit)
    (rows : List (Fin n × Fin n × Fin n × Fin n × Fin n))
    (hout : C.output < n + C.size) :
    (appendRows n C rows).output < n + (appendRows n C rows).size := by
  induction rows generalizing C with
  | nil => exact hout
  | cons r rows ih =>
    exact ih _ (appendStar_valid _ _ _ _ _ _ _)

lemma appendRows_eval (n : ℕ) (C : Circuit)
    (rows : List (Fin n × Fin n × Fin n × Fin n × Fin n))
    (hout : C.output < n + C.size) (x : Fin n → Bool) :
    (appendRows n C rows).eval (List.ofFn x) =
      (C.eval (List.ofFn x) || rows.any (rowValue x)) := by
  induction rows generalizing C with
  | nil => simp [appendRows]
  | cons r rows ih =>
    change (appendRows n (appendStar n C r.1 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2) rows).eval _ = _
    rw [ih _ (appendStar_valid _ _ _ _ _ _ _), appendStar_eval _ _ _ _ _ _ _ hout]
    simp only [List.any_cons, rowValue, Bool.or_assoc]

lemma lift_and_append (n m : ℕ) (f : Fin n → Fin m) (C : Circuit)
    (rows : List (Fin m × Fin m × Fin m × Fin m × Fin m))
    (hm : Monotone2 C) (hout : C.output < n + C.size) :
    ∃ D : Circuit, Monotone2 D ∧ D.size = C.size + 5 * rows.length ∧
      ∀ x : Fin m → Bool, D.eval (List.ofFn x) =
        (C.eval (List.ofFn fun i : Fin n => x (f i)) || rows.any (rowValue x)) := by
  refine ⟨appendRows m (liftedCircuit n m f C) rows,
    appendRows_monotone _ _ _ (liftedCircuit_monotone _ _ _ _ hm), ?_, ?_⟩
  · rw [appendRows_size, liftedCircuit_size]
  · intro x
    rw [appendRows_eval _ _ _ (liftedCircuit_valid _ _ _ _ hout), liftedCircuit_eval]




def input_k4_p2 : Fin 14 → Fin 26 := ![0, 1, 2, 5, 13, 14, 15, 16, 17, 20, 21, 22, 24, 25]

def function_k4_p2 (y : Fin 14 → Bool) : Bool :=
  (y 0 && (y 4 || y 5 || y 7 || y 11)) || (y 1 && (y 4 || y 6 || y 10 || y 13)) || (y 2 && (y 5 || y 9 || y 12 || y 13)) || (y 3 && (y 8 || y 10 || y 11 || y 12))

def remaining_k4_p2 : List (Fin 26 × Fin 26 × Fin 26 × Fin 26 × Fin 26) :=
  [(3, 13, 19, 23, 24), (4, 18, 22, 23, 25), (6, 16, 20, 21, 23), (7, 15, 19, 20, 22), (8, 14, 18, 19, 21), (9, 13, 17, 18, 20), (10, 16, 17, 19, 25), (11, 15, 16, 18, 24), (12, 14, 15, 17, 23)]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma complete_k4_p2 (C : Circuit) (mono : Monotone2 C) (size : C.size ≤ 18)
    (out : C.output < 14 + C.size)
    (correct : ∀ y : Fin 14 → Bool, C.eval (List.ofFn y) = function_k4_p2 y) :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 63 ∧ (∀ x : Fin 26 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 26, (u.val, v.val) ∈ ([(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25), (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24), (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24), (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22), (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20), (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24), (12, 14), (12, 15), (12, 17), (12, 23)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  obtain ⟨D, hm, hs, he⟩ := lift_and_append 14 26 input_k4_p2 C remaining_k4_p2 mono out
  refine ⟨D, hm, ?_, ?_⟩
  · have count : remaining_k4_p2.length = 9 := rfl
    rw [count] at hs
    omega
  · intro x
    rw [he, correct]
    simp [function_k4_p2, input_k4_p2, remaining_k4_p2, rowValue,
      Fin.exists_iff, Prod.mk.injEq, or_and_right, exists_or,
      and_assoc, and_or_left, or_assoc, or_left_comm, or_comm]

def input_k6_p3 : Fin 17 → Fin 26 := ![0, 1, 2, 3, 6, 7, 13, 14, 15, 16, 19, 20, 21, 22, 23, 24, 25]

def function_k6_p3 (y : Fin 17 → Bool) : Bool :=
  (y 0 && (y 6 || y 7 || y 9 || y 13)) || (y 1 && (y 6 || y 8 || y 12 || y 16)) || (y 2 && (y 7 || y 11 || y 15 || y 16)) || (y 3 && (y 6 || y 10 || y 14 || y 15)) || (y 4 && (y 9 || y 11 || y 12 || y 14)) || (y 5 && (y 8 || y 10 || y 11 || y 13))

def remaining_k6_p3 : List (Fin 26 × Fin 26 × Fin 26 × Fin 26 × Fin 26) :=
  [(4, 18, 22, 23, 25), (5, 17, 21, 22, 24), (8, 14, 18, 19, 21), (9, 13, 17, 18, 20), (10, 16, 17, 19, 25), (11, 15, 16, 18, 24), (12, 14, 15, 17, 23)]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma complete_k6_p3 (C : Circuit) (mono : Monotone2 C) (size : C.size ≤ 28)
    (out : C.output < 17 + C.size)
    (correct : ∀ y : Fin 17 → Bool, C.eval (List.ofFn y) = function_k6_p3 y) :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 63 ∧ (∀ x : Fin 26 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 26, (u.val, v.val) ∈ ([(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25), (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24), (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24), (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22), (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20), (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24), (12, 14), (12, 15), (12, 17), (12, 23)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  obtain ⟨D, hm, hs, he⟩ := lift_and_append 17 26 input_k6_p3 C remaining_k6_p3 mono out
  refine ⟨D, hm, ?_, ?_⟩
  · have count : remaining_k6_p3.length = 7 := rfl
    rw [count] at hs
    omega
  · intro x
    rw [he, correct]
    simp [function_k6_p3, input_k6_p3, remaining_k6_p3, rowValue,
      Fin.exists_iff, Prod.mk.injEq, or_and_right, exists_or,
      and_assoc, and_or_left, or_assoc, or_left_comm, or_comm]

end PEqualNP.Outside.L_meta_650
