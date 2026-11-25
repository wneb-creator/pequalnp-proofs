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




def AllAndSound (n : ℕ) (C : Circuit) : Prop :=
  ∀ (i : Fin C.gates.length) (x : Fin n → Bool),
    (C.gates.get i).op = .and →
    (C.wires (List.ofFn x)).getD (n + i.val) false = true →
    C.eval (List.ofFn x) = true

lemma starTail_output_of_and (w : List Bool) (p a b c d out : ℕ)
    (hp : p < w.length) (ha : a < w.length) (hb : b < w.length)
    (hc : c < w.length) (hd : d < w.length) (hout : out < w.length) :
    (liftRun (starTail w.length p a b c d out) w).getD (w.length + 4) false =
      (w.getD out false ||
        (liftRun (starTail w.length p a b c d out) w).getD (w.length + 3) false) := by
  simp only [liftRun, starTail, List.foldl_cons, List.foldl_nil,
    List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
    List.any_cons, List.any_nil, id_eq, Bool.and_true, Bool.or_false]
  simp (disch := omega) only [lift_snoc_read, List.length_append, List.length_cons,
    List.length_nil, Nat.add_assoc, Nat.reduceAdd, Nat.add_left_cancel_iff,
    ite_eq_left, ite_eq_right, ite_true]

lemma appendStar_sound (n : ℕ) (C : Circuit) (p a b c d : Fin n)
    (hout : C.output < n + C.size) (hs : AllAndSound n C) :
    AllAndSound n (appendStar n C p a b c d) := by
  intro i x hop hv
  change ((C.gates ++ starTail (n + C.size) p.val a.val b.val c.val d.val C.output)[i.val]).op = .and at hop
  let w := C.wires (List.ofFn x)
  have hlen : w.length = n + C.size := by
    simpa only [w, Circuit.wires, Circuit.size, liftRun, List.length_ofFn]
      using liftRun_length C.gates (List.ofFn x)
  have hwire : (appendStar n C p a b c d).wires (List.ofFn x) =
      liftRun (starTail (n + C.size) p.val a.val b.val c.val d.val C.output) w := by
    simp only [appendStar, Circuit.wires, liftRun, List.foldl_append, w]
  by_cases hold : i.val < C.gates.length
  · let j : Fin C.gates.length := ⟨i.val, hold⟩
    have hj : (C.gates.get j).op = .and := by
      simpa [appendStar, List.get_eq_getElem, List.getElem_append, hold, j] using hop
    have hvold : (C.wires (List.ofFn x)).getD (n + j.val) false = true := by
      rw [hwire, liftRun_preserve _ w _ (by rw [hlen]; change n + i.val < n + C.gates.length; omega)] at hv
      exact hv
    rw [appendStar_eval n C p a b c d hout x, hs j x hj hvold]
    simp
  · have hi : i.val < C.gates.length + 5 := by
      have hi := i.isLt
      simpa [appendStar, starTail] using hi
    have choices : i.val = C.gates.length ∨ i.val = C.gates.length + 1 ∨
        i.val = C.gates.length + 2 ∨ i.val = C.gates.length + 3 ∨
        i.val = C.gates.length + 4 := by omega
    have hidx : i.val = C.gates.length + 3 := by
      rcases choices with h | h | h | h | h
      all_goals try { simp [appendStar, starTail, List.get_eq_getElem, List.getElem_append, h] at hop }
      exact h
    have hvnew : (liftRun (starTail w.length p.val a.val b.val c.val d.val C.output) w).getD
        (w.length + 3) false = true := by
      rw [hwire, hidx] at hv
      simpa only [hlen, Circuit.size, Nat.add_assoc] using hv
    change ((appendStar n C p a b c d).wires (List.ofFn x)).getD
      (n + C.size + 4) false = true
    rw [hwire, ← hlen, starTail_output_of_and]
    · rw [hvnew]; simp
    all_goals rw [hlen]
    · have := p.isLt; omega
    · have := a.isLt; omega
    · have := b.isLt; omega
    · have := c.isLt; omega
    · have := d.isLt; omega
    · exact hout

lemma appendRows_sound (n : ℕ) (C : Circuit)
    (rows : List (Fin n × Fin n × Fin n × Fin n × Fin n))
    (hout : C.output < n + C.size) (hs : AllAndSound n C) :
    AllAndSound n (appendRows n C rows) := by
  induction rows generalizing C with
  | nil => exact hs
  | cons r rows ih =>
    exact ih _ (appendStar_valid _ _ _ _ _ _ _)
      (appendStar_sound _ _ _ _ _ _ _ hout hs)

end PEqualNP.Outside.L_meta_650
