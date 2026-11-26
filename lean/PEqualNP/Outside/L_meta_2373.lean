import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2373_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def BoolLe (a b : Bool) : Prop := a = true → b = true

def InputLe {n : ℕ} (x y : Fin n → Bool) : Prop := ∀ i, BoolLe (x i) (y i)

def SameZeroLe (x y : Fin 10 → Bool) : Prop := x 0 = y 0 ∧ InputLe x y

lemma related_getD {xs ys : List Bool} (h : List.Forall₂ BoolLe xs ys) (i : ℕ) :
    BoolLe (xs.getD i false) (ys.getD i false) := by
  induction h generalizing i with
  | nil => simp [BoolLe]
  | @cons a b xs ys hab h ih =>
    cases i with
    | zero => simpa using hab
    | succ i => simpa using ih i

lemma related_append {xs ys us vs : List Bool}
    (h : List.Forall₂ BoolLe xs ys) (h' : List.Forall₂ BoolLe us vs) :
    List.Forall₂ BoolLe (xs ++ us) (ys ++ vs) := by
  induction h with
  | nil => exact h'
  | cons h ht ih => exact List.Forall₂.cons h ih

lemma related_ofFn {n : ℕ} (x y : Fin n → Bool) (h : InputLe x y) :
    List.Forall₂ BoolLe (List.ofFn x) (List.ofFn y) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ]
    exact List.Forall₂.cons (h 0) (ih (fun i => x i.succ) (fun i => y i.succ)
      (fun i => h i.succ))

lemma gate_related (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    {xs ys : List Bool} (h : List.Forall₂ BoolLe xs ys) :
    BoolLe (g.op.eval (g.inputs.map fun i => xs.getD i false))
      (g.op.eval (g.inputs.map fun i => ys.getD i false)) := by
  rcases hg with hg | hg
  · simp only [hg, GateOp.eval, BoolLe, List.all_map, Function.comp_def,
      List.all_eq_true]
    intro hx i hi
    exact related_getD h i (hx i hi)
  · simp only [hg, GateOp.eval, BoolLe, List.any_map, Function.comp_def,
      List.any_eq_true]
    rintro ⟨i, hi, hx⟩
    exact ⟨i, hi, related_getD h i hx⟩

lemma gates_related (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    {xs ys : List Bool} (h : List.Forall₂ BoolLe xs ys) :
    List.Forall₂ BoolLe
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) xs)
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) ys) := by
  induction gs generalizing xs ys with
  | nil => exact h
  | cons g gs ih =>
    apply ih (fun g' h' => hg g' (List.mem_cons_of_mem g h'))
    exact related_append h (List.Forall₂.cons (gate_related g (hg g (by simp)) h)
      List.Forall₂.nil)

lemma monotone2_eval_related (C : Circuit) (hC : Monotone2 C)
    {xs ys : List Bool} (h : List.Forall₂ BoolLe xs ys) :
    BoolLe (C.eval xs) (C.eval ys) := by
  apply related_getD (gates_related C.gates ?_ h) C.output
  intro g hg
  have hp := (hC g hg).1
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hp

def oneNotEval (C : Circuit) (x : Fin 10 → Bool) : Bool :=
  C.eval (List.ofFn x ++ [!(x 0)])

lemma oneNotEval_partial_monotone (C : Circuit) (hC : Monotone2 C)
    {x y : Fin 10 → Bool} (hxy : SameZeroLe x y) :
    BoolLe (oneNotEval C x) (oneNotEval C y) := by
  apply monotone2_eval_related C hC
  apply related_append (related_ofFn x y hxy.2)
  apply List.Forall₂.cons
  · simp [BoolLe, hxy.1]
  · exact List.Forall₂.nil

lemma oneNotEval_eq_prefix (C : Circuit) (x : Fin 10 → Bool) :
    oneNotEval C x =
      (Circuit.mk (({ op := GateOp.not, inputs := [0] } : Gate) :: C.gates) C.output).eval (List.ofFn x) := by
  simp [oneNotEval, Circuit.eval, Circuit.wires, GateOp.eval]

lemma boundary_suffices {α : Type*} (R : α → α → Prop)
    (f target : α → Bool) (positive negative : List α)
    (hmono : ∀ {x y}, R x y → BoolLe (f x) (f y))
    (hp : ∀ p ∈ positive, f p = true)
    (hn : ∀ p ∈ negative, f p = false)
    (hcoverp : ∀ x, target x = true → ∃ p ∈ positive, R p x)
    (hcovern : ∀ x, target x = false → ∃ p ∈ negative, R x p) :
    ∀ x, f x = target x := by
  intro x
  cases ht : target x with
  | false =>
    obtain ⟨p, hpmem, hxp⟩ := hcovern x ht
    have hpf := hn p hpmem
    cases hf : f x with
    | false => rfl
    | true =>
      have hpt := hmono hxp hf
      rw [hpf] at hpt
      cases hpt
  | true =>
    obtain ⟨p, hpmem, hpx⟩ := hcoverp x ht
    exact hmono hpx (hp p hpmem)

def row (m : ℕ) (i : Fin 10) : Bool := m.testBit i.val

def graphF (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def positiveRows : List ℕ :=
  [3,6,12,13,17,24,33,66,132,133,160,264,265,288,320,321,528,576,577,640,641]

def negativeRows : List ℕ :=
  [50,69,104,116,138,200,201,208,276,385,402,521,548,554,770,772,773]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma positive_rows_true : ∀ m ∈ positiveRows, graphF (row m) = true := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma negative_rows_false : ∀ m ∈ negativeRows, graphF (row m) = false := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rows_cover : ∀ x : Fin 10 → Bool,
    (graphF x = true → ∃ m ∈ positiveRows, SameZeroLe (row m) x) ∧
    (graphF x = false → ∃ m ∈ negativeRows, SameZeroLe x (row m)) := by
  unfold SameZeroLe InputLe BoolLe
  decide


lemma oneNotEval_boundary_iff (C : Circuit) (hC : Monotone2 C) :
    (∀ x, oneNotEval C x = graphF x) ↔
      (∀ m ∈ positiveRows, oneNotEval C (row m) = true) ∧
      (∀ m ∈ negativeRows, oneNotEval C (row m) = false) := by
  constructor
  · intro h
    exact ⟨fun m hm => (h (row m)).trans (positive_rows_true m hm),
      fun m hm => (h (row m)).trans (negative_rows_false m hm)⟩
  · rintro ⟨hp, hn⟩
    apply boundary_suffices SameZeroLe (oneNotEval C) graphF
      (positiveRows.map row) (negativeRows.map row)
      (fun hxy => oneNotEval_partial_monotone C hC hxy)
    · intro p hp'
      obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hp'
      exact hp m hm
    · intro p hn'
      obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hn'
      exact hn m hm
    · intro x hx
      obtain ⟨m, hm, hmx⟩ := (rows_cover x).1 hx
      exact ⟨row m, List.mem_map.mpr ⟨m, hm, rfl⟩, hmx⟩
    · intro x hx
      obtain ⟨m, hm, hxm⟩ := (rows_cover x).2 hx
      exact ⟨row m, List.mem_map.mpr ⟨m, hm, rfl⟩, hxm⟩

lemma one_not_circuit_boundary_iff (C : Circuit) (hC : Monotone2 C) :
    (∀ x, (Circuit.mk (({ op := GateOp.not, inputs := [0] } : Gate) :: C.gates) C.output).eval (List.ofFn x) = graphF x) ↔
      (∀ m ∈ positiveRows,
        (Circuit.mk (({ op := GateOp.not, inputs := [0] } : Gate) :: C.gates) C.output).eval (List.ofFn (row m)) = true) ∧
      (∀ m ∈ negativeRows,
        (Circuit.mk (({ op := GateOp.not, inputs := [0] } : Gate) :: C.gates) C.output).eval (List.ofFn (row m)) = false) := by
  simpa only [← oneNotEval_eq_prefix] using oneNotEval_boundary_iff C hC

lemma boundary_row_count : positiveRows.length + negativeRows.length = 38 := by
  decide

lemma boundary_rows_nodup : (positiveRows ++ negativeRows).Nodup := by
  decide

lemma monotone2_wires_related (C : Circuit) (hC : Monotone2 C)
    {xs ys : List Bool} (h : List.Forall₂ BoolLe xs ys) :
    List.Forall₂ BoolLe (C.wires xs) (C.wires ys) := by
  apply gates_related C.gates ?_ h
  intro g hg
  have hp := (hC g hg).1
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hp

def negSource {n : ℕ} (pre : Circuit) (j : ℕ) (x : Fin n → Bool) : Bool :=
  (pre.wires (List.ofFn x)).getD j false

def oneNegEval {n : ℕ} (pre : Circuit) (j : ℕ) (C : Circuit)
    (x : Fin n → Bool) : Bool :=
  C.eval (pre.wires (List.ofFn x) ++ [!(negSource pre j x)])

lemma negSource_monotone {n : ℕ} (pre : Circuit) (j : ℕ)
    (hpre : Monotone2 pre) {x y : Fin n → Bool} (hxy : InputLe x y) :
    BoolLe (negSource pre j x) (negSource pre j y) := by
  exact related_getD
    (monotone2_wires_related pre hpre (related_ofFn x y hxy)) j

lemma oneNegEval_partial_monotone {n : ℕ} (pre : Circuit) (j : ℕ) (C : Circuit)
    (hpre : Monotone2 pre) (hC : Monotone2 C)
    {x y : Fin n → Bool} (hxy : InputLe x y)
    (hsame : negSource pre j x = negSource pre j y) :
    BoolLe (oneNegEval pre j C x) (oneNegEval pre j C y) := by
  apply monotone2_eval_related C hC
  apply related_append
    (monotone2_wires_related pre hpre (related_ofFn x y hxy))
  apply List.Forall₂.cons
  · simp [BoolLe, hsame]
  · exact List.Forall₂.nil

lemma oneNegEval_eq_circuit {n : ℕ} (pre : Circuit) (j : ℕ) (C : Circuit)
    (x : Fin n → Bool) :
    oneNegEval pre j C x =
      (Circuit.mk
        (pre.gates ++ (({ op := GateOp.not, inputs := [j] } : Gate) :: C.gates))
        C.output).eval (List.ofFn x) := by
  simp [oneNegEval, negSource, Circuit.eval, Circuit.wires, List.foldl_append,
    GateOp.eval]

lemma oneNegEval_boundary_suffices {n : ℕ} (pre : Circuit) (j : ℕ) (C : Circuit)
    (hpre : Monotone2 pre) (hC : Monotone2 C)
    (target : (Fin n → Bool) → Bool) (positive negative : List (Fin n → Bool))
    (hp : ∀ p ∈ positive, oneNegEval pre j C p = true)
    (hn : ∀ p ∈ negative, oneNegEval pre j C p = false)
    (hcoverp : ∀ x, target x = true → ∃ p ∈ positive,
      InputLe p x ∧ negSource pre j p = negSource pre j x)
    (hcovern : ∀ x, target x = false → ∃ p ∈ negative,
      InputLe x p ∧ negSource pre j x = negSource pre j p) :
    ∀ x, oneNegEval pre j C x = target x := by
  exact boundary_suffices
    (fun x y => InputLe x y ∧ negSource pre j x = negSource pre j y)
    (oneNegEval pre j C) target positive negative
    (fun hxy => oneNegEval_partial_monotone pre j C hpre hC hxy.1 hxy.2)
    hp hn hcoverp hcovern

def manyNotEval {n : ℕ} (negative : List (Fin n)) (C : Circuit)
    (x : Fin n → Bool) : Bool :=
  C.eval (List.ofFn x ++ negative.map (fun i => !(x i)))

lemma negative_values_related {n : ℕ} (negative : List (Fin n))
    (x y : Fin n → Bool) (h : ∀ i ∈ negative, x i = y i) :
    List.Forall₂ BoolLe (negative.map (fun i => !(x i)))
      (negative.map (fun i => !(y i))) := by
  induction negative with
  | nil => exact List.Forall₂.nil
  | cons i is ih =>
    apply List.Forall₂.cons
    · have hi := h i (by simp)
      simp [BoolLe, hi]
    · exact ih (fun j hj => h j (List.mem_cons_of_mem i hj))

lemma manyNotEval_partial_monotone {n : ℕ} (negative : List (Fin n))
    (C : Circuit) (hC : Monotone2 C) {x y : Fin n → Bool}
    (hxy : InputLe x y) (hsame : ∀ i ∈ negative, x i = y i) :
    BoolLe (manyNotEval negative C x) (manyNotEval negative C y) := by
  exact monotone2_eval_related C hC
    (related_append (related_ofFn x y hxy) (negative_values_related negative x y hsame))

lemma manyNotEval_boundary_suffices {n : ℕ} (negativeInputs : List (Fin n))
    (C : Circuit) (hC : Monotone2 C)
    (target : (Fin n → Bool) → Bool) (positive negative : List (Fin n → Bool))
    (hp : ∀ p ∈ positive, manyNotEval negativeInputs C p = true)
    (hn : ∀ p ∈ negative, manyNotEval negativeInputs C p = false)
    (hcoverp : ∀ x, target x = true → ∃ p ∈ positive,
      InputLe p x ∧ ∀ i ∈ negativeInputs, p i = x i)
    (hcovern : ∀ x, target x = false → ∃ p ∈ negative,
      InputLe x p ∧ ∀ i ∈ negativeInputs, x i = p i) :
    ∀ x, manyNotEval negativeInputs C x = target x := by
  exact boundary_suffices
    (fun x y => InputLe x y ∧ ∀ i ∈ negativeInputs, x i = y i)
    (manyNotEval negativeInputs C) target positive negative
    (fun hxy => manyNotEval_partial_monotone negativeInputs C hC hxy.1 hxy.2)
    hp hn hcoverp hcovern

lemma input_getD_append {n : ℕ} (x : Fin n → Bool) (extra : List Bool) (i : Fin n) :
    (List.ofFn x ++ extra).getD i.val false = x i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp)]
  simp

def rawNotGates {n : ℕ} (negative : List (Fin n)) : List Gate :=
  negative.map (fun i => { op := GateOp.not, inputs := [i.val] })

lemma rawNot_fold {n : ℕ} (negative : List (Fin n)) (x : Fin n → Bool)
    (extra : List Bool) :
    (rawNotGates negative).foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))])
      (List.ofFn x ++ extra) =
    List.ofFn x ++ (extra ++ negative.map (fun i => !(x i))) := by
  induction negative generalizing extra with
  | nil => simp [rawNotGates]
  | cons i is ih =>
    have hlookup := input_getD_append x extra i
    simp only [List.getD_eq_getElem?_getD] at hlookup
    simpa [rawNotGates, GateOp.eval, List.append_assoc, hlookup]
      using ih (extra ++ [!(x i)])

lemma manyNotEval_eq_circuit {n : ℕ} (negative : List (Fin n)) (C : Circuit)
    (x : Fin n → Bool) :
    manyNotEval negative C x =
      (Circuit.mk (rawNotGates negative ++ C.gates) C.output).eval (List.ofFn x) := by
  have hp := rawNot_fold negative x []
  simp only [List.append_nil, List.nil_append] at hp
  simp only [manyNotEval, Circuit.eval, Circuit.wires, List.foldl_append, hp]

def twoRawInputs : List (Fin 10) := [0, 2]

def twoRawPositiveRows : List ℕ := [3, 6, 7, 12, 13, 17, 21, 24, 33, 37, 66, 132, 133, 160, 264, 265, 288, 292, 320, 321, 324, 325, 528, 532, 576, 577, 580, 581, 640, 641]

def twoRawNegativeRows : List ℕ := [50, 69, 104, 112, 116, 138, 200, 201, 208, 276, 385, 402, 521, 548, 554, 769, 770, 772, 773]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma twoRaw_positive_rows_true : ∀ m ∈ twoRawPositiveRows, graphF (row m) = true := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma twoRaw_negative_rows_false : ∀ m ∈ twoRawNegativeRows, graphF (row m) = false := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma twoRaw_rows_cover : ∀ x : Fin 10 → Bool,
    (graphF x = true → ∃ m ∈ twoRawPositiveRows,
      InputLe (row m) x ∧ ∀ i ∈ twoRawInputs, row m i = x i) ∧
    (graphF x = false → ∃ m ∈ twoRawNegativeRows,
      InputLe x (row m) ∧ ∀ i ∈ twoRawInputs, x i = row m i) := by
  unfold InputLe BoolLe
  simp only [twoRawInputs, List.forall_mem_cons, List.not_mem_nil, false_implies, forall_const, and_true]
  decide

lemma twoRawNotEval_boundary_iff (C : Circuit) (hC : Monotone2 C) :
    (∀ x, manyNotEval twoRawInputs C x = graphF x) ↔
      (∀ m ∈ twoRawPositiveRows, manyNotEval twoRawInputs C (row m) = true) ∧
      (∀ m ∈ twoRawNegativeRows, manyNotEval twoRawInputs C (row m) = false) := by
  constructor
  · intro h
    exact ⟨fun m hm => (h (row m)).trans (twoRaw_positive_rows_true m hm),
      fun m hm => (h (row m)).trans (twoRaw_negative_rows_false m hm)⟩
  · rintro ⟨hp, hn⟩
    apply manyNotEval_boundary_suffices twoRawInputs C hC graphF
      (twoRawPositiveRows.map row) (twoRawNegativeRows.map row)
    · intro p hp'
      obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hp'
      exact hp m hm
    · intro p hn'
      obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hn'
      exact hn m hm
    · intro x hx
      obtain ⟨m, hm, hmx⟩ := (twoRaw_rows_cover x).1 hx
      exact ⟨row m, List.mem_map.mpr ⟨m, hm, rfl⟩, hmx⟩
    · intro x hx
      obtain ⟨m, hm, hxm⟩ := (twoRaw_rows_cover x).2 hx
      exact ⟨row m, List.mem_map.mpr ⟨m, hm, rfl⟩, hxm⟩

lemma twoRaw_boundary_row_count : twoRawPositiveRows.length + twoRawNegativeRows.length = 49 := by
  decide

lemma twoRaw_boundary_rows_nodup : (twoRawPositiveRows ++ twoRawNegativeRows).Nodup := by
  decide

lemma and_operand_replacement {ι : Type*} (f a b : ι → Bool)
    (k : ι → Bool → Bool)
    (hk : ∀ x u v, BoolLe u v → BoolLe (k x u) (k x v))
    (hcorrect : ∀ x, k x (a x && b x) = f x)
    (hnegative : ∀ x, f x = false → a x = true → b x = true) :
    ∀ x, k x (a x) = f x := by
  intro x
  have hm := hk x false true (by simp [BoolLe])
  have hc := hcorrect x
  have hn := hnegative x
  cases ha : a x <;> cases hb : b x <;> cases hf : f x <;>
    cases h0 : k x false <;> cases h1 : k x true <;> simp_all [BoolLe]

lemma or_operand_replacement {ι : Type*} (f a b : ι → Bool)
    (k : ι → Bool → Bool)
    (hk : ∀ x u v, BoolLe u v → BoolLe (k x u) (k x v))
    (hcorrect : ∀ x, k x (a x || b x) = f x)
    (hpositive : ∀ x, f x = true → b x = true → a x = true) :
    ∀ x, k x (a x) = f x := by
  intro x
  have hm := hk x false true (by simp [BoolLe])
  have hc := hcorrect x
  have hp := hpositive x
  cases ha : a x <;> cases hb : b x <;> cases hf : f x <;>
    cases h0 : k x false <;> cases h1 : k x true <;> simp_all [BoolLe]

lemma and_operand_negative_witness {ι : Type*} (f a b : ι → Bool)
    (k : ι → Bool → Bool)
    (hk : ∀ x u v, BoolLe u v → BoolLe (k x u) (k x v))
    (hcorrect : ∀ x, k x (a x && b x) = f x)
    (hnecessary : ¬ ∀ x, k x (a x) = f x) :
    ∃ x, f x = false ∧ a x = true ∧ b x = false := by
  classical
  by_contra h
  apply hnecessary
  apply and_operand_replacement f a b k hk hcorrect
  intro x hf ha
  cases hb : b x
  · exact False.elim (h ⟨x, hf, ha, hb⟩)
  · rfl

lemma or_operand_positive_witness {ι : Type*} (f a b : ι → Bool)
    (k : ι → Bool → Bool)
    (hk : ∀ x u v, BoolLe u v → BoolLe (k x u) (k x v))
    (hcorrect : ∀ x, k x (a x || b x) = f x)
    (hnecessary : ¬ ∀ x, k x (a x) = f x) :
    ∃ x, f x = true ∧ a x = false ∧ b x = true := by
  classical
  by_contra h
  apply hnecessary
  apply or_operand_replacement f a b k hk hcorrect
  intro x hf hb
  cases ha : a x
  · exact False.elim (h ⟨x, hf, ha, hb⟩)
  · rfl

end PEqualNP.Outside.L_meta_2373_aux
