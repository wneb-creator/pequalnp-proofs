import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux.InputSlots

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

local instance : DecidableEq GateOp := lineDegreeGateOpDecEq

-- NOT ignores all but its first input; these are precisely the effective slots.
def effective (g : Gate) : List ℕ :=
  if g.op = GateOp.not then g.inputs.take 1 else g.inputs

def slots (C : Circuit) : List ℕ := C.gates.flatMap effective

def normGate (g : Gate) : Gate := ⟨g.op, effective g⟩

def normalize (C : Circuit) : Circuit := ⟨C.gates.map normGate, C.output⟩

lemma normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  rcases g with ⟨op, ins⟩
  cases op <;> simp only [normGate, effective]
  all_goals first | rfl | (cases ins <;> simp [GateOp.eval])

lemma normalize_eval (C : Circuit) (x : List Bool) :
    (normalize C).eval x = C.eval x := by
  have h : ∀ (gs : List Gate) (w : List Bool),
      (gs.map normGate).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w := by
    intro gs
    induction gs with
    | nil => intro w; rfl
    | cons g gs ih =>
      intro w
      simp only [List.map_cons, List.foldl_cons, normGate_eval]
      exact ih _
  exact congrArg (fun w => w.getD C.output false) (h C.gates x)

lemma normalize_size (C : Circuit) : (normalize C).size = C.size := by
  simp [normalize, Circuit.size]

lemma normalize_notCount (C : Circuit) :
    NotBracket.notCount (normalize C) = NotBracket.notCount C := by
  simp only [NotBracket.notCount, normalize, List.filter_map, List.length_map]
  rfl

lemma effective_length (g : Gate) (hlen : g.inputs.length ≤ 2) :
    (effective g).length + (if g.op = GateOp.not then 1 else 0) ≤ 2 := by
  by_cases hn : g.op = GateOp.not
  · simp [effective, hn]
  · simpa [effective, hn] using hlen

lemma slots_bound (C : Circuit) (fan : FanInTwo C) :
    (slots C).length + NotBracket.notCount C ≤ 2 * C.size := by
  have h : ∀ (gs : List Gate), (∀ g ∈ gs, g.inputs.length ≤ 2) →
      (gs.flatMap effective).length + (gs.filter fun g => decide (g.op = GateOp.not)).length ≤
        2 * gs.length := by
    intro gs
    induction gs with
    | nil => intro _; simp
    | cons g gs ih =>
      intro hg
      have hh := effective_length g (hg g (by simp))
      have ht := ih (fun q hq => hg q (List.mem_cons_of_mem _ hq))
      simp only [List.flatMap_cons, List.length_append, List.filter_cons, List.length_cons]
      split_ifs <;> simp_all only [decide_eq_true_eq, ite_true, ite_false, List.length_cons] <;> omega
  exact h C.gates (fun g hg => (fan g hg).2)

lemma count_sum_le (xs : List ℕ) (S : Finset ℕ) :
    ∑ i ∈ S, xs.count i ≤ xs.length := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.count_cons, beq_iff_eq, Finset.sum_add_distrib, List.length_cons]
    have hi : (∑ i ∈ S, if a = i then 1 else 0) ≤ 1 := by
      simp only [Finset.sum_ite_eq]
      split_ifs <;> omega
    omega

lemma shifted_count_sum_le (xs : List ℕ) (n m : ℕ) :
    ∑ j ∈ Finset.range m, xs.count (n + j) ≤ xs.length := by
  have h := count_sum_le xs ((Finset.range m).image fun j => n + j)
  rw [Finset.sum_image] at h
  · exact h
  · intro a ha b hb hab
    exact Nat.add_left_cancel hab

lemma internal_count (xs : List ℕ) (n m out : ℕ)
    (live : ∀ j, j < m → n + j ≠ out → n + j ∈ xs) :
    m ≤ (∑ j ∈ Finset.range m, xs.count (n + j)) + 1 := by
  have hp : ∀ j ∈ Finset.range m,
      1 ≤ xs.count (n + j) + ([out] : List ℕ).count (n + j) := by
    intro j hj
    by_cases he : n + j = out
    · simp [he]
    · have hh := List.count_pos_iff.mpr (live j (Finset.mem_range.mp hj) he)
      omega
  have hsum := Finset.sum_le_sum hp
  have hout := shifted_count_sum_le [out] n m
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one,
    Finset.sum_add_distrib, List.length_singleton] at hsum hout
  omega

-- Every essential input is read. If at most one gate output may be unread,
-- a circuit with fewer than 2n - 1 + t gates has an input used exactly once.
lemma input_once (C : Circuit) (n : ℕ) (fan : FanInTwo C)
    (essential : ∀ i, i < n → i ∈ slots C)
    (live : ∀ j, j < C.size → n + j ≠ C.output → n + j ∈ slots C)
    (budget : C.size + 1 < 2 * n + NotBracket.notCount C) :
    ∃ i, i < n ∧ (slots C).count i = 1 := by
  by_contra hn
  push Not at hn
  have hraw : 2 * n ≤ ∑ i ∈ Finset.range n, (slots C).count i := by
    have h := Finset.sum_le_sum (fun i hi => show 2 ≤ (slots C).count i from by
      have hp := List.count_pos_iff.mpr (essential i (Finset.mem_range.mp hi))
      have hne := hn i (Finset.mem_range.mp hi)
      omega)
    simpa [Nat.mul_comm] using h
  have hint := internal_count (slots C) n C.size C.output live
  have htotal := count_sum_le (slots C) (Finset.range (n + C.size))
  rw [Finset.sum_range_add] at htotal
  have hb := slots_bound C fan
  omega

lemma petersen_input_once (C : Circuit) (fan : FanInTwo C)
    (essential : ∀ i, i < 10 → i ∈ slots C)
    (live : ∀ j, j < C.size → 10 + j ≠ C.output → 10 + j ∈ slots C)
    (budget : C.size ≤ 19) (hasNot : 1 ≤ NotBracket.notCount C) :
    ∃ i, i < 10 ∧ (slots C).count i = 1 := by
  apply input_once C 10 fan essential live
  omega

lemma unique_reader (gs : List Gate) (i : ℕ)
    (once : (gs.flatMap effective).count i = 1) :
    ∃ q, q < gs.length ∧ i ∈ effective (gs.getD q ⟨GateOp.or, []⟩) ∧
      ∀ t, t < gs.length → t ≠ q → i ∉ effective (gs.getD t ⟨GateOp.or, []⟩) := by
  induction gs with
  | nil => simp at once
  | cons g gs ih =>
    simp only [List.flatMap_cons, List.count_append] at once
    by_cases hg : i ∈ effective g
    · have hp := List.count_pos_iff.mpr hg
      have hz : (gs.flatMap effective).count i = 0 := by omega
      have hno := List.count_eq_zero.mp hz
      refine ⟨0, by simp, by simpa using hg, ?_⟩
      intro t ht hne hi
      cases t with
      | zero => exact hne rfl
      | succ t =>
        have htl : t < gs.length := by simpa using ht
        apply hno
        apply List.mem_flatMap.mpr
        refine ⟨gs.getD t ⟨GateOp.or, []⟩, ?_, ?_⟩
        · rw [List.getD_eq_getElem _ _ htl]
          exact List.getElem_mem _
        · simpa using hi
    · have hz := List.count_eq_zero_of_not_mem hg
      have ho : (gs.flatMap effective).count i = 1 := by omega
      obtain ⟨q, hq, hr, hu⟩ := ih ho
      refine ⟨q + 1, by simpa using hq, by simpa using hr, ?_⟩
      intro t ht hne
      cases t with
      | zero => simpa using hg
      | succ t =>
        apply hu t (by simpa using ht) (by omega)

lemma petersen_unique_reader (C : Circuit) (fan : FanInTwo C)
    (essential : ∀ i, i < 10 → i ∈ slots C)
    (live : ∀ j, j < C.size → 10 + j ≠ C.output → 10 + j ∈ slots C)
    (budget : C.size ≤ 19) (hasNot : 1 ≤ NotBracket.notCount C) :
    ∃ (i : Fin 10) (q : ℕ), q < C.gates.length ∧
      i.val ∈ effective (C.gates.getD q ⟨GateOp.or, []⟩) ∧
      ∀ t, t < C.gates.length → t ≠ q →
        i.val ∉ effective (C.gates.getD t ⟨GateOp.or, []⟩) := by
  obtain ⟨i, hi, hone⟩ := petersen_input_once C fan essential live budget hasNot
  obtain ⟨q, hq, hr, hu⟩ := unique_reader C.gates i hone
  exact ⟨⟨i, hi⟩, q, hq, hr, hu⟩

end PEqualNP.Outside.L_meta_2592_aux.InputSlots
