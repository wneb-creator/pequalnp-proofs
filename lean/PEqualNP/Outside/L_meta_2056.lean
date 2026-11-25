import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_2056_aux

def baseline : Circuit :=
  { gates := [
      ⟨GateOp.or, [13, 14]⟩,
      ⟨GateOp.or, [26, 16]⟩,
      ⟨GateOp.or, [27, 22]⟩,
      ⟨GateOp.and, [0, 28]⟩,
      ⟨GateOp.or, [13, 15]⟩,
      ⟨GateOp.or, [30, 21]⟩,
      ⟨GateOp.or, [31, 25]⟩,
      ⟨GateOp.and, [1, 32]⟩,
      ⟨GateOp.or, [14, 20]⟩,
      ⟨GateOp.or, [34, 24]⟩,
      ⟨GateOp.or, [35, 25]⟩,
      ⟨GateOp.and, [2, 36]⟩,
      ⟨GateOp.or, [13, 19]⟩,
      ⟨GateOp.or, [38, 23]⟩,
      ⟨GateOp.or, [39, 24]⟩,
      ⟨GateOp.and, [3, 40]⟩,
      ⟨GateOp.or, [18, 22]⟩,
      ⟨GateOp.or, [42, 23]⟩,
      ⟨GateOp.or, [43, 25]⟩,
      ⟨GateOp.and, [4, 44]⟩,
      ⟨GateOp.or, [17, 21]⟩,
      ⟨GateOp.or, [46, 22]⟩,
      ⟨GateOp.or, [47, 24]⟩,
      ⟨GateOp.and, [5, 48]⟩,
      ⟨GateOp.or, [16, 20]⟩,
      ⟨GateOp.or, [50, 21]⟩,
      ⟨GateOp.or, [51, 23]⟩,
      ⟨GateOp.and, [6, 52]⟩,
      ⟨GateOp.or, [15, 19]⟩,
      ⟨GateOp.or, [54, 20]⟩,
      ⟨GateOp.or, [55, 22]⟩,
      ⟨GateOp.and, [7, 56]⟩,
      ⟨GateOp.or, [14, 18]⟩,
      ⟨GateOp.or, [58, 19]⟩,
      ⟨GateOp.or, [59, 21]⟩,
      ⟨GateOp.and, [8, 60]⟩,
      ⟨GateOp.or, [13, 17]⟩,
      ⟨GateOp.or, [62, 18]⟩,
      ⟨GateOp.or, [63, 20]⟩,
      ⟨GateOp.and, [9, 64]⟩,
      ⟨GateOp.or, [16, 17]⟩,
      ⟨GateOp.or, [66, 19]⟩,
      ⟨GateOp.or, [67, 25]⟩,
      ⟨GateOp.and, [10, 68]⟩,
      ⟨GateOp.or, [15, 16]⟩,
      ⟨GateOp.or, [70, 18]⟩,
      ⟨GateOp.or, [71, 24]⟩,
      ⟨GateOp.and, [11, 72]⟩,
      ⟨GateOp.or, [14, 15]⟩,
      ⟨GateOp.or, [74, 17]⟩,
      ⟨GateOp.or, [75, 23]⟩,
      ⟨GateOp.and, [12, 76]⟩,
      ⟨GateOp.or, [29, 33]⟩,
      ⟨GateOp.or, [78, 37]⟩,
      ⟨GateOp.or, [79, 41]⟩,
      ⟨GateOp.or, [80, 45]⟩,
      ⟨GateOp.or, [81, 49]⟩,
      ⟨GateOp.or, [82, 53]⟩,
      ⟨GateOp.or, [83, 57]⟩,
      ⟨GateOp.or, [84, 61]⟩,
      ⟨GateOp.or, [85, 65]⟩,
      ⟨GateOp.or, [86, 69]⟩,
      ⟨GateOp.or, [87, 73]⟩,
      ⟨GateOp.or, [88, 77]⟩],
    output := 89 }

def baselineExpression (x : Fin 26 → Bool) : Bool :=
  (((((((((((((x 0 && (((x 13 || x 14) || x 16) || x 22)) ||
    (x 1 && (((x 13 || x 15) || x 21) || x 25))) ||
    (x 2 && (((x 14 || x 20) || x 24) || x 25))) ||
    (x 3 && (((x 13 || x 19) || x 23) || x 24))) ||
    (x 4 && (((x 18 || x 22) || x 23) || x 25))) ||
    (x 5 && (((x 17 || x 21) || x 22) || x 24))) ||
    (x 6 && (((x 16 || x 20) || x 21) || x 23))) ||
    (x 7 && (((x 15 || x 19) || x 20) || x 22))) ||
    (x 8 && (((x 14 || x 18) || x 19) || x 21))) ||
    (x 9 && (((x 13 || x 17) || x 18) || x 20))) ||
    (x 10 && (((x 16 || x 17) || x 19) || x 25))) ||
    (x 11 && (((x 15 || x 16) || x 18) || x 24))) ||
    (x 12 && (((x 14 || x 15) || x 17) || x 23)))

def incidenceEdges : List (Fin 13 × Fin 13) :=
  [(0, 0), (0, 1), (0, 3), (0, 9), (1, 0), (1, 2), (1, 8), (1, 12), (2, 1), (2, 7), (2, 11), (2, 12), (3, 0), (3, 6), (3, 10), (3, 11), (4, 5), (4, 9), (4, 10), (4, 12), (5, 4), (5, 8), (5, 9), (5, 11), (6, 3), (6, 7), (6, 8), (6, 10), (7, 2), (7, 6), (7, 7), (7, 9), (8, 1), (8, 5), (8, 6), (8, 8), (9, 0), (9, 4), (9, 5), (9, 7), (10, 3), (10, 4), (10, 6), (10, 12), (11, 2), (11, 3), (11, 5), (11, 11), (12, 1), (12, 2), (12, 4), (12, 10)]

def pointWire (p : Fin 13) : Fin 26 := ⟨p.val, by omega⟩

def lineWire (l : Fin 13) : Fin 26 := ⟨13 + l.val, by omega⟩

lemma baseline_size : baseline.size = 64 := rfl

lemma baseline_monotone : Monotone2 baseline := by
  simp [Monotone2, baseline]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma baseline_eval (x : Fin 26 → Bool) :
    baseline.eval (List.ofFn x) = baselineExpression x := by
  simp [baseline, Circuit.eval, Circuit.wires, GateOp.eval, baselineExpression, List.ofFn_succ]

set_option maxHeartbeats 4000000 in
lemma baseline_eval_edges (x : Fin 26 → Bool) :
    baseline.eval (List.ofFn x) = true ↔
      ∃ e ∈ incidenceEdges, x (pointWire e.1) = true ∧ x (lineWire e.2) = true := by
  rw [baseline_eval]
  simp [baselineExpression, incidenceEdges, pointWire, lineWire, Bool.or_eq_true,
    Bool.and_eq_true, and_or_left, or_assoc]

set_option maxRecDepth 10000 in
lemma incidenceEdges_exact : ∀ p l : Fin 13,
    (p, l) ∈ incidenceEdges ↔ (p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ) := by
  decide +kernel

lemma baseline_correct (x : Fin 26 → Bool) :
    baseline.eval (List.ofFn x) = true ↔
      ∃ p l : Fin 13, (p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ) ∧
        x (pointWire p) = true ∧ x (lineWire l) = true := by
  rw [baseline_eval_edges]
  constructor
  · rintro ⟨⟨p, l⟩, hm, hp, hl⟩
    exact ⟨p, l, (incidenceEdges_exact p l).mp hm, hp, hl⟩
  · rintro ⟨p, l, hm, hp, hl⟩
    exact ⟨(p, l), (incidenceEdges_exact p l).mpr hm, hp, hl⟩

def baselineBits (s t : Finset (Fin 13)) (i : Fin 26) : Bool :=
  if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ s)
  else decide (Fin.ofNat 13 i.val ∈ t)

lemma baselineBits_point (s t : Finset (Fin 13)) (p : Fin 13) :
    baselineBits s t (pointWire p) = decide (p ∈ s) := by
  simp [baselineBits, pointWire, p.isLt]

lemma baselineBits_line (s t : Finset (Fin 13)) (l : Fin 13) :
    baselineBits s t (lineWire l) = decide (l ∈ t) := by
  have h : Fin.ofNat 13 (13 + l.val) = l := by
    ext
    simp [Fin.ofNat, Nat.mod_eq_of_lt l.isLt]
  change (if 13 + l.val < 13 then decide (Fin.ofNat 13 (13 + l.val) ∈ s)
    else decide (Fin.ofNat 13 (13 + l.val) ∈ t)) = decide (l ∈ t)
  rw [ite_eq_right (by omega), h]

lemma baseline_sets (s t : Finset (Fin 13)) :
    baseline.eval (List.ofFn (baselineBits s t)) = true ↔
      ∃ p ∈ s, ∃ l ∈ t, (p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ) := by
  rw [baseline_correct]
  simp only [baselineBits_point, baselineBits_line, decide_eq_true_eq]
  constructor
  · rintro ⟨p, l, h, hp, hl⟩
    exact ⟨p, hp, l, hl, h⟩
  · rintro ⟨p, hp, l, hl, h⟩
    exact ⟨p, l, h, hp, hl⟩

lemma baseline_nearWitness : ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 ∧     x1.size ≤ (64 : ℕ) ∧       let x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => (↑x2 + ↑x3) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];       have x3 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x3 x4 : Finset (Fin (13 : ℕ))) (x5 : Fin (26 : ℕ)) => if ↑x5 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x5 ∈ x3) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x5 ∈ x4);       have x4 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x4 : Finset (Fin (13 : ℕ))) => {x5 : Fin (13 : ℕ) | ∀ x6 ∈ x4, ¬x2 x6 x5};       have x5 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x5 x6 : Finset (Fin (13 : ℕ))) => x1.eval (List.ofFn (x3 x5 x6));       (∀ (x6 x7 : Fin (13 : ℕ)), x2 x6 x7 → x5 {x6} {x7} = Bool.true) ∧ ∀ (x6 : Finset (Fin (13 : ℕ))), x6.card ≤ (3 : ℕ) → x5 x6 (x4 x6) = Bool.false ∧ x5 (x4 x6) x6 = Bool.false := by
  refine ⟨baseline, baseline_monotone, by simp [baseline_size], ?_⟩
  let near := fun p l : Fin 13 => (p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)
  let off := fun s : Finset (Fin 13) => Finset.univ.filter fun l : Fin 13 =>
    ∀ p ∈ s, ¬near p l
  change (∀ p l : Fin 13, near p l →
    baseline.eval (List.ofFn (baselineBits {p} {l})) = true) ∧
    ∀ s : Finset (Fin 13), s.card ≤ 3 →
      baseline.eval (List.ofFn (baselineBits s (off s))) = false ∧
      baseline.eval (List.ofFn (baselineBits (off s) s)) = false
  constructor
  · intro p l h
    exact (baseline_sets _ _).mpr ⟨p, by simp, l, by simp, h⟩
  · intro s _
    constructor
    · apply Bool.eq_false_iff.mpr
      intro h
      obtain ⟨p, hp, l, hl, incident⟩ := (baseline_sets _ _).mp h
      exact (Finset.mem_filter.mp hl).2 p hp incident
    · apply Bool.eq_false_iff.mpr
      intro h
      obtain ⟨p, hp, l, hl, incident⟩ := (baseline_sets _ _).mp h
      apply (Finset.mem_filter.mp hp).2 l hl
      simpa [near, Nat.add_comm] using incident

lemma mixed_pair (a b y u v : Bool) :
    (((y || (a && u)) || (b && v)) && (a || b)) =
      ((a && (y || u)) || (b && (y || v))) := by
  cases a <;> cases b <;> cases y <;> cases u <;> cases v <;> rfl

def mixed65 : Circuit :=
  { gates := [
      ⟨GateOp.or, [14, 16]⟩,
      ⟨GateOp.or, [26, 22]⟩,
      ⟨GateOp.and, [0, 27]⟩,
      ⟨GateOp.or, [15, 21]⟩,
      ⟨GateOp.or, [29, 25]⟩,
      ⟨GateOp.and, [1, 30]⟩,
      ⟨GateOp.or, [14, 20]⟩,
      ⟨GateOp.or, [32, 24]⟩,
      ⟨GateOp.or, [33, 25]⟩,
      ⟨GateOp.and, [2, 34]⟩,
      ⟨GateOp.or, [13, 19]⟩,
      ⟨GateOp.or, [36, 23]⟩,
      ⟨GateOp.or, [37, 24]⟩,
      ⟨GateOp.and, [3, 38]⟩,
      ⟨GateOp.or, [18, 22]⟩,
      ⟨GateOp.or, [40, 23]⟩,
      ⟨GateOp.or, [41, 25]⟩,
      ⟨GateOp.and, [4, 42]⟩,
      ⟨GateOp.or, [17, 21]⟩,
      ⟨GateOp.or, [44, 22]⟩,
      ⟨GateOp.or, [45, 24]⟩,
      ⟨GateOp.and, [5, 46]⟩,
      ⟨GateOp.or, [16, 20]⟩,
      ⟨GateOp.or, [48, 21]⟩,
      ⟨GateOp.or, [49, 23]⟩,
      ⟨GateOp.and, [6, 50]⟩,
      ⟨GateOp.or, [15, 19]⟩,
      ⟨GateOp.or, [52, 20]⟩,
      ⟨GateOp.or, [53, 22]⟩,
      ⟨GateOp.and, [7, 54]⟩,
      ⟨GateOp.or, [14, 18]⟩,
      ⟨GateOp.or, [56, 19]⟩,
      ⟨GateOp.or, [57, 21]⟩,
      ⟨GateOp.and, [8, 58]⟩,
      ⟨GateOp.or, [13, 17]⟩,
      ⟨GateOp.or, [60, 18]⟩,
      ⟨GateOp.or, [61, 20]⟩,
      ⟨GateOp.and, [9, 62]⟩,
      ⟨GateOp.or, [16, 17]⟩,
      ⟨GateOp.or, [64, 19]⟩,
      ⟨GateOp.or, [65, 25]⟩,
      ⟨GateOp.and, [10, 66]⟩,
      ⟨GateOp.or, [15, 16]⟩,
      ⟨GateOp.or, [68, 18]⟩,
      ⟨GateOp.or, [69, 24]⟩,
      ⟨GateOp.and, [11, 70]⟩,
      ⟨GateOp.or, [14, 15]⟩,
      ⟨GateOp.or, [72, 17]⟩,
      ⟨GateOp.or, [73, 23]⟩,
      ⟨GateOp.and, [12, 74]⟩,
      ⟨GateOp.or, [13, 28]⟩,
      ⟨GateOp.or, [76, 31]⟩,
      ⟨GateOp.or, [0, 1]⟩,
      ⟨GateOp.and, [77, 78]⟩,
      ⟨GateOp.or, [79, 35]⟩,
      ⟨GateOp.or, [80, 39]⟩,
      ⟨GateOp.or, [81, 43]⟩,
      ⟨GateOp.or, [82, 47]⟩,
      ⟨GateOp.or, [83, 51]⟩,
      ⟨GateOp.or, [84, 55]⟩,
      ⟨GateOp.or, [85, 59]⟩,
      ⟨GateOp.or, [86, 63]⟩,
      ⟨GateOp.or, [87, 67]⟩,
      ⟨GateOp.or, [88, 71]⟩,
      ⟨GateOp.or, [89, 75]⟩],
    output := 90 }

def mixed65Expression (x : Fin 26 → Bool) : Bool :=
  ((((((((((((((x 13 || (x 0 && ((x 14 || x 16) || x 22))) || (x 1 && ((x 15 || x 21) || x 25))) && (x 0 || x 1)) || (x 2 && (((x 14 || x 20) || x 24) || x 25))) || (x 3 && (((x 13 || x 19) || x 23) || x 24))) || (x 4 && (((x 18 || x 22) || x 23) || x 25))) || (x 5 && (((x 17 || x 21) || x 22) || x 24))) || (x 6 && (((x 16 || x 20) || x 21) || x 23))) || (x 7 && (((x 15 || x 19) || x 20) || x 22))) || (x 8 && (((x 14 || x 18) || x 19) || x 21))) || (x 9 && (((x 13 || x 17) || x 18) || x 20))) || (x 10 && (((x 16 || x 17) || x 19) || x 25))) || (x 11 && (((x 15 || x 16) || x 18) || x 24))) || (x 12 && (((x 14 || x 15) || x 17) || x 23)))

lemma mixed65_size : mixed65.size = 65 := rfl

lemma mixed65_monotone : Monotone2 mixed65 := by
  simp [Monotone2, mixed65]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma mixed65_eval (x : Fin 26 → Bool) :
    mixed65.eval (List.ofFn x) = mixed65Expression x := by
  simp [mixed65, Circuit.eval, Circuit.wires, GateOp.eval, mixed65Expression, List.ofFn_succ]

lemma mixed65_same (x : Fin 26 → Bool) :
    mixed65Expression x = baselineExpression x := by
  unfold mixed65Expression baselineExpression
  rw [mixed_pair]
  simp only [Bool.or_assoc]

lemma mixed65_equiv (x : Fin 26 → Bool) :
    mixed65.eval (List.ofFn x) = baseline.eval (List.ofFn x) := by
  rw [mixed65_eval, mixed65_same, baseline_eval]

lemma mixed65_correct (x : Fin 26 → Bool) :
    mixed65.eval (List.ofFn x) = true ↔
      ∃ p l : Fin 13, (p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ) ∧
        x (pointWire p) = true ∧ x (lineWire l) = true := by
  rw [mixed65_equiv, baseline_correct]

lemma mixed65_sets (s t : Finset (Fin 13)) :
    mixed65.eval (List.ofFn (baselineBits s t)) = true ↔
      ∃ p ∈ s, ∃ l ∈ t, (p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ) := by
  rw [mixed65_equiv, baseline_sets]

end PEqualNP.Outside.L_meta_2056_aux
