import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2602_aux

def incidence (p l : Fin 13) : Prop :=
  p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9

lemma incidence_diagonal (p : Fin 13) : incidence p p :=
  Or.inl rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
set_option synthInstance.maxSize 4096 in
lemma incidence_no_rectangle : ∀ p q l m : Fin 13,
    p ≠ q → l ≠ m → incidence p l → incidence p m → incidence q l →
    ¬ incidence q m := by
  unfold incidence
  decide

lemma incidence_point_degree : ∀ p : Fin 13,
    ((Finset.univ : Finset (Fin 13)).filter
      (fun l => p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9)).card = 4 := by
  decide

lemma incidence_line_degree : ∀ l : Fin 13,
    ((Finset.univ : Finset (Fin 13)).filter
      (fun p => p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9)).card = 4 := by
  decide

lemma incidence_edge_count :
    ((Finset.univ : Finset (Fin 13 × Fin 13)).filter
      (fun e => e.1 = e.2 ∨ e.1 = e.2 + 1 ∨ e.1 = e.2 + 3 ∨
        e.1 = e.2 + 9)).card = 52 := by
  decide

lemma incidence_deleted_edge_count :
    ((Finset.univ : Finset (Fin 13 × Fin 13)).filter
      (fun e => e.1 ≠ 0 ∧ e.2 ≠ 0 ∧
        (e.1 = e.2 ∨ e.1 = e.2 + 1 ∨ e.1 = e.2 + 3 ∨
          e.1 = e.2 + 9))).card = 45 := by
  decide

lemma incidence_deleted_cover_bound (P L : Finset (Fin 13))
    (cover : ∀ p l : Fin 13, p ≠ 0 → l ≠ 0 → incidence p l → p ∈ P ∨ l ∈ L) :
    12 ≤ P.card + L.card := by
  have sub : (Finset.univ.erase 0 : Finset (Fin 13)) ⊆ P ∪ L := by
    intro i hi
    have hi0 : i ≠ 0 := (Finset.mem_erase.mp hi).1
    exact Finset.mem_union.mpr (cover i i hi0 hi0 (incidence_diagonal i))
  calc
    12 = (Finset.univ.erase 0 : Finset (Fin 13)).card := by decide
    _ ≤ (P ∪ L).card := Finset.card_le_card sub
    _ ≤ P.card + L.card := Finset.card_union_le P L


open PEqualNP.CircuitLowerBounds

def activeStep (n : ℕ) (C : Circuit) (base : ℕ → Bool) (a w : ℕ) : Prop :=
  ∃ (j b : ℕ) (g : Gate), w = n + j ∧ C.gates[j]? = some g ∧
    (g.inputs = [a, b] ∨ g.inputs = [b, a]) ∧
    (g.op = .or ∨ base b = true)

lemma trace_carries (n : ℕ) (C : Circuit) (base d : ℕ → Bool)
    (ops : ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.op = .and ∨ g.op = .or)
    (rec : ∀ j (g : Gate) a b, C.gates[j]? = some g → g.inputs = [a, b] →
      (g.op = .and → d (n + j) = (base a && d b || d a && base b)) ∧
      (g.op = .or → d (n + j) = (d a || d b)))
    {start finish : ℕ} (init : d start = true)
    (path : Relation.ReflTransGen (activeStep n C base) start finish) :
    d finish = true := by
  induction path with
  | refl => exact init
  | tail _ step ih =>
    obtain ⟨j, b, g, rfl, hg, inputs, pass⟩ := step
    rcases inputs with e | e
    · obtain ⟨ha, ho⟩ := rec _ _ _ _ hg e
      rcases ops j g hg with h | h
      · rcases pass with bad | side
        · rw [h] at bad
          contradiction
        · simp [ha h, ih, side]
      · simp [ho h, ih]
    · obtain ⟨ha, ho⟩ := rec _ _ _ _ hg e
      rcases ops j g hg with h | h
      · rcases pass with bad | side
        · rw [h] at bad
          contradiction
        · simp [ha h, ih, side]
      · simp [ho h, ih]

lemma false_trace_no_path (n : ℕ) (C : Circuit) (base d : ℕ → Bool)
    (ops : ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.op = .and ∨ g.op = .or)
    (rec : ∀ j (g : Gate) a b, C.gates[j]? = some g → g.inputs = [a, b] →
      (g.op = .and → d (n + j) = (base a && d b || d a && base b)) ∧
      (g.op = .or → d (n + j) = (d a || d b)))
    {start finish : ℕ} (init : d start = true) (final : d finish = false) :
    ¬ Relation.ReflTransGen (activeStep n C base) start finish := by
  intro path
  have ht := trace_carries n C base d ops rec init path
  exact Bool.noConfusion (ht.symm.trans final)

lemma true_trace_reachable (n : ℕ) (C : Circuit) (base d : ℕ → Bool)
    (wf : ∀ j (g : Gate), C.gates[j]? = some g →
      (g.op = .and ∨ g.op = .or) ∧
      ∃ a b : ℕ, g.inputs = [a, b] ∧ a < n + j ∧ b < n + j)
    (rec : ∀ j (g : Gate) a b, C.gates[j]? = some g → g.inputs = [a, b] →
      (g.op = .and → d (n + j) = (base a && d b || d a && base b)) ∧
      (g.op = .or → d (n + j) = (d a || d b)))
    (start : ℕ) (init : ∀ k < n, d k = decide (k = start))
    (i : ℕ) (hi : i < n + C.gates.length) (truth : d i = true) :
    Relation.ReflTransGen (activeStep n C base) start i := by
  revert hi truth
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hi truth
    by_cases hin : i < n
    · have eq : i = start := of_decide_eq_true ((init i hin).symm.trans truth)
      subst i
      exact .refl
    · let j := i - n
      have eq : i = n + j := by dsimp [j]; omega
      have hj : j < C.gates.length := by omega
      let g := C.gates[j]
      have hg : C.gates[j]? = some g := List.getElem?_eq_getElem hj
      obtain ⟨hop, a, b, ins, ha, hb⟩ := wf j g hg
      obtain ⟨ra, ro⟩ := rec j g a b hg ins
      have pa (h : d a = true) :
          Relation.ReflTransGen (activeStep n C base) start a :=
        ih a (by omega) (by omega) h
      have pb (h : d b = true) :
          Relation.ReflTransGen (activeStep n C base) start b :=
        ih b (by omega) (by omega) h
      rcases hop with hand | hor
      · rw [eq, ra hand] at truth
        rcases Bool.or_eq_true_iff.mp truth with h | h
        · obtain ⟨hbase, hd⟩ := Bool.and_eq_true_iff.mp h
          exact (pb hd).tail ⟨j, a, g, eq, hg, Or.inr ins, Or.inr hbase⟩
        · obtain ⟨hd, hbase⟩ := Bool.and_eq_true_iff.mp h
          exact (pa hd).tail ⟨j, b, g, eq, hg, Or.inl ins, Or.inr hbase⟩
      · rw [eq, ro hor] at truth
        rcases Bool.or_eq_true_iff.mp truth with h | h
        · exact (pa h).tail ⟨j, b, g, eq, hg, Or.inl ins, Or.inl hor⟩
        · exact (pb h).tail ⟨j, a, g, eq, hg, Or.inr ins, Or.inl hor⟩

lemma trace_true_iff_reachable (n : ℕ) (C : Circuit) (base d : ℕ → Bool)
    (wf : ∀ j (g : Gate), C.gates[j]? = some g →
      (g.op = .and ∨ g.op = .or) ∧
      ∃ a b : ℕ, g.inputs = [a, b] ∧ a < n + j ∧ b < n + j)
    (rec : ∀ j (g : Gate) a b, C.gates[j]? = some g → g.inputs = [a, b] →
      (g.op = .and → d (n + j) = (base a && d b || d a && base b)) ∧
      (g.op = .or → d (n + j) = (d a || d b)))
    (start : ℕ) (hs : start < n) (init : ∀ k < n, d k = decide (k = start))
    (i : ℕ) (hi : i < n + C.gates.length) :
    d i = true ↔ Relation.ReflTransGen (activeStep n C base) start i := by
  constructor
  · exact true_trace_reachable n C base d wf rec start init i hi
  · exact trace_carries n C base d (fun j g h => (wf j g h).1) rec
      ((init start hs).trans (by simp))

lemma trace_unique (n : ℕ) (C : Circuit) (base d e : ℕ → Bool)
    (wf : ∀ j (g : Gate), C.gates[j]? = some g →
      (g.op = .and ∨ g.op = .or) ∧
      ∃ a b : ℕ, g.inputs = [a, b] ∧ a < n + j ∧ b < n + j)
    (rec : ∀ f ∈ [d, e], ∀ j (g : Gate) a b, C.gates[j]? = some g →
      g.inputs = [a, b] →
      (g.op = .and → f (n + j) = (base a && f b || f a && base b)) ∧
      (g.op = .or → f (n + j) = (f a || f b)))
    (start : ℕ) (hs : start < n)
    (init : ∀ f ∈ [d, e], ∀ k < n, f k = decide (k = start))
    (i : ℕ) (hi : i < n + C.gates.length) : d i = e i := by
  have hd := trace_true_iff_reachable n C base d wf (rec d (by simp)) start hs
    (init d (by simp)) i hi
  have he := trace_true_iff_reachable n C base e wf (rec e (by simp)) start hs
    (init e (by simp)) i hi
  have h := hd.trans he.symm
  cases hdi : d i <;> cases hei : e i <;> simp_all


open scoped Pointwise

def incidenceNeighborhood (S : Finset (Fin 13)) : Finset (Fin 13) :=
  Finset.univ.filter fun l => ∃ p ∈ S,
    p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9

def incidenceShifts : Finset (Fin 13) := {0, 12, 10, 4}

set_option synthInstance.maxSize 4096 in
lemma incidence_shift_iff : ∀ p l : Fin 13,
    (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ↔
    ∃ t ∈ incidenceShifts, p + t = l := by
  decide

lemma incidenceNeighborhood_eq_add (S : Finset (Fin 13)) :
    incidenceNeighborhood S = S + incidenceShifts := by
  ext l
  simp only [incidenceNeighborhood, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_add, incidence_shift_iff]

lemma incidence_neighborhood_expand : ∀ S : Finset (Fin 13),
    S.Nonempty → incidenceNeighborhood S ≠ Finset.univ →
    S.card + 3 ≤ (incidenceNeighborhood S).card := by
  intro S hs hn
  have ht : incidenceShifts.Nonempty := ⟨0, by simp [incidenceShifts]⟩
  have hfour : incidenceShifts.card = 4 := by decide
  have hcd := ZMod.cauchy_davenport (p := 13)
    (s := show Finset (ZMod 13) from S)
    (t := show Finset (ZMod 13) from incidenceShifts) (by decide) hs ht
  change min 13 (S.card + incidenceShifts.card - 1) ≤ (S + incidenceShifts).card at hcd
  rw [← incidenceNeighborhood_eq_add, hfour] at hcd
  have hlt : (incidenceNeighborhood S).card < 13 := by
    have h := Finset.card_lt_card
      (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, hn⟩)
    simpa using h
  simp only [min_le_iff] at hcd
  omega

lemma incidence_mixed_cover_bound (P L : Finset (Fin 13))
    (hP : P ≠ Finset.univ) (hL : L ≠ Finset.univ)
    (cover : ∀ p l : Fin 13,
      (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) → p ∈ P ∨ l ∈ L) :
    16 ≤ P.card + L.card := by
  have hS : (Finset.univ \ P).Nonempty := by
    by_contra h
    apply hP
    apply Finset.eq_univ_of_forall
    intro p
    by_contra hp
    apply h
    exact ⟨p, by simp [hp]⟩
  have hsub : incidenceNeighborhood (Finset.univ \ P) ⊆ L := by
    intro l hl
    obtain ⟨p, hp, hi⟩ := (Finset.mem_filter.mp hl).2
    exact (cover p l hi).resolve_left (Finset.mem_sdiff.mp hp).2
  have hnot : incidenceNeighborhood (Finset.univ \ P) ≠ Finset.univ := by
    intro he
    apply hL
    apply Finset.eq_univ_of_forall
    intro l
    apply hsub
    rw [he]
    exact Finset.mem_univ l
  have hbound := incidence_neighborhood_expand (Finset.univ \ P) hS hnot
  have hcard := Finset.card_le_card hsub
  have hsum := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ P)
  have hu : (Finset.univ : Finset (Fin 13)).card = 13 := by decide
  omega


open PEqualNP.CircuitLowerBounds

def upper65Circuit : Circuit :=
  ⟨[
    ⟨.or, [0, 1]⟩,
    ⟨.or, [26, 3]⟩,
    ⟨.or, [27, 9]⟩,
    ⟨.and, [13, 28]⟩,
    ⟨.or, [2, 3]⟩,
    ⟨.or, [30, 5]⟩,
    ⟨.or, [31, 11]⟩,
    ⟨.and, [15, 32]⟩,
    ⟨.or, [3, 4]⟩,
    ⟨.or, [34, 6]⟩,
    ⟨.or, [35, 12]⟩,
    ⟨.and, [16, 36]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.or, [38, 7]⟩,
    ⟨.or, [39, 0]⟩,
    ⟨.and, [17, 40]⟩,
    ⟨.or, [5, 6]⟩,
    ⟨.or, [42, 8]⟩,
    ⟨.or, [43, 1]⟩,
    ⟨.and, [18, 44]⟩,
    ⟨.or, [6, 7]⟩,
    ⟨.or, [46, 9]⟩,
    ⟨.or, [47, 2]⟩,
    ⟨.and, [19, 48]⟩,
    ⟨.or, [7, 8]⟩,
    ⟨.or, [50, 10]⟩,
    ⟨.or, [51, 3]⟩,
    ⟨.and, [20, 52]⟩,
    ⟨.or, [8, 9]⟩,
    ⟨.or, [54, 11]⟩,
    ⟨.or, [55, 4]⟩,
    ⟨.and, [21, 56]⟩,
    ⟨.or, [9, 10]⟩,
    ⟨.or, [58, 12]⟩,
    ⟨.or, [59, 5]⟩,
    ⟨.and, [22, 60]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.or, [62, 0]⟩,
    ⟨.or, [63, 6]⟩,
    ⟨.and, [23, 64]⟩,
    ⟨.or, [11, 12]⟩,
    ⟨.or, [66, 1]⟩,
    ⟨.or, [67, 7]⟩,
    ⟨.and, [24, 68]⟩,
    ⟨.or, [12, 0]⟩,
    ⟨.or, [70, 2]⟩,
    ⟨.or, [71, 8]⟩,
    ⟨.and, [25, 72]⟩,
    ⟨.or, [29, 33]⟩,
    ⟨.or, [74, 37]⟩,
    ⟨.or, [75, 41]⟩,
    ⟨.or, [76, 45]⟩,
    ⟨.or, [77, 49]⟩,
    ⟨.or, [78, 53]⟩,
    ⟨.or, [79, 57]⟩,
    ⟨.or, [80, 61]⟩,
    ⟨.or, [81, 65]⟩,
    ⟨.or, [82, 69]⟩,
    ⟨.or, [83, 73]⟩,
    ⟨.or, [84, 1]⟩,
    ⟨.or, [85, 2]⟩,
    ⟨.or, [86, 4]⟩,
    ⟨.or, [87, 10]⟩,
    ⟨.or, [84, 14]⟩,
    ⟨.and, [88, 89]⟩], 90⟩

def upper65Star (x : Fin 26 → Bool) (l : Fin 13) : Bool :=
  x (Fin.natAdd 13 l) &&
    (x (Fin.castAdd 13 l) || x (Fin.castAdd 13 (l + 1)) ||
      x (Fin.castAdd 13 (l + 3)) || x (Fin.castAdd 13 (l + 9)))

def upper65Rest (x : Fin 26 → Bool) : Bool :=
  upper65Star x 0 || upper65Star x 2 || upper65Star x 3 || upper65Star x 4 || upper65Star x 5 || upper65Star x 6 || upper65Star x 7 || upper65Star x 8 || upper65Star x 9 || upper65Star x 10 || upper65Star x 11 || upper65Star x 12

def upper65B (x : Fin 26 → Bool) : Bool := x 1 || x 2 || x 4 || x 10

lemma upper65_size : upper65Circuit.size = 65 := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
lemma upper65_eval (x : Fin 26 → Bool) :
    upper65Circuit.eval (List.ofFn x) =
      ((upper65Rest x || upper65B x) && (upper65Rest x || x 14)) := by
  simp [upper65Circuit, Circuit.eval, Circuit.wires, GateOp.eval,
    List.ofFn_succ, List.ofFn_zero, upper65Rest, upper65Star, upper65B, Bool.or_assoc]

lemma upper65_absorb (r b y : Bool) :
    ((r || b) && (r || y)) = (r || (y && b)) := by
  cases r <;> cases b <;> cases y <;> rfl

def upper65Lines : List (Fin 13) := [0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 1]

lemma upper65_lines_mem (l : Fin 13) : l ∈ upper65Lines := by
  fin_cases l <;> simp [upper65Lines]

lemma upper65_eval_stars (x : Fin 26 → Bool) :
    upper65Circuit.eval (List.ofFn x) = upper65Lines.any (upper65Star x) := by
  rw [upper65_eval, upper65_absorb]
  simp [upper65Lines, upper65Rest, upper65Star, upper65B, Bool.or_assoc]

lemma upper65_star_true (x : Fin 26 → Bool) (l : Fin 13) :
    upper65Star x l = true ↔ ∃ p : Fin 13,
      (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧
      x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true := by
  simp only [upper65Star, Bool.and_eq_true, Bool.or_eq_true, or_assoc]
  constructor
  · rintro ⟨hl, h | h | h | h⟩
    · exact ⟨l, Or.inl rfl, h, hl⟩
    · exact ⟨l + 1, Or.inr (Or.inl rfl), h, hl⟩
    · exact ⟨l + 3, Or.inr (Or.inr (Or.inl rfl)), h, hl⟩
    · exact ⟨l + 9, Or.inr (Or.inr (Or.inr rfl)), h, hl⟩
  · rintro ⟨p, h | h | h | h, hp, hl⟩
    · exact ⟨hl, Or.inl (h ▸ hp)⟩
    · exact ⟨hl, Or.inr (Or.inl (h ▸ hp))⟩
    · exact ⟨hl, Or.inr (Or.inr (Or.inl (h ▸ hp)))⟩
    · exact ⟨hl, Or.inr (Or.inr (Or.inr (h ▸ hp)))⟩

lemma upper65_semantics (x : Fin 26 → Bool) :
    upper65Circuit.eval (List.ofFn x) = true ↔ ∃ p l : Fin 13,
      (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧
      x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true := by
  rw [upper65_eval_stars, List.any_eq_true]
  constructor
  · rintro ⟨l, _, hl⟩
    obtain ⟨p, hp⟩ := (upper65_star_true x l).mp hl
    exact ⟨p, l, hp⟩
  · rintro ⟨p, l, hp⟩
    exact ⟨l, upper65_lines_mem l, (upper65_star_true x l).mpr ⟨p, hp⟩⟩

lemma upper65_gate_bound (j : ℕ) (g : Gate)
    (hj : upper65Circuit.gates[j]? = some g) : j < 65 := by
  by_contra h
  have hn : upper65Circuit.gates[j]? = none :=
    List.getElem?_eq_none (by change 65 ≤ j; omega)
  simp [hj] at hn

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
lemma upper65_valid (j : ℕ) (g : Gate)
    (hj : upper65Circuit.gates[j]? = some g) :
    (g.op = .and ∨ g.op = .or) ∧ ∃ a b : ℕ,
      g.inputs = [a, b] ∧ a ≠ b ∧ a < 26 + j ∧ b < 26 + j := by
  have jb := upper65_gate_bound j g hj
  interval_cases j <;>
    simp only [upper65Circuit, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.some.injEq] at hj <;>
    subst g <;> norm_num

def upper65Base0 : List Bool :=
  (List.range 91).map fun i => [0, 26, 27, 28, 40, 63, 64, 70, 71, 72].contains i

def upper65Base13 : List Bool :=
  (List.range 91).map fun i => [13].contains i

set_option maxRecDepth 4096 in
lemma upper65_wires0 :
    upper65Circuit.wires (List.ofFn fun i : Fin 26 => decide (i.val = 0)) =
      upper65Base0 := by decide

set_option maxRecDepth 4096 in
lemma upper65_wires13 :
    upper65Circuit.wires (List.ofFn fun i : Fin 26 => decide (i.val = 13)) =
      upper65Base13 := by decide

def upper65Trace13 (i : ℕ) : Bool :=
  [13, 29, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89].contains i

def upper65Trace0 (i : ℕ) : Bool :=
  [0, 26, 27, 28, 29, 40, 63, 64, 70, 71, 72, 74, 75, 76, 77,
    78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89].contains i

lemma upper65_trace13_init (i : ℕ) (hi : i < 26) :
    upper65Trace13 i = decide (i = 13) := by
  interval_cases i <;> decide

lemma upper65_trace0_init (i : ℕ) (hi : i < 26) :
    upper65Trace0 i = decide (i = 0) := by
  interval_cases i <;> decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
lemma upper65_trace13_rec (j : ℕ) (g : Gate) (a b : ℕ)
    (hj : upper65Circuit.gates[j]? = some g) (ins : g.inputs = [a, b]) :
    (g.op = .and → upper65Trace13 (26 + j) =
      ((upper65Circuit.wires (List.ofFn fun i : Fin 26 => decide (i.val = 0))).getD a false &&
        upper65Trace13 b || upper65Trace13 a &&
        (upper65Circuit.wires (List.ofFn fun i : Fin 26 => decide (i.val = 0))).getD b false)) ∧
    (g.op = .or → upper65Trace13 (26 + j) = (upper65Trace13 a || upper65Trace13 b)) := by
  simp only [upper65_wires0]
  have jb := upper65_gate_bound j g hj
  interval_cases j <;>
    simp only [upper65Circuit, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.some.injEq] at hj <;>
    subst g <;>
    simp only [List.cons.injEq, and_true] at ins <;>
    rcases ins with ⟨rfl, rfl⟩ <;>
    norm_num [upper65Trace13, upper65Base0]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
lemma upper65_trace0_rec (j : ℕ) (g : Gate) (a b : ℕ)
    (hj : upper65Circuit.gates[j]? = some g) (ins : g.inputs = [a, b]) :
    (g.op = .and → upper65Trace0 (26 + j) =
      ((upper65Circuit.wires (List.ofFn fun i : Fin 26 => decide (i.val = 13))).getD a false &&
        upper65Trace0 b || upper65Trace0 a &&
        (upper65Circuit.wires (List.ofFn fun i : Fin 26 => decide (i.val = 13))).getD b false)) ∧
    (g.op = .or → upper65Trace0 (26 + j) = (upper65Trace0 a || upper65Trace0 b)) := by
  simp only [upper65_wires13]
  have jb := upper65_gate_bound j g hj
  interval_cases j <;>
    simp only [upper65Circuit, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.some.injEq] at hj <;>
    subst g <;>
    simp only [List.cons.injEq, and_true] at ins <;>
    rcases ins with ⟨rfl, rfl⟩ <;>
    norm_num [upper65Trace0, upper65Base13]

lemma upper65_trace13_output : upper65Trace13 upper65Circuit.output = false := rfl

lemma upper65_trace0_output : upper65Trace0 upper65Circuit.output = false := rfl


lemma rectangle_filter_point_iff {α β : Type*} [DecidableEq α] [DecidableEq β]
    (R : α → β → Prop) (X : Finset α) (Y : Finset β) (p : α) (hp : p ∈ X) :
    (∀ (f : α → Bool) (g : β → Bool),
      (∃ x ∈ X, f x = true) → (∃ y ∈ Y, g y = true) → f p = true →
      ∃ x y, R x y ∧ f x = true ∧ g y = true) ↔ ∀ y ∈ Y, R p y := by
  constructor
  · intro clean y hy
    obtain ⟨x, z, hR, hx, hz⟩ := clean (fun x => decide (x = p))
      (fun z => decide (z = y)) ⟨p, hp, by simp⟩ ⟨y, hy, by simp⟩ (by simp)
    simp only [decide_eq_true_eq] at hx hz
    subst x z
    exact hR
  · intro full f g _ hy hp
    obtain ⟨y, hy, hgy⟩ := hy
    exact ⟨p, y, full y hy, hp, hgy⟩

lemma rectangle_filter_line_iff {α β : Type*} [DecidableEq α] [DecidableEq β]
    (R : α → β → Prop) (X : Finset α) (Y : Finset β) (l : β) (hl : l ∈ Y) :
    (∀ (f : α → Bool) (g : β → Bool),
      (∃ x ∈ X, f x = true) → (∃ y ∈ Y, g y = true) → g l = true →
      ∃ x y, R x y ∧ f x = true ∧ g y = true) ↔ ∀ x ∈ X, R x l := by
  constructor
  · intro clean x hx
    obtain ⟨p, y, hR, hp, hy⟩ := clean (fun p => decide (p = x))
      (fun y => decide (y = l)) ⟨x, hx, by simp⟩ ⟨l, hl, by simp⟩ (by simp)
    simp only [decide_eq_true_eq] at hp hy
    subst p y
    exact hR
  · intro full f g hx _ hl
    obtain ⟨x, hx, hfx⟩ := hx
    exact ⟨x, l, full x hx, hfx, hl⟩

lemma rectangle_full_points_card {α β : Type*} [DecidableEq α] [DecidableEq β]
    (R : α → β → Prop) [DecidableRel R]
    (noRect : ∀ p q l m, p ≠ q → l ≠ m → R p l → R p m → R q l → ¬ R q m)
    (X : Finset α) (Y : Finset β) (hY : 2 ≤ Y.card) :
    (X.filter (fun p => ∀ l ∈ Y, R p l)).card ≤ 1 := by
  obtain ⟨l, hl, m, hm, hlm⟩ := Finset.one_lt_card.mp (by omega : 1 < Y.card)
  apply Finset.card_le_one.mpr
  intro p hp q hq
  by_contra hpq
  have hp' := (Finset.mem_filter.mp hp).2
  have hq' := (Finset.mem_filter.mp hq).2
  exact noRect p q l m hpq hlm (hp' l hl) (hp' m hm) (hq' l hl) (hq' m hm)

lemma rectangle_full_lines_card {α β : Type*} [DecidableEq α] [DecidableEq β]
    (R : α → β → Prop) [DecidableRel R]
    (noRect : ∀ p q l m, p ≠ q → l ≠ m → R p l → R p m → R q l → ¬ R q m)
    (X : Finset α) (Y : Finset β) (hX : 2 ≤ X.card) :
    (Y.filter (fun l => ∀ p ∈ X, R p l)).card ≤ 1 := by
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp (by omega : 1 < X.card)
  apply Finset.card_le_one.mpr
  intro l hl m hm
  by_contra hlm
  have hl' := (Finset.mem_filter.mp hl).2
  have hm' := (Finset.mem_filter.mp hm).2
  exact noRect p q l m hpq hlm (hl' p hp) (hm' p hp) (hl' q hq) (hm' q hq)

lemma rectangle_point_filter_absorb {α β : Type*}
    (X : Finset α) (Y : Finset β) (p : α) (hp : p ∈ X)
    (f : α → Prop) (g : β → Prop) :
    ((∃ x ∈ X, f x) ∧ (∃ y ∈ Y, g y)) ∧ f p ↔ f p ∧ ∃ y ∈ Y, g y := by
  constructor
  · exact fun h => ⟨h.2, h.1.2⟩
  · exact fun h => ⟨⟨⟨p, hp, h.1⟩, h.2⟩, h.1⟩

lemma rectangle_line_filter_absorb {α β : Type*}
    (X : Finset α) (Y : Finset β) (l : β) (hl : l ∈ Y)
    (f : α → Prop) (g : β → Prop) :
    ((∃ x ∈ X, f x) ∧ (∃ y ∈ Y, g y)) ∧ g l ↔ (∃ x ∈ X, f x) ∧ g l := by
  constructor
  · exact fun h => ⟨h.1.1, h.2⟩
  · exact fun h => ⟨⟨h.1, ⟨l, hl, h.2⟩⟩, h.2⟩

lemma rectangle_filters_expand {α β : Type*}
    (X A : Finset α) (Y B : Finset β) (hA : A ⊆ X) (hB : B ⊆ Y)
    (f : α → Prop) (g : β → Prop) :
    ((∃ x ∈ X, f x) ∧ (∃ y ∈ Y, g y)) ∧
        ((∃ a ∈ A, f a) ∨ ∃ b ∈ B, g b) ↔
      ((∃ a ∈ A, f a) ∧ ∃ y ∈ Y, g y) ∨
        ((∃ x ∈ X, f x) ∧ ∃ b ∈ B, g b) := by
  constructor
  · rintro ⟨⟨hx, hy⟩, ha | hb⟩
    · exact Or.inl ⟨ha, hy⟩
    · exact Or.inr ⟨hx, hb⟩
  · rintro (⟨⟨a, ha, hfa⟩, hy⟩ | ⟨hx, ⟨b, hb, hgb⟩⟩)
    · exact ⟨⟨⟨a, hA ha, hfa⟩, hy⟩, Or.inl ⟨a, ha, hfa⟩⟩
    · exact ⟨⟨hx, ⟨b, hB hb, hgb⟩⟩, Or.inr ⟨b, hb, hgb⟩⟩


lemma rectangle_filter_pair_footprint {α β : Type*} [DecidableEq α] [DecidableEq β]
    (X A : Finset α) (Y B : Finset β) (p : α) (l : β) :
    ((∃ x ∈ X, decide (x = p) = true) ∧ (∃ y ∈ Y, decide (y = l) = true)) ∧
        ((∃ a ∈ A, decide (a = p) = true) ∨ ∃ b ∈ B, decide (b = l) = true) ↔
      (p ∈ A ∩ X ∧ l ∈ Y) ∨ (p ∈ X ∧ l ∈ B ∩ Y) := by
  simp only [decide_eq_true_eq, exists_eq_right, Finset.mem_inter]
  tauto

lemma rectangle_filter_clean_centers {α β : Type*} [DecidableEq α] [DecidableEq β]
    (R : α → β → Prop) (X A : Finset α) (Y B : Finset β)
    (clean : ∀ (f : α → Bool) (g : β → Bool),
      (∃ x ∈ X, f x = true) → (∃ y ∈ Y, g y = true) →
      ((∃ a ∈ A, f a = true) ∨ ∃ b ∈ B, g b = true) →
      ∃ x y, R x y ∧ f x = true ∧ g y = true) :
    (∀ p ∈ A ∩ X, ∀ l ∈ Y, R p l) ∧
      (∀ l ∈ B ∩ Y, ∀ p ∈ X, R p l) := by
  constructor
  · intro p hp
    obtain ⟨ha, hx⟩ := Finset.mem_inter.mp hp
    apply (rectangle_filter_point_iff R X Y p hx).mp
    intro f g hf hg hfp
    exact clean f g hf hg (Or.inl ⟨p, ha, hfp⟩)
  · intro l hl
    obtain ⟨hb, hy⟩ := Finset.mem_inter.mp hl
    apply (rectangle_filter_line_iff R X Y l hy).mp
    intro f g hf hg hgl
    exact clean f g hf hg (Or.inr ⟨l, hb, hgl⟩)

lemma rectangle_filter_two_stars {α β : Type*} [DecidableEq α] [DecidableEq β]
    (R : α → β → Prop) [DecidableRel R]
    (noRect : ∀ p q l m, p ≠ q → l ≠ m → R p l → R p m → R q l → ¬ R q m)
    (X A : Finset α) (Y B : Finset β) (hX : 2 ≤ X.card) (hY : 2 ≤ Y.card)
    (clean : ∀ (f : α → Bool) (g : β → Bool),
      (∃ x ∈ X, f x = true) → (∃ y ∈ Y, g y = true) →
      ((∃ a ∈ A, f a = true) ∨ ∃ b ∈ B, g b = true) →
      ∃ x y, R x y ∧ f x = true ∧ g y = true) :
    (A ∩ X).card ≤ 1 ∧ (B ∩ Y).card ≤ 1 := by
  obtain ⟨hp, hl⟩ := rectangle_filter_clean_centers R X A Y B clean
  constructor
  · apply le_trans (Finset.card_le_card ?_) (rectangle_full_points_card R noRect X Y hY)
    intro p h
    exact Finset.mem_filter.mpr ⟨(Finset.mem_inter.mp h).2, hp p h⟩
  · apply le_trans (Finset.card_le_card ?_) (rectangle_full_lines_card R noRect X Y hX)
    intro l h
    exact Finset.mem_filter.mpr ⟨(Finset.mem_inter.mp h).2, hl l h⟩

lemma upper65_witness :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (63 : ℕ) ≤ x1.size ∧ x1.size ≤ (65 : ℕ) ∧ (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (26 : ℕ) + x2 ∧ x6 < (26 : ℕ) + x2) ∧ (∀ (x2 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true ↔ ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), (x3 = x4 ∨ x3 = x4 + (1 : Fin (13 : ℕ)) ∨ x3 = x4 + (3 : Fin (13 : ℕ)) ∨ x3 = x4 + (9 : Fin (13 : ℕ))) ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true) ∧ (∃ (x2 : ℕ → Bool), (∀ x3 < (26 : ℕ), x2 x3 = Decidable.decide (x3 = (13 : ℕ))) ∧ (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate) (x5 x6 : ℕ), x1.gates[x3]? = Option.some x4 → x4.inputs = [x5, x6] → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and → x2 ((26 : ℕ) + x3) = ((x1.wires (List.ofFn fun (x10 : Fin (26 : ℕ)) => Decidable.decide (↑x10 = (0 : ℕ)))).getD x5 Bool.false && x2 x6 || x2 x5 && (x1.wires (List.ofFn fun (x10 : Fin (26 : ℕ)) => Decidable.decide (↑x10 = (0 : ℕ)))).getD x6 Bool.false)) ∧ (x4.op = PEqualNP.CircuitLowerBounds.GateOp.or → x2 ((26 : ℕ) + x3) = (x2 x5 || x2 x6))) ∧ x2 x1.output = Bool.false) ∧ ∃ (x2 : ℕ → Bool), (∀ x3 < (26 : ℕ), x2 x3 = Decidable.decide (x3 = (0 : ℕ))) ∧ (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate) (x5 x6 : ℕ), x1.gates[x3]? = Option.some x4 → x4.inputs = [x5, x6] → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and → x2 ((26 : ℕ) + x3) = ((x1.wires (List.ofFn fun (x10 : Fin (26 : ℕ)) => Decidable.decide (↑x10 = (13 : ℕ)))).getD x5 Bool.false && x2 x6 || x2 x5 && (x1.wires (List.ofFn fun (x10 : Fin (26 : ℕ)) => Decidable.decide (↑x10 = (13 : ℕ)))).getD x6 Bool.false)) ∧ (x4.op = PEqualNP.CircuitLowerBounds.GateOp.or → x2 ((26 : ℕ) + x3) = (x2 x5 || x2 x6))) ∧ x2 x1.output = Bool.false := by
  refine ⟨upper65Circuit, ?_, ?_, upper65_valid, upper65_semantics, ?_, ?_⟩
  · decide
  · decide
  · exact ⟨upper65Trace13, upper65_trace13_init, upper65_trace13_rec,
      upper65_trace13_output⟩
  · exact ⟨upper65Trace0, upper65_trace0_init, upper65_trace0_rec,
      upper65_trace0_output⟩

end PEqualNP.Outside.L_meta_2602_aux
