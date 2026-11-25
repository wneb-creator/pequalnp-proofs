import Mathlib.Combinatorics.Additive.CauchyDavenport
import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2602_aux

def incidence (p l : Fin 13) : Prop :=
  p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9

lemma incidence_diagonal (p : Fin 13) : incidence p p :=
  Or.inl rfl

lemma incidence_sub_right (p m l : Fin 13) :
    incidence (p - l) (m - l) ↔ incidence p m := by
  simp only [incidence, sub_add_eq_add_sub, sub_left_inj]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
set_option synthInstance.maxSize 4096 in
lemma incidence_no_rectangle_zero : ∀ p q d : Fin 13,
    p ≠ q → d ≠ 0 → incidence p 0 → incidence p d → incidence q 0 →
    ¬ incidence q d := by
  unfold incidence
  decide

lemma incidence_no_rectangle : ∀ p q l m : Fin 13,
    p ≠ q → l ≠ m → incidence p l → incidence p m → incidence q l →
    ¬ incidence q m := by
  intro p q l m hpq hlm hpl hpm hql hqm
  have hpq' : p - l ≠ q - l := by
    intro h
    exact hpq (sub_left_inj.mp h)
  have hdm : m - l ≠ 0 := sub_ne_zero.mpr hlm.symm
  have hpl' : incidence (p - l) 0 := by
    simpa only [sub_self] using (incidence_sub_right p l l).mpr hpl
  have hql' : incidence (q - l) 0 := by
    simpa only [sub_self] using (incidence_sub_right q l l).mpr hql
  exact incidence_no_rectangle_zero (p - l) (q - l) (m - l) hpq' hdm
    hpl' ((incidence_sub_right p m l).mpr hpm)
    hql' ((incidence_sub_right q m l).mpr hqm)


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

namespace OneJunk

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

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
      · rw [if_pos hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [if_neg hi]; exact getD_ge w i (by omega)
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

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

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

def OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

lemma opMono_eq : OpMono Eq := by
  intro op _ l f g h
  rw [List.map_congr_left h]

lemma opMono_imp : OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [if_neg hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [if_pos hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h'; exact ⟨hlt, h'⟩
    · rw [if_neg hlt] at h'; cases h'
  · intro h i hi
    rw [if_pos (h i hi).1]; exact (h i hi).2

lemma biclique_star {n : ℕ} (G : SimpleGraph (Fin n))
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (A B : Finset (Fin n)) (hab : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) :
    A.card ≤ 1 ∨ B.card ≤ 1 := by
  by_contra hcon
  simp only [not_or, not_le] at hcon
  obtain ⟨a, ha, c, hc, hac⟩ := Finset.one_lt_card.mp hcon.1
  obtain ⟨b, hb, d, hd, hbd⟩ := Finset.one_lt_card.mp hcon.2
  exact h4 a b c d hac hbd
    ⟨hab a ha b hb, (hab c hc b hb).symm, hab c hc d hd, (hab a ha d hd).symm⟩

lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

lemma gateVal_eq_val (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    PEqualNP.EdgeOwnership.gateVal n C j x = val C (List.ofFn x) (n + j) := rfl

def OrStep (n : ℕ) (C : Circuit) (w w' : ℕ) : Prop :=
  ∃ k, k < C.gates.length ∧ w = n + k ∧ (gateAt C k).op = GateOp.or ∧
    w' ∈ (gateAt C k).inputs ∧ w' < n + k

lemma orStep_up {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') (hv : val C x w' = true) :
    val C x w = true := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hv
  | head hstep _ ih =>
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (val_or hx hk hop).mpr ⟨_, hin, hlt, ih⟩

lemma or_trace {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) :
    ∀ w : ℕ, val C x w = true →
      ∃ w', Relation.ReflTransGen (OrStep n C) w w' ∧ val C x w' = true ∧
        (w' < n ∨ ∃ h, h < C.gates.length ∧ w' = n + h ∧ (gateAt C h).op ≠ GateOp.or) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < n
    · exact ⟨w, Relation.ReflTransGen.refl, hv, Or.inl hw⟩
    · by_cases hlen : n + C.gates.length ≤ w
      · rw [val_ge hx hlen] at hv; cases hv
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        by_cases hop : (gateAt C k).op = GateOp.or
        · obtain ⟨i, hin, hlt, hi⟩ := (val_or hx hk hop).mp hv
          obtain ⟨w', hr, hv', hw'⟩ := ih i hlt hi
          exact ⟨w', Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hin, hlt⟩ hr, hv', hw'⟩
        · exact ⟨n + k, Relation.ReflTransGen.refl, hv, Or.inr ⟨k, hk, rfl, hop⟩⟩

open PEqualNP.EdgeOwnership in
lemma pairInput_left {n : ℕ} (u v : Fin n) : pairInput u v u = true := by
  simp [pairInput]

open PEqualNP.EdgeOwnership in
lemma pairInput_right {n : ℕ} (u v : Fin n) : pairInput u v v = true := by
  simp [pairInput]

open PEqualNP.EdgeOwnership in
lemma pairInput_true {n : ℕ} (u v w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by
  simp [pairInput]

open PEqualNP.EdgeOwnership in
lemma graphFun_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq, pairInput_true]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  · intro h
    exact ⟨u, v, h, Or.inl rfl, Or.inr rfl⟩

open PEqualNP.EdgeOwnership in
lemma operand_trace {n : ℕ} {C : Circuit} (u v : Fin n) (p : ℕ)
    (hv : val C (List.ofFn (pairInput u v)) p = true) :
    (∃ t : Fin n, (t = u ∨ t = v) ∧ Relation.ReflTransGen (OrStep n C) p t.val) ∨
    (∃ h, h < C.gates.length ∧ (gateAt C h).op ≠ GateOp.or ∧
      Relation.ReflTransGen (OrStep n C) p (n + h) ∧
      val C (List.ofFn (pairInput u v)) (n + h) = true) := by
  obtain ⟨w', hr, hv', hw'⟩ := or_trace (n := n) (C := C) (x := List.ofFn (pairInput u v))
    (by simp) p hv
  rcases hw' with hlt | ⟨h, hh, rfl, hop⟩
  · left
    refine ⟨⟨w', hlt⟩, ?_, hr⟩
    have h1 := val_ofFn C (pairInput u v) ⟨w', hlt⟩
    rw [show (⟨w', hlt⟩ : Fin n).val = w' from rfl, hv'] at h1
    exact (pairInput_true u v _).mp h1.symm
  · right
    exact ⟨h, hh, hop, hr, hv'⟩

open PEqualNP.EdgeOwnership in
lemma reach_var_val {n : ℕ} {C : Circuit} (x : Fin n → Bool) (p : ℕ) (t : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p t.val) (ht : x t = true) :
    val C (List.ofFn x) p = true :=
  orStep_up (n := n) (by simp) hr (by rw [val_ofFn]; exact ht)

open PEqualNP.EdgeOwnership in
lemma side_adj {n : ℕ} (G : SimpleGraph (Fin n)) {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hF : ∀ u v : Fin n, F (pairInput u v) = true → G.Adj u v)
    (a : ℕ) (ha : a < C.gates.length) (hop : (gateAt C a).op = GateOp.and)
    (hbel : ∀ x : Fin n → Bool, val C (List.ofFn x) (n + a) = true → F x = true)
    (p q : ℕ) (hin : (gateAt C a).inputs = [p, q]) (hp : p < n + a) (hq : q < n + a)
    (u v : Fin n) (hu : Relation.ReflTransGen (OrStep n C) p u.val)
    (hv : Relation.ReflTransGen (OrStep n C) q v.val) : G.Adj u v := by
  apply hF
  apply hbel
  rw [val_and (n := n) (by simp) ha hop, hin]
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact ⟨hp, reach_var_val _ _ u hu (pairInput_left u v)⟩
  · exact ⟨hq, reach_var_val _ _ v hv (pairInput_right u v)⟩

open PEqualNP.EdgeOwnership in
lemma edge_trace {n : ℕ} (G : SimpleGraph (Fin n)) {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hF : ∀ u v : Fin n, F (pairInput u v) = true → G.Adj u v)
    (hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = F x)
    (u v : Fin n) (huv : F (pairInput u v) = true) :
    ∃ a, a < C.gates.length ∧ (gateAt C a).op ≠ GateOp.or ∧
      Relation.ReflTransGen (OrStep n C) C.output (n + a) ∧
      val C (List.ofFn (pairInput u v)) (n + a) = true := by
  rcases operand_trace (C := C) u v C.output (by rw [hout]; exact huv) with
    ⟨t, _, hr⟩ | h
  · exfalso
    have h1 := reach_var_val (pairInput t t) _ t hr (pairInput_left t t)
    rw [hout] at h1
    exact G.irrefl (hF t t h1)
  · exact h

lemma below_of_reach {n : ℕ} {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = F x) (a : ℕ)
    (hr : Relation.ReflTransGen (OrStep n C) C.output (n + a)) (x : Fin n → Bool)
    (hv : val C (List.ofFn x) (n + a) = true) : F x = true := by
  rw [← hout]
  exact orStep_up (n := n) (by simp) hr hv

open PEqualNP.EdgeOwnership

lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

lemma orStep_le {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') : w' ≤ w := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact le_rfl
  | head hstep _ ih =>
    obtain ⟨k, _, rfl, _, _, hlt⟩ := hstep
    omega

lemma orStep_cone {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') :
    ∀ k h', w = n + k → w' = n + h' → h' = k ∨ InCone n C h' k := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => intro k h' h1 h2; left; omega
  | @head a c hstep hrest ih =>
    intro k h' h1 h2
    obtain ⟨k0, hk0, e, _, hin, hlt⟩ := hstep
    have hk : k0 = k := by omega
    subst hk
    have hle := orStep_le hrest
    obtain ⟨k1, hk1⟩ : ∃ k1, c = n + k1 := ⟨c - n, by omega⟩
    subst hk1
    right
    rw [inCone_iff]
    exact ⟨hk0, k1, by omega, hin, ih k1 h' rfl h2⟩

lemma operand_cone {n : ℕ} {C : Circuit} {a p h : ℕ} (ha : a < C.gates.length)
    (hin : p ∈ (gateAt C a).inputs) (hp : p < n + a)
    (hr : Relation.ReflTransGen (OrStep n C) p (n + h)) : InCone n C h a := by
  have hle := orStep_le hr
  obtain ⟨k1, rfl⟩ : ∃ k1, p = n + k1 := ⟨p - n, by omega⟩
  rw [inCone_iff]
  exact ⟨ha, k1, by omega, hin, orStep_cone hr k1 h rfl rfl⟩


def TraceCondition {n : ℕ} (C : Circuit) (source : Fin n) (base d : ℕ → Bool) : Prop :=
  (∀ t : Fin n, d t.val = decide (t = source)) ∧
  ∀ j, j < C.gates.length → ∀ a b, (gateAt C j).inputs = [a,b] →
    ((gateAt C j).op = .and → d (n+j) = (base a && d b || d a && base b)) ∧
    ((gateAt C j).op = .or → d (n+j) = (d a || d b))

lemma trace_or_up {n : ℕ} {C : Circuit} {source : Fin n} {base d : ℕ → Bool}
    (h2 : ∀ g ∈ C.gates, g.inputs.length = 2)
    (hd : TraceCondition C source base d) {a b : ℕ}
    (path : Relation.ReflTransGen (OrStep n C) a b) (hb : d b = true) : d a = true := by
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl => exact hb
  | @head a c step rest ih =>
    obtain ⟨j,hj,rfl,ho,hm,_⟩ := step
    obtain ⟨u,v,hi⟩ := List.length_eq_two.mp (h2 _ (gateAt_mem hj))
    rw [(hd.2 j hj u v hi).2 ho]
    rw [hi] at hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl <;> simp [ih]

lemma trace_and_up {n : ℕ} {C : Circuit} {source : Fin n} {base d : ℕ → Bool}
    (hd : TraceCondition C source base d) {j a b : ℕ} (hj : j < C.gates.length)
    (ho : (gateAt C j).op = .and)
    (hi : (gateAt C j).inputs = [a,b] ∨ (gateAt C j).inputs = [b,a])
    (ha : d a = true) (hb : base b = true) : d (n+j) = true := by
  rcases hi with hi | hi
  · rw [(hd.2 j hj a b hi).1 ho]
    simp [ha,hb]
  · rw [(hd.2 j hj b a hi).1 ho]
    simp [ha,hb]

lemma value_and_up {n : ℕ} {C : Circuit} (x : Fin n → Bool)
    {j a b : ℕ} (hj : j < C.gates.length) (ho : (gateAt C j).op = .and)
    (hi : (gateAt C j).inputs = [a,b] ∨ (gateAt C j).inputs = [b,a])
    (ha : a < n+j) (hb : b < n+j)
    (va : val C (List.ofFn x) a = true) (vb : val C (List.ofFn x) b = true) :
    val C (List.ofFn x) (n+j) = true := by
  rw [val_and (n := n) (by simp) hj ho]
  intro i hm
  rcases hi with hi | hi
  · rw [hi] at hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · exact ⟨ha,va⟩
    · exact ⟨hb,vb⟩
  · rw [hi] at hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · exact ⟨hb,vb⟩
    · exact ⟨ha,va⟩

open PEqualNP.TopForm PEqualNP.CleanedNonEdge

set_option maxHeartbeats 2000000 in
lemma topform_one_active_junk_trace {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (model : IsAO2 n C) (top : PEqualNP.TopForm.TopForm G C)
    (spec : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = graphFun G ∅ x)
    (p q : Fin n) (edge : G.Adj p q) (dl dp : ℕ → Bool)
    (small : ((junk G C).filter fun h =>
      val C (List.ofFn (pairInput p q)) (n+h) = true).card ≤ 1)
    (hl : TraceCondition C q (val C (List.ofFn (pairInput p p))) dl)
    (hp : TraceCondition C p (val C (List.ofFn (pairInput q q))) dp) :
    dl C.output = true ∨ dp C.output = true := by
  classical
  obtain ⟨ops,reads,two⟩ := model
  have hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = graphFun G ∅ x := spec
  have hF : ∀ u v : Fin n, graphFun G ∅ (pairInput u v) = true → G.Adj u v :=
    fun u v h => (graphFun_pair G u v).mp h
  obtain ⟨a,ha,hnot,ra,va⟩ := edge_trace G (graphFun G ∅) hF hout p q
    ((graphFun_pair G p q).mpr edge)
  have ao : (gateAt C a).op = .and := by
    rcases ops _ (gateAt_mem ha) with h | h
    · exact h
    · exact (hnot h).elim
  have below : BelowF G C a := fun x hx => below_of_reach (graphFun G ∅) hout a ra x hx
  have badP : val C (List.ofFn (pairInput p p)) (n+a) = true → False :=
    fun h => G.irrefl (hF p p (below _ h))
  have badQ : val C (List.ofFn (pairInput q q)) (n+a) = true → False :=
    fun h => G.irrefl (hF q q (below _ h))
  have pval (w : ℕ) (r : Relation.ReflTransGen (OrStep n C) w p.val) :
      val C (List.ofFn (pairInput p p)) w = true :=
    reach_var_val _ _ p r (pairInput_left p p)
  have qval (w : ℕ) (r : Relation.ReflTransGen (OrStep n C) w q.val) :
      val C (List.ofFn (pairInput q q)) w = true :=
    reach_var_val _ _ q r (pairInput_left q q)
  have pdiff (w : ℕ) (r : Relation.ReflTransGen (OrStep n C) w p.val) : dp w = true :=
    trace_or_up two hp r (by rw [hp.1 p]; simp)
  have qdiff (w : ℕ) (r : Relation.ReflTransGen (OrStep n C) w q.val) : dl w = true :=
    trace_or_up two hl r (by rw [hl.1 q]; simp)
  have uniq : ∀ i ∈ junk G C, val C (List.ofFn (pairInput p q)) (n+i) = true →
      ∀ j ∈ junk G C, val C (List.ofFn (pairInput p q)) (n+j) = true → i = j := by
    intro i hi vi j hj vj
    exact Finset.card_le_one.mp small i (Finset.mem_filter.mpr ⟨hi,vi⟩)
      j (Finset.mem_filter.mpr ⟨hj,vj⟩)
  have dirty_of (j : ℕ) (hj : j < C.gates.length) (jo : (gateAt C j).op = .and)
      (w : ℕ) (hm : w ∈ (gateAt C j).inputs) (hw : w < n+j)
      (h : ℕ) (hh : h < C.gates.length) (hnot : (gateAt C h).op ≠ .or)
      (r : Relation.ReflTransGen (OrStep n C) w (n+h)) :
      h ∈ junk G C ∧ (gateAt C h).op = .and ∧ ¬ BelowF G C h := by
    have ho : (gateAt C h).op = .and := by
      rcases ops _ (gateAt_mem hh) with ho | ho
      · exact ho
      · exact (hnot ho).elim
    have nc : ¬ BelowF G C h := fun bh => top h hh j hj ho bh jo (operand_cone hj hm hw r)
    have dirt : IsDirtyAnd n G C h := by
      refine ⟨ho,hh,?_⟩
      by_contra no
      apply nc
      intro x hx
      by_contra hf
      exact no ⟨x,hx,Bool.eq_false_iff.mpr hf⟩
    exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hh,dirt⟩,ho,nc⟩
  have no_ands_below (h : ℕ) (hh : h < C.gates.length) (ho : (gateAt C h).op = .and)
      (hjunk : h ∈ junk G C) (vh : val C (List.ofFn (pairInput p q)) (n+h) = true)
      (w : ℕ) (hm : w ∈ (gateAt C h).inputs)
      (hw : w < n+h) (vw : val C (List.ofFn (pairInput p q)) w = true) :
      ∃ t : Fin n, (t = p ∨ t = q) ∧ Relation.ReflTransGen (OrStep n C) w t.val := by
    rcases operand_trace (C := C) p q w vw with hit | ⟨k,hk,kn,rk,vk⟩
    · exact hit
    · obtain ⟨kj,_,_⟩ := dirty_of h hh ho w hm hw k hk kn rk
      have eq := uniq k kj vk h hjunk vh
      subst k
      have le := orStep_le rk
      omega
  obtain ⟨u,v,uv⟩ := List.length_eq_two.mp (two _ (gateAt_mem ha))
  have um : u ∈ (gateAt C a).inputs := by simp [uv]
  have vm : v ∈ (gateAt C a).inputs := by simp [uv]
  have uval := (val_and (n := n) (by simp) ha ao).mp va u um
  have vval := (val_and (n := n) (by simp) ha ao).mp va v vm
  have finish : dl (n+a) = true ∨ dp (n+a) = true →
      dl C.output = true ∨ dp C.output = true := by
    rintro (h | h)
    · exact Or.inl (trace_or_up two hl ra h)
    · exact Or.inr (trace_or_up two hp ra h)
  have chain (w z h : ℕ) (wz : (gateAt C a).inputs = [w,z] ∨ (gateAt C a).inputs = [z,w])
      (hw : w < n+a) (hz : z < n+a) (hh : h < C.gates.length)
      (ho : (gateAt C h).op = .and) (hjunk : h ∈ junk G C)
      (rw : Relation.ReflTransGen (OrStep n C) w (n+h))
      (vh : val C (List.ofFn (pairInput p q)) (n+h) = true)
      (t : Fin n) (ht : t = p ∨ t = q) (rz : Relation.ReflTransGen (OrStep n C) z t.val) :
      dl (n+a) = true ∨ dp (n+a) = true := by
    obtain ⟨b,c,bc⟩ := List.length_eq_two.mp (two _ (gateAt_mem hh))
    have bm : b ∈ (gateAt C h).inputs := by simp [bc]
    have cm : c ∈ (gateAt C h).inputs := by simp [bc]
    have vb := (val_and (n := n) (by simp) hh ho).mp vh b bm
    have vc := (val_and (n := n) (by simp) hh ho).mp vh c cm
    obtain ⟨r,hr,rb⟩ := no_ands_below h hh ho hjunk vh b bm vb.1 vb.2
    obtain ⟨s,hs,rc⟩ := no_ands_below h hh ho hjunk vh c cm vc.1 vc.2
    have swap : (gateAt C a).inputs = [z,w] ∨ (gateAt C a).inputs = [w,z] := wz.symm
    rcases hr with rfl | rfl <;> rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
    · exact (badP (value_and_up _ ha ao wz hw hz
        (orStep_up (n := n) (by simp) rw (value_and_up _ hh ho (Or.inl bc) vb.1 vc.1 (pval _ rb) (pval _ rc))) (pval _ rz))).elim
    · exact Or.inl (trace_and_up hl ha ao swap (qdiff _ rz)
        (orStep_up (n := n) (by simp) rw (value_and_up _ hh ho (Or.inl bc) vb.1 vc.1 (pval _ rb) (pval _ rc))))
    · exact Or.inl (trace_and_up hl ha ao wz
        (trace_or_up two hl rw (trace_and_up hl hh ho (Or.inr bc) (qdiff _ rc) (pval _ rb))) (pval _ rz))
    · exact Or.inr (trace_and_up hp ha ao wz
        (trace_or_up two hp rw (trace_and_up hp hh ho (Or.inl bc) (pdiff _ rb) (qval _ rc))) (qval _ rz))
    · exact Or.inl (trace_and_up hl ha ao wz
        (trace_or_up two hl rw (trace_and_up hl hh ho (Or.inl bc) (qdiff _ rb) (pval _ rc))) (pval _ rz))
    · exact Or.inr (trace_and_up hp ha ao wz
        (trace_or_up two hp rw (trace_and_up hp hh ho (Or.inr bc) (pdiff _ rc) (qval _ rb))) (qval _ rz))
    · exact Or.inr (trace_and_up hp ha ao swap (pdiff _ rz)
        (orStep_up (n := n) (by simp) rw (value_and_up _ hh ho (Or.inl bc) vb.1 vc.1 (qval _ rb) (qval _ rc))))
    · exact (badQ (value_and_up _ ha ao wz hw hz
        (orStep_up (n := n) (by simp) rw (value_and_up _ hh ho (Or.inl bc) vb.1 vc.1 (qval _ rb) (qval _ rc))) (qval _ rz))).elim
  rcases operand_trace (C := C) p q u uval.2 with ⟨t,ht,rt⟩ | ⟨h,hh,hn,rh,vh⟩
  · rcases operand_trace (C := C) p q v vval.2 with ⟨s,hs,rs⟩ | ⟨h,hh,hn,rh,vh⟩
    · apply finish
      rcases ht with rfl | rfl <;> rcases hs with rfl | rfl
      · exact (badP (value_and_up _ ha ao (Or.inl uv) uval.1 vval.1 (pval _ rt) (pval _ rs))).elim
      · exact Or.inl (trace_and_up hl ha ao (Or.inr uv) (qdiff _ rs) (pval _ rt))
      · exact Or.inl (trace_and_up hl ha ao (Or.inl uv) (qdiff _ rt) (pval _ rs))
      · exact (badQ (value_and_up _ ha ao (Or.inl uv) uval.1 vval.1 (qval _ rt) (qval _ rs))).elim
    · obtain ⟨hj,ho,_⟩ := dirty_of a ha ao v vm vval.1 h hh hn rh
      exact finish (chain v u h (Or.inr uv) vval.1 uval.1 hh ho hj rh vh t ht rt)
  · obtain ⟨hj,ho,hnotbelow⟩ := dirty_of a ha ao u um uval.1 h hh hn rh
    rcases operand_trace (C := C) p q v vval.2 with ⟨s,hs,rs⟩ | ⟨k,hk,kn,rk,vk⟩
    · exact finish (chain u v h (Or.inl uv) uval.1 vval.1 hh ho hj rh vh s hs rs)
    · obtain ⟨kj,_,_⟩ := dirty_of a ha ao v vm vval.1 k hk kn rk
      have eq := uniq k kj vk h hj vh
      subst k
      exfalso
      apply hnotbelow
      intro x hx
      apply below x
      exact value_and_up x ha ao (Or.inl uv) uval.1 vval.1
        (orStep_up (n := n) (by simp) rh hx) (orStep_up (n := n) (by simp) rk hx)


lemma topform_one_junk_trace {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (model : IsAO2 n C) (top : PEqualNP.TopForm.TopForm G C)
    (small : (junk G C).card ≤ 1)
    (spec : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = graphFun G ∅ x)
    (p q : Fin n) (edge : G.Adj p q) (dl dp : ℕ → Bool)
    (hl : TraceCondition C q (val C (List.ofFn (pairInput p p))) dl)
    (hp : TraceCondition C p (val C (List.ofFn (pairInput q q))) dp) :
    dl C.output = true ∨ dp C.output = true := by
  apply topform_one_active_junk_trace G C model top spec p q edge dl dp _ hl hp
  exact le_trans (Finset.card_filter_le _ _) small

end OneJunk

lemma rectangle_meet_full_point {α β : Type*} [DecidableEq α] [DecidableEq β]
    (R : α → β → Prop) (X₁ X₂ : Finset α) (Y₁ Y₂ : Finset β)
    (clean : ∀ (f : α → Bool) (g : β → Bool),
      (∃ x ∈ X₁, f x = true) → (∃ y ∈ Y₁, g y = true) →
      (∃ x ∈ X₂, f x = true) → (∃ y ∈ Y₂, g y = true) →
      ∃ x y, R x y ∧ f x = true ∧ g y = true)
    (p : α) (hp₁ : p ∈ X₁) (hp₂ : p ∈ X₂) :
    (∀ y ∈ Y₁, R p y) ∨ (∀ y ∈ Y₂, R p y) := by
  classical
  by_cases h₁ : ∀ y ∈ Y₁, R p y
  · exact Or.inl h₁
  right
  by_contra h₂
  push_neg at h₁ h₂
  obtain ⟨l,hl,hnl⟩ := h₁
  obtain ⟨m,hm,hnm⟩ := h₂
  obtain ⟨x,y,hxy,hx,hy⟩ := clean (fun x => decide (x = p))
    (fun y => decide (y = l ∨ y = m)) ⟨p,hp₁,by simp⟩ ⟨l,hl,by simp⟩
    ⟨p,hp₂,by simp⟩ ⟨m,hm,by simp⟩
  simp only [decide_eq_true_eq] at hx hy
  subst x
  rcases hy with rfl | rfl
  · exact hnl hxy
  · exact hnm hxy

lemma rectangle_meet_full_line {α β : Type*} [DecidableEq α] [DecidableEq β]
    (R : α → β → Prop) (X₁ X₂ : Finset α) (Y₁ Y₂ : Finset β)
    (clean : ∀ (f : α → Bool) (g : β → Bool),
      (∃ x ∈ X₁, f x = true) → (∃ y ∈ Y₁, g y = true) →
      (∃ x ∈ X₂, f x = true) → (∃ y ∈ Y₂, g y = true) →
      ∃ x y, R x y ∧ f x = true ∧ g y = true)
    (l : β) (hl₁ : l ∈ Y₁) (hl₂ : l ∈ Y₂) :
    (∀ x ∈ X₁, R x l) ∨ (∀ x ∈ X₂, R x l) := by
  apply rectangle_meet_full_point (fun y x => R x y) Y₁ Y₂ X₁ X₂ _ l hl₁ hl₂
  intro g f hy₁ hx₁ hy₂ hx₂
  obtain ⟨x,y,hxy,hx,hy⟩ := clean f g hx₁ hy₁ hx₂ hy₂
  exact ⟨y,x,hxy,hy,hx⟩

lemma rectangle_meet_global_centers {α β : Type*} [DecidableEq α] [DecidableEq β]
    (R : α → β → Prop) [DecidableRel R]
    (noRect : ∀ p q l m, p ≠ q → l ≠ m → R p l → R p m → R q l → ¬ R q m)
    (X₁ X₂ : Finset α) (Y₁ Y₂ : Finset β)
    (hx₁ : 2 ≤ X₁.card) (hx₂ : 2 ≤ X₂.card)
    (hy₁ : 2 ≤ Y₁.card) (hy₂ : 2 ≤ Y₂.card)
    (clean : ∀ (f : α → Bool) (g : β → Bool),
      (∃ x ∈ X₁, f x = true) → (∃ y ∈ Y₁, g y = true) →
      (∃ x ∈ X₂, f x = true) → (∃ y ∈ Y₂, g y = true) →
      ∃ x y, R x y ∧ f x = true ∧ g y = true) :
    let P := X₁.filter (fun p => ∀ l ∈ Y₁, R p l) ∪
      X₂.filter (fun p => ∀ l ∈ Y₂, R p l)
    let L := Y₁.filter (fun l => ∀ p ∈ X₁, R p l) ∪
      Y₂.filter (fun l => ∀ p ∈ X₂, R p l)
    P.card ≤ 2 ∧ L.card ≤ 2 ∧
      X₁ ∩ X₂ ⊆ P ∧ Y₁ ∩ Y₂ ⊆ L := by
  dsimp only
  refine ⟨?_,?_,?_,?_⟩
  · have h := Finset.card_union_le
      (X₁.filter (fun p => ∀ l ∈ Y₁, R p l))
      (X₂.filter (fun p => ∀ l ∈ Y₂, R p l))
    have h₁ := rectangle_full_points_card R noRect X₁ Y₁ hy₁
    have h₂ := rectangle_full_points_card R noRect X₂ Y₂ hy₂
    omega
  · have h := Finset.card_union_le
      (Y₁.filter (fun l => ∀ p ∈ X₁, R p l))
      (Y₂.filter (fun l => ∀ p ∈ X₂, R p l))
    have h₁ := rectangle_full_lines_card R noRect X₁ Y₁ hx₁
    have h₂ := rectangle_full_lines_card R noRect X₂ Y₂ hx₂
    omega
  · intro p hp
    obtain ⟨hp₁,hp₂⟩ := Finset.mem_inter.mp hp
    rcases rectangle_meet_full_point R X₁ X₂ Y₁ Y₂ clean p hp₁ hp₂ with h | h
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hp₁,h⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hp₂,h⟩))
  · intro l hl
    obtain ⟨hl₁,hl₂⟩ := Finset.mem_inter.mp hl
    rcases rectangle_meet_full_line R X₁ X₂ Y₁ Y₂ clean l hl₁ hl₂ with h | h
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hl₁,h⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hl₂,h⟩))


namespace RectangleCNF

def edge (E : Fin 512) (p q : Fin 3) : Prop := E.val.testBit (3*p.val+q.val) = true

def diagonal (E : Fin 512) : Prop := ∀ i : Fin 3, edge E i i

def noFour (E : Fin 512) : Prop :=
  ∀ p q l m : Fin 3, p ≠ q → l ≠ m → ¬ (edge E p l ∧ edge E p m ∧ edge E q l ∧ edge E q m)

def independent (E : Fin 512) (S : Fin 64) : Prop :=
  ∀ p q : Fin 3, edge E p q → ¬ (S.val.testBit p.val = true ∧ S.val.testBit (3+q.val) = true)

def conflict (S T : Fin 64) : Prop :=
  ∃ i : Fin 3, (S.val.testBit i.val || T.val.testBit i.val) = true ∧
    (S.val.testBit (3+i.val) || T.val.testBit (3+i.val)) = true

def cert (E : Fin 512) : Fin 5 → Fin 64 :=
  if E.val &&& 279 = E.val then ![1,14,28,42,56] else
  if E.val &&& 309 = E.val then ![3,10,17,28,56] else
  if E.val &&& 313 = E.val then ![2,21,28,49,56] else
  if E.val &&& 345 = E.val then ![6,20,34,49,56] else
  if E.val &&& 371 = E.val then ![7,10,20,33,56] else
  if E.val &&& 403 = E.val then ![5,12,33,42,56] else
  if E.val &&& 413 = E.val then ![7,12,17,34,56] else
  ![4,35,42,49,56]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma cert_correct : ∀ E : Fin 512, diagonal E → noFour E →
    (∀ i : Fin 5, independent E (cert E i)) ∧
      (∀ i j : Fin 5, i ≠ j → conflict (cert E i) (cert E j)) := by
  unfold diagonal noFour independent conflict edge
  decide


def accepts (A : Finset (Fin 6)) (S : Fin 64) : Prop :=
  ∃ v ∈ A, S.val.testBit v.val = true

lemma no_four_clauses (E : Fin 512) (hd : diagonal E) (h4 : noFour E)
    (A : Fin 4 → Finset (Fin 6))
    (hits : ∀ c : Fin 4, ∀ i : Fin 3,
      Fin.castAdd 3 i ∈ A c ∨ Fin.natAdd 3 i ∈ A c)
    (clean : ∀ S : Fin 64, (∀ c : Fin 4, accepts (A c) S) →
      ∃ p q : Fin 3, edge E p q ∧ S.val.testBit p.val = true ∧
        S.val.testBit (3+q.val) = true) : False := by
  classical
  obtain ⟨ind,conf⟩ := cert_correct E hd h4
  have miss : ∀ i : Fin 5, ∃ c : Fin 4, ¬ accepts (A c) (cert E i) := by
    intro i
    by_contra h
    push Not at h
    obtain ⟨p,q,hpq,hp,hq⟩ := clean (cert E i) h
    exact ind i p q hpq ⟨hp,hq⟩
  choose f hf using miss
  have inj : Function.Injective f := by
    intro i j heq
    by_contra hne
    obtain ⟨k,hp,hq⟩ := conf i j hne
    simp only [Bool.or_eq_true] at hp hq
    rcases hits (f i) k with h | h
    · rcases hp with hbit | hbit
      · exact hf i ⟨Fin.castAdd 3 k,h,hbit⟩
      · exact hf j ⟨Fin.castAdd 3 k,heq ▸ h,hbit⟩
    · rcases hq with hbit | hbit
      · exact hf i ⟨Fin.natAdd 3 k,h,hbit⟩
      · exact hf j ⟨Fin.natAdd 3 k,heq ▸ h,hbit⟩
  have card := Fintype.card_le_of_injective f inj
  simp only [Fintype.card_fin] at card
  omega

end RectangleCNF

end PEqualNP.Outside.L_meta_2602_aux
