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


def bits (R : Fin 3 → Fin 3 → Bool) : BitVec 9 :=
  BitVec.ofBool (R 2 2) ++ BitVec.ofBool (R 2 1) ++ BitVec.ofBool (R 2 0) ++
  BitVec.ofBool (R 1 2) ++ BitVec.ofBool (R 1 1) ++ BitVec.ofBool (R 1 0) ++
  BitVec.ofBool (R 0 2) ++ BitVec.ofBool (R 0 1) ++ BitVec.ofBool (R 0 0)

def encode (R : Fin 3 → Fin 3 → Bool) : Fin 512 := (bits R).toFin

lemma edge_encode (R : Fin 3 → Fin 3 → Bool) (p q : Fin 3) :
    edge (encode R) p q ↔ R p q = true := by
  change (bits R).toNat.testBit (3*p.val+q.val) = true ↔ R p q = true
  rw [BitVec.testBit_toNat]
  fin_cases p <;> fin_cases q <;>
    norm_num only [bits,BitVec.getLsbD_append,BitVec.getLsbD_ofBool] <;> simp

lemma no_matching_three {α β : Type*} [DecidableEq α] [DecidableEq β]
    (R : α → β → Prop) [DecidableRel R]
    (noRect : ∀ p q l m, p ≠ q → l ≠ m → R p l → R p m → R q l → ¬ R q m)
    (P : Fin 3 → α) (Q : Fin 3 → β) (hP : Function.Injective P) (hQ : Function.Injective Q)
    (matching : ∀ i : Fin 3, R (P i) (Q i))
    (C : Fin 4 → Finset (α ⊕ β))
    (hits : ∀ c : Fin 4, ∀ i : Fin 3, Sum.inl (P i) ∈ C c ∨ Sum.inr (Q i) ∈ C c)
    (clean : ∀ (f : α → Bool) (g : β → Bool),
      (∀ c : Fin 4, ∃ v ∈ C c, Sum.elim f g v = true) →
      ∃ p q, R p q ∧ f p = true ∧ g q = true) : False := by
  classical
  let E := encode (fun i j => decide (R (P i) (Q j)))
  have he : ∀ i j : Fin 3, edge E i j ↔ R (P i) (Q j) := by
    intro i j
    simpa [E] using edge_encode (fun i j => decide (R (P i) (Q j))) i j
  have hd : diagonal E := fun i => (he i i).mpr (matching i)
  have h4 : noFour E := by
    intro i j k l hij hkl ⟨h1,h2,h3,h4⟩
    exact noRect (P i) (P j) (Q k) (Q l) (fun h => hij (hP h))
      (fun h => hkl (hQ h)) ((he i k).mp h1) ((he i l).mp h2)
      ((he j k).mp h3) ((he j l).mp h4)
  let vertex : Fin 6 → α ⊕ β := fun v => Fin.addCases (motive := fun _ => α ⊕ β)
    (fun i => Sum.inl (P i)) (fun j => Sum.inr (Q j)) v
  let A : Fin 4 → Finset (Fin 6) := fun c => Finset.univ.filter (fun v => vertex v ∈ C c)
  have ha : ∀ c : Fin 4, ∀ i : Fin 3, Fin.castAdd 3 i ∈ A c ∨ Fin.natAdd 3 i ∈ A c := by
    intro c i
    simpa only [A,Finset.mem_filter,Finset.mem_univ,true_and,vertex,
      Fin.addCases_left,Fin.addCases_right] using hits c i
  apply no_four_clauses E hd h4 A ha
  intro S hs
  let f : α → Bool := fun p => decide (∃ i : Fin 3, P i = p ∧ S.val.testBit i.val = true)
  let g : β → Bool := fun q => decide (∃ i : Fin 3, Q i = q ∧ S.val.testBit (3+i.val) = true)
  have split (v : Fin 6) : (∃ i : Fin 3, v = Fin.castAdd 3 i) ∨
      (∃ j : Fin 3, v = Fin.natAdd 3 j) := by
    by_cases h : v.val < 3
    · exact Or.inl ⟨⟨v.val,h⟩,rfl⟩
    · refine Or.inr ⟨⟨v.val-3,by omega⟩,?_⟩
      apply Fin.ext
      dsimp
      omega
  have pass : ∀ c : Fin 4, ∃ v ∈ C c, Sum.elim f g v = true := by
    intro c
    obtain ⟨v,hv,hbit⟩ := hs c
    have hv' := (Finset.mem_filter.mp hv).2
    rcases split v with ⟨i,rfl⟩ | ⟨j,rfl⟩
    · refine ⟨Sum.inl (P i),by simpa only [vertex,Fin.addCases_left,Fin.addCases_right] using hv',?_⟩
      change decide (∃ j : Fin 3, P j = P i ∧ S.val.testBit j.val = true) = true
      exact decide_eq_true ⟨i,rfl,hbit⟩
    · refine ⟨Sum.inr (Q j),by simpa only [vertex,Fin.addCases_left,Fin.addCases_right] using hv',?_⟩
      change decide (∃ i : Fin 3, Q i = Q j ∧ S.val.testBit (3+i.val) = true) = true
      exact decide_eq_true ⟨j,rfl,hbit⟩
  obtain ⟨p,q,hpq,hp,hq⟩ := clean f g pass
  have hp' : ∃ i : Fin 3, P i = p ∧ S.val.testBit i.val = true := of_decide_eq_true hp
  have hq' : ∃ i : Fin 3, Q i = q ∧ S.val.testBit (3+i.val) = true := of_decide_eq_true hq
  obtain ⟨i,rfl,hi⟩ := hp'
  obtain ⟨j,rfl,hj⟩ := hq'
  exact ⟨i,j,(he i j).mpr hpq,hi,hj⟩


lemma no_two_filtered_edges_away_from_pair {α β : Type*} [DecidableEq α] [DecidableEq β]
    (R : α → β → Prop) [DecidableRel R]
    (noRect : ∀ p q l m, p ≠ q → l ≠ m → R p l → R p m → R q l → ¬ R q m)
    (P : Fin 3 → α) (Q : Fin 3 → β) (hP : Function.Injective P) (hQ : Function.Injective Q)
    (matching : ∀ i : Fin 3, R (P i) (Q i))
    (S T : Finset (α ⊕ β))
    (hitS : ∀ i : Fin 3, Sum.inl (P i) ∈ S ∨ Sum.inr (Q i) ∈ S)
    (hitT : ∀ i : Fin 3, Sum.inl (P i) ∈ T ∨ Sum.inr (Q i) ∈ T)
    (w₁ w₂ : α ⊕ β)
    (hw₁ : w₁ = Sum.inl (P 1) ∨ w₁ = Sum.inr (Q 1))
    (hw₂ : w₂ = Sum.inl (P 2) ∨ w₂ = Sum.inr (Q 2))
    (clean : ∀ (f : α → Bool) (g : β → Bool),
      (∃ v ∈ S, Sum.elim f g v = true) → (∃ v ∈ T, Sum.elim f g v = true) →
      (Sum.elim f g w₁ = true ∨ Sum.elim f g w₂ = true) →
      ∃ p q, R p q ∧ f p = true ∧ g q = true) : False := by
  classical
  let C : Fin 4 → Finset (α ⊕ β) :=
    ![S,T,{Sum.inl (P 0),w₁,w₂},{Sum.inr (Q 0),w₁,w₂}]
  have hits : ∀ c : Fin 4, ∀ i : Fin 3,
      Sum.inl (P i) ∈ C c ∨ Sum.inr (Q i) ∈ C c := by
    intro c i
    fin_cases c
    · exact hitS i
    · exact hitT i
    · fin_cases i
      · exact Or.inl (by simp [C])
      · rcases hw₁ with h | h
        · exact Or.inl (by simp [C,h])
        · exact Or.inr (by simp [C,h])
      · rcases hw₂ with h | h
        · exact Or.inl (by simp [C,h])
        · exact Or.inr (by simp [C,h])
    · fin_cases i
      · exact Or.inr (by simp [C])
      · rcases hw₁ with h | h
        · exact Or.inl (by simp [C,h])
        · exact Or.inr (by simp [C,h])
      · rcases hw₂ with h | h
        · exact Or.inl (by simp [C,h])
        · exact Or.inr (by simp [C,h])
  apply no_matching_three R noRect P Q hP hQ matching C hits
  intro f g pass
  have hs : ∃ v ∈ S, Sum.elim f g v = true := pass 0
  have ht : ∃ v ∈ T, Sum.elim f g v = true := pass 1
  have triple (a b c : α ⊕ β)
      (h : ∃ v ∈ ({a,b,c} : Finset (α ⊕ β)), Sum.elim f g v = true) :
      Sum.elim f g a = true ∨ Sum.elim f g b = true ∨ Sum.elim f g c = true := by
    obtain ⟨v,hv,hbit⟩ := h
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact Or.inl hbit
    · exact Or.inr (Or.inl hbit)
    · exact Or.inr (Or.inr hbit)
  have hp := triple (Sum.inl (P 0)) w₁ w₂ (pass 2)
  have hq := triple (Sum.inr (Q 0)) w₁ w₂ (pass 3)
  rcases hp with hp | h₁ | h₂
  · rcases hq with hq | h₁ | h₂
    · exact ⟨P 0,Q 0,matching 0,hp,hq⟩
    · exact clean f g hs ht (Or.inl h₁)
    · exact clean f g hs ht (Or.inr h₂)
  · exact clean f g hs ht (Or.inl h₁)
  · exact clean f g hs ht (Or.inr h₂)


lemma no_matching_implies_star {α β : Type*} (H : α → β → Prop)
    (noTwo : ∀ p q l m, p ≠ q → l ≠ m → H p l → H q m → False) :
    (∀ p l, ¬ H p l) ∨ (∃ p, ∀ q l, H q l → q = p) ∨
      (∃ l, ∀ p m, H p m → m = l) := by
  classical
  by_cases h : ∃ p l, H p l
  · obtain ⟨p,l,hpl⟩ := h
    by_cases all : ∀ q m, H q m → q = p
    · exact Or.inr (Or.inl ⟨p,all⟩)
    · push Not at all
      obtain ⟨q,m,hqm,hqp⟩ := all
      have hml : m = l := by
        by_contra hm
        exact noTwo q p m l hqp hm hqm hpl
      subst m
      right; right
      refine ⟨l,?_⟩
      intro a b hab
      by_contra hbl
      have hap : a = p := by
        by_contra hap
        exact noTwo a p b l hap hbl hab hpl
      subst a
      exact noTwo p q b l (Ne.symm hqp) hbl hab hqm
  · left
    intro p l hpl
    exact h ⟨p,l,hpl⟩

def filterClean {α β : Type*} (R : α → β → Prop)
    (S T : Finset (α ⊕ β)) (w : α ⊕ β) : Prop :=
  ∀ (f : α → Bool) (g : β → Bool),
    (∃ v ∈ S, Sum.elim f g v = true) → (∃ v ∈ T, Sum.elim f g v = true) →
    Sum.elim f g w = true → ∃ p q, R p q ∧ f p = true ∧ g q = true

lemma all_clean_filters_one_extra_center {α β : Type*} [DecidableEq α] [DecidableEq β]
    (R : α → β → Prop) [DecidableRel R]
    (noRect : ∀ p q l m, p ≠ q → l ≠ m → R p l → R p m → R q l → ¬ R q m)
    (S T : Finset (α ⊕ β)) (p : α) (q : β) (hpq : R p q)
    (hs : Sum.inl p ∈ S ∨ Sum.inr q ∈ S)
    (ht : Sum.inl p ∈ T ∨ Sum.inr q ∈ T) :
    ∃ center : α ⊕ β, ∀ a b, R a b →
      (Sum.inl a ∈ S ∨ Sum.inr b ∈ S) → (Sum.inl a ∈ T ∨ Sum.inr b ∈ T) →
      (∃ w, (w = Sum.inl a ∨ w = Sum.inr b) ∧ filterClean R S T w) →
      a = p ∨ b = q ∨ center = Sum.inl a ∨ center = Sum.inr b := by
  classical
  let H : α → β → Prop := fun a b => a ≠ p ∧ b ≠ q ∧ R a b ∧
    (Sum.inl a ∈ S ∨ Sum.inr b ∈ S) ∧ (Sum.inl a ∈ T ∨ Sum.inr b ∈ T) ∧
    ∃ w, (w = Sum.inl a ∨ w = Sum.inr b) ∧ filterClean R S T w
  have noTwo : ∀ a c b d, a ≠ c → b ≠ d → H a b → H c d → False := by
    intro a c b d hac hbd hab hcd
    obtain ⟨hap,hbq,hab,has,hat,w₁,hw₁,hc₁⟩ := hab
    obtain ⟨hcp,hdq,hcd,hcs,hct,w₂,hw₂,hc₂⟩ := hcd
    let P : Fin 3 → α := ![p,a,c]
    let Q : Fin 3 → β := ![q,b,d]
    have hP : Function.Injective P := by
      intro i j hij
      fin_cases i <;> fin_cases j
      · rfl
      · exact (hap hij.symm).elim
      · exact (hcp hij.symm).elim
      · exact (hap hij).elim
      · rfl
      · exact (hac hij).elim
      · exact (hcp hij).elim
      · exact (hac hij.symm).elim
      · rfl
    have hQ : Function.Injective Q := by
      intro i j hij
      fin_cases i <;> fin_cases j
      · rfl
      · exact (hbq hij.symm).elim
      · exact (hdq hij.symm).elim
      · exact (hbq hij).elim
      · rfl
      · exact (hbd hij).elim
      · exact (hdq hij).elim
      · exact (hbd hij.symm).elim
      · rfl
    apply no_two_filtered_edges_away_from_pair R noRect P Q hP hQ
      (by intro i; fin_cases i <;> assumption) S T
      (by intro i; fin_cases i <;> assumption)
      (by intro i; fin_cases i <;> assumption) w₁ w₂ hw₁ hw₂
    intro f g hS hT hw
    rcases hw with hw | hw
    · exact hc₁ f g hS hT hw
    · exact hc₂ f g hS hT hw
  rcases no_matching_implies_star H noTwo with empty | ⟨a₀,star⟩ | ⟨b₀,star⟩
  · refine ⟨Sum.inl p,?_⟩
    intro a b hab hS hT hf
    by_cases hpa : a = p
    · exact Or.inl hpa
    by_cases hqb : b = q
    · exact Or.inr (Or.inl hqb)
    exact (empty a b ⟨hpa,hqb,hab,hS,hT,hf⟩).elim
  · refine ⟨Sum.inl a₀,?_⟩
    intro a b hab hS hT hf
    by_cases hpa : a = p
    · exact Or.inl hpa
    by_cases hqb : b = q
    · exact Or.inr (Or.inl hqb)
    exact Or.inr (Or.inr (Or.inl (congrArg Sum.inl (star a b ⟨hpa,hqb,hab,hS,hT,hf⟩).symm)))
  · refine ⟨Sum.inr b₀,?_⟩
    intro a b hab hS hT hf
    by_cases hpa : a = p
    · exact Or.inl hpa
    by_cases hqb : b = q
    · exact Or.inr (Or.inl hqb)
    exact Or.inr (Or.inr (Or.inr (congrArg Sum.inr (star a b ⟨hpa,hqb,hab,hS,hT,hf⟩).symm)))


lemma no_matching_three_augmented {α β : Type*} [DecidableEq α] [DecidableEq β]
    (R : α → β → Prop) [DecidableRel R]
    (noRect : ∀ p q l m, p ≠ q → l ≠ m → R p l → R p m → R q l → ¬ R q m)
    (P : Fin 3 → α) (Q : Fin 3 → β) (hP : Function.Injective P) (hQ : Function.Injective Q)
    (matching : ∀ i : Fin 3, R (P i) (Q i))
    (S T U V W : Finset (α ⊕ β))
    (hitS : ∀ i : Fin 3, Sum.inl (P i) ∈ S ∨ Sum.inr (Q i) ∈ S)
    (hitT : ∀ i : Fin 3, Sum.inl (P i) ∈ T ∨ Sum.inr (Q i) ∈ T)
    (hitU : ∀ i : Fin 3, Sum.inl (P i) ∈ U ∪ W ∨ Sum.inr (Q i) ∈ U ∪ W)
    (hitV : ∀ i : Fin 3, Sum.inl (P i) ∈ V ∪ W ∨ Sum.inr (Q i) ∈ V ∪ W)
    (productClean : ∀ (f : α → Bool) (g : β → Bool),
      (∃ v ∈ S, Sum.elim f g v = true) → (∃ v ∈ T, Sum.elim f g v = true) →
      (∃ v ∈ U, Sum.elim f g v = true) → (∃ v ∈ V, Sum.elim f g v = true) →
      ∃ p q, R p q ∧ f p = true ∧ g q = true)
    (filtersClean : ∀ w ∈ W, filterClean R S T w) : False := by
  classical
  let C : Fin 4 → Finset (α ⊕ β) := ![S,T,U ∪ W,V ∪ W]
  apply no_matching_three R noRect P Q hP hQ matching C
    (by intro c i; fin_cases c; exact hitS i; exact hitT i; exact hitU i; exact hitV i)
  intro f g pass
  have hs : ∃ v ∈ S, Sum.elim f g v = true := pass 0
  have ht : ∃ v ∈ T, Sum.elim f g v = true := pass 1
  by_cases hw : ∃ w ∈ W, Sum.elim f g w = true
  · obtain ⟨w,hw,hval⟩ := hw
    exact filtersClean w hw f g hs ht hval
  · have strip (A : Finset (α ⊕ β))
        (h : ∃ v ∈ A ∪ W, Sum.elim f g v = true) :
        ∃ v ∈ A, Sum.elim f g v = true := by
      obtain ⟨v,hv,hval⟩ := h
      rcases Finset.mem_union.mp hv with ha | hW
      · exact ⟨v,ha,hval⟩
      · exact (hw ⟨v,hW,hval⟩).elim
    exact productClean f g hs ht (strip U (pass 2)) (strip V (pass 3))

lemma product_and_filters_one_extra_center {α β : Type*} [DecidableEq α] [DecidableEq β]
    (R : α → β → Prop) [DecidableRel R]
    (noRect : ∀ p q l m, p ≠ q → l ≠ m → R p l → R p m → R q l → ¬ R q m)
    (S T U V : Finset (α ⊕ β)) (p : α) (q : β) (hpq : R p q)
    (hs : Sum.inl p ∈ S ∨ Sum.inr q ∈ S)
    (ht : Sum.inl p ∈ T ∨ Sum.inr q ∈ T)
    (hu : Sum.inl p ∈ U ∨ Sum.inr q ∈ U)
    (hv : Sum.inl p ∈ V ∨ Sum.inr q ∈ V)
    (productClean : ∀ (f : α → Bool) (g : β → Bool),
      (∃ v ∈ S, Sum.elim f g v = true) → (∃ v ∈ T, Sum.elim f g v = true) →
      (∃ v ∈ U, Sum.elim f g v = true) → (∃ v ∈ V, Sum.elim f g v = true) →
      ∃ p q, R p q ∧ f p = true ∧ g q = true) :
    ∃ center : α ⊕ β, ∀ a b, R a b →
      (Sum.inl a ∈ S ∨ Sum.inr b ∈ S) → (Sum.inl a ∈ T ∨ Sum.inr b ∈ T) →
      (((Sum.inl a ∈ U ∨ Sum.inr b ∈ U) ∧ (Sum.inl a ∈ V ∨ Sum.inr b ∈ V)) ∨
        ∃ w, (w = Sum.inl a ∨ w = Sum.inr b) ∧ filterClean R S T w) →
      a = p ∨ b = q ∨ center = Sum.inl a ∨ center = Sum.inr b := by
  classical
  let H : α → β → Prop := fun a b => a ≠ p ∧ b ≠ q ∧ R a b ∧
    (Sum.inl a ∈ S ∨ Sum.inr b ∈ S) ∧ (Sum.inl a ∈ T ∨ Sum.inr b ∈ T) ∧
    (((Sum.inl a ∈ U ∨ Sum.inr b ∈ U) ∧ (Sum.inl a ∈ V ∨ Sum.inr b ∈ V)) ∨
      ∃ w, (w = Sum.inl a ∨ w = Sum.inr b) ∧ filterClean R S T w)
  have select (a : α) (b : β)
      (h : ((Sum.inl a ∈ U ∨ Sum.inr b ∈ U) ∧ (Sum.inl a ∈ V ∨ Sum.inr b ∈ V)) ∨
        ∃ w, (w = Sum.inl a ∨ w = Sum.inr b) ∧ filterClean R S T w) :
      ∃ W : Finset (α ⊕ β), (∀ w ∈ W, filterClean R S T w) ∧
        (Sum.inl a ∈ U ∪ W ∨ Sum.inr b ∈ U ∪ W) ∧
        (Sum.inl a ∈ V ∪ W ∨ Sum.inr b ∈ V ∪ W) := by
    rcases h with ⟨hU,hV⟩ | ⟨w,hw,hclean⟩
    · exact ⟨∅,by simp,by simpa using hU,by simpa using hV⟩
    · refine ⟨{w},?_,?_,?_⟩
      · intro z hz
        have : z = w := Finset.mem_singleton.mp hz
        subst z
        exact hclean
      · rcases hw with rfl | rfl
        · exact Or.inl (by simp)
        · exact Or.inr (by simp)
      · rcases hw with rfl | rfl
        · exact Or.inl (by simp)
        · exact Or.inr (by simp)
  have hitMono (A B : Finset (α ⊕ β)) (hAB : A ⊆ B) (a : α) (b : β) :
      (Sum.inl a ∈ A ∨ Sum.inr b ∈ A) → (Sum.inl a ∈ B ∨ Sum.inr b ∈ B) :=
    Or.imp (fun h => hAB h) (fun h => hAB h)
  have noTwo : ∀ a c b d, a ≠ c → b ≠ d → H a b → H c d → False := by
    intro a c b d hac hbd hab hcd
    obtain ⟨hap,hbq,hab,has,hat,hfirst⟩ := hab
    obtain ⟨hcp,hdq,hcd,hcs,hct,hsecond⟩ := hcd
    obtain ⟨W₁,hc₁,hu₁,hv₁⟩ := select a b hfirst
    obtain ⟨W₂,hc₂,hu₂,hv₂⟩ := select c d hsecond
    let W := W₁ ∪ W₂
    have sub₁ : W₁ ⊆ W := Finset.subset_union_left
    have sub₂ : W₂ ⊆ W := Finset.subset_union_right
    let P : Fin 3 → α := ![p,a,c]
    let Q : Fin 3 → β := ![q,b,d]
    have hP : Function.Injective P := by
      intro i j hij
      fin_cases i <;> fin_cases j
      · rfl
      · exact (hap hij.symm).elim
      · exact (hcp hij.symm).elim
      · exact (hap hij).elim
      · rfl
      · exact (hac hij).elim
      · exact (hcp hij).elim
      · exact (hac hij.symm).elim
      · rfl
    have hQ : Function.Injective Q := by
      intro i j hij
      fin_cases i <;> fin_cases j
      · rfl
      · exact (hbq hij.symm).elim
      · exact (hdq hij.symm).elim
      · exact (hbq hij).elim
      · rfl
      · exact (hbd hij).elim
      · exact (hdq hij).elim
      · exact (hbd hij.symm).elim
      · rfl
    apply no_matching_three_augmented R noRect P Q hP hQ
      (by intro i; fin_cases i <;> assumption) S T U V W
      (by intro i; fin_cases i <;> assumption)
      (by intro i; fin_cases i <;> assumption) ?_ ?_ productClean ?_
    · intro i
      fin_cases i
      · exact hitMono U (U ∪ W) Finset.subset_union_left p q hu
      · exact hitMono (U ∪ W₁) (U ∪ W)
          (Finset.union_subset_union (Finset.Subset.refl _) sub₁) a b hu₁
      · exact hitMono (U ∪ W₂) (U ∪ W)
          (Finset.union_subset_union (Finset.Subset.refl _) sub₂) c d hu₂
    · intro i
      fin_cases i
      · exact hitMono V (V ∪ W) Finset.subset_union_left p q hv
      · exact hitMono (V ∪ W₁) (V ∪ W)
          (Finset.union_subset_union (Finset.Subset.refl _) sub₁) a b hv₁
      · exact hitMono (V ∪ W₂) (V ∪ W)
          (Finset.union_subset_union (Finset.Subset.refl _) sub₂) c d hv₂
    · intro w hw
      rcases Finset.mem_union.mp hw with h | h
      · exact hc₁ w h
      · exact hc₂ w h
  rcases no_matching_implies_star H noTwo with empty | ⟨a₀,star⟩ | ⟨b₀,star⟩
  · refine ⟨Sum.inl p,?_⟩
    intro a b hab hS hT hf
    by_cases hpa : a = p
    · exact Or.inl hpa
    by_cases hqb : b = q
    · exact Or.inr (Or.inl hqb)
    exact (empty a b ⟨hpa,hqb,hab,hS,hT,hf⟩).elim
  · refine ⟨Sum.inl a₀,?_⟩
    intro a b hab hS hT hf
    by_cases hpa : a = p
    · exact Or.inl hpa
    by_cases hqb : b = q
    · exact Or.inr (Or.inl hqb)
    exact Or.inr (Or.inr (Or.inl (congrArg Sum.inl (star a b ⟨hpa,hqb,hab,hS,hT,hf⟩).symm)))
  · refine ⟨Sum.inr b₀,?_⟩
    intro a b hab hS hT hf
    by_cases hpa : a = p
    · exact Or.inl hpa
    by_cases hqb : b = q
    · exact Or.inr (Or.inl hqb)
    exact Or.inr (Or.inr (Or.inr (congrArg Sum.inr (star a b ⟨hpa,hqb,hab,hS,hT,hf⟩).symm)))


lemma two_rectangles_four_center_cover {α β : Type*} [DecidableEq α] [DecidableEq β]
    (R : α → β → Prop) [DecidableRel R]
    (noRect : ∀ p q l m, p ≠ q → l ≠ m → R p l → R p m → R q l → ¬ R q m)
    (S T U V : Finset (α ⊕ β)) (p : α) (q : β) (hpq : R p q)
    (hs : Sum.inl p ∈ S ∨ Sum.inr q ∈ S)
    (ht : Sum.inl p ∈ T ∨ Sum.inr q ∈ T)
    (hu : Sum.inl p ∈ U ∨ Sum.inr q ∈ U)
    (hv : Sum.inl p ∈ V ∨ Sum.inr q ∈ V)
    (productClean : ∀ (f : α → Bool) (g : β → Bool),
      (∃ v ∈ S, Sum.elim f g v = true) → (∃ v ∈ T, Sum.elim f g v = true) →
      (∃ v ∈ U, Sum.elim f g v = true) → (∃ v ∈ V, Sum.elim f g v = true) →
      ∃ p q, R p q ∧ f p = true ∧ g q = true) :
    ∃ K : Finset (α ⊕ β), K.card ≤ 4 ∧ Sum.inl p ∈ K ∧ Sum.inr q ∈ K ∧
      ∀ a b, R a b →
        (((Sum.inl a ∈ S ∨ Sum.inr b ∈ S) ∧ (Sum.inl a ∈ T ∨ Sum.inr b ∈ T) ∧
            ∃ w, (w = Sum.inl a ∨ w = Sum.inr b) ∧ filterClean R S T w) ∨
         ((Sum.inl a ∈ U ∨ Sum.inr b ∈ U) ∧ (Sum.inl a ∈ V ∨ Sum.inr b ∈ V) ∧
            ∃ w, (w = Sum.inl a ∨ w = Sum.inr b) ∧ filterClean R U V w) ∨
         ((Sum.inl a ∈ S ∨ Sum.inr b ∈ S) ∧ (Sum.inl a ∈ T ∨ Sum.inr b ∈ T) ∧
            (Sum.inl a ∈ U ∨ Sum.inr b ∈ U) ∧ (Sum.inl a ∈ V ∨ Sum.inr b ∈ V))) →
        Sum.inl a ∈ K ∨ Sum.inr b ∈ K := by
  classical
  obtain ⟨c₁,h₁⟩ := product_and_filters_one_extra_center R noRect S T U V p q hpq hs ht hu hv productClean
  obtain ⟨c₂,h₂⟩ := all_clean_filters_one_extra_center R noRect U V p q hpq hu hv
  let K : Finset (α ⊕ β) := {Sum.inl p,Sum.inr q,c₁,c₂}
  refine ⟨K,?_,by simp [K],by simp [K],?_⟩
  · have h₁ := Finset.card_insert_le (Sum.inl p) ({Sum.inr q,c₁,c₂} : Finset (α ⊕ β))
    have h₂ := Finset.card_insert_le (Sum.inr q) ({c₁,c₂} : Finset (α ⊕ β))
    have h₃ := Finset.card_insert_le c₁ ({c₂} : Finset (α ⊕ β))
    have h₄ : ({c₂} : Finset (α ⊕ β)).card = 1 := Finset.card_singleton c₂
    dsimp [K]
    omega
  · intro a b hab h
    have cover (z : α ⊕ β) (hz : z ∈ K)
        (h : a = p ∨ b = q ∨ z = Sum.inl a ∨ z = Sum.inr b) :
        Sum.inl a ∈ K ∨ Sum.inr b ∈ K := by
      rcases h with h | h | h | h
      · exact Or.inl (by simp [K,h])
      · exact Or.inr (by simp [K,h])
      · exact Or.inl (h ▸ hz)
      · exact Or.inr (h ▸ hz)
    rcases h with ⟨hS,hT,hf⟩ | ⟨hU,hV,hf⟩ | ⟨hS,hT,hU,hV⟩
    · exact cover c₁ (by simp [K]) (h₁ a b hab hS hT (Or.inr hf))
    · exact cover c₂ (by simp [K]) (h₂ a b hab hU hV hf)
    · exact cover c₁ (by simp [K]) (h₁ a b hab hS hT (Or.inl ⟨hU,hV⟩))

end RectangleCNF

namespace PairClean

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover


def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

lemma wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

lemma wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

lemma wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

lemma getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega


lemma wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

lemma gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false) := by
  rw [wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, wf_snoc]
  have := getD_snoc_eq (wf (gates.take k) X)
    (gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false))
  rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
  exact this

def val (gates : List Gate) {n : ℕ} (w : ℕ) (x : Fin n → Bool) : Bool :=
  (wf gates (List.ofFn x)).getD w false

lemma iv_eq (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k ≤ gates.length)
    (i : ℕ) : (wf (gates.take k) (List.ofFn x)).getD i false = true ↔
      i < n + k ∧ val gates i x = true := by
  by_cases hi : i < n + k
  · rw [val, wire_take gates (List.ofFn x) k i (by simpa using hi) hk]
    simp [hi]
  · rw [List.getD_eq_default _ _ (by rw [wf_len, List.length_take, Nat.min_eq_left hk]; simp; omega)]
    simp [hi]

lemma val_and (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.and) :
    val gates (n + k) x = true ↔ ∀ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
  constructor
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).1 (h i hi)
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).2 (h i hi)

lemma val_or (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.or) :
    val gates (n + k) x = true ↔ ∃ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).1 h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).2 h⟩

lemma val_input (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val gates w x = x ⟨w, hw⟩ := by
  rw [val, wf_keep gates _ w (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

lemma val_big (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ)
    (hw : n + gates.length ≤ w) : val gates w x = false := by
  rw [val, List.getD_eq_default _ _ (by rw [wf_len]; simpa using hw)]

lemma val_mono (gates : List Gate) {n : ℕ}
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x x' : Fin n → Bool) (hx : ∀ v, x v = true → x' v = true) :
    ∀ w, val gates w x = true → val gates w x' = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro h
    by_cases hwn : w < n
    · rw [val_input gates _ w hwn] at h ⊢
      exact hx _ h
    · by_cases hbig : n + gates.length ≤ w
      · rw [val_big gates x w hbig] at h
        exact Bool.noConfusion h
      · have hi : w - n < gates.length := by omega
        have he : n + (w - n) = w := by omega
        rw [← he] at h ⊢
        rcases (legal gates[w - n] (List.getElem_mem hi)).1 with ha | ho
        · apply (val_and gates x' (w - n) hi ha).2
          intro j hj
          obtain ⟨hjlt, hjv⟩ := (val_and gates x (w - n) hi ha).1 h j hj
          exact ⟨hjlt, ih j (by omega) hjv⟩
        · obtain ⟨j, hj, hjlt, hv⟩ := (val_or gates x (w - n) hi ho).1 h
          exact (val_or gates x' (w - n) hi ho).2 ⟨j, hj, hjlt, ih j (by omega) hv⟩

def adjb (s t : Fin 26) : Bool :=
  decide (s.val < 13 ∧ 13 ≤ t.val ∧ (s.val + 26 - t.val) % 13 ∈ [0, 1, 3, 9]) ||
  decide (t.val < 13 ∧ 13 ≤ s.val ∧ (t.val + 26 - s.val) % 13 ∈ [0, 1, 3, 9])

def pr (s t : Fin 26) : Fin 26 → Bool := fun u => decide (u = s ∨ u = t)

def N (v : Fin 26) : Finset (Fin 26) := Finset.univ.filter (fun y => adjb v y = true)

lemma mem_N (v y : Fin 26) : y ∈ N v ↔ adjb v y = true := by
  simp [N]

lemma adj_irr : ∀ s : Fin 26, adjb s s = false := by decide +kernel

lemma adj_symm : ∀ s t : Fin 26, adjb s t = adjb t s := by decide +kernel

lemma hLN : ∀ i j : Fin 26, i ≠ j → (N i ∩ N j).card ≤ 1 := by decide +kernel

lemma degN : ∀ v : Fin 26, (N v).card = 4 := by decide +kernel

lemma adj_total :
    ∑ v : Fin 26, ∑ y : Fin 26, (if adjb v y = true then (1 : ℕ) else 0) = 104 := by
  decide +kernel

lemma k22 (s1 s2 t1 t2 : Fin 26) (h11 : adjb s1 t1 = true) (h12 : adjb s1 t2 = true)
    (h21 : adjb s2 t1 = true) (h22 : adjb s2 t2 = true) (hne : s1 ≠ s2) : t1 = t2 := by
  have hc := hLN s1 s2 hne
  rw [Finset.card_le_one] at hc
  exact hc t1 (Finset.mem_inter.2 ⟨(mem_N _ _).2 h11, (mem_N _ _).2 h21⟩) t2
    (Finset.mem_inter.2 ⟨(mem_N _ _).2 h12, (mem_N _ _).2 h22⟩)


lemma cost (B : Finset (Finset (Fin 26))) (T : Finset (Finset (Fin 26)))
    (hT : ∀ X ∈ T, X.card ≤ 1 ∨ X ∈ B)
    (hB : ∀ X ∈ B, ∃ U V : Finset (Fin 26), X = U ∪ V ∧ U.card < X.card ∧ V.card < X.card ∧
      (U.card ≤ 1 ∨ U ∈ B) ∧ (V.card ≤ 1 ∨ V ∈ B)) :
    (T.biUnion id).card ≤ T.card + B.card := by
  classical
  induction B using Finset.strongInductionOn generalizing T with
  | _ B ih =>
    by_cases h : B.Nonempty
    · obtain ⟨X,hX,hmax⟩ := Finset.exists_max_image B Finset.card h
      obtain ⟨U,V,he,hu,hv,hU,hV⟩ := hB X hX
      have carry (Y : Finset (Fin 26)) (hn : Y ≠ X) (hy : Y.card ≤ 1 ∨ Y ∈ B) :
          Y.card ≤ 1 ∨ Y ∈ B.erase X :=
        hy.imp_right (fun hh => Finset.mem_erase.mpr ⟨hn,hh⟩)
      have split' : ∀ Y ∈ B.erase X, ∃ U V : Finset (Fin 26), Y = U ∪ V ∧ U.card < Y.card ∧
          V.card < Y.card ∧ (U.card ≤ 1 ∨ U ∈ B.erase X) ∧ (V.card ≤ 1 ∨ V ∈ B.erase X) := by
        intro Y hy
        have hY := Finset.mem_of_mem_erase hy
        obtain ⟨u,v,e,hu',hv',a,b⟩ := hB Y hY
        have hm := hmax Y hY
        exact ⟨u,v,e,hu',hv',carry u (fun eq => by rw [eq] at hu'; omega) a,
          carry v (fun eq => by rw [eq] at hv'; omega) b⟩
      have dec := Finset.erase_ssubset hX
      have hc := Finset.card_erase_add_one hX
      by_cases inT : X ∈ T
      · let D := insert U (insert V (T.erase X))
        have result :=  ih (B.erase X) dec D (by
          intro Y hY
          change Y ∈ insert U (insert V (T.erase X)) at hY
          simp only [Finset.mem_insert,Finset.mem_erase] at hY
          rcases hY with rfl | rfl | ⟨hn,hm⟩
          · exact carry _ (fun eq => by rw [eq] at hu; omega) hU
          · exact carry _ (fun eq => by rw [eq] at hv; omega) hV
          · exact carry _ hn (hT _ hm)) split'
        have sub : T.biUnion id ⊆ D.biUnion id := by
          intro y hy
          obtain ⟨Z,hZ,hyZ⟩ := Finset.mem_biUnion.mp hy
          by_cases e : Z = X
          · change y ∈ Z at hyZ
            rw [e,he,Finset.mem_union] at hyZ
            rcases hyZ with z | z
            · exact Finset.mem_biUnion.mpr ⟨U,by simp [D],z⟩
            · exact Finset.mem_biUnion.mpr ⟨V,by simp [D],z⟩
          · exact Finset.mem_biUnion.mpr ⟨Z,by simp [D,e,hZ],hyZ⟩
        have c := Finset.card_le_card sub
        have c1 := Finset.card_insert_le U (insert V (T.erase X))
        have c2 := Finset.card_insert_le V (T.erase X)
        have c3 := Finset.card_erase_add_one inT
        dsimp [D] at result c
        omega
      · have result :=  ih (B.erase X) dec T (fun Y hY => carry Y (fun eq => inT (eq ▸ hY)) (hT Y hY)) split'
        omega
    · have B0 := Finset.not_nonempty_iff_eq_empty.mp h
      subst B
      apply Finset.card_biUnion_le.trans
      simpa using (Finset.sum_le_sum (s := T) (g := fun _ => (1 : ℕ)) (fun X hX => by simpa using hT X hX))

abbrev Vtx := Fin 26
abbrev Sup := Finset Vtx

def W {m : ℕ} (j : Fin m) : ℕ := 26+j.val

lemma W_inj {m : ℕ} : Function.Injective (@W m) := by
  intro a b h
  exact Fin.ext (Nat.add_left_cancel h)

def Needed {m : ℕ} (a b : Fin m → ℕ) (o w : ℕ) : Prop :=
  ∀ S : ℕ → Prop, S o → (∀ j : Fin m, S (W j) → S (a j) ∧ S (b j)) → S w

lemma parent {m : ℕ} {a b : Fin m → ℕ} {o w} (h : Needed a b o w) :
    w = o ∨ ∃ j, Needed a b o (W j) ∧ (a j = w ∨ b j = w) := by
  apply h
  · exact .inl rfl
  · intro j hj
    have base : Needed a b o (W j) := by
      rcases hj with eq | ⟨i,hi,eq | eq⟩
      · rw [eq]; exact fun _ h _ => h
      · exact fun S ho hs => eq ▸ (hs i (hi S ho hs)).1
      · exact fun S ho hs => eq ▸ (hs i (hi S ho hs)).2
    exact ⟨.inr ⟨j,base,.inl rfl⟩, .inr ⟨j,base,.inr rfl⟩⟩

lemma children {m : ℕ} {a b : Fin m → ℕ} {o j} (h : Needed a b o (W j)) :
    Needed a b o (a j) ∧ Needed a b o (b j) :=
  ⟨fun S ho hs => (hs j (h S ho hs)).1, fun S ho hs => (hs j (h S ho hs)).2⟩

def fork {m : ℕ} (a b : Fin m → ℕ) (S : ℕ → Sup) (j : Fin m) :=
  (S (a j)).Nonempty ∧ (S (b j)).Nonempty

open Classical in
noncomputable def roots {m : ℕ} (a b : Fin m → ℕ) (S : ℕ → Sup) (o : ℕ) : Finset (Fin m) :=
  Finset.univ.filter fun j => Needed a b o (W j) ∧ S (W j) = ∅ ∧ fork a b S j

open Classical in
noncomputable def merges {m : ℕ} (a b : Fin m → ℕ) (S : ℕ → Sup) : Finset (Fin m) :=
  Finset.univ.filter fun j => S (W j) ≠ ∅ ∧ fork a b S j

open Classical in
noncomputable def darks {m : ℕ} (a b : Fin m → ℕ) (S : ℕ → Sup) (o : ℕ) : Finset (Fin m) :=
  Finset.univ.filter fun j => Needed a b o (W j) ∧ S (W j) = ∅

open Classical in
def pins {m : ℕ} (a b : Fin m → ℕ) (S : ℕ → Sup) (j : Fin m) : Finset ℕ :=
  ({a j,b j} : Finset ℕ).filter fun w => S w = ∅

open Classical in
noncomputable def usedPins {m : ℕ} (a b : Fin m → ℕ) (S : ℕ → Sup) (o : ℕ) (j : Fin m) :=
  if Needed a b o (W j) then pins a b S j else ∅

open Classical in
lemma pc {m : ℕ} (a b : Fin m → ℕ) (S : ℕ → Sup) (o : ℕ) (j : Fin m)
    (step : S (W j) = ∅ ∨ S (W j) = S (a j) ∪ S (b j)) :
    (usedPins a b S o j).card + 2 * (if j ∈ roots a b S o then 1 else 0) +
      (if j ∈ merges a b S then 1 else 0) ≤ 1 + (if j ∈ darks a b S o then 1 else 0) := by
  classical
  have bd := Finset.card_insert_le (a j) ({b j} : Finset ℕ)
  simp only [Finset.card_singleton] at bd
  rcases step with h | h <;>
    by_cases ha : S (a j) = ∅ <;> by_cases hb : S (b j) = ∅ <;>
    by_cases nu : Needed a b o (W j) <;>
    simp [usedPins,pins,roots,merges,darks,fork,h,nu,ha,hb,Finset.filter_insert,
      Finset.filter_singleton,Finset.nonempty_iff_ne_empty,bd]

lemma pairDis {ι α : Type} [Fintype ι] [DecidableEq ι] [DecidableEq α] (P : ι → Finset α)
    (eq : (Finset.univ.biUnion P).card = ∑ j, (P j).card) :
    ∀ j k : ι, j ≠ k → Disjoint (P j) (P k) := by
  classical
  intro j k ne
  let E := (Finset.univ : Finset (ι)).erase j
  have hj : j ∉ E := Finset.notMem_erase _ _
  have de : insert j E = Finset.univ := Finset.insert_erase (Finset.mem_univ _)
  rw [← de, Finset.biUnion_insert, Finset.sum_insert hj] at eq
  have hle := Finset.card_biUnion_le (s := E) (t := P)
  have hcard := Finset.card_union_add_card_inter (P j) (E.biUnion P)
  have hz : (P j ∩ E.biUnion P).card = 0 := by omega
  have dis := Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp hz)
  exact dis.mono_right (Finset.subset_biUnion_of_mem P (Finset.mem_erase.mpr ⟨ne.symm,Finset.mem_univ k⟩))

lemma budget {m : ℕ} (a b : Fin m → ℕ) (S : ℕ → Sup) (o : ℕ)
    (step : ∀ j, S (W j) = ∅ ∨ S (W j) = S (a j) ∪ S (b j)) :
    let U := roots a b S o
    let M := merges a b S
    let D := darks a b S o
    let P := usedPins a b S o
    2*U.card + M.card ≤ m+1 ∧
    (2*U.card + M.card = m+1 →
      (∀ j k : Fin m, j ≠ k → Disjoint (P j) (P k)) ∧
      ∀ j ∈ D, ¬ fork a b S j → (P j).card = 2) := by
  classical
  intro U M D P
  have bound := Finset.sum_le_sum (s := Finset.univ) (fun j _ => pc a b S o j (step j))
  change (∑ j, ((P j).card + 2 * (if j ∈ U then 1 else 0) + (if j ∈ M then 1 else 0))) ≤
    ∑ j, (1 + (if j ∈ D then 1 else 0)) at bound
  simp only [Finset.sum_add_distrib,← Finset.mul_sum] at bound
  simp at bound
  have sub : D.image W ⊆ insert o (Finset.univ.biUnion P) := by
    intro w hw
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨_,nu,h0⟩ := Finset.mem_filter.mp hj
    rcases parent nu with eq | ⟨k,nk,pk⟩
    · exact eq ▸ Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      apply Finset.mem_biUnion.mpr
      refine ⟨k,Finset.mem_univ _,?_⟩
      change W j ∈ usedPins a b S o k
      simp only [usedPins,ite_eq_left nk,pins,Finset.mem_filter,Finset.mem_insert,Finset.mem_singleton]
      exact ⟨pk.imp Eq.symm Eq.symm,h0⟩
  have dsub := Finset.card_le_card sub
  rw [Finset.card_image_of_injective _ W_inj] at dsub
  have ins := Finset.card_insert_le o (Finset.univ.biUnion P)
  have uni := Finset.card_biUnion_le (s := Finset.univ) (t := P)
  refine ⟨by omega,?_⟩
  intro tight
  have eq : (Finset.univ.biUnion P).card = ∑ j, (P j).card := by omega
  refine ⟨pairDis P eq,?_⟩
  intro j hj nf
  have hp := pc a b S o j (step j)
  have notU : j ∉ U := fun h => nf (Finset.mem_filter.mp h).2.2.2
  have notM : j ∉ M := fun h => nf (Finset.mem_filter.mp h).2.2
  have allEq : ∀ k : Fin m,
      (P k).card + 2*(if k ∈ U then 1 else 0) + (if k ∈ M then 1 else 0) =
        1 + (if k ∈ D then 1 else 0) := by
    intro k
    apply (Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (fun k _ => pc a b S o k (step k))).mp ?_ _ (Finset.mem_univ _)
    change (∑ k, ((P k).card + 2 * (if k ∈ U then 1 else 0) + (if k ∈ M then 1 else 0))) =
      ∑ k, (1 + (if k ∈ D then 1 else 0))
    simp only [Finset.sum_add_distrib,← Finset.mul_sum]
    simp
    omega
  simpa [notU,notM,hj] using allEq j

lemma pieceWire {m : ℕ} (a b : Fin m → ℕ) (S : ℕ → Sup)
    (low : ∀ w < 26, (S w).card ≤ 1) (ha : ∀ j, a j < W j) (hb : ∀ j, b j < W j)
    (step : ∀ j, S (W j) = ∅ ∨ S (W j) = S (a j) ∪ S (b j)) :
    ∀ w < 26+m, 2 ≤ (S w).card →
    ∃ j ∈ merges a b S, S (W j) = S w ∧
      S (W j) = S (a j) ∪ S (b j) ∧ (S (a j)).card < (S w).card ∧ (S (b j)).card < (S w).card := by
  classical
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hc
    by_cases hlo : w < 26
    · have := low w hlo
      omega
    let j : Fin m := ⟨w-26,by omega⟩
    have eq : W j = w := by dsimp [W,j]; omega
    have h1 := ha j
    have h2 := hb j
    rw [eq] at h1 h2
    rcases step j with he | he
    · rw [← eq,he] at hc
      simp at hc
    rw [eq] at he
    by_cases xa : S (a j) = S w
    · obtain ⟨k,hk,hk',hku,hka,hkb⟩ := ih _ h1 (by omega) (by rwa [xa])
      exact ⟨k,hk,hk'.trans xa,hku,xa ▸ hka,xa ▸ hkb⟩
    by_cases xb : S (b j) = S w
    · obtain ⟨k,hk,hk',hku,hka,hkb⟩ := ih _ h2 (by omega) (by rwa [xb])
      exact ⟨k,hk,hk'.trans xb,hku,xb ▸ hka,xb ▸ hkb⟩
    have ac := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨he ▸ Finset.subset_union_left,xa⟩)
    have bc := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨he ▸ Finset.subset_union_right,xb⟩)
    refine ⟨j,?_,congrArg S eq,eq ▸ he,ac,bc⟩
    simp only [merges,Finset.mem_filter,Finset.mem_univ,true_and,eq,fork,Finset.nonempty_iff_ne_empty]
    refine ⟨fun e => by simp [e] at hc,fun e => xb (by simpa [e] using he.symm),
      fun e => xa (by simpa [e] using he.symm)⟩

noncomputable def bucket {m : ℕ} (a b : Fin m → ℕ) (S : ℕ → Sup) (v : Vtx) :=
  (merges a b S).filter fun j => 2 ≤ (S (W j)).card ∧ S (W j) ⊆ N v

lemma groupCost {m : ℕ} (a b : Fin m → ℕ) (S : ℕ → Sup)
    (low : ∀ w < 26, (S w).card ≤ 1) (ha : ∀ j, a j < W j) (hb : ∀ j, b j < W j)
    (step : ∀ j, S (W j) = ∅ ∨ S (W j) = S (a j) ∪ S (b j)) (v : Vtx)
    (G : Finset (Fin m)) (leaf : Fin m → ℕ)
    (bd : ∀ j ∈ G, leaf j < 26+m) (sub : ∀ j ∈ G, S (leaf j) ⊆ N v) :
    (G.biUnion (fun j => S (leaf j))).card ≤ G.card + (bucket a b S v).card := by
  classical
  let B := (bucket a b S v).image (fun j => S (W j))
  let T := G.image (fun j => S (leaf j))
  have piece (w : ℕ) (hw : w < 26+m) (hs : S w ⊆ N v) :
      (S w).card ≤ 1 ∨ S w ∈ B := by
    by_cases h : (S w).card ≤ 1
    · exact Or.inl h
    have h2 : 2 ≤ (S w).card := by omega
    obtain ⟨k,hk,eq,_⟩ := pieceWire a b S low ha hb step w hw h2
    exact Or.inr (Finset.mem_image.mpr ⟨k,Finset.mem_filter.mpr ⟨hk,eq ▸ h2,eq ▸ hs⟩,eq⟩)
  have calcH := cost B T (by
    intro X hx
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hx
    exact piece _ (bd _ hj) (sub _ hj)) (by
    intro X hx
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨_,h2,hs⟩ := Finset.mem_filter.mp hj
    have wlt (k : Fin m) : W k < 26 + m := Nat.add_lt_add_left k.isLt _
    obtain ⟨k,hk,eq,he,e1,e2⟩ := pieceWire a b S low ha hb step _ (wlt j) h2
    have hu := eq.symm.trans he
    rw [hu] at hs
    exact ⟨_,_,hu,e1,e2,piece _ ((ha k).trans (wlt k)) (Finset.subset_union_left.trans hs),
      piece _ ((hb k).trans (wlt k)) (Finset.subset_union_right.trans hs)⟩)
  have ct : T.card ≤ G.card := Finset.card_image_le
  have cb : B.card ≤ (bucket a b S v).card := Finset.card_image_le
  have eq : T.biUnion id = G.biUnion (fun j => S (leaf j)) := by
    ext y
    simp [T]
  rw [eq] at calcH
  omega

def tag (x y : Vtx) := (min x y,max x y)

def edges := (Finset.univ : Finset (Vtx × Vtx)).filter fun e => e.1 < e.2 ∧ adjb e.1 e.2 = true

lemma ecard : edges.card = 52 := by decide +kernel

lemma geom : ∀ x y : Vtx, adjb x y = true ↔ tag x y ∈ edges := by decide +kernel

lemma avoid : ∀ x z : Vtx, ∃ y ∈ N x, ∀ a ∈ ({x,y,z} : Sup), ∀ b ∈ ({x,y,z} : Sup),
    adjb a b = true → a = x ∨ b = x := by
  intro x z
  by_cases eq : x = z
  · subst z
    obtain ⟨y,hy⟩ := Finset.card_pos.mp (by rw [degN]; decide : 0 < (N x).card)
    refine ⟨y,hy,?_⟩
    simp only [Finset.mem_insert,Finset.mem_singleton]
    intro a ha b hb h
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> simp_all [adj_irr]
  · have h : ¬ N x ⊆ N z := by
      intro sub
      have hc := hLN x z eq
      rw [Finset.inter_eq_left.mpr sub,degN] at hc
      omega
    obtain ⟨y,hy,hn⟩ := Finset.not_subset.mp h
    have hz : adjb z y = false := by simpa [mem_N] using hn
    have hyz : adjb y z = false := (adj_symm y z).trans hz
    refine ⟨y,hy,?_⟩
    simp only [Finset.mem_insert,Finset.mem_singleton]
    intro a ha b hb h
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> simp_all [adj_irr]

lemma tallyRoots {m : ℕ} (a b : Fin m → ℕ) (S : ℕ → Sup) (o : ℕ) (z : Fin m → Vtx)
    (leaf : Fin m → ℕ) (low : ∀ w < 26, (S w).card ≤ 1) (ha : ∀ j, a j < W j)
    (hb : ∀ j, b j < W j) (step : ∀ j, S (W j) = ∅ ∨ S (W j) = S (a j) ∪ S (b j))
    (bd : ∀ j, leaf j < 26+m) (hsz : m ≤ 64)
    (sub : ∀ j ∈ roots a b S o, S (leaf j) ⊆ N (z j))
    (cover : ∀ e ∈ edges, ∃ j ∈ roots a b S o, ∃ y ∈ S (leaf j), e = tag (z j) y) :
    let U := roots a b S o
    let M := merges a b S
    let E := fun j => (S (leaf j)).image (tag (z j))
    2*U.card+M.card = m+1 ∧ (∀ j ∈ U, S (leaf j) = N (z j)) ∧
      ∀ j ∈ U, ∀ k ∈ U, j ≠ k → Disjoint (E j) (E k) := by
  classical
  intro U M E
  let G := fun v => U.filter (fun j => z j = v)
  let L := fun v => (G v).biUnion (fun j => S (leaf j))
  have costs (v) : (L v).card ≤ (G v).card + (bucket a b S v).card := by
    apply groupCost a b S low ha hb step v (G v) leaf (fun j _ => bd j)
    intro j hj
    obtain ⟨hu,hz⟩ := Finset.mem_filter.mp hj
    exact hz ▸ sub j hu
  have unionE : edges ⊆ Finset.univ.biUnion (fun v => (L v).image (tag v)) := by
    intro e he
    obtain ⟨j,hj,y,hy,rfl⟩ := cover e he
    exact Finset.mem_biUnion.mpr ⟨z j,Finset.mem_univ _,Finset.mem_image.mpr
      ⟨y,Finset.mem_biUnion.mpr ⟨j,Finset.mem_filter.mpr ⟨hj,rfl⟩,hy⟩,rfl⟩⟩
  have c52 : 52 ≤ ∑ v, (L v).card := ecard ▸ (Finset.card_le_card unionE).trans
    (Finset.card_biUnion_le.trans (Finset.sum_le_sum (fun _ _ => Finset.card_image_le)))
  have dis : (↑(Finset.univ : Finset Vtx) : Set Vtx).PairwiseDisjoint (bucket a b S) := by
    intro i _ j _ ne
    rw [Function.onFun,Finset.disjoint_left]
    intro k hi hj
    obtain ⟨_,hc,si⟩ := Finset.mem_filter.mp hi
    have sj := (Finset.mem_filter.mp hj).2.2
    have hcard := Finset.card_le_card (Finset.subset_inter si sj)
    have hsmall := hLN i j ne
    omega
  have cb : (∑ v, (bucket a b S v).card) ≤ M.card := by
    rw [← Finset.card_biUnion dis]
    exact Finset.card_le_card (Finset.biUnion_subset.mpr (fun _ _ => Finset.filter_subset _ _))
  have cg : ∑ v, (G v).card = U.card :=
    (Finset.card_eq_sum_card_fiberwise (fun j (_ : j ∈ U) => Finset.mem_univ (z j))).symm
  have sumc := Finset.sum_le_sum (s := Finset.univ) (fun v _ => costs v)
  rw [Finset.sum_add_distrib,cg] at sumc
  let F := fun j => if j ∈ U then E j else ∅
  have all : edges ⊆ Finset.univ.biUnion F := by
    intro e he
    obtain ⟨j,hj,y,hy,rfl⟩ := cover e he
    change j ∈ U at hj
    exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,by simpa [F,hj,E] using Finset.mem_image_of_mem (tag (z j)) hy⟩
  have mass (j) : (F j).card ≤ (if j ∈ U then 4 else 0) := by
    by_cases hj : j ∈ U
    · simp only [F,ite_eq_left hj,E]
      exact Finset.card_image_le.trans ((Finset.card_le_card (sub j hj)).trans_eq (degN _))
    · simp [F,hj]
  have cm := Finset.sum_le_sum (s := Finset.univ) (fun j _ => mass j)
  have sf : (∑ j : Fin m, (if j ∈ U then 4 else 0 : ℕ)) = U.card*4 := by simp
  rw [sf] at cm
  have cAll := Finset.card_le_card all
  rw [ecard] at cAll
  have cbi := Finset.card_biUnion_le (s := Finset.univ) (t := F)
  have budgetH := (budget a b S o step).1
  change 2*U.card + M.card ≤ m+1 at budgetH
  refine ⟨by omega,?_,?_⟩
  · intro j hj
    have sumEq : (∑ j, (F j).card) = ∑ j : Fin m, (if j ∈ U then 4 else 0 : ℕ) := by rw [sf]; omega
    have eq := (Finset.sum_eq_sum_iff_of_le (fun j _ => mass j)).mp sumEq j (Finset.mem_univ j)
    simp only [F,ite_eq_left hj,E] at eq
    apply Finset.eq_of_subset_of_card_le (sub j hj)
    rw [degN,← eq]
    exact Finset.card_image_le
  · intro j hj k hk ne
    have eq : (Finset.univ.biUnion F).card = ∑ j, (F j).card := by omega
    simpa [F,hj,hk] using pairDis F eq j k ne

def Cross {m : ℕ} (a b : Fin m → ℕ) (S : ℕ → Sup) (j : Fin m) (x y : Vtx) :=
  (x ∈ S (a j) ∧ y ∈ S (b j)) ∨ (y ∈ S (a j) ∧ x ∈ S (b j))

lemma tag_symm (x y : Vtx) : tag x y = tag y x := by simp [tag,min_comm,max_comm]

lemma starChoice {m : ℕ} (a b : Fin m → ℕ) (S : ℕ → Sup) (o : ℕ)
    (sound : ∀ j ∈ roots a b S o, ∀ x ∈ S (a j), ∀ y ∈ S (b j), adjb x y = true) :
    ∃ (z : Fin m → Vtx) (leaf : Fin m → ℕ), (∀ j, leaf j = a j ∨ leaf j = b j) ∧
      ∀ j ∈ roots a b S o, S (leaf j) ⊆ N (z j) ∧ ∀ x y, Cross a b S j x y →
        ∃ t ∈ S (leaf j), tag x y = tag (z j) t := by
  classical
  suffices h : ∀ j : Fin m, ∃ (z : Vtx) (w : ℕ), (w = a j ∨ w = b j) ∧
      (j ∈ roots a b S o → S w ⊆ N z ∧ ∀ x y, Cross a b S j x y →
        ∃ t ∈ S w, tag x y = tag z t) by
    choose z w hw hz using h
    exact ⟨z,w,hw,hz⟩
  intro j
  by_cases hj : j ∈ roots a b S o
  · obtain ⟨_,_,⟨u,hu⟩,v,hv⟩ := (Finset.mem_filter.mp hj).2
    by_cases one : ∀ x ∈ S (a j), x = u
    · refine ⟨u,b j,Or.inr rfl,fun _ => ⟨fun y hy => (mem_N _ _).2 (sound j hj u hu y hy),?_⟩⟩
      intro x y cr
      rcases cr with ⟨h,k⟩ | ⟨h,k⟩
      · exact ⟨y,k,by rw [one x h]⟩
      · exact ⟨x,k,by rw [one y h,tag_symm]⟩
    · push Not at one
      obtain ⟨u',hu',ne⟩ := one
      have only (y) (hy : y ∈ S (b j)) : y = v :=
        k22 u' u y v (sound j hj _ hu' _ hy) (sound j hj _ hu' _ hv)
          (sound j hj _ hu _ hy) (sound j hj _ hu _ hv) ne
      refine ⟨v,a j,Or.inl rfl,fun _ => ⟨fun x hx => (mem_N _ _).2 ((adj_symm v x).trans (sound j hj _ hx _ hv)),?_⟩⟩
      intro x y cr
      rcases cr with ⟨h,k⟩ | ⟨h,k⟩
      · exact ⟨x,h,by rw [only y k,tag_symm]⟩
      · exact ⟨y,h,by rw [only x k]⟩
  · exact ⟨0,a j,Or.inl rfl,fun h => (hj h).elim⟩

def Holds (S : ℕ → Sup) (T : Sup) (w : ℕ) := ∃ t ∈ T, t ∈ S w

def ClosedAt {m : ℕ} (a b : Fin m → ℕ) (A : Fin m → Prop) (o : ℕ) (r : Fin m)
    (H : ℕ → Prop) :=
  ∀ j : Fin m, Needed a b o (W j) → j ≠ r →
    (A j → H (a j) → H (b j) → H (W j)) ∧ (¬ A j → H (a j) ∨ H (b j) → H (W j))

def Force {m : ℕ} (a b : Fin m → ℕ) (A : Fin m → Prop) (o : ℕ) (r : Fin m)
    (p : Vtx) (w : ℕ) :=
  ∀ l ∈ N p, ∀ H : ℕ → Prop, H p.val → H l.val → ClosedAt a b A o r H → H w → H o

lemma route {m : ℕ} (a b : Fin m → ℕ) (S : ℕ → Sup) (A : Fin m → Prop) (o : ℕ)
    (ha : ∀ j, a j < W j) (hb : ∀ j, b j < W j) (neab : ∀ j, a j ≠ b j)
    (inputs : ∀ t : Vtx, t ∈ S t.val)
    (out0 : S o = ∅) (ops : ∀ j, (A j → S (W j) = ∅) ∧ (¬ A j → S (W j) = S (a j) ∪ S (b j)))
    (z : Fin m → Vtx) (leaf : Fin m → ℕ)
    (hs : ∀ j ∈ roots a b S o, S (leaf j) = N (z j))
    (origin : ∀ j ∈ roots a b S o, ∀ x y, Cross a b S j x y →
      adjb x y = true ∧ ∃ t ∈ S (leaf j), tag x y = tag (z j) t)
    (dis : ∀ j ∈ roots a b S o, ∀ k ∈ roots a b S o, j ≠ k →
      Disjoint ((S (leaf j)).image (tag (z j))) ((S (leaf k)).image (tag (z k))))
    (tight : 2*(roots a b S o).card + (merges a b S).card = m+1)
    (r : Fin m) (hr : r ∈ roots a b S o)
    (start : Force a b A o r (z r) (W r)) (D : ℕ → Prop)
    (dr : D (W r)) (dOr : ∀ j, ¬ A j → D (a j) ∨ D (b j) → D (W j)) : D o := by
  classical
  have step (j) : S (W j) = ∅ ∨ S (W j) = S (a j) ∪ S (b j) := by
    by_cases h : A j
    · exact .inl ((ops j).1 h)
    · exact .inr ((ops j).2 h)
  obtain ⟨uniq,two⟩ := (budget a b S o step).2 tight
  let p := z r
  have shield (v : Vtx) : ∃ l ∈ N p, ∃ H : ℕ → Prop, H p.val ∧ H l.val ∧
      ClosedAt a b A o r H ∧ ¬ H o ∧ (∀ w, S w = ∅ → ¬ H w) ∧ ∀ w, v ∈ S w → H w := by
    obtain ⟨l,hl,good⟩ := avoid p v
    let T : Sup := {p,l,v}
    refine ⟨l,hl,Holds S T,⟨p,by simp [T],inputs p⟩,⟨l,by simp [T],inputs l⟩,?_,
      by simp [Holds,out0],fun w h => by simp [Holds,h],fun w h => ⟨v,by simp [T],h⟩⟩
    intro k nk ne
    constructor
    · intro ak ⟨s,hsT,hsa⟩ ⟨t,htT,htb⟩
      have hk : k ∈ roots a b S o := Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,nk,(ops k).1 ak,⟨s,hsa⟩,⟨t,htb⟩⟩
      obtain ⟨adj,y,hy,ey⟩ := origin k hk s t (.inl ⟨hsa,htb⟩)
      have mk : tag s t ∈ (S (leaf k)).image (tag (z k)) :=
        Finset.mem_image.mpr ⟨y,hy,ey.symm⟩
      have mr : tag s t ∈ (S (leaf r)).image (tag (z r)) := by
        rw [hs r hr]
        rcases good s hsT t htT adj with hh | hh
        · exact Finset.mem_image.mpr ⟨t,(mem_N _ _).mpr (by change adjb p t = true; rwa [← hh]),by rw [hh]⟩
        · exact Finset.mem_image.mpr ⟨s,(mem_N _ _).mpr (by change adjb p s = true; rw [← hh]; exact (adj_symm t s).trans adj),
              by rw [hh,tag_symm]⟩
      exact (Finset.disjoint_left.mp (dis k hk r hr ne) mk mr).elim
    · intro no ab
      rw [show Holds S T (W k) ↔ ∃ x ∈ T, x ∈ S (W k) from Iff.rfl,(ops k).2 no]
      rcases ab with ⟨x,hx,h⟩ | ⟨x,hx,h⟩
      · exact ⟨x,hx,Finset.mem_union_left _ h⟩
      · exact ⟨x,hx,Finset.mem_union_right _ h⟩
  have walk : ∀ n w, 26+m-w = n → Needed a b o w → D w → Force a b A o r p w → D o := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro w en nw dw fw
      by_cases eo : w = o
      · exact eo ▸ dw
      have zero : S w = ∅ := by
        by_contra h
        obtain ⟨v,hv⟩ := Finset.nonempty_iff_ne_empty.mpr h
        obtain ⟨l,hl,H,hp,hL,hc,hn,_,lift⟩ := shield v
        exact hn (fw l hl H hp hL hc (lift w hv))
      obtain ⟨k,nk,readW⟩ := (parent nw).resolve_left eo
      have member (g : Fin m) (ng : Needed a b o (W g)) (rg : a g = w ∨ b g = w) :
          w ∈ usedPins a b S o g := by
        simp only [usedPins,ite_eq_left ng,pins,Finset.mem_filter,Finset.mem_insert,Finset.mem_singleton]
        exact ⟨rg.imp Eq.symm Eq.symm,zero⟩
      have only (g : Fin m) (ng : Needed a b o (W g)) (rg : a g = w ∨ b g = w) : g = k := by
        by_contra neq
        exact Finset.disjoint_left.mp (uniq g k neq) (member g ng rg) (member k nk readW)
      have relay (H : ℕ → Prop) (hc : ClosedAt a b A o r H)
          (hk : (A k → (H (a k) ∨ a k = w) → (H (b k) ∨ b k = w) → H (W k)) ∧
            (¬A k → H (a k) ∨ a k = w ∨ H (b k) ∨ b k = w → H (W k))) :
          ClosedAt a b A o r (fun t => H t ∨ t = w) := by
        intro g ng nr
        by_cases e : g = k
        · subst g
          constructor
          · intro op h1 h2
            exact .inl (hk.1 op h1 h2)
          · intro op h
            apply Or.inl
            apply hk.2 op
            tauto
        · have na : a g ≠ w := fun h => e (only g ng (.inl h))
          have nb : b g ≠ w := fun h => e (only g ng (.inr h))
          simp only [na,nb,or_false]
          exact ⟨fun op h1 h2 => .inl ((hc g ng nr).1 op h1 h2),
            fun op h => .inl ((hc g ng nr).2 op h)⟩
      by_cases op : A k
      · have dk : k ∈ darks a b S o := Finset.mem_filter.mpr ⟨Finset.mem_univ _,nk,(ops k).1 op⟩
        have nf : ¬fork a b S k := by
          rcases readW with e | e <;> simp [fork,e,zero]
        have htwo := two k dk nf
        have both : S (a k) = ∅ ∧ S (b k) = ∅ := by
          by_cases za : S (a k) = ∅ <;> by_cases zb : S (b k) = ∅ <;>
            simp_all [usedPins,pins,Finset.filter_insert,Finset.filter_singleton]
        obtain ⟨l,hl,H,hp,hL,hc,hn,off,_⟩ := shield p
        have hk := relay H hc ⟨by
          intro _ h1 h2
          have e1 := h1.resolve_left (off _ both.1)
          have e2 := h2.resolve_left (off _ both.2)
          exact (neab k (e1.trans e2.symm)).elim,fun no => (no op).elim⟩
        have bad := fw l hl _ (Or.inl hp) (Or.inl hL) hk (Or.inr rfl)
        exact (bad.elim hn (fun e => eo e.symm)).elim
      · have fk : Force a b A o r p (W k) := by
          intro l hl H hP hL hc hW
          have h := fw l hl _ (Or.inl hP) (Or.inl hL)
            (relay H hc ⟨fun _ _ _ => hW,fun _ _ => hW⟩) (Or.inr rfl)
          exact h.resolve_right (Ne.symm eo)
        have lt : w < W k := readW.elim (fun e => e ▸ ha k) (fun e => e ▸ hb k)
        have bd : W k < 26+m := Nat.add_lt_add_left k.isLt _
        exact ih _ (by omega : 26+m-W k < n) _ rfl nk
          (dOr k op (by rcases readW with h | h; exact .inl (h.symm ▸ dw); exact .inr (h.symm ▸ dw))) fk
  exact walk _ _ rfl (Finset.mem_filter.mp hr).2.1 dr start

lemma decomp {m w : ℕ} (h : w < 26+m) : w < 26 ∨ ∃ j : Fin m, w = W j := by
  by_cases hw : w < 26
  · exact .inl hw
  · exact .inr ⟨⟨w-26,by omega⟩,by dsimp [W]; omega⟩

set_option maxHeartbeats 2000000 in
lemma assemble {m : ℕ} (a b : Fin m → ℕ) (S : ℕ → Sup) (A : Fin m → Prop) (o : ℕ)
    (ha : ∀ j, a j < W j) (hb : ∀ j, b j < W j) (neab : ∀ j, a j ≠ b j)
    (hsz : m ≤ 64) (hout : o < 26+m)
    (inp : ∀ t : Vtx, S t.val = {t}) (out0 : S o = ∅)
    (ops : ∀ j, (A j → S (W j) = ∅) ∧ (¬ A j → S (W j) = S (a j) ∪ S (b j)))
    (Q : Vtx → Vtx → ℕ → Prop)
    (qIn : ∀ x y t : Vtx, Q x y t.val → t = x ∨ t = y)
    (qOut : ∀ x y, adjb x y = true → Q x y o)
    (qStep : ∀ x y j, Q x y (W j) →
      (A j → Q x y (a j) ∧ Q x y (b j)) ∧ (¬ A j → Q x y (a j) ∨ Q x y (b j)))
    (sound : ∀ j, A j → ∀ x ∈ S (a j), ∀ y ∈ S (b j), adjb x y = true)
    (x y : Vtx) (edge : adjb x y = true) (D : ℕ → Prop) (dy : D y.val)
    (dAnd : ∀ j, A j → ((x ∈ S (a j) ∧ D (b j)) ∨ (D (a j) ∧ x ∈ S (b j))) → D (W j))
    (dOr : ∀ j, ¬ A j → D (a j) ∨ D (b j) → D (W j)) : D o := by
  classical
  let U := roots a b S o
  have rootAnd (j : Fin m) (hj : j ∈ U) : A j := by
    by_contra no
    obtain ⟨_,h0,f⟩ := (Finset.mem_filter.mp hj).2
    rw [(ops j).2 no,Finset.union_eq_empty] at h0
    exact f.1.ne_empty h0.1
  have sov (j : Fin m) (hj : j ∈ U) := sound j (rootAnd j hj)
  obtain ⟨z,leaf,hside,hstar⟩ := starChoice a b S o sov
  have wlt (j : Fin m) : W j < 26+m := Nat.add_lt_add_left j.isLt _
  have seek (s t : Vtx) (h : adjb s t = true) : ∃ j ∈ U, Cross a b S j s t := by
    suffices run : ∀ w < 26+m, Needed a b o w → Q s t w →
        (s ∈ S w ∨ t ∈ S w) ∨ ∃ j ∈ U, Cross a b S j s t by
      simpa [out0] using run o hout (fun _ ho _ => ho) (qOut s t h)
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw nw qw
      rcases decomp hw with lo | ⟨j,rfl⟩
      · let v : Vtx := ⟨w,lo⟩
        have eq : S w = {v} := inp v
        rcases qIn s t v qw with e | e
        · exact .inl (.inl (by rw [eq,Finset.mem_singleton]; exact e.symm))
        · exact .inl (.inr (by rw [eq,Finset.mem_singleton]; exact e.symm))
      obtain ⟨na,nb⟩ := children nw
      by_cases aj : A j
      · obtain ⟨qa,qb⟩ := (qStep s t j qw).1 aj
        rcases ih _ (ha j) ((ha j).trans hw) na qa with hitsA | got
        · rcases ih _ (hb j) ((hb j).trans hw) nb qb with hitsB | got
          · right
            have single (v) (h1 : v ∈ S (a j)) (h2 : v ∈ S (b j)) : False := by
              have e := sound j aj v h1 v h2
              rw [adj_irr] at e
              contradiction
            rcases hitsA with aa | aa <;> rcases hitsB with bb | bb
            · exact (single s aa bb).elim
            · exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,nw,(ops j).1 aj,⟨s,aa⟩,⟨t,bb⟩⟩,.inl ⟨aa,bb⟩⟩
            · exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,nw,(ops j).1 aj,⟨t,aa⟩,⟨s,bb⟩⟩,.inr ⟨aa,bb⟩⟩
            · exact (single t aa bb).elim
          · exact .inr got
        · exact .inr got
      · rcases (qStep s t j qw).2 aj with qa | qb
        · have hh := ih _ (ha j) ((ha j).trans hw) na qa
          rw [(ops j).2 aj]
          simp only [Finset.mem_union]
          tauto
        · have hh := ih _ (hb j) ((hb j).trans hw) nb qb
          rw [(ops j).2 aj]
          simp only [Finset.mem_union]
          tauto
  have st (j) : S (W j) = ∅ ∨ S (W j) = S (a j) ∪ S (b j) := by
    by_cases aj : A j
    · exact .inl ((ops j).1 aj)
    · exact .inr ((ops j).2 aj)
  have low (w : ℕ) (hw : w < 26) : (S w).card ≤ 1 := by
    rw [inp (⟨w,hw⟩ : Vtx)]
    simp
  have bound (j) : leaf j < 26+m := (hside j).elim (fun e => e.symm ▸ (ha j).trans (wlt j))
    (fun e => e.symm ▸ (hb j).trans (wlt j))
  obtain ⟨tight,full,apart⟩ := tallyRoots a b S o z leaf low ha hb st bound hsz
    (fun j hj => (hstar j hj).1) (by
      rintro ⟨s,t⟩ he
      obtain ⟨_,hst,adj⟩ := Finset.mem_filter.mp he
      obtain ⟨j,hj,hcr⟩ := seek s t adj
      obtain ⟨u,hu,eq⟩ := (hstar j hj).2 s t hcr
      exact ⟨j,hj,u,hu,by simpa [tag,min_eq_left hst.le,max_eq_right hst.le] using eq⟩)
  obtain ⟨r,hr,cr⟩ := seek x y edge
  have ys : ∀ w < 26+m, y ∈ S w → D w := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw hy
      rcases decomp hw with lo | ⟨k,rfl⟩
      · have ht : y = (⟨w,lo⟩ : Vtx) := Finset.mem_singleton.mp ((inp ⟨w,lo⟩) ▸ hy)
        have e : y.val = w := congrArg Fin.val ht
        exact e ▸ dy
      by_cases ak : A k
      · simp [(ops k).1 ak] at hy
      · rw [(ops k).2 ak,Finset.mem_union] at hy
        exact dOr k ak (hy.imp (ih _ (ha k) ((ha k).trans hw)) (ih _ (hb k) ((hb k).trans hw)))
  apply route a b S A o ha hb neab (fun t => by rw [inp]; simp) out0 ops z leaf full
      (fun j hj s t hc => ⟨by
        rcases hc with ⟨aa,bb⟩ | ⟨aa,bb⟩
        · exact sov j hj s aa t bb
        · exact (adj_symm s t).trans (sov j hj t aa s bb),(hstar j hj).2 s t hc⟩)
      apart tight r hr ?_ D ?_ dOr
  · intro l hl H hp hl' hc hroot
    suffices hh : ∀ w < 26+m, Needed a b o w → Q (z r) l w → H w from
      hh o hout (fun _ ho _ => ho) (qOut _ _ ((mem_N _ _).mp hl))
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw nw hq
      rcases decomp hw with lo | ⟨j,rfl⟩
      · rcases qIn _ _ ⟨w,lo⟩ hq with eq | eq
        · have e : w = (z r).val := congrArg Fin.val eq
          exact e.symm ▸ hp
        · have e : w = l.val := congrArg Fin.val eq
          exact e.symm ▸ hl'
      by_cases e : j = r
      · exact e.symm ▸ hroot
      obtain ⟨na,nb⟩ := children nw
      have ia := ih _ (ha j) ((ha j).trans hw) na
      have ib := ih _ (hb j) ((hb j).trans hw) nb
      by_cases aj : A j
      · obtain ⟨q1,q2⟩ := (qStep _ _ _ hq).1 aj
        exact (hc j nw e).1 aj (ia q1) (ib q2)
      · exact (hc j nw e).2 aj (((qStep _ _ _ hq).2 aj).imp ia ib)
  · apply dAnd r (rootAnd r hr)
    rcases cr with ⟨aa,bb⟩ | ⟨aa,bb⟩
    · exact .inl ⟨aa,ys _ ((hb r).trans (wlt r)) bb⟩
    · exact .inr ⟨ys _ ((ha r).trans (wlt r)) aa,bb⟩

def Jset : Finset (Fin 13) := {0,1,3,9}

lemma adjSide : ∀ p l : Fin 13, adjb (Fin.castAdd 13 p) (Fin.natAdd 13 l) = true ↔ p-l ∈ Jset := by
  decide +kernel

lemma pairSpec (s t : Vtx) : adjb s t = true ↔ ∃ p l : Fin 13, p-l ∈ Jset ∧
    pr s t (Fin.castAdd 13 p) = true ∧ pr s t (Fin.natAdd 13 l) = true := by
  constructor
  · have hc : ∀ s t : Vtx, adjb s t = true →
        (let p : Fin 13 := ⟨(min s.val t.val)%13,by omega⟩
         let l : Fin 13 := ⟨(max s.val t.val-13)%13,by omega⟩
         p-l ∈ Jset ∧ pr s t (Fin.castAdd 13 p) = true ∧ pr s t (Fin.natAdd 13 l) = true) := by
      decide +kernel
    intro h
    exact ⟨_,_,hc s t h⟩
  · rintro ⟨p,l,edge,hp,hl⟩
    have h := (adjSide p l).2 edge
    have ep : Fin.castAdd 13 p = s ∨ Fin.castAdd 13 p = t := of_decide_eq_true hp
    have el : Fin.natAdd 13 l = s ∨ Fin.natAdd 13 l = t := of_decide_eq_true hl
    have ne : Fin.castAdd 13 p ≠ Fin.natAdd 13 l := by
      intro eq
      have h1 := congrArg Fin.val eq
      change p.val = 13 + l.val at h1
      omega
    rcases ep with eq | eq <;> rcases el with eq' | eq'
    · exact (ne (eq.trans eq'.symm)).elim
    · simpa only [eq,eq'] using h
    · rw [adj_symm]
      simpa only [eq,eq'] using h
    · exact (ne (eq.trans eq'.symm)).elim


def pairClean (C : Circuit) : Prop :=
  ∀ j < C.gates.length,
    (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = .and →
    ∀ s t : Fin 26, adjb s t = false →
      (C.wires (List.ofFn (pr s t))).getD (26 + j) false = false

set_option maxHeartbeats 2000000 in
lemma pair_clean_trace : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.and; have x3 : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.or; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : Fin (13 : ℕ)) (x7 x8 : ℕ → Bool),   have x9 : Fin (26 : ℕ) → ℕ → (ℕ → Bool) → Prop := fun (x9 : Fin (26 : ℕ)) (x10 : ℕ) (x11 : ℕ → Bool) =>     (∀ x12 < (26 : ℕ), x11 x12 = Decidable.decide (x12 = x10)) ∧       have x12 : List Bool := x4.wires (List.ofFn fun (x12 : Fin (26 : ℕ)) => Decidable.decide (x12 = x9));       ∀ (x13 : ℕ) (x14 : PEqualNP.CircuitLowerBounds.Gate) (x15 x16 : ℕ), x4.gates[x13]? = Option.some x14 → x14.inputs = [x15, x16] → (x14.op = x2 → x11 ((26 : ℕ) + x13) = (x12.getD x15 Bool.false && x11 x16 || x11 x15 && x12.getD x16 Bool.false)) ∧ (x14.op = x3 → x11 ((26 : ℕ) + x13) = (x11 x15 || x11 x16));   x4.size ≤ (64 : ℕ) → (∀ (x11 : ℕ) (x12 : PEqualNP.CircuitLowerBounds.Gate), x4.gates[x11]? = Option.some x12 → (x12.op = x2 ∨ x12.op = x3) ∧ ∃ (x14 : ℕ) (x15 : ℕ), x12.inputs = [x14, x15] ∧ x14 ≠ x15 ∧ x14 < (26 : ℕ) + x11 ∧ x15 < (26 : ℕ) + x11) → (∀ (x12 : Fin (26 : ℕ) → Bool), x4.eval (List.ofFn x12) = Bool.true ↔ ∃ (x13 : Fin (13 : ℕ)) (x14 : Fin (13 : ℕ)), x13 - x14 ∈ x1 ∧ x12 (Fin.castAdd (13 : ℕ) x13) = Bool.true ∧ x12 (Fin.natAdd (13 : ℕ) x14) = Bool.true) → pairClean x4 → x5 - x6 ∈ x1 → x9 (Fin.castAdd (13 : ℕ) x5) ((13 : ℕ) + ↑x6) x7 → x9 (Fin.natAdd (13 : ℕ) x6) (↑x5) x8 → x7 x4.output = Bool.true ∨ x8 x4.output = Bool.true := by
  dsimp only
  intro C p l dP dL size gates correct clean incidence traceP traceL
  classical
  let m := C.gates.length
  let g (j : Fin m) := C.gates[j.val]
  have hg (j : Fin m) : C.gates[j.val]? = some (g j) := List.getElem?_eq_getElem j.isLt
  have raw (j : Fin m) := (gates j (g j) (hg j)).2
  choose a b pins ne ha hb using raw
  let A (j : Fin m) := (g j).op = GateOp.and
  have orOp (j : Fin m) (no : ¬ A j) : (g j).op = GateOp.or :=
    ((gates j (g j) (hg j)).1).resolve_left no
  let V (f : Vtx → Bool) w := val C.gates w f = true
  let one (v : Vtx) (u : Vtx) := decide (u=v)
  let S (w : ℕ) : Sup := Finset.univ.filter fun v => V (one v) w
  have mem (w : ℕ) (u : Vtx) : u ∈ S w ↔ V (one u) w := by simp [S]
  have andEv (f : Vtx → Bool) (j : Fin m) (op : A j) :
      V f (W j) ↔ V f (a j) ∧ V f (b j) := by
    have h := val_and C.gates f j.val j.isLt op
    change _ ↔ ∀ k ∈ (g j).inputs, _ at h
    simpa [V,W,pins j,ha j,hb j] using h
  have orEv (f : Vtx → Bool) (j : Fin m) (op : ¬A j) :
      V f (W j) ↔ V f (a j) ∨ V f (b j) := by
    have h := val_or C.gates f j.val j.isLt (orOp j op)
    change _ ↔ ∃ k ∈ (g j).inputs, _ at h
    simpa [V,W,pins j,ha j,hb j] using h
  have same (s t : Vtx) : V (pr s t) C.output ↔ adjb s t = true :=
    (correct (pr s t)).trans (pairSpec s t).symm
  have off (s : Vtx) : ¬V (one s) C.output := by
    intro h
    have eq : one s = pr s s := by funext v; simp [one,pr]
    rw [eq] at h
    have h1 := (same s s).1 h
    simp [adj_irr] at h1
  have cleanG (s t : Vtx) (j : Fin m) (op : A j)
      (h : V (pr s t) (W j)) : V (pr s t) C.output := by
    apply (same s t).2
    cases he : adjb s t with
    | true => rfl
    | false =>
      have hop : (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = .and := by
        unfold PEqualNP.MetaComplexity.NestedCover.gateAt
        change (C.gates[j.val]?.getD ⟨.or, []⟩).op = .and
        rw [hg]
        exact op
      have hz := clean j j.isLt hop s t he
      change val C.gates (W j) (pr s t) = false at hz
      exact (Bool.false_ne_true (hz.symm.trans h)).elim
  have cleanOne (v : Vtx) (j : Fin m) (op : A j)
      (h : V (one v) (W j)) : V (one v) C.output := by
    have he : one v = pr v v := by funext z; simp [one, pr]
    rw [he] at h ⊢
    exact cleanG v v j op h
  have legal : ∀ h ∈ C.gates, (h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2 := by
    intro h hh
    obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp hh
    obtain ⟨op,a',b',eq,_⟩ := gates j h hj
    exact ⟨op,by simp [eq]⟩
  have up (s t u : Vtx) (hu : u = s ∨ u = t) (w : ℕ) (hw : u ∈ S w) : V (pr s t) w := by
    apply val_mono C.gates legal (one u) (pr s t) _ w ((mem w u).1 hw)
    intro v hv
    have eq : v = u := of_decide_eq_true hv
    exact decide_eq_true (eq.symm ▸ hu)
  let X : Vtx := Fin.castAdd 13 p
  let Y : Vtx := Fin.natAdd 13 l
  have edge : adjb X Y = true := (adjSide p l).2 incidence
  have hout : C.output < 26+m := by
    by_contra! h
    have yes := (same X Y).2 edge
    change val C.gates C.output (pr X Y) = true at yes
    rw [val_big _ _ _ h] at yes
    contradiction
  left
  apply assemble a b S A C.output ha hb ne size hout ?_ ?_ ?_
    (fun s t w => V (pr s t) w) ?_ (fun s t => (same s t).2) ?_ ?_
    X Y edge (fun w => dP w = true) ?_ ?_ ?_
  · intro t
    ext s
    rw [mem]
    change val C.gates t.val (one s) = true ↔ _
    rw [val_input _ _ _ t.isLt]
    simp [one,eq_comm]
  · apply Finset.eq_empty_iff_forall_notMem.mpr
    exact fun v hv => off v ((mem _ _).mp hv)
  · intro j
    constructor
    · intro aj
      apply Finset.eq_empty_iff_forall_notMem.mpr
      exact fun v hv => off v (cleanOne v j aj ((mem _ _).mp hv))
    · intro no
      ext v
      rw [Finset.mem_union,mem,mem,mem,orEv _ j no]
  · intro s t v h
    change val C.gates v.val (pr s t) = true at h
    rw [val_input _ _ _ v.isLt] at h
    exact of_decide_eq_true h
  · intro s t j h
    exact ⟨fun op => (andEv _ j op).1 h,fun op => (orEv _ j op).1 h⟩
  · intro j op s hsa t htb
    exact (same s t).1 (cleanG s t j op ((andEv _ j op).2
      ⟨up s t s (.inl rfl) _ hsa,up s t t (.inr rfl) _ htb⟩))
  · rw [traceP.1 _ Y.isLt]
    simp [Y,Nat.add_comm]
  · intro j op h
    change dP (26+j.val) = true
    rw [(traceP.2 j (g j) (a j) (b j) (hg j) (pins j)).1 op]
    simp only [Bool.or_eq_true,Bool.and_eq_true]
    exact h.imp (fun hh => ⟨(mem _ _).mp hh.1,hh.2⟩) (fun hh => ⟨hh.1,(mem _ _).mp hh.2⟩)
  · intro j no h
    change dP (26+j.val) = true
    rw [(traceP.2 j (g j) (a j) (b j) (hg j) (pins j)).2 (orOp _ no),Bool.or_eq_true]
    exact h

lemma pair_clean_no_double : ¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), pairClean x1 ∧ (63 : ℕ) ≤ x1.size ∧ x1.size ≤ (64 : ℕ) ∧ (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (26 : ℕ) + x2 ∧ x6 < (26 : ℕ) + x2) ∧ (∀ (x2 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true ↔ ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), (x3 = x4 ∨ x3 = x4 + (1 : Fin (13 : ℕ)) ∨ x3 = x4 + (3 : Fin (13 : ℕ)) ∨ x3 = x4 + (9 : Fin (13 : ℕ))) ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true) ∧ (∃ (x2 : ℕ → Bool), (∀ x3 < (26 : ℕ), x2 x3 = Decidable.decide (x3 = (13 : ℕ))) ∧ (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate) (x5 x6 : ℕ), x1.gates[x3]? = Option.some x4 → x4.inputs = [x5, x6] → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and → x2 ((26 : ℕ) + x3) = ((x1.wires (List.ofFn fun (x10 : Fin (26 : ℕ)) => Decidable.decide (↑x10 = (0 : ℕ)))).getD x5 Bool.false && x2 x6 || x2 x5 && (x1.wires (List.ofFn fun (x10 : Fin (26 : ℕ)) => Decidable.decide (↑x10 = (0 : ℕ)))).getD x6 Bool.false)) ∧ (x4.op = PEqualNP.CircuitLowerBounds.GateOp.or → x2 ((26 : ℕ) + x3) = (x2 x5 || x2 x6))) ∧ x2 x1.output = Bool.false) ∧ ∃ (x2 : ℕ → Bool), (∀ x3 < (26 : ℕ), x2 x3 = Decidable.decide (x3 = (0 : ℕ))) ∧ (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate) (x5 x6 : ℕ), x1.gates[x3]? = Option.some x4 → x4.inputs = [x5, x6] → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and → x2 ((26 : ℕ) + x3) = ((x1.wires (List.ofFn fun (x10 : Fin (26 : ℕ)) => Decidable.decide (↑x10 = (13 : ℕ)))).getD x5 Bool.false && x2 x6 || x2 x5 && (x1.wires (List.ofFn fun (x10 : Fin (26 : ℕ)) => Decidable.decide (↑x10 = (13 : ℕ)))).getD x6 Bool.false)) ∧ (x4.op = PEqualNP.CircuitLowerBounds.GateOp.or → x2 ((26 : ℕ) + x3) = (x2 x5 || x2 x6))) ∧ x2 x1.output = Bool.false := by
  rintro ⟨C, hclean, hlo, hhi, hg, hf, ⟨v, hv0, hvstep, hvout⟩,
    w, hw0, hwstep, hwout⟩
  have hdiff (p l : Fin 13) :
      p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) ↔
      p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9 := by
    simp only [Finset.mem_insert, Finset.mem_singleton, sub_eq_zero,
      sub_eq_iff_eq_add, add_comm, add_zero]
  have hcorrect : ∀ x : Fin 26 → Bool,
      C.eval (List.ofFn x) = true ↔ ∃ p l : Fin 13,
      p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) ∧
      x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true := by
    intro x
    simpa only [hdiff] using hf x
  have hpval : (Fin.castAdd 13 (0 : Fin 13)).val = 0 := rfl
  have hlval : (Fin.natAdd 13 (0 : Fin 13)).val = 13 := rfl
  have result := pair_clean_trace C (0 : Fin 13) (0 : Fin 13) v w hhi hg hcorrect
    hclean (by decide) (by
      constructor
      · simpa using hv0
      · simpa only [Fin.ext_iff, hpval] using hvstep) (by
      constructor
      · simpa using hw0
      · simpa only [Fin.ext_iff, hlval] using hwstep)
  rcases result with h | h
  · rw [hvout] at h
    cases h
  · rw [hwout] at h
    cases h

end PairClean

end PEqualNP.Outside.L_meta_2602_aux
