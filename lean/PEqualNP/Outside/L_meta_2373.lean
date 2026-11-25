import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_2373

def edge (x : Fin 10 → Bool) : Bool :=
    x 0 && x 1 ||
    x 1 && x 2 ||
    x 2 && x 3 ||
    x 3 && x 4 ||
    x 4 && x 0 ||
    x 0 && x 5 ||
    x 1 && x 6 ||
    x 2 && x 7 ||
    x 3 && x 8 ||
    x 4 && x 9 ||
    x 5 && x 7 ||
    x 7 && x 9 ||
    x 9 && x 6 ||
    x 6 && x 8 ||
    x 8 && x 5

lemma five_cycle_cover_weight (a b c d e : Nat)
    (hab : 1 ≤ a + b) (hbc : 1 ≤ b + c) (hcd : 1 ≤ c + d)
    (hde : 1 ≤ d + e) (hea : 1 ≤ e + a) : 3 ≤ a + b + c + d + e := by
  omega

lemma petersen_cover_weight (w : Fin 10 → Nat)
    (h01 : 1 ≤ w 0 + w 1) (h12 : 1 ≤ w 1 + w 2)
    (h23 : 1 ≤ w 2 + w 3) (h34 : 1 ≤ w 3 + w 4)
    (h40 : 1 ≤ w 4 + w 0) (h57 : 1 ≤ w 5 + w 7)
    (h79 : 1 ≤ w 7 + w 9) (h96 : 1 ≤ w 9 + w 6)
    (h68 : 1 ≤ w 6 + w 8) (h85 : 1 ≤ w 8 + w 5) :
    6 ≤ w 0 + w 1 + w 2 + w 3 + w 4 + w 5 + w 6 + w 7 + w 8 + w 9 := by
  have ho := five_cycle_cover_weight (w 0) (w 1) (w 2) (w 3) (w 4)
    h01 h12 h23 h34 h40
  have hi := five_cycle_cover_weight (w 5) (w 7) (w 9) (w 6) (w 8)
    h57 h79 h96 h68 h85
  omega


def petersenEdges : Finset (Fin 10 × Fin 10) :=
  {(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7),
    (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)}

lemma vertex_cover_size (s : Finset (Fin 10))
    (h : ∀ e ∈ petersenEdges, e.1 ∈ s ∨ e.2 ∈ s) : 6 ≤ s.card := by
  let w : Fin 10 → Nat := fun i => if i ∈ s then 1 else 0
  have hw (a b : Fin 10) (hab : (a, b) ∈ petersenEdges) : 1 ≤ w a + w b := by
    rcases h (a, b) hab with ha | hb
    · simp [w, ha]
    · simp [w, hb]
  have hh := petersen_cover_weight w
    (hw 0 1 (by decide)) (hw 1 2 (by decide)) (hw 2 3 (by decide))
    (hw 3 4 (by decide)) (hw 4 0 (by decide)) (hw 5 7 (by decide))
    (hw 7 9 (by decide)) (hw 9 6 (by decide)) (hw 6 8 (by decide))
    (hw 8 5 (by decide))
  have hsum : (∑ i : Fin 10, w i) = s.card := by
    simp [w]
  have hsum' : w 0 + w 1 + w 2 + w 3 + w 4 + w 5 + w 6 + w 7 + w 8 + w 9 =
      s.card := by
    simpa [Fin.sum_univ_succ, Nat.add_assoc] using hsum
  omega

lemma minimum_vertex_cover :
    ∃ s : Finset (Fin 10), s.card = 6 ∧
      ∀ e ∈ petersenEdges, e.1 ∈ s ∨ e.2 ∈ s := by
  exact ⟨{1, 3, 4, 5, 6, 7}, by decide, by decide⟩

lemma independent_set_size (s : Finset (Fin 10))
    (h : ∀ e ∈ petersenEdges, ¬ (e.1 ∈ s ∧ e.2 ∈ s)) : s.card ≤ 4 := by
  have hc : 6 ≤ sᶜ.card := vertex_cover_size sᶜ (by
    intro e he
    simpa only [Finset.mem_compl, not_and_or] using h e he)
  have hsum : sᶜ.card + s.card = 10 := by
    simpa only [Fintype.card_fin] using Finset.card_compl_add_card s
  omega

lemma edge_eq_false_iff (x : Fin 10 → Bool) :
    edge x = false ↔ ∀ e ∈ petersenEdges, x e.1 = false ∨ x e.2 = false := by
  simp only [edge, Bool.or_eq_false_iff, Bool.and_eq_false_iff]
  simp only [petersenEdges, Finset.forall_mem_insert, Finset.mem_singleton, forall_eq]
  simp only [and_assoc]

lemma false_input_support_size (x : Fin 10 → Bool) (hx : edge x = false) :
    (Finset.univ.filter fun i => x i = true).card ≤ 4 := by
  apply independent_set_size
  intro e he hab
  have hz := (edge_eq_false_iff x).mp hx e he
  rcases hz with hz | hz
  · have ht := (Finset.mem_filter.mp hab.1).2
    simp_all
  · have ht := (Finset.mem_filter.mp hab.2).2
    simp_all


end PEqualNP.Outside.L_meta_2373
