import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2373.RectangleAndEdge

open PEqualNP.MetaComplexity

def edge (x : Fin 10 → Bool) : Bool :=
  ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),
    (5,7),(7,9),(9,6),(6,8),(8,5)] : List (Fin 10 × Fin 10)).any
    (fun e => x e.1 && x e.2)

def assignment (r : Nat) : Fin 10 → Bool := fun i => r.testBit i.val

def augment (x : Fin 10 → Bool) : Fin 11 → Bool := Fin.lastCases (x 0 && x 1) x

def positiveRows : Fin 15 → Nat := ![3, 6, 12, 24, 17, 33, 66, 132, 264, 528, 160, 640, 576, 320, 288]
def negativeRows : Fin 15 → Nat := ![50, 69, 104, 116, 138, 201, 208, 276, 385, 402, 521, 548, 554, 770, 773]
def positiveSample (r : Fin 15) : Fin 11 → Bool := augment (assignment (positiveRows r))
def negativeSample (r : Fin 15) : Fin 11 → Bool := augment (assignment (negativeRows r))
def weight : Fin 15 → Fin 15 → Int := ![
  ![0, 0, 0, -2, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2],
  ![0, 0, 0, 2, 0, -3, 0, 0, 0, 3, 0, 0, 2, 1, 4],
  ![0, 0, 0, 3, 0, 3, 0, 0, 0, -5, 1, 1, 2, 0, 2],
  ![0, 0, 0, 3, 2, 2, 0, 0, 0, 3, 0, -1, 2, 0, -3],
  ![0, 0, 0, 2, -2, 4, 1, 1, 0, 2, 0, 0, -2, 0, 2],
  ![0, 1, 2, 2, 0, 3, -1, -1, 0, -2, 0, 0, 2, 0, 2],
  ![2, 3, 0, 0, 1, 3, 0, 0, 0, 2, 0, 0, 1, 0, -3],
  ![0, 1, 0, 2, 0, 3, 0, 1, 0, 3, -1, 0, -2, -1, 2],
  ![0, 0, 0, -3, 1, 2, 0, 0, 0, 3, 2, 0, 1, 0, 3],
  ![2, 0, 0, 2, 0, -4, 0, 0, 0, 2, 0, 1, 2, 0, 3],
  ![2, -1, 0, 2, 1, 2, 1, -1, 0, 2, 0, 0, 2, 0, -2],
  ![-2, 0, 0, -2, 1, 2, 0, 0, 0, 3, 1, 0, 2, 1, 2],
  ![0, 0, 0, 2, -1, 4, 0, 0, 0, -3, 2, 0, 1, 0, 3],
  ![-2, 0, 0, 3, 0, 3, 0, 0, 0, 3, -2, 0, -1, 0, 3],
  ![2, 0, 0, 3, -1, -3, 0, 2, 0, 2, 0, 0, 1, 0, 2]]
def positions : Fin 11 → Fin 6 → Fin 15 := ![
  ![0, 4, 5, 0, 0, 0],
  ![0, 1, 6, 0, 0, 0],
  ![1, 2, 7, 1, 1, 1],
  ![2, 3, 8, 2, 2, 2],
  ![3, 4, 9, 3, 3, 3],
  ![5, 10, 14, 5, 5, 5],
  ![6, 12, 13, 6, 6, 6],
  ![7, 10, 11, 7, 7, 7],
  ![8, 13, 14, 8, 8, 8],
  ![9, 11, 12, 9, 9, 9],
  ![0, 0, 0, 0, 0, 0]]

def rect (S T : Finset (Fin 15)) : Int := ∑ r ∈ S, ∑ c ∈ T, weight r c

def negativeSet (i : Fin 11) : Finset (Fin 15) :=
  Finset.univ.filter (fun c => negativeSample c i = false)

def selected (i : Fin 11) (keep : Fin 6 → Bool) : Finset (Fin 15) :=
  (Finset.univ.filter (fun k => keep k = true ∧ positiveSample (positions i k) i = true)).image (positions i)

def maxRect (i : Fin 11) (S : Finset (Fin 15)) : Int :=
  ∑ c ∈ negativeSet i, max (∑ r ∈ S, weight r c) 0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma positions_cover : ∀ (i : Fin 11) (r : Fin 15),
    positiveSample r i = true → ∃ k : Fin 6, positions i k = r := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma finite_rectangle_bound : ∀ (i : Fin 11) (keep : Fin 6 → Bool),
    maxRect i (selected i keep) ≤ 6 := by
  intro i
  fin_cases i <;> decide +kernel

lemma selected_covers (i : Fin 11) (S : Finset (Fin 15))
    (hs : ∀ r ∈ S, positiveSample r i = true) :
    selected i (fun k => decide (positions i k ∈ S)) = S := by
  ext r
  simp only [selected, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and, decide_eq_true_eq]
  constructor
  · rintro ⟨k, ⟨hk, _⟩, rfl⟩
    exact hk
  · intro hr
    obtain ⟨k, hk⟩ := positions_cover i r (hs r hr)
    exact ⟨k, ⟨by simpa only [hk] using hr, by simpa only [hk] using hs r hr⟩, hk⟩

lemma leaf_bound (i : Fin 11) (S T : Finset (Fin 15))
    (hs : ∀ r ∈ S, positiveSample r i = true)
    (ht : ∀ c ∈ T, negativeSample c i = false) : rect S T ≤ 6 := by
  have sub : T ⊆ negativeSet i := by
    intro c hc
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ c, ht c hc⟩
  calc
    rect S T = ∑ c ∈ T, ∑ r ∈ S, weight r c := by
      unfold rect
      rw [Finset.sum_comm]
    _ ≤ ∑ c ∈ T, max (∑ r ∈ S, weight r c) 0 :=
      Finset.sum_le_sum (fun _ _ => le_max_left _ _)
    _ ≤ maxRect i S := by
      exact Finset.sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => le_max_right _ _)
    _ ≤ 6 := by
      rw [← selected_covers i S hs]
      exact finite_rectangle_bound i _

lemma rect_union_left (S U T : Finset (Fin 15)) (h : Disjoint S U) :
    rect (S ∪ U) T = rect S T + rect U T := by
  exact Finset.sum_union h

lemma rect_union_right (S T U : Finset (Fin 15)) (h : Disjoint T U) :
    rect S (T ∪ U) = rect S T + rect S U := by
  simp only [rect, Finset.sum_union h, Finset.sum_add_distrib]

def positive : DMFormula 11 → Prop
  | .lit _ b => b = true
  | .and a b => positive a ∧ positive b
  | .or a b => positive a ∧ positive b

lemma formula_rectangle_bound (F : DMFormula 11) (hp : positive F) :
    ∀ (S T : Finset (Fin 15)),
      (∀ r ∈ S, F.eval (positiveSample r) = true) →
      (∀ c ∈ T, F.eval (negativeSample c) = false) →
      rect S T ≤ 6 * (F.leaves : Int) := by
  induction F with
  | lit i b =>
    have hb : b = true := hp
    subst b
    intro S T hs ht
    simpa only [DMFormula.leaves, Nat.cast_one, mul_one] using
      leaf_bound i S T (by simpa [DMFormula.eval] using hs)
        (by simpa [DMFormula.eval] using ht)
  | and A B ihA ihB =>
    intro S T hs ht
    let T0 := T.filter (fun c => A.eval (negativeSample c) = false)
    let T1 := T.filter (fun c => A.eval (negativeSample c) = true)
    have part : T0 ∪ T1 = T := by
      ext c
      simp only [T0, T1, Finset.mem_union, Finset.mem_filter]
      cases A.eval (negativeSample c) <;> simp
    have disj : Disjoint T0 T1 := by
      apply Finset.disjoint_left.mpr
      intro c hc hd
      have h0 := (Finset.mem_filter.mp hc).2
      have h1 := (Finset.mem_filter.mp hd).2
      exact Bool.false_ne_true (h0.symm.trans h1)
    have ha := ihA hp.1 S T0
      (fun r hr => (Bool.and_eq_true_iff.mp (hs r hr)).1)
      (fun c hc => (Finset.mem_filter.mp hc).2)
    have hb := ihB hp.2 S T1
      (fun r hr => (Bool.and_eq_true_iff.mp (hs r hr)).2)
      (fun c hc => by
        obtain ⟨hc, ha⟩ := Finset.mem_filter.mp hc
        have h := ht c hc
        change (A.eval (negativeSample c) && B.eval (negativeSample c)) = false at h
        simpa only [ha, Bool.true_and] using h)
    rw [← part, rect_union_right S T0 T1 disj]
    simpa only [DMFormula.leaves, Nat.cast_add, mul_add] using add_le_add ha hb
  | or A B ihA ihB =>
    intro S T hs ht
    let S0 := S.filter (fun r => A.eval (positiveSample r) = true)
    let S1 := S.filter (fun r => A.eval (positiveSample r) = false)
    have part : S0 ∪ S1 = S := by
      ext r
      simp only [S0, S1, Finset.mem_union, Finset.mem_filter]
      cases A.eval (positiveSample r) <;> simp
    have disj : Disjoint S0 S1 := by
      apply Finset.disjoint_left.mpr
      intro r hr hd
      have h0 := (Finset.mem_filter.mp hr).2
      have h1 := (Finset.mem_filter.mp hd).2
      exact Bool.false_ne_true (h1.symm.trans h0)
    have ha := ihA hp.1 S0 T
      (fun r hr => (Finset.mem_filter.mp hr).2)
      (fun c hc => (Bool.or_eq_false_iff.mp (ht c hc)).1)
    have hb := ihB hp.2 S1 T
      (fun r hr => by
        obtain ⟨hr, ha⟩ := Finset.mem_filter.mp hr
        have h := hs r hr
        change (A.eval (positiveSample r) || B.eval (positiveSample r)) = true at h
        simpa only [ha, Bool.false_or] using h)
      (fun c hc => (Bool.or_eq_false_iff.mp (ht c hc)).2)
    rw [← part, rect_union_left S0 S1 T disj]
    simpa only [DMFormula.leaves, Nat.cast_add, mul_add] using add_le_add ha hb

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma full_weight : rect Finset.univ Finset.univ = 117 := by decide +kernel

lemma positive_rows : ∀ r, edge (assignment (positiveRows r)) = true := by decide +kernel
lemma negative_rows : ∀ r, edge (assignment (negativeRows r)) = false := by decide +kernel

lemma adjacent_and_formula_lower (F : DMFormula 11) (hp : positive F)
    (compute : ∀ x : Fin 10 → Bool, F.eval (augment x) = edge x) : 20 ≤ F.leaves := by
  have bound := formula_rectangle_bound F hp Finset.univ Finset.univ
    (fun r _ => (compute (assignment (positiveRows r))).trans (positive_rows r))
    (fun r _ => (compute (assignment (negativeRows r))).trans (negative_rows r))
  rw [full_weight] at bound
  omega

end PEqualNP.Outside.L_meta_2373.RectangleAndEdge

namespace PEqualNP.Outside.L_meta_2373.RectangleAndNonedge

open PEqualNP.MetaComplexity

def edge (x : Fin 10 → Bool) : Bool :=
  ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),
    (5,7),(7,9),(9,6),(6,8),(8,5)] : List (Fin 10 × Fin 10)).any
    (fun e => x e.1 && x e.2)

def assignment (r : Nat) : Fin 10 → Bool := fun i => r.testBit i.val

def augment (x : Fin 10 → Bool) : Fin 11 → Bool := Fin.lastCases (x 0 && x 2) x

def positiveRows : Fin 15 → Nat := ![3, 6, 12, 24, 17, 33, 66, 132, 264, 528, 160, 640, 576, 320, 288]
def negativeRows : Fin 15 → Nat := ![50, 69, 104, 116, 138, 201, 208, 276, 385, 402, 521, 548, 554, 770, 773]
def positiveSample (r : Fin 15) : Fin 11 → Bool := augment (assignment (positiveRows r))
def negativeSample (r : Fin 15) : Fin 11 → Bool := augment (assignment (negativeRows r))
def weight : Fin 15 → Fin 15 → Int := ![
  ![0, 0, 0, -1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1],
  ![1, 0, 0, 1, 0, -1, 0, 1, 0, 0, 0, 0, 1, 0, 0],
  ![-1, 0, 0, 1, 0, 1, 0, 0, -1, 0, 0, 0, 1, 0, 1],
  ![1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1],
  ![0, 0, 0, 1, -1, 1, 0, 0, 0, 1, 0, 0, -1, 0, 1],
  ![0, 1, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 1],
  ![0, 0, 0, 1, 0, 1, 0, -1, 0, 1, 0, 0, 1, 0, -1],
  ![0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, -1, 0, 1],
  ![0, 0, 0, -1, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1],
  ![0, 0, 0, 1, 0, -1, 0, 0, 0, 1, 0, 0, 1, 0, 1],
  ![0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, -1],
  ![0, 0, -1, -1, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 1],
  ![0, 0, 1, 0, 0, 1, 0, 0, 0, -1, 0, 0, 1, 0, 1],
  ![0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, -1, 0, 0],
  ![0, -1, 0, 1, 0, -1, 0, 0, 0, 1, 0, 0, 1, 0, 1]]
def positions : Fin 11 → Fin 6 → Fin 15 := ![
  ![0, 4, 5, 0, 0, 0],
  ![0, 1, 6, 0, 0, 0],
  ![1, 2, 7, 1, 1, 1],
  ![2, 3, 8, 2, 2, 2],
  ![3, 4, 9, 3, 3, 3],
  ![5, 10, 14, 5, 5, 5],
  ![6, 12, 13, 6, 6, 6],
  ![7, 10, 11, 7, 7, 7],
  ![8, 13, 14, 8, 8, 8],
  ![9, 11, 12, 9, 9, 9],
  ![0, 0, 0, 0, 0, 0]]

def rect (S T : Finset (Fin 15)) : Int := ∑ r ∈ S, ∑ c ∈ T, weight r c

def negativeSet (i : Fin 11) : Finset (Fin 15) :=
  Finset.univ.filter (fun c => negativeSample c i = false)

def selected (i : Fin 11) (keep : Fin 6 → Bool) : Finset (Fin 15) :=
  (Finset.univ.filter (fun k => keep k = true ∧ positiveSample (positions i k) i = true)).image (positions i)

def maxRect (i : Fin 11) (S : Finset (Fin 15)) : Int :=
  ∑ c ∈ negativeSet i, max (∑ r ∈ S, weight r c) 0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma positions_cover : ∀ (i : Fin 11) (r : Fin 15),
    positiveSample r i = true → ∃ k : Fin 6, positions i k = r := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma finite_rectangle_bound : ∀ (i : Fin 11) (keep : Fin 6 → Bool),
    maxRect i (selected i keep) ≤ 2 := by
  intro i
  fin_cases i <;> decide +kernel

lemma selected_covers (i : Fin 11) (S : Finset (Fin 15))
    (hs : ∀ r ∈ S, positiveSample r i = true) :
    selected i (fun k => decide (positions i k ∈ S)) = S := by
  ext r
  simp only [selected, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and, decide_eq_true_eq]
  constructor
  · rintro ⟨k, ⟨hk, _⟩, rfl⟩
    exact hk
  · intro hr
    obtain ⟨k, hk⟩ := positions_cover i r (hs r hr)
    exact ⟨k, ⟨by simpa only [hk] using hr, by simpa only [hk] using hs r hr⟩, hk⟩

lemma leaf_bound (i : Fin 11) (S T : Finset (Fin 15))
    (hs : ∀ r ∈ S, positiveSample r i = true)
    (ht : ∀ c ∈ T, negativeSample c i = false) : rect S T ≤ 2 := by
  have sub : T ⊆ negativeSet i := by
    intro c hc
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ c, ht c hc⟩
  calc
    rect S T = ∑ c ∈ T, ∑ r ∈ S, weight r c := by
      unfold rect
      rw [Finset.sum_comm]
    _ ≤ ∑ c ∈ T, max (∑ r ∈ S, weight r c) 0 :=
      Finset.sum_le_sum (fun _ _ => le_max_left _ _)
    _ ≤ maxRect i S := by
      exact Finset.sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => le_max_right _ _)
    _ ≤ 2 := by
      rw [← selected_covers i S hs]
      exact finite_rectangle_bound i _

lemma rect_union_left (S U T : Finset (Fin 15)) (h : Disjoint S U) :
    rect (S ∪ U) T = rect S T + rect U T := by
  exact Finset.sum_union h

lemma rect_union_right (S T U : Finset (Fin 15)) (h : Disjoint T U) :
    rect S (T ∪ U) = rect S T + rect S U := by
  simp only [rect, Finset.sum_union h, Finset.sum_add_distrib]

def positive : DMFormula 11 → Prop
  | .lit _ b => b = true
  | .and a b => positive a ∧ positive b
  | .or a b => positive a ∧ positive b

lemma formula_rectangle_bound (F : DMFormula 11) (hp : positive F) :
    ∀ (S T : Finset (Fin 15)),
      (∀ r ∈ S, F.eval (positiveSample r) = true) →
      (∀ c ∈ T, F.eval (negativeSample c) = false) →
      rect S T ≤ 2 * (F.leaves : Int) := by
  induction F with
  | lit i b =>
    have hb : b = true := hp
    subst b
    intro S T hs ht
    simpa only [DMFormula.leaves, Nat.cast_one, mul_one] using
      leaf_bound i S T (by simpa [DMFormula.eval] using hs)
        (by simpa [DMFormula.eval] using ht)
  | and A B ihA ihB =>
    intro S T hs ht
    let T0 := T.filter (fun c => A.eval (negativeSample c) = false)
    let T1 := T.filter (fun c => A.eval (negativeSample c) = true)
    have part : T0 ∪ T1 = T := by
      ext c
      simp only [T0, T1, Finset.mem_union, Finset.mem_filter]
      cases A.eval (negativeSample c) <;> simp
    have disj : Disjoint T0 T1 := by
      apply Finset.disjoint_left.mpr
      intro c hc hd
      have h0 := (Finset.mem_filter.mp hc).2
      have h1 := (Finset.mem_filter.mp hd).2
      exact Bool.false_ne_true (h0.symm.trans h1)
    have ha := ihA hp.1 S T0
      (fun r hr => (Bool.and_eq_true_iff.mp (hs r hr)).1)
      (fun c hc => (Finset.mem_filter.mp hc).2)
    have hb := ihB hp.2 S T1
      (fun r hr => (Bool.and_eq_true_iff.mp (hs r hr)).2)
      (fun c hc => by
        obtain ⟨hc, ha⟩ := Finset.mem_filter.mp hc
        have h := ht c hc
        change (A.eval (negativeSample c) && B.eval (negativeSample c)) = false at h
        simpa only [ha, Bool.true_and] using h)
    rw [← part, rect_union_right S T0 T1 disj]
    simpa only [DMFormula.leaves, Nat.cast_add, mul_add] using add_le_add ha hb
  | or A B ihA ihB =>
    intro S T hs ht
    let S0 := S.filter (fun r => A.eval (positiveSample r) = true)
    let S1 := S.filter (fun r => A.eval (positiveSample r) = false)
    have part : S0 ∪ S1 = S := by
      ext r
      simp only [S0, S1, Finset.mem_union, Finset.mem_filter]
      cases A.eval (positiveSample r) <;> simp
    have disj : Disjoint S0 S1 := by
      apply Finset.disjoint_left.mpr
      intro r hr hd
      have h0 := (Finset.mem_filter.mp hr).2
      have h1 := (Finset.mem_filter.mp hd).2
      exact Bool.false_ne_true (h1.symm.trans h0)
    have ha := ihA hp.1 S0 T
      (fun r hr => (Finset.mem_filter.mp hr).2)
      (fun c hc => (Bool.or_eq_false_iff.mp (ht c hc)).1)
    have hb := ihB hp.2 S1 T
      (fun r hr => by
        obtain ⟨hr, ha⟩ := Finset.mem_filter.mp hr
        have h := hs r hr
        change (A.eval (positiveSample r) || B.eval (positiveSample r)) = true at h
        simpa only [ha, Bool.false_or] using h)
      (fun c hc => (Bool.or_eq_false_iff.mp (ht c hc)).2)
    rw [← part, rect_union_left S0 S1 T disj]
    simpa only [DMFormula.leaves, Nat.cast_add, mul_add] using add_le_add ha hb

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma full_weight : rect Finset.univ Finset.univ = 40 := by decide +kernel

lemma positive_rows : ∀ r, edge (assignment (positiveRows r)) = true := by decide +kernel
lemma negative_rows : ∀ r, edge (assignment (negativeRows r)) = false := by decide +kernel

lemma nonadjacent_and_formula_lower (F : DMFormula 11) (hp : positive F)
    (compute : ∀ x : Fin 10 → Bool, F.eval (augment x) = edge x) : 20 ≤ F.leaves := by
  have bound := formula_rectangle_bound F hp Finset.univ Finset.univ
    (fun r _ => (compute (assignment (positiveRows r))).trans (positive_rows r))
    (fun r _ => (compute (assignment (negativeRows r))).trans (negative_rows r))
  rw [full_weight] at bound
  omega

end PEqualNP.Outside.L_meta_2373.RectangleAndNonedge

namespace PEqualNP.Outside.L_meta_2373.RectangleOrNonedge

open PEqualNP.MetaComplexity

def edge (x : Fin 10 → Bool) : Bool :=
  ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),
    (5,7),(7,9),(9,6),(6,8),(8,5)] : List (Fin 10 × Fin 10)).any
    (fun e => x e.1 && x e.2)

def assignment (r : Nat) : Fin 10 → Bool := fun i => r.testBit i.val

def augment (x : Fin 10 → Bool) : Fin 11 → Bool := Fin.lastCases (x 0 || x 2) x

def positiveRows : Fin 15 → Nat := ![3, 6, 12, 24, 17, 33, 66, 132, 264, 528, 160, 640, 576, 320, 288]
def negativeRows : Fin 15 → Nat := ![50, 69, 104, 116, 138, 201, 208, 276, 385, 402, 521, 548, 554, 770, 773]
def positiveSample (r : Fin 15) : Fin 11 → Bool := augment (assignment (positiveRows r))
def negativeSample (r : Fin 15) : Fin 11 → Bool := augment (assignment (negativeRows r))
def weight : Fin 15 → Fin 15 → Int := ![
  ![0, -1, 0, -5, 0, 6, 0, 0, 0, 4, 6, 0, 4, 0, 0],
  ![0, 1, 0, 5, 0, -6, 0, 0, 0, 0, 0, 0, 4, 0, 6],
  ![0, 0, 0, 2, 0, 4, 0, 0, -2, -5, 6, 3, 2, 0, 7],
  ![1, 0, 0, 2, 4, 3, 4, 0, 0, 5, 0, 0, 5, 0, -7],
  ![0, 0, 0, 4, 0, 5, 0, 4, 0, 4, 0, -2, -5, 0, 7],
  ![0, 0, 0, 8, 0, 4, 0, -4, 0, -4, 0, 2, 2, 0, 8],
  ![0, 1, 0, 5, 0, 6, 0, 0, 0, 6, -6, 0, 6, 0, -6],
  ![0, 0, 0, 4, 0, 0, 0, 0, 8, 4, -4, 0, -4, 0, 8],
  ![-1, 0, 0, -2, 0, 6, -4, 0, 2, 5, 0, -3, 6, 0, 5],
  ![0, 0, 0, 6, -4, -6, 0, 0, 0, 6, 0, 2, 5, 0, 5],
  ![0, 0, 2, 6, 0, 8, 0, 0, 0, 4, 0, 0, 4, 0, -8],
  ![0, 0, -2, -6, 4, 2, 0, 0, 0, 6, 4, 0, 4, 0, 4],
  ![0, 0, 2, 4, 0, 6, 0, 0, 0, -6, 6, 0, 6, 0, 0],
  ![0, 0, 0, 2, 0, 6, 4, 0, 0, 6, 0, 0, -6, 0, 6],
  ![1, 0, 0, 2, 0, -8, 0, 4, 0, 4, 0, 3, 6, 0, 4]]
def positions : Fin 11 → Fin 6 → Fin 15 := ![
  ![0, 4, 5, 0, 0, 0],
  ![0, 1, 6, 0, 0, 0],
  ![1, 2, 7, 1, 1, 1],
  ![2, 3, 8, 2, 2, 2],
  ![3, 4, 9, 3, 3, 3],
  ![5, 10, 14, 5, 5, 5],
  ![6, 12, 13, 6, 6, 6],
  ![7, 10, 11, 7, 7, 7],
  ![8, 13, 14, 8, 8, 8],
  ![9, 11, 12, 9, 9, 9],
  ![0, 1, 2, 4, 5, 7]]

def rect (S T : Finset (Fin 15)) : Int := ∑ r ∈ S, ∑ c ∈ T, weight r c

def negativeSet (i : Fin 11) : Finset (Fin 15) :=
  Finset.univ.filter (fun c => negativeSample c i = false)

def selected (i : Fin 11) (keep : Fin 6 → Bool) : Finset (Fin 15) :=
  (Finset.univ.filter (fun k => keep k = true ∧ positiveSample (positions i k) i = true)).image (positions i)

def maxRect (i : Fin 11) (S : Finset (Fin 15)) : Int :=
  ∑ c ∈ negativeSet i, max (∑ r ∈ S, weight r c) 0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma positions_cover : ∀ (i : Fin 11) (r : Fin 15),
    positiveSample r i = true → ∃ k : Fin 6, positions i k = r := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma finite_rectangle_bound : ∀ (i : Fin 11) (keep : Fin 6 → Bool),
    maxRect i (selected i keep) ≤ 12 := by
  intro i
  fin_cases i <;> decide +kernel

lemma selected_covers (i : Fin 11) (S : Finset (Fin 15))
    (hs : ∀ r ∈ S, positiveSample r i = true) :
    selected i (fun k => decide (positions i k ∈ S)) = S := by
  ext r
  simp only [selected, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and, decide_eq_true_eq]
  constructor
  · rintro ⟨k, ⟨hk, _⟩, rfl⟩
    exact hk
  · intro hr
    obtain ⟨k, hk⟩ := positions_cover i r (hs r hr)
    exact ⟨k, ⟨by simpa only [hk] using hr, by simpa only [hk] using hs r hr⟩, hk⟩

lemma leaf_bound (i : Fin 11) (S T : Finset (Fin 15))
    (hs : ∀ r ∈ S, positiveSample r i = true)
    (ht : ∀ c ∈ T, negativeSample c i = false) : rect S T ≤ 12 := by
  have sub : T ⊆ negativeSet i := by
    intro c hc
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ c, ht c hc⟩
  calc
    rect S T = ∑ c ∈ T, ∑ r ∈ S, weight r c := by
      unfold rect
      rw [Finset.sum_comm]
    _ ≤ ∑ c ∈ T, max (∑ r ∈ S, weight r c) 0 :=
      Finset.sum_le_sum (fun _ _ => le_max_left _ _)
    _ ≤ maxRect i S := by
      exact Finset.sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => le_max_right _ _)
    _ ≤ 12 := by
      rw [← selected_covers i S hs]
      exact finite_rectangle_bound i _

lemma rect_union_left (S U T : Finset (Fin 15)) (h : Disjoint S U) :
    rect (S ∪ U) T = rect S T + rect U T := by
  exact Finset.sum_union h

lemma rect_union_right (S T U : Finset (Fin 15)) (h : Disjoint T U) :
    rect S (T ∪ U) = rect S T + rect S U := by
  simp only [rect, Finset.sum_union h, Finset.sum_add_distrib]

def positive : DMFormula 11 → Prop
  | .lit _ b => b = true
  | .and a b => positive a ∧ positive b
  | .or a b => positive a ∧ positive b

lemma formula_rectangle_bound (F : DMFormula 11) (hp : positive F) :
    ∀ (S T : Finset (Fin 15)),
      (∀ r ∈ S, F.eval (positiveSample r) = true) →
      (∀ c ∈ T, F.eval (negativeSample c) = false) →
      rect S T ≤ 12 * (F.leaves : Int) := by
  induction F with
  | lit i b =>
    have hb : b = true := hp
    subst b
    intro S T hs ht
    simpa only [DMFormula.leaves, Nat.cast_one, mul_one] using
      leaf_bound i S T (by simpa [DMFormula.eval] using hs)
        (by simpa [DMFormula.eval] using ht)
  | and A B ihA ihB =>
    intro S T hs ht
    let T0 := T.filter (fun c => A.eval (negativeSample c) = false)
    let T1 := T.filter (fun c => A.eval (negativeSample c) = true)
    have part : T0 ∪ T1 = T := by
      ext c
      simp only [T0, T1, Finset.mem_union, Finset.mem_filter]
      cases A.eval (negativeSample c) <;> simp
    have disj : Disjoint T0 T1 := by
      apply Finset.disjoint_left.mpr
      intro c hc hd
      have h0 := (Finset.mem_filter.mp hc).2
      have h1 := (Finset.mem_filter.mp hd).2
      exact Bool.false_ne_true (h0.symm.trans h1)
    have ha := ihA hp.1 S T0
      (fun r hr => (Bool.and_eq_true_iff.mp (hs r hr)).1)
      (fun c hc => (Finset.mem_filter.mp hc).2)
    have hb := ihB hp.2 S T1
      (fun r hr => (Bool.and_eq_true_iff.mp (hs r hr)).2)
      (fun c hc => by
        obtain ⟨hc, ha⟩ := Finset.mem_filter.mp hc
        have h := ht c hc
        change (A.eval (negativeSample c) && B.eval (negativeSample c)) = false at h
        simpa only [ha, Bool.true_and] using h)
    rw [← part, rect_union_right S T0 T1 disj]
    simpa only [DMFormula.leaves, Nat.cast_add, mul_add] using add_le_add ha hb
  | or A B ihA ihB =>
    intro S T hs ht
    let S0 := S.filter (fun r => A.eval (positiveSample r) = true)
    let S1 := S.filter (fun r => A.eval (positiveSample r) = false)
    have part : S0 ∪ S1 = S := by
      ext r
      simp only [S0, S1, Finset.mem_union, Finset.mem_filter]
      cases A.eval (positiveSample r) <;> simp
    have disj : Disjoint S0 S1 := by
      apply Finset.disjoint_left.mpr
      intro r hr hd
      have h0 := (Finset.mem_filter.mp hr).2
      have h1 := (Finset.mem_filter.mp hd).2
      exact Bool.false_ne_true (h1.symm.trans h0)
    have ha := ihA hp.1 S0 T
      (fun r hr => (Finset.mem_filter.mp hr).2)
      (fun c hc => (Bool.or_eq_false_iff.mp (ht c hc)).1)
    have hb := ihB hp.2 S1 T
      (fun r hr => by
        obtain ⟨hr, ha⟩ := Finset.mem_filter.mp hr
        have h := hs r hr
        change (A.eval (positiveSample r) || B.eval (positiveSample r)) = true at h
        simpa only [ha, Bool.false_or] using h)
      (fun c hc => (Bool.or_eq_false_iff.mp (ht c hc)).2)
    rw [← part, rect_union_left S0 S1 T disj]
    simpa only [DMFormula.leaves, Nat.cast_add, mul_add] using add_le_add ha hb

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma full_weight : rect Finset.univ Finset.univ = 231 := by decide +kernel

lemma positive_rows : ∀ r, edge (assignment (positiveRows r)) = true := by decide +kernel
lemma negative_rows : ∀ r, edge (assignment (negativeRows r)) = false := by decide +kernel

lemma nonadjacent_or_formula_lower (F : DMFormula 11) (hp : positive F)
    (compute : ∀ x : Fin 10 → Bool, F.eval (augment x) = edge x) : 20 ≤ F.leaves := by
  have bound := formula_rectangle_bound F hp Finset.univ Finset.univ
    (fun r _ => (compute (assignment (positiveRows r))).trans (positive_rows r))
    (fun r _ => (compute (assignment (negativeRows r))).trans (negative_rows r))
  rw [full_weight] at bound
  omega

end PEqualNP.Outside.L_meta_2373.RectangleOrNonedge
