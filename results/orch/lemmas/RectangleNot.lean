import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2373.RectangleNot

open PEqualNP.MetaComplexity

def edge (x : Fin 10 → Bool) : Bool :=
  ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),
    (5,7),(7,9),(9,6),(6,8),(8,5)] : List (Fin 10 × Fin 10)).any
    (fun e => x e.1 && x e.2)

def assignment (r : Nat) : Fin 10 → Bool := fun i => r.testBit i.val

def augment (x : Fin 10 → Bool) : Fin 11 → Bool := Fin.lastCases (!(x 0)) x

def positiveRows : Fin 21 → Nat := ![3, 6, 12, 13, 17, 24, 33, 66, 132, 133, 160, 264, 265, 288, 320, 321, 528, 576, 577, 640, 641]
def negativeRows : Fin 17 → Nat := ![50, 69, 104, 116, 138, 200, 201, 208, 276, 385, 402, 521, 548, 554, 770, 772, 773]
def positiveSample (r : Fin 21) : Fin 11 → Bool := augment (assignment (positiveRows r))
def negativeSample (r : Fin 17) : Fin 11 → Bool := augment (assignment (negativeRows r))
def weight : Fin 21 → Fin 17 → Int := ![
  ![-1, 0, -1, -67, 29, 0, 42, -3, -6, 25, 28, 12, -2, 50, 14, 0, 43],
  ![4, 0, -13, 52, 0, -6, -42, -3, 6, -13, 57, -8, 16, 60, 1, 9, 40],
  ![-3, 5, 13, 15, 0, 3, 1, -1, 2, -1, -18, 2, 8, 20, 0, 5, 1],
  ![1, 49, 0, 3, 0, -3, 43, 2, -4, -7, -39, 45, -2, -2, 1, 1, 37],
  ![2, 18, -1, 49, -2, 0, 43, 4, 11, 25, 59, 0, -5, -54, -14, 0, 37],
  ![8, -16, 0, 55, 2, 23, 43, 3, 3, -13, 57, 0, -7, 54, -10, -6, -37],
  ![-1, 15, 1, 64, -27, 0, 49, -2, -5, 0, -59, 13, 6, 54, -1, 0, 45],
  ![39, 0, 14, 59, 1, 6, 38, 5, 0, -12, 24, -4, -14, 58, 0, -9, -43],
  ![-1, 0, 0, 56, 0, 5, 0, 4, 0, 5, 56, 0, 0, -55, 0, 17, 0],
  ![0, 4, 0, 0, 0, 0, 41, 0, 0, 12, 0, -41, 0, -4, 0, 0, 45],
  ![1, 0, 0, 62, 27, 16, 38, 2, 0, 0, 39, -8, 0, 59, -1, -23, -45],
  ![-5, -3, -1, -52, 2, 17, 3, -2, -1, 0, 56, 2, -1, 54, 10, 6, 3],
  ![1, -36, 0, -3, -1, -2, 40, -1, 2, 13, 0, 8, 0, 0, 0, 0, 34],
  ![6, -15, 2, 54, 0, -16, -43, 0, 0, 0, 54, -4, 2, 58, 1, 23, 45],
  ![-1, 14, -1, 21, -1, 5, 0, 3, 0, 11, 21, 0, -1, -20, 0, 8, 1],
  ![1, 39, 1, 0, 0, 2, 41, -2, 0, 41, -1, -6, 1, -38, -1, -1, 43],
  ![37, -1, 0, 62, 0, -23, -43, 0, 0, -12, 23, 0, 12, 47, 25, 6, 33],
  ![-37, 0, 0, 55, -1, 19, 0, 0, 0, 0, -18, 0, 15, 56, 0, 1, 0],
  ![1, 5, 0, 1, 0, 0, 42, 0, 0, -39, -5, 8, 0, 0, 0, 0, 43],
  ![0, 0, 0, -21, 1, 6, 0, 0, 0, 9, 21, 8, 0, 21, 1, 7, 0],
  ![0, -3, 0, -41, 0, 0, 42, 0, 0, 42, 2, 42, 0, 0, 0, -1, 45]]
def support : Fin 11 → List (Fin 21) := ![
  [0, 3, 4, 6, 9, 12, 15, 18, 20],
  [0, 1, 7],
  [1, 2, 3, 8, 9],
  [2, 3, 5, 11, 12],
  [4, 5, 16],
  [6, 10, 13],
  [7, 14, 15, 17, 18],
  [8, 9, 10, 19, 20],
  [11, 12, 13, 14, 15],
  [16, 17, 18, 19, 20],
  [1, 2, 5, 7, 8, 10, 11, 13, 14, 16, 17, 19]]

def positions (i : Fin 11) (k : Fin (support i).length) : Fin 21 := (support i).get k

def rect (S : Finset (Fin 21)) (T : Finset (Fin 17)) : Int := ∑ r ∈ S, ∑ c ∈ T, weight r c

def negativeSet (i : Fin 11) : Finset (Fin 17) :=
  Finset.univ.filter (fun c => negativeSample c i = false)

def selected (i : Fin 11) (keep : Fin (support i).length → Bool) : Finset (Fin 21) :=
  (Finset.univ.filter (fun k => keep k = true)).image (positions i)

def maxRect (i : Fin 11) (S : Finset (Fin 21)) : Int :=
  ∑ c ∈ negativeSet i, max (∑ r ∈ S, weight r c) 0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma positions_cover : ∀ (i : Fin 11) (r : Fin 21),
    positiveSample r i = true ↔ ∃ k : Fin (support i).length, positions i k = r := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma finite_rectangle_bound : ∀ (i : Fin 11) (keep : Fin (support i).length → Bool),
    maxRect i (selected i keep) ≤ 128 := by
  intro i
  fin_cases i <;> decide +kernel

lemma selected_covers (i : Fin 11) (S : Finset (Fin 21))
    (hs : ∀ r ∈ S, positiveSample r i = true) :
    selected i (fun k => decide (positions i k ∈ S)) = S := by
  ext r
  simp only [selected, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and, decide_eq_true_eq]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact hk
  · intro hr
    obtain ⟨k, hk⟩ := (positions_cover i r).mp (hs r hr)
    exact ⟨k, by simpa only [hk] using hr, hk⟩

lemma leaf_bound (i : Fin 11) (S : Finset (Fin 21)) (T : Finset (Fin 17))
    (hs : ∀ r ∈ S, positiveSample r i = true)
    (ht : ∀ c ∈ T, negativeSample c i = false) : rect S T ≤ 128 := by
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
    _ ≤ 128 := by
      rw [← selected_covers i S hs]
      exact finite_rectangle_bound i _

lemma rect_union_left (S U : Finset (Fin 21)) (T : Finset (Fin 17)) (h : Disjoint S U) :
    rect (S ∪ U) T = rect S T + rect U T := by
  exact Finset.sum_union h

lemma rect_union_right (S : Finset (Fin 21)) (T U : Finset (Fin 17)) (h : Disjoint T U) :
    rect S (T ∪ U) = rect S T + rect S U := by
  simp only [rect, Finset.sum_union h, Finset.sum_add_distrib]

def positive : DMFormula 11 → Prop
  | .lit _ b => b = true
  | .and a b => positive a ∧ positive b
  | .or a b => positive a ∧ positive b

lemma formula_rectangle_bound (F : DMFormula 11) (hp : positive F) :
    ∀ (S : Finset (Fin 21)) (T : Finset (Fin 17)),
      (∀ r ∈ S, F.eval (positiveSample r) = true) →
      (∀ c ∈ T, F.eval (negativeSample c) = false) →
      rect S T ≤ 128 * (F.leaves : Int) := by
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
lemma full_weight : rect Finset.univ Finset.univ = 2439 := by decide +kernel

lemma positive_rows : ∀ r, edge (assignment (positiveRows r)) = true := by decide +kernel
lemma negative_rows : ∀ r, edge (assignment (negativeRows r)) = false := by decide +kernel

lemma not_formula_lower (F : DMFormula 11) (hp : positive F)
    (compute : ∀ x : Fin 10 → Bool, F.eval (augment x) = edge x) : 20 ≤ F.leaves := by
  have bound := formula_rectangle_bound F hp Finset.univ Finset.univ
    (fun r _ => (compute (assignment (positiveRows r))).trans (positive_rows r))
    (fun r _ => (compute (assignment (negativeRows r))).trans (negative_rows r))
  rw [full_weight] at bound
  omega

end PEqualNP.Outside.L_meta_2373.RectangleNot
