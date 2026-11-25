import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583_aux.FourClause

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

abbrev Row := Fin 64
abbrev Matrix := Fin 512

def bit (r : Row) (v : Fin 6) : Bool := r.val.testBit v.val

def adj (m : Matrix) (p l : Fin 3) : Bool := m.val.testBit (3 * p.val + l.val)

def valid (m : Matrix) : Prop :=
  (∀ p : Fin 3, adj m p p = true) ∧
  (∀ p p' l l' : Fin 3, p ≠ p' → l ≠ l' →
    ¬ (adj m p l = true ∧ adj m p' l = true ∧ adj m p l' = true ∧ adj m p' l' = true))

def rows (m : Matrix) : List ℕ :=
  match m.val with
  | 273 => [7, 14, 21, 28, 35]
  | 275 => [7, 14, 28, 35, 42]
  | 277 => [7, 14, 21, 28, 42]
  | 279 => [7, 14, 28, 42, 56]
  | 281 => [7, 21, 28, 35, 49]
  | 285 => [7, 21, 28, 34, 56]
  | 305 => [7, 14, 21, 28, 49]
  | 307 => [7, 14, 28, 33, 56]
  | 309 => [7, 14, 21, 28, 56]
  | 313 => [7, 21, 28, 49, 56]
  | 337 => [7, 21, 35, 42, 49]
  | 339 => [7, 20, 35, 42, 56]
  | 345 => [7, 21, 35, 49, 56]
  | 369 => [7, 10, 21, 49, 56]
  | 371 => [7, 10, 20, 33, 56]
  | 401 => [7, 14, 35, 42, 49]
  | 403 => [7, 14, 35, 42, 56]
  | 405 => [7, 14, 17, 42, 56]
  | 409 => [7, 12, 35, 49, 56]
  | 413 => [7, 12, 17, 34, 56]
  | 465 => [7, 35, 42, 49, 56]
  | _ => []

def witness (m : Matrix) (i : Fin 5) : Row := Fin.ofNat 64 ((rows m).getD i.val 0)

def independent (m : Matrix) (r : Row) : Prop :=
  ∀ p l : Fin 3, adj m p l = true →
    ¬ (bit r (Fin.castAdd 3 p) = true ∧ bit r (Fin.natAdd 3 l) = true)

def pairCovered (r s : Row) : Prop :=
  ∃ p : Fin 3,
    (bit r (Fin.castAdd 3 p) = true ∨ bit s (Fin.castAdd 3 p) = true) ∧
    (bit r (Fin.natAdd 3 p) = true ∨ bit s (Fin.natAdd 3 p) = true)

theorem certificate : ∀ m : Matrix, valid m →
    (∀ i : Fin 5, independent m (witness m i)) ∧
    (∀ i j : Fin 5, i ≠ j → pairCovered (witness m i) (witness m j)) := by
  letI (m : Matrix) : Decidable (valid m) := by unfold valid; infer_instance
  letI (m : Matrix) (r : Row) : Decidable (independent m r) := by unfold independent; infer_instance
  letI (r s : Row) : Decidable (pairCovered r s) := by unfold pairCovered; infer_instance
  decide

theorem clauses_ge_five {k : ℕ} (m : Matrix) (hm : valid m)
    (clauses : Fin k → Finset (Fin 6))
    (hmatching : ∀ j p, Fin.castAdd 3 p ∈ clauses j ∨ Fin.natAdd 3 p ∈ clauses j)
    (hclean : ∀ x : Fin 6 → Bool,
      (∀ j, ∃ v ∈ clauses j, x v = true) →
      ∃ p l : Fin 3, adj m p l = true ∧
        x (Fin.castAdd 3 p) = true ∧ x (Fin.natAdd 3 l) = true) :
    5 ≤ k := by
  classical
  have hc := certificate m hm
  have hex (i : Fin 5) : ∃ j, ¬ ∃ v ∈ clauses j, bit (witness m i) v = true := by
    by_contra h
    push_neg at h
    obtain ⟨p, l, hpl, hp, hl⟩ := hclean (bit (witness m i)) h
    exact hc.1 i p l hpl ⟨hp, hl⟩
  choose selected hselected using hex
  have hinj : Function.Injective selected := by
    intro i j hij
    by_contra hne
    obtain ⟨p, hp, hl⟩ := hc.2 i j hne
    rcases hmatching (selected i) p with hmem | hmem
    · rcases hp with hi | hj
      · exact hselected i ⟨_, hmem, hi⟩
      · exact hselected j ⟨_, hij ▸ hmem, hj⟩
    · rcases hl with hi | hj
      · exact hselected i ⟨_, hmem, hi⟩
      · exact hselected j ⟨_, hij ▸ hmem, hj⟩
  have hcard := Fintype.card_le_of_injective selected hinj
  simpa using hcard

theorem four_clauses_impossible (m : Matrix) (hm : valid m)
    (clauses : Fin 4 → Finset (Fin 6))
    (hmatching : ∀ j p, Fin.castAdd 3 p ∈ clauses j ∨ Fin.natAdd 3 p ∈ clauses j)
    (hclean : ∀ x : Fin 6 → Bool,
      (∀ j, ∃ v ∈ clauses j, x v = true) →
      ∃ p l : Fin 3, adj m p l = true ∧
        x (Fin.castAdd 3 p) = true ∧ x (Fin.natAdd 3 l) = true) : False := by
  have := clauses_ge_five m hm clauses hmatching hclean
  omega

def encode (R : Fin 3 → Fin 3 → Bool) : Matrix := Fin.ofNat 512 (
  (if R 0 0 then 1 else 0) +
  (if R 0 1 then 2 else 0) +
  (if R 0 2 then 4 else 0) +
  (if R 1 0 then 8 else 0) +
  (if R 1 1 then 16 else 0) +
  (if R 1 2 then 32 else 0) +
  (if R 2 0 then 64 else 0) +
  (if R 2 1 then 128 else 0) +
  (if R 2 2 then 256 else 0))

theorem adj_encode : ∀ (R : Fin 3 → Fin 3 → Bool) (p l : Fin 3),
    adj (encode R) p l = R p l := by decide

theorem clauses_ge_five_relation {k : ℕ} (R : Fin 3 → Fin 3 → Prop) [DecidableRel R]
    (hdiag : ∀ p, R p p)
    (hrect : ∀ p p' l l', p ≠ p' → l ≠ l' → ¬ (R p l ∧ R p' l ∧ R p l' ∧ R p' l'))
    (clauses : Fin k → Finset (Fin 6))
    (hmatching : ∀ j p, Fin.castAdd 3 p ∈ clauses j ∨ Fin.natAdd 3 p ∈ clauses j)
    (hclean : ∀ x : Fin 6 → Bool,
      (∀ j, ∃ v ∈ clauses j, x v = true) →
      ∃ p l : Fin 3, R p l ∧
        x (Fin.castAdd 3 p) = true ∧ x (Fin.natAdd 3 l) = true) :
    5 ≤ k := by
  let m := encode (fun p l => decide (R p l))
  have hm : valid m := by
    constructor
    · intro p
      simpa [m, adj_encode] using hdiag p
    · intro p p' l l' hp hl
      simpa only [m, adj_encode, decide_eq_true_eq] using hrect p p' l l' hp hl
  apply clauses_ge_five m hm clauses hmatching
  intro x hx
  obtain ⟨p, l, hpl, hp, hl⟩ := hclean x hx
  refine ⟨p, l, ?_, hp, hl⟩
  simpa [m, adj_encode] using hpl

theorem clauses_ge_five_on_matching {P L : Type*} [DecidableEq P] [DecidableEq L]
    {k : ℕ} (I : P → L → Prop) [DecidableRel I]
    (p : Fin 3 → P) (l : Fin 3 → L)
    (hp : Function.Injective p) (hl : Function.Injective l)
    (hdiag : ∀ i, I (p i) (l i))
    (hrect : ∀ p p' l l', p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p' l ∧ I p l' ∧ I p' l'))
    (cp : Fin k → Finset P) (cl : Fin k → Finset L)
    (hmatching : ∀ j i, p i ∈ cp j ∨ l i ∈ cl j)
    (hclean : ∀ (x : P → Bool) (y : L → Bool),
      (∀ j, (∃ u ∈ cp j, x u = true) ∨ (∃ v ∈ cl j, y v = true)) →
      ∃ u v, I u v ∧ x u = true ∧ y v = true) : 5 ≤ k := by
  classical
  let clauses (j : Fin k) : Finset (Fin 6) :=
    ((Finset.univ.filter fun i => p i ∈ cp j).image (Fin.castAdd 3)) ∪
    ((Finset.univ.filter fun i => l i ∈ cl j).image (Fin.natAdd 3))
  apply clauses_ge_five_relation (fun i j => I (p i) (l j)) hdiag ?_ clauses ?_ ?_
  · intro i i' j j' hi hj
    exact hrect _ _ _ _ (hp.ne hi) (hl.ne hj)
  · intro j i
    rcases hmatching j i with hpi | hli
    · left
      exact Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpi⟩, rfl⟩)
    · right
      exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hli⟩, rfl⟩)
  · intro x hx
    let xp : P → Bool := fun u => decide (∃ i : Fin 3, p i = u ∧ x (Fin.castAdd 3 i) = true)
    let yl : L → Bool := fun v => decide (∃ i : Fin 3, l i = v ∧ x (Fin.natAdd 3 i) = true)
    have hall : ∀ j, (∃ u ∈ cp j, xp u = true) ∨ (∃ v ∈ cl j, yl v = true) := by
      intro j
      obtain ⟨v, hv, hxv⟩ := hx j
      rcases Finset.mem_union.mp hv with hpoint | hline
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hpoint
        refine Or.inl ⟨p i, (Finset.mem_filter.mp hi).2, ?_⟩
        simp only [xp, decide_eq_true_eq]
        exact ⟨i, rfl, hxv⟩
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hline
        refine Or.inr ⟨l i, (Finset.mem_filter.mp hi).2, ?_⟩
        simp only [yl, decide_eq_true_eq]
        exact ⟨i, rfl, hxv⟩
    obtain ⟨u, v, huv, hxp, hyl⟩ := hclean xp yl hall
    have hxp' : ∃ i : Fin 3, p i = u ∧ x (Fin.castAdd 3 i) = true := of_decide_eq_true hxp
    have hyl' : ∃ i : Fin 3, l i = v ∧ x (Fin.natAdd 3 i) = true := of_decide_eq_true hyl
    obtain ⟨i, rfl, hix⟩ := hxp'
    obtain ⟨j, rfl, hjx⟩ := hyl'
    exact ⟨i, j, huv, hix, hjx⟩

end PEqualNP.Outside.L_meta_2583_aux.FourClause
