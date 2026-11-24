import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.Tauto

namespace PEqualNP.Outside.L_meta_3821_aux

def edgeFn (x : Fin 10 → Bool) : Bool :=
  (List.finRange 5).any fun i =>
    (x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i + 1))) ||
    (x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i)) ||
    (x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i + 2)))

def edges : List (Fin 10 × Fin 10) :=
  [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),
    (3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]

set_option maxHeartbeats 2000000 in
lemma edgeFn_true (x : Fin 10 → Bool) :
    edgeFn x = true ↔ ∃ e ∈ edges, x e.1 = true ∧ x e.2 = true := by
  change (((x 0 && x 1) || (x 0 && x 5) || (x 5 && x 7)) ||
    (((x 1 && x 2) || (x 1 && x 6) || (x 6 && x 8)) ||
    (((x 2 && x 3) || (x 2 && x 7) || (x 7 && x 9)) ||
    (((x 3 && x 4) || (x 3 && x 8) || (x 8 && x 5)) ||
    (((x 4 && x 0) || (x 4 && x 9) || (x 9 && x 6)) || false))))) = true ↔ _
  simp only [edges, List.mem_cons, List.not_mem_nil, or_false,
    or_and_right, exists_or, exists_eq_left, Bool.or_eq_true, Bool.and_eq_true,
    Bool.false_eq_true]
  apply Iff.of_eq
  ac_rfl

def singleton (i : Fin 10) : Fin 10 → Bool := fun k => decide (k = i)

def pair (i j : Fin 10) : Fin 10 → Bool := fun k => decide (k = i ∨ k = j)

def Adj (i j : Fin 10) : Prop := (i, j) ∈ edges ∨ (j, i) ∈ edges

def PartialCorrect (U : (Fin 10 → Bool) → Bool) : Prop :=
  ∀ x, edgeFn x = false ∨ (List.ofFn x).count true ≤ 2 → U x = edgeFn x

def Essential (U : (Fin 10 → Bool) → Bool) (i : Fin 10) : Prop :=
  ∃ x y, (∀ k, k ≠ i → x k = y k) ∧ U x ≠ U y

lemma singleton_false : ∀ i, edgeFn (singleton i) = false := by decide

lemma pair_count : ∀ i j, (List.ofFn (pair i j)).count true ≤ 2 := by decide

lemma pair_edge : ∀ i j, edgeFn (pair i j) = true ↔ Adj i j := by
  unfold Adj
  decide

lemma neighbor_exists : ∀ i : Fin 10, ∃ j, i ≠ j ∧ Adj i j := by
  unfold Adj
  decide

set_option synthInstance.maxSize 1000 in
lemma private_neighbors : ∀ i j : Fin 10, i ≠ j →
    ∃ a b, a ≠ i ∧ a ≠ j ∧ b ≠ i ∧ b ≠ j ∧
      Adj i a ∧ ¬ Adj j a ∧ Adj j b ∧ ¬ Adj i b := by
  unfold Adj
  decide

set_option synthInstance.maxSize 1000 in
lemma neighbor_avoiding : ∀ r i : Fin 10, ∃ j, j ≠ r ∧ Adj i j := by
  unfold Adj
  decide

lemma partial_singleton {U : (Fin 10 → Bool) → Bool} (h : PartialCorrect U)
    (i : Fin 10) : U (singleton i) = false :=
  (h _ (Or.inl (singleton_false i))).trans (singleton_false i)

lemma partial_pair {U : (Fin 10 → Bool) → Bool} (h : PartialCorrect U)
    (i j : Fin 10) : U (pair i j) = edgeFn (pair i j) :=
  h _ (Or.inr (pair_count i j))

lemma partial_essential {U : (Fin 10 → Bool) → Bool} (h : PartialCorrect U)
    (i : Fin 10) : Essential U i := by
  obtain ⟨j, _, hij⟩ := neighbor_exists i
  refine ⟨singleton j, pair i j, ?_, ?_⟩
  · intro k hk
    simp [singleton, pair, hk]
  · rw [partial_singleton h, partial_pair h, (pair_edge i j).mpr hij]
    decide

lemma partial_essential_with_zero {U : (Fin 10 → Bool) → Bool} (h : PartialCorrect U)
    (r i : Fin 10) (hir : i ≠ r) :
    ∃ x y, x r = false ∧ y r = false ∧
      (∀ k, k ≠ i → x k = y k) ∧ U x ≠ U y := by
  obtain ⟨j, hjr, hij⟩ := neighbor_avoiding r i
  refine ⟨singleton j, pair i j, ?_, ?_, ?_, ?_⟩
  · simp [singleton, Ne.symm hjr]
  · simp [pair, Ne.symm hir, Ne.symm hjr]
  · intro k hk
    simp [singleton, pair, hk]
  · rw [partial_singleton h, partial_pair h, (pair_edge i j).mpr hij]
    decide

lemma partial_or_off {A B : (Fin 10 → Bool) → Bool}
    (h : PartialCorrect fun x => A x || B x) (x : Fin 10 → Bool)
    (hx : edgeFn x = false) : A x = false ∧ B x = false := by
  have hh := (h x (Or.inl hx)).trans hx
  exact Bool.or_eq_false_iff.mp hh

lemma partial_or_edge {A B : (Fin 10 → Bool) → Bool}
    (h : PartialCorrect fun x => A x || B x) (i j : Fin 10) (hij : Adj i j) :
    A (pair i j) = true ∨ B (pair i j) = true := by
  have hh := (partial_pair h i j).trans ((pair_edge i j).mpr hij)
  simpa only [Bool.or_eq_true] using hh

lemma partial_or_wire_essential {A B : (Fin 10 → Bool) → Bool}
    (h : PartialCorrect fun x => A x || B x) (i j : Fin 10)
    (ha : A (pair i j) = true) : Essential A i := by
  refine ⟨singleton j, pair i j, ?_, ?_⟩
  · intro k hk
    simp [singleton, pair, hk]
  · rw [(partial_or_off h _ (singleton_false j)).1, ha]
    decide

def symmetryTable (i j : Fin 10) : Fin 10 :=
  (([[9,6,8,3,4,7,1,5,2,0],
    [4,9,7,5,0,3,6,2,8,1],
    [0,4,9,6,1,5,3,7,8,2],
    [0,1,6,9,4,5,2,8,7,3],
    [6,1,2,7,9,8,0,3,5,4],
    [4,3,2,1,0,9,8,7,6,5],
    [0,4,3,2,1,5,9,8,7,6],
    [0,1,6,8,5,4,2,9,3,7],
    [0,1,2,7,5,4,6,3,9,8],
    [0,1,2,3,4,5,6,7,8,9]] : List (List (Fin 10))).getD i []).getD j 0

lemma symmetry_involutive : ∀ i, Function.Involutive (symmetryTable i) := by
  unfold Function.Involutive
  decide

lemma symmetry_last : ∀ i, symmetryTable i i = 9 := by decide

lemma symmetry_edges : ∀ i e, e ∈ edges →
    (symmetryTable i e.1, symmetryTable i e.2) ∈ edges ∨
    (symmetryTable i e.2, symmetryTable i e.1) ∈ edges := by decide

def symmetry (i : Fin 10) : Equiv.Perm (Fin 10) :=
  ⟨symmetryTable i, symmetryTable i, symmetry_involutive i, symmetry_involutive i⟩

lemma symmetry_preserves (i : Fin 10) (x : Fin 10 → Bool) :
    edgeFn (x ∘ symmetry i) = edgeFn x := by
  apply Bool.eq_iff_iff.mpr
  rw [edgeFn_true, edgeFn_true]
  constructor
  · rintro ⟨e, he, hx, hy⟩
    rcases symmetry_edges i e he with hforward | hreverse
    · exact ⟨_, hforward, hx, hy⟩
    · exact ⟨_, hreverse, hy, hx⟩
  · rintro ⟨e, he, hx, hy⟩
    rcases symmetry_edges i e he with hforward | hreverse
    · refine ⟨_, hforward, ?_, ?_⟩
      · change x (symmetryTable i (symmetryTable i e.1)) = true
        rw [symmetry_involutive]
        exact hx
      · change x (symmetryTable i (symmetryTable i e.2)) = true
        rw [symmetry_involutive]
        exact hy
    · refine ⟨_, hreverse, ?_, ?_⟩
      · change x (symmetryTable i (symmetryTable i e.2)) = true
        rw [symmetry_involutive]
        exact hy
      · change x (symmetryTable i (symmetryTable i e.1)) = true
        rw [symmetry_involutive]
        exact hx

lemma symmetry_sends_to_last (i : Fin 10) : symmetry i i = Fin.last 9 :=
  symmetry_last i

lemma automorphism_to_last (i : Fin 10) : ∃ s : Equiv.Perm (Fin 10),
    s i = Fin.last 9 ∧ ∀ x : Fin 10 → Bool, edgeFn (x ∘ s) = edgeFn x :=
  ⟨symmetry i, symmetry_sends_to_last i, symmetry_preserves i⟩


def cpSingle {α : Type} [DecidableEq α] (a : α) : α → Bool :=
  fun i => decide (i = a)

def cpPair {α : Type} [DecidableEq α] (a b : α) : α → Bool :=
  fun i => decide (i = a ∨ i = b)

def cpNoCompression {α : Type} [DecidableEq α]
    (U : (α → Bool) → Bool) (p q : α) : Prop :=
  ∀ code : Bool → Bool → Bool, ∃ x y : α → Bool,
    (∀ i, i ≠ p → i ≠ q → x i = y i) ∧
    code (x p) (x q) = code (y p) (y q) ∧ U x ≠ U y

def cpNoCompressionAtZero {α : Type} [DecidableEq α]
    (U : (α → Bool) → Bool) (r p q : α) : Prop :=
  ∀ code : Bool → Bool → Bool, ∃ x y : α → Bool,
    x r = false ∧ y r = false ∧
    (∀ i, i ≠ p → i ≠ q → x i = y i) ∧
    code (x p) (x q) = code (y p) (y q) ∧ U x ≠ U y

lemma cp_three_pattern_collision (code : Bool → Bool → Bool) :
    code false false = code true false ∨
    code false false = code false true ∨
    code true false = code false true := by
  cases h0 : code false false <;>
    cases h1 : code true false <;>
    cases h2 : code false true <;> simp_all

lemma cp_noCompression_of_five_rows {α : Type} [DecidableEq α]
    (U : (α → Bool) → Bool) (p q a b : α)
    (hpq : p ≠ q) (hap : a ≠ p) (haq : a ≠ q)
    (hbp : b ≠ p) (hbq : b ≠ q)
    (ha0 : U (cpSingle a) = false)
    (hap1 : U (cpPair a p) = true)
    (haq0 : U (cpPair a q) = false)
    (hb0 : U (cpSingle b) = false)
    (hbq1 : U (cpPair b q) = true) : cpNoCompression U p q := by
  intro code
  rcases cp_three_pattern_collision code with h | h | h
  · refine ⟨cpSingle a, cpPair a p, ?_, ?_, ?_⟩
    · intro i hip hiq
      simp [cpSingle, cpPair, hip]
    · simpa [cpSingle, cpPair, Ne.symm hap, Ne.symm haq, Ne.symm hpq] using h
    · simp [ha0, hap1]
  · refine ⟨cpSingle b, cpPair b q, ?_, ?_, ?_⟩
    · intro i hip hiq
      simp [cpSingle, cpPair, hiq]
    · simpa [cpSingle, cpPair, Ne.symm hbp, Ne.symm hbq, hpq] using h
    · simp [hb0, hbq1]
  · refine ⟨cpPair a p, cpPair a q, ?_, ?_, ?_⟩
    · intro i hip hiq
      simp [cpPair, hip, hiq]
    · simpa [cpPair, Ne.symm hap, Ne.symm haq, hpq, Ne.symm hpq] using h
    · simp [hap1, haq0]

lemma cp_noCompressionAtZero_of_five_rows {α : Type} [DecidableEq α]
    (U : (α → Bool) → Bool) (r p q a b : α)
    (hpq : p ≠ q) (hap : a ≠ p) (haq : a ≠ q)
    (hbp : b ≠ p) (hbq : b ≠ q)
    (hpr : p ≠ r) (hqr : q ≠ r) (har : a ≠ r) (hbr : b ≠ r)
    (ha0 : U (cpSingle a) = false)
    (hap1 : U (cpPair a p) = true)
    (haq0 : U (cpPair a q) = false)
    (hb0 : U (cpSingle b) = false)
    (hbq1 : U (cpPair b q) = true) : cpNoCompressionAtZero U r p q := by
  intro code
  rcases cp_three_pattern_collision code with h | h | h
  · refine ⟨cpSingle a, cpPair a p, ?_, ?_, ?_, ?_, ?_⟩
    · simp [cpSingle, Ne.symm har]
    · simp [cpPair, Ne.symm har, Ne.symm hpr]
    · intro i hip hiq
      simp [cpSingle, cpPair, hip]
    · simpa [cpSingle, cpPair, Ne.symm hap, Ne.symm haq, Ne.symm hpq] using h
    · simp [ha0, hap1]
  · refine ⟨cpSingle b, cpPair b q, ?_, ?_, ?_, ?_, ?_⟩
    · simp [cpSingle, Ne.symm hbr]
    · simp [cpPair, Ne.symm hbr, Ne.symm hqr]
    · intro i hip hiq
      simp [cpSingle, cpPair, hiq]
    · simpa [cpSingle, cpPair, Ne.symm hbp, Ne.symm hbq, hpq] using h
    · simp [hb0, hbq1]
  · refine ⟨cpPair a p, cpPair a q, ?_, ?_, ?_, ?_, ?_⟩
    · simp [cpPair, Ne.symm har, Ne.symm hpr]
    · simp [cpPair, Ne.symm har, Ne.symm hqr]
    · intro i hip hiq
      simp [cpPair, hip, hiq]
    · simpa [cpPair, Ne.symm hap, Ne.symm haq, hpq, Ne.symm hpq] using h
    · simp [hap1, haq0]

def cpEdge (x : Fin 10 → Bool) : Bool :=
  (List.finRange 5).any fun i : Fin 5 =>
    x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i + 1)) ||
    x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i) ||
    x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i + 2))

lemma cp_single_zero : ∀ a : Fin 10, cpEdge (cpSingle a) = false := by
  decide

lemma cp_pair_count : ∀ a b : Fin 10, (List.ofFn (cpPair a b)).count true ≤ 2 := by
  decide

lemma cp_private_neighbor : ∀ p q : Fin 10, p ≠ q →
    ∃ a : Fin 10, a ≠ p ∧ a ≠ q ∧
      cpEdge (cpPair a p) = true ∧ cpEdge (cpPair a q) = false := by
  decide

lemma cp_private_neighbor_avoid : ∀ p q r : Fin 10, p ≠ q →
    ∃ a : Fin 10, a ≠ p ∧ a ≠ q ∧ a ≠ r ∧
      cpEdge (cpPair a p) = true ∧ cpEdge (cpPair a q) = false := by
  decide

lemma cp_petersen_noCompression (U : (Fin 10 → Bool) → Bool)
    (hU : ∀ x, cpEdge x = false ∨ (List.ofFn x).count true ≤ 2 → U x = cpEdge x)
    (p q : Fin 10) (hpq : p ≠ q) : cpNoCompression U p q := by
  obtain ⟨a, hap, haq, hap1, haq0⟩ := cp_private_neighbor p q hpq
  obtain ⟨b, hbq, hbp, hbq1, _⟩ := cp_private_neighbor q p (Ne.symm hpq)
  have hsingle (v : Fin 10) : U (cpSingle v) = false :=
    (hU _ (Or.inl (cp_single_zero v))).trans (cp_single_zero v)
  have hpair (v w : Fin 10) : U (cpPair v w) = cpEdge (cpPair v w) :=
    hU _ (Or.inr (cp_pair_count v w))
  exact cp_noCompression_of_five_rows U p q a b hpq hap haq hbp hbq
    (hsingle a) ((hpair a p).trans hap1) ((hpair a q).trans haq0)
    (hsingle b) ((hpair b q).trans hbq1)

lemma cp_petersen_noCompression_of_pairs (U : (Fin 10 → Bool) → Bool)
    (hsingle : ∀ a : Fin 10, U (cpSingle a) = false)
    (hpair : ∀ a b : Fin 10, U (cpPair a b) = cpEdge (cpPair a b))
    (p q : Fin 10) (hpq : p ≠ q) : cpNoCompression U p q := by
  obtain ⟨a, hap, haq, hap1, haq0⟩ := cp_private_neighbor p q hpq
  obtain ⟨b, hbq, hbp, hbq1, _⟩ := cp_private_neighbor q p (Ne.symm hpq)
  exact cp_noCompression_of_five_rows U p q a b hpq hap haq hbp hbq
    (hsingle a) ((hpair a p).trans hap1) ((hpair a q).trans haq0)
    (hsingle b) ((hpair b q).trans hbq1)

lemma cp_petersen_noCompressionAtZero (U : (Fin 10 → Bool) → Bool)
    (hU : ∀ x, cpEdge x = false ∨ (List.ofFn x).count true ≤ 2 → U x = cpEdge x)
    (r p q : Fin 10) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    cpNoCompressionAtZero U r p q := by
  obtain ⟨a, hap, haq, har, hap1, haq0⟩ := cp_private_neighbor_avoid p q r hpq
  obtain ⟨b, hbq, hbp, hbr, hbq1, _⟩ := cp_private_neighbor_avoid q p r (Ne.symm hpq)
  have hsingle (v : Fin 10) : U (cpSingle v) = false :=
    (hU _ (Or.inl (cp_single_zero v))).trans (cp_single_zero v)
  have hpair (v w : Fin 10) : U (cpPair v w) = cpEdge (cpPair v w) :=
    hU _ (Or.inr (cp_pair_count v w))
  exact cp_noCompressionAtZero_of_five_rows U r p q a b hpq hap haq hbp hbq
    hpr hqr har hbr (hsingle a) ((hpair a p).trans hap1) ((hpair a q).trans haq0)
    (hsingle b) ((hpair b q).trans hbq1)



def maskRow (n : ℕ) (i : Fin 10) : Bool := n.testBit i.val

def maximalMasks : List ℕ :=
  [50,69,104,116,138,201,208,276,385,402,521,548,554,770,773]

lemma maximal_masks_negative : ∀ n ∈ maximalMasks, edgeFn (maskRow n) = false := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
lemma independent_below_maximal : ∀ x : Fin 10 → Bool, edgeFn x = false →
    ∃ n ∈ maximalMasks, ∀ i, x i = true → maskRow n i = true := by
  decide +kernel

def BooleanMonotone (U : (Fin 10 → Bool) → Bool) : Prop :=
  ∀ x y, (∀ i, x i = true → y i = true) → U x = true → U y = true

lemma monotone_thirty_rows (U : (Fin 10 → Bool) → Bool) (hm : BooleanMonotone U)
    (negative : ∀ n ∈ maximalMasks, U (maskRow n) = false)
    (positive : ∀ e ∈ edges, U (pair e.1 e.2) = true) :
    ∀ x, U x = edgeFn x := by
  intro x
  cases hx : edgeFn x with
  | false =>
    obtain ⟨n, hn, hxn⟩ := independent_below_maximal x hx
    cases hu : U x with
    | false => rfl
    | true =>
      have hh := hm x (maskRow n) hxn hu
      rw [negative n hn] at hh
      contradiction
  | true =>
    obtain ⟨e, he, hi, hj⟩ := (edgeFn_true x).mp hx
    apply hm (pair e.1 e.2) x _ (positive e he)
    intro i hpair
    simp only [pair, decide_eq_true_eq] at hpair
    rcases hpair with rfl | rfl
    · exact hi
    · exact hj



def orbitTable (i j : Fin 10) : Fin 10 :=
  (([[0,1,2,3,4,5,6,7,8,9],
    [1,0,5,8,6,2,4,7,3,9],
    [2,1,0,5,7,3,6,4,8,9],
    [3,2,1,0,4,8,7,6,5,9],
    [0,1,2,3,4,5,6,7,8,9],
    [5,8,3,2,7,0,6,4,1,9],
    [1,0,5,8,6,2,4,7,3,9],
    [2,1,0,5,7,3,6,4,8,9],
    [8,3,2,1,6,5,4,7,0,9],
    [0,1,2,3,4,5,6,7,8,9]] : List (List (Fin 10))).getD i []).getD j 0

lemma orbit_involutive : ∀ i, Function.Involutive (orbitTable i) := by
  unfold Function.Involutive
  decide

lemma orbit_fixes_last : ∀ i, orbitTable i 9 = 9 := by decide

lemma orbit_target : ∀ i : Fin 10, i ≠ 9 →
    orbitTable i i = if edgeFn (pair 9 i) then 4 else 0 := by decide

lemma orbit_edges : ∀ i e, e ∈ edges →
    (orbitTable i e.1, orbitTable i e.2) ∈ edges ∨
    (orbitTable i e.2, orbitTable i e.1) ∈ edges := by decide

def orbitSymmetry (i : Fin 10) : Equiv.Perm (Fin 10) :=
  ⟨orbitTable i, orbitTable i, orbit_involutive i, orbit_involutive i⟩

lemma orbit_preserves (i : Fin 10) (x : Fin 10 → Bool) :
    edgeFn (x ∘ orbitSymmetry i) = edgeFn x := by
  apply Bool.eq_iff_iff.mpr
  rw [edgeFn_true, edgeFn_true]
  constructor
  · rintro ⟨e, he, hx, hy⟩
    rcases orbit_edges i e he with hforward | hreverse
    · exact ⟨_, hforward, hx, hy⟩
    · exact ⟨_, hreverse, hy, hx⟩
  · rintro ⟨e, he, hx, hy⟩
    rcases orbit_edges i e he with hforward | hreverse
    · refine ⟨_, hforward, ?_, ?_⟩
      · change x (orbitTable i (orbitTable i e.1)) = true
        rw [orbit_involutive]
        exact hx
      · change x (orbitTable i (orbitTable i e.2)) = true
        rw [orbit_involutive]
        exact hy
    · refine ⟨_, hreverse, ?_, ?_⟩
      · change x (orbitTable i (orbitTable i e.2)) = true
        rw [orbit_involutive]
        exact hy
      · change x (orbitTable i (orbitTable i e.1)) = true
        rw [orbit_involutive]
        exact hx

lemma orbit_first_symmetry_edge : ∀ p q : Fin 10,
    edgeFn (pair 9 (symmetryTable p q)) = edgeFn (pair p q) := by decide

def pairSymmetry (p q : Fin 10) : Equiv.Perm (Fin 10) :=
  (symmetry p).trans (orbitSymmetry (symmetry p q))

lemma pairSymmetry_preserves (p q : Fin 10) (x : Fin 10 → Bool) :
    edgeFn (x ∘ pairSymmetry p q) = edgeFn x := by
  change edgeFn ((x ∘ orbitSymmetry (symmetry p q)) ∘ symmetry p) = edgeFn x
  rw [symmetry_preserves, orbit_preserves]

lemma pairSymmetry_first (p q : Fin 10) : pairSymmetry p q p = 9 := by
  change orbitTable (symmetry p q) (symmetryTable p p) = 9
  rw [symmetry_last, orbit_fixes_last]

lemma pairSymmetry_second (p q : Fin 10) (hpq : p ≠ q) :
    pairSymmetry p q q = if edgeFn (pair p q) then 4 else 0 := by
  have hq : symmetry p q ≠ 9 := by
    intro h
    have heq : symmetry p q = symmetry p p := h.trans (symmetry_last p).symm
    exact hpq ((symmetry p).injective heq).symm
  change orbitTable (symmetry p q) (symmetry p q) = _
  rw [orbit_target _ hq]
  change (if edgeFn (pair 9 (symmetryTable p q)) then 4 else 0) = _
  rw [orbit_first_symmetry_edge]

lemma automorphism_ordered_pair (p q : Fin 10) (hpq : p ≠ q) :
    ∃ s : Equiv.Perm (Fin 10),
      (∀ x : Fin 10 → Bool, edgeFn (x ∘ s) = edgeFn x) ∧
      s p = 9 ∧ s q = if edgeFn (pair p q) then 4 else 0 := by
  exact ⟨pairSymmetry p q, pairSymmetry_preserves p q,
    pairSymmetry_first p q, pairSymmetry_second p q hpq⟩

lemma automorphism_ordered_pair_adjacent (p q : Fin 10) (hpq : p ≠ q) :
    ∃ s : Equiv.Perm (Fin 10),
      (∀ x : Fin 10 → Bool, edgeFn (x ∘ s) = edgeFn x) ∧
      s p = 9 ∧ (Adj p q → s q = 4) ∧ (¬ Adj p q → s q = 0) := by
  obtain ⟨s, hs, hp, hq⟩ := automorphism_ordered_pair p q hpq
  refine ⟨s, hs, hp, ?_, ?_⟩
  · intro hadj
    simpa [(pair_edge p q).mpr hadj] using hq
  · intro hnadj
    have hoff : edgeFn (pair p q) = false := by
      cases h : edgeFn (pair p q)
      · rfl
      · exact False.elim (hnadj ((pair_edge p q).mp h))
    simpa [hoff] using hq



def kwNeighbor (v : Fin 10) (j : Fin 3) : Fin 10 :=
  (([[1,4,5],
    [0,2,6],
    [1,3,7],
    [2,4,8],
    [0,3,9],
    [0,7,8],
    [1,8,9],
    [2,5,9],
    [3,5,6],
    [4,6,7]] : List (List (Fin 10))).getD v []).getD j 0

def kwNegativeMask (v : Fin 10) (i : Fin 3) : ℕ :=
  (([[116,554,402],
    [116,201,773],
    [201,402,554],
    [402,773,116],
    [554,773,201],
    [402,773,201],
    [773,554,402],
    [554,773,116],
    [116,201,554],
    [201,402,116]] : List (List ℕ)).getD v []).getD i 0

lemma kw_negative : ∀ v i, edgeFn (maskRow (kwNegativeMask v i)) = false := by decide

lemma kw_center_absent : ∀ v i, maskRow (kwNegativeMask v i) v = false := by decide

lemma kw_positive : ∀ v j, edgeFn (pair v (kwNeighbor v j)) = true := by decide

lemma kw_neighbor_injective : ∀ v, Function.Injective (kwNeighbor v) := by
  unfold Function.Injective
  decide

lemma kw_masks_injective : ∀ v, Function.Injective (kwNegativeMask v) := by
  unfold Function.Injective
  decide

lemma kw_neighbor_symmetric : ∀ v i, ∃ j, kwNeighbor (kwNeighbor v i) j = v := by decide

lemma kw_mask_weight : ∀ v i,
    (List.ofFn (maskRow (kwNegativeMask v i))).count true = 4 := by decide

lemma kw_neighbor_incidence : ∀ v i j,
    maskRow (kwNegativeMask v i) (kwNeighbor v j) = decide (i ≠ j) := by decide

lemma kw_only_difference : ∀ (v : Fin 10) (i j : Fin 3) (k : Fin 10),
    pair v (kwNeighbor v j) k = true → maskRow (kwNegativeMask v i) k = false →
      k = v ∨ (i = j ∧ k = kwNeighbor v j) := by decide

lemma kw_opposite_diagonal : ∀ (u v : Fin 10) (i j : Fin 3),
    kwNeighbor u i = v → kwNeighbor v j = u →
      kwNegativeMask u i = kwNegativeMask v j := by decide


end PEqualNP.Outside.L_meta_3821_aux
