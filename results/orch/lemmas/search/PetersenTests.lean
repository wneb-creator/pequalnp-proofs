import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic

namespace PEqualNP.Outside.L_meta_2592_aux

def petersenEdges : List (Fin 10 × Fin 10) :=
  [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7),
   (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)]

def petersenValue (x : Fin 10 → Bool) : Bool :=
  petersenEdges.any (fun e => x e.1 && x e.2)

def petersenIndependentMasks : List ℕ :=
  [69, 521, 385, 138, 50, 770, 276, 548, 104, 208, 773, 201, 554, 402, 116]

def petersenMaskInput (m : ℕ) (i : Fin 10) : Bool :=
  m.testBit i.val

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
lemma petersen_independent_tests :
    ∀ m ∈ petersenIndependentMasks, petersenValue (petersenMaskInput m) = false := by
  decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
lemma petersen_independent_cover :
    ∀ x : Fin 10 → Bool, petersenValue x = false →
      ∃ m ∈ petersenIndependentMasks,
        ∀ i : Fin 10, x i = true → petersenMaskInput m i = true := by
  intro x hx
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;>
    cases h3 : x 3 <;> cases h4 : x 4 <;> cases h5 : x 5 <;>
    cases h6 : x 6 <;> cases h7 : x 7 <;> cases h8 : x 8 <;>
    cases h9 : x 9 <;>
    simp_all [petersenValue, petersenEdges, petersenIndependentMasks,
      petersenMaskInput, Fin.forall_fin_succ] <;> decide

lemma petersen_positive_edge (x : Fin 10 → Bool) :
    petersenValue x = true ↔
      ∃ e ∈ petersenEdges, ∀ i : Fin 10,
        decide (i = e.1 ∨ i = e.2) = true → x i = true := by
  rw [petersenValue, List.any_eq_true]
  constructor
  · rintro ⟨e, he, hleft⟩
    obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp hleft
    refine ⟨e, he, ?_⟩
    intro i hi
    have h : i = e.1 ∨ i = e.2 := by simpa using hi
    rcases h with rfl | rfl
    · exact ha
    · exact hb
  · rintro ⟨e, he, below⟩
    exact ⟨e, he, Bool.and_eq_true_iff.mpr ⟨below e.1 (by simp), below e.2 (by simp)⟩⟩

def petersenIndependentTests : List (Fin 10 → Bool) :=
  petersenIndependentMasks.map petersenMaskInput

lemma petersen_independent_test_cover (x : Fin 10 → Bool)
    (hx : petersenValue x = false) :
    ∃ y ∈ petersenIndependentTests, ∀ i, x i = true → y i = true := by
  obtain ⟨m, hm, below⟩ := petersen_independent_cover x hx
  exact ⟨petersenMaskInput m, List.mem_map.mpr ⟨m, hm, rfl⟩, below⟩

end PEqualNP.Outside.L_meta_2592_aux
