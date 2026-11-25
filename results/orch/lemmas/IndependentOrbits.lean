import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2373.IndependentOrbits

def adjacent (a b : Fin 10) : Bool :=
  ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] : List (Fin 10 × Fin 10)).any
    (fun e => (a == e.1 && b == e.2) || (a == e.2 && b == e.1))

abbrev independent (I : Finset (Fin 10)) : Prop := ∀ a ∈ I, ∀ b ∈ I, adjacent a b = false

def representative : Fin 6 → Finset (Fin 10) := ![{}, {0}, {0, 2}, {1, 3, 5}, {1, 4, 5}, {2, 4, 5, 6}]
def knownSet : Fin 76 → Finset (Fin 10) := ![{}, {0}, {1}, {2}, {0, 2}, {3}, {0, 3}, {1, 3}, {4}, {1, 4}, {2, 4}, {5}, {1, 5}, {2, 5}, {3, 5}, {1, 3, 5}, {4, 5}, {1, 4, 5}, {2, 4, 5}, {6}, {0, 6}, {2, 6}, {0, 2, 6}, {3, 6}, {0, 3, 6}, {4, 6}, {2, 4, 6}, {5, 6}, {2, 5, 6}, {3, 5, 6}, {4, 5, 6}, {2, 4, 5, 6}, {7}, {0, 7}, {1, 7}, {3, 7}, {0, 3, 7}, {1, 3, 7}, {4, 7}, {1, 4, 7}, {6, 7}, {0, 6, 7}, {3, 6, 7}, {0, 3, 6, 7}, {4, 6, 7}, {8}, {0, 8}, {1, 8}, {2, 8}, {0, 2, 8}, {4, 8}, {1, 4, 8}, {2, 4, 8}, {7, 8}, {0, 7, 8}, {1, 7, 8}, {4, 7, 8}, {1, 4, 7, 8}, {9}, {0, 9}, {1, 9}, {2, 9}, {0, 2, 9}, {3, 9}, {0, 3, 9}, {1, 3, 9}, {5, 9}, {1, 5, 9}, {2, 5, 9}, {3, 5, 9}, {1, 3, 5, 9}, {8, 9}, {0, 8, 9}, {1, 8, 9}, {2, 8, 9}, {0, 2, 8, 9}]
def classOf : Fin 76 → Fin 6 := ![0, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 2, 3, 2, 4, 3, 1, 2, 2, 4, 2, 3, 2, 3, 2, 3, 4, 3, 5, 1, 2, 2, 2, 3, 4, 2, 3, 2, 3, 3, 5, 4, 1, 2, 2, 2, 3, 2, 3, 4, 2, 4, 3, 3, 5, 1, 2, 2, 2, 3, 2, 4, 3, 2, 3, 4, 3, 5, 2, 3, 4, 3, 5]
def permutationTable : Fin 51 → Fin 10 → Fin 10 := ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9], ![1, 0, 4, 3, 2, 6, 5, 9, 8, 7], ![2, 1, 0, 4, 3, 7, 6, 5, 9, 8], ![2, 3, 4, 0, 1, 7, 8, 9, 5, 6], ![0, 4, 3, 2, 1, 5, 9, 8, 7, 6], ![3, 2, 1, 0, 4, 8, 7, 6, 5, 9], ![1, 2, 3, 4, 0, 6, 7, 8, 9, 5], ![3, 4, 0, 1, 2, 8, 9, 5, 6, 7], ![1, 2, 3, 8, 6, 0, 7, 4, 5, 9], ![1, 0, 4, 9, 6, 2, 5, 3, 7, 8], ![3, 4, 0, 5, 8, 2, 9, 1, 7, 6], ![3, 8, 5, 0, 4, 2, 6, 7, 1, 9], ![1, 6, 8, 3, 2, 0, 9, 5, 4, 7], ![2, 1, 6, 8, 3, 7, 0, 9, 5, 4], ![0, 1, 6, 8, 5, 4, 2, 9, 3, 7], ![6, 1, 0, 4, 9, 8, 2, 5, 3, 7], ![8, 3, 4, 0, 5, 6, 2, 9, 1, 7], ![3, 4, 9, 7, 2, 8, 0, 6, 5, 1], ![4, 0, 1, 2, 3, 9, 5, 6, 7, 8], ![3, 4, 9, 6, 8, 2, 0, 7, 1, 5], ![4, 0, 1, 6, 9, 3, 5, 2, 8, 7], ![2, 3, 8, 5, 7, 1, 4, 6, 0, 9], ![0, 4, 9, 6, 1, 5, 3, 7, 8, 2], ![2, 3, 4, 9, 7, 1, 8, 0, 6, 5], ![0, 4, 3, 8, 5, 1, 9, 2, 6, 7], ![3, 2, 1, 6, 8, 4, 7, 0, 9, 5], ![8, 6, 1, 0, 5, 3, 9, 2, 4, 7], ![3, 8, 5, 7, 2, 4, 6, 0, 9, 1], ![0, 1, 2, 7, 5, 4, 6, 3, 9, 8], ![8, 3, 4, 9, 6, 5, 2, 0, 7, 1], ![9, 4, 0, 1, 6, 7, 3, 5, 2, 8], ![2, 3, 8, 6, 1, 7, 4, 5, 9, 0], ![0, 4, 9, 7, 5, 1, 3, 6, 2, 8], ![3, 2, 7, 5, 8, 4, 1, 9, 0, 6], ![8, 3, 2, 1, 6, 5, 4, 7, 0, 9], ![1, 0, 5, 8, 6, 2, 4, 7, 3, 9], ![3, 8, 6, 1, 2, 4, 5, 9, 0, 7], ![6, 8, 3, 4, 9, 1, 5, 2, 0, 7], ![4, 3, 2, 7, 9, 0, 8, 1, 5, 6], ![4, 9, 6, 8, 3, 0, 7, 1, 5, 2], ![3, 2, 7, 9, 4, 8, 1, 5, 6, 0], ![8, 3, 2, 7, 5, 6, 4, 1, 9, 0], ![1, 0, 5, 7, 2, 6, 4, 8, 9, 3], ![6, 8, 3, 2, 1, 9, 5, 4, 7, 0], ![4, 3, 2, 1, 0, 9, 8, 7, 6, 5], ![3, 8, 6, 9, 4, 2, 5, 1, 7, 0], ![0, 1, 6, 9, 4, 5, 2, 8, 7, 3], ![4, 9, 6, 1, 0, 3, 7, 8, 2, 5], ![8, 6, 9, 4, 3, 5, 1, 7, 0, 2], ![1, 6, 9, 4, 0, 2, 8, 7, 3, 5], ![9, 4, 3, 2, 7, 6, 0, 8, 1, 5]]
def permutationIndex : Fin 76 → Fin 51 := ![0, 0, 1, 2, 0, 3, 4, 5, 6, 1, 7, 8, 9, 10, 11, 0, 12, 0, 4, 13, 14, 15, 1, 16, 1, 17, 18, 19, 20, 21, 22, 0, 23, 24, 25, 26, 12, 2, 27, 28, 29, 9, 30, 2, 31, 21, 32, 33, 34, 35, 36, 14, 3, 37, 8, 38, 39, 24, 31, 22, 40, 41, 42, 43, 6, 44, 45, 46, 23, 47, 4, 48, 49, 13, 50, 13]
def permutation (i : Fin 76) : Fin 10 → Fin 10 := permutationTable (permutationIndex i)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma coverage : ∀ I : Finset (Fin 10), independent I → ∃ i : Fin 76, knownSet i = I := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma witness_facts : ∀ i : Fin 76,
    Function.Bijective (permutation i) ∧
    (∀ a b, adjacent (permutation i a) (permutation i b) = adjacent a b) ∧
    (knownSet i).image (permutation i) = representative (classOf i) := by
  intro i
  fin_cases i <;> decide +kernel

lemma canonicalize (I : Finset (Fin 10)) (h : independent I) :
    ∃ (k : Fin 6) (f : Fin 10 → Fin 10), Function.Bijective f ∧
      (∀ a b, adjacent (f a) (f b) = adjacent a b) ∧
      I.image f = representative k := by
  obtain ⟨i, rfl⟩ := coverage I h
  exact ⟨classOf i, permutation i, witness_facts i⟩

lemma nonempty_canonicalize (I : Finset (Fin 10)) (h : independent I) (hne : I.Nonempty) :
    ∃ (k : Fin 5) (f : Fin 10 → Fin 10), Function.Bijective f ∧
      (∀ a b, adjacent (f a) (f b) = adjacent a b) ∧
      I.image f = representative k.succ := by
  obtain ⟨k, f, hf, ha, hi⟩ := canonicalize I h
  cases k using Fin.cases with
  | zero =>
    obtain ⟨v, hv⟩ := hne
    have member := Finset.mem_image_of_mem f hv
    rw [hi] at member
    simp [representative] at member
  | succ k => exact ⟨k, f, hf, ha, hi⟩

lemma empty_representative : representative 0 = ∅ := rfl

end PEqualNP.Outside.L_meta_2373.IndependentOrbits
