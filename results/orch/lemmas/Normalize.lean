import Lean

namespace PEqualNP.Outside.L_meta_5112_aux

def gateStep (xs : List Nat) (g : Bool × Nat × Nat) : List Nat :=
  xs ++ [if g.1 = true then xs.getD g.2.1 0 ||| xs.getD g.2.2 0
    else xs.getD g.2.1 0 &&& xs.getD g.2.2 0]

def clipGate (n : Nat) (g : Bool × Nat × Nat) : Bool × Nat × Nat :=
  (g.1, min g.2.1 n, min g.2.2 n)

def clipProgram (n : Nat) : List (Bool × Nat × Nat) → List (Bool × Nat × Nat)
  | [] => []
  | g :: gs => clipGate n g :: clipProgram (n + 1) gs

theorem getD_default (xs : List Nat) (i : Nat) (h : xs.length ≤ i) : xs.getD i 0 = 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem getD_clip (xs : List Nat) (i : Nat) :
    xs.getD (min i xs.length) 0 = xs.getD i 0 := by
  by_cases h : i ≤ xs.length
  · rw [Nat.min_eq_left h]
  · have h' : xs.length ≤ i := by omega
    rw [Nat.min_eq_right h', getD_default _ _ (by omega),
      getD_default _ _ h']

theorem gateStep_clip (xs : List Nat) (g : Bool × Nat × Nat) :
    gateStep xs (clipGate xs.length g) = gateStep xs g := by
  simp only [gateStep, clipGate, getD_clip]

theorem clipProgram_length (n : Nat) (gs : List (Bool × Nat × Nat)) :
    (clipProgram n gs).length = gs.length := by
  induction gs generalizing n with
  | nil => rfl
  | cons g gs ih => simp [clipProgram, ih]

theorem gateStep_length (xs : List Nat) (g : Bool × Nat × Nat) :
    (gateStep xs g).length = xs.length + 1 := by
  simp [gateStep]

theorem eval_clipProgram (xs : List Nat) (gs : List (Bool × Nat × Nat)) :
    (clipProgram xs.length gs).foldl gateStep xs = gs.foldl gateStep xs := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    simp only [clipProgram, List.foldl_cons, gateStep_clip]
    rw [← gateStep_length xs g]
    exact ih _

theorem clipProgram_sources (n : Nat) (gs : List (Bool × Nat × Nat)) :
    ∀ g ∈ clipProgram n gs, g.2.1 < n + gs.length + 1 ∧
      g.2.2 < n + gs.length + 1 := by
  induction gs generalizing n with
  | nil => simp [clipProgram]
  | cons g gs ih =>
    intro a ha
    simp only [clipProgram, List.mem_cons] at ha
    rcases ha with rfl | ha
    · simp only [clipGate, List.length_cons]
      constructor
      · exact Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by omega)
      · exact Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by omega)
    · have h := ih (n + 1) a ha
      simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

end PEqualNP.Outside.L_meta_5112_aux
