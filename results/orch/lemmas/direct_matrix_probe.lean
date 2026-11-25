import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583_aux.MatrixProbe

def pointWires : List (Fin 16) := (List.finRange 8).map (Fin.castAdd 8)

def lineWires : List (Fin 16) := (List.finRange 8).map (Fin.natAdd 8)

def bitPointWires (b : ℕ) (v : Bool) : List (Fin 16) :=
  ((List.finRange 8).filter (fun i => i.val.testBit b == v)).map (Fin.castAdd 8)

def bitLineWires (b : ℕ) (v : Bool) : List (Fin 16) :=
  ((List.finRange 8).filter (fun i => i.val.testBit b == v)).map (Fin.natAdd 8)

def clauses : List (List (Fin 16)) :=
  [pointWires, lineWires] ++ (List.range 3).flatMap (fun b =>
    [bitPointWires b false ++ bitLineWires b true,
      bitPointWires b true ++ bitLineWires b false])

def value (z : Fin 16 → Bool) : Bool := clauses.all (fun c => c.any z)

def pairInput (p l : Fin 8) : Fin 16 → Bool :=
  fun i => decide (i = Fin.castAdd 8 p ∨ i = Fin.natAdd 8 l)

def witness : Fin 16 → Bool := fun i => decide (i.val ∈ [0, 7, 9, 14])

lemma clause_count : clauses.length = 8 := by decide

lemma clause_lengths : ∀ c ∈ clauses, c.length = 8 := by decide

set_option maxRecDepth 10000 in
lemma pair_matching : ∀ p l : Fin 8, value (pairInput p l) = decide (p = l) := by
  decide

lemma mixed_matrix_eq :
    (fun p l : Fin 8 => if value (pairInput p l) then (1 : ℚ) else 0) =
      (1 : Matrix (Fin 8) (Fin 8) ℚ) := by
  ext p l
  simp [pair_matching, Matrix.one_apply]

lemma mixed_matrix_rank :
    Matrix.rank (fun p l : Fin 8 => if value (pairInput p l) then (1 : ℚ) else 0) = 8 := by
  rw [mixed_matrix_eq, Matrix.rank_one]
  simp

lemma no_points (z : Fin 16 → Bool) (h : ∀ p : Fin 8, z (Fin.castAdd 8 p) = false) :
    value z = false := by
  have hz : pointWires.any z = false := by
    simp only [pointWires, List.any_eq_false, List.mem_map]
    rintro i ⟨p, hp, rfl⟩
    intro htrue
    rw [h p] at htrue
    cases htrue
  simp [value, clauses, hz]

lemma no_lines (z : Fin 16 → Bool) (h : ∀ l : Fin 8, z (Fin.natAdd 8 l) = false) :
    value z = false := by
  have hz : lineWires.any z = false := by
    simp only [lineWires, List.any_eq_false, List.mem_map]
    rintro i ⟨l, hl, rfl⟩
    intro htrue
    rw [h l] at htrue
    cases htrue
  simp [value, clauses, hz]

lemma witness_accepted : value witness = true := by decide

lemma witness_has_no_matching_edge :
    ¬ ∃ i : Fin 8, witness (Fin.castAdd 8 i) = true ∧
      witness (Fin.natAdd 8 i) = true := by decide

end PEqualNP.Outside.L_meta_2583_aux.MatrixProbe
