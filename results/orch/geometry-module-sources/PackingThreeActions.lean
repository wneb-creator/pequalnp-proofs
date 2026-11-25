import PackingOrbitsDefs
import TwentyOne

namespace PEqualNP.Outside.L_meta_1896_aux.PackingOrbits

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma vertexPerm_bijective : ∀ g : Fin 4, Function.Bijective (vertexPerm g) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma row_inverse_identities : ∀ g : Fin 4, ∀ r : AllRows.R,
    rowInverse g (rowPerm g r) = r ∧
    rowPerm g (rowInverse g r) = r := by
  decide +kernel

lemma rowPerm_bijective (g : Fin 4) : Function.Bijective (rowPerm g) := by
  constructor
  · intro x y h
    have hx := (row_inverse_identities g x).1
    have hy := (row_inverse_identities g y).1
    rw [h] at hx
    exact hx.symm.trans hy
  · intro y
    exact ⟨rowInverse g y, (row_inverse_identities g y).2⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma flag_inverse_identities : ∀ g : Fin 4, ∀ a : Fin 52,
    flagInverse g (flagPerm g a) = a ∧
    flagPerm g (flagInverse g a) = a := by
  decide +kernel

lemma flagPerm_bijective (g : Fin 4) : Function.Bijective (flagPerm g) := by
  constructor
  · intro x y h
    have hx := (flag_inverse_identities g x).1
    have hy := (flag_inverse_identities g y).1
    rw [h] at hx
    exact hx.symm.trans hy
  · intro y
    exact ⟨flagInverse g y, (flag_inverse_identities g y).2⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pair_inverse_identities : ∀ g : Fin 4, ∀ i : Fin 325,
    pairInverse g (pairPerm g i) = i ∧
    pairPerm g (pairInverse g i) = i := by
  decide +kernel

lemma pairPerm_bijective (g : Fin 4) : Function.Bijective (pairPerm g) := by
  constructor
  · intro x y h
    have hx := (pair_inverse_identities g x).1
    have hy := (pair_inverse_identities g y).1
    rw [h] at hx
    exact hx.symm.trans hy
  · intro y
    exact ⟨pairInverse g y, (pair_inverse_identities g y).2⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pairPerm_ends : ∀ g : Fin 4, ∀ i : Fin 325,
    ({(pairEnds (pairPerm g i)).1, (pairEnds (pairPerm g i)).2} : Finset (Fin 26)) =
    {vertexPerm g (pairEnds i).1, vertexPerm g (pairEnds i).2} := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma row_preserved_0 : ∀ r : AllRows.R, ∀ v : Fin 26,
    AllRows.row (rowPerm 0 r) (vertexPerm 0 v) = AllRows.row r v := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma row_preserved_1 : ∀ r : AllRows.R, ∀ v : Fin 26,
    AllRows.row (rowPerm 1 r) (vertexPerm 1 v) = AllRows.row r v := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma row_preserved_2 : ∀ r : AllRows.R, ∀ v : Fin 26,
    AllRows.row (rowPerm 2 r) (vertexPerm 2 v) = AllRows.row r v := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma row_preserved_3 : ∀ r : AllRows.R, ∀ v : Fin 26,
    AllRows.row (rowPerm 3 r) (vertexPerm 3 v) = AllRows.row r v := by
  decide +kernel

lemma row_preserved : ∀ g : Fin 4, ∀ r : AllRows.R, ∀ v : Fin 26,
    AllRows.row (rowPerm g r) (vertexPerm g v) = AllRows.row r v := by
  exact Fin.cases row_preserved_0 (Fin.cases row_preserved_1
    (Fin.cases row_preserved_2 (Fin.cases row_preserved_3 (fun i => Fin.elim0 i))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma flag_preserved : ∀ g : Fin 4, ∀ a : Fin 52, ∀ v : Fin 26,
    Flags.input (flagPerm g a) (vertexPerm g v) = Flags.input a v := by
  decide +kernel

end PEqualNP.Outside.L_meta_1896_aux.PackingOrbits
