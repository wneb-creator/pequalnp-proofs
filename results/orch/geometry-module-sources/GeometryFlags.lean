import GeometryRowsDefs

namespace PEqualNP.Outside.L_meta_1896_aux

namespace FourRows

def pairInput (p l : Fin 13) (v : Fin 26) : Bool :=
  decide (v = Fin.castAdd 13 p ∨ v = Fin.natAdd 13 l)

end FourRows

namespace Flags

open FourRows

def flag (a : Fin 52) : Fin 13 × Fin 13 :=
  ([(0, 0), (1, 0), (3, 0), (9, 0), (1, 1), (2, 1), (4, 1), (10, 1), (2, 2), (3, 2), (5, 2), (11, 2), (3, 3), (4, 3), (6, 3), (12, 3), (4, 4), (5, 4), (7, 4), (0, 4), (5, 5), (6, 5), (8, 5), (1, 5), (6, 6), (7, 6), (9, 6), (2, 6), (7, 7), (8, 7), (10, 7), (3, 7), (8, 8), (9, 8), (11, 8), (4, 8), (9, 9), (10, 9), (12, 9), (5, 9), (10, 10), (11, 10), (0, 10), (6, 10), (11, 11), (12, 11), (1, 11), (7, 11), (12, 12), (0, 12), (2, 12), (8, 12)] : List (Fin 13 × Fin 13)).getD a.val (0, 0)

def input (a : Fin 52) : Fin 26 → Bool := pairInput (flag a).1 (flag a).2

def indexFor (p l : Fin 13) : Fin 52 :=
  let d : Fin 4 := if p = l then 0 else if p = l + 1 then 1 else if p = l + 3 then 2 else 3
  ⟨4 * l.val + d.val, by omega⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma flag_indexFor : ∀ p l : Fin 13, AllRows.incidence p l → flag (indexFor p l) = (p, l) := by
  decide +kernel

lemma incident_covered (p l : Fin 13) (h : AllRows.incidence p l) :
    ∃ a : Fin 52, flag a = (p, l) :=
  ⟨indexFor p l, flag_indexFor p l h⟩

lemma input_indexFor (p l : Fin 13) (h : AllRows.incidence p l) :
    input (indexFor p l) = pairInput p l := by
  unfold input
  rw [flag_indexFor p l h]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma incidence_all : ∀ a : Fin 52, AllRows.incidence (flag a).1 (flag a).2 := by
  decide +kernel

end Flags
end PEqualNP.Outside.L_meta_1896_aux
