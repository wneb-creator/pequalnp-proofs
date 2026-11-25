import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1890_aux

def edgeValue (x : Fin 10 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
  (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
  (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) ||
  (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)

def seedVertex (s : Fin 2) : Fin 10 := if s = 0 then 0 else 2

def seedOther (s : Fin 2) : Fin 10 := if s = 0 then 2 else 0

def seedNeighbor (s : Fin 2) : Fin 10 := if s = 0 then 5 else 7

def seedOff (s : Fin 2) (useOr : Bool) (i : Fin 10) : Bool :=
  decide (i = seedNeighbor s) || (!useOr && decide (i = seedOther s))

def seedOn (s : Fin 2) (useOr : Bool) (i : Fin 10) : Bool :=
  seedOff s useOr i || decide (i = seedVertex s)

def seedFold (s : Fin 2) (useOr : Bool) (x : Fin 10 → Bool) : Bool :=
  if useOr then x (seedVertex s) || !(x 0 && x 2)
  else x (seedVertex s) && !(x 0 && x 2)

lemma seed_not_collisions (s : Fin 2) (useOr : Bool) :
    ∃ x y : Fin 10 → Bool,
      (∀ i, i ≠ seedVertex s → x i = y i) ∧
      seedFold s useOr x = seedFold s useOr y ∧
      edgeValue x = false ∧ edgeValue y = true := by
  refine ⟨seedOff s useOr, seedOn s useOr, ?_⟩
  fin_cases s <;> cases useOr <;> decide +kernel

end PEqualNP.Outside.L_meta_1890_aux
