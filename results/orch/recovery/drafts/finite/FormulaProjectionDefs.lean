namespace PEqualNP.Outside.L_meta_2592.FormulaPruning

open PEqualNP.MetaComplexity

def joinProjection (isOr : Bool) : Option (DMFormula 3) → Option (DMFormula 3) →
    Option (DMFormula 3)
  | none, b => b
  | a, none => a
  | some a, some b => some (if isOr then .or a b else .and a b)

def project {n : Nat} (ρ : Fin n → Option (Fin 3)) : DMFormula n → Option (DMFormula 3)
  | .lit i b => (ρ i).map (fun j => .lit j b)
  | .and a b => joinProjection false (project ρ a) (project ρ b)
  | .or a b => joinProjection true (project ρ a) (project ρ b)

def tablesOpt : Option (DMFormula 3) → List Nat
  | none => [0,255]
  | some a => pruningTables a

def occursOpt (a : Option (DMFormula 3)) (i : Fin 3) : Nat :=
  match a with
  | none => 0
  | some φ => occurs φ i

def leavesOpt : Option (DMFormula 3) → Nat
  | none => 0
  | some φ => φ.leaves

def cofactorInput {n : Nat} (ρ : Fin n → Option (Fin 3)) (base : Fin n → Bool)
    (r : Fin 8) (i : Fin n) : Bool :=
  match ρ i with
  | none => base i
  | some j => r.val.testBit j.val

def realizes (a : Option (DMFormula 3)) (f : Fin 8 → Bool) : Prop :=
  ∃ t ∈ tablesOpt a, ∀ r, f r = t.testBit r.val

end PEqualNP.Outside.L_meta_2592.FormulaPruning
