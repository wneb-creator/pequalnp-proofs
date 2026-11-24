namespace PEqualNP.Outside.L_meta_670_aux.FreshCodeSearch

open LiveCheck DynamicLeaf

abbrev ProgramBuilder (n : Nat) :=
  (Sig → Nat) → List Sig → Fin n →
    List PEqualNP.CircuitLowerBounds.Gate × List Nat

def forceCodes {α : Type} : List Nat → (List Nat → α) → α
  | [], f => f []
  | a :: xs, f => MemoBoolFast.forceNat a fun b =>
      forceCodes xs fun ys => f (b :: ys)

lemma forceCodes_eq {α : Type} (codes : List Nat) (f : List Nat → α) :
    forceCodes codes f = f codes := by
  induction codes generalizing f with
  | nil => rfl
  | cons a xs ih => simp only [forceCodes,MemoBoolFast.forceNat_eq,ih]

def recipeCode (hint : Sig → Nat) : Recipe → Nat
  | .unary a => MetadataStrictEdges.appendCode (hint a) 10
  | .binary d a b => MetadataStrictEdges.appendCode
      (MetadataStrictEdges.appendCode (hint a) (hint b)) (if d then 12 else 11)

def nextCodes (unary : Bool) (v : List Sig) (codes : List Nat)
    (w : List Sig) : List Nat :=
  let hint := MetadataStrictEdges.listHint v codes
  let z := w.headD zero
  let r := if unary then findUnary v z else findBinary v z
  let newCode := (r.map (recipeCode hint)).getD 0
  w.map fun a => if a == z then newCode else hint a

def cut {n : Nat} (oracles : Fin n → Oracle)
    (rho : Fin n → Fin 9 → Base1007.Sig) (programs : ProgramBuilder n)
    (k t : Nat) (v : List Sig) (codes : List Nat) : Bool :=
  let hint := MetadataStrictEdges.listHint v codes
  let ctx := FastRecipe.initial oracles rho hint v (programs hint v)
  ((List.finRange n).any fun i =>
    !(Base1007.unionSep (decide (0<t)) (ctx i).vals == Base1007.top)) ||
      pruned oracles k ctx

def search {n : Nat} (oracles : Fin n → Oracle)
    (rho : Fin n → Fin 9 → Base1007.Sig) (programs : ProgramBuilder n) :
    Nat → Nat → List Sig → List Nat → Bool
  | 0,t,v,codes => if cut oracles rho programs 0 t v codes then false else v == [target]
  | k+1,t,v,codes =>
      MemoBoolFast.forceWires v fun values =>
        forceCodes codes fun flat =>
          if cut oracles rho programs (k+1) t values flat then false else
            stepTest k t values
              (fun w => search oracles rho programs k (t-1) w
                (nextCodes true values flat w))
              (fun w => search oracles rho programs k t w
                (nextCodes false values flat w))

def leafCheck {n : Nat} (oracles : Fin n → Oracle)
    (rho : Fin n → Fin 9 → Base1007.Sig) (programs : ProgramBuilder n)
    (k t : Nat) (v : List Sig) (codes : List Nat) : Bool :=
  BoolNodup.check v && !(search oracles rho programs k t v codes)

end PEqualNP.Outside.L_meta_670_aux.FreshCodeSearch
