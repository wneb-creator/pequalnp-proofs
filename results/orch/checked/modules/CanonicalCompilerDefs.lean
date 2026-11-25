import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1896_aux.CanonicalCompiler

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

inductive Program : Nat → Type where
  | done {n : Nat} (output : List (Fin n)) : Program n
  | step {n : Nat} (left right : List (Fin n)) (tail : Program (n + 1)) : Program n

def Program.orCount {n : Nat} : Program n → Nat
  | .done _ => 0
  | .step _ _ tail => tail.orCount + 1

def Program.eval {n : Nat} : Program n → (Fin n → Bool) → Bool
  | .done output, values => output.all values
  | .step left right tail, values =>
      tail.eval (Fin.snoc values (left.all values || right.all values))

def conjunction (offset : Nat) : List Nat → List Gate
  | [] => [⟨.and, []⟩]
  | wire :: tail => conjunction offset tail ++ [⟨.and, [wire, offset + tail.length]⟩]

def compile {n : Nat} : Program n → Nat → (Fin n → Nat) → Circuit
  | .done output, offset, refs =>
      ⟨conjunction offset (output.map refs), offset + output.length⟩
  | .step left right tail, offset, refs =>
      let leftGates := conjunction offset (left.map refs)
      let rightOffset := offset + left.length + 1
      let rightGates := conjunction rightOffset (right.map refs)
      let orWire := rightOffset + right.length + 1
      let later := compile tail (orWire + 1) (Fin.snoc refs orWire)
      ⟨leftGates ++ rightGates ++
          [⟨.or, [offset + left.length, rightOffset + right.length]⟩] ++ later.gates,
        later.output⟩

end PEqualNP.Outside.L_meta_1896_aux.CanonicalCompiler
