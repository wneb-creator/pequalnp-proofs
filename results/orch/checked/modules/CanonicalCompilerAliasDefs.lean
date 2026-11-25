import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1896_aux.CanonicalCompiler

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def Program (n : Nat) : Nat → Type
  | 0 => List (Fin n)
  | k + 1 => (List (Fin n) × List (Fin n)) × Program (n + 1) k

def evaluate {n : Nat} : (k : Nat) → Program n k → (Fin n → Bool) → Bool
  | 0, output, values => output.all values
  | k + 1, program, values =>
      evaluate k program.2 (Fin.snoc values (program.1.1.all values || program.1.2.all values))

def conjunction (offset : Nat) : List Nat → List Gate
  | [] => [⟨.and, []⟩]
  | wire :: tail => conjunction offset tail ++ [⟨.and, [wire, offset + tail.length]⟩]

def compile {n : Nat} : (k : Nat) → Program n k → Nat → (Fin n → Nat) → Circuit
  | 0, output, offset, refs =>
      ⟨conjunction offset (output.map refs), offset + output.length⟩
  | k + 1, program, offset, refs =>
      let left := program.1.1
      let right := program.1.2
      let leftGates := conjunction offset (left.map refs)
      let rightOffset := offset + left.length + 1
      let rightGates := conjunction rightOffset (right.map refs)
      let orWire := rightOffset + right.length + 1
      let later := compile k program.2 (orWire + 1) (Fin.snoc refs orWire)
      ⟨leftGates ++ rightGates ++
          [⟨.or, [offset + left.length, rightOffset + right.length]⟩] ++ later.gates,
        later.output⟩

end PEqualNP.Outside.L_meta_1896_aux.CanonicalCompiler
