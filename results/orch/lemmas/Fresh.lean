import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux.Fresh

abbrev Row := Fin 512

def containsMask (r : Row) (m : Nat) : Bool :=
  r.val &&& m == m

def edge (r : Row) : Bool :=
  [3, 6, 12, 33, 66, 132, 264, 80, 320, 288, 160, 144].any (containsMask r)

def neighbor (r : Row) : Bool :=
  r.val &&& 25 != 0

def exceptional (r : Row) : Bool :=
  containsMask r 386 || containsMask r 100

def increases (r s : Row) : Prop :=
  r.val &&& s.val = r.val

def addNeighbor (r : Row) (m : Nat) : Row := Fin.ofNat 512 (r.val ||| m)

def extension (r : Row) : Row :=
  if !edge (addNeighbor r 1) then addNeighbor r 1
  else if !edge (addNeighbor r 8) then addNeighbor r 8
  else addNeighbor r 16

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma independent_extension : ∀ r : Row, edge r = false → exceptional r = false →
    r.val &&& (extension r).val = r.val ∧
    edge (extension r) = false ∧ neighbor (extension r) = true := by
  decide +kernel

lemma neutralReaderSupport
    (a b : Row → Bool) (g : Row → Bool → Bool → Bool)
    (increasing : ∀ r s, increases r s → a r = true → a s = true)
    (suffix : ∀ r v, g r true false = true → g r true v = true)
    (low : ∀ r, g r (a r) (b r) = edge r)
    (high : ∀ r, g r true false = (edge r || neighbor r))
    (r : Row) (ha : a r = true) : edge r = true ∨ exceptional r = true := by
  cases hr : edge r with
  | true => exact Or.inl rfl
  | false =>
    cases hx : exceptional r with
    | true => exact Or.inr rfl
    | false =>
      obtain ⟨sub, noEdge, hits⟩ := independent_extension r hr hx
      have hA := increasing r (extension r) sub ha
      have hi : g (extension r) true false = true := by
        rw [high, hits, Bool.or_true]
      have hG := suffix (extension r) (b (extension r)) hi
      have lo := low (extension r)
      rw [hA, hG, noEdge] at lo
      contradiction

end PEqualNP.Outside.L_meta_2592_aux.Fresh
