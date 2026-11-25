import Mathlib

namespace PEqualNP.Outside.L_meta_2373.Live1024

abbrev Sig := BitVec 1024
abbrev Row := Fin 1024

def zero : Sig := 0

def bit (i : Row) (a : Sig) : Bool := a.getLsbD i.val

def bin (d : Nat) (a b : Sig) : Sig :=
  if d = 0 then a &&& b else if d = 1 then a ||| b else
    if d = 2 then a &&& ~~~b else ~~~a &&& b

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,
  0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,
  0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,
  0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,
  0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,
  0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,
  0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,
  0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000,
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000]
def graph : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc8fffffffffffffffffffffffffffffffffffffffffffffffffffffaeafffff8c8fffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8

def pairRow (a c : Fin 10) : Row :=
  Fin.ofNat 1024 ((1 <<< a.val) ||| (1 <<< c.val))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma or_separator_rows : ∀ a b : Fin 10, a ≠ b → ∃ c : Fin 10,
    (∀ i : Fin 10, i ≠ a → i ≠ b →
      bit (pairRow a c) (inputs.getD i.val zero) =
        bit (pairRow b c) (inputs.getD i.val zero)) ∧
    bit (pairRow a c) (bin 1 (inputs.getD a.val zero) (inputs.getD b.val zero)) =
      bit (pairRow b c) (bin 1 (inputs.getD a.val zero) (inputs.getD b.val zero)) ∧
    bit (pairRow a c) graph ≠ bit (pairRow b c) graph := by
  decide +kernel

lemma no_or_identification_rows : ∀ a b : Fin 10, a ≠ b →
    ∃ r s : Row,
      (∀ i : Fin 10, i ≠ a → i ≠ b →
        bit r (inputs.getD i.val zero) = bit s (inputs.getD i.val zero)) ∧
      bit r (bin 1 (inputs.getD a.val zero) (inputs.getD b.val zero)) =
        bit s (bin 1 (inputs.getD a.val zero) (inputs.getD b.val zero)) ∧
      bit r graph ≠ bit s graph := by
  intro a b hab
  obtain ⟨c, hc⟩ := or_separator_rows a b hab
  exact ⟨pairRow a c, pairRow b c, hc⟩

end PEqualNP.Outside.L_meta_2373.Live1024
