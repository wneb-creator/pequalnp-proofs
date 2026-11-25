import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_2592
abbrev Sig := BitVec 512
abbrev Row := Fin 512
def zero : Sig := 0
def bit (r : Row) (a : Sig) : Bool := a.getLsbD r.val
def observe (a : Sig) : Row → Bool := fun r => bit r a
def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def graph : Sig := 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
namespace Extended
abbrev Sig := BitVec 1024
abbrev Row := Fin 1024
def zero : Sig := 0
def bit (r : Row) (a : Sig) : Bool := a.getLsbD r.val
def observe (a : Sig) : Row → Bool := fun r => bit r a
def pins : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc]
def target : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc8fffffffffffffffffffffffffffffffffffffffffffffffffffffaeafffff8c8fffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
def initial := pins
end Extended

namespace Projection

def coord (i : Fin 10) : Nat := ([9, 7, 5, 8, 6, 4, 2, 0, 3, 1] : List Nat).getD i.val 9

def sources (v : Fin 10) : List Nat :=
  ([[0,1,2,3,4,5,6,7,8,9], [1,0,4,3,2,6,5,9,8,7],
    [6,8,3,2,1,9,5,4,7,0], [8,3,2,7,5,6,4,1,9,0],
    [5,7,2,3,8,0,9,1,4,6], [7,2,3,4,9,5,1,8,0,6],
    [1,6,9,7,2,0,8,4,5,3], [9,4,3,2,7,6,0,8,1,5],
    [3,2,7,9,4,8,1,5,6,0], [4,9,7,2,3,0,6,5,1,8]] : List (List Nat)).getD v.val []

def row (v : Fin 10) (r : Row) : Extended.Row :=
  Fin.ofNat 1024 ((sources v).foldr (fun j n => Nat.bit (r.val.testBit j) n) 0)

def pin (v : Fin 10) : Extended.Sig := Extended.pins.getD v.val Extended.zero

def image (v i : Fin 10) : Sig := inputs.getD ((sources v).getD (coord i) 9) zero

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma target_values : ∀ (v : Fin 10) (r : Row),
    Extended.bit (row v r) Extended.target = bit r graph := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma pin_values : ∀ (v i : Fin 10) (r : Row),
    Extended.bit (row v r) (pin i) = bit r (image v i) := by
  decide +kernel

lemma image_allowed : ∀ v i : Fin 10, image v i = zero ∨ image v i ∈ inputs := by
  decide +kernel

lemma image_diagonal : ∀ v : Fin 10, image v v = zero := by
  decide +kernel

lemma pins_ofFn : Extended.pins = List.ofFn pin := by
  decide +kernel

lemma pin_injective : Function.Injective pin := by
  decide +kernel

lemma pin_member (i : Fin 10) : pin i ∈ Extended.initial := by
  rw [Extended.initial, pins_ofFn]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩

lemma initial_pin {a : Extended.Sig} (ha : a ∈ Extended.initial) :
    ∃ i : Fin 10, a = pin i := by
  rw [Extended.initial, pins_ofFn] at ha
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp ha
  exact ⟨i, hi.symm⟩

lemma deleted_value (v : Fin 10) (r : Row) :
    Extended.bit (row v r) (pin v) = false := by
  rw [pin_values, image_diagonal]
  simp [bit, zero]

end Projection

end PEqualNP.Outside.L_meta_2592
