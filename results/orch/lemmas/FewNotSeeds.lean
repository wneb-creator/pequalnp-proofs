import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_2592.FewNot
abbrev Sig := BitVec 512
def zero : Sig := 0
def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def graph : Sig := 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
namespace Extended
abbrev Sig := BitVec 1024
def zero : Sig := 0
def one : Sig := BitVec.allOnes 1024
def neg (a : Sig) : Sig := ~~~a
def bin (d : Nat) (a b : Sig) : Sig :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def bit (i : Fin 1024) (a : Sig) : Bool := a.getLsbD i.val
abbrev Row := Fin 1024
def pins : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc]
def first : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
def target : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc8fffffffffffffffffffffffffffffffffffffffffffffffffffffaeafffff8c8fffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
end Extended
def projected (a : Extended.Sig) : Sig := a.setWidth 512



def seeded (j : Fin 9) (d : Fin 4) : List Extended.Sig :=
  Extended.pins ++ [Extended.bin d.val Extended.first (Extended.pins.getD (j.val + 1) Extended.zero)]

def seedRow (j : Fin 9) (d : Fin 4) : Extended.Row :=
  if d.val = 0 ∨ d.val = 3 then
    if j.val = 0 then 64 else 128
  else
    (![128, 96, 384, 64, 16, 68, 129, 136, 130] : Fin 9 → Extended.Row) j

def seedRowNext (j : Fin 9) (d : Fin 4) : Extended.Row :=
  ⟨(seedRow j d).val + 512, by
    fin_cases j <;> fin_cases d <;> decide⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma seed_target_diff : ∀ (j : Fin 9) (d : Fin 4),
    Extended.bit (seedRow j d) Extended.target ≠
      Extended.bit (seedRowNext j d) Extended.target := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma seed_stable : ∀ (j : Fin 9) (d : Fin 4),
    (seeded j d).all (fun a =>
      (Extended.bit (seedRow j d) a == Extended.bit (seedRowNext j d) a) ||
        (a == Extended.first)) = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma seed_permitted : ∀ (j : Fin 9) (d : Fin 4),
    (seeded j d).all (fun a =>
      (projected a == zero) || inputs.contains (projected a)) = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma seed_zero : ∀ (j : Fin 9) (d : Fin 4),
    Extended.bit 0 (Extended.bin d.val Extended.first
      (Extended.pins.getD (j.val + 1) Extended.zero)) = false := by decide +kernel


set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma seed_extra_stable : ∀ (j : Fin 9) (d : Fin 4),
    Extended.bit (seedRow j d)
      (Extended.bin d.val Extended.first (Extended.pins.getD (j.val + 1) Extended.zero)) =
    Extended.bit (seedRowNext j d)
      (Extended.bin d.val Extended.first (Extended.pins.getD (j.val + 1) Extended.zero)) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma seed_pin_stable : ∀ (j : Fin 9) (d : Fin 4) (v : Fin 10), v ≠ 0 →
    Extended.bit (seedRow j d) (Extended.pins.getD v.val Extended.zero) =
      Extended.bit (seedRowNext j d) (Extended.pins.getD v.val Extended.zero) := by
  decide +kernel

end PEqualNP.Outside.L_meta_2592.FewNot
