import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux.Extended

abbrev Sig := BitVec 1024
abbrev Row := Fin 1024
def zero : Sig := 0
def bin (d : Nat) (a b : Sig) : Sig :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def bit (i : Fin 1024) (a : Sig) : Bool := a.getLsbD i.val
def pins : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc]
def target : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc8fffffffffffffffffffffffffffffffffffffffffffffffffffffaeafffff8c8fffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8

def retentionMasks : List Nat :=
  [0, 0, 64, 128, 128, 96, 128, 384, 128, 64, 128, 16, 128, 68, 128, 129, 128, 136, 128, 130, 32, 512, 0, 0, 512, 32, 512, 768, 512, 96, 512, 48, 512, 4, 512, 513, 512, 520, 512, 514, 128, 768, 256, 128, 0, 0, 128, 256, 128, 192, 128, 144, 128, 260, 128, 1, 128, 136, 128, 130, 32, 544, 32, 192, 64, 32, 0, 0, 32, 64, 32, 48, 32, 36, 32, 65, 32, 8, 32, 34, 256, 512, 512, 384, 512, 544, 512, 256, 0, 0, 512, 272, 512, 516, 512, 513, 512, 520, 512, 2, 1, 512, 512, 129, 512, 544, 512, 768, 512, 65, 0, 0, 512, 516, 512, 1, 512, 8, 512, 514, 128, 520, 8, 128, 128, 40, 128, 384, 128, 192, 128, 144, 0, 0, 128, 129, 128, 8, 128, 2, 32, 544, 32, 144, 16, 32, 32, 272, 32, 96, 32, 16, 32, 36, 0, 0, 32, 40, 32, 2, 256, 768, 256, 384, 256, 48, 16, 256, 256, 80, 256, 16, 256, 4, 256, 257, 0, 0, 256, 258, 64, 516, 64, 192, 64, 96, 64, 260, 4, 64, 64, 80, 64, 4, 64, 1, 64, 72, 0, 0]

def retentionPlaces : List Nat := [9, 7, 5, 8, 6, 4, 2, 0, 3, 1]

def retentionLow (i j : Fin 10) (d : Fin 4) : Row :=
  ⟨(retentionMasks.getD (i.val * 20 + j.val * 2 + if d.val = 1 ∨ d.val = 2 then 1 else 0) 0) % 1024,
    Nat.mod_lt _ (by decide)⟩

def retentionHigh (i j : Fin 10) (d : Fin 4) : Row :=
  ⟨(retentionLow i j d + 2 ^ retentionPlaces.getD i.val 0) % 1024, Nat.mod_lt _ (by decide)⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma retention_checked : ∀ (i j : Fin 10) (d : Fin 4), i ≠ j →
    bit (retentionLow i j d) target ≠ bit (retentionHigh i j d) target ∧
    bit (retentionLow i j d) (bin d.val (pins.getD i.val zero) (pins.getD j.val zero)) =
      bit (retentionHigh i j d) (bin d.val (pins.getD i.val zero) (pins.getD j.val zero)) ∧
    ∀ v : Fin 10, v ≠ i →
      bit (retentionLow i j d) (pins.getD v.val zero) =
        bit (retentionHigh i j d) (pins.getD v.val zero) := by
  decide +kernel

lemma retention_witness (i j : Fin 10) (h : i ≠ j) (d : Fin 4) :
    ∃ r s : Row, bit r target ≠ bit s target ∧
      bit r (bin d.val (pins.getD i.val zero) (pins.getD j.val zero)) =
        bit s (bin d.val (pins.getD i.val zero) (pins.getD j.val zero)) ∧
      ∀ v : Fin 10, v ≠ i → bit r (pins.getD v.val zero) = bit s (pins.getD v.val zero) :=
  ⟨retentionLow i j d, retentionHigh i j d, retention_checked i j d h⟩

end PEqualNP.Outside.L_meta_2592_aux.Extended
