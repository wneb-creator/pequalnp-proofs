import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux.RowWitness
abbrev Sig := BitVec 1024
def zero : Sig := 0
def bin (d : Nat) (a b : Sig) : Sig :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def bit (i : Fin 1024) (a : Sig) : Bool := a.getLsbD i.val
def pins : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc]
def target : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc8fffffffffffffffffffffffffffffffffffffffffffffffffffffaeafffff8c8fffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8

def witnesses : List (Fin 1024 × Fin 1024) := [
  (0, 0), (0, 0), (0, 0), (0, 0), (16, 528), (128, 640), (128, 640), (16, 528), (16, 528), (48, 560),
  (48, 560), (16, 528), (16, 528), (272, 784), (272, 784), (16, 528), (16, 528), (64, 576), (64, 576), (16, 528),
  (64, 576), (16, 528), (16, 528), (64, 576), (16, 528), (20, 532), (20, 532), (16, 528), (16, 528), (65, 577),
  (65, 577), (16, 528), (16, 528), (72, 584), (72, 584), (16, 528), (16, 528), (18, 530), (18, 530), (16, 528),
  (4, 132), (512, 640), (512, 640), (4, 132), (0, 0), (0, 0), (0, 0), (0, 0), (4, 132), (32, 160),
  (32, 160), (4, 132), (4, 132), (260, 388), (260, 388), (4, 132), (4, 132), (68, 196), (68, 196), (4, 132),
  (4, 132), (20, 148), (20, 148), (4, 132), (32, 160), (4, 132), (4, 132), (32, 160), (4, 132), (5, 133),
  (5, 133), (4, 132), (4, 132), (40, 168), (40, 168), (4, 132), (4, 132), (34, 162), (34, 162), (4, 132),
  (1, 33), (513, 545), (513, 545), (1, 33), (1, 33), (128, 160), (128, 160), (1, 33), (0, 0), (0, 0),
  (0, 0), (0, 0), (1, 33), (256, 288), (256, 288), (1, 33), (1, 33), (65, 97), (65, 97), (1, 33),
  (1, 33), (144, 176), (144, 176), (1, 33), (1, 33), (5, 37), (5, 37), (1, 33), (128, 160), (1, 33),
  (1, 33), (128, 160), (1, 33), (9, 41), (9, 41), (1, 33), (1, 33), (130, 162), (130, 162), (1, 33),
  (8, 264), (520, 776), (520, 776), (8, 264), (8, 264), (136, 392), (136, 392), (8, 264), (8, 264), (32, 288),
  (32, 288), (8, 264), (0, 0), (0, 0), (0, 0), (0, 0), (8, 264), (64, 320), (64, 320), (8, 264),
  (8, 264), (48, 304), (48, 304), (8, 264), (8, 264), (36, 292), (36, 292), (8, 264), (8, 264), (9, 265),
  (9, 265), (8, 264), (32, 288), (8, 264), (8, 264), (32, 288), (8, 264), (10, 266), (10, 266), (8, 264),
  (2, 66), (512, 576), (512, 576), (2, 66), (2, 66), (130, 194), (130, 194), (2, 66), (2, 66), (34, 98),
  (34, 98), (2, 66), (2, 66), (256, 320), (256, 320), (2, 66), (0, 0), (0, 0), (0, 0), (0, 0),
  (2, 66), (18, 82), (18, 82), (2, 66), (2, 66), (260, 324), (260, 324), (2, 66), (2, 66), (257, 321),
  (257, 321), (2, 66), (2, 66), (10, 74), (10, 74), (2, 66), (256, 320), (2, 66), (2, 66), (256, 320),
  (1, 17), (512, 528), (512, 528), (1, 17), (1, 17), (129, 145), (129, 145), (1, 17), (1, 17), (40, 56),
  (40, 56), (1, 17), (1, 17), (257, 273), (257, 273), (1, 17), (1, 17), (65, 81), (65, 81), (1, 17),
  (0, 0), (0, 0), (0, 0), (0, 0), (1, 17), (5, 21), (5, 21), (1, 17), (8, 24), (1, 17),
  (1, 17), (8, 24), (1, 17), (8, 24), (8, 24), (1, 17), (1, 17), (10, 26), (10, 26), (1, 17),
  (2, 6), (514, 518), (514, 518), (2, 6), (2, 6), (128, 132), (128, 132), (2, 6), (2, 6), (34, 38),
  (34, 38), (2, 6), (2, 6), (258, 262), (258, 262), (2, 6), (2, 6), (72, 76), (72, 76), (2, 6),
  (2, 6), (18, 22), (18, 22), (2, 6), (0, 0), (0, 0), (0, 0), (0, 0), (2, 6), (9, 13),
  (9, 13), (2, 6), (2, 6), (8, 12), (8, 12), (2, 6), (8, 12), (2, 6), (2, 6), (8, 12),
  (2, 3), (514, 515), (514, 515), (2, 3), (2, 3), (130, 131), (130, 131), (2, 3), (2, 3), (32, 33),
  (32, 33), (2, 3), (2, 3), (258, 259), (258, 259), (2, 3), (2, 3), (80, 81), (80, 81), (2, 3),
  (2, 3), (16, 17), (16, 17), (2, 3), (2, 3), (20, 21), (20, 21), (2, 3), (0, 0), (0, 0),
  (0, 0), (0, 0), (2, 3), (10, 11), (10, 11), (2, 3), (16, 17), (2, 3), (2, 3), (16, 17),
  (4, 12), (516, 524), (516, 524), (4, 12), (4, 12), (144, 152), (144, 152), (4, 12), (4, 12), (36, 44),
  (36, 44), (4, 12), (4, 12), (256, 264), (256, 264), (4, 12), (4, 12), (68, 76), (68, 76), (4, 12),
  (4, 12), (16, 24), (16, 24), (4, 12), (16, 24), (4, 12), (4, 12), (16, 24), (4, 12), (5, 13),
  (5, 13), (4, 12), (0, 0), (0, 0), (0, 0), (0, 0), (4, 12), (18, 26), (18, 26), (4, 12),
  (1, 3), (513, 515), (513, 515), (1, 3), (1, 3), (129, 131), (129, 131), (1, 3), (1, 3), (36, 38),
  (36, 38), (1, 3), (1, 3), (257, 259), (257, 259), (1, 3), (1, 3), (64, 66), (64, 66), (1, 3),
  (1, 3), (20, 22), (20, 22), (1, 3), (1, 3), (4, 6), (4, 6), (1, 3), (4, 6), (1, 3),
  (1, 3), (4, 6), (1, 3), (9, 11), (9, 11), (1, 3), (0, 0), (0, 0), (0, 0), (0, 0)]

def choose (i j : Fin 10) (d : Fin 4) :=
  witnesses.getD ((i.val * 10 + j.val) * 4 + d.val) (0, 0)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma separating_rows : ∀ (i j : Fin 10) (d : Fin 4), i ≠ j →
    let r := (choose i j d).1
    let s := (choose i j d).2
    bit r target ≠ bit s target ∧
      bit r (bin d.val (pins.getD i.val zero) (pins.getD j.val zero)) =
        bit s (bin d.val (pins.getD i.val zero) (pins.getD j.val zero)) ∧
      ∀ t : Fin 10, t ≠ i → bit r (pins.getD t.val zero) = bit s (pins.getD t.val zero) := by
  decide +kernel

end PEqualNP.Outside.L_meta_2592_aux.RowWitness
