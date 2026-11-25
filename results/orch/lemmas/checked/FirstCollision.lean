import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592.Extended

abbrev Sig := BitVec 1024
abbrev Row := Fin 1024
def zero : Sig := 0
def bin (d : Nat) (a b : Sig) : Sig :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def bit (i : Fin 1024) (a : Sig) : Bool := a.getLsbD i.val
def allowed (u : Bool) (d : Nat) : Prop := d<2 ∨ (u=true ∧ d<4)
def pins : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc]
def initial : List Sig := pins
def target : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc8fffffffffffffffffffffffffffffffffffffffffffffffffffffaeafffff8c8fffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8

def collisionRows0 : List (Nat × Nat) :=
  [(0,0), (16,528), (16,528), (16,528), (16,528), (64,576), (16,528), (16,528), (16,528), (16,528), (4,132), (0,0), (4,132), (4,132), (4,132), (4,132), (32,160), (4,132), (4,132), (4,132), (1,33), (1,33), (0,0), (1,33), (1,33), (1,33), (1,33), (128,160), (1,33), (1,33), (8,264), (8,264), (8,264), (0,0), (8,264), (8,264), (8,264), (8,264), (32,288), (8,264), (2,66), (2,66), (2,66), (2,66), (0,0), (2,66), (2,66), (2,66), (2,66), (256,320), (1,17), (1,17), (1,17), (1,17), (1,17), (0,0), (1,17), (8,24), (1,17), (1,17), (2,6), (2,6), (2,6), (2,6), (2,6), (2,6), (0,0), (2,6), (2,6), (8,12), (2,3), (2,3), (2,3), (2,3), (2,3), (2,3), (2,3), (0,0), (2,3), (16,17), (4,12), (4,12), (4,12), (4,12), (4,12), (4,12), (16,24), (4,12), (0,0), (4,12), (1,3), (1,3), (1,3), (1,3), (1,3), (1,3), (1,3), (4,6), (1,3), (0,0)]

def collisionRows1 : List (Nat × Nat) :=
  [(0,0), (128,640), (48,560), (272,784), (64,576), (16,528), (20,532), (65,577), (72,584), (18,530), (512,640), (0,0), (32,160), (260,388), (68,196), (20,148), (4,132), (5,133), (40,168), (34,162), (513,545), (128,160), (0,0), (256,288), (65,97), (144,176), (5,37), (1,33), (9,41), (130,162), (520,776), (136,392), (32,288), (0,0), (64,320), (48,304), (36,292), (9,265), (8,264), (10,266), (512,576), (130,194), (34,98), (256,320), (0,0), (18,82), (260,324), (257,321), (10,74), (2,66), (512,528), (129,145), (40,56), (257,273), (65,81), (0,0), (5,21), (1,17), (8,24), (10,26), (514,518), (128,132), (34,38), (258,262), (72,76), (18,22), (0,0), (9,13), (8,12), (2,6), (514,515), (130,131), (32,33), (258,259), (80,81), (16,17), (20,21), (0,0), (10,11), (2,3), (516,524), (144,152), (36,44), (256,264), (68,76), (16,24), (4,12), (5,13), (0,0), (18,26), (513,515), (129,131), (36,38), (257,259), (64,66), (20,22), (4,6), (1,3), (9,11), (0,0)]

def collisionRows (i j : Fin 10) (d : Fin 4) : Row × Row :=
  let rows := if d.val = 1 ∨ d.val = 2 then collisionRows1 else collisionRows0
  let pair := rows.getD (i.val * 10 + j.val) (0, 0)
  (Fin.ofNat 1024 pair.1, Fin.ofNat 1024 pair.2)

def collisionCheck (i j : Fin 10) (d : Fin 4) : Prop :=
  let r := (collisionRows i j d).1
  let s := (collisionRows i j d).2
  bit r target ≠ bit s target ∧
    bit r (bin d.val (pins.getD i.val zero) (pins.getD j.val zero)) =
      bit s (bin d.val (pins.getD i.val zero) (pins.getD j.val zero)) ∧
    ∀ k : Fin 10, k ≠ i → bit r (pins.getD k.val zero) = bit s (pins.getD k.val zero)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma collisionCheck0 : ∀ j : Fin 10, ∀ d : Fin 4, (0 : Fin 10) ≠ j → collisionCheck 0 j d := by
  unfold collisionCheck
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma collisionCheck1 : ∀ j : Fin 10, ∀ d : Fin 4, (1 : Fin 10) ≠ j → collisionCheck 1 j d := by
  unfold collisionCheck
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma collisionCheck2 : ∀ j : Fin 10, ∀ d : Fin 4, (2 : Fin 10) ≠ j → collisionCheck 2 j d := by
  unfold collisionCheck
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma collisionCheck3 : ∀ j : Fin 10, ∀ d : Fin 4, (3 : Fin 10) ≠ j → collisionCheck 3 j d := by
  unfold collisionCheck
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma collisionCheck4 : ∀ j : Fin 10, ∀ d : Fin 4, (4 : Fin 10) ≠ j → collisionCheck 4 j d := by
  unfold collisionCheck
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma collisionCheck5 : ∀ j : Fin 10, ∀ d : Fin 4, (5 : Fin 10) ≠ j → collisionCheck 5 j d := by
  unfold collisionCheck
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma collisionCheck6 : ∀ j : Fin 10, ∀ d : Fin 4, (6 : Fin 10) ≠ j → collisionCheck 6 j d := by
  unfold collisionCheck
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma collisionCheck7 : ∀ j : Fin 10, ∀ d : Fin 4, (7 : Fin 10) ≠ j → collisionCheck 7 j d := by
  unfold collisionCheck
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma collisionCheck8 : ∀ j : Fin 10, ∀ d : Fin 4, (8 : Fin 10) ≠ j → collisionCheck 8 j d := by
  unfold collisionCheck
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma collisionCheck9 : ∀ j : Fin 10, ∀ d : Fin 4, (9 : Fin 10) ≠ j → collisionCheck 9 j d := by
  unfold collisionCheck
  decide +kernel

lemma collisionChecked (i j : Fin 10) (d : Fin 4) (hij : i ≠ j) : collisionCheck i j d := by
  fin_cases i
  · exact collisionCheck0 j d hij
  · exact collisionCheck1 j d hij
  · exact collisionCheck2 j d hij
  · exact collisionCheck3 j d hij
  · exact collisionCheck4 j d hij
  · exact collisionCheck5 j d hij
  · exact collisionCheck6 j d hij
  · exact collisionCheck7 j d hij
  · exact collisionCheck8 j d hij
  · exact collisionCheck9 j d hij

lemma firstCollision (a b : Sig) (d : Nat) (ha : a ∈ initial) (hb : b ∈ initial)
    (hab : a ≠ b) (hd : allowed true d) :
    ∃ r s : Row, bit r target ≠ bit s target ∧ bit r (bin d a b) = bit s (bin d a b) ∧
      ∀ c ∈ initial, c ≠ a → bit r c = bit s c := by
  obtain ⟨i, hi, hai⟩ := List.mem_iff_getElem.mp ha
  obtain ⟨j, hj, hbj⟩ := List.mem_iff_getElem.mp hb
  have hilen : i < 10 := by simpa only [initial, pins, List.length_cons, List.length_nil] using hi
  have hjlen : j < 10 := by simpa only [initial, pins, List.length_cons, List.length_nil] using hj
  let ii : Fin 10 := ⟨i, hilen⟩
  let jj : Fin 10 := ⟨j, hjlen⟩
  have ai : pins.getD ii.val zero = a := (List.getD_eq_getElem _ _ hi).trans hai
  have bj : pins.getD jj.val zero = b := (List.getD_eq_getElem _ _ hj).trans hbj
  have hij : ii ≠ jj := by
    intro he
    apply hab
    rw [← ai, ← bj, he]
  have hd4 : d < 4 := by rcases hd with hd | ⟨_, hd⟩ <;> omega
  obtain ⟨hchange, hsame, hrest⟩ := collisionChecked ii jj ⟨d, hd4⟩ hij
  refine ⟨(collisionRows ii jj ⟨d, hd4⟩).1, (collisionRows ii jj ⟨d, hd4⟩).2,
    hchange, ?_, ?_⟩
  · simpa only [ai, bj] using hsame
  · intro c hc hca
    obtain ⟨k, hk, hck⟩ := List.mem_iff_getElem.mp hc
    have hklen : k < 10 := by simpa only [initial, pins, List.length_cons, List.length_nil] using hk
    let kk : Fin 10 := ⟨k, hklen⟩
    have ck : pins.getD kk.val zero = c := (List.getD_eq_getElem _ _ hk).trans hck
    have hki : kk ≠ ii := by
      intro he
      apply hca
      rw [← ck, ← ai, he]
    simpa only [ck] using hrest kk hki

end PEqualNP.Outside.L_meta_2592.Extended
