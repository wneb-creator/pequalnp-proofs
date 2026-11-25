import Structural16

namespace PEqualNP.Outside.L_meta_2592_aux.SignedFloor.Extended

open PEqualNP.CircuitLowerBounds

def retentionRows : List (Nat × Nat) := [(0, 0), (0, 0), (0, 0), (0, 0), (64, 576), (192, 704), (192, 704), (64, 576), (64, 576), (96, 608), (96, 608), (64, 576), (128, 640), (384, 896), (384, 896), (128, 640), (128, 640), (192, 704), (192, 704), (128, 640), (128, 640), (144, 656), (144, 656), (128, 640), (64, 576), (68, 580), (68, 580), (64, 576), (128, 640), (129, 641), (129, 641), (128, 640), (128, 640), (136, 648), (136, 648), (128, 640), (128, 640), (130, 642), (130, 642), (128, 640), (32, 160), (544, 672), (544, 672), (32, 160), (0, 0), (0, 0), (0, 0), (0, 0), (512, 640), (544, 672), (544, 672), (512, 640), (512, 640), (768, 896), (768, 896), (512, 640), (32, 160), (96, 224), (96, 224), (32, 160), (32, 160), (48, 176), (48, 176), (32, 160), (512, 640), (516, 644), (516, 644), (512, 640), (512, 640), (513, 641), (513, 641), (512, 640), (512, 640), (520, 648), (520, 648), (512, 640), (512, 640), (514, 642), (514, 642), (512, 640), (256, 288), (768, 800), (768, 800), (256, 288), (256, 288), (384, 416), (384, 416), (256, 288), (0, 0), (0, 0), (0, 0), (0, 0), (128, 160), (384, 416), (384, 416), (128, 160), (128, 160), (192, 224), (192, 224), (128, 160), (128, 160), (144, 176), (144, 176), (128, 160), (256, 288), (260, 292), (260, 292), (256, 288), (128, 160), (129, 161), (129, 161), (128, 160), (128, 160), (136, 168), (136, 168), (128, 160), (128, 160), (130, 162), (130, 162), (128, 160), (32, 288), (544, 800), (544, 800), (32, 288), (64, 320), (192, 448), (192, 448), (64, 320), (64, 320), (96, 352), (96, 352), (64, 320), (0, 0), (0, 0), (0, 0), (0, 0), (32, 288), (96, 352), (96, 352), (32, 288), (32, 288), (48, 304), (48, 304), (32, 288), (32, 288), (36, 292), (36, 292), (32, 288), (64, 320), (65, 321), (65, 321), (64, 320), (32, 288), (40, 296), (40, 296), (32, 288), (32, 288), (34, 290), (34, 290), (32, 288), (256, 320), (768, 832), (768, 832), (256, 320), (256, 320), (384, 448), (384, 448), (256, 320), (512, 576), (544, 608), (544, 608), (512, 576), (512, 576), (768, 832), (768, 832), (512, 576), (0, 0), (0, 0), (0, 0), (0, 0), (256, 320), (272, 336), (272, 336), (256, 320), (512, 576), (516, 580), (516, 580), (512, 576), (512, 576), (513, 577), (513, 577), (512, 576), (512, 576), (520, 584), (520, 584), (512, 576), (512, 576), (514, 578), (514, 578), (512, 576), (1, 17), (513, 529), (513, 529), (1, 17), (1, 17), (129, 145), (129, 145), (1, 17), (512, 528), (544, 560), (544, 560), (512, 528), (512, 528), (768, 784), (768, 784), (512, 528), (1, 17), (65, 81), (65, 81), (1, 17), (0, 0), (0, 0), (0, 0), (0, 0), (512, 528), (516, 532), (516, 532), (512, 528), (512, 528), (513, 529), (513, 529), (512, 528), (512, 528), (520, 536), (520, 536), (512, 528), (512, 528), (514, 530), (514, 530), (512, 528), (8, 12), (520, 524), (520, 524), (8, 12), (8, 12), (136, 140), (136, 140), (8, 12), (8, 12), (40, 44), (40, 44), (8, 12), (128, 132), (384, 388), (384, 388), (128, 132), (128, 132), (192, 196), (192, 196), (128, 132), (128, 132), (144, 148), (144, 148), (128, 132), (0, 0), (0, 0), (0, 0), (0, 0), (128, 132), (129, 133), (129, 133), (128, 132), (128, 132), (136, 140), (136, 140), (128, 132), (128, 132), (130, 134), (130, 134), (128, 132), (32, 33), (544, 545), (544, 545), (32, 33), (16, 17), (144, 145), (144, 145), (16, 17), (16, 17), (48, 49), (48, 49), (16, 17), (16, 17), (272, 273), (272, 273), (16, 17), (32, 33), (96, 97), (96, 97), (32, 33), (32, 33), (48, 49), (48, 49), (32, 33), (32, 33), (36, 37), (36, 37), (32, 33), (0, 0), (0, 0), (0, 0), (0, 0), (32, 33), (40, 41), (40, 41), (32, 33), (32, 33), (34, 35), (34, 35), (32, 33), (256, 264), (768, 776), (768, 776), (256, 264), (256, 264), (384, 392), (384, 392), (256, 264), (16, 24), (48, 56), (48, 56), (16, 24), (16, 24), (272, 280), (272, 280), (16, 24), (16, 24), (80, 88), (80, 88), (16, 24), (256, 264), (272, 280), (272, 280), (256, 264), (256, 264), (260, 268), (260, 268), (256, 264), (256, 264), (257, 265), (257, 265), (256, 264), (0, 0), (0, 0), (0, 0), (0, 0), (256, 264), (258, 266), (258, 266), (256, 264), (4, 6), (516, 518), (516, 518), (4, 6), (64, 66), (192, 194), (192, 194), (64, 66), (64, 66), (96, 98), (96, 98), (64, 66), (4, 6), (260, 262), (260, 262), (4, 6), (4, 6), (68, 70), (68, 70), (4, 6), (64, 66), (80, 82), (80, 82), (64, 66), (64, 66), (68, 70), (68, 70), (64, 66), (64, 66), (65, 67), (65, 67), (64, 66), (64, 66), (72, 74), (72, 74), (64, 66), (0, 0), (0, 0), (0, 0), (0, 0)]

def retentionPair (a b : Sig) (d : Nat) : Row × Row :=
  let p := retentionRows.getD ((pins.idxOf a * 10 + pins.idxOf b) * 4 + d) (0, 0)
  (Fin.ofNat 1024 p.1, Fin.ofNat 1024 p.2)

def retentionTest (a b : Sig) (d : Nat) : Bool :=
  let r := (retentionPair a b d).1
  let s := (retentionPair a b d).2
  (bit r target != bit s target) && (bit r (bin d a b) == bit s (bin d a b)) &&
    pins.all (fun z => z == a || bit r z == bit s z)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma retentionCertificate : pins.all (fun a => pins.all (fun b =>
    (List.range 4).all (fun d => a == b || retentionTest a b d))) = true := by
  decide +kernel

lemma retentionWitness {a b : Sig} {d : Nat} (ha : a ∈ pins) (hb : b ∈ pins)
    (hab : a ≠ b) (hd : d < 4) :
    ∃ r s : Row, bit r target ≠ bit s target ∧
      bit r (bin d a b) = bit s (bin d a b) ∧
      ∀ z ∈ pins, z ≠ a → bit r z = bit s z := by
  have check := List.all_eq_true.mp (List.all_eq_true.mp
    (List.all_eq_true.mp retentionCertificate a ha) b hb) d (List.mem_range.mpr hd)
  have good : retentionTest a b d = true := by
    simpa only [Bool.or_eq_true, beq_iff_eq, hab, false_or] using check
  simp only [retentionTest, Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at good
  refine ⟨(retentionPair a b d).1, (retentionPair a b d).2,
    good.1.1, good.1.2, ?_⟩
  intro z hz hza
  have equal := List.all_eq_true.mp good.2 z hz
  simpa only [Bool.or_eq_true, beq_iff_eq, hza, false_or] using equal

lemma first_left_retained {a b : Sig} {d k : Nat} {U : Finset Sig}
    (ha : a ∈ pins) (hb : b ∈ pins) (hab : a ≠ b) (hd : d < 4)
    (raw : ∀ z ∈ U, z ∈ pins) (tail : Live true target k (insert (bin d a b) U)) :
    a ∈ U := by
  by_contra missing
  obtain ⟨r,s,diff,same,others⟩ := retentionWitness ha hb hab hd
  obtain ⟨z,hz,changed⟩ := live_row_difference tail diff
  rcases Finset.mem_insert.mp hz with rfl | hz
  · exact changed same
  · exact changed (others z (raw z hz) (fun e => missing (e ▸ hz)))

lemma first_retained {a b : Sig} {d k : Nat} {U : Finset Sig}
    (ha : a ∈ pins) (hb : b ∈ pins) (hab : a ≠ b) (hd : d < 4)
    (raw : ∀ z ∈ U, z ∈ pins) (tail : Live true target k (insert (bin d a b) U)) :
    a ∈ U ∨ b ∈ U :=
  Or.inl (first_left_retained ha hb hab hd raw tail)

lemma first_both_retained {a b : Sig} {d k : Nat} {U : Finset Sig}
    (ha : a ∈ pins) (hb : b ∈ pins) (hab : a ≠ b) (hd : allowed true d)
    (raw : ∀ z ∈ U, z ∈ pins) (tail : Live true target k (insert (bin d a b) U)) :
    a ∈ U ∧ b ∈ U := by
  have dlt : d < 4 := by rcases hd with h | ⟨_, h⟩ <;> omega
  have flipped := (flip_flip hd).1
  have flt : flipOp d < 4 := by rcases flipped with h | ⟨_, h⟩ <;> omega
  refine ⟨first_left_retained ha hb hab dlt raw tail, ?_⟩
  apply first_left_retained hb ha (Ne.symm hab) flt raw
  rwa [← bin_flip hd]

end PEqualNP.Outside.L_meta_2592_aux.SignedFloor.Extended
