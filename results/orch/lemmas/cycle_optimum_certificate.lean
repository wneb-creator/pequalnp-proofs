import PEqualNP.Defs.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1031_aux.SemanticCertificate

def initial : List (BitVec 10) :=
  [0, 1, 2, 4, 8, 16, 32, 64, 113, 128, 204, 256, 387, 512, 550, 792, 1023]

def extend (xs : List (BitVec 10)) (v : BitVec 10) : List (BitVec 10) :=
  (xs ++ xs.map (fun u => u &&& v)).eraseDups

def ors (xs : List (BitVec 10)) : List (BitVec 10) :=
  (xs.flatMap (fun a => xs.map (fun b => a ||| b))).eraseDups

def full (xs : List (BitVec 10)) : List (BitVec 10) :=
  xs.filter (fun u => (u &&& 31) == 31)

def finish (xs : List (BitVec 10)) : Bool :=
  (full xs).all (fun u => xs.all (fun a => xs.all (fun b => !((u &&& (a ||| b)) == 31))))

def checkFirst (v : BitVec 10) : Bool :=
  let xs := extend initial v
  (ors xs).all (fun w => finish (extend xs w))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_0 : checkFirst 0 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_1 : checkFirst 1 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_2 : checkFirst 2 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_3 : checkFirst 3 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_4 : checkFirst 4 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_5 : checkFirst 5 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_6 : checkFirst 6 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_8 : checkFirst 8 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_9 : checkFirst 9 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_10 : checkFirst 10 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_12 : checkFirst 12 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_16 : checkFirst 16 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_17 : checkFirst 17 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_18 : checkFirst 18 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_20 : checkFirst 20 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_24 : checkFirst 24 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_32 : checkFirst 32 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_33 : checkFirst 33 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_34 : checkFirst 34 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_36 : checkFirst 36 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_40 : checkFirst 40 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_48 : checkFirst 48 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_64 : checkFirst 64 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_65 : checkFirst 65 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_66 : checkFirst 66 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_68 : checkFirst 68 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_72 : checkFirst 72 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_80 : checkFirst 80 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_96 : checkFirst 96 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_113 : checkFirst 113 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_115 : checkFirst 115 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_117 : checkFirst 117 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_121 : checkFirst 121 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_128 : checkFirst 128 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_129 : checkFirst 129 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_130 : checkFirst 130 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_132 : checkFirst 132 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_136 : checkFirst 136 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_144 : checkFirst 144 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_160 : checkFirst 160 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_192 : checkFirst 192 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_204 : checkFirst 204 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_205 : checkFirst 205 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_206 : checkFirst 206 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_220 : checkFirst 220 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_236 : checkFirst 236 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_241 : checkFirst 241 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_253 : checkFirst 253 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_256 : checkFirst 256 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_257 : checkFirst 257 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_258 : checkFirst 258 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_260 : checkFirst 260 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_264 : checkFirst 264 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_272 : checkFirst 272 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_288 : checkFirst 288 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_320 : checkFirst 320 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_369 : checkFirst 369 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_384 : checkFirst 384 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_387 : checkFirst 387 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_391 : checkFirst 391 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_395 : checkFirst 395 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_403 : checkFirst 403 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_419 : checkFirst 419 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_451 : checkFirst 451 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_460 : checkFirst 460 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_463 : checkFirst 463 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_499 : checkFirst 499 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_512 : checkFirst 512 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_513 : checkFirst 513 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_514 : checkFirst 514 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_516 : checkFirst 516 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_520 : checkFirst 520 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_528 : checkFirst 528 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_544 : checkFirst 544 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_550 : checkFirst 550 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_551 : checkFirst 551 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_558 : checkFirst 558 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_566 : checkFirst 566 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_576 : checkFirst 576 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_614 : checkFirst 614 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_625 : checkFirst 625 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_631 : checkFirst 631 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_640 : checkFirst 640 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_678 : checkFirst 678 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_716 : checkFirst 716 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_750 : checkFirst 750 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_768 : checkFirst 768 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_792 : checkFirst 792 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_793 : checkFirst 793 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_794 : checkFirst 794 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_796 : checkFirst 796 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_806 : checkFirst 806 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_824 : checkFirst 824 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_830 : checkFirst 830 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_856 : checkFirst 856 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_889 : checkFirst 889 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_899 : checkFirst 899 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_920 : checkFirst 920 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_923 : checkFirst 923 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_935 : checkFirst 935 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_988 : checkFirst 988 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem first_1023 : checkFirst 1023 = true := by
  decide +kernel

lemma ors_initial_eq : ors initial = [0, 1, 2, 4, 8, 16, 32, 64, 113, 128, 204, 256, 387, 512, 550, 792, 1023, 3, 5, 9, 17, 33, 65, 129, 205, 257, 513, 551, 793, 6, 10, 18, 34, 66, 115, 130, 206, 258, 514, 794, 12, 20, 36, 68, 117, 132, 260, 391, 516, 796, 24, 40, 72, 121, 136, 264, 395, 520, 558, 48, 80, 144, 220, 272, 403, 528, 566, 96, 160, 236, 288, 419, 544, 824, 192, 320, 451, 576, 614, 856, 241, 253, 369, 499, 625, 631, 889, 384, 640, 678, 920, 460, 463, 716, 750, 988, 768, 806, 899, 935, 923, 830] := by
  decide +kernel

theorem all_first_cases : ∀ v ∈ ors initial, checkFirst v = true := by
  intro v hv
  rw [ors_initial_eq] at hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact first_0
  · exact first_1
  · exact first_2
  · exact first_4
  · exact first_8
  · exact first_16
  · exact first_32
  · exact first_64
  · exact first_113
  · exact first_128
  · exact first_204
  · exact first_256
  · exact first_387
  · exact first_512
  · exact first_550
  · exact first_792
  · exact first_1023
  · exact first_3
  · exact first_5
  · exact first_9
  · exact first_17
  · exact first_33
  · exact first_65
  · exact first_129
  · exact first_205
  · exact first_257
  · exact first_513
  · exact first_551
  · exact first_793
  · exact first_6
  · exact first_10
  · exact first_18
  · exact first_34
  · exact first_66
  · exact first_115
  · exact first_130
  · exact first_206
  · exact first_258
  · exact first_514
  · exact first_794
  · exact first_12
  · exact first_20
  · exact first_36
  · exact first_68
  · exact first_117
  · exact first_132
  · exact first_260
  · exact first_391
  · exact first_516
  · exact first_796
  · exact first_24
  · exact first_40
  · exact first_72
  · exact first_121
  · exact first_136
  · exact first_264
  · exact first_395
  · exact first_520
  · exact first_558
  · exact first_48
  · exact first_80
  · exact first_144
  · exact first_220
  · exact first_272
  · exact first_403
  · exact first_528
  · exact first_566
  · exact first_96
  · exact first_160
  · exact first_236
  · exact first_288
  · exact first_419
  · exact first_544
  · exact first_824
  · exact first_192
  · exact first_320
  · exact first_451
  · exact first_576
  · exact first_614
  · exact first_856
  · exact first_241
  · exact first_253
  · exact first_369
  · exact first_499
  · exact first_625
  · exact first_631
  · exact first_889
  · exact first_384
  · exact first_640
  · exact first_678
  · exact first_920
  · exact first_460
  · exact first_463
  · exact first_716
  · exact first_750
  · exact first_988
  · exact first_768
  · exact first_806
  · exact first_899
  · exact first_935
  · exact first_923
  · exact first_830

def select (p : BitVec 8) (i : Nat) (v : BitVec 10) : BitVec 10 :=
  if p.getLsbD i then v else 1023

def meet0 (p : BitVec 8) : BitVec 10 :=
  select p 0 113 &&& select p 1 387 &&& select p 2 550 &&&
    select p 3 204 &&& select p 4 792

def meet1 (p : BitVec 8) (v : BitVec 10) : BitVec 10 := meet0 p &&& select p 5 v

def meet2 (p : BitVec 8) (v w : BitVec 10) : BitVec 10 := meet1 p v &&& select p 6 w

def meet3 (p : BitVec 8) (v w z : BitVec 10) : BitVec 10 := meet2 p v w &&& select p 7 z

lemma initial_meet0 : ∀ p : BitVec 8, meet0 p ∈ initial := by
  decide +kernel

lemma mem_extend {xs : List (BitVec 10)} {u : BitVec 10} (hu : u ∈ xs) (v : BitVec 10) :
    u ∈ extend xs v := by
  simp [extend, hu]

lemma and_mem_extend {xs : List (BitVec 10)} {u : BitVec 10} (hu : u ∈ xs) (v : BitVec 10) :
    u &&& v ∈ extend xs v := by
  simp only [extend, List.mem_eraseDups, List.mem_append, List.mem_map]
  exact Or.inr ⟨u, hu, rfl⟩

lemma selected_mem_extend {xs : List (BitVec 10)} {u : BitVec 10} (hu : u ∈ xs)
    (v : BitVec 10) (bit : Bool) :
    u &&& (if bit then v else (1023 : BitVec 10)) ∈ extend xs v := by
  cases bit with
  | false =>
    change u &&& BitVec.allOnes 10 ∈ extend xs v
    rw [BitVec.and_allOnes]
    exact mem_extend hu v
  | true => exact and_mem_extend hu v

lemma meet1_mem (p : BitVec 8) (v : BitVec 10) : meet1 p v ∈ extend initial v :=
  selected_mem_extend (initial_meet0 p) v (p.getLsbD 5)

lemma meet2_mem (p : BitVec 8) (v w : BitVec 10) :
    meet2 p v w ∈ extend (extend initial v) w :=
  selected_mem_extend (meet1_mem p v) w (p.getLsbD 6)

lemma or_mem {xs : List (BitVec 10)} {a b : BitVec 10} (ha : a ∈ xs) (hb : b ∈ xs) :
    a ||| b ∈ ors xs := by
  simp only [ors, List.mem_eraseDups, List.mem_flatMap, List.mem_map]
  exact ⟨a, ha, b, hb, rfl⟩

lemma finish_sound (xs : List (BitVec 10)) (hfinish : finish xs = true)
    {u a b : BitVec 10} (hu : u ∈ xs) (ha : a ∈ xs) (hb : b ∈ xs) :
    u &&& (a ||| b) ≠ (31 : BitVec 10) := by
  intro heq
  have hmask : u &&& (31 : BitVec 10) = 31 := by
    rw [← heq, ← BitVec.and_assoc, BitVec.and_self]
  have hfull : u ∈ full xs := by
    apply List.mem_filter.mpr
    exact ⟨hu, by simpa only [beq_iff_eq] using hmask⟩
  have htest := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp hfinish u hfull) a ha) b hb
  rw [heq] at htest
  simp at htest

lemma finish_selected_sound (xs : List (BitVec 10)) (hfinish : finish xs = true)
    {u a b : BitVec 10} (hu : u ∈ xs) (ha : a ∈ xs) (hb : b ∈ xs)
    (hone : (1023 : BitVec 10) ∈ xs) (bit : Bool) :
    u &&& (if bit then a ||| b else (1023 : BitVec 10)) ≠ (31 : BitVec 10) := by
  cases bit with
  | false => simpa only [Bool.false_eq_true, ↓reduceIte, BitVec.or_self] using finish_sound xs hfinish hu hone hone
  | true => exact finish_sound xs hfinish hu ha hb

theorem semantic_soundness
    (hchecks : ∀ v ∈ ors initial, checkFirst v = true) :
    ∀ a b c d e f o : BitVec 8,
      let v := meet0 a ||| meet0 b
      let w := meet1 c v ||| meet1 d v
      let z := meet2 e v w ||| meet2 f v w
      meet3 o v w z ≠ (31 : BitVec 10) := by
  intro a b c d e f o
  let v := meet0 a ||| meet0 b
  let w := meet1 c v ||| meet1 d v
  have hv : v ∈ ors initial := or_mem (initial_meet0 a) (initial_meet0 b)
  have hw : w ∈ ors (extend initial v) := or_mem (meet1_mem c v) (meet1_mem d v)
  have hall : (ors (extend initial v)).all
      (fun w => finish (extend (extend initial v) w)) = true := hchecks v hv
  have hfinish := List.all_eq_true.mp hall w hw
  have hone : (1023 : BitVec 10) ∈ extend (extend initial v) w :=
    mem_extend (mem_extend (by simp [initial]) v) w
  exact finish_selected_sound _ hfinish (meet2_mem o v w) (meet2_mem e v w)
    (meet2_mem f v w) hone (o.getLsbD 7)

end PEqualNP.Outside.L_meta_1031_aux.SemanticCertificate


namespace PEqualNP.Outside.L_meta_1031_aux.CompactOr

open PEqualNP.CircuitLowerBounds

def meet (values : List Bool) (atoms : List ℕ) : Bool :=
  atoms.all (fun i => values.getD i false)

def step (values : List Bool) (g : List ℕ × List ℕ) : List Bool :=
  values ++ [meet values g.1 || meet values g.2]

def wires (program : List (List ℕ × List ℕ)) (x : List Bool) : List Bool :=
  program.foldl step x

def eval (program : List (List ℕ × List ℕ)) (output : List ℕ) (x : List Bool) : Bool :=
  meet (wires program x) output

def bounded (bound : ℕ) (atoms : List ℕ) : Prop := ∀ i ∈ atoms, i < bound

def wellFormed (n : ℕ) (program : List (List ℕ × List ℕ)) : Prop :=
  ∀ j < program.length,
    bounded (n + j) (program.getD j ([], [])).1 ∧
    bounded (n + j) (program.getD j ([], [])).2

def isOr (g : Gate) : Bool := match g.op with
  | GateOp.or => true
  | _ => false

def orCount (gs : List Gate) : ℕ := gs.countP isOr

lemma meet_append (values : List Bool) (a b : List ℕ) :
    meet values (a ++ b) = (meet values a && meet values b) := by
  simp [meet]

lemma meet_singleton (values : List Bool) (i : ℕ) :
    meet values [i] = values.getD i false := by
  simp [meet]

lemma meet_congr {a b : List Bool} {atoms : List ℕ}
    (h : ∀ i ∈ atoms, a.getD i false = b.getD i false) : meet a atoms = meet b atoms := by
  induction atoms with
  | nil => rfl
  | cons i atoms ih =>
    change (a.getD i false && meet a atoms) = (b.getD i false && meet b atoms)
    rw [h i (by simp), ih (fun j hj => h j (by simp [hj]))]

lemma meet_extend (values suffix : List Bool) (atoms : List ℕ)
    (h : bounded values.length atoms) : meet (values ++ suffix) atoms = meet values atoms := by
  apply meet_congr
  intro i hi
  exact List.getD_append values suffix false i (h i hi)

lemma wires_length (program : List (List ℕ × List ℕ)) (x : List Bool) :
    (wires program x).length = x.length + program.length := by
  induction program generalizing x with
  | nil => simp [wires]
  | cons g gs ih =>
    change (wires gs (step x g)).length = _
    rw [ih]
    simp [step]
    omega

lemma wires_append (program : List (List ℕ × List ℕ)) (g : List ℕ × List ℕ)
    (x : List Bool) : wires (program ++ [g]) x = step (wires program x) g := by
  simp [wires, List.foldl_append]

lemma original_wires_length (gs : List Gate) (x : List Bool) :
    (Circuit.wires ⟨gs, 0⟩ x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [Circuit.wires]
  | cons g gs ih =>
    change (Circuit.wires ⟨gs, 0⟩ (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)])).length = _
    rw [ih]
    simp
    omega

lemma original_wires_append (gs : List Gate) (g : Gate) (x : List Bool) :
    Circuit.wires ⟨gs ++ [g], 0⟩ x =
      Circuit.wires ⟨gs, 0⟩ x ++
        [g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨gs, 0⟩ x).getD i false)] := by
  simp [Circuit.wires, List.foldl_append]


def Represents (n : ℕ) (gs : List Gate) (program : List (List ℕ × List ℕ))
    (reps : List (List ℕ)) : Prop :=
  wellFormed n program ∧ reps.length = n + gs.length ∧
  (∀ r ∈ reps, bounded (n + program.length) r) ∧
  ∀ x : List Bool, x.length = n →
    reps.map (meet (wires program x)) = Circuit.wires ⟨gs, 0⟩ x

lemma getD_mem {α : Type} (xs : List α) (d : α) {i : ℕ} (hi : i < xs.length) :
    xs.getD i d ∈ xs := by
  simp [hi]

lemma rep_value {values old : List Bool} {reps : List (List ℕ)} {i : ℕ}
    (hrep : reps.map (meet values) = old) (hi : i < reps.length) :
    meet values (reps.getD i []) = old.getD i false := by
  rw [← hrep]
  simp [hi]

lemma getD_snoc {α : Type} (xs : List α) (a d : α) :
    (xs ++ [a]).getD xs.length d = a := by
  simp [List.getD_eq_getElem?_getD]

lemma represents_nil (n : ℕ) :
    Represents n [] [] ((List.range n).map (fun i => [i])) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j hj
    simp at hj
  · simp
  · intro r hr
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
    intro j hj
    have : j = i := by simpa using hj
    subst j
    simpa using List.mem_range.mp hi
  · intro x hx
    simp only [wires, List.foldl_nil, List.map_map, Circuit.wires]
    apply List.ext_getElem
    · simpa using hx.symm
    · intro i hi hx'
      simp only [List.length_map, List.length_range] at hi
      simp [hx, hi, meet]

lemma represents_and {n : ℕ} {gs : List Gate} {program : List (List ℕ × List ℕ)}
    {reps : List (List ℕ)} (hrep : Represents n gs program reps)
    (a b : ℕ) (ha : a < reps.length) (hb : b < reps.length) :
    Represents n (gs ++ [⟨GateOp.and, [a, b]⟩]) program
      (reps ++ [reps.getD a [] ++ reps.getD b []]) := by
  rcases hrep with ⟨hwf, hlen, hbound, hvalues⟩
  refine ⟨hwf, ?_, ?_, ?_⟩
  · simp [hlen, Nat.add_assoc]
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact hbound r hr
    · have heq : r = reps.getD a [] ++ reps.getD b [] := by simpa using hr
      subst r
      intro i hi
      rcases List.mem_append.mp hi with hi | hi
      · exact hbound _ (getD_mem reps [] ha) i hi
      · exact hbound _ (getD_mem reps [] hb) i hi
  · intro x hx
    rw [List.map_append]
    simp only [List.map_singleton, meet_append, original_wires_append]
    rw [hvalues x hx, rep_value (hvalues x hx) ha, rep_value (hvalues x hx) hb]
    simp [GateOp.eval]


lemma wellFormed_append {n : ℕ} {program : List (List ℕ × List ℕ)}
    (hwf : wellFormed n program) (a b : List ℕ)
    (ha : bounded (n + program.length) a) (hb : bounded (n + program.length) b) :
    wellFormed n (program ++ [(a, b)]) := by
  intro j hj
  by_cases hlt : j < program.length
  · rw [List.getD_append program [(a, b)] ([], []) j hlt]
    exact hwf j hlt
  · have heq : j = program.length := by simp only [List.length_append, List.length_singleton] at hj; omega
    subst j
    rw [getD_snoc]
    exact ⟨ha, hb⟩

lemma represents_or {n : ℕ} {gs : List Gate} {program : List (List ℕ × List ℕ)}
    {reps : List (List ℕ)} (hrep : Represents n gs program reps)
    (a b : ℕ) (ha : a < reps.length) (hb : b < reps.length) :
    Represents n (gs ++ [⟨GateOp.or, [a, b]⟩])
      (program ++ [(reps.getD a [], reps.getD b [])])
      (reps ++ [[n + program.length]]) := by
  rcases hrep with ⟨hwf, hlen, hbound, hvalues⟩
  refine ⟨wellFormed_append hwf _ _ (hbound _ (getD_mem reps [] ha))
    (hbound _ (getD_mem reps [] hb)), ?_, ?_, ?_⟩
  · simp [hlen, Nat.add_assoc]
  · intro r hr i hi
    rcases List.mem_append.mp hr with hr | hr
    · have hbnd := hbound r hr i hi
      simp only [List.length_append, List.length_singleton]
      omega
    · have heq : r = [n + program.length] := by simpa using hr
      subst r
      have hieq : i = n + program.length := by simpa using hi
      simp [hieq]
  · intro x hx
    have hmaps : reps.map (meet (wires (program ++ [(reps.getD a [], reps.getD b [])]) x)) =
        reps.map (meet (wires program x)) := by
      apply List.map_congr_left
      intro r hr
      rw [wires_append]
      apply meet_extend
      simpa [wires_length, hx] using hbound r hr
    rw [List.map_append]
    simp only [List.map_singleton, meet_singleton]
    rw [hmaps, hvalues x hx, wires_append]
    change Circuit.wires ⟨gs, 0⟩ x ++
      [(wires program x ++ [meet (wires program x) (reps.getD a []) ||
        meet (wires program x) (reps.getD b [])]).getD (n + program.length) false] = _
    have hwlen : n + program.length = (wires program x).length := by simp [wires_length, hx]
    rw [hwlen, getD_snoc, rep_value (hvalues x hx) ha, rep_value (hvalues x hx) hb]
    simp [original_wires_append, GateOp.eval]


def normalized (n : ℕ) (gs : List Gate) : Prop :=
  ∀ j (hj : j < gs.length), ∃ a b : ℕ,
    gs[j].inputs = [a, b] ∧ a < n + j ∧ b < n + j ∧
      (gs[j].op = GateOp.and ∨ gs[j].op = GateOp.or)

theorem compile (n : ℕ) (gs : List Gate) (hnorm : normalized n gs) :
    ∃ program reps, Represents n gs program reps ∧ program.length = orCount gs := by
  induction gs using List.reverseRecOn with
  | nil =>
    exact ⟨[], (List.range n).map (fun i => [i]), represents_nil n, rfl⟩
  | append_singleton gs g ih =>
    have hprefix : normalized n gs := by
      intro j hj
      obtain ⟨a, b, hp, ha, hb, hop⟩ := hnorm j (by simp; omega)
      exact ⟨a, b, by simpa [List.getElem_append_left hj] using hp, ha, hb,
        by simpa [List.getElem_append_left hj] using hop⟩
    obtain ⟨program, reps, hrep, hcount⟩ := ih hprefix
    obtain ⟨a, b, hp, ha, hb, hop⟩ := hnorm gs.length (by simp)
    have hlast : (gs ++ [g])[gs.length] = g := by simp
    rw [hlast] at hp hop
    have harep : a < reps.length := by rw [hrep.2.1]; exact ha
    have hbrep : b < reps.length := by rw [hrep.2.1]; exact hb
    rcases hop with hand | hor
    · have hg : g = ⟨GateOp.and, [a, b]⟩ := by cases g; simp_all
      subst g
      refine ⟨program, reps ++ [reps.getD a [] ++ reps.getD b []],
        represents_and hrep a b harep hbrep, ?_⟩
      simpa [orCount, isOr] using hcount
    · have hg : g = ⟨GateOp.or, [a, b]⟩ := by cases g; simp_all
      subst g
      refine ⟨program ++ [(reps.getD a [], reps.getD b [])],
        reps ++ [[n + program.length]], represents_or hrep a b harep hbrep, ?_⟩
      simpa [orCount, isOr] using hcount

theorem circuit_translation (n : ℕ) (C : Circuit) (hnorm : normalized n C.gates)
    (hout : C.output < n + C.gates.length) :
    ∃ program output, program.length = orCount C.gates ∧ wellFormed n program ∧
      bounded (n + program.length) output ∧
      ∀ x : List Bool, x.length = n → eval program output x = C.eval x := by
  obtain ⟨program, reps, hrep, hcount⟩ := compile n C.gates hnorm
  have ho : C.output < reps.length := by rw [hrep.2.1]; exact hout
  refine ⟨program, reps.getD C.output [], hcount, hrep.1,
    hrep.2.2.1 _ (getD_mem reps [] ho), ?_⟩
  intro x hx
  exact rep_value (hrep.2.2.2 x hx) ho


lemma meet_wires (program : List (List ℕ × List ℕ)) (x : List Bool) (atoms : List ℕ)
    (hbound : bounded x.length atoms) : meet (wires program x) atoms = meet x atoms := by
  induction program generalizing x with
  | nil => rfl
  | cons g gs ih =>
    change meet (wires gs (step x g)) atoms = meet x atoms
    rw [ih]
    · exact meet_extend x _ atoms hbound
    · intro i hi
      have hb := hbound i hi
      simp only [step, List.length_append, List.length_singleton]
      omega

lemma eval_append (n : ℕ) (program suffix : List (List ℕ × List ℕ)) (output : List ℕ)
    (hbound : bounded (n + program.length) output) (x : List Bool) (hx : x.length = n) :
    eval (program ++ suffix) output x = eval program output x := by
  unfold eval
  have heq : wires (program ++ suffix) x = wires suffix (wires program x) := by
    simp [wires, List.foldl_append]
  rw [heq]
  apply meet_wires
  simpa [wires_length, hx] using hbound

theorem pad_by (n : ℕ) (program : List (List ℕ × List ℕ)) (output : List ℕ)
    (hn : 0 < n) (hwf : wellFormed n program)
    (hbound : bounded (n + program.length) output) (extra : ℕ) :
    ∃ padded, padded.length = program.length + extra ∧ wellFormed n padded ∧
      bounded (n + padded.length) output ∧
      ∀ x : List Bool, x.length = n → eval padded output x = eval program output x := by
  induction extra generalizing program with
  | zero => exact ⟨program, by simp, hwf, hbound, fun _ _ => rfl⟩
  | succ extra ih =>
    let next := program ++ [([0], [0])]
    have hzero : bounded (n + program.length) [0] := by
      intro i hi
      have : i = 0 := by simpa using hi
      omega
    have hnext : wellFormed n next := wellFormed_append hwf [0] [0] hzero hzero
    have hbnext : bounded (n + next.length) output := by
      intro i hi
      have hb := hbound i hi
      simp only [next, List.length_append, List.length_singleton]
      omega
    obtain ⟨padded, hlen, hpwf, hpbound, hpeval⟩ := ih next hnext hbnext
    refine ⟨padded, ?_, hpwf, hpbound, ?_⟩
    · simp only [next, List.length_append, List.length_singleton] at hlen
      omega
    · intro x hx
      exact (hpeval x hx).trans (eval_append n program [([0], [0])] output hbound x hx)

theorem pad_to (n : ℕ) (program : List (List ℕ × List ℕ)) (output : List ℕ)
    (hn : 0 < n) (hwf : wellFormed n program)
    (hbound : bounded (n + program.length) output) (k : ℕ) (hk : program.length ≤ k) :
    ∃ padded, padded.length = k ∧ wellFormed n padded ∧ bounded (n + k) output ∧
      ∀ x : List Bool, x.length = n → eval padded output x = eval program output x := by
  obtain ⟨padded, hlen, hpwf, hpbound, hpeval⟩ := pad_by n program output hn hwf hbound (k - program.length)
  have heq : padded.length = k := by omega
  exact ⟨padded, heq, hpwf, heq ▸ hpbound, hpeval⟩


lemma meet_eq_selection (values : List Bool) (atoms : List ℕ) (bound : ℕ)
    (hbound : bounded bound atoms) :
    meet values atoms = (List.range bound).all
      (fun i => if i ∈ atoms then values.getD i false else true) := by
  apply Bool.eq_iff_iff.mpr
  simp only [meet, List.all_eq_true]
  constructor
  · intro h i hi
    by_cases hm : i ∈ atoms
    · simpa [hm] using h i hm
    · simp [hm]
  · intro h i hi
    have hv := h i (List.mem_range.mpr (hbound i hi))
    simpa [hi] using hv


def mask8 (atoms : List ℕ) : BitVec 8 :=
  BitVec.ofBool (decide (7 ∈ atoms)) ++ BitVec.ofBool (decide (6 ∈ atoms)) ++
  BitVec.ofBool (decide (5 ∈ atoms)) ++ BitVec.ofBool (decide (4 ∈ atoms)) ++
  BitVec.ofBool (decide (3 ∈ atoms)) ++ BitVec.ofBool (decide (2 ∈ atoms)) ++
  BitVec.ofBool (decide (1 ∈ atoms)) ++ BitVec.ofBool (decide (0 ∈ atoms))

lemma mask8_get (atoms : List ℕ) (i : ℕ) (hi : i < 8) :
    (mask8 atoms).getLsbD i = decide (i ∈ atoms) := by
  have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [mask8, BitVec.getLsbD_append] <;> simp

lemma meet_eq_mask8 (values : List Bool) (atoms : List ℕ) (bound : ℕ)
    (hbound : bounded bound atoms) (hsmall : bound ≤ 8) :
    meet values atoms = (List.range bound).all
      (fun i => if (mask8 atoms).getLsbD i then values.getD i false else true) := by
  apply Bool.eq_iff_iff.mpr
  simp only [meet, List.all_eq_true]
  constructor
  · intro h i hi
    rw [mask8_get atoms i (by have := List.mem_range.mp hi; omega)]
    by_cases hm : i ∈ atoms
    · simpa [hm] using h i hm
    · simp [hm]
  · intro h i hi
    have hv := h i (List.mem_range.mpr (hbound i hi))
    rw [mask8_get atoms i (by have := hbound i hi; omega)] at hv
    simpa [hi] using hv


def vmeet (values : List (BitVec 10)) (atoms : List ℕ) : BitVec 10 :=
  atoms.foldr (fun i rest => values.getD i 0 &&& rest) (BitVec.allOnes 10)

def vstep (values : List (BitVec 10)) (g : List ℕ × List ℕ) : List (BitVec 10) :=
  values ++ [vmeet values g.1 ||| vmeet values g.2]

def vwires (program : List (List ℕ × List ℕ)) (x : List (BitVec 10)) : List (BitVec 10) :=
  program.foldl vstep x

def veval (program : List (List ℕ × List ℕ)) (output : List ℕ) (x : List (BitVec 10)) : BitVec 10 :=
  vmeet (vwires program x) output

lemma band_bits (atoms : List ℕ) (f : ℕ → BitVec 10) (i : ℕ) (hi : i < 10) :
    (atoms.foldr (fun a rest => f a &&& rest) (BitVec.allOnes 10)).getLsbD i =
      atoms.all (fun a => (f a).getLsbD i) := by
  induction atoms with
  | nil =>
    change (BitVec.allOnes 10).getLsbD i = true
    rw [BitVec.getLsbD_allOnes]
    simp [hi]
  | cons a atoms ih =>
    simp only [List.foldr_cons, BitVec.getLsbD_and, List.all_cons]
    rw [ih]

lemma vmeet_bits (values : List (BitVec 10)) (atoms : List ℕ) (i : ℕ) (hi : i < 10) :
    (vmeet values atoms).getLsbD i = meet (values.map (fun v => v.getLsbD i)) atoms := by
  rw [vmeet, band_bits atoms _ i hi]
  unfold meet
  apply congrArg (fun f : ℕ → Bool => atoms.all f)
  funext a
  simpa using (List.getD_map values (0 : BitVec 10) (n := a) (fun v => v.getLsbD i)).symm

lemma vwires_bits (program : List (List ℕ × List ℕ)) (values : List (BitVec 10))
    (i : ℕ) (hi : i < 10) :
    (vwires program values).map (fun v => v.getLsbD i) =
      wires program (values.map (fun v => v.getLsbD i)) := by
  induction program generalizing values with
  | nil => rfl
  | cons g gs ih =>
    change (vwires gs (vstep values g)).map (fun v => v.getLsbD i) =
      wires gs (step (values.map (fun v => v.getLsbD i)) g)
    rw [ih]
    apply congrArg (wires gs)
    simp only [vstep, step, List.map_append, List.map_singleton,
      BitVec.getLsbD_or, vmeet_bits values g.1 i hi, vmeet_bits values g.2 i hi]

lemma veval_bits (program : List (List ℕ × List ℕ)) (output : List ℕ)
    (values : List (BitVec 10)) (i : ℕ) (hi : i < 10) :
    (veval program output values).getLsbD i =
      eval program output (values.map (fun v => v.getLsbD i)) := by
  rw [veval, vmeet_bits _ output i hi, vwires_bits program values i hi]
  rfl

def vselect (values : List (BitVec 10)) (bound : ℕ) (p : BitVec 8) : BitVec 10 :=
  (List.range bound).foldr (fun i rest =>
    (if p.getLsbD i then values.getD i 0 else BitVec.allOnes 10) &&& rest) (BitVec.allOnes 10)

lemma vmeet_eq_mask8 (values : List (BitVec 10)) (atoms : List ℕ) (bound : ℕ)
    (hbound : bounded bound atoms) (hsmall : bound ≤ 8) :
    vmeet values atoms = vselect values bound (mask8 atoms) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [vmeet_bits values atoms i hi, meet_eq_mask8 _ atoms bound hbound hsmall]
  rw [vselect, band_bits _ _ i hi]
  apply congrArg (fun f : ℕ → Bool => (List.range bound).all f)
  funext a
  cases hmask : (mask8 atoms).getLsbD a with
  | false =>
    change true = (BitVec.allOnes 10).getLsbD i
    rw [BitVec.getLsbD_allOnes]
    simp [hi]
  | true =>
    simpa [hmask] using List.getD_map values (0 : BitVec 10) (n := a) (fun v => v.getLsbD i)


def cycleInputs : List (BitVec 10) := [113, 387, 550, 204, 792]

def FiniteObstruction : Prop := ∀ a b c d e f o : BitVec 8,
  let v := vselect cycleInputs 5 a ||| vselect cycleInputs 5 b
  let w := vselect (cycleInputs ++ [v]) 6 c ||| vselect (cycleInputs ++ [v]) 6 d
  let z := vselect (cycleInputs ++ [v] ++ [w]) 7 e ||| vselect (cycleInputs ++ [v] ++ [w]) 7 f
  vselect (cycleInputs ++ [v] ++ [w] ++ [z]) 8 o ≠ 31

lemma list_three {α : Type} (l : List α) (hlen : l.length = 3) :
    ∃ a b c, l = [a, b, c] := by
  cases l with
  | nil => simp at hlen
  | cons a l =>
    cases l with
    | nil => simp at hlen
    | cons b l =>
      cases l with
      | nil => simp at hlen
      | cons c l =>
        have hempty : l = [] := by
          cases l with
          | nil => rfl
          | cons d l => simp only [List.length_cons] at hlen; omega
        subst l
        exact ⟨a, b, c, rfl⟩

theorem three_program_obstruction (hfinite : FiniteObstruction)
    (program : List (List ℕ × List ℕ)) (output : List ℕ)
    (hlen : program.length = 3) (hwf : wellFormed 5 program) (houtput : bounded 8 output) :
    veval program output cycleInputs ≠ 31 := by
  obtain ⟨g0, g1, g2, rfl⟩ := list_three program hlen
  have h0 : bounded 5 g0.1 ∧ bounded 5 g0.2 := by simpa using hwf 0 (by simp)
  have h1 : bounded 6 g1.1 ∧ bounded 6 g1.2 := by simpa using hwf 1 (by simp)
  have h2 : bounded 7 g2.1 ∧ bounded 7 g2.2 := by simpa using hwf 2 (by simp)
  let v := vselect cycleInputs 5 (mask8 g0.1) ||| vselect cycleInputs 5 (mask8 g0.2)
  let w := vselect (cycleInputs ++ [v]) 6 (mask8 g1.1) ||| vselect (cycleInputs ++ [v]) 6 (mask8 g1.2)
  let z := vselect (cycleInputs ++ [v] ++ [w]) 7 (mask8 g2.1) |||
    vselect (cycleInputs ++ [v] ++ [w]) 7 (mask8 g2.2)
  have heval : veval [g0, g1, g2] output cycleInputs =
      vselect (cycleInputs ++ [v] ++ [w] ++ [z]) 8 (mask8 output) := by
    simp only [veval, vwires, List.foldl_cons, List.foldl_nil, vstep]
    rw [vmeet_eq_mask8 cycleInputs g0.1 5 h0.1 (by decide),
      vmeet_eq_mask8 cycleInputs g0.2 5 h0.2 (by decide)]
    change vmeet (cycleInputs ++ [v] ++
      [vmeet (cycleInputs ++ [v]) g1.1 ||| vmeet (cycleInputs ++ [v]) g1.2] ++
      [vmeet (cycleInputs ++ [v] ++
        [vmeet (cycleInputs ++ [v]) g1.1 ||| vmeet (cycleInputs ++ [v]) g1.2]) g2.1 |||
       vmeet (cycleInputs ++ [v] ++
        [vmeet (cycleInputs ++ [v]) g1.1 ||| vmeet (cycleInputs ++ [v]) g1.2]) g2.2]) output = _
    rw [vmeet_eq_mask8 (cycleInputs ++ [v]) g1.1 6 h1.1 (by decide),
      vmeet_eq_mask8 (cycleInputs ++ [v]) g1.2 6 h1.2 (by decide)]
    change vmeet (cycleInputs ++ [v] ++ [w] ++
      [vmeet (cycleInputs ++ [v] ++ [w]) g2.1 ||| vmeet (cycleInputs ++ [v] ++ [w]) g2.2]) output = _
    rw [vmeet_eq_mask8 (cycleInputs ++ [v] ++ [w]) g2.1 7 h2.1 (by decide),
      vmeet_eq_mask8 (cycleInputs ++ [v] ++ [w]) g2.2 7 h2.2 (by decide)]
    exact vmeet_eq_mask8 (cycleInputs ++ [v] ++ [w] ++ [z]) output 8 houtput le_rfl
  rw [heval]
  exact hfinite (mask8 g0.1) (mask8 g0.2) (mask8 g1.1) (mask8 g1.2)
    (mask8 g2.1) (mask8 g2.2) (mask8 output)

theorem circuit_four_ors (hfinite : FiniteObstruction) (C : Circuit)
    (hnorm : normalized 5 C.gates) (hout : C.output < 5 + C.gates.length)
    (hvalues : ∀ i : Fin 10,
      C.eval (cycleInputs.map (fun v => v.getLsbD i.val)) = (31 : BitVec 10).getLsbD i.val) :
    4 ≤ orCount C.gates := by
  by_contra hlt
  have hcount : orCount C.gates ≤ 3 := by omega
  obtain ⟨program, output, hlen, hwf, hbound, heval⟩ := circuit_translation 5 C hnorm hout
  obtain ⟨padded, hpadlen, hpadwf, hpadbound, hpadeval⟩ :=
    pad_to 5 program output (by decide) hwf hbound 3 (by omega)
  have hvec : veval padded output cycleInputs = 31 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [veval_bits padded output cycleInputs i hi]
    have hsize : (cycleInputs.map (fun v => v.getLsbD i)).length = 5 := by simp [cycleInputs]
    rw [hpadeval _ hsize, heval _ hsize]
    exact hvalues ⟨i, hi⟩
  exact three_program_obstruction hfinite padded output hpadlen hpadwf hpadbound hvec


def select8 (p : BitVec 8) (i : Nat) (v : BitVec 10) : BitVec 10 :=
  if p.getLsbD i then v else 1023

def expr0 (p : BitVec 8) : BitVec 10 :=
  select8 p 0 113 &&& select8 p 1 387 &&& select8 p 2 550 &&&
    select8 p 3 204 &&& select8 p 4 792

def expr1 (p : BitVec 8) (v : BitVec 10) : BitVec 10 := expr0 p &&& select8 p 5 v

def expr2 (p : BitVec 8) (v w : BitVec 10) : BitVec 10 := expr1 p v &&& select8 p 6 w

def expr3 (p : BitVec 8) (v w z : BitVec 10) : BitVec 10 := expr2 p v w &&& select8 p 7 z

lemma and1023 (v : BitVec 10) : BitVec.and v (BitVec.ofNat 10 1023) = v := BitVec.and_allOnes

lemma vselect_five (p : BitVec 8) : vselect cycleInputs 5 p = expr0 p := by
  simp [vselect, cycleInputs, List.range_succ, expr0, select8, BitVec.and_assoc]
  simp only [← BitVec.and_assoc]
  exact BitVec.and_allOnes

lemma vselect_six (p : BitVec 8) (v : BitVec 10) :
    vselect (cycleInputs ++ [v]) 6 p = expr1 p v := by
  simp [vselect, cycleInputs, List.range_succ, expr1, expr0, select8, BitVec.and_assoc]
  simp only [← BitVec.and_assoc]
  exact BitVec.and_allOnes

lemma vselect_seven (p : BitVec 8) (v w : BitVec 10) :
    vselect (cycleInputs ++ [v] ++ [w]) 7 p = expr2 p v w := by
  simp [vselect, cycleInputs, List.range_succ, expr2, expr1, expr0, select8, BitVec.and_assoc]
  simp only [← BitVec.and_assoc]
  exact BitVec.and_allOnes

lemma vselect_eight (p : BitVec 8) (v w z : BitVec 10) :
    vselect (cycleInputs ++ [v] ++ [w] ++ [z]) 8 p = expr3 p v w z := by
  simp [vselect, cycleInputs, List.range_succ, expr3, expr2, expr1, expr0, select8, BitVec.and_assoc]
  simp only [← BitVec.and_assoc]
  exact BitVec.and_allOnes

lemma finiteObstruction_of_expanded
    (h : ∀ a b c d e f o : BitVec 8,
      let v := expr0 a ||| expr0 b
      let w := expr1 c v ||| expr1 d v
      let z := expr2 e v w ||| expr2 f v w
      expr3 o v w z ≠ 31) : FiniteObstruction := by
  intro a b c d e f o
  simp only [vselect_five, vselect_six, vselect_seven, vselect_eight]
  exact h a b c d e f o


def cycleTruth (x : Fin 5 → Bool) : Bool :=
  decide (∃ u v : Fin 5, (u + 1 = v ∨ v + 1 = u) ∧ x u = true ∧ x v = true)

lemma cycle_columns : ∀ i : Fin 10,
    cycleTruth (fun j : Fin 5 => (cycleInputs.getD j.val 0).getLsbD i.val) =
      (31 : BitVec 10).getLsbD i.val := by decide

lemma cycle_test_lists : ∀ i : Fin 10,
    List.ofFn (fun j : Fin 5 => (cycleInputs.getD j.val 0).getLsbD i.val) =
      cycleInputs.map (fun v => v.getLsbD i.val) := by decide

theorem cycle_four_ors (hfinite : FiniteObstruction) (C : Circuit)
    (hnorm : normalized 5 C.gates)
    (hcomputes : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = cycleTruth x) :
    4 ≤ orCount C.gates := by
  have hvalues : ∀ i : Fin 10,
      C.eval (cycleInputs.map (fun v => v.getLsbD i.val)) = (31 : BitVec 10).getLsbD i.val := by
    intro i
    rw [← cycle_test_lists i, hcomputes]
    exact cycle_columns i
  have hout : C.output < 5 + C.gates.length := by
    by_contra hbad
    have htest := hvalues (0 : Fin 10)
    have htrue : (31 : BitVec 10).getLsbD (0 : Fin 10).val = true := by decide
    rw [htrue] at htest
    have hfalse : C.eval (cycleInputs.map (fun v => v.getLsbD 0)) = false := by
      apply List.getD_eq_default
      change (Circuit.wires ⟨C.gates, 0⟩ (cycleInputs.map (fun v => v.getLsbD 0))).length ≤ C.output
      rw [original_wires_length]
      simp only [List.length_map, cycleInputs, List.length_cons, List.length_nil] at *
      omega
    exact Bool.noConfusion (hfalse.symm.trans htest)
  exact circuit_four_ors hfinite C hnorm hout hvalues

end PEqualNP.Outside.L_meta_1031_aux.CompactOr

namespace PEqualNP.Outside.L_meta_1031_aux.CompactOr

theorem certified_finite_obstruction : FiniteObstruction := by
  apply finiteObstruction_of_expanded
  exact PEqualNP.Outside.L_meta_1031_aux.SemanticCertificate.semantic_soundness
    PEqualNP.Outside.L_meta_1031_aux.SemanticCertificate.all_first_cases

theorem certified_cycle_four_ors (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hnorm : normalized 5 C.gates)
    (hcomputes : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = cycleTruth x) :
    4 ≤ orCount C.gates :=
  cycle_four_ors certified_finite_obstruction C hnorm hcomputes

end PEqualNP.Outside.L_meta_1031_aux.CompactOr


namespace PEqualNP.Outside.L_meta_1031_aux.CycleAndBound

open PEqualNP.CircuitLowerBounds

/- Generic zero-family bound adapted from checked L_meta_267. -/

-- One evaluation step: the gate adds one wire.
def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stp x := rfl

theorem getD_ge (W : List Bool) (i : ℕ) (h : W.length ≤ i) : W.getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

theorem getD_ofFn {m : ℕ} (x : Fin m → Bool) (i : ℕ) (h : i < m) :
    (List.ofFn x).getD i false = x ⟨i, h⟩ := by
  simp [List.getD_eq_getElem?_getD, h]

theorem getD_app (W : List Bool) (v : Bool) (i : ℕ) :
    (W ++ [v]).getD i false
      = if i < W.length then W.getD i false else if i = W.length then v else false := by
  split_ifs with h1 h2
  · exact List.getD_append _ _ _ _ h1
  · subst h2
    simp [List.getD_eq_getElem?_getD]
  · exact getD_ge _ _ (by simp; omega)

-- The join of two inputs.
def jn {n : ℕ} (z z' : Fin n → Bool) : Fin n → Bool := fun i => z i || z' i

-- An AND gate that really reads two wires.
def realAnd (g : Gate) : Bool :=
  match g.op with
  | GateOp.and => decide (g.inputs.length = 2)
  | _ => false

theorem realAnd_spec (g : Gate) (h : realAnd g = true) : ∃ a b, g = ⟨GateOp.and, [a, b]⟩ := by
  obtain ⟨op, l⟩ := g
  cases op <;> simp [realAnd] at h
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp h
  exact ⟨a, b, rfl⟩

theorem eval_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (f f' : ℕ → Bool)
    (h : ∀ i, f i = true → f' i = true) :
    g.op.eval (g.inputs.map f) = true → g.op.eval (g.inputs.map f') = true := by
  rcases hg with e | e
  · rw [e]
    simp only [GateOp.eval]
    intro H
    rw [List.all_eq_true] at H ⊢
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact h i (H _ (List.mem_map.mpr ⟨i, hi, rfl⟩))
  · rw [e]
    simp only [GateOp.eval]
    intro H
    rw [List.any_eq_true] at H ⊢
    obtain ⟨b, hb, hbt⟩ := H
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact ⟨f' i, List.mem_map.mpr ⟨i, hi, rfl⟩, h i hbt⟩

-- Raising wire values never lowers a later wire of a circuit of AND and OR gates.
theorem mono_fold : ∀ (gs : List Gate) (W W' : List Bool), W.length = W'.length →
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    (∀ i, W.getD i false = true → W'.getD i false = true) →
    ∀ i, (gs.foldl stp W).getD i false = true → (gs.foldl stp W').getD i false = true := by
  intro gs
  induction gs with
  | nil => intro W W' _ _ h i; exact h i
  | cons g gs ih =>
    intro W W' hl hops h
    simp only [List.foldl_cons]
    apply ih (stp W g) (stp W' g) (by simp [stp, hl]) (fun g' hg' => hops g' (by simp [hg']))
    intro i
    simp only [stp]
    rw [getD_app, getD_app, ← hl]
    split_ifs
    · exact h i
    · exact eval_mono g (hops g (by simp)) _ _ h
    · exact id

theorem any_or (l : List ℕ) (f1 f2 : ℕ → Bool) :
    (l.map (fun i => f1 i || f2 i)).any id = ((l.map f1).any id || (l.map f2).any id) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.any_cons, ih, id]
    generalize (l.map f1).any id = X
    generalize (l.map f2).any id = Y
    cases f1 a <;> cases f2 a <;> cases X <;> cases Y <;> rfl

-- A gate that is not a real AND gate commutes with the join.
theorem eval_join (g : Gate) (hm : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hr : realAnd g = false) (f f1 f2 : ℕ → Bool) (h : ∀ i, f i = (f1 i || f2 i)) :
    g.op.eval (g.inputs.map f)
      = (g.op.eval (g.inputs.map f1) || g.op.eval (g.inputs.map f2)) := by
  have e : g.inputs.map f = g.inputs.map (fun i => f1 i || f2 i) :=
    List.map_congr_left (fun i _ => h i)
  rw [e]
  obtain ⟨op, l⟩ := g
  obtain ⟨hop, hlen⟩ := hm
  simp only at hop hlen
  rcases hop with rfl | rfl
  · rcases l with _ | ⟨i, _ | ⟨j, _ | ⟨k, l⟩⟩⟩
    · simp [GateOp.eval]
    · simp [GateOp.eval]
    · simp [realAnd] at hr
    · simp at hlen
  · simp only [GateOp.eval]
    exact any_or l f1 f2

theorem join_fold : ∀ (gs : List Gate) (W W1 W2 : List Bool), W.length = W1.length →
    W.length = W2.length →
    (∀ g ∈ gs, ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      realAnd g = false) →
    (∀ i, W.getD i false = (W1.getD i false || W2.getD i false)) →
    ∀ i, (gs.foldl stp W).getD i false
      = ((gs.foldl stp W1).getD i false || (gs.foldl stp W2).getD i false) := by
  intro gs
  induction gs with
  | nil => intro W W1 W2 _ _ _ h i; exact h i
  | cons g gs ih =>
    intro W W1 W2 hl1 hl2 hg h
    simp only [List.foldl_cons]
    apply ih (stp W g) (stp W1 g) (stp W2 g) (by simp [stp, hl1]) (by simp [stp, hl2])
      (fun g' hg' => hg g' (by simp [hg']))
    intro i
    simp only [stp]
    rw [getD_app, getD_app, getD_app, ← hl1, ← hl2]
    split_ifs
    · exact h i
    · exact eval_join g (hg g (by simp)).1 (hg g (by simp)).2 _ _ _ h
    · rfl

theorem ofFn_jn {n : ℕ} (z z' : Fin n → Bool) (i : ℕ) :
    (List.ofFn (jn z z')).getD i false
      = ((List.ofFn z).getD i false || (List.ofFn z').getD i false) := by
  by_cases h : i < n
  · rw [getD_ofFn _ i h, getD_ofFn _ i h, getD_ofFn _ i h]
    rfl
  · rw [getD_ge _ _ (by simp; omega), getD_ge _ _ (by simp; omega),
      getD_ge _ _ (by simp; omega)]
    rfl

-- Without a real AND gate the circuit commutes with joins, so at most one member of a
-- family of zeros with pairwise true joins exists.
theorem bound0 {n : ℕ} {ι : Type} [DecidableEq ι] (Z : ι → Fin n → Bool) (o : ℕ)
    (gs : List Gate)
    (hm : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (h0 : gs.countP realAnd = 0) (S : Finset ι)
    (hz : ∀ s ∈ S, (gs.foldl stp (List.ofFn (Z s))).getD o false = false)
    (hj : ∀ s ∈ S, ∀ t ∈ S, s ≠ t →
      (gs.foldl stp (List.ofFn (jn (Z s) (Z t)))).getD o false = true) :
    S.card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro s hs t ht
  by_contra hne
  have h1 := hj s hs t ht hne
  have hreal : ∀ g ∈ gs, realAnd g = false := by
    intro g hg
    have := List.countP_eq_zero.mp h0 g hg
    simpa using this
  rw [join_fold gs _ (List.ofFn (Z s)) (List.ofFn (Z t)) (by simp) (by simp)
    (fun g hg => ⟨hm g hg, hreal g hg⟩) (ofFn_jn (Z s) (Z t)) o, hz s hs, hz t ht] at h1
  simp at h1

-- Replacing a real AND gate by one of its two operands.
theorem and_zero (W : List Bool) (a b o : ℕ) (post : List Gate)
    (h : (post.foldl stp (stp W ⟨GateOp.and, [a, b]⟩)).getD o false = false) :
    (post.foldl stp (stp W ⟨GateOp.and, [a]⟩)).getD o false = false ∨
      (post.foldl stp (stp W ⟨GateOp.and, [b]⟩)).getD o false = false := by
  have e1 : stp W ⟨GateOp.and, [a, b]⟩ = W ++ [W.getD a false && W.getD b false] := by
    simp [stp, GateOp.eval]
  have e2 : stp W ⟨GateOp.and, [a]⟩ = W ++ [W.getD a false] := by simp [stp, GateOp.eval]
  have e3 : stp W ⟨GateOp.and, [b]⟩ = W ++ [W.getD b false] := by simp [stp, GateOp.eval]
  rw [e1] at h
  rw [e2, e3]
  cases ha : W.getD a false
  · rw [ha] at h
    exact Or.inl h
  · rw [ha] at h
    exact Or.inr h

theorem and_up (W : List Bool) (a b o : ℕ) (post : List Gate)
    (hops : ∀ g ∈ post, g.op = GateOp.and ∨ g.op = GateOp.or)
    (h : (post.foldl stp (stp W ⟨GateOp.and, [a, b]⟩)).getD o false = true) :
    (post.foldl stp (stp W ⟨GateOp.and, [a]⟩)).getD o false = true ∧
      (post.foldl stp (stp W ⟨GateOp.and, [b]⟩)).getD o false = true := by
  have e1 : stp W ⟨GateOp.and, [a, b]⟩ = W ++ [W.getD a false && W.getD b false] := by
    simp [stp, GateOp.eval]
  have e2 : stp W ⟨GateOp.and, [a]⟩ = W ++ [W.getD a false] := by simp [stp, GateOp.eval]
  have e3 : stp W ⟨GateOp.and, [b]⟩ = W ++ [W.getD b false] := by simp [stp, GateOp.eval]
  rw [e1] at h
  rw [e2, e3]
  constructor
  · apply mono_fold post _ _ (by simp) hops _ o h
    intro i
    rw [getD_app, getD_app]
    split_ifs
    · exact id
    · intro hv
      rw [Bool.and_eq_true] at hv
      exact hv.1
    · exact id
  · apply mono_fold post _ _ (by simp) hops _ o h
    intro i
    rw [getD_app, getD_app]
    split_ifs
    · exact id
    · intro hv
      rw [Bool.and_eq_true] at hv
      exact hv.2
    · exact id

-- A family of zeros whose pairwise joins are true has at most 2 ^ r members when the circuit
-- has at most r real AND gates.
theorem bound {n : ℕ} {ι : Type} [DecidableEq ι] (Z : ι → Fin n → Bool) (o : ℕ) :
    ∀ (r : ℕ) (gs : List Gate),
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
      gs.countP realAnd ≤ r → ∀ S : Finset ι,
      (∀ s ∈ S, (gs.foldl stp (List.ofFn (Z s))).getD o false = false) →
      (∀ s ∈ S, ∀ t ∈ S, s ≠ t →
        (gs.foldl stp (List.ofFn (jn (Z s) (Z t)))).getD o false = true) →
      S.card ≤ 2 ^ r := by
  intro r
  induction r with
  | zero =>
    intro gs hm hc S hz hj
    have := bound0 Z o gs hm (by omega) S hz hj
    simpa using this
  | succ r ih =>
    intro gs hm hc S hz hj
    by_cases h0 : gs.countP realAnd = 0
    · have h1 := bound0 Z o gs hm h0 S hz hj
      have h2 : 1 ≤ 2 ^ (r + 1) := Nat.one_le_two_pow
      omega
    · have hex : ∃ g ∈ gs, realAnd g = true := by
        by_contra hno
        apply h0
        apply List.countP_eq_zero.mpr
        intro g hg hp
        exact hno ⟨g, hg, hp⟩
      obtain ⟨g, hg, hreal⟩ := hex
      obtain ⟨a, b, rfl⟩ := realAnd_spec g hreal
      obtain ⟨pre, post, rfl⟩ := List.append_of_mem hg
      have hpost : ∀ g ∈ post, g.op = GateOp.and ∨ g.op = GateOp.or :=
        fun g hg' => (hm g (by simp [hg'])).1
      have hcount : ∀ c : ℕ, (pre ++ (⟨GateOp.and, [c]⟩ : Gate) :: post).countP realAnd ≤ r := by
        intro c
        have e1 : (pre ++ (⟨GateOp.and, [a, b]⟩ : Gate) :: post).countP realAnd
            = pre.countP realAnd + (post.countP realAnd + 1) := by
          rw [List.countP_append, List.countP_cons_of_pos (by simp [realAnd])]
        have e2 : (pre ++ (⟨GateOp.and, [c]⟩ : Gate) :: post).countP realAnd
            = pre.countP realAnd + post.countP realAnd := by
          rw [List.countP_append, List.countP_cons_of_neg (by simp [realAnd])]
        omega
      have hmono : ∀ c : ℕ, ∀ g ∈ pre ++ (⟨GateOp.and, [c]⟩ : Gate) :: post,
          (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
        intro c g hg'
        rcases List.mem_append.mp hg' with h | h
        · exact hm g (by simp [h])
        · rcases List.mem_cons.mp h with rfl | h
          · exact ⟨Or.inl rfl, by simp⟩
          · exact hm g (by simp [h])
      simp only [List.foldl_append, List.foldl_cons] at hz hj
      have ha := ih (pre ++ (⟨GateOp.and, [a]⟩ : Gate) :: post) (hmono a) (hcount a)
        (S.filter (fun s => (post.foldl stp (stp (pre.foldl stp (List.ofFn (Z s)))
          ⟨GateOp.and, [a]⟩)).getD o false = false))
        (by
          intro s hs
          simp only [List.foldl_append, List.foldl_cons]
          exact (Finset.mem_filter.mp hs).2)
        (by
          intro s hs t ht hne
          simp only [List.foldl_append, List.foldl_cons]
          exact (and_up _ a b o post hpost
            (hj s (Finset.mem_filter.mp hs).1 t (Finset.mem_filter.mp ht).1 hne)).1)
      have hb := ih (pre ++ (⟨GateOp.and, [b]⟩ : Gate) :: post) (hmono b) (hcount b)
        (S.filter (fun s => (post.foldl stp (stp (pre.foldl stp (List.ofFn (Z s)))
          ⟨GateOp.and, [b]⟩)).getD o false = false))
        (by
          intro s hs
          simp only [List.foldl_append, List.foldl_cons]
          exact (Finset.mem_filter.mp hs).2)
        (by
          intro s hs t ht hne
          simp only [List.foldl_append, List.foldl_cons]
          exact (and_up _ a b o post hpost
            (hj s (Finset.mem_filter.mp hs).1 t (Finset.mem_filter.mp ht).1 hne)).2)
      have hsub : S ⊆ S.filter (fun s => (post.foldl stp (stp (pre.foldl stp (List.ofFn (Z s)))
            ⟨GateOp.and, [a]⟩)).getD o false = false) ∪
          S.filter (fun s => (post.foldl stp (stp (pre.foldl stp (List.ofFn (Z s)))
            ⟨GateOp.and, [b]⟩)).getD o false = false) := by
        intro s hs
        rcases and_zero _ a b o post (hz s hs) with h | h
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hs, h⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hs, h⟩)
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_union_le
        (S.filter (fun s => (post.foldl stp (stp (pre.foldl stp (List.ofFn (Z s)))
          ⟨GateOp.and, [a]⟩)).getD o false = false))
        (S.filter (fun s => (post.foldl stp (stp (pre.foldl stp (List.ofFn (Z s)))
          ⟨GateOp.and, [b]⟩)).getD o false = false))
      have h3 : 2 ^ (r + 1) = 2 ^ r + 2 ^ r := by simp [Nat.pow_succ, Nat.mul_two]
      omega


abbrev adjacent (u v : Fin 5) : Prop := u + 1 = v ∨ v + 1 = u

def independentInput (p : Fin 5) : Fin 5 → Bool := fun v => decide (v = p ∨ v = p + 2)

lemma independentInput_false : ∀ p : Fin 5,
    ¬ ∃ u v : Fin 5, adjacent u v ∧ independentInput p u = true ∧
      independentInput p v = true := by decide

lemma independentInput_join_true : ∀ p q : Fin 5, p ≠ q → ∃ u v : Fin 5,
    adjacent u v ∧ jn (independentInput p) (independentInput q) u = true ∧
      jn (independentInput p) (independentInput q) v = true := by decide

lemma cycle_requires_three_binary_ands (C : Circuit)
    (mono : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (computes : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) =
      decide (∃ u v : Fin 5, adjacent u v ∧ x u = true ∧ x v = true)) :
    3 ≤ C.gates.countP realAnd := by
  by_contra hn
  have hc : C.gates.countP realAnd ≤ 2 := by omega
  have hb := bound independentInput C.output 2 C.gates mono hc
    (Finset.univ : Finset (Fin 5))
    (by
      intro p _
      have h := computes (independentInput p)
      simp only [independentInput_false p, decide_false] at h
      simpa only [Circuit.eval, wires_eq] using h)
    (by
      intro p _ q _ hpq
      have h := computes (jn (independentInput p) (independentInput q))
      simp only [independentInput_join_true p q hpq, decide_true] at h
      simpa only [Circuit.eval, wires_eq] using h)
  norm_num at hb

end PEqualNP.Outside.L_meta_1031_aux.CycleAndBound


namespace PEqualNP.Outside.L_meta_1031_aux.CycleWitness

open PEqualNP.CircuitLowerBounds

def circuit : Circuit :=
  ⟨[⟨.or, [1, 4]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [1, 3]⟩,
    ⟨.and, [2, 7]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [6, 8]⟩,
    ⟨.or, [9, 10]⟩], 11⟩

lemma size_seven : circuit.size = 7 := rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma computes_cycle : ∀ x : Fin 5 → Bool,
    circuit.eval (List.ofFn x) =
      decide (∃ u v : Fin 5, (u + 1 = v ∨ v + 1 = u) ∧
        x u = true ∧ x v = true) := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma every_and_sound : ∀ (x : Fin 5 → Bool) (t : Fin 7),
    (t.val = 1 ∨ t.val = 3 ∨ t.val = 4) →
    (circuit.wires (List.ofFn x)).getD (5 + t.val) false = true →
    circuit.eval (List.ofFn x) = true := by
  decide

lemma monotone_binary : ∀ g ∈ circuit.gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_1031_aux.CycleWitness


namespace PEqualNP.Outside.L_meta_1031_aux.CycleOptimal

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_1031_aux

lemma gate_counts_le (g : Gate) :
    (if CycleAndBound.realAnd g then 1 else 0 : ℕ) +
      (if CompactOr.isOr g then 1 else 0 : ℕ) ≤ 1 := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp [CycleAndBound.realAnd, CompactOr.isOr]
  split_ifs <;> omega

lemma counts_le_length (gs : List Gate) :
    gs.countP CycleAndBound.realAnd + CompactOr.orCount gs ≤ gs.length := by
  induction gs with
  | nil => simp [CompactOr.orCount]
  | cons g gs ih =>
    have hg := gate_counts_le g
    simp only [CompactOr.orCount, List.countP_cons, List.length_cons] at *
    omega

lemma normalized_mono (n : ℕ) (C : Circuit) (hnorm : CompactOr.normalized n C.gates) :
    ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
  obtain ⟨a, b, hp, _, _, hop⟩ := hnorm j hj
  exact ⟨hop, by simp [hp]⟩

theorem cycle_size_ge_seven (hfinite : CompactOr.FiniteObstruction) (C : Circuit)
    (hnorm : CompactOr.normalized 5 C.gates)
    (hcomputes : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = CompactOr.cycleTruth x) :
    7 ≤ C.size := by
  have hand := CycleAndBound.cycle_requires_three_binary_ands C (normalized_mono 5 C hnorm) hcomputes
  have hor := CompactOr.cycle_four_ors hfinite C hnorm hcomputes
  have htotal := counts_le_length C.gates
  change 7 ≤ C.gates.length
  omega

lemma witness_normalized : CompactOr.normalized 5 CycleWitness.circuit.gates := by
  intro j hj
  have hjlt : j < 7 := by simpa [CycleWitness.circuit] using hj
  have hcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [CycleWitness.circuit]

lemma cycle_size_seven_exists : ∃ C : Circuit,
    CompactOr.normalized 5 C.gates ∧
    (∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = CompactOr.cycleTruth x) ∧ C.size = 7 :=
  ⟨CycleWitness.circuit, witness_normalized, CycleWitness.computes_cycle, CycleWitness.size_seven⟩

theorem cycle_optimum_seven (hfinite : CompactOr.FiniteObstruction) : ∃ C : Circuit,
    CompactOr.normalized 5 C.gates ∧
    (∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = CompactOr.cycleTruth x) ∧ C.size = 7 ∧
    ∀ D : Circuit, CompactOr.normalized 5 D.gates →
      (∀ x : Fin 5 → Bool, D.eval (List.ofFn x) = CompactOr.cycleTruth x) → C.size ≤ D.size := by
  obtain ⟨C, hnorm, hcomputes, hsize⟩ := cycle_size_seven_exists
  refine ⟨C, hnorm, hcomputes, hsize, ?_⟩
  intro D hD hDcomputes
  rw [hsize]
  exact cycle_size_ge_seven hfinite D hD hDcomputes

end PEqualNP.Outside.L_meta_1031_aux.CycleOptimal


namespace PEqualNP.Outside.L_meta_1031_aux.CycleOptimal

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_1031_aux

theorem certified_cycle_size_ge_seven (C : Circuit)
    (hnorm : CompactOr.normalized 5 C.gates)
    (hcomputes : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = CompactOr.cycleTruth x) :
    7 ≤ C.size :=
  cycle_size_ge_seven CompactOr.certified_finite_obstruction C hnorm hcomputes

theorem certified_cycle_optimum_seven : ∃ C : Circuit,
    CompactOr.normalized 5 C.gates ∧
    (∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = CompactOr.cycleTruth x) ∧ C.size = 7 ∧
    ∀ D : Circuit, CompactOr.normalized 5 D.gates →
      (∀ x : Fin 5 → Bool, D.eval (List.ofFn x) = CompactOr.cycleTruth x) → C.size ≤ D.size :=
  cycle_optimum_seven CompactOr.certified_finite_obstruction

end PEqualNP.Outside.L_meta_1031_aux.CycleOptimal

#print axioms PEqualNP.Outside.L_meta_1031_aux.SemanticCertificate.all_first_cases
#print axioms PEqualNP.Outside.L_meta_1031_aux.SemanticCertificate.semantic_soundness
#print axioms PEqualNP.Outside.L_meta_1031_aux.CompactOr.certified_finite_obstruction
#print axioms PEqualNP.Outside.L_meta_1031_aux.CompactOr.certified_cycle_four_ors
#print axioms PEqualNP.Outside.L_meta_1031_aux.CycleAndBound.cycle_requires_three_binary_ands
#print axioms PEqualNP.Outside.L_meta_1031_aux.CycleOptimal.certified_cycle_size_ge_seven
#print axioms PEqualNP.Outside.L_meta_1031_aux.CycleOptimal.certified_cycle_optimum_seven
#print axioms PEqualNP.Outside.L_meta_1031_aux.CycleWitness.every_and_sound
