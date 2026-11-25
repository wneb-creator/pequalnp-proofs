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

lemma ors_initial_eq : ors initial = [0, 1, 2, 4, 8, 16, 32, 64, 113, 128, 204, 256, 387, 512, 550, 792, 1023, 3, 5, 9, 17, 33, 65, 129, 205, 257, 513, 551, 793, 6, 10, 18, 34, 66, 115, 130, 206, 258, 514, 794, 12, 20, 36, 68, 117, 132, 260, 391, 516, 796, 24, 40, 72, 121, 136, 264, 395, 520, 558, 48, 80, 144, 220, 272, 403, 528, 566, 96, 160, 236, 288, 419, 544, 824, 192, 320, 451, 576, 614, 856, 241, 253, 369, 499, 625, 631, 889, 384, 640, 678, 920, 460, 463, 716, 750, 988, 768, 806, 899, 935, 923, 830] := by
  decide +kernel

theorem assemble_checks
    (hfirst_0 : checkFirst 0 = true)
    (hfirst_1 : checkFirst 1 = true)
    (hfirst_2 : checkFirst 2 = true)
    (hfirst_4 : checkFirst 4 = true)
    (hfirst_8 : checkFirst 8 = true)
    (hfirst_16 : checkFirst 16 = true)
    (hfirst_32 : checkFirst 32 = true)
    (hfirst_64 : checkFirst 64 = true)
    (hfirst_113 : checkFirst 113 = true)
    (hfirst_128 : checkFirst 128 = true)
    (hfirst_204 : checkFirst 204 = true)
    (hfirst_256 : checkFirst 256 = true)
    (hfirst_387 : checkFirst 387 = true)
    (hfirst_512 : checkFirst 512 = true)
    (hfirst_550 : checkFirst 550 = true)
    (hfirst_792 : checkFirst 792 = true)
    (hfirst_1023 : checkFirst 1023 = true)
    (hfirst_3 : checkFirst 3 = true)
    (hfirst_5 : checkFirst 5 = true)
    (hfirst_9 : checkFirst 9 = true)
    (hfirst_17 : checkFirst 17 = true)
    (hfirst_33 : checkFirst 33 = true)
    (hfirst_65 : checkFirst 65 = true)
    (hfirst_129 : checkFirst 129 = true)
    (hfirst_205 : checkFirst 205 = true)
    (hfirst_257 : checkFirst 257 = true)
    (hfirst_513 : checkFirst 513 = true)
    (hfirst_551 : checkFirst 551 = true)
    (hfirst_793 : checkFirst 793 = true)
    (hfirst_6 : checkFirst 6 = true)
    (hfirst_10 : checkFirst 10 = true)
    (hfirst_18 : checkFirst 18 = true)
    (hfirst_34 : checkFirst 34 = true)
    (hfirst_66 : checkFirst 66 = true)
    (hfirst_115 : checkFirst 115 = true)
    (hfirst_130 : checkFirst 130 = true)
    (hfirst_206 : checkFirst 206 = true)
    (hfirst_258 : checkFirst 258 = true)
    (hfirst_514 : checkFirst 514 = true)
    (hfirst_794 : checkFirst 794 = true)
    (hfirst_12 : checkFirst 12 = true)
    (hfirst_20 : checkFirst 20 = true)
    (hfirst_36 : checkFirst 36 = true)
    (hfirst_68 : checkFirst 68 = true)
    (hfirst_117 : checkFirst 117 = true)
    (hfirst_132 : checkFirst 132 = true)
    (hfirst_260 : checkFirst 260 = true)
    (hfirst_391 : checkFirst 391 = true)
    (hfirst_516 : checkFirst 516 = true)
    (hfirst_796 : checkFirst 796 = true)
    (hfirst_24 : checkFirst 24 = true)
    (hfirst_40 : checkFirst 40 = true)
    (hfirst_72 : checkFirst 72 = true)
    (hfirst_121 : checkFirst 121 = true)
    (hfirst_136 : checkFirst 136 = true)
    (hfirst_264 : checkFirst 264 = true)
    (hfirst_395 : checkFirst 395 = true)
    (hfirst_520 : checkFirst 520 = true)
    (hfirst_558 : checkFirst 558 = true)
    (hfirst_48 : checkFirst 48 = true)
    (hfirst_80 : checkFirst 80 = true)
    (hfirst_144 : checkFirst 144 = true)
    (hfirst_220 : checkFirst 220 = true)
    (hfirst_272 : checkFirst 272 = true)
    (hfirst_403 : checkFirst 403 = true)
    (hfirst_528 : checkFirst 528 = true)
    (hfirst_566 : checkFirst 566 = true)
    (hfirst_96 : checkFirst 96 = true)
    (hfirst_160 : checkFirst 160 = true)
    (hfirst_236 : checkFirst 236 = true)
    (hfirst_288 : checkFirst 288 = true)
    (hfirst_419 : checkFirst 419 = true)
    (hfirst_544 : checkFirst 544 = true)
    (hfirst_824 : checkFirst 824 = true)
    (hfirst_192 : checkFirst 192 = true)
    (hfirst_320 : checkFirst 320 = true)
    (hfirst_451 : checkFirst 451 = true)
    (hfirst_576 : checkFirst 576 = true)
    (hfirst_614 : checkFirst 614 = true)
    (hfirst_856 : checkFirst 856 = true)
    (hfirst_241 : checkFirst 241 = true)
    (hfirst_253 : checkFirst 253 = true)
    (hfirst_369 : checkFirst 369 = true)
    (hfirst_499 : checkFirst 499 = true)
    (hfirst_625 : checkFirst 625 = true)
    (hfirst_631 : checkFirst 631 = true)
    (hfirst_889 : checkFirst 889 = true)
    (hfirst_384 : checkFirst 384 = true)
    (hfirst_640 : checkFirst 640 = true)
    (hfirst_678 : checkFirst 678 = true)
    (hfirst_920 : checkFirst 920 = true)
    (hfirst_460 : checkFirst 460 = true)
    (hfirst_463 : checkFirst 463 = true)
    (hfirst_716 : checkFirst 716 = true)
    (hfirst_750 : checkFirst 750 = true)
    (hfirst_988 : checkFirst 988 = true)
    (hfirst_768 : checkFirst 768 = true)
    (hfirst_806 : checkFirst 806 = true)
    (hfirst_899 : checkFirst 899 = true)
    (hfirst_935 : checkFirst 935 = true)
    (hfirst_923 : checkFirst 923 = true)
    (hfirst_830 : checkFirst 830 = true)
    : ∀ v ∈ ors initial, checkFirst v = true := by
  intro v hv
  rw [ors_initial_eq] at hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hfirst_0
  · exact hfirst_1
  · exact hfirst_2
  · exact hfirst_4
  · exact hfirst_8
  · exact hfirst_16
  · exact hfirst_32
  · exact hfirst_64
  · exact hfirst_113
  · exact hfirst_128
  · exact hfirst_204
  · exact hfirst_256
  · exact hfirst_387
  · exact hfirst_512
  · exact hfirst_550
  · exact hfirst_792
  · exact hfirst_1023
  · exact hfirst_3
  · exact hfirst_5
  · exact hfirst_9
  · exact hfirst_17
  · exact hfirst_33
  · exact hfirst_65
  · exact hfirst_129
  · exact hfirst_205
  · exact hfirst_257
  · exact hfirst_513
  · exact hfirst_551
  · exact hfirst_793
  · exact hfirst_6
  · exact hfirst_10
  · exact hfirst_18
  · exact hfirst_34
  · exact hfirst_66
  · exact hfirst_115
  · exact hfirst_130
  · exact hfirst_206
  · exact hfirst_258
  · exact hfirst_514
  · exact hfirst_794
  · exact hfirst_12
  · exact hfirst_20
  · exact hfirst_36
  · exact hfirst_68
  · exact hfirst_117
  · exact hfirst_132
  · exact hfirst_260
  · exact hfirst_391
  · exact hfirst_516
  · exact hfirst_796
  · exact hfirst_24
  · exact hfirst_40
  · exact hfirst_72
  · exact hfirst_121
  · exact hfirst_136
  · exact hfirst_264
  · exact hfirst_395
  · exact hfirst_520
  · exact hfirst_558
  · exact hfirst_48
  · exact hfirst_80
  · exact hfirst_144
  · exact hfirst_220
  · exact hfirst_272
  · exact hfirst_403
  · exact hfirst_528
  · exact hfirst_566
  · exact hfirst_96
  · exact hfirst_160
  · exact hfirst_236
  · exact hfirst_288
  · exact hfirst_419
  · exact hfirst_544
  · exact hfirst_824
  · exact hfirst_192
  · exact hfirst_320
  · exact hfirst_451
  · exact hfirst_576
  · exact hfirst_614
  · exact hfirst_856
  · exact hfirst_241
  · exact hfirst_253
  · exact hfirst_369
  · exact hfirst_499
  · exact hfirst_625
  · exact hfirst_631
  · exact hfirst_889
  · exact hfirst_384
  · exact hfirst_640
  · exact hfirst_678
  · exact hfirst_920
  · exact hfirst_460
  · exact hfirst_463
  · exact hfirst_716
  · exact hfirst_750
  · exact hfirst_988
  · exact hfirst_768
  · exact hfirst_806
  · exact hfirst_899
  · exact hfirst_935
  · exact hfirst_923
  · exact hfirst_830

end PEqualNP.Outside.L_meta_1031_aux.SemanticCertificate
