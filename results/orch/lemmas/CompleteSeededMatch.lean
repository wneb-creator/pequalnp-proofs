import Mathlib.Data.Nat.Bitwise

namespace PEqualNP.Outside.L_meta_2592_aux.FastSeededMatch

abbrev Sig := Nat

def inv (a : Sig) : Sig := a ^^^ 8191

def target : Sig := 30

def seeds : List Sig :=
  [0, 8191, 2726, 5446, 1642, 6538, 498, 7698,
    6142, 7166, 7934, 8158, 7630, 2042, 7802, 6650]

def generated (bank : List Sig) : List Sig :=
  bank ++ bank.map (fun a => inv a) ++
    bank.flatMap (fun a => bank.flatMap (fun b => [a &&& b, a ||| b]))

def choices (bank : List Sig) : List Sig := (generated bank).eraseDups

def Safe (bank : List Sig) : Prop :=
  (∀ a ∈ bank, a ≠ target) ∧
  (∀ a ∈ bank, inv a ≠ target) ∧
  (∀ a ∈ bank, ∀ b ∈ bank, a &&& b ≠ target ∧ a ||| b ≠ target)

def newOK (bank : List Sig) (a : Sig) : Bool :=
  decide (a ≠ target ∧ inv a ≠ target) &&
    bank.all (fun b => decide (a &&& b ≠ target ∧ a ||| b ≠ target))

lemma safe_cons {bank : List Sig} (hs : Safe bank) {a : Sig}
    (ha : newOK bank a = true) : Safe (a :: bank) := by
  simp only [newOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at ha
  rcases ha with ⟨⟨ha, hn⟩, hb⟩
  refine ⟨?_, ?_, ?_⟩
  · intro b hmem
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact ha
    · exact hs.1 b hmem
  · intro b hmem
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact hn
    · exact hs.2.1 b hmem
  · intro b hbm c hcm
    rcases List.mem_cons.mp hbm with hba | hbB
    · subst b
      rcases List.mem_cons.mp hcm with rfl | hcB
      · simpa using And.intro ha ha
      · exact hb c hcB
    · rcases List.mem_cons.mp hcm with hca | hcB
      · subst c
        simpa [Nat.and_comm, Nat.or_comm] using hb b hbB
      · exact hs.2.2 b hbB c hcB

lemma safe_choices {bank : List Sig} (hs : Safe bank) {a : Sig}
    (ha : a ∈ choices bank) : a ≠ target := by
  simp only [choices, List.mem_eraseDups, generated, List.mem_append,
    List.mem_map, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with (h | ⟨b, hb, rfl⟩) | ⟨b, hb, c, hc, h⟩
  · exact hs.1 a h
  · exact hs.2.1 b hb
  · rcases h with rfl | rfl
    · exact (hs.2.2 b hb c hc).1
    · exact (hs.2.2 b hb c hc).2

lemma seeds_safe : Safe seeds := by
  unfold Safe
  decide +kernel

def afterFirst (a : Sig) : Bool :=
  newOK seeds a && (choices (a :: seeds)).all (fun b => newOK (a :: seeds) b)

def noThree : Bool := (choices seeds).all afterFirst

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_0 : afterFirst 0 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_1 : afterFirst 8191 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_2 : afterFirst 2726 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_3 : afterFirst 5446 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_4 : afterFirst 1642 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_5 : afterFirst 6538 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_6 : afterFirst 498 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_7 : afterFirst 7698 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_8 : afterFirst 6142 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_9 : afterFirst 7166 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_10 : afterFirst 7934 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_11 : afterFirst 8158 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_12 : afterFirst 7630 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_13 : afterFirst 2042 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_14 : afterFirst 7802 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_15 : afterFirst 6650 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_16 : afterFirst 5465 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_17 : afterFirst 2745 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_18 : afterFirst 6549 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_19 : afterFirst 1653 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_20 : afterFirst 7693 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_21 : afterFirst 493 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_22 : afterFirst 2049 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_23 : afterFirst 1025 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_24 : afterFirst 257 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_25 : afterFirst 33 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_26 : afterFirst 561 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_27 : afterFirst 6149 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_28 : afterFirst 389 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_29 : afterFirst 1541 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_30 : afterFirst 6 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_31 : afterFirst 8166 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_32 : afterFirst 546 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_33 : afterFirst 3822 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_34 : afterFirst 2178 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_35 : afterFirst 7086 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_36 : afterFirst 162 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_37 : afterFirst 3062 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_38 : afterFirst 2562 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_39 : afterFirst 7862 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_40 : afterFirst 678 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_41 : afterFirst 8190 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_42 : afterFirst 2694 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_43 : afterFirst 2182 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_44 : afterFirst 8174 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_45 : afterFirst 674 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_46 : afterFirst 4094 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_47 : afterFirst 2594 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_48 : afterFirst 2210 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_49 : afterFirst 1090 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_50 : afterFirst 5998 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_51 : afterFirst 4354 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_52 : afterFirst 322 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_53 : afterFirst 5622 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_54 : afterFirst 5122 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_55 : afterFirst 8022 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_56 : afterFirst 4422 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_57 : afterFirst 5190 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_58 : afterFirst 1346 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_59 : afterFirst 5186 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_60 : afterFirst 8062 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_61 : afterFirst 4418 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_62 : afterFirst 7678 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_63 : afterFirst 10 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_64 : afterFirst 8170 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_65 : afterFirst 98 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_66 : afterFirst 1538 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_67 : afterFirst 618 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_68 : afterFirst 1610 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_69 : afterFirst 1098 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_70 : afterFirst 106 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_71 : afterFirst 8186 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_72 : afterFirst 386 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_73 : afterFirst 6146 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_74 : afterFirst 8090 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_75 : afterFirst 4490 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_76 : afterFirst 6282 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_77 : afterFirst 394 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_78 : afterFirst 6154 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_79 : afterFirst 18 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_80 : afterFirst 8178 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_81 : afterFirst 242 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_82 : afterFirst 466 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_83 : afterFirst 450 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_84 : afterFirst 114 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_85 : afterFirst 5650 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_86 : afterFirst 6674 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_87 : afterFirst 7170 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_88 : afterFirst 1554 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_89 : afterFirst 6162 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_90 : afterFirst 5118 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_91 : afterFirst 5886 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_92 : afterFirst 6110 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_93 : afterFirst 5582 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_94 : afterFirst 5754 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_95 : afterFirst 4602 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_96 : afterFirst 6910 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_97 : afterFirst 7134 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_98 : afterFirst 6606 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_99 : afterFirst 1018 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_100 : afterFirst 6778 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_101 : afterFirst 7902 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_102 : afterFirst 7374 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_103 : afterFirst 1786 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_104 : afterFirst 6394 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_105 : afterFirst 2010 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_106 : afterFirst 7770 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_107 : afterFirst 6618 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_108 : afterFirst 1482 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_109 : afterFirst 7242 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_110 : afterFirst 6602 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_111 : afterFirst 1658 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_112 : afterFirst 506 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_first_113 : afterFirst 6266 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_noThree : noThree = true := by
  have h : choices seeds = [0, 8191, 2726, 5446, 1642, 6538, 498, 7698, 6142, 7166, 7934, 8158, 7630, 2042, 7802, 6650, 5465, 2745, 6549, 1653, 7693, 493, 2049, 1025, 257, 33, 561, 6149, 389, 1541, 6, 8166, 546, 3822, 2178, 7086, 162, 3062, 2562, 7862, 678, 8190, 2694, 2182, 8174, 674, 4094, 2594, 2210, 1090, 5998, 4354, 322, 5622, 5122, 8022, 4422, 5190, 1346, 5186, 8062, 4418, 7678, 10, 8170, 98, 1538, 618, 1610, 1098, 106, 8186, 386, 6146, 8090, 4490, 6282, 394, 6154, 18, 8178, 242, 466, 450, 114, 5650, 6674, 7170, 1554, 6162, 5118, 5886, 6110, 5582, 5754, 4602, 6910, 7134, 6606, 1018, 6778, 7902, 7374, 1786, 6394, 2010, 7770, 6618, 1482, 7242, 6602, 1658, 506, 6266] := by decide +kernel
  unfold noThree
  rw [h]
  simp only [List.all_cons, List.all_nil, checked_first_0, checked_first_1, checked_first_2, checked_first_3, checked_first_4, checked_first_5, checked_first_6, checked_first_7, checked_first_8, checked_first_9, checked_first_10, checked_first_11, checked_first_12, checked_first_13, checked_first_14, checked_first_15, checked_first_16, checked_first_17, checked_first_18, checked_first_19, checked_first_20, checked_first_21, checked_first_22, checked_first_23, checked_first_24, checked_first_25, checked_first_26, checked_first_27, checked_first_28, checked_first_29, checked_first_30, checked_first_31, checked_first_32, checked_first_33, checked_first_34, checked_first_35, checked_first_36, checked_first_37, checked_first_38, checked_first_39, checked_first_40, checked_first_41, checked_first_42, checked_first_43, checked_first_44, checked_first_45, checked_first_46, checked_first_47, checked_first_48, checked_first_49, checked_first_50, checked_first_51, checked_first_52, checked_first_53, checked_first_54, checked_first_55, checked_first_56, checked_first_57, checked_first_58, checked_first_59, checked_first_60, checked_first_61, checked_first_62, checked_first_63, checked_first_64, checked_first_65, checked_first_66, checked_first_67, checked_first_68, checked_first_69, checked_first_70, checked_first_71, checked_first_72, checked_first_73, checked_first_74, checked_first_75, checked_first_76, checked_first_77, checked_first_78, checked_first_79, checked_first_80, checked_first_81, checked_first_82, checked_first_83, checked_first_84, checked_first_85, checked_first_86, checked_first_87, checked_first_88, checked_first_89, checked_first_90, checked_first_91, checked_first_92, checked_first_93, checked_first_94, checked_first_95, checked_first_96, checked_first_97, checked_first_98, checked_first_99, checked_first_100, checked_first_101, checked_first_102, checked_first_103, checked_first_104, checked_first_105, checked_first_106, checked_first_107, checked_first_108, checked_first_109, checked_first_110, checked_first_111, checked_first_112, checked_first_113, Bool.and_self]

lemma choices_noThree (a b c : Sig)
    (ha : a ∈ choices seeds) (hb : b ∈ choices (a :: seeds))
    (hc : c ∈ choices (b :: a :: seeds)) : c ≠ target := by
  have h := List.all_eq_true.mp checked_noThree a ha
  simp only [afterFirst, Bool.and_eq_true] at h
  have hsa := safe_cons seeds_safe h.1
  have hsb := safe_cons hsa (List.all_eq_true.mp h.2 b hb)
  exact safe_choices hsb hc

end PEqualNP.Outside.L_meta_2592_aux.FastSeededMatch


namespace PEqualNP.Outside.L_meta_2592_aux.SeededRows

def rows : List Nat := [0, 63, 3, 12, 48, 21, 22, 25, 26, 37, 38, 41, 42]

def seeds : List Nat :=
  [0, 8191, 2726, 5446, 1642, 6538, 498, 7698,
    6142, 7166, 7934, 8158, 7630, 2042, 7802, 6650]

def seedValues (r : Nat) : List Bool :=
  let a := r.testBit 0
  let b := r.testBit 1
  let c := r.testBit 2
  let d := r.testBit 3
  let e := r.testBit 4
  let f := r.testBit 5
  [false, true, a, b, c, d, e, f,
    b || c || e, a || d || e, a || c || f, b || d || f,
    b || d, c || e, c || f, d || e]

def matching (r : Nat) : Bool :=
  (r.testBit 0 && r.testBit 1) ||
  (r.testBit 2 && r.testBit 3) ||
  (r.testBit 4 && r.testBit 5)

lemma seeds_semantics :
    ∀ r : Fin 13,
      seeds.map (fun mask => mask.testBit r.val) = seedValues (rows.getD r.val 0) := by
  decide +kernel

lemma target_semantics :
    ∀ r : Fin 13, (30 : Nat).testBit r.val = matching (rows.getD r.val 0) := by
  decide +kernel

lemma rows_distinct : rows.Nodup := by decide +kernel

lemma rows_small : ∀ r ∈ rows, r < 64 := by decide +kernel

def Agrees (mask : Nat) (f : Nat → Bool) : Prop :=
  ∀ r : Fin 13, mask.testBit r.val = f (rows.getD r.val 0)

lemma agrees_and {a b : Nat} {f g : Nat → Bool}
    (ha : Agrees a f) (hb : Agrees b g) :
    Agrees (a &&& b) (fun r => f r && g r) := by
  intro r
  rw [Nat.testBit_land, ha r, hb r]

lemma agrees_or {a b : Nat} {f g : Nat → Bool}
    (ha : Agrees a f) (hb : Agrees b g) :
    Agrees (a ||| b) (fun r => f r || g r) := by
  intro r
  rw [Nat.testBit_lor, ha r, hb r]

lemma agrees_not {a : Nat} {f : Nat → Bool} (ha : Agrees a f) :
    Agrees (a ^^^ 8191) (fun r => !(f r)) := by
  have mask : ∀ r : Fin 13, (8191 : Nat).testBit r.val = true := by decide +kernel
  intro r
  rw [Nat.testBit_xor, ha r, mask r]
  simp

lemma agrees_matching {a : Nat} (ha : a < 8192) (hf : Agrees a matching) : a = 30 := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 13
  · exact (hf ⟨i, hi⟩).trans (target_semantics ⟨i, hi⟩).symm
  · have hp : (2 : Nat) ^ 13 ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
    have haa : a < 2 ^ i := lt_of_lt_of_le ha hp
    have htt : 30 < 2 ^ i := lt_of_lt_of_le (by decide : 30 < 2 ^ 13) hp
    rw [Nat.testBit_lt_two_pow haa, Nat.testBit_lt_two_pow htt]

def generated (bank : List Nat) : List Nat :=
  bank ++ bank.map (fun a => a ^^^ 8191) ++
    bank.flatMap (fun a => bank.flatMap (fun b => [a &&& b, a ||| b]))

def choices (bank : List Nat) : List Nat := (generated bank).eraseDups

lemma choices_small {bank : List Nat} (hb : ∀ a ∈ bank, a < 8192)
    {a : Nat} (ha : a ∈ choices bank) : a < 8192 := by
  simp only [choices, List.mem_eraseDups, generated, List.mem_append,
    List.mem_map, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with (h | ⟨b, hbmem, rfl⟩) | ⟨b, hbmem, c, hcmem, h⟩
  · exact hb a h
  · exact Nat.xor_lt_two_pow (n := 13) (hb b hbmem) (by decide)
  · rcases h with rfl | rfl
    · exact Nat.and_lt_two_pow (n := 13) b (hb c hcmem)
    · exact Nat.or_lt_two_pow (n := 13) (hb b hbmem) (hb c hcmem)

end PEqualNP.Outside.L_meta_2592_aux.SeededRows


namespace PEqualNP.Outside.L_meta_2592_aux.FastSeededMatch

lemma matching_requires_four (a b c : Sig)
    (ha : a ∈ choices seeds) (hb : b ∈ choices (a :: seeds))
    (hc : c ∈ choices (b :: a :: seeds))
    (hf : SeededRows.Agrees c SeededRows.matching) : False := by
  have hs : ∀ x ∈ SeededRows.seeds, x < 8192 := by decide +kernel
  have hsa : ∀ x ∈ a :: SeededRows.seeds, x < 8192 := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact SeededRows.choices_small hs ha
    · exact hs x hx
  have hsb : ∀ x ∈ b :: a :: SeededRows.seeds, x < 8192 := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact SeededRows.choices_small hsa hb
    · exact hsa x hx
  have ht := SeededRows.agrees_matching (SeededRows.choices_small hsb hc) hf
  exact choices_noThree a b c ha hb hc ht

end PEqualNP.Outside.L_meta_2592_aux.FastSeededMatch
