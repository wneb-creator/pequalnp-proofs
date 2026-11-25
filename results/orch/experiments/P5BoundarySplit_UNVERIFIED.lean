import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1031.P5Boundary

structure Signal where
  value : BitVec 32
  ancestors : BitVec 4
  deriving DecidableEq, BEq

def base (i : BitVec 4) : Signal :=
  ⟨if i = 0 then 2863311530 else
    if i = 1 then 3435973836 else
    if i = 2 then 4042322160 else
    if i = 3 then 4278255360 else
    if i = 4 then 4294901760 else
    if i = 5 then 4291624908 else
    if i = 6 then 4244438268 else
    if i = 7 then 4294966524 else
    if i = 8 then 4294945450 else
    if i = 9 then 4294966010 else
    if i = 10 then 4289396650 else
    if i = 11 then 4294639610 else
    if i = 13 then 4294967295 else 0, 0⟩

def edgeMask (v : BitVec 32) : BitVec 4 :=
  (if v.getLsbD 3 then 1 else 0) |||
  (if v.getLsbD 6 then 2 else 0) |||
  (if v.getLsbD 12 then 4 else 0) |||
  (if v.getLsbD 24 then 8 else 0)

def gate (isAnd : Bool) (a b : Signal) : Signal :=
  let v := if isAnd then a.value &&& b.value else a.value ||| b.value
  ⟨v, a.ancestors ||| b.ancestors ||| (if isAnd then edgeMask v else 0)⟩

def legal (isAnd : Bool) (a b : Signal) : Bool :=
  let own := edgeMask (a.value &&& b.value) &&& ~~~(a.ancestors ||| b.ancestors)
  !isAnd || (own != 0 && (own &&& 12 == 0 || own &&& 9 == 0 || own &&& 3 == 0))

def boundary : List Signal :=
  ((List.range 14).map fun i => base (BitVec.ofNat 4 i)).dedup

def extensions (a b : Signal) : List Signal :=
  gate false a b :: if legal true a b then [gate true a b] else []

def next (xs : List Signal) : List Signal :=
  (xs.flatMap fun a => xs.flatMap fun b => extensions a b).dedup

def misses (xs : List Signal) : Bool :=
  xs.all fun s => s.value != 4291360968

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def firsts : List Signal :=
  [⟨4008636142, 0⟩,
   ⟨2290649224, 1⟩,
   ⟨4210752250, 0⟩,
   ⟨3233857728, 2⟩,
   ⟨4293984240, 0⟩,
   ⟨4026593280, 4⟩,
   ⟨4294954188, 0⟩,
   ⟨4294963440, 0⟩,
   ⟨4294967040, 0⟩,
   ⟨4278190080, 8⟩,
   ⟨2861083272, 1⟩,
   ⟨4039176384, 6⟩,
   ⟨4294967244, 0⟩,
   ⟨4291559424, 8⟩,
   ⟨4278124286, 0⟩,
   ⟨2829625512, 1⟩,
   ⟨4227922944, 4⟩,
   ⟨4294770684, 0⟩,
   ⟨2863311016, 1⟩,
   ⟨4278254592, 12⟩,
   ⟨4294967292, 0⟩,
   ⟨4294962926, 0⟩,
   ⟨3435956360, 1⟩,
   ⟨4278233600, 8⟩,
   ⟨4294967278, 0⟩,
   ⟨4244416680, 1⟩,
   ⟨3435972808, 3⟩,
   ⟨4278254080, 12⟩,
   ⟨4294967038, 0⟩,
   ⟨3431517320, 1⟩,
   ⟨4037079200, 4⟩,
   ⟨4289331200, 8⟩,
   ⟨4293853166, 0⟩,
   ⟨4294967210, 0⟩,
   ⟨3435711688, 3⟩,
   ⟨4294574080, 8⟩,
   ⟨4294901758, 0⟩,
   ⟨4294967294, 0⟩,
   ⟨4294967290, 0⟩,
   ⟨2863311530, 0⟩,
   ⟨3435973836, 0⟩,
   ⟨4042322160, 0⟩,
   ⟨4278255360, 0⟩,
   ⟨4294901760, 0⟩,
   ⟨4291624908, 0⟩,
   ⟨4244438268, 0⟩,
   ⟨4294966524, 0⟩,
   ⟨4294945450, 0⟩,
   ⟨4294966010, 0⟩,
   ⟨4289396650, 0⟩,
   ⟨4294639610, 0⟩,
   ⟨0, 0⟩,
   ⟨2863311530, 1⟩,
   ⟨3435973836, 3⟩,
   ⟨4042322160, 6⟩,
   ⟨4278255360, 12⟩,
   ⟨4294901760, 8⟩,
   ⟨4294967295, 0⟩]

lemma firsts_eq : next boundary = firsts := by decide +kernel

lemma not_initial : misses boundary = true := by decide +kernel

lemma not_one : misses firsts = true := by decide +kernel

lemma case_0_two : misses (next ((⟨4008636142, 0⟩ : Signal) :: boundary)) = true := by
  decide +kernel

lemma case_0_three : (next ((⟨4008636142, 0⟩ : Signal) :: boundary)).all (fun y =>
    (y :: (⟨4008636142, 0⟩ : Signal) :: boundary).all (fun z => misses (extensions y z))) = true := by
  decide +kernel

lemma case_1_two : misses (next ((⟨2290649224, 1⟩ : Signal) :: boundary)) = true := by
  decide +kernel

lemma case_1_three : (next ((⟨2290649224, 1⟩ : Signal) :: boundary)).all (fun y =>
    (y :: (⟨2290649224, 1⟩ : Signal) :: boundary).all (fun z => misses (extensions y z))) = true := by
  decide +kernel

lemma case_2_two : misses (next ((⟨4210752250, 0⟩ : Signal) :: boundary)) = true := by
  decide +kernel

lemma case_2_three : (next ((⟨4210752250, 0⟩ : Signal) :: boundary)).all (fun y =>
    (y :: (⟨4210752250, 0⟩ : Signal) :: boundary).all (fun z => misses (extensions y z))) = true := by
  decide +kernel

lemma case_3_two : misses (next ((⟨3233857728, 2⟩ : Signal) :: boundary)) = true := by
  decide +kernel

lemma case_3_three : (next ((⟨3233857728, 2⟩ : Signal) :: boundary)).all (fun y =>
    (y :: (⟨3233857728, 2⟩ : Signal) :: boundary).all (fun z => misses (extensions y z))) = true := by
  decide +kernel

lemma case_4_two : misses (next ((⟨4293984240, 0⟩ : Signal) :: boundary)) = true := by
  decide +kernel

lemma case_4_three : (next ((⟨4293984240, 0⟩ : Signal) :: boundary)).all (fun y =>
    (y :: (⟨4293984240, 0⟩ : Signal) :: boundary).all (fun z => misses (extensions y z))) = true := by
  decide +kernel

lemma case_5_two : misses (next ((⟨4026593280, 4⟩ : Signal) :: boundary)) = true := by
  decide +kernel

lemma case_5_three : (next ((⟨4026593280, 4⟩ : Signal) :: boundary)).all (fun y =>
    (y :: (⟨4026593280, 4⟩ : Signal) :: boundary).all (fun z => misses (extensions y z))) = true := by
  decide +kernel

lemma case_6_two : misses (next ((⟨4294954188, 0⟩ : Signal) :: boundary)) = true := by
  decide +kernel

lemma case_6_three : (next ((⟨4294954188, 0⟩ : Signal) :: boundary)).all (fun y =>
    (y :: (⟨4294954188, 0⟩ : Signal) :: boundary).all (fun z => misses (extensions y z))) = true := by
  decide +kernel

lemma case_7_two : misses (next ((⟨4294963440, 0⟩ : Signal) :: boundary)) = true := by
  decide +kernel

lemma case_7_three : (next ((⟨4294963440, 0⟩ : Signal) :: boundary)).all (fun y =>
    (y :: (⟨4294963440, 0⟩ : Signal) :: boundary).all (fun z => misses (extensions y z))) = true := by
  decide +kernel

lemma case_8_two : misses (next ((⟨4294967040, 0⟩ : Signal) :: boundary)) = true := by
  decide +kernel

lemma case_8_three : (next ((⟨4294967040, 0⟩ : Signal) :: boundary)).all (fun y =>
    (y :: (⟨4294967040, 0⟩ : Signal) :: boundary).all (fun z => misses (extensions y z))) = true := by
  decide +kernel

lemma case_9_two : misses (next ((⟨4278190080, 8⟩ : Signal) :: boundary)) = true := by
  decide +kernel

lemma case_9_three : (next ((⟨4278190080, 8⟩ : Signal) :: boundary)).all (fun y =>
    (y :: (⟨4278190080, 8⟩ : Signal) :: boundary).all (fun z => misses (extensions y z))) = true := by
  decide +kernel

lemma case_10_two : misses (next ((⟨2861083272, 1⟩ : Signal) :: boundary)) = true := by
  decide +kernel

lemma case_10_three : (next ((⟨2861083272, 1⟩ : Signal) :: boundary)).all (fun y =>
    (y :: (⟨2861083272, 1⟩ : Signal) :: boundary).all (fun z => misses (extensions y z))) = true := by
  decide +kernel

lemma case_11_two : misses (next ((⟨4039176384, 6⟩ : Signal) :: boundary)) = true := by
  decide +kernel

lemma case_11_three : (next ((⟨4039176384, 6⟩ : Signal) :: boundary)).all (fun y =>
    (y :: (⟨4039176384, 6⟩ : Signal) :: boundary).all (fun z => misses (extensions y z))) = true := by
  decide +kernel

lemma case_12_two : misses (next ((⟨4294967244, 0⟩ : Signal) :: boundary)) = true := by
  decide +kernel

lemma case_12_three : (next ((⟨4294967244, 0⟩ : Signal) :: boundary)).all (fun y =>
    (y :: (⟨4294967244, 0⟩ : Signal) :: boundary).all (fun z => misses (extensions y z))) = true := by
  decide +kernel

lemma case_13_two : misses (next ((⟨4291559424, 8⟩ : Signal) :: boundary)) = true := by
  decide +kernel

lemma case_13_three : (next ((⟨4291559424, 8⟩ : Signal) :: boundary)).all (fun y =>
    (y :: (⟨4291559424, 8⟩ : Signal) :: boundary).all (fun z => misses (extensions y z))) = true := by
  decide +kernel

lemma case_14_two : misses (next ((⟨4278124286, 0⟩ : Signal) :: boundary)) = true := by
  decide +kernel

lemma case_14_three : (next ((⟨4278124286, 0⟩ : Signal) :: boundary)).all (fun y =>
    (y :: (⟨4278124286, 0⟩ : Signal) :: boundary).all (fun z => misses (extensions y z))) = true := by
  decide +kernel

lemma case_15_two : misses (next ((⟨2829625512, 1⟩ : Signal) :: boundary)) = true := by
  decide +kernel

lemma case_15_three : (next ((⟨2829625512, 1⟩ : Signal) :: boundary)).all (fun y =>
    (y :: (⟨2829625512, 1⟩ : Signal) :: boundary).all (fun z => misses (extensions y z))) = true := by
  decide +kernel

lemma case_16_two : misses (next ((⟨4227922944, 4⟩ : Signal) :: boundary)) = true := by
  decide +kernel

lemma case_16_three : (next ((⟨4227922944, 4⟩ : Signal) :: boundary)).all (fun y =>
    (y :: (⟨4227922944, 4⟩ : Signal) :: boundary).all (fun z => misses (extensions y z))) = true := by
  decide +kernel

lemma case_17_two : misses (next ((⟨4294770684, 0⟩ : Signal) :: boundary)) = true := by
  decide +kernel

lemma case_17_three : (next ((⟨4294770684, 0⟩ : Signal) :: boundary)).all (fun y =>
    (y :: (⟨4294770684, 0⟩ : Signal) :: boundary).all (fun z => misses (extensions y z))) = true := by
  decide +kernel

lemma case_18_two : misses (next ((⟨2863311016, 1⟩ : Signal) :: boundary)) = true := by
  decide +kernel

lemma case_18_three : (next ((⟨2863311016, 1⟩ : Signal) :: boundary)).all (fun y =>
    (y :: (⟨2863311016, 1⟩ : Signal) :: boundary).all (fun z => misses (extensions y z))) = true := by
  decide +kernel

lemma case_19_two : misses (next ((⟨4278254592, 12⟩ : Signal) :: boundary)) = true := by
  decide +kernel

lemma case_19_three : (next ((⟨4278254592, 12⟩ : Signal) :: boundary)).all (fun y =>
    (y :: (⟨4278254592, 12⟩ : Signal) :: boundary).all (fun z => misses (extensions y z))) = true := by
  decide +kernel

lemma case_20_two : misses (next ((⟨4294967292, 0⟩ : Signal) :: boundary)) = true := by
  decide +kernel

lemma case_20_three : (next ((⟨4294967292, 0⟩ : Signal) :: boundary)).all (fun y =>
    (y :: (⟨4294967292, 0⟩ : Signal) :: boundary).all (fun z => misses (extensions y z))) = true := by
  decide +kernel

lemma case_21_two : misses (next ((⟨4294962926, 0⟩ : Signal) :: boundary)) = true := by
  decide +kernel

lemma case_21_three : (next ((⟨4294962926, 0⟩ : Signal) :: boundary)).all (fun y =>
    (y :: (⟨4294962926, 0⟩ : Signal) :: boundary).all (fun z => misses (extensions y z))) = true := by
  decide +kernel

lemma case_22_two : misses (next ((⟨3435956360, 1⟩ : Signal) :: boundary)) = true := by
  decide +kernel

lemma case_22_three : (next ((⟨3435956360, 1⟩ : Signal) :: boundary)).all (fun y =>
    (y :: (⟨3435956360, 1⟩ : Signal) :: boundary).all (fun z => misses (extensions y z))) = true := by
  decide +kernel

lemma case_23_two : misses (next ((⟨4278233600, 8⟩ : Signal) :: boundary)) = true := by
  decide +kernel

lemma case_23_three : (next ((⟨4278233600, 8⟩ : Signal) :: boundary)).all (fun y =>
    (y :: (⟨4278233600, 8⟩ : Signal) :: boundary).all (fun z => misses (extensions y z))) = true := by
  decide +kernel

lemma case_24_two : misses (next ((⟨4294967278, 0⟩ : Signal) :: boundary)) = true := by
  decide +kernel

lemma case_24_three : (next ((⟨4294967278, 0⟩ : Signal) :: boundary)).all (fun y =>
    (y :: (⟨4294967278, 0⟩ : Signal) :: boundary).all (fun z => misses (extensions y z))) = true := by
  decide +kernel

lemma case_25_two : misses (next ((⟨4244416680, 1⟩ : Signal) :: boundary)) = true := by
  decide +kernel

lemma case_25_three : (next ((⟨4244416680, 1⟩ : Signal) :: boundary)).all (fun y =>
    (y :: (⟨4244416680, 1⟩ : Signal) :: boundary).all (fun z => misses (extensions y z))) = true := by
  decide +kernel

lemma case_26_two : misses (next ((⟨3435972808, 3⟩ : Signal) :: boundary)) = true := by
  decide +kernel

lemma case_26_three : (next ((⟨3435972808, 3⟩ : Signal) :: boundary)).all (fun y =>
    (y :: (⟨3435972808, 3⟩ : Signal) :: boundary).all (fun z => misses (extensions y z))) = true := by
  decide +kernel

lemma case_27_two : misses (next ((⟨4278254080, 12⟩ : Signal) :: boundary)) = true := by
  decide +kernel

lemma case_27_three : (next ((⟨4278254080, 12⟩ : Signal) :: boundary)).all (fun y =>
    (y :: (⟨4278254080, 12⟩ : Signal) :: boundary).all (fun z => misses (extensions y z))) = true := by
  decide +kernel

lemma case_28_two : misses (next ((⟨4294967038, 0⟩ : Signal) :: boundary)) = true := by
  decide +kernel

lemma case_28_three : (next ((⟨4294967038, 0⟩ : Signal) :: boundary)).all (fun y =>
    (y :: (⟨4294967038, 0⟩ : Signal) :: boundary).all (fun z => misses (extensions y z))) = true := by
  decide +kernel

lemma case_29_two : misses (next ((⟨3431517320, 1⟩ : Signal) :: boundary)) = true := by
  decide +kernel

lemma case_29_three : (next ((⟨3431517320, 1⟩ : Signal) :: boundary)).all (fun y =>
    (y :: (⟨3431517320, 1⟩ : Signal) :: boundary).all (fun z => misses (extensions y z))) = true := by
  decide +kernel

lemma case_30_two : misses (next ((⟨4037079200, 4⟩ : Signal) :: boundary)) = true := by
  decide +kernel

lemma case_30_three : (next ((⟨4037079200, 4⟩ : Signal) :: boundary)).all (fun y =>
    (y :: (⟨4037079200, 4⟩ : Signal) :: boundary).all (fun z => misses (extensions y z))) = true := by
  decide +kernel

lemma case_31_two : misses (next ((⟨4289331200, 8⟩ : Signal) :: boundary)) = true := by
  decide +kernel

lemma case_31_three : (next ((⟨4289331200, 8⟩ : Signal) :: boundary)).all (fun y =>
    (y :: (⟨4289331200, 8⟩ : Signal) :: boundary).all (fun z => misses (extensions y z))) = true := by
  decide +kernel

lemma case_32_two : misses (next ((⟨4293853166, 0⟩ : Signal) :: boundary)) = true := by
  decide +kernel

lemma case_32_three : (next ((⟨4293853166, 0⟩ : Signal) :: boundary)).all (fun y =>
    (y :: (⟨4293853166, 0⟩ : Signal) :: boundary).all (fun z => misses (extensions y z))) = true := by
  decide +kernel

lemma case_33_two : misses (next ((⟨4294967210, 0⟩ : Signal) :: boundary)) = true := by
  decide +kernel

lemma case_33_three : (next ((⟨4294967210, 0⟩ : Signal) :: boundary)).all (fun y =>
    (y :: (⟨4294967210, 0⟩ : Signal) :: boundary).all (fun z => misses (extensions y z))) = true := by
  decide +kernel

lemma case_34_two : misses (next ((⟨3435711688, 3⟩ : Signal) :: boundary)) = true := by
  decide +kernel

lemma case_34_three : (next ((⟨3435711688, 3⟩ : Signal) :: boundary)).all (fun y =>
    (y :: (⟨3435711688, 3⟩ : Signal) :: boundary).all (fun z => misses (extensions y z))) = true := by
  decide +kernel

lemma case_35_two : misses (next ((⟨4294574080, 8⟩ : Signal) :: boundary)) = true := by
  decide +kernel

lemma case_35_three : (next ((⟨4294574080, 8⟩ : Signal) :: boundary)).all (fun y =>
    (y :: (⟨4294574080, 8⟩ : Signal) :: boundary).all (fun z => misses (extensions y z))) = true := by
  decide +kernel

lemma case_36_two : misses (next ((⟨4294901758, 0⟩ : Signal) :: boundary)) = true := by
  decide +kernel

lemma case_36_three : (next ((⟨4294901758, 0⟩ : Signal) :: boundary)).all (fun y =>
    (y :: (⟨4294901758, 0⟩ : Signal) :: boundary).all (fun z => misses (extensions y z))) = true := by
  decide +kernel

lemma case_37_two : misses (next ((⟨4294967294, 0⟩ : Signal) :: boundary)) = true := by
  decide +kernel

lemma case_37_three : (next ((⟨4294967294, 0⟩ : Signal) :: boundary)).all (fun y =>
    (y :: (⟨4294967294, 0⟩ : Signal) :: boundary).all (fun z => misses (extensions y z))) = true := by
  decide +kernel

lemma case_38_two : misses (next ((⟨4294967290, 0⟩ : Signal) :: boundary)) = true := by
  decide +kernel

lemma case_38_three : (next ((⟨4294967290, 0⟩ : Signal) :: boundary)).all (fun y =>
    (y :: (⟨4294967290, 0⟩ : Signal) :: boundary).all (fun z => misses (extensions y z))) = true := by
  decide +kernel

lemma case_39_two : misses (next ((⟨2863311530, 0⟩ : Signal) :: boundary)) = true := by
  decide +kernel

lemma case_39_three : (next ((⟨2863311530, 0⟩ : Signal) :: boundary)).all (fun y =>
    (y :: (⟨2863311530, 0⟩ : Signal) :: boundary).all (fun z => misses (extensions y z))) = true := by
  decide +kernel

lemma case_40_two : misses (next ((⟨3435973836, 0⟩ : Signal) :: boundary)) = true := by
  decide +kernel

lemma case_40_three : (next ((⟨3435973836, 0⟩ : Signal) :: boundary)).all (fun y =>
    (y :: (⟨3435973836, 0⟩ : Signal) :: boundary).all (fun z => misses (extensions y z))) = true := by
  decide +kernel

lemma case_41_two : misses (next ((⟨4042322160, 0⟩ : Signal) :: boundary)) = true := by
  decide +kernel

lemma case_41_three : (next ((⟨4042322160, 0⟩ : Signal) :: boundary)).all (fun y =>
    (y :: (⟨4042322160, 0⟩ : Signal) :: boundary).all (fun z => misses (extensions y z))) = true := by
  decide +kernel

lemma case_42_two : misses (next ((⟨4278255360, 0⟩ : Signal) :: boundary)) = true := by
  decide +kernel

lemma case_42_three : (next ((⟨4278255360, 0⟩ : Signal) :: boundary)).all (fun y =>
    (y :: (⟨4278255360, 0⟩ : Signal) :: boundary).all (fun z => misses (extensions y z))) = true := by
  decide +kernel

lemma case_43_two : misses (next ((⟨4294901760, 0⟩ : Signal) :: boundary)) = true := by
  decide +kernel

lemma case_43_three : (next ((⟨4294901760, 0⟩ : Signal) :: boundary)).all (fun y =>
    (y :: (⟨4294901760, 0⟩ : Signal) :: boundary).all (fun z => misses (extensions y z))) = true := by
  decide +kernel

lemma case_44_two : misses (next ((⟨4291624908, 0⟩ : Signal) :: boundary)) = true := by
  decide +kernel

lemma case_44_three : (next ((⟨4291624908, 0⟩ : Signal) :: boundary)).all (fun y =>
    (y :: (⟨4291624908, 0⟩ : Signal) :: boundary).all (fun z => misses (extensions y z))) = true := by
  decide +kernel

lemma case_45_two : misses (next ((⟨4244438268, 0⟩ : Signal) :: boundary)) = true := by
  decide +kernel

lemma case_45_three : (next ((⟨4244438268, 0⟩ : Signal) :: boundary)).all (fun y =>
    (y :: (⟨4244438268, 0⟩ : Signal) :: boundary).all (fun z => misses (extensions y z))) = true := by
  decide +kernel

lemma case_46_two : misses (next ((⟨4294966524, 0⟩ : Signal) :: boundary)) = true := by
  decide +kernel

lemma case_46_three : (next ((⟨4294966524, 0⟩ : Signal) :: boundary)).all (fun y =>
    (y :: (⟨4294966524, 0⟩ : Signal) :: boundary).all (fun z => misses (extensions y z))) = true := by
  decide +kernel

lemma case_47_two : misses (next ((⟨4294945450, 0⟩ : Signal) :: boundary)) = true := by
  decide +kernel

lemma case_47_three : (next ((⟨4294945450, 0⟩ : Signal) :: boundary)).all (fun y =>
    (y :: (⟨4294945450, 0⟩ : Signal) :: boundary).all (fun z => misses (extensions y z))) = true := by
  decide +kernel

lemma case_48_two : misses (next ((⟨4294966010, 0⟩ : Signal) :: boundary)) = true := by
  decide +kernel

lemma case_48_three : (next ((⟨4294966010, 0⟩ : Signal) :: boundary)).all (fun y =>
    (y :: (⟨4294966010, 0⟩ : Signal) :: boundary).all (fun z => misses (extensions y z))) = true := by
  decide +kernel

lemma case_49_two : misses (next ((⟨4289396650, 0⟩ : Signal) :: boundary)) = true := by
  decide +kernel

lemma case_49_three : (next ((⟨4289396650, 0⟩ : Signal) :: boundary)).all (fun y =>
    (y :: (⟨4289396650, 0⟩ : Signal) :: boundary).all (fun z => misses (extensions y z))) = true := by
  decide +kernel

lemma case_50_two : misses (next ((⟨4294639610, 0⟩ : Signal) :: boundary)) = true := by
  decide +kernel

lemma case_50_three : (next ((⟨4294639610, 0⟩ : Signal) :: boundary)).all (fun y =>
    (y :: (⟨4294639610, 0⟩ : Signal) :: boundary).all (fun z => misses (extensions y z))) = true := by
  decide +kernel

lemma case_51_two : misses (next ((⟨0, 0⟩ : Signal) :: boundary)) = true := by
  decide +kernel

lemma case_51_three : (next ((⟨0, 0⟩ : Signal) :: boundary)).all (fun y =>
    (y :: (⟨0, 0⟩ : Signal) :: boundary).all (fun z => misses (extensions y z))) = true := by
  decide +kernel

lemma case_52_two : misses (next ((⟨2863311530, 1⟩ : Signal) :: boundary)) = true := by
  decide +kernel

lemma case_52_three : (next ((⟨2863311530, 1⟩ : Signal) :: boundary)).all (fun y =>
    (y :: (⟨2863311530, 1⟩ : Signal) :: boundary).all (fun z => misses (extensions y z))) = true := by
  decide +kernel

lemma case_53_two : misses (next ((⟨3435973836, 3⟩ : Signal) :: boundary)) = true := by
  decide +kernel

lemma case_53_three : (next ((⟨3435973836, 3⟩ : Signal) :: boundary)).all (fun y =>
    (y :: (⟨3435973836, 3⟩ : Signal) :: boundary).all (fun z => misses (extensions y z))) = true := by
  decide +kernel

lemma case_54_two : misses (next ((⟨4042322160, 6⟩ : Signal) :: boundary)) = true := by
  decide +kernel

lemma case_54_three : (next ((⟨4042322160, 6⟩ : Signal) :: boundary)).all (fun y =>
    (y :: (⟨4042322160, 6⟩ : Signal) :: boundary).all (fun z => misses (extensions y z))) = true := by
  decide +kernel

lemma case_55_two : misses (next ((⟨4278255360, 12⟩ : Signal) :: boundary)) = true := by
  decide +kernel

lemma case_55_three : (next ((⟨4278255360, 12⟩ : Signal) :: boundary)).all (fun y =>
    (y :: (⟨4278255360, 12⟩ : Signal) :: boundary).all (fun z => misses (extensions y z))) = true := by
  decide +kernel

lemma case_56_two : misses (next ((⟨4294901760, 8⟩ : Signal) :: boundary)) = true := by
  decide +kernel

lemma case_56_three : (next ((⟨4294901760, 8⟩ : Signal) :: boundary)).all (fun y =>
    (y :: (⟨4294901760, 8⟩ : Signal) :: boundary).all (fun z => misses (extensions y z))) = true := by
  decide +kernel

lemma case_57_two : misses (next ((⟨4294967295, 0⟩ : Signal) :: boundary)) = true := by
  decide +kernel

lemma case_57_three : (next ((⟨4294967295, 0⟩ : Signal) :: boundary)).all (fun y =>
    (y :: (⟨4294967295, 0⟩ : Signal) :: boundary).all (fun z => misses (extensions y z))) = true := by
  decide +kernel

lemma not_two : (next boundary).all (fun x => misses (next (x :: boundary))) = true := by
  simp only [firsts_eq, firsts, List.all_cons, List.all_nil,
    case_0_two,
    case_1_two,
    case_2_two,
    case_3_two,
    case_4_two,
    case_5_two,
    case_6_two,
    case_7_two,
    case_8_two,
    case_9_two,
    case_10_two,
    case_11_two,
    case_12_two,
    case_13_two,
    case_14_two,
    case_15_two,
    case_16_two,
    case_17_two,
    case_18_two,
    case_19_two,
    case_20_two,
    case_21_two,
    case_22_two,
    case_23_two,
    case_24_two,
    case_25_two,
    case_26_two,
    case_27_two,
    case_28_two,
    case_29_two,
    case_30_two,
    case_31_two,
    case_32_two,
    case_33_two,
    case_34_two,
    case_35_two,
    case_36_two,
    case_37_two,
    case_38_two,
    case_39_two,
    case_40_two,
    case_41_two,
    case_42_two,
    case_43_two,
    case_44_two,
    case_45_two,
    case_46_two,
    case_47_two,
    case_48_two,
    case_49_two,
    case_50_two,
    case_51_two,
    case_52_two,
    case_53_two,
    case_54_two,
    case_55_two,
    case_56_two,
    case_57_two, Bool.true_and]

lemma not_three : (next boundary).all (fun x =>
    (next (x :: boundary)).all (fun y =>
      (y :: x :: boundary).all (fun z => misses (extensions y z)))) = true := by
  simp only [firsts_eq, firsts, List.all_cons, List.all_nil,
    case_0_three,
    case_1_three,
    case_2_three,
    case_3_three,
    case_4_three,
    case_5_three,
    case_6_three,
    case_7_three,
    case_8_three,
    case_9_three,
    case_10_three,
    case_11_three,
    case_12_three,
    case_13_three,
    case_14_three,
    case_15_three,
    case_16_three,
    case_17_three,
    case_18_three,
    case_19_three,
    case_20_three,
    case_21_three,
    case_22_three,
    case_23_three,
    case_24_three,
    case_25_three,
    case_26_three,
    case_27_three,
    case_28_three,
    case_29_three,
    case_30_three,
    case_31_three,
    case_32_three,
    case_33_three,
    case_34_three,
    case_35_three,
    case_36_three,
    case_37_three,
    case_38_three,
    case_39_three,
    case_40_three,
    case_41_three,
    case_42_three,
    case_43_three,
    case_44_three,
    case_45_three,
    case_46_three,
    case_47_three,
    case_48_three,
    case_49_three,
    case_50_three,
    case_51_three,
    case_52_three,
    case_53_three,
    case_54_three,
    case_55_three,
    case_56_three,
    case_57_three, Bool.true_and]

end PEqualNP.Outside.L_meta_1031.P5Boundary

#print axioms PEqualNP.Outside.L_meta_1031.P5Boundary.firsts_eq
#print axioms PEqualNP.Outside.L_meta_1031.P5Boundary.not_two
#print axioms PEqualNP.Outside.L_meta_1031.P5Boundary.not_three
