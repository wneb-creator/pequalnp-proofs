import Case159Child11
import Case159Prefixes
import Case159OtherChildren
namespace PEqualNP.Outside.L_meta_670_aux.FiniteCase159
open LiveCheck
lemma all59 (h56 : Impossible 12 (child 56).nots (child 56).wires) :
    ∀ i : Fin 59, Impossible 12 (child i.val).nots (child i.val).wires := by
  intro i
  fin_cases i
  · exact prefixCheck_sound 0 prefix0_checked
  · exact prefixCheck_sound 1 prefix1_checked
  · exact prefixCheck_sound 2 prefix2_checked
  · exact prefixCheck_sound 3 prefix3_checked
  · exact prefixCheck_sound 4 prefix4_checked
  · exact prefixCheck_sound 5 prefix5_checked
  · exact prefixCheck_sound 6 prefix6_checked
  · exact prefixCheck_sound 7 prefix7_checked
  · exact prefixCheck_sound 8 prefix8_checked
  · exact prefixCheck_sound 9 prefix9_checked
  · exact check_sound 10 child10_checked
  · exact check_sound 11 child11_checked
  · exact prefixCheck_sound 12 prefix12_checked
  · exact prefixCheck_sound 13 prefix13_checked
  · exact prefixCheck_sound 14 prefix14_checked
  · exact prefixCheck_sound 15 prefix15_checked
  · exact check_sound 16 child16_checked
  · exact check_sound 17 child17_checked
  · exact prefixCheck_sound 18 prefix18_checked
  · exact prefixCheck_sound 19 prefix19_checked
  · exact prefixCheck_sound 20 prefix20_checked
  · exact prefixCheck_sound 21 prefix21_checked
  · exact prefixCheck_sound 22 prefix22_checked
  · exact prefixCheck_sound 23 prefix23_checked
  · exact prefixCheck_sound 24 prefix24_checked
  · exact prefixCheck_sound 25 prefix25_checked
  · exact prefixCheck_sound 26 prefix26_checked
  · exact prefixCheck_sound 27 prefix27_checked
  · exact prefixCheck_sound 28 prefix28_checked
  · exact prefixCheck_sound 29 prefix29_checked
  · exact prefixCheck_sound 30 prefix30_checked
  · exact prefixCheck_sound 31 prefix31_checked
  · exact prefixCheck_sound 32 prefix32_checked
  · exact prefixCheck_sound 33 prefix33_checked
  · exact prefixCheck_sound 34 prefix34_checked
  · exact prefixCheck_sound 35 prefix35_checked
  · exact prefixCheck_sound 36 prefix36_checked
  · exact prefixCheck_sound 37 prefix37_checked
  · exact prefixCheck_sound 38 prefix38_checked
  · exact prefixCheck_sound 39 prefix39_checked
  · exact prefixCheck_sound 40 prefix40_checked
  · exact check_sound 41 child41_checked
  · exact prefixCheck_sound 42 prefix42_checked
  · exact check_sound 43 child43_checked
  · exact prefixCheck_sound 44 prefix44_checked
  · exact prefixCheck_sound 45 prefix45_checked
  · exact prefixCheck_sound 46 prefix46_checked
  · exact prefixCheck_sound 47 prefix47_checked
  · exact prefixCheck_sound 48 prefix48_checked
  · exact prefixCheck_sound 49 prefix49_checked
  · exact prefixCheck_sound 50 prefix50_checked
  · exact prefixCheck_sound 51 prefix51_checked
  · exact prefixCheck_sound 52 prefix52_checked
  · exact check_sound 53 child53_checked
  · exact prefixCheck_sound 54 prefix54_checked
  · exact check_sound 55 child55_checked
  · exact h56
  · exact prefixCheck_sound 57 prefix57_checked
  · exact prefixCheck_sound 58 prefix58_checked

lemma children_sound (h56 : Impossible 12 (child 56).nots (child 56).wires) :
    ∀ p ∈ proposals, Impossible 12 p.nots p.wires := by
  intro p hp
  obtain ⟨i,hi,he⟩ := List.getElem_of_mem hp
  have hi59 : i < 59 := by simpa only [child_count] using hi
  have hs := all59 h56 ⟨i,hi59⟩
  have hc : child i = p := by
    simp only [child,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some,he]
  change Impossible 12 (child i).nots (child i).wires at hs
  simpa only [hc] using hs

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma parent_checked : ProjectedChild.parentCheck 12 2 case159State = true := by decide +kernel

lemma case159_excluded_of_child56
    (h56 : Impossible 12 (child 56).nots (child 56).wires) : Impossible 13 2 case159State :=
  ProjectedChild.parentCheck_sound (children_sound h56) parent_checked
end PEqualNP.Outside.L_meta_670_aux.FiniteCase159
