import Case159GrandPrefixes
import Case159GrandOthers
namespace PEqualNP.Outside.L_meta_670_aux.FiniteCase159
open LiveCheck
lemma all44 : ∀ i : Fin 44, Impossible 11 (grandchild i.val).nots (grandchild i.val).wires := by
  intro i
  fin_cases i
  · exact grandCheck_sound 0 grand0_checked
  · exact grandCheck_sound 1 grand1_checked
  · exact grandPrefixCheck_sound 2 grandprefix2_checked
  · exact grandPrefixCheck_sound 3 grandprefix3_checked
  · exact grandPrefixCheck_sound 4 grandprefix4_checked
  · exact grandPrefixCheck_sound 5 grandprefix5_checked
  · exact grandPrefixCheck_sound 6 grandprefix6_checked
  · exact grandPrefixCheck_sound 7 grandprefix7_checked
  · exact grandPrefixCheck_sound 8 grandprefix8_checked
  · exact grandPrefixCheck_sound 9 grandprefix9_checked
  · exact grandPrefixCheck_sound 10 grandprefix10_checked
  · exact grandPrefixCheck_sound 11 grandprefix11_checked
  · exact grandCheck_sound 12 grand12_checked
  · exact grandCheck_sound 13 grand13_checked
  · exact grandPrefixCheck_sound 14 grandprefix14_checked
  · exact grandPrefixCheck_sound 15 grandprefix15_checked
  · exact grandPrefixCheck_sound 16 grandprefix16_checked
  · exact grandPrefixCheck_sound 17 grandprefix17_checked
  · exact grandCheck_sound 18 grand18_checked
  · exact grandCheck_sound 19 grand19_checked
  · exact grandPrefixCheck_sound 20 grandprefix20_checked
  · exact grandPrefixCheck_sound 21 grandprefix21_checked
  · exact grandPrefixCheck_sound 22 grandprefix22_checked
  · exact grandPrefixCheck_sound 23 grandprefix23_checked
  · exact grandPrefixCheck_sound 24 grandprefix24_checked
  · exact grandPrefixCheck_sound 25 grandprefix25_checked
  · exact grandPrefixCheck_sound 26 grandprefix26_checked
  · exact grandPrefixCheck_sound 27 grandprefix27_checked
  · exact grandPrefixCheck_sound 28 grandprefix28_checked
  · exact grandPrefixCheck_sound 29 grandprefix29_checked
  · exact grandPrefixCheck_sound 30 grandprefix30_checked
  · exact grandCheck_sound 31 grand31_checked
  · exact grandPrefixCheck_sound 32 grandprefix32_checked
  · exact grandPrefixCheck_sound 33 grandprefix33_checked
  · exact grandPrefixCheck_sound 34 grandprefix34_checked
  · exact grandPrefixCheck_sound 35 grandprefix35_checked
  · exact grandPrefixCheck_sound 36 grandprefix36_checked
  · exact grandCheck_sound 37 grand37_checked
  · exact grandPrefixCheck_sound 38 grandprefix38_checked
  · exact grandPrefixCheck_sound 39 grandprefix39_checked
  · exact grandPrefixCheck_sound 40 grandprefix40_checked
  · exact grandPrefixCheck_sound 41 grandprefix41_checked
  · exact grandPrefixCheck_sound 42 grandprefix42_checked
  · exact grandPrefixCheck_sound 43 grandprefix43_checked

lemma grandchildren_sound : ∀ p ∈ proposals56, Impossible 11 p.nots p.wires := by
  intro p hp
  obtain ⟨i,hi,he⟩ := List.getElem_of_mem hp
  have hi44 : i < 44 := by simpa only [grandchild_count] using hi
  have hs := all44 ⟨i,hi44⟩
  have hc : grandchild i = p := by
    simp only [grandchild,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some,he]
  change Impossible 11 (grandchild i).nots (grandchild i).wires at hs
  simpa only [hc] using hs

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma grand_parent_checked : ProjectedChild.parentCheck 11 (child 56).nots (child 56).wires = true := by
  decide +kernel

lemma child56_excluded : Impossible 12 (child 56).nots (child 56).wires :=
  ProjectedChild.parentCheck_sound grandchildren_sound grand_parent_checked

lemma case159_excluded : Impossible 13 2 case159State :=
  case159_excluded_of_child56 child56_excluded

end PEqualNP.Outside.L_meta_670_aux.FiniteCase159
