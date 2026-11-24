import Case159GrandCommon

namespace PEqualNP.Outside.L_meta_670_aux.CompactCase159

open LiveCheck FiniteCase159

def smallTop : List Nat := [10,11,16,17,41,43,53,55]
def smallGrand : List Nat := [0,1,12,13,18,19,31,37]

def topCheck (i : Nat) : Bool :=
  if i = 56 then true else if i ∈ smallTop then check i else prefixCheck i

def grandCheckChoice (i : Nat) : Bool :=
  if i ∈ smallGrand then grandCheck i else grandPrefixCheck i

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma top_checked : ∀ i : Fin 59, topCheck i.val = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma grand_checked : ∀ i : Fin 44, grandCheckChoice i.val = true := by
  intro i
  fin_cases i <;> decide +kernel

lemma grand_excluded (i : Fin 44) :
    Impossible 11 (grandchild i.val).nots (grandchild i.val).wires := by
  have h := grand_checked i
  by_cases hi : i.val ∈ smallGrand
  · exact grandCheck_sound i.val (by simpa only [grandCheckChoice,if_pos hi] using h)
  · exact grandPrefixCheck_sound i.val (by simpa only [grandCheckChoice,if_neg hi] using h)

lemma grandchildren : ∀ p ∈ proposals56, Impossible 11 p.nots p.wires := by
  intro p hp
  obtain ⟨i,hi,he⟩ := List.getElem_of_mem hp
  have hi44 : i < 44 := by simpa only [grandchild_count] using hi
  have hs := grand_excluded ⟨i,hi44⟩
  have hc : grandchild i = p := by
    simp only [grandchild,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,
      Option.getD_some,he]
  change Impossible 11 (grandchild i).nots (grandchild i).wires at hs
  simpa only [hc] using hs

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma grand_parent_checked : ProjectedChild.parentCheck 11
    (child 56).nots (child 56).wires = true := by decide +kernel

lemma child56 : Impossible 12 (child 56).nots (child 56).wires :=
  ProjectedChild.parentCheck_sound grandchildren grand_parent_checked

lemma top_excluded (i : Fin 59) :
    Impossible 12 (child i.val).nots (child i.val).wires := by
  have h := top_checked i
  by_cases hi : i.val = 56
  · simpa only [hi] using child56
  · by_cases hs : i.val ∈ smallTop
    · exact check_sound i.val (by simpa only [topCheck,if_neg hi,if_pos hs] using h)
    · exact prefixCheck_sound i.val (by simpa only [topCheck,if_neg hi,if_neg hs] using h)

lemma children : ∀ p ∈ proposals, Impossible 12 p.nots p.wires := by
  intro p hp
  obtain ⟨i,hi,he⟩ := List.getElem_of_mem hp
  have hi59 : i < 59 := by simpa only [child_count] using hi
  have hs := top_excluded ⟨i,hi59⟩
  have hc : child i = p := by
    simp only [child,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,
      Option.getD_some,he]
  change Impossible 12 (child i).nots (child i).wires at hs
  simpa only [hc] using hs

lemma excluded : Impossible 13 2 case159State :=
  ProjectedChild.parentCheck_sound children FiniteCase159.parent_checked

end PEqualNP.Outside.L_meta_670_aux.CompactCase159

#print axioms PEqualNP.Outside.L_meta_670_aux.CompactCase159.excluded
