import RootSevenBase
namespace PEqualNP.Outside.L_meta_670_aux.RootSeven

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma enumerate12 : MetadataReplay.enabledNodes config 12 4 = nodes12 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma checks12 : ∀ i : Fin nodes12.length,
    MetadataReplay.nodeCheck config 12 4 nodes12[i.val] = true := by
  intro i
  fin_cases i <;> decide +kernel

lemma level12 : MetadataReplay.levelCheck config 12 4 = true :=
  MetadataReplay.levelCheck_of_list config nodes12 enumerate12 checks12

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma enumerate13 : MetadataReplay.enabledNodes config 13 5 = nodes13 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma checks13 : ∀ i : Fin nodes13.length,
    MetadataReplay.nodeCheck config 13 5 nodes13[i.val] = true := by
  intro i
  fin_cases i <;> decide +kernel

lemma level13 : MetadataReplay.levelCheck config 13 5 = true :=
  MetadataReplay.levelCheck_of_list config nodes13 enumerate13 checks13

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma enumerate14 : MetadataReplay.enabledNodes config 14 6 = nodes14 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma checks14 : ∀ i : Fin nodes14.length,
    MetadataReplay.nodeCheck config 14 6 nodes14[i.val] = true := by
  intro i
  fin_cases i <;> decide +kernel

lemma level14 : MetadataReplay.levelCheck config 14 6 = true :=
  MetadataReplay.levelCheck_of_list config nodes14 enumerate14 checks14

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma enumerate15 : MetadataReplay.enabledNodes config 15 7 = nodes15 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma checks15 : ∀ i : Fin nodes15.length,
    MetadataReplay.nodeCheck config 15 7 nodes15[i.val] = true := by
  intro i
  fin_cases i <;> decide +kernel

lemma level15 : MetadataReplay.levelCheck config 15 7 = true :=
  MetadataReplay.levelCheck_of_list config nodes15 enumerate15 checks15

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma root_link : MetadataReplay.linkCheck config (Cut12StrictReplay.hint 15 7 1876) 15 7 LiveCheck.raw = true := by
  decide +kernel

end PEqualNP.Outside.L_meta_670_aux.RootSeven
