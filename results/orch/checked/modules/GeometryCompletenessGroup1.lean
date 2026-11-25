import GeometryMaskData
import GeometryCompletenessProofs

namespace PEqualNP.Outside.L_meta_1896_aux.GeometryComplete

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma classified_8 : ∀ i : Fin 128,
    let m : Fin 8192 := ⟨128 * 8 + i.val, by omega⟩
    AllRows.admissible (decode m) → AllRows.points (rowFor m) = decode m := by
  unfold AllRows.admissible
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma classified_9 : ∀ i : Fin 128,
    let m : Fin 8192 := ⟨128 * 9 + i.val, by omega⟩
    AllRows.admissible (decode m) → AllRows.points (rowFor m) = decode m := by
  unfold AllRows.admissible
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma classified_10 : ∀ i : Fin 128,
    let m : Fin 8192 := ⟨128 * 10 + i.val, by omega⟩
    AllRows.admissible (decode m) → AllRows.points (rowFor m) = decode m := by
  unfold AllRows.admissible
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma classified_11 : ∀ i : Fin 128,
    let m : Fin 8192 := ⟨128 * 11 + i.val, by omega⟩
    AllRows.admissible (decode m) → AllRows.points (rowFor m) = decode m := by
  unfold AllRows.admissible
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma classified_12 : ∀ i : Fin 128,
    let m : Fin 8192 := ⟨128 * 12 + i.val, by omega⟩
    AllRows.admissible (decode m) → AllRows.points (rowFor m) = decode m := by
  unfold AllRows.admissible
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma classified_13 : ∀ i : Fin 128,
    let m : Fin 8192 := ⟨128 * 13 + i.val, by omega⟩
    AllRows.admissible (decode m) → AllRows.points (rowFor m) = decode m := by
  unfold AllRows.admissible
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma classified_14 : ∀ i : Fin 128,
    let m : Fin 8192 := ⟨128 * 14 + i.val, by omega⟩
    AllRows.admissible (decode m) → AllRows.points (rowFor m) = decode m := by
  unfold AllRows.admissible
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma classified_15 : ∀ i : Fin 128,
    let m : Fin 8192 := ⟨128 * 15 + i.val, by omega⟩
    AllRows.admissible (decode m) → AllRows.points (rowFor m) = decode m := by
  unfold AllRows.admissible
  decide +kernel

end PEqualNP.Outside.L_meta_1896_aux.GeometryComplete
