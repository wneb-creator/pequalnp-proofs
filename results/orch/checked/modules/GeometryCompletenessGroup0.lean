import GeometryMaskData
import GeometryCompletenessProofs

namespace PEqualNP.Outside.L_meta_1896_aux.GeometryComplete

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma classified_0 : ∀ i : Fin 128,
    let m : Fin 8192 := ⟨128 * 0 + i.val, by omega⟩
    AllRows.admissible (decode m) → AllRows.points (rowFor m) = decode m := by
  unfold AllRows.admissible
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma classified_1 : ∀ i : Fin 128,
    let m : Fin 8192 := ⟨128 * 1 + i.val, by omega⟩
    AllRows.admissible (decode m) → AllRows.points (rowFor m) = decode m := by
  unfold AllRows.admissible
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma classified_2 : ∀ i : Fin 128,
    let m : Fin 8192 := ⟨128 * 2 + i.val, by omega⟩
    AllRows.admissible (decode m) → AllRows.points (rowFor m) = decode m := by
  unfold AllRows.admissible
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma classified_3 : ∀ i : Fin 128,
    let m : Fin 8192 := ⟨128 * 3 + i.val, by omega⟩
    AllRows.admissible (decode m) → AllRows.points (rowFor m) = decode m := by
  unfold AllRows.admissible
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma classified_4 : ∀ i : Fin 128,
    let m : Fin 8192 := ⟨128 * 4 + i.val, by omega⟩
    AllRows.admissible (decode m) → AllRows.points (rowFor m) = decode m := by
  unfold AllRows.admissible
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma classified_5 : ∀ i : Fin 128,
    let m : Fin 8192 := ⟨128 * 5 + i.val, by omega⟩
    AllRows.admissible (decode m) → AllRows.points (rowFor m) = decode m := by
  unfold AllRows.admissible
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma classified_6 : ∀ i : Fin 128,
    let m : Fin 8192 := ⟨128 * 6 + i.val, by omega⟩
    AllRows.admissible (decode m) → AllRows.points (rowFor m) = decode m := by
  unfold AllRows.admissible
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma classified_7 : ∀ i : Fin 128,
    let m : Fin 8192 := ⟨128 * 7 + i.val, by omega⟩
    AllRows.admissible (decode m) → AllRows.points (rowFor m) = decode m := by
  unfold AllRows.admissible
  decide +kernel

end PEqualNP.Outside.L_meta_1896_aux.GeometryComplete
