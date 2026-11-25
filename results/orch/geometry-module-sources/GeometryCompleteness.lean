import GeometryCompletenessGroup0
import GeometryCompletenessGroup1
import GeometryCompletenessGroup2
import GeometryCompletenessGroup3
import GeometryCompletenessGroup4
import GeometryCompletenessGroup5
import GeometryCompletenessGroup6
import GeometryCompletenessGroup7

namespace PEqualNP.Outside.L_meta_1896_aux.GeometryComplete

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma masks_classified : ∀ m : Fin 8192,
    AllRows.admissible (decode m) → AllRows.points (rowFor m) = decode m := by
  apply classified_of_chunks rowFor
  exact (Fin.cases classified_0 (Fin.cases classified_1 (Fin.cases classified_2 (Fin.cases classified_3 (Fin.cases classified_4 (Fin.cases classified_5 (Fin.cases classified_6 (Fin.cases classified_7 (Fin.cases classified_8 (Fin.cases classified_9 (Fin.cases classified_10 (Fin.cases classified_11 (Fin.cases classified_12 (Fin.cases classified_13 (Fin.cases classified_14 (Fin.cases classified_15 (Fin.cases classified_16 (Fin.cases classified_17 (Fin.cases classified_18 (Fin.cases classified_19 (Fin.cases classified_20 (Fin.cases classified_21 (Fin.cases classified_22 (Fin.cases classified_23 (Fin.cases classified_24 (Fin.cases classified_25 (Fin.cases classified_26 (Fin.cases classified_27 (Fin.cases classified_28 (Fin.cases classified_29 (Fin.cases classified_30 (Fin.cases classified_31 (Fin.cases classified_32 (Fin.cases classified_33 (Fin.cases classified_34 (Fin.cases classified_35 (Fin.cases classified_36 (Fin.cases classified_37 (Fin.cases classified_38 (Fin.cases classified_39 (Fin.cases classified_40 (Fin.cases classified_41 (Fin.cases classified_42 (Fin.cases classified_43 (Fin.cases classified_44 (Fin.cases classified_45 (Fin.cases classified_46 (Fin.cases classified_47 (Fin.cases classified_48 (Fin.cases classified_49 (Fin.cases classified_50 (Fin.cases classified_51 (Fin.cases classified_52 (Fin.cases classified_53 (Fin.cases classified_54 (Fin.cases classified_55 (Fin.cases classified_56 (Fin.cases classified_57 (Fin.cases classified_58 (Fin.cases classified_59 (Fin.cases classified_60 (Fin.cases classified_61 (Fin.cases classified_62 (Fin.cases classified_63 (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

lemma admissible_complete (X : Finset (Fin 13)) (hX : AllRows.admissible X) :
    ∃ r : AllRows.R, AllRows.points r = X := by
  exact complete_of_classified rowFor masks_classified X hX

end PEqualNP.Outside.L_meta_1896_aux.GeometryComplete
