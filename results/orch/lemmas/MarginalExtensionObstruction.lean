import CanonicalExtensionCover
import MarginalCoverFinite

namespace PEqualNP.Outside.L_meta_1896_aux.MarginalExtensionObstruction

open PEqualNP.Outside.L_meta_1896_aux.CanonicalCompiler
open PEqualNP.Outside.L_meta_1896_aux.MarginalCoverFinite

lemma table_extension_needs_eight (k : Nat) (program : Program 98 k)
    (hbad : evaluate k program wireBad = false)
    (hgood : ∀ a : Fin 52, evaluate k program (wireGood a) = true) : 8 ≤ k := by
  have h := extension_cover_lower_bound k program wireBad wireGood 9
    nine_le_table_cover_card hbad hgood
  omega

lemma retained_forty_eight_needs_fifty_six (k : Nat) (program : Program 98 k)
    (hbad : evaluate k program wireBad = false)
    (hgood : ∀ a : Fin 52, evaluate k program (wireGood a) = true) : 56 ≤ 48 + k := by
  have h := table_extension_needs_eight k program hbad hgood
  omega

end PEqualNP.Outside.L_meta_1896_aux.MarginalExtensionObstruction
