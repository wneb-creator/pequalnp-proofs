import ResidualShape4293
import Public4293

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore
open DagTools

set_option maxHeartbeats 0 in
theorem residual_exclude4293 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 4293=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := Compact.construct_layout (k:=2) h hc bp eq (by decide +kernel)
  obtain ⟨empty5,empty10⟩ := residual_empty4293 h hc z eq Z.branch Z.pure Z.order
  apply Public4293.low_slots_impossible h hc eq
  · simpa only [Compact.countAt,empty5,Finset.card_empty,Nat.add_zero] using Z.size_code h hc 5
  · simpa only [Compact.countAt,empty10,Finset.card_empty,Nat.add_zero] using Z.size_code h hc 10

end PEqualNP.Outside.L_meta_9775.UpstreamCore
