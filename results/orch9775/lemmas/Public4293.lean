import CompactFramework

/-
The last-case strategy below is adapted from `elim_132` / `pa_m1` in
Thomas Brovelli (GitHub ithurtstom), public PR #18338, exact head
79345c8812d893da9c305e0d1bec931bb198594a:
https://github.com/open-goat/pequalnp-proofs/pull/18338
This specialization uses our existing DagTools and direct slot counting.
-/
namespace PEqualNP.Outside.L_meta_9775.UpstreamCore
open DagTools
namespace Public4293

theorem assigned_mem {D : Dag} {pos : V → Nat × Bool}
    (hp : k4_Pos 14 adj D pos) {i x : V}
    (hi : i ∈ ineligSet 14 D) (hx : adj i x) : pos i ∈ sem_W 14 D x := by
  obtain ⟨h1,h2,h4,_⟩ := hp.1 i hi
  exact sem_mem_W.mpr ⟨h1,h4 x hx,by rw [h2]; exact Finset.notMem_empty x⟩

theorem assigned_private {D : Dag} {pos : V → Nat × Bool}
    (hp : k4_Pos 14 adj D pos) {i x : V}
    (hi : i ∈ ineligSet 14 D) (hx : sem_bar (pos i) ∈ sem_W 14 D x) : x=i := by
  have yes := (sem_mem_W.mp hx).2.1
  rw [show src D (sem_bar (pos i))=src D ((pos i).1, !(pos i).2) from rfl,
    (hp.1 i hi).2.2.2] at yes
  exact Finset.mem_singleton.mp yes

theorem two_slots {α : Type} [DecidableEq α] {S : Finset α} {a b : α}
    (ha : a∈S) (hb : b∈S) (ab : a≠b) (bound : S.card≤2) :
    ∀ e∈S, e=a ∨ e=b := by
  intro e he
  by_contra bad
  rw [not_or] at bad
  have many := Finset.two_lt_card.mpr ⟨e,he,a,ha,b,hb,bad.1,bad.2,ab⟩
  omega

set_option maxHeartbeats 0 in
theorem low_slots_impossible {D : Dag} (h : StrictLive 14 D)
    (hc : sem_Comp 14 adj D) (eq : mask 4293=ineligSet 14 D)
    (h5 : (sem_W 14 D 5).card≤2) (h10 : (sem_W 14 D 10).card≤2) : False := by
  classical
  obtain ⟨pos,hp⟩ := k4_assigned graph_ok h hc
  have i0 : (0:V)∈ineligSet 14 D := eq ▸ (by decide +kernel : (0:V)∈mask 4293)
  have i12 : (12:V)∈ineligSet 14 D := eq ▸ (by decide +kernel : (12:V)∈mask 4293)
  have p0 := assigned_mem hp i0 (by decide +kernel : adj 0 10)
  have p12 := assigned_mem hp i12 (by decide +kernel : adj 12 5)
  obtain ⟨e,he,be,_⟩ := sem_edge_slots graph_ok h.1 hc (by decide +kernel : adj 5 10)
  obtain ⟨f,hf,bf,_⟩ := sem_edge_slots graph_ok h.1 hc (by decide +kernel : adj 5 9)
  have ep : e≠pos 12 := by
    intro same
    have bad : (10:V)=12 := assigned_private hp i12 (same ▸ be)
    exact (by decide : (10:V)≠12) bad
  have fp : f≠pos 12 := by
    intro same
    have bad : (9:V)=12 := assigned_private hp i12 (same ▸ bf)
    exact (by decide : (9:V)≠12) bad
  have fe : f=e := (two_slots p12 he ep.symm h5 f hf).resolve_left fp
  have be0 : sem_bar e≠pos 0 := by
    intro same
    have hei : sem_bar (pos 0)∈sem_W 14 D 5 := by rw [←same,sem_bar_bar]; exact he
    have bad : (5:V)=0 := assigned_private hp i0 hei
    exact (by decide : (5:V)≠0) bad
  obtain ⟨g,hg,no8,no9⟩ := sem_cover_free graph_ok h.1 hc
    (by decide +kernel : ¬adj 8 9) (by decide +kernel : adj 10 4)
    (by decide +kernel : ¬adj 4 8) (by decide +kernel : ¬adj 4 9)
  have gp : g≠pos 0 := by
    intro same
    exact no8 (same ▸ (hp.1 0 i0).2.2.1 8 (by decide +kernel : adj 0 8))
  have ge : g=sem_bar e := (two_slots p0 be be0.symm h10 g hg).resolve_left gp
  exact no9 (by rw [ge,←fe]; exact (sem_mem_W.mp bf).2.1)

end Public4293
end PEqualNP.Outside.L_meta_9775.UpstreamCore
