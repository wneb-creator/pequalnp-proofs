import PEqualNP.MetaComplexity.Helpers.Deg2Cover
import PEqualNP.MetaComplexity.Helpers.Deg2S0Top

/-!
# Below the edge function: the cover (card D2-17)

`card17_cover` with "computes" weakened to "below", for the incident pairs the circuit accepts.
Conjecture until checked.
-/

namespace PEqualNP.MetaComplexity.Deg2

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

open PEqualNP.MetaComplexity.Deg2.Api PEqualNP.MetaComplexity.Deg2.Path

variable {N : ℕ}

theorem cv_honest_of_list_below (I : Fin N → Fin N → Prop) (D : Dag N) (hc : Below I D.fn)
    (hid : ∀ x : Fin (N + N) → Bool, D.fn x = true ↔
      ∃ b, D.IsItem b ∧ D.ctx b x = true ∧ ∀ r, D.IsFactor b r → D.val x r = true)
    (p w : Fin N) {b : ℕ} (hb : D.IsItem b) (hctx : D.ctx b (ep p w) = true)
    (hf : ∀ r, D.IsFactor b r → D.val (ep p w) r = true) (ws : List ℕ)
    (hws : ∀ r, D.IsFactor b r ↔ r ∈ ws) :
    ∃ r ∈ ws, IsHonest I (fun x => D.val x r) p := by
  have key := HonestFactor.main N I (D.ctx b) (ws.map (fun r x => D.val x r)) p w
    (cv_ctx_mono D b) (fun z z' h => cv_ctx_pts D b h)
    (by
      intro f hfm
      simp only [List.mem_map] at hfm
      obtain ⟨r, -, rfl⟩ := hfm
      intro x y hxy
      exact api_val_mono D r hxy)
    (by
      intro z hz
      rw [Bool.and_eq_true, List.all_map, List.all_eq_true] at hz
      apply hc z
      apply (hid z).2
      refine ⟨b, hb, hz.1, fun r hr => ?_⟩
      have := hz.2 r ((hws r).1 hr)
      simpa using this)
    (by
      rw [cv_ep_eq', Bool.and_eq_true, List.all_map, List.all_eq_true]
      refine ⟨hctx, fun r hr => ?_⟩
      have := hf r ((hws r).2 hr)
      simpa using this)
  obtain ⟨-, f, hfm, hf0, hfu⟩ := key
  simp only [List.mem_map] at hfm
  obtain ⟨r, hr, rfl⟩ := hfm
  refine ⟨r, hr, ?_, fun u hu => hfu u ?_⟩
  · rw [cv_pt_eq]; exact hf0
  · rw [cv_ep_eq']; exact hu

theorem cv_honest_factor_below (I : Fin N → Fin N → Prop) (D : Dag N) (hwf : D.WF)
    (hc : Below I D.fn)
    (hid : ∀ x : Fin (N + N) → Bool, D.fn x = true ↔
      ∃ b, D.IsItem b ∧ D.ctx b x = true ∧ ∀ r, D.IsFactor b r → D.val x r = true)
    (p w : Fin N) {b : ℕ} (hb : D.IsItem b) (hctx : D.ctx b (ep p w) = true)
    (hf : ∀ r, D.IsFactor b r → D.val (ep p w) r = true) :
    ∃ r, D.IsFactor b r ∧ D.deg r = 1 ∧ IsHonest I (fun x => D.val x r) p := by
  classical
  rcases hb.2 with hb1 | hbt
  · have hws : ∀ r, D.IsFactor b r ↔ r ∈ [b] := by
      intro r
      constructor
      · rintro (⟨_, rfl⟩ | ⟨hT, _⟩)
        · simp
        · have : D.deg b = 2 := by
            unfold Dag.Tmix Dag.T at hT
            exact (Finset.mem_filter.1 (Finset.mem_filter.1 hT).1).2
          omega
      · intro hr
        simp only [List.mem_singleton] at hr
        exact Or.inl ⟨hb1, hr⟩
    obtain ⟨r, hr, hh⟩ := cv_honest_of_list_below I D hc hid p w hb hctx hf [b] hws
    simp only [List.mem_singleton] at hr
    subst hr
    refine ⟨r, Or.inl ⟨hb1, rfl⟩, ?_, hh⟩
    rcases Nat.lt_or_ge (D.deg r) 1 with h0 | h1
    · exfalso
      have e1 := hf r (Or.inl ⟨hb1, rfl⟩)
      rw [← api_val_xonly D (by omega) (x := pt p) (y := ep p w)
        (fun q => by rw [circ_ep_pts])] at e1
      have := hh.1
      simp only at this
      rw [this] at e1
      exact Bool.false_ne_true e1
    · omega
  · have hbt' := hbt
    unfold Dag.Tmix at hbt'
    obtain ⟨-, a, a', hg, ha1, ha1'⟩ := Finset.mem_filter.1 hbt'
    have hlt := hwf b _ hg
    have hal : a < b := hlt a (by simp [G.kids])
    have hal' : a' < b := hlt a' (by simp [G.kids])
    have hT2 : D.deg b = 2 := by
      unfold Dag.Tmix Dag.T at hbt
      exact (Finset.mem_filter.1 (Finset.mem_filter.1 hbt).1).2
    have hws : ∀ r, D.IsFactor b r ↔ r ∈ [a, a'] := by
      intro r
      constructor
      · rintro (⟨h, _⟩ | ⟨_, hk⟩)
        · omega
        · obtain ⟨g, hg', hrg, -⟩ := hk
          rw [hg] at hg'
          cases hg'
          simpa [G.kids] using hrg
      · intro hr
        refine Or.inr ⟨hbt, circ_kid_of hg ?_ ?_⟩
        · simpa [G.kids] using hr
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> assumption
    obtain ⟨r, hr, hh⟩ := cv_honest_of_list_below I D hc hid p w ⟨hb.1, Or.inr hbt⟩ hctx hf [a, a'] hws
    refine ⟨r, (hws r).2 hr, ?_, hh⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> assumption

/-- D2-17 (cover) for a circuit below the edge function: on the cleaned circuit every accepted
incident pair is pinned, served, in `F_2` or a marker edge. -/
theorem card17_cover_below
    (I : Fin N → Fin N → Prop) (D : Dag N) (hwf : D.WF)
    (hc : Below I D.fn) (hd : D.deg D.out ≤ 2) (hcl : D.Cleaned I D.cone) :
    ∀ p w : Fin N, I p w → D.fn (ep p w) = true →
      (p, w) ∈ D.pinned I ∪ D.served I ∪ D.fSet I D.cone 2 ∪ D.markerEdges I := by
  classical
  intro p w hpw hacc
  have hid' := card15_identity_below I D hwf hc hd
  obtain ⟨b, hb, hctx, hf⟩ := (hid' _).1 hacc
  obtain ⟨r, hfac, hr1, hh⟩ := cv_honest_factor_below I D hwf hc hid' p w hb hctx hf
  have hrw := hf r hfac
  obtain ⟨π, hπ, hπv, hlab, hpen⟩ := card06_honest_path I D r p w hr1 hh hrw
  have hdeg : ∀ v ∈ π, D.deg v = 1 := fun v hv => (hπv v hv).1
  have hreach_r : D.Reach D.out r := by
    rcases hfac with ⟨_, rfl⟩ | ⟨_, hk⟩
    · exact cv_top_reach D hb.1
    · exact (cv_top_reach D hb.1).tail hk
  have hreach : ∀ j, j < π.length → D.Reach D.out (π.getD j 0) :=
    fun j hj => hreach_r.trans (cv_path_reach D hπ j hj)
  have hlen : 0 < π.length := by
    cases π with
    | nil => simp [Dag.IsPath] at hπ
    | cons _ _ => simp
  have hhead : π.getD 0 0 = r := by
    obtain ⟨hh0, -, -⟩ := hπ
    cases π with
    | nil => simp at hh0
    | cons c _ => simpa using hh0
  simp only [Finset.mem_union]
  let P : ℕ → Prop := fun k => k + 1 < π.length ∧ ∃ f, D.LabAnd (π.getD k 0) f (π.getD (k + 1) 0)
  by_cases hex : ∃ k, P k
  · -- I: a labelled wire on the path; the last one
    obtain ⟨k0, hk0⟩ := hex
    let K := Nat.findGreatest P π.length
    have hPK : P K := Nat.findGreatest_spec (P := P) (by have := hk0.1; omega) hk0
    have hmax : ∀ k, K < k → ¬ P k := by
      intro k hk hPk
      exact Nat.findGreatest_is_greatest hk (by have := hPk.1; omega) hPk
    obtain ⟨hK, f, hfl⟩ := hPK
    set e := π.getD K 0 with he
    set v := π.getD (K + 1) 0 with hv
    have hvr : D.VReach v w := by
      refine cv_vreach_suffix D hwf hπ hdeg (π.length - (K + 1) - 1) (K + 1) (by omega) ?_
      intro k f' hk hk' hl
      exact hmax k (by omega) ⟨hk', f', hl⟩
    have hvmem : v ∈ π := circ_getD_mem hK
    rcases cv_card_split (cv_vstar_mem hvr) with h2 | h1
    · left; left; left
      exact cv_pinned I D hvr (hreach _ hK) (hdeg v hvmem) (hpen v hvmem) h2
    · -- the labelled wire e = AND(f, v)
      obtain ⟨hgate, hf0, -⟩ := hfl
      have hemem : e ∈ π := circ_getD_mem (by omega)
      have hgE : ∃ g, D.gateAt e = some g := by
        rcases hgate with h | h
        · exact ⟨_, h⟩
        · exact ⟨_, h⟩
      obtain ⟨gE, hgE⟩ := hgE
      have hElt := cv_gate_lt D hgE
      have hEcone := cv_mem_cone D hElt.1 hElt.2 (hreach K (by omega))
      have hAndM : e ∈ D.AndM := by
        unfold Dag.AndM Dag.M
        refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hEcone, hdeg e hemem⟩, ?_⟩
        rcases hgate with h | h
        · exact ⟨_, _, h⟩
        · exact ⟨_, _, h⟩
      have hdead := hcl e hEcone f v ⟨hgate, hf0, hdeg v hvmem⟩
      have halive : p ∈ D.alive f := by
        unfold Dag.alive
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hlab K f hK ⟨hgate, hf0, hdeg v hvmem⟩⟩
      by_cases hle : (D.alive f ∩ ptsOn I w).card ≤ 2
      · left; left; right
        unfold Dag.served
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, e, hAndM, f, v,
          ⟨hgate, hf0, hdeg v hvmem⟩, h1, halive, hpw, hle⟩
      · left; right
        have hfk : D.Kid e f := by
          rcases hgate with h | h
          · exact circ_kid_of h (by simp [G.kids]) (hwf e _ h f (by simp [G.kids]))
          · exact circ_kid_of h (by simp [G.kids]) (hwf e _ h f (by simp [G.kids]))
        have hfgate : N + N ≤ f := by
          by_contra hlt
          have h1' := circ_alive_input D (i := f) (by omega)
          have := Finset.card_le_card (Finset.inter_subset_left (s₁ := D.alive f)
            (s₂ := ptsOn I w))
          omega
        have hfcone : f ∈ D.cone :=
          cv_mem_cone D hfgate (by have := circ_kid_lt hfk; omega)
            ((hreach K (by omega)).tail hfk)
        unfold Dag.fSet
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hpw, f, hfcone, hf0, hdead, halive,
          by show 2 + 1 ≤ (D.alive f ∩ ptsOn I w).card; omega⟩
  · -- II: no labelled wire on the path
    have hrv : D.VReach r w := by
      have := cv_vreach_suffix D hwf hπ hdeg (π.length - 1) 0 (by omega)
        (fun k f' _ hk' hl => hex ⟨k, hk', f', hl⟩)
      rwa [hhead] at this
    have hrmem : r ∈ π := by rw [← hhead]; exact circ_getD_mem hlen
    rcases cv_card_split (cv_vstar_mem hrv) with h2 | h1
    · left; left; left
      exact cv_pinned I D hrv hreach_r hr1 (hpen r hrmem) h2
    · right
      unfold Dag.markerEdges
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, hpw, b, hb, ?_, hf, r, hfac, hr1, h1⟩
      rw [cv_ctx_pts D b (y := ep p w) (fun q => by rw [circ_ep_pts])]
      exact hctx

end PEqualNP.MetaComplexity.Deg2
