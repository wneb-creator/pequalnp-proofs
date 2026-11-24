import PEqualNP.MetaComplexity.Helpers.Deg2Transp4
import PEqualNP.MetaComplexity.Helpers.Deg2S0Top

/-!
# Below the edge function: the marker form (card D2-16)

`card16_form` with "computes" weakened to "below". Conjecture until checked.
-/

namespace PEqualNP.MetaComplexity.Deg2

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

variable {N : ℕ}

/-- A term under `y_w` is below the edge function: an item `b`, a factor `r` of `b` that is a
marker of `w`, `y_w` on, the context true and every other factor true. -/
theorem tr_term_sound_below (I : Fin N → Fin N → Prop) {D : Dag N} (hwf : D.WF)
    (hc : Below I D.fn) (hd : D.deg D.out ≤ 2) {b r : ℕ} {w : Fin N} (hb : D.IsItem b)
    (hm : D.IsMarker r w) (z : Fin (N + N) → Bool)
    (hz : z (Fin.natAdd N w) = true) (hctx : D.ctx b z = true)
    (hrest : ∀ x, D.IsFactor b x → x ≠ r → D.val z x = true) :
    ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true := by
  refine hc z ((card15_identity_below I D hwf hc hd z).2 ⟨b, hb, hctx, fun x hx => ?_⟩)
  by_cases hxr : x = r
  · subst hxr; exact tr_marker_above hwf hm z hz
  · exact hrest x hx hxr

/-- G2: a marker item of degree at most one never has the constant context. -/
theorem tr_no_const_below (I : Fin N → Fin N → Prop) {D : Dag N} (hwf : D.WF)
    (hc : Below I D.fn) (hd : D.deg D.out ≤ 2) {b : ℕ} {w : Fin N} (hb : D.IsItem b)
    (hb1 : D.deg b ≤ 1) (hm : D.IsMarker b w) : ¬ ∀ x, D.ctx b x = true := by
  classical
  intro hall
  have hz : inp (∅ : Finset (Fin N)) {w} (Fin.natAdd N w) = true := by
    unfold inp; rw [Fin.addCases_right]; simp
  obtain ⟨p, l, -, hp, -⟩ := tr_term_sound_below I hwf hc hd hb hm _ hz (hall _)
    (fun x hx hxb => by
      rcases hx with ⟨-, rfl⟩ | ⟨hmix, -⟩
      · exact absurd rfl hxb
      · have := (Finset.mem_filter.1 (Finset.mem_filter.1 hmix).1).2; omega)
  unfold inp at hp
  rw [Fin.addCases_left] at hp
  simp at hp

/-- Jobs of a degree-one item: at most one per OR of T. -/
theorem tr_jobs1_card_below (I : Fin N → Fin N → Prop) {D : Dag N} (hwf : D.WF)
    (hc : Below I D.fn) (hd : D.deg D.out ≤ 2) :
    ((tr_jobs D).filter (fun j => D.deg j.1 ≤ 1)).card ≤ D.Tor.card := by
  classical
  have key : ∀ j ∈ (tr_jobs D).filter (fun j => D.deg j.1 ≤ 1),
      j.2.1 = j.1 ∧ ∃ h ∈ D.Tor, D.Kid h j.1 := by
    intro j hj
    obtain ⟨b, r, w⟩ := j
    rw [Finset.mem_filter, tr_mem_jobs] at hj
    obtain ⟨⟨hb, hr, hm⟩, h1⟩ := hj
    have hrb : r = b := by
      rcases hr with ⟨-, rfl⟩ | ⟨hmix, -⟩
      · rfl
      · have := (Finset.mem_filter.1 (Finset.mem_filter.1 hmix).1).2; dsimp only at h1; omega
    subst hrb
    refine ⟨rfl, tr_item_parent hb.1 ?_ h1⟩
    rintro rfl
    exact tr_no_const_below I hwf hc hd hb h1 hm (fun x => by
      unfold Dag.ctx; exact decide_eq_true Dag.Top.root)
  let f : ℕ × ℕ × Fin N → ℕ := fun j =>
    if h : ∃ h ∈ D.Tor, D.Kid h j.1 then h.choose else 0
  apply Finset.card_le_card_of_injOn f
  · intro j hj
    have hx := (key j hj).2
    simp only [f, dif_pos hx]
    exact hx.choose_spec.1
  · intro j hj j' hj' he
    have hx := (key j hj).2
    have hx' := (key j' hj').2
    simp only [f, dif_pos hx, dif_pos hx'] at he
    have hk := hx.choose_spec.2
    rw [he] at hk
    have h1 := (Finset.mem_filter.1 hj).2
    have h1' := (Finset.mem_filter.1 hj').2
    have hbb := tr_tor_low_unique hwf hx'.choose_spec.1 hk hx'.choose_spec.2 h1 h1'
    obtain ⟨b, r, w⟩ := j
    obtain ⟨b', r', w'⟩ := j'
    have hm := ((tr_mem_jobs.1 (Finset.mem_filter.1 hj).1)).2.2
    have hm' := ((tr_mem_jobs.1 (Finset.mem_filter.1 hj').1)).2.2
    have e1 := (key _ hj).1
    have e2 := (key _ hj').1
    dsimp only at hbb e1 e2 hm hm'
    subst e1 e2 hbb
    rw [tr_marker_line hm hm']

theorem tr_term_ok_below (I : Fin N → Fin N → Prop) {D D' : Dag N} (hwf : D.WF)
    (hc : Below I D.fn) (hd : D.deg D.out ≤ 2) (hpre : D.gates <+: D'.gates)
    (hit : ∀ b, D.IsItem b → (∀ x, D.ctx b x = true) ∨
      ∃ i, D'.deg i = 0 ∧ (∀ x, D'.val x i = D.ctx b x) ∧
        D'.coneOf {i} ⊆ D.X ∪ Finset.Ico (N + N + D.size) (N + N + D'.size))
    {gs : List G} (hB : tr_Base D D' gs) {b r : ℕ} {w : Fin N}
    (hj : (b, r, w) ∈ tr_jobs D) :
    tr_Base D D' (tr_term D D' gs b r).1 ∧ gs <+: (tr_term D D' gs b r).1 ∧
      (tr_term D D' gs b r).1.length + 1 ≤ gs.length + tr_cost D (b, r, w) ∧
      (∀ v, (tr_term D D' gs b r).2 = some v →
        tr_Good4 D D' (tr_term D D' gs b r).1.length v ∧ tr_Snd I D (tr_term D D' gs b r).1 w v) ∧
      (∀ p, tr_Cond D (b, r, w) p → ∃ v, (tr_term D D' gs b r).2 = some v ∧
        (⟨(tr_term D D' gs b r).1, D.out⟩ : Dag N).val (ep p w) v = true) := by
  classical
  obtain ⟨hb, hr, hm⟩ := tr_mem_jobs.1 hj
  have hsz : D'.size ≤ gs.length := hB.1.length_le
  have hxo : ∀ p, ∀ q : Fin N, pt p (Fin.castAdd N q) = ep p w (Fin.castAdd N q) :=
    fun p q => tr_pt_ep p w q
  by_cases h1 : D.deg b ≤ 1
  · have hrb : r = b := by
      rcases hr with ⟨-, rfl⟩ | ⟨hmix, -⟩
      · rfl
      · have := (Finset.mem_filter.1 (Finset.mem_filter.1 hmix).1).2; omega
    subst hrb
    have e : tr_term D D' gs r r = (gs, tr_psi D D' r) := by
      unfold tr_term; rw [if_pos h1]
    have hcost : tr_cost D (r, r, w) = 1 := by unfold tr_cost; rw [if_pos h1]
    rw [e, hcost]
    refine ⟨hB, List.prefix_refl _, le_rfl, fun v hv => ?_, fun p hp => ?_⟩
    · have hold := tr_old_psi hv
      obtain ⟨hlt, -, hval, -⟩ := tr_psi_some hv
      refine ⟨Or.inl hold, fun z hz hvz => ?_⟩
      rw [tr_val_old hB hlt, hval] at hvz
      exact tr_term_sound_below I hwf hc hd hb hm z hz hvz (fun x hx hxr => by
        rcases hx with ⟨-, rfl⟩ | ⟨hmix, -⟩
        · exact absurd rfl hxr
        · have := (Finset.mem_filter.1 (Finset.mem_filter.1 hmix).1).2; omega)
    · cases hps : tr_psi D D' r with
      | none =>
        rcases tr_psi_none hit hb hps with hall | hall
        · exact absurd hall (tr_no_const_below I hwf hc hd hb h1 hm)
        · have := hp.1; rw [hall] at this; cases this
      | some v =>
        obtain ⟨hlt, -, hval, -⟩ := tr_psi_some hps
        refine ⟨v, rfl, ?_⟩
        rw [tr_val_old hB hlt, hval, ← tr_ctx_xonly (hxo p)]
        exact hp.1
  · have hbm : b ∈ D.Tmix := by
      rcases hb.2 with h | h
      · exact absurd h h1
      · exact h
    have hkr : D.Kid b r := by
      rcases hr with ⟨h, -⟩ | ⟨-, h⟩
      · exact absurd h h1
      · exact h
    obtain ⟨hko, hdo, hfo⟩ := tr_other_spec hwf hbm hkr
    have hbc : b ∈ D.cone := (Finset.mem_filter.1 (Finset.mem_filter.1 hbm).1).1
    have hoo : tr_Old D D' (tr_other D b r) := tr_old_kid hpre hbc hko (by omega)
    have hol := hoo.1
    have hoD : (tr_other D b r) < N + N + D.gates.length := by
      have := Finset.mem_Ico.1 (Api.coneOf_sub D {D.out} hbc)
      obtain ⟨_, _, _, hlt⟩ := hko
      unfold Dag.size at this; omega
    have hvo : ∀ (gs' : List G), tr_Base D D' gs' → ∀ x,
        (⟨gs', D.out⟩ : Dag N).val x (tr_other D b r) = D.val x (tr_other D b r) := by
      intro gs' hB' x
      rw [tr_val_old hB' hol]
      exact tr_val_prefix hpre D.out D'.out x _ hoD
    have hrest : ∀ z, D.val z (tr_other D b r) = true →
        ∀ x, D.IsFactor b x → x ≠ r → D.val z x = true := by
      intro z hz x hx hxr
      rw [hfo x hx hxr]; exact hz
    have hcost : tr_cost D (b, r, w) = 2 := by unfold tr_cost; dsimp only; rw [if_neg h1]
    rw [hcost]
    cases hps : tr_psi D D' b with
    | some i =>
      have e : tr_term D D' gs b r =
          (gs ++ [.and i (tr_other D b r)], some (N + N + gs.length)) := by
        unfold tr_term; rw [if_neg h1, hps]
      rw [e]
      obtain ⟨hlt, hi0, hval, -⟩ := tr_psi_some hps
      have hold := tr_old_psi hps
      have hB' := tr_Base_append hB (g := .and i (tr_other D b r)) (Or.inl ⟨_, _, rfl, hold, hi0, hoo⟩)
      have hgate := tr_gateAt_last (N := N) gs (.and i (tr_other D b r)) D.out
      have hv : ∀ z, (⟨gs ++ [.and i (tr_other D b r)], D.out⟩ : Dag N).val z (N + N + gs.length) =
          (D.ctx b z && D.val z (tr_other D b r)) := by
        intro z
        rw [tr_val_and hgate (by omega) (by omega), tr_val_old hB' hlt, hval, hvo _ hB']
      refine ⟨hB', List.prefix_append _ _, by simp, fun v hv' => ?_, fun p hp => ?_⟩
      · cases hv'
        refine ⟨Or.inr ⟨by omega, by simp⟩, fun z hz hvz => ?_⟩
        rw [hv, Bool.and_eq_true] at hvz
        exact tr_term_sound_below I hwf hc hd hb hm z hz hvz.1 (hrest z hvz.2)
      · refine ⟨_, rfl, ?_⟩
        rw [hv, Bool.and_eq_true, ← tr_ctx_xonly (hxo p)]
        exact ⟨hp.1, hp.2 _ (Or.inr ⟨hbm, hko⟩)⟩
    | none =>
      by_cases hall : ∀ x, D.ctx b x = true
      · have e : tr_term D D' gs b r = (gs, some (tr_other D b r)) := by
          unfold tr_term; rw [if_neg h1, hps]; dsimp only; rw [if_pos hall]
        rw [e]
        refine ⟨hB, List.prefix_refl _, by dsimp only; omega, fun v hv' => ?_, fun p hp => ?_⟩
        · cases hv'
          refine ⟨Or.inl hoo, fun z hz hvz => ?_⟩
          rw [hvo _ hB] at hvz
          exact tr_term_sound_below I hwf hc hd hb hm z hz (hall z) (hrest z hvz)
        · refine ⟨_, rfl, ?_⟩
          rw [hvo _ hB]
          exact hp.2 _ (Or.inr ⟨hbm, hko⟩)
      · have e : tr_term D D' gs b r = (gs, none) := by
          unfold tr_term; rw [if_neg h1, hps]; dsimp only; rw [if_neg hall]
        rw [e]
        refine ⟨hB, List.prefix_refl _, by dsimp only; omega,
          fun v hv' => absurd hv' (by simp), fun p hp => ?_⟩
        rcases tr_psi_none hit hb hps with h2 | h2
        · exact absurd h2 hall
        · have := hp.1; rw [h2] at this; cases this

theorem tr_job_ok_below (I : Fin N → Fin N → Prop) {D D' : Dag N} (hwf : D.WF)
    (hc : Below I D.fn) (hd : D.deg D.out ≤ 2) (hpre : D.gates <+: D'.gates)
    (hit : ∀ b, D.IsItem b → (∀ x, D.ctx b x = true) ∨
      ∃ i, D'.deg i = 0 ∧ (∀ x, D'.val x i = D.ctx b x) ∧
        D'.coneOf {i} ⊆ D.X ∪ Finset.Ico (N + N + D.size) (N + N + D'.size))
    {st : List G × (Fin N → Option ℕ)} {Pl : List (ℕ × ℕ × Fin N)}
    (hI : tr_Inv4 I D D' st Pl) {j : ℕ × ℕ × Fin N} (hj : j ∈ tr_jobs D) :
    tr_Inv4 I D D' (tr_job D D' st j) (Pl ++ [j]) := by
  obtain ⟨gs, ρ⟩ := st
  obtain ⟨b, r, w⟩ := j
  obtain ⟨hB, hlen, hρ, hcov⟩ := hI
  dsimp only at hB hlen hρ hcov
  obtain ⟨hB1, hp1, hl1, ht1, hc1⟩ := tr_term_ok_below I hwf hc hd hpre hit hB hj
  unfold tr_job
  dsimp only
  generalize tr_term D D' gs b r = t at hB1 hp1 hl1 ht1 hc1 ⊢
  obtain ⟨gs1, t⟩ := t
  dsimp only at hB1 hp1 hl1 ht1 hc1 ⊢
  have hρ1 : ∀ w u, ρ w = some u → tr_Good4 D D' gs1.length u ∧ tr_Snd I D gs1 w u :=
    fun w u h => tr_lift hB hp1 (hρ w u h)
  obtain ⟨hB2, hp2, hl2, hρ2, hmono, hnew⟩ := tr_put_ok hB1 hρ1 ht1
  generalize tr_put N gs1 ρ w t = st2 at hB2 hp2 hl2 hρ2 hmono hnew ⊢
  obtain ⟨gs2, ρ2⟩ := st2
  dsimp only at hB2 hp2 hl2 hρ2 hmono hnew ⊢
  refine ⟨hB2, ?_, hρ2, ?_⟩
  · rw [List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  · intro j hj p hp
    rcases List.mem_append.1 hj with hj | hj
    · obtain ⟨u, hu, hv⟩ := hcov j hj p hp
      exact hmono _ u _ hu (by rw [tr_val_lift hB hp1 (hρ _ u hu).1]; exact hv)
    · simp only [List.mem_singleton] at hj
      subst hj
      obtain ⟨v, hv, hvv⟩ := hc1 p hp
      exact hnew v _ hv hvv

theorem tr_fold4_below (I : Fin N → Fin N → Prop) {D D' : Dag N} (hwf : D.WF)
    (hc : Below I D.fn) (hd : D.deg D.out ≤ 2) (hpre : D.gates <+: D'.gates)
    (hit : ∀ b, D.IsItem b → (∀ x, D.ctx b x = true) ∨
      ∃ i, D'.deg i = 0 ∧ (∀ x, D'.val x i = D.ctx b x) ∧
        D'.coneOf {i} ⊆ D.X ∪ Finset.Ico (N + N + D.size) (N + N + D'.size)) :
    ∀ (L : List (ℕ × ℕ × Fin N)) st Pl, (∀ j ∈ L, j ∈ tr_jobs D) → tr_Inv4 I D D' st Pl →
      tr_Inv4 I D D' (L.foldl (tr_job D D') st) (Pl ++ L) := by
  intro L
  induction L with
  | nil => intro st Pl _ hI; simpa using hI
  | cons j t ih =>
    intro st Pl hL hI
    rw [List.foldl_cons, show Pl ++ j :: t = (Pl ++ [j]) ++ t by simp]
    exact ih _ _ (fun j' h => hL j' (List.mem_cons_of_mem _ h))
      (tr_job_ok_below I hwf hc hd hpre hit hI (hL j (by simp)))

/-- D2-16 (constant 48 version). The form built from the marker terms: sound, covers the marker
edges, of size at most `|M| + |X| + 4 |T|`. -/
theorem card16_form_below (I : Fin N → Fin N → Prop) (D : Dag N) (hwf : D.WF)
    (hc : Below I D.fn) (hd : D.deg D.out ≤ 2) :
    ∃ (F : Dag N) (W : Finset (Fin N)) (R : Fin N → ℕ), Dag.SoundPartialForm I F W R ∧
      D.markerEdges I ⊆ F.countedEdges W R ∧
      (F.rootCone W R).card ≤ D.M.card + D.X.card + 4 * D.T.card := by
  classical
  obtain ⟨D', hpre, hwf', hsz', hit⟩ := card15c_contexts D hwf hd
  have hinit : tr_Inv4 I D D' (D'.gates, fun _ => none) [] := by
    refine ⟨⟨List.prefix_refl _, fun j g hj hg => ?_⟩, by simp [Dag.size], ?_, ?_⟩
    rotate_left
    · intro w u h; simp at h
    · intro j hj; simp at hj
    have : D'.gates[j]? = none :=
      List.getElem?_eq_none_iff.2 (by unfold Dag.size at hj; omega)
    rw [this] at hg
    cases hg
  have hfin := tr_fold4_below I hwf hc hd hpre hit (tr_jobs D).toList _ []
    (fun j hj => Finset.mem_toList.1 hj) hinit
  rw [List.nil_append] at hfin
  generalize List.foldl (tr_job D D') (D'.gates, fun _ => none) (tr_jobs D).toList = st at hfin
  obtain ⟨hB, hlen, hρ, hcov⟩ := hfin
  have hroot : ∀ w, (st.2 w).isSome → ∃ u, st.2 w = some u := fun w h =>
    Option.isSome_iff_exists.1 h
  refine ⟨⟨st.1, D.out⟩, Finset.univ.filter (fun w => (st.2 w).isSome),
    fun w => (st.2 w).getD 0, ⟨tr_wf4 hwf' hB D.out, ?_, ?_⟩, ?_, ?_⟩
  · intro w hw
    obtain ⟨u, hu⟩ := hroot w (Finset.mem_filter.1 hw).2
    simp only [hu, Option.getD_some]
    exact (tr_good4_final hB D.out u (hρ w u hu).1).1
  · rintro z ⟨w, hw, hz, hv⟩
    obtain ⟨u, hu⟩ := hroot w (Finset.mem_filter.1 hw).2
    simp only [hu, Option.getD_some] at hv
    exact (hρ w u hu).2 z hz hv
  · rintro ⟨p, w⟩ he
    unfold Dag.markerEdges at he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
    obtain ⟨-, b, hb, hctx, hfac, r, hr, hm⟩ := he
    have hj : (b, r, w) ∈ (tr_jobs D).toList :=
      Finset.mem_toList.2 (tr_mem_jobs.2 ⟨hb, hr, hm⟩)
    obtain ⟨u, hu, hv⟩ := hcov _ hj p ⟨hctx, hfac⟩
    unfold Dag.countedEdges
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    dsimp only at hu hv
    refine ⟨by simp [hu], ?_⟩
    simp only [hu, Option.getD_some]
    exact hv
  · have hsz : D'.size ≤ st.1.length := hB.1.length_le
    have hDD : D.size ≤ D'.size := hpre.length_le
    have hsub : (⟨st.1, D.out⟩ : Dag N).rootCone (Finset.univ.filter (fun w => (st.2 w).isSome))
        (fun w => (st.2 w).getD 0) ⊆
        (D.M ∪ D.X) ∪ Finset.Ico (N + N + D.size) (N + N + st.1.length) := by
      intro m hm
      unfold Dag.rootCone Dag.coneOf at hm
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image] at hm
      obtain ⟨-, hm1, r, ⟨w, hw, rfl⟩, hr⟩ := hm
      obtain ⟨u, hu⟩ := hroot w hw.2
      simp only [hu, Option.getD_some] at hr
      have hg : tr_Good4 D D' st.1.length m := by
        clear hm1
        induction hr with
        | refl => exact (hρ w u hu).1
        | tail _ hk ih => exact (tr_good4_final hB D.out _ ih).2 _ hk
      rcases hg with hold | hnew
      · rcases hold.2.2 m Relation.ReflTransGen.refl hm1 with h | h | h
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ h)
        · exact Finset.mem_union_right _ (Finset.mem_Ico.2 ⟨h.1, by omega⟩)
      · exact Finset.mem_union_right _ (Finset.mem_Ico.2 ⟨by omega, hnew.2⟩)
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le (D.M ∪ D.X) (Finset.Ico (N + N + D.size) (N + N + st.1.length))
    have h3 := Finset.card_union_le D.M D.X
    have h4 : (Finset.Ico (N + N + D.size) (N + N + st.1.length)).card =
        st.1.length - D.size := by rw [Nat.card_Ico]; omega
    have hsum : ((tr_jobs D).toList.map (tr_cost D)).sum =
        ((tr_jobs D).filter (fun j => D.deg j.1 ≤ 1)).card +
          2 * ((tr_jobs D).filter (fun j => ¬ D.deg j.1 ≤ 1)).card := by
      rw [Finset.sum_map_toList]
      unfold tr_cost
      rw [Finset.sum_ite]
      simp [Finset.sum_const, smul_eq_mul, mul_comm]
    have hj1 := tr_jobs1_card_below I hwf hc hd
    have hj2 := tr_jobs2_card (D := D)
    have hT := tr_T_split D
    show ((⟨st.1, D.out⟩ : Dag N).rootCone _ _).card ≤ _
    omega

end PEqualNP.MetaComplexity.Deg2
