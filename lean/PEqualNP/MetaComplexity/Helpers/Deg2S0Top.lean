import PEqualNP.MetaComplexity.Helpers.Deg2Transp
import PEqualNP.MetaComplexity.Helpers.Deg2Bridge

/-!
# Below the edge function: cleaning and the identity (cards D2-04, D2-15)

The cards of the degree-two chain with "computes the edge function" weakened to "below the edge
function" (`Below`): true only at inputs carrying an incident pair. Conjecture until checked.
-/

namespace PEqualNP.MetaComplexity.Deg2

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

variable {N : ℕ}

/-- `f` is true only at inputs carrying an incident pair: the forward half of `Computes`. -/
def Below {N : ℕ} (I : Fin N → Fin N → Prop) (f : (Fin (N + N) → Bool) → Bool) : Prop :=
  ∀ z, f z = true → ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true

theorem below_of_computes {I : Fin N → Fin N → Prop} {f : (Fin (N + N) → Bool) → Bool}
    (h : Computes I f) : Below I f := fun z hz => (h z).1 hz

/-! ## Rejection of the test inputs gives "below" -/

/-- The input `x` with only the lines of `S` kept. -/
def s0_rst (x : Fin (N + N) → Bool) (S : Finset (Fin N)) : Fin (N + N) → Bool :=
  Fin.addCases (motive := fun _ => Bool) (fun p => x (Fin.castAdd N p))
    (fun l => x (Fin.natAdd N l) && decide (l ∈ S))

theorem s0_rst_mono (x : Fin (N + N) → Bool) {S S' : Finset (Fin N)} (h : S ⊆ S') :
    s0_rst x S ≤ s0_rst x S' := by
  intro k
  refine Fin.addCases (fun p => ?_) (fun l => ?_) k
  · simp [s0_rst]
  · simp only [s0_rst, Fin.addCases_right]
    apply Bridge.ble_of_imp
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact fun hl => ⟨hl.1, h hl.2⟩

theorem s0_val_mono {D : Dag N} {i : ℕ} {x y : Fin (N + N) → Bool} (h : x ≤ y)
    (hx : D.val x i = true) : D.val y i = true := by
  have := Api.api_val_mono D i h
  rw [hx] at this
  revert this
  cases D.val y i <;> decide

/-- A true wire of degree `d` at `x` stays true with at most `d` of the lines of `x` kept. -/
theorem s0_inv (D : Dag N) (hwf : D.WF) (x : Fin (N + N) → Bool) (i : ℕ)
    (hi : D.val x i = true) : ∃ S : Finset (Fin N), S.card ≤ D.deg i ∧
      D.val (s0_rst x S) i = true := by
  classical
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  by_cases h0 : i < N + N
  · have hv : ∀ y : Fin (N + N) → Bool, D.val y i = y ⟨i, h0⟩ := by
      intro y; rw [Dag.val, dif_pos h0]
    rw [hv] at hi
    have hdeg : D.deg i = if N ≤ i then 1 else 0 := by rw [Dag.deg, if_pos h0]
    rw [hdeg]
    by_cases hN : N ≤ i
    · have e : (⟨i, h0⟩ : Fin (N + N)) = Fin.natAdd N ⟨i - N, by omega⟩ := by
        apply Fin.ext; simp only [Fin.val_natAdd]; omega
      refine ⟨{⟨i - N, by omega⟩}, by simp [hN], ?_⟩
      rw [hv]
      rw [e] at hi ⊢
      simp only [s0_rst, Fin.addCases_right, hi, Finset.mem_singleton, decide_true, Bool.and_self]
    · have e : (⟨i, h0⟩ : Fin (N + N)) = Fin.castAdd N ⟨i, by omega⟩ := by
        apply Fin.ext; simp
      refine ⟨∅, by simp, ?_⟩
      rw [hv]
      rw [e] at hi ⊢
      simp only [s0_rst, Fin.addCases_left, hi]
  · cases hg : D.gateAt i with
    | none =>
      exfalso
      have hg' : D.gates[i - (N + N)]? = none := by
        unfold Dag.gateAt at hg; rwa [if_pos (by omega)] at hg
      rw [Dag.val, dif_neg h0, hg'] at hi
      exact Bool.false_ne_true hi
    | some g =>
      cases g with
      | cst v =>
        refine ⟨∅, by simp, ?_⟩
        rw [Dag.val, dif_neg h0, (Api.gateAt_some hg).2] at hi ⊢
        exact hi
      | and a b =>
        have ha := hwf _ _ hg a (by simp [G.kids])
        have hb := hwf _ _ hg b (by simp [G.kids])
        rw [tr_val_and hg ha hb, Bool.and_eq_true] at hi
        obtain ⟨S, hS, hSv⟩ := ih a ha hi.1
        obtain ⟨S', hS', hSv'⟩ := ih b hb hi.2
        refine ⟨S ∪ S', ?_, ?_⟩
        · rw [tr_deg_and hg ha hb]
          exact le_trans (Finset.card_union_le _ _) (by omega)
        · rw [tr_val_and hg ha hb, Bool.and_eq_true]
          exact ⟨s0_val_mono (s0_rst_mono x Finset.subset_union_left) hSv,
            s0_val_mono (s0_rst_mono x Finset.subset_union_right) hSv'⟩
      | or a b =>
        have ha := hwf _ _ hg a (by simp [G.kids])
        have hb := hwf _ _ hg b (by simp [G.kids])
        rw [tr_val_or hg ha hb, Bool.or_eq_true] at hi
        rcases hi with hi | hi
        · obtain ⟨S, hS, hSv⟩ := ih a ha hi
          refine ⟨S, ?_, ?_⟩
          · rw [tr_deg_or hg ha hb]; exact le_trans hS (le_max_left _ _)
          · rw [tr_val_or hg ha hb, hSv, Bool.true_or]
        · obtain ⟨S, hS, hSv⟩ := ih b hb hi
          refine ⟨S, ?_, ?_⟩
          · rw [tr_deg_or hg ha hb]; exact le_trans hS (le_max_right _ _)
          · rw [tr_val_or hg ha hb, hSv, Bool.or_true]

/-- Output degree at most two and false at every test input of at most two lines: below the edge
function. -/
theorem test_below (I : Fin N → Fin N → Prop) (D : Dag N) (hwf : D.WF) (hd : D.deg D.out ≤ 2)
    (htest : ∀ S : Finset (Fin N), S.card ≤ 2 → D.fn (testInput I S) = false) :
    Below I D.fn := by
  classical
  intro z hz
  by_contra hne
  obtain ⟨S, hS, hv⟩ := s0_inv D hwf z D.out hz
  let S' : Finset (Fin N) := S.filter (fun l => z (Fin.natAdd N l) = true)
  have hle : s0_rst z S ≤ testInput I S' := by
    intro k
    refine Fin.addCases (fun p => ?_) (fun l => ?_) k
    · apply Bridge.ble_of_imp
      intro h
      simp only [s0_rst, Fin.addCases_left] at h
      simp only [testInput, inp, Fin.addCases_left, decide_eq_true_eq, Finset.mem_filter,
        Finset.mem_univ, true_and]
      intro l hl hI
      exact hne ⟨p, l, hI, h, (Finset.mem_filter.1 hl).2⟩
    · apply Bridge.ble_of_imp
      intro h
      simp only [s0_rst, Fin.addCases_right, Bool.and_eq_true, decide_eq_true_eq] at h
      simp only [testInput, inp, Fin.addCases_right, decide_eq_true_eq]
      exact Finset.mem_filter.2 ⟨h.2, h.1⟩
  have h1 : D.fn (testInput I S') = true := s0_val_mono hle hv
  rw [htest S' (le_trans (Finset.card_filter_le _ _) (le_trans hS hd))] at h1
  exact Bool.false_ne_true h1

/-- D2-04 for a circuit below the edge function: the cleaned circuit is below too and accepts
every input the circuit accepts. -/
theorem card04_clean_below (I : Fin N → Fin N → Prop) (D : Dag N) (hwf : D.WF)
    (hc : Below I D.fn) (hd : D.deg D.out ≤ 2) :
    ∃ D' : Dag N, D'.WF ∧ D'.size ≤ D.size ∧ Below I D'.fn ∧ D'.deg D'.out ≤ 2 ∧
      D'.Cleaned I D'.cone ∧ ∀ z, D.fn z = true → D'.fn z = true := by
  have hdeg' : (Bridge.clean I D).deg (Bridge.clean I D).out ≤ 2 := by
    rw [Bridge.clean_deg I D hwf]; exact hd
  refine ⟨Bridge.clean I D, Bridge.clean_wf I D hwf, by simp [Bridge.clean, Dag.size], ?_, hdeg',
    Bridge.clean_cleaned I D hwf _, ?_⟩
  · refine test_below I _ (Bridge.clean_wf I D hwf) hdeg' ?_
    intro S hS
    unfold Dag.fn
    show (Bridge.clean I D).val (testInput I S) D.out = false
    rw [Bridge.clean_test I D hwf hS]
    cases ht : D.val (testInput I S) D.out
    · rfl
    · exact absurd (hc _ ht) (Bridge.testInput_noEdge I S)
  · intro z h1
    have := Bridge.clean_mono I D z D.out
    unfold Dag.fn at h1 ⊢
    rw [h1] at this
    change (Bridge.clean I D).val z D.out = true
    revert this
    cases (Bridge.clean I D).val z D.out <;> decide

/-! ## D2-15 -/

/-- A degree-0 child of a reached wire is false whenever the labels on the way are true. -/
theorem tr_drop_below {D : Dag N} {I : Fin N → Fin N → Prop} (hwf : D.WF) (hc : Below I D.fn)
    {x : Fin (N + N) → Bool} {c a : ℕ} (hT : D.Top (fun f => D.val x f = true) c)
    (ha0 : D.deg a = 0) (hva : D.val x a = true)
    (hup : D.val (tr_noLines x) a = true → D.val (tr_noLines x) c = true) : False := by
  have hx := tr_noLines_pts x
  have hT' : D.Top (fun f => D.val (tr_noLines x) f = true) c := by
    refine tr_top_mono ?_ hT
    intro f hf hv
    rw [← Api.api_val_xonly D hf hx]; exact hv
  have hva' : D.val (tr_noLines x) a = true := by
    rw [← Api.api_val_xonly D ha0 hx]; exact hva
  have hout := tr_top_val hwf hT' (hup hva')
  obtain ⟨p, l, -, -, hl⟩ := hc (tr_noLines x) hout
  simp [tr_noLines, Fin.coe_natAdd] at hl

theorem tr_descend_below {D : Dag N} {I : Fin N → Fin N → Prop} (hwf : D.WF) (hc : Below I D.fn)
    (hd : D.deg D.out ≤ 2) (x : Fin (N + N) → Bool) :
    ∀ c, D.Top (fun f => D.val x f = true) c → D.val x c = true →
      ∃ b, D.IsItem b ∧ D.ctx b x = true ∧ ∀ r, D.IsFactor b r → D.val x r = true := by
  classical
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
  intro hT hv
  have hitem : D.Top (fun _ => True) c := tr_top_mono (fun _ _ _ => trivial) hT
  have hctx : D.ctx c x = true := by unfold Dag.ctx; exact decide_eq_true hT
  have hreach := tr_top_reach hT
  have hdc : D.deg c ≤ 2 := le_trans (Api.api_reach_deg D hreach) hd
  by_cases h1 : D.deg c ≤ 1
  · refine ⟨c, ⟨hitem, Or.inl h1⟩, hctx, ?_⟩
    intro r hr
    rcases hr with ⟨-, rfl⟩ | ⟨hm, -⟩
    · exact hv
    · have := (Finset.mem_filter.1 (Finset.mem_filter.1 hm).1).2; omega
  have h2 : D.deg c = 2 := by omega
  obtain ⟨g, hg, hlt⟩ := tr_gate_of_deg (D := D) (c := c) (by omega)
  have hge := (Api.gateAt_some hg).1
  have hcone := tr_mem_cone hge hlt hreach
  have hT2 : c ∈ D.T := Finset.mem_filter.2 ⟨hcone, h2⟩
  cases g with
  | cst v => rw [tr_deg_cst hg] at h2; omega
  | and a b =>
    have ha := hwf _ _ hg a (by simp [G.kids])
    have hb := hwf _ _ hg b (by simp [G.kids])
    have hdeg := tr_deg_and hg ha hb
    rw [tr_val_and hg ha hb, Bool.and_eq_true] at hv
    by_cases hab : D.deg a = 1 ∧ D.deg b = 1
    · have hmix : c ∈ D.Tmix := Finset.mem_filter.2 ⟨hT2, a, b, hg, hab⟩
      refine ⟨c, ⟨hitem, Or.inr hmix⟩, hctx, ?_⟩
      intro r hr
      rcases hr with ⟨h1', -⟩ | ⟨-, g', hg', hrg, -⟩
      · omega
      · rw [hg] at hg'; cases hg'
        simp only [G.kids, List.mem_cons, List.not_mem_nil, or_false] at hrg
        rcases hrg with rfl | rfl
        · exact hv.1
        · exact hv.2
    · have hf : D.deg a = 0 ∨ D.deg b = 0 := by omega
      have hTf : c ∈ D.Tandf := Finset.mem_filter.2 ⟨hT2, a, b, hg, hf⟩
      rcases hf with hf | hf
      · exact ih b hb (Dag.Top.andStep hT hTf (Or.inl hg) hf (by omega) ha hb hv.1) hv.2
      · exact ih a ha (Dag.Top.andStep hT hTf (Or.inr hg) hf (by omega) hb ha hv.2) hv.1
  | or a b =>
    have ha := hwf _ _ hg a (by simp [G.kids])
    have hb := hwf _ _ hg b (by simp [G.kids])
    have hTor : c ∈ D.Tor := Finset.mem_filter.2 ⟨hT2, a, b, hg⟩
    rw [tr_val_or hg ha hb, Bool.or_eq_true] at hv
    rcases hv with hv | hv
    · by_cases h0 : D.deg a = 0
      · exact (tr_drop_below hwf hc hT h0 hv (fun h => by rw [tr_val_or hg ha hb, h]; rfl)).elim
      · exact ih a ha (Dag.Top.orStep hT hTor (tr_kid_of hg (by simp [G.kids]) ha)
          (by omega)) hv
    · by_cases h0 : D.deg b = 0
      · exact (tr_drop_below hwf hc hT h0 hv
          (fun h => by rw [tr_val_or hg ha hb, h]; simp)).elim
      · exact ih b hb (Dag.Top.orStep hT hTor (tr_kid_of hg (by simp [G.kids]) hb)
          (by omega)) hv

/-- D2-15 (i), (ii). The identity: the output is the OR over items of context AND factors. -/
theorem card15_identity_below (I : Fin N → Fin N → Prop) (D : Dag N) (hwf : D.WF)
    (hc : Below I D.fn) (hd : D.deg D.out ≤ 2) (x : Fin (N + N) → Bool) :
    D.fn x = true ↔
      ∃ b, D.IsItem b ∧ D.ctx b x = true ∧ ∀ r, D.IsFactor b r → D.val x r = true := by
  classical
  constructor
  · intro h
    exact tr_descend_below hwf hc hd x D.out Dag.Top.root h
  · rintro ⟨b, ⟨-, hb⟩, hctx, hfac⟩
    have hT : D.Top (fun f => D.val x f = true) b := by
      unfold Dag.ctx at hctx; exact of_decide_eq_true hctx
    apply tr_top_val hwf hT
    rcases hb with hb | hb
    · exact hfac b (Or.inl ⟨hb, rfl⟩)
    · obtain ⟨-, a, a', hg, -, -⟩ := Finset.mem_filter.1 hb
      have ha := hwf _ _ hg a (by simp [G.kids])
      have ha' := hwf _ _ hg a' (by simp [G.kids])
      rw [tr_val_and hg ha ha', hfac a (Or.inr ⟨hb, tr_kid_of hg (by simp [G.kids]) ha⟩),
        hfac a' (Or.inr ⟨hb, tr_kid_of hg (by simp [G.kids]) ha'⟩)]
      rfl

end PEqualNP.MetaComplexity.Deg2
