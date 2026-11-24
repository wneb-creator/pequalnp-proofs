import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1477.SharedFilterEdgeCover

lemma active_edge_cover_bound {V : Type*} [Fintype V] [DecidableEq V]
    (P H : SimpleGraph V) [DecidableRel P.Adj] [DecidableRel H.Adj]
    (hPH : P ≤ H) (S R Q : Finset V)
    (hcover : ∀ v ∈ S, ∃ b, P.Adj v b) (hR : R ⊆ S)
    (hactive : ∀ c ∈ R \ Q, ∃ q ∈ Q, H.Adj c q ∧ ∃ b, P.Adj c b ∧ b ≠ q) :
    S.card + (R \ Q).card ≤ H.edgeFinset.card + P.edgeFinset.card := by
  classical
  let K := S.filter fun v => 2 ≤ P.degree v
  have hdeg : ∀ v ∈ S, 1 ≤ P.degree v := by
    intro v hv
    obtain ⟨b,hb⟩ := hcover v hv
    have hp : 0 < (P.neighborFinset v).card :=
      Finset.card_pos.mpr ⟨b,(P.mem_neighborFinset v b).mpr hb⟩
    rw [P.card_neighborFinset_eq_degree] at hp
    omega
  have hweighted : S.card + K.card ≤ ∑ v ∈ S, P.degree v := by
    have hh := Finset.sum_le_sum (s := S) (f := fun v => 1 + if 2 ≤ P.degree v then 1 else 0)
      (g := fun v => P.degree v) (by
        intro v hv
        have hd := hdeg v hv
        split_ifs <;> omega)
    simpa [Finset.sum_add_distrib,K] using hh
  have hsum : (∑ v ∈ S, P.degree v) ≤ 2 * P.edgeFinset.card := by
    rw [← P.sum_degrees_eq_twice_card_edges]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (by intros; omega)
  have hK : S.card + K.card ≤ 2 * P.edgeFinset.card := hweighted.trans hsum
  let L := (R \ Q).filter fun c => P.degree c ≤ 1
  have hpart : (R \ Q).card ≤ L.card + K.card := by
    apply (Finset.card_le_card (show R \ Q ⊆ L ∪ K from ?_)).trans (Finset.card_union_le _ _)
    intro c hc
    by_cases hd : P.degree c ≤ 1
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hc,hd⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨hR (Finset.mem_sdiff.mp hc).1,by omega⟩)
  have hex : ∀ c : L, ∃ q ∈ Q, H.Adj c.val q ∧ ∃ b, P.Adj c.val b ∧ b ≠ q :=
    fun c => hactive c.val (Finset.mem_filter.mp c.property).1
  choose q hq hH b hb hneq using hex
  let f : L → Sym2 V := fun c => s(c.val,q c)
  have hf : ∀ c : L, f c ∈ H.edgeFinset \ P.edgeFinset := by
    intro c
    apply Finset.mem_sdiff.mpr
    constructor
    · exact SimpleGraph.mem_edgeFinset.mpr (H.mem_edgeSet.mpr (hH c))
    · intro he
      have hp : P.Adj c.val (q c) := P.mem_edgeSet.mp (SimpleGraph.mem_edgeFinset.mp he)
      have hd : (P.neighborFinset c.val).card ≤ 1 := (Finset.mem_filter.mp c.property).2
      have heq := Finset.card_le_one.mp hd (b c) ((P.mem_neighborFinset _ _).mpr (hb c))
        (q c) ((P.mem_neighborFinset _ _).mpr hp)
      exact hneq c heq
  have hinj : Function.Injective f := by
    intro c d he
    rcases Sym2.eq_iff.mp he with ⟨hcd,_⟩ | ⟨hcq,_⟩
    · exact Subtype.ext hcd
    · have hn := (Finset.mem_sdiff.mp (Finset.mem_filter.mp c.property).1).2
      exact (hn (hcq.symm ▸ hq d)).elim
  have hL : L.card ≤ (H.edgeFinset \ P.edgeFinset).card := by
    have hh : Fintype.card L ≤ (H.edgeFinset \ P.edgeFinset).card :=
      Finset.card_le_card_of_injOn f (fun c _ => hf c) (fun c _ d _ he => hinj he)
    simpa only [Fintype.card_coe] using hh
  have hdiff := Finset.card_sdiff_add_card_eq_card (SimpleGraph.edgeFinset_mono hPH)
  omega

lemma active_edge_cover_bound_with_roots {V : Type*} [Fintype V] [DecidableEq V]
    (P H : SimpleGraph V) [DecidableRel P.Adj] [DecidableRel H.Adj]
    (hPH : P ≤ H) (S R Q : Finset V)
    (hcover : ∀ v ∈ S, ∃ b, P.Adj v b) (hR : R ⊆ S)
    (hactive : ∀ c ∈ R \ Q, ∃ q ∈ Q, H.Adj c q ∧ ∃ b, P.Adj c b ∧ b ≠ q) :
    S.card + R.card ≤ H.edgeFinset.card + P.edgeFinset.card + Q.card := by
  have hh := active_edge_cover_bound P H hPH S R Q hcover hR hactive
  have hp := Finset.card_sdiff_add_card_inter R Q
  have hq : (R ∩ Q).card ≤ Q.card := Finset.card_le_card Finset.inter_subset_right
  omega

end PEqualNP.Outside.L_meta_1477.SharedFilterEdgeCover
