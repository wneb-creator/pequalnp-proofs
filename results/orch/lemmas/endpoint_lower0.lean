import endpoint_restrict

namespace PEqualNP.Outside.L_meta_1886_aux.EndpointLowerZero

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2592_aux.ConstantSweep
open PEqualNP.Outside.L_meta_2592_aux.Stronger
open ConstantSweepMono EndpointRestrict MapRigidity

lemma touched_true (M : Finset ℕ) (g : Gate) (hg : monoGood g) (i : ℕ)
    (hi : i ∈ g.inputs) (hm : i ∈ M) : touched M g = true := by
  have hw : width g.op = 2 := by
    rcases hg.1 with h | h <;> rw [h] <;> decide
  unfold touched
  rw [hw,List.take_of_length_le hg.2]
  exact List.any_eq_true.mpr ⟨i,hi,by simpa using hm⟩

lemma two_mem_length {α : Type} (xs : List α) (a b : α)
    (ha : a ∈ xs) (hb : b ∈ xs) (hne : a ≠ b) : 2 ≤ xs.length := by
  rcases xs with _ | ⟨v, _ | ⟨w,ws⟩⟩
  · simp at ha
  · simp only [List.mem_singleton] at ha hb
    exact False.elim (hne (ha.trans hb.symm))
  · simp

lemma charged_twice (pre suffix : List Gate) (outIdx : ℕ)
    (monoPre : Monotone2 (Circuit.mk pre 0))
    (monoSuffix : Monotone2 (Circuit.mk suffix outIdx))
    (used : ∃ q ∈ suffix, 11 + pre.length ∈ q.inputs)
    (computes : ∀ x : Fin 10 → Bool,
      (Circuit.mk (pre ++ ⟨.not,[0]⟩ :: suffix) outIdx).eval (EndpointOrder.initial x) = edge10 x) :
    2 ≤ (pre.filter (touched marks)).length +
      (suffix.filter (touched (insert (11 + pre.length) marks))).length := by
  have hp := monoGood_of_mono pre 0 monoPre
  have hs := monoGood_of_mono suffix outIdx monoSuffix
  obtain ⟨q,hq,hqz⟩ := used
  have qm : q ∈ suffix.filter (touched (insert (11 + pre.length) marks)) := by
    exact List.mem_filter.mpr ⟨hq,touched_true _ q (hs q hq) _ hqz (by simp)⟩
  have suffixOne : 1 ≤ (suffix.filter (touched (insert (11 + pre.length) marks))).length :=
    List.length_pos_iff.mpr (List.ne_nil_of_mem qm)
  have split := EndpointOrder.consumer_distinct 0 pre suffix outIdx
    (fun g hg => (hp g hg).1) (fun g hg => (hs g hg).1) computes
  rcases split with ⟨g,hg,hg0⟩ | ⟨g,hg,hg0,hgz⟩
  · have gm : g ∈ pre.filter (touched marks) :=
      List.mem_filter.mpr ⟨hg,touched_true _ g (hp g hg) 0 hg0 (by decide +kernel)⟩
    have preOne : 1 ≤ (pre.filter (touched marks)).length :=
      List.length_pos_iff.mpr (List.ne_nil_of_mem gm)
    omega
  · have gm : g ∈ suffix.filter (touched (insert (11 + pre.length) marks)) :=
      List.mem_filter.mpr ⟨hg,touched_true _ g (hs g hg) 0 hg0 (by simp [marks])⟩
    have hne : g ≠ q := by
      intro he
      exact hgz (he.symm ▸ hqz)
    have suffixTwo := two_mem_length _ g q gm qm hne
    omega

lemma lower (nineLower : ¬ HasCircuitSize 9 edge 15) (pre suffix : List Gate) (outIdx : ℕ)
    (monoPre : Monotone2 (Circuit.mk pre 0))
    (monoSuffix : Monotone2 (Circuit.mk suffix outIdx))
    (used : ∃ q ∈ suffix, 11 + pre.length ∈ q.inputs)
    (computes : ∀ x : Fin 10 → Bool,
      (Circuit.mk (pre ++ ⟨.not,[0]⟩ :: suffix) outIdx).eval (EndpointOrder.initial x) = edge10 x) :
    19 ≤ (Circuit.mk (pre ++ ⟨.not,[0]⟩ :: suffix) outIdx).size := by
  obtain ⟨D,dm,saved,dc⟩ := EndpointRestrict.restrict pre suffix outIdx monoPre monoSuffix computes
  have charged := charged_twice pre suffix outIdx monoPre monoSuffix used computes
  have bound : 16 ≤ D.size := by
    by_contra small
    have legal : FanInTwo D := fun g hg =>
      monoGood_good (monoGood_of_mono D.gates D.output dm g hg)
    exact nineLower ⟨D,legal,by omega,dc⟩
  omega

end PEqualNP.Outside.L_meta_1886_aux.EndpointLowerZero
