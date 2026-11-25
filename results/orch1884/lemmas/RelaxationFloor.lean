import LeastLiftNormalization
import LeastGateFacts
import RelaxationSemantics
import ClosedRelaxOrGeneral
import UniqueReader
import SoleAndRestriction

namespace PEqualNP.Outside.L_meta_1884.RelaxationFloor

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.LiftFix
open StrongRelaxRows

theorem fourteen (D : Circuit) (hM : Monotone2 D)
    (hp : ∀ m ∈ positives, circuitFun 9 D (row m) = true)
    (hn : ∀ m ∈ negatives, circuitFun 9 D (row m) = false) : 14 ≤ D.size := by
  by_contra hsmall
  have hs : D.size ≤ 13 := by omega
  obtain ⟨E, hAO, hsize, hfun, hmin, T, hA, hB, hC⟩ :=
    LeastLiftNormalization.normalize 9 D hM (RelaxedFacts.nonconstant D hp hn)
  have hm : Monotone2 E := mono_of_AO2 9 E hAO
  have hEs : E.size ≤ 13 := Nat.le_trans hsize hs
  have hpE : ∀ m ∈ positives, circuitFun 9 E (row m) = true := by
    intro m hmem
    rw [hfun]
    exact hp m hmem
  have hnE : ∀ m ∈ negatives, circuitFun 9 E (row m) = false := by
    intro m hmem
    rw [hfun]
    exact hn m hmem
  have hcofactor : ∀ x : Fin 9 → Bool, x 2 = false → circuitFun 9 E x = target x :=
    exact_cofactor (circuitFun 9 E) (ClosedOrSafety.output_mono 9 E hm) hpE hnE 2 (Or.inl rfl)
  have hcount := RestrictionEight.cofactor_reader_floor E hm hcofactor
  have honereader : E.gates.countP (ElimManyCount.reads RestrictionEight.deleted) ≤ 1 := by omega
  obtain ⟨pre, g, post, hd, hread, hpre, hpost⟩ :=
    UniqueReader.raw_two_split E honereader (RelaxedFacts.some_reader_two E hm hpE hnE)
  have hg : E.gates[pre.length]? = some g := by simp [hd]
  have hmem : g ∈ E.gates := List.mem_of_getElem? hg
  have hlen := hAO.2.2 g hmem
  have hpair : ∃ a, g.inputs = [2, a] ∨ g.inputs = [a, 2] := by
    obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
    rw [hab] at hread
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hread
    rcases hread with rfl | rfl
    · exact ⟨b, Or.inl hab⟩
    · exact ⟨a, Or.inr hab⟩
  obtain ⟨a, hin⟩ := hpair
  have hat : a ≠ 2 := by
    intro heq
    apply RelaxedFacts.no_repeated_operand 9 E hm hAO.2.1 hmin pre.length 2 g hg
    rcases hin with hin | hin <;> simpa [heq] using hin
  rcases hAO.1 g hmem with hop | hop
  · have hout := LeastGateFacts.output_not_and_reader E hAO.2.1 pre.length g hg hop hread hcofactor
    have hreader := LeastGateFacts.post_reader 9 E pre post g hd hAO hmin hout
    have hDeq : E = ⟨pre ++ g :: post, E.output⟩ := by cases E; simp_all
    have hgate : g = ⟨GateOp.and, [2, a]⟩ ∨ g = ⟨GateOp.and, [a, 2]⟩ := by
      rcases hin with hin | hin
      · left
        cases g with
        | mk op ins =>
          change op = GateOp.and at hop
          change ins = [2, a] at hin
          cases hop
          cases hin
          rfl
      · right
        cases g with
        | mk op ins =>
          change op = GateOp.and at hop
          change ins = [a, 2] at hin
          cases hop
          cases hin
          rfl
    have hcorrect : ∀ y : Fin 8 → Bool,
        Circuit.eval ⟨pre ++ g :: post, E.output⟩ (RestrictionEight.seed y) = EightExtension.eight y := by
      intro y
      rw [← hDeq, RestrictionEight.seed_eq]
      exact (hcofactor (RestrictionEight.embed y) (by rfl)).trans (RestrictionEight.target_eq y)
    have hfloor := SoleAndRestriction.and_reader_floor pre post g a E.output hgate
      (by simpa only [← hDeq] using hm) hreader hcorrect
    rw [← hDeq] at hfloor
    omega
  · apply ClosedRelaxOrGeneral.sole_or_impossible E pre post 2 a g T (Or.inl rfl) hd hop hin hat
      hpre hpost (RelaxedFacts.output_not_two E hpE) hm hAO.2.1 hmin hA hB hC
    · exact hcofactor
    · exact positive_rows (circuitFun 9 E) (ClosedOrSafety.output_mono 9 E hm) hpE
    · exact RelaxationSemantics.exceptional_accepted E hm hEs hpE hnE
    · exact RelaxedFacts.singleton_rejected E hm hnE 2

end PEqualNP.Outside.L_meta_1884.RelaxationFloor
