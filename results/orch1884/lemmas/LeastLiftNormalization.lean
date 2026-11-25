import PEqualNP.MetaComplexity.Helpers.LocClean
import PEqualNP.MetaComplexity.Helpers.NormalFormLift

namespace PEqualNP.Outside.L_meta_1884.LeastLiftNormalization

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.MetaComplexity.LiftFix
open PEqualNP.MetaComplexity.Loc

lemma mono_size (n : Nat) (D : Circuit) (hM : Monotone2 D) :
    HasMonoSize n (circuitFun n D) D.size := by
  refine ⟨D, ?_, ?_, le_rfl, fun x => rfl⟩
  · intro g hg
    have hop : g.op = GateOp.and ∨ g.op = GateOp.or := by simpa using (hM g hg).1
    refine ⟨?_, (hM g hg).2⟩
    rcases hop with h | h <;> simp [h]
  · intro g hg hnot
    have hop : g.op = GateOp.and ∨ g.op = GateOp.or := by simpa using (hM g hg).1
    rcases hop with h | h <;> rw [hnot] at h <;> cases h

lemma clean_gate (n : Nat) (gs : List Gate) (hc : CleanL n gs) (hn : NotFree gs)
    (k : Nat) (g : Gate) (hg : gs[k]? = some g) :
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      ∃ a b, a < n + k ∧ b < n + k ∧ g.inputs = [a, b] := by
  rcases hc k g hg with ⟨hop, _⟩ | h
  · exact False.elim (hn g (List.mem_of_getElem? hg) hop)
  · exact h

lemma clean_ao (n : Nat) (gs : List Gate) (o : Nat) (hc : CleanL n gs)
    (hn : NotFree gs) : PEqualNP.TopForm.IsAO2 n ⟨gs, o⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨k, hk, hkg⟩ := List.getElem_of_mem hg
    exact (clean_gate n gs hc hn k g (List.getElem?_eq_some_iff.mpr ⟨hk, hkg⟩)).1
  · apply readsBack_of_get
    intro k g hg i hi
    obtain ⟨_, a, b, ha, hb, hins⟩ := clean_gate n gs hc hn k g hg
    simp only [hins, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> assumption
  · intro g hg
    obtain ⟨k, hk, hkg⟩ := List.getElem_of_mem hg
    obtain ⟨_, a, b, _, _, hins⟩ := clean_gate n gs hc hn k g
      (List.getElem?_eq_some_iff.mpr ⟨hk, hkg⟩)
    simp [hins]

theorem normalize (n : Nat) (D : Circuit) (hM : Monotone2 D)
    (hnc : ∃ x y : Fin n → Bool, circuitFun n D x ≠ circuitFun n D y) :
    ∃ E : Circuit, PEqualNP.TopForm.IsAO2 n E ∧ E.size ≤ D.size ∧
      circuitFun n E = circuitFun n D ∧
      (∀ F : Circuit, Monotone2 F → circuitFun n F = circuitFun n E → E.size ≤ F.size) ∧
      ∃ T : Finset Nat, PA E T ∧ PB n E T ∧ PC n E T := by
  obtain ⟨gs, o, hleast, hsize⟩ := Clean.ToolLeast_proof n (circuitFun n D) D.size hnc
    (mono_size n D hM)
  let C : Circuit := ⟨gs, o⟩
  have hao : PEqualNP.TopForm.IsAO2 n C := clean_ao n gs o hleast.1 hleast.2.1
  have hfun : circuitFun n C = circuitFun n D := funext hleast.2.2.1
  have hmin : ∀ F : Circuit, Monotone2 F → circuitFun n F = circuitFun n C → C.size ≤ F.size := by
    intro F hF heq
    have hhas : HasMonoSize n (circuitFun n D) F.size := by
      rw [← hfun, ← heq]
      exact mono_size n F hF
    obtain ⟨gs', o', hc', hn', hsz', hf'⟩ := Clean.mclean_of n (circuitFun n D) F.size hnc hhas
    have hm := hleast.2.2.2 gs' o' hc' hn' hf'
    exact Nat.le_trans hm hsz'
  obtain ⟨E, hE, hlen, hfunE, T, hA, hB, hC⟩ :=
    main_AO n (2 * C.gates.length) C ∅ (by simp) hao
      (by intro j hj; simp at hj) (by intro j hj; simp at hj)
  refine ⟨E, hE, ?_, hfunE.trans hfun, ?_, T, hA, hB, hC⟩
  · change E.gates.length ≤ D.size
    rw [hlen]
    exact hsize
  · intro F hF hf
    change E.gates.length ≤ F.size
    rw [hlen]
    exact hmin F hF (hf.trans hfunE)

end PEqualNP.Outside.L_meta_1884.LeastLiftNormalization
