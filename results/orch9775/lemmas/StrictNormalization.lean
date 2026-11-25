import EdgeReadDeficit
import PEqualNP.MetaComplexity.Helpers.LocClean

namespace PEqualNP.Outside.L_meta_9775.StrictNormalization

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers PEqualNP.MetaComplexity.NestedCover
open PEqualNP.MetaComplexity.Loc CircuitHarness

lemma mono_size (n : Nat) (C : Circuit) (hm : Monotone2 C) :
    HasMonoSize n (circuitFun n C) C.size := by
  refine ⟨C, ?_, ?_, le_rfl, fun _ => rfl⟩
  · intro g hg
    have hop : g.op = GateOp.and ∨ g.op = GateOp.or := by simpa using (hm g hg).1
    refine ⟨?_, (hm g hg).2⟩
    rcases hop with h | h <;> simp [h]
  · intro g hg hnot
    have hop : g.op = GateOp.and ∨ g.op = GateOp.or := by simpa using (hm g hg).1
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
  · intro k hk i hi
    have hget : gs[k]? = some gs[k] := List.getElem?_eq_getElem hk
    obtain ⟨_, a, b, ha, hb, hins⟩ := clean_gate n gs hc hn k gs[k] hget
    change i ∈ (gs.getD k ⟨GateOp.or, []⟩).inputs at hi
    simp only [List.getD_eq_getElem?_getD, hget, Option.getD_some, hins,
      List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> assumption
  · intro g hg
    obtain ⟨k, hk, hkg⟩ := List.getElem_of_mem hg
    obtain ⟨_, a, b, _, _, hins⟩ := clean_gate n gs hc hn k g
      (List.getElem?_eq_some_iff.mpr ⟨hk, hkg⟩)
    simp [hins]

theorem normalize (C : Circuit) (hm : Monotone2 C)
    (hc : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = target x) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 14 D ∧ D.size ≤ C.size ∧
      ∀ x : Fin 14 → Bool, D.eval (List.ofFn x) = target x := by
  have hn : ∃ x y : Fin 14 → Bool, target x ≠ target y := by
    exact ⟨fun _ => false, fun _ => true, by decide⟩
  have hf : circuitFun 14 C = target := funext hc
  have hhas := mono_size 14 C hm
  rw [hf] at hhas
  obtain ⟨gs, o, hclean, hnot, hsize, heval⟩ := Clean.mclean_of 14 target C.size hn hhas
  exact ⟨⟨gs, o⟩, clean_ao 14 gs o hclean hnot, hsize, heval⟩

theorem normalized_deficient_edge (C : Circuit) (hm : Monotone2 C)
    (hc : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = target x)
    (hs : C.size ≤ 24) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 14 D ∧ D.size ≤ C.size ∧
      (∀ x : Fin 14 → Bool, D.eval (List.ofFn x) = target x) ∧
      ∃ u v : Fin 14, (u, v) ∈ edges ∧
        PEqualNP.ReadK.readsAtMost D 14 [u.val, v.val] 1 = false := by
  obtain ⟨D, hAO, hsize, heval⟩ := normalize C hm hc
  exact ⟨D, hAO, hsize, heval,
    EdgeReadDeficit.deficient_edge D hAO heval (hsize.trans hs)⟩

end PEqualNP.Outside.L_meta_9775.StrictNormalization
