
namespace PEqualNP.Outside.L_meta_2448.cross

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

lemma owns_primary_input {n : ℕ} (C : Circuit) (j : ℕ) (a : Fin n)
    (ha : a.val ∈ (gateAt C j).inputs) {u v : Fin n} (ho : Owns n C j u v) :
    u = a ∨ v = a := by
  obtain ⟨hj, hop, hv, _⟩ := ho
  rw [gateAt_eq C j hj] at ha hop
  rw [valf n C (pairInput u v) j hj, hop] at hv
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id] at hv
  have he := hv a.val ha
  rw [wf_keep _ _ a.val (by simp), getD_ofFn] at he
  have ha' : a = u ∨ a = v := of_decide_eq_true he
  exact ha'.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)

lemma star_of_primary_operands {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
    (ha : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∃ a : Fin n, a.val ∈ (gateAt C j).inputs) :
    HasStarProfile n G C := by
  intro j hj hop
  obtain ⟨a, hmem⟩ := ha j hj hop
  right
  refine ⟨a, ?_⟩
  intro u v _ ho
  exact owns_primary_input C j a hmem ho

end PEqualNP.Outside.L_meta_2448.cross
