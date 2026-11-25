import ActualOneNotBridge
import ComputationalLiveBound
import PEqualNP.Outside.L_meta_10760

namespace PEqualNP.Outside.L_meta_10760_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma target_eq_f : ∀ x : Fin 7 → Bool, L_meta_10760.target x = f x := by
  decide +kernel

lemma close_from_checker (Q : List (ℕ × ℕ))
    (hp : pOk 0 Q = true) (hQ : ∀ e ∈ Q, Imp [] e.1 e.2)
    (hcheck : chk [] Q 0 13 1 FF 1 = false)
    (gates : List Gate) (o : ℕ)
    (hb : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hu : ∀ i j : Fin gates.length, (gates.get i).op = GateOp.not →
      (gates.get j).op = GateOp.not → i = j)
    (hf : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = L_meta_10760.target x) :
    ∃ (gates' : List Gate) (o' : ℕ),
      (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧
      ∀ x : Fin 7 → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = L_meta_10760.target x := by
  classical
  by_cases he : ∃ g ∈ gates, g.op = GateOp.not
  · have hD : FanInTwo ⟨gates, o⟩ := by
      intro g hg
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hb g hg
    have hff : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = f x :=
      fun x => (hf x).trans (target_eq_f x)
    have hlen : 14 ≤ gates.length := by
      by_contra hn
      obtain ⟨S, hS, hl⟩ := circuit_live_one_small gates o hD hff hu he (by omega)
      apply live_chk_false (E := []) (Q := Q) (Z := 0) (L := 14)
        (Or.inl rfl) hp (by omega) hQ (by omega) hS hl root13 ffull
      intro p hp'
      simp only [List.mem_singleton] at hp'
      subst p
      exact hcheck
    exact ⟨L_meta_10760.witnessGates, 20, L_meta_10760.witness_basis,
      by simpa only [L_meta_10760.witness_size] using hlen, L_meta_10760.witness_eval⟩
  · refine ⟨gates, o, ?_, le_rfl, hf⟩
    intro g hg
    obtain ⟨hops, hlen⟩ := hb g hg
    refine ⟨?_, hlen⟩
    rcases hops with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (he ⟨g, hg, h⟩).elim

end PEqualNP.Outside.L_meta_10760_aux
