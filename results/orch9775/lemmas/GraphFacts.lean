import CircuitHarness

namespace PEqualNP.Outside.L_meta_9775.GraphFacts

open CircuitHarness

def graph : SimpleGraph (Fin 14) where
  Adj u v := (u, v) ∈ edges ∨ (v, u) ∈ edges
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by decide⟩

instance : DecidableRel graph.Adj := fun _ _ => inferInstanceAs
  (Decidable (_ ∈ edges ∨ _ ∈ edges))

lemma no_four_cycle : PEqualNP.TopForm.NoFourCycle graph := by decide

lemma edge_card : graph.edgeFinset.card = 19 := by decide

def left (i : Fin 7) : Fin 14 := ⟨i.val, by omega⟩

def right : Fin 7 → Fin 14 := ![8, 7, 13, 11, 10, 12, 9]

lemma matching_edges : ∀ i : Fin 7, graph.Adj (left i) (right i) := by decide

lemma matching_disjoint : ∀ i j : Fin 7, i ≠ j →
    left i ≠ left j ∧ left i ≠ right j ∧ right i ≠ left j ∧ right i ≠ right j := by
  decide

lemma cover_size (T : Finset (Fin 14))
    (hT : ∀ u v, graph.Adj u v → u ∈ T ∨ v ∈ T) : 7 ≤ T.card := by
  let pick : Fin 7 → Fin 14 := fun i => if left i ∈ T then left i else right i
  have hp : Function.Injective pick := by
    intro i j hij
    by_contra hne
    obtain ⟨hll, hlr, hrl, hrr⟩ := matching_disjoint i j hne
    dsimp [pick] at hij
    split_ifs at hij
    · exact hll hij
    · exact hlr hij
    · exact hrl hij
    · exact hrr hij
  have hs : Finset.univ.image pick ⊆ T := by
    intro v hv
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
    dsimp [pick]
    split_ifs with hi
    · exact hi
    · exact (hT _ _ (matching_edges i)).resolve_left hi
  have hc := Finset.card_le_card hs
  simpa only [Finset.card_image_of_injective _ hp, Finset.card_univ,
    Fintype.card_fin] using hc

lemma target_graph (x : Fin 14 → Bool) : target x =
    decide (∃ u v : Fin 14, graph.Adj u v ∧ x u = true ∧ x v = true) := by
  apply Bool.eq_iff_iff.mpr
  rw [Bool.decide_iff, target_spec]
  constructor
  · rintro ⟨u, v, he, hu, hv⟩
    exact ⟨u, v, Or.inl ((edge_iff u v).mpr he), hu, hv⟩
  · rintro ⟨u, v, he, hu, hv⟩
    rcases he with he | he
    · exact ⟨u, v, (edge_iff u v).mp he, hu, hv⟩
    · exact ⟨v, u, (edge_iff v u).mp he, hv, hu⟩

end PEqualNP.Outside.L_meta_9775.GraphFacts
