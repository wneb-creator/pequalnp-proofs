import Mathlib.Combinatorics.SimpleGraph.Basic

namespace PEqualNP.Outside.L_meta_1031_aux.StarCover

lemma edge_of_two_centers {α : Type} (G : SimpleGraph α) (p q u v : α)
    (hpq : p ≠ q) (huv : G.Adj u v)
    (hp : u = p ∨ v = p) (hq : u = q ∨ v = q) : G.Adj p q := by
  rcases hp with rfl | rfl
  · have hvq : v = q := hq.resolve_left hpq
    simpa only [hvq] using huv
  · have huq : u = q := hq.resolve_right hpq
    simpa only [huq] using huv.symm

lemma adjacent_double_cover_collapses {α : Type} (G : SimpleGraph α)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (a d c : α) (had : G.Adj a d) (R : α → α → Prop)
    (hedge : ∀ u v, R u v → G.Adj u v)
    (hstar : ∀ u v, R u v → u = c ∨ v = c)
    (hcover : ∀ u v, R u v → u = a ∨ v = a ∨ u = d ∨ v = d) :
    (∀ u v, R u v → u = a ∨ v = a) ∨
      (∀ u v, R u v → u = d ∨ v = d) := by
  classical
  by_cases hca : c = a
  · exact Or.inl (by simpa only [hca] using hstar)
  by_cases hcd : c = d
  · exact Or.inr (by simpa only [hcd] using hstar)
  by_cases halla : ∀ u v, R u v → u = a ∨ v = a
  · exact Or.inl halla
  right
  push_neg at halla
  obtain ⟨u₀, v₀, hr₀, hu₀, hv₀⟩ := halla
  have hd₀ : u₀ = d ∨ v₀ = d := by
    rcases hcover u₀ v₀ hr₀ with h | h | h | h
    · exact (hu₀ h).elim
    · exact (hv₀ h).elim
    · exact Or.inl h
    · exact Or.inr h
  have hcdEdge : G.Adj c d :=
    edge_of_two_centers G c d u₀ v₀ hcd (hedge u₀ v₀ hr₀) (hstar u₀ v₀ hr₀) hd₀
  intro u v hr
  by_contra hn
  have hud : u ≠ d := fun h => hn (Or.inl h)
  have hvd : v ≠ d := fun h => hn (Or.inr h)
  have ha : u = a ∨ v = a := by
    rcases hcover u v hr with h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hud h).elim
    · exact (hvd h).elim
  have hcaEdge : G.Adj c a :=
    edge_of_two_centers G c a u v hca (hedge u v hr) (hstar u v hr) ha
  exact htri a d c had hcdEdge.symm hcaEdge

end PEqualNP.Outside.L_meta_1031_aux.StarCover
