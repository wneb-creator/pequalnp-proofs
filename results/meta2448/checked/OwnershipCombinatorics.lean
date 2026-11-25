import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2448_aux

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

lemma intersecting_edge_family {V : Type} (G : SimpleGraph V) (R : V → V → Prop)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hsub : ∀ a b, R a b → G.Adj a b)
    (hmeet : ∀ a b c d, R a b → R c d → a = c ∨ a = d ∨ b = c ∨ b = d) :
    (∀ a b, ¬ R a b) ∨ ∃ c, ∀ a b, R a b → a = c ∨ b = c := by
  classical
  by_cases hempty : ∀ a b, ¬ R a b
  · exact Or.inl hempty
  right
  push_neg at hempty
  obtain ⟨a, b, hab⟩ := hempty
  by_cases ha : ∀ u v, R u v → u = a ∨ v = a
  · exact ⟨a, ha⟩
  push_neg at ha
  obtain ⟨p, q, hpq, hpa, hqa⟩ := ha
  have hbpq : p = b ∨ q = b := by
    have h := hmeet p q a b hpq hab
    tauto
  have hext : ∃ w, w ≠ a ∧ G.Adj b w ∧
      ∀ u v, R u v → u = b ∨ v = b ∨ u = w ∨ v = w := by
    rcases hbpq with rfl | rfl
    · refine ⟨q, hqa, hsub _ _ hpq, ?_⟩
      intro u v huv
      have h := hmeet u v p q huv hpq
      tauto
    · refine ⟨p, hpa, (hsub _ _ hpq).symm, ?_⟩
      intro u v huv
      have h := hmeet u v p q huv hpq
      tauto
  obtain ⟨w, hwa, hbw, hmeetw⟩ := hext
  refine ⟨b, ?_⟩
  intro u v huv
  by_contra hn
  push_neg at hn
  have huva : u = a ∨ v = a := by
    have h := hmeet u v a b huv hab
    tauto
  have huvw : u = w ∨ v = w := by
    have h := hmeetw u v huv
    tauto
  have hwaAdj : G.Adj w a := by
    rcases huva with h | h
    · subst u
      have hvw : v = w := huvw.resolve_left (Ne.symm hwa)
      simpa [hvw] using (hsub _ _ huv).symm
    · subst v
      have huw : u = w := huvw.resolve_right (Ne.symm hwa)
      simpa [huw] using hsub _ _ huv
  exact htri a b w (hsub _ _ hab) hbw hwaAdj

def OwnedEdgesIntersect (n : Nat) (G : SimpleGraph (Fin n)) (C : Circuit) : Prop :=
  ∀ j u v p q, G.Adj u v → G.Adj p q →
    Owns n C j u v → Owns n C j p q → u = p ∨ u = q ∨ v = p ∨ v = q

lemma star_iff_owned_edges_intersect (n : Nat) (G : SimpleGraph (Fin n)) (C : Circuit)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a) :
    HasStarProfile n G C ↔ OwnedEdgesIntersect n G C := by
  constructor
  · intro hstar j u v p q huv hpq hown hown'
    rcases hstar j hown.1 hown.2.1 with hempty | ⟨c, hc⟩
    · exact (hempty u v huv hown).elim
    have h1 := hc u v huv hown
    have h2 := hc p q hpq hown'
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> aesop
  · intro hmeet j hj hop
    have h := intersecting_edge_family G
      (fun u v => G.Adj u v ∧ Owns n C j u v) htri
      (fun _ _ h => h.1)
      (fun u v p q h1 h2 => hmeet j u v p q h1.1 h2.1 h1.2 h2.2)
    rcases h with hempty | ⟨c, hc⟩
    · left
      intro u v huv hown
      exact hempty u v ⟨huv, hown⟩
    · right
      exact ⟨c, fun u v huv hown => hc u v ⟨huv, hown⟩⟩

lemma nonstar_disjoint_owned_edges (n : Nat) (G : SimpleGraph (Fin n)) (C : Circuit)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hstar : ¬ HasStarProfile n G C) :
    ∃ j u v p q, G.Adj u v ∧ G.Adj p q ∧
      Owns n C j u v ∧ Owns n C j p q ∧
      u ≠ p ∧ u ≠ q ∧ v ≠ p ∧ v ≠ q := by
  classical
  rw [star_iff_owned_edges_intersect n G C htri] at hstar
  unfold OwnedEdgesIntersect at hstar
  push_neg at hstar
  exact hstar

end PEqualNP.Outside.L_meta_2448_aux
