import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Tactic

namespace PEqualNP.Outside.L_meta_1031

lemma intersecting_edges_star {α : Type*} (G : SimpleGraph α) (r : α → α → Prop)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hedge : ∀ u v, r u v → G.Adj u v)
    (hne : ∃ a b, r a b)
    (hmeet : ∀ u v p q, r u v → r p q → u = p ∨ u = q ∨ v = p ∨ v = q) :
    ∃ c, ∀ u v, r u v → u = c ∨ v = c := by
  classical
  obtain ⟨a, b, hab⟩ := hne
  by_cases ha : ∀ u v, r u v → u = a ∨ v = a
  · exact ⟨a, ha⟩
  · push_neg at ha
    obtain ⟨p, q, hpq, hpa, hqa⟩ := ha
    have hbpq : p = b ∨ q = b := by
      have h := hmeet p q a b hpq hab
      tauto
    have hext : ∃ w, w ≠ a ∧ G.Adj b w ∧
        ∀ u v, r u v → u = b ∨ v = b ∨ u = w ∨ v = w := by
      rcases hbpq with rfl | rfl
      · refine ⟨q, hqa, hedge p q hpq, ?_⟩
        intro u v huv
        have h := hmeet u v p q huv hpq
        tauto
      · refine ⟨p, hpa, (hedge p q hpq).symm, ?_⟩
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
        simpa [hvw] using (hedge a v huv).symm
      · subst v
        have huw : u = w := huvw.resolve_right (Ne.symm hwa)
        simpa [huw] using hedge u a huv
    exact htri a b w (hedge a b hab) hbw hwaAdj

lemma nonstar_has_disjoint_edges {α : Type*} (G : SimpleGraph α) (r : α → α → Prop)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hedge : ∀ u v, r u v → G.Adj u v)
    (hne : ∃ a b, r a b)
    (hnostar : ¬ ∃ c, ∀ u v, r u v → u = c ∨ v = c) :
    ∃ u v p q, r u v ∧ r p q ∧ u ≠ p ∧ u ≠ q ∧ v ≠ p ∧ v ≠ q := by
  classical
  by_contra h
  apply hnostar
  apply intersecting_edges_star G r htri hedge hne
  intro u v p q huv hpq
  by_contra hd
  push_neg at hd
  exact h ⟨u, v, p, q, huv, hpq, hd.1, hd.2.1, hd.2.2.1, hd.2.2.2⟩

end PEqualNP.Outside.L_meta_1031
