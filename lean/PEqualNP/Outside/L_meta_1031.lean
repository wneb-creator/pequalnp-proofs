import Mathlib
import PEqualNP.Defs

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
  · push Not at ha
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
    push Not at hn
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
  push Not at hd
  exact h ⟨u, v, p, q, huv, hpq, hd.1, hd.2.1, hd.2.2.1, hd.2.2.2⟩

open PEqualNP.CircuitLowerBounds

lemma edgeless_least (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : ∀ u v : Fin n, ¬ G.Adj u v) :
    ∃ C : Circuit, C.gates = [] ∧
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) =
        decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) ∧
      ∀ D : Circuit, C.size ≤ D.size := by
  refine ⟨⟨[], n⟩, rfl, ?_, ?_⟩
  · intro x
    have hfalse : ¬ ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true := by
      rintro ⟨i, j, hij, _, _⟩
      exact hG i j hij
    simp [Circuit.eval, Circuit.wires, List.getD_eq_getElem?_getD, hfalse]
  · intro D
    simp [Circuit.size]

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def p4Cnf : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.or, [1, 3]⟩, ⟨.and, [4, 5]⟩,
    ⟨.or, [1, 2]⟩, ⟨.and, [6, 7]⟩], 8⟩

def p4Star : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.and, [1, 4]⟩, ⟨.and, [2, 3]⟩,
    ⟨.or, [5, 6]⟩], 7⟩

lemma p4_boolean_exchange (a b c d : Bool) :
    (((a || c) && (b || d)) && (b || c)) =
      ((b && (a || c)) || (c && d)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

lemma p4_exchange (a b c d : Bool) :
    p4Cnf.eval [a, b, c, d] = p4Star.eval [a, b, c, d] := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

lemma p4_functions : circuitFun 4 p4Cnf = circuitFun 4 p4Star := by
  funext x
  change p4Cnf.eval [x 0, x 1, x 2, x 3] = p4Star.eval [x 0, x 1, x 2, x 3]
  exact p4_exchange _ _ _ _

lemma p4Star_mono : Monotone2 p4Star := by
  simp [Monotone2, p4Star]

lemma p4Cnf_mono : Monotone2 p4Cnf := by
  simp [Monotone2, p4Cnf]

lemma p4_size_drop : p4Star.size + 1 = p4Cnf.size := rfl

lemma p4Cnf_not_minimal : ¬ IsMinimalMonoCircuit 4 p4Cnf := by
  intro h
  have hs := h.2 p4Star p4Star_mono p4_functions.symm
  change 5 ≤ 4 at hs
  omega

lemma no_four_common_center {V : Type*} (G : SimpleGraph V)
    (hfour : ∀ a b c d : V, G.Adj a b → G.Adj b c →
      G.Adj c d → G.Adj d a → a = c ∨ b = d)
    {a b c u : V} (hac : a ≠ c) (hab : G.Adj a b)
    (hbc : G.Adj b c) (hua : G.Adj u a) (huc : G.Adj u c) : u = b := by
  exact ((hfour a b c u hab hbc huc.symm hua).resolve_left hac).symm

lemma no_triangle_common_center {V : Type*} (G : SimpleGraph V)
    (htri : ∀ a b c : V, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    {b c : V} (hbc : G.Adj b c) :
    ¬ ∃ u : V, G.Adj u b ∧ G.Adj u c := by
  rintro ⟨u, hub, huc⟩
  exact htri u b c hub hbc huc.symm

lemma p4_or_sharing {V : Type*} (G : SimpleGraph V)
    (htri : ∀ a b c : V, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hfour : ∀ a b c d : V, G.Adj a b → G.Adj b c →
      G.Adj c d → G.Adj d a → a = c ∨ b = d)
    {a b c d : V} (hac : a ≠ c) (hbd : b ≠ d)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) :
    (∀ u : V, G.Adj u a → G.Adj u c → u = b) ∧
    (∀ u : V, G.Adj u b → G.Adj u d → u = c) ∧
    (∀ u : V, ¬ (G.Adj u b ∧ G.Adj u c)) := by
  refine ⟨fun u hua huc => no_four_common_center G hfour hac hab hbc hua huc,
    fun u hub hud => no_four_common_center G hfour hbd hbc hcd hub hud, ?_⟩
  intro u hu
  exact no_triangle_common_center G htri hbc ⟨u, hu⟩

lemma pair_edge {V : Type*} (G : SimpleGraph V) {a b : V}
    (h : ∃ u v : V, G.Adj u v ∧ (u = a ∨ u = b) ∧ (v = a ∨ v = b)) :
    G.Adj a b := by
  obtain ⟨u, v, huv, hu, hv⟩ := h
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · exact (huv.ne rfl).elim
  · exact huv
  · exact huv.symm
  · exact (huv.ne rfl).elim

lemma sound_or_singleton_center {n : ℕ} (G : SimpleGraph (Fin n))
    (hfour : ∀ a b c d : Fin n, G.Adj a b → G.Adj b c →
      G.Adj c d → G.Adj d a → a = c ∨ b = d)
    {a b c : Fin n} (hac : a ≠ c) (hab : G.Adj a b) (hbc : G.Adj b c)
    (F : (Fin n → Bool) → Bool)
    (hmono : ∀ x y : Fin n → Bool, (∀ i, x i = true → y i = true) →
      F x = true → F y = true)
    (hsound : ∀ x : Fin n → Bool, ((x a || x c) && F x) = true →
      ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)
    (u : Fin n) (hu : F (fun i => decide (i = u)) = true) : u = b := by
  have center (v : Fin n) (hv : v = a ∨ v = c) : G.Adj v u := by
    let x : Fin n → Bool := fun i => decide (i = v ∨ i = u)
    have hx : F x = true := by
      apply hmono (fun i => decide (i = u)) x ?_ hu
      intro i hi
      have hiu : i = u := of_decide_eq_true hi
      exact decide_eq_true (Or.inr hiu)
    have hor : (x a || x c) = true := by
      rcases hv with rfl | rfl <;> simp [x]
    obtain ⟨p, q, hpq, hp, hq⟩ := hsound x (by simp [hor, hx])
    exact pair_edge G ⟨p, q, hpq, of_decide_eq_true hp, of_decide_eq_true hq⟩
  exact no_four_common_center G hfour hac hab hbc
    (center a (Or.inl rfl)).symm (center c (Or.inr rfl)).symm

end PEqualNP.Outside.L_meta_1031
