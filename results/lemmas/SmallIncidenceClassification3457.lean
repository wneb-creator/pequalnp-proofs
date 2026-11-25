import Mathlib

namespace PEqualNP.Outside.L_meta_3457.SmallClassification

lemma no_three_coloring :
    ¬ ∃ s : Fin 3 → Bool, ∀ a b, (SimpleGraph.cycleGraph 3).Adj a b → s a ≠ s b := by
  decide

lemma no_five_coloring :
    ¬ ∃ s : Fin 5 → Bool, ∀ a b, (SimpleGraph.cycleGraph 5).Adj a b → s a ≠ s b := by
  decide

lemma cycle_length_six {n : ℕ} (G : SimpleGraph (Fin n)) (hn : n ≤ 6)
    (s : Fin n → Bool) (hs : ∀ a b, G.Adj a b → s a ≠ s b)
    (hfour : ∀ a b c d, a ≠ c → b ≠ d →
      G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a)
    {v : Fin n} (p : G.Walk v v) (hp : p.IsCycle) : p.length = 6 := by
  have hlo := hp.three_le_length
  have hhi : p.length ≤ n := by simpa using hp.length_le_natCard
  have hc : p.length = 3 ∨ p.length = 4 ∨ p.length = 5 ∨ p.length = 6 := by omega
  rcases hc with h | h | h | h
  · obtain ⟨e⟩ := (SimpleGraph.cycleGraph_isContained_iff (by decide : 2 < 3)).2
      ⟨v, p, hp, h⟩
    exact False.elim (no_three_coloring ⟨fun a => s (e a),
      fun a b hab => hs _ _ (e.toHom.map_adj hab)⟩)
  · obtain ⟨e⟩ := (SimpleGraph.cycleGraph_isContained_iff (by decide : 2 < 4)).2
      ⟨v, p, hp, h⟩
    exact False.elim (hfour (e 0) (e 1) (e 2) (e 3)
      (fun he => (by decide : (0 : Fin 4) ≠ 2) (e.injective he))
      (fun he => (by decide : (1 : Fin 4) ≠ 3) (e.injective he))
      (e.toHom.map_adj (by decide)) (e.toHom.map_adj (by decide))
      (e.toHom.map_adj (by decide)) (e.toHom.map_adj (by decide)))
  · obtain ⟨e⟩ := (SimpleGraph.cycleGraph_isContained_iff (by decide : 2 < 5)).2
      ⟨v, p, hp, h⟩
    exact False.elim (no_five_coloring ⟨fun a => s (e a),
      fun a b hab => hs _ _ (e.toHom.map_adj hab)⟩)
  · exact h

lemma small_acyclic {n : ℕ} (G : SimpleGraph (Fin n)) (hn : n ≤ 5)
    (s : Fin n → Bool) (hs : ∀ a b, G.Adj a b → s a ≠ s b)
    (hfour : ∀ a b c d, a ≠ c → b ≠ d →
      G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) : G.IsAcyclic := by
  intro v p hp
  have he := cycle_length_six G (by omega) s hs hfour p hp
  have hl : p.length ≤ n := by simpa using hp.length_le_natCard
  omega

lemma six_two_neighbors (G : SimpleGraph (Fin 6))
    (s : Fin 6 → Bool) (hs : ∀ a b, G.Adj a b → s a ≠ s b)
    (hfour : ∀ a b c d, a ≠ c → b ≠ d →
      G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a)
    (hcyc : ¬ G.IsAcyclic) :
    ∀ v : Fin 6, ∃ a b, a ≠ b ∧ G.Adj v a ∧ G.Adj v b := by
  obtain ⟨v, p, hp⟩ := SimpleGraph.not_isAcyclic_iff_exists_isCycle.mp hcyc
  have hl := cycle_length_six G (by omega) s hs hfour p hp
  obtain ⟨e⟩ := (SimpleGraph.cycleGraph_isContained_iff (by decide : 2 < 6)).2
    ⟨v, p, hp, hl⟩
  have hsurj : Function.Surjective e := Finite.surjective_of_injective e.injective
  intro w
  obtain ⟨i, rfl⟩ := hsurj w
  refine ⟨e (i + 1), e (i - 1), ?_, ?_, ?_⟩
  · intro h
    have h' := e.injective h
    have hne : ∀ i : Fin 6, i + 1 ≠ i - 1 := by decide
    exact hne i h'
  · apply e.toHom.map_adj
    have h : ∀ i : Fin 6, (SimpleGraph.cycleGraph 6).Adj i (i + 1) := by decide
    exact h i
  · apply e.toHom.map_adj
    have h : ∀ i : Fin 6, (SimpleGraph.cycleGraph 6).Adj i (i - 1) := by decide
    exact h i

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
set_option synthInstance.maxSize 20000 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma matrix_three_classification :
    ∀ B : Fin 3 → Fin 3 → Bool,
      (∀ p p' l l', p ≠ p' → l ≠ l' →
        ¬ (B p l = true ∧ B p l' = true ∧ B p' l = true ∧ B p' l' = true)) →
      (∀ p, ∃ l l', l ≠ l' ∧ B p l = true ∧ B p l' = true) →
      (∀ l, ∃ p p', p ≠ p' ∧ B p l = true ∧ B p' l = true) →
      ∃ f : Fin 3 → Fin 3, Function.Bijective f ∧
        ∀ p l, B p l = true ↔ p ≠ f l := by
  unfold Function.Bijective Function.Injective Function.Surjective
  decide

lemma left_ne_right {N : ℕ} (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
  intro h
  have := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at this
  omega

lemma left_neighbor {N : ℕ} (I : Fin N → Fin N → Prop)
    (G : SimpleGraph (Fin (N + N)))
    (hG : ∀ u v, G.Adj u v ↔
      (∃ p l : Fin N, I p l ∧ u = Fin.castAdd N p ∧ v = Fin.natAdd N l) ∨
      (∃ p l : Fin N, I p l ∧ u = Fin.natAdd N l ∧ v = Fin.castAdd N p))
    (p : Fin N) {v : Fin (N + N)} (h : G.Adj (Fin.castAdd N p) v) :
    ∃ l, I p l ∧ v = Fin.natAdd N l := by
  rcases (hG _ _).1 h with ⟨p', l, hI, he, hv⟩ | ⟨p', l, _, he, _⟩
  · have hp : p = p' := Fin.ext (by simpa only [Fin.val_castAdd] using congrArg Fin.val he)
    subst p'
    exact ⟨l, hI, hv⟩
  · exact False.elim (left_ne_right p l he)

lemma right_neighbor {N : ℕ} (I : Fin N → Fin N → Prop)
    (G : SimpleGraph (Fin (N + N)))
    (hG : ∀ u v, G.Adj u v ↔
      (∃ p l : Fin N, I p l ∧ u = Fin.castAdd N p ∧ v = Fin.natAdd N l) ∨
      (∃ p l : Fin N, I p l ∧ u = Fin.natAdd N l ∧ v = Fin.castAdd N p))
    (l : Fin N) {v : Fin (N + N)} (h : G.Adj v (Fin.natAdd N l)) :
    ∃ p, I p l ∧ v = Fin.castAdd N p := by
  rcases (hG _ _).1 h with ⟨p, l', hI, hv, he⟩ | ⟨p, l', _, _, he⟩
  · have hl : l = l' := Fin.ext (by
      have := congrArg Fin.val he
      simp only [Fin.val_natAdd] at this
      omega)
    subst l'
    exact ⟨p, hI, hv⟩
  · exact False.elim (left_ne_right p l he.symm)

lemma incidence_four_free {N : ℕ} (I : Fin N → Fin N → Prop)
    (G : SimpleGraph (Fin (N + N)))
    (hG : ∀ u v, G.Adj u v ↔
      (∃ p l : Fin N, I p l ∧ u = Fin.castAdd N p ∧ v = Fin.natAdd N l) ∨
      (∃ p l : Fin N, I p l ∧ u = Fin.natAdd N l ∧ v = Fin.castAdd N p))
    (hI : ∀ p p' l l', p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) :
    ∀ a b c d, a ≠ c → b ≠ d →
      G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a := by
  intro a b c d hac hbd hab hbc hcd hda
  rcases (hG _ _).1 hab with ⟨p, l, hpl, rfl, rfl⟩ | ⟨p, l, hpl, rfl, rfl⟩
  · obtain ⟨p', hpl', rfl⟩ := right_neighbor I G hG l hbc.symm
    obtain ⟨l', hpl'', rfl⟩ := left_neighbor I G hG p hda.symm
    obtain ⟨q, hlast, hq⟩ := right_neighbor I G hG l' hcd
    have heq : p' = q := Fin.ext (by simpa only [Fin.val_castAdd] using congrArg Fin.val hq)
    subst q
    exact hI p p' l l' (fun h => hac (congrArg (Fin.castAdd N) h))
      (fun h => hbd (congrArg (Fin.natAdd N) h)) ⟨hpl, hpl'', hpl', hlast⟩
  · obtain ⟨l', hpl', rfl⟩ := left_neighbor I G hG p hbc
    obtain ⟨p', hpl'', rfl⟩ := right_neighbor I G hG l hda
    obtain ⟨q, hlast, hq⟩ := right_neighbor I G hG l' hcd.symm
    have heq : p' = q := Fin.ext (by simpa only [Fin.val_castAdd] using congrArg Fin.val hq)
    subst q
    exact hI p p' l l' (fun h => hbd (congrArg (Fin.castAdd N) h))
      (fun h => hac (congrArg (Fin.natAdd N) h)) ⟨hpl, hpl', hpl'', hlast⟩

lemma incidence_coloring {N : ℕ} (I : Fin N → Fin N → Prop)
    (G : SimpleGraph (Fin (N + N)))
    (hG : ∀ u v, G.Adj u v ↔
      (∃ p l : Fin N, I p l ∧ u = Fin.castAdd N p ∧ v = Fin.natAdd N l) ∨
      (∃ p l : Fin N, I p l ∧ u = Fin.natAdd N l ∧ v = Fin.castAdd N p)) :
    ∀ u v, G.Adj u v → decide (u.val < N) ≠ decide (v.val < N) := by
  intro u v huv
  rcases (hG _ _).1 huv with ⟨p, l, _, rfl, rfl⟩ | ⟨p, l, _, rfl, rfl⟩
  all_goals simp only [Fin.val_castAdd, Fin.val_natAdd, Fin.is_lt, decide_true]
  all_goals simp

lemma three_incidence_classification (I : Fin 3 → Fin 3 → Prop) [DecidableRel I]
    (G : SimpleGraph (Fin (3 + 3)))
    (hG : ∀ u v, G.Adj u v ↔
      (∃ p l : Fin 3, I p l ∧ u = Fin.castAdd 3 p ∧ v = Fin.natAdd 3 l) ∨
      (∃ p l : Fin 3, I p l ∧ u = Fin.natAdd 3 l ∧ v = Fin.castAdd 3 p))
    (hI : ∀ p p' l l', p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) :
    G.IsAcyclic ∨ ∃ f : Fin 3 → Fin 3, Function.Bijective f ∧
      ∀ p l, I p l ↔ p ≠ f l := by
  classical
  by_cases hac : G.IsAcyclic
  · exact Or.inl hac
  right
  have htwo := six_two_neighbors G (fun u => decide (u.val < 3))
    (incidence_coloring I G hG) (incidence_four_free I G hG hI) hac
  have hr : ∀ p, ∃ l l', l ≠ l' ∧ I p l ∧ I p l' := by
    intro p
    obtain ⟨a, b, hab, ha, hb⟩ := htwo (Fin.castAdd 3 p)
    obtain ⟨l, hpl, rfl⟩ := left_neighbor I G hG p ha
    obtain ⟨l', hpl', rfl⟩ := left_neighbor I G hG p hb
    exact ⟨l, l', fun h => hab (congrArg (Fin.natAdd 3) h), hpl, hpl'⟩
  have hc : ∀ l, ∃ p p', p ≠ p' ∧ I p l ∧ I p' l := by
    intro l
    obtain ⟨a, b, hab, ha, hb⟩ := htwo (Fin.natAdd 3 l)
    obtain ⟨p, hpl, rfl⟩ := right_neighbor I G hG l ha.symm
    obtain ⟨p', hpl', rfl⟩ := right_neighbor I G hG l hb.symm
    exact ⟨p, p', fun h => hab (congrArg (Fin.castAdd 3) h), hpl, hpl'⟩
  simpa only [decide_eq_true_eq] using
    matrix_three_classification (fun p l => decide (I p l))
      (by simpa only [decide_eq_true_eq] using hI)
      (by simpa only [decide_eq_true_eq] using hr)
      (by simpa only [decide_eq_true_eq] using hc)

lemma two_incidence_acyclic {N : ℕ} (hN : N ≤ 2) (I : Fin N → Fin N → Prop)
    (G : SimpleGraph (Fin (N + N)))
    (hG : ∀ u v, G.Adj u v ↔
      (∃ p l : Fin N, I p l ∧ u = Fin.castAdd N p ∧ v = Fin.natAdd N l) ∨
      (∃ p l : Fin N, I p l ∧ u = Fin.natAdd N l ∧ v = Fin.castAdd N p))
    (hI : ∀ p p' l l', p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) : G.IsAcyclic := by
  exact small_acyclic G (by omega) (fun u => decide (u.val < N))
    (incidence_coloring I G hG) (incidence_four_free I G hG hI)

end PEqualNP.Outside.L_meta_3457.SmallClassification
