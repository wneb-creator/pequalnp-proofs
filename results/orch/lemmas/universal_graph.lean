import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3451

lemma acyclic_of_one_nonleaf_side {V : Type*} (G : SimpleGraph V)
    (P : V → Prop) (u : V)
    (bip : ∀ a b, G.Adj a b → (P a ↔ ¬ P b))
    (leaf : ∀ a, P a → a ≠ u → ∀ b c, G.Adj a b → G.Adj a c → b = c) :
    G.IsAcyclic := by
  classical
  have center {a : V} (c : G.Walk a a) (hc : c.IsCycle) (ha : P a) : a = u := by
    by_contra hne
    exact hc.snd_ne_penultimate
      (leaf a ha hne c.snd c.penultimate (c.adj_snd hc.not_nil)
        (c.adj_penultimate hc.not_nil).symm)
  have no_right {a : V} (c : G.Walk a a) (hc : c.IsCycle) (ha : ¬ P a) : False := by
    have hs : P c.snd := (bip c.snd a (c.adj_snd hc.not_nil).symm).2 ha
    have ht : P c.penultimate := (bip c.penultimate a (c.adj_penultimate hc.not_nil)).2 ha
    have es : c.snd = u := center (c.rotate c.snd (c.getVert_mem_support 1)) (hc.rotate _) hs
    have et : c.penultimate = u := center
      (c.rotate c.penultimate (c.getVert_mem_support (c.length - 1))) (hc.rotate _) ht
    exact hc.snd_ne_penultimate (es.trans et.symm)
  intro a c hc
  by_cases ha : P a
  · have hs : ¬ P c.snd := (bip a c.snd (c.adj_snd hc.not_nil)).1 ha
    exact no_right (c.rotate c.snd (c.getVert_mem_support 1)) (hc.rotate _) hs
  · exact no_right c hc ha

def incGraph (N : ℕ) (I : Fin N → Fin N → Prop) : SimpleGraph (Fin (N + N)) where
  Adj a b := ∃ p l : Fin N, I p l ∧
    ((a = Fin.castAdd N p ∧ b = Fin.natAdd N l) ∨
      (a = Fin.natAdd N l ∧ b = Fin.castAdd N p))
  symm := ⟨by
    rintro a b ⟨p, l, hI, h⟩
    exact ⟨p, l, hI, by tauto⟩⟩
  loopless := ⟨by
    rintro a ⟨p, l, hI, h⟩
    rcases h with ⟨hp, hl⟩ | ⟨hl, hp⟩
    all_goals
      have h := congrArg Fin.val (hp.symm.trans hl)
      have := p.isLt
      change p.val = N + l.val at h
      omega⟩

lemma incGraph_bipartite (N : ℕ) (I : Fin N → Fin N → Prop) :
    ∀ a b, (incGraph N I).Adj a b → (a.val < N ↔ ¬ b.val < N) := by
  rintro a b ⟨p, l, hI, h⟩
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    have := p.isLt
    simp only [Fin.val_castAdd, Fin.val_natAdd]
    omega

lemma incGraph_left_neighbors (N : ℕ) (I : Fin N → Fin N → Prop)
    (p : Fin N) (b : Fin (N + N)) :
    (incGraph N I).Adj (Fin.castAdd N p) b ↔
      ∃ l : Fin N, I p l ∧ b = Fin.natAdd N l := by
  constructor
  · rintro ⟨q, l, hI, h⟩
    rcases h with ⟨h, hb⟩ | ⟨h, hb⟩
    · have hq : p = q := Fin.ext (congrArg (fun x : Fin (N + N) => x.val) h)
      subst q
      exact ⟨l, hI, hb⟩
    · have he := congrArg Fin.val h
      have := p.isLt
      change p.val = N + l.val at he
      omega
  · rintro ⟨l, hI, hb⟩
    exact ⟨p, l, hI, Or.inl ⟨rfl, hb⟩⟩

lemma incGraph_right_neighbors (N : ℕ) (I : Fin N → Fin N → Prop)
    (l : Fin N) (b : Fin (N + N)) :
    (incGraph N I).Adj (Fin.natAdd N l) b ↔
      ∃ p : Fin N, I p l ∧ b = Fin.castAdd N p := by
  constructor
  · rintro ⟨p, q, hI, h⟩
    rcases h with ⟨h, hb⟩ | ⟨h, hb⟩
    · have he := congrArg Fin.val h
      have := p.isLt
      change N + l.val = p.val at he
      omega
    · have he := congrArg Fin.val h
      have hq : l = q := Fin.ext (by simpa using he)
      subst q
      exact ⟨p, hI, hb⟩
  · rintro ⟨p, hI, hb⟩
    exact ⟨p, l, hI, Or.inr ⟨rfl, hb⟩⟩

lemma incGraph_acyclic_of_universal_row (N : ℕ) (I : Fin N → Fin N → Prop)
    (hfour : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (p0 : Fin N) (hall : ∀ l, I p0 l) : (incGraph N I).IsAcyclic := by
  apply acyclic_of_one_nonleaf_side (incGraph N I) (fun a => a.val < N)
    (Fin.castAdd N p0) (incGraph_bipartite N I)
  intro a ha hne b c hab hac
  let p : Fin N := ⟨a.val, ha⟩
  have he : a = Fin.castAdd N p := Fin.ext rfl
  have hp : p ≠ p0 := by
    intro h
    exact hne (he.trans (congrArg (Fin.castAdd N) h))
  rw [he, incGraph_left_neighbors] at hab hac
  obtain ⟨l, hpl, rfl⟩ := hab
  obtain ⟨l', hpl', rfl⟩ := hac
  have hll : l = l' := by
    by_contra h
    exact hfour p p0 l l' hp h ⟨hpl, hpl', hall l, hall l'⟩
  exact congrArg (Fin.natAdd N) hll

lemma incGraph_acyclic_of_universal_column (N : ℕ) (I : Fin N → Fin N → Prop)
    (hfour : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (l0 : Fin N) (hall : ∀ p, I p l0) : (incGraph N I).IsAcyclic := by
  have hbip : ∀ a b, (incGraph N I).Adj a b → (N ≤ a.val ↔ ¬ N ≤ b.val) := by
    intro a b hab
    have h := incGraph_bipartite N I a b hab
    omega
  apply acyclic_of_one_nonleaf_side (incGraph N I) (fun a => N ≤ a.val)
    (Fin.natAdd N l0) hbip
  intro a ha hne b c hab hac
  let l : Fin N := ⟨a.val - N, by have := a.isLt; omega⟩
  have he : a = Fin.natAdd N l := Fin.ext (by dsimp [l]; omega)
  have hl : l ≠ l0 := by
    intro h
    exact hne (he.trans (congrArg (Fin.natAdd N) h))
  rw [he, incGraph_right_neighbors] at hab hac
  obtain ⟨p, hpl, rfl⟩ := hab
  obtain ⟨p', hpl', rfl⟩ := hac
  have hpp : p = p' := by
    by_contra h
    exact hfour p p' l l0 h hl ⟨hpl, hall p, hpl', hall p'⟩
  exact congrArg (Fin.castAdd N) hpp

def incGraphDecidable (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] :
    DecidableRel (incGraph N I).Adj := by
  intro a b
  change Decidable (∃ p l : Fin N, I p l ∧
    ((a = Fin.castAdd N p ∧ b = Fin.natAdd N l) ∨
      (a = Fin.natAdd N l ∧ b = Fin.castAdd N p)))
  infer_instance

lemma incGraph_edge_iff (N : ℕ) (I : Fin N → Fin N → Prop) (z : Fin (N + N) → Bool) :
    (∃ a b : Fin (N + N), (incGraph N I).Adj a b ∧ z a = true ∧ z b = true) ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true := by
  constructor
  · rintro ⟨a, b, ⟨p, l, hI, h⟩, ha, hb⟩
    refine ⟨p, l, hI, ?_⟩
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨ha, hb⟩
    · exact ⟨hb, ha⟩
  · rintro ⟨p, l, hI, hp, hl⟩
    exact ⟨Fin.castAdd N p, Fin.natAdd N l,
      ⟨p, l, hI, Or.inl ⟨rfl, rfl⟩⟩, hp, hl⟩

lemma incGraph_graphFun_iff (N : ℕ) (I : Fin N → Fin N → Prop)
    [DecidableRel (incGraph N I).Adj] (z : Fin (N + N) → Bool) :
    PEqualNP.MetaComplexity.NestedCover.graphFun (incGraph N I) ∅ z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true := by
  simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, Finset.notMem_empty,
    false_and, exists_false, decide_false, Bool.false_or, decide_eq_true_eq]
  exact incGraph_edge_iff N I z

end PEqualNP.Outside.L_meta_3451
