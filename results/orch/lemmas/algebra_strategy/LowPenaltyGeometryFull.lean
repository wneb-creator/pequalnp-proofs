import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_650_aux.LowPenaltyGeometry

open PEqualNP.MetaComplexity.NestedCover

set_option maxRecDepth 8192
set_option maxHeartbeats 0

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

theorem neighbor_colors (color : Fin n → Bool)
    (bip : ∀ a b, G.Adj a b → color a ≠ color b)
    {a b c : Fin n} (hab : G.Adj a b) (hac : G.Adj a c) : color b = color c := by
  have h1 := bip a b hab
  have h2 := bip a c hac
  cases hca : color a <;> cases hcb : color b <;> cases hcc : color c <;> simp_all

theorem no_common_opposite (color : Fin n → Bool)
    (bip : ∀ a b, G.Adj a b → color a ≠ color b)
    {a b : Fin n} (hab : color a ≠ color b) :
    ∀ c, ¬ (G.Adj a c ∧ G.Adj b c) := by
  rintro c ⟨hac, hbc⟩
  exact hab (neighbor_colors G color bip hac.symm hbc.symm)

theorem pair_negative {a b : Fin n} (hab : ¬ G.Adj a b) :
    graphFun G ∅ (fun i => decide (i = a ∨ i = b)) = false := by
  suffices h : ¬ ∃ u v, G.Adj u v ∧ (u = a ∨ u = b) ∧ (v = a ∨ v = b) by
    simpa [graphFun] using h
  rintro ⟨u, v, huv, hu, hv⟩
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · exact G.irrefl huv
  · exact hab huv
  · exact hab huv.symm
  · exact G.irrefl huv

theorem two_arms_impossible (color : Fin n → Bool)
    (bip : ∀ a b, G.Adj a b → color a ≠ color b)
    (no4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (U : Finset (Sym2 (Fin n))) (sub : U ⊆ G.edgeFinset)
    (v w p z q : Fin n)
    (hw : (G.deleteEdges ↑U).Adj v w) (hz : (G.deleteEdges ↑U).Adj v z)
    (ew : s(w,p) ∈ U) (ez : s(z,q) ∈ U) (different : s(w,p) ≠ s(z,q))
    (promise : ∀ x : Fin n → Bool, x w = true → graphFun G ∅ x = false →
      ∃ K : Finset (Fin n),
        (K.card ≤ 1 ∨ ∃ a, ∀ b ∈ K, (G.deleteEdges ↑U).Adj b a) ∧
        (∀ a b, s(a,b) ∈ U → a ∈ K ∨ b ∈ K) ∧ ∀ a ∈ K, x a = false) : False := by
  classical
  have hvw := (SimpleGraph.deleteEdges_adj.mp hw).1
  have hvz := (SimpleGraph.deleteEdges_adj.mp hz).1
  have hwp : G.Adj w p := SimpleGraph.mem_edgeFinset.mp (sub ew)
  have hzq : G.Adj z q := SimpleGraph.mem_edgeFinset.mp (sub ez)
  have hpv : p ≠ v := by
    intro hp
    subst p
    exact (SimpleGraph.deleteEdges_adj.mp hw).2 (by simpa [Sym2.eq_swap] using ew)
  have hqv : q ≠ v := by
    intro hq
    subst q
    exact (SimpleGraph.deleteEdges_adj.mp hz).2 (by simpa [Sym2.eq_swap] using ez)
  by_cases hsame : w = z
  · subst z
    have hpq : p ≠ q := by intro h; subst q; exact different rfl
    let x : Fin n → Bool := fun i => decide (i = w ∨ i = w)
    obtain ⟨K, hK, cover, avoid⟩ := promise x (by simp [x])
      (pair_negative G G.irrefl)
    have hwK : w ∉ K := by intro h; have := avoid w h; simp [x] at this
    have hpK : p ∈ K := (cover w p ew).resolve_left hwK
    have hqK : q ∈ K := (cover w q ez).resolve_left hwK
    rcases hK with hsmall | ⟨a, ha⟩
    · have h := Finset.card_le_one.mp hsmall p hpK q hqK
      exact hpq h
    · have hpa := ha p hpK
      have hqa := ha q hqK
      have hwa : w ≠ a := by
        intro h
        subst a
        exact (SimpleGraph.deleteEdges_adj.mp hpa).2
          (by simpa [Sym2.eq_swap] using ew)
      exact no4 p w q a hpq hwa ⟨hwp.symm, hzq,
        (SimpleGraph.deleteEdges_adj.mp hqa).1, (SimpleGraph.deleteEdges_adj.mp hpa).1.symm⟩
  · have hwq : ¬ G.Adj w q := by
      intro h
      exact no4 v w q z (Ne.symm hqv) hsame ⟨hvw, h, hzq.symm, hvz.symm⟩
    have colors : color w = color z := neighbor_colors G color bip hvw hvz
    have hpz : color p ≠ color z := by
      intro h
      exact bip w p hwp (colors.trans h.symm)
    let x : Fin n → Bool := fun i => decide (i = w ∨ i = q)
    obtain ⟨K, hK, cover, avoid⟩ := promise x (by simp [x]) (pair_negative G hwq)
    have hwK : w ∉ K := by intro h; have := avoid w h; simp [x] at this
    have hqK : q ∉ K := by intro h; have := avoid q h; simp [x] at this
    have hpK : p ∈ K := (cover w p ew).resolve_left hwK
    have hzK : z ∈ K := (cover z q ez).resolve_right hqK
    rcases hK with hsmall | ⟨a, ha⟩
    · have h := Finset.card_le_one.mp hsmall p hpK z hzK
      exact hpz (congrArg color h)
    · exact no_common_opposite G color bip hpz a
        ⟨(SimpleGraph.deleteEdges_adj.mp (ha p hpK)).1,
          (SimpleGraph.deleteEdges_adj.mp (ha z hzK)).1⟩


theorem residual_card_le_one (color : Fin n → Bool)
    (bip : ∀ a b, G.Adj a b → color a ≠ color b)
    (no4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (U : Finset (Sym2 (Fin n))) (sub : U ⊆ G.edgeFinset)
    (center : ∃ v : Fin n, ∀ a b, s(a,b) ∈ U → ∃ w,
      (w = a ∨ w = b) ∧ (G.deleteEdges ↑U).Adj v w ∧
      ∀ x : Fin n → Bool, x w = true → graphFun G ∅ x = false →
      ∃ K : Finset (Fin n),
        (K.card ≤ 1 ∨ ∃ c, ∀ d ∈ K, (G.deleteEdges ↑U).Adj d c) ∧
        (∀ c d, s(c,d) ∈ U → c ∈ K ∨ d ∈ K) ∧ ∀ c ∈ K, x c = false) :
    U.card ≤ 1 := by
  classical
  obtain ⟨v, hv⟩ := center
  let Promise := fun w : Fin n => ∀ x : Fin n → Bool,
    x w = true → graphFun G ∅ x = false → ∃ K : Finset (Fin n),
      (K.card ≤ 1 ∨ ∃ c, ∀ d ∈ K, (G.deleteEdges ↑U).Adj d c) ∧
      (∀ c d, s(c,d) ∈ U → c ∈ K ∨ d ∈ K) ∧ ∀ c ∈ K, x c = false
  have orient : ∀ e ∈ U, ∃ w p, s(w,p) = e ∧
      (G.deleteEdges ↑U).Adj v w ∧ Promise w := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      obtain ⟨w, hor, hw, hp⟩ := hv a b he
      rcases hor with hwa | hwb
      · subst w; exact ⟨a, b, rfl, hw, hp⟩
      · subst w; exact ⟨b, a, Sym2.eq_swap, hw, hp⟩
  apply Finset.card_le_one.mpr
  intro e he f hf
  by_contra hne
  obtain ⟨w, p, heq, hw, hp⟩ := orient e he
  obtain ⟨z, q, hfq, hz, hq⟩ := orient f hf
  exact two_arms_impossible G color bip no4 U sub v w p z q hw hz
    (by simpa [heq] using he) (by simpa [hfq] using hf)
    (by simpa [heq, hfq] using hne) hp


theorem cover_delete_one (U : Finset (Sym2 (Fin n))) (small : U.card ≤ 1)
    (K : Finset (Fin n)) (cover : (G.deleteEdges ↑U).IsVertexCover ↑K) :
    ∃ T : Finset (Fin n), G.IsVertexCover ↑T ∧ T.card ≤ K.card + 1 := by
  classical
  by_cases empty : U = ∅
  · refine ⟨K, ?_, by omega⟩
    simpa [empty] using cover
  · obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr empty
    induction e using Sym2.ind with
    | _ u v =>
      refine ⟨insert u K, ?_, Finset.card_insert_le _ _⟩
      intro a b hab
      by_cases hmem : s(a,b) ∈ U
      · have eq : s(a,b) = s(u,v) := Finset.card_le_one.mp small _ hmem _ he
        rcases Sym2.eq_iff.mp eq with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · exact Or.inl (by simp [ha])
        · exact Or.inr (by simp [hb])
      · have hd : (G.deleteEdges ↑U).Adj a b :=
          SimpleGraph.deleteEdges_adj.mpr ⟨hab, hmem⟩
        rcases cover hd with ha | hb
        · exact Or.inl (Finset.mem_insert_of_mem ha)
        · exact Or.inr (Finset.mem_insert_of_mem hb)

end PEqualNP.Outside.L_meta_650_aux.LowPenaltyGeometry
