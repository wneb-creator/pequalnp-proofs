import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17764

open PEqualNP.BicliqueBlockCost

noncomputable def small {n : ℕ} (p : Block n) : Finset (Fin n) :=
  if p.1.card ≤ 1 then p.1 else p.2

noncomputable def pairs {n : ℕ} (p : Block n) : Finset (Sym2 (Fin n)) :=
  (p.1 ×ˢ p.2).image (fun ab => s(ab.1, ab.2))

lemma small_card {n : ℕ} (p : Block n) (h : p.1.card ≤ 1 ∨ p.2.card ≤ 1) :
    (small p).card ≤ 1 := by
  unfold small
  split_ifs with h1
  · exact h1
  · rcases h with h | h
    · exact absurd h h1
    · exact h

lemma pairs_card {n : ℕ} (G : SimpleGraph (Fin n)) (p : Block n) (hb : IsBlock G p)
    (h : p.1.card ≤ 1 ∨ p.2.card ≤ 1) : (pairs p).card ≤ blockCost p := by
  obtain ⟨_, h1, h2, _⟩ := hb
  have a1 : 1 ≤ p.1.card := Finset.card_pos.mpr h1
  have a2 : 1 ≤ p.2.card := Finset.card_pos.mpr h2
  have hc : (pairs p).card ≤ p.1.card * p.2.card := by
    unfold pairs
    exact Finset.card_image_le.trans (le_of_eq (Finset.card_product _ _))
  unfold blockCost
  rcases h with h | h
  · have e : p.1.card = 1 := le_antisymm h a1
    rw [e] at hc ⊢
    omega
  · have e : p.2.card = 1 := le_antisymm h a2
    rw [e] at hc ⊢
    omega

lemma main {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (F : Finset (Block n))
    (hF : IsBlockCover G F) (hs : ∀ p ∈ F, p.1.card ≤ 1 ∨ p.2.card ≤ 1) :
    ∃ X : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G X ∧
      G.edgeFinset.card + X.card ≤ familyCost F + 1 := by
  classical
  obtain ⟨hblk, hcov⟩ := hF
  refine ⟨F.biUnion small, ?_, ?_⟩
  · intro u v huv
    obtain ⟨p, hp, hc⟩ := hcov u v huv
    have key : ∀ a b : Fin n, a ∈ p.1 → b ∈ p.2 → a ∈ small p ∨ b ∈ small p := by
      intro a b ha hb
      unfold small
      split_ifs
      · exact Or.inl ha
      · exact Or.inr hb
    rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rcases key u v h1 h2 with h | h
      · exact Or.inl (Finset.mem_biUnion.mpr ⟨p, hp, h⟩)
      · exact Or.inr (Finset.mem_biUnion.mpr ⟨p, hp, h⟩)
    · rcases key v u h1 h2 with h | h
      · exact Or.inr (Finset.mem_biUnion.mpr ⟨p, hp, h⟩)
      · exact Or.inl (Finset.mem_biUnion.mpr ⟨p, hp, h⟩)
  · have hsub : G.edgeFinset ⊆ F.biUnion pairs := by
      intro e
      refine Sym2.ind (fun u v => ?_) e
      intro he
      obtain ⟨p, hp, hc⟩ := hcov u v (SimpleGraph.mem_edgeFinset.mp he)
      refine Finset.mem_biUnion.mpr ⟨p, hp, ?_⟩
      unfold pairs
      rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Finset.mem_image.mpr ⟨(u, v), Finset.mem_product.mpr ⟨h1, h2⟩, rfl⟩
      · exact Finset.mem_image.mpr ⟨(v, u), Finset.mem_product.mpr ⟨h1, h2⟩, Sym2.eq_swap⟩
    have hE : G.edgeFinset.card ≤ ∑ p ∈ F, blockCost p := by
      calc G.edgeFinset.card ≤ (F.biUnion pairs).card := Finset.card_le_card hsub
        _ ≤ ∑ p ∈ F, (pairs p).card := Finset.card_biUnion_le
        _ ≤ ∑ p ∈ F, blockCost p :=
            Finset.sum_le_sum (fun p hp => pairs_card G p (hblk p hp) (hs p hp))
    have hX : (F.biUnion small).card ≤ F.card := by
      calc (F.biUnion small).card ≤ ∑ p ∈ F, (small p).card := Finset.card_biUnion_le
        _ ≤ ∑ _p ∈ F, 1 := Finset.sum_le_sum (fun p hp => small_card p (hs p hp))
        _ = F.card := by simp
    unfold familyCost
    omega

end PEqualNP.Outside.L_meta_17764

theorem PEqualNP.Outside.L_meta_17764 : (let x1 : SimpleGraph (Fin (26 : ℕ)) :=   PEqualNP.EdgeOwnership.edgeGraph (26 : ℕ)     (have x1 : List (ℕ × ℕ) :=       have x1 : List (ℕ × ℕ) :=         have x1 : List (ℕ × ℕ) := [((11 : ℕ), (23 : ℕ)), ((11 : ℕ), (24 : ℕ)), ((12 : ℕ), (16 : ℕ)), ((12 : ℕ), (22 : ℕ)), ((12 : ℕ), (24 : ℕ)), ((12 : ℕ), (25 : ℕ))];         ((10 : ℕ), (14 : ℕ)) :: ((10 : ℕ), (20 : ℕ)) :: ((10 : ℕ), (22 : ℕ)) :: ((10 : ℕ), (23 : ℕ)) :: ((11 : ℕ), (15 : ℕ)) :: ((11 : ℕ), (21 : ℕ)) :: x1;       have x2 : List (ℕ × ℕ) := ((8 : ℕ), (20 : ℕ)) :: ((8 : ℕ), (21 : ℕ)) :: ((8 : ℕ), (25 : ℕ)) :: ((9 : ℕ), (19 : ℕ)) :: ((9 : ℕ), (21 : ℕ)) :: ((9 : ℕ), (22 : ℕ)) :: x1;       ((7 : ℕ), (17 : ℕ)) :: ((7 : ℕ), (19 : ℕ)) :: ((7 : ℕ), (20 : ℕ)) :: ((7 : ℕ), (24 : ℕ)) :: ((8 : ℕ), (18 : ℕ)) :: x2;     have x2 : List (ℕ × ℕ) :=       have x2 : List (ℕ × ℕ) := ((5 : ℕ), (18 : ℕ)) :: ((5 : ℕ), (22 : ℕ)) :: ((6 : ℕ), (16 : ℕ)) :: ((6 : ℕ), (18 : ℕ)) :: ((6 : ℕ), (19 : ℕ)) :: ((6 : ℕ), (23 : ℕ)) :: x1;       ((4 : ℕ), (16 : ℕ)) :: ((4 : ℕ), (17 : ℕ)) :: ((4 : ℕ), (21 : ℕ)) :: ((5 : ℕ), (15 : ℕ)) :: ((5 : ℕ), (17 : ℕ)) :: x2;     have x3 : List (ℕ × ℕ) := ((2 : ℕ), (19 : ℕ)) :: ((2 : ℕ), (25 : ℕ)) :: ((3 : ℕ), (15 : ℕ)) :: ((3 : ℕ), (16 : ℕ)) :: ((3 : ℕ), (20 : ℕ)) :: ((4 : ℕ), (14 : ℕ)) :: x2;     ((1 : ℕ), (14 : ℕ)) :: ((1 : ℕ), (18 : ℕ)) :: ((1 : ℕ), (24 : ℕ)) :: ((2 : ℕ), (14 : ℕ)) :: ((2 : ℕ), (15 : ℕ)) :: x3); ∀ (x2 : Finset (PEqualNP.BicliqueBlockCost.Block (26 : ℕ))), PEqualNP.BicliqueBlockCost.IsBlockCover x1 x2 → (∀ x4 ∈ x2, x4.1.card ≤ (1 : ℕ) ∨ x4.2.card ≤ (1 : ℕ)) → ∃ (x5 : Finset (Fin (26 : ℕ))), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover x1 x5 ∧ x1.edgeFinset.card + x5.card ≤ PEqualNP.BicliqueBlockCost.familyCost x2 + (1 : ℕ)) := by
  intro G F hF hs
  exact PEqualNP.Outside.L_meta_17764.main G F hF hs
