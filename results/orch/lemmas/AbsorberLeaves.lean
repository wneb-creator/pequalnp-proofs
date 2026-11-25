import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1031.AbsorberLeaves

def HasEdge {V : Type*} (G : SimpleGraph V) (X : Set V) : Prop :=
  ∃ u ∈ X, ∃ v ∈ X, G.Adj u v

lemma edge_in_triple {V : Type*} (G : SimpleGraph V) {b d z : V}
    (hbd : ¬ G.Adj b d) (h : HasEdge G {b,d,z}) : G.Adj z b ∨ G.Adj z d := by
  obtain ⟨u,hu,v,hv,he⟩ := h
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hu hv
  rcases hu with rfl|rfl|rfl <;> rcases hv with rfl|rfl|rfl
  · exact (he.ne rfl).elim
  · exact (hbd he).elim
  · exact Or.inl he.symm
  · exact (hbd he.symm).elim
  · exact (he.ne rfl).elim
  · exact Or.inr he.symm
  · exact Or.inl he
  · exact Or.inr he
  · exact (he.ne rfl).elim

lemma leaf_restriction {V : Type*} (G : SimpleGraph V) (L : Set V) (y a b c d : V)
    (h4 : ∀ p q r s, G.Adj p q → G.Adj q r → G.Adj r s → G.Adj s p →
      p = r ∨ q = s)
    (hab : G.Adj a b) (hcd : G.Adj c d) (hya : G.Adj y a) (hyc : G.Adj y c)
    (hyb : y ≠ b) (hyd : y ≠ d) (hbd : ¬ G.Adj b d)
    (hL : ∀ z ∈ L, G.Adj y z)
    (hsound : ∀ X : Set V, (∃ z ∈ L, z ∈ X) →
      (a ∈ X ∨ d ∈ X) → (b ∈ X ∨ c ∈ X) → (b ∈ X ∨ d ∈ X) → HasEdge G X) :
    L ⊆ {a,c} := by
  intro z hz
  have he : HasEdge G {b,d,z} := hsound {b,d,z} ⟨z,hz,by simp⟩
    (Or.inr (by simp)) (Or.inl (by simp)) (Or.inl (by simp))
  rcases edge_in_triple G hbd he with hzb|hzd
  · have hza := ((h4 y a b z hya hab hzb.symm (hL z hz).symm).resolve_left hyb).symm
    exact Set.mem_insert_iff.mpr (Or.inl hza)
  · have hzc := ((h4 y c d z hyc hcd hzd.symm (hL z hz).symm).resolve_left hyd).symm
    exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr hzc))

def residual {V : Type*} (a b c d : V) (x : V → Bool) : Bool :=
  (x a || x d) && (x b || x c) && (x b || x d)

lemma enlarged_or_leaf_restriction {V : Type*} (G : SimpleGraph V) (L : Set V)
    (y a b c d : V)
    (h4 : ∀ p q r s, G.Adj p q → G.Adj q r → G.Adj r s → G.Adj s p →
      p = r ∨ q = s)
    (hab : G.Adj a b) (hcd : G.Adj c d) (hya : G.Adj y a) (hyc : G.Adj y c)
    (hyb : y ≠ b) (hyd : y ≠ d) (hbd : ¬ G.Adj b d)
    (hL : ∀ z ∈ L, G.Adj y z)
    (hsound : ∀ x : V → Bool, (∃ z ∈ L, x z = true) →
      (x y || residual a b c d x) = true →
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) :
    L ⊆ {a,c} := by
  classical
  apply leaf_restriction G L y a b c d h4 hab hcd hya hyc hyb hyd hbd hL
  intro X hXL had hbc hbd'
  let x : V → Bool := fun z => decide (z ∈ X)
  have hr : residual a b c d x = true := by
    simp only [residual,Bool.and_eq_true,Bool.or_eq_true,x,decide_eq_true_eq]
    exact ⟨⟨had,hbc⟩,hbd'⟩
  have hxL : ∃ z ∈ L, x z = true := by
    obtain ⟨z,hz,hzx⟩ := hXL
    exact ⟨z,hz,by simpa [x] using hzx⟩
  obtain ⟨u,v,he,hu,hv⟩ := hsound x hxL (by simp [hr])
  exact ⟨u,of_decide_eq_true hu,v,of_decide_eq_true hv,he⟩

lemma poison_nonedge_from_common_neighbor {V : Type*} (G : SimpleGraph V)
    (htri : ∀ p q r, G.Adj p q → G.Adj q r → ¬ G.Adj r p)
    {b d s : V} (hsb : G.Adj s b) (hsd : G.Adj s d) : ¬ G.Adj b d := by
  intro hbd
  exact htri s b d hsb hbd hsd.symm

end PEqualNP.Outside.L_meta_1031.AbsorberLeaves
