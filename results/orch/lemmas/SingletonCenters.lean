import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5349_aux

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover

def singletonSupport (n : ℕ) (C : Circuit) (g : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun v => gateVal n C g (pairInput v v) = true

lemma graphFun_pair_true {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v : Fin n) : graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq, pairInput]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  · intro h
    exact ⟨u, v, h, by simp, by simp⟩

lemma wmax_singleton_adj {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g : ℕ)
    (hmono : ∀ (x y : Fin n → Bool), (∀ v, x v = true → y v = true) →
      gateVal n C g x = true → gateVal n C g y = true)
    {u v : Fin n} (hu : u ∈ wmax G C g) (hv : v ∈ singletonSupport n C g) :
    G.Adj u v := by
  have hvv : gateVal n C g (pairInput v v) = true := (Finset.mem_filter.mp hv).2
  have huv : gateVal n C g (pairInput u v) = true := hmono _ _ (by
    intro w hw
    simp only [pairInput, decide_eq_true_eq] at hw ⊢
    exact Or.inr (hw.elim id id)) hvv
  apply (graphFun_pair_true G u v).mp
  exact (Finset.mem_filter.mp hu).2 _ huv (by simp [pairInput])

lemma same_singleton_center_unique {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (g h : ℕ) (h4 : NoFourCycle G)
    (mg : ∀ (x y : Fin n → Bool), (∀ v, x v = true → y v = true) →
      gateVal n C g x = true → gateVal n C g y = true)
    (mh : ∀ (x y : Fin n → Bool), (∀ v, x v = true → y v = true) →
      gateVal n C h x = true → gateVal n C h y = true)
    {u u' v c : Fin n} (hu : u ∈ wmax G C g) (hu' : u' ∈ wmax G C h)
    (hcg : c ∈ singletonSupport n C g) (hch : c ∈ singletonSupport n C h)
    (huv : G.Adj u v) (huv' : G.Adj u' v) (hcv : c ≠ v) : u = u' := by
  by_contra hne
  have hac := wmax_singleton_adj G C g mg hu hcg
  have hbc := wmax_singleton_adj G C h mh hu' hch
  have hsub : ({c,v} : Finset (Fin n)) ⊆
      Finset.univ.filter (fun x => G.Adj u x ∧ G.Adj u' x) := by
    intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hac,hbc⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,huv,huv'⟩
  have hcard := Finset.card_le_card hsub
  have hlim := h4 u u' hne
  have htwo : ({c,v} : Finset (Fin n)).card = 2 := by simp [hcv]
  rw [htwo] at hcard
  omega

end PEqualNP.Outside.L_meta_5349_aux
