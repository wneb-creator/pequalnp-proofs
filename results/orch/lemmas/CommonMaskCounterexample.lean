import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1477.StructuralMasks

def orValue {n : ℕ} (A : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∃ a ∈ A, x a = true)

def productValue {n : ℕ} (A B : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  orValue A x && orValue B x

def CleanMask {n : ℕ} (G : SimpleGraph (Fin n)) (A B : Finset (Fin n))
    (c : Fin n) : Prop :=
  ∀ x : Fin n → Bool, productValue A B x = true → x c = true →
    ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true

def EffectiveMask {n : ℕ} (G : SimpleGraph (Fin n)) (A B : Finset (Fin n))
    (c : Fin n) : Prop :=
  ∃ u v : Fin n, G.Adj u v ∧
    productValue A B (PEqualNP.EdgeOwnership.pairInput u v) = true ∧
    PEqualNP.EdgeOwnership.pairInput u v c = true

lemma graph_pair_iff {n : ℕ} (G : SimpleGraph (Fin n)) (c d : Fin n) :
    (∃ u v : Fin n, G.Adj u v ∧ PEqualNP.EdgeOwnership.pairInput c d u = true ∧
      PEqualNP.EdgeOwnership.pairInput c d v = true) ↔ G.Adj c d := by
  constructor
  · rintro ⟨u, v, huv, hu, hv⟩
    simp only [PEqualNP.EdgeOwnership.pairInput, decide_eq_true_eq] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact (G.loopless.irrefl _ huv).elim
    · exact huv
    · exact huv.symm
    · exact (G.loopless.irrefl _ huv).elim
  · intro h
    exact ⟨c, d, h, by simp [PEqualNP.EdgeOwnership.pairInput],
      by simp [PEqualNP.EdgeOwnership.pairInput]⟩

lemma cleanMask_of_mem_left_iff {n : ℕ} (G : SimpleGraph (Fin n))
    (A B : Finset (Fin n)) (c : Fin n) (hc : c ∈ A) :
    CleanMask G A B c ↔ ∀ b ∈ B, G.Adj c b := by
  constructor
  · intro h b hb
    apply (graph_pair_iff G c b).mp
    apply h (PEqualNP.EdgeOwnership.pairInput c b)
    · simp only [productValue, Bool.and_eq_true, orValue, decide_eq_true_eq]
      exact ⟨⟨c, hc, by simp [PEqualNP.EdgeOwnership.pairInput]⟩,
        ⟨b, hb, by simp [PEqualNP.EdgeOwnership.pairInput]⟩⟩
    · simp [PEqualNP.EdgeOwnership.pairInput]
  · intro h x hx hxc
    simp only [productValue, Bool.and_eq_true, orValue, decide_eq_true_eq] at hx
    obtain ⟨b, hb, hxb⟩ := hx.2
    exact ⟨c, b, h b hb, hxc, hxb⟩

lemma cleanMask_of_mem_right_iff {n : ℕ} (G : SimpleGraph (Fin n))
    (A B : Finset (Fin n)) (c : Fin n) (hc : c ∈ B) :
    CleanMask G A B c ↔ ∀ a ∈ A, G.Adj a c := by
  have hs : CleanMask G A B c ↔ CleanMask G B A c := by
    simp only [CleanMask, productValue, Bool.and_comm]
  rw [hs, cleanMask_of_mem_left_iff G B A c hc]
  exact forall₂_congr fun a _ => G.adj_comm c a

lemma cleanMask_adj_overlap {n : ℕ} (G : SimpleGraph (Fin n))
    (A B : Finset (Fin n)) (c : Fin n) (hc : CleanMask G A B c)
    (z : Fin n) (hz : z ∈ A ∩ B) : G.Adj c z := by
  apply (graph_pair_iff G c z).mp
  apply hc (PEqualNP.EdgeOwnership.pairInput c z)
  · simp only [productValue, Bool.and_eq_true, orValue, decide_eq_true_eq]
    exact ⟨⟨z, (Finset.mem_inter.mp hz).1, by simp [PEqualNP.EdgeOwnership.pairInput]⟩,
      ⟨z, (Finset.mem_inter.mp hz).2, by simp [PEqualNP.EdgeOwnership.pairInput]⟩⟩
  · simp [PEqualNP.EdgeOwnership.pairInput]

lemma effectiveMask_mem_union {n : ℕ} (G : SimpleGraph (Fin n))
    (A B : Finset (Fin n)) (hdis : Disjoint A B) (c : Fin n)
    (hc : EffectiveMask G A B c) : c ∈ A ∪ B := by
  obtain ⟨u, v, _, hprod, hmask⟩ := hc
  simp only [productValue, Bool.and_eq_true, orValue, decide_eq_true_eq] at hprod
  obtain ⟨a, ha, hpa⟩ := hprod.1
  obtain ⟨b, hb, hpb⟩ := hprod.2
  simp only [PEqualNP.EdgeOwnership.pairInput, decide_eq_true_eq] at hpa hpb hmask
  by_contra hnot
  have hca : c ∉ A := fun h => hnot (Finset.mem_union_left _ h)
  have hcb : c ∉ B := fun h => hnot (Finset.mem_union_right _ h)
  have hab : a ≠ b := fun h => (Finset.disjoint_left.mp hdis ha) (h ▸ hb)
  rcases hmask with rfl | rfl <;>
    rcases hpa with rfl | rfl <;> rcases hpb with rfl | rfl <;> contradiction

end PEqualNP.Outside.L_meta_1477.StructuralMasks
namespace PEqualNP.Outside.L_meta_1477.CommonMaskCounterexample

open StructuralMasks

def graphEdges : Finset (Sym2 (Fin 6)) :=
  {s(0, 3), s(0, 4), s(1, 3), s(1, 5), s(2, 5), s(2, 4)}

def resultEdges : Finset (Sym2 (Fin 6)) :=
  {s(0, 3), s(0, 4), s(1, 3), s(2, 5), s(2, 4)}

def graph : SimpleGraph (Fin 6) where
  Adj u v := s(u, v) ∈ graphEdges
  symm := ⟨by intro u v h; simpa only [Sym2.eq_swap] using h⟩
  loopless := ⟨by intro u; fin_cases u <;> decide⟩

def left₀ : Finset (Fin 6) := {0, 1}
def right₀ : Finset (Fin 6) := {3, 4}
def left₁ : Finset (Fin 6) := {2, 1}
def right₁ : Finset (Fin 6) := {5, 4}
def masks : Finset (Fin 6) := {0, 3, 2}

def resultValue (x : Fin 6 → Bool) : Bool :=
  (productValue left₀ right₀ x || productValue left₁ right₁ x) && orValue masks x

lemma common_masks : ∀ q ∈ masks,
    CleanMask graph left₀ right₀ q ∧ CleanMask graph left₁ right₁ q := by
  intro q hq
  have hq : q = 0 ∨ q = 3 ∨ q = 2 := by simpa [masks] using hq
  rcases hq with rfl | rfl | rfl <;> constructor <;> dsimp only [CleanMask, graph] <;> decide

lemma both_dirty :
    productValue left₀ right₀ (PEqualNP.EdgeOwnership.pairInput 1 4) = true ∧
      productValue left₁ right₁ (PEqualNP.EdgeOwnership.pairInput 1 4) = true ∧ ¬ graph.Adj 1 4 := by
  unfold graph
  decide

lemma no_four_cycle_card : ∀ c q : Fin 6, c ≠ q →
    (Finset.univ.filter (fun v => s(c, v) ∈ graphEdges ∧ s(q, v) ∈ graphEdges)).card ≤ 1 := by decide

lemma exact_pair_shadow : ∀ u v : Fin 6,
    resultValue (PEqualNP.EdgeOwnership.pairInput u v) = decide (s(u, v) ∈ resultEdges) := by decide

lemma result_below_graph : ∀ x : Fin 6 → Bool, resultValue x = true →
    ∃ u v : Fin 6, s(u, v) ∈ graphEdges ∧ x u = true ∧ x v = true := by decide

lemma cover_not_two : ¬ ∃ T : Finset (Fin 6), T.card ≤ 2 ∧
    ∀ e ∈ resultEdges, ∃ v ∈ T, v ∈ e := by decide

end PEqualNP.Outside.L_meta_1477.CommonMaskCounterexample
