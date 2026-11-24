import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1477.ClauseAntichain

open PEqualNP.TopForm

def neighbors {n r : ℕ} (Q : Finset (Fin n)) (A : Fin r → Finset (Fin n))
    (p : Fin n) : Finset (Fin n) :=
  Q.filter fun q => ∀ i, p ∈ A i ∨ q ∈ A i

def signature {n r : ℕ} (A : Fin r → Finset (Fin n)) (p : Fin n) : Finset (Fin r) :=
  Finset.univ.filter fun i => p ∈ A i

lemma signature_mono_neighbors {n r : ℕ} (Q : Finset (Fin n))
    (A : Fin r → Finset (Fin n)) (p q : Fin n)
    (h : signature A p ⊆ signature A q) : neighbors Q A p ⊆ neighbors Q A q := by
  intro u hu
  obtain ⟨huQ, huA⟩ := Finset.mem_filter.mp hu
  refine Finset.mem_filter.mpr ⟨huQ, ?_⟩
  intro i
  rcases huA i with hp | hu
  · left
    have hi : i ∈ signature A p := by simp [signature, hp]
    simpa [signature] using h hi
  · exact Or.inr hu

lemma heavy_signature_eq {n r : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (P Q : Finset (Fin n)) (A : Fin r → Finset (Fin n))
    (hcross : ∀ p ∈ P, ∀ q ∈ neighbors Q A p, G.Adj p q)
    (p q : Fin n) (hp : p ∈ P) (hq : q ∈ P)
    (hheavy : 2 ≤ (neighbors Q A p).card)
    (hsig : signature A p ⊆ signature A q) : p = q := by
  by_contra hne
  have hsub : neighbors Q A p ⊆
      Finset.univ.filter (fun u => G.Adj p u ∧ G.Adj q u) := by
    intro u hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcross p hp u hu,
      hcross q hq u (signature_mono_neighbors Q A p q hsig hu)⟩
  have hsmall := (Finset.card_le_card hsub).trans (hG p q hne)
  omega

lemma heavy_card_bound {n r : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (P Q : Finset (Fin n)) (A : Fin r → Finset (Fin n))
    (hcross : ∀ p ∈ P, ∀ q ∈ neighbors Q A p, G.Adj p q) :
    (P.filter fun p => 2 ≤ (neighbors Q A p).card).card ≤ r.choose (r / 2) := by
  classical
  let H := P.filter fun p => 2 ≤ (neighbors Q A p).card
  have heq : ∀ p ∈ H, ∀ q ∈ H, signature A p ⊆ signature A q → p = q := by
    intro p hp q hq hsub
    exact heavy_signature_eq G hG P Q A hcross p q
      (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hq).1
      (Finset.mem_filter.mp hp).2 hsub
  have hinj : Set.InjOn (signature A) (H : Set (Fin n)) := by
    intro p hp q hq he
    exact heq p hp q hq (by rw [he])
  have hac : IsAntichain (fun s t : Finset (Fin r) => s ⊆ t)
      ((H.image (signature A)) : Set (Finset (Fin r))) := by
    intro s hs t ht hne hsub
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ht
    exact hne (congrArg (signature A) (heq p hp q hq hsub))
  have hbound := hac.sperner
  rw [Finset.card_image_of_injOn hinj] at hbound
  simpa only [Fintype.card_fin] using hbound

lemma three_filter_heavy_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (P Q : Finset (Fin n)) (A : Fin 3 → Finset (Fin n))
    (hcross : ∀ p ∈ P, ∀ q ∈ neighbors Q A p, G.Adj p q) :
    (P.filter fun p => 2 ≤ (neighbors Q A p).card).card ≤ 3 := by
  simpa using heavy_card_bound G hG P Q A hcross

end PEqualNP.Outside.L_meta_1477.ClauseAntichain

namespace PEqualNP.Outside.L_meta_1477.ClauseCycleBudget

open PEqualNP.TopForm ClauseAntichain

lemma sparse_family_sum {α β : Type*} [DecidableEq α] [DecidableEq β]
    (H : Finset α) (N : α → Finset β)
    (hpair : ∀ a ∈ H, ∀ b ∈ H, a ≠ b → (N a ∩ N b).card ≤ 1) :
    (∑ a ∈ H, (N a).card) ≤ (H.biUnion N).card + H.card.choose 2 := by
  induction H using Finset.induction_on with
  | empty => simp
  | @insert a H ha ih =>
    have hp : ∀ b ∈ H, (N a ∩ N b).card ≤ 1 := by
      intro b hb
      exact hpair a (by simp) b (Finset.mem_insert_of_mem hb) (by
        intro h
        exact ha (h.symm ▸ hb))
    have hrest := ih (fun b hb c hc hbc =>
      hpair b (Finset.mem_insert_of_mem hb) c (Finset.mem_insert_of_mem hc) hbc)
    have he : N a ∩ H.biUnion N = H.biUnion (fun b => N a ∩ N b) := by
      ext q
      simp only [Finset.mem_inter, Finset.mem_biUnion]
      aesop
    have hi : (N a ∩ H.biUnion N).card ≤ H.card := by
      rw [he]
      calc
        _ ≤ ∑ b ∈ H, (N a ∩ N b).card := Finset.card_biUnion_le
        _ ≤ ∑ b ∈ H, 1 := Finset.sum_le_sum hp
        _ = H.card := by simp
    have hu := Finset.card_union_add_card_inter (N a) (H.biUnion N)
    rw [Finset.sum_insert ha, Finset.biUnion_insert, Finset.card_insert_of_notMem ha,
      Nat.choose_succ_succ]
    simp only [Nat.choose_one_right]
    norm_num only at *
    omega

lemma row_edge_budget {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (P Q : Finset (Fin n)) (N : Fin n → Finset (Fin n))
    (hsub : ∀ p ∈ P, N p ⊆ Q)
    (hAdj : ∀ p ∈ P, ∀ q ∈ N p, G.Adj p q) :
    let H := P.filter fun p => 2 ≤ (N p).card
    (∑ p ∈ P, (N p).card) + H.card ≤ P.card + Q.card + H.card.choose 2 := by
  classical
  intro H
  have hHP : H ⊆ P := Finset.filter_subset _ _
  have hpairs : ∀ a ∈ H, ∀ b ∈ H, a ≠ b → (N a ∩ N b).card ≤ 1 := by
    intro a ha b hb hne
    have hinc : N a ∩ N b ⊆ Finset.univ.filter (fun q => G.Adj a q ∧ G.Adj b q) := by
      intro q hq
      obtain ⟨haq, hbq⟩ := Finset.mem_inter.mp hq
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hAdj a (hHP ha) q haq,
        hAdj b (hHP hb) q hbq⟩
    exact (Finset.card_le_card hinc).trans (hG a b hne)
  have hheavy := sparse_family_sum H N hpairs
  have hunion : H.biUnion N ⊆ Q := by
    intro q hq
    obtain ⟨p, hp, hqp⟩ := Finset.mem_biUnion.mp hq
    exact hsub p (hHP hp) hqp
  have hu := Finset.card_le_card hunion
  have hlight : (∑ p ∈ P \ H, (N p).card) ≤ (P \ H).card := by
    calc
      _ ≤ ∑ p ∈ P \ H, 1 := by
        apply Finset.sum_le_sum
        intro p hp
        obtain ⟨hpP, hpH⟩ := Finset.mem_sdiff.mp hp
        have hn : ¬ 2 ≤ (N p).card := by
          intro hn
          exact hpH (Finset.mem_filter.mpr ⟨hpP, hn⟩)
        omega
      _ = _ := by simp
  have hs := Finset.sum_sdiff (f := fun p => (N p).card) hHP
  have hc := Finset.card_sdiff_add_card_eq_card hHP
  omega

lemma three_heavy_edge_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (P Q : Finset (Fin n)) (N : Fin n → Finset (Fin n))
    (hsub : ∀ p ∈ P, N p ⊆ Q)
    (hAdj : ∀ p ∈ P, ∀ q ∈ N p, G.Adj p q)
    (hheavy : (P.filter fun p => 2 ≤ (N p).card).card ≤ 3) :
    (∑ p ∈ P, (N p).card) ≤ P.card + Q.card := by
  have hbound := row_edge_budget G hG P Q N hsub hAdj
  dsimp only at hbound
  have hchoose : (P.filter fun p => 2 ≤ (N p).card).card.choose 2 ≤
      (P.filter fun p => 2 ≤ (N p).card).card := by
    have h := hheavy
    generalize hk : (P.filter fun p => 2 ≤ (N p).card).card = k at h ⊢
    interval_cases k <;> decide
  omega

lemma three_filter_edge_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (P Q : Finset (Fin n)) (A : Fin 3 → Finset (Fin n))
    (hcross : ∀ p ∈ P, ∀ q ∈ neighbors Q A p, G.Adj p q) :
    (∑ p ∈ P, (neighbors Q A p).card) ≤ P.card + Q.card := by
  exact three_heavy_edge_bound G hG P Q (neighbors Q A)
    (fun _ _ => Finset.filter_subset _ _) hcross (three_filter_heavy_card G hG P Q A hcross)

end PEqualNP.Outside.L_meta_1477.ClauseCycleBudget
