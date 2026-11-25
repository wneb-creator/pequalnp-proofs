import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4675.ClusterCharge
open PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover

lemma countUnion {α : Type*} [DecidableEq α] (support : ℕ → Finset α)
    (paid : Finset ℕ) (m : ℕ)
    (step : ∀ w < m, 1 < (support w).card → ∃ cs : Finset ℕ,
      cs ⊆ Finset.range w ∧ support w ⊆ cs.biUnion support ∧
      cs.card ≤ 1 + (if w ∈ paid then 1 else 0))
    (roots : Finset ℕ) (hr : roots ⊆ Finset.range m) :
    (roots.biUnion support).card ≤ roots.card + ((Finset.range m) ∩ paid).card := by
  classical
  induction m generalizing roots with
  | zero =>
    have : roots = ∅ := by simpa using hr
    simp [this]
  | succ m ih =>
    have old := ih (fun w hw => step w (by omega))
    have hpre : roots.erase m ⊆ Finset.range m := by
      intro w hw
      have ⟨hne, hmem⟩ := Finset.mem_erase.mp hw
      have hlt := Finset.mem_range.mp (hr hmem)
      exact Finset.mem_range.mpr (by omega)
    have hcost : ((Finset.range (m + 1)) ∩ paid).card =
        ((Finset.range m) ∩ paid).card + (if m ∈ paid then 1 else 0) := by
      by_cases h : m ∈ paid
      · have he : Finset.range (m + 1) ∩ paid = insert m (Finset.range m ∩ paid) := by
          ext w
          by_cases hw : w = m <;> simp [Finset.range_add_one, hw, h]
        simp [he, h]
      · have he : Finset.range (m + 1) ∩ paid = Finset.range m ∩ paid := by
          ext w
          by_cases hw : w = m <;> simp [Finset.range_add_one, hw, h]
        simp [he, h]
    rw [hcost]
    by_cases hm : m ∈ roots
    · have hrins := Finset.insert_erase hm
      have hroots : (roots.erase m).card + 1 = roots.card :=
        Finset.card_erase_add_one hm
      by_cases hb : 1 < (support m).card
      · obtain ⟨cs, hcpre, hcov, hcard⟩ := step m (by omega) hb
        have hsub : roots.biUnion support ⊆ ((roots.erase m) ∪ cs).biUnion support := by
          intro a ha
          obtain ⟨w, hw, haw⟩ := Finset.mem_biUnion.mp ha
          by_cases heq : w = m
          · subst w
            obtain ⟨v, hv, hav⟩ := Finset.mem_biUnion.mp (hcov haw)
            exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_union_right _ hv, hav⟩
          · exact Finset.mem_biUnion.mpr
              ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨heq, hw⟩), haw⟩
        have hh := old ((roots.erase m) ∪ cs) (Finset.union_subset hpre hcpre)
        have hh' := Finset.card_le_card hsub
        have hu := Finset.card_union_le (roots.erase m) cs
        omega
      · have hh := old (roots.erase m) hpre
        have he : roots.biUnion support = support m ∪ (roots.erase m).biUnion support := by
          conv_lhs => rw [← hrins]
          rw [Finset.biUnion_insert]
        rw [he]
        have hu := Finset.card_union_le (support m) ((roots.erase m).biUnion support)
        omega
    · rw [Finset.erase_eq_of_notMem hm] at hpre
      have hh := old roots hpre
      omega

lemma dag_union_bound {α : Type*} [DecidableEq α] (f : ℕ → Finset α) (R B : Finset ℕ)
    (step : ∀ i, 1 < (f i).card → (∃ a < i, f i ⊆ f a) ∨
      (i ∈ B ∧ ∃ a < i, ∃ b < i, f i ⊆ f a ∪ f b)) :
    (R.biUnion f).card ≤ R.card + B.card := by
  classical
  let m := R.sup id + 1
  have hr : R ⊆ Finset.range m := by
    intro w hw
    have h : w ≤ R.sup id := Finset.le_sup (f := id) hw
    exact Finset.mem_range.mpr (by dsimp [m]; omega)
  have haux : (R.biUnion f).card ≤ R.card + (Finset.range m ∩ B).card := by
    apply countUnion f B m _ R hr
    intro i _ hi
    rcases step i hi with ⟨a, ha, hsub⟩ | ⟨hiB, a, ha, b, hb, hsub⟩
    · refine ⟨{a}, ?_, ?_, ?_⟩
      · simpa using ha
      · simpa using hsub
      · simp
    · refine ⟨{a,b}, ?_, ?_, ?_⟩
      · intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact Finset.mem_range.mpr ha
        · rw [Finset.mem_singleton.mp hw]
          exact Finset.mem_range.mpr hb
      · simpa using hsub
      · simp only [hiB, ite_true]
        exact Finset.card_le_two
  have hl := Finset.card_le_card (Finset.inter_subset_right (s₁ := Finset.range m) (s₂ := B))
  omega

lemma hit_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (a : Fin n) (Z S : Finset (Fin n))
    (ha : a ∉ S) (hcentres : ∀ z∈Z, G.Adj a z)
    (hhit : ∀ z∈Z, ∃ u∈S, G.Adj z u) : Z.card ≤ S.card := by
  classical
  let f : Fin n → Fin n := fun z => if hz : z∈Z then (hhit z hz).choose else a
  have hf (z : Fin n) (hz : z∈Z) : f z∈S ∧ G.Adj z (f z) := by
    simp only [f,hz,dif_pos]
    exact (hhit z hz).choose_spec
  apply Finset.card_le_card_of_injOn f
  · intro z hz
    exact (hf z hz).1
  · intro z hz z' hz' heq
    by_contra hzz
    have hau : a ≠ f z := by intro he; exact ha (he ▸ (hf z hz).1)
    have hsub : ({z,z'} : Finset (Fin n)) ⊆
        Finset.univ.filter (fun w => G.Adj a w ∧ G.Adj (f z) w) := by
      intro w hw
      simp only [Finset.mem_insert,Finset.mem_singleton] at hw
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      rcases hw with hw | hw
      · subst w
        exact ⟨hcentres z hz,(hf z hz).2.symm⟩
      · subst w
        exact ⟨hcentres z' hz',by rw [heq]; exact (hf z' hz').2.symm⟩
    have hc := (Finset.card_le_card hsub).trans (h4 a (f z) hau)
    rw [Finset.card_pair hzz] at hc
    omega

lemma extension_neighbour {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → Bool) (hno : graphFun G ∅ x = false) (z : Fin n)
    (hext : graphFun G ∅ (Function.update x z true) = true) :
    ∃ u, x u = true ∧ G.Adj z u := by
  have hf : ∃ u v, G.Adj u v ∧ Function.update x z true u = true ∧
      Function.update x z true v = true := by simpa [graphFun] using hext
  obtain ⟨u,v,huv,hu,hv⟩ := hf
  by_cases huz : u=z
  · subst u
    have hvz : v≠z := G.ne_of_adj huv.symm
    rw [Function.update_of_ne hvz] at hv
    exact ⟨v,hv,huv⟩
  · rw [Function.update_of_ne huz] at hu
    by_cases hvz : v=z
    · subst v
      exact ⟨u,hu,huv.symm⟩
    · rw [Function.update_of_ne hvz] at hv
      have hyes : graphFun G ∅ x = true := by
        simp only [graphFun,Bool.or_eq_true,decide_eq_true_eq]
        exact Or.inr ⟨u,v,huv,hu,hv⟩
      rw [hno] at hyes
      cases hyes


lemma common_witness_cluster_charge {n : ℕ} {ι : Type*} [DecidableEq ι]
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (h4 : NoFourCycle G)
    (a : Fin n) (H : Finset ι) (Z : ι → Finset (Fin n))
    (f : ι → (Fin n → Bool) → Bool) (r : ι → ℕ)
    (hcentres : ∀ h ∈ H, ∀ z ∈ Z h, G.Adj a z)
    (hmono : ∀ h ∈ H, ∀ x y, (∀ u, x u = true → y u = true) → f h x = true → f h y = true)
    (hclean : ∀ h ∈ H, ∀ z ∈ Z h, ∀ y, f h y = true → y z = true → graphFun G ∅ y = true)
    (x : Fin n → Bool) (ha : x a = false) (hno : graphFun G ∅ x = false)
    (T : ℕ → Finset (Fin n)) (B : Finset ℕ)
    (hstep : ∀ i, 1 < (T i).card → (∃ j < i, T i ⊆ T j) ∨
      (i ∈ B ∧ ∃ j < i, ∃ k < i, T i ⊆ T j ∪ T k))
    (hsub : ∀ h ∈ H, ∀ u ∈ T (r h), x u = true)
    (htrace : ∀ h ∈ H, f h (fun u => decide (u ∈ T (r h))) = true) :
    (H.biUnion Z).card ≤ (H.image r).card + B.card := by
  classical
  let S := (H.image r).biUnion T
  have haS : a ∉ S := by
    intro ham
    obtain ⟨w, hw, haw⟩ := Finset.mem_biUnion.mp ham
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hw
    have he := hsub h hh a haw
    rw [ha] at he
    cases he
  have hhit : ∀ z ∈ H.biUnion Z, ∃ u ∈ S, G.Adj z u := by
    intro z hz
    obtain ⟨h, hh, hzh⟩ := Finset.mem_biUnion.mp hz
    let y : Fin n → Bool := fun u => decide (u ∈ T (r h))
    have hyno : graphFun G ∅ y = false := by
      cases he : graphFun G ∅ y
      · rfl
      · obtain ⟨u,v,huv,hu,hv⟩ : ∃ u v, G.Adj u v ∧ y u = true ∧ y v = true := by
          simpa [graphFun] using he
        have hyes : graphFun G ∅ x = true := by
          simp only [graphFun, Bool.or_eq_true, decide_eq_true_eq]
          exact Or.inr ⟨u, v, huv, hsub h hh u (of_decide_eq_true hu),
            hsub h hh v (of_decide_eq_true hv)⟩
        rw [hno] at hyes
        cases hyes
    have hle : ∀ u, y u = true → Function.update y z true u = true := by
      intro u hu
      by_cases huz : u = z
      · subst u; simp
      · rw [Function.update_of_ne huz]; exact hu
    have hext := hclean h hh z hzh (Function.update y z true)
      (hmono h hh y _ hle (htrace h hh)) (by simp)
    obtain ⟨u, hu, hzu⟩ := extension_neighbour G y hyno z hext
    refine ⟨u, Finset.mem_biUnion.mpr ⟨r h, Finset.mem_image.mpr ⟨h, hh, rfl⟩,
      of_decide_eq_true hu⟩, hzu⟩
  have hcent : (H.biUnion Z).card ≤ S.card := by
    apply hit_bound G h4 a (H.biUnion Z) S haS ?_ hhit
    intro z hz
    obtain ⟨h, hh, hzh⟩ := Finset.mem_biUnion.mp hz
    exact hcentres h hh z hzh
  exact hcent.trans (dag_union_bound T (H.image r) B hstep)

end PEqualNP.Outside.L_meta_4675.ClusterCharge
