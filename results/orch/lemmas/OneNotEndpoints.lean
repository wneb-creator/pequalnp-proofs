import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux.OneNot

abbrev Point (n : ℕ) := Fin n → Bool

def Below {n : ℕ} (x y : Point n) : Prop := ∀ i, x i = true → y i = true

def Increasing {n : ℕ} (h : Point n → Bool) : Prop :=
  ∀ x y, Below x y → h x = true → h y = true

lemma increasing_endpoints {n : ℕ} (h : Point n → Bool) (mono : Increasing h)
    (someTrue : ∃ x, h x = true) (someFalse : ∃ x, h x = false) :
    h (fun _ => false) = false ∧ h (fun _ => true) = true := by
  obtain ⟨a, ha⟩ := someTrue
  obtain ⟨b, hb⟩ := someFalse
  constructor
  · cases hz : h (fun _ => false)
    · rfl
    · have bad := mono (fun _ => false) b (by intro i hi; cases hi) hz
      rw [hb] at bad
      cases bad
  · exact mono a (fun _ => true) (by intro i hi; rfl) ha

lemma not_output {n : ℕ} (h f : Point n → Bool)
    (hzero : h (fun _ => false) = false) (fzero : f (fun _ => false) = false) :
    ¬∀ x, f x = !(h x) := by
  intro same
  have bad := same (fun _ => false)
  simp [hzero, fzero] at bad

lemma not_and_output {n : ℕ} (h q f : Point n → Bool)
    (hone : h (fun _ => true) = true) (fone : f (fun _ => true) = true) :
    ¬∀ x, f x = (!(h x) && q x) := by
  intro same
  have bad := same (fun _ => true)
  simp [hone, fone] at bad

lemma not_or_output {n : ℕ} (h q f : Point n → Bool)
    (hzero : h (fun _ => false) = false) (fzero : f (fun _ => false) = false) :
    ¬∀ x, f x = (!(h x) || q x) := by
  intro same
  have bad := same (fun _ => false)
  simp [hzero, fzero] at bad

def Hits {n : ℕ} (S A : Finset (Fin n)) : Prop := ∃ i ∈ S, i ∈ A

lemma hits_singleton {n : ℕ} (S : Finset (Fin n)) (i : Fin n) :
    Hits S {i} ↔ i ∈ S := by
  simp [Hits]

lemma masked_or_new {n : ℕ} (H W R S : Finset (Fin n))
    (same : ∀ A, ((Hits W A ∧ ¬Hits H A) ∨ Hits R A) ↔ Hits S A)
    (fresh : ¬ S ⊆ R) : H ⊆ R ∧ S = W ∪ R := by
  classical
  have single (i : Fin n) : ((i ∈ W ∧ i ∉ H) ∨ i ∈ R) ↔ i ∈ S := by
    simpa only [hits_singleton] using same {i}
  obtain ⟨j, hjS, hjR⟩ : ∃ j, j ∈ S ∧ j ∉ R := by
    simpa only [Finset.subset_iff, not_forall, not_imp, exists_prop] using fresh
  obtain ⟨hjW, hjH⟩ := (single j).mpr hjS |>.resolve_right hjR
  have hr : H ⊆ R := by
    intro h hh
    by_contra hn
    have hs : Hits S {j, h} := ⟨j, hjS, by simp⟩
    rcases (same {j, h}).mpr hs with ⟨_, noH⟩ | inR
    · exact noH ⟨h, hh, by simp⟩
    · obtain ⟨i, hi, he⟩ := inR
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl
      · exact hjR hi
      · exact hn hi
  refine ⟨hr, ?_⟩
  ext i
  constructor
  · intro hi
    rcases (single i).mpr hi with h | h
    · exact Finset.mem_union_left _ h.1
    · exact Finset.mem_union_right _ h
  · intro hi
    apply (single i).mp
    rcases Finset.mem_union.mp hi with hw | hr'
    · by_cases hh : i ∈ H
      · exact Or.inr (hr hh)
      · exact Or.inl ⟨hw, hh⟩
    · exact Or.inr hr'

lemma masked_and_subset {n : ℕ} (H W R S : Finset (Fin n))
    (same : ∀ A, ((Hits W A ∨ ¬Hits H A) ∧ Hits R A) ↔ Hits S A) :
    S ⊆ R := by
  intro i hi
  have h := (same {i}).mpr ((hits_singleton S i).mpr hi)
  exact (hits_singleton R i).mp h.2

lemma masked_or_no_triple {n : ℕ} (H W R S : Finset (Fin n))
    (triple : 3 ≤ S.card)
    (smallW : W ⊆ S → W.card ≤ 1)
    (smallR : R ⊆ S → R.card ≤ 1) :
    ¬∀ A, ((Hits W A ∧ ¬Hits H A) ∨ Hits R A) ↔ Hits S A := by
  classical
  intro same
  have rs : R ⊆ S := by
    intro i hi
    apply (hits_singleton S i).mp
    exact (same {i}).mp (Or.inr ((hits_singleton R i).mpr hi))
  have rsmall := smallR rs
  have fresh : ¬ S ⊆ R := by
    intro sub
    have := Finset.card_le_card sub
    omega
  obtain ⟨_, equal⟩ := masked_or_new H W R S same fresh
  have ws : W ⊆ S := by rw [equal]; exact Finset.subset_union_left
  have wsmall := smallW ws
  have bound := Finset.card_union_le W R
  rw [← equal] at bound
  omega

lemma masked_and_no_triple {n : ℕ} (H W R S : Finset (Fin n))
    (notAbove : ¬ S ⊆ R) :
    ¬∀ A, ((Hits W A ∨ ¬Hits H A) ∧ Hits R A) ↔ Hits S A := by
  intro same
  exact notAbove (masked_and_subset H W R S same)

end PEqualNP.Outside.L_meta_2592_aux.OneNot
