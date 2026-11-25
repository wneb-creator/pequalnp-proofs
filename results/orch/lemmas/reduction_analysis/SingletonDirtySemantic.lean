import Mathlib

namespace PEqualNP.Outside.L_meta_650

def setHits {α : Type*} (S : Finset α) (x : α → Bool) : Prop :=
  ∃ v ∈ S, x v = true

lemma setHits_mono {α : Type*} (S : Finset α) (x y : α → Bool)
    (hxy : ∀ v, x v = true → y v = true) : setHits S x → setHits S y := by
  rintro ⟨v, hv, hx⟩
  exact ⟨v, hv, hxy v hx⟩

lemma setHits_pair {α : Type*} [DecidableEq α] (S : Finset α) (u v : α) :
    setHits S (fun w => decide (w = u ∨ w = v)) ↔ u ∈ S ∨ v ∈ S := by
  simp only [setHits, decide_eq_true_eq]
  constructor
  · rintro ⟨w, hw, rfl | rfl⟩
    · exact Or.inl hw
    · exact Or.inr hw
  · rintro (hu | hv)
    · exact ⟨u, hu, Or.inl rfl⟩
    · exact ⟨v, hv, Or.inr rfl⟩

/-- The singleton-support case of eliminating one unsafe AND gate.
The remaining circuit is represented by its monotone predicate H. The union W
of the later filters avoids both operand supports P and Q. No claim about a
circuit size or the availability of this normal form is assumed or concluded. -/
theorem singleton_dirty_semantic {α : Type*} [DecidableEq α]
    (E : α → α → Prop) (H : (α → Bool) → Prop)
    (P Q W : Finset α) (c : α)
    (hcP : c ∈ P) (hcQ : c ∈ Q)
    (common : ∀ a, a ∈ P → a ∈ Q → a = c)
    (disP : Disjoint W P) (disQ : Disjoint W Q)
    (monoH : ∀ x y, (∀ v, x v = true → y v = true) → H x → H y)
    (computes : ∀ x, (H x ∨ setHits P x ∧ setHits Q x ∧ setHits W x) ↔
      ∃ u v, E u v ∧ x u = true ∧ x v = true) :
    ∀ x, (H x ∨ x c = true ∧ setHits W x) ↔
      ∃ u v, E u v ∧ x u = true ∧ x v = true := by
  intro x
  constructor
  · intro hx
    apply (computes x).mp
    rcases hx with hH | ⟨hc, hW⟩
    · exact Or.inl hH
    · exact Or.inr ⟨⟨c, hcP, hc⟩, ⟨c, hcQ, hc⟩, hW⟩
  · rintro ⟨u, v, huv, hxu, hxv⟩
    let y : α → Bool := fun w => decide (w = u ∨ w = v)
    have hyx : ∀ w, y w = true → x w = true := by
      intro w hw
      change decide (w = u ∨ w = v) = true at hw
      rcases of_decide_eq_true hw with rfl | rfl
      · exact hxu
      · exact hxv
    have hy : H y ∨ setHits P y ∧ setHits Q y ∧ setHits W y :=
      (computes y).mpr ⟨u, v, huv, by simp [y], by simp [y]⟩
    rcases hy with hH | ⟨hP, hQ, hW⟩
    · exact Or.inl (monoH y x hyx hH)
    · apply Or.inr
      refine ⟨?_, setHits_mono W y x hyx hW⟩
      have hP' := (setHits_pair P u v).mp hP
      have hQ' := (setHits_pair Q u v).mp hQ
      have hW' := (setHits_pair W u v).mp hW
      rcases hW' with huW | hvW
      · have huP : u ∉ P := fun h => Finset.disjoint_left.mp disP huW h
        have huQ : u ∉ Q := fun h => Finset.disjoint_left.mp disQ huW h
        have hvP := hP'.resolve_left huP
        have hvQ := hQ'.resolve_left huQ
        rw [← common v hvP hvQ]
        exact hxv
      · have hvP : v ∉ P := fun h => Finset.disjoint_left.mp disP hvW h
        have hvQ : v ∉ Q := fun h => Finset.disjoint_left.mp disQ hvW h
        have huP := hP'.resolve_right hvP
        have huQ := hQ'.resolve_right hvQ
        rw [← common u huP huQ]
        exact hxu

end PEqualNP.Outside.L_meta_650
