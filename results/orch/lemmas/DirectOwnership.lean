import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1031.DirectOwnership

def MonoBool {n : ℕ} (F : (Fin n → Bool) → Bool) : Prop :=
  ∀ x y : Fin n → Bool, (∀ i, x i = true → y i = true) →
    F x = true → F y = true

def edgeInput {n : ℕ} (u v : Fin n) : Fin n → Bool :=
  fun i => decide (i = u ∨ i = v)

lemma edge_sandwich {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (F : (Fin n → Bool) → Bool) (hmono : MonoBool F)
    (hbelow : ∀ x, F x = true →
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
    (hedges : ∀ u v, G.Adj u v → F (edgeInput u v) = true) :
    ∀ x, F x = decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) := by
  intro x
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · exact hbelow x
  · rintro ⟨u, v, huv, hu, hv⟩
    apply hmono (edgeInput u v) x ?_ (hedges u v huv)
    intro i hi
    rcases of_decide_eq_true hi with rfl | rfl
    · exact hu
    · exact hv

def inputOr {n : ℕ} (A : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∃ i ∈ A, x i = true)

lemma inputOr_mono {n : ℕ} (A : Finset (Fin n)) : MonoBool (inputOr A) := by
  intro x y hxy hx
  obtain ⟨i, hi, hxi⟩ := of_decide_eq_true hx
  exact decide_eq_true ⟨i, hi, hxy i hxi⟩

lemma literal_and_mono {n : ℕ} (c : Fin n) (B : Finset (Fin n)) :
    MonoBool (fun x => x c && inputOr B x) := by
  intro x y hxy hx
  obtain ⟨hc, hB⟩ := Bool.and_eq_true_iff.mp hx
  exact Bool.and_eq_true_iff.mpr ⟨hxy c hc, inputOr_mono B x y hxy hB⟩

lemma narrow_below {n : ℕ} (A B : Finset (Fin n)) (c : Fin n) (hc : c ∈ A)
    (x : Fin n → Bool) :
    x c && inputOr B x = true → inputOr A x && inputOr B x = true := by
  rintro h
  obtain ⟨hcx, hB⟩ := Bool.and_eq_true_iff.mp h
  exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true ⟨c, hc, hcx⟩, hB⟩

lemma narrow_edge_equal {n : ℕ} (A B : Finset (Fin n)) (c u v : Fin n)
    (hc : c ∈ A)
    (hstar : inputOr A (edgeInput u v) && inputOr B (edgeInput u v) = true →
      u = c ∨ v = c) :
    (edgeInput u v c && inputOr B (edgeInput u v)) =
      (inputOr A (edgeInput u v) && inputOr B (edgeInput u v)) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · exact narrow_below A B c hc _
  · intro h
    have hcenter : edgeInput u v c = true := by
      rcases hstar h with rfl | rfl <;> simp [edgeInput]
    exact Bool.and_eq_true_iff.mpr ⟨hcenter, (Bool.and_eq_true_iff.mp h).2⟩

lemma star_center_substitution {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B : Finset (Fin n)) (c : Fin n) (hc : c ∈ A)
    (K : (Fin n → Bool) → Bool → Bool)
    (hK : ∀ x y : Fin n → Bool, ∀ b d : Bool,
      (∀ i, x i = true → y i = true) → (b = true → d = true) →
        K x b = true → K y d = true)
    (hold : ∀ x, K x (inputOr A x && inputOr B x) =
      decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true))
    (hstar : ∀ u v, G.Adj u v →
      inputOr A (edgeInput u v) && inputOr B (edgeInput u v) = true →
        u = c ∨ v = c) :
    ∀ x, K x (x c && inputOr B x) =
      decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) := by
  apply edge_sandwich G
  · intro x y hxy hx
    exact hK x y _ _ hxy (literal_and_mono c B x y hxy) hx
  · intro x hx
    have h := hK x x _ _ (fun _ hi => hi) (narrow_below A B c hc x) hx
    exact of_decide_eq_true ((hold x) ▸ h)
  · intro u v huv
    rw [narrow_edge_equal A B c u v hc (hstar u v huv), hold]
    apply decide_eq_true
    exact ⟨u, v, huv, by simp [edgeInput], by simp [edgeInput]⟩

lemma inputOr_on_pair {n : ℕ} (A : Finset (Fin n)) (u v : Fin n) :
    inputOr A (edgeInput u v) = true ↔ u ∈ A ∨ v ∈ A := by
  simp only [inputOr, decide_eq_true_eq, edgeInput]
  constructor
  · rintro ⟨i, hi, h⟩
    rcases h with rfl | rfl
    · exact Or.inl hi
    · exact Or.inr hi
  · rintro (hu | hv)
    · exact ⟨u, hu, by simp⟩
    · exact ⟨v, hv, by simp⟩

lemma external_center_has_leaf {n : ℕ} (G : SimpleGraph (Fin n))
    (A B : Finset (Fin n)) (c : Fin n) (hcA : c ∉ A) (hcB : c ∉ B)
    (hne : ∃ u v, G.Adj u v ∧
      inputOr A (edgeInput u v) && inputOr B (edgeInput u v) = true)
    (hstar : ∀ u v, G.Adj u v →
      inputOr A (edgeInput u v) && inputOr B (edgeInput u v) = true →
        u = c ∨ v = c) :
    ∃ v, G.Adj c v ∧ ∀ w, G.Adj v w → w = c := by
  have leaf (v : Fin n) (hcv : G.Adj c v) (hvA : v ∈ A) (hvB : v ∈ B) :
      ∀ w, G.Adj v w → w = c := by
    intro w hvw
    have hval : inputOr A (edgeInput v w) && inputOr B (edgeInput v w) = true :=
      Bool.and_eq_true_iff.mpr ⟨(inputOr_on_pair A v w).mpr (Or.inl hvA),
        (inputOr_on_pair B v w).mpr (Or.inl hvB)⟩
    exact (hstar v w hvw hval).resolve_left hcv.ne.symm
  obtain ⟨u, v, huv, hval⟩ := hne
  have huA := (inputOr_on_pair A u v).mp (Bool.and_eq_true_iff.mp hval).1
  have huB := (inputOr_on_pair B u v).mp (Bool.and_eq_true_iff.mp hval).2
  rcases hstar u v huv hval with rfl | rfl
  · exact ⟨v, huv, leaf v huv (huA.resolve_left hcA) (huB.resolve_left hcB)⟩
  · exact ⟨u, huv.symm, leaf u huv.symm (huA.resolve_right hcA) (huB.resolve_right hcB)⟩

end PEqualNP.Outside.L_meta_1031.DirectOwnership
