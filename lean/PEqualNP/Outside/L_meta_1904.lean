import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Bool.Basic
import Mathlib.Order.Preorder.Finite

namespace PEqualNP.Outside.L_meta_1904_aux

def SupportMonotone {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x y, (∀ v, x v = true → y v = true) → f x = true → f y = true

lemma supportMonotone_of_monotone {n : ℕ} (f : (Fin n → Bool) → Bool)
    (hf : Monotone f) : SupportMonotone f := by
  intro x y hxy hfx
  exact Bool.le_iff_imp.mp (hf (fun v => Bool.le_iff_imp.mpr (hxy v))) hfx

noncomputable def setInput {n : ℕ} (s : Set (Fin n)) : Fin n → Bool := by
  classical
  exact fun v => decide (v ∈ s)

def EdgeHolds {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → Bool) : Prop :=
  ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true

noncomputable def edgeFunction {n : ℕ} (G : SimpleGraph (Fin n))
    (x : Fin n → Bool) : Bool := by
  classical
  exact decide (EdgeHolds G x)

lemma setInput_true_iff {n : ℕ} (s : Set (Fin n)) (v : Fin n) :
    setInput s v = true ↔ v ∈ s := by
  classical
  simp [setInput]

lemma exists_maximal_independent_superset {n : ℕ} (G : SimpleGraph (Fin n))
    {s : Set (Fin n)} (hs : G.IsIndepSet s) :
    ∃ t, s ⊆ t ∧ Maximal G.IsIndepSet t := by
  exact Finite.exists_le_maximal hs

lemma independent_support_iff {n : ℕ} (G : SimpleGraph (Fin n))
    (x : Fin n → Bool) :
    G.IsIndepSet {v | x v = true} ↔ ¬ EdgeHolds G x := by
  constructor
  · intro hs ⟨u, v, huv, hxu, hxv⟩
    exact hs hxu hxv huv.ne huv
  · intro h u hu v hv _ hadj
    exact h ⟨u, v, hadj, hu, hv⟩

lemma implies_edge_iff_rejects_maximal {n : ℕ} (G : SimpleGraph (Fin n))
    (f : (Fin n → Bool) → Bool) (hf : SupportMonotone f) :
    (∀ x, f x = true → EdgeHolds G x) ↔
      ∀ s, Maximal G.IsIndepSet s → f (setInput s) = false := by
  constructor
  · intro h s hs
    cases hfs : f (setInput s) with
    | false => rfl
    | true =>
      obtain ⟨u, v, huv, hu, hv⟩ := h _ hfs
      exact False.elim (hs.1 ((setInput_true_iff s u).mp hu)
        ((setInput_true_iff s v).mp hv) huv.ne huv)
  · intro h x hx
    by_contra he
    obtain ⟨s, hxs, hs⟩ := exists_maximal_independent_superset G
      ((independent_support_iff G x).mpr he)
    have htrue : f (setInput s) = true := hf x (setInput s)
      (fun v hv => (setInput_true_iff s v).mpr (hxs hv)) hx
    rw [h s hs] at htrue
    cases htrue

lemma equals_edge_iff_boundary {n : ℕ} (G : SimpleGraph (Fin n))
    (f : (Fin n → Bool) → Bool) (hf : SupportMonotone f) :
    (∀ x, f x = edgeFunction G x) ↔
      (∀ u v, G.Adj u v → f (setInput ({u, v} : Set (Fin n))) = true) ∧
      (∀ s, Maximal G.IsIndepSet s → f (setInput s) = false) := by
  constructor
  · intro h
    have himplies : ∀ x, f x = true → EdgeHolds G x := by
      intro x hx
      rw [h x] at hx
      simpa [edgeFunction] using hx
    refine ⟨?_, (implies_edge_iff_rejects_maximal G f hf).mp himplies⟩
    intro u v huv
    rw [h]
    simp only [edgeFunction, decide_eq_true_eq]
    exact ⟨u, v, huv, (setInput_true_iff _ _).mpr (by simp),
      (setInput_true_iff _ _).mpr (by simp)⟩
  · rintro ⟨hpairs, hmax⟩ x
    have himplies := (implies_edge_iff_rejects_maximal G f hf).mpr hmax
    have hiff : f x = true ↔ EdgeHolds G x := by
      refine ⟨himplies x, ?_⟩
      rintro ⟨u, v, huv, hu, hv⟩
      apply hf (setInput ({u, v} : Set (Fin n))) x ?_ (hpairs u v huv)
      intro w hw
      have hmem := (setInput_true_iff ({u, v} : Set (Fin n)) w).mp hw
      rcases hmem with hwu | hwv
      · simpa only [hwu] using hu
      · have hwv' : w = v := by simpa only [Set.mem_singleton_iff] using hwv
        simpa only [hwv'] using hv
    cases hfx : f x <;> cases hex : edgeFunction G x <;> try rfl
    · have he : EdgeHolds G x := by simpa [edgeFunction] using hex
      have := hiff.mpr he
      simp [hfx] at this
    · have he := hiff.mp hfx
      have : edgeFunction G x = true := by simpa [edgeFunction] using he
      simp [hex] at this

end PEqualNP.Outside.L_meta_1904_aux
