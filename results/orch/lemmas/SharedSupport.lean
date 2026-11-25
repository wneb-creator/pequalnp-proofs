import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card

namespace PEqualNP.Outside.L_meta_2602_aux.SharedSupport

lemma support_difference {α : Type} [DecidableEq α]
    (S T A B : Finset α) (hSA : S ⊆ A) (hTB : T ⊆ B)
    (hsize : 2 ≤ S.card)
    (hintersection : ∀ p q, p ∈ A → p ∈ B → q ∈ A → q ∈ B → p = q) :
    ∃ p ∈ S, p ∉ T := by
  by_contra! h
  have hsmall : S.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro p hp q hq
    exact hintersection p q (hSA hp) (hTB (h p hp)) (hSA hq) (hTB (h q hq))
  omega

lemma baseline_influence {α : Type} [DecidableEq α]
    (S T Z A B : Finset α) (hSA : S ⊆ A) (hTB : T ⊆ B) (hZT : Z ⊆ T)
    (hsize : 2 ≤ S.card)
    (hintersection : ∀ p q, p ∈ A → p ∈ B → q ∈ A → q ∈ B → p = q) :
    ∃ p ∈ S, p ∉ Z := by
  obtain ⟨p, hp, hn⟩ := support_difference S T A B hSA hTB hsize hintersection
  exact ⟨p, hp, fun hz => hn (hZT hz)⟩

def singleton {n : ℕ} (p : Fin n) : Fin n → Bool := fun q => decide (q = p)

def support (v : ℕ) (f : (Fin v → Bool) → Bool) : Finset (Fin v) :=
  Finset.univ.filter (fun p => f (singleton p) = true)

lemma cofactor_influence (n v : ℕ) (A : Fin n → Finset (Fin v))
    (F : (Fin n → Bool) → (Fin v → Bool) → Bool) (p q : Fin n)
    (hp : ∀ x, F (singleton p) x = true → ∃ i ∈ A p, x i = true)
    (hq : ∀ x, F (singleton q) x = true → ∃ i ∈ A q, x i = true)
    (hmono : ∀ x, F (fun _ => false) x = true → F (singleton q) x = true)
    (hsize : 2 ≤ (support v (F (singleton p))).card)
    (hintersection : ∀ i j, i ∈ A p → i ∈ A q → j ∈ A p → j ∈ A q → i = j) :
    ∃ l : Fin v, F (singleton p) (singleton l) = true ∧
      F (fun _ => false) (singleton l) = false := by
  have hS : support v (F (singleton p)) ⊆ A p := by
    intro l hl
    have h := hp (singleton l) (Finset.mem_filter.mp hl).2
    simpa [singleton] using h
  have hT : support v (F (singleton q)) ⊆ A q := by
    intro l hl
    have h := hq (singleton l) (Finset.mem_filter.mp hl).2
    simpa [singleton] using h
  have hZ : support v (F (fun _ => false)) ⊆ support v (F (singleton q)) := by
    intro l hl
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmono _ (Finset.mem_filter.mp hl).2⟩
  obtain ⟨l, hl, hn⟩ := baseline_influence _ _ _ (A p) (A q) hS hT hZ hsize hintersection
  refine ⟨l, (Finset.mem_filter.mp hl).2, Bool.eq_false_iff.mpr ?_⟩
  intro ht
  exact hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩)

end PEqualNP.Outside.L_meta_2602_aux.SharedSupport
