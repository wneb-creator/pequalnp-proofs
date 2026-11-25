import PEqualNP.Defs
import Mathlib.Tactic

namespace PEqualNP.Outside.L_meta_4970.Structure

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

lemma or_support_eq {V : Type*} [Fintype V] [DecidableEq V] (A B : Finset V)
    (h : ∀ x : V → Bool, decide (∃ a ∈ A, x a = true) =
      decide (∃ b ∈ B, x b = true)) : A = B := by
  ext v
  have hv := h (fun w => decide (w = v))
  simpa using hv

lemma two_members {V : Type*} [DecidableEq V] (A : Finset V) (hA : 2 ≤ A.card) :
    ∃ a ∈ A, ∃ b ∈ A, a ≠ b := by
  exact Finset.one_lt_card.mp (by omega)

lemma centre_unique {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hE : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a,b) ∈ E ∧ (a,b') ∈ E ∧ (a',b) ∈ E ∧ (a',b') ∈ E))
    (a a' : Fin p) (Q : Finset (Fin l)) (hq : 2 ≤ Q.card)
    (ha : ∀ b ∈ Q, (a,b) ∈ E) (ha' : ∀ b ∈ Q, (a',b) ∈ E) : a = a' := by
  by_contra hne
  obtain ⟨b,hb,b',hb',hne'⟩ := two_members Q hq
  exact hE a a' b b' hne hne' ⟨ha b hb,ha b' hb',ha' b hb,ha' b' hb'⟩

lemma centre_unique_right {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hE : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a,b) ∈ E ∧ (a,b') ∈ E ∧ (a',b) ∈ E ∧ (a',b') ∈ E))
    (b b' : Fin l) (P : Finset (Fin p)) (hp : 2 ≤ P.card)
    (hb : ∀ a ∈ P, (a,b) ∈ E) (hb' : ∀ a ∈ P, (a,b') ∈ E) : b = b' := by
  by_contra hne
  obtain ⟨a,ha,a',ha',hne'⟩ := two_members P hp
  exact hE a a' b b' hne' hne ⟨hb a ha,hb' a ha,hb a' ha',hb' a' ha'⟩

lemma row_support_eq {p l : ℕ} (Q R : Finset (Fin l))
    (h : ∀ x : Fin (p+l) → Bool,
      decide (∃ b ∈ Q, x (Fin.natAdd p b) = true) =
      decide (∃ b ∈ R, x (Fin.natAdd p b) = true)) : Q = R := by
  apply or_support_eq
  intro y
  have hx := h (Fin.addCases (fun _ => false) y)
  simpa using hx

lemma col_support_eq {p l : ℕ} (P R : Finset (Fin p))
    (h : ∀ x : Fin (p+l) → Bool,
      decide (∃ a ∈ P, x (Fin.castAdd l a) = true) =
      decide (∃ a ∈ R, x (Fin.castAdd l a) = true)) : P = R := by
  apply or_support_eq
  intro y
  have hx := h (Fin.addCases y (fun _ => false))
  simpa using hx

lemma opposite_support_ne {p l : ℕ} (P : Finset (Fin p)) (Q : Finset (Fin l))
    (hP : P.Nonempty)
    (h : ∀ x : Fin (p+l) → Bool,
      decide (∃ a ∈ P, x (Fin.castAdd l a) = true) =
      decide (∃ b ∈ Q, x (Fin.natAdd p b) = true)) : False := by
  have hx := h (Fin.addCases (fun _ => true) (fun _ => false))
  have hempty : ∀ a, a ∉ P := by simpa using hx
  obtain ⟨a, ha⟩ := hP
  exact hempty a ha

def Witness (p l : ℕ) (E : Finset (Fin p × Fin l)) (C : Circuit)
    (j : ℕ) (v : Fin (p+l)) : Prop :=
  (∃ (a : Fin p) (Q : Finset (Fin l)), v = Fin.castAdd l a ∧ 2 ≤ Q.card ∧
    (∀ b ∈ Q, (a,b) ∈ E) ∧ ∀ x : Fin (p+l) → Bool,
      (C.wires (List.ofFn x)).getD (p+l+j) false =
        decide (∃ b ∈ Q, x (Fin.natAdd p b) = true)) ∨
  (∃ (b : Fin l) (P : Finset (Fin p)), v = Fin.natAdd p b ∧ 2 ≤ P.card ∧
    (∀ a ∈ P, (a,b) ∈ E) ∧ ∀ x : Fin (p+l) → Bool,
      (C.wires (List.ofFn x)).getD (p+l+j) false =
        decide (∃ a ∈ P, x (Fin.castAdd l a) = true))

lemma witness_unique {p l : ℕ} (E : Finset (Fin p × Fin l)) (C : Circuit)
    (hE : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a,b) ∈ E ∧ (a,b') ∈ E ∧ (a',b) ∈ E ∧ (a',b') ∈ E))
    {j : ℕ} {v w : Fin (p+l)} (hv : Witness p l E C j v)
    (hw : Witness p l E C j w) : v = w := by
  rcases hv with ⟨a,Q,rfl,hQ,ha,hv⟩ | ⟨b,P,rfl,hP,hb,hv⟩
  · rcases hw with ⟨a',R,rfl,hR,ha',hw⟩ | ⟨b,R,rfl,hR,hb,hw⟩
    · have hQR : Q = R := row_support_eq Q R (fun x => (hv x).symm.trans (hw x))
      subst R
      exact congrArg (Fin.castAdd l) (centre_unique E hE a a' Q hQ ha ha')
    · exact (opposite_support_ne R Q (Finset.card_pos.mp (by omega))
        (fun x => (hw x).symm.trans (hv x))).elim
  · rcases hw with ⟨a,R,rfl,hR,ha,hw⟩ | ⟨b',R,rfl,hR,hb',hw⟩
    · exact (opposite_support_ne P R (Finset.card_pos.mp (by omega))
        (fun x => (hv x).symm.trans (hw x))).elim
    · have hPR : P = R := col_support_eq P R (fun x => (hv x).symm.trans (hw x))
      subst R
      exact congrArg (Fin.natAdd p) (centre_unique_right E hE b b' P hP hb hb')

lemma witness_cover_bound {p l : ℕ} (E : Finset (Fin p × Fin l)) (C : Circuit)
    (hE : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a,b) ∈ E ∧ (a,b') ∈ E ∧ (a',b) ∈ E ∧ (a',b') ∈ E))
    (J : Finset ℕ)
    (hcover : ∀ (a : Fin p) (b : Fin l), (a,b) ∈ E →
      ∃ j ∈ J, Witness p l E C j (Fin.castAdd l a) ∨
        Witness p l E C j (Fin.natAdd p b)) :
    ∃ S : Finset (Fin (p+l)),
      (∀ (a : Fin p) (b : Fin l), (a,b) ∈ E →
        Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧ S.card ≤ J.card := by
  classical
  let S : Finset (Fin (p+l)) := Finset.univ.filter fun v => ∃ j ∈ J, Witness p l E C j v
  have hs (v : {v // v ∈ S}) : ∃ j : {j // j ∈ J}, Witness p l E C j v := by
    obtain ⟨j,hj,hv⟩ := (Finset.mem_filter.mp v.property).2
    exact ⟨⟨j,hj⟩,hv⟩
  let f : {v // v ∈ S} → {j // j ∈ J} := fun v => Classical.choose (hs v)
  have hf (v : {v // v ∈ S}) : Witness p l E C (f v) v := Classical.choose_spec (hs v)
  have hinj : Function.Injective f := by
    intro v w h
    apply Subtype.ext
    have hw := hf w
    rw [← h] at hw
    exact witness_unique E C hE (hf v) hw
  refine ⟨S, ?_, ?_⟩
  · intro a b he
    obtain ⟨j,hj,h⟩ := hcover a b he
    rcases h with ha | hb
    · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _,j,hj,ha⟩)
    · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,j,hj,hb⟩)
  · simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hinj

end PEqualNP.Outside.L_meta_4970.Structure
