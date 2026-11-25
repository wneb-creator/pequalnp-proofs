import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4675.SemanticLinear

def TruthMono {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true

def BelowLinear {n : ℕ} (S : Finset (Fin n)) (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x, f x = true → ∃ i ∈ S, x i = true

lemma and_below_linear {n : ℕ} (S : Finset (Fin n))
    (f g : (Fin n → Bool) → Bool) (hf : TruthMono f) (hg : TruthMono g)
    (h : BelowLinear S (fun x => f x && g x)) :
    BelowLinear S f ∨ BelowLinear S g := by
  classical
  by_contra hn
  have hnf : ¬ BelowLinear S f := fun h' => hn (Or.inl h')
  have hng : ¬ BelowLinear S g := fun h' => hn (Or.inr h')
  unfold BelowLinear at hnf hng
  push Not at hnf hng
  obtain ⟨x, hfx, hx⟩ := hnf
  obtain ⟨y, hgy, hy⟩ := hng
  let z : Fin n → Bool := fun i => decide (i ∉ S)
  have hfz : f z = true := hf x z (by
    intro i hi
    apply decide_eq_true
    intro his
    exact hx i his hi) hfx
  have hgz : g z = true := hg y z (by
    intro i hi
    apply decide_eq_true
    intro his
    exact hy i his hi) hgy
  obtain ⟨i, his, hiz⟩ := h z (by simp only [hfz, hgz, Bool.and_self])
  have hin : i ∉ S := of_decide_eq_true hiz
  exact hin his

lemma or_below_linear {n : ℕ} (S : Finset (Fin n))
    (f g : (Fin n → Bool) → Bool)
    (h : BelowLinear S (fun x => f x || g x)) :
    BelowLinear S f ∧ BelowLinear S g := by
  constructor
  · intro x hx
    exact h x (by simp [hx])
  · intro x hx
    exact h x (by simp [hx])

end PEqualNP.Outside.L_meta_4675.SemanticLinear
