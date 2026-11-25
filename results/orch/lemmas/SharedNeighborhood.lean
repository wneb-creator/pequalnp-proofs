import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2448.sharedNeighborhood

variable {V : Type*} [DecidableEq V]

def ends (D : Finset (V × V)) : Finset V :=
  D.biUnion fun e => {e.1, e.2}

def oldValue (D : Finset (V × V)) (x q : V → Bool) : Bool :=
  decide (∃ e ∈ D, q e.1 = true ∧ q e.2 = true ∧ (x e.1 = true ∨ x e.2 = true))

def newValue (D : Finset (V × V)) (x q : V → Bool) : Bool :=
  decide (∃ v ∈ ends D, x v = true ∧ q v = true)

lemma block_identity (a b p q : Bool)
    (ha : a = true → q = true) (hb : b = true → p = true) :
    ((p && q) && (a || b)) = ((a && p) || (b && q)) := by
  cases a <;> cases b <;> cases p <;> cases q <;> simp_all

lemma mem_ends (D : Finset (V × V)) (v : V) :
    v ∈ ends D ↔ ∃ e ∈ D, v = e.1 ∨ v = e.2 := by
  simp [ends]

lemma family_identity (D : Finset (V × V)) (x q : V → Bool)
    (h : ∀ e ∈ D, (x e.1 = true → q e.2 = true) ∧
      (x e.2 = true → q e.1 = true)) :
    oldValue D x q = newValue D x q := by
  apply Bool.eq_iff_iff.mpr
  simp only [oldValue, newValue, decide_eq_true_eq, mem_ends]
  constructor
  · rintro ⟨e, he, hp, hq, ha | hb⟩
    · exact ⟨e.1, ⟨e, he, Or.inl rfl⟩, ha, hp⟩
    · exact ⟨e.2, ⟨e, he, Or.inr rfl⟩, hb, hq⟩
  · rintro ⟨v, ⟨e, he, hv | hv⟩, hx, hq⟩
    · subst v
      exact ⟨e, he, hq, (h e he).1 hx, Or.inl hx⟩
    · subst v
      exact ⟨e, he, (h e he).2 hx, hq, Or.inr hx⟩

lemma ends_card_le (D : Finset (V × V)) : (ends D).card ≤ 2 * D.card := by
  classical
  calc
    (ends D).card ≤ ∑ e ∈ D, ({e.1, e.2} : Finset V).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ D, 2 := by
      apply Finset.sum_le_sum
      intro e he
      exact Finset.card_le_two
    _ = 2 * D.card := by simp [Nat.mul_comm]

lemma gate_budget (D : Finset (V × V)) :
    (ends D).card + ((ends D).card - 1) ≤
      3 * D.card + (D.card - 1) := by
  have h := ends_card_le D
  omega

lemma exact_budget (D : Finset (V × V)) :
    2 * (ends D).card - 1 ≤ 4 * D.card - 1 := by
  have h := ends_card_le D
  omega

lemma boundary_budget (D : Finset (V × V)) :
    (ends D).card + D.card ≤ 3 * D.card := by
  have h := ends_card_le D
  omega

variable [Fintype V]

def neighbors (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Bool) (v : V) : Bool :=
  decide (∃ w, G.Adj v w ∧ x w = true)

lemma edge_cross (G : SimpleGraph V) [DecidableRel G.Adj]
    (x : V → Bool) (u v : V) (huv : G.Adj u v) :
    (x u = true → neighbors G x v = true) ∧
      (x v = true → neighbors G x u = true) := by
  constructor <;> intro hx <;> simp only [neighbors, decide_eq_true_eq]
  · exact ⟨u, huv.symm, hx⟩
  · exact ⟨v, huv, hx⟩

lemma graph_family_identity (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : Finset (V × V)) (hD : ∀ e ∈ D, G.Adj e.1 e.2) (x : V → Bool) :
    oldValue D x (neighbors G x) = newValue D x (neighbors G x) := by
  apply family_identity
  intro e he
  exact edge_cross G x e.1 e.2 (hD e he)

end PEqualNP.Outside.L_meta_2448.sharedNeighborhood
