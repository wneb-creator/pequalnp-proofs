import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1772_aux.StarSemantics

open PEqualNP.EdgeOwnership

variable {n : ℕ}

def leaves (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (f : (Fin n → Bool) → Bool) (u : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun v => G.Adj u v ∧ f (pairInput u v) = true

def star (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (f : (Fin n → Bool) → Bool) (u : Fin n) (x : Fin n → Bool) : Bool :=
  x u && decide (∃ v ∈ leaves G f u, x v = true)

lemma star_below (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (f : (Fin n → Bool) → Bool) (u : Fin n)
    (mono : ∀ x y, (∀ v, x v = true → y v = true) → f x = true → f y = true)
    (x : Fin n → Bool) : star G f u x = true → f x = true := by
  intro h
  have hh : x u = true ∧ ∃ v ∈ leaves G f u, x v = true := by
    simpa [star] using h
  obtain ⟨hu, v, hv, hxv⟩ := hh
  have hfv : f (pairInput u v) = true := (Finset.mem_filter.mp hv).2.2
  apply mono (pairInput u v) x ?_ hfv
  intro w hw
  have hw' : w = u ∨ w = v := of_decide_eq_true hw
  rcases hw' with rfl | rfl
  · exact hu
  · exact hxv

lemma star_on_edges (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (f : (Fin n → Bool) → Bool) (u : Fin n)
    (mono : ∀ x y, (∀ v, x v = true → y v = true) → f x = true → f y = true)
    (center : ∀ a b, G.Adj a b → f (pairInput a b) = true → a = u ∨ b = u)
    (a b : Fin n) (edge : G.Adj a b) :
    star G f u (pairInput a b) = f (pairInput a b) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · exact star_below G f u mono _
  · intro h
    rcases center a b edge h with hcen | hcen
    · subst a
      suffices (pairInput u b) u = true ∧
          ∃ v ∈ leaves G f u, (pairInput u b) v = true by
        simpa [star] using this
      refine ⟨by simp [pairInput], ?_⟩
      exact ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, edge, h⟩,
        by simp [pairInput]⟩
    · subst b
      have swap : pairInput a u = pairInput u a := by
        funext v
        simp only [pairInput, or_comm]
      have h' : f (pairInput u a) = true := swap ▸ h
      suffices (pairInput a u) u = true ∧
          ∃ v ∈ leaves G f u, (pairInput a u) v = true by
        simpa [star] using this
      refine ⟨by simp [pairInput], ?_⟩
      exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, edge.symm, h'⟩,
        by simp [pairInput]⟩

lemma center_not_mem_leaves (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (f : (Fin n → Bool) → Bool) (u : Fin n) : u ∉ leaves G f u := by
  simp [leaves]

lemma star_from_existing_wire (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (f q : (Fin n → Bool) → Bool) (u : Fin n)
    (wire : ∀ x, q x = decide (∃ v ∈ leaves G f u, x v = true)) :
    (fun x => x u && q x) = star G f u := by
  funext x
  rw [wire]
  rfl

end PEqualNP.Outside.L_meta_1772_aux.StarSemantics
