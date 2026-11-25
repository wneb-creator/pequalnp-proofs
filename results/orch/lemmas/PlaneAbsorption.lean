import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583

lemma absorbed_context (context : Bool → Bool) (u t : Bool)
    (below : t = true → context (u || t) = true) :
    context (u || t) = (context u || t) := by
  cases t
  · simp
  · simpa using below rfl

lemma repeated_input_context (context : Bool → Bool) (u a b : Bool)
    (below : (a && b) = true → context ((u || a) && (u || b)) = true) :
    context ((u || a) && (u || b)) = (context u || (a && b)) := by
  have distribution : ((u || a) && (u || b)) = (u || (a && b)) := by
    cases u <;> cases a <;> cases b <;> rfl
  rw [distribution] at below ⊢
  exact absorbed_context context u (a && b) below

lemma extract_repeated_input {α : Type} (target u a b : α → Bool)
    (context : α → Bool → Bool)
    (computes : ∀ x, context x ((u x || a x) && (u x || b x)) = target x)
    (below : ∀ x, (a x && b x) = true → target x = true) :
    ∀ x, (context x (u x) || (a x && b x)) = target x := by
  intro x
  rw [← computes x]
  symm
  apply repeated_input_context
  intro h
  rw [computes x]
  exact below x h

end PEqualNP.Outside.L_meta_2583
