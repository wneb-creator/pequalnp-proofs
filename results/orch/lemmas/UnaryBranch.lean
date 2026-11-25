import Mathlib.Logic.Relation

namespace PEqualNP.Outside.L_meta_2592_aux

lemma no_first_stop_after_unary {α : Type*} (reads : α → α → Prop)
    (stops : α → Prop) (p q i : α) (different : i ≠ q)
    (predecessor : ∀ r, reads r q → r = p) (stopped : stops p) :
    ¬ Relation.ReflTransGen (fun a b => reads a b ∧ ¬ stops a) i q := by
  intro path
  rcases path.cases_tail with same | ⟨r, _, last⟩
  · exact different same.symm
  · exact last.2 ((predecessor r last.1).symm ▸ stopped)

end PEqualNP.Outside.L_meta_2592_aux
