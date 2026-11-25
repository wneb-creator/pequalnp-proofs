import PEqualNP.Defs.MetaComplexity

namespace PEqualNP.Outside.L_meta_9811_aux

lemma dep_mem_support {n : ℕ} (f : (Fin n → Bool) → Bool)
    (T : Finset (Fin n))
    (hSupp : ∀ x y : Fin n → Bool, (∀ i ∈ T, x i = y i) → f x = f y)
    (p : Fin n)
    (hdep : ∃ x : Fin n → Bool, f (Function.update x p (!x p)) ≠ f x) : p ∈ T := by
  by_contra hp
  obtain ⟨x, hx⟩ := hdep
  apply hx
  apply hSupp
  intro i hi
  have hip : i ≠ p := by
    intro he
    apply hp
    simpa [he] using hi
  exact Function.update_of_ne hip (!x p) x

lemma any_eq_of_agree {α : Type} (L : List α) (p q : α → Bool)
    (h : ∀ a ∈ L, p a = q a) : L.any p = L.any q := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    simp only [List.any_cons]
    rw [h a (by simp), ih (by intro b hb; exact h b (by simp [hb]))]

lemma graph_supported {n : ℕ} (A : List (Fin n)) (E : List (Fin n × Fin n))
    (T : Finset (Fin n)) (ha : ∀ a ∈ A, a ∈ T)
    (he : ∀ e ∈ E, e.1 ∈ T ∧ e.2 ∈ T)
    (x y : Fin n → Bool) (hxy : ∀ i ∈ T, x i = y i) :
    (A.any (fun a => x a) || E.any (fun e => x e.1 && x e.2)) =
    (A.any (fun a => y a) || E.any (fun e => y e.1 && y e.2)) := by
  congr 1
  · apply any_eq_of_agree
    intro a h
    exact hxy a (ha a h)
  · apply any_eq_of_agree
    intro e h
    rw [hxy e.1 (he e h).1, hxy e.2 (he e h).2]

end PEqualNP.Outside.L_meta_9811_aux
