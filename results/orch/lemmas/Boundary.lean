import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Max

namespace PEqualNP.Outside.L_meta_2602_aux.Boundary

abbrev Independent {α : Type} (E : Finset (α × α)) (S : Finset α) : Prop :=
  ∀ e ∈ E, ¬ (e.1 ∈ S ∧ e.2 ∈ S)

abbrev MaximalIndependent {α : Type} (E : Finset (α × α)) (S : Finset α) : Prop :=
  Independent E S ∧ ∀ T, Independent E T → S ⊆ T → T ⊆ S

lemma extend_independent {α : Type} [Fintype α] [DecidableEq α]
    (E : Finset (α × α)) (S : Finset α) (hS : Independent E S) :
    ∃ T, S ⊆ T ∧ MaximalIndependent E T := by
  classical
  let F : Finset (Finset α) := Finset.univ.filter fun T => S ⊆ T ∧ Independent E T
  have mem (T : Finset α) : T ∈ F ↔ S ⊆ T ∧ Independent E T := by simp [F]
  have nonempty : F.Nonempty := ⟨S, (mem S).2 ⟨Finset.Subset.refl S, hS⟩⟩
  obtain ⟨T,hT,hmax⟩ := Finset.exists_max_image F Finset.card nonempty
  obtain ⟨sub,hind⟩ := (mem T).1 hT
  refine ⟨T,sub,hind,?_⟩
  intro U hU hTU
  have hUF : U ∈ F := (mem U).2 ⟨Finset.Subset.trans sub hTU,hU⟩
  have eq : T = U := Finset.eq_of_subset_of_card_le hTU (hmax U hUF)
  exact eq ▸ Finset.Subset.refl U

lemma finset_boundary_complete {α : Type} [Fintype α] [DecidableEq α]
    (E : Finset (α × α)) (f : Finset α → Bool)
    (mono : ∀ S T, S ⊆ T → f S = true → f T = true)
    (positive : ∀ e ∈ E, f {e.1,e.2} = true)
    (negative : ∀ T, MaximalIndependent E T → f T = false) :
    ∀ S, f S = true ↔ ∃ e ∈ E, e.1 ∈ S ∧ e.2 ∈ S := by
  classical
  intro S
  constructor
  · intro hx
    by_contra bad
    have hind : Independent E S := by
      intro e he hedges
      exact bad ⟨e,he,hedges⟩
    obtain ⟨T,hST,hT⟩ := extend_independent E S hind
    have yes := mono S T hST hx
    rw [negative T hT] at yes
    contradiction
  · rintro ⟨e,he,h1,h2⟩
    apply mono {e.1,e.2} S _ (positive e he)
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact h1
    · exact h2

lemma bool_boundary_complete {α : Type} [Fintype α] [DecidableEq α]
    (E : Finset (α × α)) (f : (α → Bool) → Bool)
    (mono : ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true)
    (positive : ∀ e ∈ E, f (fun i => decide (i = e.1 ∨ i = e.2)) = true)
    (negative : ∀ T, MaximalIndependent E T → f (fun i => decide (i ∈ T)) = false) :
    ∀ x, f x = true ↔ ∃ e ∈ E, x e.1 = true ∧ x e.2 = true := by
  classical
  let fs := fun S : Finset α => f (fun i => decide (i ∈ S))
  have monoS (S T : Finset α) (hST : S ⊆ T) (hS : fs S = true) : fs T = true := by
    apply mono (fun i => decide (i ∈ S)) (fun i => decide (i ∈ T)) _ hS
    intro i hi
    exact decide_eq_true (hST (of_decide_eq_true hi))
  have posS (e) (he : e ∈ E) : fs {e.1,e.2} = true := by
    simpa only [fs, Finset.mem_insert, Finset.mem_singleton] using positive e he
  intro x
  let S := Finset.univ.filter fun i => x i = true
  have recover : (fun i => decide (i ∈ S)) = x := by
    funext i
    cases hi : x i <;> simp [S,hi]
  have h := finset_boundary_complete E fs monoS posS negative S
  change f (fun i => decide (i ∈ S)) = true ↔ ∃ e ∈ E, e.1 ∈ S ∧ e.2 ∈ S at h
  rw [recover] at h
  simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using h

end PEqualNP.Outside.L_meta_2602_aux.Boundary
