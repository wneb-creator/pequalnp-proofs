import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_095
open PEqualNP.ProofComplexity

theorem inK {V : Type} [DecidableEq V] (F : Set (Clause V)) (K : List (Clause V)) (w : ℕ)
    (hax : ∀ C ∈ F, C.card ≤ w → C ∈ K)
    (hcl : ∀ C ∈ K, ∀ D ∈ K, ∀ v : V, (v, true) ∈ C → (v, false) ∈ D →
      (C.erase (v, true) ∪ D.erase (v, false)).card ≤ w →
      C.erase (v, true) ∪ D.erase (v, false) ∈ K) :
    ∀ π, IsDerivation F π → (∀ D ∈ π, D.card ≤ w) → ∀ D ∈ π, D ∈ K := by
  intro π h
  induction h with
  | nil => intro _ D hD; exact absurd hD List.not_mem_nil
  | ax _ hC ih =>
    intro hw D hD
    rcases List.mem_cons.1 hD with h | hD
    · subst h
      exact hax _ hC (hw _ List.mem_cons_self)
    · exact ih (fun E hE => hw E (List.mem_cons_of_mem _ hE)) D hD
  | res _ hC hD hR ih =>
    intro hw E hE
    have ih' := ih (fun E hE => hw E (List.mem_cons_of_mem _ hE))
    rcases List.mem_cons.1 hE with h | hE
    · subst h
      obtain ⟨v, h1, h2, h3⟩ := hR
      have hc := hw _ List.mem_cons_self
      rw [h3] at hc ⊢
      exact hcl _ (ih' _ hC) _ (ih' _ hD) v h1 h2 hc
    · exact ih' E hE

def closedB {V : Type} [DecidableEq V] (vars : List V) (K : List (Clause V)) (w : ℕ) : Bool :=
  vars.all fun v => (K.filter fun C => decide ((v, true) ∈ C)).all fun C =>
    (K.filter fun D => decide ((v, false) ∈ D)).all fun D =>
      decide (w < (C.erase (v, true) ∪ D.erase (v, false)).card) ||
      decide (C.erase (v, true) ∪ D.erase (v, false) ∈ K)

theorem noRef {V : Type} [DecidableEq V] (F : Set (Clause V)) (K : List (Clause V)) (w : ℕ)
    (vars : List V) (hv : ∀ v, v ∈ vars)
    (hax : ∀ C ∈ F, C.card ≤ w → C ∈ K)
    (h : closedB vars K w = true) (hE : (∅ : Clause V) ∉ K) :
    ¬ ∃ π, IsRefutation F π ∧ ∀ D ∈ π, D.card ≤ w := by
  rintro ⟨π, ⟨hd, he⟩, hw⟩
  refine hE (inK F K w hax ?_ π hd hw ∅ he)
  intro C hC D hD v h1 h2 h3
  simp only [closedB, List.all_eq_true, List.mem_filter, decide_eq_true_eq, Bool.or_eq_true,
    and_imp] at h
  rcases h v (hv v) C hC h1 D hD h2 with h | h
  · omega
  · exact h

def run {V : Type} [DecidableEq V] (A : List (Clause V)) :
    List (Clause V) → List (ℕ ⊕ (ℕ × ℕ × V)) → Option (List (Clause V))
  | acc, [] => some acc
  | acc, Sum.inl k :: r =>
    match A[k]? with
    | some C => run A (C :: acc) r
    | none => none
  | acc, Sum.inr (i, j, v) :: r =>
    match acc[acc.length - 1 - i]?, acc[acc.length - 1 - j]? with
    | some C, some D =>
      if (v, true) ∈ C ∧ (v, false) ∈ D then
        run A ((C.erase (v, true) ∪ D.erase (v, false)) :: acc) r
      else none
    | _, _ => none

theorem run_sound {V : Type} [DecidableEq V] (F : Set (Clause V)) (A : List (Clause V))
    (hA : ∀ C ∈ A, C ∈ F) :
    ∀ (s : List (ℕ ⊕ (ℕ × ℕ × V))) (acc π : List (Clause V)),
      IsDerivation F acc → run A acc s = some π → IsDerivation F π := by
  intro s
  induction s with
  | nil =>
    intro acc π h e
    simp only [run, Option.some.injEq] at e
    exact e ▸ h
  | cons a r ih =>
    intro acc π h e
    rcases a with k | ⟨i, j, v⟩
    · simp only [run] at e
      cases hk : A[k]? with
      | none => rw [hk] at e; exact absurd e (by simp)
      | some C =>
        rw [hk] at e
        exact ih _ _ (IsDerivation.ax h (hA C (List.mem_of_getElem? hk))) e
    · simp only [run] at e
      cases hi : acc[acc.length - 1 - i]? with
      | none => rw [hi] at e; exact absurd e (by simp)
      | some C =>
        cases hj : acc[acc.length - 1 - j]? with
        | none => rw [hi, hj] at e; exact absurd e (by simp)
        | some D =>
          rw [hi, hj] at e
          by_cases hc : (v, true) ∈ C ∧ (v, false) ∈ D
          · simp only [hc, and_self, ↓reduceIte] at e
            exact ih _ _ (IsDerivation.res h (List.mem_of_getElem? hi) (List.mem_of_getElem? hj)
              ⟨v, hc.1, hc.2, rfl⟩) e
          · simp only [hc, ↓reduceIte] at e
            exact absurd e (by simp)

def okB {V : Type} [DecidableEq V] (A : List (Clause V)) (s : List (ℕ ⊕ (ℕ × ℕ × V)))
    (w : ℕ) : Bool :=
  match run A [] s with
  | some π => decide ((∅ : Clause V) ∈ π) && π.all fun D => decide (D.card ≤ w)
  | none => false

theorem ok_sound {V : Type} [DecidableEq V] (F : Set (Clause V)) (A : List (Clause V))
    (hA : ∀ C ∈ A, C ∈ F) (s : List (ℕ ⊕ (ℕ × ℕ × V))) (w : ℕ) (h : okB A s w = true) :
    ∃ π, IsRefutation F π ∧ ∀ D ∈ π, D.card ≤ w := by
  unfold okB at h
  cases hr : run A [] s with
  | none => rw [hr] at h; exact absurd h (by simp)
  | some π =>
    rw [hr] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    exact ⟨π, ⟨run_sound F A hA s [] π IsDerivation.nil hr, h.1⟩, h.2⟩

def Fa : Set (Clause ((Fin 6 × Fin 3) ⊕ Fin 6)) :=
  {C6 | ∃ v7 : Fin 6, C6 = Finset.univ.image (fun t8 : Fin 3 => ((Sum.inl (v7, t8) : (Fin 6 × Fin 3) ⊕ Fin 6), true))} ∪ {C9 | ∃ (u10 v11 : Fin 6) (f12 : Fin 3 → Bool), u10 ≠ v11 ∧ ¬ (u10 ≠ v11 ∧ u10.val / 3 = v11.val / 3) ∧ C9 = Finset.univ.image (fun t13 : Fin 3 => ((Sum.inl (if f12 t13 = true then v11 else u10, t13) : (Fin 6 × Fin 3) ⊕ Fin 6), true))} ∪ {C14 | ∃ (e15 : Fin 6) (t16 : Fin 3), C14 = {((Sum.inr e15 : (Fin 6 × Fin 3) ⊕ Fin 6), false), ((Sum.inl (((![(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : Fin 6 → Fin 6 × Fin 6) e15).1, t16) : (Fin 6 × Fin 3) ⊕ Fin 6), false), ((Sum.inl (((![(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : Fin 6 → Fin 6 × Fin 6) e15).2, t16) : (Fin 6 × Fin 3) ⊕ Fin 6), false)}} ∪ {C17 | ∃ S18 : Finset (Fin 6), S18.card = 2 ∧ C17 = (Finset.univ.filter (fun e19 : Fin 6 => ((![(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : Fin 6 → Fin 6 × Fin 6) e19).1 ∉ S18 ∧ ((![(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : Fin 6 → Fin 6 × Fin 6) e19).2 ∉ S18)).image (fun e20 : Fin 6 => ((Sum.inr e20 : (Fin 6 × Fin 3) ⊕ Fin 6), true))}

def varsa : List ((Fin 6 × Fin 3) ⊕ Fin 6) :=
  [Sum.inl (0, 0), Sum.inl (0, 1), Sum.inl (0, 2), Sum.inl (1, 0), Sum.inl (1, 1), Sum.inl (1, 2), Sum.inl (2, 0), Sum.inl (2, 1), Sum.inl (2, 2), Sum.inl (3, 0), Sum.inl (3, 1), Sum.inl (3, 2), Sum.inl (4, 0), Sum.inl (4, 1), Sum.inl (4, 2), Sum.inl (5, 0), Sum.inl (5, 1), Sum.inl (5, 2), Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inr 3, Sum.inr 4, Sum.inr 5]

def Ka : List (Clause ((Fin 6 × Fin 3) ⊕ Fin 6)) :=
  [{(Sum.inl (0, 0), true), (Sum.inl (0, 1), true), (Sum.inl (0, 2), true)},
   {(Sum.inl (1, 0), true), (Sum.inl (1, 1), true), (Sum.inl (1, 2), true)},
   {(Sum.inl (2, 0), true), (Sum.inl (2, 1), true), (Sum.inl (2, 2), true)},
   {(Sum.inl (3, 0), true), (Sum.inl (3, 1), true), (Sum.inl (3, 2), true)},
   {(Sum.inl (4, 0), true), (Sum.inl (4, 1), true), (Sum.inl (4, 2), true)},
   {(Sum.inl (5, 0), true), (Sum.inl (5, 1), true), (Sum.inl (5, 2), true)},
   {(Sum.inl (0, 0), true), (Sum.inl (0, 1), true), (Sum.inl (3, 2), true)},
   {(Sum.inl (0, 0), true), (Sum.inl (0, 2), true), (Sum.inl (3, 1), true)},
   {(Sum.inl (0, 0), true), (Sum.inl (3, 1), true), (Sum.inl (3, 2), true)},
   {(Sum.inl (0, 1), true), (Sum.inl (0, 2), true), (Sum.inl (3, 0), true)},
   {(Sum.inl (0, 1), true), (Sum.inl (3, 0), true), (Sum.inl (3, 2), true)},
   {(Sum.inl (0, 2), true), (Sum.inl (3, 0), true), (Sum.inl (3, 1), true)},
   {(Sum.inl (0, 0), true), (Sum.inl (0, 1), true), (Sum.inl (4, 2), true)},
   {(Sum.inl (0, 0), true), (Sum.inl (0, 2), true), (Sum.inl (4, 1), true)},
   {(Sum.inl (0, 0), true), (Sum.inl (4, 1), true), (Sum.inl (4, 2), true)},
   {(Sum.inl (0, 1), true), (Sum.inl (0, 2), true), (Sum.inl (4, 0), true)},
   {(Sum.inl (0, 1), true), (Sum.inl (4, 0), true), (Sum.inl (4, 2), true)},
   {(Sum.inl (0, 2), true), (Sum.inl (4, 0), true), (Sum.inl (4, 1), true)},
   {(Sum.inl (0, 0), true), (Sum.inl (0, 1), true), (Sum.inl (5, 2), true)},
   {(Sum.inl (0, 0), true), (Sum.inl (0, 2), true), (Sum.inl (5, 1), true)},
   {(Sum.inl (0, 0), true), (Sum.inl (5, 1), true), (Sum.inl (5, 2), true)},
   {(Sum.inl (0, 1), true), (Sum.inl (0, 2), true), (Sum.inl (5, 0), true)},
   {(Sum.inl (0, 1), true), (Sum.inl (5, 0), true), (Sum.inl (5, 2), true)},
   {(Sum.inl (0, 2), true), (Sum.inl (5, 0), true), (Sum.inl (5, 1), true)},
   {(Sum.inl (1, 0), true), (Sum.inl (1, 1), true), (Sum.inl (3, 2), true)},
   {(Sum.inl (1, 0), true), (Sum.inl (1, 2), true), (Sum.inl (3, 1), true)},
   {(Sum.inl (1, 0), true), (Sum.inl (3, 1), true), (Sum.inl (3, 2), true)},
   {(Sum.inl (1, 1), true), (Sum.inl (1, 2), true), (Sum.inl (3, 0), true)},
   {(Sum.inl (1, 1), true), (Sum.inl (3, 0), true), (Sum.inl (3, 2), true)},
   {(Sum.inl (1, 2), true), (Sum.inl (3, 0), true), (Sum.inl (3, 1), true)},
   {(Sum.inl (1, 0), true), (Sum.inl (1, 1), true), (Sum.inl (4, 2), true)},
   {(Sum.inl (1, 0), true), (Sum.inl (1, 2), true), (Sum.inl (4, 1), true)},
   {(Sum.inl (1, 0), true), (Sum.inl (4, 1), true), (Sum.inl (4, 2), true)},
   {(Sum.inl (1, 1), true), (Sum.inl (1, 2), true), (Sum.inl (4, 0), true)},
   {(Sum.inl (1, 1), true), (Sum.inl (4, 0), true), (Sum.inl (4, 2), true)},
   {(Sum.inl (1, 2), true), (Sum.inl (4, 0), true), (Sum.inl (4, 1), true)},
   {(Sum.inl (1, 0), true), (Sum.inl (1, 1), true), (Sum.inl (5, 2), true)},
   {(Sum.inl (1, 0), true), (Sum.inl (1, 2), true), (Sum.inl (5, 1), true)},
   {(Sum.inl (1, 0), true), (Sum.inl (5, 1), true), (Sum.inl (5, 2), true)},
   {(Sum.inl (1, 1), true), (Sum.inl (1, 2), true), (Sum.inl (5, 0), true)},
   {(Sum.inl (1, 1), true), (Sum.inl (5, 0), true), (Sum.inl (5, 2), true)},
   {(Sum.inl (1, 2), true), (Sum.inl (5, 0), true), (Sum.inl (5, 1), true)},
   {(Sum.inl (2, 0), true), (Sum.inl (2, 1), true), (Sum.inl (3, 2), true)},
   {(Sum.inl (2, 0), true), (Sum.inl (2, 2), true), (Sum.inl (3, 1), true)},
   {(Sum.inl (2, 0), true), (Sum.inl (3, 1), true), (Sum.inl (3, 2), true)},
   {(Sum.inl (2, 1), true), (Sum.inl (2, 2), true), (Sum.inl (3, 0), true)},
   {(Sum.inl (2, 1), true), (Sum.inl (3, 0), true), (Sum.inl (3, 2), true)},
   {(Sum.inl (2, 2), true), (Sum.inl (3, 0), true), (Sum.inl (3, 1), true)},
   {(Sum.inl (2, 0), true), (Sum.inl (2, 1), true), (Sum.inl (4, 2), true)},
   {(Sum.inl (2, 0), true), (Sum.inl (2, 2), true), (Sum.inl (4, 1), true)},
   {(Sum.inl (2, 0), true), (Sum.inl (4, 1), true), (Sum.inl (4, 2), true)},
   {(Sum.inl (2, 1), true), (Sum.inl (2, 2), true), (Sum.inl (4, 0), true)},
   {(Sum.inl (2, 1), true), (Sum.inl (4, 0), true), (Sum.inl (4, 2), true)},
   {(Sum.inl (2, 2), true), (Sum.inl (4, 0), true), (Sum.inl (4, 1), true)},
   {(Sum.inl (2, 0), true), (Sum.inl (2, 1), true), (Sum.inl (5, 2), true)},
   {(Sum.inl (2, 0), true), (Sum.inl (2, 2), true), (Sum.inl (5, 1), true)},
   {(Sum.inl (2, 0), true), (Sum.inl (5, 1), true), (Sum.inl (5, 2), true)},
   {(Sum.inl (2, 1), true), (Sum.inl (2, 2), true), (Sum.inl (5, 0), true)},
   {(Sum.inl (2, 1), true), (Sum.inl (5, 0), true), (Sum.inl (5, 2), true)},
   {(Sum.inl (2, 2), true), (Sum.inl (5, 0), true), (Sum.inl (5, 1), true)},
   {(Sum.inl (0, 0), false), (Sum.inl (1, 0), false), (Sum.inr 0, false)},
   {(Sum.inl (0, 1), false), (Sum.inl (1, 1), false), (Sum.inr 0, false)},
   {(Sum.inl (0, 2), false), (Sum.inl (1, 2), false), (Sum.inr 0, false)},
   {(Sum.inl (1, 0), false), (Sum.inl (2, 0), false), (Sum.inr 1, false)},
   {(Sum.inl (1, 1), false), (Sum.inl (2, 1), false), (Sum.inr 1, false)},
   {(Sum.inl (1, 2), false), (Sum.inl (2, 2), false), (Sum.inr 1, false)},
   {(Sum.inl (0, 0), false), (Sum.inl (2, 0), false), (Sum.inr 2, false)},
   {(Sum.inl (0, 1), false), (Sum.inl (2, 1), false), (Sum.inr 2, false)},
   {(Sum.inl (0, 2), false), (Sum.inl (2, 2), false), (Sum.inr 2, false)},
   {(Sum.inl (3, 0), false), (Sum.inl (4, 0), false), (Sum.inr 3, false)},
   {(Sum.inl (3, 1), false), (Sum.inl (4, 1), false), (Sum.inr 3, false)},
   {(Sum.inl (3, 2), false), (Sum.inl (4, 2), false), (Sum.inr 3, false)},
   {(Sum.inl (4, 0), false), (Sum.inl (5, 0), false), (Sum.inr 4, false)},
   {(Sum.inl (4, 1), false), (Sum.inl (5, 1), false), (Sum.inr 4, false)},
   {(Sum.inl (4, 2), false), (Sum.inl (5, 2), false), (Sum.inr 4, false)},
   {(Sum.inl (3, 0), false), (Sum.inl (5, 0), false), (Sum.inr 5, false)},
   {(Sum.inl (3, 1), false), (Sum.inl (5, 1), false), (Sum.inr 5, false)},
   {(Sum.inl (3, 2), false), (Sum.inl (5, 2), false), (Sum.inr 5, false)},
   {(Sum.inr 3, true), (Sum.inr 4, true), (Sum.inr 5, true)},
   {(Sum.inr 1, true), (Sum.inr 4, true)},
   {(Sum.inr 1, true), (Sum.inr 5, true)},
   {(Sum.inr 1, true), (Sum.inr 3, true)},
   {(Sum.inr 2, true), (Sum.inr 4, true)},
   {(Sum.inr 2, true), (Sum.inr 5, true)},
   {(Sum.inr 2, true), (Sum.inr 3, true)},
   {(Sum.inr 0, true), (Sum.inr 4, true)},
   {(Sum.inr 0, true), (Sum.inr 5, true)},
   {(Sum.inr 0, true), (Sum.inr 3, true)},
   {(Sum.inr 0, true), (Sum.inr 1, true), (Sum.inr 2, true)},
   {(Sum.inl (1, 0), false), (Sum.inl (2, 0), false), (Sum.inr 4, true)},
   {(Sum.inl (1, 1), false), (Sum.inl (2, 1), false), (Sum.inr 4, true)},
   {(Sum.inl (1, 2), false), (Sum.inl (2, 2), false), (Sum.inr 4, true)},
   {(Sum.inl (4, 0), false), (Sum.inl (5, 0), false), (Sum.inr 1, true)},
   {(Sum.inl (4, 1), false), (Sum.inl (5, 1), false), (Sum.inr 1, true)},
   {(Sum.inl (4, 2), false), (Sum.inl (5, 2), false), (Sum.inr 1, true)},
   {(Sum.inl (3, 0), false), (Sum.inl (5, 0), false), (Sum.inr 1, true)},
   {(Sum.inl (3, 1), false), (Sum.inl (5, 1), false), (Sum.inr 1, true)},
   {(Sum.inl (3, 2), false), (Sum.inl (5, 2), false), (Sum.inr 1, true)},
   {(Sum.inl (1, 0), false), (Sum.inl (2, 0), false), (Sum.inr 5, true)},
   {(Sum.inl (1, 1), false), (Sum.inl (2, 1), false), (Sum.inr 5, true)},
   {(Sum.inl (1, 2), false), (Sum.inl (2, 2), false), (Sum.inr 5, true)},
   {(Sum.inl (3, 0), false), (Sum.inl (4, 0), false), (Sum.inr 1, true)},
   {(Sum.inl (3, 1), false), (Sum.inl (4, 1), false), (Sum.inr 1, true)},
   {(Sum.inl (3, 2), false), (Sum.inl (4, 2), false), (Sum.inr 1, true)},
   {(Sum.inl (1, 0), false), (Sum.inl (2, 0), false), (Sum.inr 3, true)},
   {(Sum.inl (1, 1), false), (Sum.inl (2, 1), false), (Sum.inr 3, true)},
   {(Sum.inl (1, 2), false), (Sum.inl (2, 2), false), (Sum.inr 3, true)},
   {(Sum.inl (0, 0), false), (Sum.inl (2, 0), false), (Sum.inr 4, true)},
   {(Sum.inl (0, 1), false), (Sum.inl (2, 1), false), (Sum.inr 4, true)},
   {(Sum.inl (0, 2), false), (Sum.inl (2, 2), false), (Sum.inr 4, true)},
   {(Sum.inl (4, 0), false), (Sum.inl (5, 0), false), (Sum.inr 2, true)},
   {(Sum.inl (4, 1), false), (Sum.inl (5, 1), false), (Sum.inr 2, true)},
   {(Sum.inl (4, 2), false), (Sum.inl (5, 2), false), (Sum.inr 2, true)},
   {(Sum.inl (0, 0), false), (Sum.inl (2, 0), false), (Sum.inr 5, true)},
   {(Sum.inl (0, 1), false), (Sum.inl (2, 1), false), (Sum.inr 5, true)},
   {(Sum.inl (0, 2), false), (Sum.inl (2, 2), false), (Sum.inr 5, true)},
   {(Sum.inl (3, 0), false), (Sum.inl (5, 0), false), (Sum.inr 2, true)},
   {(Sum.inl (3, 1), false), (Sum.inl (5, 1), false), (Sum.inr 2, true)},
   {(Sum.inl (3, 2), false), (Sum.inl (5, 2), false), (Sum.inr 2, true)},
   {(Sum.inl (0, 0), false), (Sum.inl (2, 0), false), (Sum.inr 3, true)},
   {(Sum.inl (0, 1), false), (Sum.inl (2, 1), false), (Sum.inr 3, true)},
   {(Sum.inl (0, 2), false), (Sum.inl (2, 2), false), (Sum.inr 3, true)},
   {(Sum.inl (3, 0), false), (Sum.inl (4, 0), false), (Sum.inr 2, true)},
   {(Sum.inl (3, 1), false), (Sum.inl (4, 1), false), (Sum.inr 2, true)},
   {(Sum.inl (3, 2), false), (Sum.inl (4, 2), false), (Sum.inr 2, true)},
   {(Sum.inl (0, 0), false), (Sum.inl (1, 0), false), (Sum.inr 4, true)},
   {(Sum.inl (0, 1), false), (Sum.inl (1, 1), false), (Sum.inr 4, true)},
   {(Sum.inl (0, 2), false), (Sum.inl (1, 2), false), (Sum.inr 4, true)},
   {(Sum.inl (4, 0), false), (Sum.inl (5, 0), false), (Sum.inr 0, true)},
   {(Sum.inl (4, 1), false), (Sum.inl (5, 1), false), (Sum.inr 0, true)},
   {(Sum.inl (4, 2), false), (Sum.inl (5, 2), false), (Sum.inr 0, true)},
   {(Sum.inl (3, 0), false), (Sum.inl (5, 0), false), (Sum.inr 0, true)},
   {(Sum.inl (3, 1), false), (Sum.inl (5, 1), false), (Sum.inr 0, true)},
   {(Sum.inl (3, 2), false), (Sum.inl (5, 2), false), (Sum.inr 0, true)},
   {(Sum.inl (0, 0), false), (Sum.inl (1, 0), false), (Sum.inr 5, true)},
   {(Sum.inl (0, 1), false), (Sum.inl (1, 1), false), (Sum.inr 5, true)},
   {(Sum.inl (0, 2), false), (Sum.inl (1, 2), false), (Sum.inr 5, true)},
   {(Sum.inl (3, 0), false), (Sum.inl (4, 0), false), (Sum.inr 0, true)},
   {(Sum.inl (3, 1), false), (Sum.inl (4, 1), false), (Sum.inr 0, true)},
   {(Sum.inl (3, 2), false), (Sum.inl (4, 2), false), (Sum.inr 0, true)},
   {(Sum.inl (0, 0), false), (Sum.inl (1, 0), false), (Sum.inr 3, true)},
   {(Sum.inl (0, 1), false), (Sum.inl (1, 1), false), (Sum.inr 3, true)},
   {(Sum.inl (0, 2), false), (Sum.inl (1, 2), false), (Sum.inr 3, true)}]

theorem haxa : ∀ C ∈ Fa, C.card ≤ 3 → C ∈ Ka := by
  rintro C (((⟨v, rfl⟩ | ⟨u, v, f, h1, h2, rfl⟩) | ⟨e, t, rfl⟩) | ⟨S, hS, rfl⟩)
  · revert v
    decide +kernel
  · obtain ⟨a, b, c, rfl⟩ : ∃ a b c : Bool, f = ![a, b, c] :=
      ⟨f 0, f 1, f 2, by funext t; fin_cases t <;> rfl⟩
    have h12 := decide_eq_true (And.intro h1 h2)
    clear h1 h2
    apply of_decide_eq_true
    revert h12
    revert a b c
    revert u v
    decide +kernel
  · revert e t
    decide +kernel
  · revert S
    decide +kernel

theorem loa : ¬ ∃ π, IsRefutation Fa π ∧ ∀ D ∈ π, D.card ≤ 3 :=
  noRef Fa Ka 3 varsa (by decide +kernel) haxa (by decide +kernel)
    (by decide +kernel)

def Aa : List (Clause ((Fin 6 × Fin 3) ⊕ Fin 6)) :=
  [{(Sum.inl (2, 0), true), (Sum.inl (4, 1), true), (Sum.inl (4, 2), true)},
   {(Sum.inl (2, 0), true), (Sum.inl (5, 1), true), (Sum.inl (5, 2), true)},
   {(Sum.inr 1, true), (Sum.inr 4, true)},
   {(Sum.inl (4, 1), false), (Sum.inl (5, 1), false), (Sum.inr 4, false)},
   {(Sum.inr 0, true), (Sum.inr 1, true), (Sum.inr 2, true)},
   {(Sum.inl (0, 0), true), (Sum.inl (3, 1), true), (Sum.inl (3, 2), true)},
   {(Sum.inl (1, 0), true), (Sum.inl (3, 1), true), (Sum.inl (3, 2), true)},
   {(Sum.inl (0, 0), false), (Sum.inl (1, 0), false), (Sum.inr 0, false)},
   {(Sum.inl (2, 0), true), (Sum.inl (3, 1), true), (Sum.inl (3, 2), true)},
   {(Sum.inl (0, 0), false), (Sum.inl (2, 0), false), (Sum.inr 2, false)},
   {(Sum.inr 1, true), (Sum.inr 3, true)},
   {(Sum.inl (3, 1), false), (Sum.inl (4, 1), false), (Sum.inr 3, false)},
   {(Sum.inr 1, true), (Sum.inr 5, true)},
   {(Sum.inl (3, 2), false), (Sum.inl (5, 2), false), (Sum.inr 5, false)},
   {(Sum.inl (4, 2), false), (Sum.inl (5, 2), false), (Sum.inr 4, false)},
   {(Sum.inl (3, 1), false), (Sum.inl (5, 1), false), (Sum.inr 5, false)},
   {(Sum.inl (3, 2), false), (Sum.inl (4, 2), false), (Sum.inr 3, false)},
   {(Sum.inl (1, 0), true), (Sum.inl (4, 1), true), (Sum.inl (4, 2), true)},
   {(Sum.inl (1, 0), true), (Sum.inl (5, 1), true), (Sum.inl (5, 2), true)},
   {(Sum.inl (0, 0), true), (Sum.inl (4, 1), true), (Sum.inl (4, 2), true)},
   {(Sum.inl (0, 0), true), (Sum.inl (5, 1), true), (Sum.inl (5, 2), true)},
   {(Sum.inl (2, 1), true), (Sum.inl (5, 0), true), (Sum.inl (5, 2), true)},
   {(Sum.inl (1, 1), true), (Sum.inl (5, 0), true), (Sum.inl (5, 2), true)},
   {(Sum.inl (1, 1), false), (Sum.inl (2, 1), false), (Sum.inr 1, false)},
   {(Sum.inl (1, 2), true), (Sum.inl (5, 0), true), (Sum.inl (5, 1), true)},
   {(Sum.inl (2, 2), true), (Sum.inl (5, 0), true), (Sum.inl (5, 1), true)},
   {(Sum.inl (1, 2), false), (Sum.inl (2, 2), false), (Sum.inr 1, false)},
   {(Sum.inr 3, true), (Sum.inr 4, true), (Sum.inr 5, true)},
   {(Sum.inl (1, 0), false), (Sum.inl (2, 0), false), (Sum.inr 1, false)},
   {(Sum.inr 0, true), (Sum.inr 4, true)},
   {(Sum.inl (0, 2), true), (Sum.inl (4, 0), true), (Sum.inl (4, 1), true)},
   {(Sum.inl (1, 2), true), (Sum.inl (4, 0), true), (Sum.inl (4, 1), true)},
   {(Sum.inl (0, 2), false), (Sum.inl (1, 2), false), (Sum.inr 0, false)},
   {(Sum.inl (4, 0), true), (Sum.inl (4, 1), true), (Sum.inl (4, 2), true)},
   {(Sum.inl (2, 1), true), (Sum.inl (4, 0), true), (Sum.inl (4, 2), true)},
   {(Sum.inl (1, 1), true), (Sum.inl (4, 0), true), (Sum.inl (4, 2), true)},
   {(Sum.inl (0, 1), true), (Sum.inl (5, 0), true), (Sum.inl (5, 2), true)},
   {(Sum.inl (0, 1), false), (Sum.inl (1, 1), false), (Sum.inr 0, false)},
   {(Sum.inl (5, 0), true), (Sum.inl (5, 1), true), (Sum.inl (5, 2), true)},
   {(Sum.inl (0, 2), true), (Sum.inl (5, 0), true), (Sum.inl (5, 1), true)},
   {(Sum.inl (4, 0), false), (Sum.inl (5, 0), false), (Sum.inr 4, false)},
   {(Sum.inl (0, 1), true), (Sum.inl (4, 0), true), (Sum.inl (4, 2), true)},
   {(Sum.inl (2, 2), true), (Sum.inl (4, 0), true), (Sum.inl (4, 1), true)},
   {(Sum.inl (2, 1), true), (Sum.inl (3, 0), true), (Sum.inl (3, 2), true)},
   {(Sum.inl (1, 1), true), (Sum.inl (3, 0), true), (Sum.inl (3, 2), true)},
   {(Sum.inl (3, 0), false), (Sum.inl (4, 0), false), (Sum.inr 3, false)},
   {(Sum.inl (3, 0), false), (Sum.inl (5, 0), false), (Sum.inr 5, false)},
   {(Sum.inl (1, 2), true), (Sum.inl (3, 0), true), (Sum.inl (3, 1), true)},
   {(Sum.inl (2, 2), true), (Sum.inl (3, 0), true), (Sum.inl (3, 1), true)}]

theorem hAa : ∀ C ∈ Aa, C ∈ Fa := by
  unfold Aa Fa
  simp only [List.forall_mem_cons]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun _ h => absurd h List.not_mem_nil⟩
  · refine Or.inl (Or.inl (Or.inr ⟨2, 4, ![false, true, true], ?_, ?_, ?_⟩)) <;> decide +kernel
  · refine Or.inl (Or.inl (Or.inr ⟨2, 5, ![false, true, true], ?_, ?_, ?_⟩)) <;> decide +kernel
  · refine Or.inr ⟨{0, 3}, ?_, ?_⟩ <;> decide +kernel
  · refine Or.inl (Or.inr ⟨4, 1, ?_⟩); decide +kernel
  · refine Or.inr ⟨{3, 4}, ?_, ?_⟩ <;> decide +kernel
  · refine Or.inl (Or.inl (Or.inr ⟨0, 3, ![false, true, true], ?_, ?_, ?_⟩)) <;> decide +kernel
  · refine Or.inl (Or.inl (Or.inr ⟨1, 3, ![false, true, true], ?_, ?_, ?_⟩)) <;> decide +kernel
  · refine Or.inl (Or.inr ⟨0, 0, ?_⟩); decide +kernel
  · refine Or.inl (Or.inl (Or.inr ⟨2, 3, ![false, true, true], ?_, ?_, ?_⟩)) <;> decide +kernel
  · refine Or.inl (Or.inr ⟨2, 0, ?_⟩); decide +kernel
  · refine Or.inr ⟨{0, 5}, ?_, ?_⟩ <;> decide +kernel
  · refine Or.inl (Or.inr ⟨3, 1, ?_⟩); decide +kernel
  · refine Or.inr ⟨{0, 4}, ?_, ?_⟩ <;> decide +kernel
  · refine Or.inl (Or.inr ⟨5, 2, ?_⟩); decide +kernel
  · refine Or.inl (Or.inr ⟨4, 2, ?_⟩); decide +kernel
  · refine Or.inl (Or.inr ⟨5, 1, ?_⟩); decide +kernel
  · refine Or.inl (Or.inr ⟨3, 2, ?_⟩); decide +kernel
  · refine Or.inl (Or.inl (Or.inr ⟨1, 4, ![false, true, true], ?_, ?_, ?_⟩)) <;> decide +kernel
  · refine Or.inl (Or.inl (Or.inr ⟨1, 5, ![false, true, true], ?_, ?_, ?_⟩)) <;> decide +kernel
  · refine Or.inl (Or.inl (Or.inr ⟨0, 4, ![false, true, true], ?_, ?_, ?_⟩)) <;> decide +kernel
  · refine Or.inl (Or.inl (Or.inr ⟨0, 5, ![false, true, true], ?_, ?_, ?_⟩)) <;> decide +kernel
  · refine Or.inl (Or.inl (Or.inr ⟨2, 5, ![true, false, true], ?_, ?_, ?_⟩)) <;> decide +kernel
  · refine Or.inl (Or.inl (Or.inr ⟨1, 5, ![true, false, true], ?_, ?_, ?_⟩)) <;> decide +kernel
  · refine Or.inl (Or.inr ⟨1, 1, ?_⟩); decide +kernel
  · refine Or.inl (Or.inl (Or.inr ⟨1, 5, ![true, true, false], ?_, ?_, ?_⟩)) <;> decide +kernel
  · refine Or.inl (Or.inl (Or.inr ⟨2, 5, ![true, true, false], ?_, ?_, ?_⟩)) <;> decide +kernel
  · refine Or.inl (Or.inr ⟨1, 2, ?_⟩); decide +kernel
  · refine Or.inr ⟨{0, 1}, ?_, ?_⟩ <;> decide +kernel
  · refine Or.inl (Or.inr ⟨1, 0, ?_⟩); decide +kernel
  · refine Or.inr ⟨{2, 3}, ?_, ?_⟩ <;> decide +kernel
  · refine Or.inl (Or.inl (Or.inr ⟨0, 4, ![true, true, false], ?_, ?_, ?_⟩)) <;> decide +kernel
  · refine Or.inl (Or.inl (Or.inr ⟨1, 4, ![true, true, false], ?_, ?_, ?_⟩)) <;> decide +kernel
  · refine Or.inl (Or.inr ⟨0, 2, ?_⟩); decide +kernel
  · refine Or.inl (Or.inl (Or.inl ⟨4, ?_⟩)); decide +kernel
  · refine Or.inl (Or.inl (Or.inr ⟨2, 4, ![true, false, true], ?_, ?_, ?_⟩)) <;> decide +kernel
  · refine Or.inl (Or.inl (Or.inr ⟨1, 4, ![true, false, true], ?_, ?_, ?_⟩)) <;> decide +kernel
  · refine Or.inl (Or.inl (Or.inr ⟨0, 5, ![true, false, true], ?_, ?_, ?_⟩)) <;> decide +kernel
  · refine Or.inl (Or.inr ⟨0, 1, ?_⟩); decide +kernel
  · refine Or.inl (Or.inl (Or.inl ⟨5, ?_⟩)); decide +kernel
  · refine Or.inl (Or.inl (Or.inr ⟨0, 5, ![true, true, false], ?_, ?_, ?_⟩)) <;> decide +kernel
  · refine Or.inl (Or.inr ⟨4, 0, ?_⟩); decide +kernel
  · refine Or.inl (Or.inl (Or.inr ⟨0, 4, ![true, false, true], ?_, ?_, ?_⟩)) <;> decide +kernel
  · refine Or.inl (Or.inl (Or.inr ⟨2, 4, ![true, true, false], ?_, ?_, ?_⟩)) <;> decide +kernel
  · refine Or.inl (Or.inl (Or.inr ⟨2, 3, ![true, false, true], ?_, ?_, ?_⟩)) <;> decide +kernel
  · refine Or.inl (Or.inl (Or.inr ⟨1, 3, ![true, false, true], ?_, ?_, ?_⟩)) <;> decide +kernel
  · refine Or.inl (Or.inr ⟨3, 0, ?_⟩); decide +kernel
  · refine Or.inl (Or.inr ⟨5, 0, ?_⟩); decide +kernel
  · refine Or.inl (Or.inl (Or.inr ⟨1, 3, ![true, true, false], ?_, ?_, ?_⟩)) <;> decide +kernel
  · refine Or.inl (Or.inl (Or.inr ⟨2, 3, ![true, true, false], ?_, ?_, ?_⟩)) <;> decide +kernel

def Sa : List (ℕ ⊕ (ℕ × ℕ × ((Fin 6 × Fin 3) ⊕ Fin 6))) :=
  [Sum.inl 0,
   Sum.inl 1,
   Sum.inl 2,
   Sum.inl 3,
   Sum.inr (2, 3, Sum.inr 4),
   Sum.inr (1, 4, Sum.inl (5, 1)),
   Sum.inl 4,
   Sum.inl 5,
   Sum.inl 6,
   Sum.inl 7,
   Sum.inr (8, 9, Sum.inl (1, 0)),
   Sum.inr (7, 10, Sum.inl (0, 0)),
   Sum.inr (6, 11, Sum.inr 0),
   Sum.inl 8,
   Sum.inl 9,
   Sum.inr (13, 14, Sum.inl (2, 0)),
   Sum.inr (7, 15, Sum.inl (0, 0)),
   Sum.inr (12, 16, Sum.inr 2),
   Sum.inl 10,
   Sum.inl 11,
   Sum.inr (18, 19, Sum.inr 3),
   Sum.inr (17, 20, Sum.inl (3, 1)),
   Sum.inl 12,
   Sum.inl 13,
   Sum.inr (22, 23, Sum.inr 5),
   Sum.inr (21, 24, Sum.inl (3, 2)),
   Sum.inr (5, 25, Sum.inl (5, 2)),
   Sum.inr (0, 26, Sum.inl (4, 1)),
   Sum.inl 14,
   Sum.inr (2, 28, Sum.inr 4),
   Sum.inr (1, 29, Sum.inl (5, 2)),
   Sum.inl 15,
   Sum.inr (22, 31, Sum.inr 5),
   Sum.inr (17, 32, Sum.inl (3, 1)),
   Sum.inl 16,
   Sum.inr (18, 34, Sum.inr 3),
   Sum.inr (33, 35, Sum.inl (3, 2)),
   Sum.inr (30, 36, Sum.inl (5, 1)),
   Sum.inr (27, 37, Sum.inl (4, 2)),
   Sum.inl 17,
   Sum.inl 18,
   Sum.inr (40, 4, Sum.inl (5, 1)),
   Sum.inr (41, 25, Sum.inl (5, 2)),
   Sum.inr (39, 42, Sum.inl (4, 1)),
   Sum.inr (40, 29, Sum.inl (5, 2)),
   Sum.inr (44, 36, Sum.inl (5, 1)),
   Sum.inr (43, 45, Sum.inl (4, 2)),
   Sum.inl 19,
   Sum.inl 20,
   Sum.inr (48, 4, Sum.inl (5, 1)),
   Sum.inr (49, 25, Sum.inl (5, 2)),
   Sum.inr (47, 50, Sum.inl (4, 1)),
   Sum.inr (48, 29, Sum.inl (5, 2)),
   Sum.inr (52, 36, Sum.inl (5, 1)),
   Sum.inr (51, 53, Sum.inl (4, 2)),
   Sum.inr (54, 9, Sum.inl (0, 0)),
   Sum.inr (46, 55, Sum.inl (1, 0)),
   Sum.inr (6, 56, Sum.inr 0),
   Sum.inr (54, 14, Sum.inl (0, 0)),
   Sum.inr (57, 58, Sum.inr 2),
   Sum.inr (38, 59, Sum.inl (2, 0)),
   Sum.inl 21,
   Sum.inl 22,
   Sum.inl 23,
   Sum.inr (62, 63, Sum.inl (1, 1)),
   Sum.inr (61, 64, Sum.inl (2, 1)),
   Sum.inr (60, 65, Sum.inr 1),
   Sum.inl 24,
   Sum.inl 25,
   Sum.inl 26,
   Sum.inr (68, 69, Sum.inl (2, 2)),
   Sum.inr (67, 70, Sum.inl (1, 2)),
   Sum.inr (60, 71, Sum.inr 1),
   Sum.inl 27,
   Sum.inl 28,
   Sum.inr (40, 74, Sum.inl (1, 0)),
   Sum.inr (1, 75, Sum.inl (2, 0)),
   Sum.inr (60, 76, Sum.inr 1),
   Sum.inl 29,
   Sum.inl 30,
   Sum.inl 31,
   Sum.inl 32,
   Sum.inr (80, 81, Sum.inl (1, 2)),
   Sum.inr (79, 82, Sum.inl (0, 2)),
   Sum.inr (78, 83, Sum.inr 0),
   Sum.inl 33,
   Sum.inr (85, 28, Sum.inl (4, 2)),
   Sum.inr (84, 86, Sum.inr 4),
   Sum.inr (87, 25, Sum.inl (4, 1)),
   Sum.inl 34,
   Sum.inl 35,
   Sum.inr (90, 63, Sum.inl (1, 1)),
   Sum.inr (89, 91, Sum.inl (2, 1)),
   Sum.inr (88, 92, Sum.inr 1),
   Sum.inr (93, 28, Sum.inl (4, 2)),
   Sum.inr (39, 74, Sum.inl (1, 0)),
   Sum.inr (0, 95, Sum.inl (2, 0)),
   Sum.inr (60, 96, Sum.inr 1),
   Sum.inl 36,
   Sum.inl 37,
   Sum.inr (62, 99, Sum.inl (1, 1)),
   Sum.inr (98, 100, Sum.inl (0, 1)),
   Sum.inr (78, 101, Sum.inr 0),
   Sum.inl 38,
   Sum.inr (103, 3, Sum.inl (5, 1)),
   Sum.inr (102, 104, Sum.inr 4),
   Sum.inr (105, 25, Sum.inl (5, 2)),
   Sum.inr (106, 71, Sum.inr 1),
   Sum.inr (107, 3, Sum.inl (5, 1)),
   Sum.inr (97, 108, Sum.inl (4, 1)),
   Sum.inl 39,
   Sum.inr (67, 81, Sum.inl (1, 2)),
   Sum.inr (110, 111, Sum.inl (0, 2)),
   Sum.inr (78, 112, Sum.inr 0),
   Sum.inr (103, 28, Sum.inl (5, 2)),
   Sum.inr (113, 114, Sum.inr 4),
   Sum.inr (115, 36, Sum.inl (5, 1)),
   Sum.inr (116, 65, Sum.inr 1),
   Sum.inr (117, 28, Sum.inl (5, 2)),
   Sum.inr (109, 118, Sum.inl (4, 2)),
   Sum.inl 40,
   Sum.inr (119, 120, Sum.inl (5, 0)),
   Sum.inr (94, 121, Sum.inl (4, 0)),
   Sum.inr (77, 122, Sum.inl (5, 2)),
   Sum.inl 41,
   Sum.inr (90, 99, Sum.inl (1, 1)),
   Sum.inr (124, 125, Sum.inl (0, 1)),
   Sum.inr (78, 126, Sum.inr 0),
   Sum.inr (85, 3, Sum.inl (4, 1)),
   Sum.inr (127, 128, Sum.inr 4),
   Sum.inr (129, 36, Sum.inl (4, 2)),
   Sum.inl 42,
   Sum.inr (131, 69, Sum.inl (2, 2)),
   Sum.inr (80, 132, Sum.inl (1, 2)),
   Sum.inr (130, 133, Sum.inr 1),
   Sum.inr (134, 3, Sum.inl (4, 1)),
   Sum.inr (135, 121, Sum.inl (4, 0)),
   Sum.inr (123, 136, Sum.inl (5, 1)),
   Sum.inr (73, 137, Sum.inr 4),
   Sum.inr (60, 133, Sum.inr 1),
   Sum.inr (60, 92, Sum.inr 1),
   Sum.inr (8, 74, Sum.inl (1, 0)),
   Sum.inr (13, 141, Sum.inl (2, 0)),
   Sum.inr (17, 142, Sum.inr 1),
   Sum.inr (143, 19, Sum.inl (3, 1)),
   Sum.inr (144, 34, Sum.inl (3, 2)),
   Sum.inr (140, 145, Sum.inl (4, 2)),
   Sum.inr (139, 146, Sum.inl (4, 1)),
   Sum.inl 43,
   Sum.inl 44,
   Sum.inr (149, 63, Sum.inl (1, 1)),
   Sum.inr (148, 150, Sum.inl (2, 1)),
   Sum.inr (60, 151, Sum.inr 1),
   Sum.inl 45,
   Sum.inr (152, 153, Sum.inl (3, 0)),
   Sum.inr (147, 154, Sum.inl (4, 0)),
   Sum.inr (138, 155, Sum.inr 3),
   Sum.inr (143, 31, Sum.inl (3, 1)),
   Sum.inr (156, 157, Sum.inr 5),
   Sum.inr (72, 158, Sum.inl (5, 1)),
   Sum.inl 46,
   Sum.inr (152, 160, Sum.inl (3, 0)),
   Sum.inr (156, 161, Sum.inr 5),
   Sum.inr (159, 162, Sum.inl (5, 0)),
   Sum.inr (97, 34, Sum.inl (4, 2)),
   Sum.inr (155, 164, Sum.inl (3, 2)),
   Sum.inl 47,
   Sum.inl 48,
   Sum.inr (167, 69, Sum.inl (2, 2)),
   Sum.inr (166, 168, Sum.inl (1, 2)),
   Sum.inr (60, 169, Sum.inr 1),
   Sum.inr (147, 153, Sum.inl (4, 0)),
   Sum.inr (170, 171, Sum.inl (3, 0)),
   Sum.inr (172, 19, Sum.inl (3, 1)),
   Sum.inr (165, 173, Sum.inl (4, 1)),
   Sum.inr (138, 174, Sum.inr 3),
   Sum.inr (175, 23, Sum.inr 5),
   Sum.inr (163, 176, Sum.inl (3, 2)),
   Sum.inr (66, 177, Sum.inl (5, 2)),
   Sum.inr (138, 171, Sum.inr 3),
   Sum.inr (179, 160, Sum.inr 5),
   Sum.inr (170, 180, Sum.inl (3, 0)),
   Sum.inr (178, 181, Sum.inl (5, 0)),
   Sum.inr (77, 31, Sum.inl (5, 1)),
   Sum.inr (175, 183, Sum.inr 5),
   Sum.inr (184, 177, Sum.inl (5, 2)),
   Sum.inr (182, 185, Sum.inl (3, 1))]

theorem upa : ∃ π, IsRefutation Fa π ∧ ∀ D ∈ π, D.card ≤ 4 :=
  ok_sound Fa Aa hAa Sa 4 (by decide +kernel)

end PEqualNP.Outside.L_pcx_095

theorem PEqualNP.Outside.L_pcx_095 : (∀ F1 : Set (PEqualNP.ProofComplexity.Clause ((Fin 6 × Fin 3) ⊕ Fin 6)), F1 = {C6 | ∃ v7 : Fin 6, C6 = Finset.univ.image (fun t8 : Fin 3 => ((Sum.inl (v7, t8) : (Fin 6 × Fin 3) ⊕ Fin 6), true))} ∪ {C9 | ∃ (u10 v11 : Fin 6) (f12 : Fin 3 → Bool), u10 ≠ v11 ∧ ¬ (u10 ≠ v11 ∧ u10.val / 3 = v11.val / 3) ∧ C9 = Finset.univ.image (fun t13 : Fin 3 => ((Sum.inl (if f12 t13 = true then v11 else u10, t13) : (Fin 6 × Fin 3) ⊕ Fin 6), true))} ∪ {C14 | ∃ (e15 : Fin 6) (t16 : Fin 3), C14 = {((Sum.inr e15 : (Fin 6 × Fin 3) ⊕ Fin 6), false), ((Sum.inl (((![(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : Fin 6 → Fin 6 × Fin 6) e15).1, t16) : (Fin 6 × Fin 3) ⊕ Fin 6), false), ((Sum.inl (((![(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : Fin 6 → Fin 6 × Fin 6) e15).2, t16) : (Fin 6 × Fin 3) ⊕ Fin 6), false)}} ∪ {C17 | ∃ S18 : Finset (Fin 6), S18.card = 2 ∧ C17 = (Finset.univ.filter (fun e19 : Fin 6 => ((![(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : Fin 6 → Fin 6 × Fin 6) e19).1 ∉ S18 ∧ ((![(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : Fin 6 → Fin 6 × Fin 6) e19).2 ∉ S18)).image (fun e20 : Fin 6 => ((Sum.inr e20 : (Fin 6 × Fin 3) ⊕ Fin 6), true))} → (∃ π2, PEqualNP.ProofComplexity.IsRefutation F1 π2 ∧ ∀ D3 ∈ π2, D3.card ≤ 4) ∧ ¬ ∃ π4, PEqualNP.ProofComplexity.IsRefutation F1 π4 ∧ ∀ D5 ∈ π4, D5.card ≤ 3) :=
  fun F hF => by
    subst hF
    exact ⟨PEqualNP.Outside.L_pcx_095.upa, PEqualNP.Outside.L_pcx_095.loa⟩
