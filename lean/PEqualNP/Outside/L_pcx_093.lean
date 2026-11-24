import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_093_aux

open PEqualNP.ProofComplexity

private def stepOK {V : Type} [DecidableEq V] (axioms : List (Clause V))
    (acc : List (Clause V)) (C : Clause V) : Option (ℕ × ℕ × V) → Bool
  | none => decide (C ∈ axioms)
  | some (i, j, v) =>
    match acc[i]?, acc[j]? with
    | some A, some B =>
      decide ((v, true) ∈ A ∧ (v, false) ∈ B ∧
        C = A.erase (v, true) ∪ B.erase (v, false))
    | _, _ => false

private theorem checkedStep {V : Type} [DecidableEq V] {F : Set (Clause V)}
    {axioms acc : List (Clause V)} {C : Clause V} {reason : Option (ℕ × ℕ × V)}
    (sub : ∀ D ∈ axioms, D ∈ F) (hd : IsDerivation F acc)
    (ok : stepOK axioms acc C reason = true) : IsDerivation F (C :: acc) := by
  rcases reason with _ | ⟨i, j, v⟩
  · exact .ax hd (sub C (of_decide_eq_true ok))
  · cases hA : acc[i]? with
    | none => simp [stepOK, hA] at ok
    | some A =>
      cases hB : acc[j]? with
      | none => simp [stepOK, hA, hB] at ok
      | some B =>
        exact .res hd (List.mem_of_getElem? hA) (List.mem_of_getElem? hB)
          ⟨v, of_decide_eq_true (by simpa only [stepOK, hA, hB] using ok)⟩

private def certOK {V : Type} [DecidableEq V] (axioms : List (Clause V)) (w : ℕ)
    (acc : List (Clause V)) : List (Clause V × Option (ℕ × ℕ × V)) → Bool
  | [] => decide ((∅ : Clause V) ∈ acc)
  | (C, why) :: rest =>
    (decide (C.card ≤ w) && stepOK axioms acc C why) && certOK axioms w (C :: acc) rest

private theorem checkedCert {V : Type} [DecidableEq V] {F : Set (Clause V)}
    {axioms : List (Clause V)} {w : ℕ} (sub : ∀ D ∈ axioms, D ∈ F)
    (steps : List (Clause V × Option (ℕ × ℕ × V))) (acc : List (Clause V))
    (hd : IsDerivation F acc) (hw : ∀ D ∈ acc, D.card ≤ w)
    (ok : certOK axioms w acc steps = true) :
    ∃ π, IsRefutation F π ∧ ∀ D ∈ π, D.card ≤ w := by
  induction steps generalizing acc with
  | nil => exact ⟨acc, ⟨hd, of_decide_eq_true ok⟩, hw⟩
  | cons step rest ih =>
    obtain ⟨C, why⟩ := step
    simp only [certOK, Bool.and_eq_true, decide_eq_true_eq] at ok
    exact ih (C :: acc) (checkedStep sub hd ok.1.2)
      (fun D hD => by
        rcases List.mem_cons.mp hD with rfl | hD
        · exact ok.1.1
        · exact hw D hD)
      ok.2

private theorem noNarrow {V : Type} [DecidableEq V] {F : Set (Clause V)}
    {w : ℕ} (a : V → Bool) (sat : ∀ C ∈ F, C.card ≤ w → ClauseSat a C) :
    ¬ ∃ π, IsRefutation F π ∧ ∀ D ∈ π, D.card ≤ w := by
  rintro ⟨π, ⟨hd, he⟩, hw⟩
  have allSat : ∀ C ∈ π, ClauseSat a C := by
    clear he
    induction hd with
    | nil => simp
    | @ax π C d hC ih =>
      intro D hD
      rcases List.mem_cons.mp hD with rfl | hD
      · exact sat D hC (hw D (by simp))
      · exact ih (fun A hA => hw A (List.mem_cons_of_mem _ hA)) D hD
    | @res π C D R d hc hd hr ih =>
      intro E hE
      have prev := ih (fun A hA => hw A (List.mem_cons_of_mem _ hA))
      rcases List.mem_cons.mp hE with rfl | hE
      · obtain ⟨v, _, _, rfl⟩ := hr
        by_cases hv : a v = true
        · obtain ⟨l, hl, hs⟩ := prev D hd
          refine ⟨l, Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨?_, hl⟩), hs⟩
          rintro rfl
          simp [hv] at hs
        · obtain ⟨l, hl, hs⟩ := prev C hc
          refine ⟨l, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨?_, hl⟩), hs⟩
          rintro rfl
          exact hv hs
      · exact prev E hE
  simpa [ClauseSat] using allSat ∅ he

private theorem imageCard {n m : ℕ} (f : Fin m → Fin n) :
    (Finset.univ.image
      (fun t : Fin m => ((Sum.inl (f t, t) : (Fin n × Fin m) ⊕ Fin n), true))).card = m := by
  rw [Finset.card_image_of_injective]
  · simp
  · intro i j h
    exact congrArg Prod.snd (Sum.inl.inj (congrArg Prod.fst h))


private def cycleFormula : Set (Clause ((Fin 5 × Fin 3) ⊕ Fin 5)) :=
  {C6 | ∃ v7 : Fin 5, C6 = Finset.univ.image (fun t8 : Fin 3 => ((Sum.inl (v7, t8) : (Fin 5 × Fin 3) ⊕ Fin 5), true))} ∪ {C9 | ∃ (u10 v11 : Fin 5) (f12 : Fin 3 → Bool), u10 ≠ v11 ∧ ¬ (v11 = u10 + 1 ∨ u10 = v11 + 1) ∧ C9 = Finset.univ.image (fun t13 : Fin 3 => ((Sum.inl (if f12 t13 = true then v11 else u10, t13) : (Fin 5 × Fin 3) ⊕ Fin 5), true))} ∪ {C14 | ∃ (e15 : Fin 5) (t16 : Fin 3), C14 = {((Sum.inr e15 : (Fin 5 × Fin 3) ⊕ Fin 5), false), ((Sum.inl (e15, t16) : (Fin 5 × Fin 3) ⊕ Fin 5), false), ((Sum.inl (e15 + 1, t16) : (Fin 5 × Fin 3) ⊕ Fin 5), false)}} ∪ {C17 | ∃ S18 : Finset (Fin 5), S18.card = 2 ∧ C17 = (Finset.univ.filter (fun e19 : Fin 5 => e19 ∉ S18 ∧ e19 + 1 ∉ S18)).image (fun e20 : Fin 5 => ((Sum.inr e20 : (Fin 5 × Fin 3) ⊕ Fin 5), true))}

private def cycleAxioms : List (Clause ((Fin 5 × Fin 3) ⊕ Fin 5)) :=
  [
  {(Sum.inr 3, true)},
  {(Sum.inr 3, false), (Sum.inl (4, 0), false), (Sum.inl (3, 0), false)},
  {(Sum.inl (2, 2), true), (Sum.inl (4, 0), true), (Sum.inl (4, 1), true)},
  {(Sum.inr 4, true)},
  {(Sum.inr 4, false), (Sum.inl (4, 1), false), (Sum.inl (0, 1), false)},
  {(Sum.inr 2, true)},
  {(Sum.inr 2, false), (Sum.inl (3, 0), false), (Sum.inl (2, 0), false)},
  {(Sum.inl (0, 1), true), (Sum.inl (2, 0), true), (Sum.inl (2, 2), true)},
  {(Sum.inl (1, 1), true), (Sum.inl (1, 2), true), (Sum.inl (4, 0), true)},
  {(Sum.inr 1, true)},
  {(Sum.inr 1, false), (Sum.inl (2, 1), false), (Sum.inl (1, 1), false)},
  {(Sum.inr 1, false), (Sum.inl (2, 2), false), (Sum.inl (1, 2), false)},
  {(Sum.inl (1, 1), true), (Sum.inl (1, 2), true), (Sum.inl (3, 0), true)},
  {(Sum.inr 0, true)},
  {(Sum.inr 0, false), (Sum.inl (1, 2), false), (Sum.inl (0, 2), false)},
  {(Sum.inr 2, false), (Sum.inl (3, 1), false), (Sum.inl (2, 1), false)},
  {(Sum.inl (0, 2), true), (Sum.inl (3, 0), true), (Sum.inl (3, 1), true)},
  {(Sum.inl (2, 1), true), (Sum.inl (4, 0), true), (Sum.inl (4, 2), true)},
  {(Sum.inr 4, false), (Sum.inl (4, 2), false), (Sum.inl (0, 2), false)},
  {(Sum.inl (0, 2), true), (Sum.inl (2, 0), true), (Sum.inl (2, 1), true)},
  {(Sum.inr 0, false), (Sum.inl (1, 1), false), (Sum.inl (0, 1), false)},
  {(Sum.inl (1, 1), true), (Sum.inl (3, 0), true), (Sum.inl (3, 2), true)},
  {(Sum.inl (0, 1), true), (Sum.inl (3, 0), true), (Sum.inl (3, 2), true)},
  {(Sum.inr 3, false), (Sum.inl (4, 2), false), (Sum.inl (3, 2), false)},
  {(Sum.inr 4, false), (Sum.inl (4, 0), false), (Sum.inl (0, 0), false)},
  {(Sum.inr 2, false), (Sum.inl (3, 2), false), (Sum.inl (2, 2), false)},
  {(Sum.inl (0, 0), true), (Sum.inl (2, 1), true), (Sum.inl (2, 2), true)}
  ]

private theorem cycleAxiomsValid : ∀ C ∈ cycleAxioms, C ∈ cycleFormula := by
  intro C h
  simp only [cycleAxioms, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inr ⟨{0, 2}, by decide, by decide⟩
  · exact Or.inl (Or.inr ⟨3, 0, by decide⟩)
  · exact Or.inl (Or.inl (Or.inr ⟨2, 4, ![true, true, false], by decide, by decide, by decide⟩))
  · exact Or.inr ⟨{1, 3}, by decide, by decide⟩
  · exact Or.inl (Or.inr ⟨4, 1, by decide⟩)
  · exact Or.inr ⟨{1, 4}, by decide, by decide⟩
  · exact Or.inl (Or.inr ⟨2, 0, by decide⟩)
  · exact Or.inl (Or.inl (Or.inr ⟨0, 2, ![true, false, true], by decide, by decide, by decide⟩))
  · exact Or.inl (Or.inl (Or.inr ⟨1, 4, ![true, false, false], by decide, by decide, by decide⟩))
  · exact Or.inr ⟨{0, 3}, by decide, by decide⟩
  · exact Or.inl (Or.inr ⟨1, 1, by decide⟩)
  · exact Or.inl (Or.inr ⟨1, 2, by decide⟩)
  · exact Or.inl (Or.inl (Or.inr ⟨1, 3, ![true, false, false], by decide, by decide, by decide⟩))
  · exact Or.inr ⟨{2, 4}, by decide, by decide⟩
  · exact Or.inl (Or.inr ⟨0, 2, by decide⟩)
  · exact Or.inl (Or.inr ⟨2, 1, by decide⟩)
  · exact Or.inl (Or.inl (Or.inr ⟨0, 3, ![true, true, false], by decide, by decide, by decide⟩))
  · exact Or.inl (Or.inl (Or.inr ⟨2, 4, ![true, false, true], by decide, by decide, by decide⟩))
  · exact Or.inl (Or.inr ⟨4, 2, by decide⟩)
  · exact Or.inl (Or.inl (Or.inr ⟨0, 2, ![true, true, false], by decide, by decide, by decide⟩))
  · exact Or.inl (Or.inr ⟨0, 1, by decide⟩)
  · exact Or.inl (Or.inl (Or.inr ⟨1, 3, ![true, false, true], by decide, by decide, by decide⟩))
  · exact Or.inl (Or.inl (Or.inr ⟨0, 3, ![true, false, true], by decide, by decide, by decide⟩))
  · exact Or.inl (Or.inr ⟨3, 2, by decide⟩)
  · exact Or.inl (Or.inr ⟨4, 0, by decide⟩)
  · exact Or.inl (Or.inr ⟨2, 2, by decide⟩)
  · exact Or.inl (Or.inl (Or.inr ⟨0, 2, ![false, true, true], by decide, by decide, by decide⟩))

private def cycleCertificate : List (Clause ((Fin 5 × Fin 3) ⊕ Fin 5) × Option (ℕ × ℕ × ((Fin 5 × Fin 3) ⊕ Fin 5))) :=
  [
  ({(Sum.inr 3, true)}, none),
  ({(Sum.inr 3, false), (Sum.inl (4, 0), false), (Sum.inl (3, 0), false)}, none),
  ({(Sum.inl (4, 0), false), (Sum.inl (3, 0), false)}, some (1, 0, Sum.inr 3)),
  ({(Sum.inl (2, 2), true), (Sum.inl (4, 0), true), (Sum.inl (4, 1), true)}, none),
  ({(Sum.inl (3, 0), false), (Sum.inl (2, 2), true), (Sum.inl (4, 1), true)}, some (0, 1, Sum.inl (4, 0))),
  ({(Sum.inr 4, true)}, none),
  ({(Sum.inr 4, false), (Sum.inl (4, 1), false), (Sum.inl (0, 1), false)}, none),
  ({(Sum.inl (4, 1), false), (Sum.inl (0, 1), false)}, some (1, 0, Sum.inr 4)),
  ({(Sum.inl (3, 0), false), (Sum.inl (0, 1), false), (Sum.inl (2, 2), true)}, some (3, 0, Sum.inl (4, 1))),
  ({(Sum.inr 2, true)}, none),
  ({(Sum.inr 2, false), (Sum.inl (3, 0), false), (Sum.inl (2, 0), false)}, none),
  ({(Sum.inl (3, 0), false), (Sum.inl (2, 0), false)}, some (1, 0, Sum.inr 2)),
  ({(Sum.inl (0, 1), true), (Sum.inl (2, 0), true), (Sum.inl (2, 2), true)}, none),
  ({(Sum.inl (3, 0), false), (Sum.inl (0, 1), true), (Sum.inl (2, 2), true)}, some (0, 1, Sum.inl (2, 0))),
  ({(Sum.inl (3, 0), false), (Sum.inl (2, 2), true)}, some (0, 5, Sum.inl (0, 1))),
  ({(Sum.inl (1, 1), true), (Sum.inl (1, 2), true), (Sum.inl (4, 0), true)}, none),
  ({(Sum.inl (3, 0), false), (Sum.inl (1, 1), true), (Sum.inl (1, 2), true)}, some (0, 13, Sum.inl (4, 0))),
  ({(Sum.inr 1, true)}, none),
  ({(Sum.inr 1, false), (Sum.inl (2, 1), false), (Sum.inl (1, 1), false)}, none),
  ({(Sum.inl (2, 1), false), (Sum.inl (1, 1), false)}, some (1, 0, Sum.inr 1)),
  ({(Sum.inl (3, 0), false), (Sum.inl (2, 1), false), (Sum.inl (1, 2), true)}, some (3, 0, Sum.inl (1, 1))),
  ({(Sum.inr 1, false), (Sum.inl (2, 2), false), (Sum.inl (1, 2), false)}, none),
  ({(Sum.inl (2, 2), false), (Sum.inl (1, 2), false)}, some (4, 0, Sum.inr 1)),
  ({(Sum.inl (3, 0), false), (Sum.inl (2, 2), false), (Sum.inl (2, 1), false)}, some (2, 0, Sum.inl (1, 2))),
  ({(Sum.inl (3, 0), false), (Sum.inl (2, 1), false)}, some (9, 0, Sum.inl (2, 2))),
  ({(Sum.inl (1, 1), true), (Sum.inl (1, 2), true), (Sum.inl (3, 0), true)}, none),
  ({(Sum.inl (2, 1), false), (Sum.inl (1, 2), true), (Sum.inl (3, 0), true)}, some (0, 6, Sum.inl (1, 1))),
  ({(Sum.inr 0, true)}, none),
  ({(Sum.inr 0, false), (Sum.inl (1, 2), false), (Sum.inl (0, 2), false)}, none),
  ({(Sum.inl (1, 2), false), (Sum.inl (0, 2), false)}, some (1, 0, Sum.inr 0)),
  ({(Sum.inl (2, 1), false), (Sum.inl (0, 2), false), (Sum.inl (3, 0), true)}, some (3, 0, Sum.inl (1, 2))),
  ({(Sum.inr 2, false), (Sum.inl (3, 1), false), (Sum.inl (2, 1), false)}, none),
  ({(Sum.inl (3, 1), false), (Sum.inl (2, 1), false)}, some (22, 0, Sum.inr 2)),
  ({(Sum.inl (0, 2), true), (Sum.inl (3, 0), true), (Sum.inl (3, 1), true)}, none),
  ({(Sum.inl (2, 1), false), (Sum.inl (0, 2), true), (Sum.inl (3, 0), true)}, some (0, 1, Sum.inl (3, 1))),
  ({(Sum.inl (2, 1), false), (Sum.inl (3, 0), true)}, some (0, 4, Sum.inl (0, 2))),
  ({(Sum.inl (2, 1), false)}, some (0, 11, Sum.inl (3, 0))),
  ({(Sum.inl (2, 1), true), (Sum.inl (4, 0), true), (Sum.inl (4, 2), true)}, none),
  ({(Sum.inl (3, 0), false), (Sum.inl (2, 1), true), (Sum.inl (4, 2), true)}, some (0, 35, Sum.inl (4, 0))),
  ({(Sum.inr 4, false), (Sum.inl (4, 2), false), (Sum.inl (0, 2), false)}, none),
  ({(Sum.inl (4, 2), false), (Sum.inl (0, 2), false)}, some (34, 0, Sum.inr 4)),
  ({(Sum.inl (3, 0), false), (Sum.inl (0, 2), false), (Sum.inl (2, 1), true)}, some (2, 0, Sum.inl (4, 2))),
  ({(Sum.inl (0, 2), true), (Sum.inl (2, 0), true), (Sum.inl (2, 1), true)}, none),
  ({(Sum.inl (3, 0), false), (Sum.inl (0, 2), true), (Sum.inl (2, 1), true)}, some (0, 31, Sum.inl (2, 0))),
  ({(Sum.inl (3, 0), false), (Sum.inl (2, 1), true)}, some (0, 2, Sum.inl (0, 2))),
  ({(Sum.inr 0, false), (Sum.inl (1, 1), false), (Sum.inl (0, 1), false)}, none),
  ({(Sum.inl (1, 1), false), (Sum.inl (0, 1), false)}, some (18, 0, Sum.inr 0)),
  ({(Sum.inl (1, 1), true), (Sum.inl (3, 0), true), (Sum.inl (3, 2), true)}, none),
  ({(Sum.inl (0, 1), false), (Sum.inl (3, 0), true), (Sum.inl (3, 2), true)}, some (0, 1, Sum.inl (1, 1))),
  ({(Sum.inl (0, 1), true), (Sum.inl (3, 0), true), (Sum.inl (3, 2), true)}, none),
  ({(Sum.inl (3, 0), true), (Sum.inl (3, 2), true)}, some (0, 1, Sum.inl (0, 1))),
  ({(Sum.inl (2, 1), true), (Sum.inl (3, 2), true)}, some (0, 6, Sum.inl (3, 0))),
  ({(Sum.inr 3, false), (Sum.inl (4, 2), false), (Sum.inl (3, 2), false)}, none),
  ({(Sum.inl (4, 2), false), (Sum.inl (3, 2), false)}, some (52, 0, Sum.inr 3)),
  ({(Sum.inl (3, 2), false), (Sum.inl (2, 1), true), (Sum.inl (4, 0), true)}, some (16, 0, Sum.inl (4, 2))),
  ({(Sum.inr 4, false), (Sum.inl (4, 0), false), (Sum.inl (0, 0), false)}, none),
  ({(Sum.inl (4, 0), false), (Sum.inl (0, 0), false)}, some (50, 0, Sum.inr 4)),
  ({(Sum.inl (3, 2), false), (Sum.inl (0, 0), false), (Sum.inl (2, 1), true)}, some (2, 0, Sum.inl (4, 0))),
  ({(Sum.inr 2, false), (Sum.inl (3, 2), false), (Sum.inl (2, 2), false)}, none),
  ({(Sum.inl (3, 2), false), (Sum.inl (2, 2), false)}, some (49, 0, Sum.inr 2)),
  ({(Sum.inl (0, 0), true), (Sum.inl (2, 1), true), (Sum.inl (2, 2), true)}, none),
  ({(Sum.inl (3, 2), false), (Sum.inl (0, 0), true), (Sum.inl (2, 1), true)}, some (0, 1, Sum.inl (2, 2))),
  ({(Sum.inl (3, 2), false), (Sum.inl (2, 1), true)}, some (0, 4, Sum.inl (0, 0))),
  ({(Sum.inl (2, 1), true)}, some (11, 0, Sum.inl (3, 2))),
  (∅, some (0, 27, Sum.inl (2, 1)))
  ]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem cycleUpper :
    ∃ π, IsRefutation cycleFormula π ∧ ∀ C ∈ π, C.card ≤ 3 := by
  exact checkedCert cycleAxiomsValid cycleCertificate [] .nil (by simp) (by decide)


private theorem cycleLower :
    ¬ ∃ π, IsRefutation cycleFormula π ∧ ∀ C ∈ π, C.card ≤ 2 := by
  let a : ((Fin 5 × Fin 3) ⊕ Fin 5) → Bool := Sum.elim (fun _ => false) (fun _ => true)
  apply noNarrow a
  intro C hC hw
  rcases hC with ((⟨v, rfl⟩ | ⟨u, v, f, _, _, rfl⟩) | ⟨e, t, rfl⟩) | ⟨S, hs, rfl⟩
  · have := imageCard (n := 5) (m := 3) (fun _ => v)
    omega
  · have := imageCard (m := 3) (fun t => if f t = true then v else u)
    omega
  ·
    have hSize : ∀ (e : Fin 5) (t : Fin 3), ({(Sum.inr e, false), (Sum.inl (e, t), false), (Sum.inl (e+1, t), false)} : Clause ((Fin 5 × Fin 3) ⊕ Fin 5)).card = 3 := by decide
    have := hSize e t
    omega
  · have nonempty : ∀ S : Finset (Fin 5), S.card = 2 →
        ∃ e : Fin 5, e ∉ S ∧ e + 1 ∉ S := by decide
    obtain ⟨e, he⟩ := nonempty S hs
    exact ⟨(Sum.inr e, true), Finset.mem_image.mpr ⟨e, by simp [he], rfl⟩, rfl⟩


private def trianglesFormula : Set (Clause ((Fin 6 × Fin 4) ⊕ Fin 6)) :=
  {C26 | ∃ v27 : Fin 6, C26 = Finset.univ.image (fun t28 : Fin 4 => ((Sum.inl (v27, t28) : (Fin 6 × Fin 4) ⊕ Fin 6), true))} ∪ {C29 | ∃ (u30 v31 : Fin 6) (f32 : Fin 4 → Bool), u30 ≠ v31 ∧ ¬ (u30 ≠ v31 ∧ u30.val / 3 = v31.val / 3) ∧ C29 = Finset.univ.image (fun t33 : Fin 4 => ((Sum.inl (if f32 t33 = true then v31 else u30, t33) : (Fin 6 × Fin 4) ⊕ Fin 6), true))} ∪ {C34 | ∃ (e35 : Fin 6) (t36 : Fin 4), C34 = {((Sum.inr e35 : (Fin 6 × Fin 4) ⊕ Fin 6), false), ((Sum.inl (((![(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : Fin 6 → Fin 6 × Fin 6) e35).1, t36) : (Fin 6 × Fin 4) ⊕ Fin 6), false), ((Sum.inl (((![(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : Fin 6 → Fin 6 × Fin 6) e35).2, t36) : (Fin 6 × Fin 4) ⊕ Fin 6), false)}} ∪ {C37 | ∃ S38 : Finset (Fin 6), S38.card = 3 ∧ C37 = (Finset.univ.filter (fun e39 : Fin 6 => ((![(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : Fin 6 → Fin 6 × Fin 6) e39).1 ∉ S38 ∧ ((![(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : Fin 6 → Fin 6 × Fin 6) e39).2 ∉ S38)).image (fun e40 : Fin 6 => ((Sum.inr e40 : (Fin 6 × Fin 4) ⊕ Fin 6), true))}

private def trianglesAxioms : List (Clause ((Fin 6 × Fin 4) ⊕ Fin 6)) :=
  [
  {(Sum.inl (0, 0), true), (Sum.inl (4, 1), true), (Sum.inl (4, 2), true), (Sum.inl (4, 3), true)},
  {(Sum.inr 0, false), (Sum.inl (1, 0), false), (Sum.inl (0, 0), false)},
  {(Sum.inr 0, true)},
  {(Sum.inl (1, 0), true), (Sum.inl (4, 1), true), (Sum.inl (4, 2), true), (Sum.inl (4, 3), true)},
  {(Sum.inr 4, false), (Sum.inl (5, 1), false), (Sum.inl (4, 1), false)},
  {(Sum.inr 4, true)},
  {(Sum.inl (0, 3), true), (Sum.inl (3, 0), true), (Sum.inl (3, 1), true), (Sum.inl (3, 2), true)},
  {(Sum.inr 0, false), (Sum.inl (1, 3), false), (Sum.inl (0, 3), false)},
  {(Sum.inl (1, 3), true), (Sum.inl (3, 0), true), (Sum.inl (3, 1), true), (Sum.inl (3, 2), true)},
  {(Sum.inr 5, false), (Sum.inl (5, 1), false), (Sum.inl (3, 1), false)},
  {(Sum.inr 5, true)},
  {(Sum.inr 3, false), (Sum.inl (4, 2), false), (Sum.inl (3, 2), false)},
  {(Sum.inr 3, true)},
  {(Sum.inl (0, 2), true), (Sum.inl (3, 0), true), (Sum.inl (3, 1), true), (Sum.inl (3, 3), true)},
  {(Sum.inr 0, false), (Sum.inl (1, 2), false), (Sum.inl (0, 2), false)},
  {(Sum.inl (1, 2), true), (Sum.inl (3, 0), true), (Sum.inl (3, 1), true), (Sum.inl (3, 3), true)},
  {(Sum.inr 3, false), (Sum.inl (4, 3), false), (Sum.inl (3, 3), false)},
  {(Sum.inr 3, false), (Sum.inl (4, 0), false), (Sum.inl (3, 0), false)},
  {(Sum.inl (5, 0), true), (Sum.inl (5, 1), true), (Sum.inl (5, 2), true), (Sum.inl (5, 3), true)},
  {(Sum.inr 4, false), (Sum.inl (5, 0), false), (Sum.inl (4, 0), false)},
  {(Sum.inr 4, false), (Sum.inl (5, 3), false), (Sum.inl (4, 3), false)},
  {(Sum.inr 5, false), (Sum.inl (5, 3), false), (Sum.inl (3, 3), false)},
  {(Sum.inr 3, false), (Sum.inl (4, 1), false), (Sum.inl (3, 1), false)},
  {(Sum.inl (0, 1), true), (Sum.inl (3, 0), true), (Sum.inl (3, 2), true), (Sum.inl (3, 3), true)},
  {(Sum.inr 0, false), (Sum.inl (1, 1), false), (Sum.inl (0, 1), false)},
  {(Sum.inl (1, 1), true), (Sum.inl (3, 0), true), (Sum.inl (3, 2), true), (Sum.inl (3, 3), true)},
  {(Sum.inr 4, false), (Sum.inl (5, 2), false), (Sum.inl (4, 2), false)},
  {(Sum.inr 5, false), (Sum.inl (5, 2), false), (Sum.inl (3, 2), false)},
  {(Sum.inl (0, 1), true), (Sum.inl (0, 2), true), (Sum.inl (4, 0), true), (Sum.inl (4, 3), true)},
  {(Sum.inl (0, 1), true), (Sum.inl (0, 2), true), (Sum.inl (5, 0), true), (Sum.inl (5, 3), true)},
  {(Sum.inr 2, false), (Sum.inl (2, 2), false), (Sum.inl (0, 2), false)},
  {(Sum.inr 2, true)},
  {(Sum.inl (1, 1), true), (Sum.inl (1, 2), true), (Sum.inl (4, 0), true), (Sum.inl (4, 3), true)},
  {(Sum.inr 1, false), (Sum.inl (2, 2), false), (Sum.inl (1, 2), false)},
  {(Sum.inr 1, true)},
  {(Sum.inl (2, 1), true), (Sum.inl (2, 2), true), (Sum.inl (4, 0), true), (Sum.inl (4, 3), true)},
  {(Sum.inr 2, false), (Sum.inl (2, 1), false), (Sum.inl (0, 1), false)},
  {(Sum.inr 1, false), (Sum.inl (2, 1), false), (Sum.inl (1, 1), false)},
  {(Sum.inl (0, 3), true), (Sum.inl (4, 0), true), (Sum.inl (4, 1), true), (Sum.inl (4, 2), true)},
  {(Sum.inl (1, 3), true), (Sum.inl (4, 0), true), (Sum.inl (4, 1), true), (Sum.inl (4, 2), true)},
  {(Sum.inr 5, false), (Sum.inl (5, 0), false), (Sum.inl (3, 0), false)},
  {(Sum.inl (2, 1), true), (Sum.inl (2, 2), true), (Sum.inl (2, 3), true), (Sum.inl (4, 0), true)},
  {(Sum.inr 2, false), (Sum.inl (2, 3), false), (Sum.inl (0, 3), false)},
  {(Sum.inl (0, 2), true), (Sum.inl (0, 3), true), (Sum.inl (4, 0), true), (Sum.inl (4, 1), true)},
  {(Sum.inl (1, 2), true), (Sum.inl (1, 3), true), (Sum.inl (4, 0), true), (Sum.inl (4, 1), true)},
  {(Sum.inl (1, 1), true), (Sum.inl (1, 2), true), (Sum.inl (1, 3), true), (Sum.inl (4, 0), true)},
  {(Sum.inl (0, 1), true), (Sum.inl (0, 3), true), (Sum.inl (4, 0), true), (Sum.inl (4, 2), true)},
  {(Sum.inl (2, 1), true), (Sum.inl (2, 3), true), (Sum.inl (4, 0), true), (Sum.inl (4, 2), true)},
  {(Sum.inl (1, 1), true), (Sum.inl (1, 3), true), (Sum.inl (4, 0), true), (Sum.inl (4, 2), true)},
  {(Sum.inr 1, false), (Sum.inl (2, 3), false), (Sum.inl (1, 3), false)},
  {(Sum.inl (0, 0), true), (Sum.inl (3, 1), true), (Sum.inl (3, 2), true), (Sum.inl (3, 3), true)},
  {(Sum.inl (1, 0), true), (Sum.inl (3, 1), true), (Sum.inl (3, 2), true), (Sum.inl (3, 3), true)},
  {(Sum.inl (2, 2), true), (Sum.inl (2, 3), true), (Sum.inl (4, 0), true), (Sum.inl (4, 1), true)}
  ]

private theorem trianglesAxiomsValid : ∀ C ∈ trianglesAxioms, C ∈ trianglesFormula := by
  intro C h
  simp only [trianglesAxioms, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (Or.inl (Or.inr ⟨0, 4, ![false, true, true, true], by decide, by decide, by decide⟩))
  · exact Or.inl (Or.inr ⟨0, 0, by decide⟩)
  · exact Or.inr ⟨{2, 3, 4}, by decide, by decide⟩
  · exact Or.inl (Or.inl (Or.inr ⟨1, 4, ![false, true, true, true], by decide, by decide, by decide⟩))
  · exact Or.inl (Or.inr ⟨4, 1, by decide⟩)
  · exact Or.inr ⟨{0, 1, 3}, by decide, by decide⟩
  · exact Or.inl (Or.inl (Or.inr ⟨0, 3, ![true, true, true, false], by decide, by decide, by decide⟩))
  · exact Or.inl (Or.inr ⟨0, 3, by decide⟩)
  · exact Or.inl (Or.inl (Or.inr ⟨1, 3, ![true, true, true, false], by decide, by decide, by decide⟩))
  · exact Or.inl (Or.inr ⟨5, 1, by decide⟩)
  · exact Or.inr ⟨{0, 1, 4}, by decide, by decide⟩
  · exact Or.inl (Or.inr ⟨3, 2, by decide⟩)
  · exact Or.inr ⟨{0, 1, 5}, by decide, by decide⟩
  · exact Or.inl (Or.inl (Or.inr ⟨0, 3, ![true, true, false, true], by decide, by decide, by decide⟩))
  · exact Or.inl (Or.inr ⟨0, 2, by decide⟩)
  · exact Or.inl (Or.inl (Or.inr ⟨1, 3, ![true, true, false, true], by decide, by decide, by decide⟩))
  · exact Or.inl (Or.inr ⟨3, 3, by decide⟩)
  · exact Or.inl (Or.inr ⟨3, 0, by decide⟩)
  · exact Or.inl (Or.inl (Or.inl ⟨5, by decide⟩))
  · exact Or.inl (Or.inr ⟨4, 0, by decide⟩)
  · exact Or.inl (Or.inr ⟨4, 3, by decide⟩)
  · exact Or.inl (Or.inr ⟨5, 3, by decide⟩)
  · exact Or.inl (Or.inr ⟨3, 1, by decide⟩)
  · exact Or.inl (Or.inl (Or.inr ⟨0, 3, ![true, false, true, true], by decide, by decide, by decide⟩))
  · exact Or.inl (Or.inr ⟨0, 1, by decide⟩)
  · exact Or.inl (Or.inl (Or.inr ⟨1, 3, ![true, false, true, true], by decide, by decide, by decide⟩))
  · exact Or.inl (Or.inr ⟨4, 2, by decide⟩)
  · exact Or.inl (Or.inr ⟨5, 2, by decide⟩)
  · exact Or.inl (Or.inl (Or.inr ⟨0, 4, ![true, false, false, true], by decide, by decide, by decide⟩))
  · exact Or.inl (Or.inl (Or.inr ⟨0, 5, ![true, false, false, true], by decide, by decide, by decide⟩))
  · exact Or.inl (Or.inr ⟨2, 2, by decide⟩)
  · exact Or.inr ⟨{1, 3, 4}, by decide, by decide⟩
  · exact Or.inl (Or.inl (Or.inr ⟨1, 4, ![true, false, false, true], by decide, by decide, by decide⟩))
  · exact Or.inl (Or.inr ⟨1, 2, by decide⟩)
  · exact Or.inr ⟨{0, 3, 4}, by decide, by decide⟩
  · exact Or.inl (Or.inl (Or.inr ⟨2, 4, ![true, false, false, true], by decide, by decide, by decide⟩))
  · exact Or.inl (Or.inr ⟨2, 1, by decide⟩)
  · exact Or.inl (Or.inr ⟨1, 1, by decide⟩)
  · exact Or.inl (Or.inl (Or.inr ⟨0, 4, ![true, true, true, false], by decide, by decide, by decide⟩))
  · exact Or.inl (Or.inl (Or.inr ⟨1, 4, ![true, true, true, false], by decide, by decide, by decide⟩))
  · exact Or.inl (Or.inr ⟨5, 0, by decide⟩)
  · exact Or.inl (Or.inl (Or.inr ⟨2, 4, ![true, false, false, false], by decide, by decide, by decide⟩))
  · exact Or.inl (Or.inr ⟨2, 3, by decide⟩)
  · exact Or.inl (Or.inl (Or.inr ⟨0, 4, ![true, true, false, false], by decide, by decide, by decide⟩))
  · exact Or.inl (Or.inl (Or.inr ⟨1, 4, ![true, true, false, false], by decide, by decide, by decide⟩))
  · exact Or.inl (Or.inl (Or.inr ⟨1, 4, ![true, false, false, false], by decide, by decide, by decide⟩))
  · exact Or.inl (Or.inl (Or.inr ⟨0, 4, ![true, false, true, false], by decide, by decide, by decide⟩))
  · exact Or.inl (Or.inl (Or.inr ⟨2, 4, ![true, false, true, false], by decide, by decide, by decide⟩))
  · exact Or.inl (Or.inl (Or.inr ⟨1, 4, ![true, false, true, false], by decide, by decide, by decide⟩))
  · exact Or.inl (Or.inr ⟨1, 3, by decide⟩)
  · exact Or.inl (Or.inl (Or.inr ⟨0, 3, ![false, true, true, true], by decide, by decide, by decide⟩))
  · exact Or.inl (Or.inl (Or.inr ⟨1, 3, ![false, true, true, true], by decide, by decide, by decide⟩))
  · exact Or.inl (Or.inl (Or.inr ⟨2, 4, ![true, true, false, false], by decide, by decide, by decide⟩))

private def trianglesCertificate : List (Clause ((Fin 6 × Fin 4) ⊕ Fin 6) × Option (ℕ × ℕ × ((Fin 6 × Fin 4) ⊕ Fin 6))) :=
  [
  ({(Sum.inl (0, 0), true), (Sum.inl (4, 1), true), (Sum.inl (4, 2), true), (Sum.inl (4, 3), true)}, none),
  ({(Sum.inr 0, false), (Sum.inl (1, 0), false), (Sum.inl (0, 0), false)}, none),
  ({(Sum.inr 0, true)}, none),
  ({(Sum.inl (1, 0), false), (Sum.inl (0, 0), false)}, some (0, 1, Sum.inr 0)),
  ({(Sum.inl (1, 0), false), (Sum.inl (4, 1), true), (Sum.inl (4, 2), true), (Sum.inl (4, 3), true)}, some (3, 0, Sum.inl (0, 0))),
  ({(Sum.inl (1, 0), true), (Sum.inl (4, 1), true), (Sum.inl (4, 2), true), (Sum.inl (4, 3), true)}, none),
  ({(Sum.inl (4, 1), true), (Sum.inl (4, 2), true), (Sum.inl (4, 3), true)}, some (0, 1, Sum.inl (1, 0))),
  ({(Sum.inr 4, false), (Sum.inl (5, 1), false), (Sum.inl (4, 1), false)}, none),
  ({(Sum.inr 4, true)}, none),
  ({(Sum.inl (5, 1), false), (Sum.inl (4, 1), false)}, some (0, 1, Sum.inr 4)),
  ({(Sum.inl (5, 1), false), (Sum.inl (4, 2), true), (Sum.inl (4, 3), true)}, some (3, 0, Sum.inl (4, 1))),
  ({(Sum.inl (0, 3), true), (Sum.inl (3, 0), true), (Sum.inl (3, 1), true), (Sum.inl (3, 2), true)}, none),
  ({(Sum.inr 0, false), (Sum.inl (1, 3), false), (Sum.inl (0, 3), false)}, none),
  ({(Sum.inl (1, 3), false), (Sum.inl (0, 3), false)}, some (10, 0, Sum.inr 0)),
  ({(Sum.inl (1, 3), false), (Sum.inl (3, 0), true), (Sum.inl (3, 1), true), (Sum.inl (3, 2), true)}, some (2, 0, Sum.inl (0, 3))),
  ({(Sum.inl (1, 3), true), (Sum.inl (3, 0), true), (Sum.inl (3, 1), true), (Sum.inl (3, 2), true)}, none),
  ({(Sum.inl (3, 0), true), (Sum.inl (3, 1), true), (Sum.inl (3, 2), true)}, some (0, 1, Sum.inl (1, 3))),
  ({(Sum.inr 5, false), (Sum.inl (5, 1), false), (Sum.inl (3, 1), false)}, none),
  ({(Sum.inr 5, true)}, none),
  ({(Sum.inl (5, 1), false), (Sum.inl (3, 1), false)}, some (0, 1, Sum.inr 5)),
  ({(Sum.inl (5, 1), false), (Sum.inl (3, 0), true), (Sum.inl (3, 2), true)}, some (3, 0, Sum.inl (3, 1))),
  ({(Sum.inr 3, false), (Sum.inl (4, 2), false), (Sum.inl (3, 2), false)}, none),
  ({(Sum.inr 3, true)}, none),
  ({(Sum.inl (4, 2), false), (Sum.inl (3, 2), false)}, some (0, 1, Sum.inr 3)),
  ({(Sum.inl (5, 1), false), (Sum.inl (4, 2), false), (Sum.inl (3, 0), true)}, some (3, 0, Sum.inl (3, 2))),
  ({(Sum.inl (5, 1), false), (Sum.inl (3, 0), true), (Sum.inl (4, 3), true)}, some (14, 0, Sum.inl (4, 2))),
  ({(Sum.inl (0, 2), true), (Sum.inl (3, 0), true), (Sum.inl (3, 1), true), (Sum.inl (3, 3), true)}, none),
  ({(Sum.inr 0, false), (Sum.inl (1, 2), false), (Sum.inl (0, 2), false)}, none),
  ({(Sum.inl (1, 2), false), (Sum.inl (0, 2), false)}, some (25, 0, Sum.inr 0)),
  ({(Sum.inl (1, 2), false), (Sum.inl (3, 0), true), (Sum.inl (3, 1), true), (Sum.inl (3, 3), true)}, some (2, 0, Sum.inl (0, 2))),
  ({(Sum.inl (1, 2), true), (Sum.inl (3, 0), true), (Sum.inl (3, 1), true), (Sum.inl (3, 3), true)}, none),
  ({(Sum.inl (3, 0), true), (Sum.inl (3, 1), true), (Sum.inl (3, 3), true)}, some (0, 1, Sum.inl (1, 2))),
  ({(Sum.inr 3, false), (Sum.inl (4, 3), false), (Sum.inl (3, 3), false)}, none),
  ({(Sum.inl (4, 3), false), (Sum.inl (3, 3), false)}, some (10, 0, Sum.inr 3)),
  ({(Sum.inl (4, 3), false), (Sum.inl (3, 0), true), (Sum.inl (3, 1), true)}, some (2, 0, Sum.inl (3, 3))),
  ({(Sum.inl (5, 1), false), (Sum.inl (4, 3), false), (Sum.inl (3, 0), true)}, some (0, 15, Sum.inl (3, 1))),
  ({(Sum.inl (5, 1), false), (Sum.inl (3, 0), true)}, some (10, 0, Sum.inl (4, 3))),
  ({(Sum.inr 3, false), (Sum.inl (4, 0), false), (Sum.inl (3, 0), false)}, none),
  ({(Sum.inl (4, 0), false), (Sum.inl (3, 0), false)}, some (15, 0, Sum.inr 3)),
  ({(Sum.inl (5, 1), false), (Sum.inl (4, 0), false)}, some (2, 0, Sum.inl (3, 0))),
  ({(Sum.inl (5, 0), true), (Sum.inl (5, 1), true), (Sum.inl (5, 2), true), (Sum.inl (5, 3), true)}, none),
  ({(Sum.inr 4, false), (Sum.inl (5, 0), false), (Sum.inl (4, 0), false)}, none),
  ({(Sum.inl (5, 0), false), (Sum.inl (4, 0), false)}, some (33, 0, Sum.inr 4)),
  ({(Sum.inl (4, 0), false), (Sum.inl (5, 1), true), (Sum.inl (5, 2), true), (Sum.inl (5, 3), true)}, some (2, 0, Sum.inl (5, 0))),
  ({(Sum.inl (4, 0), false), (Sum.inl (5, 2), true), (Sum.inl (5, 3), true)}, some (0, 4, Sum.inl (5, 1))),
  ({(Sum.inr 4, false), (Sum.inl (5, 3), false), (Sum.inl (4, 3), false)}, none),
  ({(Sum.inl (5, 3), false), (Sum.inl (4, 3), false)}, some (37, 0, Sum.inr 4)),
  ({(Sum.inl (5, 3), false), (Sum.inl (4, 1), true), (Sum.inl (4, 2), true)}, some (40, 0, Sum.inl (4, 3))),
  ({(Sum.inr 5, false), (Sum.inl (5, 3), false), (Sum.inl (3, 3), false)}, none),
  ({(Sum.inl (5, 3), false), (Sum.inl (3, 3), false)}, some (30, 0, Sum.inr 5)),
  ({(Sum.inl (5, 3), false), (Sum.inl (3, 0), true), (Sum.inl (3, 1), true)}, some (18, 0, Sum.inl (3, 3))),
  ({(Sum.inr 3, false), (Sum.inl (4, 1), false), (Sum.inl (3, 1), false)}, none),
  ({(Sum.inl (4, 1), false), (Sum.inl (3, 1), false)}, some (29, 0, Sum.inr 3)),
  ({(Sum.inl (5, 3), false), (Sum.inl (4, 1), false), (Sum.inl (3, 0), true)}, some (2, 0, Sum.inl (3, 1))),
  ({(Sum.inl (5, 3), false), (Sum.inl (3, 0), true), (Sum.inl (4, 2), true)}, some (6, 0, Sum.inl (4, 1))),
  ({(Sum.inl (0, 1), true), (Sum.inl (3, 0), true), (Sum.inl (3, 2), true), (Sum.inl (3, 3), true)}, none),
  ({(Sum.inr 0, false), (Sum.inl (1, 1), false), (Sum.inl (0, 1), false)}, none),
  ({(Sum.inl (1, 1), false), (Sum.inl (0, 1), false)}, some (54, 0, Sum.inr 0)),
  ({(Sum.inl (1, 1), false), (Sum.inl (3, 0), true), (Sum.inl (3, 2), true), (Sum.inl (3, 3), true)}, some (2, 0, Sum.inl (0, 1))),
  ({(Sum.inl (1, 1), true), (Sum.inl (3, 0), true), (Sum.inl (3, 2), true), (Sum.inl (3, 3), true)}, none),
  ({(Sum.inl (3, 0), true), (Sum.inl (3, 2), true), (Sum.inl (3, 3), true)}, some (0, 1, Sum.inl (1, 1))),
  ({(Sum.inl (5, 3), false), (Sum.inl (3, 0), true), (Sum.inl (3, 2), true)}, some (0, 11, Sum.inl (3, 3))),
  ({(Sum.inl (5, 3), false), (Sum.inl (4, 2), false), (Sum.inl (3, 0), true)}, some (0, 38, Sum.inl (3, 2))),
  ({(Sum.inl (5, 3), false), (Sum.inl (3, 0), true)}, some (8, 0, Sum.inl (4, 2))),
  ({(Sum.inl (5, 3), false), (Sum.inl (4, 0), false)}, some (0, 25, Sum.inl (3, 0))),
  ({(Sum.inl (4, 0), false), (Sum.inl (5, 2), true)}, some (20, 0, Sum.inl (5, 3))),
  ({(Sum.inr 4, false), (Sum.inl (5, 2), false), (Sum.inl (4, 2), false)}, none),
  ({(Sum.inl (5, 2), false), (Sum.inl (4, 2), false)}, some (58, 0, Sum.inr 4)),
  ({(Sum.inl (5, 2), false), (Sum.inl (4, 1), true), (Sum.inl (4, 3), true)}, some (61, 0, Sum.inl (4, 2))),
  ({(Sum.inl (4, 1), false), (Sum.inl (3, 0), true), (Sum.inl (3, 2), true)}, some (52, 16, Sum.inl (3, 1))),
  ({(Sum.inr 5, false), (Sum.inl (5, 2), false), (Sum.inl (3, 2), false)}, none),
  ({(Sum.inl (5, 2), false), (Sum.inl (3, 2), false)}, some (52, 0, Sum.inr 5)),
  ({(Sum.inl (5, 2), false), (Sum.inl (4, 1), false), (Sum.inl (3, 0), true)}, some (2, 0, Sum.inl (3, 2))),
  ({(Sum.inl (5, 2), false), (Sum.inl (3, 0), true), (Sum.inl (4, 3), true)}, some (4, 0, Sum.inl (4, 1))),
  ({(Sum.inl (4, 3), false), (Sum.inl (3, 0), true), (Sum.inl (3, 2), true)}, some (13, 40, Sum.inl (3, 3))),
  ({(Sum.inl (5, 2), false), (Sum.inl (4, 3), false), (Sum.inl (3, 0), true)}, some (0, 3, Sum.inl (3, 2))),
  ({(Sum.inl (5, 2), false), (Sum.inl (3, 0), true)}, some (2, 0, Sum.inl (4, 3))),
  ({(Sum.inl (5, 2), false), (Sum.inl (4, 0), false)}, some (0, 38, Sum.inl (3, 0))),
  ({(Sum.inl (4, 0), false)}, some (12, 0, Sum.inl (5, 2))),
  ({(Sum.inl (0, 1), true), (Sum.inl (0, 2), true), (Sum.inl (4, 0), true), (Sum.inl (4, 3), true)}, none),
  ({(Sum.inl (0, 1), true), (Sum.inl (0, 2), true), (Sum.inl (4, 3), true)}, some (0, 1, Sum.inl (4, 0))),
  ({(Sum.inl (5, 3), false), (Sum.inl (0, 1), true), (Sum.inl (0, 2), true)}, some (0, 34, Sum.inl (4, 3))),
  ({(Sum.inl (0, 1), true), (Sum.inl (0, 2), true), (Sum.inl (5, 0), true), (Sum.inl (5, 3), true)}, none),
  ({(Sum.inl (0, 1), true), (Sum.inl (0, 2), true), (Sum.inl (5, 0), true)}, some (0, 1, Sum.inl (5, 3))),
  ({(Sum.inl (1, 1), false), (Sum.inl (0, 2), true), (Sum.inl (4, 3), true)}, some (3, 26, Sum.inl (0, 1))),
  ({(Sum.inr 2, false), (Sum.inl (2, 2), false), (Sum.inl (0, 2), false)}, none),
  ({(Sum.inr 2, true)}, none),
  ({(Sum.inl (2, 2), false), (Sum.inl (0, 2), false)}, some (0, 1, Sum.inr 2)),
  ({(Sum.inl (2, 2), false), (Sum.inl (1, 1), false), (Sum.inl (4, 3), true)}, some (3, 0, Sum.inl (0, 2))),
  ({(Sum.inl (1, 1), true), (Sum.inl (1, 2), true), (Sum.inl (4, 0), true), (Sum.inl (4, 3), true)}, none),
  ({(Sum.inl (1, 1), true), (Sum.inl (1, 2), true), (Sum.inl (4, 3), true)}, some (0, 11, Sum.inl (4, 0))),
  ({(Sum.inr 1, false), (Sum.inl (2, 2), false), (Sum.inl (1, 2), false)}, none),
  ({(Sum.inr 1, true)}, none),
  ({(Sum.inl (2, 2), false), (Sum.inl (1, 2), false)}, some (0, 1, Sum.inr 1)),
  ({(Sum.inl (2, 2), false), (Sum.inl (1, 1), true), (Sum.inl (4, 3), true)}, some (3, 0, Sum.inl (1, 2))),
  ({(Sum.inl (2, 2), false), (Sum.inl (4, 3), true)}, some (0, 6, Sum.inl (1, 1))),
  ({(Sum.inl (2, 1), true), (Sum.inl (2, 2), true), (Sum.inl (4, 0), true), (Sum.inl (4, 3), true)}, none),
  ({(Sum.inl (2, 1), true), (Sum.inl (2, 2), true), (Sum.inl (4, 3), true)}, some (0, 18, Sum.inl (4, 0))),
  ({(Sum.inl (2, 1), true), (Sum.inl (4, 3), true)}, some (0, 2, Sum.inl (2, 2))),
  ({(Sum.inr 2, false), (Sum.inl (2, 1), false), (Sum.inl (0, 1), false)}, none),
  ({(Sum.inl (2, 1), false), (Sum.inl (0, 1), false)}, some (13, 0, Sum.inr 2)),
  ({(Sum.inl (2, 1), false), (Sum.inl (0, 2), true), (Sum.inl (4, 3), true)}, some (20, 0, Sum.inl (0, 1))),
  ({(Sum.inl (0, 2), true), (Sum.inl (4, 3), true)}, some (3, 0, Sum.inl (2, 1))),
  ({(Sum.inr 1, false), (Sum.inl (2, 1), false), (Sum.inl (1, 1), false)}, none),
  ({(Sum.inl (2, 1), false), (Sum.inl (1, 1), false)}, some (11, 0, Sum.inr 1)),
  ({(Sum.inl (1, 1), false), (Sum.inl (2, 2), true), (Sum.inl (4, 3), true)}, some (7, 0, Sum.inl (2, 1))),
  ({(Sum.inl (1, 1), false), (Sum.inl (4, 3), true)}, some (0, 17, Sum.inl (2, 2))),
  ({(Sum.inl (0, 2), false), (Sum.inl (1, 1), true), (Sum.inl (4, 3), true)}, some (16, 78, Sum.inl (1, 2))),
  ({(Sum.inl (0, 2), false), (Sum.inl (4, 3), true)}, some (0, 1, Sum.inl (1, 1))),
  ({(Sum.inl (4, 3), true)}, some (6, 0, Sum.inl (0, 2))),
  ({(Sum.inl (3, 0), true), (Sum.inl (3, 2), true)}, some (0, 35, Sum.inl (4, 3))),
  ({(Sum.inl (0, 3), true), (Sum.inl (4, 0), true), (Sum.inl (4, 1), true), (Sum.inl (4, 2), true)}, none),
  ({(Sum.inl (0, 3), true), (Sum.inl (4, 1), true), (Sum.inl (4, 2), true)}, some (0, 33, Sum.inl (4, 0))),
  ({(Sum.inl (1, 3), false), (Sum.inl (4, 1), true), (Sum.inl (4, 2), true)}, some (0, 99, Sum.inl (0, 3))),
  ({(Sum.inl (1, 3), true), (Sum.inl (4, 0), true), (Sum.inl (4, 1), true), (Sum.inl (4, 2), true)}, none),
  ({(Sum.inl (1, 3), true), (Sum.inl (4, 1), true), (Sum.inl (4, 2), true)}, some (0, 36, Sum.inl (4, 0))),
  ({(Sum.inl (4, 1), true), (Sum.inl (4, 2), true)}, some (0, 2, Sum.inl (1, 3))),
  ({(Sum.inl (3, 2), false), (Sum.inl (4, 1), true)}, some (0, 93, Sum.inl (4, 2))),
  ({(Sum.inl (3, 0), true), (Sum.inl (4, 1), true)}, some (7, 0, Sum.inl (3, 2))),
  ({(Sum.inl (4, 3), false), (Sum.inl (4, 1), false), (Sum.inl (3, 0), true)}, some (84, 66, Sum.inl (3, 1))),
  ({(Sum.inl (4, 1), false), (Sum.inl (3, 0), true)}, some (10, 0, Sum.inl (4, 3))),
  ({(Sum.inl (3, 0), true)}, some (2, 0, Sum.inl (4, 1))),
  ({(Sum.inr 5, false), (Sum.inl (5, 0), false), (Sum.inl (3, 0), false)}, none),
  ({(Sum.inl (5, 0), false), (Sum.inl (3, 0), false)}, some (104, 0, Sum.inr 5)),
  ({(Sum.inl (5, 0), false)}, some (2, 0, Sum.inl (3, 0))),
  ({(Sum.inl (0, 1), true), (Sum.inl (0, 2), true)}, some (41, 0, Sum.inl (5, 0))),
  ({(Sum.inl (2, 1), false), (Sum.inl (0, 2), true)}, some (0, 25, Sum.inl (0, 1))),
  ({(Sum.inl (2, 1), false), (Sum.inl (1, 2), false)}, some (0, 98, Sum.inl (0, 2))),
  ({(Sum.inl (2, 1), true), (Sum.inl (2, 2), true), (Sum.inl (2, 3), true), (Sum.inl (4, 0), true)}, none),
  ({(Sum.inl (2, 1), true), (Sum.inl (2, 2), true), (Sum.inl (2, 3), true)}, some (0, 50, Sum.inl (4, 0))),
  ({(Sum.inl (1, 2), false), (Sum.inl (2, 1), true), (Sum.inl (2, 3), true)}, some (0, 36, Sum.inl (2, 2))),
  ({(Sum.inl (1, 2), false), (Sum.inl (2, 3), true)}, some (0, 3, Sum.inl (2, 1))),
  ({(Sum.inr 2, false), (Sum.inl (2, 3), false), (Sum.inl (0, 3), false)}, none),
  ({(Sum.inl (2, 3), false), (Sum.inl (0, 3), false)}, some (46, 0, Sum.inr 2)),
  ({(Sum.inl (1, 2), false), (Sum.inl (0, 3), false)}, some (2, 0, Sum.inl (2, 3))),
  ({(Sum.inl (0, 2), true), (Sum.inl (0, 3), true), (Sum.inl (4, 0), true), (Sum.inl (4, 1), true)}, none),
  ({(Sum.inl (0, 2), true), (Sum.inl (0, 3), true), (Sum.inl (4, 1), true)}, some (0, 57, Sum.inl (4, 0))),
  ({(Sum.inl (1, 2), false), (Sum.inl (0, 3), true), (Sum.inl (4, 1), true)}, some (0, 108, Sum.inl (0, 2))),
  ({(Sum.inl (1, 2), false), (Sum.inl (4, 1), true)}, some (0, 3, Sum.inl (0, 3))),
  ({(Sum.inl (1, 2), true), (Sum.inl (1, 3), true), (Sum.inl (4, 0), true), (Sum.inl (4, 1), true)}, none),
  ({(Sum.inl (1, 2), true), (Sum.inl (1, 3), true), (Sum.inl (4, 1), true)}, some (0, 61, Sum.inl (4, 0))),
  ({(Sum.inl (1, 3), true), (Sum.inl (4, 1), true)}, some (0, 2, Sum.inl (1, 2))),
  ({(Sum.inl (1, 1), true), (Sum.inl (1, 2), true), (Sum.inl (1, 3), true), (Sum.inl (4, 0), true)}, none),
  ({(Sum.inl (1, 1), true), (Sum.inl (1, 2), true), (Sum.inl (1, 3), true)}, some (0, 64, Sum.inl (4, 0))),
  ({(Sum.inl (2, 1), false), (Sum.inl (1, 2), true), (Sum.inl (1, 3), true)}, some (0, 39, Sum.inl (1, 1))),
  ({(Sum.inl (2, 1), false), (Sum.inl (1, 3), true)}, some (0, 17, Sum.inl (1, 2))),
  ({(Sum.inl (2, 1), false), (Sum.inl (0, 3), false)}, some (0, 132, Sum.inl (1, 3))),
  ({(Sum.inl (0, 1), true), (Sum.inl (0, 3), true), (Sum.inl (4, 0), true), (Sum.inl (4, 2), true)}, none),
  ({(Sum.inl (0, 1), true), (Sum.inl (0, 3), true), (Sum.inl (4, 2), true)}, some (0, 69, Sum.inl (4, 0))),
  ({(Sum.inl (2, 1), false), (Sum.inl (0, 3), true), (Sum.inl (4, 2), true)}, some (0, 48, Sum.inl (0, 1))),
  ({(Sum.inl (2, 1), false), (Sum.inl (4, 2), true)}, some (0, 3, Sum.inl (0, 3))),
  ({(Sum.inl (2, 1), true), (Sum.inl (2, 3), true), (Sum.inl (4, 0), true), (Sum.inl (4, 2), true)}, none),
  ({(Sum.inl (2, 1), true), (Sum.inl (2, 3), true), (Sum.inl (4, 2), true)}, some (0, 73, Sum.inl (4, 0))),
  ({(Sum.inl (2, 3), true), (Sum.inl (4, 2), true)}, some (0, 2, Sum.inl (2, 1))),
  ({(Sum.inl (1, 1), false), (Sum.inl (0, 2), true)}, some (28, 96, Sum.inl (0, 1))),
  ({(Sum.inl (2, 2), false), (Sum.inl (1, 1), false)}, some (0, 67, Sum.inl (0, 2))),
  ({(Sum.inl (1, 1), false), (Sum.inl (2, 2), true), (Sum.inl (2, 3), true)}, some (26, 51, Sum.inl (2, 1))),
  ({(Sum.inl (1, 1), false), (Sum.inl (2, 3), true)}, some (0, 1, Sum.inl (2, 2))),
  ({(Sum.inl (1, 1), false), (Sum.inl (0, 3), false)}, some (0, 24, Sum.inl (2, 3))),
  ({(Sum.inl (1, 1), false), (Sum.inl (0, 3), true), (Sum.inl (4, 2), true)}, some (10, 101, Sum.inl (0, 1))),
  ({(Sum.inl (1, 1), false), (Sum.inl (4, 2), true)}, some (0, 1, Sum.inl (0, 3))),
  ({(Sum.inl (1, 1), true), (Sum.inl (1, 3), true), (Sum.inl (4, 0), true), (Sum.inl (4, 2), true)}, none),
  ({(Sum.inl (1, 1), true), (Sum.inl (1, 3), true), (Sum.inl (4, 2), true)}, some (0, 83, Sum.inl (4, 0))),
  ({(Sum.inr 1, false), (Sum.inl (2, 3), false), (Sum.inl (1, 3), false)}, none),
  ({(Sum.inl (2, 3), false), (Sum.inl (1, 3), false)}, some (71, 0, Sum.inr 1)),
  ({(Sum.inl (2, 3), false), (Sum.inl (1, 1), true), (Sum.inl (4, 2), true)}, some (2, 0, Sum.inl (1, 3))),
  ({(Sum.inl (2, 3), false), (Sum.inl (4, 2), true)}, some (0, 5, Sum.inl (1, 1))),
  ({(Sum.inl (4, 2), true)}, some (13, 0, Sum.inl (2, 3))),
  ({(Sum.inl (0, 0), true), (Sum.inl (3, 1), true), (Sum.inl (3, 2), true), (Sum.inl (3, 3), true)}, none),
  ({(Sum.inl (1, 0), false), (Sum.inl (3, 1), true), (Sum.inl (3, 2), true), (Sum.inl (3, 3), true)}, some (0, 165, Sum.inl (0, 0))),
  ({(Sum.inl (1, 0), true), (Sum.inl (3, 1), true), (Sum.inl (3, 2), true), (Sum.inl (3, 3), true)}, none),
  ({(Sum.inl (3, 1), true), (Sum.inl (3, 2), true), (Sum.inl (3, 3), true)}, some (0, 1, Sum.inl (1, 0))),
  ({(Sum.inl (4, 3), false), (Sum.inl (3, 1), true), (Sum.inl (3, 2), true)}, some (0, 138, Sum.inl (3, 3))),
  ({(Sum.inl (4, 3), false), (Sum.inl (4, 1), false), (Sum.inl (3, 2), true)}, some (0, 120, Sum.inl (3, 1))),
  ({(Sum.inl (4, 3), false), (Sum.inl (4, 2), false), (Sum.inl (4, 1), false)}, some (0, 150, Sum.inl (3, 2))),
  ({(Sum.inl (4, 2), false), (Sum.inl (4, 1), false)}, some (65, 0, Sum.inl (4, 3))),
  ({(Sum.inl (4, 1), false)}, some (8, 0, Sum.inl (4, 2))),
  ({(Sum.inl (2, 2), false), (Sum.inl (1, 1), true), (Sum.inl (1, 3), true)}, some (33, 83, Sum.inl (1, 2))),
  ({(Sum.inl (2, 2), false), (Sum.inl (1, 3), true)}, some (0, 22, Sum.inl (1, 1))),
  ({(Sum.inl (2, 2), false), (Sum.inl (0, 3), false)}, some (0, 165, Sum.inl (1, 3))),
  ({(Sum.inl (2, 2), false), (Sum.inl (0, 3), true), (Sum.inl (4, 1), true)}, some (43, 92, Sum.inl (0, 2))),
  ({(Sum.inl (2, 2), false), (Sum.inl (4, 1), true)}, some (0, 1, Sum.inl (0, 3))),
  ({(Sum.inl (2, 2), true), (Sum.inl (2, 3), true), (Sum.inl (4, 0), true), (Sum.inl (4, 1), true)}, none),
  ({(Sum.inl (2, 2), true), (Sum.inl (2, 3), true), (Sum.inl (4, 1), true)}, some (0, 104, Sum.inl (4, 0))),
  ({(Sum.inl (1, 3), false), (Sum.inl (2, 2), true), (Sum.inl (4, 1), true)}, some (0, 19, Sum.inl (2, 3))),
  ({(Sum.inl (1, 3), false), (Sum.inl (4, 1), true)}, some (0, 3, Sum.inl (2, 2))),
  ({(Sum.inl (1, 3), false)}, some (0, 9, Sum.inl (4, 1))),
  ({(Sum.inl (4, 1), true)}, some (45, 0, Sum.inl (1, 3))),
  (∅, some (0, 11, Sum.inl (4, 1)))
  ]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem trianglesUpper :
    ∃ π, IsRefutation trianglesFormula π ∧ ∀ C ∈ π, C.card ≤ 4 := by
  exact checkedCert trianglesAxiomsValid trianglesCertificate [] .nil (by simp) (by decide)


private theorem trianglesLower :
    ¬ ∃ π, IsRefutation trianglesFormula π ∧ ∀ C ∈ π, C.card ≤ 3 := by
  let a : ((Fin 6 × Fin 4) ⊕ Fin 6) → Bool := Sum.elim (fun _ => false) (fun _ => true)
  apply noNarrow a
  intro C hC hw
  rcases hC with ((⟨v, rfl⟩ | ⟨u, v, f, _, _, rfl⟩) | ⟨e, t, rfl⟩) | ⟨S, hs, rfl⟩
  · have := imageCard (n := 6) (m := 4) (fun _ => v)
    omega
  · have := imageCard (m := 4) (fun t => if f t = true then v else u)
    omega
  ·
    exact ⟨(Sum.inl (((![(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : Fin 6 → Fin 6 × Fin 6) e).1, t), false), by simp, rfl⟩
  · have nonempty : ∀ S : Finset (Fin 6), S.card = 3 →
        ∃ e : Fin 6, ((![(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : Fin 6 → Fin 6 × Fin 6) e).1 ∉ S ∧ ((![(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : Fin 6 → Fin 6 × Fin 6) e).2 ∉ S := by decide
    obtain ⟨e, he⟩ := nonempty S hs
    exact ⟨(Sum.inr e, true), Finset.mem_image.mpr ⟨e, by simp [he], rfl⟩, rfl⟩


end PEqualNP.Outside.L_pcx_093_aux

open PEqualNP.Outside.L_pcx_093_aux in
theorem PEqualNP.Outside.L_pcx_093 :
    (∀ F1 : Set (PEqualNP.ProofComplexity.Clause ((Fin 5 × Fin 3) ⊕ Fin 5)), F1 = {C6 | ∃ v7 : Fin 5, C6 = Finset.univ.image (fun t8 : Fin 3 => ((Sum.inl (v7, t8) : (Fin 5 × Fin 3) ⊕ Fin 5), true))} ∪ {C9 | ∃ (u10 v11 : Fin 5) (f12 : Fin 3 → Bool), u10 ≠ v11 ∧ ¬ (v11 = u10 + 1 ∨ u10 = v11 + 1) ∧ C9 = Finset.univ.image (fun t13 : Fin 3 => ((Sum.inl (if f12 t13 = true then v11 else u10, t13) : (Fin 5 × Fin 3) ⊕ Fin 5), true))} ∪ {C14 | ∃ (e15 : Fin 5) (t16 : Fin 3), C14 = {((Sum.inr e15 : (Fin 5 × Fin 3) ⊕ Fin 5), false), ((Sum.inl (e15, t16) : (Fin 5 × Fin 3) ⊕ Fin 5), false), ((Sum.inl (e15 + 1, t16) : (Fin 5 × Fin 3) ⊕ Fin 5), false)}} ∪ {C17 | ∃ S18 : Finset (Fin 5), S18.card = 2 ∧ C17 = (Finset.univ.filter (fun e19 : Fin 5 => e19 ∉ S18 ∧ e19 + 1 ∉ S18)).image (fun e20 : Fin 5 => ((Sum.inr e20 : (Fin 5 × Fin 3) ⊕ Fin 5), true))} → (∃ π2, PEqualNP.ProofComplexity.IsRefutation F1 π2 ∧ ∀ D3 ∈ π2, D3.card ≤ 3) ∧ ¬ ∃ π4, PEqualNP.ProofComplexity.IsRefutation F1 π4 ∧ ∀ D5 ∈ π4, D5.card ≤ 2) ∧ (∀ F21 : Set (PEqualNP.ProofComplexity.Clause ((Fin 6 × Fin 4) ⊕ Fin 6)), F21 = {C26 | ∃ v27 : Fin 6, C26 = Finset.univ.image (fun t28 : Fin 4 => ((Sum.inl (v27, t28) : (Fin 6 × Fin 4) ⊕ Fin 6), true))} ∪ {C29 | ∃ (u30 v31 : Fin 6) (f32 : Fin 4 → Bool), u30 ≠ v31 ∧ ¬ (u30 ≠ v31 ∧ u30.val / 3 = v31.val / 3) ∧ C29 = Finset.univ.image (fun t33 : Fin 4 => ((Sum.inl (if f32 t33 = true then v31 else u30, t33) : (Fin 6 × Fin 4) ⊕ Fin 6), true))} ∪ {C34 | ∃ (e35 : Fin 6) (t36 : Fin 4), C34 = {((Sum.inr e35 : (Fin 6 × Fin 4) ⊕ Fin 6), false), ((Sum.inl (((![(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : Fin 6 → Fin 6 × Fin 6) e35).1, t36) : (Fin 6 × Fin 4) ⊕ Fin 6), false), ((Sum.inl (((![(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : Fin 6 → Fin 6 × Fin 6) e35).2, t36) : (Fin 6 × Fin 4) ⊕ Fin 6), false)}} ∪ {C37 | ∃ S38 : Finset (Fin 6), S38.card = 3 ∧ C37 = (Finset.univ.filter (fun e39 : Fin 6 => ((![(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : Fin 6 → Fin 6 × Fin 6) e39).1 ∉ S38 ∧ ((![(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : Fin 6 → Fin 6 × Fin 6) e39).2 ∉ S38)).image (fun e40 : Fin 6 => ((Sum.inr e40 : (Fin 6 × Fin 4) ⊕ Fin 6), true))} → (∃ π22, PEqualNP.ProofComplexity.IsRefutation F21 π22 ∧ ∀ D23 ∈ π22, D23.card ≤ 4) ∧ ¬ ∃ π24, PEqualNP.ProofComplexity.IsRefutation F21 π24 ∧ ∀ D25 ∈ π24, D25.card ≤ 3) := by
  constructor
  · intro F h
    subst F
    exact ⟨cycleUpper, cycleLower⟩
  · intro F h
    subst F
    exact ⟨trianglesUpper, trianglesLower⟩
