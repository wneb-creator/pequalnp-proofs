import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def ptEdges : List (Fin 10 × Fin 10) :=
  [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7),
    (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)]

def ptFun (x : Fin 10 → Bool) : Bool :=
  ptEdges.any fun e => x e.1 && x e.2

lemma ptFun_eq (x : Fin 10 → Bool) :
    ptFun x = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
      x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
      x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 ||
      x 8 && x 5) := by
  simp [ptFun, ptEdges, Bool.or_assoc]

def pt20 : Circuit :=
  ⟨[⟨.or, [0, 2]⟩,
    ⟨.or, [10, 6]⟩,
    ⟨.and, [1, 11]⟩,
    ⟨.or, [2, 4]⟩,
    ⟨.or, [13, 8]⟩,
    ⟨.and, [3, 14]⟩,
    ⟨.or, [0, 9]⟩,
    ⟨.and, [4, 16]⟩,
    ⟨.or, [0, 7]⟩,
    ⟨.or, [18, 8]⟩,
    ⟨.and, [5, 19]⟩,
    ⟨.or, [9, 8]⟩,
    ⟨.and, [6, 21]⟩,
    ⟨.or, [2, 9]⟩,
    ⟨.and, [7, 23]⟩,
    ⟨.or, [12, 15]⟩,
    ⟨.or, [25, 17]⟩,
    ⟨.or, [26, 20]⟩,
    ⟨.or, [27, 22]⟩,
    ⟨.or, [28, 24]⟩], 29⟩

lemma pt20_size : pt20.size = 20 := rfl

lemma pt20_monotone : Monotone2 pt20 := by
  simp [Monotone2, pt20]

lemma pt20_fanInTwo : FanInTwo pt20 := by
  simp [FanInTwo, pt20]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
lemma pt20_eval : ∀ x : Fin 10 → Bool, pt20.eval (List.ofFn x) = ptFun x := by
  intro x
  have hinput : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9] := rfl
  have distrib (a b c : Bool) : (a && (b || c)) = (a && b || a && c) := by
    cases a <;> cases b <;> cases c <;> rfl
  rw [hinput]
  simp [pt20, Circuit.eval, Circuit.wires, GateOp.eval, ptFun, ptEdges, distrib]
  ac_rfl

lemma pt20_witness : HasCircuitSize 10 ptFun 20 :=
  ⟨pt20, pt20_fanInTwo, Nat.le_of_eq pt20_size, pt20_eval⟩

def ptIndependent (S : Finset (Fin 10)) : Prop :=
  ∀ e ∈ ptEdges, ¬ (e.1 ∈ S ∧ e.2 ∈ S)

def ptCover (S : Finset (Fin 10)) : Prop :=
  ∀ e ∈ ptEdges, e.1 ∈ S ∨ e.2 ∈ S

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
lemma pt_independent_bound : ∀ S : Finset (Fin 10), ptIndependent S → S.card ≤ 4 := by
  unfold ptIndependent
  decide

lemma pt_independent_four :
    ptIndependent ({0, 2, 8, 9} : Finset (Fin 10)) ∧
      ({0, 2, 8, 9} : Finset (Fin 10)).card = 4 := by
  unfold ptIndependent
  decide

lemma pt_cover_bound (S : Finset (Fin 10)) (hS : ptCover S) : 6 ≤ S.card := by
  have hI : ptIndependent Sᶜ := by
    intro e he hmem
    rcases hS e he with h | h
    · exact (Finset.mem_compl.mp hmem.1) h
    · exact (Finset.mem_compl.mp hmem.2) h
  have hb := pt_independent_bound Sᶜ hI
  have hc : Sᶜ.card = 10 - S.card := by simpa using Finset.card_compl S
  have hs : S.card ≤ 10 := by simpa using Finset.card_le_univ S
  omega

lemma pt_cover_six :
    ptCover ({1, 3, 4, 5, 6, 7} : Finset (Fin 10)) ∧
      ({1, 3, 4, 5, 6, 7} : Finset (Fin 10)).card = 6 := by
  unfold ptCover
  decide

lemma input_not_irrelevant {n : ℕ} (i : Fin n)
    (H : (Fin n → Bool) → Bool → Bool)
    (hignore : ∀ (x : Fin n → Bool) (b z : Bool), H (Function.update x i b) z = H x z)
    (hmono : Monotone (fun x => H x (!(x i))))
    (hgate : ∀ x, Monotone (H x)) :
    ∀ x, H x false = H x true := by
  intro x
  apply le_antisymm
  · exact hgate x (by decide)
  · have hab : Function.update x i false ≤ Function.update x i true := by
      intro j
      by_cases hj : j = i
      · subst j
        simp
      · simp [Function.update_of_ne hj]
    have h := hmono hab
    simpa only [Function.update_self, Bool.not_false, Bool.not_true, hignore] using h

lemma input_not_replace_false {n : ℕ} (i : Fin n)
    (H : (Fin n → Bool) → Bool → Bool)
    (hignore : ∀ (x : Fin n → Bool) (b z : Bool), H (Function.update x i b) z = H x z)
    (hmono : Monotone (fun x => H x (!(x i))))
    (hgate : ∀ x, Monotone (H x)) :
    ∀ x, H x (!(x i)) = H x false := by
  intro x
  cases hi : x i
  · simpa only [Bool.not_false] using (input_not_irrelevant i H hignore hmono hgate x).symm
  · simp

lemma input_not_cannot_compute {n : ℕ} (i : Fin n)
    (f : (Fin n → Bool) → Bool) (H : (Fin n → Bool) → Bool → Bool)
    (hignore : ∀ (x : Fin n → Bool) (b z : Bool), H (Function.update x i b) z = H x z)
    (hf : Monotone f)
    (hdep : ∃ x, f (Function.update x i false) ≠ f (Function.update x i true))
    (hgate : ∀ x, Monotone (H x)) :
    ¬ ∀ x, H x (!(x i)) = f x := by
  intro correct
  have hmono : Monotone (fun x => H x (!(x i))) := by
    simpa only [correct] using hf
  obtain ⟨x, hdiff⟩ := hdep
  apply hdiff
  rw [← correct, ← correct]
  simpa only [Function.update_self, Bool.not_false, Bool.not_true, hignore] using
    (input_not_irrelevant i H hignore hmono hgate x).symm

lemma ptFun_monotone : Monotone ptFun := by
  intro x y hxy
  apply Bool.le_iff_imp.mpr
  intro hx
  obtain ⟨e, he, hval⟩ := List.any_eq_true.mp hx
  apply List.any_eq_true.mpr
  refine ⟨e, he, ?_⟩
  have hs : x e.1 = true ∧ x e.2 = true := by simpa using hval
  simp only [Bool.and_eq_true]
  exact ⟨(Bool.le_iff_imp.mp (hxy e.1)) hs.1,
    (Bool.le_iff_imp.mp (hxy e.2)) hs.2⟩

set_option maxRecDepth 2000 in
set_option maxHeartbeats 400000 in
lemma ptFun_essential : ∀ i : Fin 10, ∃ x : Fin 10 → Bool,
    ptFun (Function.update x i false) ≠ ptFun (Function.update x i true) := by
  let neighbor : Fin 10 → Fin 10 := ![1, 0, 1, 2, 0, 0, 1, 2, 3, 4]
  have cert : ∀ i : Fin 10,
      ptFun (Function.update (fun j => decide (j = neighbor i)) i false) = false ∧
      ptFun (Function.update (fun j => decide (j = neighbor i)) i true) = true := by
    decide
  intro i
  refine ⟨fun j => decide (j = neighbor i), ?_⟩
  rw [(cert i).1, (cert i).2]
  decide

lemma pt_input_not_cannot_compute (i : Fin 10)
    (H : (Fin 10 → Bool) → Bool → Bool)
    (hignore : ∀ (x : Fin 10 → Bool) (b z : Bool), H (Function.update x i b) z = H x z)
    (hgate : ∀ x, Monotone (H x)) :
    ¬ ∀ x, H x (!(x i)) = ptFun x :=
  input_not_cannot_compute i ptFun H hignore ptFun_monotone (ptFun_essential i) hgate

end PEqualNP.Outside.L_meta_2592
