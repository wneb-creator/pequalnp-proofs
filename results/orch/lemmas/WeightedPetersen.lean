import WeightedLive

namespace PEqualNP.Outside.L_meta_2592_aux.WeightedPetersen

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open InputSlots Prune WeightedLive

lemma run_input (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (Prune.run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (Prune.run gs (w ++ [_])).getD i false = w.getD i false
    rw [ih _ (by simp; omega), getD_snoc]
    simp [hi]

lemma run_agree (gs : List Gate) (i : ℕ) (noRead : ∀ g ∈ gs, i ∉ g.inputs)
    (u v : List Bool) (hlen : u.length = v.length) (hi : i < u.length)
    (same : ∀ k, k ≠ i → u.getD k false = v.getD k false) :
    ∀ k, k ≠ i → (Prune.run gs u).getD k false = (Prune.run gs v).getD k false := by
  induction gs generalizing u v with
  | nil => exact same
  | cons g gs ih =>
    have hg : g.op.eval (g.inputs.map fun k => u.getD k false) =
        g.op.eval (g.inputs.map fun k => v.getD k false) := by
      congr 1
      apply List.map_congr_left
      intro k hk
      exact same k (fun he => noRead g (by simp) (he ▸ hk))
    apply ih (fun q hq => noRead q (List.mem_cons_of_mem _ hq))
      (u ++ [_]) (v ++ [_]) (by simp [hlen]) (by simp; omega)
    intro k hk
    rw [getD_snoc, getD_snoc, hlen]
    split_ifs <;> first | exact same k hk | exact hg | rfl

lemma ofFn_getD {n : ℕ} (x : Fin n → Bool) (k : ℕ) :
    (List.ofFn x).getD k false = if h : k < n then x ⟨k, h⟩ else false := by
  by_cases h : k < n
  · simp [List.getD_eq_getElem (List.ofFn x) false (by simpa using h), h]
  · simp [List.getD_eq_default (List.ofFn x) false (by simpa using Nat.le_of_not_gt h), h]

def petersen (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def neighbor (i : Fin 10) : Fin 10 :=
  ([1, 0, 1, 2, 0, 0, 1, 2, 3, 4] : List (Fin 10)).getD i.val 0

def low (i : Fin 10) : Fin 10 → Bool := fun j => decide (j = neighbor i)
def high (i : Fin 10) : Fin 10 → Bool := fun j => decide (j = i ∨ j = neighbor i)

lemma witness : ∀ i : Fin 10,
    petersen (low i) = false ∧ petersen (high i) = true ∧
    ∀ j, j ≠ i → low i j = high i j := by decide +kernel

lemma singleton_false : ∀ i : Fin 10,
    petersen (fun j => decide (j = i)) = false := by decide +kernel

lemma output_not_input (C : Circuit)
    (correct : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersen x) (i : Fin 10) :
    C.output ≠ i.val := by
  intro he
  have h := correct (fun j => decide (j = i))
  change (Prune.run C.gates (List.ofFn fun j => decide (j = i))).getD C.output false = _ at h
  rw [he, run_input _ _ i.val (by simp), ofFn_getD, singleton_false] at h
  simp at h

lemma essential (C : Circuit) (hnorm : Normal C)
    (correct : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersen x) :
    ∀ i, i < 10 → i ∈ slots C := by
  intro i hi
  by_contra hnot
  have hno : ∀ g ∈ C.gates, i ∉ g.inputs := by
    intro g hg hm
    apply hnot
    apply List.mem_flatMap.mpr
    refine ⟨g, hg, ?_⟩
    rwa [effective_eq C hnorm g hg]
  let a : Fin 10 := ⟨i, hi⟩
  have he := run_agree C.gates i hno (List.ofFn (low a)) (List.ofFn (high a))
    (by simp) (by simp [hi]) (by
      intro k hk
      rw [ofFn_getD, ofFn_getD]
      split_ifs with h
      · exact (witness a).2.2 ⟨k, h⟩ (fun e => hk (congrArg Fin.val e))
      · rfl) C.output (output_not_input C correct a)
  change C.eval (List.ofFn (low a)) = C.eval (List.ofFn (high a)) at he
  rw [correct, correct, (witness a).1, (witness a).2.1] at he
  contradiction

lemma normalized_unique_reader (C : Circuit) (fan : FanInTwo C)
    (budget : C.size ≤ 19) (hasNot : 1 ≤ NotBracket.notCount C)
    (correct : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersen x) :
    ∃ (D : Circuit) (i : Fin 10) (q : ℕ), FanInTwo D ∧ Normal D ∧ weight D ≤ 19 ∧
      (∀ x : Fin 10 → Bool, D.eval (List.ofFn x) = petersen x) ∧
      q < D.gates.length ∧ i.val ∈ (D.gates.getD q ⟨GateOp.or, []⟩).inputs ∧
      ∀ t, t < D.gates.length → t ≠ q → i.val ∉ (D.gates.getD t ⟨GateOp.or, []⟩).inputs := by
  obtain ⟨D, hfan, hnorm, hweight, heval, hlive⟩ := exists_live 10 C fan
  have hCweight : weight C ≤ 19 := by unfold weight; simp [show NotBracket.notCount C ≠ 0 by omega]; omega
  have hw : weight D ≤ 19 := hweight.trans hCweight
  have hc : ∀ x : Fin 10 → Bool, D.eval (List.ofFn x) = petersen x := fun x => (heval x).trans (correct x)
  have hb : D.size + 1 < 2 * 10 + NotBracket.notCount D := by
    unfold weight at hw
    split_ifs at hw <;> omega
  obtain ⟨i, hi, hone⟩ := input_once D 10 hfan (essential D hnorm hc) hlive hb
  obtain ⟨q, hq, hread, hother⟩ := unique_reader D.gates i hone
  have get_mem : ∀ t, t < D.gates.length → D.gates.getD t ⟨GateOp.or, []⟩ ∈ D.gates := by
    intro t ht
    rw [List.getD_eq_getElem _ _ ht]
    exact List.getElem_mem ht
  refine ⟨D, ⟨i, hi⟩, q, hfan, hnorm, hw, hc, hq, ?_, ?_⟩
  · rwa [effective_eq D hnorm _ (get_mem q hq)] at hread
  · intro t ht hne
    have h := hother t ht hne
    rwa [effective_eq D hnorm _ (get_mem t ht)] at h

end PEqualNP.Outside.L_meta_2592_aux.WeightedPetersen
