import FirstMerge

namespace PEqualNP.Outside.L_meta_2592_aux.FirstMerge

open PEqualNP.CircuitLowerBounds

lemma cutCost_append (origins : List (Option ℕ)) (v : ℕ) (pre post : List Gate) :
    cutCost origins v (pre ++ post) =
      cutCost origins v pre + cutCost (pre.foldl originStep origins) v post := by
  induction pre generalizing origins with
  | nil => simp [cutCost]
  | cons g gs ih => simp only [List.cons_append, cutCost, List.foldl_cons, ih, Nat.add_assoc]

lemma cutCost_not_prefix (origins : List (Option ℕ)) (v : ℕ) (pre : List Gate)
    (allNot : ∀ g ∈ pre, g.op = GateOp.not) : cutCost origins v pre = 0 := by
  induction pre generalizing origins with
  | nil => rfl
  | cons g gs ih =>
    have head := allNot g (by simp)
    have tail := ih (originStep origins g) (by intro a ha; exact allNot a (by simp [ha]))
    simp [cutCost, cutCharge, head, isNotGate, tail]

lemma suffix_cost_zero (origins : List (Option ℕ)) (v : ℕ) (pre post : List Gate) (g : Gate)
    (cost : cutCost origins v (pre ++ g :: post) ≤ 1)
    (notFlag : isNotGate g.op = false)
    (reads : readsOrigin (pre.foldl originStep origins) v g = true) :
    cutCost (originStep (pre.foldl originStep origins) g) v post = 0 := by
  rw [cutCost_append] at cost
  simp only [cutCost, cutCharge, notFlag, reads, Bool.false_eq_true, Bool.true_eq,
    ↓reduceIte] at cost
  omega

lemma agreeOutside_initial (n : ℕ) (u v : Fin n) (x y : Fin n → Bool)
    (agree : ∀ i : Fin n, i ≠ u → i ≠ v → x i = y i) :
    AgreeOutside (List.ofFn (fun i : Fin n => some i.val)) u.val v.val
      (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp, by simp, ?_⟩
  intro i notU notV
  by_cases before : i < n
  · have neU : i ≠ u.val := by simpa [before] using notU
    have neV : i ≠ v.val := by simpa [before] using notV
    have h := agree ⟨i, before⟩ (by intro eq; exact neU (congrArg Fin.val eq))
      (by intro eq; exact neV (congrArg Fin.val eq))
    simpa [before] using h
  · simp [List.getD_eq_default, List.length_ofFn, Nat.le_of_not_gt before]

end PEqualNP.Outside.L_meta_2592_aux.FirstMerge
