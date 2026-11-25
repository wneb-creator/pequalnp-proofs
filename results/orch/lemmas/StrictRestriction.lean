import Restriction
import PEqualNP.Outside.L_meta_7493

namespace PEqualNP.Outside.L_meta_2592_aux.StrictRestriction

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2592_restrict.CircuitProof

def Marked (origins : List (Option ℕ)) (stats : List Stat) (i : ℕ) : Prop :=
  origins.getD i none = none ∧ ∃ b, stats.getD i (Sum.inl false) = Sum.inl b

lemma originConstant_run (n : ℕ) (gs : List Gate) (origins : List (Option ℕ)) (v : ℕ)
    (acc : List Stat × List Gate) (known : OriginConstant origins v acc.1) :
    OriginConstant (gs.foldl originStep origins) v (elim n gs acc).1 := by
  induction gs generalizing origins acc with
  | nil => exact known
  | cons g gs ih =>
    exact ih _ _ (originConstant_step n origins v acc g known)

lemma origin_run_length (gs : List Gate) (origins : List (Option ℕ)) :
    (gs.foldl originStep origins).length = origins.length + gs.length := by
  induction gs generalizing origins with
  | nil => simp
  | cons g gs ih =>
    simpa [originStep, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (ih (originStep origins g))

lemma stats_run_length (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) :
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simpa [elim, elimStep, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (ih (elimStep n acc g))

lemma origin_run_prefix (gs : List Gate) (origins : List (Option ℕ)) (i : ℕ)
    (before : i < origins.length) :
    (gs.foldl originStep origins).getD i none = origins.getD i none := by
  induction gs generalizing origins with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [originStep]; omega)]
    exact List.getD_append _ _ _ _ before

lemma stats_run_prefix (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) (i : ℕ)
    (before : i < acc.1.length) :
    (elim n gs acc).1.getD i (Sum.inl false) = acc.1.getD i (Sum.inl false) := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    change (elim n gs (elimStep n acc g)).1.getD i _ = _
    rw [ih _ (by simp [elimStep]; omega)]
    exact List.getD_append _ _ _ _ before

lemma elim_append (n : ℕ) (pre post : List Gate) (acc : List Stat × List Gate) :
    elim n (pre ++ post) acc = elim n post (elim n pre acc) := by
  simp only [elim, List.foldl_append]

lemma cutCost_append (origins : List (Option ℕ)) (v : ℕ) (pre post : List Gate) :
    cutCost origins v (pre ++ post) =
      cutCost origins v pre + cutCost (pre.foldl originStep origins) v post := by
  induction pre generalizing origins with
  | nil => simp [cutCost]
  | cons g gs ih => simp only [List.cons_append, cutCost, List.foldl_cons, ih, Nat.add_assoc]

lemma count_append (pre post : List Gate) :
    nonNotCount (pre ++ post) = nonNotCount pre + nonNotCount post := by
  simp [nonNotCount]

lemma strict_saving_at (n : ℕ) (pre post : List Gate) (g : Gate)
    (origins : List (Option ℕ)) (v : ℕ) (acc : List Stat × List Gate)
    (ok : ∀ a ∈ pre ++ g :: post, Ok a) (known : OriginConstant origins v acc.1)
    (notNot : isNotGate g.op = false)
    (uncharged : cutCharge (pre.foldl originStep origins) v g = 0)
    (gone : (simplify g.op (n + (elim n pre acc).2.length)
      (g.inputs.map fun i => (elim n pre acc).1.getD i (Sum.inl false))).1 = none) :
    nonNotCount (elim n (pre ++ g :: post) acc).2 +
      cutCost origins v (pre ++ g :: post) + 1 ≤
        nonNotCount acc.2 + nonNotCount (pre ++ g :: post) := by
  have before := elim_cut_cost n pre origins v acc
    (by intro a ha; exact ok a (List.mem_append_left _ ha)) known
  have knownPre := originConstant_run n pre origins v acc known
  have knownNext := originConstant_step n (pre.foldl originStep origins) v
    (elim n pre acc) g knownPre
  have after := elim_cut_cost n post (originStep (pre.foldl originStep origins) g) v
    (elimStep n (elim n pre acc) g)
    (by intro a ha; exact ok a (List.mem_append_right _ (List.mem_cons_of_mem _ ha)))
    knownNext
  have unchanged : (elimStep n (elim n pre acc) g).2 = (elim n pre acc).2 := by
    change (elim n pre acc).2 ++ _ = _
    rw [gone]
    simp
  rw [unchanged] at after
  rw [elim_append, cutCost_append]
  change nonNotCount (elim n post (elimStep n (elim n pre acc) g)).2 +
    (cutCost origins v pre + (cutCharge (pre.foldl originStep origins) v g +
      cutCost (originStep (pre.foldl originStep origins) g) v post)) + 1 ≤ _
  rw [uncharged, count_append]
  have count : nonNotCount (g :: post) = nonNotCount post + 1 := by
    simp [nonNotCount, notNot]
  rw [count]
  omega

lemma marked_gate (n m : ℕ) (origins : List (Option ℕ)) (v : ℕ)
    (acc : List Stat × List Gate) (g : Gate) (clean : CleanGate m g)
    (known : OriginConstant origins v acc.1)
    (noExtra : isNotGate g.op = false → cutCharge origins v g = 0 →
      (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 ≠ none)
    (markedRead : ∃ i ∈ g.inputs, Marked origins acc.1 i) :
    (match g.op, g.inputs with | .not, i :: _ => origins.getD i none | _, _ => none) = none ∧
      ∃ b, (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2 = Sum.inl b := by
  rcases clean with ⟨op, a, _, inputs⟩ | ⟨op, a, b, _, _, inputs⟩
  · obtain ⟨i, member, mark⟩ := markedRead
    have eq : i = a := by simpa only [inputs, List.mem_singleton] using member
    subst i
    obtain ⟨c, hc⟩ := mark.2
    refine ⟨by simpa only [op, inputs] using mark.1, !c, ?_⟩
    simp only [op, inputs, List.map_cons, List.map_nil, simplify, hc, simpNot]
  · have notNot : isNotGate g.op = false := by
      rcases op with op | op <;> simp [op, isNotGate]
    obtain ⟨i, member, mark⟩ := markedRead
    obtain ⟨c, hc⟩ := mark.2
    have gone : (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
      apply simplify_count g.op _ _ (Or.elim op (fun h => Or.inl h) (fun h => Or.inr (Or.inl h)))
        (by simp [inputs]) (by intro hn; simp [hn, isNotGate] at notNot)
      exact ⟨c, List.mem_map.mpr ⟨i, member, hc⟩⟩
    have charged : cutCharge origins v g = 1 := by
      have nz : cutCharge origins v g ≠ 0 := fun hz => noExtra notNot hz gone
      cases h : readsOrigin origins v g <;> simp_all [cutCharge]
    have reads : readsOrigin origins v g = true := by
      cases h : readsOrigin origins v g <;> simp_all [cutCharge]
    obtain ⟨j, memberJ, originJ⟩ := List.any_eq_true.mp reads
    have originJ' : origins.getD j none = some v := of_decide_eq_true originJ
    obtain ⟨d, hd⟩ := known.2 j originJ'
    have distinct : i ≠ j := by
      intro same
      have absent := mark.1
      rw [same, originJ'] at absent
      cases absent
    have pair : (i = a ∧ j = b) ∨ (i = b ∧ j = a) := by
      simp only [inputs, List.mem_cons, List.mem_nil_iff, or_false] at member memberJ
      rcases member with rfl | rfl <;> rcases memberJ with rfl | rfl <;> simp_all
    rcases pair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases op with op | op <;>
      simp only [op, inputs, List.map_cons, List.map_nil, simplify, hc, hd, simpAnd, simpOr] <;>
      exact ⟨trivial, _, rfl⟩

end PEqualNP.Outside.L_meta_2592_aux.StrictRestriction
