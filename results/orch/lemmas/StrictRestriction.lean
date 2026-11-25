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


namespace PEqualNP.Outside.L_meta_2592_aux.StrictRestriction

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2592_restrict.CircuitProof
open PEqualNP.Outside.L_meta_7493.PetersenCutTrace

lemma origin_before_gate (pre post : List Gate) (g : Gate) (origins : List (Option ℕ))
    (i : ℕ) (before : i < origins.length + pre.length) :
    ((pre ++ g :: post).foldl originStep origins).getD i none =
      (pre.foldl originStep origins).getD i none := by
  rw [List.foldl_append]
  apply origin_run_prefix
  simpa only [origin_run_length] using before

lemma stats_before_gate (n : ℕ) (pre post : List Gate) (g : Gate)
    (acc : List Stat × List Gate) (i : ℕ) (before : i < acc.1.length + pre.length) :
    (elim n (pre ++ g :: post) acc).1.getD i (Sum.inl false) =
      (elim n pre acc).1.getD i (Sum.inl false) := by
  rw [elim_append]
  apply stats_run_prefix
  simpa only [stats_run_length] using before

lemma origin_at_gate (pre post : List Gate) (g : Gate) (origins : List (Option ℕ)) :
    ((pre ++ g :: post).foldl originStep origins).getD (origins.length + pre.length) none =
      (match g.op, g.inputs with
      | .not, i :: _ => (pre.foldl originStep origins).getD i none
      | _, _ => none) := by
  rw [List.foldl_append, List.foldl_cons]
  rw [origin_run_prefix post _ _ (by simp [originStep, origin_run_length])]
  have length := origin_run_length pre origins
  rw [← length]
  exact getD_snoc_eq _ _ _

lemma stats_at_gate (n : ℕ) (pre post : List Gate) (g : Gate) (acc : List Stat × List Gate) :
    (elim n (pre ++ g :: post) acc).1.getD (acc.1.length + pre.length) (Sum.inl false) =
      (simplify g.op (n + (elim n pre acc).2.length)
        (g.inputs.map fun i => (elim n pre acc).1.getD i (Sum.inl false))).2 := by
  rw [elim_append]
  change (elim n post (elimStep n (elim n pre acc) g)).1.getD _ _ = _
  rw [stats_run_prefix n post _ _ (by simp [elimStep, stats_run_length])]
  have length := stats_run_length n pre acc
  rw [← length]
  exact getD_snoc_eq _ _ _

lemma marked_final_reader (n k : ℕ) (gs : List Gate) (origins : List (Option ℕ))
    (v : ℕ) (acc : List Stat × List Gate) (originLength : origins.length = k)
    (statsLength : acc.1.length = k) (clean : CleanL k gs)
    (known : OriginConstant origins v acc.1)
    (noExtra : ∀ pre g post, gs = pre ++ g :: post →
      isNotGate g.op = false → cutCharge (pre.foldl originStep origins) v g = 0 →
      (simplify g.op (n + (elim n pre acc).2.length)
        (g.inputs.map fun i => (elim n pre acc).1.getD i (Sum.inl false))).1 ≠ none)
    (a b : Fin (k + gs.length)) (edge : readEdge gs a b)
    (marked : Marked (gs.foldl originStep origins) (elim n gs acc).1 a.val) :
    Marked (gs.foldl originStep origins) (elim n gs acc).1 b.val := by
  obtain ⟨p, g, atGate, target, reads⟩ := edge
  have gateClean := clean p g atGate
  have before := gateClean.lt a.val reads
  obtain ⟨pre, post, split, length⟩ := split_at gs p g atGate
  have localMark : Marked (pre.foldl originStep origins) (elim n pre acc).1 a.val := by
    rcases marked with ⟨originNone, ⟨c, status⟩⟩
    simp only [split] at originNone status
    rw [origin_before_gate pre post g origins a.val (by omega)] at originNone
    rw [stats_before_gate n pre post g acc a.val (by omega)] at status
    exact ⟨originNone, c, status⟩
  have propagated := marked_gate n (k + p) (pre.foldl originStep origins) v (elim n pre acc) g
    gateClean (originConstant_run n pre origins v acc known)
    (noExtra pre g post split) ⟨a.val, reads, localMark⟩
  refine ⟨?_, ?_⟩
  · rw [target, split, ← length, ← originLength, origin_at_gate]
    exact propagated.1
  · obtain ⟨c, status⟩ := propagated.2
    refine ⟨c, ?_⟩
    rw [target, split, ← length, ← statsLength, stats_at_gate]
    exact status

lemma marked_reaches_output (n k : ℕ) (gs : List Gate) (origins : List (Option ℕ))
    (v : ℕ) (acc : List Stat × List Gate) (originLength : origins.length = k)
    (statsLength : acc.1.length = k) (clean : CleanL k gs)
    (known : OriginConstant origins v acc.1)
    (noExtra : ∀ pre g post, gs = pre ++ g :: post →
      isNotGate g.op = false → cutCharge (pre.foldl originStep origins) v g = 0 →
      (simplify g.op (n + (elim n pre acc).2.length)
        (g.inputs.map fun i => (elim n pre acc).1.getD i (Sum.inl false))).1 ≠ none)
    (out : Fin (k + gs.length))
    (live : ∀ w : Fin (k + gs.length), w ≠ out → ∃ z, readEdge gs w z)
    (seed : Fin (k + gs.length))
    (seedMarked : Marked (gs.foldl originStep origins) (elim n gs acc).1 seed.val) :
    Marked (gs.foldl originStep origins) (elim n gs acc).1 out.val := by
  classical
  let marked := Finset.univ.filter (fun w : Fin (k + gs.length) =>
    Marked (gs.foldl originStep origins) (elim n gs acc).1 w.val)
  have nonempty : marked.Nonempty := ⟨seed, Finset.mem_filter.mpr ⟨Finset.mem_univ _, seedMarked⟩⟩
  let peak := marked.max' nonempty
  have peakMem : peak ∈ marked := Finset.max'_mem _ _
  have peakMarked := (Finset.mem_filter.mp peakMem).2
  by_cases eqOut : peak = out
  · simpa only [eqOut] using peakMarked
  · obtain ⟨next, edge⟩ := live peak eqOut
    have nextMarked := marked_final_reader n k gs origins v acc originLength statsLength
      clean known noExtra peak next edge peakMarked
    have nextMem : next ∈ marked := Finset.mem_filter.mpr ⟨Finset.mem_univ _, nextMarked⟩
    have le : next ≤ peak := Finset.le_max' _ _ nextMem
    have lt : peak < next := read_order clean edge
    exact False.elim ((not_lt_of_ge le) lt)

lemma strict_saving_of_marked (n k : ℕ) (gs : List Gate) (origins : List (Option ℕ))
    (v : ℕ) (acc : List Stat × List Gate) (originLength : origins.length = k)
    (statsLength : acc.1.length = k) (clean : CleanL k gs)
    (known : OriginConstant origins v acc.1)
    (out : Fin (k + gs.length))
    (live : ∀ w : Fin (k + gs.length), w ≠ out → ∃ z, readEdge gs w z)
    (seed : Fin (k + gs.length))
    (seedMarked : Marked (gs.foldl originStep origins) (elim n gs acc).1 seed.val)
    (outputNotConstant : ¬ ∃ b, (elim n gs acc).1.getD out.val (Sum.inl false) = Sum.inl b) :
    nonNotCount (elim n gs acc).2 + cutCost origins v gs + 1 ≤
      nonNotCount acc.2 + nonNotCount gs := by
  by_contra fails
  have noExtra : ∀ pre g post, gs = pre ++ g :: post →
      isNotGate g.op = false → cutCharge (pre.foldl originStep origins) v g = 0 →
      (simplify g.op (n + (elim n pre acc).2.length)
        (g.inputs.map fun i => (elim n pre acc).1.getD i (Sum.inl false))).1 ≠ none := by
    intro pre g post split notNot uncharged gone
    apply fails
    rw [split]
    exact strict_saving_at n pre post g origins v acc
      (by intro a ha; exact (clean_nok k gs clean a (split ▸ ha)).1)
      known notNot uncharged gone
  have reaches := marked_reaches_output n k gs origins v acc originLength statsLength clean
    known noExtra out live seed seedMarked
  exact outputNotConstant reaches.2

end PEqualNP.Outside.L_meta_2592_aux.StrictRestriction


namespace PEqualNP.Outside.L_meta_2592_aux.StrictRestriction

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2592_restrict.CircuitProof
open PEqualNP.Outside.L_meta_7493.PetersenCutTrace

lemma annihilating_status (op : GateOp) (c : Bool) (m : ℕ) (a b : Stat)
    (annihilates : (op = GateOp.and ∧ c = false) ∨ (op = GateOp.or ∧ c = true))
    (fixed : a = Sum.inl c ∨ b = Sum.inl c) :
    (simplify op m [a, b]).2 = Sum.inl c := by
  rcases annihilates with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases fixed with rfl | rfl
  · cases b <;> simp [simplify, simpAnd]
  · cases a <;> simp [simplify, simpAnd]
  · cases b <;> simp [simplify, simpOr]
  · cases a <;> simp [simplify, simpOr]

lemma marked_of_constant_binary (n k : ℕ) (pre post : List Gate) (g : Gate)
    (origins : List (Option ℕ)) (acc : List Stat × List Gate)
    (originLength : origins.length = k) (statsLength : acc.1.length = k)
    (notNot : isNotGate g.op = false)
    (constant : ∃ b, (simplify g.op (n + (elim n pre acc).2.length)
      (g.inputs.map fun i => (elim n pre acc).1.getD i (Sum.inl false))).2 = Sum.inl b) :
    Marked ((pre ++ g :: post).foldl originStep origins)
      (elim n (pre ++ g :: post) acc).1 (k + pre.length) := by
  refine ⟨?_, ?_⟩
  · rw [← originLength, origin_at_gate]
    cases op : g.op <;> simp_all [isNotGate]
  · rw [← statsLength, stats_at_gate]
    exact constant

lemma strict_restriction_with_marked (n k : ℕ) (C : Circuit) (fan : FanInTwo C)
    (seedStats : List Stat) (origins : List (Option ℕ)) (v : ℕ)
    (valuation : (Fin n → Bool) → (Fin k → Bool))
    (initial : ∀ x : Fin n → Bool,
      Inv n (List.ofFn x) (List.ofFn (valuation x)) (seedStats, []))
    (known : OriginConstant origins v seedStats)
    (nonconstant : ∃ x y : Fin n → Bool,
      C.eval (List.ofFn (valuation x)) ≠ C.eval (List.ofFn (valuation y)))
    (clean : CleanL k C.gates) (outValid : C.output < k + C.gates.length)
    (live : ∀ w : Fin (k + C.gates.length), w ≠ ⟨C.output, outValid⟩ →
      ∃ z, readEdge C.gates w z)
    (source : Fin (k + C.gates.length))
    (marked : Marked (C.gates.foldl originStep origins)
      (elim n C.gates (seedStats, [])).1 source.val) :
    ∃ D : Circuit, FanInTwo D ∧
      nonNotCount D.gates + cutCost origins v C.gates + 1 ≤ nonNotCount C.gates ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn (valuation x)) := by
  let acc := elim n C.gates (seedStats, [])
  have ok : ∀ g ∈ C.gates, Ok g := fan
  have statsLength : seedStats.length = k := by
    simpa only [List.length_ofFn] using (initial (fun _ => false)).1
  have originLength : origins.length = k := known.1.trans statsLength
  have resultInv (x : Fin n → Bool) :
      Inv n (List.ofFn x) (wiresFrom C.gates (List.ofFn (valuation x))) acc :=
    inv_elim n _ (by simp) C.gates _ _ ok (initial x)
  have value (x : Fin n → Bool) :
      (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn x)) =
        C.eval (List.ofFn (valuation x)) := by
    exact (resultInv x).2 C.output |>.2
  have notConstant : ¬ ∃ b, acc.1.getD C.output (Sum.inl false) = Sum.inl b := by
    rintro ⟨b, outputStat⟩
    obtain ⟨x, y, different⟩ := nonconstant
    apply different
    rw [← value x, ← value y, outputStat]
    rfl
  have budget := strict_saving_of_marked n k C.gates origins v (seedStats, [])
    originLength statsLength clean known ⟨C.output, outValid⟩ live source marked notConstant
  cases outputStat : acc.1.getD C.output (Sum.inl false) with
  | inl b => exact False.elim (notConstant ⟨b, outputStat⟩)
  | inr j =>
    refine ⟨⟨acc.2, j⟩, ?_, ?_, ?_⟩
    · have newClean := clean_elim n (List.ofFn (fun _ : Fin n => false)) (by simp)
        C.gates _ _ ok (initial (fun _ => false)) (by intro p g hp; simp at hp)
      intro g hg
      exact (clean_nok n acc.2 newClean g hg).1
    · simpa only [nonNotCount, List.countP_nil, Nat.zero_add] using budget
    · intro x
      change (wiresFrom acc.2 (List.ofFn x)).getD j false = _
      simpa only [outputStat, Stat.val] using value x

end PEqualNP.Outside.L_meta_2592_aux.StrictRestriction
