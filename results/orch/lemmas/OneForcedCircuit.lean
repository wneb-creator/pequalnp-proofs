import PositiveOrder

namespace PEqualNP.Outside.L_meta_2373.Live1024.OneForcedBank
open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_2373 LiftSeventeen OneNotFirstAnd

lemma raw_state_eq {S : Finset Sig} {k : Nat} (run : Live false graph k S)
    (sub : ∀ w ∈ S, w ∈ inputs) : S = inputs.toFinset := by
  ext w
  constructor
  · exact fun hw => List.mem_toFinset.mpr (sub w hw)
  · intro hw
    obtain ⟨i, rfl⟩ := input_index w (List.mem_toFinset.mp hw)
    apply raw_required run inputs (input i) sub (absentRow i) (presentRow i)
      (requiredInputs.1 i)
    intro v hv hn
    obtain ⟨j, rfl⟩ := input_index v hv
    apply requiredInputs.2 i j
    rintro rfl
    exact hn rfl

lemma circuit_dichotomy (h : Sig) (a : Fin 10) (forces : forcesInput h a)
    (C : Circuit) (pre mid post : List Gate) (g : Gate)
    (gatesEq : C.gates = pre ++ [g] ++ mid ++
      [{op := .not, inputs := [10 + pre.length]}] ++ post)
    (value : gv (execute pre inputs) g = h)
    (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (monoPre : ∀ q ∈ pre, isNot q = false) (monoG : isNot g = false)
    (monoMid : ∀ q ∈ mid, isNot q = false)
    (monoPost : ∀ q ∈ post, isNot q = false)
    (computes : PEqualNP.MetaComplexity.circuitFun 10 C = edge) :
    20 ≤ C.size ∨ ∃ k, k + 1 ≤ C.size ∧ Live false graph k inputs.toFinset := by
  let ng : Gate := {op := .not, inputs := [10 + pre.length]}
  let free := [h, neg h]
  let wp := execute pre inputs
  let wa := wp ++ [gv wp g]
  let wm := execute mid wa
  let wn := wm ++ [gv wm ng]
  have nv : gv wm ng = neg h := OneNotForcedPair.stored_gate_value pre mid g h value
  have whole : execute C.gates inputs = execute post wn := by
    rw [gatesEq]
    simp only [execute, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rfl
  have output : graph ∈ execute post wn := whole ▸ output_member C legal computes
  have legalPre : ∀ q ∈ pre, q.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      q.inputs.length ≤ 2 := fun q hq => legal q (by rw [gatesEq]; simp [hq])
  have legalMid : ∀ q ∈ mid, q.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      q.inputs.length ≤ 2 := fun q hq => legal q (by rw [gatesEq]; simp [hq])
  have legalPrefix : ∀ q ∈ pre ++ [g] ++ mid,
      q.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ q.inputs.length ≤ 2 := by
    intro q hq
    exact legal q (by rw [gatesEq]; simp only [List.mem_append] at hq ⊢; tauto)
  have monoPrefix : ∀ q ∈ pre ++ [g] ++ mid, isNot q = false := by
    intro q hq
    simp only [List.mem_append, List.mem_singleton] at hq
    rcases hq with (hq | rfl) | hq
    · exact monoPre q hq
    · exact monoG
    · exact monoMid q hq
  have prefixEq : execute (pre ++ [g] ++ mid) inputs = wm := by
    simp only [execute, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rfl
  have size : C.size = pre.length + mid.length + post.length + 2 := by
    simp [Circuit.size, gatesEq]
    omega
  obtain ⟨k1, S1, bound1, run1, sub1⟩ := PositiveTail.positive_tail_extract post wn
    (fun q hq => legal q (by rw [gatesEq]; simp [hq])) monoPost graph_proper output
  by_cases used : neg h ∈ S1
  · left
    have hp := proper_neg (live_entries_proper run1 (neg h) used)
    obtain ⟨r, on, off⟩ := neg_drop_rows h a forces hp
    have prefixOrder := positive_execute_order 0 r (pre ++ [g]) inputs
      (fun q hq => legalPrefix q (List.mem_append_left mid hq))
      (fun q hq => monoPrefix q (List.mem_append_left mid hq)) (inputs_order r)
    have waOrder : bankOrder 0 r wa := by
      simpa only [wa, wp, execute, List.foldl_append, List.foldl_cons, List.foldl_nil] using prefixOrder
    have subN : ∀ w ∈ S1, w ∈ execute mid wa ++ free := by
      intro w hw
      have hm := sub1 w hw
      have old : w ∈ wm ∨ w = neg h := by simpa [wn, nv] using hm
      rcases old with old | rfl
      · exact List.mem_append_left free old
      · simp [free]
    obtain ⟨k2, S2, bound2, run2, sub2, kept2⟩ := pull_positive_chunk_keep mid wa free
      legalMid monoMid (positive_prefix_safe 0 r mid wa (neg h) legalMid monoMid waOrder on off)
      run1 subN used
    have knownG : gv wp g ∈ free := by simp [free, wp, value]
    have subG := FreeBank.skip_free_gate wp free g knownG sub2
    obtain ⟨k3, S3, bound3, run3, sub3, kept3⟩ := pull_positive_chunk_keep pre inputs free
      legalPre monoPre (positive_prefix_safe 0 r pre inputs (neg h) legalPre monoPre
        (inputs_order r) on off) run2 subG kept2
    have subset : S3 ⊆ OneNotForcedPair.bank h := by
      intro w hw
      have mem := sub3 w hw
      simpa [free, OneNotForcedPair.bank, List.mem_append, List.mem_cons,
        List.mem_singleton, or_assoc, or_left_comm, or_comm] using mem
    have lower := positive_tail_lower_used h a forces subset kept3 run3
    omega
  · right
    have subW : ∀ w ∈ S1, w ∈ wm := by
      intro w hw
      have mem := sub1 w hw
      have hn : w ≠ neg h := fun eq => used (eq ▸ hw)
      simpa [wn, nv, hn] using mem
    obtain ⟨k2, S2, bound2, run2, sub2⟩ := FreeBank.pull_positive_chunk (pre ++ [g] ++ mid)
      inputs [] legalPrefix monoPrefix run1 (by simpa only [prefixEq, List.append_nil] using subW)
    have sub : ∀ w ∈ S2, w ∈ inputs := by simpa only [List.append_nil] using sub2
    refine ⟨k2, ?_, raw_state_eq run2 sub ▸ run2⟩
    simp only [List.length_append, List.length_singleton] at bound2
    omega

lemma dichotomy_small {C : Circuit} (small : C.size ≤ 19)
    (alternative : 20 ≤ C.size ∨ ∃ k, k + 1 ≤ C.size ∧ Live false graph k inputs.toFinset) :
    Live false graph 18 inputs.toFinset := by
  rcases alternative with large | ⟨k, bound, run⟩
  · omega
  · have lower := monotone_rt_lower run
    have eq : k = 18 := by omega
    exact eq ▸ run

end PEqualNP.Outside.L_meta_2373.Live1024.OneForcedBank
