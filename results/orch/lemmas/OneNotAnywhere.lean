import OneNotOrderedCircuit
import FreeBankExtraction

namespace PEqualNP.Outside.L_meta_2373.Live1024.OneNotFirstAnd
open PEqualNP.CircuitLowerBounds

lemma execute_prefix (gs : List Gate) (w : List Sig) : ∃ extra, execute gs w = w ++ extra := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp [execute]⟩
  | cons g gs ih =>
    obtain ⟨extra, he⟩ := ih (w ++ [gv w g])
    exact ⟨gv w g :: extra, by simpa [execute, List.append_assoc] using he⟩

lemma execute_length (gs : List Gate) (w : List Sig) :
    (execute gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [execute]
  | cons g gs ih =>
    change (execute gs (w ++ [gv w g])).length = _
    rw [ih]
    simp [Nat.add_assoc, Nat.add_comm]

lemma getD_append_left (w v : List Sig) (i : Nat) (hi : i < w.length) :
    (w ++ v).getD i zero = w.getD i zero := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_slot (w v : List Sig) (a : Sig) :
    ((w ++ [a]) ++ v).getD w.length zero = a := by
  induction w with
  | nil => simp
  | cons b w ih => simpa only [List.cons_append, List.length_cons, List.getD_cons_succ] using ih

lemma execute_input (gs : List Gate) (i : Fin 10) :
    (execute gs inputs).getD i.val zero = LiftSeventeen.input i := by
  obtain ⟨extra, he⟩ := execute_prefix gs inputs
  rw [he]
  exact getD_append_left inputs extra i.val i.isLt

lemma arbitrary_and_value (pre : List Gate) (a b : Fin 10) :
    gv (execute pre inputs) {op := .and, inputs := [a.val, b.val]} = andColumn a b := by
  simp only [gv, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
    execute_input, prime, Bool.false_eq_true, ite_false]
  have unit (v : Sig) : v &&& one = v := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_and]
    change (v.getLsbD i && (BitVec.allOnes 1024).getLsbD i) = v.getLsbD i
    rw [BitVec.getLsbD_allOnes]
    simp [hi]
  change LiftSeventeen.input a &&& (LiftSeventeen.input b &&& one) =
    LiftSeventeen.input a &&& LiftSeventeen.input b
  rw [unit]

lemma arbitrary_not_value (pre mid : List Gate) (a b : Fin 10) :
    gv (execute mid (execute pre inputs ++ [andColumn a b]))
      {op := .not, inputs := [10 + pre.length]} = neg (andColumn a b) := by
  obtain ⟨extra, he⟩ := execute_prefix mid (execute pre inputs ++ [andColumn a b])
  have len : (execute pre inputs).length = 10 + pre.length := execute_length pre inputs
  simp only [gv, List.map_cons, List.map_nil, List.headD_cons]
  rw [he, ← len, getD_append_slot]

lemma anywhere_circuit_lower (a b : Fin 10) (ab : a ≠ b) (C : Circuit)
    (pre mid post : List Gate)
    (gatesEq : C.gates = pre ++ [{op := .and, inputs := [a.val, b.val]}] ++ mid ++
      [{op := .not, inputs := [10 + pre.length]}] ++ post)
    (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (monoPre : ∀ g ∈ pre, isNot g = false)
    (monoMid : ∀ g ∈ mid, isNot g = false)
    (monoPost : ∀ g ∈ post, isNot g = false)
    (computes : PEqualNP.MetaComplexity.circuitFun 10 C = edge) : 20 ≤ C.size := by
  let ag : Gate := {op := .and, inputs := [a.val, b.val]}
  let ng : Gate := {op := .not, inputs := [10 + pre.length]}
  let h := andColumn a b
  let free := [h, neg h]
  let wp := execute pre inputs
  let wa := wp ++ [gv wp ag]
  let wm := execute mid wa
  let wn := wm ++ [gv wm ng]
  have av : gv wp ag = h := arbitrary_and_value pre a b
  have nv : gv wm ng = neg h := by
    change gv (execute mid (wp ++ [gv wp ag])) ng = _
    rw [av]
    exact arbitrary_not_value pre mid a b
  have whole : execute C.gates inputs = execute post wn := by
    rw [gatesEq]
    simp only [execute, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rfl
  have output : graph ∈ execute post wn := whole ▸ output_member C legal computes
  obtain ⟨k1, S1, bound1, run1, sub1⟩ := FreeBank.pull_positive_chunk post wn free
    (fun g hg => legal g (by rw [gatesEq]; simp [hg])) monoPost (Live.stop graph_proper)
    (by intro w hw; have he : w = graph := Finset.mem_singleton.mp hw
        subst w; exact List.mem_append_left free output)
  have knownN : gv wm ng ∈ free := by simp [free, nv]
  have subN := FreeBank.skip_free_gate wm free ng knownN sub1
  obtain ⟨k2, S2, bound2, run2, sub2⟩ := FreeBank.pull_positive_chunk mid wa free
    (fun g hg => legal g (by rw [gatesEq]; simp [hg])) monoMid run1 subN
  have knownA : gv wp ag ∈ free := by simp [free, av]
  have subA := FreeBank.skip_free_gate wp free ag knownA sub2
  obtain ⟨k3, S3, bound3, run3, sub3⟩ := FreeBank.pull_positive_chunk pre inputs free
    (fun g hg => legal g (by rw [gatesEq]; simp [hg])) monoPre run2 subA
  have subset : S3 ⊆ bank a b := by
    intro w hw
    have mem := sub3 w hw
    simpa [free, h, bank, List.mem_append, List.mem_cons, List.mem_singleton,
      or_assoc, or_left_comm, or_comm] using mem
  have lower := all_positive_tail_lower a b ab subset run3
  have size : C.size = pre.length + mid.length + post.length + 2 := by
    simp [Circuit.size, gatesEq]
    omega
  omega

end PEqualNP.Outside.L_meta_2373.Live1024.OneNotFirstAnd
