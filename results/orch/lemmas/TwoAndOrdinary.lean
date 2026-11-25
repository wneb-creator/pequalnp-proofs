import TwoAndBankLower
import FreeSegments

namespace PEqualNP.Outside.L_meta_2373.Live1024.TwoAndBank
open PEqualNP.CircuitLowerBounds
open FreeSegments

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
    gv (execute pre inputs) {op := .and, inputs := [a.val, b.val]} = andCol a b := by
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
    gv (execute mid (execute pre inputs ++ [andCol a b]))
      {op := .not, inputs := [10 + pre.length]} = neg (andCol a b) := by
  obtain ⟨extra, he⟩ := execute_prefix mid (execute pre inputs ++ [andCol a b])
  have len : (execute pre inputs).length = 10 + pre.length := execute_length pre inputs
  simp only [gv, List.map_cons, List.map_nil, List.headD_cons]
  rw [he, ← len, getD_append_slot]

lemma output_member (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : PEqualNP.MetaComplexity.circuitFun 10 C = edge) :
    graph ∈ execute C.gates inputs := by
  have goalEq : (execute C.gates inputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j, hj⟩
    exact (table_eval C legal C.output r).trans
      ((congrFun computes (sample r)).trans (edge_table r).symm)
  simp only [List.getD_eq_getElem?_getD] at goalEq
  cases h : (execute C.gates inputs)[C.output]? with
  | none =>
    rw [h] at goalEq
    exact False.elim (graph_proper.1 goalEq.symm)
  | some z =>
    rw [h] at goalEq
    exact goalEq ▸ List.mem_of_getElem? h

lemma four_free_outputs_lower (a b c d : Fin 10) (ab : a ≠ b) (cd : c ≠ d)
    (C : Circuit) (segments : List (List Gate × Gate)) (tail : List Gate)
    (four : segments.length = 4) (gatesEq : C.gates = weave segments ++ tail)
    (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (mono : ∀ seg ∈ segments, ∀ g ∈ seg.1, isNot g = false)
    (monoTail : ∀ g ∈ tail, isNot g = false)
    (known : freeTrace [andCol a b, neg (andCol a b), andCol c d, neg (andCol c d)] segments inputs)
    (computes : PEqualNP.MetaComplexity.circuitFun 10 C = edge) : 20 ≤ C.size := by
  let free := [andCol a b, neg (andCol a b), andCol c d, neg (andCol c d)]
  have output := output_member C legal computes
  rw [gatesEq] at output
  have table : execute (weave segments ++ tail) inputs = execute tail (execute (weave segments) inputs) := by
    simp only [execute, List.foldl_append]
  rw [table] at output
  obtain ⟨l, U, bound, run, sub⟩ := FreeBank.pull_positive_chunk tail (execute (weave segments) inputs) free
    (fun g hg => legal g (by rw [gatesEq]; exact List.mem_append_right _ hg)) monoTail (Live.stop graph_proper)
    (by intro w hw; have he : w = graph := Finset.mem_singleton.mp hw
        subst w; exact List.mem_append_left free output)
  obtain ⟨k, S, count, trace, subset⟩ := pull_segments segments inputs free
    (fun seg hs g hg => legal g (by rw [gatesEq]; exact List.mem_append_left _ (member_weave hs hg)))
    mono known run sub
  have covered : S ⊆ bank a b c d := by
    intro w hw
    have mem := subset w hw
    simpa [free, bank, List.mem_append, List.mem_cons, List.mem_singleton,
      or_assoc, or_left_comm, or_comm] using mem
  have lower := positive_tail_lower a b c d ab cd covered trace
  have size : C.size = charge segments + tail.length + 4 := by
    simp only [Circuit.size, gatesEq, List.length_append, weave_length, four]
    omega
  omega

def andGate (a b : Fin 10) : Gate := {op := .and, inputs := [a.val, b.val]}
def notGate (i : Nat) : Gate := {op := .not, inputs := [i]}
def beforeSecond (a b : Fin 10) (p0 p1 p2 : List Gate) : List Gate :=
  p0 ++ [andGate a b] ++ p1 ++ [notGate (10 + p0.length)] ++ p2

def separatedSegments (a b c d : Fin 10) (p0 p1 p2 p3 : List Gate) : List (List Gate × Gate) :=
  [(p0, andGate a b), (p1, notGate (10 + p0.length)), (p2, andGate c d),
    (p3, notGate (10 + (beforeSecond a b p0 p1 p2).length))]

lemma execute_append (xs ys : List Gate) (w : List Sig) :
    execute (xs ++ ys) w = execute ys (execute xs w) := by
  simp only [execute, List.foldl_append]

lemma execute_singleton (g : Gate) (w : List Sig) : execute [g] w = w ++ [gv w g] := rfl

lemma separated_free (a b c d : Fin 10) (p0 p1 p2 p3 : List Gate) :
    freeTrace [andCol a b, neg (andCol a b), andCol c d, neg (andCol c d)]
      (separatedSegments a b c d p0 p1 p2 p3) inputs := by
  have av1 : gv (execute p0 inputs) (andGate a b) = andCol a b := arbitrary_and_value p0 a b
  have nv1 : gv (execute p1 (execute p0 inputs ++ [andCol a b])) (notGate (10 + p0.length)) =
      neg (andCol a b) := arbitrary_not_value p0 p1 a b
  have beforeEq : execute (beforeSecond a b p0 p1 p2) inputs =
      execute p2 (execute p1 (execute p0 inputs ++ [andCol a b]) ++ [neg (andCol a b)]) := by
    simp only [beforeSecond, execute_append, execute_singleton]
    rw [av1, nv1]
  have av2 : gv (execute (beforeSecond a b p0 p1 p2) inputs) (andGate c d) = andCol c d :=
    arbitrary_and_value _ c d
  have nv2 : gv (execute p3 (execute (beforeSecond a b p0 p1 p2) inputs ++ [andCol c d]))
      (notGate (10 + (beforeSecond a b p0 p1 p2).length)) = neg (andCol c d) :=
    arbitrary_not_value _ p3 c d
  simp only [separatedSegments, freeTrace]
  rw [av1, nv1, ← beforeEq, av2, nv2]
  simp

lemma separated_two_not_lower (a b c d : Fin 10) (ab : a ≠ b) (cd : c ≠ d)
    (C : Circuit) (p0 p1 p2 p3 p4 : List Gate)
    (gatesEq : C.gates = beforeSecond a b p0 p1 p2 ++ [andGate c d] ++ p3 ++
      [notGate (10 + (beforeSecond a b p0 p1 p2).length)] ++ p4)
    (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (mono : ∀ g ∈ p0 ++ p1 ++ p2 ++ p3 ++ p4, isNot g = false)
    (computes : PEqualNP.MetaComplexity.circuitFun 10 C = edge) : 20 ≤ C.size := by
  apply four_free_outputs_lower a b c d ab cd C (separatedSegments a b c d p0 p1 p2 p3) p4 rfl
  · simpa [separatedSegments, weave, beforeSecond, List.append_assoc] using gatesEq
  · exact legal
  · intro seg hs g hg
    simp only [separatedSegments, List.mem_cons, List.mem_nil_iff, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl <;> apply mono g <;> simp [hg]
  · intro g hg
    exact mono g (by simp [hg])
  · exact separated_free a b c d p0 p1 p2 p3
  · exact computes

end PEqualNP.Outside.L_meta_2373.Live1024.TwoAndBank
