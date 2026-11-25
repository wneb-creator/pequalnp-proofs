import CutFloor
import SignedRestriction
import BinarySixteen
import SingleUse

namespace PEqualNP.Outside.L_meta_2592_aux.StrictCutFloor

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2592_restrict.CircuitProof
open PEqualNP.Outside.L_meta_2592_aux.Restriction
open PEqualNP.Outside.L_meta_2592_aux.CutFloor
open PEqualNP.Outside.L_meta_2592_aux.StrictRestriction
open PEqualNP.Outside.L_meta_7493.CircuitProof.Readers
open PEqualNP.Outside.L_meta_7493.PetersenCutTrace

set_option maxHeartbeats 2000000 in
lemma strict_cut_floor (C : Circuit) (fan : FanInTwo C)
    (correct : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersen x)
    (v : Fin 10) (clean : CleanL 10 C.gates)
    (outValid : C.output < 10 + C.gates.length)
    (live : ∀ w : Fin (10 + C.gates.length),
      w ≠ ⟨C.output, outValid⟩ → ∃ z, readEdge C.gates w z)
    (source : Fin (10 + C.gates.length))
    (marked : Marked (C.gates.foldl originStep (initialOrigins 10))
      (elim 9 C.gates (List.ofFn (restrictionSeed v), [])).1 source.val) :
    15 + cutCost (initialOrigins 10) v.val C.gates ≤ nonNotCount C.gates := by
  have nonconstant : ∃ x y : Fin 9 → Bool,
      C.eval (List.ofFn (liftInput v x)) ≠ C.eval (List.ofFn (liftInput v y)) := by
    refine ⟨fun _ => false, fun _ => true, ?_⟩
    rw [correct, correct, liftInput_petersen, liftInput_petersen]
    decide
  obtain ⟨D, fanD, budget, computes⟩ := strict_restriction_with_marked 9 10 C fan
    (List.ofFn (restrictionSeed v)) (initialOrigins 10) v.val (liftInput v)
    (inv_seed 9 10 (restrictionSeed v) (liftInput v)
      (restrictionSeed_valid v) (restrictionSeed_eval v))
    (originConstant_seed 10 (restrictionSeed v) v false (restrictionSeed_fixed v))
    nonconstant clean outValid live source marked
  have floor : 14 ≤ nonNotCount D.gates := by
    apply PEqualNP.Outside.L_meta_7493.binaryFloor D fanD
    intro x
    rw [computes, correct, liftInput_petersen]
    have values : Fin.lastCases false x =
        ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, false] := by
      funext i
      refine Fin.lastCases ?_ (fun k => ?_) i
      · rfl
      · rw [Fin.lastCases_castSucc]
        fin_cases k <;> rfl
    rw [values]
    simp [petersen, PEqualNP.Outside.L_meta_7493.petersenF,
      PEqualNP.Outside.L_meta_7493.PetersenNine.edgeFun,
      PEqualNP.Outside.L_meta_7493.PetersenNine.edges]
    ac_rfl
  omega

lemma petersen_dependent (v : Fin 10) : Dep petersen v := by
  refine ⟨fun i => decide (i = v + 5), ?_⟩
  fin_cases v <;> decide

lemma petersen_still_nonconstant (v : Fin 10) (b : Bool) :
    ∃ x y, petersen (Function.update x v b) ≠ petersen (Function.update y v b) := by
  refine ⟨fun _ => false, fun _ => true, ?_⟩
  rw [(FirstOrigin.petersen_cofactor_values v b).1,
    (FirstOrigin.petersen_cofactor_values v b).2]
  decide

lemma least_output_valid {gs : List Gate} {out : ℕ}
    (least : Least 10 petersen gs out) : out < 10 + gs.length := by
  by_contra! after
  obtain ⟨x, y, different⟩ := least.ncv BinarySixteen.petersen_nonconstant
  exact different ((vl_beyond gs x out after).trans (vl_beyond gs y out after).symm)

lemma least_strict_cut_floor {gs : List Gate} {out : ℕ}
    (least : Least 10 petersen gs out) (v : Fin 10)
    (source : Fin (10 + gs.length))
    (marked : Marked (gs.foldl originStep (initialOrigins 10))
      (elim 9 gs (List.ofFn (restrictionSeed v), [])).1 source.val) :
    15 + cutCost (initialOrigins 10) v.val gs ≤ nonNotCount gs := by
  let C : Circuit := ⟨gs, out⟩
  have fan : FanInTwo C := fun g hg => (clean_nok 10 gs least.hcl g hg).1
  exact strict_cut_floor C fan least.hev v least.hcl (least_output_valid least)
    (PEqualNP.Outside.L_meta_7493.least_read_edge_live least
      BinarySixteen.petersen_nonconstant petersen_dependent petersen_still_nonconstant
      (least_output_valid least)) source marked

lemma signed_first_canal (op : GateOp) (shape : op = .and ∨ op = .or) (sa sb : Bool) :
    ∃ b : Bool, ∀ a : Bool,
      op.eval [if sa then !a else a, if sb then !b else b] =
        op.eval [if sa then !false else false, if sb then !b else b] := by
  rcases shape with rfl | rfl <;> cases sa <;> cases sb <;> decide

lemma first_operand_twice (C : Circuit) (pre post : List Gate) (g : Gate)
    (split : C.gates = pre ++ g :: post) (allNot : ∀ q ∈ pre, q.op = .not)
    (shape : g.op = .and ∨ g.op = .or) (a b : ℕ) (inputs : g.inputs = [a, b])
    (u v : Fin 10) (different : u ≠ v) (sa sb : Bool)
    (origin : (pre.foldl originStep (initialOrigins 10)).getD a none = some u.val)
    (valueA : ∀ x : Fin 10 → Bool,
      (wiresFrom pre (List.ofFn x)).getD a false = if sa then !(x u) else x u)
    (valueB : ∀ x : Fin 10 → Bool,
      (wiresFrom pre (List.ofFn x)).getD b false = if sb then !(x v) else x v)
    (correct : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersen x) :
    2 ≤ cutCost (initialOrigins 10) u.val C.gates := by
  by_contra! small
  have flag : FirstMerge.isNotGate g.op = false := by
    rcases shape with op | op <;> simp [FirstMerge.isNotGate, op]
  have read : FirstMerge.readsOrigin
      (pre.foldl FirstMerge.originStep (List.ofFn fun i : Fin 10 => some i.val)) u.val g = true := by
    apply List.any_eq_true.mpr
    refine ⟨a, by simp [inputs], ?_⟩
    exact decide_eq_true origin
  apply SingleUse.no_first_single_use C pre post g split allNot flag u v different
    (fun x y => g.op.eval [if sa then !x else x, if sb then !y else y])
    (signed_first_canal g.op shape sa sb) ?_ read ?_ correct
  · intro x
    simp only [inputs, List.map_cons, List.map_nil]
    change g.op.eval [(wiresFrom pre (List.ofFn x)).getD a false,
      (wiresFrom pre (List.ofFn x)).getD b false] = _
    rw [valueA, valueB]
  · rw [BinarySixteen.cutCost_eq]
    exact Nat.le_of_lt_succ small

lemma signed_operand_seventeen {gs : List Gate} {out : ℕ}
    (least : Least 10 petersen gs out) (pre post : List Gate) (g : Gate)
    (split : gs = pre ++ g :: post) (a b wire : ℕ) (inputs : g.inputs = [a, b])
    (operand : wire = a ∨ wire = b) (v : Fin 10) (sign : Bool)
    (origin : (pre.foldl originStep (initialOrigins 10)).getD wire none = some v.val)
    (signed : ∀ x : Fin 10 → Bool,
      (wiresFrom pre (List.ofFn x)).getD wire false = if sign then !(x v) else x v)
    (cost : 2 ≤ cutCost (initialOrigins 10) v.val gs)
    (annihilates : (g.op = GateOp.and ∧ sign = false) ∨
      (g.op = GateOp.or ∧ sign = true)) : 17 ≤ nonNotCount gs := by
  have prefixOk : ∀ h ∈ pre, Ok h := by
    intro h hh
    apply (clean_nok 10 gs least.hcl h _).1
    rw [split]
    exact List.mem_append_left _ hh
  have marked := SignedRestriction.marked_of_signed_operand 9 10 pre post g
    (List.ofFn (restrictionSeed v)) (initialOrigins 10) v (liftInput v)
    (inv_seed 9 10 (restrictionSeed v) (liftInput v)
      (restrictionSeed_valid v) (restrictionSeed_eval v))
    (originConstant_seed 10 (restrictionSeed v) v false (restrictionSeed_fixed v))
    prefixOk wire a b inputs operand sign origin
    (liftInput_removed v) signed annihilates
  have sourceValid : 10 + pre.length < 10 + gs.length := by
    rw [split, List.length_append, List.length_cons]
    omega
  have floor := least_strict_cut_floor least v ⟨10 + pre.length, sourceValid⟩
    (by simpa only [split] using marked)
  omega

end PEqualNP.Outside.L_meta_2592_aux.StrictCutFloor
