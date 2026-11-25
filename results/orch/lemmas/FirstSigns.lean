import DeletionFifteen
import StrictCutFloor

namespace PEqualNP.Outside.L_meta_2592_aux.FirstSigns

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
    16 + cutCost (initialOrigins 10) v.val C.gates ≤ nonNotCount C.gates := by
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
  have floor : 15 ≤ nonNotCount D.gates := by
    apply DeletionFifteen.deletion_floor D fanD
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
    simp [petersen, PEqualNP.Outside.L_meta_5236.edge]
  omega

lemma least_strict_cut_floor {gs : List Gate} {out : ℕ}
    (least : Least 10 petersen gs out) (v : Fin 10)
    (source : Fin (10 + gs.length))
    (marked : Marked (gs.foldl originStep (initialOrigins 10))
      (elim 9 gs (List.ofFn (restrictionSeed v), [])).1 source.val) :
    16 + cutCost (initialOrigins 10) v.val gs ≤ nonNotCount gs := by
  let C : Circuit := ⟨gs, out⟩
  have fan : FanInTwo C := fun g hg => (clean_nok 10 gs least.hcl g hg).1
  exact strict_cut_floor C fan least.hev v least.hcl (StrictCutFloor.least_output_valid least)
    (PEqualNP.Outside.L_meta_7493.least_read_edge_live least
      BinarySixteen.petersen_nonconstant StrictCutFloor.petersen_dependent StrictCutFloor.petersen_still_nonconstant
      (StrictCutFloor.least_output_valid least)) source marked

lemma signed_operand_eighteen {gs : List Gate} {out : ℕ}
    (least : Least 10 petersen gs out) (pre post : List Gate) (g : Gate)
    (split : gs = pre ++ g :: post) (a b wire : ℕ) (inputs : g.inputs = [a, b])
    (operand : wire = a ∨ wire = b) (v : Fin 10) (sign : Bool)
    (origin : (pre.foldl originStep (initialOrigins 10)).getD wire none = some v.val)
    (signed : ∀ x : Fin 10 → Bool,
      (wiresFrom pre (List.ofFn x)).getD wire false = if sign then !(x v) else x v)
    (cost : 2 ≤ cutCost (initialOrigins 10) v.val gs)
    (annihilates : (g.op = GateOp.and ∧ sign = false) ∨
      (g.op = GateOp.or ∧ sign = true)) : 18 ≤ nonNotCount gs := by
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


lemma second_operand_twice (C : Circuit) (pre post : List Gate) (g : Gate)
    (split : C.gates = pre ++ g :: post) (allNot : ∀ q ∈ pre, q.op = .not)
    (shape : g.op = .and ∨ g.op = .or) (a b : ℕ) (inputs : g.inputs = [a, b])
    (u v : Fin 10) (different : u ≠ v) (sa sb : Bool)
    (origin : (pre.foldl originStep (initialOrigins 10)).getD b none = some v.val)
    (valueA : ∀ x : Fin 10 → Bool,
      (wiresFrom pre (List.ofFn x)).getD a false = if sa then !(x u) else x u)
    (valueB : ∀ x : Fin 10 → Bool,
      (wiresFrom pre (List.ofFn x)).getD b false = if sb then !(x v) else x v)
    (correct : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersen x) :
    2 ≤ cutCost (initialOrigins 10) v.val C.gates := by
  by_contra! small
  have flag : FirstMerge.isNotGate g.op = false := by
    rcases shape with op | op <;> simp [FirstMerge.isNotGate, op]
  have read : FirstMerge.readsOrigin
      (pre.foldl FirstMerge.originStep (List.ofFn fun i : Fin 10 => some i.val)) v.val g = true := by
    apply List.any_eq_true.mpr
    refine ⟨b, by simp [inputs], ?_⟩
    exact decide_eq_true origin
  have canal : ∃ z : Bool, ∀ x : Bool,
      g.op.eval [if sa then !z else z, if sb then !x else x] =
        g.op.eval [if sa then !z else z, if sb then !false else false] := by
    rcases shape with op | op <;> rw [op] <;> cases sa <;> cases sb <;> decide
  apply SingleUse.no_first_single_use C pre post g split allNot flag v u different.symm
    (fun x y => g.op.eval [if sa then !y else y, if sb then !x else x])
    canal ?_ read ?_ correct
  · intro x
    simp only [inputs, List.map_cons, List.map_nil]
    change g.op.eval [(wiresFrom pre (List.ofFn x)).getD a false,
      (wiresFrom pre (List.ofFn x)).getD b false] = _
    rw [valueA, valueB]
  · rw [BinarySixteen.cutCost_eq]
    exact Nat.le_of_lt_succ small

lemma first_signs_nonannihilating {gs : List Gate} {out : ℕ}
    (least : Least 10 petersen gs out) (budget : nonNotCount gs ≤ 17)
    (pre post : List Gate) (g : Gate) (split : gs = pre ++ g :: post)
    (allNot : ∀ h ∈ pre, h.op = .not) (shape : g.op = .and ∨ g.op = .or)
    (a b : ℕ) (inputs : g.inputs = [a, b]) (u v : Fin 10)
    (different : u ≠ v) (sa sb : Bool)
    (originU : (pre.foldl originStep (initialOrigins 10)).getD a none = some u.val)
    (originV : (pre.foldl originStep (initialOrigins 10)).getD b none = some v.val)
    (valueA : ∀ x : Fin 10 → Bool,
      (wiresFrom pre (List.ofFn x)).getD a false = if sa then !(x u) else x u)
    (valueB : ∀ x : Fin 10 → Bool,
      (wiresFrom pre (List.ofFn x)).getD b false = if sb then !(x v) else x v) :
    (g.op = .or ∧ sa = false ∧ sb = false) ∨
      (g.op = .and ∧ sa = true ∧ sb = true) := by
  let C : Circuit := ⟨gs, out⟩
  have costU := StrictCutFloor.first_operand_twice C pre post g split allNot shape
    a b inputs u v different sa sb originU valueA valueB least.hev
  have costV := second_operand_twice C pre post g split allNot shape
    a b inputs u v different sa sb originV valueA valueB least.hev
  have noU : ¬ ((g.op = GateOp.and ∧ sa = false) ∨
      (g.op = GateOp.or ∧ sa = true)) := by
    intro destroys
    have floor := signed_operand_eighteen least pre post g split a b a inputs
      (Or.inl rfl) u sa originU valueA costU destroys
    omega
  have noV : ¬ ((g.op = GateOp.and ∧ sb = false) ∨
      (g.op = GateOp.or ∧ sb = true)) := by
    intro destroys
    have floor := signed_operand_eighteen least pre post g split a b b inputs
      (Or.inr rfl) v sb originV valueB costV destroys
    omega
  rcases shape with op | op <;> cases sa <;> cases sb <;> simp_all

end PEqualNP.Outside.L_meta_2592_aux.FirstSigns
