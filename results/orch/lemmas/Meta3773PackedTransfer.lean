import Mathlib.Data.Nat.BinaryRec
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3773_aux.Packed

open PEqualNP.CircuitLowerBounds

def gateOf (g : Bool × ℕ × ℕ) : Gate :=
  ⟨if g.1 then GateOp.or else GateOp.and,[g.2.1,g.2.2]⟩

def circuitOf (gs : List (Bool × ℕ × ℕ)) : Circuit :=
  ⟨gs.map gateOf,25+gs.length⟩

def packedStep (w : List ℕ) (g : Bool × ℕ × ℕ) : List ℕ :=
  w ++ [if g.1 then w.getD g.2.1 0 ||| w.getD g.2.2 0
    else w.getD g.2.1 0 &&& w.getD g.2.2 0]

def boolStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]

lemma getD_bits (w : List ℕ) (i k : ℕ) :
    (w.map fun r => r.testBit i).getD k false = (w.getD k 0).testBit i := by
  cases h : w[k]? <;>
    simp [List.getD_eq_getElem?_getD,List.getElem?_map,h]

lemma step_bits (w : List ℕ) (g : Bool × ℕ × ℕ) (i : ℕ) :
    boolStep (w.map fun r => r.testBit i) (gateOf g) =
      (packedStep w g).map fun r => r.testBit i := by
  rcases g with ⟨op,a,b⟩
  cases op <;> simp [boolStep,gateOf,packedStep,GateOp.eval] <;>
    cases ha : w[a]? <;> cases hb : w[b]? <;> simp [ha,hb]

lemma fold_bits (gs : List (Bool × ℕ × ℕ)) (w : List ℕ) (i : ℕ) :
    (gs.map gateOf).foldl boolStep (w.map fun r => r.testBit i) =
      (gs.foldl packedStep w).map fun r => r.testBit i := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons,List.foldl_cons]
    rw [step_bits]
    exact ih (packedStep w g)

lemma packed_length (gs : List (Bool × ℕ × ℕ)) (w : List ℕ) :
    (gs.foldl packedStep w).length = w.length+gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp [List.foldl_cons,ih,packedStep,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

lemma circuitOf_eval (gs : List (Bool × ℕ × ℕ)) (w : List ℕ) (i : ℕ)
    (hw : w.length = 26) :
    (circuitOf gs).eval (w.map fun r => r.testBit i) =
      ((gs.foldl packedStep w).getLastD 0).testBit i := by
  change ((gs.map gateOf).foldl boolStep (w.map fun r => r.testBit i)).getD
    (25+gs.length) false = _
  rw [fold_bits,getD_bits]
  have hlen := packed_length gs w
  have hi : 25+gs.length = (gs.foldl packedStep w).length-1 := by omega
  rw [hi]
  simp only [List.getD_eq_getElem?_getD,List.getLastD_eq_getLast?,List.getLast?_eq_getElem?]

lemma circuitOf_monotone (gs : List (Bool × ℕ × ℕ)) :
    PEqualNP.MetaComplexity.Monotone2 (circuitOf gs) := by
  intro g hg
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hg
  cases h : x.1 <;> simp [gateOf,h]

lemma transfer (gs : List (Bool × ℕ × ℕ)) (h : Bool × ℕ × ℕ)
    (hh : h ∈ gs.head?)
    (allowed : h ∈ [(false,0,13),(true,0,1),(true,0,13),(true,2,13)]) :
    ∃ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size = gs.length ∧
      (∃ g : Gate, C.gates.head? = some g ∧
        ((g.op = .and ∧ g.inputs = [0,13]) ∨
          (g.op = .or ∧ g.inputs ∈ [[0,1],[0,13],[2,13]]))) ∧
      ∀ (w : List ℕ) (i : ℕ), w.length = 26 →
        C.eval (w.map fun r => r.testBit i) =
          ((gs.foldl (fun (w : List ℕ) (g : Bool × ℕ × ℕ) =>
            w ++ [if g.1 then w.getD g.2.1 0 ||| w.getD g.2.2 0
              else w.getD g.2.1 0 &&& w.getD g.2.2 0]) w).getLastD 0).testBit i := by
  refine ⟨circuitOf gs,circuitOf_monotone gs,?_,?_,?_⟩
  · simp [circuitOf,Circuit.size]
  · refine ⟨gateOf h,?_,?_⟩
    · change (gs.map gateOf).head? = some (gateOf h)
      rw [List.head?_map,show gs.head? = some h from hh]
      rfl
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at allowed
      rcases allowed with rfl | rfl | rfl | rfl <;> simp [gateOf]
  · intro w i hw
    exact circuitOf_eval gs w i hw

end PEqualNP.Outside.L_meta_3773_aux.Packed
