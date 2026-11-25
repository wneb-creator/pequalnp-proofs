import conjunction_bound
import Batteries.Tactic.OpenPrivate

export private PEqualNP.Outside.L_meta_2592_aux.Stronger.Extended.b_read PEqualNP.Outside.L_meta_2592_aux.Stronger.Extended.execute_bits PEqualNP.Outside.L_meta_2592_aux.Stronger.Extended.get_rep PEqualNP.Outside.L_meta_2592_aux.Stronger.Extended.extract from PEqualNP.Outside.L_meta_2592

namespace PEqualNP.Outside.L_meta_2592_aux.Stronger.Extended

open PEqualNP.CircuitLowerBounds

lemma realizeBank (C : Circuit) (w : List Sig)
    (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (plain : w.all plainWord = true)
    (computes : ∀ r : Row, C.eval (w.map (bit r)) = bit r target) :
    ∃ k S, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live true target k S ∧
      ∀ a ∈ S, a ∈ w := by
  have he : (execute C.gates w).getD C.output zero = target := by
    apply bit_ext
    intro r
    rw [←b_read,execute_bits _ _ _ (fun g hg => (legal g hg).1)]
    exact computes r
  have hp : proper target := by unfold proper; decide +kernel
  have out := get_rep (u:=true) (execute C.gates w) C.output
  rw [he] at out
  unfold Repr at out
  rw [nrm_id (show bit 0 target=false by decide +kernel)] at out
  obtain ⟨k,S,hk,run,hs⟩ := extract C.gates w legal (u:=true) (by simp) hp
    (out.resolve_right (fun h => h hp))
  rw [nrm_map plain] at hs
  exact ⟨k,S,hk,run,hs⟩

lemma first_and_tail_binary_lower (C : Circuit) (a b : Fin 10) (hab : a ≠ b)
    (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x ++ [x a && x b]) = f10 x) :
    17 ≤ C.gates.countP (fun g => !isNot g) := by
  let w := pins ++ [bin 0 (pins.getD a.val zero) (pins.getD b.val zero)]
  have hp : ∀ a b : Fin 10,
      (pins ++ [bin 0 (pins.getD a.val zero) (pins.getD b.val zero)]).all plainWord = true := by
    decide +kernel
  have rows (r : Row) : w.map (bit r) =
      List.ofFn (assign r) ++ [assign r a && assign r b] := by
    simp [w, List.map_append, rowPins, transport_bit_bin, assign]
  obtain ⟨k,S,hk,run,raw⟩ := realizeBank C w legal (hp a b) (fun r => by
    rw [rows, computes, rowTarget])
  have lower : 17 ≤ k := by
    by_cases used : bin 0 (pins.getD a.val zero) (pins.getD b.val zero) ∈ S
    · exact conjunction_tail_lower 0 (by decide) a b hab run used raw
    · apply seventeen_of_raw_pins run
      intro v hv
      have hm := raw v hv
      simp only [w,List.mem_append,List.mem_singleton] at hm
      exact hm.resolve_right (fun eq => used (eq ▸ hv))
  omega

lemma first_and_size_lower (C : Circuit) (a b : Fin 10) (hab : a ≠ b)
    (firstGate : ∃ gs, C.gates = ⟨.and,[a.val,b.val]⟩ :: gs)
    (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = f10 x) : 18 ≤ C.size := by
  obtain ⟨gs,hgs⟩ := firstGate
  let D : Circuit := ⟨gs,C.output⟩
  have ld : PEqualNP.MetaComplexity.FanInTwo D := by
    intro g hg
    apply legal g
    simp [hgs,D] at hg ⊢
    exact Or.inr hg
  have cd : ∀ x : Fin 10 → Bool, D.eval (List.ofFn x ++ [x a && x b]) = f10 x := by
    intro x
    have h := computes x
    have get (i : Fin 10) : (List.ofFn x).getD i.val false = x i := by
      fin_cases i <;> rfl
    have head : GateOp.and.eval ([a.val,b.val].map (fun i => (List.ofFn x).getD i false)) =
        (x a && x b) := by
      simp only [List.map_cons,List.map_nil,get,GateOp.eval,List.all_cons,List.all_nil,id,Bool.and_true]
    simpa only [Circuit.eval,Circuit.wires,hgs,List.foldl_cons,head,D] using h
  have lower := first_and_tail_binary_lower D a b hab ld cd
  have bound : gs.countP (fun g => !isNot g) ≤ gs.length := List.countP_le_length
  change 18 ≤ C.gates.length
  rw [hgs]
  change 17 ≤ gs.countP (fun g => !isNot g) at lower
  simp only [List.length_cons]
  omega

end PEqualNP.Outside.L_meta_2592_aux.Stronger.Extended
