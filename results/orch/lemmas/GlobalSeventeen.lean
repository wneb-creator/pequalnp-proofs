import FewNotGeneric

namespace PEqualNP.Outside.L_meta_2592.FewNot.Extended

open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000
set_option maxHeartbeats 0

lemma live_floor_from_pair_floor (base : List Sig) (target : Sig) (L : ℕ)
    (fresh : target ∉ base)
    (pairFloor : ∀ (d : ℕ) (a b : Sig), allowed true d → a ∈ base → b ∈ base →
      proper a → proper b → a ≠ b → ∀ (k : ℕ) (S : Finset Sig),
        Live true target k S → (∀ v ∈ S, v ∈ base ∨ v = bin d a b) → L ≤ k)
    {k : ℕ} {S : Finset Sig} (run : Live true target k S)
    (raw : ∀ v ∈ S, v ∈ base) : L + 1 ≤ k := by
  cases k with
  | zero =>
    obtain ⟨rfl,hp⟩ := run
    exact False.elim (fresh (raw target (Finset.mem_singleton_self target)))
  | succ k =>
    obtain ⟨U,a,b,d,hd,rfl,hpa,hpb,hab,hfresh,tail⟩ := run
    have ha : a ∈ base := raw a (by simp)
    have hb : b ∈ base := raw b (by simp)
    have htail : ∀ v ∈ insert (bin d a b) U, v ∈ base ∨ v = bin d a b := by
      intro v hv
      rcases Finset.mem_insert.mp hv with hv | hv
      · exact Or.inr hv
      · exact Or.inl (raw v (by simp [hv]))
    have bound := pairFloor d a b hd ha hb hpa hpb hab k _ tail htail
    omega

lemma rowInputs_plain (r : Row) : pins.map (bit r) = List.ofFn (assign r) := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_ofFn]
    rfl
  · intro i hi hj
    simp only [List.getElem_map, List.getElem_ofFn, assign]
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hi)]

def plainWord_bridge (a : Sig) : Bool := !(bit 0 a)

lemma nrm_pins_plain : pins.map (nrm true) = pins := by
  have plain : pins.all plainWord_bridge = true := by decide +kernel
  have eq : pins.map (nrm true) = pins.map id := by
    apply List.map_congr_left
    intro a ha
    exact nrm_id (by simpa [plainWord_bridge] using List.all_eq_true.mp plain a ha)
  rw [eq, List.map_id]

lemma realize_plain (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = f10 x) :
    ∃ k S, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live true target k S ∧
      ∀ a ∈ S, a ∈ pins := by
  have he : (execute C.gates pins).getD C.output zero = target := by
    apply bit_ext
    intro r
    rw [←b_read,execute_bits _ _ _ (fun g hg => (legal g hg).1)]
    change (C.wires (pins.map (bit r))).getD C.output false = _
    rw [rowInputs_plain]
    exact (computes _).trans (rowTarget r).symm
  have hp : proper target := by unfold proper; decide +kernel
  have out := get_rep (u := true) (execute C.gates pins) C.output
  rw [he] at out
  unfold Repr at out
  rw [nrm_id (show bit 0 target = false by decide +kernel)] at out
  obtain ⟨k,S,hk,run,hs⟩ := extract C.gates pins legal (u := true) (by simp) hp
    (out.resolve_right (fun h => h hp))
  rw [nrm_pins_plain] at hs
  exact ⟨k,S,hk,run,hs⟩

lemma binary_not_count_eq (C : Circuit) :
    C.gates.countP (fun g => !isNot g) + PEqualNP.NotBracket.notCount C = C.size := by
  have sameNot :
      (fun g : Gate => @decide (g.op = GateOp.not)
        (PEqualNP.CircuitLowerBounds.lineDegreeGateOpDecEq g.op GateOp.not)) = isNot := by
    funext g
    obtain ⟨op, operands⟩ := g
    cases op <;> rfl
  have countNot : PEqualNP.NotBracket.notCount C = C.gates.countP isNot := by
    rw [PEqualNP.NotBracket.notCount, sameNot, ← List.countP_eq_length_filter]
  have negSame : (fun g : Gate => decide (¬ isNot g = true)) = (fun g => !isNot g) := by
    funext g
    cases isNot g <;> rfl
  have count := List.length_eq_countP_add_countP isNot (l := C.gates)
  rw [negSame] at count
  change _ + PEqualNP.NotBracket.notCount C = C.gates.length
  omega

lemma seventeen_plus_not_of_binary_floor (C : Circuit)
    (floor : 17 ≤ C.gates.countP (fun g => !isNot g)) :
    17 + PEqualNP.NotBracket.notCount C ≤ C.size := by
  have count := binary_not_count_eq C
  omega

lemma at_most_two_nots_of_binary_floor (C : Circuit) (size : C.size ≤ 19)
    (floor : 17 ≤ C.gates.countP (fun g => !isNot g)) :
    PEqualNP.NotBracket.notCount C ≤ 2 := by
  have bound := seventeen_plus_not_of_binary_floor C floor
  omega

lemma live_seventeen {k : Nat} {S : Finset Sig} (run : Live true target k S)
    (raw : ∀ v ∈ S, v ∈ pins) : 17 ≤ k := by
  apply live_floor_from_pair_floor pins target 16 (by decide +kernel) _ run raw
  intro d a b hd ha hb _ _ hab n T hT hraw
  exact PEqualNP.Outside.L_meta_2592.FewNot.pair_sixteen hd ha hb hab hT hraw

lemma binary_seventeen (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = f10 x) :
    17 ≤ C.gates.countP (fun g => !isNot g) := by
  obtain ⟨k,S,hk,run,raw⟩ := realize_plain C legal computes
  exact (live_seventeen run raw).trans hk

lemma seventeen_plus_not (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = f10 x) :
    17 + PEqualNP.NotBracket.notCount C ≤ C.size := by
  exact seventeen_plus_not_of_binary_floor C (binary_seventeen C legal computes)

lemma at_most_two_nots (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (size : C.size ≤ 19)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = f10 x) :
    PEqualNP.NotBracket.notCount C ≤ 2 := by
  exact at_most_two_nots_of_binary_floor C size (binary_seventeen C legal computes)

end PEqualNP.Outside.L_meta_2592.FewNot.Extended
