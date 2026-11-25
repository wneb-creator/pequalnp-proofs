import NonOrSeed

namespace PEqualNP.Outside.L_meta_2592.FewNot.Extended

open PEqualNP.CircuitLowerBounds

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

lemma live_seventeen_starts_or {S : Finset Sig} (run : Live true target 17 S)
    (raw : ∀ v ∈ S, v ∈ pins) :
    ∃ a b : Sig, ∃ U : Finset Sig,
      a ∈ pins ∧ b ∈ pins ∧ proper a ∧ proper b ∧ a ≠ b ∧
      S = insert a (insert b U) ∧ (∀ v ∈ U, v ∈ pins) ∧
      bin 1 a b ∉ insert a (insert b U) ∧
      Live true target 16 (insert (bin 1 a b) U) := by
  obtain ⟨U,a,b,d,hd,hS,hpa,hpb,hab,hfresh,tail⟩ := run
  have ha : a ∈ pins := raw a (hS ▸ (by simp))
  have hb : b ∈ pins := raw b (hS ▸ (by simp))
  have hU : ∀ v ∈ U, v ∈ pins := by
    intro v hv
    exact raw v (hS ▸ (by simp [hv]))
  have htail : ∀ v ∈ insert (bin d a b) U, v ∈ pins ∨ v = bin d a b := by
    intro v hv
    rcases Finset.mem_insert.mp hv with hv | hv
    · exact Or.inr hv
    · exact Or.inl (hU v hv)
  have op : d = 1 := by
    by_contra nonOr
    have impossible := PEqualNP.Outside.L_meta_2592.FewNot.pair_seventeen
      hd nonOr ha hb hab tail htail
    exact (by decide : ¬ (17 : Nat) ≤ 16) impossible
  subst d
  exact ⟨a,b,U,ha,hb,hpa,hpb,hab,hS,hU,hfresh,tail⟩

lemma two_not_or_first (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (size : C.size ≤ 19) (nots : PEqualNP.NotBracket.notCount C = 2)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = f10 x) :
    C.size = 19 ∧ C.gates.countP (fun g => !isNot g) = 17 ∧
      ∃ a b : Sig, ∃ U : Finset Sig,
        a ∈ pins ∧ b ∈ pins ∧ proper a ∧ proper b ∧ a ≠ b ∧
        (∀ v ∈ U, v ∈ pins) ∧ bin 1 a b ∉ insert a (insert b U) ∧
        Live true target 16 (insert (bin 1 a b) U) := by
  obtain ⟨k,S,hk,run,raw⟩ := realize_plain C legal computes
  have low := PEqualNP.Outside.L_meta_2592.FewNot.pins_seventeen run raw
  have count := binary_not_count_eq C
  have kexact : k = 17 := by omega
  have cexact : C.gates.countP (fun g => !isNot g) = 17 := by omega
  have sexact : C.size = 19 := by omega
  subst k
  obtain ⟨a,b,U,ha,hb,hpa,hpb,hab,hS,hU,hfresh,tail⟩ := live_seventeen_starts_or run raw
  exact ⟨sexact,cexact,a,b,U,ha,hb,hpa,hpb,hab,hU,hfresh,tail⟩

end PEqualNP.Outside.L_meta_2592.FewNot.Extended
