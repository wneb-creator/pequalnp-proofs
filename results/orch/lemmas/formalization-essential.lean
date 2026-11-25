import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1479

def BinaryAO (n : ℕ) (C : Circuit) : Prop :=
  ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
    (g.op = .and ∨ g.op = .or) ∧
      ∃ a b : ℕ, g.inputs = [a,b] ∧ a ≠ b ∧ a < n+j ∧ b < n+j

def supportWireStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma support_run_extends (gs : List Gate) (w : List Bool) :
    ∃ t : List Bool, gs.foldl supportWireStep w = w++t ∧ t.length=gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[],by simp,rfl⟩
  | cons g gs ih =>
    obtain ⟨t,ht,hlen⟩ := ih (supportWireStep w g)
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false)::t,?_,?_⟩
    · simpa [supportWireStep,List.append_assoc] using ht
    · simp [hlen]

lemma support_wire_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
    (C.wires (List.ofFn x)).getD i.val false = x i := by
  obtain ⟨t,ht,_⟩ := support_run_extends C.gates (List.ofFn x)
  change (C.gates.foldl supportWireStep (List.ofFn x)).getD i.val false = _
  rw [ht,List.getD_append _ _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD]

lemma support_wire_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool)
    (j : ℕ) (g : Gate) (a b : ℕ) (hj : C.gates[j]?=some g)
    (hab : g.inputs=[a,b]) (ha : a<n+j) (hb : b<n+j) :
    (C.wires (List.ofFn x)).getD (n+j) false =
      g.op.eval [(C.wires (List.ofFn x)).getD a false,
        (C.wires (List.ofFn x)).getD b false] := by
  have hlt := (List.getElem?_eq_some_iff.mp hj).1
  have split : C.gates = C.gates.take j ++ g :: C.gates.drop (j+1) := by
    have h := List.take_append_drop j C.gates
    rw [List.drop_eq_getElem?_toList_append,hj] at h
    simpa using h.symm
  let pre := (C.gates.take j).foldl supportWireStep (List.ofFn x)
  have plen : pre.length=n+j := by
    obtain ⟨t,ht,hlen⟩ := support_run_extends (C.gates.take j) (List.ofFn x)
    change ((C.gates.take j).foldl supportWireStep (List.ofFn x)).length=n+j
    rw [ht,List.length_append,List.length_ofFn,hlen,List.length_take]
    omega
  obtain ⟨t,ht,_⟩ := support_run_extends (C.gates.drop (j+1)) (supportWireStep pre g)
  have full : C.wires (List.ofFn x) =
      pre ++ g.op.eval (g.inputs.map fun i => pre.getD i false)::t := by
    change C.gates.foldl supportWireStep (List.ofFn x) = _
    rw [split,List.foldl_append,List.foldl_cons]
    simpa [pre,supportWireStep,List.append_assoc] using ht
  have preserve (i : ℕ) (hi : i<n+j) :
      (C.wires (List.ofFn x)).getD i false = pre.getD i false := by
    rw [full,List.getD_append _ _ _ _ (by omega)]
  rw [preserve a ha,preserve b hb,full]
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp [plen,hab]

lemma substitution_wires_length {n : ℕ} (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n+C.gates.length := by
  obtain ⟨t,ht,hlen⟩ := support_run_extends C.gates (List.ofFn x)
  change (C.gates.foldl supportWireStep (List.ofFn x)).length = _
  rw [ht,List.length_append,List.length_ofFn,hlen]

lemma essential_unread_input_mono {n : ℕ} {C : Circuit}
    (normal : BinaryAO n C) (i : Fin n)
    (unread : ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → i.val ∉ g.inputs)
    (x y : Fin n → Bool) (ordered : ∀ k, k ≠ i → x k = true → y k = true)
    (out : C.output ≠ i.val) :
    C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true := by
  have bounded : ∀ w, w < n+C.gates.length → w ≠ i.val →
      (C.wires (List.ofFn x)).getD w false = true →
        (C.wires (List.ofFn y)).getD w false = true := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw different
      by_cases hin : w<n
      · rw [support_wire_input C x ⟨w,hin⟩,support_wire_input C y ⟨w,hin⟩]
        apply ordered ⟨w,hin⟩
        intro equal
        exact different (congrArg Fin.val equal)
      · have hj : w-n<C.gates.length := by omega
        let g : Gate := C.gates[w-n]
        have atGate : C.gates[w-n]? = some g :=
          List.getElem?_eq_some_iff.mpr ⟨hj,rfl⟩
        obtain ⟨hop,a,b,hab,_,ha,hb⟩ := normal (w-n) g atGate
        have heq : n+(w-n)=w := by omega
        have na : a ≠ i.val := by
          intro equal
          exact unread (w-n) g atGate (by simp [hab,equal])
        have nb : b ≠ i.val := by
          intro equal
          exact unread (w-n) g atGate (by simp [hab,equal])
        have ia := ih a (by omega) (by omega) na
        have ib := ih b (by omega) (by omega) nb
        have xv := support_wire_gate C x (w-n) g a b atGate hab ha hb
        have yv := support_wire_gate C y (w-n) g a b atGate hab ha hb
        rcases hop with hop | hop
        · have xv' : (C.wires (List.ofFn x)).getD w false =
              ((C.wires (List.ofFn x)).getD a false &&
                (C.wires (List.ofFn x)).getD b false) := by
            simpa [heq,hop,GateOp.eval] using xv
          have yv' : (C.wires (List.ofFn y)).getD w false =
              ((C.wires (List.ofFn y)).getD a false &&
                (C.wires (List.ofFn y)).getD b false) := by
            simpa [heq,hop,GateOp.eval] using yv
          rw [xv',yv']
          simp only [Bool.and_eq_true_iff]
          exact fun h => ⟨ia h.1,ib h.2⟩
        · have xv' : (C.wires (List.ofFn x)).getD w false =
              ((C.wires (List.ofFn x)).getD a false ||
                (C.wires (List.ofFn x)).getD b false) := by
            simpa [heq,hop,GateOp.eval] using xv
          have yv' : (C.wires (List.ofFn y)).getD w false =
              ((C.wires (List.ofFn y)).getD a false ||
                (C.wires (List.ofFn y)).getD b false) := by
            simpa [heq,hop,GateOp.eval] using yv
          rw [xv',yv']
          simp only [Bool.or_eq_true_iff]
          exact Or.imp ia ib
  intro yes
  by_cases bound : C.output < n+C.gates.length
  · exact bounded C.output bound out yes
  · have hlen := substitution_wires_length C x
    change (C.wires (List.ofFn x)).getD C.output false = true at yes
    rw [List.getD_eq_default _ _ (by omega)] at yes
    contradiction

lemma essential_input_directly_read {n : ℕ} {C : Circuit}
    (normal : BinaryAO n C) (i : Fin n) (x y : Fin n → Bool)
    (ordered : ∀ k, k ≠ i → x k = true → y k = true)
    (out : C.output ≠ i.val) (positive : C.eval (List.ofFn x) = true)
    (negative : C.eval (List.ofFn y) = false) :
    ∃ (j : ℕ) (g : Gate), C.gates[j]? = some g ∧ i.val ∈ g.inputs := by
  classical
  by_contra absent
  have unread : ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → i.val ∉ g.inputs := by
    intro j g atGate occurs
    exact absent ⟨j,g,atGate,occurs⟩
  have impossible := essential_unread_input_mono normal i unread x y ordered out positive
  rw [negative] at impossible
  contradiction

def essentialH (m : Fin 512) : Bool :=
  (m.val.testBit 0 && (m.val.testBit 3 || m.val.testBit 6 || m.val.testBit 8)) ||
  (m.val.testBit 1 && (m.val.testBit 3 || m.val.testBit 4 || m.val.testBit 7)) ||
  (m.val.testBit 2 && (m.val.testBit 4 || m.val.testBit 5 || m.val.testBit 6))

def essentialFeatures (m : Fin 512) (k : Fin 11) : Bool :=
  if k.val < 9 then m.val.testBit k.val else
  if k.val = 9 then m.val.testBit 5 || m.val.testBit 7 else
  m.val.testBit 8 || (m.val.testBit 5 || m.val.testBit 7)

def essentialRows (i : Fin 9) : Fin 512 × Fin 512 :=
  [(9,396),(10,396),(20,177),(9,7),(18,7),(36,133),(65,7),(130,35),(257,35)].getD i.val (0,0)

lemma essential_row_certificate : ∀ i : Fin 9,
    essentialH (essentialRows i).1 = true ∧ essentialH (essentialRows i).2 = false ∧
      ∀ k : Fin 11, k.val ≠ i.val →
        essentialFeatures (essentialRows i).1 k = true →
          essentialFeatures (essentialRows i).2 k = true := by
  decide

lemma essential_fixed_prefix_direct_reads {C : Circuit} (normal : BinaryAO 11 C)
    (computed : ∀ m : Fin 512, C.eval (List.ofFn (essentialFeatures m)) = essentialH m)
    (gateOutput : 11 ≤ C.output) :
    ∀ i : Fin 9, ∃ (j : ℕ) (g : Gate), C.gates[j]? = some g ∧ i.val ∈ g.inputs := by
  intro i
  obtain ⟨positive,negative,ordered⟩ := essential_row_certificate i
  apply essential_input_directly_read normal ⟨i.val,by omega⟩
    (essentialFeatures (essentialRows i).1) (essentialFeatures (essentialRows i).2)
  · intro k different
    apply ordered k
    intro equal
    apply different
    exact Fin.ext equal
  · have hi := i.isLt
    omega
  · rw [computed]
    exact positive
  · rw [computed]
    exact negative

end PEqualNP.Outside.L_meta_1479
