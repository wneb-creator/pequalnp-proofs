import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583.Q3Semantic

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

def evalGates (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma evalGates_length (gs : List Gate) (w : List Bool) :
    (evalGates gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [evalGates]
  | cons g gs ih =>
    simp only [evalGates, List.foldl_cons] at ih ⊢
    rw [ih]
    simp
    omega

lemma evalGates_append (gs1 gs2 : List Gate) (w : List Bool) :
    evalGates (gs1 ++ gs2) w = evalGates gs2 (evalGates gs1 w) := by
  simp [evalGates, List.foldl_append]

lemma evalGates_getD_lt (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < w.length) :
    (evalGates gs w).getD k false = w.getD k false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [evalGates, List.foldl_cons] at ih ⊢
    have hk' : k < (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).length := by
      simp
      omega
    rw [ih _ hk']
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

lemma evalGates_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (evalGates gs w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i => (evalGates (gs.take j) w).getD i false) := by
  have hsplit : gs = gs.take j ++ [gs[j]] ++ gs.drop (j + 1) := by
    have h1 := List.take_append_drop j gs
    have h2 : gs.drop j = gs[j] :: gs.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    simp
  conv_lhs => rw [hsplit]
  rw [evalGates_append, evalGates_append]
  set w1 := evalGates (gs.take j) w
  have hw1 : w1.length = w.length + j := by
    rw [evalGates_length, List.length_take]
    omega
  have hlt : w.length + j < (evalGates [gs[j]] w1).length := by
    rw [evalGates_length, hw1]
    simp
  rw [evalGates_getD_lt _ _ _ hlt]
  simp only [evalGates, List.foldl_cons, List.foldl_nil]
  rw [← hw1]
  simp [List.getD_eq_getElem?_getD]

lemma gateAt_eq_getElem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma wires_getD_gate (n : ℕ) (C : Circuit) (hRB : ReadsBack n C)
    (x : List Bool) (hx : x.length = n) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (n + j) false =
      (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i => (C.wires x).getD i false) := by
  change (evalGates C.gates x).getD (n + j) false = _
  have h1 := evalGates_getD_gate C.gates x j hj
  rw [hx] at h1
  rw [h1]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi_lt : i < n + j := by
    have := hRB j hj i
    rw [gateAt_eq_getElem C j hj] at this
    exact this hi
  have hlen : (evalGates (C.gates.take j) x).length = n + j := by
    rw [evalGates_length, hx, List.length_take]
    omega
  have hsplit : C.gates = C.gates.take j ++ C.gates.drop j := (List.take_append_drop j C.gates).symm
  symm
  change (evalGates C.gates x).getD i false = (evalGates (C.gates.take j) x).getD i false
  conv_lhs => rw [hsplit, evalGates_append]
  exact evalGates_getD_lt (C.gates.drop j) (evalGates (C.gates.take j) x) i (by omega)

lemma gateOp_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l : List ℕ) (f g : ℕ → Bool) (hfg : ∀ u ∈ l, f u = true → g u = true) :
    op.eval (l.map f) = true → op.eval (l.map g) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
    intro hf b hb
    rcases hb with ⟨u, hu, rfl⟩
    exact hfg u hu (hf (f u) ⟨u, hu, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
    rintro ⟨b, ⟨u, hu, rfl⟩, hfu⟩
    exact ⟨g u, ⟨u, hu, rfl⟩, hfg u hu hfu⟩

lemma wires_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
    (C.wires (List.ofFn x)).getD i false = x i := by
  change (evalGates C.gates (List.ofFn x)).getD i false = _
  rw [evalGates_getD_lt C.gates (List.ofFn x) i (by simpa using i.isLt)]
  simp [List.getD_eq_getElem?_getD]

lemma wire_mono (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true) :
    ∀ k < n + C.gates.length, (C.wires (List.ofFn x)).getD k false = true →
      (C.wires (List.ofFn y)).getD k false = true := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro hk htrue
    by_cases hkn : k < n
    · have hx := wires_input n C x ⟨k, hkn⟩
      have hy := wires_input n C y ⟨k, hkn⟩
      exact hy.trans (hxy _ (hx.symm.trans htrue))
    · let j := k - n
      have hkj : k = n + j := by omega
      have hj : j < C.gates.length := by omega
      rw [hkj, wires_getD_gate n C hAO.2.1 _ List.length_ofFn j hj] at htrue ⊢
      apply gateOp_eval_mono _ (hAO.1 _ (List.getElem_mem hj)) _ _ _ ?_ htrue
      intro u hu huTrue
      have hu_lt : u < n + j := by
        have hh := hAO.2.1 j hj u
        rw [gateAt_eq_getElem C j hj] at hh
        exact hh hu
      exact ih u (by omega) (by omega) huTrue

lemma output_lt_of_true (n : ℕ) (C : Circuit) (x : Fin n → Bool)
    (htrue : PEqualNP.MetaComplexity.circuitFun n C x = true) :
    C.output < n + C.gates.length := by
  have hlen : (C.wires (List.ofFn x)).length = n + C.gates.length := by
    change (evalGates C.gates (List.ofFn x)).length = n + C.gates.length
    simpa using evalGates_length C.gates (List.ofFn x)
  by_contra h
  have hout : (C.wires (List.ofFn x)).length ≤ C.output := by omega
  change (C.wires (List.ofFn x)).getD C.output false = true at htrue
  rw [List.getD_eq_default _ _ hout] at htrue
  cases htrue


lemma circuit_mono (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true)
    (hx : circuitFun n C x = true) : circuitFun n C y = true :=
  wire_mono n C hAO x y hxy C.output (output_lt_of_true n C x hx) hx

def incidenceValue {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (z : Fin (N + N) → Bool) : Bool :=
  decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
    z (Fin.natAdd N l) = true)

def canonicalNegative {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (A : Finset (Fin N)) : Fin (N + N) → Bool :=
  Fin.addCases (fun p => decide (p ∈ A))
    (fun l => decide (∀ p ∈ A, ¬ I p l))

lemma canonicalNegative_false {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (A : Finset (Fin N)) : incidenceValue I (canonicalNegative I A) = false := by
  apply decide_eq_false
  rintro ⟨p, l, hi, hp, hl⟩
  have hp' : p ∈ A := by
    simpa only [canonicalNegative, Fin.addCases_left, decide_eq_true_eq] using hp
  have hl' : ∀ p ∈ A, ¬ I p l := by
    simpa only [canonicalNegative, Fin.addCases_right, decide_eq_true_eq] using hl
  exact hl' p hp' hi

lemma below_canonicalNegative {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (z : Fin (N + N) → Bool) (hz : incidenceValue I z = false) :
    ∀ i, z i = true → canonicalNegative I
      (Finset.univ.filter fun p => z (Fin.castAdd N p) = true) i = true := by
  have hno : ¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
      z (Fin.natAdd N l) = true := by
    simpa only [incidenceValue, decide_eq_false_iff_not] using hz
  intro i hi
  cases i using Fin.addCases with
  | left p =>
    simpa only [canonicalNegative, Fin.addCases_left, decide_eq_true_eq,
      Finset.mem_filter, Finset.mem_univ, true_and] using hi
  | right l =>
    simp only [canonicalNegative, Fin.addCases_right, decide_eq_true_eq]
    intro p hp hpl
    have hp' : z (Fin.castAdd N p) = true := (Finset.mem_filter.mp hp).2
    exact hno ⟨p, l, hpl, hp', hi⟩

lemma semantics_of_boundary {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (F : (Fin (N + N) → Bool) → Bool)
    (hmono : ∀ x y, (∀ i, x i = true → y i = true) → F x = true → F y = true)
    (hpos : ∀ p l : Fin N, I p l →
      F (pairInput (Fin.castAdd N p) (Fin.natAdd N l)) = true)
    (hneg : ∀ A : Finset (Fin N), F (canonicalNegative I A) = false) :
    ∀ z, F z = incidenceValue I z := by
  intro z
  cases hz : incidenceValue I z
  · cases hf : F z
    · rfl
    · have hle := below_canonicalNegative I z hz
      have htrue := hmono z _ hle hf
      rw [hneg] at htrue
      cases htrue
  · have hex : ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
        z (Fin.natAdd N l) = true := of_decide_eq_true hz
    obtain ⟨p, l, hi, hp, hl⟩ := hex
    apply hmono _ z ?_ (hpos p l hi)
    intro i hii
    simp only [pairInput, decide_eq_true_eq] at hii
    rcases hii with rfl | rfl
    · exact hp
    · exact hl

lemma ao2_semantics_of_boundary {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (hAO : IsAO2 (N + N) C)
    (hpos : ∀ p l : Fin N, I p l →
      circuitFun (N + N) C (pairInput (Fin.castAdd N p) (Fin.natAdd N l)) = true)
    (hneg : ∀ A : Finset (Fin N),
      circuitFun (N + N) C (canonicalNegative I A) = false) :
    ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
        z (Fin.natAdd N l) = true) :=
  semantics_of_boundary I (circuitFun (N + N) C) (circuit_mono (N + N) C hAO) hpos hneg

abbrev q3Incidence (p l : Fin 13) : Prop :=
  p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9

lemma q3_parameters : 2 ≤ (3 : ℕ) ∧ 13 = 3 ^ 2 + 3 + 1 := by decide

lemma q3_columns : ∀ l : Fin 13,
    (Finset.univ.filter fun p => q3Incidence p l).card = 3 + 1 := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma q3_unique_line : ∀ p p' : Fin 13, p ≠ p' →
    ∃! l : Fin 13, q3Incidence p l ∧ q3Incidence p' l := by
  unfold ExistsUnique
  decide

lemma q3_positive_count :
    ((Finset.univ : Finset (Fin 13 × Fin 13)).filter
      (fun e => q3Incidence e.1 e.2)).card = 52 := by decide

lemma q3_negative_count : Fintype.card (Finset (Fin 13)) = 8192 := by simp

def maskSet {N : ℕ} (b : BitVec N) : Finset (Fin N) :=
  Finset.univ.filter fun p => b.getLsbD p.val = true

def setMask {N : ℕ} (A : Finset (Fin N)) : BitVec N :=
  (BitVec.ofBoolListLE (List.ofFn fun p : Fin N => decide (p ∈ A))).cast List.length_ofFn

lemma maskSet_setMask {N : ℕ} (A : Finset (Fin N)) : maskSet (setMask A) = A := by
  ext p
  simp only [maskSet, Finset.mem_filter, Finset.mem_univ, true_and, setMask,
    BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

def canonicalMask {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (b : BitVec N) : Fin (N + N) → Bool :=
  Fin.addCases (fun p => b.getLsbD p.val)
    (fun l => decide (∀ p : Fin N, b.getLsbD p.val = true → ¬ I p l))

lemma canonicalMask_eq {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (b : BitVec N) : canonicalMask I b = canonicalNegative I (maskSet b) := by
  funext i
  cases i using Fin.addCases <;>
    simp [canonicalMask, canonicalNegative, maskSet]

lemma ao2_semantics_of_masks {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (hAO : IsAO2 (N + N) C)
    (hpos : ∀ p l : Fin N, I p l →
      circuitFun (N + N) C (pairInput (Fin.castAdd N p) (Fin.natAdd N l)) = true)
    (hneg : ∀ b : BitVec N, circuitFun (N + N) C (canonicalMask I b) = false) :
    ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
        z (Fin.natAdd N l) = true) := by
  apply ao2_semantics_of_boundary I C hAO hpos
  intro A
  simpa only [canonicalMask_eq, maskSet_setMask] using hneg (setMask A)

lemma q3_mask_line (b : BitVec 13) (l : Fin 13) :
    canonicalMask q3Incidence b (Fin.natAdd 13 l) =
      !(b.getLsbD l.val || b.getLsbD (l + 1).val ||
        b.getLsbD (l + 3).val || b.getLsbD (l + 9).val) := by
  have hpred : (∀ p : Fin 13, b.getLsbD p.val = true → ¬ q3Incidence p l) ↔
      ¬ (b.getLsbD l.val = true ∨ b.getLsbD (l + 1).val = true ∨
        b.getLsbD (l + 3).val = true ∨ b.getLsbD (l + 9).val = true) := by
    constructor
    · rintro h (h0 | h1 | h3 | h9)
      · exact h l h0 (by simp [q3Incidence])
      · exact h (l + 1) h1 (by simp [q3Incidence])
      · exact h (l + 3) h3 (by simp [q3Incidence])
      · exact h (l + 9) h9 (by simp [q3Incidence])
    · intro h p hp hi
      apply h
      rcases hi with rfl | rfl | rfl | rfl
      · exact Or.inl hp
      · exact Or.inr (Or.inl hp)
      · exact Or.inr (Or.inr (Or.inl hp))
      · exact Or.inr (Or.inr (Or.inr hp))
  simp only [canonicalMask, Fin.addCases_right]
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq, hpred]
  simp [or_assoc, and_assoc]

def q3MaskFast (b : BitVec 13) : Fin 26 → Bool :=
  @Fin.addCases 13 13 (fun _ => Bool) (fun p : Fin 13 => b.getLsbD p.val)
    (fun l : Fin 13 => !(b.getLsbD l.val || b.getLsbD (l + 1).val ||
      b.getLsbD (l + 3).val || b.getLsbD (l + 9).val))

lemma q3MaskFast_eq (b : BitVec 13) : q3MaskFast b = canonicalMask q3Incidence b := by
  funext i
  cases i using @Fin.addCases 13 13 with
  | left p => simp only [q3MaskFast, canonicalMask, Fin.addCases_left]
  | right l => simp only [q3MaskFast, Fin.addCases_right, q3_mask_line]

end PEqualNP.Outside.L_meta_2583.Q3Semantic


namespace PEqualNP.Outside.L_meta_2583.WordCertificate

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

def wordGate {k : ℕ} (g : Gate) (w : List (BitVec k)) : BitVec k :=
  match g.op with
  | .and => w.getD (g.inputs.getD 0 0) 0 &&& w.getD (g.inputs.getD 1 0) 0
  | .or => w.getD (g.inputs.getD 0 0) 0 ||| w.getD (g.inputs.getD 1 0) 0
  | _ => 0

def wordWires {k : ℕ} (C : Circuit) (x : List (BitVec k)) : List (BitVec k) :=
  C.gates.foldl (fun w g => w ++ [wordGate g w]) x

def wordEval {k : ℕ} (C : Circuit) (x : List (BitVec k)) : BitVec k :=
  (wordWires C x).getD C.output 0

lemma getD_bit {k : ℕ} (xs : List (BitVec k)) (i t : ℕ) :
    (xs.getD i 0).getLsbD t = (xs.map fun w => w.getLsbD t).getD i false := by
  induction xs generalizing i with
  | nil => simp
  | cons x xs ih => cases i <;> simp_all

lemma gate_bit {k : ℕ} (g : Gate)
    (hop : g.op = .and ∨ g.op = .or) (hlen : g.inputs.length = 2)
    (xs : List (BitVec k)) (t : ℕ) :
    (wordGate g xs).getLsbD t =
      g.op.eval (g.inputs.map fun i =>
        (xs.map fun w => w.getLsbD t).getD i false) := by
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  rcases hop with hop | hop
  · have h : wordGate g xs = xs.getD a 0 &&& xs.getD b 0 := by
      simp [wordGate, hop, hab]
    rw [h, BitVec.getLsbD_and, getD_bit, getD_bit, hop, hab]
    simp [GateOp.eval]
  · have h : wordGate g xs = xs.getD a 0 ||| xs.getD b 0 := by
      simp [wordGate, hop, hab]
    rw [h, BitVec.getLsbD_or, getD_bit, getD_bit, hop, hab]
    simp [GateOp.eval]

lemma fold_bit {k : ℕ} (gs : List Gate) :
    (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) →
    ∀ (xs : List (BitVec k)) (t : ℕ),
      (gs.foldl (fun w g => w ++ [wordGate g w]) xs).map (fun w => w.getLsbD t) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (xs.map fun w => w.getLsbD t) := by
  induction gs with
  | nil => intro h xs t; rfl
  | cons g gs ih =>
    intro h xs t
    have hg := h g (by simp)
    have hs : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 := by
      intro a ha
      exact h a (by simp [ha])
    simp only [List.foldl_cons]
    rw [ih hs]
    congr 1
    simp only [List.map_append, List.map_cons, List.map_nil,
      gate_bit g hg.1 hg.2 xs t]

lemma wordEval_sound {n k : ℕ} (C : Circuit) (hAO : IsAO2 n C)
    (X : Fin n → BitVec k) (t : ℕ) :
    (wordEval C (List.ofFn X)).getLsbD t =
      circuitFun n C (fun i => (X i).getLsbD t) := by
  have h := fold_bit C.gates
    (fun g hg => ⟨hAO.1 g hg, hAO.2.2 g hg⟩) (List.ofFn X) t
  have he := congrArg (fun xs : List Bool => xs.getD C.output false) h
  rw [← getD_bit] at he
  simpa only [wordEval, wordWires, circuitFun, Circuit.eval, Circuit.wires,
    List.map_ofFn, Function.comp_def] using he

lemma zero_certificate {n k : ℕ} (C : Circuit) (hAO : IsAO2 n C)
    (X : Fin n → BitVec k) (hzero : wordEval C (List.ofFn X) = 0) :
    ∀ t : ℕ, circuitFun n C (fun i => (X i).getLsbD t) = false := by
  intro t
  rw [← wordEval_sound C hAO X t, hzero]
  simp

lemma equality_certificate {n k : ℕ} (C : Circuit) (hAO : IsAO2 n C)
    (X : Fin n → BitVec k) (expected : BitVec k)
    (heq : wordEval C (List.ofFn X) = expected) :
    ∀ t : ℕ, circuitFun n C (fun i => (X i).getLsbD t) = expected.getLsbD t := by
  intro t
  rw [← wordEval_sound C hAO X t, heq]

def packRows {k : ℕ} (f : Fin k → Bool) : BitVec k :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast List.length_ofFn

lemma packRows_bit {k : ℕ} (f : Fin k → Bool) (t : Fin k) :
    (packRows f).getLsbD t.val = f t := by
  simp only [packRows, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

lemma packed_sound {n k : ℕ} (C : Circuit) (hAO : IsAO2 n C)
    (rows : Fin k → Fin n → Bool) (t : Fin k) :
    (wordEval C (List.ofFn fun i => packRows (fun r => rows r i))).getLsbD t.val =
      circuitFun n C (rows t) := by
  rw [wordEval_sound C hAO]
  congr 1
  funext i
  exact packRows_bit (fun r => rows r i) t

lemma packed_zero_certificate {n k : ℕ} (C : Circuit) (hAO : IsAO2 n C)
    (rows : Fin k → Fin n → Bool)
    (hzero : wordEval C (List.ofFn fun i => packRows (fun r => rows r i)) = 0) :
    ∀ t : Fin k, circuitFun n C (rows t) = false := by
  intro t
  rw [← packed_sound C hAO rows t, hzero]
  simp

end PEqualNP.Outside.L_meta_2583.WordCertificate

namespace PEqualNP.Outside.L_meta_2583.Q3WordControl

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Outside.L_meta_2583.WordCertificate

def circuit : Circuit :=
  ⟨[⟨.or, [0, 1]⟩,
    ⟨.or, [26, 3]⟩,
    ⟨.or, [27, 9]⟩,
    ⟨.and, [28, 13]⟩,
    ⟨.or, [1, 2]⟩,
    ⟨.or, [30, 4]⟩,
    ⟨.or, [31, 10]⟩,
    ⟨.and, [32, 14]⟩,
    ⟨.or, [2, 3]⟩,
    ⟨.or, [34, 5]⟩,
    ⟨.or, [35, 11]⟩,
    ⟨.and, [36, 15]⟩,
    ⟨.or, [3, 4]⟩,
    ⟨.or, [38, 6]⟩,
    ⟨.or, [39, 12]⟩,
    ⟨.and, [40, 16]⟩,
    ⟨.or, [0, 4]⟩,
    ⟨.or, [42, 5]⟩,
    ⟨.or, [43, 7]⟩,
    ⟨.and, [44, 17]⟩,
    ⟨.or, [1, 5]⟩,
    ⟨.or, [46, 6]⟩,
    ⟨.or, [47, 8]⟩,
    ⟨.and, [48, 18]⟩,
    ⟨.or, [2, 6]⟩,
    ⟨.or, [50, 7]⟩,
    ⟨.or, [51, 9]⟩,
    ⟨.and, [52, 19]⟩,
    ⟨.or, [3, 7]⟩,
    ⟨.or, [54, 8]⟩,
    ⟨.or, [55, 10]⟩,
    ⟨.and, [56, 20]⟩,
    ⟨.or, [4, 8]⟩,
    ⟨.or, [58, 9]⟩,
    ⟨.or, [59, 11]⟩,
    ⟨.and, [60, 21]⟩,
    ⟨.or, [5, 9]⟩,
    ⟨.or, [62, 10]⟩,
    ⟨.or, [63, 12]⟩,
    ⟨.and, [64, 22]⟩,
    ⟨.or, [0, 6]⟩,
    ⟨.or, [66, 10]⟩,
    ⟨.or, [67, 11]⟩,
    ⟨.and, [68, 23]⟩,
    ⟨.or, [1, 7]⟩,
    ⟨.or, [70, 11]⟩,
    ⟨.or, [71, 12]⟩,
    ⟨.and, [72, 24]⟩,
    ⟨.or, [0, 2]⟩,
    ⟨.or, [74, 8]⟩,
    ⟨.or, [75, 12]⟩,
    ⟨.and, [76, 25]⟩,
    ⟨.or, [29, 33]⟩,
    ⟨.or, [78, 37]⟩,
    ⟨.or, [79, 41]⟩,
    ⟨.or, [80, 45]⟩,
    ⟨.or, [81, 49]⟩,
    ⟨.or, [82, 53]⟩,
    ⟨.or, [83, 57]⟩,
    ⟨.or, [84, 61]⟩,
    ⟨.or, [85, 65]⟩,
    ⟨.or, [86, 69]⟩,
    ⟨.or, [87, 73]⟩,
    ⟨.or, [88, 77]⟩], 89⟩

def backwardCheck (n : ℕ) : List Gate → Bool
  | [] => true
  | g :: gs => g.inputs.all (fun w => decide (w < n)) && backwardCheck (n + 1) gs

lemma backwardCheck_sound (n : ℕ) (gs : List Gate) (out : ℕ)
    (h : backwardCheck n gs = true) : ReadsBack n ⟨gs, out⟩ := by
  intro j hj w hw
  induction gs generalizing n j with
  | nil => simp at hj
  | cons g gs ih =>
    have hc : g.inputs.all (fun w => decide (w < n)) = true ∧
        backwardCheck (n + 1) gs = true := by
      simpa only [backwardCheck, Bool.and_eq_true] using h
    cases j with
    | zero =>
      simp only [gateAt, List.getD_cons_zero] at hw
      have hh := List.all_eq_true.mp hc.1 w hw
      simpa using hh
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have hw' : w ∈ (gateAt ⟨gs, out⟩ j).inputs := by
        simpa [gateAt] using hw
      have hh := ih (n + 1) hc.2 j hj' hw'
      omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
lemma circuit_ao : IsAO2 26 circuit := by
  refine ⟨?_, backwardCheck_sound 26 circuit.gates circuit.output (by decide +kernel), ?_⟩
  · decide +kernel
  · decide +kernel

lemma circuit_size : circuit.size = 64 := rfl

def positiveWords : List (BitVec 52) :=
  [0xf,
    0xf0,
    0xf00,
    0xf000,
    0xf0000,
    0xf00000,
    0xf000000,
    0xf0000000,
    0xf00000000,
    0xf000000000,
    0xf0000000000,
    0xf00000000000,
    0xf000000000000,
    0x1000001011,
    0x10000010120,
    0x100000102200,
    0x1000001024000,
    0x10240002,
    0x102400040,
    0x2024000400,
    0x20240008000,
    0x204400080000,
    0x2048000800000,
    0x480008000004,
    0x4800080000080,
    0x8000800000808]

def negativeWords : List (BitVec 8192) :=
  [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,
    0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,
    0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,
    0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,
    0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,
    0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,
    0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,
    0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,
    0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000,
    0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,
    0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,
    0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,
    0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,
    0x1100110011001100110011001100110011001100110011001100110011001100110011001100110011001100110011001100110011001100110011001100110000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000110011001100110011001100110011001100110011001100110011001100110011001100110011001100110011001100110011001100110011001100110011000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000011001100110011001100110011001100110011001100110011001100110011001100110011001100110011001100110011001100110011001100110011001100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001100110011001100110011001100110011001100110011001100110011001100110011001100110011001100110011001100110011001100110011001100110000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000110011001100110011001100110011001100110011001100110011001100110011001100110011001100110011001100110011001100110011001100110011000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000011001100110011001100110011001100110011001100110011001100110011001100110011001100110011001100110011001100110011001100110011001100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001100110011001100110011001100110011001100110011001100110011001100110011001100110011001100110011001100110011001100110011001100110000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000110011001100110011001100110011001100110011001100110011001100110011001100110011001100110011001100110011001100110011001100110011,
    0x30300000303000003030000030300000303000003030000030300000303000003030000030300000303000003030000030300000303000003030000030300000303000003030000030300000303000003030000030300000303000003030000030300000303000003030000030300000303000003030000030300000303000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000303000003030000030300000303000003030000030300000303000003030000030300000303000003030000030300000303000003030000030300000303000003030000030300000303000003030000030300000303000003030000030300000303000003030000030300000303000003030000030300000303000003030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003030000030300000303000003030000030300000303000003030000030300000303000003030000030300000303000003030000030300000303000003030000030300000303000003030000030300000303000003030000030300000303000003030000030300000303000003030000030300000303000003030000030300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030300000303000003030000030300000303000003030000030300000303000003030000030300000303000003030000030300000303000003030000030300000303000003030000030300000303000003030000030300000303000003030000030300000303000003030000030300000303000003030000030300000303,
    0xf000f00000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000000f000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000000f000f,
    0xff000000ff0000000000000000000000ff000000ff0000000000000000000000ff000000ff0000000000000000000000ff000000ff0000000000000000000000ff000000ff0000000000000000000000ff000000ff0000000000000000000000ff000000ff0000000000000000000000ff000000ff0000000000000000000000ff000000ff0000000000000000000000ff000000ff0000000000000000000000ff000000ff0000000000000000000000ff000000ff0000000000000000000000ff000000ff0000000000000000000000ff000000ff0000000000000000000000ff000000ff0000000000000000000000ff000000ff0000000000000000000000ff000000ff0000000000000000000000ff000000ff0000000000000000000000ff000000ff0000000000000000000000ff000000ff0000000000000000000000ff000000ff0000000000000000000000ff000000ff0000000000000000000000ff000000ff0000000000000000000000ff000000ff0000000000000000000000ff000000ff0000000000000000000000ff000000ff0000000000000000000000ff000000ff0000000000000000000000ff000000ff0000000000000000000000ff000000ff0000000000000000000000ff000000ff0000000000000000000000ff000000ff0000000000000000000000ff000000ff,
    0x555500000000000055550000000000000000000000000000000000000000000055550000000000005555000000000000000000000000000000000000000000005555000000000000555500000000000000000000000000000000000000000000555500000000000055550000000000000000000000000000000000000000000055550000000000005555000000000000000000000000000000000000000000005555000000000000555500000000000000000000000000000000000000000000555500000000000055550000000000000000000000000000000000000000000055550000000000005555000000000000000000000000000000000000000000005555000000000000555500000000000000000000000000000000000000000000555500000000000055550000000000000000000000000000000000000000000055550000000000005555000000000000000000000000000000000000000000005555000000000000555500000000000000000000000000000000000000000000555500000000000055550000000000000000000000000000000000000000000055550000000000005555000000000000000000000000000000000000000000005555000000000000555500000000000000000000000000000000000000000000555500000000000055550000000000000000000000000000000000000000000055550000000000005555000000000000000000000000000000000000000000005555000000000000555500000000000000000000000000000000000000000000555500000000000055550000000000000000000000000000000000000000000055550000000000005555000000000000000000000000000000000000000000005555000000000000555500000000000000000000000000000000000000000000555500000000000055550000000000000000000000000000000000000000000055550000000000005555000000000000000000000000000000000000000000005555000000000000555500000000000000000000000000000000000000000000555500000000000055550000000000000000000000000000000000000000000055550000000000005555000000000000000000000000000000000000000000005555000000000000555500000000000000000000000000000000000000000000555500000000000055550000000000000000000000000000000000000000000055550000000000005555000000000000000000000000000000000000000000005555000000000000555500000000000000000000000000000000000000000000555500000000000055550000000000000000000000000000000000000000000055550000000000005555,
    0x3333333300000000000000000000000033333333000000000000000000000000000000000000000000000000000000000000000000000000000000000000000033333333000000000000000000000000333333330000000000000000000000000000000000000000000000000000000000000000000000000000000000000000333333330000000000000000000000003333333300000000000000000000000000000000000000000000000000000000000000000000000000000000000000003333333300000000000000000000000033333333000000000000000000000000000000000000000000000000000000000000000000000000000000000000000033333333000000000000000000000000333333330000000000000000000000000000000000000000000000000000000000000000000000000000000000000000333333330000000000000000000000003333333300000000000000000000000000000000000000000000000000000000000000000000000000000000000000003333333300000000000000000000000033333333000000000000000000000000000000000000000000000000000000000000000000000000000000000000000033333333000000000000000000000000333333330000000000000000000000000000000000000000000000000000000000000000000000000000000000000000333333330000000000000000000000003333333300000000000000000000000000000000000000000000000000000000000000000000000000000000000000003333333300000000000000000000000033333333000000000000000000000000000000000000000000000000000000000000000000000000000000000000000033333333000000000000000000000000333333330000000000000000000000000000000000000000000000000000000000000000000000000000000000000000333333330000000000000000000000003333333300000000000000000000000000000000000000000000000000000000000000000000000000000000000000003333333300000000000000000000000033333333000000000000000000000000000000000000000000000000000000000000000000000000000000000000000033333333000000000000000000000000333333330000000000000000000000000000000000000000000000000000000000000000000000000000000000000000333333330000000000000000000000003333333300000000000000000000000000000000000000000000000000000000000000000000000000000000000000003333333300000000000000000000000033333333,
    0xf0f0f0f0f0f0f0f0000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f0000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f0000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f0000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f0000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f0000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f0000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f0000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f,
    0xff00ff00ff00ff00ff00ff00ff00ff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ff00ff00ff00ff00ff00ff00ff00ff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ff00ff00ff00ff00ff00ff00ff00ff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ff00ff00ff00ff00ff00ff00ff00ff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ff00ff00ff00ff00ff00ff00ff00ff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ff00ff00ff00ff00ff00ff00ff00ff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ff00ff00ff00ff00ff00ff00ff00ff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ff00ff00ff00ff00ff00ff00ff00ff,
    0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff,
    0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff,
    0x5555555555555555000000000000000055555555555555550000000000000000555555555555555500000000000000005555555555555555000000000000000055555555555555550000000000000000555555555555555500000000000000005555555555555555000000000000000055555555555555550000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000555555555555555500000000000000005555555555555555000000000000000055555555555555550000000000000000555555555555555500000000000000005555555555555555000000000000000055555555555555550000000000000000555555555555555500000000000000005555555555555555,
    0x333333333333333333333333333333330000000000000000000000000000000033333333333333333333333333333333000000000000000000000000000000003333333333333333333333333333333300000000000000000000000000000000333333333333333333333333333333330000000000000000000000000000000033333333333333333333333333333333000000000000000000000000000000003333333333333333333333333333333300000000000000000000000000000000333333333333333333333333333333330000000000000000000000000000000033333333333333333333333333333333,
    0x50505050505050505050505050505050505050505050505050505050505050500000000000000000000000000000000000000000000000000000000000000000505050505050505050505050505050505050505050505050505050505050505000000000000000000000000000000000000000000000000000000000000000005050505050505050505050505050505050505050505050505050505050505050000000000000000000000000000000000000000000000000000000000000000050505050505050505050505050505050505050505050505050505050505050500000000000000000000000000000000000000000000000000000000000000000505050505050505050505050505050505050505050505050505050505050505000000000000000000000000000000000000000000000000000000000000000005050505050505050505050505050505050505050505050505050505050505050000000000000000000000000000000000000000000000000000000000000000050505050505050505050505050505050505050505050505050505050505050500000000000000000000000000000000000000000000000000000000000000000505050505050505050505050505050505050505050505050505050505050505]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma positive_word_certificate : wordEval circuit positiveWords = (0xfffffffffffff : BitVec 52) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
lemma negative_word_certificate : wordEval circuit negativeWords = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
lemma point_words_pack (p : Fin 13) : negativeWords.getD p.val 0 =
    packRows (fun r : Fin 8192 => (BitVec.ofNat 13 r.val).getLsbD p.val) := by
  fin_cases p <;> decide +kernel

open PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_2583.Q3Semantic

lemma point_word_bit (p : Fin 13) (b : BitVec 13) :
    (negativeWords.getD p.val 0).getLsbD b.toNat = b.getLsbD p.val := by
  rw [point_words_pack]
  have h := packRows_bit
    (fun r : Fin 8192 => (BitVec.ofNat 13 r.val).getLsbD p.val)
    (⟨b.toNat, b.isLt⟩ : Fin 8192)
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
lemma line_words (l : Fin 13) : negativeWords.getD (13 + l.val) 0 =
    ~~~(negativeWords.getD l.val 0 ||| negativeWords.getD (l + 1).val 0 |||
      negativeWords.getD (l + 3).val 0 ||| negativeWords.getD (l + 9).val 0) := by
  fin_cases l <;> decide +kernel

lemma negative_word_bits (b : BitVec 13) (i : Fin (13 + 13)) :
    (negativeWords.getD i.val 0).getLsbD b.toNat = canonicalMask q3Incidence b i := by
  have hb : b.toNat < 8192 := b.isLt
  cases i using @Fin.addCases 13 13 with
  | left p =>
    change (negativeWords.getD p.val 0).getLsbD b.toNat =
      canonicalMask q3Incidence b (Fin.castAdd 13 p)
    simpa only [canonicalMask, Fin.addCases_left] using point_word_bit p b
  | right l =>
    change (negativeWords.getD (13 + l.val) 0).getLsbD b.toNat =
      canonicalMask q3Incidence b (Fin.natAdd 13 l)
    rw [line_words, q3_mask_line]
    simp only [BitVec.getLsbD_not, BitVec.getLsbD_or, point_word_bit,
      hb, decide_true, Bool.true_and]

set_option maxRecDepth 100000 in
lemma negative_ofFn :
    List.ofFn (fun i : Fin 26 => negativeWords.getD i.val 0) = negativeWords := by
  decide +kernel

lemma negative_certificate (D : Circuit) (hAO : IsAO2 26 D)
    (hzero : wordEval D negativeWords = 0) :
    ∀ b : BitVec 13, circuitFun 26 D (canonicalMask q3Incidence b) = false := by
  intro b
  let X : Fin 26 → BitVec 8192 := fun i => negativeWords.getD i.val 0
  have hX : List.ofFn X = negativeWords := negative_ofFn
  have hz : wordEval D (List.ofFn X) = 0 := by rw [hX]; exact hzero
  have hv := zero_certificate D hAO X hz b.toNat
  have hr : (fun i : Fin 26 => (X i).getLsbD b.toNat) = canonicalMask q3Incidence b :=
    funext (fun i => negative_word_bits b i)
  simpa only [hr] using hv

def positivePairs : List (Fin 13 × Fin 13) :=
  [(0, 0), (0, 4), (0, 10), (0, 12), (1, 0), (1, 1), (1, 5), (1, 11), (2, 1), (2, 2), (2, 6), (2, 12), (3, 0), (3, 2), (3, 3), (3, 7), (4, 1), (4, 3), (4, 4), (4, 8), (5, 2), (5, 4), (5, 5), (5, 9), (6, 3), (6, 5), (6, 6), (6, 10), (7, 4), (7, 6), (7, 7), (7, 11), (8, 5), (8, 7), (8, 8), (8, 12), (9, 0), (9, 6), (9, 8), (9, 9), (10, 1), (10, 7), (10, 9), (10, 10), (11, 2), (11, 8), (11, 10), (11, 11), (12, 3), (12, 9), (12, 11), (12, 12)]

def positivePair (t : Fin 52) : Fin 13 × Fin 13 := positivePairs.getD t.val (0, 0)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma positive_word_bits : ∀ t : Fin 52, ∀ i : Fin 26,
    (positiveWords.getD i.val 0).getLsbD t.val =
      pairInput (Fin.castAdd 13 (positivePair t).1) (Fin.natAdd 13 (positivePair t).2) i := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma positive_covers : ∀ p l : Fin 13, q3Incidence p l →
    ∃ t : Fin 52, positivePair t = (p, l) := by
  decide +kernel

lemma positive_ofFn :
    List.ofFn (fun i : Fin 26 => positiveWords.getD i.val 0) = positiveWords := by
  decide +kernel

lemma positive_allones_bit : ∀ t : Fin 52,
    (0xfffffffffffff : BitVec 52).getLsbD t.val = true := by decide

lemma positive_certificate (D : Circuit) (hAO : IsAO2 26 D)
    (hfull : wordEval D positiveWords = (0xfffffffffffff : BitVec 52)) :
    ∀ p l : Fin 13, q3Incidence p l →
      circuitFun 26 D (pairInput (Fin.castAdd 13 p) (Fin.natAdd 13 l)) = true := by
  intro p l hi
  obtain ⟨t, ht⟩ := positive_covers p l hi
  let X : Fin 26 → BitVec 52 := fun i => positiveWords.getD i.val 0
  have hX : List.ofFn X = positiveWords := positive_ofFn
  have hv : circuitFun 26 D (fun i => (X i).getLsbD t.val) = true := by
    rw [← wordEval_sound D hAO X t.val, hX, hfull]
    exact positive_allones_bit t
  have hr : (fun i : Fin 26 => (X i).getLsbD t.val) =
      pairInput (Fin.castAdd 13 p) (Fin.natAdd 13 l) := by
    funext i
    change (positiveWords.getD i.val 0).getLsbD t.val = _
    rw [positive_word_bits, ht]
  simpa only [hr] using hv

lemma full_semantics_of_words (D : Circuit) (hAO : IsAO2 26 D)
    (hpos : wordEval D positiveWords = (0xfffffffffffff : BitVec 52))
    (hneg : wordEval D negativeWords = 0) :
    ∀ z : Fin 26 → Bool, circuitFun 26 D z =
      decide (∃ p l : Fin 13, q3Incidence p l ∧ z (Fin.castAdd 13 p) = true ∧
        z (Fin.natAdd 13 l) = true) :=
  ao2_semantics_of_masks q3Incidence D hAO
    (positive_certificate D hAO hpos) (negative_certificate D hAO hneg)

lemma canonical_full_semantics : ∀ z : Fin 26 → Bool, circuitFun 26 circuit z =
    decide (∃ p l : Fin 13, q3Incidence p l ∧ z (Fin.castAdd 13 p) = true ∧
      z (Fin.natAdd 13 l) = true) :=
  full_semantics_of_words circuit circuit_ao positive_word_certificate negative_word_certificate

end PEqualNP.Outside.L_meta_2583.Q3WordControl
