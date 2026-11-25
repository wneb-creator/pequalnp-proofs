import Mathlib.Tactic
import Mathlib.Data.List.OfFn
import Mathlib.Order.Monotone.Basic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma split_last_not (gs : List Gate) (hn : ∃ g ∈ gs, g.op = GateOp.not) :
    ∃ pre g post, gs = pre ++ g :: post ∧ g.op = GateOp.not ∧
      ∀ h ∈ post, h.op ≠ GateOp.not := by
  classical
  induction gs with
  | nil => simp at hn
  | cons a gs ih =>
    by_cases ht : ∃ g ∈ gs, g.op = GateOp.not
    · obtain ⟨pre, g, post, he, hop, hm⟩ := ih ht
      exact ⟨a :: pre, g, post, by simp only [he, List.cons_append], hop, hm⟩
    · have ha : a.op = GateOp.not := by
        obtain ⟨g, hg, hop⟩ := hn
        rcases List.mem_cons.mp hg with rfl | hg
        · exact hop
        · exact (ht ⟨g, hg, hop⟩).elim
      exact ⟨[], a, gs, rfl, ha, fun g hg hop => ht ⟨g, hg, hop⟩⟩

lemma wires_length (gs : List Gate) (x : List Bool) :
    (Circuit.wires ⟨gs, 0⟩ x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [Circuit.wires]
  | cons g gs ih =>
    change (Circuit.wires ⟨gs, 0⟩ (x ++ [_])).length = _
    rw [ih]
    simp only [List.length_append, List.length_singleton, List.length_cons, List.length_nil]
    omega

lemma cut_last_not (n : ℕ) (C : Circuit) (hf : FanInTwo C)
    (hn : ∃ g ∈ C.gates, g.op = GateOp.not) :
    ∃ P Q : Circuit, FanInTwo P ∧ Monotone2 Q ∧ P.size + Q.size + 1 = C.size ∧
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) =
        Q.eval (P.wires (List.ofFn x) ++ [!P.eval (List.ofFn x)]) := by
  obtain ⟨pre, g, post, he, hop, hpost⟩ := split_last_not C.gates hn
  let P : Circuit := ⟨pre, g.inputs.headD (n + pre.length)⟩
  let Q : Circuit := ⟨post, C.output⟩
  have hP : FanInTwo P := by
    intro h hh
    exact hf h (he ▸ List.mem_append_left _ hh)
  have hQ : Monotone2 Q := by
    intro h hh
    obtain ⟨ho, hi⟩ := hf h (he ▸ List.mem_append_right _ (List.mem_cons_of_mem _ hh))
    refine ⟨?_, hi⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ho ⊢
    rcases ho with ho | ho | ho
    · exact Or.inl ho
    · exact Or.inr ho
    · exact (hpost h hh ho).elim
  refine ⟨P, Q, hP, hQ, ?_, ?_⟩
  · simp only [P, Q, Circuit.size, he, List.length_append, List.length_cons]
    omega
  · intro x
    have hlen : (P.wires (List.ofFn x)).length = n + pre.length := by
      simpa only [P, Circuit.wires, List.length_ofFn] using wires_length pre (List.ofFn x)
    have hv : g.op.eval (g.inputs.map fun i => (P.wires (List.ofFn x)).getD i false) =
        !P.eval (List.ofFn x) := by
      rw [hop]
      cases hi : g.inputs with
      | nil =>
        change true = !(P.wires (List.ofFn x)).getD (g.inputs.headD (n + pre.length)) false
        rw [hi]
        simp only [List.headD_nil]
        rw [List.getD_eq_default _ _ (by omega)]
        rfl
      | cons i ins =>
        change (!((P.wires (List.ofFn x)).getD i false)) =
          (!((P.wires (List.ofFn x)).getD (g.inputs.headD (n + pre.length)) false))
        rw [hi]
        rfl
    change (C.gates.foldl _ (List.ofFn x)).getD C.output false = _
    rw [he, List.foldl_append]
    change Q.eval (P.wires (List.ofFn x) ++
      [g.op.eval (g.inputs.map fun i => (P.wires (List.ofFn x)).getD i false)]) = _
    rw [hv]

lemma monotone_snoc_value (l : List Bool) (v : Bool) :
    (l ++ [v]).getD l.length false = v := by
  simp [List.getD_eq_getElem?_getD]

lemma monotone_gate_value (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (ins : List ℕ) (a b : List Bool)
    (hab : ∀ i, a.getD i false = true → b.getD i false = true) :
    op.eval (ins.map fun i => a.getD i false) = true →
      op.eval (ins.map fun i => b.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun hall i hi => hab i (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, hv⟩ => ⟨i, hi, hab i hv⟩

lemma monotone_wires_value (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (a b : List Bool) (hlen : a.length = b.length)
    (hab : ∀ i, a.getD i false = true → b.getD i false = true) (i : ℕ) :
    (Circuit.wires ⟨gs, 0⟩ a).getD i false = true →
      (Circuit.wires ⟨gs, 0⟩ b).getD i false = true := by
  induction gs generalizing a b with
  | nil => exact hab i
  | cons g gs ih =>
    change (Circuit.wires ⟨gs, 0⟩ (a ++ [_])).getD i false = true →
      (Circuit.wires ⟨gs, 0⟩ (b ++ [_])).getD i false = true
    apply ih (fun h hh => hgs h (List.mem_cons_of_mem _ hh)) _ _ (by simp [hlen])
    intro j hj
    rcases Nat.lt_trichotomy j a.length with hj' | hj' | hj'
    · rw [List.getD_append _ _ _ _ hj'] at hj
      rw [List.getD_append _ _ _ _ (by omega)]
      exact hab j hj
    · rw [hj', monotone_snoc_value] at hj
      rw [hj', hlen, monotone_snoc_value]
      exact monotone_gate_value g.op (hgs g List.mem_cons_self) g.inputs a b hab hj
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
      contradiction

lemma monotone_circuit_value (n : ℕ) (C : Circuit) (hm : Monotone2 C)
    (a b : Fin n → Bool) (hab : ∀ i, a i = true → b i = true) :
    C.eval (List.ofFn a) = true → C.eval (List.ofFn b) = true := by
  apply monotone_wires_value C.gates
    (fun g hg => by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (hm g hg).1)
    (List.ofFn a) (List.ofFn b) (by simp) _ C.output
  intro i
  by_cases hi : i < n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, dite_true,
      Option.getD_some]
    exact hab ⟨i, hi⟩
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp

lemma monotone_prefix_cannot_end_in_not (n : ℕ) (C : Circuit) (hm : Monotone2 C)
    (f : (Fin n → Bool) → Bool) (hf0 : f (fun _ => false) = false)
    (hf1 : f (fun _ => true) = true) :
    ¬ ∀ x : Fin n → Bool, (!C.eval (List.ofFn x)) = f x := by
  intro he
  have h0 : C.eval (List.ofFn (fun _ : Fin n => false)) = true := by
    have hh := he (fun _ => false)
    rw [hf0] at hh
    cases hp : C.eval (List.ofFn (fun _ : Fin n => false)) <;> simp_all
  have h1 : C.eval (List.ofFn (fun _ : Fin n => true)) = true :=
    monotone_circuit_value n C hm _ _ (by simp) h0
  have hh := he (fun _ => true)
  rw [h1, hf1] at hh
  contradiction

lemma monotone_prefix_not_final_and (n : ℕ) (P : Circuit) (hm : Monotone2 P)
    (g : (Fin n → Bool) → Bool)
    (hone : ((!P.eval (List.ofFn (fun _ : Fin n => true))) && g (fun _ => true)) = true) :
    ∀ x : Fin n → Bool, ((!P.eval (List.ofFn x)) && g x) = g x := by
  have htop : P.eval (List.ofFn (fun _ : Fin n => true)) = false := by
    cases hp : P.eval (List.ofFn (fun _ : Fin n => true)) <;> simp_all
  intro x
  have hx : P.eval (List.ofFn x) = false := by
    cases he : P.eval (List.ofFn x) with
    | false => rfl
    | true =>
      have ht := monotone_circuit_value n P hm x (fun _ => true) (by simp) he
      rw [htop] at ht
      contradiction
  rw [hx]
  rfl

lemma monotone_prefix_not_final_or (n : ℕ) (P : Circuit) (hm : Monotone2 P)
    (g : (Fin n → Bool) → Bool)
    (hzero : ((!P.eval (List.ofFn (fun _ : Fin n => false))) || g (fun _ => false)) = false) :
    ∀ x : Fin n → Bool, ((!P.eval (List.ofFn x)) || g x) = g x := by
  have hbot : P.eval (List.ofFn (fun _ : Fin n => false)) = true := by
    cases hp : P.eval (List.ofFn (fun _ : Fin n => false)) <;> simp_all
  intro x
  have hx := monotone_circuit_value n P hm (fun _ => false) x (by simp) hbot
  rw [hx]
  rfl

def pruneStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma pruneRun_length (gs : List Gate) (w : List Bool) :
    (gs.foldl pruneStep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [pruneStep, ih]; omega

def pruneIndex (k a : ℕ) : ℕ := if k < a then a - 1 else a

lemma pruneRead (w : List Bool) {k a : ℕ} (hne : a ≠ k) :
    (w.eraseIdx k).getD (pruneIndex k a) false = w.getD a false := by
  simp only [List.getD_eq_getElem?_getD, pruneIndex]
  by_cases h : k < a
  · have ha : a - 1 + 1 = a := by omega
    simp [h, List.getElem?_eraseIdx_of_ge (show k ≤ a - 1 by omega), ha]
  · simp [h, List.getElem?_eraseIdx_of_lt (show a < k by omega)]

def pruneGate (k : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (pruneIndex k)⟩

lemma pruneRun (gs : List Gate) (k : ℕ) (w : List Bool)
    (hk : k < w.length) (hn : ∀ g ∈ gs, k ∉ g.inputs) :
    (gs.map (pruneGate k)).foldl pruneStep (w.eraseIdx k) =
      (gs.foldl pruneStep w).eraseIdx k := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    have hreads : (g.inputs.map (pruneIndex k)).map (fun i => (w.eraseIdx k).getD i false) =
        g.inputs.map (fun i => w.getD i false) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro a ha
      exact pruneRead _ (fun e => hn g (by simp) (e ▸ ha))
    have hstep : pruneStep (w.eraseIdx k) (pruneGate k g) = (pruneStep w g).eraseIdx k := by
      simp only [pruneStep, pruneGate, hreads, List.eraseIdx_append_of_lt_length hk]
    simp only [List.map_cons, List.foldl_cons, hstep]
    exact ih _ (by simp [pruneStep]; omega) (fun h hh => hn h (by simp [hh]))

def pruneCircuit (n : ℕ) (C : Circuit) (j : ℕ) : Circuit :=
  ⟨C.gates.take j ++ (C.gates.drop (j + 1)).map (pruneGate (n + j)),
    pruneIndex (n + j) C.output⟩

lemma pruneCircuit_run (C : Circuit) (w : List Bool) (j : ℕ) (hj : j < C.gates.length)
    (hn : ∀ g ∈ C.gates.drop (j + 1), w.length + j ∉ g.inputs) :
    ((pruneCircuit w.length C j).gates.foldl pruneStep w) =
      (C.gates.foldl pruneStep w).eraseIdx (w.length + j) := by
  let b := (C.gates.take j).foldl pruneStep w
  have hb : b.length = w.length + j := by
    simp [b, pruneRun_length, List.length_take, Nat.min_eq_left hj.le]
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
    simp [List.take_append_drop]
  have hlen : w.length + j < (pruneStep b C.gates[j]).length := by simp [pruneStep, hb]
  unfold pruneCircuit
  simp only [List.foldl_append]
  conv_rhs => rw [hsplit, List.foldl_append, List.foldl_cons]
  change ((C.gates.drop (j + 1)).map (pruneGate (w.length + j))).foldl pruneStep b =
    ((C.gates.drop (j + 1)).foldl pruneStep (pruneStep b C.gates[j])).eraseIdx (w.length + j)
  rw [← pruneRun _ _ _ hlen hn]
  congr 1
  simp [pruneStep, ← hb, List.eraseIdx_append_of_length_le]

lemma erase_unused_gate (n : ℕ) (C : Circuit) (j : ℕ) (hf : FanInTwo C)
    (hj : j < C.gates.length) (ho : C.output ≠ n + j)
    (hn : ∀ g ∈ C.gates.drop (j + 1), n + j ∉ g.inputs) :
    ∃ D : Circuit, FanInTwo D ∧ D.size + 1 = C.size ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x) := by
  refine ⟨pruneCircuit n C j, ?_, ?_, ?_⟩
  · intro g hg
    simp only [pruneCircuit, List.mem_append, List.mem_map] at hg
    rcases hg with hg | ⟨g', hg', rfl⟩
    · exact hf _ (List.mem_of_mem_take hg)
    · have hh := hf g' (List.mem_of_mem_drop hg')
      simpa [pruneGate] using hh
  · simp only [pruneCircuit, Circuit.size, List.length_append, List.length_take,
      List.length_map, List.length_drop, Nat.min_eq_left hj.le]
    omega
  · intro x
    have h := pruneCircuit_run C (List.ofFn x) j hj (by simpa using hn)
    simp only [List.length_ofFn] at h
    change (((pruneCircuit n C j).gates.foldl pruneStep (List.ofFn x))).getD
      (pruneIndex (n + j) C.output) false = _
    rw [h, pruneRead _ ho]
    rfl

lemma minimal_not_preserving_representative (n : ℕ) (C : Circuit) (hf : FanInTwo C)
    (hn : ∃ g ∈ C.gates, g.op = GateOp.not) :
    ∃ D : Circuit, FanInTwo D ∧ D.size ≤ C.size ∧
      ((∃ g ∈ D.gates, g.op = GateOp.not) ∨ D.size < C.size) ∧
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) ∧
      ∀ j < D.gates.length, D.output = n + j ∨
        ∃ g ∈ D.gates.drop (j + 1), n + j ∈ g.inputs := by
  classical
  let Good := fun D : Circuit => FanInTwo D ∧ D.size ≤ C.size ∧
    ((∃ g ∈ D.gates, g.op = GateOp.not) ∨ D.size < C.size) ∧
    ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)
  have hex : ∃ m : ℕ, ∃ D : Circuit, Good D ∧ D.size = m :=
    ⟨C.size, C, ⟨hf, le_rfl, Or.inl hn, fun _ => rfl⟩, rfl⟩
  obtain ⟨D, hD, hm⟩ := Nat.find_spec hex
  have hmin (E : Circuit) (hE : Good E) : Nat.find hex ≤ E.size :=
    Nat.find_min' hex ⟨E, hE, rfl⟩
  obtain ⟨hfD, hsizeD, hnotD, heqD⟩ := hD
  refine ⟨D, hfD, hsizeD, hnotD, heqD, ?_⟩
  intro j hj
  by_contra! unused
  obtain ⟨E, hfE, hsizeE, heqE⟩ := erase_unused_gate n D j hfD hj unused.1 unused.2
  have hEC : E.size < C.size := by omega
  have hgoodE : Good E :=
    ⟨hfE, hEC.le, Or.inr hEC, fun x => (heqE x).trans (heqD x)⟩
  have hmE := hmin E hgoodE
  omega

lemma used_gates_output_last (n : ℕ) (D : Circuit) (hne : D.gates ≠ [])
    (hused : ∀ j < D.gates.length, D.output = n + j ∨
      ∃ g ∈ D.gates.drop (j + 1), n + j ∈ g.inputs) :
    D.output + 1 = n + D.size := by
  have hpos : 0 < D.gates.length := List.length_pos_iff.mpr hne
  have hj : D.gates.length - 1 < D.gates.length := by omega
  rcases hused (D.gates.length - 1) hj with he | ⟨g, hg, _⟩
  · unfold Circuit.size
    omega
  · have hlen : D.gates.length - 1 + 1 = D.gates.length := by omega
    rw [hlen, List.drop_length] at hg
    contradiction

abbrev PetInput := Fin 10 → Bool

def petMask (m : ℕ) : PetInput := fun i => m.testBit i.val

def petEdges : List ℕ := [3, 6, 12, 24, 17, 33, 66, 132, 264, 528, 160, 640, 576, 320, 288]

def petBlockers : List ℕ := [50, 69, 104, 116, 138, 201, 208, 276, 385, 402, 521, 548, 554, 770, 773]

def petFunction (x : PetInput) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

lemma petMask_surjective (x : PetInput) : ∃ m : Fin 1024, petMask m = x := by
  let b := BitVec.ofBoolListLE (List.ofFn x)
  have small : b.toNat < 1024 := by simpa [b] using b.isLt
  refine ⟨⟨b.toNat, small⟩, ?_⟩
  funext i
  change b.getLsbD i.val = x i
  dsimp only [b]
  rw [BitVec.getLsbD_ofBoolListLE]
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp only [i.isLt, dite_true, Option.getD_some]

lemma petMask_le_of_and_eq (a b : ℕ) (h : a &&& b = a) : petMask a ≤ petMask b := by
  intro i
  have same := congrArg (fun k => k.testBit i.val) h
  rw [Nat.testBit_and] at same
  change a.testBit i.val ≤ b.testBit i.val
  cases ha : a.testBit i.val <;> cases hb : b.testBit i.val <;> simp_all

def petBoundaryTest (m : ℕ) : Bool :=
  if petFunction (petMask m) then petEdges.any (fun e => m &&& e == e)
  else petBlockers.any (fun z => m &&& z == m)

lemma pet_boundary_chunk0 : ∀ m : Fin 64, petBoundaryTest (0 + m.val) = true := by
  decide +kernel
lemma pet_boundary_chunk1 : ∀ m : Fin 64, petBoundaryTest (64 + m.val) = true := by
  decide +kernel
lemma pet_boundary_chunk2 : ∀ m : Fin 64, petBoundaryTest (128 + m.val) = true := by
  decide +kernel
lemma pet_boundary_chunk3 : ∀ m : Fin 64, petBoundaryTest (192 + m.val) = true := by
  decide +kernel
lemma pet_boundary_chunk4 : ∀ m : Fin 64, petBoundaryTest (256 + m.val) = true := by
  decide +kernel
lemma pet_boundary_chunk5 : ∀ m : Fin 64, petBoundaryTest (320 + m.val) = true := by
  decide +kernel
lemma pet_boundary_chunk6 : ∀ m : Fin 64, petBoundaryTest (384 + m.val) = true := by
  decide +kernel
lemma pet_boundary_chunk7 : ∀ m : Fin 64, petBoundaryTest (448 + m.val) = true := by
  decide +kernel
lemma pet_boundary_chunk8 : ∀ m : Fin 64, petBoundaryTest (512 + m.val) = true := by
  decide +kernel
lemma pet_boundary_chunk9 : ∀ m : Fin 64, petBoundaryTest (576 + m.val) = true := by
  decide +kernel
lemma pet_boundary_chunk10 : ∀ m : Fin 64, petBoundaryTest (640 + m.val) = true := by
  decide +kernel
lemma pet_boundary_chunk11 : ∀ m : Fin 64, petBoundaryTest (704 + m.val) = true := by
  decide +kernel
lemma pet_boundary_chunk12 : ∀ m : Fin 64, petBoundaryTest (768 + m.val) = true := by
  decide +kernel
lemma pet_boundary_chunk13 : ∀ m : Fin 64, petBoundaryTest (832 + m.val) = true := by
  decide +kernel
lemma pet_boundary_chunk14 : ∀ m : Fin 64, petBoundaryTest (896 + m.val) = true := by
  decide +kernel
lemma pet_boundary_chunk15 : ∀ m : Fin 64, petBoundaryTest (960 + m.val) = true := by
  decide +kernel

lemma pet_boundary_table (m : Fin 1024) :
    (if petFunction (petMask m) then petEdges.any (fun e => m.val &&& e == e)
      else petBlockers.any (fun z => m.val &&& z == m.val)) = true := by
  change petBoundaryTest m.val = true
  have quotient : m.val / 64 < 16 := by omega
  have remainder : m.val % 64 < 64 := Nat.mod_lt _ (by decide)
  interval_cases hq : m.val / 64
  · simpa only [show 0 + m.val % 64 = m.val by omega] using
      pet_boundary_chunk0 ⟨m.val % 64, remainder⟩
  · simpa only [show 64 + m.val % 64 = m.val by omega] using
      pet_boundary_chunk1 ⟨m.val % 64, remainder⟩
  · simpa only [show 128 + m.val % 64 = m.val by omega] using
      pet_boundary_chunk2 ⟨m.val % 64, remainder⟩
  · simpa only [show 192 + m.val % 64 = m.val by omega] using
      pet_boundary_chunk3 ⟨m.val % 64, remainder⟩
  · simpa only [show 256 + m.val % 64 = m.val by omega] using
      pet_boundary_chunk4 ⟨m.val % 64, remainder⟩
  · simpa only [show 320 + m.val % 64 = m.val by omega] using
      pet_boundary_chunk5 ⟨m.val % 64, remainder⟩
  · simpa only [show 384 + m.val % 64 = m.val by omega] using
      pet_boundary_chunk6 ⟨m.val % 64, remainder⟩
  · simpa only [show 448 + m.val % 64 = m.val by omega] using
      pet_boundary_chunk7 ⟨m.val % 64, remainder⟩
  · simpa only [show 512 + m.val % 64 = m.val by omega] using
      pet_boundary_chunk8 ⟨m.val % 64, remainder⟩
  · simpa only [show 576 + m.val % 64 = m.val by omega] using
      pet_boundary_chunk9 ⟨m.val % 64, remainder⟩
  · simpa only [show 640 + m.val % 64 = m.val by omega] using
      pet_boundary_chunk10 ⟨m.val % 64, remainder⟩
  · simpa only [show 704 + m.val % 64 = m.val by omega] using
      pet_boundary_chunk11 ⟨m.val % 64, remainder⟩
  · simpa only [show 768 + m.val % 64 = m.val by omega] using
      pet_boundary_chunk12 ⟨m.val % 64, remainder⟩
  · simpa only [show 832 + m.val % 64 = m.val by omega] using
      pet_boundary_chunk13 ⟨m.val % 64, remainder⟩
  · simpa only [show 896 + m.val % 64 = m.val by omega] using
      pet_boundary_chunk14 ⟨m.val % 64, remainder⟩
  · simpa only [show 960 + m.val % 64 = m.val by omega] using
      pet_boundary_chunk15 ⟨m.val % 64, remainder⟩

lemma pet_boundary_values :
    (∀ m ∈ petEdges, petFunction (petMask m) = true) ∧
    (∀ m ∈ petBlockers, petFunction (petMask m) = false) := by
  decide +kernel

lemma pet_boundary :
    (∀ x : PetInput, petFunction x = true →
      ∃ m ∈ petEdges, petMask m ≤ x ∧ petFunction (petMask m) = true) ∧
    (∀ x : PetInput, petFunction x = false →
      ∃ m ∈ petBlockers, x ≤ petMask m ∧ petFunction (petMask m) = false) := by
  constructor
  · intro x hx
    obtain ⟨m, rfl⟩ := petMask_surjective x
    have table := pet_boundary_table m
    rw [hx] at table
    simp only [reduceIte] at table
    obtain ⟨e, member, overlap⟩ := List.any_eq_true.mp table
    have same : m.val &&& e = e := by simpa using overlap
    exact ⟨e, member, petMask_le_of_and_eq e m (by simpa [Nat.and_comm] using same),
      pet_boundary_values.1 e member⟩
  · intro x hx
    obtain ⟨m, rfl⟩ := petMask_surjective x
    have table := pet_boundary_table m
    rw [hx] at table
    simp only [Bool.false_eq_true, reduceIte] at table
    obtain ⟨z, member, overlap⟩ := List.any_eq_true.mp table
    have same : m.val &&& z = m.val := by simpa using overlap
    exact ⟨z, member, petMask_le_of_and_eq m z same, pet_boundary_values.2 z member⟩

lemma petBlockers_maximal : ∀ m ∈ petBlockers, ∀ i : Fin 10,
    petMask m i = false → petFunction (Function.update (petMask m) i true) = true := by
  decide +kernel

lemma oneNot_essential_witnesses (h : PetInput → Bool) (G : PetInput → Bool → Bool)
    (sourceMono : Monotone h) (inputMono : ∀ z, Monotone (fun x => G x z))
    (bitMono : ∀ x, Monotone (G x))
    (correct : ∀ x, G x (!h x) = petFunction x)
    (falseChanges : ∃ x, G x false ≠ petFunction x)
    (trueChanges : ∃ x, G x true ≠ petFunction x) :
    (∃ m ∈ petEdges, h (petMask m) = false ∧ G (petMask m) false = false ∧
      petFunction (petMask m) = true) ∧
    (∃ m ∈ petBlockers, h (petMask m) = true ∧ G (petMask m) true = true ∧
      petFunction (petMask m) = false) := by
  constructor
  · obtain ⟨x, changed⟩ := falseChanges
    have below : G x false ≤ petFunction x := by
      rw [← correct x]
      exact bitMono x (Bool.false_le _)
    have value : petFunction x = true := by
      cases hg : G x false <;> cases hf : petFunction x <;> simp_all
      cases Bool.eq_false_of_le_false below
    have oldValue : G x false = false := by
      cases hg : G x false <;> simp_all
    have source : h x = false := by
      cases hh : h x
      · rfl
      · have same := correct x
        simp only [hh, Bool.not_true] at same
        exact (changed same).elim
    obtain ⟨m, member, smaller, edge⟩ := pet_boundary.1 x value
    refine ⟨m, member, ?_, ?_, edge⟩
    · have bound := sourceMono smaller
      rw [source] at bound
      exact le_antisymm bound (Bool.false_le _)
    · have bound : G (petMask m) false ≤ G x false := inputMono false smaller
      rw [oldValue] at bound
      exact le_antisymm bound (Bool.false_le _)
  · obtain ⟨x, changed⟩ := trueChanges
    have above : petFunction x ≤ G x true := by
      rw [← correct x]
      exact bitMono x (Bool.le_true _)
    have value : petFunction x = false := by
      cases hg : G x true <;> cases hf : petFunction x <;> simp_all
      cases Bool.eq_false_of_le_false above
    have oldValue : G x true = true := by
      cases hg : G x true <;> simp_all
    have source : h x = true := by
      cases hh : h x
      · have same := correct x
        simp only [hh, Bool.not_false] at same
        exact (changed same).elim
      · rfl
    obtain ⟨m, member, larger, independent⟩ := pet_boundary.2 x value
    refine ⟨m, member, ?_, ?_, independent⟩
    · have bound := sourceMono larger
      rw [source] at bound
      exact le_antisymm (Bool.le_true _) bound
    · have bound : G x true ≤ G (petMask m) true := inputMono true larger
      rw [oldValue] at bound
      exact le_antisymm (Bool.le_true _) bound

end PEqualNP.Outside.L_meta_2592_aux
