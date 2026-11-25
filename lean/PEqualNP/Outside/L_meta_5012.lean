import PEqualNP.Defs
import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace PEqualNP.Outside.L_meta_5012_aux




open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
  PEqualNP.CleanedNonEdge PEqualNP.TopForm

def gateBit (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def stepWire (w : List Bool) (g : Gate) : List Bool := w ++ [gateBit w g]

def WiresLE (w z : List Bool) : Prop :=
  w.length = z.length ∧ ∀ i, w.getD i false = true → z.getD i false = true

def IsMonoGate (g : Gate) : Prop := g.op = GateOp.and ∨ g.op = GateOp.or

lemma monoGate_of_mem {C : Circuit} (hC : Monotone2 C) {g : Gate} (hg : g ∈ C.gates) :
    IsMonoGate g := by
  simpa [IsMonoGate] using (hC g hg).1

lemma bit_mono {w z : List Bool} (h : WiresLE w z) {g : Gate} (hg : IsMonoGate g)
    (hw : gateBit w g = true) : gateBit z g = true := by
  rcases hg with hop | hop
  · simp only [gateBit, hop, GateOp.eval, List.all_map, List.all_eq_true,
      Function.comp_apply, id_eq] at hw ⊢
    exact fun i hi => h.2 i (hw i hi)
  · simp only [gateBit, hop, GateOp.eval, List.any_map, List.any_eq_true,
      Function.comp_apply, id_eq] at hw ⊢
    obtain ⟨i, hi, hv⟩ := hw
    exact ⟨i, hi, h.2 i hv⟩

lemma append_mono {w z : List Bool} {a b : Bool} (h : WiresLE w z)
    (hab : a = true → b = true) : WiresLE (w ++ [a]) (z ++ [b]) := by
  refine ⟨by simp [h.1], ?_⟩
  intro i hi
  rw [List.getD_eq_getElem?_getD] at hi ⊢
  by_cases hlt : i < w.length
  · rw [List.getElem?_append_left hlt] at hi
    rw [List.getElem?_append_left (by rwa [← h.1])]
    simpa only [List.getD_eq_getElem?_getD] using h.2 i
      (by simpa only [List.getD_eq_getElem?_getD] using hi)
  · rw [List.getElem?_append_right (Nat.le_of_not_gt hlt)] at hi
    rw [List.getElem?_append_right (by rw [← h.1]; omega), ← h.1]
    cases hd : i - w.length with
    | zero =>
      simp only [hd, List.getElem?_cons_zero, Option.getD_some] at hi ⊢
      exact hab hi
    | succ k => simp [hd] at hi

lemma fold_mono (gs : List Gate) (hg : ∀ g ∈ gs, IsMonoGate g)
    {w z : List Bool} (h : WiresLE w z) :
    WiresLE (gs.foldl stepWire w) (gs.foldl stepWire z) := by
  induction gs generalizing w z with
  | nil => exact h
  | cons g gs ih =>
    exact ih (fun k hk => hg k (List.mem_cons_of_mem _ hk))
      (append_mono h (bit_mono h (hg g (by simp))))

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma fold_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (stepWire w g) (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma ofFn_getD {n : ℕ} (x : Fin n → Bool) (u : Fin n) :
    (List.ofFn x).getD u.val false = x u := by
  simp [List.getD_eq_getElem?_getD]

lemma ofFn_mono {n : ℕ} {x y : Fin n → Bool} (h : ∀ u, x u = true → y u = true) :
    WiresLE (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp, ?_⟩
  intro i hi
  by_cases hlt : i < n
  · rw [ofFn_getD y ⟨i, hlt⟩]
    exact h ⟨i, hlt⟩ (by simpa only [ofFn_getD x ⟨i, hlt⟩] using hi)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hlt)] at hi
    cases hi

def patch (C : Circuit) (j : ℕ) (g : Gate) : Circuit := ⟨C.gates.set j g, C.output⟩

def earlierWires (C : Circuit) (j : ℕ) (w : List Bool) : List Bool :=
  (C.gates.take j).foldl stepWire w

def off : Gate := ⟨GateOp.or, []⟩


lemma off_bit (w : List Bool) : gateBit w off = false := rfl


lemma wires_patch {C : Circuit} {j : ℕ} (hj : j < C.gates.length) (g : Gate) (w : List Bool) :
    (patch C j g).wires w = (C.gates.drop (j + 1)).foldl stepWire (stepWire (earlierWires C j w) g) := by
  change (C.gates.set j g).foldl stepWire w = _
  rw [List.set_eq_take_append_cons_drop, ite_eq_left hj, List.foldl_append, List.foldl_cons]
  rfl

lemma original_patch {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    patch C j C.gates[j] = C := by
  cases C with
  | mk gates output =>
    change Circuit.mk (gates.set j gates[j]) output = Circuit.mk gates output
    congr 1
    exact List.set_getElem_self hj

lemma patch_mono {C : Circuit} (hC : Monotone2 C) {j : ℕ} (hj : j < C.gates.length)
    (g h : Gate) (w : List Bool)
    (hbit : gateBit (earlierWires C j w) g = true → gateBit (earlierWires C j w) h = true) :
    WiresLE ((patch C j g).wires w) ((patch C j h).wires w) := by
  rw [wires_patch hj, wires_patch hj]
  apply fold_mono _ (fun k hk => monoGate_of_mem hC (List.mem_of_mem_drop hk))
  exact append_mono ⟨rfl, fun _ h => h⟩ hbit

lemma patch_bit {n : ℕ} {C : Circuit} {j : ℕ} (hj : j < C.gates.length)
    (g : Gate) (x : Fin n → Bool) :
    gateVal n (patch C j g) j x = gateBit (earlierWires C j (List.ofFn x)) g := by
  have hlen : (earlierWires C j (List.ofFn x)).length = n + j := by
    unfold earlierWires
    rw [fold_length]
    simp [Nat.min_eq_left (Nat.le_of_lt hj)]
  unfold gateVal
  rw [wires_patch hj, fold_getD_lt _ _ _ (by simp [stepWire, hlen]), ← hlen]
  simp [stepWire, List.getD_eq_getElem?_getD]


lemma gateAt_patch_ne (C : Circuit) (j k : ℕ) (g : Gate) (hne : j ≠ k) :
    gateAt (patch C j g) k = gateAt C k := by
  simp [patch, gateAt, List.getD_eq_getElem?_getD, List.getElem?_set_ne hne]

lemma graph_true {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
  simp [graphFun]

lemma pair_le {n : ℕ} {x : Fin n → Bool} {u v : Fin n}
    (hu : x u = true) (hv : x v = true) (k : Fin n) :
    pairInput u v k = true → x k = true := by
  simp only [pairInput, decide_eq_true_eq]
  rintro (rfl | rfl)
  · exact hu
  · exact hv

lemma circuit_mono {n : ℕ} {C : Circuit} (hC : Monotone2 C) {x y : Fin n → Bool}
    (hxy : ∀ u, x u = true → y u = true) :
    circuitFun n C x = true → circuitFun n C y = true :=
  (fold_mono C.gates (fun _ hg => monoGate_of_mem hC hg) (ofFn_mono hxy)).2 C.output

lemma mem_junk {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {j : ℕ} :
    j ∈ junk G C ↔ j < C.gates.length ∧ IsDirtyAnd n G C j := by
  unfold junk gatesWhere
  rw [Finset.mem_filter, Finset.mem_range]

lemma ao_mono {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) : Monotone2 C := by
  intro r hr
  exact ⟨by simpa using hAO.1 r hr, (hAO.2.2 r hr).le⟩

lemma patch_gate_ao {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) (r : Gate)
    (hrop : IsMonoGate r) (hrlen : r.inputs.length = 2)
    (hrback : ∀ i ∈ r.inputs, i < n + j) : IsAO2 n (patch C j r) := by
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    rcases List.mem_or_eq_of_mem_set hq with hq | rfl
    · exact hAO.1 q hq
    · exact hrop
  · intro k hk i hi
    have hkc : k < C.gates.length := by simpa [patch] using hk
    by_cases h : j = k
    · subst k
      have he : gateAt (patch C j r) j = r := by
        simp [gateAt, patch, List.getD_eq_getElem?_getD, hj]
      rw [he] at hi
      exact hrback i hi
    · rw [gateAt_patch_ne C j k r h] at hi
      exact hAO.2.1 k hkc i hi
  · intro q hq
    rcases List.mem_or_eq_of_mem_set hq with hq | rfl
    · exact hAO.2.2 q hq
    · exact hrlen


lemma gateVal_patch_before {n : ℕ} {C : Circuit} {j k : ℕ}
    (hj : j < C.gates.length) (hkj : k < j) (r : Gate) (x : Fin n → Bool) :
    gateVal n (patch C j r) k x = gateVal n C k x := by
  have hlen : (earlierWires C j (List.ofFn x)).length = n + j := by
    unfold earlierWires
    rw [fold_length]
    simp [Nat.min_eq_left hj.le]
  have hp (r : Gate) : gateVal n (patch C j r) k x =
      (earlierWires C j (List.ofFn x)).getD (n + k) false := by
    unfold gateVal
    rw [wires_patch hj, fold_getD_lt _ _ _ (by simp [stepWire, hlen]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (show n + k < (earlierWires C j (List.ofFn x)).length by omega)]
  rw [hp, ← hp C.gates[j], original_patch hj]




lemma earlier_read_eq_wireVal {n : ℕ} {C : Circuit} {j w : ℕ}
    (hj : j < C.gates.length) (hw : w < n + j) (x : Fin n → Bool) :
    (earlierWires C j (List.ofFn x)).getD w false = wireVal n C w x := by
  have hlen : (earlierWires C j (List.ofFn x)).length = n + j := by
    unfold earlierWires
    rw [fold_length]
    simp [Nat.min_eq_left hj.le]
  calc
    (earlierWires C j (List.ofFn x)).getD w false =
        ((patch C j C.gates[j]).wires (List.ofFn x)).getD w false := by
      rw [wires_patch hj, fold_getD_lt _ _ _ (by simp [stepWire, hlen]; omega)]
      simp [stepWire, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (show w < (earlierWires C j (List.ofFn x)).length by omega)]
    _ = wireVal n C w x := by rw [original_patch hj]; rfl










namespace FourClauses

def matrixCode (R : Fin 3 → Fin 3 → Bool) : Nat :=
  (if R 0 1 then 1 else 0) + (if R 0 2 then 2 else 0) +
  (if R 1 0 then 4 else 0) + (if R 1 2 then 8 else 0) +
  (if R 2 0 then 16 else 0) + (if R 2 1 then 32 else 0)

def certificate (R : Fin 3 → Fin 3 → Bool) : List Nat :=
  match matrixCode R with
  | 0 => [7, 14, 21, 28, 35]
  | 1 => [7, 14, 28, 35, 42]
  | 2 => [7, 14, 21, 28, 42]
  | 3 => [7, 14, 28, 42, 56]
  | 4 => [7, 21, 28, 35, 49]
  | 6 => [7, 21, 28, 34, 56]
  | 8 => [7, 14, 21, 28, 49]
  | 9 => [7, 14, 28, 33, 56]
  | 10 => [7, 14, 21, 28, 56]
  | 12 => [7, 21, 28, 49, 56]
  | 16 => [7, 21, 35, 42, 49]
  | 17 => [7, 20, 35, 42, 56]
  | 20 => [7, 21, 35, 49, 56]
  | 24 => [7, 10, 21, 49, 56]
  | 25 => [7, 10, 20, 33, 56]
  | 32 => [7, 14, 35, 42, 49]
  | 33 => [7, 14, 35, 42, 56]
  | 34 => [7, 14, 17, 42, 56]
  | 36 => [7, 12, 35, 49, 56]
  | 38 => [7, 12, 17, 34, 56]
  | 48 => [7, 35, 42, 49, 56]
  | _ => []

def leftBit (R : Fin 3 → Fin 3 → Bool) (k : Fin 5) (i : Fin 3) : Bool :=
  Nat.testBit ((certificate R).getD k.val 0) i.val

def rightBit (R : Fin 3 → Fin 3 → Bool) (k : Fin 5) (i : Fin 3) : Bool :=
  Nat.testBit ((certificate R).getD k.val 0) (3 + i.val)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma certificate_valid : ∀ (R : Fin 3 → Fin 3 → Bool),
    (∀ i, R i i = true) →
    (∀ i i' j j', i ≠ i' → j ≠ j' →
      R i j = true → R i j' = true → R i' j = true → R i' j' = true → False) →
    (∀ k : Fin 5, ∀ i j : Fin 3,
      leftBit R k i = true → rightBit R k j = true → R i j = false) ∧
    (∀ k l : Fin 5, k ≠ l → ∃ i : Fin 3,
      (leftBit R k i = true ∧ rightBit R l i = true) ∨
      (rightBit R k i = true ∧ leftBit R l i = true)) := by
  decide

lemma independent_four_clauses (R : Fin 3 → Fin 3 → Bool)
    (diag : ∀ i, R i i = true)
    (no4 : ∀ i i' j j', i ≠ i' → j ≠ j' →
      R i j = true → R i j' = true → R i' j = true → R i' j' = true → False)
    (clause : Fin 4 → Fin 3 → Bool) :
    ∃ U V : Fin 3 → Bool,
      (∀ i j, U i = true → V j = true → R i j = false) ∧
      ∀ k, ∃ i, (U i = true ∧ clause k i = true) ∨
        (V i = true ∧ clause k i = false) := by
  classical
  obtain ⟨hind, hsep⟩ := certificate_valid R diag no4
  by_contra hn
  have hbad : ∀ t : Fin 5, ∃ k : Fin 4, ¬ ∃ i : Fin 3,
      (leftBit R t i = true ∧ clause k i = true) ∨
      (rightBit R t i = true ∧ clause k i = false) := by
    intro t
    by_contra ht
    apply hn
    refine ⟨leftBit R t, rightBit R t, hind t, ?_⟩
    intro k
    by_contra hk
    exact ht ⟨k, hk⟩
  choose f hf using hbad
  have hni : ¬ Function.Injective f :=
    Fintype.not_injective_of_card_lt f (by decide)
  have hex : ∃ t u : Fin 5, f t = f u ∧ t ≠ u := by
    by_contra h
    apply hni
    intro t u he
    by_contra htu
    exact h ⟨t, u, he, htu⟩
  obtain ⟨t, u, hfu, htu⟩ := hex
  obtain ⟨i, hcross⟩ := hsep t u htu
  cases hc : clause (f t) i with
  | false =>
    rcases hcross with h | h
    · exact hf u ⟨i, Or.inr ⟨h.2, by simpa [hfu] using hc⟩⟩
    · exact hf t ⟨i, Or.inr ⟨h.1, hc⟩⟩
  | true =>
    rcases hcross with h | h
    · exact hf t ⟨i, Or.inl ⟨h.1, hc⟩⟩
    · exact hf u ⟨i, Or.inl ⟨h.2, by simpa [hfu] using hc⟩⟩

end FourClauses


namespace FourClausePullback

open PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover

lemma no_four_edges {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (a b c d : Fin n) (hab : a ≠ b) (hcd : c ≠ d)
    (hac : G.Adj a c) (had : G.Adj a d) (hbc : G.Adj b c) (hbd : G.Adj b d) : False := by
  have hcard := h4 a b hab
  have hsub : ({c, d} : Finset (Fin n)) ⊆
      Finset.univ.filter (fun w => G.Adj a w ∧ G.Adj b w) := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · simp [hac, hbc]
    · simp [had, hbd]
  have hle := Finset.card_le_card hsub
  rw [Finset.card_pair hcd] at hle
  omega

lemma no_matching_of_finite
    (finite : ∀ (R : Fin 3 → Fin 3 → Bool),
      (∀ i, R i i = true) →
      (∀ i i' j j', i ≠ i' → j ≠ j' → R i j = true → R i j' = true →
        R i' j = true → R i' j' = true → False) →
      ∀ clause : Fin 4 → Fin 3 → Bool, ∃ U V : Fin 3 → Bool,
        (∀ i j, U i = true → V j = true → R i j = false) ∧
        ∀ k, ∃ i, (U i = true ∧ clause k i = true) ∨
          (V i = true ∧ clause k i = false))
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : NoFourCycle G) (A : Fin 4 → Finset (Fin n))
    (hclean : ∀ x : Fin n → Bool,
      (∀ k, ∃ u ∈ A k, x u = true) → graphFun G ∅ x = true)
    (left right : Fin 3 → Fin n)
    (hleft : Function.Injective left) (hright : Function.Injective right)
    (hleftcol : ∀ i, s (left i) = false) (hrightcol : ∀ i, s (right i) = true)
    (hedge : ∀ i, G.Adj (left i) (right i))
    (haccept : ∀ i k, left i ∈ A k ∨ right i ∈ A k) : False := by
  classical
  let R : Fin 3 → Fin 3 → Bool := fun i j => decide (G.Adj (left i) (right j))
  have hdiag : ∀ i, R i i = true := by
    intro i
    simpa [R] using hedge i
  have hR4 : ∀ i i' j j', i ≠ i' → j ≠ j' → R i j = true → R i j' = true →
      R i' j = true → R i' j' = true → False := by
    intro i i' j j' hii hjj hij hij' hi'j hi'j'
    apply no_four_edges G h4 (left i) (left i') (right j) (right j')
      (fun h => hii (hleft h)) (fun h => hjj (hright h))
    · simpa [R] using hij
    · simpa [R] using hij'
    · simpa [R] using hi'j
    · simpa [R] using hi'j'
  let clause : Fin 4 → Fin 3 → Bool := fun k i => decide (left i ∈ A k)
  obtain ⟨U, V, hindep, hhit⟩ := finite R hdiag hR4 clause
  let x : Fin n → Bool := fun v => decide
    ((∃ i, U i = true ∧ v = left i) ∨ (∃ i, V i = true ∧ v = right i))
  have hxleft (i : Fin 3) (hi : U i = true) : x (left i) = true := by
    simp only [x, decide_eq_true_eq]
    exact Or.inl ⟨i, hi, rfl⟩
  have hxright (i : Fin 3) (hi : V i = true) : x (right i) = true := by
    simp only [x, decide_eq_true_eq]
    exact Or.inr ⟨i, hi, rfl⟩
  have hall : ∀ k, ∃ u ∈ A k, x u = true := by
    intro k
    obtain ⟨i, h | h⟩ := hhit k
    · refine ⟨left i, ?_, hxleft i h.1⟩
      simpa [clause] using h.2
    · refine ⟨right i, ?_, hxright i h.1⟩
      have hnot : left i ∉ A k := by simpa [clause] using h.2
      exact (haccept i k).resolve_left hnot
  have hout := hclean x hall
  have hgraph : graphFun G ∅ x = true ↔
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by simp [graphFun]
  obtain ⟨u, v, huv, hu, hv⟩ := hgraph.mp hout
  simp only [x, decide_eq_true_eq] at hu hv
  rcases hu with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ <;>
    rcases hv with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
  · exact hcol _ _ huv ((hleftcol i).trans (hleftcol j).symm)
  · have hno := hindep i j hi hj
    have hyes : R i j = true := by simpa [R] using huv
    rw [hyes] at hno
    cases hno
  · have hno := hindep j i hj hi
    have hyes : R j i = true := by simpa [R] using huv.symm
    rw [hyes] at hno
    cases hno
  · exact hcol _ _ huv ((hrightcol i).trans (hrightcol j).symm)

end FourClausePullback

namespace FourClausePullback

open PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover

lemma no_three_disjoint_accepted_edges
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : NoFourCycle G) (A : Fin 4 → Finset (Fin n))
    (hclean : ∀ x : Fin n → Bool,
      (∀ k, ∃ u ∈ A k, x u = true) → graphFun G ∅ x = true) :
    ¬ ∃ left right : Fin 3 → Fin n,
      Function.Injective left ∧ Function.Injective right ∧
      (∀ i, s (left i) = false) ∧ (∀ i, s (right i) = true) ∧
      (∀ i, G.Adj (left i) (right i)) ∧
      (∀ i k, left i ∈ A k ∨ right i ∈ A k) := by
  rintro ⟨left, right, hl, hr, hlc, hrc, he, ha⟩
  exact no_matching_of_finite FourClauses.independent_four_clauses
    G s hcol h4 A hclean left right hl hr hlc hrc he ha

end FourClausePullback


namespace TwoCover

def NoThree {α : Type} (R : α → α → Prop) : Prop :=
  ∀ a c e b d f, a ≠ c → a ≠ e → c ≠ e → b ≠ d → b ≠ f → d ≠ f →
    R a b → R c d → R e f → False

lemma edge_touches {α : Type} {R : α → α → Prop} (h3 : NoThree R)
    {a c b d : α} (hac : a ≠ c) (hbd : b ≠ d) (hab : R a b) (hcd : R c d)
    {u v : α} (huv : R u v) : u = a ∨ u = c ∨ v = b ∨ v = d := by
  by_contra hn
  push Not at hn
  exact h3 a c u b d v hac hn.1.symm hn.2.1.symm hbd hn.2.2.1.symm
    hn.2.2.2.symm hab hcd huv

lemma cover_with_external {α : Type} [DecidableEq α] {R : α → α → Prop}
    (h3 : NoThree R) {a c b d x : α}
    (hac : a ≠ c) (hbd : b ≠ d) (hab : R a b) (hcd : R c d)
    (hax : R a x) (hxb : x ≠ b) (hxd : x ≠ d) :
    ∃ K : Finset α, K.card ≤ 2 ∧ ∀ u v, R u v → u ∈ K ∨ v ∈ K := by
  classical
  have no_b : ∀ u, u ≠ a → u ≠ c → ¬ R u b := by
    intro u hua huc hub
    exact h3 a c u x d b hac hua.symm huc.symm hxd hxb hbd.symm hax hcd hub
  by_cases hd : ∃ u, u ≠ a ∧ u ≠ c ∧ R u d
  · obtain ⟨l, hla, hlc, hld⟩ := hd
    have no_c_ext : ∀ v, v ≠ b → v ≠ d → ¬ R c v := by
      intro v hvb hvd hcv
      exact h3 a c l b v d hac hla.symm hlc.symm hvb.symm hbd hvd hab hcv hld
    have no_cb : ¬ R c b := by
      intro hcb
      exact h3 a c l x b d hac hla.symm hlc.symm hxb hxd hbd hax hcb hld
    refine ⟨{a, d}, Finset.card_le_two, ?_⟩
    intro u v huv
    by_cases hua : u = a
    · subst u; exact Or.inl (by simp)
    by_cases hvd : v = d
    · subst v; exact Or.inr (by simp)
    exfalso
    have hb : v = b := by
      by_contra hvb
      rcases edge_touches h3 hac hbd hab hcd huv with h | h | h | h
      · exact hua h
      · subst u; exact no_c_ext v hvb hvd huv
      · exact hvb h
      · exact hvd h
    subst v
    by_cases huc : u = c
    · subst u; exact no_cb huv
    · exact no_b u hua huc huv
  · refine ⟨{a, c}, Finset.card_le_two, ?_⟩
    intro u v huv
    by_cases hua : u = a
    · subst u; exact Or.inl (by simp)
    by_cases huc : u = c
    · subst u; exact Or.inl (by simp)
    exfalso
    rcases edge_touches h3 hac hbd hab hcd huv with h | h | h | h
    · exact hua h
    · exact huc h
    · subst v; exact no_b u hua huc huv
    · subst v; exact hd ⟨u, hua, huc, huv⟩

lemma cover_of_two_edges {α : Type} [DecidableEq α] {R : α → α → Prop}
    (h3 : NoThree R) {a c b d : α}
    (hac : a ≠ c) (hbd : b ≠ d) (hab : R a b) (hcd : R c d) :
    ∃ K : Finset α, K.card ≤ 2 ∧ ∀ u v, R u v → u ∈ K ∨ v ∈ K := by
  classical
  by_cases ha : ∃ x, x ≠ b ∧ x ≠ d ∧ R a x
  · obtain ⟨x, hxb, hxd, hax⟩ := ha
    exact cover_with_external h3 hac hbd hab hcd hax hxb hxd
  by_cases hc : ∃ x, x ≠ b ∧ x ≠ d ∧ R c x
  · obtain ⟨x, hxb, hxd, hcx⟩ := hc
    exact cover_with_external h3 hac.symm hbd.symm hcd hab hcx hxd hxb
  refine ⟨{b, d}, Finset.card_le_two, ?_⟩
  intro u v huv
  by_cases hvb : v = b
  · subst v; exact Or.inr (by simp)
  by_cases hvd : v = d
  · subst v; exact Or.inr (by simp)
  exfalso
  rcases edge_touches h3 hac hbd hab hcd huv with h | h | h | h
  · subst u; exact ha ⟨v, hvb, hvd, huv⟩
  · subst u; exact hc ⟨v, hvb, hvd, huv⟩
  · exact hvb h
  · exact hvd h

lemma cover_of_noThree {α : Type} [DecidableEq α] {R : α → α → Prop}
    (h3 : NoThree R) :
    ∃ K : Finset α, K.card ≤ 2 ∧ ∀ u v, R u v → u ∈ K ∨ v ∈ K := by
  classical
  by_cases he : ∃ a b, R a b
  · obtain ⟨a, b, hab⟩ := he
    by_cases hcover : ∀ u v, R u v → u = a ∨ v = b
    · refine ⟨{a, b}, Finset.card_le_two, ?_⟩
      intro u v huv
      rcases hcover u v huv with rfl | rfl <;> simp
    · push Not at hcover
      obtain ⟨c, d, hcd, hca, hdb⟩ := hcover
      exact cover_of_two_edges h3 hca.symm hdb.symm hab hcd
  · refine ⟨∅, by simp, ?_⟩
    intro u v huv
    exact False.elim (he ⟨u, v, huv⟩)

lemma triple_injective {α : Type} (a b c : α) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : Function.Injective ![a, b, c] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

lemma bipartite_relation_cover_of_no_matching_three {α : Type} [DecidableEq α]
    (P : α → α → Prop) (hsymm : ∀ u v, P u v → P v u)
    (s : α → Bool) (hcol : ∀ u v, P u v → s u ≠ s v)
    (h3 : ¬ ∃ left right : Fin 3 → α,
      Function.Injective left ∧ Function.Injective right ∧
      (∀ i, s (left i) = false) ∧ (∀ i, s (right i) = true) ∧
      ∀ i, P (left i) (right i)) :
    ∃ K : Finset α, K.card ≤ 2 ∧ ∀ u v, P u v → u ∈ K ∨ v ∈ K := by
  classical
  let R : α → α → Prop := fun u v => P u v ∧ s u = false ∧ s v = true
  have hR3 : NoThree R := by
    intro a c e b d f hac hae hce hbd hbf hdf hab hcd hef
    apply h3
    refine ⟨![a, c, e], ![b, d, f], triple_injective _ _ _ hac hae hce,
      triple_injective _ _ _ hbd hbf hdf, ?_, ?_, ?_⟩
    · intro i; fin_cases i <;> simp_all [R]
    · intro i; fin_cases i <;> simp_all [R]
    · intro i; fin_cases i <;> simp_all [R]
  obtain ⟨K, hcard, hcov⟩ := cover_of_noThree hR3
  refine ⟨K, hcard, ?_⟩
  intro u v huv
  have hneq := hcol u v huv
  cases hu : s u <;> cases hv : s v
  · exact False.elim (hneq (hu.trans hv.symm))
  · exact hcov u v ⟨huv, hu, hv⟩
  · exact (hcov v u ⟨hsymm u v huv, hv, hu⟩).symm
  · exact False.elim (hneq (hu.trans hv.symm))

lemma bipartite_cover_of_no_matching_three {n : ℕ} (G : SimpleGraph (Fin n))
    (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (h3 : ¬ ∃ left right : Fin 3 → Fin n,
      Function.Injective left ∧ Function.Injective right ∧
      (∀ i, s (left i) = false) ∧ (∀ i, s (right i) = true) ∧
      ∀ i, G.Adj (left i) (right i)) :
    ∃ K : Finset (Fin n), K.card ≤ 2 ∧ ∀ u v, G.Adj u v → u ∈ K ∨ v ∈ K :=
  bipartite_relation_cover_of_no_matching_three G.Adj (fun _ _ h => h.symm) s hcol h3

end TwoCover

namespace FourClausePullback

open PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover

lemma two_center_cover
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : NoFourCycle G) (A : Fin 4 → Finset (Fin n))
    (hclean : ∀ x : Fin n → Bool,
      (∀ k, ∃ u ∈ A k, x u = true) → graphFun G ∅ x = true) :
    ∃ K : Finset (Fin n), K.card ≤ 2 ∧
      ∀ u v, G.Adj u v → (∀ k, u ∈ A k ∨ v ∈ A k) → u ∈ K ∨ v ∈ K := by
  classical
  let H : SimpleGraph (Fin n) :=
    { Adj := fun u v => G.Adj u v ∧ ∀ k, u ∈ A k ∨ v ∈ A k
      symm := by
        constructor
        intro u v h
        exact ⟨h.1.symm, fun k => (h.2 k).symm⟩
      loopless := by
        constructor
        intro u h
        simpa using h.1 }
  have hHcol : ∀ u v, H.Adj u v → s u ≠ s v := fun u v h => hcol u v h.1
  have hH3 : ¬ ∃ left right : Fin 3 → Fin n,
      Function.Injective left ∧ Function.Injective right ∧
      (∀ i, s (left i) = false) ∧ (∀ i, s (right i) = true) ∧
      ∀ i, H.Adj (left i) (right i) := by
    rintro ⟨left, right, hl, hr, hlc, hrc, he⟩
    exact no_three_disjoint_accepted_edges G s hcol h4 A hclean
      ⟨left, right, hl, hr, hlc, hrc, fun i => (he i).1, fun i => (he i).2⟩
  obtain ⟨K, hKcard, hKcover⟩ := TwoCover.bipartite_cover_of_no_matching_three H s hHcol hH3
  exact ⟨K, hKcard, fun u v he ha => hKcover u v ⟨he, ha⟩⟩

lemma clean_two_products_two_center_cover
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : NoFourCycle G) (A B C D : Finset (Fin n))
    (hclean : ∀ x : Fin n → Bool,
      (∃ a ∈ A, x a = true) → (∃ b ∈ B, x b = true) →
      (∃ c ∈ C, x c = true) → (∃ d ∈ D, x d = true) → graphFun G ∅ x = true) :
    ∃ K : Finset (Fin n), K.card ≤ 2 ∧
      ∀ u v, G.Adj u v → (u ∈ A ∨ v ∈ A) → (u ∈ B ∨ v ∈ B) →
        (u ∈ C ∨ v ∈ C) → (u ∈ D ∨ v ∈ D) → u ∈ K ∨ v ∈ K := by
  obtain ⟨K, hKcard, hKcover⟩ := two_center_cover G s hcol h4 ![A, B, C, D] (by
    intro x hx
    exact hclean x (hx 0) (hx 1) (hx 2) (hx 3))
  refine ⟨K, hKcard, ?_⟩
  intro u v he hA hB hC hD
  apply hKcover u v he
  intro k
  fin_cases k <;> simp_all

end FourClausePullback


namespace Cost

open PEqualNP.TopForm






end Cost


namespace MixedGeometry

open PEqualNP.MetaComplexity.NestedCover

def inputOf {n : ℕ} (S : Finset (Fin n)) : Fin n → Bool := fun v => decide (v ∈ S)

lemma independent_three {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (a b d : Fin n) (hsame : s b = s d) (hab : ¬ G.Adj a b) (had : ¬ G.Adj a d) :
    graphFun G ∅ (inputOf {a, b, d}) = false := by
  have hnone : ¬ ∃ u v, G.Adj u v ∧ inputOf {a, b, d} u = true ∧
      inputOf {a, b, d} v = true := by
    rintro ⟨u, v, huv, hu, hv⟩
    simp only [inputOf, decide_eq_true_eq, Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
    · exact hcol _ _ huv rfl
    · exact hab huv
    · exact had huv
    · exact hab huv.symm
    · exact hcol _ _ huv rfl
    · exact hcol _ _ huv hsame
    · exact had huv.symm
    · exact hcol _ _ huv hsame.symm
    · exact hcol _ _ huv rfl
  simpa [graphFun] using hnone

lemma clean_four_factor_missing_side
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (A B C D : Finset (Fin n))
    (hclean : ∀ x : Fin n → Bool,
      (∃ a ∈ A, x a = true) → (∃ b ∈ B, x b = true) →
      (∃ c ∈ C, x c = true) → (∃ d ∈ D, x d = true) → graphFun G ∅ x = true)
    (u b : Fin n) (huA : u ∈ A) (huC : u ∈ C) (hbB : b ∈ B)
    (hub : ¬ G.Adj u b) :
    u ∉ D ∧ b ∉ D ∧ ∀ d ∈ D, s d = s b → G.Adj u d := by
  have pairFalse : graphFun G ∅ (inputOf {u, b, b}) = false :=
    independent_three G s hcol u b b rfl hub hub
  have hu_true : inputOf {u, b, b} u = true := by simp [inputOf]
  have hb_true : inputOf {u, b, b} b = true := by simp [inputOf]
  have huD : u ∉ D := by
    intro huD
    have hh := hclean (inputOf {u, b, b}) ⟨u, huA, hu_true⟩ ⟨b, hbB, hb_true⟩
      ⟨u, huC, hu_true⟩ ⟨u, huD, hu_true⟩
    rw [pairFalse] at hh
    cases hh
  have hbD : b ∉ D := by
    intro hbD
    have hh := hclean (inputOf {u, b, b}) ⟨u, huA, hu_true⟩ ⟨b, hbB, hb_true⟩
      ⟨u, huC, hu_true⟩ ⟨b, hbD, hb_true⟩
    rw [pairFalse] at hh
    cases hh
  refine ⟨huD, hbD, ?_⟩
  intro d hd hsame
  by_contra hno
  have hfalse := independent_three G s hcol u b d hsame.symm hub hno
  have htrue := hclean (inputOf {u, b, d})
    ⟨u, huA, by simp [inputOf]⟩ ⟨b, hbB, by simp [inputOf]⟩
    ⟨u, huC, by simp [inputOf]⟩ ⟨d, hd, by simp [inputOf]⟩
  rw [hfalse] at htrue
  cases htrue

lemma clean_four_factor_star_choice
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (A B C D : Finset (Fin n))
    (hclean : ∀ x : Fin n → Bool,
      (∃ a ∈ A, x a = true) → (∃ b ∈ B, x b = true) →
      (∃ c ∈ C, x c = true) → (∃ d ∈ D, x d = true) → graphFun G ∅ x = true)
    (u : Fin n) (huA : u ∈ A) (huC : u ∈ C) (color : Bool)
    (hB : ∀ b ∈ B, s b = color) :
    (∀ b ∈ B, G.Adj u b) ∨
      (u ∉ D ∧ ∀ d ∈ D, s d = color → G.Adj u d) := by
  classical
  by_cases h : ∀ b ∈ B, G.Adj u b
  · exact Or.inl h
  · push Not at h
    obtain ⟨b, hb, hub⟩ := h
    obtain ⟨huD, _, hD⟩ := clean_four_factor_missing_side G s hcol A B C D hclean u b huA huC hb hub
    exact Or.inr ⟨huD, fun d hd hc => hD d hd (hc.trans (hB b hb).symm)⟩

end MixedGeometry

namespace Mixed

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq_foldl, foldl_stepWire_length, List.length_ofFn]

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]


def W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma W_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then W n C x i else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gj := by rw [gateAt_eq C k hk]; exact hgj
  rw [hga]
  let w0 := pre.foldl stepWire (List.ofFn x)
  have hw0_len : w0.length = n + k := by
    simp [w0, foldl_stepWire_length, hpre_len]
  have hCj : W n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [foldl_stepWire_getD_lt post (stepWire w0 gj) (n + k) (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < n + k
  · simp only [hi, ↓reduceIte]
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append]
    exact (foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact getD_ge_length w0 i (by omega)

lemma W_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    W n C x u = x ⟨u, hu⟩ := by
  simp only [W]
  rw [wires_eq_foldl, foldl_stepWire_getD_lt C.gates (List.ofFn x) u (by simpa using hu)]
  simp [List.getD_eq_getElem?_getD, hu]

open PEqualNP.CleanedNonEdge in
lemma orFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

open PEqualNP.CleanedNonEdge in
lemma orStep_mem_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) (x : ℕ) :
    x ∈ (orStep n cs g).getD cs.length [] ↔ x = cs.length ∨ (g.op = GateOp.or ∧
      ∃ w ∈ g.inputs, n ≤ w ∧ w < n + cs.length ∧ x ∈ cs.getD (w - n) []) := by
  by_cases h : g.op = GateOp.or
  · simp only [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl, h,
      ↓reduceIte, true_and, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some,
      List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro (h1 | ⟨w, ⟨hw, hn, hlt⟩, hx⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, hw, hn, hlt, hx⟩
    · rintro (h1 | ⟨w, hw, hn, hlt, hx⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, ⟨hw, hn, hlt⟩, hx⟩
  · simp [orStep, List.getD_eq_getElem?_getD, h]

open PEqualNP.CleanedNonEdge in
lemma orStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (orStep n cs g).getD m [] = cs.getD m [] := by
  simp [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

open PEqualNP.CleanedNonEdge in
lemma orFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (orStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (orStep n cs g) (by simp [orStep]; omega)]
    exact orStep_getD_lt n cs g k hk

open PEqualNP.CleanedNonEdge in
lemma orSets_mem_iff (n : ℕ) (C : Circuit) (k x : ℕ) (hk : k < C.gates.length) :
    x ∈ (orSets n C).getD k [] ↔ x = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧ x ∈ (orSets n C).getD (w - n) []) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : orSets n C = post.foldl (orStep n) (orStep n (pre.foldl (orStep n) []) gk) := by
    simp only [orSets]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (orStep n) []).length = k := by
    rw [orFold_length]; simp [hpre_len]
  have hl1 : (orStep n (pre.foldl (orStep n) []) gk).length = k + 1 := by
    simp [orStep, hl0]
  have h1 : (orSets n C).getD k [] = (orStep n (pre.foldl (orStep n) []) gk).getD k [] := by
    rw [hc, orFold_getD_lt n post _ k (by omega)]
  have h2 : ∀ m, m < k → (orSets n C).getD m [] = (pre.foldl (orStep n) []).getD m [] := by
    intro m hm
    rw [hc, orFold_getD_lt n post _ m (by omega)]
    exact orStep_getD_lt n _ gk m (by omega)
  have h3 := orStep_mem_last n (pre.foldl (orStep n) []) gk x
  rw [hl0] at h3
  rw [h1, h3]
  constructor
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [h2 (w - n) (by omega)]; exact hx⟩
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [← h2 (w - n) (by omega)]; exact hx⟩


lemma W_or (n : ℕ) (C : Circuit) (x : Fin n → Bool) (r : ℕ) (hr : r < C.gates.length)
    (hop : (gateAt C r).op = GateOp.or) (i : ℕ) (hi : i ∈ (gateAt C r).inputs)
    (hlt : i < n + r) (hv : W n C x i = true) : W n C x (n + r) = true := by
  rw [W_gate n C x r hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  exact ⟨i, hi, by rw [ite_eq_left hlt]; exact hv⟩

lemma W_and (n : ℕ) (C : Circuit) (x : Fin n → Bool) (r : ℕ) (hr : r < C.gates.length)
    (hop : (gateAt C r).op = GateOp.and)
    (h : ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ W n C x i = true) :
    W n C x (n + r) = true := by
  rw [W_gate n C x r hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  intro i hi
  rw [ite_eq_left (h i hi).1]; exact (h i hi).2

open PEqualNP.CleanedNonEdge in
lemma reach_val (n : ℕ) (C : Circuit) (x : Fin n → Bool) (g : ℕ)
    (hv : W n C x (n + g) = true) :
    ∀ k, k < C.gates.length → g ∈ (orSets n C).getD k [] → W n C x (n + k) = true := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk hmem
    rcases (orSets_mem_iff n C k g hk).mp hmem with h | ⟨hop, w, hw, hn, hlt, hx⟩
    · rw [← h]; exact hv
    · have h3 := ih (w - n) (by omega) (by omega) hx
      have e : n + (w - n) = w := by omega
      rw [e] at h3
      exact W_or n C x k hk hop w hw hlt h3

open PEqualNP.CleanedNonEdge in
lemma reach_up (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w g : ℕ)
    (h : OrReaches n C w g) (hv : W n C x (n + g) = true) : W n C x w = true := by
  obtain ⟨hn, hmem⟩ := h
  by_cases hk : w - n < C.gates.length
  · have h3 := reach_val n C x g hv (w - n) hk hmem
    have e : n + (w - n) = w := by omega
    rw [e] at h3
    exact h3
  · exfalso
    have hlen : (orSets n C).length = C.gates.length := by
      unfold orSets; rw [orFold_length]; simp
    have hge : (orSets n C).length ≤ w - n := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge] at hmem
    simp at hmem

lemma mem_filter_gen {α : Type} (p : α → Prop) (d : DecidablePred p) (s : Finset α) (a : α)
    (h : a ∈ @Finset.filter α p d s) : p a :=
  ((@Finset.mem_filter α p d s a).mp h).2

lemma side_val (n : ℕ) (C : Circuit) (x : Fin n → Bool) (j : ℕ) (b : Fin 2) (i : Fin n)
    (hi : i ∈ PEqualNP.TopForm.side (n := n) C j b) (hx : x i = true) :
    W n C x (PEqualNP.TopForm.opnd C j b) = true := by
  unfold PEqualNP.TopForm.side PEqualNP.TopForm.orIn at hi
  have hi2 := mem_filter_gen _ _ _ _ hi
  rcases hi2 with h | ⟨k, hk, hreach, hop, hin⟩
  · rw [← h, W_input n C x i.val i.isLt]; exact hx
  · have hk1 : W n C x (n + k) = true := by
      apply W_or n C x k hk hop i.val hin (by have := i.isLt; omega)
      rw [W_input n C x i.val i.isLt]; exact hx
    exact reach_up n C x _ k hreach hk1

open PEqualNP.EdgeOwnership in
lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

open PEqualNP.EdgeOwnership in
lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

open PEqualNP.EdgeOwnership in
lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3


lemma gateAt_mem' (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq C j hj]; exact List.getElem_mem hj

open PEqualNP.EdgeOwnership in
lemma inCone_lt (n : ℕ) (C : Circuit) : ∀ j i, InCone n C i j → i < j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro i h
    obtain ⟨_, k, hk, _, h3⟩ := (inCone_iff n C i j).mp h
    rcases h3 with h3 | h3
    · omega
    · have := ih k hk i h3; omega

open PEqualNP.CleanedNonEdge in
lemma orReach_trans (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (w : ℕ) (hw : w ∈ (gateAt C k).inputs)
    (hlt : w < n + k) (g : ℕ) (h : OrReaches n C w g) : OrReaches n C (n + k) g := by
  obtain ⟨hn, hmem⟩ := h
  refine ⟨by omega, ?_⟩
  have e : n + k - n = k := by omega
  rw [e]
  exact (orSets_mem_iff n C k g hk).mpr (Or.inr ⟨hop, w, hw, hn, hlt, hmem⟩)

open PEqualNP.CleanedNonEdge in
lemma orReach_self (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    OrReaches n C (n + k) k := by
  refine ⟨by omega, ?_⟩
  have e : n + k - n = k := by omega
  rw [e]
  exact (orSets_mem_iff n C k k hk).mpr (Or.inl rfl)

lemma orIn_mem (n : ℕ) (C : Circuit) (w : ℕ) (i : Fin n) :
    i ∈ PEqualNP.TopForm.orIn n C w ↔ ((i : ℕ) = w ∨ ∃ k < C.gates.length,
      PEqualNP.CleanedNonEdge.OrReaches n C w k ∧ (gateAt C k).op = GateOp.or ∧
        (i : ℕ) ∈ (gateAt C k).inputs) := by
  unfold PEqualNP.TopForm.orIn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

open PEqualNP.CleanedNonEdge in
lemma down (n : ℕ) (C : Circuit) (x : Fin n → Bool)
    (hAO : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) :
    ∀ w, W n C x w = true → (∃ i : Fin n, i ∈ PEqualNP.TopForm.orIn n C w ∧ x i = true) ∨
      ∃ k, k < C.gates.length ∧ OrReaches n C w k ∧ (gateAt C k).op = GateOp.and ∧
        W n C x (n + k) = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hwn : w < n
    · left
      refine ⟨⟨w, hwn⟩, (orIn_mem n C w _).mpr (Or.inl rfl), ?_⟩
      rw [← W_input n C x w hwn]; exact hv
    · by_cases hk : w - n < C.gates.length
      · have hw : w = n + (w - n) := by omega
        set k := w - n with hkdef
        rcases hAO k hk with hop | hop
        · right
          refine ⟨k, hk, ?_, hop, ?_⟩
          · rw [hw]; exact orReach_self n C k hk
          · rw [← hw]; exact hv
        · have hv2 := hv
          rw [hw, W_gate n C x k hk, hop] at hv2
          simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq] at hv2
          obtain ⟨i, hi, hiv⟩ := hv2
          split_ifs at hiv with hlt
          rcases ih i (by omega) hiv with ⟨j, hj, hxj⟩ | ⟨k', hk', hr, hop', hv'⟩
          · left
            refine ⟨j, ?_, hxj⟩
            rw [orIn_mem] at hj ⊢
            right
            rcases hj with hj | ⟨k'', hk'', hr, hop'', hin⟩
            · refine ⟨k, hk, ?_, hop, ?_⟩
              · rw [hw]; exact orReach_self n C k hk
              · rw [hj]; exact hi
            · refine ⟨k'', hk'', ?_, hop'', hin⟩
              rw [hw]; exact orReach_trans n C k hk hop i hi hlt k'' hr
          · right
            refine ⟨k', hk', ?_, hop', hv'⟩
            rw [hw]; exact orReach_trans n C k hk hop i hi hlt k' hr
      · exfalso
        have hl := wires_length n C x
        have : W n C x w = false := getD_ge_length _ w (by omega)
        rw [this] at hv; exact Bool.false_ne_true hv

open PEqualNP.EdgeOwnership in
lemma orSets_cone (n : ℕ) (C : Circuit) : ∀ m, m < C.gates.length → ∀ k,
    k ∈ (PEqualNP.CleanedNonEdge.orSets n C).getD m [] → k = m ∨ InCone n C k m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm k hk
    rcases (orSets_mem_iff n C m k hm).mp hk with h | ⟨_, w, hw, hn, hlt, hx⟩
    · exact Or.inl h
    · right
      have h2 := ih (w - n) (by omega) (by omega) k hx
      have e : n + (w - n) = w := by omega
      exact (inCone_iff n C k m).mpr ⟨hm, w - n, by omega, by rw [e]; exact hw, h2⟩

open PEqualNP.EdgeOwnership in
lemma reach_cone (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (o : ℕ)
    (ho : o ∈ (gateAt C j).inputs) (hlt : o < n + j) (k : ℕ)
    (h : PEqualNP.CleanedNonEdge.OrReaches n C o k) : InCone n C k j := by
  obtain ⟨hn, hmem⟩ := h
  have h2 := orSets_cone n C (o - n) (by omega) k hmem
  have e : n + (o - n) = o := by omega
  exact (inCone_iff n C k j).mpr ⟨hj, o - n, by omega, by rw [e]; exact ho, h2⟩


open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

def monoInput {n : ℕ} (s : Fin n → Bool) (c : Bool) : Fin n → Bool :=
  fun u => decide (s u = c)

lemma monoInput_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v) (c : Bool) :
    graphFun G ∅ (monoInput s c) = false := by
  have hn : ¬ ∃ u v, G.Adj u v ∧ monoInput s c u = true ∧ monoInput s c v = true := by
    rintro ⟨u, v, huv, hu, hv⟩
    have hu' : s u = c := by simpa [monoInput] using hu
    have hv' : s v = c := by simpa [monoInput] using hv
    exact hcol u v huv (hu'.trans hv'.symm)
  simp [graphFun, hn]

lemma opnd_mem {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
    opnd C a b ∈ (gateAt C a).inputs := by
  have hlen := hAO.2.2 _ (gateAt_mem' C a ha)
  unfold opnd
  have hb : b.val < (gateAt C a).inputs.length := by omega
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb, Option.getD_some]
  exact List.getElem_mem hb

lemma opnd_lt {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
    opnd C a b < n + a := hAO.2.1 a ha _ (opnd_mem hAO ha b)

lemma mem_inputs_iff_opnd {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {a : ℕ} (ha : a < C.gates.length) (w : ℕ) :
    w ∈ (gateAt C a).inputs ↔ ∃ b : Fin 2, opnd C a b = w := by
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem' C a ha))
  constructor
  · intro hw
    rw [hin] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact ⟨0, by simp [opnd, hin]⟩
    · exact ⟨1, by simp [opnd, hin]⟩
  · rintro ⟨b, rfl⟩
    exact opnd_mem hAO ha b

lemma and_two {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {a : ℕ} (ha : a < C.gates.length) (hand : (gateAt C a).op = GateOp.and)
    (b : Fin 2) (x : Fin n → Bool)
    (hb : W n C x (opnd C a b) = true)
    (hc : W n C x (opnd C a (1 - b)) = true) :
    gateVal n C a x = true := by
  apply W_and n C x a ha hand
  intro w hw
  obtain ⟨d, rfl⟩ := (mem_inputs_iff_opnd hAO ha w).mp hw
  refine ⟨opnd_lt hAO ha d, ?_⟩
  have hd : d = b ∨ d = 1 - b := by fin_cases b <;> fin_cases d <;> decide
  rcases hd with rfl | rfl
  · exact hb
  · exact hc

lemma wire_all_true {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) :
    ∀ w, w < n + C.gates.length → W n C (fun _ => true) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hn : w < n
    · rw [W_input n C _ w hn]
    · have hk : w - n < C.gates.length := by omega
      have heq : w = n + (w - n) := by omega
      rcases hAO.1 _ (gateAt_mem' C (w - n) hk) with hand | hor
      · rw [heq]
        apply W_and n C _ _ hk hand
        intro i hi
        have hi' := hAO.2.1 (w - n) hk i hi
        exact ⟨hi', ih i (by omega) (by omega)⟩
      · rw [heq]
        apply W_or n C _ _ hk hor (opnd C (w - n) 0)
          (opnd_mem hAO hk 0) (opnd_lt hAO hk 0)
        exact ih _ (by have := opnd_lt hAO hk 0; omega)
          (by have := opnd_lt hAO hk 0; omega)

lemma and_ancestor_junk {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hTop : TopForm G C) {a k : ℕ}
    (ha : a < C.gates.length) (hand : (gateAt C a).op = GateOp.and)
    (hk : k < C.gates.length) (hkand : (gateAt C k).op = GateOp.and)
    (hc : InCone n C k a) : k ∈ junk G C := by
  have hnb : ¬ BelowF G C k := fun hb => hTop k hk a ha hkand hb hand hc
  have hd : IsDirtyAnd n G C k := by
    unfold IsDirtyAnd IsDirty
    refine ⟨hkand, hk, ?_⟩
    by_contra he
    apply hnb
    intro x hx
    by_contra hf
    exact he ⟨x, hx, Bool.eq_false_iff.mpr hf⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hd⟩

lemma opposite_of_mixed_junk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (hAO : IsAO2 n C) (hTop : TopForm G C) (g h : ℕ) (hJ : junk G C = {g, h})
    (hmix : ∀ c : Bool, gateVal n C h (monoInput s c) = true)
    (t : ℕ) (ht : t < C.gates.length) (htand : (gateAt C t).op = GateOp.and)
    (htbelow : BelowF G C t) (b : Fin 2) (hreach : OrReaches n C (opnd C t b) h) :
    side (n := n) C t (1 - b) = ∅ ∧
      ¬ OrReaches n C (opnd C t (1 - b)) h ∧
      OrReaches n C (opnd C t (1 - b)) g ∧
      ∀ x : Fin n → Bool, wireVal n C (opnd C t (1 - b)) x = gateVal n C g x := by
  have hempty : side (n := n) C t (1 - b) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro u hu
    have hh : W n C (monoInput s (s u)) (opnd C t b) = true :=
      reach_up n C _ _ h hreach (hmix (s u))
    have ho : W n C (monoInput s (s u)) (opnd C t (1 - b)) = true :=
      side_val n C _ t (1 - b) u hu (by simp [monoInput])
    have htf := htbelow _ (and_two hAO ht htand b _ hh ho)
    rw [monoInput_false G s hcol] at htf
    cases htf
  have hnot : ¬ OrReaches n C (opnd C t (1 - b)) h := by
    intro hr
    have hh : W n C (monoInput s false) (opnd C t b) = true :=
      reach_up n C _ _ h hreach (hmix false)
    have ho : W n C (monoInput s false) (opnd C t (1 - b)) = true :=
      reach_up n C _ _ h hr (hmix false)
    have htf := htbelow _ (and_two hAO ht htand b _ hh ho)
    rw [monoInput_false G s hcol] at htf
    cases htf
  have hdown (x : Fin n → Bool) (hv : W n C x (opnd C t (1 - b)) = true) :
      OrReaches n C (opnd C t (1 - b)) g ∧ gateVal n C g x = true := by
    rcases down n C x (fun k hk => hAO.1 _ (gateAt_mem' C k hk)) _ hv with
      ⟨u, hu, _⟩ | ⟨k, hk, hr, hkand, hkv⟩
    · change u ∈ side (n := n) C t (1 - b) at hu
      rw [hempty] at hu
      exact False.elim (Finset.notMem_empty _ hu)
    · have hcone := reach_cone n C t ht _ (opnd_mem hAO ht (1 - b))
        (opnd_lt hAO ht (1 - b)) k hr
      have hkJ := and_ancestor_junk hTop ht htand hk hkand hcone
      have hkg : k = g ∨ k = h := by simpa [hJ] using hkJ
      rcases hkg with hkg | hkg <;> subst k
      · exact ⟨hr, hkv⟩
      · exact False.elim (hnot hr)
  have hr := (hdown (fun _ => true) (wire_all_true hAO _
    (by have := opnd_lt hAO ht (1 - b); omega))).1
  refine ⟨hempty, hnot, hr, ?_⟩
  intro x
  apply Bool.eq_iff_iff.mpr
  constructor
  · exact fun hv => (hdown x hv).2
  · exact reach_up n C x _ g hr

lemma W_or_patch {n : ℕ} {C : Circuit} {h : ℕ} (hhand : (gateAt C h).op = GateOp.and)
    (r : Gate) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hkor : (gateAt C k).op = GateOp.or) (w : ℕ) (hw : w ∈ (gateAt C k).inputs)
    (hwlt : w < n + k) (hv : W n (patch C h r) x w = true) :
    W n (patch C h r) x (n + k) = true := by
  have hne : h ≠ k := by rintro rfl; rw [hhand] at hkor; cases hkor
  apply W_or n (patch C h r) x k (by simpa [patch] using hk) _ w _ hwlt hv
  · rw [gateAt_patch_ne C h k r hne]; exact hkor
  · rw [gateAt_patch_ne C h k r hne]; exact hw

lemma W_and_patch {n : ℕ} {C : Circuit} {h : ℕ} (r : Gate) (x : Fin n → Bool)
    (k : ℕ) (hk : k < C.gates.length) (hkop : (gateAt C k).op = GateOp.and)
    (hne : h ≠ k)
    (hall : ∀ w ∈ (gateAt C k).inputs, w < n + k ∧ W n (patch C h r) x w = true) :
    W n (patch C h r) x (n + k) = true := by
  apply W_and n (patch C h r) x k (by simpa [patch] using hk)
  · rw [gateAt_patch_ne C h k r hne]; exact hkop
  · rw [gateAt_patch_ne C h k r hne]; exact hall

lemma reach_val_patch {n : ℕ} {C : Circuit} {h : ℕ}
    (hhand : (gateAt C h).op = GateOp.and) (r : Gate) (x : Fin n → Bool) (g : ℕ)
    (hv : W n (patch C h r) x (n + g) = true) :
    ∀ k, k < C.gates.length → g ∈ (orSets n C).getD k [] →
      W n (patch C h r) x (n + k) = true := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk hmem
    rcases (orSets_mem_iff n C k g hk).mp hmem with he | ⟨hop, w, hw, hn, hlt, hx⟩
    · rw [← he]; exact hv
    · have h3 := ih (w - n) (by omega) (by omega) hx
      have e : n + (w - n) = w := by omega
      rw [e] at h3
      exact W_or_patch hhand r x k hk hop w hw hlt h3

lemma reach_up_patch {n : ℕ} {C : Circuit} {h : ℕ}
    (hhand : (gateAt C h).op = GateOp.and) (r : Gate) (x : Fin n → Bool) (w g : ℕ)
    (hr : OrReaches n C w g) (hv : W n (patch C h r) x (n + g) = true) :
    W n (patch C h r) x w = true := by
  obtain ⟨hn, hmem⟩ := hr
  by_cases hk : w - n < C.gates.length
  · have h3 := reach_val_patch hhand r x g hv (w - n) hk hmem
    have e : n + (w - n) = w := by omega
    rw [e] at h3
    exact h3
  · exfalso
    have hlen : (orSets n C).length = C.gates.length := by
      unfold orSets; rw [orFold_length]; simp
    have hge : (orSets n C).length ≤ w - n := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge] at hmem
    simp at hmem

lemma orIn_val_patch {n : ℕ} {C : Circuit} {h : ℕ}
    (hhand : (gateAt C h).op = GateOp.and) (r : Gate) (x : Fin n → Bool)
    (w : ℕ) (u : Fin n) (hu : u ∈ orIn n C w) (hxu : x u = true) :
    W n (patch C h r) x w = true := by
  rcases (orIn_mem n C w u).mp hu with hu | ⟨k, hk, hr, hkor, huk⟩
  · rw [← hu, W_input n (patch C h r) x u.val u.isLt]
    exact hxu
  · apply reach_up_patch hhand r x w k hr
    apply W_or_patch hhand r x k hk hkor u.val huk (by have := u.isLt; omega)
    rw [W_input n (patch C h r) x u.val u.isLt]
    exact hxu

lemma down_patch {n : ℕ} {C : Circuit} {h : ℕ}
    (hhand : (gateAt C h).op = GateOp.and) (r : Gate) (x : Fin n → Bool)
    (hAO : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) :
    ∀ w, W n (patch C h r) x w = true →
      (∃ i : Fin n, i ∈ orIn n C w ∧ x i = true) ∨
      ∃ k, k < C.gates.length ∧ OrReaches n C w k ∧ (gateAt C k).op = GateOp.and ∧
        W n (patch C h r) x (n + k) = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hwn : w < n
    · left
      refine ⟨⟨w, hwn⟩, (orIn_mem n C w _).mpr (Or.inl rfl), ?_⟩
      rw [← W_input n (patch C h r) x w hwn]; exact hv
    · by_cases hk : w - n < C.gates.length
      · have hw : w = n + (w - n) := by omega
        set k := w - n with hkdef
        rcases hAO k hk with hop | hop
        · right
          refine ⟨k, hk, ?_, hop, ?_⟩
          · rw [hw]; exact orReach_self n C k hk
          · rw [← hw]; exact hv
        · have hv2 := hv
          have hne : h ≠ k := by rintro rfl; rw [hhand] at hop; cases hop
          rw [hw, W_gate n (patch C h r) x k (by simpa [patch] using hk),
            gateAt_patch_ne C h k r hne, hop] at hv2
          simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq] at hv2
          obtain ⟨i, hi, hiv⟩ := hv2
          split_ifs at hiv with hlt
          rcases ih i (by omega) hiv with ⟨j, hj, hxj⟩ | ⟨k', hk', hr, hop', hv'⟩
          · left
            refine ⟨j, ?_, hxj⟩
            rw [orIn_mem] at hj ⊢
            right
            rcases hj with hj | ⟨k'', hk'', hr, hop'', hin⟩
            · refine ⟨k, hk, ?_, hop, ?_⟩
              · rw [hw]; exact orReach_self n C k hk
              · rw [hj]; exact hi
            · refine ⟨k'', hk'', ?_, hop'', hin⟩
              rw [hw]; exact orReach_trans n C k hk hop i hi hlt k'' hr
          · right
            refine ⟨k', hk', ?_, hop', hv'⟩
            rw [hw]; exact orReach_trans n C k hk hop i hi hlt k' hr
      · exfalso
        have hl : ((patch C h r).wires (List.ofFn x)).length = n + C.gates.length := by
          rw [wires_length]
          simp [patch]
        have : W n (patch C h r) x w = false := getD_ge_length _ w (by omega)
        rw [this] at hv; exact Bool.false_ne_true hv

lemma and_true_operands {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {t : ℕ} (ht : t < C.gates.length) (hop : (gateAt C t).op = GateOp.and)
    (x : Fin n → Bool) (hv : gateVal n C t x = true) (b : Fin 2) :
    W n C x (opnd C t b) = true := by
  change W n C x (n + t) = true at hv
  rw [W_gate n C x t ht, hop] at hv
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq] at hv
  have hb := hv _ (opnd_mem hAO ht b)
  rwa [ite_eq_left (opnd_lt hAO ht b)] at hb

lemma and_true_operands_patch {n : ℕ} {C : Circuit} {h : ℕ} (r : Gate)
    (hAO : IsAO2 n C) {t : ℕ} (ht : t < C.gates.length)
    (hop : (gateAt C t).op = GateOp.and) (hne : h ≠ t)
    (x : Fin n → Bool) (hv : gateVal n (patch C h r) t x = true) (b : Fin 2) :
    W n (patch C h r) x (opnd C t b) = true := by
  change W n (patch C h r) x (n + t) = true at hv
  rw [W_gate n (patch C h r) x t (by simpa [patch] using ht),
    gateAt_patch_ne C h t r hne, hop] at hv
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq] at hv
  have hb := hv _ (opnd_mem hAO ht b)
  rwa [ite_eq_left (opnd_lt hAO ht b)] at hb

lemma and_junk_or_below {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} {k : ℕ} (hk : k < C.gates.length)
    (hand : (gateAt C k).op = GateOp.and) : k ∈ junk G C ∨ BelowF G C k := by
  by_cases hb : BelowF G C k
  · exact Or.inr hb
  · left
    apply mem_junk.mpr
    refine ⟨hk, hand, hk, ?_⟩
    by_contra he
    apply hb
    intro x hx
    by_contra hf
    exact he ⟨x, hx, Bool.eq_false_iff.mpr hf⟩

lemma orIn_val (n : ℕ) (C : Circuit) (x : Fin n → Bool)
    (w : ℕ) (u : Fin n) (hu : u ∈ orIn n C w) (hxu : x u = true) :
    W n C x w = true := by
  rcases (orIn_mem n C w u).mp hu with hu | ⟨k, hk, hr, hkor, huk⟩
  · rw [← hu, W_input n C x u.val u.isLt]
    exact hxu
  · apply reach_up n C x w k hr
    apply W_or n C x k hk hkor u.val huk (by have := u.isLt; omega)
    rw [W_input n C x u.val u.isLt]
    exact hxu

lemma mixed_ne_clean {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} {s : Fin n → Bool} (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    {h t : ℕ} (hmix : ∀ c : Bool, gateVal n C h (monoInput s c) = true)
    (htbelow : BelowF G C t) : h ≠ t := by
  rintro rfl
  have hf := htbelow (monoInput s false) (hmix false)
  rw [monoInput_false G s hcol] at hf
  cases hf

lemma output_not_reaches_mixed {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} {s : Fin n → Bool} (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (hF : circuitFun n C = graphFun G ∅) {h : ℕ}
    (hmix : ∀ c : Bool, gateVal n C h (monoInput s c) = true) :
    ¬ OrReaches n C C.output h := by
  intro hr
  have hv := reach_up n C (monoInput s false) C.output h hr (hmix false)
  change circuitFun n C (monoInput s false) = true at hv
  rw [hF, monoInput_false G s hcol] at hv
  cases hv

lemma patched_opposite_implies_other {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (hAO : IsAO2 n C) (hTop : TopForm G C) (g h : ℕ) (hJ : junk G C = {g, h})
    (hmix : ∀ c : Bool, gateVal n C h (monoInput s c) = true)
    (t : ℕ) (ht : t < C.gates.length) (htand : (gateAt C t).op = GateOp.and)
    (htbelow : BelowF G C t) (b : Fin 2) (hreach : OrReaches n C (opnd C t b) h)
    (r : Gate) (x : Fin n → Bool)
    (hv : wireVal n (patch C h r) (opnd C t (1 - b)) x = true) :
    gateVal n (patch C h r) g x = true := by
  have hhJ : h ∈ junk G C := by simp [hJ]
  have hhand := (mem_junk.mp hhJ).2.1
  obtain ⟨hempty, hnot, _, _⟩ :=
    opposite_of_mixed_junk G C s hcol hAO hTop g h hJ hmix t ht htand htbelow b hreach
  rcases down_patch hhand r x (fun k hk => hAO.1 _ (gateAt_mem' C k hk)) _ hv with
    ⟨u, hu, _⟩ | ⟨k, hk, hr, hkand, hkv⟩
  · change u ∈ side (n := n) C t (1 - b) at hu
    rw [hempty] at hu
    exact False.elim (Finset.notMem_empty _ hu)
  · have hcone := reach_cone n C t ht _ (opnd_mem hAO ht (1 - b))
      (opnd_lt hAO ht (1 - b)) k hr
    have hkJ := and_ancestor_junk hTop ht htand hk hkand hcone
    have hkg : k = g ∨ k = h := by simpa [hJ] using hkJ
    rcases hkg with hkg | hkg <;> subst k
    · exact hkv
    · exact False.elim (hnot hr)

lemma clean_and_false_under_guard {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (hAO : IsAO2 n C) (hTop : TopForm G C) (g h : ℕ) (hJ : junk G C = {g, h})
    (hmix : ∀ c : Bool, gateVal n C h (monoInput s c) = true)
    (r : Gate) (x : Fin n → Bool) (hxF : graphFun G ∅ x = false)
    (hxg : gateVal n (patch C h r) g x = false)
    (t : ℕ) (ht : t < C.gates.length) (htand : (gateAt C t).op = GateOp.and)
    (htbelow : BelowF G C t) : gateVal n (patch C h r) t x = false := by
  have hhJ : h ∈ junk G C := by simp [hJ]
  have hhand := (mem_junk.mp hhJ).2.1
  have hne := mixed_ne_clean hcol hmix htbelow
  cases hv : gateVal n (patch C h r) t x with
  | false => rfl
  | true =>
    have hraw (b : Fin 2) : W n C x (opnd C t b) = true := by
      have hb := and_true_operands_patch r hAO ht htand hne x hv b
      rcases down_patch hhand r x (fun k hk => hAO.1 _ (gateAt_mem' C k hk)) _ hb with
        ⟨u, hu, hxu⟩ | ⟨k, hk, hr, hkand, hkv⟩
      · exact orIn_val n C x _ u hu hxu
      · have hcone := reach_cone n C t ht _ (opnd_mem hAO ht b) (opnd_lt hAO ht b) k hr
        have hkJ := and_ancestor_junk hTop ht htand hk hkand hcone
        have hkg : k = g ∨ k = h := by simpa [hJ] using hkJ
        rcases hkg with hkg | hkg <;> subst k
        · change gateVal n (patch C h r) g x = true at hkv
          rw [hxg] at hkv
          cases hkv
        · have hother := and_true_operands_patch r hAO ht htand hne x hv (1 - b)
          have hg := patched_opposite_implies_other G C s hcol hAO hTop g h hJ hmix
            t ht htand htbelow b hr r x hother
          rw [hxg] at hg
          cases hg
    have hf := htbelow x (and_two hAO ht htand 0 x (hraw 0) (hraw (1 - 0)))
    rw [hxF] at hf
    cases hf

lemma output_false_under_guard {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (hAO : IsAO2 n C) (hTop : TopForm G C) (hF : circuitFun n C = graphFun G ∅)
    (g h : ℕ) (hJ : junk G C = {g, h})
    (hmix : ∀ c : Bool, gateVal n C h (monoInput s c) = true)
    (r : Gate) (x : Fin n → Bool) (hxF : graphFun G ∅ x = false)
    (hxg : gateVal n (patch C h r) g x = false) :
    circuitFun n (patch C h r) x = false := by
  have hhJ : h ∈ junk G C := by simp [hJ]
  have hhand := (mem_junk.mp hhJ).2.1
  cases hv : circuitFun n (patch C h r) x with
  | false => rfl
  | true =>
    rcases down_patch hhand r x (fun k hk => hAO.1 _ (gateAt_mem' C k hk)) C.output hv with
      ⟨u, hu, hxu⟩ | ⟨k, hk, hr, hkand, hkv⟩
    · have hvC := orIn_val n C x C.output u hu hxu
      change circuitFun n C x = true at hvC
      rw [hF, hxF] at hvC
      cases hvC
    · rcases and_junk_or_below (G := G) hk hkand with hkJ | hkbelow
      · have hkg : k = g ∨ k = h := by simpa [hJ] using hkJ
        rcases hkg with hkg | hkg <;> subst k
        · change gateVal n (patch C h r) g x = true at hkv
          rw [hxg] at hkv
          cases hkv
        · exact False.elim (output_not_reaches_mixed hcol hF hmix hr)
      · have hf := clean_and_false_under_guard G C s hcol hAO hTop g h hJ hmix
          r x hxF hxg k hk hkand hkbelow
        change gateVal n (patch C h r) k x = true at hkv
        rw [hf] at hkv
        cases hkv

lemma clean_and_survives_without_other {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (hAO : IsAO2 n C) (hTop : TopForm G C) (g h : ℕ) (hJ : junk G C = {g, h})
    (hmix : ∀ c : Bool, gateVal n C h (monoInput s c) = true)
    (r : Gate) (x : Fin n → Bool) (hxg : gateVal n C g x = false)
    (t : ℕ) (ht : t < C.gates.length) (htand : (gateAt C t).op = GateOp.and)
    (htbelow : BelowF G C t) (hv : gateVal n C t x = true) :
    gateVal n (patch C h r) t x = true := by
  have hhJ : h ∈ junk G C := by simp [hJ]
  have hhand := (mem_junk.mp hhJ).2.1
  have hne := mixed_ne_clean hcol hmix htbelow
  have hraw (b : Fin 2) : W n (patch C h r) x (opnd C t b) = true := by
    have hb := and_true_operands hAO ht htand x hv b
    rcases down n C x (fun k hk => hAO.1 _ (gateAt_mem' C k hk)) _ hb with
      ⟨u, hu, hxu⟩ | ⟨k, hk, hr, hkand, hkv⟩
    · exact orIn_val_patch hhand r x _ u hu hxu
    · have hcone := reach_cone n C t ht _ (opnd_mem hAO ht b) (opnd_lt hAO ht b) k hr
      have hkJ := and_ancestor_junk hTop ht htand hk hkand hcone
      have hkg : k = g ∨ k = h := by simpa [hJ] using hkJ
      rcases hkg with hkg | hkg <;> subst k
      · change gateVal n C g x = true at hkv
        rw [hxg] at hkv
        cases hkv
      · have hother := and_true_operands hAO ht htand x hv (1 - b)
        have heq := (opposite_of_mixed_junk G C s hcol hAO hTop g h hJ hmix
          t ht htand htbelow b hr).2.2.2 x
        change wireVal n C (opnd C t (1 - b)) x = true at hother
        rw [heq, hxg] at hother
        cases hother
  apply W_and_patch r x t ht htand hne
  intro w hw
  obtain ⟨b, rfl⟩ := (mem_inputs_iff_opnd hAO ht w).mp hw
  exact ⟨opnd_lt hAO ht b, hraw b⟩

lemma output_survives_without_other {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (hAO : IsAO2 n C) (hTop : TopForm G C) (hF : circuitFun n C = graphFun G ∅)
    (g h : ℕ) (hJ : junk G C = {g, h})
    (hmix : ∀ c : Bool, gateVal n C h (monoInput s c) = true)
    (r : Gate) (x : Fin n → Bool) (hxg : gateVal n C g x = false)
    (hv : circuitFun n C x = true) : circuitFun n (patch C h r) x = true := by
  have hhJ : h ∈ junk G C := by simp [hJ]
  have hhand := (mem_junk.mp hhJ).2.1
  rcases down n C x (fun k hk => hAO.1 _ (gateAt_mem' C k hk)) C.output hv with
    ⟨u, hu, hxu⟩ | ⟨k, hk, hr, hkand, hkv⟩
  · exact orIn_val_patch hhand r x C.output u hu hxu
  · rcases and_junk_or_below (G := G) hk hkand with hkJ | hkbelow
    · have hkg : k = g ∨ k = h := by simpa [hJ] using hkJ
      rcases hkg with hkg | hkg <;> subst k
      · change gateVal n C g x = true at hkv
        rw [hxg] at hkv
        cases hkv
      · exact False.elim (output_not_reaches_mixed hcol hF hmix hr)
    · apply reach_up_patch hhand r x C.output k hr
      exact clean_and_survives_without_other G C s hcol hAO hTop g h hJ hmix r x hxg
        k hk hkand hkbelow hkv

lemma lost_edge_uses_other {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (hAO : IsAO2 n C) (hTop : TopForm G C) (hF : circuitFun n C = graphFun G ∅)
    (g h : ℕ) (hJ : junk G C = {g, h})
    (hmix : ∀ c : Bool, gateVal n C h (monoInput s c) = true)
    (r : Gate) (u v : Fin n) (huv : G.Adj u v)
    (hlost : circuitFun n (patch C h r) (pairInput u v) = false) :
    gateVal n C g (pairInput u v) = true := by
  cases hg : gateVal n C g (pairInput u v) with
  | true => rfl
  | false =>
    have hv : circuitFun n C (pairInput u v) = true := by
      rw [hF]
      exact (graph_true G (pairInput u v)).mpr
        ⟨u, v, huv, by simp [pairInput], by simp [pairInput]⟩
    have hp := output_survives_without_other G C s hcol hAO hTop hF g h hJ hmix r _ hg hv
    rw [hlost] at hp
    cases hp

lemma wire_unchanged_away {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (f : ℕ) (r : Gate) (x : Fin n → Bool) :
    ∀ w, w < n + C.gates.length → w ≠ n + f →
      (∀ k, w = n + k → ¬ InCone n C f k) →
      W n (patch C f r) x w = W n C x w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hwne hwcone
    by_cases hwn : w < n
    · rw [W_input n (patch C f r) x w hwn, W_input n C x w hwn]
    · have hk : w - n < C.gates.length := by omega
      have heq : w = n + (w - n) := by omega
      have hne : f ≠ w - n := by intro hf; apply hwne; omega
      rw [heq, W_gate n (patch C f r) x (w - n) (by simpa [patch] using hk),
        W_gate n C x (w - n) hk, gateAt_patch_ne C f (w - n) r hne]
      congr 1
      apply List.map_congr_left
      intro i hi
      have hil := hAO.2.1 (w - n) hk i hi
      rw [ite_eq_left hil, ite_eq_left hil]
      apply ih i (by omega) (by omega)
      · intro hie
        apply hwcone (w - n) heq
        apply (inCone_iff n C f (w - n)).mpr
        refine ⟨hk, f, by omega, ?_, Or.inl rfl⟩
        rwa [← hie]
      · intro k hik hfk
        apply hwcone (w - n) heq
        apply (inCone_iff n C f (w - n)).mpr
        refine ⟨hk, k, by omega, ?_, Or.inr hfk⟩
        rwa [← hik]

lemma gate_unchanged_of_notCone {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (f k : ℕ) (r : Gate) (hk : k < C.gates.length) (hne : f ≠ k)
    (hcone : ¬ InCone n C f k) (x : Fin n → Bool) :
    gateVal n (patch C f r) k x = gateVal n C k x := by
  apply wire_unchanged_away hAO f r x (n + k) (by omega) (by omega)
  intro j hj
  have hkj : k = j := by omega
  subst j
  exact hcone

lemma guarded_or_repair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (hAO : IsAO2 n C) (hTop : TopForm G C) (hF : circuitFun n C = graphFun G ∅)
    (g h : ℕ) (hJ : junk G C = {g, h})
    (hmix : ∀ c : Bool, gateVal n C h (monoInput s c) = true)
    (r : Gate) (hror : r.op = GateOp.or) (hrlen : r.inputs.length = 2)
    (hrback : ∀ i ∈ r.inputs, i < n + h)
    (preserve : ∀ x : Fin n → Bool, gateVal n (patch C h r) g x = gateVal n C g x)
    (guarded : ∀ x : Fin n → Bool, gateVal n C g x = true →
      gateBit (earlierWires C h (List.ofFn x)) r = true → graphFun G ∅ x = true)
    (critical : ∀ a b, G.Adj a b → circuitFun n (patch C h off) (pairInput a b) = false →
      gateBit (earlierWires C h (List.ofFn (pairInput a b))) r = true) :
    let D := patch C h r
    IsAO2 n D ∧ circuitFun n D = graphFun G ∅ ∧ D.size = C.size ∧
      junk G D ⊆ junk G C ∧ h ∉ junk G D := by
  have hhJ : h ∈ junk G C := by simp [hJ]
  have hh := (mem_junk.mp hhJ).1
  have hC := ao_mono hAO
  let D := patch C h r
  have hDAO : IsAO2 n D := patch_gate_ao hAO hh r (Or.inr hror) hrlen hrback
  have hmono : Monotone2 D := ao_mono hDAO
  have hdom (x : Fin n → Bool) (hxF : graphFun G ∅ x = false)
      (hxg : gateVal n C g x = true) :
      WiresLE (D.wires (List.ofFn x)) (C.wires (List.ofFn x)) := by
    rw [← original_patch hh]
    apply patch_mono hC hh
    intro hr
    have hf := guarded x hxg hr
    rw [hxF] at hf
    cases hf
  have clean_stays (t : ℕ) (ht : t < C.gates.length)
      (htand : (gateAt C t).op = GateOp.and) (htbelow : BelowF G C t) : BelowF G D t := by
    intro x hx
    cases hxF : graphFun G ∅ x with
    | true => rfl
    | false =>
      cases hxg : gateVal n C g x with
      | false =>
        have hgp : gateVal n D g x = false := (preserve x).trans hxg
        have hf := clean_and_false_under_guard G C s hcol hAO hTop g h hJ hmix
          r x hxF hgp t ht htand htbelow
        rw [hf] at hx
        cases hx
      | true =>
        have hv : gateVal n C t x = true := (hdom x hxF hxg).2 (n + t) hx
        have hf := htbelow x hv
        rw [hxF] at hf
        cases hf
  have allEdges (a b : Fin n) (hab : G.Adj a b) : circuitFun n D (pairInput a b) = true := by
    cases hcut : circuitFun n (patch C h off) (pairInput a b) with
    | true =>
      exact (patch_mono hC hh off r (List.ofFn (pairInput a b))
        (by simp [off_bit])).2 C.output hcut
    | false =>
      have hle := patch_mono hC hh C.gates[h] r (List.ofFn (pairInput a b))
        (fun _ => critical a b hab hcut)
      rw [original_patch hh] at hle
      apply hle.2 C.output
      change circuitFun n C (pairInput a b) = true
      rw [hF]
      exact (graph_true G (pairInput a b)).mpr
        ⟨a, b, hab, by simp [pairInput], by simp [pairInput]⟩
  have hcompute : circuitFun n D = graphFun G ∅ := by
    funext x
    cases hxF : graphFun G ∅ x with
    | true =>
      obtain ⟨a, b, hab, ha, hb⟩ := (graph_true G x).mp hxF
      exact circuit_mono hmono (pair_le ha hb) (allEdges a b hab)
    | false =>
      cases hxg : gateVal n C g x with
      | false =>
        exact output_false_under_guard G C s hcol hAO hTop hF g h hJ hmix
          r x hxF ((preserve x).trans hxg)
      | true =>
        cases hxD : circuitFun n D x with
        | false => rfl
        | true =>
          have hv : circuitFun n C x = true := (hdom x hxF hxg).2 C.output hxD
          rw [hF, hxF] at hv
          cases hv
  have hlen : D.gates.length = C.gates.length := List.length_set
  have hclean : h ∉ junk G D := by
    intro hd
    have hop := (mem_junk.mp hd).2.1
    have he : gateAt D h = r := by
      simp [D, patch, gateAt, List.getD_eq_getElem?_getD, hh]
    rw [he, hror] at hop
    cases hop
  have hsub : junk G D ⊆ junk G C := by
    intro k hk
    have hne : h ≠ k := fun he => hclean (he.symm ▸ hk)
    obtain ⟨hklen, hkop, _, x, hx, hxF⟩ := mem_junk.mp hk
    have hkc : k < C.gates.length := hlen ▸ hklen
    have hcop : (gateAt C k).op = GateOp.and := by
      rwa [show gateAt D k = gateAt C k from gateAt_patch_ne C h k r hne] at hkop
    rcases and_junk_or_below (G := G) hkc hcop with hkJ | hkbelow
    · exact hkJ
    · have hf := clean_stays k hkc hcop hkbelow x hx
      rw [hxF] at hf
      cases hf
  exact ⟨hDAO, hcompute, hlen, hsub, hclean⟩



end Mixed

namespace MixedOr

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
  PEqualNP.Outside.L_meta_5012_aux.Mixed

lemma W_or_patch_ne {n : ℕ} {C : Circuit} {e : ℕ} (r : Gate)
    (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hne : e ≠ k) (hkor : (gateAt C k).op = GateOp.or)
    (w : ℕ) (hw : w ∈ (gateAt C k).inputs) (hwlt : w < n + k)
    (hv : W n (patch C e r) x w = true) :
    W n (patch C e r) x (n + k) = true := by
  apply W_or n (patch C e r) x k (by simpa [patch] using hk) _ w _ hwlt hv
  · rw [gateAt_patch_ne C e k r hne]; exact hkor
  · rw [gateAt_patch_ne C e k r hne]; exact hw

lemma reach_val_patch_away {n : ℕ} {C : Circuit} {e : ℕ}
    (r : Gate) (x : Fin n → Bool) (g : ℕ)
    (hv : W n (patch C e r) x (n + g) = true) :
    ∀ k, k < C.gates.length → e ∉ (orSets n C).getD k [] →
      g ∈ (orSets n C).getD k [] → W n (patch C e r) x (n + k) = true := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk hnot hmem
    rcases (orSets_mem_iff n C k g hk).mp hmem with he | ⟨hop, w, hw, hn, hlt, hx⟩
    · rw [← he]; exact hv
    · have hne : e ≠ k := fun he => hnot ((orSets_mem_iff n C k e hk).mpr (Or.inl he))
      have hnot' : e ∉ (orSets n C).getD (w - n) [] := by
        intro he
        exact hnot ((orSets_mem_iff n C k e hk).mpr
          (Or.inr ⟨hop, w, hw, hn, hlt, he⟩))
      have h3 := ih (w - n) (by omega) (by omega) hnot' hx
      have heq : n + (w - n) = w := by omega
      rw [heq] at h3
      exact W_or_patch_ne r x k hk hne hop w hw hlt h3

lemma reach_up_patch_away {n : ℕ} {C : Circuit} {e : ℕ}
    (r : Gate) (x : Fin n → Bool) (w g : ℕ)
    (hnot : ¬ OrReaches n C w e)
    (hr : OrReaches n C w g) (hv : W n (patch C e r) x (n + g) = true) :
    W n (patch C e r) x w = true := by
  obtain ⟨hn, hmem⟩ := hr
  by_cases hk : w - n < C.gates.length
  · have hnot' : e ∉ (orSets n C).getD (w - n) [] := fun he => hnot ⟨hn, he⟩
    have h3 := reach_val_patch_away r x g hv (w - n) hk hnot' hmem
    have heq : n + (w - n) = w := by omega
    rwa [heq] at h3
  · exfalso
    have hlen : (orSets n C).length = C.gates.length := by
      unfold orSets; rw [orFold_length]; simp
    have hge : (orSets n C).length ≤ w - n := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge] at hmem
    simp at hmem

lemma orIn_val_patch_away {n : ℕ} {C : Circuit} {e : ℕ}
    (r : Gate) (x : Fin n → Bool) (w : ℕ)
    (hnot : ¬ OrReaches n C w e)
    (u : Fin n) (hu : u ∈ orIn n C w) (hxu : x u = true) :
    W n (patch C e r) x w = true := by
  rcases (orIn_mem n C w u).mp hu with hu | ⟨k, hk, hr, hkor, huk⟩
  · rw [← hu, W_input n (patch C e r) x u.val u.isLt]
    exact hxu
  · have hne : e ≠ k := by rintro rfl; exact hnot hr
    apply reach_up_patch_away r x w k hnot hr
    apply W_or_patch_ne r x k hk hne hkor u.val huk (by have := u.isLt; omega)
    rw [W_input n (patch C e r) x u.val u.isLt]
    exact hxu

end MixedOr

namespace MixedOr

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
  PEqualNP.Outside.L_meta_5012_aux.Mixed

lemma opposite_of_mixed_gate {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (hAO : IsAO2 n C) (hTop : TopForm G C) (g h : ℕ) (hJ : junk G C = {g, h})
    (hmix : ∀ c : Bool, gateVal n C h (monoInput s c) = true)
    (E : ℕ) (hmixE : ∀ c : Bool, gateVal n C E (monoInput s c) = true)
    (t : ℕ) (ht : t < C.gates.length) (htand : (gateAt C t).op = GateOp.and)
    (htbelow : BelowF G C t) (b : Fin 2) (hreach : OrReaches n C (opnd C t b) E) :
    side (n := n) C t (1 - b) = ∅ ∧
      ¬ OrReaches n C (opnd C t (1 - b)) h ∧
      OrReaches n C (opnd C t (1 - b)) g ∧
      ∀ x : Fin n → Bool, wireVal n C (opnd C t (1 - b)) x = gateVal n C g x := by
  have hempty : side (n := n) C t (1 - b) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro u hu
    have hh : W n C (monoInput s (s u)) (opnd C t b) = true :=
      reach_up n C _ _ E hreach (hmixE (s u))
    have ho : W n C (monoInput s (s u)) (opnd C t (1 - b)) = true :=
      side_val n C _ t (1 - b) u hu (by simp [monoInput])
    have htf := htbelow _ (and_two hAO ht htand b _ hh ho)
    rw [monoInput_false G s hcol] at htf
    cases htf
  have hnot : ¬ OrReaches n C (opnd C t (1 - b)) h := by
    intro hr
    have hh : W n C (monoInput s false) (opnd C t b) = true :=
      reach_up n C _ _ E hreach (hmixE false)
    have ho : W n C (monoInput s false) (opnd C t (1 - b)) = true :=
      reach_up n C _ _ h hr (hmix false)
    have htf := htbelow _ (and_two hAO ht htand b _ hh ho)
    rw [monoInput_false G s hcol] at htf
    cases htf
  have hdown (x : Fin n → Bool) (hv : W n C x (opnd C t (1 - b)) = true) :
      OrReaches n C (opnd C t (1 - b)) g ∧ gateVal n C g x = true := by
    rcases down n C x (fun k hk => hAO.1 _ (gateAt_mem' C k hk)) _ hv with
      ⟨u, hu, _⟩ | ⟨k, hk, hr, hkand, hkv⟩
    · change u ∈ side (n := n) C t (1 - b) at hu
      rw [hempty] at hu
      exact False.elim (Finset.notMem_empty _ hu)
    · have hcone := reach_cone n C t ht _ (opnd_mem hAO ht (1 - b))
        (opnd_lt hAO ht (1 - b)) k hr
      have hkJ := and_ancestor_junk hTop ht htand hk hkand hcone
      have hkg : k = g ∨ k = h := by simpa [hJ] using hkJ
      rcases hkg with hkg | hkg <;> subst k
      · exact ⟨hr, hkv⟩
      · exact False.elim (hnot hr)
  have hr := (hdown (fun _ => true) (wire_all_true hAO _
    (by have := opnd_lt hAO ht (1 - b); omega))).1
  refine ⟨hempty, hnot, hr, ?_⟩
  intro x
  apply Bool.eq_iff_iff.mpr
  constructor
  · exact fun hv => (hdown x hv).2
  · exact reach_up n C x _ g hr

end MixedOr

namespace MixedOr

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
  PEqualNP.Outside.L_meta_5012_aux.Mixed

lemma clean_and_survives_mixed_patch {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (hAO : IsAO2 n C) (hTop : TopForm G C) (g h : ℕ) (hJ : junk G C = {g, h})
    (hmix : ∀ c : Bool, gateVal n C h (monoInput s c) = true)
    (e : ℕ) (hmixE : ∀ c : Bool, gateVal n C e (monoInput s c) = true)
    (r : Gate) (x : Fin n → Bool) (hxg : gateVal n C g x = false)
    (t : ℕ) (ht : t < C.gates.length) (htand : (gateAt C t).op = GateOp.and)
    (htbelow : BelowF G C t) (hv : gateVal n C t x = true) :
    gateVal n (patch C e r) t x = true := by
  have hne := mixed_ne_clean hcol hmixE htbelow
  have hnot (b : Fin 2) : ¬ OrReaches n C (opnd C t b) e := by
    intro hr
    have heq := (opposite_of_mixed_gate G C s hcol hAO hTop g h hJ hmix
      e hmixE t ht htand htbelow b hr).2.2.2 x
    have hother := and_true_operands hAO ht htand x hv (1 - b)
    change wireVal n C (opnd C t (1 - b)) x = true at hother
    rw [heq, hxg] at hother
    cases hother
  have hraw (b : Fin 2) : W n (patch C e r) x (opnd C t b) = true := by
    have hb := and_true_operands hAO ht htand x hv b
    rcases down n C x (fun k hk => hAO.1 _ (gateAt_mem' C k hk)) _ hb with
      ⟨u, hu, hxu⟩ | ⟨k, hk, hr, hkand, hkv⟩
    · exact orIn_val_patch_away r x _ (hnot b) u hu hxu
    · have hcone := reach_cone n C t ht _ (opnd_mem hAO ht b) (opnd_lt hAO ht b) k hr
      have hkJ := and_ancestor_junk hTop ht htand hk hkand hcone
      have hkg : k = g ∨ k = h := by simpa [hJ] using hkJ
      rcases hkg with hkg | hkg <;> subst k
      · change gateVal n C g x = true at hkv
        rw [hxg] at hkv
        cases hkv
      · have hother := and_true_operands hAO ht htand x hv (1 - b)
        have heq := (opposite_of_mixed_junk G C s hcol hAO hTop g h hJ hmix
          t ht htand htbelow b hr).2.2.2 x
        change wireVal n C (opnd C t (1 - b)) x = true at hother
        rw [heq, hxg] at hother
        cases hother
  apply W_and_patch r x t ht htand hne
  intro w hw
  obtain ⟨b, rfl⟩ := (mem_inputs_iff_opnd hAO ht w).mp hw
  exact ⟨opnd_lt hAO ht b, hraw b⟩

lemma output_survives_mixed_patch {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (hAO : IsAO2 n C) (hTop : TopForm G C) (hF : circuitFun n C = graphFun G ∅)
    (g h : ℕ) (hJ : junk G C = {g, h})
    (hmix : ∀ c : Bool, gateVal n C h (monoInput s c) = true)
    (e : ℕ) (hmixE : ∀ c : Bool, gateVal n C e (monoInput s c) = true)
    (r : Gate) (x : Fin n → Bool) (hxg : gateVal n C g x = false)
    (hv : circuitFun n C x = true) : circuitFun n (patch C e r) x = true := by
  have hnot := output_not_reaches_mixed hcol hF hmixE
  rcases down n C x (fun k hk => hAO.1 _ (gateAt_mem' C k hk)) C.output hv with
    ⟨u, hu, hxu⟩ | ⟨k, hk, hr, hkand, hkv⟩
  · exact orIn_val_patch_away r x C.output hnot u hu hxu
  · rcases and_junk_or_below (G := G) hk hkand with hkJ | hkbelow
    · have hkg : k = g ∨ k = h := by simpa [hJ] using hkJ
      rcases hkg with hkg | hkg <;> subst k
      · change gateVal n C g x = true at hkv
        rw [hxg] at hkv
        cases hkv
      · exact False.elim (output_not_reaches_mixed hcol hF hmix hr)
    · apply reach_up_patch_away r x C.output k hnot hr
      exact clean_and_survives_mixed_patch G C s hcol hAO hTop g h hJ hmix e hmixE
        r x hxg k hk hkand hkbelow hkv

lemma mixed_lost_edge_uses_other {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (hAO : IsAO2 n C) (hTop : TopForm G C) (hF : circuitFun n C = graphFun G ∅)
    (g h : ℕ) (hJ : junk G C = {g, h})
    (hmix : ∀ c : Bool, gateVal n C h (monoInput s c) = true)
    (e : ℕ) (hmixE : ∀ c : Bool, gateVal n C e (monoInput s c) = true)
    (r : Gate) (u v : Fin n) (huv : G.Adj u v)
    (hlost : circuitFun n (patch C e r) (pairInput u v) = false) :
    gateVal n C g (pairInput u v) = true := by
  cases hg : gateVal n C g (pairInput u v) with
  | true => rfl
  | false =>
    have hv : circuitFun n C (pairInput u v) = true := by
      rw [hF]
      exact (graph_true G (pairInput u v)).mpr
        ⟨u, v, huv, by simp [pairInput], by simp [pairInput]⟩
    have hp := output_survives_mixed_patch G C s hcol hAO hTop hF g h hJ hmix e hmixE
      r _ hg hv
    rw [hlost] at hp
    cases hp

end MixedOr


namespace Mixed

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

lemma cone_trans {n : ℕ} {C : Circuit} {i j k : ℕ}
    (hij : InCone n C i j) (hjk : InCone n C j k) : InCone n C i k := by
  induction k using Nat.strong_induction_on generalizing j with
  | _ k ih =>
    obtain ⟨hk, p, hpk, hpin, hjp⟩ := (inCone_iff n C j k).mp hjk
    apply (inCone_iff n C i k).mpr
    refine ⟨hk, p, hpk, hpin, Or.inr ?_⟩
    rcases hjp with he | hjp
    · subst j; exact hij
    · exact ih p hpk hij hjp

lemma no_and_below_independent_junk {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hTop : TopForm G C) {g h : ℕ} (hJ : junk G C = {g, h})
    (hgh : ¬ InCone n C g h) :
    ∀ k, InCone n C k h → (gateAt C k).op ≠ GateOp.and := by
  have hhJ : h ∈ junk G C := by simp [hJ]
  have hh := (mem_junk.mp hhJ).1
  have hhand := (mem_junk.mp hhJ).2.1
  intro k hkh hand
  have hkl := inCone_lt n C h k hkh
  have hkJ := and_ancestor_junk hTop hh hhand (by omega) hand hkh
  have hk : k = g ∨ k = h := by simpa [hJ] using hkJ
  rcases hk with hkg | hkh'
  · subst k; exact hgh hkh
  · omega

def InsideWire (n : ℕ) (C : Circuit) (h w : ℕ) : Prop :=
  w < n ∨ ∃ k, w = n + k ∧ InCone n C k h


lemma operand_inside {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {t h : ℕ} (ht : t < C.gates.length) (hth : t = h ∨ InCone n C t h)
    (w : ℕ) (hw : w ∈ (gateAt C t).inputs) : InsideWire n C h w := by
  by_cases hwn : w < n
  · exact Or.inl hwn
  · right
    have hwt := hAO.2.1 t ht w hw
    have heq : w = n + (w - n) := by omega
    have hct : InCone n C (w - n) t := by
      apply (inCone_iff n C (w - n) t).mpr
      exact ⟨ht, w - n, by omega, by rwa [← heq], Or.inl rfl⟩
    refine ⟨w - n, heq, ?_⟩
    rcases hth with rfl | hth
    · exact hct
    · exact cone_trans hct hth

lemma inside_reached_and {n : ℕ} {C : Circuit} {h w k : ℕ}
    (hinside : InsideWire n C h w) (hr : OrReaches n C w k) : InCone n C k h := by
  rcases hinside with hi | ⟨j, rfl, hjh⟩
  · have := hr.1; omega
  · have hjl := inCone_lt n C h j hjh
    have hh : h < C.gates.length := (inCone_iff n C j h).mp hjh |>.1
    have hmem : k ∈ (orSets n C).getD j [] := by simpa using hr.2
    rcases orSets_cone n C j (by omega) k hmem with heq | hkj
    · subst k; exact hjh
    · exact cone_trans hkj hjh

lemma inside_pure_or {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {h w : ℕ}
    (hnoand : ∀ k, InCone n C k h → (gateAt C k).op ≠ GateOp.and)
    (hinside : InsideWire n C h w) (x : Fin n → Bool) :
    wireVal n C w x = decide (∃ u ∈ orIn n C w, x u = true) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · intro hv
    rcases down n C x (fun k hk => hAO.1 _ (gateAt_mem' C k hk)) w hv with
      hr | ⟨k, _, hk, hand, _⟩
    · exact hr
    · exact False.elim (hnoand k (inside_reached_and hinside hk) hand)
  · rintro ⟨u, hu, hxu⟩
    exact orIn_val n C x w u hu hxu

lemma mixed_wire_not_input {n : ℕ} {C : Circuit} {s : Fin n → Bool} {w : ℕ}
    (hmix : ∀ c : Bool, W n C (monoInput s c) w = true) : ¬ w < n := by
  intro hw
  have h0 := hmix false
  have h1 := hmix true
  rw [W_input n C _ w hw] at h0 h1
  simp only [monoInput, decide_eq_true_eq] at h0 h1
  rw [h0] at h1
  cases h1

lemma or_two_value {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {e : ℕ} (he : e < C.gates.length) (heor : (gateAt C e).op = GateOp.or)
    (x : Fin n → Bool) :
    gateVal n C e x = (wireVal n C (opnd C e 0) x || wireVal n C (opnd C e 1) x) := by
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem' C e he))
  have hp : p < n + e := hAO.2.1 e he p (by simp [hin])
  have hq : q < n + e := hAO.2.1 e he q (by simp [hin])
  change W n C x (n + e) = _
  rw [W_gate n C x e he]
  simp [heor, hin, GateOp.eval, hp, hq, opnd]
  rfl

lemma earliest_mixed_or {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hAO : IsAO2 n C) (hTop : TopForm G C)
    (g h : ℕ) (hJ : junk G C = {g, h}) (hind : ¬ InCone n C g h)
    (hmix : ∀ c : Bool, gateVal n C h (monoInput s c) = true) :
    ∃ e : ℕ, e < h ∧ InCone n C e h ∧ (gateAt C e).op = GateOp.or ∧
      (∀ c : Bool, gateVal n C e (monoInput s c) = true) ∧
      (∀ b : Fin 2, ∃ c : Bool, wireVal n C (opnd C e b) (monoInput s c) = false) ∧
      (∀ b : Fin 2, (side (n := n) C e b).Nonempty ∧
        ∀ x : Fin n → Bool, wireVal n C (opnd C e b) x =
          decide (∃ u ∈ side (n := n) C e b, x u = true)) ∧
      ∃ c : Bool, (∀ u ∈ side (n := n) C e 0, s u = c) ∧
        (∀ u ∈ side (n := n) C e 1, s u = !c) := by
  classical
  have hhJ : h ∈ junk G C := by simp [hJ]
  have hh := (mem_junk.mp hhJ).1
  have hhand := (mem_junk.mp hhJ).2.1
  have hnoand := no_and_below_independent_junk hTop hJ hind
  have hstart : ∃ e : ℕ, InCone n C e h ∧
      ∀ c : Bool, gateVal n C e (monoInput s c) = true := by
    have hm : ∀ c : Bool, W n C (monoInput s c) (opnd C h 0) = true :=
      fun c => and_true_operands hAO hh hhand _ (hmix c) 0
    have hi := operand_inside hAO hh (Or.inl rfl) _ (opnd_mem hAO hh 0)
    rcases hi with hi | ⟨e, heq, heh⟩
    · exact False.elim (mixed_wire_not_input hm hi)
    · refine ⟨e, heh, ?_⟩
      intro c
      have hc := hm c
      rw [heq] at hc
      exact hc
  let e := Nat.find hstart
  have heh : InCone n C e h := (Nat.find_spec hstart).1
  have hem : ∀ c : Bool, gateVal n C e (monoInput s c) = true := (Nat.find_spec hstart).2
  have heh' : e < h := inCone_lt n C h e heh
  have he : e < C.gates.length := by omega
  have heor : (gateAt C e).op = GateOp.or := by
    rcases hAO.1 _ (gateAt_mem' C e he) with hea | heo
    · exact False.elim (hnoand e heh hea)
    · exact heo
  have hins (b : Fin 2) : InsideWire n C h (opnd C e b) :=
    operand_inside hAO he (Or.inr heh) _ (opnd_mem hAO he b)
  have hnotmixed (b : Fin 2) : ∃ c : Bool,
      wireVal n C (opnd C e b) (monoInput s c) = false := by
    by_contra hn
    push Not at hn
    have hm : ∀ c : Bool, W n C (monoInput s c) (opnd C e b) = true := by
      intro c
      cases hv : wireVal n C (opnd C e b) (monoInput s c) with
      | true => exact hv
      | false => exact False.elim (hn c hv)
    rcases hins b with hi | ⟨k, heq, hkh⟩
    · exact mixed_wire_not_input hm hi
    · have hkm : ∀ c : Bool, gateVal n C k (monoInput s c) = true := by
        intro c
        have hc := hm c
        rw [heq] at hc
        exact hc
      have hmin : e ≤ k := Nat.find_min' hstart ⟨hkh, hkm⟩
      have hlt := opnd_lt hAO he b
      omega
  have hpure (b : Fin 2) : (side (n := n) C e b).Nonempty ∧
      ∀ x : Fin n → Bool, wireVal n C (opnd C e b) x =
        decide (∃ u ∈ side (n := n) C e b, x u = true) := by
    have hp := inside_pure_or hAO hnoand (hins b)
    refine ⟨?_, hp⟩
    have hall := wire_all_true hAO (opnd C e b) (by have := opnd_lt hAO he b; omega)
    change wireVal n C (opnd C e b) (fun _ => true) = true at hall
    rw [hp] at hall
    simpa [Finset.Nonempty, side] using hall
  refine ⟨e, heh', heh, heor, hem, hnotmixed, hpure, ?_⟩
  obtain ⟨c, hc⟩ := hnotmixed 0
  have h1 : wireVal n C (opnd C e 1) (monoInput s c) = true := by
    have hm := hem c
    rw [or_two_value hAO he heor, hc, Bool.false_or] at hm
    exact hm
  obtain ⟨d, hd⟩ := hnotmixed 1
  have hdc : d ≠ c := by intro hdc; subst d; rw [h1] at hd; cases hd
  have hd' : d = !c := by cases d <;> cases c <;> simp_all
  subst d
  refine ⟨!c, ?_, ?_⟩
  · intro u hu
    have huc : s u ≠ c := by
      intro huc
      have hv := side_val n C (monoInput s c) e 0 u hu (by simp [monoInput, huc])
      change wireVal n C (opnd C e 0) (monoInput s c) = true at hv
      rw [hc] at hv
      cases hv
    cases hsu : s u <;> cases c <;> simp_all
  · intro u hu
    have huc : s u ≠ !c := by
      intro huc
      have hv := side_val n C (monoInput s (!c)) e 1 u hu (by simp [monoInput, huc])
      change wireVal n C (opnd C e 1) (monoInput s (!c)) = true at hv
      rw [hd] at hv
      cases hv
    cases hsu : s u <;> cases c <;> simp_all

end Mixed


namespace Mixed

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

lemma pair_same_color_eq {n : ℕ} {G : SimpleGraph (Fin n)} {s : Fin n → Bool}
    (hcol : ∀ a b, G.Adj a b → s a ≠ s b) {a b u v : Fin n} (hab : G.Adj a b)
    (hu : pairInput a b u = true) (hv : pairInput a b v = true) (hcolor : s v = s u) :
    v = u := by
  simp only [pairInput, decide_eq_true_eq] at hu hv
  rcases hu with hu | hu <;> rcases hv with hv | hv
  · exact hv.trans hu.symm
  · apply False.elim
    apply hcol a b hab
    simpa only [hu, hv] using hcolor.symm
  · apply False.elim
    apply hcol a b hab
    simpa only [hu, hv] using hcolor
  · exact hv.trans hu.symm

lemma or_two_value_oriented {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {e : ℕ} (he : e < C.gates.length) (heor : (gateAt C e).op = GateOp.or)
    (b : Fin 2) (x : Fin n → Bool) :
    gateVal n C e x =
      (wireVal n C (opnd C e b) x || wireVal n C (opnd C e (1 - b)) x) := by
  fin_cases b <;> simpa [Bool.or_comm] using or_two_value hAO he heor x

lemma raw_mixed_or_alias_for_star {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hcol : ∀ a b, G.Adj a b → s a ≠ s b)
    (hAO : IsAO2 n C) (e g : ℕ) (he : e < C.gates.length)
    (heor : (gateAt C e).op = GateOp.or)
    (hpure : ∀ b : Fin 2, ∀ x : Fin n → Bool, wireVal n C (opnd C e b) x =
      decide (∃ v ∈ side (n := n) C e b, x v = true))
    (hcolors : ∃ c : Bool, (∀ v ∈ side (n := n) C e 0, s v = c) ∧
      (∀ v ∈ side (n := n) C e 1, s v = !c))
    (u : Fin n)
    (hcenter : ∀ a b, G.Adj a b → gateVal n C g (pairInput a b) = true →
      pairInput a b u = true) :
    ∃ w : ℕ, w < n + e ∧
      (∀ x : Fin n → Bool, wireVal n C w x = true → gateVal n C e x = true) ∧
      ∀ a b, G.Adj a b → gateVal n C g (pairInput a b) = true →
        wireVal n C w (pairInput a b) = gateVal n C e (pairInput a b) := by
  classical
  obtain ⟨c, hcol0, hcol1⟩ := hcolors
  have horient : ∃ b : Fin 2, ∀ v ∈ side (n := n) C e b, s v = s u := by
    by_cases hu : s u = c
    · exact ⟨0, fun v hv => (hcol0 v hv).trans hu.symm⟩
    · have hc : (!c) = s u := by cases hsu : s u <;> cases c <;> simp_all
      exact ⟨1, fun v hv => (hcol1 v hv).trans hc⟩
  obtain ⟨b, hbcol⟩ := horient
  by_cases hu : u ∈ side (n := n) C e b
  · refine ⟨u.val, by have := u.isLt; omega, ?_, ?_⟩
    · intro x hxu
      have hxu' : x u = true := by
        change W n C x u.val = true at hxu
        rwa [W_input n C x u.val u.isLt] at hxu
      exact W_or n C x e he heor _ (opnd_mem hAO he b) (opnd_lt hAO he b)
        (side_val n C x e b u hu hxu')
    · intro a d had hg
      have hw : wireVal n C u.val (pairInput a d) = true := by
        change W n C (pairInput a d) u.val = true
        rw [W_input n C _ u.val u.isLt]
        exact hcenter a d had hg
      have hev : gateVal n C e (pairInput a d) = true :=
        W_or n C _ e he heor _ (opnd_mem hAO he b) (opnd_lt hAO he b)
          (side_val n C _ e b u hu (hcenter a d had hg))
      exact hw.trans hev.symm
  · refine ⟨opnd C e (1 - b), opnd_lt hAO he (1 - b), ?_, ?_⟩
    · intro x hx
      exact W_or n C x e he heor _ (opnd_mem hAO he (1 - b))
        (opnd_lt hAO he (1 - b)) hx
    · intro a d had hg
      have hn : ¬ ∃ v ∈ side (n := n) C e b, pairInput a d v = true := by
        rintro ⟨v, hv, hpv⟩
        have heq : v = u := pair_same_color_eq hcol had (hcenter a d had hg) hpv (hbcol v hv)
        subst v
        exact hu hv
      have hvfalse : wireVal n C (opnd C e b) (pairInput a d) = false := by
        rw [hpure]
        simp [hn]
      have heq := or_two_value_oriented hAO he heor b (pairInput a d)
      rw [hvfalse, Bool.false_or] at heq
      exact heq.symm

lemma earliest_mixed_or_alias {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hcol : ∀ a b, G.Adj a b → s a ≠ s b)
    (hAO : IsAO2 n C) (hTop : TopForm G C)
    (g h : ℕ) (hJ : junk G C = {g, h}) (hind : ¬ InCone n C g h)
    (hmix : ∀ c : Bool, gateVal n C h (monoInput s c) = true)
    (u : Fin n)
    (hcenter : ∀ a b, G.Adj a b → gateVal n C g (pairInput a b) = true →
      pairInput a b u = true) :
    ∃ e w : ℕ, e < h ∧ InCone n C e h ∧ (gateAt C e).op = GateOp.or ∧
      (∀ c : Bool, gateVal n C e (monoInput s c) = true) ∧ w < n + e ∧
      (∀ x : Fin n → Bool, wireVal n C w x = true → gateVal n C e x = true) ∧
      ∀ a b, G.Adj a b → gateVal n C g (pairInput a b) = true →
        wireVal n C w (pairInput a b) = gateVal n C e (pairInput a b) := by
  obtain ⟨e, heh, hecone, heor, hemix, _, hpure, hcolors⟩ :=
    earliest_mixed_or G C s hAO hTop g h hJ hind hmix
  have hhJ : h ∈ junk G C := by simp [hJ]
  have hh := (mem_junk.mp hhJ).1
  obtain ⟨w, hw, hunder, hagree⟩ := raw_mixed_or_alias_for_star G C s hcol hAO e g
    (by omega) heor (fun b => (hpure b).2) hcolors u hcenter
  exact ⟨e, w, heh, hecone, heor, hemix, hw, hunder, hagree⟩

def copyGate (w : ℕ) : Gate := ⟨GateOp.or, [w, w]⟩

lemma copy_bit {n : ℕ} {C : Circuit} {e w : ℕ}
    (he : e < C.gates.length) (hw : w < n + e) (x : Fin n → Bool) :
    gateBit (earlierWires C e (List.ofFn x)) (copyGate w) = wireVal n C w x := by
  simp only [gateBit, copyGate, GateOp.eval, List.map_cons, List.map_nil,
    List.any_cons, List.any_nil, id_eq, Bool.or_false, Bool.or_self]
  exact earlier_read_eq_wireVal he hw x

lemma original_gate_bit {n : ℕ} {C : Circuit} {e : ℕ}
    (he : e < C.gates.length) (x : Fin n → Bool) :
    gateVal n C e x = gateBit (earlierWires C e (List.ofFn x)) C.gates[e] := by
  have hp := patch_bit he C.gates[e] x
  rwa [original_patch he] at hp

lemma lost_input_gate_true {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {e : ℕ} (he : e < C.gates.length) (x : Fin n → Bool)
    (hon : circuitFun n C x = true) (hoff : circuitFun n (patch C e off) x = false) :
    gateVal n C e x = true := by
  cases hv : gateVal n C e x with
  | true => rfl
  | false =>
    have hbit : gateBit (earlierWires C e (List.ofFn x)) C.gates[e] = false :=
      (original_gate_bit he x).symm.trans hv
    have hle := patch_mono (ao_mono hAO) he C.gates[e] off (List.ofFn x)
      (by rw [hbit, off_bit]; exact id)
    rw [original_patch he] at hle
    have hout : circuitFun n (patch C e off) x = true := hle.2 C.output hon
    rw [hoff] at hout
    cases hout

lemma alias_patch_computes_of_critical {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hAO : IsAO2 n C) (hF : circuitFun n C = graphFun G ∅)
    (e w : ℕ) (he : e < C.gates.length) (hw : w < n + e)
    (hunder : ∀ x : Fin n → Bool, wireVal n C w x = true → gateVal n C e x = true)
    (hcritical : ∀ a b, G.Adj a b → circuitFun n (patch C e off) (pairInput a b) = false →
      wireVal n C w (pairInput a b) = true) :
    let D := patch C e (copyGate w)
    IsAO2 n D ∧ circuitFun n D = graphFun G ∅ ∧ D.size = C.size := by
  let D := patch C e (copyGate w)
  have hC := ao_mono hAO
  have hDAO : IsAO2 n D := by
    apply patch_gate_ao hAO he
    · exact Or.inr rfl
    · rfl
    · intro i hi
      have hiw : i = w := by simpa [copyGate] using hi
      subst i
      exact hw
  have hmono := ao_mono hDAO
  have hdom (x : Fin n → Bool) : WiresLE (D.wires (List.ofFn x)) (C.wires (List.ofFn x)) := by
    rw [← original_patch he]
    apply patch_mono hC he
    intro hbit
    rw [copy_bit he hw] at hbit
    have hold := hunder x hbit
    rwa [original_gate_bit he] at hold
  have allEdges (a b : Fin n) (hab : G.Adj a b) : circuitFun n D (pairInput a b) = true := by
    cases hcut : circuitFun n (patch C e off) (pairInput a b) with
    | true =>
      exact (patch_mono hC he off (copyGate w) (List.ofFn (pairInput a b))
        (by simp [off_bit])).2 C.output hcut
    | false =>
      have hle := patch_mono hC he C.gates[e] (copyGate w) (List.ofFn (pairInput a b))
        (by intro _; rw [copy_bit he hw]; exact hcritical a b hab hcut)
      rw [original_patch he] at hle
      apply hle.2 C.output
      change circuitFun n C (pairInput a b) = true
      rw [hF]
      exact (graph_true G (pairInput a b)).mpr
        ⟨a, b, hab, by simp [pairInput], by simp [pairInput]⟩
  have hcompute : circuitFun n D = graphFun G ∅ := by
    funext x
    cases hxF : graphFun G ∅ x with
    | true =>
      obtain ⟨a, b, hab, ha, hb⟩ := (graph_true G x).mp hxF
      exact circuit_mono hmono (pair_le ha hb) (allEdges a b hab)
    | false =>
      cases hxD : circuitFun n D x with
      | false => rfl
      | true =>
        have hv : circuitFun n C x = true := (hdom x).2 C.output hxD
        rw [hF, hxF] at hv
        cases hv
  exact ⟨hDAO, hcompute, List.length_set⟩

lemma alias_patch_computes_from_guard {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hAO : IsAO2 n C) (hF : circuitFun n C = graphFun G ∅)
    (e w g : ℕ) (he : e < C.gates.length) (hw : w < n + e)
    (hunder : ∀ x : Fin n → Bool, wireVal n C w x = true → gateVal n C e x = true)
    (hcritical : ∀ a b, G.Adj a b → circuitFun n (patch C e off) (pairInput a b) = false →
      gateVal n C g (pairInput a b) = true)
    (hagree : ∀ a b, G.Adj a b → gateVal n C g (pairInput a b) = true →
      wireVal n C w (pairInput a b) = gateVal n C e (pairInput a b)) :
    circuitFun n (patch C e (copyGate w)) = graphFun G ∅ := by
  apply (alias_patch_computes_of_critical G C hAO hF e w he hw hunder ?_).2.1
  intro a b hab hlost
  rw [hagree a b hab (hcritical a b hab hlost)]
  apply lost_input_gate_true hAO he (pairInput a b) _ hlost
  rw [hF]
  exact (graph_true G (pairInput a b)).mpr
    ⟨a, b, hab, by simp [pairInput], by simp [pairInput]⟩

end Mixed


namespace Splice

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover


def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

lemma run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega


lemma getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

lemma run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

lemma run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

lemma run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_prefix gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at']
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)


def Ok (n : ℕ) (gs : List Gate) : Prop :=
  ∀ j (hj : j < gs.length), ∃ o s t, gs[j] = ⟨o, [s, t]⟩ ∧ (o = GateOp.and ∨ o = GateOp.or) ∧
    s < n + j ∧ t < n + j

lemma ok_snoc {n : ℕ} {gs : List Gate} (h : Ok n gs) {o : GateOp} {s t : ℕ}
    (ho : o = GateOp.and ∨ o = GateOp.or) (hs : s < n + gs.length) (ht : t < n + gs.length) :
    Ok n (gs ++ [⟨o, [s, t]⟩]) := by
  intro j hj
  by_cases hlt : j < gs.length
  · rw [List.getElem_append_left hlt]; exact h j hlt
  · have : j = gs.length := by simp at hj; omega
    subst this
    exact ⟨o, s, t, by simp, ho, hs, ht⟩

open Classical in
noncomputable def dc (n : ℕ) (F : (Fin n → Bool) → Bool) (gs : List Gate) : ℕ :=
  ((Finset.range gs.length).filter fun i => (gs.getD i ⟨GateOp.or, []⟩).op = GateOp.and ∧
    ∃ x : Fin n → Bool, (run gs (List.ofFn x)).getD (n + i) false = true ∧ F x = false).card

open Classical in
lemma dc_snoc (n : ℕ) (F : (Fin n → Bool) → Bool) (gs : List Gate) (g : Gate) :
    dc n F (gs ++ [g]) ≤ dc n F gs + if g.op = GateOp.and ∧
      ∃ x : Fin n → Bool, (run (gs ++ [g]) (List.ofFn x)).getD (n + gs.length) false = true ∧
        F x = false then 1 else 0 := by
  unfold dc
  rw [List.length_append, List.length_singleton, Finset.range_add_one, Finset.filter_insert]
  have e : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
    simp [List.getD_eq_getElem?_getD]
  rw [e]
  have h1 : ((Finset.range gs.length).filter fun i =>
      ((gs ++ [g]).getD i ⟨GateOp.or, []⟩).op = GateOp.and ∧ ∃ x : Fin n → Bool,
        (run (gs ++ [g]) (List.ofFn x)).getD (n + i) false = true ∧ F x = false) =
      (Finset.range gs.length).filter fun i =>
      (gs.getD i ⟨GateOp.or, []⟩).op = GateOp.and ∧ ∃ x : Fin n → Bool,
        (run gs (List.ofFn x)).getD (n + i) false = true ∧ F x = false := by
    refine Finset.filter_congr fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    rw [getD_ltz _ _ _ _ hi']
    refine and_congr_right fun _ => exists_congr fun x => ?_
    rw [run_prefix gs [g] _ _ (by simp; omega)]
  rw [h1]
  split_ifs with h
  · exact (Finset.card_insert_le _ _)
  · simp


def Maps (n p : ℕ) (M : Finset ℕ) (gs : List Gate) (m : ℕ → ℕ)
    (V : (Fin n → Bool) → ℕ → Bool) : Prop :=
  ∀ w < n + p, (w < n ∨ w - n ∉ M) → m w < n + gs.length ∧
    ∀ x : Fin n → Bool, (run gs (List.ofFn x)).getD (m w) false = V x w

def Keeps (n p : ℕ) (Del : Finset ℕ) (gs : List Gate) (m : ℕ → ℕ)
    (op : ℕ → GateOp) : Prop :=
  ∀ j < p, j ∉ Del → ∃ k < gs.length, m (n + j) = n + k ∧
    (gs.getD k ⟨GateOp.or, []⟩).op = op j

lemma append_getD {α : Type} (z : α) (gs hs : List α) (k : ℕ) (hk : k < gs.length) :
    (gs ++ hs).getD k z = gs.getD k z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

lemma next_value (n : ℕ) (gs : List Gate) (o : GateOp) (a b : ℕ)
    (x : Fin n → Bool) :
    (run (gs ++ [⟨o, [a, b]⟩]) (List.ofFn x)).getD (n + gs.length) false =
      o.eval [(run gs (List.ofFn x)).getD a false,
        (run gs (List.ofFn x)).getD b false] := by
  rw [run_snoc]
  have heq : n + gs.length = (run gs (List.ofFn x)).length := by simp [run_length]
  rw [heq, getD_at]
  rfl

open Classical in
lemma build_splice
    (n N h r : ℕ) (M : Finset ℕ) (hnotM : h ∉ M)
    (op : ℕ → GateOp) (a b : ℕ → ℕ)
    (V : (Fin n → Bool) → ℕ → Bool) (F : (Fin n → Bool) → Bool)
    (hin : ∀ x w, w < n → V x w = (List.ofFn x).getD w false)
    (hop : ∀ j < N, op j = GateOp.and ∨ op j = GateOp.or)
    (hback : ∀ j < N, a j < n + j ∧ b j < n + j)
    (havoid : ∀ j < N, j ∉ insert h M →
      (a j < n ∨ a j - n ∉ M) ∧ (b j < n ∨ b j - n ∉ M))
    (hval : ∀ j < N, j ∉ insert h M → ∀ x,
      V x (n + j) = (op j).eval [V x (a j), V x (b j)])
    (block : ∀ (gs : List Gate) (m : ℕ → ℕ), Ok n gs → Maps n h M gs m V →
      ∃ (hs : List Gate) (o : ℕ), Ok n (gs ++ hs) ∧ hs.length ≤ r ∧
        o < n + (gs ++ hs).length ∧
        (∀ x : Fin n → Bool, (run (gs ++ hs) (List.ofFn x)).getD o false = V x (n + h)) ∧
        dc n F (gs ++ hs) ≤ dc n F gs) :
    ∀ p, p ≤ N → ∃ (gs : List Gate) (m : ℕ → ℕ),
      Ok n gs ∧ Maps n p M gs m V ∧ Keeps n p (insert h M) gs m op ∧
      gs.length + ((Finset.range p).filter (· ∈ insert h M)).card ≤
        p + (if h < p then r else 0) ∧
      dc n F gs ≤ ((Finset.range p).filter fun j => j ∉ insert h M ∧ op j = GateOp.and ∧
        ∃ x : Fin n → Bool, V x (n + j) = true ∧ F x = false).card := by
  classical
  intro p
  induction p with
  | zero =>
    intro _
    refine ⟨[], id, ?_, ?_, ?_, ?_, ?_⟩
    · intro j hj; simp at hj
    · intro w hw _
      refine ⟨by simpa using hw, fun x => ?_⟩
      exact (hin x w (by simpa using hw)).symm
    · intro j hj; omega
    · simp
    · simp [dc]
  | succ p ih =>
    intro hpN
    obtain ⟨gs, m, hok, hm, hkeep, hlen, hdirty⟩ := ih (by omega)
    have hp : p < N := by omega
    suffices hh : ∃ (hs : List Gate) (o : ℕ), Ok n (gs ++ hs) ∧
        (p ∉ M → o < n + (gs ++ hs).length) ∧
        (p ∉ M → ∀ x : Fin n → Bool,
          (run (gs ++ hs) (List.ofFn x)).getD o false = V x (n + p)) ∧
        (p ∉ insert h M → ∃ k < (gs ++ hs).length, o = n + k ∧
          ((gs ++ hs).getD k ⟨GateOp.or, []⟩).op = op p) ∧
        hs.length + (if p ∈ insert h M then 1 else 0) ≤ 1 + (if p = h then r else 0) ∧
        dc n F (gs ++ hs) ≤ dc n F gs +
          if p ∉ insert h M ∧ op p = GateOp.and ∧
            ∃ x : Fin n → Bool, V x (n + p) = true ∧ F x = false then 1 else 0 by
      obtain ⟨hs, o, h1, h2, h3, h4, h5, h6⟩ := hh
      refine ⟨gs ++ hs, Function.update m (n + p) o, h1, ?_, ?_, ?_, ?_⟩
      · intro w hw hvalid
        by_cases hwp : w = n + p
        · subst w
          rw [Function.update_self]
          have hpm : p ∉ M := by simpa using hvalid
          exact ⟨h2 hpm, h3 hpm⟩
        · rw [Function.update_of_ne hwp]
          obtain ⟨hbound, hvalue⟩ := hm w (by omega) hvalid
          refine ⟨by simp; omega, fun x => ?_⟩
          rw [run_prefix gs hs _ _ (by simpa using hbound)]
          exact hvalue x
      · intro j hj hjDel
        by_cases hjp : j = p
        · subst j
          rw [Function.update_self]
          exact h4 hjDel
        · obtain ⟨k, hk, heq, hopk⟩ := hkeep j (by omega) hjDel
          refine ⟨k, by simp; omega, ?_, ?_⟩
          · rw [Function.update_of_ne (by omega)]
            exact heq
          · rw [append_getD _ _ _ _ hk]
            exact hopk
      · rw [List.length_append, Finset.range_add_one, Finset.filter_insert]
        by_cases hDel : p ∈ insert h M
        · rw [ite_eq_left hDel, Finset.card_insert_of_notMem (by simp)]
          rw [ite_eq_left hDel] at h5
          by_cases hph : p = h
          · subst p
            simp only [lt_self_iff_false, ↓reduceIte, Nat.lt_succ_self] at hlen ⊢
            simp only [↓reduceIte] at h5
            omega
          · have hei : (h < p + 1) ↔ h < p := by omega
            simp only [ite_eq_right hph] at h5
            simp only [hei]
            omega
        · rw [ite_eq_right hDel]
          rw [ite_eq_right hDel] at h5
          have hph : p ≠ h := by intro heq; apply hDel; simp [heq]
          have hei : (h < p + 1) ↔ h < p := by omega
          simp only [ite_eq_right hph] at h5
          simp only [hei]
          omega
      · rw [Finset.range_add_one, Finset.filter_insert]
        split_ifs at h6 ⊢ with hj
        · rw [Finset.card_insert_of_notMem (by simp)]
          omega
        · omega
    by_cases hpM : p ∈ M
    · refine ⟨[], 0, by simpa using hok, fun h => False.elim (h hpM),
        fun h => False.elim (h hpM), ?_, ?_, ?_⟩
      · intro h; exact False.elim (h (Finset.mem_insert_of_mem hpM))
      · have hph : p ≠ h := by intro heq; subst p; exact hnotM hpM
        simp [hpM, hph]
      · simp [hpM]
    by_cases hph : p = h
    · subst p
      obtain ⟨hs, o, hb1, hb2, hb3, hb4, hb5⟩ := block gs m hok hm
      refine ⟨hs, o, hb1, fun _ => hb3, fun _ => hb4, ?_, ?_, ?_⟩
      · simp
      · simp; omega
      · simpa using hb5
    have hpDel : p ∉ insert h M := by simp [hph, hpM]
    obtain ⟨hap, hbp⟩ := hback p hp
    obtain ⟨haValid, hbValid⟩ := havoid p hp hpDel
    obtain ⟨haBound, haValue⟩ := hm (a p) hap haValid
    obtain ⟨hbBound, hbValue⟩ := hm (b p) hbp hbValid
    let g : Gate := ⟨op p, [m (a p), m (b p)]⟩
    have hnew : ∀ x : Fin n → Bool,
        (run (gs ++ [g]) (List.ofFn x)).getD (n + gs.length) false = V x (n + p) := by
      intro x
      rw [next_value, haValue x, hbValue x]
      exact (hval p hp hpDel x).symm
    refine ⟨[g], n + gs.length, ok_snoc hok (hop p hp) haBound hbBound, ?_, ?_, ?_, ?_, ?_⟩
    · intro _; simp
    · intro _; exact hnew
    · intro _
      refine ⟨gs.length, by simp, rfl, ?_⟩
      simp [g, List.getD_eq_getElem?_getD]
    · simp [hpDel, hph]
    · have hd := dc_snoc n F gs g
      have heq : (g.op = GateOp.and ∧ ∃ x : Fin n → Bool,
          (run (gs ++ [g]) (List.ofFn x)).getD (n + gs.length) false = true ∧ F x = false) ↔
          (p ∉ insert h M ∧ op p = GateOp.and ∧
            ∃ x : Fin n → Bool, V x (n + p) = true ∧ F x = false) := by
        simp only [g, hnew, hpDel, not_false_eq_true, true_and]
      rw [if_congr heq rfl rfl] at hd
      exact hd

lemma ok_isAO2 (n : ℕ) (gs : List Gate) (out : ℕ) (hok : Ok n gs) :
    PEqualNP.TopForm.IsAO2 n ⟨gs, out⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    obtain ⟨o, a, b, heq, hop, _, _⟩ := hok j hj
    simpa [heq] using hop
  · intro j hj w hw
    obtain ⟨o, a, b, heq, _, ha, hb⟩ := hok j hj
    have hgate : gateAt (⟨gs, out⟩ : Circuit) j = ⟨o, [a, b]⟩ := by
      change gs.getD j _ = _
      rw [List.getD_eq_getElem _ _ hj]
      exact heq
    rw [hgate] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact ha
    · exact hb
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    obtain ⟨o, a, b, heq, _, _, _⟩ := hok j hj
    simp [heq]

lemma isAO2_ok (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C) :
    Ok n C.gates := by
  intro j hj
  have heq : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
  have hmem : gateAt C j ∈ C.gates := by rw [heq]; exact List.getElem_mem hj
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (hC.2.2 _ hmem)
  refine ⟨(gateAt C j).op, a, b, ?_, hC.1 _ hmem, ?_, ?_⟩
  · rw [← heq]
    have hgate : ∀ (g : Gate), g.inputs = [a, b] → g = ⟨g.op, [a, b]⟩ := by
      intro g hg; cases g; cases hg; rfl
    exact hgate _ hab
  · exact hC.2.1 j hj a (by rw [hab]; simp)
  · exact hC.2.1 j hj b (by rw [hab]; simp)

lemma dc_eq_junk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (gs : List Gate) (out : ℕ) :
    dc n (graphFun G ∅) gs = (PEqualNP.TopForm.junk G ⟨gs, out⟩).card := by
  classical
  unfold dc PEqualNP.TopForm.junk PEqualNP.TopForm.gatesWhere
  congr 1
  apply Finset.filter_congr
  intro j hj
  have hj' : j < gs.length := Finset.mem_range.mp hj
  simp only [PEqualNP.CleanedNonEdge.IsDirtyAnd, PEqualNP.CleanedNonEdge.IsDirty,
    gateAt, PEqualNP.EdgeOwnership.gateVal, Circuit.wires, run, hj', true_and]

lemma dc_append_clean (n : ℕ) (F : (Fin n → Bool) → Bool) (gs hs : List Gate)
    (hclean : ∀ j, gs.length ≤ j → j < (gs ++ hs).length →
      ((gs ++ hs).getD j ⟨GateOp.or, []⟩).op = GateOp.and →
      ∀ x : Fin n → Bool,
        (run (gs ++ hs) (List.ofFn x)).getD (n + j) false = true → F x = true) :
    dc n F (gs ++ hs) = dc n F gs := by
  classical
  unfold dc
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  by_cases hj : j < gs.length
  · have hlong : j < (gs ++ hs).length := by simp; omega
    rw [append_getD _ _ _ _ hj]
    simp only [hj, hlong, true_and]
    refine and_congr_right fun _ => exists_congr fun x => ?_
    rw [run_prefix gs hs _ _ (by simp; omega)]
  · constructor
    · rintro ⟨hjlong, hop, x, hx, hFx⟩
      have ht := hclean j (by omega) hjlong hop x hx
      rw [hFx] at ht
      cases ht
    · rintro ⟨hj', _⟩
      exact False.elim (hj hj')

lemma kept_dirty {n p h : ℕ} {M : Finset ℕ} {gs : List Gate} {m : ℕ → ℕ}
    {V : (Fin n → Bool) → ℕ → Bool} {op : ℕ → GateOp}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (out : ℕ)
    (hm : Maps n p M gs m V) (hk : Keeps n p (insert h M) gs m op)
    (g : ℕ) (hg : g < p) (hgkeep : g ∉ insert h M) (hop : op g = GateOp.and)
    (hdirty : ∃ x : Fin n → Bool, V x (n + g) = true ∧ graphFun G ∅ x = false) :
    (PEqualNP.TopForm.junk G ⟨gs, out⟩).Nonempty := by
  classical
  obtain ⟨k, hklen, hmap, hkop⟩ := hk g hg hgkeep
  have hgM : g ∉ M := fun hm' => hgkeep (Finset.mem_insert_of_mem hm')
  have hv := (hm (n + g) (by omega) (Or.inr (by simpa using hgM))).2
  obtain ⟨x, hx, hFx⟩ := hdirty
  refine ⟨k, ?_⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr hklen, ?_⟩
  change (gs.getD k ⟨GateOp.or, []⟩).op = GateOp.and ∧
    k < gs.length ∧ ∃ x, (run gs (List.ofFn x)).getD (n + k) false = true ∧ graphFun G ∅ x = false
  refine ⟨?_, hklen, x, ?_, hFx⟩
  · exact hkop.trans hop
  · rw [← hmap, hv x]
    exact hx

open Classical in
lemma splice_complete
    (n N h r : ℕ) (M : Finset ℕ) (hnotM : h ∉ M) (hh : h < N)
    (hM : M ⊆ Finset.range N) (out : ℕ) (hout : out < n + N)
    (houtM : out < n ∨ out - n ∉ M)
    (op : ℕ → GateOp) (a b : ℕ → ℕ)
    (V : (Fin n → Bool) → ℕ → Bool)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hin : ∀ x w, w < n → V x w = (List.ofFn x).getD w false)
    (hop : ∀ j < N, op j = GateOp.and ∨ op j = GateOp.or)
    (hback : ∀ j < N, a j < n + j ∧ b j < n + j)
    (havoid : ∀ j < N, j ∉ insert h M →
      (a j < n ∨ a j - n ∉ M) ∧ (b j < n ∨ b j - n ∉ M))
    (hval : ∀ j < N, j ∉ insert h M → ∀ x,
      V x (n + j) = (op j).eval [V x (a j), V x (b j)])
    (houtput : ∀ x, V x out = graphFun G ∅ x)
    (block : ∀ (gs : List Gate) (m : ℕ → ℕ), Ok n gs → Maps n h M gs m V →
      ∃ (hs : List Gate) (o : ℕ), Ok n (gs ++ hs) ∧ hs.length ≤ r ∧
        o < n + (gs ++ hs).length ∧
        (∀ x : Fin n → Bool, (run (gs ++ hs) (List.ofFn x)).getD o false = V x (n + h)) ∧
        dc n (graphFun G ∅) (gs ++ hs) ≤ dc n (graphFun G ∅) gs) :
    ∃ (D : Circuit) (m : ℕ → ℕ), PEqualNP.TopForm.IsAO2 n D ∧
      circuitFun n D = graphFun G ∅ ∧
      Maps n N M D.gates m V ∧ Keeps n N (insert h M) D.gates m op ∧
      D.size + M.card + 1 ≤ N + r ∧
      (PEqualNP.TopForm.junk G D).card ≤ ((Finset.range N).filter fun j =>
        j ∉ insert h M ∧ op j = GateOp.and ∧
        ∃ x : Fin n → Bool, V x (n + j) = true ∧ graphFun G ∅ x = false).card := by
  obtain ⟨gs, m, hok, hm, hk, hlen, hdc⟩ :=
    build_splice n N h r M hnotM op a b V (graphFun G ∅)
      hin hop hback havoid hval block N le_rfl
  have hDel : ((Finset.range N).filter (· ∈ insert h M)) = insert h M := by
    ext j
    simp only [Finset.mem_filter]
    constructor
    · exact And.right
    · intro hj
      refine ⟨?_, hj⟩
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact Finset.mem_range.mpr hh
      · exact hM hj
  rw [hDel, Finset.card_insert_of_notMem hnotM, ite_eq_left hh] at hlen
  refine ⟨⟨gs, m out⟩, m, ok_isAO2 n gs (m out) hok, ?_, hm, hk, ?_, ?_⟩
  · funext x
    exact ((hm out hout houtM).2 x).trans (houtput x)
  · simpa only [Circuit.size, Nat.add_assoc] using hlen
  · rwa [dc_eq_junk G gs (m out)] at hdc

end Splice

namespace Alias

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.Outside.L_meta_5012_aux.Splice

lemma ok_set_alias (n : ℕ) (gs : List Gate) (hok : Ok n gs)
    (j w : ℕ) (hw : w < n + j) :
    Ok n (gs.set j ⟨GateOp.or, [w, w]⟩) := by
  intro k hk
  have hk' : k < gs.length := by simpa using hk
  by_cases hkj : k = j
  · subst k
    refine ⟨GateOp.or, w, w, ?_, Or.inr rfl, hw, hw⟩
    simp
  · obtain ⟨o, a, b, hg, ho, ha, hb⟩ := hok k hk'
    refine ⟨o, a, b, ?_, ho, ha, hb⟩
    rw [List.getElem_set_ne (fun h => hkj h.symm)]
    exact hg

lemma gate_pair {n : ℕ} {C : Circuit} (h : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
    C.gates[j] = gateAt C j ∧ (gateAt C j).inputs = [opnd C j 0, opnd C j 1] ∧
    opnd C j 0 < n + j ∧ opnd C j 1 < n + j ∧
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) := by
  have e : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
  have hm : gateAt C j ∈ C.gates := by rw [e]; exact List.getElem_mem hj
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (h.2.2 _ hm)
  have ea : opnd C j 0 = a := by unfold opnd; rw [hab]; rfl
  have eb : opnd C j 1 = b := by unfold opnd; rw [hab]; rfl
  refine ⟨e.symm, by rw [hab, ea, eb], ?_, ?_, h.1 _ hm⟩
  · rw [ea]; exact h.2.1 j hj a (by rw [hab]; simp)
  · rw [eb]; exact h.2.1 j hj b (by rw [hab]; simp)

lemma gate_value {n : ℕ} {C : Circuit} (h : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length)
    (x : Fin n → Bool) :
    (run C.gates (List.ofFn x)).getD (n + j) false =
      (gateAt C j).op.eval [(run C.gates (List.ofFn x)).getD (opnd C j 0) false,
        (run C.gates (List.ofFn x)).getD (opnd C j 1) false] := by
  obtain ⟨heq, hin, ha, hb, _⟩ := gate_pair h hj
  have hh := run_gate C.gates (List.ofFn x) j hj
  rw [List.length_ofFn, heq, hin] at hh
  simpa [ha, hb] using hh

lemma least_output_valid {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (j : ℕ) (hj : j < C.gates.length) :
    C.output < n + C.gates.length := by
  by_contra hn
  have hfalse : ∀ x : Fin n → Bool, circuitFun n C x = false := by
    intro x
    apply List.getD_eq_default
    change (run C.gates (List.ofFn x)).length ≤ C.output
    rw [run_length, List.length_ofFn]
    omega
  let D : Circuit := ⟨[], n⟩
  have hD : IsAO2 n D := by simp [IsAO2, PEqualNP.EdgeOwnership.AndOrOnly, ReadsBack, D]
  have hDF : circuitFun n D = graphFun G ∅ := by
    funext x
    rw [← hL.2.1, hfalse]
    simp [D, circuitFun, Circuit.eval, Circuit.wires, List.getD_eq_getElem?_getD]
  have hs := hL.2.2 D hD hDF
  simp only [Circuit.size, D, List.length_nil] at hs
  omega

lemma least_patch_alias_impossible {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : IsLeastAO G C) (e w : ℕ) (he : e < C.gates.length) (hw : w < n + e)
    (hpatch : circuitFun n ⟨C.gates.set e ⟨GateOp.or, [w, w]⟩, C.output⟩ = graphFun G ∅) :
    False := by
  classical
  let P : Circuit := ⟨C.gates.set e ⟨GateOp.or, [w, w]⟩, C.output⟩
  have hP : IsAO2 n P := ok_isAO2 n P.gates P.output
    (ok_set_alias n C.gates (isAO2_ok n C hL.1) e w hw)
  have hlen : P.gates.length = C.gates.length := List.length_set
  have heP : e < P.gates.length := by rwa [hlen]
  let V : (Fin n → Bool) → ℕ → Bool := fun x v => (run P.gates (List.ofFn x)).getD v false
  let op : ℕ → GateOp := fun j => (gateAt P j).op
  let a : ℕ → ℕ := fun j => opnd P j 0
  let b : ℕ → ℕ := fun j => opnd P j 1
  have hin : ∀ x v, v < n → V x v = (List.ofFn x).getD v false := by
    intro x v hv
    exact run_input P.gates (List.ofFn x) v (by simpa using hv)
  have hop : ∀ j < P.gates.length, op j = GateOp.and ∨ op j = GateOp.or := by
    intro j hj
    exact (gate_pair hP hj).2.2.2.2
  have hback : ∀ j < P.gates.length, a j < n + j ∧ b j < n + j := by
    intro j hj
    exact ⟨(gate_pair hP hj).2.2.1, (gate_pair hP hj).2.2.2.1⟩
  have hval : ∀ j < P.gates.length, j ∉ insert e (∅ : Finset ℕ) → ∀ x,
      V x (n + j) = (op j).eval [V x (a j), V x (b j)] := by
    intro j hj _ x
    exact gate_value hP hj x
  have hgate : gateAt P e = ⟨GateOp.or, [w, w]⟩ := by
    simp [P, gateAt, List.getD_eq_getElem?_getD, he]
  have hVe : ∀ x, V x (n + e) = V x w := by
    intro x
    have hh := gate_value hP heP x
    simpa [V, opnd, hgate, GateOp.eval] using hh
  obtain ⟨D, m, hDAO, hDF, _, _, hsize, _⟩ :=
    splice_complete n P.gates.length e 0 ∅ (by simp) heP (by simp) P.output
      (by simpa only [P, List.length_set] using least_output_valid G C hL e he)
      (Or.inr (by simp)) op a b V G hin hop hback (by simp) hval
      (fun x => congrFun hpatch x) (by
        intro gs m hok hm
        have hmW := hm w hw (Or.inr (by simp))
        refine ⟨[], m w, by simpa using hok, by simp, by simpa using hmW.1, ?_, by simp⟩
        intro x
        simpa using (hmW.2 x).trans (hVe x).symm)
  have hmin := hL.2.2 D hDAO hDF
  simp only [Finset.card_empty, Nat.add_zero, hlen] at hsize
  change C.gates.length ≤ D.gates.length at hmin
  change D.gates.length + 1 ≤ C.gates.length at hsize
  omega

end Alias

namespace Mixed

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

lemma no_singleton_guard_for_mixed_junk {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (s : Fin n → Bool) (hcol : ∀ a b, G.Adj a b → s a ≠ s b)
    (hL : IsLeastAO G C) (hTop : TopForm G C)
    (g h : ℕ) (hJ : junk G C = {g, h}) (hind : ¬ InCone n C g h)
    (hmix : ∀ c : Bool, gateVal n C h (monoInput s c) = true)
    (u : Fin n)
    (hcenter : ∀ a b, G.Adj a b → gateVal n C g (pairInput a b) = true →
      pairInput a b u = true) : False := by
  obtain ⟨e, w, heh, hecone, heor, hemix, hw, hunder, hagree⟩ :=
    earliest_mixed_or_alias G C s hcol hL.1 hTop g h hJ hind hmix u hcenter
  have hhJ : h ∈ junk G C := by simp [hJ]
  have hh := (mem_junk.mp hhJ).1
  have he : e < C.gates.length := by omega
  have hcritical : ∀ a b, G.Adj a b →
      circuitFun n (patch C e off) (pairInput a b) = false →
      gateVal n C g (pairInput a b) = true := by
    intro a b hab hlost
    exact MixedOr.mixed_lost_edge_uses_other G C s hcol hL.1 hTop hL.2.1
      g h hJ hmix e hemix off a b hab hlost
  have hpatch := alias_patch_computes_from_guard G C hL.1 hL.2.1 e w g he hw
    hunder hcritical hagree
  exact Alias.least_patch_alias_impossible G C hL e w he hw hpatch

lemma no_singleton_factor_for_mixed_junk {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (s : Fin n → Bool) (hcol : ∀ a b, G.Adj a b → s a ≠ s b)
    (hL : IsLeastAO G C) (hTop : TopForm G C)
    (g h : ℕ) (hJ : junk G C = {g, h}) (hind : ¬ InCone n C g h)
    (hmix : ∀ c : Bool, gateVal n C h (monoInput s c) = true)
    (u : Fin n) (K : Finset (Fin n))
    (hfactor : ∀ x : Fin n → Bool,
      gateVal n C g x = (x u && decide (∃ v ∈ K, x v = true))) : False := by
  apply no_singleton_guard_for_mixed_junk G C s hcol hL hTop g h hJ hind hmix u
  intro a b _ hg
  rw [hfactor, Bool.and_eq_true] at hg
  exact hg.1

end Mixed


namespace ORCompiler

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

lemma run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

lemma getD_lt (l : List Bool) (b : Bool) (t : Nat) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

lemma run_prefix (gs hs : List Gate) (x : List Bool) (i : Nat) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_lt _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

lemma run_input (gs : List Gate) (x : List Bool) (i : Nat) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

lemma ofFn_getD {n : Nat} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD i.val false = x i := by
  simp [List.getD_eq_getElem?_getD]

def OrOk (n : Nat) (gs : List Gate) : Prop :=
  ∀ j (hj : j < gs.length), ∃ a b, gs[j] = ⟨GateOp.or, [a, b]⟩ ∧
    a < n + j ∧ b < n + j

lemma orOk_nil (n : Nat) : OrOk n [] := by
  intro j hj
  simp at hj

lemma orOk_snoc {n : Nat} {gs : List Gate} (h : OrOk n gs) {a b : Nat}
    (ha : a < n + gs.length) (hb : b < n + gs.length) :
    OrOk n (gs ++ [⟨GateOp.or, [a, b]⟩]) := by
  intro j hj
  by_cases hlt : j < gs.length
  · rw [List.getElem_append_left hlt]
    exact h j hlt
  · have : j = gs.length := by simp at hj; omega
    subst this
    exact ⟨a, b, by simp, ha, hb⟩


lemma run_new_or (n : Nat) (gs : List Gate) (x : Fin n → Bool) (a b : Nat) :
    (run (gs ++ [⟨GateOp.or, [a, b]⟩]) (List.ofFn x)).getD (n + gs.length) false =
      ((run gs (List.ofFn x)).getD a false || (run gs (List.ofFn x)).getD b false) := by
  rw [run_snoc]
  have hlen : n + gs.length = (run gs (List.ofFn x)).length := by simp [run_length]
  rw [hlen, getD_at]
  simp [GateOp.eval]

lemma append_chain (n : Nat) : ∀ l : List (Fin n),
    ∀ gs : List Gate, OrOk n gs → ∀ seed : Nat, seed < n + gs.length →
    ∃ hs : List Gate, ∃ out : Nat,
      OrOk n (gs ++ hs) ∧ hs.length = l.length ∧ out < n + (gs ++ hs).length ∧
      ∀ x : Fin n → Bool,
        (run (gs ++ hs) (List.ofFn x)).getD out false =
          ((run gs (List.ofFn x)).getD seed false || l.any fun i => x i) := by
  intro l
  induction l with
  | nil =>
    intro gs hgs seed hseed
    exact ⟨[], seed, by simpa using hgs, rfl, by simpa using hseed, by simp⟩
  | cons t l ih =>
    intro gs hgs seed hseed
    let g : Gate := ⟨GateOp.or, [seed, t.val]⟩
    have ht : t.val < n + gs.length := by have := t.isLt; omega
    obtain ⟨hs, out, hok, hlen, hout, heval⟩ := ih (gs ++ [g])
      (orOk_snoc hgs hseed ht) (n + gs.length) (by simp)
    refine ⟨g :: hs, out, by simpa [List.append_assoc] using hok,
      by simp [hlen], by simpa [List.append_assoc] using hout, ?_⟩
    intro x
    have he : gs ++ g :: hs = (gs ++ [g]) ++ hs := by simp
    rw [he, heval]
    rw [show g = ⟨GateOp.or, [seed, t.val]⟩ from rfl, run_new_or]
    rw [run_input gs (List.ofFn x) t.val (by simp), ofFn_getD]
    simp [Bool.or_assoc]

def hit {n : Nat} (S : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∃ i ∈ S, x i = true)

def Realizes {n : Nat} (gs : List Gate) (out : Nat) (S : Finset (Fin n)) : Prop :=
  out < n + gs.length ∧
    ∀ x : Fin n → Bool, (run gs (List.ofFn x)).getD out false = hit S x

lemma hit_union {n : Nat} (S T : Finset (Fin n)) (x : Fin n → Bool) :
    (hit S x || hit T x) = hit (S ∪ T) x := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, hit, decide_eq_true_eq, Finset.mem_union]
  aesop

lemma hit_list {n : Nat} (S : Finset (Fin n)) (x : Fin n → Bool) :
    S.toList.any (fun i => x i) = hit S x := by
  apply Bool.eq_iff_iff.mpr
  simp [hit, List.any_eq_true]

lemma realizes_prefix {n : Nat} {gs : List Gate} {out : Nat} {S : Finset (Fin n)}
    (h : Realizes gs out S) (hs : List Gate) : Realizes (gs ++ hs) out S := by
  refine ⟨by have := h.1; simp; omega, ?_⟩
  intro x
  rw [run_prefix gs hs (List.ofFn x) out (by simpa using h.1), h.2]

lemma append_support {n : Nat} (gs : List Gate) (hok : OrOk n gs)
    (seed : Nat) (S T : Finset (Fin n)) (hseed : Realizes gs seed S) :
    ∃ hs : List Gate, ∃ out : Nat, OrOk n (gs ++ hs) ∧ hs.length = T.card ∧
      Realizes (gs ++ hs) out (S ∪ T) := by
  obtain ⟨hs, out, h1, h2, h3, h4⟩ := append_chain n T.toList gs hok seed hseed.1
  refine ⟨hs, out, h1, by simpa using h2, h3, ?_⟩
  intro x
  rw [h4, hseed.2, hit_list, hit_union]

lemma make_support {n : Nat} (gs : List Gate) (hok : OrOk n gs)
    (S : Finset (Fin n)) (hne : S.Nonempty) :
    ∃ hs : List Gate, ∃ out : Nat, OrOk n (gs ++ hs) ∧ hs.length + 1 = S.card ∧
      Realizes (gs ++ hs) out S := by
  obtain ⟨i, hi⟩ := hne
  have hseed : Realizes gs i.val {i} := by
    refine ⟨by have := i.isLt; omega, ?_⟩
    intro x
    rw [run_input gs (List.ofFn x) i.val (by simp), ofFn_getD]
    simp [hit]
  obtain ⟨hs, out, h1, h2, h3⟩ := append_support gs hok i.val {i} (S.erase i) hseed
  have hset : {i} ∪ S.erase i = S := by
    ext j
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_erase]
    by_cases hj : j = i
    · simp [hj, hi]
    · simp [hj]
  refine ⟨hs, out, h1, ?_, by simpa [hset] using h3⟩
  rw [h2]
  exact Finset.card_erase_add_one hi

lemma two_supports_disjoint {n : Nat} (S T : Finset (Fin n))
    (hS : S.Nonempty) (hT : T.Nonempty) (hd : Disjoint S T) :
    ∃ gs : List Gate, ∃ outS outT : Nat,
      OrOk n gs ∧ gs.length + 2 = (S ∪ T).card ∧
      Realizes gs outS S ∧ Realizes gs outT T := by
  obtain ⟨gs, outS, hok, hlen, hrealS⟩ := make_support [] (orOk_nil n) S hS
  simp only [List.nil_append] at hok hrealS
  obtain ⟨hs, outT, hok', hlen', hrealT⟩ := make_support gs hok T hT
  refine ⟨gs ++ hs, outS, outT, hok', ?_, realizes_prefix hrealS hs, hrealT⟩
  have hc := Finset.card_union_of_disjoint hd
  simp only [List.length_append]
  omega

lemma two_supports_common {n : Nat} (S T : Finset (Fin n))
    (hI : (S ∩ T).Nonempty) :
    ∃ gs : List Gate, ∃ outS outT : Nat,
      OrOk n gs ∧ gs.length + 1 = (S ∪ T).card ∧
      Realizes gs outS S ∧ Realizes gs outT T := by
  let I := S ∩ T
  have hIS : I ⊆ S := Finset.inter_subset_left
  have hIT : I ⊆ T := Finset.inter_subset_right
  have hSI : I ∪ S \ I = S := Finset.union_sdiff_of_subset hIS
  have hTI : I ∪ T \ I = T := Finset.union_sdiff_of_subset hIT
  obtain ⟨gs, outI, hok, hlen, hrealI⟩ := make_support [] (orOk_nil n) I hI
  simp only [List.nil_append] at hok hrealI
  obtain ⟨hs, outS, hokS, hlenS, hrealS⟩ := append_support gs hok outI I (S \ I) hrealI
  rw [hSI] at hrealS
  obtain ⟨ks, outT, hokT, hlenT, hrealT⟩ :=
    append_support (gs ++ hs) hokS outI I (T \ I) (realizes_prefix hrealI hs)
  rw [hTI] at hrealT
  refine ⟨(gs ++ hs) ++ ks, outS, outT, hokT, ?_,
    realizes_prefix hrealS ks, hrealT⟩
  have hcS := Finset.card_sdiff_add_card_eq_card hIS
  have hcT := Finset.card_sdiff_add_card_eq_card hIT
  have hcU := Finset.card_union_add_card_inter S T
  change (S ∪ T).card + I.card = S.card + T.card at hcU
  simp only [List.length_append]
  omega

lemma two_supports {n : Nat} (S T : Finset (Fin n))
    (hS : S.Nonempty) (hT : T.Nonempty) :
    ∃ gs : List Gate, ∃ outS outT : Nat,
      OrOk n gs ∧ gs.length + (if Disjoint S T then 2 else 1) = (S ∪ T).card ∧
      Realizes gs outS S ∧ Realizes gs outT T := by
  by_cases hd : Disjoint S T
  · simpa [hd] using two_supports_disjoint S T hS hT hd
  · have hI : (S ∩ T).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      exact fun he => hd (Finset.disjoint_iff_inter_eq_empty.mpr he)
    simpa [hd] using two_supports_common S T hI






end ORCompiler

namespace ORBlock

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_5012_aux

lemma append_or_ok {n : Nat} (gs hs : List Gate) (hgs : Splice.Ok n gs)
    (hhs : ORCompiler.OrOk (n + gs.length) hs) : Splice.Ok n (gs ++ hs) := by
  intro j hj
  by_cases hjg : j < gs.length
  · rw [List.getElem_append_left hjg]
    exact hgs j hjg
  · have hjh : j - gs.length < hs.length := by simp at hj; omega
    rw [List.getElem_append_right (by omega)]
    obtain ⟨a, b, heq, ha, hb⟩ := hhs (j - gs.length) hjh
    exact ⟨GateOp.or, a, b, heq, Or.inr rfl, by omega, by omega⟩

lemma append_or_dc {n : Nat} (F : (Fin n → Bool) → Bool) (gs hs : List Gate)
    (hhs : ORCompiler.OrOk (n + gs.length) hs) :
    Splice.dc n F (gs ++ hs) = Splice.dc n F gs := by
  apply Splice.dc_append_clean
  intro j hjg hj hop
  have hjh : j - gs.length < hs.length := by simp at hj; omega
  have heq : (gs ++ hs).getD j ⟨GateOp.or, []⟩ = hs[j - gs.length] := by
    rw [List.getD_eq_getElem _ _ hj, List.getElem_append_right hjg]
  obtain ⟨a, b, hg, _, _⟩ := hhs (j - gs.length) hjh
  rw [heq, hg] at hop
  cases hop

def prefixVal {n : Nat} (gs : List Gate) (x : Fin n → Bool) :
    Fin (n + gs.length) → Bool :=
  fun i => (Splice.run gs (List.ofFn x)).getD i.val false

lemma prefixVal_ofFn {n : Nat} (gs : List Gate) (x : Fin n → Bool) :
    List.ofFn (prefixVal gs x) = Splice.run gs (List.ofFn x) := by
  apply List.ext_getElem
  · simp [Splice.run_length]
  · intro i hi hj
    simp only [List.getElem_ofFn, prefixVal]
    exact List.getD_eq_getElem _ _ hj

lemma run_compiled_append {n : Nat} (gs hs : List Gate) (x : Fin n → Bool) :
    Splice.run (gs ++ hs) (List.ofFn x) = ORCompiler.run hs (List.ofFn (prefixVal gs x)) := by
  rw [prefixVal_ofFn]
  simp [Splice.run, ORCompiler.run, List.foldl_append]

lemma mapped_or_cost {q k : Nat} (S T : Finset (Fin q)) (f : Fin q → Fin k)
    (size : Nat)
    (hsize : size + (if Disjoint (S.image f) (T.image f) then 2 else 1) =
      (S.image f ∪ T.image f).card) :
    size + (if Disjoint S T then 2 else 1) ≤ (S ∪ T).card := by
  have himage : (S.image f ∪ T.image f).card ≤ (S ∪ T).card := by
    rw [← Finset.image_union]
    exact Finset.card_image_le
  by_cases hd : Disjoint S T
  · by_cases hd' : Disjoint (S.image f) (T.image f)
    · simp only [hd, hd', ↓reduceIte] at hsize ⊢
      omega
    · have hne : ¬ Set.InjOn f (↑(S ∪ T) : Set (Fin q)) := by
        intro hinj
        apply hd'
        rw [Finset.disjoint_left]
        intro z hzS hzT
        obtain ⟨u, hu, huf⟩ := Finset.mem_image.mp hzS
        obtain ⟨v, hv, hvf⟩ := Finset.mem_image.mp hzT
        have huv : u = v := hinj (Finset.mem_union_left _ hu)
          (Finset.mem_union_right _ hv) (huf.trans hvf.symm)
        exact Finset.disjoint_left.mp hd hu (huv ▸ hv)
      have hcardne : (S.image f ∪ T.image f).card ≠ (S ∪ T).card := by
        intro heq
        apply hne
        apply Finset.card_image_iff.mp
        simpa [Finset.image_union] using heq
      simp only [hd, hd', ↓reduceIte] at hsize ⊢
      omega
  · simp only [hd, ↓reduceIte]
    split_ifs at hsize <;> omega

def boundaryHit {n q : Nat} (gs : List Gate) (wire : Fin q → Nat)
    (S : Finset (Fin q)) (x : Fin n → Bool) : Bool :=
  decide (∃ i ∈ S, (Splice.run gs (List.ofFn x)).getD (wire i) false = true)

lemma two_boundary_outputs {n q : Nat} (gs : List Gate) (hok : Splice.Ok n gs)
    (wire : Fin q → Nat) (hwire : ∀ i, wire i < n + gs.length)
    (S T : Finset (Fin q)) (hS : S.Nonempty) (hT : T.Nonempty)
    (F : (Fin n → Bool) → Bool) :
    ∃ hs : List Gate, ∃ outS outT : Nat,
      Splice.Ok n (gs ++ hs) ∧
      hs.length + (if Disjoint S T then 2 else 1) ≤ (S ∪ T).card ∧
      outS < n + (gs ++ hs).length ∧ outT < n + (gs ++ hs).length ∧
      (∀ x : Fin n → Bool,
        (Splice.run (gs ++ hs) (List.ofFn x)).getD outS false = boundaryHit gs wire S x ∧
        (Splice.run (gs ++ hs) (List.ofFn x)).getD outT false = boundaryHit gs wire T x) ∧
      Splice.dc n F (gs ++ hs) = Splice.dc n F gs := by
  let f : Fin q → Fin (n + gs.length) := fun i => ⟨wire i, hwire i⟩
  obtain ⟨hs, outS, outT, hOr, hsize, hrealS, hrealT⟩ :=
    ORCompiler.two_supports (S.image f) (T.image f) (hS.image f) (hT.image f)
  refine ⟨hs, outS, outT, append_or_ok gs hs hok hOr,
    mapped_or_cost S T f hs.length hsize, ?_, ?_, ?_, append_or_dc F gs hs hOr⟩
  · have := hrealS.1
    simp only [List.length_append]
    omega
  · have := hrealT.1
    simp only [List.length_append]
    omega
  · intro x
    rw [run_compiled_append]
    rw [hrealS.2, hrealT.2]
    constructor <;> apply Bool.eq_iff_iff.mpr <;>
      simp only [ORCompiler.hit, boundaryHit, decide_eq_true_eq, Finset.mem_image, prefixVal, f] <;>
      aesop

lemma two_mapped_outputs {n q p : Nat} (M : Finset Nat)
    (gs : List Gate) (m : Nat → Nat) (V : (Fin n → Bool) → Nat → Bool)
    (hok : Splice.Ok n gs) (hm : Splice.Maps n p M gs m V)
    (wire : Fin q → Nat) (hwire : ∀ i, wire i < n + p)
    (hkeep : ∀ i, wire i < n ∨ wire i - n ∉ M)
    (S T : Finset (Fin q)) (hS : S.Nonempty) (hT : T.Nonempty)
    (F : (Fin n → Bool) → Bool) :
    ∃ hs : List Gate, ∃ outS outT : Nat,
      Splice.Ok n (gs ++ hs) ∧
      hs.length + (if Disjoint S T then 2 else 1) ≤ (S ∪ T).card ∧
      outS < n + (gs ++ hs).length ∧ outT < n + (gs ++ hs).length ∧
      (∀ x : Fin n → Bool,
        (Splice.run (gs ++ hs) (List.ofFn x)).getD outS false =
          decide (∃ i ∈ S, V x (wire i) = true) ∧
        (Splice.run (gs ++ hs) (List.ofFn x)).getD outT false =
          decide (∃ i ∈ T, V x (wire i) = true)) ∧
      Splice.dc n F (gs ++ hs) = Splice.dc n F gs := by
  have hw : ∀ i, m (wire i) < n + gs.length := fun i =>
    (hm (wire i) (hwire i) (hkeep i)).1
  obtain ⟨hs, outS, outT, hok', hsize, hSlt, hTlt, hval, hdc⟩ :=
    two_boundary_outputs gs hok (fun i => m (wire i)) hw S T hS hT F
  refine ⟨hs, outS, outT, hok', hsize, hSlt, hTlt, ?_, hdc⟩
  intro x
  have hsem : ∀ i, (Splice.run gs (List.ofFn x)).getD (m (wire i)) false = V x (wire i) :=
    fun i => (hm (wire i) (hwire i) (hkeep i)).2 x
  simpa only [boundaryHit, hsem] using hval x

end ORBlock


namespace FactorColors

lemma opposite_colors {α : Type} [DecidableEq α] (s : α → Bool)
    (A B : Finset α) (hA : A.Nonempty) (hB : B.Nonempty)
    (hmono : ∀ c : Bool, ¬ ((∃ a ∈ A, s a = c) ∧ ∃ b ∈ B, s b = c)) :
    ((∀ a ∈ A, s a = false) ∧ ∀ b ∈ B, s b = true) ∨
      ((∀ a ∈ A, s a = true) ∧ ∀ b ∈ B, s b = false) := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  cases hsa : s a with
  | false =>
    have hBtrue : ∀ v ∈ B, s v = true := by
      intro v hv
      cases hsv : s v with
      | true => rfl
      | false => exact False.elim (hmono false ⟨⟨a, ha, hsa⟩, ⟨v, hv, hsv⟩⟩)
    refine Or.inl ⟨?_, hBtrue⟩
    intro u hu
    cases hsu : s u with
    | false => rfl
    | true => exact False.elim (hmono true ⟨⟨u, hu, hsu⟩, ⟨b, hb, hBtrue b hb⟩⟩)
  | true =>
    have hBfalse : ∀ v ∈ B, s v = false := by
      intro v hv
      cases hsv : s v with
      | false => rfl
      | true => exact False.elim (hmono true ⟨⟨a, ha, hsa⟩, ⟨v, hv, hsv⟩⟩)
    refine Or.inr ⟨?_, hBfalse⟩
    intro u hu
    cases hsu : s u with
    | true => rfl
    | false => exact False.elim (hmono false ⟨⟨u, hu, hsu⟩, ⟨b, hb, hBfalse b hb⟩⟩)



end FactorColors

namespace MixedAlias

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
  PEqualNP.Outside.L_meta_5012_aux.Mixed

lemma alias_bit {n : ℕ} {C : Circuit} {j w : ℕ}
    (hj : j < C.gates.length) (hw : w < n + j) (x : Fin n → Bool) :
    gateBit (earlierWires C j (List.ofFn x)) ⟨GateOp.or, [w, w]⟩ =
      wireVal n C w x := by
  simp only [gateBit, GateOp.eval, List.map_cons, List.map_nil, List.any_cons,
    List.any_nil, id_eq, Bool.or_false, Bool.or_self]
  exact earlier_read_eq_wireVal hj hw x

lemma guarded_alias_computes {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (hAO : IsAO2 n C) (hTop : TopForm G C) (hF : circuitFun n C = graphFun G ∅)
    (g h : ℕ) (hJ : junk G C = {g, h})
    (hmix : ∀ c : Bool, gateVal n C h (monoInput s c) = true)
    (w : ℕ) (hw : w < n + h)
    (preserve : ∀ x : Fin n → Bool,
      gateVal n (patch C h ⟨GateOp.or, [w, w]⟩) g x = gateVal n C g x)
    (guarded : ∀ x : Fin n → Bool, gateVal n C g x = true →
      wireVal n C w x = true → graphFun G ∅ x = true)
    (gedges : ∀ u v, G.Adj u v → gateVal n C g (pairInput u v) = true →
      wireVal n C w (pairInput u v) = true) :
    circuitFun n (patch C h ⟨GateOp.or, [w, w]⟩) = graphFun G ∅ := by
  have hhJ : h ∈ junk G C := by simp [hJ]
  have hh := (mem_junk.mp hhJ).1
  have hback : ∀ i ∈ (⟨GateOp.or, [w, w]⟩ : Gate).inputs, i < n + h := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hi
    subst i
    exact hw
  have hguard : ∀ x : Fin n → Bool, gateVal n C g x = true →
      gateBit (earlierWires C h (List.ofFn x)) ⟨GateOp.or, [w, w]⟩ = true →
      graphFun G ∅ x = true := by
    intro x hxg hxw
    rw [alias_bit hh hw] at hxw
    exact guarded x hxg hxw
  have hcritical : ∀ u v, G.Adj u v →
      circuitFun n (patch C h off) (pairInput u v) = false →
      gateBit (earlierWires C h (List.ofFn (pairInput u v)))
        ⟨GateOp.or, [w, w]⟩ = true := by
    intro u v huv hlost
    rw [alias_bit hh hw]
    exact gedges u v huv
      (lost_edge_uses_other G C s hcol hAO hTop hF g h hJ hmix off u v huv hlost)
  exact (guarded_or_repair G C s hcol hAO hTop hF g h hJ hmix
    ⟨GateOp.or, [w, w]⟩ rfl rfl hback preserve hguard hcritical).2.1

lemma no_guarded_alias {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (hL : IsLeastAO G C) (hTop : TopForm G C)
    (g h : ℕ) (hJ : junk G C = {g, h})
    (hmix : ∀ c : Bool, gateVal n C h (monoInput s c) = true)
    (w : ℕ) (hw : w < n + h)
    (preserve : ∀ x : Fin n → Bool,
      gateVal n (patch C h ⟨GateOp.or, [w, w]⟩) g x = gateVal n C g x)
    (guarded : ∀ x : Fin n → Bool, gateVal n C g x = true →
      wireVal n C w x = true → graphFun G ∅ x = true)
    (gedges : ∀ u v, G.Adj u v → gateVal n C g (pairInput u v) = true →
      wireVal n C w (pairInput u v) = true) : False := by
  have hhJ : h ∈ junk G C := by simp [hJ]
  apply Alias.least_patch_alias_impossible G C hL h w (mem_junk.mp hhJ).1 hw
  exact guarded_alias_computes G C s hcol hL.1 hTop hL.2.1 g h hJ hmix
    w hw preserve guarded gedges


lemma no_guarded_independent_alias {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (hL : IsLeastAO G C) (hTop : TopForm G C)
    (g h : ℕ) (hne : h ≠ g) (hcone : ¬ InCone n C h g) (hJ : junk G C = {g, h})
    (hmix : ∀ c : Bool, gateVal n C h (monoInput s c) = true)
    (w : ℕ) (hw : w < n + h)
    (guarded : ∀ x : Fin n → Bool, gateVal n C g x = true →
      wireVal n C w x = true → graphFun G ∅ x = true)
    (gedges : ∀ u v, G.Adj u v → gateVal n C g (pairInput u v) = true →
      wireVal n C w (pairInput u v) = true) : False := by
  have hgJ : g ∈ junk G C := by simp [hJ]
  exact no_guarded_alias G C s hcol hL hTop g h hJ hmix w hw
    (gate_unchanged_of_notCone hL.1 h g _ (mem_junk.mp hgJ).1 hne hcone) guarded gedges

end MixedAlias


namespace PrivacyGeometry

open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover

lemma pair_graph_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v : Fin n) : graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq, pairInput]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · simp at hab
    · exact hab
    · exact hab.symm
    · simp at hab
  · intro huv
    exact ⟨u, v, huv, by simp, by simp⟩

lemma common_neighbor_unique {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) {a b u v : Fin n} (hab : a ≠ b)
    (hau : G.Adj a u) (hbu : G.Adj b u) (hav : G.Adj a v) (hbv : G.Adj b v) :
    u = v := by
  exact Finset.card_le_one.mp (h4 a b hab) u (by simp [hau, hbu])
    v (by simp [hav, hbv])

lemma clean_filter_left {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B E : Finset (Fin n))
    (hclean : ∀ x : Fin n → Bool,
      (∃ a ∈ A, x a = true) → (∃ b ∈ B, x b = true) →
      (∃ e ∈ E, x e = true) → graphFun G ∅ x = true)
    {a : Fin n} (ha : a ∈ A ∩ E) : ∀ b ∈ B, G.Adj a b := by
  intro b hb
  exact (pair_graph_iff G a b).mp (hclean (pairInput a b)
    ⟨a, (Finset.mem_inter.mp ha).1, by simp [pairInput]⟩
    ⟨b, hb, by simp [pairInput]⟩
    ⟨a, (Finset.mem_inter.mp ha).2, by simp [pairInput]⟩)

lemma clean_filter_right {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B E : Finset (Fin n))
    (hclean : ∀ x : Fin n → Bool,
      (∃ a ∈ A, x a = true) → (∃ b ∈ B, x b = true) →
      (∃ e ∈ E, x e = true) → graphFun G ∅ x = true)
    {b : Fin n} (hb : b ∈ B ∩ E) : ∀ a ∈ A, G.Adj a b := by
  intro a ha
  exact (clean_filter_left G B A E (fun x hB hA hE => hclean x hA hB hE) hb a ha).symm

lemma filter_side_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (A B E : Finset (Fin n)) (hB : 2 ≤ B.card)
    (hclean : ∀ x : Fin n → Bool,
      (∃ a ∈ A, x a = true) → (∃ b ∈ B, x b = true) →
      (∃ e ∈ E, x e = true) → graphFun G ∅ x = true) :
    (A ∩ E).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro a ha c hc
  by_contra hac
  have hsub : B ⊆ Finset.univ.filter (fun w => G.Adj a w ∧ G.Adj c w) := by
    intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨clean_filter_left G A B E hclean ha b hb,
      clean_filter_left G A B E hclean hc b hb⟩
  have := Finset.card_le_card hsub
  have := h4 a c hac
  omega

lemma two_filter_centers_cover {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (A B E : Finset (Fin n))
    (hclean : ∀ x : Fin n → Bool,
      (∃ a ∈ A, x a = true) → (∃ b ∈ B, x b = true) →
      (∃ e ∈ E, x e = true) → graphFun G ∅ x = true)
    {a b : Fin n} (ha : a ∈ A ∩ E) (hb : b ∈ B ∩ E) :
    ∀ u ∈ A, ∀ v ∈ B, G.Adj u v → u = a ∨ v = b := by
  intro u hu v hv huv
  by_cases hua : u = a
  · exact Or.inl hua
  · exact Or.inr (common_neighbor_unique G h4 hua huv
      (clean_filter_left G A B E hclean ha v hv)
      (clean_filter_right G A B E hclean hb u hu)
      (clean_filter_left G A B E hclean ha b (Finset.mem_inter.mp hb).1))

lemma clean_filter_dichotomy {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (A B E : Finset (Fin n)) (hA : 2 ≤ A.card) (hB : 2 ≤ B.card)
    (hclean : ∀ x : Fin n → Bool,
      (∃ a ∈ A, x a = true) → (∃ b ∈ B, x b = true) →
      (∃ e ∈ E, x e = true) → graphFun G ∅ x = true) :
    ((A ∪ B) ∩ E).card ≤ 1 ∨
      (∀ u ∈ A, ∀ v ∈ B, G.Adj u v → u ∈ E ∨ v ∈ E) := by
  classical
  by_cases hleft : (A ∩ E).Nonempty
  · by_cases hright : (B ∩ E).Nonempty
    · obtain ⟨a, ha⟩ := hleft
      obtain ⟨b, hb⟩ := hright
      right
      intro u hu v hv huv
      rcases two_filter_centers_cover G h4 A B E hclean ha hb u hu v hv huv with rfl | rfl
      · exact Or.inl (Finset.mem_inter.mp ha).2
      · exact Or.inr (Finset.mem_inter.mp hb).2
    · left
      have hEq : (A ∪ B) ∩ E = A ∩ E := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_union]
        constructor
        · rintro ⟨hx | hx, he⟩
          · exact ⟨hx, he⟩
          · exact False.elim (hright ⟨x, Finset.mem_inter.mpr ⟨hx, he⟩⟩)
        · rintro ⟨hx, he⟩
          exact ⟨Or.inl hx, he⟩
      rw [hEq]
      exact filter_side_card G h4 A B E hB hclean
  · left
    have hEq : (A ∪ B) ∩ E = B ∩ E := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨hx | hx, he⟩
        · exact False.elim (hleft ⟨x, Finset.mem_inter.mpr ⟨hx, he⟩⟩)
        · exact ⟨hx, he⟩
      · rintro ⟨hx, he⟩
        exact ⟨Or.inr hx, he⟩
    rw [hEq]
    exact filter_side_card G h4 B A E hA (fun x hB hA hE => hclean x hA hB hE)

lemma singleton_filter_alias {n : ℕ} (A B E : Finset (Fin n))
    (hcard : ((A ∪ B) ∩ E).card ≤ 1)
    {z : Fin n} (hz : z ∈ (A ∪ B) ∩ E) :
    ∀ u ∈ A, ∀ v ∈ B, (u ∈ E ∨ v ∈ E) ↔ (u = z ∨ v = z) := by
  intro u hu v hv
  constructor
  · rintro (he | he)
    · exact Or.inl (Finset.card_le_one.mp hcard u
        (Finset.mem_inter.mpr ⟨Finset.mem_union.mpr (Or.inl hu), he⟩) z hz)
    · exact Or.inr (Finset.card_le_one.mp hcard v
        (Finset.mem_inter.mpr ⟨Finset.mem_union.mpr (Or.inr hv), he⟩) z hz)
  · rintro (rfl | rfl)
    · exact Or.inl (Finset.mem_inter.mp hz).2
    · exact Or.inr (Finset.mem_inter.mp hz).2

lemma pair_factors_iff {n : ℕ} (A B : Finset (Fin n)) (hd : Disjoint A B)
    (u v : Fin n) :
    ((∃ a ∈ A, pairInput u v a = true) ∧ (∃ b ∈ B, pairInput u v b = true)) ↔
      (u ∈ A ∧ v ∈ B) ∨ (v ∈ A ∧ u ∈ B) := by
  simp only [pairInput, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨a, ha, rfl | rfl⟩, ⟨b, hb, rfl | rfl⟩⟩
    · exact False.elim (Finset.disjoint_left.mp hd ha hb)
    · exact Or.inl ⟨ha, hb⟩
    · exact Or.inr ⟨ha, hb⟩
    · exact False.elim (Finset.disjoint_left.mp hd ha hb)
  · rintro (⟨hu, hv⟩ | ⟨hv, hu⟩)
    · exact ⟨⟨u, hu, Or.inl rfl⟩, ⟨v, hv, Or.inr rfl⟩⟩
    · exact ⟨⟨v, hv, Or.inr rfl⟩, ⟨u, hu, Or.inl rfl⟩⟩

lemma clean_filter_trichotomy {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (A B E : Finset (Fin n)) (hA : 2 ≤ A.card) (hB : 2 ≤ B.card)
    (hd : Disjoint A B)
    (hclean : ∀ x : Fin n → Bool,
      (∃ a ∈ A, x a = true) → (∃ b ∈ B, x b = true) →
      (∃ e ∈ E, x e = true) → graphFun G ∅ x = true)
    (f q : (Fin n → Bool) → Bool)
    (hf : ∀ x, f x = true ↔ (∃ a ∈ A, x a = true) ∧ (∃ b ∈ B, x b = true))
    (hq : ∀ x, q x = true ↔ ∃ e ∈ E, x e = true) :
    (∀ u v, G.Adj u v → f (pairInput u v) = true → q (pairInput u v) = false) ∨
    (∃ z ∈ E, ∀ u v, G.Adj u v → f (pairInput u v) = true →
      q (pairInput u v) = pairInput u v z) ∨
    (∀ u v, G.Adj u v → f (pairInput u v) = true → q (pairInput u v) = true) := by
  classical
  have hqpair (u v : Fin n) : q (pairInput u v) = true ↔ u ∈ E ∨ v ∈ E := by
    rw [hq]
    simp only [pairInput, decide_eq_true_eq]
    constructor
    · rintro ⟨e, he, rfl | rfl⟩
      · exact Or.inl he
      · exact Or.inr he
    · rintro (hu | hv)
      · exact ⟨u, hu, Or.inl rfl⟩
      · exact ⟨v, hv, Or.inr rfl⟩
  rcases clean_filter_dichotomy G h4 A B E hA hB hclean with hcard | hall
  · by_cases hne : ((A ∪ B) ∩ E).Nonempty
    · obtain ⟨z, hz⟩ := hne
      right
      left
      refine ⟨z, (Finset.mem_inter.mp hz).2, ?_⟩
      intro u v huv hfg
      have hmem := (pair_factors_iff A B hd u v).mp ((hf _).mp hfg)
      have hequiv : q (pairInput u v) = true ↔ pairInput u v z = true := by
        rw [hqpair]
        simp only [pairInput, decide_eq_true_eq]
        rcases hmem with ⟨hu, hv⟩ | ⟨hv, hu⟩
        · simpa only [eq_comm] using singleton_filter_alias A B E hcard hz u hu v hv
        · simpa only [eq_comm, or_comm] using singleton_filter_alias A B E hcard hz v hv u hu
      exact Bool.eq_iff_iff.mpr hequiv
    · left
      intro u v huv hfg
      have hmem := (pair_factors_iff A B hd u v).mp ((hf _).mp hfg)
      cases heq : q (pairInput u v) with
      | false => rfl
      | true =>
        have he := (hqpair u v).mp heq
        exfalso
        apply hne
        rcases hmem with ⟨hu, hv⟩ | ⟨hv, hu⟩
        · rcases he with he | he
          · exact ⟨u, by simp [hu, he]⟩
          · exact ⟨v, by simp [hv, he]⟩
        · rcases he with he | he
          · exact ⟨u, by simp [hu, he]⟩
          · exact ⟨v, by simp [hv, he]⟩
  · right
    right
    intro u v huv hfg
    apply (hqpair u v).mpr
    rcases (pair_factors_iff A B hd u v).mp ((hf _).mp hfg) with ⟨hu, hv⟩ | ⟨hv, hu⟩
    · exact hall u hu v hv huv
    · exact (hall v hv u hu huv.symm).symm

end PrivacyGeometry

namespace Mixed

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

lemma independent_junk_raw_factors {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hAO : IsAO2 n C) (hTop : TopForm G C)
    (g h : ℕ) (hJ : junk G C = {g, h}) (hind : ¬ InCone n C g h) :
    ∀ b : Fin 2, (side (n := n) C h b).Nonempty ∧
      ∀ x : Fin n → Bool, wireVal n C (opnd C h b) x =
        decide (∃ u ∈ side (n := n) C h b, x u = true) := by
  have hhJ : h ∈ junk G C := by simp [hJ]
  have hh := (mem_junk.mp hhJ).1
  have hnoand := no_and_below_independent_junk hTop hJ hind
  intro b
  have hins := operand_inside hAO hh (Or.inl rfl) _ (opnd_mem hAO hh b)
  have hp := inside_pure_or hAO hnoand hins
  refine ⟨?_, hp⟩
  have hall := wire_all_true hAO (opnd C h b) (by have := opnd_lt hAO hh b; omega)
  change wireVal n C (opnd C h b) (fun _ => true) = true at hall
  rw [hp] at hall
  simpa [Finset.Nonempty, side] using hall

lemma independent_junk_raw_value {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hAO : IsAO2 n C) (hTop : TopForm G C)
    (g h : ℕ) (hJ : junk G C = {g, h}) (hind : ¬ InCone n C g h)
    (x : Fin n → Bool) :
    gateVal n C h x =
      (decide (∃ u ∈ side (n := n) C h 0, x u = true) &&
       decide (∃ v ∈ side (n := n) C h 1, x v = true)) := by
  have hhJ : h ∈ junk G C := by simp [hJ]
  have hh := (mem_junk.mp hhJ).1
  have hhand := (mem_junk.mp hhJ).2.1
  have hf := independent_junk_raw_factors G C hAO hTop g h hJ hind
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · intro hv
    have h0 := and_true_operands hAO hh hhand x hv 0
    have h1 := and_true_operands hAO hh hhand x hv 1
    change wireVal n C (opnd C h 0) x = true at h0
    change wireVal n C (opnd C h 1) x = true at h1
    rw [(hf 0).2 x] at h0
    rw [(hf 1).2 x] at h1
    exact ⟨of_decide_eq_true h0, of_decide_eq_true h1⟩
  · rintro ⟨h0, h1⟩
    apply and_two hAO hh hhand 0 x
    · change wireVal n C (opnd C h 0) x = true
      rw [(hf 0).2 x]
      exact decide_eq_true h0
    · change wireVal n C (opnd C h 1) x = true
      rw [(hf 1).2 x]
      exact decide_eq_true h1

lemma no_mixed_or_clean_guard {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (s : Fin n → Bool) (hcol : ∀ a b, G.Adj a b → s a ≠ s b)
    (h4 : NoFourCycle G) (hL : IsLeastAO G C) (hTop : TopForm G C)
    (g h : ℕ) (hne : h ≠ g) (hind : ¬ InCone n C h g)
    (hJ : junk G C = {g, h})
    (hmix : ∀ c : Bool, gateVal n C h (monoInput s c) = true)
    (e : ℕ) (heh : e < h) (heor : (gateAt C e).op = GateOp.or)
    (hemix : ∀ c : Bool, gateVal n C e (monoInput s c) = true)
    (A B E : Finset (Fin n)) (hA : 2 ≤ A.card) (hB : 2 ≤ B.card) (hd : Disjoint A B)
    (hf : ∀ x : Fin n → Bool, gateVal n C g x = true ↔
      (∃ a ∈ A, x a = true) ∧ (∃ b ∈ B, x b = true))
    (hq : ∀ x : Fin n → Bool, gateVal n C e x = true ↔ ∃ v ∈ E, x v = true)
    (hclean : ∀ x : Fin n → Bool, gateVal n C g x = true →
      gateVal n C e x = true → graphFun G ∅ x = true) : False := by
  classical
  have hhJ : h ∈ junk G C := by simp [hJ]
  have hh := (mem_junk.mp hhJ).1
  have he : e < C.gates.length := by omega
  have hrawclean : ∀ x : Fin n → Bool,
      (∃ a ∈ A, x a = true) → (∃ b ∈ B, x b = true) →
      (∃ v ∈ E, x v = true) → graphFun G ∅ x = true := by
    intro x hax hbx hex
    exact hclean x ((hf x).mpr ⟨hax, hbx⟩) ((hq x).mpr hex)
  have hcritical : ∀ a b, G.Adj a b →
      circuitFun n (patch C e off) (pairInput a b) = false →
      gateVal n C g (pairInput a b) = true := by
    intro a b hab hlost
    exact MixedOr.mixed_lost_edge_uses_other G C s hcol hL.1 hTop hL.2.1
      g h hJ hmix e hemix off a b hab hlost
  rcases PrivacyGeometry.clean_filter_trichotomy G h4 A B E hA hB hd hrawclean
    (gateVal n C g) (gateVal n C e) hf hq with hzero | hsingle | hall
  · let w := opnd C e 0
    have hw : w < n + e := opnd_lt hL.1 he 0
    have hunder : ∀ x : Fin n → Bool, wireVal n C w x = true → gateVal n C e x = true := by
      intro x hx
      exact W_or n C x e he heor w (opnd_mem hL.1 he 0) hw hx
    have hpatch := (alias_patch_computes_of_critical G C hL.1 hL.2.1 e w he hw hunder ?_).2.1
    · exact Alias.least_patch_alias_impossible G C hL e w he hw hpatch
    · intro a b hab hlost
      have hg := hcritical a b hab hlost
      have hetrue : gateVal n C e (pairInput a b) = true := by
        apply lost_input_gate_true hL.1 he (pairInput a b) _ hlost
        rw [hL.2.1]
        exact (graph_true G (pairInput a b)).mpr
          ⟨a, b, hab, by simp [pairInput], by simp [pairInput]⟩
      rw [hzero a b hab hg] at hetrue
      cases hetrue
  · obtain ⟨z, hzE, hzeq⟩ := hsingle
    have hw : z.val < n + e := by have := z.isLt; omega
    have hunder : ∀ x : Fin n → Bool, wireVal n C z.val x = true → gateVal n C e x = true := by
      intro x hx
      apply (hq x).mpr
      refine ⟨z, hzE, ?_⟩
      change W n C x z.val = true at hx
      rwa [W_input n C x z.val z.isLt] at hx
    have hagree : ∀ a b, G.Adj a b → gateVal n C g (pairInput a b) = true →
        wireVal n C z.val (pairInput a b) = gateVal n C e (pairInput a b) := by
      intro a b hab hg
      change W n C (pairInput a b) z.val = _
      rw [W_input n C _ z.val z.isLt]
      exact (hzeq a b hab hg).symm
    have hpatch := alias_patch_computes_from_guard G C hL.1 hL.2.1 e z.val g he hw
      hunder hcritical hagree
    exact Alias.least_patch_alias_impossible G C hL e z.val he hw hpatch
  · apply MixedAlias.no_guarded_independent_alias G C s hcol hL hTop g h hne hind hJ hmix
      (n + e) (by omega)
    · intro x hg heval
      exact hclean x hg heval
    · intro a b hab hg
      exact hall a b hab hg

lemma no_clean_top_reading_mixed_or {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (s : Fin n → Bool) (hcol : ∀ a b, G.Adj a b → s a ≠ s b)
    (h4 : NoFourCycle G) (hL : IsLeastAO G C) (hTop : TopForm G C)
    (g h : ℕ) (hne : h ≠ g) (hind : ¬ InCone n C h g)
    (hJ : junk G C = {g, h})
    (hmix : ∀ c : Bool, gateVal n C h (monoInput s c) = true)
    (e : ℕ) (heh : e < h) (heor : (gateAt C e).op = GateOp.or)
    (hemix : ∀ c : Bool, gateVal n C e (monoInput s c) = true)
    (A B E : Finset (Fin n)) (hA : 2 ≤ A.card) (hB : 2 ≤ B.card) (hd : Disjoint A B)
    (hf : ∀ x : Fin n → Bool, gateVal n C g x = true ↔
      (∃ a ∈ A, x a = true) ∧ (∃ b ∈ B, x b = true))
    (hq : ∀ x : Fin n → Bool, gateVal n C e x = true ↔ ∃ v ∈ E, x v = true)
    (t : ℕ) (ht : t < C.gates.length) (htand : (gateAt C t).op = GateOp.and)
    (htbelow : BelowF G C t) (b : Fin 2) (hreach : OrReaches n C (opnd C t b) e) : False := by
  apply no_mixed_or_clean_guard G C s hcol h4 hL hTop g h hne hind hJ hmix
    e heh heor hemix A B E hA hB hd hf hq
  intro x hg he
  have hother := (MixedOr.opposite_of_mixed_gate G C s hcol hL.1 hTop g h hJ hmix
    e hemix t ht htand htbelow b hreach).2.2.2 x
  have hb : W n C x (opnd C t b) = true := reach_up n C x _ e hreach he
  have hbother : W n C x (opnd C t (1 - b)) = true := by
    change wireVal n C (opnd C t (1 - b)) x = true
    rw [hother]
    exact hg
  exact htbelow x (and_two hL.1 ht htand b x hb hbother)

lemma mixed_or_below_junk_no_top_reader {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (s : Fin n → Bool) (hcol : ∀ a b, G.Adj a b → s a ≠ s b)
    (h4 : NoFourCycle G) (hL : IsLeastAO G C) (hTop : TopForm G C)
    (g h : ℕ) (hne : h ≠ g) (hindgh : ¬ InCone n C g h) (hindhg : ¬ InCone n C h g)
    (hJ : junk G C = {g, h})
    (hmix : ∀ c : Bool, gateVal n C h (monoInput s c) = true)
    (hA : 2 ≤ (side (n := n) C g 0).card) (hB : 2 ≤ (side (n := n) C g 1).card)
    (hd : Disjoint (side (n := n) C g 0) (side (n := n) C g 1))
    (e : ℕ) (hecone : InCone n C e h)
    (hemix : ∀ c : Bool, gateVal n C e (monoInput s c) = true)
    (t : ℕ) (ht : t < C.gates.length) (htand : (gateAt C t).op = GateOp.and)
    (htbelow : BelowF G C t) (b : Fin 2) (hreach : OrReaches n C (opnd C t b) e) : False := by
  have hhJ : h ∈ junk G C := by simp [hJ]
  have hh := (mem_junk.mp hhJ).1
  have heh : e < h := inCone_lt n C h e hecone
  have he : e < C.gates.length := by omega
  have hnoand := no_and_below_independent_junk hTop hJ hindgh
  have heor : (gateAt C e).op = GateOp.or := by
    rcases hL.1.1 _ (gateAt_mem' C e he) with hea | heo
    · exact False.elim (hnoand e hecone hea)
    · exact heo
  have hJswap : junk G C = {h, g} := by simpa [Finset.pair_comm] using hJ
  have hfg := independent_junk_raw_value G C hL.1 hTop h g hJswap hindhg
  have hf : ∀ x : Fin n → Bool, gateVal n C g x = true ↔
      (∃ a ∈ side (n := n) C g 0, x a = true) ∧
      (∃ b ∈ side (n := n) C g 1, x b = true) := by
    intro x
    rw [hfg x]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
  have heval := inside_pure_or hL.1 hnoand
    (show InsideWire n C h (n + e) from Or.inr ⟨e, rfl, hecone⟩)
  have hq : ∀ x : Fin n → Bool, gateVal n C e x = true ↔
      ∃ v ∈ orIn n C (n + e), x v = true := by
    intro x
    change wireVal n C (n + e) x = true ↔ _
    rw [heval x]
    simp only [decide_eq_true_eq]
  exact no_clean_top_reading_mixed_or G C s hcol h4 hL hTop g h hne hindhg hJ hmix
    e heh heor hemix (side (n := n) C g 0) (side (n := n) C g 1) (orIn n C (n + e))
    hA hB hd hf hq t ht htand htbelow b hreach

lemma pure_junk_no_mixed_operand {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (s : Fin n → Bool) (hAO : IsAO2 n C) (hTop : TopForm G C)
    (g h : ℕ) (hJ : junk G C = {g, h}) (hind : ¬ InCone n C h g)
    (gzero : ∀ c : Bool, gateVal n C g (monoInput s c) = false)
    (e : ℕ) (emix : ∀ c : Bool, gateVal n C e (monoInput s c) = true)
    (b : Fin 2) : ¬ OrReaches n C (opnd C g b) e := by
  intro hr
  have hgJ : g ∈ junk G C := by simp [hJ]
  have hg := (mem_junk.mp hgJ).1
  have hgand := (mem_junk.mp hgJ).2.1
  have hJswap : junk G C = {h, g} := by simpa [Finset.pair_comm] using hJ
  obtain ⟨u, hu⟩ := (independent_junk_raw_factors G C hAO hTop h g hJswap hind (1 - b)).1
  have hb : W n C (monoInput s (s u)) (opnd C g b) = true :=
    reach_up n C _ _ e hr (emix (s u))
  have ho : W n C (monoInput s (s u)) (opnd C g (1 - b)) = true :=
    side_val n C _ g (1 - b) u hu (by simp [monoInput])
  have hgv := and_two hAO hg hgand b _ hb ho
  rw [gzero] at hgv
  cases hgv

lemma mixed_or_and_reader_eq_junk {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (s : Fin n → Bool) (hcol : ∀ a b, G.Adj a b → s a ≠ s b)
    (h4 : NoFourCycle G) (hL : IsLeastAO G C) (hTop : TopForm G C)
    (g h : ℕ) (hne : h ≠ g) (hindgh : ¬ InCone n C g h) (hindhg : ¬ InCone n C h g)
    (hJ : junk G C = {g, h})
    (hmix : ∀ c : Bool, gateVal n C h (monoInput s c) = true)
    (gzero : ∀ c : Bool, gateVal n C g (monoInput s c) = false)
    (hA : 2 ≤ (side (n := n) C g 0).card) (hB : 2 ≤ (side (n := n) C g 1).card)
    (hd : Disjoint (side (n := n) C g 0) (side (n := n) C g 1))
    (e : ℕ) (hecone : InCone n C e h)
    (hemix : ∀ c : Bool, gateVal n C e (monoInput s c) = true)
    (t : ℕ) (ht : t < C.gates.length) (htand : (gateAt C t).op = GateOp.and)
    (hread : n + e ∈ (gateAt C t).inputs) : t = h := by
  have heh := inCone_lt n C h e hecone
  have hh : h < C.gates.length := (inCone_iff n C e h).mp hecone |>.1
  have he : e < C.gates.length := by omega
  obtain ⟨b, hb⟩ := (mem_inputs_iff_opnd hL.1 ht (n + e)).mp hread
  have hr : OrReaches n C (opnd C t b) e := by
    rw [hb]
    exact orReach_self n C e he
  rcases and_junk_or_below (G := G) ht htand with htJ | htbelow
  · have htg : t = g ∨ t = h := by simpa [hJ] using htJ
    rcases htg with htg | hth
    · subst t
      exact False.elim (pure_junk_no_mixed_operand G C s hL.1 hTop g h hJ hindhg gzero e hemix b hr)
    · exact hth
  · exact False.elim (mixed_or_below_junk_no_top_reader G C s hcol h4 hL hTop
      g h hne hindgh hindhg hJ hmix hA hB hd e hecone hemix t ht htand htbelow b hr)

end Mixed

namespace Mixed

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

lemma least_gate_reaches_output {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : IsLeastAO G C) (e : ℕ) (he : e < C.gates.length) :
    C.output = n + e ∨ ∃ k, C.output = n + k ∧ InCone n C e k := by
  classical
  by_contra hn
  push Not at hn
  obtain ⟨houtne, houtcone⟩ := hn
  let w := opnd C e 0
  have hw : w < n + e := opnd_lt hL.1 he 0
  apply Alias.least_patch_alias_impossible G C hL e w he hw
  funext x
  change W n (patch C e (copyGate w)) x C.output = graphFun G ∅ x
  rw [wire_unchanged_away hL.1 e (copyGate w) x C.output
    (Alias.least_output_valid G C hL e he) houtne houtcone]
  change circuitFun n C x = graphFun G ∅ x
  exact congrFun hL.2.1 x

lemma cone_first_and {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (e : ℕ) : ∀ k, InCone n C e k →
      OrReaches n C (n + k) e ∨
      ∃ t, t < C.gates.length ∧ (gateAt C t).op = GateOp.and ∧
        ∃ b : Fin 2, OrReaches n C (opnd C t b) e := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hcone
    obtain ⟨hk, p, hpk, hpin, hep⟩ := (inCone_iff n C e k).mp hcone
    have hr : OrReaches n C (n + p) e ∨
        ∃ t, t < C.gates.length ∧ (gateAt C t).op = GateOp.and ∧
          ∃ b : Fin 2, OrReaches n C (opnd C t b) e := by
      rcases hep with hep | hep
      · subst p
        exact Or.inl (orReach_self n C e (by omega))
      · exact ih p hpk hep
    rcases hr with hr | hr
    · rcases hAO.1 _ (gateAt_mem' C k hk) with hand | hor
      · right
        obtain ⟨b, hb⟩ := (mem_inputs_iff_opnd hAO hk (n + p)).mp hpin
        refine ⟨k, hk, hand, b, ?_⟩
        rwa [hb]
      · exact Or.inl (orReach_trans n C k hk hor (n + p) hpin (by omega) e hr)
    · exact Or.inr hr

lemma orReach_indices_trans {n : ℕ} {C : Circuit} (a b c : ℕ)
    (ha : a < C.gates.length)
    (hab : OrReaches n C (n + a) b) (hbc : OrReaches n C (n + b) c) :
    OrReaches n C (n + a) c := by
  have go : ∀ a, a < C.gates.length →
      b ∈ (orSets n C).getD a [] → c ∈ (orSets n C).getD a [] := by
    intro a
    induction a using Nat.strong_induction_on with
    | _ a ih =>
      intro ha hmem
      rcases (orSets_mem_iff n C a b ha).mp hmem with heq | ⟨hor, w, hw, hwn, hwa, hbw⟩
      · subst a
        simpa using hbc.2
      · apply (orSets_mem_iff n C a c ha).mpr
        right
        exact ⟨hor, w, hw, hwn, hwa, ih (w - n) (by omega) (by omega) hbw⟩
  refine ⟨by omega, ?_⟩
  simpa using go a ha (by simpa using hab.2)

lemma orReach_wire_trans {n : ℕ} {C : Circuit} {w b c : ℕ}
    (hwb : OrReaches n C w b) (hbc : OrReaches n C (n + b) c) :
    OrReaches n C w c := by
  have hwn := hwb.1
  have hlen : (orSets n C).length = C.gates.length := by
    unfold orSets; rw [orFold_length]; simp
  have hwk : w - n < C.gates.length := by
    by_contra hn
    have hmem := hwb.2
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (show (orSets n C).length ≤ w - n by omega)] at hmem
    simp at hmem
  have heq : n + (w - n) = w := by omega
  have hh := orReach_indices_trans (w - n) b c hwk (by rwa [heq]) hbc
  rwa [heq] at hh

lemma mixed_or_and_user_eq_junk {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (s : Fin n → Bool) (hcol : ∀ a b, G.Adj a b → s a ≠ s b)
    (h4 : NoFourCycle G) (hL : IsLeastAO G C) (hTop : TopForm G C)
    (g h : ℕ) (hne : h ≠ g) (hindgh : ¬ InCone n C g h) (hindhg : ¬ InCone n C h g)
    (hJ : junk G C = {g, h})
    (hmix : ∀ c : Bool, gateVal n C h (monoInput s c) = true)
    (gzero : ∀ c : Bool, gateVal n C g (monoInput s c) = false)
    (hA : 2 ≤ (side (n := n) C g 0).card) (hB : 2 ≤ (side (n := n) C g 1).card)
    (hd : Disjoint (side (n := n) C g 0) (side (n := n) C g 1))
    (e : ℕ) (hecone : InCone n C e h)
    (hemix : ∀ c : Bool, gateVal n C e (monoInput s c) = true)
    (t : ℕ) (ht : t < C.gates.length) (htand : (gateAt C t).op = GateOp.and)
    (b : Fin 2) (hread : OrReaches n C (opnd C t b) e) : t = h := by
  rcases and_junk_or_below (G := G) ht htand with htJ | htbelow
  · have htg : t = g ∨ t = h := by simpa [hJ] using htJ
    rcases htg with htg | hth
    · subst t
      exact False.elim (pure_junk_no_mixed_operand G C s hL.1 hTop g h hJ hindhg gzero e hemix b hread)
    · exact hth
  · exact False.elim (mixed_or_below_junk_no_top_reader G C s hcol h4 hL hTop
      g h hne hindgh hindhg hJ hmix hA hB hd e hecone hemix t ht htand htbelow b hread)

lemma mixed_or_reader_closure {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (s : Fin n → Bool) (hcol : ∀ a b, G.Adj a b → s a ≠ s b)
    (h4 : NoFourCycle G) (hL : IsLeastAO G C) (hTop : TopForm G C)
    (g h : ℕ) (hne : h ≠ g) (hindgh : ¬ InCone n C g h) (hindhg : ¬ InCone n C h g)
    (hJ : junk G C = {g, h})
    (hmix : ∀ c : Bool, gateVal n C h (monoInput s c) = true)
    (gzero : ∀ c : Bool, gateVal n C g (monoInput s c) = false)
    (hA : 2 ≤ (side (n := n) C g 0).card) (hB : 2 ≤ (side (n := n) C g 1).card)
    (hd : Disjoint (side (n := n) C g 0) (side (n := n) C g 1))
    (e : ℕ) (hecone : InCone n C e h)
    (hemix : ∀ c : Bool, gateVal n C e (monoInput s c) = true)
    (t : ℕ) (ht : t < C.gates.length) (hread : n + e ∈ (gateAt C t).inputs) :
    t = h ∨ (InCone n C t h ∧ (gateAt C t).op = GateOp.or ∧
      ∀ c : Bool, gateVal n C t (monoInput s c) = true) := by
  rcases hL.1.1 _ (gateAt_mem' C t ht) with htand | htor
  · exact Or.inl (mixed_or_and_reader_eq_junk G C s hcol h4 hL hTop g h hne hindgh hindhg
      hJ hmix gzero hA hB hd e hecone hemix t ht htand hread)
  · have het : e < t := by have := hL.1.2.1 t ht (n + e) hread; omega
    have hte : OrReaches n C (n + t) e :=
      orReach_trans n C t ht htor (n + e) hread (by omega) e (orReach_self n C e (by omega))
    have htmix : ∀ c : Bool, gateVal n C t (monoInput s c) = true := by
      intro c
      exact reach_up n C _ _ e hte (hemix c)
    have hfound : ∃ a, a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧
        ∃ b : Fin 2, OrReaches n C (opnd C a b) t := by
      rcases least_gate_reaches_output G C hL t ht with hout | ⟨k, hout, htk⟩
      · have hrout : OrReaches n C C.output t := by rw [hout]; exact orReach_self n C t ht
        exact False.elim (output_not_reaches_mixed hcol hL.2.1 htmix hrout)
      · rcases cone_first_and hL.1 t k htk with hrout | hf
        · rw [← hout] at hrout
          exact False.elim (output_not_reaches_mixed hcol hL.2.1 htmix hrout)
        · exact hf
    obtain ⟨a, ha, haand, b, hat⟩ := hfound
    have hae : OrReaches n C (opnd C a b) e := orReach_wire_trans hat hte
    have hah : a = h := mixed_or_and_user_eq_junk G C s hcol h4 hL hTop g h hne hindgh hindhg
      hJ hmix gzero hA hB hd e hecone hemix a ha haand b hae
    subst a
    have hth := reach_cone n C h ha _ (opnd_mem hL.1 ha b) (opnd_lt hL.1 ha b) t hat
    exact Or.inr ⟨hth, htor, htmix⟩

end Mixed

namespace NestedMixed

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
  PEqualNP.Outside.L_meta_5012_aux.Mixed

lemma clean_gate_unchanged_without_reader {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (hAO : IsAO2 n C) (hTop : TopForm G C) (g h : ℕ) (hJ : junk G C = {g, h})
    (hmix : ∀ c : Bool, gateVal n C h (monoInput s c) = true)
    (r : Gate) (preserve : ∀ x, gateVal n (patch C h r) g x = gateVal n C g x)
    (t : ℕ) (ht : t < C.gates.length) (htand : (gateAt C t).op = GateOp.and)
    (htbelow : BelowF G C t)
    (hnot : ∀ b : Fin 2, ¬ OrReaches n C (opnd C t b) h) (x : Fin n → Bool) :
    gateVal n (patch C h r) t x = gateVal n C t x := by
  have hhJ : h ∈ junk G C := by simp [hJ]
  have hhand := (mem_junk.mp hhJ).2.1
  have hne := mixed_ne_clean hcol hmix htbelow
  have transfer (b : Fin 2) :
      W n (patch C h r) x (opnd C t b) = true ↔ W n C x (opnd C t b) = true := by
    constructor
    · intro hv
      rcases down_patch hhand r x (fun k hk => hAO.1 _ (gateAt_mem' C k hk)) _ hv with
        ⟨u, hu, hxu⟩ | ⟨k, hk, hr, hkand, hkv⟩
      · exact orIn_val n C x _ u hu hxu
      · have hcone := reach_cone n C t ht _ (opnd_mem hAO ht b) (opnd_lt hAO ht b) k hr
        have hkJ := and_ancestor_junk hTop ht htand hk hkand hcone
        have hkg : k = g ∨ k = h := by simpa [hJ] using hkJ
        rcases hkg with hkg | hkg <;> subst k
        · apply reach_up n C x _ g hr
          change gateVal n (patch C h r) g x = true at hkv
          rwa [preserve x] at hkv
        · exact False.elim (hnot b hr)
    · intro hv
      rcases down n C x (fun k hk => hAO.1 _ (gateAt_mem' C k hk)) _ hv with
        ⟨u, hu, hxu⟩ | ⟨k, hk, hr, hkand, hkv⟩
      · exact orIn_val_patch hhand r x _ u hu hxu
      · have hcone := reach_cone n C t ht _ (opnd_mem hAO ht b) (opnd_lt hAO ht b) k hr
        have hkJ := and_ancestor_junk hTop ht htand hk hkand hcone
        have hkg : k = g ∨ k = h := by simpa [hJ] using hkJ
        rcases hkg with hkg | hkg <;> subst k
        · apply reach_up_patch hhand r x _ g hr
          change gateVal n (patch C h r) g x = true
          rw [preserve x]
          exact hkv
        · exact False.elim (hnot b hr)
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hv
    apply and_two hAO ht htand 0 x
    · exact (transfer 0).mp (and_true_operands_patch r hAO ht htand hne x hv 0)
    · exact (transfer (1 - 0)).mp (and_true_operands_patch r hAO ht htand hne x hv (1 - 0))
  · intro hv
    apply W_and_patch r x t ht htand hne
    intro w hw
    obtain ⟨b, rfl⟩ := (mem_inputs_iff_opnd hAO ht w).mp hw
    exact ⟨opnd_lt hAO ht b, (transfer b).mpr (and_true_operands hAO ht htand x hv b)⟩

lemma output_frontier_below {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hF : circuitFun n C = graphFun G ∅) (k : ℕ)
    (hr : OrReaches n C C.output k) : BelowF G C k := by
  intro x hx
  have hout := reach_up n C x C.output k hr hx
  change circuitFun n C x = true at hout
  rwa [hF] at hout

lemma no_reader_patch_computes {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (hAO : IsAO2 n C) (hTop : TopForm G C) (hF : circuitFun n C = graphFun G ∅)
    (g h : ℕ) (hJ : junk G C = {g, h})
    (hmix : ∀ c : Bool, gateVal n C h (monoInput s c) = true)
    (r : Gate) (preserve : ∀ x, gateVal n (patch C h r) g x = gateVal n C g x)
    (hnot : ∀ t, t < C.gates.length → (gateAt C t).op = GateOp.and →
      BelowF G C t → ∀ b : Fin 2, ¬ OrReaches n C (opnd C t b) h) :
    circuitFun n (patch C h r) = graphFun G ∅ := by
  have hhJ : h ∈ junk G C := by simp [hJ]
  have hhand := (mem_junk.mp hhJ).2.1
  have hclean (t : ℕ) (ht : t < C.gates.length) (htand : (gateAt C t).op = GateOp.and)
      (htbelow : BelowF G C t) (x : Fin n → Bool) :
      gateVal n (patch C h r) t x = gateVal n C t x :=
    clean_gate_unchanged_without_reader G C s hcol hAO hTop g h hJ hmix r preserve
      t ht htand htbelow (hnot t ht htand htbelow) x
  rw [← hF]
  funext x
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hv
    rcases down_patch hhand r x (fun k hk => hAO.1 _ (gateAt_mem' C k hk)) C.output hv with
      ⟨u, hu, hxu⟩ | ⟨k, hk, hr, hkand, hkv⟩
    · exact orIn_val n C x _ u hu hxu
    · apply reach_up n C x C.output k hr
      change gateVal n (patch C h r) k x = true at hkv
      rwa [hclean k hk hkand (output_frontier_below G C hF k hr) x] at hkv
  · intro hv
    rcases down n C x (fun k hk => hAO.1 _ (gateAt_mem' C k hk)) C.output hv with
      ⟨u, hu, hxu⟩ | ⟨k, hk, hr, hkand, hkv⟩
    · exact orIn_val_patch hhand r x _ u hu hxu
    · apply reach_up_patch hhand r x C.output k hr
      change gateVal n (patch C h r) k x = true
      rw [hclean k hk hkand (output_frontier_below G C hF k hr) x]
      exact hkv


end NestedMixed

namespace NestedMixed

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
  PEqualNP.Outside.L_meta_5012_aux.Mixed

lemma least_independent_mixed_has_clean_reader {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (hL : IsLeastAO G C) (hTop : TopForm G C)
    (g h : ℕ) (hne : h ≠ g) (hcone : ¬ InCone n C h g) (hJ : junk G C = {g, h})
    (hmix : ∀ c : Bool, gateVal n C h (monoInput s c) = true) :
    ∃ t, t < C.gates.length ∧ (gateAt C t).op = GateOp.and ∧ BelowF G C t ∧
      ∃ b : Fin 2, OrReaches n C (opnd C t b) h := by
  classical
  by_contra hn
  have hnot : ∀ t, t < C.gates.length → (gateAt C t).op = GateOp.and →
      BelowF G C t → ∀ b : Fin 2, ¬ OrReaches n C (opnd C t b) h := by
    intro t ht htand htbelow b hr
    exact hn ⟨t, ht, htand, htbelow, b, hr⟩
  have hhJ : h ∈ junk G C := by simp [hJ]
  have hgJ : g ∈ junk G C := by simp [hJ]
  have hh := (mem_junk.mp hhJ).1
  let w := opnd C h 0
  have hw : w < n + h := opnd_lt hL.1 hh 0
  apply Alias.least_patch_alias_impossible G C hL h w hh hw
  exact no_reader_patch_computes G C s hcol hL.1 hTop hL.2.1 g h hJ hmix
    ⟨GateOp.or, [w, w]⟩
    (gate_unchanged_of_notCone hL.1 h g _ (mem_junk.mp hgJ).1 hne hcone) hnot

lemma least_mixed_guard_clean {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (hL : IsLeastAO G C) (hTop : TopForm G C)
    (g h : ℕ) (hne : h ≠ g) (hcone : ¬ InCone n C h g) (hJ : junk G C = {g, h})
    (hmix : ∀ c : Bool, gateVal n C h (monoInput s c) = true) :
    ∀ x : Fin n → Bool, gateVal n C g x = true → gateVal n C h x = true →
      graphFun G ∅ x = true := by
  obtain ⟨t, ht, htand, htbelow, b, hr⟩ :=
    least_independent_mixed_has_clean_reader G C s hcol hL hTop g h hne hcone hJ hmix
  intro x hxg hxh
  have heq := (opposite_of_mixed_junk G C s hcol hL.1 hTop g h hJ hmix
    t ht htand htbelow b hr).2.2.2 x
  have hfirst : W n C x (opnd C t b) = true := reach_up n C x _ h hr hxh
  have hother : W n C x (opnd C t (1 - b)) = true := heq.trans hxg
  exact htbelow x (and_two hL.1 ht htand b x hfirst hother)

lemma other_false_on_monochrome {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (hL : IsLeastAO G C) (hTop : TopForm G C)
    (g h : ℕ) (hne : h ≠ g) (hcone : ¬ InCone n C h g) (hJ : junk G C = {g, h})
    (hmix : ∀ c : Bool, gateVal n C h (monoInput s c) = true) :
    ∀ c : Bool, gateVal n C g (monoInput s c) = false := by
  intro c
  cases hgc : gateVal n C g (monoInput s c) with
  | false => rfl
  | true =>
    have hf := least_mixed_guard_clean G C s hcol hL hTop g h hne hcone hJ hmix
      (monoInput s c) hgc (hmix c)
    rw [monoInput_false G s hcol] at hf
    cases hf

lemma other_raw_factors_opposite {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (hL : IsLeastAO G C) (hTop : TopForm G C)
    (g h : ℕ) (hne : h ≠ g) (hcone : ¬ InCone n C h g) (hJ : junk G C = {g, h})
    (hmix : ∀ c : Bool, gateVal n C h (monoInput s c) = true)
    (A B : Finset (Fin n)) (hA : A.Nonempty) (hB : B.Nonempty)
    (hraw : ∀ x : Fin n → Bool, gateVal n C g x = true ↔
      (∃ a ∈ A, x a = true) ∧ ∃ b ∈ B, x b = true) :
    ((∀ a ∈ A, s a = false) ∧ ∀ b ∈ B, s b = true) ∨
      ((∀ a ∈ A, s a = true) ∧ ∀ b ∈ B, s b = false) := by
  apply FactorColors.opposite_colors s A B hA hB
  intro c ⟨⟨a, ha, hsa⟩, ⟨b, hb, hsb⟩⟩
  have hv : gateVal n C g (monoInput s c) = true := by
    apply (hraw _).mpr
    exact ⟨⟨a, ha, by simp [monoInput, hsa]⟩, ⟨b, hb, by simp [monoInput, hsb]⟩⟩
  rw [other_false_on_monochrome G C s hcol hL hTop g h hne hcone hJ hmix c] at hv
  cases hv

end NestedMixed

namespace MixedSetup

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
  PEqualNP.Outside.L_meta_5012_aux.Mixed

lemma guard_factor_card {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (hL : IsLeastAO G C) (hTop : TopForm G C)
    (g h : ℕ) (hindgh : ¬ InCone n C g h) (hindhg : ¬ InCone n C h g)
    (hJ : junk G C = {g, h})
    (hmix : ∀ c : Bool, gateVal n C h (monoInput s c) = true) (b : Fin 2) :
    2 ≤ (side (n := n) C g b).card := by
  have hJswap : junk G C = {h, g} := by simpa [Finset.pair_comm] using hJ
  have hfac := independent_junk_raw_factors G C hL.1 hTop h g hJswap hindhg
  have hprod := independent_junk_raw_value G C hL.1 hTop h g hJswap hindhg
  have hpos := Finset.card_pos.mpr (hfac b).1
  by_contra hlt
  have hone : (side (n := n) C g b).card = 1 := by omega
  obtain ⟨u, heq⟩ := Finset.card_eq_one.mp hone
  apply no_singleton_factor_for_mixed_junk G C s hcol hL hTop g h hJ hindgh hmix
    u (side (n := n) C g (1 - b))
  intro x
  fin_cases b
  · have heq0 : side (n := n) C g 0 = {u} := by simpa using heq
    rw [hprod x, heq0]
    simp
  · have heq1 : side (n := n) C g 1 = {u} := by simpa using heq
    rw [hprod x, heq1]
    simp [Bool.and_comm]

lemma independent_mixed_setup {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (hL : IsLeastAO G C) (hTop : TopForm G C)
    (g h : ℕ) (hne : h ≠ g)
    (hindgh : ¬ InCone n C g h) (hindhg : ¬ InCone n C h g)
    (hJ : junk G C = {g, h})
    (hmix : ∀ c : Bool, gateVal n C h (monoInput s c) = true) :
    let A := side (n := n) C g 0
    let B := side (n := n) C g 1
    let S := side (n := n) C h 0
    let T := side (n := n) C h 1
    2 ≤ A.card ∧ 2 ≤ B.card ∧ Disjoint A B ∧
      (((∀ a ∈ A, s a = false) ∧ ∀ b ∈ B, s b = true) ∨
       ((∀ a ∈ A, s a = true) ∧ ∀ b ∈ B, s b = false)) ∧
      (∀ c : Bool, ∃ v ∈ S, s v = c) ∧
      (∀ c : Bool, ∃ v ∈ T, s v = c) ∧
      (∀ x : Fin n → Bool, gateVal n C g x =
        (decide (∃ a ∈ A, x a = true) && decide (∃ b ∈ B, x b = true))) ∧
      (∀ x : Fin n → Bool, gateVal n C h x =
        (decide (∃ v ∈ S, x v = true) && decide (∃ v ∈ T, x v = true))) ∧
      (∀ x : Fin n → Bool, gateVal n C g x = true → gateVal n C h x = true →
        graphFun G ∅ x = true) := by
  let A := side (n := n) C g 0
  let B := side (n := n) C g 1
  have hJswap : junk G C = {h, g} := by simpa [Finset.pair_comm] using hJ
  have hgf := independent_junk_raw_factors G C hL.1 hTop h g hJswap hindhg
  have hgv := independent_junk_raw_value G C hL.1 hTop h g hJswap hindhg
  have hhf := independent_junk_raw_factors G C hL.1 hTop g h hJ hindgh
  have hhv := independent_junk_raw_value G C hL.1 hTop g h hJ hindgh
  have hiff : ∀ x : Fin n → Bool, gateVal n C g x = true ↔
      (∃ a ∈ A, x a = true) ∧ ∃ b ∈ B, x b = true := by
    intro x
    rw [hgv x]
    simp only [Bool.and_eq_true, decide_eq_true_eq, A, B]
  have hcolors := NestedMixed.other_raw_factors_opposite G C s hcol hL hTop
    g h hne hindhg hJ hmix A B (hgf 0).1 (hgf 1).1 hiff
  have hd : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro v hvA hvB
    rcases hcolors with hcolors | hcolors
    · have h0 := hcolors.1 v hvA
      have h1 := hcolors.2 v hvB
      rw [h0] at h1
      cases h1
    · have h1 := hcolors.1 v hvA
      have h0 := hcolors.2 v hvB
      rw [h1] at h0
      cases h0
  have hhJ : h ∈ junk G C := by simp [hJ]
  have hh := (mem_junk.mp hhJ).1
  have hhand := (mem_junk.mp hhJ).2.1
  have hmixed (b : Fin 2) (c : Bool) : ∃ v ∈ side (n := n) C h b, s v = c := by
    have hv := and_true_operands hL.1 hh hhand (monoInput s c) (hmix c) b
    change wireVal n C (opnd C h b) (monoInput s c) = true at hv
    rw [(hhf b).2] at hv
    simpa [monoInput] using of_decide_eq_true hv
  exact ⟨guard_factor_card G C s hcol hL hTop g h hindgh hindhg hJ hmix 0,
    guard_factor_card G C s hcol hL hTop g h hindgh hindhg hJ hmix 1,
    hd, hcolors, hmixed 0, hmixed 1, hgv, hhv,
    NestedMixed.least_mixed_guard_clean G C s hcol hL hTop g h hne hindhg hJ hmix⟩

end MixedSetup


namespace CenterGeometry

open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

def ProductClean {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B C D : Finset (Fin n)) : Prop :=
  ∀ x : Fin n → Bool,
    (∃ a ∈ A, x a = true) → (∃ b ∈ B, x b = true) →
    (∃ c ∈ C, x c = true) → (∃ d ∈ D, x d = true) → graphFun G ∅ x = true

def Trace {n : Nat} (A B C D : Finset (Fin n)) (u v : Fin n) : Prop :=
  (u ∈ A ∨ v ∈ A) ∧ (u ∈ B ∨ v ∈ B) ∧
  (u ∈ C ∨ v ∈ C) ∧ (u ∈ D ∨ v ∈ D)

def traceGraph {n : Nat} (G : SimpleGraph (Fin n))
    (A B C D : Finset (Fin n)) : SimpleGraph (Fin n) :=
  { Adj := fun u v => G.Adj u v ∧ Trace A B C D u v
    symm := by
      constructor
      intro u v h
      exact ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.1.symm, h.2.2.2.2.symm⟩
    loopless := by
      constructor
      intro u h
      exact G.irrefl h.1 }

lemma graphFun_pair {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v : Fin n) : graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    simp only [pairInput, decide_eq_true_eq] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  · intro huv
    exact ⟨u, v, huv, by simp [pairInput], by simp [pairInput]⟩

lemma trace_adj {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B C D : Finset (Fin n)) (hclean : ProductClean G A B C D)
    {u v : Fin n} (ht : Trace A B C D u v) : G.Adj u v := by
  apply (graphFun_pair G u v).mp
  have hit : ∀ S : Finset (Fin n), (u ∈ S ∨ v ∈ S) → ∃ a ∈ S, pairInput u v a = true := by
    intro S hs
    rcases hs with hu | hv
    · exact ⟨u, hu, by simp [pairInput]⟩
    · exact ⟨v, hv, by simp [pairInput]⟩
  exact hclean _ (hit A ht.1) (hit B ht.2.1) (hit C ht.2.2.1) (hit D ht.2.2.2)

lemma trace_cross {n : Nat} (A B C D : Finset (Fin n)) (hAB : Disjoint A B)
    {u v : Fin n} (ht : Trace A B C D u v) :
    (u ∈ A ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ A) := by
  rcases ht.1 with huA | hvA <;> rcases ht.2.1 with huB | hvB
  · exact (Finset.disjoint_left.mp hAB huA huB).elim
  · exact Or.inl ⟨huA, hvB⟩
  · exact Or.inr ⟨huB, hvA⟩
  · exact (Finset.disjoint_left.mp hAB hvA hvB).elim

lemma universal_unique {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (S : Finset (Fin n)) (hS : 2 ≤ S.card)
    (u v : Fin n) (hu : ∀ z ∈ S, G.Adj u z) (hv : ∀ z ∈ S, G.Adj v z) : u = v := by
  by_contra hne
  have hsmall := h4 u v hne
  have hsub : S ⊆ Finset.univ.filter fun z => G.Adj u z ∧ G.Adj v z := by
    intro z hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu z hz, hv z hz⟩
  have := Finset.card_le_card hsub
  omega

lemma trace_outside_neighbor_unique {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (A B C D : Finset (Fin n)) (hAB : Disjoint A B)
    (hA : 2 ≤ A.card) (hB : 2 ≤ B.card) (hclean : ProductClean G A B C D)
    (z u v : Fin n) (hz : z ∉ C ∪ D)
    (hzu : (traceGraph G A B C D).Adj z u)
    (hzv : (traceGraph G A B C D).Adj z v) : u = v := by
  have hzC : z ∉ C := fun h => hz (Finset.mem_union_left _ h)
  have hzD : z ∉ D := fun h => hz (Finset.mem_union_right _ h)
  have huC : u ∈ C := hzu.2.2.2.1.resolve_left hzC
  have huD : u ∈ D := hzu.2.2.2.2.resolve_left hzD
  have hvC : v ∈ C := hzv.2.2.2.1.resolve_left hzC
  have hvD : v ∈ D := hzv.2.2.2.2.resolve_left hzD
  rcases trace_cross A B C D hAB hzu.2 with ⟨hzA, huB⟩ | ⟨hzB, huA⟩
  · have hvB : v ∈ B := hzv.2.2.1.resolve_left (fun hzB => Finset.disjoint_left.mp hAB hzA hzB)
    apply universal_unique G h4 A hA u v
    · intro a ha
      exact (trace_adj G A B C D hclean ⟨Or.inl ha, Or.inr huB, Or.inr huC, Or.inr huD⟩).symm
    · intro a ha
      exact (trace_adj G A B C D hclean ⟨Or.inl ha, Or.inr hvB, Or.inr hvC, Or.inr hvD⟩).symm
  · have hvA : v ∈ A := hzv.2.1.resolve_left (fun hzA => Finset.disjoint_left.mp hAB hzA hzB)
    apply universal_unique G h4 B hB u v
    · intro b hb
      exact trace_adj G A B C D hclean ⟨Or.inl huA, Or.inr hb, Or.inl huC, Or.inl huD⟩
    · intro b hb
      exact trace_adj G A B C D hclean ⟨Or.inl hvA, Or.inr hb, Or.inl hvC, Or.inl hvD⟩

lemma cover_inside_of_outside_degree_one {n : Nat} (H : SimpleGraph (Fin n))
    [DecidableRel H.Adj] (U K : Finset (Fin n))
    (hcover : ∀ a b, H.Adj a b → a ∈ K ∨ b ∈ K)
    (hinside : ∀ z, z ∉ U → ∀ w, H.Adj z w → w ∈ U)
    (hdegree : ∀ z, z ∉ U → (H.neighborFinset z).card ≤ 1) :
    ∃ K' : Finset (Fin n), K' ⊆ U ∧ K'.card ≤ K.card ∧
      ∀ a b, H.Adj a b → a ∈ K' ∨ b ∈ K' := by
  classical
  let f : Fin n → Finset (Fin n) := fun z => if z ∈ U then {z} else H.neighborFinset z
  let K' := K.biUnion f
  have hsmall : ∀ z, (f z).card ≤ 1 := by
    intro z
    by_cases hz : z ∈ U
    · simp [f, hz]
    · simpa [f, hz] using hdegree z hz
  refine ⟨K', ?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨z, hzK, hwf⟩ := Finset.mem_biUnion.mp hw
    by_cases hz : z ∈ U
    · have hwz : w = z := by simpa [f, hz] using hwf
      simpa [hwz] using hz
    · exact hinside z hz w (by simpa [f, hz] using hwf)
  · calc
      K'.card ≤ ∑ z ∈ K, (f z).card := Finset.card_biUnion_le
      _ ≤ ∑ _z ∈ K, 1 := Finset.sum_le_sum fun z _ => hsmall z
      _ = K.card := by simp
  · intro a b hab
    have hmove : ∀ z w, z ∈ K → H.Adj z w → z ∈ K' ∨ w ∈ K' := by
      intro z w hzK hzw
      by_cases hz : z ∈ U
      · exact Or.inl (Finset.mem_biUnion.mpr ⟨z, hzK, by simp [f, hz]⟩)
      · exact Or.inr (Finset.mem_biUnion.mpr ⟨z, hzK, by simpa [f, hz] using hzw⟩)
    rcases hcover a b hab with ha | hb
    · exact hmove a b ha hab
    · exact (hmove b a hb hab.symm).symm

lemma trace_cover_inside {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (A B C D K : Finset (Fin n)) (hAB : Disjoint A B)
    (hA : 2 ≤ A.card) (hB : 2 ≤ B.card) (hclean : ProductClean G A B C D)
    (hcover : ∀ a b, (traceGraph G A B C D).Adj a b → a ∈ K ∨ b ∈ K) :
    ∃ K' : Finset (Fin n), K' ⊆ C ∪ D ∧ K'.card ≤ K.card ∧
      ∀ a b, (traceGraph G A B C D).Adj a b → a ∈ K' ∨ b ∈ K' := by
  classical
  apply cover_inside_of_outside_degree_one (traceGraph G A B C D) (C ∪ D) K hcover
  · intro z hz w hzw
    apply Finset.mem_union_left
    exact hzw.2.2.2.1.resolve_left (fun hzC => hz (Finset.mem_union_left _ hzC))
  · intro z hz
    apply Finset.card_le_one.mpr
    intro u hu v hv
    exact trace_outside_neighbor_unique G h4 A B C D hAB hA hB hclean z u v hz
      (((traceGraph G A B C D).mem_neighborFinset z u).mp hu)
      (((traceGraph G A B C D).mem_neighborFinset z v).mp hv)

def GoodCenter {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B : Finset (Fin n)) (u : Fin n) : Prop :=
  ∀ x : Fin n → Bool,
    (∃ a ∈ A, x a = true) → (∃ b ∈ B, x b = true) → x u = true → graphFun G ∅ x = true

lemma overlap_good {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B C D : Finset (Fin n)) (hclean : ProductClean G A B C D)
    (u : Fin n) (huC : u ∈ C) (huD : u ∈ D) : GoodCenter G A B u := by
  intro x hA hB hu
  exact hclean x hA hB ⟨u, huC, hu⟩ ⟨u, huD, hu⟩

lemma nongood_exclusive {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B C D : Finset (Fin n)) (hclean : ProductClean G A B C D)
    (u : Fin n) (hu : u ∈ C ∪ D) (hbad : ¬ GoodCenter G A B u) :
    (u ∈ C ∧ u ∉ D) ∨ (u ∈ D ∧ u ∉ C) := by
  rcases Finset.mem_union.mp hu with huC | huD
  · exact Or.inl ⟨huC, fun huD => hbad (overlap_good G A B C D hclean u huC huD)⟩
  · exact Or.inr ⟨huD, fun huC => hbad (overlap_good G A B C D hclean u huC huD)⟩

lemma separate_clauses_pair_cover_reduces {n : Nat}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (h4 : NoFourCycle G)
    (A B C D : Finset (Fin n)) (hAB : Disjoint A B)
    (hclean : ProductClean G A B C D) (u v : Fin n)
    (huA : u ∈ A) (huC : u ∈ C) (huD : u ∉ D)
    (hvB : v ∈ B) (hvD : v ∈ D) (hvC : v ∉ C)
    (hcover : ∀ a b, (traceGraph G A B C D).Adj a b →
      a = u ∨ a = v ∨ b = u ∨ b = v) :
    (∀ a b, (traceGraph G A B C D).Adj a b → a = u ∨ b = u) ∨
      (∀ a b, (traceGraph G A B C D).Adj a b → a = v ∨ b = v) := by
  classical
  let H := traceGraph G A B C D
  by_cases huc : ∀ a b, H.Adj a b → a = u ∨ b = u
  · exact Or.inl huc
  right
  intro a b hab
  by_contra habv
  have hav : a ≠ v := fun h => habv (Or.inl h)
  have hbv : b ≠ v := fun h => habv (Or.inr h)
  have hu_neighbor : ∃ w, H.Adj u w ∧ w ≠ v := by
    rcases hcover a b hab with hau | hav' | hbu | hbv'
    · subst a
      exact ⟨b, hab, hbv⟩
    · exact (hav hav').elim
    · subst b
      exact ⟨a, hab.symm, hav⟩
    · exact (hbv hbv').elim
  have hv_neighbor : ∃ t, H.Adj v t ∧ t ≠ u := by
    push Not at huc
    obtain ⟨c, d, hcd, hcu, hdu⟩ := huc
    rcases hcover c d hcd with hcu' | hcv | hdu' | hdv
    · exact (hcu hcu').elim
    · subst c
      exact ⟨d, hcd, hdu⟩
    · exact (hdu hdu').elim
    · subst d
      exact ⟨c, hcd.symm, hcu⟩
  obtain ⟨w, huw, hwv⟩ := hu_neighbor
  obtain ⟨t, hvt, htu⟩ := hv_neighbor
  have huB : u ∉ B := fun h => Finset.disjoint_left.mp hAB huA h
  have hvA : v ∉ A := fun h => Finset.disjoint_left.mp hAB h hvB
  have hwB : w ∈ B := huw.2.2.1.resolve_left huB
  have hwD : w ∈ D := huw.2.2.2.2.resolve_left huD
  have htA : t ∈ A := hvt.2.1.resolve_left hvA
  have htC : t ∈ C := hvt.2.2.2.1.resolve_left hvC
  have huv : G.Adj u v := trace_adj G A B C D hclean
    ⟨Or.inl huA, Or.inr hvB, Or.inl huC, Or.inr hvD⟩
  have htw : G.Adj t w := trace_adj G A B C D hclean
    ⟨Or.inl htA, Or.inr hwB, Or.inl htC, Or.inr hwD⟩
  have hut : u = t := universal_unique G h4 {v, w} (by simp [hwv.symm]) u t
    (by intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl; exact huv; exact huw.1)
    (by intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl; exact hvt.1.symm; exact htw)
  exact htu hut.symm

end CenterGeometry

namespace CenterGeometry

open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

lemma minimal_trace_cover {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (A B C D K0 : Finset (Fin n)) (hAB : Disjoint A B)
    (hA : 2 ≤ A.card) (hB : 2 ≤ B.card) (hclean : ProductClean G A B C D)
    (hcover : ∀ a b, (traceGraph G A B C D).Adj a b → a ∈ K0 ∨ b ∈ K0) :
    ∃ K : Finset (Fin n), K ⊆ C ∪ D ∧ K.card ≤ K0.card ∧
      (∀ a b, (traceGraph G A B C D).Adj a b → a ∈ K ∨ b ∈ K) ∧
      ∀ J : Finset (Fin n), J ⊆ C ∪ D →
        (∀ a b, (traceGraph G A B C D).Adj a b → a ∈ J ∨ b ∈ J) → K.card ≤ J.card := by
  classical
  obtain ⟨K1, hK1U, hK1card, hK1cover⟩ :=
    trace_cover_inside G h4 A B C D K0 hAB hA hB hclean hcover
  have hex : ∃ m : Nat, ∃ K : Finset (Fin n), K ⊆ C ∪ D ∧
      (∀ a b, (traceGraph G A B C D).Adj a b → a ∈ K ∨ b ∈ K) ∧ K.card = m :=
    ⟨K1.card, K1, hK1U, hK1cover, rfl⟩
  obtain ⟨K, hKU, hKcover, hKcard⟩ := Nat.find_spec hex
  have hmin : ∀ J : Finset (Fin n), J ⊆ C ∪ D →
      (∀ a b, (traceGraph G A B C D).Adj a b → a ∈ J ∨ b ∈ J) → K.card ≤ J.card := by
    intro J hJU hJcover
    rw [hKcard]
    exact Nat.find_min' hex ⟨J, hJU, hJcover, rfl⟩
  exact ⟨K, hKU, (hmin K1 hK1U hK1cover).trans hK1card, hKcover, hmin⟩

lemma minimal_center_incident {n : Nat} (H : SimpleGraph (Fin n)) (U K : Finset (Fin n))
    (hKU : K ⊆ U) (hcover : ∀ a b, H.Adj a b → a ∈ K ∨ b ∈ K)
    (hmin : ∀ J : Finset (Fin n), J ⊆ U →
      (∀ a b, H.Adj a b → a ∈ J ∨ b ∈ J) → K.card ≤ J.card)
    (u : Fin n) (hu : u ∈ K) : ∃ v, H.Adj u v := by
  classical
  by_contra hn
  have hcover' : ∀ a b, H.Adj a b → a ∈ K.erase u ∨ b ∈ K.erase u := by
    intro a b hab
    have hau : a ≠ u := by
      intro heq
      subst a
      exact hn ⟨b, hab⟩
    have hbu : b ≠ u := by
      intro heq
      subst b
      exact hn ⟨a, hab.symm⟩
    rcases hcover a b hab with ha | hb
    · exact Or.inl (Finset.mem_erase.mpr ⟨hau, ha⟩)
    · exact Or.inr (Finset.mem_erase.mpr ⟨hbu, hb⟩)
  have hbound := hmin (K.erase u) (Finset.Subset.trans (Finset.erase_subset u K) hKU) hcover'
  have hcard := Finset.card_erase_add_one hu
  omega

def leaves {n : Nat} (s : Fin n → Bool) (C D : Finset (Fin n)) (u : Fin n) : Finset (Fin n) :=
  (if u ∈ C then D else C).filter fun v => s v ≠ s u

lemma good_of_universal_left {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B : Finset (Fin n)) (u : Fin n) (_hu : u ∈ A)
    (hall : ∀ b ∈ B, G.Adj u b) : GoodCenter G A B u := by
  intro x hA hB hxu
  obtain ⟨b, hb, hxb⟩ := hB
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq]
  exact ⟨u, b, hall b hb, hxu, hxb⟩

lemma good_of_universal_right {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B : Finset (Fin n)) (u : Fin n) (_hu : u ∈ B)
    (hall : ∀ a ∈ A, G.Adj u a) : GoodCenter G A B u := by
  intro x hA hB hxu
  obtain ⟨a, ha, hxa⟩ := hA
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq]
  exact ⟨u, a, hall a ha, hxu, hxa⟩

lemma nongood_leaves_clean {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hcol : ∀ a b, G.Adj a b → s a ≠ s b)
    (A B C D : Finset (Fin n)) (hclean : ProductClean G A B C D)
    (hAcol : ∀ a ∈ A, s a = false) (hBcol : ∀ b ∈ B, s b = true)
    (u : Fin n) (huAB : u ∈ A ∪ B) (huCD : u ∈ C ∪ D)
    (hbad : ¬ GoodCenter G A B u) : ∀ v ∈ leaves s C D u, G.Adj u v := by
  classical
  have hex := nongood_exclusive G A B C D hclean u huCD hbad
  have hcleanBA : ProductClean G B A C D := fun x hB hA hC hD => hclean x hA hB hC hD
  have hcleanDC : ProductClean G A B D C := fun x hA hB hD hC => hclean x hA hB hC hD
  have hcleanBADC : ProductClean G B A D C := fun x hB hA hD hC => hclean x hA hB hC hD
  intro v hv
  rcases Finset.mem_union.mp huAB with huA | huB
  · have huc := hAcol u huA
    rcases hex with ⟨huC, huD⟩ | ⟨huD, huC⟩
    · have hv' : v ∈ D ∧ s v = true := by
        simpa [leaves, huC, huc] using hv
      rcases MixedGeometry.clean_four_factor_star_choice G s hcol A B C D hclean
        u huA huC true hBcol with hgood | hstar
      · exact (hbad (good_of_universal_left G A B u huA hgood)).elim
      · exact hstar.2 v hv'.1 hv'.2
    · have hv' : v ∈ C ∧ s v = true := by
        simpa [leaves, huC, huc] using hv
      rcases MixedGeometry.clean_four_factor_star_choice G s hcol A B D C hcleanDC
        u huA huD true hBcol with hgood | hstar
      · exact (hbad (good_of_universal_left G A B u huA hgood)).elim
      · exact hstar.2 v hv'.1 hv'.2
  · have huc := hBcol u huB
    rcases hex with ⟨huC, huD⟩ | ⟨huD, huC⟩
    · have hv' : v ∈ D ∧ s v = false := by
        simpa [leaves, huC, huc] using hv
      rcases MixedGeometry.clean_four_factor_star_choice G s hcol B A C D hcleanBA
        u huB huC false hAcol with hgood | hstar
      · exact (hbad (good_of_universal_right G A B u huB hgood)).elim
      · exact hstar.2 v hv'.1 hv'.2
    · have hv' : v ∈ C ∧ s v = false := by
        simpa [leaves, huC, huc] using hv
      rcases MixedGeometry.clean_four_factor_star_choice G s hcol B A D C hcleanBADC
        u huB huD false hAcol with hgood | hstar
      · exact (hbad (good_of_universal_right G A B u huB hgood)).elim
      · exact hstar.2 v hv'.1 hv'.2

lemma nongood_leaves_complete {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hcol : ∀ a b, G.Adj a b → s a ≠ s b)
    (A B C D : Finset (Fin n)) (hclean : ProductClean G A B C D)
    (u v : Fin n) (huCD : u ∈ C ∪ D) (hbad : ¬ GoodCenter G A B u)
    (huv : (traceGraph G A B C D).Adj u v) : v ∈ leaves s C D u := by
  have hvcol : s v ≠ s u := (hcol u v huv.1).symm
  rcases nongood_exclusive G A B C D hclean u huCD hbad with ⟨huC, huD⟩ | ⟨huD, huC⟩
  · have hvD := huv.2.2.2.2.resolve_left huD
    simp [leaves, huC, hvD, hvcol]
  · have hvC := huv.2.2.2.1.resolve_left huC
    simp [leaves, huC, hvC, hvcol]

lemma replacement_center_selection {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hcol : ∀ a b, G.Adj a b → s a ≠ s b)
    (h4 : NoFourCycle G) (A B C D K0 : Finset (Fin n)) (hAB : Disjoint A B)
    (hA : 2 ≤ A.card) (hB : 2 ≤ B.card) (hclean : ProductClean G A B C D)
    (hAcol : ∀ a ∈ A, s a = false) (hBcol : ∀ b ∈ B, s b = true)
    (hK0 : K0.card ≤ 2)
    (hcover : ∀ a b, (traceGraph G A B C D).Adj a b → a ∈ K0 ∨ b ∈ K0) :
    ∃ K : Finset (Fin n), K ⊆ C ∪ D ∧ K.card ≤ 2 ∧
      (∀ a b, (traceGraph G A B C D).Adj a b → a ∈ K ∨ b ∈ K) ∧
      (∀ J : Finset (Fin n), J ⊆ C ∪ D →
        (∀ a b, (traceGraph G A B C D).Adj a b → a ∈ J ∨ b ∈ J) → K.card ≤ J.card) ∧
      (∀ u ∈ K, ∃ v, (traceGraph G A B C D).Adj u v) ∧
      ∀ u ∈ K, ¬ GoodCenter G A B u →
        ((u ∈ C ∧ u ∉ D) ∨ (u ∈ D ∧ u ∉ C)) ∧
        (∀ v ∈ leaves s C D u, G.Adj u v) ∧
        ∀ v, (traceGraph G A B C D).Adj u v → v ∈ leaves s C D u := by
  obtain ⟨K, hKU, hKcard, hKcover, hKmin⟩ :=
    minimal_trace_cover G h4 A B C D K0 hAB hA hB hclean hcover
  have hincident : ∀ u ∈ K, ∃ v, (traceGraph G A B C D).Adj u v :=
    fun u hu => minimal_center_incident (traceGraph G A B C D) (C ∪ D) K hKU hKcover hKmin u hu
  refine ⟨K, hKU, hKcard.trans hK0, hKcover, hKmin, hincident, ?_⟩
  intro u hu hbad
  obtain ⟨v, huv⟩ := hincident u hu
  have huAB : u ∈ A ∪ B := by
    rcases trace_cross A B C D hAB huv.2 with huA | huB
    · exact Finset.mem_union_left _ huA.1
    · exact Finset.mem_union_right _ huB.1
  exact ⟨nongood_exclusive G A B C D hclean u (hKU hu) hbad,
    nongood_leaves_clean G s hcol A B C D hclean hAcol hBcol u huAB (hKU hu) hbad,
    fun v huv => nongood_leaves_complete G s hcol A B C D hclean u v (hKU hu) hbad huv⟩

def RepairHit {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (A B C D K : Finset (Fin n)) (x : Fin n → Bool) : Prop :=
  ∃ u ∈ K, x u = true ∧
    (GoodCenter G A B u ∨ ∃ v ∈ leaves s C D u, x v = true)

lemma repair_safe {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (A B C D K : Finset (Fin n))
    (hstar : ∀ u ∈ K, ¬ GoodCenter G A B u → ∀ v ∈ leaves s C D u, G.Adj u v)
    (x : Fin n → Bool) (hA : ∃ a ∈ A, x a = true) (hB : ∃ b ∈ B, x b = true)
    (hrepair : RepairHit G s A B C D K x) : graphFun G ∅ x = true := by
  classical
  obtain ⟨u, huK, hxu, hu⟩ := hrepair
  by_cases hgood : GoodCenter G A B u
  · exact hgood x hA hB hxu
  obtain ⟨v, hv, hxv⟩ := hu.resolve_left hgood
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq]
  exact ⟨u, v, hstar u huK hgood v hv, hxu, hxv⟩

lemma repair_pair_complete {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hcol : ∀ a b, G.Adj a b → s a ≠ s b)
    (A B C D K : Finset (Fin n)) (hclean : ProductClean G A B C D)
    (hKU : K ⊆ C ∪ D)
    (hcover : ∀ a b, (traceGraph G A B C D).Adj a b → a ∈ K ∨ b ∈ K)
    (u v : Fin n) (huv : (traceGraph G A B C D).Adj u v) :
    RepairHit G s A B C D K (PEqualNP.EdgeOwnership.pairInput u v) := by
  classical
  have hmake : ∀ a b, a ∈ K → (traceGraph G A B C D).Adj a b →
      RepairHit G s A B C D K (PEqualNP.EdgeOwnership.pairInput a b) := by
    intro a b ha hab
    refine ⟨a, ha, by simp [PEqualNP.EdgeOwnership.pairInput], ?_⟩
    by_cases hgood : GoodCenter G A B a
    · exact Or.inl hgood
    · exact Or.inr ⟨b, nongood_leaves_complete G s hcol A B C D hclean a b (hKU ha) hgood hab,
        by simp [PEqualNP.EdgeOwnership.pairInput]⟩
  rcases hcover u v huv with hu | hv
  · exact hmake u v hu huv
  · have hh := hmake v u hv huv.symm
    have heq : PEqualNP.EdgeOwnership.pairInput v u = PEqualNP.EdgeOwnership.pairInput u v := by
      funext a
      simp [PEqualNP.EdgeOwnership.pairInput, or_comm]
    rw [heq] at hh
    exact hh

lemma exclusive_pair_same_color {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (h4 : NoFourCycle G) (A B C D : Finset (Fin n))
    (hAB : Disjoint A B) (hclean : ProductClean G A B C D)
    (hAcol : ∀ a ∈ A, s a = false) (hBcol : ∀ b ∈ B, s b = true)
    (u v : Fin n) (huAB : u ∈ A ∪ B) (hvAB : v ∈ A ∪ B)
    (huC : u ∈ C) (huD : u ∉ D) (hvD : v ∈ D) (hvC : v ∉ C)
    (hcover : ∀ a b, (traceGraph G A B C D).Adj a b →
      a = u ∨ a = v ∨ b = u ∨ b = v)
    (hnotu : ¬ ∀ a b, (traceGraph G A B C D).Adj a b → a = u ∨ b = u)
    (hnotv : ¬ ∀ a b, (traceGraph G A B C D).Adj a b → a = v ∨ b = v) :
    s u = s v := by
  rcases Finset.mem_union.mp huAB with huA | huB <;>
    rcases Finset.mem_union.mp hvAB with hvA | hvB
  · exact (hAcol u huA).trans (hAcol v hvA).symm
  · rcases separate_clauses_pair_cover_reduces G h4 A B C D hAB hclean u v
      huA huC huD hvB hvD hvC hcover with h | h
    · exact (hnotu h).elim
    · exact (hnotv h).elim
  · have hswap : traceGraph G A B D C = traceGraph G A B C D := by
      ext a b
      simp [traceGraph, Trace, and_assoc, and_comm]
    have hclean' : ProductClean G A B D C := fun x hA hB hD hC => hclean x hA hB hC hD
    have hcover' : ∀ a b, (traceGraph G A B D C).Adj a b →
        a = v ∨ a = u ∨ b = v ∨ b = u := by
      intro a b hab
      rw [hswap] at hab
      have hh := hcover a b hab
      tauto
    have hh := separate_clauses_pair_cover_reduces G h4 A B D C hAB hclean' v u
      hvA hvD hvC huB huC huD hcover'
    rw [hswap] at hh
    rcases hh with h | h
    · exact (hnotv h).elim
    · exact (hnotu h).elim
  · exact (hBcol u huB).trans (hBcol v hvB).symm

lemma nongood_pair_pattern {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (h4 : NoFourCycle G) (A B C D K : Finset (Fin n))
    (hAB : Disjoint A B) (hclean : ProductClean G A B C D)
    (hAcol : ∀ a ∈ A, s a = false) (hBcol : ∀ b ∈ B, s b = true)
    (hKU : K ⊆ C ∪ D) (hKcard : K.card ≤ 2)
    (hcover : ∀ a b, (traceGraph G A B C D).Adj a b → a ∈ K ∨ b ∈ K)
    (hmin : ∀ J : Finset (Fin n), J ⊆ C ∪ D →
      (∀ a b, (traceGraph G A B C D).Adj a b → a ∈ J ∨ b ∈ J) → K.card ≤ J.card)
    (u v : Fin n) (huK : u ∈ K) (hvK : v ∈ K) (huv : u ≠ v)
    (hbadU : ¬ GoodCenter G A B u) (hbadV : ¬ GoodCenter G A B v) :
    (u ∈ C ∧ v ∈ C) ∨ (u ∈ D ∧ v ∈ D) ∨ s u = s v := by
  classical
  have hpairSub : ({u, v} : Finset (Fin n)) ⊆ K := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> assumption
  have hpairCard : ({u, v} : Finset (Fin n)).card = 2 := Finset.card_pair huv
  have hpair : K = {u, v} := (Finset.eq_of_subset_of_card_le hpairSub (by omega)).symm
  have hKtwo : K.card = 2 := by rw [hpair]; exact hpairCard
  have hcover4 : ∀ a b, (traceGraph G A B C D).Adj a b →
      a = u ∨ a = v ∨ b = u ∨ b = v := by
    intro a b hab
    have hh := hcover a b hab
    simp only [hpair, Finset.mem_insert, Finset.mem_singleton] at hh
    tauto
  have hnot : ∀ z ∈ K, ¬ ∀ a b, (traceGraph G A B C D).Adj a b → a = z ∨ b = z := by
    intro z hz hh
    have hbound := hmin {z} (by intro a ha; simp only [Finset.mem_singleton] at ha; simpa [ha] using hKU hz)
      (by intro a b hab; simpa using hh a b hab)
    simp only [Finset.card_singleton] at hbound
    omega
  have hab : ∀ z ∈ K, z ∈ A ∪ B := by
    intro z hz
    obtain ⟨w, hzw⟩ := minimal_center_incident (traceGraph G A B C D) (C ∪ D) K hKU hcover hmin z hz
    rcases trace_cross A B C D hAB hzw.2 with hh | hh
    · exact Finset.mem_union_left _ hh.1
    · exact Finset.mem_union_right _ hh.1
  rcases nongood_exclusive G A B C D hclean u (hKU huK) hbadU with ⟨huC, huD⟩ | ⟨huD, huC⟩ <;>
    rcases nongood_exclusive G A B C D hclean v (hKU hvK) hbadV with ⟨hvC, hvD⟩ | ⟨hvD, hvC⟩
  · exact Or.inl ⟨huC, hvC⟩
  · exact Or.inr (Or.inr (exclusive_pair_same_color G s h4 A B C D hAB hclean hAcol hBcol
      u v (hab u huK) (hab v hvK) huC huD hvD hvC hcover4 (hnot u huK) (hnot v hvK)))
  · have hcover4' : ∀ a b, (traceGraph G A B C D).Adj a b →
        a = v ∨ a = u ∨ b = v ∨ b = u := by
      intro a b h
      have := hcover4 a b h
      tauto
    exact Or.inr (Or.inr (exclusive_pair_same_color G s h4 A B C D hAB hclean hAcol hBcol
      v u (hab v hvK) (hab u huK) hvC hvD huD huC hcover4' (hnot v hvK) (hnot u huK)).symm)
  · exact Or.inr (Or.inl ⟨huD, hvD⟩)

end CenterGeometry

namespace CenterGeometry

open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

lemma small_center_shapes {n : Nat} (K : Finset (Fin n)) (hK : K.card ≤ 2) :
    K = ∅ ∨ (∃ u, K = {u}) ∨ ∃ u v, u ≠ v ∧ K = {u, v} := by
  classical
  by_cases hzero : K.card = 0
  · exact Or.inl (Finset.card_eq_zero.mp hzero)
  by_cases hone : K.card = 1
  · exact Or.inr (Or.inl (Finset.card_eq_one.mp hone))
  have htwo : K.card = 2 := by omega
  obtain ⟨u, v, huv, hK⟩ := Finset.card_eq_two.mp htwo
  exact Or.inr (Or.inr ⟨u, v, huv, hK⟩)

lemma repair_singleton_good {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (A B C D : Finset (Fin n)) (u : Fin n)
    (hgood : GoodCenter G A B u) (x : Fin n → Bool) :
    RepairHit G s A B C D {u} x ↔ x u = true := by
  simp [RepairHit, hgood]

lemma repair_singleton_bad {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (A B C D : Finset (Fin n)) (u : Fin n)
    (hbad : ¬ GoodCenter G A B u) (x : Fin n → Bool) :
    RepairHit G s A B C D {u} x ↔
      (x u && decide (∃ v ∈ leaves s C D u, x v = true)) = true := by
  simp [RepairHit, hbad]

lemma repair_pair_good_good {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (A B C D : Finset (Fin n)) (u v : Fin n)
    (hu : GoodCenter G A B u) (hv : GoodCenter G A B v) (x : Fin n → Bool) :
    RepairHit G s A B C D {u, v} x ↔ (x u || x v) = true := by
  simp [RepairHit, hu, hv]

lemma repair_pair_good_bad {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (A B C D : Finset (Fin n)) (u v : Fin n)
    (hu : GoodCenter G A B u) (hv : ¬ GoodCenter G A B v) (x : Fin n → Bool) :
    RepairHit G s A B C D {u, v} x ↔
      (x u || (x v && decide (∃ w ∈ leaves s C D v, x w = true))) = true := by
  simp [RepairHit, hu, hv]

lemma repair_pair_bad_bad {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (A B C D : Finset (Fin n)) (u v : Fin n)
    (hu : ¬ GoodCenter G A B u) (hv : ¬ GoodCenter G A B v) (x : Fin n → Bool) :
    RepairHit G s A B C D {u, v} x ↔
      ((x u && decide (∃ w ∈ leaves s C D u, x w = true)) ||
        (x v && decide (∃ w ∈ leaves s C D v, x w = true))) = true := by
  simp [RepairHit, hu, hv]


lemma leaves_same_clause_color {n : Nat} (s : Fin n → Bool)
    (C D : Finset (Fin n)) (u v : Fin n)
    (hclause : (u ∈ C ↔ v ∈ C)) (hcolor : s u = s v) :
    leaves s C D u = leaves s C D v := by
  simp only [leaves, hclause, hcolor]

lemma repair_pair_bad_same_leaves {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (A B C D : Finset (Fin n)) (u v : Fin n)
    (hu : ¬ GoodCenter G A B u) (hv : ¬ GoodCenter G A B v)
    (hleaves : leaves s C D u = leaves s C D v) (x : Fin n → Bool) :
    RepairHit G s A B C D {u, v} x ↔
      ((x u || x v) && decide (∃ w ∈ leaves s C D u, x w = true)) = true := by
  rw [repair_pair_bad_bad G s A B C D u v hu hv x, ← hleaves]
  simp only [Bool.and_eq_true, Bool.or_eq_true]
  tauto

end CenterGeometry


namespace BoundaryLossGeneric

lemma exclusive_atom {n : Nat} {ι : Type*} [DecidableEq ι] (atoms : ι → Finset (Fin n))
    (S T : Finset (ι)) (u : Fin n)
    (huS : u ∈ S.biUnion atoms) (huT : u ∉ T.biUnion atoms) :
    ∃ i ∈ S, i ∉ T ∧ u ∈ atoms i := by
  obtain ⟨i, hi, hui⟩ := Finset.mem_biUnion.mp huS
  exact ⟨i, hi, fun hiT => huT (Finset.mem_biUnion.mpr ⟨i, hiT, hui⟩), hui⟩

lemma different_outputs_two_drops {n : Nat} {ι : Type*} [DecidableEq ι] (atoms : ι → Finset (Fin n))
    (s : Fin n → Bool) (color : ι → Bool)
    (hmono : ∀ i v, v ∈ atoms i → s v = color i)
    (S T : Finset (ι)) (u v : Fin n)
    (huS : u ∈ S.biUnion atoms) (huT : u ∉ T.biUnion atoms)
    (hvT : v ∈ T.biUnion atoms) (hvS : v ∉ S.biUnion atoms) (hsame : s u = s v) :
    2 ≤ ((S ∪ T) \ ((S.filter fun i => color i ≠ s u) ∪
      (T.filter fun i => color i ≠ s u))).card := by
  obtain ⟨i, hiS, hiT, hui⟩ := exclusive_atom atoms S T u huS huT
  obtain ⟨j, hjT, hjS, hvj⟩ := exclusive_atom atoms T S v hvT hvS
  have hij : i ≠ j := by
    intro heq
    subst j
    exact hiT hjT
  have hic : color i = s u := (hmono i u hui).symm
  have hjc : color j = s u := (hmono j v hvj).symm.trans hsame.symm
  have hsub : ({i, j} : Finset (ι)) ⊆
      (S ∪ T) \ ((S.filter fun i => color i ≠ s u) ∪ (T.filter fun i => color i ≠ s u)) := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · simp [hiS, hiT, hic]
    · simp [hjT, hjS, hjc]
  have hh := Finset.card_le_card hsub
  rw [Finset.card_pair hij] at hh
  exact hh

lemma same_output_opposite_two_drops {n : Nat} {ι : Type*} [DecidableEq ι] (atoms : ι → Finset (Fin n))
    (s : Fin n → Bool) (color : ι → Bool)
    (hmono : ∀ i v, v ∈ atoms i → s v = color i)
    (S T : Finset (ι)) (u v : Fin n)
    (huS : u ∈ S.biUnion atoms) (huT : u ∉ T.biUnion atoms)
    (hvS : v ∈ S.biUnion atoms) (hvT : v ∉ T.biUnion atoms) (hdiff : s u ≠ s v) :
    2 ≤ ((S ∪ T) \ T).card := by
  obtain ⟨i, hiS, hiT, hui⟩ := exclusive_atom atoms S T u huS huT
  obtain ⟨j, hjS, hjT, hvj⟩ := exclusive_atom atoms S T v hvS hvT
  have hij : i ≠ j := by
    intro heq
    subst j
    exact hdiff ((hmono i u hui).trans (hmono i v hvj).symm)
  have hsub : ({i, j} : Finset (ι)) ⊆ (S ∪ T) \ T := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · simp [hiS, hiT]
    · simp [hjS, hjT]
  have hh := Finset.card_le_card hsub
  rw [Finset.card_pair hij] at hh
  exact hh

lemma mixed_output_has_dropped_atom {n : Nat} {ι : Type*} [DecidableEq ι] (atoms : ι → Finset (Fin n))
    (s : Fin n → Bool) (color : ι → Bool)
    (hmono : ∀ i v, v ∈ atoms i → s v = color i)
    (T : Finset (ι)) (c : Bool)
    (hvertex : ∃ u ∈ T.biUnion atoms, s u = c) :
    ∃ i ∈ T, i ∉ T.filter fun j => color j ≠ c := by
  obtain ⟨u, hu, huc⟩ := hvertex
  obtain ⟨i, hi, hui⟩ := Finset.mem_biUnion.mp hu
  have hic : color i = c := (hmono i u hui).symm.trans huc
  exact ⟨i, hi, by simp [hic]⟩

lemma union_budget_one_output_saving {ι : Type*} [DecidableEq ι] (S T U : Finset (ι)) (m p : Nat)
    (hS : S.Nonempty) (hUT : U ⊆ T) (hdrop : ∃ j ∈ T, j ∉ U)
    (hbudget : (S ∪ T).card ≤ m + (if Disjoint S T then 2 else 1))
    (hcompile : p + 1 ≤ U.card) : p + 1 ≤ m := by
  obtain ⟨j, hjT, hjU⟩ := hdrop
  have hsub : U ⊆ S ∪ T := hUT.trans Finset.subset_union_right
  have hcard := Finset.card_sdiff_add_card_eq_card hsub
  have hloss : (if Disjoint S T then 2 else 1) ≤ ((S ∪ T) \ U).card := by
    by_cases hd : Disjoint S T
    · obtain ⟨i, hiS⟩ := hS
      have hiT : i ∉ T := fun hi => Finset.disjoint_left.mp hd hiS hi
      have hij : i ≠ j := fun h => hiT (h ▸ hjT)
      have hiU : i ∉ U := fun hi => hiT (hUT hi)
      have hp : ({i, j} : Finset (ι)) ⊆ (S ∪ T) \ U := by
        intro k hk
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl
        · simp [hiS, hiU]
        · simp [hjT, hjU]
      have hh := Finset.card_le_card hp
      simpa [hd, Finset.card_pair hij] using hh
    · have hne : ((S ∪ T) \ U).Nonempty :=
        ⟨j, Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _ hjT, hjU⟩⟩
      simpa [hd] using Finset.card_pos.mpr hne
  omega




lemma project_biUnion {n : Nat} {ι : Type*} [DecidableEq ι]
    (atoms : ι → Finset (Fin n)) (s : Fin n → Bool) (color : ι → Bool)
    (hmono : ∀ i v, v ∈ atoms i → s v = color i)
    (S : Finset ι) (c : Bool) :
    (S.biUnion atoms).filter (fun v => s v ≠ c) =
      (S.filter fun i => color i ≠ c).biUnion atoms := by
  ext v
  simp only [Finset.mem_filter, Finset.mem_biUnion]
  constructor
  · rintro ⟨⟨i, hi, hvi⟩, hvc⟩
    exact ⟨i, ⟨hi, fun hic => hvc ((hmono i v hvi).trans hic)⟩, hvi⟩
  · rintro ⟨i, ⟨hi, hic⟩, hvi⟩
    exact ⟨⟨i, hi, hvi⟩, fun hvc => hic ((hmono i v hvi).symm.trans hvc)⟩

lemma projected_signal_value {n : Nat} {ι : Type*} [DecidableEq ι]
    (atoms : ι → Finset (Fin n)) (s : Fin n → Bool) (color : ι → Bool)
    (hmono : ∀ i v, v ∈ atoms i → s v = color i)
    (S : Finset ι) (c : Bool) (x : Fin n → Bool) (value : ι → Bool)
    (hvalue : ∀ i ∈ S, value i = decide (∃ v ∈ atoms i, x v = true)) :
    decide (∃ i ∈ S.filter (fun i => color i ≠ c), value i = true) =
      decide (∃ v ∈ (S.biUnion atoms).filter (fun v => s v ≠ c), x v = true) := by
  classical
  rw [project_biUnion atoms s color hmono S c]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, Finset.mem_biUnion]
  constructor
  · rintro ⟨i, hi, hvi⟩
    rw [hvalue i (Finset.mem_filter.mp hi).1, decide_eq_true_eq] at hvi
    obtain ⟨v, hv, hx⟩ := hvi
    exact ⟨v, ⟨i, hi, hv⟩, hx⟩
  · rintro ⟨v, ⟨i, hi, hvi⟩, hx⟩
    refine ⟨i, hi, ?_⟩
    rw [hvalue i (Finset.mem_filter.mp hi).1, decide_eq_true_eq]
    exact ⟨v, hvi, hx⟩



lemma mixed_projection_budget {n : Nat} {ι : Type*} [DecidableEq ι]
    (atoms : ι → Finset (Fin n)) (s : Fin n → Bool) (color : ι → Bool)
    (hmono : ∀ i v, v ∈ atoms i → s v = color i)
    (S T : Finset ι) (c : Bool) (m p : Nat) (hS : S.Nonempty)
    (hvertex : ∃ u ∈ T.biUnion atoms, s u = c)
    (hbudget : (S ∪ T).card ≤ m + (if Disjoint S T then 2 else 1))
    (hcompile : p + 1 ≤ (T.filter fun i => color i ≠ c).card) : p + 1 ≤ m :=
  union_budget_one_output_saving S T _ m p hS (Finset.filter_subset _ _)
    (mixed_output_has_dropped_atom atoms s color hmono T c hvertex) hbudget hcompile

lemma mixed_projection_card_budget {n : Nat} {ι : Type*} [DecidableEq ι]
    (atoms : ι → Finset (Fin n)) (s : Fin n → Bool) (color : ι → Bool)
    (hmono : ∀ i v, v ∈ atoms i → s v = color i)
    (S T : Finset ι) (c : Bool) (m : Nat) (hS : S.Nonempty)
    (hvertex : ∃ u ∈ T.biUnion atoms, s u = c)
    (hbudget : (S ∪ T).card ≤ m + (if Disjoint S T then 2 else 1)) :
    (T.filter fun i => color i ≠ c).card ≤ m := by
  by_cases hzero : (T.filter fun i => color i ≠ c).card = 0
  · omega
  have hc : (T.filter fun i => color i ≠ c).card - 1 + 1 =
      (T.filter fun i => color i ≠ c).card := by omega
  have hh := mixed_projection_budget atoms s color hmono S T c m
    ((T.filter fun i => color i ≠ c).card - 1) hS hvertex hbudget (by omega)
  omega

lemma different_outputs_projection_card_budget {n : Nat} {ι : Type*} [DecidableEq ι]
    (atoms : ι → Finset (Fin n)) (s : Fin n → Bool) (color : ι → Bool)
    (hmono : ∀ i v, v ∈ atoms i → s v = color i)
    (S T : Finset ι) (u v : Fin n) (m : Nat)
    (huS : u ∈ S.biUnion atoms) (huT : u ∉ T.biUnion atoms)
    (hvT : v ∈ T.biUnion atoms) (hvS : v ∉ S.biUnion atoms) (hsame : s u = s v)
    (hbudget : (S ∪ T).card ≤ m + (if Disjoint S T then 2 else 1)) :
    ((S.filter fun i => color i ≠ s u) ∪ (T.filter fun i => color i ≠ s u)).card + 2 ≤
      m + (if Disjoint (S.filter fun i => color i ≠ s u)
        (T.filter fun i => color i ≠ s u) then 2 else 1) := by
  let U := S.filter fun i => color i ≠ s u
  let V := T.filter fun i => color i ≠ s u
  have hsub : U ∪ V ⊆ S ∪ T :=
    Finset.union_subset_union (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hcard := Finset.card_sdiff_add_card_eq_card hsub
  have hdrop := different_outputs_two_drops atoms s color hmono S T u v huS huT hvT hvS hsame
  have hdelta : (if Disjoint S T then 2 else 1) ≤ (if Disjoint U V then 2 else 1) := by
    by_cases hd : Disjoint S T
    · have hd' : Disjoint U V := hd.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
      simp [hd, hd']
    · simp only [hd, ↓reduceIte]
      split_ifs <;> omega
  change (U ∪ V).card + 2 ≤ m + (if Disjoint U V then 2 else 1)
  change 2 ≤ ((S ∪ T) \ (U ∪ V)).card at hdrop
  omega

lemma same_output_opposite_card_budget {n : Nat} {ι : Type*} [DecidableEq ι]
    (atoms : ι → Finset (Fin n)) (s : Fin n → Bool) (color : ι → Bool)
    (hmono : ∀ i v, v ∈ atoms i → s v = color i)
    (S T : Finset ι) (u v : Fin n) (m : Nat)
    (huS : u ∈ S.biUnion atoms) (huT : u ∉ T.biUnion atoms)
    (hvS : v ∈ S.biUnion atoms) (hvT : v ∉ T.biUnion atoms) (hdiff : s u ≠ s v)
    (hbudget : (S ∪ T).card ≤ m + (if Disjoint S T then 2 else 1)) :
    T.card ≤ m := by
  have hdrop := same_output_opposite_two_drops atoms s color hmono S T u v huS huT hvS hvT hdiff
  have hcard := Finset.card_sdiff_add_card_eq_card (Finset.subset_union_right (s₁ := S) (s₂ := T))
  have hd : (if Disjoint S T then 2 else 1) ≤ 2 := by split_ifs <;> omega
  omega

end BoundaryLossGeneric


namespace BoundaryLossGeneric

lemma opposite_projection_partition {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (color : ι → Bool) (c d : Bool) (hcd : c ≠ d) :
    Disjoint (S.filter fun i => color i ≠ c) (S.filter fun i => color i ≠ d) ∧
      (S.filter fun i => color i ≠ c) ∪ (S.filter fun i => color i ≠ d) = S := by
  constructor
  · apply Finset.disjoint_left.mpr
    intro i hi hj
    have hc := (Finset.mem_filter.mp hi).2
    have hd := (Finset.mem_filter.mp hj).2
    cases hci : color i <;> cases c <;> cases d <;> simp_all
  · ext i
    simp only [Finset.mem_union, Finset.mem_filter]
    cases hci : color i <;> cases c <;> cases d <;> simp_all

lemma projection_nonempty_of_vertex {n : Nat} {ι : Type*} [DecidableEq ι]
    (atoms : ι → Finset (Fin n)) (s : Fin n → Bool) (color : ι → Bool)
    (hmono : ∀ i v, v ∈ atoms i → s v = color i)
    (S : Finset ι) (c : Bool)
    (hvertex : ∃ v ∈ S.biUnion atoms, s v ≠ c) :
    (S.filter fun i => color i ≠ c).Nonempty := by
  obtain ⟨v, hv, hvc⟩ := hvertex
  obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.mp hv
  exact ⟨i, Finset.mem_filter.mpr ⟨hi, fun hic => hvc ((hmono i v hvi).trans hic)⟩⟩

end BoundaryLossGeneric

namespace GateBlock

open PEqualNP.CircuitLowerBounds

def val {n : Nat} (gs : List Gate) (w : Nat) (x : Fin n → Bool) : Bool :=
  (Splice.run gs (List.ofFn x)).getD w false

lemma val_prefix {n : Nat} (gs hs : List Gate) (w : Nat) (hw : w < n + gs.length)
    (x : Fin n → Bool) : val (gs ++ hs) w x = val gs w x := by
  exact Splice.run_prefix gs hs (List.ofFn x) w (by simpa using hw)

lemma val_input {n : Nat} (gs : List Gate) (u : Fin n) (x : Fin n → Bool) :
    val gs u.val x = x u := by
  rw [val, Splice.run_input gs (List.ofFn x) u.val (by simp)]
  simp

lemma append_binary {n : Nat} (F : (Fin n → Bool) → Bool) (gs : List Gate)
    (hok : Splice.Ok n gs) (o : GateOp) (ho : o = GateOp.and ∨ o = GateOp.or)
    (a b : Nat) (ha : a < n + gs.length) (hb : b < n + gs.length)
    (A B : (Fin n → Bool) → Bool)
    (hA : ∀ x, val gs a x = A x) (hB : ∀ x, val gs b x = B x)
    (hsafe : o = GateOp.and → ∀ x, A x = true → B x = true → F x = true) :
    Splice.Ok n (gs ++ [⟨o, [a, b]⟩]) ∧
    Splice.dc n F (gs ++ [⟨o, [a, b]⟩]) = Splice.dc n F gs ∧
    ∀ x, val (gs ++ [⟨o, [a, b]⟩]) (n + gs.length) x = o.eval [A x, B x] := by
  have hv (x : Fin n → Bool) :
      val (gs ++ [⟨o, [a, b]⟩]) (n + gs.length) x = o.eval [A x, B x] := by
    rw [val, Splice.next_value]
    change o.eval [val gs a x, val gs b x] = _
    rw [hA, hB]
  refine ⟨Splice.ok_snoc hok ho ha hb, ?_, hv⟩
  apply Splice.dc_append_clean
  intro j hjg hj hop x hx
  have hjj : j = gs.length := by simp at hj; omega
  subst j
  have hoand : o = GateOp.and := by simpa using hop
  have hh : A x = true ∧ B x = true := by
    change val (gs ++ [⟨o, [a, b]⟩]) (n + gs.length) x = true at hx
    rw [hv, hoand] at hx
    simpa [GateOp.eval] using hx
  exact hsafe hoand x hh.1 hh.2

lemma append_and {n : Nat} (F : (Fin n → Bool) → Bool) (gs : List Gate)
    (hok : Splice.Ok n gs) (a b : Nat)
    (ha : a < n + gs.length) (hb : b < n + gs.length)
    (A B : (Fin n → Bool) → Bool)
    (hA : ∀ x, val gs a x = A x) (hB : ∀ x, val gs b x = B x)
    (hsafe : ∀ x, A x = true → B x = true → F x = true) :
    Splice.Ok n (gs ++ [⟨GateOp.and, [a, b]⟩]) ∧
    Splice.dc n F (gs ++ [⟨GateOp.and, [a, b]⟩]) = Splice.dc n F gs ∧
    ∀ x, val (gs ++ [⟨GateOp.and, [a, b]⟩]) (n + gs.length) x = (A x && B x) := by
  simpa [GateOp.eval] using append_binary F gs hok GateOp.and (Or.inl rfl)
    a b ha hb A B hA hB (fun _ => hsafe)

lemma append_or {n : Nat} (F : (Fin n → Bool) → Bool) (gs : List Gate)
    (hok : Splice.Ok n gs) (a b : Nat)
    (ha : a < n + gs.length) (hb : b < n + gs.length)
    (A B : (Fin n → Bool) → Bool)
    (hA : ∀ x, val gs a x = A x) (hB : ∀ x, val gs b x = B x) :
    Splice.Ok n (gs ++ [⟨GateOp.or, [a, b]⟩]) ∧
    Splice.dc n F (gs ++ [⟨GateOp.or, [a, b]⟩]) = Splice.dc n F gs ∧
    ∀ x, val (gs ++ [⟨GateOp.or, [a, b]⟩]) (n + gs.length) x = (A x || B x) := by
  simpa [GateOp.eval] using append_binary F gs hok GateOp.or (Or.inr rfl)
    a b ha hb A B hA hB (by intro h; cases h)

lemma two_products_block {n : Nat} (F : (Fin n → Bool) → Bool) (gs : List Gate)
    (hok : Splice.Ok n gs) (a b c d : Nat)
    (ha : a < n + gs.length) (hb : b < n + gs.length)
    (hc : c < n + gs.length) (hd : d < n + gs.length)
    (A B C D : (Fin n → Bool) → Bool)
    (hA : ∀ x, val gs a x = A x) (hB : ∀ x, val gs b x = B x)
    (hC : ∀ x, val gs c x = C x) (hD : ∀ x, val gs d x = D x)
    (hsafeAB : ∀ x, A x = true → B x = true → F x = true)
    (hsafeCD : ∀ x, C x = true → D x = true → F x = true) :
    ∃ hs : List Gate, hs.length = 3 ∧ Splice.Ok n (gs ++ hs) ∧
      Splice.dc n F (gs ++ hs) = Splice.dc n F gs ∧
      ∀ x, val (gs ++ hs) (n + gs.length + 2) x =
        ((A x && B x) || (C x && D x)) := by
  let g1 : Gate := ⟨GateOp.and, [a, b]⟩
  let g2 : Gate := ⟨GateOp.and, [c, d]⟩
  let g3 : Gate := ⟨GateOp.or, [n + gs.length, n + gs.length + 1]⟩
  obtain ⟨ok1, dc1, hv1⟩ := append_and F gs hok a b ha hb A B hA hB hsafeAB
  obtain ⟨ok2, dc2, hv2⟩ := append_and F (gs ++ [g1]) ok1 c d
    (by simp; omega) (by simp; omega) C D
    (fun x => (val_prefix gs [g1] c hc x).trans (hC x))
    (fun x => (val_prefix gs [g1] d hd x).trans (hD x)) hsafeCD
  obtain ⟨ok3, dc3, hv3⟩ := append_or F ((gs ++ [g1]) ++ [g2]) ok2
    (n + gs.length) (n + gs.length + 1) (by simp) (by simp; omega)
    (fun x => A x && B x) (fun x => C x && D x)
    (fun x => (val_prefix (gs ++ [g1]) [g2] (n + gs.length) (by simp) x).trans (hv1 x))
    (by simpa [g2, Nat.add_assoc] using hv2)
  refine ⟨[g1, g2, g3], rfl, ?_, ?_, ?_⟩
  · simpa only [List.append_assoc, List.cons_append, List.nil_append] using ok3
  · simpa only [List.append_assoc, List.cons_append, List.nil_append] using dc3.trans (dc2.trans dc1)
  · intro x
    simpa [g3, List.append_assoc, Nat.add_assoc] using hv3 x

lemma raw_or_product_block {n : Nat} (F : (Fin n → Bool) → Bool) (gs : List Gate)
    (hok : Splice.Ok n gs) (a b c : Nat)
    (ha : a < n + gs.length) (hb : b < n + gs.length) (hc : c < n + gs.length)
    (A B C : (Fin n → Bool) → Bool)
    (hA : ∀ x, val gs a x = A x) (hB : ∀ x, val gs b x = B x)
    (hC : ∀ x, val gs c x = C x)
    (hsafe : ∀ x, B x = true → C x = true → F x = true) :
    ∃ hs : List Gate, hs.length = 2 ∧ Splice.Ok n (gs ++ hs) ∧
      Splice.dc n F (gs ++ hs) = Splice.dc n F gs ∧
      ∀ x, val (gs ++ hs) (n + gs.length + 1) x = (A x || (B x && C x)) := by
  let g1 : Gate := ⟨GateOp.and, [b, c]⟩
  let g2 : Gate := ⟨GateOp.or, [a, n + gs.length]⟩
  obtain ⟨ok1, dc1, hv1⟩ := append_and F gs hok b c hb hc B C hB hC hsafe
  obtain ⟨ok2, dc2, hv2⟩ := append_or F (gs ++ [g1]) ok1 a (n + gs.length)
    (by simp; omega) (by simp) A (fun x => B x && C x)
    (fun x => (val_prefix gs [g1] a ha x).trans (hA x)) hv1
  refine ⟨[g1, g2], rfl, ?_, ?_, ?_⟩
  · simpa only [List.append_assoc, List.cons_append, List.nil_append] using ok2
  · simpa only [List.append_assoc, List.cons_append, List.nil_append] using dc2.trans dc1
  · intro x
    simpa [g2, List.append_assoc, Nat.add_assoc] using hv2 x

lemma merged_centers_block {n : Nat} (F : (Fin n → Bool) → Bool) (gs : List Gate)
    (hok : Splice.Ok n gs) (a b c : Nat)
    (ha : a < n + gs.length) (hb : b < n + gs.length) (hc : c < n + gs.length)
    (A B C : (Fin n → Bool) → Bool)
    (hA : ∀ x, val gs a x = A x) (hB : ∀ x, val gs b x = B x)
    (hC : ∀ x, val gs c x = C x)
    (hsafeA : ∀ x, A x = true → C x = true → F x = true)
    (hsafeB : ∀ x, B x = true → C x = true → F x = true) :
    ∃ hs : List Gate, hs.length = 2 ∧ Splice.Ok n (gs ++ hs) ∧
      Splice.dc n F (gs ++ hs) = Splice.dc n F gs ∧
      ∀ x, val (gs ++ hs) (n + gs.length + 1) x = ((A x || B x) && C x) := by
  let g1 : Gate := ⟨GateOp.or, [a, b]⟩
  let g2 : Gate := ⟨GateOp.and, [n + gs.length, c]⟩
  obtain ⟨ok1, dc1, hv1⟩ := append_or F gs hok a b ha hb A B hA hB
  obtain ⟨ok2, dc2, hv2⟩ := append_and F (gs ++ [g1]) ok1 (n + gs.length) c
    (by simp) (by simp; omega) (fun x => A x || B x) C hv1
    (fun x => (val_prefix gs [g1] c hc x).trans (hC x)) (by
      intro x hx hcx
      have hx' : A x = true ∨ B x = true := by simpa using hx
      rcases hx' with hx | hx
      · exact hsafeA x hx hcx
      · exact hsafeB x hx hcx)
  refine ⟨[g1, g2], rfl, ?_, ?_, ?_⟩
  · simpa only [List.append_assoc, List.cons_append, List.nil_append] using ok2
  · simpa only [List.append_assoc, List.cons_append, List.nil_append] using dc2.trans dc1
  · intro x
    simpa [g2, List.append_assoc, Nat.add_assoc] using hv2 x

end GateBlock

namespace ORBlock

open PEqualNP.CircuitLowerBounds

lemma two_mapped_nat_outputs {n p : Nat} (M : Finset Nat)
    (gs : List Gate) (m : Nat → Nat) (V : (Fin n → Bool) → Nat → Bool)
    (hok : Splice.Ok n gs) (hm : Splice.Maps n p M gs m V)
    (S T : Finset Nat) (hS : S.Nonempty) (hT : T.Nonempty)
    (hwire : ∀ w ∈ S ∪ T, w < n + p)
    (hkeep : ∀ w ∈ S ∪ T, w < n ∨ w - n ∉ M)
    (F : (Fin n → Bool) → Bool) :
    ∃ hs : List Gate, ∃ outS outT : Nat,
      Splice.Ok n (gs ++ hs) ∧
      hs.length + (if Disjoint S T then 2 else 1) ≤ (S ∪ T).card ∧
      outS < n + (gs ++ hs).length ∧ outT < n + (gs ++ hs).length ∧
      (∀ x : Fin n → Bool,
        (Splice.run (gs ++ hs) (List.ofFn x)).getD outS false =
          decide (∃ w ∈ S, V x w = true) ∧
        (Splice.run (gs ++ hs) (List.ofFn x)).getD outT false =
          decide (∃ w ∈ T, V x w = true)) ∧
      Splice.dc n F (gs ++ hs) = Splice.dc n F gs := by
  classical
  let B := S ∪ T
  let q := Fintype.card ↥B
  let e : Fin q ≃ ↥B := (Fintype.equivFin ↥B).symm
  let wire : Fin q → Nat := fun i => (e i).val
  have hinj : Function.Injective wire := by
    intro i j hij
    apply e.injective
    exact Subtype.ext hij
  have hmem : ∀ i, wire i ∈ B := fun i => (e i).prop
  have hfilter : ∀ R : Finset Nat, R ⊆ B →
      (Finset.univ.filter fun i : Fin q => wire i ∈ R).image wire = R := by
    intro R hR
    ext w
    constructor
    · rintro hw
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
      exact (Finset.mem_filter.mp hi).2
    · intro hw
      obtain ⟨i, hi⟩ := e.surjective ⟨w, hR hw⟩
      have heq : wire i = w := congrArg Subtype.val hi
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [heq] using hw⟩, heq⟩
  let Si := Finset.univ.filter fun i : Fin q => wire i ∈ S
  let Ti := Finset.univ.filter fun i : Fin q => wire i ∈ T
  have hSi : Si.image wire = S := hfilter S Finset.subset_union_left
  have hTi : Ti.image wire = T := hfilter T Finset.subset_union_right
  have hSi_ne : Si.Nonempty := Finset.image_nonempty.mp (by rw [hSi]; exact hS)
  have hTi_ne : Ti.Nonempty := Finset.image_nonempty.mp (by rw [hTi]; exact hT)
  have hcard : (Si ∪ Ti).card = (S ∪ T).card := by
    rw [← hSi, ← hTi, ← Finset.image_union, Finset.card_image_of_injective _ hinj]
  have hdisj : Disjoint S T ↔ Disjoint Si Ti := by
    rw [← hSi, ← hTi]
    exact Finset.disjoint_image hinj
  obtain ⟨hs, outS, outT, hok', hsize, hltS, hltT, heval, hdc⟩ :=
    two_mapped_outputs M gs m V hok hm wire
      (fun i => hwire _ (hmem i)) (fun i => hkeep _ (hmem i)) Si Ti hSi_ne hTi_ne F
  refine ⟨hs, outS, outT, hok', ?_, hltS, hltT, ?_, hdc⟩
  · simpa only [← hdisj, hcard] using hsize
  · intro x
    rw [← hSi, ← hTi]
    simp only [Finset.exists_mem_image]
    exact heval x

end ORBlock


namespace ORCut


lemma vertices_le_edges_add_components {V : Type} [Finite V] (G : SimpleGraph V) :
    Nat.card V ≤ G.edgeSet.ncard + Nat.card G.ConnectedComponent := by
  classical
  let := Fintype.ofFinite G.ConnectedComponent
  have h : ∀ c : G.ConnectedComponent, c.supp.ncard ≤ c.toSimpleGraph.edgeSet.ncard + 1 := by
    intro c
    have hc := c.connected_toSimpleGraph.card_vert_le_card_edgeSet_add_one
    simpa only [← c.ncard_supp, Nat.card_coe_set_eq] using hc
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun c _ => h c)
  simpa only [Finset.sum_add_distrib, G.sum_connectedComponent_ncard_supp,
    G.sum_connectedComponent_ncard_edgeSet, Finset.sum_const, Finset.card_univ,
    Nat.card_eq_fintype_card, smul_eq_mul, mul_one] using hs

lemma components_le_roots {V : Type} [Finite V] (G : SimpleGraph V)
    (roots : Finset V) (hroot : ∀ v, ∃ r ∈ roots, G.Reachable v r) :
    Nat.card G.ConnectedComponent ≤ roots.card := by
  classical
  have hs : Function.Surjective (fun r : {v // v ∈ roots} => G.connectedComponentMk r.val) := by
    intro c
    induction c using SimpleGraph.ConnectedComponent.ind with
    | h v =>
      obtain ⟨r, hr, hvr⟩ := hroot v
      exact ⟨⟨r, hr⟩, (SimpleGraph.ConnectedComponent.sound hvr).symm⟩
  have hc := Nat.card_le_card_of_surjective _ hs
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using hc

def oldWireEdges (W J : Finset ℕ) (a b : ℕ → ℕ) (hJ : J ⊆ W)
    (ha : ∀ j ∈ J, a j ∈ W) (hb : ∀ j ∈ J, b j ∈ W) :
    Finset (Sym2 {w // w ∈ W}) :=
  J.attach.image (fun j : {j // j ∈ J} => s(⟨a j, ha j j.property⟩, ⟨j, hJ j.property⟩)) ∪
  J.attach.image (fun j : {j // j ∈ J} => s(⟨b j, hb j j.property⟩, ⟨j, hJ j.property⟩))

def oldWireGraph (W J : Finset ℕ) (a b : ℕ → ℕ) (hJ : J ⊆ W)
    (ha : ∀ j ∈ J, a j ∈ W) (hb : ∀ j ∈ J, b j ∈ W) :
    SimpleGraph {w // w ∈ W} :=
  SimpleGraph.fromEdgeSet (oldWireEdges W J a b hJ ha hb)

lemma oldWireGraph_edges_le (W J : Finset ℕ) (a b : ℕ → ℕ) (hJ : J ⊆ W)
    (ha : ∀ j ∈ J, a j ∈ W) (hb : ∀ j ∈ J, b j ∈ W) :
    (oldWireGraph W J a b hJ ha hb).edgeSet.ncard ≤ 2 * J.card := by
  classical
  unfold oldWireGraph
  rw [SimpleGraph.edgeSet_fromEdgeSet]
  calc
    _ ≤ (↑(oldWireEdges W J a b hJ ha hb) : Set (Sym2 {w // w ∈ W})).ncard :=
      Set.ncard_le_ncard Set.sdiff_subset
    _ = (oldWireEdges W J a b hJ ha hb).card := Set.ncard_coe_finset _
    _ ≤ (J.attach.image (fun j : {j // j ∈ J} => s(⟨a j, ha j j.property⟩, ⟨j, hJ j.property⟩)) :
          Finset (Sym2 {w // w ∈ W})).card +
        (J.attach.image (fun j : {j // j ∈ J} => s(⟨b j, hb j j.property⟩, ⟨j, hJ j.property⟩)) :
          Finset (Sym2 {w // w ∈ W})).card := Finset.card_union_le _ _
    _ ≤ J.card + J.card := by
      apply Nat.add_le_add
      · exact Finset.card_image_le.trans_eq Finset.card_attach
      · exact Finset.card_image_le.trans_eq Finset.card_attach
    _ = 2 * J.card := by omega

lemma old_boundary_le_gates_add_components (B J : Finset ℕ) (hdis : Disjoint B J)
    (a b : ℕ → ℕ) (ha : ∀ j ∈ J, a j ∈ B ∪ J) (hb : ∀ j ∈ J, b j ∈ B ∪ J) :
    B.card ≤ J.card + Nat.card (oldWireGraph (B ∪ J) J a b
      Finset.subset_union_right ha hb).ConnectedComponent := by
  have hv := vertices_le_edges_add_components
    (oldWireGraph (B ∪ J) J a b Finset.subset_union_right ha hb)
  have he := oldWireGraph_edges_le (B ∪ J) J a b Finset.subset_union_right ha hb
  have hu : (B ∪ J).card = B.card + J.card := Finset.card_union_of_disjoint hdis
  simp only [Nat.card_eq_fintype_card, Fintype.card_coe] at hv ⊢
  omega

lemma old_operand_reachable (W J : Finset ℕ) (a b : ℕ → ℕ) (hJ : J ⊆ W)
    (ha : ∀ j ∈ J, a j ∈ W) (hb : ∀ j ∈ J, b j ∈ W)
    (u j : ℕ) (hu : u ∈ W) (hj : j ∈ J) (hoperand : u = a j ∨ u = b j) :
    (oldWireGraph W J a b hJ ha hb).Reachable ⟨u, hu⟩ ⟨j, hJ hj⟩ := by
  classical
  by_cases heq : u = j
  · have hsub : (⟨u, hu⟩ : {w // w ∈ W}) = ⟨j, hJ hj⟩ := Subtype.ext heq
    rw [hsub]
  apply SimpleGraph.Adj.reachable
  rw [oldWireGraph, SimpleGraph.fromEdgeSet_adj]
  refine ⟨?_, fun h => heq (congrArg Subtype.val h)⟩
  rcases hoperand with rfl | rfl
  · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨⟨j, hj⟩, by simp, rfl⟩)
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨⟨j, hj⟩, by simp, rfl⟩)

def step (Q : Finset ℕ) (a b : ℕ → ℕ) (u v : ℕ) : Prop :=
  v ∈ Q ∧ (u = a v ∨ u = b v)

open Classical in
noncomputable def frontier (Q : Finset ℕ) (a b : ℕ → ℕ) (r : ℕ) : Finset ℕ :=
  (Finset.range (r + 1)).filter fun u => u ∉ Q ∧ Relation.ReflTransGen (step Q a b) u r

lemma path_le (Q : Finset ℕ) (a b : ℕ → ℕ)
    (hback : ∀ q ∈ Q, a q < q ∧ b q < q)
    {u v : ℕ} (h : Relation.ReflTransGen (step Q a b) u v) : u ≤ v := by
  induction h with
  | refl => exact le_rfl
  | @tail v w _ hstep ih =>
    obtain ⟨hw, h | h⟩ := hstep
    · have := (hback w hw).1; omega
    · have := (hback w hw).2; omega

lemma mem_frontier (Q : Finset ℕ) (a b : ℕ → ℕ)
    (hback : ∀ q ∈ Q, a q < q ∧ b q < q) (u r : ℕ) :
    u ∈ frontier Q a b r ↔ u ∉ Q ∧ Relation.ReflTransGen (step Q a b) u r := by
  classical
  unfold frontier
  rw [Finset.mem_filter, Finset.mem_range]
  constructor
  · exact And.right
  · intro h
    exact ⟨by have := path_le Q a b hback h.2; omega, h⟩

lemma frontier_of_not_mem (Q : Finset ℕ) (a b : ℕ → ℕ)
    (hback : ∀ q ∈ Q, a q < q ∧ b q < q) (r : ℕ) (hr : r ∉ Q) :
    frontier Q a b r = {r} := by
  ext u
  rw [mem_frontier Q a b hback, Finset.mem_singleton]
  constructor
  · rintro ⟨_, h⟩
    cases h with
    | refl => rfl
    | tail _ hs => exact False.elim (hr hs.1)
  · rintro rfl
    exact ⟨hr, Relation.ReflTransGen.refl⟩

lemma frontier_of_mem (Q : Finset ℕ) (a b : ℕ → ℕ)
    (hback : ∀ q ∈ Q, a q < q ∧ b q < q) (r : ℕ) (hr : r ∈ Q) :
    frontier Q a b r = frontier Q a b (a r) ∪ frontier Q a b (b r) := by
  ext u
  rw [Finset.mem_union, mem_frontier Q a b hback, mem_frontier Q a b hback,
    mem_frontier Q a b hback]
  constructor
  · rintro ⟨hu, hpath⟩
    cases hpath with
    | refl => exact False.elim (hu hr)
    | tail hp hs =>
      rcases hs.2 with heq | heq
      · exact Or.inl ⟨hu, heq ▸ hp⟩
      · exact Or.inr ⟨hu, heq ▸ hp⟩
  · rintro (⟨hu, hp⟩ | ⟨hu, hp⟩)
    · exact ⟨hu, hp.tail ⟨hr, Or.inl rfl⟩⟩
    · exact ⟨hu, hp.tail ⟨hr, Or.inr rfl⟩⟩

lemma frontier_nonempty (Q : Finset ℕ) (a b : ℕ → ℕ)
    (hback : ∀ q ∈ Q, a q < q ∧ b q < q) :
    ∀ r, (frontier Q a b r).Nonempty := by
  intro r
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    by_cases hr : r ∈ Q
    · rw [frontier_of_mem Q a b hback r hr]
      exact (ih (a r) (hback r hr).1).mono Finset.subset_union_left
    · rw [frontier_of_not_mem Q a b hback r hr]
      exact Finset.singleton_nonempty _

lemma frontier_semantics {X : Type} (Q : Finset ℕ) (a b : ℕ → ℕ)
    (hback : ∀ q ∈ Q, a q < q ∧ b q < q) (V : X → ℕ → Bool)
    (hOR : ∀ q ∈ Q, ∀ x, V x q = (V x (a q) || V x (b q))) :
    ∀ r x, V x r = true ↔ ∃ u ∈ frontier Q a b r, V x u = true := by
  intro r
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    intro x
    by_cases hr : r ∈ Q
    · rw [hOR r hr x, Bool.or_eq_true, ih (a r) (hback r hr).1 x,
        ih (b r) (hback r hr).2 x, frontier_of_mem Q a b hback r hr]
      simp only [Finset.mem_union]
      aesop
    · rw [frontier_of_not_mem Q a b hback r hr]
      simp

lemma path_reachable (W Q : Finset ℕ) (a b : ℕ → ℕ) (hQ : Q ⊆ W)
    (ha : ∀ q ∈ Q, a q ∈ W) (hb : ∀ q ∈ Q, b q ∈ W)
    {u v : ℕ} (hu : u ∈ W) (hp : Relation.ReflTransGen (step Q a b) u v) :
    ∃ hv : v ∈ W, (oldWireGraph W Q a b hQ ha hb).Reachable ⟨u, hu⟩ ⟨v, hv⟩ := by
  induction hp with
  | refl => exact ⟨hu, SimpleGraph.Reachable.refl _⟩
  | tail _ hs ih =>
    obtain ⟨ht, hreach⟩ := ih
    exact ⟨hQ hs.1, hreach.trans (old_operand_reachable W Q a b hQ ha hb
      _ _ ht hs.1 hs.2)⟩

lemma frontier_union_disjoint (Q : Finset ℕ) (a b : ℕ → ℕ)
    (hback : ∀ q ∈ Q, a q < q ∧ b q < q) (r s : ℕ) :
    Disjoint (frontier Q a b r ∪ frontier Q a b s) Q := by
  rw [Finset.disjoint_left]
  intro u hu hQ
  rcases Finset.mem_union.mp hu with hu | hu
  · exact ((mem_frontier Q a b hback u r).mp hu).1 hQ
  · exact ((mem_frontier Q a b hback u s).mp hu).1 hQ

lemma roots_mem (Q : Finset ℕ) (a b : ℕ → ℕ)
    (hback : ∀ q ∈ Q, a q < q ∧ b q < q) (r s : ℕ) :
    r ∈ (frontier Q a b r ∪ frontier Q a b s) ∪ Q ∧
    s ∈ (frontier Q a b r ∪ frontier Q a b s) ∪ Q := by
  constructor
  · by_cases hr : r ∈ Q
    · exact Finset.mem_union_right _ hr
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        ((mem_frontier Q a b hback r r).mpr ⟨hr, Relation.ReflTransGen.refl⟩))
  · by_cases hs : s ∈ Q
    · exact Finset.mem_union_right _ hs
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        ((mem_frontier Q a b hback s s).mpr ⟨hs, Relation.ReflTransGen.refl⟩))

lemma children_mem (Q : Finset ℕ) (a b : ℕ → ℕ)
    (hback : ∀ q ∈ Q, a q < q ∧ b q < q) (r s : ℕ)
    (hroot : ∀ q ∈ Q, Relation.ReflTransGen (step Q a b) q r ∨
      Relation.ReflTransGen (step Q a b) q s) :
    ∀ q ∈ Q, a q ∈ (frontier Q a b r ∪ frontier Q a b s) ∪ Q ∧
      b q ∈ (frontier Q a b r ∪ frontier Q a b s) ∪ Q := by
  intro q hq
  have child (v : ℕ) (hv : v = a q ∨ v = b q) :
      v ∈ (frontier Q a b r ∪ frontier Q a b s) ∪ Q := by
    by_cases hvQ : v ∈ Q
    · exact Finset.mem_union_right _ hvQ
    · have hstep : step Q a b v q := ⟨hq, hv⟩
      rcases hroot q hq with hp | hp
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          ((mem_frontier Q a b hback v r).mpr ⟨hvQ, (Relation.ReflTransGen.single hstep).trans hp⟩))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          ((mem_frontier Q a b hback v s).mpr ⟨hvQ, (Relation.ReflTransGen.single hstep).trans hp⟩))
  exact ⟨child _ (Or.inl rfl), child _ (Or.inr rfl)⟩

lemma frontier_budget (Q : Finset ℕ) (a b : ℕ → ℕ)
    (hback : ∀ q ∈ Q, a q < q ∧ b q < q) (r s : ℕ)
    (hroot : ∀ q ∈ Q, Relation.ReflTransGen (step Q a b) q r ∨
      Relation.ReflTransGen (step Q a b) q s) :
    (frontier Q a b r ∪ frontier Q a b s).card ≤ Q.card +
      (if Disjoint (frontier Q a b r) (frontier Q a b s) then 2 else 1) := by
  classical
  let B := frontier Q a b r ∪ frontier Q a b s
  let W := B ∪ Q
  have hQ : Q ⊆ W := Finset.subset_union_right
  have ha : ∀ q ∈ Q, a q ∈ W := fun q hq => (children_mem Q a b hback r s hroot q hq).1
  have hb : ∀ q ∈ Q, b q ∈ W := fun q hq => (children_mem Q a b hback r s hroot q hq).2
  have hR : r ∈ W ∧ s ∈ W := roots_mem Q a b hback r s
  let H := oldWireGraph W Q a b hQ ha hb
  let rr : {w // w ∈ W} := ⟨r, hR.1⟩
  let ss : {w // w ∈ W} := ⟨s, hR.2⟩
  have hreach : ∀ u : {w // w ∈ W}, H.Reachable u rr ∨ H.Reachable u ss := by
    intro u
    have paths : Relation.ReflTransGen (step Q a b) u.val r ∨
        Relation.ReflTransGen (step Q a b) u.val s := by
      rcases Finset.mem_union.mp u.property with hu | hu
      · rcases Finset.mem_union.mp hu with hu | hu
        · exact Or.inl ((mem_frontier Q a b hback _ _).mp hu).2
        · exact Or.inr ((mem_frontier Q a b hback _ _).mp hu).2
      · exact hroot _ hu
    rcases paths with hp | hp
    · obtain ⟨_, hh⟩ := path_reachable W Q a b hQ ha hb u.property hp
      exact Or.inl hh
    · obtain ⟨_, hh⟩ := path_reachable W Q a b hQ ha hb u.property hp
      exact Or.inr hh
  have hcard := old_boundary_le_gates_add_components B Q
    (frontier_union_disjoint Q a b hback r s) a b ha hb
  change B.card ≤ Q.card + Nat.card H.ConnectedComponent at hcard
  by_cases hd : Disjoint (frontier Q a b r) (frontier Q a b s)
  · have hc := components_le_roots H {rr, ss} (by
      intro u
      rcases hreach u with hu | hu
      · exact ⟨rr, by simp, hu⟩
      · exact ⟨ss, by simp, hu⟩)
    have htwo : ({rr, ss} : Finset {w // w ∈ W}).card ≤ 2 := Finset.card_le_two
    simp only [hd, ↓reduceIte]
    change B.card ≤ Q.card + 2
    omega
  · have hI : (frontier Q a b r ∩ frontier Q a b s).Nonempty :=
      Finset.not_disjoint_iff_nonempty_inter.mp hd
    obtain ⟨u, huI⟩ := hI
    obtain ⟨hur, hus⟩ := Finset.mem_inter.mp huI
    have hu : u ∈ W := Finset.mem_union_left _ (Finset.mem_union_left _ hur)
    obtain ⟨_, hpR⟩ := path_reachable W Q a b hQ ha hb hu
      ((mem_frontier Q a b hback _ _).mp hur).2
    obtain ⟨_, hpS⟩ := path_reachable W Q a b hQ ha hb hu
      ((mem_frontier Q a b hback _ _).mp hus).2
    have hrs : H.Reachable rr ss := hpR.symm.trans hpS
    have hc := components_le_roots H {rr} (by
      intro v
      refine ⟨rr, by simp, ?_⟩
      rcases hreach v with hv | hv
      · exact hv
      · exact hv.trans hrs.symm)
    simp only [Finset.card_singleton] at hc
    simp only [hd, ↓reduceIte]
    change B.card ≤ Q.card + 1
    omega

lemma frontier_exact_cost (Q : Finset ℕ) (a b : ℕ → ℕ)
    (hback : ∀ q ∈ Q, a q < q ∧ b q < q) (r s : ℕ)
    (hroot : ∀ q ∈ Q, Relation.ReflTransGen (step Q a b) q r ∨
      Relation.ReflTransGen (step Q a b) q s) :
    (frontier Q a b r ∪ frontier Q a b s).card -
      (if Disjoint (frontier Q a b r) (frontier Q a b s) then 2 else 1) ≤ Q.card := by
  have hh := frontier_budget Q a b hback r s hroot
  omega

lemma gate_index_card (n : ℕ) (Q : Finset ℕ) (hQ : ∀ q ∈ Q, n ≤ q) :
    (Q.image (fun q => q - n)).card = Q.card := by
  apply Finset.card_image_of_injOn
  intro u hu v hv heq
  have hu' := hQ u hu
  have hv' := hQ v hv
  change u - n = v - n at heq
  omega







end ORCut

namespace ORCut

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.Outside.L_meta_5012_aux

def leftWire (n : ℕ) (C : Circuit) (q : ℕ) : ℕ := opnd C (q - n) 0
def rightWire (n : ℕ) (C : Circuit) (q : ℕ) : ℕ := opnd C (q - n) 1

def IsOrCut (n : ℕ) (C : Circuit) (Q : Finset ℕ) : Prop :=
  ∀ q ∈ Q, n ≤ q ∧ q < n + C.gates.length ∧ (gateAt C (q - n)).op = GateOp.or

lemma circuit_backward {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {Q : Finset ℕ} (hQ : IsOrCut n C Q) :
    ∀ q ∈ Q, leftWire n C q < q ∧ rightWire n C q < q := by
  intro q hq
  obtain ⟨hqge, hqlt, _⟩ := hQ q hq
  have hj : q - n < C.gates.length := by omega
  have hh := Alias.gate_pair hAO hj
  dsimp [leftWire, rightWire]
  constructor <;> omega

lemma circuit_frontier_semantics {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {Q : Finset ℕ} (hQ : IsOrCut n C Q) (r : ℕ) (x : Fin n → Bool) :
    (Splice.run C.gates (List.ofFn x)).getD r false =
      decide (∃ u ∈ frontier Q (leftWire n C) (rightWire n C) r,
        (Splice.run C.gates (List.ofFn x)).getD u false = true) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  apply frontier_semantics Q (leftWire n C) (rightWire n C) (circuit_backward hAO hQ)
    (fun x q => (Splice.run C.gates (List.ofFn x)).getD q false)
  intro q hq y
  obtain ⟨hqge, hqlt, hop⟩ := hQ q hq
  have hj : q - n < C.gates.length := by omega
  have heq : n + (q - n) = q := by omega
  have hv := Alias.gate_value hAO hj y
  rw [heq, hop] at hv
  simpa [leftWire, rightWire, GateOp.eval] using hv

lemma wire_removed_iff (n : ℕ) (Q : Finset ℕ) (hQ : ∀ q ∈ Q, n ≤ q)
    (u : ℕ) (hu : n ≤ u) :
    u - n ∈ Q.image (fun q => q - n) ↔ u ∈ Q := by
  constructor
  · intro hm
    obtain ⟨q, hq, heq⟩ := Finset.mem_image.mp hm
    have hqge := hQ q hq
    have : q = u := by omega
    simpa only [this] using hq
  · exact fun hm => Finset.mem_image.mpr ⟨u, hm, rfl⟩

lemma frontier_kept (n : ℕ) (Q : Finset ℕ) (a b : ℕ → ℕ)
    (hback : ∀ q ∈ Q, a q < q ∧ b q < q) (hQ : ∀ q ∈ Q, n ≤ q)
    (r u : ℕ) (hu : u ∈ frontier Q a b r) :
    u < n ∨ u - n ∉ Q.image (fun q => q - n) := by
  by_cases hun : u < n
  · exact Or.inl hun
  · apply Or.inr
    intro hm
    exact ((mem_frontier Q a b hback u r).mp hu).1
      ((wire_removed_iff n Q hQ u (by omega)).mp hm)

lemma frontier_lt (Q : Finset ℕ) (a b : ℕ → ℕ)
    (hback : ∀ q ∈ Q, a q < q ∧ b q < q) (r N u : ℕ)
    (hr : r < N) (hu : u ∈ frontier Q a b r) : u < N := by
  have hh := path_le Q a b hback ((mem_frontier Q a b hback u r).mp hu).2
  omega

lemma circuit_cut_data {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {Q : Finset ℕ} (hQ : IsOrCut n C Q) (h r s : ℕ)
    (hr : r < n + h) (hs : s < n + h)
    (hroot : ∀ q ∈ Q,
      Relation.ReflTransGen (step Q (leftWire n C) (rightWire n C)) q r ∨
      Relation.ReflTransGen (step Q (leftWire n C) (rightWire n C)) q s) :
    let S := frontier Q (leftWire n C) (rightWire n C) r
    let T := frontier Q (leftWire n C) (rightWire n C) s
    let M := Q.image (fun q => q - n)
    S.Nonempty ∧ T.Nonempty ∧ M.card = Q.card ∧
      (∀ j ∈ M, j < h) ∧
      (∀ u ∈ S ∪ T, u < n + h ∧ (u < n ∨ u - n ∉ M)) ∧
      (S ∪ T).card - (if Disjoint S T then 2 else 1) ≤ M.card ∧
      (∀ x : Fin n → Bool,
        (Splice.run C.gates (List.ofFn x)).getD r false =
          decide (∃ u ∈ S, (Splice.run C.gates (List.ofFn x)).getD u false = true) ∧
        (Splice.run C.gates (List.ofFn x)).getD s false =
          decide (∃ u ∈ T, (Splice.run C.gates (List.ofFn x)).getD u false = true)) := by
  dsimp only
  have hb := circuit_backward hAO hQ
  have hn : ∀ q ∈ Q, n ≤ q := fun q hq => (hQ q hq).1
  have hc := gate_index_card n Q hn
  refine ⟨frontier_nonempty Q _ _ hb r, frontier_nonempty Q _ _ hb s, hc, ?_, ?_, ?_, ?_⟩
  · intro j hj
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hj
    have hqn := hn q hq
    rcases hroot q hq with hqr | hqs
    · have hh := path_le Q _ _ hb hqr
      omega
    · have hh := path_le Q _ _ hb hqs
      omega
  · intro u hu
    rcases Finset.mem_union.mp hu with hu | hu
    · exact ⟨frontier_lt Q _ _ hb r _ u hr hu, frontier_kept n Q _ _ hb hn r u hu⟩
    · exact ⟨frontier_lt Q _ _ hb s _ u hs hu, frontier_kept n Q _ _ hb hn s u hu⟩
  · rw [hc]
    exact frontier_exact_cost Q _ _ hb r s hroot
  · intro x
    exact ⟨circuit_frontier_semantics hAO hQ r x, circuit_frontier_semantics hAO hQ s x⟩


end ORCut

namespace Splice

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.Outside.L_meta_5012_aux PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge

lemma one_junk_splice_impossible {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : IsLeastAO G C)
    (rungOne : ∀ D : Circuit, IsLeastAO G D → (junk G D).card = 1 → False)
    (h g : ℕ) (M : Finset ℕ) (hh : h < C.gates.length)
    (hnotM : h ∉ M) (hM : M ⊆ Finset.range C.gates.length)
    (hout : C.output < n + C.gates.length) (houtM : C.output < n ∨ C.output - n ∉ M)
    (op : ℕ → GateOp) (a b : ℕ → ℕ)
    (V : (Fin n → Bool) → ℕ → Bool)
    (hin : ∀ x w, w < n → V x w = (List.ofFn x).getD w false)
    (hop : ∀ j < C.gates.length, op j = GateOp.and ∨ op j = GateOp.or)
    (hback : ∀ j < C.gates.length, a j < n + j ∧ b j < n + j)
    (havoid : ∀ j < C.gates.length, j ∉ insert h M →
      (a j < n ∨ a j - n ∉ M) ∧ (b j < n ∨ b j - n ∉ M))
    (hval : ∀ j < C.gates.length, j ∉ insert h M → ∀ x,
      V x (n + j) = (op j).eval [V x (a j), V x (b j)])
    (houtput : ∀ x, V x C.output = graphFun G ∅ x)
    (hg : g < C.gates.length) (hgkeep : g ∉ insert h M) (hAND : op g = GateOp.and)
    (hdirty : ∃ x : Fin n → Bool, V x (n + g) = true ∧ graphFun G ∅ x = false)
    (hclean : ∀ j < C.gates.length, j ∉ insert h M → j ≠ g → op j = GateOp.and →
      ∀ x, V x (n + j) = true → graphFun G ∅ x = true)
    (block : ∀ (gs : List Gate) (m : ℕ → ℕ), Ok n gs → Maps n h M gs m V →
      ∃ (hs : List Gate) (o : ℕ), Ok n (gs ++ hs) ∧ hs.length ≤ M.card + 1 ∧
        o < n + (gs ++ hs).length ∧
        (∀ x : Fin n → Bool, (run (gs ++ hs) (List.ofFn x)).getD o false = V x (n + h)) ∧
        dc n (graphFun G ∅) (gs ++ hs) ≤ dc n (graphFun G ∅) gs) : False := by
  classical
  obtain ⟨D, m, hAO, hF, hm, hk, hsize, hjunk⟩ :=
    splice_complete n C.gates.length h (M.card + 1) M hnotM hh hM C.output
      hout houtM op a b V G hin hop hback havoid hval houtput block
  have hsize' : D.size ≤ C.size := by
    dsimp only [Circuit.size] at hsize ⊢
    omega
  have hleast : IsLeastAO G D :=
    ⟨hAO, hF, fun E hEAO hEF => hsize'.trans (hL.2.2 E hEAO hEF)⟩
  have hsub : ((Finset.range C.gates.length).filter fun j =>
      j ∉ insert h M ∧ op j = GateOp.and ∧
      ∃ x : Fin n → Bool, V x (n + j) = true ∧ graphFun G ∅ x = false) ⊆ {g} := by
    intro j hj
    obtain ⟨hj, hkeep, hopj, x, hx, hFx⟩ := Finset.mem_filter.mp hj
    have hjlt := Finset.mem_range.mp hj
    apply Finset.mem_singleton.mpr
    by_contra hne
    have hh := hclean j hjlt hkeep hne hopj x hx
    rw [hFx] at hh
    cases hh
  have hle : (junk G D).card ≤ 1 := by
    have hh := hjunk.trans (Finset.card_le_card hsub)
    simpa only [Finset.card_singleton] using hh
  have hne : (junk G D).Nonempty := by
    exact kept_dirty G D.output hm hk g hg hgkeep hAND hdirty
  have hpos := Finset.card_pos.mpr hne
  exact rungOne D hleast (by omega)

lemma actual_one_junk_splice_impossible {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : IsLeastAO G C)
    (rungOne : ∀ D : Circuit, IsLeastAO G D → (junk G D).card = 1 → False)
    (h g : ℕ) (M : Finset ℕ) (hh : h < C.gates.length)
    (hM : ∀ j ∈ M, j < h) (hgkeep : g ∉ insert h M) (hgJ : g ∈ junk G C)
    (houtM : C.output < n ∨ C.output - n ∉ M)
    (V : (Fin n → Bool) → ℕ → Bool)
    (hin : ∀ x w, w < n → V x w = (List.ofFn x).getD w false)
    (havoid : ∀ j < C.gates.length, j ∉ insert h M →
      (opnd C j 0 < n ∨ opnd C j 0 - n ∉ M) ∧
      (opnd C j 1 < n ∨ opnd C j 1 - n ∉ M))
    (hval : ∀ j < C.gates.length, j ∉ insert h M → ∀ x,
      V x (n + j) = (gateAt C j).op.eval [V x (opnd C j 0), V x (opnd C j 1)])
    (houtput : ∀ x, V x C.output = graphFun G ∅ x)
    (hgval : ∀ x, V x (n + g) = gateVal n C g x)
    (hclean : ∀ j < C.gates.length, j ∉ insert h M → j ≠ g →
      (gateAt C j).op = GateOp.and → ∀ x, V x (n + j) = true → graphFun G ∅ x = true)
    (block : ∀ (gs : List Gate) (m : ℕ → ℕ), Ok n gs → Maps n h M gs m V →
      ∃ (hs : List Gate) (o : ℕ), Ok n (gs ++ hs) ∧ hs.length ≤ M.card + 1 ∧
        o < n + (gs ++ hs).length ∧
        (∀ x : Fin n → Bool, (run (gs ++ hs) (List.ofFn x)).getD o false = V x (n + h)) ∧
        dc n (graphFun G ∅) (gs ++ hs) ≤ dc n (graphFun G ∅) gs) : False := by
  classical
  have hglen : g < C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hgJ).1
  have hgdirty := (Finset.mem_filter.mp hgJ).2
  change (gateAt C g).op = GateOp.and ∧ g < C.gates.length ∧
    ∃ x, gateVal n C g x = true ∧ graphFun G ∅ x = false at hgdirty
  have hnotM : h ∉ M := by intro hmem; have := hM h hmem; omega
  have hMrange : M ⊆ Finset.range C.gates.length := by
    intro j hj
    exact Finset.mem_range.mpr (lt_trans (hM j hj) hh)
  have hdirty : ∃ x, V x (n + g) = true ∧ graphFun G ∅ x = false := by
    obtain ⟨x, hx, hFx⟩ := hgdirty.2.2
    exact ⟨x, (hgval x).trans hx, hFx⟩
  apply one_junk_splice_impossible G C hL rungOne h g M hh hnotM hMrange
    (Alias.least_output_valid G C hL g hglen) houtM
    (fun j => (gateAt C j).op) (fun j => opnd C j 0) (fun j => opnd C j 1)
    V hin (fun j hj => (Alias.gate_pair hL.1 hj).2.2.2.2)
    (fun j hj => ⟨(Alias.gate_pair hL.1 hj).2.2.1, (Alias.gate_pair hL.1 hj).2.2.2.1⟩)
    havoid hval houtput hglen hgkeep hgdirty.1 hdirty hclean block

end Splice

namespace SemanticPatch

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

lemma valuation_mono {n : ℕ} (C : Circuit) (h : ℕ)
    (R : (Fin n → Bool) → Bool) (V : (Fin n → Bool) → ℕ → Bool)
    (hAO : IsAO2 n C)
    (hin : ∀ x w, w < n → V x w = (List.ofFn x).getD w false)
    (hh : ∀ x, V x (n + h) = R x)
    (heq : ∀ j, j < C.gates.length → j ≠ h → ∀ x,
      V x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (V x)))
    (hmonoR : ∀ x y, (∀ u, x u = true → y u = true) → R x = true → R y = true) :
    ∀ x y, (∀ u, x u = true → y u = true) →
      ∀ w, w < n + C.gates.length → V x w = true → V y w = true := by
  intro x y hxy w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hv
    by_cases hwn : w < n
    · rw [hin x w hwn] at hv
      rw [hin y w hwn]
      exact (ofFn_mono hxy).2 w hv
    · have hj : w - n < C.gates.length := by omega
      have ew : w = n + (w - n) := by omega
      by_cases he : w - n = h
      · have eh : w = n + h := by omega
        rw [eh, hh] at hv ⊢
        exact hmonoR x y hxy hv
      · have hop := hAO.1 _ (Mixed.gateAt_mem' C (w - n) hj)
        rw [ew, heq (w - n) hj he x] at hv
        rw [ew, heq (w - n) hj he y]
        rcases hop with hand | hor
        · simp only [hand, GateOp.eval, List.all_map, List.all_eq_true,
            Function.comp_apply, id_eq] at hv ⊢
          intro i hi
          have hib := hAO.2.1 (w - n) hj i hi
          exact ih i (by omega) (by omega) (hv i hi)
        · simp only [hor, GateOp.eval, List.any_map, List.any_eq_true,
            Function.comp_apply, id_eq] at hv ⊢
          obtain ⟨i, hi, hiv⟩ := hv
          have hib := hAO.2.1 (w - n) hj i hi
          exact ⟨i, hi, ih i (by omega) (by omega) hiv⟩

end SemanticPatch

namespace SemanticPatch

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
  PEqualNP.Outside.L_meta_5012_aux.Mixed

def constGate (b : Bool) : Gate := if b then ⟨GateOp.and, []⟩ else off

lemma const_bit (ws : List Bool) (b : Bool) : gateBit ws (constGate b) = b := by
  cases b <;> rfl

def values {n : ℕ} (C : Circuit) (h : ℕ) (R : (Fin n → Bool) → Bool)
    (x : Fin n → Bool) (w : ℕ) : Bool :=
  wireVal n (patch C h (constGate (R x))) w x

lemma values_input {n : ℕ} (C : Circuit) (h : ℕ) (R : (Fin n → Bool) → Bool)
    (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    values C h R x w = (List.ofFn x).getD w false := by
  unfold values wireVal Circuit.wires
  exact fold_getD_lt _ _ w (by simpa using hw)

lemma values_at {n : ℕ} (C : Circuit) (h : ℕ) (R : (Fin n → Bool) → Bool)
    (hh : h < C.gates.length) (x : Fin n → Bool) : values C h R x (n + h) = R x := by
  change gateVal n (patch C h (constGate (R x))) h x = R x
  rw [patch_bit hh, const_bit]

lemma values_gate {n : ℕ} (C : Circuit) (h : ℕ) (R : (Fin n → Bool) → Bool)
    (hAO : IsAO2 n C) (j : ℕ) (hj : j < C.gates.length) (hne : j ≠ h)
    (x : Fin n → Bool) :
    values C h R x (n + j) =
      (gateAt C j).op.eval ((gateAt C j).inputs.map (values C h R x)) := by
  change W n (patch C h (constGate (R x))) x (n + j) = _
  rw [W_gate n (patch C h (constGate (R x))) x j (by simpa [patch] using hj),
    gateAt_patch_ne C h j _ hne.symm]
  congr 1
  apply List.map_congr_left
  intro w hw
  rw [ite_eq_left (hAO.2.1 j hj w hw)]
  rfl

lemma values_preserve_of_notCone {n : ℕ} (C : Circuit) (h g : ℕ)
    (R : (Fin n → Bool) → Bool) (hAO : IsAO2 n C) (hg : g < C.gates.length)
    (hne : h ≠ g) (hcone : ¬ InCone n C h g) (x : Fin n → Bool) :
    values C h R x (n + g) = gateVal n C g x := by
  exact gate_unchanged_of_notCone hAO h g _ hg hne hcone x

lemma values_preserve_before {n : ℕ} (C : Circuit) (h g : ℕ)
    (R : (Fin n → Bool) → Bool) (hh : h < C.gates.length) (hgh : g < h)
    (x : Fin n → Bool) : values C h R x (n + g) = gateVal n C g x := by
  exact gateVal_patch_before hh hgh _ x

lemma values_down {n : ℕ} (C : Circuit) (h : ℕ) (R : (Fin n → Bool) → Bool)
    (hAO : IsAO2 n C) (hh : h < C.gates.length)
    (x : Fin n → Bool) (hR : R x = false) (w : ℕ)
    (hv : values C h R x w = true) : wireVal n C w x = true := by
  have hle := patch_mono (ao_mono hAO) hh (constGate (R x)) C.gates[h] (List.ofFn x)
    (by rw [const_bit, hR]; intro he; cases he)
  rw [original_patch hh] at hle
  exact hle.2 w hv

lemma values_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (hAO : IsAO2 n C) (hTop : TopForm G C) (hF : circuitFun n C = graphFun G ∅)
    (g h : ℕ) (hJ : junk G C = {g, h})
    (hmix : ∀ c : Bool, gateVal n C h (monoInput s c) = true)
    (R : (Fin n → Bool) → Bool)
    (preserve : ∀ x, values C h R x (n + g) = gateVal n C g x)
    (guarded : ∀ x, gateVal n C g x = true → R x = true → graphFun G ∅ x = true)
    (x : Fin n → Bool) (hxF : graphFun G ∅ x = false) :
    values C h R x C.output = false := by
  have hhJ : h ∈ junk G C := by simp [hJ]
  have hh := (mem_junk.mp hhJ).1
  cases hxg : gateVal n C g x with
  | false =>
    exact output_false_under_guard G C s hcol hAO hTop hF g h hJ hmix
      (constGate (R x)) x hxF ((preserve x).trans hxg)
  | true =>
    have hR : R x = false := by
      cases hr : R x with
      | false => rfl
      | true => have hf := guarded x hxg hr; rw [hxF] at hf; cases hf
    cases hv : values C h R x C.output with
    | false => rfl
    | true =>
      have ho := values_down C h R hAO hh x hR C.output hv
      change circuitFun n C x = true at ho
      rw [hF, hxF] at ho
      cases ho

lemma values_clean {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (hAO : IsAO2 n C) (hTop : TopForm G C)
    (g h : ℕ) (hJ : junk G C = {g, h})
    (hmix : ∀ c : Bool, gateVal n C h (monoInput s c) = true)
    (R : (Fin n → Bool) → Bool)
    (preserve : ∀ x, values C h R x (n + g) = gateVal n C g x)
    (guarded : ∀ x, gateVal n C g x = true → R x = true → graphFun G ∅ x = true)
    (t : ℕ) (ht : t < C.gates.length) (htand : (gateAt C t).op = GateOp.and)
    (htbelow : BelowF G C t) (x : Fin n → Bool)
    (hv : values C h R x (n + t) = true) : graphFun G ∅ x = true := by
  have hhJ : h ∈ junk G C := by simp [hJ]
  have hh := (mem_junk.mp hhJ).1
  cases hxF : graphFun G ∅ x with
  | true => rfl
  | false =>
    cases hxg : gateVal n C g x with
    | false =>
      have hf := clean_and_false_under_guard G C s hcol hAO hTop g h hJ hmix
        (constGate (R x)) x hxF ((preserve x).trans hxg) t ht htand htbelow
      change values C h R x (n + t) = false at hf
      rw [hf] at hv
      cases hv
    | true =>
      have hR : R x = false := by
        cases hr : R x with
        | false => rfl
        | true => have hf := guarded x hxg hr; rw [hxF] at hf; cases hf
      have hf := htbelow x (values_down C h R hAO hh x hR (n + t) hv)
      rw [hxF] at hf
      cases hf

lemma values_edge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hF : circuitFun n C = graphFun G ∅)
    (h : ℕ) (hh : h < C.gates.length) (R : (Fin n → Bool) → Bool)
    (critical : ∀ a b, G.Adj a b → circuitFun n (patch C h off) (pairInput a b) = false →
      R (pairInput a b) = true)
    (a b : Fin n) (hab : G.Adj a b) : values C h R (pairInput a b) C.output = true := by
  cases hcut : circuitFun n (patch C h off) (pairInput a b) with
  | true =>
    exact (patch_mono (ao_mono hAO) hh off (constGate (R (pairInput a b)))
      (List.ofFn (pairInput a b)) (by simp [off_bit])).2 C.output hcut
  | false =>
    have hle := patch_mono (ao_mono hAO) hh C.gates[h] (constGate (R (pairInput a b)))
      (List.ofFn (pairInput a b)) (by intro _; rw [const_bit]; exact critical a b hab hcut)
    rw [original_patch hh] at hle
    apply hle.2 C.output
    change circuitFun n C (pairInput a b) = true
    rw [hF]
    exact (graph_true G (pairInput a b)).mpr
      ⟨a, b, hab, by simp [pairInput], by simp [pairInput]⟩

end SemanticPatch

namespace SemanticPatch

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
  PEqualNP.Outside.L_meta_5012_aux.Mixed

lemma values_before {n : ℕ} (C : Circuit) (h : ℕ) (R : (Fin n → Bool) → Bool)
    (hh : h < C.gates.length) (x : Fin n → Bool) (w : ℕ) (hw : w < n + h) :
    values C h R x w = wireVal n C w x := by
  by_cases hwn : w < n
  · change W n (patch C h (constGate (R x))) x w = W n C x w
    rw [W_input n (patch C h (constGate (R x))) x w hwn, W_input n C x w hwn]
  · have heq : w = n + (w - n) := by omega
    rw [heq]
    exact values_preserve_before C h (w - n) R hh (by omega) x

lemma values_pair {n : ℕ} (C : Circuit) (h : ℕ) (R : (Fin n → Bool) → Bool)
    (hAO : IsAO2 n C) (j : ℕ) (hj : j < C.gates.length) (hne : j ≠ h)
    (x : Fin n → Bool) :
    values C h R x (n + j) = (gateAt C j).op.eval
      [values C h R x (opnd C j 0), values C h R x (opnd C j 1)] := by
  rw [values_gate C h R hAO j hj hne]
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem' C j hj))
  simp [hab, opnd]

lemma values_mono {n : ℕ} (C : Circuit) (h : ℕ) (R : (Fin n → Bool) → Bool)
    (hAO : IsAO2 n C) (hh : h < C.gates.length)
    (hmonoR : ∀ x y, (∀ u, x u = true → y u = true) → R x = true → R y = true) :
    ∀ x y, (∀ u, x u = true → y u = true) →
      ∀ w, w < n + C.gates.length → values C h R x w = true → values C h R y w = true := by
  exact valuation_mono C h R (values C h R) hAO (values_input C h R)
    (values_at C h R hh) (values_gate C h R hAO) hmonoR

lemma values_compute {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (hAO : IsAO2 n C) (hTop : TopForm G C) (hF : circuitFun n C = graphFun G ∅)
    (hout : C.output < n + C.gates.length)
    (g h : ℕ) (hJ : junk G C = {g, h})
    (hmix : ∀ c : Bool, gateVal n C h (monoInput s c) = true)
    (R : (Fin n → Bool) → Bool)
    (hmonoR : ∀ x y, (∀ u, x u = true → y u = true) → R x = true → R y = true)
    (preserve : ∀ x, values C h R x (n + g) = gateVal n C g x)
    (guarded : ∀ x, gateVal n C g x = true → R x = true → graphFun G ∅ x = true)
    (critical : ∀ a b, G.Adj a b → circuitFun n (patch C h off) (pairInput a b) = false →
      R (pairInput a b) = true) :
    ∀ x, values C h R x C.output = graphFun G ∅ x := by
  have hhJ : h ∈ junk G C := by simp [hJ]
  have hh := (mem_junk.mp hhJ).1
  intro x
  cases hxF : graphFun G ∅ x with
  | true =>
    obtain ⟨a, b, hab, ha, hb⟩ := (graph_true G x).mp hxF
    exact values_mono C h R hAO hh hmonoR (pairInput a b) x (pair_le ha hb) C.output hout
      (values_edge G C hAO hF h hh R critical a b hab)
  | false => exact values_false G C s hcol hAO hTop hF g h hJ hmix R preserve guarded x hxF


end SemanticPatch

namespace SemanticPatch

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
  PEqualNP.Outside.L_meta_5012_aux.Mixed

lemma values_clean_except {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (hAO : IsAO2 n C) (hTop : TopForm G C)
    (g h : ℕ) (hJ : junk G C = {g, h})
    (hmix : ∀ c : Bool, gateVal n C h (monoInput s c) = true)
    (R : (Fin n → Bool) → Bool)
    (preserve : ∀ x, values C h R x (n + g) = gateVal n C g x)
    (guarded : ∀ x, gateVal n C g x = true → R x = true → graphFun G ∅ x = true)
    (j : ℕ) (hj : j < C.gates.length) (hjg : j ≠ g) (hjh : j ≠ h)
    (hand : (gateAt C j).op = GateOp.and) (x : Fin n → Bool)
    (hv : values C h R x (n + j) = true) : graphFun G ∅ x = true := by
  rcases and_junk_or_below (G := G) hj hand with hdirty | hbelow
  · simp [hJ, hjg, hjh] at hdirty
  · exact values_clean G C s hcol hAO hTop g h hJ hmix R preserve guarded j hj hand hbelow x hv

end SemanticPatch

namespace SemanticPatch

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
  PEqualNP.Outside.L_meta_5012_aux.Mixed

lemma mixed_semantic_splice_impossible {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (hL : IsLeastAO G C) (hTop : TopForm G C)
    (rungOne : ∀ D : Circuit, IsLeastAO G D → (junk G D).card = 1 → False)
    (g h : ℕ) (hJ : junk G C = {g, h})
    (hindhg : ¬ InCone n C h g)
    (hmix : ∀ c : Bool, gateVal n C h (monoInput s c) = true)
    (M : Finset ℕ) (hM : ∀ j ∈ M, j < h) (hgkeep : g ∉ insert h M)
    (houtM : C.output < n ∨ C.output - n ∉ M)
    (havoid : ∀ j < C.gates.length, j ∉ insert h M →
      (opnd C j 0 < n ∨ opnd C j 0 - n ∉ M) ∧
      (opnd C j 1 < n ∨ opnd C j 1 - n ∉ M))
    (R : (Fin n → Bool) → Bool)
    (hmonoR : ∀ x y, (∀ u, x u = true → y u = true) → R x = true → R y = true)
    (guarded : ∀ x, gateVal n C g x = true → R x = true → graphFun G ∅ x = true)
    (critical : ∀ a b, G.Adj a b → circuitFun n (patch C h off) (pairInput a b) = false →
      R (pairInput a b) = true)
    (block : ∀ (gs : List Gate) (m : ℕ → ℕ), Splice.Ok n gs →
      Splice.Maps n h M gs m (values C h R) →
      ∃ (hs : List Gate) (o : ℕ), Splice.Ok n (gs ++ hs) ∧ hs.length ≤ M.card + 1 ∧
        o < n + (gs ++ hs).length ∧
        (∀ x : Fin n → Bool, (Splice.run (gs ++ hs) (List.ofFn x)).getD o false = R x) ∧
        Splice.dc n (graphFun G ∅) (gs ++ hs) ≤ Splice.dc n (graphFun G ∅) gs) : False := by
  have hhJ : h ∈ junk G C := by simp [hJ]
  have hgJ : g ∈ junk G C := by simp [hJ]
  have hh := (mem_junk.mp hhJ).1
  have hg := (mem_junk.mp hgJ).1
  have hne : h ≠ g := by
    intro heq
    apply hgkeep
    simp [heq]
  have preserve (x : Fin n → Bool) : values C h R x (n + g) = gateVal n C g x :=
    values_preserve_of_notCone C h g R hL.1 hg hne hindhg x
  have keep_ne (j : ℕ) (hj : j ∉ insert h M) : j ≠ h := by
    intro heq
    apply hj
    simp [heq]
  apply Splice.actual_one_junk_splice_impossible G C hL rungOne h g M hh hM hgkeep hgJ
    houtM (values C h R) (values_input C h R) havoid
    (fun j hj hkeep x => values_pair C h R hL.1 j hj (keep_ne j hkeep) x)
    (values_compute G C s hcol hL.1 hTop hL.2.1
      (Alias.least_output_valid G C hL h hh) g h hJ hmix R hmonoR preserve guarded critical)
    preserve
    (fun j hj hkeep hjg hand x hv => values_clean_except G C s hcol hL.1 hTop g h hJ hmix
      R preserve guarded j hj hjg (keep_ne j hkeep) hand x hv)
  intro gs m hok hm
  obtain ⟨hs, o, hOK, hlen, hout, hvalue, hdc⟩ := block gs m hok hm
  exact ⟨hs, o, hOK, hlen, hout, fun x => (hvalue x).trans (values_at C h R hh x).symm, hdc⟩

end SemanticPatch

namespace ActualCut

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
  PEqualNP.Outside.L_meta_5012_aux.Mixed

open Classical in
noncomputable def removed (n : ℕ) (C : Circuit) (s : Fin n → Bool) (h : ℕ) : Finset ℕ :=
  (Finset.range h).filter fun e => InCone n C e h ∧ (gateAt C e).op = GateOp.or ∧
    ∀ c : Bool, gateVal n C e (monoInput s c) = true

noncomputable def wires (n : ℕ) (C : Circuit) (s : Fin n → Bool) (h : ℕ) : Finset ℕ :=
  (removed n C s h).image (fun e => n + e)

lemma mem_removed {n : ℕ} {C : Circuit} {s : Fin n → Bool} {h e : ℕ} :
    e ∈ removed n C s h ↔ e < h ∧ InCone n C e h ∧
      (gateAt C e).op = GateOp.or ∧ ∀ c : Bool, gateVal n C e (monoInput s c) = true := by
  classical
  simp only [removed, Finset.mem_filter, Finset.mem_range]

lemma mem_wires {n : ℕ} {C : Circuit} {s : Fin n → Bool} {h w : ℕ} :
    w ∈ wires n C s h ↔ ∃ e ∈ removed n C s h, w = n + e := by
  simp only [wires, Finset.mem_image]
  exact exists_congr fun e => and_congr_right fun _ => eq_comm

lemma cut_isOrCut {n : ℕ} {C : Circuit} {s : Fin n → Bool} {h : ℕ}
    (hh : h < C.gates.length) : ORCut.IsOrCut n C (wires n C s h) := by
  intro w hw
  obtain ⟨e, he, rfl⟩ := mem_wires.mp hw
  obtain ⟨heh, _, heor, _⟩ := mem_removed.mp he
  exact ⟨by omega, by omega, by simpa using heor⟩

lemma cut_indices (n : ℕ) (C : Circuit) (s : Fin n → Bool) (h : ℕ) :
    (wires n C s h).image (fun q => q - n) = removed n C s h := by
  classical
  simp [wires, Finset.image_image, Function.comp_def]

lemma inside_cone_orReach {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {h : ℕ}
    (hnoand : ∀ k, InCone n C k h → (gateAt C k).op ≠ GateOp.and) (e : ℕ) :
    ∀ k, InCone n C k h → (e = k ∨ InCone n C e k) → OrReaches n C (n + k) e := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hkh hek
    have hk : k < C.gates.length := by
      have := inCone_lt n C h k hkh
      have := ((inCone_iff n C k h).mp hkh).1
      omega
    rcases hek with rfl | hek
    · exact orReach_self n C e hk
    · obtain ⟨_, p, hpk, hpinput, hep⟩ := (inCone_iff n C e k).mp hek
      have hpkcone : InCone n C p k :=
        (inCone_iff n C p k).mpr ⟨hk, p, hpk, hpinput, Or.inl rfl⟩
      have hph := cone_trans hpkcone hkh
      have hpor := ih p hpk hph hep
      have hkor : (gateAt C k).op = GateOp.or :=
        (hAO.1 _ (gateAt_mem' C k hk)).resolve_left (hnoand k hkh)
      exact orReach_trans n C k hk hkor (n + p) hpinput (by omega) e hpor

lemma cone_reaches_operand {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {h e : ℕ}
    (hnoand : ∀ k, InCone n C k h → (gateAt C k).op ≠ GateOp.and)
    (heh : InCone n C e h) : ∃ b : Fin 2, OrReaches n C (opnd C h b) e := by
  obtain ⟨hh, p, hph, hpinput, hep⟩ := (inCone_iff n C e h).mp heh
  have hpc : InCone n C p h :=
    (inCone_iff n C p h).mpr ⟨hh, p, hph, hpinput, Or.inl rfl⟩
  obtain ⟨b, hb⟩ := (mem_inputs_iff_opnd hAO hh (n + p)).mp hpinput
  refine ⟨b, ?_⟩
  rw [hb]
  exact inside_cone_orReach hAO hnoand e p hpc hep

lemma mixed_reach_path {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {s : Fin n → Bool} {h e : ℕ}
    (hemix : ∀ c : Bool, gateVal n C e (monoInput s c) = true) :
    ∀ w, InsideWire n C h w → OrReaches n C w e →
      Relation.ReflTransGen (ORCut.step (wires n C s h)
        (ORCut.leftWire n C) (ORCut.rightWire n C)) (n + e) w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hwi hr
    obtain ⟨k, rfl, hkh⟩ := hwi.resolve_left (by have := hr.1; omega)
    have hkhlt := inCone_lt n C h k hkh
    have hh := ((inCone_iff n C k h).mp hkh).1
    have hk : k < C.gates.length := by omega
    have hmem : e ∈ (orSets n C).getD k [] := by simpa using hr.2
    rcases (orSets_mem_iff n C k e hk).mp hmem with rfl | ⟨hkor, v, hv, hvn, hvk, hev⟩
    · exact Relation.ReflTransGen.refl
    · have hvm : OrReaches n C v e := ⟨hvn, hev⟩
      have hvi := operand_inside hAO hk (Or.inr hkh) v hv
      have hpath := ih v hvk hvi hvm
      have hkmix : ∀ c : Bool, gateVal n C k (monoInput s c) = true := by
        intro c
        exact reach_up n C (monoInput s c) (n + k) e hr (hemix c)
      have hkQ : n + k ∈ wires n C s h :=
        mem_wires.mpr ⟨k, mem_removed.mpr ⟨hkhlt, hkh, hkor, hkmix⟩, rfl⟩
      obtain ⟨b, hb⟩ := (mem_inputs_iff_opnd hAO hk v).mp hv
      apply Relation.ReflTransGen.tail hpath
      refine ⟨hkQ, ?_⟩
      fin_cases b
      · left; simpa [ORCut.leftWire] using hb.symm
      · right; simpa [ORCut.rightWire] using hb.symm

lemma cut_root_paths {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {s : Fin n → Bool} {h : ℕ}
    (hnoand : ∀ k, InCone n C k h → (gateAt C k).op ≠ GateOp.and) :
    ∀ q ∈ wires n C s h,
      Relation.ReflTransGen (ORCut.step (wires n C s h)
        (ORCut.leftWire n C) (ORCut.rightWire n C)) q (opnd C h 0) ∨
      Relation.ReflTransGen (ORCut.step (wires n C s h)
        (ORCut.leftWire n C) (ORCut.rightWire n C)) q (opnd C h 1) := by
  intro q hq
  obtain ⟨e, he, rfl⟩ := mem_wires.mp hq
  obtain ⟨_, heh, _, hemix⟩ := mem_removed.mp he
  have hh := ((inCone_iff n C e h).mp heh).1
  obtain ⟨b, hb⟩ := cone_reaches_operand hAO hnoand heh
  have hi := operand_inside hAO hh (Or.inl rfl) (opnd C h b) (opnd_mem hAO hh b)
  have hp := mixed_reach_path hAO hemix _ hi hb
  fin_cases b
  · exact Or.inl hp
  · exact Or.inr hp

lemma path_inside {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {s : Fin n → Bool} {h u r : ℕ}
    (hp : Relation.ReflTransGen (ORCut.step (wires n C s h)
      (ORCut.leftWire n C) (ORCut.rightWire n C)) u r) :
    InsideWire n C h r → InsideWire n C h u := by
  induction hp with
  | refl => exact id
  | @tail v w hp hw ih =>
    intro _
    obtain ⟨hwQ, hwchild⟩ := hw
    obtain ⟨e, he, rfl⟩ := mem_wires.mp hwQ
    obtain ⟨_, heh, _, _⟩ := mem_removed.mp he
    have hh := ((inCone_iff n C e h).mp heh).1
    have hel := inCone_lt n C h e heh
    have heC : e < C.gates.length := by omega
    apply ih
    rcases hwchild with rfl | rfl
    · simpa [ORCut.leftWire] using
        operand_inside hAO heC (Or.inr heh) (opnd C e 0) (opnd_mem hAO heC 0)
    · simpa [ORCut.rightWire] using
        operand_inside hAO heC (Or.inr heh) (opnd C e 1) (opnd_mem hAO heC 1)

end ActualCut

namespace ActualCut

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
  PEqualNP.Outside.L_meta_5012_aux.Mixed

lemma boundary_homogeneous {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {s : Fin n → Bool} {h u : ℕ}
    (hnoand : ∀ k, InCone n C k h → (gateAt C k).op ≠ GateOp.and)
    (hu : InsideWire n C h u) (huQ : u ∉ wires n C s h) :
    (orIn n C u).Nonempty ∧ (∃ c : Bool, ∀ v ∈ orIn n C u, s v = c) ∧
      ∀ x : Fin n → Bool, wireVal n C u x = decide (∃ v ∈ orIn n C u, x v = true) := by
  have hsem := inside_pure_or hAO hnoand hu
  have hub : u < n + C.gates.length := by
    rcases hu with hraw | ⟨e, rfl, heh⟩
    · omega
    · have := inCone_lt n C h e heh
      have := ((inCone_iff n C e h).mp heh).1
      omega
  have hnon : (orIn n C u).Nonempty := by
    have ht := wire_all_true hAO u hub
    change wireVal n C u (fun _ => true) = true at ht
    rw [hsem] at ht
    obtain ⟨v, hv, _⟩ := of_decide_eq_true ht
    exact ⟨v, hv⟩
  have hnotmix : ¬ ∀ c : Bool, wireVal n C u (monoInput s c) = true := by
    intro hmix
    have hnotraw : ¬ u < n := mixed_wire_not_input hmix
    obtain ⟨e, rfl, heh⟩ := hu.resolve_left hnotraw
    have hel := inCone_lt n C h e heh
    have hh := ((inCone_iff n C e h).mp heh).1
    have he : e < C.gates.length := by omega
    have hor := (hAO.1 _ (gateAt_mem' C e he)).resolve_left (hnoand e heh)
    exact huQ (mem_wires.mpr ⟨e, mem_removed.mpr ⟨hel, heh, hor, hmix⟩, rfl⟩)
  push Not at hnotmix
  obtain ⟨c, hc⟩ := hnotmix
  have hcolors : ∀ v ∈ orIn n C u, s v = !c := by
    intro v hv
    have hne : s v ≠ c := by
      intro heq
      apply hc
      rw [hsem]
      apply decide_eq_true
      exact ⟨v, hv, by simp [monoInput, heq]⟩
    cases hc' : c <;> cases hs : s v <;> simp_all
  exact ⟨hnon, ⟨!c, hcolors⟩, hsem⟩

lemma cut_private {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (s : Fin n → Bool) (hcol : ∀ a b, G.Adj a b → s a ≠ s b)
    (h4 : NoFourCycle G) (hL : IsLeastAO G C) (hTop : TopForm G C)
    (g h : ℕ) (hne : h ≠ g) (hindgh : ¬ InCone n C g h) (hindhg : ¬ InCone n C h g)
    (hJ : junk G C = {g, h})
    (hmix : ∀ c : Bool, gateVal n C h (monoInput s c) = true)
    (gzero : ∀ c : Bool, gateVal n C g (monoInput s c) = false)
    (hA : 2 ≤ (side (n := n) C g 0).card) (hB : 2 ≤ (side (n := n) C g 1).card)
    (hd : Disjoint (side (n := n) C g 0) (side (n := n) C g 1)) :
    ∀ t < C.gates.length, t ∉ insert h (removed n C s h) → ∀ b : Fin 2,
      opnd C t b < n ∨ opnd C t b - n ∉ removed n C s h := by
  intro t ht hkeep b
  by_cases hb : opnd C t b < n
  · exact Or.inl hb
  · right
    intro hmem
    obtain ⟨_, heh, _, hemix⟩ := mem_removed.mp hmem
    have heq : n + (opnd C t b - n) = opnd C t b := by omega
    have hread : n + (opnd C t b - n) ∈ (gateAt C t).inputs := by
      rw [heq]; exact opnd_mem hL.1 ht b
    rcases mixed_or_reader_closure G C s hcol h4 hL hTop g h hne hindgh hindhg
      hJ hmix gzero hA hB hd _ heh hemix t ht hread with rfl | ⟨hth, htor, htmix⟩
    · exact hkeep (Finset.mem_insert_self _ _)
    · exact hkeep (Finset.mem_insert_of_mem (mem_removed.mpr
        ⟨inCone_lt n C h t hth, hth, htor, htmix⟩))

lemma output_kept {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (s : Fin n → Bool) (hcol : ∀ a b, G.Adj a b → s a ≠ s b)
    (hF : circuitFun n C = graphFun G ∅) (h : ℕ) :
    C.output < n ∨ C.output - n ∉ removed n C s h := by
  by_cases ho : C.output < n
  · exact Or.inl ho
  · right
    intro hmem
    obtain ⟨_, heh, _, hemix⟩ := mem_removed.mp hmem
    have he := inCone_lt n C h (C.output - n) heh
    have hh := ((inCone_iff n C (C.output - n) h).mp heh).1
    have hbound : C.output - n < C.gates.length := by omega
    have heq : C.output = n + (C.output - n) := by omega
    have hr : OrReaches n C C.output (C.output - n) := by
      conv_lhs => rw [heq]
      exact orReach_self n C _ hbound
    exact output_not_reaches_mixed hcol hF hemix hr

end ActualCut

namespace ActualCut

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
  PEqualNP.Outside.L_meta_5012_aux.Mixed

noncomputable def boundary (n : ℕ) (C : Circuit) (s : Fin n → Bool) (h : ℕ)
    (b : Fin 2) : Finset ℕ :=
  ORCut.frontier (wires n C s h) (ORCut.leftWire n C) (ORCut.rightWire n C) (opnd C h b)

def CutData (n : ℕ) (C : Circuit) (s : Fin n → Bool) (g h : ℕ) : Prop :=
  h < C.gates.length ∧
  h ∉ removed n C s h ∧
  (∀ e ∈ removed n C s h, e < h) ∧
  (∀ e ∈ removed n C s h, (gateAt C e).op = GateOp.or) ∧
  g ∉ insert h (removed n C s h) ∧
  (∀ e ∈ removed n C s h, e ≠ g ∧ ¬ InCone n C e g) ∧
  (C.output < n ∨ C.output - n ∉ removed n C s h) ∧
  (∀ t < C.gates.length, t ∉ insert h (removed n C s h) →
    ∀ b : Fin 2, opnd C t b < n ∨ opnd C t b - n ∉ removed n C s h) ∧
  ORCut.IsOrCut n C (wires n C s h) ∧
  (wires n C s h).image (fun q => q - n) = removed n C s h ∧
  (∀ b : Fin 2, (boundary n C s h b).Nonempty) ∧
  (∀ b : Fin 2, ∀ u ∈ boundary n C s h b,
    u < n + h ∧ (u < n ∨ u - n ∉ removed n C s h)) ∧
  (∀ b : Fin 2, ∀ u ∈ boundary n C s h b,
    (orIn n C u).Nonempty ∧ (∃ c : Bool, ∀ v ∈ orIn n C u, s v = c) ∧
      ∀ x : Fin n → Bool, wireVal n C u x = decide (∃ v ∈ orIn n C u, x v = true)) ∧
  (boundary n C s h 0 ∪ boundary n C s h 1).card -
    (if Disjoint (boundary n C s h 0) (boundary n C s h 1) then 2 else 1) ≤
      (removed n C s h).card ∧
  (∀ b : Fin 2, ∀ x : Fin n → Bool,
    wireVal n C (opnd C h b) x =
      decide (∃ u ∈ boundary n C s h b, wireVal n C u x = true))

lemma actual_mixed_cut {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (s : Fin n → Bool) (hcol : ∀ a b, G.Adj a b → s a ≠ s b)
    (h4 : NoFourCycle G) (hL : IsLeastAO G C) (hTop : TopForm G C)
    (g h : ℕ) (hne : h ≠ g) (hindgh : ¬ InCone n C g h) (hindhg : ¬ InCone n C h g)
    (hJ : junk G C = {g, h})
    (hmix : ∀ c : Bool, gateVal n C h (monoInput s c) = true) :
    CutData n C s g h := by
  classical
  have hhJ : h ∈ junk G C := by simp [hJ]
  have hh := (mem_junk.mp hhJ).1
  have hnoand := no_and_below_independent_junk hTop hJ hindgh
  have hQ := cut_isOrCut (s := s) hh
  have hback := ORCut.circuit_backward hL.1 hQ
  have hroots := cut_root_paths (s := s) hL.1 hnoand
  have hdata := ORCut.circuit_cut_data hL.1 hQ h (opnd C h 0) (opnd C h 1)
    (opnd_lt hL.1 hh 0) (opnd_lt hL.1 hh 1) hroots
  dsimp only at hdata
  rw [cut_indices] at hdata
  obtain ⟨hS, hT, _, _, hbkeep, hcost, hsem⟩ := hdata
  have hsetup := MixedSetup.independent_mixed_setup G C s hcol hL hTop
    g h hne hindgh hindhg hJ hmix
  dsimp only at hsetup
  obtain ⟨hA, hB, hd, _⟩ := hsetup
  have gzero := NestedMixed.other_false_on_monochrome G C s hcol hL hTop
    g h hne hindhg hJ hmix
  have hgnot : g ∉ removed n C s h := fun hg => hindgh (mem_removed.mp hg).2.1
  refine ⟨hh, ?_, ?_, ?_, ?_, ?_, output_kept G C s hcol hL.2.1 h,
    cut_private G C s hcol h4 hL hTop g h hne hindgh hindhg hJ hmix gzero hA hB hd,
    hQ, cut_indices n C s h, ?_, ?_, ?_, hcost, ?_⟩
  · exact fun hm => (Nat.lt_irrefl h) (mem_removed.mp hm).1
  · intro e he; exact (mem_removed.mp he).1
  · intro e he; exact (mem_removed.mp he).2.2.1
  · simpa only [Finset.mem_insert, not_or] using And.intro (Ne.symm hne) hgnot
  · intro e he
    refine ⟨fun heq => hgnot (heq ▸ he), ?_⟩
    intro heg
    have hJswap : junk G C = {h, g} := by simpa [Finset.pair_comm] using hJ
    have hnag := no_and_below_independent_junk hTop hJswap hindhg
    obtain ⟨b, hb⟩ := cone_reaches_operand hL.1 hnag heg
    exact pure_junk_no_mixed_operand G C s hL.1 hTop g h hJ hindhg gzero
      e (mem_removed.mp he).2.2.2 b hb
  · intro b
    fin_cases b
    · exact hS
    · exact hT
  · intro b u hu
    apply hbkeep u
    fin_cases b
    · exact Finset.mem_union_left _ hu
    · exact Finset.mem_union_right _ hu
  · intro b u hu
    have hi := operand_inside hL.1 hh (Or.inl rfl) (opnd C h b) (opnd_mem hL.1 hh b)
    have hpath := (ORCut.mem_frontier (wires n C s h) _ _ hback u (opnd C h b)).mp hu
    exact boundary_homogeneous hL.1 hnoand (path_inside hL.1 hpath.2 hi) hpath.1
  · intro b x
    fin_cases b
    · exact (hsem x).1
    · exact (hsem x).2

end ActualCut



namespace CriticalEdge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

lemma run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega


lemma getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

lemma run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

lemma run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

lemma run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_prefix gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at']
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)



def u (n : ℕ) (A : ℕ → Bool) (a b : ℕ → ℕ) (Del : Finset ℕ) (L : ℕ → List ℕ) (x : List Bool)
    (w : ℕ) : Bool :=
  if w < n then x.getD w false
  else if w - n ∈ Del then false
  else if A (w - n) = true then
    ((if _h : a (w - n) < w then u n A a b Del L x (a (w - n)) else false) ||
      (L (w - n)).any (fun t => x.getD t false)) &&
    (if _h : b (w - n) < w then u n A a b Del L x (b (w - n)) else false)
  else
    (if _h : a (w - n) < w then u n A a b Del L x (a (w - n)) else false) ||
    (if _h : b (w - n) < w then u n A a b Del L x (b (w - n)) else false)
termination_by w

section LocalScope1
variable {n : ℕ} {A : ℕ → Bool} {a b : ℕ → ℕ} {Del : Finset ℕ} {L : ℕ → List ℕ} {x : List Bool}

lemma u_in {w : ℕ} (h : w < n) : u n A a b Del L x w = x.getD w false := by
  rw [u, if_pos h]

lemma u_del {j : ℕ} (h : j ∈ Del) : u n A a b Del L x (n + j) = false := by
  rw [u, if_neg (by omega), Nat.add_sub_cancel_left, if_pos h]

lemma u_and {j : ℕ} (h : j ∉ Del) (hA : A j = true) (ha : a j < n + j) (hb : b j < n + j) :
    u n A a b Del L x (n + j) = ((u n A a b Del L x (a j) ||
      (L j).any (fun t => x.getD t false)) && u n A a b Del L x (b j)) := by
  rw [u, if_neg (by omega), Nat.add_sub_cancel_left, if_neg h, if_pos hA, dif_pos ha, dif_pos hb]

lemma u_or {j : ℕ} (h : j ∉ Del) (hA : A j = false) (ha : a j < n + j) (hb : b j < n + j) :
    u n A a b Del L x (n + j) = (u n A a b Del L x (a j) || u n A a b Del L x (b j)) := by
  rw [u, if_neg (by omega), Nat.add_sub_cancel_left, if_neg h, if_neg (by simp [hA]), dif_pos ha,
    dif_pos hb]
end LocalScope1

def Ok (n : ℕ) (gs : List Gate) : Prop :=
  ∀ j (hj : j < gs.length), ∃ o s t, gs[j] = ⟨o, [s, t]⟩ ∧ (o = GateOp.and ∨ o = GateOp.or) ∧
    s < n + j ∧ t < n + j

lemma ok_snoc {n : ℕ} {gs : List Gate} (h : Ok n gs) {o : GateOp} {s t : ℕ}
    (ho : o = GateOp.and ∨ o = GateOp.or) (hs : s < n + gs.length) (ht : t < n + gs.length) :
    Ok n (gs ++ [⟨o, [s, t]⟩]) := by
  intro j hj
  by_cases hlt : j < gs.length
  · rw [List.getElem_append_left hlt]; exact h j hlt
  · have : j = gs.length := by simp at hj; omega
    subst this
    exact ⟨o, s, t, by simp, ho, hs, ht⟩

open Classical in
noncomputable def dc (n : ℕ) (F : (Fin n → Bool) → Bool) (gs : List Gate) : ℕ :=
  ((Finset.range gs.length).filter fun i => (gs.getD i ⟨GateOp.or, []⟩).op = GateOp.and ∧
    ∃ x : Fin n → Bool, (run gs (List.ofFn x)).getD (n + i) false = true ∧ F x = false).card

open Classical in
lemma dc_snoc (n : ℕ) (F : (Fin n → Bool) → Bool) (gs : List Gate) (g : Gate) :
    dc n F (gs ++ [g]) ≤ dc n F gs + if g.op = GateOp.and ∧
      ∃ x : Fin n → Bool, (run (gs ++ [g]) (List.ofFn x)).getD (n + gs.length) false = true ∧
        F x = false then 1 else 0 := by
  unfold dc
  rw [List.length_append, List.length_singleton, Finset.range_add_one, Finset.filter_insert]
  have e : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
    simp [List.getD_eq_getElem?_getD]
  rw [e]
  have h1 : ((Finset.range gs.length).filter fun i =>
      ((gs ++ [g]).getD i ⟨GateOp.or, []⟩).op = GateOp.and ∧ ∃ x : Fin n → Bool,
        (run (gs ++ [g]) (List.ofFn x)).getD (n + i) false = true ∧ F x = false) =
      (Finset.range gs.length).filter fun i =>
      (gs.getD i ⟨GateOp.or, []⟩).op = GateOp.and ∧ ∃ x : Fin n → Bool,
        (run gs (List.ofFn x)).getD (n + i) false = true ∧ F x = false := by
    refine Finset.filter_congr fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    rw [getD_ltz _ _ _ _ hi']
    refine and_congr_right fun _ => exists_congr fun x => ?_
    rw [run_prefix gs [g] _ _ (by simp; omega)]
  rw [h1]
  split_ifs with h
  · exact (Finset.card_insert_le _ _)
  · simp

def ov (gs : List Gate) (x : List Bool) (o : Option ℕ) : Bool :=
  match o with
  | none => false
  | some w => (run gs x).getD w false

lemma ov_ext (gs hs : List Gate) (x : List Bool) (o : Option ℕ)
    (h : ∀ w, o = some w → w < x.length + gs.length) : ov (gs ++ hs) x o = ov gs x o := by
  cases o with
  | none => rfl
  | some w => exact run_prefix gs hs x w (h w rfl)

lemma ov_new (gs : List Gate) (n : ℕ) (x : List Bool) (hx : x.length = n) (o : GateOp) (s t : ℕ)
    (hs : s < n + gs.length) (ht : t < n + gs.length) :
    ov (gs ++ [⟨o, [s, t]⟩]) x (some (n + gs.length)) =
      o.eval [(run gs x).getD s false, (run gs x).getD t false] := by
  unfold ov
  simp only
  rw [run_snoc]
  have : n + gs.length = (run gs x).length := by rw [run_length, hx]
  rw [this, getD_at]
  rfl

lemma chain (n : ℕ) (F : (Fin n → Bool) → Bool) : ∀ (l : List ℕ), (∀ t ∈ l, t < n) →
    ∀ (gs : List Gate), Ok n gs → ∀ o : Option ℕ, (∀ w, o = some w → w < n + gs.length) →
    ∃ (hs : List Gate) (o' : Option ℕ), Ok n (gs ++ hs) ∧ hs.length ≤ l.length ∧
      dc n F (gs ++ hs) ≤ dc n F gs ∧ (∀ w, o' = some w → w < n + (gs ++ hs).length) ∧
      ∀ x : Fin n → Bool, ov (gs ++ hs) (List.ofFn x) o' =
        (ov gs (List.ofFn x) o || l.any (fun t => (List.ofFn x).getD t false)) := by
  intro l
  induction l with
  | nil =>
    intro _ gs hgs o ho
    exact ⟨[], o, by simpa using hgs, by simp, by simp, by simpa using ho, by simp⟩
  | cons t l ih =>
    intro hl gs hgs o ho
    have ht : t < n := hl t (by simp)
    have hl' : ∀ t ∈ l, t < n := fun s hs => hl s (by simp [hs])
    cases o with
    | none =>
      obtain ⟨hs, o', h1, h2, h3, h4, h5⟩ := ih hl' gs hgs (some t) (by
        intro w hw; cases hw; omega)
      refine ⟨hs, o', h1, by simp; omega, h3, h4, fun x => ?_⟩
      rw [h5 x]
      have : ov gs (List.ofFn x) (some t) = (List.ofFn x).getD t false :=
        run_input _ _ _ (by simpa using ht)
      rw [this]; simp [ov]
    | some w =>
      have hw := ho w rfl
      obtain ⟨hs, o', h1, h2, h3, h4, h5⟩ := ih hl' (gs ++ [⟨GateOp.or, [w, t]⟩])
        (ok_snoc hgs (Or.inr rfl) hw (by omega)) (some (n + gs.length)) (by
          intro w hw; cases hw; simp)
      refine ⟨⟨GateOp.or, [w, t]⟩ :: hs, o', by simpa using h1, by simp; omega, ?_,
        by simpa using h4, fun x => ?_⟩
      · have := dc_snoc n F gs ⟨GateOp.or, [w, t]⟩
        rw [if_neg (by simp)] at this
        have e : gs ++ ⟨GateOp.or, [w, t]⟩ :: hs = gs ++ [⟨GateOp.or, [w, t]⟩] ++ hs := by simp
        rw [e]; omega
      · have e : gs ++ ⟨GateOp.or, [w, t]⟩ :: hs = gs ++ [⟨GateOp.or, [w, t]⟩] ++ hs := by simp
        rw [e, h5 x, ov_new gs n _ (by simp) _ _ _ hw (by omega)]
        rw [run_input gs (List.ofFn x) t (by simpa using ht)]
        simp [ov, GateOp.eval, Bool.or_assoc]

open Classical in
lemma build (n : ℕ) (A : ℕ → Bool) (a b : ℕ → ℕ) (Del R : Finset ℕ) (L : ℕ → List ℕ)
    (F : (Fin n → Bool) → Bool) (hL : ∀ j, ∀ t ∈ L j, t < n)
    (hR : ∀ j ∈ R, A j = false ∧ j ∉ Del ∧ ∃ d ∈ Del, d < j ∧ (a j = n + d ∨ b j = n + d)) :
    ∀ p, (∀ j < p, a j < n + j ∧ b j < n + j) →
    ∃ (gs : List Gate) (m : ℕ → Option ℕ), Ok n gs ∧
      (∀ w < n + p, (∀ w', m w = some w' → w' < n + gs.length) ∧
        ∀ x : Fin n → Bool, ov gs (List.ofFn x) (m w) = u n A a b Del L (List.ofFn x) w) ∧
      (∀ d ∈ Del, d < p → m (n + d) = none) ∧
      gs.length + ((Finset.range p).filter (· ∈ Del)).card +
        ((Finset.range p).filter (· ∈ R)).card ≤ p + ∑ j ∈ Finset.range p, (L j).length ∧
      dc n F gs ≤ ((Finset.range p).filter fun j => A j = true ∧ j ∉ Del ∧
        ∃ x : Fin n → Bool, u n A a b Del L (List.ofFn x) (n + j) = true ∧ F x = false).card := by
  intro p
  induction p with
  | zero =>
    intro _
    refine ⟨[], fun w => some w, by intro j hj; simp at hj, ?_, by simp, by simp, by simp [dc]⟩
    intro w hw
    refine ⟨by intro w' h; cases h; simpa using hw, fun x => ?_⟩
    rw [u_in (by omega)]; rfl
  | succ p ih =>
    intro hab
    obtain ⟨gs, m, hok, hm, hd, hc, hj⟩ := ih fun j hj => hab j (by omega)
    obtain ⟨hap, hbp⟩ := hab p (by omega)
    suffices hh : ∃ (hs : List Gate) (o : Option ℕ), Ok n (gs ++ hs) ∧
        (∀ w, o = some w → w < n + (gs ++ hs).length) ∧ (p ∈ Del → o = none) ∧
        (∀ x : Fin n → Bool, ov (gs ++ hs) (List.ofFn x) o =
          u n A a b Del L (List.ofFn x) (n + p)) ∧
        hs.length + (if p ∈ Del then 1 else 0) + (if p ∈ R then 1 else 0) ≤ 1 + (L p).length ∧
        dc n F (gs ++ hs) ≤ dc n F gs + if A p = true ∧ p ∉ Del ∧ ∃ x : Fin n → Bool,
          u n A a b Del L (List.ofFn x) (n + p) = true ∧ F x = false then 1 else 0 by
      obtain ⟨hs, o, h1, h2, h3, h4, h5, h6⟩ := hh
      refine ⟨gs ++ hs, Function.update m (n + p) o, h1, ?_, ?_, ?_, ?_⟩
      · intro w hw
        by_cases hwp : w = n + p
        · subst hwp; rw [Function.update_self]; exact ⟨h2, h4⟩
        · rw [Function.update_of_ne hwp]
          obtain ⟨q1, q2⟩ := hm w (by omega)
          refine ⟨fun w' hw' => by have := q1 w' hw'; simp; omega, fun x => ?_⟩
          rw [ov_ext gs hs _ _ (by simpa using q1), q2]
      · intro d hdd hdp
        by_cases hdp' : d = p
        · subst hdp'; rw [Function.update_self]; exact h3 hdd
        · rw [Function.update_of_ne (by omega)]; exact hd d hdd (by omega)
      · rw [Finset.range_add_one, Finset.filter_insert, Finset.filter_insert,
          Finset.sum_insert (by simp), List.length_append]
        split_ifs at h5 ⊢ with q1 q2 q2 <;>
          (try rw [Finset.card_insert_of_notMem (by simp)]) <;>
          (try rw [Finset.card_insert_of_notMem (by simp)]) <;> omega
      · rw [Finset.range_add_one, Finset.filter_insert]
        split_ifs at h6 ⊢ with q1
        · rw [Finset.card_insert_of_notMem (by simp)]; omega
        · omega
    by_cases hpd : p ∈ Del
    · have hpR : p ∉ R := fun h => (hR p h).2.1 hpd
      refine ⟨[], none, by simpa using hok, by simp, fun _ => rfl, fun x => ?_, ?_, by simp⟩
      · rw [u_del hpd]; rfl
      · rw [if_pos hpd, if_neg hpR]; simp
    obtain ⟨a1, a2⟩ := hm (a p) hap
    obtain ⟨b1, b2⟩ := hm (b p) hbp
    cases hA : A p with
    | false =>
      have hu := fun x : Fin n → Bool => u_or (L := L) (x := List.ofFn x) hpd hA hap hbp
      rcases ha0 : m (a p) with _ | s
      · refine ⟨[], m (b p), by simpa using hok, by simpa using b1, fun h => absurd h hpd,
          fun x => ?_, ?_, by simp⟩
        · rw [hu x, ← a2 x, ← b2 x, ha0]; simp [ov]
        · rw [if_neg hpd]; split_ifs <;> simp
      rcases hb0 : m (b p) with _ | t
      · refine ⟨[], m (a p), by simpa using hok, by simpa using a1, fun h => absurd h hpd,
          fun x => ?_, ?_, by simp⟩
        · rw [hu x, ← a2 x, ← b2 x, hb0]; simp [ov]
        · rw [if_neg hpd]; split_ifs <;> simp
      have hpR : p ∉ R := by
        intro h
        obtain ⟨_, _, d, hd1, hd2, hd3⟩ := hR p h
        have := hd d hd1 hd2
        rcases hd3 with h | h
        · rw [h, this] at ha0; cases ha0
        · rw [h, this] at hb0; cases hb0
      have hs := a1 s ha0
      have ht := b1 t hb0
      refine ⟨[⟨GateOp.or, [s, t]⟩], some (n + gs.length), ok_snoc hok (Or.inr rfl) hs ht,
        by intro w hw; cases hw; simp, fun h => absurd h hpd, fun x => ?_, ?_, ?_⟩
      · rw [ov_new gs n _ (by simp) _ _ _ hs ht, hu x, ← a2 x, ← b2 x, ha0, hb0]
        simp [ov, GateOp.eval]
      · rw [if_neg hpd, if_neg hpR]; simp
      · have := dc_snoc n F gs ⟨GateOp.or, [s, t]⟩
        rw [if_neg (by simp)] at this
        omega
    | true =>
      have hu := fun x : Fin n → Bool => u_and (L := L) (x := List.ofFn x) hpd hA hap hbp
      have hpR : p ∉ R := fun h => by rw [(hR p h).1] at hA; cases hA
      obtain ⟨hs, o', c1, c2, c3, c4, c5⟩ := chain n F (L p) (hL p) gs hok (m (a p)) a1
      rcases ho : o' with _ | s
      · refine ⟨hs, none, c1, by simp, fun _ => rfl, fun x => ?_, ?_, by omega⟩
        · have := c5 x
          rw [ho, a2 x] at this
          rw [hu x, ← this]; simp [ov]
        · rw [if_neg hpd, if_neg hpR]; omega
      rcases hb0 : m (b p) with _ | t
      · refine ⟨hs, none, c1, by simp, fun _ => rfl, fun x => ?_, ?_, by omega⟩
        · have := b2 x
          rw [hb0] at this
          rw [hu x, ← this]; simp [ov]
        · rw [if_neg hpd, if_neg hpR]; omega
      have hs' := c4 s ho
      have ht : t < n + (gs ++ hs).length := by have := b1 t hb0; simp; omega
      have hval : ∀ x : Fin n → Bool, ov (gs ++ hs ++ [⟨GateOp.and, [s, t]⟩]) (List.ofFn x)
          (some (n + (gs ++ hs).length)) = u n A a b Del L (List.ofFn x) (n + p) := by
        intro x
        rw [ov_new (gs ++ hs) n _ (by simp) _ _ _ hs' ht, hu x, ← a2 x, ← b2 x, ← c5 x, ho, hb0,
          ← ov_ext gs hs (List.ofFn x) (some t) (by intro w hw; cases hw; simpa using b1 t hb0)]
        simp [ov, GateOp.eval]
      refine ⟨hs ++ [⟨GateOp.and, [s, t]⟩], some (n + (gs ++ hs).length), ?_, ?_,
        fun h => absurd h hpd, fun x => ?_, ?_, ?_⟩
      · rw [← List.append_assoc]; exact ok_snoc c1 (Or.inl rfl) hs' ht
      · intro w hw; cases hw; simp
      · rw [← List.append_assoc]; exact hval x
      · rw [if_neg hpd, if_neg hpR]; simp; omega
      · rw [← List.append_assoc]
        have := dc_snoc n F (gs ++ hs) ⟨GateOp.and, [s, t]⟩
        have e : ((⟨GateOp.and, [s, t]⟩ : Gate).op = GateOp.and ∧ ∃ x : Fin n → Bool,
            (run (gs ++ hs ++ [⟨GateOp.and, [s, t]⟩]) (List.ofFn x)).getD
              (n + (gs ++ hs).length) false = true ∧ F x = false) ↔
            (true = true ∧ p ∉ Del ∧ ∃ x : Fin n → Bool,
              u n A a b Del L (List.ofFn x) (n + p) = true ∧ F x = false) := by
          refine ⟨fun h => ⟨rfl, hpd, ?_⟩, fun h => ⟨rfl, ?_⟩⟩
          · obtain ⟨x, h1, h2⟩ := h.2
            exact ⟨x, by rw [← hval x]; exact h1, h2⟩
          · obtain ⟨x, h1, h2⟩ := h.2.2
            exact ⟨x, by rw [← hval x] at h1; exact h1, h2⟩
        rw [if_congr e rfl rfl] at this
        omega

lemma gf {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ p q, G.Adj p q ∧ x p = true ∧ x q = true := by
  simp [graphFun]

lemma gD {n : ℕ} (x : Fin n → Bool) (p : Fin n) : (List.ofFn x).getD p.val false = x p := by
  simp [List.getD_eq_getElem?_getD]

lemma u_mono {n N : ℕ} {A : ℕ → Bool} {a b : ℕ → ℕ} {Del : Finset ℕ} {L : ℕ → List ℕ}
    (hab : ∀ j < N, a j < n + j ∧ b j < n + j) (x y : List Bool)
    (h : ∀ t, x.getD t false = true → y.getD t false = true) :
    ∀ w < n + N, u n A a b Del L x w = true → u n A a b Del L y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hx
    by_cases h9 : w < n
    · rw [u_in h9] at hx ⊢; exact h _ hx
    obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
    obtain ⟨ha, hb⟩ := hab j (by omega)
    by_cases hd : j ∈ Del
    · rw [u_del hd] at hx; cases hx
    have ia := ih (a j) ha (by omega)
    have ib := ih (b j) hb (by omega)
    cases hA : A j with
    | true =>
      rw [u_and hd hA ha hb, Bool.and_eq_true, Bool.or_eq_true] at hx ⊢
      refine ⟨?_, ib hx.2⟩
      rcases hx.1 with h1 | h1
      · exact Or.inl (ia h1)
      · right
        rw [List.any_eq_true] at h1 ⊢
        obtain ⟨t, h2, h3⟩ := h1
        exact ⟨t, h2, h t h3⟩
    | false =>
      rw [u_or hd hA ha hb, Bool.or_eq_true] at hx ⊢
      rcases hx with h1 | h1
      · exact Or.inl (ia h1)
      · exact Or.inr (ib h1)

lemma gate2 {n : ℕ} {C : Circuit} (h : TopForm.IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
    C.gates[j] = gateAt C j ∧ (gateAt C j).inputs = [TopForm.opnd C j 0, TopForm.opnd C j 1] ∧
    TopForm.opnd C j 0 < n + j ∧ TopForm.opnd C j 1 < n + j ∧
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) := by
  have e : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
  have hm : gateAt C j ∈ C.gates := by rw [e]; exact List.getElem_mem hj
  have hl := h.2.2 _ hm
  obtain ⟨s, t, hst⟩ := List.length_eq_two.1 hl
  have hb := h.2.1 j hj
  rw [hst] at hb
  have e0 : TopForm.opnd C j 0 = s := by unfold TopForm.opnd; rw [hst]; rfl
  have e1 : TopForm.opnd C j 1 = t := by unfold TopForm.opnd; rw [hst]; rfl
  refine ⟨e.symm, by rw [hst, e0, e1], by rw [e0]; exact hb s (by simp),
    by rw [e1]; exact hb t (by simp), h.1 _ hm⟩



lemma gDv {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (List.ofFn x).getD w false = x ⟨w, hw⟩ := gD x ⟨w, hw⟩
lemma ok_ao {n : ℕ} {gs : List Gate} {w : ℕ} (hok : Ok n gs) : TopForm.IsAO2 n ⟨gs, w⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hq
    obtain ⟨o', s', t', h1, h2, _⟩ := hok i hi
    rw [h1]; exact h2
  · intro j hj i hi
    obtain ⟨o', s', t', h1, h2, h3, h4⟩ := hok j hj
    have e1 : gateAt ⟨gs, w⟩ j = gs[j] := List.getD_eq_getElem _ _ hj
    rw [e1, h1] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> assumption
  · intro q hq
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hq
    obtain ⟨o', s', t', h1, h2, _⟩ := hok i hi
    rw [h1]; rfl

open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

def isAnd (C : Circuit) (j : ℕ) : Bool :=
  match (gateAt C j).op with
  | .and => true
  | _ => false

def val (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (run C.gates (List.ofFn x)).getD w false

def cutVal (n : ℕ) (C : Circuit) (Del : Finset ℕ) (x : Fin n → Bool) (w : ℕ) : Bool :=
  u n (isAnd C) (fun j => opnd C j 0) (fun j => opnd C j 1) Del (fun _ => []) (List.ofFn x) w

lemma val_in {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val n C x w = (List.ofFn x).getD w false := by
  exact run_input C.gates (List.ofFn x) w (by simpa using hw)

lemma val_rec {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (x : Fin n → Bool) (j : ℕ)
    (hj : j < C.gates.length) :
    val n C x (n + j) = if isAnd C j = true then
      val n C x (opnd C j 0) && val n C x (opnd C j 1)
    else val n C x (opnd C j 0) || val n C x (opnd C j 1) := by
  obtain ⟨heq, hin, ha, hb, hop⟩ := gate2 hC hj
  have hr := run_gate C.gates (List.ofFn x) j hj
  rw [List.length_ofFn, heq, hin] at hr
  rcases hop with hop | hop
  · simp only [val, hr, hop, List.map_cons, List.map_nil, if_pos ha, if_pos hb]
    simp [isAnd, hop, GateOp.eval]
  · simp only [val, hr, hop, List.map_cons, List.map_nil, if_pos ha, if_pos hb]
    simp [isAnd, hop, GateOp.eval]

lemma cutVal_le {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (Del : Finset ℕ)
    (x : Fin n → Bool) :
    ∀ w < n + C.gates.length, cutVal n C Del x w = true → val n C x w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw h
    by_cases hin : w < n
    · simpa only [cutVal, u_in hin, val_in C x w hin] using h
    obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
    have hj : j < C.gates.length := by omega
    obtain ⟨_, _, ha, hb, _⟩ := gate2 hC hj
    by_cases hd : j ∈ Del
    · simp only [cutVal, u_del hd] at h
      cases h
    rw [val_rec C hC x j hj]
    cases hA : isAnd C j with
    | false =>
      simp only [hA, Bool.false_eq_true, ↓reduceIte]
      rw [cutVal, u_or hd hA ha hb, Bool.or_eq_true] at h
      rcases h with h | h
      · rw [Bool.or_eq_true]; exact Or.inl (ih _ ha (by omega) h)
      · rw [Bool.or_eq_true]; exact Or.inr (ih _ hb (by omega) h)
    | true =>
      simp only [hA, ↓reduceIte]
      rw [cutVal, u_and hd hA ha hb] at h
      simp only [List.any_nil, Bool.or_false, Bool.and_eq_true] at h
      rw [Bool.and_eq_true]; exact ⟨ih _ ha (by omega) h.1, ih _ hb (by omega) h.2⟩

lemma cutVal_eq_of_zero {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (j : ℕ)
    (x : Fin n → Bool) (hz : val n C x (n + j) = false) :
    ∀ w < n + C.gates.length, cutVal n C {j} x w = val n C x w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hin : w < n
    · simp only [cutVal, u_in hin, val_in C x w hin]
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have hk : k < C.gates.length := by omega
    obtain ⟨_, _, ha, hb, _⟩ := gate2 hC hk
    by_cases hd : k ∈ ({j} : Finset ℕ)
    · have hkj : k = j := Finset.mem_singleton.mp hd
      subst k
      rw [cutVal, u_del (Finset.mem_singleton_self j), hz]
    rw [val_rec C hC x k hk]
    have ia := ih (opnd C k 0) ha (by omega)
    have ib := ih (opnd C k 1) hb (by omega)
    cases hA : isAnd C k with
    | false =>
      simp only [hA, Bool.false_eq_true, ↓reduceIte]
      rw [cutVal, u_or hd hA ha hb]
      exact congrArg₂ Bool.or ia ib
    | true =>
      simp only [hA, ↓reduceIte]
      rw [cutVal, u_and hd hA ha hb]
      simp only [List.any_nil, Bool.or_false]
      exact congrArg₂ Bool.and ia ib

lemma cutVal_mono {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (Del : Finset ℕ)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true)
    (w : ℕ) (hw : w < n + C.gates.length) :
    cutVal n C Del x w = true → cutVal n C Del y w = true := by
  have hab : ∀ j < C.gates.length, opnd C j 0 < n + j ∧ opnd C j 1 < n + j := by
    intro j hj
    exact ⟨(gate2 hC hj).2.2.1, (gate2 hC hj).2.2.2.1⟩
  have hget : ∀ t, (List.ofFn x).getD t false = true → (List.ofFn y).getD t false = true := by
    intro t ht
    by_cases ht' : t < n
    · rw [gDv y t ht']
      exact hxy ⟨t, ht'⟩ (by simpa only [gDv x t ht'] using ht)
    · have : (List.ofFn x).getD t false = false :=
        List.getD_eq_default _ _ (by simp; omega)
      rw [this] at ht
      cases ht
  exact u_mono hab (List.ofFn x) (List.ofFn y) hget w hw

lemma val_out {n : ℕ} (C : Circuit) (x : Fin n → Bool) :
    val n C x C.output = circuitFun n C x := rfl

lemma output_lt {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hF : circuitFun n C = graphFun G ∅) (hE : G.edgeFinset.Nonempty) :
    C.output < n + C.gates.length := by
  have hE' : ∃ p q, G.Adj p q := by
    obtain ⟨e, he⟩ := hE
    induction e using Sym2.ind with
    | _ p q => exact ⟨p, q, by simpa using he⟩
  obtain ⟨p, q, hpq⟩ := hE'
  have htrue : val n C (fun _ => true) C.output = true := by
    rw [val_out, hF]
    exact (gf G _).mpr ⟨p, q, hpq, rfl, rfl⟩
  by_contra h
  have hfalse : val n C (fun _ => true) C.output = false :=
    List.getD_eq_default _ _ (by rw [run_length, List.length_ofFn]; omega)
  rw [hfalse] at htrue
  cases htrue

lemma compile_cut {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (j : ℕ)
    (hj : j < C.gates.length) (hout : C.output < n + C.gates.length) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size < C.size ∧
      ∀ x : Fin n → Bool, circuitFun n D x = cutVal n C {j} x C.output := by
  obtain ⟨gs, m, hok, hm, _, hsize, _⟩ := build n (isAnd C)
    (fun k => opnd C k 0) (fun k => opnd C k 1) {j} ∅ (fun _ => [])
    (fun _ => false) (by simp) (by simp) C.gates.length
    (fun k hk => ⟨(gate2 hC hk).2.2.1, (gate2 hC hk).2.2.2.1⟩)
  have hcard : ((Finset.range C.gates.length).filter (· ∈ ({j} : Finset ℕ))).card = 1 := by
    have : (Finset.range C.gates.length).filter (· ∈ ({j} : Finset ℕ)) = {j} := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      omega
    rw [this]
    simp
  simp only [hcard, Finset.notMem_empty, Finset.filter_false, Finset.card_empty,
    Nat.add_zero, List.length_nil, Finset.sum_const_zero] at hsize
  rcases hm C.output hout with ⟨hbound, heq⟩
  cases ho : m C.output with
  | none =>
    refine ⟨⟨gs, n + gs.length⟩, ok_ao hok, by simp only [Circuit.size]; omega, ?_⟩
    intro x
    have hfalse : (run gs (List.ofFn x)).getD (n + gs.length) false = false :=
      List.getD_eq_default _ _ (by rw [run_length, List.length_ofFn])
    change (run gs (List.ofFn x)).getD (n + gs.length) false = _
    rw [hfalse]
    have hh := heq x
    simpa only [ho, ov, cutVal] using hh
  | some w =>
    refine ⟨⟨gs, w⟩, ok_ao hok, by simp only [Circuit.size]; omega, ?_⟩
    intro x
    change (run gs (List.ofFn x)).getD w false = _
    have hh := heq x
    simpa only [ho, ov, cutVal] using hh

lemma least_gate_critical {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hE : G.edgeFinset.Nonempty) (j : ℕ)
    (hj : j < C.gates.length) :
    ∃ p q : Fin n, G.Adj p q ∧ cutVal n C {j} (pairInput p q) C.output = false := by
  have hout := output_lt G C hL.2.1 hE
  by_contra h
  push Not at h
  have hF : ∀ x : Fin n → Bool, cutVal n C {j} x C.output = graphFun G ∅ x := by
    intro x
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro hx
      have hval := cutVal_le C hL.1 {j} x C.output hout hx
      rwa [val_out, hL.2.1] at hval
    · intro hx
      obtain ⟨p, q, hpq, hp, hq⟩ := (gf G x).mp hx
      have hedge : cutVal n C {j} (pairInput p q) C.output = true := by
        cases ht : cutVal n C {j} (pairInput p q) C.output
        · exact (h p q hpq ht).elim
        · rfl
      apply cutVal_mono C hL.1 {j} (pairInput p q) x ?_ C.output hout hedge
      intro i hi
      have : i = p ∨ i = q := by simpa [pairInput] using hi
      rcases this with rfl | rfl <;> assumption
  obtain ⟨D, hAO, hsize, heq⟩ := compile_cut C hL.1 j hj hout
  have hDF : circuitFun n D = graphFun G ∅ := funext fun x => (heq x).trans (hF x)
  have hmin := hL.2.2 D hAO hDF
  omega



lemma cutVal_eq_set {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (j : ℕ)
    (x : Fin n → Bool) :
    ∀ w < n + C.gates.length,
      cutVal n C {j} x w =
        (run (C.gates.set j ⟨GateOp.or, []⟩) (List.ofFn x)).getD w false := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hin : w < n
    · rw [cutVal, u_in hin, run_input _ _ w (by simpa using hin)]
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have hk : k < C.gates.length := by omega
    have hk' : k < (C.gates.set j ⟨GateOp.or, []⟩).length := by simpa using hk
    have hrec := run_gate (C.gates.set j ⟨GateOp.or, []⟩) (List.ofFn x) k hk'
    rw [List.length_ofFn] at hrec
    by_cases hkj : k = j
    · subst k
      rw [cutVal, u_del (Finset.mem_singleton_self j), hrec]
      simp [GateOp.eval]
    have hnot : k ∉ ({j} : Finset ℕ) := by simpa using hkj
    have hgt : (C.gates.set j ⟨GateOp.or, []⟩)[k] = C.gates[k] := by
      simp [List.getElem_set, hkj, Ne.symm hkj]
    obtain ⟨heq, hinp, ha, hb, hop⟩ := gate2 hC hk
    rw [hgt, heq, hinp] at hrec
    simp only [List.map_cons, List.map_nil, if_pos ha, if_pos hb] at hrec
    have ia := ih (opnd C k 0) ha (by omega)
    have ib := ih (opnd C k 1) hb (by omega)
    rcases hop with hop | hop
    · have hA : isAnd C k = true := by simp [isAnd, hop]
      rw [cutVal, u_and hnot hA ha hb, hrec, hop]
      simp only [List.any_nil, Bool.or_false, GateOp.eval, List.all_cons, List.all_nil,
        Bool.and_true, id_eq]
      exact congrArg₂ Bool.and ia ib
    · have hA : isAnd C k = false := by simp [isAnd, hop]
      rw [cutVal, u_or hnot hA ha hb, hrec, hop]
      simp only [GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq]
      exact congrArg₂ Bool.or ia ib

lemma least_gate_critical_edge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hE : G.edgeFinset.Nonempty) (j : ℕ)
    (hj : j < C.gates.length) :
    ∃ p q : Fin n, G.Adj p q ∧ gateVal n C j (pairInput p q) = true ∧
      circuitFun n ⟨C.gates.set j ⟨GateOp.or, []⟩, C.output⟩ (pairInput p q) = false := by
  obtain ⟨p, q, hpq, hcut⟩ := least_gate_critical G C hL hE j hj
  have hkill : circuitFun n ⟨C.gates.set j ⟨GateOp.or, []⟩, C.output⟩ (pairInput p q) = false := by
    change (run (C.gates.set j ⟨GateOp.or, []⟩) (List.ofFn (pairInput p q))).getD C.output false = false
    rw [← cutVal_eq_set C hL.1 j (pairInput p q) C.output (output_lt G C hL.2.1 hE)]
    exact hcut
  refine ⟨p, q, hpq, ?_, hkill⟩
  cases hz : gateVal n C j (pairInput p q) with
  | true => rfl
  | false =>
    have heq := cutVal_eq_of_zero C hL.1 j (pairInput p q) hz C.output
      (output_lt G C hL.2.1 hE)
    rw [hcut, val_out, hL.2.1] at heq
    have hf : graphFun G ∅ (pairInput p q) = true :=
      (gf G _).mpr ⟨p, q, hpq, by simp [pairInput], by simp [pairInput]⟩
    rw [hf] at heq
    cases heq

lemma least_nonempty_of_gate {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (j : ℕ) (hj : j < C.gates.length) :
    G.edgeFinset.Nonempty := by
  by_contra hempty
  have hempty : G.edgeFinset = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
  have hadj : ∀ p q : Fin n, ¬ G.Adj p q := by
    intro p q hpq
    have he : s(p, q) ∈ G.edgeFinset := by simpa using hpq
    rw [hempty] at he
    exact Finset.notMem_empty _ he
  let D : Circuit := ⟨[], n⟩
  have hAO : IsAO2 n D := by
    simp [IsAO2, AndOrOnly, ReadsBack, D]
  have hF : circuitFun n D = graphFun G ∅ := by
    funext x
    have hfalse : graphFun G ∅ x = false := by
      cases hx : graphFun G ∅ x with
      | false => rfl
      | true =>
        obtain ⟨p, q, hpq, _, _⟩ := (gf G x).mp hx
        exact (hadj p q hpq).elim
    rw [hfalse]
    simp [circuitFun, D, Circuit.eval, Circuit.wires, List.getD_eq_getElem?_getD]
  have hsize := hL.2.2 D hAO hF
  simp only [Circuit.size, D, List.length_nil] at hsize
  omega

lemma least_gate_critical_edge_of_least {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hL : IsLeastAO G C) (j : ℕ)
    (hj : j < C.gates.length) :
    ∃ p q : Fin n, G.Adj p q ∧ gateVal n C j (pairInput p q) = true ∧
      circuitFun n ⟨C.gates.set j ⟨GateOp.or, []⟩, C.output⟩ (pairInput p q) = false := by
  exact least_gate_critical_edge G C hL (least_nonempty_of_gate G C hL j hj) j hj


end CriticalEdge

namespace Mixed

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm

lemma joint_accepted_edge {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (hL : IsLeastAO G C) (hTop : TopForm G C)
    (g h : ℕ) (hJ : junk G C = {g, h})
    (hmix : ∀ c : Bool, gateVal n C h (monoInput s c) = true) :
    ∃ u v, G.Adj u v ∧ gateVal n C g (pairInput u v) = true ∧
      gateVal n C h (pairInput u v) = true := by
  have hhJ : h ∈ junk G C := by simp [hJ]
  obtain ⟨u, v, huv, hhv, hlost⟩ :=
    CriticalEdge.least_gate_critical_edge_of_least G C hL h (mem_junk.mp hhJ).1
  have hgv := lost_edge_uses_other G C s hcol hL.1 hTop hL.2.1 g h hJ hmix off u v huv hlost
  exact ⟨u, v, huv, hgv, hhv⟩

end Mixed

namespace CenterGeometry

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm

open Classical in
noncomputable def repairBool {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (A B C D K : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide (RepairHit G s A B C D K x)

lemma repair_mono {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (A B C D K : Finset (Fin n))
    (x y : Fin n → Bool) (hxy : ∀ u, x u = true → y u = true) :
    repairBool G s A B C D K x = true → repairBool G s A B C D K y = true := by
  classical
  simp only [repairBool, decide_eq_true_eq]
  rintro ⟨u, huK, hxu, hgood | ⟨v, hv, hxv⟩⟩
  · exact ⟨u, huK, hxy u hxu, Or.inl hgood⟩
  · exact ⟨u, huK, hxy u hxu, Or.inr ⟨v, hv, hxy v hxv⟩⟩

lemma hit_pair_iff {n : Nat} (S : Finset (Fin n)) (u v : Fin n) :
    (∃ a ∈ S, pairInput u v a = true) ↔ u ∈ S ∨ v ∈ S := by
  simp only [pairInput, decide_eq_true_eq]
  constructor
  · rintro ⟨a, ha, rfl | rfl⟩
    · exact Or.inl ha
    · exact Or.inr ha
  · rintro (hu | hv)
    · exact ⟨u, hu, Or.inl rfl⟩
    · exact ⟨v, hv, Or.inr rfl⟩

lemma nonempty_minimal_repair_cover {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hcol : ∀ a b, G.Adj a b → s a ≠ s b)
    (h4 : NoFourCycle G) (A B C D : Finset (Fin n)) (hAB : Disjoint A B)
    (hA : 2 ≤ A.card) (hB : 2 ≤ B.card) (hclean : ProductClean G A B C D)
    (hAcol : ∀ a ∈ A, s a = false) (hBcol : ∀ b ∈ B, s b = true)
    (hne : ∃ u v, (traceGraph G A B C D).Adj u v) :
    ∃ K : Finset (Fin n), K.Nonempty ∧ K ⊆ C ∪ D ∧ K.card ≤ 2 ∧
      (∀ a b, (traceGraph G A B C D).Adj a b → a ∈ K ∨ b ∈ K) ∧
      (∀ J : Finset (Fin n), J ⊆ C ∪ D →
        (∀ a b, (traceGraph G A B C D).Adj a b → a ∈ J ∨ b ∈ J) → K.card ≤ J.card) ∧
      (∀ u ∈ K, ∃ v, (traceGraph G A B C D).Adj u v) ∧
      ∀ u ∈ K, ¬ GoodCenter G A B u →
        ((u ∈ C ∧ u ∉ D) ∨ (u ∈ D ∧ u ∉ C)) ∧
        (∀ v ∈ leaves s C D u, G.Adj u v) ∧
        ∀ v, (traceGraph G A B C D).Adj u v → v ∈ leaves s C D u := by
  obtain ⟨K0, hK0, hcov0⟩ :=
    FourClausePullback.clean_two_products_two_center_cover G s hcol h4 A B C D hclean
  obtain ⟨K, hKU, hKcard, hcov, hmin, hinc, hstars⟩ :=
    replacement_center_selection G s hcol h4 A B C D K0 hAB hA hB hclean hAcol hBcol hK0
      (by intro u v huv; exact hcov0 u v huv.1 huv.2.1 huv.2.2.1 huv.2.2.2.1 huv.2.2.2.2)
  have hKne : K.Nonempty := by
    obtain ⟨u, v, huv⟩ := hne
    rcases hcov u v huv with hu | hv
    · exact ⟨u, hu⟩
    · exact ⟨v, hv⟩
  exact ⟨K, hKne, hKU, hKcard, hcov, hmin, hinc, hstars⟩

lemma repair_guarded {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Ckt : Circuit) (s : Fin n → Bool) (g : Nat) (A B C D K : Finset (Fin n))
    (hraw : ∀ x, gateVal n Ckt g x = true ↔
      (∃ a ∈ A, x a = true) ∧ (∃ b ∈ B, x b = true))
    (hstar : ∀ u ∈ K, ¬ GoodCenter G A B u → ∀ v ∈ leaves s C D u, G.Adj u v) :
    ∀ x, gateVal n Ckt g x = true → repairBool G s A B C D K x = true →
      graphFun G ∅ x = true := by
  classical
  intro x hg hr
  obtain ⟨hA, hB⟩ := (hraw x).mp hg
  exact repair_safe G s A B C D K hstar x hA hB (of_decide_eq_true hr)

lemma repair_covers_critical {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Ckt : Circuit) (s : Fin n → Bool) (hcol : ∀ a b, G.Adj a b → s a ≠ s b)
    (hAO : IsAO2 n Ckt) (hTop : TopForm G Ckt) (hF : circuitFun n Ckt = graphFun G ∅)
    (g h : Nat) (hJ : junk G Ckt = {g, h})
    (hmix : ∀ c : Bool, gateVal n Ckt h (Mixed.monoInput s c) = true)
    (A B C D K : Finset (Fin n)) (hclean : ProductClean G A B C D)
    (hgraw : ∀ x, gateVal n Ckt g x = true ↔
      (∃ a ∈ A, x a = true) ∧ (∃ b ∈ B, x b = true))
    (hhraw : ∀ x, gateVal n Ckt h x = true ↔
      (∃ c ∈ C, x c = true) ∧ (∃ d ∈ D, x d = true))
    (hKU : K ⊆ C ∪ D)
    (hcover : ∀ a b, (traceGraph G A B C D).Adj a b → a ∈ K ∨ b ∈ K) :
    ∀ u v, G.Adj u v → circuitFun n (patch Ckt h off) (pairInput u v) = false →
      repairBool G s A B C D K (pairInput u v) = true := by
  classical
  intro u v huv hlost
  have hg := Mixed.lost_edge_uses_other G Ckt s hcol hAO hTop hF g h hJ hmix off u v huv hlost
  have hhJ : h ∈ junk G Ckt := by simp [hJ]
  have hpos : circuitFun n Ckt (pairInput u v) = true := by
    rw [hF]
    exact (PrivacyGeometry.pair_graph_iff G u v).mpr huv
  have hh := Mixed.lost_input_gate_true hAO (mem_junk.mp hhJ).1 (pairInput u v) hpos hlost
  obtain ⟨huA, huB⟩ := (hgraw _).mp hg
  obtain ⟨huC, huD⟩ := (hhraw _).mp hh
  have ht : (traceGraph G A B C D).Adj u v :=
    ⟨huv, (hit_pair_iff A u v).mp huA, (hit_pair_iff B u v).mp huB,
      (hit_pair_iff C u v).mp huC, (hit_pair_iff D u v).mp huD⟩
  exact decide_eq_true (repair_pair_complete G s hcol A B C D K hclean hKU hcover u v ht)

end CenterGeometry

namespace ActualCut

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
  PEqualNP.Outside.L_meta_5012_aux.Mixed

open Classical in
noncomputable def boundaryAtoms (n : ℕ) (C : Circuit) (s : Fin n → Bool) (h u : ℕ) :
    Finset (Fin n) :=
  if u ∈ boundary n C s h 0 ∪ boundary n C s h 1 then orIn n C u else ∅

lemma boundary_subset_union (n : ℕ) (C : Circuit) (s : Fin n → Bool) (h : ℕ)
    (b : Fin 2) {u : ℕ} (hu : u ∈ boundary n C s h b) :
    u ∈ boundary n C s h 0 ∪ boundary n C s h 1 := by
  fin_cases b
  · exact Finset.mem_union_left _ hu
  · exact Finset.mem_union_right _ hu

lemma boundary_raw_union {n : ℕ} {C : Circuit} {s : Fin n → Bool} {g h : ℕ}
    (hD : CutData n C s g h)
    (hpure : ∀ b : Fin 2, ∀ x : Fin n → Bool, wireVal n C (opnd C h b) x =
      decide (∃ v ∈ side (n := n) C h b, x v = true)) :
    ∀ b : Fin 2, side (n := n) C h b =
      (boundary n C s h b).biUnion (boundaryAtoms n C s h) := by
  classical
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hhom, _, hroot⟩ := hD
  intro b
  ext v
  constructor
  · intro hv
    let x : Fin n → Bool := fun a => decide (a = v)
    have hx : wireVal n C (opnd C h b) x = true := by
      rw [hpure]; apply decide_eq_true
      exact ⟨v, hv, by simp [x]⟩
    rw [hroot] at hx
    obtain ⟨u, hu, hux⟩ := of_decide_eq_true hx
    rw [(hhom b u hu).2.2] at hux
    obtain ⟨a, ha, hax⟩ := of_decide_eq_true hux
    have heq : a = v := of_decide_eq_true hax
    subst a
    apply Finset.mem_biUnion.mpr
    exact ⟨u, hu, by simpa [boundaryAtoms, boundary_subset_union n C s h b hu] using ha⟩
  · intro hv
    obtain ⟨u, hu, hvu⟩ := Finset.mem_biUnion.mp hv
    have hraw : v ∈ orIn n C u := by
      simpa [boundaryAtoms, boundary_subset_union n C s h b hu] using hvu
    let x : Fin n → Bool := fun a => decide (a = v)
    have hux : wireVal n C u x = true := by
      rw [(hhom b u hu).2.2]; apply decide_eq_true
      exact ⟨v, hraw, by simp [x]⟩
    have hx : wireVal n C (opnd C h b) x = true := by
      rw [hroot]; apply decide_eq_true
      exact ⟨u, hu, hux⟩
    rw [hpure] at hx
    obtain ⟨a, ha, hax⟩ := of_decide_eq_true hx
    have heq : a = v := of_decide_eq_true hax
    simpa only [heq] using ha

lemma boundary_atom_data {n : ℕ} {C : Circuit} {s : Fin n → Bool} {g h : ℕ}
    (hD : CutData n C s g h)
    (hpure : ∀ b : Fin 2, ∀ x : Fin n → Bool, wireVal n C (opnd C h b) x =
      decide (∃ v ∈ side (n := n) C h b, x v = true))
    (hmix : ∀ b : Fin 2, ∀ c : Bool, wireVal n C (opnd C h b) (monoInput s c) = true) :
    ∃ color : ℕ → Bool,
      (∀ u, ∀ v ∈ boundaryAtoms n C s h u, s v = color u) ∧
      (∀ b : Fin 2, side (n := n) C h b =
        (boundary n C s h b).biUnion (boundaryAtoms n C s h)) ∧
      (∀ b : Fin 2, ∀ c : Bool, ∃ v ∈ side (n := n) C h b, s v = c) ∧
      (∀ u ∈ boundary n C s h 0 ∪ boundary n C s h 1,
        (boundaryAtoms n C s h u).Nonempty ∧
        ∀ x : Fin n → Bool, wireVal n C u x =
          decide (∃ v ∈ boundaryAtoms n C s h u, x v = true)) ∧
      (∀ b : Fin 2, ∀ c : Bool, ∃ u ∈ boundary n C s h b, color u = c) := by
  classical
  have hrawunion := boundary_raw_union hD hpure
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hhom, _, hroot⟩ := hD
  have hhu : ∀ u ∈ boundary n C s h 0 ∪ boundary n C s h 1,
      (orIn n C u).Nonempty ∧ (∃ c : Bool, ∀ v ∈ orIn n C u, s v = c) ∧
        ∀ x : Fin n → Bool, wireVal n C u x = decide (∃ v ∈ orIn n C u, x v = true) := by
    intro u hu
    rcases Finset.mem_union.mp hu with hu | hu
    · exact hhom 0 u hu
    · exact hhom 1 u hu
  have hc : ∀ u : ℕ, ∃ c : Bool, ∀ v ∈ boundaryAtoms n C s h u, s v = c := by
    intro u
    by_cases hu : u ∈ boundary n C s h 0 ∪ boundary n C s h 1
    · obtain ⟨c, hc⟩ := (hhu u hu).2.1
      exact ⟨c, by simpa [boundaryAtoms, hu] using hc⟩
    · exact ⟨false, by simp [boundaryAtoms, hu]⟩
  choose color hcolor using hc
  refine ⟨color, hcolor, hrawunion, ?_, ?_, ?_⟩
  · intro b c
    have hx := hmix b c
    rw [hpure] at hx
    simpa [monoInput] using of_decide_eq_true hx
  · intro u hu
    simpa [boundaryAtoms, hu] using And.intro (hhu u hu).1 (hhu u hu).2.2
  · intro b c
    have hx := hmix b c
    rw [hroot] at hx
    obtain ⟨u, hu, hux⟩ := of_decide_eq_true hx
    rw [(hhom b u hu).2.2] at hux
    obtain ⟨v, hv, hvc⟩ := of_decide_eq_true hux
    have hsvc : s v = c := by simpa [monoInput] using hvc
    have hvAtoms : v ∈ boundaryAtoms n C s h u := by
      simpa [boundaryAtoms, boundary_subset_union n C s h b hu] using hv
    exact ⟨u, hu, (hcolor u v hvAtoms).symm.trans hsvc⟩

lemma actual_boundary_atoms {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (s : Fin n → Bool) (hcol : ∀ a b, G.Adj a b → s a ≠ s b)
    (h4 : NoFourCycle G) (hL : IsLeastAO G C) (hTop : TopForm G C)
    (g h : ℕ) (hne : h ≠ g) (hindgh : ¬ InCone n C g h) (hindhg : ¬ InCone n C h g)
    (hJ : junk G C = {g, h})
    (hmix : ∀ c : Bool, gateVal n C h (monoInput s c) = true) :
    ∃ color : ℕ → Bool,
      (∀ u, ∀ v ∈ boundaryAtoms n C s h u, s v = color u) ∧
      (∀ b : Fin 2, side (n := n) C h b =
        (boundary n C s h b).biUnion (boundaryAtoms n C s h)) ∧
      (∀ b : Fin 2, ∀ c : Bool, ∃ v ∈ side (n := n) C h b, s v = c) ∧
      (∀ u ∈ boundary n C s h 0 ∪ boundary n C s h 1,
        (boundaryAtoms n C s h u).Nonempty ∧
        ∀ x : Fin n → Bool, wireVal n C u x =
          decide (∃ v ∈ boundaryAtoms n C s h u, x v = true)) ∧
      (∀ b : Fin 2, ∀ c : Bool, ∃ u ∈ boundary n C s h b, color u = c) := by
  have hd := actual_mixed_cut G C s hcol h4 hL hTop g h hne hindgh hindhg hJ hmix
  have hfac := independent_junk_raw_factors G C hL.1 hTop g h hJ hindgh
  have hhJ : h ∈ junk G C := by simp [hJ]
  have hh := (mem_junk.mp hhJ).1
  have hhand := (mem_junk.mp hhJ).2.1
  apply boundary_atom_data hd (fun b => (hfac b).2)
  intro b c
  exact and_true_operands hL.1 hh hhand (monoInput s c) (hmix c) b

end ActualCut
namespace CostedCenter

open PEqualNP.CircuitLowerBounds

def signal {n : Nat} (V : (Fin n → Bool) → Nat → Bool) (U : Finset Nat)
    (x : Fin n → Bool) : Bool := decide (∃ i ∈ U, V x i = true)

def Builds {n : Nat} (F : (Fin n → Bool) → Bool) (gs : List Gate)
    (R : (Fin n → Bool) → Bool) (budget : Nat) : Prop :=
  ∃ hs : List Gate, ∃ out : Nat, hs.length ≤ budget ∧ Splice.Ok n (gs ++ hs) ∧
    out < n + (gs ++ hs).length ∧
    (∀ x, GateBlock.val (gs ++ hs) out x = R x) ∧
    Splice.dc n F (gs ++ hs) = Splice.dc n F gs

lemma raw_center {n : Nat} (F : (Fin n → Bool) → Bool) (gs : List Gate)
    (hok : Splice.Ok n gs) (u : Fin n) (budget : Nat) :
    Builds F gs (fun x => x u) budget := by
  refine ⟨[], u.val, by simp, by simpa using hok, ?_, ?_, by simp⟩
  · simp only [List.append_nil]
    have := u.isLt
    omega
  · intro x
    simpa using GateBlock.val_input gs u x

lemma raw_pair {n : Nat} (F : (Fin n → Bool) → Bool) (gs : List Gate)
    (hok : Splice.Ok n gs) (u v : Fin n) (budget : Nat) (hbudget : 1 ≤ budget) :
    Builds F gs (fun x => x u || x v) budget := by
  obtain ⟨hok', hdc, hval⟩ := GateBlock.append_or F gs hok u.val v.val
    (by have := u.isLt; omega) (by have := v.isLt; omega)
    (fun x => x u) (fun x => x v) (GateBlock.val_input gs u) (GateBlock.val_input gs v)
  exact ⟨[⟨GateOp.or, [u.val, v.val]⟩], n + gs.length, hbudget, hok', by simp, hval, hdc⟩

lemma compile_one {n p : Nat} (M : Finset Nat) (gs : List Gate)
    (m : Nat → Nat) (V : (Fin n → Bool) → Nat → Bool)
    (hok : Splice.Ok n gs) (hm : Splice.Maps n p M gs m V)
    (U : Finset Nat) (hU : U.Nonempty)
    (hwire : ∀ w ∈ U, w < n + p) (hkeep : ∀ w ∈ U, w < n ∨ w - n ∉ M)
    (F : (Fin n → Bool) → Bool) :
    ∃ hs : List Gate, ∃ out : Nat, Splice.Ok n (gs ++ hs) ∧ hs.length + 1 ≤ U.card ∧
      out < n + (gs ++ hs).length ∧
      (∀ x, GateBlock.val (gs ++ hs) out x = signal V U x) ∧
      Splice.dc n F (gs ++ hs) = Splice.dc n F gs := by
  have hnd : ¬ Disjoint U U := by
    intro hd
    obtain ⟨u, hu⟩ := hU
    exact Finset.disjoint_left.mp hd hu hu
  obtain ⟨hs, out, _, hok', hsize, hout, _, heval, hdc⟩ :=
    ORBlock.two_mapped_nat_outputs M gs m V hok hm U U hU hU
      (by simpa using hwire) (by simpa using hkeep) F
  exact ⟨hs, out, hok', by simpa only [ite_eq_right hnd, Finset.union_self] using hsize,
    hout, fun x => (heval x).1, hdc⟩

lemma one_star {n p : Nat} (M : Finset Nat) (gs : List Gate)
    (m : Nat → Nat) (V : (Fin n → Bool) → Nat → Bool)
    (hok : Splice.Ok n gs) (hm : Splice.Maps n p M gs m V)
    (U : Finset Nat) (hU : U.Nonempty)
    (hwire : ∀ w ∈ U, w < n + p) (hkeep : ∀ w ∈ U, w < n ∨ w - n ∉ M)
    (F : (Fin n → Bool) → Bool) (u : Fin n)
    (hsafe : ∀ x, x u = true → signal V U x = true → F x = true)
    (budget : Nat) (hbudget : U.card ≤ budget) :
    Builds F gs (fun x => x u && signal V U x) budget := by
  obtain ⟨hs, out, hok', hsize, hout, hval, hdc⟩ :=
    compile_one M gs m V hok hm U hU hwire hkeep F
  obtain ⟨hok'', hdc', hval'⟩ := GateBlock.append_and F (gs ++ hs) hok' u.val out
    (by have := u.isLt; omega) hout (fun x => x u) (signal V U)
    (GateBlock.val_input (gs ++ hs) u) hval hsafe
  refine ⟨hs ++ [⟨GateOp.and, [u.val, out]⟩], n + (gs ++ hs).length, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.length_append, List.length_singleton]
    omega
  · simpa only [List.append_assoc] using hok''
  · simp only [List.length_append, List.length_singleton]
    omega
  · simpa only [List.append_assoc] using hval'
  · simpa only [List.append_assoc] using hdc'.trans hdc

lemma raw_and_star {n p : Nat} (M : Finset Nat) (gs : List Gate)
    (m : Nat → Nat) (V : (Fin n → Bool) → Nat → Bool)
    (hok : Splice.Ok n gs) (hm : Splice.Maps n p M gs m V)
    (U : Finset Nat) (hU : U.Nonempty)
    (hwire : ∀ w ∈ U, w < n + p) (hkeep : ∀ w ∈ U, w < n ∨ w - n ∉ M)
    (F : (Fin n → Bool) → Bool) (u v : Fin n)
    (hsafe : ∀ x, x v = true → signal V U x = true → F x = true)
    (budget : Nat) (hbudget : U.card + 1 ≤ budget) :
    Builds F gs (fun x => x u || (x v && signal V U x)) budget := by
  obtain ⟨hs, out, hok', hsize, hout, hval, hdc⟩ :=
    compile_one M gs m V hok hm U hU hwire hkeep F
  obtain ⟨ks, hklen, hok'', hdc', hval'⟩ :=
    GateBlock.raw_or_product_block F (gs ++ hs) hok' u.val v.val out
      (by have := u.isLt; omega) (by have := v.isLt; omega) hout
      (fun x => x u) (fun x => x v) (signal V U)
      (GateBlock.val_input (gs ++ hs) u) (GateBlock.val_input (gs ++ hs) v) hval hsafe
  refine ⟨hs ++ ks, n + (gs ++ hs).length + 1, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.length_append, hklen]
    omega
  · simpa only [List.append_assoc] using hok''
  · simp only [List.length_append, hklen]
    omega
  · simpa only [List.append_assoc] using hval'
  · simpa only [List.append_assoc] using hdc'.trans hdc

lemma merged_stars {n p : Nat} (M : Finset Nat) (gs : List Gate)
    (m : Nat → Nat) (V : (Fin n → Bool) → Nat → Bool)
    (hok : Splice.Ok n gs) (hm : Splice.Maps n p M gs m V)
    (U : Finset Nat) (hU : U.Nonempty)
    (hwire : ∀ w ∈ U, w < n + p) (hkeep : ∀ w ∈ U, w < n ∨ w - n ∉ M)
    (F : (Fin n → Bool) → Bool) (u v : Fin n)
    (hsafeU : ∀ x, x u = true → signal V U x = true → F x = true)
    (hsafeV : ∀ x, x v = true → signal V U x = true → F x = true)
    (budget : Nat) (hbudget : U.card + 1 ≤ budget) :
    Builds F gs (fun x => (x u || x v) && signal V U x) budget := by
  obtain ⟨hs, out, hok', hsize, hout, hval, hdc⟩ :=
    compile_one M gs m V hok hm U hU hwire hkeep F
  obtain ⟨ks, hklen, hok'', hdc', hval'⟩ :=
    GateBlock.merged_centers_block F (gs ++ hs) hok' u.val v.val out
      (by have := u.isLt; omega) (by have := v.isLt; omega) hout
      (fun x => x u) (fun x => x v) (signal V U)
      (GateBlock.val_input (gs ++ hs) u) (GateBlock.val_input (gs ++ hs) v) hval hsafeU hsafeV
  refine ⟨hs ++ ks, n + (gs ++ hs).length + 1, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.length_append, hklen]
    omega
  · simpa only [List.append_assoc] using hok''
  · simp only [List.length_append, hklen]
    omega
  · simpa only [List.append_assoc] using hval'
  · simpa only [List.append_assoc] using hdc'.trans hdc

lemma two_stars {n p : Nat} (M : Finset Nat) (gs : List Gate)
    (m : Nat → Nat) (V : (Fin n → Bool) → Nat → Bool)
    (hok : Splice.Ok n gs) (hm : Splice.Maps n p M gs m V)
    (U W : Finset Nat) (hU : U.Nonempty) (hW : W.Nonempty)
    (hwire : ∀ w ∈ U ∪ W, w < n + p)
    (hkeep : ∀ w ∈ U ∪ W, w < n ∨ w - n ∉ M)
    (F : (Fin n → Bool) → Bool) (u v : Fin n)
    (hsafeU : ∀ x, x u = true → signal V U x = true → F x = true)
    (hsafeV : ∀ x, x v = true → signal V W x = true → F x = true)
    (budget : Nat)
    (hbudget : (U ∪ W).card + 3 ≤ budget + (if Disjoint U W then 2 else 1)) :
    Builds F gs (fun x => (x u && signal V U x) || (x v && signal V W x)) budget := by
  obtain ⟨hs, outU, outW, hok', hsize, houtU, houtW, hval, hdc⟩ :=
    ORBlock.two_mapped_nat_outputs M gs m V hok hm U W hU hW hwire hkeep F
  obtain ⟨ks, hklen, hok'', hdc', hval'⟩ :=
    GateBlock.two_products_block F (gs ++ hs) hok' u.val outU v.val outW
      (by have := u.isLt; omega) houtU (by have := v.isLt; omega) houtW
      (fun x => x u) (signal V U) (fun x => x v) (signal V W)
      (GateBlock.val_input (gs ++ hs) u) (fun x => (hval x).1)
      (GateBlock.val_input (gs ++ hs) v) (fun x => (hval x).2) hsafeU hsafeV
  refine ⟨hs ++ ks, n + (gs ++ hs).length + 2, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.length_append, hklen]
    omega
  · simpa only [List.append_assoc] using hok''
  · simp only [List.length_append, hklen]
    omega
  · simpa only [List.append_assoc] using hval'
  · simpa only [List.append_assoc] using hdc'.trans hdc

end CostedCenter
namespace CostedCenter

open PEqualNP.MetaComplexity.NestedCover CenterGeometry BoundaryLossGeneric

def projection {n : Nat} (s : Fin n → Bool) (C : Finset (Fin n))
    (S T : Finset Nat) (color : Nat → Bool) (u : Fin n) : Finset Nat :=
  (if u ∈ C then T else S).filter fun i => color i ≠ s u

lemma projection_subset {n : Nat} (s : Fin n → Bool) (C : Finset (Fin n))
    (S T : Finset Nat) (color : Nat → Bool) (u : Fin n) :
    projection s C S T color u ⊆ S ∪ T := by
  intro i hi
  unfold projection at hi
  split_ifs at hi with hu
  · exact Finset.mem_union_right _ (Finset.mem_filter.mp hi).1
  · exact Finset.mem_union_left _ (Finset.mem_filter.mp hi).1

lemma projection_value {n : Nat} (atoms : Nat → Finset (Fin n))
    (s : Fin n → Bool) (color : Nat → Bool)
    (hmono : ∀ i v, v ∈ atoms i → s v = color i)
    (S T : Finset Nat) (C D : Finset (Fin n))
    (hC : C = S.biUnion atoms) (hD : D = T.biUnion atoms)
    (V : (Fin n → Bool) → Nat → Bool)
    (hV : ∀ x i, i ∈ S ∪ T → V x i = decide (∃ v ∈ atoms i, x v = true))
    (u : Fin n) (x : Fin n → Bool) :
    signal V (projection s C S T color u) x =
      decide (∃ v ∈ leaves s C D u, x v = true) := by
  unfold projection leaves
  by_cases hu : u ∈ C
  · simp only [hu, ↓reduceIte]
    rw [hD]
    exact projected_signal_value atoms s color hmono T (s u) x (V x)
      (fun i hi => hV x i (Finset.mem_union_right _ hi))
  · simp only [hu, ↓reduceIte]
    rw [hC]
    exact projected_signal_value atoms s color hmono S (s u) x (V x)
      (fun i hi => hV x i (Finset.mem_union_left _ hi))

lemma projection_nonempty {n : Nat} (atoms : Nat → Finset (Fin n))
    (s : Fin n → Bool) (color : Nat → Bool)
    (hmono : ∀ i v, v ∈ atoms i → s v = color i)
    (S T : Finset Nat) (C D : Finset (Fin n))
    (hC : C = S.biUnion atoms) (hD : D = T.biUnion atoms)
    (u : Fin n) (hleaf : (leaves s C D u).Nonempty) :
    (projection s C S T color u).Nonempty := by
  obtain ⟨v, hv⟩ := hleaf
  by_cases hu : u ∈ C
  · have hv' : v ∈ D ∧ s v ≠ s u := by simpa [leaves, hu] using hv
    simpa [projection, hu] using projection_nonempty_of_vertex atoms s color hmono T (s u)
      ⟨v, hD ▸ hv'.1, hv'.2⟩
  · have hv' : v ∈ C ∧ s v ≠ s u := by simpa [leaves, hu] using hv
    simpa [projection, hu] using projection_nonempty_of_vertex atoms s color hmono S (s u)
      ⟨v, hC ▸ hv'.1, hv'.2⟩

lemma projection_card {n : Nat} (atoms : Nat → Finset (Fin n))
    (s : Fin n → Bool) (color : Nat → Bool)
    (hmono : ∀ i v, v ∈ atoms i → s v = color i)
    (S T : Finset Nat) (C D : Finset (Fin n))
    (hC : C = S.biUnion atoms) (hD : D = T.biUnion atoms)
    (hS : S.Nonempty) (hT : T.Nonempty)
    (hCmixed : ∀ c, ∃ u ∈ C, s u = c) (hDmixed : ∀ c, ∃ u ∈ D, s u = c)
    (m : Nat) (hbudget : (S ∪ T).card ≤ m + (if Disjoint S T then 2 else 1))
    (u : Fin n) : (projection s C S T color u).card ≤ m := by
  by_cases hu : u ∈ C
  · simpa [projection, hu] using mixed_projection_card_budget atoms s color hmono S T (s u) m hS
      (hD ▸ hDmixed (s u)) hbudget
  · have hb : (T ∪ S).card ≤ m + (if Disjoint T S then 2 else 1) := by
      simpa only [Finset.union_comm, disjoint_comm] using hbudget
    simpa [projection, hu] using mixed_projection_card_budget atoms s color hmono T S (s u) m hT
      (hC ▸ hCmixed (s u)) hb

lemma projection_pair_budget {n : Nat} (atoms : Nat → Finset (Fin n))
    (s : Fin n → Bool) (color : Nat → Bool)
    (hmono : ∀ i v, v ∈ atoms i → s v = color i)
    (S T : Finset Nat) (C D : Finset (Fin n))
    (hC : C = S.biUnion atoms) (hD : D = T.biUnion atoms)
    (m : Nat) (hbudget : (S ∪ T).card ≤ m + (if Disjoint S T then 2 else 1))
    (u v : Fin n)
    (hu : (u ∈ C ∧ u ∉ D) ∨ (u ∈ D ∧ u ∉ C))
    (hv : (v ∈ C ∧ v ∉ D) ∨ (v ∈ D ∧ v ∉ C))
    (hpattern : (u ∈ C ∧ v ∈ C) ∨ (u ∈ D ∧ v ∈ D) ∨ s u = s v)
    (hnmerge : ¬ ((u ∈ C ↔ v ∈ C) ∧ s u = s v)) :
    ((projection s C S T color u) ∪ (projection s C S T color v)).card + 2 ≤
      m + (if Disjoint (projection s C S T color u) (projection s C S T color v)
        then 2 else 1) := by
  have hbSwap : (T ∪ S).card ≤ m + (if Disjoint T S then 2 else 1) := by
    simpa only [Finset.union_comm, disjoint_comm] using hbudget
  rcases hu with ⟨huC, huD⟩ | ⟨huD, huC⟩ <;>
    rcases hv with ⟨hvC, hvD⟩ | ⟨hvD, hvC⟩
  · have hdiff : s u ≠ s v := fun he => hnmerge ⟨by simp [huC, hvC], he⟩
    have hc := same_output_opposite_card_budget atoms s color hmono S T u v m
      (hC ▸ huC) (hD ▸ huD) (hC ▸ hvC) (hD ▸ hvD) hdiff hbudget
    obtain ⟨hd, he⟩ := opposite_projection_partition T color (s u) (s v) hdiff
    simpa [projection, huC, hvC, hd, he] using Nat.add_le_add_right hc 2
  · have hsame : s u = s v := by rcases hpattern with h | h | h <;> tauto
    have hc := different_outputs_projection_card_budget atoms s color hmono S T u v m
      (hC ▸ huC) (hD ▸ huD) (hD ▸ hvD) (hC ▸ hvC) hsame hbudget
    simpa only [projection, huC, hvC, ↓reduceIte, ← hsame, Finset.union_comm, disjoint_comm] using hc
  · have hsame : s u = s v := by rcases hpattern with h | h | h <;> tauto
    have hc := different_outputs_projection_card_budget atoms s color hmono T S u v m
      (hD ▸ huD) (hC ▸ huC) (hC ▸ hvC) (hD ▸ hvD) hsame hbSwap
    simpa only [projection, huC, hvC, ↓reduceIte, ← hsame, Finset.union_comm, disjoint_comm] using hc
  · have hdiff : s u ≠ s v := fun he => hnmerge ⟨by simp [huC, hvC], he⟩
    have hc := same_output_opposite_card_budget atoms s color hmono T S u v m
      (hD ▸ huD) (hC ▸ huC) (hD ▸ hvD) (hC ▸ hvC) hdiff hbSwap
    obtain ⟨hd, he⟩ := opposite_projection_partition S color (s u) (s v) hdiff
    simpa [projection, huC, hvC, hd, he] using Nat.add_le_add_right hc 2

end CostedCenter
namespace CostedCenter

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover CenterGeometry

lemma builds_congr {n : Nat} (F : (Fin n → Bool) → Bool) (gs : List Gate)
    (R R' : (Fin n → Bool) → Bool) (budget : Nat)
    (h : ∀ x, R x = true ↔ R' x = true) (hb : Builds F gs R budget) :
    Builds F gs R' budget := by
  obtain ⟨hs, out, hlen, hok, hout, hval, hdc⟩ := hb
  exact ⟨hs, out, hlen, hok, hout,
    fun x => (hval x).trans (Bool.eq_iff_iff.mpr (h x)), hdc⟩

lemma selected_center_block {n p : Nat}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (A B C D K : Finset (Fin n))
    (M : Finset Nat) (gs : List Gate) (m : Nat → Nat)
    (V : (Fin n → Bool) → Nat → Bool)
    (hok : Splice.Ok n gs) (hm : Splice.Maps n p M gs m V)
    (S T : Finset Nat) (atoms : Nat → Finset (Fin n)) (color : Nat → Bool)
    (hmono : ∀ i v, v ∈ atoms i → s v = color i)
    (hC : C = S.biUnion atoms) (hD : D = T.biUnion atoms)
    (hV : ∀ x i, i ∈ S ∪ T → V x i = decide (∃ v ∈ atoms i, x v = true))
    (hS : S.Nonempty) (hT : T.Nonempty)
    (hCmixed : ∀ c, ∃ u ∈ C, s u = c) (hDmixed : ∀ c, ∃ u ∈ D, s u = c)
    (hwire : ∀ w ∈ S ∪ T, w < n + p)
    (hkeep : ∀ w ∈ S ∪ T, w < n ∨ w - n ∉ M)
    (hbudget : (S ∪ T).card ≤ M.card + (if Disjoint S T then 2 else 1))
    (hKne : K.Nonempty) (hKcard : K.card ≤ 2)
    (hbad : ∀ u ∈ K, ¬ GoodCenter G A B u →
      ((u ∈ C ∧ u ∉ D) ∨ (u ∈ D ∧ u ∉ C)) ∧
      (leaves s C D u).Nonempty ∧ (∀ v ∈ leaves s C D u, G.Adj u v))
    (hpattern : ∀ u ∈ K, ∀ v ∈ K, u ≠ v →
      ¬ GoodCenter G A B u → ¬ GoodCenter G A B v →
      (u ∈ C ∧ v ∈ C) ∨ (u ∈ D ∧ v ∈ D) ∨ s u = s v)
    (R : (Fin n → Bool) → Bool)
    (hR : ∀ x, R x = true ↔ RepairHit G s A B C D K x) :
    Builds (graphFun G ∅) gs R (M.card + 1) := by
  classical
  let P := projection s C S T color
  have hsub : ∀ u, P u ⊆ S ∪ T := projection_subset s C S T color
  have hvalue : ∀ u x, signal V (P u) x = decide (∃ v ∈ leaves s C D u, x v = true) :=
    projection_value atoms s color hmono S T C D hC hD V hV
  have hbound : ∀ u, (P u).card ≤ M.card :=
    projection_card atoms s color hmono S T C D hC hD hS hT hCmixed hDmixed M.card hbudget
  have hdata : ∀ u ∈ K, ¬ GoodCenter G A B u →
      (P u).Nonempty ∧ (∀ x, x u = true → signal V (P u) x = true → graphFun G ∅ x = true) := by
    intro u hu hnot
    obtain ⟨_, hne, hclean⟩ := hbad u hu hnot
    refine ⟨projection_nonempty atoms s color hmono S T C D hC hD u hne, ?_⟩
    intro x hxu hhit
    rw [hvalue u x, decide_eq_true_eq] at hhit
    obtain ⟨v, hv, hxv⟩ := hhit
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq]
    exact ⟨u, v, hclean v hv, hxu, hxv⟩
  have hlift : ∀ Z : (Fin n → Bool) → Bool,
      (∀ x, Z x = true ↔ RepairHit G s A B C D K x) →
      Builds (graphFun G ∅) gs Z (M.card + 1) → Builds (graphFun G ∅) gs R (M.card + 1) := by
    intro Z hZ hb
    exact builds_congr _ _ Z R _ (fun x => (hZ x).trans (hR x).symm) hb
  rcases small_center_shapes K hKcard with hzero | ⟨u, hsingle⟩ | ⟨u, v, huv, hpair⟩
  · exact (Finset.not_nonempty_empty (hzero ▸ hKne)).elim
  · have huK : u ∈ K := by simp [hsingle]
    by_cases hgood : GoodCenter G A B u
    · apply hlift (fun x => x u)
      · intro x
        rw [hsingle, repair_singleton_good G s A B C D u hgood]
      · exact raw_center _ gs hok u _
    · obtain ⟨hne, hsafe⟩ := hdata u huK hgood
      apply hlift (fun x => x u && signal V (P u) x)
      · intro x
        rw [hsingle, repair_singleton_bad G s A B C D u hgood, hvalue]
      · exact one_star M gs m V hok hm (P u) hne
          (fun w hw => hwire w (hsub u hw)) (fun w hw => hkeep w (hsub u hw))
          _ u hsafe _ (by have := hbound u; omega)
  · have huK : u ∈ K := by simp [hpair]
    have hvK : v ∈ K := by simp [hpair]
    by_cases hgu : GoodCenter G A B u
    · by_cases hgv : GoodCenter G A B v
      · apply hlift (fun x => x u || x v)
        · intro x
          rw [hpair, repair_pair_good_good G s A B C D u v hgu hgv]
        · exact raw_pair _ gs hok u v _ (by omega)
      · obtain ⟨hne, hsafe⟩ := hdata v hvK hgv
        apply hlift (fun x => x u || (x v && signal V (P v) x))
        · intro x
          rw [hpair, repair_pair_good_bad G s A B C D u v hgu hgv, hvalue]
        · exact raw_and_star M gs m V hok hm (P v) hne
            (fun w hw => hwire w (hsub v hw)) (fun w hw => hkeep w (hsub v hw))
            _ u v hsafe _ (Nat.add_le_add_right (hbound v) 1)
    · by_cases hgv : GoodCenter G A B v
      · obtain ⟨hne, hsafe⟩ := hdata u huK hgu
        apply hlift (fun x => x v || (x u && signal V (P u) x))
        · intro x
          rw [hpair, Finset.pair_comm u v, repair_pair_good_bad G s A B C D v u hgv hgu, hvalue]
        · exact raw_and_star M gs m V hok hm (P u) hne
            (fun w hw => hwire w (hsub u hw)) (fun w hw => hkeep w (hsub u hw))
            _ v u hsafe _ (Nat.add_le_add_right (hbound u) 1)
      · obtain ⟨hneU, hsafeU⟩ := hdata u huK hgu
        obtain ⟨hneV, hsafeV⟩ := hdata v hvK hgv
        by_cases hmerge : (u ∈ C ↔ v ∈ C) ∧ s u = s v
        · have hP : P u = P v := by simp only [P, projection, hmerge.1, hmerge.2]
          have hleaves := leaves_same_clause_color s C D u v hmerge.1 hmerge.2
          apply hlift (fun x => (x u || x v) && signal V (P u) x)
          · intro x
            rw [hpair, repair_pair_bad_same_leaves G s A B C D u v hgu hgv hleaves, hvalue]
          · exact merged_stars M gs m V hok hm (P u) hneU
              (fun w hw => hwire w (hsub u hw)) (fun w hw => hkeep w (hsub u hw))
              _ u v hsafeU (by simpa only [hP] using hsafeV) _
              (Nat.add_le_add_right (hbound u) 1)
        · have hcost := projection_pair_budget atoms s color hmono S T C D hC hD M.card hbudget
            u v (hbad u huK hgu).1 (hbad v hvK hgv).1
            (hpattern u huK v hvK huv hgu hgv) hmerge
          apply hlift (fun x => (x u && signal V (P u) x) || (x v && signal V (P v) x))
          · intro x
            rw [hpair, repair_pair_bad_bad G s A B C D u v hgu hgv, hvalue, hvalue]
          · exact two_stars M gs m V hok hm (P u) (P v) hneU hneV
              (fun w hw => hwire w ((Finset.union_subset (hsub u) (hsub v)) hw))
              (fun w hw => hkeep w ((Finset.union_subset (hsub u) (hsub v)) hw))
              _ u v hsafeU hsafeV _ (by
                change (P u ∪ P v).card + 2 ≤ M.card +
                  (if Disjoint (P u) (P v) then 2 else 1) at hcost
                omega)

end CostedCenter
namespace ActualCut

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
  PEqualNP.Outside.L_meta_5012_aux.Mixed

lemma boundary_values_before {n : ℕ} {C : Circuit} {s : Fin n → Bool} {g h : ℕ}
    (hcut : CutData n C s g h) (R : (Fin n → Bool) → Bool) :
    ∀ x : Fin n → Bool, ∀ w ∈ boundary n C s h 0 ∪ boundary n C s h 1,
      SemanticPatch.values C h R x w = wireVal n C w x := by
  obtain ⟨hh, _, _, _, _, _, _, _, _, _, _, hb, _, _, _⟩ := hcut
  intro x w hw
  apply SemanticPatch.values_before C h R hh x w
  rcases Finset.mem_union.mp hw with hw | hw
  · exact (hb 0 w hw).1
  · exact (hb 1 w hw).1

lemma boundary_values {n : ℕ} {C : Circuit} {s : Fin n → Bool} {g h : ℕ}
    (hcut : CutData n C s g h) (R : (Fin n → Bool) → Bool) :
    ∀ x : Fin n → Bool, ∀ w ∈ boundary n C s h 0 ∪ boundary n C s h 1,
      SemanticPatch.values C h R x w = decide (∃ v ∈ orIn n C w, x v = true) := by
  have hbefore := boundary_values_before hcut R
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hhom, _, _⟩ := hcut
  intro x w hw
  rw [hbefore x w hw]
  rcases Finset.mem_union.mp hw with hw | hw
  · exact (hhom 0 w hw).2.2 x
  · exact (hhom 1 w hw).2.2 x

lemma boundary_atom_values {n : ℕ} {C : Circuit} {s : Fin n → Bool} {g h : ℕ}
    (hcut : CutData n C s g h) (R : (Fin n → Bool) → Bool)
    (atoms : ℕ → Finset (Fin n))
    (hatoms : ∀ w ∈ boundary n C s h 0 ∪ boundary n C s h 1, atoms w = orIn n C w) :
    ∀ x : Fin n → Bool, ∀ w ∈ boundary n C s h 0 ∪ boundary n C s h 1,
      SemanticPatch.values C h R x w = decide (∃ v ∈ atoms w, x v = true) := by
  intro x w hw
  rw [hatoms w hw]
  exact boundary_values hcut R x w hw


lemma boundary_budget {n : ℕ} {C : Circuit} {s : Fin n → Bool} {g h : ℕ}
    (hcut : CutData n C s g h) :
    (boundary n C s h 0 ∪ boundary n C s h 1).card ≤ (removed n C s h).card +
      (if Disjoint (boundary n C s h 0) (boundary n C s h 1) then 2 else 1) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hcost, _⟩ := hcut
  omega

lemma replacement_impossible {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (hL : IsLeastAO G C) (hTop : TopForm G C)
    (rungOne : ∀ D : Circuit, IsLeastAO G D → (junk G D).card = 1 → False)
    (g h : ℕ) (hJ : junk G C = {g, h}) (hindhg : ¬ InCone n C h g)
    (hmix : ∀ c : Bool, gateVal n C h (monoInput s c) = true)
    (hcut : CutData n C s g h)
    (R : (Fin n → Bool) → Bool)
    (hmonoR : ∀ x y, (∀ u, x u = true → y u = true) → R x = true → R y = true)
    (guarded : ∀ x, gateVal n C g x = true → R x = true → graphFun G ∅ x = true)
    (critical : ∀ a b, G.Adj a b → circuitFun n (patch C h off) (pairInput a b) = false →
      R (pairInput a b) = true)
    (block : ∀ (gs : List Gate) (m : ℕ → ℕ), Splice.Ok n gs →
      Splice.Maps n h (removed n C s h) gs m (SemanticPatch.values C h R) →
      ∃ (hs : List Gate) (o : ℕ), Splice.Ok n (gs ++ hs) ∧
        hs.length ≤ (removed n C s h).card + 1 ∧ o < n + (gs ++ hs).length ∧
        (∀ x : Fin n → Bool, (Splice.run (gs ++ hs) (List.ofFn x)).getD o false = R x) ∧
        Splice.dc n (graphFun G ∅) (gs ++ hs) ≤ Splice.dc n (graphFun G ∅) gs) : False := by
  obtain ⟨_, _, hM, _, hgkeep, _, houtM, hread, _, _, _, _, _, _, _⟩ := hcut
  exact SemanticPatch.mixed_semantic_splice_impossible G C s hcol hL hTop rungOne
    g h hJ hindhg hmix (removed n C s h) hM hgkeep houtM
    (fun j hj hkeep => ⟨hread j hj hkeep 0, hread j hj hkeep 1⟩)
    R hmonoR guarded critical block

end ActualCut
namespace ActualCut

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
  PEqualNP.Outside.L_meta_5012_aux.Mixed PEqualNP.Outside.L_meta_5012_aux.CenterGeometry

lemma selected_replacement_impossible {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : NoFourCycle G) (hL : IsLeastAO G C) (hTop : TopForm G C)
    (rungOne : ∀ D : Circuit, IsLeastAO G D → (junk G D).card = 1 → False)
    (g h : ℕ) (hne : h ≠ g) (hindgh : ¬ InCone n C g h) (hindhg : ¬ InCone n C h g)
    (hJ : junk G C = {g, h}) (hmix : ∀ c : Bool, gateVal n C h (monoInput s c) = true)
    (A B K : Finset (Fin n)) (hKne : K.Nonempty) (hKcard : K.card ≤ 2)
    (hbad : ∀ u ∈ K, ¬ GoodCenter G A B u →
      ((u ∈ side (n := n) C h 0 ∧ u ∉ side (n := n) C h 1) ∨
       (u ∈ side (n := n) C h 1 ∧ u ∉ side (n := n) C h 0)) ∧
      (leaves s (side C h 0) (side C h 1) u).Nonempty ∧
      (∀ v ∈ leaves s (side C h 0) (side C h 1) u, G.Adj u v))
    (hpattern : ∀ u ∈ K, ∀ v ∈ K, u ≠ v →
      ¬ GoodCenter G A B u → ¬ GoodCenter G A B v →
      (u ∈ side (n := n) C h 0 ∧ v ∈ side (n := n) C h 0) ∨
      (u ∈ side (n := n) C h 1 ∧ v ∈ side (n := n) C h 1) ∨ s u = s v)
    (R : (Fin n → Bool) → Bool)
    (hR : ∀ x, R x = true ↔ RepairHit G s A B (side C h 0) (side C h 1) K x)
    (hmonoR : ∀ x y, (∀ u, x u = true → y u = true) → R x = true → R y = true)
    (guarded : ∀ x, gateVal n C g x = true → R x = true → graphFun G ∅ x = true)
    (critical : ∀ a b, G.Adj a b → circuitFun n (patch C h off) (pairInput a b) = false →
      R (pairInput a b) = true) : False := by
  classical
  have hcut := actual_mixed_cut G C s hcol h4 hL hTop g h hne hindgh hindhg hJ hmix
  obtain ⟨color, hcolor, hraw, hmixed, _, _⟩ :=
    actual_boundary_atoms G C s hcol h4 hL hTop g h hne hindgh hindhg hJ hmix
  have hatoms : ∀ w ∈ boundary n C s h 0 ∪ boundary n C s h 1,
      boundaryAtoms n C s h w = orIn n C w := by
    intro w hw
    simp only [boundaryAtoms, if_pos hw]
  have hvalues := boundary_atom_values hcut R (boundaryAtoms n C s h) hatoms
  have hbudget := boundary_budget hcut
  have hdata := hcut
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hneB, hkeepB, _, _, _⟩ := hdata
  apply replacement_impossible G C s hcol hL hTop rungOne g h hJ hindhg hmix
    hcut R hmonoR guarded critical
  intro gs m hok hm
  have hb := CostedCenter.selected_center_block G s A B (side C h 0) (side C h 1) K
    (removed n C s h) gs m (SemanticPatch.values C h R) hok hm
    (boundary n C s h 0) (boundary n C s h 1) (boundaryAtoms n C s h) color
    hcolor (hraw 0) (hraw 1) hvalues (hneB 0) (hneB 1) (hmixed 0) (hmixed 1)
    (by
      intro w hw
      rcases Finset.mem_union.mp hw with hw | hw
      · exact (hkeepB 0 w hw).1
      · exact (hkeepB 1 w hw).1)
    (by
      intro w hw
      rcases Finset.mem_union.mp hw with hw | hw
      · exact (hkeepB 0 w hw).2
      · exact (hkeepB 1 w hw).2)
    hbudget hKne hKcard hbad hpattern R hR
  obtain ⟨hs, o, hlen, hOk, hout, hval, hdc⟩ := hb
  exact ⟨hs, o, hOk, hlen, hout, hval, hdc.le⟩

end ActualCut

namespace CompleteIndependent

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
  PEqualNP.Outside.L_meta_5012_aux.Mixed
  PEqualNP.Outside.L_meta_5012_aux.CenterGeometry

lemma oriented_both_mono_impossible {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : NoFourCycle G) (hL : IsLeastAO G C) (hTop : TopForm G C)
    (rungOne : ∀ D : Circuit, IsLeastAO G D → (junk G D).card = 1 → False)
    (g h : ℕ) (hne : h ≠ g) (hindgh : ¬ InCone n C g h) (hindhg : ¬ InCone n C h g)
    (hJ : junk G C = {g, h})
    (hmix : ∀ c : Bool, gateVal n C h (monoInput s c) = true)
    (A B : Finset (Fin n)) (hA : 2 ≤ A.card) (hB : 2 ≤ B.card) (hAB : Disjoint A B)
    (hAcol : ∀ u ∈ A, s u = false) (hBcol : ∀ u ∈ B, s u = true)
    (hgraw : ∀ x, gateVal n C g x = true ↔
      (∃ a ∈ A, x a = true) ∧ (∃ b ∈ B, x b = true)) : False := by
  classical
  let U := side (n := n) C h 0
  let W := side (n := n) C h 1
  have hhraw : ∀ x, gateVal n C h x = true ↔
      (∃ u ∈ U, x u = true) ∧ (∃ w ∈ W, x w = true) := by
    intro x
    rw [independent_junk_raw_value G C hL.1 hTop g h hJ hindgh x]
    simp only [Bool.and_eq_true, decide_eq_true_eq, U, W]
  have hclean : ProductClean G A B U W := by
    intro x ha hb hu hw
    exact NestedMixed.least_mixed_guard_clean G C s hcol hL hTop g h hne hindhg hJ hmix x
      ((hgraw x).mpr ⟨ha, hb⟩) ((hhraw x).mpr ⟨hu, hw⟩)
  have htrace : ∃ u v, (traceGraph G A B U W).Adj u v := by
    obtain ⟨u, v, huv, hg, hh⟩ := joint_accepted_edge G C s hcol hL hTop g h hJ hmix
    obtain ⟨huA, huB⟩ := (hgraw _).mp hg
    obtain ⟨huU, huW⟩ := (hhraw _).mp hh
    exact ⟨u, v, huv, (hit_pair_iff A u v).mp huA, (hit_pair_iff B u v).mp huB,
      (hit_pair_iff U u v).mp huU, (hit_pair_iff W u v).mp huW⟩
  obtain ⟨K, hKne, hKU, hKcard, hcover, hmin, hinc, hstars⟩ :=
    nonempty_minimal_repair_cover G s hcol h4 A B U W hAB hA hB hclean hAcol hBcol htrace
  have hbad : ∀ u ∈ K, ¬ GoodCenter G A B u →
      ((u ∈ U ∧ u ∉ W) ∨ (u ∈ W ∧ u ∉ U)) ∧
      (leaves s U W u).Nonempty ∧ (∀ v ∈ leaves s U W u, G.Adj u v) := by
    intro u hu hnot
    obtain ⟨v, huv⟩ := hinc u hu
    have hd := hstars u hu hnot
    exact ⟨hd.1, ⟨v, hd.2.2 v huv⟩, hd.2.1⟩
  have hpattern : ∀ u ∈ K, ∀ v ∈ K, u ≠ v →
      ¬ GoodCenter G A B u → ¬ GoodCenter G A B v →
      (u ∈ U ∧ v ∈ U) ∨ (u ∈ W ∧ v ∈ W) ∨ s u = s v := by
    intro u hu v hv huv hbu hbv
    exact nongood_pair_pattern G s h4 A B U W K hAB hclean hAcol hBcol hKU hKcard
      hcover hmin u v hu hv huv hbu hbv
  let R := repairBool G s A B U W K
  have hR : ∀ x, R x = true ↔ RepairHit G s A B U W K x := by
    intro x
    simp only [R, repairBool, decide_eq_true_eq]
  have hmonoR : ∀ x y, (∀ u, x u = true → y u = true) → R x = true → R y = true :=
    repair_mono G s A B U W K
  have guarded : ∀ x, gateVal n C g x = true → R x = true → graphFun G ∅ x = true :=
    repair_guarded G C s g A B U W K hgraw (fun u hu hnot => (hstars u hu hnot).2.1)
  have critical : ∀ u v, G.Adj u v → circuitFun n (patch C h off) (pairInput u v) = false →
      R (pairInput u v) = true :=
    repair_covers_critical G C s hcol hL.1 hTop hL.2.1 g h hJ hmix A B U W K hclean
      hgraw hhraw hKU hcover
  exact ActualCut.selected_replacement_impossible G C s hcol h4 hL hTop
    rungOne g h hne hindgh hindhg hJ hmix A B K hKne hKcard hbad hpattern
    R hR hmonoR guarded critical

lemma no_both_mono_independent_pair {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : NoFourCycle G) (hL : IsLeastAO G C) (hTop : TopForm G C)
    (rungOne : ∀ D : Circuit, IsLeastAO G D → (junk G D).card = 1 → False)
    (g h : ℕ) (hne : h ≠ g) (hindgh : ¬ InCone n C g h) (hindhg : ¬ InCone n C h g)
    (hJ : junk G C = {g, h})
    (hmix : ∀ c : Bool, gateVal n C h (monoInput s c) = true) : False := by
  have hdata := MixedSetup.independent_mixed_setup G C s hcol hL hTop
    g h hne hindgh hindhg hJ hmix
  dsimp only at hdata
  obtain ⟨hA, hB, hd, hcolors, _, _, hgv, _, _⟩ := hdata
  have hraw : ∀ x, gateVal n C g x = true ↔
      (∃ a ∈ side (n := n) C g 0, x a = true) ∧
      (∃ b ∈ side (n := n) C g 1, x b = true) := by
    intro x
    rw [hgv x]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
  rcases hcolors with ⟨hAcol, hBcol⟩ | ⟨hAcol, hBcol⟩
  · exact oriented_both_mono_impossible G C s hcol h4 hL hTop rungOne g h hne hindgh hindhg hJ hmix
      (side (n := n) C g 0) (side (n := n) C g 1) hA hB hd hAcol hBcol hraw
  · apply oriented_both_mono_impossible G C s hcol h4 hL hTop rungOne g h hne hindgh hindhg hJ hmix
      (side (n := n) C g 1) (side (n := n) C g 0) hB hA hd.symm hBcol hAcol
    intro x
    exact (hraw x).trans and_comm

end CompleteIndependent

end PEqualNP.Outside.L_meta_5012_aux
