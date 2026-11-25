import PEqualNP.Defs


-- The support invariant follows MetaComplexity.Helpers.Support.

namespace PEqualNP.Outside.L_meta_2585.Support

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

open PEqualNP.CircuitLowerBounds

variable {n : ℕ}

lemma getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

/-- The support of a gate: the union of the supports of the wires it reads. -/
def gateSupp (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

lemma mem_foldr_union (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

lemma mem_gateSupp (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

/-- The supports of all wires, starting from the supports `L` of the wires present. -/
def suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

/-- The supports of the input wires: input `i` has support `{i}`. -/
def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

/-- Wire lists `w`, `w'` (for the inputs `x`, `y`) agree on every wire whose support `x` and
`y` agree on. -/
def Agree (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

lemma agree_wiresFrom (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

lemma agree_inputs (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

/-- Any set `W` of wires has a joint support of size at most `t + |W|`. -/
def Cnt (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

lemma cnt_inputs : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

lemma cnt_step (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ g.inputs.toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

lemma cnt_suppsFrom (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, g.inputs.length ≤ 2) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self) h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this

lemma essential_card_le (n : ℕ) (C : Circuit)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (A : Finset (Fin n))
    (hdep : ∀ i ∈ A, ∃ x : Fin n → Bool,
      PEqualNP.MetaComplexity.circuitFun n C (Function.update x i (!x i)) ≠
        PEqualNP.MetaComplexity.circuitFun n C x) :
    A.card ≤ C.size + 1 := by
  set S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅ with hS
  have hsub : A ⊆ S := by
    intro i hiA
    by_contra hi
    obtain ⟨x, hx⟩ := hdep i hiA
    apply hx
    exact (agree_wiresFrom (Function.update x i (!x i)) x C.gates _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ i := fun e => hi (e ▸ hk)
        simp [Function.update_of_ne this])
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) hfan cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  exact (Finset.card_le_card hsub).trans hc

lemma cast_ne_nat {P L : ℕ} (p : Fin P) (l : Fin L) :
    Fin.castAdd L p ≠ Fin.natAdd P l := by
  intro h
  have hv := congrArg Fin.val h
  change p.val = P + l.val at hv
  omega

lemma incident_point_essential (P L : ℕ) (I : Fin P → Fin L → Prop)
    [DecidableRel I] (C : Circuit)
    (hf : ∀ x : Fin (P + L) → Bool,
      PEqualNP.MetaComplexity.circuitFun (P + L) C x =
        decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
          x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true))
    (p : Fin P) (l : Fin L) (hi : I p l) :
    ∃ x : Fin (P + L) → Bool,
      PEqualNP.MetaComplexity.circuitFun (P + L) C
        (Function.update x (Fin.castAdd L p) (!x (Fin.castAdd L p))) ≠
      PEqualNP.MetaComplexity.circuitFun (P + L) C x := by
  let x : Fin (P + L) → Bool :=
    fun i => decide (i = Fin.castAdd L p ∨ i = Fin.natAdd P l)
  have hp : x (Fin.castAdd L p) = true := by simp [x]
  have hl : x (Fin.natAdd P l) = true := by simp [x]
  have htrue : PEqualNP.MetaComplexity.circuitFun (P + L) C x = true := by
    rw [hf, decide_eq_true_eq]
    exact ⟨p, l, hi, hp, hl⟩
  have hall (q : Fin P) :
      Function.update x (Fin.castAdd L p) (!x (Fin.castAdd L p)) (Fin.castAdd L q) = false := by
    rw [hp]
    by_cases heq : Fin.castAdd L q = Fin.castAdd L p
    · simp [heq]
    · rw [Function.update_of_ne heq]
      simp [x, heq, cast_ne_nat q l]
  have hfalse : PEqualNP.MetaComplexity.circuitFun (P + L) C
      (Function.update x (Fin.castAdd L p) (!x (Fin.castAdd L p))) = false := by
    rw [hf, decide_eq_false_iff_not]
    rintro ⟨q, m, _, hq, _⟩
    rw [hall q] at hq
    exact Bool.false_ne_true hq
  exact ⟨x, by rw [hfalse, htrue]; decide⟩

lemma incident_line_essential (P L : ℕ) (I : Fin P → Fin L → Prop)
    [DecidableRel I] (C : Circuit)
    (hf : ∀ x : Fin (P + L) → Bool,
      PEqualNP.MetaComplexity.circuitFun (P + L) C x =
        decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
          x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true))
    (p : Fin P) (l : Fin L) (hi : I p l) :
    ∃ x : Fin (P + L) → Bool,
      PEqualNP.MetaComplexity.circuitFun (P + L) C
        (Function.update x (Fin.natAdd P l) (!x (Fin.natAdd P l))) ≠
      PEqualNP.MetaComplexity.circuitFun (P + L) C x := by
  let x : Fin (P + L) → Bool :=
    fun i => decide (i = Fin.castAdd L p ∨ i = Fin.natAdd P l)
  have hp : x (Fin.castAdd L p) = true := by simp [x]
  have hl : x (Fin.natAdd P l) = true := by simp [x]
  have htrue : PEqualNP.MetaComplexity.circuitFun (P + L) C x = true := by
    rw [hf, decide_eq_true_eq]
    exact ⟨p, l, hi, hp, hl⟩
  have hall (m : Fin L) :
      Function.update x (Fin.natAdd P l) (!x (Fin.natAdd P l)) (Fin.natAdd P m) = false := by
    rw [hl]
    by_cases heq : Fin.natAdd P m = Fin.natAdd P l
    · simp [heq]
    · rw [Function.update_of_ne heq]
      simp [x, heq, (cast_ne_nat p m).symm]
  have hfalse : PEqualNP.MetaComplexity.circuitFun (P + L) C
      (Function.update x (Fin.natAdd P l) (!x (Fin.natAdd P l))) = false := by
    rw [hf, decide_eq_false_iff_not]
    rintro ⟨q, m, _, _, hm⟩
    rw [hall m] at hm
    exact Bool.false_ne_true hm
  exact ⟨x, by rw [hfalse, htrue]; decide⟩

lemma incident_vertices_card_le (P L : ℕ) (I : Fin P → Fin L → Prop)
    [DecidableRel I] (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 (P + L) C)
    (hf : ∀ x : Fin (P + L) → Bool,
      PEqualNP.MetaComplexity.circuitFun (P + L) C x =
        decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
          x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true)) :
    (Finset.univ.filter (fun v : Fin (P + L) => ∃ p : Fin P, ∃ l : Fin L,
      I p l ∧ (v = Fin.castAdd L p ∨ v = Fin.natAdd P l))).card ≤ C.size + 1 := by
  apply essential_card_le
  · intro g hg
    exact (hC.2.2 g hg).le
  · intro v hv
    obtain ⟨p, l, hi, hv⟩ := (Finset.mem_filter.mp hv).2
    rcases hv with rfl | rfl
    · exact incident_point_essential P L I C hf p l hi
    · exact incident_line_essential P L I C hf p l hi

end PEqualNP.Outside.L_meta_2585.Support


namespace PEqualNP.Outside.L_meta_2585.FreshCostExample

open PEqualNP.CircuitLowerBounds

set_option maxHeartbeats 0
set_option maxRecDepth 100000

-- Two disjoint three-leaf stars amplify the repeated edges without amplifying
-- the gap between this dirty circuit and the ordinary read-one construction.

def C : Circuit :=
  ⟨[⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [8, 4]⟩,
    ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.or, [10, 7]⟩,
    ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [9, 11]⟩,
    ⟨GateOp.or, [0, 11]⟩, ⟨GateOp.or, [1, 9]⟩,
    ⟨GateOp.and, [12, 13]⟩, ⟨GateOp.and, [14, 15]⟩,
    ⟨GateOp.and, [16, 17]⟩], 18⟩

def D : Circuit :=
  ⟨[⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [8, 4]⟩,
    ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.or, [10, 7]⟩,
    ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.and, [1, 11]⟩,
    ⟨GateOp.or, [12, 13]⟩], 14⟩

def E : List (ℕ × ℕ) := [(0, 2), (0, 3), (0, 4), (1, 5), (1, 6), (1, 7)]

def isLine (i : ℕ) : Bool := decide (2 ≤ i)

def I (p : Fin 2) (l : Fin 6) : Prop :=
  (p = 0 ∧ l.val < 3) ∨ (p = 1 ∧ 3 ≤ l.val)

instance : DecidableRel I := fun _ _ => by unfold I; infer_instance

lemma valid_C : PEqualNP.TopForm.IsAO2 8 C := by decide

lemma valid_D : PEqualNP.TopForm.IsAO2 8 D := by decide

lemma no_four_cycle : ∀ p p' : Fin 2, ∀ l l' : Fin 6,
    p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l') := by decide

lemma computes_C : ∀ z : Fin 8 → Bool,
    PEqualNP.MetaComplexity.circuitFun 8 C z =
      decide (∃ p : Fin 2, ∃ l : Fin 6, I p l ∧
        z (Fin.castAdd 6 p) = true ∧ z (Fin.natAdd 2 l) = true) := by decide

lemma computes_D : ∀ z : Fin 8 → Bool,
    PEqualNP.MetaComplexity.circuitFun 8 D z =
      decide (∃ p : Fin 2, ∃ l : Fin 6, I p l ∧
        z (Fin.castAdd 6 p) = true ∧ z (Fin.natAdd 2 l) = true) := by decide

lemma all_interior_not_below : ∀ w : Fin 18,
    ¬ PEqualNP.CircuitMoves.WireBelowOutput 8 C w.val := by decide

lemma all_edges_double_reread : PEqualNP.ReadK.doubleReread C 8 isLine E = E := by decide

lemma read_one_D : PEqualNP.ReadK.IsReadK 8 D 1 := by decide

lemma sizes : C.size = 11 ∧ D.size = 7 := by decide

lemma repeats_exceed_size_gap :
    C.size - D.size < (PEqualNP.ReadK.doubleReread C 8 isLine E).length := by decide

end PEqualNP.Outside.L_meta_2585.FreshCostExample


namespace PEqualNP.Outside.L_meta_2585.FreshCostExample

lemma replacement_optimal (T : PEqualNP.CircuitLowerBounds.Circuit)
    (hT : PEqualNP.TopForm.IsAO2 8 T)
    (hf : PEqualNP.MetaComplexity.circuitFun 8 T =
      PEqualNP.MetaComplexity.circuitFun 8 C) : D.size ≤ T.size := by
  have hTf : ∀ z : Fin 8 → Bool,
      PEqualNP.MetaComplexity.circuitFun 8 T z =
        decide (∃ p : Fin 2, ∃ l : Fin 6, I p l ∧
          z (Fin.castAdd 6 p) = true ∧ z (Fin.natAdd 2 l) = true) := by
    intro z
    rw [hf]
    exact computes_C z
  have hbound := PEqualNP.Outside.L_meta_2585.Support.incident_vertices_card_le
    2 6 I T hT hTf
  have hcard : (Finset.univ.filter (fun v : Fin (2 + 6) =>
      ∃ p : Fin 2, ∃ l : Fin 6, I p l ∧
        (v = Fin.castAdd 6 p ∨ v = Fin.natAdd 2 l))).card = 8 := by decide
  rw [hcard] at hbound
  change 7 ≤ T.size
  omega

lemma optimum_plus_repeats_too_large :
    C.size < D.size + (PEqualNP.ReadK.doubleReread C 8 isLine E).length := by decide

end PEqualNP.Outside.L_meta_2585.FreshCostExample
