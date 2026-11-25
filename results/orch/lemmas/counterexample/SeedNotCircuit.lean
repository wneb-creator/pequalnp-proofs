import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1890_aux

def edgeValue (x : Fin 10 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
  (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
  (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) ||
  (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)

def seedVertex (s : Fin 2) : Fin 10 := if s = 0 then 0 else 2

def seedOther (s : Fin 2) : Fin 10 := if s = 0 then 2 else 0

def seedNeighbor (s : Fin 2) : Fin 10 := if s = 0 then 5 else 7

def seedOff (s : Fin 2) (useOr : Bool) (i : Fin 10) : Bool :=
  decide (i = seedNeighbor s) || (!useOr && decide (i = seedOther s))

def seedOn (s : Fin 2) (useOr : Bool) (i : Fin 10) : Bool :=
  seedOff s useOr i || decide (i = seedVertex s)

def seedFold (s : Fin 2) (useOr : Bool) (x : Fin 10 → Bool) : Bool :=
  if useOr then x (seedVertex s) || !(x 0 && x 2)
  else x (seedVertex s) && !(x 0 && x 2)

lemma seed_not_collisions (s : Fin 2) (useOr : Bool) :
    ∃ x y : Fin 10 → Bool,
      (∀ i, i ≠ seedVertex s → x i = y i) ∧
      seedFold s useOr x = seedFold s useOr y ∧
      edgeValue x = false ∧ edgeValue y = true := by
  refine ⟨seedOff s useOr, seedOn s useOr, ?_⟩
  fin_cases s <;> cases useOr <;> decide +kernel


lemma wires_agree_safe (safe : Nat → Prop)
    (gs : List PEqualNP.CircuitLowerBounds.Gate) (a b : List Bool)
    (hlen : a.length = b.length)
    (hsafe : ∀ g ∈ gs, ∀ i ∈ g.inputs, safe i)
    (hbase : ∀ i, safe i → a.getD i false = b.getD i false) :
    ∀ i, safe i →
      ((⟨gs, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires a).getD i false =
        ((⟨gs, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires b).getD i false := by
  induction gs generalizing a b with
  | nil => exact hbase
  | cons g gs ih =>
    have hv : g.op.eval (g.inputs.map fun i => a.getD i false) =
        g.op.eval (g.inputs.map fun i => b.getD i false) := by
      apply congrArg g.op.eval
      apply List.map_congr_left
      intro i hi
      exact hbase i (hsafe g List.mem_cons_self i hi)
    have next : ∀ i, safe i →
        (a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)]).getD i false =
          (b ++ [g.op.eval (g.inputs.map fun i => b.getD i false)]).getD i false := by
      intro i hi
      by_cases h : i < a.length
      · rw [List.getD_append _ _ _ _ h, List.getD_append _ _ _ _ (by omega)]
        exact hbase i hi
      · rw [List.getD_append_right _ _ _ _ (by omega),
          List.getD_append_right _ _ _ _ (by omega)]
        rw [hlen, hv]
    simpa only [PEqualNP.CircuitLowerBounds.Circuit.wires, List.foldl_cons] using
      ih _ _ (by simp [hlen]) (fun g hg i hi => hsafe g (List.mem_cons_of_mem _ hg) i hi) next

def seedTail (s : Fin 2) (useOr : Bool) (x : Fin 10 → Bool) : List Bool :=
  List.ofFn x ++ [x 0 && x 2, !(x 0 && x 2), seedFold s useOr x]

def seedSafe (s : Fin 2) (i : Nat) : Prop :=
  i ≠ (seedVertex s).val ∧ i ≠ 10 ∧ i ≠ 11

lemma seed_tail_agreement (s : Fin 2) (useOr : Bool) (i : Nat) (hi : seedSafe s i) :
    (seedTail s useOr (seedOff s useOr)).getD i false =
      (seedTail s useOr (seedOn s useOr)).getD i false := by
  have finite : ∀ (s : Fin 2) (useOr : Bool) (i : Fin 13), seedSafe s i.val →
      (seedTail s useOr (seedOff s useOr)).getD i.val false =
        (seedTail s useOr (seedOn s useOr)).getD i.val false := by
    unfold seedSafe
    decide +kernel
  by_cases h : i < 13
  · exact finite s useOr ⟨i, h⟩ hi
  · rw [List.getD_eq_default _ _ (by simp [seedTail]; omega),
        List.getD_eq_default _ _ (by simp [seedTail]; omega)]

lemma seed_values (s : Fin 2) (useOr : Bool) :
    edgeValue (seedOff s useOr) = false ∧ edgeValue (seedOn s useOr) = true := by
  fin_cases s <;> cases useOr <;> decide +kernel

lemma seed_not_tail_impossible (s : Fin 2) (useOr : Bool)
    (D : PEqualNP.CircuitLowerBounds.Circuit)
    (hsafe : ∀ g ∈ D.gates, ∀ i ∈ g.inputs, seedSafe s i)
    (hout : seedSafe s D.output) :
    ¬∀ x : Fin 10 → Bool, D.eval (seedTail s useOr x) = edgeValue x := by
  intro correct
  have eq := wires_agree_safe (seedSafe s) D.gates
    (seedTail s useOr (seedOff s useOr)) (seedTail s useOr (seedOn s useOr))
    (by simp [seedTail]) hsafe (seed_tail_agreement s useOr) D.output hout
  change D.eval (seedTail s useOr (seedOff s useOr)) =
    D.eval (seedTail s useOr (seedOn s useOr)) at eq
  rw [correct, correct, (seed_values s useOr).1, (seed_values s useOr).2] at eq
  cases eq

end PEqualNP.Outside.L_meta_1890_aux
