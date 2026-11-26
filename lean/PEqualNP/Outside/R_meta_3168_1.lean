import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.NotBracket
open PEqualNP.MetaComplexity.NestedCover

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
set_option synthInstance.maxSize 512 in
theorem PEqualNP.Outside.R_meta_3168_1
    (many :
      let target (x : Fin 9 → Bool) : Bool :=
        ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
          (fun k => x (Fin.ofNat 9 (k / 10)) && x (Fin.ofNat 9 (k % 10)))
      ∀ C : Circuit, FanInTwo C → C.size = 14 → 2 ≤ notCount C → ¬ (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 && x 2]) = target x))
    (endpoint :
      let target (x : Fin 9 → Bool) : Bool :=
        ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
          (fun k => x (Fin.ofNat 9 (k / 10)) && x (Fin.ofNat 9 (k % 10)))
      let read (C : Circuit) (i : ℕ) := C.gates.filter (fun g => decide (i ∈ g.inputs))
      let strict (C : Circuit) : Prop :=
        ∀ g ∈ C.gates, (g.op = GateOp.not ∧ g.inputs.length = 1) ∨
          (g.op ≠ GateOp.not ∧ g.inputs.length = 2 ∧ g.inputs.Nodup)
      ∀ (C : Circuit) (e : ℕ), e ∈ ([0,2] : List ℕ) →
        FanInTwo C → strict C → notCount C ≤ 1 → (read C e).length = 1 →
        (∀ g ∈ C.gates, e ∈ g.inputs → 9 ∉ g.inputs ∧ (if e = 0 then 2 else 0) ∉ g.inputs) →
        (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 && x 2]) = target x) →
        ∀ g ∈ C.gates, e ∈ g.inputs → ∃ i ∈ g.inputs, 10 ≤ i)
    (remaining :
      let target (x : Fin 9 → Bool) : Bool :=
        ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
          (fun k => x (Fin.ofNat 9 (k / 10)) && x (Fin.ofNat 9 (k % 10)))
      let read (C : Circuit) (i : ℕ) := C.gates.filter (fun g => decide (i ∈ g.inputs))
      let strict (C : Circuit) : Prop :=
        ∀ g ∈ C.gates, (g.op = GateOp.not ∧ g.inputs.length = 1) ∨
          (g.op ≠ GateOp.not ∧ g.inputs.length = 2 ∧ g.inputs.Nodup)
      ∀ C : Circuit, FanInTwo C → ReadsBack 10 C → strict C → C.size = 14 → notCount C ≤ 1 →
        (∃ g : Gate, g.op = GateOp.or ∧ read C 9 = [g]) →
        (∀ e ∈ ([0,2] : List ℕ), (read C e).length = 1) →
        (∀ i : Fin 9, (read C i.val).length ≤ ([1,3,1,3,2,3,2,2,3] : List ℕ).getD i.val 0) →
        (∀ e ∈ ([0,2] : List ℕ), ∀ g ∈ C.gates, e ∈ g.inputs → ∃ i ∈ g.inputs, 10 ≤ i) →
        ¬ (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 && x 2]) = target x)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   have x2 : ℕ → List PEqualNP.CircuitLowerBounds.Gate := fun (x2 : ℕ) => List.filter (fun (x3 : PEqualNP.CircuitLowerBounds.Gate) => Decidable.decide (x2 ∈ x3.inputs)) x1.gates;   PEqualNP.MetaComplexity.FanInTwo x1 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (10 : ℕ) x1 → (∀ x5 ∈ x1.gates, (x5.op = PEqualNP.CircuitLowerBounds.GateOp.not → x5.inputs.length = (1 : ℕ)) ∧ (x5.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → x5.inputs.length = (2 : ℕ) ∧ x5.inputs.Nodup)) → x1.size = (14 : ℕ) → (∃ (x7 : PEqualNP.CircuitLowerBounds.Gate), x7.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ x2 (9 : ℕ) = [x7]) → (∀ x8 ∈ [(0 : ℕ), (2 : ℕ)], (x2 x8).length = (1 : ℕ)) → (∀ x9 ∈ [(4 : ℕ), (6 : ℕ), (7 : ℕ)], (x2 x9).length ≤ (2 : ℕ)) → (∀ (x10 : Fin (9 : ℕ)), (x2 ↑x10).length ≤ (3 : ℕ)) → (∀ x11 ∈ x1.gates, ¬((0 : ℕ) ∈ x11.inputs ∧ (2 : ℕ) ∈ x11.inputs) ∧ ((9 : ℕ) ∈ x11.inputs → (0 : ℕ) ∉ x11.inputs ∧ (2 : ℕ) ∉ x11.inputs)) → ¬∀ (x12 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x12 ++ [x12 (0 : Fin (9 : ℕ)) && x12 (2 : Fin (9 : ℕ))]) = (x12 (0 : Fin (9 : ℕ)) && x12 (1 : Fin (9 : ℕ)) || x12 (1 : Fin (9 : ℕ)) && x12 (2 : Fin (9 : ℕ)) || x12 (2 : Fin (9 : ℕ)) && x12 (3 : Fin (9 : ℕ)) || x12 (3 : Fin (9 : ℕ)) && x12 (4 : Fin (9 : ℕ)) || x12 (4 : Fin (9 : ℕ)) && x12 (0 : Fin (9 : ℕ)) || x12 (0 : Fin (9 : ℕ)) && x12 (5 : Fin (9 : ℕ)) || x12 (1 : Fin (9 : ℕ)) && x12 (6 : Fin (9 : ℕ)) || x12 (2 : Fin (9 : ℕ)) && x12 (7 : Fin (9 : ℕ)) || x12 (3 : Fin (9 : ℕ)) && x12 (8 : Fin (9 : ℕ)) || x12 (5 : Fin (9 : ℕ)) && x12 (7 : Fin (9 : ℕ)) || x12 (6 : Fin (9 : ℕ)) && x12 (8 : Fin (9 : ℕ)) || x12 (8 : Fin (9 : ℕ)) && x12 (5 : Fin (9 : ℕ))) := by
  intro C
  dsimp only
  intro hFan hBack hClean hSize hOr hEnds hRare hCaps hDisjoint hEval
  let target (x : Fin 9 → Bool) : Bool :=
    ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
      (fun k => x (Fin.ofNat 9 (k / 10)) && x (Fin.ofNat 9 (k % 10)))
  let read (i : ℕ) := C.gates.filter (fun g => decide (i ∈ g.inputs))
  have simple (x : Fin 9 → Bool) : target x =
      (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
       x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
       x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) := by
    simp only [target, List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc] <;> rfl
  have correct (x : Fin 9 → Bool) : C.eval (List.ofFn x ++ [x 0 && x 2]) = target x :=
    (hEval x).trans (simple x).symm
  by_cases hTwo : 2 ≤ notCount C
  · exact many C hFan hSize hTwo correct
  have hOne : notCount C ≤ 1 := by omega
  have hStrict : ∀ g ∈ C.gates, (g.op = GateOp.not ∧ g.inputs.length = 1) ∨
      (g.op ≠ GateOp.not ∧ g.inputs.length = 2 ∧ g.inputs.Nodup) := by
    intro g hg
    by_cases hn : g.op = GateOp.not
    · exact Or.inl ⟨hn, (hClean g hg).1 hn⟩
    · exact Or.inr ⟨hn, (hClean g hg).2 hn⟩
  have computed : ∀ e ∈ ([0,2] : List ℕ), ∀ g ∈ C.gates,
      e ∈ g.inputs → ∃ i ∈ g.inputs, 10 ≤ i := by
    intro e he
    apply endpoint C e he hFan hStrict hOne (hEnds e he) ?_ correct
    intro g hg hr
    have hBoth := hDisjoint g hg
    have he' : e = 0 ∨ e = 2 := by
      simpa only [List.mem_cons, List.not_mem_nil, or_false] using he
    rcases he' with h | h
    · subst e
      refine ⟨fun h9 => (hBoth.2 h9).1 hr, ?_⟩
      change 2 ∉ g.inputs
      exact fun h2 => hBoth.1 ⟨hr, h2⟩
    · subst e
      refine ⟨fun h9 => (hBoth.2 h9).2 hr, ?_⟩
      change 0 ∉ g.inputs
      exact fun h0 => hBoth.1 ⟨h0, hr⟩
  have compactCaps : ∀ i : Fin 9,
      (read i.val).length ≤ ([1,3,1,3,2,3,2,2,3] : List ℕ).getD i.val 0 := by
    let budget : List ℕ := [1,3,1,3,2,3,2,2,3]
    have cases : ∀ i : Fin 9,
        (i.val ∈ ([0,2] : List ℕ) ∧ budget.getD i.val 0 = 1) ∨
        (i.val ∈ ([4,6,7] : List ℕ) ∧ budget.getD i.val 0 = 2) ∨
        budget.getD i.val 0 = 3 := by
      decide +kernel
    intro i
    change (read i.val).length ≤ budget.getD i.val 0
    rcases cases i with ⟨he, ht⟩ | ⟨he, ht⟩ | ht
    · exact (hEnds i.val he).le.trans_eq ht.symm
    · exact (hRare i.val he).trans_eq ht.symm
    · exact (hCaps i).trans_eq ht.symm
  exact remaining C hFan hBack hStrict hSize hOne hOr hEnds compactCaps computed correct
