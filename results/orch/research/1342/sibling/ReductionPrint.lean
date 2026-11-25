import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_1342_46
    (build : ∀ a b c d : Fin 11,
      let B : Circuit := ⟨[⟨.or,[a.val,b.val]⟩,⟨.or,[c.val,d.val]⟩,⟨.and,[11,12]⟩],13⟩
      Monotone2 B ∧ B.size = 3 ∧ ∀ x : Fin 11 → Bool,
        B.wires (List.ofFn x) = List.ofFn x ++
          [x a || x b, x c || x d, (x a || x b) && (x c || x d)])
    (continuation : ∃ a b c d : Fin 11, ∃ D : Circuit,
      let B : Circuit := ⟨[⟨.or,[a.val,b.val]⟩,⟨.or,[c.val,d.val]⟩,⟨.and,[11,12]⟩],13⟩
      let E : List (ℕ × ℕ) := [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
        (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
      a < b ∧ c < d ∧ a.val * 11 + b.val < c.val * 11 + d.val ∧
      Monotone2 D ∧ D.size ≤ 18 ∧
      (PEqualNP.TopForm.junk (PEqualNP.EdgeOwnership.edgeGraph 11 E)
        (⟨B.gates ++ D.gates,D.output⟩ : Circuit)).card = 2 ∧
      ∀ x : Fin 11 → Bool,
        D.eval (List.ofFn x ++ [x a || x b, x c || x d, (x a || x b) && (x c || x d)]) = true ↔
          ∃ u v : Fin 11, (u.val,v.val) ∈ E ∧ x u = true ∧ x v = true) :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ (∀ x : Fin 11 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 11, (u.val, v.val) ∈ ([(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) ∧ C.size ≤ 21 := by
  obtain ⟨a,b,c,d,D,h⟩ := continuation
  dsimp only at h
  obtain ⟨_,_,_,model,budget,_,correct⟩ := h
  let B : Circuit := ⟨[⟨.or,[a.val,b.val]⟩,⟨.or,[c.val,d.val]⟩,⟨.and,[11,12]⟩],13⟩
  have built := build a b c d
  change Monotone2 B ∧ B.size = 3 ∧ _ at built
  let C : Circuit := ⟨B.gates ++ D.gates,D.output⟩
  refine ⟨C,?_,?_,?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact built.1 g hg
    · exact model g hg
  · intro x
    have eval : C.eval (List.ofFn x) = D.eval (B.wires (List.ofFn x)) := by
      simp [C, Circuit.eval, Circuit.wires, List.foldl_append]
    rw [eval, built.2.2 x]
    exact correct x
  · change (B.gates ++ D.gates).length ≤ 21
    rw [List.length_append]
    change B.size + D.size ≤ 21
    omega

run_elab do
  let ci ← Lean.getConstInfo `PEqualNP.Outside.R_meta_1342_46
  let mut t := ci.type
  for i in [0:2] do
    match t with
    | .forallE _ h rest _ =>
      let mut opts : Lean.Options := {}
      for n in [`pp.fullNames, `pp.funBinderTypes, `pp.numericTypes, `pp.proofs,
                `pp.structureInstanceTypes, `pp.letVarTypes] do
        opts := opts.setBool n true
      let p ← Lean.withOptions (fun _ => opts) (Lean.Meta.ppExpr h)
      let s := p.pretty 1000000
      Lean.logInfo m!"CHILD {i+1} LEN {s.length} {s}"
      t := rest.lowerLooseBVars 1 1
    | _ => throwError "unexpected theorem shape"
