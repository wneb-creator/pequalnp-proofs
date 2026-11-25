namespace PEqualNP.Outside.L_meta_6659_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def overrideOfficialGate (g : Bool × ℕ × ℕ) : Gate :=
  ⟨if g.1 then .and else .or, [g.2.1, g.2.2]⟩

def overrideOfficial (D : Dag) (output : ℕ) : Circuit :=
  ⟨D.map overrideOfficialGate, output⟩

lemma overrideOfficial_size (D : Dag) (output : ℕ) : (overrideOfficial D output).size = D.length := by
  simp [overrideOfficial, Circuit.size]

lemma overrideOfficial_monotone (D : Dag) (output : ℕ) : Monotone2 (overrideOfficial D output) := by
  intro g hg
  obtain ⟨⟨t,a,b⟩, _, rfl⟩ := List.mem_map.mp hg
  cases t <;> simp [overrideOfficialGate]

lemma overrideOfficial_fold (D : Dag) (x : List Bool) :
    (D.map overrideOfficialGate).foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x = wl D x := by
  induction D generalizing x with
  | nil => rfl
  | cons g D ih =>
    obtain ⟨t,a,b⟩ := g
    cases t
    · simpa [overrideOfficialGate, wl, wstep, GateOp.eval, gop] using
        ih (x ++ [gop false (x.getD a false) (x.getD b false)])
    · simpa [overrideOfficialGate, wl, wstep, GateOp.eval, gop] using
        ih (x ++ [gop true (x.getD a false) (x.getD b false)])

lemma overrideOfficial_wires (D : Dag) (output : ℕ) (x : List Bool) :
    (overrideOfficial D output).wires x = wl D x := overrideOfficial_fold D x

lemma overrideOfficial_eval (D : Dag) (output : ℕ) {n : ℕ} (x : Fin n → Bool) :
    (overrideOfficial D output).eval (List.ofFn x) = val D x output := by
  rw [Circuit.eval, overrideOfficial_wires]
  rfl

lemma overrideAlias_smaller {n : Nat} {D : Dag} (edit : Nat) (he : edit < D.length)
    (output : Nat) :
    (∃ b : Bool, ∀ x : Fin n → Bool,val (overrideAlias D edit) x output=b) ∨
    (∃ i : Fin n, ∀ x : Fin n → Bool,val (overrideAlias D edit) x output=x i) ∨
    (∃ E : Dag,Strict n E ∧ E≠[] ∧ E.length<D.length ∧
      ∀ x : Fin n → Bool,val E x (outW n E)=val (overrideAlias D edit) x output) := by
  let C := overrideOfficial (overrideAlias D edit) output
  have duplicate : ∃ g ∈ C.gates, ∃ a,g.inputs=[a,a] := by
    have bound : edit < (overrideAlias D edit).length := by simpa [overrideAlias_length] using he
    refine ⟨overrideOfficialGate ((overrideAlias D edit)[edit]),?_,opB D edit,?_⟩
    · apply List.mem_map.mpr
      exact ⟨_,List.getElem_mem bound,rfl⟩
    · simp [overrideOfficialGate,overrideAlias]
  rcases override_strict_of_duplicate C (overrideOfficial_monotone _ _) duplicate with
    constant | input | ⟨E,strict,nonempty,size,correct⟩
  · obtain ⟨b,hb⟩ := constant
    exact Or.inl ⟨b,fun x => (overrideOfficial_eval _ output x).symm.trans (hb x)⟩
  · obtain ⟨i,hi⟩ := input
    exact Or.inr (Or.inl ⟨i,fun x => (overrideOfficial_eval _ output x).symm.trans (hi x)⟩)
  · have size' : E.length < D.length := by
      simpa only [C,overrideOfficial_size,overrideAlias_length] using size
    exact Or.inr (Or.inr ⟨E,strict,nonempty,size',fun x =>
      (correct x).trans (overrideOfficial_eval _ output x)⟩)

end PEqualNP.Outside.L_meta_6659_aux
