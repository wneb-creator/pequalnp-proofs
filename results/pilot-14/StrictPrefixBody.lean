namespace PEqualNP.Outside.L_meta_670_aux.StrictPrefix

open LiveCheck DynamicLeaf PEqualNP.CircuitLowerBounds

def rootOf (v : List Sig) (roots : List Nat) (a : Sig) : Nat :=
  roots.getD (v.idxOf a) 8

def recipeGate (v : List Sig) (roots : List Nat) : Recipe → Gate
  | .unary a => ⟨.not,[rootOf v roots a]⟩
  | .binary d a b => ⟨if d then .or else .and,[rootOf v roots a,rootOf v roots b]⟩

def traceWire (gs : List Gate) : Nat → Nat → List Nat → List Gate →
    Nat × List Nat × List Gate
  | 0, _, seen, out => (8,seen,out)
  | fuel+1, j, seen, out =>
      MemoForced.forceNat j fun j =>
        if j < 10 then (j,seen,out)
        else if seen.contains j then
          MemoForced.forceNat (10+seen.idxOf j) fun index => (index,seen,out)
        else
          match gs.getD (j-10) ⟨.or,[]⟩ with
          | ⟨op,inputs⟩ =>
              match inputs.foldl (fun (s : List Nat × List Nat × List Gate) a =>
                  match s with
                  | (roots,seen,out) =>
                      match traceWire gs fuel a seen out with
                      | (index,seen,out) =>
                          MemoForced.forceNat index fun index =>
                            (roots ++ [index],seen,out)) ([],seen,out) with
              | (roots,seen,out) =>
                  MemoForced.forceNat (10+out.length) fun index =>
                    (index,seen ++ [j],out ++ [⟨op,roots⟩])

def compactParts (gates : List Gate) (roots : List Nat) : List Gate × List Nat :=
  match roots.foldl (fun (s : List Nat × List Nat × List Gate) j =>
      match s with
      | (roots,seen,out) =>
          match traceWire gates (gates.length+1) j seen out with
          | (index,seen,out) =>
              MemoForced.forceNat index fun index =>
                (roots ++ [index],seen,out)) ([],[],[]) with
  | (roots,_,out) => (out,roots)

def compact : PrefixCtx → PrefixCtx
  | ⟨gates,roots,vals⟩ =>
      let parts := compactParts gates roots
      ⟨parts.1,parts.2,vals⟩

lemma compact_vals (c : PrefixCtx) : (compact c).vals = c.vals := by
  cases c
  rfl

def updateOne (o : Oracle) (v w : List Sig) : PrefixCtx → Option Recipe → PrefixCtx
  | ⟨gates,roots,vals⟩, r =>
      let z := w.headD zero
      let q := proposedValue o v vals z r
      let old := vals.idxOf q
      let cached := vals.contains q
      let free := o.inputs.contains q
      let fresh := !(free || cached)
      let g := match r with
        | some a => recipeGate v roots a
        | none => ⟨.or,[]⟩
      let out := if free then o.inputs.idxOf q
        else if cached then roots.getD old 8 else 10+gates.length
      compact ⟨if fresh then gates ++ [g] else gates,
        w.map (fun a => if a == z then out else rootOf v roots a),
        w.map (fun a => if a == z then q else retrieve o.project v vals a)⟩

lemma updateOne_vals (o : Oracle) (v w : List Sig) (c : PrefixCtx) (r : Option Recipe) :
    (updateOne o v w c r).vals =
      w.map (fun a => if a == w.headD zero then
        proposedValue o v c.vals (w.headD zero) r else retrieve o.project v c.vals a) := by
  cases c
  rfl

def updateWithRecipe {n : Nat} (oracles : Fin n → Oracle) (v w : List Sig)
    (ctx : Context n) (r : Option Recipe) : Context n :=
  fun i => updateOne (oracles i) v w (ctx i) r

lemma updateWithRecipe_valid {n : Nat} {oracles : Fin n → Oracle} {v : List Sig}
    {ctx : Context n} (h : Valid oracles v ctx) (w : List Sig) (r : Option Recipe) :
    Valid oracles w (updateWithRecipe oracles v w ctx r) := by
  intro i
  simp only [updateWithRecipe,updateOne_vals]
  apply List.map_congr_left
  intro a ha
  rw [h i]
  split
  · rename_i he
    rw [proposedValue_map]
    exact congrArg (oracles i).project (beq_iff_eq.mp he).symm
  · exact retrieve_map _ _ _

end PEqualNP.Outside.L_meta_670_aux.StrictPrefix
