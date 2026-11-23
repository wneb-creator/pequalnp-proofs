import DynamicBase
namespace PEqualNP.Outside.L_meta_670_aux.DynamicLeaf

open PEqualNP.CircuitLowerBounds
open LiveCheck ProjectionData

structure Oracle where
  project : Sig → Base1007.Sig
  mapNeg : ∀ a, project (neg a) = Base1007.neg (project a)
  mapBin : ∀ d a b, project (bin d a b) = Base1007.bin d (project a) (project b)
  inputs : List Base1007.Sig
  check : Nat → List Gate → List Base1007.Sig → Bool
  sound : ∀ {k t : Nat} {v : List Sig} {gs : List Gate} {ps : List Base1007.Sig},
    v.Nodup → ps = v.map project → check k gs ps = true → Impossible k t v

structure PrefixCtx where
  gates : List Gate
  roots : List Nat
  vals : List Base1007.Sig

abbrev Context (n : Nat) := Fin n → PrefixCtx

def Valid {n : Nat} (oracles : Fin n → Oracle) (v : List Sig) (ctx : Context n) : Prop :=
  ∀ i, (ctx i).vals = v.map (oracles i).project

def retrieve (p : Sig → Base1007.Sig) :
    List Sig → List Base1007.Sig → Sig → Base1007.Sig
  | a :: v, b :: ps, z => if z == a then b else retrieve p v ps z
  | _, _, z => p z

lemma retrieve_map (p : Sig → Base1007.Sig) (v : List Sig) (z : Sig) :
    retrieve p v (v.map p) z = p z := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    simp only [List.map_cons, retrieve]
    split
    · rename_i h
      exact congrArg p (beq_iff_eq.mp h).symm
    · exact ih

inductive Recipe where
  | unary (a : Sig)
  | binary (d : Bool) (a b : Sig)

def Recipe.value : Recipe → Sig
  | .unary a => neg a
  | .binary d a b => bin d a b

def Recipe.projected (p : Sig → Base1007.Sig) (v : List Sig)
    (ps : List Base1007.Sig) : Recipe → Base1007.Sig
  | .unary a => Base1007.neg (retrieve p v ps a)
  | .binary d a b => Base1007.bin d (retrieve p v ps a) (retrieve p v ps b)

lemma Recipe.projected_map (o : Oracle) (v : List Sig) (r : Recipe) :
    r.projected o.project v (v.map o.project) = o.project r.value := by
  cases r <;> simp only [Recipe.projected, Recipe.value, retrieve_map,
    o.mapNeg, o.mapBin]

def proposedValue (o : Oracle) (v : List Sig) (ps : List Base1007.Sig)
    (z : Sig) (r : Option Recipe) : Base1007.Sig :=
  match r with
  | none => retrieve o.project v ps z
  | some r => if r.value == z then r.projected o.project v ps
    else retrieve o.project v ps z

lemma proposedValue_map (o : Oracle) (v : List Sig) (z : Sig) (r : Option Recipe) :
    proposedValue o v (v.map o.project) z r = o.project z := by
  cases r with
  | none => exact retrieve_map _ _ _
  | some r =>
    simp only [proposedValue]
    split
    · rename_i h
      rw [Recipe.projected_map, (beq_iff_eq.mp h)]
    · exact retrieve_map _ _ _

def findUnary (v : List Sig) (z : Sig) : Option Recipe :=
  (v.find? fun a => neg a == z).map Recipe.unary

def findBinary (v : List Sig) (z : Sig) : Option Recipe :=
  v.findSome? fun a => v.findSome? fun b =>
    if bin false a b == z then some (.binary false a b)
    else if bin true a b == z then some (.binary true a b) else none

def rootOf (v : List Sig) (c : PrefixCtx) (a : Sig) : Nat :=
  c.roots.getD (v.idxOf a) 8

def recipeGate (v : List Sig) (c : PrefixCtx) : Recipe → Gate
  | .unary a => ⟨.not, [rootOf v c a]⟩
  | .binary d a b => ⟨if d then .or else .and, [rootOf v c a,rootOf v c b]⟩

def traceWire (gs : List Gate) : Nat → Nat → List Nat → List Gate →
    Nat × List Nat × List Gate
  | 0, _, seen, out => (8,seen,out)
  | fuel+1, j, seen, out =>
    if j < 10 then (j,seen,out)
    else if seen.contains j then (10+seen.idxOf j,seen,out)
    else
      let g := gs.getD (j-10) ⟨.or,[]⟩
      let acc := g.inputs.foldl (fun (s : List Nat × List Nat × List Gate) a =>
        let q := traceWire gs fuel a s.2.1 s.2.2
        (s.1 ++ [q.1],q.2.1,q.2.2)) ([],seen,out)
      (10+acc.2.2.length,acc.2.1 ++ [j],acc.2.2 ++ [⟨g.op,acc.1⟩])

def compact (c : PrefixCtx) : PrefixCtx :=
  let acc := c.roots.foldl (fun (s : List Nat × List Nat × List Gate) j =>
    let q := traceWire c.gates (c.gates.length+1) j s.2.1 s.2.2
    (s.1 ++ [q.1],q.2.1,q.2.2)) ([],[],[])
  ⟨acc.2.2,acc.1,c.vals⟩

def updateOne (o : Oracle) (v w : List Sig) (c : PrefixCtx)
    (r : Option Recipe) : PrefixCtx :=
  let z := w.headD zero
  let q := proposedValue o v c.vals z r
  let old := c.vals.idxOf q
  let cached := c.vals.contains q
  let free := o.inputs.contains q
  let fresh := !(free || cached)
  let g := match r with
    | some a => recipeGate v c a
    | none => ⟨.or,[]⟩
  let out := if free then o.inputs.idxOf q
    else if cached then c.roots.getD old 8 else 10+c.gates.length
  compact ⟨if fresh then c.gates ++ [g] else c.gates,
    w.map (fun a => if a == z then out else rootOf v c a),
    w.map (fun a => if a == z then q else retrieve o.project v c.vals a)⟩

def update {n : Nat} (oracles : Fin n → Oracle) (unary : Bool)
    (v w : List Sig) (ctx : Context n) : Context n :=
  let r := if unary then findUnary v (w.headD zero) else findBinary v (w.headD zero)
  fun i => updateOne (oracles i) v w (ctx i) r

lemma update_valid {n : Nat} {oracles : Fin n → Oracle} {v : List Sig}
    {ctx : Context n} (h : Valid oracles v ctx)
    (u : Bool) (w : List Sig) : Valid oracles w (update oracles u v w ctx) := by
  intro i
  simp only [update, updateOne, compact]
  apply List.map_congr_left
  intro a ha
  rw [h i]
  split
  · rename_i he
    rw [proposedValue_map]
    exact congrArg (oracles i).project (beq_iff_eq.mp he).symm
  · exact retrieve_map _ _ _

def initial {n : Nat} (oracles : Fin n → Oracle) (v : List Sig)
    (programs : Fin n → List Gate × List Nat) : Context n :=
  fun i => ⟨(programs i).1,(programs i).2,v.map (oracles i).project⟩

lemma initial_valid {n : Nat} (oracles : Fin n → Oracle) (v : List Sig)
    (programs : Fin n → List Gate × List Nat) :
    Valid oracles v (initial oracles v programs) := fun _ => rfl

end PEqualNP.Outside.L_meta_670_aux.DynamicLeaf
namespace PEqualNP.Outside.L_meta_670_aux.DynamicLeaf

open LiveCheck

def pruned {n : Nat} (oracles : Fin n → Oracle) (k : Nat) (ctx : Context n) : Bool :=
  (List.finRange n).any fun i => (oracles i).check k (ctx i).gates (ctx i).vals

def search {n : Nat} (oracles : Fin n → Oracle) :
    Nat → Nat → List Sig → Context n → Bool
  | 0, _, v, ctx =>
    if v.Nodup then if pruned oracles 0 ctx then false else v == [target] else true
  | k+1, t, v, ctx =>
    if v.Nodup then
      if pruned oracles (k+1) ctx then false else
        stepTest k t v
          (fun w => search oracles k (t-1) w (update oracles true v w ctx))
          (fun w => search oracles k t w (update oracles false v w ctx))
    else true

lemma pruned_sound {n k t : Nat} {oracles : Fin n → Oracle}
    {v : List Sig} {ctx : Context n} (hv : v.Nodup) (hctx : Valid oracles v ctx)
    (hc : pruned oracles k ctx = true) : Impossible k t v := by
  obtain ⟨i,hi,hc⟩ := List.any_eq_true.mp hc
  exact (oracles i).sound hv (hctx i) hc

lemma search_sound {n : Nat} (oracles : Fin n → Oracle)
    (k t : Nat) (v : List Sig) (ctx : Context n) (hctx : Valid oracles v ctx)
    (hc : search oracles k t v ctx = false) : Impossible k t v := by
  induction k generalizing t v ctx with
  | zero =>
    by_cases hv : v.Nodup
    · by_cases hp : pruned oracles 0 ctx = true
      · exact pruned_sound hv hctx hp
      · have hs : (v == [target]) = false := by
          simpa only [search, if_pos hv, if_neg hp] using hc
        exact exclude_search hv hs
    · simp [search,hv] at hc
  | succ k ih =>
    by_cases hv : v.Nodup
    · by_cases hp : pruned oracles (k+1) ctx = true
      · exact pruned_sound hv hctx hp
      · have hs : stepTest k t v
            (fun w => search oracles k (t-1) w (update oracles true v w ctx))
            (fun w => search oracles k t w (update oracles false v w ctx)) = false := by
          simpa only [search,if_pos hv,if_neg hp] using hc
        apply exclude_step hv ?_ ?_ hs
        · intro w hw
          exact ih (t-1) w _ (update_valid hctx true w) hw
        · intro w hw
          exact ih t w _ (update_valid hctx false w) hw
    · simp [search,hv] at hc

def leafCheck {n : Nat} (oracles : Fin n → Oracle) (k t : Nat) (v : List Sig)
    (programs : Fin n → List PEqualNP.CircuitLowerBounds.Gate × List Nat) : Bool :=
  !(search oracles k t v (initial oracles v programs))

lemma leafCheck_sound {n : Nat} (oracles : Fin n → Oracle)
    {k t : Nat} {v : List Sig}
    {programs : Fin n → List PEqualNP.CircuitLowerBounds.Gate × List Nat}
    (hc : leafCheck oracles k t v programs = true) : Impossible k t v := by
  apply search_sound oracles k t v (initial oracles v programs)
    (initial_valid oracles v programs)
  unfold leafCheck at hc
  cases hs : search oracles k t v (initial oracles v programs) with
  | false => rfl
  | true => simp only [hs, Bool.not_true, Bool.false_eq_true] at hc

end PEqualNP.Outside.L_meta_670_aux.DynamicLeaf
