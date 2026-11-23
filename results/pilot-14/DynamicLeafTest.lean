import DynamicBase
namespace PEqualNP.Outside.L_meta_670_aux.DynamicLeaf

open PEqualNP.CircuitLowerBounds
open LiveCheck ProjectionData

structure PrefixCtx where
  gates : List Gate
  roots : List Nat
  vals : List Base1007.Sig

abbrev Context := Fin 3 → PrefixCtx

def Valid (v : List Sig) (ctx : Context) : Prop :=
  ∀ i, (ctx i).vals = v.map (project i)

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

lemma Recipe.projected_map (i : Fin 3) (v : List Sig) (r : Recipe) :
    r.projected (project i) v (v.map (project i)) = project i r.value := by
  cases r <;> simp only [Recipe.projected, Recipe.value, retrieve_map,
    project_neg, project_bin]

def proposedValue (i : Fin 3) (v : List Sig) (ps : List Base1007.Sig)
    (z : Sig) (r : Option Recipe) : Base1007.Sig :=
  match r with
  | none => retrieve (project i) v ps z
  | some r => if r.value == z then r.projected (project i) v ps
    else retrieve (project i) v ps z

lemma proposedValue_map (i : Fin 3) (v : List Sig) (z : Sig) (r : Option Recipe) :
    proposedValue i v (v.map (project i)) z r = project i z := by
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

def updateOne (i : Fin 3) (v w : List Sig) (c : PrefixCtx)
    (r : Option Recipe) : PrefixCtx :=
  let z := w.headD zero
  let q := proposedValue i v c.vals z r
  let old := c.vals.idxOf q
  let cached := c.vals.contains q
  let fresh := !(q == Base1007.zero || q == Base1007.one || cached)
  let g := match r with
    | some a => recipeGate v c a
    | none => ⟨.or,[]⟩
  let out := if q == Base1007.zero then 8 else if q == Base1007.one then 9
    else if cached then c.roots.getD old 8 else 10+c.gates.length
  compact ⟨if fresh then c.gates ++ [g] else c.gates,
    w.map (fun a => if a == z then out else rootOf v c a),
    w.map (fun a => if a == z then q else retrieve (project i) v c.vals a)⟩

def update (unary : Bool) (v w : List Sig) (ctx : Context) : Context :=
  let r := if unary then findUnary v (w.headD zero) else findBinary v (w.headD zero)
  fun i => updateOne i v w (ctx i) r

lemma update_valid {v : List Sig} {ctx : Context} (h : Valid v ctx)
    (u : Bool) (w : List Sig) : Valid w (update u v w ctx) := by
  intro i
  simp only [update, updateOne, compact]
  apply List.map_congr_left
  intro a ha
  rw [h i]
  split
  · rename_i he
    rw [proposedValue_map]
    exact congrArg (project i) (beq_iff_eq.mp he).symm
  · exact retrieve_map _ _ _

def initial (v : List Sig) (programs : Fin 3 → List Gate × List Nat) : Context :=
  fun i => ⟨(programs i).1,(programs i).2,v.map (project i)⟩

lemma initial_valid (v : List Sig) (programs : Fin 3 → List Gate × List Nat) :
    Valid v (initial v programs) := fun _ => rfl

end PEqualNP.Outside.L_meta_670_aux.DynamicLeaf
