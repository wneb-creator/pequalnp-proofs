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

namespace PEqualNP.Outside.L_meta_670_aux.AutoContext

open PEqualNP.CircuitLowerBounds
open LiveCheck

structure Build where
  gates : List Gate
  values : List Base1007.Sig

def emit (g : Gate) (a : Base1007.Sig) (b : Build) : Nat × Build :=
  if b.values.contains a then (b.values.idxOf a,b)
  else (b.values.length,⟨b.gates ++ [g],b.values ++ [a]⟩)

def unary (i : Nat) (b : Build) : Nat × Build :=
  emit ⟨.not,[i]⟩ (Base1007.neg (b.values.getD i Base1007.zero)) b

def binary (d : Bool) (i j : Nat) (b : Build) : Nat × Build :=
  emit ⟨if d then .or else .and,[i,j]⟩
    (Base1007.bin d (b.values.getD i Base1007.zero)
      (b.values.getD j Base1007.zero)) b

def step (rho : Fin 9 → Nat) (op : Nat) (stack : List Nat) (b : Build) :
    List Nat × Build :=
  if op ≤ 9 then (rho (Fin.ofNat 9 (op-1)) :: stack,b)
  else match stack with
  | [] => ([],b)
  | i :: tail =>
    if op = 10 then let q := unary i b; (q.1 :: tail,q.2)
    else match tail with
    | [] => ([],b)
    | j :: rest => let q := binary (decide (op = 12)) i j b; (q.1 :: rest,q.2)

def run (rho : Fin 9 → Nat) : Nat → Nat → List Nat → Build → List Nat × Build
  | 0, _, stack, b => (stack,b)
  | fuel+1, code, stack, b =>
    if code = 0 then (stack,b)
    else let q := step rho (code &&& 15) stack b
      run rho fuel (code >>> 4) q.1 q.2

def oneGate (a : Base1007.Sig) (b : Build) : Option Gate :=
  let ids := List.range b.values.length
  match ids.find? (fun i => Base1007.neg (b.values.getD i Base1007.zero) == a) with
  | some i => some ⟨.not,[i]⟩
  | none => ids.findSome? fun i => ids.findSome? fun j =>
    if i < j then
      let x := b.values.getD i Base1007.zero
      let y := b.values.getD j Base1007.zero
      if Base1007.bin false x y == a then some ⟨.and,[i,j]⟩
      else if Base1007.bin true x y == a then some ⟨.or,[i,j]⟩ else none
    else none

def add (rho : Fin 9 → Nat) (hint : Sig → Nat)
    (a : Sig × Base1007.Sig) (b : Build) : Build :=
  if b.values.contains a.2 then b
  else match oneGate a.2 b with
  | some g => (emit g a.2 b).2
  | none => (run rho 31 (hint a.1) [] b).2

def insert (hint : Sig → Nat) (a : Sig × Base1007.Sig) :
    List (Sig × Base1007.Sig) → List (Sig × Base1007.Sig)
  | [] => [a]
  | b :: rest => if hint a.1 ≤ hint b.1 then a :: b :: rest
    else b :: insert hint a rest

def order (hint : Sig → Nat) : List (Sig × Base1007.Sig) → List (Sig × Base1007.Sig)
  | [] => []
  | a :: rest => insert hint a (order hint rest)

def compile (inputs : List Base1007.Sig) (rho : Fin 9 → Nat) (hint : Sig → Nat)
    (v : List Sig) (ps : List Base1007.Sig) (reverse : Bool) : List Gate × List Nat :=
  let pairs := order hint (v.zip ps)
  let ordered := if reverse then pairs.reverse else pairs
  let b := ordered.foldl (fun b a => add rho hint a b) ⟨[],inputs⟩
  let c := DynamicLeaf.compact ⟨b.gates,ps.map b.values.idxOf,ps⟩
  (c.gates,c.roots)

def programs (inputs : List Base1007.Sig) (rho : Fin 9 → Nat) (hint : Sig → Nat)
    (v : List Sig) (ps : List Base1007.Sig) : List Gate × List Nat :=
  let first := compile inputs rho hint v ps false
  if first.1.length ≤ 2 then first
  else let second := compile inputs rho hint v ps true
    if second.1.length < first.1.length then second else first

end PEqualNP.Outside.L_meta_670_aux.AutoContext

namespace PEqualNP.Outside.L_meta_670_aux.AutoContext

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma sample_shared :
    (programs (Base1007.raw ++ [Base1007.zero,Base1007.one]) (fun i => i.val)
      (fun a => if a == LiveCheck.bin false (LiveCheck.raw.getD 0 LiveCheck.zero)
        (LiveCheck.raw.getD 1 LiveCheck.zero) then 0xb21 else 0xc3b21)
      [LiveCheck.bin false (LiveCheck.raw.getD 0 LiveCheck.zero)
          (LiveCheck.raw.getD 1 LiveCheck.zero),
        LiveCheck.bin true (LiveCheck.raw.getD 2 LiveCheck.zero)
          (LiveCheck.bin false (LiveCheck.raw.getD 0 LiveCheck.zero)
            (LiveCheck.raw.getD 1 LiveCheck.zero))]
      [Base1007.bin false (Base1007.raw.getD 0 Base1007.zero)
          (Base1007.raw.getD 1 Base1007.zero),
        Base1007.bin true (Base1007.raw.getD 2 Base1007.zero)
          (Base1007.bin false (Base1007.raw.getD 0 Base1007.zero)
            (Base1007.raw.getD 1 Base1007.zero))]).1.length = 2 := by
  decide +kernel

end PEqualNP.Outside.L_meta_670_aux.AutoContext
