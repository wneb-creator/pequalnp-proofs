namespace PEqualNP.Outside.L_meta_670_aux.DynamicPrepared

open LiveCheck DynamicLeaf PEqualNP.CircuitLowerBounds

inductive Route (v : List Sig) (a : Sig) where
  | cached (index : Nat) (correct : v[index]? = some a)
  | direct

def route (v : List Sig) (a : Sig) : Route v a :=
  let i := v.idxOf a
  if h : v[i]? = some a then .cached i h else .direct

def Route.value {v : List Sig} {a : Sig} (p : Sig → Base1007.Sig)
    (ps : List Base1007.Sig) : Route v a → Base1007.Sig
  | .cached i _ => ps.getD i Base1007.zero
  | .direct => p a

lemma Route.value_map {v : List Sig} {a : Sig} (p : Sig → Base1007.Sig)
    (r : Route v a) : r.value p (v.map p) = p a := by
  cases r with
  | cached i h => simp [Route.value,List.getD_eq_getElem?_getD,List.getElem?_map,h]
  | direct => rfl

def Route.root {v : List Sig} {a : Sig} (roots : List Nat) : Route v a → Nat
  | .cached i _ => roots.getD i 8
  | .direct => 8

inductive Expression (v : List Sig) (z : Sig) where
  | leaf (r : Route v z)
  | unary (a : Sig) (r : Route v a) (correct : neg a = z)
  | binary (d : Bool) (a b : Sig) (ra : Route v a) (rb : Route v b)
      (correct : bin d a b = z)

def expression (v : List Sig) (z : Sig) : Option Recipe → Expression v z
  | none => .leaf (route v z)
  | some (.unary a) =>
      if h : neg a = z then .unary a (route v a) h else .leaf (route v z)
  | some (.binary d a b) =>
      if h : bin d a b = z then .binary d a b (route v a) (route v b) h
      else .leaf (route v z)

def Expression.value {v : List Sig} {z : Sig} (o : Oracle)
    (ps : List Base1007.Sig) : Expression v z → Base1007.Sig
  | .leaf r => r.value o.project ps
  | .unary _ r _ => Base1007.neg (r.value o.project ps)
  | .binary d _ _ ra rb _ => Base1007.bin d (ra.value o.project ps) (rb.value o.project ps)

lemma Expression.value_map {v : List Sig} {z : Sig} (o : Oracle)
    (e : Expression v z) : e.value o (v.map o.project) = o.project z := by
  cases e with
  | leaf r => exact r.value_map _
  | unary a r h => simp only [Expression.value,Route.value_map,← o.mapNeg,h]
  | binary d a b ra rb h => simp only [Expression.value,Route.value_map,← o.mapBin,h]

def Expression.gate {v : List Sig} {z : Sig} (roots : List Nat) : Expression v z → Gate
  | .leaf _ => ⟨.or,[]⟩
  | .unary _ r _ => ⟨.not,[r.root roots]⟩
  | .binary d _ _ ra rb _ => ⟨if d then .or else .and,[ra.root roots,rb.root roots]⟩

inductive Selection (v : List Sig) (z a : Sig) where
  | fresh (correct : a = z)
  | old (r : Route v a)

def selection (v : List Sig) (z a : Sig) : Selection v z a :=
  if h : a = z then .fresh h else .old (route v a)

def Selection.value {v : List Sig} {z a : Sig} (p : Sig → Base1007.Sig)
    (ps : List Base1007.Sig) (q : Base1007.Sig) : Selection v z a → Base1007.Sig
  | .fresh _ => q
  | .old r => r.value p ps

lemma Selection.value_map {v : List Sig} {z a : Sig} (p : Sig → Base1007.Sig)
    (s : Selection v z a) : s.value p (v.map p) (p z) = p a := by
  cases s with
  | fresh h => simp [Selection.value,h]
  | old r => exact r.value_map _

def Selection.root {v : List Sig} {z a : Sig} (roots : List Nat) (out : Nat) :
    Selection v z a → Nat
  | .fresh _ => out
  | .old r => r.root roots

inductive Selections (v : List Sig) (z : Sig) : List Sig → Type
  | nil : Selections v z []
  | cons {a : Sig} {w : List Sig} (head : Selection v z a)
      (tail : Selections v z w) : Selections v z (a :: w)

def selections (v : List Sig) (z : Sig) : (w : List Sig) → Selections v z w
  | [] => .nil
  | a :: w => .cons (selection v z a) (selections v z w)

def Selections.values {v : List Sig} {z : Sig} (p : Sig → Base1007.Sig)
    (ps : List Base1007.Sig) (q : Base1007.Sig) :
    {w : List Sig} → Selections v z w → List Base1007.Sig
  | [], .nil => []
  | _ :: _, .cons a as => a.value p ps q :: as.values p ps q

lemma Selections.values_map {v : List Sig} {z : Sig} {w : List Sig}
    (p : Sig → Base1007.Sig) (s : Selections v z w) :
    s.values p (v.map p) (p z) = w.map p := by
  induction s with
  | nil => rfl
  | cons a as ih => simp only [Selections.values,Selection.value_map,List.map_cons,ih]

def Selections.roots {v : List Sig} {z : Sig} (roots : List Nat) (out : Nat) :
    {w : List Sig} → Selections v z w → List Nat
  | [], .nil => []
  | _ :: _, .cons a as => a.root roots out :: as.roots roots out

structure Plan (v w : List Sig) where
  value : Expression v (w.headD zero)
  routes : Selections v (w.headD zero) w

def plan (v w : List Sig) (r : Option Recipe) : Plan v w :=
  ⟨expression v (w.headD zero) r,selections v (w.headD zero) w⟩

def forceRoute {α : Type} {v : List Sig} {a : Sig} (r : Route v a)
    (f : Route v a → α) : α :=
  match r with
  | .direct => f .direct
  | .cached 0 h => f (.cached 0 h)
  | .cached (i+1) h => f (.cached (i+1) h)

lemma forceRoute_eq {α : Type} {v : List Sig} {a : Sig} (r : Route v a)
    (f : Route v a → α) : forceRoute r f = f r := by
  cases r with
  | direct => rfl
  | cached i h => cases i <;> rfl

def forceExpression {α : Type} {v : List Sig} {z : Sig}
    (e : Expression v z) (f : Expression v z → α) : α :=
  match e with
  | .leaf r => forceRoute r fun s => f (.leaf s)
  | .unary a r h => forceRoute r fun s => f (.unary a s h)
  | .binary d a b ra rb h =>
      forceRoute ra fun sa => forceRoute rb fun sb => f (.binary d a b sa sb h)

lemma forceExpression_eq {α : Type} {v : List Sig} {z : Sig}
    (e : Expression v z) (f : Expression v z → α) : forceExpression e f = f e := by
  cases e <;> simp only [forceExpression,forceRoute_eq]

def forceSelection {α : Type} {v : List Sig} {z a : Sig}
    (s : Selection v z a) (f : Selection v z a → α) : α :=
  match s with
  | .fresh h => f (.fresh h)
  | .old r => forceRoute r fun q => f (.old q)

lemma forceSelection_eq {α : Type} {v : List Sig} {z a : Sig}
    (s : Selection v z a) (f : Selection v z a → α) : forceSelection s f = f s := by
  cases s <;> simp only [forceSelection,forceRoute_eq]

def forceSelections {α : Type} {v : List Sig} {z : Sig} :
    {w : List Sig} → (s : Selections v z w) → (Selections v z w → α) → α
  | [], .nil, f => f .nil
  | _ :: _, .cons a as, f =>
      forceSelection a fun b => forceSelections as fun bs => f (.cons b bs)

lemma forceSelections_eq {α : Type} {v : List Sig} {z : Sig} {w : List Sig}
    (s : Selections v z w) (f : Selections v z w → α) : forceSelections s f = f s := by
  induction s with
  | nil => rfl
  | cons a as ih => simp only [forceSelections,forceSelection_eq,ih]

def forcePlan {α : Type} {v w : List Sig} (p : Plan v w) (f : Plan v w → α) : α :=
  forceExpression p.value fun e => forceSelections p.routes fun rs => f ⟨e,rs⟩

lemma forcePlan_eq {α : Type} {v w : List Sig} (p : Plan v w) (f : Plan v w → α) :
    forcePlan p f = f p := by
  simp only [forcePlan,forceExpression_eq,forceSelections_eq]

def updateOne {v w : List Sig} (o : Oracle) (p : Plan v w) (c : PrefixCtx) : PrefixCtx :=
  let q := p.value.value o c.vals
  let old := c.vals.idxOf q
  let cached := old < c.vals.length
  let free := o.inputs.contains q
  let fresh := !(free || cached)
  let out := if free then o.inputs.idxOf q
    else if cached then c.roots.getD old 8 else 10+c.gates.length
  compact ⟨if fresh then c.gates ++ [p.value.gate c.roots] else c.gates,
    p.routes.roots c.roots out,
    p.routes.values o.project c.vals q⟩

lemma updateOne_valid {v w : List Sig} (o : Oracle) (p : Plan v w) (c : PrefixCtx)
    (hc : c.vals = v.map o.project) :
    (updateOne o p c).vals = w.map o.project := by
  simp only [updateOne,compact,hc,Expression.value_map]
  exact p.routes.values_map _

def updatePrepared {n : Nat} (oracles : Fin n → Oracle) (v w : List Sig)
    (ctx : Context n) (r : Option Recipe) : Context n :=
  forcePlan (plan v w r) fun p => fun i => updateOne (oracles i) p (ctx i)

lemma updatePrepared_valid {n : Nat} {oracles : Fin n → Oracle} {v : List Sig}
    {ctx : Context n} (h : Valid oracles v ctx) (w : List Sig) (r : Option Recipe) :
    Valid oracles w (updatePrepared oracles v w ctx r) := by
  simp only [updatePrepared,forcePlan_eq]
  intro i
  exact updateOne_valid _ _ _ (h i)

end PEqualNP.Outside.L_meta_670_aux.DynamicPrepared
