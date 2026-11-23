namespace PEqualNP.Outside.L_meta_670_aux.DynamicIndexed

open LiveCheck DynamicLeaf PEqualNP.CircuitLowerBounds

structure Route where
  wire : Sig
  index : Nat
  cached : Bool

def route (v : List Sig) (a : Sig) : Route :=
  let i := v.idxOf a
  ⟨a,i,v[i]? == some a⟩

def Route.value (p : Sig → Base1007.Sig) (ps : List Base1007.Sig) (r : Route) : Base1007.Sig :=
  if r.cached then ps.getD r.index Base1007.zero else p r.wire

lemma route_value (p : Sig → Base1007.Sig) (v : List Sig) (a : Sig) :
    (route v a).value p (v.map p) = p a := by
  change (if v[v.idxOf a]? == some a then
    (v.map p).getD (v.idxOf a) Base1007.zero else p a) = p a
  by_cases h : (v[v.idxOf a]? == some a) = true
  · rw [if_pos h]
    have hh : v[v.idxOf a]? = some a := beq_iff_eq.mp h
    simp only [List.getD_eq_getElem?_getD,List.getElem?_map,hh,Option.map_some,Option.getD_some]
  · rw [if_neg h]

def Route.root (roots : List Nat) (r : Route) : Nat :=
  if r.cached then roots.getD r.index 8 else 8

inductive Expression where
  | leaf (r : Route)
  | unary (r : Route)
  | binary (isOr : Bool) (a b : Route)

def expression (v : List Sig) (z : Sig) : Option Recipe → Expression
  | none => .leaf (route v z)
  | some (.unary a) =>
      if neg a == z then .unary (route v a) else .leaf (route v z)
  | some (.binary d a b) =>
      if bin d a b == z then .binary d (route v a) (route v b) else .leaf (route v z)

def Expression.value (o : Oracle) (ps : List Base1007.Sig) : Expression → Base1007.Sig
  | .leaf r => r.value o.project ps
  | .unary r => Base1007.neg (r.value o.project ps)
  | .binary d a b => Base1007.bin d (a.value o.project ps) (b.value o.project ps)

lemma expression_value (o : Oracle) (v : List Sig) (z : Sig) (r : Option Recipe) :
    (expression v z r).value o (v.map o.project) = o.project z := by
  cases r with
  | none => exact route_value _ _ _
  | some r =>
    cases r with
    | unary a =>
      simp only [expression]
      split
      · rename_i h
        simp only [Expression.value,route_value,← o.mapNeg,beq_iff_eq.mp h]
      · exact route_value _ _ _
    | binary d a b =>
      simp only [expression]
      split
      · rename_i h
        simp only [Expression.value,route_value,← o.mapBin,beq_iff_eq.mp h]
      · exact route_value _ _ _

def Expression.gate (roots : List Nat) : Expression → Gate
  | .leaf _ => ⟨.or,[]⟩
  | .unary r => ⟨.not,[r.root roots]⟩
  | .binary d a b => ⟨if d then .or else .and,[a.root roots,b.root roots]⟩

inductive Selection where
  | fresh
  | old (r : Route)

def selection (v : List Sig) (z a : Sig) : Selection :=
  if a == z then .fresh else .old (route v a)

def Selection.value (p : Sig → Base1007.Sig) (ps : List Base1007.Sig)
    (q : Base1007.Sig) : Selection → Base1007.Sig
  | .fresh => q
  | .old r => r.value p ps

lemma selection_value (p : Sig → Base1007.Sig) (v : List Sig) (z a : Sig) :
    (selection v z a).value p (v.map p) (p z) = p a := by
  simp only [selection]
  split
  · rename_i h
    simp only [Selection.value,beq_iff_eq.mp h]
  · exact route_value _ _ _

def Selection.root (roots : List Nat) (out : Nat) : Selection → Nat
  | .fresh => out
  | .old r => r.root roots

structure Plan where
  value : Expression
  routes : List Selection

def plan (v w : List Sig) (r : Option Recipe) : Plan :=
  ⟨expression v (w.headD zero) r,w.map (selection v (w.headD zero))⟩

def forceNumber {α : Type} (n : Nat) (f : Nat → α) : α :=
  match n with
  | 0 => f 0
  | i+1 => f (i+1)

lemma forceNumber_eq {α : Type} (n : Nat) (f : Nat → α) : forceNumber n f = f n := by
  cases n <;> rfl

def forceRoute {α : Type} (r : Route) (f : Route → α) : α :=
  match r with
  | ⟨a,i,c⟩ => forceNumber i fun j =>
      match c with
      | true => f ⟨a,j,true⟩
      | false => f ⟨a,j,false⟩

lemma forceRoute_eq {α : Type} (r : Route) (f : Route → α) : forceRoute r f = f r := by
  rcases r with ⟨a,i,c⟩
  simp only [forceRoute,forceNumber_eq]
  cases c <;> rfl

def forceExpression {α : Type} (e : Expression) (f : Expression → α) : α :=
  match e with
  | .leaf r => forceRoute r fun s => f (.leaf s)
  | .unary r => forceRoute r fun s => f (.unary s)
  | .binary d a b => forceRoute a fun x => forceRoute b fun y => f (.binary d x y)

lemma forceExpression_eq {α : Type} (e : Expression) (f : Expression → α) :
    forceExpression e f = f e := by
  cases e <;> simp only [forceExpression,forceRoute_eq]

def forceSelection {α : Type} (s : Selection) (f : Selection → α) : α :=
  match s with
  | .fresh => f .fresh
  | .old r => forceRoute r fun q => f (.old q)

lemma forceSelection_eq {α : Type} (s : Selection) (f : Selection → α) :
    forceSelection s f = f s := by
  cases s <;> simp only [forceSelection,forceRoute_eq]

def forceSelections {α : Type} : List Selection → (List Selection → α) → α
  | [],f => f []
  | a :: as,f => forceSelection a fun b => forceSelections as fun bs => f (b :: bs)

lemma forceSelections_eq {α : Type} (s : List Selection) (f : List Selection → α) :
    forceSelections s f = f s := by
  induction s generalizing f with
  | nil => rfl
  | cons a as ih => simp only [forceSelections,forceSelection_eq,ih]

def forcePlan {α : Type} (p : Plan) (f : Plan → α) : α :=
  match p with
  | ⟨e,rs⟩ => forceExpression e fun e' => forceSelections rs fun rs' => f ⟨e',rs'⟩

lemma forcePlan_eq {α : Type} (p : Plan) (f : Plan → α) : forcePlan p f = f p := by
  cases p
  simp only [forcePlan,forceExpression_eq,forceSelections_eq]

def updateOne (o : Oracle) (p : Plan) : PrefixCtx → PrefixCtx
  | ⟨gs,rs,ps⟩ =>
      let q := p.value.value o ps
      let old := ps.idxOf q
      let cached := old < ps.length
      let free := o.inputs.contains q
      let fresh := !(free || cached)
      let out := if free then o.inputs.idxOf q
        else if cached then rs.getD old 8 else 10+gs.length
      compact ⟨if fresh then gs ++ [p.value.gate rs] else gs,
        p.routes.map (Selection.root rs out),
        p.routes.map (Selection.value o.project ps q)⟩

lemma updateOne_valid (o : Oracle) (v w : List Sig) (r : Option Recipe) (c : PrefixCtx)
    (hc : c.vals = v.map o.project) :
    (updateOne o (plan v w r) c).vals = w.map o.project := by
  rcases c with ⟨gs,rs,ps⟩
  simp only [PrefixCtx.vals] at hc
  simp only [updateOne,compact,plan,hc,expression_value,List.map_map]
  apply List.map_congr_left
  intro a ha
  exact selection_value _ _ _ _

def updateIndexed {n : Nat} (oracles : Fin n → Oracle) (v w : List Sig)
    (ctx : Context n) (r : Option Recipe) : Context n :=
  forcePlan (plan v w r) fun p => fun i => updateOne (oracles i) p (ctx i)

lemma updateIndexed_valid {n : Nat} {oracles : Fin n → Oracle} {v : List Sig}
    {ctx : Context n} (h : Valid oracles v ctx) (w : List Sig) (r : Option Recipe) :
    Valid oracles w (updateIndexed oracles v w ctx r) := by
  simp only [updateIndexed,forcePlan_eq]
  intro i
  exact updateOne_valid _ _ _ _ _ (h i)

end PEqualNP.Outside.L_meta_670_aux.DynamicIndexed
