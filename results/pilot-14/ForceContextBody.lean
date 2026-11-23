namespace PEqualNP.Outside.L_meta_670_aux.ForceContext

open PEqualNP.CircuitLowerBounds DynamicLeaf

def nat {α : Type} (n : Nat) (f : Nat → α) : α :=
  match n with
  | 0 => f 0
  | k+1 => f (k+1)

lemma nat_eq {α : Type} (n : Nat) (f : Nat → α) : nat n f = f n := by
  cases n <;> rfl

def list {α β : Type} (force : α → (α → β) → β) :
    List α → (List α → β) → β
  | [], f => f []
  | a :: xs, f => force a fun b => list force xs fun ys => f (b :: ys)

lemma list_eq {α β : Type} (force : α → (α → β) → β)
    (hf : ∀ a f, force a f = f a) (xs : List α) (f : List α → β) :
    list force xs f = f xs := by
  induction xs generalizing f with
  | nil => rfl
  | cons a xs ih => simp only [list,hf,ih]

def op {α : Type} : GateOp → (GateOp → α) → α
  | .and, f => f .and
  | .or, f => f .or
  | .not, f => f .not
  | .mod m, f => nat m fun n => f (.mod n)
  | .maj, f => f .maj

lemma op_eq {α : Type} (o : GateOp) (f : GateOp → α) : op o f = f o := by
  cases o <;> simp only [op,nat_eq]

def gate {α : Type} (g : Gate) (f : Gate → α) : α :=
  op g.op fun o => list nat g.inputs fun xs => f ⟨o,xs⟩

lemma gate_eq {α : Type} (g : Gate) (f : Gate → α) : gate g f = f g := by
  cases g
  simp only [gate,op_eq,list_eq nat nat_eq]

def sig {α : Type} (a : Base1007.Sig) (f : Base1007.Sig → α) : α :=
  nat a.1.toNat fun p => nat a.2.toNat fun n =>
    f (BitVec.ofNat 252 p,BitVec.ofNat 252 n)

lemma sig_eq {α : Type} (a : Base1007.Sig) (f : Base1007.Sig → α) :
    sig a f = f a := by
  simp only [sig,nat_eq,BitVec.ofNat_toNat,BitVec.setWidth_eq]

def record {α : Type} (c : PrefixCtx) (f : PrefixCtx → α) : α :=
  list gate c.gates fun gs => list nat c.roots fun rs =>
    list sig c.vals fun vs => f ⟨gs,rs,vs⟩

lemma record_eq {α : Type} (c : PrefixCtx) (f : PrefixCtx → α) :
    record c f = f c := by
  cases c
  simp only [record,list_eq gate gate_eq,list_eq nat nat_eq,list_eq sig sig_eq]

def materialize {n : Nat} {α : Type} (c : Context n) (f : Context n → α) : α :=
  list record (List.ofFn c) fun cs =>
    f (fun i => cs.getD i.val ⟨[],[],[]⟩)

lemma materialize_eq {n : Nat} {α : Type} (c : Context n) (f : Context n → α) :
    materialize c f = f c := by
  rw [materialize,list_eq record record_eq]
  congr 1
  funext i
  simp [List.getD_eq_getElem?_getD]

end PEqualNP.Outside.L_meta_670_aux.ForceContext
