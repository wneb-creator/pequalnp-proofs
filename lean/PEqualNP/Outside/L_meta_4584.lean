import Mathlib
import PEqualNP.Defs

-- First gate OR(x0, x4) of a circuit for the Petersen-minus-vertex edge function forces 16 gates.
-- The checker and the plain bound certificates are those of the merged L_meta_1667 family (PR 4332, Apache-2.0);
-- the seeded column variant (varsX, rawMask, strong_low) follows the open submission 7298 for OR(x4, x6).
-- The seeded ladder and the forest named live were produced by an independent search.
namespace PEqualNP.Outside.L_meta_4584
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Bool) (a b : Sig) : Sig := if d then a ||| b else a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
private theorem bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]

def Live (target : Sig) : Nat → Nat → Finset Sig → Prop
  | 0,t,S => t=0 ∧ S={target} ∧ proper target
  | k+1,t,S =>
    (∃ (u : Nat) (U : Finset Sig) (a : Sig), t=u+1 ∧ S=insert a U ∧ proper a ∧
      neg a ∉ insert a U ∧ Live target k u (insert (neg a) U)) ∨
    (∃ (U : Finset Sig) (a b : Sig) (d : Bool), S=insert a (insert b U) ∧ proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live target k t (insert (bin d a b) U))
theorem Live.stop {target : Sig} (hp : proper target) : Live target 0 0 {target} := ⟨rfl,rfl,hp⟩
theorem Live.unary {target : Sig} {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
    (hfresh : neg a ∉ insert a U) (tail : Live target k t (insert (neg a) U)) :
    Live target (k+1) (t+1) (insert a U) :=
  Or.inl ⟨t,U,a,rfl,rfl,ha,hfresh,tail⟩
theorem Live.binary {target : Sig} {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live target k t (insert (bin d a b) U)) :
    Live target (k+1) t (insert a (insert b U)) :=
  Or.inr ⟨U,a,b,d,rfl,ha,hb,hab,hfresh,tail⟩
theorem Live.ind {target : Sig} {motive : ∀ (k t : Nat) (S : Finset Sig), Live target k t S → Prop}
    (stop : ∀ (hp : proper target), motive 0 0 {target} (Live.stop hp))
    (unary : ∀ {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live target k t (insert (neg a) U)),
      motive k t (insert (neg a) U) tail → motive (k+1) (t+1) (insert a U) (Live.unary ha hfresh tail))
    (binary : ∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live target k t (insert (bin d a b) U)),
      motive k t (insert (bin d a b) U) tail →
      motive (k+1) t (insert a (insert b U)) (Live.binary ha hb hab hfresh tail))
    {k t : Nat} {S : Finset Sig} (h : Live target k t S) : motive k t S h := by
  induction k generalizing t S with
  | zero =>
    obtain ⟨rfl,rfl,hp⟩ := h
    exact stop hp
  | succ k ih =>
    rcases h with ⟨u,U,a,rfl,rfl,ha,hf,tail⟩ | ⟨U,a,b,d,rfl,ha,hb,hab,hf,tail⟩
    · exact unary ha hf tail (ih tail)
    · exact binary ha hb hab hf tail (ih tail)

private lemma live_proper {k t S} (h : Live target k t S) : ∀ a ∈ S, proper a := by
  induction h using Live.ind with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {k t S} (h : Live target k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @unary k t U a ha hf _ ih =>
    have hu : neg a ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc := Finset.card_insert_le a U
    exact ⟨by omega,by omega⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    exact ⟨by omega,by omega⟩


def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (bin false) one
  | .or => xs.foldr (bin true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v

private lemma get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (fun h => h.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)

private lemma bin_laws (a : Sig) :
    bin false a one = a ∧ bin true a zero = a ∧
    bin false a zero = zero ∧ bin true a one = one ∧
    bin false a a = a ∧ bin true a a = a := by
  simp only [bin,one,zero,Bool.false_eq_true,ite_false,ite_true,BitVec.and_allOnes,BitVec.or_zero,BitVec.and_zero,BitVec.or_allOnes,BitVec.and_self,BitVec.or_self,and_self] <;> simp

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (w : List Sig) (z : Sig) : Prop :=
  (∃ a ∈ w, proper a ∧ z = neg a) ∨
  (∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)

private lemma bin_rep {w a b} (d : Bool) (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ witness w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a0,az,ao,aa,aa'⟩ := bin_laws a
  obtain ⟨b1,b0,bz,bo,bb,bb'⟩ := bin_laws b
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · rw [bin_comm]; cases d <;> simp_all
  · rw [bin_comm]; cases d <;> simp_all
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he : a=b
  · subst b; cases d <;> simp_all
  exact Or.inr (Or.inr ⟨d,a,b,ham,hbm,hap,hbp,he,rfl⟩)

private lemma gate_rep (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2) :
    represented w (gv w g) ∨ witness w (gv w g) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  have nx (a : Sig) (ha : represented w a) : represented w (neg a) ∨ witness w (neg a) := by
    rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
    · exact Or.inl (neg_laws.1 ▸ ro)
    · exact Or.inl (neg_laws.2 ▸ rz)
    · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)
  cases l with
  | nil =>
    rcases ho with rfl | rfl | rfl
    · exact Or.inl ro
    · exact Or.inl rz
    · exact nx _ rz
  | cons i l =>
    cases l with
    | nil =>
      rcases ho with rfl | rfl | rfl
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · exact nx _ (get_rep w i)
    | cons j l =>
      cases l with
      | cons a l => simp at hl
      | nil =>
        rcases ho with rfl | rfl | rfl
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using bin_rep false (get_rep w i) (get_rep w j)
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using bin_rep true (get_rep w i) (get_rep w j)
        · exact nx _ (get_rep w i)

-- Remove a last computed signal from a backward derivation. A gate whose value
-- is already available, or is unused by the suffix, needs no entry in the plan.
private lemma pull_gate {w : List Sig} {z : Sig} {k t S} (h : Live target k t S)
    (hz : represented w z ∨ witness w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' t' S', k' ≤ k+1 ∧ Live target k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | (⟨a,ha,hp',eq⟩ | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (neg a)
        have ht : Live target k t (insert (neg a) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : neg a ∉ insert a U := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.unary hp' hf ht,by simpa using And.intro ha hu⟩
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live target k t (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extract (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (hp : proper target) (hout : target ∈ execute gs w) :
    ∃ k t S, k ≤ gs.length ∧ Live target k t S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0,0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,t,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,u,T,hl,hu,hT⟩ := pull_gate ht (gate_rep w g (legal g (by simp))) hs
    exact ⟨l,u,T,by simp; omega,hu,hT⟩

def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [bit,bin]

private lemma b_read (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl

private lemma run_bit (i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _
    | cons a l ih =>
      change bit i (bin false _ _) = (_ && _)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (bin true _ _) = (_ || _)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _

private lemma execute_bits (gs : List Gate) (i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit i g w (hg g (by simp))]




abbrev Wire (R : Type) := R → Bool

def inv {R} (a : Wire R) : Wire R := fun r => !(a r)

def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r

def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0

noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum

def Available {R} (pool : List (Wire R)) (v : Wire R) : Prop := v ∈ pool ∨ Constant v

def supply {R} (pool xs : List (Wire R)) := ∀ a ∈ xs, Available pool a

def Reach {R} (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | 0,b => b=roots
  | p+1,c => (∃ bank a, Reach roots p bank ∧ Available bank a ∧ c=inv a :: bank) ∨
    (∃ (op : Bool) (bank : List (Wire R)) (a b : Wire R), Reach roots p bank ∧ Available bank a ∧
      Available bank b ∧ c=combine op a b :: bank)
theorem Reach.start {R} {roots : List (Wire R)} : Reach roots 0 roots := rfl
theorem Reach.one {R} {roots : List (Wire R)} {p bank a} (h : Reach roots p bank)
    (ha : Available bank a) : Reach roots (p+1) (inv a :: bank) := Or.inl ⟨bank,a,h,ha,rfl⟩
theorem Reach.two {R} {roots : List (Wire R)} {p bank a b} (op : Bool) (h : Reach roots p bank)
    (ha : Available bank a) (hb : Available bank b) : Reach roots (p+1) (combine op a b :: bank) :=
  Or.inr ⟨op,bank,a,b,h,ha,hb,rfl⟩
theorem Reach.ind {R} {roots : List (Wire R)} {motive : ∀ p bank, Reach roots p bank → Prop}
    (start : motive 0 roots Reach.start)
    (one : ∀ {p bank a} (h : Reach roots p bank) (ha : Available bank a), motive p bank h →
      motive (p+1) (inv a :: bank) (Reach.one h ha))
    (two : ∀ {p bank a b} (op : Bool) (h : Reach roots p bank) (ha : Available bank a)
      (hb : Available bank b), motive p bank h →
      motive (p+1) (combine op a b :: bank) (Reach.two op h ha hb))
    {p bank} (h : Reach roots p bank) : motive p bank h := by
  induction p generalizing bank with
  | zero =>
    obtain rfl := h
    exact start
  | succ p ih =>
    rcases h with ⟨bank,a,h,ha,rfl⟩ | ⟨op,bank,a,b,h,ha,hb,rfl⟩
    · exact one h ha (ih h)
    · exact two op h ha hb (ih h)

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

def Run {R} (goal : Wire R) : Nat → List (Wire R) → Prop
  | 0,zs => List.Perm [goal] zs
  | s+1,zs => (∃ (save : Bool) (a : Wire R) (rest : List (Wire R)), (a::rest).Perm zs ∧
      Run goal s (inv a :: kept save a rest)) ∨
    (∃ (op ka kb : Bool) (a b : Wire R) (rest : List (Wire R)), (a::b::rest).Perm zs ∧
      Run goal s (combine op a b :: kept ka a (kept kb b rest)))
theorem Run.stop {R} {goal : Wire R} : Run goal 0 [goal] := List.Perm.refl _
theorem Run.perm {R} {goal : Wire R} {s : Nat} {xs zs : List (Wire R)} (p : xs.Perm zs)
    (h : Run goal s xs) : Run goal s zs := by
  cases s with
  | zero => exact List.Perm.trans h p
  | succ s =>
    rcases h with ⟨save,a,rest,q,h⟩ | ⟨op,ka,kb,a,b,rest,q,h⟩
    · exact Or.inl ⟨save,a,rest,q.trans p,h⟩
    · exact Or.inr ⟨op,ka,kb,a,b,rest,q.trans p,h⟩
theorem Run.one {R} {goal : Wire R} {s : Nat} {a : Wire R} {rest : List (Wire R)} (save : Bool)
    (h : Run goal s (inv a :: kept save a rest)) : Run goal (s+1) (a::rest) :=
  Or.inl ⟨save,a,rest,List.Perm.refl _,h⟩
theorem Run.two {R} {goal : Wire R} {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op ka kb : Bool)
    (h : Run goal s (combine op a b :: kept ka a (kept kb b rest))) : Run goal (s+1) (a::b::rest) :=
  Or.inr ⟨op,ka,kb,a,b,rest,List.Perm.refl _,h⟩
theorem Run.ind {R} {goal : Wire R} {motive : ∀ s ws, Run goal s ws → Prop}
    (stop : motive 0 [goal] Run.stop)
    (perm : ∀ {s xs zs} (p : List.Perm xs zs) (h : Run goal s xs), motive s xs h → motive s zs (Run.perm p h))
    (one : ∀ {s a rest} (save : Bool) (h : Run goal s (inv a :: kept save a rest)),
      motive s _ h → motive (s+1) (a::rest) (Run.one save h))
    (two : ∀ {s a b rest} (op ka kb : Bool) (h : Run goal s (combine op a b :: kept ka a (kept kb b rest))),
      motive s _ h → motive (s+1) (a::b::rest) (Run.two op ka kb h))
    {s ws} (h : Run goal s ws) : motive s ws h := by
  induction s generalizing ws with
  | zero => exact perm h Run.stop stop
  | succ s ih =>
    rcases h with ⟨save,a,rest,p,h⟩ | ⟨op,ka,kb,a,b,rest,p,h⟩
    · exact perm p (Run.one save h) (one save h (ih h))
    · exact perm p (Run.two op ka kb h) (two op ka kb h (ih h))

theorem mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a + mass xs := by
  simp [mass]

theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept,mass_cons]

theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩

theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩

theorem from_constant {R} (op) {a b : Wire R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available bank a) (hb : Available bank b) :
    Available bank (combine op a b) := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false, by funext x; simp [combine]⟩
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr ⟨true, by funext x; simp [combine]⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false, by funext x; simp [combine]⟩
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr ⟨true, by funext x; simp [combine]⟩

theorem available_cons {R} {bank v} (w : Wire R) (h : Available bank v) :
    Available (w::bank) v := by
  exact h.elim (fun h => Or.inl (List.mem_cons_of_mem _ h)) Or.inr

theorem extend_one {R} (roots : List (Wire R)) {p bank a} (hp : Reach roots p bank)
    (ha : Available bank a) :
    ∃ q next, Reach roots q next ∧ Available next (inv a) ∧
        (∀ v, Available bank v → Available next v) ∧ q+cost a ≤ p+1+cost (inv a) := by
  classical
  by_cases c : Constant a
  · exact ⟨p,bank,hp,Or.inr (inv_constant c),fun _ h => h,by simp [cost,c,inv_constant c]⟩
  · exact ⟨p+1,_,Reach.one hp ha,Or.inl (by simp),fun _ h => available_cons _ h,by simp [cost,c]⟩

theorem extend_two {R} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach roots p bank)
    (ha : Available bank a) (hb : Available bank b) :
    ∃ q next, Reach roots q next ∧ Available next (combine op a b) ∧
        (∀ v, Available bank v → Available next v) ∧
        q+cost a+cost b ≤ p+1+cost (combine op a b) := by
  classical
  by_cases c : Constant a ∨ Constant b
  · refine ⟨p,bank,hp,from_constant op c ha hb,fun _ h => h,?_⟩
    by_cases ca : Constant a <;> by_cases cb : Constant b
    · simp [cost,ca,cb,both_constant op ca cb]
    · simp [cost,ca,cb]
    · simp [cost,ca,cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬Constant a := fun h => c (Or.inl h)
    have cb : ¬Constant b := fun h => c (Or.inr h)
    exact ⟨p+1,_,Reach.two op hp ha hb,Or.inl (by simp),fun _ h => available_cons _ h,
      by simp [cost,ca,cb]⟩

theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]

theorem contraction {R} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach roots p bank) (hs : supply bank ws) :
    ∃ q next, Reach roots q next ∧ Available next goal ∧ q+mass ws ≤ p+s := by
  classical
  induction h using Run.ind generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih =>
    have hsub : supply bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @one s a rest save _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_one roots hp (hs a (by simp))
    have ht : supply T (inv a :: kept save a rest) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · exact inc v (hs v (List.mem_cons.mpr (mem_kept hh)))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a rest save
    rw [mass_cons] at hl ⊢
    exact ⟨q,W,hW,hv,by omega⟩
  | @two s a b rest op ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_two roots op hp (hs a (by simp)) (hs b (by simp))
    have ht : supply T (combine op a b :: kept ka a (kept kb b rest)) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v
        apply hs
        rcases mem_kept hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept hh))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a (kept kb b rest) ka
    have hlen' := mass_kept b rest kb
    rw [mass_cons] at hl
    refine ⟨q,W,hW,hv,?_⟩
    rw [mass_cons,mass_cons]
    omega

def restrictRows {R S : Type} (rows : S → R) (a : Wire R) : Wire S :=
  fun r => a (rows r)

theorem restrict_kept {R S : Type} (rows : S → R) (k : Bool) (a : Wire R) (ws) :
    (kept k a ws).map (restrictRows rows) =
    kept k (restrictRows rows a) (ws.map (restrictRows rows)) := by
  cases k <;> simp [kept]

theorem restrict_run {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws) :
    Run (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h using Run.ind with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | one save _ ih =>
    simp only [List.map_cons,restrict_kept] at ih ⊢
    exact Run.one save ih
  | two op ka kb _ ih =>
    simp only [List.map_cons,restrict_kept] at ih ⊢
    cases op
    · exact Run.two false ka kb ih
    · exact Run.two true ka kb ih

theorem projected_bound {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach roots p bank) (hs : supply bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach roots q bs → Available bs (restrictRows rows goal) → L ≤ q) :
    L + mass (ws.map (restrictRows rows)) ≤ p+s := by
  obtain ⟨q,bs,hq,ht,hle⟩ := contraction nc (restrict_run rows h) roots hp hs
  have hqle := hl q bs hq ht
  omega


abbrev Row := Fin 512
def observe (a : Sig) : Wire Row := fun r => bit r a
def table (f : Wire Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)

theorem bit_table (f : Wire Row) (r : Row) : bit r (table f) = f r := by
  simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]

theorem table_observe (v : Sig) : table (observe v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact bit_table (observe v) ⟨j,hj⟩

theorem observe_table (f : Wire Row) : observe (table f) = f := by
  funext r
  exact bit_table f r

theorem obs_neg (a : Sig) : observe (neg a) = inv (observe a) := by
  funext r
  exact bit_neg _ _

theorem obs_bin (d : Bool) (a b : Sig) :
    observe (bin d a b) = combine d (observe a) (observe b) := by
  funext r
  cases d <;> exact bit_bin _ _ _ _

theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl

theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]

theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

theorem list_run {T : Sig} {k u S} (h : Live T k u S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run (observe T) k (v.map observe) := by
  classical
  induction h using Live.ind generalizing v with
  | stop hp =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @unary k u U a ha fresh _ ih =>
    let rest := (U.erase a).toList
    let save := decide (a ∈ U)
    let tail := kept save a rest
    have er : rest.toFinset = U.erase a := by simp [rest]
    have hm : a ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have ht : tail.toFinset = U := by
      rw [show tail=kept save a rest by rfl,kept_fin,er]
      by_cases hh : a ∈ U <;> simp [save,hh]
    have nd := kept_nd save a rest hr hm
    have hf : neg a ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz))
    have progress := ih (neg a::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    rw [List.map_cons,map_kept,obs_neg] at progress
    have perm : (a::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (List.nodup_cons.mpr ⟨hm,hr⟩) hv
      simp [er,eqv]
    exact Run.perm (perm.map _) (Run.one save progress)
  | @binary k u U a b d ha hb hab fresh _ ih =>
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := kept kb b rest
    let tail := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm := kept_nd kb b rest hr br
    have am : a ∉ mid := by cases h : kb <;> simp [mid,kept,h,hab,ar]
    have nd := kept_nd ka a mid bm am
    have ht : tail.toFinset = U := by
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kept_fin,kept_fin,er]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j=a <;>
        by_cases bj : j=b <;> simp_all [ka,kb]
    have hf : bin d a b ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress := ih (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    change Run _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,map_kept,map_kept,obs_bin] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d ka kb progress)


theorem table_inv (f : Wire Row) : table (inv f) = neg (table f) := by
  rw [←table_observe (neg (table f)),obs_neg,observe_table]

theorem table_bin (d : Bool) (f g : Wire Row) :
    table (combine d f g) = bin d (table f) (table g) := by
  rw [←table_observe (bin d (table f) (table g)),obs_bin,observe_table,observe_table]

theorem available_rep {bank : List (Wire Row)} {a} (h : Available bank a) :
    represented (bank.map table) (table a) := by
  rcases h with hm | ⟨b,rfl⟩
  · exact Or.inl (List.mem_map_of_mem hm)
  · apply Or.inr
    cases b
    · have z : table (fun _ => false) = zero := by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        exact (bit_table _ ⟨j,hj⟩).trans (bit_zero ⟨j,hj⟩).symm
      exact fun hp => hp.1 z
    · have z : table (fun _ => true) = one := by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        exact (bit_table _ ⟨j,hj⟩).trans (bit_one ⟨j,hj⟩).symm
      exact fun hp => hp.2 z

theorem inv_rep {w a} (ha : represented w a) :
    represented w (neg a) ∨ witness w (neg a) := by
  rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
  · exact Or.inl (Or.inr fun h => h.2 neg_laws.1)
  · exact Or.inl (Or.inr fun h => h.1 neg_laws.2)
  · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)

theorem pull_cons {w : List Sig} {z : Sig} {T k t S} (h : Live T k t S)
    (hz : represented w z ∨ witness w z) (hs : ∀ a ∈ S, a ∈ z::w) :
    ∃ k' t' S', k' ≤ k+1 ∧ Live T k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  apply pull_gate h hz
  intro a hm
  simpa [or_comm] using hs a hm

theorem reach_live_sub {roots : List (Wire Row)} {p bank}
    (h : Reach roots p bank) {T k t S} (run : Live T k t S)
    (sub : ∀ a ∈ S, a ∈ bank.map table) :
    ∃ l v U, l ≤ p+k ∧ Live T l v U ∧ ∀ a ∈ U, a ∈ roots.map table := by
  induction h using Reach.ind generalizing k t S with
  | start => exact ⟨k,t,S,by omega,run,sub⟩
  | @one p bank a h ha ih =>
    rw [List.map_cons,table_inv] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩ := pull_cons run (inv_rep (available_rep ha)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons,table_bin] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩ := pull_cons run (bin_rep d (available_rep ha) (available_rep hb)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩

theorem reach_live {roots : List Sig} {p bank T} (hp : proper T)
    (h : Reach (roots.map observe) p bank) (hit : Available bank (observe T)) :
    ∃ k t S, k ≤ p ∧ Live T k t S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := available_rep hit
  rw [table_observe] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,v,U,hl,hr,hs⟩ := reach_live_sub h (Live.stop hp) (by simpa using mem)
  refine ⟨l,v,U,by omega,hr,?_⟩
  simpa [List.map_map,Function.comp_def,table_observe] using hs

theorem live_row_difference {T k t S} (h : Live T k t S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @unary k t U a hp hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · refine ⟨a,by simp,?_⟩
      exact fun he => hd (by rw [bit_neg,bit_neg,he])
    · exact ⟨v,Finset.mem_insert_of_mem hu,hd⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩

theorem raw_required {T k t S} (h : Live T k t S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def graph : Sig := 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
def seed : Sig := inputs.getD 0 zero ||| inputs.getD 4 zero

def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem seed_table : ∀ r : Row, bit r seed = (sample r 0 || sample r 4) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem seed_nonzero : seed ≠ zero := by decide +kernel
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
theorem sampled (r : Row) : List.ofFn (sample r) = inputs.map (bit r) := by
  rw [←input_list]
  rw [List.map_ofFn]
  rfl

theorem table_eval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates inputs).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sampled]
  rfl

theorem exec_extends (gs : List Gate) (ws : List Sig) : ∃ l, execute gs ws = ws ++ l := by
  induction gs generalizing ws with
  | nil => exact ⟨[],by simp [execute]⟩
  | cons g gs ih =>
    obtain ⟨l,hl⟩ := ih (ws++[gv ws g])
    exact ⟨gv ws g::l,by simpa [execute,List.append_assoc] using hl⟩

def neighbor (i : Fin 9) : Nat := [4,2,1,2,3,0,1,2,3].getD i.val 0
def absentRow (i : Fin 9) : Row := Fin.ofNat 512 (1 <<< neighbor i)
def presentRow (i : Fin 9) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< neighbor i))

theorem initial_live (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (first : ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 4))
    (computes : PEqualNP.MetaComplexity.circuitFun 9 C = edge) (small : C.size ≤ 15) :
    ∃ k t S, k ≤ 14 ∧ Live graph k t S ∧ ∀ a ∈ S, a ∈ inputs++[seed] := by
  have headEq : (execute C.gates inputs).getD 9 zero = seed := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C legal 9 r).trans ((first (sample r)).trans (seed_table r).symm)
  have goalEq : (execute C.gates inputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C legal C.output r).trans ((congrFun computes (sample r)).trans (edge_table r).symm)
  have out := get_rep (execute C.gates inputs) C.output
  rw [goalEq] at out
  have targetIn := out.resolve_right (fun hn => hn graph_proper)
  cases hgs : C.gates with
  | nil =>
    rw [hgs] at headEq
    exact False.elim (seed_nonzero headEq.symm)
  | cons g gs =>
    have eq0 : gv inputs g = seed := by
      rw [hgs] at headEq
      change (execute gs (inputs++[gv inputs g])).getD 9 zero = seed at headEq
      obtain ⟨l,hl⟩ := exec_extends gs (inputs++[gv inputs g])
      rw [hl] at headEq
      exact headEq
    rw [hgs] at targetIn
    change graph ∈ execute gs (inputs++[gv inputs g]) at targetIn
    rw [eq0] at targetIn
    have tailLegal : ∀ gate ∈ gs, gate.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ gate.inputs.length≤2 := by
      intro gate hg
      apply legal
      rw [hgs]
      exact List.mem_cons_of_mem _ hg
    obtain ⟨k,t,S,hk,run,hs⟩ := extract gs _ tailLegal graph_proper targetIn
    have len : gs.length+1 ≤ 15 := by simpa [Circuit.size,hgs] using small
    exact ⟨k,t,S,by omega,run,hs⟩


def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a
theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := bit_table _ _
theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a) = restrictRows f (observe a) := by funext r; exact bit_rename f a r
theorem rename_neg (f : Row → Row) (a : Sig) : rename f (neg a) = neg (rename f a) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change bit ⟨j,hj⟩ (rename f (neg a)) = bit ⟨j,hj⟩ (neg (rename f a))
  rw [bit_rename,bit_neg,bit_neg,bit_rename]
theorem rename_bin (f : Row → Row) (d : Bool) (a b : Sig) :
    rename f (bin d a b) = bin d (rename f a) (rename f b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change bit ⟨j,hj⟩ (rename f (bin d a b)) = bit ⟨j,hj⟩ (bin d (rename f a) (rename f b))
  rw [bit_rename,bit_bin,bit_bin,bit_rename,bit_rename]
theorem rename_inj (f : Row → Row) (onto : Function.Surjective f) :
    Function.Injective (rename f) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨r,hr⟩ := onto ⟨j,hj⟩
  have he := congrArg (bit r) h
  change bit ⟨j,hj⟩ a = bit ⟨j,hj⟩ b
  rw [bit_rename,bit_rename,hr] at he
  exact he
theorem rename_constants (f : Row → Row) : rename f zero = zero ∧ rename f one = one := by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · exact (bit_rename f zero ⟨j,hj⟩).trans ((bit_zero _).trans (bit_zero ⟨j,hj⟩).symm)
  · exact (bit_rename f one ⟨j,hj⟩).trans ((bit_one _).trans (bit_one ⟨j,hj⟩).symm)
theorem live_rename {T k t S} (h : Live T k t S) (f : Row → Row) (onto : Function.Surjective f) :
    Live (rename f T) k t (S.image (rename f)) := by
  have inj := rename_inj f onto
  obtain ⟨fz,fo⟩ := rename_constants f
  have pp (v) (p : proper v) : proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h using Live.ind with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @unary k t U a hp hf _ ih =>
    have fresh : rename f (neg a) ∉ (insert a U).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_neg] at fresh ih ⊢
    exact Live.unary (pp _ hp) fresh ih
  | @binary k t U a b d ha hb hab hf _ ih =>
    have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_bin] at fresh ih ⊢
    exact Live.binary (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih

theorem mono_row_difference {T k t S} (h : Live T k t S) (none : t=0) {r s : Row}
    (pos : bit r T = true) (negRow : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | unary _ _ _ _ => omega
  | @binary k t U a b d ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩ := ih none
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [bit_bin] at hp hn
      cases d <;> cases p : bit r a <;> cases q : bit s a <;>
        cases u : bit r b <;> cases z : bit s b <;> simp_all
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩

def Lower (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach (roots.map observe) p bank → Available bank (observe T) → L ≤ p

def Impossible (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k t, k ≤ cap → ¬Live T k t S

def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v

theorem lower_impossible {roots T L} (hp : proper T)
    (essential : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible T L roots.toFinset) : Lower roots T (L+1) := by
  intro p bank h ha
  obtain ⟨k,t,S,hk,run,hs⟩ := reach_live hp h ha
  have he : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩ := essential _ hm
    exact raw_required run roots a hs r s hd iso
  by_contra! small
  exact noRun k t (by omega) (he.symm ▸ run)

theorem observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v) := by
  rintro ⟨b,h⟩
  have hr : represented ([] : List Sig) v := by
    have avail : Available ([] : List (Wire Row)) (observe v) := Or.inr ⟨b,h⟩
    simpa only [List.map_nil,table_observe] using available_rep avail
  exact (hr.resolve_left (by simp)) hv

theorem mass_append {R} (a b : List (Wire R)) : mass (a++b) = mass a + mass b := by
  simp [mass]
theorem mass_constants {R} (xs : List (Wire R)) (hc : ∀ x ∈ xs, Constant x) :
    mass xs = xs.length := by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [mass_cons,List.length_cons,cost,if_pos ha,ih (fun x hx => hc x (by simp [hx]))]
    omega

theorem lower_slice {roots other : List Sig} {T G : Sig} (pT : proper T) (pG : proper G)
    (r : Row → Row) (eq : rename r T = G)
    (covered : ∀ a ∈ roots, Available (other.map observe) (observe (rename r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (observe (rename r a)))
    (L : Nat) (prior : Lower other G L) : Lower roots T (L + singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k,t,S,hk,run,sub⟩ := reach_live pT hh ha
  have subS : singles ⊆ S := by
    intro a hs
    obtain ⟨i,j,hd,hiso⟩ := necessary a hs
    exact raw_required run roots a sub i j hd hiso
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front,List.nodup_append]
    refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
    intro a ha b hb he
    subst b
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset=S := by ext a; simp [front,Finset.union_sdiff_of_subset subS]
  have run' := list_run run front nd fe
  have gc : restrictRows r (observe T) = observe G := (observe_rename _ _).symm.trans (congrArg observe eq)
  have supp : supply (other.map observe) ((front.map observe).map (restrictRows r)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
    rw [←observe_rename]
    exact covered a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
  have bound := projected_bound r run' (gc ▸ observe_proper pG) Reach.start supp
    (L:=L) (gc ▸ prior)
  have massLo : singles.card ≤ mass ((front.map observe).map (restrictRows r)) := by
    simp only [front,List.map_append,mass_append]
    let xs := (singles.toList.map observe).map (restrictRows r)
    have only : ∀ v ∈ xs, Constant v := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
      rw [←observe_rename]
      exact constant _ (Finset.mem_toList.mp hmem)
    have sz := mass_constants xs only
    simp only [xs,List.length_map,Finset.length_toList] at sz
    change singles.card ≤ mass xs + _
    rw [sz]
    omega
  omega



def childOne (ws : List Sig) (a : Sig) (keep : Bool) : List Sig :=
  neg a :: kept keep a (ws.erase a)
def childTwo (ws : List Sig) (a b : Sig) (d ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]

theorem enum_step {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (oneStep : ∀ a ∈ ws, ∀ keep, neg a ∉ ws → proper (neg a) →
      (childOne ws a keep).length ≤ cap →
      Impossible T (cap-1) (childOne ws a keep).toFinset)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible T cap ws.toFinset := by
  classical
  intro k t hk h
  generalize he : ws.toFinset = S at h
  induction h using Live.ind with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @unary k t U a ha hf tail _ =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have fresh : neg a ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let keep := decide (a ∈ U)
    have er := erase_fin hn a
    have rest : (kept keep a (ws.erase a)).toFinset = U := by
      rw [kept_fin,er,he]
      by_cases hm : a ∈ U <;> simp [keep,hm]
    have nd : (childOne ws a keep).Nodup := by
      have na : a ∉ ws.erase a := hn.not_mem_erase
      have nk := kept_nd keep a (ws.erase a) (hn.erase _) na
      refine List.nodup_cons.mpr ⟨?_,nk⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (rest ▸ List.mem_toFinset.mpr h))
    have eq : (childOne ws a keep).toFinset = insert (neg a) U := by simp [childOne,rest]
    have sc := (live_size tail).2
    have len : (childOne ws a keep).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact oneStep a am keep fresh hz len k t (by omega) (eq.symm ▸ tail)
  | @binary k t U a b d ha hb hab hf tail _ =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest=(ws.erase a).erase b by rfl,erase_fin (hn.erase _) b,
        erase_fin hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kept_fin,kept_fin,er,he]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j=a <;>
        by_cases jb : j=b <;> simp_all [ka,kb]
    have rn : rest.Nodup := (hn.erase _).erase _
    have ar : a ∉ rest := fun h => (hn.not_mem_erase) (List.mem_of_mem_erase h)
    have br : b ∉ rest := (hn.erase a).not_mem_erase
    have nk := kept_nd kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept,ar,hab]
    have nd : (childTwo ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨?_,kept_nd ka a _ nk ax⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
    have eq : (childTwo ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b::kept ka a (kept kb b rest)).toFinset = _
      simp [ke]
    have sc := (live_size tail).2
    have len : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d ka kb hab fresh hz len k t (by omega) (eq.symm ▸ tail)

def Sep (T : Sig) (width : Nat) (pos negRow : Fin width → Row)
    (asig : Sig → BitVec width × BitVec width) : Prop :=
  (∀ i, bit (pos i) T = true ∧ bit (negRow i) T = false) ∧
  ∀ w i, (asig w).1.getLsbD i.val = bit (pos i) w ∧
    (asig w).2.getLsbD i.val = bit (negRow i) w

def column {n} (oriented : Bool) (s : BitVec n × BitVec n) : BitVec n :=
  if oriented then s.1 &&& ~~~s.2 else s.1 ^^^ s.2

def covered {n} (oriented : Bool) (sig : Sig → BitVec n × BitVec n) : List Sig → BitVec n
  | [] => 0
  | a::ws => column oriented (sig a) ||| covered oriented sig ws

theorem covered_bit {n : Nat} {oriented : Bool} {sig : Sig → BitVec n × BitVec n} {ws : List Sig} {i : Fin n} :
    (covered oriented sig ws).getLsbD i.val = true ↔
    ∃ a ∈ ws, (column oriented (sig a)).getLsbD i.val = true := by
  induction ws with
  | nil => simp [covered]
  | cons a ws ih =>
    simp only [covered,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]

theorem cover_sound {T k t S} (h : Live T k t S) {ws : List Sig} (he : ws.toFinset=S)
    {width : Nat} {r s : Fin width → Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented=true → t=0) :
    covered oriented sig ws = BitVec.allOnes width := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin width := ⟨j,hj⟩
  have yes := (correct.1 i).1
  have no := (correct.1 i).2
  rw [BitVec.getLsbD_allOnes]; simp only [hj,decide_true]
  apply (covered_bit (i:=i)).mpr
  cases oriented with
  | false =>
    obtain ⟨a,ha,hd⟩ := live_row_difference h (show bit (r i) T ≠ bit (s i) T by simp [yes,no])
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,Bool.false_eq_true,ite_false,BitVec.getLsbD_xor,(correct.2 a i).1,(correct.2 a i).2]
    cases hx : bit (r i) a <;> cases hy : bit (s i) a <;> simp_all
  | true =>
    obtain ⟨a,ha,hp,hn⟩ := mono_row_difference h (zeroNot rfl) yes no
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,
      Bool.true_and,(correct.2 a i).1,(correct.2 a i).2,hp,hn,Bool.not_false,Bool.and_self]

theorem cover_required {T cap ws k t} (h : Live T k t (List.toFinset ws))
    (hk : k ≤ cap) (hn : ws.Nodup) {n : Nat} {r s : Fin n → Row} {sig}
    (correct : Sep T n r s sig) :
    covered (decide (ws.length=cap+1)) sig ws = BitVec.allOnes n := by
  apply cover_sound h rfl correct
  intro hh
  have eq := of_decide_eq_true hh
  have bound := (live_size h).2
  rw [List.toFinset_card_of_nodup hn] at bound
  omega



def Slice (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, Available (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank, Reach (roots.map observe) p bank → Available bank (restrictRows f (observe T)) → L ≤ p

def masked (d a : Sig) := a &&& d
def availableB (d : Sig) (pool : List Sig) (a : Sig) :=
  let m := masked d a
  m == zero || m == d || (pool.map (masked d)).any (fun v => v==m)

theorem masked_eq {f : Row → Row} {d a b : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = masked d b) :
    restrictRows f (observe a) = restrictRows f (observe b) := by
  funext r
  have h := congrArg (bit (f r)) eq
  change bit (f r) a = bit (f r) b
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using h

theorem masked_zero {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = zero) : restrictRows f (observe a) = fun _ => false := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = false
  rw [bit_zero] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

theorem masked_one {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = d) : restrictRows f (observe a) = fun _ => true := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = true
  rw [dom r] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

def poolSupply (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) :=
  ∀ a ∈ pool, Available bank (restrictRows f (observe a))

theorem availableB_sound {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bit (f r) d = true) (supplyB : poolSupply f bank pool)
    (check : availableB d pool a = true) : Available bank (restrictRows f (observe a)) := by
  simp only [availableB,List.any_map,Function.comp_def,Bool.or_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with (hz | ho) | ⟨v,hv,he⟩
  · exact Or.inr ⟨false,masked_zero dom hz⟩
  · exact Or.inr ⟨true,masked_one dom ho⟩
  · exact masked_eq dom he ▸ supplyB v hv

abbrev Choice := Nat × Sig × Sig
def choiceVal (c : Choice) :=
  if c.1=2 then neg c.2.1 else bin (c.1==1) c.2.1 c.2.2
def choiceOK (d : Sig) (pool : List Sig) (c : Choice) :=
  availableB d pool c.2.1 && (c.1==2 || availableB d pool c.2.2)

theorem pay_choice {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r, bit (f r) d = true) (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (c : Choice) (valid : choiceOK d pool c = true) :
    ∃ next, Reach roots (q+1) next ∧ poolSupply f next (choiceVal c :: pool) := by
  have ok : availableB d pool c.2.1 = true ∧ (c.1==2 || availableB d pool c.2.2) = true := by simpa only [choiceOK,Bool.and_eq_true] using valid
  have ha := availableB_sound dom hs ok.1
  let z := restrictRows f (observe (choiceVal c))
  have hz : Reach roots (q+1) (z::bank) := by
    by_cases unary : c.1=2
    · change Reach _ _ (restrictRows f (observe (choiceVal c)) :: _)
      rw [choiceVal,if_pos unary,obs_neg]
      exact Reach.one hp ha
    · have hb : availableB d pool c.2.2 = true := by simpa [unary] using ok.2
      have hz' := Reach.two (c.1==1) hp ha (availableB_sound dom hs hb)
      change Reach _ _ (restrictRows f (observe (choiceVal c)) :: _)
      rw [choiceVal,if_neg unary,obs_bin]
      have comm (b : Bool) (v w : Wire Row) : restrictRows f (combine b v w) = combine b (restrictRows f v) (restrictRows f w) := by cases b <;> rfl
      rw [comm]
      exact hz'
  refine ⟨_,hz,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · exact Or.inl (by simp [z])
  · exact available_cons _ (hs _ hm)

def makePool (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c::cs => if choiceOK d pool c then makePool d (choiceVal c::pool) cs else none

theorem makePool_sound {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    {roots bank q pool} (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (cs : List Choice) {result} (ok : makePool d pool cs = some result) :
    ∃ next, Reach roots (q+cs.length) next ∧ poolSupply f next result := by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨_,hp,hs⟩
  | cons c cs ih =>
    simp only [makePool] at ok
    split at ok
    next h =>
      obtain ⟨next,hr,sh⟩ := pay_choice dom hp hs c h
      obtain ⟨out,hr',sh'⟩ := ih hr sh ok
      exact ⟨out,by simpa [Nat.add_assoc,Nat.add_comm 1] using hr',sh'⟩
    next => contradiction

def isMaskedConstant (d a : Sig) := masked d a == zero || masked d a == d
theorem count_constants {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    (ws : List Sig) : ws.countP (isMaskedConstant d) ≤ mass ((ws.map observe).map (restrictRows f)) := by
  classical
  induction ws with
  | nil => simp [mass]
  | cons a ws ih =>
    simp only [List.countP_cons,List.map_cons,mass_cons]
    cases h : isMaskedConstant d a
    · simpa using (Nat.le_add_left _ _ |> ih.trans)
    · have hc : Constant (restrictRows f (observe a)) := by
        have hh : masked d a = zero ∨ masked d a = d := by simpa only [isMaskedConstant,Bool.or_eq_true,beq_iff_eq] using h
        rcases hh with hz | ho
        · exact ⟨false,masked_zero dom hz⟩
        · exact ⟨true,masked_one dom ho⟩
      simpa [cost,hc,Nat.add_comm] using Nat.succ_le_succ ih

def poolCut (d : Sig) (L k p : Nat) (pool ws : List Sig) :=
  decide (k+p < L+ws.countP (isMaskedConstant d)) && ws.all (availableB d pool)

theorem poolCut_sound {raw T d L} (slice : Slice raw T d L) (cs : List Choice)
    {pool ws cap} (built : makePool d raw cs = some pool)
    (nd : ws.Nodup) (cut : poolCut d L cap cs.length pool ws = true) :
    Impossible T cap ws.toFinset := by
  intro k t hk h
  obtain ⟨f,roots,dom,base,nc,lo⟩ := slice
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) base cs built
  simp only [poolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩ := cut
  have coveredS : supply bank ((ws.map observe).map (restrictRows f)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
    exact availableB_sound dom hs (List.all_eq_true.mp all a ha)
  have b := projected_bound f (list_run h ws nd rfl) nc hr coveredS lo
  have massLo := count_constants dom ws
  have hu := ineq
  simp only [Nat.zero_add] at b
  omega



abbrev Move := Sig × Sig × Row
def shifted (d r : Row) : Row :=
  if h : r.val < 512-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(512-d.val),by omega⟩
def backwards (d : Row) : Row := Fin.ofNat 512 (512-d.val)
def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)

theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (shifted d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 512-d.val <;> simp [shifted,h,r.isLt]

theorem bool_mux (p x y : Bool) : (p && x || !p && y) = (if p then x else y) := by cases p <;> simp

theorem bit_mux (r : Row) (m a b : Sig) :
    bit r (mux m a b) = if bit r m then bit r a else bit r b := by
  simp only [bit,mux,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,r.isLt,
    decide_true,Bool.true_and]
  exact bool_mux _ _ _

theorem bit_move (r : Row) (m : Move) (a : Sig) : bit r (wordMove m a) = bit (rowMove m r) a := by
  simp only [wordMove,bit_mux,bit_shift,rowMove]
  cases bit r m.1 <;> cases bit r m.2.1 <;> rfl

def movedRow (ms : List Move) (r : Row) := ms.foldl (fun j m => rowMove m j) r
def movedWord (ms : List Move) (a : Sig) := ms.foldr wordMove a
theorem bit_moved (ms : List Move) (a : Sig) (r : Row) :
    bit r (movedWord ms a) = bit (movedRow ms r) a := by
  induction ms generalizing r with
  | nil => rfl
  | cons m ms ih => exact (bit_move r m _).trans (ih _)
theorem moved_eq_rename (ms : List Move) (a : Sig) : movedWord ms a = rename (movedRow ms) a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact (bit_moved ms a ⟨j,hj⟩).trans (bit_rename _ _ ⟨j,hj⟩).symm

def freeWord (roots : List Sig) (w : Sig) := w==zero || w==one || roots.contains w
theorem freeWord_ok {roots w} (ok : freeWord roots w = true) :
    Available (roots.map observe) (observe w) := by
  simp only [freeWord,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr ⟨false,funext bit_zero⟩
  · exact Or.inr ⟨true,funext bit_one⟩
  · exact Or.inl (List.mem_map_of_mem hm)

def checkMap (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T == G && raw.all (fun a => freeWord base (movedWord ms a))

theorem map_correct {ms raw T base G} (ok : checkMap ms raw T base G = true) :
    rename (movedRow ms) T = G ∧
    ∀ a ∈ raw, Available (base.map observe) (observe (rename (movedRow ms) a)) := by
  simp only [checkMap,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,moved_eq_rename] at ok
  exact ⟨ok.1,fun a ha => freeWord_ok (ok.2 a ha)⟩

theorem lower_map {ms raw T base G L} (ok : checkMap ms raw T base G = true)
    (pT : proper T) (pG : proper G) (hL : Lower base G L) : Lower raw T L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  simpa using lower_slice pT pG (movedRow ms) eq supp ∅ (by simp) (by simp) L hL

theorem slice_correct {ms raw T base G L d} (ok : checkMap ms raw T base G = true)
    (all : movedWord ms d = one) (properG : proper G) (hL : Lower base G L) :
    Slice raw T d L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  have obs : restrictRows (movedRow ms) (observe T) = observe G :=
    (observe_rename _ _).symm.trans (congrArg observe eq)
  refine ⟨movedRow ms,base,?_,?_,?_,?_⟩
  · intro r
    rw [←bit_moved,all,bit_one]
  · intro a ha
    rw [←observe_rename]
    exact supp a ha
  · rw [obs]
    exact observe_proper properG
  · rw [obs]
    exact hL

def witnessB (T : Sig) (roots : List Sig) (a : Sig) (rs : Row × Row) :=
  (bit rs.1 T != bit rs.2 T) &&
  roots.all (fun w => w == a || bit rs.1 w == bit rs.2 w)
theorem witnessB_sound {T roots a rs} (ok : witnessB T roots a rs = true) : Essential T roots a := by
  simp only [witnessB,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
  exact ⟨rs.1,rs.2,ok.1,fun w hw hne => (ok.2 w hw).resolve_left hne⟩

def checkEssential (T : Sig) (raw : List Sig) (xs : List (Sig × Row × Row)) :=
  xs.all (fun a => witnessB T raw a.1 a.2)
theorem essential_ok {T raw xs} (ok : checkEssential T raw xs = true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset, Essential T raw a := by
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact witnessB_sound (List.all_eq_true.mp ok _ hm)

theorem lower_count {raw T} (properT : proper T) (xs : List (Sig × Row × Row))
    (ok : checkEssential T raw xs = true) :
    Lower raw T ((xs.map Prod.fst).toFinset.card-1) := by
  intro p bank hr hit
  obtain ⟨k,t,S,hk,run,sub⟩ := reach_live properT hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩ := essential_ok ok a ha
    exact raw_required run raw a sub r s hd iso
  have bound := (live_size run).2
  omega

def checkLift (ms : List Move) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) :=
  checkMap ms raw T base G && checkEssential T raw xs &&
    xs.all (fun a => movedWord ms a.1 == zero || movedWord ms a.1 == one)

theorem lift_ok {ms T raw base G xs L} (ok : checkLift ms T raw base G xs = true)
    (properT : proper T) (properG : proper G) (low : Lower base G L) :
    Lower raw T (L+(xs.map Prod.fst).toFinset.card) := by
  simp only [checkLift,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩ := map_correct ok.1.1
  apply lower_slice properT properG _ eq supp _ (essential_ok ok.1.2) _ L low
  intro a ha
  obtain ⟨⟨v,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  have hh := List.all_eq_true.mp ok.2 _ hm
  simp only [Bool.or_eq_true,beq_iff_eq,moved_eq_rename] at hh
  rcases hh with h | h
  · rw [h]
    exact ⟨false,funext bit_zero⟩
  · rw [h]
    exact ⟨true,funext bit_one⟩



def selected (m : Nat) : List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat) := (selected m).map Prod.snd
def varsX (m : Nat) : List Sig := if m.testBit 9 then vars m ++ [seed] else vars m
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero
def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
def cube0 : Nat → Nat
  | 0 => 0xff
  | 1 => 0x55
  | 2 => 0x33
  | 3 => 0x11
  | 4 => 0xf
  | 5 => 0x5
  | 6 => 0x3
  | _ => 0x1
def cube3 : Nat → Nat
  | 0 => 0x101010101010101
  | 1 => 0x1000100010001
  | 2 => 0x10100000101
  | 3 => 0x100000001
  | 4 => 0x1010101
  | 5 => 0x10001
  | 6 => 0x101
  | _ => 0x1
def cube6 : Nat → Nat
  | 0 => 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
  | 1 => 0x1000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001
  | 2 => 0x100000000000000010000000000000000000000000000000000000000000000010000000000000001
  | 3 => 0x10000000000000000000000000000000000000000000000000000000000000001
  | 4 => 0x1000000000000000100000000000000010000000000000001
  | 5 => 0x100000000000000000000000000000001
  | 6 => 0x10000000000000001
  | _ => 0x1
def subcube (z o : Nat) : Sig :=
  let fixed := z ||| o
  if z &&& o != 0 then zero else
    BitVec.ofNat 512 ((cube0 (fixed &&& 7)*cube3 ((fixed >>> 3) &&& 7)*cube6 ((fixed >>> 6) &&& 7)) <<< o)
def fixRows (z o : Nat) : List Move :=
  (List.range 9).filterMap fun j =>
    let x := inputs.getD j zero
    let step := Fin.ofNat 512 (1 <<< j)
    if z.testBit j then some (zero,x,step)
    else if o.testBit j then some (~~~x,zero,step) else none
def swapRows (v : Nat) : Move :=
  let i := v &&& 15
  let j := v >>> 4
  let a := inputs.getD i zero
  let b := inputs.getD j zero
  let d := (1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 512 d)

def supportPairs (mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) => (a,0,Fin.ofNat 512 (1 <<< i))

def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r := 1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def properB (T : Sig) := T != zero && T != one
theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
def assertSize (m hints L : Nat) :=
  let xs := graphPairs m hints
  properB (graphGoal m) && checkEssential (graphGoal m) (vars m) xs &&
    decide (L ≤ (xs.map Prod.fst).toFinset.card-1)
theorem size_of {m hints L} (h : assertSize m hints L = true) :
    Lower (vars m) (graphGoal m) L := by
  simp only [assertSize,Bool.and_eq_true,decide_eq_true_eq] at h
  intro p bank hr ha
  exact h.2.trans (lower_count (proper_of _ h.1.1) _ h.1.2 p bank hr ha)

abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
def colFree (m z o : Nat) := m ^^^ (m &&& (z ||| o))
def chartGoal (m : Nat) : Sig := graphGoal m
def rawMask (m : Nat) (c : ColumnInfo) : Nat := m ^^^ (m &&& (c.1 &&& 512))
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let raw := rawMask m c
  let free := colFree raw z o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs s
  let count := (xs.map Prod.fst).toFinset.card
  properB G && checkMap ms (varsX raw) (chartGoal m) (varsX free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (varsX free) xs && decide (L ≤ count-1)
     else properB (graphGoal q) &&
       checkLift (fixRows (colFree free q 0) 0) G (varsX free) (varsX q) (graphGoal q) xs &&
       decide (L ≤ prior q+count))

theorem col_sound {m : Nat} (c : ColumnInfo) (prior : Nat → Nat)
    (valid : ∀ q, Lower (varsX q) (graphGoal q) (prior q))
    (ok : colCheck m c prior = true) : Slice (varsX (rawMask m c)) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  revert ok
  obtain ⟨z,o,q,s,L⟩ := c
  intro ok
  let ms := fixRows z o
  let raw := rawMask m (z,o,q,s,L)
  let free := colFree raw z o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs s
  change (((properB G && checkMap ms (varsX raw) (chartGoal m) (varsX free) G) &&
    (movedWord ms (subcube z o)==one)) && _) = true at ok
  simp only [Bool.and_eq_true,beq_iff_eq] at ok
  apply slice_correct ok.1.1.2 ok.1.2 (proper_of _ ok.1.1.1)
  intro p bank hr ha
  have hh := ok.2
  by_cases hq : q=0
  · simp only [colCheck,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lower_count (proper_of _ ok.1.1.1) xs hh.1 p bank hr ha)
  · simp only [colCheck,hq,if_false,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lift_ok hh.1.2 (proper_of _ ok.1.1.1) (proper_of _ hh.1.1) (valid q) p bank hr ha)

def relabelOK (old rep : Nat) (swaps : List Nat) :=
  properB (graphGoal old) && properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (varsX old) (graphGoal old) (varsX rep) (graphGoal rep)
theorem relabel_of {old rep L swaps} (ok : relabelOK old rep swaps = true)
    (h : Lower (varsX rep) (graphGoal rep) L) : Lower (varsX old) (graphGoal old) L := by
  simp only [relabelOK,Bool.and_eq_true] at ok
  exact lower_map ok.2 (proper_of _ ok.1.1) (proper_of _ ok.1.2) h

def boundsBefore (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1 == q)).map Prod.snd).getD 0
theorem before_sound (entries : List (Nat × Nat))
    (sound : ∀ e ∈ entries, Lower (varsX e.1) (graphGoal e.1) e.2) (q : Nat) :
    Lower (varsX q) (graphGoal q) (boundsBefore entries q) := by
  unfold boundsBefore
  cases h : entries.find? (fun a => a.1 == q) with
  | none => exact fun _ _ _ _ => Nat.zero_le _
  | some e =>
    have he := List.mem_of_find?_eq_some h
    have hit : (fun a : Nat × Nat => a.1 == q) e = true := List.find?_some (p:=fun a : Nat × Nat => a.1 == q) (a:=e) h
    have eq : e.1=q := beq_iff_eq.mp hit
    simpa only [Option.map_some,Option.getD_some,eq] using sound e he


abbrev BoundPool := Sig × Nat × Nat × List Sig
def BoundPool.domain (c : BoundPool) : Sig := c.1
def BoundPool.bound (c : BoundPool) : Nat := c.2.1
def BoundPool.paid (c : BoundPool) : Nat := c.2.2.1
def BoundPool.wires (c : BoundPool) : List Sig := c.2.2.2

def ValidPool (raw : List Sig) (T : Sig) (c : BoundPool) :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r, bit (f r) c.domain = true) ∧ ¬Constant (restrictRows f (observe T)) ∧
    (∀ q ws, Reach (roots.map observe) q ws → Available ws (restrictRows f (observe T)) → c.bound ≤ q) ∧
    Reach (roots.map observe) c.paid bank ∧ poolSupply f bank c.wires ∧ True

theorem build_valid {raw T d lb} (h : Slice raw T d lb) (cs : List Choice) {ws}
    (build : makePool d raw cs = some ws) : ValidPool raw T ⟨d,lb,cs.length,ws⟩ := by
  obtain ⟨f,roots,dom,sup,nc,prior⟩ := h
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa [BoundPool.paid] using hr,hs,trivial⟩

theorem valid_exclude {raw T c} (valid : ValidPool raw T c) (k : Nat) (rest : List Sig)
    (choice : Choice) (paid : Bool)
    (known : ∀ a ∈ rest, availableB c.domain c.wires a = true)
    (buy : if paid then choiceOK c.domain c.wires choice = true
       else availableB c.domain c.wires (choiceVal choice) = true)
    (bound : k+c.paid+paid.toNat <
      c.bound+(choiceVal choice :: rest).countP (isMaskedConstant c.domain))
    (nd : (choiceVal choice :: rest).Nodup) :
    Impossible T k (choiceVal choice :: rest).toFinset := by
  intro t num ht run
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩ := valid
  let ws := choiceVal choice::rest
  have done (n : Nat) (out : List (Wire Row)) (reach : Reach (roots.map observe) n out)
      (zs : poolSupply f out (choiceVal choice::rest)) (le : n = c.paid+paid.toNat) : False := by
    have covered : supply out ((ws.map observe).map (restrictRows f)) := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
      exact zs _ ha
    have b := projected_bound f (list_run run ws nd rfl) nc reach covered lo
    have cm := count_constants dom ws
    change k+c.paid+paid.toNat < c.bound+ws.countP (isMaskedConstant c.domain) at bound
    omega
  cases paid with
  | false =>
    apply done _ _ hp _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact availableB_sound dom hs buy
    · exact availableB_sound dom hs (known _ hm)
  | true =>
    obtain ⟨out,hr,hc⟩ := pay_choice dom hp hs choice buy
    apply done _ _ hr _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact hc _ (by simp)
    · have avail := availableB_sound dom hs (known _ hm)
      rcases avail with mem | con
      · have ha : availableB c.domain c.wires a = true := known _ hm
        have point : ∀ u ∈ c.wires, Available out (restrictRows f (observe u)) :=
          fun u hu => hc u (List.mem_cons_of_mem _ hu)
        exact availableB_sound dom point ha
      · exact Or.inr con

def scalarPoolCut (c : BoundPool) (k : Nat) (rest : List Sig) (op : Choice) :=
  let z := choiceVal op
  let extra := !(availableB c.domain c.wires z)
  ((k+c.paid+extra.toNat < c.bound+(z::rest).countP (isMaskedConstant c.domain)) &&
    rest.all (availableB c.domain c.wires)) && (!extra || choiceOK c.domain c.wires op)

theorem scalarPoolCut_sound {raw T c} (valid : ValidPool raw T c) {k rest op}
    (nd : (choiceVal op::rest).Nodup) (cut : scalarPoolCut c k rest op = true) :
    Impossible T k (choiceVal op::rest).toFinset := by
  let extra := !(availableB c.domain c.wires (choiceVal op))
  apply valid_exclude valid k rest op extra _ _ _ nd
  · simp only [scalarPoolCut,Bool.and_eq_true,List.all_eq_true] at cut
    exact cut.1.2
  · simp only [scalarPoolCut,Bool.and_eq_true,Bool.or_eq_true] at cut
    cases he : availableB c.domain c.wires (choiceVal op) <;> simp_all [extra]
  · simp only [scalarPoolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
    exact cut.1.1

def materialize (raw : List Sig) (cs : List Choice) (d : Sig) (lb : Nat) : Option BoundPool :=
  (makePool d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
theorem materialize_sound {raw T d L cs c} (slice : Slice raw T d L)
    (h : materialize raw cs d L = some c) : ValidPool raw T c := by
  unfold materialize at h
  cases he : makePool d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he,Option.map_some,Option.some.injEq] at h
    subst c
    exact build_valid slice cs he


abbrev Bits := BitVec 768
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 768 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 768 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 768 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 768 → Row) (x : Decor) := x.2 = pairSig r s x.1
def dneg (x : Decor) : Decor := (neg x.1,~~~x.2.1,~~~x.2.2)
def dbin (d : Bool) (x y : Decor) : Decor :=
  if d then (bin d x.1 y.1,x.2.1 ||| y.2.1,x.2.2 ||| y.2.2)
  else (bin d x.1 y.1,x.2.1 &&& y.2.1,x.2.2 &&& y.2.2)

theorem ofRows_neg (r : Fin 768 → Row) (a : Sig) : ofRows r (neg a) = ~~~ofRows r a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (neg a) ⟨j,hj⟩
  rw [bit_neg,←ofRows_bit r a ⟨j,hj⟩] at h
  simpa only [BitVec.getLsbD_not,hj,decide_true,Bool.true_and] using h
theorem ofRows_bin (r : Fin 768 → Row) (d : Bool) (a b : Sig) :
    ofRows r (bin d a b) = if d then ofRows r a ||| ofRows r b else ofRows r a &&& ofRows r b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (bin d a b) ⟨j,hj⟩
  rw [bit_bin,←ofRows_bit r a ⟨j,hj⟩,←ofRows_bit r b ⟨j,hj⟩] at h
  cases d <;> simpa only [Bool.false_eq_true,ite_false,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_or] using h
theorem faithful_neg {r s x} (h : faithful r s x) : faithful r s (dneg x) := by
  change x.2 = _ at h
  simp only [faithful,dneg,pairSig,ofRows_neg, h]
theorem faithful_bin {r s x y} (d) (hx : faithful r s x) (hy : faithful r s y) :
    faithful r s (dbin d x y) := by
  change x.2 = _ at hx
  change y.2 = _ at hy
  cases d <;> simp only [faithful,dbin,Bool.false_eq_true,ite_false,ite_true,pairSig,ofRows_bin,hx,hy]

def codeDecor (op : Nat) (x y : Decor) := if op=2 then dneg x else dbin (op==1) x y
def defaultDecor : Decor := (zero,0,0)
theorem faithful_default (r s) : faithful r s defaultDecor := by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · change (0 : Bits).getLsbD j = (ofRows r zero).getLsbD j
    rw [show (ofRows r zero).getLsbD j = bit (r ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
  · change (0 : Bits).getLsbD j = (ofRows s zero).getLsbD j
    rw [show (ofRows s zero).getLsbD j = bit (s ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
theorem faithful_get {r s ws} (all : ∀ v ∈ ws, faithful r s v) (i : Nat) :
    faithful r s (List.getD ws i defaultDecor) := by
  simp only [List.getD_eq_getElem?_getD]
  cases e : ws[i]? with
  | none => exact faithful_default _ _
  | some v => exact all _ (List.mem_of_getElem? e)
def decodeBank (n : Nat) (bits : Nat) (ws : List Decor) : List Decor :=
  match n with
  | 0 => ws
  | k+1 =>
    let a := ws.getD (bits &&& 15) defaultDecor
    let b := ws.getD ((bits >>> 4) &&& 15) defaultDecor
    decodeBank k (bits >>> 10) (ws++[codeDecor ((bits >>> 8) &&& 3) a b])
theorem decode_faithful (n bits) (ws) (r s) (base : ∀ v ∈ ws, faithful r s v) :
    ∀ v ∈ decodeBank n bits ws, faithful r s v := by
  induction n generalizing ws bits with
  | zero => exact base
  | succ n ih =>
    apply ih
    intro v hv
    rcases List.mem_append.mp hv with hw | hz
    · exact base _ hw
    · obtain rfl := List.mem_singleton.mp hz
      unfold codeDecor
      split
      · exact faithful_neg (faithful_get base _)
      · exact faithful_bin _ (faithful_get base _) (faithful_get base _)

def asRow (cols : Nat → Bits) (i : Fin 768) : Row :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 9 => (cols j.val).getLsbD i.val))).toFin.cast
    (by simp [List.length_ofFn])
theorem coordinate0 : ∀ r : Row, bit r (inputs.getD 0 zero) = r.val.testBit 0 := by decide +kernel
theorem coordinate1 : ∀ r : Row, bit r (inputs.getD 1 zero) = r.val.testBit 1 := by decide +kernel
theorem coordinate2 : ∀ r : Row, bit r (inputs.getD 2 zero) = r.val.testBit 2 := by decide +kernel
theorem coordinate3 : ∀ r : Row, bit r (inputs.getD 3 zero) = r.val.testBit 3 := by decide +kernel
theorem coordinate4 : ∀ r : Row, bit r (inputs.getD 4 zero) = r.val.testBit 4 := by decide +kernel
theorem coordinate5 : ∀ r : Row, bit r (inputs.getD 5 zero) = r.val.testBit 5 := by decide +kernel
theorem coordinate6 : ∀ r : Row, bit r (inputs.getD 6 zero) = r.val.testBit 6 := by decide +kernel
theorem coordinate7 : ∀ r : Row, bit r (inputs.getD 7 zero) = r.val.testBit 7 := by decide +kernel
theorem coordinate8 : ∀ r : Row, bit r (inputs.getD 8 zero) = r.val.testBit 8 := by decide +kernel
theorem input_coords : ∀ (j : Fin 9) (r : Row),
    bit r (inputs.getD j.val zero) = r.val.testBit j.val := by
  intro j r
  fin_cases j
  · exact coordinate0 r
  · exact coordinate1 r
  · exact coordinate2 r
  · exact coordinate3 r
  · exact coordinate4 r
  · exact coordinate5 r
  · exact coordinate6 r
  · exact coordinate7 r
  · exact coordinate8 r
theorem asRow_bit (cols : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow cols i) (inputs.getD j.val zero) = (cols j.val).getLsbD i.val := by
  rw [input_coords]
  change (BitVec.ofBoolListLE (List.ofFn (fun h : Fin 9 => (cols h.val).getLsbD i.val))).getLsbD j.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]
def rawDecor (m : Nat) (p q : Nat → Bits) : List Decor :=
  (selected m).map (fun (j,a) => (a,p j,q j))
theorem selected_entry {m j a} (h : (j,a) ∈ selected m) :
    j<9 ∧ a=inputs.getD j zero := by
  obtain ⟨v,hv,hh⟩ := List.mem_filterMap.mp h
  simp only [List.mem_range] at hv
  split at hh
  next =>
    cases hh
    exact ⟨hv,rfl⟩
  next => contradiction
theorem raw_faithful (m) (p q : Nat → Bits) :
    ∀ a ∈ rawDecor m p q, faithful (asRow p) (asRow q) a := by
  intro a ha
  obtain ⟨⟨j,v⟩,hv,rfl⟩ := List.mem_map.mp ha
  obtain ⟨hj,rfl⟩ := selected_entry hv
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · exact (asRow_bit p ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm
  · exact (asRow_bit q ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm

def liftGoal (m : Nat) (v : Nat → Bits) : Bits :=
  let x := fun j => if m.testBit j then v j else 0
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  simp only [bit,graphGoal,liftGoal,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide),pos 8 (by decide)]
abbrev Cov := Bits × Bits × Bits

def addCov (z : Bits) (c : Cov) : Cov :=
  (z ||| c.1, (z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))

def coverage (d : Bool) (v : List Decor) : Cov :=
  v.foldr (fun a c => addCov (column d a.2) c) (0,0,0)

def takeOne (c : Cov) (a : Bits) : Bits := c.1 &&& ~~~(c.2.1 &&& a)
def takeTwo (c : Cov) (a b : Bits) : Bits :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))

private theorem cov_one (c : Cov) (a : Bits) : takeOne (addCov a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeOne,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl

private theorem cov_two (c : Cov) (a b : Bits) : takeTwo (addCov a (addCov b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem add_swap (c : Cov) (a b : Bits) : addCov a (addCov b c)=addCov b (addCov a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addCov,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem cov_perm (d : Bool) {l r : List Decor} (h : l.Perm r) : coverage d l=coverage d r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (column d a.2)) ih
  | swap a b t => exact add_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2



theorem cov_word (d : Bool) (v : List Decor) {r s} (good : ∀ a ∈ v, faithful r s a) :
    (coverage d v).1 = covered d (pairSig r s) (v.map Prod.fst) := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    change (column d a.2 ||| (coverage d v).1) = column d (pairSig r s a.1) ||| _
    rw [show a.2=pairSig r s a.1 from good _ (by simp),ih (fun a ha => good a (by simp [ha]))]

def delOne (ws : List Decor) (a : Decor) (keep : Bool) :=
  if keep then ws else ws.erase a
def delTwo (ws : List Decor) (a b : Decor) (ka kb : Bool) :=
  delOne (delOne ws a ka) b kb

theorem delOne_perm {ws : List Decor} (a : Decor) (ha : a ∈ ws) :
    ws.Perm (a::ws.erase a) := List.perm_cons_erase ha

theorem cover_one {ws : List Decor} (d : Bool) (a : Decor) (ha : a ∈ ws) (keep : Bool) :
    (coverage d (delOne ws a keep)).1 =
      (if keep then (coverage d ws).1 else takeOne (coverage d ws) (column d a.2)) := by
  cases keep
  · change (coverage d (ws.erase a)).1 = takeOne (coverage d ws) _
    rw [cov_perm d (delOne_perm a ha)]
    exact (cov_one _ _).symm
  · rfl
theorem delTwo_perm {ws : List Decor} (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws) (hne : a≠b) :
    ws.Perm (a::b::(ws.erase a).erase b) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm hne)).mpr hb
  exact (delOne_perm a ha).trans (List.Perm.cons _ (delOne_perm b hm))

theorem cover_two {ws : List Decor} (d : Bool) (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a ≠ b) (ka kb : Bool) :
    (coverage d (delTwo ws a b ka kb)).1 =
      (if ka then (if kb then (coverage d ws).1 else takeOne (coverage d ws) (column d b.2))
       else if kb then takeOne (coverage d ws) (column d a.2)
       else takeTwo (coverage d ws) (column d a.2) (column d b.2)) := by
  cases ka <;> cases kb
  · change (coverage d ((ws.erase a).erase b)).1 = takeTwo (coverage d ws) _ _
    rw [cov_perm d (delTwo_perm a b ha hb ne)]
    exact (cov_two _ _ _).symm
  · exact cover_one d a ha false
  · exact cover_one d b hb false
  · rfl

def sameWords (a b : List Sig) := (a.all (fun x => b.contains x)) && (b.all (fun x => a.contains x))
theorem sameWords_sound {xs ys} (h : sameWords xs ys = true) : xs.toFinset=ys.toFinset := by
  simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
  ext a
  simp only [List.mem_toFinset]
  exact ⟨h.1 a,h.2 a⟩


def keyWord (v : Sig) :=
  let n := v.toNat % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
def keySet (xs : List Sig) := xs.foldl (fun v x => v+keyWord x) 0

def closeChild (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links (keySet ws)).any (sameWords ws) || pools.any (fun p => scalarPoolCut p k rest op)

theorem closeChild_sound {raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild pools links k rest op = true) :
    Impossible T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · exact scalarPoolCut_sound (pValid _ hp) nd ok

abbrev CovPair := Cov × Cov
def preCov (ws : List Decor) : CovPair := (coverage false ws,coverage true ws)
def getCov (c : CovPair) (d : Bool) := if d then c.2 else c.1
theorem get_preCov (ws) (d : Bool) : getCov (preCov ws) d = coverage d ws := by cases d <;> rfl
def restCov (v : Cov) (a b : Bits) (un ka kb : Bool) :=
  if un then (if ka then v.1 else takeOne v a) else
    if ka then (if kb then v.1 else takeOne v b)
    else if kb then takeOne v a else takeTwo v a b
def opKeep (un ka kb : Bool) (a b : Decor) (ws : List Decor) :=
  if un then delOne ws a ka else delTwo ws a b ka kb

theorem rest_coverage {ws : List Decor} {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws)
    (un ka kb d : Bool) (ne : un=false → a≠b) :
    (coverage d (opKeep un ka kb a b ws)).1 =
      restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) un ka kb := by
  rw [get_preCov]
  cases un
  · exact cover_two d a b ha hb (ne rfl) ka kb
  · exact cover_one d a ha ka

theorem delOne_sub (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws := by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
theorem keep_sub (ws : List Decor) (a b : Decor) (un ka kb : Bool) :
    (opKeep un ka kb a b ws).Sublist ws := by
  cases un
  · exact (delOne_sub _ _ _).trans (delOne_sub _ _ _)
  · exact delOne_sub _ _ _
theorem len_keep (ws : List Decor) (a b : Decor) (un ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : un=false → a≠b) :
    (opKeep un ka kb a b ws).length =
      ws.length - (if ka then 0 else 1) - (if un || kb then 0 else 1) := by
  cases un
  · have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm (ne rfl))).mpr hb
    cases ka <;> cases kb <;> simp [opKeep,delTwo,delOne,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]
  · cases ka <;> cases kb <;> simp [opKeep,delOne,List.length_erase_of_mem ha]

def movedDecor (op : Nat) (a b : Decor) := codeDecor op a b
def movedChoice (op : Nat) (a b : Decor) : Choice := (op,a.1,b.1)
theorem moved_full (op) (a b : Decor) :
    (movedDecor op a b).1 = choiceVal (movedChoice op a b) := by
  by_cases h : op=2
  · simp [movedDecor,codeDecor,h,dneg,choiceVal,movedChoice]
  · cases hh : op==1 <;> simp [movedDecor,codeDecor,h,hh,dbin,choiceVal,movedChoice]
theorem moved_faithful {r s a b} (ha : faithful r s a) (hb : faithful r s b) (op : Nat) :
    faithful r s (movedDecor op a b) := by
  unfold movedDecor codeDecor
  split
  · exact faithful_neg ha
  · exact faithful_bin _ ha hb

abbrev NodeContext := Nat × Nat × List Decor × CovPair × List BoundPool × (Nat → List (List Sig))
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let un := op==2
  let len := 1+(n - (if ka then 0 else 1) - (if un || kb then 0 else 1))
  if len>cap then true else
    let d := len==cap
    let rs := restCov (getCov cov d) (column d a.2) (column d b.2) un ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 768 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (opKeep un ka kb a b ws).map Prod.fst
      closeChild pools links (cap-1) rest (movedChoice op a b)

def moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (movedDecor op a b).1 :: (opKeep (op==2) ka kb a b ws).map Prod.fst
theorem evalMove_sound {raw T r s ws pools links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : (op==2)=false → a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible T (cap-1) (List.toFinset xs))
    (pro : proper (movedDecor op a b).1) (fresh : (movedDecor op a b).1 ∉ ws.map Prod.fst)
    (test : evalMove (cap,ws.length,ws,preCov ws,pools,links) op a b (movedDecor op a b) ka kb = true) :
    Impossible T (cap-1) (moveFront ws op a b ka kb).toFinset := by
  let z := movedDecor op a b
  let rest := opKeep (op==2) ka kb a b ws
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := keep_sub _ _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
    nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1==z.1) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp : properB z.1 = true := by simpa [properB,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if (op==2) || kb then 0 else 1)) = child.length := by
    change _ = (z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,len_keep _ _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k t hk h
  have hsz := (live_size h).2
  change child.toFinset.card + t ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold evalMove at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  have sep := cover_required h hk ndc (pair_sep pairs)
  have ce : cap-1+1=cap := by omega
  rw [ce] at sep
  let d := child.length==cap
  have g : (coverage d rest).1 = covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz := rest_coverage ha hb (op==2) ka kb d ne
  have hf := moved_faithful (faith _ ha) (faith _ hb) op
  have deq : decide (child.length=cap) = (child.length==cap) := by by_cases he : child.length=cap <;> simp [he]
  change covered (decide (child.length = cap)) (pairSig r s) child = BitVec.allOnes 768 at sep
  rw [deq] at sep
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) (op==2) ka kb ||| column d z.2) != BitVec.allOnes 768) = false := by simp [sep]
  change (if (_ != _) then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  have val := moved_full op a b
  change z.1 = _ at val
  change Live T k t child.toFinset at h
  have nd' := ndc
  change (z.1::rest.map Prod.fst).Nodup at nd'
  change Live T k t (z.1::rest.map Prod.fst).toFinset at h
  rw [val] at nd' h
  exact closeChild_sound pv lv nd' test k t hk h


def testPair (ctx : NodeContext) (a b : Decor) (d : Bool) :=
  let op := if d then 1 else 0
  let z := movedDecor op a b
  let attempt := evalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
  let z := movedDecor 2 a a
  evalMove ctx 2 a a z false false && evalMove ctx 2 a a z true true &&
    bs.all (fun b => testPair ctx a b false && testPair ctx a b true)
def testAll (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRow ctx a bs && testAll ctx bs

theorem all_unary {ctx ws} (h : testAll ctx ws=true) {a : Decor} (ha : a∈ws) (keep : Bool) :
    evalMove ctx 2 a a (movedDecor 2 a a) keep keep=true := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow] at h
    rcases List.mem_cons.mp ha with rfl | hm
    · cases keep
      · exact h.1.1.1
      · exact h.1.1.2
    · exact ih h.2 hm

theorem all_binary {ctx ws} (h : testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) (d : Bool) : testPair ctx a b d=true ∨ testPair ctx b a d=true := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      left
      cases d <;> first | exact (h.1.2 b bm).1 | exact (h.1.2 b bm).2
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · right
        cases d <;> first | exact (h.1.2 a haTail).1 | exact (h.1.2 a haTail).2
      · exact ih h.2 haTail hbTail

theorem testPair_at {ctx a b d} (h : testPair ctx a b d = true) (ka kb : Bool) :
    evalMove ctx (if d then 1 else 0) a b (movedDecor (if d then 1 else 0) a b) ka kb = true := by
  simp only [testPair,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2

theorem keep_mem {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v ↔ (w=a ∧ k=true) ∨ w∈v := by cases k <;> simp [kept]
theorem mem_delone {v : List Decor} (nd : v.Nodup) (a w : Decor) (k : Bool) :
    w ∈ delOne v a k ↔ w∈v ∧ (w≠a ∨ k=true) := by
  cases k <;> simp [delOne,nd.mem_erase_iff,and_comm]

theorem unique_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (eq : a.1=b.1) : a=b := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    obtain ⟨hn,ht⟩ := List.nodup_cons.mp nd
    rcases List.mem_cons.mp ha with rfl | haTail <;> rcases List.mem_cons.mp hb with rfl | hbTail
    · rfl
    · exact False.elim (hn (eq ▸ List.mem_map_of_mem hbTail))
    · exact False.elim (hn (eq.symm ▸ List.mem_map_of_mem haTail))
    · exact ih ht haTail hbTail

theorem kept_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (un ka kb : Bool) (v : Sig) :
    v ∈ (opKeep un ka kb a b ws).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (un=true ∨ v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist (delOne_sub ws a ka)
  cases un <;> simp only [opKeep,Bool.false_eq_true,ite_false,ite_true,delTwo,List.mem_map,
    mem_delone wn,mem_delone dn,or_false,false_or,true_or,and_true] <;> constructor
  all_goals
    first
    | rintro ⟨w,hw,rfl⟩
      first
      | exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (unique_value nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (unique_value nd hw.1.1 hb eq)) id⟩
      | exact ⟨⟨_,hw.1,rfl⟩,hw.2.imp (fun ne eq => ne (unique_value nd hw.1 ha eq)) id⟩
    | rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
      exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩
    | rintro ⟨⟨w,hm,rfl⟩,h1⟩
      exact ⟨w,⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩

theorem unary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a : Decor} (ha : a∈ws)
    (keep : Bool) :
    (moveFront ws 2 a a keep keep).toFinset = (childOne (ws.map Prod.fst) a.1 keep).toFinset := by
  ext v
  simp only [moveFront,childOne,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha ha,keep_mem,nd.mem_erase_iff,movedDecor,codeDecor,dneg,ite_true,
    Nat.reduceBEq,true_or,and_true]
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  by_cases e : v=a.1 <;> cases keep <;> simp_all

theorem binary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d ka kb : Bool) :
    (moveFront ws (if d then 1 else 0) a b ka kb).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv := List.mem_map_of_mem (f:=Prod.fst) hb
  cases d <;> simp only [moveFront,childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha hb,keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,movedDecor,codeDecor,dbin,
    Bool.false_eq_true,Nat.reduceBEq,ite_true,ite_false,false_or]
  all_goals by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all

theorem childTwo_swap (v : List Sig) (nd : v.Nodup) (a b : Sig) (d ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a d kb ka).toFinset := by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_comm d b a]
  tauto

theorem node_sound {raw T r s ws pools links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible T (cap-1) (List.toFinset xs))
    (checks : testAll (cap,ws.length,ws,preCov ws,pools,links) ws = true) :
    Impossible T cap (ws.map Prod.fst).toFinset := by
  by_cases hc : cap=0
  · intro k t hk h
    have ke : k=0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    obtain ⟨_,hS,_⟩ := h
    exact out (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  have hc' : 0<cap := by omega
  apply enum_step nd out
  · intro v hv keep fresh pro len
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hv
    have hf := unary_front nd ha keep
    rw [←hf]
    exact evalMove_sound pairs faith nd ha ha (by simp) hc' pv lv pro fresh (all_unary checks ha keep)
  · intro a ha b hb d ka kb ne fresh pro len
    obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
    obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
    have ab : a≠b := fun e => ne (congrArg Prod.fst e)
    have one (a b : Decor) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
        (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
        (test : testPair (cap,ws.length,ws,preCov ws,pools,links) a b d = true) :
        Impossible T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
      rw [←binary_front nd aa bb ne']
      have eq : (movedDecor (if d then 1 else 0) a b).1 = bin d a.1 b.1 := by cases d <;> rfl
      exact evalMove_sound pairs faith nd aa bb (fun _ e => ne' (congrArg Prod.fst e)) hc' pv lv
        (eq ▸ pr) (eq ▸ fr) (testPair_at test ka kb)
    rcases all_binary checks haW hbW ab d with hh | hh
    · exact one a b haW hbW ne ka kb pro fresh hh
    · rw [childTwo_swap _ nd]
      exact one b a hbW haW (Ne.symm ne) kb ka (bin_comm d a.1 b.1 ▸ pro)
        (bin_comm d a.1 b.1 ▸ fresh) hh


theorem agree_inputs (r s : Row) (h : ∀ a ∈ inputs, bit r a = bit s a) : r=s := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j<9
  · let i : Fin 9 := ⟨j,hj⟩
    have hm : inputs.getD i.val zero ∈ inputs := by
      rw [← input_list]
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
    exact (input_coords i r).symm.trans ((h _ hm).trans (input_coords i s))
  · have le : 512 ≤ 2^j := by
      change 2^9 ≤ 2^j
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le r.isLt le)).trans
      (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le s.isLt le)).symm

def composedOK (p q : List Move) := inputs.all (fun a => movedWord p (movedWord q a) == a)
theorem composed_id {p q} (h : composedOK p q = true) (r : Row) :
    movedRow q (movedRow p r) = r := by
  apply agree_inputs
  intro a ha
  rw [←bit_moved,←bit_moved]
  have eq := beq_iff_eq.mp (List.all_eq_true.mp h a ha)
  rw [eq]

def autoOK (T : Sig) (p : List Move) :=
  (movedWord p T == T) && composedOK p p.reverse && composedOK p.reverse p
theorem rotate_excluded {T n} {ws : List Sig} (hi : Impossible T n ws.toFinset)
    (p : List Move) (ok : autoOK T p = true) : Impossible T n (ws.map (movedWord p.reverse)).toFinset := by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p) := fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  intro k t hk h
  have run := live_rename h (movedRow p) onto
  have goal : rename (movedRow p) T = T := (moved_eq_rename p T).symm.trans ok.1.1
  have inv (x : Sig) : rename (movedRow p) (movedWord p.reverse x) = x := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    change bit ⟨j,hj⟩ _ = bit ⟨j,hj⟩ _
    rw [bit_rename,bit_moved,composed_id ok.1.2]
  have back : (ws.map (movedWord p.reverse)).toFinset.image (rename (movedRow p)) = ws.toFinset := by
    ext a
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩
      simpa only [inv] using hw
    · intro ha
      exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
  rw [goal,back] at run
  exact hi k t hk run

abbrev Packing := Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat → Nat)
def emptyPacking : Packing := (0,0,0,0,0,0,0,fun _ => 0)
def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/8192
  let shift := pos % 8192
  let lo := word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)


def lookupWord (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh)%slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots)%16 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none


abbrev Forest := Nat × Nat × (Nat → Bits × Bits) × List ColumnInfo × List (List Nat) ×
  (Nat → Packing) × (Nat → Nat → Option (Nat × Nat))
def Forest.mask (g : Forest) : Nat := g.1
def Forest.cap (g : Forest) : Nat := g.2.1
def Forest.samples (g : Forest) : Nat → Bits × Bits := g.2.2.1
def Forest.cols (g : Forest) : List ColumnInfo := g.2.2.2.1
def Forest.autos (g : Forest) : List (List Nat) := g.2.2.2.2.1
def Forest.levels (g : Forest) : Nat → Packing := g.2.2.2.2.2.1
def Forest.index (g : Forest) : Nat → Nat → Option (Nat × Nat) := g.2.2.2.2.2.2

def wiresOf (g : Forest) :=
  let ws := rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  ws
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a := by
  exact raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)

def targetOf (g : Forest) := chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) :=
  liftGoal m v
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  exact bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 768) (hq : chartSamples m q = 0) :
    properPairs (chartGoal m) (asRow p) (asRow q) := by
  intro i
  simp only [chart_bit,hp,hq,BitVec.getLsbD_allOnes,i.isLt,decide_true,BitVec.getLsbD_zero]
  simp
def selectLive {α : Type} (bits : Nat) : List α → List α
  | [] => []
  | w::ws => if bits &&& 1 == 1 then w::selectLive (bits >>> 1) ws else selectLive (bits >>> 1) ws
theorem selectLive_sub {α : Type} (bits : Nat) (ws : List α) : (selectLive bits ws).Sublist ws := by
  induction ws generalizing bits with
  | nil => exact List.Sublist.slnil
  | cons a ws ih =>
    unfold selectLive
    split
    · exact List.Sublist.cons₂ _ (ih _)
    · exact List.Sublist.cons _ (ih _)

def storedDepth (_g : Forest) (depth : Nat) := depth
def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*storedDepth g depth
  let width := len+raw.length+depth
  let recp := packedAt data (i*width) width
  let stored := recp &&& ((1 <<< len)-1)
  let ops := stored
  let bank := decodeBank depth ops raw
  (ops,bank,selectLive (recp >>> len) bank)

def getFieldV (x pos width : Nat) := (x >>> pos) &&& ((1 <<< width)-1)
def chosenSteps (bank : List Decor) (ops paid : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let more := chosenSteps bank (ops >>> 10) (paid >>> 1) n
    if paid &&& 1 == 0 then more else
      (getFieldV ops 8 2,(bank.getD (ops &&& 15) defaultDecor).1,
        (bank.getD (getFieldV ops 4 4) defaultDecor).1) :: more

def buildRule (g : Forest) (ops d : Nat) (bank : List Decor) (idx paid : Nat) : Option BoundPool :=
  (g.cols[idx]?).bind fun ci =>
    materialize (varsX (rawMask g.mask ci)) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2

theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols, Slice (varsX (rawMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : buildRule g ops depth bank i paid = some c) :
    ValidPool (vars g.mask) (targetOf g) c := by
  unfold buildRule at h
  cases e : g.cols[i]? with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    apply materialize_sound _ h
    exact cols ci (List.mem_of_getElem? e)

def getPairs (data : Nat → Nat) (w v : Nat) : Nat → Nat → List (Nat × Nat)
  | 0,_ => []
  | n+1,pos =>
    let x := packedAt data pos (w+v)
    (x &&& ((1 <<< w)-1),x >>> w) :: getPairs data w v n (pos+w+v)

def stateSet (g : Forest) (k i : Nat) := (readNode g k i).2.2.map Prod.fst
def linkedSet (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).map fun perm => (stateSet g k pair.1).map (movedWord (perm.map swapRows).reverse)

theorem linkedSet_sound (g : Forest) (k : Nat)
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
    (earlier : ∀ i < (g.levels k).1, Impossible (targetOf g) k (stateSet g k i).toFinset)
    {pair out} (h : linkedSet g k pair = some out) :
    Impossible (targetOf g) k out.toFinset := by
  unfold linkedSet at h
  split at h
  · contradiction
  next valid =>
    cases e : g.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact rotate_excluded (earlier _ (by omega)) _ (names _ (List.mem_of_getElem? e))

def nodeVerified (g : Forest) (k i : Nat) :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let values := ws.map Prod.fst
  let start := num*(10*storedDepth g depth+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 5
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let rules := (getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  decide values.Nodup && !(values.contains (targetOf g)) &&
    (if k=0 then true else testAll (k,ws.length,ws,preCov ws,rules,ls) ws)

theorem nodeVerified_sound (g : Forest) (k i : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols, Slice (varsX (rawMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, Impossible (targetOf g) (k-1) (stateSet g (k-1) j).toFinset)
    (checked : nodeVerified g k i = true) : Impossible (targetOf g) k (stateSet g k i).toFinset := by
  simp only [nodeVerified,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have hN := checked.1.1
  have hT : targetOf g ∉ stateSet g k i := by simpa [stateSet] using checked.1.2
  by_cases h0 : k=0
  · subst k
    intro t u lo h
    have ht : t=0 := by omega
    subst t
    generalize he : (stateSet g 0 i).toFinset = S at h
    obtain ⟨_,hS,_⟩ := h
    exact hT (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  apply node_sound (raw:=vars g.mask) samples _ hN hT _ _ (by simpa only [h0,if_false] using checked.2)
  · intro v hv
    apply decode_faithful _ _ _ _ _ (wires_faithful g) v
    exact (selectLive_sub _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hp
    exact buildRule_sound g cols h
  · intro tag xs hx
    have e : ((g.index k tag).bind (linkedSet g (k-1)))=some xs := by simpa using hx
    obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
    exact linkedSet_sound g _ names (prior (by omega)) h


def block (g : Forest) (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => nodeVerified g k (start+n) && block g k start n
theorem block_at {g k start n} (h : block g k start n=true) (j : Nat) (lo : start≤j) (hi : j<start+n) :
    nodeVerified g k j=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [block,Bool.and_eq_true] at h
    by_cases eq : j=start+n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)
theorem block_merge {g k start a b} (h : block g k start a=true)
    (h' : block g k (start+a) b=true) : block g k start (a+b)=true := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [block,Bool.and_eq_true] at h'
    simp only [Nat.add_succ,block,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩

def checkedTables (g : Forest) (top : Nat) :=
  ∀ k ≤ top, block g k 0 (g.levels k).1 = true
def graphValid (g : Forest) (prior : Nat → Nat) :=
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 768) &&
  (chartSamples g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.all (fun c => colCheck g.mask c prior) &&
  g.autos.all (fun p => autoOK (targetOf g) (p.map swapRows))

theorem forest_all (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower (varsX q) (graphGoal q) (prior q))
    (geometry : graphValid g prior = true) (rows : checkedTables g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible (targetOf g) k (stateSet g k i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    apply nodeVerified_sound g 0 i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact block_at (rows 0 hk) i (by omega) (by omega)
  | succ k ih =>
    intro hk i hi
    apply nodeVerified_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2
      (fun _ => by simpa using ih (by omega))
    exact block_at (rows _ hk) i (by omega) (by omega)

def indexedRoot (g : Forest) (k i : Nat) (ws : List Sig) :=
  decide (i < (g.levels k).1) && sameWords (stateSet g k i) ws
theorem root_index {g top prior k i ws} (low : ∀ q, Lower (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g top) (le : k ≤ top)
    (idx : indexedRoot g k i ws = true) : Impossible (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact forest_all g top prior low geom blocks _ le i idx.1

theorem lower_forest {g prior i hints} (low : ∀ q, Lower (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g g.cap)
    (idx : indexedRoot g g.cap i (vars g.mask) = true) (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask) :
    Lower (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) _ (root_index low geom blocks (Nat.le_refl _) idx)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

theorem lower_discard {g prior ci hints} (low : ∀ q, Lower (varsX q) (graphGoal q) (prior q))
    (ok : colCheck g.mask ci prior = true)
    (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask)
    (nd : (vars g.mask).Nodup)
    (cut : poolCut (subcube ci.1 ci.2.1) ci.2.2.2.2 g.cap 0 (varsX (rawMask g.mask ci)) (vars g.mask)=true) :
    Lower (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) _ (poolCut_sound (col_sound ci prior low ok) [] rfl nd cut)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

def Known (entries : List (Nat × Nat)) := ∀ e ∈ entries, Lower (varsX e.1) (graphGoal e.1) e.2
def extendKnown (old : List (Nat × Nat)) (L : Nat) (relabels : List (Nat × List Nat)) :=
  relabels.map (fun v => (v.1,L)) ++ old
theorem extendKnown_ok {old L m relabels} (previous : Known old)
    (main : Lower (varsX m) (graphGoal m) L)
    (ok : relabels.all (fun v => relabelOK v.1 m v.2) = true) :
    Known (extendKnown old L relabels) := by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact relabel_of (List.all_eq_true.mp ok _ hv) main
  · exact previous e h
theorem baseKnown : Known [] := by simp [Known]
def lanePlace (v : Nat) (upper : Nat) := 2^769*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^769 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
theorem lanes_and {α} (f g : α → Bits) (xs) :
    combineLanes f xs &&& combineLanes g xs = combineLanes (fun x => f x &&& g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_and,ih]
theorem lanes_or {α} (f g : α → Bits) (xs) :
    combineLanes f xs ||| combineLanes g xs = combineLanes (fun x => f x ||| g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_or,ih]
theorem lanes_xor {α} (f g : α → Bits) (xs) :
    combineLanes f xs ^^^ combineLanes g xs = combineLanes (fun x => f x ^^^ g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_xor,ih]
theorem broadcast {α} (a : Bits) (xs : List α) :
    units xs.length * a.toNat = combineLanes (fun _ => a) xs := by
  induction xs with
  | nil => simp [units,combineLanes]
  | cons v xs ih => simp only [List.length_cons,units,combineLanes,lanePlace,Nat.add_mul,Nat.mul_assoc,ih,Nat.one_mul]

def fullMarks (r packed : Nat) := ((packed+r) >>> 768) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (769*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^769)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 769*(i+1)-769=769*i := by omega
      have ge : ¬769*(i+1)<769 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 768 = (a==BitVec.allOnes 768) := by
  by_cases h : a=BitVec.allOnes 768
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^768-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^768 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm

set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (769*i) =
      (f xs[i]==BitVec.allOnes 768) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^769*u+x+(2^769*v+1)=2^769*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^769 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬769*(i+1)+768<769 := by omega
      have di : 769*(i+1)+768-769=769*i+768 := by omega
      simp only [ge,ite_false,di,List.getElem_cons_succ]
      apply ih i (by omega)


abbrev PackedSig := Nat × Nat
abbrev PackedCov := Nat × Nat × Nat

def packedSig {α} (s : α → Signals) (xs : List α) : PackedSig :=
  (combineLanes (fun x => (s x).1) xs,combineLanes (fun x => (s x).2) xs)
def packedCov {α} (c : α → Cov) (xs : List α) : PackedCov :=
  (combineLanes (fun x => (c x).1) xs,combineLanes (fun x => (c x).2.1) xs,
   combineLanes (fun x => (c x).2.2) xs)
def packedColumn (d : Bool) (a : PackedSig) :=
  if d then a.1 ^^^ (a.1 &&& a.2) else a.1 ^^^ a.2

theorem xor_meet (a b : Bits) : a ^^^ (a &&& b) = a &&& ~~~b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

theorem packed_column {α} (s : α → Signals) (xs : List α) (d : Bool) :
    packedColumn d (packedSig s xs) = combineLanes (fun x => column d (s x)) xs := by
  cases d <;> simp only [packedColumn,packedSig,column,Bool.false_eq_true,ite_false,ite_true,lanes_and,lanes_xor,xor_meet]

def packedOp (full : Nat) (op : Nat) (a b : PackedSig) : PackedSig :=
  if op=2 then (full ^^^ a.1,full ^^^ a.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
  else (a.1 &&& b.1,a.2 &&& b.2)
theorem top_xor (a : Bits) : BitVec.allOnes 768 ^^^ a = ~~~a := BitVec.allOnes_xor
theorem packed_op {α} (a b : α → Decor) (xs : List α) (op : Nat) :
    packedOp (units xs.length*(BitVec.allOnes 768).toNat) op
      (packedSig (fun x => (a x).2) xs) (packedSig (fun x => (b x).2) xs) =
    packedSig (fun x => (movedDecor op (a x) (b x)).2) xs := by
  by_cases un : op=2
  · simp only [packedOp,un,ite_true,packedSig,broadcast,lanes_xor,top_xor,movedDecor,codeDecor,dneg]
  · by_cases one : op=1 <;> simp [packedOp,un,one,packedSig,lanes_or,lanes_and,movedDecor,codeDecor,dbin]

def takePacked (c : PackedCov) (a b : Nat) (un ka kb : Bool) :=
  let without1 := fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
  let without2 := c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if un then (if ka then c.1 else without1 a)
  else if ka then (if kb then c.1 else without1 b)
  else if kb then without1 a else without2

theorem takePacked_ok {α} (c : α → Cov) (a b : α → Bits) (xs : List α) (un ka kb : Bool) :
    takePacked (packedCov c xs) (combineLanes a xs) (combineLanes b xs) un ka kb =
    combineLanes (fun x => restCov (c x) (a x) (b x) un ka kb) xs := by
  cases un <;> cases ka <;> cases kb <;>
    simp only [takePacked,packedCov,lanes_and,lanes_or,lanes_xor,xor_meet,restCov,takeOne,takeTwo,
      Bool.false_eq_true,ite_false,ite_true]

def contextWire (c : NodeContext) (i : Nat) := c.2.2.1.getD i defaultDecor
def checkAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  evalMove c op a b (movedDecor op a b) ka kb
def combField (c : NodeContext) (d un ka kb : Bool) (op i j : Nat) :=
  let a := contextWire c i
  let b := contextWire c j
  restCov (getCov c.2.2.2.1 d) (column d a.2) (column d b.2) un ka kb |||
    column d (movedDecor op a b).2

def onMarks {α : Type} (f : α → Bool) (mask : Nat) : List α → Bool
  | [] => true
  | x::xs => if mask=0 then true else
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 769) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (769*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
  induction xs generalizing mask i with
  | nil => simp at hi
  | cons x xs ih =>
    have ne : mask≠0 := by intro e; simp [e] at bitOn
    simp only [onMarks,ne,ite_false,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
    cases i with
    | zero =>
      have nonzero : mask &&& 1 ≠ 0 := by
        intro he
        have at0 := congrArg (fun n : Nat => n.testBit 0) he
        simp only [Nat.testBit_and] at at0
        change mask.testBit 0=true at bitOn
        simp [bitOn] at at0
      exact ok.1.resolve_left nonzero
    | succ i =>
      apply ih (mask:=mask >>> 769) (i:=i) (by simpa using hi) _ ok.2
      simpa only [Nat.testBit_shiftRight,Nat.mul_succ,Nat.add_comm] using bitOn

abbrev Batch := Nat × Nat × Nat × List PackedSig × PackedCov × PackedCov
def makeBatch (k n : Nat) (xs : List NodeContext) : Batch :=
  (k,n,units xs.length,(List.range n).map (fun i => packedSig (fun c => (contextWire c i).2) xs),
    packedCov (fun c => c.2.2.2.1.1) xs,packedCov (fun c => c.2.2.2.1.2) xs)
def laneWire (b : Batch) (i : Nat) := b.2.2.2.1.getD i (0,0)
theorem laneWire_at (k n) (xs) {i : Nat} (h : i<n) :
    laneWire (makeBatch k n xs) i = packedSig (fun c => (contextWire c i).2) xs := by
  simp [laneWire,makeBatch,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]

def availableMasked (p : BoundPool) (m : Sig) :=
  m==zero || m==p.domain || (p.wires.map (masked p.domain)).any (fun v => v==m)
theorem available_mask (p : BoundPool) (x : Sig) :
    availableB p.domain p.wires x = availableMasked p (masked p.domain x) := rfl

def constantLoss (p : Decor → Bool) (a : Decor) (keep : Bool) :=
  if keep then 0 else (p a).toNat
theorem lossBound (p : Decor → Bool) (ws : List Decor) (a : Decor) (keep : Bool) :
    ws.countP p ≤ (delOne ws a keep).countP p + constantLoss p a keep := by
  cases keep
  · simp only [delOne,Bool.false_eq_true,ite_false,constantLoss,List.countP_erase]
    split
    next h => simp [h.2]; omega
    next => omega
  · simp [delOne,constantLoss]

theorem keptCount (p : Decor → Bool) (ws : List Decor) (a b : Decor) (un ka kb : Bool) :
    ws.countP p - constantLoss p a ka - constantLoss p b (un || kb) ≤
    (opKeep un ka kb a b ws).countP p := by
  have h1 := lossBound p ws a ka
  have h2 := lossBound p (delOne ws a ka) b kb
  cases un <;> simp only [opKeep,delTwo,Bool.false_eq_true,ite_false,ite_true,
    Bool.false_or,Bool.true_or] <;> first | omega | simp [constantLoss]; omega

abbrev QuickPool := BoundPool × Nat × Bool
def summarizePool (ws : List Decor) (p : BoundPool) : QuickPool :=
  (p,ws.countP (fun w => isMaskedConstant p.domain w.1),
     ws.all (fun w => availableB p.domain p.wires w.1))
def fastCost (s : QuickPool) (k : Nat) (a b : Decor) (op : Nat) (ka kb : Bool) :=
  if !s.2.2 then false else
  let p := s.1
  let un := op==2
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := choiceVal (movedChoice op a b)
  let zm := masked p.domain z
  let zc := isMaskedConstant p.domain z
  let cm := s.2.1 - constantLoss const a ka - constantLoss const b (un || kb) + zc.toNat
  let free := zc || zm==masked p.domain a.1 || zm==masked p.domain b.1
  decide (k+p.paid+(!free).toNat < p.bound+cm)

theorem fastCost_good {p k ws a b op ka kb} (ha : a∈ws) (hb : b∈ws)
    (h : fastCost (summarizePool ws p) k a b op ka kb=true) :
    scalarPoolCut p k ((opKeep (op==2) ka kb a b ws).map Prod.fst) (movedChoice op a b)=true := by
  let z := choiceVal (movedChoice op a b)
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let free := isMaskedConstant p.domain z || masked p.domain z==masked p.domain a.1 ||
      masked p.domain z==masked p.domain b.1
  let rest := opKeep (op==2) ka kb a b ws
  have ck := keptCount const ws a b (op==2) ka kb
  change ws.countP const - constantLoss const a ka - constantLoss const b ((op==2) || kb) ≤ rest.countP const at ck
  by_cases all : ws.all (fun w => availableB p.domain p.wires w.1)=true
  · have hav := List.all_eq_true.mp all
    have ready : free=true → availableB p.domain p.wires z=true := by
      intro f
      simp only [free,Bool.or_eq_true,beq_iff_eq] at f
      rcases f with (zc|za)|zb
      · simp only [availableB,isMaskedConstant,Bool.or_eq_true] at zc ⊢
        exact Or.inl zc
      · rw [available_mask,za,←available_mask]
        exact hav _ ha
      · rw [available_mask,zb,←available_mask]
        exact hav _ hb
    have extra : (!availableB p.domain p.wires z).toNat ≤ (!free).toNat := by
      cases hf : free <;> cases he : availableB p.domain p.wires z <;> simp_all
    have hs : (rest.map Prod.fst).all (availableB p.domain p.wires)=true := by
      apply List.all_eq_true.mpr
      intro _ hm
      obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
      exact hav w ((keep_sub ws a b (op==2) ka kb).subset hw)
    have opOK : choiceOK p.domain p.wires (movedChoice op a b)=true := by
      simp [choiceOK,movedChoice,hav _ ha,hav _ hb]
    simp only [fastCost,summarizePool,all,Bool.not_true,Bool.false_eq_true,ite_false,decide_eq_true_eq] at h
    change k+p.paid+(!free).toNat < p.bound+(ws.countP const - constantLoss const a ka -
        constantLoss const b ((op==2)||kb)+(isMaskedConstant p.domain z).toNat) at h
    dsimp only [rest] at hs
    simp only [scalarPoolCut,hs,opOK,Bool.or_true,Bool.and_true,decide_eq_true_eq,List.countP_cons,
      List.countP_map,Function.comp_def]
    change k+p.paid+(!availableB p.domain p.wires z).toNat <
      p.bound+(rest.countP const + if isMaskedConstant p.domain z then 1 else 0)
    cases hc : isMaskedConstant p.domain z <;> simp [hc] at h ⊢ <;> omega
  · simp [fastCost,summarizePool,all] at h

def quickAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  (c.2.2.2.2.1.map (summarizePool c.2.2.1)).any (fun s => fastCost s (c.1-1) a b op ka kb)

theorem quickAt_good {c i j op ka kb} (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length)
    (h : quickAt c i j op ka kb=true) : checkAt c i j op ka kb=true := by
  have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
    simp [contextWire,List.getD_eq_getElem?_getD,ht]
  obtain ⟨_,hm,ok⟩ := List.any_eq_true.mp h
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
  have closed := fastCost_good (mem _ hi) (mem _ hj) ok
  have cut : c.2.2.2.2.1.any (fun p => scalarPoolCut p (c.1-1)
      ((opKeep (op==2) ka kb (contextWire c i) (contextWire c j) c.2.2.1).map Prod.fst)
      (movedChoice op (contextWire c i) (contextWire c j)))=true :=
    List.any_eq_true.mpr ⟨p,hp,closed⟩
  simp only [checkAt,evalMove,closeChild,cut,Bool.or_true]
  repeat' split
  all_goals rfl

def fallbackAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  (if i<c.2.2.1.length ∧ j<c.2.2.1.length then quickAt c i j op ka kb else false) ||
    checkAt c i j op ka kb
theorem fallback_sound {c i j op ka kb} (h : fallbackAt c i j op ka kb=true) :
    checkAt c i j op ka kb=true := by
  simp only [fallbackAt,Bool.or_eq_true] at h
  rcases h with h | h
  · split at h
    next yes => exact quickAt_good yes.1 yes.2 h
    next => contradiction
  · exact h
def batchMove (b : Batch) (xs : List NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,u,v) := b
  let un := op==2
  let len := 1+(n-(if ka then 0 else 1)-(if un || kb then 0 else 1))
  if len>k then true else
    let d := len==k
    let a := laneWire b i
    let b' := laneWire b j
    let z := packedOp (r*(BitVec.allOnes 768).toNat) op a b'
    let cov := if d then v else u
    let mask := fullMarks r (takePacked cov (packedColumn d a) (packedColumn d b') un ka kb ||| packedColumn d z)
    onMarks (fun c => fallbackAt c i j op ka kb) mask xs

theorem batchMove_at (k n) (xs : List NodeContext) {i j op : Nat} {ka kb}
    (hi : i<n) (hj : j<n) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n)
    (pass : batchMove (makeBatch k n xs) xs i j op ka kb=true) :
    checkAt xs[q] i j op ka kb=true := by
  let len := 1+(n-(if ka then 0 else 1)-(if (op==2) || kb then 0 else 1))
  let d := len==k
  have eval : checkAt xs[q] i j op ka kb =
      if len>k then true else if combField xs[q] d (op==2) ka kb op i j != BitVec.allOnes 768 then true
      else if !properB (movedDecor op (contextWire xs[q] i) (contextWire xs[q] j)).1 ||
        xs[q].2.2.1.any (fun v => v.1==(movedDecor op (contextWire xs[q] i) (contextWire xs[q] j)).1)
      then true else closeChild xs[q].2.2.2.2.1 xs[q].2.2.2.2.2 (k-1)
        ((opKeep (op==2) ka kb (contextWire xs[q] i) (contextWire xs[q] j) xs[q].2.2.1).map Prod.fst)
        (movedChoice op (contextWire xs[q] i) (contextWire xs[q] j)) := by
    simp only [checkAt,evalMove,budget,arity,len,d,combField] <;> rfl
  by_cases small : len>k
  · simp [eval,small]
  · let r := units xs.length
    let a := laneWire (makeBatch k n xs) i
    let b := laneWire (makeBatch k n xs) j
    let cov := if d then packedCov (fun c : NodeContext => c.2.2.2.1.2) xs
            else packedCov (fun c : NodeContext => c.2.2.2.1.1) xs
    change (if len>k then true else onMarks _ (fullMarks r
       (takePacked cov (packedColumn d a) (packedColumn d b) (op==2) ka kb |||
        packedColumn d (packedOp (r*(BitVec.allOnes 768).toNat) op a b))) xs) = true at pass
    rw [if_neg small] at pass
    have chosen : cov = packedCov (fun c => getCov c.2.2.2.1 d) xs := by
      dsimp only [cov]
      cases d <;> rfl
    have ca : a = _ := laneWire_at k n xs hi
    have cb : b = _ := laneWire_at k n xs hj
    dsimp only [r] at pass
    rw [ca,cb,packed_op,packed_column,packed_column,packed_column,chosen,takePacked_ok,lanes_or] at pass
    by_cases hit : combField xs[q] d (op==2) ka kb op i j = BitVec.allOnes 768
    · apply fallback_sound
      apply marked_ok _ _ _ q hq _ pass
      rw [mark_at _ _ _ hq]
      exact beq_iff_eq.mpr hit
    · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]


def batchPair (b : Batch) (xs : List NodeContext) (i j op : Nat) :=
  let f := batchMove b xs i j op
  f false false && f true false && f false true && f true true
def batchRow (b : Batch) (xs : List NodeContext) (i : Nat) (js : List Nat) :=
  batchMove b xs i i 2 false false && batchMove b xs i i 2 true true &&
    js.all (fun j => batchPair b xs i j 0 && batchPair b xs i j 1)
def batchRows (b : Batch) (xs : List NodeContext) : List Nat → Bool
  | [] => true
  | i::js => batchRow b xs i js && batchRows b xs js

theorem batchRows_at (k n) (xs : List NodeContext) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (js : List Nat)
    (bounds : ∀ j ∈ js, j<n) (allRows : batchRows (makeBatch k n xs) xs js=true) :
    testAll xs[q] (js.map (contextWire xs[q])) = true := by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [batchRows,Bool.and_eq_true,batchRow,List.all_eq_true] at allRows
    simp only [List.map_cons,testAll,testRow,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi := bounds i List.mem_cons_self
    have check := @batchMove_at k n xs
    refine ⟨⟨⟨check hi hi hq budget arity allRows.1.1.1,check hi hi hq budget arity allRows.1.1.2⟩,?_⟩,
      ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j,hj,rfl⟩
    have hj' := bounds j (List.mem_cons_of_mem _ hj)
    have both := allRows.1.2 j hj
    have opCheck (d : Bool) (pass : batchPair (makeBatch k n xs) xs i j (if d then 1 else 0)=true) :
        testPair xs[q] (contextWire xs[q] i) (contextWire xs[q] j) d=true := by
      simp only [batchPair,Bool.and_eq_true] at pass
      simp only [testPair,Bool.and_eq_true]
      exact ⟨⟨⟨check hi hj' hq budget arity pass.1.1.1,check hi hj' hq budget arity pass.1.1.2⟩,
        check hi hj' hq budget arity pass.1.2⟩,check hi hj' hq budget arity pass.2⟩
    exact ⟨opCheck false both.1,opCheck true both.2⟩

def runBatch (k n : Nat) (xs : List NodeContext) :=
    batchRows (makeBatch k n xs) xs (List.range n)
theorem runBatch_at {k n} {xs : List NodeContext} {q} (hq : q<xs.length)
    (hb : xs[q].1=k) (ha : xs[q].2.1=n) (hn : xs[q].2.2.1.length=n)
    (pass : runBatch k n xs=true) : testAll xs[q] xs[q].2.2.1=true := by
  have all := batchRows_at k n xs hq hb ha (List.range n) (fun _ => List.mem_range.mp) pass
  have eq : (List.range n).map (contextWire xs[q]) = xs[q].2.2.1 := by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2
      simp [contextWire,List.getD_eq_getElem?_getD,h2]
  rwa [eq] at all

def contextOf (g : Forest) (k i : Nat) : NodeContext :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let start := num*(10*storedDepth g depth+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 5
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let rules := (getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  (k,ws.length,ws,preCov ws,rules,ls)


def prelim (T : Sig) (c : NodeContext) :=
  let ws := c.2.2.1.map Prod.fst
  decide ws.Nodup && !(ws.contains T)
theorem from_context (g : Forest) (k i : Nat) :
    nodeVerified g k i = (prelim (targetOf g) (contextOf g k i) &&
      (if k=0 then true else testAll (contextOf g k i) (contextOf g k i).2.2.1)) := rfl

theorem makeBlock {g k start n} (h : ∀ (i : Nat), start ≤ i → i < start + n → nodeVerified g k i = true) :
    block g k start n=true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [block,Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega),ih (fun i le lt => h i le (by omega))⟩

def contexts (g : Forest) (k start n : Nat) :=
  ((List.range n).map (start+·)).map (contextOf g k)
def header (g : Forest) (k start n ar : Nat) :=
  (contexts g k start n).all (fun c => c.2.1==ar && prelim (targetOf g) c)
def rowCut (g : Forest) (k start n ar lo len : Nat) :=
  let xs := contexts g k start n
  let b := makeBatch k ar xs
  (List.range len).all (fun d =>
    let i := lo+d
    batchRow b xs i (List.range' (i+1) (ar-(i+1))))
theorem rowCut_at {g k start n ar lo len} (h : rowCut g k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    batchRow (makeBatch k ar (contexts g k start n)) (contexts g k start n)
      i (List.range' (i+1) (ar-(i+1)))=true := by
  have ha := List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha

theorem rowCut_merge {g k start n ar lo a b}
    (h : rowCut g k start n ar lo a=true) (t : rowCut g k start n ar (lo+a) b=true) :
    rowCut g k start n ar lo (a+b)=true := by
  apply List.all_eq_true.mpr
  intro j hj
  have jlt := List.mem_range.mp hj
  by_cases first : j<a
  · exact rowCut_at h (lo+j) (by omega) (by omega)
  · exact rowCut_at t (lo+j) (by omega) (by omega)

theorem cutsRun {g k start n ar} (h : rowCut g k start n ar 0 ar=true) :
    runBatch k ar (contexts g k start n)=true := by
  let xs := contexts g k start n
  have go (lo num : Nat) (eq : lo+num=ar) :
      batchRows (makeBatch k ar xs) xs (List.range' lo num)=true := by
    induction num generalizing lo with
    | zero => rfl
    | succ num ih =>
      simp only [List.range'_succ,batchRows,Bool.and_eq_true]
      refine ⟨?_,ih (lo+1) (by omega)⟩
      have ok := rowCut_at h lo (by omega) (by omega)
      simpa only [show ar-(lo+1)=num by omega] using ok
  unfold runBatch
  rw [List.range_eq_range']
  exact go 0 ar (by omega)

theorem cutsBlock {g k start n ar} (hd : header g k start n ar=true)
    (h : rowCut g k start n ar 0 ar=true) : block g k start n=true := by
  apply makeBlock
  intro i lo hi
  let xs := contexts g k start n
  have hm : contextOf g k i ∈ xs := by
    apply List.mem_map.mpr
    exact ⟨i,List.mem_map.mpr ⟨i-start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  obtain ⟨q,hq,e⟩ := List.getElem_of_mem hm
  have one := List.all_eq_true.mp hd _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at one
  have hb : xs[q].1=k := by rw [e]; rfl
  have ha : xs[q].2.1=ar := e ▸ one.1
  have hn : xs[q].2.2.1.length=ar := by rw [e]; exact one.1
  rw [from_context,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ runBatch_at hq hb ha hn (cutsRun h)

def boxes (g : Forest) (k start n ar lo num : Nat) : Nat → Prop
  | 0 => rowCut g k start n ar lo num=true
  | d+1 => boxes g k start n ar lo (num/2) d ∧ boxes g k start n ar (lo+num/2) (num-num/2) d
theorem boxesCut {g k start n ar lo num d} (h : boxes g k start n ar lo num d) :
    rowCut g k start n ar lo num=true := by
  induction d generalizing lo num with
  | zero => exact h
  | succ d ih =>
    have v := rowCut_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self num 2)] using v

def cells (g : Forest) (k start n ar rows : Nat) : Nat → Prop
  | 0 => header g k start n ar=true ∧ boxes g k start n ar 0 ar rows
  | d+1 => cells g k start (n/2) ar rows d ∧ cells g k (start+n/2) (n-n/2) ar rows d
theorem cellsBlock {g k start n ar rows d} (h : cells g k start n ar rows d) :
    block g k start n=true := by
  induction d generalizing start n with
  | zero => exact cutsBlock h.1 (boxesCut h.2)
  | succ d ih =>
    have v := block_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v

def listPieces {α} (f : α → Bool) (xs : List α) : Nat → Prop
  | 0 => xs.all f=true
  | d+1 => listPieces f (xs.take (xs.length/2)) d ∧ listPieces f (xs.drop (xs.length/2)) d
theorem listPieces_all {α f xs d} (h : @listPieces α f xs d) : xs.all f=true := by
  induction d generalizing xs with
  | zero => exact h
  | succ d ih =>
    have ap : ((xs.take (xs.length/2)) ++ (xs.drop (xs.length/2))).all f=true := by
      simp only [List.all_append,ih h.1,ih h.2,Bool.and_self]
    simpa only [List.take_append_drop] using ap
def g15d3 (i : Nat) : Nat := 0xf
def g15l3 : Packing := (1,0,0,0,1,0,0,g15d3)
def g15samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbaf3ea78de4d799d,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff450cc90c3c245919),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdf7ff8fe9f9b7ed5,0x20812421801324c4),(0xefbdbf97f9f6bf6a,0x102a401415600a0a),(0xf3a9d7437375f5ba,0xfc028ab620235b0),(0,0),(0,0),(0,0),(0,0),(0,0)]
def g15columns : List ColumnInfo := []
def g15autos : List (List Nat) := [[],[33,48]]
def g15levels : Nat → Packing
  | 3 => g15l3
  | _ => emptyPacking
def g15index : Nat → Nat → Option (Nat × Nat)
  | 3 => fun _ => none
  | _ => fun _ => none
def g15 : Forest := ⟨15,3,fun j => g15samples[j]?.getD (0,0),g15columns,g15autos,g15levels,g15index⟩
def key31l6 (i : Nat) : Nat := 0x820007028af371d000003180048302e380000000003819155875690d58000003d
def g31d5 (i : Nat) : Nat := 0x84001e90fd02fd01fa00
def g31l5 : Packing := (3,1,3,0,4,4,0,g31d5)
def g31d6 (i : Nat) : Nat := 0x11a20bf
def g31l6 : Packing := (1,0,3,2,4,0,0,g31d6)
def g31samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdafffab2d55fb9f999d9ceeefacb357b78f9ce2bb554a3bac97b2a9d65,0x250142092220460600407048c382809c2160e048740030a88143281c44),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffef5dfed46f26fea572a7ba9effd7341aff97ad1ab5bd2d547d6793334b,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff90aa211010d10141c4300836206168204010183680184d04682483210b),(0x73ef3f3c8ff8df3fe567b556c9567ffcd665219778a6bd6e36bfd946ac,0xc10d0c3000214920a0d648109801012344d60802686b04210115006a4),(0x7c7fd57b7ffa3476e74d6f3fc4bddbd44dc213c5eb8bdea95bf6ee7492,0x38022048645c06490200044a25241818912934541000824c322ae5002),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8fe76ff6451fda6ff84b6daf38f5bb6f6a5ee88a4d6be3f71c64aa3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8076989008882001270e063010011622500c04308a174300141c40a239),(0,0),(0,0),(0,0),(0,0)]
def g31columns : List ColumnInfo := [(1,0,30,0,4),(2,0,29,0,4),(4,0,27,0,4),(8,0,23,0,4),(16,0,15,0,4)]
def g31autos : List (List Nat) := [[],[50,65],[66,16],[67,50,33,16],[67,32],[67,66,49,32],[33,48],[67,50,65,48],[67,66,65,64],[49,64]]
def g31levels : Nat → Packing
  | 5 => g31l5
  | 6 => g31l6
  | _ => emptyPacking
def g31index : Nat → Nat → Option (Nat × Nat)
  | 5 => fun _ => none
  | 6 => lookupWord 5 25 2 10 2 4 (key31l6)
  | _ => fun _ => none
def g31 : Forest := ⟨31,6,fun j => g31samples[j]?.getD (0,0),g31columns,g31autos,g31levels,g31index⟩
def g47samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffddffff5cfaafae7dd35b9ce7bbffd6b6b7b7cfbb8d3b7ad85ddf257b56b575,0x2200a042011011800c00803812181c2009c1061c0107200c09440143143444),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeebefed537937fcb8ab173daa7df7f7691aff9776b2b7dcb92a3f3678b2b59,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9149112428688034a38448020d64a21d120601022ea84882b022a624830919),(0x77db9fef67fc77f3ffe6e3dd55f86b6fffcab66472f7c57fb768dabfad4eae,0x820641080010508440806b120004c020121a4ec1002247c020840112806a4),(0x78ebe4ae9ffd0d576de696b3cff805db7d426c00d8ded437ed436ff6f66c92,0x71419416322f057a950700411b6b328381c4110e8d4580325370f22d66812),(0,0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0bf9ebdb2287acd4afec26dbb6d98eabb3768bb508ca4b7f1fdd1c709a3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80f74f1424444852a26637058ca3a012d22680c12e48c8e17411561c608a3b),(0,0),(0,0),(0,0)]
def g47columns : List ColumnInfo := [(8,0,39,0,4)]
def g47autos : List (List Nat) := [[],[83,32]]
def g47levels : Nat → Packing
  | _ => emptyPacking
def g47index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g47 : Forest := ⟨47,4,fun j => g47samples[j]?.getD (0,0),g47columns,g47autos,g47levels,g47index⟩
def g55samples : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbfffffdf7defdfafbfd3fcebcfdeffcebffefe76de77fed7f1773f95eb2ebeb,0x400028000010005000000400701010180030103060043200102204010904888),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdb7fbfbb9ad3afd94caf0b9db5bbdf7f7d39bfcdadcf77ec9eccd2fb9cf16b5,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2484444214284026a4e002420468a8a43140a00408d944460a4082569431231),(0xeda5e7e7b2fc29de4ffc371dba2bf0775ff12db9b18bb528fedad96afcd3c5e,0x12589919410293410206d0396285445a082c5d2bf0022b20f0895d2048c2c4e),(0,0),(0xf1cd79264efe956afa7a64bb677ab40beba463600362eda36f3357b7d763926,0xe3a8651b1a36a0acc57538a080f6ea703078a0c13c28dc34c91f3868663126),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe05fe74eda341d5872cbf684d5e2ed19e7e3bba5e964550dd792aec724f479,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01fb53db1204342a549861b60b6727a22d48ac0b14da4445855161ae724b471),(0,0),(0,0),(0,0)]
def g55columns : List ColumnInfo := [(16,0,39,0,4)]
def g55autos : List (List Nat) := [[],[84]]
def g55levels : Nat → Packing
  | _ => emptyPacking
def g55index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g55 : Forest := ⟨55,4,fun j => g55samples[j]?.getD (0,0),g55columns,g55autos,g55levels,g55index⟩
def g63samples : Array (Bits × Bits) := #[(0xdabffdfdbdf61bfbfc7dcbe34f7f1b17917df75df7edd9eff77b6dbd3dcebed3cfbfaddba50fcabded46bc9b579eb7bd3d92776566ad4ad3debe36d74deb7f9faf189ad76da7dc1a6b4eaf21eb254de4ae1f7451bb34d9456fd18e934db17349,0x4400202400040800310000100084000ac0000102800a1100490002240004b2800a001b4000190000008108000574009200040400000594000190004218c0010840002890800550053044a00410008802d0060013000c004400188120c206208),(0xb6678efeffcbf5a9cad5bfd527a7a5bd74d1314b7915f5b2ffdec2fc5d978f8ab3b44b2b5add5b771711b15ce99bf2b3f5bce975ef94cd59a34e76ab937848a94ef6be6c9579db5905539ea703c87a7d4ae11fe2ae423fade4a3c3299b0724e7,0x499461811a200a55004cf88854029340027a680613c002ec00233c1096d01045025d0203d400243150030b7e4900b00499e023395882049d0206ec00041398010bbb1000b7310ad00cc0858112c8207810e917400e423d0034024309910504e5),(0xbfdd27bedf8fade4776ebf9d185bc5bd76aeffb29711f77d628e86e5fffdff6d1a52bff6da987348e3e147dcecdbcc68d1accc4e7d7d77b9734cfbbcefbc022d72eff5a31a72e32584dd5a72accb1256ede309af577ea6b3ab2be572a2769632,0x20983204990108b1910222a2810c12a8041040402e00006394000908008912a582448429aad10a21a0240190b504314209040621245140c82010e8812042049440841100c0c52080310832a5111106e902488a012c82618908a42202729212),(0x77ddb87389d95f9f7bbe7e8eb89e6e76fbf75ca7fd5bb3758b555b578affe964ae7e7fa493e06d03bebc4fb5cff51e46b2dd5bdbb1eab66f60f7d916b9c6944fd85b6f0fc30a2ae7d2afc9dc369ef80bb1b0b2dd52e9331e786f7a5d38e8c8b4,0x1482478012444200420888514440810c402202189081ecc814422aa4c048408050190921c0450c000a080254044021081134422900082c11250884167012813a48094aca870a3283708e41084282480000c012150640581c30655a55288040a4),(0xdca768aafb78ce8d2db2ec3fbdddfa4ec963339dbac7a8e05eccbf0bb99ddf5febcef6dc7762a4a79d9ad8f70324ba6e724754bded1eed86f695f276b70acbd73dc66e39a88d0cfed920a0ee10b5a4dd5893bba709bff6dc1ece388c561e1ed5,0x210938550593284a984457082a220ca002159526023c0223a02100100d271046aa46f2022bb0201ea5730921b3008e848a002106a7520082d20653c8040064810364a00030c5086c0c2084761035a077101508a009ba22e00b822088521e1c51),(0x77dad76bd4ced656e7ec247a694c9eb5b66dc4de71aac18acebb177a9bac7a62d6f3e3996dd9d62d6ecf7b18557229a30b5ebb1ef46b568a8f3400a7c2d3365caade63d0f2234a24623735bcfaee29c0664eddfc63b2a86915f817ca03dc41fa,0x88252894b2b3256598a758928465236453b27d28c68c4c28a24dcc0d24d500d4a845700845b04bd175706d345a20a0a24d641d897dd822a1d52444cad2629c8e732b305273362844202335b73c8d8150424e93e44a78286995ec17c803dc01f2),(0,0),(0,0),(0,0)]
def g63columns : List ColumnInfo := [(32,0,31,0,7)]
def g63autos : List (List Nat) := [[],[50,65]]
def g63levels : Nat → Packing
  | _ => emptyPacking
def g63index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g63 : Forest := ⟨63,7,fun j => g63samples[j]?.getD (0,0),g63columns,g63autos,g63levels,g63index⟩
def g111d6 (i : Nat) : Nat := 0x120ff
def g111l6 : Packing := (1,0,2,0,1,0,0,g111d6)
def g111samples : Array (Bits × Bits) := #[(0xeafcc7b96fc59ffd26c5e2bb3d7bd378fb35ff5dcb26f92afa5f57eff59a73b7aaa379b2fc8d7a99e2ef9efcf4defd4efabc9c89733cebade5579ad5abbcd64d8557ad3d63bd1c6a75510ce3b9bf05e462ee0edf6dfb2914efc74c7d31727465,0x4d00310a2003881269402d0c00406ccc142a8012908082d00025ac006a88036948003229000032d4001bf20024ec2018680000aaf2500325400423a6f02003840040a8016ea8106822700071012c01d500600ad401ea0010f407087831504444),(0xf771ad34ff2bcf4fbd7f5f5de52efaeb7ebbabfffefbf2eab7c7cf56f8ecea565ddfabcf87cb61db9d6ef4aecff7cebd76fe679cfb9935e6adabc77cdcdb677ed3da5e4f56b4cbe39cfd7aed1f519a6b999796b48a51f4f7b8ad91a66cc6d9cb,0x1204940050200482000010001c10308054448009004424020800871400ac0690000402004e0508404004081210450414000904018220d090010808000a44280600460810104d92040818880c1010088d8400200a10a1400808810604821909),(0xf5be76df5e79b8b5d13f5f6e3ecd176fbeee538a7cfb9f7f6b7fad9b13bb7fed97560ecd71f29f3f1e3ef959a338e3a9e32bd5e7cfc7b51df73d7e9e165479b3baa9a0d59e62e11eead3ad5c624777de8699f96d3766d64d1f3fa2ca8f3d2e52,0x8e4d19200884440101e4a802e100a0c04000830eb000289800c49240c1c411082c325a6812b0485430294040c52402008322a4b0e00c0021216842103a050a9080848145264020288841a770220547500211500d95204c05521120880b352452),(0xde2ebbc73c1cf83c4cedbed77297d7f5b666582db23d5c5d7bf4a54b37a75f4992f88d683d388ea5bafb57791a5deb9b257390777cf70e9d329773c24416edd93fe3d2909bc3b81d7e62dd94d70a759eb42b6b51587d63da2e7eea6ce78912bc,0x10b22099c5638280b403142808691e02bd9d04d1097a9640ce2041351e20e64283892100494815238b12089820999d9858901b4e1903515e001721098578a5416f515492d981d895722018845902b08a5c4a2a2248dd03d08c66ca64e48812ac),(0,0),(0x4a99db5e74fdf3bbfb83b4b12e735e58f515867b75942dba656f9eeac55739b971685432ece5b39368c30fbbb9f895ca9efa5eceda2fea7be4766f052ba5def635ccf928215f7640050f6846acafb2ca6efbba0bffbfdb9043d87d111c3c3ebd,0x12d68401de50564414b80023f49c0203c0413d800068400bbb08034f0177ac0427f40400f6de0023bcc009fc1201950403ff4900082ea08a2fc908010c8a4053de0011e801464d050407f806ac13f8026d9b800bfa055d40038875010c2c3ab9),(0x107b7e8791b6519a9ebd6f37d374faa298392ebad8b5e4afe6bd267679568b3365bebaabdf6ef4e9035a918e8ca50ef74769b2b74aea726a09a6c5e9463715fb76745a9b1b6212a1b9add6dec52a9ba55b57e399ab660ca6d0f217384af881fe,0xadc48a6a24248ac9294916cc74a18dce4988890976a839d0a90054480a8f001149b409fd5690d8d50882129489ae3083c83b5253565cd02541ca4550f495b985581508b28aaa022919a1e755a00eaaa54243a315f06a0c87d4f216384a7880f6),(0,0),(0,0)]
def g111columns : List ColumnInfo := [(4,8,99,0,4),(1,32,78,0,4),(64,0,47,0,5)]
def g111autos : List (List Nat) := [[],[83,32]]
def g111levels : Nat → Packing
  | 6 => g111l6
  | _ => emptyPacking
def g111index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | _ => fun _ => none
def g111 : Forest := ⟨111,6,fun j => g111samples[j]?.getD (0,0),g111columns,g111autos,g111levels,g111index⟩
def g119samples : Array (Bits × Bits) := #[(0xfab75f3dfbfa3756f92d9ff7baf5ff7dbfebb9b33bef7dcdf77fbffe7bbbf75546cedccfd6f7eb762bef3ffdd2ede7abbef7e4e4b775eb9be6ab6f4d5fde77f2b955ece57b3feb97c6d99b5cdd2fdd2ea315de5f3efbf8d44ddcaa7566eda9cd,0x20100000802449000a820000c1900042800052080010000098c000620802429000050a2000012e00000be20013404000082000047420011240000c8b8000110080002480036500158018000c4009400c9000c0062803a0400e00885042a10888),(0xaf7efcd6de9febfb57d6f5ddedde36f3db7fffeed79fdbfafcf255738c743cbbbff3e3b86b8f9fb9f5bdf54fbff79bd74f5afb3f7fba34f5bf5f9afae879ab5feefe93fa9ee6566f7bbee6bf67d426d75cfb2bace9344fabf72bd58e999b76b3,0x9300010000091004000400382060802420900110020801010208161810541520000000800198110400c004084880812115000049028020c0800220200009220a01801050108206a8408406120184808104430800802442850101410609083421),(0xd3aee9d1a16b8afb579b1b1a2ede96c634714fced4ed35afb8d86696aabedb2eada373270f48f3a9b93de8a90d87d8f6684756adef8eb40bf672fc78b9342c9c7aaa652b2aec9422dd38b32b2a5255bdcc3d35b2da5f372953f3c4ba3a70d996,0x2c07b23e74020fd2aa41748155856818d263d681015680dac92709c7448b08586eaf3a512642c64b613a9091954b38c222671d26711d023332d48951dd0691952839212f8b6888039910b9ac2a42653c283c65315b1b95185ae084b83270c996),(0,0),(0x759a506bc07865de6f37bc2fabe39a5e2705b6a3eec6bd3cca572e3ed72f0325f632aa43d8e0e833eaeab6f86ad5fa72dbaf9c83b9e70faa212acf122e177ae733d8fa39a0b0bb12b7915f7134c3b9a9ed98d75362b1d9c725676c3caf04637c,0x16e5f59c6d01a255c44806523c0cddb5529a2196d082e7c24415d298c0f10d071e6090549dc090f8ed501938009f3fb2169588d90b0b506d102e01343cb84ad135f45369a498be0a36011e712702bb816af81651c4b05c0701a6642cad046374),(0x6339c3e76f77dc41ec6c9766b8b0f93592cd6e58a17db2abb9eea5cd269eeae2dc2c1c9ec755bae6a2821f6b678c3538a75edaf56c57e97ff4e8b90d55c4e75ce36b37ac511be4c610c6f229b9ab77956345b3a117ef6f3608dd37697870ba61,0x84ef690f5888a6bc0049f9381c0ba0115db000874a075d2102333605e754184fe100105f739880fb92c019ec481f2d2102dbf2480954a0ad3f922114724920d57f80032e5018c6a22083e62199863ec06b43378157e41d3d00d937293850b261),(0xd5cc96ab2735f4eedbcfece9fd4d847149d75b8aa71ff3959066dc7566c66ecb75975abde9bb8d684d89311f3151135dd1ce4d97acd9737d0b4d97b62b1596cf57b51ab1b6b408593b67d5bb928b32dabad66fc43367241aeaae177095e247ea,0x481560b0cd924918c5323d4303992d88d1232e6a49f254a2454320824e8122936522ef3572424e688310332525616c12e023da92a435d213539c9243b254cc21b63548a8e4258841b361f1c95a017252ba1c47902bc1245a7a8e167094e243ca),(0,0),(0,0)]
def g119columns : List ColumnInfo := [(4,0,115,0,5)]
def g119autos : List (List Nat) := [[],[84],[98],[84,98],[101,66,16],[101,100,66,16],[101,84,82,16],[100,82,16]]
def g119levels : Nat → Packing
  | _ => emptyPacking
def g119index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g119 : Forest := ⟨119,5,fun j => g119samples[j]?.getD (0,0),g119columns,g119autos,g119levels,g119index⟩
def key189l7 (i : Nat) : Nat := 0xa81337040d4b600002948880000590cc33d41450272020001b1
def g189d6 (i : Nat) : Nat := 0x82000f487f40bfa03fa00
def g189l6 : Packing := (3,1,3,0,4,4,0,g189d6)
def g189d7 (i : Nat) : Nat := 0x1f5859bf
def g189l7 : Packing := (1,0,3,2,4,0,0,g189d7)
def g189samples : Array (Bits × Bits) := #[(0x76b7b935ad7f6fd4d735f26d2df10ff4361bcad97bdde979efcd6e58b7554d7ea7eff73e73de92e56562d7533a4ef3de34b1f6acf1d6e216666babd43dbaabce3ad8d545ed4e53771cb4e6d84ab365f9722155b0decf672135d0ab0e8aab3265,0x8404642124899480a2a81184400c4494a40542200633c0114901482008a100b4c40690c02a500485280025a8300be5004d078022244028e4a0122910034dd0088624c002500565400b4701a401901a06a801c60d40e430038408b0c08aa0264),(0,0),(0xb725f7b34edfbeffaf8e64c99fca263eeb8ebd6e6efba6759d07fff35f0d57cf0f1af1c8e8596f2d9f9a363b65aade972ff9af593499366f72b4e55d5e6f961954d5fce693a74e66d370dbbd59357a0ab5d8c2e2b4913d9ddc0ac963246654eb,0x2019084c910042485050a84580141012107000421c10cd02a29a004c0424911090cb1414ac1a4012048a60a1130c00921224ba8854044c203120d1318881010110848d88109408245548f0845c253042044cc0e02091152804424943044214c9),(0x6b3b37beb0d3b3db67cafb77eb9e1dd789aebdb18d1db77732f653e35977f97f4dd313687fb67a399a5d29e7c5c2df2ae361e9d1a8a6a7bdf9b41bf76bf3c59c972736ba642a6ec8e10ddd388a5d8a2fef454b2f6c5cd8cb4dafd1a5458caf32,0x84c42401462a8882042c15880121e0040f09501440a3008044047580824b00c92204cb801220a2e8d004050a8c13a8082552010080e322ce0002224042220e86c96110212062d680201609100358082de8010e0a0c4e080169249024018caa32),(0xeed4ecfef66eeb7efebdd9aee7077cf1671b7b7a97dfdfd372d0ed94ede3ade9c50737565e265d36d07689d4ac4faafe5abbfdc5676e89f79f8f9a623b38502f3db98ff0fa982b81b88d0790fae9d8d74f74351d5187af7a955e769667c1914c,0x112b0124099000041080680538580102a03620812918016ca82b084951200b0011391441e40a1406003a00a460640102802906c05910d52121d05c00b8012058249003c452192901d049060038a0e052051c011422a1a0780618649266411108),(0xd9cafe65094bbf5f7264b7bbce3ffbefdc6762cbb35969c8ac2ddbae62ff5a5f3ee2cea13be5ccd265ed5a725a1921f7f9e712e69e98fb2d45e97fd5f2e0abe4f3f7676b375491bf662220c7ec1235aaa52f7b260bfdf8f023b73c589c1c3f19,0x2215018860a440b0408528403b942810a5b0009c1c080302094a000184016510830b02e2ac10b810014a60046c8c012e120b028809b84c0105208c4e88802201101131880274018a550300819c02301e012cc3000b90a8a80382305084143519),(0,0),(0xe9cbc8feffb7f8e7b8d17ff4f26deb6af5fadcfef4fa8da189aed6c66eadfbba567e7aa58acda76b57bfee9d03799233ac5e277f4fab9af55d736c18d65d30adcab7ab9d1b9dcbcc02d24b67373e9182d29baedd99bcc115aa3d04dc337a48be,0x1420360100482d00252a00a2440945244a022b202187302c44004bb2035a00002400090800450025fa000d1a80010240a950404582409154ca522280124a1c0c672a40054909a2500214036203d800a092812c0514244211e81d048c33284826),(0,0)]
def g189columns : List ColumnInfo := [(1,0,188,0,5),(12,0,177,0,4),(16,0,173,0,5),(17,0,172,0,4),(24,0,165,0,4),(33,0,156,0,4),(132,0,57,0,4),(160,0,29,0,4)]
def g189autos : List (List Nat) := [[],[84,115],[117,67,32],[116,83,32],[82,48],[84,115,82,48],[117,116,115,114,64],[83,114,64],[116,50,80],[117,84,67,50,80],[84,115,66,112],[66,112]]
def g189levels : Nat → Packing
  | 6 => g189l6
  | 7 => g189l7
  | _ => emptyPacking
def g189index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | 7 => lookupWord 5 18 5 10 2 4 (key189l7)
  | _ => fun _ => none
def g189 : Forest := ⟨189,7,fun j => g189samples[j]?.getD (0,0),g189columns,g189autos,g189levels,g189index⟩
def g127samples : Array (Bits × Bits) := #[(0x27ec63be833e95d9cd8b1b0f8c7b949b955ab7ff06f2f46fb53d19a8b89e2cf938ea5b637a679113a99b1a558cf5d3757100e2a2d92956b1df648864a3a84cf9f5aafcc4980f547cd2d2abacb351593072ded0ca36876c216b176a15583d3069,0x215000b22a840210400a1040082a19401000220004808d00802008c02014082088420800402688520818425544410445400040805130408104600820a3600c001020e0440008143510802b10a111102142440000168440214816081150281060),(0xd1272c7d4d43f0bd72e56dab39ddfe7c6a407c139e413a8c95b2f6c7134bd9d2e6151acc0f6f6e61aecc859cb80ab9d38d1f9c08bbd08127631b9fb156aefb042a9049abe4f27cdb8815184a3fa2b5dede495570df2830da3c38c46cf1426d13,0x806000d540888802080408280406213088804000000320c048631024209804006241648090164a10080940a08001912a8109004a2408004431a0101080453200880088a80c0004a880100481a02008819080040c10830122428406420422c11),(0x3757a63bdee4ba3fd3e2275cd925bbac4327c3605b6a92ba668b6b375f5956a61c0ee4c8b6382a0c726a8d674c1d24e187c7697b46618e9a3259ec9e635cb1935494676727a9c6a3df6b34450ca72f271676b8367562d5a985429aaa9a64d626,0xe190134200c030558e6885084d0788a40161e860830e0412a109c61098d030850809a9902628890c322a09e446182064058721691005078a1841cc5c6248a09654242521162044855722240404692506023498262462c48981029a8a9a244222),(0x7c12f7ae7cb67a121957d4766ab145360dad0baa714fd5dd4ad95b9245e39e4cff88a61691dd24ee5570ea624367b54a6aea5375c626bc6f4082772e38770d5a1955fa1dcb198b20afa8d659c70c9ab5dbb42b955b55e374e0f839c3068a9694,0x100b203118264280010702e3020864421484020c18c0438c4090018044060d7096401604915660c20151c00201478d0220604290c2020821402022221025140809114a0c4919231288809339110498f1918002911b15216460582041008a9494),(0x5f0ed2cab79191489f9794fa9f865222c0c45f4f23977137ba6ec87e2fb718cbcb3281372d8190b9e5b2713c276012285f3b185c628f375c96ee95cada25845527c7ad5b31bc018c667be7de6cdf9480211b73e5e0fc0e1e03a683a80feb2399,0x4e04900c0410144f3ce0e018c1840020605099a3823d30032c4ce03413c1e08c412481b32c810028f486342022205010179b1c44008d375c030cd5d908008055e282051134c40088667900c444ea04000013f960e0680e1a03a083a80f412309),(0x64ed11ab034e6565aa5f6f0a73fb2abb553e90eaf5f2056f4f2ad1a6a7112f3107edc462d825611a42150349a39be3bcbdfa3bf68749fd950e410251758bd0aaed7e1f93ab81b400f6cd22629068e5bc2da9dbde283bbf115009f3b1a197a662,0x46299909050b25a18c71e62a5095c63ecb8f04a3c26b60b927cda532c109201915ade64b3091412042050108b390e3bab9cb9877060097580a090251508bf2aae7571e1ba185a2088a6c00621068c596ada8d9f5a83bbf101009f3a0a197a602),(0xed72aa63cb994444b8dcf183254b4e7cee24db3ad729ab4a1ba98c700af5e5480459e832e1cc5750368c89edf172492ed4565f186db3259850f427f3943aea1f7b1d745054d56ed5059c9e36e00b68fdae413f628aa9c64ad98b04d0b38dd9ac,0x4400b2628be723745844a119668f0ccc9303b92a933d014173710ec9a0c0658c41596832a4cc13563c0629c5d4a2402c44020f584d31651810e10cda143b2c95631f726414156f15141896b3a1182c75a6e53b222aa1c648d9830490938dd1ac),(0,0),(0,0)]
def g127columns : List ColumnInfo := [(32,0,95,0,8)]
def g127autos : List (List Nat) := [[],[101,66,16]]
def g127levels : Nat → Packing
  | _ => emptyPacking
def g127index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g127 : Forest := ⟨127,8,fun j => g127samples[j]?.getD (0,0),g127columns,g127autos,g127levels,g127index⟩
def key191l10 (i : Nat) : Nat := 0xa2d43b28d7001ab368009df79a6668d8a485480048c00a24000002900046192841e000000005078511fa7b8000001d8000000000050332001c2200008044
def key191l9 (i : Nat) : Nat := 0xb5d65558d2140ea31b806b286019a820212fb2e35aa613228a5a077246e6fc20ca1a41bb2d080a9c3e39f318874648000323b01b537426ceae26842215792e4b19e71cc72290229e7cad73d5f333056000d205f83e366a30000000d49821b1f1088000bb771a5c8c0000000000eb0000e0cb6ac6bec3c000c1b800347e18451880000012040006004d1cd8e0000001866e151a0000282800081e2a5e9518b100010bc00000030815564ae0000000000000ba722a1a34000000e6c5a954a6f09e6780014941d61a7112de27d595e7f09e40be3dc9678ab0bf3d70002c438a3dd4912345fe50900b4e481ecbbcceb07786be83e621d46430465b9b583a98309000098f882ae3a444b1d707c001bdad01b2c800179a0001f6d90464c82da1658b094500004b589e042e51604dd58429e06b90ff614389938aaeb6d12bb049522a72f25c09129e0463116174d50c3960b150c0a182d435d81d03dcbc0b346f3525916e494182a5649d22c9002ab560902d0004c5bd2828ce425700001e0842090d9c2ec56f6a2934aac61902201440c3800d7464005040d9808000b00120008008026140608781000c78f2e086830a0c98000580830000a023a002141e004000c001040a00380
def key191l8 (i : Nat) : Nat := 0x18cd14b25011e7225b26001876a3412158c6fc726c2320d6e3243bdd05603f1613ebb0007f7c604089b00125f5892200bf9421800b5e245039f1cf3cb8436d7f2000047800310000002025492575bf0012c00000042000001b8021c00800c01d000c080081
def key191l7 (i : Nat) : Nat := 0x2c
def g191d6 (i : Nat) : Nat := 0x47d6448788a00
def g191l6 : Packing := (1,4,6,0,2,0,0,g191d6)
def g191d7 (i : Nat) : Nat := 0x1021aae2c480c58812165850610304200048200685020d100000000000200100000fce5cec0b2a49f918c877974664f4a45403b36312c2722140f0a0500fd51548d13edd3641903fd51544d03fe92540d02df57305d02ff10305d02df4179dd02bf5819dd02df5819dd029fd819dd02df5155cd019fe885c901fe92440901ff114409019fc8788a009bd849dd039f5819dd02ed6668ce11f56558ce119f47840a11f3a5591200eda668ce00f5a558ce00bb9841ca00fca3388a00fb24484600fd23384600fe22284600
def g191l7 : Packing := (28,3,6,0,2,8,0,g191d7)
def g191d8 (i : Nat) : Nat := 0x850910304081c2440c0e2128f09183458e0d563c424bf1e12406128b1c7846402045834a31022c1244b4112285081c2449f022410c0418818084041a2060210127868c180849614f082043003c28008103c00a001050011a0c10d03085c404064a2030a0610180108a409488504804aab1e40a0610805408d7f063c2499716b62841c098f1800a084818401971629005810a08556544b736241080077f04053c18a8a2824181120efe78c80844603045000e102828008e8b070510443840106263000efe5858a100024042202241d09811e292070e043021810a5c588002801000c0052e2c5001418110006003021810c08516144821810a085042001810afc7897e3c49e14f0a7850604482184f83a8258107f37d67c179c77f77274572070b6f66e16cc6bf6aa69568066b64e63962c61f61a60d5f85e35ce5b95ac59758256d55053b50e4f94d44bf4a247d45843b4264113e43d73ca3b53a039338635934432f3122d52c02b328e27925c24f22a21d1f81db1be1b11a419718217516815b14e13912c11710a0fd0f00e30d60c10b40a709a08d08007305e04903c02f02200d000ffa4c91ffd0548ffe93227ff41513ffa4c81ffd1640ffe83207ff49503ffa2a81ffd0540ffea2a05ff4d502ffae6817fd2340bfe89a05ff40d02ffa2e817fe7740bfe9b203ff51501ffa6a80ffd24407fe91a03ff5cd01ffa0680ffd72407fe81203ff4da00ffa47007fd13803fe89401ff88a00bfceea2dfe774d6febb247f74d923bfcee91dfd7644efebaa27fd45513bfcee89fdd2344efebb207f74d903bfaea81fdd3540eff3ba07f744d03fba4d19fdd168cfee83467f749633fba2b19fdd058cefeb9a05fe40d02fbc66817f41740aff3ba057f5cc02fbc66015fd7100afeba203fd45101f7c8880dfd73407ef19a037f5c901ff20480dfe77407faa2c23fd4d611fea4708ff503847fa81423fd00a11ff209007be44803fc81c01f78ce00ff205007f901803fb08c01fe4da00ff28b007f935803fc92401fe45200ff247007f913803fc89401fe1ca00ff445006de668cfaf2ac67f58ce11f7489007da33803f511401fc84600
def g191l8 : Packing := (100,2,6,5,2,12,0,g191d8)
def g191d9 (i : Nat) : Nat := 0x180327c7c11a70600f8f1304b1c05f0c3c541303017c38f1204e0ef8f13040180df9e0e080325463418a006077cbcf0238c0ef961b3c041381be3e0900df9e30006fcf825f86eb1755933dd9099319085000ff517fd35ff48ffd13ff40ffd02ff00bfd01ff803de33fd847fa00
def g191l9 : Packing := (12,1,6,7,2,9,0,g191d9)
def g191d10 (i : Nat) : Nat := 0x1f3c11ff
def g191l10 : Packing := (1,0,6,4,2,0,0,g191d10)
def g191samples : Array (Bits × Bits) := #[(0x6acfda3c2cb83a92b793db4cbe83faea9cb2634793e21db352fb83fe8df2bc07a86d83614e9e1d6652f73c866931a299021d0d35cea03b8bca899a3ae9b0852968ae39aed598c502d3cc66c95e3918558ba9636cd1546c95b4522b12e41c6251,0x8027018c1220821109402382a0c04040242201142810004800310a01021028020024504420900008134444101889108100844480011218a0808a088000429588a002494484002118004005c4110108908c2000154441190520210a0142200),(0x7913ceb593e8bd03514889e55f4c93639759259376fb3230720c9a865196f27cc74c193b9b758265cc3f7b6a39d891145642471fe1a3e402ed12036d66f3fc532a7d00122732be1cd6f8a0d631223ddb153772d463789a2c383ce02e7842d163,0x88036081c60419a2c82401d04754b2b302101402821d5c654204040641a4c69d42c491108805a675482c4b1a3210132646402113b58224122512010966d1b044833550122312b410427aa086012a6ec1101538c042289a0c282ca02a5842d161),(0x557693cafd0fd9424efb95e75ddf8ed5bd78c8ecb52fa208a8d45cb3574ccaab77d93b1e650b4399e9518160864e914bee471a4d6078d8cd3710b8c5462d299957d5836e24a95a7b253cdb2e6196070b78eaa32a2b4a267149c447650cd138a6,0x10c082401088400012d0c4008000004018ca8080142020182010002082500860100b028600824082a011044180428040210612040030c884904098c2002801191040822880a108c8040449084010010648220108084220210140474504110882),(0x9c642d62a2f2f7ba22bc048df67d49f5212576be5994f8cdc5e270babb8959b792802cb3e87f90d4054ae918d4ab1ce241d9cf541d5d16b72277276810cef58c9e0f2a3137066d66292bcd81a96583d025d9fd03afbb585aa2b81e898b063d44,0x8024093988519a8e002822a41919198600217873085849c0c483198871885081c08060615e498874054ab3104029780240914c50140c132321226228088464808a9608100702c12708ba84812c642a102598ac01a5195852a098180889063544),(0xd23eefb5d75806b89dcda38864b64661c9f5e2babc176a70b2d3a56f26f32e727e31fe7789e6e58a36284c9dbcb30e74d59821a10b67441120e71511dbf31ab50b42210b3baf1a3e4c47734dcff8958cfd1109f7ce27c18a062741ac46d7cd91,0x7413208444084451d48501104604c068b3980408840422121160844600658c78341c18180024668a9220480b8c940760b50821038273441010c51501633a18440140258228a50a1044455344031a81ae1001013e42228188062541a446c1c891),(0x44ee3263ec00331534507b30f50239085a477dc26fc97fafdd3677e1adedabf5a6627a917685fed951e16b05c441608531a6eebab7bf0ffa2c9d6923c000425ae070ded9cbf43ff0702d561449016826463c1cddf881bbc98109fdb0912bda0a,0x5c9601812402000310c10a308504200a188ca4d220b13a418220c4ac1700cc49329049900289169c4a408a09044020043184b638a739649c2011540242004250a0701ac901871eb02048c310010048264632184cec01aac801096da0110b580a),(0,0),(0x3ab08ab4b6d74c50e56bc9651caf5894b179e03465572acbdca5615696769c27053d6dc580568c9318a62a712d4d06df8fcf0933a8a96615b24c8891d85dee28deccf746ecda09546a23c7138dbf2215a9d969340b49504d34d905859a5a4fc,0x8020482e4971b288ed202044508b9ca5050108094844412451461041282e3192c9648008d0242841110660a6538444294c484083188002614b0e00011891a8820d8e45006648e00548a230c32acf32918089829300b41504d204901848a4a474),(0,0)]
def g191columns : List ColumnInfo := [(1,0,190,0,7),(2,0,189,0,8),(3,0,188,0,5),(4,0,187,0,7),(6,0,185,0,5),(8,0,183,0,8),(0,8,163,20,6),(10,0,181,0,5),(12,0,179,0,5),(4,8,163,16,5),(14,0,177,0,4),(16,0,175,0,8),(0,16,166,9,6),(1,16,166,8,5),(19,0,172,0,4),(24,0,167,0,7),(16,8,163,4,5),(8,16,166,1,5),(25,0,166,0,4),(9,16,166,0,4),(20,8,163,0,4),(32,0,159,0,8),(1,32,30,128,5),(35,0,156,0,4),(40,0,151,0,5),(48,0,143,0,5),(56,0,135,0,4),(128,0,63,0,8),(130,0,61,0,5),(4,128,27,32,5),(136,0,55,0,5),(160,0,31,0,7),(128,32,30,1,5),(32,128,27,4,5),(161,0,30,0,4),(129,32,30,0,4),(164,0,27,0,4),(36,128,27,0,4)]
def g191autos : List (List Nat) := [[],[84,115],[117,67,32],[116,83,32]]
def g191levels : Nat → Packing
  | 6 => g191l6
  | 7 => g191l7
  | 8 => g191l8
  | 9 => g191l9
  | 10 => g191l10
  | _ => emptyPacking
def g191index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | 7 => lookupWord 1 3 0 6 0 2 (key191l7)
  | 8 => lookupWord 17 64 6 11 5 2 (key191l8)
  | 9 => lookupWord 68 242 7 13 7 2 (key191l9)
  | 10 => lookupWord 9 46 4 10 4 2 (key191l10)
  | _ => fun _ => none
def g191 : Forest := ⟨191,10,fun j => g191samples[j]?.getD (0,0),g191columns,g191autos,g191levels,g191index⟩
def g251samples : Array (Bits × Bits) := #[(0x7c5b1073c997e37379da30f398119ee6fb6b9ec3f472bcb960b6e16b764eab308775a6f93b85666e9d3190b2b24d642ca5712b6de7ab3f7906c1699135342a691b3ae0a5aa4ef7bb316cf861cfcc30541d6a6cc4992b1a999615c8e8d911c1e1,0x2118206040004a02130d09680103a002090a061080141a8c00302460220208340600a251588102029c90b010225400202065234404234e080480294178042009180840240246b20a0024c060c50410001a48a084882a181106058840c1114140),(0xcce5a5f376b735aeaefe578ced15d32ecca61663a9af3bd1860bc21b19116b79223f9d41251db7915d2d676e62aaa4f819f9d341f91890478f7c179edecb18b88452ff03ce59b2503e9c1117dab8cd95ebc956b7a216470f30e3a2b3ec2d18bb,0x4842cb022293909020208080c0985104462050200a232050248f580a09002349282c0500277025a04229050a00aa2098018840837118b0c40a78400806c358a084123a0140090810bc8810142aa8e601010152222014470a10a222b02c2818b9),(0,0),(0x615f43b7c5899d56d0ed540d07e5651da134ed341e9bc1f74f237fc0ae8a342e74d0d54381c29b89aafb968c73300f2ad24e70d94c925aaf7c71d97b8e42ee34b1eb0d1c78f57307cdbb8ab0333b96f243ce283ea4988c525a6cf93575cb22d6,0x600508638c1a9f0381c44ce96aa5f40532886e32158a42c5402a7e6c4a89343c9410964685c08b09acb0120c353c06229a6c00c94c92de87444159522882ae0499430c1549527146cd2ac810537252985246622c84980c521a4cf835558922d2),(0x743743261165c64a5893c74b56706899b56f313d76fa70640bd59bea9f4cd6cd40c9796a92725dcea2baccf628444b5fc70e36349d152cf473b98c6d967cf8571ea4949a30a5a9a67c52f2db3fa12e66e966315b35ec80fa603e034c2e56ad7c,0x8e228200012500a04432a202145800c8c044118122412020998581138524c38140cb492802205484420a48e00002411d45001410a1402070b13084088559515204a0a28a24a10ca03050168720812c4621201151314480a8603203082a468c2c),(0xf3d9bb1a8ffcdc97c518eaf4c8cf14e122f0fafd99d5fdca7ef0f64eebb658a39d280ab679b66835384c18039df39cc970c09cab32e75b6d986af50aa1e14f67f56dcf6f41924d79e9e39f3990e7fa0a34138f4a5e417d209f607f101fc4fe09,0x9201861738918010c41062040c8818244620088911c0e1638783100880a45083c120082600262524204640020401ded90000982b30080131d06c4002816148a041658f0100904561e8880e0910f0e60220020e2216414120916065101cc4aa09),(0x8c34b489b6743f0cbbb4f14fa7d16d9fa49b993f9ba2b3789eb911d5e1cd7a6f64e2a177140a8013c504eb6dd8b5e7f7e94f5a351463882a81261e97691b96dcefd6ddbc37c1e3432aa0876640524995f6a595fd43d7d81429dbe94302afe942,0x269c30c1984c0e0408d2577d35632830a8c6a4165540daa693102041644d9ca647426045188a80110514e824d9155760ee46136c04410a2a918614976910825e2b85c52c35a0b36b4200852245520814f6b484dd43c398142959c9430287e142),(0x1bb2ab4aa0e85ba9e596de5ec3ce129b01134cce9757f2d674620576a8bd96bf3a893c9457f0a28da9ccac591d7731877093a6c205d64d4c2bcaa6363cd0b55e770f7a466dfb2a9c82572d4ce3aa90cf64d9c30549ce2fe50b809671629a567c,0xd9639e04222012901869c59f133e18908110146a61f169c201c69140019863c2e851098d7d900098988b54119762026501322c440c64c4e0e9086343c860556368a70222d632a1a145321c6e30c00cc44fdf181498e2ec50a809261621a5474),(0,0)]
def g251columns : List ColumnInfo := [(8,0,243,0,7)]
def g251autos : List (List Nat) := [[],[84,115],[99,65],[118,84,115,65],[118,81],[118,84,99,81]]
def g251levels : Nat → Packing
  | _ => emptyPacking
def g251index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g251 : Forest := ⟨251,7,fun j => g251samples[j]?.getD (0,0),g251columns,g251autos,g251levels,g251index⟩
def g255samples : Array (Bits × Bits) := #[(0x9b665c544a8481c32c829a3849d25a0c2e734bceaece0410b1910c9246b692285657c973ca335d593cb00f0546b90059eb43e97a932728851785431870f031165ac8b80393ba6e576270cc58c906b870841734e15dc89803598ab05c2460a6b1,0x104454110880808228020a2041d8002c08600a02808c02009111060244ac12008614a1024802115108904700443200508241c8821224200116051018407029164080a01212302c0942400010c90428108414142154888803090a9048202086a0),(0xf315668af28fdb1ca228365b7ccc05a0011317731e21482f697635c521d4e57b4580944cacd08190116899ef79421d834fcee4e488905930903982805fb1c61927af17aaf49049a676974192f0d0160363a1bd03830701b0dc1f8281c2dc6123,0x83112a82400c43108201140b24040542001210600e014836084820c40800442b4181104024900000902098cc210099010006246088901220003082011981800902040620cc814002101041843090160043212902810201b054050081825c2101),(0x380526282fa13ac851f4c9c505254980d6e8ec3804b3594a769d93b950ebc251b0d8e2a15610b8154799066089743516386914b45de9a6e1e91c2d64aa4bec2945782990b2d68e61aa4d3cd1b24a6ab680984b4c1298da14a63264e421a50a46,0x184000082381184051a442400021c800c760240c008201086414493150c8805030586481420228050588002082640402084818905528808149002d00020c144045280184104604602a043c40824a60b20098024012185a048212646400810a02),(0x96903da21572f2b1f1c959078994a771bc47364121282ac5966e24786e0f6b8886ae49c27124b27b7242ff2e0094e0b4b1b582696d3c94568c371a6b03b30075a8d6353ad9672c0089eb12ba6325f80dd24d451b8459a7c113618d0b812f118c,0x86100cb01034a2a12848198388d4226018030240202c8a411a0a044824066a838a240842212092185a40cf0a0080e094a530c6680a1400448645526011312024a0c7343889210800016b021a61259805924545098441a1c11120810b812e1184),(0xca830c6ee5a1c1ac77b2c4bb013b84b271c7189edce77b42164b82b2ec44ccc2202552493f52e619512b4f09e2177ba801c291327039cbf4fba1fd7ca29d36ceca40c4508827295a1b45be11b7c00687be220f65622167c80c13fe90c415919,0x1282044674a181cc515204830038803270c71014e5265b22464b9241a4004482002443590d10ca0850630203a411b2a000c201185038c3861ba0d078200d6480c204804048212d4a89449e11258006869a220d60222163c80c12ea00c414819),(0xadcb89db333a54791fc5b16de6a74b1fbdaa5224c4caa060c8434905e130b3e50875189fa3aee40ebf67487ce98db2673644923b555505294552488c144494c2312ef3656d2d51ee39b1b44e04f3d3ec4d148000ab72771f011403179f478e82,0xa991884a13221d3803c5e045a0014312e78660240442614040424905201081f109410899826ca6043646807ca808b20b342020284941850001124c8410049440302c118d6904416438b533460072d3ec490080008b50771c0014031517470802),(0xccf1d170b069949f14600d7679a83ea985e068495997ad010287ff4ea745b576050c4fa9e8e0fabd2497448bd27a5aa8acea4ac0268e4d44dc2df9de452a225ad1457b3d721818b9bf9e05034d50ecb938aed67098a522a72856072e55b8d214,0xce85130b040942f1560095449a91aad8dc0e80b5196a18140955b282345b194266c47298868eeb9221d4601c27a00e8acf04a8036004c04cc8c58ecc43a23d68161791d311c0cb9abcc24434d40e8b9388ed67018a522072852072e55a0d214),(0x442aa5b9d884c622461c21eaaaf556fac8da8923687abbfb99c9c28096422e0eb83cb34c1d8918aec8c55d99f53bc2670104934ee2f27258616b2c55a56fa8970e02486406e9b92b5242282d15890d903f02672424a3e96d3ce1d022fa0aa8e8,0x460a679588446000a40a01aa08c414e80818810338389a92898982c08602320ec02091061180118a88016c815113416481048146a2821250206d8051a4632a958802cc600689381b004a400915810c003602652424a380613ce19002e808a0e8),(0,0)]
def g255columns : List ColumnInfo := [(64,0,191,0,11)]
def g255autos : List (List Nat) := [[],[84,115],[117,67,32],[116,83,32]]
def g255levels : Nat → Packing
  | _ => emptyPacking
def g255index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g255 : Forest := ⟨255,11,fun j => g255samples[j]?.getD (0,0),g255columns,g255autos,g255levels,g255index⟩
def key383l12 (i : Nat) : Nat := 0xf8400002630000023000000000000000000b83d5688000000000341000030000000000814000015d0000000210344000018d003b10000000000e080000000e70005c3803500091000000000008
def key383l11 (i : Nat) : Nat := 0x404c001fd7a0dd080d1200990f207c017043e0ac430a491c9aec7438f32422a414035a0e000e6f384202824e3e5491f317a0090ee161490000d0e481ce32000c4b9104c1860ad6100030920000000003c06000000722ae38f1200000035c780290bd08d23d219503209024ec0512fd44dc0985ef07266b48508d728f004824e9809324688ad260642ee33843c9e425582082c2260138002f8f81ac0c0002216a57414583e222000012800202204f00400024f34c01300e78608380c041012080080846040
def key383l10 (i : Nat) : Nat := 0x8a7028008f8208641c25de616202731427f0aa3ea6a9bc18603a40bac46606be46000184a7c7d25a0000000b98af69a264a6b01ac3b3a21709000001146294f5b28f5117b2b2368000000119a0000000503689a2858e10b056a96282c8039064ce4000005a1824c4b68b4a1ca0160003a96c1c5108908a005faaaa16a13000042ba8544116a040004b6aa18802880c23178071841517e2559911705a04117c6495c00000000085d314e242a96a0880000a01fc56687256502c84968668866a1180000003d68390f815a1fa922000012b8020000c2a6caf0234475dcf201fa032887c28e092c47a60725df80221bc02a000007a61e192100d1c1f61f683d817642e40874ab202e012c0cd05141d60b104cb094626909c0000000c0e573a858d7326a6285e00010ac0007468e22e50bc16f60921b5c8f41249001273800322800110cb04e0005728622182280ff076809bc29a93800081a596455d1053c0607cc3a5870000108081400524002801c04219100c0821c60cc13c0c2030a201001e00285000001f020030024000800c08280
def key383l9 (i : Nat) : Nat := 0x6977b1303806491384c288005f480044300b4273a470aef249bb09d0238c000000000000000603688ce51876813ab9e6c881d7b37687df408050502a181c84000606800000000000000424bbbaa9612800409100800346576b8a520800702905aa985610b9a10486080010008502020c0020a18085
def g383d8 (i : Nat) : Nat := 0x7c610014028800000000000000302080140040000000a09b827d78736e69645f5a55504b4637322d1e19140f0a0500cef45d94a2103afbaa93760801f7445d0744d03aaf69017618038fb68a9960d01ad76949760c01af34a89760c01af64289760c01adb6943760801aeb69037608018fb6683760801af94683760801afa42837608018ef690988ce009fcaa9190de009fa68a9944e009deaa99504e009deaa99520e009ee690988ce00be6690178ce00be6690918ce00be6690988ce00bf84a83784600bbc6989384600f749de3384600
def g383l8 : Packing := (25,4,6,0,3,8,0,g383d8)
def g383d9 (i : Nat) : Nat := 0x2dd0028c0601f18c02041010022160ac183c0004580028bb3c71c058816e807460680741c30700441602883bd0180c08009e92a09189248391a905315048c4c0a178c440a1c344e20480c5e3ec8c4124f1f67a1c70097c7d918050801b86cae3f18d8123489e81e3f187030392c68303e84a0683078305e30e0607e38f83c60f060a511f174250341f8c5e031010ee21078c3c161c0cee22050c28801004142c00504800c7c3000f402160a08ae97100120112003c70a082689408970b120030209083000c003000838e14007c610001c70838e1020020212004000023e3ec8cb8e14489e2f1a14a23e23d15c47a2b88f457115cca2f195c5e3ecf438e4f9debbcbf80ec1d2799709dd3b93626add2d9db38e63c8786afd5e3b876b2cad6ca75446864ec9992b24646c8990d60abf57bcf1dd3b7e6bccf98f3075e0b6565abd55ea85452734dc95d24a3b45a858ff9f13c6754e39b9356698cc18a2f85dcb916d2be568a61472724d08e918226438650b3138214370570800a4005ff65c1840f7fa2f442077fd9720d01dfe9bd1080dffa6537006ffd329bc017fd9704e009fe44a2e81ddf6541840f7ea300c2077bd94a2103ddeca51081cff6468840ffb20e89a07fd41844d03def4422681cff6241700f5fa2ec3007afc1761803d7e8cb0c01cff65d8100f7ea2ec08073fe99604039fe44a6e80cff65d834067fd32c1a03bdd8320d019fec4a0680cff64e884067fb121b8033fd9760c01dee9bb0600ef70dd830067fd32c1803bdd9760c01dee4bb0600ef7a65830077da6ec1003bec37608019fe44a6f005ef65037802fda521bc017f5190de00bfc8486f004ff22513802efb2a09c017f90904e00bfccba07007f644d03803fb20719c013fc988ce00bfcc9a03007fc406118027f93108c017f8894de00bfd4ca6f005fe46437802ff32e89c01ff11744e00bfc44a27005fea6513802ff32e09c017f99720e00fec89907005fe64483803fb26f19c01fd9138ce00bfc4c467007f645e33803fb02f19c01fd8918ce00fec4c467005fe64c81803fb46640c01ff11384600fed19c23005fe26211803fe26f08c01ff03784600ff849c23007fc8ce11803fe13108c013bd94a210397f4cb0c01cf7a6583006f73281bc017e9290de00bf88c86f005de65413802ef32a41c01fd23384600
def g383l9 : Packing := (91,3,6,5,3,11,0,g383d9)
def g383d10 (i : Nat) : Nat := 0xb1c029771ece80316e3a8b78f40771ca00d1002da03a69a8d16d01d28d4d3292968b98ba7f8c288f4271a30301042b0c2ce3d9d0c753d16f1a58de8639cbb8c715c8d44b554a1a9a3e0a89a12200921586544f91de7c3c6840c59058fc73e70a427a578082339c40459aa8af185209a7d34148d4cb55354aae60605689f215010071ece816c5e382c02c0800b78f67401b1c150a01655c62e06083462ae3d9d02d06c70541505820071ece801e380c14030a8b4a07c8d48497c63f8e66a4b4202e31fc73a14025b571ece863a00201e95c8d50005c7b3a084978e980d957652718d2b8da90a038f655cc3ed026a4b80d9d0683120b8d0ca07c4503e24b0080e3d9d0c73a100400171ece863a2041f8deb9e05d31c9dc29ad59e194d8397a571169d5a94d53c132d2591c5050edce08cf4b60acc9f89047f075c62859452044c3f83242b025c208114003ff45d03ffd1840fff06103ffe8840fff44d03ffd1700fff05c03ffd37407ff60d01ffc83407ff40d01ffe88407ff4dc01ffc37007ff4de00ffc37803ff44e00ffc13803ff8ce00ffe11802ffa2103fdd1340eff60403bfd83406ffa2101bfd83007fe40e00ff901803fe4de00ff837803fe44e00ff813803fe20e00ffa33803fe20600ffa11802bf61803bdd83006fb60801fda33803fc84600
def g383l10 : Packing := (41,2,6,7,3,12,0,g383d10)
def g383d11 (i : Nat) : Nat := 0x540b1d9a02e3804632e686a85e3b342382008507c4a8582c71cf98063b342397069da95ca003fe81ffc03ffa03ff007ff007fa00
def g383l11 : Packing := (6,1,6,6,3,8,0,g383d11)
def g383d12 (i : Nat) : Nat := 0x11b280e4ff
def g383l12 : Packing := (1,0,6,3,3,0,0,g383d12)
def g383samples : Array (Bits × Bits) := #[(0x22c0d3a3723e453b61b292904161c19166ba4156452239cb2ce776d1285888036922ca069735ba1c39466bb49cb80c880d6801ee650cd2ea8938a452f08d3169a1612a59384753bad95626662c63076161205bac29b905015369815a61884cb1,0x22a042a308281022412222104041018102a0455c0820218028210490004898014122a802062510400900403480940c80084001804506910881200012c0203148e041211030641239500420000c630440212052a0291101014268811220880c80),(0x3e4782180591e1e8ca415c93fb0e30440ddb7b080a80044a5e58703417b0ed0da2975b6df4e0151155ba1024096257dc7280e61c3739c9924483ab0a0d0a407f268250f5cf15b48886f76ba0ccf46838068d8de07060e07838bc1a040b61c283,0x9028018810161088ac0504223081040850928000290004c425070241b00400822080144b0c0241004a20000482053184202c40808184882448102000d0800b3040a404084018c8080110220c214483800898940502040781814120409604201),(0xc3b0d0243e2c92704a6d0bb89a642e3e324709614c855ba1b03c2574c53f0c84bca3b709607618aaaaca1686a79e094292d1a5b2e1a729d1ef4c761d2455891cd68664af136132ce19aaa19e6c55a2caed1460758145348a6cc923aa16a49516,0xc22070243c088a32102908b09820ae3610c20125cc051d809026055084360c62d8a3320940364922a8484682858e00c384d420b061233141a94434152055010c599024a50348105611a2a11e2441a2c2e41460350145348264c921aa12049512),(0x4138264952b1d12493a4452d72585b389605825093cff11edb60090262cf75191c382db2876b8a708e04945dba40fc5c0117030382d504a579e551698e39d387601c521a9a75d96750089c8958b895e01b82b803f01d0be08606741604bc230c,0x1080c0b03b031008084040c42504188060180103100c00a0a40008040890111041009902b010250040410442a404c140103030210c08ca050a00048c0a8c022200c1018d83149210000148108b815200b021800b00809600202141404b82204),(0x7a0c641d50044e150338db871c0d9c6d8b49b017941b1c71c485efc79a14e6ae159b09d8c200cd085276a758cd18f3623c4db7d00870524c281de7f5fe3e2adc1756b294808a0882ea6a1f2df107bc01d0df010f4d40469e2105ef94c107b239,0xd004201450464809021899a3188eb82288483003841b1c31c500f247991664ae92090048c000c90e723223084509b040f48cd45008304046281cf3843e140e8407928284000804822b6a8b24f004a801d0dd010f4440469e21056a80c1079039),(0xcc62da0a5fa8f5e2c996caf343c42faac6de9a345ff56a94813a6425060416282f4d23c281526277465dd835f65817a533b901ad51024edaaa84a94a69219208d911c25be8aad34a7f39eda22807bafd8e8540012ec5ecf42900c6dcd341c02,0x8452d0021128d5c8c9144a91d1c007ab845a00141d69e1982122246c02041428290423d28902225305595421e41c17a5023985a908040a15a0c4800269208200d9018058b1aa90485c38f99a2803baf58c8040010ec1ece00900c4d4d341002),(0xdaef1c77688221978d1e0c4ad4cf460c43747468370c9781a044ccfb808507cfc7550e6f05834be93d3c1e4e94918217a4e0da637baa95002472c84f89f63e421033ad28de7ab208228bfb0281a229d272553696158289b300da2c9976c32464,0x92e959624882001701040c005417432c02544069252c9701a0048cc280a00e56d4150e31071309c931151f4c9213080304e00a4233c09500a002c04d90b29c403071012c5a3a310c128ab91220a221c27244349605808983008a2c9966812464),(0,0),(0x941a1aee99450a81362f36506691ad42486aa7b56b55a36c2710c35afdccd2f0604110c2892f54d343a9228b60c516b3ea6e18394813263b179331842a516d8adc29c7c000c846f164b52014130d4016a078833106127956c94690a3b81ad1d8,0x4120210904c02803268a2402080b401402a07040a01006405204110294490a020401002d0205402c22800a1400c2280a20c04a14813021a0411310009012188c000460020c0069060300020050540108030832102126010c94480229002c198)]
def g383columns : List ColumnInfo := [(1,0,382,0,9),(0,1,332,50,7),(2,0,381,0,9),(0,2,312,69,7),(3,0,380,0,6),(2,1,332,48,6),(1,2,312,68,6),(4,0,379,0,11),(5,0,378,0,7),(7,0,376,0,5),(5,2,312,64,5),(8,0,375,0,9),(0,8,99,276,7),(12,0,371,0,8),(13,0,354,0,4),(14,0,369,0,5),(16,0,367,0,11),(17,0,366,0,8),(18,0,365,0,7),(19,0,364,0,5),(18,1,332,32,5),(24,0,359,0,8),(25,0,358,0,5),(28,0,355,0,7),(20,8,99,256,5),(32,0,351,0,11),(33,0,350,0,8),(32,1,332,18,6),(35,0,348,0,5),(34,1,332,16,5),(44,0,339,0,5),(49,0,334,0,7),(48,1,332,2,5),(33,16,326,8,5),(56,0,327,0,5),(64,0,319,0,11),(65,0,318,0,7),(66,0,317,0,8),(67,0,316,0,5),(65,2,312,4,5),(70,0,313,0,7),(34,64,29,256,5),(256,0,127,0,9),(0,256,23,104,7),(264,0,119,0,6),(256,8,99,20,6),(8,256,23,96,6),(268,0,115,0,5),(260,8,99,16,5),(280,0,103,0,5),(272,8,99,4,5),(288,0,95,0,8),(289,0,94,0,5),(40,256,23,64,5),(304,0,79,0,5),(320,0,63,0,8),(322,0,61,0,5),(258,64,61,0,5),(352,0,31,0,7)]
def g383autos : List (List Nat) := [[],[84,131,98],[101,66,16],[100,131,82,16],[82,129,48],[101,100,131,98,129,48],[100,49,128],[101,84,131,66,49,128]]
def g383levels : Nat → Packing
  | 8 => g383l8
  | 9 => g383l9
  | 10 => g383l10
  | 11 => g383l11
  | 12 => g383l12
  | _ => emptyPacking
def g383index : Nat → Nat → Option (Nat × Nat)
  | 8 => fun _ => none
  | 9 => lookupWord 17 68 7 12 5 3 (key383l9)
  | 10 => lookupWord 57 200 7 14 7 3 (key383l10)
  | 11 => lookupWord 30 108 6 13 6 3 (key383l11)
  | 12 => lookupWord 6 61 1 10 3 3 (key383l12)
  | _ => fun _ => none
def g383 : Forest := ⟨383,12,fun j => g383samples[j]?.getD (0,0),g383columns,g383autos,g383levels,g383index⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low3 : Lower (vars 3) (graphGoal 3) 1 := size_of (hints:=1) (by decide +kernel)
def maps3 : List (Nat × List Nat) := []
def known3 := extendKnown [] 1 maps3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid3 : Known known3 := extendKnown_ok (m:=3) baseKnown low3 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low7 : Lower (vars 7) (graphGoal 7) 2 := size_of (hints:=257) (by decide +kernel)
def maps7 : List (Nat × List Nat) := []
def known7 := extendKnown known3 2 maps7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid7 : Known known7 := extendKnown_ok (m:=7) valid3 low7 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom15 : graphValid g15 (boundsBefore known7) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s15_3_0 : block g15 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl15_3 : block g15 3 0 1 = true := s15_3_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables15 : checkedTables g15 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g15 0 0 0 = true)
  · exact (rfl : block g15 1 0 0 = true)
  · exact (rfl : block g15 2 0 0 = true)
  · exact bl15_3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low15 : Lower (vars 15) (graphGoal 15) 4 :=
  lower_forest (g:=g15) (i:=0) (hints:=8449) (before_sound known7 valid7) geom15 tables15 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps15 : List (Nat × List Nat) := [(15,[]),(23,[32,67]),(27,[16,66]),(29,[65,50]),(30,[64,65,66,67]),(39,[32,67,84]),(57,[32,65,82,83]),(78,[64,33,67,84,101]),(99,[16,33,66,83,100,101]),(135,[67,84,101,118]),(156,[64,81,83,101,118]),(163,[16,66,83,100,101,118]),(165,[65,50,83,100,101,118]),(166,[64,65,66,83,100,118]),(172,[64,81,82,67,100,101,118]),(177,[16,65,82,99,118]),(198,[64,83,100,117]),(281,[65,82,83,101,118,135]),(305,[16,65,82,99,118,135]),(312,[64,81,98,83,118,135]),(326,[64,66,83,100,117,135]),(330,[64,65,82,100,117,135]),(332,[64,81,66,83,100,117,118,135]),(344,[64,81,98,83,117,118,135]),(353,[65,82,99,116,117,135]),(354,[64,65,82,99,116,101,118,135]),(396,[64,81,82,83,100,117,134,135]),(424,[64,81,98,67,116,101,134]),(480,[64,81,98,115,132,101,134])]
def known15 := extendKnown known7 4 maps15
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid15 : Known known15 := extendKnown_ok (m:=15) valid7 low15 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low45 : Lower (vars 45) (graphGoal 45) 3 := size_of (hints:=8965) (by decide +kernel)
def maps45 : List (Nat × List Nat) := []
def known45 := extendKnown known15 3 maps45
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid45 : Known known45 := extendKnown_ok (m:=45) valid15 low45 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low51 : Lower (vars 51) (graphGoal 51) 3 := size_of (hints:=1) (by decide +kernel)
def maps51 : List (Nat × List Nat) := []
def known51 := extendKnown known45 3 maps51
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid51 : Known known51 := extendKnown_ok (m:=51) valid45 low51 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom31 : graphValid g31 (boundsBefore known51) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_5_0 : block g31 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_5_1 : block g31 5 1 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl31_5 : block g31 5 0 3 = true := (@block_merge g31 5 0 1 2 s31_5_0 s31_5_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_6_0 : block g31 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl31_6 : block g31 6 0 1 = true := s31_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables31 : checkedTables g31 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g31 0 0 0 = true)
  · exact (rfl : block g31 1 0 0 = true)
  · exact (rfl : block g31 2 0 0 = true)
  · exact (rfl : block g31 3 0 0 = true)
  · exact (rfl : block g31 4 0 0 = true)
  · exact bl31_5
  · exact bl31_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low31 : Lower (vars 31) (graphGoal 31) 7 :=
  lower_forest (g:=g31) (i:=0) (hints:=8449) (before_sound known51 valid51) geom31 tables31 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps31 : List (Nat × List Nat) := [(31,[]),(167,[83,100,101,118]),(313,[81,98,99,84,118,135]),(334,[80,81,82,83,100,117,135]),(355,[82,99,116,117,118,135]),(428,[80,97,82,99,116,101,134])]
def known31 := extendKnown known51 7 maps31
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid31 : Known known31 := extendKnown_ok (m:=31) valid51 low31 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low47 : Lower (vars 47) (graphGoal 47) 5 :=
  lower_discard (g:=g47) (ci:=(8,0,39,0,4)) (hints:=8449) (before_sound known31 valid31) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps47 : List (Nat × List Nat) := [(47,[]),(61,[65,50]),(94,[64,65,66,67,101]),(151,[67,84,101,118]),(173,[48,65,50,83,100,118]),(181,[65,50,99,84,118]),(185,[16,65,98,83,101,118]),(188,[64,97,98,67,84,118]),(227,[16,66,99,116,117,118]),(230,[64,65,66,99,116,101]),(301,[48,65,82,100,118,135]),(331,[80,81,66,100,117,118,135]),(339,[66,99,84,117,118,135]),(345,[80,65,98,67,84,117,118,135]),(346,[64,49,98,67,84,117,135]),(358,[64,65,82,99,116,101,118,135]),(369,[65,98,115,84,118,135]),(422,[64,81,66,99,116,117,134]),(440,[64,97,114,67,84,117,134]),(454,[64,66,99,116,133,118,135]),(460,[64,97,66,99,116,133,135]),(482,[64,49,98,115,132,133,135]),(484,[64,97,82,115,132,101,118,135])]
def known47 := extendKnown known31 5 maps47
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid47 : Known known47 := extendKnown_ok (m:=47) valid31 low47 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low55 : Lower (vars 55) (graphGoal 55) 5 :=
  lower_discard (g:=g55) (ci:=(16,0,39,0,4)) (hints:=257) (before_sound known47 valid47) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps55 : List (Nat × List Nat) := [(55,[]),(79,[64,65,66,67,101]),(103,[16,66,100,101]),(115,[50,99]),(143,[32,67,101,118]),(174,[48,65,50,83,100,118]),(179,[65,50,99,84,118]),(206,[48,50,67,100,117]),(286,[48,33,101,118,135]),(316,[48,97,66,84,118,135]),(327,[64,65,82,100,117,135]),(348,[48,97,66,84,117,118,135]),(364,[48,97,99,116,118,135]),(376,[48,97,114,99,116,118,135]),(398,[48,65,50,67,100,117,134]),(433,[16,49,98,115,100,117,134,135])]
def known55 := extendKnown known47 5 maps55
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid55 : Known known55 := extendKnown_ok (m:=55) valid47 low55 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low63 : Lower (vars 63) (graphGoal 63) 8 :=
  lower_discard (g:=g63) (ci:=(32,0,31,0,7)) (hints:=8449) (before_sound known55 valid55) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps63 : List (Nat × List Nat) := [(63,[]),(95,[16,66,101]),(159,[32,67,101,118]),(175,[32,83,100,118]),(183,[99,84,118]),(231,[16,66,99,116,117,118]),(317,[32,97,82,83,100,118,135]),(350,[96,33,99,84,117,135]),(359,[16,82,99,116,118,135]),(366,[96,49,116,118,135]),(371,[98,115,84,135]),(377,[48,97,114,99,116,117,118,135]),(429,[80,97,116,134,135]),(430,[96,81,98,83,116,134]),(441,[16,97,114,116,101,134,135]),(444,[96,113,114,99,84,101,134]),(462,[96,98,67,116,133,135]),(492,[96,113,115,132,133,134])]
def known63 := extendKnown known55 8 maps63
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid63 : Known known63 := extendKnown_ok (m:=63) valid55 low63 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom111 : graphValid g111 (boundsBefore known63) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s111_6_0 : block g111 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl111_6 : block g111 6 0 1 = true := s111_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables111 : checkedTables g111 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g111 0 0 0 = true)
  · exact (rfl : block g111 1 0 0 = true)
  · exact (rfl : block g111 2 0 0 = true)
  · exact (rfl : block g111 3 0 0 = true)
  · exact (rfl : block g111 4 0 0 = true)
  · exact (rfl : block g111 5 0 0 = true)
  · exact bl111_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low111 : Lower (vars 111) (graphGoal 111) 7 :=
  lower_forest (g:=g111) (i:=0) (hints:=16785665) (before_sound known63 valid63) geom111 tables111 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps111 : List (Nat × List Nat) := [(187,[16,97,66,83,100,101,118]),(190,[64,97,98,67,84,118]),(215,[67,84,117]),(222,[64,65,66,67,117,118]),(238,[64,65,66,99,116,101]),(243,[16,66,115,100,101]),(318,[64,81,66,83,100,118,135]),(349,[80,65,98,67,84,117,118,135]),(365,[48,65,82,116,135]),(378,[64,49,114,67,84,101,118,135]),(413,[48,65,50,67,117,134]),(437,[65,50,115,84,134]),(455,[96,98,67,116,133,135]),(476,[64,113,66,115,100,133,118,135]),(490,[64,49,114,99,132,133,118,135]),(497,[65,114,131,84,134,135]),(504,[64,113,130,67,84,133,135])]
def known111 := extendKnown known63 7 maps111
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid111 : Known known111 := extendKnown_ok (m:=111) valid63 low111 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low119 : Lower (vars 119) (graphGoal 119) 6 :=
  lower_discard (g:=g119) (ci:=(4,0,115,0,5)) (hints:=16777473) (before_sound known111 valid111) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps119 : List (Nat × List Nat) := [(119,[]),(207,[64,65,66,67,117,118]),(380,[48,113,66,84,101,135]),(414,[48,65,50,67,117,134])]
def known119 := extendKnown known111 6 maps119
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid119 : Known known119 := extendKnown_ok (m:=119) valid111 low119 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom189 : graphValid g189 (boundsBefore known119) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_6_0 : block g189 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_6_1 : block g189 6 1 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl189_6 : block g189 6 0 3 = true := (@block_merge g189 6 0 1 2 s189_6_0 s189_6_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_7_0 : block g189 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl189_7 : block g189 7 0 1 = true := s189_7_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables189 : checkedTables g189 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g189 0 0 0 = true)
  · exact (rfl : block g189 1 0 0 = true)
  · exact (rfl : block g189 2 0 0 = true)
  · exact (rfl : block g189 3 0 0 = true)
  · exact (rfl : block g189 4 0 0 = true)
  · exact (rfl : block g189 5 0 0 = true)
  · exact bl189_6
  · exact bl189_7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low189 : Lower (vars 189) (graphGoal 189) 8 :=
  lower_forest (g:=g189) (i:=0) (hints:=536879876) (before_sound known119 valid119) geom189 tables189 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps189 : List (Nat × List Nat) := [(189,[]),(347,[65,66,115,84,101,118,135]),(486,[16,66,99,132,133,134,135])]
def known189 := extendKnown known119 8 maps189
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid189 : Known known189 := extendKnown_ok (m:=189) valid119 low189 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low250 : Lower (vars 250) (graphGoal 250) 5 := size_of (hints:=1366507616) (by decide +kernel)
def maps250 : List (Nat × List Nat) := []
def known250 := extendKnown known189 5 maps250
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid250 : Known known250 := extendKnown_ok (m:=250) valid189 low250 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low127 : Lower (vars 127) (graphGoal 127) 9 :=
  lower_discard (g:=g127) (ci:=(32,0,95,0,8)) (hints:=16785665) (before_sound known250 valid250) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps127 : List (Nat × List Nat) := [(127,[]),(223,[64,65,66,67,117,118]),(247,[115,84]),(375,[98,115,84,135]),(381,[48,113,82,135]),(382,[112,49,66,115,84,101,135]),(415,[48,65,50,67,117,134]),(446,[112,81,114,83,100,134,135]),(478,[112,65,114,67,100,133,135]),(493,[80,113,50,132,135]),(499,[65,114,131,84,134,135]),(505,[64,113,130,131,132,133,135]),(508,[112,129,66,115,84])]
def known127 := extendKnown known250 9 maps127
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid127 : Known known127 := extendKnown_ok (m:=127) valid250 low127 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom191 : graphValid g191 (boundsBefore known127) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_6_0 : block g191 6 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_6 : block g191 6 0 1 = true := s191_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_7_0 : block g191 7 0 13=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_7_1 : block g191 7 13 15=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_7 : block g191 7 0 28 = true := (@block_merge g191 7 0 13 15 s191_7_0 s191_7_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_0 : block g191 8 0 7=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_1 : block g191 8 7 61=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_2 : block g191 8 68 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_8 : block g191 8 0 100 = true := (@block_merge g191 8 0 68 32 (@block_merge g191 8 0 7 61 s191_8_0 s191_8_1) s191_8_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_9_0 : block g191 9 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_9_1 : block g191 9 3 9=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_9 : block g191 9 0 12 = true := (@block_merge g191 9 0 3 9 s191_9_0 s191_9_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_10_0 : block g191 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_10 : block g191 10 0 1 = true := s191_10_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables191 : checkedTables g191 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g191 0 0 0 = true)
  · exact (rfl : block g191 1 0 0 = true)
  · exact (rfl : block g191 2 0 0 = true)
  · exact (rfl : block g191 3 0 0 = true)
  · exact (rfl : block g191 4 0 0 = true)
  · exact (rfl : block g191 5 0 0 = true)
  · exact bl191_6
  · exact bl191_7
  · exact bl191_8
  · exact bl191_9
  · exact bl191_10
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low191 : Lower (vars 191) (graphGoal 191) 11 :=
  lower_forest (g:=g191) (i:=0) (hints:=536879361) (before_sound known127 valid127) geom191 tables191 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps191 : List (Nat × List Nat) := [(191,[]),(319,[65,50,135]),(351,[64,65,66,67,101,135]),(367,[80,81,66,100,117,118,135]),(379,[81,98,118,135]),(431,[48,65,50,83,100,134,135]),(445,[48,97,82,134]),(487,[16,66,99,132,133,134,135]),(494,[96,65,98,67,132,117,134])]
def known191 := extendKnown known127 11 maps191
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid191 : Known known191 := extendKnown_ok (m:=191) valid127 low191 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low251 : Lower (vars 251) (graphGoal 251) 8 :=
  lower_discard (g:=g251) (ci:=(8,0,243,0,7)) (hints:=1358970881) (before_sound known191 valid191) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps251 : List (Nat × List Nat) := [(251,[]),(254,[32,67,117]),(471,[16,66,67,100,133,134,135]),(501,[16,33,50,131,100,133,118]),(506,[32,49,130,100])]
def known251 := extendKnown known191 8 maps251
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid251 : Known known251 := extendKnown_ok (m:=251) valid191 low251 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low255 : Lower (vars 255) (graphGoal 255) 12 :=
  lower_discard (g:=g255) (ci:=(64,0,191,0,11)) (hints:=553656577) (before_sound known251 valid251) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps255 : List (Nat × List Nat) := [(255,[]),(479,[64,65,66,67,133,134,135]),(503,[16,66,131,100,101,135]),(507,[81,130,118]),(509,[48,129,82]),(510,[128,65,130,67,100,117])]
def known255 := extendKnown known251 12 maps255
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid255 : Known known255 := extendKnown_ok (m:=255) valid251 low255 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom383 : graphValid g383 (boundsBefore known255) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_8_0 : block g383 8 0 23=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_8_1 : block g383 8 23 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_8 : block g383 8 0 25 = true := (@block_merge g383 8 0 23 2 s383_8_0 s383_8_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_0 : block g383 9 0 9=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_1 : block g383 9 9 75=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_2 : block g383 9 84 7=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_9 : block g383 9 0 91 = true := (@block_merge g383 9 0 84 7 (@block_merge g383 9 0 9 75 s383_9_0 s383_9_1) s383_9_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_0 : block g383 10 0 5=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_1 : block g383 10 5 16=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_2 : block g383 10 21 20=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_10 : block g383 10 0 41 = true := (@block_merge g383 10 0 21 20 (@block_merge g383 10 0 5 16 s383_10_0 s383_10_1) s383_10_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_11_0 : block g383 11 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_11_1 : block g383 11 1 5=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_11 : block g383 11 0 6 = true := (@block_merge g383 11 0 1 5 s383_11_0 s383_11_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_12_0 : block g383 12 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_12 : block g383 12 0 1 = true := s383_12_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables383 : checkedTables g383 12 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g383 0 0 0 = true)
  · exact (rfl : block g383 1 0 0 = true)
  · exact (rfl : block g383 2 0 0 = true)
  · exact (rfl : block g383 3 0 0 = true)
  · exact (rfl : block g383 4 0 0 = true)
  · exact (rfl : block g383 5 0 0 = true)
  · exact (rfl : block g383 6 0 0 = true)
  · exact (rfl : block g383 7 0 0 = true)
  · exact bl383_8
  · exact bl383_9
  · exact bl383_10
  · exact bl383_11
  · exact bl383_12
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low383 : Lower (vars 383) (graphGoal 383) 13 :=
  lower_forest (g:=g383) (i:=0) (hints:=12901687553) (before_sound known255 valid255) geom383 tables383 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps383 : List (Nat × List Nat) := [(383,[]),(447,[65,50,131,84,118,135]),(495,[80,81,82,83,116,133,118])]
def known383 := extendKnown known255 13 maps383
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid383 : Known known383 := extendKnown_ok (m:=383) valid255 low383 (by decide +kernel)
def hashdeadl14 (i : Nat) : Nat := 0x4592c8500000000002800049a6c68a83340e9800000aa00684000000054a001bcc7001e180000682000000000000001d46a1840000003a00000001c
def hashdeadl13 (i : Nat) : Nat := 0x301a0007b2f00e0aa2992094818000e2e0000000269e056438000000000d33e40e4a200074d00000000000003b10001e0240a9bd45d962582900000000000001430001e1400000fc03b84a000614e69108a1108000810000d04c9d0000000408800000160f24180010b9d040003080001e0c000000000001997f401183740ee12000000000080d312c00102c00000000012070000000001d35000308c000a4c0001b30000000cb3800183000070f0000001abcc008002c8cc133000000000000000000000020b000000064ec0a00000f8000cc5000105d8204160001a38001c1c467309c000000a7700000016de30f80000008380b08e000d3001
def hashdeadl12 (i : Nat) : Nat := (if i<1 then 0x7b02c3200425d610a000042a0327300000000106b33757005e04600006037d811679d009461963480703e1077f067f2582384275d80a540a20109b59b4006305d00000000ab6dfb0bf59ec084c806986b30597776440b146b100c50a956520000878e0000747c463e108bc029e7600000395ef090d06800000000f0550000d0b1e4af00000000f324d141840ca4380000000051505017000067300000e779907b0000e77730641201ea62a089a48ff0924111e9a7a041b2a180aee462f29d9b47b01eb0427030e02a5973605b9086f08d5081d04bb014363000006038c0b6d110106cc731308e0023a07fb1305601ba1839b4c088a10b88011043e427e75a600831464016903d3ba52b1ec095000ec050b011b0730478f11a0000755e331ef63db004a00a000069a91680e225f60f90092a9d0000764650a40000c591f95ac03baa33c5a1283d11871a6d2772c01c1057280f201f5012328b908232a5505e000fe02b507cf0809817c267c05c9528506d997696872194b206264030ad402d007d586d7228701d30605840f67838625a51443ce034d47ed45f704cb08730a1794e1252000070330000b56f0000b0b4000000000000a842e047609d406ae26b67b08a4de12aa0a34019000000000000b664342c50b50000c0af924dc9aa401870366002b26d00000000841e0000000060986614000000000000783ae10d980ee051d0ab4022a615808f0000a0832619a148d81500007000e007d616b032d01b483f163f00104028276b2015141030631049a027580cd0a7a05ab977802fb09ff07a97899053b0a80816e83be0790a1b809b8b460a4f0000178b0000847be03cf139a1170000b07850b3605408416262696b908af0aa7b1f5b446070d024601a42492101d496f4b4e035922127ab0000e18600008284831c00440000f031500310656013b071b045b25b4113766b5b4c6b0800008291b4888a50000000000000e38b0000225eb04d807230618425c0b097ae226f809e00000000f00d93480485e88728040000b11c3039204e9432711f445c905f004a300b97ada05680211292f09a7b1a696f3106704f19748066703f00000204d074ba20a118f025458794596091a06f000065946020913b783e342dd08c819b5b452076c21dc075e0991a4a183c3b19d7a750a68058c8379643a487b408d0523762d062b422e0b2d47fc0ac224a46231a5dca3b6069a4390000768a5433e07e0000da410b00003102090604000a010a1f88080000080d030b0c310304001300040113030203141f0c0001000232030b0801010a010007110002020208010605020401010119010b0304070203070506000210070d110100150b0a0504051d050002020b05000c0402003d0e1500260200020108040b03090500060204000d0602010100180501000001030f04 else 0xe0a0512830933085c048e216509713746026a02ec09cb040548400000268f701103ac254729fc29e8096145a39ab47552144806e00019612b7b4491ea44bc1)
def hashdeadl11 (i : Nat) : Nat := 0x5b144463e05aea749a36008e0000f05f008fc82400000000057a08357304bb42c02b0000807cd1701823000007095811411b96631031e07218223334c77b980e8010305dd000180820521064ca3ef0420000409b626cd483a833f03ac022e048a008f80a513f0000db73410f3393ca38834018881012b081c465a02c6142704300002631809700000000715300007115b00dd054b2886014000054161b183099000000000129f0870000a24110110427972915960000477d5b457113518aa01a00007134a023d08a1053002d678ef06b604a6076520f5468b025698fe62d5060c1370000e07eb793c95be02a510198285417000000000000000000005b72220ea00f9098e036e09602120000503908396112556c56084a3a211d0342f0784635707b4293308d0624205556235211962a72516903a0190235010e7765e07d5784f16feb3c248834149073d088b0134091f720f0803275f0052809446ed494b01b1b0305939136b20cf495111aba390000db890950e9807026e609a0205015880ba66b8778d4967988f077f007110cd289d0160000e278401d0000000000000000f032027400000000a08c6209804c4030102eb368a33f3b1d798e0000538a70215061a44e228300000000000000000000d01710838075e4517067406f00000000609a00003253a089a4002093b00a8125000090790000c0599583180c00000000c0411830f1160047224900000000906992725046700b000050511a67544b00000407c35bb06d0000504d3821ca470002762e0000cb1760948827b10a603b4009e06552019464444f9688a0286169097ab82524185057db2feb3d000e6303670ac01e70822426b090d664c05cf764008be03c365d6a2549347068706a71244461f086277c5780380d698dd120b27c20626037d807f403502fe1110000ea6e5071301cb0388044704f411c809595011003b20deb1a98372208b0561092820a91190049704bb03ec070670890335001a03f64504063613c50294b430832441aba46e146c8120193598c103df8314066401fd460e0745084044c100c7760b24b824f4006205b0000563070507a7c9058000000006a440000506e3040e97d006cd027646a6207807fb0450138e56fa018704e8482e0356085662f762c5b3be05eb81f1004f836000000000000000046203a6ac89692730000b034807a613d00008145702433536a79b0407805012a04e80082c50a0c0e782286421a0e4c00400004833a1491a02243880c0851202004211c6408c1835c192e081800c39681005000c04e408002001860c34c8040000000400008087400400100892c38005148410524200800478080001438126000000020022
def hashdeadl10 (i : Nat) : Nat := 0x1c05302000382d2ecf474c3a08f618409ea54931a0a2272b385214e934380040192451090d15cc0564307983441ce005970002c06068f08a82680cc070001a2c5d4a1440400018207150002808001022205d856c41e1700072d518800084a2900000a334a12801820030b1a27
def hashdeadl9 (i : Nat) : Nat := 0x202e0
def deadd8 (i : Nat) : Nat := 0xa24b7baf6624ad253281df927589c4d52540d02
def deadl8 : Packing := (2,6,7,0,4,3,0,deadd8)
def deadd9 (i : Nat) : Nat := 0x17a6100d01602e1f830400f202c200003405840f980801c0010720e8006a183c001d000f8007c00200001509fc5a0b0071b79b2bc5ba99429c459e8d258238d84a14078280a00a7becc495a4a6503c6fdb66689a4d50287fcbc661a544d029ef9c6aed1840d02bed9c626d3540d02ff49184d52540d02ff489c4d52540d02d7f11826d1540d02ffc1184951340d029f6cbc4a1354950195fdc7aed2564d01ff49384d52540901ff61384951540901ef4935496aa40d02df49b54951340d02f7493549503a6502bf62cc4951540901ef6125456aa40901f7612545502a6501fb61284612545600fbc1284612344e009dd9c7aed258ce009ee9c6aed1888a009df1c7aed2584600ff42558ce2284600
def deadl9 : Packing := (25,5,7,1,4,9,0,deadd9)
def deadd10 (i : Nat) : Nat := (if i<1 then 0x2693540b3fecd1349aa055ff26d1a4d502cffb30d2a26815ffabb4610340bfec8c26a81a05ff626d3540d02ffd23092a06817ff1184550340abff5da6b4ca059ff4d5a1a65029ff9569426a80cffdb8aa9354067fed95549aa03fdb4a13549501affb7092b2680e7fda849593407bf69424ac9a035ffaed2564d01cffab15532680e7fd25aa993406bfedc26ac92035ffaed3564901cffab0d1b2480e7fd38aa9924073fe9ad54c92037fe6e13540901fef2b09aa0480ffd9384d502406ffd5da6a81203ffa4e12540901ffe2708aa0480f7f95864d02406bff5da714ca03df74e135a6501affd769ad3280d7febb49699407bbe9aa4b4ca035ff6e123a6501efda5091d3280d7fdb548e99406bff5da474ca039ef495a4a65038ffb63553308167f9b0aa998408bff5dd54cc2053bf6daaa461028ffb6a4d2268157fabb6610340bbf4cc24a81a055fe26d1540d02cff33155206816fd935aa90340b7f492d5481a057f66d51340d02ff924a89a06816fdaaa44d0340b3fcd42074ca05df64d503a6502efd24a81d328157fabb40e9940bbec89a074ca059fd461a1a65029bfb6f5524a80c7febb6a1934063fedc554c9a031ff6d6aa64d01cf7b695532680c7fdb2aa9934073fcd8554c9a031ffaeda8649018ffb6ad1b2480c7febb68d92406ff55da4a81203fda4d52540901fee34a8aa0480f7e92564d02406bfd5db2681203bfa496aa40901dfe22b5520480e7f993aa902407bf492a054ca03dfc45502a65019ff36755251004ff9b1aa928802ff55da5092c01efa4a11849600dfd2515524b007f692849515803fb88c24a8ac017deaed2545600def55492a2b004ffabb6a123802ff55da5091c01efa4a11848e00dfd25155247004ffabb6a1138027fc55a5089c01afe6a12844e00bfe5768c227007bf128461138027fd5db4a89c01bde6952544e00dfe23155227004ff9b8aa9138027fcdad5489c013fe6caaa44e00ff925091a27007fd11848d13802fed5da4689c01bf6aa92344e00bfb57692c67005fdabb45633803fac92a2b19c013feaeda844a009ff370d2a25004ffabb695128027fcdc346894013fe6d5a344a009ff576d1a25006ff1a844d12802ff95da2689401bf66963344a00dfe22755225006fda33aa912802ff55da71114017faaed1888a00bfd3709ac45007fc9384d622802ff55da6b114017fa6e11388a00ffc23089c45007bea8844e22802ff4daa27114017faaed1388a00bfe5769c423007fd1384d611802ff95da6b08c017fcaed2584600fee26a92c23005ff1b848e11803ff09424708c017fc6d52384600bfe57691c23007fd1588ce11803fe89446708c01ff44963384600ffc27111423007fe13588a11803fa49aa4a81a05fd849515409019bf36f5524b007bd2888ce11803df14444508c01ff08ce2284600 else 0x4000888405e986c113905805080340b02e1f06087905c2003f080d05c2010004400c0288128f50060048004020800804100127c503a3f6c170230c990618643002074409038882341900e30020304004060800870140c00228180045c08224a09086c45817020801a183810008ad48702001100108e2b0c1c0800456383810230b0200117dff6de0be2c10281f00a20021f8a108140c707c503e3f8bed83901520010dd505020c988c1183426000e000e00086905c20a40d058002020340034003c1834002fd2040bdb798060306e1b00c84f01a5f8a10bc3024202bf0c090605c00880505210010fc506e1cc0693effc5f6de600097e28190cc11092183f1414080603412860a40cc6004380038003800340034003c003c0020e00107000f000801c0020e00100f78ee2192287800ec3041c003c00361820e001f8a1e001e001e00100000b0411ef1dc4377ae886cc5917b60fc50f000d8e083e2840000016a420f6c1b1c100000b521002c30416383f1420003e284000100c4aca220cd523db61a02c91b20b40600a0dbf169c61a02c9f6de60578fe2fb6f303f8bedbcc0fe2fb6f303d0acfaceacb9c93c83c68c63c53c38c1dc02bd1bb6b9bb96b70b4ab24b09aeeac8aada92a77a5ca41a31a169fb9eb9e69e19d19b69a698b97096094593591a8ff8c38a889887284c81b80b7f07bf7af79f78f7747597497397297197096f96de6b867c64b62560a5ef5df5ae5725415315164fb4d54c54b54a549548547546545545044043b42b41b4164114013fc3ec3e73cc3a639639138137136135c34c33c32c31c30c3073022fd2f82e82cd2b229728727726725725224223d23823322e2292192142041f41ef1ea1e51e01d01cb1c61b61b11a119118c18718217216d16810009807204c026000affd7692d3281defdb6)
def deadl10 : Packing := (156,4,7,5,4,12,0,deadd10)
def deadd11 (i : Nat) : Nat := (if i<1 then 0x86120d08111f407ad1db072b1c206d11ab867718d8613174859115b85231388497118042910183c50e603570c082b709d822b07a8195055010902a80410003ffd1849503fff6692540fffd2546503fff4613540bffd9a4d502fff2693540bffd1a4d502fff4619340bffd3546502fff4d69940bffd9a4e101fff6a135407ffd284d501fff4a935407ffd9a4d501fffaa935407ffd3849501fff4e925407ffd9a49501fff56123407ffd9a48d01fff56193407ffd2864d01fff49593407ffd5864901fff4e192407ffd3564901bff6a11940f7fd9846503dff6551940effeaa46503dff4a51940f7fd25a6503bffaa99840b7fd1a66102dffaa99840b7fd9a46102bffaa91840bbfd9846102dff6619340affda564d02dff6559340affeaa64d02bff6951340bfdd9344d02ffe6a10340bff99840d02ffe4610340bff9a540d02ffe6550340bff91540d02ffe4690340affda846502dff6611940affda346502dff64d1940bff90346502dff6629940b7fd93a6502ffe40e9940b7fd18a6502dff4d69940b7fd13a6502dff66935406ffeaa4d501dff66925406ffeaa49501fdf4d525406ffda864d01dff66193406ffeaa64d01dff561934077fda864d01dff4a1934077fda564d01dff495934077fd2a64d01dffaa993406ffda864901dff66192406ffda564901dff65592406ffda364901dff64d924077fd3864901dff6a1924077fd3564901dff68d92407ff95840901ffe4e102407ff9a840901ffe66102407ff93540901ffe69502407ff99540901ffe68d02407ff99340901dff4e2994077fd35a6501dff496994077fd23a6501ffe4e928803ff91a4a200ffeaa928803ff9a849600ffe46125803ff93a49600ffe46925803ff92845600ffe4e915803ff92a45600ffe6a123803ff91848e00ffe69523803ff91548e00ffe46923803ff9a844e00ffe4a113803ff9a544e00ffe49513803ff92a44e00ffeaa913803ff95844a00ffe4e112803ff9a844a00ffe4d512803ff9a544a00ffe68d128027feaa661029ff2693540a7fc9a44d02dfe6610340bfd93540d02ffa4950340affaaa40d02ff644d0340a7fda8a6502dfe40e9940a7fda3a65029ff6869940a7fda864d019ffaa9934067fda8649019ff68d924067feaa64901ffa49502407ff11540901dfe64d02406ffaaa40901dfe40a99406ffaaa4a200ffa4a125802ffaaa49600bfeaa915803f792545600bfe6a123803fe92848e00bfeaa923802ff9a844e00ffc46113802ff9a544e00bfeaa913803fd92344e00ff649633803fd9158ce00bfe6a112802ff9a544a00bfe68d12803ff11344a00ff68cd12802ffaaa44a00ffa4e222803fe91888a00ffa4d622803fe91388a00ffc4e211803ff13584600ffc49611803ff123846009ef6929940fbea8888a00ff48ce11803fe22284600 else (if i<2 then 0x6718d1b071686b63b38c6ac837ab208143ea5f4a804c20460a84911c7405186a093027a82ae19d57d066c694fa70dcc0ac4ea478ce31a1ecaeaf303c8c241ac2f19b38c69c83fbee47302190238ea2305424c6856399d2085637d12388c0c16cbeff1d208076416c80b40c0049e29d5208144b23f46802b201800c183275231bc58d5919c2ba9ed854030806003067bf9c352078df64634afd056e600c20020b418eaf319c182b832c8683382f1c2de703e3ac80ac412003efc19433aad06707f7f38754282036168bdf159a0ce09fa590158824f17a919786904bef86bc33ab209458f7dd8e39c8904deff5232b9120958e0b701b7e8611b1e288d8776dd9609e2b1c2f1582105b80098e0b90124824976d090cd009250909820be81c002d484d8f144c3068ea08444c12222609117812260911961224208de83785dd4e900b63480dfc5edb981b80c307224fbfd4f301f09477d2a0d202e2010188cddb353cc69017202256222f7fb60add5a80164f6c116903054660bb98d200c6e0e18f8afa73037818602100ed9a0d20beff8bdb752d00186f7fc5ea78e6e01e33bfe2f534770c056718d202388c2401066f7fc5ea68ee1b388131a6862ef8df646718d182bf7fa963ac8ce31a3fbfe2f6dd4f31c70187010d8f7c2b7561a05a04ce121581816fbfdb3530d74005590a1982b682c8ce0be2f6dcc0184f14410307c705b875e98d59067d2d5c686717058176d8d1b06f7c92f17b6e602d3634e457030b7007d2a0b20be2be9500fdf0b7b6c68d029b1803bfe2d415c1bc57d2a01fbfc3600ead415c1bdf363c5c6a8eae0d8d3915c0fdfe0b00ed9a9a81c83fbfc3600ead40dc1ba9e3b0e77f1ab22b839c4d4e356457053ab00682c8ae0bdb341640fdfea700682c8ae0dd49c58d1bc4ea782c02c87d1a03753c751d873bf64634dc23dfe0a86c03b6755a03fbfd4e0164340dc1a82ea786c03c57d1a03fbfc36015c3aad01bdfe3a8ec3ab86a71a7211eff5380570d03906f7fc5edba9e1b82040ec751d87590fa7538d71ddc2586a198ec1bdff16b8ea71ae195efb915c7ab8d74068ed23878d423198bda2f18b3a2a189fa24788e221f881a1e387521a785ea14384820fd83ba0cb82a2071816203f8099ff97ee1f8b7d29f137b21e9179b9e377829ddd76c1d8d7581d3373c9cb17239c6170f9bfd6f41ba36e01b536c99af96b31a9f69c9a4568619f5665990f63618ab610981f5f517935dc17435c0969959b163558495c7566954f54b14f552f949151914374f393a14ce130b4b2929349c124347e11cb46c9185456112143a90a941c9063415103b4088ff53f70fc33ea8f9b3e30f7d3d68f4b3cc8f233c50f053bd8edd3b38eb53a70e8339d0e5b3930e3d37a0da73570d2f3368c7b3160c0d2f30b952d50b132af8a3727d89ab2580901226 else 0x6c244e0445e2e80648bc5050262048e47300a0565ed8f60346f5d8ae98260a0c0068580a0c27015b807c906026158e08c030604c2b2a82103cee10cc378bc503c5a1a381a3a2d03cb121b082409e29104f14d80b00b29b02601632490481068e0401093981802127303093987200a0aca00c1820060c1003060ba9e62b81ec8b40d15c753cc0a26ae1d5e606624740ac47cc0483c9bdf72398ae02b28b1eff6cec705e2c44719c65bd0520ccbd4b702a0c67030651f4282f8a37f6c0f90083dbc507c95c01a2901847d2a015c7efbab500764fd1d5a800524460a84613d40171bdf12bb67568e07cc1703e060df4d22a00b883dd40220c2777c2ed22a06e0defe90110884fd1d5a800526915008831e748a802e219d5c0560f91f4ea40c1509ef89ad00884fd0566800c25702b3400611df1500c10c813b1c0f00a44001e0b8625494a83ec3b7532876c0fa40c07c018307cf7fb66a40f0d782d231a682c8a82a1e8185ce3c519b1a206a008183e7be5a8cd9c5ab50287af14281809827bfc7))
def deadl11 : Packing := (183,3,7,8,4,14,0,deadd11)
def deadd12 (i : Nat) : Nat := 0x226c48bbfb654c3991828d28cddfe2ea731865c0891b87a0bb538ea405a3487b1d9bfa906e3a90b8064694310477f6ca947523051a4f7f6c2ed4a3a91828d23bfa90b0351c15a42e0191a577f8ab8d4e631c0c3f7e91b6d4c6b1c0c3811c4dfe2ea51d869c41234a020c7bed54772271048d2408d8efaa71cc89c4123490277f528e4932271048d27e9c5d4a830c011d1fe8c8d4907400c377f8bb6d4e1b04223bd3538ea46e23461177f6da950523047efedb538ea4608191a477f8ba94761a711a3f7f538e644e0191a3f7f5398d032019383963e9c516e8018413c39e9a98d63991b83b6205dfdb2a635a0646093df6ac6b41c816ae0f00efedb52a0493230488077f8ba95061970704f7f531ac732112b842091d02eff176da98d61b04a4140bbec8db6a6358ec1250d06eff1571a98d6830c994a8fd8b08517fb7ae74f70b6c76686125bc5665224e74a34684243d739334f30b2c728322d1e919c15810b0ac056000ffe92a07ffd1940fffb30817ff46102ffe9aa05ffd9340bffa26817ff46502fff4ca05ffd38407ffa6a80fff49501ffe91a03ffd93407ffb2480dffa6503bfecc205ff90340affd32815ff64d01bfec9203ff902406ffd3280ffe4a200ffc92c01ff915803ff247007fe44e00ffc89401fda33803fd445007fc84600
def deadl12 : Packing := (32,2,7,8,4,12,0,deadd12)
def deadd13 (i : Nat) : Nat := 0x22dfc5b6a90e86821a4efdb54c724410d1f7f16a63a18e01069005bf8b6d52351d0d049cf924d00ffd03ffd02ffd01ffa00
def deadl13 : Packing := (4,1,7,5,4,8,0,deadd13)
def deadd14 (i : Nat) : Nat := 0x17e2b6526070604013ff
def deadl14 : Packing := (1,0,7,2,4,0,0,deadd14)
def deadsamples : Array (Bits × Bits) := #[(0xf854605d026923a5a16008862c9d18d42fd85e54d221898f1e440284a107a02910c3e03c06c40d2642ca74f54627022c11e389d9b43b30c961ca72386ce81500aa210d1ba1a121108a6c99348979d054ac200727ac054c0970110780155ad581,0x6844620d0040231585204884208800c4270824141201090814040082a10700282003e02402c4084602ca04a440240a1091218919100a2084314a220840a00480aa210819a02120100a4409048968c05484200702a805440920100380144a9480),(0x80b20c31f72bfc4e1481d27000d43c9c5bd438a9c5e0286040f054f111d001ce10920229bde170b8d339029e2bcac4cd494fb74d1052452141a61c5b9ca1e642f40c600258428f0e5c00df481e03202a204cd465e10fe01206e82c7b03150603,0x80100c30e6089040109182600012282018c41889c5e0204002b0604000c009861080028b1c2120a0d12000120908c00d005a724402504200402010501c01c208540860025840090e1400964816012008204cd0254102a00206a0247b01150201),(0x12ce100c308544478a85796a2341d206e4242e31335abb35943abb40be28c8e05c4c115123137950052a02a9ba0d31c096458c656cc338623e92230683d8962194d5145c2aa62229438824d8e06246d0cd124850733918c390189888a426380a,0x10ca0000108540870900790a0240900460282200221a991490081a0028289000cc41010021184410080a0a28a20020c0200184206c0128621092200a03d8103080d5145c02a2022143880090804206d04d100840322918c190088800a4221002),(0x8628ebbd17000228c83c0291b729e17b3643984a392a815889878936d04e41b82b8e28807cc302855ead3105d9868885c748c2b0724ae81086518e259124cd4278a18b4aa01db88524c3a3435a0814469349110c18f0c24c2a8052bd88818268,0xc2206a1d05000020401c0090e509051303449848110100480001811490070429238c000818c508010485900541c68805c240409012420000024186258024450270208b02a00da0842041a3414a08100690490104085040042a8052bc00818028),(0xbc8ccda8781e4d8151cd3cf93a4a0a01509a42078c1bc4a783ea4aec6c7bbbd02ef85be130b1750bcd872a062d01842a34826040203d5b99ac8899721d47b82106b4f88001d04ee6f42e103eb14e0a090b95e84905a08ef7a2230402e2b14bc5,0x148981a0109a5c8210c1a4690a42220050930202c418c4a7837a48680e50b9d00c601bc02020f518c9002a002c1124282402304220255b598c9019921c51b8010494708001d04e62d42a103a30060a090b94e84905a08af280230402e2304b45),(0xd3b19712becef4647857054f8773c68492608a46265cd6cd0106c449284294958830b40e8328a4102841c46a63b66493288c7290c714876750b08cb0eb0a532e014ce7e24f9c08720240400006971f885be46b00080a21145aa7f52cf42a8012,0x92218c003e8654007015040a0c73c50280c0084821449285810a8400004080918c301008002824100801c000230200c0688c40804110046300b00cb28307502a0004c5624f9c086200004000021315805bc46800000a00145205f42ce0200002),(0x3145d24845746a93b60987114c89950ee90ab5809889781e716b0d141d9e036fea797f20c896480c8b565809c5575a81eabcad03980701be24b7e8d7401960b32336416db2f0c4c050f169960250e8b311988b92828b0074bd455ad232c2112c,0x2307720c00346283a400011d4c09950fa108a4001a095004514a0014181e2261ab3d3060c0d6480a2ac41009e4571880ea848181d90321bc24d38a860208103323340169a2b084c040f169960050c8b211800b9082890074b8455a803282012c),(0x49615339cc24bb41a658244591d020101222d0f578b5376254a121290a30cd5c4e2ad1d6dabfa9e032f022500c91031b32331a7a9ace0ca4e96243014a4009cd0d2a3210b66014de852533c420acc80ff443ad9cc5d0f4808cd621151170ac54,0x4900539a4030aa408668006591882010120251355ca1242200a1212102144d6e020a42d6d2878b6832b420400cb9813312321a4a924e408ce04943054c0001c10d2a2200b040149c8425334420acc80fa003859cc5d0e4000cd201111150ac54),(0x2108654280dbc21c532263cad6a2ab60a053058994f658a43b3dd89384745a04932387065124c385d01899e2cc083e3c1e3327061d61ca921a4965c8583262f4485320b5c04953298d1f02098424a39520b6148b236021a80528c3236c545ab4,0xc0001428049001c03a04a4012802a200013019184320c200a34088304a0580410028702010083a440180cc2080827381411260a0400ca0098085048489022c408432094004053098d0e0008842422012032140b21202188052801030c545a90)]
def deadcolumns : List ColumnInfo := [(1,0,510,0,12),(0,1,460,50,8),(2,0,509,0,12),(0,2,440,69,8),(3,0,508,0,9),(2,1,460,48,7),(4,0,507,0,12),(0,4,369,138,8),(5,0,506,0,8),(6,0,505,0,9),(4,2,440,65,7),(2,4,369,136,7),(7,0,504,0,7),(5,2,440,64,6),(8,0,503,0,12),(0,8,227,276,8),(9,0,486,0,8),(10,0,501,0,8),(12,0,499,0,9),(8,4,369,130,7),(4,8,227,272,7),(14,0,497,0,7),(10,4,369,128,6),(15,0,480,0,4),(16,0,495,0,13),(0,16,486,9,10),(17,0,494,0,11),(16,1,460,34,7),(19,0,492,0,8),(16,4,353,138,7),(21,0,490,0,7),(21,2,424,64,5),(24,0,487,0,11),(8,16,486,1,9),(25,0,486,0,8),(9,16,486,0,8),(27,0,484,0,5),(11,16,484,0,5),(24,4,353,130,6),(29,0,482,0,5),(26,4,353,128,5),(32,0,479,0,12),(0,32,94,385,8),(32,1,460,18,7),(1,32,94,384,7),(35,0,476,0,7),(34,1,460,16,6),(36,0,347,0,8),(39,0,344,0,4),(40,0,471,0,8),(49,0,462,0,8),(48,1,460,2,6),(50,1,460,0,5),(56,0,455,0,7),(64,0,447,0,13),(0,64,189,258,10),(66,0,445,0,11),(2,64,189,256,9),(67,0,444,0,8),(66,1,396,48,6),(70,0,441,0,8),(69,2,440,0,5),(74,0,437,0,7),(74,4,305,128,5),(80,0,431,0,11),(83,0,428,0,7),(96,0,415,0,9),(96,1,396,18,6),(98,1,396,16,5),(128,0,383,0,13),(128,1,332,50,7),(3,128,344,36,6),(132,0,379,0,11),(4,128,347,32,9),(133,0,378,0,7),(134,0,377,0,8),(132,2,312,65,6),(133,2,312,64,5),(136,0,375,0,9),(128,8,99,276,7),(140,0,371,0,8),(132,8,99,272,6),(138,4,369,0,5),(144,0,367,0,11),(152,4,353,2,5),(160,0,351,0,11),(160,1,332,18,6),(162,1,332,16,5),(164,0,347,0,8),(36,128,347,0,8),(172,0,339,0,5),(176,1,332,2,5),(180,0,331,0,5),(192,0,319,0,11),(198,0,313,0,7),(256,0,255,0,12),(258,0,189,0,8),(260,0,251,0,8),(264,0,247,0,9),(256,8,227,20,7),(8,256,151,96,7),(268,0,243,0,7),(260,8,227,16,6),(273,0,238,0,7),(280,0,231,0,8),(276,8,227,0,5),(288,0,223,0,9),(256,32,94,129,7),(32,256,151,72,7),(257,32,94,128,6),(296,0,215,0,7),(40,256,151,64,6),(304,0,207,0,6),(288,16,198,9,6),(273,32,78,128,5),(56,256,135,64,5),(320,0,191,0,11),(256,64,189,2,9),(322,0,189,0,8),(258,64,189,0,8),(324,0,187,0,7),(324,8,163,16,5),(321,32,30,128,5),(388,8,99,16,5),(168,256,23,64,5),(224,256,23,8,5)]
def deadautos : List (List Nat) := [[],[118,130,81],[100,131,82,16],[118,133,100,131,50,33,16],[116,83,32],[118,116,83,130,49,32],[118,133,33,48],[82,129,48],[118,133,116,83,82,81,80],[116,50,129,80],[100,49,128],[118,100,83,130,81,128]]
def deadlevels : Nat → Packing
  | 8 => deadl8
  | 9 => deadl9
  | 10 => deadl10
  | 11 => deadl11
  | 12 => deadl12
  | 13 => deadl13
  | 14 => deadl14
  | _ => emptyPacking
def deadindex : Nat → Nat → Option (Nat × Nat)
  | 8 => fun _ => none
  | 9 => lookupWord 1 3 0 9 1 4 (hashdeadl9)
  | 10 => lookupWord 17 61 5 13 5 4 (hashdeadl10)
  | 11 => lookupWord 124 434 7 16 8 4 (hashdeadl11)
  | 12 => lookupWord 137 475 8 16 8 4 (hashdeadl12)
  | 13 => lookupWord 26 148 3 13 5 4 (hashdeadl13)
  | 14 => lookupWord 7 47 1 10 2 4 (hashdeadl14)
  | _ => fun _ => none
def dead : Forest := ⟨511,14,fun j => deadsamples[j]?.getD (0,0),deadcolumns,deadautos,deadlevels,deadindex⟩
set_option maxHeartbeats 0 in
theorem geomdead : graphValid dead (boundsBefore known383) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=5) ?_⟩,listPieces_all (d:=3) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead8_0 : block dead 8 0 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead8 : block dead 8 0 2=true := sdead8_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead9_0 : block dead 9 0 12=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead9_12 : block dead 9 12 13=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead9 : block dead 9 0 25=true := (@block_merge dead 9 0 12 13 sdead9_0 sdead9_12)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_0 : block dead 10 0 6=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_6 : block dead 10 6 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_42 : block dead 10 42 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_78 : block dead 10 78 35=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_113 : block dead 10 113 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_149 : block dead 10 149 7=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead10 : block dead 10 0 156=true := (@block_merge dead 10 0 149 7 (@block_merge dead 10 0 113 36 (@block_merge dead 10 0 78 35 (@block_merge dead 10 0 42 36 (@block_merge dead 10 0 6 36 sdead10_0 sdead10_6) sdead10_42) sdead10_78) sdead10_113) sdead10_149)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_0 : block dead 11 0 4=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_4 : block dead 11 4 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_40 : block dead 11 40 15=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_55 : block dead 11 55 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_91 : block dead 11 91 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_127 : block dead 11 127 29=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_156 : block dead 11 156 27=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead11 : block dead 11 0 183=true := (@block_merge dead 11 0 156 27 (@block_merge dead 11 0 127 29 (@block_merge dead 11 0 91 36 (@block_merge dead 11 0 55 36 (@block_merge dead 11 0 40 15 (@block_merge dead 11 0 4 36 sdead11_0 sdead11_4) sdead11_40) sdead11_55) sdead11_91) sdead11_127) sdead11_156)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead12_0 : block dead 12 0 3=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead12_3 : block dead 12 3 14=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead12_17 : block dead 12 17 15=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead12 : block dead 12 0 32=true := (@block_merge dead 12 0 17 15 (@block_merge dead 12 0 3 14 sdead12_0 sdead12_3) sdead12_17)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead13_0 : block dead 13 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead13_1 : block dead 13 1 3=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead13 : block dead 13 0 4=true := (@block_merge dead 13 0 1 3 sdead13_0 sdead13_1)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead14_0 : block dead 14 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead14 : block dead 14 0 1=true := sdead14_0
theorem tablesdead : checkedTables dead 14 := by
  intro k hk
  interval_cases k
  · exact (rfl : block dead 0 0 0 = true)
  · exact (rfl : block dead 1 0 0 = true)
  · exact (rfl : block dead 2 0 0 = true)
  · exact (rfl : block dead 3 0 0 = true)
  · exact (rfl : block dead 4 0 0 = true)
  · exact (rfl : block dead 5 0 0 = true)
  · exact (rfl : block dead 6 0 0 = true)
  · exact (rfl : block dead 7 0 0 = true)
  · exact alldead8
  · exact alldead9
  · exact alldead10
  · exact alldead11
  · exact alldead12
  · exact alldead13
  · exact alldead14
theorem slice_self {raw : List Sig} {T : Sig} {L : Nat} (pT : proper T) (h : Lower raw T L) :
    Slice raw T one L := by
  refine ⟨id,raw,fun r => bit_one r,fun a ha => ?_,observe_proper pT,h⟩
  exact Or.inl (List.mem_map_of_mem ha)

theorem plainA {m q cap : Nat} {prior : Nat → Nat} (low : ∀ q, Lower (varsX q) (graphGoal q) (prior q))
    (e : (graphGoal q == graphGoal m && (varsX q == vars m) && (prior q == cap+1) && properB (graphGoal m) &&
      decide (vars m).Nodup && poolCut one (cap+1) cap 0 (vars m) (vars m)) = true) :
    Impossible (graphGoal m) cap (vars m).toFinset := by
  simp only [Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at e
  obtain ⟨⟨⟨⟨⟨e1,e2⟩,e3⟩,e4⟩,e5⟩,e6⟩ := e
  have h := low q
  rw [e1,e2,e3] at h
  exact poolCut_sound (slice_self (proper_of _ e4) h) [] rfl e5 e6

def rootB (m : Nat) : List Sig := vars m ++ [seed]
theorem cut_root {m cap : Nat} {prior : Nat → Nat} {ws : List Sig}
    (low : ∀ q, Lower (varsX q) (graphGoal q) (prior q)) (ci : ColumnInfo)
    (ok : colCheck m ci prior = true)
    (cut : (decide ws.Nodup && poolCut (subcube ci.1 ci.2.1) ci.2.2.2.2 cap 0 (varsX (rawMask m ci)) ws)=true) :
    Impossible (graphGoal m) cap ws.toFinset := by
  simp only [Bool.and_eq_true,decide_eq_true_eq] at cut
  exact poolCut_sound (col_sound ci prior low ok) [] rfl cut.1 cut.2

theorem index_root {g : Forest} {m cap i : Nat} {prior : Nat → Nat} {ws : List Sig}
    (hm : g.mask=m) (low : ∀ q, Lower (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g cap)
    (idx : indexedRoot g cap i ws = true) : Impossible (graphGoal m) cap ws.toFinset := by
  subst hm
  exact root_index low geom blocks (Nat.le_refl _) idx

def pairsX (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r := (1 <<< ((hints >>> (4*i)) &&& 15)) ||| (if i=0 then 16 else if i=4 then 1 else 0)
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def splitOK (m hints : Nat) : Bool :=
  checkEssential (graphGoal m) (rootB m) (pairsX m hints) &&
    ((pairsX m hints).map Prod.fst == vars m) && properB (graphGoal m)

theorem strong_split {m hints : Nat} (ok : splitOK m hints = true) {k t : Nat} {S : Finset Sig}
    (h : Live (graphGoal m) k t S) (sub : ∀ v ∈ S, v ∈ rootB m) :
    S=(vars m).toFinset ∨ S=(rootB m).toFinset := by
  simp only [splitOK,Bool.and_eq_true,beq_iff_eq] at ok
  obtain ⟨⟨ess,alls⟩,_⟩ := ok
  have rest : ∀ v ∈ vars m, v ∈ S := by
    intro v hv
    rw [←alls] at hv
    obtain ⟨r,s,hd,hi⟩ := essential_ok ess v (List.mem_toFinset.mpr hv)
    exact raw_required h (rootB m) v sub r s hd hi
  have mem : ∀ v, v ∈ rootB m ↔ v ∈ vars m ∨ v=seed := by
    intro v
    simp [rootB]
  by_cases hs : seed ∈ S
  · refine Or.inr ?_
    ext v
    rw [List.mem_toFinset]
    refine ⟨sub v,fun hv => ?_⟩
    rcases (mem v).mp hv with hv | rfl
    · exact rest v hv
    · exact hs
  · refine Or.inl ?_
    ext v
    rw [List.mem_toFinset]
    refine ⟨fun hv => ?_,rest v⟩
    rcases (mem v).mp (sub v hv) with hv | rfl
    · exact hv
    · exact False.elim (hs hv)

theorem strong_low {m hints cap : Nat} (ok : splitOK m hints = true)
    (a : Impossible (graphGoal m) cap (vars m).toFinset)
    (b : Impossible (graphGoal m) cap (rootB m).toFinset) :
    Lower (rootB m) (graphGoal m) (cap+1) := by
  have ok' := ok
  simp only [splitOK,Bool.and_eq_true,beq_iff_eq] at ok'
  intro p bank hr ha
  obtain ⟨k,t,S,hk,run,hs⟩ := reach_live (proper_of _ ok'.2) hr ha
  by_contra! small
  rcases strong_split ok run hs with e | e
  · exact a k t (by omega) (e ▸ run)
  · exact b k t (by omega) (e ▸ run)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low511 : Lower (vars 511) (graphGoal 511) 15 :=
  lower_forest (g:=dead) (i:=0) (hints:=13438558465) (before_sound known383 valid383) geomdead tablesdead (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps511 : List (Nat × List Nat) := [(511,[])]
def known511 := extendKnown known383 15 maps511
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid511 : Known known511 := extendKnown_ok (m:=511) valid383 low511 (by decide +kernel)
theorem plainB {m q cap : Nat} {prior : Nat → Nat} (low : ∀ q, Lower (varsX q) (graphGoal q) (prior q))
    (e : (graphGoal q == graphGoal m && (varsX q == vars m) && decide (cap+1 ≤ prior q) && properB (graphGoal m) &&
      decide (vars m).Nodup && poolCut one (cap+1) cap 0 (vars m) (vars m)) = true) :
    Impossible (graphGoal m) cap (vars m).toFinset := by
  simp only [Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at e
  obtain ⟨⟨⟨⟨⟨e1,e2⟩,e3⟩,e4⟩,e5⟩,e6⟩ := e
  have h := low q
  rw [e1,e2] at h
  have h' : Lower (vars m) (graphGoal m) (cap+1) := fun p bank hr ha => le_trans e3 (h p bank hr ha)
  exact poolCut_sound (slice_self (proper_of _ e4) h') [] rfl e5 e6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx23 : Lower (varsX 535) (graphGoal 535) 4 :=
  strong_low (m:=535) (cap:=3) (hints:=257) (by decide +kernel) (plainB (q:=23) (prior:=boundsBefore known511) (before_sound known511 valid511) (by decide +kernel))
    (cut_root (prior:=boundsBefore known511) (before_sound known511 valid511) (516,1,0,18,1) (by decide +kernel) (by decide +kernel))
def mapsx23 : List (Nat × List Nat) := [(535,[]),(817,[118,130,81])]
def knownx23 := extendKnown known511 4 mapsx23
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx23 : Known knownx23 := extendKnown_ok (m:=535) valid511 lowx23 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx27 : Lower (varsX 539) (graphGoal 539) 4 :=
  strong_low (m:=539) (cap:=3) (hints:=16385) (by decide +kernel) (plainB (q:=27) (prior:=boundsBefore knownx23) (before_sound knownx23 validx23) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx23) (before_sound knownx23 validx23) (520,1,0,18,1) (by decide +kernel) (by decide +kernel))
def mapsx27 : List (Nat × List Nat) := [(539,[]),(569,[118,130,81])]
def knownx27 := extendKnown knownx23 4 mapsx27
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx27 : Known knownx27 := extendKnown_ok (m:=539) validx23 lowx27 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx29 : Lower (varsX 541) (graphGoal 541) 4 :=
  strong_low (m:=541) (cap:=3) (hints:=8964) (by decide +kernel) (plainB (q:=29) (prior:=boundsBefore knownx27) (before_sound knownx27 validx27) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx27) (before_sound knownx27 validx27) (516,16,0,9,1) (by decide +kernel) (by decide +kernel))
def mapsx29 : List (Nat × List Nat) := [(541,[]),(793,[118,130,81])]
def knownx29 := extendKnown knownx27 4 mapsx29
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx29 : Known knownx29 := extendKnown_ok (m:=541) validx27 lowx29 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx177 : Lower (varsX 689) (graphGoal 689) 4 :=
  strong_low (m:=689) (cap:=3) (hints:=1342177284) (by decide +kernel) (plainB (q:=177) (prior:=boundsBefore knownx29) (before_sound knownx29 validx29) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx29) (before_sound knownx29 validx29) (640,1,0,48,1) (by decide +kernel) (by decide +kernel))
def mapsx177 : List (Nat × List Nat) := [(689,[])]
def knownx177 := extendKnown knownx29 4 mapsx177
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx177 : Known knownx177 := extendKnown_ok (m:=689) validx29 lowx177 (by decide +kernel)
def x31samples : Array (Bits × Bits) := #[(0x7b3c035bd9e01adecf00d6f67806b7b3c035bd9e01adecf00d6f67806b7b3c035bd9e01adecf00d6f67806b7b3c035bd9e01adecf00d6f67806b7b3c035bd9e01adecf00d6f67806b7b3c035bd9e01adecf00d6f67806b7b3c035bd9e01adecf,0x681d965b40ecb2da076596d03b2cb681d965b40ecb2da076596d03b2cb681d965b40ecb2da076596d03b2cb681d965b40ecb2da076596d03b2cb681d965b40ecb2da076596d03b2cb681d965b40ecb2da076596d03b2cb681d965b40ecb2da07),(0xbde60d2def30696f79834b7bcc1a5bde60d2def30696f79834b7bcc1a5bde60d2def30696f79834b7bcc1a5bde60d2def30696f79834b7bcc1a5bde60d2def30696f79834b7bcc1a5bde60d2def30696f79834b7bcc1a5bde60d2def30696f79,0x91e221048f11082478884123c442091e221048f11082478884123c442091e221048f11082478884123c442091e221048f11082478884123c442091e221048f11082478884123c442091e221048f11082478884123c442091e221048f11082478),(0x6ddecb036ef6581b77b2c0dbbd9606ddecb036ef6581b77b2c0dbbd9606ddecb036ef6581b77b2c0dbbd9606ddecb036ef6581b77b2c0dbbd9606ddecb036ef6581b77b2c0dbbd9606ddecb036ef6581b77b2c0dbbd9606ddecb036ef6581b7,0x60d0cf8306867c183433e0c1a19f060d0cf8306867c183433e0c1a19f060d0cf8306867c183433e0c1a19f060d0cf8306867c183433e0c1a19f060d0cf8306867c183433e0c1a19f060d0cf8306867c183433e0c1a19f060d0cf8306867c183),(0x985bf284c2df942616fca130b7e50985bf284c2df942616fca130b7e50985bf284c2df942616fca130b7e50985bf284c2df942616fca130b7e50985bf284c2df942616fca130b7e50985bf284c2df942616fca130b7e50985bf284c2df942616,0x7852f303c297981e14bcc0f0a5e607852f303c297981e14bcc0f0a5e607852f303c297981e14bcc0f0a5e607852f303c297981e14bcc0f0a5e607852f303c297981e14bcc0f0a5e607852f303c297981e14bcc0f0a5e607852f303c297981e14),(0xc6a21256351092b1a884958d4424ac6a21256351092b1a884958d4424ac6a21256351092b1a884958d4424ac6a21256351092b1a884958d4424ac6a21256351092b1a884958d4424ac6a21256351092b1a884958d4424ac6a21256351092b1a8,0x87a008043d004021e802010f4010087a008043d004021e802010f4010087a008043d004021e802010f4010087a008043d004021e802010f4010087a008043d004021e802010f4010087a008043d004021e802010f4010087a008043d004021e8),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def x31autos : List (List Nat) := [[],[65,50],[16,66],[32,67],[48,33],[64,49],[16,32,48,64],[32,64,16,48],[48,16,64,32],[64,48,32,16]]
def x31d5 (i : Nat) : Nat := 0x1888001db920bf2aa817d52502faa2a07e4c140
def x31l5 : Packing := (4,2,2,0,4,5,0,x31d5)
def x31d6 (i : Nat) : Nat := 0x1a23fd40
def x31h6 (i : Nat) : Nat := 0xf080000183000d4002c035601
def x31l6 : Packing := (1,1,2,2,4,0,0,x31d6)
def x31columns : List ColumnInfo := [(528,0,15,0,4),(8,0,535,0,4),(4,0,539,0,4),(2,0,541,0,4)]
def x31levels : Nat → Packing
  | 5 => x31l5
  | 6 => x31l6
  | _ => emptyPacking
def x31index : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 10 0 10 2 4 x31h6
  | _ => fun _ => none
def x31 : Forest := ⟨543,6,fun j => x31samples[j]?.getD (0,0),x31columns,x31autos,x31levels,x31index⟩
set_option maxHeartbeats 0 in
theorem geomx31 : graphValid x31 (boundsBefore knownx177) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx315_0 : block x31 5 0 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx315 : block x31 5 0 4=true := sx315_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx316_0 : block x31 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx316 : block x31 6 0 1=true := sx316_0
theorem tablesx31 : checkedTables x31 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block x31 0 0 0 = true)
  · exact (rfl : block x31 1 0 0 = true)
  · exact (rfl : block x31 2 0 0 = true)
  · exact (rfl : block x31 3 0 0 = true)
  · exact (rfl : block x31 4 0 0 = true)
  · exact allx315
  · exact allx316
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx31 : Lower (varsX 543) (graphGoal 543) 7 :=
  strong_low (m:=543) (cap:=6) (hints:=8449) (by decide +kernel) (plainB (q:=31) (prior:=boundsBefore knownx177) (before_sound knownx177 validx177) (by decide +kernel))
    (index_root (g:=x31) (i:=0) rfl (before_sound knownx177 validx177) geomx31 tablesx31 (by decide +kernel))
def mapsx31 : List (Nat × List Nat) := [(543,[]),(825,[118,130,81])]
def knownx31 := extendKnown knownx177 7 mapsx31
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx31 : Known knownx31 := extendKnown_ok (m:=543) validx177 lowx31 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx55 : Lower (varsX 567) (graphGoal 567) 5 :=
  strong_low (m:=567) (cap:=4) (hints:=257) (by decide +kernel) (plainB (q:=55) (prior:=boundsBefore knownx31) (before_sound knownx31 validx31) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx31) (before_sound knownx31 validx31) (32,0,535,0,4) (by decide +kernel) (by decide +kernel))
def mapsx55 : List (Nat × List Nat) := [(567,[])]
def knownx55 := extendKnown knownx31 5 mapsx55
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx55 : Known knownx55 := extendKnown_ok (m:=567) validx31 lowx55 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx61 : Lower (varsX 573) (graphGoal 573) 5 :=
  strong_low (m:=573) (cap:=4) (hints:=8964) (by decide +kernel) (plainB (q:=61) (prior:=boundsBefore knownx55) (before_sound knownx55 validx55) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx55) (before_sound knownx55 validx55) (32,0,541,0,4) (by decide +kernel) (by decide +kernel))
def mapsx61 : List (Nat × List Nat) := [(573,[])]
def knownx61 := extendKnown knownx55 5 mapsx61
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx61 : Known knownx61 := extendKnown_ok (m:=573) validx55 lowx61 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx115 : Lower (varsX 627) (graphGoal 627) 5 :=
  strong_low (m:=627) (cap:=4) (hints:=16777217) (by decide +kernel) (plainB (q:=115) (prior:=boundsBefore knownx61) (before_sound knownx61 validx61) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx61) (before_sound knownx61 validx61) (528,0,99,0,4) (by decide +kernel) (by decide +kernel))
def mapsx115 : List (Nat × List Nat) := [(627,[]),(691,[118,130,81])]
def knownx115 := extendKnown knownx61 5 mapsx115
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx115 : Known knownx115 := extendKnown_ok (m:=627) validx61 lowx115 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx151 : Lower (varsX 663) (graphGoal 663) 5 :=
  strong_low (m:=663) (cap:=4) (hints:=536871169) (by decide +kernel) (plainB (q:=151) (prior:=boundsBefore knownx115) (before_sound knownx115 validx115) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx115) (before_sound knownx115 validx115) (128,0,535,0,4) (by decide +kernel) (by decide +kernel))
def mapsx151 : List (Nat × List Nat) := [(663,[]),(881,[118,130,81])]
def knownx151 := extendKnown knownx115 5 mapsx151
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx151 : Known knownx151 := extendKnown_ok (m:=663) validx115 lowx151 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx181 : Lower (varsX 693) (graphGoal 693) 5 :=
  strong_low (m:=693) (cap:=4) (hints:=536872708) (by decide +kernel) (plainB (q:=181) (prior:=boundsBefore knownx151) (before_sound knownx151 validx151) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx151) (before_sound knownx151 validx151) (528,0,165,0,4) (by decide +kernel) (by decide +kernel))
def mapsx181 : List (Nat × List Nat) := [(693,[]),(851,[118,130,81])]
def knownx181 := extendKnown knownx151 5 mapsx181
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx181 : Known knownx181 := extendKnown_ok (m:=693) validx151 lowx181 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx185 : Lower (varsX 697) (graphGoal 697) 5 :=
  strong_low (m:=697) (cap:=4) (hints:=1342193668) (by decide +kernel) (plainB (q:=185) (prior:=boundsBefore knownx181) (before_sound knownx181 validx181) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx181) (before_sound knownx181 validx181) (128,0,569,0,4) (by decide +kernel) (by decide +kernel))
def mapsx185 : List (Nat × List Nat) := [(697,[])]
def knownx185 := extendKnown knownx181 5 mapsx185
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx185 : Known knownx185 := extendKnown_ok (m:=697) validx181 lowx185 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx345 : Lower (varsX 857) (graphGoal 857) 5 :=
  strong_low (m:=857) (cap:=4) (hints:=13019136004) (by decide +kernel) (plainB (q:=345) (prior:=boundsBefore knownx185) (before_sound knownx185 validx185) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx185) (before_sound knownx185 validx185) (64,0,793,0,4) (by decide +kernel) (by decide +kernel))
def mapsx345 : List (Nat × List Nat) := [(857,[])]
def knownx345 := extendKnown knownx185 5 mapsx345
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx345 : Known knownx345 := extendKnown_ok (m:=857) validx185 lowx345 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx63 : Lower (varsX 575) (graphGoal 575) 8 :=
  strong_low (m:=575) (cap:=7) (hints:=8449) (by decide +kernel) (plainB (q:=63) (prior:=boundsBefore knownx345) (before_sound knownx345 validx345) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx345) (before_sound knownx345 validx345) (32,0,543,0,7) (by decide +kernel) (by decide +kernel))
def mapsx63 : List (Nat × List Nat) := [(575,[])]
def knownx63 := extendKnown knownx345 8 mapsx63
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx63 : Known knownx63 := extendKnown_ok (m:=575) validx345 lowx63 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx95 : Lower (varsX 607) (graphGoal 607) 8 :=
  strong_low (m:=607) (cap:=7) (hints:=16785665) (by decide +kernel) (plainB (q:=95) (prior:=boundsBefore knownx63) (before_sound knownx63 validx63) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx63) (before_sound knownx63 validx63) (64,0,543,0,7) (by decide +kernel) (by decide +kernel))
def mapsx95 : List (Nat × List Nat) := [(607,[]),(953,[118,130,81])]
def knownx95 := extendKnown knownx63 8 mapsx95
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx95 : Known knownx95 := extendKnown_ok (m:=607) validx63 lowx95 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx119 : Lower (varsX 631) (graphGoal 631) 6 :=
  strong_low (m:=631) (cap:=5) (hints:=16777473) (by decide +kernel) (plainB (q:=119) (prior:=boundsBefore knownx95) (before_sound knownx95 validx95) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx95) (before_sound knownx95 validx95) (64,0,567,0,5) (by decide +kernel) (by decide +kernel))
def mapsx119 : List (Nat × List Nat) := [(631,[])]
def knownx119 := extendKnown knownx95 6 mapsx119
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx119 : Known knownx119 := extendKnown_ok (m:=631) validx95 lowx119 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx159 : Lower (varsX 671) (graphGoal 671) 8 :=
  strong_low (m:=671) (cap:=7) (hints:=536879361) (by decide +kernel) (plainB (q:=159) (prior:=boundsBefore knownx119) (before_sound knownx119 validx119) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx119) (before_sound knownx119 validx119) (128,0,543,0,7) (by decide +kernel) (by decide +kernel))
def mapsx159 : List (Nat × List Nat) := [(671,[]),(889,[118,130,81])]
def knownx159 := extendKnown knownx119 8 mapsx159
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx159 : Known knownx159 := extendKnown_ok (m:=671) validx119 lowx159 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx183 : Lower (varsX 695) (graphGoal 695) 8 :=
  strong_low (m:=695) (cap:=7) (hints:=536871169) (by decide +kernel) (plainB (q:=183) (prior:=boundsBefore knownx159) (before_sound knownx159 validx159) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx159) (before_sound knownx159 validx159) (528,0,167,0,7) (by decide +kernel) (by decide +kernel))
def mapsx183 : List (Nat × List Nat) := [(695,[]),(883,[118,130,81])]
def knownx183 := extendKnown knownx159 8 mapsx183
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx183 : Known knownx183 := extendKnown_ok (m:=695) validx159 lowx183 (by decide +kernel)
def x187samples : Array (Bits × Bits) := #[(0x1b5fdbdc836bfb7b906d7f6f720dafedee41b5fdbdc836bfb7b906d7f6f720dafedee41b5fdbdc836bfb7b906d7f6f720dafedee41b5fdbdc836bfb7b906d7f6f720dafedee41b5fdbdc836bfb7b906d7f6f720dafedee41b5fdbdc836bfb7b9,0x23581bdc846b037b908d606f7211ac0dee423581bdc846b037b908d606f7211ac0dee423581bdc846b037b908d606f7211ac0dee423581bdc846b037b908d606f7211ac0dee423581bdc846b037b908d606f7211ac0dee423581bdc846b037b9),(0x9ca784db9394f09b72729e136e4e53c26dc9ca784db9394f09b72729e136e4e53c26dc9ca784db9394f09b72729e136e4e53c26dc9ca784db9394f09b72729e136e4e53c26dc9ca784db9394f09b72729e136e4e53c26dc9ca784db9394f09b7,0x84a7a4237094f4846e129e908dc253d211b84a7a4237094f4846e129e908dc253d211b84a7a4237094f4846e129e908dc253d211b84a7a4237094f4846e129e908dc253d211b84a7a4237094f4846e129e908dc253d211b84a7a4237094f4846),(0x0,0x0),(0x63603ce7ec6c079cfd8d80f39fb1b01e73f63603ce7ec6c079cfd8d80f39fb1b01e73f63603ce7ec6c079cfd8d80f39fb1b01e73f63603ce7ec6c079cfd8d80f39fb1b01e73f63603ce7ec6c079cfd8d80f39fb1b01e73f63603ce7ec6c079cf,0xa3503af7f46a075efe8d40ebdfd1a81d7bfa3503af7f46a075efe8d40ebdfd1a81d7bfa3503af7f46a075efe8d40ebdfd1a81d7bfa3503af7f46a075efe8d40ebdfd1a81d7bfa3503af7f46a075efe8d40ebdfd1a81d7bfa3503af7f46a075ef),(0x67fee4006cffdc800d9ffb9001b3ff7200367fee4006cffdc800d9ffb9001b3ff7200367fee4006cffdc800d9ffb9001b3ff7200367fee4006cffdc800d9ffb9001b3ff7200367fee4006cffdc800d9ffb9001b3ff7200367fee4006cffdc800,0x5ca7c4000b94f88001729f10002e53e20005ca7c4000b94f88001729f10002e53e20005ca7c4000b94f88001729f10002e53e20005ca7c4000b94f88001729f10002e53e20005ca7c4000b94f88001729f10002e53e20005ca7c4000b94f8800),(0xcc81ff2719903fe4e33207fc9c6640ff938cc81ff2719903fe4e33207fc9c6640ff938cc81ff2719903fe4e33207fc9c6640ff938cc81ff2719903fe4e33207fc9c6640ff938cc81ff2719903fe4e33207fc9c6640ff938cc81ff2719903fe4e,0xcc03e40219807c8043300f90086601f2010cc03e40219807c8043300f90086601f2010cc03e40219807c8043300f90086601f2010cc03e40219807c8043300f90086601f2010cc03e40219807c8043300f90086601f2010cc03e40219807c804),(0x0,0x0),(0xa4d8033fb49b0067f693600cfed26c019fda4d8033fb49b0067f693600cfed26c019fda4d8033fb49b0067f693600cfed26c019fda4d8033fb49b0067f693600cfed26c019fda4d8033fb49b0067f693600cfed26c019fda4d8033fb49b0067f,0x32fc13bde65f8277bccbf04ef7997e09def32fc13bde65f8277bccbf04ef7997e09def32fc13bde65f8277bccbf04ef7997e09def32fc13bde65f8277bccbf04ef7997e09def32fc13bde65f8277bccbf04ef7997e09def32fc13bde65f8277b),(0x0,0x0)]
def x187autos : List (List Nat) := [[],[115,84]]
def x187d5 (i : Nat) : Nat := 0x22f54c530
def x187l5 : Packing := (1,2,1,0,4,0,0,x187d5)
def x187d6 (i : Nat) : Nat := 0x45fd30
def x187h6 (i : Nat) : Nat := 0x1e0
def x187l6 : Packing := (1,1,1,1,4,0,0,x187d6)
def x187columns : List ColumnInfo := [(528,8,163,0,4),(10,0,689,0,4)]
def x187levels : Nat → Packing
  | 5 => x187l5
  | 6 => x187l6
  | _ => emptyPacking
def x187index : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 3 0 9 1 4 x187h6
  | _ => fun _ => none
def x187 : Forest := ⟨699,6,fun j => x187samples[j]?.getD (0,0),x187columns,x187autos,x187levels,x187index⟩
set_option maxHeartbeats 0 in
theorem geomx187 : graphValid x187 (boundsBefore knownx183) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx1875_0 : block x187 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx1875 : block x187 5 0 1=true := sx1875_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx1876_0 : block x187 6 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx1876 : block x187 6 0 1=true := sx1876_0
theorem tablesx187 : checkedTables x187 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block x187 0 0 0 = true)
  · exact (rfl : block x187 1 0 0 = true)
  · exact (rfl : block x187 2 0 0 = true)
  · exact (rfl : block x187 3 0 0 = true)
  · exact (rfl : block x187 4 0 0 = true)
  · exact allx1875
  · exact allx1876
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx187 : Lower (varsX 699) (graphGoal 699) 7 :=
  strong_low (m:=699) (cap:=6) (hints:=1342193665) (by decide +kernel) (plainB (q:=187) (prior:=boundsBefore knownx183) (before_sound knownx183 validx183) (by decide +kernel))
    (index_root (g:=x187) (i:=0) rfl (before_sound knownx183 validx183) geomx187 tablesx187 (by decide +kernel))
def mapsx187 : List (Nat × List Nat) := [(699,[])]
def knownx187 := extendKnown knownx183 7 mapsx187
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx187 : Known knownx187 := extendKnown_ok (m:=699) validx183 lowx187 (by decide +kernel)
def x189samples : Array (Bits × Bits) := #[(0x72bf082bb70ee57e10576e1dcafc20aedc3b95f8415db8772bf082bb70ee57e10576e1dcafc20aedc3b95f8415db8772bf082bb70ee57e10576e1dcafc20aedc3b95f8415db8772bf082bb70ee57e10576e1dcafc20aedc3b95f8415db8772bf,0x60371011b76ec06e20236edd80dc4046ddbb01b8808dbb760371011b76ec06e20236edd80dc4046ddbb01b8808dbb760371011b76ec06e20236edd80dc4046ddbb01b8808dbb760371011b76ec06e20236edd80dc4046ddbb01b8808dbb76037),(0x0,0x0),(0x7bff3f0409e2f7fe7e0813c5effcfc10278bdff9f8204f17bff3f0409e2f7fe7e0813c5effcfc10278bdff9f8204f17bff3f0409e2f7fe7e0813c5effcfc10278bdff9f8204f17bff3f0409e2f7fe7e0813c5effcfc10278bdff9f8204f17bff,0x1bbd1e0424c0377a3c0849806ef478109300dde8f0212601bbd1e0424c0377a3c0849806ef478109300dde8f0212601bbd1e0424c0377a3c0849806ef478109300dde8f0212601bbd1e0424c0377a3c0849806ef478109300dde8f0212601bbd),(0xc44341ddd2e3888683bba5c7110d07774b8e221a0eee971c44341ddd2e3888683bba5c7110d07774b8e221a0eee971c44341ddd2e3888683bba5c7110d07774b8e221a0eee971c44341ddd2e3888683bba5c7110d07774b8e221a0eee971c443,0xc4424119932f88848233265f110904664cbe221208cc997c4424119932f88848233265f110904664cbe221208cc997c4424119932f88848233265f110904664cbe221208cc997c4424119932f88848233265f110904664cbe221208cc997c442),(0x132846f2ce9426508de59d284ca11bcb3a509942379674a132846f2ce9426508de59d284ca11bcb3a509942379674a132846f2ce9426508de59d284ca11bcb3a509942379674a132846f2ce9426508de59d284ca11bcb3a509942379674a1328,0x138806e2489027100dc491204e201b8922409c403712448138806e2489027100dc491204e201b8922409c403712448138806e2489027100dc491204e201b8922409c403712448138806e2489027100dc491204e201b8922409c4037124481388),(0x8dcc884f30991b99109e61323732213cc2646e64427984c8dcc884f30991b99109e61323732213cc2646e64427984c8dcc884f30991b99109e61323732213cc2646e64427984c8dcc884f30991b99109e61323732213cc2646e64427984c8dcc,0x99c84d4e008133909a9c0102672135380204ce426a7004099c84d4e008133909a9c0102672135380204ce426a7004099c84d4e008133909a9c0102672135380204ce426a7004099c84d4e008133909a9c0102672135380204ce426a7004099c8),(0x0,0x0),(0xad12b6b01b3d5a256d60367ab44adac06cf56895b580d9ead12b6b01b3d5a256d60367ab44adac06cf56895b580d9ead12b6b01b3d5a256d60367ab44adac06cf56895b580d9ead12b6b01b3d5a256d60367ab44adac06cf56895b580d9ead12,0x2402a0b1db3e48054163b67c900a82c76cf92015058ed9f2402a0b1db3e48054163b67c900a82c76cf92015058ed9f2402a0b1db3e48054163b67c900a82c76cf92015058ed9f2402a0b1db3e48054163b67c900a82c76cf92015058ed9f2402),(0x0,0x0)]
def x189autos : List (List Nat) := [[],[115,84],[48,82],[112,66],[32,67,117],[32,83,116],[64,114,83],[80,50,116],[48,112,82,66],[112,48,66,82],[64,48,32,112,80],[80,112,32,48,64]]
def x189d6 (i : Nat) : Nat := 0x2100c920bf58930bf58530fe48130
def x189l6 : Packing := (3,2,2,0,4,5,0,x189d6)
def x189d7 (i : Nat) : Nat := 0x83fd30
def x189h7 (i : Nat) : Nat := 0xd6400e0000000000008200101000da0000000198
def x189l7 : Packing := (1,1,2,2,4,0,0,x189d7)
def x189columns : List ColumnInfo := [(528,0,173,0,5),(8,0,693,0,5),(529,0,172,0,4)]
def x189levels : Nat → Packing
  | 6 => x189l6
  | 7 => x189l7
  | _ => emptyPacking
def x189index : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 17 0 10 2 4 x189h7
  | _ => fun _ => none
def x189 : Forest := ⟨701,7,fun j => x189samples[j]?.getD (0,0),x189columns,x189autos,x189levels,x189index⟩
set_option maxHeartbeats 0 in
theorem geomx189 : graphValid x189 (boundsBefore knownx187) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx1896_0 : block x189 6 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx1896 : block x189 6 0 3=true := sx1896_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx1897_0 : block x189 7 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx1897 : block x189 7 0 1=true := sx1897_0
theorem tablesx189 : checkedTables x189 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block x189 0 0 0 = true)
  · exact (rfl : block x189 1 0 0 = true)
  · exact (rfl : block x189 2 0 0 = true)
  · exact (rfl : block x189 3 0 0 = true)
  · exact (rfl : block x189 4 0 0 = true)
  · exact (rfl : block x189 5 0 0 = true)
  · exact allx1896
  · exact allx1897
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx189 : Lower (varsX 701) (graphGoal 701) 8 :=
  strong_low (m:=701) (cap:=7) (hints:=536879876) (by decide +kernel) (plainB (q:=189) (prior:=boundsBefore knownx187) (before_sound knownx187 validx187) (by decide +kernel))
    (index_root (g:=x189) (i:=0) rfl (before_sound knownx187 validx187) geomx189 tablesx189 (by decide +kernel))
def mapsx189 : List (Nat × List Nat) := [(701,[]),(859,[118,130,81])]
def knownx189 := extendKnown knownx187 8 mapsx189
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx189 : Known knownx189 := extendKnown_ok (m:=701) validx187 lowx189 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx215 : Lower (varsX 727) (graphGoal 727) 7 :=
  strong_low (m:=727) (cap:=6) (hints:=553648385) (by decide +kernel) (plainB (q:=215) (prior:=boundsBefore knownx189) (before_sound knownx189 validx189) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx189) (before_sound knownx189 validx189) (512,16,198,1,5) (by decide +kernel) (by decide +kernel))
def mapsx215 : List (Nat × List Nat) := [(727,[]),(1009,[118,130,81])]
def knownx215 := extendKnown knownx189 7 mapsx215
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx215 : Known knownx215 := extendKnown_ok (m:=727) validx189 lowx215 (by decide +kernel)
def x243samples : Array (Bits × Bits) := #[(0xfd85febcfec2ff5e7f617faf3fb0bfd79fd85febcfec2ff5e7f617faf3fb0bfd79fd85febcfec2ff5e7f617faf3fb0bfd79fd85febcfec2ff5e7f617faf3fb0bfd79fd85febcfec2ff5e7f617faf3fb0bfd79fd85febcfec2ff5e7f617faf3fb,0x85febc0042ff5e00217faf0010bfd780085febc0042ff5e00217faf0010bfd780085febc0042ff5e00217faf0010bfd780085febc0042ff5e00217faf0010bfd780085febc0042ff5e00217faf0010bfd780085febc0042ff5e00217faf001),(0x73fa017fb9fd00bfdcfe805fee7f402ff73fa017fb9fd00bfdcfe805fee7f402ff73fa017fb9fd00bfdcfe805fee7f402ff73fa017fb9fd00bfdcfe805fee7f402ff73fa017fb9fd00bfdcfe805fee7f402ff73fa017fb9fd00bfdcfe805fee7,0x7b7a0100bdbd00805ede80402f6f402017b7a0100bdbd00805ede80402f6f402017b7a0100bdbd00805ede80402f6f402017b7a0100bdbd00805ede80402f6f402017b7a0100bdbd00805ede80402f6f402017b7a0100bdbd00805ede80402f6),(0x0,0x0),(0x0,0x0),(0xef481f83f7a40fc1fbd207e0fde903f07ef481f83f7a40fc1fbd207e0fde903f07ef481f83f7a40fc1fbd207e0fde903f07ef481f83f7a40fc1fbd207e0fde903f07ef481f83f7a40fc1fbd207e0fde903f07ef481f83f7a40fc1fbd207e0fde,0xff480103ffa40081ffd20040ffe900207ff480103ffa40081ffd20040ffe900207ff480103ffa40081ffd20040ffe900207ff480103ffa40081ffd20040ffe900207ff480103ffa40081ffd20040ffe900207ff480103ffa40081ffd20040ffe),(0x9f77e1414fbbf0a0a7ddf85053eefc2829f77e1414fbbf0a0a7ddf85053eefc2829f77e1414fbbf0a0a7ddf85053eefc2829f77e1414fbbf0a0a7ddf85053eefc2829f77e1414fbbf0a0a7ddf85053eefc2829f77e1414fbbf0a0a7ddf85053e,0xdf7000436fb80021b7dc0010dbee00086df7000436fb80021b7dc0010dbee00086df7000436fb80021b7dc0010dbee00086df7000436fb80021b7dc0010dbee00086df7000436fb80021b7dc0010dbee00086df7000436fb80021b7dc0010dbe),(0x69d98f3034ecc7981a7663cc0d3b31e6069d98f3034ecc7981a7663cc0d3b31e6069d98f3034ecc7981a7663cc0d3b31e6069d98f3034ecc7981a7663cc0d3b31e6069d98f3034ecc7981a7663cc0d3b31e6069d98f3034ecc7981a7663cc0d,0x8485dcfb4242ee7da121773ed090bb9f68485dcfb4242ee7da121773ed090bb9f68485dcfb4242ee7da121773ed090bb9f68485dcfb4242ee7da121773ed090bb9f68485dcfb4242ee7da121773ed090bb9f68485dcfb4242ee7da121773ed09),(0x20e6678c107333c6083999e3041cccf1820e6678c107333c6083999e3041cccf1820e6678c107333c6083999e3041cccf1820e6678c107333c6083999e3041cccf1820e6678c107333c6083999e3041cccf1820e6678c107333c6083999e3041,0x208f77ac9047bbd64823ddeb2411eef59208f77ac9047bbd64823ddeb2411eef59208f77ac9047bbd64823ddeb2411eef59208f77ac9047bbd64823ddeb2411eef59208f77ac9047bbd64823ddeb2411eef59208f77ac9047bbd64823ddeb241),(0x0,0x0)]
def x243autos : List (List Nat) := [[],[81,118]]
def x243d6 (i : Nat) : Nat := 0x1fd20
def x243l6 : Packing := (1,1,1,0,4,0,0,x243d6)
def x243columns : List ColumnInfo := []
def x243levels : Nat → Packing
  | 6 => x243l6
  | _ => emptyPacking
def x243index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def x243 : Forest := ⟨755,6,fun j => x243samples[j]?.getD (0,0),x243columns,x243autos,x243levels,x243index⟩
set_option maxHeartbeats 0 in
theorem geomx243 : graphValid x243 (boundsBefore knownx215) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx2436_0 : block x243 6 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx2436 : block x243 6 0 1=true := sx2436_0
theorem tablesx243 : checkedTables x243 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block x243 0 0 0 = true)
  · exact (rfl : block x243 1 0 0 = true)
  · exact (rfl : block x243 2 0 0 = true)
  · exact (rfl : block x243 3 0 0 = true)
  · exact (rfl : block x243 4 0 0 = true)
  · exact (rfl : block x243 5 0 0 = true)
  · exact allx2436
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx243 : Lower (varsX 755) (graphGoal 755) 7 :=
  strong_low (m:=755) (cap:=6) (hints:=1358954497) (by decide +kernel) (plainB (q:=243) (prior:=boundsBefore knownx215) (before_sound knownx215 validx215) (by decide +kernel))
    (index_root (g:=x243) (i:=0) rfl (before_sound knownx215 validx215) geomx243 tablesx243 (by decide +kernel))
def mapsx243 : List (Nat × List Nat) := [(755,[])]
def knownx243 := extendKnown knownx215 7 mapsx243
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx243 : Known knownx243 := extendKnown_ok (m:=755) validx215 lowx243 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx317 : Lower (varsX 829) (graphGoal 829) 8 :=
  strong_low (m:=829) (cap:=7) (hints:=12884910852) (by decide +kernel) (plainB (q:=317) (prior:=boundsBefore knownx243) (before_sound knownx243 validx243) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx243) (before_sound knownx243 validx243) (4,0,825,0,7) (by decide +kernel) (by decide +kernel))
def mapsx317 : List (Nat × List Nat) := [(829,[])]
def knownx317 := extendKnown knownx243 8 mapsx317
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx317 : Known knownx317 := extendKnown_ok (m:=829) validx243 lowx317 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx349 : Lower (varsX 861) (graphGoal 861) 7 :=
  strong_low (m:=861) (cap:=6) (hints:=13019128580) (by decide +kernel) (plainB (q:=349) (prior:=boundsBefore knownx317) (before_sound knownx317 validx317) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx317) (before_sound knownx317 validx317) (512,1,332,16,5) (by decide +kernel) (by decide +kernel))
def mapsx349 : List (Nat × List Nat) := [(861,[])]
def knownx349 := extendKnown knownx317 7 mapsx349
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx349 : Known knownx349 := extendKnown_ok (m:=861) validx317 lowx349 (by decide +kernel)
def x437samples : Array (Bits × Bits) := #[(0x37ffc6fcdfff1bf37ffc6fcdfff1bf37ffc6fcdfff1bf37ffc6fcdfff1bf37ffc6fcdfff1bf37ffc6fcdfff1bf37ffc6fcdfff1bf37ffc6fcdfff1bf37ffc6fcdfff1bf37ffc6fcdfff1bf37ffc6fcdfff1bf37ffc6fcdfff1bf37ffc6fcdfff,0x3606c6fcd81b1bf3606c6fcd81b1bf3606c6fcd81b1bf3606c6fcd81b1bf3606c6fcd81b1bf3606c6fcd81b1bf3606c6fcd81b1bf3606c6fcd81b1bf3606c6fcd81b1bf3606c6fcd81b1bf3606c6fcd81b1bf3606c6fcd81b1bf3606c6fcd81b),(0x0,0x0),(0xf1e7ffdbc79fff6f1e7ffdbc79fff6f1e7ffdbc79fff6f1e7ffdbc79fff6f1e7ffdbc79fff6f1e7ffdbc79fff6f1e7ffdbc79fff6f1e7ffdbc79fff6f1e7ffdbc79fff6f1e7ffdbc79fff6f1e7ffdbc79fff6f1e7ffdbc79fff6f1e7ffdbc79f,0x87f77fda1fddff687f77fda1fddff687f77fda1fddff687f77fda1fddff687f77fda1fddff687f77fda1fddff687f77fda1fddff687f77fda1fddff687f77fda1fddff687f77fda1fddff687f77fda1fddff687f77fda1fddff687f77fda1fdd),(0x0,0x0),(0x8bdb201e2f6c8078bdb201e2f6c8078bdb201e2f6c8078bdb201e2f6c8078bdb201e2f6c8078bdb201e2f6c8078bdb201e2f6c8078bdb201e2f6c8078bdb201e2f6c8078bdb201e2f6c8078bdb201e2f6c8078bdb201e2f6c8078bdb201e2f6c,0x89f9200227e480089f9200227e480089f9200227e480089f9200227e480089f9200227e480089f9200227e480089f9200227e480089f9200227e480089f9200227e480089f9200227e480089f9200227e480089f9200227e480089f9200227e4),(0x8c3d39e230f4e788c3d39e230f4e788c3d39e230f4e788c3d39e230f4e788c3d39e230f4e788c3d39e230f4e788c3d39e230f4e788c3d39e230f4e788c3d39e230f4e788c3d39e230f4e788c3d39e230f4e788c3d39e230f4e788c3d39e230f4,0x8b9380022e4e0008b9380022e4e0008b9380022e4e0008b9380022e4e0008b9380022e4e0008b9380022e4e0008b9380022e4e0008b9380022e4e0008b9380022e4e0008b9380022e4e0008b9380022e4e0008b9380022e4e0008b9380022e4),(0x0,0x0),(0x7800ce01e0033807800ce01e0033807800ce01e0033807800ce01e0033807800ce01e0033807800ce01e0033807800ce01e0033807800ce01e0033807800ce01e0033807800ce01e0033807800ce01e0033807800ce01e0033807800ce01e003,0x70008025c00200970008025c00200970008025c00200970008025c00200970008025c00200970008025c00200970008025c00200970008025c00200970008025c00200970008025c00200970008025c00200970008025c00200970008025c002),(0xc646f127191bc49c646f127191bc49c646f127191bc49c646f127191bc49c646f127191bc49c646f127191bc49c646f127191bc49c646f127191bc49c646f127191bc49c646f127191bc49c646f127191bc49c646f127191bc49c646f127191b,0xe746c5b79d1b16de746c5b79d1b16de746c5b79d1b16de746c5b79d1b16de746c5b79d1b16de746c5b79d1b16de746c5b79d1b16de746c5b79d1b16de746c5b79d1b16de746c5b79d1b16de746c5b79d1b16de746c5b79d1b16de746c5b79d1b)]
def x437autos : List (List Nat) := [[],[112,66]]
def x437d6 (i : Nat) : Nat := 0x1fd20
def x437l6 : Packing := (1,1,1,0,4,0,0,x437d6)
def x437columns : List ColumnInfo := []
def x437levels : Nat → Packing
  | 6 => x437l6
  | _ => emptyPacking
def x437index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def x437 : Forest := ⟨949,6,fun j => x437samples[j]?.getD (0,0),x437columns,x437autos,x437levels,x437index⟩
set_option maxHeartbeats 0 in
theorem geomx437 : graphValid x437 (boundsBefore knownx349) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx4376_0 : block x437 6 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx4376 : block x437 6 0 1=true := sx4376_0
theorem tablesx437 : checkedTables x437 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block x437 0 0 0 = true)
  · exact (rfl : block x437 1 0 0 = true)
  · exact (rfl : block x437 2 0 0 = true)
  · exact (rfl : block x437 3 0 0 = true)
  · exact (rfl : block x437 4 0 0 = true)
  · exact (rfl : block x437 5 0 0 = true)
  · exact allx4376
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx437 : Lower (varsX 949) (graphGoal 949) 7 :=
  strong_low (m:=949) (cap:=6) (hints:=22011709188) (by decide +kernel) (plainB (q:=437) (prior:=boundsBefore knownx349) (before_sound knownx349 validx349) (by decide +kernel))
    (index_root (g:=x437) (i:=0) rfl (before_sound knownx349 validx349) geomx437 tablesx437 (by decide +kernel))
def mapsx437 : List (Nat × List Nat) := [(949,[])]
def knownx437 := extendKnown knownx349 7 mapsx437
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx437 : Known knownx437 := extendKnown_ok (m:=949) validx349 lowx437 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx127 : Lower (varsX 639) (graphGoal 639) 9 :=
  strong_low (m:=639) (cap:=8) (hints:=16785665) (by decide +kernel) (plainB (q:=127) (prior:=boundsBefore knownx437) (before_sound knownx437 validx437) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx437) (before_sound knownx437 validx437) (64,0,575,0,8) (by decide +kernel) (by decide +kernel))
def mapsx127 : List (Nat × List Nat) := [(639,[])]
def knownx127 := extendKnown knownx437 9 mapsx127
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx127 : Known knownx127 := extendKnown_ok (m:=639) validx437 lowx127 (by decide +kernel)
def x191samples : Array (Bits × Bits) := #[(0xa7c5ffc2671e45ef489014466d36f1158008452319bd58b4fda954f94fd172f0b0b4f8bff84ce3c8bde9120288cda6de22b00108a46337ab169fb52a9f29fa2e5e16169f17ff099c7917bd22405119b4dbc4560021148c66f562d3f6a553e53f,0x1ff00000781e41f0004120000c126110084001201be40434fd8094510fc0100e4003fe00000f03c83e0008240001824c2201080024037c80869fb0128a21f80201c8007fc00001e07907c00104800030498440210004806f9010d3f60251443f),(0xc08fbf2767806247cc640f16b66da40724bca4986077bba206e76b8ff0b58ee076f811f7e4ecf00c48f98c81e2d6cdb480e49794930c0ef77440dced71fe16b1dc0edf023efc9d9e01891f31903c5ad9b6901c92f2926181deee881b9dae3fc2,0x99d060540300cae240c1623699a07269fac9c6013998200656b8e703f8d6186800133a0c0a8060195c48182c46d3340e4d3f5938c027330400cad71ce07f1ac30d0002674181500c032b89030588da6681c9a7eb271804e66080195ae39c0),(0x4118613f18211e2004799381928c051a3d240929a64a6649325a1520afe06d1d3f08230c27e30423c4008f3270325180a347a4812534c94cc9264b42a415fc0da3a7e1046184fc6084788011e64e064a301468f49024a699299924c9685482bf,0x60f900200e001050d381000404001920400186486265821a00208ec0609c3000000c1f200401c0020a1a70200080800324080030c90c4cb043400411d80c138600000183e40080380041434e04001010006481000619218996086800823b),(0x57b38c0a69fe3817202dec2f11c009e007433bfe0395855a1c55865f314c87464a4af671814d3fc702e405bd85e238013c00e8677fc072b0ab438ab0cbe62990e8c9495ece3029a7f8e05c80b7b0bc470027801d0ceff80e5615687156197cc5,0x505b920241d8502300ab2c3411c2688026433e6a419585987dc1865d31009f62c80a0b7240483b0a046015658682384d1004c867cd4832b0b30fb830cba62013ec5901416e48090761408c02acb0d04709a200990cf9a906561661f7061974c4),(0x3223a8a082ca2490ba54dda9c0785aeac24050959082f9470b04eb32c23ca46fc06644751410594492174a9bb5380f0b5d58480a12b2105f28e1609d665847948df80cc88ea2820b289242e95376a701e16bab09014256420be51c2c13accb08,0xa0046dd58620aa08f210c3cbc22d926fc000c015a0027a43022c69a2c000009137f4008dbab0c415411e4218797845b24df8001802b4004f4860458d345800001226fe8011b7561882a823c8430f2f08b649bf000300568009e90c08b1a68b00),(0x1c44435687b48b0d9b92755299071220e29ffac66d0802d9c01a2beef40ad0b0868388886ad0f69161b3724eaa5320e2441c53ff58cda1005b3803457dde815a1610d071110d5a1ed22c366e49d54a641c48838a7feb19b4200b670068afbbd0,0x4006e37b82800c0d188a54c3910516a3a21d5a9f641892c9021a23aaf0380da0a68800dc6f70500181a3114a987220a2d47443ab53ec831259204344755e0701b414d1001b8dee0a0030346229530e44145a8e88756a7d90624b2408688eabc0),(0x0,0x0),(0x98194014fc1f9032b70620b862810a185893a760dc22050161e5f8551902100b45930328029f83f20656e0c4170c5021430b1274ec1b8440a02c3cbf0aa320420168b260650053f07e40cadc1882e18a042861624e9d83708814058797e15464,0xbfe91c043c47d012670420386ed8084c4482854018230d127de5d855010702414977fd23808788fa024ce084070ddb0109889050a8030461a24fbcbb0aa020e048292effa47010f11f40499c1080e1bb602131120a1500608c3449f797615404),(0x0,0x0)]
def x191autos : List (List Nat) := [[],[115,84],[32,67,117],[32,83,116]]
def x191d6 (i : Nat) : Nat := 0x1418404143580351c935517254940b6528d7258541502ba4a2619414c540
def x191l6 : Packing := (3,5,6,0,4,5,0,x191d6)
def x191d7 (i : Nat) : Nat := 0x18403080000010709061210200000009061010241841a81c44284040c0810027026063414213408201061210283908221d03110f81881340c4004f03102d01882405a031810408281082820b101a0c2418400204000000005001a0034086810d04102c341841608061010200016100c200000040400000004040009430184a140c03080818670ba14c1a81701a00bfc7eefc9f1bd478af01ddbb674ee61c4b7a6c2d49a1b3465ec317eae45beb4160aa851e9d92ea5847e899019fe3de7a8ed9d638e6e0d499a32a618c097c2ee5c8b69682c6550a293624e460848fa1d6370668c81862d0528a0136258488820fa1e03986e0d21682a850082078078008fec8d10bb2811fd92a21755023fb23442eaa047f6488758d408fec910ea9a811fd91a21725033e902b1ae4a067d205535c94097ecb510a928157c9754d52503a7aa8b92a4a057724d7254940afa48ae4a92819dc8758d325023f930bac44a066f21d5488940afac8ceeb0a815dc935c9615023fb2443aa2a057724d7254540cbe43aa4a8a817b49258541503b6ae4b0a82a07ad5896150540cde43aa898a81bb5865053150376904a0a62a07e54c9414c5409becad10b02815dc935c960502be922b92c0a07ad5854158140f6cb1ac098281f395454930503f32c6a0a60a07e654d414c140fd8b0a8298281f99544c530503fa2a298a60a04fd6468848140cfa40aec902819f4815d52050376902aa240a067d2057348140afa48ae4902819f587205205037e10298240a057724d7244140ddac328288281fb141481105022fb2b442eca04f664c80591409ecc9900aa281799932015450237b29442e6a047764e885c9408fac8d10b92818dc83999725031e903332e4a065720e555c940cba40caab92819b481911725023b93119ae4a0675206335c940cea41902b92815cc935ca22502bc922b9444a04f664c8050540bccc9900a0a811f4985ca11502ba926b9422a046f662771014099f4cb0a2028193e776144050347cccc2880a064f6157210140d96c2c44202813b6996044050336ceec0880a06ad9998110140d9b2ab02202819b5726044050374c44c0880a06cd6161110140f8caa2a698281f91414c530502bb126b9400a057c2457280140
def x191h7 (i : Nat) : Nat := 0xb0702e000000000
def x191l7 : Packing := (88,4,6,2,4,11,0,x191d7)
def x191d8 (i : Nat) : Nat := (if i<1 then 0xd7158140efd6158140fbd4158140dfe7754140dfd7354140dfc7254140fbd4154140bfd864c140bfd854c140fdd634c140fdd534c140fdd314c140ff9604c140ff9504c140ff9624c140ff9524c140ff9614c140ff9514c140ff9214c140bfe8848140dfc8748140dfe7748140bfd8648140dfd7648140bfd8548140dfd7548140fbd5448140bfd8348140dfd7348140dfd7248140fed5248140ff48148140dfd7148140fbd4148140fed2148140ff96048140ff93048140bfd8608140bfd8508140bfd8644140dfd7644140bfd8544140dfd7544140fbd5444140bfd8344140dfd7344140bfd8244140dfd7244140ff55144140ff93044140ff920441409fd869dd409fd859dd40dbd849dd409fd839dd409fd829dd409fd819dd409fe885d940cfe77999409fe885d540d7e7795540bf88059140bf88055140bbe8855140dbe7755140fb88055140dbe7791140dbd7691140ebe6691140dbd7591140f3e55911409fe885cd40cfe665cd40d7e555cd409fd8758d409fc8758d40cfd7658d409fd8754d409fc8754d40f3d5454d40dde778cd40ddd768cd40ede668cd40ddd758cd40f5e558cd40f9d548cd409fe885c940cfe665c940d7e555c940dbd545c940dbe445c940ddc835c940dde335c940df4815c940ded721c9409fd861c940cfe661c9409fd851c940d7e551c940dbe441c9409fd831c940dde331c9409fd811c9409fd87589409fc87589409fd87549409fc8754940f3d54549409fc8750940dec7250940bf880509409fd874c9409fc874c9409fc8788940ded7288940dec8788940dee7788940ded7688940eee6688940ded7588940f6e5588940fad5488940fae4488940ded7388940fce33889409fe885c540cfe665c540d7e555c540dbe445c540dde335c540dee225c5409fd87585409fc87585409fd87545409fc8754540bf88050540bbe8850540dbe7750540ebe6650540bbd8550540f3e5550540f9e3350540dbd7250540fae2250540fb56150540fb880505409fd874c5409fc874c540fb5414c5409fd87485409fc8748540df67784540df57684540ef66684540df57584540f765584540fb55484540fb64484540df57384540fd63384540df57284540df47284540fe62284540f3d5454140dbe7710140ebe6610140bbd8510140f3e5510140dbd7210140fae2210140bbd8110140fb61110140bfa884c140dfa774c140efa664c140f7a554c140fb9544c140fd9634c140fd9534c140df9724c140fea224c140fb9414c140fd9314c140ff2114c1409fd8748140dec7248140fb54144140dfa7780140df97680140efa6680140df97580140f7a5580140fb95480140fba4480140bf98380140df97380140fda3380140df97280140df87280140fea2280140df97180140fb94180140ff21180140b3d8510140bb58110140 else (if i<2 then 0x87080021020420018400b130900140850414184081018044230f8903c30a03c4061207860010404182040d04100a09040c10208820a07040e0d0e041800e19109c14090108ca150240c5040181c2c3050903e382050e100042040840030820818204006140806000000808000018406181860610121c5030b21c062522044a20189450381840484140d0803128e0610200c3c162004c06140d0414384001081021000c2030800a102840040a102004018408030ad2767cb32d93ac6f620b005782b935b2ad6d65aaff568aa8d4c6a354faa71d30e95949ea43d19e8a1439a11505280d3ef9ec4ee274338a9b9cd7268b32e98bcc025d32d29594a6e4f726492b48da42d1ff8efc6b631b1768afc4fe23f10887443461870ac84ac1d60ab03e8184066004feb7ea3ed1f3af867bc3d85ea6f457973c5de00ef276dbb35d6ce9f74439e9cb4e437163855beadde6dab679b0ed796b13509a44d02675b32d968ca664c32058e6c5c622b0dd840c125fdaf91788bad5cb2e216e2b5a5a62cd563cb1057cab89584aa254a29f54cca46517a8854149fc4fba7c93c89d64e8a70d36a9b04d1267530c9784b52529254901475234d1788ae450226d11a88843d214508683540aa01cfce7d93e11ef4f4c7983c09dcceca74e3a01c5cddc6ce3529a14cca64e3249910c485fb2e496ecb5a59f2c89630afc5792b59598ab055329e14b8a4051228213d89ac4b624f91fc8f446c22f114084e4192058fac7ba3bd1dc0e846de3461930c185f02ea1728b5c5a42c415f8ac455829e1480a2c4d626613089704ae24912208fc47422c10f08404041e20dc86883041740aa04d024c0fd07c03601940bc05b82a4148096048820c0ea070031015009e04101980b802e000dfc825d540fbc8255140bfe8858d40dfe7758d40bfe8854d40dfe7754d40dfd635c940dfd535c940bfd861c940bfd851c940dfd751c940fbd541c940dfd541c940dfe7758940dfd7358940efd6358940bfe8854940dfe7754940f7d5454940dfd7354940f7d5354940dfd7254940dfe774c940bfd854c940dfd754c940fdd634c940dfe7788940dfd7588940fbd5488940dfd635c540dfd535c540dfd525c540dfe225c540bfe8858540dfe7758540dfd7358540dfd7258540bfe8854540dfe7754540dfd7354540dfd7254540dfc7254540f7d5254540ff56150540fbd6350540fbd5350540fbd6250540fbd5250540fbe2250540bfe884c540dfe774c540bfd864c540dfd764c540bfd854c540dfd754c540fbd544c540dfd724c540fdd324c540ff5514c540bfe8848540dfd8748540dfe7748540bfd8648540dfd7648540bfd8548540dfd7548540fbd5448540bfd8348540dfd7348540dfd7248540ff56148540ff53148540bfe8858140dfe7758140dfd7358140efd6358140dfd7258140df else 0x28088160910341820582840b05084a0d048c4a16080c2400106824200690220286840b04883a0910941283182c14205c1c1430101c41d0541c625018a0e10602c4120006861405083000102c0a202850210483441005083a0a438c4c05102c122058244090708120e102c2420582841e05083c0b10141420d01c083020004268220c626820a0810d21e083132160830602c4240583061202c12061328250e1518482620505441681a046250b05462682084816818c240b109c21205882409105c128718481400185c1424084240b105c16213c1041f00084a24418c040b10260e283840e88141c307081d08283a10401050a0210501441a08061020d42042804085011402108381a1c42884084b0310950f03184e06212058270320960620102c42608144c2048044c304a1c0a3000983430501440b4086860b130910144043481109820b13081684101021840091010900041a09081202008d0f0410280428204348110a004282041602106e0820d845088109a0820085c4830208840303042c2510784821307448314084500085840280840000840210408287080021002c482400502102004423018983831401e0621205c1e213070416100a06143840010810210902812282200281082102281a20384c38586830e1c2c2007442240043a20120428208504a2418414260c87c8010200c2240f8903a300010060f2098481d1e0c0e201848502000081e058c14098189880a048144c242814205082c2))
def x191h8 (i : Nat) : Nat := 0x1c15c02ca087615a809c802205da0fe00d6849300da11241a405320940003c1e001c603d814001448450000000140400006075e01f02a8000b081215d8008052901f20df00ba01d0001c06e8269803509e00c6c0c2039b09dc15000000000000800101500001017252bc130000706c0000c187832d04000018090000803fa0f4000684c0000000181f003b0001202b817b810100a20a480b00000000000140cd84b0000e104c13d825002a0001c077048f04800000000000b0080001006280d50700000411b809904560440006046e06a810bc0a000010a2c0840005047306660b5a27b059aaa608802402cac31800
def x191l8 : Packing := (282,3,6,7,4,13,0,x191d8)
def x191d9 (i : Nat) : Nat := 0x602122820c02c2038b1416101c588300b080e5050502840728281920b0c341610605898201d020160b08324c100e805840304871630c0293121024120c2c7c901ce15063a1708480e70503848728286059393438418620c9610921c14e084c2c30e0583180b24040740f02c18d05920203a01098a062a160a32250e081080b0427248728d8c02c1c204039c6c160e10201cc4810503058483041b8708393140808109860a040e0c4c5062606050084880b8724482818c4214039a12201c60b1108500e584880718341c2140396121c18208360b08110e4a68487081820281c2439418086498849014d0801110e0a526058804872830341934382141a221c106100c284282587082c20043834416126071fddf29e75e01cedbd9b05a7197d8897d570160d5994853712fd1e9135040f6cef8e04db0d3cc68b34a609ec9388c481077c6a863456048c3d83042301bc1680b4003ff3ba81ff5d940ffaeaa07fd64503feaa281ff5cd40ffac6a07fd53503feb9281ff1c940ffac4a07fd52503fea1281ff4c940ffc44a07fd71503feb0a81ff54540ffa82a07fd31503fe90a81ff58140ffaa0a07fd30503fe90281ff08140ffa20a07fe00502ff3ba817f5d940dfccca05fd75503bf2aa81ef55140f7c88a05fd73503ef19a817f5c940bf8e4a07ee22502feb8a81ef50540fec22a07bc40503fc98281fe80140
def x191h9 (i : Nat) : Nat := 0x30048208fd031800030133406be018b0308c03c00000000000028a038084a05e902e0ca00802dc00cf801d01dc600930831840840ae00cb702b282d44051e104e089e824a815b40ae4008d8ad3c1912118c080e92c5817f6023700a5026e8165810b5050b8118c1a280afc07370039801ec107304f9007181f8a06f5006083a880246069e05118458c0568108600d78274c0b72098707d28096422100a6f270401d48207007e00768807f0081e0a8f01d50377c122a4d67077982cc000080820000402c0c17c41111001882d9c009c0170064b81cc00b480516029a8314c5476018f0220013b800a0085103d802700001a0c600005010940fe00009014f823800e1e094707d8000281c98080e041800014040a01da02e40037c0ab2054835b783e2416e0000e060980fb421860bc80219026b0158605f0000302ae01ea80daa017802c5c1ab80f6e07ec0181c1fc06dbd00378449c141e08ba075a8162c07900c00000000000001004a5082f82410229c008e086e0164419f4074201e883d1808bc016e05d301db41ef80bb00000000141e5e0e0d07f8808400000000d06690098809a00008072f02aa41af4013007c883b00000e07ab03290360000140e900004831cc1a9a07d603b8000000014096304ab01b08215e07923861034340d0000000000000201b820f100000000000006062000028330000000000000303cdc113604ff0650011c0000c0c3000000000000062c6503e6940f016800000000402e40000e034b069d00e2805d004b7070e838a80c9c0d92051900fc00000000102f781428002000000003038f412e00008040e039c000000004005800000152000010740000340660000100ae00e640f0e0ce00002000b00140000803558198022ba0885043c037c0000000000000000300600000603900000000000000000280c80000c08d3000100ed8059e037000000001c200806d90621824c01b760dec06b602970dd740a7600dd822ac06bc04c50290000000000000004f281c40000c109000060127c1e0e05d00000045c804400000000000000001c067000000001006c60270000404640001e0862024301b80000a02a8164f9408000000a4c0460000000000000c087d03490083a0610000000400000810e0118111b003503330f07251a2e0700170104007a000004002d06670436000400080202108d0400130d08043a1c05061508080a3c0207121c181d071300134b022c313708052b0706034c
def x191l9 : Packing := (46,2,6,9,4,12,0,x191d9)
def x191d10 (i : Nat) : Nat := 0x82038ffd40
def x191h10 (i : Nat) : Nat := 0x404c0002026c06b00a419803302a0000000404b400a06f028e05d42460780005083c1500014274068c2dc00400000000000000c2cd0a4c16f051c210001404606100bd040000900e40840380000014000f03e422602bc07000280dc07c0255070823f09b4111076c2b00006981234001000080
def x191l10 : Packing := (1,1,6,6,4,0,0,x191d10)
def x191columns : List ColumnInfo := [(128,0,575,0,8),(32,0,671,0,8),(528,0,175,0,8),(8,0,695,0,8),(2,0,701,0,8),(4,0,699,0,7),(513,0,190,0,7),(160,0,543,0,7),(536,0,167,0,7),(0,128,539,36,6),(512,32,30,129,6),(512,16,166,9,6),(512,8,163,20,6),(136,0,567,0,5),(130,0,573,0,5),(640,32,30,1,5),(40,0,663,0,5),(32,128,539,4,5),(529,0,174,0,5),(528,8,163,4,5),(12,0,691,0,5),(10,0,693,0,5),(520,16,166,1,5),(6,0,697,0,5),(4,128,539,32,5),(516,8,163,16,5),(513,32,30,128,5),(513,16,166,8,5),(168,0,535,0,4),(164,0,539,0,4),(162,0,541,0,4),(134,0,569,0,4),(641,32,30,0,4),(36,128,539,0,4),(540,0,163,0,4),(538,0,165,0,4),(537,0,166,0,4),(532,8,163,0,4),(531,0,172,0,4),(14,0,689,0,4),(521,16,166,0,4)]
def x191levels : Nat → Packing
  | 6 => x191l6
  | 7 => x191l7
  | 8 => x191l8
  | 9 => x191l9
  | 10 => x191l10
  | _ => emptyPacking
def x191index : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 6 0 10 2 4 x191h7
  | 8 => lookupWord 22 120 5 15 7 4 x191h8
  | 9 => lookupWord 74 387 8 17 9 4 x191h9
  | 10 => lookupWord 11 61 6 14 6 4 x191h10
  | _ => fun _ => none
def x191 : Forest := ⟨703,10,fun j => x191samples[j]?.getD (0,0),x191columns,x191autos,x191levels,x191index⟩
set_option maxHeartbeats 0 in
theorem geomx191 : graphValid x191 (boundsBefore knownx127) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=2) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx1916_0 : block x191 6 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx1916 : block x191 6 0 3=true := sx1916_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx1917_0 : block x191 7 0 36=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx1917_36 : block x191 7 36 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx1917_38 : block x191 7 38 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx1917_74 : block x191 7 74 14=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx1917 : block x191 7 0 88=true := (@block_merge x191 7 0 74 14 (@block_merge x191 7 0 38 36 (@block_merge x191 7 0 36 2 sx1917_0 sx1917_36) sx1917_38) sx1917_74)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx1918_0 : block x191 8 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx1918_2 : block x191 8 2 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx1918_38 : block x191 8 38 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx1918_74 : block x191 8 74 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx1918_110 : block x191 8 110 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx1918_146 : block x191 8 146 8=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx1918_154 : block x191 8 154 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx1918_190 : block x191 8 190 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx1918_226 : block x191 8 226 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx1918_262 : block x191 8 262 20=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx1918 : block x191 8 0 282=true := (@block_merge x191 8 0 262 20 (@block_merge x191 8 0 226 36 (@block_merge x191 8 0 190 36 (@block_merge x191 8 0 154 36 (@block_merge x191 8 0 146 8 (@block_merge x191 8 0 110 36 (@block_merge x191 8 0 74 36 (@block_merge x191 8 0 38 36 (@block_merge x191 8 0 2 36 sx1918_0 sx1918_2) sx1918_38) sx1918_74) sx1918_110) sx1918_146) sx1918_154) sx1918_190) sx1918_226) sx1918_262)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx1919_0 : block x191 9 0 18=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx1919_18 : block x191 9 18 28=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx1919 : block x191 9 0 46=true := (@block_merge x191 9 0 18 28 sx1919_0 sx1919_18)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx19110_0 : block x191 10 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx19110 : block x191 10 0 1=true := sx19110_0
theorem tablesx191 : checkedTables x191 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block x191 0 0 0 = true)
  · exact (rfl : block x191 1 0 0 = true)
  · exact (rfl : block x191 2 0 0 = true)
  · exact (rfl : block x191 3 0 0 = true)
  · exact (rfl : block x191 4 0 0 = true)
  · exact (rfl : block x191 5 0 0 = true)
  · exact allx1916
  · exact allx1917
  · exact allx1918
  · exact allx1919
  · exact allx19110
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx191 : Lower (varsX 703) (graphGoal 703) 11 :=
  strong_low (m:=703) (cap:=10) (hints:=536879361) (by decide +kernel) (plainB (q:=191) (prior:=boundsBefore knownx127) (before_sound knownx127 validx127) (by decide +kernel))
    (index_root (g:=x191) (i:=0) rfl (before_sound knownx127 validx127) geomx191 tablesx191 (by decide +kernel))
def mapsx191 : List (Nat × List Nat) := [(703,[]),(891,[118,130,81])]
def knownx191 := extendKnown knownx127 11 mapsx191
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx191 : Known knownx191 := extendKnown_ok (m:=703) validx127 lowx191 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx223 : Lower (varsX 735) (graphGoal 735) 9 :=
  strong_low (m:=735) (cap:=8) (hints:=553656577) (by decide +kernel) (plainB (q:=223) (prior:=boundsBefore knownx191) (before_sound knownx191 validx191) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx191) (before_sound knownx191 validx191) (128,0,607,0,8) (by decide +kernel) (by decide +kernel))
def mapsx223 : List (Nat × List Nat) := [(735,[]),(1017,[118,130,81])]
def knownx223 := extendKnown knownx191 9 mapsx223
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx223 : Known knownx223 := extendKnown_ok (m:=735) validx191 lowx223 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx247 : Lower (varsX 759) (graphGoal 759) 9 :=
  strong_low (m:=759) (cap:=8) (hints:=553648385) (by decide +kernel) (plainB (q:=247) (prior:=boundsBefore knownx223) (before_sound knownx223 validx223) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx223) (before_sound knownx223 validx223) (64,0,695,0,8) (by decide +kernel) (by decide +kernel))
def mapsx247 : List (Nat × List Nat) := [(759,[]),(1011,[118,130,81])]
def knownx247 := extendKnown knownx223 9 mapsx247
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx247 : Known knownx247 := extendKnown_ok (m:=759) validx223 lowx247 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx251 : Lower (varsX 763) (graphGoal 763) 8 :=
  strong_low (m:=763) (cap:=7) (hints:=1358970881) (by decide +kernel) (plainB (q:=251) (prior:=boundsBefore knownx247) (before_sound knownx247 validx247) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx247) (before_sound knownx247 validx247) (64,0,699,0,7) (by decide +kernel) (by decide +kernel))
def mapsx251 : List (Nat × List Nat) := [(763,[])]
def knownx251 := extendKnown knownx247 8 mapsx251
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx251 : Known knownx251 := extendKnown_ok (m:=763) validx247 lowx251 (by decide +kernel)
def x319samples : Array (Bits × Bits) := #[(0xfa8093ffcc0fae3c464af89bf6824ed180a97830048c0cfdfe1d7a53b3cfd206e73f50127ff981f5c788c95f137ed049da30152f060091819fbfc3af4a7679fa40dce7ea024fff303eb8f1192be26fda093b4602a5e0c0123033f7f875e94ecf,0x71001019a0880e21000af22440045610000008311000803dfd1d4a1033d0010040ce200203341101c420015e4488008ac20000010622001007bfa3a942067a00200819c400406682203884002bc89100115840000020c4400200f7f4752840cf),(0x881bf52aef8122901c77096b3ec3498d3c97a56f63e62fe02ad2a5bfcc804a38b031037ea55df02452038ee12d67d86931a792f4adec7cc5fc055a54b7f99009471606206fd4abbe048a4071dc25acfb0d2634f25e95bd8f98bf80ab4a96ff32,0x861bc4a24f5421904414090b368280cdbfd3a74e69e60ec00282a4afc420f07aa130c3789449ea84320882812166d05019b7fa74e9cd3cc1d800505495f8841e0f5426186f12893d5086411050242cda0a0336ff4e9d39a7983b000a0a92bf10),(0xe1052659a38240c50bbd82e00a797f34642c0141df39f3128cfc51481fdd0b9058dc20a4cb34704818a177b05c014f2fe68c8580283be73e62519f8a2903fba1720b1b841499668e0903142ef60b8029e5fcd190b005077ce7cc4a33f145207f,0x11843204208a502f0aa1c6e000397f20402c10818619f13c9c7c51401b9f07810e8230864084114a05e15438dc00072fe40805821030c33e27938f8a280373e0f021d04610c810822940bc2a871b8000e5fc8100b042061867c4f271f145006e),(0x706e8121d304141b1cc0586517482fb4b1046063967c08a81098e31655fa1f910c0e0dd0243a60828363980b0ca2e905f696208c0c72cf811502131c62cabf43f22181c1ba04874c10506c730161945d20bed2c411818e59f022a042638c595,0x840000205c31a04091440109114480c21200444239260083630182116440000610308000040b8634081228802122289018424008884724c0106c6030422c880000c2061000008170c68102451004244512030848011108e498020d8c06084591),(0x2cf806811ef465223e805d21a810148aaa7816920641175501e5a0ec8a1061068f059f00d023de8ca447d00ba435020291554f02d240c822eaa03cb41d91420c20d1e0b3e01a047bd19488fa017486a040522aa9e05a4819045d54079683b228,0xae5e3c20046418e60b104908e992809e0fab38406413f4000e030ee880fa6f0af015cbc784008c831cc16209211d325013c1f567080c827e8001c061dd101f4de15e02b978f080119063982c412423a64a02783eace101904fd000380c3ba20),(0xd87a6164034b980e7a44a793bfc8b8c3da42dbc8c89970025622d3efdc229c32483b0f4c2c80697301cf4894f277f917187b485b7919132e004ac45a7dfb845386490761e985900d2e6039e9129e4eff22e30f690b6f232265c009588b4fbf70,0x8c53a1444b61b05c7ae00493abc0a8e3fa1e73ca699d6402026091ebcc03dcb213318a7428896c360b8f5c00927578151c7f43ce794d33ac80404c123d79807b964266314e85112d86c171eb80124eaf02a38fe879cf29a6759008098247af30),(0x0,0x0),(0x0,0x0),(0x2fe4803804611068410822445bdf714114388bda4529b2c10222c8473a4076948e05fc9007008c220d082104488b7bee282287117b48a5365820445908e7480ed291c0bf9200e0118441a1042089116f7dc50450e22f6914a6cb04088b211ce,0x73ac4c9b8086418204137a64043b111c05e1883586409b7c9c822c0413bc2341444e7589937010c83040826f4c8087622380bc3106b0c8136f93904580827784682889ceb1326e02190608104de99010ec4470178620d619026df27208b0104e)]
def x319autos : List (List Nat) := [[],[81,130],[48,33,133],[48,129,82]]
def x319d5 (i : Nat) : Nat := 0xa20dc5d10ecaa82982813c46d4a8505314c140
def x319l5 : Packing := (2,6,6,0,4,3,0,x319d5)
def x319d6 (i : Nat) : Nat := 0x584058405840584058400001b081b080003c202c20000b081e01620016080007820053a93449fcea6b3095c9a431c8bc1deee76bb1d84bd5c2a13093471f8dc693215072341207c340a028029ada49dd8210d40aad6984360440502ba5a210d811014086f6929961d305031b487644844c140ce364d92211305032b596644844c140ccd65591211305033a592644844c140a4f694845c9305029b9a4a20874c140c6e650879dd3050378993648844c140dac659912113050373195644844c140de464d91211305037a192644844c140cec21d91211305035b087644844c140be46848450d30502d39a5211724c140b6c684845c930502799a424d624c1409f46849358930502739a5261414c140e6c68487505305023b8a8655414c140c6e21d95505305027b0a9605414c140e6c21d8150530502f19a5211314c140b7429d514c530502f90a8505314c140f6421d414c530503d9176505314c140d6c25d414c1105031b087644844c140
def x319h6 (i : Nat) : Nat := 0x241c1
def x319l6 : Packing := (37,5,6,1,4,9,0,x319d6)
def x319d7 (i : Nat) : Nat := (if i<1 then 0xd544c540afa4bac298a815f497545315027e930a0a62a076d5d9414c5408fecc4ee202819de7760c40502f5b2421880a067b9dd8210140cf6b9b04202818fd865c8405033bb06b9080a06e760d4210140cfb3bb02202819f5766044050376ac8c0880a067d5cd8110140dda21b02202819f5726044050376a84c0880a04ef652884c1408ff4cb0e982813bc9421d30502b792843a60a047fa64874c140aeec9cee982813ed92211305027eb2242260a066f21c844c140bdac8908982819be772113050373b2642260a06eb648844c140ddac8908982819bc845cd305023f930b9260a066f211724c1408fe4c2e2982819bc845c53050277930a0a60a066f21d414c140bf4c9080982817f19110130502f732944260a05ee250874c140cfd4410e982819fa9921d305033f32843a60a067e64c874c140cfcc890e982819f8879dd30502fb3273ba60a05fa648844c140bf8c890898281bb88721130503b710e42260a07e664c844c140fd4c9108982817b99121130503f632242260a05f624e444c140cfc43ae698281dd88750d30503f3108a1a60a05fa648434c140bf8c8886982815f89760930502f7128c1260a04fe261724c140afc4c2e498281db8845c930502fb126b1260a057e25d814c140cfc43b02982817b894605305027f130b8a60a067e21d714c140afc4baa2982819f88754530503f3286a0a60a05ee261414c140ddc43a8298281db88750530503b72eca0a60a05ee655414c140fd8c0a8298281fb1414c530503bb10e98a60a07765d9314c140beccaa62982817d9944c530503f310898a60a07e6551314c140fe8b0a6298281fd1514c530503fa28298a60a047f662770c1409fac8d10902811fc97619205023f92ec1a40a04ef25183481408fe4bb0c882811fc97615105023f92ec1a20a04ef2518344140edabb28288281db47350510502bf12e98220a07ec50530441409deca107002813f59120e005027f32041c00a047f2617280140afc4ba61002819fa889de005033f510b9c00a047d644839dd40adc4bb01222811bd94a217350237931222e6a047b648841cd408fac890839a811f99021073502ba922c3c66a047d646885c9408ee49b0eb12813d99320141502f332640282a046f66277101409db4cb02202819b6776044050336aecc0880a06ad9998110140cda39b0220281b96336044050336ae4c0880a06e98898110140d9ac2c22202811f897a20405023f3313b880a04f6a658310140ced3bb0620281b9a4460c4050379306c1080a06f260e2210140de8c1b0220281be182604405037a30708880a046f250874c1409dac8908982811fa9921d305033710e42260a05ec644844c140cdc43c88982819d88750d305033b10f19a60a047e261724c140cf443c44982819b88750530503f228298a60a067c21e114c140 else (if i<2 then 0xb001002c0a880f080810002005815100000040000000b02a2002c1001610868610161002c0ad02303c205840b0800b0800002c205840002c205840002c205841603c405840b0800b0800b08161a1820586860836106c2060681083c05880b0d021000810000f0d02103c20f041605404190c1078861502107820002c105820058200000048400001410582000021000010016100c3020400000010001703c4005c0f10021060c0c0800000000000000000000000000002c20d842202c20b81e205820584005841ba18181d0c10780f102c430a810cbf4bccba4b7cb54adca649ec97494c9248fc88480c79471c6f467c65462c6045dc5b458c56453c5144ec4c449c47444c4243fc3d435c2e42bc2441cc1a417c15412c1040dc0b408c06403c013febfc3f9bf23eabe83e5bde3d6bd43ccbc53bdbb63aebac3a9ba73a4ba239fb9d39ab8e38bb7f37cb7a377b75372b6b363b5c359b5234ab4833bb3432cb25322b16313b11309b07304b022ffafd2f0aee2e6ae42dcad02c8ac62b4aad2a5a9e29ba94291a8f28ca8527da7b278a71269a67264a5d255a49241a3a237a3022da2621ea1720fa082009f91f19ea1dd9d61ce9cc1c49c21bf9b81b09a91a199018897c17496d16a96816095915694f14c94a14794513d93b13893612e92712492211a91811090e1068ff0f78f50f28f00e88e60e38d70d48c80c08be0b18af0ac8aa0a78a50a28a009d89b09889609389108e88c08988708488207f87d07a87306685f05284b0438410398280208140078004fd644839dd40ddcc23013ba819dd8320e77502beb2241ceea047f640839dd408fe4bb07222813f99020e44502b7b29442e6a057764e885cd408feca510b9a819bd94a21735023f931222e6a056f652771cd408fec810839a815dd939dd435023f92f44086a047f6627710d40adeca4ee21a81aed86608435033dceec1086a06bd6198110d40dbac2b0221a81be582604435033eceec0886a06fa6098010d40df8c0b0021a811fe9921e335023f92ec1466a047f25d818cd408fe4bb0119a819de8821e335027eb23442e4a047f642885c9409ee49b0eb12811fd9321d625023fb2e41ac4a04ef65083589409fac8906b12813f99020d625027f32144284a04f724d865094097ecb106a128137d9520d425027eb2241a84a047f25d864c9409f64c284992811fd93a21715029fb2c21ae2a055f654435c540af6c9086b8a811fc988cd715023fb2643ac2a047f65c83585409beca906b0a813bd9420d615027f32041ac2a047f64c87545408fecb906a8a813bd9420d515027f32041aa2a04df6548350540b5ecb086a0a8173d9510d41502f5b2421a82a05cf6548350540bdcc8106a0a815bd961cd4150337b0a39a82a056f25d63505409f6c951098a811fc97619315023f92ec2a62a066f21 else 0x584000800100020000840816100020204042040000000000000000000000384040800b080010000000000000000000408161000040816106021c0438087010e021000000000005a061001e8184000000a18343040408185))
def x319h7 (i : Nat) : Nat := 0x418c008d04a802307180a004cc23f06dc062118857c114000203bc0bc01e01171214223344418508301a0000000a17841e00010524085416400dc5300010154143c51f162800a025001000241f703741d103c000c16c000000306000000000000000c050000000184d00000004016c197090000717e0101101c0cb15600452464177e460faa340549
def x319l7 : Packing := (233,4,6,6,4,12,0,x319d7)
def x319d8 (i : Nat) : Nat := (if i<2 then (if i<1 then 0xd314c140ff8404c140ffa884c140ff8874c140ffa774c140ff8844c140ffa444c140ff9734c140ff8734c140ff9434c140ff8434c140ffa334c140ff9824c140ff9724c140ff9624c140ff9424c140ff9324c140ff9814c140ff9714c140ff9614c140ff9514c140ff9414c140ff9314c140dfe770c140bfd840c140dfd730c140bfd820c140bfd810c140ff9300c140bfe8848140dfe7748140bfd8648140dfd7648140dfd7548140bfc8448140fbd5448140bfd8348140bfc8348140dfd7348140fed6248140fed5248140fed4248140ff93048140bfe8844140dfe7744140bfd8644140dfd7644140bfd8544140dfd7544140bfc8444140fbd5444140bfd8344140bfc8344140dfd7344140dfc7344140ff55144140ff54144140ff93044140dfe7780140bfc8480140bfc8380140dfd7380140dfc7380140dfd7280140ff93080140dbd849dd409fd839dd409fc839dd409fd829dd409fd819dd409fd809dd40df9809dd40bf98091140dbc8791140dbe7791140bbd8191140fb980911409fe885cd40dbe445cd40ddd731cd409fe881cd409fc841cd40dbe441cd409fd821cd409fd811cd40df9801cd409fc8750d40bf88050d40bed8210d40bf58110d409fd878cd409fc878cd40ddc738cd40bf8808cd40ddd878cd40ddc878cd40dde778cd40f9e448cd40fd8808cd409fe885c940dbe445c9409fc835c940dde335c9409fd87589409fc8758940bf880509409fc874c940dee7788940ded7688940eee6688940fae4488940dec7388940fce33889409fe885c540cfe665c540dbe445c5409fc835c540dde335c5409fd87585409fc87585409fd87545409fc8754540bf88050540bbe8850540dbe7750540dbd7650540ebe6650540bbd8550540dbc7350540f9e3350540fb880505409fd874c5409fc874c540fb5414c540df67784540df57684540ef66684540df57584540f765584540fb55484540fb64484540df57384540df47384540fd63384540bdd8310140bed8210140bf58110140dbe7710140dbc7310140f9e3310140dbd7210140fae2210140bbd8110140fb61110140bfa8810140dfa7710140fba4410140bf98310140fd98310140fda3310140fe98210140fea2210140ff18110140ff211101409fd874c1409fc874c140bbc844c140ddc734c140bfa884c140bf8874c140df8874c140dfa774c140bf8844c140fb8844c140fba444c140df8734c140fd8734c140fd9434c140fda334c140df9724c140fea224c140fb9414c140fd9314c140ff2114c140fd9300c140bbc8448140bbc8444140fb541441409fc8780140df88780140dfa7780140bf88480140fba4480140bf98380140df97380140df87380140fda3380140df97280140fea2280140df97180140fb94180140ff21180140bb58110140bd983101409f8874c140 else 0x11a87642b209103e7f63e69e90ec07523901c48e1a7083819bd4d986be34f1a40ce06503259888c2860630097f0bdc5e92e016c8b485842bb1558a6c51f27f93e89d84de25f12c092048223a11bc89e4262030fe07d43e51eb8f487883bf1d88e8c73c36c1a18c446183071810bf45f02f31770ba45c82df16d0b545a02cb1630b0457828a123085041e20a0f086e03661a50d0066c32c1910c6061c2f216b0aa051827013309704802120d7064831016c0b1051827812008b03e81e00d405c02b8124076000fbd849dd40bfd839dd40bfc839dd40bfd829dd40bfd819dd40ff9809dd40dfd849dd40dfd839dd40dfc839dd40dfd829dd40dfd819dd40dfd809dd40dfd409dd40dfc8791140dfe7791140bfd8391140bfc8391140bfd8291140bfd8191140bfd8091140fbe8891140bfe885cd40dfe775cd40dfe885cd40dfe445cd40dfd815cd40bfe881cd40dfe771cd40bfc841cd40dfd731cd40bfd821cd40bfd811cd40ff9801cd40dfd801cd40dfd401cd40dfe7750d40bfe8810d40dfe7710d40bfd8210d40fed8210d40bfd8110d40ff58110d40ff98010d40bfd878cd40bfc878cd40dfc878cd40dfe778cd40bfd848cd40bfc848cd40bfd828cd40bfd818cd40bfd808cd40ff8808cd40fde888cd40bfe885c940dfe775c940dfd765c940bfc835c940dfd735c940dfe445c940bfe8858940bfd8758940bfc8758940dfe7758940bfc8458940bfc8358940bfe8850940dfe7750940bfd8650940dfd7650940bfc8350940bfe884c940bfd874c940bfc874c940dfe774c940bfd864c940dfd764c940bfc844c940fed624c940fed424c940bfe885c540dfe775c540dfd765c540dfd755c540bfc835c540dfd735c540dfc735c540dfd645c540dfe445c540dfc835c540dfd635c540dfd435c540dfc435c540dfe335c540bfe8858540bfd8758540bfc8758540dfe7758540bfc8458540bfc8358540dfd7358540bfe8854540bfd8754540bfc8754540dfe7754540bfc8454540bfc8354540dfd7354540dfc7354540bfe8850540dfe7750540bfd8650540dfd7650540bfd8550540dfd7550540fbd6450540fbd5450540fbe4450540bfc8350540dfd7350540dfc7350540fbd4350540fbc4350540fbe7750540fbd7650540fbd7550540fbc8350540fbd7350540fbc7350540fbd6350540fbe3350540bfe884c540bfd874c540bfc874c540dfe774c540bfd864c540dfd764c540bfd854c540dfd754c540bfd844c540bfc844c540fbd544c540ff5614c540ff5514c540ff5414c540dfe7710140bfd8310140dfd7310140fbc4310140bfd8210140dfd7210140fbd4210140bfd8110140bfe884c140bfc874c140dfc874c140dfe774c140bfd844c140bfc844c140fbc844c140dfd734c140dfc734c140dfd724c140dfd714c140fbd414c140fd) else (if i<3 then 0x20681c41a0a880040868102003004011868102060281030203c40105080e041216022040105010c0500242c04416078a02180842c0f105a0220b40440f80858685808a0210b404501085a02280843c16808c3c0a100c200f4181430380c407832143c40400c0030f0220c30501006304182c200042c06010c0c1006c200b05442004881286101020f0b08361000361001020006c209430814140858416408816106010400581040b0810162003021b082c2040608228610450c2080422108850c100402007843c86100000f00c41609881810488040983080e02008d0b06141820408120c2048045060c182060008041030104118308260f100414203808485808810180840810b040616140430108301420a8084040c0420003021b08320821004081020414090401c4017306c3c1818643e20605c4230f05c40b085c000f18102000841610d82810070a064c0002c401818782e206043c1f10784220d878303000582a110d9401e080503040807c3021207804060c1014090401c08200b9c1810b05422100214181000004088010070f920c10dc18303830405060e8e0c040c8c008038103c483050a10020c1004c10071091001008437060c0c021018083a3830103430f038506020686000840210f2160c3808408210e0c3c1808400302848608038103c40f01842380850a104042042841010c04200de1702210e170a210f87081b07e14421c28000000000000000000000140803850325050202210020782e70d8582b86c29400088430c182618201f0b9000b0800000001f0a1821643090c140840002040821106c12000785ca0408016100102006040860800214084004082c21b07e183a1f0b9b2b394bc9ee49b21f90ac82e4031f78edc6fe36b1878b5c58628b12987dc2ee163083833c12e05f025804bfb5fa2fc77debe3dec2f5779dbcc5e06ec375cba2dd02e53724b8fdc22df56f5b73db42d976b4b4ed9f6cdf658b2558aac27605afbd782b935b2ad6d65ab23571ab1d532a6b51ea8853e69d74e6a67d30694349ca4752268e545ba26d0fe863423a0f50428053fd9f34f3e7833b39ce4e3a7133729b6cd5a67f328991cc565fd2f996ccb0a54528b93a497648d22f910c82a3e71dc8e747023531928bdc56e28913688fc4461f50ec86642d614f0a284141ae0850228013f89fbafc67dc3e61f14f857bbbdc9eb6f44796bc7de10efa77abbc1dc4edd767bb29d8aeb77503a49cf6e6472b38fdc74e2370ab7f9bf2deb6eeb73db70da16c535f1adcd606a93535a7ed3a6963455a20d0b68333bd9b0cca659b2718f8c6562bb125864c1b606affd7d0bda5e1aeb172ab7e5b3ad41684b345932c61602af3572ab3956eaa954daa59522a8353aa9794a0a4251a27e53b29c24d1262d2fa95d4a7a52927892e479a3b91d28c94592291 else 0x6c20c082406200858400000860a04200581040b08016106044001105826031801604106c20c086c2043040810604000f00c41e0b0801b080180410100c051803c091001e161000020088081003020c02080090208140410300401183020c0208401100260c3832145060c1822083083207100802200640e2000c000c188020910080e0412160c283043c091004200f02440708780e85180001004c1e2050044850c043010c0420400426100300e20d82840a082820d038804100340e2003))
def x319h8 (i : Nat) : Nat := 0xa0bec00c60df00000000e148005c105a40490034000060668040c092019600000000e10d9185a07550e01176a18fa006b0d2c144d04240ded0e6f1770000215f30a9708f00784085000000004166807db080a167503120ac91000000c17c50308346d000e1d55183000000000000b0c111bb20c5e07600000000717a203241cf207760e8c19100000000e14f101900000000f03500830000217f00000000b01c70710000611a000070e7000091ab00b3405840b2d07f6178f1d4d02501a60000f0cee07430c8a110b08800000000908d603810c3309100000000f044c05df0db00000000000020bb00b42192000031aa5251301a006a0000206dd081000000000000f351910f90d330e510aa60895103009640a620afb0c9406eb1c3900210040000f1994062c09d10c40000f08e109ad0ba50bcd02070e24145f0b9505481570000a0870000000020a78084704d7111203d0000f0d5a0290000d0d700004125f1860000d005a016f07cd05910450000d206b246e108c1460000600ff0e49051402fe0c0e0b12128a01100009008702ca263e11e000000b7400a808c8026f102e0a020a3d0630099004bb0cc10c7019dc0ca00000000a01200000000905090d1c11c0000000081800000506c0000c00100000000000000000000b09b0000d064b01e00000000c16ba0cd516f1055301f82900000d0a1f151a1e85007e03f3028909c0000000080dda01390185195b0a2000070b5b05b706b20530000503af057304e1009c193306f22972039907b0000e1b980100000000090a50000c08ae0673154d0274160d1d1e19e002e303b00000000f15a0000a0cbc0210000b04aa198a03c0000404cc024b0334014909390487262b0b6e0b871e521a43003a041516520da30a41061200e0065000000000000000061d0d098902a0000f09f0000e0e1000010470000c194a07a5190914e911bf01d4015506020232094b0dc905650ad2070d0bf0000b0d4409e112781b8908210d63197c10bd13210d800000068014d40a8000030ab902df0ae209000727017b0526097411d90e3601b8073700b000070d010bd00008046000040b0f05f00000000b0220000b12c8043207e000000008142f037f08bb0690000f03e8095a135505e7079a0d950c28149603600000000216c102b804f00000000000010cf60c60117200d20860008001082c5800a0800c003018b100038408640860c004020235154001c6000404d960040202020031b14000025e44090200c1821430a23061c28856080031224100080420a
def x319l8 : Packing := (370,3,6,8,4,13,0,x319d8)
def x319d9 (i : Nat) : Nat := 0x4868518d824342921a1442220090d0a5041b868520882084342944410421a14a230a0c31904100605288824283107810461418b0a0c20d0410060528d020a83029458121418814083d0a0c51b8581211c043434288407c54846010c230a0c3850610b0ac342821410021a148010d0a08486851020802c30d8f8c1c021a146230a0c3850610b42830c105a141890a0c204085861a144010d0a08496f24a3ec50856ff9e8bb470ed899ab205e6b1950a7447e8a8fa9d8386658b894c26e3e86e8c01562383485408e0e812800ffceea07fe44503feb9a81ff1cd40ffa86a07fc43503ff19a81ff5c940ffac4a07fd42503fe99281ff5c540ffac2a07fd51503fea0a81ff4c540ff880a07fd30503fe18281ff48140ffa20a07fe00502ff3ba81ef91140bfae6a05fc73503ef19a817f5c940fdc44a05fd71503dea0a81fd84540f7880a07f840503fc98281fe80140
def x319h9 (i : Nat) : Nat := (if i<1 then 0x75803e202578286c5c5e10a7008f03b580d2603dd093f001c019e0000000020c5242dba2cef0615803d06040000c103485bc00016205109170a940000a301737d489d3008bc312000000002c1cc00002032981b50111a29a9001d8203c15940c70000000000001a0db0000188f80df0e0a0302958b6a09f4608d00002006081ce00009193a81db042fc07e706288b37454841440000000034275405d00001093341ca82dc102e308ac0001224b4012180a780172558d19b885918251c04d81779830280c1a154000078813465da2159175900988eb0a2ab803911399c00d422c4022481ee82a02097a11ec836244c1a15c414080003c62c000081b3881e0c18c0000724b80001013f608a503be8274000120f1a19000001c6b00000214e70213481480c9402d8080c00006034e009000000000c0e4505b98578000000000000500e040286043907ab08d040578171919b583e7c0762037000000001c212654ea11b70504405066970000302aec203e273718860c540000000061a040dbb82d6607c20a1800018042e138b06a80000c5f06081d15470bda4001e0eaa114e093e829e00000151000000000405f303600002826466a6804a80003c65202f70000402e844b5e05990070011e4221e0f050b100001c083c11b6094d88eb4526e0498029802c20565a3238037a0c7000000000b07400001c26e201f000000c0f804e40878065502a4811240aac03a7047d449c6296000000003c5c860fee0b04837001d6806e000068914000000f4000070248827c000041769829c0000833f712b5041000000000309b4010981a400003018800000000230d00005007bc69700dd018ca02f742460000a09600002010600008070200d8846ba14e3017a045c0001401ca0a69038dc2662106f0312000685f4613f6122103fc00006147413080003c218850650b478445c0d7e0336031e0b024189848f81790824541a3800dd006001eb42250716603f800024078e102000020b9f002e600af1b6b052e0235c11d00006808a457e000080479049004d0000000004037c0000836020264812cc17882fcc0b50811a01de610dc04350533026a02ac4057512980000a11ed089883340001210750459013d89a800e28051c8497c0080000308580003406a0000208c00003c28b602c607eb992400000000d14f08a200001a093000010358413220de000000002c695e16c000078af1c060000000005026180e7a12a010009070301033e370d0c020217041c0d030620010508041802141a10040a0b0a0400030e00000d0702000e01070f230209010d05030221030403030b000e02000200291d10001e000906020106050102071b0400009201380304063a041915000b050001000d3a000405120207080001181b083d0d040006010d2b0209000a0003b32504001f0306 else 0x204b000000000a233612808809426200000000404f380c3e216000000000813d20ec00000000180740000d0a9800000001c449000010af442b60000e15b4004c00006005d02b800000000c22a000058b9bc0cfa63f000000c6a05e882ccc08a00554000063530028b8919419d824900000000342c683520000102fe40d000ad207c78aea807ec259712f50bfc00004048d053184bcc9bc0000000008d2341ec0000518d80002409c8040000000000000000000000000034276000020b3800000165612be01c8000000012295809c80003c62fe1030000181a800000000c15c905a401280000100ea8a7fc0c9c2990000002bc827a0000702ac10fc820a802e005df83de426980eeb0b7602e105fdc0705079d0503c261001a110cb02c7c17ca0569008705940000405e917899459c50f42ae708b58525c04a00007060d02d641382090000070c95c541a142304600002411dc0b92090088fd80b0c1082196303438295c266708020025456e000000005890385d20000e02d000000001600870acb005b8476c020b17ce02d00000e0f26167f8519022a62f000002081c0000c0fb000040549416c215831a48000301b44170005200003448224f87038e054400000000907d38216c19900d4b02a180cac1a60000000058484c562601bf18f80000c1f9a09a00b0904b40000a02de03ec8a3746be0000b074e832f400460a5d087e03674576c079704db04380001c12ec0b31030c00012475b00cd049b41908082c0af8000180a14157d13c78b670238000011b420a9a098680a80000100aa00cc000080a4481d704f2015a000000002c5d462db910c18558000000000154c8288004706e640aea02cd41ae4243600a80002023262f5114ba895fc4bac25c000048384c6)
def x319l9 : Packing := (36,2,6,9,4,11,0,x319d9)
def x319d10 (i : Nat) : Nat := 0x1828bfd40
def x319h10 (i : Nat) : Nat := 0x2400715dc4661518140000c12608505c500e4076025020e037817f04400600034450000000d005815307381fe065050203c000000000000000000001c13a02c000e11c402000200a4163c59f15405ac0780009074000d031404d062c2381210100000000f06841b0038000d05800000000000000000000000000000000001c0800038220001005913f4440807303ccb19480
def x319l10 : Packing := (1,1,6,6,4,0,0,x319d10)
def x319columns : List ColumnInfo := [(256,0,575,0,8),(2,0,829,0,8),(32,0,543,0,7),(4,0,825,0,7),(513,0,318,0,7),(288,0,543,0,7),(6,0,825,0,7),(0,256,535,40,6),(512,32,30,257,6),(0,4,817,10,6),(512,2,312,5,6),(784,0,47,0,5),(264,0,567,0,5),(258,0,573,0,5),(768,32,30,1,5),(530,0,301,0,5),(8,256,535,32,5),(8,4,817,2,5),(516,2,312,1,5),(515,0,316,0,5),(2,4,817,8,5),(513,32,30,256,5),(513,2,312,4,5),(816,0,15,0,4),(296,0,535,0,4),(292,0,539,0,4),(290,0,541,0,4),(792,0,39,0,4),(769,32,30,0,4),(40,256,535,0,4),(14,0,817,0,4),(10,4,817,0,4),(519,0,312,0,4),(517,2,312,0,4)]
def x319levels : Nat → Packing
  | 5 => x319l5
  | 6 => x319l6
  | 7 => x319l7
  | 8 => x319l8
  | 9 => x319l9
  | 10 => x319l10
  | _ => emptyPacking
def x319index : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 3 0 9 1 4 x319h6
  | 7 => lookupWord 14 74 4 14 6 4 x319h7
  | 8 => lookupWord 80 427 7 16 8 4 x319h8
  | 9 => lookupWord 137 720 8 17 9 4 x319h9
  | 10 => lookupWord 12 79 5 14 6 4 x319h10
  | _ => fun _ => none
def x319 : Forest := ⟨831,10,fun j => x319samples[j]?.getD (0,0),x319columns,x319autos,x319levels,x319index⟩
set_option maxHeartbeats 0 in
theorem geomx319 : graphValid x319 (boundsBefore knownx251) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=2) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3195_0 : block x319 5 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx3195 : block x319 5 0 2=true := sx3195_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3196_0 : block x319 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3196_1 : block x319 6 1 36=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx3196 : block x319 6 0 37=true := (@block_merge x319 6 0 1 36 sx3196_0 sx3196_1)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3197_0 : block x319 7 0 36=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3197_36 : block x319 7 36 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3197_45 : block x319 7 45 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3197_81 : block x319 7 81 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3197_117 : block x319 7 117 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3197_153 : block x319 7 153 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3197_189 : block x319 7 189 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3197_225 : block x319 7 225 8=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx3197 : block x319 7 0 233=true := (@block_merge x319 7 0 225 8 (@block_merge x319 7 0 189 36 (@block_merge x319 7 0 153 36 (@block_merge x319 7 0 117 36 (@block_merge x319 7 0 81 36 (@block_merge x319 7 0 45 36 (@block_merge x319 7 0 36 9 sx3197_0 sx3197_36) sx3197_45) sx3197_81) sx3197_117) sx3197_153) sx3197_189) sx3197_225)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3198_0 : block x319 8 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3198_3 : block x319 8 3 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3198_39 : block x319 8 39 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3198_75 : block x319 8 75 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3198_111 : block x319 8 111 29=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3198_140 : block x319 8 140 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3198_176 : block x319 8 176 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3198_212 : block x319 8 212 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3198_248 : block x319 8 248 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3198_284 : block x319 8 284 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3198_320 : block x319 8 320 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3198_356 : block x319 8 356 14=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx3198 : block x319 8 0 370=true := (@block_merge x319 8 0 356 14 (@block_merge x319 8 0 320 36 (@block_merge x319 8 0 284 36 (@block_merge x319 8 0 248 36 (@block_merge x319 8 0 212 36 (@block_merge x319 8 0 176 36 (@block_merge x319 8 0 140 36 (@block_merge x319 8 0 111 29 (@block_merge x319 8 0 75 36 (@block_merge x319 8 0 39 36 (@block_merge x319 8 0 3 36 sx3198_0 sx3198_3) sx3198_39) sx3198_75) sx3198_111) sx3198_140) sx3198_176) sx3198_212) sx3198_248) sx3198_284) sx3198_320) sx3198_356)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3199_0 : block x319 9 0 14=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3199_14 : block x319 9 14 22=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx3199 : block x319 9 0 36=true := (@block_merge x319 9 0 14 22 sx3199_0 sx3199_14)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx31910_0 : block x319 10 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx31910 : block x319 10 0 1=true := sx31910_0
theorem tablesx319 : checkedTables x319 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block x319 0 0 0 = true)
  · exact (rfl : block x319 1 0 0 = true)
  · exact (rfl : block x319 2 0 0 = true)
  · exact (rfl : block x319 3 0 0 = true)
  · exact (rfl : block x319 4 0 0 = true)
  · exact allx3195
  · exact allx3196
  · exact allx3197
  · exact allx3198
  · exact allx3199
  · exact allx31910
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx319 : Lower (varsX 831) (graphGoal 831) 11 :=
  strong_low (m:=831) (cap:=10) (hints:=12884910337) (by decide +kernel) (plainB (q:=319) (prior:=boundsBefore knownx251) (before_sound knownx251 validx251) (by decide +kernel))
    (index_root (g:=x319) (i:=0) rfl (before_sound knownx251 validx251) geomx319 tablesx319 (by decide +kernel))
def mapsx319 : List (Nat × List Nat) := [(831,[])]
def knownx319 := extendKnown knownx251 11 mapsx319
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx319 : Known knownx319 := extendKnown_ok (m:=831) validx251 lowx319 (by decide +kernel)
def x351samples : Array (Bits × Bits) := #[(0xbfbc04e2d49e618c040f605e4f9964880501d5eff9afdb26fef0138b52798630103d81793e659220140757bfe6bf6c9bfbc04e2d49e618c040f605e4f9964880501d5eff9afdb26fef0138b52798630103d81793e659220140757bfe6bf6c9bf,0x3f3c78e0c19a8842034f711c8f9174880907dd67b18edb00fcf1e383066a21080d3dc4723e45d220241f759ec63b6c03f3c78e0c19a8842034f711c8f9174880907dd67b18edb00fcf1e383066a21080d3dc4723e45d220241f759ec63b6c03f),(0xc2163839c85b31c582c03a6468c43d7faa30741a0b7107df0858e0e7216cc7160b00e991a310f5fea8c1d0682dc41f7c2163839c85b31c582c03a6468c43d7faa30741a0b7107df0858e0e7216cc7160b00e991a310f5fea8c1d0682dc41f7c2,0xc0000414044002044000086070460363903000080a31049f000010501100081100002181c1180d8e40c0002028c4127c0000414044002044000086070460363903000080a31049f000010501100081100002181c1180d8e40c0002028c4127c0),(0x3fce7218a3995968a4d09039880d00747adb9b97d4407ae8ff39c8628e6565a2934240e6203401d1eb6e6e5f5101eba3fce7218a3995968a4d09039880d00747adb9b97d4407ae8ff39c8628e6565a2934240e6203401d1eb6e6e5f5101eba3f,0x3ea07329a2141568b4de1219888800146ac959f7c4406a60fa81cca6885055a2d378486622200051ab2567df1101a983ea07329a2141568b4de1219888800146ac959f7c4406a60fa81cca6885055a2d378486622200051ab2567df1101a983e),(0x454903c047e2c8b261048d8992731208512eaf00921ed11d15240f011f8b22c98412362649cc482144babc02487b447454903c047e2c8b261048d8992731208512eaf00921ed11d15240f011f8b22c98412362649cc482144babc02487b44745,0x415004c01902e8920200e1a01331120891262600312a911d05401300640ba248080386804cc4482244989800c4aa447415004c01902e8920200e1a01331120891262600312a911d05401300640ba248080386804cc4482244989800c4aa44741),(0xa0833c423065164e3e095212166a88c7653400cd6c522ce2820cf108c1945938f825484859aa231d94d00335b148b38a0833c423065164e3e095212166a88c7653400cd6c522ce2820cf108c1945938f825484859aa231d94d00335b148b38a0,0x800300022465162d38900a02604e8847661000884c5124e2000c0008919458b4e2402809813a211d984002213144938800300022465162d38900a02604e8847661000884c5124e2000c0008919458b4e2402809813a211d98400221314493880),(0x0,0x0),(0x7f32c8c5783e27a11e3213802121f983cecfea702582a561fccb2315e0f89e8478c84e008487e60f3b3fa9c0960a9587f32c8c5783e27a11e3213802121f983cecfea702582a561fccb2315e0f89e8478c84e008487e60f3b3fa9c0960a9587f,0x374bd8095a2c6da1061013820330f88c4e8efa74f102a160dd2f602568b1b68418404e080cc3e2313a3be9d3c40a858374bd8095a2c6da1061013820330f88c4e8efa74f102a160dd2f602568b1b68418404e080cc3e2313a3be9d3c40a85837),(0x0,0x0),(0x98a0c186a481865479ff0dc1a196c73000c100a006ddee926283061a92061951e7fc3706865b1cc0030402801b77ba498a0c186a481865479ff0dc1a196c73000c100a006ddee926283061a92061951e7fc3706865b1cc0030402801b77ba498,0x8884213604c10240f9ef0c45a48e0531205001830ed54e82221084d813040903e7bc3116923814c48140060c3b553a08884213604c10240f9ef0c45a48e0531205001830ed54e82221084d813040903e7bc3116923814c48140060c3b553a088)]
def x351autos : List (List Nat) := [[],[96,132],[64,49,134],[128,49,100]]
def x351d6 (i : Nat) : Nat := 0x3f8092505314c140
def x351l6 : Packing := (1,5,5,0,4,0,0,x351d6)
def x351d7 (i : Nat) : Nat := 0x21000021020420010420070400f08024109042410387041c0e865dedc59d2d04946c43d3ab3b12a27a09992870047f64a885d5408fec8906baa811fd9120d725026fb2b442c2a04fb64a884c540af64930e98a811fc985d5315033d904baa62a067b61c824c540cf6412e298a817e8924c530503f912498a60a07f4585314c140fe898a429828117d9520d725023f321442e2a047e261764c1408fc4c2ea982811f8985c93050277130a0a60a07e4505314c140
def x351h7 (i : Nat) : Nat := 0x2000000
def x351l7 : Packing := (21,4,5,1,4,8,0,x351d7)
def x351d8 (i : Nat) : Nat := 0xa071040a0850244140e21508861c30a840c184850c10a0710a848854244021860850388012022c31211050f2638448683c68e10e0010384881c3c4140e200403818c40204120e2100910503884028406181080861c21f0e8c30f0e105c38a1c21c8d0e387087c38a1c23a2e20d07861d2050d080421f0e26300050f1c0840143624008284344c6c6821030118189028c0c343040228143190f1020908183c40a1000800c200708004200208e061c21e382870c3847030e10f071c1c38e0a1c37aaeadc0b5763ab8d5ca9f4ea92d10a073da70cdc97f26a46c708c713a1cc2481f029f6bd8786eb9ccb846eeda9aeb50666c7984afc5beb495eab05369d930a5446e86906a083e6798ec9bc35e648ba9602864b88c9041ee3a8728d81a6318608b415e2884a8880e61982c84c07e08806800bfe8854940dfd625c540dfd525c540bfe8858540dfd7358540dfd7258540efd6258540dfd7158540bfe8854540dfd7354540dfd7254540f7d5254540dfd7154540bfe884c540dfd874c540bfd854c540dfd754c540fec824c540dfd724c540dfd714c540ff5614c540bfd850c540bfd820c540bfe8848540dfd8748540bfd8648540dfd7648540bfd8548540dfd7548540bfd8348540dfd7348540fed5248540dfd7148540ff53148540ff9634c140ff9534c140ff9624c140ff9524c140ff9324c140ff9614c140ff9514c140ff9314c140ff9214c1409fe885d5409fc835d5409fe885c940d7e555c9409fc835c9409fd8754940ded7588940f6e55889409fe885c540cfe665c540d7e555c5409fc835c540dee225c5409fd8758540cfd76585409fd87545409fd874c5409fd870c540bf9800c5409fd8748540df57184540df57684540ef66684540df57584540f765584540df57384540fd63384540df57284540fe62284540bfa884c140df9764c140efa664c140df9754c140f7a554c140fda334c140df9724c140fea224c140fb9414c140fd9314c140ff2114c140
def x351h8 (i : Nat) : Nat := 0x3c130100000000492000000584480820e109f03cc19e056038000000000a052008001c01000580e400a0b4043818000e12a06800082800032b00
def x351l8 : Packing := (83,3,5,5,4,11,0,x351d8)
def x351d9 (i : Nat) : Nat := 0xf12140868e61e200868e51e240868e50c0638e39c10f021a390785021a39c3051f0439c0c60d1c4149011f183980c7105821e31d2858e21f049460e5da632c94a9bc59ceb8529d8c63b14003fea9281ff58540ffaa2a07fd31503fe18a81ff48540ffc22a05fd75503bf2aa817f5c940fdc44a05fd71503fb08a81fe4c140
def x351h9 (i : Nat) : Nat := 0x1406441b312ea01760fc0000035e20aa0974a64044d09e000109200000001e0c00000000126200bcc0d510cc031804109a1943d04264b000000000000000342068082228250bc01790350770141c11b1013075847800060110000c05109fc015e041e4c1422b029402dc01b4902832d01f00dec978000605c00000006915804c6014029000082320002c1c782c00006120806800012120002894b0410000000181e80000000642c00000005244004c0000000a03e206c0004042502f00cc00008461271a12d489095100000003c26982da098601241c80000000602b81a003c70120000806313d5292c0488840028227c0001c90e8070000e0c58a7602a9039c006407304e2095211f09cd800a092a089888981ea2366077c13b948e23500af001c843e07d0536c28a8246209043890466064c002f2021470560425440038b500a104382158
def x351l9 : Packing := (14,2,5,7,4,9,0,x351d9)
def x351d10 (i : Nat) : Nat := 0x8c38ffd40
def x351h10 (i : Nat) : Nat := 0x101c00000282c0024ac00000309c0000000000000028284058b101a488000003c994304940010030240004360228b400180c003808000000000000001013c840000000038140a20800001c80
def x351l10 : Packing := (1,1,5,4,4,0,0,x351d10)
def x351columns : List ColumnInfo := [(256,0,607,0,8),(4,0,859,0,8),(513,0,350,0,8),(64,0,543,0,7),(528,0,334,0,7),(2,0,861,0,7),(320,0,543,0,7),(529,0,334,0,7),(0,256,535,72,6),(0,64,541,258,6),(512,16,326,9,6),(512,1,332,18,6),(256,64,541,2,5),(12,0,851,0,5),(8,256,535,64,5),(520,16,326,1,5),(6,0,857,0,5),(2,64,541,256,5),(514,1,332,16,5),(328,0,535,0,4),(324,0,539,0,4),(322,0,541,0,4),(785,0,78,0,4),(258,64,541,0,4),(72,256,535,0,4),(537,0,326,0,4),(533,0,330,0,4),(531,0,332,0,4),(530,1,332,0,4),(521,16,326,0,4)]
def x351levels : Nat → Packing
  | 6 => x351l6
  | 7 => x351l7
  | 8 => x351l8
  | 9 => x351l9
  | 10 => x351l10
  | _ => emptyPacking
def x351index : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 3 0 9 1 4 x351h7
  | 8 => lookupWord 5 34 4 13 5 4 x351h8
  | 9 => lookupWord 31 162 6 15 7 4 x351h9
  | 10 => lookupWord 6 53 3 12 4 4 x351h10
  | _ => fun _ => none
def x351 : Forest := ⟨863,10,fun j => x351samples[j]?.getD (0,0),x351columns,x351autos,x351levels,x351index⟩
set_option maxHeartbeats 0 in
theorem geomx351 : graphValid x351 (boundsBefore knownx319) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=2) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3516_0 : block x351 6 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx3516 : block x351 6 0 1=true := sx3516_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3517_0 : block x351 7 0 7=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3517_7 : block x351 7 7 14=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx3517 : block x351 7 0 21=true := (@block_merge x351 7 0 7 14 sx3517_0 sx3517_7)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3518_0 : block x351 8 0 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3518_36 : block x351 8 36 4=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3518_40 : block x351 8 40 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3518_76 : block x351 8 76 7=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx3518 : block x351 8 0 83=true := (@block_merge x351 8 0 76 7 (@block_merge x351 8 0 40 36 (@block_merge x351 8 0 36 4 sx3518_0 sx3518_36) sx3518_40) sx3518_76)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3519_0 : block x351 9 0 7=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3519_7 : block x351 9 7 7=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx3519 : block x351 9 0 14=true := (@block_merge x351 9 0 7 7 sx3519_0 sx3519_7)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx35110_0 : block x351 10 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx35110 : block x351 10 0 1=true := sx35110_0
theorem tablesx351 : checkedTables x351 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block x351 0 0 0 = true)
  · exact (rfl : block x351 1 0 0 = true)
  · exact (rfl : block x351 2 0 0 = true)
  · exact (rfl : block x351 3 0 0 = true)
  · exact (rfl : block x351 4 0 0 = true)
  · exact (rfl : block x351 5 0 0 = true)
  · exact allx3516
  · exact allx3517
  · exact allx3518
  · exact allx3519
  · exact allx35110
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx351 : Lower (varsX 863) (graphGoal 863) 11 :=
  strong_low (m:=863) (cap:=10) (hints:=12901687553) (by decide +kernel) (plainB (q:=351) (prior:=boundsBefore knownx319) (before_sound knownx319 validx319) (by decide +kernel))
    (index_root (g:=x351) (i:=0) rfl (before_sound knownx319 validx319) geomx351 tablesx351 (by decide +kernel))
def mapsx351 : List (Nat × List Nat) := [(863,[]),(957,[118,130,81])]
def knownx351 := extendKnown knownx319 11 mapsx351
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx351 : Known knownx351 := extendKnown_ok (m:=863) validx319 lowx351 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx375 : Lower (varsX 887) (graphGoal 887) 9 :=
  strong_low (m:=887) (cap:=8) (hints:=21491613953) (by decide +kernel) (plainB (q:=375) (prior:=boundsBefore knownx351) (before_sound knownx351 validx351) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx351) (before_sound knownx351 validx351) (528,0,359,0,8) (by decide +kernel) (by decide +kernel))
def mapsx375 : List (Nat × List Nat) := [(887,[])]
def knownx375 := extendKnown knownx351 9 mapsx375
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx375 : Known knownx375 := extendKnown_ok (m:=887) validx351 lowx375 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx381 : Lower (varsX 893) (graphGoal 893) 9 :=
  strong_low (m:=893) (cap:=8) (hints:=13019128580) (by decide +kernel) (plainB (q:=381) (prior:=boundsBefore knownx375) (before_sound knownx375 validx375) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx375) (before_sound knownx375 validx375) (64,0,829,0,8) (by decide +kernel) (by decide +kernel))
def mapsx381 : List (Nat × List Nat) := [(893,[])]
def knownx381 := extendKnown knownx375 9 mapsx381
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx381 : Known knownx381 := extendKnown_ok (m:=893) validx375 lowx381 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx471 : Lower (varsX 983) (graphGoal 983) 8 :=
  strong_low (m:=983) (cap:=7) (hints:=26323452161) (by decide +kernel) (plainB (q:=471) (prior:=boundsBefore knownx381) (before_sound knownx381 validx381) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx381) (before_sound knownx381 validx381) (256,0,727,0,7) (by decide +kernel) (by decide +kernel))
def mapsx471 : List (Nat × List Nat) := [(983,[]),(1013,[118,130,81])]
def knownx471 := extendKnown knownx381 8 mapsx471
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx471 : Known knownx471 := extendKnown_ok (m:=983) validx381 lowx471 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx255 : Lower (varsX 767) (graphGoal 767) 12 :=
  strong_low (m:=767) (cap:=11) (hints:=553656577) (by decide +kernel) (plainB (q:=255) (prior:=boundsBefore knownx471) (before_sound knownx471 validx471) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx471) (before_sound knownx471 validx471) (64,0,703,0,11) (by decide +kernel) (by decide +kernel))
def mapsx255 : List (Nat × List Nat) := [(767,[]),(1019,[118,130,81])]
def knownx255 := extendKnown knownx471 12 mapsx255
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx255 : Known knownx255 := extendKnown_ok (m:=767) validx471 lowx255 (by decide +kernel)
def x383samples : Array (Bits × Bits) := #[(0x58f101603ffc34e1997c52bc3237fc64c0004055154088fd734aa3342240885bafdbc7bcc94733e45bfbf81783f5607cebfe5026c566eb1e202c07ff869c332f8a578646ff8c9800080aa2a8111fae6954668448110b75fb78f79928e67c8b7f,0x104036015c00822a11450ac02246561500200070240008c714083942206010a07db84acc90711e403fbfc8784428000c406940065444020806c02b8010454228a1580448cac2a004000e04800118e2810728440c02140fb70959920e23c807f),(0xdc3b086ec2023b806c8a42dbb3e25d1097c88d48dbc47d8b2cfb78409fea7c2f7b040b423690eb1fec400e3800680f7a01e6399aaf9d1b87610dd84047700d91485b767c4ba212f911a91b788fb1659f6f0813fd4f85ef60816846d21d63fd88,0xde3b0086c0023081140903103102989086482058381478038c9b70410df95c25680003402600ea1be8000050602c4e7a01b009d090091bc76010d8004610228120620620531210c9040b07028f0071936e0821bf2b84ad00006804c01d437d00),(0x980f122ba5dc75027e25ccf4cf9260a339b9fa247a1b320006581ad508ea2f295e53c9bd2790ce517fbc4a817c2b98cfcc1b6ef6bc0e1301e24574bb8ea04fc4b99e99f24c1467373f448f43664000cb035aa11d45e52bca7937a4f219ca2ff,0x100e1000e1dc74823e29ccb4c59060079979fa7c7a183206264812c1006a2da95a73c3fd05804e417dfbe298fd381841c4d742f2980e0201c2001c3b8e9047c5399698b20c00f32f3f4f8f430640c4c90258200d45b52b4e787fa0b009c82fb),(0x2656771d024140124125b684540c53ff64112012083b46838893169743750124404142c169af5143e0280080704496780401a0511dca04cacee3a04828024824b6d08a818a7fec822402410768d0711262d2e86ea024880828582d35ea287c05,0x6275025d00000810d81502000204416f84000018000824c680831e93477001244218438001a75101e0200096600878020382814004320c4ea04ba00001021b02a0400040882df080000300010498d01063d268ee0024884308700034ea203c04),(0x2017f095e0a2af8c3411a560209980b01f7530c1e40b4a300f14453891b1e111b42c187a020cec3a1c84910aa3ba470468192e3072a8c402fe12bc1455f1868234ac0413301603eea6183c81694601e288a712363c223685830f40419d874390,0x1888f080a236b30d026aa50390db80100b7573a0f927db310e0c40689081f011b82418521248ae1a1c040320008501fc287922991a8923111e101446d661a04d54a0721b7002016eae741f24fb6621c1880d12103e023704830a424915c34380),(0x5cf9f80d2b3cb46d98e8a342c895928605b44bfce52fb05396128e4bcc193e500094711594face9bfd0722457c1920fb9ba06e3f08aa2b9f3f01a567968db31d14685912b250c0b6897f9ca5f60a72c251c9798327ca00128e22b29f59d37fa0,0x5c91581d2239874118e8a352c8d8928e02f459f8c5afb4518a991c2bcd593c502004691110f8ce0bfc0402381ab925e813816a3718a22b922b03a44730e8231d146a591b1251c05e8b3f18b5f68a3153238579ab278a04008d22221f19c17f80),(0xb5c0f8d87e1789104be498c985f9650919675420c5a6045c53045ca2ac06c1cc127aec2510fe950037fa43081b1320201100430e4cb156b81f1b0fc2f122097c931930bf2ca1232cea8418b4c08b8a608b945580d839824f5d84a21fd2a006ff,0x20c0b9102a6d0c104960a8cbc4ed216d11275ca085ab04dc13040ca2e006a14a125a68bdd0fe150015f8028e1b5131040803620a4cb024181722054da182092c1519789da42da224eb9410b5609b826081945c00d429424b4d17ba1fc2a002bf),(0x0,0x0),(0x430887841400902e234c4b2c39002041682e32af2a500306e4a4204a20005680c822b4422f0034fc8215c1404c0e02d310581e900701886110f082801205c4698965872004082d05c655e54a0060dc94840944000ad01904568845e0069f9042,0x810204a2518050ae26024424310008006808a2073a50432060206040108042818da190422e0020f40200014184068211e05c04802345902040944a300a15c4c04884862001000d011440e74a08640c040c080210085031b4320845c0041e8040)]
def x383autos : List (List Nat) := [[],[98,131,84],[16,66,101],[48,129,82],[128,49,100],[16,82,131,100],[48,16,128,98,82,66],[128,16,48,66,82,98]]
def x383d8 (i : Nat) : Nat := 0x1e001000000001e061f01081078088030221a10001e0410780040b8205c13000817040b8205c1001704c18204013000817040b820078004000250d0307c003e021f010f8084000001e0010000000000003c043e001f0008000e05054101387c003a040a82078007c0020f00083c0020180b02f000f8007c003e001f000fcdeafa1e5f8de0f79dbf65d0f21b9ec5a8e99a3e8598e598de157cdd16bd8d5ad614fd1d3ecd92dc9522c8117c5512c2901be4f0ba0dfb74dab60d5b4ccab20c5b0cc0af8bbae4b6ad0b1aa4a0a6095a4c90a08799c4629805793c4c910418e42a88819844088014bf6da99a21715025deda554c1ae2a052fdb6a65835c540c77d544c2e6a0a814ef2e5875cd41502cdedb906b8a82a053edb2a66884c5408dfb6d5532e98a811fb6caaa65d315025bedad54c3a62a053edb2a65874c540b5bb6c51b0e98a816ed6dc9850531502dda5c4eea0a62a05bb4b85cd414c5408dfb6c54cef08a811fb6c8a98ce1150277cdb554b8a60a0437db52a6889dd4092fb6a54d113ba8149f6d4a76588350295eda14ecb106a052ddb329d9620d40a5db6453b2c41a814bd6c4a76588350297cd814ecb106a060feaa9dd9620d40a1fb6e50b2c41a8149f6d4a16588350295eda142cb106a052ddb32859620d40a5db6450b2c41a814be6c0a1658835029da5c348c88e6a043bdb42a6888cd4096bb6b5530f19a810bf6daaa661715021bedad54cc2e2a042fcb9698835c540c57b4cca10638a8146f2e5879dd4150255f5db4c41a82a062be996988350540d17ceed3106a0a810ef6e8981cd4150315e4c34c39a82a063ac986887350540c76930d08e6a0a818ee261a01cd415029ce5cb0f19a82a0719c989de33505409f3576d1920a0a819e665da3241415035ccc3b4648282a06d9a7768c9050540df2362d1920a0a810ef6d2aa661315021f6d9554cc262a05f91b028d414c540bf23665028298a816ad6d883506115025badad54c3c22a04bb5b4aa9838454095ed76d310708a81a3d9dda620e115031ce41b494ca60a0473db52a5414c140c77130d25329828147e2e5879dd3050279cda952a0a60a05f91b4245314c140bf2576a0a6298281be4aa9414c530502fc85ca8298a60a0779299505314c140f72150a0a6298281ee4a21414c530503dc8c3a8298a60a07d9277505314c140a7e172c3c22982812de6d6aa61e005025dcda554c1c00a04bb8ba61d4180140
def x383l8 : Packing := (83,5,7,0,4,10,0,x383d8)
def x383d9 (i : Nat) : Nat := (if i<3 then (if i<1 then 0x9884540afd2a68884540afd29e8884540afd28e8884540afd6a09784540bf96889784540afdaa98784540afd2a58784540afd28d8784540afd68c8784540afd2a27784540e7d61e7784540e7d2a27784540e7d2627784540e7da227784540afd6a09384540bbd6989384540bfc6809384540afdaa98384540afd2a58384540afd29d8384540e7d9dd8384540afd69c8384540e7d9dc8384540afd6a17384540afd2a17384540afd6a07384540bbd6987384540bdd6947384540bed6907384540bf96887384540bfc6807384540afd2a23384540bfc2823384540ef52a23384540ef52623384540ef5a223384540ef561e3384540ef521e3384540f759de3384540ff428233845409df696995c1409ef692995c1409ef2a5415c1409ef692994c1409ef2a5414c140fe5505314c140bee692994c140dee692994c140cfea66884c140bfa688974c140afeaa9874c140cfe2a5874c140cfea65874c140ef628d874c140e7e61e774c140d7ea66774c140e7e2a2774c140e7ea22774c140ef6a22334c140ef661e334c140f769de334c140bde694914c140bee690914c140afe6a0714c140bee690714c140bf668c714c140beeaa9414c140bee2a5414c140deea65414c140eeea21414c140eee61d414c140f6e9dd414c140fe668d414c140fe68cd414c140fec645414c140fec505314c140bf6aa9314c140df6a65314c140ef62a1314c140ef6a21314c140ef661d314c140f769dd314c140ff4245314c140ff45c5314c140fe6505314c140fec506114c140ff44c6114c140dfca66114c140efca22114c140efc61e114c140f7c9de114c140ff428e114c140ff48ce114c1409ef69299441408ff6a587441408ff6a58344140bedaa94144140deda654144140eed61d4144140f6d9dd4144140ded64d4144140fe58cd4144140fec5053044140afeaa98780140cfe2a58780140afe28d8780140afe2858780140e7e61e7780140afeaa98380140afe29d8380140e7e9dd8380140afe2858380140afe6a17380140afe6a07380140bbe6987380140bde6947380140bee6907380140bfa6887380140bfc68473801409fe2a63380140ef660e3380140df62a63380140ef661e3380140f769de3380140afeaa98180140afe29d8180140e7e9dd8180140afe28d8180140ef68cd8180140afe6a17180140afe6a07180140bee6907180140beeaa94180140eee61d4180140f6e9dd4180140fe68cd4180140afe6a13180140fec5053180140afe6a03180140bde6943180140bee6903180140efc6061180140fec5061180140efc61e1180140f7c9de1180140efc60e1180140ff48ce11801408df6969961d408ef6929960d408bfaa99620d40c3f9dd9620d40c6f2627750540aaf6988350540ce72623350540be668c9050540abd6988384540fe4505314c140 else (if i<2 then 0xc7fa667760540c7f24e7760540cf764c93605408ff2a573605408ff6a47360540abf6987360540adf6947360540aef6907360540afb6887360540afd6847360540afe68073605408ff2a63360540cf72a63360540cf7a663360540cf725e3360540e779de33605408ffaa99720540c7f65e77205408ffaa99320540c7f9dd93205408ff6a57320540c7f65d73205408ff6a47320540abf6987320540adf6947320540aef6907320540afb6887320540afd6847320540afe6807320540cf764e3320540cf765e3320540e779de33205408ff6a2995c5409bf69a995c5408ffaa9985c5408ff2a6885c540c7f662775c540c7f262775c5408ff2a5835c5408ff6a4835c540a7f69c835c540abf698835c540afd684835c540cf7662335c540cf7262335c5408ffaa9981c5409efaa9941c540cefa21941c5408ff6a5831c540cef651831c5408ff6a4831c540abf698831c540cef650831c540cf7662331c540de7652331c540aef69c9850540cefa668850540cef2619750540aefaa98750540cef2a58750540cefa658750540eed2858750540cef2627750540e6f61e7750540d6fa667750540e6f2a27750540e6f2627750540e6fa227750540cef2619350540bcf6949350540bee6809350540cefa648350540aef69c8350540e6f9dc8350540cef26173505409ef6a47350540aef6a07350540cef2607350540baf6987350540bcf6947350540beb6887350540bed6847350540bee6807350540cef2623350540de7a663350540ee72623350540ee7a223350540ee761e3350540f679de3350540fe52863350540fe62823350540dee65c9050540eee61c9050540f6e9dc9050540bee68c9050540fe68cc90505408ff6a2994c5409fb68a994c5408ffaa9984c5408ff2a6884c5408ff6a5874c5408ff2a5874c5408ff6a4874c540afd684874c540c7f262774c540cf7262334c540bedaa9414c540deda65414c540eed2a1414c540eed261414c540eeda21414c540eed61d414c540f6d9dd414c540fe528d414c540fe58cd414c540fec281414c5408ffaa9980c5408ff6a5870c540c7f65d870c5408ff6a4870c540c7f662770c5409dfaa9950c540cdf6a1950c540cdfa21950c540cdf61d950c540cdf21d950c540d5f9dd950c540dcf691950c540cefa21940c540cef61d940c540d6f9dd940c5409feaa9900c540cfea21900c540cfe61d900c540d7e9dd900c5408ff2a688845408ff2a58784540afd6848784540c7f26277845408ff2a58384540abf6988384540afd6848384540cf72623384540afd29d8184540e7d9dd8184540afd28d8184540ef58cd8184540afd6a17184540afd2a17184540eeda214184540eed61d4184540f6d9dd4184540eed20d4184540fe58cd4184540afd6a13184540afd2a13184540afd69c9884540afd68c else 0xa994c5409ff69e994c540dfb68a994c540aff69c984c540cffa66884c540aff2a1974c540cff261974c5409ffaa9974c540cff2a1974c540cffa21974c540aff6a0974c540bef690974c540affaa9874c540cffa65874c540ef728d874c5409ff2a6774c540aff2a2774c540aff2a1734c540cff261734c540cff25d814c5409ff6a5714c540aff2a1714c540cff261714c540efd2a1714c540efd261714c540efda21714c540def25d414c540eef61d414c540fed29d414c540fed25d414c540fed9dd414c540fed5cd414c5409ffaa9970c540cffa21970c540cff662770c540def9dd940c540dfe9dd900c540aff68c87845409ff2a67784540aff69c83845409ff2a57384540cff2617384540bbf6987384540bdf6947384540bef6907384540bfb6887384540bfd68473845409ff2a63384540f7d5c5315c140fed505315c140ff55c5314c140bfe684974c140bfe69c914c140bfeaa9714c140fee9dd414c140fee5cd414c140fee5c5414c140fee505314c140ff65c5314c140aff28d8744140aff29d8344140bbf6987344140bdf6947344140bef6907344140bfb6887344140bfd6847344140fed9dd4144140fed5cd41441409df6969961d409fe6829961d40adf6969961d40aef6929961d40afe6829961d40cdf6969961d40cef6929961d408ff68e9961d408ff6869961d408ff6829961d40cfe6829961d40abf6989361d40cf764c9361d40cfd6449161d408ffaa99321d408ffaa99121d408ff2a6889dd40a7f28d879dd40a7f285879dd40a7f68c989dd40a7f684989dd40a7f2a6889dd40a7f28e889dd40a7f286889dd40a7f6a0939dd40b7e680939dd40a7f6a0919dd40b5f694919dd40b6f690919dd40aef6929960d40cef6929960d408ff6869960d40cfd6449160d408ffaa99720d40c7f65e7720d40cbfaa99620d40cbf69d9620d40cbf29d9620d40cbf9dd9620d40cbf6859620d40cbf2859620d408ffaa99120d40c7f9dd9120d408ff6a2995cd408ff2a6885cd40c7f262775cd408ffaa9981cd40cbfa21961cd40cdfa21951cd40cefa21941cd40cfba21921cd409fdaa9911cd40cfd6a1911cd40cfd2a1911cd40cfda21911cd40ded691911cd409feaa9901cd40cfea21901cd408ff2a6888cd408ff2a5878cd40af768c878cd40c7f262778cd40d7e242778cd40af72a1738cd40af769c988cd40af7684988cd40af729e888cd40af7286888cd40af76a0978cd40af7aa9878cd40af72a5878cd40af7285878cd40af7684878cd40af72a2778cd40e7761e778cd40e772a2778cd40e77262778cd40e77a22778cd40af76a0918cd40be7690918cd40ef661c908cd40f769dc908cd40aef69299605408ff69e9960540cef69299605408ff68e9960540cfe6829960540c7f65c97605408ff2a67760540c7f2a6776054)) else (if i<4 then 0x7dc046fa5bce6ef9bae6e4db786d75b4d6cf5b2d6c75b0d6bf5aed6b75acd6af5aad6a75a8d69f5a6d69a1a636979a4e68f9a2e68a5a0e67cd9e367219b866cd98d65f596d657595864c991763f18e162ed8a061e985460e5829606580960117e95f657be5eb97885db57475cb17115bd96db5b016a55a556855a0166558a560357a15d857215ad561d56c5545536546d50b53c14e053154aa521145e510d41250093f24f5d3c74e853914dad35b4d5933b4cad3264c593064c052db4b012a54a55259492522e484d1f847751cd46f51ad467518d45c916d4575158452114344cd1234479119445110f44290e442a10824171036406cff53f68fca3ee8faa3e68f743d64f493c60f083c0cef33bb8ed33ab4e9239b0e5c3930e313858df03754dc5367cd8f35d0d643550d4434a4d1933f8ce3334ccc332a0c8231c8c623148c4d30f4c383074c0d3020bf82fa0bcd2ef4bad2e74b8d2df4b6d2d74b4d2cf4b2d2c74b0d2bf4aed2b74acd2b20ac32af8aae2a78a8e29f8a6e2978a592924a3928a4a1928249f927a49d927249b926a4999265098f262897a25d497025ac95024d493024288ef23508c422d08a421f886e212083820cc823207880e20248041fd07e41f247ae1e4c7781da07581cf472d1c746f71b9c6cc1af06a119ec66b196c6561918620184060b17945ca16e85aa16945a0164058015c0560151451f13e44e913644a8126047d11b44521108432108841210083f20f883dd0f343bd0eb439d0e3437d0db435d0d343480d0c3330cb831e0c383090be42f40b642c90ae42b40a902940a102740990254091023408bc21f083c20a0814200068c15104d811b04000c402a40780174000aff6849361d40aff68c9161d40aff69c9160d40cff9dd9120d409ff686995cd40aff285985cd40aff684985cd40cffa66885cd40aff286885cd40aff285875cd40aff2a1915cd40cff261915cd40aff6a0915cd40bef690915cd409ffaa9911cd40cffa21911cd40dfdaa9911cd40dfd681911cd40aff684878cd409ff2a6778cd40aff29d8360540aff68c9760540cffa667760540aff29d9360540aff69c9360540affaa97360540cffa657360540aff29e3360540affaa97320540bbf69a995c540dbf69a995c5409ff68e995c540aff68c985c540cffa66885c540aff2a1935c540cff261935c540aff6a0935c540bdf694935c540bef690935c540bfe680935c540affaa9835c540cffa65835c540aff2a1735c540cff261735c5409ff2a6335c540aff2a2335c540bfe282335c5409ffaa9931c540cffa21931c540bef68c9750540eef2627750540bef29d9350540bef69c9350540bef29d8350540eef9dc8350540befaa97350540eef2a17350540eef2617350540eef61d7350540bef29e3350540eef61d7150540eef20d7150540bfb68 else (if i<5 then 0x1386160238a0c0780042b84710000a4138601427081704e10040a02e03c005c002044248b800408849104705a2e02028260f818280a6323413c405f81a080a64e001408100c0f840343c001a0501f000f010320d07c00200ae11c5c0020e001e00100290320dc605c2a880b83e1602082002fc000d10e2e020a1a432200e0f840181f082b847103e083e083e083e083e084909e2070008380041c003c002000000009c04278f80024e0213021178083209830200cc278c0000b060309e124400c1784c18040a02e001e001e001e001040434280f028501700083b019c002c1380041c002002214440180584e18050402e060e4228f800780041d82a102009a202c0641a0e0c85117000816e001547c002014100a02878007800402836170208390a020441245c003c00208828080681b0943e001e001e001070008380f001700082030603040350214060f030f000f010f020f00090409050f000f000f000f0009050f000f000f0108000e001e021e041e001e001e00107000f020f010f000f000f010f0009040f000f020f000f0008000e02100018341b080002010000038068381a150408828082a0780078104167020aa3e001e021241b0f80041c0020e001002028781078105410170a8200a150405c2a082a0681068105417000f000820018150740820341f0a810681054130203c1607c003c0020e00100a1302a0f80041c078004c18240a826041e001003800781078007810400020100001613860000582d1f000c0d083e00d4082a1206860683a140d0b020a82e001020120a120c1e021e001e00107000f010f000f010f0009040f000f0008050801c0420e001e001070008380f00170009040838006068606878187800780078004828404183c042000004f02045c0f8005809c105003381f0106dc00260433c0e834281d06848650d081c82005c06887150ca1a1703e000680b908711a101741ac0b80f03e001542622d7eb562d3db48ad07b3decdcb306cb1b286c91b1dac5bb12ec30b056bfaaf7ebc4aea6b99adfab63ad4eb38ac76b02abcaad7aac6a96a9eea55a8eaa2aa86a9f4a73a9b3a662972a55e947a4de91ca4328fca3868c6a2ae890a20285aa12a824a05280f9fd27e49f527c49e7a76d9d4a7379c466f69b9a6d69aee6a099ea65498ba61397b65c796b259c963257c95b254694da526942e4f093824d092aa48f91d24649152439907a4038fce3e38f223ad8e4a3778d9e34c8cc630b8bc22d58aea2aa8a3e27f896624988e621387e21d2870a1a7865e18785b215184da11b84020f083820c582aa08481a604e80ce0238021fed7f49fc27e71f977e49f777d71f417cc5f217c45f017bc5ee17b45ec17ac5ea17a45e81796de407895e207815df57769dbf7665d7e758dd3d7489d1273b1cc672d9c9b7201c657129c2f70 else 0x1df010403e020ec110c14810100403e20220344418207008080800d11060906090d0f03e0020380404070204406881030d10200482049c0840140e880880d1104081c0222020010441020700808088101011020220810380184094080001825020202203440a408700181001a221a10901052043800c1481fe00320bc005c0b800808810e0030220404434283420440688868780040880d101101a207415854100b8882041001701a3208105d417010c088400800b8806048206050417602e00304c0900181e201001a204c04840438183b181101a221a109e10220345c0f800806f0004230440ec1e0c1d83c05830420484048087011822e020f06044068886848685068502040800d02a321a141a1053c0040e381881005020411703076305801840b0100816040f040880d100d0382020010407c207c204c03080880d10060562022034483438181c0b030381038c0c43078181c0810024101101a204410440d0408820f816702181f0f02082c01b408607a810812502e00381c1049c004414241020fb81081f7021023218207dc08408c86080684068706834100006c20021041a0c00020100006c20821605c00207c26081104910230882e001e021241a0c00024114404c238808049110509060f000f000f0009050f000f000f020f000f000906080007013060e0168811051100080451700082809420500d450360d84a181f094209e1285c0c1c845181309e2e00102203c228f8183a08a3e0010221244080248810049101109220401245c0021141888278491020092207c1e00102812440e026080f84917000f000f000f000f000f0009040f000f010f000f0009060f000f000f0108000e00120c1e0010000040209e14c5c002080298b80041c0c1c84e1f000f000f000838183908a308a0c441181a082303417030100d061181a08028090623e060202a8c1004c17000f000f0008008047170008380982e0010060e4180c0283010040ae11c613c248827849104f092209e124413c24882784917000f0008007047170303fc04280402f03074)))
def x383h9 (i : Nat) : Nat := 0xa00200000000000d02be6520102800204e00000000000a05520c2802b821803ee11601b70043078c11e4251037b073602402718100000410b0095843009b808a00e00004064000200a3008805d6059024602c30768075c0c00000000813280300000000000381598256066c0900000000c014c1240004835d0a4c0d040f0831e0880003c058819203420e0c140000107ba14682800290000a03cc070000607cc05c0000002000000000005826507e4044000080d000000008178000f08000024208000000000028099ba43037612c0000000f074a13cc16e0032019a118803e181a04620a12d0c0611ada00904f98007
def x383l9 : Packing := (535,4,7,7,4,14,0,x383d9)
def x383d10 (i : Nat) : Nat := (if i<2 then (if i<1 then 0xe39b02a06ff8cd815037fcee40a81bfd7320540dfe39902a06ff8cc81502ffd32b8a817fd985c540dfecc2e2a06ff261715037fd10b8a81bfd875c540eff3bae2a06ff60d715037f906b8a81fde335c540dfec0ae2a05ff660715037fd1038a817fd931c540dfec18e2a06ff20c71503fbc6638a817fd901c540fdf4ca82a07ef65d41503f792ea0a81fbd8750540fdf3ba82a07ef64d41503f7926a0a81fbd8350540fdeb9a82a07ef1cd41503f7c66a0a81fbd7150540fdec8282a05ffa6531502ffb3098a81bfd984c540dfe4c262a06ffa2131502ffb2e98a81bfd874c540dfe43a62a077f9dd31503fbc6698a81bfd814c540ffab8a62a07ef50531502ffb3018a81bfe880c540bfecb862a06ff61c315037f90e18a81dfe770c540bfec8062a06ffa22115037fb0f08a81bfc8784540eff3bc22a06ff60e115037f90708a81fde3384540ffac0c22a07fd5c611503fea6308a81ff49784540ffac3c22a07fd9de11503fe92708a81ff58384540ffab9c22a07fd1ce11503fec6708a817fe995c140eff3bae0a06ff60d70503fbc66b8281bfd815c140efeb8ae0a07ef50570503fec22b82817fe994c140bfecba60a06ff61d30503bfcee98281fde334c140dfec0a60a07ef50530503fba6298281ff6114c140ffcb8260a07fea6530503ff32e98281ff8974c140ffcc3a60a07fe9dd30503ff2e698281ff9914c140ffc48a60a07fe60530503ff2e298281ff8714c140ffc98a60a07fe84530502ffd32882817fd9744140dfec3a20a077f9dd10502ffb2688281bfd8344140fef19a20a07ef50510503fec2288281ff93044140ffd3bc00a07fe5ce00503ff0e700281ffa3380140ffcb8c00a07fe1c600503ff26300281ff83180140ffd08c00a04ffa65875027fb2643a813fd9121d40cfec3ceea067f262775033fd113ba813fe9960d409fecb906a067f9dc835027fb2241a813fd981cd40b7ecb0e6a05df65473502f7b2839a817ed921cd40bfac88e6a05fe640735037b93119a81bde888cd40deec3c66a06f721e33503bbcef19a81fd8908cd409ff4cb02a067f9dd815037bc66c0a813fd9720540cff3b902a04ff64c815037bc6640a813fd985c5409fecc0e2a05ef65071502f7d32a0a81bbc9850540ddf44282a06ef61d41503b7ceea0a81bbc8350540fcf19a82a07ee241415027fb3098a81fb5414c5409fecc062a05df65431502f7b2818a817f9900c540dfac0c22a07ed506115037e93108a81bf68884540dfac3c22a06fd21e11503becef08a81bf58384540dfa41c22a07f58ce11502ff53298281bfa884c140dfcc3a60a077e9dd30503fb46698281fb9414c140fec98a60a07fc84530503f6a8288281bf98780140efd3bc00a06fe60e00503fb46700281bf98180140fdca0c00a07fc846005025fb2c41a813bc9850540 else 0x3efcf33395cdcb34fccb32ebcafb291c99322dc8031ddc6eb197c5d313dc46b0f7c32b09dc1c3057c0d3011bf6afadbe52f5dbceaf17bbd2ed1babae8bb97ae31b7eadcdb682d69b4f2ce7b362cc9b2eac8db132c3db042be3af02b89ac5aae9aacaa8fa962a17a8229efa70a96da52a8ffa2d2887a1e2869a16a84ba0f282da07a7f19eea7ab9dd27659ce27019b52693999a643976a5ad960254994724f9930a44f908a3eb8efa37d8d1a3378b3a28d89fa23d88921f786b2189857214d84aa10783920a381da0358049fdb7ee1f637cd9f097b71eb97919e0f7789dbf75f9d157289c6b7171c4d7059bc16e51b7b6d39b036b59ab36a91a8169019f567219af65e194164a191964298fb63b18dd63398bf62c18a1622187961318335ff17e35e8977f5d2172f5c096d55a7968559b162b58215e55731595557952753c14c3523144b50513e74ec135b4cb92f74b01293497122548311d54679185453913543f90e543590c742b9095421906d41790453f70f9b3d68f2d3c28ee739f8e3d3818dc53660d6b34f8d113390cb73250c713138c172fa8ba92e18b092b48a9b29b8a4b28789fb269896f24e08f7232889320a87f31ec87711d106ef1a6865918b05f516f8591156854114784e712e8479110840b0f283890d703070b1829908e81e50690163050011303980b9023005f00c80190003ffceec1a81ffe995cd40ffecc2e6a07ff61d73503ffb06b9a81ffd915cd40ffe48ae6a07ff64173503ffcef19a81ffe7760540ffeb9b02a07ffa6571503ffb30b8a81ffd875c540ffec9ae2a07ff24d71503ffb06b8a81ffd735c540fff19ae2a07ff60571503ffb20b8a81ffe331c540fff4ca62a07ff66131503ffb2e98a81ffc974c540ffec3a62a07ff9dd31503ffb0698a81ffd734c540ffec0a62a07ff5c531503ffb2098a81ffe770c540fff3bc22a07ff5ce11503ff8e708a81ffe3384540ffeb9ae0a07ff8cd70503ffae2b8281ffd315c140fff3ba60a07ff5cd30503ffae298281ffd314c140fff3ba20a07ff5cd10503ff8e688281ffe3344140ffeb8a20a07ff4c510502ffd32c3a81bfe9961d40dfec9b0ea06ff24d875037fb22c3a81bfc9161d40dff444eea077f61e77503bf9273ba81dfc919dd40bff4cb06a06ff61d83503bfceec1a81bfe9960d40dfec8b06a06ff245835037fcee41a817fe995cd40bfecc2e6a06ff661735037f930b9a81bfe885cd40dfec3ae6a077f9dd73502ffb3039a81bfe881cd40bfec88e6a05ff640735037fd1119a81bfd878cd40dfe43c66a077f9de33503fbb0719a81fdd738cd40fee4bc66a07f761e33503fbcef19a81fdc918cd40bff4cb02a06ff61d81503bfceec0a81bfd8360540fef19b02a06ffa65815037fb2ec0a81bfc9760540dff3bb02a06ff64d815037f926c0a81bfd7360540df) else (if i<3 then 0x645520180d01428103906455182802606126001e8401601b0ce02b0740400e190d0b81e008d0984c0d1a13c62483a1de0181a346052060901f0442c03701c0f005026028920f87c1d8581d60180e06b04f0343518130b818703083b81a34028a05017020101f0b301c0f00440a0d01e2810380d040e01b0c8a240701003422c040c064f808750789c44121914470287020505318921004486c3229983b07c04c0b018645438380243229930281841483a02c322a141cc080c864532e0503080d0e001c0c282051a0a0814142868700080c8209050809068922a1302868580e00870102a170286841003f80a32040a86c020d1506062040c8342a1702868402871068a84c08158685426000d00a2c0a85c0a0d160506881dc0b0001458150c1f01a2a0f03834541e05068b02c000e06854280e02e041c0a85c0f01c0302150a02e05800982a97000381a15081101b81230261422c0700c081a130c16605800362a17024640d1508166058001c2a141f050380b303c0700c0900f6048c8a84c07000680e130a16605800362a140683439150802e040cc342a143c06808064542c1b810804c081983454283b8001c0c8a858370210721201a0c8a85037021059816000d8a8503504141a1834282c1a2037001208103703141a141a0d100c02c1a1160580e018189c24a80604b0303457060c0285209e0606830603702c0c182607802343c0f0046860300906e050660780e002a098a0181c043000381a3009816010743450103904f000381a300c110360c1020c341b06081061a0d83040e02306c182041868360c1020c341b0608110360c0f03c011a1e0780234301702c0f00c04a02e0684234481504c0f02c030136000723430e4170140408b02c061ac0f001545060098160780e00501702c0f01c00a0283e0d03240121986860203a0d03240161986860284581e01816022809c8017020f80f060a0b80e1f01e0c1703c070005e0d808c1002e0d032403303c0006068a068188200c1d607806030c8aaa81b03c060dc00a100041ce0087034681905c0f01837003607800340b9004c0822c0f00c045013110280580a1b806062a8a0801014c040c14419302c0609a0c9022c040c1441928298081828832503702c0419202e816028683250651a160780234301b03c0b00c04a0360684234481904c0f00c0b01300d8160780e00501b02c010e468b0320b81e01816026c0205c0e0dc070236078000a0d130001422c0f02c044e131106c0b8060780e046c000dc041b202f02a058181b80e002c0a898340dc0702c0f001504c441b02e0181e0381183e0e703c0050068d81e000d0d04c0f0086880660780034441703c021a202f81e000d1017c0f000688836078043440381a10340c8b5edd7035b1d66357fd573543d4ab507d3bb4d5d27b485d18b43fd04b else 0xe104100a0203808111a08208d0811434581e00080c2207048d604207e050b061ca0820e411100c0260014820546b001021802343c0c10c006148098003e4c0038044602e00080c3807c06c010528238021a346b00c08611058100c2401805c0c3b078c1003c86e06409300c0c1e207602e06161049088054683c280d818921613020343c18098183c30880d0f0602032120c240790dc0f02283e1009a30e42912461c8458140c40e2060890c207103072861010868424c34860f000421a189381e041143450e3024120d203d068838c0b0008a0d28b00f41a30e504c0861c829810c3e0510c187c1ca183c00248346116061241a48340412454202206e022489c5c0700438362077808b0271011c030143c4e2e0224a322a1029088200710dc0e0812508d05050a0c18340c0e054260780e00070101b1a0d081a06070261303c050a0b4811232288c1fc090883849283808009816061101a166010de02b0060e82036204486e030d86054344b11461103981e008d142201701c0c0d138d8004380d0406c101e09240800d0a4140930d06c1846041c0a8312422017004343c144e1d8441060206c36271c1d83908144902840d0e00141028d05040a0c1834170e4542607808100c868583420ee00070321a160d082e06872281104c07000d031283b81a102990200741cc0c39460c0ee061a0624c003c14c60a02609020100381ce0780e00a04f0342055203802c322a903807404864492824084330d11058644918520f80b0c8a2505004c0024c0c2e0801f03619c057020310c8684c0b01c003f138b806068688e40801f0a703c011a36060c01a0789c5c00209e04110201c0521660780e00a04f02c03034344e360010801fc001a0245030721a081c036191249810381103c0681e0c1c228604c1e040e4322992040e041c8a83008171546068322a8c3905c06c0f00150c030350c8aa48340d033030e518301a0c8aa305f03c000d154a068322a8e0d4140dc0f01c0054141012607800aa4035050))
def x383h10 (i : Nat) : Nat := (if i<1 then 0x147105b9c06f40668813a000010178004210138f01380000907f30062000000036a06c9012ed04f40000e083981b11065800000000181d800000000000003416f6026200a4806f0000000134415800000000000000000000001c17d20094c192907bcc155a08540000000000000b00bc0000c01c4000000001406b903240000701dc000000820cc30804b0401b4059c0000d018c0000d066601480000000000000000000000382001027840d9200ec000000003c174804c80000e01e10c8bf06fa4193c02740000507340000402d00000707d80000305340000000010183a00a4807df0833c0adb0834000000000000000003c09260070420190125c11f405900000a02bcc0e300001018200000c150c0548000000002c141d071a817650345c01e9054c00006034b41e810067818900000813e006d040d0307eb81c7504c2c1d9a075880cff05adc0a6d0851c1ddf06600000a010d41056028240a10021c000040639810690354000000000c0a9300a1008df0397c0de0025f41630000140134084ac1dc403ef80cd702cd018c5011c000000002c1f50000280a3e02e6c10bb0265c179f03680000000000000404d6812fe03ce80e9003e0812800000c06ca0587c0cc2047400006077ec1dba044781872044dc1b8000010052902c4405d2074e41adf015800000000000004046ac0d7e031901a9803d000009075640183040800003049e415a0000240bef02478085001dbc162504de814ac079140f2403e54100f07c441735009ec170701d4cc2e906c08096202f78157b066ec16a4022381bb206b04144307100000306a0811b00003c0467062c00d80036ec00290132c1861082c0000000014061806444c2c2043b403cb01000000f03dbc04a000000000c038000000000180720000281eba01d381bda06740000e00e38009b053f014e304570042000000000b0819c2132321501454022540e26019b41feb030f017fd06d840dd201e881810000000000000280a7907b1808ce00800000300af015b803840000907b941c500000c090f04e400b8207988041a003481d11030b017200000c1a600001014ca065000004012101ab100aac0d60000000000014e80ed701a900f53020500930000201a1002ba814900002c0bc4045e4ca0f02a040550000100ef930504d750000141227041c003000003c131c068ac165d07d301b5507400000b07f7c0aa0000001fb000cc000070599001f5075240b61b0201000800100301003801210b1f1c0d00451a06240005040104140a002402050406000a13160e010d050700040131000102020521000c0002040a0203320000000604031710960013094711140805030817010b1c010d00260e0d1b1404060f0c02042f0005050a20000b000501060604000203001e1800024e0d030905000200071802010935 else 0xe302f01c35019100ffe062a81c2c01f3c03220748c17ab01780000103708143907c0000080768000010738000000002804bd049541ccd0486c0803073d41b700405c0cb00000000000003c1f830315806040784420300001002dc017c000000001013fc081dc0eb70794c0ced04980000000004045b01a000000000000001047000004043c4034000000000d019d803db0304c1e35060280a2903518197f06bb42055045881181056540b700610413600001400e00002820410694401a204a7c017000000000a067f814bb03f80000000000000d0164000000000819050492c1f2d000301b360160000000000015ff0297407f207a40000f05d400009000641c0300e800000000000000000201090000281bf1043301cab002b009a004ee812b40413c120000028216f0824420a7079d408e401a700235008800009022bc1ded078b8004501e7c00b404480000d04a84188f07ce807ee30f400001037cc0c0600fc40860050b4171d0847000c000018031506170026c004880b24075e00c83000c00002083c81f70013d00c7807b60156b03c1808fa00f880ea006e78073c03f5809c40016c083c047801a3c01ec0000605780119d019400eee07fc81400000240ca0000140bac039b016d302c20154a0519c070d00500015d045240828034e41c88021281afd03ea801d00000005b0000080ac700d480c41011000fca05dc005c0000280e460253815dd072d80f1506eac0106043440168022d005150680400700002c123a080bc0e80000000006004480b5201ba0095301b74134d02ac00009042a40bb400dc0000b03dd413c90441005430143c18f5067181c10000081e0801694006000000000b06a80000c06558057805f88169207270160f0573c19eb003f80ec405b3017bb040d402c7008581a4007e540393069c00bf00000021000003c1ea00002809f000228024104b5c16800636417c1026e80e7b00b98151604cc4)
def x383l10 : Packing := (302,3,7,10,4,14,0,x383d10)
def x383d11 (i : Nat) : Nat := 0x6028104503800f0348068180b0286c0c3071c01809021140e003c0d241a0602812050181c023491043436182018082006c06011a0da072050240e003c0c86900d02818090280c0e011a488a1b0207860a0d020180b0280c02071a488a1b0106064a0d02810450280c683280301493021140e001a401808388108a07000d200a041c85205038006434903014090380068c060283601018140c3088182034381404130380468c0602016050181c00348014001c1a240a07010dc02346028101b038040a0219406434280c0e00190d16050181c00331a301603028040c34681c00343d819f3135d0b4f56a86cb790b0bdfebb06c6c5960285470860ee9902ce4b06f8c812c16c10000ffd87503ff9dd40ffd83503ff5cd40ffc73503ff8cd40ffd81503ff5c540ffc71503ff4c540ffc31503ff84540ffd70503ff4c140ffd10502ffa2140bfd87502ff21d40dfe77502ff60d40bfc83503f78cd40bfd81502ff20540fbd41503fd84540ff930503fe80140
def x383h11 (i : Nat) : Nat := 0x16008b027b81300001e035603bb80340000802e2083800038158000000000000240180000f07f000000000a0a8c040900180001a0e4d03fd8135004600003004902dcc166000000004038f4096a102d0660000340bbe06f204c0010d81d00000d062800018074000030350000000006011806d684240000000000783008902460000000000001413b011c80880000241b740f400004047c000140cb00000000380f7e658109000240c0a600e60000300e6c0b44093d052b01ad81076019f0226008000002079000018153824c6076a0851004e408bc057900ac04574100005610209802e41c22010e00d0802881888070c01c1023e802c601f5061f009c4227801290135812b815a00d1d05c881c700f840c7701ba00d3001ee0f5e07b40475008ee0b8405d81bacc0c900ee80310824701436614c02760186820d6051907bd0450c19f403b404d6017dc1f840045051f82278c0d20a48088b84858116c0eb6073a826e412ce099503ea837580784069f08b70179c118c06e5042582c180012088000000000000080c0000000000405a0000d0574014ac0ea801d000000003c191a6ea00000000200aba0f1e017a83a4c1bda0be008d80000000000740000304b001b8e0df4054b0411803041270096a0198000180010000183e80001e0d5608280003c12e20ab5069c00f8c0b7a094307d8000082102029d03d70122416da087105ef01b000000000a02c600fc0000c0c98069583a8402e00001043001b40001c01e809120100000100143086b8015000e0000f05a70350413dc0b21042a84a0c11c00005060f03354232202a8087e02f2024a0000808d199eac065a06080494800c000140c29053402c7c1a00000000060270817f2072002cf00c700c660ba202e484058195810eb07f80000000000005094b00a3811a606810714840241e64046e095380868140e1174051098864105e02c5045000008092000070180000000a0c12b00004819401ca80d80000082bfc0e6000000003029c0001a078108c2044800000000000000000000001247063783b00001411e0086000000000000000004027c0001e0ce901eb007000000000b345283be412b402400000840e81e400000000183f4400480f8205a800000000802b6085b010b01ae60d940550000001da207ec06b08380006600001012a803a003600f92033800dbb20214c29005b0c00d20062c104710030b7d764100110407c480045cc21cf04920605119d1912009db0481851d00248c30832410060c6044bc0
def x383l11 : Packing := (28,2,7,9,4,11,0,x383d11)
def x383d12 (i : Nat) : Nat := 0x20103001a2ffd40
def x383h12 (i : Nat) : Nat := 0x60680000000000008003816e0920b2808001218a01e02000100cc0a0001c22a130003817c0fe00000005c001a06e07a84101480440d90640000000000000000e1a0000000025a15000483800087041
def x383l12 : Packing := (1,1,7,5,4,0,0,x383d12)
def x383columns : List ColumnInfo := [(64,0,831,0,11),(32,0,863,0,11),(528,0,367,0,11),(4,0,891,0,11),(256,0,639,0,9),(8,0,887,0,9),(2,0,893,0,9),(513,0,382,0,9),(320,0,575,0,8),(288,0,607,0,8),(66,0,829,0,8),(36,0,859,0,8),(536,0,359,0,8),(529,0,366,0,8),(12,0,883,0,8),(6,0,889,0,8),(0,256,535,104,7),(512,16,358,9,7),(512,8,99,276,7),(512,2,312,69,7),(512,1,332,50,7),(68,0,825,0,7),(34,0,861,0,7),(530,0,365,0,7),(352,0,543,0,7),(70,0,825,0,7),(561,0,334,0,7),(540,0,355,0,7),(264,0,631,0,6),(768,8,99,20,6),(528,8,99,260,6),(8,256,535,96,6),(520,16,358,1,6),(516,16,354,9,6),(514,1,332,48,6),(513,16,358,8,6),(513,2,312,68,6),(258,0,573,0,5),(10,0,881,0,5),(521,0,358,0,5),(328,0,567,0,5),(322,0,573,0,5),(832,32,30,1,5),(792,0,103,0,5),(784,8,99,4,5),(772,8,99,16,5),(258,64,573,0,5),(609,0,286,0,5),(96,256,535,8,5),(580,2,312,1,5),(577,2,312,4,5),(560,1,332,2,5),(552,16,326,1,5),(34,64,541,256,5),(546,1,332,16,5),(545,16,326,8,5),(537,0,358,0,5),(531,0,364,0,5),(530,1,332,32,5),(14,0,881,0,5),(524,16,354,1,5),(10,4,881,0,5),(521,16,358,0,5),(517,2,312,64,5),(290,0,541,0,4),(785,0,78,0,4),(74,0,817,0,4),(553,0,326,0,4),(880,0,15,0,4),(360,0,535,0,4),(356,0,539,0,4),(354,0,541,0,4),(326,0,569,0,4),(817,0,78,0,4),(290,64,541,0,4),(796,0,99,0,4),(788,8,99,0,4),(785,32,78,0,4),(104,256,535,0,4),(78,0,817,0,4),(581,2,312,0,4),(569,0,326,0,4),(565,0,330,0,4),(563,0,332,0,4),(562,1,332,0,4),(553,16,326,0,4),(542,0,353,0,4),(541,0,354,0,4),(525,16,354,0,4)]
def x383levels : Nat → Packing
  | 8 => x383l8
  | 9 => x383l9
  | 10 => x383l10
  | 11 => x383l11
  | 12 => x383l12
  | _ => emptyPacking
def x383index : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 21 121 5 15 7 4 x383h9
  | 10 => lookupWord 136 709 8 18 10 4 x383h10
  | 11 => lookupWord 77 404 6 17 9 4 x383h11
  | 12 => lookupWord 7 47 3 13 5 4 x383h12
  | _ => fun _ => none
def x383 : Forest := ⟨895,12,fun j => x383samples[j]?.getD (0,0),x383columns,x383autos,x383levels,x383index⟩
set_option maxHeartbeats 0 in
theorem geomx383 : graphValid x383 (boundsBefore knownx255) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3838_0 : block x383 8 0 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3838_36 : block x383 8 36 29=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3838_65 : block x383 8 65 18=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx3838 : block x383 8 0 83=true := (@block_merge x383 8 0 65 18 (@block_merge x383 8 0 36 29 sx3838_0 sx3838_36) sx3838_65)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3839_0 : block x383 9 0 10=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3839_10 : block x383 9 10 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3839_46 : block x383 9 46 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3839_82 : block x383 9 82 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3839_118 : block x383 9 118 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3839_154 : block x383 9 154 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3839_190 : block x383 9 190 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3839_226 : block x383 9 226 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3839_262 : block x383 9 262 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3839_298 : block x383 9 298 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3839_334 : block x383 9 334 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3839_370 : block x383 9 370 35=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3839_405 : block x383 9 405 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3839_441 : block x383 9 441 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3839_477 : block x383 9 477 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx3839_513 : block x383 9 513 22=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx3839 : block x383 9 0 535=true := (@block_merge x383 9 0 513 22 (@block_merge x383 9 0 477 36 (@block_merge x383 9 0 441 36 (@block_merge x383 9 0 405 36 (@block_merge x383 9 0 370 35 (@block_merge x383 9 0 334 36 (@block_merge x383 9 0 298 36 (@block_merge x383 9 0 262 36 (@block_merge x383 9 0 226 36 (@block_merge x383 9 0 190 36 (@block_merge x383 9 0 154 36 (@block_merge x383 9 0 118 36 (@block_merge x383 9 0 82 36 (@block_merge x383 9 0 46 36 (@block_merge x383 9 0 10 36 sx3839_0 sx3839_10) sx3839_46) sx3839_82) sx3839_118) sx3839_154) sx3839_190) sx3839_226) sx3839_262) sx3839_298) sx3839_334) sx3839_370) sx3839_405) sx3839_441) sx3839_477) sx3839_513)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx38310_0 : block x383 10 0 2=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx38310_2 : block x383 10 2 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx38310_38 : block x383 10 38 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx38310_74 : block x383 10 74 1=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx38310_75 : block x383 10 75 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx38310_111 : block x383 10 111 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx38310_147 : block x383 10 147 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx38310_183 : block x383 10 183 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx38310_219 : block x383 10 219 31=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx38310_250 : block x383 10 250 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx38310_286 : block x383 10 286 16=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx38310 : block x383 10 0 302=true := (@block_merge x383 10 0 286 16 (@block_merge x383 10 0 250 36 (@block_merge x383 10 0 219 31 (@block_merge x383 10 0 183 36 (@block_merge x383 10 0 147 36 (@block_merge x383 10 0 111 36 (@block_merge x383 10 0 75 36 (@block_merge x383 10 0 74 1 (@block_merge x383 10 0 38 36 (@block_merge x383 10 0 2 36 sx38310_0 sx38310_2) sx38310_38) sx38310_74) sx38310_75) sx38310_111) sx38310_147) sx38310_183) sx38310_219) sx38310_250) sx38310_286)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx38311_0 : block x383 11 0 13=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx38311_13 : block x383 11 13 15=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx38311 : block x383 11 0 28=true := (@block_merge x383 11 0 13 15 sx38311_0 sx38311_13)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx38312_0 : block x383 12 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx38312 : block x383 12 0 1=true := sx38312_0
theorem tablesx383 : checkedTables x383 12 := by
  intro k hk
  interval_cases k
  · exact (rfl : block x383 0 0 0 = true)
  · exact (rfl : block x383 1 0 0 = true)
  · exact (rfl : block x383 2 0 0 = true)
  · exact (rfl : block x383 3 0 0 = true)
  · exact (rfl : block x383 4 0 0 = true)
  · exact (rfl : block x383 5 0 0 = true)
  · exact (rfl : block x383 6 0 0 = true)
  · exact (rfl : block x383 7 0 0 = true)
  · exact allx3838
  · exact allx3839
  · exact allx38310
  · exact allx38311
  · exact allx38312
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx383 : Lower (varsX 895) (graphGoal 895) 13 :=
  strong_low (m:=895) (cap:=12) (hints:=12901687553) (by decide +kernel) (plainB (q:=383) (prior:=boundsBefore knownx255) (before_sound knownx255 validx255) (by decide +kernel))
    (index_root (g:=x383) (i:=0) rfl (before_sound knownx255 validx255) geomx383 tablesx383 (by decide +kernel))
def mapsx383 : List (Nat × List Nat) := [(895,[]),(959,[118,130,81])]
def knownx383 := extendKnown knownx255 13 mapsx383
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx383 : Known knownx383 := extendKnown_ok (m:=895) validx255 lowx383 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx479 : Lower (varsX 991) (graphGoal 991) 12 :=
  strong_low (m:=991) (cap:=11) (hints:=13438558465) (by decide +kernel) (plainB (q:=479) (prior:=boundsBefore knownx383) (before_sound knownx383 validx383) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx383) (before_sound knownx383 validx383) (128,0,863,0,11) (by decide +kernel) (by decide +kernel))
def mapsx479 : List (Nat × List Nat) := [(991,[]),(1021,[118,130,81])]
def knownx479 := extendKnown knownx383 12 mapsx479
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx479 : Known knownx479 := extendKnown_ok (m:=991) validx383 lowx479 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx503 : Lower (varsX 1015) (graphGoal 1015) 12 :=
  strong_low (m:=1015) (cap:=11) (hints:=22028484865) (by decide +kernel) (plainB (q:=503) (prior:=boundsBefore knownx479) (before_sound knownx479 validx479) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx479) (before_sound knownx479 validx479) (528,0,487,0,11) (by decide +kernel) (by decide +kernel))
def mapsx503 : List (Nat × List Nat) := [(1015,[])]
def knownx503 := extendKnown knownx479 12 mapsx503
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx503 : Known knownx503 := extendKnown_ok (m:=1015) validx479 lowx503 (by decide +kernel)
def livesamples : Array (Bits × Bits) := #[(0x742ee97b7e62b7e89db2c6d63a3dfe77d0004fc332e448005f01a1dab4010481132f3705021ef50ea5c2d27660f9aa819c85c11a0a558afd106e6b5298453d885120b4f26c04094446199e64a5f1099049ba1774bdbf315bf44ed9636b1d1eff,0x44208b797e63a788143246562a25fe140f00cfc0709420011f80018800005805002c0308801ec046010440d24cd5a2a11c0042180e44863c10422b90822529801081b442280409450218966425b0099809a21045bcbf31d3c40a19232b1512ff),(0x360d340001cee85060c999a1f5d605642e78206730a40120e07d8e2050e40d9e808e4c5074030091a9e2826db10048a486510584038be1008e9c41f8a08342598b78c0271c96a213a9e620a5d00e8e206f9b069a0000e774283064ccd0faeb02,0x321c20000084484000c998a1d5d000600078002380280130c07d8e20606c0410c08204c00000009128e2a228a00248068049890000a341404e84c46c20004059c3784221d41020b0b9a66081d00e242176190e1000004224200064cc50eae800),(0x140d7fe9baa1605ea76605f208bff0897cd301847038b918f86144184d7b8072cc0da5eff113aca460102133f3c9602601204e000143b83f008008075df863480d5188000fd5a4b0f2c85da0649c24a1800a06bff4dd50b02f53b302f9045ff,0x4560d69e3b2a1605ea06404c200bf701b70330185f030480000021c000838a0f3c40c01eff0138081610100119289450681224e010101083a008208115cb26200481088a00e7424b0609050a2241c2420822b06b4f1d950b02f50320261005fb),(0x1310034142b548c311382504dfe40a8010c11f783c50244a06e1c205082f5480641071008180ca70020c05b2ce87866974419200cc20063a763089160360e084209aa240d109a49c8058c0d515b4381dd3898801a0a15aa461889c12826ff205,0x1210096104d108c211b821005fe4089408c08fe0202428087fe18003b8145080c03530610080c066004c03b6c6d522a014005201ec0046204a308036820080842810a2404108a1048150c89595b6281cd3890804b08268846108dc10802ff204),(0xe88b700a850d14bdc24d9869821a2003ee3fc120001c444e90167a06638aa9613e43cc020364d58952358489906a004e79564b46d573298f050044050d985471c6484c1837d254bc340105000a9df365267445b80542868a5ee126cc34c10d10,0xa88f7402810c1035ca4598a9801a0000303f000d034bd5668016720047ab236033c2489274602581fab114092108514ee1d78c66113b39c2050c44491dd85271c760489916d254b87c0301020a09d261245447ba014086081ae522cc54c00d00),(0x89b0dc85081011332b8d79a9dddb0091e0329200c34858260009a9dc4f03063a0130a8b765a9220cdcc93b0c722b6154618b39eb69887cd00b79b62b14800c075c0848bd408a4060599768024162f4a7b044d86e428408089995c6bcd4eeed80,0xb910548401101033298d31a995da0101700710120040598a400124140f01842a6d11c8a575613228d6c93305322a4058609511e661087840a039142b144084244a2808bd41da403849c568815043f005125c882a420088081994c698d4caed00),(0xcfe30ef5a55921bfad24330a0a6fff8fed858ccc13d7dc8127d2007e9c13d1c99e25f23a1540f267c1315084524891f8063606f5bb0abcbdb0db191903c195e23a05814c23e3af0960419a587f53105c85e7f1877ad2ac90dfd69219850537ff,0xcda30fe5ad7937bbad24210a0a2f7e9fcc87a00c3757bc83388200df9493d1e81e75f03a51e1b666c71d50d41864017843a6063daa58bcbdb049191307d49522380528dc216b8f0d4051085c0f51905c89e6d187f2d6bc9bddd69210850517bf),(0x828729a094c5eb4a14578e124b24489e08788084009da251398ed82bb138208088c0374208bec506490ecd58441463a60328c029acc604384f869d75ea3c489a2007ff008e40dd843232e15c8cac0dc8a4414394d04a62f5a50a2bc709259224,0x28f2961c4c5e9c814508e124a2408120880c8a4009ca251bd00d823b03860c080803740008e45c008268cc2441529a69768c01986e604184d86cb44ea3458dbb116f740be00b584b032827488ac0d88e5014794b0e262f4e40a284709251204),(0x85c00166014c8045642ce7c24209040030f4c80c90230b4002902004a60c270409885a80a50203130d16c0800801c17082ab8501021502201832a804e2023e9a5c2234b922011a290a213232a0045b204042e000b300a64022b21673e121048,0x4ca00a5206c0044242ce542000806003284001c8000274801c0b0000602a14008a04008a10091120028c0801001c030808a8001021010205842280682a2a4985c255029a00108234221322200807a20400265005290360022121672a100040)]
def liveautos : List (List Nat) := [[],[81,130,118],[32,83,116],[48,129,82],[128,49,100],[16,82,131,100],[48,33,133,118],[80,129,50,116],[32,128,49,81,116,100],[128,32,81,49,100,116],[16,32,48,128,80,100,116],[80,128,48,32,16,116,100]]
def lived8 (i : Nat) : Nat := 0x28a1af792bb71aaa64d815027d91e7b7552505314c140
def livel8 : Packing := (2,7,8,0,4,3,0,lived8)
def lived9 (i : Nat) : Nat := 0x7c021b81420e80c20f01c3e02841d02040078102007408107c001f0143e02fc002f0176031000790f4041e80820000078081e030fc041f8083f00874050fc00100000000000001204771b44708416fc3e6f039ae436ad8356cc326c72f6bb2c6a825e872127b1c66819663182571524b106380ba2506e1905a140460f0320a01e0500a0061bfaedc6aa99560540a3deea57755326c0a8186febb71aaa64d815028bfbaf5db52a9302a04bee37130691a35454093deea194dcb04a8a8137b5d4b319360551503e6cb26c12a4c0aa2a0556f75ebb6615250540cbdaa0996cc34a98a8126fdd6b31a8655315025d7bad66350aa262a0517f75ebb6a5524c540f9e2cab049930298a81fb855460932605315027b6baf662a4a0a62a049bf75acc6a19548540975eeb598d42a890a8125fdd7b31a564d215028f7ba95db4ac9a42a055be75abb649814c140a7dc6d368d92a2982816fb0da6d18154530502afe1b6c9302a8a60a07ed860952605514c1409fcce9d98c1282982813db9d7b3152505305027bb3af662a498a60a057f236d82549314c140fdc8aa304c0a6298281fbc182549814c530502ff25baa928298a60a07fe060952505314c1408f7ceb598dc242982811df9d7b31b548530503be3370aa2a690a60a077e46e1544c5214c14093d6ea194cc444a8a8153b5d4aee8864e11502ae6ba95dcaac9c22a055d534db995582845409bd2ea598c9c4508a814f98da6d1b354530503b725774428298a60a077e0aee22505314c140fdc144444a0a6298281bf12cc5515384530503f62510aa2a708a60a07fc05515388a114c140
def liveh9 (i : Nat) : Nat := 0x1c001
def livel9 : Packing := (49,6,8,1,4,10,0,lived9)
def lived10 (i : Nat) : Nat := (if i<2 then (if i<1 then 0x97f4cb6615384540df36bb5515384540fb36885515384540ff155460d5384540f3d6886563384540b7d5c96163384540fb9688552338454097f5c8aed928454097f5c5aed9284540d3f6bba21928454097f4cb6159284540d776bb9559284540f3b688551928454097f4cb60d928454097f4cb54d9284540f3d6888cd9284540f756558cd928454097f5c9aed8284540b7d4c36e5828454097f4cb6558284540d775b99558284540d7b5b9551828454097f4cb64d8284540d7d5b98cd82845409df5c7aed528454097f5cb661528454097f4cb6615284540d3f5b9a21528454097f4cb64d5284540d7d5b98cd528454097f5c96e13284540d3f5b9a21328454097f5c96d53284540d775b99553284540b7e6cc6622284540b7e6cc6562284540f3e6886562284540b7e5c96162284540f765989562284540fb66889562284540bfa6cc5522284540f7a5985522284540fba6885522284540b7e6cc64e2284540f7665564e2284540b7e5c954e2284540ff255454e2284540f7c5988ce2284540fbc6888ce2284540f7c5958ce2284540ff46558ce2284540ff85548ce22845409fd9c3aed824c140ebeaaaa22224c1409ef9c6aed814c140afb8ca6d1514c140df99b46cd514c14097f8cb649514c140dfa9b4889514c140fbaa88889414c1409fd9c5aed314c140cfdabbaa9314c140d7dabb661314c140dbdabba21314c140ebdaaaa21314c1409fdacc6d5314c140cfdaaa6d5314c140df5a556d5314c140df99546d5314c140df9abb551314c140fb9a88551314c140d7dabb649314c140f3da88649314c140d7d9b5649314c1409fd8cb609314c140dfcabb889314c140efcaaa889314c140f7c998889314c140fbca88889314c140dfc9b5889314c140ff8954889314c140bfd2cc605314c140dfd2bb605314c140efd2aa605314c140dfd1b5605314c140ff9154605314c140f7d192605314c140fbd182605314c140ffc222605314c140ff92bb505314c140ff91b8505314c140ff91b5505314c140ff91b2505314c140ff9182505314c140ff9152505314c140ff195454d214c140bfd2cc4c5214c140dfd2bb4c5214c140efd2aa4c5214c140dfd1b84c5214c140f7d1984c5214c140fbd2884c5214c140ff91544c5214c140ebf2aaa22114c140ef72aa956114c140fbb288552114c140bfd2cc54e114c140efd2aa54e114c140f7d19854e114c140fbd28854e114c140ff518554e114c140f3f28864a114c140f7725564a114c140f7d15364a114c140b7f1c960a114c140ff515354a114c140efe2aa88a114c140f7e19888a114c140fbe28888a114c140ff625588a114c140ffa15488a114c140ffc15388a114c14097b5c4aed938454097d4c36e58284540df92bb505314c140fb9288505314c140ff8222505314c140ff115454e114c140 else 0xbfb6cc549414c540ffa582549414c540ff95c84c9414c540ff95c54c9414c5408ffdc3aeda84854097fdc5aed98485408ffdc3aeda548540a7fecc6a19548540c7febb6a19548540afbecc6a15448540a7fecc6959348540c7febb6959348540a7fdca6159348540c7fdba6558348540cfbdba5518348540c7fdb96a1534854097fccb6615348540ef3da85515348540ff1d5460d5348540e7f5a86553148540efb5a85513148540d7fabb649814c1409ff8cb549814c140fbe982549814c140dfb9b46c9514c140dfb9b4609514c140ffb1b4605514c140f7f192605514c140fbf182605514c140ff7152605514c140bfbacc609414c140bfbacc549414c140ffa982549414c140ff99b8551314c140ff9954609314c140bfdacc549314c140f7d998549314c140ffc982549314c140ffd152605314c1409ffacc6e1214c1409ffacc6d5214c140d7f9986d5214c140dfb9546d5214c1409ff9cb615214c140dfb9b8551214c140dfdabb54d214c140dfd9b854d214c140f7d99854d214c140ffd1854c5214c140c3fe886e2aa64940c77e556d6aa64940c7f6116c6aa6494097ddc3aeda96094097dccb6a63360940a7dcc36a5a16094097edc5aed988894097edc1aed9888940e3eeaaa222264540f3ce888ce2264540a6fdc6aa9956054097bdc4aed9360540a6fdc6aa99360540aeddc6aaa3360540a7dcca656336054097f5c1aed9260540a6fdc6aa99260540c7dcba8cd9260540b3dcc36e58260540aeedc6aaa2260540a7ecca6562260540e7cda98ce226054097f9c0aeda954540a7dcc36a5a35454097bdc4aed935454087fdc82e9925454087fdc32e99254540c7dcba8cd925454097dcc36e58254540a7edc9aaa2254540a7ecca6622254540e7ada46622254540e3eda9a222254540e7cda98ce2254540ef8da48ce2254540a7f4ca6498154540fb65825498154540eb3e88955a550540b79cc36e582505409dbdc7aed5250540ebaeaaa222250540ebae886962250540ef2e556962250540fb8e888ce2250540c3fdb9a21a84c54087fdc52e9984c540a3fdc9aaa884c540a77cc56a5a54c540c77db9955a54c540c3fcbaa21954c54087fdc82e9924c54087fdc52e9924c540c3fcbaa21924c540a7f4ca649814c540fbc5824c9814c540ebb6aaa21414c540bf96cc4c9414c540ef96aa4c9414c540fb96884c9414c540ff85824c9414c540efa6aa889414c540fba688889414c540a7dcc36e5a848540c3fdb9a21a848540c77db9955a548540c3fdbaa219548540c3fcbaa21954854097bdc4aed9348540e3dda9a22334854097f5c5aed988454097f5c2aed9884540d3f6bba219584540dbb6bba215484540d3f6bba21938454097f4cb6159384540d776bb955938454097f4cb655838454097f5c9aed538454097f5c96e15384540) else (if i<3 then 0xa062050f807c010391d03fc00e0981c9281fe0170640e48c0ff00f8008724d14e82b3d79cccd6e63b2f995dc9f64b3235908c81e3c71bf8b3c50e23f0e185ec2660eb037809bfbdf96fc17dbbeb5f12f657a0bc75df2ed573eb8fdc02ddd6dcb5edaaed3367ab34595ac89632b09d806bf95eaaec574eb835afaced662b0d567ab15542a7d51fa8053869854a3a4251ca8a7434a0acfda7af3b89ccce1e7053709a8ccfe65b31b97e4baa57d29f946c9ee4b924a915c86640f2028eb47123651938ba45222530fd86f433215b09b84b42120e5060820c0be03b00b7fcbfd1fdefc37bebd11e64f20780bb55d86eb174fba35cf6e5c72bb8adc18ded6e736f1b54d986c33605af8d6a69f3449a00cee66132f5956c99643b1d58acc4461fb0b5836bef5e82ef9724b665b0ad3d67ab2b572ab815b6ac955baa95526a8152aa94147ca2c513a88943aa0b50327d13c49d04df26e53689a24cea66130c9744b1257529694649a248922090b48323d11c48d0465a2e514e895441a1c50be84d41da0a502e8124001fecfec7f13f61f9cfc47dd3ec1f18f687af3d51e94f4079b3cb1e44f1877a3ad9d58e6e70b36f9a98d286823381978c7e63a3141858c085f22e99704b5e59d2c595b0a8053b2949428a0a4f3270933c97a4ab246118088242f20e8ff87a43a61c38d6c62a2dc1650ae054c28712d892445422511008384121f70f2878039c1bc0d5062c2f21670b1054027c12c08d04541d20d705581c807200097fdc5aed826454097fdc3aed8264540c7febbaa9826454097fecc6e13264540c7febbaa99560540c7febbaa99360540b3fecc6558260540aefdc6aa95260540c7febb6a55260540a7fcca64d5260540c7fcba64d5260540aefdc6aa93260540f3ed956093260540efb930691a354540a7fdc9aa98254540a7fcca6e58254540e7bda46e58254540b7dcc36e58254540c7febb6a58254540a7fcca64d8254540c7fda96e13254540cfbda46e13254540a7fcca6613254540e7eda96093254540efada46093254540b7f6cc64d8154540f3f5936098154540f775935498154540fbe5824c981545409fbdc5aed82505409fbdc3aed8250540cfbebb6958250540d7bebb6615250540fbad8360952505409fbecc6e1325054097fccb661a54c540a7fecc6a1954c540afbecc6a1544c540c7fdb9695824c540e3fda8655824c540ebbda8551824c5409dfdc7aed524c540afedc2aa9524c540c7febb6a5524c540a7fdc96a1524c540c7fdb96a1524c54097fccb661524c540afecca609524c540e7eda9609524c540ebeda8609524c540f7cd95609324c540ff8d54609324c540ffc5c1609324c540f3f595609814c540fbb554609814c540b7f5c9549814c540fbe582549814c540f7d5954c9814c540ff95544c9814c540bfb6cc609414c540 else 0x1c0048401202088044012100740242011804840230090b40c1f07f800401201e88856141587c1e10183c24120810c07d60f19048260508074024221b85030140c040d40201580c28180e80c2000381e1e078781e1e038780e104d040b0005d020c03a0121004b408240c0740c1d0358105e0f0e82c201e00908824140c0445e100d040456031001820702044401038102418081e420702040f1a0f101c061d0787c01a0f10103c1e200f006440120078803a0121007407a2d020403c01210078078204280f0403501e8bc0360f101d007a201000645e0108340a1d02d8105c050f8083e020f80181e240c0408b6036078f80a078102342079081e301e2d0105c07a0217804206b08103180504a0c0f0104a04081e0210063c0420247017c003f00019c5e02f00820c7e01e028811c1012f8044418083c001f0007c00102d02784218098143e000f80020001a7c004231f81bc09e00f0088a0be06f0278008464f0007c001e04821c5c03f0002a07e00098143e000f8003e0108190126206817c020a31824813c204582504018f000840a1f0007c001209040020c0407760604b0c07c0a804a8f81e130287c02226e078c1c0f0f03c3c070f80420750498bc001078003e000801407c09a182881262f000407443904d0fc000430540c1e000f8003e00081bbc03e00d07c060a00181428120f8003e000f8003e01f00024060f0007c0010001e00083c001f0007c001f000400f000400b0207c001f00041e00082c081f0007c001003c001f0007c001008483e00088603e01088483e000f8003e000f8003e00083c0010000000000b0206c08100000000007020781e049100447e021780681c0a31b03c0c809518104031606045110301d010404e181c860318051010721f0007c001f00040b60a6178003e000c06030180c0600f02033806011e3020e42818c02881e000f8003e000f8003e000816c13027027805072340c026040980f800202704a0bc0805504a0fc0340f04a0c09e094178040300941809fc0209870640e4a040f00f8001544f0007c001f000680a09815015c124391f8003e0121c8800b010404390906020f000780a1e0284830c05170143e0008380a1f0107c041701041e01f0008))
def liveh10 (i : Nat) : Nat := 0x207c8071159c5ba193c0ba0420096135020e188000000000041778190001421f050006b090000d0a700f604fc1b10140000000000103ac2d40238250002c01a00942bc075c0d91b74553168000000342f0002c04009844250020ea00020226048000000000001a800000000000003c1791a14183033c2ca08cc1c0000000605800000015a40000000f14c000b0a38030001040a078030a14b057a06959d9029027a04782e60ab815e104010508232648404008014a08c
def livel10 : Packing := (316,5,8,6,4,13,0,lived10)
def lived11 (i : Nat) : Nat := (if i<4 then (if i<2 then (if i<1 then 0x54a11503ff2c12a508a817fdaed3284540efeb7299422a05ff5b84ca11503bfacc26508a81efda213284540bfeb6a99422a077f5954ca11503fbb2aa6508a81fed5513284540ffcb0499422a07fe58588a11503ff2c1c4508a81ff954e2284540bff576d1260a05ffabb60930502ffcdd30498281bfeaa9824c140eff372c1260a07fe9a888930502ffd5db4298281efea21a14c140dff344d0a60a07fea2268530502ffd5db02982817fe6e9814c140dff554c0a60a077f99260530503dfcc130298281ffa889814c140bff576a8a60a05ff9ba545305037fd552a298281fee6d1514c140ffb366a8a60a077f99254530503ff5112a298281ffc605514c140ff7304a0a60a07fb95250530503fed5da6298281ff66e1314c140ffb35098a60a07fd9b54c530503fecd2a6298281ff66c9314c140ffb34498a60a07fd9824c530503feca9262982817feaed214c140bff37490a60a06ffaaa48530502ffcdc24298281dfe661214c140f7f51090a60a05ff9b548530503fdcaa24298281ff654d214c140ffe35108a60a07ff1a584530503ff8c2c2298281ffc68a114c140ffe30508a60a07ff152845305023fedc554c92811ff6d6aa649408ffb6355324a057dcb36a582502bf75db3111281df36623388940f79d1119c44a063feaaa21915039ef44466c8a819fbaaa2264540e7dd1111322a077ce338899150277edb554c0a819fb6a622605408ff974c92a2a067eda9889515035df55510a0a81bcf955a550540f73d1119a82a073be88649415037d755444a0a81deb6622250540f75d1111282a06fada588941503fc719c44a0a811ff2e9984c5408ff974c9262a06fb6aa50531503ddb4428298a81fe54c9414c540ff4c44a0a62a063fda9a2121502bfb5db3108a815fdaed9584540e7ed10cac22a057f5b961611502fdb5daa908a81ded6615484540f76d10aa422a057f6bb64e115039fb4432708a81ddd9559384540afeb72c1c22a057f5b954e11503f9aaa2a708a81df56623384540f7ad1119c22a077d5958ce11503fab2ac6708a81fe55523384540afed76c9422a073f68864a11503bbb2ab2508a81ded5519284540efac66c9422a057f5b960a11502bfadcaa508a815fd6e53284540efcb3111422a07be68888a11503bf2cac4508a81fd99562284540ff4aa911422a077e59388a11503fe319c4508a81bfaaaa224c140efd33111260a07bea8888930503ddd4428298281fea889414c140bfb57698a60a06fdaaa4c530503beccc26298281ef6a21314c140bfb36a98a60a07f99544c530503becc926298281ff2889314c140ffa30298a60a07fd131485305037f95542298281dfc662114c140f7e51108a60a07f725584530503fd8aa42298281ff454e114c140efe32508a60a07fe222845305023deda554c9a81fe4505314c140 else 0x819ff6a5a54c5409ffd76d2a62a067fdb9695315033fecab4a98a81bdf955a54c540df7aa8d2a62a067feaa655315033fed432a98a81cffa21954c540df7d54aa262a06fbda855131503ddf442a898a819ff6a5a24c540cffd54c9262a067fda8649315039ff4432498a819ff695924c5409ff974c1262a067fda9609315035fed430498a819ff6a5524c540bfbd7699262a06fdeaa4c931503beedca6498a81df76a5324c540efbb3099262a07bde884c931503beecaa6498a81fe7551324c540ff9b0499262a06feeaa88931503bf6d4c4498a81bfb6a2224c540efdb3111262a07bee88889315037f6d2c4498a81dfb656224c540ff5aa911262a05ff6bb605315037fb5530298a81dfd6e5814c540efeb52c0a62a06ff5a560531503bfacab0298a81fed551814c540efeb24c0a62a07bf58260531503fea9930298a81ff9889814c540ff6d54a0a62a07fb5a850531503fdad2a8298a81fed689414c540ff6b04a0a62a07fb55250531502bff5db5290a819ff6a5a8485409ffd76d4242a067fdb96a1215033fecc35090a81affa21a848540affd76cc242a057fdba661215033ff5533090a81affaaa8848540e7fb5344242a067fda9695215027ff5db4a90a819ff6e5a548540cffb30d2a42a06bfe88695215033fecab4a90a81bdf955a548540df7aa8d2a42a057febb65521502bfedd32a90a819ffaa99548540cffb50caa42a073fe88655215027fedd30a90a819ff6a58548540bf7d76aa242a06fbeaa551215037ded42a890a81def6615448540f77d10aa242a067fda968d215027ff5db4690a819ff6e5a348540cffb30d1a42a06bfe8868d215033fecab4690a81bef551a348540cffb26d1a42a06fde3368d215037fc9834690a815ffaed9348540affb74c9a42a067feaa64d215033fed2b2690a813ff6e983485409ffb74a9a42a057fdb954d21503f9eaa2a690a81bf7aaa3348540efbb5319a42a06fdda88cd21503beecc46690a81ef7a223348540dfbb4b19a42a077dd958cd21503fceaa46690a817fdaed3148540dfed5498a42a077f5b94c521503bfad4a6290a81bfd6a13148540efeb3098a42a07bf6884c521503bfacaa6290a81fed5513148540bfed76c2c22a077f5b961611503bfac2b2708a817fdaed8384540efeb72c1c22a077f59560e11503fdaaa30708a817fdaed5384540efeb72a9c22a05ff5b854e11503bfacc2a708a81efda215384540feeb0aa9c22a07fd58354e11503feac2c6708a81dfd6159284540efeb06c9422a077f55364a11502ffb5db0508a81dfd6e58284540efeb2ac1422a07f765560a11503fdaaa30508a81dfd64d8284540f7eb06c1422a07fd63360a11502ffb5daa508a81dfd6e55284540bfeb70a9422a077f59854a11503dfb442a508a81dfd64d5284540feeaa6a9422a07fd633) else (if i<3 then 0x50a9a42a077fd9854d21503feec1aa690a81ffd6153148540fff362c1260a07ff9ba60530503ffcdab0298281ffe695814c140fff364c0a60a07ff9a260530503ffca930298281ffe6c9514c140fff304a8a60a07ff9b848530503ffcd424298281ffe6d5214c140fff34a90a60a07ff985485305027fed9d54c12813ff6c6aa60940affd76d4b04a067feaa6a582503bee59b52c12819ff6a5a360940dfbd5519b04a077dda98cd825033fed4b42c12819ff6a5a84c9409ffd76d4264a067fdb96a1325033fecc35099281affa21a84c940cffd54cc264a067fda969532502ff75db0499281bfbaa9824c940efdb72c1264a077eda9609325033fed4b42992817fbaed8388940efdb72c1c44a057febb60d91502bff5db04c8a819ff6e98264540cffd54c1322a073fd8360991503bef19b04c8a815ffaed3264540affb7099322a073fe884c991503bf6c1264c8a81dfb60e2264540affd76d4b02a067fda969581502bff5db2ac0a815ff6e99560540cffd54cab02a067fda968d81502bff5db26c0a815ff6e99360540cffd54c9b02a06fdeaa8cd81503beed4c66c0a81df76563360540cffb52d1302a057febb64981502bfedd324c0a819ffaa99260540efbc66c9302a05bfebb609815035ff55304c0a81cff6e58260540e7fb52c1302a073fd9560981503def19b04c0a819ff6a55260540f7db04a9302a07bed824c9815037f755444c0a81dfb6a62260540efdb2b11302a07fce33889815027fed9d54a8a813ff6caaa54540affd76d4aa2a067feaa6a551502fdf5db48a8a81befaa9a454540cffb52d1aa2a06fbda468d51502bff5db26a8a815ff6e99354540cffd54c9aa2a06fdeaa8cd51503beed4c66a8a81fe76923354540cffb52d12a2a06fbda468951502bff5db24a8a815ff6e99254540cffd54c92a2a077bda464951503bef19b24a8a813ff2e98254540affb72c12a2a067fda9609515037f755444a8a81dfb6a62254540efdb31112a2a07bee8888951503fd6d2444a8a81ff38ce2254540bfed76c0aa2a06ff6aa60551503bfadcb02a8a81dfd6a58154540ff6b48c0aa2a077f59360551503feb19b02a8a81dfd6498154540f7eb04c0aa2a07f755260551503ff311302a8a81bef615a550540df7aa4d2a82a05fbebb60d41502fdf5db04a0a81befaa98250540ef7b72c1282a06fbda560941503ddec1b04a0a81fe78cd8250540bf7d76a9282a06fbeaa54941503bdecc2a4a0a81eefa215250540ff3c66a9282a07fad8254941502fdf5da64a0a817ef6e13250540f77d1099282a07fad824c941503fd6c1c44a0a813ff6e2aa4c5409ffb6b55262a04ffdb2aa9315033ff5535298a819ff6a5a84c5409ffd76d4262a067fdb96a1315033fecc35098a81affa21a84c540cffd54cc262a06bfeaaa21315039fed4d1098a else 0x804d0011fe53fa87f0cfd31f953ef07d9cfab1f393e507c2cf771edd3d987aecf551e993d10791cf0f1df53bc876bcecf1d5d3a80742ce771cb9390871cce191bfd37c06e7cdb51b4d36306bbcd571a9d34b8686cced19a532e064ecc8318d13150619cc1f17f12f785e4cbc117352e005bbcb51166d2c40583caf915e12ba056fcad1153d29b0519ca2b142d27d84edc9c7134126304b2c945123d23f8468c8b111392220436c853107d2090407c7f50fc11ee83c9c77f0ec91ce038ec6fd0dc51b38353c6870ce51960321c6290bf917582d7c58f0ae91538296c50d09e51378264c4a308f91188220c42108010f801dcc39f06f10d781a4c32306110bd016cc2bf05490a28134c24f043908200f0c1bb031d05e80a6c121021903c806bc0bd01450238039c059005900017ffaeda160940dffd54d0b04a06ffda5685825037fed1b42c1281bff615a84c940dffb62d4264a06ffd816a132502fff5db4a99281bff6a1a54c940effb30d2a64a07fedb560932503ff6d2b0499281ffb6c5824c940dffb50d0a64a06ffda568532503ff6c134299281dff6c98364540effd76c1322a077fdb560991503bfed9b04c8a81dff6e13264540effb6a99322a077fd9568d81503bfecab44c0a81dff64da260540f7fd76c1302a07bfdb560981503dfed9b04c0a81bffaa95260540effb52a9302a077fd9354981502fff5da64c0a81bff6e93260540dffd5499302a077fdb94c981503bfed4a64c0a81dff6553260540effb26d12a2a05ffebb609515037fedd304a8a81bffaa98254540effb72c12a2a077fda960951503fded2304a8a81dff64d8254540bffd76992a2a06ffdba4c9515037ff55264a8a81dff6e53254540effb52992a2a05ffdb84c951503bfecc264a8a81fef6913254540ffdb04992a2a07ff53260551503fded9306a0a81fefaed8250540ff7b6ac1282a07fbdb360941503fdedc2a4a0a81fef6cd5250540ff7b06a9282a07fbdb84c941503fdedaa64a0a81bff615a84c540dffb04d4262a077fd9869531503bfed432a98a81fef6a1544c540bffd76c1262a06ffdba609315037ff5530498a81bff695824c540effb2ac1262a07fbd5460931503ffad8b0498a817ffaed524c540dffd54a9262a077fda9549315037fed42a498a81dff661524c540ffdb04a9262a07fddb84c931503feedaa6498a81ffd549814c540dffb0ad4242a06ffd836a121503bfecc34a90a81dff6a19548540dffd54c2a42a077fda961521503fded42a890a81bff60da348540dffaa6d1a42a077fda564d21503bfec2b2690a817ffaed8348540dffb74c1a42a06ffeaa60d21503bfedcb0690a81dff6a58348540dffb4ac1a42a077fd9560d21503fdeaa30690a817ffaed5348540dffd54a9a42a077fdb954d21503bfed4aa690a817ff6e15348540dffb)) else (if i<6 then (if i<5 then 0x725e05e0460360fa0cc0d3603d06304f079381581380d83f036830d40d81ac17c1e4c0d60b60f1b07f02701b07606d061981703683383c9c034188723c05a0c6094392602f00f006079380203e8360e49404c1941b0724027e00c0fa0d80e2e07f0050681c9009c01780281c2502098240e51c0141b81e3e00067c0fa0d0a60943207f01847506b0581c9809f8101e283583027c0e4fc0141b81e3e00837068e0bc0f6090943a1bf02700d0660785404a1f8028350e47c0181cc128724c0fe00609c0e2607f00f006071180a83582d0e4941ac1781e3c05a0d60c4392607f00b066071381f81b81380f8078000a0e81fc0dc09c07c03c000727cb4995bf29d6505c9b992cf2456449c8298faf1db6381c6998c8f17d62ddc5818a2f1316245c45187ff0eb61adc309856f0936109c1a9824f03b6035c0197f8efd75f79be897c6ef795ec9bd4179def275e19bbf9774eed55d81bac9751ee8f5cf5b99972bee495c81b8b170eee0f5c01b7c96eeedd55b8db6b16c8ed7d5ad1b56969fed2b5a21b3c166deccd5971b291641ec6f58a9b0b960fec1157f9afa15e6ebb95749ae415baeb6756b1ad11594eb1555f5ab81565eab15545aa5153cea6554ada909516ea1f5415a7c14eae9c15359a6614c1e96f52b5a4e9492e90b51eda389463e8b3513da22943ae8675081a099402e7eb4fad9ef13d6e7a54f099da93a1e72f4e299c31375e6cb4d859ae9352e6914ced99a132fe63f4c1997e12eee5bd4b5d96392b3e5594a7194a9281e4e3499192d1249e473489990e1208e40347f58fb11e8e3b1472d8df11b6e36546b98d3919ce31346158ba9164e2a345298a31141e27544b58901112e21143f987890e3e1b3433186110b1e15542998511091e10341d1835105ce0a541398209030e047407d80d9016e02540398051005e0033fd17f50fdfdf993f217df0fb3df593ea17cf0f90df013db57b48f5bde913ced79a0f23de3f3c497858f03dde73b9976b0ed1dd893b017598ea2dd2b3a2d73d8e5edca9391171e8e29dc4b388570a0e03dbf937bd6f58ddadb9536dd6d98da5db2b36456c20d76dacd35896a90d3eda5d34856888d0cda1133f967a0ce0d9b9333d6628caed94f328d64e0c94d92132316428c80d8f931e16358c60d8a7311961c8c31d849305d6098c05d7eb2f955ed8bc7d7692e9d5cb8b7dd6e72d995af8b4bd6772cb95938b22d6252c0957c0ae7d5c12b415648abbd55d2a8554a0a7ad4ed299952b0a51d48f28c55138a22d42b282150089ead3cd274d4e309bbd36926a94cd0992d30525a54a98942d25f247d48c0913d213240947f08f3d1d923a147208dfd1ab232d45f08add15322714478887d10721fd43c0873d0df21ad4338862d0bd216942b0851d09b21254228840d07320d5418882cd0512091410081bd02f20414060 else 0x6090aa3f07840d404b80f80582c2a8c01fc02c16154460f0a9094180c7078823813c250606fc03c0042415250a907b101b836823a29054942040ec0dc0e806283f037031002401f407c0140a0a01507012030a050a8095280c809701f00d058551811183f8078002a8a031c1e2e00080c707f008c13c8605c1e1018e0fe00182790c098103c001e000854e030500c2a681427c6083c0140a1504a05e04c0c6090aa2d028780f0338042a8940ac17c021544213e0f1700078002429c1e2e00090c0583c3c1e1e000f07848603c1e16030b018783c3c0012180b0290c0b83c3c001e000f07858103c0016050f07848bf83c5c001e0fe0015058783f8005c0016050f07f000980c242fc1e2e000f078413c8605c1e1e0fe00102790c0b83c2c1e16030f078783c3c1e104ee020728390a3284260784a0f80780828c687210624180490a427010406f8082320e428cb073c042039606e0208a241cf010b8182870388ac9c0dc040661464e010e02f02306506a1c9410583303a8349c05c022018e06e020510a32f03701028851900e703c580bc0281e1464c0f064095180c303602f008519703c20d181f41781cc125e04a02e00a0d8392f01d01506b05c1c941ac01409c250940fc080aa12840390780550a32607b0204304a138080e4154250811c09e1283039e020780550a3280c50684a0c2318101e283703d830dc05c17c121544e020510a31f00041040de830176837038d80bc00c121544e02083381402c506d066079980b80582c2a8811140c0b141ac1781e6e020a1cf010b8083c041c050f0170008234013807803834060278139011a007c03c01c1a0300de09c8021004e01084018e00e0909f04e4902870328248e47c0fc09818c124725a05c0c609e0f270020c22a8f01f81b8138018260e4dc008308aa3c07e05e04c0fa0c6093702701e06d0621c9781b81781380383c08cd80fc094198128725012e05e03e02e01a0c04d3d03701e06e05a1c97801061154781a0a70723603e00c0d8392301d06606c1c938010611546c0741981a8724e00c0dc0f1e07e06d0621c928330350e46031c0809fc000980906018e04e03e0004c04e3700406c1c8e83f8018260e49c080ddc0609fc02c180727a0f60ce018392603f02606504a1c9701f8028248e49c024304a63e06e05a0fc07a0b6093603f03505d0491c9780682c8e4780ec134164724c0da0ba0f1f00f0010911b9283f81b81283b01f801824f41fc0dc0741d81ac166c07e06e04e00a092393703701e06d0591c9583f8078008e49c0dc08c07c0181a4726c07a05e00609e0f2f03701e06b0591c9681703582f83c981ac164723c0da0c2391f02f02301d07d066069a81b81780e83f03582cd40d81ac164724e04e03a0cc0d2392f02501d0660691c9681b80f03682c8e4bc09c0781b4184) else (if i<7 then 0x3460f09e2027700f0590c05414053804234278809dc008561504018c0d170007800380e13c2e01a0609e1b07d0300e84d305e069a818204d80f813416872504303ee0fc0da0b2821820f00502f07e06990af83c5c021e010f07f008804811b83c28c802401e11a146403803508909320078448498c0d405a83c60040960ce1464e05e0660f093230784384a8c04b8048dc28c9c0c0c81263037018e06e090a3280c7078b8002c1e160fe00019e0e093283770002fb0784a941381908602a09419c1c126301204e08d0a320258320540c860209202408c146404ba06218a090a32811606e05a1c9383c3c001e000f078583c3c1e1e000f00078178070102809c0b406140360fa030a81b02849021307e05d049a80c3407816150303ec0b0a8185404a8a80c381e0ec12a3053c0d8180952009603f0201904d9405a83301c20282703cc8241e04c0d41c0a42607f0202df00606a1c9b03f8030350e4803180e2e05e01099c0f22f2f000580f0378010e4980fc002c07e001021b01e07e06d059404815f034294981fc000a781b0725c0f0e07f00606c1c9303c2024095c1e154401200f00a0950aa28090078468551003c2302507c02029c08c1e140506702701d01201100fe00c050a84f008308500f01781b03583c278bc1fc022c05048818e04e0a0aa3707878003c09c02c1e128401200fc050a809528328498b81813d83c24c9c1e1e06e0141860f095281a809505f04855140d781826a82f0360e4d0301012a040500aa2703507d05f00c1c9683c2c1e15209e128404e81808d09f2027700f05c0c05416060209dc07c010301505067e0101801ae0f0aa301170220e60684a140768330142a09c0604d81b4188725e000f0007813034250615340c1283018017e04a0c6090aa35030780f8068302a8981ac16154308d04303b603e00c0de0f3827f078b8003c1fc02204f41817078783c209e830260f0f00078003c09c0380a1404e04a030a01801e0284a8541182c26a8250e48c1ec09c0287244180a81020f00602854100ef80280c2a0940610070270600aa2507e02f05b048541683f80f8020602a0b03009e1503e0406e04f60ce018393701837027f00b0641c981380e029c27c9c02057c08c1e0f6506701d01901201100fe000a84307f0084f0f01b03583c2789c1fc022079048012e00a090aa300bf0270083683d941238111482a88833c1e2e000f00017f01b0783d9404804003c2a0254bc01c1c1263048018c0cc0d0952f07f000983f80006783824cbc1fc002e0503302f09520097009298551380f8001b41ec806bc068a41544a0fc0601d03509a039a0bc0d47000403c063033034254a02602581b81813a5e000d020280550c0f809301806282f03683cec134161543a040b0785482783d9004803c1a02a881520e02079048012e04e0 else 0xe803a033c1e05a501d007e0f046270080ef07b059380407783d814803bc1ec083e0101de0f1f0780eb068c09407c06383c0d8bc0003fc1ec06407e8314181f07f000106029383e80c0800c49c1fc0204180a401fe0f603180ff07b058c08013c40930302a06a0302201d270004880e8c1250604093030207e231818183990c7008c1d007780460e803bc023e0f003022180ef07f0060390074124404dc00857c1e4042a04099e0105c2f00f00081a808f80485f83cbc0203fc1e301742be0f184582182782b1010826780410480d5c021344304e0008101e18110327078c0a407783c60440c9c1e304302203e182104481d0c1b983c19016c80c80b42064e0f06a1f0000ff078c1a819383c611603e208901e10338327078c1241e48606096088c1e3e0f6031707d018b03c340d4060863e00043120c6078b01f800581fc00202ce00c0f1e078780303c5c0203bc1ec084e0160601de0f202c013a0c0f8041ce0607c0341e2022078e0f06b270080ef078c1af83c13c234811a045c1e0f20f0506b09a4181835b07881e0104124604e45fc1e306be0fe0004f08d284650302f0f8078001a028880d740d80b4160f28306603079100c0248b83c2380c47c1fc000f23e0101de0f604203404b80e8c2060c808060e8868040306d013419e0f20538100a813804403fc1ec06308ee0f6040402040a190100c2a42701b415c80b2032429c1e4e0101de0f183680a20cf07901dc074414e0402067e00059e0f202384d10c0c0b183c40da0c7c1e3063e0f08e184400f0829c13c08060ec0ce0dbc1e4067e01063e0f202383c90c0c06383d80c611dc1f40a3041098c05182c700f010c1a303f80461108734060e5c045068c05e011845d038397011380b80780060cfc0181e3078c0f064c052034700e028c13c19780860d1c0181e30aa065e021823f01080138078000bb83c124dc000a6092150404e048043a0f09e280782182484f138201982786c1e08609213c4018e0f17000410f80406583c278ac1fc080920fa4004e01e0002ee0f049370382483d0f81d0601242789c1e1012048e04e0d0a52f00017f01b0783e978003c001062c0509f1f0250184f8d83c2a413c1c08429c1e2e00080901c70370584d9701c1680fc1880600e2832825005487013c3e04e004184552702700038e06a0c141250604024071c09c1214a5e00c0de040498528393024c0c0b8138001c7036060a0928302048015e0103808d09e3009f03700b0784f1781b80486094c9c0211a13c3e00e05e0c05342b280a703700b0784f1781b81380084b0248dcdc0211a13c3037e04e00e0c0a142b300c7078b8042031c022e01)))
def liveh11 (i : Nat) : Nat := (if i<1 then 0x80ae6075f8bc5c22e60ee000070a23d9ebc332562f8000000000000106270c520022a08a0000480f4000020f8000000000446c0136d05f30053c02a00000000000038027e205000021c880000000000000000145b320f20000081ac41b620df4104980080000e05900000000201b3c25b00002013f854620fbe02248c4c0000c2e5d02e881b9c1368660c070000024226e0240000201a40000000000002814800000000400098456062400000117d0b2000014040000000001421ea212105e50a35c5608206903c80003c4100000e099e0218013ee1237063133d00000031d0000489550210000000000000300fce0cdf13850cd40000211f106f0810f00e98310509260180000040ac0000000034277c08f111cc00df40ae030b0000404340010c12da026101fc015a4c520000180400000c0d55059580d2c12200009087402058199a0b0a137a0085803aa03c1115483fe023dc01b112700002419de2d14071703fa58c20000b0750094ec60b20c78067d81b682300000001d00002864400002065a344000000000000000003c192a0bb40747096484f6c33b618ca8b3c00012036a302e84a40000205ff08e0814c0000000020500000000000000b176d83400000000060074808b061540f6b04460932c1ce0000539450a9d85e18301605b880b381e16c052118a02e5424001160000000004205808e0000000000000000080608000241320000503c0000105ce42c7d13c800000000000020863812000014107504210194000000af0000000000000e0d2c177903c700e2a13451223001585bbe0f4205d582cc80d5c0e50000183694e400000a00f0000000000000804140159c0eca08700000840d4191e09d712d0041800624211f070a829dc0d962c3b004e80d781b80000513e68446c258a2dc00004007f860600000000708600001e0ef501c8000184200230414330140c24be2e3d1063017380f982710197901bf81076095000000058593da012809cb016044562030312bc00b94181410be0034811400d0a110d09b883e70255812e6017b818cc0018028305fe831718a640d6762f40b818119c00cb08d084d605e806b61003f888380ef40cae076584c3842860a91014b00ee402ec20ee02d800008168220f000078c78c05a0000000060b7c82448042c080384a2c4e7c0fdc020b09fd01f9627ed097d816ac14200ab916d3823585f400003049a02900000000000007093c0000e276000000000000100a3d03098243c0e60000304e000000001407d204b00002420200894340302d8030041c102060c1807c0809b080078112003092a1418d262829f0e016860a1000c266c8aa043020622801070a24ea350347008c780011800c65021c6a0041000a102420102384820a481940628e010a80802b8b400a0020001343c00a020c1a30e24002 else 0x70894807000000000f012d019a061ea2c500004819345b680d4e09d50144000042070000703dc81160000b05c08098c5a1801a008a50499c0ea0000113a409340001c0030095c813604006216e040104cb00e00000f04a0000300e4210aa07488cce024e2046618da808ec213e32100006835c00f60000d0734834c816b625ca02380003c17b40dd1027400f90271004a8082800000000c0d1908e8000000000000f144bb3c141e60000d03d603e90612a264d06180001451682f2d169a8b85c1c6e33ae024a8263050e80a2200cc0413c041c0d8f10a80000000042d600000000244cec055612f702a15a162256801fc0217c4a36131102f703d40135c0a6c07218062004f60aa902a6884e81dbe119d03130bdd412f83256049300350009000ff0611846fc611623fe052980e34055a338311be827a406620b18015809f685dc20321033a002c00010121518d1812f0015)
def livel11 : Packing := (573,4,8,9,4,15,0,lived11)
def lived12 (i : Nat) : Nat := (if i<1 then 0x79f02e04c0683d1ca0c81a7c0b81301c0d41814b079f03e06c0980f00e000727c0e01702603c028301c9e1be07c0980e02e0141903d181801604c07801068393837c0d81301e0041b03cf0df03604c0703f0020d81c8b1fac42afeebbfad8ab26ab7ea8da8ee9c8a55690ea3768a1a0e67c69e2a7389bc66b598b25a39572515928a4718ffa3808cba2d189fe23887c618984de0da824e0367f0df667c7dec27911dc675a5ceb7291c5d6fd5ba36d45ade6a31a0e671d98b64b98d161d18225ee975d5bd568d58ed5de560552f537548b51113fd4f0537a4c752aa498d211467914143910664050fc23decf293b88e9b3950e0d3694d4833acc833098bc92ddcb302ba4aa22940a0926dc97024208c1219081d1f8479a1d4c7011abc66818845cf162053613bc49211003e30e703550be02a6095020206c015e04040af0174000fffaa982503ffda360940fff68582503ffda84c940fff69532503ffda14c940fff69581503ffda360540fff68981503ffd5260540fff4c981503ffeaa54540fff68d51503ffda254540fff60951503ffd3254540fffaa931503ffda84c540fff69531503ffda24c540fff60931503ffd524c540fff6a121503ffda548540fff61521503ffda348540fff60d21503ffd5348540bffaa9825037fda960940ff78cd82502ffeaa4c940dff6a532502ffda84c940dff66132503fed824c940ffb60e225037fd8364540dff609915037fd3264540bffaa9815037fda960540dff655815037fd9360540ff78cd815037fd9260540eff60981503fee2260540bffaa9515037fda954540fef691515037fd9354540ff78cd515037fd9254540ffb88951503ff58154540fef60d41503fbd8250540fef54941503fbd3250540bffaa9315037fda94c540bff6a1315037fd984c540effa2131502ffda54c540dff65531503fbd544c540dff64931503fdd324c540ffb88931503ff5814c540bffaa9215037fda948540bff6a1215037fd9848540effa2121502ffda548540dff65521503fbd5448540bff68d215037fd9348540ff78cd21503ff53148540ffd61611503ff58384540ffd54e11503ff58284540ffd54a11503ff53284540ffe68930503ff9824c140ffe68530503ff9814c140ffe54530503ff9214c1409ffaa9935027feaa64940df78cd925027fda960940dfb66222503bee8888940ff38ce225027feaa64540cffa21915037de3364540dfb889915027fda9605409ff6a551502fbeaa50540def66141503bbe8850540bef69541503f9e3350540def64941503fae22505409ff6a531503fb5414c5409ff6a5215037f59884540efda22115037f59584540fdd95611503fb55484540dfd64e11503fd63384540dfd64a11503fe62284540bfeaa9305037f9924c140ffa88930503fb9414c140ff64c530503ff2114c140 else (if i<2 then 0x40b03204e0f3e07c0980f00e0f0a86c0f81301e01072150c12409607c090170082a81983d205f03e0411d031048393849c0f81202e0006282707a303e0440b03104e0f307602980306203c170341ca01c01209381207c0787282506455521702f81301a0c81a1481ca303605c098030782b3605c098070360041e1fc15a215812c0a0af0320f80e82d1cc094a6b0240de15a12c0d81203a0fc0083a04ac0c606c0900d02e0081b83d01380960505781107c07472832048a85e05c0903707a0c1506c0b81203a0c81383cc04801e060978143cc0d81783d380f0360581683e068933e03c0d81605c0d41e24ce12c1b812c0d80d07c0b41d03451ab0360303081606c0bc1e709c12c46812c0b80e0220f41903451af02e0340d03605e0f3605c1e826058a82e0481f81901e000ed0341ca00960480f06104c0f41915508bf01a0683103607a0b8aa842f03f026034190341c9c09006c0980e0284fc0103707a42d606c0180f05c0d0f80e5004803603c0823602e0081b83d209c0288ec0183203e0b4120e5381b0240540780206e0f38120078030640512b03707a01a827c0d80c4740d4160e5181907e0311d03505839382711b81301c0d4180e4f8130184f81b83d060a83e04c070150640dc1e6c0980202e0f4122a0d81702603c1e148b8170260343083c2918096030d18170240c81b83d01230281903181203a0f818824552b02e0440703206e0f30120078143cc0d81983ce0d70281903101b01a0f81a82c55281a81880d80d07c0d4162a9004834604c0613e0640dc1e806e0480ca12c0980d07a0e81b03054ac0c604c068160640dc1e7c0980f00a05c1f030541f0360540703505e0f3606c0901d02e0041383cf81b01a0581a82f079b02e0480e83104e0f3605c0681a06a0bc1e6c0980d02c0d41983cd81f02602c020e7048844180dd20e703e0480a83104c0f1288c0d80f0060bc0425106839422b86f81b0220381f80106c0e4839c0d80e07a0b41b03851a01be04c0703d0640e41a2a5181b02601c1b803048373e07c0980f00c0c0726c0980706e098180e4c01703e048190241c9b02e07c0883d1ca098187c0f8170240c41383cd81f0260340b8060660f3e06c0980f000180aa6c0b81b0240f80f0e7002098aa9c078030660b81a0e4d8170260381f0e606a0c8aa8c0183203e0b8120e4d81b01c0d8160e4b81b02603c000602a9b03604407802068393606c0901e0c60041303ce02303604c07802068393e06c0980f0040d0726c0980d0640d0a40e4d81301a0c81b0602940f3e03c0183305c0d072641f81b02603c018041c9f0260381b030290393605c0d81101a18c0083e06a303605c0901f00209c1e7c0b81b01a0f47282e06a534606c0b80e06a0bc1e6c0d80d0c20f81a82cd81909604c0683f0020e81a8c0d81301a05c010370 else 0x181f0240c81383c249902e01c0183c249702e0403b03106e0f3018c020c707849281f03181f01a04c0383c2a200c60106383c551707e05c020ad058a8360fc0980502e000562a0f83f02e04c03800158a838680ce09815e0540d00e06a0bc1ea0d008c0c017c0900d02a0c81b83d412c03804c1e1904a9b07a05150254983d06605150254a19c25822c0a81901c0d81783d219c2581802f80d0320581b02f07a803818c1e1ac54140c600c1f01705a09150703183e02e034162a0c0610360f11c2a0a1b02d02704406046e044070150640dc1ec0d819c1381811a0bf01a0480b0350660f660fc0b811018521506c1f81701a040642a0c1a0338190278160320381a82f07a902e0f11c2a081a00c81802981101a0581903707a83406704a0600ce0380c81606a0bc1eb03181f02049819027079c36605c0981e04c0c41e279006303e04))
def liveh12 (i : Nat) : Nat := (if i<1 then 0x5f181f90000000000153000005003f81fe716560552f18ed81c7f12a80038d06e9409dd1759855bf00a084c7000024206c12d1412ab00994077b0890000000002c0ef903ec0000f007e85ec51144000000001821e00003c1a400002c546b088340fed03180076716940000c0216000b000030549000000015902f80000f057800955135000004110800007027a45ebd14a640e70101d85ed10715c07ef1280815ca608001412151380219172d80bae0509016870842c4cd2070ec1b610630422ba648140fff35d50561a046a811de187c002fe00c800002084f812f2139d41521008ac0bfe05ce856e00001c510c18000000901ef8569005ec00000000245c1607a58158203a0c102601f58231811740189512448228305ff8428000000000d12e6cd5ad04ee81aa008bd81600000000000000342020000341b8d11780000505180000c178d02189047880fc914494157803100000306ec00000000000000065201ff00000000000000c0ca201708120901e580cb104218188204da801400002c44300894000000001019a6043b408e60059019c00001c1d400000000011731002a512c78408615a8c1e0106dc423ad05fb41bde010800000000000000000301010000300cc51684819dd169b416fc046cc0df913434112b30c004ce0116e812d0000000009069bc10a001fe0216000000000000038161000000469114b2812200002c0e4d05350030401600171012a30618f00180000210aa013ca11bc01f000396809b302ec4230404dec5250000345f24011c8055f08200000e02d042290000000007167c0000e018e4586b06a3021c801310169c06298153305d1042b714a9c520006188072d1118ccb90077e400000000c084000010484d0354000000002c18b304c7c11300000c09f0000200af108980000c04580000000000000000024480e083e049f20360000000001c40910833806b3034d01543073a80f78005c00005063ec205802c241ccb02b1c51801184c1dc000000000306b80000104d2c4ba2035f0435503834172807c400004105e8033e053b04adb049785f000003016a0000301bf000000000405e000001068a8073f0602062200002818560427c193000000184e03a5421d031620010201000301110201040835010e06010503000f277e0000050f08191000170110020a01000b000d300c0800000d000d00020906060400d603083c34080300050e0711110211020d030010113d2a003a04000f010301220603011515071f0000010001071d0103251102120008011c1b0c0d070c10000105151d0c170100071a03000a0c26050313010b0903180004004e0d0913030200000c17000203032f1307241e010b050030030600040c01040a32130509210c270000031c250d0d09120507001f01030442000007010c04127f3f3000 else (if i<2 then 0x6800c80076c1b030565016450339823ce11ffc455208ee019530529407800001c234e016dc51100002c1b4306be802c0000241a010685013a610df822d00000c0b2010d240927176c80e3a07540139010980000503700000000000000000034557618a8000000003c6025082f01a7e02a2012b41044000000001846a712db046600003005fc071900ed915ac44ab000018088512c800000078ac1ab00002011420065062b000024143b052dc1790000080691138f41e700002c15b4015941fd71484000000000c10f3067f803f104140000211f54009f10ca41ebc10554004812b1c4c900001462c2108b441cd06c40000000000000e031c0000d03cac1500000041658003400000000181e30000101d90000100bd0000080c2208e400002162040b550577819001183020031287c4ca000004111c00b9442d9116b812c402a545a7904368052208340148e12718103405980000a01ab4412f04cfc55aa011001ed0000100618029e80c0a0268c45fc04d505e8617d84637106b40000c013d80467167a00705168b40c15046640354084a84740000000006049b419e905c0c0c3d085400000008c00006129c0000000000000205240000a04fbc42500000000000002c17ab036b81fc00000c2334041200ad605b800000000000009089e42233047000004020201fba16ac0490801bcc4d1708ba058a0000000005048480a2135d00000811d6c0b7b05dd0629a0263c1d6f05ae842eb06a7412e00001c01c100480000d329340d0000014c32000000156000000000101e8406e107e30473000000000b00140000e11880000307cac238415fc0000000034232901014436802440000f0490004d0000385c46081c421400003c4f7602d800004014000008044201d83185ec03db04f541e60000140dd000000000c153c0000016b441f461615c132c07a00000b0728000040838c0ec0000301b2000010096e07680000200f340db8009c0000a060804479121a04dfe03c3813f000008107f050000006045481cf00002016c00001d8a47021c00000000141d10000181ac9175400000000141c9a38900000500940000a11d80000000000000e1564000000002819100000000000000860b903a9c0f640387449aa1014c4af1041a4221d072005f74124b8048b074f059900001860951421811f000008075f60ca00c5a00f84183e15200000c03e80000160bb401ef0197c1b55181c0000d123085514634584940000340e2030bdc0a64022dc123a13a9c00e206f3989c412b8c50ff183545d930605403be07b901f7b1804000000287c5ffe0252c03ad022904a3f178941de0000000003648b40d2007000000235cc0000801a00000d0812407c4086f84e10000240ee4068e0421c1399c0d4807cd84e0000038097b1741c4b0501b258ce8055705d2c15800000 else 0x3c44f017cd44a911275c222e019c04bbf152c40c8917368404e1363c064f04024031e18e742119053dc20a6087fc2194001c000000001c0515188ec16d0000144723042fc0895065a852d110b34041000000039000000000607b10526806ccc1efe08d9008da07d800009049c808f9014c00009078640b800002c071902c4c4a2a0206415f00001c0e60000341d2c02080000b00d0802901038000040568818e10233051ae08b3c63200002041b70337055ca146541fa310e90176f01d045d4b12e000002017a0493000000000c106185bc5033c01620000259ded03e344cf40708c01b0000000000000001d7613bb81ea2136600590000000009026400f3101240000b07d541475118dc5d760020c1b9f0547c49e508dfc0de603640000000000000000000000603d00010000000000000000000000000000b1391800a00000000000002c187402400000512580000910e6844a9157905c8d06f8c01ae000800001180f8499a169101283080440a320774404e202ad0197e00dc41300000100b3b015286204136bc0eb000028424a1590c4c5b182101cd01814c0fd816114621000038563216ffc604d021bc0bc8086ac17d1685dc454c10748163e079301cb015bf81170035885cf6016b806d50514c0c9f02ab414ce00b640578076c8433f03c7c0f9b1194410ca018bc0d1a06678138b080d04efb024d8410b0114c2099151d8018116a0c1a54126c4024007960043c0743841e803d4c46400002002ba1738c4b5b0270054d3348884a5f085e450a200da81c4000004175916400000904a4c56c507050167315f0c0a0b16d5004a80634c0a5f004fc19bf008080119020c0000000000118311b48543f05138192c000e82350000244c840175c5650000184b3902e445dcb02bb80666123800004012e452400003c22a7131b806030293c4b7a06610438e000))
def livel12 : Packing := (134,3,8,10,4,14,0,lived12)
def lived13 (i : Nat) : Nat := 0x81e058100c0260f302f03c090180b0081907a02b81a05810038000d83d10340b0181a05c1e681a0480c058000d83ce0cc0b024060601b079e07818128120303e018000e4c0f034090180b00c0107a00581e0480c0f80439031103c0b0240700819079c0581a0480c0f03439800554c0d024060c01b0001e2aa2068160480e000360f386f03c0d0240607c030001c9866f79c4b485faac9299fe3525787f8aa0be003ffb04a07ff4c940ffec0a81ffd51503ffa62a07ff48540bfec9a81fde33502ffb24a07fb88940bfec8a81fbd41503fec22a07fe4c140
def liveh13 (i : Nat) : Nat := 0x140d80001823ba25a000080b4a0f2000180340000000042142043a06da25e00ae0050c00ba00c625dc108c2b4a046a00546a4425000000000c0540001205f6041a0fe0000e06e0268001400000001824d2090a03a0001400200018074c072621da077c0446024002be01d8235e285429e6031c07e02a0229742e142b6c0094273c0bf4019c0e4000160b602e3c10400000000626060efe21b229cc04860dea0e780cb40a6a28e000020840210826f605242ae003360fc42c400ea00000000e0d3201ae298c0b8000140a800004277403de22360e8c04aa0da028dc0d000012065a09c000000c36087c05b40c0a0a4405c22be008ca212c07a0000e22fa0aaa02fc0bc00000000000160d62201e0ccc0c5e02de2ec60a000008100203e000000016039408ae0fa0001401f00620000e29a0000e0f4405822c1e0c820680001806660eccc13a106024200a3e0f8400fe252000000000000000082290027e0e12218809660e200010099c0604007828a0079ac22e10ac070c0c74263a04dc26da07c0001c238608322d460b180dd020200000000430600f0402002c20000a257e010827062460000c0baa204622c0001e2748012000140360022204fa01660f7a23fc0ac809b80880000c28700940000a1020000000000b2000000000001c2f0000000000001a08000008208208e00004612a06b6267e2d6e0d4a0286056e093a20642b3e09f4622c0ce0000a2c6000060180124af0600040080a0c01300040a31430297022c6851608000243c0820c0038e5c0008706440051005102
def livel13 : Packing := (14,2,8,8,4,11,0,lived13)
def lived14 (i : Nat) : Nat := 0x7030140803008001e8ffd40
def liveh14 (i : Nat) : Nat := 0x83800000100ae28207a04027236001a1200000000180800082b20de24000001410000c0160f61a001232630e22403619a150168a3400
def livel14 : Packing := (1,1,8,4,4,0,0,lived14)
def livecolumns : List ColumnInfo := [(128,0,895,0,13),(64,0,959,0,13),(528,0,495,0,13),(256,0,767,0,12),(32,0,991,0,12),(8,0,1015,0,12),(4,0,1019,0,12),(2,0,1021,0,12),(513,0,510,0,12),(320,0,703,0,11),(192,0,831,0,11),(160,0,863,0,11),(132,0,891,0,11),(66,0,957,0,11),(536,0,487,0,11),(529,0,494,0,11),(0,128,859,36,10),(0,64,701,258,10),(512,16,486,9,10),(288,0,735,0,9),(264,0,759,0,9),(256,64,701,2,9),(530,0,493,0,9),(12,0,1011,0,9),(520,16,486,1,9),(6,0,1017,0,9),(4,128,859,32,9),(515,0,508,0,9),(513,16,486,8,9),(0,256,663,104,8),(512,32,94,385,8),(512,8,227,276,8),(0,4,881,138,8),(512,2,440,69,8),(260,0,763,0,8),(258,0,701,0,8),(560,0,462,0,8),(40,0,983,0,8),(36,0,859,0,8),(10,0,1013,0,8),(521,0,486,0,8),(448,0,575,0,8),(328,0,695,0,8),(322,0,701,0,8),(792,0,231,0,8),(258,64,701,0,8),(194,0,829,0,8),(164,0,859,0,8),(657,0,366,0,8),(140,0,883,0,8),(134,0,889,0,8),(593,0,430,0,8),(70,0,953,0,8),(561,0,462,0,8),(36,128,859,0,8),(537,0,486,0,8),(531,0,492,0,8),(521,16,486,0,8),(768,32,94,129,7),(768,8,227,20,7),(640,16,358,9,7),(576,32,30,385,7),(32,256,663,72,7),(544,1,460,18,7),(528,8,227,260,7),(8,256,663,96,7),(516,2,440,65,7),(2,4,881,136,7),(513,32,94,384,7),(513,2,440,68,7),(324,0,699,0,7),(296,0,727,0,7),(785,0,238,0,7),(268,0,755,0,7),(224,0,543,0,7),(162,0,861,0,7),(74,0,949,0,7),(547,0,476,0,7),(533,0,490,0,7),(14,0,1009,0,7),(480,0,543,0,7),(856,0,167,0,7),(198,0,825,0,7),(689,0,334,0,7),(668,0,355,0,7),(595,0,428,0,7),(832,8,163,20,6),(800,16,198,9,6),(784,8,227,4,6),(776,16,230,1,6),(772,8,227,16,6),(769,32,94,128,6),(160,256,535,72,6),(672,1,332,18,6),(644,8,99,272,6),(584,16,422,1,6),(577,2,440,4,6),(560,256,135,72,6),(40,256,663,64,6),(552,16,454,1,6),(546,1,460,16,6),(532,8,227,256,6),(530,4,353,136,6),(529,32,78,384,6),(529,2,424,68,6),(12,64,689,258,6),(524,16,482,1,6),(522,16,484,1,6),(10,4,881,128,6),(518,16,480,9,6),(517,2,440,64,6),(960,32,30,1,5),(912,8,99,4,5),(396,0,627,0,5),(848,8,163,4,5),(330,0,693,0,5),(326,0,697,0,5),(817,0,206,0,5),(808,16,198,1,5),(793,0,230,0,5),(788,8,227,0,5),(785,32,78,128,5),(224,256,535,8,5),(200,4,817,2,5),(708,2,312,1,5),(194,4,817,8,5),(172,0,851,0,5),(168,256,535,64,5),(680,16,326,1,5),(166,0,857,0,5),(674,1,332,16,5),(665,0,358,0,5),(610,1,396,16,5),(601,0,422,0,5),(593,2,424,4,5),(581,2,440,0,5),(569,0,454,0,5),(563,0,460,0,5),(562,1,460,0,5),(541,0,482,0,5),(539,0,484,0,5),(533,2,424,64,5),(526,16,480,1,5),(523,16,484,0,5),(527,0,480,0,4),(484,0,539,0,4),(482,0,541,0,4),(961,32,30,0,4),(916,8,99,0,4),(913,32,78,0,4),(867,0,156,0,4),(857,0,166,0,4),(852,8,163,0,4),(851,0,172,0,4),(334,0,689,0,4),(841,16,166,0,4),(825,0,198,0,4),(809,16,198,0,4),(232,256,535,0,4),(202,4,817,0,4),(709,2,312,0,4),(697,0,326,0,4),(693,0,330,0,4),(690,1,332,0,4),(666,4,353,0,4),(653,16,354,0,4),(626,1,396,0,4),(599,0,424,0,4),(597,2,424,0,4),(543,0,480,0,4),(527,16,480,0,4)]
def livelevels : Nat → Packing
  | 8 => livel8
  | 9 => livel9
  | 10 => livel10
  | 11 => livel11
  | 12 => livel12
  | 13 => livel13
  | 14 => livel14
  | _ => emptyPacking
def liveindex : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 1 3 0 9 1 4 liveh9
  | 10 => lookupWord 17 97 6 14 6 4 liveh10
  | 11 => lookupWord 114 594 7 17 9 4 liveh11
  | 12 => lookupWord 214 1118 8 18 10 4 liveh12
  | 13 => lookupWord 51 266 7 16 8 4 liveh13
  | 14 => lookupWord 5 34 5 12 4 4 liveh14
  | _ => fun _ => none
def live : Forest := ⟨1023,14,fun j => livesamples[j]?.getD (0,0),livecolumns,liveautos,livelevels,liveindex⟩
set_option maxHeartbeats 0 in
theorem geomlive : graphValid live (boundsBefore knownx503) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive8_0 : block live 8 0 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alllive8 : block live 8 0 2=true := slive8_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive9_0 : block live 9 0 12=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive9_12 : block live 9 12 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive9_48 : block live 9 48 1=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alllive9 : block live 9 0 49=true := (@block_merge live 9 0 48 1 (@block_merge live 9 0 12 36 slive9_0 slive9_12) slive9_48)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive10_0 : block live 10 0 6=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive10_6 : block live 10 6 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive10_42 : block live 10 42 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive10_78 : block live 10 78 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive10_114 : block live 10 114 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive10_150 : block live 10 150 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive10_186 : block live 10 186 21=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive10_207 : block live 10 207 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive10_243 : block live 10 243 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive10_279 : block live 10 279 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive10_315 : block live 10 315 1=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alllive10 : block live 10 0 316=true := (@block_merge live 10 0 315 1 (@block_merge live 10 0 279 36 (@block_merge live 10 0 243 36 (@block_merge live 10 0 207 36 (@block_merge live 10 0 186 21 (@block_merge live 10 0 150 36 (@block_merge live 10 0 114 36 (@block_merge live 10 0 78 36 (@block_merge live 10 0 42 36 (@block_merge live 10 0 6 36 slive10_0 slive10_6) slive10_42) slive10_78) slive10_114) slive10_150) slive10_186) slive10_207) slive10_243) slive10_279) slive10_315)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_0 : block live 11 0 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_2 : block live 11 2 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_38 : block live 11 38 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_74 : block live 11 74 16=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_90 : block live 11 90 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_126 : block live 11 126 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_162 : block live 11 162 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_198 : block live 11 198 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_234 : block live 11 234 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_270 : block live 11 270 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_306 : block live 11 306 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_342 : block live 11 342 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_378 : block live 11 378 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_414 : block live 11 414 32=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_446 : block live 11 446 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_482 : block live 11 482 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_518 : block live 11 518 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_554 : block live 11 554 19=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alllive11 : block live 11 0 573=true := (@block_merge live 11 0 554 19 (@block_merge live 11 0 518 36 (@block_merge live 11 0 482 36 (@block_merge live 11 0 446 36 (@block_merge live 11 0 414 32 (@block_merge live 11 0 378 36 (@block_merge live 11 0 342 36 (@block_merge live 11 0 306 36 (@block_merge live 11 0 270 36 (@block_merge live 11 0 234 36 (@block_merge live 11 0 198 36 (@block_merge live 11 0 162 36 (@block_merge live 11 0 126 36 (@block_merge live 11 0 90 36 (@block_merge live 11 0 74 16 (@block_merge live 11 0 38 36 (@block_merge live 11 0 2 36 slive11_0 slive11_2) slive11_38) slive11_74) slive11_90) slive11_126) slive11_162) slive11_198) slive11_234) slive11_270) slive11_306) slive11_342) slive11_378) slive11_414) slive11_446) slive11_482) slive11_518) slive11_554)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive12_0 : block live 12 0 36=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive12_36 : block live 12 36 2=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive12_38 : block live 12 38 36=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive12_74 : block live 12 74 32=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive12_106 : block live 12 106 28=true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alllive12 : block live 12 0 134=true := (@block_merge live 12 0 106 28 (@block_merge live 12 0 74 32 (@block_merge live 12 0 38 36 (@block_merge live 12 0 36 2 slive12_0 slive12_36) slive12_38) slive12_74) slive12_106)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive13_0 : block live 13 0 8=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive13_8 : block live 13 8 6=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alllive13 : block live 13 0 14=true := (@block_merge live 13 0 8 6 slive13_0 slive13_8)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive14_0 : block live 14 0 1=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alllive14 : block live 14 0 1=true := slive14_0
theorem tableslive : checkedTables live 14 := by
  intro k hk
  interval_cases k
  · exact (rfl : block live 0 0 0 = true)
  · exact (rfl : block live 1 0 0 = true)
  · exact (rfl : block live 2 0 0 = true)
  · exact (rfl : block live 3 0 0 = true)
  · exact (rfl : block live 4 0 0 = true)
  · exact (rfl : block live 5 0 0 = true)
  · exact (rfl : block live 6 0 0 = true)
  · exact (rfl : block live 7 0 0 = true)
  · exact alllive8
  · exact alllive9
  · exact alllive10
  · exact alllive11
  · exact alllive12
  · exact alllive13
  · exact alllive14
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem caseA : Impossible (graphGoal 1023) 14 (vars 1023).toFinset := by
  have h := root_index (g:=dead) (before_sound known383 valid383) geomdead tablesdead (k:=14) (by decide)
    (i:=0) (ws:=vars 1023) (by decide +kernel)
  have e : targetOf dead=graphGoal 1023 := by decide +kernel
  exact e ▸ h
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem caseB : Impossible (graphGoal 1023) 14 (rootB 1023).toFinset :=
  index_root (g:=live) (i:=0) rfl (before_sound knownx503 validx503) geomlive tableslive (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem bound : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 4)) →
      PEqualNP.MetaComplexity.circuitFun 9 C = edge → 16 ≤ C.size := by
  intro C legal first h
  by_contra! small
  obtain ⟨k,t,S,hk,run,sub⟩ := initial_live C legal first h (by omega)
  have eg : graph=graphGoal 1023 := by decide +kernel
  have er : inputs++[seed]=rootB 1023 := by decide +kernel
  rw [eg] at run
  rw [er] at sub
  have ok : splitOK 1023 13438558465 = true := by decide +kernel
  rcases strong_split ok run sub with e | e
  · exact caseA k t hk (e ▸ run)
  · exact caseB k t hk (e ▸ run)
theorem Root.base : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 4)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size := by
  intro C legal first h
  exact PEqualNP.Outside.L_meta_4584.bound C legal first h

end PEqualNP.Outside.L_meta_4584
namespace PEqualNP.Outside.L_meta_4584
namespace R16
open PEqualNP.CircuitLowerBounds

abbrev Legal (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2
def legalB (g : Gate) : Bool :=
  (match g.op with
    | GateOp.and => true
    | GateOp.or => true
    | GateOp.not => true
    | _ => false) && decide (g.inputs.length ≤ 2)
lemma legal_all (G : List Gate) (h : G.all legalB = true) : ∀ g ∈ G, Legal g := by
  intro g hg
  have hb := List.all_eq_true.mp h g hg
  obtain ⟨o, l⟩ := g
  simp only [legalB, Bool.and_eq_true, decide_eq_true_eq] at hb
  refine ⟨?_, hb.2⟩
  cases o <;> simp_all
def gval (g : Gate) (l : List Bool) : Bool :=
  match g with
  | ⟨GateOp.and, []⟩ => true
  | ⟨GateOp.or, []⟩ => false
  | ⟨GateOp.and, [i]⟩ => l.getD i false
  | ⟨GateOp.or, [i]⟩ => l.getD i false
  | ⟨GateOp.not, [i]⟩ => !l.getD i false
  | ⟨GateOp.and, [i, j]⟩ => (l.getD i false && l.getD j false)
  | ⟨GateOp.or, [i, j]⟩ => (l.getD i false || l.getD j false)
  | ⟨o, is⟩ => o.eval (is.map fun i => l.getD i false)
lemma gval_eq (g : Gate) (l : List Bool) :
    gval g l = g.op.eval (g.inputs.map fun i => l.getD i false) := by
  unfold gval; split <;> simp [GateOp.eval]
def pwires (G : List Gate) (l : List Bool) : List Bool := G.foldl (fun w g => w ++ [gval g w]) l
lemma pwires_eq (G : List Gate) (l : List Bool) : pwires G l = (⟨G, 0⟩ : Circuit).wires l := by
  have e : (fun (w : List Bool) (g : Gate) => w ++ [gval g w]) =
      fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] := by
    funext w g; rw [gval_eq]
  simp only [pwires, Circuit.wires, e]
lemma wires_len (G : List Gate) : ∀ (l : List Bool),
    ((⟨G, 0⟩ : Circuit).wires l).length = l.length + G.length := by
  induction G with
  | nil => intro l; rfl
  | cons g G ih =>
    intro l
    have h := ih (l ++ [g.op.eval (g.inputs.map fun i => l.getD i false)])
    simp only [List.length_append, List.length_cons, List.length_nil] at h
    simp only [Circuit.wires, List.foldl_cons, List.length_cons] at h ⊢
    omega
lemma wires_getD_lt (G : List Gate) : ∀ (l : List Bool) (i : ℕ), i < l.length →
    ((⟨G, 0⟩ : Circuit).wires l).getD i false = l.getD i false := by
  induction G with
  | nil => intro l i _; rfl
  | cons g G ih =>
    intro l i hi
    have h := ih (l ++ [g.op.eval (g.inputs.map fun i => l.getD i false)]) i (by simp; omega)
    simp only [Circuit.wires, List.foldl_cons] at h ⊢
    rw [h]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
def PMV (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
lemma pmv_pairs (x : Fin 9 → Bool) :
    ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8),
      (8, 5)] : List (Fin 9 × Fin 9)).any (fun p => x p.1 && x p.2) = PMV x := by
  simp only [List.any_cons, List.any_nil, PMV, Bool.or_false, Bool.or_assoc]
lemma pmv_codes (x : Fin 9 → Bool) :
    ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any
      (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))) = PMV x := by
  simp only [List.any_cons, List.any_nil, PMV, Bool.or_false, Bool.or_assoc]
  rfl
theorem comp16 (w : (Fin 9 → Bool) → Bool)
    (root : ∀ C : Circuit, PEqualNP.MetaComplexity.FanInTwo C →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = w y) →
      PEqualNP.MetaComplexity.circuitFun 9 C = PMV → 16 ≤ C.size)
    (G : List Gate) (C : Circuit) (hG : ∀ g ∈ G, Legal g) (hlen : 0 < G.length)
    (hf : PEqualNP.MetaComplexity.FanInTwo C) (hs : C.size + G.length ≤ 15)
    (h9 : ∀ y : Fin 9 → Bool, (pwires G (List.ofFn y)).getD 9 false = w y)
    (he : ∀ x : Fin 9 → Bool, C.eval (pwires G (List.ofFn x)) = PMV x) : False := by
  let C' : Circuit := ⟨G ++ C.gates, C.output⟩
  have hC' : PEqualNP.MetaComplexity.FanInTwo C' := by
    intro g hg
    rcases List.mem_append.mp hg with h | h
    · exact hG g h
    · exact hf g h
  have hw : ∀ l : List Bool, C'.wires l = C.wires ((⟨G, 0⟩ : Circuit).wires l) := by
    intro l
    simp only [Circuit.wires, C', List.foldl_append]
  have h9' : ∀ y : Fin 9 → Bool, (C'.wires (List.ofFn y)).getD 9 false = w y := by
    intro y
    rw [hw]
    have hl : 9 < ((⟨G, 0⟩ : Circuit).wires (List.ofFn y)).length := by
      rw [wires_len]; simp; omega
    have h1 := wires_getD_lt C.gates ((⟨G, 0⟩ : Circuit).wires (List.ofFn y)) 9 hl
    have h2 : (⟨C.gates, 0⟩ : Circuit).wires ((⟨G, 0⟩ : Circuit).wires (List.ofFn y)) =
        C.wires ((⟨G, 0⟩ : Circuit).wires (List.ofFn y)) := rfl
    rw [← h2, h1, ← pwires_eq]
    exact h9 y
  have hfun : PEqualNP.MetaComplexity.circuitFun 9 C' = PMV := by
    funext x
    have h1 : C'.eval (List.ofFn x) = C.eval ((⟨G, 0⟩ : Circuit).wires (List.ofFn x)) := by
      simp only [Circuit.eval, hw]
      rfl
    change C'.eval (List.ofFn x) = PMV x
    rw [h1, ← pwires_eq]
    exact he x
  have h16 := root C' hC' h9' hfun
  have hsz : C'.size = G.length + C.gates.length := by
    simp only [Circuit.size, C', List.length_append]
  have hc : C.size = C.gates.length := rfl
  omega

lemma mono_fan {C : Circuit} (h : PEqualNP.MetaComplexity.Monotone2 C) :
    PEqualNP.MetaComplexity.FanInTwo C := fun g hg => by
  refine ⟨?_, (h g hg).2⟩
  have h1 := (h g hg).1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1 ⊢
  tauto

end R16
end PEqualNP.Outside.L_meta_4584

theorem PEqualNP.Outside.L_meta_4584 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (13 : ℕ) → (∀ (x4 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [x4 (0 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)), x4 (1 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ))]) = [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x5 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x4 x5.1 && x4 x5.2) → False := by
  intro x1 h1 h2 h3
  refine PEqualNP.Outside.L_meta_4584.R16.comp16 (fun y => y 0 || y 4) PEqualNP.Outside.L_meta_4584.Root.base [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩] x1 (PEqualNP.Outside.L_meta_4584.R16.legal_all _ rfl) (Nat.succ_pos _) h1 (show x1.size + 2 ≤ 15 by omega) (fun y => by first | rfl | exact Bool.and_comm _ _ | exact Bool.or_comm _ _) (fun x4 => ?_)
  exact (h3 x4).trans (by first | rfl | exact PEqualNP.Outside.L_meta_4584.R16.pmv_pairs _ | exact PEqualNP.Outside.L_meta_4584.R16.pmv_codes _)
