import Mathlib
import PEqualNP.Defs
-- The sampled first-OR lower bound is from dsgallups, PR 8665.
-- The clause interpretation below is adapted from arvindf232, PR 7578.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
namespace PEqualNP.Outside.L_meta_4807_aux.Seeded
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
def hashrestrictedl13 (i : Nat) : Nat := 0x3266d629c3000cc09800002c5a916a703a921aa561d5132e8d2800000381db0ef80ad078788712ce0036333c001b9c02082090848
def hashrestrictedl12 (i : Nat) : Nat := 0x62203295be14261132f30f3f1b40f70c8570ea66463a299d46c1ba2855693691546f740aeb454505f848713832723d0330abaef704500000000000000000002246c7f88ca8ddb1706419d9dfb457c0dd31f15082e0960004df3cf70400398003d17a2e309f11f451c7ee3c12b621bf3c50e3a1244b5ac092482789280c6564dc983c8302b1b20b118a5000015fc042239f2935ba13ff30f307a60f4e277ab838768f4897601ade5b3cc02721800000040b41f3cd8ce1d764963e1314d739b00162400126810b794f6be00053524d7cba0002ad8002c0325551ae8fc431233c90982be9e00000000034280009902110cb80007548254000000f1d800124d8a5e47463801066bfc798d0000b73042ca022e292214900000004943bd408c0000000005cc584c000c8b8002534e7c000622267486115380024940580007aa1947a4c4a8696fd33d25c0d7104063e0ecbc168c6eab8544eeabead2c83731524e6b306c0d0e1c4a7181079a312f870459c1949b742b43a40fe50dc8574d5a519b98ac54ed289cdc149c2f696baac46c504797113ed0d22df2d4cbc0010484160000231227702a9c9c08c67c09295f541c2a112421e513a8f00011e703768da14b1f5e046066c37470001c9cc81a1a4000000510127b5220000000000d36c76a3a000140e000bcd80000011496038b063a005800610001005489e36724000a60786185c2900f1439b5a08b00124c018022858000b4043180008626004825c0c3870a0401806148870c0c2800a1c3000204301042c184
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
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx23 : Lower (varsX 535) (graphGoal 535) 4 :=
  strong_low (m:=535) (cap:=3) (hints:=257) (by decide +kernel) (plainA (q:=23) (prior:=boundsBefore known511) (before_sound known511 valid511) (by decide +kernel))
    (cut_root (prior:=boundsBefore known511) (before_sound known511 valid511) (512,5,0,18,1) (by decide +kernel) (by decide +kernel))
def mapsx23 : List (Nat × List Nat) := [(535,[]),(541,[49,64]),(689,[114,33,97,82,49]),(793,[130,114,98,82,49,64]),(817,[130,114,33,97,82,49])]
def knownx23 := extendKnown known511 4 mapsx23
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx23 : Known knownx23 := extendKnown_ok (m:=535) valid511 lowx23 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx27 : Lower (varsX 539) (graphGoal 539) 4 :=
  strong_low (m:=539) (cap:=3) (hints:=16385) (by decide +kernel) (plainA (q:=27) (prior:=boundsBefore knownx23) (before_sound knownx23 validx23) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx23) (before_sound knownx23 validx23) (512,9,0,18,1) (by decide +kernel) (by decide +kernel))
def mapsx27 : List (Nat × List Nat) := [(539,[]),(569,[81,33])]
def knownx27 := extendKnown knownx23 4 mapsx27
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx27 : Known knownx27 := extendKnown_ok (m:=539) validx23 lowx27 (by decide +kernel)
def x31d6 (i : Nat) : Nat := 0x1103fd40
def x31l6 : Packing := (1,1,2,0,0,0,0,x31d6)
def x31h6 (i : Nat) : Nat := 0x30139ba050f42600000020
def x31d5 (i : Nat) : Nat := 0x844040dc8a0bf2aa81f930502faa4a05f54540
def x31l5 : Packing := (4,2,2,0,0,5,0,x31d5)
def x31samples : Array (Bits × Bits) := #[(0xfb547acecd4be963b7a737cb4ff66f4debefea7bd3e7d37cee3da7eb1fd4ef7ffa3bc393ef77ebf5333d97899d84cb7e721f3b67d9bf321f5df9e9e85f97b76d6477b24fdcdef6d8bbd8f465a54d7674b9f4f9fbccbe459eb9ae34421605f773,0x1225031072893190210d10ae050089453030c80142c21848a18e8b1801c04e3e040d085c00258c04207000320030a028154000410201401a02802321218e2c099813246a2703a82800008a40611140830c508220583ae02218120d2ac6012652),(0xdeaf5eff46e97bea49ad7ee4b37e1efaa62d368ae5de37c176efdbaadaabfdcef7ab6ff2768f7afdbd3ddefe99496dee85489efcf19e5b7cdfd4f8fb3dbc2cebd73c69b715d3fd85cf5cbbc96fbe1ed73efd651967c06fe2fadc130596e2497f,0x9c20462014002200210280100891092034010d03c19c594000024c40614900138804003c880006a56028a8072805811e212002401d688e188101402c000d124004c8000c8bc10c641d401040488900022a2611186000c850589b21518c44829),(0xeda3d43bc557f49fed7befaf577979968fee5190b7d6ee5d1bcbb567fca33e35c5bce021c3c8171ced2771b9facf33d7e6fdedbf86799bf7ef35d897207f9efe92db77a4eb7b72762fee6fbeeb77615fffb34ebdf5db37687f790b8da9238e9c,0x4200589100ab4580910d52c0e00269484c0c01020344200af830510a40690534072bb214001b561180087129016720241508c48308200106242c2054323220d24e1102031102820092031c2111034731c415820408318100901241c863238514),(0x3faadfc2ffbe267e2c5aa5befe9beb36b9bf4fce881aeb9b97c1cc97ba5d7c9a1d661fff97064caae9faebdf677b1c67abf6f38eefccc5aa74f2c787ef5e4bfa59fb7e503f6bbbfb69330697b0e0dbdad3eb07f7578bfc7f46a5ccb869d80ee0,0xa1a503203e543011200200011ab004312062e69840a3092003490e800b00124a000408800244088202210c0260180480c010120457d1da811002802341009404114e19600e09695d6500a14062e828cc00c84800700e600b07419c2384940ae0),(0xe65ca3fd7fe2bab5fba04679eed3cd2bf1d2eeffdef9c7f7ce5f6cf30ddf0bebca539e7ddf708f4efbedbbee4cb4e639d96f4557e927e7d1026bc707d2b3f9d47ddf9b5ddfe57bebd8f95aa771c9befd50ec9e4bfb7789bfc322e47641dff000,0xc4a48c88122c26096b06150600c6002848110248918c28108100043f43aa08100f28720f1805119080e430d06c508460a09a9a228200004cd4950040241013220004000d0b416029a1014319000042020050102858018c4c0ac62d4196ad100),(0,0),(0,0),(0,0),(0,0)]
def x31columns : List ColumnInfo := [(514,0,29,0,4),(8,0,535,0,4),(4,0,539,0,4)]
def x31autos : List (List Nat) := [[],[65,50],[16,66],[16,32,48,64],[32,67],[32,49,64,16],[48,33],[48,65,32,33],[64,16,33,50],[64,49]]
def x31levels : Nat → Packing
  | 6 => x31l6
  | 5 => x31l5
  | _ => emptyPacking
def x31index : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 2 9 3 10 2 4 x31h6
  | _ => fun _ => none
def x31 : Forest := ⟨543,6,fun j => x31samples[j]?.getD (0,0),x31columns,x31autos,x31levels,x31index⟩
set_option maxHeartbeats 0 in
theorem geomx31 : graphValid x31 (boundsBefore knownx27) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx31_6_0 : block x31 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx31_6 : block x31 6 0 1=true := sx31_6_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx31_5_0 : block x31 5 0 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx31_5 : block x31 5 0 4=true := sx31_5_0
theorem tablesx31 : checkedTables x31 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block x31 0 0 0 = true)
  · exact (rfl : block x31 1 0 0 = true)
  · exact (rfl : block x31 2 0 0 = true)
  · exact (rfl : block x31 3 0 0 = true)
  · exact (rfl : block x31 4 0 0 = true)
  · exact allx31_5
  · exact allx31_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx31 : Lower (varsX 543) (graphGoal 543) 7 :=
  strong_low (m:=543) (cap:=6) (hints:=8449) (by decide +kernel) (plainA (q:=31) (prior:=boundsBefore knownx27) (before_sound knownx27 validx27) (by decide +kernel))
    (index_root (g:=x31) (i:=0) rfl (before_sound knownx27 validx27) geomx31 tablesx31 (by decide +kernel))
def mapsx31 : List (Nat × List Nat) := [(543,[]),(825,[130,114,98,81])]
def knownx31 := extendKnown knownx27 7 mapsx31
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx31 : Known knownx31 := extendKnown_ok (m:=543) validx27 lowx31 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx55 : Lower (varsX 567) (graphGoal 567) 5 :=
  strong_low (m:=567) (cap:=4) (hints:=257) (by decide +kernel) (plainA (q:=55) (prior:=boundsBefore knownx31) (before_sound knownx31 validx31) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx31) (before_sound knownx31 validx31) (528,0,39,0,4) (by decide +kernel) (by decide +kernel))
def mapsx55 : List (Nat × List Nat) := [(567,[])]
def knownx55 := extendKnown knownx31 5 mapsx55
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx55 : Known knownx55 := extendKnown_ok (m:=567) validx31 lowx55 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx151 : Lower (varsX 663) (graphGoal 663) 5 :=
  strong_low (m:=663) (cap:=4) (hints:=536871169) (by decide +kernel) (plainA (q:=151) (prior:=boundsBefore knownx55) (before_sound knownx55 validx55) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx55) (before_sound knownx55 validx55) (128,0,535,0,4) (by decide +kernel) (by decide +kernel))
def mapsx151 : List (Nat × List Nat) := [(851,[135,98,82,50])]
def knownx151 := extendKnown knownx55 5 mapsx151
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx151 : Known knownx151 := extendKnown_ok (m:=663) validx55 lowx151 (by decide +kernel)
def x187d6 (i : Nat) : Nat := 0x105fd30
def x187l6 : Packing := (1,1,1,0,0,0,0,x187d6)
def x187h6 (i : Nat) : Nat := 0x78
def x187d5 (i : Nat) : Nat := 0x102f54c530
def x187l5 : Packing := (1,2,1,0,0,0,0,x187d5)
def x187samples : Array (Bits × Bits) := #[(0xbc96b74e51bdedae677fbdd5f9dfd6ffbf54daae71e9d9fb9fecceffb6eeb3df27bffc7ffb6efcbfb4fedacfad39dbd7fa6f9789f78e0ded7fe2fbc1f7fd627df9337cabb37992f2ba65bbdae7bde36fff77ade37fe638970ffc08427f0ff27f,0x80c00114011c31405000012d01109c008000000a02089000490201081240000209c00410204100012a0085000034004030045070500080000642304d0086821000a008100364000800040103141000840458480260000088421008422a01222a),(0x7aaff3fd2690cea0406ab7efd36a977a596d04f86c2beb8f77f31d4eccd2d654ebe49c1f7ed58339e82d8ab40cbdff836fccded3f1e21709f0e7bec8e4df765795cc90b5b9bad974c3b9741f02a6b54fa8fdd13bf90e3800007f318c4fca4c4f,0x5d1d80429e21028ea45bf4c080e2417d0ddde424b0d105e830e9ec86e03c0a01a22eb9a000048af60413325490c9f1860e3ba38425b106ebc8844db268601540b91bd28c6c00bcb6c4d2a8a44a439d6a2001a67c978f4777bdef318c45ca4c45),(0,0),(0x7b6e5fbcacfe53dd33a58fa46ee4aa056ca7777bf31c7ed629236353ab1a6dfe7f95ed5e729ff3f2161b3dfdf25b244981d64277d3e7e573fed08b3e54f2fbc6626cd3d734b05789f33d15adf7c3b50faffd701d8e87212070003e0f8cf38f8c,0xcd0789c42c491194042d342c94804054202082054cd2018c02a1aa08819c00990ae42a23da8503614a9615175d81d0ba6a59265d19804b24c61a4e2606df080165261c0020c14a60fd245728d1a090080c038b67c420fad6b43e0b0ca38b0c),(0xf329cfb3ff6b1f55cbb73e45ece73a8dfcafd544d7347eb92e67af938f516e3dbcb92158b7f5bbc3feb85552db5fef3c99ab7ca267ffdebec0b6dbbe980d8f3aeecfdf578ff24f9f7d0ef6f7747b9637df7efc9feec551207f83c00ff0fc0ff0,0x1f02f86002c20082297292c0d20220ad095c1211d80204a0120c085065006398260012c5c02038200495682060000c2e4090a48002242010583085b0d9112082980a81a1a88122840502402841260763610320348031c705294bc004d05c04d0),(0xc57dc4d14f6d3e3efdfa4c3fbff9c7e33698eb3b1eee2affd25c56adf2bdedc6f8cffab8869add655dc725af36fce7784e7a295f8df437c62f3dcedbeb7b1fa9acfdb7efefdfefc62fff6bb8b9cb599d21c6f372c3fcd6df8003fff000fff000,0x3403c2483820448009040680084140c808c4ae341014090302a80881cc23785d2231e2cb85380822400420940908b0204d000588020d0000389900301570386c00509042881353f16780c0e029c40800210514858d61b206b18ea52000fed000),(0,0),(0xcb4bc98dea5efc8dfbdbca3b728a43e9ca6dfd1b0e6a959defd954cdecd9b790ef7dcef08c82aca659257c3163ec1fb71e15efd46c50f7609b9d26380d4777ed44f49be8cf27ae5e2df7e0131b34e89875cf12b2bd9dee488003ffffff000000,0x96831104282910e00a0b00a93b22806d53a114bc16896381941a67803140582100811246880730d12b1d720d6c40094329d6a75d0d22632406474806a0ec710cfa92e3504acac0c90053b1a4023912cca62626252904df94e715adfff000000),(0,0)]
def x187columns : List ColumnInfo := [(10,0,689,0,4),(528,8,163,0,4)]
def x187autos : List (List Nat) := [[],[115,84]]
def x187levels : Nat → Packing
  | 6 => x187l6
  | 5 => x187l5
  | _ => emptyPacking
def x187index : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 3 1 6 1 1 x187h6
  | _ => fun _ => none
def x187 : Forest := ⟨699,6,fun j => x187samples[j]?.getD (0,0),x187columns,x187autos,x187levels,x187index⟩
set_option maxHeartbeats 0 in
theorem geomx187 : graphValid x187 (boundsBefore knownx151) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx187_6_0 : block x187 6 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx187_6 : block x187 6 0 1=true := sx187_6_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx187_5_0 : block x187 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx187_5 : block x187 5 0 1=true := sx187_5_0
theorem tablesx187 : checkedTables x187 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block x187 0 0 0 = true)
  · exact (rfl : block x187 1 0 0 = true)
  · exact (rfl : block x187 2 0 0 = true)
  · exact (rfl : block x187 3 0 0 = true)
  · exact (rfl : block x187 4 0 0 = true)
  · exact allx187_5
  · exact allx187_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx187 : Lower (varsX 699) (graphGoal 699) 7 :=
  strong_low (m:=699) (cap:=6) (hints:=1342193665) (by decide +kernel) (plainA (q:=187) (prior:=boundsBefore knownx151) (before_sound knownx151 validx151) (by decide +kernel))
    (index_root (g:=x187) (i:=0) rfl (before_sound knownx151 validx151) geomx187 tablesx187 (by decide +kernel))
def mapsx187 : List (Nat × List Nat) := [(699,[])]
def knownx187 := extendKnown knownx151 7 mapsx187
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx187 : Known knownx187 := extendKnown_ok (m:=699) validx151 lowx187 (by decide +kernel)
def x189d7 (i : Nat) : Nat := 0x3fd30
def x189l7 : Packing := (1,1,1,0,0,0,0,x189d7)
def x189h7 (i : Nat) : Nat := 0x4bdee00100502000008ec04000
def x189d6 (i : Nat) : Nat := 0x42420d50fe48130bf58530bf58930
def x189l6 : Packing := (3,2,1,0,0,4,0,x189d6)
def x189samples : Array (Bits × Bits) := #[(0xfac95919f9fa4c07fd2053e9efa7bc6637e3d83f767b7b179fff2b4b7e2ddd833e31ea1a383c966b87eceab27cd2b3a30836b45bffde1b26d7a7dee926cbbf6156f4a70bb8d27c1cfc06752faa2af36c27851c296edea20d00e01125d83bf4fc,0x150f00205886020840010412080a920058118002ab84ab1040224042028f1d4ac98263094d2aa43186645112c8c85dc08006424380154918851080c024014170802c8b6360838188030048010d50a008021110a00800681324e9112c1802a4ac),(0,0),(0xddfa33929f0527d1e1c3897b1c5b4d3e9bfbdf5dfde197e6b79f767ccdc3cc9c497f28ce3cdff359a9ded4cf7a67a6f84cf7f6568bfd95d576e9f7907b91d184b4b431fff4aaf1b3f0ec39936aa9bcfce3f2a6f1baf82522011fc20a3f24c8cf,0x62442cc059598052406e860adc10989054a000a0a2c30208074f7888142098022368541402189c2200020b300032800c8362c3c6663002140aa065a200200834912144e1a3468853215044021400427560c06b7420201950523c6091520c8ca),(0xd3d2e5d2df96c8fc0f7f9c7ab2767ce69e49cfc365e4363ae331b9f7fbabbdc5c16e7db59cc23f80d42313eedfff9e3ddcb8cffe8cd5fd192fb52b5ac52c76dbfff3cbb86269a3fb26edc2f991ffad759e1b6ee13b5729403e1f1c3021c70f0f,0x49032102f04a030802c805091218844448b1200581c10d5f6100004340110246c80802060108623cc4451d042c00530a2480c242011891448c10800494444e38a204a021e583041001004b90148011082121b94030547822384c1834608f0605),(0x3073bf4dd6335d2ef77de0d16e2ca78425e1a3fb1c1ae97869a9a9b03cf6334da3b27227ac6d9b2745765f7d1764b897d2525def7626deade8faa4aac4a6affddb6e97ca3a41ff7597d3ff73bd7ebd0abdfefad9955d8a406fa0a437c1f00ff0,0x80b0c8010511e062181648e425a440b9210a4fa0402a00a01e8025948c40a00130650460129111422980a20003138035506800945ae0062052607e180032b0025c12141c101802045439042a82254e530c4a4006c3a887ccc310e40381700950),(0x526e6b2537e8975f4847b72dabcb3275d98df0b482a5900719de03afd6d87722bcbdd77e5b3ccf967f99f08eb1f879986b585bd6c361f2af29573e776d5bafcf763f7a05d996d8cdef72967c6fe372934873e7ff457b509dd042bbc001fff000,0x404047510419512714b04a289410010226225b8004405420a4c4a518e1006205221c805610911802010b0ae130110004401004945a40304500084e3a0b00988a4550000c8d442e52140d0184408810a1d44e4400451191a40806ee8141fd5000),(0,0),(0xcd6c62356155b7182cf8e625313ac31dfe973e47deacf2ebad557fdd8bd63ef869b977476ffde1fd78d52e81c32e6adbbbef3d68ccf877e55b5bff3c9e135cce3359d9cdad9c12f01751edbde4db58db6363dd3fd6b27cb2d380fbfabe000000,0x989a1002f20206104a40048040028404c895a475111382ca1901004106811040d8c10a00864e6425dce0840c4704151316c0c1408080ce00a7018100d43d21302001e3300089102048a04a0b1826c31808001800184c6e4af2d81176aa000000),(0,0)]
def x189columns : List ColumnInfo := [(529,0,172,0,4),(536,0,165,0,4)]
def x189autos : List (List Nat) := [[],[115,84],[32,67,117],[32,83,116],[48,82],[48,82,112,66],[64,114,50,48,80],[64,114,83],[80,50,116],[80,50,66,32,114],[112,66,48,82],[112,66]]
def x189levels : Nat → Packing
  | 7 => x189l7
  | 6 => x189l6
  | _ => emptyPacking
def x189index : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 3 11 1 10 2 4 x189h7
  | _ => fun _ => none
def x189 : Forest := ⟨701,7,fun j => x189samples[j]?.getD (0,0),x189columns,x189autos,x189levels,x189index⟩
set_option maxHeartbeats 0 in
theorem geomx189 : graphValid x189 (boundsBefore knownx187) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx189_7_0 : block x189 7 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx189_7 : block x189 7 0 1=true := sx189_7_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx189_6_0 : block x189 6 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx189_6 : block x189 6 0 3=true := sx189_6_0
theorem tablesx189 : checkedTables x189 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block x189 0 0 0 = true)
  · exact (rfl : block x189 1 0 0 = true)
  · exact (rfl : block x189 2 0 0 = true)
  · exact (rfl : block x189 3 0 0 = true)
  · exact (rfl : block x189 4 0 0 = true)
  · exact (rfl : block x189 5 0 0 = true)
  · exact allx189_6
  · exact allx189_7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx189 : Lower (varsX 701) (graphGoal 701) 8 :=
  strong_low (m:=701) (cap:=7) (hints:=536879876) (by decide +kernel) (plainA (q:=189) (prior:=boundsBefore knownx187) (before_sound knownx187 validx187) (by decide +kernel))
    (index_root (g:=x189) (i:=0) rfl (before_sound knownx187 validx187) geomx189 tablesx189 (by decide +kernel))
def mapsx189 : List (Nat × List Nat) := [(701,[]),(859,[130,114,98,33,81])]
def knownx189 := extendKnown knownx187 8 mapsx189
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx189 : Known knownx189 := extendKnown_ok (m:=701) validx187 lowx189 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx215 : Lower (varsX 727) (graphGoal 727) 7 :=
  strong_low (m:=727) (cap:=6) (hints:=553648385) (by decide +kernel) (plainA (q:=215) (prior:=boundsBefore knownx189) (before_sound knownx189 validx189) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx189) (before_sound knownx189 validx189) (513,16,198,0,4) (by decide +kernel) (by decide +kernel))
def mapsx215 : List (Nat × List Nat) := [(727,[]),(861,[130,114,98,49,64]),(1009,[118,33,129,82,49])]
def knownx215 := extendKnown knownx189 7 mapsx215
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx215 : Known knownx215 := extendKnown_ok (m:=727) validx189 lowx215 (by decide +kernel)
def x243d6 (i : Nat) : Nat := 0x1fd20
def x243l6 : Packing := (1,1,1,0,0,0,0,x243d6)
def x243samples : Array (Bits × Bits) := #[(0xadfd67fcdcfc77b48f7cbead9df8f7de3ebf6fffcdebd2bd3ffeedbe575379dedef03d88ff61fbf478fd2bb1ab5f5f9d77fb723f3a67753ed3fcff37cbdeefd9feb7a54d4f7ecd3ebde7e5bfceaf7ff677bf574bf6fff8217ffc87009f2673ff,0x4508600414000801024890c0a882814240300c1104800058c02190092058422000c0a004050000a10800000a8e88220402802813801004087004022082000c21000040220411830088208024988800040001020c8006130042085008a04504a),(0xd3ffe8873f3ae8ffb8d772f76d7d381b3bd0bbc4f1d6fc737ef368899fb3bd6baffdfff7f11469cfee77df27d6f7aeec42b3cbd7f755afb19fe563aa9db3aba3371ad3a737af5df1b7de474df390cba9f906bb7d757d6496007c19f313d99e93,0x1a240dd0a080e6201082010c0240200c894422a4285908252840044056008400002040625012120071c690e1011384206003800438058102090bc08825408150e3c11001024a400233986403073414200532000273f8442d29410b311910a91),(0,0),(0,0),(0x7d3596d9eae447092d75ae7cd1ac76d66cc033fb707baa86052401548ed297bfdc8cd2237e6f1ed9dc0379bf38711c89730ff9af6d09d4500c3eb31f229b86eaeeb6367dbf3ab4eadf75b2a62ef3215b017b4e187b9788000f831e3c1ce1e31c,0x1a0c719598be800f265052d1a15384e88824830ae127fe22620166c3282a009cb79371073f03cc40e23f1e98521050093e523d4c4284f02f20f4aa844518f511c958b848140a4649b41920101253662a8c91051832db1ecffbdf1a3c14e1a314),(0x6faabfb3638154fce289efb8ab7e85e9ea2fd7c9afd665ffe148f6ebec9deeb57777b1da72bfaf3acffc4c4ae3cd657acef4e4f325ba94cf6367afdff6f77075794f4db8edf5b27e7570bf95714edebc9ec2539b8f9ed369f003e03fe0fe03e0,0xf00959020a3d2c0f824a3043000050490838072c0105048a2220000a600010890700814dba040004424100a1011010122800d5008314838000001015d4084a254e438a84c08e02833118c600a0065c28a42945440085884e318e402a40fa03a0),(0x1eac3cd2b7078eeff5ef9c7e6ce5eecf215df0bebca539e7c5c708f4edbcdbb664cb4e679596b4555e92fe6d1424b4704d2a3f91c7d8da95dd6e479ebd8f95a2751c9bead504c9e5bfbf78d97812052dab05a8ec250dec960003ffc000fffc00,0xe6049f00207111044ad18c6910c14005374bac00110a2c702d180713d088e43dd1ec5181d2a6da9ea08202014cc485184864c413a00006090d0f416029a9c562d14108420282525b9840018c4e0884b536acdccad0c05bbd2d6bef40006ef400),(0xc667b593681d6c6adb276d6796e7136ef087d2e783131573bc7df2d9abbf1f19a19686d8ee9e571ffb90047fe0e7dd1abc95f6ce01fdb9ef31d733e47cf8d53c525dcd97b9df725cde513e0a8566c9b357ec3992c9e9db488003ffffff000000,0x3a28041140252704c3488b81e3581b41381b051b05a69710d14d4b180a24372f049520004d19bb2353e1d087c862e0415150a404461641614e0c6c003d00190012c04790841cc304e8239045578a18013569283325877b1ce71bfd5bf000000),(0,0)]
def x243columns : List ColumnInfo := []
def x243autos : List (List Nat) := [[],[81,118]]
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
theorem sx243_6_0 : block x243 6 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx243_6 : block x243 6 0 1=true := sx243_6_0
theorem tablesx243 : checkedTables x243 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block x243 0 0 0 = true)
  · exact (rfl : block x243 1 0 0 = true)
  · exact (rfl : block x243 2 0 0 = true)
  · exact (rfl : block x243 3 0 0 = true)
  · exact (rfl : block x243 4 0 0 = true)
  · exact (rfl : block x243 5 0 0 = true)
  · exact allx243_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx243 : Lower (varsX 755) (graphGoal 755) 7 :=
  strong_low (m:=755) (cap:=6) (hints:=1358954497) (by decide +kernel) (plainA (q:=243) (prior:=boundsBefore knownx215) (before_sound knownx215 validx215) (by decide +kernel))
    (index_root (g:=x243) (i:=0) rfl (before_sound knownx215 validx215) geomx243 tablesx243 (by decide +kernel))
def mapsx243 : List (Nat × List Nat) := [(755,[])]
def knownx243 := extendKnown knownx215 7 mapsx243
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx243 : Known knownx243 := extendKnown_ok (m:=755) validx215 lowx243 (by decide +kernel)
def x191d10 (i : Nat) : Nat := 0x10200ffd40
def x191l10 : Packing := (1,1,5,0,0,0,0,x191d10)
def x191h10 (i : Nat) : Nat := 0x2c88468000c45430cacc40000001435458000000000414078c10425c96c1ec654b087fc2004c83a89ac6d07487183eca888f028c0cca704980009d45602f45e4a188300b0180038040000000024b4090002c52084460000000008000100c00014210800000120380000800210441200000000008043
def x191d9 (i : Nat) : Nat := 0x141c18408080386070000c0804e160c280001030280a06140000819c6810631306108080c01c40584080033011a0c62c08406420141c20c100804050308003282080c6382c110101820080b081000651e16108080c080408823820300610146842050308140000ce120000430198401181a00008150082031880b081000660a04580080cc0410418a0b0448406080204050708141020101c2050c0e000040521018858114217000921410030a0e1018018c2c084800819a0c00430a044420600c06006101029a1020b0601458505040c0080d1085c18004b0a0011c2061a001285021014006604140c2800cc2c0c20600a16081840c01a141003f37d97946f2db1a8b39e59c717eee9db9af95528bce898f24631425816f71d6b936acc656aac255ea393a24542c7f0e699e2ec4e4888f719e28038849034003fea8281ff4c940ffa40a07fd72503fe98281ff54940ffaeca07fd73503ff3ba81ff54d40ffaa8a07fd41503feb0a81ff5d540ffac6a07fd62503fe39281ff50940ffa42a07fe22503feb8a81ff59140ffc00a07fd10503fea8a81ff58140ffa62a07fc20503de20281ef91140dfccca05fd73503dea0a81fd84540bfaeca05fc72503f7112817f9dd40ff400a07de33503fc982817f5c540bfae4a07bd54502febaa81df95540
def x191l9 : Packing := (46,2,5,0,0,11,0,x191d9)
def x191h9 (i : Nat) : Nat := 0x285700001034a0ad83f00000000000186080000000a41b062205821bd204c04b10610000000146830f7400e8456a63d8adc9d02256c74205440008039079d062b1cbe289861284b502800000000000e10002d101f2023909c0000000210c000123db871100c510c435bc74b05ec060204047560b7818ee2bf4141840d0e27311833208c120e62fc436e0bc611dc2e908828cce02b01b30594876b170234701d80cb1176418e88a40fb716dc0fc0006012f1ea23250290867000000016738000000180e4c2e800071a841eac84009ed09bc22f06da0da2142602ec7a282c423020e0000000030dfa014b8048e0d1356275557582df2156273401882210ad233800000009108a22884f80002190c37f85af904a098c221458f0e40001217303480005032000000070a3cd532267c283893512f61a1432e83a600ce029c2ad057f14dc2fb404f105e1f9a38685020fd91b9c3b3066c1090173c40603f903c409123b641480f8000000000000000000121cc817101e318600cf41390080022612643a0000a042620fc54c834a1514361c7fe90d0000000087cc879622e0003f86981c0001a1bb00b0000a1e2a23785530a721a7a0dc46cd8ca708200020302898b98a2398c44f08750a3a0f643500006008e3010774072108f538400040ac00f80000000181f201ae06c81a800071f4c16ec7f3abfd09fdbfb88b1077721e034ac89308ff0b30206c3ed80f208a0003c8708312105424800070ef00000467855800000040002c598000a0f7444cc0eb90b018b02160806020208c8318000589b605feb5e852f0440000000182578e341e5819181b000055840000838000000000003088800010f1c2f6015000010ea000000000e732040000058286bf120837400000000001533c0000000100322500679053503003ac8196024f1e0a09a821d8d7f0bea246481800000000003c6ad0a400000002c21381790b5e094000000014010000501d06338000004000200200b0010800000400003000000000020002800810480160000080c00010000430000001800011401820400020000000000000000000000000000000000010090020000010c410000100110200c0402840430800400000000020020442450000002820820400410000000810000000001060000031000400800030800030000000800000000c00000010000012410810000000000400c00000400000000010000400010401800400020000000c1000040001042001000000005000000080000000040000002002083040000000
def x191d8 (i : Nat) : Nat := (if i<1 then 0xd6358940f7d5254d40dfd7258540ff9104c140bfe8858540dfe774c940ff53154540dfd754c940dfd714c940ff9524c140dfe7754140dfd205c540fbd4158140fbd4154140dfd724c540dfd7254540fdd634c140ff9604c140dfd7358140fbd541c940bfe8858d40fdd314c140bfd8608140ff93058540dfd7588940bfd8508140dfc7254540ff52158540dfd215d940bfd8244140dfd7254140dfd315d940bfd864c140bfe8858140dfd7354540dfd7158940dfe774c540bfe884c540bfd8154d40ff9204c140dfe7754540dfd7158140ff48148140dfd7248540dfc8748140ff93058940fdd534c140fbd5444140dfd7358540fbd4154d40dfd7188940dfa005d5409fc87589409fd8758940dbe7791140ded73889409fd861c9409fe885d540efa0099940bf88055140fb941801409fc8788940ebe66101409fc8754940f3d54541409fc87545409fe885c940fb61110140f9d548cd40cfe7799940bf88059140fae2291140ded201c940fb95480140ff13084540bbd8510140fb9544c1409fd8758540ddc835c9409fd835d9409fd8748540fb54158540cfd73999409fd8754d409fd839dd40df575845409fe885c540cfc7299940ddd728cd409fd825d540dbd7591140bf98380140fe622845409fd851c940ede668cd40d7d7295540fd93054d40dbd71911409fd874c540fce228cd409fc874c540df9724c140ff20084540fb61191140fb554845409fc874c940df67784540ef61199940f3e5591140dee225d940ddd768cd40dbc7291140f7a0095540df97280140ebe6691140df57384540df87280140fb9414c1409fd874c940df4815c940dee225d540d7d73955409fd811c940dde778cd409fd829dd40fb88055140bbe8850540d7e7795540f3d4195540bbe88551409fc8758d40dec7250940dec8788940bf88050940dfa7780140f9d418cd409fc8750940f3d5454940bbd8110140dec725c940bfa884c140dbe7710140fd93058d40fb54144140cfd71999409fd859dd409fe885cd40ddd758cd40ded7188940fb5414c540f3e5510140cfd635d940fea2280140d7c72955409fe885d940fda008cd40fba00911409fd819dd409fd815d540dbd7255140ef93099940fae2210140ddc728cd40ddd718cd409fc8754d409fc8748540f793095540df57284540dbd849dd40fe93088940ded7288940fad4188940f3d5454d409fd831c940cfd7299940dbe77505409fd8750940dbd7250540bf88050540eee2299940dbd72911409fc8758540df6115d940fad5488940fb88050540fd6118cd40f5e3395540bbd8454540d7d7195540ebd4199940fd9314c140f761195540dbd7210140dfa005d940dbe7755140dee7788940dbd7691140f6e2295540df97380140df47284540df97180140dfa774c1409fd869dd40bb58110140b3d8510140 else (if i<2 then 0x21810a10088042022608300204082142011020189040044600008400700020c4040b031c08404304461a062810c084321408040ca0000103082020421006200108503461c0628000010322080881021810820988243810308820228141101850404485028234201101888830184850282301081008501920808040c8002140808c381a00109008224001100000b821103240850804484020c30008601044021810a040880021810c08404202100830b01105808adbb6c8b55da5ad0366cb27d8eac3b608af9d77ab835bcacfd62aaeb560aa1d4baa3350ca77d34a96b4a0a45d1da8c343ca0fd00a7db3d09d9ce7a7033649a3ccea64b308975cb1a56328c93bc98a4ab240915c81a3e31dc8e7c6ea33b1888c1c5ba29313488bc3aa1ab0b8851c23a0f305c81bc06a00afe87e9bef9f42f847b7bd49e6af20785bbb9db2ec474fba29ceae60729b8d9c32e046f3b769b8adb06c9b5f9ad2d5c6a3b4c9a3ad00675b339962c9463fb1a98aac38611b0397e2bdc5e7af0975aba05c1add96c2b4c59bac8962aaf8569ab19572aa4547aa2950aa70521a8f94429fc4efa6e936a9a04c9a6393129844b7a5692aa93848da3f91c28c444fa2490fa86842da1190728243ff9fc8fca7e03e59f18f527943c39dc8eda7483959c98e4270c3739b68daa6d035d9a98d3269433b99c8cca65831d9878c125fc2f79728b7a5a82d19658b125742b39528a8a5382999498a224fc26f93689aa4c8261927890247422b910886a4281fd8fd87a23cc1df8ea874a3a01c18db86923341978c8862a30016d8b185622a414789c84ba24811988584121e40df86e836a1980b9857829214409f84e822a10807983581a20c4057828812a08003d81b80c205402380a802a000dfd7254940ff56150540fbd4188940dfe7754d40efd6358140fbd5488940dfd205d540dfd7354140dfe7754940dfc7255140dfe7758540bfd861c940bfd8058940dfc825d540dfd205cd40dfd7358940bfd814c140bfe8848140efd6158140dfd215d540dfd7158d40dfd8748540fbd4154940bfd8254540dfd7244140fbd4158940bfe8854940dfe7758940f7d5255140dfd7258140ff5214c540fbd4158d40dfd7154d40dfd7354940dfd7248140bfd851c940fbd4148140fbd544c540bfd8158140ff55144140dfe7758d40ff92058140ff93054140dfd205d940bfd8354140dfd7258d40bfe8854d40dfd315d540fbd5448540bfd804c940fdd314c940ff93054540dfd7644140dfe7748540fed2048540dfd7344140bfd854c940dfc7254140dfc725d540dfd7348540fbd2055140dfe7788940fed2054940bfd8358540bfe8848540dfe7758140dfd7154140dfe7748140ff92044140fbc8255140dfd7254d40dfd7154940dfd7544140ff9214c140fdd634c940bfe8854540f7d5254540ef else 0x42418000201008a1411086080620041120000815080c6820228003091820488100c4800620003041810a040461c0620301100818908000c6180620313120840a0024608000634102031a10108100c408062010012120c0001018043060884023040314001840e0909046128024202031a001808c000c046061060310040a08c0d040460a8500064030110321098190100c406182400c08209081041a0c06824031210201880c2820220400091c0a08801806242800309202018826000c60a0904820c5040314001820c000c406082810414001808c1908400c90006103020310340808c200040608209020018320818c1804406821c30381011820188100c41a820630c03102018819020404800082030412140082420c06183410a03181808902040470010940102018908040c6800020641101840d004081220e0010601c00c0c044822406303800c18040808c040c41a062040310681820c100c4080c2428101182018a002081820c102041904046061034010187081108408062410830a020c0408000c902101087040a000c40021008824200c1810a0060804184808001902c34286121008064020008a04200010004482022000a0018c0004207858006302000818080018e15040a0080210e06101830a04208062810a140880408000c9021010802044404281411c0030a042000c20048406021004180c6002000882420301090210020104481022810810a050460010c08405080c60414063c0031208404212100818481089820800))
def x191l8 : Packing := (282,3,5,0,0,13,0,x191d8)
def x191h8 (i : Nat) : Nat := 0xe1f934b35000f1400060af3271b92900081a000718b2a730000513f20000c37000001d39e2c019c31c07b00a1040e00050482f82551ce067160059ab01243630b52602bf24c11715a2e52d333108000803d0f12171ec0d000d38528c2241700000043aa2300080cc27f0923b00200000081d1a1060004608760d0a2c028e3
def x191d7 (i : Nat) : Nat := 0x420208840212000101190a002018044020204400018822010400000c20000c2004c0040014044010c140c8220901a03208c0060088021000808113042001840000000000000000000002101840610000206018c061000021aaa939ce5c916408a62487e087e9f57c1eb775d874dc5701a96918d5fd564d9314690c41d023acdd360ca314c02ecb62c4ac29ca22749824c8e224841fc7a1b05e1404b118260601303800fcaa0a6299281eb56150562503a7aa4b92a8a07ad5056158140fcc982a898a811fd92a2175503db2c6b0260a04df6568858140fcc98282a9a81fb1414c161503f628290220a047f2617588940cbe43aa4a9a811fd91a21725023fb2443aa2a047f646885d540cee43ac6992819f5616067750376a82c0ac0a065f21d5254540cdeaa10f11281db5615c9415023fb2443aa6a06ed5058358540fe898262a8a811fd91a2176503f3282982c6a047f6488758d409fac8d10902812fd96a2152503e72a8a9260a067d61c8148140cdeaa10e98a811f4985ca1150267d32c2880a04f664c80591409ecc9900aa2811bd94a2173502f332640282a04f664c80505408decc4ee20281b2d858884050327b0b3b880a068f6166610140d9ac0caa20281ba5818884050366b0b08880a05e664c80551408becad10bb2811dd93a217250336b02b9080a0477261728cd40cea41902b9281ab581998405023eb23442e4a07e4505314c140f8c982a8a9a813b6996044050336b033b880a064f6157210140
def x191l7 : Packing := (60,4,5,0,0,10,0,x191d7)
def x191samples : Array (Bits × Bits) := #[(0xe0df8ac10d69e5c6fcf0c034f56eff269b2c3e47b6f51fd71ace93fec69ed5ff0b3a7fadcfcb6af2af1df474235f35cbdf745d9dfeb7a62edf046a4ffbd5e195b59bae284fb27e2e26c2ead13965504079a0c0921f66acd018d205f66e01f267,0x4010001240409100100000680100402080404000200800a0120288000290540001a2001570140090046480240180100008004400802114826005c00808400409c205000110042081800041018495061c808111419020c8000d7400064002246),(0x5e9db9bb43baeb5845a44eabc9b35c674b38fdea63d8df635bd5d58fe434e1db69660c2629277c9c8e6999a7fc1d3a61e711bf945d2131db75af9ff017bae01f9195cf3e3cebe75ed0ae4bcca41225685072a6854a9006200142b1b6a8c6487b,0x11d021025b20f00014952568598d41f11599ca39cd405054ae84c06060009a2328a48c4228343034528080d8b501a05cba11008127a4003248f100f455412623421223930880140246803006a0122f0c3073a4c262703244eb20b5a798e54839),(0xfebcbb085bb0bba9febfb79bb38f2f9a53151bbd167e3b5f197e508b0cc854c829462da5e8fd55a51f917baaf14ffbdbb8b7a86dd4dafe5a4bddbf1bfa20cd07f0040fffb7792b6683dbd5897c392a90c877e4d84800627c11d900991068b88,0xa4271c2000010565a102521304408002026031002090a8a140180115108040904701201050400488a02036000a02122001021b300010420112048500880088080d0040004021c0b00134001815a190a1048c42399c8084330004421001028100),(0x543975eef7e504f95d45fce8b98de197e7cf9836debb4a5bf4d92de42cb8beedc311cbc3f8e8cc1d7caa9faa59bad8996f349230e78cca66fb10b4b69e9df539e0e09bd6186943647281740498ccaf4f4b4d8100c100580ac4a92a0c41f80ee0,0x18082481882481a184588688b081425101c88f80740420823a12400630e2145289000ca063b2024050048024049248a0084044111e015226440623e4204614202101b681dc0230c4401d1c0884c6f5acb61914421027a4c29c9850e60b00ee0),(0x9f99380e77fefaed9f75e976f72750d14d8fde40fda9236b0d1d1d6e7b66be03f5bb40b3b4701ddcae1a77cbfdee4593ac6fff0f1db96df8651b946e794d3bfff9e67af671cfc160b45ca68d0a3b290617084502d5fb90c91c202ac041fef000,0xd8703106c2789024c48a47914466c088c623420038303d318810107008d05000d541c41008441fd0a09027eda0068060962973ba2009609109020040042a12394042840320101453234c022f233200043402462bc6fd8013d6203af1114fd000),(0xa3df764f5e3995023fe65cdaddcfc36b7fd299a6d7a9450b52b22ad1094745b034f3f1cd5ed756eb708f3c93ca1a900e37fd2d7b3203f49acbdaba452b456297cc7f19763e151f7f972a8b6ac1367410a6d40031a41d6b3022806ccc8e010514,0x504630220003040038a1060101460a1120583b40003022b09e41910b160230026c814046a8968084a00124b804012428fe10a01095504001482f01724910988041810501088520a70334830a81a6241626954229a65cd3364800bedf8a020100),(0,0),(0xb9dfde360ccd466ea3fcd825aa373cb556dce8bb2fda3b6456a154f99df0e0cbed69ef05a17e7319d9a0b97bd4edaf64bdbc1f2d6f51d113356d2093bbdff56ea96ad07e0b4cbe9c93ac4b64a5805d89550bce82019418d369e400110000514,0x918805481e850080000a940f28971e8d584803b534b550600a26a408001856180540409000878734382410650788114008c004e0a090c5621107a0816aa0273901e88c290180f08700a44a54a584348d942bdc4402320c8b7bb012070210414),(0,0)]
def x191columns : List ColumnInfo := [(160,0,543,0,7),(536,0,167,0,7),(2,0,701,0,8),(521,16,166,0,4),(531,0,172,0,4),(4,0,699,0,7),(532,8,163,0,4),(538,0,165,0,4),(36,128,539,0,4),(513,32,30,128,5),(674,0,29,0,4),(513,0,190,0,7),(14,0,689,0,4),(537,0,166,0,4),(134,0,569,0,4),(136,0,567,0,5),(568,0,135,0,4),(641,32,30,0,4),(547,0,156,0,4),(680,0,23,0,4),(676,0,27,0,4)]
def x191autos : List (List Nat) := [[],[115,84],[32,67,117],[32,83,116]]
def x191levels : Nat → Packing
  | 10 => x191l10
  | 9 => x191l9
  | 8 => x191l8
  | 7 => x191l7
  | _ => emptyPacking
def x191index : Nat → Nat → Option (Nat × Nat)
  | 10 => lookupWord 46 59 5 12 6 2 x191h10
  | 9 => lookupWord 297 373 6 15 9 2 x191h9
  | 8 => lookupWord 20 77 5 12 6 2 x191h8
  | _ => fun _ => none
def x191 : Forest := ⟨703,10,fun j => x191samples[j]?.getD (0,0),x191columns,x191autos,x191levels,x191index⟩
set_option maxHeartbeats 0 in
theorem geomx191 : graphValid x191 (boundsBefore knownx243) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_10_0 : block x191 10 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx191_10 : block x191 10 0 1=true := sx191_10_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_9_0 : block x191 9 0 18=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_9_18 : block x191 9 18 28=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx191_9 : block x191 9 0 46=true := (@block_merge x191 9 0 18 28 sx191_9_0 sx191_9_18)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_0 : block x191 8 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_2 : block x191 8 2 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_38 : block x191 8 38 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_74 : block x191 8 74 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_110 : block x191 8 110 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_146 : block x191 8 146 8=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_154 : block x191 8 154 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_190 : block x191 8 190 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_226 : block x191 8 226 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_262 : block x191 8 262 20=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx191_8 : block x191 8 0 282=true := (@block_merge x191 8 0 262 20 (@block_merge x191 8 0 226 36 (@block_merge x191 8 0 190 36 (@block_merge x191 8 0 154 36 (@block_merge x191 8 0 146 8 (@block_merge x191 8 0 110 36 (@block_merge x191 8 0 74 36 (@block_merge x191 8 0 38 36 (@block_merge x191 8 0 2 36 sx191_8_0 sx191_8_2) sx191_8_38) sx191_8_74) sx191_8_110) sx191_8_146) sx191_8_154) sx191_8_190) sx191_8_226) sx191_8_262)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_7_0 : block x191 7 0 27=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_7_27 : block x191 7 27 33=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx191_7 : block x191 7 0 60=true := (@block_merge x191 7 0 27 33 sx191_7_0 sx191_7_27)
theorem tablesx191 : checkedTables x191 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block x191 0 0 0 = true)
  · exact (rfl : block x191 1 0 0 = true)
  · exact (rfl : block x191 2 0 0 = true)
  · exact (rfl : block x191 3 0 0 = true)
  · exact (rfl : block x191 4 0 0 = true)
  · exact (rfl : block x191 5 0 0 = true)
  · exact (rfl : block x191 6 0 0 = true)
  · exact allx191_7
  · exact allx191_8
  · exact allx191_9
  · exact allx191_10
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx191 : Lower (varsX 703) (graphGoal 703) 11 :=
  strong_low (m:=703) (cap:=10) (hints:=536879361) (by decide +kernel) (plainA (q:=191) (prior:=boundsBefore knownx243) (before_sound knownx243 validx243) (by decide +kernel))
    (index_root (g:=x191) (i:=0) rfl (before_sound knownx243 validx243) geomx191 tablesx191 (by decide +kernel))
def mapsx191 : List (Nat × List Nat) := [(703,[]),(891,[130,114,98,81])]
def knownx191 := extendKnown knownx243 11 mapsx191
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx191 : Known knownx191 := extendKnown_ok (m:=703) validx243 lowx191 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx223 : Lower (varsX 735) (graphGoal 735) 9 :=
  strong_low (m:=735) (cap:=8) (hints:=553656577) (by decide +kernel) (plainA (q:=223) (prior:=boundsBefore knownx191) (before_sound knownx191 validx191) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx191) (before_sound knownx191 validx191) (192,0,543,0,7) (by decide +kernel) (by decide +kernel))
def mapsx223 : List (Nat × List Nat) := [(1017,[118,130,81])]
def knownx223 := extendKnown knownx191 9 mapsx223
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx223 : Known knownx223 := extendKnown_ok (m:=735) validx191 lowx223 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx247 : Lower (varsX 759) (graphGoal 759) 9 :=
  strong_low (m:=759) (cap:=8) (hints:=553648385) (by decide +kernel) (plainA (q:=247) (prior:=boundsBefore knownx223) (before_sound knownx223 validx223) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx223) (before_sound knownx223 validx223) (592,0,167,0,7) (by decide +kernel) (by decide +kernel))
def mapsx247 : List (Nat × List Nat) := [(1011,[118,130,50,81])]
def knownx247 := extendKnown knownx223 9 mapsx247
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx247 : Known knownx247 := extendKnown_ok (m:=759) validx223 lowx247 (by decide +kernel)
def x351d10 (i : Nat) : Nat := 0x4100ffd40
def x351l10 : Packing := (1,1,4,0,0,0,0,x351d10)
def x351h10 (i : Nat) : Nat := 0x4311c0044c000034c72b1165785f6a19e0000f2c00c240047400000000031616246e4b810000040888b13970038dba40300061
def x351d9 (i : Nat) : Nat := 0x80c206028214038061081840c031850c206028a206103018308180824020e21a100a20e10d08060601083c400c09840e202118c1402c5dd2c73a8bbb9a2c04e9d0c63a08803feb0a81ff4c540ff862a07fe11503fea8a81ff54940ffa42a07f611503fc982817f5c940efcaaa05fd75502feb9a81fb88940
def x351l9 : Packing := (14,2,4,0,0,9,0,x351d9)
def x351h9 (i : Nat) : Nat := 0x20754f427648b0060000000001816000000000021cc09baf1895041110111f84724831e2aaad44aaf61748dad3000000b800206e0000005a44000000d235888000000a260a9d032000c04e135594043843582b90004fd63207f007e2f519badf40040c70d380819e485612389c40241430e9908d18031c1ea8840000000000002d15a3482248a4c74a10164d06fc652b0a66b0afc6140e55c80d597a000000783584a493648393a411a2ad022856c30611f1d903f05869400060fd54ca38c25a0991842c30000003d34000505b2fbd51250e02e848893688e169a1d0732c50000001c7c4970007aca14aa8b0000002933e40f147079d40000b56214402011a0180c619007108070000408084220000002152444010400140208821214624080490002
def x351d8 (i : Nat) : Nat := 0xc20200871c1860438b00430010b0c2421430e0801830c1400050432018600214184803091043001030c282140004003090001064020a1c2420c50c0043008830430a1030c21a1840828000900430b1410c1461800a1200030c0041810b1860020f090002090c20010e21f0400720100010e0c2001400040030801c3083c10c3020860d0001200c20010e0030d0001000800800840e30810010010618428388207100080181c61800c1840e20010030c2001042830c004006db5b1b4b62ebc56cab351a96512a0d3ce6ccc69672824a4818dd18a27c3c853059f73db790ef1d4b96706dddb235868acad8c2fe5d6b455f29d514a15392514988e51321a40e7d0f79dc3846a0ca9822ec570a493d2624b0891061f43b86d8c816a2a4478750c41582883e06406006000bfd820c540dfd8748540fbd4148540dfd315c940f7d5354940fec824c540bfe8848540dfd7648540dfd615c940ff93058540f7d5254540dfd7148540fbd4158540bfd824c540dfd7154940fbd4154940dfd874c540bfe884c540dfd7354540dfd7158540dfd7154540bfd850c540ff93054540ff93054940dfd754c540bfe8858540ff53158540fed2154940dfd7354940dfd7348540dfd7548540ff5214c540ff93048540fbd4154540bfd8354940dfd7358540bfd8254540dfd714c540bfe8854540bfd8354540bfe8854940ff9304c540dfd7254540fe611889409fd815c9409fc835d540fd63384540fe930889409fe885c940d7d7195540f793095540bf9800c540f6e5588940df9305d5409fe885d5409fd8758540f3d4195540fd9304c540ded7588940fb9414c140ff13084540df57184540d7d7295540f7611955409fd855c940fb54184540df57384540df575845409fe885cd409fd8754540dbd415c940df576845409fc835c940cfd7658540dbd415d540ded7188940f5e33955409fd870c540bfa884c1409fd874c540d7d7395540df57284540
def x351l8 : Packing := (82,3,4,0,0,11,0,x351d8)
def x351h8 (i : Nat) : Nat := 0x850010040d62d0463d08a4c0205a1a002100049d0eb980000067c061a0804
def x351d7 (i : Nat) : Nat := 0x820003041820c10006103041c208b86817c777265605b4e41341f1205008fec8906baa811fc985d531503f926041262a047f64a885d540cf64130e98a81fd1314c1215023fb2241ae4a04df65688585409f6c951098a81fd1304c5615023f130982eaa07e44c5414c1409dc4c282982811f99020d725022fb2a41ae4a046f652885cd40
def x351l7 : Packing := (16,4,4,0,0,8,0,x351d7)
def x351h7 (i : Nat) : Nat := 0x100000
def x351d6 (i : Nat) : Nat := 0x3f80a24c5414c140
def x351l6 : Packing := (1,5,4,0,0,0,0,x351d6)
def x351samples : Array (Bits × Bits) := #[(0xe9e5f434b7d467d6c9e4fb64d7b6792da1da7c7cffc0119c079df9d9ae4fea5f2f4f8ffcb10755cf85f9668c9fe6cb785ae3f9d0b298735cbbeb4964ad31e6e558e10d49506bb885fcbb6fcd492508c07502016135a5e200a800e6a2821fe73,0x254020e91650844607048f41200450c7c4410828648808c88e182a644c628f3a064844101021d02881c2180083a02034d22208120010338540390c11146b09ea114212200480644460d88083495095342740261273c24e045283a449a8212c72),(0x79239f5b53977db38ef2f767ffe51f7f9c4457b2fec8fffeb176b64dc9fc5533f1f94030239659367efef30ef864a9d7e7d17d55987639c65fdb93ce10ea79c3e30d734d7197b7dfea6a72f998af068b89a444de0b00b00242138a9a7ec6405f,0x120410818c01208002402804080020090090c08004870010400110001010410180802c0e040100082c002a24490808050841cd40260020ae00128020848004001064001200808200010800040f2a8a102c002c0808b0628408021044c44009),(0xff71092399a6b902ef4d531ff2da63b64fb10b59cabc6b557b32cd074313e9afe7082ea32c5e0e1257ed6934a0dadf769254a95a6530486595c081f6f45ebed1a90978c7ba1ed2eea393c51d383151454c609bd80430c04d1613841431078d9c,0xe74141c43022004b0cad134761c420cc00ee240349f3302226837049120940a2384a6a8040394e565211ab05098482f30811200094894e064064803c180b30118ece03b9480065085ab2150d80405155ee51fdd062b0000d7315dd0f31038f14),(0xd3e5af53a6568eb6e1aa786e3f75e248af7b189dd533deebea6eedeb56cf7e770a3ececff7cb262ff7f24e8bc251df6c9b6dfda7665c47bd866fd0bb842ec35903d17aaacae554622a9a6bef3bd8292274c10b01d5c3d05f94ec6105c1f805c0,0x89008000494f130b342a4000c014103741101100408008088088c20ac0412450035012201028128018000c03028050042809116001411412501300100508ac810116c04b628901000096002091a8e20118802009543d02004422010c0b000e0),(0x9c0893173e7d465e10cdae38aedf85b3607bf3ed55d74aac0de9bf18949a8f877f2ff3190823436dfe1f0c69d7c9b3391fab7ba967bb2df228fafc05dff135e677ff28c946b7cbfed3219cdf6465582b42123081d83c0831080c15e181fff220,0x40228512690a028100a80036519aac30018684829373c13701e7401803882000b0808a40605422455c08c43e481518082849464180230c228a44416ae2847405ec2000cb41000983172401540085408bc81358a9083c2059a91c5ba2014ed200),(0,0),(0xdb9045fea89de6a2906fc9f741d97be1b6d7f025aa2124ade6d7b817bd6d6a7b7f3bdd96eaa0c5858c19eb567fce27347b7ffb6b9dbff7e3ff270b0a6599516459a0ad73af2cde9b16beed134914c755c48ed421bd272780610014e47e000800,0xa98c0b800462a0522b409d025104910324f50018000318540c9aaa2086c14624001b011221186271b4811b510a1011230082a832b55064441001e8509a214c0ae88c0b01849a20000064208fa810c501c582ba01b78305007212e5e7ba000a20),(0,0),(0x63b7eba7fb381970b5a7bdbef8d4d0be9bcc3e5ca9889e7a5df5a3f47373dcf95d5053f6da3ffaf7ad42feba971bfe82febf2bb194dafa3929bfffbcb161d57beff68f3a00ee58b4de4d8f79bf29b0de306f91f628f70f93a9e0700000000800,0x241e456db010a0040a8422080e80a74830048c373106622120050c0511880127440b6c992640c840868a0208040e0d42d5d06084001080200d8048644861110044290ba48454dc92d008130548130de2a7545fe483c2adf89ad1a0800000000)]
def x351columns : List ColumnInfo := [(529,0,334,0,7),(320,0,543,0,7),(4,0,859,0,8),(537,0,326,0,4),(2,0,861,0,7),(258,64,541,0,4),(530,1,332,0,4),(521,16,326,0,4),(512,256,23,72,6),(834,0,29,0,4),(836,0,27,0,4),(785,0,78,0,4),(72,256,535,0,4),(518,0,345,0,5),(533,0,330,0,4),(12,0,851,0,5)]
def x351autos : List (List Nat) := [[],[64,49,134],[96,132],[128,49,100]]
def x351levels : Nat → Packing
  | 10 => x351l10
  | 9 => x351l9
  | 8 => x351l8
  | 7 => x351l7
  | 6 => x351l6
  | _ => emptyPacking
def x351index : Nat → Nat → Option (Nat × Nat)
  | 10 => lookupWord 8 37 5 10 4 2 x351h10
  | 9 => lookupWord 62 157 5 13 7 2 x351h9
  | 8 => lookupWord 5 23 5 10 4 2 x351h8
  | 7 => lookupWord 1 3 1 7 1 2 x351h7
  | _ => fun _ => none
def x351 : Forest := ⟨863,10,fun j => x351samples[j]?.getD (0,0),x351columns,x351autos,x351levels,x351index⟩
set_option maxHeartbeats 0 in
theorem geomx351 : graphValid x351 (boundsBefore knownx247) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=2) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx351_10_0 : block x351 10 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx351_10 : block x351 10 0 1=true := sx351_10_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx351_9_0 : block x351 9 0 7=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx351_9_7 : block x351 9 7 7=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx351_9 : block x351 9 0 14=true := (@block_merge x351 9 0 7 7 sx351_9_0 sx351_9_7)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx351_8_0 : block x351 8 0 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx351_8_36 : block x351 8 36 3=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx351_8_39 : block x351 8 39 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx351_8_75 : block x351 8 75 7=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx351_8 : block x351 8 0 82=true := (@block_merge x351 8 0 75 7 (@block_merge x351 8 0 39 36 (@block_merge x351 8 0 36 3 sx351_8_0 sx351_8_36) sx351_8_39) sx351_8_75)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx351_7_0 : block x351 7 0 6=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx351_7_6 : block x351 7 6 10=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx351_7 : block x351 7 0 16=true := (@block_merge x351 7 0 6 10 sx351_7_0 sx351_7_6)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx351_6_0 : block x351 6 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx351_6 : block x351 6 0 1=true := sx351_6_0
theorem tablesx351 : checkedTables x351 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block x351 0 0 0 = true)
  · exact (rfl : block x351 1 0 0 = true)
  · exact (rfl : block x351 2 0 0 = true)
  · exact (rfl : block x351 3 0 0 = true)
  · exact (rfl : block x351 4 0 0 = true)
  · exact (rfl : block x351 5 0 0 = true)
  · exact allx351_6
  · exact allx351_7
  · exact allx351_8
  · exact allx351_9
  · exact allx351_10
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx351 : Lower (varsX 863) (graphGoal 863) 11 :=
  strong_low (m:=863) (cap:=10) (hints:=12901687553) (by decide +kernel) (plainA (q:=351) (prior:=boundsBefore knownx247) (before_sound knownx247 validx247) (by decide +kernel))
    (index_root (g:=x351) (i:=0) rfl (before_sound knownx247 validx247) geomx351 tablesx351 (by decide +kernel))
def mapsx351 : List (Nat × List Nat) := [(863,[]),(957,[118,130,81])]
def knownx351 := extendKnown knownx247 11 mapsx351
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx351 : Known knownx351 := extendKnown_ok (m:=863) validx247 lowx351 (by decide +kernel)
def x511d14 (i : Nat) : Nat := 0xa08060402006ffd40
def x511l14 : Packing := (1,1,7,0,0,0,0,x511d14)
def x511h14 (i : Nat) : Nat := 0x432908000000160c00070900000000000000000c130006048447e2c804e88b003007705609bc55600d02f847440e0381400c2c16c2e8034835c09c0f81080000000000000003c1162b000600800100e000000000022d20b4c4000e5090000
def x511d13 (i : Nat) : Nat := 0x82808080300a3200705c0e02058200a00781c060a0202400c0782c0c090200c00f0282c100601801a090381014030034120a09018040500382209038280803003c0e0a070200803003c0c0f020281003003c0e030202c1200682c12070200c00d03808180b0282000f0581c06080280180d03808160504001e0b038101003003412060681004000a3c100805818020401030292058180204010301014802c0e0800808180479d129234c257d4ebdb5b275c6a7d322293ca6a8b312b1ce24422000ffebb281ffd32503ffb04a07ff60540ffea8a81ffd31503ffae2a07ff48540ffeb1281ffd63503fbc66a07fd84540bfec9a81fee22503ff260a07bf99940fdea0a817fd91502ffb2ca05ff64940
def x511l13 : Packing := (20,2,7,0,0,11,0,x511d13)
def x511h13 (i : Nat) : Nat := 0x78c7781158d0205080002805e0ad8000484c5027e09f800010060000685ba856800000001b3d8000600d000040477021705d404f403828a0000000b3204ec0c368d450bd8854000000000000000020cef0932801800008c0a81080007809e05b380c18020021a8aa901248dd0098a8c66851009c10d38000000000c28000482f0000e313000000004881b0d10000703e582a90138000088540259b10d3347804081f000020a6f031a8dae0151824e00a00000000682d601ea016d80100000000786040d9585e5017d8a268261807503d0000700ce88d50be78b5c84b68243093d0b758d6c85368b2181fb055c014384a880ae84ff09b1822183b40196017589680ae100e8835489280005882800040038000301e00005888103f501180000000305fa859800070985860f8527046f89e28878815c854d80b0028984d188268370809600fa88dd826b85640895046204a7007d02be8ad1003288b8000309f7836e0c3d0cd785dc032989a40128000509d0000000030bfc04318029099d8865057408c7890f02968c8001638589851b00f005aa841a05ca84138479832483cc88718c5000040a90000400880000000401cc029a8340000581c00af4018800008a2e843e82b10256057805a78abb85ec049c00000000000600e682e9823684ba8a9b8a7389ec0271835c839d05c502d8000483a101d40cbc8406097f83390bed80480006855189048945823f0408010501da83ee0d56390803ae0b000003018581ad028105f308a8037f048e0b10000303fc00d98b380007b93383c104280007014a8c4b09488c0202ff850384e68ba483be8c68000481308d5b04c8000000000a6000023bdd0dc403120bd000058b5000000000034c00500000000184500000820a8a198585044b83968481833000000006036281b7849202c202a3030f81b909be845c04250cc88594886a81a102010888038c0228019800028cb000018b0c006800000000000000000004044000068c8c0b6d00878b60000000060a4c82ca8616853b80bb0a7f8aeb83d8000000008b1f052b82e184df0bb6830116440010303004b00000800a214143818e95020860002140020a1418e00640240000009041c00104002010600e8000b000102183202800105000028600040051e20003002c10206101090c08104020011808081060800080
def x511d12 (i : Nat) : Nat := (if i<2 then (if i<1 then 0x3ffda360940fffaa982503ffda354540fff60951503ffda24c540fff61521503ffda84c940fff54981503ffd5358940fff68532503ffda160940fff68d21503ffeaa54540fff4c582503ffda760540fff68981503ffd5360540fff69932503ffda360540fff6a131503ffda848540fff54d21503ffda560540fff54963503ffd3254540fffaa931503ffd8348540fff60d71503ffda54c540fff60532503ffda74c540fff69521503ffda254540fff69532503ff55284540dff6a5215037fd935d940dff66171503ff53148540dff6a551503fbd4160940ffe4c171503ff9824c140ff748633503bfe885c540ff754633503ff9514c140bff68d82502ffeaa48540ffe68530503fbd5458d40ffb889635037fd9848540dff54d925037fd5264540ff760a33503ff93058940ffe485305037fda960540ffe68930503ff58154540ffd61611503ff9305d940bffaa951502ffeaa4c940f7f61d71503fbd8350540ff78cd625037fda960940ffe60530503fbd8550540dff5c593503fed8388940ffb4c6225037fd9258d40bffaa962503efd5399940ffb60622503fde335c540dff4c592503fbda454540dff60592502ffeaa5c540dff4c9965037fd8564540ffb889515037fd5364540dff54d96502ffda54c940dff6a5325037fd5164d40dff64951503f7e5558d40bff68d515037fd7365940ffb54e22503ff9a64c140dff605935037fd9558d40fbf58d62503f7e5558940fef54d41503ff61160940eff60582502ffda160940dff4c991503fdd314c940dff60d92502ffda35d940fef54941502ffda358940ff760633502ffda35c540fbf4ca66503fbd3250540dff48593502ffda85c540ffb4c982503bfe8848540bffaa981503ff53160540fbf5ce66503ff53284540ff78cd76502ffeaa58d40dff60d915037fd9558940ffd54e11502ffeaa60940bff68d21503efd5299940fef551625037fd5265940ffd60e11502ffda254540dff6a5315037fd9160940bffaa931503fd9314c1409ff69993503ff2114c1409ff6a576503bbe88505409ff6a191502ffaaa4c140dbf65666503fce228cd40df78cd965027feaa64d40fe750633502fbeaa505409ffaa9915027fda954540ddf955965036fe6664d40dfe649305027fda164d40efda2211503eee22999409ffaa992503fe62284540dfd845935037bd9850540feb88941503bee8888940dbf64a665037bd9250540fcf955415027fda95c540fed4c541503ef93099940ddf955915027fda958940dfb662225027feaa65940bef69151503fb9414c140faf55266503ede3399940f9f956665037f59884540d7f9dd96503fea224c1409ff6a582503fd6118cd40dfb889915037f59284540dbf58d965037ee2265940df7646335033fe8864540df764a33503f7655845409ff68991503cfe7799940 else 0x6c1405c0b03c0007360581a0b804080b19094160140a0440f003a0881a0b00a0580190501a028120180e8cc011816078000e0d170380d0306504c0818804064c0e8282a03c048340281a0102426b409044160140f00300d80e060bc0502600701b0305b044160280700420a8140900a0780181584e07809068110080503480d02a2805205034090040281a9038041341504c00c03009828248140301e008c0902c1104043038040f01920500c07606832028040901214a01b02027048170303601c012036098160680c006c0b0301807240d826050060680c0a70181b01c78140303606824006c0a01c0d04018b80e0582606031505c09024010640e018112d4e0780c0b82205801b02c0e01810062e038103b82606031b04c0b03404062e0981606030145c1302c0c06028b81005824030180c68170280a00806068110382938140d02e0680c00821c05c0f01c1102018d82009816068080c6c17028070341300360b81c028140809e00701f03c070480806360b8260700a0409e007c130281a05c0e00404f8140381a08031704c0d028060604e003e0b80e0701209801905c0d008110640a013e0981c0281026031b02c120680503800d820090080c0d9600c1302c0c01018c8360482e0702402801e05c0a02c120081a0140e0a4803818070100c039905c070340106412023e0502606030145c0800c120180c0630018260581a02031b0241a014020440cd8120b81c0900e006c17028110380421c00e82e048220d81a01009e0581a00805028110382910360780c0b82205001c05c0401c0e02810063e098140b81a03801a05c1204c0e0081a0140a0a4a0b826068020c81402700302c0c0601cb02e0701c0100c0d0220505270441302c0d01018d02e050040381c0c824148c0d03c070440806360b8160900a07801b0300f0440a0104c063e0a814030220609e007efdbbb5edfbb1feba3a7fe9239d5e53b917e30b895e17b7d7de5b74bdb3b683d90b5edd6b3539d3e3471d0233d1cd7b2ebca5b223c713183c4e30edc2b306bc032f8fbd12edbb9f2e1db722d7db4cace7b24ac3daff2ba7acfaaf3aa2aa2ba6e296da43a8afa19280f9f627979d0a6d99a62661980a5ad95124ef926a41d8f7239b8d1a30f8b3a28d88e21cf8612111836a0858099fe57df1f1d7af9e7d7851da17559d0172b1c6b7081bad6d61b216b59a7768d99f5668193763b188361598015f017755ca96e95a5162b57a95955551513534948751193f14ee935b4ba12a74971207471916743f90bd41a10093e80f413c00ed33a20e653890ded36d8d573458cdf3278c6730c0bf92ee0b592c38acd2a30a4b28009bf25d092923c88a7219881b1f687991d887211b5867718d85eb16d057314c84f112c046510683c50de832f0bb828f091020d06b816d04600d7025804b000) else (if i<3 then 0x503c01682a01020408182c607c1a04a070181b01d028160181103c01a0f4080900c82a0408c0301e00ac000a0181c058a0b0260340681a080ca0b01403802c178240602413416018090480f00580d802018220902a060b20110580680d0301d048160240700580d80200816088240a8182c9415004110304c16360a82e00802040b0247040064050341300044e82a088140281e00641704c0d0640013320c0320b00c05024068051890ba1b06c13c140680603402024102966098180282c058002c7c0902c1104c1601402030582852140500d81c088320101202986c064030480e01809050a520360381c0a812090002080190440e0540901c00f0dc0a8240500c07801d02412050190140f00380d816090020281c0a12201701b01c0d0580a04c0118280b8260780026680102413030741040406440e00605010350220700842032a0780e0540a0181300385c828278180d00a01012080e2805c110409903c0418808064a360340a0de09032050040305206b0190140e0540904c00f0380d81a0b0240480402162406c1104c0e00815024041c4a0b02207812001584078010140f040742440806460b802090182c5415028050440f00320c82c050240301a0146230500804078060481680603c0158180780e09800226c15048070006cb0000181a06826040c40203260701a034160480a01c01012e0b80a0282e070140880054a41e06c0a0041303406054014036048240081c0213a01d46c1b04c06c120040e05405020a5880a0682c04826006411034160240700340f8183500a0502026032305c0c07c00132a0482c030220780190540d0180904c00d0d80d0220b0140301e008c120441016c0c0d4060204c06560882e0501c0280050708c0681407c0e064060080904059782e080de000995110470380502810130190130158100c8240081c0213a6058110280603c00c05605012048204c0c2070080ca0981802b02811038042101920380d808250140b8220780270340f01c1006044c0f03a036058240080c0a81848a08c1e41406c11064090080603059703c0502a0700c09801c0600b040590580603c0108882300a0481c080980c84120204d0540f00320581a44820208080c70740641c07c0a0640605c0e0041160d40f8140881c021080c8c0d0580b0001cb03c0a81c0901403801f0240a000010406103804064c0b01a0301409801b05c0d0180b00058c0360a0b6070240480e00802b0481104c0c0d40a0104c0656098183880c058002c7c06014060340c190610480806520b8003603900a46f0440a068050380118180682c058000e6019038150404501c00e016080220b00e000d9d034160480502c00c006088260608a050080c80741301b04c0e05801014081c560a02a0900e000d9817c07034140204604c01102c068240500e00 else 0x82c05026000b950380a0404f0005cd80200828240b141e059054090405e0180f00480c8101a0e02c504816416024101804e0140f00500c820238002e50481b05a054140740a0480503c016160240c40e0302603c0482c0302207803406c01010441c2e0a82e068184b0120380210004c1c05880183c050480b141f0701005c0680d0305a0441602407006a0a80408102060b1905409008110308016384a0c00d010240b00f00a0a81c098031070190341101c00113a010220a818400b1806c01008170340d04059082a00822060982c6060160190404813809058))
def x511l12 : Packing := (195,3,7,0,0,14,0,x511d12)
def x511h12 (i : Nat) : Nat := (if i<2 then (if i<1 then 0x80a700000d0284000000000000000000000000000000000003c23100002c4c3101eec0fdd05c504162145740700000201cc91029c4f620135c049809c3c4ab106530036205e70500d171c0501000014188006c4810e81166455b00002056a71348c04c600ba4192b02e944e24153f4035717b5c011a05f9c09f70821047bc14de85a82104b46b6c09b5069c005e0c1f99057684fac01b7869d91240000030b0105cbf15cc81dbb0773015c00001414000003804b0000202510000000011000000030400011c00000000040000010000020c010400008214000100100100025914758004000000200008314000000001600000000200400300000c0010c00000000c100000000200500014000500300000000bb940060000000080c30020014ce0024c00412800400052850004000020040423c70000000400400016c208000b0010010002801c00410c20000090410000000801007880000400000005460000000040800e20000000000400020010000000000000000813020800830000440000000004c30042800c01800000cb0021400090410000001010010005000001c00401400020000001000000000000000000802801800004000c00060000481800050cc0000410400000010400000050c00010020000010040030020800002000010001c22c40040040000000030000000800000010880010800000000000020000000000400010000000411400000000000000800010001400000402801400000800421800000000000070000000030c508000004000000a10000000000a1800000000000400011800470000020403c00010070011010000000410000010000010400001800010000400000440041401401000040000004000003c20000830001c00000010012400000000001010c000208100100000400200408000000018000004100018104300000000000000000000000000008200020200000104000000000000000100204004000004004000000000008000b08000000004600000000000200000038000000000a0000000000400010000000000400c40010840c00010420000c000600300010000124108100a0000400010000040000000030000020030010410040010000000000400000000000000800000000000010030000000020000800001000410010000000010000400001400000000400400000000000000003020000400000400400400050000010000000000410010000000000010000002800000000000000001010400000000400000000010430010000000000000010000000430000010012821000010000000810040000c10000c000000000000000100200000000000000200000004000000208000d040000044000000040040001000003000000041040000000000000000000005041000000000001000000000 else 0x240753048b41ed961a20132b01130609c01fd9963f1784828860a84c0347044a42b3c007444d7d00598423a010ec030d08174680b11e3c605206a74096402cc824aa080781319113d84a650326009e609afc05b309a2c615b096800008014204da00003420fd057b8444f11fc0000103afc1d6c17ab067840178000000000046df18b14624009700074303479e5a5108884bd604670564400cdc2345073f416290374000000000000000001401e304140000000000000c05c80000000000000515d102a01080f813830959c0e5713bd820910552c2b740006c0ac7031100b271317c17ad141c00000000000000000000000153841e100002064a0000000dc000038543e0b07c08a304cec6008190dc21700000000000002042f000000000000000000011a80000000004118000000000c074800000000301ba00000000000000000000001021171927869ed15c182151017444dc302b4422d201e800000000281ceb1777592500001c0c64187580fc97111800fa10fc40cb10880000000000000000000000031488409d40706024e605dac013b16ab81340000000009102186a7608f582644018f19fed020e0511b08da0169000a0c269f190b45c07069d0228a02f9c20d01ab446b9003654142e02be446ee1a104222e04540245c06ed81e9a0690000000000000000000000000003c258b0a370181e1906845660a584158604b0000000002460d715440000000000190310a2067551781806f90271858f7058f44be00ad201cac15fa40b55025281840099f02803116ac1fbe096c452b80320c12a4155d806690369421f801f94248f160444d4006f2419ea00575c04612ea40d271769441c612ee000ca0514412dc042d05506103741ad50223023b10505c2b040a158683d09d08279c07949c32417e4412be19e6c22900000000010997c095d07f0c1e201a93407851b03414600002c5e500003c072000024266e184e024d00000000050746c65120a278067506980000e01a10060402d100ff509540000517518486e07c9812770053dc50017ea066f000014246000000000d187100e4f0a180103d0ab8000000001022c105240000c040341c7b05b4000000000000000000c0a90000000000000000003011800000000104498026e024c5030305e2a02f1428171259052e000000000167bb051a073d480bd709fc044241a46c2bf816dc4606c080a01dfa06588193f0459c1c84033a421c66a8741c9505400000b0513c104c097c000010224027111706c1b27075c0000200e140a82012b822a911720017a09cfc16f600ee0071613b8000000002c11b00000000051a31064b608ac406a00000c5e7009ea8292000004658406cc000000000000000000c53500003864eb060b813fd01500000f088e41c59006b403750109443120103c6a63001800) else (if i<3 then 0x1b000000000000002805211a4f056f7144d86bad03b3057f6076004af316364287e0757003fb611240ef50a3f4151d15598241b08418124316e8c68b2053a04b0f16944291f008c415ae0912c47191a3882534076880abd053018f5f74118061b08e10599705a0000011643c5ad0000044df16090862b000000000d08fd4041205f701ff207a04495c157b02aa003b8c167e15b1848510336017be150b449e50a98452820a4144059176300565030f4626f16e00000b03dc00002049ac0ed00000000010008000000000000000000000000002814d0000341800000140a690ada8415f00f444e6d16ac0000000000000000038276006d40000c025f1904c1a34000000002451dc036c85618683042974045e00984015dc13b0000140f31054a02721033280bb50444c1a5a0a3a844d802e040d0514a4000000003863b518bdc2590143e42a26037f41c20000000000000000000000000000000101f7516990277117b8d9d4207a8416010162c432410a9416b30aa00000b0ab10027000000000510b400000000280e80000000000000000000000242b81090300a0918f24022306ba44830000305c90000000000000344b5204dbc206611d00000000000000000000000000000000b1a58c59aa008740f1f12f00000114b2012e5170fc5495067546a1b198640035020a4018a001c455ac1839c1990162d8153f01a44688f06a04503906fe058c90aaf81de100b705ff61426c446012ca80044079b8262217a0c4f9d138f06b8d035158bb60191418360ae5c21ba079000000037845de907528086a00f180f08089e0482c115240e901a6702a3c0a2a4175408be862351478008ee047c421311965826ea0168d804516e5c46380a68025710235446c2091e844ef002200f9119944092c028d850200000000000000000080668011000003850851712c00e108dd000500001c1f51198b81b800001043981a50449d0097b413c612fc40e020802c2a700000000000000000000002445721992c1cd310f40000d11da403a00399c11331841817fe0138c419d0384c1f34002c0000a018885bba007cc11e81060812f9103000009174ec15b000000000000000000f061484ad3081e41f070558452610a61814fe00a980d3410820559c03ea8031e0848c129d074d426070314416560a6f01213031d41ec40a96441fe0a30000000000c579000000000209efc15f712cf81ab000000166219a88235268340000f0424c0cae050c044500003813a0000000000000000000000000000000041487152000000000284b4000028055c04c00000405d0000091a1f84c8a014400009102700870000000000000081be5125c000020ab704f8314700000000000000000000000602c00000000000000104528650d19498499717d281eb50269001200000000000000000000 else (if i<4 then 0xb1a278518600ac82140029c41d03004141d90000300530000000000000000000000000000009800000000000003104480b92047044e9106d38539202160427405bbc18d50240c2be10072060300000c0e20000181250000244ea6065c000061194c5146614200805055681616116241fa2092c456d5090d1dd41119340bf218a08294000000000517df18ea619fec27840780810fb08eb0020e083a8252d16c785fe768cb426a3138140aa408ccc5d221078d91991332408fb145b866b30363c53cc0a93c19f206e400009166f467da12b80000e19db8473d1364c0fe709d746b20000081890000105ac50646821d606a8c4e700002c5efb05cc0000000028137000000000000000000f15a3421800000866600000813eb179b86a200002420b0000102bad05b2c53400002011d407b9819b1072cc653218810091a046a00b6000000000a00280000000000000000000000c01b080cf904080000e08900000e0a55063e00000c05f000000000907bc0000101f0c06ec09fac1fe4189d0032c06bc80a2b041bc076e0a7400000000345c5000018079000018024309b000000000280650000246ac0000381c0000000000b006545623154c00000000000007098d841320a6400003093c000000000823e502928039000000000d062b80b7f162104fd0000244b8b021200f400002c669e063c0000203d74221007d982bd609080000e1561827d0000141640000340d6000000000808e54293e063a46ab60869041bd042145ca0070cc107102c54226308bbc00d31552c6b7801ddc099b13f04584807d282a9e0896c219a078e81595013c000000003808c00000000000000000020aef84380130685f800003028200483c4a200003c139711ca817071251429e3186bc1a280207c1dda063246a9305de80ea0000184ce703c9826fa01ac00000000000008017201871154a8546a00a4448cf0ac941a1c0810c5ae902bbc02fe136f869881346803e306628672406b3025461a6a41a0d0712c0f690af2465f30a2ec440c1018c407d14280000000008583f043080e7710dfc6823022f81953181fc19c4758e81c61055d414ab035c00008102c846b4052c0000408c00000000000000000030073508784186415acc1bd517b0d94f71050443a00002060ae123485b2e068e80c280859c57b00001420a4124ec4a0000038147019dd401b705a80000000000000000000000b07c400009149000000000000002043440f8000000000000000000000010261e175c04c2f042a8283000000000000010123309f0000000000000000000000000000c009000000000d19c382b10000000000000000000000142494702e00c10000000000000041fd40abf81355011f41b70000200e300001025d677fc000000000000000000000000001c else 0x20355846fa0297817c016d504c0116880000e0943c18b00000000000002007d000000000d04f40000000034000508c80000417925a631040641f8512040284417f1020cf0115c059c0a7c0000903ec000021950000000001823c904a3c4b16024ec637f00b00000e19d1c0484706281e7c06d88532318f702b5e009405a3e14f4049a0)))
def x511d11 (i : Nat) : Nat := (if i<5 then (if i<2 then (if i<1 then 0x486335033ff55242c9a81ff64c1a84c540ef7b0ac9282a07ede3354a66503dfcc0b0498281fe7615418cd40ffb260a9b02a05ffabb689305033fec1352a8a81ff654da24c140cffb72d2a64a06f7eaa955635037deaa34690a81bfd846aa60940df7aa555282a06fed82aa932502ff75da6311281fed506aa4c540affd76d4aa2a05ffabb4c1715035ff44346b8a81df76e5518cd40bff370d0a60a06ff61168d82502bff5db0ac8a81fd58ce5584540dfe42355260a07faa22505305037ec9855498a81efa4c28888940cfec22d4b04a074fd939de66503b77112c6cb281fc7955418cd40adfd76c94cca06fae22691515033f711554c8a81ddd64a5584540dfb26355260a073de8864a33503dcf4428319a81f378ce7799940ffa260a9c22a07bd68884633503f37114ab33281cfea21924c140ee7caacc282a063fe886a57150277edb554c0a81ddd64e55845408ffb7155324a07fd1304c521503a7ecbae733281ff24c15388940eebcaac9466a065feaa9dd96503fb8984ab08a81ef38ce8888940efcb3111422a07fc9304c622503beb08b2519a81fcd4c65550540efb26098b24a065fe776a1915039ef4432319a81efc4c28884540adfd76caccca067ee226a5515033f711350c8a819df955a864540fd9c67114cca07ee93088a66503be71132319a819bf68a6664d40f77510a0a60a076de3365666503f4f19aa933281df388a3365940ff2a6299282a067f611aa9925039bf444aac8a81db7999928cd40edf260c94cca075de339dd965031ff44554c92819fd846aa64d40cfdc455532ca0677e55aa9925023fed8d54c92819bfaaa6664d40dfd44555260a07cf9309de665033bf2ab44c8a81fe3889418cd40ff4a6311282a0776e5588991503b771132b33281ddb9562265940eebcaac8c66a0677e55aa9915033bf2ad54cb281beb88aaa50540dfb260d1aa2a0767d93956665033bf2ab52b12811ff6d6aa64940fd7260aa4cca06f3e55aa941503beca9b24982811ff2e95364940c7fd1155322a07eae2255266502fdb5da62a0a81ef98468888940ee7caac9282a06bbe88aa941503bf908b24982819fb889a164d40fcbc672accca07f2e2295541503fe898262c0a81fb64c15399940ff32a6a0a60a07f6622956115023fe5d324a8a81dde955924c140eebcab19b2ca073f68884593502f5f5daa9332819df955a164d40ef5c44cc282a07e793095666502b7edcae733281ecfa225550540e7ed10c9422a073ed91a2222503b3ec94ab33281ff84c22284540ff8c6711422a077e59388a11503f1ea9aa933281d6f9dd9850540c7fd10d0b26a07f3a5550530503dda98d10a0a81cefa219250540c7fd10d1322a05efabb4c266503dd6a0d11112819fb889a664d40ecfcaab1b2ca047fcba4c5925023deda554c9a81fe44c5414c140 else 0x815ffaed985c540dff26155302a077f59261611503fdac1262a0a81aff60aaa60540efdaa711322a0777d5254d915037fb55262c0a81bef551a358940eefaa4a9b2ca067fdb968951503beea9466cb281dfe615924c140affd7699322a067fd9568d625033fec9d54b8a81ff58cd52845409ffd76d1aa2a06ff581aa951502ffcdd304982817f7aed518cd40dff261552a2a0777e554c996502fdf5db0aa0a81fcf6155350540efdc44a9b2ca07f9d52506335033fea8d54c9a815ff6c58364940affd76d4b02a07f6e554c622502f7f5daa533281efd60e1160940fedc452aac6a07ebd5458d625033fecab42c1281fed505a24c540cffb2355304a077dd8164a33502fef5db0519a81dfe605924c140efeb72c0aa2a07bf930a2171502bfedcb4a90a81dfd6e55284540defcaad1ac4a077f9b9609305037fa98b42c12819ff609a164d40f77d10a9a82a07f3d5454d81503def44466b8a819ff606aa64d40bdfb6a994cca077f5b94ca11503f7c982a533281dfb8899558d409ffd76d12a2a06fee2268d51503bdea9330a0a81ddf60a5564540bff576d0a60a05fbebb54941502bfedcb06b8a819ffaa99258d40bfbd76c0c66a067fda9aa951503ff51134298281bfe6e9305d940cffb22d1b04a07bf68854a115037dec1554a0a819ff6a5a54c940ff9b0498a64a057fdb548593503fe6a9b0711281ff54c5814c940ff3a82c1466a07fb982505305033fed4b4690a819ff6e5a360940ffb2a6d3260a0777e556a531502ffadaa6508a81ef7605828cd40cffb30d1ae2a07fb54169531503bfaa9b2508a81ef7a21218cd40ffb262c1260a06fbd5468582502f7f5dae733281efb609814c940edfb72a9ccca06feeaa889635027fed955498a817bfaed5399940ffd444d3260a07fd58354e11503bfc98330b8a815ff6d53264540cffb0355324a05ff5b2616115033fec1554c8a81efda213284540cffb52d2a62a07ff211689305027fedad5498a819ff64aaa54540ffb26155262a04ffebb68d21503feac0aa319a817fdaed3160540efbb3119ae2a06fed82695325037fc98350b8a81ffc605514c140affb72d12a2a077f5a984582502bff5daa6c9281ddf9553164940eefcaa90b26a05fbebb54d41503df6c12a4c0a81fee549414c140bff576982eca06ff9ba4c162503eef19b0eb8a813ff6c9a354540ffe260a9422a057febb54996503f9ec14aaa0a81fde955a24c140f7eb04c0aa2a06fbd4168d825037fc98344a8a817feaeda64c140ffb260a9a42a067feaa65562503bfadca6290a81dfb6093264540ffcb0499422a07bbd8260d415037ded2554a8a81bfe4c2aa48540cffb52d1302a0777d8554d91503dfac1262c0a819ff6a5a254540ff9c66c0c44a07ef9b54c266503fdc982a8b1281dfd6a53148540bfbd7690c66a07f5e55) else (if i<3 then 0x74c12a2a06fbda468d51502bff5db52c1281bf7aaa33589409ffb6355304a077ee226a5515033fec2d54c9281bdfaaa5558940dff30355260a067fd52aa996503fdaaa26508a81ddf60e5564540ff6a62c2a82a07f758295611503bfacc2a508a81fde4c25558940df7d54aa2c4a06fdeaa4c5325037fa98d5490a819ff64da85c540efbb24a8c66a057fdb969581503fdcc2a8298281def505a960940affb62d4b04a057febb60592503bf699352c1281dfd8458364940cffb0b55322a07e7d5354a665039ff442a6c8a81ff64c1a74c540cffb52d2a42a07f9d548cd625039fec0b52c1281cff54a8864540ffb260a9ac4a07df93061d71502ffb5db02a8a81dfd6613148540edfaa4b1b2ca06fed32aa982502bff5daa6cb2815ff6d53265940feeaa6c2c22a07fd953685305037fc98554b12819ff54aaa64540ffb260d1aa2a077dd326a5315033fedcb4690a819ff6a5a760540eefcaad4a64a057febb60d92502ffb5daa508a81dbf6556358940ffcb0711422a07ef9b24c266503fec9834a98a819ff6a5a64c940d7fd5544242a06ff9a268530502bfedcb44c0a81fde955a14c140efdaa2cc444a077f58164951503bef19b2ab1281df7549918cd40ffcb04a9422a057febb64d765037df552a8b1a81cffa213164940affd76d4a42a06fdeaa8cd715037fc98554b8a81dfb6e58388940e7fb04c1b22a077ed8388991503ff908b0498281df76e5218cd40ef7b24d22a2a07bed31a2222503ff298b03112819ff6a5a848540fe7aa4a9a82a067feaa655635027fed8b46c1281dbf54d9299940ffb262d1260a05fbebb4c9415033fed4b4ac0a81fdd54d5284540f7ea6344242a067fda9685325033fea8d54c92819ff549a864540efeb72c2c22a07e7e5558d62503dfd44342982819ff655a348540bfbb64a8c66a05fddb160a335027ff5db46c12819ff615a264540bff374a8a60a05ffabb60930502ffcd934298281eefa213250540e7fd10b8b26a077dd8354d91502bff5daa6c8a815ff6e5a848540efbb72c0c66a05fbebb55162502fef5da62992819ff545a960940ff5c44d22a2a07fb58169151503bbf2aa64c8a81ff3889518cd40d7fb0355304a067fd9268d515033fed4d5498a815ffaed8364540fbf4eed3260a07fad8588941503bf698b3111281df7615918cd40efdc44a8b26a077dd9160a33503b7edca6533281dfd6053164940ffd260c0c44a067fda96a132503faf2ac66b12817efaed8350540ffb260d1262a06fee22aa9515033fed4b4e98a819ff6a5a84c540efeb02d4aa2a04ffdb2aa951503bf6c135299281fbb54e2299940df7b0b55282a04ffebb69532503dfc9851090a817fbaed8388940e7fb5344242a075fd9361d715037ded2344a8a81ff954e2284540fe7caa99282a07fae2254d41503ff89830b08a else (if i<4 then 0x502fff5daa690a81ffb4c9a160940dffb50d0a64a077fd9568d815037fed0d54c1281bff60da254540effb26d2a42a06ffd32aa951503bfed4b0a90a81bff60aaa54540effb2355304a077fd826a551503bfed4b0299281ffe4c1a548540dffd54a92c6a077fd9369581502fff5daa6c0a81bffaa98548540dffaa2d1b04a05ffebb60532502fff5db4a99281fef551a360540effb2ad4242a07bfd81aa982503ffa98b0a90a817ffaed5358940fff260d2b02a07ff98568530503fee98b5099281bff695a14c940ff7a82d1b04a06ffeaa54981502ffedab5099281dff545a960940fff260d4242a07ff5814c951503bfecc34a90a81ffe6e9814c140dffb74c1ae2a077fdb254d965037fed1aa4c0a81bff695a84c940dffd54a9b02a077fd854c991503fdeaa35090a81dff655a260540effb52a9302a077fdb84c9915037ff5530690a81ffb609a14c940effb72a9a42a04ffdba61521502fdf5db48a8a81bfe546aa4c140dff30555260a057febb54593503fceda2a319a819ff6e5a354540efbaa6c1b24a07fe58188951503bf6dca6311281dfb6095264540affd76caac4a04ffcba4c582503fd6c1c44a0a81feb6095250540ff5aa8c0c44a057fdb560d92502bff5da64cb281cffa21a94c540defcaad1a42a067fda9689315027fed9d54a8a81bfe6e9305c540ff5b0499282a067fd98aa9215033fea934cc9a81fde955a64c140cffb72d0b04a05ff6bb54e11503bf6dcb03112813ff6e2aa4c540affb72d1a42a05efebb4ca66502ff6d8b07112817fdaed3148540efdb0b11322a067fda9aa982503bee98b52992815ffaed5264540affd7690b26a07fea22545305033fea9342c9a815ff6e5a354540feeaa2a9302a073fe884c991502bff5dae6cb2819ff6a5a354540cffb42d4b04a06bfe8868951503ff2c2c4508a81fee4c1a454540f7f510d1260a057febb4c592503fdaa0b5098a81ddf9559258d40efeb02a8b26a077f59354a11502fdedaa64a0a817fdaed8384540f7daa344444a077f951649305037dea0d54c1281affa21a348540bff576982c4a04ffdb3aa982503bfac0b5298a81bfe486aa4c140efb966d4b04a077ddb960a335035ff44554b8a81fed505a74c540ff5c44aa2c6a067fda548593503f3e994ab332817fe6c5824c140affb72d1b02a076fd52999935039fec1352c0a81bfd605a354540dfbc66d42e2a076fdb954a66503b7e9932b332815ff6e5a760540affd76c0b26a067fd9868951503f9eaa2a6b1281ddf9558364940df7b04d22a2a07fd61160a33503f5eaa26533281dfd6a53160540bfed7699422a05ff6bb616115027ff5db42c1281fdd4ca5584540bfdd76a9c44a067fd98aa9715033fed4b46c0a819ffaa97164d40ff3b06a9a82a077dd8564a335033fed4b46c12817fbaed81889409ff9 else 0x17b72efb5dc0babd744ae4d5c38b7d96e2adb55b1eb5d16912ce65996b2c16452c38583aaf595e32bab56f4ad515a22b2955daaa4152a2a2e53faa7b54de299652b4a4a547c28c75158a27143b283a4fe69edd3c3276b4e329c25371a6b24cec98e931525f94bbc96892be25354a1e93a5261a487488090111dea38c46b68c7d18222d3454489f1125a20f43bc86890be2156423483a506720b340ee81190101ffa3f927eb8fa89f153db27aa0f3b9e5c3c567814ef51dda3b7e7638eae9d4d3a387430e6d9cb538f27120e169bfc37806e3cda41b0135a06aa8d3c9a3d342e6740cd5196e32906404c6d98aa30dc60f4c0097d02f285d34b7d969e2cc4591cb0595cf2b3c55b4a9315002988524ca2093fa277c4e609b3932b25c84aa0936123023e846b48c39140221e434c840905b20283f347c88f4a1e483bf87668e911c68380c6f40da11aca34fc6870cc7190030e45fe8bd7174c2e005a20afd158229e851f0a18138c25fc4b209331230239c455889010be20b83f907cc0ef41d2438106d10cfe193830905cb0b34157829104e60954121021e83f6075e0df81a6830605940a0c123821603e006d00bc0152025803ec0650083008e0003bfed4b0690a81ffd4c55260540fff260c2a42a07fbdb54c941503ffc98344c0a81bff546aa60940dffd54c0a64a077fd9569932503bfed8b06c9281dff4c9a954540bffd76c1ae2a05ffebb60d21502fff5da64a8a81bff54eaa48540bffd7698b04a06ffd5368582503bfec12a2c9a81ffe545824c140dffb04d1aa2a077fdb960532503ff6a9342c1281fef5498350540f7fb04a9b02a077fd9354981503fdec12a6a0a817ffaeda64c940effaa4c1b22a07fdd5360d21502ffedab42c1281dff5458364940ffea62d0b04a077fd956a132503bfec9b44a8a817ff6e1a14c940ffdb04d2a64a07fbd546a131503ffc98344a8a81dff661a54c540bffb6ad0a64a07fbd5469932503bfec8b46c1281dff6959160940effb26d3b02a077fd9768d81503bfedca64a8a81fef6153250540effb72a9b02a07ff93069d81503dfec0b46c1281dff6152164d40effb52a9a42a07fbd5468981502ffed8b46c1281ffe615a24c140f7fb06d0b04a077fdb54c996503bfec2a62c9281fef551a160940bffd76a92c6a05ffebb68582503ffcc0b4498281dff661a74c540effb04a9b22a07fbd3269151503ffc982a4c0a81fef506aa60940dffb46c2a42a06ffda569932503ffca934c98281fef609a454540dffd54c1ae2a07fdd3169532503bfecab5098a81ffb6093254540fbfb0ed3a62a07ff9b1609305037fed0b46c1281fef551a84c940effb24a9b02a06ffd31aa9825037ff552a6b1281dff6e5835c540dffb62d1b04a06ffda568582503fdedc264a0a81dff6d53264540effb72c1a42a07ff9526853))) else (if i<7 then (if i<6 then 0xc1090d00a05804cc1580b0360180a821982b02c08c0300d033305a05805801182e01a05c008c1582303601806811b00d00c0840c831700b02607006824063501806c1209c062c0060740603130050440c3c030068130480c5c034098202180c5c09804830f01301600360500e03407240060701a039382703c054040300d3702e03c13818062c00e09c0880f0300c6ffe1fefffd27f89fec7fcf7f80fee6fd81fa97f3a7e43fc25f787ed87d8afab3f477e6b7c9af8d3f0e3e0efbcbf74bedd3d9c7b12f5c3eaefd4afa7af4a9e8bbcfef9e2f379e65bcb87960f28be47fc7778bdf145e1f3c25f825f015df67bd9f78deecfdd07b82f6dfed73da7bb3c7647ec2dd797adff599ead1d50ba88f4e0e975d227a2c7432e819cf9b9daf38fe6bdcd3b983f2d6e561ca57937f233e447c7f78f171a6e2ebc4e7889f0e2e163c22f832f034e033bfa37dbef91dec1bceb784eed8dd4fb9db722ee14dbc7b6f76cbed71da97b46b67a6cc3d951b1df62e6c2bd80baf275d1eb88d6c5acf3585eae5d53da9b7523ea16d3f7a72b4c1e968d26fa473480e8c5d13fa1e742f6817d00f9fb33cd677fcedf9ca337be6b0cd15993b31465d6cb35962b2b26533c9ef931b24ae459c85190631ee63b6c7218d7f1a2631ec5f18ba31616291c4c188670eee1acc2cb84ff09260fec1858247030603ac0557fe6fe9dfa2bee37d5af87dedebd19799af2b5e1abba776b6ecedd56ba4b7456e77dcdfb97371cae265c05b7eb6ebadbedb4cb64d6bd6d67daa9b507694ad05d9c4b2e56532c8dd900b1b562a6c475868b02d601abf057afaee75cdeb8356e0ad5f5a26b2c561cabc156eaac4d579aa655432a78d4c0a93551d2a1c5428a7ef4f729db53a6a72d4d3e99a5303a5a54a5a938523fa41d47a28dbd19ca2ed44ea879d0d8a14f41da822d014a0093ef67c64f7c9e6b3bba769ce979ce3390270d4de99b9d364a6c14d3b9a2b33be66fccc49927315e618cc00979f2e7a5c1cb5d966f2c1a575ca9994d12962513ca0193b7272e4c7c969928724ce486c8fd91c5226e43548398fcf1f323c8476a8e5d1c4e37c46c78d2d196a325462f8bfd16de2c8c56b8a4913a225bc48688ab10be204c3cd870d0d56197c31f861f0af6156c28784c3091a11b420583bf068e0c9c17882bb04de088c0eb81b7030204d4069809d0075ffbbfd17f2afd65f943ef77d8cfad9f533e497c5cf84df01bdbc7b00f5c1ea53d247a12f335e4e3c76785ef07ddfcbbbd775aedf1da03b0f75bceab5d38ba40741ee7a5cd6b99d72eee545c8ab8ef7192e261c39384c7036df7dbcc37886ec4dd1db9bb7116d68da39b18b6006bcad6a5abc355d6a6ed445a75b4af68fcd0dda08b3ca675ecdcd9a6b33d662ecbc595ab28f64bcc8e18f8b1b562dcc49d880b0db6154c1e581930175ff8bf0 else 0xd80416603600601580003010048502140c13e01c04c00c0b282a074264c040d50103926032040e300c062904c062c00c0b00c06200003c0581211804210383a040280983726022098048182728256054140b1182d05a04408141483500a08320d888800c80604a0780483160110506a0a88400068a035001006a034090e81c2e01a06028081300d0204e320d402818c12d02603814940101880850304f8060db00025811008f00006038090a05f00e03063018a0180802d0484a0640c19028220640e2c020018181c2406800c0c6c0c818a81848000d100101a0580e100a80a060058880c301a0040240648061c00410088242406800c0c602b0102102609cac1700d03e0046030184c0a0050180c401ac000060140a560b80a823002405c0980a01b0180c660b40b00b00c0940cd0018140680e4607406030f00e04a04418940200601c07018ac0a0340a1b05604c1300b00a066c00c04030e80d0360940a03168050180c360b40b02601a07c00d80681b001e05a02c13801181604a07807801602d02609018980600d04607018b805824068364e0bc0b81f0000e560ac0982300c0340cd808248166080181b823390600d00781e02600058082300e042004188d9681b001501a0541181c062d02c0940d0320a2e0160140d829182e02a09c008c1582303a04c03009b015016003a0940d80d0280c5c0140d00a06200de0604280e02054018f8058150460604e031a81304a07406031582e016003c038108312d2302c0380e10c062e01806c0a8201380c6c0341181c1380c560b81281601e00560b40b026016005a08c0a81d0180c5a034118120300e818d00280c061e01a0581203d0320c6c0381281906260160580f024062f0402dc0c06a01a04018ec07014061e0260886b00601a066602c1281907a05018c41702601a04418b40a81e0183781103198260280c3603076030d8160480d028901d81803c05018b80b8202108c0198082a0468a034110ea06230280c260b40b02601a06c00d40b00b03043018ac0a80c061d0240380103128160482380300b03330222380680604a066a0504700604607804d40a82303a03018ac0e0340a1e0460701a0511814068143c06c0300824020560ac0b00b00c0940cd0070130380d01ca0800b30300c0a0119b02100c0340c831581e0180c304c0158182c049408031c03806e0340c1302334068142c0381281d00240180c260380a827002502c0300581c062c06814280ac06814062501605086031182e04a07807801681e01c00320c0180b703601810081f00e04a06c009c0a00018607404031981601a07c00841803704c034028101e3c05a04c0e031301601607812031702d01c0780209b043601c084b483120250160704e031700c01605412031580503c09805829700e0400e4188d9681e01c003a0a) else (if i<8 then 0x220909802003031c1380c40c740c81e01c0409ca02b02006c0404c1398829038260a894108260319030b03081e80b01803604c04090f4003401820161c0a80cc0c7402030a818411c2120c05880001a810180a035808098272d220e00206201a4184428032031c1d80c40c6428036031e030c0602c2a08c03018d8030302e0a8901b00080360002609c84000e0101c06407000740a8190302c040ac0c125042080e4b41501904072400c0000b0242304a064101511800481840d80702c01800602c0a0490c0281888001715030e01a0901082007836600cc000550202456001c01001818f00400206360100c406c83602a080a4b0098002f80e424241a018d8180d02cc098240635030a0a40c40c78041a02c207018ac0c2c0c1690680e4c020d30210380c5c0680c22828220a00cc0c819202b04a0409c80280312106a10ca8081690680e400cc120d8292106a0140c601800505024058b00c3800088241806806400601a02300022090b02a033031e0002609c64130090304e4815018818e80303406300cc0e0e824202320840e03016282e00f8100502b02c6a00120c402018d0350316000b0320d01c60c58001660601b0202a05a82000700b0c126040200280360206e05900198260320e420005c501581d02603018ac1701821072460100c44120982a1d0380640c701a003031a0540c018080252e02c08c140b100b806c0100e80810360080040c780821103025810831a0360013026070758240629064064b4780c2c0281c031c2d80c40c606c03000024058b01a002031e01a08c0e031105206a06301501b00006020090c01b00e0007e46ca04c83006c05410149a81a0303401c1f02a300620180c6000180281c06c00c0e001280204022090980a01b0360205c831a805031006a06220140c08103054503e05808202609407801c0ee05a0404803501c00c0c1e8365203206202180a82016200660180c700181b02a03018ac001a80d054460605c150e8080605a0408c0c24190192d1902c06205c4160120100841a0d9c80504a068180b14829061406a00200cc04080c03501c04c0c17e04600720c46c407c12a02c0bc02809a01850320710060000580e10831008063a44180640c441483602a080a4a02882034c02c0d1081380c8046c1181c0602c520d00c968d81b0280d0289400340c0b1030204c00c0e000c030000260480e140302302c09080700300d020400c0000b01c24032062606142601a018c12b04009814091403504c020698041b3016c0b40f003042906006090141182d03102380d00c1360102609cf018304e033031806c0004c13900f825e01806819600304a02c0e03150186802040140a4901001880302da0a0580915805038063c0a01b0260101446cc81b005031e006070006097018161b00c040b5809062d020 else (if i<9 then 0x3042070a06e0330380e4a44160b8110230006e520041a018e82104c06300c0878001c2035054220041b018c8360321436061414818818c0001704a0a88c06819010204c0b80413e0401446cc07403035242070b802004062064808c128081b607018c01809039181202c2815019818f00e0400c46c21940301220a0e494158090006e480c80e168d800483603200090980181c00182380c058151005206a06058906a030b0283bc0140c1cb04311b20d40e0190826000018058181380c720041b018d800602c0600d408121413e02c081281cb00340080cc0c6c0c380b02003027c000b98035032080e4940c20181282a1e030c0080c80c740a8210040d40c0b1a00503206302601a80a04606070cc0034100ed02052c07029b0200404a0e4886d03303206460404c1b8c02505024058801901c0a1d0380640c6444834031e040420e412900ee0220580c17907302ea0500c03601024604e04980601c05810831e0d406606380180701c06250080c2200c0d018c033030340e48400068880106806302401c00006c058100b1d800480106806360a04e0d829240400c068128392806a034090e8292d03207804139090806406300c0940b82a210020d80c601b0181704846004008301202c505c08e8002a04a540001a818f0102d02e058880c208c0b006609808139900206a06360940c581181c068144200c0d018d05206a06302d80281d0404e5600120d40e0191b2300a062a0081d098d818681868201680801c0ec1b340300c2c0801012839240060740413908290104841824140d10a06e304780883816200604a41415120d406606300cc0e0502721060062815018818e81100a0605808168230420140c8182a33032062a0ac0480837220a40cc0c819003601a060b0941300b008364406120b80803303608070d0020330380e4a0610158040360202609cc02b00b030698120318830031504c000b4030102b0080e0b06c1181c0681446000900b0d8150302604080d4080a8140400c04c1295818411806c0780409827310020d00c6808834071b000e22200220140c0b0102303048018808102a0040d40c70000300a0484c080680b037260080cc0e0011019061304c06058704c03103190a00cc0d0192019031601c058130191dd18418e01a81a0707c480c10460281a816200640100c6c020d8291e030b02c060e300c062a0a40d40c780181c061e03081e0480586c00241b0189805036064100502a3601c0040e03100350240e0f8980b0200600141410816390520c200d8000800a048501a4840e0e025030420941c94830031206a0626000d406810202300c0900b130081ba08c0e0316018581c061406c00c0e001016e0100cc118181c30068064b4601b0190a1e02c0800f8000a02e604201b00d0204e5209800088242103c000280810826 else 0x3502c240c41a818162413600260780058100d0161b00048058601e82406088058a110080882044020306005858020302902c4c010180e01626002000900e120000602c07084008301c02c404f0280b0e0ea1d40c040980100206021018a05c0940020c0400b1812807a081100b1412c04a0001c846f004006064404058446e03a07c08818835033e0080009c60682201002c481482a0330304e5c00018818f8010304a42890180b027182520c040605c080a0183602c3e00040850c82500020044941180080b403600340c034080f8012d0203600102e4184c0c238251e048080c40b130240408841880d408080e600800304f8110382c260480805860940b8910c1380c07080d4068161e04808c0c60940810a1e000200e8609501004a00418ac0c1a010180602c09c701012880303c02430260c4128072107c000b00512812060540408060128101824a00058701f02300a0648050100f8d032000380589401800106064237488080c0950004805880190002902c400c428088e8204402c3209802030c81104e000408094166051825088c048311800482e0480e81c8301630166000d4081017816058307a0404810220101c04a00c0012b0328440b0306804060f408088dc06c00044081603106024058809602204a00418a034080161e04808104831000b0004a10090b40c0161d0306c05860198002406a406a058501812016800480501012810201206005860700810703e420140c0b0e8183c03e04898120203b02c4c080940b012201c40c0480b118002402c418801c0310002c40300d00801b26046060287410188161d0000805c6419015001906c000600b130200a02c380d8000803a200602e2a00c0008303210003e240d40c09016270025a040607c0bd0520c094a41a820161d004062a060d80b0e820160143e008080820a2103068048681883204a06058199a80300020c0c8018090161c0a4150180e128230316048080c40b1003816c088108d82b301002e200c8000e016240601a205e048400c05006024058a0b68000a1a0000c40c740c03080ee04c040180802433000816020203541003103c03808139e01a0316030812c0011c12e01a066c098048312d2012e0606c030400386c00802818c15304c0140f009682303406304605a82006c03808139c05006c060b42615818600406606300c0d406810200400c08c258242a04a00044121300102c0301880b98181))))
def x511l11 : Packing := (706,4,7,0,0,15,0,x511d11)
def x511h11 (i : Nat) : Nat := (if i<1 then 0x66303d8000162ce00000000000018099000020476802e0120b00180000000000000000038e4c0e76121308c80000000061220000000000000000000000000000000000d07d80001417a0000906978b820022e0ec3049b82c29e4142fea190583e181080000000000001814a000000002828140820000c78580003014de2d5d03700002456200000000300740001229d7054c8be38231009ed1760000041de0000d178800024104eed3106800001015162f6808980000000102a200006889bc14fa0470000209ce85ba00008003000030190000000006027c000000000000000000001c27e000000000000000000000000000000000000007017000000000000000000c1e40000000030269c447e028204280af540abe0ee000040bb48500c25bf06dc00600001e314801828bf6c1ac0000000000894000000001067080e6c1c020a330167019bc09680e1503b700f240f8a088000060b93c589031be04778a7d4451a10921818022c84f2a01b000030030043a00008735782f0c120e01c018788b0c0001ecfc000008816c4ff4097300850a3800016083315200089c11960dca00a58973845c00000019e80540000e22dd100a8884819b80a2c18310c154049e2cd012140922c1aac2f34136a0a71406be06d61161817b85e1008ff13a302004047a262404578c2681b480d8e10368bbbc0b60000e033b336000000000000000257821a421b403193044000000008158081e6c1ca803e20812015c012440515085c80c8000060bb90602010c841140a4615988acbc1f260023078d8bef806f023061573818184e2e09c80076018a863140d4c03a0000102480000000060378004f60c9e62e9046c0001a1085102000010143a209000028a20c10380e20000289f1441642646006a00e881c860fdc04a000000001a11200002033f4644c0fe000000003003ce0f3008500002c5be2016808e001cac0d90053917d1080ad9b82283f00f803fc01d42034013580bf3c0c2810ef18f98094000102e8a7880000281d000006083a030584ae000021918000000014104301c2045ac1f4000000007001000000000968800001c1300000000078b0bc188410c6082f040dc0fa0000808d50bff41c780d90000000000000a021000000003016a604a000050083c055c086a105680ae4014e2ba0000300988185c069e708b843c00000c23003c500508148015300300030200004100400701a0044a81d00000030801011540000083963010863000012430020420060020801c000a08000104400100000000f00a0900041c204004014308000008f0000000000000c20000c80040821020800002001010000090c904104418000000000000208004200408000a1cc4100441010033800040000000010040000803020401090900400010850000061c5000280142040000 else 0x1034ec05c80d7d05c1014200f0000000000000100bb80566108401c600760000a032101ac0000a20ff024b040680be0000000580000000000000000000000000000000007822705302012b14600002c0804234807480120000160fcf05980000000102460000000028187c0dd5153d83474034e247408fd0020c4a42d0bc0260000080a50c5cc14f483c00000c0e680570000001628311e00cc81f800e0ee5040217334e84278077312ef02b30063c2c5961c9025a9802c09be0638013b415ec09d218cb811404d54114b076888fd8602e0002126103d480dfe23e0065402ca0221a24a113de031b052f406a8186f08e204336044e139702ea44acc111f03ff8234862fc0b78056e81ea042be005a00480000000020b900001b0ec0001003fe15008007016800009007e887d00f700e7e134304780000a23c00002045d05ce624e206f9b12d80eb425f000040846c06c0000c05b183d00000ee01f055000019c97404f911ac0966812380f7d003c0317807a82d2f02a000000001e0ab0043b84180000a0cb417bd848fc4de4059402690403802722d9000010162863962b6e02323140c17ec02fe182182f980cba0298075e0a36005a00000000000000001c05a50344845605c200004)
def x511d10 (i : Nat) : Nat := (if i<2 then (if i<1 then 0xfbe2114c28888940fba9414c2888894087fdc12e95364940fe2e2254d5499940e37e55a22aa64940e3ee8888aaa64540efd153846aa4c140f67a554c19299940dfc930aed3188940f3f288845924c140bcfacc4c27799940dfd130aed5384540de3d54aed5399940f36e556468888940fe59534c152999409fb8cb4c1a454540ff46228ce5584540ff9130505a84c540d6ee22aed9599940fbc5824c5814c940d3f5b9a215284540b67ecc64e5599940dfa541aed3188940ff19544c15358940cef9b64c2aa60540df9531aed3250540efd131486aa4c140ff51534c15284540efd130aa9316054095fdc7aed5264540afd9c3546aa4c140e3f6aaa221164d40f77255845924c14087fdc32e99254540b775c94ca5584540f7665564e2284540ded953aed3099940fba5414c68888940be7acc4c25599940f66e229556365940fbd1314c28848540ff51534c18584540c7f5b1606aa64940ffc1314c18188940c7f4ba6059254540ff155460d5384540efe222846aa4c140e67e5568a6664d409eedc6aed8188940fe4e228ce5599940bf72cc4c25584540ff0e55889418cd40d3f5b9a213284540fe8e228cd5499940fec93054e2299940f37a88955924c140fbc9304c68888940f3ce88889918cd4087fdc82e93164940ebae88889a454540ff254195531889409dbdc7aed5250540f6d9534c19299940dfd130aed3160540fb2e555068888940f74e22955918cd40fb668888a5584540f35e55a21928cd40c7bdb4546aa64d4096fdc5aed9299940b7e5c960e2284540ff4930955318894096fccb54d92999409eddc6aed818cd40dfc930aed5388940f35e88955918cd4096fdc6aed8164940e3f611a22aa64940d67e55aed9299940f75655845928cd40ef99a44c1a354540ff0d5454d8388940f759309553164940fe6a224c25599940c77cba9553164940efd131606aa4c140df9541aed314c940ff2a22955414c14097f4cb54d9284540f7c9304c59888940f3d930a213164940f7d1306053164940f72e55889985054087fdc82e99254540ff1930549535054097dccb649518cd40ebf288846aa4c140c3fe886d6aa64940feaa224c1549994096fdc6aed8164d40ff62224c25584540ff85316093250540efd130605a354540c3fcbaa213164940c7f4ba6053164940cfd9302e93160940fbc6118ce8888940b7e6cc64e2284540df2d54aed5388940ffc13054e2284540a7bdc4aa97164d40ff19305515360540fb1e88955418cd40bbeacc4c28888940c7f6116d6aa64940e3ee88889a954540f6ce228cd9599940ff9131615414c1409df5c7aed5284540d7d930aed5364940cfd930aeda354540fb9131a21414c140a6bdc4aaa6664d40ff1131955414c140ff81304c62250540fe19534c15499940c7b5b4846aa64d40df9130aed3150540 else 0xffb130605a454540cfed522e93160940f3dd8260d5364540c7fdb5aa92164d40dfb930aed5250540ffd1304c55260540cfbebb551a160940fb3d825515360540cfbdb8551a348540cfbd546c6aa609408ffdc3aeda160940c7fdb1616aa64940a7fdc2616aa64540aefdc6aa95360540bfb9c2615414c140e7f930661a25454097fecc6d53264540b7becc5499850540fb9d536098350540ff2d825495350540e7ed5260aaa64540ff95414c5a54c940c7fcba6153164940f75d5260d5364540fbb954605824c140ef3d54aa95358940b7facc605924c140c7fd916ceaa60940c7feaaaed8164d4097fccb661a54c540f3f5816095164d40efb930691a254540ff1d5260d5350540c7febb655a160940f76d825495364540f7755164d52605409ff9cb545824c140a7fcca545836494097fdcb6153264540c7fd93aeda254540a7fecc54aaa65940d7edb56093264540fbf181545824c140cfbd41aeda54c940a7fdc960da254540cfed526caaa4c540b5fecc64d875c540a7fecc54aaa6454097fecc6d53265940c7febb645a360940fdb54161da74c540efd930aa95360540f7d9306495360540b6fecc5496365940cffabb4c1a254540efb5414c6aa60940f7f1306059254540c7febbaa99558940ff1d5454d8348540a7fecc549a664d40ebed8268d5260540f3ed526098364540dfadb56093250540ffc5314c9a1609409fd9c3aed824c14097bdc4aed935d940df3554aed5384540a7dcca6e5828cd40c3fe886c6aa6494095fdc7aed5265940fbd131605824c14097f9c0aeda954540e77655846aa64940f7d1306613148540ff89308895350540b776cc64e5584540c7bdb4606aa64d409cfdc7aed5299940e76e55889a664d40a7bdc4aa92164d40ef2e22956aa50540fb9930a215350540c77e556c6aa64940b4fecc64e7799940c77e556e2aa64940efd1304c6aa48540f7d13054d9284540ff9131609414c14097eccb545988894097f8cb545924c140efd1304c5a160940ded930aed5399940ff91414c1a74c540fb3a88955414c140c7f6116e2aa64940deae22aed5499940f66e2264e5599940e37e55a21a264540f74e229563365940f7659888a5584540e76e22956aa65940f65e55999928cd4097ddc3aeda960940ff19306155350540efc95388aaa4c140f3d688845928cd40deea22aed3099940afdacc4c6aa4c140dfd130aed3148540e37e88956aa64540eb3e88956aa50540e76e22956aa64540ebae8888aaa50540f33e55a219250540efc930889a354540fb8e88889418cd40ff9130505a24c540fb65825455260540efc93188aaa4c140e7d930649a35454087fdc52e93164940cfd9306d6aa4c540d7d930aed3164940ff9130506aa4c540ff255454e2284540ff9130505a54c540b775c960a5584540df9930aed5350540) else (if i<3 then 0x5010100020c10030003a0614030d8200300b0f80c2021c0602c34030801c06100340020d030830142000030220128f00020e0111be0018828833018ec0c36001000080d606048360308014061e030801c04a0802c3000060004802c32030a035818ac0036061d030d818700034061105106e031a03581890180b05802103b0251700c81a030c01b00c403030c800780c41c0c476001016902b04e004062f018160ac0c202480c02c301200601c180000103680e810149009e40c04041b810ba00101818400016b04b0302722018501501a40c74061b04c004061e80e821030d407002c0d0189a05402c0040c4e01e049005031062d80a030b00501858c8c5be29b113878c33e12b08b834c11dfbafa37c0bddde7af03770ba9dd0ae63714b81dbcadab6c4b53da5ad0b65cb1fd88ac0b5f4af7d77ab835a4abdd5aaacb548a9bd49aa134f8a6dd2fa943484a33d15a8734109f3cf5a78b3b49d1ce1a6d33649a3ccda64b308975cb0a57b2a0947c99a4c325c919c85a3f31d08d9c68a3231688a5c4ba23b10086bc2ea12308c831c14a05300c7f7bf49f9afb07cfbe69efaf6c7a7bc09dfaeec76dba69d12e6c733b8f9c5ae286f9b789bbadb46d7b679b1ad886bbb599a7ad1467bb309932c9462fb13987ac38619b0b9852c2460fb0697fabe05e7af2978abb45d1ae79732b945c7adf96dab5c59fac5960aae8565aae953aa8053da949482a3050fa8393e29ec4f3a7893a29c04dda6a934a9a04cda65930a95c4aba48923a8f4471a3791b28a4443a1d90ca854421a038ffa7f83f39f28f8a7c03d79ea8f4a7943c19dc8e927383879bf8df26f43719b78db26c83619ac8d5a69c34b9a48cd265832998a8c025f02ef9768baa5d02d39658b2258c2bd95a8aca56029b94c8a5a52827f93b89a24c0257927891a47c235910884a4081fb8f687623941c78df86da3441998bc85aa2c414d89c84da26813189784521e80eb87483821bc0db86082e214809b84381ca0b003d80e803a000a7fecc609a954540fbad526098350540f7d9306153164940a7fecc60aaa64540e7f581546aa64d40ff9953609414c140a7fecc64da85c540fbe5816093254540ff9930551a84c540fbd953605824c14097fccb545a960940c7fd956c6aa609409dfdc7aed5258d40ffd1304c58548540efb9544c2aa58940afbecc609a454540cfbd416ceaa6094097fdcb6152164d40ff95414c5a84c940fbe5824c55260540d7f5b96053254540dfb5b24c585505409efdc6aed814c940a7fecc549a864540fbe9824c15260540c7fda9aed814c940efd93054eaa48540b77dc26155364540cff930aeda160940aefdc6aa95260540dfb941aed824c140bf3dc26155350540cfbebb505a360940ef3d54aa95360540ff71305455260540efd93054da1609408ffdc3aeda254540 else 0x940185c001406080500308c0c204e10160241034102020102ad0010602520150030b8002002c3001600080080a8207a0202500080b0407a80c4a061e0008030150ac00202c00c201c08030601c041c007a01a06201002a170000308110200160813e0208000018402d406a00301b0800580404c0010100a03d818980436060142000703100800b0809005840140522d000e00008880b8c1700c623601400c3c010f000780026061500011100900b081202c00202c0e0284018094400e00c201020600618300cc005c0014070160061800209c0005e302702510050148a06c058018602c00c2104080b0606dc00018606c0202703003160204028018423602c00c300a00610084814820c020a20c0583c000a0dd800030c041000540602c2016006100048018400410082700080943c000202e02e01e04106e03e8c3008182e061e04503e0104702a28160409005840105b0401c1c8184160560680d608440308340b404070609030b81840e061d0308828835018ec10018040620d4062025000006024270200300b0c1a05a060140204c000b8184000000000080128a40c09c480c10020183606100000c010d0187400201a02020250120161a0304418040408802429030a03581880340404010001001619828640c36001300081a80b080002030641420c050800002018780e41409060206d0300a0162018080a80586a06100001940f8040b0880f6002b030e818500c36061e05e0111b047248184180a103))
def x511l10 : Packing := (293,5,7,0,0,13,0,x511d10)
def x511h10 (i : Nat) : Nat := 0x301390a0c23717c000e178000618c000f19bc4a400bc27964bc47805641b8034c08a70f844466182b578e81630ab02c000041860440005002820d14d8220000000601a85801a301e0000000c068c0400500000000c5c6070c5450980004144000702b06a40a5c4d919702d21b25d2e00c0000000000000380e0000000101c0000000000e04a05b00034500002041713b0090000000000000000068675096017b040455b03d424013c80ba06781f0002421e10f40c601501d052467240002a1000e10300031610001000308
def x511d9 (i : Nat) : Nat := 0xe0006c001000582b030d8003e000805833030838081001a0610001820e020415030f01420e0084a01a0310000058042300e018800000000000000000f2f839dbcdbe972781b7d7697469a4be551889c05f8ea72b4d82bc5522d0c813e1dcca46208f06e32168a0461e0c8501e0a02803e6cb04a8b26a9302a0497f75ecc549a664d409a7eebd98a92c6cb2819db9c74c2bb549415028f7ba955576c0b26a07ef0609304c55260540dfc8e1262c2a82982819f99c3506bb60930503f61b04a9306a9a82a07ed854981545824c140e3dada302a8d54c9a81aed9c64c2aa54d815026b7ba966326c3ae2a0497f75ecc54aaa65940f9a6a9aa4c1306c8a8186fdb971aaa549815038fe17498302c92a2a06fc64c1c26155350540f78caa261552a6c0a8127bdd4b31936a1715024bfbaf662a555322a061ef711b5aa92164d409b7ceb598c0b249828186fdc6aaabb605935026b7baf662a4cc282a057ec36d30605a454540d71ee32a9552a6c0a8186fdc66a6bb60532503fe1304982a4a9a82a073f2549302e93160940fd8c98304aa2a6c0a812fb8dc4c1a468951503be22a898576a9c22a058ed752aaa221164d409bd2ea598c9c4508a81ff01544c15388a11503f702829826344444a077e04c141aed3188940ef0c982a95daa73328134bdd4b31939de665025f31b8d2260d1aa2a077c24c154aed53889409b1eea598c9cab33281ff013188a5550530503fc12a711260aa4cca04dcd752cc64e5584540
def x511l9 : Packing := (46,6,7,0,0,9,0,x511d9)
def x511h9 (i : Nat) : Nat := 0x1c04100002
def x511d8 (i : Nat) : Nat := 0x28c1af751c6aaabb60593503ae193071954aa95360540
def x511l8 : Packing := (2,7,7,0,0,3,0,x511d8)
def x511samples : Array (Bits × Bits) := #[(0xcca2c34eade6ab34b3780064fbff7ada7f7eef5d6ddbf07c7d7793a358ae86824569a8cb245bfd614264781b1408610514980c39101202205aa084910c803ec0b0002101080818c10807a68d05000322082507db335ad18334940347be21f673,0x881c0070002003108201000900a4aa202280071409017206020e060c1002602202e022048100c0e0581a1000608504180c05141000285a360090057014a0a1222188800a5844882506882621cb22082502c3242941022c9420a224212652),(0x2e1fddaff93c72a2bb56c1db845ce8a8bafdaa27555f4edd5fd7f7b0c174166f114216790abb66c33431a533aec418322106b94401c668903922508030e0fa4240010280004020201082186ca0ae502b30c6241c3180a604c2ff040448c6487f,0xd0241021230710104080283ca2249811408055518800122a804110000020085012d0710f058108112411a545ae2488304080a3c00086608125880040a08961160495120048412021718a3877d01c10090042241413c0a4208242060408c44829),(0x4d0f20d3c64d87f2e476bd21ce89db9fc9a3c163ba96b86f02a1ba0b514792cc345cc465d38a47f6490b9808329ad4020128441aeb40b94e2024100dbb4240188901c00001008100013840b2eab9fb9411803867c00000470518810871078f9c,0xc900110c0a061482208064000c840000530a8000008405402000218101002200000021088088046c10a1028118854030921041acf401b4a007294191f5208489100a4b60100c104001440800803c64621841002840748470818a10071038514),(0xbf3238b47db373dd9e49bcd35f6fa7787abf87c1bfd3ebf1c1a0dd3c7bbab12ef966070cf42d9f742cc464d09801c094ce2890807804e068935148a8a41d012505181558848f000201f05f5200410cd00e03c0600400005805e0f81f01f80fe0,0x4a804004a04241cd00081c0311001a0050443e03480891c001923420f0983f13aa442452422802c446090884180c056889a05309ce001df0c4980e08140860c0a1148e08d000220083502017808101e0180780160201005e0129f80b00ae0),(0x67134edcd3660a6afe82646b852feefcce82bfda50ed7b2ce042698f660063738fa4dbba05eceaeb505285e482be23a2a2d020aa5243430060d184120800010d4040c41195f301f900c7e04101440005c003ff000010005ff000bd4001fff000,0x151053410f04f213200931061b848310455ac930000b504201304050989002640e05090d18ca483f1212856503be0322a14220aa42430f9020c184431a0eab5950d4ce371d7003b941d2c051d08634c5e0827d000216986dd2008d40014ed000),(0xf830d4a3c9d58fbbb855e22d7aa68e45d321fe797165ad137b478c44eddc102c3d71ec392550f8200f16c5a441ad0e281101b65343ce64c28708294b48010081766528063a00413ebe0000801c000005cf78008002f757a008009bcffe000000,0x22e0008090002146300b41088c80c001014a4028202210000410840091b3022110006410808022c40a1684a020ed0c68130192b063c660438148350b5a014043481112663a8101125400201359101414b5100018001286a000009b4dda000000),(0xa9cf6b7b822973b19da6fcf4d8699e6b7a8fe5a9a5603f7317fbae15e4e45bf307f8f5120c71cfc89a5c42a8584b2741a74f1534dff581119a027a0e4020840bc08a02a0537cbf00400000000c4603282000000008182fdff7ff042000000000,0x2041480094c8e340a6791283445100260945000822a54540041806074cc4672700218810c00020449a4c40a0504b2748a74f1c345b718414da577d0e5a0482c9c80a286eb3acd784000400000de1efb030040008043a13df75bd008080000000),(0x96fdb5ce3f7d845d6d6dfdad0e89d66ffefd3746d739bdb18a919462ee1b14daa8d94421c7335e1934e93917cc17ab18845ee100022890243a8c6806630304182e6cc90324004000200800405e54a32dcf7bff67f88c00000800449000000000,0x8103804b27528a8085b4a02213150414220517d145c12322280060c6404c5c828540988d1125011934e12957cc12a314e4de6904002984247e854ac4a02cb6b426ee4909c40202c1a1280040a6ec29a94a6befe57be83000020044b000000000),(0xaece72cbb266d2e436ef4326262b148202f22bdd10bdecc29f883dae99ce7ad2ffa753ed48592ec9e1831b0a072054774c71434a84311da3a5a00360041c0520a2dad16d577cbf3edec3dfec00000440000000000ca908200000443000000000,0xdc00123b221018900104202432000b10403001940948081063254008000000000e40002d000b4d1b41a11b4a071050170830614a840019a820a08270057a3d3032e4c091045228698bf3caeca2020042008000800a8548000a00642000000000)]
def x511columns : List ColumnInfo := [(529,0,494,0,11),(66,0,957,0,11),(132,0,891,0,11),(160,0,863,0,11),(320,0,703,0,11),(536,0,487,0,11),(521,16,486,0,8),(258,64,701,0,8),(6,0,1017,0,9),(4,128,859,32,9),(595,0,428,0,7),(12,0,1011,0,9),(704,0,319,0,11),(14,0,1009,0,7),(780,0,243,0,7),(708,2,312,1,5),(916,8,99,0,4),(668,0,355,0,7),(913,32,78,0,4),(198,0,825,0,7),(164,0,859,0,8),(561,0,462,0,8),(597,2,424,0,4),(268,0,755,0,7),(808,16,198,1,5),(792,0,231,0,8),(856,0,167,0,7),(36,128,859,0,8),(527,16,480,0,4),(537,0,486,0,8),(547,0,476,0,7),(74,4,817,128,5),(322,0,701,0,8),(480,0,543,0,7),(592,0,431,0,11),(533,0,490,0,7),(626,1,396,0,4),(632,256,135,0,4),(808,0,215,0,7),(809,16,198,0,4),(961,32,30,0,4),(690,1,332,0,4),(714,4,305,0,4),(680,256,23,64,5),(852,8,163,0,4),(689,0,334,0,7),(785,0,238,0,7),(697,0,326,0,4),(627,0,396,0,4),(454,0,569,0,4),(658,4,353,8,5),(693,0,330,0,4),(684,0,339,0,5),(543,0,480,0,4),(102,128,793,0,4),(744,256,23,0,4),(924,0,99,0,4),(709,2,312,0,4),(825,0,198,0,4),(482,0,541,0,4),(529,64,172,258,6),(857,0,166,0,4),(841,16,166,0,4),(851,0,172,0,4),(324,0,699,0,7),(858,0,165,0,4),(296,0,727,0,7),(653,16,354,0,4),(334,0,689,0,4),(664,4,353,2,5),(565,128,330,0,4),(484,0,539,0,4),(666,4,353,0,4),(674,0,349,0,7),(787,64,172,0,4),(691,0,332,0,4),(782,64,177,0,4)]
def x511autos : List (List Nat) := [[],[81,130,118],[16,82,131,100],[16,32,48,128,100,80,116],[32,83,116],[32,49,128,81,116,100],[48,33,133,118],[48,129,82],[80,16,33,50,116,131,100],[80,129,50,116],[128,49,100],[128,81,32,49,100,116]]
def x511levels : Nat → Packing
  | 14 => x511l14
  | 13 => x511l13
  | 12 => x511l12
  | 11 => x511l11
  | 10 => x511l10
  | 9 => x511l9
  | 8 => x511l8
  | _ => emptyPacking
def x511index : Nat → Nat → Option (Nat × Nat)
  | 14 => lookupWord 17 53 4 13 5 4 x511h14
  | 13 => lookupWord 101 381 7 16 8 4 x511h13
  | 12 => lookupWord 1115 1507 6 18 10 4 x511h12
  | 11 => lookupWord 227 617 6 17 9 4 x511h11
  | 10 => lookupWord 38 105 4 14 6 4 x511h10
  | 9 => lookupWord 1 5 1 9 1 4 x511h9
  | _ => fun _ => none
def x511 : Forest := ⟨1023,14,fun j => x511samples[j]?.getD (0,0),x511columns,x511autos,x511levels,x511index⟩
set_option maxHeartbeats 0 in
theorem geomx511 : graphValid x511 (boundsBefore knownx351) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_14_0 : block x511 14 0 1=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx511_14 : block x511 14 0 1=true := sx511_14_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_13_0 : block x511 13 0 10=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_13_10 : block x511 13 10 10=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx511_13 : block x511 13 0 20=true := (@block_merge x511 13 0 10 10 sx511_13_0 sx511_13_10)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_12_0 : block x511 12 0 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_12_36 : block x511 12 36 21=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_12_57 : block x511 12 57 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_12_93 : block x511 12 93 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_12_129 : block x511 12 129 32=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_12_161 : block x511 12 161 34=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx511_12 : block x511 12 0 195=true := (@block_merge x511 12 0 161 34 (@block_merge x511 12 0 129 32 (@block_merge x511 12 0 93 36 (@block_merge x511 12 0 57 36 (@block_merge x511 12 0 36 21 sx511_12_0 sx511_12_36) sx511_12_57) sx511_12_93) sx511_12_129) sx511_12_161)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_11_0 : block x511 11 0 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_11_2 : block x511 11 2 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_11_38 : block x511 11 38 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_11_74 : block x511 11 74 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_11_110 : block x511 11 110 19=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_11_129 : block x511 11 129 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_11_165 : block x511 11 165 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_11_201 : block x511 11 201 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_11_237 : block x511 11 237 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_11_273 : block x511 11 273 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_11_309 : block x511 11 309 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_11_345 : block x511 11 345 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_11_381 : block x511 11 381 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_11_417 : block x511 11 417 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_11_453 : block x511 11 453 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_11_489 : block x511 11 489 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_11_525 : block x511 11 525 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_11_561 : block x511 11 561 6=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_11_567 : block x511 11 567 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_11_603 : block x511 11 603 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_11_639 : block x511 11 639 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_11_675 : block x511 11 675 31=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx511_11 : block x511 11 0 706=true := (@block_merge x511 11 0 675 31 (@block_merge x511 11 0 639 36 (@block_merge x511 11 0 603 36 (@block_merge x511 11 0 567 36 (@block_merge x511 11 0 561 6 (@block_merge x511 11 0 525 36 (@block_merge x511 11 0 489 36 (@block_merge x511 11 0 453 36 (@block_merge x511 11 0 417 36 (@block_merge x511 11 0 381 36 (@block_merge x511 11 0 345 36 (@block_merge x511 11 0 309 36 (@block_merge x511 11 0 273 36 (@block_merge x511 11 0 237 36 (@block_merge x511 11 0 201 36 (@block_merge x511 11 0 165 36 (@block_merge x511 11 0 129 36 (@block_merge x511 11 0 110 19 (@block_merge x511 11 0 74 36 (@block_merge x511 11 0 38 36 (@block_merge x511 11 0 2 36 sx511_11_0 sx511_11_2) sx511_11_38) sx511_11_74) sx511_11_110) sx511_11_129) sx511_11_165) sx511_11_201) sx511_11_237) sx511_11_273) sx511_11_309) sx511_11_345) sx511_11_381) sx511_11_417) sx511_11_453) sx511_11_489) sx511_11_525) sx511_11_561) sx511_11_567) sx511_11_603) sx511_11_639) sx511_11_675)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_10_0 : block x511 10 0 7=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_10_7 : block x511 10 7 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_10_43 : block x511 10 43 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_10_79 : block x511 10 79 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_10_115 : block x511 10 115 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_10_151 : block x511 10 151 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_10_187 : block x511 10 187 5=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_10_192 : block x511 10 192 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_10_228 : block x511 10 228 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_10_264 : block x511 10 264 29=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx511_10 : block x511 10 0 293=true := (@block_merge x511 10 0 264 29 (@block_merge x511 10 0 228 36 (@block_merge x511 10 0 192 36 (@block_merge x511 10 0 187 5 (@block_merge x511 10 0 151 36 (@block_merge x511 10 0 115 36 (@block_merge x511 10 0 79 36 (@block_merge x511 10 0 43 36 (@block_merge x511 10 0 7 36 sx511_10_0 sx511_10_7) sx511_10_43) sx511_10_79) sx511_10_115) sx511_10_151) sx511_10_187) sx511_10_192) sx511_10_228) sx511_10_264)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_9_0 : block x511 9 0 14=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_9_14 : block x511 9 14 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx511_9 : block x511 9 0 46=true := (@block_merge x511 9 0 14 32 sx511_9_0 sx511_9_14)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_8_0 : block x511 8 0 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx511_8 : block x511 8 0 2=true := sx511_8_0
theorem tablesx511 : checkedTables x511 14 := by
  intro k hk
  interval_cases k
  · exact (rfl : block x511 0 0 0 = true)
  · exact (rfl : block x511 1 0 0 = true)
  · exact (rfl : block x511 2 0 0 = true)
  · exact (rfl : block x511 3 0 0 = true)
  · exact (rfl : block x511 4 0 0 = true)
  · exact (rfl : block x511 5 0 0 = true)
  · exact (rfl : block x511 6 0 0 = true)
  · exact (rfl : block x511 7 0 0 = true)
  · exact allx511_8
  · exact allx511_9
  · exact allx511_10
  · exact allx511_11
  · exact allx511_12
  · exact allx511_13
  · exact allx511_14
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
  index_root (g:=x511) (i:=0) rfl (before_sound knownx351 validx351) geomx511 tablesx511 (by decide +kernel)
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
theorem cor_head (gs : List Gate) (o : Nat) (w : List Bool) :
    ∃ l, (Circuit.mk gs o).wires w = w ++ l := by
  induction gs generalizing w with
  | nil => exact ⟨[],by simp [Circuit.wires]⟩
  | cons g gs ih =>
    obtain ⟨l,hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    exact ⟨_,hl.trans (List.append_assoc _ _ _)⟩
theorem cor_first (y : Fin 9 → Bool) (gs : List Gate) (o : Nat) :
    (Circuit.mk (Gate.mk GateOp.or [0,4] :: gs) o).wires (List.ofFn y) =
      (Circuit.mk gs o).wires (List.ofFn y ++ [y 0 || y 4]) := by
  have e : GateOp.eval GateOp.or (([0,4] : List Nat).map fun i => (List.ofFn y).getD i false) = (y 0 || y 4) := by
    simp [GateOp.eval,List.ofFn_succ]
  change (Circuit.mk gs o).wires (List.ofFn y ++
    [GateOp.eval GateOp.or (([0,4] : List Nat).map fun i => (List.ofFn y).getD i false)]) = _
  rw [e]
theorem cor_core (gs : List Gate) (o : Nat)
    (legal : PEqualNP.MetaComplexity.FanInTwo (Circuit.mk gs o)) (small : gs.length ≤ 14)
    (h : ∀ y : Fin 9 → Bool, (Circuit.mk gs o).eval (List.ofFn y ++ [y 0 || y 4]) = edge y) : False := by
  have b := bound (Circuit.mk (Gate.mk GateOp.or [0,4] :: gs) o) (by
      intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · simp
      · exact legal g hg) (by
      intro y
      rw [cor_first]
      obtain ⟨l,hl⟩ := cor_head gs o (List.ofFn y ++ [y 0 || y 4])
      rw [hl,List.append_assoc]
      simp [List.getD_eq_getElem?_getD]) (by
      funext y
      change ((Circuit.mk (Gate.mk GateOp.or [0,4] :: gs) o).wires (List.ofFn y)).getD o false = _
      rw [cor_first]
      exact h y)
  have s : (Circuit.mk (Gate.mk GateOp.or [0,4] :: gs) o).size = gs.length+1 := rfl
  omega
theorem cor_mono (gs : List Gate) (o : Nat) (legal : PEqualNP.MetaComplexity.Monotone2 (Circuit.mk gs o))
    (w v : List Bool) (len : w.length = v.length)
    (le : ∀ i, w.getD i false = true → v.getD i false = true) :
    ∀ i, ((Circuit.mk gs o).wires w).getD i false = true → ((Circuit.mk gs o).wires v).getD i false = true := by
  induction gs generalizing w v with
  | nil => exact le
  | cons g gs ih =>
    have lg := (legal g (List.mem_cons_self ..)).1
    refine ih (fun k hk => legal k (List.mem_cons_of_mem _ hk))
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]) (by simp [len]) ?_
    have step : g.op.eval (g.inputs.map fun i => w.getD i false) = true →
        g.op.eval (g.inputs.map fun i => v.getD i false) = true := by
      have lg2 : g.op = GateOp.and ∨ g.op = GateOp.or := by simpa using lg
      rcases lg2 with e | e <;> rw [e]
      · simp only [GateOp.eval,List.all_map,List.all_eq_true,Function.comp,id]
        exact fun q a ha => le a (q a ha)
      · simp only [GateOp.eval,List.any_map,List.any_eq_true,Function.comp,id]
        exact fun ⟨a,ha,q⟩ => ⟨a,ha,le a q⟩
    intro i
    rcases Nat.lt_trichotomy i w.length with h | h | h
    · rw [List.getD_append _ _ _ _ h,List.getD_append _ _ _ _ (len ▸ h)]
      exact le i
    · have hv : i = v.length := by omega
      have e1 : ∀ b : Bool, (w ++ [b]).getD i false = b := by
        intro b; rw [h]; simp [List.getD_eq_getElem?_getD]
      have e2 : ∀ b : Bool, (v ++ [b]).getD i false = b := by
        intro b; rw [hv]; simp [List.getD_eq_getElem?_getD]
      rw [e1,e2]
      exact step
    · rw [List.getD_eq_default _ _ (by simp only [List.length_append,List.length_cons,List.length_nil]; omega)]
      intro q
      cases q
def cor_pts : List Nat := [3,6,12,17,24,33,42,50,66,69,104,116,132,138,160,201,208,261,264,276,288,320,385,402]
def cor_pos : List Nat := [3,6,12,17,24,33,66,132,160,264,288,320]
def cor_bits (n : Nat) : Fin 9 → Bool := fun i => n.testBit i.val
theorem cor_cover_pos : ∀ n : Fin 512, edge (cor_bits n.val) = true → ∃ p ∈ cor_pos, p ∈ cor_pts ∧
    ∀ i : Fin 9, cor_bits p i = true → cor_bits n.val i = true := by decide +kernel
theorem cor_cover_neg : ∀ n : Fin 512, edge (cor_bits n.val) = false → ∃ p ∈ cor_pts, p ∉ cor_pos ∧
    ∀ i : Fin 9, cor_bits n.val i = true → cor_bits p i = true := by decide +kernel
theorem cor_num (y : Fin 9 → Bool) : ∃ n : Fin 512, cor_bits n.val = y :=
  ⟨⟨Nat.ofBits y,Nat.ofBits_lt_two_pow y⟩,by
    funext i
    exact Nat.testBit_ofBits_lt y i.val i.isLt⟩
theorem cor_le (a b : Fin 9 → Bool) (h : ∀ i, a i = true → b i = true) :
    ∀ i, (List.ofFn a ++ [a 0 || a 4]).getD i false = true → (List.ofFn b ++ [b 0 || b 4]).getD i false = true := by
  intro i
  rcases Nat.lt_trichotomy i 9 with q | q | q
  · rw [List.getD_append _ _ _ _ (by simpa using q),List.getD_append _ _ _ _ (by simpa using q)]
    rw [List.getD_eq_getElem?_getD,List.getD_eq_getElem?_getD,List.getElem?_ofFn,List.getElem?_ofFn]
    simp only [q,dite_eq_left,Option.getD_some]
    exact h _
  · subst q
    simp only [List.getD_eq_getElem?_getD,List.length_ofFn,Std.le_refl,List.getElem?_append_right,Nat.sub_self,
      List.length_cons,List.length_nil,Nat.lt_add_one,getElem?_pos,List.getElem_cons_zero,Option.getD_some,Bool.or_eq_true]
    exact fun z => z.imp (h 0) (h 4)
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    intro z
    cases z
theorem cor_mono_core (gs : List Gate) (o : Nat) (legal : PEqualNP.MetaComplexity.Monotone2 (Circuit.mk gs o))
    (small : gs.length ≤ 14)
    (h : ∀ p ∈ cor_pts, (Circuit.mk gs o).eval (List.ofFn (cor_bits p) ++ [cor_bits p 0 || cor_bits p 4]) =
      decide (p ∈ cor_pos)) : False := by
  refine cor_core gs o (fun g hg => ?_) small fun y => ?_
  · have := legal g hg
    refine ⟨?_,this.2⟩
    have q : g.op = GateOp.and ∨ g.op = GateOp.or := by simpa using this.1
    rcases q with q | q <;> simp [q]
  · obtain ⟨n,rfl⟩ := cor_num y
    rcases e : edge (cor_bits n.val) with _ | _
    · obtain ⟨p,hp,np,le⟩ := cor_cover_neg n e
      rw [← Bool.not_eq_true]
      intro q
      have := cor_mono gs o legal _ _ (by simp) (cor_le _ _ le) o q
      have hh := h p hp
      rw [decide_eq_false np] at hh
      exact absurd (this.symm.trans hh) (by simp)
    · obtain ⟨p,pp,hp,le⟩ := cor_cover_pos n e
      have hh := h p hp
      rw [decide_eq_true pp] at hh
      exact cor_mono gs o legal _ _ (by simp) (cor_le _ _ le) o hh
end PEqualNP.Outside.L_meta_4807_aux.Seeded

namespace PEqualNP.Outside.L_meta_4807_aux

theorem parentLower : ∀ (x1 : Fin (9 : ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x2 →     (∀ x4 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (42 : ℕ), (50 : ℕ), (66 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (132 : ℕ), (138 : ℕ), (160 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (264 : ℕ), (276 : ℕ), (288 : ℕ), (320 : ℕ), (385 : ℕ), (402 : ℕ)],         have x6 : Fin (9 : ℕ) → Bool := fun (x6 : Fin (9 : ℕ)) => x4.testBit ↑x6;         x2.eval (List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)), x6 (0 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) || x6 x1]) = Decidable.decide (x4 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ)])) →       (14 : ℕ) ≤ x2.size := by
  intro a D legal h
  by_contra! small
  refine PEqualNP.Outside.L_meta_4807_aux.Seeded.cor_mono_core (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [9,a.val] :: D.gates)
    D.output ?_ ?_ ?_
  · intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · simp
    · exact legal g hg
  · simp only [PEqualNP.CircuitLowerBounds.Circuit.size] at small
    simp only [List.length_cons]
    omega
  · intro p hp
    refine Eq.trans ?_ (h p hp)
    refine congrArg (fun w : List Bool => D.eval w) ?_
    rw [List.append_cons (List.ofFn _) _ [_]]
    refine congrArg (fun b => _ ++ [b]) ?_
    fin_cases a <;> simp [PEqualNP.CircuitLowerBounds.GateOp.eval,List.ofFn_succ,PEqualNP.Outside.L_meta_4807_aux.Seeded.cor_bits]

end PEqualNP.Outside.L_meta_4807_aux


namespace PEqualNP.Outside.L_meta_4807_aux

namespace Decode4807
variable (rows : List Nat) (truth : Nat → Bool)
open PEqualNP.Defs.LratEncoding
def lit (k j t : Nat) (b : Bool) := 2*(((k*14+j)*2073+t)+1) + if b then 0 else 1
def num (a : Nat → Bool) (k j t : Nat) := a (((k*14+j)*2073+t)+1)

structure Present (f : List (List Nat)) : Prop where
  opcode : ∀ j < 13, (List.range 3).map (fun k => lit 0 j k true) ∈ f
  input : ∀ e ∈ [1,2], ∀ j < 13, (List.range (11+j+1)).map (fun i => lit e j i true) ∈ f
  raw : ∀ e ∈ [1,2], ∀ j < 13, ∀ r ∈ rows, ∀ i < 11, [lit e j i false,lit (e+3) j r (r.testBit i)] ∈ f
  prev : ∀ e ∈ [1,2], ∀ j < 13, ∀ r ∈ rows, ∀ t < j,
    [lit e j (11+t) false,lit (e+3) j r false,lit 3 t r true] ∈ f ∧
    [lit e j (11+t) false,lit (e+3) j r true,lit 3 t r false] ∈ f
  zero : ∀ e ∈ [1,2], ∀ j < 13, ∀ r ∈ rows, [lit e j (11+j) false,lit (e+3) j r false] ∈ f
  gates : ∀ j < 13, ∀ r ∈ rows, ∀ c ∈ [
    [lit 0 j 0 false,lit 3 j r false,lit 4 j r true], [lit 0 j 0 false,lit 3 j r false,lit 5 j r true],
    [lit 0 j 0 false,lit 3 j r true,lit 4 j r false,lit 5 j r false],
    [lit 0 j 1 false,lit 3 j r true,lit 4 j r false], [lit 0 j 1 false,lit 3 j r true,lit 5 j r false],
    [lit 0 j 1 false,lit 3 j r false,lit 4 j r true,lit 5 j r true],
    [lit 0 j 2 false,lit 3 j r true]], c ∈ f
  output : (List.range 25).map (fun i => lit 6 0 i true) ∈ f
  outRaw : ∀ r ∈ rows, ∀ i < 11, r.testBit i ≠ truth r → [lit 6 0 i false] ∈ f
  outPrev : ∀ r ∈ rows, ∀ t < 13, [lit 6 0 (11+t) false,lit 3 t r (truth r)] ∈ f
  outZero : ∀ r ∈ rows, truth r = true → [lit 6 0 24 false] ∈ f
end Decode4807

namespace Decode4807
variable (rows : List Nat) (truth : Nat → Bool)
open PEqualNP.Defs.LratEncoding

private theorem addrPos (k j t : Nat) : P (ix 11 13 k j t) = lit k j t true := by
  simp [P,ix,wd,lit]
  omega

private theorem addrNeg (k j t : Nat) : Q (ix 11 13 k j t) = lit k j t false := by
  simp [Q,ix,wd,lit]
  omega

private theorem addrBit (k j t : Nat) (b : Bool) :
    L (ix 11 13 k j t) b = lit k j t b := by
  cases b
  · exact addrNeg ..
  · exact addrPos ..

private theorem containsBlocks (a b c d e f g h i j k l : List (List Nat)) :
    let z := a ++ b ++ c ++ d ++ e ++ f ++ g ++ h ++ i ++ j ++ k ++ l
    (∀ {x}, x ∈ a → x ∈ z) ∧ (∀ {x}, x ∈ b → x ∈ z) ∧
    (∀ {x}, x ∈ c → x ∈ z) ∧ (∀ {x}, x ∈ d → x ∈ z) ∧
    (∀ {x}, x ∈ e → x ∈ z) ∧ (∀ {x}, x ∈ f → x ∈ z) := by
  dsimp only
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  all_goals intro x hx; simp only [List.mem_append]; tauto

theorem present_enc : Present rows truth (enc 11 13 truth rows) := by
  let F := enc 11 13 truth rows
  have included :
      (∀ {c}, c ∈ fOp 11 13 → c ∈ F) ∧
      (∀ {c}, c ∈ fSrcAlo 11 13 → c ∈ F) ∧
      (∀ {c}, c ∈ fSrcEq 11 13 rows → c ∈ F) ∧
      (∀ {c}, c ∈ fGate 11 13 rows → c ∈ F) ∧
      (∀ {c}, c ∈ fOutAlo 11 13 → c ∈ F) ∧
      (∀ {c}, c ∈ fOutEq 11 13 truth rows → c ∈ F) := by
    exact containsBlocks _ _ _ _ _ _ _ _ _ _ _ _
  obtain ⟨opBlock,choiceBlock,srcBlock,gateBlock,outBlock,outEqBlock⟩ := included
  have source {e j r i : Nat} {c : List Nat} (he : e ∈ [1,2]) (hj : j < 13)
      (hr : r ∈ rows) (hi : i < 11+j+1) (hc : c ∈ srcEq 11 13 e j i r) : c ∈ F := by
    apply srcBlock
    unfold fSrcEq
    exact List.mem_flatMap.mpr ⟨e,he,List.mem_flatMap.mpr ⟨j,List.mem_range.mpr hj,
      List.mem_flatMap.mpr ⟨r,hr,List.mem_flatMap.mpr ⟨i,List.mem_range.mpr hi,hc⟩⟩⟩⟩
  have lastSource {r i : Nat} {c : List Nat} (hr : r ∈ rows) (hi : i < 25)
      (hc : c ∈ outEq 11 13 truth i r) : c ∈ F := by
    apply outEqBlock
    unfold fOutEq
    exact List.mem_flatMap.mpr ⟨r,hr,List.mem_flatMap.mpr ⟨i,List.mem_range.mpr hi,hc⟩⟩
  constructor
  · intro j hj
    apply opBlock
    unfold fOp
    refine List.mem_map.mpr ⟨j,List.mem_range.mpr hj,?_⟩
    have aligned : [P (ix 11 13 0 j 0),P (ix 11 13 0 j 1),P (ix 11 13 0 j 2)] =
        (List.range 3).map (fun k => lit 0 j k true) := by
      simp only [addrPos]
      rfl
    exact aligned
  · intro e he j hj
    apply choiceBlock
    unfold fSrcAlo
    refine List.mem_flatMap.mpr ⟨e,he,List.mem_map.mpr ⟨j,List.mem_range.mpr hj,?_⟩⟩
    simp only [addrPos]
  · intro e he j hj r hr i hi
    apply source (i := i) he hj hr (by omega)
    simp [srcEq,hi,addrNeg,addrBit]
  · intro e he j hj r hr t ht
    have above : ¬ 11+t < 11 := by omega
    have below : 11+t < 11+j := by omega
    constructor <;> apply source (i := 11+t) he hj hr (by omega) <;>
      simp [srcEq,above,below,addrNeg,addrPos]
  · intro e he j hj r hr
    apply source (i := 11+j) he hj hr (by omega)
    have above : ¬ 11+j < 11 := by omega
    simp [srcEq,above,addrNeg]
  · intro j hj r hr c hc
    apply gateBlock
    unfold fGate
    refine List.mem_flatMap.mpr ⟨j,List.mem_range.mpr hj,List.mem_flatMap.mpr ⟨r,hr,?_⟩⟩
    simpa only [gateCl,addrNeg,addrPos] using hc
  · apply outBlock
    simp [fOutAlo,addrPos]
  · intro r hr i hi mismatch
    apply lastSource (i := i) hr (by omega)
    simp [outEq,hi,mismatch,addrNeg]
  · intro r hr t ht
    apply lastSource (i := 11+t) hr (by omega)
    have above : ¬ 11+t < 11 := by omega
    have below : 11+t < 11+13 := by omega
    simp [outEq,above,below,addrNeg,addrBit]
  · intro r hr hit
    apply lastSource (i := 24) hr (by decide)
    simp [outEq,hit,addrNeg]
end Decode4807

namespace Decode4807
variable (rows : List Nat) (truth : Nat → Bool)
open PEqualNP.Defs.LratEncoding

private theorem litEval (a) (k j t) (b : Bool) :
    litVal a (lit k j t b) = if b then num a k j t else !(num a k j t) := by
  let u := ((k*14+j)*2073+t)+1
  unfold litVal
  cases b
  · change _ = !(a u)
    have form : lit k j t false = 2*u+1 := rfl
    have rem : (2*u+1)%2 = 1 := by omega
    have div : (2*u+1)/2 = u := by omega
    rw [form,rem,div]
    cases a u <;> rfl
  · change _ = a u
    have form : lit k j t true = 2*u+0 := rfl
    have rem : (2*u+0)%2 = 0 := by omega
    have div : (2*u+0)/2 = u := by omega
    rw [form,rem,div]
    cases a u <;> rfl

private theorem satCons (a : Nat → Bool) (k j t) (b : Bool) (cs : List Nat) :
    ClauseSat a (lit k j t b :: cs) ↔ num a k j t = b ∨ ClauseSat a cs := by
  unfold ClauseSat
  simp only [List.mem_cons,exists_eq_or_imp,litEval]
  cases b <;> simp

def valIn (a : Nat → Bool) (j i r : Nat) : Bool :=
  if i<11 then r.testBit i else if i < 11+j then num a 3 (i-11) r else false

structure Meaning (a : Nat → Bool) : Prop where
  op : ∀ j<13, ∃ k<3, num a 0 j k = true
  input : ∀ e∈[1,2], ∀ j<13, ∃ i<11+j+1, num a e j i = true
  side : ∀ e∈[1,2], ∀ j<13, ∀ i<11+j+1, num a e j i = true →
    ∀ r∈rows, num a (e+3) j r = valIn a j i r
  eval : ∀ j<13, ∀ k<3, num a 0 j k = true → ∀ r∈rows, num a 3 j r =
    if k=0 then num a 4 j r && num a 5 j r else if k=1 then num a 4 j r || num a 5 j r else true
  out : ∃ i<25, ∀ r∈rows, valIn a 13 i r = truth r

theorem meaning {f} (covers : Present rows truth f) {a : Nat → Bool} (sat : ∀ c ∈ f, ClauseSat a c) : Meaning rows truth a := by
  have al (k j bound) (mem : (List.range bound).map (fun i => lit k j i true) ∈ f) :
      ∃ i<bound, num a k j i = true := by
    obtain ⟨v,hv,hon⟩ := sat _ mem
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hv
    exact ⟨i,List.mem_range.mp hi,by simpa [litEval] using hon⟩
  have nil : ¬ ClauseSat a [] := by simp [ClauseSat]
  constructor
  · exact fun j hj => al _ _ _ (covers.opcode j hj)
  · exact fun e eh j jh => al _ _ _ (covers.input e eh j jh)
  · intro e eh j jh i ih sel r rh
    by_cases raw : i<11
    · have h := sat _ (covers.raw e eh j jh r rh i raw)
      simpa [satCons,sel,nil,valIn,raw] using h
    · by_cases prev : i < 11+j
      · obtain ⟨u,eu⟩ : ∃ u, i=11+u := ⟨i-11,by omega⟩
        subst i
        obtain ⟨hp,hq⟩ := covers.prev e eh j jh r rh u (by omega)
        have a₁ := sat _ hp; have a₂ := sat _ hq
        simp [satCons,nil,sel] at a₁ a₂
        simp [valIn,raw,prev]
        grind
      · have iis : i=11+j := by omega
        subst i
        have h := sat _ (covers.zero e eh j jh r rh)
        simpa [satCons,nil,sel,valIn,raw,prev] using h
  · intro j jh k kh selected r rh
    have g := covers.gates j jh r rh
    simp only [List.mem_cons,List.mem_nil_iff,or_false,forall_eq_or_imp] at g
    obtain ⟨g0,g1,g2,g3,g4,g5,g6⟩ := g
    have h0 := sat _ g0; have h1 := sat _ g1; have h2 := sat _ g2
    have h3 := sat _ g3; have h4 := sat _ g4; have h5 := sat _ g5; have h6 := sat _ (g6 _ rfl)
    interval_cases k <;> simp [satCons,nil,selected] at * <;> grind
  · obtain ⟨i,ih,sel⟩ := al _ _ _ covers.output
    use i,ih
    intro r rh
    by_cases raw : i<11
    · simp only [valIn,raw,↓reduceIte]
      by_contra diff
      have h := sat _ (covers.outRaw r rh i raw diff)
      simp [satCons,nil,sel] at h
    · by_cases prev : i<24
      · obtain ⟨u,eu⟩ : ∃ u, i=11+u := ⟨i-11,by omega⟩
        subst i
        have h := sat _ (covers.outPrev r rh u (by omega))
        simpa [satCons,nil,sel,valIn,raw,show 11+u<11+13 by omega] using h
      · have iis : i=24 := by omega
        subst i
        cases tr : truth r
        · rfl
        · have h := sat _ (covers.outZero r rh tr)
          simp [satCons,nil,sel] at h
end Decode4807


end PEqualNP.Outside.L_meta_4807_aux
namespace PEqualNP.Outside.L_meta_4807_aux.Decode4807
open PEqualNP.Defs.LratEncoding

theorem sat_model (rows : List Nat) (truth : Nat → Bool) (cube : Nat)
    (sat : FormulaSat (enc2 11 13 truth rows ++ enc2Cube 11 13 cube)) :
    ∃ a : Nat → Bool, Meaning rows truth a := by
  obtain ⟨a,valid⟩ := sat
  refine ⟨a, meaning rows truth (present_enc rows truth) ?_⟩
  intro c hc
  exact valid c (List.mem_append_left _ (List.mem_append_left _ hc))

theorem semantic {rows : List Nat} {truth : Nat → Bool} {a : Nat → Bool}
    (h : Meaning rows truth a) :
    (∀ j < 13, ∃ k < 3, ∃ p q : Nat, ∀ r ∈ rows, num a 3 j r =
      if k = 0 then valIn a j p r && valIn a j q r
      else if k = 1 then valIn a j p r || valIn a j q r else true) ∧
    ∃ o : Nat, ∀ r ∈ rows, valIn a 13 o r = truth r := by
  constructor
  · intro j hj
    obtain ⟨k,hk,op⟩ := h.op j hj
    obtain ⟨p,hp,px⟩ := h.input 1 (by decide) j hj
    obtain ⟨q,hq,qx⟩ := h.input 2 (by decide) j hj
    refine ⟨k,hk,p,q,?_⟩
    intro r hr
    rw [h.eval j hj k hk op r hr]
    have left := h.side 1 (by decide) j hj p hp px r hr
    have right := h.side 2 (by decide) j hj q hq qx r hr
    change num a 4 j r = _ at left
    change num a 5 j r = _ at right
    rw [left,right]
  · obtain ⟨o,_,answer⟩ := h.out
    exact ⟨o,answer⟩
end PEqualNP.Outside.L_meta_4807_aux.Decode4807

namespace PEqualNP.Outside.L_meta_4807_aux.CircuitDecode
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def read (n : ℕ) (v : ℕ → ℕ → Bool) (j i r : ℕ) :=
  if i < n then r.testBit i else if i < n+j then v (i-n) r else false

def makeGate (k a b : ℕ) : Gate :=
  if k=0 then ⟨.and,[a,b]⟩ else if k=1 then ⟨.or,[a,b]⟩ else ⟨.and,[]⟩

private def wires (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

private lemma nextWires (gs : List Gate) (g : Gate) (x : List Bool) :
    wires (gs++[g]) x = wires gs x ++ [g.op.eval (g.inputs.map fun i => (wires gs x).getD i false)] := by
  simp [wires,List.foldl_append]

private lemma wireCount (gs : List Gate) (x : List Bool) : (wires gs x).length = x.length+gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [wires]
  | append_singleton gs g ih => rw [nextWires]; simp [ih]; omega

private lemma readAppend (w : List Bool) (b : Bool) (i : ℕ) :
    (w++[b]).getD i false = if i=w.length then b else w.getD i false := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases h : i < w.length
  · simp [List.getElem?_append_left h,Nat.ne_of_lt h]
  · rw [List.getElem?_append_right (by omega),List.getElem?_eq_none (by omega : w.length ≤ i)]
    by_cases eq : i=w.length
    · simp [eq]
    · simp [eq,show i-w.length ≠ 0 by omega]

private lemma update (n : ℕ) (v : ℕ → ℕ → Bool) (j i r : ℕ) :
    read n v (j+1) i r = if i=n+j then v j r else read n v j i r := by
  by_cases h : i < n
  · simp [read,h,show i ≠ n+j by omega]
  by_cases e : i=n+j
  · subst i; simp [read]
  by_cases b : i < n+j
  · simp [read,h,e,b,show i < n+(j+1) by omega]
  · simp [read,h,e,b,show ¬i < n+(j+1) by omega]

theorem circuitOfRows (n s : ℕ) (rows : List ℕ) (target : ℕ → Bool) (v : ℕ → ℕ → Bool)
    (gates : ∀ j < s, ∃ k < 3, ∃ a b : ℕ, ∀ r ∈ rows, v j r =
        if k=0 then read n v j a r && read n v j b r
        else if k=1 then read n v j a r || read n v j b r else true)
    (output : ∃ o, ∀ r ∈ rows, read n v s o r = target r) :
    ∃ C : Circuit, Monotone2 C ∧ C.size = s ∧
      ∀ r ∈ rows, C.eval (List.ofFn fun i : Fin n => r.testBit i.val) = target r := by
  let input (r : ℕ) := List.ofFn fun i : Fin n => r.testBit i.val
  have buildPrefix (j : ℕ) (hj : j ≤ s) : ∃ gs : List Gate,
      gs.length = j ∧ Monotone2 ⟨gs,0⟩ ∧ ∀ r ∈ rows, ∀ i,
        (wires gs (input r)).getD i false = read n v j i r := by
    induction j with
    | zero =>
      refine ⟨[],rfl,by intro g hg; simp at hg,?_⟩
      intro r hr i
      by_cases h : i < n <;> simp [wires,input,read,List.getD_eq_getElem?_getD,h]
    | succ j ih =>
      obtain ⟨gs,len,mono,agree⟩ := ih (by omega)
      obtain ⟨k,_,a,b,eval⟩ := gates j (by omega)
      let g := makeGate k a b
      have ok : g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
        unfold g makeGate; split <;> (try split) <;> simp
      refine ⟨gs++[g], by simp [len], ?_, ?_⟩
      · intro u hu
        rcases List.mem_append.mp hu with h|h
        · exact mono u h
        · simpa only [List.mem_singleton.mp h] using ok
      · intro r hr i
        have value : g.op.eval (g.inputs.map fun u => (wires gs (input r)).getD u false) = v j r := by
          have hv := agree r hr
          simp only [List.getD_eq_getElem?_getD] at hv
          rw [eval r hr]
          unfold g makeGate
          split <;> (try split) <;> simp [GateOp.eval,hv]
        rw [nextWires,readAppend,wireCount,value,agree r hr i,update,len]
        simp [input]
  obtain ⟨gs,len,mono,agree⟩ := buildPrefix s (by rfl)
  obtain ⟨o,ho⟩ := output
  exact ⟨⟨gs,o⟩,mono,len,fun r hr => (agree r hr o).trans (ho r hr)⟩

end PEqualNP.Outside.L_meta_4807_aux.CircuitDecode
namespace PEqualNP.Outside.L_meta_4807_aux

def rows : List Nat := [3,6,12,17,24,33,42,50,66,69,104,116,132,138,160,201,208,261,264,276,288,320,385,402]
def positives : List Nat := [3,6,12,17,24,33,66,132,160,264,288,320]
def expanded (a : Fin 9) (r : Nat) : Nat :=
  let b := r.testBit 0 || r.testBit 4
  r + 512 * b.toNat + 1024 * (b || r.testBit a.val).toNat
def rawBits (r : Nat) (i : Fin 9) := r.testBit i.val
theorem expanded_rows : ∀ a : Fin 9, ∀ r ∈ rows,
    List.ofFn (fun i : Fin 11 => (expanded a r).testBit i.val) =
      List.ofFn (rawBits r) ++ [rawBits r 0 || rawBits r 4, rawBits r 0 || rawBits r 4 || rawBits r a] ∧
    positives.contains (expanded a r % 512) = decide (r ∈ positives) := by decide +kernel
end PEqualNP.Outside.L_meta_4807_aux
open PEqualNP.Outside.L_meta_4807_aux in
theorem PEqualNP.Outside.L_meta_4807 : ∀ (x1 : Fin (9 : ℕ)),   ∀ x2 < PEqualNP.Defs.LratEncoding.enc2CubeCount (11 : ℕ) (13 : ℕ),     have x4 : List ℕ := [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (42 : ℕ), (50 : ℕ), (66 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (132 : ℕ), (138 : ℕ), (160 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (264 : ℕ), (276 : ℕ), (288 : ℕ), (320 : ℕ), (385 : ℕ), (402 : ℕ)];     have x5 : List ℕ := [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ)];     have x6 : ℕ → ℕ := fun (x6 : ℕ) =>       have x7 : Bool := x6.testBit (0 : ℕ) || x6.testBit (4 : ℕ);       x6 + (512 : ℕ) * x7.toNat + (1024 : ℕ) * (x7 || x6.testBit ↑x1).toNat;     ¬PEqualNP.Defs.LratEncoding.FormulaSat (PEqualNP.Defs.LratEncoding.enc2 (11 : ℕ) (13 : ℕ) (fun (x7 : ℕ) => x5.contains (x7 % (512 : ℕ))) (List.map x6 x4) ++ PEqualNP.Defs.LratEncoding.enc2Cube (11 : ℕ) (13 : ℕ) x2) := by

  intro a cube _
  let label := fun r : Nat => positives.contains (r % 512)
  let data := rows.map (expanded a)
  change ¬ PEqualNP.Defs.LratEncoding.FormulaSat
    (PEqualNP.Defs.LratEncoding.enc2 11 13 label data ++ PEqualNP.Defs.LratEncoding.enc2Cube 11 13 cube)
  intro sat
  obtain ⟨asn,sem⟩ := Decode4807.sat_model data label cube sat
  obtain ⟨steps,last⟩ := Decode4807.semantic sem
  obtain ⟨C,monotone,sz,correct⟩ :=
    CircuitDecode.circuitOfRows 11 13 data label (Decode4807.num asn 3) steps last
  have large := parentLower a C monotone (by
    intro r hr
    have tested := correct (expanded a r) (List.mem_map_of_mem hr)
    obtain ⟨inp,output⟩ := expanded_rows a r hr
    change C.eval (List.ofFn fun i : Fin 11 => (expanded a r).testBit i.val) =
      positives.contains (expanded a r % 512) at tested
    rw [inp,output] at tested
    exact tested)
  omega
