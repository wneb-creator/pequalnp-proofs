import PEqualNP.Defs

-- Adapted from the L-meta-4570 certificate by leoli001031-blip, in project pull request 10361.
-- The additional partner 6 supplies a second copy of an existing input. Its set of available
-- signals is contained in that for partner 1, so the same circuit lower bound applies.
-- The truth-table verifier is adapted from L_meta_1667 and L_meta_3640.
-- The signed subgraph certificate uses the vertex-deletion argument from L_meta_1665.
namespace PEqualNP.Outside.L_meta_3394
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
def seed : Sig := neg (inputs.getD 0 zero)

def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem seed_table : ∀ r : Row, bit r seed = !(sample r 0) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
theorem sampled (r : Row) : List.ofFn (sample r) = inputs.map (bit r) := by
  rw [←input_list]
  rw [List.map_ofFn]
  rfl

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
set_option maxHeartbeats 0 in
theorem geom15 : graphValid g15 (boundsBefore []) = true := by
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
  lower_forest (g:=g15) (i:=0) (hints:=8449) (before_sound [] baseKnown) geom15 tables15 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps15 : List (Nat × List Nat) := [(15,[]),(23,[32,67]),(27,[16,66]),(29,[65,50]),(30,[64,65,66,67]),(39,[32,67,84]),(57,[32,65,82,83]),(78,[64,33,67,84,101]),(99,[16,33,66,83,100,101]),(135,[67,84,101,118]),(156,[64,81,83,101,118]),(163,[16,66,83,100,101,118]),(165,[65,50,83,100,101,118]),(166,[64,65,66,83,100,118]),(172,[64,81,82,67,100,101,118]),(177,[16,65,82,99,118]),(305,[16,65,82,99,118,135]),(312,[64,81,98,83,118,135]),(326,[64,66,83,100,117,135]),(332,[64,81,66,83,100,117,118,135]),(344,[64,81,98,83,117,118,135]),(353,[65,82,99,116,117,135]),(354,[64,65,82,99,116,101,118,135])]
def known15 := extendKnown [] 4 maps15
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid15 : Known known15 := extendKnown_ok (m:=15) baseKnown low15 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom31 : graphValid g31 (boundsBefore known15) = true := by
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
  lower_forest (g:=g31) (i:=0) (hints:=8449) (before_sound known15 valid15) geom31 tables31 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps31 : List (Nat × List Nat) := [(31,[]),(167,[83,100,101,118]),(313,[81,98,99,84,118,135]),(334,[80,81,82,83,100,117,135]),(355,[82,99,116,117,118,135])]
def known31 := extendKnown known15 7 maps31
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid31 : Known known31 := extendKnown_ok (m:=31) valid15 low31 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low47 : Lower (vars 47) (graphGoal 47) 5 :=
  lower_discard (g:=g47) (ci:=(8,0,39,0,4)) (hints:=8449) (before_sound known31 valid31) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps47 : List (Nat × List Nat) := [(47,[]),(61,[65,50]),(94,[64,65,66,67,101]),(151,[67,84,101,118]),(173,[48,65,50,83,100,118]),(181,[65,50,99,84,118]),(185,[16,65,98,83,101,118]),(188,[64,97,98,67,84,118]),(339,[66,99,84,117,118,135]),(358,[64,65,82,99,116,101,118,135]),(369,[65,98,115,84,118,135])]
def known47 := extendKnown known31 5 maps47
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid47 : Known known47 := extendKnown_ok (m:=47) valid31 low47 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low55 : Lower (vars 55) (graphGoal 55) 5 :=
  lower_discard (g:=g55) (ci:=(16,0,39,0,4)) (hints:=257) (before_sound known47 valid47) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps55 : List (Nat × List Nat) := [(55,[]),(79,[64,65,66,67,101]),(103,[16,66,100,101]),(115,[50,99]),(143,[32,67,101,118]),(179,[65,50,99,84,118]),(316,[48,97,66,84,118,135]),(327,[64,65,82,100,117,135]),(348,[48,97,66,84,117,118,135]),(364,[48,97,99,116,118,135]),(376,[48,97,114,99,116,118,135])]
def known55 := extendKnown known47 5 maps55
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid55 : Known known55 := extendKnown_ok (m:=55) valid47 low55 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low63 : Lower (vars 63) (graphGoal 63) 8 :=
  lower_discard (g:=g63) (ci:=(32,0,31,0,7)) (hints:=8449) (before_sound known55 valid55) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps63 : List (Nat × List Nat) := [(63,[]),(95,[16,66,101]),(159,[32,67,101,118]),(175,[32,83,100,118]),(183,[99,84,118]),(317,[32,97,82,83,100,118,135]),(350,[96,33,99,84,117,135]),(359,[16,82,99,116,118,135]),(366,[96,49,116,118,135]),(371,[98,115,84,135])]
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
def maps111 : List (Nat × List Nat) := [(187,[16,97,66,83,100,101,118]),(190,[64,97,98,67,84,118]),(318,[64,81,66,83,100,118,135]),(349,[80,65,98,67,84,117,118,135]),(365,[48,65,82,116,135]),(378,[64,49,114,67,84,101,118,135])]
def known111 := extendKnown known63 7 maps111
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid111 : Known known111 := extendKnown_ok (m:=111) valid63 low111 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low119 : Lower (vars 119) (graphGoal 119) 6 :=
  lower_discard (g:=g119) (ci:=(4,0,115,0,5)) (hints:=16777473) (before_sound known111 valid111) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps119 : List (Nat × List Nat) := [(119,[]),(380,[48,113,66,84,101,135])]
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
def maps189 : List (Nat × List Nat) := [(189,[])]
def known189 := extendKnown known119 8 maps189
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid189 : Known known189 := extendKnown_ok (m:=189) valid119 low189 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low127 : Lower (vars 127) (graphGoal 127) 9 :=
  lower_discard (g:=g127) (ci:=(32,0,95,0,8)) (hints:=16785665) (before_sound known189 valid189) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps127 : List (Nat × List Nat) := [(127,[]),(375,[98,115,84,135]),(381,[48,113,82,135]),(382,[112,49,66,115,84,101,135])]
def known127 := extendKnown known189 9 maps127
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid127 : Known known127 := extendKnown_ok (m:=127) valid189 low127 (by decide +kernel)
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
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
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
def maps191 : List (Nat × List Nat) := [(191,[]),(319,[65,50,135]),(351,[64,65,66,67,101,135]),(367,[80,81,66,100,117,118,135]),(379,[81,98,118,135])]
def known191 := extendKnown known127 11 maps191
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid191 : Known known191 := extendKnown_ok (m:=191) valid127 low191 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom383 : graphValid g383 (boundsBefore known191) = true := by
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
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
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
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_1 : block g383 9 9 75=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
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
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
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
  lower_forest (g:=g383) (i:=0) (hints:=12901687553) (before_sound known191 valid191) geom383 tables383 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps383 : List (Nat × List Nat) := [(383,[])]
def known383 := extendKnown known191 13 maps383
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid383 : Known known383 := extendKnown_ok (m:=383) valid191 low383 (by decide +kernel)
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
def rootC (m : Nat) : List Sig := (vars m).tail ++ [seed]
def headSig : Sig := inputs.getD 0 zero

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

def splitOK (m hints nb : Nat) : Bool :=
  let xs := (graphPairs m hints).tail
  checkEssential (graphGoal m) (rootB m) xs && (xs.map Prod.fst == (vars m).tail) &&
    (vars m == headSig :: (vars m).tail) && properB (graphGoal m) &&
    (bit (Fin.ofNat 512 (1 <<< nb)) (graphGoal m) != bit (Fin.ofNat 512 (1+(1 <<< nb))) (graphGoal m)) &&
    (rootB m).all (fun w => w == headSig || w == seed ||
      bit (Fin.ofNat 512 (1 <<< nb)) w == bit (Fin.ofNat 512 (1+(1 <<< nb))) w)

theorem strong_split {m hints nb : Nat} (ok : splitOK m hints nb = true) {k t : Nat} {S : Finset Sig}
    (h : Live (graphGoal m) k t S) (sub : ∀ v ∈ S, v ∈ rootB m) :
    S=(vars m).toFinset ∨ S=(rootB m).toFinset ∨ S=(rootC m).toFinset := by
  simp only [splitOK,Bool.and_eq_true,beq_iff_eq] at ok
  obtain ⟨⟨⟨⟨⟨ess,alls⟩,hd⟩,_⟩,diff⟩,iso⟩ := ok
  have rest : ∀ v ∈ (vars m).tail, v ∈ S := by
    intro v hv
    rw [←alls] at hv
    obtain ⟨r,s,hd,hi⟩ := essential_ok ess v (List.mem_toFinset.mpr hv)
    exact raw_required h (rootB m) v sub r s hd hi
  have mem : ∀ v, v ∈ rootB m ↔ v=headSig ∨ v ∈ (vars m).tail ∨ v=seed := by
    intro v
    have e : rootB m = headSig :: (vars m).tail ++ [seed] := congrArg (· ++ [seed]) hd
    rw [e]
    simp
  have memA : ∀ v, v ∈ vars m ↔ v=headSig ∨ v ∈ (vars m).tail := by
    intro v
    rw [hd]
    simp
  have memC : ∀ v, v ∈ rootC m ↔ v ∈ (vars m).tail ∨ v=seed := by
    intro v
    simp [rootC]
  have one : headSig ∈ S ∨ seed ∈ S := by
    obtain ⟨v,hv,hd⟩ := live_row_difference h (bne_iff_ne.mp diff)
    have hc := List.all_eq_true.mp iso v (sub v hv)
    simp only [Bool.or_eq_true,beq_iff_eq] at hc
    rcases hc with (rfl | rfl) | hc
    · exact Or.inl hv
    · exact Or.inr hv
    · exact False.elim (hd hc)
  by_cases hs : seed ∈ S
  · by_cases hh : headSig ∈ S
    · refine Or.inr (Or.inl ?_)
      ext v
      rw [List.mem_toFinset]
      refine ⟨sub v,fun hv => ?_⟩
      rcases (mem v).mp hv with rfl | hv | rfl
      · exact hh
      · exact rest v hv
      · exact hs
    · refine Or.inr (Or.inr ?_)
      ext v
      rw [List.mem_toFinset,memC]
      constructor
      · intro hv
        rcases (mem v).mp (sub v hv) with rfl | hv | rfl
        · exact False.elim (hh hv)
        · exact Or.inl hv
        · exact Or.inr rfl
      · rintro (hv | rfl)
        · exact rest v hv
        · exact hs
  · have hh := one.resolve_right hs
    refine Or.inl ?_
    ext v
    rw [List.mem_toFinset,memA]
    constructor
    · intro hv
      rcases (mem v).mp (sub v hv) with rfl | hv | rfl
      · exact Or.inl rfl
      · exact Or.inr hv
      · exact False.elim (hs hv)
    · rintro (rfl | hv)
      · exact hh
      · exact rest v hv

theorem strong_low {m hints nb cap : Nat} (ok : splitOK m hints nb = true)
    (a : Impossible (graphGoal m) cap (vars m).toFinset)
    (b : Impossible (graphGoal m) cap (rootB m).toFinset)
    (c : Impossible (graphGoal m) cap (rootC m).toFinset) :
    Lower (rootB m) (graphGoal m) (cap+1) := by
  have ok' := ok
  simp only [splitOK,Bool.and_eq_true,beq_iff_eq] at ok'
  intro p bank hr ha
  obtain ⟨k,t,S,hk,run,hs⟩ := reach_live (proper_of _ ok'.1.1.2) hr ha
  by_contra! small
  rcases strong_split ok run hs with e | e | e
  · exact a k t (by omega) (e ▸ run)
  · exact b k t (by omega) (e ▸ run)
  · exact c k t (by omega) (e ▸ run)

def x15d3 (i : Nat) : Nat := 0x7a00
def x15l3 : Packing := (1,1,1,0,0,0,0,x15d3)
def x15samples : Array (Bits × Bits) := #[(0xbf91f3ebde7f2f8899fbfe080cf3efbae3ffa5dfd3e72f7062b3b1ff3dd6abf7ff75cfbd5f3bfddfe7cf1a7fbceaea2f183996ebbcd8239f45570a56f58136c1e9fe8cffc76899f5febc557574eca139f7e2d5fb4fafcf64fb9f29bcf1e23673,0xd88462b11645aa7408888a4824409780a4c4702084051fea913216f652a26ff00a6cc08d8c2b509a295476e2810980c039a840506700241f251c25602c91288868ca507d40008011ac4af8030408a8820970200002758300326775a94bedb652),(0xf6feffffee7f6b3afeffbfffefadff97df7bb9dfaffe9fe795fb48db0fffb6fbfffddfbd974cff3bf747fffadfffdfe7c2ded3e87adfdebdebdfbdfc93cd7ff797665e5ee7687fb69eef78f096bfd15dfdb3dffd5ddbcff636976bba7b63f87f,0x243b000440ba440b105320a2112e402e112008014048a00028c56008044890017002125002000224408b001154801d1ac2443b8908408240c200d001412e81120401200003907ec8028003c86902172c26019478e588344c4480024624124829),(0xe97f9d743bbdd6f7ff84d7fffbfeb0ff7fc55ebafe3ff3ffffdfffeff77d7d6f31bfbcc7e9ffe7e5dfffedb56b15b5d9ffe7ff57c777fdeabefff7effe7ed93ffeffffa7bbb7e75f6f77afafeff37effbaff7fc7fb7cf8dbddfddedfbebdcf9c,0x80002d8200022c400a04940a4c08e110e4040802e1002231012093369910ca081018408611011da08506422803a82600521006041bc109031140466209134a0010a004460218100e0029803844100c0814020801a1108000025c0104a049514),(0xd2dfdf1518dfeefe77cdaaf35f36beeef9df7fe501160db7f9cff37fcf9c9b74d1f77faefbffaddfcbd9cef2b6d245bbfb5ff37d7bbf36355a4ff7bfdbbfebffdbbb7fbf8f7c75d67308f2fffd93ff2c75ee81beebf72dddb6cb65df5bc0fe0,0x63e67d040c5e811bb648b2af48256022e108887b11ec5490af809084906232156eac588288ee2020240308841f85648a105a231d3a4167230e6a21909908434ebc00fa98131e7c091ac1016c09bee32a30b75a6c40c655793d48364b853b6ae0),(0,0),(0,0),(0,0),(0,0),(0,0)]
def x15columns : List ColumnInfo := []
def x15autos : List (List Nat) := [[],[48,33]]
def x15levels : Nat → Packing
  | 3 => x15l3
  | _ => emptyPacking
def x15index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def x15 : Forest := ⟨527,3,fun j => x15samples[j]?.getD (0,0),x15columns,x15autos,x15levels,x15index⟩
set_option maxHeartbeats 0 in
theorem geomx15 : graphValid x15 (boundsBefore known383) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx15_3_0 : block x15 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx15_3 : block x15 3 0 1=true := sx15_3_0
theorem tablesx15 : checkedTables x15 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block x15 0 0 0 = true)
  · exact (rfl : block x15 1 0 0 = true)
  · exact (rfl : block x15 2 0 0 = true)
  · exact allx15_3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx15 : Lower (varsX 527) (graphGoal 527) 4 :=
  strong_low (m:=527) (cap:=3) (hints:=8449) (nb:=1) (by decide +kernel) (plainA (q:=15) (prior:=boundsBefore known383) (before_sound known383 valid383) (by decide +kernel))
    (cut_root (prior:=boundsBefore known383) (before_sound known383 valid383) (512,5,0,10,1) (by decide +kernel) (by decide +kernel))
    (index_root (g:=x15) (i:=0) rfl (before_sound known383 valid383) geomx15 tablesx15 (by decide +kernel))
def mapsx15 : List (Nat × List Nat) := [(527,[]),(541,[50,65]),(647,[115,99,83,67]),(677,[114,33,97,82,50,65]),(793,[131,115,99,50,82,65])]
def knownx15 := extendKnown known383 4 mapsx15
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx15 : Known knownx15 := extendKnown_ok (m:=527) valid383 lowx15 (by decide +kernel)
def x23d3 (i : Nat) : Nat := 0x7a00
def x23l3 : Packing := (1,1,1,0,0,0,0,x23d3)
def x23samples : Array (Bits × Bits) := #[(0xbf91f3ebdfffbfcd99fbfe081cf3effae3ffe7ffd3e76f786ab7b7fffdd6ebf7ff77efff7fbbfddfefff1a7fbceaea3f3d39beffbdf823df55774a57fdb3b6c9e9ffadffdfff99fdffbcd77f7decafbbf7eef5fbefafff6dfbffbdfdf5fc73f3,0x980002b112012a64088008402440978004c4700084010b6a1032067242804de00040800d0401509a095476628008804029a040404500001c211404602491288040ca006540008010a40af803040008800940200002318200022741a04ac49252),(0xf2fe9f7eafffd377fe87b7fffbacb4d75f635abbaffedfef9dff4ecbc77f766bb3ffbcc7b1cce723df77efb0df97dff5e7cefbdc6b77dcfcbafff5ed9a7ed97f96677f06bfbf7fbe9feffafa8fb7dedfb8bf7fe5f958fdfb34f7dffb3e63fc9f,0x449d600044e4c410001b8208110a000cb02000204004b4808145708c142aa2101a2e42d08a2a02046088009141011990d20c18902200a443c408f1014826801828015018008002c1084002806008b40606308410a54c210470c0340d21292889),(0xe97f9d743a3d46b2ff84d7ffebfeb0bf7fc51c9afe3fb3f7f7dbf9ef377d3d6f31bd9c85c97fe7e5d7cfedb56b15b5c9dae7d743c657fdaaaedfb7eef64c5937fefedea7a320e7576e772da5e6f3707dbaf35fc75b7cc8d2dd9d4a9ebaa38f1c,0x282202dc201a22cf10e069e2a4e4ce330f4048812e5802233892093369d11ca1e1019408611011fa0853642294ba866a0561236949fc129033140466219935a2050a20446331fd08e282994b8d4303e8a14130e85a911c480425c2524e16d714),(0,0),(0xd2dfdf1518dfeefe77cdaaf35f36beeef9df7fe501160db7f9cff37fcf9c9b74d1f77faefbffaddfcbd9cef2b6d245bbfb5ff37d7bbf36355a4ff7bfdbbfebffdbbb7fbf8f7c75d67308f2fffd93ff2c75ee81beebf72dddb6cb65df5bc0fe0,0x63e67d040c5e811bb648b2af48256022e108887b11ec5490af809084906232156eac588288ee2020240308841f85648a105a231d3a4167230e6a21909908434ebc00fa98131e7c091ac1016c09bee32a30b75a6c40c655793d48364b853b6da0),(0,0),(0,0),(0,0),(0,0)]
def x23columns : List ColumnInfo := []
def x23autos : List (List Nat) := [[],[16,66]]
def x23levels : Nat → Packing
  | 3 => x23l3
  | _ => emptyPacking
def x23index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def x23 : Forest := ⟨535,3,fun j => x23samples[j]?.getD (0,0),x23columns,x23autos,x23levels,x23index⟩
set_option maxHeartbeats 0 in
theorem geomx23 : graphValid x23 (boundsBefore knownx15) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx23_3_0 : block x23 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx23_3 : block x23 3 0 1=true := sx23_3_0
theorem tablesx23 : checkedTables x23 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block x23 0 0 0 = true)
  · exact (rfl : block x23 1 0 0 = true)
  · exact (rfl : block x23 2 0 0 = true)
  · exact allx23_3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx23 : Lower (varsX 535) (graphGoal 535) 4 :=
  strong_low (m:=535) (cap:=3) (hints:=257) (nb:=1) (by decide +kernel) (plainA (q:=23) (prior:=boundsBefore knownx15) (before_sound knownx15 validx15) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx15) (before_sound knownx15 validx15) (512,5,0,18,1) (by decide +kernel) (by decide +kernel))
    (index_root (g:=x23) (i:=0) rfl (before_sound knownx15 validx15) geomx23 tablesx23 (by decide +kernel))
def mapsx23 : List (Nat × List Nat) := [(535,[]),(539,[50,65]),(551,[84]),(569,[65,33,82,49]),(675,[114,33,97,82,50,65]),(689,[114,33,97,82,49])]
def knownx23 := extendKnown knownx15 4 mapsx23
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx23 : Known knownx23 := extendKnown_ok (m:=535) validx15 lowx23 (by decide +kernel)
def x31d6 (i : Nat) : Nat := 0x10c840aa02d0fe00fa00
def x31l6 : Packing := (2,1,3,0,0,4,0,x31d6)
def x31h6 (i : Nat) : Nat := 0x30c0021c100000000000180
def x31d5 (i : Nat) : Nat := 0xa3e423007a88a00
def x31l5 : Packing := (2,2,3,0,0,3,0,x31d5)
def x31samples : Array (Bits × Bits) := #[(0x4f2899a86b639ff137f9e6807adff6bcf6df6de144a4ea1b1e7ceebef4966b7e2fff83e3ed1e935fe7f2fdebb97ff9d9f71668ffb5a372fdd3d563fde6b77b5277bdfc63a91c5c545bdd9c16ee8664ca1572b256f9498799c6e708977a017273,0x4040c825c8a83006d0136031115960825130504906882b86080b200065a82013901a040043016040400860c02402c80c8343b800ca301c20200540812004c6018f0800838a0040900002c25409b2722c12401005a01068a040109a2f2a12412),(0xc7bee778cce7cdeff624fcfdbf766b5f7878f5dffdff6f66dd42a40767f61647ae35ce5279faf8d6ed5ffeff3e859ca48c83dee978eeebeb6f7dd953f56c9b1a5e0afbeebfaf60ddff5be28eacd0cbaeedacfbbf393d7396b3788288aa46ce7f,0x6248900d031474260064803804880042580ca8a162843106070040f6818024a0c272118ba84ee1332380515090b9c250070244481108c00871e20901c8c08008e00469018140e040412110c0226000cd04806065a162d1402170e2540c44c869),(0xb8c3dff9b7a19cbfd8e79b7df7afbde36386f21cb75d33bfe39a474b9b7cc58bd60b148cb6fdd6b5bbed937de2a7c2346bfedfab9ffcf75fcd6c2736b9dfc7b6298f2bcb06e3b7979beaffb3de78abe5e68c94efbfb2e8ea6c105209d5a78d9c,0x110609602001808010000c424a76c898a1d013400d320419b0262109327d5a0d100d02340391084888632a040600150320041200a81416b48810e6f202020220008900a860a710950000c8044d98981010319d9810000018c28a1d0943230714),(0xfef7fdf77addf8aa9ccbada65d3d3f918beff6578f7adcf1ffa9936dfcbfd9c8f70bfddf9a81beedd733c7f67fa79622f87977924f717dab3e8bfe309aa137bfef7f3b1ff6449fee2c35a37f7f3d3a13defd4db9b6bf9f6edf0df5e055f809a0,0xa468b0051c841b360c8402a4910105610c06048812418880021948a4008080600042a040000412152510108a085440280c01280402004101060a080518014d0a1a3460479440ab400cd20081b205040f850420444b3048401815c0e6b89088a0),(0xe73f631ef51c6256dddcf24bb7bb983fdd2d9aff89ba9efbbd7dfbf5184b7ff30dc769b1c6762d5957fe27888ddb657bfb8df71ff8311d35b2c2b98edb5e6ef9effeb4ff54bf0be86f8c7c69d5b7dcf6ffdb59db7fcf5fb59f8fad77015f7000,0x1111407880014040020201082c8a288252405210641075048804004960013586c0080b31384b80a81a46214140a31246238a0072a05c8a3060008122a540b28061080f30401800304024c05a0900d8c01ad912b224ce0125e2ea3619054e5240),(0,0),(0,0),(0,0),(0,0)]
def x31columns : List ColumnInfo := [(513,0,30,0,4),(514,0,29,0,4),(16,0,527,0,4),(8,0,535,0,4),(4,0,539,0,4),(512,0,31,0,7)]
def x31autos : List (List Nat) := [[],[65,50],[16,66],[16,32,48,64],[32,67],[32,49,64,16],[48,33],[48,65,32,33],[64,16,33,50],[64,49]]
def x31levels : Nat → Packing
  | 6 => x31l6
  | 5 => x31l5
  | _ => emptyPacking
def x31index : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 11 1 9 1 4 x31h6
  | _ => fun _ => none
def x31 : Forest := ⟨543,6,fun j => x31samples[j]?.getD (0,0),x31columns,x31autos,x31levels,x31index⟩
set_option maxHeartbeats 0 in
theorem geomx31 : graphValid x31 (boundsBefore knownx23) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx31_6_0 : block x31 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx31_6_1 : block x31 6 1 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx31_6 : block x31 6 0 2=true := (@block_merge x31 6 0 1 1 sx31_6_0 sx31_6_1)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx31_5_0 : block x31 5 0 2=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx31_5 : block x31 5 0 2=true := sx31_5_0
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
  strong_low (m:=543) (cap:=6) (hints:=8449) (nb:=1) (by decide +kernel) (plainA (q:=31) (prior:=boundsBefore knownx23) (before_sound knownx23 validx23) (by decide +kernel))
    (index_root (g:=x31) (i:=1) rfl (before_sound knownx23 validx23) geomx31 tablesx31 (by decide +kernel))
    (index_root (g:=x31) (i:=0) rfl (before_sound knownx23 validx23) geomx31 tablesx31 (by decide +kernel))
def mapsx31 : List (Nat × List Nat) := [(543,[]),(679,[115,67,100,83]),(825,[131,115,65,50,98,81]),(867,[131,50,66,116,99,82])]
def knownx31 := extendKnown knownx23 7 mapsx31
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx31 : Known knownx31 := extendKnown_ok (m:=543) validx23 lowx31 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx47 : Lower (varsX 559) (graphGoal 559) 5 :=
  strong_low (m:=559) (cap:=4) (hints:=8449) (nb:=1) (by decide +kernel) (plainA (q:=47) (prior:=boundsBefore knownx31) (before_sound knownx31 validx31) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx31) (before_sound knownx31 validx31) (32,0,527,0,4) (by decide +kernel) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx31) (before_sound knownx31 validx31) (32,0,527,0,4) (by decide +kernel) (by decide +kernel))
def mapsx47 : List (Nat × List Nat) := [(851,[131,50,114,82,99,66])]
def knownx47 := extendKnown knownx31 5 mapsx47
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx47 : Known knownx47 := extendKnown_ok (m:=559) validx31 lowx47 (by decide +kernel)
def x187d6 (i : Nat) : Nat := 0x4101e3fc01fa00
def x187l6 : Packing := (2,1,1,0,0,3,0,x187d6)
def x187h6 (i : Nat) : Nat := 0x58
def x187d5 (i : Nat) : Nat := 0xbd58600
def x187l5 : Packing := (1,2,1,0,0,0,0,x187d5)
def x187samples : Array (Bits × Bits) := #[(0x11f7fb766ddfd7a3f1dfbbf677fafc8e77fb74bdcb8ffbffd7f5b2eb78f63ab57fdc7edd59c9777f763720d475a743ebe66eeecd767afbdfd53ee5b7681dedd3b7f77ddc0eba3b3bffd1cd7d9e3efe9f76bf8bca7feed21317fc38427f0ef27f,0x10224060004344200140025504000200409004522820a0420010030d010240170008610008940008000828081544000040702022c0a008801820aa01620541028a42a0080040024000605000c1043080020c200847440040525028402a00222a),(0xc01f0ffc9ad51faa0d91a3ba8d6bedaad31c8ddccdbda0aff482ff428db889edf945de3a73c6658892444b19e1712585bc63b2d635be99bfcf79022ef45bbfc487f0efa8524e22b2d7e887c8549089c75d70119af1a5e001081f018e4fcb4c4f,0xa355820a578cab004ebc452880d0cdb72f4c518d419449214f83a4100e08b1e0c6f0187c9721e3735f8357246a8beec3950d8e991414b520a110144800523664203c1575df371c03059a2f1308ab8b2649810732189076bfadaf518e45cb4c45),(0,0),(0x42f5bd2d7374f3b8f6b85e608b1a16748d973bf176f0bf19bd08c6b8c725fa58943385663746ced95fe1defe71bcf55d719b62f77a815405cad8efe7b5a2596878de4c7fabaf97efb2dfc8e2578783cffcf6d7bd95dfa820e8406e0d8cf38f8c,0x21af12023b4875b030149a5e430ac003b0090acac74a5282dc18801b8083496104c58f6062ab5011835e8129160d5b6203f078e05d13102559d8a1358241d6bc87d2abc462c2d94a4068ca3b50005322100584527954ec775ed46e090ca38b0c),(0x1fefd99d031ce12cbeecfec8ae8e53f3aa673ee0adfa77e7aebf5623bf1397ff85a3dbafba7faaf3fdccc77842feb6c93ff735231e71b7cb3bd493d696ee5b3d8d9e3f7fdb9dc9d5ed3d26f71fbe99ddd4e2f755cf3b7920e7c3d00df0fc0ff0,0xc108c840400020bc822640008d430340962e1240005013400e614804428b280b000100f800002e65c21440668122019800c020522000048a00314020412080010014013142124911d0621000239084c6402180180221388a12b9006d05c04d0),(0xeef8aeaff6ea19dd7ab2f34fdc153bbfd7bef1fbb3979b3c8177cbfef2dce79f171c23d3b6f37edd933f398fde5ad9777a49f9bcc196d1e134abfe4d1f63625775b99e7af67e5689d4727fabf45367b2ffddea65e04817de1823aff000fff000,0x48321a32a43b5f90117c00a1e404180b04110403010004b12838200414100888200c094022903406900617c89900320a000804014244612183504e88000824243c0480a0a7118f610420080a08492ec160022028091286218ec52000ffd000),(0,0),(0xfd5dbd83baf649df199ed64da075b1ab6c9db59e5b9c4dbbc21f4b9e0c4c55cef1f7cb66aefc7c66865a1b63ba795c7fee4011ff839f746af257db3807f6e7bcc75ccf91f3e354f14977365ee77dc9737944f82a159b25cc08438ffdff010000,0x6280c1e04d0b80000e8a0104500949c130d222e078d606d04e06c146c169a5c4345352c602890dcbc125480013466ec8d4f87421f218b810545429011185905853831b000f40064004b011e4210730c13a08e41155e28579de711adfff000000),(0,0)]
def x187columns : List ColumnInfo := [(160,0,539,0,4),(24,0,675,0,4)]
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
theorem geomx187 : graphValid x187 (boundsBefore knownx47) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx187_6_0 : block x187 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx187_6_1 : block x187 6 1 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx187_6 : block x187 6 0 2=true := (@block_merge x187 6 0 1 1 sx187_6_0 sx187_6_1)
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
  strong_low (m:=699) (cap:=6) (hints:=1342193665) (nb:=1) (by decide +kernel) (plainA (q:=187) (prior:=boundsBefore knownx47) (before_sound knownx47 validx47) (by decide +kernel))
    (index_root (g:=x187) (i:=1) rfl (before_sound knownx47 validx47) geomx187 tablesx187 (by decide +kernel))
    (index_root (g:=x187) (i:=0) rfl (before_sound knownx47 validx47) geomx187 tablesx187 (by decide +kernel))
def mapsx187 : List (Nat × List Nat) := [(699,[])]
def knownx187 := extendKnown knownx47 7 mapsx187
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx187 : Known knownx187 := extendKnown_ok (m:=699) validx47 lowx187 (by decide +kernel)
def x189d7 (i : Nat) : Nat := 0x2206c0ac3fc01fa00
def x189l7 : Packing := (2,1,2,0,0,4,0,x189d7)
def x189h7 (i : Nat) : Nat := 0x2040008a00409409003
def x189d6 (i : Nat) : Nat := 0xa50fc84600f68ce00fa88a00
def x189l6 : Packing := (3,2,2,0,0,4,0,x189d6)
def x189samples : Array (Bits × Bits) := #[(0xf90d27f9f9e72fe2ed8ee0ffb89953ffb73caa566d6b5fddda0b913afabea42f7f48bf75b8e3ffbbf07938876f7604d8aa5b70f2ebdfaa6f9fa6eae3eea49c6f7efe67acf77439baf7aaa965b5effc3fcf2fc42479bc26640360001bd833f4fc,0x186c21206c80864100034043a1180051d0018895000041618a200100a3104f0051221d844135163c1e115100c4036804a0157a10c48198a00060840204b63201c802e20402540089015e818508324900320889f1120286620ee911091802a4ac),(0,0),(0xb2c3ef63f5acebee4f5b7b28378f15536f71136f0ab6efff48272bdf756acb82289f174b37fedb251fbdc6daadd8f8d4f3a8ebef19da635e1c97a1761ba765dd79b2a641b394df25d5450d83a1f9a3dbd7f29b6f2ffac713803f23042f2cc8c7,0x8ea5d541830020c6446000900e00660a0030108bea081213810088a200240912100f120080c0008011690450434cd204108380e3121180ac4cc58a4820b32912820000204805226314a50401820c461794031008623402450c270b261528c8c2),(0xa12945bee63afa2f17b35e24376dfb3a94c967f692b4f4a2cdf9bdefb434525ac09b828b70aa046e2756b58ed4baee2317f7b92e546ed4c8f5e9805753c22b1b8774227cbcc2cde4faef57ea1711c382477246bce3f79e28961d9c0021cf0f07,0x140202664171e29a00a0843611a1001210861701486c4641410561013406680c0a024402b032e48ac92c8028cb00048e25806044da0500112005513960482455c276e148002108ccb0862682823192809b848b41803ec2ad2c8340860870605),(0x987686c5a9e7518d50df06dda399d9fef529cedaee0f206b0dd1cb990ef55d52e4f3cda16b2b35e9cb5fa8accb7f3fabcc1fa8d38d0e4dd6f7fe7bb7f11cc826ffe3c4f6a83faa55cbaafe5d73ead774130ae8c8f7a191093600d81fd1f00ff0,0x209300411100001417c4320010404c80063216084b10300001c5204d04a8102c005180138408400040440414314087011c2081a10208070a2c052a8c280044a20288000229284f521080181092cc0692c005320a01b411952116c83681700950),(0x751eb73b5fde14fce83aca8afcebf705fbc6f8ff3d6ad7d4f75b74edf35d6c7dbb74f3dea0fc4b7b7929b123f679c15caf4b5e92f3fdf8f7fd19f6c8dcfab673004f9bff47e97dff7e37747a6e678f45fa05751e0cbda8e569c046e001fff008,0x6083cac0820008122f3406301ac0198c0aa0640049c8b48a0000e602006e0005224c001008c281c221620046000c121210ca84e2023040102d8d1b91704008da034100500c8900602c80005a318000930d84600c40346805d0066aa241fd5000),(0,0),(0x86f6bd23eef66fbeffe1f175c363272fddf39bcdd9ac1b2879744e2ff5fbcfc7cc7df8e7bf7fa9fd9edf4ffe5f37ff644f65c6798faf1fd6b77bdf98467d5fc012c3fe6f8c3dca4dc93966d1dbc2295cb5d73fff2e7a5dbb6aa267e5ae000008,0x104000063cbc97019088000561340071f50e8b701421016436f9100c1581428084b02dac12114400c6949308a89204a00c002a1464443000821264040704d02178006189205259980048e8240c303128600088f1194815ba23d89459aa000008),(0,0)]
def x189columns : List ColumnInfo := [(545,0,156,0,4),(132,0,569,0,4),(24,0,677,0,4),(512,0,189,0,8)]
def x189autos : List (List Nat) := [[],[115,84],[32,67,117],[32,83,116],[48,82],[48,82,112,66],[64,114,50,48,80],[64,114,83],[80,50,116],[80,50,66,32,114],[112,66,48,82],[112,66]]
def x189levels : Nat → Packing
  | 7 => x189l7
  | 6 => x189l6
  | _ => emptyPacking
def x189index : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 5 7 1 10 2 4 x189h7
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
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx189_7_1 : block x189 7 1 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx189_7 : block x189 7 0 2=true := (@block_merge x189 7 0 1 1 sx189_7_0 sx189_7_1)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx189_6_0 : block x189 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
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
  strong_low (m:=701) (cap:=7) (hints:=536879876) (nb:=4) (by decide +kernel) (plainA (q:=189) (prior:=boundsBefore knownx187) (before_sound knownx187 validx187) (by decide +kernel))
    (index_root (g:=x189) (i:=1) rfl (before_sound knownx187 validx187) geomx189 tablesx189 (by decide +kernel))
    (index_root (g:=x189) (i:=0) rfl (before_sound knownx187 validx187) geomx189 tablesx189 (by decide +kernel))
def mapsx189 : List (Nat × List Nat) := [(701,[]),(859,[130,50,98,82,115,33,65])]
def knownx189 := extendKnown knownx187 8 mapsx189
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx189 : Known knownx189 := extendKnown_ok (m:=701) validx187 lowx189 (by decide +kernel)
def x349d6 (i : Nat) : Nat := 0x3fa00
def x349l6 : Packing := (1,1,1,0,0,0,0,x349d6)
def x349samples : Array (Bits × Bits) := #[(0xc3ada743e1bd77cc4f34f91cefb66973971bf7ff2f2b25d691ec756a2b28bcb83390ecfeec6e01a8e34887d6ccddcd9aece5e79faa7dcb6e401ad2a16becdab815543677ffa39af93c7db53ee96d1710ffdd8b145bcf240097880cc3a44fc4fc,0x3718570042a988178d958c27f61a3f398ad5e5009a014425090232e509db54d0547b80630f8d4e489512b6840300b18439622948c2f026f0c0812f7c53781e99844fb006021154673010164ca2030cf43421f5aaf424605e75bc2cc2ac4ac4ac),(0,0),(0x3daa3f545f630775a2d7df74a23d9b78db7b6557e985fec41f5017f9fe9bfc74c788ce330680d6234ae34b0b58c535ac6b7c307d9ff204d5d8b77f8d0ee3df84ac844564a7d10ed089255a8fb7f2273e634bcf1b8bddf88004650b0b788cf8cf,0x6e166320f061304c0624804b49a29183de1832c3b9170a08171153888c89b8a9ef4664b6b6a3b002669ff6c784fb54f3b22e324b2330586b002e61480c2403626da5ae9488452a10234be34405104aa0fa801644d4a50ff34ef72f0b708ca8ca),(0x7efbcf756f72fee5bef53ce13d6ef7e9ede67e3bf8d0cdf16f6bb4b3fcf74beeee8f9fa2bf89fcf4eb7fe8bbe32755ee7513bb2b9de197cdfb67bb5695feb9ff5f7f6bcf4dbf03c6af0f4b9ffddfafffeb3f7e7feffef827787e300c7ff0ff0f,0x808c570008ccb0018900241210021c0002800c006020320804a043010002520000804808140a5c9820002002000108080000805007200404809c0100814088804211020298d42684101418800a00040028e1112142200c310810000a605605),(0x8639e259fdd9fd914d1ca7ee56ce7d435bf5efcf5f7fac46fe266fff0b47b75f54fb54f7dbdb8fe805fd6f925ffcaa46bce36f9477b96fa70ddcb6fb7a3c7eafb72397bafa7adcee1f7d36bba1e5eeaa9ef6f524f6169c81a393e40f80ff0ff0,0x806000090440000302260c801e5c04070080ae0018c8b8882d14d086004a10d00001d94b0429000428440138018040344101031080818002b2c0000a002802628004c2038042388426a41824c14f0030844004408009fa18a43c00d40950950),(0,0),(0xedd433baf565e69fa82a777eaf7de377672f367902ef97fce5b8cf3e2e3847a74de2fcbb067e730f3cb5b2eed491b379832da3c06957fc921ec6c4aeea733ca5ece4ad12a8e4fe57c8a6ce65f7bbd4cac09029ad582943d81401dbf000fff000,0x654e76bf2022f80163ca08b017282208760208896250f2c80aa8281910449912804538780d201c2f93b2006494001009029498e24b0eb09d33081048c8780901414e271ec20861985618d35f86d0c440581221a92d4a71ce3b86baa048fff000),(0,0),(0x75ec93be333dac9b50eb6357d93b6bbcb7389b77843e973d1899ab9de3ef96cd7dfcf9cd2cb436d7f4f2b8fffc8263ff073ee8d7e4afb6782fedcf798fb99f73e7dea9e392ee6dbdeefb93e6fa89f0552b364ddabf61cbfedc09dbffb7000000,0x9a1100001d14020880109302608445c081ac05209c0d00058053438068a2248c05120387824a8000240cdd9129f0e842e4216000a0a04202000320b0270636001e800880096002400006208070010822a3c50c0092b48631c471455fb5000000)]
def x349columns : List ColumnInfo := [(512,0,349,0,7)]
def x349autos : List (List Nat) := [[],[96,132]]
def x349levels : Nat → Packing
  | 6 => x349l6
  | _ => emptyPacking
def x349index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def x349 : Forest := ⟨861,6,fun j => x349samples[j]?.getD (0,0),x349columns,x349autos,x349levels,x349index⟩
set_option maxHeartbeats 0 in
theorem geomx349 : graphValid x349 (boundsBefore knownx189) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx349_6_0 : block x349 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx349_6 : block x349 6 0 1=true := sx349_6_0
theorem tablesx349 : checkedTables x349 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block x349 0 0 0 = true)
  · exact (rfl : block x349 1 0 0 = true)
  · exact (rfl : block x349 2 0 0 = true)
  · exact (rfl : block x349 3 0 0 = true)
  · exact (rfl : block x349 4 0 0 = true)
  · exact (rfl : block x349 5 0 0 = true)
  · exact allx349_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx349 : Lower (varsX 861) (graphGoal 861) 7 :=
  strong_low (m:=861) (cap:=6) (hints:=13019128580) (nb:=4) (by decide +kernel) (plainA (q:=349) (prior:=boundsBefore knownx189) (before_sound knownx189 validx189) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx189) (before_sound knownx189 validx189) (512,1,332,16,5) (by decide +kernel) (by decide +kernel))
    (index_root (g:=x349) (i:=0) rfl (before_sound knownx189 validx189) geomx349 tablesx349 (by decide +kernel))
def mapsx349 : List (Nat × List Nat) := [(861,[]),(877,[84,131,98])]
def knownx349 := extendKnown knownx189 7 mapsx349
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx349 : Known knownx349 := extendKnown_ok (m:=861) validx189 lowx349 (by decide +kernel)
def x191d10 (i : Nat) : Nat := 0xc204024820608058c0ff803fa00
def x191l10 : Packing := (2,1,5,0,0,6,0,x191d10)
def x191h10 (i : Nat) : Nat := 0x705e2ca19814713447c2985711f000d6660d151459e2031e053c15e16a27545c62c17000d5f069000f0eb0aa08641e26b5240ff9a000f09c07925e4f70682881ca56a01b4900000000031051d250000c12e48000d0000091b000000424000711f1860482ae0c000a2110276004262336100046592b000c4c21a70350b122000000400000001000000600018408e2004002a080a18018000640000
def x191d9 (i : Nat) : Nat := 0x100b0c18804000a05070700041023012618a0f020850470b0c182010408a4070b0c1800404520140820c30b3080b0c1820034e201430f0400a38e100a1c082045854c3070208d1414120407070408c040100a0801628a0c002822c5184870b08441020818054404001810a60a0c087002c5410490a08001065810418c18002148141810008a140010608b0e080182060401028206000942c00e0054106090141030200a141030200a141030200b0e0801880e14186820802070c1f04294101000c8141810400a082882830200114282060401410302008141010600a14108385061a0820070a08181005810418e1c1003870400f244010c2c1807f2dd4b8e6dfd459cf1ee07b8761aa4d219e529e3c434818fc9e8ba9702d9da331e5c2ae548a6949e848f51c9342638b313e23a3d4710ac1081a828036001ff58e00ffa43007fc72803fea1401ff55200ffa21007fd53803fe98401ff88a00ffa41007fd32803fea0401ff50600ffa63007f920802feb9401fe44200fec23007fa22803fcb9c01fe5c600fbc67007f932803fcb1c017f5c600ff281007f953803fc98401ef91200bfae7005fc72803fc90c01fe5d200ff0e5007f972803fc98c01fe50a00ff283007f820802feba401fe55200fe423007ba44803ed19c01fa88a00
def x191l9 : Packing := (45,2,5,0,0,11,0,x191d9)
def x191h9 (i : Nat) : Nat := (if i<1 then 0x69ecd00a829a19018d60af08de8001aa6a86acc08001c65d102c4d6867804a3669458000c56e938009405a0000029823106405b000121cd0b5668eac38b900000005848a09da960000000000000144480000004b136a008632248a4e3020263ede40a2000729000048f10cf000000000016008819e10000165db11e25f894d65100000007a52a0520ea000000000072f7cc76b640000000c4d8278c3762ca000000129ee21424559856333a16598897a0000000000382200040500006911834c1200003360000000000000000005964a10e2138518000b188001e178001cba000020c80014c2628c00000004993b36c631b7f05861b00b6e0fe6956b42aa1600f2e4607e207110a08e311ae1db89986738da80c19954b8884a82ac469e0f499fe6d0000115b045aba8000286592d86402670e0316aa622b6a71bf30cc2e800000048c40000001c27288f482aa56000000000051a000ed0a4202800145280000005a420000000e3c8000cb7992660d50066228000655895800009a800019b68380000000000000000004964a0422bb86d45ccb99869014800a8a32806917caeba036a05a178032595345092f84541104ac8a859ac918ee00042d945c604c641fac6000409401d592eca38000000682c0002afc2a8b9aaa25f922c9100000000000c53800182ca880a0fb36eeaa584e2318955e11c916635ca0163a108800000008a780000000001e20c941a6180014b86387842516263f000000010bd03990fa8394808000000053052068035079c439b73e600000000000000052360004368000122b18268210b5a071c5bf4700001182000333a0000001e3078e2000227c43b622408c0001215000000000008c9800000050840005129833800003442940000000000226e81482778adf374a4fe9ad6d8b2d2490725c45d586140e60bf047298fe9410ac000000000000000007226a27b19a000000045718a1c3d2a020005ab000019a7a6b800041b800000000a6688709bc6cf8560000001282102e0004c450ae0001632e0b80000000c1750b06933aad69fb9984496068688eb1b262f0c362db0d8e57b0d584c00000002ad40000001697c0f8a460000859800180780000005a1faaec19270002000000c0001000040084b0000038000000030000018003000c3100270002010802000c0000001040000000080000040109c2000400000a0280012000100000100000042028440000a0004001000000400000400000101003000001006100800080200002200000008000140110003008000040000000080200000000000000002040000000058000802408000000000048001000000001804000002080000840000c000000100000000000040000000000600000000001000c2000000002000000000000802100c000000000000004000800000c0000000 else 0x7090401000161e80000007ad104e910c00000000005272000000000000000003010000112b4218001abc8001c3d80004378000000000188b8b950d6ca5a6e3b93daa7000124c80000000000000000161f0001a9b59)
def x191d8 (i : Nat) : Nat := (if i<1 then 0xd824c200ff48148200fdd634c200fed2148200dfc7250600dfd625d200bfd8244200fed211ca00bfe8848600ff53148600bfe884ca00bfc8748600dfd625ce00dfd615d200bfc874c600bfd8344200dfd215ce00dfc7244200bfd831ca00dfc7250200bfe884c600ff9204c200bfd8258e00dfd315ca00dfd615ce00dfd7488a00dfd325c600dfd215d200ff56150600dfd635ca00bfc874ca00dfd325ca00bfd814ca00ff21158e00bf98055200fe92088a00bf981552009fd801ca00fe9211ca00ded7288a00fe88788a00ff2111ca00ff21108200bf98344200fea225ca00bf9801ca00df6115d200efa6650600df47284600ff2115d200efa6650200fb940506009fc874ca009fc8788a00f3e5591200ded211ca00bf88788a00fb94055200df6115ce00efa6650a00bfa8855200bf98255200f7a5550600fba4408200bf98108200fe92188a00fe92148200ff1315c600df9205c600bfa8848600efa665ce009fc8754e00fd9634c200bf88755200fb94250600bf9831ca00ede668ce00ff12084600ff2114ca00fb9425d200f7a555d200fda3348200fea225c600fba441ca00ff130846009fc8750600bf88750600ff21150200bf98448600bf98158e00f7a554c600df9205ce00fe9421ca00bf98254e00dee225d200bbd841ca00f7a5550200d7e555ce00ff13148600bf98050a00dde331ca00bf9811ca00df6115ca00f7a554c200ff21155200ff16150600bf98258e00dde335ca00fea22552009fc8748600bf88758e00dbe445ca009fd831ca009fd841ca00bf8874ca009fc874c600cfe665d200bf88754e00f7a555ce009fc8755200fba4444200bf9864c200ff2115ca00ff21154e00bfa884c600efa664c600f7a5550a00fda3308200ff08148200fba4448600fda3344200bfa8850600fda331ca00fea225d200fda335ca00dbd7450a00df97244200bf88748600bf98348600dee225c600fba445ca00bf98154e00efa664c200fb94255200fb64484600fea2254e00bf88750a00bf9841ca00ff21188a00fe93288a00fba4448200bfa8858e00fe94288a00bf98408200dde335c600fe93188a00bf8874c600fea225ce00df9305ca00efa665d200ff11050600fba4488a00d7e555d200cfe665ce00dbe441ca00dbe445c600ebe66912009fc8750a00fd9314c200bf98244200fda3388a00dec7250a00bf9824c200fd9314ca00bfa8850a00bfa8854e00fba445c600fe92050a009fc8758e00fda335c600f7a554ca00f795254e009fd811ca00bf98308200dee225ce00fd93258e00ff2115ce00bf98054e00ff14284600df5315c600fd93054e00bfa884ca00fd63384600efa664ca00bf98050600fda3348600fe21188a00eda668ce00f3a55912009bd841ca00fca3388a00fd23384600fb24484600f5a558ce00bb9841ca00 else 0x430828140c0110e04306180628101104010840040060000a120a00808404060420428108141c28618162858212081000c14084161421102106040820410c0a1040108022042110d121043048404182050a00428144100420002101060430286042220b08605880830500821a30210101020400618042040050c300105030f0d0e0a3218506010060001000050300202031000410010000c0041c100f0018508070a030e1005380381c283080a1010010006003001018000180086102181890000506062830804c344020028008180090020000140040830800028010b0a14004080002058010200280101801000704442860000a000080e00006801430c0c0200e00208000140060500400e070a0c240060500006181e20f0a140043820301c0024c001800804c28400180001c0c00810010400408610020020040841400286041830a00500302002800c004040040002c009002004186002801400a0041000020010008100002000040028000240080143c28606002830801428407000030300140060420800010440880c0000011038507061100282181011000204480145000a1c0808a00200418408614180120c0083c14303828a801400a005060040a1defdcadadd98d83d6ed51d4cd37d22d0dcf8cf3cdecc1cacc97c7ac65c50c3bc2ec21c14bffbeabe5bd0bbbbaeb99b84b77b6ab55b40b2bb1eb01aecadfacaab5a98a83a7ea61a4ca47a3aa2da209eb9de9c19bc9b79b299d98897396696195494f94a9359088cb8c68a189487f87286585883b83683182481f80a7f57e07d37ce7b97a479778277577076b76675174c73f73a72d72070b6fe6f96e46cf6ca6bd6b069b68e67166c65f64a62d6206135f65e95e45cf5c25ad5a858357655954452f5224ed4e04d34ce4b94b449748247d47046b45e45944c44744243543042b41e4013f43e73da3cd3b83ab39e38938437f36a35d35835334633932c31f31230d2f82f32de2d92c42bf2b22a529028327e26124c23f23a2252081f31e61d91d41bf1a219d19818315e15114412f12a1151080eb0d60c90c40bf0b20ad0a008b07604903c02f02200d000bfd811ca00bfd8158e00dfd215ca00fdd314ca00fdd3258e00bfe8858e00bfd864c200bfc8788a00fdd314c200dfd8748600dfd635c600ff92044200bfc8758e00dfd7188a00dfc7255200bf)
def x191l8 : Packing := (220,3,5,0,0,12,0,x191d8)
def x191h8 (i : Nat) : Nat := 0xd090009a6505313000123000000000c5214fd4901992a608000000d0e30d822f24d0c12c71700000011031bd25000000000b4141a00af27f4490f016b5422181c11ee2ed00000000000b5f214b12f2bd970003019605d2c28f18551215604000000000000000000906d92b26559407c11000a0b31f000000000803663c8271d447329000000e20a2d202000000000a28008000000000a0001d64200004308200008008000000a
def x191d7 (i : Nat) : Nat := 0x10400100408a201840100800610000002142000000050400200414008000c0050010028018284000000020a0020bfdeaeb70b15529f38954962f12823fdf4f5783adbad869b3992c45b2c5589e4ca2d0c813e1b8c05b2b1207435180ac4c2109814019f491600728033eb2243c450047f64087486008fec890f114011fd9221d638033ea20c08e50047f6448758e00afac8ac6b8c019ed80484728023f930ba4450047f25d8158e00abeca8e4a0c01dd5314c9718023f92ec12c70057d25d6150600adeca0e4884013f59121d638023f92f442430047f2617188a00ceeb190e994013f59121e22802afb2a39281004fc2612084600f95114ab224011f8976055480277532c20e5006d6616331ca00ccec246639401fc233846228032bb0b198e5005f86448788a00dd8c242239401ed21199a338027e32243ac7004f664e8850a00dccc2466394011f59121e2280327b0b220e5004fc6448788a00d9cc2c88394013d8988cd72803e94452ac67007d4846558ce00f9908cab224011dc988cd72802b6b28394230047d6448758e00
def x191l7 : Packing := (47,4,5,0,0,9,0,x191d7)
def x191h7 (i : Nat) : Nat := 0x71b0
def x191d6 (i : Nat) : Nat := 0x2887d684985d2228021f5a125e8848600
def x191l6 : Packing := (2,5,5,0,0,3,0,x191d6)
def x191samples : Array (Bits × Bits) := #[(0xba07c15f4fdf6cf95faadf1fd7e5b3316b7bf9e78a5f84755da36f78f331570e4fba890137fdb6746422f21e58f4adde98651beaffd713f934f1b23fdf74bf03ffc32eeb9896bfe4764fdaac632deb90c43838203187d246940112477e23f023,0xd48c0000003c44c084a0810c17032100020d10700c0884430050000050208100284d014438a0008291a2948120011930d800004200401041118170210000021010004200002904100041416305639040190c00220482140c20640214202012),(0x73ffab4a9ef40d638bec853881a69eaea537e3ae667704cc3323eb30e4fe3f11125fd6e1ace557832b59c88ffdd4df10b7b2fd0e24edfc4cc3a5f74e3fae2b27d7dfb24f073434d13c0f2d279ade11b285600001f5328c0001e3d215d8c4482f,0x202853918452802021320e4c00081418225902070920936298c1a802a800cc60d5d010c08a055e2b3c600c4a3419c6a4c40313c4845a990f3e264408120d4609c24eacac34080672a4062cac90da1047056401c7495b1c62e1d39335a8c6c869),(0xfd7bfde6b4b4b5aefc4fecfecd732aba3ee8eef0b7faebba267a9abe3c5ba83971dde5a95eaa22a7cde32ba373d4f6c1cbf004940cc3ccaf32f7253f702e9937a79cb8b6baffe5fdcf6a97c2c92327214a5540bbcca040316beec50881040d8c,0x88830408200121d008015002481000800004002094412000213c43410621128700002c0200182040830a11104186100000080833108160604080238208022000058100020101c000523081024920e7200a01d20886a040010c08408051010514),(0xdb31df144f2733742f5f3b4e781d140e205762cd298d44dee148be6bad5204ac7567fe6d487ff389bd6cdffbe0b9d631f6b68b7d7a885cfe01dbfaf96a9c76ac95f41e894eb36b3daa9e5fd379b1ccf871a62a44008a0386a10289e01f80bf0,0x30548b0218c4160325002818848621701003570061220388d2020028c09ca05028e280b1800092083c3002a40060617a27524208e600058c10010c64202890005070441c52020c85808128c1269f188185180466610db03cc320a72e00b08ae0),(0x9294ecfb8f3dd2b61efca2afc35763f6918d20c178f41c84dadabfa7c29c55eee3e3de9f8f0dcdb81d7834bdebd1036efc8e75e968ff22d4bd5d4ef0219ffede44dc2c88dd8cd973eeffaf739c60d24e1faa0a15003f500b101028d021fd7050,0x86017009071940801832544433481c0ce89c00ac0291d03320a882400a01042a060400060ac101b300064d4868180e840821b45008a09220244252001c030f04a008090129ed1242077602189860806e3ae6d39988724043309218d1614f5000),(0xb7302f4fdb4bba79f91b57fef62d87b7e377598d555cb84dd2cc12f945af0da64d494f73067189f1430dd2cf046bdca1e6398ef2fbd9f936db116bc9dc60d5e28babc729c9c70394e5365cf9acf0ac213f80b76056d22fc48400087e8e028600,0xd70040c1415381a21e3b5958608000c4f32440680543121080842c31a021c22e6000225eb242028c280a40000a4c00200b252b190920a0211608020a0a96f5f40c896298208610910ab380a28c708c251f02f3e8dd8a1942c00289ddca010600),(0,0),(0xd41f73c9bc9ae386f65a4aca6a3d2525ded60678ddb6ffbf3afc535792a983a7614e19f8d64efd0eae8e2cd3e7de7c0ae854b5fe873db7856b426364a42481bea0a865f1698e49aa23d433aa72df101878ad8d5b0a502f89124d052000000640,0x48192406840805e1c02020930791320401a391083448845803000000c829400d7211014d05581240318e8100116d0004c2d444c65e1e0808634045e0010008e0420c240658216225007e04328f109a60ac0c17205526bc33f5362020028040),(0,0)]
def x191columns : List ColumnInfo := [(24,0,679,0,7),(160,0,543,0,7),(513,0,190,0,7),(2,0,701,0,8),(512,0,191,0,11),(4,0,699,0,7),(547,0,156,0,4),(513,32,30,128,5),(516,8,163,16,5),(26,0,677,0,4),(521,16,166,0,4),(531,0,172,0,4),(14,0,689,0,4),(641,32,30,0,4),(548,128,27,0,4),(20,8,675,0,4),(152,0,551,0,4),(134,0,569,0,4),(537,0,166,0,4),(56,0,647,0,4)]
def x191autos : List (List Nat) := [[],[115,84],[32,67,117],[32,83,116]]
def x191levels : Nat → Packing
  | 10 => x191l10
  | 9 => x191l9
  | 8 => x191l8
  | 7 => x191l7
  | 6 => x191l6
  | _ => emptyPacking
def x191index : Nat → Nat → Option (Nat × Nat)
  | 10 => lookupWord 68 87 3 12 6 2 x191h10
  | 9 => lookupWord 349 509 5 14 8 2 x191h9
  | 8 => lookupWord 64 95 3 12 6 2 x191h8
  | 7 => lookupWord 1 3 1 7 1 2 x191h7
  | _ => fun _ => none
def x191 : Forest := ⟨703,10,fun j => x191samples[j]?.getD (0,0),x191columns,x191autos,x191levels,x191index⟩
set_option maxHeartbeats 0 in
theorem geomx191 : graphValid x191 (boundsBefore knownx349) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=2) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_10_0 : block x191 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_10_1 : block x191 10 1 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx191_10 : block x191 10 0 2=true := (@block_merge x191 10 0 1 1 sx191_10_0 sx191_10_1)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_9_0 : block x191 9 0 4=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_9_4 : block x191 9 4 27=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_9_31 : block x191 9 31 14=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx191_9 : block x191 9 0 45=true := (@block_merge x191 9 0 31 14 (@block_merge x191 9 0 4 27 sx191_9_0 sx191_9_4) sx191_9_31)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_0 : block x191 8 0 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_9 : block x191 8 9 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_45 : block x191 8 45 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_81 : block x191 8 81 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_117 : block x191 8 117 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_153 : block x191 8 153 19=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_172 : block x191 8 172 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_208 : block x191 8 208 12=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx191_8 : block x191 8 0 220=true := (@block_merge x191 8 0 208 12 (@block_merge x191 8 0 172 36 (@block_merge x191 8 0 153 19 (@block_merge x191 8 0 117 36 (@block_merge x191 8 0 81 36 (@block_merge x191 8 0 45 36 (@block_merge x191 8 0 9 36 sx191_8_0 sx191_8_9) sx191_8_45) sx191_8_81) sx191_8_117) sx191_8_153) sx191_8_172) sx191_8_208)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_7_0 : block x191 7 0 25=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_7_25 : block x191 7 25 22=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx191_7 : block x191 7 0 47=true := (@block_merge x191 7 0 25 22 sx191_7_0 sx191_7_25)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_6_0 : block x191 6 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx191_6 : block x191 6 0 2=true := sx191_6_0
theorem tablesx191 : checkedTables x191 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block x191 0 0 0 = true)
  · exact (rfl : block x191 1 0 0 = true)
  · exact (rfl : block x191 2 0 0 = true)
  · exact (rfl : block x191 3 0 0 = true)
  · exact (rfl : block x191 4 0 0 = true)
  · exact (rfl : block x191 5 0 0 = true)
  · exact allx191_6
  · exact allx191_7
  · exact allx191_8
  · exact allx191_9
  · exact allx191_10
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx191 : Lower (varsX 703) (graphGoal 703) 11 :=
  strong_low (m:=703) (cap:=10) (hints:=536879361) (nb:=1) (by decide +kernel) (plainA (q:=191) (prior:=boundsBefore knownx349) (before_sound knownx349 validx349) (by decide +kernel))
    (index_root (g:=x191) (i:=1) rfl (before_sound knownx349 validx349) geomx191 tablesx191 (by decide +kernel))
    (index_root (g:=x191) (i:=0) rfl (before_sound knownx349 validx349) geomx191 tablesx191 (by decide +kernel))
def mapsx191 : List (Nat × List Nat) := [(831,[135,50,65]),(891,[130,50,81,115,98,65])]
def knownx191 := extendKnown knownx349 11 mapsx191
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx191 : Known knownx191 := extendKnown_ok (m:=703) validx349 lowx191 (by decide +kernel)
def x351d10 (i : Nat) : Nat := 0x82018c4009320ff803fa00
def x351l10 : Packing := (2,1,4,0,0,5,0,x351d10)
def x351h10 (i : Nat) : Nat := 0x20e803e0b80f00022b50d00000032752a62c000000a06b00616b2300072281a00011140ca3080412680742da20000018000825a1d621a2e629000000802f1540a60991c000808000c14000105912c1ec2fe17f1b61f000b01e28b240000000000003132190006109800210c1100c0001c020094318000
def x351d9 (i : Nat) : Nat := 0x71630a10301c588284180c38a018314608a0602c440e0c052c688224180e34000229a39c614228180c14004239498881c180d10f00108231c584112028b143012286019254200a514200120a004090504200918b004080600510a1020105080048280084414204020a008004218a100090508004810200c508004828461608840088c588284180e284080488180610008c28000452840023142001204282010508100910300c286018a10009228401c108438a004714008e306216084d9c60c50426bc56e6cb573aa1486794c994d1f62742b81cfddea3b7734df5aa34364cc25762cf57ca9d4526d4ac8e5021d5370684c51672a04cc8b0f91c432c570971001a429029001ff58a00ffa63007fc31803fea8c01ff58e00ffac3007fe11803fea9401ff48600ffaa7007fe33803fe99401fd84600fbc67005fc71803fca9401fe58a00ff241007f931803fc18c01fe50a00ff2c9007f932803fc39c01fe1c600ff243007f963803fcaa401fe50600ff2a7005fc73803fd19c01fe50e00dfccd007f961803fd08c01fe54600ff2c1007f910803fc98401df95600fdc45007f950803dd22401fa88a00df4cd0077a55803f908c01f68ce00
def x351l9 : Packing := (49,2,4,0,0,11,0,x351d9)
def x351h9 (i : Nat) : Nat := 0x513290bda1ab459b05d0000000042f8000d02c00000002ac700000000000411f0001649f46a288511640002c644805110d623ac5208fb4136680000038ce818ac495c7ea880526163be80380019015c106c3e804920880003495891d5117a29fc4f101ad0a2000081890f9d177805c846906d0000220a833212e61e0413a939500401f0c3c8c74f01441f8e056823b022c242818b867b8e7c1f4c34e48d083ec15a000000000000232020c000402a000000000006105b17ec29800031340001018eb507811a0efa13086c800090ca00004371120103262ac84630dd104762f7087c8c4d0e7a49b89138af2006000000000000001628c0006084d07a000142b187100000001499e90790f9e40800030df423c0000000000000840003454000082168277c9a800020d000000000000f16c0001c98800040d2643387f38929102000000000ae000121e6c8a00000001c3d5c79c8de825a000381e08460000000000000000000e43442ba929000142e800030da00000003452e8980001e03040e98e43080a187477483a2064635c0003860c5f842f0000687800000002033a0640001407a07670c661cc61634550000519599880800000b46a21ae087108811ad038b82ca06c0121c459092608a505f847303810ccb133403c8269095001783fe41f812c2187c16a0753853d052225c80dc8d8303164ab81ac0b4220600019417050000000020601904a1c7a30702a20edc057e386489b0eb2112000383f884a209ee09000000000001a11600758dc000043c600929109123a1f9c09e055d11e00000004915b0e862c2c104093105000020588000312c42e5c8d90260000000303d8000a23000020291833000000000240843000162f800000009250000286590e0a18fa0d0c7bc0255000a324897f8e8b01203da43a8000526d040501b6002000023940007a050020e42043d081c70ece3d000028066142621fc8518b510e5c425804583900000003425b837e16e203640ffe0a822500b8000006f8184427c010e1171140848f06da9060001a33605c309a0001c3480000000d077a34645660d0000000004510000d2220000000000081ab616f44a002c506100e284e385c704e0000000582d11520c28016201b242242091e0cb071408381011c801203c1063604a0014197800814200040c00200583000a4c20b00141840004f03023c0810000080001408b004850014041000000081000c1801c00000001c680120400006043810000980
def x351d8 (i : Nat) : Nat := (if i<1 then 0x63384600ef96158200ff13158600bf98250e00ff13148600fb95291200fd9314c200f7a5550e00fd9311ce00bf98150e00ef96458e00bfa8850600bfa8855200ef93099a00bf9808ce00fe93258a00ff2114ca00bf88358600ddc878ce00fda331ce00fea2284600fd93154e00bf98355200f795254e00ef91099a00bf8874ca00bf9861c600fe92154a00bf98255200fda334ca00fda3359200bf9821c6009fd821ce00d7c7195600fd9318ce00fda330c600ff21150e00ff1310c600bf88359200fb96450e00bf98158200bf9804ca00ef94199a009fc8754e00efa6684600bf9840c600bf980486009fc8754600bf88758600f795355200f7a5548600ff21159200fb94155200fd9868ce00bfa8850e00cfc7199a00df8714c200ff13184600efa6650e00fd9828ce00bf983486009fc8758a00ff21158a00fda3350e00fda33542009fc8748600bfa884c200f794195600f7a5584600bf88358a00ff21155200bf883552009fc8758e00ff23384600fb95191200bfa8858e00bf9848ce00bfa88592009fd811ce00cfc7399a00f7910956009fc8784600fda3358a00bf88350a00ff21154200fda3358200fda3355200fe93188a00bf98254200fea220c600fba1191200fda3344200fea22592009fe881ce00bf88348600f792095600fd9808ce00bfa884c600fea221ce00bfa8854e00bf9861ce00bf88350600bf98258e00fb94250e00fea221c600fda331c600ef92199a00ff211582009fd861ce00bf98344200bf98158e00fb94159200fd9308ce00bf98058e00ff11084600fea2254200bf9858ce00ef92099a00fd8878ce00fda3350600fda3384600bfa8858600bf8874c600df88750600bfa8854600fd8818ce00f7a5550a00bf98054e00f7a554ca00bf9818ce009fc878ce00fe92058a00ff21154a00ff12184600fda3358e00fea2258e00fea2255200bf98354600ef96158a009fc8758600bf88354a00f6e2295600ff13084600ddc718ce00bf98158a00fda3354600f795254600bf98259200fea2250600ff14184600bf9821ce00fb96191200d7c7395600bf98458e00bf981592009fc874ca00fe94254a00fda3354a00eee2299a00bf9820c600fda3348600ff21158e00fea2254600bf9851ce00bf88754e00efa661ce00fb93191200ff13150600fe9424ca009fd821c600fba440c600bf9828ce00bfa8858a00bf88754a00bf9831c600ef94299a00bf98258200fea2254e00dec7388a00fea228ce00bf88354600bfa8850a00bf9851c600ff21154600bf98254600bfa8844200f7a551ce00bf88754600ef96159200bf98155200bf98054600bf883846009fd831c600f5a3395600ef21199a00f721195600fca3388a00faa2291200fd23384600fb21191200eea2299a009f88750600f6a2295600fe22284600f3a5591200 else (if i<2 then 0x4008582130090430430430830038e0201c00c108c002821441421fbcfa9f9df91f85f72f5ff4cf39f26f13ef9ee6edaec7eade9ae87e74e61e4ee42e28e1ce09df6deadd0dbddaad9ed8bd6ad57d44d38d25d04cf8cf3ceece9cddccacc5cc0cbbcb6caaca5ca0c94c81c75c62c5dc43c37c32c26c21c0ec02befbe3bdebd2bcdbc1baeb94b88b83b77b6bb5fb53b40b2db21b1cb10afdaf1ae5ae0ad4ac8abcab7ab2aa6a9aa8ea82a76a6aa65a4ba38a2ca20a1ba16a0aa05a009ed9da9ce9bb9b69a399e99297f96c95994d94193592291d90a8fe8f98f48e18ce8bb8b68aa89788487887386e86284183582982481f81a8007ed7da7c77c27af7aa79e79277876c75975474f73c73772b71f70c7006fb6f66ea6d76d26cd6c86a769b69669167066b65864564063b62f6236175f65ea5e55d25cd5b35ae5a95a459f58c58758257d57855e54b5465415355305245185054f94e64e14dc4d74d24bf4a548b47846c45945444f44343e43943442f42341740b3ff3fa3f53db3d63c33b039d39839338e38938436a35734432a32531930d2fa2f52e22d62d12cc2c02b42a829c28926825525024b23f23a2352302242182132071f41e11c01bb1af1a319718417f17316715b15614a13e13212d1211151101040f10e50d90c60a509908d08107506904f04303702401800c000bfd850c600bfd860c600f7d5254600fec824c600dfc714ca00bfe884ca00efd6258e00dfc7354a00dfc7158e00bfe8858a00f7d5254e00efd6258600fdd3154e00fed5248600ff53148600bfd8258600bfd814ca00bfe8858e00dfc7158a00bfe8854a00bfe884c600dfc7348600ff53158600fed624ca00bfe8858600bfe8854e00fdd314ca00bfd8158e00dfc7354600bfd8254e00dfc734c600bfd8254600bfd8154e00dfc718ce00bfe8854600dfc874c600bfd8258e009fc874c600fea2258600fd9858ce00f761195600ff21150a00bf88344200ef96258e00fd9848ce00fe61188a00ef61199a00f5e3395600ff08384600fda3350a00fce3388a00bf9860c600fe92048600bf9868ce00f795054e00ede3399a00ddc734c600bf9850c600fb92191200df47384600fda33482009fd851c600bf88748600fb94150a00df48784600fea2250e00ddc738ce00ff12084600bfa8854a009fd851ce009fd861c600bf88358200efa661c600ff16184600bf88758a00fd9818ce00fe8824c600bf88354200fd9314ca00bf88758e00fea2258200bf88348200bf98254e00bfa884ca00bf9811ce00fe91088a00ef93199a00fda3354e00fda3358600efa660c600ff08784600bfa8848600df8734c200fe93088a00dec7188a00f793195600ff21154e00f7a550c6009fc8754a00f795054600bf98448600f793095600f7a3395600f7a551c600bf9800c600ff2111ce00fd else 0x182003043038021423000910210c1221614430008101122023070460860610210c443c63000860010916218004300086045c102302118004300086046010e3121843078a10460010c820439030510900240118004245a01a48210001002080880000100400421400048420008802458d1a108000402848900410012008000410422c4880891638010210a00a10a20c000284084802080182045083002044182182100210460500400510608410500a1a000240140100100400800050408a00610210200010200414012000280005002802803040881040890040082044060081011010040c014102280100200448b8010800288200000c0003020040600900010058d1010050045411a34018000400010020400800a500244100210470d10000122d00724008000a0810040400021034400410a00c0089802c69000403038800a0001800000580200000001c58e10210018c2082180180005042080080000040b102800060a081181002401400040021080000410a008d0c108000500018030110c0c240004000000050408c1011411a2050400c08020030408800808a00400801421001401030042c4a01a4400040022080008014010220c0002400042e0090e40220c10a00828020400c108008208600600410430020401000450028021))
def x351l8 : Packing := (311,3,4,0,0,12,0,x351d8)
def x351h8 (i : Nat) : Nat := 0x1a23313ceb9518a02f0f88d3486e22215b834001e44a0b000343a000e0d886182323a41ee82388a61af0550ba8078338081878881c2aa070014050821c1e285c87d2906066081c08a3970a58ec86d82440ce0bc06bc0171bc90b8126acd230002826000b239001c640005160000000206000000247fa2900020c0537a151131104001a2d0097071862c0b000181c000000f128000000a38000000181e00000c02012b0f022101d3111a051d30000741500
def x351d7 (i : Nat) : Nat := 0x20800081080000010400010000820000040000004082000000c0081042181c108001812008300202008300380102084000030038010718430200c08000410830030a106005003801c108030218198e5e9665491e428f6388ce268861483e0a7f5f87cde6785dc75dca6f5b86cdae6a5a465d92615785ad665855451d424d53048d1e445043fcf23b4e838cde344c42fcb2294a024c8e224841dc721945814c460e42c07c1a034008fec990ea8c01dcc73209318023fb24c08e70047f64d821c600abe4baa4a9c011fd9221d618023fd32c18e3004df65688586008fec910eb1c015dd931c5328033dac443a650047f64c8748600cf64930638c012fd96a21538023fb2643ac30067b208874c6008fec910ea9c011fd9321d62803ba8e698a430047f648874c6009f6c951098c011fd9321d528033ea42c08e7006774c5821ce00fa519c452ac01ee21188a66803ec423114ab007c68ce55912009bcca906a1401ed233846668025f32d442a70047e25d818ce009dcca106b1401f523384655802af12ea0cab0047e25d84486009dcca10eb14017999421e338025f32c41a850053e25d4199a00aceca10f19c019d8878cd418027b126c12c9004fc6448359200f5522445334013799520d62802be12ea0c23007f08ce2284600bb8ca90708c013e8984c6228026f32a41a41004de6548358200bccca10319c013e992a21318023f12ec0aa90046f650878ce008deca10eb1401f923384644802bb12ec0c67007e884622912009bccad10b0c019e887889418026f32a41ac9004de6548384600b6ccb10319c013f19120d428027732944261004fa64883592009f8c8906b1401f3211956448023f12ec0ac90047e25d8150e00
def x351l7 : Packing := (72,4,4,0,0,10,0,x351d7)
def x351h7 (i : Nat) : Nat := 0x5800
def x351d6 (i : Nat) : Nat := 0x21eda2a65831c600
def x351l6 : Packing := (1,5,4,0,0,0,0,x351d6)
def x351samples : Array (Bits × Bits) := #[(0xf1405419e53b37c1a894fcbc1efffeb7bd53e8398d5ed3ad216467c7af76bc05fe54e2f39df53ada7a917a78adaf781e9fa252df8b386939ff32fc9fdee774efbdbb1cdcb3bad3dff6c77536d060b50cce9c0517214644802008037b2821fc3b,0x10186c8a0003408822003510029010012a31544288021419e8722040019008e130612deb066324058262838128132044100224754422ad044d10d404e868a105a9124f65d02005b0891d349020950cce0c4096120641ace25ac94a2821263a),(0x60684bd3fdbc7429906c83de8bbf4bc1bf8c4695ffecff6a94d3fc9a851d39cce2e87757697f8a75bdfbbd77e57ddcff9ac7e9ffb86aff8df2b6bbcc7bcfab39df67afeac1c3c7e53fd1d24f6003463f032d55686431080404d7869bbe02401f,0x108c2825404000d00110000448842258880800334004501240400180080008102010840001014023020806854032c02306041920228c1008020e00022000100100004100a08d8000420424b4101403200a0b468c8910c400081220144004801),(0x2c9337c7e540d5b5c5daff3dda7a9a5e988319776abb9fe569bcb5206fd6af5971bf01f0b39deeeee6ccafab0ab8779ad4576f4a5bffde6962e6f285b5385e074eff302ccdf5ecf953b26531a455106ab5069859040d30cacc17848431038594,0xbe0000340a08b060a9cecd00133401803248231cc02490840ab8bfc1580a87044c960715444ca881851001020b44800dc4100c45695020101bc202031142600bc239400ed18704692813a430b074108db30648952766b3af5d149c9631438714),(0x6b6db5b70bffcedfdcabf7bed6f6f03ef3235dc6473b0e5dcd360f31daca66248115dd8c5fbb7797633ea20ed27bd126013f95b9e6dd1746571b0bcefb667ba0c6cfd7e0ec337fc69512a39a1d1ad542943baa105a0881fad9a86904417805c8,0x4050ca8840800a06001000540800400000000000020802339102400c82011840a300a0020900072002220a818039100220884200900292270000708004298480010007112e50008400080b820582c6320428820210884400824a4109403000c8),(0xb6d4b423cb9b4fdfda1b38b13eecff53cffb362e2a4522ff9eb0bc773829dbc37b167b69e65c0a2c55a257914f977d1b46324ee0f7201a37fd8df9795fc3476c85fa8e9eb063b6b2795c10c9e87d60c0789200475f56441001001d60c1fff800,0xb5ac24132425f0a113852780a3dc2c226655482a9131f5880614841334c243870c43048010f088c8e84514786c04e8019844b08302a10950d3b20f09a004015a9050a0001023865a47402049685520c131d21869ed708253150036b081ced800),(0,0),(0x3ddeacaf374ac7033721c1d5b791f113233e962ddce93163f3cbb6281f076792d422890e28c499b7a44f07e5eafffb6dfeba8e965580d79f135004a281d382936c70cd477afcaaea8ced7df00ac69a91206a41a284bc3a0522401164be840260,0x6c2025088998553042a883340831811003362b0c8818a01252e33280c4085832fd90260604c80310c2047b048098009183020c01510200313c0e100c050d8e10812821882000239c600d19b00cc68e81100a0106170c6306d242c5febac00260),(0,0),(0x87be8ccc0cac83e923542157b5079cfbf1e48685a772e4896e8a1af8b4ed6d364e0eb6e754b3319009a141969651876dfbabfd6771bfe695f84b04f7559cffa2a2c363a3925f312bbffebe2cf3bcb9c4e0c526d18090bb313aad700000840260,0x30f0013320620489c057009a0c20885ec48c4d155660c080c000c202894a60c000050b1b22198800d5004601644c7681004b15602f1254042600b21a050316050d39066512a98419042040cf239314c6ac56cf9a87298f92db53a0000040800)]
def x351columns : List ColumnInfo := [(529,0,334,0,7),(320,0,543,0,7),(4,0,859,0,8),(512,0,351,0,11),(12,0,851,0,5),(2,0,861,0,7),(537,0,326,0,4),(519,0,344,0,4),(840,0,23,0,4),(258,64,541,0,4),(70,0,793,0,4),(72,256,535,0,4),(514,1,332,16,5),(530,1,332,0,4),(836,0,27,0,4),(833,0,30,0,4)]
def x351autos : List (List Nat) := [[],[64,49,134],[96,132],[128,49,100]]
def x351levels : Nat → Packing
  | 10 => x351l10
  | 9 => x351l9
  | 8 => x351l8
  | 7 => x351l7
  | 6 => x351l6
  | _ => emptyPacking
def x351index : Nat → Nat → Option (Nat × Nat)
  | 10 => lookupWord 24 69 5 12 6 2 x351h10
  | 9 => lookupWord 107 435 7 15 9 2 x351h9
  | 8 => lookupWord 38 97 4 13 7 2 x351h8
  | 7 => lookupWord 1 3 1 7 1 2 x351h7
  | _ => fun _ => none
def x351 : Forest := ⟨863,10,fun j => x351samples[j]?.getD (0,0),x351columns,x351autos,x351levels,x351index⟩
set_option maxHeartbeats 0 in
theorem geomx351 : graphValid x351 (boundsBefore knownx191) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=2) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx351_10_0 : block x351 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx351_10_1 : block x351 10 1 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx351_10 : block x351 10 0 2=true := (@block_merge x351 10 0 1 1 sx351_10_0 sx351_10_1)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx351_9_0 : block x351 9 0 6=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx351_9_6 : block x351 9 6 31=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx351_9_37 : block x351 9 37 12=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx351_9 : block x351 9 0 49=true := (@block_merge x351 9 0 37 12 (@block_merge x351 9 0 6 31 sx351_9_0 sx351_9_6) sx351_9_37)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx351_8_0 : block x351 8 0 12=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx351_8_12 : block x351 8 12 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx351_8_48 : block x351 8 48 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx351_8_84 : block x351 8 84 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx351_8_120 : block x351 8 120 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx351_8_156 : block x351 8 156 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx351_8_192 : block x351 8 192 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx351_8_228 : block x351 8 228 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx351_8_264 : block x351 8 264 10=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx351_8_274 : block x351 8 274 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx351_8_310 : block x351 8 310 1=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx351_8 : block x351 8 0 311=true := (@block_merge x351 8 0 310 1 (@block_merge x351 8 0 274 36 (@block_merge x351 8 0 264 10 (@block_merge x351 8 0 228 36 (@block_merge x351 8 0 192 36 (@block_merge x351 8 0 156 36 (@block_merge x351 8 0 120 36 (@block_merge x351 8 0 84 36 (@block_merge x351 8 0 48 36 (@block_merge x351 8 0 12 36 sx351_8_0 sx351_8_12) sx351_8_48) sx351_8_84) sx351_8_120) sx351_8_156) sx351_8_192) sx351_8_228) sx351_8_264) sx351_8_274) sx351_8_310)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx351_7_0 : block x351 7 0 36=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx351_7_36 : block x351 7 36 12=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx351_7_48 : block x351 7 48 24=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx351_7 : block x351 7 0 72=true := (@block_merge x351 7 0 48 24 (@block_merge x351 7 0 36 12 sx351_7_0 sx351_7_36) sx351_7_48)
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
  strong_low (m:=863) (cap:=10) (hints:=12901687553) (nb:=1) (by decide +kernel) (plainA (q:=351) (prior:=boundsBefore knownx191) (before_sound knownx191 validx191) (by decide +kernel))
    (index_root (g:=x351) (i:=1) rfl (before_sound knownx191 validx191) geomx351 tablesx351 (by decide +kernel))
    (index_root (g:=x351) (i:=0) rfl (before_sound knownx191 validx191) geomx351 tablesx351 (by decide +kernel))
def mapsx351 : List (Nat × List Nat) := [(863,[]),(879,[84,131,98])]
def knownx351 := extendKnown knownx191 11 mapsx351
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx351 : Known knownx351 := extendKnown_ok (m:=863) validx191 lowx351 (by decide +kernel)
def f383S : Array (Bits × Bits) := #[(0x45d1830271014506932243be8409db65144e962aa6c1511945835860040800cf330d6c5fac0892681c6791daaf60a50a4519e2c1190f5cd281be24817a00cdac58f6980f0343030217100489410445fc242f42c0692344243281292bfa625307,0x44d083a001010100400240840010800510400eb8b501011005821820009800423b000447880882200c2300c00a00200a0019f0d00803401201ac0020c2000488585111340640a684045fc24d20044130200c4080682004043280292bba000305),(0xbe68c01f1e9e9488111829e89795291c0250656b4642af1012b8231b8a5379587e913a4042d6bc2ba10e488ff5f11e506044850bf6cbe1bb8ce1dac7a50c1a3c68d40b10c85286729980540120b91403b92e7c8f928fc048e12a178008d84820,0x8128400a0c84908815980108874a28000000200002460200002004180240601c4011b8000246180aa000080735611840e144010352c881a08800da4401880a242004268891b1104ba3003ca248a9040191222807820fc008812a120000c84000),(0x4a588255f2689ce3686efced88e113a84c1041c465388844ef696a13e4d33bfa75341010f302665192f1f7b35ae687ee2a2561720011882b5ec6440ca727a440407842100810d4680842801008107118d104d84045f82a96dd11ccd5cbb08a6e,0x2a508205f2682e374040fce000a11338141841446530c046ed414203249313e0152604109000664112503080488ae78e028162f00113080b53460400a02184484069d8736e0c2f2054bec251301071184004504045e02a124c11ccd5cb308a2e),(0x447cd844526958658f9f557f72c045ed2305b53d3a1234895d9b8072244660232ac1677d3a113d8265b4435a510331135d7c672ee4a674c288be5e418a3a558d81406004a4580c2046a0369a81270032f08617985c25af1ad82b242701a0d8,0x2079d805024080250703153c524045a0410481180a0010101e190040000000e200200169221130802480430250001011521c060c04a48480882016488022043882010480d3d0972841098c8701040030308614981c05a512882320040120c0),(0x3b8e270712e2fa7298f0dc6ae68f62e4752ff0057a9f7c4d8125dbe50d236faa10e24dbc0b3001cff74201f0a00bb21f4e843021bbacd96d3c5099c80385d7a38c2a8061058500040610202802e27074cfc2217305e20a42c24fb282442bd899,0xbb07040010e0ba5298f0986ac20d008044baf00442847cc42021c2cb15216d88046248300251084f43500930848b82c46e840021b38808694e5109c8016cd1638428eecb792c0968d3a0343258e23044cfc2216305c20a42c0479080402ad818),(0xab1b226465d50f6c0e5e2172cc62d5418aa5134b0af03fcc5e8c151a690eb795c304128137a87ae9e9d40214015ad0a539f00ba6d5d927e90214284e5c25bc433624340e0208010040090a804585088a4da103701b0e83a1412ed07d915c9cfe,0xb909684460308e4d0d0c3163c46245402aa5110302b01e0c5a0c859b09431305c044000027800489a15402100153582521e00b26c1082ee90200081e1c35fb4220268e0af9bf581ba90029908781008a0da10270130e83a1410ed04401549cfa),(0x7071ab189d3748415213f3f77a94a7d6b3d3afa2ca26be6af3abd93f0aaa93008ac2001387d540c64678593580045e2ec4e3961ccf00360c37cb0b2650532106e5bc0180f000209180a05140206a91ab0848a668fc649d5446128540d91733d8,0x38519f501132484362023275489483dcb1d31da20821b80adf8fd927098a83018ac600030d91c0c0005071108006462206b31e688500360406c100000013210085d29926684ece940855c35c870291aa084886687c60054446108540d91730d8),(0x0,0x0),(0xc612d8a9a8e50b390cc5aa8c43250ca384a12c50a1a4c1f66012646411ac81f280688eaf90c349906d9902e827be40cedcebcd9fc0f96715b94e57b0a179a49b8309248030282881602d0b46944baa504016392666007f19a4e4d0db222c2700,0x42840021004d1130808088880201002004004054210441e020402000142440f20019868c10440a02448900a82ca800c8c800809100e14112312216a0a1480439000160d10600216056aa142378482a504006390200007818a060009b22280300)]
def f383C : List ColumnInfo := [(880,0,15,0,4),(872,0,23,0,4),(866,0,29,0,4),(865,0,30,0,4),(864,0,31,0,7),(352,0,543,0,7),(856,0,39,0,4),(838,0,57,0,4),(833,32,30,0,4),(817,0,78,0,4),(802,64,29,0,4),(796,0,99,0,4),(788,8,99,0,4),(616,256,23,0,4),(590,0,305,0,4),(586,4,305,0,4),(583,0,312,0,4),(582,0,313,0,7),(70,0,825,0,7),(581,2,312,0,4),(577,0,318,0,7),(576,0,319,0,11),(64,0,831,0,11),(569,0,326,0,4),(563,0,332,0,4),(562,1,332,0,4),(561,0,334,0,7),(556,0,339,0,5),(553,16,326,0,4),(34,0,861,0,7),(544,0,351,0,11),(32,0,863,0,11),(542,0,353,0,4),(541,0,354,0,4),(540,0,355,0,7),(28,0,867,0,7),(18,0,877,0,7),(528,0,367,0,11),(16,0,879,0,11),(525,16,354,0,4),(517,0,378,0,7),(516,0,379,0,11),(4,0,891,0,11)]
def f383A : List (List Nat) := [[],[98,131,84]]
def f383d8 (i : Nat) : Nat := 0x7690800000c10321000f0800c840008200820006100000302000000000c080000001080000820082008200820082008200820082008200820082008200820082000020802080208020802080008400840084008400840084060400000003020018101810181018100010801080060400000000001d3f45c971bc4707b9ec7af69da4e739a6498a61f7fdf57ade1705b76b5a36658f6156556d5151d3d47513424e9324a92246912429023e8f23a8e2368d233ecd314bd2d4ad294a2a6a92a2a829ea729aa68196631825e1585392e438ee338c4290841e85a140460f0320a01e0500a0053bdb41cd9020600a7db6439b2040c012df6d4a89dd318031de4c34839c230063ec986887384600a67b6843b2a41c014d76cc876548380293edb14eca90700533db429d9520e00a6db6453b2a41c014dd6c4a7654838029bcd814eca9070043bdb42a2995ce00af63685032239c015f86c8a0644738025cf5db4843c67004b5db52a2778ce00b33b684c4ef19c01b729dda2242338021deda15319b0300539db42a6336060087db655532640c010ef6d0a8a65318021f6d91514ca630061bd97690870c600a67b6843b2a18c012ddaeda520e118025dada15119c23005b95b42a23384600b72b6843c6708c017f06c8a08ce1180327d554eecb0610066b996690710c200ade576cb42218401d3c9dd9684430802b6cdb14ec9821005759b529d9304200af336853b26084015f26c8a764c108023dcdd32839821006739a56507304200ceb34ac98e6084019e6691931cc108032f4cbb4439821006769956887304200cf5328d10e6084019f264da21cc108033d8ca342398210067d1936847304200abb576cbc6608401d669dd948cc108023f4dd0e6c90210056e9b61cd9204200aed36a39b24084015ea6d07364810802bf0d88e6c90210075ca778cd9204200acf36c53b2a41c015ce6d0a765483802bb4d914eca907005771b129d9520e00ae736843b2a41c015d66cc87654838023dcda1514cae7004f9abb690878ce009eb36a544ef19c017666d0989de338027cd5db4848c67006d9a77690918ce008f736854c66c0c015e66d0a98cd818023f4d9554c99030047b9b42a2994c6008fd3645453298c011fa6caaa65d31802af4d95333ba630065b997690870c600ae736843b2a18c0195eaaa77654318023f4d915319c230057c9b22a633846009de576d312708c013dcaeda520e118027f0d915319c23004fb1b42a23384600bf836454c6708c017e46d0a88ce11802fe0d912f19c23005f91b421e3384600
def f383l8 : Packing := (89,5,6,0,0,10,0,f383d8)
def f383d9 (i : Nat) : Nat := (if i<2 then (if i<1 then 0x911ce00dfc2a1911ce009fe69c988ce00dee690988ce009fe684988ce009fe2a5878ce00cfe261878ce00bee690878ce00bf668c878ce009fe2a6778ce00bf62a1738ce00f769dd738ce00bf669c988ce00fe6690988ce00bf6684988ce00bf6684978ce00bf62a5878ce00ef6261878ce00bf6684878ce00bf62a6778ce00bf62a2778ce00f7661e778ce00f762a6778ce00f76262778ce00bf669c918ce00f769dc918ce009fe2a57360600bee6907360600bfa6887360600bfc68473606009fe2a63360600df62a63360600f769de33606009feaa993206009fe6a48320600bde6948320600df664c8320600bfc68483206009fe6a573206009fe6a47320600bee6907320600bfa6887320600bfc6847320600df664e3320600df665e3320600f769de3320600bfa68a994c6009fe2a2994c6009fe69e994c600dfa68a994c600cfe660984c6009feaa8984c6009fe69c984c6009feaa9974c6009fe2a1974c600d7e65c974c600bee690974c6009fe2a5874c6009fe6a4874c600bee690874c600bfc684874c6009fe2a6774c600d7e2a6774c600d7ea66774c600d7e262774c600f7c286774c600cfe261834c600df6a64834c600f769dc834c600bf62a2334c600df6262334c600df665e334c600f769de334c600cfe261814c6009fe6a5714c600dfca65714c600ff428d714c600ff420d714c600ff48cd714c6009feaa9970c6009fe2a1970c6009fe6a4870c600d7e65c870c600bee690870c600d7e65e770c600dde6a1950c600dde69d950c600dde61d950c600dde21d950c600dde9dd950c6009fe68c98846009fe2a58384600bde6948384600bfc68483846009fe2a57384600afe6a07384600bee6907384600bfa6887384600bfc68473846009fe2a63384600df62a63384600df62623384600f769de3384600ff48cd8184600bfc2a13184600bfc69d3184600f7c9dd3184600ff420d3184600ff48cd3184600bfc68c9884600bfc69c9384600bfc2a58384600bfc69c8384600bfcaa97384600bfc2a57384600bfc2a17384600bfc2a63384600bfc2a23384600ff460e3384600ff45ce3384600ff42a63384600ff42a23384600ff42623384600ff429e3384600ff425e3384600ff461e3384600ff421e3384600ff49de33846008dfaa99520e008ef690988ce00ae7690988ce00ae7690878ce00bf2688908ce00add69483846009beaa9960c200d3e9dd960c200dbc65a110c2009f6aa99304200d7665e3304200dd66563304200de66523304200d7a9dd9204200df28cd92042009deaa99520e009fcaa9911ce009ee690988ce00be6690988ce00be6690878ce00be6690918ce009fa68a994c6009deaa9950c600d5e9dd950c600bbc6989384600bdc6948384600afc6a07384600bec6907384600bf86887384600f749de3384600 else 0xafd6848384600cf72623384600ef58cd8184600afd2a13184600ef520d3184600afd68c9884600bbd6989384600bfc6809384600afd2a58384600bdd6948384600bfc6808384600afd69c8384600afd6808384600afd2a17384600bed6907384600bf96887384600bfc6807384600afd2a23384600ef560e3384600ef52a23384600ef52623384600ef561e3384600ef521e3384600f759de3384600ff42823384600bfc68c9084600ff48cc90846009ef692994c2008ff2a1974c2008ff6a4874c200aef690874c200af768c874c200afe680874c200af768c814c200bee692994c200cfe2a1974c200d7e65c974c200bfa688974c200afe2a5874c200bee690874c200bf668c874c2009fe2a6774c200afe2a2774c200e7e61e774c200d7e2a6774c200e7e2a2774c2009fe6a5734c200afe2a1734c200df665e334c200ef661e334c200f769de334c200bde694914c200dfc644914c200bf668c814c2009fe2a5714c2009fe6a4714c200bee690714c200bf668c714c200afe2a1314c200bf6aa9314c200ef62a1314c200ef661d314c200f769dd314c200ff4245314c200ff45c5314c2009fe2a6114c200ff44c6114c200dfc2a6114c200dfc65e114c200efc61e114c200f7c9de114c200ff428e114c200ff48ce114c2009feaa9970c200d7e65e770c200dbe69d960c200dbe9dd960c200dbe685960c2009feaa9910c200d7e9dd910c2009fe6a5710c200d7e65d710c200dbe659710c200dfc645710c2009fe6a4710c200dbe658710c200bee690710c200dbe65a110c200dfc646110c200dfc65e110c200f7c9de110c2008ff2a193442008ff6a48344200adf6948344200afd6848344200cfe2a19344200df664c9344200bde6948344200bfc68483442009fe6a573442009fe2a573442009fe6a47344200bee6907344200bfa6887344200bfc68473442009fe2a63344200df664e3344200df62a63344200df665e3344200f769de33442009fe6a53144200afe2a13144200dfc64e1144200ff48ce11442009feaa99304200df6aa99304200df669d9304200df629d93042009fe6a57304200dee6517304200df664d73042009fe6a47304200bee6907304200dee6507304200df664c7304200bfa6887304200bfc6847304200d7e65e3304200dde6563304200dee6523304200df664e3304200df665e3304200f769de3304200dfa9dd9204200dfa5cd9204200dfa1cd9204200dfa8cd92042009feaa99720e009fe6a48720e00bf668c8720e00ddeaa99520e00dde69d9520e00dde29d9520e00dde21d9520e00dde6859520e00dde2859520e009feaa99120e009fe2a2995ce009fe686995ce00cfe660985ce009feaa8985ce009fe684985ce00cfe261835ce00dfc644915ce009feaa9911ce009fe2a1911ce00dfcaa9911ce00dfc6a1) else (if i<3 then 0x78cb264a31d98b0c3a60e2ff97c0bd65dc2e696d0b4a5962c395e0ad25642aa9518a6e52828c9428a0a50027d93d89e24e2269933897e4ba25a92c09564a6250927092e49224191f88f247423791a88ca45622891308523f21e78eb07123661a18c805fa2da15b8a504e224e11588203ca1c20cf85f02c613608983c01ae0b404881b80960009ffaa99720e00aff684985ce00aff2a1915ce00cff261915ce00aff684878ce009ff2a6778ce00affaa97360600aff69c8320600bef6907320600bfb6887320600affaa97320600cff5cd9020600cff1cd9020600cff8cd90206009ff69e994c600bef690974c600bef690874c600aff680874c6009ff2a6774c600aff2a2774c600cff262774c600ef79dc834c600aff2a1734c600cff261734c6009ffaa9970c600aff69c8384600cff2617384600cff2607384600bef6907384600bfb6887384600cff2623384600aff69c814c200aff69c8344200bef6907344200bfb6887344200af768c8720e009dfaa99520e00cdf21d9520e00dde6819520e008ffaa99720e00cdfaa99520e00cdf69d9520e00cdf29d9520e00cdf6859520e00cdf2859520e00cdf6819520e008ffaa99120e008ff2a2995ce008ffaa8985ce008ff684985ce008ff2a1911ce009fdaa9911ce00cfd6a1911ce00cfd2a1911ce00dfc681911ce00dfc281911ce008ff69c988ce00cef690988ce008ff684988ce008ff2a5878ce00aef690878ce00af768c878ce00af72a1738ce00be7690988ce00af769c988ce00ee7690988ce00af7684988ce00bf6680978ce00af72a5878ce00be7690878ce00bf6680878ce00af7684878ce00af7680878ce00af72a2778ce00e7761e778ce00e77262778ce00be7690918ce00bf6680918ce00bf669c908ce00f769dc908ce00bf6684908ce008ff2a57360600aef6907360600afb6887360600afd6847360600afe68073606008ff2a63360600cf72a63360600e779de3360600adf6948320600cf764c8320600afd6848320600df68cd90206008ffaa993206008ff6a573206008ff6a47320600aef6907320600afb6887320600afd6847320600afe6807320600cf764e3320600cf765e3320600e779de3320600cf78cd90206008ff2a2994c6009fb68a994c6008ffaa8984c6008ff69c984c6008ff2a1974c6008ff2a5874c6008ff6a4874c600aef690874c600afd684874c600c7f262774c600bf6680834c600cf7a64834c600e779dc834c600af7680834c600af72a2334c600cf7262334c600ef520d714c600bbe698904c6008ff2a1970c6008ff6a4870c600c7f65c870c600aef690870c6009dfaa9950c600cdf6a1950c600cdf61d950c600cdf21d950c600d5f9dd950c600dde681950c600cfe61d900c600d7e9dd900c6008ff68c98846008ff2a58384600adf694838460 else (if i<4 then 0x842080c08c41020a1001831080e0a46100181030206041400840605110888060802110511804105002102801080208041034207040e08181020b1188020c22105002101c100420084010802100420083420042040401081c10302008400084130800010402110401040308041030206041308181000210002100000010a100000010a1000000042018403088801880c080006040e081c1038207040c144401088200820104020a241414201440c1018103020604007040d1104060413083aa081c1210511109b48844213691908100000000000224188c2021051100006860508021004200840108021001010042040a22004200840c082010382000420104020804100820604000000288612082120800000000001120800000008904007579688c7cf819cb03211979fe58231809d510a3e589a08c7aaf2c518c1486a2318290d44630511a48c628c35090c514691218a28d22431451a448628c35090c5186a121babcb44631120588c7cff2c118f96e7c231889d510a3e7c921025cb73fd3101d88e1218a311c243e7ca316abcb14631108528c62210a518c44214a31a2442a0bcb73fd37547ffcff83f8ffaefcafdf3ec7f4af9dfcb3e27efaf6bfafbd4be8cf39f8f3c47e00ef3f763b7fda6ec6f5d3ab7d38e94f46ba03cd4e5df28b913c70e30f0fb85fc16dfeef9376fb9edbded6367fb1cd81ebab58fab8d4fea1b4efa68d27e8db43ba04cf5e77339b9becd7e683323982cb9e5932ab946c96e47b21f90ac7de3db1e38ecc73e313157892c3ce18308f838c19e042fef7e8bf1df2af4f784bb5dd4ae73716b7edb92dbf6d0b56da02ccf644b15d84abdf5ccad4d66ab03572ab1d52aa7752ca89d4129c34bea52d2328fb464a20d07a81f4009f8cfb27a73ba9cbce226f33749b2cd5a68f338999cc9262b30697bcb7a59f2c0958ca8a52728493fc9ea4d7266930c97249b248917c8323d31c68d6c6522f716c8aec56229313a890c4221f30ea872c3821b70c2859c29213f090840c1f20c705481dc08a012ffa7fabf99faefc87e1bed1f4af967c8be09efaf6e7b4bd69e96f4679bbca1e32f0a782bbb1da6eba750ba49d06e74732b981cb6e5671eb869beedde6e7b729b76da26bfb5c1ac2d526a1b4a9a36d0c683b3e19e6cda665b2f196eca864cb2298e2c62629b0e982ec085f7af5978ebb85d4ae69716b7c5bbad7969eb40593ac61612afa575ab7159aab4552aa5950ea78534a9694aaa4651ba8c945aa1e502a7d93ce9d84e4a6e935699c4cba6213069744b7a5a92ca9604ada53128e94249ea4e126692448fa46922a910480a3c91c68ca45da2d91628a2449a2110ea866426a0d104a8164039fe0fd27e43e59ef0f5a79e3cc9e28ee27623a99d38e7e73038b9bf8db66cc3639b08d7a6b83599ab8d526a434f9a40d0267c33199 else 0x30206002203001100205880100840081820040c101a0088030806100402101800880004c19180206080303040704e20642710064205006818500c0d100606ed230000d101a104c0b1018008801034401002203001102009832300820104010304009090d01a403001100401880200c40083220202058020c8c1a081a00881702040081020681b00419203204080e05c0118440b81030641310140603230800110320988040081318061084031004098a040804101c1710320b881905c40b81820700c100210043cb040c0818104c242840c08061214201040321040184840801008000001600832308403104201882200c40c806205c0c10181001a0703230641310261001c06081102413180801026308002104001080204c41000e0c8c0c4444012082002010640c04c7cf01810026404c0e10080b826306413101c09882800c0c1ed20181830136904c6070451030407040e082206080c081c1034131754101c01064603832030c07064413802202020c8102044170406038020c8c08081010342002410102608080803819181c104020038207040c082410020102024d040108184d08010806100c201840c0a22100111080002682005c1910160083230680706461104e060c0403040203220880c1046100420e9820084622104221082210242040001080d08010a34104461e98201100c100412101a104842084421040604006040c0c241001812442288408d041b284091840108001080210282070400688821440d1028050844034400840108021028200001904c40d022060c0f02c19180809880c08396088809880c06851180212102420484088)))
def f383l9 : Packing := (452,4,6,0,0,13,0,f383d9)
def f383h9 (i : Nat) : Nat := 0x2a199ef1aa890ddc96b816d33d0000526c6c49e20a3a200070848c38bb0fac080000074cc6b68682a0214a449506a2070664d68003e5e8e0000002d6000295c28da48002830001d806ac110000006d1b9980039f29849780005488ea9080021d052b9b04b91f82c5509990d7b9330b00041a16461da039a7f0f6048000006a591898cc239047828287540000004e98000058000972a600042aa81da0aa052b487b1cc53f80b8a88d21c00039b809b523050926167a71867143cda12a4c5139020002e54ebd148406471233648a29a9500208cab910458a250918a0000c830a0080d0a281009e0c60436007090e004030a00000000810318fca880008083
def f383d10 (i : Nat) : Nat := (if i<2 then (if i<1 then 0xec1a63007f720d31803fbc6698c01bfd814c600ffab8a63007fe64131803ff12098c017fd970c600dfec3863006ff21c31803bfcee18c017fd900c600dfec1c23006ff20e11803fbc6708c01ff53184600ffa4c423007fd24e11803fe90708c01ff57384600ffa39c23007fd8ce11802ffd32984017fd974c200dfe43a610077f9dd30803fbc6698401bfc814c200fee98a61007fd84530803ff2e098401ffa994c200ffccba61007fe25d30803ff10e98401ffa774c200ffcb9a61007fe64530803ff12298401ff8814c200ffcb8a61007fe1c530803ff26298401ffa114c200ffd3b861007fe5c430803ff0e218401ffa110c200bff4ca21005ff64d108037f90688401fde3344200ffb08a21007fe4c110803ff53288401ff99344200ffc49a21007fe20d10803ff2e688401ff87344200ffd19a21007fe4c510803ff2e608401ff87304200ffd19821007fe21c83803ff532b9c01ff9985ce00ffc4c2e7007fe60d73803ff322b9c01ff8915ce00ffcc3c67007fe21e33803ff4ef19c01ff97360600ffc39b03007fe8cd81803ff10640c01ff97320600ffc39903007fe8cc81803ff53298c01ff9984c600ffc4c263007fe65d31803ff12e98c01ff9874c600ffc43a63007fe9dd31803ff30698c01ff9734c600ffcc0a63007fe5c531803ff30e18c01ff8870c600ffd3b863007fe60e11803ff10708c01ff97384600ffc39c23007fe8ce11802efb2a41c017f99020e009fecb907004ff644838027fb2041c013fc985ce00bdeca0e7005fb64873802feb2239c017f9901ce009fe4c467006f760e338037b93119c01bdd878ce00dee43c67007779de33803fb12119c01bde3360600bfcc8103004ff64c818037bc6640c013fd90206009fe4c263006f720d31802efb2a18c017f9900c6009fe4c423006fd606118037e93108c01bf58384600dfa41c23007f58ce11803fe12108c017f9974c200dfcc3a610077e9dd30803fb46698401fd9314c200ff908a61005fe65c30803bf4ee184017f9910c200ff908861005fe64d10803fb46688401ff21144200bfcc9821007f68cc10802ff32e41c017f99120e00bfd4cae7005fe26173802ff32239c017f8988ce00fecc1c67007f65ce33803fb13119c01fd8978ce00fecc3c67007f621e33803fb4ef19c01fd8918ce00fed19b03005fe64c81803fb46640c017fa994c600bfc4c263005fe65d31803bf4ee98c01fd8834c600fed19a63007fc5c531802ff32e18c01dfa770c600bfc4c423007f68ce11803fe30308c01ff13184600ff84c423007fc24e11803fe30708c01ff08384600ff8b9c23007fc1ce11803fe46708c0137d9520e00b7ccb061005ee65010802fb326084017e99204200bbcca907004fe66073802f732839c017e9921ce00bf8c88e7007769de33802ef32a18c01fd23384600 else 0x8886291e9b5492429d359f11a48812cb41755128d18899f0d6982452898a359fd3448c2828e7e25232265b4c23d5288823cb67f541a0969919fd306b2c12d518251ab4c4b3e44cb69a47aa50532d9f11923596cf9460a2330173fa611e5b546cf86824232144891acfc8e24622188349ad367c24728c15471acfe9a24742a8c249a22173fa63126824642e7f4ca30915359f0928c814cb21547aa09268f554d1472d9f51980a8551a6b4d96cf9475492226824855196ab12cb67d0aa3306b2c231850342318682420d04841a09093e1acb08c81a0288c60511880a2310144626a8172d9fd36a90b2340744612184aaaa3cb6ab3fa68922bfbafb6bcdaeb6b8dadb6b4dacb6b0dabb6ac4aa92a7ba94aa32a84a9f2a74a9a9a602945a4728f3a32a8a1a176834a05279a9d367249bee6c09a82689995e63797aa5b8968658a95aa55394ce513931a49491664158fb23d58e2235f8c4a2ce8a4e27c894e221879a1ab862e15084c2119837a0b5827a07e80ea0087f7dfbf7e7df6d7cedf1b7c11eed7b35eb67a7de767959e2d7811dd276c9d9b7581d37745dcee735dcc072a5c9271c9c5b7111c2d7059bf66f59bbf6e7db7f6da1b516cc5b086b7daad6a35a766959a3f687da1167e99ec67319b5667998765c195064e591963e58eb632d8ab627587d617583460757fd5f997cf5ee17985de17585d0572a5c4d6fc5b4d6b35a2966a592962a58295ea574d5b3567157c559554554714e152bd46250793da4e113644d113244bed2ae49f124148191d4461d16744b110342fd08d4148fea3e98f7d3d50efe3b54e9a397ce2d3780dc93638d5c33f4cc231f8c1f2fd8bc42e6cb692cb8ad82a74a7d2950a2227c0991253492d23c88c0221485320cc7ef1ed07701d1c70c1b6869f19005f316e055914c04f512e849111584120f383a50da83380c3c2cb0a4023a08201cd06b418d05d815f052011f03fc0e803440ba01b404d0003ffd32b9c01ffc985ce00ffec8ae7007ff24573803ffb20b9c01ffc878ce00fff3bc67007ff5cc81803ff8e640c01ffe3320600ffe4ba63007ff21d31803ffcee98c01ffd734c600fff3b863007ff5ce11803ff8e708c01ffe3384600fff3ba61007ff5cd30803ffae298401ffd314c200ffeb9a21007ff1cd10803ffc66884017fd9720e00dfe43907005ff64483802ffd32b9c01bfd985ce00bfe4c2e7006ff261738037fb06b9c01ff9905ce00ffc482e7005ff64473802ffb2039c01bfd878ce00dfe43c67007f75ce33803fb93119c01fdc978ce00fee43c67007f79de33803fb92319c01bfd7360600dfe39b03006ff8cd81802ffb2640c01bfc8320600fef19903006ff5cc818037f8e640c01bfe3320600bff4ca63006ff66131802ff93098c01bfc984c600bfecba63006ff61d318037f90e98c01dfe774c600df) else (if i<3 then 0x682c34d02089229a080501a0c465b549a0c9018190580489111060081406181805118c2801101428230484ca230c80c69511041340e140342e802034440c00940a9a118934201a690a301a684034d2146104d24861388e5b541a058423481105026210194071a00888201730301c0311c6834133834220e0c90211a1034220c0ce7f4c1088a022191000880d11044219f8880840806070219f10050267088a1341a09830c19098845aa0704c80d0903034132845342811024266025a4260342030c12b4c686284d044340c09982819098e3423100c508411068266028341813208f542096a8503cf83404140c88c2470a034221708142201038648108d4486120806460208a682610282c441107064a108d4486124d08a29a104934a3185134202a6841201a690a4aaa6946311c6832172068211a0c91081a020303250a48a3430a08c40c0106922110c9844140c84c81491468605118683240a08c41ad30835a61110342425948830288c5a6118835a61068482cab56ca30d2104830908c491118906148d11060d0a088801105234511c682419081012230c84c9965100444192842231a1844282118682430a0484130d0486100e58c42ca84881a420f2a62108c24228c444020a08a262890c88011004c44418300a2318042140288c60c0288c6010b54c49a1910c4851912466242902996111006141c68c42288384518888881a010ca262890ca262d50c25aa108f542096a8423d5082612118a0844425a4684b48488841408c2430288c2431408c2430288c24306850a23220044518911069a28894662288e22511110a2851989465189113e19cb020461a31132c510d08ca118d0101b96cf804468088103396cf84c467020441819cb06846708eab4c041167f2c0b0ca40605118c0605118c2605118ca2190288c8114d010199fcb0644684265922234d15229acfe59082330152baacb2453460208b55a64295aa05cb67f4daa42c8d19611a686128244b55968d1888620d0488040986b4d9f06048e111169b3f1228104413080682460208b541acb0441f9fd306426b0a0383396cf84c4670e820461221133e23091008224d06833a6cf860249422893412221145a6cfa682460a2132daa08a68d5508e5b3ea3284aaaa3cb6ab3fa68920249a165b54510d69b3e62208b55960d15ab658d44b2c44cfeaa47a650522596cfc144660d08f2d9f0969b5476ad963451cb4173faa91e99596288684640a1132d238d172c440d08c81428e5a35232e5b3e4411eab4c609414c596d546b3fa689242905cfe9a4612311034121944471a8910a39602e7c4650967c89961194505191c174c44cb67c47aa51472daad3014479f38a00a23194535962267c466cb21524234d148996cfa692423324b2d9f4288ca9a11a146056ae590baa49268e444d18b55a6429 else 0x2e030600489a0814460c1a6820011804329a1804321c1834060c1c682619180c261918383217180f541307105019098c19690900c805098304640c8041038884c3230104c323098641c30c8041217206446148d102e0d8d0502619303032211192231a080648020980c3240c8382017265826100088c351a388816010c902419098f3fa6118302796d50644e080))
def f383l10 : Packing := (262,3,6,0,0,14,0,f383d10)
def f383h10 (i : Nat) : Nat := (if i<1 then 0x26ce0001676d3256269113097a22221e0579d3c9c4082816058bf11718ec21a60cee4853206a05f08840438c000210e34480001130636c0d7dba0003c758abd7b30003404b9c371e466800000035590aad012bb54000f0a4000c028000d224000000017f0003198000000008ef61046c4778f88145fe344c2142bc00000000000001d398a54000cf0000000018e2ae94125fef54521dc5956c39ea84354207ac0756b5e4d6c66aaf66c3c2ea29fea4e2d24c4ec7f4259cefb5deecc7428f03fa1cab4a022b724627b7bd45a47892c7197f69419be4cb166a20400082573a9e3c87a6a98e109299c9ade94392fd5c4522d50676be498000754514c00000003e539b21056033e0164613620000000041000000009ecb19f19c6dab0001fc2000132d23efe019e84000792ab8d867a8ea000000000035141b53a4f0001f7900000002afe5acb21b361ecf638798f7ba4306644ae9df8a83309856b66737cc53ea3ebe4f81fbacd79276bfcf035278bdf1bf051060e15c000310b806e5bc62e206da529e594340026222cad78c685301ef81b618dca8a418bd20950143d56986bb5ea1c6eb8e1cdf149eb0c8240000a9d381e0001f022b28000c0daea07a728466444000a5361550000000b197e3f63177b8b397933e3e0c01741400000035a183f5e55532f4d46c92447c01e6cd86110e4994efb6ea2400043e959d0a8470ff12e82700000004db84f14412b2c6c497350003ae4f0c80008174d8b5d8fa51b2680009828000924c000b50957db071f647333c40e106079ae80000b122c5e84fd129f06051cc2f9e803434a9daa78a232419450f12515823d7a12cc5c50364b08eb8dc1262e1d05632c8e907598551bc5e58433521cd8e4dcf3863673901bda96c30c4fb9dd74000cd9c00000017bb000300f2e79902828bd7ae06b0726edcc600003a210002d1f32b70130001a2b2b119a00e1408fcbeb5740000374913c725a421842ae184b40000000000296a640348ab671b1c6f07416f1c4234f23400053e7a68661e809cac3daab2a90b2768e4c616ef014c1a9817f4c76debaf3355d5b6d68e0bf97ee3284ff34548e0f2d5d75a6188e30a1b1700000cfe08f0000c01ab91cbd18384d5c25c1b0834b00010bbb54c000d0c3c20000088e0a080009538000b038000a13800000020e8beb67bf43206001a04003100c00b2e6401e5478300020c62c08408000c041001c2c68008c4184002c0021c80581021c4835010087320c08406200120a0c18400400000000101000008008040a71c0c00b72549823e0088902940801200cdc041c0118048003066408e0200080120008618b4b8400a0090360400304041040094d0000009802c100803a74021001c099041c108045c083000020a0054001020c30502cc0880400102041c309001c5a22c000810e58612 else 0x5a95ed32d7a5ae116a8c70000000000106433cc8990002346ba4a283cdf68a92b2694600029c3ca8b02db3de06cb568000abd687c0000000c5e0498f492c82e2b9e7df65702e0000857cca8000cce40001a9c00050e7f653150ae000025183089f6092ce4fc28abd348d3fe949c2cec0555092e0000d7c5a2348530f330162ad57300006a60cae0119af8000116c000000215bae9f4c3a9cf24366c2f1d960a119bd88000d4e30230000000b50e38ea1640000000000b34f89111365b594fa4acaa2cea300019676a599969a92bb0f302a1a6c3580b669c3ae02e6eb6fde800000022020003c24cc2b1b4980d94b33d2d28051d47b2e8b50fb6fc8db7c6e06b9230000bae95b3894a552000000080e8136e156fba8160000000000095a4ce1837813a0443d3b0001002080318aa617144384f9a2a39921f44ada2c3e3e36fa3b60dac09754565ed863f44c98036930e9126d754f589b53a836ccf000000074f4f2600000008371ed6b958e3073740000000e750002445521272181fae3392dc00090328eea5dab7ed57f75cbadc2c1000)
def f383d11 (i : Nat) : Nat := 0x1996231a2090d4fd34b554d0291a4680c148c80a2435352d3e467121a102b48d0953554b4f9189a86864427c8c48c0a4634333f4d3424805122319aa96211a40291884b5509890d2010a4448e5aa868e352d3e46455a6aa9f969a2338211554b090d1a9a7c68488ab2d553f4d342470565121aaaa6969f234cb0d118c148e5aaa7e986849034242056912aa96231a38d4b4f9190684a5a7e9aa8148d0340a4631205969f2328291cb55090d1a7e98684880ad234472d553f4c2491a9f231220291cfd30915569aaa5a7c8ccab2d553f4c246cd787afcdbcb4f54a8ecd892713a08bec75ede9aab18596ab934a5442e7c8d69902c64b8848bc12e1a81a800ffc83803ff5ce00ffc73803ff8ce00ffc81803ff4c600ffc31803ff84600ffd30803ff44200bfd83802ff20e00fde33802ff60600bfc81803fd84600ff930803fe0c200ff910803fe04200ff983803fe20e00ff973803fe1ce00ffa33803fe60600ff881803fe4c600ff831803fe84600fda33803fc84600
def f383l11 : Packing := (32,2,6,0,0,11,0,f383d11)
def f383h11 (i : Nat) : Nat := 0x12f1f2ec000f2f0a4cd82123539be64391d362aea4f8099bdaebaeb5746b73aaa50e254ed02145025f0f54907a08000000249ecbb48ae32ac0f2c2aba5a23142a4724beb300006f518bc8284af5e0f00018d352e94bd01e400070e28dbd189a144a1b4d04a7c0005c0bc4899084dfc82b6e863b4000bae7a34994e6647b13a22696dc30b3000000000ee3f26782b8a83ccc5324a15017728b20f8c3c028f03be81081bdb85875f83800c198cad64c152181a3ca5c60864c75063c829b52290a09a8f3615f0cf602defe1b6968083c2600189fc69000188b7b2ee16310ccf881434f70001a059a46c1938444a7512d4c8ebe645459980001ac82caa22b05f89a42993bd3efd1b7f65819160390002af800012855b9848748de6d3e27000063740006a60000a292cb2c08044e79e06252a3a09dda264b90002c0a291de1e000000031b0000d19c837b1fdac9e3ef0cee9a00005077a6e9bfc000031060d99fe0c6b2a1688fb88e62f9deae5cabbc700001aa5a9b1098ca6c0001a2b4f99884000000182938ffcb8000287ab037e090001eb5f8c8cd4000009b805829a0001eeb00020a600006fc69f185b0000000f3c747100030a00000000b04667d19380a5a1780008070c330003e2d115aeac000323e49180000003a7b0002cde0000c68d1b8000dbcacfcdc07466f050000093fd00000244d784000023940007b6f4539996c962250000888f08e19d8000501525422ffc9f33ea6410001e330002b037a1f2b60000000aac1a4400038619b2000000022bb8bdc2e7d0e8c65328aebfb0a92920002c8f42c76a3b1db2e4f16bc4982db032f1fbc3fba10408d948cc112d5e26000126bb0d88350002ad252696953337659f364000d1ccc6f3bbf8600b0e4ecaa04000c84b8e0fc02a40eadc2bee01e61d09ebe962c1226708baee071b5c429aa9e796308ad1000102c232b8d59abfc04f006012bbb8000000324d0a5f60281544100001423c3580005a50efa1aa4000eb7881fd80fc24709c0000000e8de9c021a90c66d853680ad0003a7e4a7ba13e2b00000003844f8d8a8322bc6061bce84a700263b88e4ae93370a6a8ad2a9ce0880000b5c4722286a8c52fb4f46ae3e17000140070007c704b00000020c740bdc400208000c000880012000004d8e112084414010e80c000000168060000000e200000000008098000c220204400370703c00000282000020080000002580800000a82c0000000002000070000000048005a000007c0a0b00000040a003095004000c400070000c001b0080414000000000003000000000000000128608800010b1dc0000
def f383d12 (i : Nat) : Nat := 0x1f4c5951a2963e99512103ff007fa00
def f383l12 : Packing := (2,1,6,0,0,6,0,f383d12)
def f383h12 (i : Nat) : Nat := 0x1ba000004d4000000029d8ad7c0027e0064954565f4c5a1dafaf61c6d304e003154a18e7b773f000138ac4b2c17580bfa7f3800070000017e42e21d4200000c0deeb9ddd8cd082996a17801d5800ad00000000fd000004023280e41080010022c4480
def f383levels : Nat → Packing
  | 8 => f383l8
  | 9 => f383l9
  | 10 => f383l10
  | 11 => f383l11
  | 12 => f383l12
  | _ => emptyPacking
def f383index : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 41 145 7 12 7 1 f383h9
  | 10 => lookupWord 202 713 7 14 9 1 f383h10
  | 11 => lookupWord 130 458 9 14 9 1 f383h11
  | 12 => lookupWord 19 69 5 10 5 1 f383h12
  | _ => fun _ => none
def f383 : Forest := ⟨895,12,fun i => f383S[i]?.getD (0,0),f383C,f383A,f383levels,f383index⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geometry383 : graphValid f383 (boundsBefore knownx351) = true := by
  simp only [graphValid, Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel, by decide +kernel⟩, listPieces_all (d:=3) ?_⟩, by decide +kernel⟩
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem verify8_0 : block f383 8 0 24 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem verify8_24 : block f383 8 24 24 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem verify8_48 : block f383 8 48 24 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem verify8_72 : block f383 8 72 12 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem verify8_84 : block f383 8 84 5 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem level8 : block f383 8 0 89 = true := (@block_merge f383 8 0 84 5 (@block_merge f383 8 0 72 12 (@block_merge f383 8 0 48 24 (@block_merge f383 8 0 24 24 verify8_0 verify8_24) verify8_48) verify8_72) verify8_84)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem verify9_0 : block f383 9 0 24 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem verify9_24 : block f383 9 24 6 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem verify9_30 : block f383 9 30 24 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem verify9_54 : block f383 9 54 24 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem verify9_78 : block f383 9 78 24 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem verify9_102 : block f383 9 102 24 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem verify9_126 : block f383 9 126 24 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem verify9_150 : block f383 9 150 24 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem verify9_174 : block f383 9 174 24 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem verify9_198 : block f383 9 198 24 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem verify9_222 : block f383 9 222 24 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem verify9_246 : block f383 9 246 24 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem verify9_270 : block f383 9 270 24 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem verify9_294 : block f383 9 294 24 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem verify9_318 : block f383 9 318 24 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem verify9_342 : block f383 9 342 24 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem verify9_366 : block f383 9 366 24 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem verify9_390 : block f383 9 390 24 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem verify9_414 : block f383 9 414 3 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem verify9_417 : block f383 9 417 24 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem verify9_441 : block f383 9 441 11 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem level9 : block f383 9 0 452 = true := (@block_merge f383 9 0 441 11 (@block_merge f383 9 0 417 24 (@block_merge f383 9 0 414 3 (@block_merge f383 9 0 390 24 (@block_merge f383 9 0 366 24 (@block_merge f383 9 0 342 24 (@block_merge f383 9 0 318 24 (@block_merge f383 9 0 294 24 (@block_merge f383 9 0 270 24 (@block_merge f383 9 0 246 24 (@block_merge f383 9 0 222 24 (@block_merge f383 9 0 198 24 (@block_merge f383 9 0 174 24 (@block_merge f383 9 0 150 24 (@block_merge f383 9 0 126 24 (@block_merge f383 9 0 102 24 (@block_merge f383 9 0 78 24 (@block_merge f383 9 0 54 24 (@block_merge f383 9 0 30 24 (@block_merge f383 9 0 24 6 verify9_0 verify9_24) verify9_30) verify9_54) verify9_78) verify9_102) verify9_126) verify9_150) verify9_174) verify9_198) verify9_222) verify9_246) verify9_270) verify9_294) verify9_318) verify9_342) verify9_366) verify9_390) verify9_414) verify9_417) verify9_441)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem verify10_0 : block f383 10 0 13 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem verify10_13 : block f383 10 13 24 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem verify10_37 : block f383 10 37 24 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem verify10_61 : block f383 10 61 24 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem verify10_85 : block f383 10 85 13 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem verify10_98 : block f383 10 98 24 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem verify10_122 : block f383 10 122 24 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem verify10_146 : block f383 10 146 24 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem verify10_170 : block f383 10 170 24 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem verify10_194 : block f383 10 194 24 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem verify10_218 : block f383 10 218 19 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem verify10_237 : block f383 10 237 24 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem verify10_261 : block f383 10 261 1 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem level10 : block f383 10 0 262 = true := (@block_merge f383 10 0 261 1 (@block_merge f383 10 0 237 24 (@block_merge f383 10 0 218 19 (@block_merge f383 10 0 194 24 (@block_merge f383 10 0 170 24 (@block_merge f383 10 0 146 24 (@block_merge f383 10 0 122 24 (@block_merge f383 10 0 98 24 (@block_merge f383 10 0 85 13 (@block_merge f383 10 0 61 24 (@block_merge f383 10 0 37 24 (@block_merge f383 10 0 13 24 verify10_0 verify10_13) verify10_37) verify10_61) verify10_85) verify10_98) verify10_122) verify10_146) verify10_170) verify10_194) verify10_218) verify10_237) verify10_261)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem verify11_0 : block f383 11 0 2 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem verify11_2 : block f383 11 2 20 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem verify11_22 : block f383 11 22 10 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem level11 : block f383 11 0 32 = true := (@block_merge f383 11 0 22 10 (@block_merge f383 11 0 2 20 verify11_0 verify11_2) verify11_22)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem verify12_0 : block f383 12 0 1 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem verify12_1 : block f383 12 1 1 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem level12 : block f383 12 0 2 = true := (@block_merge f383 12 0 1 1 verify12_0 verify12_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem verified383 : checkedTables f383 12 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact level8
  · exact level9
  · exact level10
  · exact level11
  · exact level12
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem signed383 : Lower (varsX 895) (graphGoal 895) 13 :=
  strong_low (m:=895) (cap:=12) (hints:=12901884161) (nb:=1) (by decide +kernel)
    (plainA (q:=383) (prior:=boundsBefore knownx351) (before_sound knownx351 validx351) (by decide +kernel))
    (index_root (g:=f383) (i:=1) rfl (before_sound knownx351 validx351) geometry383 verified383 (by decide +kernel))
    (index_root (g:=f383) (i:=0) rfl (before_sound knownx351 validx351) geometry383 verified383 (by decide +kernel))
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem signed447 : Lower (varsX 959) (graphGoal 959) 13 :=
  relabel_of (old:=959) (rep:=895) (swaps:=[65,50,131,84,118,135]) (by decide +kernel) signed383
theorem subsumed {T : Sig} {roots : List Sig} {k t S L}
    (hp : proper T) (h : Live T k t S) (sub : ∀ a ∈ S, a ∈ roots)
    (lb : Lower roots T L) : L ≤ k := by
  have run := list_run h S.toList (Finset.nodup_toList _) (by simp)
  have sup : supply (roots.map observe) (S.toList.map observe) := by
    intro a ha
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp ha
    exact Or.inl (List.mem_map_of_mem (sub _ (Finset.mem_toList.mp hv)))
  obtain ⟨q,bank,reach,hit,budget⟩ := contraction (observe_proper hp) run _ Reach.start sup
  have bound := lb q bank reach hit
  omega


def extraInputs (j : Fin 9) := inputs ++ [seed] ++ [bin true (inputs.getD 6 zero) (inputs.getD j.val zero)]
def witnesses (r s : Row) := [(inputs.getD 6 zero, r, s)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem partner1 : Lower (extraInputs 1) graph 14 :=
  lift_ok (ms:=fixRows 64 0) (xs:=witnesses 2 66) (by decide +kernel)
    graph_proper (proper_of _ (by decide +kernel)) signed447
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem partner2 : Lower (extraInputs 2) graph 14 :=
  lift_ok (ms:=fixRows 64 0) (xs:=witnesses 260 324) (by decide +kernel)
    graph_proper (proper_of _ (by decide +kernel)) signed447
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem partner3 : Lower (extraInputs 3) graph 14 :=
  lift_ok (ms:=fixRows 64 0) (xs:=witnesses 10 74) (by decide +kernel)
    graph_proper (proper_of _ (by decide +kernel)) signed447
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem partner5 : Lower (extraInputs 5) graph 14 :=
  lift_ok (ms:=fixRows 64 0) (xs:=witnesses 34 98) (by decide +kernel)
    graph_proper (proper_of _ (by decide +kernel)) signed447
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem partner7 : Lower (extraInputs 7) graph 14 :=
  lift_ok (ms:=fixRows 64 0) (xs:=witnesses 130 194) (by decide +kernel)
    graph_proper (proper_of _ (by decide +kernel)) signed447
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem partner8 : Lower (extraInputs 8) graph 14 :=
  lift_ok (ms:=fixRows 64 0) (xs:=witnesses 256 320) (by decide +kernel)
    graph_proper (proper_of _ (by decide +kernel)) signed447
theorem edgeLower (j : Fin 9) (hj : j ∈ [1, 2, 3, 5, 7, 8]) :
    Lower (extraInputs j) graph 14 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
  · exact partner1
  · exact partner2
  · exact partner3
  · exact partner5
  · exact partner7
  · exact partner8
theorem allInputs (j : Fin 9) (r : Row) :
    (extraInputs j).map (bit r) = List.ofFn (sample r) ++ [!(sample r 0)] ++ [sample r 6 || sample r j] := by
  simp only [extraInputs, List.map_append, List.map_singleton, ←sampled, seed_table, bit_bin, ite_true]
  rfl

theorem sixSuppliedByOne :
    (extraInputs 6).all (fun a => (extraInputs 1).contains a) = true := by decide +kernel

theorem lowerBound (j : Fin 9) (hj : j ∈ [1, 2, 3, 5, 6, 7, 8])
    (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C) (size : C.size ≤ 13)
    (computes : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0] ++ [x 6 || x j]) = edge x) : False := by
  have eq : (execute C.gates (extraInputs j)).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    let r : Row := ⟨i,hi⟩
    change bit r _ = bit r graph
    rw [←b_read, execute_bits _ _ _ (fun g hg => (legal g hg).1), allInputs, edge_table]
    exact computes (sample r)
  have out := get_rep (execute C.gates (extraInputs j)) C.output
  rw [eq] at out
  obtain ⟨k,t,S,hk,run,sub⟩ := extract C.gates (extraInputs j) legal graph_proper
    (out.resolve_right (fun h => h graph_proper))
  have lo : 14 ≤ k := by
    by_cases same : j = 6
    · subst j
      apply subsumed graph_proper run _ partner1
      intro a ha
      simpa only [List.contains_iff_mem] using List.all_eq_true.mp sixSuppliedByOne a (sub a ha)
    · have rest : j ∈ ([1, 2, 3, 5, 7, 8] : List (Fin 9)) := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢
        tauto
      exact subsumed graph_proper run sub (edgeLower j rest)
  change C.gates.length ≤ 13 at size
  omega
end PEqualNP.Outside.L_meta_3394

theorem PEqualNP.Outside.L_meta_3394 : ∀ x1 ∈ [(1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))], ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (13 : ℕ) → ∃ (x6 : Fin (9 : ℕ) → Bool), x3.eval (List.ofFn x6 ++ [!x6 (0 : Fin (9 : ℕ))] ++ [x6 (6 : Fin (9 : ℕ)) || x6 x1]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro j hj C legal size
  by_contra h
  exact PEqualNP.Outside.L_meta_3394.lowerBound j hj C legal size
    (fun x => not_not.mp (not_exists.mp h x))
