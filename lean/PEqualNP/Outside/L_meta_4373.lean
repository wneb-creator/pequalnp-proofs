import PEqualNP.Defs
-- Move verifier from the accepted L-meta-1665, file SHA-256 2fbab5299779587e3528ab36e9f447fe89ccdc3f57e345e763377652caae21c7.
-- Signed forest, complete root argument and original certificate by dsgallups, PR #6907.
-- The move witness stream below selects a restriction, a linked state, or a repeated value.
-- Each selected reason is verified against the actual node before use.
-- Search framework and the plain 15-gate tables adapted from PEqualNP/Outside/L_meta_1667.lean, Apache-2.0.
namespace PEqualNP.Outside.L_meta_4373
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
  | 0,t,S => t = 0 ∧ proper target ∧ S = {target}
  | k+1,t,S => (∃ (u : Nat) (U : Finset Sig) (a : Sig), t = u+1 ∧ S = insert a U ∧ proper a ∧
        neg a ∉ insert a U ∧ Live target k u (insert (neg a) U)) ∨
      (∃ (U : Finset Sig) (a b : Sig) (d : Bool), S = insert a (insert b U) ∧ proper a ∧ proper b ∧
        a ≠ b ∧ bin d a b ∉ insert a (insert b U) ∧ Live target k t (insert (bin d a b) U))
theorem Live.stop {target : Sig} (hp : proper target) : Live target 0 0 {target} := ⟨rfl,hp,rfl⟩
theorem Live.unary {target : Sig} {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
    (hfresh : neg a ∉ insert a U) (tail : Live target k t (insert (neg a) U)) :
    Live target (k+1) (t+1) (insert a U) := Or.inl ⟨t,U,a,rfl,rfl,ha,hfresh,tail⟩
theorem Live.binary {target : Sig} {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live target k t (insert (bin d a b) U)) :
    Live target (k+1) t (insert a (insert b U)) := Or.inr ⟨U,a,b,d,rfl,ha,hb,hab,hfresh,tail⟩
theorem Live.ind {target : Sig} {motive : ∀ (k t : Nat) (S : Finset Sig), Live target k t S → Prop}
    (stop : ∀ (hp : proper target), motive 0 0 {target} (Live.stop hp))
    (unary : ∀ {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live target k t (insert (neg a) U)),
      motive _ _ _ tail → motive _ _ _ (Live.unary ha hfresh tail))
    (binary : ∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live target k t (insert (bin d a b) U)),
      motive _ _ _ tail → motive _ _ _ (Live.binary ha hb hab hfresh tail))
    {k t : Nat} {S : Finset Sig} (h : Live target k t S) : motive k t S h := by
  induction k generalizing t S with
  | zero =>
    obtain ⟨rfl,hp,rfl⟩ := h
    exact stop hp
  | succ k ih =>
    have hh := h
    rcases hh with ⟨u,U,a,rfl,rfl,ha,hf,tl⟩ | ⟨U,a,b,d,rfl,ha,hb,hab,hf,tl⟩
    · exact unary ha hf tl (ih tl)
    · exact binary ha hb hab hf tl (ih tl)

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
  | 0,bank => bank = roots
  | p+1,bank => (∃ (b : List (Wire R)) (a : Wire R), bank = inv a :: b ∧ Reach roots p b ∧ Available b a) ∨
      (∃ (b : List (Wire R)) (a c : Wire R) (op : Bool), bank = combine op a c :: b ∧ Reach roots p b ∧
        Available b a ∧ Available b c)
theorem Reach.start {R} {roots : List (Wire R)} : Reach roots 0 roots := rfl
theorem Reach.one {R} {roots : List (Wire R)} {p : Nat} {bank : List (Wire R)} {a : Wire R}
    (h : Reach roots p bank) (ha : Available bank a) : Reach roots (p+1) (inv a :: bank) :=
  Or.inl ⟨bank,a,rfl,h,ha⟩
theorem Reach.two {R} {roots : List (Wire R)} {p : Nat} {bank : List (Wire R)} {a b : Wire R} (op : Bool)
    (h : Reach roots p bank) (ha : Available bank a) (hb : Available bank b) :
    Reach roots (p+1) (combine op a b :: bank) := Or.inr ⟨bank,a,b,op,rfl,h,ha,hb⟩
theorem Reach.ind {R} {roots : List (Wire R)}
    {motive : ∀ (p : Nat) (bank : List (Wire R)), Reach roots p bank → Prop}
    (start : motive 0 roots Reach.start)
    (one : ∀ {p : Nat} {bank : List (Wire R)} {a : Wire R} (h : Reach roots p bank) (ha : Available bank a),
      motive _ _ h → motive _ _ (Reach.one h ha))
    (two : ∀ {p : Nat} {bank : List (Wire R)} {a b : Wire R} (op : Bool) (h : Reach roots p bank)
      (ha : Available bank a) (hb : Available bank b), motive _ _ h → motive _ _ (Reach.two op h ha hb))
    {p : Nat} {bank : List (Wire R)} (h : Reach roots p bank) : motive p bank h := by
  induction p generalizing bank with
  | zero =>
    have hh := h
    obtain rfl : bank = roots := hh
    exact start
  | succ p ih =>
    have hh := h
    rcases hh with ⟨b,a,rfl,hb,ha⟩ | ⟨b,a,c,op,rfl,hb,ha,hc⟩
    · exact one hb ha (ih hb)
    · exact two op hb ha hc (ih hb)

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

def Run {R} (goal : Wire R) (s : Nat) (xs : List (Wire R)) : Prop :=
  ∀ P : Nat → List (Wire R) → Prop, P 0 [goal] →
    (∀ {s : Nat} {xs zs : List (Wire R)}, xs.Perm zs → P s xs → P s zs) →
    (∀ {s : Nat} {a : Wire R} {rest : List (Wire R)} (save : Bool),
      P s (inv a :: kept save a rest) → P (s+1) (a::rest)) →
    (∀ {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op ka kb : Bool),
      P s (combine op a b :: kept ka a (kept kb b rest)) → P (s+1) (a::b::rest)) → P s xs
theorem Run.stop {R} {goal : Wire R} : Run goal 0 [goal] := fun _ h0 _ _ _ => h0
theorem Run.perm {R} {goal : Wire R} {s : Nat} {xs zs : List (Wire R)} (p : xs.Perm zs)
    (h : Run goal s xs) : Run goal s zs := fun P h0 hp h1 h2 => hp p (h P h0 hp h1 h2)
theorem Run.one {R} {goal : Wire R} {s : Nat} {a : Wire R} {rest : List (Wire R)} (save : Bool)
    (h : Run goal s (inv a :: kept save a rest)) : Run goal (s+1) (a::rest) :=
  fun P h0 hp h1 h2 => h1 save (h P h0 hp h1 h2)
theorem Run.two {R} {goal : Wire R} {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op ka kb : Bool)
    (h : Run goal s (combine op a b :: kept ka a (kept kb b rest))) : Run goal (s+1) (a::b::rest) :=
  fun P h0 hp h1 h2 => h2 op ka kb (h P h0 hp h1 h2)
theorem Run.ind {R} {goal : Wire R} {motive : ∀ (s : Nat) (xs : List (Wire R)), Run goal s xs → Prop}
    (stop : motive 0 [goal] Run.stop)
    (perm : ∀ {s : Nat} {xs zs : List (Wire R)} (p : xs.Perm zs) (h : Run goal s xs),
      motive _ _ h → motive _ _ (Run.perm p h))
    (one : ∀ {s : Nat} {a : Wire R} {rest : List (Wire R)} (save : Bool)
      (h : Run goal s (inv a :: kept save a rest)), motive _ _ h → motive _ _ (Run.one save h))
    (two : ∀ {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op ka kb : Bool)
      (h : Run goal s (combine op a b :: kept ka a (kept kb b rest))), motive _ _ h →
      motive _ _ (Run.two op ka kb h))
    {s : Nat} {xs : List (Wire R)} (h : Run goal s xs) : motive s xs h := by
  have key : ∃ h' : Run goal s xs, motive s xs h' := by
    refine h (fun s xs => ∃ h' : Run goal s xs, motive s xs h') ⟨_,stop⟩ ?_ ?_ ?_
    · rintro s xs zs p ⟨h',m⟩
      exact ⟨_,perm p h' m⟩
    · rintro s a rest save ⟨h',m⟩
      exact ⟨_,one save h' m⟩
    · rintro s a b rest op ka kb ⟨h',m⟩
      exact ⟨_,two op ka kb h' m⟩
  exact key.2

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

theorem seed_witness : ∀ i : Fin 9, i ≠ 0 →
    ((bit (absentRow i) graph != bit (presentRow i) graph) &&
    ((inputs++[seed]).all fun w => w == inputs.getD i.val zero ||
      bit (absentRow i) w == bit (presentRow i) w)) = true := by decide +kernel
def EssentialAt (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v
theorem split_roots {T : Sig} {k t S} (ws : List Sig) (x n : Sig) (h : Live T k t S)
    (sub : ∀ v ∈ S, v ∈ ws++[n])
    (ess : ∀ a ∈ ws, a ≠ x → EssentialAt T (ws++[n]) a) (r s : Row) (d : bit r T ≠ bit s T)
    (iso : ∀ v ∈ ws, v ≠ x → bit r v = bit s v) :
    S=ws.toFinset ∨ S=(ws++[n]).toFinset ∨ S=(ws.filter (fun a => a != x) ++ [n]).toFinset := by
  have all : ∀ a ∈ ws, a ≠ x → a ∈ S := by
    intro a ha hne
    obtain ⟨r,s,hd,hi⟩ := ess a ha hne
    exact raw_required h _ a sub r s hd hi
  have cover : ∀ v ∈ S, v ∈ ws ∨ v = n := by
    intro v hv
    simpa using sub v hv
  by_cases hn : n ∈ S <;> by_cases hx : x ∈ S
  · right; left
    ext a
    simp only [List.toFinset_append,Finset.mem_union,List.mem_toFinset,List.mem_singleton]
    refine ⟨cover a,?_⟩
    rintro (ha | rfl)
    · by_cases e : a=x
      · exact e ▸ hx
      · exact all a ha e
    · exact hn
  · right; right
    ext a
    simp only [List.toFinset_append,Finset.mem_union,List.mem_toFinset,List.mem_singleton,
      List.mem_filter,bne_iff_ne]
    constructor
    · intro ha
      rcases cover a ha with hw | e
      · exact Or.inl ⟨hw,fun e => hx (e ▸ ha)⟩
      · exact Or.inr e
    · rintro (⟨ha,e⟩ | rfl)
      · exact all a ha e
      · exact hn
  · left
    ext a
    simp only [List.mem_toFinset]
    constructor
    · intro ha
      exact (cover a ha).resolve_right (fun e => hn (e ▸ ha))
    · intro ha
      by_cases e : a=x
      · exact e ▸ hx
      · exact all a ha e
  · exfalso
    obtain ⟨v,hv,hd⟩ := live_row_difference h d
    have hw := (cover v hv).resolve_right (fun e => hn (e ▸ hv))
    exact hd (iso v hw (fun e => hx (e ▸ hv)))

theorem x0_row : bit (Fin.ofNat 512 2) graph ≠ bit (Fin.ofNat 512 3) graph := by decide +kernel
theorem x0_all : (inputs.all fun v => v == inputs.getD 0 zero ||
    bit (Fin.ofNat 512 2) v == bit (Fin.ofNat 512 3) v) = true := by decide +kernel
theorem x0_iso : ∀ v ∈ inputs, v ≠ inputs.getD 0 zero →
    bit (Fin.ofNat 512 2) v = bit (Fin.ofNat 512 3) v := by
  intro v hv hne
  have h := List.all_eq_true.mp x0_all v hv
  simp only [Bool.or_eq_true,beq_iff_eq] at h
  exact h.resolve_left hne
def lowInputs := inputs.filter (fun a => a != inputs.getD 0 zero) ++ [seed]

theorem all_roots {k t S} (h : Live graph k t S) (sub : ∀ v ∈ S, v ∈ inputs++[seed]) :
    S=inputs.toFinset ∨ S=(inputs++[seed]).toFinset ∨ S=lowInputs.toFinset := by
  apply split_roots inputs (inputs.getD 0 zero) seed h sub _ _ _ x0_row x0_iso
  intro a ha hne
  rw [←input_list,List.mem_ofFn] at ha
  obtain ⟨i,rfl⟩ := ha
  have hi : i ≠ 0 := fun e => hne (by rw [e]; rfl)
  have cut := seed_witness i hi
  simp only [Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at cut
  exact ⟨absentRow i,presentRow i,cut.1,fun v hv hne => (cut.2 v hv).resolve_left hne⟩

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
  | @unary k t U a ha hf tail =>
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
  | @binary k t U a b d ha hb hab hf tail =>
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
def negInput : Sig := neg (inputs.getD 0 zero)
def vars (m : Nat) := (selected m).map Prod.snd ++ (if m.testBit 9 then [negInput] else [])
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
def colFree (m z o : Nat) :=
  let f := m ^^^ (m &&& (z ||| o))
  if (z ||| o).testBit 0 then f &&& 511 else f
def chartGoal (m : Nat) : Sig := graphGoal m
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs s
  let count := (xs.map Prod.fst).toFinset.card
  properB G && checkMap ms (vars m) (chartGoal m) (vars free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (vars free) xs && decide (L ≤ count-1)
     else properB (graphGoal q) &&
       checkLift (fixRows (colFree free q 0) 0) G (vars free) (vars q) (graphGoal q) xs &&
       decide (L ≤ prior q+count))

theorem col_sound {m : Nat} (c : ColumnInfo) (prior : Nat → Nat)
    (valid : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (ok : colCheck m c prior = true) : Slice (vars m) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  obtain ⟨z,o,q,s,L⟩ := c
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs s
  change (((properB G && checkMap ms (vars m) (chartGoal m) (vars free) G) &&
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

def remapOK (old rep : Nat) (swaps : List Nat) :=
  properB (graphGoal old) && properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (vars old) (graphGoal old) (vars rep) (graphGoal rep)
theorem remap_of {old rep L swaps} (ok : remapOK old rep swaps = true)
    (h : Lower (vars rep) (graphGoal rep) L) : Lower (vars old) (graphGoal old) L := by
  simp only [remapOK,Bool.and_eq_true] at ok
  exact lower_map ok.2 (proper_of _ ok.1.1) (proper_of _ ok.1.2) h

def boundsBefore (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1 == q)).map Prod.snd).getD 0
theorem before_sound (entries : List (Nat × Nat))
    (sound : ∀ e ∈ entries, Lower (vars e.1) (graphGoal e.1) e.2) (q : Nat) :
    Lower (vars q) (graphGoal q) (boundsBefore entries q) := by
  unfold boundsBefore
  cases h : entries.find? (fun a => a.1 == q) with
  | none => exact fun _ _ _ _ => Nat.zero_le _
  | some e =>
    have he := List.mem_of_find?_eq_some h
    have hit : (fun a : Nat × Nat => a.1 == q) e = true := List.find?_some (p:=fun a : Nat × Nat => a.1 == q) (a:=e) h
    have eq : e.1=q := beq_iff_eq.mp hit
    simpa only [Option.map_some,Option.getD_some,eq] using sound e he


abbrev BoundPool := Sig × Nat × Nat × List Sig
abbrev BoundPool.domain (c : BoundPool) : Sig := c.1
abbrev BoundPool.bound (c : BoundPool) : Nat := c.2.1
abbrev BoundPool.paid (c : BoundPool) : Nat := c.2.2.1
abbrev BoundPool.wires (c : BoundPool) : List Sig := c.2.2.2

def ValidPool (raw : List Sig) (T : Sig) (c : BoundPool) :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r, bit (f r) c.domain = true) ∧ ¬Constant (restrictRows f (observe T)) ∧
    (∀ q ws, Reach (roots.map observe) q ws → Available ws (restrictRows f (observe T)) → c.bound ≤ q) ∧
    Reach (roots.map observe) c.paid bank ∧ poolSupply f bank c.wires ∧ True

theorem build_valid {raw T d lb} (h : Slice raw T d lb) (cs : List Choice) {ws}
    (build : makePool d raw cs = some ws) : ValidPool raw T ⟨d,lb,cs.length,ws⟩ := by
  obtain ⟨f,roots,dom,sup,nc,prior⟩ := h
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa using hr,hs,trivial⟩

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
-- Repeats the same 64-bit sample pattern across the packed word.
def repeatSamples : Bits := 0x100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
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
    obtain ⟨_,_,rfl⟩ := h
    exact out (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
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


abbrev IndexTree (α : Type) := List α
abbrev IndexTree.read {α} (xs : IndexTree α) (i : Nat) : Option α := xs[i]?
abbrev IndexTree.values {α} (xs : IndexTree α) : List α := xs
theorem IndexTree.read_mem {α} (tree : IndexTree α) {i x} (e : IndexTree.read tree i=some x) :
    x ∈ IndexTree.values tree := List.mem_of_getElem? e

abbrev Forest := Nat × Nat × (Nat → Bits × Bits) × List ColumnInfo × Array (List Nat) ×
  (Nat → Packing) × (Nat → Nat → Option (Nat × Nat))
abbrev Forest.mask (g : Forest) : Nat := g.1
abbrev Forest.cap (g : Forest) : Nat := g.2.1
abbrev Forest.samples (g : Forest) : Nat → Bits × Bits := g.2.2.1
abbrev Forest.cols (g : Forest) : List ColumnInfo := g.2.2.2.1
abbrev Forest.autos (g : Forest) : Array (List Nat) := g.2.2.2.2.1
abbrev Forest.levels (g : Forest) : Nat → Packing := g.2.2.2.2.2.1
abbrev Forest.index (g : Forest) : Nat → Nat → Option (Nat × Nat) := g.2.2.2.2.2.2

def wiresOf (g : Forest) :=
  let ws := rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  if g.mask.testBit 9 then ws ++ [dneg (ws.getD 0 defaultDecor)] else ws
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a := by
  have base := raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  intro a ha
  unfold wiresOf at ha
  split at ha
  · rcases List.mem_append.mp ha with hm | hm
    · exact base _ hm
    · obtain rfl := List.mem_singleton.mp hm
      exact faithful_neg (faithful_get base 0)
  · exact base _ ha

def targetOf (g : Forest) := chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) := liftGoal m v
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := bit_liftGoal m v i
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
  (IndexTree.read g.cols idx).bind fun ci =>
    materialize (vars g.mask) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2

theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ (IndexTree.values g.cols), Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : buildRule g ops depth bank i paid = some c) :
    ValidPool (vars g.mask) (targetOf g) c := by
  unfold buildRule at h
  cases e : IndexTree.read g.cols i with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    apply materialize_sound _ h
    exact cols ci (IndexTree.read_mem g.cols e)

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
    (names : ∀ x ∈ g.autos.toList, autoOK (targetOf g) (x.map swapRows) = true)
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
      exact rotate_excluded (earlier _ (by omega)) _ (names _ (by simpa using Array.mem_of_getElem? e))

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
    (cols : ∀ ci ∈ (IndexTree.values g.cols), Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos.toList, autoOK (targetOf g) (x.map swapRows) = true)
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
    obtain ⟨_,_,rfl⟩ := h
    exact hT (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
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
  (IndexTree.values g.cols).all (fun c => colCheck g.mask c prior) &&
  g.autos.toList.all (fun p => autoOK (targetOf g) (p.map swapRows))

theorem forest_all (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower (vars q) (graphGoal q) (prior q))
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
theorem root_index {g top prior k i ws} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g top) (le : k ≤ top)
    (idx : indexedRoot g k i ws = true) : Impossible (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact forest_all g top prior low geom blocks _ le i idx.1

theorem lower_forest {g prior i hints} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
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

theorem lower_discard {g prior ci hints} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (ok : colCheck g.mask ci prior = true)
    (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask)
    (nd : (vars g.mask).Nodup)
    (cut : poolCut (subcube ci.1 ci.2.1) ci.2.2.2.2 g.cap 0 (vars g.mask) (vars g.mask)=true) :
    Lower (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) _ (poolCut_sound (col_sound ci prior low ok) [] rfl nd cut)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

def Known (entries : List (Nat × Nat)) := ∀ e ∈ entries, Lower (vars e.1) (graphGoal e.1) e.2
def extendKnown (old : List (Nat × Nat)) (L : Nat) (remaps : List (Nat × List Nat)) :=
  remaps.map (fun v => (v.1,L)) ++ old
theorem extendKnown_ok {old L m remaps} (previous : Known old)
    (main : Lower (vars m) (graphGoal m) L)
    (ok : remaps.all (fun v => remapOK v.1 m v.2) = true) :
    Known (extendKnown old L remaps) := by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact remap_of (List.all_eq_true.mp ok _ hv) main
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
-- A node certificate may name one applicable restriction or the previously verified child.
-- The number is just a witness. The kernel checks the chosen reason on the actual move.
def recommended (c : NodeContext) (i j op : Nat) (ka kb : Bool) (tag : Nat) : Bool :=
  let a := contextWire c i
  let b := contextWire c j
  let z := movedDecor op a b
  let rest := (opKeep (op==2) ka kb a b c.2.2.1).map Prod.fst
  let action := movedChoice op a b
  let ws := choiceVal action :: rest
  if tag=0 then !properB z.1 || c.2.2.1.any (fun w => w.1 == z.1)
  else if tag=1 then (c.2.2.2.2.2 (keySet ws)).any (sameWords ws)
  else ((c.2.2.2.2.1[(tag-2)/2]?).any fun p =>
    if tag % 2 = 0 then
      decide (i<c.2.2.1.length ∧ j<c.2.2.1.length) &&
        fastCost (summarizePool c.2.2.1 p) (c.1-1) a b op ka kb
    else scalarPoolCut p (c.1-1) rest action)

lemma selected_good {c i j op ka kb tag} (h : recommended c i j op ka kb tag=true) :
    checkAt c i j op ka kb=true := by
  let a := contextWire c i
  let b := contextWire c j
  let z := movedDecor op a b
  let rest := (opKeep (op==2) ka kb a b c.2.2.1).map Prod.fst
  let action := movedChoice op a b
  let ws := choiceVal action :: rest
  have done (cap : closeChild c.2.2.2.2.1 c.2.2.2.2.2 (c.1-1) rest action = true) :
      checkAt c i j op ka kb = true := by
    change evalMove c op a b z ka kb = true
    unfold evalMove
    dsimp only
    repeat' split
    all_goals first | rfl | exact cap
  unfold recommended at h
  dsimp only at h
  split at h
  · change evalMove c op a b z ka kb = true
    change (!properB z.1 || c.2.2.1.any (fun w => w.1 == z.1)) = true at h
    simp only [evalMove,h,ite_true]
    repeat' split
    all_goals rfl
  split at h
  · apply done
    exact Bool.or_eq_true_iff.mpr (Or.inl h)
  cases hp : c.2.2.2.2.1[(tag-2)/2]? with
  | none => simp [hp] at h
  | some p =>
    have mem := List.mem_of_getElem? hp
    simp only [hp,Option.any_some] at h
    apply done
    apply Bool.or_eq_true_iff.mpr
    right
    apply List.any_eq_true.mpr
    refine ⟨p,mem,?_⟩
    split at h
    · obtain ⟨bounds,success⟩ := Bool.and_eq_true_iff.mp h
      have good := of_decide_eq_true bounds
      have present (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
        simp [contextWire,List.getD_eq_getElem?_getD,ht]
      exact fastCost_good (present i good.1) (present j good.2) success
    · exact h


-- The stream records one reason for each surviving state, in gate and state order.
-- A successful check returns the unused part of the stream.
def readTag (s : Nat) : Nat × Nat := (if s &&& 1 = 0 then (2, s >>> 1) else (if s &&& 2 = 0 then (if s &&& 4 = 0 then (if s &&& 8 = 0 then (if s &&& 16 = 0 then (10, s >>> 5) else (if s &&& 32 = 0 then (12, s >>> 6) else (if s &&& 64 = 0 then (if s &&& 128 = 0 then (11, s >>> 8) else (if s &&& 256 = 0 then (if s &&& 512 = 0 then (if s &&& 1024 = 0 then (if s &&& 2048 = 0 then (if s &&& 4096 = 0 then (23, s >>> 13) else (if s &&& 8192 = 0 then (if s &&& 16384 = 0 then (22, s >>> 15) else (if s &&& 32768 = 0 then (24, s >>> 16) else (26, s >>> 16))) else (if s &&& 16384 = 0 then (27, s >>> 15) else (25, s >>> 15)))) else (20, s >>> 12)) else (21, s >>> 11)) else (17, s >>> 10)) else (16, s >>> 9))) else (if s &&& 128 = 0 then (9, s >>> 8) else (if s &&& 256 = 0 then (if s &&& 512 = 0 then (if s &&& 1024 = 0 then (18, s >>> 11) else (19, s >>> 11)) else (15, s >>> 10)) else (13, s >>> 9)))))) else (if s &&& 16 = 0 then (8, s >>> 5) else (if s &&& 32 = 0 then (3, s >>> 6) else (if s &&& 64 = 0 then (5, s >>> 7) else (if s &&& 128 = 0 then (14, s >>> 8) else (7, s >>> 8)))))) else (4, s >>> 3)) else (if s &&& 4 = 0 then (0, s >>> 3) else (if s &&& 8 = 0 then (6, s >>> 4) else (1, s >>> 4)))))

def consume {α : Type} (ok : Nat → α → Bool) (mask code : Nat) : List α → Option Nat
  | [] => some code
  | x::xs =>
    if mask=0 then some code else if mask &&& 1 == 0 then consume ok (mask >>> 769) code xs
    else let p := readTag code
         if ok p.1 x then consume ok (mask >>> 769) p.2 xs else none

theorem consume_sound {α} {ok : Nat → α → Bool} {f : α → Bool}
    (valid : ∀ t c, ok t c=true → f c=true) (m v : Nat) (xs : List α) {r}
    (h : consume ok m v xs=some r) : onMarks f m xs=true := by
  induction xs generalizing m v with
  | nil => rfl
  | cons x xs ih =>
    by_cases mz : m=0
    · simp [onMarks,mz]
    simp only [consume,mz,ite_false] at h
    simp only [onMarks,mz,ite_false,Bool.and_eq_true,Bool.or_eq_true]
    split at h
    next ht => exact ⟨Or.inl ht,ih _ _ h⟩
    next =>
      split at h
      next yes => exact ⟨Or.inr (valid _ x yes),ih _ _ h⟩
      next => cases h

def streamMove (b : Batch) (xs : List NodeContext) (i j op : Nat) (ka kb : Bool) (v : Nat) :=
  let (k,n,r,_,u,cov2) := b
  let un := op==2
  let len := 1+(n-(if ka then 0 else 1)-(if un || kb then 0 else 1))
  if len>k then some v else
    let d := len==k
    let a := laneWire b i
    let b' := laneWire b j
    let z := packedOp (r*(BitVec.allOnes 768).toNat) op a b'
    let cov := if d then cov2 else u
    let mask := fullMarks r (takePacked cov (packedColumn d a) (packedColumn d b') un ka kb ||| packedColumn d z)
    consume (fun t c => recommended c i j op ka kb t) mask v xs

lemma streamMove_ok (b xs i j op ka kb v r) :
    streamMove b xs i j op ka kb v=some r → batchMove b xs i j op ka kb=true := by
  unfold streamMove batchMove
  dsimp only
  by_cases hlen : b.1 < 1+(b.2.1-(if ka then 0 else 1)-(if (op==2 || kb) then 0 else 1))
  · simp only [gt_iff_lt,hlen,ite_true,imp_true_iff]
  · simp only [gt_iff_lt,hlen,ite_false]
    exact consume_sound (fun t c h => Bool.or_eq_true_iff.mpr (Or.inr (selected_good h))) _ _ _

lemma splitBind {α β} {x : Option α} {f : α → Option β} {r : β}
    (h : x.bind f=some r) : ∃ u, x=some u ∧ f u=some r := by
  cases x with
  | none => cases h
  | some u => exact ⟨u,rfl,h⟩

def streamPair (b xs i j op) (v : Nat) := do
  let w ← streamMove b xs i j op false false v
  let w ← streamMove b xs i j op true false w
  let w ← streamMove b xs i j op false true w
  streamMove b xs i j op true true w
lemma streamPair_ok (b xs i j op v r) (pass : streamPair b xs i j op v = some r) :
    batchPair b xs i j op=true := by
  obtain ⟨v1,h1,more⟩ := splitBind pass
  obtain ⟨v2,h2,more⟩ := splitBind more
  obtain ⟨v3,h3,h4⟩ := splitBind more
  simp only [batchPair,Bool.and_eq_true]
  exact ⟨⟨⟨streamMove_ok _ _ _ _ _ _ _ _ _ h1,streamMove_ok _ _ _ _ _ _ _ _ _ h2⟩,
    streamMove_ok _ _ _ _ _ _ _ _ _ h3⟩,streamMove_ok _ _ _ _ _ _ _ _ _ h4⟩

def streamJs (b : Batch) (xs : List NodeContext) (i : Nat) : List Nat → Nat → Option Nat
  | [],v => some v
  | j::js,v => do
    let w ← streamPair b xs i j 0 v
    let w ← streamPair b xs i j 1 w
    streamJs b xs i js w
lemma streamJs_ok (b xs i js v r) (pass : streamJs b xs i js v=some r) :
    js.all (fun j => batchPair b xs i j 0 && batchPair b xs i j 1)=true := by
  induction js generalizing v with
  | nil => rfl
  | cons j js ih =>
    obtain ⟨v1,h1,more⟩ := splitBind pass
    obtain ⟨v2,h2,more⟩ := splitBind more
    simp only [List.all_cons,Bool.and_eq_true]
    exact ⟨⟨streamPair_ok _ _ _ _ _ _ _ h1,streamPair_ok _ _ _ _ _ _ _ h2⟩,ih _ more⟩

def streamRow (b xs i js) (v : Nat) := do
  let w ← streamMove b xs i i 2 false false v
  let w ← streamMove b xs i i 2 true true w
  streamJs b xs i js w
lemma streamRow_ok (b xs i js v r) (pass : streamRow b xs i js v=some r) : batchRow b xs i js=true := by
  obtain ⟨v1,h1,more⟩ := splitBind pass
  obtain ⟨v2,h2,more⟩ := splitBind more
  simp only [batchRow,Bool.and_eq_true]
  exact ⟨⟨streamMove_ok _ _ _ _ _ _ _ _ _ h1,streamMove_ok _ _ _ _ _ _ _ _ _ h2⟩,streamJs_ok _ _ _ _ _ _ more⟩

def streamCut (words : Array Nat) (g : Forest) (k start n ar : Nat) :=
  let xs := contexts g k start n
  let b := makeBatch k ar xs
  (List.range ar).all (fun i =>
    (streamRow b xs i (List.range' (i+1) (ar-(i+1))) (words[i]?.getD 0)).isSome)
lemma streamBlock {w g k start n ar} (h : header g k start n ar=true)
    (run : streamCut w g k start n ar=true) : block g k start n=true := by
  apply cutsBlock h
  unfold rowCut
  simp only [Nat.zero_add]
  unfold streamCut at run
  apply List.all_eq_true.mpr
  intro i hi
  obtain ⟨r,ok⟩ := Option.isSome_iff_exists.mp (List.all_eq_true.mp run i hi)
  exact streamRow_ok _ _ _ _ _ r ok

def g15d3 (i : Nat) : Nat := 0xf
def g15l3 : Packing := (1,0,0,0,1,0,0,g15d3)
def g15samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbaf3ea78de4d799d,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff450cc90c3c245919),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdf7ff8fe9f9b7ed5,0x20812421801324c4),(0xefbdbf97f9f6bf6a,0x102a401415600a0a),(0xf3a9d7437375f5ba,0xfc028ab620235b0),(0,0),(0,0),(0,0),(0,0),(0,0)]
def g15columns : IndexTree ColumnInfo := []
def g15autos : Array (List Nat) := #[[],[33,48]]
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
def g31columns : IndexTree ColumnInfo := [(1,0,30,0,4),(2,0,29,0,4),(4,0,27,0,4),(8,0,23,0,4),(16,0,15,0,4)]
def g31autos : Array (List Nat) := #[[],[50,65],[66,16],[67,50,33,16],[67,32],[67,66,49,32],[33,48],[67,50,65,48],[67,66,65,64],[49,64]]
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
def g47columns : IndexTree ColumnInfo := [(8,0,39,0,4)]
def g47autos : Array (List Nat) := #[[],[83,32]]
def g47levels : Nat → Packing
  | _ => emptyPacking
def g47index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g47 : Forest := ⟨47,4,fun j => g47samples[j]?.getD (0,0),g47columns,g47autos,g47levels,g47index⟩
def g55samples : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbfffffdf7defdfafbfd3fcebcfdeffcebffefe76de77fed7f1773f95eb2ebeb,0x400028000010005000000400701010180030103060043200102204010904888),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdb7fbfbb9ad3afd94caf0b9db5bbdf7f7d39bfcdadcf77ec9eccd2fb9cf16b5,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2484444214284026a4e002420468a8a43140a00408d944460a4082569431231),(0xeda5e7e7b2fc29de4ffc371dba2bf0775ff12db9b18bb528fedad96afcd3c5e,0x12589919410293410206d0396285445a082c5d2bf0022b20f0895d2048c2c4e),(0,0),(0xf1cd79264efe956afa7a64bb677ab40beba463600362eda36f3357b7d763926,0xe3a8651b1a36a0acc57538a080f6ea703078a0c13c28dc34c91f3868663126),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe05fe74eda341d5872cbf684d5e2ed19e7e3bba5e964550dd792aec724f479,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01fb53db1204342a549861b60b6727a22d48ac0b14da4445855161ae724b471),(0,0),(0,0),(0,0)]
def g55columns : IndexTree ColumnInfo := [(16,0,39,0,4)]
def g55autos : Array (List Nat) := #[[],[84]]
def g55levels : Nat → Packing
  | _ => emptyPacking
def g55index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g55 : Forest := ⟨55,4,fun j => g55samples[j]?.getD (0,0),g55columns,g55autos,g55levels,g55index⟩
def g63samples : Array (Bits × Bits) := #[(0xdabffdfdbdf61bfbfc7dcbe34f7f1b17917df75df7edd9eff77b6dbd3dcebed3cfbfaddba50fcabded46bc9b579eb7bd3d92776566ad4ad3debe36d74deb7f9faf189ad76da7dc1a6b4eaf21eb254de4ae1f7451bb34d9456fd18e934db17349,0x4400202400040800310000100084000ac0000102800a1100490002240004b2800a001b4000190000008108000574009200040400000594000190004218c0010840002890800550053044a00410008802d0060013000c004400188120c206208),(0xb6678efeffcbf5a9cad5bfd527a7a5bd74d1314b7915f5b2ffdec2fc5d978f8ab3b44b2b5add5b771711b15ce99bf2b3f5bce975ef94cd59a34e76ab937848a94ef6be6c9579db5905539ea703c87a7d4ae11fe2ae423fade4a3c3299b0724e7,0x499461811a200a55004cf88854029340027a680613c002ec00233c1096d01045025d0203d400243150030b7e4900b00499e023395882049d0206ec00041398010bbb1000b7310ad00cc0858112c8207810e917400e423d0034024309910504e5),(0xbfdd27bedf8fade4776ebf9d185bc5bd76aeffb29711f77d628e86e5fffdff6d1a52bff6da987348e3e147dcecdbcc68d1accc4e7d7d77b9734cfbbcefbc022d72eff5a31a72e32584dd5a72accb1256ede309af577ea6b3ab2be572a2769632,0x20983204990108b1910222a2810c12a8041040402e00006394000908008912a582448429aad10a21a0240190b504314209040621245140c82010e8812042049440841100c0c52080310832a5111106e902488a012c82618908a42202729212),(0x77ddb87389d95f9f7bbe7e8eb89e6e76fbf75ca7fd5bb3758b555b578affe964ae7e7fa493e06d03bebc4fb5cff51e46b2dd5bdbb1eab66f60f7d916b9c6944fd85b6f0fc30a2ae7d2afc9dc369ef80bb1b0b2dd52e9331e786f7a5d38e8c8b4,0x1482478012444200420888514440810c402202189081ecc814422aa4c048408050190921c0450c000a080254044021081134422900082c11250884167012813a48094aca870a3283708e41084282480000c012150640581c30655a55288040a4),(0xdca768aafb78ce8d2db2ec3fbdddfa4ec963339dbac7a8e05eccbf0bb99ddf5febcef6dc7762a4a79d9ad8f70324ba6e724754bded1eed86f695f276b70acbd73dc66e39a88d0cfed920a0ee10b5a4dd5893bba709bff6dc1ece388c561e1ed5,0x210938550593284a984457082a220ca002159526023c0223a02100100d271046aa46f2022bb0201ea5730921b3008e848a002106a7520082d20653c8040064810364a00030c5086c0c2084761035a077101508a009ba22e00b822088521e1c51),(0x77dad76bd4ced656e7ec247a694c9eb5b66dc4de71aac18acebb177a9bac7a62d6f3e3996dd9d62d6ecf7b18557229a30b5ebb1ef46b568a8f3400a7c2d3365caade63d0f2234a24623735bcfaee29c0664eddfc63b2a86915f817ca03dc41fa,0x88252894b2b3256598a758928465236453b27d28c68c4c28a24dcc0d24d500d4a845700845b04bd175706d345a20a0a24d641d897dd822a1d52444cad2629c8e732b305273362844202335b73c8d8150424e93e44a78286995ec17c803dc01f2),(0,0),(0,0),(0,0)]
def g63columns : IndexTree ColumnInfo := [(32,0,31,0,7)]
def g63autos : Array (List Nat) := #[[],[50,65]]
def g63levels : Nat → Packing
  | _ => emptyPacking
def g63index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g63 : Forest := ⟨63,7,fun j => g63samples[j]?.getD (0,0),g63columns,g63autos,g63levels,g63index⟩
def g111d6 (i : Nat) : Nat := 0x120ff
def g111l6 : Packing := (1,0,2,0,1,0,0,g111d6)
def g111samples : Array (Bits × Bits) := #[(0xeafcc7b96fc59ffd26c5e2bb3d7bd378fb35ff5dcb26f92afa5f57eff59a73b7aaa379b2fc8d7a99e2ef9efcf4defd4efabc9c89733cebade5579ad5abbcd64d8557ad3d63bd1c6a75510ce3b9bf05e462ee0edf6dfb2914efc74c7d31727465,0x4d00310a2003881269402d0c00406ccc142a8012908082d00025ac006a88036948003229000032d4001bf20024ec2018680000aaf2500325400423a6f02003840040a8016ea8106822700071012c01d500600ad401ea0010f407087831504444),(0xf771ad34ff2bcf4fbd7f5f5de52efaeb7ebbabfffefbf2eab7c7cf56f8ecea565ddfabcf87cb61db9d6ef4aecff7cebd76fe679cfb9935e6adabc77cdcdb677ed3da5e4f56b4cbe39cfd7aed1f519a6b999796b48a51f4f7b8ad91a66cc6d9cb,0x1204940050200482000010001c10308054448009004424020800871400ac0690000402004e0508404004081210450414000904018220d090010808000a44280600460810104d92040818880c1010088d8400200a10a1400808810604821909),(0xf5be76df5e79b8b5d13f5f6e3ecd176fbeee538a7cfb9f7f6b7fad9b13bb7fed97560ecd71f29f3f1e3ef959a338e3a9e32bd5e7cfc7b51df73d7e9e165479b3baa9a0d59e62e11eead3ad5c624777de8699f96d3766d64d1f3fa2ca8f3d2e52,0x8e4d19200884440101e4a802e100a0c04000830eb000289800c49240c1c411082c325a6812b0485430294040c52402008322a4b0e00c0021216842103a050a9080848145264020288841a770220547500211500d95204c05521120880b352452),(0xde2ebbc73c1cf83c4cedbed77297d7f5b666582db23d5c5d7bf4a54b37a75f4992f88d683d388ea5bafb57791a5deb9b257390777cf70e9d329773c24416edd93fe3d2909bc3b81d7e62dd94d70a759eb42b6b51587d63da2e7eea6ce78912bc,0x10b22099c5638280b403142808691e02bd9d04d1097a9640ce2041351e20e64283892100494815238b12089820999d9858901b4e1903515e001721098578a5416f515492d981d895722018845902b08a5c4a2a2248dd03d08c66ca64e48812ac),(0,0),(0x4a99db5e74fdf3bbfb83b4b12e735e58f515867b75942dba656f9eeac55739b971685432ece5b39368c30fbbb9f895ca9efa5eceda2fea7be4766f052ba5def635ccf928215f7640050f6846acafb2ca6efbba0bffbfdb9043d87d111c3c3ebd,0x12d68401de50564414b80023f49c0203c0413d800068400bbb08034f0177ac0427f40400f6de0023bcc009fc1201950403ff4900082ea08a2fc908010c8a4053de0011e801464d050407f806ac13f8026d9b800bfa055d40038875010c2c3ab9),(0x107b7e8791b6519a9ebd6f37d374faa298392ebad8b5e4afe6bd267679568b3365bebaabdf6ef4e9035a918e8ca50ef74769b2b74aea726a09a6c5e9463715fb76745a9b1b6212a1b9add6dec52a9ba55b57e399ab660ca6d0f217384af881fe,0xadc48a6a24248ac9294916cc74a18dce4988890976a839d0a90054480a8f001149b409fd5690d8d50882129489ae3083c83b5253565cd02541ca4550f495b985581508b28aaa022919a1e755a00eaaa54243a315f06a0c87d4f216384a7880f6),(0,0),(0,0)]
def g111columns : IndexTree ColumnInfo := [(4,8,99,0,4),(1,32,78,0,4),(64,0,47,0,5)]
def g111autos : Array (List Nat) := #[[],[83,32]]
def g111levels : Nat → Packing
  | 6 => g111l6
  | _ => emptyPacking
def g111index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | _ => fun _ => none
def g111 : Forest := ⟨111,6,fun j => g111samples[j]?.getD (0,0),g111columns,g111autos,g111levels,g111index⟩
def g119samples : Array (Bits × Bits) := #[(0xfab75f3dfbfa3756f92d9ff7baf5ff7dbfebb9b33bef7dcdf77fbffe7bbbf75546cedccfd6f7eb762bef3ffdd2ede7abbef7e4e4b775eb9be6ab6f4d5fde77f2b955ece57b3feb97c6d99b5cdd2fdd2ea315de5f3efbf8d44ddcaa7566eda9cd,0x20100000802449000a820000c1900042800052080010000098c000620802429000050a2000012e00000be20013404000082000047420011240000c8b8000110080002480036500158018000c4009400c9000c0062803a0400e00885042a10888),(0xaf7efcd6de9febfb57d6f5ddedde36f3db7fffeed79fdbfafcf255738c743cbbbff3e3b86b8f9fb9f5bdf54fbff79bd74f5afb3f7fba34f5bf5f9afae879ab5feefe93fa9ee6566f7bbee6bf67d426d75cfb2bace9344fabf72bd58e999b76b3,0x9300010000091004000400382060802420900110020801010208161810541520000000800198110400c004084880812115000049028020c0800220200009220a01801050108206a8408406120184808104430800802442850101410609083421),(0xd3aee9d1a16b8afb579b1b1a2ede96c634714fced4ed35afb8d86696aabedb2eada373270f48f3a9b93de8a90d87d8f6684756adef8eb40bf672fc78b9342c9c7aaa652b2aec9422dd38b32b2a5255bdcc3d35b2da5f372953f3c4ba3a70d996,0x2c07b23e74020fd2aa41748155856818d263d681015680dac92709c7448b08586eaf3a512642c64b613a9091954b38c222671d26711d023332d48951dd0691952839212f8b6888039910b9ac2a42653c283c65315b1b95185ae084b83270c996),(0,0),(0x759a506bc07865de6f37bc2fabe39a5e2705b6a3eec6bd3cca572e3ed72f0325f632aa43d8e0e833eaeab6f86ad5fa72dbaf9c83b9e70faa212acf122e177ae733d8fa39a0b0bb12b7915f7134c3b9a9ed98d75362b1d9c725676c3caf04637c,0x16e5f59c6d01a255c44806523c0cddb5529a2196d082e7c24415d298c0f10d071e6090549dc090f8ed501938009f3fb2169588d90b0b506d102e01343cb84ad135f45369a498be0a36011e712702bb816af81651c4b05c0701a6642cad046374),(0x6339c3e76f77dc41ec6c9766b8b0f93592cd6e58a17db2abb9eea5cd269eeae2dc2c1c9ec755bae6a2821f6b678c3538a75edaf56c57e97ff4e8b90d55c4e75ce36b37ac511be4c610c6f229b9ab77956345b3a117ef6f3608dd37697870ba61,0x84ef690f5888a6bc0049f9381c0ba0115db000874a075d2102333605e754184fe100105f739880fb92c019ec481f2d2102dbf2480954a0ad3f922114724920d57f80032e5018c6a22083e62199863ec06b43378157e41d3d00d937293850b261),(0xd5cc96ab2735f4eedbcfece9fd4d847149d75b8aa71ff3959066dc7566c66ecb75975abde9bb8d684d89311f3151135dd1ce4d97acd9737d0b4d97b62b1596cf57b51ab1b6b408593b67d5bb928b32dabad66fc43367241aeaae177095e247ea,0x481560b0cd924918c5323d4303992d88d1232e6a49f254a2454320824e8122936522ef3572424e688310332525616c12e023da92a435d213539c9243b254cc21b63548a8e4258841b361f1c95a017252ba1c47902bc1245a7a8e167094e243ca),(0,0),(0,0)]
def g119columns : IndexTree ColumnInfo := [(4,0,115,0,5)]
def g119autos : Array (List Nat) := #[[],[84],[98],[84,98],[101,66,16],[101,100,66,16],[101,84,82,16],[100,82,16]]
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
def g189columns : IndexTree ColumnInfo := [(1,0,188,0,5),(12,0,177,0,4),(16,0,173,0,5),(17,0,172,0,4),(24,0,165,0,4),(33,0,156,0,4),(132,0,57,0,4),(160,0,29,0,4)]
def g189autos : Array (List Nat) := #[[],[84,115],[117,67,32],[116,83,32],[82,48],[84,115,82,48],[117,116,115,114,64],[83,114,64],[116,50,80],[117,84,67,50,80],[84,115,66,112],[66,112]]
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
def g127columns : IndexTree ColumnInfo := [(32,0,95,0,8)]
def g127autos : Array (List Nat) := #[[],[101,66,16]]
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
def g191columns : IndexTree ColumnInfo := [(1,0,190,0,7),(2,0,189,0,8),(3,0,188,0,5),(4,0,187,0,7),(6,0,185,0,5),(8,0,183,0,8),(0,8,163,20,6),(10,0,181,0,5),(12,0,179,0,5),(4,8,163,16,5),(14,0,177,0,4),(16,0,175,0,8),(0,16,166,9,6),(1,16,166,8,5),(19,0,172,0,4),(24,0,167,0,7),(16,8,163,4,5),(8,16,166,1,5),(25,0,166,0,4),(9,16,166,0,4),(20,8,163,0,4),(32,0,159,0,8),(1,32,30,128,5),(35,0,156,0,4),(40,0,151,0,5),(48,0,143,0,5),(56,0,135,0,4),(128,0,63,0,8),(130,0,61,0,5),(4,128,27,32,5),(136,0,55,0,5),(160,0,31,0,7),(128,32,30,1,5),(32,128,27,4,5),(161,0,30,0,4),(129,32,30,0,4),(164,0,27,0,4),(36,128,27,0,4)]
def g191autos : Array (List Nat) := #[[],[84,115],[117,67,32],[116,83,32]]
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
def g251columns : IndexTree ColumnInfo := [(8,0,243,0,7)]
def g251autos : Array (List Nat) := #[[],[84,115],[99,65],[118,84,115,65],[118,81],[118,84,99,81]]
def g251levels : Nat → Packing
  | _ => emptyPacking
def g251index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g251 : Forest := ⟨251,7,fun j => g251samples[j]?.getD (0,0),g251columns,g251autos,g251levels,g251index⟩
def g255samples : Array (Bits × Bits) := #[(0x9b665c544a8481c32c829a3849d25a0c2e734bceaece0410b1910c9246b692285657c973ca335d593cb00f0546b90059eb43e97a932728851785431870f031165ac8b80393ba6e576270cc58c906b870841734e15dc89803598ab05c2460a6b1,0x104454110880808228020a2041d8002c08600a02808c02009111060244ac12008614a1024802115108904700443200508241c8821224200116051018407029164080a01212302c0942400010c90428108414142154888803090a9048202086a0),(0xf315668af28fdb1ca228365b7ccc05a0011317731e21482f697635c521d4e57b4580944cacd08190116899ef79421d834fcee4e488905930903982805fb1c61927af17aaf49049a676974192f0d0160363a1bd03830701b0dc1f8281c2dc6123,0x83112a82400c43108201140b24040542001210600e014836084820c40800442b4181104024900000902098cc210099010006246088901220003082011981800902040620cc814002101041843090160043212902810201b054050081825c2101),(0x380526282fa13ac851f4c9c505254980d6e8ec3804b3594a769d93b950ebc251b0d8e2a15610b8154799066089743516386914b45de9a6e1e91c2d64aa4bec2945782990b2d68e61aa4d3cd1b24a6ab680984b4c1298da14a63264e421a50a46,0x184000082381184051a442400021c800c760240c008201086414493150c8805030586481420228050588002082640402084818905528808149002d00020c144045280184104604602a043c40824a60b20098024012185a048212646400810a02),(0x96903da21572f2b1f1c959078994a771bc47364121282ac5966e24786e0f6b8886ae49c27124b27b7242ff2e0094e0b4b1b582696d3c94568c371a6b03b30075a8d6353ad9672c0089eb12ba6325f80dd24d451b8459a7c113618d0b812f118c,0x86100cb01034a2a12848198388d4226018030240202c8a411a0a044824066a838a240842212092185a40cf0a0080e094a530c6680a1400448645526011312024a0c7343889210800016b021a61259805924545098441a1c11120810b812e1184),(0xca830c6ee5a1c1ac77b2c4bb013b84b271c7189edce77b42164b82b2ec44ccc2202552493f52e619512b4f09e2177ba801c291327039cbf4fba1fd7ca29d36ceca40c4508827295a1b45be11b7c00687be220f65622167c80c13fe90c415919,0x1282044674a181cc515204830038803270c71014e5265b22464b9241a4004482002443590d10ca0850630203a411b2a000c201185038c3861ba0d078200d6480c204804048212d4a89449e11258006869a220d60222163c80c12ea00c414819),(0xadcb89db333a54791fc5b16de6a74b1fbdaa5224c4caa060c8434905e130b3e50875189fa3aee40ebf67487ce98db2673644923b555505294552488c144494c2312ef3656d2d51ee39b1b44e04f3d3ec4d148000ab72771f011403179f478e82,0xa991884a13221d3803c5e045a0014312e78660240442614040424905201081f109410899826ca6043646807ca808b20b342020284941850001124c8410049440302c118d6904416438b533460072d3ec490080008b50771c0014031517470802),(0xccf1d170b069949f14600d7679a83ea985e068495997ad010287ff4ea745b576050c4fa9e8e0fabd2497448bd27a5aa8acea4ac0268e4d44dc2df9de452a225ad1457b3d721818b9bf9e05034d50ecb938aed67098a522a72856072e55b8d214,0xce85130b040942f1560095449a91aad8dc0e80b5196a18140955b282345b194266c47298868eeb9221d4601c27a00e8acf04a8036004c04cc8c58ecc43a23d68161791d311c0cb9abcc24434d40e8b9388ed67018a522072852072e55a0d214),(0x442aa5b9d884c622461c21eaaaf556fac8da8923687abbfb99c9c28096422e0eb83cb34c1d8918aec8c55d99f53bc2670104934ee2f27258616b2c55a56fa8970e02486406e9b92b5242282d15890d903f02672424a3e96d3ce1d022fa0aa8e8,0x460a679588446000a40a01aa08c414e80818810338389a92898982c08602320ec02091061180118a88016c815113416481048146a2821250206d8051a4632a958802cc600689381b004a400915810c003602652424a380613ce19002e808a0e8),(0,0)]
def g255columns : IndexTree ColumnInfo := [(64,0,191,0,11)]
def g255autos : Array (List Nat) := #[[],[84,115],[117,67,32],[116,83,32]]
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
def g383columns : IndexTree ColumnInfo := [(1,0,382,0,9),(0,1,332,50,7),(2,0,381,0,9),(0,2,312,69,7),(3,0,380,0,6),(2,1,332,48,6),(1,2,312,68,6),(4,0,379,0,11),(5,0,378,0,7),(7,0,376,0,5),(5,2,312,64,5),(8,0,375,0,9),(0,8,99,276,7),(12,0,371,0,8),(13,0,354,0,4),(14,0,369,0,5),(16,0,367,0,11),(17,0,366,0,8),(18,0,365,0,7),(19,0,364,0,5),(18,1,332,32,5),(24,0,359,0,8),(25,0,358,0,5),(28,0,355,0,7),(20,8,99,256,5),(32,0,351,0,11),(33,0,350,0,8),(32,1,332,18,6),(35,0,348,0,5),(34,1,332,16,5),(44,0,339,0,5),(49,0,334,0,7),(48,1,332,2,5),(33,16,326,8,5),(56,0,327,0,5),(64,0,319,0,11),(65,0,318,0,7),(66,0,317,0,8),(67,0,316,0,5),(65,2,312,4,5),(70,0,313,0,7),(34,64,29,256,5),(256,0,127,0,9),(0,256,23,104,7),(264,0,119,0,6),(256,8,99,20,6),(8,256,23,96,6),(268,0,115,0,5),(260,8,99,16,5),(280,0,103,0,5),(272,8,99,4,5),(288,0,95,0,8),(289,0,94,0,5),(40,256,23,64,5),(304,0,79,0,5),(320,0,63,0,8),(322,0,61,0,5),(258,64,61,0,5),(352,0,31,0,7)]
def g383autos : Array (List Nat) := #[[],[84,131,98],[101,66,16],[100,131,82,16],[82,129,48],[101,100,131,98,129,48],[100,49,128],[101,84,131,66,49,128]]
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
theorem valid3 : Known known3 := extendKnown_ok baseKnown low3 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low7 : Lower (vars 7) (graphGoal 7) 2 := size_of (hints:=257) (by decide +kernel)
def maps7 : List (Nat × List Nat) := []
def known7 := extendKnown known3 2 maps7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid7 : Known known7 := extendKnown_ok valid3 low7 (by decide +kernel)
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
theorem s15_3_0 : block g15 3 0 1=true :=
  @streamBlock #[0,0,0,0] g15 3 0 1 4 (by decide +kernel) (by decide +kernel)
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
theorem valid15 : Known known15 := extendKnown_ok valid7 low15 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low45 : Lower (vars 45) (graphGoal 45) 3 := size_of (hints:=8965) (by decide +kernel)
def maps45 : List (Nat × List Nat) := []
def known45 := extendKnown known15 3 maps45
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid45 : Known known45 := extendKnown_ok valid15 low45 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low51 : Lower (vars 51) (graphGoal 51) 3 := size_of (hints:=1) (by decide +kernel)
def maps51 : List (Nat × List Nat) := []
def known51 := extendKnown known45 3 maps51
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid51 : Known known51 := extendKnown_ok valid45 low51 (by decide +kernel)
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
theorem s31_5_0 : block g31 5 0 1=true :=
  @streamBlock #[0,0,0,0,0] g31 5 0 1 5 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_5_1 : block g31 5 1 2=true :=
  @streamBlock #[0x1b,0xcb,0x3,0,0,0] g31 5 1 2 6 (by decide +kernel) (by decide +kernel)
theorem bl31_5 : block g31 5 0 3 = true := (@block_merge g31 5 0 1 2 s31_5_0 s31_5_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_6_0 : block g31 6 0 1=true :=
  @streamBlock #[0x1ef7bcf,0xfbf7edf,0xf7f77f,0x3d29f,0x1f] g31 6 0 1 5 (by decide +kernel) (by decide +kernel)
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
theorem valid31 : Known known31 := extendKnown_ok valid51 low31 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low47 : Lower (vars 47) (graphGoal 47) 5 :=
  lower_discard (g:=g47) (ci:=(8,0,39,0,4)) (hints:=8449) (before_sound known31 valid31) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps47 : List (Nat × List Nat) := [(47,[]),(61,[65,50]),(94,[64,65,66,67,101]),(151,[67,84,101,118]),(173,[48,65,50,83,100,118]),(181,[65,50,99,84,118]),(185,[16,65,98,83,101,118]),(188,[64,97,98,67,84,118]),(227,[16,66,99,116,117,118]),(230,[64,65,66,99,116,101]),(301,[48,65,82,100,118,135]),(331,[80,81,66,100,117,118,135]),(339,[66,99,84,117,118,135]),(345,[80,65,98,67,84,117,118,135]),(346,[64,49,98,67,84,117,135]),(358,[64,65,82,99,116,101,118,135]),(369,[65,98,115,84,118,135]),(422,[64,81,66,99,116,117,134]),(440,[64,97,114,67,84,117,134]),(454,[64,66,99,116,133,118,135]),(460,[64,97,66,99,116,133,135]),(482,[64,49,98,115,132,133,135]),(484,[64,97,82,115,132,101,118,135])]
def known47 := extendKnown known31 5 maps47
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid47 : Known known47 := extendKnown_ok valid31 low47 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low55 : Lower (vars 55) (graphGoal 55) 5 :=
  lower_discard (g:=g55) (ci:=(16,0,39,0,4)) (hints:=257) (before_sound known47 valid47) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps55 : List (Nat × List Nat) := [(55,[]),(79,[64,65,66,67,101]),(103,[16,66,100,101]),(115,[50,99]),(143,[32,67,101,118]),(174,[48,65,50,83,100,118]),(179,[65,50,99,84,118]),(206,[48,50,67,100,117]),(286,[48,33,101,118,135]),(316,[48,97,66,84,118,135]),(327,[64,65,82,100,117,135]),(348,[48,97,66,84,117,118,135]),(364,[48,97,99,116,118,135]),(376,[48,97,114,99,116,118,135]),(398,[48,65,50,67,100,117,134]),(433,[16,49,98,115,100,117,134,135])]
def known55 := extendKnown known47 5 maps55
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid55 : Known known55 := extendKnown_ok valid47 low55 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low63 : Lower (vars 63) (graphGoal 63) 8 :=
  lower_discard (g:=g63) (ci:=(32,0,31,0,7)) (hints:=8449) (before_sound known55 valid55) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps63 : List (Nat × List Nat) := [(63,[]),(95,[16,66,101]),(159,[32,67,101,118]),(175,[32,83,100,118]),(183,[99,84,118]),(231,[16,66,99,116,117,118]),(317,[32,97,82,83,100,118,135]),(350,[96,33,99,84,117,135]),(359,[16,82,99,116,118,135]),(366,[96,49,116,118,135]),(371,[98,115,84,135]),(377,[48,97,114,99,116,117,118,135]),(429,[80,97,116,134,135]),(430,[96,81,98,83,116,134]),(441,[16,97,114,116,101,134,135]),(444,[96,113,114,99,84,101,134]),(462,[96,98,67,116,133,135]),(492,[96,113,115,132,133,134])]
def known63 := extendKnown known55 8 maps63
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid63 : Known known63 := extendKnown_ok valid55 low63 (by decide +kernel)
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
theorem s111_6_0 : block g111 6 0 1=true :=
  @streamBlock #[0x2d,0x7a,0,0,0,0] g111 6 0 1 6 (by decide +kernel) (by decide +kernel)
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
theorem valid111 : Known known111 := extendKnown_ok valid63 low111 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low119 : Lower (vars 119) (graphGoal 119) 6 :=
  lower_discard (g:=g119) (ci:=(4,0,115,0,5)) (hints:=16777473) (before_sound known111 valid111) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps119 : List (Nat × List Nat) := [(119,[]),(207,[64,65,66,67,117,118]),(380,[48,113,66,84,101,135]),(414,[48,65,50,67,117,134])]
def known119 := extendKnown known111 6 maps119
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid119 : Known known119 := extendKnown_ok valid111 low119 (by decide +kernel)
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
theorem s189_6_0 : block g189 6 0 1=true :=
  @streamBlock #[0,0,0,0,0,0] g189 6 0 1 6 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_6_1 : block g189 6 1 2=true :=
  @streamBlock #[0x1b,0x3,0x3,0x19,0,0,0] g189 6 1 2 7 (by decide +kernel) (by decide +kernel)
theorem bl189_6 : block g189 6 0 3 = true := (@block_merge g189 6 0 1 2 s189_6_0 s189_6_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_7_0 : block g189 7 0 1=true :=
  @streamBlock #[0xf247bcf,0x1bf7d6df,0x3efd75f,0x7bcf,0x4529f,0x1f] g189 7 0 1 6 (by decide +kernel) (by decide +kernel)
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
theorem valid189 : Known known189 := extendKnown_ok valid119 low189 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low250 : Lower (vars 250) (graphGoal 250) 5 := size_of (hints:=1366507616) (by decide +kernel)
def maps250 : List (Nat × List Nat) := []
def known250 := extendKnown known189 5 maps250
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid250 : Known known250 := extendKnown_ok valid189 low250 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low127 : Lower (vars 127) (graphGoal 127) 9 :=
  lower_discard (g:=g127) (ci:=(32,0,95,0,8)) (hints:=16785665) (before_sound known250 valid250) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps127 : List (Nat × List Nat) := [(127,[]),(223,[64,65,66,67,117,118]),(247,[115,84]),(375,[98,115,84,135]),(381,[48,113,82,135]),(382,[112,49,66,115,84,101,135]),(415,[48,65,50,67,117,134]),(446,[112,81,114,83,100,134,135]),(478,[112,65,114,67,100,133,135]),(493,[80,113,50,132,135]),(499,[65,114,131,84,134,135]),(505,[64,113,130,131,132,133,135]),(508,[112,129,66,115,84])]
def known127 := extendKnown known250 9 maps127
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid127 : Known known127 := extendKnown_ok valid250 low127 (by decide +kernel)
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
theorem s191_6_0 : block g191 6 0 1=true :=
  @streamBlock #[0,0,0,0,0,0,0] g191 6 0 1 7 (by decide +kernel) (by decide +kernel)
theorem bl191_6 : block g191 6 0 1 = true := s191_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_7_0 : block g191 7 0 13=true :=
  @streamBlock #[0,0,0,0,0,0,0xf] g191 7 0 13 7 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_7_1 : block g191 7 13 15=true :=
  @streamBlock #[0x396c,0xffdb6,0xd9,0x659,0x39,0x195,0x1ed99,0] g191 7 13 15 8 (by decide +kernel) (by decide +kernel)
theorem bl191_7 : block g191 7 0 28 = true := (@block_merge g191 7 0 13 15 s191_7_0 s191_7_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_0 : block g191 8 0 7=true :=
  @streamBlock #[0xfffffff,0xfffffff,0x7f8ff,0xfffff,0x2dfffff,0x19659659,0x16872] g191 8 0 7 7 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_1 : block g191 8 7 61=true :=
  @block_merge g191 8 7 36 25 (@streamBlock #[0x3b956d9b6ce9b6db6db96db6db6db6dfffbde,0x3ff9b6dbdb6db6f5b6db6db6db696db96dbffd7fbc,0x3a4a66c1b96db6db96fce58,0x1dcb56dcbdb662c6cbb6dcb72db78,0x1cc558cbd9c8ce4dcb6dfd,0x7bc4f4e2f8d13f2e5fffcd,0x7f126be4d8ef1a7ca5c4e5fcbfc32cb265932cb2cb2cb2c99,0x326464cf99659] g191 8 7 36 8 (by decide +kernel) (by decide +kernel)) (@streamBlock #[0xb56abb759b63938b97136db6db3fb6db7eeff9685f78,0x5a56fe9559b61c9b6ff24b6dfcb6ebf965effffbd2dbe,0x2d76ab5adbadb1ba14ad98b6dd6add6a50ea,0xa66c6656db6d8db6dd6db6db6e852fcfc85,0xab4e876bd8cc52969cb6ea96d,0x5a76ba6d68d9b6dc9d92c1696db73f2e7,0xb5d6aed3319431b90df250d7f2c75c98d659659659,0x28a39] g191 8 43 25 8 (by decide +kernel) (by decide +kernel))
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_2 : block g191 8 68 32=true :=
  @streamBlock #[0x66db72dc5b6db6db6db6db6db6db6db6cff,0x3ccb6cb6d9bf36cfcfcf9cb2f6db6db7eff,0x15b6db6db6db6db6db6cda,0x3e7e6d6db6dd6db6cdb6db6dd65c9e,0x3735b64ae5595,0xdb96db6dd7,0x6db6ed99,0x1c9cbe4f90eab6e4e4e59ad5565cb3f2c9c5c8c5c59cd6d972cfcb2cccb2e59f,0] g191 8 68 32 9 (by decide +kernel) (by decide +kernel)
theorem bl191_8 : block g191 8 0 100 = true := (@block_merge g191 8 0 68 32 (@block_merge g191 8 0 7 61 s191_8_0 s191_8_1) s191_8_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_9_0 : block g191 9 0 3=true :=
  @streamBlock #[0x15c35dffef5ffef57fe9fffe7ffbdfefff,0x5709ffffd5fffd5eff97ffcafffff,0x15c357ffdd7ffdd6ad5f5fff,0x15c356ffd5bff56adff,0x570daef5debbd7fff,0x15c36bbd7fff,0x570d771] g191 9 0 3 7 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_9_1 : block g191 9 3 9=true :=
  @streamBlock #[0x4d6db6dffffb6db654b6db6dbf8fc7e3f16db6db487fffdf7fc0842d4bfffc9bfe0421692ee9f2a7fc770b5ddebf7dffff2b854d7ffffb7df7ff168d5ebffdfe77fc014a7f83ffffff7b,0x2b7f3bffefffddb4ed33f769da67f1690fbfd1bf696d12f7f8687fed2da12e4fa497fb4b68ef5bfdbfff696d0ffaffb7ffed2da5a5b4fff7ffdf,0x1d76febff7fedfd61775db56ef1bc5de3f16fe378b690ffffbffa5ed77a1452ffff7f0fffa5ed77a9449774fbfa5ffdded77a77775fefffbbdaef5dddd3ef6bbdffffffff7ff,0x1b6fdf5db6fffebb6da4adb6edb693bb6dbbbd7f47fc3fee9ae94d7776f5fc3e1f774d74a6bba5277ae94bba5d35d29a77777b5d35ddd2ee9ffff,0x19ebf95a5dd3fff5a6ba5256969774a4eed24bba7d3e94ba5dd2909d9dd3e9f4a5d2ee94a277725dd2949dd2ee9ffff,0x1b4d7f26b7ffffff5ba9084adb6108420a2da410842108521084210a514a410842148521fffffff,0x4d7f7d487fffffea43521095210842105148421084214521fffffff,0x5afe3ffffff7b] g191 9 3 9 8 (by decide +kernel) (by decide +kernel)
theorem bl191_9 : block g191 9 0 12 = true := (@block_merge g191 9 0 3 9 s191_9_0 s191_9_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_10_0 : block g191 10 0 1=true :=
  @streamBlock #[0x7bfbfdfbffeff,0x3def7bcf,0x3dfdfefdff,0x7dfb6df,0x1f7edf,0x777f,0x7f] g191 10 0 1 7 (by decide +kernel) (by decide +kernel)
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
theorem valid191 : Known known191 := extendKnown_ok valid127 low191 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low251 : Lower (vars 251) (graphGoal 251) 8 :=
  lower_discard (g:=g251) (ci:=(8,0,243,0,7)) (hints:=1358970881) (before_sound known191 valid191) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps251 : List (Nat × List Nat) := [(251,[]),(254,[32,67,117]),(471,[16,66,67,100,133,134,135]),(501,[16,33,50,131,100,133,118]),(506,[32,49,130,100])]
def known251 := extendKnown known191 8 maps251
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid251 : Known known251 := extendKnown_ok valid191 low251 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low255 : Lower (vars 255) (graphGoal 255) 12 :=
  lower_discard (g:=g255) (ci:=(64,0,191,0,11)) (hints:=553656577) (before_sound known251 valid251) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps255 : List (Nat × List Nat) := [(255,[]),(479,[64,65,66,67,133,134,135]),(503,[16,66,131,100,101,135]),(507,[81,130,118]),(509,[48,129,82]),(510,[128,65,130,67,100,117])]
def known255 := extendKnown known251 12 maps255
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid255 : Known known255 := extendKnown_ok valid251 low255 (by decide +kernel)
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
theorem s383_8_0 : block g383 8 0 23=true :=
  @streamBlock #[0x5,0xa,0x5,0xa,0,0,0x32,0] g383 8 0 23 8 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_8_1 : block g383 8 23 2=true :=
  @streamBlock #[0,0x3,0,0,0,0,0x3,0,0] g383 8 23 2 9 (by decide +kernel) (by decide +kernel)
theorem bl383_8 : block g383 8 0 25 = true := (@block_merge g383 8 0 23 2 s383_8_0 s383_8_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_0 : block g383 9 0 9=true :=
  @streamBlock #[0x2aaaaaa9e7f9e,0x2dfa8a86a6bdbff455,0xf5ddceeeeeef68a7,0x1294a290a7eadb49,0x68521084356d5f,0x23514a28adb7fd9,0x26a59659659fff659659659,0x15966f16593ffd9] g383 9 0 9 8 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_1 : block g383 9 9 75=true :=
  @block_merge g383 9 9 36 39 (@streamBlock #[0xdbf6db6db3,0x5f6cdcb91b,0x16ffff8cdb,0x2dff639,0x5fff0,0x2d6c72db,0x5ad9636db32,0x16b6db6e5b0e464cb2c996432,0] g383 9 9 36 9 (by decide +kernel) (by decide +kernel)) (@block_merge g383 9 45 36 3 (@streamBlock #[0x533515685fff6ca036c734720db6ccdb36db6dd6e87f28,0x1831b6c330b4b6b93bffedb6db36db36c72e39286db6edb680cb2a50aa,0xed05282d2b6effff632828006ca6a0b4a335cd05a,0x5aa2d75b33969dcfffeedb615c8db66302b6dbab4adb66b9a603d,0x16a8b41c55a1fffffe155c8e3928e415d682d05f9734,0x56e72b9ea969eda7fffb02b912ae4e5c7295368b4a3b2f4,0x66dd76c7524d5375bada4fdb6ccdb0dd702f973b66cdab70b6d6db4a1d97a,0x6cdad3aed3b76bb559d6ddae6edf99b3677e5429b0df2e4ccdba57716eb758db3,0x6401401f8] g383 9 45 36 9 (by decide +kernel) (by decide +kernel)) (@streamBlock #[0x36d8,0x50,0x1c7,0x36dd,0x2d,0x247,0x147,0x28,0] g383 9 81 3 9 (by decide +kernel) (by decide +kernel)))
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_2 : block g383 9 84 7=true :=
  @streamBlock #[0x1b6,0xdb,0xf,0x6cb,0x7fd,0xf,0xf,0x36db72,0x7cb973f36bb932cb2,0] g383 9 84 7 10 (by decide +kernel) (by decide +kernel)
theorem bl383_9 : block g383 9 0 91 = true := (@block_merge g383 9 0 84 7 (@block_merge g383 9 0 9 75 s383_9_0 s383_9_1) s383_9_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_0 : block g383 10 0 5=true :=
  @streamBlock #[0x3c878043c3c3c120907070a140a01e1e,0x1f6b62f6bfed23f6bd6bd6be84d09a1e87b6adb57ed7fdaf,0xb6db6db6dfb6dfb56dab6da5b4b696d2db7edb7ed,0x28ef477a3bd1dc3b877a3bd1de8ef477,0xa25344a6894d12909484a6894d129,0x16bcec56ffad0a2b7fd6ffadff,0xffa145fefffff851fff659,0x3fd79d8ffd659] g383 10 0 5 8 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_1 : block g383 10 5 16=true :=
  @streamBlock #[0xae749a6da4ebdffb7e6fdb636f6db636317589b18b6dbac77da96338c1ae3bf63fe1c571c0e2b8e46d70e2b8e46a6d038915c73a6a6ffbfc529d5c7005007fbfdffffeff3,0x2b6d4f6da8287d6dbadb4b16dd001b7bbb86f96d5bf7621770df5b56bc84e11e6d2910bb8490a36d5042ee1a8fdb6ad4d74bd4d4a4b6ad5b56fffffd050,0xe9726b6dba6a6bf6db6fcdba9b5ea6b6dba6a6bf8b6db631adb774d4db5293a53537c974a6a6df3a53534245d2a9251774aa474a6a55ed74a6a474a6a6d2ba535355d29a9ae94d4dfff7d3ff,0x2ee2c5988a5fbb6934a7ed1addb75a582c5db490add0ba53eff528a53ee8f8514a7636d4a2979d8da1449793c9289179028a528912514851128a53efe8a7ffeda4d2d,0x442e45e117948515af42f55ffff5e685c14521456b82538517485105e529448bca4289179485122f20a245e41448bca428917948515af42f6d7,0xf211e47922f2774d44e3eec48b9e48bc9dd24471e5c8bcb6343b125e4f3b122f279d891793cec48bc9e76245e4ee9a89dc,0x1b10bb635ec42f3b1bfedfffbce8f1af2f5ec42f3b1bf1bc5b9e27c5f17b170bcec6d08f10a7637623c42f3b1bb1f0bcec6fffdffffff,0x177458b9bfffff6de5f62966716e8f1a977058a420b1963f1ac7858b8dbef3f7f2c42fe9f7b5e5f629a9a9ffffffb5965966b359,0x2869dfe7ffdc7fffde33] g383 10 5 16 9 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_2 : block g383 10 21 20=true :=
  @streamBlock #[0x7d8b2acf17595413f3ffffeadb962cc2b58b3628e7f16d7e35cdb6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6f34ad8bd2eea9a0dfe001e,0xd8edb66dcb174af8fc5b36d3fedb6db6d9b758b1d5e2ed98b6db778b36ecaadb6db51dfed9b6dcf1ac91b6db6e2c8e6ffcb6dbb488277b6bad5aa7a37f8,0x1c0b8053baaff8000ea77147c4000a553fc7701c3b8a2b8,0x1b6dd6eec6db36db6efc42db6db6db6e58b36936dd6db6da5b6db6db636db6fe2cbf2551b7ffeedb6cdb6db314b7062e91db6dfb8fcaaa6da0d2bd097b54,0x29d36d2da14e73fffed25c3db5687487b44d0f6d2aa9cff4d097b45aa0e9097b54,0x3834a777a29273fffc340bd775a1eb1380d2bbbbd5553bbfc3408ef6824c4e,0x74685e9d2ee57a9257fd1229136a420daaf46351a08d2d74bbad753bbfffd14bba44868454d39a8d,0x36ddf7adb7f1b6deadb6db6c256dde2ac6b6dd62f8a5b6d879a54bde2ee2ae2ea777ffcf10bbd0c7e37e20c5262717,0x3b6eafc5b3f92856dd278b66287b6ffffdbf7febf17278b6e862d9862e2cb16dd2b16cc51dedbf977b6e2d7dfefffd3a7bd31b6db,0xfa757dc7ef71b] g383 10 21 20 10 (by decide +kernel) (by decide +kernel)
theorem bl383_10 : block g383 10 0 41 = true := (@block_merge g383 10 0 21 20 (@block_merge g383 10 0 5 16 s383_10_0 s383_10_1) s383_10_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_11_0 : block g383 11 0 1=true :=
  @streamBlock #[0x7ffd2977b7fcff,0,0x1fff4a5dedff,0x2db6db6d,0x77777777,0x1294a529,0x1fff,0x59] g383 11 0 1 8 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_11_1 : block g383 11 1 5=true :=
  @streamBlock #[0x1b6db6db6db6db6db6db6dbf79fe0224445c0082004922403797c61ca72bd03ccbe0d407ef3,0x1e6cffdb3f367789b717fff7ffedf45d1ae8bdae10408544d4894da7dfbfef6dfb5edb6dbff6ffffdf,0x538b5ebe9ca75b5edb5edb5edb5eda729cb5cb5cb5edb5edb5edb5ed,0x37e337fe7edf8dbbc462fefffbdfff46a35dea35c20817044d4897a91effffdfff,0x92426a4f4922524894d489a9135226a4492249135226a4,0x410104f08204102081040820410208104,0x112208ba35fe8911122745d1ae8ba35d1746ba2e8d7,0x7bc7fffbfde562ac5f1ffffffffff,0x3de7ef3] g383 11 1 5 9 (by decide +kernel) (by decide +kernel)
theorem bl383_11 : block g383 11 0 6 = true := (@block_merge g383 11 0 1 5 s383_11_0 s383_11_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_12_0 : block g383 12 0 1=true :=
  @streamBlock #[0x3fd2977b7fcffff,0x3fd2977b7fcff,0,0xff4a5dedff,0xb6db6d,0x777777,0x4a529,0xff] g383 12 0 1 8 (by decide +kernel) (by decide +kernel)
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
theorem valid383 : Known known383 := extendKnown_ok valid255 low383 (by decide +kernel)
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
def deadcolumns : IndexTree ColumnInfo := [(1,0,510,0,12),(0,1,460,50,8),(2,0,509,0,12),(0,2,440,69,8),(3,0,508,0,9),(2,1,460,48,7),(4,0,507,0,12),(0,4,369,138,8),(5,0,506,0,8),(6,0,505,0,9),(4,2,440,65,7),(2,4,369,136,7),(7,0,504,0,7),(5,2,440,64,6),(8,0,503,0,12),(0,8,227,276,8),(9,0,486,0,8),(10,0,501,0,8),(12,0,499,0,9),(8,4,369,130,7),(4,8,227,272,7),(14,0,497,0,7),(10,4,369,128,6),(15,0,480,0,4),(16,0,495,0,13),(0,16,486,9,10),(17,0,494,0,11),(16,1,460,34,7),(19,0,492,0,8),(16,4,353,138,7),(21,0,490,0,7),(21,2,424,64,5),(24,0,487,0,11),(8,16,486,1,9),(25,0,486,0,8),(9,16,486,0,8),(27,0,484,0,5),(11,16,484,0,5),(24,4,353,130,6),(29,0,482,0,5),(26,4,353,128,5),(32,0,479,0,12),(0,32,94,385,8),(32,1,460,18,7),(1,32,94,384,7),(35,0,476,0,7),(34,1,460,16,6),(36,0,347,0,8),(39,0,344,0,4),(40,0,471,0,8),(49,0,462,0,8),(48,1,460,2,6),(50,1,460,0,5),(56,0,455,0,7),(64,0,447,0,13),(0,64,189,258,10),(66,0,445,0,11),(2,64,189,256,9),(67,0,444,0,8),(66,1,396,48,6),(70,0,441,0,8),(69,2,440,0,5),(74,0,437,0,7),(74,4,305,128,5),(80,0,431,0,11),(83,0,428,0,7),(96,0,415,0,9),(96,1,396,18,6),(98,1,396,16,5),(128,0,383,0,13),(128,1,332,50,7),(3,128,344,36,6),(132,0,379,0,11),(4,128,347,32,9),(133,0,378,0,7),(134,0,377,0,8),(132,2,312,65,6),(133,2,312,64,5),(136,0,375,0,9),(128,8,99,276,7),(140,0,371,0,8),(132,8,99,272,6),(138,4,369,0,5),(144,0,367,0,11),(152,4,353,2,5),(160,0,351,0,11),(160,1,332,18,6),(162,1,332,16,5),(164,0,347,0,8),(36,128,347,0,8),(172,0,339,0,5),(176,1,332,2,5),(180,0,331,0,5),(192,0,319,0,11),(198,0,313,0,7),(256,0,255,0,12),(258,0,189,0,8),(260,0,251,0,8),(264,0,247,0,9),(256,8,227,20,7),(8,256,151,96,7),(268,0,243,0,7),(260,8,227,16,6),(273,0,238,0,7),(280,0,231,0,8),(276,8,227,0,5),(288,0,223,0,9),(256,32,94,129,7),(32,256,151,72,7),(257,32,94,128,6),(296,0,215,0,7),(40,256,151,64,6),(304,0,207,0,6),(288,16,198,9,6),(273,32,78,128,5),(56,256,135,64,5),(320,0,191,0,11),(256,64,189,2,9),(322,0,189,0,8),(258,64,189,0,8),(324,0,187,0,7),(324,8,163,16,5),(321,32,30,128,5),(388,8,99,16,5),(168,256,23,64,5),(224,256,23,8,5)]
def deadautos : Array (List Nat) := #[[],[118,130,81],[100,131,82,16],[118,133,100,131,50,33,16],[116,83,32],[118,116,83,130,49,32],[118,133,33,48],[82,129,48],[118,133,116,83,82,81,80],[116,50,129,80],[100,49,128],[118,100,83,130,81,128]]
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
theorem dead_start {prior : Nat → Nat}
    (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geometry : graphValid dead prior=true) (checks : checkedTables dead 14) :
    Impossible graph 14 inputs.toFinset := by
  have noRun := root_index (g:=dead) low geometry checks (k:=14) (by decide)
    (i:=0) (ws:=inputs) (by decide +kernel)
  have tgt : targetOf dead=graph := by decide +kernel
  exact tgt ▸ noRun

theorem live_reach {T : Sig} (hp : proper T) {k t} {ws : List Sig} (nd : ws.Nodup)
    (h : Live T k t ws.toFinset) :
    ∃ q bank, Reach (ws.map observe) q bank ∧ Available bank (observe T) ∧ q ≤ k := by
  obtain ⟨q,bank,hr,ha,hl⟩ := contraction (observe_proper hp) (list_run h ws nd rfl)
    (ws.map observe) (Reach.start) (fun a ha => Or.inl ha)
  exact ⟨q,bank,hr,ha,by omega⟩

theorem lower_split {T : Sig} {ws : List Sig} {x n : Sig} {L : Nat} (hp : proper T) (nd : ws.Nodup)
    (ess : ∀ a ∈ ws, a ≠ x → Essential T (ws++[n]) a) (r s : Row) (d : bit r T ≠ bit s T)
    (iso : ∀ v ∈ ws, v ≠ x → bit r v = bit s v)
    (plain : Lower ws T (L+1)) (both : Impossible T L (ws++[n]).toFinset)
    (only : Impossible T L (ws.filter (fun a => a != x) ++ [n]).toFinset) :
    Lower (ws++[n]) T (L+1) := by
  intro p bank h ha
  obtain ⟨k,t,S,hk,run,hs⟩ := reach_live hp h ha
  by_contra! small
  rcases split_roots ws x n run hs ess r s d iso with e | e | e <;> subst e
  · obtain ⟨q,bk,hr,hb,hq⟩ := live_reach hp nd run
    have := plain q bk hr hb
    omega
  · exact both k t (by omega) run
  · exact only k t (by omega) run

theorem reach_extra {ws : List (Wire Row)} {n : Wire Row} {a : Wire Row} (ha : a ∈ ws) (hn : n = inv a)
    {p bank} (h : Reach (ws++[n]) p bank) :
    ∃ out, Reach ws (p+1) out ∧ ∀ v ∈ bank, v ∈ out := by
  induction h using Reach.ind with
  | start =>
    refine ⟨inv a :: ws,Reach.one Reach.start (Or.inl ha),?_⟩
    intro v hv
    rcases List.mem_append.mp hv with h | h
    · exact List.mem_cons_of_mem _ h
    · rw [List.mem_singleton.mp h,hn]
      exact List.mem_cons_self
  | one h hv ih =>
    obtain ⟨out,hr,hs⟩ := ih
    refine ⟨_,Reach.one hr (hv.imp (hs _) id),?_⟩
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (hs _ hv)
  | two op h hv hw ih =>
    obtain ⟨out,hr,hs⟩ := ih
    refine ⟨_,Reach.two op hr (hv.imp (hs _) id) (hw.imp (hs _) id),?_⟩
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (hs _ hv)

theorem lower_weak {T : Sig} {ws : List Sig} {x : Sig} {L : Nat} (hx : x ∈ ws)
    (h : Lower ws T (L+1)) : Lower (ws++[neg x]) T L := by
  intro p bank hr ha
  rw [List.map_append] at hr
  obtain ⟨out,ho,hs⟩ := reach_extra (a:=observe x) (List.mem_map_of_mem hx) (obs_neg x) hr
  have := h (p+1) out ho (ha.imp (hs _) id)
  omega

def x0 : Sig := inputs.getD 0 zero
def weakOK (old : List (Nat × Nat)) (e : Nat × Nat) :=
  (vars e.1 == vars (e.1-512) ++ [neg x0]) && (vars (e.1-512)).contains x0 &&
    (graphGoal e.1 == graphGoal (e.1-512)) && (boundsBefore old (e.1-512) == e.2+1)
theorem addWeak {old : List (Nat × Nat)} (es : List (Nat × Nat)) (previous : Known old)
    (ok : es.all (weakOK old) = true) : Known (es ++ old) := by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · have w := List.all_eq_true.mp ok e hx
    simp only [weakOK,Bool.and_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at w
    have low := before_sound old previous (e.1-512)
    rw [w.2] at low
    rw [w.1.1.1,w.1.2]
    exact lower_weak w.1.1.2 low
  · exact previous e h

def splitOK (g : Forest) (m hints : Nat) (r s : Row) (old : List (Nat × Nat)) (i j : Nat) :=
  (vars g.mask == vars m ++ [neg x0]) && decide ((vars m).Nodup) && properB (targetOf g) &&
    (graphGoal m == targetOf g) && (boundsBefore old m == g.cap+1) &&
    ((vars m).all (fun a => a==x0 || ((graphPairs (m-1) hints).map Prod.fst).contains a)) &&
    checkEssential (targetOf g) (vars g.mask) (graphPairs (m-1) hints) &&
    (bit r (targetOf g) != bit s (targetOf g)) && (vars m).all (fun v => v==x0 || bit r v == bit s v) &&
    indexedRoot g g.cap i (vars g.mask) &&
    indexedRoot g g.cap j ((vars m).filter (fun a => a != x0) ++ [neg x0])

theorem lower_forest9 {g : Forest} {old m hints r s i j} (previous : Known old)
    (geom : graphValid g (boundsBefore old) = true) (blocks : checkedTables g g.cap)
    (ok : splitOK g m hints r s old i j = true) : Lower (vars g.mask) (graphGoal g.mask) (g.cap+1) := by
  simp only [splitOK,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq,bne_iff_ne,List.all_eq_true,
    Bool.or_eq_true,List.contains_eq_mem] at ok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hv,nd⟩,hp⟩,hg⟩,hb⟩,hall⟩,hess⟩,hd⟩,hiso⟩,ia⟩,ib⟩ := ok
  have low := before_sound old previous
  have plain := low m
  rw [hb,hg] at plain
  have A := root_index low geom blocks (Nat.le_refl _) ia
  have B := root_index low geom blocks (Nat.le_refl _) ib
  rw [hv] at A hess
  have all := essential_ok hess
  change Lower (vars g.mask) (targetOf g) (g.cap+1)
  rw [hv]
  apply lower_split (x:=x0) (proper_of _ hp) nd _ r s hd _ plain A B
  · intro a ha hne
    exact all a (List.mem_toFinset.mpr ((hall a ha).resolve_left hne))
  · intro v hv hne
    exact (hiso v hv).resolve_left hne

def n15d3 (i : Nat) : Nat := 0xa3df
def n15l3 : Packing := (2,0,0,0,0,3,0,n15d3)
def n15samples : Array (Bits × Bits) := #[(0xd697a7b9ef407673*repeatSamples,0x820800199b8db652*repeatSamples),(0xfdf6dfff9763f87f*repeatSamples,0x1112104404524829*repeatSamples),(0xebfffeeffcbf8f9c*repeatSamples,0x8248822282049514*repeatSamples),(0x93fbe35669bc0fe0*repeatSamples,0x6d8751492c1b6ae0*repeatSamples),(0x0*repeatSamples,0x0*repeatSamples),(0x0*repeatSamples,0x0*repeatSamples),(0x0*repeatSamples,0x0*repeatSamples),(0x0*repeatSamples,0x0*repeatSamples),(0x0*repeatSamples,0x0*repeatSamples)]
def n15columns : List ColumnInfo := []
def n15autos : Array (List Nat) := #[[],[48,33]]
def n15levels : Nat → Packing
  | 3 => n15l3
  | _ => emptyPacking
def n15index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def n15 : Forest := (527,3,fun j => n15samples[j]?.getD (0,0),n15columns,n15autos,n15levels,n15index)
set_option maxHeartbeats 0 in
theorem geomn15 : graphValid n15 (boundsBefore known383) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn153_0 : block n15 3 0 1=true :=
  @streamBlock #[0,0,0,0,0] n15 3 0 1 5 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn153_1 : block n15 3 1 1=true :=
  @streamBlock #[0,0,0,0] n15 3 1 1 4 (by decide +kernel) (by decide +kernel)
theorem alln153 : block n15 3 0 2=true := (@block_merge n15 3 0 1 1 sn153_0 sn153_1)
theorem tablesn15 : checkedTables n15 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block n15 0 0 0 = true)
  · exact (rfl : block n15 1 0 0 = true)
  · exact (rfl : block n15 2 0 0 = true)
  · exact alln153
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lown15 : Lower (vars 527) (graphGoal 527) 4 :=
  lower_forest9 (g:=n15) (m:=15) (hints:=8993) (r:=2) (s:=3) (i:=0) (j:=1) valid383 geomn15 tablesn15 (by decide +kernel)
def mapsn15 : List (Nat × List Nat) := [(527,[]),(541,[50,65]),(647,[115,99,83,67]),(677,[114,33,97,82,50,65]),(793,[131,115,99,50,82,65]),(865,[130,33,113,99,82,65])]
def knownn15 := extendKnown known383 4 mapsn15
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validn15 : Known knownn15 := extendKnown_ok valid383 lown15 (by decide +kernel)
def n23d3 (i : Nat) : Nat := 0xa3df
def n23l3 : Packing := (2,0,0,0,0,3,0,n23d3)
def n23samples : Array (Bits × Bits) := #[(0xd69fa7b9efdc73f3*repeatSamples,0x8208001093849252*repeatSamples),(0xedfedeef96e3fc9f*repeatSamples,0x1010000d08492889*repeatSamples),(0xebf7feeffc238f1c*repeatSamples,0x834a92628616d714*repeatSamples),(0x0*repeatSamples,0x0*repeatSamples),(0x93fbe35669bc0fe0*repeatSamples,0x6d8751492c1b6da0*repeatSamples),(0x0*repeatSamples,0x0*repeatSamples),(0x0*repeatSamples,0x0*repeatSamples),(0x0*repeatSamples,0x0*repeatSamples),(0x0*repeatSamples,0x0*repeatSamples)]
def n23columns : List ColumnInfo := []
def n23autos : Array (List Nat) := #[[],[16,66]]
def n23levels : Nat → Packing
  | 3 => n23l3
  | _ => emptyPacking
def n23index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def n23 : Forest := (535,3,fun j => n23samples[j]?.getD (0,0),n23columns,n23autos,n23levels,n23index)
set_option maxHeartbeats 0 in
theorem geomn23 : graphValid n23 (boundsBefore knownn15) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn233_0 : block n23 3 0 1=true :=
  @streamBlock #[0,0,0,0,0] n23 3 0 1 5 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn233_1 : block n23 3 1 1=true :=
  @streamBlock #[0,0,0,0] n23 3 1 1 4 (by decide +kernel) (by decide +kernel)
theorem alln233 : block n23 3 0 2=true := (@block_merge n23 3 0 1 1 sn233_0 sn233_1)
theorem tablesn23 : checkedTables n23 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block n23 0 0 0 = true)
  · exact (rfl : block n23 1 0 0 = true)
  · exact (rfl : block n23 2 0 0 = true)
  · exact alln233
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lown23 : Lower (vars 535) (graphGoal 535) 4 :=
  lower_forest9 (g:=n23) (m:=23) (hints:=289) (r:=2) (s:=3) (i:=0) (j:=1) validn15 geomn23 tablesn23 (by decide +kernel)
def mapsn23 : List (Nat × List Nat) := [(535,[]),(539,[50,65]),(551,[84]),(569,[65,33,82,49]),(611,[66,100,82,50]),(675,[114,33,97,82,50,65]),(689,[114,33,97,82,49]),(817,[130,114,33,97,82,49])]
def knownn23 := extendKnown knownn15 4 mapsn23
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validn23 : Known knownn23 := extendKnown_ok validn15 lown23 (by decide +kernel)
def n31d5 (i : Nat) : Nat := 0x5285e957d445f211
def n31l5 : Packing := (3,1,3,0,0,4,0,n31d5)
def n31d6 (i : Nat) : Nat := 0x63441680fbf
def n31l6 : Packing := (2,0,3,0,0,5,0,n31d6)
def hashn31l6 (i : Nat) : Nat := 0xd5f40780000649c0
def n31samples : Array (Bits × Bits) := #[(0xa8d01f003e2ab86f*repeatSamples,0x30086318c628282d*repeatSamples),(0x75640007fe1be3f0*repeatSamples,0x4b18c631803c350*repeatSamples),(0xd79c00ffc199468f*repeatSamples,0x820e318c6318048b*repeatSamples),(0xcb3fe0f801e4457c*repeatSamples,0x7840c6318ce04074*repeatSamples),(0xfbafff0001649b93*repeatSamples,0x821718c631049382*repeatSamples),(0x0*repeatSamples,0x0*repeatSamples),(0x0*repeatSamples,0x0*repeatSamples),(0x0*repeatSamples,0x0*repeatSamples),(0x0*repeatSamples,0x0*repeatSamples)]
def n31columns : List ColumnInfo := [(1,0,30,0,4),(2,0,541,0,4),(4,0,539,0,4),(8,0,535,0,4),(16,0,527,0,4)]
def n31autos : Array (List Nat) := #[[],[65,50],[16,66],[64,65,66,67],[32,67],[48,65,50,67],[48,33],[32,49,66,67],[16,33,50,67],[64,49]]
def n31levels : Nat → Packing
  | 5 => n31l5
  | 6 => n31l6
  | _ => emptyPacking
def n31index : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 4 8 2 7 2 1 (hashn31l6)
  | _ => fun _ => none
def n31 : Forest := (543,6,fun j => n31samples[j]?.getD (0,0),n31columns,n31autos,n31levels,n31index)
set_option maxHeartbeats 0 in
theorem geomn31 : graphValid n31 (boundsBefore knownn23) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=2) ?_⟩,listPieces_all (d:=3) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn315_0 : block n31 5 0 3=true :=
  @streamBlock #[0,0,0,0,0] n31 5 0 3 5 (by decide +kernel) (by decide +kernel)
theorem alln315 : block n31 5 0 3=true := sn315_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn316_0 : block n31 6 0 1=true :=
  @streamBlock #[0x1b,0x5,0x7,0x9,0x1,0x3] n31 6 0 1 6 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn316_1 : block n31 6 1 1=true :=
  @streamBlock #[0xf,0xf,0xf,0xf,0xf] n31 6 1 1 5 (by decide +kernel) (by decide +kernel)
theorem alln316 : block n31 6 0 2=true := (@block_merge n31 6 0 1 1 sn316_0 sn316_1)
theorem tablesn31 : checkedTables n31 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block n31 0 0 0 = true)
  · exact (rfl : block n31 1 0 0 = true)
  · exact (rfl : block n31 2 0 0 = true)
  · exact (rfl : block n31 3 0 0 = true)
  · exact (rfl : block n31 4 0 0 = true)
  · exact alln315
  · exact alln316
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lown31 : Lower (vars 543) (graphGoal 543) 7 :=
  lower_forest9 (g:=n31) (m:=31) (hints:=17185) (r:=2) (s:=3) (i:=0) (j:=1) validn23 geomn31 tablesn31 (by decide +kernel)
def mapsn31 : List (Nat × List Nat) := [(543,[]),(679,[115,67,100,83]),(825,[131,115,65,50,98,81]),(867,[131,50,66,116,99,82])]
def knownn31 := extendKnown knownn23 7 mapsn31
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validn31 : Known knownn31 := extendKnown_ok validn23 lown31 (by decide +kernel)
def n187d5 (i : Nat) : Nat := 0x2f561
def n187l5 : Packing := (1,1,1,0,0,0,0,n187d5)
def n187d6 (i : Nat) : Nat := 0x10c2e3f7f
def n187l6 : Packing := (2,0,1,0,0,3,0,n187d6)
def hashn187l6 (i : Nat) : Nat := 0x4
def n187samples : Array (Bits × Bits) := #[(0xffc08e2ff1ed699*repeatSamples,0x421008420a0c4219*repeatSamples),(0x7f318c6de69750*repeatSamples,0xbdef318c65e29540*repeatSamples),(0x0*repeatSamples,0x0*repeatSamples),(0xf0003e0f8eeb2d32*repeatSamples,0xd6b43e0b8e8b0530*repeatSamples),(0xff83c0af51f9692a*repeatSamples,0x294bc0a451702802*repeatSamples),(0x3fff0a2c200e7*repeatSamples,0x318ea5a0a0c200a6*repeatSamples),(0x0*repeatSamples,0x0*repeatSamples),(0x3ff5f5c00324c*repeatSamples,0xce715a5f5c003248*repeatSamples),(0x0*repeatSamples,0x0*repeatSamples)]
def n187columns : List ColumnInfo := [(10,0,689,0,4),(130,0,569,0,4)]
def n187autos : Array (List Nat) := #[[],[115,84]]
def n187levels : Nat → Packing
  | 5 => n187l5
  | 6 => n187l6
  | _ => emptyPacking
def n187index : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 1 0 6 1 1 (hashn187l6)
  | _ => fun _ => none
def n187 : Forest := (699,6,fun j => n187samples[j]?.getD (0,0),n187columns,n187autos,n187levels,n187index)
set_option maxHeartbeats 0 in
theorem geomn187 : graphValid n187 (boundsBefore knownn31) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn1875_0 : block n187 5 0 1=true :=
  @streamBlock #[0,0,0,0,0,0] n187 5 0 1 6 (by decide +kernel) (by decide +kernel)
theorem alln1875 : block n187 5 0 1=true := sn1875_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn1876_0 : block n187 6 0 1=true :=
  @streamBlock #[0,0xf,0,0,0,0x5,0] n187 6 0 1 7 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn1876_1 : block n187 6 1 1=true :=
  @streamBlock #[0,0,0,0,0,0x19] n187 6 1 1 6 (by decide +kernel) (by decide +kernel)
theorem alln1876 : block n187 6 0 2=true := (@block_merge n187 6 0 1 1 sn1876_0 sn1876_1)
theorem tablesn187 : checkedTables n187 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block n187 0 0 0 = true)
  · exact (rfl : block n187 1 0 0 = true)
  · exact (rfl : block n187 2 0 0 = true)
  · exact (rfl : block n187 3 0 0 = true)
  · exact (rfl : block n187 4 0 0 = true)
  · exact alln1875
  · exact alln1876
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lown187 : Lower (vars 699) (graphGoal 699) 7 :=
  lower_forest9 (g:=n187) (m:=187) (hints:=1349533697) (r:=2) (s:=3) (i:=0) (j:=1) validn31 geomn187 tablesn187 (by decide +kernel)
def mapsn187 : List (Nat × List Nat) := [(699,[]),(755,[99,65])]
def knownn187 := extendKnown knownn31 7 mapsn187
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validn187 : Known knownn187 := extendKnown_ok validn31 lown187 (by decide +kernel)
def n189d6 (i : Nat) : Nat := 0xfa50be99bda33fa88bf211
def n189l6 : Packing := (4,1,2,0,0,4,0,n189d6)
def n189d7 (i : Nat) : Nat := 0x20a71343f7f
def n189l7 : Packing := (2,0,2,0,0,4,0,n189d7)
def hashn189l7 (i : Nat) : Nat := 0x110b00018ce4002680
def n189samples : Array (Bits × Bits) := #[(0x83e019ac5a30dd2d*repeatSamples,0xa52911244a109d28*repeatSamples),(0x0*repeatSamples,0x0*repeatSamples),(0x1faa45f50afb20*repeatSamples,0x94a5aa40940ac920*repeatSamples),(0x7c1f347ee45123ca*repeatSamples,0x294a143e6010224a*repeatSamples),(0x7fe0e8b30c734cd1*repeatSamples,0x5294e88104634091*repeatSamples),(0x8000df4816a482de*repeatSamples,0x18c6ca48142402c6*repeatSamples),(0x0*repeatSamples,0x0*repeatSamples),(0xd731618f1433*repeatSamples,0x6318153161811411*repeatSamples),(0x0*repeatSamples,0x0*repeatSamples)]
def n189columns : List ColumnInfo := [(12,0,689,0,4),(17,0,172,0,4),(33,0,156,0,4),(132,0,569,0,4)]
def n189autos : Array (List Nat) := #[[],[115,84],[32,67,117],[32,83,116],[48,82],[112,66,115,84],[80,50,67,84,117],[64,114,83],[80,50,116],[64,114,115,116,117],[48,82,115,84],[112,66]]
def n189levels : Nat → Packing
  | 6 => n189l6
  | 7 => n189l7
  | _ => emptyPacking
def n189index : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 4 10 0 7 2 1 (hashn189l7)
  | _ => fun _ => none
def n189 : Forest := (701,7,fun j => n189samples[j]?.getD (0,0),n189columns,n189autos,n189levels,n189index)
set_option maxHeartbeats 0 in
theorem geomn189 : graphValid n189 (boundsBefore knownn187) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=2) ?_⟩,listPieces_all (d:=3) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn1896_0 : block n189 6 0 4=true :=
  @streamBlock #[0,0,0,0,0,0] n189 6 0 4 6 (by decide +kernel) (by decide +kernel)
theorem alln1896 : block n189 6 0 4=true := sn1896_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn1897_0 : block n189 7 0 1=true :=
  @streamBlock #[0x1b,0x5,0x7,0x9,0,0x5,0x3] n189 7 0 1 7 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn1897_1 : block n189 7 1 1=true :=
  @streamBlock #[0xf,0xf,0xf,0xf,0xf,0xf] n189 7 1 1 6 (by decide +kernel) (by decide +kernel)
theorem alln1897 : block n189 7 0 2=true := (@block_merge n189 7 0 1 1 sn1897_0 sn1897_1)
theorem tablesn189 : checkedTables n189 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block n189 0 0 0 = true)
  · exact (rfl : block n189 1 0 0 = true)
  · exact (rfl : block n189 2 0 0 = true)
  · exact (rfl : block n189 3 0 0 = true)
  · exact (rfl : block n189 4 0 0 = true)
  · exact (rfl : block n189 5 0 0 = true)
  · exact alln1896
  · exact alln1897
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lown189 : Lower (vars 701) (graphGoal 701) 8 :=
  lower_forest9 (g:=n189) (m:=189) (hints:=544228101) (r:=32) (s:=33) (i:=0) (j:=1) validn187 geomn189 tablesn189 (by decide +kernel)
def mapsn189 : List (Nat × List Nat) := [(701,[]),(859,[130,114,98,33,81])]
def knownn189 := extendKnown knownn187 8 mapsn189
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validn189 : Known knownn189 := extendKnown_ok validn187 lown189 (by decide +kernel)
def n215d6 (i : Nat) : Nat := 0x41c3f7f
def n215l6 : Packing := (2,0,1,0,0,3,0,n215d6)
def n215samples : Array (Bits × Bits) := #[(0xf07c3c83ba7f1c1b*repeatSamples,0x94a42c811847141a*repeatSamples),(0xffcc1f37383e5a5*repeatSamples,0x4210811262002125*repeatSamples),(0xf830e1d44eee3d2*repeatSamples,0x318e0a0900eec0c2*repeatSamples),(0x0*repeatSamples,0x0*repeatSamples),(0xf003f15ea8f8388a*repeatSamples,0x6b5bd15ea0b82880*repeatSamples),(0x0*repeatSamples,0x0*repeatSamples),(0x3ffe111e09a24*repeatSamples,0xbdef7ee111e09a00*repeatSamples),(0x3febec604065c*repeatSamples,0xce71f4b6c600061c*repeatSamples),(0x0*repeatSamples,0x0*repeatSamples)]
def n215columns : List ColumnInfo := [(1,16,198,0,4)]
def n215autos : Array (List Nat) := #[[],[32,116]]
def n215levels : Nat → Packing
  | 6 => n215l6
  | _ => emptyPacking
def n215index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def n215 : Forest := (727,6,fun j => n215samples[j]?.getD (0,0),n215columns,n215autos,n215levels,n215index)
set_option maxHeartbeats 0 in
theorem geomn215 : graphValid n215 (boundsBefore knownn189) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn2156_0 : block n215 6 0 1=true :=
  @streamBlock #[0,0,0,0,0,0,0] n215 6 0 1 7 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn2156_1 : block n215 6 1 1=true :=
  @streamBlock #[0,0,0,0,0,0] n215 6 1 1 6 (by decide +kernel) (by decide +kernel)
theorem alln2156 : block n215 6 0 2=true := (@block_merge n215 6 0 1 1 sn2156_0 sn2156_1)
theorem tablesn215 : checkedTables n215 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block n215 0 0 0 = true)
  · exact (rfl : block n215 1 0 0 = true)
  · exact (rfl : block n215 2 0 0 = true)
  · exact (rfl : block n215 3 0 0 = true)
  · exact (rfl : block n215 4 0 0 = true)
  · exact (rfl : block n215 5 0 0 = true)
  · exact alln2156
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lown215 : Lower (vars 727) (graphGoal 727) 7 :=
  lower_forest9 (g:=n215) (m:=215) (hints:=553649953) (r:=2) (s:=3) (i:=0) (j:=1) validn189 geomn215 tablesn215 (by decide +kernel)
def mapsn215 : List (Nat × List Nat) := [(727,[]),(1009,[118,33,129,82,49])]
def knownn215 := extendKnown knownn189 7 mapsn215
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validn215 : Known knownn215 := extendKnown_ok validn189 lown215 (by decide +kernel)
def n349d6 (i : Nat) : Nat := 0x20a3f7f
def n349l6 : Packing := (2,0,1,0,0,3,0,n349d6)
def n349samples : Array (Bits × Bits) := #[(0xf802cd3e45b26ed*repeatSamples,0xb5ac2cc2245a26ec*repeatSamples),(0x0*repeatSamples,0x0*repeatSamples),(0x7f0d5bb882fa58*repeatSamples,0xdef70d5bb8803a18*repeatSamples),(0xf07c320c3ff6f968*repeatSamples,0x210830000276c060*repeatSamples),(0xff83c25fc0f50f85*repeatSamples,0x4a53c21dc0810901*repeatSamples),(0x0*repeatSamples,0x0*repeatSamples),(0x3fff008e940da*repeatSamples,0x739ebaf008e140d8*repeatSamples),(0x0*repeatSamples,0x0*repeatSamples),(0x3fdaf77080036*repeatSamples,0x8c61450f75080006*repeatSamples)]
def n349columns : List ColumnInfo := [(0,1,332,16,5)]
def n349autos : Array (List Nat) := #[[],[96,132]]
def n349levels : Nat → Packing
  | 6 => n349l6
  | _ => emptyPacking
def n349index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def n349 : Forest := (861,6,fun j => n349samples[j]?.getD (0,0),n349columns,n349autos,n349levels,n349index)
set_option maxHeartbeats 0 in
theorem geomn349 : graphValid n349 (boundsBefore knownn215) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn3496_0 : block n349 6 0 1=true :=
  @streamBlock #[0,0,0,0,0,0,0] n349 6 0 1 7 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn3496_1 : block n349 6 1 1=true :=
  @streamBlock #[0,0,0,0,0,0] n349 6 1 1 6 (by decide +kernel) (by decide +kernel)
theorem alln3496 : block n349 6 0 2=true := (@block_merge n349 6 0 1 1 sn3496_0 sn3496_1)
theorem tablesn349 : checkedTables n349 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block n349 0 0 0 = true)
  · exact (rfl : block n349 1 0 0 = true)
  · exact (rfl : block n349 2 0 0 = true)
  · exact (rfl : block n349 3 0 0 = true)
  · exact (rfl : block n349 4 0 0 = true)
  · exact (rfl : block n349 5 0 0 = true)
  · exact alln3496
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lown349 : Lower (vars 861) (graphGoal 861) 7 :=
  lower_forest9 (g:=n349) (m:=349) (hints:=13019136772) (r:=16) (s:=17) (i:=0) (j:=1) validn215 geomn349 tablesn349 (by decide +kernel)
def mapsn349 : List (Nat × List Nat) := [(861,[])]
def knownn349 := extendKnown knownn215 7 mapsn349
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validn349 : Known knownn349 := extendKnown_ok validn215 lown349 (by decide +kernel)
def n455d6 (i : Nat) : Nat := 0x20a3f7f
def n455l6 : Packing := (2,0,1,0,0,3,0,n455d6)
def n455samples : Array (Bits × Bits) := #[(0x7d8cf092de5b85*repeatSamples,0xf7bd8cb0905e5b84*repeatSamples),(0xfffe12c3569ff619*repeatSamples,0x842104342810019*repeatSamples),(0xf801d3ddd6684ae*repeatSamples,0x5294083c9c268406*repeatSamples),(0x0*repeatSamples,0x0*repeatSamples),(0x0*repeatSamples,0x0*repeatSamples),(0x0*repeatSamples,0x0*repeatSamples),(0xf003e23e206d6d74*repeatSamples,0x318d4228006c6564*repeatSamples),(0x3fdc189f920a6*repeatSamples,0xad6bf5c101d920a0*repeatSamples),(0x3fdfe36000b4a*repeatSamples,0xce72bdd636000a0a*repeatSamples)]
def n455columns : List ColumnInfo := [(0,256,647,64,5)]
def n455autos : Array (List Nat) := #[[],[98,135]]
def n455levels : Nat → Packing
  | 6 => n455l6
  | _ => emptyPacking
def n455index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def n455 : Forest := (967,6,fun j => n455samples[j]?.getD (0,0),n455columns,n455autos,n455levels,n455index)
set_option maxHeartbeats 0 in
theorem geomn455 : graphValid n455 (boundsBefore knownn349) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn4556_0 : block n455 6 0 1=true :=
  @streamBlock #[0,0,0,0,0,0,0] n455 6 0 1 7 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn4556_1 : block n455 6 1 1=true :=
  @streamBlock #[0,0,0,0,0,0x19] n455 6 1 1 6 (by decide +kernel) (by decide +kernel)
theorem alln4556 : block n455 6 0 2=true := (@block_merge n455 6 0 1 1 sn4556_0 sn4556_1)
theorem tablesn455 : checkedTables n455 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block n455 0 0 0 = true)
  · exact (rfl : block n455 1 0 0 = true)
  · exact (rfl : block n455 2 0 0 = true)
  · exact (rfl : block n455 3 0 0 = true)
  · exact (rfl : block n455 4 0 0 = true)
  · exact (rfl : block n455 5 0 0 = true)
  · exact alln4556
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lown455 : Lower (vars 967) (graphGoal 967) 7 :=
  lower_forest9 (g:=n455) (m:=455) (hints:=26440894241) (r:=2) (s:=3) (i:=0) (j:=1) validn349 geomn455 tablesn455 (by decide +kernel)
def mapsn455 : List (Nat × List Nat) := [(967,[])]
def knownn455 := extendKnown knownn349 7 mapsn455
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validn455 : Known knownn455 := extendKnown_ok validn349 lown455 (by decide +kernel)
def n191d6 (i : Nat) : Nat := 0x2887d684985d22287d68497a2121
def n191l6 : Packing := (2,4,4,0,0,3,0,n191d6)
def n191d7 (i : Nat) : Nat := 0x9080000000502012112904902000000005085089080000002840000208000000010210210210200040c4082bb51a651e853d9c4ce4f228b40deef276ba1c6de6cb3582b5582ad4ca14e2411686409d4e06b33184b857258fc6627110742205004fd6448758e3fb2443ac71fd9121d638fe4bb0c9967721d634ca3fb2243c459f59121e228fe4c2e91147f262225c6afb2a392831fc9761931cfac32e298f754c9714c73e90ea8a631fc97a2121abeca8e4a04fd646884823fb30392215bd941c910afac88e48857e640724427e32243ac73d8988cd729dd4cb08396ce616441cb6b30b198e5b99848cc729ecc9d10a15f86448788bd94cd19c45f4a558ce228fc4bb0aa0fcc95644847da4cd19c23f52558ce11bd8ca0e508ff08ce228463eb2243ac71be9961072c9ec2c8839657616331cb33b09198e51f59121e22be4c99011156d650728467e323442413f09884520
def n191l7 : Packing := (47,3,4,0,0,9,0,n191d7)
def hashn191l7 (i : Nat) : Nat := 0xe6c
def n191d8 (i : Nat) : Nat := (if i<1 then 0x5aa9a65a51a25a119cd9b998d9619359098dd8c989d88985d83181d8097f57c97b577175d73171d6a967d66963d5e15555295154e94d54794353a93652f12c526923d1c91550f909d010f3cee0eb4ea0e74e60e4ce20df4dc8d6cce0c84c10b84b58b44b18b04aa8a7ca68a54a28a149d09bc9789649208f48c889c8588147d07a47607347086946506245e05b458855c5305044d84ac49846c45842c4183ec3d83ac39836c35832c3002ec2c027c2381f41c816c1401140e80bc002ffa2163bfc8758f7f58d72bfd831caff60472dfd541caffa2132bfc874caff61932dfd764cb7f5d532fdd634cb7f5c932dfd7488b7f58d71dfd325c77f88971dfc72506ffa2131bfc874c6ff61931dfd764c77f5d531dfd724c7f74c931ff5514c6ffa2121dfd87486ff21d21dfd74486ff60d21dfd734877f5c921fec72487fd4c521dfc72502ff61930fdd634c3f74c530bfe88482ff60d20ff481483fb48520ff930482ff60d10bfd824437f1c910ff920442fea2154bf887553ee5d644f7a555cefea2163bf88758efea2153bf88754ff65da33fd9758cfee91172fda335cbfa88972bf9841cbee91072bf9831cbf68cc72bf9811cafea2142bf88750bbe99942bf98550bde95542fb97450bee59142fb95450bfa1c942bfa884cafe21d32bf9864cbbe99932bf9854cbde95532fd9634cbfa21e22fea7788bfa5d222fe97388bfa58e22fe95388bee91171fda335c7fa88971bfa88506fe21d41efa66506fe61541f7a55507ee50941bfa884c6fe21d31bf9864c7be99931bf9854c7de95531fd9324c7fa88931ff1714c7fc54531bfa88486fe21d21bf984487ee91121bf983487f68cd21fe872487fc4c521ff174847fc55211ff173847fc58e11ff153847fc5ca11ff072847fc50a11ff1328467f21d54dbd75913cf95644d7e555ce7f21d639fc8754f775da33ede668cf775d633f5e558cf6f91172dde335caef61072bf9801ca7f61072dbe441ca7f60c72dde331ca7f604729fc8750b6f5d142dec7250a7f21d329fc8788b7b5ca22ded7488beb91222ded7388bf38ce22fe88088b6f91171dde335c77b889719fc875067f21d31df5714c67f21d21dec724877d5d211fb6448477d5ce11fd6338477d5ca11df472847f988a11efa66502fe61540f7a55503ee55140fea22503ee50540ff211502fe61930efa664c2fe61530f7a554c3f658d30fd9534c37e5c930fea224c3f64c530ff2114c2fea2120dfa77482fe61120fba44482fe60d20df973483f68cd20fe942483fa88920ff0814837e5c520fe921483fc84520bf984083ee91020bf983083f68cc20bf981083fc84420bf984443ee91110bf983443f68cd10bf9824437e5c910fea22443fc50510f3a55913b699a33f5a558ceee61072dea7788bf28ce22fb244847f48ce11fe2228466f61072 else 0xa10801122087104388708118a088008411c408e2682d50204810248811c31a8150110a009008803541001c43a02687406386241aa063847684000710e00801c403438c00c040e31c1112510301a206440200e19031e010e00880043c040c708811001541a8200541a83506a08015102a835502602404408040d01128150121a150110813412881501a03405a081a081a08080800c040000280d01050100840a80d01128102808081040a0340630c61602060208c2c04000301034c080c040286484428206822d448c50c8a822941014103551036aa1099b1d02510310e53009180b038a31c210230e410a1c120840231280463042d0394608504800a1d1534c0c108010800084108212870463042d03964a1018c10239021850442d410541054d303a020050100040800102010d0a80d01a02434220a10040a808640a8088111a613206c0a3086c0980c6160318530a614c20602060204c20602060208c20040c05aa04d5026a810814da606c0580b018c2c0d98a0f421eeb2e9ee5ae16dd2d76d32d1ecf2caec6ac3ebfabb6b72b16aeaaa6a62a369c297e93a8de89a83e8127ce7ba7767326ee69266660a5c656a50e4ca4b645a4163d238e3323062da29626a23e22a2161ea1be19216615213e0fa0ce08a05e032005ff1fc5f99f55f29ee5eb9e75e49e05dd9dadd81d55d41d15d01cd5cc1c95c81c6dc41c2dc19c05bf1bc5b99b85b59b45b01ad)
def n191l8 : Packing := (223,2,4,0,0,12,0,n191d8)
def hashn191l8 (i : Nat) : Nat := 0x891c2721554742dc16b0d54c000428222155017f9a000eca000208e43801e19b0221210fc00000c1140302024ba1405fd2b00090b21c324b5ce0751eb2e456f13d1be0c12a81811aa8840ae8a80ea04009e2541f929f2c000442126065b4a521f1000022311db053464065573480a1cd1001020046005
def n191d9 (i : Nat) : Nat := 0x901352047490b30290729013520479883ac10072027a404c514ce0d20e62827ac10e400f48098a2240e01e90910467c03470127a404c520a7a020e310664d60082083ac0c072006a41483501050106a41483520050106a414041a90520d48014041006a4100352084520602808a1a0a020d4828148190829e80834f48190a29e8083cf481a90414c3ac0133317582195326b052083a1e007d60630106a414041a90552003214041100a40ca41a9049e9039e90354c9ac175818ed5582ab54ca87ce797f2723544283efdde53a2708d99a432a618bb9682c1550a3d38a5346a870fc9e537a6a4bb95426c4387d0dc17c280488730b411819014001ff553feb1ffd53ff8e5ff50bfe997fe22ffa83ff4c7fe90ffd40ffa61ff483fe887fa77ff2e9fe553fcb9ff963ff2a7fe5cbfc397f942ff265fe5c7fca0ff931ff2437f5d3df225fd73fbc677f5cafe397ee22bfae3fd847fca07f930ff241fe083fc885fa77f7489f68cff5117f211
def n191l9 : Packing := (47,1,4,0,0,11,0,n191d9)
def hashn191l9 (i : Nat) : Nat := 0x930786134c48673454805509a9534615484274bc37f58f0663197d2286b09a1824a89ab1c5ddba337c2ea67f40fc2eb0d4a2c94d700008b0b4d6c414568e3682bac29d21400050954004629449b0a0000e0f6c94c07acc6f459080105709640715980001688157c00075e2ca1c1f4879030fcd515c2e2781f8000a14e02cc1d508391d8d1e34f207a7627891472688ca520452c29743baddbca6e18f704b3584d234ac00331628d0e2275a6e2da56c85e703e9332195b45fc87f71c49b443b0810003493a590587928842dc18bd9e0000981868d93a0000827808f676e0cc859501d01130bf43af05b84ba362d1d1082038502d9bc265a09e464224811c1186128d1c111d3928e314442050ed8d8496e31874dc5476fc00045c616f654a045d038d21863e559a24207841331b2d4478dc05255c04585c5dc08b8bf910d8dd375109d76524a9d1ac07cf43c000d32c4dad811c4dc41f954404b520a122898b1a00000000000b2be4be0001cd1000203fa6d8c7bd42a576d2ae81a68935060003175f0d9c73351e05a431000024cd08640a9497d15f07fa11d08b12e40005128cac957057a4441c196035899f6690b4002a95686920b3f682c5cb544801a3015270001157140b939b63800031b40000001c56020acc8704f48d32c74bba0085bb10ad43254ca8d30512806072346f4145d2f02f5c3904b352d000209ca2285b9969512a3087dcf032989f00001140002088a1b00001715174d13f455d4eccdbe3259ab25ba08f95fccce382e46a517a88ec47e13f014241490f2460307f009c10085b353616bf2820a433661cd025601827448b832a80dee30a8a8b1b80448754d584041167b29cc24b6cc0c712b6100f91bc64e410103e1dd804d0c2d46502380c917c0b7e33ed69113bc35005dcbc00c447221a4c4650d08b5f07581b010c000d091e0203040b08020d0f0a0c250000010c080108040113048d000a000252000e020d01040002022920002a0f0011292400130e201a013505000804000602060a061903040107180432070401001310263e030c06030a000201010515031b2a13055521141e02020002271a1b46241e2e0019
def n191d10 (i : Nat) : Nat := 0x3a81985412a0feff
def n191l10 : Packing := (2,0,4,0,0,5,0,n191d10)
def hashn191l10 (i : Nat) : Nat := 0x3831c5fcafd3cc9c892d53825846d8ec66c3c82983789bc7e848c581b2927801d62850c19485c0a5494b000397c002804414001d2399c0398a0000c83d9b089d45c96812d0a042954d0f47480c003d40a3295d17400201f48cc4f16eda9c7b82f9924238b546acb846f0a7da7463c564704a860454c610d01e08b14307d181019000b80
def n191samples : Array (Bits × Bits) := #[(0x8ff9ff6bd7d1f858797267c57e9d5a96ed734c7eed7c67d95cfd2f92713411fdaba5b9fabfbdbe0070dde370e7f50cfbbaf75f6ffaa1b33f9bf33a2c570bc0229d710c33e85f5b2800f03a183ff10251bd37ba40348a08223182c3af17acdda1,0x8600080000800400400004690100c425000018f0900422020c840500410c10834000404c96428150860432002000020000a38082281590208e0000004205c00880045040000ac0038e2012002480932204a100644002002001c0c286008cdd81),(0x3463f9604287c0b15d967c7731db6eccc0acb7823f9bb3c599e01ec60c1eb3ecf0dd3abf891f47245753bd1a75cea7383c1de4adbfd2ec97fc73a7bac1305db76019b48e2573ce5d521147b8ea48c01048501e1f75a8b71ee12095c912cd405a,0x28a274482e3ea0843eb538964e900942d10ea205403908a56202325e18a20c1400ea240108005e021922006313f21d46881c3b1d95826a481078202508222503164a21997cd42544011448241930249ddb527e99318897cee42415490a402276),(0xa3ec3bb4327b56e6a6ffed2badc0d16b62ac6e8fd097ab878f4ec84eff4af695bf9af6bf6edf73ea5d5f17876bea61d35fe9bb90d45c9d72b77edfdfbdbeafffc487b5ba97b7cee7e9f34aaff69b40ae406c41b6c160749c9a539502c0611789,0x4119023640000d3200080348200010040030080202800400011100208008c06180000000804480980419009c0c04c220120200000019052280070282114412c0082014400200822310c880914600c902040c8122c460601010138200a1290589),(0x6b17eda16fc4b69de7abd53885fbfd60bb43ce050e6a19479b0b78821a7564a527f04d46e462a15b9a59dced78ca1d6d5662696dbdc060e7e23ddacf25ef944bb68b26e40aeac4839d3cc223d976820002e043a8891f8bc3547d4518629252c6,0x16e2700105d0108d804320234c4082c0060830b8e01102f246c24dda380012021500c84917115400a382bd00120a0104a091cc641700e0085a2050516819640654d2c3a4812c4950c805512a018e32248ae3620c190e888b40cc551842867a62),(0x98f7759984d0122dd2f793d1efaa8f9ecf2bd0dfdec6de59e151e4e8cd51f6960aebaf5a70c4ecf62ec2df62fa7dfb0450974f6ca2a742aa4ae64b6ad3d0d182a3063be77c562b08fd1fdb7d2b6c8240639fa00808f70350ec3c226c34738454,0x9050786b0006b20333c929432131902c0c386040128c905812822208410cd680a6f04b0482c008f485040b44534f8e005402211804000d001800706852202c10b090003749124a000d0005518410cc9711c819224f11350ac3020613c71001c),(0x772f4f466d57ad89604fef491017f78630d197e530fe75f26c3e37b12dba7952cff2fcf903bab715d739b879d2e6bf848000c4fb49f213eb1bed74efe06d8de19c7ae0298d4bfdbab64bfdfa0db3fd419404144102cdcd2110936c500d412b76,0x4014b1be5066c23290050116a0950a124051a6016190c1ac8229e0dc00a2c96c027b0ca361801204008288488ccd08540b041835116a010a40412182a0d002d428282720c9201820508720de02634c4c1804f58204eddd4810130c1121432274),(0x0,0x0),(0xd0eea67f7caee1da9a8252196d7370ef39c693e0a535462bb200f06f94973e9b4dff41b5849702f5e0a547ca6c05df270df3d6753b0f5138f36802971f39ba8ff02dd332981625382ac3974cae2ebfae60680e410a40c0056ba06852ce10e013,0x92204c40028130402da2f4a04b084188050e50cc88022a4214c600005e1430006000e31c0c222923c0403623732015808499c6420804f2d1031894700c082c2b9216088a208301c001001400a98c32a1e3e308553a0000856fe060424e14c802),(0x0,0x0)]
def n191columns : List ColumnInfo := [(1,0,190,0,7),(1,16,166,8,5),(1,32,30,128,5),(2,0,701,0,8),(4,0,699,0,7),(4,8,675,16,5),(4,128,539,32,5),(14,0,689,0,4),(24,0,679,0,7),(152,0,551,0,4),(160,0,543,0,7)]
def n191autos : Array (List Nat) := #[[],[115,84],[32,67,117],[32,83,116]]
def n191levels : Nat → Packing
  | 6 => n191l6
  | 7 => n191l7
  | 8 => n191l8
  | 9 => n191l9
  | 10 => n191l10
  | _ => emptyPacking
def n191index : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 3 0 6 1 1 (hashn191l7)
  | 8 => lookupWord 16 71 6 12 6 2 (hashn191l8)
  | 9 => lookupWord 118 382 8 14 8 2 (hashn191l9)
  | 10 => lookupWord 23 76 6 12 6 2 (hashn191l10)
  | _ => fun _ => none
def n191 : Forest := (703,10,fun j => n191samples[j]?.getD (0,0),n191columns,n191autos,n191levels,n191index)
set_option maxHeartbeats 0 in
theorem geomn191 : graphValid n191 (boundsBefore knownn455) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn1916_0 : block n191 6 0 2=true :=
  @streamBlock #[0,0,0,0,0,0,0] n191 6 0 2 7 (by decide +kernel) (by decide +kernel)
theorem alln1916 : block n191 6 0 2=true := sn1916_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn1917_0 : block n191 7 0 26=true :=
  @streamBlock #[0,0,0,0,0,0x19659659659,0x19] n191 7 0 26 7 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn1917_26 : block n191 7 26 21=true :=
  @streamBlock #[0xdb,0x1bf33edb2db,0x1b,0,0x1b,0x19,0x339659,0] n191 7 26 21 8 (by decide +kernel) (by decide +kernel)
theorem alln1917 : block n191 7 0 47=true := (@block_merge n191 7 0 26 21 sn1917_0 sn1917_26)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn1918_0 : block n191 8 0 10=true :=
  @streamBlock #[0xee8dfa973ddffffdffffd9,0x3851bf52103ffe0ff,0x3dfffe,0xef29a9a9b6fdfffff,0xf6dacb2cfd659659f,0x7acb3432cb2cb2f,0x7b6fb219f] n191 8 0 10 7 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn1918_10 : block n191 8 10 36=true :=
  @streamBlock #[0xf72e5b6cc32cb2cdb6,0x1b6db6db6dbd,0x15b26ddadd0,0xcdad19,0x6ee,0x3bbb2e59659659,0x36d9972cde65971659659659659,0xacb2] n191 8 10 36 8 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn1918_46 : block n191 8 46 36=true :=
  @streamBlock #[0xf1c7ff336d98721e,0x798f0ffadb72391ba6fe5b7e9a0fe,0x2be40726e465d6cb6db36ed5,0x8879c8e46db9f6e7ced6c,0x1df253153971ff0e21863e,0xe238de271f97c9cfc8e5cbf659,0xdd18ec462e2c7c99cfca9fcd72e7e5965967e59659,0xf932c8] n191 8 46 36 8 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn1918_82 : block n191 8 82 36=true :=
  @streamBlock #[0x386db56db6cb6d8,0xf1ff2714d1b6db26c96d4,0x1e3dc41a36d985b75,0x7edcad6db7476cd5,0x619b72f975b96d8fb4a,0xa18f9adb6ae59659659,0x18e57e68f65965965965b9,0x3e5c8] n191 8 82 36 8 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn1918_118 : block n191 8 118 36=true :=
  @streamBlock #[0x3cdb6db6db,0x6db6dcb6d96,0x1cb6cd86db,0x1b6db,0xdb6c,0xccdb6db2cb2cb2cb9,0x36db9397b9659659659659659659659,0] n191 8 118 36 8 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn1918_154 : block n191 8 154 21=true :=
  @streamBlock #[0x7b,0xdb6cb,0x3dfb64,0x1b96dffb,0x372cb9,0x36db6db,0x6db2fd9659659659659659,0] n191 8 154 21 8 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn1918_175 : block n191 8 175 36=true :=
  @streamBlock #[0x3db6db6,0x787fb35b6e5b7d6db6db6db7e0f,0xdb6dc5b659b66db6e590,0x36d9736b66db64db5,0x7b6cb2cb2dd,0x1ffedcd,0x1f3f265cb6fe6b2e5b67e5b37d6d,0x3973f232fe5c86dcb2e7e4db6fdecdfb5fb2e6b2f6d9a3972f4ddb2e5ccb9,0] n191 8 175 36 9 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn1918_211 : block n191 8 211 12=true :=
  @streamBlock #[0,0xf6,0x36dba,0x1b6c9b,0x6,0x1ba,0x36d9f,0xcb72e5c996cb9735b27cd7ecb2,0] n191 8 211 12 9 (by decide +kernel) (by decide +kernel)
theorem alln1918 : block n191 8 0 223=true := (@block_merge n191 8 0 211 12 (@block_merge n191 8 0 175 36 (@block_merge n191 8 0 154 21 (@block_merge n191 8 0 118 36 (@block_merge n191 8 0 82 36 (@block_merge n191 8 0 46 36 (@block_merge n191 8 0 10 36 sn1918_0 sn1918_10) sn1918_46) sn1918_82) sn1918_118) sn1918_154) sn1918_175) sn1918_211)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn1919_0 : block n191 9 0 5=true :=
  @streamBlock #[0x38e712bffff5dd3f7fffedb5dfffeb6b8ff0affffeeeeaeee9f7ffff,0x1e39217fffeffadffffb6abfffd6a850a9ff5fffff,0x1c01fe147f851fe1428ff,0x1c29fffeb6badaeb6badaeffff,0x14752affffdb6bdb6bdffff,0x28ea7ab2cfb35967d9,0x191cc862] n191 9 0 5 7 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn1919_5 : block n191 9 5 28=true :=
  @streamBlock #[0x1db661cf7dfefff6db6dfbffff6e19b6c1e7b771f971f9f9717cfcb6d86f9f9726db6e5bda0bdbf6d2e6dbf7b4e56db7adb6b6bdfffffff6d3adaf47bfdffff68a5b5c120fffffbe140a5a3dfffeffff7ad0ff28f6bdffffffef7b48ad3ba5e7b4c9fffffffffed75759967fffe,0x1368dbfbeff6db7fbb5effdbf6d368db6db498b898b8b8b6d98b8b8b4a426e2e2d98b6db69fff0bdf748fffff7a5dddddfe085dd3ea10a3eff5dddde89f7ffffa5b47a5fdffffe2da3ffcefff252139c0a52145fffffffdffffffffffffeffffef,0xb5b30db798fed6c7ffed6b66d8db61b6e47f26e7e378b7789b89cb6dc9b6dffef08ffff79ddc905ff5021448dfff3bb920241bfef1541ef05503d17978a7f9e7fffffbffcfff,0x606c3d8de6f37fff8c36db31ba3937cb393aace272db6eb161e9ff087f85b402822946f85b45b7fc2da05b453fcf3c3ffffcfff,0x5605ad5bffdffecf7ffffffd60dbbf2fe6bf93972e3f2e7e5aab97262f96dd1210dffffa5b6db6bd13e1a5b6da5b6fdfb7fffffffdefffffffffff,0xb685b4ebffdfff6bdffffff6d0d7e6fcbbf272e5c7e5cfcbbb92e5c98be5fcd77774d7ffffd77774db6d7aeeee9bf7edffffffffffffffffffffff,0x1da1b1c6cc59898b6e2e2cc4c5c6d79b75b7686db63c0dfbff6ffdfffbbb9219b6e78bac99655964cb2cbbbba4217a975932c9965932cb3efdffbf6cb3f59,0x75438efbfcff7ffd506232cf99] n191 9 5 28 8 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn1919_33 : block n191 9 33 14=true :=
  @streamBlock #[0x78f3fdb6ffffffdffedb6db6f937c989172db663f262cc7e4c4c5c5cb6db6db6db6db6db6db6db6dfffbc7f96dff7fff9feffff07bdce,0xf7bcdb7fb6dfb4a535214b6d290b6dd62d13c7f9c2a7894a5e5294a5d29486a7ffd104bfffffe9,0xde6db7b7bf6db7f1f8fc5b6fe378b31f8bbc5b6c78f3fd479fe17968a5e14fbca7fdfe8bc8122f2bfe,0x1bf31f9ffb66dd6ed76b7aebb75b74044f0a2abd5a7aaea7ff5082d,0xac0b1be2c887db6cd6b5676aedb600f3c3d12ab9472bdae0,0x2bad17c4ac6f105e51f6dd75ebbd3bba5b51feff50a4bd77a7774bbd,0x6f79fefff6edebd77a7774b51ef2ff52bd74bd77a7774d,0x99e41e3edb6f937c88b96db31f931663f2317172db6793240a44d79bfdfe1ffeffffffe935b6db6db6db,0x7abdbfccfb9] n191 9 33 14 9 (by decide +kernel) (by decide +kernel)
theorem alln1919 : block n191 9 0 47=true := (@block_merge n191 9 0 33 14 (@block_merge n191 9 0 5 28 sn1919_0 sn1919_5) sn1919_33)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn19110_0 : block n191 10 0 1=true :=
  @streamBlock #[0xdb6dffdbff6ff9fe7fbfffba5b,0x7f4a7efdf7bd29f,0x7ffffbf7deff,0x3f9ef0f,0xfe7bcf,0x3fdb6df,0xff6df,0x1b] n191 10 0 1 8 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn19110_1 : block n191 10 1 1=true :=
  @streamBlock #[0xf7fbf7def77f,0xfffbf7deff,0x3def0f,0xf7bcf,0xfb6df,0x3edf,0xff] n191 10 1 1 7 (by decide +kernel) (by decide +kernel)
theorem alln19110 : block n191 10 0 2=true := (@block_merge n191 10 0 1 1 sn19110_0 sn19110_1)
theorem tablesn191 : checkedTables n191 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block n191 0 0 0 = true)
  · exact (rfl : block n191 1 0 0 = true)
  · exact (rfl : block n191 2 0 0 = true)
  · exact (rfl : block n191 3 0 0 = true)
  · exact (rfl : block n191 4 0 0 = true)
  · exact (rfl : block n191 5 0 0 = true)
  · exact alln1916
  · exact alln1917
  · exact alln1918
  · exact alln1919
  · exact alln19110
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lown191 : Lower (vars 703) (graphGoal 703) 11 :=
  lower_forest9 (g:=n191) (m:=191) (hints:=544228129) (r:=2) (s:=3) (i:=0) (j:=1) validn455 geomn191 tablesn191 (by decide +kernel)
def mapsn191 : List (Nat × List Nat) := [(703,[]),(831,[135,50,65]),(891,[130,114,98,81])]
def knownn191 := extendKnown knownn455 11 mapsn191
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validn191 : Known knownn191 := extendKnown_ok validn455 lown191 (by decide +kernel)
def n351d6 (i : Nat) : Nat := 0x28a7a68a889dd3187b68a9960c71
def n351l6 : Packing := (2,4,4,0,0,3,0,n351d6)
def n351d7 (i : Nat) : Nat := 0x20820c90800000208010400820000000a100108328728728440408400003107107107107287287287284001010210010800000108008440400000000000000000420439429439432949b244871f465134350ac2105c0cfd3eaf4bc8ec3a6e7392e237ed9b5cd133ac8b0abcadab0ab8abaa4a6a829aa528ea22829f2769d0719ae6598c5d16a58156531344a9123e8f0398dc348c82f8b42a8a02588c20878180480c0180067ea22774c63fd32c10e71fd9221d6397ecb510a9c7f6488754e3fb2643ac51fd9321d52cbe43aa6a967b21d624ca3fd32c18e39ec9260c718fecc26438e7760d321c66fb2b442c31fd9321d618fec910eb0c7f64c875467db25442631fd9221d31aeec90e698e7b21c824c7b98e6412631fd9321d218fecc0e690d7d64473487ba8e698a433799520d649f4c9106b24fc644835925f32d442a71f89760633bccca10f19d7625d818cedb32c40c6779994206339dcca10eb14de6548358a7732841ac53f19120d629ec49b0ca14be6588350a6f32a41a853f19120d42f952ac89117d29563388a6f32b442c31f89761941c7c43ccca0c7e25d855072f10f2aa839d8878cd41cf443c44a0cfa64a884c63f12ec22633e898889318fc4bb0890cde65483846be12ea0c23eb26691211f992ac8908ddc65483847ba4ef19c23ed2668ce11fa92ac6708fe491233847dc4cd11423f625588a11fd12244508ff08ce2284637b2843c6759d9421e338deca10eb14de6548358277329442613799520d20
def n351l7 : Packing := (75,3,4,0,0,10,0,n351d7)
def hashn351l7 (i : Nat) : Nat := 0x63d
def n351d8 (i : Nat) : Nat := (if i<1 then 0xfbe99873bf9851cfde95473bf9821cefe60473bfa8858efe21d63ef96458efea2153bf88754fde55153bfa8850efe61943efa6650efe61543f7a5550fee59143dfa778cefe61a33bf9858cfde95633bf9848cff61ce33fd9638cff654e33fd9438cefe60a33bf9818cff6a2233fd8878cff661a33fd9858cff661233fd9648cff655233fd9828cff660633fd8818cefea2162bf88758afe20d62ef96358bf68cd62bfa8854afe21d52fba4454afe20d52f795354bf68cd52bfa8850afe61942efa6650afe61542f7a5550afe20d42fb94350bf68cd42fe95250afea2132bf8874cafe61932bf9854cbde95532bf9844cbf68cd32fe9624cbfa50932fe96488bfa55222fe87388bfa58e22fe95388bfa50e22fea3388afe61871efa661c6fe61471f7a551c6fe60c71fda331c6fe60871fea221c6fea2161bf887587be59161fba44586fe20d61fda33587be58961fea22586fea2151bf887547ee91151bf883547f68cd51f7952547fa88951bfa885077e21d41bf986507be99941bf985507de95541fb964507ee55141bf883507f68cd41fb942507fa88941bfa884c6fe21d31dfa774c6fe61931efa664c6fe61531f7a554c6fe61131fba444c7f61cd31fd9534c7f68cd31fe8824c7f64c931fea224c7fc58531ff1414c6fe61831efa660c6fe61431f7a550c6fe61031fba440c7f68cc31bf9820c7fa88831ff1310c6fea2121bf887486fe61921efa66486fe61521f7a55486fe61121fba44486fe60d21bf883487f68cd21fe952487fc4c521efa66847de95611fba44846fe20e11fda33847fa88a11ff161847fc54611ff141847fc4c611ff121847fc21e11ff164847fc55211ff083847fc1ce11ff163847fc54e11ff143847fc8ce11ff162847fc54a11ff142847fc4ca119fe881ce7f61873cfe661ce7f61473d7e551ce7f608739fd811ce7f21d639fc8754e7f21e33ddc738cefe60233ddc878cfb799a33f5e558cff6602339fc8758a7f21d529fc874cbbb99a22f6e5588b7b1ce22fce3388a7f61871cfe661c67f61471d7e551c67f60c71dde331c67f60871dee221c67f21d619fc875467f21d31ddc734c6fe600319fc874867f21e11df487847bd99a11f76558477d1ce11fd633847f988a11bf883583f68cd60fea22583be58560ff211582fe20d50f7953543f68cd50fea22543de54550ff211542fea2130bf9864c3be99930bf9854c3de95530df8734c3f68cd30fea224c37e1c530fd9314c3fc84530bf986483be99920bf985483de95520bf983482fe20d20fda33483fa58920fe921483fc84520bfa88442fe61910efa66442fe61510f7a55442fe60d10bf883443f68cd10bf982443fa88910ff211443ce95644f5a558cfba99a22f6a5588bea91222fca3388a7e21d41df277847bc99a11f7255847ec91211fd233847f888a11 else (if i<2 then 0xc118914419424ca29432865082508250ca1a42a849145485508828840b2103210084880089108204408040800c8402044244c840c840003210321044154248b10e208220aa100b1082244094328650ca194310a288328650c41542c859081508190aa1032100190800c8400040004200010521a420122a43486908448a90d21a420a42024010041442059081908190b219420482002a16525461322882132288212a2882a8590c414829040c8550b21032102a10012080110620b2104410441044188200891441000038a2001908009040002a1542003210000054201461c630a38c708e40870903ca320794120948231290460882042084108000a550474aa30c7215048000e101240e3202310220238444a41823ca30c80aa40875461903aa09081d518611c8543208a921915080028400942004a104a11491001284128650ca115914a110328650a028a50ca1942002510250ca104a19420942c841284014a2942048200321642c8590c4188220a2552646c8590aa15651241e29e18e07df6debddadc9db8da7da2d91d7ad75d6ad59d48d31d26d15cfecedcdccd1cc0cb5c98c7bc70c5fc54c49c38c27c16bf9be8bd7bccbbbbb0ba5b94b89b7eb73b6eb63b5eb53b48b3db32b21b16b0bafaaefae4adfad4acfabeaa1a96a8ba86a7ba76a71a66a61a56a45a3aa35a2aa25a20a1ba10a0ba009fb9f09e59ce9c39be9b39a89a399298197c97196695b95094593492991e9139088fd8f28e78e28d78d28c78bc8b78ac8a78a289789288d88287d87286d85c85784c84783c83182081580a7ff7ee7e37d87cd7c87bd7b87a77a279178677b77676b76675b75074574073573072b7207096f86ed6dc6d16c06b56aa69f69468967e67966e66365865364864363863362e62361e61960e6035f85f35e85e35d85d35c85bd5b85a759c59759258d57c57757256756255d55254d54854353852d52852351851350e5095044f94f44dd4c64bb4aa49f48846b45443d42c42141640b4064013fc3e53ce3b13ac3a739c39738037536435933c33131a30f2fe2e72ca2b32a828b26e26325e25924e24924423923422f22421f2142031fe1f91ee1e91de1d31c81b71ac1a119618b17a16f16415915414313e13312812311810d1080fd0f20ed0e20dd0cc0c10bc0b10ac0a709c09108607b07006505403d03202701c00b000dfd821ceffa2163bfe8854effa2162efd6358affa2152dfc7354bdf54d52bfe884cb7f21d32bfd864caff61532dfc734cbfb58932dfd631c77f8cc71dfd621c77f4c871bfe88587bf58961bfe885477f1cd51f7d52546ffa2131dfc874c6ff61931bfd854c77f1cd31fdd534c7fb20931fdd324c7fd58531bfd860c6ff61431bfd86486ff61521bfd834877f1cd21fed52487fd4c521bfa88592fe20d64bfa88552fe20d54bf9861c else 0x8a204510228a209028812041122045100114409228c0484704438220421c6084114409290c1144402204208a254208448a4042159244105916a10423b2214110a088188914830a204510))
def n351l8 : Packing := (318,2,4,0,0,12,0,n351d8)
def hashn351l8 (i : Nat) : Nat := 0x1622421408400163fe00800000000080c306f93fe32ac4906683ee3c60f28f8c6a027401210010e81df1ed0b802bc04c1430ccc8a21ca18a09b02802ff23502406d02ac1bb023121213b0d409542501100398a700c0000001911c0b80e32488c145ac2bf06800082c63a00838e3018843c0788b2017800000480f8688852055107472a48023e081c2fa24325488c001a3b0185600d6b83880586c200cbf1140100ae4
def n351d9 (i : Nat) : Nat := 0xb926a5400f24d4c0966a42a8870093539002326a600b35210e8926a6248c9a9402966a52033519459a8c8492401a98402a482015241012520805490402a480124a404b35200a24900512480488a4024a2200a21152311523124a3024552140249443926a0249351c9351813209ca6966a3c8aa3cc90501640cd4820152410125208092900911482480a4008a924aa91caa91cb2519659a92b910cb2066a59b12d64bc6f8990ce083f27a8ed9ceb7a6c2d2197b165fab9165ab2532a0133a584888c10e2033e8780e39b333e5f0b415426c474820eb1a42e4500870e617c2583203c003feb1ffd53ffc67ff58bfea97fd32ffac3ff547fe98ffc31ffa43ff847fcb27f954ff0e7fe58ffca9ff943ff467fe58bfca97f942ff265fe1c7fcb0ff951ff283fe4c7fc18ff921ff423bf99bbf2adfc73fbc67fb88afe38ff611ff2c1fe543fc987f920ff2217e9df7d3377a55f7489f68cff5117f211
def n351l9 : Packing := (50,1,4,0,0,11,0,n351d9)
def hashn351l9 (i : Nat) : Nat := 0x3a819127a184c478015e2516310f02202bb20840d800048adc26fa361076a899c0a04217410a8731038c172467805b51f60000000382d22740001464e859924c82cb102c930d27a000285e984821c00042830590021d522c54968000119da144000604dc230000043d912fc0bc82e747218da51cca0c7486184761a2424b04e282ad1ebe348d3c803f20c861ba029e00a30b4840ac1ae0c6a15041fa887004370a82371448b04111de84710998877a23d0030031d802022ba2c3c5768fe307740458272826a01e635c89ce81741e80002879a88c9147801f45b890601446aee4074116b195826d095393bc08b63f00003006000064500005884606083f5c38686ca129a0b88550000115e20d38340000f05e20a50480919a19b611b42500b621ce3a1683b78271100835000070235104a0f00618000d26bc3c0c01f025203ca090000692bb26360dfc43d20c80f9c0e04682818721084048317812c088a46d04ed11f000082e2855b869e114000280fa8e8f246e1cb884e110a405e41fc0b10eed08002f3c9e092ce0d58490094d8b4620a622255a0000f0a5238c000704c00004315881a8394159b9ef0539055f0bb83dac44d91ac1b7806b03fd8bb526583e9876509661e58b8d89c68be2085815d443111d60ebe0f9019b0ffb198a011485789e9103a3c608ba0a6f0cb20f4805f90b90328198090700580f38355471688b60e8c27fc1d00000245643702f9136d25c430b00eb0a5c1404305465980851a681af46b2801f026c31d872900db09fa293046a020e1ba0000824a05671d3e28643c490f2058a26b47c38670000a37e06cb0f70000c262447512740e3a449890f8581107a494000009780fb80c803d48b340360002854986f0001e2d7875986d21c20001c110000722680a0000401421f2000000048c0022284d2c5f8000b013c32305d0000e0002378c25f09519001506130e07084e080002050006001102170400071f02000009040021640003100f001817170007030100212d0d1e17004d0200002b09080806110a18060a18000a0e000092012216370d3b070525022a1a7a1619163b421b000080a2
def n351d10 (i : Nat) : Nat := 0x295194a8e20feff
def n351l10 : Packing := (2,0,4,0,0,5,0,n351d10)
def hashn351l10 (i : Nat) : Nat := 0x18b05359e534a764e6ab75043d46330a1c20c0009b22ee97420b1232c4ed0b82c2a24a80781f12000d3f10210c8a5572045381dd700060b42ad7800e3122d1180015b0524b0005494180000001a07c004116000900041900001005602104
def n351samples : Array (Bits × Bits) := #[(0xacf97f5bd7d0f448597a4fc57cd95af66d674c7eed7447690ae3ae98c13810fc2be529fe29b5af8071d5e3f567e74c5a3e975fedaad5317ebb722e28530be66a91b40d3bf9d4cbe802d41adebf624002054679592100e0c0cb2639478d511e26,0x8604098810a6c600c00004690181c62580451cf1b104e3028cac459441ae108f420148ecd74283548684ba4420c8020009af90a2285700204c402104e215c03c800472218920d803cc0512cab4e1d42a597062dd8100c0008b24390309411c26),(0x3763f17853af88f36d967877719f6eadc0b8b3823f92b2ddd3fc9fcaac3ebbecf0dc3abb8b3e57a667cfbd9ef55fe7bab10dfcaffdff6e875cf2b7aaeb305fab2c5db5de35798e5f5295673c2ad9c005f8c9895ca270233624bf90f48078b598,0x288200402e1800840f90880004000040110000000029002160001202041004100080a01000204c0359600003401204820400210884800a9113380421042203000440001a14dd20c0031048200010094480021d000ab0263400980064a638a098),(0xa3ec33ac327a16e6a6ffc92bedc0d14be2ac6a8fd09e8a2f814e48527f4af7953f9a66bf6ed673686dcf17076b7b21d357e1b390d4590d63b77fdfcfbfbaadc38483b4fa87369ee7e9f34a6ba69f2004018186cdc74f09a6892fa511718c82a4,0x5319063640803d32a02a13e8200013848436188ea2800e4205d140b08008d061800048088d4480988499bcb80d2cd2201283ce6000191562400712d6315c10d502b05661e3229e2550ed901a8e8eb2b16b95a24de44f09820d27a51111835221),(0x6b17e5a96fc5f69de7abf138c7fbfd60bb47ca050e6b38ef970b78961a756ca5a7b0dd46e46ba159aac9dced785b1d6d5e62616dbdc1e0f6e23ddadf07ebb65ffe0b66e40a6b90c19d38c2a38974a8f8033006935dab502190d0281572364d5e,0x4c631811550428d0041000304418040024124304111c190c2280d4a2000020a170180e1521154042302010000020004210000041740000918204101c001622044408104000c4052880041a000414508102050901880602090400aa06834855e),(0x98f77d9184d0122dd2f797d1afaa8f9e4f2fd4dfdec6df51ed51e4e8cd51f6960aebaf5a60c4ecf61e52df66faecfb045097476ca2a6d2aa48e64b7ad1d0d382ab867ba77cd46b08fd3bdbbc2b6ea80206b6790002b0d0db7981e4061c8042e8,0x9214606a0002920333cb2947a121902408a820400280825010222209c10c460086e0410082c008b485040b05734f9e084502a118000f0d0038006020d2204c31b0b0082749321a402f0001409062ad5a6860d00627215db6081c40c14804281),(0x0,0x0),(0x772f4f466d17ad89604fef491217f78630d597e530fe75f2683e37b12dba7852cfb27cf913bab717d739b87dd2f6bf848008c4fb49f203ea19ed74efe06dade19cfaa0688dc1e9b8b44bfd7b5db59703f8090071101c4e592e02efa901c52355,0x4014b1be5066c23290050116a2950a124051a6016190c18c8629e0cc00a2c16c023b0ca361801204008288488ccd08540b041835116a010a4041218680d420f428282760c92218265087201e1265441a383960f0900848432c02ea8901c44345),(0x0,0x0),(0xd0eea67f7caee1da9a8252196d7370efb9c693e0a535462bb200f06f9497369b4dbf41b5949702f5e0a547ce6c15df270dfbd6753b0fc138f16802971f3d989ff82d9332989c253828c3974c7e28b7f8050008221c348e8802795f0883a308a3,0x92204c40028130402da2f4a049084188050e50cc88022a4210c600005e1438006000631c0c222921c0403627732015808491c6420804f2d0811894702c080c0b9296488b208105800320144169883ae5c7060e062476868c023d1500820318a0)]
def n351columns : List ColumnInfo := [(2,0,861,0,7),(2,1,332,16,5),(4,0,859,0,8),(7,0,344,0,4),(9,16,326,0,4),(17,0,334,0,7),(70,0,793,0,4),(72,256,535,0,4),(258,64,541,0,4),(320,0,543,0,7),(324,0,539,0,4),(328,0,535,0,4)]
def n351autos : Array (List Nat) := #[[],[64,49,134],[96,132],[128,49,100]]
def n351levels : Nat → Packing
  | 6 => n351l6
  | 7 => n351l7
  | 8 => n351l8
  | 9 => n351l9
  | 10 => n351l10
  | _ => emptyPacking
def n351index : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 2 4 0 6 1 1 (hashn351l7)
  | 8 => lookupWord 28 89 5 13 7 2 (hashn351l8)
  | 9 => lookupWord 94 366 8 15 9 2 (hashn351l9)
  | 10 => lookupWord 25 59 4 11 6 1 (hashn351l10)
  | _ => fun _ => none
def n351 : Forest := (863,10,fun j => n351samples[j]?.getD (0,0),n351columns,n351autos,n351levels,n351index)
set_option maxHeartbeats 0 in
theorem geomn351 : graphValid n351 (boundsBefore knownn191) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn3516_0 : block n351 6 0 2=true :=
  @streamBlock #[0,0,0,0,0,0,0] n351 6 0 2 7 (by decide +kernel) (by decide +kernel)
theorem alln3516 : block n351 6 0 2=true := sn3516_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn3517_0 : block n351 7 0 36=true :=
  @streamBlock #[0,0,0,0,0,0xcfb2c8,0] n351 7 0 36 7 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn3517_36 : block n351 7 36 13=true :=
  @streamBlock #[0,0,0,0,0,0x19659659,0] n351 7 36 13 7 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn3517_49 : block n351 7 49 26=true :=
  @streamBlock #[0,0x7b,0x7b6cb2d96cb65b,0x1b6db,0,0,0x1b2,0] n351 7 49 26 8 (by decide +kernel) (by decide +kernel)
theorem alln3517 : block n351 7 0 75=true := (@block_merge n351 7 0 49 26 (@block_merge n351 7 0 36 13 sn3517_0 sn3517_36) sn3517_49)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn3518_0 : block n351 8 0 13=true :=
  @streamBlock #[0x7ffffffdfffff,0xfffffffffffff,0xfffffff7fffff,0xff0fff,0x659659659f32cbd9,0x65965964f659659659,0x2832cfb872] n351 8 0 13 7 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn3518_13 : block n351 8 13 36=true :=
  @streamBlock #[0x1cb6db6db,0x1b6e5b6db,0x36db6d8,0x3ce46d8,0x3db3,0x19b0,0x1b01903219,0x5] n351 8 13 36 8 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn3518_49 : block n351 8 49 36=true :=
  @streamBlock #[0x50b6836ed1b6d85,0x500cdb6dd29e,0xaa7bf7f8db7ec5bf2c1f2dfde5be,0x3fe8fffef985607165f,0x2da2db7e6bfc2d01cadb,0x3be4e871f918371039f9619,0x1d771671f97cfcb89b0d419cb672c9964,0x3d9320] n351 8 49 36 8 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn3518_85 : block n351 8 85 36=true :=
  @streamBlock #[0x300db9a36d96db6c0,0xf61b6e7e5f2cadb6db95ef,0x1fff9b73f358adb6dd0,0x316d7f9419b6db,0x2bbbffe5cd036cce7,0x3f971b4d96c745f6,0x1abda65b6cdf22b72c99,0xf0] n351 8 85 36 8 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn3518_121 : block n351 8 121 36=true :=
  @streamBlock #[0x1b6db6db6db6db,0x396db6d965b6db,0xdb6db,0x1b6,0x33,0xd9965964e59,0x3f379ec8cb2659659659659,0] n351 8 121 36 8 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn3518_157 : block n351 8 157 36=true :=
  @streamBlock #[0x65b6db6db6db6db6db75,0xf6e5cdb5cab2cd,0x36db6db6db7,0x1b036db6,0x799bb9b3,0x3676ffffecb2e59659,0xdb2ce5cb2ffc32cb2cb2cb35965ef659,0] n351 8 157 36 8 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn3518_193 : block n351 8 193 36=true :=
  @streamBlock #[0x1edb,0xcb6cdb6db2db6db0,0x6fcdb6db6c,0x2b6db6db,0x3cdb63,0x3db66db65932,0x1b965b90321cb265932cb9,0] n351 8 193 36 8 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn3518_229 : block n351 8 229 36=true :=
  @streamBlock #[0x1fb671,0x3e5b7cb,0x3fdb6db6db6,0x3fdb6db6465b,0x3fdb665b393,0xf6ccfce6d659,0xdb6e4cb3edb6cc8cb2c2b2659,0] n351 8 229 36 8 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn3518_265 : block n351 8 265 13=true :=
  @streamBlock #[0x7b,0x7b,0x6db,0x72,0xf3,0x6db9,0x6c8032,0] n351 8 265 13 8 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn3518_278 : block n351 8 278 36=true :=
  @streamBlock #[0,0x7b6db6db6db6f,0x3db6fe7e5b6db73ecb767df,0x36db6db36dfb6db,0,0xcf9b96dcb758,0x6e5bf9659cb2dd65ffe,0xcb2cb6596e5cb3ecb2e596cb96e5cb2cb3eae5cb96e7e5b2cb3f2cb93932e5b8b8b36438d72cb2,0] n351 8 278 36 9 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn3518_314 : block n351 8 314 4=true :=
  @streamBlock #[0,0,0x3,0x3,0,0,0xf,0xd96596e5cb9,0] n351 8 314 4 9 (by decide +kernel) (by decide +kernel)
theorem alln3518 : block n351 8 0 318=true := (@block_merge n351 8 0 314 4 (@block_merge n351 8 0 278 36 (@block_merge n351 8 0 265 13 (@block_merge n351 8 0 229 36 (@block_merge n351 8 0 193 36 (@block_merge n351 8 0 157 36 (@block_merge n351 8 0 121 36 (@block_merge n351 8 0 85 36 (@block_merge n351 8 0 49 36 (@block_merge n351 8 0 13 36 sn3518_0 sn3518_13) sn3518_49) sn3518_85) sn3518_121) sn3518_157) sn3518_193) sn3518_229) sn3518_265) sn3518_278) sn3518_314)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn3519_0 : block n351 9 0 7=true :=
  @streamBlock #[0xa3cf4792b473fdfe91fffe2db6ffffffdb6db7ffffffd3ffe73ffffffbbbbbfa53ffffe9fffffff,0x28f3d0ef5a38ee7ff1fffe2db6ffffffdb6db5ffffffddddce77777ff7ffffff,0x28f3d0168e7f8e1fffe2aaffffffdb6abfffcefffffff,0x1479e8aab472d5b45b68b6db6db6dffffff,0x1e70aa0705b45b68ffff,0x7bd68e32cbd9f,0x28f3d0e231] n351 9 0 7 7 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn3519_7 : block n351 9 7 31=true :=
  @streamBlock #[0x1b76ffd3fffffffffffb6db6daffffb6db6db6c0fe7e7e7e7e5c5c5c5c5c5c5b6db6dbf9f9f9716db6daab6db1b6d8a36db6db7f55ff6ffffffa802bcfffff502857ffff9e7ffa8017fffffffffffffdebe07a4ffffff7ff802d17ffffffffffeffffbdb66ebfffff,0xedfffffffb6dffffffb7bfff7eeb6dbf6dc5c5c5c5c7e5db6efcfcfcb934fc5b8b8b8b716db72dd003a9fffe9be7fffd03feff87bfdfff43dfffeeaae77ffffffdb5fffffeffffff7fffdf,0x79b7fedb6fffdffffb7effff7fedd36db6ffdb6dfffbbffedffa5feffdb6dbbe00512eff777ffff77ffd4a8afffff557fbdff52094ffffffbffffffffffffffffffffffff,0x66dbfdfffbf7fbfff3fa0d9b6d9b3972df3f2dc9cb9639ad41b6dafd015cff0577fffda115ef28bf6bfdffef7fbffffffcf50,0x7e7fe7ffe7fffe53fff1b66cdc9b9a7f3f34dcfcbe7e4373f3f2db36a005057b545514f3fcfff3ffffc7fdf5fff,0x14dedfedffedfffeff77ffe9b36d9cb39adf3f359cfcbe7e4c4eb9f9f96cdbaf40572daf55cf3fcfff3ffffedfffff5fff,0x14d82d6e5c9f3f272dcb91cb97fb6db6ebedfbebf6daffdffef7fef7f9881f69964659326591966d7a169965ecb264cb2f65965bf6fdd0,0x5b59a7ffffff7ffff7fffdeedf669965cfb9f] n351 9 7 31 8 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn3519_38 : block n351 9 38 12=true :=
  @streamBlock #[0xfffffffffff700028169b6db6db6db6db6db6de7fbfe9ffe,0x3ff7ffb6db6db6cc4c4c5c4c5c5b6db6db0007a3fefe97095effdfaffffff7,0x3fcdbfff3adbf6ee96dba5cc2db7160003ba5dddddcae9bfff7ffe9fe9,0x6dbff7fedfd6db6dbf8fc5fc4c5b7c5b6c00292907fc3fe1fbff7edff,0x2d000000002d0,0x56afebfffadd75bd76ba38b7580016bdb6daef6db6d,0x3a77ddfffaeb6ebbb5da38bad8002d7b6db5ded,0x28169293cbfa5fca001ffffffffe9ff6db6db6db,0xff7fffffe3] n351 9 38 12 9 (by decide +kernel) (by decide +kernel)
theorem alln3519 : block n351 9 0 50=true := (@block_merge n351 9 0 38 12 (@block_merge n351 9 0 7 31 sn3519_0 sn3519_7) sn3519_38)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn35110_0 : block n351 10 0 1=true :=
  @streamBlock #[0x36db6f1e03c78f1b,0xffbf4fff7ff,0x7fbf4f77f,0xffbf4ff,0,0xb6df,0x2df,0x1b] n351 10 0 1 8 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn35110_1 : block n351 10 1 1=true :=
  @streamBlock #[0x7fdfbefff7ff,0x3fdfbef77f,0x7fdfbeff,0x7bcf,0xb6df,0x2df,0xf] n351 10 1 1 7 (by decide +kernel) (by decide +kernel)
theorem alln35110 : block n351 10 0 2=true := (@block_merge n351 10 0 1 1 sn35110_0 sn35110_1)
theorem tablesn351 : checkedTables n351 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block n351 0 0 0 = true)
  · exact (rfl : block n351 1 0 0 = true)
  · exact (rfl : block n351 2 0 0 = true)
  · exact (rfl : block n351 3 0 0 = true)
  · exact (rfl : block n351 4 0 0 = true)
  · exact (rfl : block n351 5 0 0 = true)
  · exact alln3516
  · exact alln3517
  · exact alln3518
  · exact alln3519
  · exact alln35110
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lown351 : Lower (vars 863) (graphGoal 863) 11 :=
  lower_forest9 (g:=n351) (m:=351) (hints:=13019136801) (r:=2) (s:=3) (i:=0) (j:=1) validn191 geomn351 tablesn351 (by decide +kernel)
def mapsn351 : List (Nat × List Nat) := [(863,[]),(879,[84,131,98]),(943,[98,118,81,130,50,65]),(957,[118,130,81])]
def knownn351 := extendKnown knownn191 11 mapsn351
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validn351 : Known knownn351 := extendKnown_ok validn191 lown351 (by decide +kernel)
def n487d6 (i : Nat) : Nat := 0x87eaa89760d10
def n487l6 : Packing := (1,4,4,0,0,0,0,n487d6)
def n487d7 (i : Nat) : Nat := 0x1000000040a2005084080008a1005084080000a10000000000081081081004080000810000000000c01c01c01c01c01003057dbc5cedd69ab5468b399a4be551e8cc3602fc7bbc9cce16e35da4cd6430d7cb2532692a89421fcf46e34990be5a2a94096461d0b8441605014015fa9921d31cfd4c90e98e7ea22774c63fb2243ac51fd9321d428fec890ea165f615651c63fd32c18e31fd9560c718fe4bd10a8cfb64a885463fb2643aa31fc9761951abe4bacaa8d5f25d545463fb3039aa35f5911cd518fe4bd1098cfe642884c63fd3243a631fd9521d31afaca8e298d7d25d514c7ba8e6a8a631fd9321d218fe4bb0c90c7f25d844863f92ec1a435ec97509219bcca902b14de6548150a7b32640a859d9831cc719f4c9510a8c7ea64874c73d10f11263dd0731c5318fc4bb0690df824542486be12e98c23e726695611bf0c910708f749de33847dc4cd11423fa24488a11fe119c4508cfc245844825f32c40a4137995205209dcca102904f664c814837c10290a411f89760d10
def n487l7 : Packing := (53,3,4,0,0,9,0,n487d7)
def hashn487l7 (i : Nat) : Nat := 0x3c
def n487d8 (i : Nat) : Nat := 0x10010800840c5004008648a324511210e510014020055080188900400409442062242386294328650ca140248128d50820081508250ca115914a124511228a5080140206505460402a855080128650b2194328650ca11c910600a390708072451aa10015080006420001954400000002a15421ca50c794a18001c038840c51e010a38410c712028e00621040863a021011c311028638881010863ca090214904800500a010001000100410040904000a2803004100550820082008010c0104ac899944065512a156512a1c878cb10e16c177d2f1dd8b8f6f2d8da6b3762abcd6eabb532a0d30a4b46a87d049f338a6bcd298f30a5bcb294f27245c808df17a29c4887b0e210c1c823019fdbf67e2f99edbd078aee9d7ba4726dd9b5b6669ed119fb3a65eca992b2062ac4185b065eabc175ae65c2b716bacc582aa949a8e5129b124a3e4367f8f99d6366658c596e2a25189d9302564808d916222418808f61e2398708d018a2e85a8aa13e2684788a0fe1e8378640be1381e83804e07005800bfe8858affa2142dfd651c77f60c71bfe88546ff61951f7d65547df55151dfc73546ffa2131dfc874c77f1c531ff5514c6ff61031bfd86486ff61121bfd834877f1cd21fed424877f1ce11bfa8858afe21d62bf88158afea2142bf88750afe20542bf9851c7de95471bf9831c77e1cc71bf9821c7fa88871bfa88546fe21d51bf986547be99951f7965547de55151fba44546fea2131bf8874c77e21d31dfa774c7fa88931ff0714c7fc54531bf9820c7fa88831fd9310c6fea2121bf887486fe61921efa66486fe61121fba44486fe60d21fe9424877e9de11bf985847de95611bf983846fe60a11fea22847fc1c611ff151847fc4c611ff031847fc48611ff288847fc21e11ff185847fc59611ff183847fc20e11ff073847fc54e11ff233847fc60a11ff162847fc50a11ff1328467f21d629fc8750bbb99a22fae4488a7fa20719fd851c75f954719fd831c67f60871dee221c67f21d519fc874c77d1c531bf9800c67f21d219fc878477d1c611bf9808477d21e11f76558477d1ce11fd633847f988a11ff180846fe61920efa66482fe61120fba444837e1cd20fda33483fa4c920bf881483fa48520ff211482fea2110bf985443de95510bf983443f68cd10bf982443fa88910df871443fc4c510ff211443ba99a22faa4488a7e21d31df277847dc95611fd233847f888a11
def n487l8 : Packing := (132,2,4,0,0,11,0,n487d8)
def hashn487l8 (i : Nat) : Nat := 0x11b8e772122e932617e4b00042dd22e20527612305b0ad31100807df1b3320670b416d2f02a11d000000830cd1d26fa740cd01f13749a02f51e1a3a6f28223000a25214cc7629719000303f47715d1cc1f71ed0903460fc6600840432409190d04e658cc902b000000f8c156b2ce1088d08760e811c180289312100000450b3101022100d02023130e
def n487d9 (i : Nat) : Nat := 0x142184854c10a104854c0e2264b028ab981100364413660509055cc02500925200492904928080124a414125200420092520a19a932580c59a9c04366b0189202904928082024a4864a3043352475093e8edb70cfb02b429e9b23a821ea6e186579183c0be2305a0c801ff58bfea17fd51ffa63ff0c7fe90ffe11ff2c5fe50bfc38ff951ff263fe0c7fc90ffa11fdc457f1c7fb08ff920ff2217e9dff5117f211
def n487l9 : Packing := (23,1,4,0,0,10,0,n487d9)
def hashn487l9 (i : Nat) : Nat := 0x18420003d29b04d85ba9854468047c54d16545e5200c2ea009917751b01b10f642291a4168c13574c5d59c06e07f911715d00a712d04cd1a80006515c4189de5560003007b1b8851c1f40000002472f40ac61814c47b91d645f0002455f0a025ef87cc7020e3805720442981ce755c501c1d0002c213821d64adc80630126d5d81de0826101573111165fa90a80f48520456402c04f1b400030afc209855e0fe10ec71b933015805875ff9cd425504a15eb8b246461e800020ea0185555c4a307a74f80a8000d87a92d0000658306800c852ee5791f0a542d4080949f383c350f6559dcec30c5c792a80035779ddc000d0ef8233168b15313ac67e9fbc7e60c453870fbc3f6d6306f495ba8160d4e68ac64d1f20bdc0e7d50a33700ea380002019000317c39c306858e776041fc00040cd237f85ae0e01e0000b0e502c7188065305310e659400054f6c34000267d643f047d563c27a471810f20cc08e1ad77d70d914d489bc17c80953325a494cb122536e550150b80ed35c070d7520b4a4891dab3551b150be02e00d342a52cc9c98526141001e18184fb0900006dd4e0c4525879f1624374175032009814871d0c5c415ba3c1199f160e001513050f074e0a000127045f010203150b010e044b5502050f6409402003060a0229040011000402890100a70900290c13030045020001011c02070d25110b0000
def n487d10 (i : Nat) : Nat := 0x951ca80e20feff
def n487l10 : Packing := (2,0,4,0,0,5,0,n487d10)
def hashn487l10 (i : Nat) : Nat := 0x3544c9123e098fa8da23ca9f10aae004b3c48937b2264a9b81b1cc0800e12534c346150a10e1a00c0012bdd8cc500021ce73210013d1b3bb6848c2f4a10a6d2609a850300001113d9002584696000426439a8d0dde802c02e0db42900095
def n487samples : Array (Bits × Bits) := #[(0x2c3957d85750f76ccbfa5b15d1f150ee626949462374cc78c2f3eac983f99f7c6bec2afe69f1e3ea69e7a4f7cd674c5a7e045de988f5e37e73f32d0c029ff448b094573c3ac29bba4bf49ccb9d2d000002088fe13a72f910b686520ce02abb15,0x8a00b806208004204311846aa1044435800038c0d03c22ab0a848258451cd4e14010401fa4e291518c463200e415029404a3a886b93580a88700040626a6a0d8a0041103d493a4e306b632513580ba74eb5aa7679872e1103e801208600ab815),(0xbfb3c9ebd32f9af76ca674b7dd1f6cbd8f9af7b8f992b9dcdeb91bd24e76b348f0dcbbb9f97a4b2e3e9ffe9ed7d7a732e18eff2b1debde82d4f0b98a9ab05fb92f79bc51e76fcc5d5385e52c0959800a008f6036bb6a189942c3312219aac5aa,0x240405c01a0862002ca0188100018100114704340100c900a02815000000011a028120e05a00080612200023012014020108030800c01a4008180120c00141010200409821404000890088040851418b00840810210c18004011490001e0452a),(0x276c23af327a0fe6244fd17bf0ecdb43ab9a2bad5a9e8a2f012a0f135dc3f9d57f9267bf4dd667026cef7111636b2153d76bb0129449cd63ff7cf3efcfaebfd3a4f3e6f644329cf7e3f76e7ab656000003f0001fc44ba68d08efa43175d83aa5,0x539b823044901d96000a0368840410d40430188a8281064a41d18022800810018010c00aa4c4c4988519349c8a03c2301283c44044398522922612d131cc121024f01441420c8207104a70a0068c96245a3062ccce43a29f0866a02174182a84),(0x0,0x0),(0x0,0x0),(0x6b17f5aa6fc5e79df79be928c75bfd60f2658b270e6b38ef964f78873afc6ca1e7b0dc44c66bb15baba99ced78431ded4e6060ed7dd120e7a23fd6df27efa66fde2b646c4a6b86939f2846a7d8f280f5fa208fc04004d3e6f11648ef9214662a,0x44d200394536809f0040010104c08040021000310081001040010d0620a2020615008040121146002300014808c200002a041000060a010218606081404142004460e4c4090c40149800c1a00220050010004080420412c68147c807121406aa),(0x98f77d9384d0032dc2d797d1af2a8f9ecf2b95ffdec6df71ec51e4e9cdd1fe924aebaf5850c4ecf61e32df62f8f4fb044097466c62a652ba4ae7436ad1d0d382aba67b27fdd67b18ff0f5f382a6cff0a040f7020459140c5a60007826c0d2e51,0x4911823ee0268932021c0314b2961812c090820100a8000d0101a22480a2cc64087e0402208c0288081040dc8ed5e8700a443011802a011200c0228601e200d0292924409c10242410d6209012200e14385971e2c68140d7a6408483680f2211),(0x772f4f446d57bc89706fef491297f78630d1d6c530fe75d2693e37b02d3a71568fb27cfb23bab715d759b879d0eebf849000cdfbc9f203eb1bed7cefe06dade19cdaa0e80cc3fdaeb45b79ff4db38001f9d00029458066204ab88f99ab44915d,0x24758610406220a125b0966a110b02404ba6046110c9a4862a60d81c10c968022b0cb14920100740c28820552c19c485100a35114070d8410105028c1024c71a0a0322a0a119e04085001f494368d1a1c60d33318045204098079889439151),(0xd0eea67f7caee1da8a8252196d7370ef39c693e0a535462bb200f06f94973e9b4dbf41b5849702f5e0a547ca6c05df270df3d6757b0f4138f36802971f39988ff82dd332589e25382ac3174dee2ffffc0620900000f5054605a0234045b1d856,0x92204c40028130402da2f4a049084188050e50cc88022a4210c600005e1430006000631c0c22292380403623712015808499c6420804f2c1031994702c080c2b9296080b608311c001001445e88d70e9c7268e143870050008a0235005e0d844)]
def n487columns : List ColumnInfo := [(1,0,486,0,8),(7,0,480,0,4),(32,0,967,0,7),(96,256,647,0,4),(130,4,865,0,4),(132,0,867,0,7),(161,0,326,0,4),(258,64,677,0,4),(289,0,198,0,4),(320,0,679,0,7),(324,0,675,0,4)]
def n487autos : Array (List Nat) := #[[],[98,135],[81,114,134],[81,130,118]]
def n487levels : Nat → Packing
  | 6 => n487l6
  | 7 => n487l7
  | 8 => n487l8
  | 9 => n487l9
  | 10 => n487l10
  | _ => emptyPacking
def n487index : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 1 0 6 1 1 (hashn487l7)
  | 8 => lookupWord 37 79 4 12 6 2 (hashn487l8)
  | 9 => lookupWord 67 251 8 14 8 2 (hashn487l9)
  | 10 => lookupWord 16 61 5 11 5 2 (hashn487l10)
  | _ => fun _ => none
def n487 : Forest := (999,10,fun j => n487samples[j]?.getD (0,0),n487columns,n487autos,n487levels,n487index)
set_option maxHeartbeats 0 in
theorem geomn487 : graphValid n487 (boundsBefore knownn351) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn4876_0 : block n487 6 0 1=true :=
  @streamBlock #[0,0,0,0,0,0,0] n487 6 0 1 7 (by decide +kernel) (by decide +kernel)
theorem alln4876 : block n487 6 0 1=true := sn4876_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn4877_0 : block n487 7 0 24=true :=
  @streamBlock #[0,0,0,0,0,0xcb2cb20,0x19f] n487 7 0 24 7 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn4877_24 : block n487 7 24 29=true :=
  @streamBlock #[0x1fedb,0xdb,0x6596596,0x6db,0,0xdb,0x7b359,0] n487 7 24 29 8 (by decide +kernel) (by decide +kernel)
theorem alln4877 : block n487 7 0 53=true := (@block_merge n487 7 0 24 29 sn4877_0 sn4877_24)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn4878_0 : block n487 8 0 7=true :=
  @streamBlock #[0x3ffcff,0xfffffff,0xfbfe,0x5befff,0x32cfd67d9,0x19af659659,0x7afb272] n487 8 0 7 7 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn4878_7 : block n487 8 7 36=true :=
  @streamBlock #[0xa0fe5b6fdb63db6cf,0x6d9b6dfd,0x3391fb608db67,0xf7bdc8716,0xf971ff97b97c9cb,0x1ee35e397cb64,0x671f97136938b396e5e32659064,0xf0] n487 8 7 36 8 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn4878_43 : block n487 8 43 36=true :=
  @streamBlock #[0x1ddd7b6d8df9b6dbadb538,0x3fd8db036db6dedcbfff,0x2f802db7138b27fd,0x1fef6c7136db65987f,0x1dca71365b96397,0xb4fdb6c3ae7df8e59,0xc5c5bf929fd96db2cb67e59,0x19f] n487 8 43 36 8 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn4878_79 : block n487 8 79 33=true :=
  @streamBlock #[0x2b6db6db6db6dbbffc,0x1f3e6e5b306fc,0x17dbf6fdb7,0x776,0x7fb63,0x7b6edbfb2c99,0xadb9f6cb76fb972dd32cb2c9964cb2cb3ef659659,0xff] n487 8 79 33 8 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn4878_112 : block n487 8 112 20=true :=
  @streamBlock #[0x3dc99,0xf6cdb6db6dbf,0x1ecb6c3f,0x1b6cdb659,0x1cb72c,0x367b,0x37ffefd9,0xcb2cb65fd96dcb2cb972e6daffdcb2e7db3ffd9659,0] n487 8 112 20 9 (by decide +kernel) (by decide +kernel)
theorem alln4878 : block n487 8 0 132=true := (@block_merge n487 8 0 112 20 (@block_merge n487 8 0 79 33 (@block_merge n487 8 0 43 36 (@block_merge n487 8 0 7 36 sn4878_0 sn4878_7) sn4878_43) sn4878_79) sn4878_112)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn4879_0 : block n487 9 0 3=true :=
  @streamBlock #[0x3bdcaef7cff5529ffe9a7fbdfefff,0x79e777fbfd69e1feb5feff,0x3bdd6bbdb56adafa26dfff,0xafa53d0f14af,0x1e53bad5aff,0xa7afaef59f,0x1dee71] n487 9 0 3 7 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn4879_3 : block n487 9 3 13=true :=
  @streamBlock #[0xadbbfffedb6ddf6db6db1ffb6db6fdb6dd3bf6376ffb6dfdffffff52fbefd05ffffb54ff7ffffd4f9f5fffffe055fffffff6ebff,0x1b6fdfefdbf6db36db93266dcb66de83e94387dff07fff87bfdfffef,0x1ffffb7ffffecfe7e5c7e5bf9714b8b8b0fffffe127fa5ffffefffffff,0xfafffffffffcebf972e4e6fc7e7e5f8777f57787edfffffffffff,0xe7bff7fbcc72d901396e0eb5fc73dfefbfef,0x3bffffffffe6efcb9727353f3f2fc53badfffffffffff,0x7638b8b71772e2fedb7df7ffbff7f84f65932ecb2ef4cb267d967dfba,0x14cfffffbddf659f] n487 9 3 13 8 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn4879_16 : block n487 9 16 7=true :=
  @streamBlock #[0x7ffffff80057adb6db6db6dbdef7fd,0x1ffb6db6db085b6db6c052529f1fffff7fefd,0x377ccdd6dd73375803bd716d7bf6dfff,0x1fffb7e6ef1f898b6316008ffa6fffdff,0xaffffceb7a3b016bd74bd7f,0x3bbf4d3776e25803bd74d4df7,0x3bfe8f9baf47602d7ae97,0x18bdd8bca7c00ffffbfedb6db,0x1fffe3] n487 9 16 7 9 (by decide +kernel) (by decide +kernel)
theorem alln4879 : block n487 9 0 23=true := (@block_merge n487 9 0 16 7 (@block_merge n487 9 0 3 13 sn4879_0 sn4879_3) sn4879_16)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn48710_0 : block n487 10 0 1=true :=
  @streamBlock #[0x1b6db78f1e3c78f1b,0x3fdfefbfffdff,0x17edbf7edf,0x7fbfdf7ff,0x3bbfd7f,0x17edf,0x77f,0x1b] n487 10 0 1 8 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn48710_1 : block n487 10 1 1=true :=
  @streamBlock #[0x7ffbefbffeff,0x3bc7bcf,0x3ffdf7dff,0xf6df5f,0x3bcf,0x1edf,0x7f] n487 10 1 1 7 (by decide +kernel) (by decide +kernel)
theorem alln48710 : block n487 10 0 2=true := (@block_merge n487 10 0 1 1 sn48710_0 sn48710_1)
theorem tablesn487 : checkedTables n487 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block n487 0 0 0 = true)
  · exact (rfl : block n487 1 0 0 = true)
  · exact (rfl : block n487 2 0 0 = true)
  · exact (rfl : block n487 3 0 0 = true)
  · exact (rfl : block n487 4 0 0 = true)
  · exact (rfl : block n487 5 0 0 = true)
  · exact alln4876
  · exact alln4877
  · exact alln4878
  · exact alln4879
  · exact alln48710
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lown487 : Lower (vars 999) (graphGoal 999) 11 :=
  lower_forest9 (g:=n487) (m:=487) (hints:=22153266977) (r:=2) (s:=3) (i:=0) (j:=1) validn351 geomn487 tablesn487 (by decide +kernel)
def mapsn487 : List (Nat × List Nat) := [(999,[])]
def knownn487 := extendKnown knownn351 11 mapsn487
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validn487 : Known knownn487 := extendKnown_ok validn351 lown487 (by decide +kernel)
def gzd8 (i : Nat) : Nat := 0x147a8a0bcc9790d96095260551d2d8aecda6095260551dac836a446095260551d2f0aecda6093260531dad0954da6093260531
def gzl8 : Packing := (5,6,6,0,0,5,0,gzd8)
def gzd9 (i : Nat) : Nat := 0x614c442628c8840001d08000041e0820f040e860f040fc1e10000001d03e203e103e1041e08000000000009ac40746000000000000156505352b101f1cd4d0f5880f92157e9df769d5715c06edb66c5a16718c5f16c5454c51d424f522449023f4ed3a0e3378d9350cf328c527c9a2549022c862047c1dc7215c310028bfbaf5d952a930373add43258254981c3dedd3885cb04a8dced750c960981547e6c9b2c12a4c0aa373e4d96095260531b66ceb5553bc66c0dbaa75aaa9122260717e57665304c0aa3abb0ca9118260551bdb16eb04a9302a8f6d8aed8254981547d6c554c12a4c0aa37b60d96095260551fd9122304a9302a8fed08cd825498154747d1934434b112838f71c5706bb69531c5f95d994c130298daf836982549814c7d6c34ac12a4c0a637bc2dd6093260531dde1663049930298f6f0aed824c9814c7d78554c1264c0a639f3255710b960a11cde865b06a9b0508d76c75ebb91152846bba3af5dc66a94233f60dc54d8254a11fda0c1aa6c12a508fec8a225591222847f685112ac67114237364d96095260551b5e26d3049930298d5cd750b995582846b7a1b6c130298a618f6abb3295354920d734654cca9aa49063dab30ba5495148396d175442a4a8a41cf48ba8cd5254520e7b05d2a4c0aa2907ad86a15260551482d6c1b4c12a4c0aa36bc0da6093260531
def gzl9 : Packing := (46,5,6,0,0,10,0,gzd9)
def hashgzl9 (i : Nat) : Nat := 0xd15324d0eb0200
def gzd10 (i : Nat) : Nat := (if i<5 then (if i<2 then (if i<1 then 0x8895611482bfcb31a384520ebf28868e11483bdc955a384520aff1ca60e11483bf46a23384520fbd2888ce11483fd49563384520bfe2cc54a11483bf86a15284520fbe28854a11483fd854d5284520ffc23354a114823fe716bb6a1108ff9c3aeda84423fe70abb6a110cff1c1aeda84429fe325b76a110a7f8c96d5a84429fe325b36a110a7f8c96c9a84425fe325ba61d10adfacc6a2774425fe708b969510d3f8b9a21a54429fe325b369510c7f8b96cda54429fe325b26951097f8c96e985442bdeb31a895510d3f8b9a21a344357e2e67768d10a7f8c9695a34435de2e65568d108ff9c8aeda34423fe716bb68d10cfb9c4aeda34423fe70abb68d10a7f8c96e1a34432feaee8868d10e3f8b9a21a34429fe325b768d10cdfabb9dda344397e2e67768d10e9fa889dda34429fe325b568d10cf7abb955a34439de2e65568d10eb7a88955a34425fe325ba60d108ffacc6e9834431fe325ba60d10cdf9ba9dd834433de6ea5560d1097f8c96e9734425fe325ba54d108ffacc6e9534431fe325ba54d10afdacc6a233443af6a21a78cd10edd9a89de33443e76a22778cd10b7d8c969633442bf6b31a58cd10e7d8c969633443bd66a2558cd10fb5a88956334429fe325b868910cbfabba21a24429fe325b568910cf7abb955a2443adea225568910cfdabb8cda2443af6a223368910ef5a558cda24425fe325ba609108ffacc6e9824431fe325ba60910cf79ba955824433f66ea33609109df9c7aed524425fe325ba549108ffacc6e9524431fe325ba549108ff9cb6a1524433f66ea33549108ffacc6e9324423fe72da84c910cbf9baa21324423fe72da54c910cf79ba95532442bfab31a888910b7e8c969622442bfab31a588910e7e8c969622443afaa21a588910afe9ca61622443bda6a25588910fb6a8895622442bfab31a388910ebea8868e22443bda955a388910afe9ca60e22442bfa7295388910efc9a88ce22443ef2a223388910efc9a58ce22443fd29563388910b7f1c22e551442dfc325b854510aff2cc6a1514433fcaeda854510dbf2bba2151443cfc2e68854510b7f0c96cd51442dfc325a354510dfd2bb8cd51443df42e63354510efd1a88cd51443ef4a223354510b7f0c96c951442fdcb315254510df72bb54951443ddc2e55254510ef71a854951443edca215254510ff523354951443fd86095254510dfe2bb88951443df82e62254510efe1a888951443ef8a222254510ffc23388951442b3e71aaa9dd81aeb9c6aaa44606bb671aaa8cd81aee9c6aaa22606afc3298260551fb6182549815469fa325a588941afc8ca609324c6afc3298260531fbc1824c9814c7e74a22778ce119fb1c42e58284677c71ebb54a11fba28891222847fc89564488a11ff42558ce228465ed710b960a11af68ca54d524833da2e95254520 else 0x1a14c357e2e677685309ef9c6aed814c25fe325ba6053097f8c96e9714c25fe325ba5453097facc2e5514c35f670cb95453097f9c22e5514c35f62e5b354530d7e8b9889514c27f6716bb4c530b7d9c82e5314c2df6325b84c530dbdabba21314c3cf62e6884c530b7d8c96dd314c3776aee774c530f5d8b99dd314c3e76a22774c530b7d8c96d5314c35f62e5b54c5309fdacc6d5314c35f6325b54c530b7d8c9695314c27f632d824c530dfcabb889314c3ef2a22224c530dfc9b5889314c2ff4b31814c530dfd2bb605314c3df42e5814c530fdd277605314c37f46d5814c530fbd182605314c3ff0889814c53097f8c96d5214c2ff4b313148530dfd2bb4c5214c37f46e13148530fbd2884c5214c3afca21a784530f9f2889de114c2dfc325a584530bfd2cc54e114c3df43255384530fbd28854e114c3fd46155384530ff515354a114c3ef8a222284530ff625588a114c3ff054e228453097f9c12e5a84823fe70ebb6a120cfe9c2aeda84823fe706bb6a120a7f8c96c5a84827fc706bb6992097f8c96e9854825fe325ba59520b778c96a2554823fe722bb68d208ff9c5aeda34833ee712bb68d20cfd9c3aeda34823fe706bb68d20cbfabba21a34829fe325b668d20cefabb999a34829fe325b568d20cf7abb955a3483adea225568d20ee7a66955a34823feb31ba60d2097f8c96e9634825fe325ba54d20cef8ba99953482bf6b31a88cd20fb5a8895633483bd669a558cd20fe5a6695633482dfa325b854920b7e8c96a1524836faaee8854920b7e8c96d9524837baaee6654920b7e8c96cd52482fdab315354920df6abb54d52483edaa215354920fe6a6654d52483fd260d5354920dfcabb8cd52483ef2a223354920feca668cd52482dfa325b1549209ef9c6aed814825fe325ba60520b3f8c96a181482afeb31a860520cbfabb6a1814838fe325a860520ebd9a88cd81483afa6a1526052097f8c96e9514823fe720ba545208ff9c32e9514832fe2ea8854520cfd8ba8cd51482fdab315254520df6abb54951483edaa215254520ff4a33549514833fc2e98154520ebf1a860551483fd8549815452097f8c9aed314823fe720ba4c5208ff9c52e9314832fe2ea884c520cf78ba95531482bf6b31a34c520cfdabb68d31483af6a21a34c520ef5a5568d314833fa2e9524c520df69b5549314833fc2e9814c520ebf1a860531483bf468d814c520b7e8c96e121482dfa325a848520dbeabba2121482dfa325b5485209feacc6d5214835fa325b548520dbea886d5214837daaee5548520fb6a88955214837f2aee3348520fbca888cd214837f26d63348520ff4a558cd21482ff8b313148520dfe2bb4c521483ef8a213148520ff62554c521483ff068d3148520b7f0c96a211482bfcb31a884520e7f0c96a211483bdc6a25584520fb72) else (if i<3 then 0x461ff72ca94c951afe9c0aaa225469fbb30a988951a7edc82a6225469fb70ca988951e3eca9a22225479f32a63388951c7f6aa2e5815475f52e63360551b3f4c9609815475dd2e55260551fb6582549815475f92e62260551a7bdc42e6aa4c71ef710b9aa93187fcc96d6aa4c61ff325b2aa93187fecc6e0a94c61ffb31b52a53187fcc9aeda84c63fe702bb6a13187fecc2e5a84c61ff714b96a13187fdc22e5a84c6afe702aaa2131a3fecc2a6884c68ff714a9a2131a3fdc22a6884c61ff720b969d31c3fcb9a21a74c61ff728b961d31a5fcc9aaa774c6b7e702aa9dd31a5fecc2a6774c697f720a99dd31a5fcc96a2774c787f2a6889dd318ff9c0aeda54c61ffb30b96953187fdc22e5a54c63fe700ba6093187fdca2e5824c65fd704b96093187fdcb2a5824c68ff720a96093187fdca2e5524c61ff72ca954931a77dc52a5524c74f72e6884c931afccca609324c69fb720a988931a7edc52a6224c69fb325a888931e3eca9a22224c69fb325a588931abf4ca609814c6cfd3258260531b7d4c94c9814c7ef1609326053187fecc6e0a94861ffb31b52a52187fcc9aeda84863fe702bb6a12187fecc2e5a84861ff714b96a12187fdc32e5a84868ff326aaa2121a3fdc52a6884868ff70ca9a21218ff9c0aeda54861ffb30b96952187fdc82e5a54861ff70cb969521c3fcb9a21a54861ff325ba6152187fdcb2a5854861ff326bb68d2187fdc82e5a34861ff714b968d21c3fcb9a21a34861ff325ba60d2187fdca2e5834861ff72ca960d2187fcc96e9534861ff728b954d2187fdcb2a5534869f7720a98cd21a7ddc52a6334869f7325a88cd21e3dca9a22334869f7325a58cd2197f5c32e5878465fd326bb6161197f5c32e5858465fd708b96161197f4c9aed838465fd714b960e1197f5c22e58384757d2e67760e1197f5c82e5738465fd325b85ce11d3f4b9a2173846d7d325875ce1197f4c9aed538467fc702bb54e1197f6cc2e5538465fd720b954e1197f5c22e5538465fd325b854e11d3f4b9a2153846df53258354e11b7d4c961e33847e75a22778ce11b7d4c9616338465fd326bb60a119ff1c0aed82846ded710b960a1197f6cc2e5828465fd714b960a11d7b5c42e5828465fd70cb960a11d774b9955828475f52e63360a119df5c7aed528465fd720b954a1197f5c32e5528465fd325b854a11d3f4b9a21528475f52e63354a11b7e4c9609528465fd326bb4ca1197f5c82e5328465fd714b94ca1197f4c96e1328474fd2e6884ca1197f4c96d5328475dd2e6554ca11b7e4c961622847ed9a225588a11b7e4c960e22846df93255388a11fbc6888ce22847fd19563388a119df9c7aed52583f9a9556388960fec9658ce22583fd2956338896097f8c9aed824c27f670ebb6093097f8c96e9624c25fe720b968530d3f8b9a2 else (if i<4 then 0xe72da854d21cbf9baa2153486bf6720a98cd21ebda882a633486bf6714a98cd21ef5a552a633486bf6b31a58cd21afd8c969633486bf6729858cd21aff2cc6a1314873fcaeda84c521dbf2bba2131487afcaaa884c521dbf2bba2154846fecb3185912119ff1c52e5838477f454cb960e119ff1c22e58384777caee7760e11ddf0b99dd838467fc720b95ce11dbf2882e5738467fc325b85ce11bdf0c961d73846ff4b31878ce11bfd0c961e338467fc716bb60a119ff1c3aed82846fec710b960a119ff1c52e5828477dc954b960a11dfb1c42e5828467fc70cb960a11dfb2bb91182847fcc9564460a11bbf2cc60d828476fcaed8360a119ff0cb54d82847ef460d5360a11dfd2bb8cd828477f42e63360a119ff1c82e5528476fca20b954a119ff1c32e5528477ecaee4454a11dfb1b891152847eeca224454a11dfd2bb8cd528477f42e63354a11fbd2888cd52846ff8b318254a11dfe2bb60952846ff83258254a11ffa24460952847ef860d8254a11ff615360952847ff08cd8254a11dbf2bba21428476fca21b550a11df72bb955428477dc6e25550a11fbb288551428467fc720b94ca119ff1c52e5328477dc954b94ca119ff2cc6e1328467fc325b84ca11dbf2bba21328476fc2e6884ca119ff2cc6d5328467fc325b54ca11dbf2886d5328467fc72d854ca11bfe2cc609328477f8aed824ca11dfe1b560932846ff8b318488a11ff625561222846ff8b315488a11bfe1c855222847ef8a215488a11ffa18455222847fe86164488a11bfe2cc60e22846ff83258388a11bfe2cc54e22846ff83255388a11bfe1c854e22847ef8a215388a11ffc18354e22847ff06163388a1187fecc6d4a958e1ffb31b22a563a7edc22e6aa60b1fb708b9aa98297becc6d0a960a9efb31b42a582c7bdb46c4a960a9f7704a98cd82a7bdc42a5a160a1ffb31b52a56287fecc6cca958a9f7714a98cd6287fecc6d4a94ca1ff704b96a13287fdc52e5a64ca9bf714a99993297edc52e58388a5fb704b960e2297edc52e56388a1ffb31b52a58187fecc6cca96061ffb31b22a581acfdc6aaa7760697f70ca99dd8187fdca2e5736065fd704b95cd81aeddc6aaa336069f7714a98cd81a7ddc22a6336079772a6778cd819bf9c0aed82606cef710b96098193fecc2e5826070ffaa8b960981d3bdc42e5826074f72e6336098187fdcb2a552606cfb325825498187fdca2e5326061ff72ca94c981aeedc6aaa226069fb714a988981a7edc32a6226079f32a6338898187fecc6e0a95c61ffb31b32a57187fdc32e5a85c68ff70ca9a217187fdcb2a5835c69f7720a98cd71a7dcc96a2335c78f72a6888cd71b5dcc961e335c61ffb31b32a551afd9c0aaa335469f7b30a98cd51a7ddc22a6335461ff728b96095197bdc42e5825461ff72ca96095187fdca2e5325 else 0xb960551b7f0c9691815477ecaee4460551efb2aa91181547fe888a4460551dfd2bb8cd81547bf4aaa3360551dfd0b98cd81546efcb318260551dbf2bb60981547afcaa98260551bbf0c960981547eec9118260551fbd233609815477dcaed5260551ef72aa549815477dc2e55260551ff324454981547fd48cd5260551fbe1824c9815469fe325a5609419df9c7aed525069fe325ba54941ebeaaaa2222507afaa21a588941afb9c42e6aa4c63fe325b8aa9318ff8c96d6aa4c63fe325b2aa9318ffacc6e0a94c63feb31b52a531cf79b8954a94c73de955b22a531cbf9c8aeda84c73be71abb6a1318ff9c5aeda84c63fe70abb6a1318ff9c52e5a84c63fe708b96a131cfea222e5a84c6afe716aaa2131abf9c2aaa884c6afe714a9a2131abf9c22a6884c67fa70abb69d318ff9c82e5a74c72fe2e68869d318ff9ca2e5874c6b7e722aa9dd31adf9c82a6774c6b7eb31a89dd31adf8c96a2774c7a7eaaa889dd31e9f8a9a22774c73f670ebb695318ff9c2aeda54c73fc706bb695318ff9c22e5a54c63fe714ba609318ff9ca2e5824c67fc704b9609318ff9cb2a5824c6afe720a960931abfacc6a1824c72feaeda8609319df9c7aed524c6bfa70aaa549318ff9ca2e5524c63fe72ca954931af79c52a5524c6bfa3298254931ebe9a8609524c76f6a20b94c931bfcacc609324c77f2aed824c931efcaaa609324c7ef26a1824c931ffc1c1609324c6bfa720a988931afe9c52a6224c7bda954a988931ebeaaaa22224c7afa2a68888931afeacc696224c6bfa325a588931ebea88696224c73fcaeeaa60531aff1c5aa9814c777caee7760531edf2aa9dd814c6bfcb31a560531cff2bb695814c6efcb318260531dbf2bb609814c7afcaa98260531bbf0c9609814c7afc6958260531ef71a5549814c7ef86095260531bfd2cc4c9814c77f4aed3260531efd2aa4c9814c6ff43253260531dfe2bb889814c7bf8aaa2260531efe1a5889814c63feb31b82a5218ffacc6d4a94873de6e2552a521cf7a556cca94873be71abb6a1218ff9c5aeda84863fe70ebb6a121cff1c1aeda84863fe714b96a121cf7a552e5a84863fe70cb96a121cfda332e5a8486afe714a9a2121eb7a552a688486afe70ca9a21218ff9c8aeda548737e71ebb695218ff9c3aeda54873fa70abb695218ff9c82e5a54863fe70cb969521cbfabba21a54872fe2e68869521a7f8c96d1a54863feb31ba615218ff8c96e9854863fe72ca96152197f8c96e954486beeb31a891121ebbaaaa2244486beeb31a591121ebba8869644486bee72985911218ff9c82e5a34863fe714b968d21cf7a552e5a34872feaee8868d21cbf8b9a21a34863feb31ba60d218ff8c96e9834863fe728b960d218ff9cb2a5834863feb31ba54d218ff8c96e9534863fe728b954d218ff9cb2a5534863f))) else (if i<7 then (if i<6 then 0x95197fdc32e5825469ffb30a960951c7febb2a5825469ff325ba4c95197fdc82e5325469ffb30a94c951c7febb2a5325469ff720a94c951c7fca96e1325479fb2a5824c951f3f4c960981546dfd3253260551d7f4b94c981547ef96093260551a7fecc2a5874c71ffaeca961d31e5fdc72a5874c797f2a5a761d3197fdc52e5824c69ff714a960931a7fcc9695824c677f71ebb54931a7fcc9aa9524c6bfb70aaa54931c7feaa2e5524c65ff720b954931a7fdc82a5524c69ff325a854931c7fcb96a1524c6bfb3298254931b7ecc9609524c7afb6a18254931b7dcc96d5324c7ff1705824c931b7f4c9549814c7ef960952605318ffdc3aeda84871ffaeca961521a7fdc32a5854869ff326aa60d2197fdc52e5834869ff714a960d21a7fcc9695834871ff2e5a560d2197fcc9aed534869ff326aa54d2197fecc2e5534871ffaa8b954d2197fdc82e5534871ffaeca954d2197fcc96e1534871ff2a5b854d21a7fcc96a153486df73258354d21e7dca960d53486dfd325854c5218ffacc6d4a958e3feb31b22a563cfe9b5888a958ebfa708b9aa9828ff8c96ceaa60a3fe325b1aa9829fbacc6d0a960abeeb31b42a582cfb9b46c4a960a3feb31b12a582cfda336c4a960a7f670ebb69182afb9c1aaa4460abee710a9685828ffacc6d4a958a3feb31b32a562cf7a556cca958b3f66d6332a5628ffacc6d4a94cb2fea21b52a532cbfa886c4a94ca3fe704b96a1328ff9c52e5a64cabbe714a9999328ffacc6d4a96063feb31b32a5818ffacc6c8a9606b7e70ca99dd81aef9c6aa9736063fe728b95cd819ff1c12e573606bf6714a98cd81afd9c22a633607b76aaa778cd81edd8a99de336072feaeeaa60981bbb9c42e5826072feaa8b960981dbb9c42e5826076f68ccb960981dbbabb91182607aeeaaa4460981aef9c6aa9526063fe72ca954981bbeacc60952607afaaa98254981bbe8c960952607eea9118254981aef9c6aa942606bbe71aaa4c9818ff9ca2e5326063fe72ca94c981bbeacc609326076faaed824c981ebeaaa60932606bfa714a988981afe9c32a622607bf28cca988981efaaaa912226063feb31b82a5718ffacc6cca95c63fe70cb96a171abf9c32a6885c63fe72ca960d71afd9c82a6335c7af6a20a98cd71afd8c96a2335c6f76325878cd71cfea226ceaa5472fea21b2aa9518ffacc6cca95463feb31b22a551cfe9b8888a9547afaa22222a551cfe9b3888a95465feb30b969151c7faaa2e5a45475fa2e62269151afb9c2aaa44547beaaaa2291151fbaa8888a44546bf670aaa8cd51afd9c22a633547bf2888a98cd51a7f8c9691a25463fe728b9609519fb9c42e5825463fe72ca960951cfb8ba911825465fe325ba509518ff9ca2e5325463fe72ca94c951cff2bbaa981546bfc70eaa60551cff2aa2e5815477f8888 else 0x49dba3b4275a8e999d2e3a3e7440e809cd4398a7238e3a9c7038c27120e1c9c34384a6fb8ddb9ba8371e6db0d9f9b1c35ca6ab8d4a9a86350269a0d2c9a4a348a68d8d139a0e33d666a8cc3996e326e64a0c8798d8317e62c0c509892310661a8c1997f22fc65f28bce97522e5e5be0b7496d02d6e5a50b2e96262bde5758ae395b82b665690aca95862aee5578aa295362a4e5488a89950429fe53c0a6b94d2298652d0a4d948c290e51e0a39946e28d25168a25943c28465050a0293f627e24f889e993c4276a4e989d0939c271a4dd09b29356268e4d08999932e26524c9098f931a262a4c4098092f225c64b7896792b6254e4a60949928e24fe49c09309248244a485890391f823d247908ea91c6236e46c88d19194231e46008b8916222a6451089a911c221a43f887790ea21b6433085e90ae213e424083b907220da41508279040206240b0809900e1ffe3fc07f08fd21f863ed07d28f961f223e087b98f641eaa3d187a08f321e463c507828ef61dce3b607648eba1d563a707468e741cca39587238e421c7a38b87148e1a1c1637c86f18dca1b7636d86d88da21b3a36386ba8d661aae352069c8d2a1a4a34806888d0219e6339066a8cc6196e32786428c8018f631d86388c58187e30c06108c1218062fa85e88bcc178e2ee05d48b9016ee2d785a28b2c163a2c3857f8af015c22b485618ab4154a2a585438a7814d2299052f8a5a14aa28f051b8a32145a28a05118a14140a27d84f389e213ba27604df89b0134226484c1897412ca25584a389381252246848588fc11da237846c88ca11622288449888410fe21e8430885c109a20f84178820102220083fe87ee0fbe1f683e587b20f461e783c787800eba1d3839a871c0e1a1bf837286cc0d7a1ae035486a40d3e1a6834a86860d0219c8336865e0cb21950327864a0c8a18d830e860e0bfe17c02f085d20b7216a82c885820ad215402a085280a321428282850009f613d827384d809a6131025a84a6091a11f8237846a08ca11802288442087a10b820a841008020fc81ec83d4078a0ed81d383a207260e101b5835c069a0cf8192832006220c0817982c605460a28138824e041a07a80de8190029e048807f80e60186028003e805a005a00025ff714b968582a7fdc52a5a160b1ff2e5a56858297fdc52e5a64ca5ffb30b96953297fdc82e5a54ca5ff704b969532c7fcb96a1a54ca9ff325a669532c7fcb9699a54cadfb325b560932b7ecc9695824ca9ff325a568532aefdc6aa9736071ffaeca95cd81b3fdc52e582606cff325b560981d3fcb96d582606bbf71aaa54981c7febb2a5526069ff70ca954981f3ecc960952606bbf71aaa4c98197fdc52e5326069ff714a94c981a7fcc96e9835c71ffaeca960d71a7fcc96e9825469ff728b960951c7fdba2e582546def710b960) else (if i<8 then 0x1f18140f8160f6214c1b90b60821ca983dc40212d4e1e6201080f9a9438080f2c46b51e2b63472085aa6c43e41541721aa58e3e4354b1c7c86a9638c42d53621803c2e28109350e1694028900e200abff27fb2ff01fd3bf8e7eeafd49f9cbf2a7e36fc09f74bed07d82fac9f4cbe807ccef8e9f15be127bdef759edebda47b16f5c9eb1bd547a76f489e84bcf079aef2f9e52bc8278d2f169e2abc467882f0c9e07bbf677ceef39ddabb9c7706eda9d9ebb247616ebc9d62baa274fee971d21ba34744ae859d03b9ee73aae6f1cd1b98a72e2e561c9fb91c71f2e381c63b8ae712ae1f1c31b84a7062e0b1c0eb80e6ffedfc1bf5b7dc6f9adef9bd7b7a06f22de09bbeb76e6ed2dd69ba5b73c6e6edcc9b91b71e6e32dc29b7db6f66dcedb61b64b6c46d6ada99b4bb6926d1ad9f9b3cb66a6cb6d959b23b6426c66d891b0ab5fc6bdad7a1aecb5ca6b76d6b1aceb58e6afed5e9abab5706ad6d599aabb53e6a5ed481a8db50c69fad3e1a79b4ee69bed369a65b4b26946d279a4cb4626892d0e9a1ab426682ed049a01b3fe67cacf599e3b3ae673ece199bbb36866b2cd519a2b3366626cc1197ab2dc659acaf9957b2aa654aca81948b28c64fac9e1934b25a6496c8f1916b21e641ec7d98f3b1e263a6c6e98d5b19262f2c5a98adb156628ec4e1894b11a6216c3f187bb0e861c6c37986cb0ca6162c2b184eb0986112c1e983ab07060d6c19982bb0526072c0a980db00c5fe6bf697eaafc65f6ebea17ccaf805ecebd3979aaf305e56bc7178baefe5dcabb59768aecc5d8ebb0975eaeb85d66ba9174fae905d02b9f1736ae685cc6b979727ae365c4eb861709ae0e5bfeb7c16f0add25b86b6a96cdad8c5b0eb5e16b4ad5a5aaab5196a0ad325a5ab4a1691ad1e5a1eb401678ace259a6b31165aacb0592eb1d1632ac56588eb0e1619ac24582aaff15f6abde57b2af515e7abb6574eae615c4ab7056c2ad495a1ab2a5636ac31583ab0255faabb9574aad05596aaf155baab25546aa51547aa8a550aa9d9538aa6c54cea98952eaa4e5492a91151faa305456a899510aa1c541aa7f94f7a9e0538ea7094d9a9a4533ea6694caa98652eea5a14aca954528aa4d9493a9225212a3e947aa8dc51aea321461a8b4514aa28144da8965122a23143ea87850d2a19142aa846506ea0a140ca80a4ff69fb13f3a7d84f7e9ec13d0a79c4f1a9e213c1a7744eb69d31399a6f24dc69b2935da6a24cea9999317a5f84b6e96a12b8a5444a2e942127ca4ea49b69309254a490490291c921da41848128fe91f5a3e647c28ef91d7a3a046fa8db91a0a31e45e28b1115aa2a6452e8a4912da22443da87790d8a198431286110baa134425e8481083a0e4415a8201024a012401a7ff8ff29fd63fa27f30fde9fae3f167da0f8e9f043dd67af8f3e9e3c3c327800ee else (if i<9 then 0x505790e62c7000a0102003830001400080e0803000131024058c0410c041502402e4398000c0d502aa1282d88090007cc085aa6c404941001c1800080f0200c00e00141e040070600028000080048080008010f051e08130f0003a611e00060501645e214c78e001c0046050200020279009400202a040416c70e04981508002b5387024c0f000100c090004048040f02a00142008001008020401801c00280408030038005000010002000410060070008000402040070600028004108000040024040004000041508358e1c0028400800e0c0005e1c21000020800700060800e040404023540806100100803000142000010050082811aa0a0708090c1c5838707083070f0e108000150e10000307a8708310f6000303c0004030240010120103c0a8005080200040204c1001c20000a1000020002000400082610001310260102003800504c200081001c003000104c00102603f2000101504c0908002d1c0038201000030801006007000a10040008040004020402000061002003830001420040070600028400800e0c00052435812b01d602096038c07180e301c60581204210a020c0410404140820408281084206301c6038c0b02c1c2081c2000387088e1d503c388e26602410482080420a301c6038c071808018c05021085cc05980f30105301000000000ac06870b30101041009871026108020070e104c2098413e1c5ac027c38c00081010003c38400004000a0410000140820c40200040008041000209875000848107100a0410404100030107070e0e1808209f0e200002a1c40a1c3c38404153020530120824107870f0e1660204040808008081010202040408083470e8e140828104080a04102028104080a041c1c383840800840404080820100190080080810140b181010140b1810101000210825808058c0b180e301020200040008000f041f0a3c1b602000401080214081e10048f080000000078405000200020084010802142c1e10168f080007830f040102c40080020001e1000020800078400041f0a04100020104000c04140828f04020c04100830104000000400440000002083438687090e1000000d30226034c04010d30187830f04000a0c100020004000800100024f040008000080163880008001278200001a3881a38747080010002000502080000a041060e10034712041060e10002000040f0c000a2083891041c40004000800010800d1c44f040c80400001900800008000080000000008000f08000a2014403c804000817c80800082dc809160805c80816e4048b079005848b049e08000012016402020834b0696092c4808960b2010000000400082180a058c08000040008058c0808c07180800104161028205cb0282c30586580a058c0808c07180e301d5b54d619026ada3b203d1d9016a8c80b10e6 else 0x1d02440e813910c1d02694183a04881d02440e840207409103a04881d02714183a04881d083a10240010000a8809000404840908132a0800d5040480020742006b582012108000103a04f4430740910124d082002440e8122074091234102420e81220241d103a04881d02440e81220241d103a04881d0801a183a04881d08318083980810000283020001010102254103a0408090204040122074081012416a804115402440e81620201d103405811aa101d02754183a04c3430278702c60e81220502048420083a107787101210081d00040e840205409103a04881d02440e812207409a5060e884000c1d02440483a207409103a0d081d00040e812207409103a048813107070f441e88202883d107a20f44101c3d107a2083a2083a20f281e502007281003620ec4107441e883d1040d107a20f441003a2082140ea8106a81062814783ac049e06050f04151061e0e8e1d1c3d1049e0c3c1000000744107ae2158e1d8820d882510400040e1003a10740b12441003d4f8b47e601d283bcc0b98083980f30101301003b8c0b980f30108b98100e10779817301e6028c0410c0618083bb1630347838c0722c6048f07180a3010001cc0400f8410f051e0c3c18783cc04820ab0120b58170e1030e100b87170e100b87103dc38b870a341023c1e1c3c387870f0e1e1c2026820003870835c3881c38400d049e08000070e10035c38b870f0e1e1c20d70e2e1c0b1020b0ab01d603c3841ae1c5c38162e1c0b170e05880007c20c1c1a13208388900800000000078204783838400f0400070e107f87170e1e1c20043c1a1c28f07070a3c107b9017201440206403c8079008390083900800007201e403c8051a0f201e402858400eeb0202c1ee407c80790088412782022c34c04902605c807900800007b9017201e403c8040bd605ac07580eb010435812301240200008b080902604081c20068e1b60200034708000002d408000d50200001aa07540c8e195022103c206a8110820003580ab01d603ac041ac061e0cb01043d2c084b0821e960409602051c32c04000001a3840258412c04580c3c191c20f06c70d8e1b6020b6024f1b027603638416c0400b6024f1b0276020e81220540907790b5387303e10241f17281108071005ca0121010200812016a1ca04050401401c20024a0a8120ef21ca58e602420a02003840049794e1c0908090f729c38124024204840908121000091000100800080400040008120a020038005079900007aa07540840100009d5020184010803aa012100c00093c0c00e001390d600918200c00e0010072781800080f041e083c10005cc02a0f000))))
def gzl10 : Packing := (941,4,6,0,0,15,0,gzd10)
def hashgzl10 (i : Nat) : Nat := 0xe138000829e000e488000800f8c9c048000000480b8341844e07004b8079818c165827e08e814e155817a14f00ee16f85000f080900d309fe2878a3e36b0072c8c04140ad011e069029e3108d5f08e83720840240000001e0e2004c12483120cc83e0004857a0bc04600340a480b0042413483a1021f103c0200e431800209000
def gzd11 (i : Nat) : Nat := (if i<8 then (if i<4 then (if i<2 then (if i<1 then 0xca958b37e54ac6b167dca98cd628ffb7054a651ff6d4a94ca3fed89529947fcb96a1328ff972d32659bf2a6664cabf65cb071157ecb958e22f79d1119c45fb399a3388a77edb554c0c7fdb52a5818ffb6654b031ff6c8a96072fe54ceec0e7dca98cd81a7f972c13039fb2a6226063fedc152b8c7fdb32a5718ff972d42e38ff2a6885c6afe5cb0eb8e7dca98cd719ff361552a31ffaeca95463fed9952a8c7fdb22a551cfb95319aa39fb2a622546bfa5cb02a8c7fcb9aa9319ff361552631ffaeca94c63fedc15298c7fdb52a5318ffb6454a631ff2e5a84c71fe54d1098c7fcb969d31cbf9533ba631ff2e5a54c6bee5ca6498e7eca9889318ff973552431ff6e0a94863feda95290c7fdb32a5218ff972d42438ff2a6884863fe5cb4a90c7fcb968d21cfb95319a435fd2e587847cfb444ef08d7f4b961611afe972c1c235fd2e573846bfa5caa708fbd6888ce11fbacef19c23fd595633846bfa5cb0508d7f4b954a11afe97299423ef9a2222847fb32ac4508ffc63388a11fcf4aab1ac1fb659633583fad2ac66b07ee96588960fed4ab112c1fba58e22583fe519c44b07bea8888930dfd34d11261fba99a224c2bfc5cb429857f8b954530bfb57698a61df62e5314c3ded44262987dda774c530bfb36a98a61ff2889314c3fe8c0a62987fd13148530f7e51108a61bfc69e114c3ef93bc22987f725584530ffa2a708a61ff888a114c2bfc5cb50904ffabb6a120cff172d4241edea22554837bcd34aa907e7a66955209ff576d1a41afea21a348377d33346906f7a5568d209ff374c1a413fe2e9534837ecd4466907bda888cd20dfb34d19a41fb699a33483fad2ac66905feabb54920f7d510a9241fba99952483fb4a9aa4907fca3354920d7f350c0a413fe2e951483fb4a92a2904ff8ba4c520dfb34698a417faaed21483df544242905fe9b548520fed4aa90a41ff28cd21483ff098a42906ff1a884520f7e51108a41fdc956114837f8d1c22907fd23384520ffc2a508a413feaeda84435fd4434e886df9a89dd10f3f5113ba215fe2e5a54427fd5db4a8867f8b969510def3512aa21edea2255442bfc5cb46884ffabb68d10cff172d1a21afea21a34436fd3bb46886f7a5568d109ff374c1a213fe6e9534437ecd4466887bda888cd10dfb34f19a21f769de334437ecd2c66887f5a558cd109ff576d1221afea21a24437bd2ab44886fda33689109ff374c12213fe6e9524427fcdd264886fe9a888910f7d51111221bfa69622443fb52ac44886fe9a388910ff9467112217fcaed51443bf85caa2886ff1a854510f7e510a8a21ff48cd51443fb8a92a2887fe222545109f736854b05eeaa224488a77cdb554c0c7f8b969541f7651122423fcc95644847de94446708fdd2778ce11f7c51111423fe891222847fe119c4508c7bdb42a582 else 0x4ff9b32a582dfb46654b053fe6c4a960b7dd55488c14ff9b52a562def4aa54ac53fe6cca958b7ed19952b16ef8a958d629ff37054a65afea20a94ca7fcda952994ff9b12a5329ff576d42653fe2e5a84ca7fc5cb4c996efaaa99932ddf153332657faaed824cb7f555304995feabb612229ff36a54b033fe6cca96067fcd9152c0edfaaa9dd81dbf1533bb03beeaaa446077ed55466c0efd8a98cd81fbb4ef19b036feaed826075fd55304c0dbf8b960981f77488c1303efa60952607df4c1264c0efeaaa88981dfd15311303fea912226067fcdc152b8cff9b32a5719ff172d42e3afeaaa885c75fc54d10b8ddf8b961d71dfb55519ae3bf62a6335c77ecd4466b8fdd9878cd719ff367552a33fe6caaa5467fcd9952a8cff9b22a551dfd44454aa35fe2e5a45477dd55488a8ffaa2291151dfb55519aa3bf62a6335467fc5d304a8dff2bb60551dfe554c0aa37fc2e581547fd922302a8ffd23360551f7e304c0aa3fdc549815475fd55510a0fbba8850941dfd55511283bfa6a222507df544444a0efe9a588941ff5309112833fe6e2aa4c67fcdad5498cff9b2aa9319ff37054a633fe6d4a94c77bd2a95298cff9b22a5319ff576d42633fe2e5a84c75fd5551098ebf8a9a21319ff172d3a63afea21a74c76fd554ee98edf8a99dd31dbf3513ba63e7ea22774c67fd5db4a98cff8b9695319ff174c1263afe6a1824c6fed5da6498efdaaa4c931bfb17299263ff2609324c77f55544498efe8a988931f7d51111263bfa696224c6ff95db0298eff2aa60531fbe4eec0a63bfc695814c7df8c130298ffd13260531ffc444c0a633fe6e0a94867fcda95290ef7a552a5219ff36654a433feaeda84867fc5cb5090ebfaaaa2121d7f153442433feaeda54867fc5cb4a90ebfa88695219ff374c2a43afea21a44877dd5548890efb9a891121f7751122243bee696444867fd5db4690cff8b968d21d7f510d1a433fe6e9834867fcdd2a690efdaaa8cd21dfb15319a43bf669633486ff95da6290eff2aa4c521dfe35098a43efca2131486ff95db0908dff2bb55211bfe370aa423efca2154847fd8c22a908ffb18591211bfe576c1c237fc2e583847ef93bb0708dff2bb5ce11bfe172b9c237fc6e173847ef8c3ae708ffd1878ce11bfe576c14237fc2e582847fd92230508fbf18360a11ffa466c14237fcaed52846ff85caa508ffb24454a11ffa466a9423ff860952846ff95da8508dff1b850a11f7e510a14237fc6d542847fb92aa8508ffb15450a11bfe576994237fc2e532846ff8dc26508fbf2884ca11bfe36a99423ff860932847ff0c244508ffe15488a11ffc30711423ff854e228463feda952b1c7fdb22a5638ff973553053fe6c2aa60abdeda152c147febb2a582cf7b6854b051ff6cca960a3fed8952c167dca98cd828ffb6a54ac51ff6c) else (if i<3 then 0xca9a41fde61553483fecc1aa6907fd9a88cd20ffb34d19a41ff669633483fecc2c66907fd9658cd20ffd370a9241ffa6a152483ff4db2a4907fe9a654920ffd366a9241ffa68d52483ff4c1aa4907fe96354920ffd362a9241bfe6a1a1483dfd44342906ff9a568520fef4aad0a41bfe68da1483fed19b42907fe95268520bff576c0a417fe6e9814837fcdd302907bf9a860520fef4aac0a41bfe68d81483fed19b02907fe95260520bff576a8a417fe6e9514837fcdd2a2905ff9b854520dff350a8a41efea2151483fbcd2aa2906ff9a354520ffb466a8a41ffa6c951483ff8c0aa2905ffabb4c520bff37498a41bfe6e931482ffcdc262906ff9a84c520f7f51098a417fe6d531483fbd2aa62907fd9a34c520ffd2a498a41ffc60531483ff4dc242907fe9a848520ffd36a90a41ffa69521483ff4c2a42907fe9b348520ffd34690a41ffa60d21483ff4a9a42907ff1a884520ffe34b08a41ffc61611483ff8d1c22907ff18384520ffe2a708a417feaeda84437fd5db50886ff9b76a110dff36ad4221bfe6cda84437fcd9350885ffabb69d10dff350d3a21efea21a7442ffd5db0e885ff9ba61d10fbf3513ba21bfe6a1a5443dfd4434a886ff9b369510dff364d2a217feaed85442ffcdd30a886ff9ba61510fef3512aa217feaeda3443bfc5cb46886ff9a868d10f7f510d1a21bfe69da3443efd3bb46886ff9a568d10fef4aad1a21bfeaeda34437fcdc346886ff9b768d10dff30ed1a21bfe6d5a34437fcc2b46886ff9b268d10bff576c1a217fe6e9834437fcdd306886ff9a760d10fbf4eec1a21fde95583442ffd5dae6885ff9ba5cd10bff370b9a21bfe6a173443dfd442e6887df9875cd10bff576a9a217fe6e9534437fcdd2a6885ff9b854d10dff350a9a21efea2153443fbcc2aa6887fd98354d10ffb35119a21ff669e33443fecc3c66887fd9a58cd10ffb30b19a21bfe6a1a2443dfd44344886ff9a568910fef4aad1221bfe68da2443fed19b44886ff9b868910dff36ad1221bfe615a24437fcd9b44886ff98368910dff2a6d12217feaed82442ffcdd304886ff9ba60910dff34ac1221fde955824437fcd1b04887bf98360910ffb466c12217feaed52442ffcdd2a4886ff9ba54910bff370a9221bfe6a152443dfd442a4886ff9a354910fef2a6a9221ff68cd52443ff4c12a4885ffabb4c910bff37499221bfe6e932442ffcdc264886ff9a84c910f7f510992217fe6d5324437fcd2a64887f7a554c910ffd30499221ffa6a222443ff4d2c44887fe98588910ffd34711221ffa60e22443ff4a9c44887ff1b854510ffe350a8a21ffc6cd51443ff8d1aa2887ff18354510ffe364a8a21ffc68951443ff8c12a2887ff132545109ff36a54ac73fe6c8a958f7f511152b1cff9b3aa9829ff363553057ee6d0a960b7dcda152c1 else 0x73fe54b0690cffdba54d21aff972a9a439ff2a5534877ef5546690efdda88cd21f7bd1119a43bf769633486ffb5da6290eff6aa4c521dfeb5098a43efda2131487ff8d826290eff9a868121f7f510d0243bfe695a04877fcd1b4090ffda3368121ffe262d02437fdaed87846ffb5db0b08fff1b061611bfed76c1c23f7d9dd83847ff8d830708dff6bb5ce11bfeb70b9c23efda2173847efac3ae708dff6bb54e11efe972a9c237fd6e153847dfb442a708ff758554e11ffab06a9c23ffc6c153847feac3c6708ffd5858ce11bfed76c1423dfd2e582847fbb2ab0508fbf58360a11ffac66c1423ffc6c182846ffb5daa508dff5b854a11f7ed10a9423fdd54d52847feb19aa508ffe58254a11ffe360a94237fdaed32846ffadc26508fbf6884ca11bfeb6a99423fdd95532847ff2c126508fff1b04ca11ffcb0b11423ff960e22847ff2a9c4508dffabb54d60dff374a9ac1fbe6d953582ffd5daa4b06ff9ba54960fdf2c6a92c1fde54d52583fed19aa4b05ffabb4c960dff374992c17fe6d532583f7cb2a64b07f7a554c960ffd2a7112c17feaeda64c2ffd5db44986ff9a868930dff34cd1261fbe999a24c2ffd5db04985ff9ba60930dff374c12617feaed624c2ffcdd2c4987fe9a888930ffd34d112617feaeda14c3bfc5cb42986ff9a868530f7f510d0a61bfe69da14c3efd3bb42986ff9a568530dff344d0a61ffa889a14c2ffd5db02985ff9ba60530dff374c0a61bfe69d814c3efd3bb02987bf98260530ffd444c0a617feaed714c2ffcdd2e2985ff9b85c530f7f510b8a61f7e61d714c2ffd5daa2985ff9ba54530dff374a8a61dfe2e5514c3fecd9aa2987fea2254530ffe302a8a61ff6aed314c3fecdc262987fd9a84c530ffb36e98a61ff669d314c3fecc3a62987fd9b54c530ffb34a98a61ff66c9314c3fecd1262987fd9824c530ffb2a498a617feaed214c2ffcdd242986ff9ba48530bff37090a61efea21214c2ffcdaa42987fd95348530ffe35108a61ffc69e114c3ff8c3c22987ff1a584530ffe30b08a61ffc68a114c3ff8c1422987ff15284530bff576d4241dfe2e5a84837fd5db50906ff9b36a120dff362d42417feaeda6482ffd5db4a906ff9a869520f7f510d2a41bfe699a5483f7d3334a905ffabb61520bff374c2a41bfe6e985482ffd5daca905ff9ba59520fdf34cb2a41fde6a255483fbcd34aa905ffabb68d20dff350d1a41efea21a34837fcd3346907efa6668d20dff34ad1a41fde955a34837fd5db46906ff9b868d20dff36cd1a41bfe6d5a34837fcc2b46906ff96568d20dff362d1a417feaed83482ffcdd306906ff9ba60d20fef4aac1a417feaed63482ffcdd2c6907ef9a658d20fef4aab1a417feaed53482ffcdd2a6906ff9ba54d20bff370a9a41efea2153482ffcdb2a6906ff9a654d20fdf4c)) else (if i<6 then (if i<5 then 0x454a11ffe308a9423ffc6cd52847ff8c1aa508fff18550a11ffe37099423ffc6d532847ff8c2a6508d7fcb9aa982cff973553053ff6ceaa60a7fed8d54c157fdb12a582cffb6254b05bf7aaa3360abfe5cb42c167fca968582bff576d0305bfeaa9a060b7fcd1b40c17fda3368182dff342d0305bf7aaa3358a7ff5db50996ff9b06a132aff972d3265bbfaaa664cabfe5cb4a995feebb60932dfdd54c1265ffa6c1824cb7fcd4340996ff9a668132fdf4ccd0265bfe695a04cbff4c1340996ff9a168132bfdd76c1c45ffa6c18388aff75dac71157fcb969d81dbfd553bb035ff2e5a5606bfe5cb46c0d7fcb95cd81cff952b9b03bf7aaa33607eef3bc66c0d7fcb968981b7fd76c1303affaa9826079fe5cb04c0fbde3360981f7f360c13039ff2a552607df6c12a4c0d7fcb94c981cff95299303efb609326077f755444c0ffce3388981dff34ed0303f7e9dda06077fcd2b40c0eff9a368181ffb466d0303bfe689a0607dfcc1340c0ffea2268181d7fd55442e35ff2e5835c73fe54b06b8efdeaa8cd71dfbb5119ae3ef7a22335c7eeec3c66b8d7fdb32a551affb6454aa39ff6cca95473fed9152a8d7fcb968d51cff952d1aa3bf7aaa33547bee54c66a8d7fcb968951cff952d12a35ff2e5825473fe54b04a8d7fcb94c951cff952992a3bfbaaa22547bf654c44a8fbee8888951ff9c67112a37fdaed815477fb55302a8f7f4a960551ffac66c0aa3efd60981547fbaa9302a8ffe62260551ffe360c0aa3bfe68da0547fed19b40a8eff9a268151ffd444d02a3ffc605a0546bfe5cd5498e7fcb9aa9319ffb71552633ff6d6aa4c67fed955498d7fdb82a531affb6e54a635ff6d4a94c73fedc15298e7fdb72a531cffb6a54a635ff2e5a84c73fe54b5098cffebb6a131cff972d4263bfe6c1a84c75ff5551098f3fca9a2131aff972d3a639ff2a5a74c75ff4434e98d7fcb961d31cff952c3a63b7faaa774c7afe54cee98edfda89dd31f3fd113ba635ff2e5a54c73fe54b4a98cffebb69531cff972d2a63bfe6c1a54c67fe5d30498d7fcb960931cff952c1263aff6a1824c6bfe5caa498e7fca954931bfbd7699263bf7aa9324c7def4426498ffcd824c931ffb36099263bfbaaa224c77f6d444498fbee8888931dfdb4b112637fdaed814c77fb5530298f7f4a960531fbeceec0a63bfd695814c7dfac130298ffd53260531ffcc44c0a63ffc6c1814c6ffd5db4098effaaa68131dff350d0263efea21a04c77fcd3b4098fdfa7768131dff34ad0263bfe689a04c7fec9934098ffea2268131ffe302d02635ff2e5a84867ff5db5090e7fcb96a121dff360d4243affaaa88486bfe5cb4a90cffebb69521cff972d2a43affa21a54877fcd834a90cffdba61521cff952c2a433ffaeda34875ff4434690eff9b068d219ffb74c1a435ff2e58348 else 0x3bfeaa942546ffcdc284a8fbfa8850951ff7348a12a37feaed32546ffcdd264a8eff9ba4c951dff554992a37fe2e5325477fc54a64a8dff9b84c951ffd304992a3ffcaa981547ff854b02a8fff1b460551ffe348c0aa3ffc6cd81547ff8d1b02a8fff1b260551ffe344c0aa3ffc50981547ff899302a8dffabb60941dff374c1283bfeaa9825077fcd2b04a0ffb9b460941bff576a9283bfe6e9525077fd552a4a0eff9a854941f7f510a9283fee61152507ff4c12a4a0eff8b9aa931bff37054a637fe6dca94c6ffcda95298ff7a552a531dff37054a63bfe6dca94c77fcda95298dffabb6a131dff554d42637fe2e5a84c77fc54b5098effabb6a131dff172d4263bfe6dda84c77fcdab5098eff9b26a131f7f55544263efe2a6884c6ffd5db4e98effaaa69d31bff172d3a63bfe2a5a74c77fcd434e98fbfa8869d31bff576c3a637fe6e9874c77fd5530e98dff8b961d31dff152c3a63f7e69d874c7efd554ee98fdf8a99dd31fbf3513ba637feaeda54c77fd5534a98dff8b969531dff152d2a63bfe6a1a54c7dfd4434a98effabb69531dff172d2a63bfe6c9a54c77fcd434498fbfa8868931dff34ad12637feaed824c6ffcdd30498eff9ba60931dff554c12637fe2e5824c77fc54b0498fbf9a860931dff34ac1263ffc6c5824c6ffd5daa498dff9ba54931dff374a9263bfeaa9524c6ffc5caa498eff8a954931dff350a9263efea21524c7fbcd2aa498ffe98254931ffb37099263ff66a1324c7fecdaa6498ffd9a54c931ffd35111263ffa696224c7ff95530298fff0a960531ffe36ec0a63ffc69d814c7ff8dab0298fff1a560531ffe364c0a63ffc689814c7ff8a930298dffabb6a121bff172d4243bfeaeda84877fc5cb5090eff9b56a121dff368d4243bfe6cda8486ffd5db4a90dff8b969521dff350d2a43efea21a54877fd5db4a90eff8b969521dff370d2a43bfe6d1a54877fcd9b4a90eff9ba61521dff554c2a43bfe2a585486ffd5db4890eff9a869121f7f510d2243bfe695a4487fbd2ab4890dffabb61121bff374c2243bfeaa9844877fcd2b0890dffabb55121bff374aa243bfeaa954486ffcdc2a890eff9a855121f7f510aa243fee61154487fdcd448890ffb9a591121ff730b22243bfe6a1a3487dfd4434690eff9a568d21dff370d1a43bfe6d5a3486ffd5db0690dff9ba60d21dff374c1a43bfeaa983486ffc5cb0690eff8a960d21dff34ac1a437feaed53486ffcdd2a690eff9ba54d21dff554a9a437fe2e5534877fc54aa690dff9b854d21dff350a9a43efea2153487fecc1aa690ffd9a58cd21ffb30b19a43ffc6e131487ff8d426290fff1b54c521ffe34a98a43ffc61531487ff8dbb0708fff1b260e11ffe576c1423ffc2e582847ff8dab0508fff1b460a11ffe2a8c1423ffc6cd82847ff8a9b0508fff1b) else (if i<7 then 0x901400122810500ec00ca00ac808f007180540036801900005ffebb68582dffd54d0b05bff695a160b7fed1b42c16ffdb16a132bffd76d32657ffaeda54cbbfe5cb4a996ffda869532dffb4cd2a65ffb6d5824cbff6d2b04997fedb160932dffb50d0a65bff695a14cbff6c1342995ffebb5cd81dffd54b9b03effaed82607dfedab04c0fbfdb360981dffd54a93037ffaed326077fedd264c0effeaa4c981bffd76c1ae3bff6e9835c77ff55306b8dffebb60951dffb74c12a3bffaa982547bfe5cb04a8f7fca960951bffd76992a3bff6e9325477ff55264a8f7fca94c951bffb70992a3ffb60932547ffa99302a8dffebb61d31dffd54c3a63dff2a5874c7efed3b0e98dffebb60931dffb74c1263bffaa9824c77fed2b0498fff5b160931bffd76a9263bffaa9524c77fed42a498ffed8254931ffbb7099263ff76d5324c7ffaa930298effeaa61521bffd76c1a43bff6e9834877ff5530690effda560d21bffd76a9a43bffaa953487bfe5caa690dffdb854d21dffb50a9a43ff760d53487ffac2a6290eff8b9aa982bff36254b05bfe6c4a960affd5db48c16ffaaa69182ff7555223057feaeda160b7fd55342c15ff8b968582dff152d0b05bfe695a160b7fcd2342c17fba4468582dff346d0b05bfe6c5a84caffd5db4c995ff8b969932bff576d2a657fe2e5a54cb7fcd434a996ff9a669532fdf4ccd2a65ffa6d5824cbff4d2b04997fe9b160932dff350d0a65bfe695a14cbff4c1342995ffabb69d81bff172d3b037feaeda5606ffc5cb4ac0dffabb69181dff34ad2303fee69644606ffd5db46c0dff8b968d81dff34ed1b03f7e9dda36077fcd2b46c0dffabb5cd81bff374b9b03bfeaa973606ffc5cae6c0eff8a95cd81ffb34f19b037feaeda2606ffc5cb44c0eff9a568981dff348d1303fee911a26077fcd1b44c0ffda3368981f7f576c1303efe2e582607dfcdab04c0fbf9a560981f7f368c1303efe69182607dfcd9b04c0fbf9a360981dff374a9303bfeaa9526077fc54aa4c0ffba4454981ffb466a93037feaed42606ffcdd284c0effaaa50981bff576993037fe6e9326077fcdd264c0effaaa4c981bff17299303bfe2a532607ff4d2444c0ffe9a388981bff576c1ae3bfe6e9835c77fd55306b8dff8b960d71dff152c1ae3ffa88aaa546ffcd9952a8dff9b22a551ffd44454aa3bfe6cca95477fcd9152a8dffabb69151dff554d22a3dfe2e5a4547ff511348a8ffbaaa91151bff576d1aa3bfeaa9a3546ffc5cb46a8eff8a968d51ffb55519aa3ff62a633546ffd5db44a8effaaa68951bff172d12a3bfe2a5a25477fcd4344a8eff9a468951ff7488d12a3bfe68da2547fed19b44a8dffabb60951bff374c12a3bfe6e9825477fd55304a8dff8b960951dff152c12a3fee91182547fed19b04a8dffabb50951bff374a12a else 0x82d612d55ad4ead432d37ad2c2d1c2d10ad052cf52ce9acde2cc9acbe2cb2acabaca02c94ac84ac792c6dac622c4dac422c36ac2b2c1fac142c08abfd2bed2be1abd62bcaabc3abbcabb5aba5ab9eab97ab8c2b80ab752b69ab62ab572b502b44ab3dab292b1dab122afdaaf22ae22ad22ac22ab6aaab2a9b2a8faa842a742a68aa5d2a48aa38aa2d2a1d2a162a0f2a03a9f3a9e829dca9d129c5a9ba29aa29a32997a987a97c2970a9652959a94e2947293ba9302924a919290da8fda8f6a8eb28dfa8d428c428b8a8ad289d2896288f2883a873a8682858284ca8412835a825a81a28132807a7f7a7ec27dc27d0a7c527b9a7ae27a7279ba7902784a779276927592749273da732272227122706a6fb26e6a6d226c226a4a68ba67726672652a639a61c25fea5e5a5d125bca5aca59ca5882573a55aa5462528a51424ffa4e6a4d6a4c224ada4992480246ba452a4352420a40323ea23da23bca3a8239ca38ca3782363a34aa331a321a30422eb22d6a2bda2ada2992284a2702260224ba2372219a200a1e7a1ca21aca18f2171a154213b2126a10da10220eda0dda0c920b920a0208ba0772062a04e203520179ffe9fea1fd59fbc9f9f1f861f6d1f541f3f9f149efb9ede1ec51eb09e979e7a1e611e439e261e089def9dd21dc21dad9d991d849d671d499d351d179cfa1cee9cda1cc59cb59c9c9c839c739c5a9c419c319c219bf69bd91bc01bb01b851b679b4a1b2c9b139afa9add1abf9aa21a849a701a529a351a1799fa19e599c819b3999f198f197f196f195a99419924190f98f218d918c918ab989718871872985e18409823180597e817d817ba97a1979197741756974b173b171d970016e716c996b51697968316659648162a961a95fd15df95c215a4958295609535951814f614d414b694991477145e14409423140a13f593d813b19394137b1362134d933d9329130b92ee12d512b7929592781263924f12319221920411e691c911b4919b91871165113e911c90fa90dd10bf90a690699050903790110fef0fd18fab0f8d8f700f528f308f130efe8edc8eba8e988e7b0e590e490e270e098df50de08dc30db30d9e8d8a0d6c8d4f0d318d140cf68ce68cd20cb48c970c798c650c508c330c1e8c010bec8bcf0bb18b988b7b0b6b0b568b468b368b220b090af48adb8ac28aa50a878a6e8a510a338a1f0a0189ed09cf89bb099d8980096289450927890a08ec88cf08b60898887b085d88400822881707fe07e087c307aa079a077c875f0741872d0721870d06f886df86c686a9068b866e06508633061585fc85df05c605a4058685720550053b851984fc04ec04c104b1049384760458843b041d840003e283c983ac038e837103538331830f82f202d482b702998277825a023c821f020181e401d401bf81ab01968186816d815))) else (if i<12 then (if i<10 then (if i<9 then 0x3cc33cc23cc13cc03cbf84beccbdccbcccbc5cbb14ba5cb9a4b8ecb834b734b6c4b5c4b554b40cb354b29cb1e4b12cb074af74aebcadbcad04ac94abdcab6caa6ca9b4a8b4a76ca66ca5fca4fca3fca2b4a1b4a0fca08ca01c9f649eac9e3c9d849d149ca49ba49b349ac499c4990c98549754965495e49574947493bc9304924c914c90948fdc8f6c8eb48dfc8d448c8c8bd48b1c8a6489ac88f4883c878486cc858484cc8414835c8214815c805c7f5c7ea47dec7cec7acc793c776475d4748c72fc71fc70fc6fb46e6c6db46cfc6c446b8c6a8c6944688c6744664464b463fc6344628c618c60d4601c5f645e645d645c645bac5aac591c581c56d4558c53fc52245124506c4f244e6c4db44c6c4b6c4ab4492447044574442c420c410c40543f543e9c3de43d2c3c743bbc3abc3a04390436e4355434543354329c319c2fc42da42c142a8428ac271c261c25ac23d4224420241dbc1c2c197c187c180c170c160c1554149c1354129c110c0f340e7c0d7c0cc40c540b540ae40a2c085406c4057c043402ec01a3ffcbfe3bfcf3fbabfa63f91bf78bf523f3dbf323f26bf1fbf06bee4bed4beb2be833e77be70be60be553e3c3e15bdf3bddf3dd83db63d98bd7b3d5dbd403d1e3d12bd0bbd003ce2bcce3cc2bcb2bca73c9bbc903c84bc703c64bc503c373c19bc0e3c02bbf2bbe2bbd73bd03bc4bbbdbbb23ba23b96bb8b3b7b3b623b3bbb273b203b14bb003ade3ac53ab9bab2ba953a7c3a5eba533a47ba25ba1139fcb9e3b9b8b99b398fb97fb9743968b961b95ab946393ab92f39283921391a390eb907b900b8f0b8e0b8d538c538b9b8ae389e3892b8873877386bb864b859384db84238323826b81b380fb80437fd37f1b7e1b7d637cf37bf37af37a3b798378cb77cb77137613755b74a373a372eb71eb7133707b6fc36f0b6e0b6d0b6c0b6b0b6a53699b68e367e366e3662b652b647363736273617360735f735e735d735c2b5b735abb597358bb57bb56bb557354bb53bb530351bb510350034f034e034cbb4c034b4b4a0349034803470345bb450343bb42734173402b3fbb3f033e033d4b3c4b3b4b3a933993384b374b3603354b344b334b3293314b304b2f932e932ddb2d6b2c6b2bb32ab329fb28fb27fb26b325fb24fb23fb22fb21fb214320d31f8b1ed31e631dab1cf31c3b1b831acb1a13191318a318331733167b153314c3140b1353129b11e3112b10730fbb0f030dbb0cbb0c030b4b0a4b090308030703064b05db05230423036b022301230022ff6afeb2fdfafd42fc42fafafa8af9d2f91af862f7aaf6f2f63af53af43af382f282f182f082ef82eecaee12ed12ec5aeba2eaa2e9eae8eae832e732e632e5c2e552e49ae3e2e2e2e22ae172e072e002df92de92dddadd6adcb2dbb2db42da8ad9d2d91ad862d7f2d73ad6 else 0xc7c2c52a05008118e508a614c87712632985a81b0f98715430b94347b0ed8a86172860f2600994a831cd1ecc616a0c7ca191694a8615b05830500e0bc2878d9083b8b0b0b2a7b2087aa616b0e23e1dc554ac617206ac6410a0a202c3c07c85630a0a3e42b0850510169e7121f0b58c81e1787715630b9036428e041c180502110630a0bc851d39042810790a3c6216e2c29a45476a641b185302e8f22c83630a6c851c300bb1614c0b0f51f2158c29b20984f22e8ee236528ee2cc617206a3a8b2185459745476a615b19032530aa2c83628e6ca68a8ed8c2e40c07110630a1a009a359083c62a985711e3507aa48b21856c1e45180255320c730132018aa616c460207aa990c2d60c1e0c012a990a3993d9043a630b54711f0f9871616a99032890ed8c8616a86d161db185aa640ca24c0132154639b4598c2d518f9034430b581d610b1005103d85715608e2885630a4885630a30502f0b106a15a985885609d0ec65344022f43b145ca51dc46eb71fa9c5ec078dd4f1642b0022d5ba990a2f628ee23f53c545c851db06ea71721d8a3b88dc5f135321476c1bb1c5c871ea8e2378bb0c5aa6418e6f1717b154c831cdd0ec65344022dd3fdd26dd125cfddceddcd4dcbbdcabdc975c875c72dc5e5c49dc355c20dc10dbfc5bec5bd35bbedbaa5b95db7cdb685b585b43db2f5b1adb01daed5add5ad65ac1daad5a98da88da78da5fda4b5a3b5a26da0dd9f959e4d9d059c059abd992d982d972d95e594559355920d910d8f7d8ded8ca58ba58a5d891587cd86858585843d82f581f580ad7ff57ef57e857d3d7c3d7b857a3d793d788577cd7715765d75a574ed747d7335727d7135707d6f7d6ec56e0d6d0d6c556b556a9d699d692d67e5672d65e5652d639d629d61e5609d5fe55e9d5de55ce55b9d5ae5599d58e557e5572d55e5552d542d532d5275517550bd50054f054e054d054c054b054a4d494d4895474d469545954495439542dd41dd409540253f6d3e253d6d3cb53bfd3b4539fd38fd37b536b535fd354534453345328d321d3165301d2f1d2e1d2d652cad2b652a6529ad293d288527cd2685258524cd245d23a522ed22352135207d1f351e7d1dc51c7d1bc51b0d1a551955185517e516e5159d149d13e5129d122d1175102d0f750ebd0e050d050c4d0b4d0a4d094d084d07950695059504dd03dd029501dd0094ff94fe4cfd04fc94fb4cfa04f8bcf7bcf6bcf5bcf504f44cf394f324f2b4f244f1d4f0d4f01cefacef3cedf4ed3cec84ebcceb14ea5ce9ece8ece834e7c4e754e69ce62ce52ce474e374e274e174e074dfbcdf4cdedcdddcdd24dcb4dc44db8cdb1cd9d4d964d8f4d83cd7ccd714d614d5a4d4ecd434d334d2c4d254d19cd0e4cfe4cf74cf04ce04cd94ccdccbdccb24ca6cc9b4c8fcc844c78cc6d4c664c5f4c53cc4) else (if i<11 then 0x720d8a39b21546c1088622c6428f54021b2154628108e22c1168f54c81ab145716428f54318aa845a3e41b062a38a8e36c6418b547131cce2aa31720d86399b0c5c85518ee233898b54c831db060ef530f90d13628a7047630f906a68a8a707740301f04e518ba204272810d10618a1f374085d822e53441f3827a194d17628a1f39148594d10243e6e876329a2a287cc1f00761a1a2ca514e02ca6898a1f28778ed8d15143466388fb1a2a2868dd862d1c3c1a2a7b45474d13a1d8ca38a8a1f307bc587ca077a0d8a2a0121f686528a043026c5946287ca09ec61f281e2b16c5504b918b94320cbd94a81909d0ec51f28e2e29bb14771651a1c5371fa9d80f714a0be3801b1450f1817d463803b1450f1c01c7ec3528a1e35518b584f11160762a788090007d8b90aa1aa8c54f0c01c7716628a1a3003c4c7cc5143460071f21626282cd62cc315344e3e418a0b13168f9862a689900a01c459862828e000a71f2198a2f881480a31c4590cc08e8a70071fc598c83528a74a28a8f90cc314c87515532198629b8e00cc3143c5048090404058884a86ea76320c511b720220c314085f1643b14502141790ea61c01d8715151870078809906c514fe2ec3532145021817d4c861c01d8b131509862e411762c39801e2c3e418a0b32898b54c85630e6ea7880187c85618a7f1553b19062810d90aa31408402653c59062f6002702763200eca38a8a7ca003c404c83628a7f17632194a2810c00e3f632194b1314f6262a68600f171f2990ac314fe2ec65320c5021b299062810810aa314cc4e3e42a8e2ac714d906299864bc8314c8425e42b0572150c4c5c85628e6ea38a8fd8c8714de2a3b5320d8e29bc5d4a3e41b1c53010979062d52c46c8314963c85518a04271fb190715538a6f171ea9906c714de2ec31f2154e29a20d8a3c78890a3b613c4ca51f44d8c2e40d54c2b613c4c3d5344d8c2e40ca2aa31d3c4cc31f4554c2e40c9ecc616a8e2c39b0e98aa6153c5cc615a1547161cd50c381060aa85630e483d430a3a82140837141ea185241db0d4a8614b5083b630a40241da950c294041e83b8b0a50121c0850aa614d94a86630ae2c39b0ea2a8615165d1615a9506c61cd94d1616a0d8c39aa0876c6149a2cc616a0d4c39ac5944287c81f0f0630b62ca1ac5944287c89ec3d61c585ca19a087ca616b09e361eb0e2686172860140844180f05cd108c45f28e2a39a311771651a147365245178f3628e6108043f94b151cc1ea3d6002212a79301fca38a8e64f6630ae2a3e50cd04c61729474f1b3185713428f94364344d8c2d1f286c282c50b8a38b0b582c2e28e268616b060088416c7c2c50d0b63c530b582e530b5018083d50c2e50146008281750c2a50c0b0f652a18502180994c2d409850d0a3514a86148d8a84530a48d3622950c29408 else 0x824235321241e5020c7d10603e6ca01430d00f948b94d107c994d107c794d15143e40165345450f95a0070c68b294532693145ca51f44603b6345450d1431a2a2c68818d131c344d131e343ca51c3c3ca61dc41f2651c5870f90201eca61db05ca61da004207b2987b10603e6c3e52c41f20630f940f132898a85892e5b15412e3c3c52c41f258a29870f9329452119080b03b603d45286016c70f100e186a07a8a5ab6890f54ac278d56aa5613c4a2e8aac8ba3a78c8bd12628e9e2a2e8e9e1e430ad4a3b634460fc7aa99025503c262d5320362b1ea990202c3d90ac103e1e2a51f205d12610f544f158b544f0f219862d518fa2301f2ce2cc068a22cc31c34403e5ac59005972c8b4d0c44c5cc2688c5c8588164a3e61169a251f309a1e428ee245928f907122c9900a08b30c7051b2007113501450a08b219863940ed4116433145341e4598c83528a621753c590a3e60c94515168f90cc1b44d4a2d1f219832143f47c8660a1fa3e433040158b300a0f97301e102a3d62cc118b980f0d8ac7cc5888c7cc58860a0fb50c598282c3cd4b1132d90432088e2aa642044aa6410c8223893154c8208b9871616a990c39944d8c8551045aa38b2082261c30e202132022c3b600856a64045870c010c1805e430ee228504587c8360b1491641b1872e1f20d40212481e8f014319005e1ec490c02f2187b1150a98b122f0f903263208bb161ca22c3e40164c85530ee285954485ac642a987328b0f54c8560ae242d630f54c81b0ae2ac61ea99030080822c85630e60208b2158c3941787aa00ac404361f21541e42a9070212a99083810954c841c0840f810a907c8388d54512632187021aa99062810998c2b8aa987c8193c856c6430f54361c3c20247b0f622361a987b111b187b10c3e04c3b50c45020790ed4b115a987b10c0ee20c51434503889b1450d1431458d0d8e1a020e341e8f0600b9001652c49016403194b1314c82b12610a9a28898a9a1c68170b11016b002c8651202116532158629a0f90ac409c59435880f9401642b0671463299081154498a2d1d345712628b94a3e40d90cc515c547ca1944d8a2e428f9436504547c8060086a3e532004240b2118a3e51c46016403147ca588c02ca08a8f90ac194498a3e432804351f2990021004a26c6428f9436528f1002128f94880109947151c6e2a3e5075621190790ac134844c8151c5582116a990a2b8ab1473641c5582111a990a2b628ee2312f21622c190a4bc8190762a2b5320d8a39b21582595c990ac15c7907151c964c838a8e4b2109c4d4a3e41b06239632042aa588c472c6418b54b11ab19062d518f623642a8c71d628b9063d52c46315608f9025958b90258ea96262e418f58310ac554c831eb06715605902115c74771162a990211ab190a2b8aa9473550c5906c108b54b151)) else (if i<14 then (if i<13 then 0x1eb0351086b030787ab030d560487ac0834c7143e3d58183c3d47186a8e207879b034c51c50f8f51c68f63a7878707c086010105c7070bb88617c3b887178161c61f0158b0e40fe1c562c3883402a861c850c3894882c38d48d0c38c1402c3d40804c388c587a80ea18711410f076c12a18711630f5019430ed41812058718083d50c390a187121ea02058790f50240b0f501950a1871c0b0f5018681754c390a98710081650c392050ba861c8503161c60aa800b0e4c386a187102aa1871d40142815430e3311630e301010402a83886240394004401441a830bb600f502441b0201541b030141ea036a0104040141ea0401441c43883604040161c604c38b0e11200b0e38161c4170161c68705894882c38d2e82c38d048b7161c882c38904e2c38d2e82c38f0ee2410d17876c0c3962107c21c0087ec440fb1c4d0083ec420502c462ac0a17581342b0285d6042600d607580d602260f54061aa808021a281608e20a69a020151c462a38a2f4713428e28bd1c4d8a38a2f4710043e02a3903ee2a38da147151db021341db031307a0ed02011a14718900347187e8e2a386494710928e5e18068e200868a14724928f1e18840358191eb0203d60421ac08435810043ce21885201eac12b0123b8845871083ee21269a0245b604a66c094cd84f0d0ae2ac0dc55813410b581869a1581a158f58185d8f581b8ab026856048505d60601a80a3550100435501c6aa0200a16a038d54041aa80046010f5407500d40201a80a3d5010790b501c7ac424c58840a00d607580d60201ac18860aac0ab010580440a42d607580d601422c388401020809851614201710809851414201c28a0a1020045056c0804e21440a0011806a020086840b6c54061e7108020410180404009004e21009b02008516d81005c420081808300b884016c08381e10700d620f12c4d81362c42b131c4d4b108241a1069c428346842603588658b1093ce21161c4283058e16a044206b10ec41b1053ce2100a8e20251c4e2a38a8e12c51c54709628e2a3840c040151c8e2a389a947109817076c11b14710860ee21811a94718840d62191ec421151c42105d1c706a38a0d47105c0d4718690c20312c41705d1dc448342e8e323b884210351c7470d1c20671084347710e0d47111dc422c38849e71090c9a121916d41a182867108021aaa0e35541006a828d550454638809541388254008802e210118e20fb1c40163880c1fb10ec411155041faa0a0d54107ea8c7191ea828355040605d507540d50206aa09440baa0e0d54102d0f5419518e28356045871080c04a38c0947151c206a38808a2a38e0d47101a8e5818128e28351c44771093ce21218286710808861219c42433604858c38861e7156068563d606c7ac09c5581215a9581869a9581b52b026a560414c83604840c641a else 0x450f883fa21689a02c82693c3e87638a1f205c3e2c3d898a1b22170e97198b0e5e62c5ca6291090f07148b0e20fc1dc4383b88517c38b0ed8141d0ee218130ed01916c4641d88c82b1190bc3d11608f1e00150ba24f0f8f58d10009d8a3e8800462d60af900a968e0baa316b09e36410a9e1e17442c8314002021522824844059062d504042a4522038a64054704316b09e282c969ee3e42b1c53812a99062880a9eaa3144040f7604054a3e438a742e893c3c2e884a29136071ed10b44d816898e28f6885a26a09441a0f0e3da21661348b18681794a3e62c413388ec59862a68b984d22c69042a2c785cc09208b510cc598a2e40140036428a6223e6014003a618ee205000ae24c31c1400298b30c5c802800662c62c40a00172085cc0f301311508f9005000d54b151c1400288c159862d52c40938028e0a0408d8b62cc2320c5cc01012505002c59812813215462a72085cc0f301c8617303c8617303cc078562cc098f98b1000962cc0815c73166000505a2f8ed4b1000d62cc083d62cc0c8f45166020b4c5147980a61c4203013200201800c864101000032b8bb1c50213c4d8e28109c5f1760084a2f61c400212f2145f1360006c8517c4d800168bd871000945f1360004a2f89b0002317b1620011b15862d880050e82c3c05ec58b0e0046418bd800118b9012170e2c8072158f1314005aa38ac4c5c856000782d521630202ea990ac3144a700012c42605b16a990ac61d485c3898a1a2a890a3c3e14590ac7898a00292da954715898b90002017d4c80143b87001fc5d4628748c5087405d805d8b8a04388c0802aa314406025618b54b1020c20ec02cc587001801a2c3e418a4b3013215462d8ab0083c500820204a914176000202a38b8a6024518b902214082a2a890a3c3e14485c38b0f62158b0e26c61ec400258b0e26c61ec4002083b062c3800a040f717b162001ac587158b0e205010043020170e383b885070c1da8283860ed810120ed4181da820241c50743b88645ec71ec40028303a1ee3f638b620023b1c7b10009620a153428d314000c24681794e3f143a0c3b143b1aac71cb05ca0ab010e8101c1a4d714c04075618a9a288235c5ec01000662c1440462881c1a0c08135c5001c3594628809474d3144040d51f8a9a0e940194310741c1aa3e418a90e838096262a68c85020a8aa2428f298512172820204081ec38a8e0026528e223e504e20c682d808118e28d058e1ac19896322d60cc333560445a3990747a288c947151cae4b1914962a2d604622591c645a38a8e1c2914545a389c5471288c4581b16b02713144c5710aa8451550354a288a887238ea9451550245aa12c7852a114745aa0aa8c71516a8231460b0325d60445a395c785228a8f451260b00a1d1c1423141c8e32bd1c40171098e0110058e21083eb03108) else (if i<15 then 0x630e31205c41e6861c604a8083404a80c0811306a3d9026418a21082a3d9026418a2120183d90a294b190a28d3d90107c091ec81320c5124220476c123d90111f20d8185c3d54c810a990105c3d90aa103d90102d3d541a7b2020f8123d9026418a22c642a832a6418e3aa640447c855071ec8083c1f16418b541c51b1901888a81e1c518f901888a81e1b1c3e22a4883c35155040b0f68aa840f55051eaa68871eaa6886170f688647d1082e1ed10c081ea3e889a20d1f4420207a8fa220134420251c4c7d1098fa210681794a3912822a38c340ba3e6081a05e6061aa38a0d98102b3145182b31451d173020504159810373006a3900407cc0c8547cc0e8f98126b30210813314720280f981e618a20505359813173020d6601754202829981e618a2aa06a8e2111ea82aa660447cc550754cc08141fb1660862cc09316210283f62cc103f98107ec42cc58841fcc588617cc10879808082f9818288f9821122f98810c159810283f47cc133014c51c40a0fd1f3040566040aa3881598111f30e2187814262c62c4363d8b3038c31ec430f262c438c58841eb16606988c588718b10a3122638c0c02b161c887b1080d62c3a0881fb120861f4386ac440300b0b58256020601616b040102d4558241a0585ac103558710f0a58710d0c82628c8ae210128a2025145450b8820408102210f588604b1098a1b10442040f5888c5b109a9621362c426a5884974d098a10b86aa83025504c50d50354710aa8113588963025884041358860405d8860405d886042a58869e43898a17104420aac0c300413143870961c42ac04420a0261c8c50b50254710aa810255041f02588762088aa820f81040202550604081021faa0aa81f101017541d5035408101754192c20baa0816a2aa0e17541012a822c3885140209c55410102e26c5504e20b6021e020a0ec5b10db162c38e0ed4b10db162c38db107b10ec587141ec429141db030fc683c362843e1a0f5888c5b10ac4d815898e263d8840a8d02c6c50868b0e21d6020a0d02eb04ac31455871098f58131eb020c5884210d58861ab1080c17a38c8ee2151c2476c0a8e11200ac4323d884240158862401262c440680ab03ac041a02ac0c041a710c1a02515609028d56065871093414d0534e2111dc42a3848ed813882d8088435621d88362088435621886c4210d884214c5886210d5607580d602210d56061aac0835581069c4210a8ab038d5604587109b014d3884e2ca09c54713632826c51c5946c09a94713528e232550554628aa8d815518e226d518e4225518e2aa31c4c7aa08c842715508c7aa08c8e2aa0cae42710caf54115ea822bd51c43070734401ca07c10707653441f04141220d17638a1f308345d8e287ca1fca5144040fd172809101728850f8f28c5100f45946288081c0f80744422e885 else 0x6810200f10401a9102000504488001a2020402400104820040c49172282034510c5c8a080594101fca0c3f1404388914043886080a4883e40f85011622020c4200f101020000108084a00008404081c430a80097a220013c151820401e8a000a000f450a840007a282020790a00aa10001ec8614405002410a20207840001e17301300103e00429908004284d164c861730090014009042a608850480061f087412c500130b98048108000221530442824003048018a3c8617300900172185cc188800cc588625c3800964020510a25001400c50212c8042a61c4a4c2820081f208841c51d14461f02103a1fc388c0050421c4030e92c103a28741754202e8aa20ed50a62040746200d3142e40d3142e30eb170ed4b114421a42d16c451086b0a20208841c518843545101042850ee50821ca1143a410d168e1d23143a2118872985001042a200038994c298879462b8a8e4ca31441fca51461f08902f94a29328050f8d3d94106b281ea8103f94a80f28c51543282a8360550638b2950111ea02680449170d61c9876288438705d6098762884987ac0c4958161eb02133))))
def gzl11 : Packing := (1329,3,6,0,0,16,0,gzd11)
def hashgzl11 (i : Nat) : Nat := (if i<2 then (if i<1 then 0x18af40ea30dfc0337d0118c129d0a850436c06ee81706136780b5906ca463091497849a308e040ffa072342cd910140566917f0037df0786c06de0bd6c6b5e0382e215803e14059800f3472e505ed4635d04b7c2c9f05728420b0e15856b208fa42a5a14ff42e1a1be9c00be15a680fe718054558a0af444e0a183ac122000020184618f7414810a1b82698689bc4d516d860440b0374000050a64000010e73417400000453930b5942d8000014309a088c000000001c42c00003c455808180000f08028379d08e68245b0e45c0b740070413510ba18631908c34202f09800090702b5454c28681801bf68dc000061cc6041a00493c20a108850326308f10284106a4010a90e6102168032d827f703b0821700001800fc09874553e0222c23a00000000010481de3750c41079c31e20053a00003c34fb0c39418940c0c8393d00e1864c401b980ed8156746af303a041a410c310737302cd832141bb242a7888ac826f915a2055ff085140b1fa59c041550e3a81d1f017e82f3e0a5a805c317168048b0717c1d2636dcc068c673a428b51d9442cc7451001c370465836f5096006e9e0239864bd05030287e0ae2c49dd183c461960e10c36790d5c01b0e15498246a0d6e875870ea38025e1e6c4081005a6c39f20c28411d510e90362304148087c0449c2d9607c882c2a099b0389507d482ea3098943a6f109f833d70681c33240dd0008c602d90054a013e8298a059ec643e181bc17dc126547129011241607019b403ad0c2e436c20e1c8273d08f74231060000130601011206011105010414400408151a0b000437000d0b000019011e03110819040c173702026b1f3f0022000b0a010208061c0b08020a1003020204080b002d230b01041223091f0a00364a1e0000500f081206053e040801100e0006020a00670a4a030506010601070a0719014c01020200020300000305180e021311040102170105d500041a0b16031e0e00070000640f0405010223083c0d230629020600000700461b292e4100060026001b0900000007000201000b001904003c003600021b020f12015d031f6d01270d00000059020e00120114053a5b0a14003a0d0206050f2f1409030004060021020921000d16010005e000000002000905080200000b02000206050001040a020a0000020009010c00001902103a03430008072c01200b1f2c0e01050327190a0d1800360100280b0004000000010303011c1e03324b70063b0c2c00032c063d002a0000000200001e120102040e020006000402100e0003080101210007191a2a00060302280317010002050721001301060406041b0609060903096600390600003a00000c014101090b052e00000c1f05040808000800000c050003012500000201004a034c022c08000400290c3f00172d13260b08011000000101 else 0x831d0000207014100940eb90c72836540d10c1cd6059140650108703ab808dc40c620b9701ed222ee2213d10bd031890143420d40e4a807c2039e01dd51e130060c061fc2d5c1063824a706b5022bf07dc874dbb82e05cb00001c1dc61343c07a90aefc388b033d82e290e5bc2fb0182687480043222377108ec4daf0d2e476b305458294709b7012c7861d02b211dd10252c890e0649e0c44820190ae706bb113f48136715a800005075240fd501600000002e80000d0456009891bcf01fee0c6e81850000182650000340fb00000c37e00001436ea0927823600003c340406e7009b003318711005b2c285c0e33410890323860c6087f863f9144c000018d9841132015d476a2005140ce00000411f40aaa42bc8038e861c7116b01d3e134b831900003024dd101983a5a0de9c28140cf1412180cb4000060e5c8145204bdc242d08d2c6bd005784430a0d400399d002b0197818d00502b06ea40308037c014aa0d200000c0d1940e99097c000080ca50008a200c0000d05dc8341f02004650d041a4009404078b60b0ce846130020e0168f181d861e000008333d00180000c03f04768409a0000000604027e00003128fa1b8400000000384c272825ea5210904000040599c2ae00003c17a00002410f40b3c00008069641b6f07940000702f544f90000145347078047ab000000000b060f46440000081ab70839c31290a7f86410000000009073b1366e16f401e4305a800000000243aa0027247991a6d4043d7009b0146b13a0c18da18fa44a540e0d41d06049b831e213fa00d500dce007bf005b424040ceec1fac04f80467810cbc66070039435d201a9c190502c380caf038a04c910055808df1641c64700a71805570aeb0002e00b2424e0a6c5804211353c342c010f807dc06e282a47134642f7000038327815260404f08800004e113402d2f09b1022fd7bc4007260a0c42caf0d4e81b7018878061604798335f1518013da01c284fcb1241c0c4703eb456200000c12e200d142ef00000035e10e85c7040000182ee2140545bc802b3c0ab344cc00d3718edc34da45eb019900000000031d580000613580000000034076014e342c3804e000003012b46e80281400008062c0000208704381b05d54514a0c6b8575710954100409c0825e028100000d096bc0da00001823f507cd02b09036c81cab05fa055e0000000000000282bfc0adb02eb507a18545b18a0c3a2e0bf4c6f8e0cad8137a0bd3c02300ca8c2a07096c0000705fdc01a614380000f0638c1c6616a040ae00001c38a806514288d0e0303acd07d384c10000000002170c00004139c0000d02580000018be8094b04fc0000000000000208cdc29b000014056a1ce12a53006f14360910cc03054089bc211a12fd02032178c0000c0b50412520301c15930b05420cc4a3bc13ac) else (if i<3 then 0x2100c832800a3e8003000000000413324256000002e05918cec2db40aaf072d5041e010400000062e0000344a600003422e401fc462ce03d84024c00ee01d7b0e9241024017ac16f903b84447000038648003c80000b068c0000302d0812bb0116c4624053d855d003c00000d0acc0000505b4861d000000000f19900000000000000f007d46b6709c40141a06f7843591eab0264e696100be0000381dfa0a6bc2e300000c30000001c4ff614d80000a0e6c000080be5c20951d27402811287c097c09e0e21400000000011249c022b0511c62a61b99463200001833600002027990e080149c12c740b29069dc6c740bc700a340bea00a8900844370901fac39a81659c1b131e1bc0c520132428c80c21808b1068802ed01c21403331c368093d11a0450590aa00208802a601556182842e6908a4c5e520e510274c15500297d18954084817ad0503b1780869be0034c54a6357d43552084d89a0f0810408ac086341aab0857621981719006c11413833e8136342f27030ec36100538036db097280318067fc0a41193e429e10a46010900003055a802ec0000000000000e07a98255b1d7fc69cd05c9864e60d5bc0bc90d9ac2fed18e4c1b4a1d2d827200cbd041e3887440aaa59dfc1ac918e20157a0a37c289b18620752a082c000070d168414b0074455cb15464053909420778410c4c1344145f4a2bb103105e440654818620ea78354e098ec0a5688ed051c300338369112bd00a7414f5828e328a146eab00fe45277006400f900b7c0000c1c1a82e0f04c682c6403d10306d262481cb1182240d7e1dc484caa05cd80c1612f2877b308b64624313e040642125085ea20b20410b1045f4a06f03514277f070700f1e01ac475b90a9a51b6d04ee41c420459863670628c254f046f9ae41171080bf209ef038bb000504563076f4339f03491b77a013905646012c438f40bc000007064e821d9094482c5b056f019a213704210609f08696ca86f41ff811aecd6aa1db900f300000005df269c0000d0d44430d80365009eb0c4e04cb901a6047a80d2941b570d338110855ab832500c5544b34081d844970b788359c3d8780a63018ec2a9462ee828a00001c33ff19088535d106c0000000024092b091fc1a8000001e46e010201a1000024219688a341f0f0468000000bb1875d7027c42d1406bdc426c05e280dec070800000155b8179900dc000000003462930dec417c30930000030b11041d8036000005166702e9f0a7502ad405534227e0043821a8285d825941708c1ebd2918000090c8043634173ec26ed1bd7c052403400000e086f83785057c427650849c64db07894304510b4037600c7ee2263178404196562704e9d00b50086f156fc295819140123b07250428b09238371b300c0000388ea4702f192843020000005f600000 else 0x2b5d07f1055530046120500b1d42d0402890338e04cdc42ea083d470b20ad3c26ba0c1e439ee00bac1e910d71845cc0cc24162c058d86b3e0ade00e171703079d6155f823b00002224450268c463000144439b0287c1c0900e7036bc1070427a31d89035f1073001d9e004b06be31dbc82be719b5c1d820660468d41cbcc4e100b5c81144140341c7c0b9307614136dc0e63261345637092fc2c03669f02ff6023e837200b9f425d70ab14565e0280c349207e2c324a16754085017f74079804e481d5300a60161f00fa05fbd10f94368706760049a134d440730e9f00673040c0132e0347c53730390c1b3400cb426a60e80c0c990c8d85611018b4188806b8000090dd5c42a00001c19b815040343510de007441afc416b0000203225281fc30151141c01e30da8c15ad0d39c2af11d01c19ed0d60000000003c4224054d0142718404442c0532470371a53a933d07d86a17d08b0425731834402b405da00d68014583171282f054fa02568165004a8c6f030d4b01d6a00f6c282f0e8e1a2fb48120377d00bf622c0000081ef20308000050e19810e505b942dd0000140f530e75c506504a2459ff1945c05ad00d681f93088a0db4a152d4196d0c598089f054284bd705c682dab657c80ef802e601fbf031c0047a0a8f815dd0ac405f300000ca2f108d5053e5054a41ec27bc2c25330be2802a308aac147007998547e0602465dc137c8497704f2c2ce00001c783e01e3c627c0bda404de060b872820b4d0a3be099e830f30276c11c30267c0dc2064b41e32124cc24331802e21bf0e37437c608a00000000008111e09f44156a063c4a1330b2f0550318e9818ca103941cf40a4241a6d0395c0b8c03df03475093f045bd01c6814bf1120848e00001808221a8f028000002054e0010400910000000000000000004079e423290003036480cb886110000081ee2135f01da2004f8027418598017b01dec39050670000091bbb414320cb004de51582c14dd17c82205b02bd010db0a4b8275f08938205301be01917056002fc603368225a0080c1be60c53421ec188f01de788bc433440a4dc1bf000039180d5551805bc00db620be0d6b8b7711300194420b7105483049f43957006202a201a8b40075668341f15150340738759f4572101d70707c0460413010cc4000060913c6eb0000141fd))
def gzd12 (i : Nat) : Nat := (if i<2 then (if i<1 then 0xffe50981ffe4c981ffe60d71ffeaa951ffe2a551ffe69151ffe68d51ffe68951ffe60951ffe50951ffe4c951ffe60941ffe54941ffeaa931ffe2a531ffe6a131ffe69d31ffe61d31ffe69531ffe68931ffe60931ffe54931ffe6a121ffe69521ffe61521ffe69121ffe61121ffe55121ffe68d21ffe60d21ffe54d21bffaa963bffaa982dff2a582ff78cd82ffe68182bffaa962fbf58d62ff78cd62bffaa932bff6a132bff69932fbf99932ffb60932ffe68132ffb60e22ffb58e22bffaa981f7f9dd81ff78cd81eff60981ffb88981ffe68181bffaa971bff6a171effa2171f7f61d71ff78cd71bffaa951dff2a551ff78cd51ffb88951ffd60551ffe68151bffaa931dff2a531bff6a131effa2131bff69d31f7f9dd31bff69531ff74c931ffb88931ffd60531ffe68131bffaa921bff6a121effa2121bff69521bff68d21ff78cd21ffd4c521ffe68121ffd61e11ffd61611ffd60e11ffd5ce11ffd54e11ffd60a11ffd54a11ffd4ca11ffe54d60ffe54960ffe4c960ffe69930ffe68930ffe60930ffe58930ffe68530ffe60530ffe5c530ffe54530ffe48530ffe6a120ffe69920ffe69520ffe61520ffe59520ffe68d20ffe60d20ffe58d20ffe54d20ffe68520ffe60520ffe54520ffe4c520ffe6a110ffe69d10ffe61d10ffe69510ffe61510ffe68d10ffe60d10ffe5cd10ffe54d10ffe68910ffe60910ffe54910ffe4c910bfeaa963bfe2a563bfeaa982bfe2a582fee91182bfeaa962bfe2a562fbe58d62bfeaa942bfe6a142bfeaa932bfe2a532bfe6a132bfe69932fbe99932ffa60932ffa61222bfeaa981bfe2a581f7e9dd81fee91181ff68cd81efe60981ffa88981bfeaa971bfe2a571bfe6a171efea2171f7e61d71ff68cd71bfeaa951bfe2a551fee91151ff68cd51ffc60551bfeaa941bfe6a141efea2141bfe69541fee61141fee50941ffa88941bfeaa931bfe2a531bfe6a131efea2131bfe69d31f7e9dd31bfe69531ff64c931ffa88931ffc60531bfeaa921bfe2a521bfe6a121efea2121bfe69521bfe69121fee91121bfe68d21ff68cd21ffc4c521ffc61211ffc55211ffc60e11ffc5ce11ffc60a11ffc54a11ffc50a11ffc4ca119ff2a563fb799a339ff2a5829ff2a5629ff2a532efba2222fbb99a22ff38ce229ff2a5819ff2a5719ff2a5519ff2a5319ff2a521efda2211f7d9de11fdd95611ff58ce11ff988a11fbe59560fde95560fbe58d60ff68cd60ffa88960bfe69930fbe99930ffa88930ff64c530ffc84530bfe6a120efea2120bfe69920fbe99920fde95520bfe68d20ff68cd20ffa54920ffa48520ffc84520bfe6a110efea2110bfe69d10f7e9dd10bfe69510fde95510bfe68d10ff68cd10bfe68910ffa88910ffc54510fb699a33efaa2222fba99a22fea91222f7c9de11fec91211ff48ce11ff888a11 else 0xf6c42ea5123c8227b631e8a155240eb3b10ba90e3c659d885d46250873ec7142e82a439b881f63514214dc5b10ba8a10e6d8c7d062948536c63e83142ca1943631e165078db18ec50aa1286c7e258d0859430b8f6c7123e84a42a3638a17411e50c298e17c5a10ab07e2d8c714501a853f16c63c2a84a18782f1f618b52164118fb0c5a90b206e2c785900b2f163aa42ac48182b8b1f51624214fc58fa90ab12060be2d847d490853f16c42ea23c818078b631d524214691c5b18f0aa9206e2c7d40a1058853acec62b16a43a81f6343171d8a50ca3b18ac58f28a07d851e245d094473ab7162ac63c82a1f895b611752411cfc5b18ba9208e6e2d8c5c75490348188fb71e9a3b4c72c8def1aea342c6508c37171a2c8c54489ef128a236c43087c70e5a1acc32c85df0a4a12ec22083b7061a0a8c11c819f026a026bff07f76fe59fb0bf347dfefb49f4ebe687c76f7f9ee4bd8c7aaef409e66bc787846ef39dbcbb44763eeba9d5aba807476e799cccb94471dee2e9c4eb8687066df79bd4b77c6e4edb49b52b6786c56d7f9ad4b5546a5ed389a4ab4606846cfb99d8b374667ecc49966b29864b6c8b98f8b1b462fec50987eb0c86116c139808afd45f3ebda979eaef85d96ba19724ae0c5baeb6896b2ad4059f6b339644ac54583eafa95d6ab705666abd955caa8c549ea8494eaa99052a6a439470a89c50bea0893eea7a84ee69cd937ca6a44c9e97e92daa5784a46933924ca44447de8e691a2a31045a68a59124a1f4436e85a908aa0d041468138ffc9fa43ede7cc8f6e9eb83cd678d8ef49d943a8e7468e669c7838566fd8de09b7c367e6c28d6a9aa834f66918d0899dc334e65a8c9e990031866218c2498142f9e5e28ba697182db65a98b3c96442bee5708abe95402a065338a4c9464284e4fc89d6938026964c78970929c24ae48688f291b022f6451888490cc212e41a881e90001f863e187ac8f1c1dbe3a887328e201bc636986b08d2c19de32c863a8c4018062f185cc8b64165e2be85628a9014c628984f089b412fe252848a88e0115621f8420880c0f8e1e283aa87180dc61ab833c86440c1e17682d285700a5613d825c847c088e10081e683a006d60cb817c82bc050e090810681d00326057809080e4014e01a801a8000fffaa982fff68d82fff68582fff6a132fff69932fff69532fff68532fff69d81fff69581fff68d81fff5cd81fff68981fff54981fff4c981fff60d71fff68d51fff68951fff60951fff4c951fffaa931fff6a131fff69d31fff61d31fff69531fff68931fff60931fff54931fff6a121fff69521fff61521fff68d21fff60d21fff54d21ffeaa982ffe2a582ffe69182ffe68d82ffe68582ffe6a132ffe69932ffe69532ffe68532ffe69d81ffe69581ffe69181ffe68d81ffe5cd81ffe68981ffe54981) else (if i<3 then 0xb120a98a8e2d4479058c5363ec482a3162992f8b1d52416314eafc5b08f20a98a7210b540f1e85905847a25078b81058f2a5142c82c283d62605c7a1689511e4142eb0490eb2c4a00485058176287540238f8f282c4c0142b12a43a8696260087a158951421d4a8c4b10ea0046021a541e58988550628750d3151058142ac282a43a828698a89500a1d416215404c544b130350aa0a90eac7d0d862948530d63ec3142ca281c2f8b1e53421560e3c8f0e4c0328c50ab09014787261e586285945050bf16c23e84a429c79626090051d8a5215202b130483c8ec50b28a0a219001624758948540d4a284280940562611e1c798a16514140214c5448f0eb10aa128a01041e6258984750948550d238f2c310319891c6a41516018e4c8f0e0c16c4a90b20b0a9058060a223aa4a10833142ac4825891d51624018c422ea80cb0c50a8f2091762a2060b47588590545312a4a108342ac4823a46952401804a0c168e3e14c50aa92090a1762a2470b588590545120f4c050ba3c2aa4827631752647890db1a88b3320486021fd8d0c5c7a294463ec680fa2d14a1f4361168a511cdb18b8f223c346d8c7a2451a2e2ec23ca0f1762474388085cd0fa1b0c52804694d8c5d0e21730f6c6822f10b987f431762518a1cf8bb1290e3c597c5d8509462873e86c628f8a31439d0b43611651891cfad458fa98bb03c70bc7d8d4451e34f2b62c863aa2c5122795b624117511e8913db18b45a88f2071ed8c5c7549034f6c62c863aa511f8b171e582c68dc58f308a34596c562c7900b34d4b45e2c863cc314a245b171d8a402cd35178bc531208f28802e2d40ac790983857163ea4c48229f8b5116411e60dc58ba9208f3061ed4c5c798623716c036a4b48011e5b5243618808d2d05a9210bb0c50e8e2d490580228b6a6c3148011b8b61524008b05c5b10aa9210e70b04e2d8c5d4908740582716c22ea4843a02f63158b521e40fb18b21a90ec46c554e287900b362f12c4843aa1b8b175162421cdc5b18a080f20a8704e2c5d890548738f6c62ea43b11b8b63171c68bc5b18e8a34502d8c562c794903cd6c62c863b14a1c0b8b15631e4250fc5b12128045e2d84590949a473827162ec4a48239c138b176242511cfc5b18a08208f2875642d86245d49047421716a22c82c239d9363158b52411ceae978bc4b08f20a88d8c562c75490325f162ac63c82a1d0b8b611641511ceafc58bb0a9208e7d8d44599902432cec43ea3128629f1f63407d165288fb18f448a3451ed8e245d01736c63e84a31629b631d8a514314db1a08fc5298a60bc7d8d4451e37163cc228d142b8b1f52426114e17c5a90fb009208a8e2d8c7451a2e3ec316a48629b8b1d62415314dc58fa8b1218a6e2d847d490c53716c63aa48629b1f52156078b3d8fa9450ab1207d8d48519471e34cc else (if i<4 then 0x4a51628f9c831f62514314da10fb0c42f8a3e71b87d85062c5173c3ac0271628b9b8a1f61405f1410f8f44b18a3c006c7a258c51e00323d16c628f0018795c002e791d61528b1558f45b18a3c0061d1e4b00c79e54a2c54800f0fcf6c23aa5162a46a411c2d926a618a53155208fc5318a0065490c7e2c5980038f800563aa48314c62a4011c2953881242631520fc5b1218a0800787d8c562002c82a43f162ac001c980011982e421d618953157210fc4b18a0069054e2d8c5040038fec000243b12a62a02c740013892e1e4153154c58fb18a3400658e2c7c51a0030d0e8063b34d4a3162a78b6314681000c34003fb1348f28c58a9001d21041ae258479094c55a82c62ca510f9a5116887c9a1b08b29448e6c54794a21f2d163ec62ca281a5315887c5cb28b18aa0c42e6049458c5621734a62a8020b951f155a89516078e8ea98b44b03c654584556a2471e3aa62ac51238f185d16142c7a41611d528948eb18b44a83c6170b471e45859058a25450b85ac010f4822aa23d1285c2d1615607a41511e8943e8b0a163521308ec528a54624790980a34822cc051353891e426114da98bc5208f306c5e298c790543050fc2a3aa48314c20298a885c095116411e61404c544142ea9208f3091f0b580602908554628750331510105ac42c843aa298b1562421c10d208a08390d4c5d8876237162ac4843aa18111614982e41618a1d515c5a98b20b10e6c5905487042820f85a2c2ac483143aa281116158a882d62421d514c48eb18a345624758c51a290a2c28d23c82c4a31258961151c68a48b1300434c48b29208ea0d62a2021a5845909447562a3820d11161560846a418a511d23c8b0a4234b121288e9d4d8991ec524303e86c0fca51629f43625289147cc3fa1b08f29458a7c7d0d81f9445a23ca63ec0f628d1b611e531478b353db08f4529218a894d8e2d0c51730fe86c43b14a629f621e531478b2fb10ec4a1298a71fd0d8148762c53e822ca6c710b999343611e518b14ec8bdb08ea128c58a8a2c7d4d8c51e34f63c82a2c51629e7b5243611e8b14e3c01b18ea9218a79ed8c79054a2c53ea63ec51228f1a438b1c2f1468d8f20c58a1659a8bc790986294c5463c8316285966a2f891e6242531518fa9c5218b30147c7d4e24590980a3f16a23c84c629b8b1d52426314c3da98e0130c58a74590980a205ea7143ec024862a38b62411410a1721a90e01b0c58a8d46287d890c532a7143c862859b8a1d62415314da9c4010f20b18a700e2d8049054c5382716c43aa48629c7b5360021d8b14fa90fc409b1208a7e2d8c7c51a2806c63c84a31629e6b631e418a5314e01c58eb121298a70400e2d8479490c5402716c23ca48629f8b60011c104253151c58fb08a345664bc762549058c543363ea482c31629d93511e43618b14eae97c48e else 0xd0d894a2c51f36823ec)))
def gzl12 : Packing := (305,2,6,0,0,15,0,gzd12)
def hashgzl12 (i : Nat) : Nat := (if i<3 then (if i<1 then 0x47030410d088380fe9412a40194b06aba2a5b04e6f895cf18cbe3358818c5817a91719a085b456420083300098337f0013188155048fc0ff941c37801861079606a00000000001093a41094056ce0a5e310b4633f5c5af300caa07abe0f22c402102d8018320084fc68db0442e101d42ef101ca3841a8091303477c02bb88e8d876400000c47123cb861041c0a2180bfb81ab6065d220a2850ca046351346c0f8bc08200acd6039ca0a984020501345086340d994126e822b00001607e4000048a9ec0242000010269080e731342a05a4827ee82a81152a00000000040465e060de29d5024380000721b400003c00d80000101e1e0e2c418e800a3c036de0cb440f4900f630a40624584135482bb12006633ad4053a0a33711aea3420c1cc840cf313302081800007091700000c101c805900000105ebe2a1d82160000000000a2f0400000000000001001ab44f3f40db60176806f0c26ce08fe60773e0aa5c14180000b11cfa02b6c0a24815500001813f3024980000e10a04067240c8301588099a00000000000000e0876009d8c12b3826c508dda2a740000204990067c62a128104689cbc063600002c55be83910000181484815a803c1707e280bac0000784dca08bb20c364657a0058a087e00003415b800006142800001024b2007a0559210506030a010e1f08000620043609040001110e01510303020b01030303080101060b1800002901025b0b1a0005070304002b195b1c0001030d06330025000207131d1e0702360a0606086d001605030017040c0115010002020104140f0f100c00002b0118032704021a0a011c0b057802151f010a010c1e0a1c0f0b06010102076642025b00031e00000103390d02010c0e1a0500001109070b0004033001060c00681f280501000d0200051b080200011b0410550c1b2e041110090500030008181017000a2d3f0d00050c1318090212153d00090815061a020901040501010002000306020e010201000904090b1d02070f250b00080504016a020300040040020800010100001c3111180102010b0919060e130600071c000c033c0e118a180e170406004101010301460056150d20023c04090217070403d01005010a1b05041c00010310040400010033003a0a010615040c00000018020d55020f031a000706020e040301054601041425351245154809030c0109040c1b424e091f000c140304050a000005010a01051708060107010700002902030008030c07072d011901030000040001440104010d6a0169150c0b090d0013080c4e081a01089100180f081a200302001e00000500110216010621060108200f02164601000913000304171e1102000e08250e14004704192504001c000b0e2b01191b120b0002660316101a0b0c0005010301011b080c02060e0100000131231008000021 else (if i<2 then 0x8902a7278a004d021d6847c200f2a2652823e80000e04a780fcec087000000037720e1f41b740137b003f234340000280e0f078980fae40f2184f161157c28ac462a803a74003aa130746853816af046a0000041e980000081d1a23b8c5f4389caa022ee0c7d446dd8be5d14ecc05b08060d8c05a11d9e114582742042861381a0586c1b24819b716538338fc120488f940724214ac0865b0b5691318811fe411fc0aa450998229f0020498028e0591a0bc2843e882fa4002121156022f004f57097340711009fa0c5b808c5c13dec1ca80990f04fba27240000683349690240837419e40082a10f5a262a81db9012500000630a8000068880202ae4143060706040400001a2f2e00365085670062a069d413900000909c440b440000189bbf1738c095c000000266f0214e140542500823b80a5ea068d84ea8820ef19da82f570040584d55138e6e37c000000a72d007ee028a847fc0b1a305cee00d64036dd8cb202cba2eef00698000066139004ecd065f829d0135ce07d8418218d1ee05e9a041d84311800ca1758004d9c4af68ab910905614c08441703e8000004141ba06860b6fa04b9431598264000a9a0046000010058800f700654000000000302d7917081038cc07ed83116073ec1037451ff8383c06c0011c1802c8831a80959e292301be60ceaf071d60474803088bd3e0110a0dd985f1605040000040bb70015d88e3b028020cec416a88b02b06d462db90287800007057c405d80000381f7a068a60234c1ba181479036142186c561e89504023003433025b2510800000000034567800000000000000000028848d14e08124885c1403434050421173c48f00000906fc0000180358000000001828f1815d083d1403c40000100069012a5143600000c0a0e0196809c92145a00d3682483030a00000000000000b06e320e4000006036c911e3e08f9c1910000000000c0d2c01a018ceeb043800000819968cf6e026620abf0530082fcf079e20eeb920700000519bde0d1d41b970245505d4209d4c110a00f9107cf60f834079243b6000c140683c5e7202a400001205f040343013100837c274000e138ab690295812af06120a9040083a8147e81fad84850000000002022028b9aa016e6014d803be01cda0399e087cc23dc0524c062ae0ed480ff009a8a08c2e088ec2149824e7002c62da7c01e884fb20a2ec04980000000009073140d5000b8910e441671801d681fb00000d08d800003821560242b05fec0b150210882e3301ae01168000000000f190440ad800001038f605b700c3c0491203416054320e04c414c04aa8039e00000c0d2e89a200001e0bf48423e81c7909b1c080c810d10cf3009940208b807f000003108b6138400000100421577a001800000000030928c0a7000000822df10bee140905b5d04f0115f6c32cec else 0xd074bc4f01c426502d600001c2a810868c03de6019922a38000018c6980692c0319c007e0269406c5e04e301cb90097914ef206040000484689129500d21843a004a54a794408f000000000000000402384262802736068c80f49c613702df308eec0eee8189b8947307e880d7288686038c6069ea10784557881b86120040ecb415cb83b0a001d210288047b8065414778135f81d0804e7706b6a2976821b3014d9077e0059bc4e0c8812815e462ea2022be8483e088f221db8257004a7004714279305623a8038082420aca023f38b5081575c0e88000060469003b96086dc64f80000104d640b01c26ff03d7303320000041ec70935f01be432c6817780000e211f42e2680a15833d6145b8103a42965828bf219f202aac0b800000903a1a0b2f45d8e03254044d206ea0094000007169c00001869040b5770a1140ddea067593b6803c1a006a42304025000000803e980a5800d590349e0f5001a700055e10b3c0b4d814af837900a0700a88c180e81486177400b26018be824a3053742a05c09f68438509012124480a80021200001d703dc22588849c15b400000000008074704b7c074d421a504660124742e4ac57d480aeb091f60769004550c6700000000034180000640000000003811d701e80000120bcd80c06838df0508000004191c8294d02dc570384240800006019e633dc00f2f029100001e070686420000050466e021cc5d580000419ca00000000040405607e154feb002db0039d086e00000815e5820b0000000002c562e81ff00000829b0011068415b102c612d08219d8c9e605566059cc27700000108224037ac572b818fb1469202f841abe0127706e780a64000050084d056060e14000008a40919f940279045290a0c6143860a9641d500000010226114040ec700212076c0000002838017400001a306d80ad889cfb0a1a00000000030333803d7e308ac641b0255000012074bc1d4a8420308f1a2f3201a9d8090d14de0000281b80805d015bb833fc062d00bf2d02410042d80baa02ce311aa80fa5856a984a960811808bb802b48162111b900a7bc18652119115c9c10040000000000018410ef6022a000001077c6119cc1a6b0168a0554c03a0000040ab2b0366a010c4229e04ed403f4c2bdc8544608e9b09a7207c58012e004c50458812dc01295084dc110ae273b0117b815f0000180f2dc215f89886097702fcf816080000a06c3c24d201720000080238a1383c5f4b80ba600ce000014235a844c00000221a6404b40ab80000080945055eb01e3000016018bc59cd099e802fc4005d4014d0c1600000403a60107e8324409420085d8142984be513db2090c000000000312fee0ad1828ed832bf128820b74463a0026eb127f60f0e4185f83a40000020363c5d1e89a0f19028135b00ef0000000001604b0a0658)) else (if i<4 then 0x96011d843ae01d5c172700824056f308c1315a7a03100000681f000159207bc024f00278815636024505eb80000b08db42d6285e480000a095b812a14144c00c8f0967013a4000068c917078000001c095f83a0a19110057000bbb0af3000004097c8078a006f90a2060f77c26a0000050401001d8005a58229f033540138c193b827ad087cc0a9dc2790000010353c227b808ca883571654204b80000601b900000c270e4173681453025ec03eec2614041341075601518100a833f5030ee21a2c0c9a0109e044b231b6424f8a10f90314000be022c28a1800000e02bd818b20bb7015fa20f1a81d1982e5a14ffe06d7c62e50c6a9133aa2e0d40a498358d01a3228280000581df002b5410f50681b83c790642a121a06388000000000e138e003748164917a5a34b3017c5819d00061c0832c14d00000000000000181237591900001c0d2a027fe09a610798802808284e803be03900000000006805f20173e0656047d10cb6a05bc80407819ca82ee1013f824e3020c5021e30033e0255046d704ebe013aa142d019bb02f99159dc108e0075e09c2f09fd20443c00a8003881667a0a6300aed8c7790918e098640529846a1049860c4a0042e80ef40670a11144293e8a8220274c32bb802f10474e08016108a860b801d900001410bc40a1f8cb500000c2efb019a80000818be0000000007800800000e2378c568084ecc1876e349ac03f9887f608ac801cbc0b5e899541a5a0000000005028ee054600001005c00000781bea0422812238198b148ee0a2885f61023931459209bc00004005090a2ae010880d668948009972105d808fd0071107de00001c52618bbd0000000b840000703ade057b0045340c310a165042a008dfc570184da0000030ee80000308d85052000000c150001af514e7a07ec0000180940000141312007c08a917085cc01c3c0d50000000886e0c0ac001504bf7017b2009381be80000d00cca0f400000483503031980624c20a308794020542b6f0267783e640661e0a5a80587026dc0a44e2bfd8596280d2d06a5a02f0824be0139a01ac607008120d02f211095201f940aa58b1f704fc81064415c088cc30226c21500000184d1c04bcc03b2056658528814e80000181dc00000f069800000401b30acb616412c012851cb0bb5401243036800000000000000a097400000000071773e0b294131a8308703440000201695010c503f981343413cf04a44031cc267d8088e839b3190c206c5c02200000e037a6002954a9282b300000c274ec50ff032f0176800002c0a6481fdd02e4e0f2b0001c02361135901298407a8852a00000000000000682c400001c00b000007897ad04f800752c07080000111d6611c5c51a8817d402372290bc062e81c5115be00000000060484000008147240b048115f00022060b80fa7808c else (if i<5 then 0xc63b4024b105ee0000001a20000081067e080b4091180d9c1a5e00000802d00000306d0e2395c26010b6de07da00000c60e8814f281a7a209c857a00000718c0e10e404c698d165177020784c017282140000000000000000000909f40000146781035f204d0000000000083825009ba054c00002033a600406218fc055800001140340b35c44300000200c6a116dc1bc702c3c4940028f8c1e128163a07d4013e541c540262000010131800000000021521a07a981bd185235019c00001400900818d877f00395455e1c004c033e223bec639c88f000000229ec0000483b400001625a18407d88ca404ef2128cc412f8a94805d840a4e804c80b5fb0117c20b8001e30086208de00001010ea03bc415c580d8c0000484b8205b200001c10258bad610ef02b9881af40427c0143c0f86813a400980000140b09c124e80e2e0979e07e00193709a49043060a1b425ad82340100f612c2812d382712065940b8b8170783ec10838813e24547d08eaa04ca629b781d478007409df6072fc1c4e850a100d34065ec0fac8a1394002c08cbc0b98015e311bac325d008d00cf89170a031bfc16e3040bc0323005ed85db203dc6079ae02d541d620393709d48002e440ee893bb092a20403028f701166102ea0e9b04ada38e42055c00d9d84c2888d61019b01377c0ab3811e3065181220c5ac881c67052e831af0476c882420708a036840a8c848ae081e2081784d538124c0a4c803d3456958051b072c011d40000383d6e04cf820a941ecd84c920a24e2a610518c03af208be00003862c682d000001e0e71806e88331019388053899e460219507fb8126044018000030879429280000484f460502c02d80470e005c000002060e41baa08a020641a2b2500c9782100091c00000457c7844a00000c2f080222102119219540f940406f8ce1612d4e1190000040ac2e073c60014c67c80000a073b012f7c48920123e083fe1394022cc0264e046260888000048432107f800003c46a60359915ae000000000581aea098682b1c827350cb7a01dd4128a80d0f0bbfa066d405e141cd781e7b057ee265ac004e90e0561eda0d46008340307e07f32269ec5ade0011c07c9801ee44e2f024f5025a806b685a7d840c10a5d4206b4533e09a9c01506149681fc6819eb065300390d86dd83b12082da0744c55fd0b63304b08081f0174d8472906bba026e008940a4340102a0272c0c220105e019680b18c51d201ca8120820f6a084e08884615a9a06c881f7080143084c00002862b803562119f828f5c570f8b8700000000000000188739089c629340000383096145e0000185f180000a079d60c380000483b3d026560bfa424d00159000000000240c4084036153f0030cc1efa08b5815b854f74c01390034519df0143b0246a083f610b060d6801468042d919e else 0x584b1605d1e14a5414648aca809b76043604cb80000000000000082278000070a2261121828c581bf403e6801f6417880049f0261421f1407348ae30089b81241006800000a195bc0c66823d5a117601f802f28000000000204e0e0a1d8029180320000000000c06e00000f878000000c24de881b803ac2220ec49eb001e00001c0f150112602da811cc20f6f417b600ff501a841119c263f03abf026a20c79c18a10369b01480000280eeb8078b0001410c1413df036f00001a2d75c22900292d03e40000300da0004ae61bfe34110016c801cd1096a00a980f680380319e3206dd58a7a816ff04c0804f74662685008014de23d844af9836d2077a00d9480b6c02278055b2338021d9f0bc080a33027130279e0a7130501a3268c1b5f0093003cc40b5081886807c008ec22fd0426780000104ff00324e87900000101e660fc9801b8000000001e0300c06380000b192ba12738022d82ac7047a00001c5b94051af0166c0d08026f78041c02f3830e1828da10db6136441414000068046501c60000181140048bf021f4347380a338424c08930076ce068c047370393e0e23c296c03ffc0386c13da40c5c0305f1a2ee0b3f81157893c402074075c0289c8406000000282541bd804af106ff40fddc4ccb82cce08f2e036c856c1003e0a1a0420d3064c489d1a156a000000000003fb00001e082800005003aa17b2202fe4592a803300001822068259383e30102023304818e10129c01d4000000000400ed000000000000004082f217c8e279b8025b0bd05156180bef0411800006046100c28056b6851490563827200000601eeb011200002001100000106064234400000000000001c054a02011828f0000140f2440242009ab009fe06fa059a4013c513ae0305000005818df086a0000381d7284ba00001207b2812c8000006287e0a7d0039a02c72137a000)))
def gzd13 (i : Nat) : Nat := 0x24327ac07a8411454d88f411148a63d623902888d45417b1883d02914e7a3d8215114539a178a39820522a05628f50c108a7c5603d42114d8ac472050d453a4327ac45a8403a24d8a1163a22863444f588b1d11420923601620b40394458c516807285cf58f588e422d444834585e28b1cc10289c5522c73040c14b62b00aa100e8c5622d4201cd8ac458e40a1a3d88f511192114f67158a81e8453d88f8a8148a6c51ec542114d60f47328aa05208b38ac05a94039ec47c5402943628f62a052064460394205331ec454446a10462b1508852d403a2ce2b116a500e7a3631478b40a1eb62b11e2d4207e17b734fe69c677dae0591ab745e744a48cf0c5fa3b0702d118aadf5529cd222153b0688b994423837c5106c06c003ffac7ffd82ffeb17ff4cbffb03ffd71ffea8fff4c7ffa43ff963ffcc17fe58bff285ff932ffcc0ffe5c7ff2a3ff941ffc98ffe487dfccdfde33ff7117fd847ff2c1ff930ffc907fe442ff533efa66fdd227f68cffd445ff211
def gzl13 : Packing := (34,1,6,0,0,11,0,gzd13)
def hashgzl13 (i : Nat) : Nat := (if i<1 then 0x1409807404a582ea000068090000000ac00000000301f2e0ab00004810a452bc10d0009408471098e07e808f680d201a82400d08c001d645a420f3f082b845740754057211fe80e4c17842a8905ee849e857860c0815550499c0934091e00f8032b4585a0462076bb98580a0a0bf00518016c01ef02f6106a90a12011f212d3022110064094c003e18bd023a419cc0d84065b002720038015204f90133411042805002e82e101c2407380537090a418ec1095181284008565c2a1d00368321c175a0431012f0b1cc562023c6075a0c5984a14081c16408248054880168130f00d40001e010000600003c5b3a0a2612d602580001830bf63080000c0b20000101c6039c0000c2a0815e882bc000140fae088f81a14163c0211086204858421c248804e50a1d847b0244f070181cb04172029611dd01e7017ce128f134f020a84100000000000001414a000000004801cc0f0005dd019303110184805c003680a3745eb4119f048103f8802f011fa015a8a7481ff20e8a1777025e400002015058208ac41680000e05dc838f8130a040603ee80f38054c26f614800002816f00607042b8896c21f400bc14960443464d40f0b035e897244d5a07cd07e80265855e20f1014a0000000c360d78153b8257822ea2070000280cc41282e01e15d80b1800016084d0925017ac07f4055e81ca009a809ce0cd011360879421d60fbe17c4808800dc4217303220cb9c1b2824f4089f0a7b8553404bf10ac84be84040000e09600000401ca083e07a503f00000e10620859036d009040ee716730acfc08ea299e1533096581e4c08980687298c8083e2e5a091a837f4116028920179006401f100c3518f4806284420077b10208452411b403e1013d03ab4431e29bf08450bd385a9a0019170d016bc5c4431ad0438000204500000e033c03194244c09e006280003018261308038f82300000a0a78080880dd548fc03d917e9833c823821125160a40f5005a400ac151a09a0806d411ad11bb0a7284c90058c022c086e487ae065704d790e5c0050c01e04030aae4462e2835b265006c8172006f01799815bc1df043ca107f0413450ac31161906317441eba26b1106102db00ed60c9f027e808d41a2c223507628137c04020de0018504bb0574e21d7059784964126a0a9d08e80c88c05d60b307060c0533002102040e032a00040121020205010511003a01020000005b2908000001100933040002000100121214422100010e0000001e09020a090d0806090305000c0016000015022f0005000000050606052b25000d011c100a001c110345023e0f07000a0200092501063c370000000007300a0e0606000113030003031d0102000a371b190000133006103b0303280115093a100e00000209000002000214000000000a050a011044d32a00000400010a070000 else 0x809d80299028401eca212f074b836ac20f00b510728814b84ae2004e006d40f181364251d101d891ac03ca07ac043008f8048020aaa03fa00a182560310710fd822b8252a0cc5009c81c1c2410066506e30bad8028a0631034b8393c1aca1037052701d2c4403447d056c82b8c01f6051c0695091fc02202e4802fd8858421562cd605058ab1c0f6226e700e6883440c422c9d02a00003c062003b0069b09888204e0e600002098c0001606a700d0000300102116306e900b000000000f054184a80000a06c608da0b3d81c4a22ac)
def gzd14 (i : Nat) : Nat := 0x195918981d41504b23c4c2880a7bc0ffbff
def gzl14 : Packing := (2,0,6,0,0,6,0,gzd14)
def hashgzl14 (i : Nat) : Nat := 0x31aec2284c18823bb3688fe493ac1358f619b94e1d80b95112c6c6e4d5c0804c6a05908e14045000000e5cc95cb00043eac618618003e9a4fe2d17c83644229039e058b00061400091ca42354eb5ed1173800000d0051b1041c920f04055022a040ed40005c0641
def gzsamples : Array (Bits × Bits) := #[(0xd866789f0851bcc5baf4c1477d7489923a4adeb26a7ef4967a54650cf77abaff3eb9d050ee8018a8e4319682dbe0000004082000800262ffe003ffc862003ee94818bc8a030b8703a051a216600e83828748908c04041a909a804a341388b04b,0x660430f6304000408000a81120d9120bf8920361000700b241a03130406001c002100343000800608905012082815115155135105115300135115195135114004810940a000a8501a001a216400c83820748808c01041a909a8008241180104b),(0x3adf76c6e74816e063e0573fd5fc348951fa1964aece4e2ae1fc61509deebf58f348f92bbed7f786cdad06dd4b30040004084206083d3c800200000827fbffee10a5320d4346642408444550a9805e51d401c9011c155421211a491a3c084f96,0x16208004d0a2d0801c0020088000140040100048030d00c80400040020008140100a400ea04030400084086054a0ce08208c20c08e00a88c2860868ac08a08e10a522044340402408440420ad800849b02449120c09c420011b4112a81c0f84),(0xedba451a51fbba6688e30d12476047ceb8a4e787317a255fbfaffc9c65c268666497287914177ab85eb7f7b43880000048800006ffc0a0500040003799fbc110020142d164867971c31a819a90330187282a400333d041fd5ac503c462d15141,0x890d044a08110c06009001754438a9002401c081000010145100a1300988008e04d0812105904f220e6a2091230c10c50c50c52c50cb0550450c50410c14950000000c1240630514302819000330386080a20014290098518c4124142c35053),(0xd5a2d6eff5f9635837ff16cb7c8d574b07fde6e83339136489cdf4ae062d46a70dd01b60d2b00497ff55aa5fb7ac00004377c285000081003db400b79a000001620690728808581499f838263de0104424b93dacda28a49cac7030803d680ca0,0x460228010302240080002188a010000358a962446d4624ba100821002462499008306249800440000d01194648801a41a01203a51241000a61a41a41821a00a16200901288084804b05838663d40100924a4158498202418a1102990bd1804a0),(0xd32f3763bb9025db737b15fb145b5cd28f779fae97ac9bf3df1569c1047d07ec5f2a58409050acb85aea94f115d4040040006083800241501fb7ff402004411280cfe802f1f1109a09812401011e04c0c1936464c689c14304b892484821eb4c,0x8199c1008034c0bd605606445a02ad840604048290a08044261002459009922c2004003458713189728a46192406a4aa4224c84aa4aa4b748a02a42228a4eb5a80cf680071f1109a0980040180120450c013607246d9c147046c92494027eb14),(0x80253ee4afe6efc3af90877935aea25fc9a272fbcaa257fc4fee68f73615712b9dc93cdfeb6bd176612dbfb39020043ff0001d7a8002c23fe04800004404001504f005813e0092ed74cad6010000a808d04417b188036b0b8022a040ee461aa4,0xb04001820243880413124a0c060c2002412c0a0200924490054200990200152422d4182244688800d80a0c094802c06006806a86c2c816c06c06404c02807d000001813e0012e404da544104002809c0203501c019610f012001d1ae460ab0),(0xfacf30e55b4166c5cd19bc40ce4d1a6882fdd0dd0e455b7831a3a63c19e4c054fe056bb784a75d566033e16c1abffbc000000203803f9c402248000046000502f90880543c7a3400020466cb521c74324e8912c19220165833a8a46b062190b1,0xe409140020949084b21291aa015b06a1d8dc425a5d060a0242a105050d4240000ca01a000081643839f60a094094330330370173b70394672178370352330760680880503c2a34002200624b121c76304e8912c1d230125c36a0a8c906229031),(0x6f323bf06e67e0b6ce4c2810063526a5e882ea1fa9e463d94f2cbf7acb5fcfe313f3afda3b716fc84c9c9c7f3b6800000c881d7877c005002048000022040416f9f7ed22c08149001206120b1259014011870b7a29c60462f21de06c91b8862c,0xa64a288a190c2c118ae041808210210fbd1c82c500e2688a2240b5a002443fa2029000218d800300dd0015a2848338338f3811003031072831833833a33c3682f9f7ec22c08149003004022a9248005011c50a7a29460460e619e82c1138840c),(0x5bd38bf781036e0a56a4a6ed5cf35b2b62b82537f8bd6ecc9332d7895968db29210eb69f721a9fff6d676d9d262bffffb377c000080020800000008000000002fdf768283d7800cd452109a44ec3a82e0b10284820e7b1004803452741876541,0x114483ea446008424100480550a0a11405020101800801012d5298c04094a428500c002400221346820004009603c43c03405c00483c22801403c0b401c0380295f768280150000941210180c08380060150081a21c688000847542640816142)]
def gzcolumns : List ColumnInfo := [(5,2,440,64,6),(7,0,504,0,7),(9,16,486,0,8),(11,16,484,0,5),(14,0,1009,0,7),(17,0,494,0,11),(19,0,492,0,8),(24,0,999,0,11),(26,4,865,128,5),(34,1,460,16,6),(35,0,476,0,7),(36,128,859,0,8),(39,128,344,0,4),(49,0,462,0,8),(56,256,647,64,5),(65,0,446,0,9),(66,0,957,0,11),(80,0,943,0,11),(129,0,382,0,9),(130,1,332,48,6),(132,0,891,0,11),(136,256,535,96,6),(144,0,879,0,11),(156,0,867,0,7),(160,0,863,0,11),(192,0,831,0,11),(198,0,825,0,7),(206,0,817,0,4),(257,0,254,0,8),(257,32,94,128,6),(258,64,701,0,8),(268,0,755,0,7),(270,64,689,0,4),(296,0,727,0,7),(320,0,703,0,11),(324,8,675,16,5),(344,0,679,0,7),(384,8,611,20,6),(480,0,543,0,7)]
def gzautos : Array (List Nat) := #[[],[81,130,118],[16,82,131,100],[80,81,82,83,116,133,118],[32,83,116],[128,81,130,83,100,118],[48,33,133,118],[48,129,82],[16,33,50,131,100,133,118],[80,129,50,116],[128,49,100],[32,49,130,83,116,118]]
def gzlevels : Nat → Packing
  | 8 => gzl8
  | 9 => gzl9
  | 10 => gzl10
  | 11 => gzl11
  | 12 => gzl12
  | 13 => gzl13
  | 14 => gzl14
  | _ => emptyPacking
def gzindex : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 1 7 0 8 3 1 (hashgzl9)
  | 10 => lookupWord 21 66 5 14 6 4 (hashgzl10)
  | 11 => lookupWord 462 1537 8 18 10 4 (hashgzl11)
  | 12 => lookupWord 545 2213 8 19 11 4 (hashgzl12)
  | 13 => lookupWord 183 493 8 17 9 4 (hashgzl13)
  | 14 => lookupWord 15 67 6 11 6 1 (hashgzl14)
  | _ => fun _ => none
def gz : Forest := (1023,14,fun j => gzsamples[j]?.getD (0,0),gzcolumns,gzautos,gzlevels,gzindex)
set_option maxHeartbeats 0 in
theorem geomgz : graphValid gz (boundsBefore knownn487) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=5) ?_⟩,listPieces_all (d:=3) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz8_0 : block gz 8 0 4=true :=
  @streamBlock #[0,0,0,0,0,0,0,0] gz 8 0 4 8 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz8_4 : block gz 8 4 1=true :=
  @streamBlock #[0,0,0,0,0,0,0,0,0] gz 8 4 1 9 (by decide +kernel) (by decide +kernel)
theorem allgz8 : block gz 8 0 5=true := (@block_merge gz 8 0 4 1 sgz8_0 sgz8_4)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz9_0 : block gz 9 0 2=true :=
  @streamBlock #[0x7,0xff,0x16d,0xe9,0x659,0xff,0x1e,0] gz 9 0 2 8 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz9_2 : block gz 9 2 36=true :=
  @streamBlock #[0xfff,0,0x7,0x5,0x1ee559,0x73ef659659,0x32,0x19,0] gz 9 2 36 9 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz9_38 : block gz 9 38 2=true :=
  @streamBlock #[0,0,0,0,0,0,0,0,0] gz 9 38 2 9 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz9_40 : block gz 9 40 6=true :=
  @streamBlock #[0,0x3ff,0x7b,0x19,0x3,0x19,0x1cb9,0xd9,0x1b,0] gz 9 40 6 10 (by decide +kernel) (by decide +kernel)
theorem allgz9 : block gz 9 0 46=true := (@block_merge gz 9 0 40 6 (@block_merge gz 9 0 38 2 (@block_merge gz 9 0 2 36 sgz9_0 sgz9_2) sgz9_38) sgz9_40)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz10_0 : block gz 10 0 19=true :=
  @streamBlock #[0xbfefbef3c1ee25341d2,0x7fff79de7ff77af,0xaafb7febdd7fded777,0x27ffeadf0b99bfffe9,0xf6df7b6b2cd7faecba6b2cdacb2cad,0x3147e2ffecb2cb37ed4fb2f777af,0x1c5fe5cfcb965965967fd967cecdb4e,0x19b6dff65ff59a19ff,0x1965965e3ddd965965c] gz 10 0 19 9 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz10_19 : block gz 10 19 36=true :=
  @streamBlock #[0x1b6db6db,0x1b6d9,0x1972cb659659659659,0x32d9659,0x19,0x6d9,0x72e5cb659659659,0x1b2659,0x39,0] gz 10 19 36 10 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz10_55 : block gz 10 55 36=true :=
  @streamBlock #[0x36db6db6db6db,0xdb6db6db,0x6db,0x3965b965965b,0x6596d9,0xcb32,0xe5b72cb,0x1b6db6d9,0x36eb2cb2cb9,0] gz 10 55 36 10 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz10_91 : block gz 10 91 36=true :=
  @streamBlock #[0x1b6db,0x3,0x6db,0x32cb2e596590659,0x6e59,0x32e5b,0x1b,0x1b6db6,0xdb6593d,0xa5285] gz 10 91 36 10 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz10_127 : block gz 10 127 36=true :=
  @streamBlock #[0x6db6db,0x1b6d9,0xcb2cb659659,0,0x3,0x2b6,0x396c99659,0x36d9,0x32cb2,0] gz 10 127 36 10 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz10_163 : block gz 10 163 36=true :=
  @streamBlock #[0xff,0x72e59ff,0x1cb2cb,0x39659,0xcb2cb2cbf,0x1965cb2,0xe59659fff6592d,0xcb72dcb2cfb2cb36d,0x190,0x190] gz 10 163 36 10 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz10_199 : block gz 10 199 36=true :=
  @streamBlock #[0x19659f,0x1b6dbf,0x6d9659,0x32cb659659,0,0x19,0xe5cb967d9659,0xdb3e,0x6cb9,0x32cb2cb2cb2c8] gz 10 199 36 10 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz10_235 : block gz 10 235 36=true :=
  @streamBlock #[0x36db,0x1b19,0x1b2c99,0xcb2,0x3,0xd9,0xe59659659659,0x1bf72db2,0x199659659,0x159659659] gz 10 235 36 10 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz10_271 : block gz 10 271 36=true :=
  @streamBlock #[0x66fd,0x5,0x646cce,0,0x5,0,0x659659659,0x2b2cb2cb2cb9,0xe4,0x1400] gz 10 271 36 10 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz10_307 : block gz 10 307 36=true :=
  @streamBlock #[0x3,0x199,0x32cb6cb,0xf659,0x1b,0x3,0x32d9,0x1b659659,0x365cb2cb2cb2cb9659659,0x19] gz 10 307 36 10 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz10_343 : block gz 10 343 36=true :=
  @streamBlock #[0x5a0c6318a,0xc66d86336db,0x18cdb0c66db,0x2831b2cb6e847f3f2db,0x14b43e55c97e7e7e5b,0x13b436d595cb96db9,0x4800ae25717171f9f9659,0x896817e4ae5cb972db659,0x2f16186cc2331310b665965965965cb965965972cb2e59,0] gz 10 343 36 10 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz10_379 : block gz 10 379 36=true :=
  @streamBlock #[0x14031836134d8c66c7a0ce802bc,0xc3500036cc3006cf07dcf,0x66001b198c5072eb36cdbad877aa,0x561aad18c66db30575cbbf2fe5b6dc7,0x14aae2014952fcdae5cdf9655,0xa7542606d2dd3975abb5c5c6b6e5b6242d3,0x2fc807cfc857cfc838dbf3f36b8ffcd33,0x5a2d0053972a50d051ae2e59f1,0x62d06331ba63108cd6d6635b974db2cb2cb2cb2cb2c99,0] gz 10 379 36 10 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz10_415 : block gz 10 415 36=true :=
  @streamBlock #[0x1837b6dd360cdb603766140,0x63060c6c6dd395de,0xb8186d8061b6d805,0x1ed5a0e9833972e5be4cb4dad89,0x2d5710538b8b252b972e7e5f36a5c33a7,0x50a130ef62b57f3f2e4e7db5738403,0x4857e40e2f9f900e2e2e2e271bc5c59b4,0xeeb40e0a5f9f9f97272dcda1f1,0x2b7f1f8ad0c6266c331898b3118d6668cb2cb2cb965cb2,0x19000] gz 10 415 36 10 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz10_451 : block gz 10 451 36=true :=
  @streamBlock #[0x6fe6800,0xc0666d980ccdb6db56db6dc7fa784f,0x33019b6db3019b6db6c76afbee,0xdeb6621b6db972cdb77e5cb6db624,0x63471072e5c4f9715f973f2db6c6ed,0x625caccdb7f2e472e4dcb72d96d92877,0x3948e0e425c5c71f9571717171f965c6bbd5,0x3b9407cfcb91cb9573f2e7e5b972e85,0x4b33989fc4c36cd2dd8c5ab31316db2cb2cb2e59659725,0] gz 10 451 36 10 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz10_487 : block gz 10 487 36=true :=
  @streamBlock #[0x5140a05a6531018a2d,0xe7306d9ce60d96db6d9b6db38,0x1547056e6b9299b3336d8,0xa14e5b92b3960,0x1e82be5f25b5cb6dbbe39,0x389c5581b31662cdda16d815ed,0xe7120dab98bb894f9f97a5,0x154970b5c69896d717c9b6cdb,0x71717c5f1121b2357172e2e4a332fe5432cb2cb2cb2cb2,0xcb34c80] gz 10 487 36 10 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz10_523 : block gz 10 523 36=true :=
  @streamBlock #[0x6db65bfc,0x32db2d965b60,0x36cb6d9,0x6db,0x6dc9cb9,0x65b2cb659659,0x36db,0x1b659659,0xf659,0] gz 10 523 36 10 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz10_559 : block gz 10 559 36=true :=
  @streamBlock #[0x196db2d87f8,0x196db3e,0x397ec,0x72db,0xcffb2c,0x1b,0x36db6db,0x3f,0x3,0] gz 10 559 36 10 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz10_595 : block gz 10 595 36=true :=
  @streamBlock #[0x36db6db,0xdb6db6d9,0x6db,0x6db,0x65b96db65cb,0x1cb2e593239659,0x7cb9632db6,0x6db6db,0xdb659659659659659659659,0xa] gz 10 595 36 10 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz10_631 : block gz 10 631 36=true :=
  @streamBlock #[0x19ffffffff,0,0x1b6dbf,0,0x32db,0xe5919,0x67db659659,0x65b6fd9659,0xdb9659659659659659,0] gz 10 631 36 10 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz10_667 : block gz 10 667 36=true :=
  @streamBlock #[0x6dbffff,0xcd96cb2d9,0x19b,0x1fb,0x6d9,0xcb91cb9,0x65b972cb6cb9,0x6d965932e5965cb9,0x64c99659659659659,0] gz 10 667 36 10 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz10_703 : block gz 10 703 36=true :=
  @streamBlock #[0xdb6,0x6db6db6,0x33,0x72e5b,0xcb6db,0x1cb2e59,0x36cb6f,0x36db659659,0x6db659659659659659659,0x5] gz 10 703 36 10 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz10_739 : block gz 10 739 36=true :=
  @streamBlock #[0x1b6dfbffff7fffbfc,0xdb6d9f,0x1b2cb2cb,0x3659,0x36db9,0xcb919,0x6cfb359659,0x1df659659,0xcb2659659,0x2d7] gz 10 739 36 10 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz10_775 : block gz 10 775 36=true :=
  @streamBlock #[0x6db6755ffeffff,0x36db05b6c,0x1b6ced9,0x3d9db,0x6cb2db6,0x3909,0x32cb66eb659,0x36c659659,0x3965965965955,0] gz 10 775 36 10 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz10_811 : block gz 10 811 36=true :=
  @streamBlock #[0x36db6c,0x6db32,0xdb,0x1b,0x3db33,0x6,0x19b659,0x36659659659,0xcb2659659659659659,0] gz 10 811 36 10 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz10_847 : block gz 10 847 7=true :=
  @streamBlock #[0,0x6,0,0x3,0,0,0xcb,0,0x1b659659,0] gz 10 847 7 10 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz10_854 : block gz 10 854 36=true :=
  @streamBlock #[0x3,0x1b6db6db7e,0x1b6db6dbb5b,0x1b6d9b6db39,0x3e5cb9,0x1b6db6db,0x65c7eb2,0xcd19,0xcb7f26e59b2cb6db659,0x1c9cb37e7e4cb972e6d765cd72e5972e5cb2965973f35cb2cb97264cb37e4cb2cb932,0] gz 10 854 36 11 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz10_890 : block gz 10 890 36=true :=
  @streamBlock #[0xdb,0x36db6dbfff,0x1cb6db6db6db6ccf,0x7fb6db6db6,0x7b,0x6db6db6db,0x1964,0x7b2cb265b,0x6db35ecb2e7d9adb6cb6cb2dcb,0xcb8b772cb9b5b972e5cb972e7e5cbf965b726596e5dd65cb2cb2c65932cb965b972cb9,0] gz 10 890 36 11 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz10_926 : block gz 10 926 15=true :=
  @streamBlock #[0xd9,0xdb,0xdb6db6db,0x36db6db,0,0x36db,0xcb6,0x659,0xcb72db6cb2,0x2fcfcb965cb973f2e5965972e5972cb2cb965cb9,0] gz 10 926 15 11 (by decide +kernel) (by decide +kernel)
theorem allgz10 : block gz 10 0 941=true := (@block_merge gz 10 0 926 15 (@block_merge gz 10 0 890 36 (@block_merge gz 10 0 854 36 (@block_merge gz 10 0 847 7 (@block_merge gz 10 0 811 36 (@block_merge gz 10 0 775 36 (@block_merge gz 10 0 739 36 (@block_merge gz 10 0 703 36 (@block_merge gz 10 0 667 36 (@block_merge gz 10 0 631 36 (@block_merge gz 10 0 595 36 (@block_merge gz 10 0 559 36 (@block_merge gz 10 0 523 36 (@block_merge gz 10 0 487 36 (@block_merge gz 10 0 451 36 (@block_merge gz 10 0 415 36 (@block_merge gz 10 0 379 36 (@block_merge gz 10 0 343 36 (@block_merge gz 10 0 307 36 (@block_merge gz 10 0 271 36 (@block_merge gz 10 0 235 36 (@block_merge gz 10 0 199 36 (@block_merge gz 10 0 163 36 (@block_merge gz 10 0 127 36 (@block_merge gz 10 0 91 36 (@block_merge gz 10 0 55 36 (@block_merge gz 10 0 19 36 sgz10_0 sgz10_19) sgz10_55) sgz10_91) sgz10_127) sgz10_163) sgz10_199) sgz10_235) sgz10_271) sgz10_307) sgz10_343) sgz10_379) sgz10_415) sgz10_451) sgz10_487) sgz10_523) sgz10_559) sgz10_595) sgz10_631) sgz10_667) sgz10_703) sgz10_739) sgz10_775) sgz10_811) sgz10_847) sgz10_854) sgz10_890) sgz10_926)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz11_0 : block gz 11 0 12=true :=
  @streamBlock #[0xa7b6da14f6db45750ba5d22ba85d2ee1d274a42908749d29452e2baa3e8a68aeae174d1e0382407079efef008eee70f4f6dae1e9edb5c0513a28a2971fe7fff4f8,0x57fb6daef5529b6daef6d5b6d4daf6adb6bdaef52f6da1486bdaf6dae94db7edb6dfffb6db6da14a5de14ee73853b97d6d7daea95b4f6bbd486db5c290bdffb6dffff,0xaeb6adb542b6adb4e05d24dae71ddc9b5c9f25c20db49a777236d3f9ddd6d73d3bbadae040b438168109ddc8daeff7bfbed7,0x3853b870a77501d6a80eb4e441cee75073babc1ceeaa0e7724e0e777bc1cee,0xaf6db6bbd5b6db6bbdaea174bdb5ebabbbbdb5ebda94851a90daf6ba5c3528daf6b85c3514535febcfffdfff,0x2bbdb6d77ab5edb6bbdaea974ba6db5d52e974db5d35d290a21486ba7dd29659652cd,0x55b6db6d55b6db6daea174ba6d7aea174ba6d7,0x2ba6db6bbd567edb6bbd,0] gz 11 0 12 9 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz11_12 : block gz 11 12 36=true :=
  @streamBlock #[0x3c9d6db66db6fdb6db66db66d9b6db6db6db6db6db6db6db6d8db6db66db6db6db6db6dd6db6db6db6db6db76bd774800ff5aa3fd7fffffebd777fd148bba2e89ce22f42f5139dffffef,0x7bdffef36ffdb6dde3f3f3f1f97c5b6cc4c5b6da7d3edb3b6fe53f16db6fc793fff7e3f14fc7e2636d7bfef7a7ffffc9ff385dd2ffffebfffef7,0x3c7cdd1fedeab6c716ddaf8fc7e2de9b636dff9cd9b6db6d98fc4dbfaf5dfe8c6bd7731aa1eff8084214db5d7ffdfe77aefaeeae,0x1eee3cd6bdfad62331c7c9bda716621985bedba0db169882fd782df9a312d0b4f6bbdaa0ff5a7b7ed7fa5e15ed,0xff63bdf9de99a9f3f2ceee2e2cc4ee66fafef7e6bb8bd0395eda075701ffff5fe8e77ff7bef1ebbbdaf4,0xaf6bfcba3daaad6d731769ed5ad5e8eaf477fffbff7ffdfe7e2637e3f1aef5ebdaffefbf473db5f7c95fff,0x7f3f35bce77fedb369662e35b8b8d73bf8fc5db3f9ff7fff1ed7ffff71f8b8bb8fc5b6db601ded005ae1bfffffff57dfed7ff739fdfd3ff477,0x4a6ba536bf7edb3ff6dda8a5a52beede53e94d4a5c5fe2cc534262cc7e2f5270b6e2e10a6d76db6dfffc214bcbca6daee385a9a01dd9fff17d966b2167ed65feecd659669fe7e5cb9,0xddb583adba36dd56edbfe3fd2a6ca13b5356b0916b35d94b3ffe508424bffed66d5aff2fffff,0x7a4cadbffe95f70ffff4fa7eb2f4b3e9] gz 11 12 36 10 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz11_48 : block gz 11 48 36=true :=
  @streamBlock #[0xf3ef9e1b6cc399b3662f881b6cd136fdfd99b6db6cd9b690db37fffe7fa36dda6dbf8bfc6d36db6dfda9be977b6da1681e7be7beae3ffdbfeff6d7ff9fffef9fcfbfe7fff7ff1c57a4b8ef0510,0x1d6dba7eefa7cedb36db367c5fca6f16dbbee38dbb57fe92db6dfc4c6a5b690bdb696da3cf7dbffffffff6da7ae73ffdebdf3ffffbbffd6f929fff,0xc3c53ff3b536529c4c4c596d61eff31c6db6dff2dab4c5f1016db6daffab47fdb5efffffff,0x13e3d3ffaef89862623898d7a6fc6d47ffd3fbbd0c7e26218bbd009fffff1ff5defffa69ffdfdded7b6d,0x1eacf55fa4b3e2ac5f9ad83a06702b8771c70141eae3dc79e577b4ea7ab8,0x298b897771c626262aa771dc480e4f89fff1ffe1262f8fc40bee74f89ff27ddcf7ffddeffe71d29,0x1ddaa5fdf96f8b4a52e85b987f1316edbfb68eeda14521484213bbbb6db6db612139ded090b5450ab4ef520bfdb6bda9ff79c1b7d37ca977,0xee9129a8859b7f8d986973a5cc7ea7c3e94a69e42c94fc6951a937f8bf5b5ddddada28250eee70441478b54cb29659ae262cfcdf67edf97cb9735965965c55d9fff,0xc6dd155d6da412e92d0555774d866ad3356dacfffffbefb3ee7ffcef5deab8,0x7bdce93bfa7def33e94ffa53f7d97f08] gz 11 48 36 10 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz11_84 : block gz 11 84 36=true :=
  @streamBlock #[0x70afdfefaed0627288edb6fefab6db5f8df91e9fbe4fbffff3adac07c536df8a7e2fe2efffd20074a569ffeae053c7fffbfef71e4ff9c07927ab537ef93feffff3ffdf,0xf09b78c66d9b66db6fc6db61b1b6db6d9ff5b7b9b66cd86d8dfc7e36b6db375b6d9b485c29b40007fffffadb43ef81fffff6827fbdfc020091dd1,0x7f828de074a898bb5b74ff76db6c6db6db76bc07ff8a0b6df8829898fc68280b5efa55bf5ebdbea147ffa97defff0,0xf6caf673e2cc75c4ee7fa428001b7ff6bfd77b4cdd75b31f8b8d77b6baddb4145aaf7ffd7ffa6dafeae97af6bd0,0x1bdfb6ddc5fcb76fffcd31f8989cef5edaf6d73bbd7af6b87af5dde9fed7b52ff6bbdb7ffdcffff,0x374e5b0eed717f5ed57a24925efffff9294a5eb8fc4c7e24955680524824925debbffffdfbfeffff4d4aa7ebd,0x78e054ba6fd388074f9dffc3ee9f96db31b6db003852e90e1293920000659af59a907eff9e1fc2925cf54e9f,0x3b86d5b6fbbbff1d7e39c1abeee2ab55ce28c69bb9b6b88217770bbba426db0521777771c485ddcd21485203e290a680c9932cd67fccfc989c7e4c59acb3f2ca99767d9659,0x1f59b76d19b6eb6d770d5d26eb384e1485ddddd967e5fff3ffe17774bb2eca6859fff,0x90e738355ec92fefff56fd3273b36d] gz 11 84 36 10 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz11_120 : block gz 11 120 36=true :=
  @streamBlock #[0x60007fbfc7bc38f0dbe3d499410568aab6da94bdac36db0db600c36db6c36db6db6db74aa0a5b6a429a9a295414a0294514a04aee4bbd28a294052aa8a5336db6db6dba55514adb6db6db6dd28a296d7fffbfe528a294052aa8a5ab5e9eda55514a00055014104927cfafeef415400000001c93c01f400000050008a5ddc9389f4fd3fc0a00014aaa2954a0d0ad1556d76b296dbdadb,0x5000050007ff78051800283000f88575776aeae6aeaeed5d5cc9a4a8f4f5e7a751e9e95d5dcaeae00aeaee5757128a428844d2540d268f4ea269340a00a7828009725dc0b92eb682e0bb89725c4b9271dcee12e49c773b89725dc0b92e1e5c8a5ddc05c938e9ff7fa7e9fe,0x4a2d20800ff7fe4f800ff1fe252d20980c452de7e497930007c46beaf2bcaa4f54a8254aa4234f2a3d3d1e9d47a7a575395d5de015d4e57572200bebd47a7af3d3a8f4f40003e80000520923a4e952524923a4e91292411d2748ff7f93e1de4e49ffe07f8f,0x50945bcbcbc052bfdfffada1edf05094b442740a1e5e52d104038d5e55297df5f2a552906a5420682b517a7a1e9d6d7a7a57577a9aeae0057577a9aeae3d70bb83415be9afa3d3ada9a0d02ab80055700148294d794a4885417904926dfff7ffad51f5dedf77,0x140014a78aabe7d7bc1401f341438000c4a551ca5a551ca5528f72954a134a5a5525ca500a5525ca5b5ebdb4a1dca5a50f4a5a5525ca5fa529fee555f57db5efbded,0x2592096790f7ffea74bdfffbdc3b9d276704b046c2eecff2a5458200e1bfb7eabedfb7ded0d55b43685dea5d5ebd77a977a9757af5dea536bd574da9b5dc03daf55eda9b5ddd146a28bbd0babd4d086843ff7ffd6ba7fefffdf738efffe74dff,0x15d5dcaeae00577b5dddd5d34ee91c569d5d5dcaeaeb5c36bd4fca6bad77726ba9c0b4b535debb935d35dc026bbd7726ba6bbaa429a9a9b5ea8536bdae01ed7aa9b6bdae1aee9774d77aee94d74d77f4d77b5ddc2e9ae9a7749bd5b74edb,0x134951e9e8ac6a6b1f97df3d7754f8ff7f9e9d47a7a7177a7f8be355e9d40311f6a6a91b5ed4bda9aab6bda93bd4baa35ebbd4fffd4ffbeffa2f5dd53e09ff5ddfe977,0xd11108d11e4cffd7ef8ffcffe7177774b8c2051184446e8584a1a881610880e91ba1a146d0d440d0a35d144cbbbba5d7effdbf7cfbff5ffccd777748529754d,0x4a24a211289e5e47fbfd9ff1fef7871e1b7c7a9] gz 11 120 36 10 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz11_156 : block gz 11 156 36=true :=
  @streamBlock #[0xb405b5ed18a02da783fd1636d4d5a4ba6daf5edab6985b6b0dadaed6d8d876b0db6edadbb5b6636ddb4a30f6da2d242c7aeada5187b6d14332d5b56d0053bd005ab6ada00a055a0a50b4df9b156829429b376a6ad0adaf681474faada9ab52b6bda0516bd5aeb6bdb5c5b5d6db5ead75b5edae2d0b5c1d6d7b6b8a1dfffff6d5ae0eb6bdb5c5a00156d0a2d0507bfe8055b428a029414ae2dfb4121dde8a5052b8b45a9ab42edaf6d716da966ad652ecb6edaf5edb6bd02d,0x96514a0721623fdfafd00a00e0eca2940d81d801451f10361e018ec974b8d838063b5749ba134ea007a709a75003d387725451c4bbbd03b92a28e5772347d054503b9efb9c00d054503b9c528295c3dff7be29414ae1e82228a252af5e2838a289492f5c02280a4df7a50714055a9045c15144a4974b87fbd7efda0a124bc9777f7,0xb52960560051fed3ef0a3dfff80b529605636028f8a2c00c6f1bc5fc7e216c02002fda9004800b6d0934296ba2e04bd04296bbb813680109000dae00e1c02dae0297dfdc07aff0a5777702d0055b42b8f5e02ada15c7004bfe170bf6d00254a52e151b680254a52e176368400941ffee9f7857ffdffff,0x8b03d4b4528b446f223ee838f7ff6fbffa3f110b03d0b0a42c2344db6c2c07016101612a2d11b6dbbb2200294bdfbf4d5dd9201294bdb434c34aa5ae17026d28aa5aeee04bd24111e28e0d7a00e1c51d6bd051485d47f70ffbb8a9094ba8eeee94bb874936b83adaf6d772ad7075b5edaee5a10b911c210852148428d46bd17a4471fffe1ffbf7d3fff6fa3e5f9,0x5a075b5eda0bff6bfd5aeffb6bffdb6b817858da075b5eda02d038b68b687055b4a03db6b8e8eda501edb68cc5ab6ada0714b56d5b40e28ab414a71e82ad052a8eaf6bd5aeb6bda057daf56badaf6816d7ab5d6d7b6bb8f6d7fab5dff5d6d7f7fb6d77396bd,0x61181ad28a2ee06858bf7bffff1ffd1dce077f69189add297700db691890dd21dc1e43ba5b6ef57c00bb874be8ef542022ee2a439535ded77701e922a6bbdaeee03d241ea527140ee701ea5271415c74a5210d44297774a2ee1d24a7fdf7fffc74fbffd79dce3c9d2eef,0x91451cae01eb14a4ae0e35c7025ed77071451cae5a070001c7a97b5c0f29028eb5dc01d2051d6bb921ae1ebba8025e9c0f5dd402da3b8774a4e28eb5dc0fe9495dbf0fae3870a5ed77,0x296ba5c0b4f2574d77ae3de2e01e3dff4f10a5aeee03d2852877700714bd31314d2ab8004bd3c8aae002da5a54d77b5ddc097a495d35deb8ef5fdc01fe97bfef,0x1dcd200d1a5790ef5ff96b8bf2efea52dfe94fbb9a401869423acee37900030d0a6214a558b6ef69212d762b217485d352b4294a4ef6bfcb5d2162b3ee9f74d4bffd29ff,0x2211206a528a514512bc9fe3c645b7ffcf7fb20ffff39] gz 11 156 36 10 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz11_192 : block gz 11 192 36=true :=
  @streamBlock #[0x3a5d01101b1b1b1cea8d2c25ad999b6d59b6ecd86c662c75b6cdb28036dbf6db6944a31b6db6db6db6d9b6db6c75514f1d54057b6bffcaf5344a6a541edb4ffff03daf4001d36d1c704db4383fde07e800900ff7b7c5783800000e9b6be8004db40a1d36d5af688a7cf428b941168fe9a8d5,0x1292209bfdbc06cdda94f9efd293ca9b36dbf9f8fc8336dda94ec489916db6f683d7b47efff7a070d4f6861d74824dafffae39369ed74a5dd3e7a74d775486bcbfa69f6d4abd0a40fb69ef80db494813f7fc94a4094b82fd054b82a8949e51a8a7fe9ffedf007ae2d4a7dfffe9f,0xf2c0f7fcb9cdb577f7efda41e8b601b36dfc5fe46db9dfe2fe2d16c06db6f4c5bef6db77d9ed62b6d5b1fc7e2db76b36dd75cc5aae90a02bd054a5ed0ab5c155ff7feba42800bffe001705af05c151705f7f7fb8057af5ffefbdd20a,0x344ff06ff75ce78fe9880de5b331316ae2cc462eb9c469bc9baded071defbfd1e81c1dfe2ff12ba4295c15ed077a07a11e21ea100400002103cffbc3bdfffae9ffff5ae7087e87d,0x11041404abd70e5780a82ad7495eb87f9a2940f47a7ff000f47ae03aa82a8af5341eda1ed7a7a716da01b6877b687aef6a527aef5c3ffdfaf,0x3790d3915b460f4dfbf7fe7fbfb454e098db7687b54fe2fe2d1bc52e0a9b76d0776ffef95eda0edda6cc4c6d3151bb6ba4e4dae93934b6db6a5ddedb6bbbbda886bb8436a8ffa7b7febd2df7dff4df7ff7,0x5724f4798f7e949898947748724edb18beb71f89fc529ff2a2939b7b41d2629f8a5262e97b41c4fa7d29796d24f4f6d39ebdae94bb89659ff4b2cf853e97fa2cfb294b2cbda8ba52ee9,0x2ba42b6fe598371710ba5eba44d36eb82fb7f744fbff0ba5eba4eab6b1429770bb9adac5614bb85dd9d749c9acb85d2cbbbb3413a59acbb2c85d2f5d2049a,0x7b4657b5ea7d2d29502b85d2f6b30deb194f69e921a52a5ae14e174bd740a7b683929fffb7ffdefbf87df70ba5eda0e,0x3cbc91048b3f7dcb7c751e9fffffffff97bde] gz 11 192 36 10 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz11_228 : block gz 11 228 36=true :=
  @streamBlock #[0x790299b1b19a9ef04b6db6ccdb6cdb3538fc4c412db6d9b37e96d98db3e2936ccd8db3c149136d72daf1c00ae1b445c0868e3bfffffffd209,0x3c0066c6c6141bb6db66336db36cc0accebb6db674d9b6c6cdb36db6d8db6cc06057594701c77b6b9ffeda0282497385a1028282d7,0xffff5a364d06c036c6f9f8fcdb59b4ab6eb0a6dd6f1bb666fe4d9bb6a807500550efffff5b68eee94d74a85705a,0x5f97cbd92eef6acf556d8c462e262d277313ad9ca8adbf96ed4dbe2ddd6fc634b7dfefff0a52eeffe9fffffb6bbfeda5,0x3c7d263bfdaba8e1cd9d6663b938b738ee53b66cdeee66e2e2eedcee3d352f1dffffcf5edae4bbd71d2eee,0x2bd3954e29b7c8dba1b6dabd39cb4aadc99ba1b747566b55dbbb70a2bdb4e3d2d725dcef6bbfd10e1,0x3c28fcf4ff35691efe35899b6518bf8a2af88c5992d4ffccd97d2311ea7c90928fe8a7d17b5fffff597ba4919ff7659,0xddb6ffd9297bf3f88099ab6db76efe262dd2931371f7f40fbafeb77e5f10bd7bc14ba4cdff6513a7d3fecbd965965967e81485965d96594d,0x3a61efcfcbf95a7f1f895554e76e84753dfdb7dff9450552a49d6b265965965965ecadb5967d964a7fb290faa6fa5d27,0x33f7c2f7f1fe79ee1de50f] gz 11 228 36 10 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz11_264 : block gz 11 264 36=true :=
  @streamBlock #[0x1e35e3de4b955bb9866c240b336eb76aeb6e19866dbd6edfbd0d9d2d6a77ea6b336f6dd6db7fffffefffa57bfea25fdf6db6ff81eb41ddffdef80972685e8eea287ff7fb68242,0x7797fffabdff0e3ac50dfcb8fcfcabd31310ce86666dbd066aed72d25edfa36c76d75ab7feb6bd3fdc1e7b6fad7ffff95edff0396db6bbd0ae,0x3c9fed1d586b5feffcdb759dd6caa6262fe7e262dd76b7d8664b5fa6eb71cb6d3b92ee1edbf6db6dafffffefff,0x5b4e4b817bf6b5fe4f96eda725c389da313967d0e3fa7cff12da7725dc0bfffbffd3fe97f2dafef,0xf7fff924dbe73b8f7ffe7f2e3f3f2492e9cff2df171f96ae0512909012ffff124a6dff4bba5dce0afeeffff,0x3fc5af4ef4c915558d62ac16bd3b910283b6c6dd79c1c00b6bd1ded74a48a5dfe7a0aa,0x9f971f9f97fbb527f8b5df1ac62626262f898bb462f89fe2b98dbf66d8df13148ff65967fffcff459b52fff67fd9f1932cb27dae,0x1ed84da4789f17e62cc7fe998bff0da5851485b7b71f7ee2e2f61f7e9adc4dffeebb19dae2f83196591967d965967ffeb2cb2cfb37d9659f67ffd3f7d59,0x6cc5f97f169aeafc5fc8b5fe59b6e8177b4d757d80295c6d7b48e2cb2cb2cb36b2c996535955acb2cf8f1dfffffff699649,0x19f67d9acff859f78f13e65fffdffd933e] gz 11 264 36 10 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz11_300 : block gz 11 300 36=true :=
  @streamBlock #[0x18e15bb5b0f4cedb666e39b1b6e87a6edd18dc74effbcced6d9fdd76999b6dd7fffdaa79ff7c75a1687ffbf828e3fc28e3c012e3bbbdb6dfffff7b6db5e87ae,0x7efffdf40ffdb6d831662fe2e2e200dc4c5b6dfffbf37c426277ff3c7700bffeffff003ef87ffdffdffeefffee01ffe,0x399fbbb86c5736674edc5fc5ddc6d8ae6db2d16d52da5adb30db31bb6c5aa2a84bba6fbd5ceeff7b7fc0f15c,0x5a39400c4530ae9311d15c46ca6716977aea6ad99855050de2ab2fc405aab697c4d53ea83fffd352ef5c9,0x55b6db686f7e53652ada2bfcb72e2d6b6ed6d3bb4edd96aab85a5aeab6aadb7ebdae9fbfe7f,0x1b1dc256d18576d99a217701ed0854d5cd9d6dd7af3817e23bd1e80a885debbc4d50774bbd7a10ad7,0x12f65bffee5ac1c55d6a7ef6d3171715ff198be6a2623aef9f99889ff389224a4a5967feb2f6df7a7fdd49659652f0a7df51f7d,0x616c263fd262c0c7fed82ee211bafce3f2e2e29f6f66340dc5c5b8affd6dbbb7edb4bb839a7c195d96597fffbd3ecb26597ffff0f2ffbd9f,0x1694e0777b680b6b8a6d383bbad3fc8f53ffe3e46559659659652ee9197fbbbbdfffffff64977a965965967d9,0x2207fdf642cf8c9dffc9020ffa] gz 11 300 36 10 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz11_336 : block gz 11 336 36=true :=
  @streamBlock #[0x123fdbca00051d1c5fc4750cd862b3bf3758eccc036d99b6db6dff80010a42e005a3ffd4ab5fff7dffebff7ffdffcf6fdfa7fbfffdfe7bfff54088508947,0x71c50ff673ed780e9cd5831f96ef9315f9018adbf6cadb2ad137ed54db687ff3bd1d3ffea7fffb8047141feeefffe9b6dfbff40,0xa1c3dfbca3fbf7b6a6766e2cc5c56be462cc69b0f7d6a8efee6238a50e26befffdb5fffdfefbffdffff,0xf7ae4b82893de9a9394939548be7e4e24d4d5f7ed4a0f6ba52e7ffa914fffdff7f7ff9352ee9,0x7bf7fbc7fea0ae5fff6cce4e2e23f971a05751bfaa0394702bfdffffff527ffb43ffd43d75a,0x15c6a8550f914a5f0c4e16a89f951438074edb6db770aff5e8774d513fe14f68a5,0x924f4e3fcb800280ad1bb8bb36f60c974609a1892a07a596529242f6b87f70336d4b2c8905,0x1b75badbff0606337ee6db6ddaadb899ee8f68fbf7edb8bd6db6eec3b39c42eefdf2e2f9717499ff0cb2cb36ab2ca2cb3ecb2fffecbfbfbb2e9,0xd94ea9b5294aaf59c5b651edd1555696d3d746596596593265965932cb2cb368932b6dafffffff6bb2cb2cb2,0xf0c83ffc1597bff97fd919] gz 11 336 36 10 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz11_372 : block gz 11 372 16=true :=
  @streamBlock #[0xee7efc6ddcc59fc4377ffc005ffff1ee28aef7effffa3e0,0x7b00edc5831980acc180e156bffffd5f405707,0x67f7db6c66634c5d6d82fd6625600af005fbff6d,0xafb689710c6dffffbe079e9fffbefb6fd,0x3f3fcfdb1b8b9f9389b8b6b5c5a0052fbfedf7f25ef,0xeee0f4ee3bba401dc77aeee97707,0x1ed1342d442ac31dd981969108951ce,0xc04bb809776db6da59b6db6d9b6d2cb232259574bd7659,0xe9671b68eadac62dff2da659659aacb2c9964a5a64,0x1fee7f9ecfb3f59] gz 11 372 16 10 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz11_388 : block gz 11 388 36=true :=
  @streamBlock #[0x6db6db6db6db6db6eb6db6db6db76ffffffd,0x36ce5b6dcb6db6db6db6db754a000,0x36db536db,0xe5c8db66667200,0x36dcb656db,0x1f2e4,0xf0cb6db6d805,0x1b6efdf7fff7659659659659659659,0x37effdfd6dcb72e7e5fcbf97ffffee5cb972e5c8032cb2cb2cb2cb2cb2e59,0xe5bfffadfffffcb6e5cfc9f2db9f9f972666,0] gz 11 388 36 11 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz11_424 : block gz 11 424 36=true :=
  @streamBlock #[0x1b6db6db6db6db6db6db6db6db6db6db6db6db,0xe5b6d9b6db6db6db6c0a,0xdcb6dcb6db6db639514,0x1cb60,0x36cdb6db74,0x1b7239a,0x6db72d86,0xdb75edb6dbdb4db659659,0x1b72ffdbf96e7fefb9f6dffcb96db965965965965eb2c99659659659659,0xf9f96ffc37effdcb7fee5c4e5b73f206dcb72e7e5b73f2,0] gz 11 424 36 11 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz11_460 : block gz 11 460 36=true :=
  @streamBlock #[0x3972db6db6db6db6db6db6db6db6db6db6db6db6db6db6db,0x75b95,0xe2c36db6c6db6db6db6db6c00,0x1cb90390007272,0xe5cb6d9b6db6dcd0,0x2d39,0xe5b36db6db9add0,0xdd6dd6db6c7bbfff5b,0x36dfbfff7fffeffedb6dffb7edb6ee5cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2,0x1f2cdfcb60dbf97efe5b73f2ce59b72db61b6e2fe5b96fe5cb,0x5] gz 11 460 36 11 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz11_496 : block gz 11 496 36=true :=
  @streamBlock #[0xe5c5cb6db3336db6db6db6db6db6d9b6dbfff5fffff,0x1b6e5b6db6fdb6ddbedb673fc,0x36db8b97edb6ff,0xe46db6dbdb7fa8,0xdc9d,0x5555aa,0xdb6db60ffa,0xf96efffbafd36db2cb91b6d9932cad659a659,0x6dfbff6dbe8eb36dcb72e7fffffffdffefff90e5f2e5c991919659659659,0x66fffd9b6d8e5b72e5c8cccdb6db,0] gz 11 496 36 11 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz11_532 : block gz 11 532 36=true :=
  @streamBlock #[0x2b0d8db56db6d8db6db6c51cf800ff,0x6db6db6db72db7f5b6db6db6db75b6db6efffdf,0xadb7,0x36d999b972e5800395,0x6db6db7eee1b6d9f5,0x1e0190,0x6db7256dfffd,0x2dfff7f7f6dfb77edb6bb6cb2cb2cb2cb2cab2,0x6fd96db6e7e7e5b97f2fe5ee7db7ffe006dbae5cfabbb2cb2cbb2cb9659,0x61cb7eedfffb3330f96df2e5bf972f9,0] gz 11 532 36 11 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz11_568 : block gz 11 568 36=true :=
  @streamBlock #[0x2ad6e6fcd,0x1cb96db6db6db6db6db6db6db6db6db6db6db6db6dbffff,0x1c436db6cdb6e4db6db6db6db6db605a0,0x39725072e5c802b972,0xcb6db6dba6db6c8,0x36db672e6d,0x3a1b0,0x7fadb6ddab9b6d6e59659,0x36db6db7ff7bfedb7ecffb8b6ddcb8fcb9f659659659659659659659659659659659,0x36dffcbf96fe5fcb7ee5cb2c36dfcb8b72d99cb6e7e5c4,0] gz 11 568 36 11 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz11_604 : block gz 11 604 36=true :=
  @streamBlock #[0xff336db6dd36c5fafff,0x1cb8b972db6db6db6edb6dbadb6db6db6db6dbb6db6db6dfe,0x5ad81b6dad603d,0x3636de0e66d,0x31b66db60,0xf96c6dcaad,0x1fcb6d8e45,0x1f2cfcf92ddfddb6d9b6dcdacecbb2cb9,0xdbf97effdb6d9df65b717f2d9f9bfffedb0e5cb975b659659659659659659659659659,0x3b7fe6d87cb7f2cdee5b72e5b6db6396dcb,0] gz 11 604 36 11 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz11_640 : block gz 11 640 36=true :=
  @streamBlock #[0x3938be5b72dfcb6dcb336db6db6db6db6edb542d7b6dffff,0xdb97f9fcb6db,0xe26db6db37f2e7db6db6cdb6db36cdd6c,0x7cdf9b4e5c872ea9cad00d850,0x36dbe4dd,0x1ee4e5b60e,0x6db6d9b6e7e4,0xedb7e9f4ffcffbb7fef65932cb2659659,0xdb93fff7cbf97f2db7fff3fedb7f3f2e3ef953939acb2cb2cb2cb2cb2cb29659,0x7cb6e2e2fe52db6d838b7f2e7e5b8b972db72dcb3,0x57] gz 11 640 36 11 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz11_676 : block gz 11 676 36=true :=
  @streamBlock #[0x7ffffbf96596e5972e5cb9ff6cb2fde,0x36cb6db96db9f96db6db6db66dbad6da0b6d0,0x39f9f6cdb6db66db36db6db66dcb0,0xe5b6e4dcd0dbbe680,0xcb6db6db6e5b,0x396db66c6c,0x7b96dc7f2a,0x1cb2e5ffffcb6dd966ffd3b659659,0x32cb2dbfff72e5cfcfdf6e5cb73f3f2dcb2cb2cb2cb2659659659659,0x1bf96dcb72dcb9096dc5b65b97f2df2fe5b3e5bf96cb9f9,0] gz 11 676 36 11 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz11_712 : block gz 11 712 36=true :=
  @streamBlock #[0x14abfffffeff6df3f272e5965cb2fe59fffffffff6db6cb972cb2dcb96fdffefffffffff,0x1b6fe5d6db36db6db294b68,0x3364d4db6c94570,0xf6cb6cb6c,0x1b66dd,0x35,0x3cdb6db96dbf9ae5b6f9aea,0x1972fdfffbf65cb965972e6fdfff7ffffe19,0x14a72cb267e9feffffff6db6cb2e5967e5972cb9,0xdb6d86d9665b659965965965972e59f9,0] gz 11 712 36 11 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz11_748 : block gz 11 748 36=true :=
  @streamBlock #[0x4a9697dff7fdfecd998d9b6ddb9764baee59726634baddad7fffffcc6975b1ab6db72d9675fb6cd134ffffffffffffffff,0x4b18e9b6d98dd9b1d372db6db6db3660c66db6d9b3a1ab0db6db6db6d86c2bec6b94e,0x4b18f6212db31bb363d89b3170b6db75cb3660c66db6db66ce86acdb967e5b616db6c50c5ab52ae,0xf5251fac649b73a8c4d8c36292f0cedb70b92498d49a5db972dbf549ffe9,0x3a92b5695cea1471b6292a5a577739534753b495,0x1788adebfdbe2d9249d6188c36e40667fbe2db694a4696ef20c59b6fcee,0x5525150af8a2aaaf472d3e7e2149014b69e5e82e5a512,0x5622a2a776c4fe289a492d1cbb13f9316c141ddb154a525a772ec4e832f7d9659,0x15496e358f311972dabaa963178bdcf6fffde1d24c318fb72cb6d6b54a2d149be3f2db7ffefeb1965964d9,0x6301f10c67104f1f895db776df5dff7ff0c6880620c601c40bedbfb7ef7ee2fee2ac664d2fdb1ffbe59,0x25944721e19] gz 11 748 36 11 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz11_784 : block gz 11 784 36=true :=
  @streamBlock #[0x16a6a47f9fffecb666db6e2c72cb96c6755fffe3326a59b6db6ffd9b2cb6c6fffdb6fff16dffffff0ffffffffff,0x3c0371bf8fb6c7406d8d99986db6d9999b6db03c37fb1fcb0245a17fbb8aaf02a4f,0xfe461c0edc435b76c06ccdb0e336db939b6db19b33d64d4ed815354ffefae550f,0x28348c876ba07b69b3331b66dbacccdd66ce5972c857611af434ee,0xab5477e2e2eba81c5ba16aaabdb4a61522a6d,0x1d78ffa8ff6b16057233a88db612dd84626db380dab47777,0x13aba2c6f49038b614736f4297574411d36d0a9b6d,0x2f138bb94e290514de27051dbfec0570d92d89f8a2e13adf481c659480dff5b7fdd6d9,0x1873affb71f32e5b71cc4037fbfffdfe053f36d170ee2e7331f93d99515b36e59659,0x66033a2256e2ddffff6cb0cc01987128afdb18a2e27974c5b720ccf3e59,0x72cb2659] gz 11 784 36 11 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz11_820 : block gz 11 820 36=true :=
  @streamBlock #[0x287fc7fffb76a406cdb6dbb5262dcb96436c01807ffdfffc36c36c6285b6c2fe4ff6db06dffe3c07fffffffff8f,0xd800012f94b6d800606d836c366db76db6db6db0db0d9b6dfe5b6db6db600d8970f5eeea0029fe002,0x600014b5180012db0000125000014b96f34048094af800,0x2800507c4206c25294a52976f5c394a529aa6c1b61b36d9b6db6db6c36d294b75b6c1b6cdb6db6d9b3304a44d086d485c,0x5a001457cf96a5294a5294b9ea4ad96a400055a94a5294a52f5ea6ab6d8b6d7,0x7a30c65621ebb6d5dd7adeb73154d56d85a9030156bbd7b5ed7714d4d7b68f47aef6d,0x50007097f88a94bd77aef692ee76e6d7265a90003b2d4a5ebbd77b5d2ee976a9b6875b6d,0x3e818c5e217e3e1362bbd775dd7315b57fddb7582d483019fc46d6bbd7b5ed7714d4b3fff7b5b6c47fcffb5b659,0x14c63070d8b96e5b2db2b4bb776ef6b77f8b6262ff36fdfbf2d4861986d8db5a94bd77aef5bb73130dbb5bff65,0x6036cccd2c4c06d999be2cf962dadbacc5baffe2d80db3334f1376a436cccd78fc586fffedadbafdbaef1bc46d80332c8f659f9,0x659000032f] gz 11 820 36 11 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz11_856 : block gz 11 856 36=true :=
  @streamBlock #[0x2801c5abffe6c1b6db6db6d872e5ca801c7fffa8d81c6db6dbfffff36dcb9723febc01feffffffff1ffe00fffffffff,0x1bf9b6a99b1b6dec5bb6db6db66c6db7f16e72db6db6c17db1f376edb03b9ddddceeeeee1a01c1,0x1198531b4d8660715716dd0830ddd6db003335adbf286807be97d,0x531660f71a626c6e2fe6d71a3138b8b752c632f1fadb676db5df95e26ed6fc97477,0x134012e93c2514fca6b8d38ec74d004ba4b6db437e4e03a6b619ba5,0x1dc00005b6db685f9b6fcdb6bbb636db345b6db6c76ed6db668b95b5db6db6c7a77977a1,0x5005a170ef3f262f5ea9ddba00b42e2db6fcd71539b6dbad9a,0x1cf401731710d31a2d6db7eee35801cf5b36b6dae3422b6db0a9cb9736dbffeb59,0x3a900b7fdda72dcb67c4c7e4c7e37e35462ffffc7b3efdfd6015ffb6db1db6df9ae26bc4db6dfd659659,0x6ccdb16c4623666311883e3e945b4b317fffe0d99be29e206ccce271039bc56b75d7f1f8d71765ecb2e406591ef659,0x1ef32] gz 11 856 36 11 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz11_892 : block gz 11 892 36=true :=
  @streamBlock #[0xb405ebbad29fe6db6db6dbf97f2f972f9b41ebbdbffffffffe00b8e016ffffffb972edfffb7fe7,0xf140f7c8006db96dbdb6cc66db6c6db318db6db6db6ca596db6db61b6b4b9763daf451409b7ebffd7df7f00f3fdefad,0xe91c40006db360937e6db6db6c3a4d9b6cb6dfcb65b6fe03ceeb9a912f49f7b56f929a97,0x113c3e52e01b0679b6db752e6189b6e5cad6c3854df,0x283bd77b7cf94b80740f5dddbeca97771c1dca8d,0xf04dbf7fffc7174807ee42df6fff595d29a30ded52bd,0x3e4503c636d00cde00028b6d00c36d4bdb4a49c9b2a4,0xb6d4bf84ae9007e00eda97751095d265191ffd15cb90869ef65965b,0x1fc002807af9b680f3ff9fd7edf7f7bfb6d98cdb6d98db6631b6db7f595e2ef1659659,0x501800c4dc4b41b8bbf98bb7ffe00d470062981d7773b60a4c9964c8f64f19,0x3dcb901cb97c8] gz 11 892 36 11 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz11_928 : block gz 11 928 36=true :=
  @streamBlock #[0x2d2db4e7c53768dd6db6db76b96aaddb6bbf4d98eb6db6db6db6ebd6d7b6ff85a5,0xdb0e2db3e2db126cdb6db6db65a6758108696d5b690b6db6c03772f943c,0x3fe3ed80db6db619b32db6d8cd95b6d9bbbbbb857dff705,0xc063036db6db6db90078006dba050,0x54daf2d0a2da9b6f9685,0x3c84fbfe1dc1eb02dbf7fed3b83d0,0x170012904b6db6db6d6d0aa4a412db6db6ea5b,0xe91dddcdc8ee0edb5b5dddea9dc1db6dbbbbd659,0x5a01c7cdcd6c06fde7466cdb6db19b2b6dbb32cd659,0x30cc6199b6db65fbf97ee5bf716575b9746d8666ed33a6db6dc5fb717f3f2dfcb7ff5d6dc9ec6c0cb,0] gz 11 928 36 11 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz11_964 : block gz 11 964 36=true :=
  @streamBlock #[0x1b6db6db6db666db6db6db6cdb6db6db,0x6db6db6db6db36db6db6db6db6db6db,0xe5cb6db6db6db6db6db000,0x1b72db96db6e80,0xd9b6dbb5b636db,0x72072,0x36391b655,0x6db6db1b6d9659659,0xdfb6dbf7edb96e4df2fdcb7219659659659659659659659659659659659,0x6e7e7e46fe5b73ffff2db9ffff7f2e5c436e5bf972e7e5cb7f2e5cb9f933,0] gz 11 964 36 11 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz11_1000 : block gz 11 1000 36=true :=
  @streamBlock #[0x3e5c5972e6b6db6db6db6db6db6db6db6db6db6db7e,0x65cfcb8fc9999b666db6db7c9c9cb96db6db6db6db6db6db6db,0x36e6d,0xdb6dcb96ea6db6fdc0,0x3e6dadcb6db76ab6db6db60,0x65cb6b4072d5,0x32e599947272dcb4aaaf9,0x3e5b6db6eb6db1b66d9659659659,0x36db6667ea66c072db7266b2cb2e4cb2659659659659659659659,0x1b26db6c8db6db9f1f2dcfcfcb33336db636db7f2e58e5fcb8b9,0] gz 11 1000 36 11 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz11_1036 : block gz 11 1036 36=true :=
  @streamBlock #[0xe3edb6e5b6db3adbf6db6db6db6db36db6dfffffdf,0xf72dc9b1b0ccdd36db6c6db6f90dc86df83fc0fff,0xf9336db6db6db6db6db6db6db,0x1f2e5b6fa,0xe7dcb6db735edb6dd6db7e,0x3972,0x3c1b6603e8,0x7b6db72fc6dbacb2cb2cb2cb2cd,0x6db6db6dbceb6d9fb639ae40cb2c99659659659659659659659659,0xcdb1db7ffb72dbfff99b6396dcb91cfcb6e4e7e466,0] gz 11 1036 36 11 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz11_1072 : block gz 11 1072 36=true :=
  @streamBlock #[0x7cb8b9f967e5b6db6db6db6db6db6db6db6db6db,0x1f5b9b4a,0x1cb965cb972e436c6ccdb36db6db6db6db6db6db6db,0,0x6dd53,0xe5c8000,0x2b96dab7267354db6d94,0x17e5b6db6db0db6db3619,0x6db6db6db6db6db6da99bf96465965964cb35965965932cb2cb2cb2cb2,0x36ccdb6d99be5fcfb9306db1b6db631b9f9f9372,0] gz 11 1072 36 11 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz11_1108 : block gz 11 1108 36=true :=
  @streamBlock #[0x15b6db6db96fe5b6db76db6dff968156dae,0x6db7f2db6db6dbb6db6dba7a05aa,0x7f96db6dcbb6deb,0x73edcb7372ccdb6e43672f977272e7e5b6cb6db,0x6dd56db6db36db,0x7c9cd,0x1e393330c051472,0xdbf6db6ecb276596596596596597,0x1b6dbf372cfdcf99f97cb90039717165932cb2cb2cb2cb2566b2,0x3f97cb6e3ffef96e27f2dc5c5b72e2e5c5bf972e5c9cb3338b7cb8bf9f93,0] gz 11 1108 36 11 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz11_1144 : block gz 11 1144 36=true :=
  @streamBlock #[0x71389c81b6d9b36db6db6db6db6db6db6db6dfffffdae5575a1402d,0x1db51b7a6db6db6dbb6a8fffff,0x76cdb99bf9a,0x7cb973e6e436dcb6dd6db6db,0xe7e5c41b6db6db6db6db6db6db,0x1c8,0x7347251b,0x1b6dbf36ed,0x672db6db6db7edb6d86ffdbf6dbff964565965c65ccb2cb2cb2cb2cb2,0x1e36666663e5b71fff97236dcb6e4db930e2dfcb972,0x7] gz 11 1144 36 11 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz11_1180 : block gz 11 1180 36=true :=
  @streamBlock #[0x7136d999b6db6db6db6701b6db6db6db6b680014fffffff,0x72f9372dcbf96db7f35b6db6db6db6ed3e5f22fffff8b6da,0x1d6dcb6dfcd6db6a5,0x3db6d5b6,0x6db3e4adb00,0x17ffddb7e7e6b90e56db682d,0x74db6c36db6db,0xf966db6dbadb6db6db6cd659659659,0x366db6db3336cdffb601f3f2c99659659659659659659659659659,0x1f20dfcffcb7296fe7ffe5b8b960db96e5fcb7172e5fcfcb6e35cb8bf9f9,0] gz 11 1180 36 11 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz11_1216 : block gz 11 1216 36=true :=
  @streamBlock #[0x38b898b8fda6c6db6db6cdb6db6db6db6cdaad528f,0x1c5c5b6db33672db6db6db6c36db6aaf6d,0xe5c9b6db73f2dcb6db6db75b6dbb4,0x1edb3535,0x32b661b76fc8,0xb7e6f9d571ab69dc956d5f950,0x726e5fcb6d8a6dbf97c9b,0x3e7e5c7e5b6db19b6db6fe6b6db6db6db659659,0xdb6db6d98d8c36c36cb2cb2cb264cb2cb2c990c99659659659,0x30dc80f97c8f90e2fe7fe586cc372c33331f2dc5cd,0] gz 11 1216 36 11 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz11_1252 : block gz 11 1252 9=true :=
  @streamBlock #[0x3b6e3,0x7b8b972db6dbb6bbda,0x1e,0xf3,0,0x72,0x3,0x3fe5c5b6db,0xdb661932cb2,0x199999b72c,0] gz 11 1252 9 11 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz11_1261 : block gz 11 1261 36=true :=
  @streamBlock #[0,0x2b372db6db6db6db6cc2db6d89a9fffff,0xf6dbb36db6db6db6db18eddfabb921,0x6ddb6ddb6db6db6dbb6755,0x6db262ed,0x159b96db6db6dbb7,0xf9f95f9f9,0x33ecb8b36d9fe5,0x772e5c7e5fb72fd3fedbff77ed9b61b6fe4cb9ffaf,0x673f2d94fcb62df973f23e5cb2e59373fedcab7afee5ffff3f3ff7fffd9ff38a55c52cb8b89c5f2e2e2e5c9cd67e5cb973f3eee7e7df5cbd7aff1eafff67c,0xdcd65c98b263bf2e5c5c5fcd7165b2e7e5cb7cb964cb97172dcb8fcb931f96cc7e5b8b8b2e2dc5c59,0] gz 11 1261 36 12 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz11_1297 : block gz 11 1297 32=true :=
  @streamBlock #[0,0xcb2db6db6db6db0bff,0x193131f96db6db6db8b6db6db6db6db6db6f,0xcb2db6db6db6db6db6db,0x3db,0x1fcb6db6dbb,0x19ffff97f3f3f2f9f9f9727,0x1965bf965b2f9f9667,0xe29a94b8b8b6dffd61f36ddb6dad69f36db7534,0x50a52f9f97b5a529acfc9cd65cfcb2e7e7defbdb5ca7cd97f57cfcffbdcf9cffb2f5295aed4a53f35ca4e3f2e2e297d0fbd4a5ffb9323f3972e7cbe73fee59,0x196e596cb2c72e7e6b898bf965b965b96dc5972db63317e5bae2ce59cb3,0] gz 11 1297 32 12 (by decide +kernel) (by decide +kernel)
theorem allgz11 : block gz 11 0 1329=true := (@block_merge gz 11 0 1297 32 (@block_merge gz 11 0 1261 36 (@block_merge gz 11 0 1252 9 (@block_merge gz 11 0 1216 36 (@block_merge gz 11 0 1180 36 (@block_merge gz 11 0 1144 36 (@block_merge gz 11 0 1108 36 (@block_merge gz 11 0 1072 36 (@block_merge gz 11 0 1036 36 (@block_merge gz 11 0 1000 36 (@block_merge gz 11 0 964 36 (@block_merge gz 11 0 928 36 (@block_merge gz 11 0 892 36 (@block_merge gz 11 0 856 36 (@block_merge gz 11 0 820 36 (@block_merge gz 11 0 784 36 (@block_merge gz 11 0 748 36 (@block_merge gz 11 0 712 36 (@block_merge gz 11 0 676 36 (@block_merge gz 11 0 640 36 (@block_merge gz 11 0 604 36 (@block_merge gz 11 0 568 36 (@block_merge gz 11 0 532 36 (@block_merge gz 11 0 496 36 (@block_merge gz 11 0 460 36 (@block_merge gz 11 0 424 36 (@block_merge gz 11 0 388 36 (@block_merge gz 11 0 372 16 (@block_merge gz 11 0 336 36 (@block_merge gz 11 0 300 36 (@block_merge gz 11 0 264 36 (@block_merge gz 11 0 228 36 (@block_merge gz 11 0 192 36 (@block_merge gz 11 0 156 36 (@block_merge gz 11 0 120 36 (@block_merge gz 11 0 84 36 (@block_merge gz 11 0 48 36 (@block_merge gz 11 0 12 36 sgz11_0 sgz11_12) sgz11_48) sgz11_84) sgz11_120) sgz11_156) sgz11_192) sgz11_228) sgz11_264) sgz11_300) sgz11_336) sgz11_372) sgz11_388) sgz11_424) sgz11_460) sgz11_496) sgz11_532) sgz11_568) sgz11_604) sgz11_640) sgz11_676) sgz11_712) sgz11_748) sgz11_784) sgz11_820) sgz11_856) sgz11_892) sgz11_928) sgz11_964) sgz11_1000) sgz11_1036) sgz11_1072) sgz11_1108) sgz11_1144) sgz11_1180) sgz11_1216) sgz11_1252) sgz11_1261) sgz11_1297)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz12_0 : block gz 12 0 8=true :=
  @streamBlock #[0x141541455a156892494a4139ddc7bffc39ddd54ef554ef5e75a04eb4f7bffce73bbbc0e7038273bbbdefff,0x1415416aa8aaa02908225ddce3a4979ee738ef6a95ed52fff921ddce2bb9cfaee71dddce3fffbcf,0x505505ab6daab6daa90a4294a6bba5d210d27de7ffe9c2e1086db68436db6bbdbef28a6d57777b55dde5c210df79f79fff,0xa028156db556db4148529b48a28ba6d2490a6d24974da46db6d3db6da45145d36bffd14da,0x1415416adb6aadb6836da94d7b6d77a95b51faeb6bbd7b6d77af36da8fd,0x1405ab6daab6da49290a52949294528a292428bca28a49fffff,0x1415416adb6aadb68290a4294a596594b29659,0xab6daab6da,0x505505] gz 12 0 8 9 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz12_8 : block gz 12 8 36=true :=
  @streamBlock #[0x5aefbaa7efb333337a6ba5c3f7fb6db6002d752eaef5d99999920666d9b24edb6d16db6002fdf7afbfdd9d6675fd7b68bffebfedb6d800af5c9573bd675999a415db6db057ae9aef5b6db6db6db6d81524bd5be9a1554e36db7aee976db604fdb5346db60573bd5aef42aa836db6db60000bf7e97effb82a8fffffff0015ebd2bd77a0aa0200016d7770e515545aefee9000b6bbb8728aaa2800057b7fd5fdde82a9cfe9b6ffa8000af6a52aeeef4154380003efaad79c50551fff5ddfffe000f5d569d4501400003fd7d36855539ffe1eb97c000252aef6855500000aaa15ee0aa3fefffffffaff800aaa14f4154040db6c0af5d2957777a2aa80b6db02fdfff5ffff71554ef,0x9ae9755aaf331bfefa57efd77cdbf7fb7aeeeab54e66306d7754d7aea4d9b76db92edb6edb69e4f2f29f7eceb67fff7c97beffbdffefdb6dff93effb6da092174b7675b34429ae4927252db6d85214b6db6974a5d2db6d81dd2170450aa74d3fbfa52e4a6bd4802a7aee903ba52e48a154ef4e977739ea5d203dfff24e9777aa95ffeee4bfbfbfdea5d249d2ee75529214bb92e977251b5dded74d24ea14482daeb6d777b5d3493a85282daeb7edb6bcff5552bdeffabbc93ffffbdb6d0474aaa94f6bbab9c38ff77bff4f141ff69cefbf7febd7f874bbd4868e28029b4e73937ef9ff6bd0aa553ff93fe9a9715ea4486d7a154aa77725297a73d4ba5210a42e93aa948852ee4a52ee4a3f7fffffffffdeaa57ffff93fffe9ff,0x26b8aed61eea976afa57ebbf46de75ef7e4d715dac02ea976aa2950d7434db6c2968a42c2dbaf43cabd61effeb4f7dfdeb5df5d8fffaffff5ebd08abd60170a2b4f517082b5c611b5d810a35d1086bd601ded703d3d4da74df7f74df70402bd03bdae07a7a9b4e9a970ba685c88423ffc255e8554fdb4ffef7f4d4b8e1084abd0aa90db4eee0b85e9d5dcb6da0770902adb5e95dcb6da0770e055b6abd34aa50fffff4dabfeae4bcffae14d2a94021485d36a842ae48201ded7a0aef547b5dceb5c03bdaf415dea8f6bb9d6b910840a36bd00852145369d14521085342efff3fed7a1ffffe9b4ffffffe9bee,0x25d5697eaad57f6d555b58f0fe8ac25d56953556abb6d555b58ce9d5cb4169cf2f35ffeaef5effb5dcefbf5dfeffaf7febbff8b4e451a4521577a44886d77383434ae8a24435ea20d77086940ef42e24953d247b5dce4d700077a17124a9e923daee726b80211fe73a6bffcaf5effb4e77dfa02139d341484af41221b4e7041a02f6d46952150122941b681deda9a5775028a53ad16d52bed577af3db542abbff8b6a94f6abbd3adb542a8085dea28d2290abbd224436bb9c1a1a3fddeffd7ffabbd7bfed773befd,0x26db582db7dd53f7edf4ab7bcecf7f9ffa6db582db5175746bda14ab0489d8c288510985175eda66d3ff6bdffdfef6fa853b6ffedffff7bf457b699b4a2f691745cef6d0a8539b75b68bd45177a1a2b6c149014abd3df4d54d577bc70b80014901757a7a17aa9aae091029b680a6da00b86daa90d0a5e842ae09273a6da0777b6aa5ebbdaeeae70e2bdb69c236d771e50553aabdb69c26daee1ca0aa28536da440a2f6a28851745ded0855c1227f4db6bcfffb7fffffffdeffabbde7,0xb5d2eab5dbf5dd9e505b6bdaddde25af6bbbaad76bd77639416dab5b1bb75b4dabdb54f34f37fce02452bedabb1af37dc02fdb5edaa4d26bb9c0a294eb6a6a6bb815e82d70d0692f4040ab6a5e80000b5d349a77a1c0ab6ba95dddebbfba9e9effd0a2416df5b5dddd4f4f5de85282daeb6bbbbdae9a4d77770e5156d75b5dfded7d8d3cdff771e2455b7ded,0x9ae9755ab7ed2a6dffbe975efd4df55bc5bde297ae9755ab51b4a9b536bbbaf5eaa58f6d76ee75eda49d297fff2a7dffff7def7dff24e97ff27fffffffffebdb493a5dc28a2548414bca35c89122452974b851242145d145144073b9d24d1ed4d3a69ddfd29700e77749201cee749347b534ef4eeee939d145145d14514493a5dc28a35521a14bca2ee45d17448bcfffff9274a2ffff553f7fffffdefffe9ff,0x55ab55d5bf6ababf7efd001be9bffc055ab55d5a1b55d546a35e6935d2e5f7436bbe60b0a28bcb606db66db3366dbadd99d6c0db36db6db6db00000294e0a57b680080340773801401b6dbba42e0a497a7a14d3a685d17452f2e6db6ee90b82925e9efa69d37dfdfd3ee,0x16db556bb55bba974ad2ebaebab6db5ea6d4db6b6db6dbb6daab56a9d52a5a955552ad5abeea9d8d2ec52bf7ea848e2b85a15eda793cbca5964c5932ecb266f17166b2ec9933594d7b69932ca5964c5932ecb266f17166b2ec993359f9,0x4d74baad5bf7dd53f436fa55e6fdd8d4a6ba5d56adfbeea9fbff7d2bf7efdf] gz 12 8 36 10 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz12_44 : block gz 12 44 36=true :=
  @streamBlock #[0x3b7c75b31e5e7cdb638005f2d49fe7e36dfff9b6d2f5ed29daeceb66385cdb6cdb0db6ddadb636d83acdb670b9b6db6db6db6db6db75bf0e9d6ebd168ae14a13bd36cdb6eb6e1d3add7a2d15c295b6db60db6db6dbdae909ae9ae4a42aaeee8dba1edb66db7b5dc26bdae74baabbba36e815b6db6ded702a6b83e93570700fff1fe73a7ffded702dae70baab8500a16bd5716bdb4f5d55d27ae2d2bd3cd7b4f55c5af6d3d755749eb8b4a0f6b826bdaeaf45a3d0b4aeffff7b5c135ed757a2d1e85a50557f09a49df7d5d71e85a5be0ff0d5770f54e7aeaae3d0b4a01aa84d0053254141dffe3e9fe7d550f40142541428294e86aeb051d39c00f5fbe3d78a505b6828a75000f401e8f6bb84d7b5ce175574b7aedbb4af6bf84d74d77ffaaba5bd76dda5,0x1ed466ccc6ffcd7cb5207b1b6d8dff9df78096accd998dbb9aa4b5206adb6db69acdb636ee6080adb6db04d958ddd15453ded1e8d9b7e49b2b1bba2a8a57b47a36637436dd36dbca52bbda1c212a80b40494a5af687772a80b4a7b6a684e0a577b46e9f14af7c7af78e0a5af6877714af5c7a0a505b683a2df7db4b457f75282db4145a15b69681c14b5ed154573e840e4bbd79c14b5ed15457135c014a1d687f487878f5e97df0a51568777048047a0a50287772da7d0f4e014a050eee5b44d0f424a52d7b43bb968553423d3ca52bbda1ffcb7dff7c7a,0x1ba9f7c6ad9ffd945a3dcebffcdb3ffb78f7f8dd47ae356ceeeca2d09736db74ee6d9ddd804a26db6ceaf43e10a2a808771fe6f2b3adaeee1455090ee12e619c74ebfe90f850e108ea0754494853ad77770a1ddc7503aba9210a9c28158e9f0e1d21ebd4e140a1ddc387487a145168028f4d2bbd7cf6fbd145a00a029a573abaa9fffe90a2a8fa7fa85552bbbb8515426810a853adaeee14cfe90a0f7bbfe9d6d7770a1ddc281c970a75aeeee143bb814d021392ea75fffff0a1ffcffa7fbdfe,0xfbe7df63de5fa7dbcf89049e16f1bc5bdfa7dffbfdffef13423d76128b4528b0a4482408db53bb22d14a2c293c8046dd7ffbd0f85effb6d57a1c57f87efffffd2521b5ddd494db6abd0e292177b52e8a68214fd487c10429a1485290941ea1052290daeee0928a6a2945294940eaea11aff147bfc35294a7fc078f5f48a450892886a529485201c7aa508b4ea46a2aae7f8bef43ea5716aa9ebaab8948a97aeeaaefbfe924ef6daaf47a3ed2d575aeeea77b6d57a3d0f69691486d777224a28d4528a42912908852177affffbffef7ffdf4fa7fcff1fffe1f,0x768facf3d7b55eab96a41eebfdbebdaaf4f5697ced08d624f5ed57aae5ae066d245a535ed57a700da5eb9e87d2a177af6abd054ef54a977a5d2f5c9a8a2954bbd7b55e82a77aa54ba2974bd77fa429f4fbbd7b55e9414012f5c94a514a6a5debdaaf4a0a08a28ba5eb8a54bbbd7b55e9c3a5c025eb8a5aeef5ed57a70e9703d50b5edab68b48bd57b695ea85af6d5b45a4bd57b6952f5c94a28a5352ef5ed57a45e9145ed2a5ebbfffd3e9f77af6abd7bd7ffda5,0xabe2d28f37dd575f2da3d4556c6fbaafffffeeff55716947aeeabaa4b6871a8af5ebbaae440919eaf8b56d5b45a09febd3dff75af5eab8b56d5b45a49d35e9ea52f6bd7aa916bbda4d0aabba812a903d5716bdb4f5d55dd40ea9135ebd502bda0d4aab9cfaf4b5f7dea816da7aeaae72d7a5a7aae2d7b69ebaaba294421af52f5297abe2d77b5b1beaafef3fff5efbdff,0x1feb283bdbcb797ef3ea2d48f4eca3bf7efffc7c47a3a6b28392d16168a28a8b5c7a66db955da2c2d145101e8dbf7ff147bffd7b55e9c4bbd1ebfdffe174a228ae8a6bdaaf4e577a3d00a23ca245c2114a17085294a290a42005a00bbca22942e8bca5290a514a2005a25dd2e17794452bcba2f2145214a28a272ba5c7af7ff14beffe1f4fa7ffce7ba7c7a,0x3c3523be7829485108521280be0f7bf7a5214421485e9f15ac4453511d444494a5e763ef2979280ae76d4a3e134428a53fffe9f50a9344210a5ea42104210d7b55e8017c0884210fa2979f0d4bca2a8bca6bdaaf400a905defff87d14421484290a210a210a5214421485dd1b6ea933ecb2cffa59ff0fb2ca52cb2cb2965dd1b7ebe,0x1518684095ed57aa2da7f95d02610835ed57a3fbfffdbd47f7c792bdaaf545b445c551e7bff7abdaaf4045e43c2979f7a1790a85e535ed57a09d2ef4145e43ecfffb359f65ecffd7b55e827f77affff,0xf4d44fbe3c92f2f2f2f3ef2f2f2a92d48f2e7fdf3ef9efffffffff5f2d49fe] gz 12 44 36 10 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz12_80 : block gz 12 80 36=true :=
  @streamBlock #[0x1ebef25a51d52df3aca3307fbc195b1b22a945ad2b3aad685bacaccc66c66448b19d66ddacd9d6ed6dc24fb8db6cadba6fc66dda7526db66d9b6dbadd1252e36db2b6e9b08cdbb4eb6db6dd6ccdb696db6db6db6db6db6fe921481489286bdaee9b52e5b49bff692f290291250d7b5dc36a5cb6934ee92913ada36cc3aeaeea90db6da49fffe75b40057577577b6db4e00007269ddc04a5b5da5b6bdb6d282d3bb87296d5a5b6bdb6d28ff26d28073abbaa436db692ffa7ab9c9493694039d5dd5dedb6d2403fc08449435e9ba35b45bffe92f82211211254d7a285b45a0514001a24a1b6db7c061dffbe0f27c013472a6db6d7002d2947383844816bbfd485ed5a4bc1fef39c1dc702d777a90bdab4e4a24bca204224a1af6bb86a42f6db49bfe4ff81089286bdaeff5217b6da4d,0x3742dae809fb7ca33cbcf86cf61fe10fffc6e85b5d0029b5ca33bb8d9b1b120148297773609ddb3d7ffbe025ffe3c82521f1b7fff3fffde776c9aeef5c0082971107777374dddeb80a5173baa707486840ff4853f53e3fd213dea70777ae005294ba6a521dddc3bd12e26803ff9c28d773bbba8ffe077a571e803852777aee777729c0eea05a5b6b85d68714e077502d2db5d2eb41ddcffa5007777ffdb5fffeff3bb95e9401ddc977b69dddc51f5ffef81e287b8b47fbc50f5ddeb80e2825c5a2b3fdedae07fdae00b5e7f8a12ef6d701d36b802d01ddc4bbbbd700290a5d21452173bbb8eee7fbffdf03fffffffffddfffe,0x6c65b7e8aa9fb7c00ce9b37bdfe06cd8cb6bd155c36b80666db366d854ee10336db6cac7bf6ff8685e552b7c0656e7f6fffaad0ccac0d4daee9ae9575ae032b76cda6d74db4db6c011b521ff4a21bff6a4016ba40136bba52e94d70dae00b5d4a3ff2d03d3da005af14572d03d3da005a000b54b6ad2800af4005aa5b569400528ffa7ab9d4f68016ad28a9a3ab9d4f680168a03536bfbd74a6b8a00b5fca1ea6d777ae94d714016b82808536bba52e94d70dae00b5ca3ffedfffffffbff6f802d7,0x7bc96dfa2aa45331ca07aaaf11b281212daf455715b31ca56650ba9dd5b657ad95eef5e7fffde85e4949b630f25aef79fffd8a5b6cfa525dea5145d17ae925cdb18096bb6cc4a28a2949b61adb00a44521485ea510a7c50125ae022912945d17ae94a5c50125ae5156bcd1340e9003ff968ab6d1340e9003a425a07708a2a5b54504bb85283b87752daa2825dc28ab7ed3d69ce00b6969dc55b6d1d69ce00b6968a442f528a2e8bd74a52e2825212d72bffebcffffbd47628a7c50fff2d7,0x7ada53c2a968acaf3fe5ff579c04cfff12b69408556b456508510c94daa18ec2144dc21fb5ed3d69ce3b87915290fbed0e73bbd7dd290db6d02b4e71dc38a14a28801a1ddddea23e91b4a255ce73bbbea697fd215a0da502ae739ddc8d7a5085288ef6da914073bb9ddedb42145100ef6dae280e7773bbdb6bbbb87d3da005145b6db6d15ed3da005145b6db6d014a436d4d02ae739ddc8bbdb68428a2ffffb7fe9eae739dddfff6dbfffe,0x575dc5aa29694a1ed0f8d6e02db4b4f575dc5aa29694a1ed0c2b70b6abdaaed3d3bb879f52d3a2943da573cfda653ad3bb87752d3a2943da51b9ded6571da777090a96d5a5b6b8f69569ddc3ba96d5a5b6b8f694ab68240a516daeef68f71556d0702945b6bbbda2d3bb87752dab4b6d74bbda5fa7770f3ea5b5696dae8bbda5,0x756c2d0ce9ed6533bcff98e6df11b3b71ab1ac6f16756c2d333a7b594ceeee6d99b6ceee999cf5dddb6cef6d7adbac33c9fe1e43ca521f56dd67fffb1ff3bdb6d6dd61822288708bbbbab6d980dadb6dc28a27745eb6db73aada09a0744e909ea689ff4854ab682681c274a27af44bbbba8903bdb6b89a0709d144eef5c28bbbb8ef6dff1340fe7ff3a3b1affffffe,0x1a8525b5347553f6a4e8779f63d923dff85bfd8d5296b6fd1d5451b513a1d1458db664b7d3f451f3088a2d2db6f4885c45214843528914921489094a521451229085145214890da794b9b14bca2f28d48f16c5127fc484a294fa4ff4ffffa7d29fb488522290a42885288514514852f3521128a290a7e9965232965967fd2cb2cffa5967ea7c4ffa59f,0x30a9cedaa6aa9768a1d2c23aedb5daedaecc27335e2c2584db6dbca9cedaa6aa9768a1fdf956d5ab6a873ff3fb57ef607bff2bed7085e52ef763b17945e4342f2794bffc790f29487d17659ff766fffffb359f7b2fff3c7b2967d9,0xf2a9792dbf4554bcda8943bcbcf8f5ff2dbf45567edf28767fc] gz 12 80 36 10 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz12_116 : block gz 12 116 11=true :=
  @streamBlock #[0x1e7c02ff8005202821285ed4bf8a4fda174453a22d48f7fff2d4877b68e15f68e145b425dc2da1deadff71fff6842e12973dfc0a1dc201fe02d78e901694285a50ab42144242f6fff8fff,0x1a87818631b674cd5b75852318334a4630d9b0a555f0a550771851dca156d0a555a14aa1ffca557fba4252a8294782940028f002811484a557f94aa,0xf290c07fbd867486366779a1a225c1a00ee4d01dcb55dc3c5aaee00000005a28be5a281cff7fb81d24a5c0ee7ae01dcf5c0e9252e0ff7fb8,0x3cb81bc562ea6f1dc1b31de9b312fef42bc3b85e804b536b82d4dae01c003805b4a02da507bbbd7143bbbd703b85eb83dfdeb8,0xf3e01ffef011480a451aa908529770d525d14a2ee8d505cb5eb87dfcb5eba5debb8e14ee38516d285fef96d2bbd451451744294521ffff7ffffff,0xb4005a035a606b5abd2da292a2da2aa96d2bbd16d2bbd02852850a2da577a5b4a17f,0x70000280a77180cee301b60e14070a771c29dc70a,0x180730c0663557596a6d526a4b536aaa7cb535c2ef4b535d9f7f,0xd2c60d99a5986d9fb1815fbad5f4294bf86a92ca597f66a99,0x3ca400cf80] gz 12 116 11 10 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz12_127 : block gz 12 127 36=true :=
  @streamBlock #[0x17feb6dbf7fbfdedb6dd66b5a9b6d9b6db6dade358d6db613989cc5f16db6eb35ad4db6cdb6db6d7feb7777f7fbfded5db6db6db6d86db6db6db6278d3bbb84f3c4f3c57895db6db6db6d9cdb6db6db6c739dd27771680a5285a57ffffaaaad5b6d28f4ffd2ffa5ffd3febf6db683d75757773d7fed7777f3fddedbeff7fbcaff6affdaeeefeff7fbcae50b4a,0x1efdb7ff7db6d35db5d5f74ffffbdb6fdb6db6db6db758b6fe358df8b6da6bb6babf174ab171bc558b6db6db6db6db6feebffdfadb6db6db6fdd3fffef754db6db6db6ce574f1b3c6b6db6db6db12bc558af15536db6db6dba7b5c71dc5726a8e7392ab56a536db55529fffb53f6db6a8eeb6dbffe07ffdffd3fff5ffe28f6b8eaee77d5b6daff6bffdfb6a536db557dd3fffef55,0x3db6312fffff6dbfff7ffffedb7ffefdb66db6db6db6c6248a21ac678b6daf1f8b31f8cf14f16db5e3f16db36db6db6feb6db6dbfffff690a7ffd3ffffee85ffe9f6db6db6956db6db68a21bc6b14a4297c4c52562f8a84f8cf14b6db6db4848490927b5c71dc00249ff7bd7af5ebdf0eeaf1fffffe9bffe9fff739c00a012fffff4a429fff4fffff8685ffe9,0xa003dae3abb87aeaeaeee1772800f6b8e3b873ab8eee1772800f6b8eaee1ebababbb802800f6b8e3b873ab8eee171c000af4e5001ed71d5dc3d7575777,0xfffffff4bfff6dfffbff7ff4dffa5ffbf6db6db6e78de3f1bc678b8fc52ef1485b61ac678b4f17f1f9a6fe4c52c62fe2db6db6dffffffffa6fffb07ffdffd3ff4effa5ffd3fe5627c6b118a6fc521021bc6b175629310a9e2975629bc54e9ff2aa94ef5ffe3ffffffd37ffc0fffbffa7fe97fd2ffe9f,0x1fbbb5ddddfbbf77eeaf5352ab5d4dd6da9b8bbb5ddddbbb7766257a9a55a5375b6bfedfbdb5ddddfbbddeeaf5352ab5d5f1f8b18f55dddcee775e257285a530250b4a094d29ebd5f7b6bbbbbddeef757a9a955aea,0x3a6d7ff76da5b6d4d5f6deffb74d566d9d36bb8fc5db696db557e5b5f9316eaacdb3a6d7ffb6da5b6d4d5f67bfe74d5395c636db4b6daaa15589d54a5294affab43a6d7ffb6da5b6d4d5fa7bfe74d5,0x12fed3efffda7da7da7fdffbf7efdfffbff6db6db6da5dc5a4c5cf1ac678b4a2d28b4989d6378bbc59fc5cf19e2758d62db6db6dbf4bfba7efffb4fba7dd3fe9ff7e1f4fa7ffd3ffee48e95ac6f1ac5d28ba5174d624de35881249ac7e24de33c5c91d2a126d774bfba7efffba7dd3ee9ff4ffdf0fa7d3ffe9ff,0x120b690b48496dd76737736eddbba5bbba4887ffde5e5e490bc112124249ed71c770e73ba4eee887ffde5e5e4290ff85b6db6db6db6db6db6db6db6db6c012b529b6daaa50b4a0016da52850b4a089092124f6b8e3b8739dd2777089092124f6b8e3b8739dd2777,0x3dbff8bfbc7fdb7ff17ff1f7ffedfc5fbff8fbffff8b7feffffdb7fefffdfffb7efdfffbffff8b7ff17f78ffb6ffe2ffe3efffdbf8bf7ff1f7fff78b71632c5de32c62c4c5b7f1bc5fc6f1ac5988f11e2dcb17f173c658fc5fc4c4c658b66378b963f131962db31962cc658fc5c58c58c58b778b317f1bc4c598c58fc6f16cc6f1778fc4c4c5b7f1bc5fc6f1f663fedde2cc5fc6f13173c4c4c591964cb2e2cb972e2e2e5cb972e4e5972393265cb932e59,0x7ffffffffffffffffffbfffffdffffefff] gz 12 127 36 11 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz12_163 : block gz 12 163 36=true :=
  @streamBlock #[0x1129f77857fdfdeffe9f79ff79ffff0d4183004dffff7fbffffffffffcc60001801806006cd4e86009aeca743006336c6db3cb7ffb3f7efffdbf6ffdd29774bb986eb3336cd9a6ffffffffffb19b636d8c36ccc36cd8c00c366666d9b34d0c318d54dd0dfb6febf7edbfaffdb6db6db6db6db6db6db6db4d1aa9ba1b36c3acdba636db6db6db6db6db6db6db61400fbff7fffdf7fef9ed7ff0dbff7fc3dfe1400000000005500a9b5edb5ddebfabbd7aaff6bda7f8550000a0000014141c77bffe4d7b7ffd3f5ded77aee26ff8505000028000154504bdae29fff43febfa6fdf17ffc2a8a000505000140a283fc0414a4290ffff4800a3ffffc0a280050500000005fffffff5fa973daee1fff0853fe9283fffffffc000000140005028038eff4f35dddeff9297b6a7fefba681fffffe050000a000003375b6db6db6cdb3adb6db75b6db66db6db4d,0x134db749b7411f4dbff36da7fefb6fdb259b6e96dba75b7adbb5b6db19b6e96dbad214685b758badb6db6db349a9a41b36fcceb37e31b7e1349a9a41b36db6db6db36d5bcb76ede496f5b9e21696db6db6c557715ebffffc000002abb8af40777746bbd4536a428d0ba6bbd49692af4f6db7ffffd6ffa7fd3e5a757a7b6db47aaef5157b6d7aa3d577a957b6db4ed255e92f6ba969d5e92f685a38a7f0a953ffffc714e90b6d5b56d0ad2ee12f47ff8505dc25eaabd573e927ae7b6df7adfffb44d24f5cf6dab6d5b689a4bbba497b5c77ffa79aeeef7fc94bdb49ffbee9be1,0x972416e6db3ffdef6cdb7ffedbff6fc0b920b76db66eedb6db6da23c913cbb6db4a28b6d10b758a2edb6db6c482b04d7ffff8f536c63fbe0415826b6ccc2f510427228abcd6ceebb0acf1ad9d7fef578b5c1e0000109d4116b805a10851b52f5d28a210a510a52f5c29b6bc915b4f5c3fe7db5ceb69eba6da977aa7aeb6d57b5efa5dea9ebadb6da5f7ada7aef6daf7ffef95ceb69ebbba5c15c03e9ffff74b82b826db6dff382487ae7bd5144e4921eb91442e4835cf5d37ffffffdfebf52e89ed770fff8429ff4df,0x14db0f2f2d5e9a6d8ff7402b866d80858db37919b67085d00af5b660d4503c499d62bc2d706a281b63c83b0b4b48e10852570b6d3fe0aa527df4800000213aa523d0a4024202002436820a87ae5a73a87ae4baabb8af55ed725d55dc57a01054ff4a55c39d470a5274851415d214507979382948e10a4ff09082948521fffe928057,0x383d20892d4787d7e97efdb1c090826bb6db6e7629e87add2c2c2dbb6db6314f29a11492db6a53ffe87fb862921a12db752e6d8502f402736dd25514000001d255140136b81084179aee9a1a1b5edaa3e87fadb540683cdb5ddd554216abbbaaa842da550f68777af5c550f68774baa821a1e52e9b5ca53fffe87ffd7f4dfbee,0x2b926f4f2de5de3fff9bd7bf3daef5dd7e2d52737a4585d5d6c49cea51613daef5dd6b6740f6877377aef792b6d794d9d03da1cdb737724ee4db528a290d375b63fea9f53e0b8000004a6a89a909ddeba5ed46bbdaef5dd4a94babd3d77b4a94babd3d77516bd5b55ed4bbb96bd5b55ed2a52eaf528a42ee3bd7ffff26bdb7ffd3f5cf6bbd775,0xf54f52af69ded7a7f57b4dfdd7b5c3d53d0abdb6b7492abbbabd37775ed75add0e2aa42b3db4eb5d5fc71ce1c5508575a56aad77777577ae734babd7715e8000012eaf5dc57a2daf5eb85ded77b5edb6db5eadab6dff77b6d7ab6adb6da977af5de855eda97b5ed7b5ddebffabbd7aaff6bdae,0x6e4bbecf5d157f58fd62ebf3d7f6dffbff24693ba967ae96dd6dba24ee84f5c2db45168a24badb6503cd047d7ffdef7bfca7ff925026826db51a451a49dc8d4684f6ba226a36d7fd516b8000007b494d516b8228a35d1451b51d886d451a8a36db6a52ea8d3d7d8fdbff7ffffdf7fef9ed7fff0dbff7fc9,0x1cc10de5e400000f7fedecffd8005c0022644345105297930d4bbca5ba52d8bcbcec7fde5e421130a205a288002fefdffffffff81450000003c3ca1415b00028a1b1fff7fa5e7d2f2f293a52ee97750411504881a45117fffffffffc10b221a145b06a28ba177fedb7fd7efdb6faffdbadb6db617,0xe98b4284d29660a9d8e25ff9b30c1ba52ee977f8fc5db30c1fc7e274c5a142694d7efc2bf5eb7bfec535cb1bc4eb355ae8add29774bbde32c7dd7efffed7ffff5de378b259b694b6da5d29774bbfb7ff99fbf7fffedfb7fe74a5dd2eecb9,0x11294b92150a5d279779794a42253e65e15ff7ff7bffa7d9ffffffffff] gz 12 163 36 11 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz12_199 : block gz 12 199 36=true :=
  @streamBlock #[0x9240bcffef277f71ceda5d76972f87830f3dfef03000db600003076d2ebb4bd346d544aed6dbab54aed6ccdb3366decf2dbff777fffedbc9b6db6db6ebd8db7b0db7fbfffffdb336ccd9b6db6db6cc6d8306d8db6db6db622cdb186d9b6db6db018574676b5376fdcdb66dbf76db6db75b6dbf15d19dac75ba36d9b6ed6db6db6db6dd50aa2fa5e89574db7ed7a57f15ffeff542a8b4050a014e55a05a53d5aae77f754bbafd73bbd72ad02d0aa00156adb5554ffbff7fffedbef7e9c93eadb5554a5aaa14282da555b4fb7cafffaf7fdaae5b4aab68b450a16a8b4aab6d7bd225211fef7fffd169556d168a142d5a29543ffe94f739dd5eba43e9f7ff2be8a550b45142805aa502d3ff97fcffe904352485354a05a55ab682800552ad5add6db6db6db895725dbafdb6db6fdb6db66db,0x121ef530dbadebb5fec79fa5e6441122eb66db6dbd66dd6f5dae899d13452ea2da5b6db75a6853cd59b6db6dd7fb5a3b36dfab742889ab36db6db6db6db36db6db7448b2ba2766d8966db6db6db6da8f703dff000aa1dc0f453d5a455d1452086a42945dd22aa8fff7ffddd22aa8eb6aadaab6a355c77254ee5a571dc953b9ffcff55015ceef7bf5c95708470aa8a5078b7ffe940116878245252fffaef392091494bb853a8ff50be9770a75025d1447448a92914f56bfffb97fcfef4821a9f2429,0x141b7314bfff46dabc6db67e0ccdb730db736edb75c5c4c68db764b76dbb6d211b6edbb6e9995d70fffe8ca6fcd95b753ffe5a66575c336db6dd93c4045db793576d2945c2299b6dbab5500fe5a0f00a5501554eef5d214a2e1aae970af52e3c94d7ba7d4970af5dc2d5ab54753a8b5d2aea3a9d408fb8eaf7dc3bffdbe171d5ebb8b6db4295e87f9f7c14af401c7577b8f78e3ab92e14a8d45c75774b8bfff4a7b9fceeaf5c90fa7dffca,0x919b3c17ffdb6e3d4cd828d236d890db6dada62dba3bc55db6035c2db6c28aa8dabffec702d15afbd6df0a2aa6d0e978804942912960a21214496a7a70f7a979400aa7a704bd120844922138577b8fe070ae771c28e714ef6ba8e714ee25ef49297fb94492925274b82d2aadbe169556d048292520a5210dfffa38f2fa44a421fef5ffff,0x1e03f6ffdffb2f87ffbcf00081b6dbf96dc678bb78b01a570a3536b6db145fab5e9f6ffe1ff497febcaffafffb5e28a1ab448eac42f8a404351294945682d02daa00516816d486a20851248a942da2f942da282a848b42a848b4b696d51e5b4b6a85b4a1ab6a7ddffc3fe92ffdbe57fffd7bfed5,0x90f57870ae777f87beb00402a0856ee15ceee11c210dadce1bd2aada8d1c2b9debeababf7ebdaa4a9556d0d1db4e15cee10a92c210a277b4e4bb5d4f7dc1c500053d4b838a1a8db5e86a552e915ebb8b689748af5dc55573fbaa877573bbaa80842908421ae171c2b9dfffebfeffffdfb7defd392,0xa0ed2a00a7ab55dc3b3baf8f74c7695030a7ab5d3b7767724e370512aa14f568eee7a52fbfab8144aa968a7ab54ee77752a5c77552a5c0f4a002a95dc0f4eef52ef535ddd5c5551d5dd3475715547573bb92a7714f56abbb9dfdd52775fafe777,0x70a6736f7efdffbf3a594fdd33670a676db6dd6dd6ebbc598b3173c6b9e2ee62bd75db6db6db740b6b8f7ef0ffbfd25b1254fd6ddb1d02dae0ddadb66f8806b13fc52e6c9574d3b6d8dcdd6db3750a05774800550a05241494db6d7b5edb52e915ebb8fe1f787fdfd2e9a12ae9bf6fdaf457,0x141819c0009e36d62e94a678d62a6330cc3063192905bbc9e762efee6effff74a6ff9aba5831dd7ffefc75416800158db78ba529ac6f11ad5010b6800ea82d3794b62f2f2773cbcbcbcb62f3c94bfd5abd25c002e7ffffe7ffbd9b5974a52cb2aaed2e613a176cb2cb2e94b2cb2a75dbf73616cdb77ddb,0x182a8f6fdde378bff1a5821d9ddd8fedfbff7fe360ddccf6fdde378bff1b0660c15418b73c5cb1962fe3f17b4b02793d677aec7458b7f17f1f8b3131a6eaad6ef6bb462dfc5fc7e2cc4c5fdb77fffafeb7f76ccdb797768b6f3dfeff6dfededbff3bbffff37e,0x92409e4ef277f71dfffffff7fcc93e05e7f67fcefeec8e] gz 12 199 36 11 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz12_235 : block gz 12 235 36=true :=
  @streamBlock #[0x3fffdfbfb6db0b485211b6eee171b0b69b7db6db66db6d913ae8b6db0b4852166dbbb85d9b0b696db6dd6db6dfffbf7f6db6db6db6db6db6db6db636db6db6db6db6db6db6d9101b6db6db6db6db6db6db6c6db6db6db6db6db6db6db03d7774bfffffdffff7bffbfff9c29ff0280512eee7a5b4010052dff4fbffa52fe5505516d516db56f85d557ffed7ffb57dfea5fcb694b69479e7ffbdfe80490a423bd7770b88b85c9,0xdb6db7fffadb67ffb6db679edb6db6db6db6db366db6db98de3f1adb6f89145b6db0205b6db6db6db6db66db6db6dfffeb3bbfffda42971e7b36db6d86db6db0a3b845124297010236db6d8e392b7febfdfffed3bbdfeab6956d5b6da28b696bffffbfffffc90a7fc00b7dd6da3efd5a79e785a16851086d3a83fffda777fff9214b8f3c,0x1fb6dffd6ffeb6f4bffad46eb75cdb6db6db36d8c2db778fc6b7f1ac6b6e24b731ad59badd36db6db6eb6d8fdb6ffeb7ffb5ffd2ffed56db6db36dab6db6d80b6d83a58dae26bde36ab6db6da5b6d5b6db6ca5b4a3fd6da0eb6d5773bba5d29fab4a3c3fed7ffb5ffd37fed52da5,0x3dda7c03eebffbae777fdd55b6adff8b6db338052eba7e2ebb89d731756ada56db7eed3e01f75ffed7f777fed6edb6adf886c38038c6d715fe36b65b4a1b4a5257fbeee757ff393e01fb5ffed7f75ffb56db6ad,0x3fffffdfd7fe9f7fe91b63dbfd297feedb36db049a62ed7f171498bac7e2966d8ac5b89d296316dd6db7fffffefebff4fbffa5b6db6fc3ffe94bff1b6db6e8248024f3c678a5b6db6e788474a6ab11b6db6e8121226874bbdaeffffffe9fb7fd3effe92923c3ffe94dff,0x2da77ee05292ef6bbd739ddd2e697777295b9a052b9ded77aee3bb9cd2eeeeb69dfb814ae977b5debbb9ddd2e028a0014a3bdaef5c3bb9c97773d00a2bdb4f7dc0a574bbdaef5ddceee97,0x12ef41d4fba772d039fedd71b0d9d41d4b8ba7755039c4edd0d86fd2ef41d4fda7776d03bffdabbe263a8051dd940e1ca1a8be977a704bbd0b53f69dd6d03bffcae,0x1b6effb6d9d1bfffdffbf7bf7fedb6db6db6db66dbae6b6d9d1988290b9e358b9e3f1345a26db6db6db6dbf6db77fdb6db6ddfffffbff7ffdfbffbfb6d9b6db6d9b6c1b6db6dd0290dac6f1b58845d13b6d9b6db6d805148dbfe052fffffdffbffef7ff7,0xdb690ba52e945210cf14fc5358cf13051ac53f14a4d219e290de2dbf697dffbfe1ffff4ff9bffd3e94fbffff7f87485d2974a29086b1498a6f1ac4051f8a678a521a90d6290fc5deb4bc03de9ff37ffa7d293ffff7ba42e94ba514842ca594b2c80a2ca594a43521652165d2cb2cb2cb2cb216596594b2c8659652ca52cd659659659,0xdb6db6db778bfbc7fdb6dffc7ffdb6fe2dfb6db6db6dfbfffbc5b6dffffc6f16dbf6fdb6db6db6ef17f78fde2db6ffe3ff1bc5b6fe2dfb6db6db6dcb173c658cb1962db6ef1bc4c658fc5b6ef16c78b6db6db6dfc5de3f131f8b6dbac658fc6f1962db72c5b8b16db6db6dbf8bbc7e263f16db7f7898de3f16dbbc5bf7bc03dfffedfffffffedfffef,0xf7dffbfffffffffedfffffffedfffef] gz 12 235 36 11 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz12_271 : block gz 12 271 1=true :=
  @streamBlock #[0x3e3eff,0xadb6cb7c,0,0x13ef,0x63ef,0x2d5,0xee77,0x76db6,0x1e9259,0xdb6db,0x3] gz 12 271 1 11 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz12_272 : block gz 12 272 33=true :=
  @streamBlock #[0xab6d0000001ffffffffffffffffff7ffffffffffffe8b40000005169ddce2b8eeeb47752d5b68000001ffffffffffffffffffffffffffffffffe00000000016d515caeeb4b546db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6c03fffffffc7ff87fff801fffffffffe00fffffffff0ffff,0x1ef7e9f6dbac5a23c478b697368b68bb778bac5ef1f6db6db6db6da264a5b6d169442da5db68b6176d2c2edb6db6db6dbff7e9f6db6db6db6db6db6db6db6db6db6db6db6db6db6506db6db6db6db6db6db6ebb6db6db6db6db6db6db76ada00000001179af2948224a2112e1102e24174514b8fe1c7fffa947fc210d0da5a39ea3455a121e3e945fdeda01e02f49e4a7d3e1e2ff452d,0x36db61db74db14db6ddbd76db6db6db36db6db6db0edba6d8a6db6edeb6db6db6da2db6db6db6c3b77a614453b5b6db6db6dd6db6db6db61cef40a452d6db6db6db75e51adb6d8000000000038073bd02914b473d779b6bd7a7ffb7fc39deabffbbbbd7af55ded77b6bd7fffbe0515f7b4a1fe9714b7d145145d1,0x1fb6d8dbdb6f75b0b6949edb4b6db6db6db6db6616db4516d10b6c28b6d85b4a42945b6db6db6db6db6d9fb6d8c2f4ec5bf62db6db67b4a5b6db6db6c0b6ddb434294421452db6db76a352945b6e85b6db6dc0000000000010451442885288428a684210d4a42946a521a108435294f9fe97ae3bda17ae9af2e8bcbbd4a7fd3e9,0x2a94002800280eee715c3bad1dd4b54a00000000b6a8ae5775a5aa5aa50000002d52bbb9c571ddd5c77240,0x3fffdf9927e96eda25bd9b7b6db6db6c2482c9694a5852dda4d4baf2d2dd45b6db6db7b1fffff7e64878fa5b6c25be789d62f0fb6d890b6a6bc852db75352f5e43686a2156db7b6adb4000000008521084294a529790a5eda14d4ba5e4294421442f6df4d7a97b6a28bbd,0xf52fd22ad71de8e3b955eb01d4dd6db6d74a5dd52e9aef6db5eb08421b5dea5fa455ae3b871dcaae2ad285b6db5d2977b52e9aef6db5c108686db56da0000003bd4bba6db6dae94bba6a5d2177b6bd7b6db6d77,0x9771d8cef4b69b2d1cf4db9ba49c1a52d2ef5eda4b6f6db5ebd36f5bb7d29771d8e7765a3a5a39ede2c70b6bd776f6da9b5edb6bd7b5db54a00000004a5dc74a52e977af6d0a6d74db6bbbd7b6bfa52f6bd,0xdb7ff6dd76b1fd663f667e96db6db6db6db6dbb9b75dad296134b4d68b0bad16db6db6db6da2db6ffedb6db71fcce3fb55ff6db6db6db60db6db74a5c36a5d35d1b6da8b6ddb6db7685b400000000113bbcdb6db5d2970a352e90ba2886a351b6db6d,0x2d0000000ab6d000000156daeee715caeeae3b92089e7c0789e5e513d23626c4204f3f45a0000003deff7ffffffffffffffffdfffffbfe00000000b56da0000005ab6d77738ae3bbab8ee482201125109fe3c0bc890762000000003c2dbf7ffffffeffffdffb7effb6db6db6db6db6db6db6db6db,0x1b6db6dbbc58f1ff6ffdb778b7f3c5bac5fcb16db6db6eb1688f1bc5bd88f16dcb16d1d8b778bac4162db6db6dde2ffef16ffdb778b7fedfbff6db6db6c78b797945b9e296dec5bd885b0b799e2db6db6da2d2885bbc6f16dcf16c2f2da58762db6db6dcb1758d632c5bbc6f16d82c5bf962dcf173c6f16f01efff3fd9e7f9eff,0x1bdfe1efff3fd9e7f9eff] gz 12 272 33 12 (by decide +kernel) (by decide +kernel)
theorem allgz12 : block gz 12 0 305=true := (@block_merge gz 12 0 272 33 (@block_merge gz 12 0 271 1 (@block_merge gz 12 0 235 36 (@block_merge gz 12 0 199 36 (@block_merge gz 12 0 163 36 (@block_merge gz 12 0 127 36 (@block_merge gz 12 0 116 11 (@block_merge gz 12 0 80 36 (@block_merge gz 12 0 44 36 (@block_merge gz 12 0 8 36 sgz12_0 sgz12_8) sgz12_44) sgz12_80) sgz12_116) sgz12_127) sgz12_163) sgz12_199) sgz12_235) sgz12_271) sgz12_272)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz13_0 : block gz 13 0 6=true :=
  @streamBlock #[0x4a5dcb6d3fffcb6d1fd4b54b68b68ffff2db43fc2d3fffcb6d2db4ffff,0xa0a0a14a5ded4ba5353ffff6a2e94abbbd5dd6f87fd6db55ffffed45d29be25368ef6a2e94dfffff,0xe070384777791dea4ffa91ddb10f2a2bf8f2744a773fddc777791ddfcff,0x1c0e0774a5dddd214435ffffebbc84213b8415775770ff9deda77790a2177ffff,0x120481214a5c946daa90a2154db445de45b44a36d27c3fe,0x1749d5dd497f7abbaabbab62fef,0x28282a52977a94a2146a7628851a9ffff,0x20080214a5dc2ca59659,0x190320] gz 13 0 6 9 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz13_6 : block gz 13 6 19=true :=
  @streamBlock #[0x3f91f6db6c1feebdafeff6db6dfedc2736db60aedb6db06e13a5b6db576db6db749217ab5db6c9a6dbadb6ae13a53569b6d695b6db6caff756b83fdfe9ffff53a556815c01c54b5a0796bfdf70a5a050029d2ab40ae7ffd14e955a05701fdfe9aed707fbddfffee13a5356815c02faba699c0a78bf5d4f400a017d5d346e07bdffffefff5d49a0038071525ac1e3efffbdc296814a15c274a6ad36dab9fdfe9ab5db6dfe,0x796dbf7a7dd7b5e7dffb6dfbffdffbf4b6dd05dddb6bbb76db6d2db741776eeddb6db0aab9294d0a95a09a95282ee0aeab6bb8ea9fff6fffa7deffe500bbad7777384a955dd7ebbb9c952abbadaeee71a8b56bd795fc02d5af541eabebff5ffffeffff4a955dcaeeee7aadef2d14af7ea94e28a52a9fbcb7fffcffbf54a716bbb8f6d4a941775aeeee7f55f7ffdbffffef,0x3f79afde7cfebdaf2ffdffd7ffe7feffdba6b0a5cd5ed45842db6dd35852e6945842db7521aee14810ab5216ba6829712156829084af5dfe7a7ffd2ff7abd12e25294852486a9ea574df09f6a9543a6bb8eeaba87fffa7affaa94035e8e17febfbd3dfffefffae9a0bd1248528829ae9a0a5c4f8ab56ba69d2e2422ad574d052e242908510437febfff9fffffeff,0x5f796f79f6fa2adbfb16ffb1f6fab6ba59d2eca2ad6d5d2ddd2ec9ab5b5486bb852042ad482ba69d2e242ad2215ebb63e7a455beaf44b8948ab6a9b152b8a5552a8714aaaea1fc156d5528220abfb1afef4f0ab7eba69de890ab6ba69d2e251156dfd8d7fd8f9fe2ad,0xf3ef28ffbb4ff9ed79fffffffff77ffffffe8a28bc9176108f6ec428a5a28a2f2f28bb0851d88514b0a4290bbd4a4215368228a297945e8428854db41452affe7bffefff4fffab8513d085105294852945551508683521092952abb89aeee72b63eab5dff5fe7fa9d2ab4af55c8a28bcbca2f421441453b10a29ffffff7bffefffffff,0x1d68faad57b5ff9d7b1f55aeffceb72ad5b6bae6cdd6e955aeeb9b35242ab5c09aa053a5568168f35e9414556ba514d2290a74aad26bd570145a779b4f25a0169edaa29d2ab4f35eab95b1f55affff5fe,0x7953dd4fabda1f7ec557dd79fa1f7a54aebbabdaee76955aebbd773b0aabaa5342a540952abb82ba9d35caa579faff7d3eff142bb9d35ddce952abb9d35ddcfb155f579faff7c3ef,0x1ba3ede7d3ff5ed4fff9bffbfffff4fff9b84d1451455ed4a2945b370a2d145145e528a516d5d2105294842a6d0a9574a2451451790a9b494528ab851228a28bca514a294528abffbffffd3ffe9fff,0xa4290b85294841b6c0290a42e14ec5216db1e3e3c52791e3e9f0057b43ffd3ffffb1ff00a4290b8529485b6ea6d659652e59659d8b2e5b6ea6d,0xf3ef289e5e7d3eaf6bcb2cb3fffffffffff5ed659659] gz 13 6 19 10 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz13_25 : block gz 13 25 9=true :=
  @streamBlock #[0x3cfec7fde7ffc01ffffffffe000000000db6db6db6db6db6db6db6db6db6db6db6db6db6d802bbfdffff78000000d8d4dfafeef00000015dfebda978000000fffff4bffbc00000000000000007fd3ffe9f78000000fa9bf7fdde0000001fc3e97b52f00001b6db6db6db6db,0x7fbedb6dfc3edb6dd35db6db6db7485db6db6db000000074d74bdb6d77f6f6a7ffebd7af6db6bdb52edaeef6d7b6db6d7af5edb435ebd7b6d7f0fa5dd4fa5d35d2f6db6800007f0a52f5a7fdfdd35d2f6db5eda9b6bbe17b6bdb6bbba6ba5edafe1f4bda9,0x3cb6feffbf6dfdff696dbd4bb6db4b6dea5db6d800000026daf52f5eb7b6ffbbffdb6da97b6d4db5ebbda9b6bd77b6bb6db5d3f6db6db5ddfea6fd7f7ff4db5ebbd000001a97f7d2ffe9b6bd4bdb6a6daf52f7ea6fdff7,0x7fb17ef3efdffbfff7ec35a210badb6145a210b0b6c000000021452884290a6bba6ffa7efd774d085210d4dfae97a9b6bd77addd35ed4dfaf5ebdb6da1ff4fa5d3e10a290a5d21000002145288429087fd3ffe9f,0,0x3cfec7fd2fffffffd2ffd146a214b0d68a2f28852c28b000000045179442970a2f5dfea5ffebb86a5c28a353435c2e9b6bd77b6bbfd7b537ebd7af6d45179442970a3ffffe97ff,0x377f5edaddfd7b52ddbd7b6b75bb7af6a5ba00000015ebd7b6daee1af6a6daf5ebdb5edb6db6a5edb6db6d7af5edb5dfebda9,0x79b6fb7fbb1a9bedfdd36d76ef5a6a6bb777600000009b6bd77b6d7b6bfbfdb6db5dea6daf5deec6a6fd7f7,0x56fede7ffeb7f7ffff5d0b45146b75b85a28a2f2d80000005770d45145e6d770d45145e6bbfdffff,0x3c7ebcbcec7fe803ffffffffdb6db6db6db6db,0x1e7ebcbcbcbcfdfffffffff] gz 13 25 9 11 (by decide +kernel) (by decide +kernel)
theorem allgz13 : block gz 13 0 34=true := (@block_merge gz 13 0 25 9 (@block_merge gz 13 0 6 19 sgz13_0 sgz13_6) sgz13_25)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz14_0 : block gz 14 0 1=true :=
  @streamBlock #[0xdb6dbc78f1e03c78f1b,0x17efdb7e9f7edf,0xfeeeff7dcf77f,0x23e1f7fbe911f,0,0x27d297fa9f,0x1435e6df,0x7f77f,0x21f,0x1b] gz 14 0 1 10 (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sgz14_1 : block gz 14 1 1=true :=
  @streamBlock #[0x15ef1ef7bcf,0x57f777f7bfdf77f,0xa9f4fbfbd29a9f,0xb7eec6bcbedf,0xa1f085fc1f,0xa443c4f,0x57f77f,0x5451f,0x5f] gz 14 1 1 9 (by decide +kernel) (by decide +kernel)
theorem allgz14 : block gz 14 0 2=true := (@block_merge gz 14 0 1 1 sgz14_0 sgz14_1)
theorem tablesgz : checkedTables gz 14 := by
  intro k hk
  interval_cases k
  · exact (rfl : block gz 0 0 0 = true)
  · exact (rfl : block gz 1 0 0 = true)
  · exact (rfl : block gz 2 0 0 = true)
  · exact (rfl : block gz 3 0 0 = true)
  · exact (rfl : block gz 4 0 0 = true)
  · exact (rfl : block gz 5 0 0 = true)
  · exact (rfl : block gz 6 0 0 = true)
  · exact (rfl : block gz 7 0 0 = true)
  · exact allgz8
  · exact allgz9
  · exact allgz10
  · exact allgz11
  · exact allgz12
  · exact allgz13
  · exact allgz14
theorem targetz : targetOf gz = graph := by decide +kernel
set_option maxRecDepth 16384 in
theorem rootA : Impossible graph 14 (inputs++[seed]).toFinset :=
  targetz ▸ root_index (g:=gz) (before_sound knownn487 validn487) geomgz tablesgz (k:=14) (by decide)
    (i:=0) (ws:=inputs++[seed]) (by decide +kernel)
set_option maxRecDepth 16384 in
theorem rootB : Impossible graph 14 lowInputs.toFinset :=
  targetz ▸ root_index (g:=gz) (before_sound knownn487 validn487) geomgz tablesgz (k:=14) (by decide)
    (i:=1) (ws:=lowInputs) (by decide +kernel)
open PEqualNP.CircuitLowerBounds
def decimal (x:Fin 9→Bool):Bool:=
  ([1,12,23,34,40,5,16,27,38,57,68,85]:List Nat).any fun e=>x (Fin.ofNat 9 (e/10)) && x (Fin.ofNat 9 (e % 10))
def asWord (r:Row):BitVec 9:=BitVec.ofNat 9 r.val
theorem rowDecode : ∀(r:Row) (j:Fin 9),(asWord r).getLsbD j.val=sample r j:=by decide +kernel
theorem listedGraph : ∀r:Row,decimal (sample r)=bit r graph:=by decide +kernel
theorem portBound (a b:Fin 9) (C:Circuit) (fan:PEqualNP.MetaComplexity.FanInTwo C) (cap:C.size≤13)
    (rawCase:∀k t,k≤14→¬Live graph k t inputs.toFinset)
    (bothCase:∀k t,k≤14→¬Live graph k t (inputs++[seed]).toFinset)
    (negCase:∀k t,k≤14→¬Live graph k t lowInputs.toFinset) :
    ∃v:BitVec 9,let x:Fin 9→Bool:=fun j=>v.getLsbD j.val
                C.eval ((List.ofFn x++[!x 0])++[x a || x b])≠decimal x:=by
  by_contra! agree
  let g:Gate:=⟨.or,[a.val,b.val]⟩
  let roots:=inputs++[seed]
  let gs:=g::C.gates
  have legal:∀h∈gs,h.op∈({GateOp.and,GateOp.or,GateOp.not}:Set GateOp) ∧ h.inputs.length≤2:=by
    intro h hh;rcases List.mem_cons.mp hh with rfl|h
    · simp [g]
    · exact fan _ h
  have goalEq:(execute gs roots).getD C.output zero=graph:=by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r:Row:=⟨j,hj⟩
    change bit r ((execute gs roots).getD C.output zero)=bit r graph
    rw [←b_read,execute_bits _ _ _ (fun g hg=>(legal g hg).1)]
    have rootsEq:roots.map (bit r)=List.ofFn (sample r)++[!sample r 0]:=by
      simp only [roots,List.map_append,List.map_singleton,sampled,seed_table]
    rw [rootsEq]
    have get (i:Fin 9):(List.ofFn (sample r)++[!sample r 0]).getD i.val false=sample r i:=by
      fin_cases i <;> rfl
    have first:g.op.eval (g.inputs.map fun v=>(List.ofFn (sample r)++[!sample r 0]).getD v false)=(sample r a || sample r b):=by
      change (((List.ofFn (sample r)++[!sample r 0]).getD a.val false) || (((List.ofFn (sample r)++[!sample r 0]).getD b.val false) || false))=_
      rw [get,get,Bool.or_false]
    simp only [gs,List.foldl_cons,first]
    have matchRow:(fun i:Fin 9=>(asWord r).getLsbD i.val)=sample r:=funext (rowDecode r)
    have yes:=Classical.not_not.mp (agree (asWord r))
    let assn:Fin 9→Bool:=fun i=>(asWord r).getLsbD i.val
    change C.eval ((List.ofFn assn++[!assn 0])++[assn a || assn b])=decimal assn at yes
    change assn=sample r at matchRow
    rw [matchRow] at yes
    exact yes.trans (listedGraph r)
  have outside:=get_rep (execute gs roots) C.output
  rw [goalEq] at outside
  obtain ⟨k,t,S,small,run,sub⟩:=extract gs roots legal graph_proper (outside.resolve_right (fun h=>h graph_proper))
  have lim:k≤14:=by change k≤C.gates.length+1 at small;change C.gates.length≤13 at cap;omega
  rcases all_roots run sub with h|h|h
  · exact rawCase k t lim (h ▸ run)
  · exact bothCase k t lim (h ▸ run)
  · exact negCase k t lim (h ▸ run)
end PEqualNP.Outside.L_meta_4373
theorem PEqualNP.Outside.L_meta_4373 : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); have x2 : (Fin (9 : ℕ) → Bool) → List Bool := fun (x2 : Fin (9 : ℕ) → Bool) => List.ofFn x2 ++ [!x2 (0 : Fin (9 : ℕ))]; have x3 : BitVec (9 : ℕ) → Fin (9 : ℕ) → Bool := fun (x3 : BitVec (9 : ℕ)) (x4 : Fin (9 : ℕ)) => x3.getLsbD ↑x4; ∀ (x4 x5 : Fin (9 : ℕ)),   (11 : ℕ) * ↑x4 + ↑x5 ∈ [(1 : ℕ), (2 : ℕ), (3 : ℕ), (4 : ℕ), (6 : ℕ), (13 : ℕ), (14 : ℕ), (15 : ℕ), (16 : ℕ), (17 : ℕ), (18 : ℕ), (19 : ℕ), (25 : ℕ), (26 : ℕ), (28 : ℕ), (29 : ℕ), (30 : ℕ), (37 : ℕ), (39 : ℕ), (50 : ℕ), (73 : ℕ)] →     ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x7 →         x7.size ≤ (13 : ℕ) →           ∃ (x10 : BitVec (9 : ℕ)),             have x11 : Fin (9 : ℕ) → Bool := x3 x10;             x7.eval (x2 x11 ++ [x11 x4 || x11 x5]) ≠ x1 x11 := by
  intro f bank decode a b _ C fan cap
  exact PEqualNP.Outside.L_meta_4373.portBound a b C fan cap
    (PEqualNP.Outside.L_meta_4373.dead_start (PEqualNP.Outside.L_meta_4373.before_sound PEqualNP.Outside.L_meta_4373.known383 PEqualNP.Outside.L_meta_4373.valid383)
      PEqualNP.Outside.L_meta_4373.geomdead PEqualNP.Outside.L_meta_4373.tablesdead) PEqualNP.Outside.L_meta_4373.rootA PEqualNP.Outside.L_meta_4373.rootB
