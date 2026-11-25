import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Push

-- The signed-circuit bound is from dsgallups, PR 7286, commit 39863e78d5.
-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
namespace PEqualNP.Outside.L_meta_4269
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


def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v

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

def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [bit,bin]

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
def edgeMask : Sig :=
  let x := fun j => inputs.getD j zero
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) ||| (x 4 &&& x 0) |||
    (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) ||| (x 3 &&& x 8) ||| (x 5 &&& x 7) |||
    (x 6 &&& x 8) ||| (x 8 &&& x 5)
theorem edge_table (r : Row) : bit r graph = edge (sample r) := by
  rw [show graph = edgeMask by decide +kernel]
  simp only [edgeMask,bit,edge,sample,BitVec.getLsbD_or,BitVec.getLsbD_and]
  rfl
theorem seed_table : ∀ r : Row, bit r seed = !(sample r 0) := fun r => bit_neg r _
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem seed_nonzero : seed ≠ zero := by decide +kernel
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
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

def Excluded (binaryOnly : Bool) (T : Sig) (cap : Nat) (S : Finset Sig) :=
  ∀ k t, k ≤ cap → Live T k t S → (binaryOnly = true → t = 0) → False

theorem enum_step {binaryOnly : Bool} {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (oneStep : ∀ a ∈ ws, ∀ keep, neg a ∉ ws → proper (neg a) →
      (childOne ws a keep).length ≤ cap →
      Excluded binaryOnly T (cap-1) (childOne ws a keep).toFinset)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Excluded binaryOnly T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Excluded binaryOnly T cap ws.toFinset := by
  classical
  intro k t hk h
  generalize he : ws.toFinset = S at h
  induction h using Live.ind with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact fun _ => out (List.mem_toFinset.mp mem)
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
    exact fun only => oneStep a am keep fresh hz len k t (by omega) (eq.symm ▸ tail)
      (fun yes => by have := only yes; omega)
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

theorem closeChild_sound {binaryOnly : Bool} {raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Excluded binaryOnly T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild pools links k rest op = true) :
    Excluded binaryOnly T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · exact fun k t hk h _ => scalarPoolCut_sound (pValid _ hp) nd ok k t hk h

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
theorem evalMove_sound {binaryOnly : Bool} {raw T r s ws pools links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : (op==2)=false → a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Excluded binaryOnly T (cap-1) (List.toFinset xs))
    (pro : proper (movedDecor op a b).1) (fresh : (movedDecor op a b).1 ∉ ws.map Prod.fst)
    (test : evalMove (cap,ws.length,ws,preCov ws,pools,links) op a b (movedDecor op a b) ka kb = true) :
    Excluded binaryOnly T (cap-1) (moveFront ws op a b ka kb).toFinset := by
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

theorem node_sound {binaryOnly : Bool} {raw T r s ws pools links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Excluded binaryOnly T (cap-1) (List.toFinset xs))
    (checks : testAll (cap,ws.length,ws,preCov ws,pools,links) ws = true) :
    Excluded binaryOnly T cap (ws.map Prod.fst).toFinset := by
  by_cases hc : cap=0
  · intro k t hk h
    have ke : k=0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    obtain ⟨_,hS,_⟩ := h
    exact fun _ => out (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
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
        Excluded binaryOnly T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
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
theorem rotate_excluded {binaryOnly : Bool} {T n} {ws : List Sig} (hi : Excluded binaryOnly T n ws.toFinset)
    (p : List Move) (ok : autoOK T p = true) : Excluded binaryOnly T n (ws.map (movedWord p.reverse)).toFinset := by
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

theorem linkedSet_sound {binaryOnly : Bool} (g : Forest) (k : Nat)
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
    (earlier : ∀ i < (g.levels k).1, Excluded binaryOnly (targetOf g) k (stateSet g k i).toFinset)
    {pair out} (h : linkedSet g k pair = some out) :
    Excluded binaryOnly (targetOf g) k out.toFinset := by
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

theorem checkedNode {binaryOnly : Bool} (g : Forest) (k i : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols, Slice (varsX (rawMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, Excluded binaryOnly (targetOf g) (k-1) (stateSet g (k-1) j).toFinset)
    (checked : nodeVerified g k i = true) : Excluded binaryOnly (targetOf g) k (stateSet g k i).toFinset := by
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
    exact fun _ => hT (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
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


theorem nodeVerified_sound (g : Forest) (k i : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols, Slice (varsX (rawMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, Impossible (targetOf g) (k-1) (stateSet g (k-1) j).toFinset)
    (checked : nodeVerified g k i = true) : Impossible (targetOf g) k (stateSet g k i).toFinset := by
  have all := checkedNode (binaryOnly:=false) g k i samples cols names
    (fun hk j hj t u ht h _ => prior hk j hj t u ht h) checked
  exact fun t u ht h => all t u ht h (by simp)

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

def pairIndices : List Nat → List (Nat × Nat)
  | [] => []
  | i::tail => tail.map (i,·) ++ pairIndices tail

theorem lanes_append {α} (field : α → Bits) (left right : List α) :
    combineLanes field (left ++ right) = combineLanes field left +
      2^(769 * left.length) * combineLanes field right := by
  induction left with
  | nil => simp [combineLanes]
  | cons first tail ih =>
    simp only [List.cons_append,List.length_cons,combineLanes,lanePlace,ih]
    rw [Nat.mul_succ 769 tail.length,Nat.pow_add,Nat.mul_add]
    exact (show ∀ a b c d e : Nat, a*b + a*(c*d) + e = (a*b + e) + (c*a)*d
      from fun a b c d e => by ac_rfl) _ _ _ _ _

theorem lanes_map {α β} (field : β → Bits) (select : α → β) (items : List α) :
    combineLanes field (items.map select) = combineLanes (fun item => field (select item)) items := by
  induction items with
  | nil => rfl
  | cons first tail ih => simp only [List.map_cons,combineLanes,ih]

def pairColumn (left : Bool) (field : Nat → Bits) : List Nat → Nat
  | [] => 0
  | index :: tail =>
    let row := if left then units tail.length * (field index).toNat else combineLanes field tail
    row + (pairColumn left field tail <<< (769 * tail.length))

theorem pairColumn_eq (left : Bool) (field : Nat → Bits) (indices : List Nat) :
    pairColumn left field indices = combineLanes
      (fun pair => field (if left then pair.1 else pair.2)) (pairIndices indices) := by
  induction indices with
  | nil => rfl
  | cons index tail ih =>
    rw [pairColumn,pairIndices,lanes_append,lanes_map,List.length_map,ih,Nat.shiftLeft_eq]
    cases left <;> simp only [ite_false,ite_true,Bool.false_eq_true]
    · rw [Nat.mul_comm (combineLanes _ _)]
    · rw [broadcast (field index) tail,Nat.mul_comm (combineLanes _ (pairIndices tail))]

def uniformCov (r : Nat) (v : Cov) : PackedCov :=
  (r*v.1.toNat,r*v.2.1.toNat,r*v.2.2.toNat)

def pairPass (c : NodeContext) (pairs : List (Nat × Nat)) (r : Nat)
    (a b : PackedSig) (op : Nat) (ka kb : Bool) : Bool :=
  let n := 1+(c.2.1-(if ka then 0 else 1)-(if kb then 0 else 1))
  if n>c.1 then true else
    let d := n==c.1
    let z := packedOp (r*(BitVec.allOnes 768).toNat) op a b
    let rest := takePacked (uniformCov r (getCov c.2.2.2.1 d))
      (packedColumn d a) (packedColumn d b) false ka kb
    let marks := fullMarks r (rest ||| packedColumn d z)
    onMarks (fun ij => fallbackAt c ij.1 ij.2 op ka kb) marks pairs

def pairPasses (c : NodeContext) (indices : List Nat) :=
  let pairs := pairIndices indices
  let r := units pairs.length
  let side := fun left => (pairColumn left (fun i => (contextWire c i).2.1) indices,
    pairColumn left (fun i => (contextWire c i).2.2) indices)
  let a := side true
  let b := side false
  let pass := pairPass c pairs r a b
  let four := fun op => pass op false false && pass op true false &&
    pass op false true && pass op true true
  four 0 && four 1

def verifyPairs (c : NodeContext) :=
  let indices := List.range c.2.2.1.length
  indices.all (fun i => checkAt c i i 2 false false && checkAt c i i 2 true true) &&
    pairPasses c indices

def cert (g : Forest) (k i : Nat) :=
  let c := contextOf g k i
  prelim (targetOf g) c && verifyPairs c

theorem uniform_packed {α} (v : Cov) (xs : List α) :
    uniformCov (units xs.length) v = packedCov (fun _ => v) xs := by
  simp only [uniformCov,packedCov,broadcast]

theorem pairPassAt (c : NodeContext) (pairs : List (Nat × Nat)) (op : Nat) (hop : op ≠ 2)
    (ka kb : Bool) (ij : Nat × Nat) (mem : ij ∈ pairs)
    (pass : pairPass c pairs (units pairs.length)
      (packedSig (fun p => (contextWire c p.1).2) pairs)
      (packedSig (fun p => (contextWire c p.2).2) pairs) op ka kb = true) :
    checkAt c ij.1 ij.2 op ka kb = true := by
  let n := 1+(c.2.1-(if ka then 0 else 1)-(if kb then 0 else 1))
  let d := n==c.1
  have un : (op==2)=false := beq_eq_false_iff_ne.mpr hop
  let field := fun p : Nat × Nat => combField c d false ka kb op p.1 p.2
  by_cases over : n>c.1
  · simp only [checkAt,evalMove,un,Bool.false_or,show 1+(c.2.1-_-_)>c.1 from over,ite_true]
  · by_cases hit : field ij = BitVec.allOnes 768
    · unfold pairPass at pass
      change (if n>c.1 then true else _) = true at pass
      rw [ite_eq_right over] at pass
      simp only [uniform_packed,packed_op,packed_column,takePacked_ok,lanes_or] at pass
      change onMarks _ (fullMarks (units pairs.length) (combineLanes field pairs)) pairs=true at pass
      obtain ⟨i,hi,eq⟩ := List.getElem_of_mem mem
      have mark := mark_at field pairs i hi
      rw [eq,hit] at mark
      have ok := marked_ok _ _ _ i hi (mark.trans (beq_self_eq_true _)) pass
      rw [eq] at ok
      exact fallback_sound ok
    · have no : (field ij != BitVec.allOnes 768) = true := bne_iff_ne.mpr hit
      simp only [checkAt,evalMove,un,Bool.false_or]
      change (if n>c.1 then true else if field ij != BitVec.allOnes 768 then true else _) = true
      rw [ite_eq_right over,no]
      rfl

theorem pairPassesAt (c : NodeContext) (indices : List Nat) (pass : pairPasses c indices=true)
    (i j : Nat) (mem : (i,j) ∈ pairIndices indices) (d : Bool) :
    testPair c (contextWire c i) (contextWire c j) d = true := by
  simp only [pairPasses,pairColumn_eq,ite_true,Bool.false_eq_true,ite_false,Bool.and_eq_true] at pass
  cases d <;> simp only [testPair,Bool.false_eq_true,ite_false,ite_true,Bool.and_eq_true] <;>
    repeat' apply And.intro
  all_goals apply pairPassAt c (pairIndices indices) _ (by decide) _ _ (i,j) mem <;> tauto

theorem verifyPairs_ok (c : NodeContext) (pass : verifyPairs c=true) :
    testAll c c.2.2.1 = true := by
  let ids := List.range c.2.2.1.length
  simp only [verifyPairs,Bool.and_eq_true] at pass
  obtain ⟨unary,binary⟩ := pass
  have go (js : List Nat) (one : ∀ i ∈ js, i ∈ ids)
      (two : ∀ p ∈ pairIndices js, p ∈ pairIndices ids) : testAll c (js.map (contextWire c))=true := by
    induction js with
    | nil => rfl
    | cons i js ih =>
      have hu := List.all_eq_true.mp unary i (one i List.mem_cons_self)
      simp only [List.map_cons,testAll,testRow,Bool.and_eq_true,List.all_eq_true,List.mem_map]
      simp only [Bool.and_eq_true] at hu
      refine ⟨⟨hu,?_⟩,ih (fun j hj => one j (List.mem_cons_of_mem _ hj))
        (fun p hp => two p (List.mem_append_right _ hp))⟩
      rintro _ ⟨j,hj,rfl⟩
      have hm := two (i,j) (List.mem_append_left _ (List.mem_map_of_mem (f:=(i,·)) hj))
      exact ⟨pairPassesAt c _ binary i j hm false,pairPassesAt c _ binary i j hm true⟩
  have eq : ids.map (contextWire c) = c.2.2.1 := by
    apply List.ext_getElem
    · simp [ids]
    · intro i h1 h2
      simp [ids,contextWire,List.getD_eq_getElem?_getD,h2]
  rw [←eq]
  exact go ids (fun _ => id) (fun _ => id)

theorem cert_ok {g k i} (pass : cert g k i=true) : nodeVerified g k i=true := by
  simp only [cert,Bool.and_eq_true] at pass
  obtain ⟨hd,hv⟩ := pass
  rw [from_context,Bool.and_eq_true]
  exact ⟨hd,by split <;> first | rfl | exact verifyPairs_ok _ hv⟩

def certRange (g : Forest) (k start n : Nat) :=
  (List.range' start n).all (cert g k)

def certPieces (g : Forest) (k start n : Nat) : Nat → Prop
  | 0 => certRange g k start n = true
  | depth+1 => certPieces g k start (n/2) depth ∧
      certPieces g k (start+n/2) (n-n/2) depth

theorem certBlock {g k start n depth} (h : certPieces g k start n depth) :
    block g k start n = true := by
  induction depth generalizing start n with
  | zero =>
    apply makeBlock
    intro i lo hi
    exact cert_ok (List.all_eq_true.mp h i (by simpa using And.intro lo hi))
  | succ depth ih =>
    have both := block_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using both

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
def g15samples : Array (Bits × Bits) := [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbaf3ea78de4d799d,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff450cc90c3c245919),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdf7ff8fe9f9b7ed5,0x20812421801324c4),(0xefbdbf97f9f6bf6a,0x102a401415600a0a),(0xf3a9d7437375f5ba,0xfc028ab620235b0),(0,0),(0,0),(0,0),(0,0),(0,0)].toArray
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
def g31samples : Array (Bits × Bits) := [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdafffab2d55fb9f999d9ceeefacb357b78f9ce2bb554a3bac97b2a9d65,0x250142092220460600407048c382809c2160e048740030a88143281c44),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffef5dfed46f26fea572a7ba9effd7341aff97ad1ab5bd2d547d6793334b,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff90aa211010d10141c4300836206168204010183680184d04682483210b),(0x73ef3f3c8ff8df3fe567b556c9567ffcd665219778a6bd6e36bfd946ac,0xc10d0c3000214920a0d648109801012344d60802686b04210115006a4),(0x7c7fd57b7ffa3476e74d6f3fc4bddbd44dc213c5eb8bdea95bf6ee7492,0x38022048645c06490200044a25241818912934541000824c322ae5002),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8fe76ff6451fda6ff84b6daf38f5bb6f6a5ee88a4d6be3f71c64aa3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8076989008882001270e063010011622500c04308a174300141c40a239),(0,0),(0,0),(0,0),(0,0)].toArray
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
def g47samples : Array (Bits × Bits) := [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffddffff5cfaafae7dd35b9ce7bbffd6b6b7b7cfbb8d3b7ad85ddf257b56b575,0x2200a042011011800c00803812181c2009c1061c0107200c09440143143444),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeebefed537937fcb8ab173daa7df7f7691aff9776b2b7dcb92a3f3678b2b59,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9149112428688034a38448020d64a21d120601022ea84882b022a624830919),(0x77db9fef67fc77f3ffe6e3dd55f86b6fffcab66472f7c57fb768dabfad4eae,0x820641080010508440806b120004c020121a4ec1002247c020840112806a4),(0x78ebe4ae9ffd0d576de696b3cff805db7d426c00d8ded437ed436ff6f66c92,0x71419416322f057a950700411b6b328381c4110e8d4580325370f22d66812),(0,0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0bf9ebdb2287acd4afec26dbb6d98eabb3768bb508ca4b7f1fdd1c709a3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80f74f1424444852a26637058ca3a012d22680c12e48c8e17411561c608a3b),(0,0),(0,0),(0,0)].toArray
def g47columns : List ColumnInfo := [(8,0,39,0,4)]
def g47autos : List (List Nat) := [[],[83,32]]
def g47levels : Nat → Packing
  | _ => emptyPacking
def g47index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g47 : Forest := ⟨47,4,fun j => g47samples[j]?.getD (0,0),g47columns,g47autos,g47levels,g47index⟩
def g55samples : Array (Bits × Bits) := [(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbfffffdf7defdfafbfd3fcebcfdeffcebffefe76de77fed7f1773f95eb2ebeb,0x400028000010005000000400701010180030103060043200102204010904888),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdb7fbfbb9ad3afd94caf0b9db5bbdf7f7d39bfcdadcf77ec9eccd2fb9cf16b5,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2484444214284026a4e002420468a8a43140a00408d944460a4082569431231),(0xeda5e7e7b2fc29de4ffc371dba2bf0775ff12db9b18bb528fedad96afcd3c5e,0x12589919410293410206d0396285445a082c5d2bf0022b20f0895d2048c2c4e),(0,0),(0xf1cd79264efe956afa7a64bb677ab40beba463600362eda36f3357b7d763926,0xe3a8651b1a36a0acc57538a080f6ea703078a0c13c28dc34c91f3868663126),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe05fe74eda341d5872cbf684d5e2ed19e7e3bba5e964550dd792aec724f479,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01fb53db1204342a549861b60b6727a22d48ac0b14da4445855161ae724b471),(0,0),(0,0),(0,0)].toArray
def g55columns : List ColumnInfo := [(16,0,39,0,4)]
def g55autos : List (List Nat) := [[],[84]]
def g55levels : Nat → Packing
  | _ => emptyPacking
def g55index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g55 : Forest := ⟨55,4,fun j => g55samples[j]?.getD (0,0),g55columns,g55autos,g55levels,g55index⟩
def g63samples : Array (Bits × Bits) := [(0xdabffdfdbdf61bfbfc7dcbe34f7f1b17917df75df7edd9eff77b6dbd3dcebed3cfbfaddba50fcabded46bc9b579eb7bd3d92776566ad4ad3debe36d74deb7f9faf189ad76da7dc1a6b4eaf21eb254de4ae1f7451bb34d9456fd18e934db17349,0x4400202400040800310000100084000ac0000102800a1100490002240004b2800a001b4000190000008108000574009200040400000594000190004218c0010840002890800550053044a00410008802d0060013000c004400188120c206208),(0xb6678efeffcbf5a9cad5bfd527a7a5bd74d1314b7915f5b2ffdec2fc5d978f8ab3b44b2b5add5b771711b15ce99bf2b3f5bce975ef94cd59a34e76ab937848a94ef6be6c9579db5905539ea703c87a7d4ae11fe2ae423fade4a3c3299b0724e7,0x499461811a200a55004cf88854029340027a680613c002ec00233c1096d01045025d0203d400243150030b7e4900b00499e023395882049d0206ec00041398010bbb1000b7310ad00cc0858112c8207810e917400e423d0034024309910504e5),(0xbfdd27bedf8fade4776ebf9d185bc5bd76aeffb29711f77d628e86e5fffdff6d1a52bff6da987348e3e147dcecdbcc68d1accc4e7d7d77b9734cfbbcefbc022d72eff5a31a72e32584dd5a72accb1256ede309af577ea6b3ab2be572a2769632,0x20983204990108b1910222a2810c12a8041040402e00006394000908008912a582448429aad10a21a0240190b504314209040621245140c82010e8812042049440841100c0c52080310832a5111106e902488a012c82618908a42202729212),(0x77ddb87389d95f9f7bbe7e8eb89e6e76fbf75ca7fd5bb3758b555b578affe964ae7e7fa493e06d03bebc4fb5cff51e46b2dd5bdbb1eab66f60f7d916b9c6944fd85b6f0fc30a2ae7d2afc9dc369ef80bb1b0b2dd52e9331e786f7a5d38e8c8b4,0x1482478012444200420888514440810c402202189081ecc814422aa4c048408050190921c0450c000a080254044021081134422900082c11250884167012813a48094aca870a3283708e41084282480000c012150640581c30655a55288040a4),(0xdca768aafb78ce8d2db2ec3fbdddfa4ec963339dbac7a8e05eccbf0bb99ddf5febcef6dc7762a4a79d9ad8f70324ba6e724754bded1eed86f695f276b70acbd73dc66e39a88d0cfed920a0ee10b5a4dd5893bba709bff6dc1ece388c561e1ed5,0x210938550593284a984457082a220ca002159526023c0223a02100100d271046aa46f2022bb0201ea5730921b3008e848a002106a7520082d20653c8040064810364a00030c5086c0c2084761035a077101508a009ba22e00b822088521e1c51),(0x77dad76bd4ced656e7ec247a694c9eb5b66dc4de71aac18acebb177a9bac7a62d6f3e3996dd9d62d6ecf7b18557229a30b5ebb1ef46b568a8f3400a7c2d3365caade63d0f2234a24623735bcfaee29c0664eddfc63b2a86915f817ca03dc41fa,0x88252894b2b3256598a758928465236453b27d28c68c4c28a24dcc0d24d500d4a845700845b04bd175706d345a20a0a24d641d897dd822a1d52444cad2629c8e732b305273362844202335b73c8d8150424e93e44a78286995ec17c803dc01f2),(0,0),(0,0),(0,0)].toArray
def g63columns : List ColumnInfo := [(32,0,31,0,7)]
def g63autos : List (List Nat) := [[],[50,65]]
def g63levels : Nat → Packing
  | _ => emptyPacking
def g63index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g63 : Forest := ⟨63,7,fun j => g63samples[j]?.getD (0,0),g63columns,g63autos,g63levels,g63index⟩
def g111d6 (i : Nat) : Nat := 0x120ff
def g111l6 : Packing := (1,0,2,0,1,0,0,g111d6)
def g111samples : Array (Bits × Bits) := [(0xeafcc7b96fc59ffd26c5e2bb3d7bd378fb35ff5dcb26f92afa5f57eff59a73b7aaa379b2fc8d7a99e2ef9efcf4defd4efabc9c89733cebade5579ad5abbcd64d8557ad3d63bd1c6a75510ce3b9bf05e462ee0edf6dfb2914efc74c7d31727465,0x4d00310a2003881269402d0c00406ccc142a8012908082d00025ac006a88036948003229000032d4001bf20024ec2018680000aaf2500325400423a6f02003840040a8016ea8106822700071012c01d500600ad401ea0010f407087831504444),(0xf771ad34ff2bcf4fbd7f5f5de52efaeb7ebbabfffefbf2eab7c7cf56f8ecea565ddfabcf87cb61db9d6ef4aecff7cebd76fe679cfb9935e6adabc77cdcdb677ed3da5e4f56b4cbe39cfd7aed1f519a6b999796b48a51f4f7b8ad91a66cc6d9cb,0x1204940050200482000010001c10308054448009004424020800871400ac0690000402004e0508404004081210450414000904018220d090010808000a44280600460810104d92040818880c1010088d8400200a10a1400808810604821909),(0xf5be76df5e79b8b5d13f5f6e3ecd176fbeee538a7cfb9f7f6b7fad9b13bb7fed97560ecd71f29f3f1e3ef959a338e3a9e32bd5e7cfc7b51df73d7e9e165479b3baa9a0d59e62e11eead3ad5c624777de8699f96d3766d64d1f3fa2ca8f3d2e52,0x8e4d19200884440101e4a802e100a0c04000830eb000289800c49240c1c411082c325a6812b0485430294040c52402008322a4b0e00c0021216842103a050a9080848145264020288841a770220547500211500d95204c05521120880b352452),(0xde2ebbc73c1cf83c4cedbed77297d7f5b666582db23d5c5d7bf4a54b37a75f4992f88d683d388ea5bafb57791a5deb9b257390777cf70e9d329773c24416edd93fe3d2909bc3b81d7e62dd94d70a759eb42b6b51587d63da2e7eea6ce78912bc,0x10b22099c5638280b403142808691e02bd9d04d1097a9640ce2041351e20e64283892100494815238b12089820999d9858901b4e1903515e001721098578a5416f515492d981d895722018845902b08a5c4a2a2248dd03d08c66ca64e48812ac),(0,0),(0x4a99db5e74fdf3bbfb83b4b12e735e58f515867b75942dba656f9eeac55739b971685432ece5b39368c30fbbb9f895ca9efa5eceda2fea7be4766f052ba5def635ccf928215f7640050f6846acafb2ca6efbba0bffbfdb9043d87d111c3c3ebd,0x12d68401de50564414b80023f49c0203c0413d800068400bbb08034f0177ac0427f40400f6de0023bcc009fc1201950403ff4900082ea08a2fc908010c8a4053de0011e801464d050407f806ac13f8026d9b800bfa055d40038875010c2c3ab9),(0x107b7e8791b6519a9ebd6f37d374faa298392ebad8b5e4afe6bd267679568b3365bebaabdf6ef4e9035a918e8ca50ef74769b2b74aea726a09a6c5e9463715fb76745a9b1b6212a1b9add6dec52a9ba55b57e399ab660ca6d0f217384af881fe,0xadc48a6a24248ac9294916cc74a18dce4988890976a839d0a90054480a8f001149b409fd5690d8d50882129489ae3083c83b5253565cd02541ca4550f495b985581508b28aaa022919a1e755a00eaaa54243a315f06a0c87d4f216384a7880f6),(0,0),(0,0)].toArray
def g111columns : List ColumnInfo := [(4,8,99,0,4),(1,32,78,0,4),(64,0,47,0,5)]
def g111autos : List (List Nat) := [[],[83,32]]
def g111levels : Nat → Packing
  | 6 => g111l6
  | _ => emptyPacking
def g111index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | _ => fun _ => none
def g111 : Forest := ⟨111,6,fun j => g111samples[j]?.getD (0,0),g111columns,g111autos,g111levels,g111index⟩
def g119samples : Array (Bits × Bits) := [(0xfab75f3dfbfa3756f92d9ff7baf5ff7dbfebb9b33bef7dcdf77fbffe7bbbf75546cedccfd6f7eb762bef3ffdd2ede7abbef7e4e4b775eb9be6ab6f4d5fde77f2b955ece57b3feb97c6d99b5cdd2fdd2ea315de5f3efbf8d44ddcaa7566eda9cd,0x20100000802449000a820000c1900042800052080010000098c000620802429000050a2000012e00000be20013404000082000047420011240000c8b8000110080002480036500158018000c4009400c9000c0062803a0400e00885042a10888),(0xaf7efcd6de9febfb57d6f5ddedde36f3db7fffeed79fdbfafcf255738c743cbbbff3e3b86b8f9fb9f5bdf54fbff79bd74f5afb3f7fba34f5bf5f9afae879ab5feefe93fa9ee6566f7bbee6bf67d426d75cfb2bace9344fabf72bd58e999b76b3,0x9300010000091004000400382060802420900110020801010208161810541520000000800198110400c004084880812115000049028020c0800220200009220a01801050108206a8408406120184808104430800802442850101410609083421),(0xd3aee9d1a16b8afb579b1b1a2ede96c634714fced4ed35afb8d86696aabedb2eada373270f48f3a9b93de8a90d87d8f6684756adef8eb40bf672fc78b9342c9c7aaa652b2aec9422dd38b32b2a5255bdcc3d35b2da5f372953f3c4ba3a70d996,0x2c07b23e74020fd2aa41748155856818d263d681015680dac92709c7448b08586eaf3a512642c64b613a9091954b38c222671d26711d023332d48951dd0691952839212f8b6888039910b9ac2a42653c283c65315b1b95185ae084b83270c996),(0,0),(0x759a506bc07865de6f37bc2fabe39a5e2705b6a3eec6bd3cca572e3ed72f0325f632aa43d8e0e833eaeab6f86ad5fa72dbaf9c83b9e70faa212acf122e177ae733d8fa39a0b0bb12b7915f7134c3b9a9ed98d75362b1d9c725676c3caf04637c,0x16e5f59c6d01a255c44806523c0cddb5529a2196d082e7c24415d298c0f10d071e6090549dc090f8ed501938009f3fb2169588d90b0b506d102e01343cb84ad135f45369a498be0a36011e712702bb816af81651c4b05c0701a6642cad046374),(0x6339c3e76f77dc41ec6c9766b8b0f93592cd6e58a17db2abb9eea5cd269eeae2dc2c1c9ec755bae6a2821f6b678c3538a75edaf56c57e97ff4e8b90d55c4e75ce36b37ac511be4c610c6f229b9ab77956345b3a117ef6f3608dd37697870ba61,0x84ef690f5888a6bc0049f9381c0ba0115db000874a075d2102333605e754184fe100105f739880fb92c019ec481f2d2102dbf2480954a0ad3f922114724920d57f80032e5018c6a22083e62199863ec06b43378157e41d3d00d937293850b261),(0xd5cc96ab2735f4eedbcfece9fd4d847149d75b8aa71ff3959066dc7566c66ecb75975abde9bb8d684d89311f3151135dd1ce4d97acd9737d0b4d97b62b1596cf57b51ab1b6b408593b67d5bb928b32dabad66fc43367241aeaae177095e247ea,0x481560b0cd924918c5323d4303992d88d1232e6a49f254a2454320824e8122936522ef3572424e688310332525616c12e023da92a435d213539c9243b254cc21b63548a8e4258841b361f1c95a017252ba1c47902bc1245a7a8e167094e243ca),(0,0),(0,0)].toArray
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
def g189samples : Array (Bits × Bits) := [(0x76b7b935ad7f6fd4d735f26d2df10ff4361bcad97bdde979efcd6e58b7554d7ea7eff73e73de92e56562d7533a4ef3de34b1f6acf1d6e216666babd43dbaabce3ad8d545ed4e53771cb4e6d84ab365f9722155b0decf672135d0ab0e8aab3265,0x8404642124899480a2a81184400c4494a40542200633c0114901482008a100b4c40690c02a500485280025a8300be5004d078022244028e4a0122910034dd0088624c002500565400b4701a401901a06a801c60d40e430038408b0c08aa0264),(0,0),(0xb725f7b34edfbeffaf8e64c99fca263eeb8ebd6e6efba6759d07fff35f0d57cf0f1af1c8e8596f2d9f9a363b65aade972ff9af593499366f72b4e55d5e6f961954d5fce693a74e66d370dbbd59357a0ab5d8c2e2b4913d9ddc0ac963246654eb,0x2019084c910042485050a84580141012107000421c10cd02a29a004c0424911090cb1414ac1a4012048a60a1130c00921224ba8854044c203120d1318881010110848d88109408245548f0845c253042044cc0e02091152804424943044214c9),(0x6b3b37beb0d3b3db67cafb77eb9e1dd789aebdb18d1db77732f653e35977f97f4dd313687fb67a399a5d29e7c5c2df2ae361e9d1a8a6a7bdf9b41bf76bf3c59c972736ba642a6ec8e10ddd388a5d8a2fef454b2f6c5cd8cb4dafd1a5458caf32,0x84c42401462a8882042c15880121e0040f09501440a3008044047580824b00c92204cb801220a2e8d004050a8c13a8082552010080e322ce0002224042220e86c96110212062d680201609100358082de8010e0a0c4e080169249024018caa32),(0xeed4ecfef66eeb7efebdd9aee7077cf1671b7b7a97dfdfd372d0ed94ede3ade9c50737565e265d36d07689d4ac4faafe5abbfdc5676e89f79f8f9a623b38502f3db98ff0fa982b81b88d0790fae9d8d74f74351d5187af7a955e769667c1914c,0x112b0124099000041080680538580102a03620812918016ca82b084951200b0011391441e40a1406003a00a460640102802906c05910d52121d05c00b8012058249003c452192901d049060038a0e052051c011422a1a0780618649266411108),(0xd9cafe65094bbf5f7264b7bbce3ffbefdc6762cbb35969c8ac2ddbae62ff5a5f3ee2cea13be5ccd265ed5a725a1921f7f9e712e69e98fb2d45e97fd5f2e0abe4f3f7676b375491bf662220c7ec1235aaa52f7b260bfdf8f023b73c589c1c3f19,0x2215018860a440b0408528403b942810a5b0009c1c080302094a000184016510830b02e2ac10b810014a60046c8c012e120b028809b84c0105208c4e88802201101131880274018a550300819c02301e012cc3000b90a8a80382305084143519),(0,0),(0xe9cbc8feffb7f8e7b8d17ff4f26deb6af5fadcfef4fa8da189aed6c66eadfbba567e7aa58acda76b57bfee9d03799233ac5e277f4fab9af55d736c18d65d30adcab7ab9d1b9dcbcc02d24b67373e9182d29baedd99bcc115aa3d04dc337a48be,0x1420360100482d00252a00a2440945244a022b202187302c44004bb2035a00002400090800450025fa000d1a80010240a950404582409154ca522280124a1c0c672a40054909a2500214036203d800a092812c0514244211e81d048c33284826),(0,0)].toArray
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
def g127samples : Array (Bits × Bits) := [(0x27ec63be833e95d9cd8b1b0f8c7b949b955ab7ff06f2f46fb53d19a8b89e2cf938ea5b637a679113a99b1a558cf5d3757100e2a2d92956b1df648864a3a84cf9f5aafcc4980f547cd2d2abacb351593072ded0ca36876c216b176a15583d3069,0x215000b22a840210400a1040082a19401000220004808d00802008c02014082088420800402688520818425544410445400040805130408104600820a3600c001020e0440008143510802b10a111102142440000168440214816081150281060),(0xd1272c7d4d43f0bd72e56dab39ddfe7c6a407c139e413a8c95b2f6c7134bd9d2e6151acc0f6f6e61aecc859cb80ab9d38d1f9c08bbd08127631b9fb156aefb042a9049abe4f27cdb8815184a3fa2b5dede495570df2830da3c38c46cf1426d13,0x806000d540888802080408280406213088804000000320c048631024209804006241648090164a10080940a08001912a8109004a2408004431a0101080453200880088a80c0004a880100481a02008819080040c10830122428406420422c11),(0x3757a63bdee4ba3fd3e2275cd925bbac4327c3605b6a92ba668b6b375f5956a61c0ee4c8b6382a0c726a8d674c1d24e187c7697b46618e9a3259ec9e635cb1935494676727a9c6a3df6b34450ca72f271676b8367562d5a985429aaa9a64d626,0xe190134200c030558e6885084d0788a40161e860830e0412a109c61098d030850809a9902628890c322a09e446182064058721691005078a1841cc5c6248a09654242521162044855722240404692506023498262462c48981029a8a9a244222),(0x7c12f7ae7cb67a121957d4766ab145360dad0baa714fd5dd4ad95b9245e39e4cff88a61691dd24ee5570ea624367b54a6aea5375c626bc6f4082772e38770d5a1955fa1dcb198b20afa8d659c70c9ab5dbb42b955b55e374e0f839c3068a9694,0x100b203118264280010702e3020864421484020c18c0438c4090018044060d7096401604915660c20151c00201478d0220604290c2020821402022221025140809114a0c4919231288809339110498f1918002911b15216460582041008a9494),(0x5f0ed2cab79191489f9794fa9f865222c0c45f4f23977137ba6ec87e2fb718cbcb3281372d8190b9e5b2713c276012285f3b185c628f375c96ee95cada25845527c7ad5b31bc018c667be7de6cdf9480211b73e5e0fc0e1e03a683a80feb2399,0x4e04900c0410144f3ce0e018c1840020605099a3823d30032c4ce03413c1e08c412481b32c810028f486342022205010179b1c44008d375c030cd5d908008055e282051134c40088667900c444ea04000013f960e0680e1a03a083a80f412309),(0x64ed11ab034e6565aa5f6f0a73fb2abb553e90eaf5f2056f4f2ad1a6a7112f3107edc462d825611a42150349a39be3bcbdfa3bf68749fd950e410251758bd0aaed7e1f93ab81b400f6cd22629068e5bc2da9dbde283bbf115009f3b1a197a662,0x46299909050b25a18c71e62a5095c63ecb8f04a3c26b60b927cda532c109201915ade64b3091412042050108b390e3bab9cb9877060097580a090251508bf2aae7571e1ba185a2088a6c00621068c596ada8d9f5a83bbf101009f3a0a197a602),(0xed72aa63cb994444b8dcf183254b4e7cee24db3ad729ab4a1ba98c700af5e5480459e832e1cc5750368c89edf172492ed4565f186db3259850f427f3943aea1f7b1d745054d56ed5059c9e36e00b68fdae413f628aa9c64ad98b04d0b38dd9ac,0x4400b2628be723745844a119668f0ccc9303b92a933d014173710ec9a0c0658c41596832a4cc13563c0629c5d4a2402c44020f584d31651810e10cda143b2c95631f726414156f15141896b3a1182c75a6e53b222aa1c648d9830490938dd1ac),(0,0),(0,0)].toArray
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
def g191samples : Array (Bits × Bits) := [(0x6acfda3c2cb83a92b793db4cbe83faea9cb2634793e21db352fb83fe8df2bc07a86d83614e9e1d6652f73c866931a299021d0d35cea03b8bca899a3ae9b0852968ae39aed598c502d3cc66c95e3918558ba9636cd1546c95b4522b12e41c6251,0x8027018c1220821109402382a0c04040242201142810004800310a01021028020024504420900008134444101889108100844480011218a0808a088000429588a002494484002118004005c4110108908c2000154441190520210a0142200),(0x7913ceb593e8bd03514889e55f4c93639759259376fb3230720c9a865196f27cc74c193b9b758265cc3f7b6a39d891145642471fe1a3e402ed12036d66f3fc532a7d00122732be1cd6f8a0d631223ddb153772d463789a2c383ce02e7842d163,0x88036081c60419a2c82401d04754b2b302101402821d5c654204040641a4c69d42c491108805a675482c4b1a3210132646402113b58224122512010966d1b044833550122312b410427aa086012a6ec1101538c042289a0c282ca02a5842d161),(0x557693cafd0fd9424efb95e75ddf8ed5bd78c8ecb52fa208a8d45cb3574ccaab77d93b1e650b4399e9518160864e914bee471a4d6078d8cd3710b8c5462d299957d5836e24a95a7b253cdb2e6196070b78eaa32a2b4a267149c447650cd138a6,0x10c082401088400012d0c4008000004018ca8080142020182010002082500860100b028600824082a011044180428040210612040030c884904098c2002801191040822880a108c8040449084010010648220108084220210140474504110882),(0x9c642d62a2f2f7ba22bc048df67d49f5212576be5994f8cdc5e270babb8959b792802cb3e87f90d4054ae918d4ab1ce241d9cf541d5d16b72277276810cef58c9e0f2a3137066d66292bcd81a96583d025d9fd03afbb585aa2b81e898b063d44,0x8024093988519a8e002822a41919198600217873085849c0c483198871885081c08060615e498874054ab3104029780240914c50140c132321226228088464808a9608100702c12708ba84812c642a102598ac01a5195852a098180889063544),(0xd23eefb5d75806b89dcda38864b64661c9f5e2babc176a70b2d3a56f26f32e727e31fe7789e6e58a36284c9dbcb30e74d59821a10b67441120e71511dbf31ab50b42210b3baf1a3e4c47734dcff8958cfd1109f7ce27c18a062741ac46d7cd91,0x7413208444084451d48501104604c068b3980408840422121160844600658c78341c18180024668a9220480b8c940760b50821038273441010c51501633a18440140258228a50a1044455344031a81ae1001013e42228188062541a446c1c891),(0x44ee3263ec00331534507b30f50239085a477dc26fc97fafdd3677e1adedabf5a6627a917685fed951e16b05c441608531a6eebab7bf0ffa2c9d6923c000425ae070ded9cbf43ff0702d561449016826463c1cddf881bbc98109fdb0912bda0a,0x5c9601812402000310c10a308504200a188ca4d220b13a418220c4ac1700cc49329049900289169c4a408a09044020043184b638a739649c2011540242004250a0701ac901871eb02048c310010048264632184cec01aac801096da0110b580a),(0,0),(0x3ab08ab4b6d74c50e56bc9651caf5894b179e03465572acbdca5615696769c27053d6dc580568c9318a62a712d4d06df8fcf0933a8a96615b24c8891d85dee28deccf746ecda09546a23c7138dbf2215a9d969340b49504d34d905859a5a4fc,0x8020482e4971b288ed202044508b9ca5050108094844412451461041282e3192c9648008d0242841110660a6538444294c484083188002614b0e00011891a8820d8e45006648e00548a230c32acf32918089829300b41504d204901848a4a474),(0,0)].toArray
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
def g251samples : Array (Bits × Bits) := [(0x7c5b1073c997e37379da30f398119ee6fb6b9ec3f472bcb960b6e16b764eab308775a6f93b85666e9d3190b2b24d642ca5712b6de7ab3f7906c1699135342a691b3ae0a5aa4ef7bb316cf861cfcc30541d6a6cc4992b1a999615c8e8d911c1e1,0x2118206040004a02130d09680103a002090a061080141a8c00302460220208340600a251588102029c90b010225400202065234404234e080480294178042009180840240246b20a0024c060c50410001a48a084882a181106058840c1114140),(0xcce5a5f376b735aeaefe578ced15d32ecca61663a9af3bd1860bc21b19116b79223f9d41251db7915d2d676e62aaa4f819f9d341f91890478f7c179edecb18b88452ff03ce59b2503e9c1117dab8cd95ebc956b7a216470f30e3a2b3ec2d18bb,0x4842cb022293909020208080c0985104462050200a232050248f580a09002349282c0500277025a04229050a00aa2098018840837118b0c40a78400806c358a084123a0140090810bc8810142aa8e601010152222014470a10a222b02c2818b9),(0,0),(0x615f43b7c5899d56d0ed540d07e5651da134ed341e9bc1f74f237fc0ae8a342e74d0d54381c29b89aafb968c73300f2ad24e70d94c925aaf7c71d97b8e42ee34b1eb0d1c78f57307cdbb8ab0333b96f243ce283ea4988c525a6cf93575cb22d6,0x600508638c1a9f0381c44ce96aa5f40532886e32158a42c5402a7e6c4a89343c9410964685c08b09acb0120c353c06229a6c00c94c92de87444159522882ae0499430c1549527146cd2ac810537252985246622c84980c521a4cf835558922d2),(0x743743261165c64a5893c74b56706899b56f313d76fa70640bd59bea9f4cd6cd40c9796a92725dcea2baccf628444b5fc70e36349d152cf473b98c6d967cf8571ea4949a30a5a9a67c52f2db3fa12e66e966315b35ec80fa603e034c2e56ad7c,0x8e228200012500a04432a202145800c8c044118122412020998581138524c38140cb492802205484420a48e00002411d45001410a1402070b13084088559515204a0a28a24a10ca03050168720812c4621201151314480a8603203082a468c2c),(0xf3d9bb1a8ffcdc97c518eaf4c8cf14e122f0fafd99d5fdca7ef0f64eebb658a39d280ab679b66835384c18039df39cc970c09cab32e75b6d986af50aa1e14f67f56dcf6f41924d79e9e39f3990e7fa0a34138f4a5e417d209f607f101fc4fe09,0x9201861738918010c41062040c8818244620088911c0e1638783100880a45083c120082600262524204640020401ded90000982b30080131d06c4002816148a041658f0100904561e8880e0910f0e60220020e2216414120916065101cc4aa09),(0x8c34b489b6743f0cbbb4f14fa7d16d9fa49b993f9ba2b3789eb911d5e1cd7a6f64e2a177140a8013c504eb6dd8b5e7f7e94f5a351463882a81261e97691b96dcefd6ddbc37c1e3432aa0876640524995f6a595fd43d7d81429dbe94302afe942,0x269c30c1984c0e0408d2577d35632830a8c6a4165540daa693102041644d9ca647426045188a80110514e824d9155760ee46136c04410a2a918614976910825e2b85c52c35a0b36b4200852245520814f6b484dd43c398142959c9430287e142),(0x1bb2ab4aa0e85ba9e596de5ec3ce129b01134cce9757f2d674620576a8bd96bf3a893c9457f0a28da9ccac591d7731877093a6c205d64d4c2bcaa6363cd0b55e770f7a466dfb2a9c82572d4ce3aa90cf64d9c30549ce2fe50b809671629a567c,0xd9639e04222012901869c59f133e18908110146a61f169c201c69140019863c2e851098d7d900098988b54119762026501322c440c64c4e0e9086343c860556368a70222d632a1a145321c6e30c00cc44fdf181498e2ec50a809261621a5474),(0,0)].toArray
def g251columns : List ColumnInfo := [(8,0,243,0,7)]
def g251autos : List (List Nat) := [[],[84,115],[99,65],[118,84,115,65],[118,81],[118,84,99,81]]
def g251levels : Nat → Packing
  | _ => emptyPacking
def g251index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g251 : Forest := ⟨251,7,fun j => g251samples[j]?.getD (0,0),g251columns,g251autos,g251levels,g251index⟩
def g255samples : Array (Bits × Bits) := [(0x9b665c544a8481c32c829a3849d25a0c2e734bceaece0410b1910c9246b692285657c973ca335d593cb00f0546b90059eb43e97a932728851785431870f031165ac8b80393ba6e576270cc58c906b870841734e15dc89803598ab05c2460a6b1,0x104454110880808228020a2041d8002c08600a02808c02009111060244ac12008614a1024802115108904700443200508241c8821224200116051018407029164080a01212302c0942400010c90428108414142154888803090a9048202086a0),(0xf315668af28fdb1ca228365b7ccc05a0011317731e21482f697635c521d4e57b4580944cacd08190116899ef79421d834fcee4e488905930903982805fb1c61927af17aaf49049a676974192f0d0160363a1bd03830701b0dc1f8281c2dc6123,0x83112a82400c43108201140b24040542001210600e014836084820c40800442b4181104024900000902098cc210099010006246088901220003082011981800902040620cc814002101041843090160043212902810201b054050081825c2101),(0x380526282fa13ac851f4c9c505254980d6e8ec3804b3594a769d93b950ebc251b0d8e2a15610b8154799066089743516386914b45de9a6e1e91c2d64aa4bec2945782990b2d68e61aa4d3cd1b24a6ab680984b4c1298da14a63264e421a50a46,0x184000082381184051a442400021c800c760240c008201086414493150c8805030586481420228050588002082640402084818905528808149002d00020c144045280184104604602a043c40824a60b20098024012185a048212646400810a02),(0x96903da21572f2b1f1c959078994a771bc47364121282ac5966e24786e0f6b8886ae49c27124b27b7242ff2e0094e0b4b1b582696d3c94568c371a6b03b30075a8d6353ad9672c0089eb12ba6325f80dd24d451b8459a7c113618d0b812f118c,0x86100cb01034a2a12848198388d4226018030240202c8a411a0a044824066a838a240842212092185a40cf0a0080e094a530c6680a1400448645526011312024a0c7343889210800016b021a61259805924545098441a1c11120810b812e1184),(0xca830c6ee5a1c1ac77b2c4bb013b84b271c7189edce77b42164b82b2ec44ccc2202552493f52e619512b4f09e2177ba801c291327039cbf4fba1fd7ca29d36ceca40c4508827295a1b45be11b7c00687be220f65622167c80c13fe90c415919,0x1282044674a181cc515204830038803270c71014e5265b22464b9241a4004482002443590d10ca0850630203a411b2a000c201185038c3861ba0d078200d6480c204804048212d4a89449e11258006869a220d60222163c80c12ea00c414819),(0xadcb89db333a54791fc5b16de6a74b1fbdaa5224c4caa060c8434905e130b3e50875189fa3aee40ebf67487ce98db2673644923b555505294552488c144494c2312ef3656d2d51ee39b1b44e04f3d3ec4d148000ab72771f011403179f478e82,0xa991884a13221d3803c5e045a0014312e78660240442614040424905201081f109410899826ca6043646807ca808b20b342020284941850001124c8410049440302c118d6904416438b533460072d3ec490080008b50771c0014031517470802),(0xccf1d170b069949f14600d7679a83ea985e068495997ad010287ff4ea745b576050c4fa9e8e0fabd2497448bd27a5aa8acea4ac0268e4d44dc2df9de452a225ad1457b3d721818b9bf9e05034d50ecb938aed67098a522a72856072e55b8d214,0xce85130b040942f1560095449a91aad8dc0e80b5196a18140955b282345b194266c47298868eeb9221d4601c27a00e8acf04a8036004c04cc8c58ecc43a23d68161791d311c0cb9abcc24434d40e8b9388ed67018a522072852072e55a0d214),(0x442aa5b9d884c622461c21eaaaf556fac8da8923687abbfb99c9c28096422e0eb83cb34c1d8918aec8c55d99f53bc2670104934ee2f27258616b2c55a56fa8970e02486406e9b92b5242282d15890d903f02672424a3e96d3ce1d022fa0aa8e8,0x460a679588446000a40a01aa08c414e80818810338389a92898982c08602320ec02091061180118a88016c815113416481048146a2821250206d8051a4632a958802cc600689381b004a400915810c003602652424a380613ce19002e808a0e8),(0,0)].toArray
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
def g383samples : Array (Bits × Bits) := [(0x22c0d3a3723e453b61b292904161c19166ba4156452239cb2ce776d1285888036922ca069735ba1c39466bb49cb80c880d6801ee650cd2ea8938a452f08d3169a1612a59384753bad95626662c63076161205bac29b905015369815a61884cb1,0x22a042a308281022412222104041018102a0455c0820218028210490004898014122a802062510400900403480940c80084001804506910881200012c0203148e041211030641239500420000c630440212052a0291101014268811220880c80),(0x3e4782180591e1e8ca415c93fb0e30440ddb7b080a80044a5e58703417b0ed0da2975b6df4e0151155ba1024096257dc7280e61c3739c9924483ab0a0d0a407f268250f5cf15b48886f76ba0ccf46838068d8de07060e07838bc1a040b61c283,0x9028018810161088ac0504223081040850928000290004c425070241b00400822080144b0c0241004a20000482053184202c40808184882448102000d0800b3040a404084018c8080110220c214483800898940502040781814120409604201),(0xc3b0d0243e2c92704a6d0bb89a642e3e324709614c855ba1b03c2574c53f0c84bca3b709607618aaaaca1686a79e094292d1a5b2e1a729d1ef4c761d2455891cd68664af136132ce19aaa19e6c55a2caed1460758145348a6cc923aa16a49516,0xc22070243c088a32102908b09820ae3610c20125cc051d809026055084360c62d8a3320940364922a8484682858e00c384d420b061233141a94434152055010c599024a50348105611a2a11e2441a2c2e41460350145348264c921aa12049512),(0x4138264952b1d12493a4452d72585b389605825093cff11edb60090262cf75191c382db2876b8a708e04945dba40fc5c0117030382d504a579e551698e39d387601c521a9a75d96750089c8958b895e01b82b803f01d0be08606741604bc230c,0x1080c0b03b031008084040c42504188060180103100c00a0a40008040890111041009902b010250040410442a404c140103030210c08ca050a00048c0a8c022200c1018d83149210000148108b815200b021800b00809600202141404b82204),(0x7a0c641d50044e150338db871c0d9c6d8b49b017941b1c71c485efc79a14e6ae159b09d8c200cd085276a758cd18f3623c4db7d00870524c281de7f5fe3e2adc1756b294808a0882ea6a1f2df107bc01d0df010f4d40469e2105ef94c107b239,0xd004201450464809021899a3188eb82288483003841b1c31c500f247991664ae92090048c000c90e723223084509b040f48cd45008304046281cf3843e140e8407928284000804822b6a8b24f004a801d0dd010f4440469e21056a80c1079039),(0xcc62da0a5fa8f5e2c996caf343c42faac6de9a345ff56a94813a6425060416282f4d23c281526277465dd835f65817a533b901ad51024edaaa84a94a69219208d911c25be8aad34a7f39eda22807bafd8e8540012ec5ecf42900c6dcd341c02,0x8452d0021128d5c8c9144a91d1c007ab845a00141d69e1982122246c02041428290423d28902225305595421e41c17a5023985a908040a15a0c4800269208200d9018058b1aa90485c38f99a2803baf58c8040010ec1ece00900c4d4d341002),(0xdaef1c77688221978d1e0c4ad4cf460c43747468370c9781a044ccfb808507cfc7550e6f05834be93d3c1e4e94918217a4e0da637baa95002472c84f89f63e421033ad28de7ab208228bfb0281a229d272553696158289b300da2c9976c32464,0x92e959624882001701040c005417432c02544069252c9701a0048cc280a00e56d4150e31071309c931151f4c9213080304e00a4233c09500a002c04d90b29c403071012c5a3a310c128ab91220a221c27244349605808983008a2c9966812464),(0,0),(0x941a1aee99450a81362f36506691ad42486aa7b56b55a36c2710c35afdccd2f0604110c2892f54d343a9228b60c516b3ea6e18394813263b179331842a516d8adc29c7c000c846f164b52014130d4016a078833106127956c94690a3b81ad1d8,0x4120210904c02803268a2402080b401402a07040a01006405204110294490a020401002d0205402c22800a1400c2280a20c04a14813021a0411310009012188c000460020c0069060300020050540108030832102126010c94480229002c198)].toArray
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
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
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
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_5_1 : block g31 5 1 2=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl31_5 : block g31 5 0 3 = true := (@block_merge g31 5 0 1 2 s31_5_0 s31_5_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_6_0 : block g31 6 0 1=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
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
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
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
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_6_1 : block g189 6 1 2=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl189_6 : block g189 6 0 3 = true := (@block_merge g189 6 0 1 2 s189_6_0 s189_6_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_7_0 : block g189 7 0 1=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
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
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_6 : block g191 6 0 1 = true := s191_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_7_0 : block g191 7 0 13=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_7_1 : block g191 7 13 15=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_7 : block g191 7 0 28 = true := (@block_merge g191 7 0 13 15 s191_7_0 s191_7_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_0 : block g191 8 0 7=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_1 : block g191 8 7 61=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_2 : block g191 8 68 32=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_8 : block g191 8 0 100 = true := (@block_merge g191 8 0 68 32 (@block_merge g191 8 0 7 61 s191_8_0 s191_8_1) s191_8_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_9_0 : block g191 9 0 3=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_9_1 : block g191 9 3 9=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_9 : block g191 9 0 12 = true := (@block_merge g191 9 0 3 9 s191_9_0 s191_9_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_10_0 : block g191 10 0 1=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
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
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_8_1 : block g383 8 23 2=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_8 : block g383 8 0 25 = true := (@block_merge g383 8 0 23 2 s383_8_0 s383_8_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_0 : block g383 9 0 9=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_1 : block g383 9 9 75=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_2 : block g383 9 84 7=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_9 : block g383 9 0 91 = true := (@block_merge g383 9 0 84 7 (@block_merge g383 9 0 9 75 s383_9_0 s383_9_1) s383_9_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_0 : block g383 10 0 5=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_1 : block g383 10 5 16=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_2 : block g383 10 21 20=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_10 : block g383 10 0 41 = true := (@block_merge g383 10 0 21 20 (@block_merge g383 10 0 5 16 s383_10_0 s383_10_1) s383_10_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_11_0 : block g383 11 0 1=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_11_1 : block g383 11 1 5=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_11 : block g383 11 0 6 = true := (@block_merge g383 11 0 1 5 s383_11_0 s383_11_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_12_0 : block g383 12 0 1=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
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
def deadsamples : Array (Bits × Bits) := [(0xf854605d026923a5a16008862c9d18d42fd85e54d221898f1e440284a107a02910c3e03c06c40d2642ca74f54627022c11e389d9b43b30c961ca72386ce81500aa210d1ba1a121108a6c99348979d054ac200727ac054c0970110780155ad581,0x6844620d0040231585204884208800c4270824141201090814040082a10700282003e02402c4084602ca04a440240a1091218919100a2084314a220840a00480aa210819a02120100a4409048968c05484200702a805440920100380144a9480),(0x80b20c31f72bfc4e1481d27000d43c9c5bd438a9c5e0286040f054f111d001ce10920229bde170b8d339029e2bcac4cd494fb74d1052452141a61c5b9ca1e642f40c600258428f0e5c00df481e03202a204cd465e10fe01206e82c7b03150603,0x80100c30e6089040109182600012282018c41889c5e0204002b0604000c009861080028b1c2120a0d12000120908c00d005a724402504200402010501c01c208540860025840090e1400964816012008204cd0254102a00206a0247b01150201),(0x12ce100c308544478a85796a2341d206e4242e31335abb35943abb40be28c8e05c4c115123137950052a02a9ba0d31c096458c656cc338623e92230683d8962194d5145c2aa62229438824d8e06246d0cd124850733918c390189888a426380a,0x10ca0000108540870900790a0240900460282200221a991490081a0028289000cc41010021184410080a0a28a20020c0200184206c0128621092200a03d8103080d5145c02a2022143880090804206d04d100840322918c190088800a4221002),(0x8628ebbd17000228c83c0291b729e17b3643984a392a815889878936d04e41b82b8e28807cc302855ead3105d9868885c748c2b0724ae81086518e259124cd4278a18b4aa01db88524c3a3435a0814469349110c18f0c24c2a8052bd88818268,0xc2206a1d05000020401c0090e509051303449848110100480001811490070429238c000818c508010485900541c68805c240409012420000024186258024450270208b02a00da0842041a3414a08100690490104085040042a8052bc00818028),(0xbc8ccda8781e4d8151cd3cf93a4a0a01509a42078c1bc4a783ea4aec6c7bbbd02ef85be130b1750bcd872a062d01842a34826040203d5b99ac8899721d47b82106b4f88001d04ee6f42e103eb14e0a090b95e84905a08ef7a2230402e2b14bc5,0x148981a0109a5c8210c1a4690a42220050930202c418c4a7837a48680e50b9d00c601bc02020f518c9002a002c1124282402304220255b598c9019921c51b8010494708001d04e62d42a103a30060a090b94e84905a08af280230402e2304b45),(0xd3b19712becef4647857054f8773c68492608a46265cd6cd0106c449284294958830b40e8328a4102841c46a63b66493288c7290c714876750b08cb0eb0a532e014ce7e24f9c08720240400006971f885be46b00080a21145aa7f52cf42a8012,0x92218c003e8654007015040a0c73c50280c0084821449285810a8400004080918c301008002824100801c000230200c0688c40804110046300b00cb28307502a0004c5624f9c086200004000021315805bc46800000a00145205f42ce0200002),(0x3145d24845746a93b60987114c89950ee90ab5809889781e716b0d141d9e036fea797f20c896480c8b565809c5575a81eabcad03980701be24b7e8d7401960b32336416db2f0c4c050f169960250e8b311988b92828b0074bd455ad232c2112c,0x2307720c00346283a400011d4c09950fa108a4001a095004514a0014181e2261ab3d3060c0d6480a2ac41009e4571880ea848181d90321bc24d38a860208103323340169a2b084c040f169960050c8b211800b9082890074b8455a803282012c),(0x49615339cc24bb41a658244591d020101222d0f578b5376254a121290a30cd5c4e2ad1d6dabfa9e032f022500c91031b32331a7a9ace0ca4e96243014a4009cd0d2a3210b66014de852533c420acc80ff443ad9cc5d0f4808cd621151170ac54,0x4900539a4030aa408668006591882010120251355ca1242200a1212102144d6e020a42d6d2878b6832b420400cb9813312321a4a924e408ce04943054c0001c10d2a2200b040149c8425334420acc80fa003859cc5d0e4000cd201111150ac54),(0x2108654280dbc21c532263cad6a2ab60a053058994f658a43b3dd89384745a04932387065124c385d01899e2cc083e3c1e3327061d61ca921a4965c8583262f4485320b5c04953298d1f02098424a39520b6148b236021a80528c3236c545ab4,0xc0001428049001c03a04a4012802a200013019184320c200a34088304a0580410028702010083a440180cc2080827381411260a0400ca0098085048489022c408432094004053098d0e0008842422012032140b21202188052801030c545a90)].toArray
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
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead8 : block dead 8 0 2=true := sdead8_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead9_0 : block dead 9 0 12=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead9_12 : block dead 9 12 13=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead9 : block dead 9 0 25=true := (@block_merge dead 9 0 12 13 sdead9_0 sdead9_12)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_0 : block dead 10 0 6=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_6 : block dead 10 6 36=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_42 : block dead 10 42 36=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_78 : block dead 10 78 35=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_113 : block dead 10 113 36=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_149 : block dead 10 149 7=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead10 : block dead 10 0 156=true := (@block_merge dead 10 0 149 7 (@block_merge dead 10 0 113 36 (@block_merge dead 10 0 78 35 (@block_merge dead 10 0 42 36 (@block_merge dead 10 0 6 36 sdead10_0 sdead10_6) sdead10_42) sdead10_78) sdead10_113) sdead10_149)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_0 : block dead 11 0 4=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_4 : block dead 11 4 36=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_40 : block dead 11 40 15=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_55 : block dead 11 55 36=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_91 : block dead 11 91 36=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_127 : block dead 11 127 29=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_156 : block dead 11 156 27=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead11 : block dead 11 0 183=true := (@block_merge dead 11 0 156 27 (@block_merge dead 11 0 127 29 (@block_merge dead 11 0 91 36 (@block_merge dead 11 0 55 36 (@block_merge dead 11 0 40 15 (@block_merge dead 11 0 4 36 sdead11_0 sdead11_4) sdead11_40) sdead11_55) sdead11_91) sdead11_127) sdead11_156)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead12_0 : block dead 12 0 3=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead12_3 : block dead 12 3 14=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead12_17 : block dead 12 17 15=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead12 : block dead 12 0 32=true := (@block_merge dead 12 0 17 15 (@block_merge dead 12 0 3 14 sdead12_0 sdead12_3) sdead12_17)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead13_0 : block dead 13 0 1=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead13_1 : block dead 13 1 3=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead13 : block dead 13 0 4=true := (@block_merge dead 13 0 1 3 sdead13_0 sdead13_1)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead14_0 : block dead 14 0 1=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
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

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low511 : Lower (vars 511) (graphGoal 511) 15 :=
  lower_forest (g:=dead) (i:=0) (hints:=13438558465) (before_sound known383 valid383) geomdead tablesdead (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps511 : List (Nat × List Nat) := [(511,[])]
def known511 := extendKnown known383 15 maps511
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid511 : Known known511 := extendKnown_ok (m:=511) valid383 low511 (by decide +kernel)
def x15d3 (i : Nat) : Nat := 0x7a00
def x15l3 : Packing := (1,1,1,0,0,0,0,x15d3)
def x15samples : Array (Bits × Bits) := [(0xbf91f3ebde7f2f8899fbfe080cf3efbae3ffa5dfd3e72f7062b3b1ff3dd6abf7ff75cfbd5f3bfddfe7cf1a7fbceaea2f183996ebbcd8239f45570a56f58136c1e9fe8cffc76899f5febc557574eca139f7e2d5fb4fafcf64fb9f29bcf1e23673,0xd88462b11645aa7408888a4824409780a4c4702084051fea913216f652a26ff00a6cc08d8c2b509a295476e2810980c039a840506700241f251c25602c91288868ca507d40008011ac4af8030408a8820970200002758300326775a94bedb652),(0xf6feffffee7f6b3afeffbfffefadff97df7bb9dfaffe9fe795fb48db0fffb6fbfffddfbd974cff3bf747fffadfffdfe7c2ded3e87adfdebdebdfbdfc93cd7ff797665e5ee7687fb69eef78f096bfd15dfdb3dffd5ddbcff636976bba7b63f87f,0x243b000440ba440b105320a2112e402e112008014048a00028c56008044890017002125002000224408b001154801d1ac2443b8908408240c200d001412e81120401200003907ec8028003c86902172c26019478e588344c4480024624124829),(0xe97f9d743bbdd6f7ff84d7fffbfeb0ff7fc55ebafe3ff3ffffdfffeff77d7d6f31bfbcc7e9ffe7e5dfffedb56b15b5d9ffe7ff57c777fdeabefff7effe7ed93ffeffffa7bbb7e75f6f77afafeff37effbaff7fc7fb7cf8dbddfddedfbebdcf9c,0x80002d8200022c400a04940a4c08e110e4040802e1002231012093369910ca081018408611011da08506422803a82600521006041bc109031140466209134a0010a004460218100e0029803844100c0814020801a1108000025c0104a049514),(0xd2dfdf1518dfeefe77cdaaf35f36beeef9df7fe501160db7f9cff37fcf9c9b74d1f77faefbffaddfcbd9cef2b6d245bbfb5ff37d7bbf36355a4ff7bfdbbfebffdbbb7fbf8f7c75d67308f2fffd93ff2c75ee81beebf72dddb6cb65df5bc0fe0,0x63e67d040c5e811bb648b2af48256022e108887b11ec5490af809084906232156eac588288ee2020240308841f85648a105a231d3a4167230e6a21909908434ebc00fa98131e7c091ac1016c09bee32a30b75a6c40c655793d48364b853b6ae0),(0,0),(0,0),(0,0),(0,0),(0,0)].toArray
def x15columns : List ColumnInfo := []
def x15autos : List (List Nat) := [[],[48,33]]
def x15levels : Nat → Packing
  | 3 => x15l3
  | _ => emptyPacking
def x15index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def x15 : Forest := ⟨527,3,fun j => x15samples[j]?.getD (0,0),x15columns,x15autos,x15levels,x15index⟩
set_option maxHeartbeats 0 in
theorem geomx15 : graphValid x15 (boundsBefore known511) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx15_3_0 : block x15 3 0 1=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
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
  strong_low (m:=527) (cap:=3) (hints:=8449) (nb:=1) (by decide +kernel) (plainA (q:=15) (prior:=boundsBefore known511) (before_sound known511 valid511) (by decide +kernel))
    (cut_root (prior:=boundsBefore known511) (before_sound known511 valid511) (512,5,0,10,1) (by decide +kernel) (by decide +kernel))
    (index_root (g:=x15) (i:=0) rfl (before_sound known511 valid511) geomx15 tablesx15 (by decide +kernel))
def mapsx15 : List (Nat × List Nat) := [(527,[]),(541,[50,65]),(647,[115,99,83,67]),(677,[114,33,97,82,50,65]),(793,[131,115,99,50,82,65]),(865,[130,33,113,99,82,65])]
def knownx15 := extendKnown known511 4 mapsx15
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx15 : Known knownx15 := extendKnown_ok (m:=527) valid511 lowx15 (by decide +kernel)
def x23d3 (i : Nat) : Nat := 0x7a00
def x23l3 : Packing := (1,1,1,0,0,0,0,x23d3)
def x23samples : Array (Bits × Bits) := [(0xbf91f3ebdfffbfcd99fbfe081cf3effae3ffe7ffd3e76f786ab7b7fffdd6ebf7ff77efff7fbbfddfefff1a7fbceaea3f3d39beffbdf823df55774a57fdb3b6c9e9ffadffdfff99fdffbcd77f7decafbbf7eef5fbefafff6dfbffbdfdf5fc73f3,0x980002b112012a64088008402440978004c4700084010b6a1032067242804de00040800d0401509a095476628008804029a040404500001c211404602491288040ca006540008010a40af803040008800940200002318200022741a04ac49252),(0xf2fe9f7eafffd377fe87b7fffbacb4d75f635abbaffedfef9dff4ecbc77f766bb3ffbcc7b1cce723df77efb0df97dff5e7cefbdc6b77dcfcbafff5ed9a7ed97f96677f06bfbf7fbe9feffafa8fb7dedfb8bf7fe5f958fdfb34f7dffb3e63fc9f,0x449d600044e4c410001b8208110a000cb02000204004b4808145708c142aa2101a2e42d08a2a02046088009141011990d20c18902200a443c408f1014826801828015018008002c1084002806008b40606308410a54c210470c0340d21292889),(0xe97f9d743a3d46b2ff84d7ffebfeb0bf7fc51c9afe3fb3f7f7dbf9ef377d3d6f31bd9c85c97fe7e5d7cfedb56b15b5c9dae7d743c657fdaaaedfb7eef64c5937fefedea7a320e7576e772da5e6f3707dbaf35fc75b7cc8d2dd9d4a9ebaa38f1c,0x282202dc201a22cf10e069e2a4e4ce330f4048812e5802233892093369d11ca1e1019408611011fa0853642294ba866a0561236949fc129033140466219935a2050a20446331fd08e282994b8d4303e8a14130e85a911c480425c2524e16d714),(0,0),(0xd2dfdf1518dfeefe77cdaaf35f36beeef9df7fe501160db7f9cff37fcf9c9b74d1f77faefbffaddfcbd9cef2b6d245bbfb5ff37d7bbf36355a4ff7bfdbbfebffdbbb7fbf8f7c75d67308f2fffd93ff2c75ee81beebf72dddb6cb65df5bc0fe0,0x63e67d040c5e811bb648b2af48256022e108887b11ec5490af809084906232156eac588288ee2020240308841f85648a105a231d3a4167230e6a21909908434ebc00fa98131e7c091ac1016c09bee32a30b75a6c40c655793d48364b853b6da0),(0,0),(0,0),(0,0),(0,0)].toArray
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
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
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
def mapsx23 : List (Nat × List Nat) := [(535,[]),(539,[50,65]),(551,[84]),(569,[65,33,82,49]),(611,[66,100,82,50]),(675,[114,33,97,82,50,65]),(689,[114,33,97,82,49]),(817,[130,114,33,97,82,49])]
def knownx23 := extendKnown knownx15 4 mapsx23
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx23 : Known knownx23 := extendKnown_ok (m:=535) validx15 lowx23 (by decide +kernel)
def x31d6 (i : Nat) : Nat := 0x10c840aa02d0fe00fa00
def x31l6 : Packing := (2,1,3,0,0,4,0,x31d6)
def x31h6 (i : Nat) : Nat := 0x30c0021c100000000000180
def x31d5 (i : Nat) : Nat := 0xa3e423007a88a00
def x31l5 : Packing := (2,2,3,0,0,3,0,x31d5)
def x31samples : Array (Bits × Bits) := [(0x4f2899a86b639ff137f9e6807adff6bcf6df6de144a4ea1b1e7ceebef4966b7e2fff83e3ed1e935fe7f2fdebb97ff9d9f71668ffb5a372fdd3d563fde6b77b5277bdfc63a91c5c545bdd9c16ee8664ca1572b256f9498799c6e708977a017273,0x4040c825c8a83006d0136031115960825130504906882b86080b200065a82013901a040043016040400860c02402c80c8343b800ca301c20200540812004c6018f0800838a0040900002c25409b2722c12401005a01068a040109a2f2a12412),(0xc7bee778cce7cdeff624fcfdbf766b5f7878f5dffdff6f66dd42a40767f61647ae35ce5279faf8d6ed5ffeff3e859ca48c83dee978eeebeb6f7dd953f56c9b1a5e0afbeebfaf60ddff5be28eacd0cbaeedacfbbf393d7396b3788288aa46ce7f,0x6248900d031474260064803804880042580ca8a162843106070040f6818024a0c272118ba84ee1332380515090b9c250070244481108c00871e20901c8c08008e00469018140e040412110c0226000cd04806065a162d1402170e2540c44c869),(0xb8c3dff9b7a19cbfd8e79b7df7afbde36386f21cb75d33bfe39a474b9b7cc58bd60b148cb6fdd6b5bbed937de2a7c2346bfedfab9ffcf75fcd6c2736b9dfc7b6298f2bcb06e3b7979beaffb3de78abe5e68c94efbfb2e8ea6c105209d5a78d9c,0x110609602001808010000c424a76c898a1d013400d320419b0262109327d5a0d100d02340391084888632a040600150320041200a81416b48810e6f202020220008900a860a710950000c8044d98981010319d9810000018c28a1d0943230714),(0xfef7fdf77addf8aa9ccbada65d3d3f918beff6578f7adcf1ffa9936dfcbfd9c8f70bfddf9a81beedd733c7f67fa79622f87977924f717dab3e8bfe309aa137bfef7f3b1ff6449fee2c35a37f7f3d3a13defd4db9b6bf9f6edf0df5e055f809a0,0xa468b0051c841b360c8402a4910105610c06048812418880021948a4008080600042a040000412152510108a085440280c01280402004101060a080518014d0a1a3460479440ab400cd20081b205040f850420444b3048401815c0e6b89088a0),(0xe73f631ef51c6256dddcf24bb7bb983fdd2d9aff89ba9efbbd7dfbf5184b7ff30dc769b1c6762d5957fe27888ddb657bfb8df71ff8311d35b2c2b98edb5e6ef9effeb4ff54bf0be86f8c7c69d5b7dcf6ffdb59db7fcf5fb59f8fad77015f7000,0x1111407880014040020201082c8a288252405210641075048804004960013586c0080b31384b80a81a46214140a31246238a0072a05c8a3060008122a540b28061080f30401800304024c05a0900d8c01ad912b224ce0125e2ea3619054e5240),(0,0),(0,0),(0,0),(0,0)].toArray
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
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx31_6_1 : block x31 6 1 1=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx31_6 : block x31 6 0 2=true := (@block_merge x31 6 0 1 1 sx31_6_0 sx31_6_1)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx31_5_0 : block x31 5 0 2=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
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
def x187samples : Array (Bits × Bits) := [(0x11f7fb766ddfd7a3f1dfbbf677fafc8e77fb74bdcb8ffbffd7f5b2eb78f63ab57fdc7edd59c9777f763720d475a743ebe66eeecd767afbdfd53ee5b7681dedd3b7f77ddc0eba3b3bffd1cd7d9e3efe9f76bf8bca7feed21317fc38427f0ef27f,0x10224060004344200140025504000200409004522820a0420010030d010240170008610008940008000828081544000040702022c0a008801820aa01620541028a42a0080040024000605000c1043080020c200847440040525028402a00222a),(0xc01f0ffc9ad51faa0d91a3ba8d6bedaad31c8ddccdbda0aff482ff428db889edf945de3a73c6658892444b19e1712585bc63b2d635be99bfcf79022ef45bbfc487f0efa8524e22b2d7e887c8549089c75d70119af1a5e001081f018e4fcb4c4f,0xa355820a578cab004ebc452880d0cdb72f4c518d419449214f83a4100e08b1e0c6f0187c9721e3735f8357246a8beec3950d8e991414b520a110144800523664203c1575df371c03059a2f1308ab8b2649810732189076bfadaf518e45cb4c45),(0,0),(0x42f5bd2d7374f3b8f6b85e608b1a16748d973bf176f0bf19bd08c6b8c725fa58943385663746ced95fe1defe71bcf55d719b62f77a815405cad8efe7b5a2596878de4c7fabaf97efb2dfc8e2578783cffcf6d7bd95dfa820e8406e0d8cf38f8c,0x21af12023b4875b030149a5e430ac003b0090acac74a5282dc18801b8083496104c58f6062ab5011835e8129160d5b6203f078e05d13102559d8a1358241d6bc87d2abc462c2d94a4068ca3b50005322100584527954ec775ed46e090ca38b0c),(0x1fefd99d031ce12cbeecfec8ae8e53f3aa673ee0adfa77e7aebf5623bf1397ff85a3dbafba7faaf3fdccc77842feb6c93ff735231e71b7cb3bd493d696ee5b3d8d9e3f7fdb9dc9d5ed3d26f71fbe99ddd4e2f755cf3b7920e7c3d00df0fc0ff0,0xc108c840400020bc822640008d430340962e1240005013400e614804428b280b000100f800002e65c21440668122019800c020522000048a00314020412080010014013142124911d0621000239084c6402180180221388a12b9006d05c04d0),(0xeef8aeaff6ea19dd7ab2f34fdc153bbfd7bef1fbb3979b3c8177cbfef2dce79f171c23d3b6f37edd933f398fde5ad9777a49f9bcc196d1e134abfe4d1f63625775b99e7af67e5689d4727fabf45367b2ffddea65e04817de1823aff000fff000,0x48321a32a43b5f90117c00a1e404180b04110403010004b12838200414100888200c094022903406900617c89900320a000804014244612183504e88000824243c0480a0a7118f610420080a08492ec160022028091286218ec52000ffd000),(0,0),(0xfd5dbd83baf649df199ed64da075b1ab6c9db59e5b9c4dbbc21f4b9e0c4c55cef1f7cb66aefc7c66865a1b63ba795c7fee4011ff839f746af257db3807f6e7bcc75ccf91f3e354f14977365ee77dc9737944f82a159b25cc08438ffdff010000,0x6280c1e04d0b80000e8a0104500949c130d222e078d606d04e06c146c169a5c4345352c602890dcbc125480013466ec8d4f87421f218b810545429011185905853831b000f40064004b011e4210730c13a08e41155e28579de711adfff000000),(0,0)].toArray
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
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx187_6_1 : block x187 6 1 1=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx187_6 : block x187 6 0 2=true := (@block_merge x187 6 0 1 1 sx187_6_0 sx187_6_1)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx187_5_0 : block x187 5 0 1=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
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
def mapsx187 : List (Nat × List Nat) := [(699,[]),(755,[99,65])]
def knownx187 := extendKnown knownx47 7 mapsx187
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx187 : Known knownx187 := extendKnown_ok (m:=699) validx47 lowx187 (by decide +kernel)
def x189d7 (i : Nat) : Nat := 0x2206c0ac3fc01fa00
def x189l7 : Packing := (2,1,2,0,0,4,0,x189d7)
def x189h7 (i : Nat) : Nat := 0x2040008a00409409003
def x189d6 (i : Nat) : Nat := 0xa50fc84600f68ce00fa88a00
def x189l6 : Packing := (3,2,2,0,0,4,0,x189d6)
def x189samples : Array (Bits × Bits) := [(0xf90d27f9f9e72fe2ed8ee0ffb89953ffb73caa566d6b5fddda0b913afabea42f7f48bf75b8e3ffbbf07938876f7604d8aa5b70f2ebdfaa6f9fa6eae3eea49c6f7efe67acf77439baf7aaa965b5effc3fcf2fc42479bc26640360001bd833f4fc,0x186c21206c80864100034043a1180051d0018895000041618a200100a3104f0051221d844135163c1e115100c4036804a0157a10c48198a00060840204b63201c802e20402540089015e818508324900320889f1120286620ee911091802a4ac),(0,0),(0xb2c3ef63f5acebee4f5b7b28378f15536f71136f0ab6efff48272bdf756acb82289f174b37fedb251fbdc6daadd8f8d4f3a8ebef19da635e1c97a1761ba765dd79b2a641b394df25d5450d83a1f9a3dbd7f29b6f2ffac713803f23042f2cc8c7,0x8ea5d541830020c6446000900e00660a0030108bea081213810088a200240912100f120080c0008011690450434cd204108380e3121180ac4cc58a4820b32912820000204805226314a50401820c461794031008623402450c270b261528c8c2),(0xa12945bee63afa2f17b35e24376dfb3a94c967f692b4f4a2cdf9bdefb434525ac09b828b70aa046e2756b58ed4baee2317f7b92e546ed4c8f5e9805753c22b1b8774227cbcc2cde4faef57ea1711c382477246bce3f79e28961d9c0021cf0f07,0x140202664171e29a00a0843611a1001210861701486c4641410561013406680c0a024402b032e48ac92c8028cb00048e25806044da0500112005513960482455c276e148002108ccb0862682823192809b848b41803ec2ad2c8340860870605),(0x987686c5a9e7518d50df06dda399d9fef529cedaee0f206b0dd1cb990ef55d52e4f3cda16b2b35e9cb5fa8accb7f3fabcc1fa8d38d0e4dd6f7fe7bb7f11cc826ffe3c4f6a83faa55cbaafe5d73ead774130ae8c8f7a191093600d81fd1f00ff0,0x209300411100001417c4320010404c80063216084b10300001c5204d04a8102c005180138408400040440414314087011c2081a10208070a2c052a8c280044a20288000229284f521080181092cc0692c005320a01b411952116c83681700950),(0x751eb73b5fde14fce83aca8afcebf705fbc6f8ff3d6ad7d4f75b74edf35d6c7dbb74f3dea0fc4b7b7929b123f679c15caf4b5e92f3fdf8f7fd19f6c8dcfab673004f9bff47e97dff7e37747a6e678f45fa05751e0cbda8e569c046e001fff008,0x6083cac0820008122f3406301ac0198c0aa0640049c8b48a0000e602006e0005224c001008c281c221620046000c121210ca84e2023040102d8d1b91704008da034100500c8900602c80005a318000930d84600c40346805d0066aa241fd5000),(0,0),(0x86f6bd23eef66fbeffe1f175c363272fddf39bcdd9ac1b2879744e2ff5fbcfc7cc7df8e7bf7fa9fd9edf4ffe5f37ff644f65c6798faf1fd6b77bdf98467d5fc012c3fe6f8c3dca4dc93966d1dbc2295cb5d73fff2e7a5dbb6aa267e5ae000008,0x104000063cbc97019088000561340071f50e8b701421016436f9100c1581428084b02dac12114400c6949308a89204a00c002a1464443000821264040704d02178006189205259980048e8240c303128600088f1194815ba23d89459aa000008),(0,0)].toArray
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
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx189_7_1 : block x189 7 1 1=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx189_7 : block x189 7 0 2=true := (@block_merge x189 7 0 1 1 sx189_7_0 sx189_7_1)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx189_6_0 : block x189 6 0 3=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
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
def x215d6 (i : Nat) : Nat := 0x3fa00
def x215l6 : Packing := (1,1,1,0,0,0,0,x215d6)
def x215samples : Array (Bits × Bits) := [(0x3253faed67db3fa645dfb5a672c7674c6387eec19d7b76ee6d16adeddbc7257bb8fb46f6fb913ce7950f1fbb47ed4a273ffa7ce26fdb33bc873b99f29f6d79be57b3de8bf02e6a6afefe21f9bb656ece5c76f5aab42ece00e07c6483b3674bf3,0x258eda4002a404a308000c00852c6864524140a40228461a8244802e6050d20410690130055054100b920014800010054540194012411490c408824d70fb4811000c24040080a001920843c4461844521c4c00ba0400c1168024668932454a52),(0x9dc67f7e9fe74e7dbbdf5fffb6b99dbb7bfb49ddfa95dea79ff7db9ff6dfdc65efedeb1977ffef7f8ea34e677bbfff1cf2bf3f7e5dd67c9fffa77dddff631f56ee9fddbdafdddf113b22ff8daef27b6fd4ab5f47ecbdb8531b7c9afa4399f49f,0x800100000d1002481000730008410082012010020482010014000400842000202b004200000020002009090028e348708009421020004002080240800404a04412a040a031600800012520001904320183800a00029100204b10881241102089),(0xe6ad37dbe9acbccb573e284b5bad7be69d71ffb76e119f5b92dd5c3429649a8576f4bdfee476917bf778f6cee81ecff9e38aec5fd03fed7f6d4cb2d161b59afb16deb7f777b9f1edfbd5b75efbedd73137b90ad82fd671ac06831f5c7ce18f1c,0x6480ef60e061bca407a400691202920d0e102245213008120904b00300091a11c04424603cb1081ad8122246040814801206004b531128690424814908a141226147a2168285c010a050924c80080080500831546400284e248e404828e18f14),(0,0),(0x63dd2d37d55f59b1c16a7e5044f75c54be4664b596ebe4d6eb327fb0a03275e648f75abbbad8eb391fd79d677e660573e6923c237a7079d28d4b62a1b3d7cfdb5b9030bc8722dc76dad83fbabc5beab8a56f5e4d2169e00f083e81780fe07e0,0x180004179048c81891b9606c32d18698008e874801c42925081365410102245b011084cdb80e8a4cf02c402303f8e54a88000091e0866a0608a71c30070494aea8c259a23a5c566604723418a807300582a1e14521c22ee97adb985680ba05a0),(0,0),(0xedd02338f561e695b828777faf7ce3f3672f367902ef85f5e529cf3e2e3847a76de6ddb3265a731cacb5a2aaf493f3688125a3826951fc8a3ec6c4aeeb723cf5ec7cad13a8e4df56a8264f25fdbbc4cbc090296d582942531d03a5a000fff800,0x6f5876bf3026f80143c88832568c6348860a0029fa5d70408879639178c0389e844721ee8f628c2f9536d4f51410100a66a4a8c24326a09d10003048687a0b014d4e2b1eca084210141292ddc2c00c62705625a9b56ee7dfb46f77e800efd800),(0x75ec93be333dac9b40eb6356d93b6b3cb7389b77843e973c1898ab9de3ef96cd5df8f8cd0cb436c774f2b8ffdc8023ff073ee8d5e4afb6700fedcf798eb99f23e7c6a9e292ee6cbdcefb92e6f289f0542b364d9abf61cbac1583a5b7ff000800,0x9a1700001d140208a012938261a445c0f1ac0da09c0d828d82d34b8868a6a58c05121b97824a9000268cdd91a9f0e843e4317020a8a85202230b20b0a70636001e800c80096023c8420e61827411c822abc50c009ab497b1db71b7b7d7000000),(0,0)].toArray
def x215columns : List ColumnInfo := [(512,0,215,0,7)]
def x215autos : List (List Nat) := [[],[32,116]]
def x215levels : Nat → Packing
  | 6 => x215l6
  | _ => emptyPacking
def x215index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def x215 : Forest := ⟨727,6,fun j => x215samples[j]?.getD (0,0),x215columns,x215autos,x215levels,x215index⟩
set_option maxHeartbeats 0 in
theorem geomx215 : graphValid x215 (boundsBefore knownx189) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx215_6_0 : block x215 6 0 1=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx215_6 : block x215 6 0 1=true := sx215_6_0
theorem tablesx215 : checkedTables x215 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block x215 0 0 0 = true)
  · exact (rfl : block x215 1 0 0 = true)
  · exact (rfl : block x215 2 0 0 = true)
  · exact (rfl : block x215 3 0 0 = true)
  · exact (rfl : block x215 4 0 0 = true)
  · exact (rfl : block x215 5 0 0 = true)
  · exact allx215_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx215 : Lower (varsX 727) (graphGoal 727) 7 :=
  strong_low (m:=727) (cap:=6) (hints:=553648385) (nb:=1) (by decide +kernel) (plainA (q:=215) (prior:=boundsBefore knownx189) (before_sound knownx189 validx189) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx189) (before_sound knownx189 validx189) (513,16,198,0,4) (by decide +kernel) (by decide +kernel))
    (index_root (g:=x215) (i:=0) rfl (before_sound knownx189 validx189) geomx215 tablesx215 (by decide +kernel))
def mapsx215 : List (Nat × List Nat) := [(727,[]),(949,[134,81,114,49]),(1009,[118,33,129,82,49])]
def knownx215 := extendKnown knownx189 7 mapsx215
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx215 : Known knownx215 := extendKnown_ok (m:=727) validx189 lowx215 (by decide +kernel)
def x349d6 (i : Nat) : Nat := 0x3fa00
def x349l6 : Packing := (1,1,1,0,0,0,0,x349d6)
def x349samples : Array (Bits × Bits) := [(0xc3ada743e1bd77cc4f34f91cefb66973971bf7ff2f2b25d691ec756a2b28bcb83390ecfeec6e01a8e34887d6ccddcd9aece5e79faa7dcb6e401ad2a16becdab815543677ffa39af93c7db53ee96d1710ffdd8b145bcf240097880cc3a44fc4fc,0x3718570042a988178d958c27f61a3f398ad5e5009a014425090232e509db54d0547b80630f8d4e489512b6840300b18439622948c2f026f0c0812f7c53781e99844fb006021154673010164ca2030cf43421f5aaf424605e75bc2cc2ac4ac4ac),(0,0),(0x3daa3f545f630775a2d7df74a23d9b78db7b6557e985fec41f5017f9fe9bfc74c788ce330680d6234ae34b0b58c535ac6b7c307d9ff204d5d8b77f8d0ee3df84ac844564a7d10ed089255a8fb7f2273e634bcf1b8bddf88004650b0b788cf8cf,0x6e166320f061304c0624804b49a29183de1832c3b9170a08171153888c89b8a9ef4664b6b6a3b002669ff6c784fb54f3b22e324b2330586b002e61480c2403626da5ae9488452a10234be34405104aa0fa801644d4a50ff34ef72f0b708ca8ca),(0x7efbcf756f72fee5bef53ce13d6ef7e9ede67e3bf8d0cdf16f6bb4b3fcf74beeee8f9fa2bf89fcf4eb7fe8bbe32755ee7513bb2b9de197cdfb67bb5695feb9ff5f7f6bcf4dbf03c6af0f4b9ffddfafffeb3f7e7feffef827787e300c7ff0ff0f,0x808c570008ccb0018900241210021c0002800c006020320804a043010002520000804808140a5c9820002002000108080000805007200404809c0100814088804211020298d42684101418800a00040028e1112142200c310810000a605605),(0x8639e259fdd9fd914d1ca7ee56ce7d435bf5efcf5f7fac46fe266fff0b47b75f54fb54f7dbdb8fe805fd6f925ffcaa46bce36f9477b96fa70ddcb6fb7a3c7eafb72397bafa7adcee1f7d36bba1e5eeaa9ef6f524f6169c81a393e40f80ff0ff0,0x806000090440000302260c801e5c04070080ae0018c8b8882d14d086004a10d00001d94b0429000428440138018040344101031080818002b2c0000a002802628004c2038042388426a41824c14f0030844004408009fa18a43c00d40950950),(0,0),(0xedd433baf565e69fa82a777eaf7de377672f367902ef97fce5b8cf3e2e3847a74de2fcbb067e730f3cb5b2eed491b379832da3c06957fc921ec6c4aeea733ca5ece4ad12a8e4fe57c8a6ce65f7bbd4cac09029ad582943d81401dbf000fff000,0x654e76bf2022f80163ca08b017282208760208896250f2c80aa8281910449912804538780d201c2f93b2006494001009029498e24b0eb09d33081048c8780901414e271ec20861985618d35f86d0c440581221a92d4a71ce3b86baa048fff000),(0,0),(0x75ec93be333dac9b50eb6357d93b6bbcb7389b77843e973d1899ab9de3ef96cd7dfcf9cd2cb436d7f4f2b8fffc8263ff073ee8d7e4afb6782fedcf798fb99f73e7dea9e392ee6dbdeefb93e6fa89f0552b364ddabf61cbfedc09dbffb7000000,0x9a1100001d14020880109302608445c081ac05209c0d00058053438068a2248c05120387824a8000240cdd9129f0e842e4216000a0a04202000320b0270636001e800880096002400006208070010822a3c50c0092b48631c471455fb5000000)].toArray
def x349columns : List ColumnInfo := [(512,0,349,0,7)]
def x349autos : List (List Nat) := [[],[96,132]]
def x349levels : Nat → Packing
  | 6 => x349l6
  | _ => emptyPacking
def x349index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def x349 : Forest := ⟨861,6,fun j => x349samples[j]?.getD (0,0),x349columns,x349autos,x349levels,x349index⟩
set_option maxHeartbeats 0 in
theorem geomx349 : graphValid x349 (boundsBefore knownx215) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx349_6_0 : block x349 6 0 1=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
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
  strong_low (m:=861) (cap:=6) (hints:=13019128580) (nb:=4) (by decide +kernel) (plainA (q:=349) (prior:=boundsBefore knownx215) (before_sound knownx215 validx215) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx215) (before_sound knownx215 validx215) (512,1,332,16,5) (by decide +kernel) (by decide +kernel))
    (index_root (g:=x349) (i:=0) rfl (before_sound knownx215 validx215) geomx349 tablesx349 (by decide +kernel))
def mapsx349 : List (Nat × List Nat) := [(861,[]),(877,[84,131,98]),(925,[118,130])]
def knownx349 := extendKnown knownx215 7 mapsx349
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx349 : Known knownx349 := extendKnown_ok (m:=861) validx215 lowx349 (by decide +kernel)
def x455d6 (i : Nat) : Nat := 0x3fa00
def x455l6 : Packing := (1,1,1,0,0,0,0,x455d6)
def x455samples : Array (Bits × Bits) := [(0x51827bc46bab6ea649f77194ffb5757d0fcbfef9dc3b5fde0b3e05abfbef04e0b199cef675898c63b002de83c7ad490d32bfffe23cdb803d812bf9f01f6119b206d7748bb8b82a787bf421eceb692e24d4325d86fc1d9c0c253c805193c8ce93,0x40c6ace82286bcaa5bc0643093654aec544140a560b8175a8a6ca43f7010ca14912c21500870583bba88005094e04045c7c491127141f40bdc0a82053c87c11441c246baf2c0e0118238f189ccdc7013cede21122088a1fefebd84f192c8ca92),(0xb797ff579bbf55795fd7cbddc6fb17bb8bedc0d9ff45fe07eaf773dbf38b2d5ef79feb5dfdef9fbbc3ae4f5f73feedbefffd776b969e4f7fe8bd7d8a7fadfd58b5bd575dfdd39d3bbd78a79cbae43bb5bdcfff7ec9d7fc04d1ff5ca21f0b0fff,0xac0142001d3002400000130008800002032810020406000014114100842030282a4042a48402a00000174905281318320009424002000000000040c8002020401a24280409200a00010702441100020011000a00061106010142580209010449),(0xeeed37b3edecb6cff7223c696badf3e6ed63b6b366819ffb87ddd4302d304aa47e94bdfee666f11ffb79f6eee01bddf9c388e44b997fddfb7a4ea284e1f798fd5cdc3f5775b5b3edf9d7ef57ffbf957b77990ad90bfa701b0e801ffc1cf1f31c,0x10c089c8c04304acc4740059200294850894274441201857012e9012100b060141100401309900316808220211e8e4c090828009b091ca6214278131078554222081808840c58040a040200120c90080829b10544088086a589402dc14a0a314),(0,0),(0,0),(0,0),(0x63dd29b7d55fd9b1c0aa7e7144f7dc55bf42f4f517ebe4d7eb32fff0a47b75f64ef75abbbbd8ed395fd79d67fe262571e6b2bd677a727992dd4a67b1b3d7effb7bb83abca7a6dc76fad93f3ab85fcab8a76f5e4f6129be0f043e05fe0fe03e0,0x40049f804ac81051e9607c125182180002824841c0396008282451110000530000844838040a6dd020002212080508088080914006a80418a41c00000080aea042512a721c54260470141988c630050032e145214a28c2328d006940fe03a0),(0xedd02378f561e695b83c777faf7ce3f3672f76790aef85f5e529cf3e2e3847a76de6ddb3265a733cacb5a2aaf497f368a125a3826951fc8e3ec6d4aeeb723cf5ec7cad13a8e4df56a8264f2dfdfbc6cbc090296d582d401f2f02f30000fffc00,0x6f1876373024f80103888822568c6348860a0029ba5d60008851638168c0389e844721ee8f628c0e9536d4f50410100a662428c24326209d00003048687a0b014d4e2b168a084210141292dcc2000c62704425a9b566e795a76bfd20005f5c00),(0x75ec93be333dac9b40eb6356d93b6b3cb7389b77843e973c1898ab9de3ef96cd5df8f8cd0cb436c774f2b8ffdc8023ff073ee8d5e4afb6700fedcf798eb99f23e7c6a9e292ee6cbdcefb92e6f289f0542b364d9abf61cbec2502b35fff040000,0x9a1700001d140208a012938261a445c0f1ac0da09c0d828d82d34b8868a6a58c05121b97824a9000268cdd91a9f0e843e4317020a8a85202230b20b0a70636001e800c80096023c8420e61827411c822abc50c009ab4973dcd72bf96bf000000)].toArray
def x455columns : List ColumnInfo := [(512,0,455,0,7)]
def x455autos : List (List Nat) := [[],[98,135]]
def x455levels : Nat → Packing
  | 6 => x455l6
  | _ => emptyPacking
def x455index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def x455 : Forest := ⟨967,6,fun j => x455samples[j]?.getD (0,0),x455columns,x455autos,x455levels,x455index⟩
set_option maxHeartbeats 0 in
theorem geomx455 : graphValid x455 (boundsBefore knownx349) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx455_6_0 : block x455 6 0 1=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx455_6 : block x455 6 0 1=true := sx455_6_0
theorem tablesx455 : checkedTables x455 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block x455 0 0 0 = true)
  · exact (rfl : block x455 1 0 0 = true)
  · exact (rfl : block x455 2 0 0 = true)
  · exact (rfl : block x455 3 0 0 = true)
  · exact (rfl : block x455 4 0 0 = true)
  · exact (rfl : block x455 5 0 0 = true)
  · exact allx455_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx455 : Lower (varsX 967) (graphGoal 967) 7 :=
  strong_low (m:=967) (cap:=6) (hints:=26323452161) (nb:=1) (by decide +kernel) (plainA (q:=455) (prior:=boundsBefore knownx349) (before_sound knownx349 validx349) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx349) (before_sound knownx349 validx349) (513,0,454,0,5) (by decide +kernel) (by decide +kernel))
    (index_root (g:=x455) (i:=0) rfl (before_sound knownx349 validx349) geomx455 tablesx455 (by decide +kernel))
def mapsx455 : List (Nat × List Nat) := [(967,[])]
def knownx455 := extendKnown knownx349 7 mapsx455
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx455 : Known knownx455 := extendKnown_ok (m:=967) validx349 lowx455 (by decide +kernel)
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
def x191samples : Array (Bits × Bits) := [(0xba07c15f4fdf6cf95faadf1fd7e5b3316b7bf9e78a5f84755da36f78f331570e4fba890137fdb6746422f21e58f4adde98651beaffd713f934f1b23fdf74bf03ffc32eeb9896bfe4764fdaac632deb90c43838203187d246940112477e23f023,0xd48c0000003c44c084a0810c17032100020d10700c0884430050000050208100284d014438a0008291a2948120011930d800004200401041118170210000021010004200002904100041416305639040190c00220482140c20640214202012),(0x73ffab4a9ef40d638bec853881a69eaea537e3ae667704cc3323eb30e4fe3f11125fd6e1ace557832b59c88ffdd4df10b7b2fd0e24edfc4cc3a5f74e3fae2b27d7dfb24f073434d13c0f2d279ade11b285600001f5328c0001e3d215d8c4482f,0x202853918452802021320e4c00081418225902070920936298c1a802a800cc60d5d010c08a055e2b3c600c4a3419c6a4c40313c4845a990f3e264408120d4609c24eacac34080672a4062cac90da1047056401c7495b1c62e1d39335a8c6c869),(0xfd7bfde6b4b4b5aefc4fecfecd732aba3ee8eef0b7faebba267a9abe3c5ba83971dde5a95eaa22a7cde32ba373d4f6c1cbf004940cc3ccaf32f7253f702e9937a79cb8b6baffe5fdcf6a97c2c92327214a5540bbcca040316beec50881040d8c,0x88830408200121d008015002481000800004002094412000213c43410621128700002c0200182040830a11104186100000080833108160604080238208022000058100020101c000523081024920e7200a01d20886a040010c08408051010514),(0xdb31df144f2733742f5f3b4e781d140e205762cd298d44dee148be6bad5204ac7567fe6d487ff389bd6cdffbe0b9d631f6b68b7d7a885cfe01dbfaf96a9c76ac95f41e894eb36b3daa9e5fd379b1ccf871a62a44008a0386a10289e01f80bf0,0x30548b0218c4160325002818848621701003570061220388d2020028c09ca05028e280b1800092083c3002a40060617a27524208e600058c10010c64202890005070441c52020c85808128c1269f188185180466610db03cc320a72e00b08ae0),(0x9294ecfb8f3dd2b61efca2afc35763f6918d20c178f41c84dadabfa7c29c55eee3e3de9f8f0dcdb81d7834bdebd1036efc8e75e968ff22d4bd5d4ef0219ffede44dc2c88dd8cd973eeffaf739c60d24e1faa0a15003f500b101028d021fd7050,0x86017009071940801832544433481c0ce89c00ac0291d03320a882400a01042a060400060ac101b300064d4868180e840821b45008a09220244252001c030f04a008090129ed1242077602189860806e3ae6d39988724043309218d1614f5000),(0xb7302f4fdb4bba79f91b57fef62d87b7e377598d555cb84dd2cc12f945af0da64d494f73067189f1430dd2cf046bdca1e6398ef2fbd9f936db116bc9dc60d5e28babc729c9c70394e5365cf9acf0ac213f80b76056d22fc48400087e8e028600,0xd70040c1415381a21e3b5958608000c4f32440680543121080842c31a021c22e6000225eb242028c280a40000a4c00200b252b190920a0211608020a0a96f5f40c896298208610910ab380a28c708c251f02f3e8dd8a1942c00289ddca010600),(0,0),(0xd41f73c9bc9ae386f65a4aca6a3d2525ded60678ddb6ffbf3afc535792a983a7614e19f8d64efd0eae8e2cd3e7de7c0ae854b5fe873db7856b426364a42481bea0a865f1698e49aa23d433aa72df101878ad8d5b0a502f89124d052000000640,0x48192406840805e1c02020930791320401a391083448845803000000c829400d7211014d05581240318e8100116d0004c2d444c65e1e0808634045e0010008e0420c240658216225007e04328f109a60ac0c17205526bc33f5362020028040),(0,0)].toArray
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
theorem geomx191 : graphValid x191 (boundsBefore knownx455) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=2) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_10_0 : block x191 10 0 1=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_10_1 : block x191 10 1 1=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx191_10 : block x191 10 0 2=true := (@block_merge x191 10 0 1 1 sx191_10_0 sx191_10_1)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_9_0 : block x191 9 0 4=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_9_4 : block x191 9 4 27=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_9_31 : block x191 9 31 14=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx191_9 : block x191 9 0 45=true := (@block_merge x191 9 0 31 14 (@block_merge x191 9 0 4 27 sx191_9_0 sx191_9_4) sx191_9_31)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_0 : block x191 8 0 9=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_9 : block x191 8 9 36=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_45 : block x191 8 45 36=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_81 : block x191 8 81 36=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_117 : block x191 8 117 36=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_153 : block x191 8 153 19=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_172 : block x191 8 172 36=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_208 : block x191 8 208 12=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx191_8 : block x191 8 0 220=true := (@block_merge x191 8 0 208 12 (@block_merge x191 8 0 172 36 (@block_merge x191 8 0 153 19 (@block_merge x191 8 0 117 36 (@block_merge x191 8 0 81 36 (@block_merge x191 8 0 45 36 (@block_merge x191 8 0 9 36 sx191_8_0 sx191_8_9) sx191_8_45) sx191_8_81) sx191_8_117) sx191_8_153) sx191_8_172) sx191_8_208)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_7_0 : block x191 7 0 25=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_7_25 : block x191 7 25 22=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx191_7 : block x191 7 0 47=true := (@block_merge x191 7 0 25 22 sx191_7_0 sx191_7_25)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_6_0 : block x191 6 0 2=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
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
  strong_low (m:=703) (cap:=10) (hints:=536879361) (nb:=1) (by decide +kernel) (plainA (q:=191) (prior:=boundsBefore knownx455) (before_sound knownx455 validx455) (by decide +kernel))
    (index_root (g:=x191) (i:=1) rfl (before_sound knownx455 validx455) geomx191 tablesx191 (by decide +kernel))
    (index_root (g:=x191) (i:=0) rfl (before_sound knownx455 validx455) geomx191 tablesx191 (by decide +kernel))
def mapsx191 : List (Nat × List Nat) := [(703,[]),(831,[135,50,65]),(891,[130,50,81,115,98,65])]
def knownx191 := extendKnown knownx455 11 mapsx191
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx191 : Known knownx191 := extendKnown_ok (m:=703) validx455 lowx191 (by decide +kernel)
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
def x351samples : Array (Bits × Bits) := [(0xf1405419e53b37c1a894fcbc1efffeb7bd53e8398d5ed3ad216467c7af76bc05fe54e2f39df53ada7a917a78adaf781e9fa252df8b386939ff32fc9fdee774efbdbb1cdcb3bad3dff6c77536d060b50cce9c0517214644802008037b2821fc3b,0x10186c8a0003408822003510029010012a31544288021419e8722040019008e130612deb066324058262838128132044100224754422ad044d10d404e868a105a9124f65d02005b0891d349020950cce0c4096120641ace25ac94a2821263a),(0x60684bd3fdbc7429906c83de8bbf4bc1bf8c4695ffecff6a94d3fc9a851d39cce2e87757697f8a75bdfbbd77e57ddcff9ac7e9ffb86aff8df2b6bbcc7bcfab39df67afeac1c3c7e53fd1d24f6003463f032d55686431080404d7869bbe02401f,0x108c2825404000d00110000448842258880800334004501240400180080008102010840001014023020806854032c02306041920228c1008020e00022000100100004100a08d8000420424b4101403200a0b468c8910c400081220144004801),(0x2c9337c7e540d5b5c5daff3dda7a9a5e988319776abb9fe569bcb5206fd6af5971bf01f0b39deeeee6ccafab0ab8779ad4576f4a5bffde6962e6f285b5385e074eff302ccdf5ecf953b26531a455106ab5069859040d30cacc17848431038594,0xbe0000340a08b060a9cecd00133401803248231cc02490840ab8bfc1580a87044c960715444ca881851001020b44800dc4100c45695020101bc202031142600bc239400ed18704692813a430b074108db30648952766b3af5d149c9631438714),(0x6b6db5b70bffcedfdcabf7bed6f6f03ef3235dc6473b0e5dcd360f31daca66248115dd8c5fbb7797633ea20ed27bd126013f95b9e6dd1746571b0bcefb667ba0c6cfd7e0ec337fc69512a39a1d1ad542943baa105a0881fad9a86904417805c8,0x4050ca8840800a06001000540800400000000000020802339102400c82011840a300a0020900072002220a818039100220884200900292270000708004298480010007112e50008400080b820582c6320428820210884400824a4109403000c8),(0xb6d4b423cb9b4fdfda1b38b13eecff53cffb362e2a4522ff9eb0bc773829dbc37b167b69e65c0a2c55a257914f977d1b46324ee0f7201a37fd8df9795fc3476c85fa8e9eb063b6b2795c10c9e87d60c0789200475f56441001001d60c1fff800,0xb5ac24132425f0a113852780a3dc2c226655482a9131f5880614841334c243870c43048010f088c8e84514786c04e8019844b08302a10950d3b20f09a004015a9050a0001023865a47402049685520c131d21869ed708253150036b081ced800),(0,0),(0x3ddeacaf374ac7033721c1d5b791f113233e962ddce93163f3cbb6281f076792d422890e28c499b7a44f07e5eafffb6dfeba8e965580d79f135004a281d382936c70cd477afcaaea8ced7df00ac69a91206a41a284bc3a0522401164be840260,0x6c2025088998553042a883340831811003362b0c8818a01252e33280c4085832fd90260604c80310c2047b048098009183020c01510200313c0e100c050d8e10812821882000239c600d19b00cc68e81100a0106170c6306d242c5febac00260),(0,0),(0x87be8ccc0cac83e923542157b5079cfbf1e48685a772e4896e8a1af8b4ed6d364e0eb6e754b3319009a141969651876dfbabfd6771bfe695f84b04f7559cffa2a2c363a3925f312bbffebe2cf3bcb9c4e0c526d18090bb313aad700000840260,0x30f0013320620489c057009a0c20885ec48c4d155660c080c000c202894a60c000050b1b22198800d5004601644c7681004b15602f1254042600b21a050316050d39066512a98419042040cf239314c6ac56cf9a87298f92db53a0000040800)].toArray
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
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx351_10_1 : block x351 10 1 1=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx351_10 : block x351 10 0 2=true := (@block_merge x351 10 0 1 1 sx351_10_0 sx351_10_1)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx351_9_0 : block x351 9 0 6=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx351_9_6 : block x351 9 6 31=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx351_9_37 : block x351 9 37 12=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx351_9 : block x351 9 0 49=true := (@block_merge x351 9 0 37 12 (@block_merge x351 9 0 6 31 sx351_9_0 sx351_9_6) sx351_9_37)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx351_8_0 : block x351 8 0 12=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx351_8_12 : block x351 8 12 36=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx351_8_48 : block x351 8 48 36=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx351_8_84 : block x351 8 84 36=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx351_8_120 : block x351 8 120 36=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx351_8_156 : block x351 8 156 36=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx351_8_192 : block x351 8 192 36=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx351_8_228 : block x351 8 228 36=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx351_8_264 : block x351 8 264 10=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx351_8_274 : block x351 8 274 36=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx351_8_310 : block x351 8 310 1=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx351_8 : block x351 8 0 311=true := (@block_merge x351 8 0 310 1 (@block_merge x351 8 0 274 36 (@block_merge x351 8 0 264 10 (@block_merge x351 8 0 228 36 (@block_merge x351 8 0 192 36 (@block_merge x351 8 0 156 36 (@block_merge x351 8 0 120 36 (@block_merge x351 8 0 84 36 (@block_merge x351 8 0 48 36 (@block_merge x351 8 0 12 36 sx351_8_0 sx351_8_12) sx351_8_48) sx351_8_84) sx351_8_120) sx351_8_156) sx351_8_192) sx351_8_228) sx351_8_264) sx351_8_274) sx351_8_310)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx351_7_0 : block x351 7 0 36=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx351_7_36 : block x351 7 36 12=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx351_7_48 : block x351 7 48 24=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx351_7 : block x351 7 0 72=true := (@block_merge x351 7 0 48 24 (@block_merge x351 7 0 36 12 sx351_7_0 sx351_7_36) sx351_7_48)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx351_6_0 : block x351 6 0 1=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
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
def mapsx351 : List (Nat × List Nat) := [(863,[]),(879,[84,131,98]),(943,[98,118,81,130,50,65]),(957,[118,130,81])]
def knownx351 := extendKnown knownx191 11 mapsx351
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx351 : Known knownx351 := extendKnown_ok (m:=863) validx191 lowx351 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx471 : Lower (varsX 983) (graphGoal 983) 8 :=
  strong_low (m:=983) (cap:=7) (hints:=26323452161) (nb:=1) (by decide +kernel) (plainA (q:=471) (prior:=boundsBefore knownx351) (before_sound knownx351 validx351) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx351) (before_sound knownx351 validx351) (256,0,727,0,7) (by decide +kernel) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx351) (before_sound knownx351 validx351) (256,0,727,0,7) (by decide +kernel) (by decide +kernel))
def mapsx471 : List (Nat × List Nat) := [(1013,[134,81,114,49])]
def knownx471 := extendKnown knownx351 8 mapsx471
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx471 : Known knownx471 := extendKnown_ok (m:=983) validx351 lowx471 (by decide +kernel)
def x487d10 (i : Nat) : Nat := 0x2040186004093a0ff803fa00
def x487l10 : Packing := (2,1,5,0,0,5,0,x487d10)
def x487h10 (i : Nat) : Nat := 0x20000000000000000000038780010cb0c00600f0a001c580061000000610f5062441800219b0930b1400000000231824000005c171d39e150000003327570d2ababc23800001298000000000039a613000000000c8001dbc00000743b36b2800fa2912a2b81405fc7824a5c4f254a480049400303800000da388c4f000d4a85000c00105000b002007000033c3001
def x487d9 (i : Nat) : Nat := 0x2c2050004102103a460914142020301012102820601858a0a101018071210441030011c3800d082053420004292184800010130008284260800850010410002024080010120404000921018030800101204000809020202008121418048008084240840470c004810a09b10b4ea49ba38825e86e5a65f96b52929420ee334ac22c6a1242f003ff19c01ff58a00ffa63007fd42803feb0c01ff0c600ffa43007f931803fc39c017f1ce00ff063007f921803fca1401fe48200fdc45007f962803fca8c01fe44200fbc67007fa33803f511401f68ce00
def x487l9 : Packing := (22,2,5,0,0,10,0,x487d9)
def x487h9 (i : Nat) : Nat := 0x28432982a385a000104200000000000006d800025adfcf020000507c96c22452718ab8b400000039a40004a1520211fa5a000000501741a4230adf9898bb36300ec68289000070f49c800103de00ba64dc9dca20978e7ca1a44ee12a59173d8b21f5369415e1ba170000d369ccba53560b38c5f32918eba55e4d88b793f55d74431a0274ea5b935191a28000273b554f9895ec06a25dd670a6dad830d8239251db82a782e4c7203903986264e22d7a4d2c743800032df192d9e628136a097034c75db3b205527a37a1c3932602055243250c4e82024cf4794e1b660617ba375de8430dbb03dc13833d56a0a6b756595370cc7db7a9cceb84f4009baf20760d95d04f2873c32b505155143b8538bd5191f42128eaf856c97800346a00000000019a0a17b48603180000072489bcc8200042b800000000000024e5c8503100024cdd70000000288a0cf62b11347bd427858336089e85943c0000001110016000241c00108c0003dbfca3529000545f48aa11d8e00004b9415035800107600000021c748c07096100008cce30334129803200000079ab96ea3f0000000000000000019400000004804800000c4000000003000200127000000000000a801c00012180020402810010002560401040010031c00000400000010020491010400010820080020000000420100000000000020000040000080020801c00400000000011810000400000000000400000000c3000001000006000000080040000080080000040000000080000042000040080002041040001000002080000000000000
def x487d8 (i : Nat) : Nat := 0x8005002180820c040b184800a04184001040b1000488041c4821e20b00101008825080860210e081041014412002400830c0040000000001001040860420400a206042810214304086042821040850030210c0b108009282043020220c400b1820430218008204000000900400b09810520100890000416121a14805020110204045021000008800400a040850c302c25008821020041c244041e0e34101140841420810a0808a04280104000080a040468218101120040a0440400801021000000840200141a4028101002000002140890a044821410e1c0200f68ec4d6fa8b42e70cb793b1ce24c1f7eaf2dd0b6769accd8caef58aaad50a774da98d2ca4f48a8ed18a2741a80cf49cf38a6acc897727a4cc8c8ff1ca36c608a711a0cc1480efc9eabd0786ed9d4b9c72ee49c6b886e6db9a4b3463ebc96ead8586ad958a9c52ea4942a684868d918a2441e7c8ee9d03866f8d899c31e608be9682964f89491c20e4087a8f01d63786c8d417e2683a8700d61983084c06e0a80e800dfc714c600bfe884c600dfc874c600dfc7348600dfc7350a00bfe8858600bfd8348600bfd8448600dfd541ce00bfd840c600bfd8350a00dfd511ce00bfe8850a00fed3250a00ff5614c600efd6158a00bfd8158a00fed4248600dfc718ce00bfe8858a00bf9800c600fd9310c600bfa884c600fd8878ce00df8874c600fd6118ce00fea224c600fea221ce00ff2118ce00f7a551ce00ff21158a00bf9811ce00fd9318ce00bf98058a00bfa8854600ff2111ce00ddc878ce00df87348200dec7388a009fc8758a00fd9108ce00dec7188a00bf98150a00bf9820c600fd9308ce00bf98050a00bf8874c600bfa8850a009fd811ce00ff21150a00ddc718ce00ef96158a009fc8758600fda3350a00bfa8858a00bf88750a00fd9311ce00bf8818ce00fd8818ce00efa6648600fd9508ce00fba4448600bf98058600fd9208ce009fc8748600fe92150a00ff1104c6009fc874c600fe93250a00df8711ce00bf98348600bf98048600fea220c600fe92048600fae4488a00f7a558ce00bf8878ce009fc8750a00df4714c600bf9851ce00eee6688a00bf9804c6009fd861ce009fc878ce00bf9821ce00efa6654600df87144200fe96088a00fda3354600ff1514c600fba4454600bf88748600f7a5544200bf88148200bf98350a00fd9328ce00bf88158a00bf88754600bf98158a00fea2244200bf88758a00fe94088a00ff2110c600bfa8848600fd9538ce00fce228ce00ef960586009fd821ce00bf88150a00fda3348600f5e558ce00fea228ce009f8874c600faa4488a00eea6688a00fca228ce00f5a558ce00fd2118ce00
def x487l8 : Packing := (118,3,5,0,0,11,0,x487d8)
def x487h8 (i : Nat) : Nat := 0x163625b608e2c24200088c000000306001c25e5360000019c0150d6000218c4daa701fa0231c000000e2f22143143d90ba55210a2a25db15622c0e8daa5940ca811a71c0e83c12001834000001247326c1c000c50c5660b005e38386448001e4501a001e1724e001040000000000000000000000c9da4ba329abc26000a3e001a3b229c0600070382015023218c10114110001
def x487d7 (i : Nat) : Nat := 0x602100000000000004200084001080000084000000000000c08418106042810a0420c0870210204204084181082081bb5a2c75eacd529f4aa2d02772d9446a2b07813f5f0ea72b81b6d668b318ec25eae1549c4ba24f66d3416898471c8d04c2109838015fa9921d318033d90e992850047fa65811ce00af64ba8490c011fd9321d428023f92ec0ac50047f64c87586009fd4c90e98c015f5951c5318023fb2243a850067ea64874c6008feca90eb0c011fe9921d318023fb30a88e70047f6448758a00cfac0aa239c01dd531544738023fb2643a43004ef65288586008feca90e98c011fc9760d218023f92ec22430047f25e884c600afa4bac298c011fc9760d428031f90eb0ac5007741c5311ce00fe11142319c011f897601318023f53243a63004fc2458050a008fc4bb0690c019e887889318027b32640a85004fa64a88546009bcca902904015d8974c6338027732840a41004f664c8148200fc519c89114013799520542803f442322445004de6548158a00f7108ccd114012f99620520802eb32a40c67004de654818ce00
def x487l7 : Packing := (47,4,5,0,0,9,0,x487d7)
def x487h7 (i : Nat) : Nat := 0x5000
def x487d6 (i : Nat) : Nat := 0x21f9a025e884c600
def x487l6 : Packing := (1,5,5,0,0,0,0,x487d6)
def x487samples : Array (Bits × Bits) := [(0x23d56768446ac8e30e3df7c1fc93be56e0fa9efe6b686a496d1af1939de97c8d1d6f6083a298a794c9956e587330d9793e3ee6363f0feea4275efd1e28ba1fb817ab5918a4f9bb47af6ce491474ac94c80504581a995d11194830c4a32c54353,0x1a684be6628b5a3a54021808981650920064526c608209545004230c1145837404839242d021d454289104d428200612dc98080d888c832df4480702224c550148299e324d180000b304c0a06642c14c0040e1a90b8716318e9edc6633574a72),(0x7e3bbb2bdcf1fe9e9ba34feb4bfb2baffdb60fc7e56bbf57bcddcfff7e39422dfe537cfa71edd95fc2d9e71d87f656db8ef7b8b9d9167e02b445b6cceef619a76f55dc056d032cf8f6f13bef20ad56c2dc70c61a2d302482001b85484399f41f,0x44019000194401042000845004400a0c03820002011140000601c000840048018800600103400009810c20081011d8440366414014002040000010c18021005c00400000100290054400300010ad1480069b0612643821821101200040802089),(0x43d4d8e33ab3340aa1f35a744eaf7cfdaf1ecdaadba4db35ebee1de9ea3025f67e8cd6944aab24ed5df1b9c3dec93f60582e58dd869fafda51ffec7fd2fd7b5f65dbb8cb7af75ab6ecb2f460a34687329d8c185b9a001008041ceb947c41871c,0x40200a001200800f9e19a009208480000163a40200021490021c6813983352114c8d02040e828028409630c42c00212008843329a61c82100500101782c8a014a900c5834c026a004f4800c740ab22996439608b400c1c0810dbb828518f14),(0,0),(0,0),(0x8b3eba746f8d6dfd8cf98751ba3ed7412ad7fdef13bae0ebfc5f68b8f39abf6f0733b76a9e753aae3fbfad7f5fa0af7c38191612e7ed3b9dcada879aafe1ac10fde26df3f59dafae157fc44efd359a858b103f64804de37493e00033804e0fc0,0x8404180c0420c02a1041c006088040289a2801080002a881f1102002023880020404000894218b024a0808550200002040805202620c82030708d5443080020400004480a062a200820c1081341a82813a18020040c8c41140019900880580),(0xd63f17fa9c68d2bdf535b38bcd758b111b39c01bd69be7f0a50ac254b1e4551cc07fdbcdedfe5eeeb387dbd53fae44c6ebdc3b6780eb5af0c1a79b91bffc324ba61dab7f27c45c8361e32fbf9dd223ace023d884d4a24ccb68001a00017df020,0x280c0c90203a206803b5498a8b3095021c48f0a156083e4a699402800127804c501e109e4800298600410326208625108400801202c10a82104a48122a18390037004ccf020c492210240b8121520a0ce020d92593464e4d42089bec004dd000),(0x99c24b80d76afbf7cef7ea7dd094ab9356b93e65a9cdffa72baed2befb5d76ef1497e07d0f969638ec5993afae29b7524ad5c1cc0308ecefeae8482712fcee6dbd4c45f9cafdf8107e690a30729a541d608c4e251699320405046a97fe220800,0x79028a21f340c9344060a413c01421161420845ac1e69c434804438164018429e013521141600870510060000a104b165a01138410190060c0083408a001345d4914eb02400215119c00128f008a445d6281c61d34bf3320860c2446d7220020),(0x9ce514163e2d31b2631774cd44055dff25d644933d575ddeb84f82db58c7eb7f669b2307f123f546793b2dd7fb279d374f30adf262f5ad3fa9a338eacbbd33f87a1e7ee2f359b9ff285f161dbee9e539378730c048c3386b6ae31020002000a0,0x4702504250011201c400920140426200c2010304a0e741100402085da8c84710a101c12111688270c5a494518030ca040bb1648dc508903c4810a00891424275c816a0101112040c8301c04a5a89e53116c520d868a93132acb7640001320820)].toArray
def x487columns : List ColumnInfo := [(513,0,486,0,8),(132,0,867,0,7),(320,0,679,0,7),(512,0,487,0,11),(32,0,967,0,7),(519,0,480,0,4),(673,0,326,0,4),(801,0,198,0,4),(322,0,677,0,4),(96,256,647,0,4),(324,0,675,0,4),(258,64,677,0,4),(514,4,353,128,5),(130,4,865,0,4),(833,0,166,0,4),(134,0,865,0,4),(900,0,99,0,4)]
def x487autos : List (List Nat) := [[],[98,135],[81,114,134],[81,130,118]]
def x487levels : Nat → Packing
  | 10 => x487l10
  | 9 => x487l9
  | 8 => x487l8
  | 7 => x487l7
  | 6 => x487l6
  | _ => emptyPacking
def x487index : Nat → Nat → Option (Nat × Nat)
  | 10 => lookupWord 27 95 4 11 5 2 x487h10
  | 9 => lookupWord 209 263 6 13 7 2 x487h9
  | 8 => lookupWord 21 89 5 12 6 2 x487h8
  | 7 => lookupWord 1 3 1 7 1 2 x487h7
  | _ => fun _ => none
def x487 : Forest := ⟨999,10,fun j => x487samples[j]?.getD (0,0),x487columns,x487autos,x487levels,x487index⟩
set_option maxHeartbeats 0 in
theorem geomx487 : graphValid x487 (boundsBefore knownx471) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=2) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx487_10_0 : block x487 10 0 1=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx487_10_1 : block x487 10 1 1=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx487_10 : block x487 10 0 2=true := (@block_merge x487 10 0 1 1 sx487_10_0 sx487_10_1)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx487_9_0 : block x487 9 0 2=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx487_9_2 : block x487 9 2 13=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx487_9_15 : block x487 9 15 7=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx487_9 : block x487 9 0 22=true := (@block_merge x487 9 0 15 7 (@block_merge x487 9 0 2 13 sx487_9_0 sx487_9_2) sx487_9_15)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx487_8_0 : block x487 8 0 6=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx487_8_6 : block x487 8 6 36=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx487_8_42 : block x487 8 42 36=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx487_8_78 : block x487 8 78 20=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx487_8_98 : block x487 8 98 20=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx487_8 : block x487 8 0 118=true := (@block_merge x487 8 0 98 20 (@block_merge x487 8 0 78 20 (@block_merge x487 8 0 42 36 (@block_merge x487 8 0 6 36 sx487_8_0 sx487_8_6) sx487_8_42) sx487_8_78) sx487_8_98)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx487_7_0 : block x487 7 0 21=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx487_7_21 : block x487 7 21 26=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx487_7 : block x487 7 0 47=true := (@block_merge x487 7 0 21 26 sx487_7_0 sx487_7_21)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx487_6_0 : block x487 6 0 1=true := by
  apply certBlock (depth:=2)
  simp only [certPieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx487_6 : block x487 6 0 1=true := sx487_6_0
theorem tablesx487 : checkedTables x487 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block x487 0 0 0 = true)
  · exact (rfl : block x487 1 0 0 = true)
  · exact (rfl : block x487 2 0 0 = true)
  · exact (rfl : block x487 3 0 0 = true)
  · exact (rfl : block x487 4 0 0 = true)
  · exact (rfl : block x487 5 0 0 = true)
  · exact allx487_6
  · exact allx487_7
  · exact allx487_8
  · exact allx487_9
  · exact allx487_10
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx487 : Lower (varsX 999) (graphGoal 999) 11 :=
  strong_low (m:=999) (cap:=10) (hints:=22028484865) (nb:=1) (by decide +kernel) (plainA (q:=487) (prior:=boundsBefore knownx471) (before_sound knownx471 validx471) (by decide +kernel))
    (index_root (g:=x487) (i:=1) rfl (before_sound knownx471 validx471) geomx487 tablesx487 (by decide +kernel))
    (index_root (g:=x487) (i:=0) rfl (before_sound knownx471 validx471) geomx487 tablesx487 (by decide +kernel))
def mapsx487 : List (Nat × List Nat) := [(999,[])]
def knownx487 := extendKnown knownx471 11 mapsx487
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx487 : Known knownx487 := extendKnown_ok (m:=999) validx471 lowx487 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx503 : Lower (varsX 1015) (graphGoal 1015) 12 :=
  strong_low (m:=1015) (cap:=11) (hints:=22028484865) (nb:=1) (by decide +kernel) (plainA (q:=503) (prior:=boundsBefore knownx487) (before_sound knownx487 validx487) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx487) (before_sound knownx487 validx487) (16,0,999,0,11) (by decide +kernel) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx487) (before_sound knownx487 validx487) (16,0,999,0,11) (by decide +kernel) (by decide +kernel))
def mapsx503 : List (Nat × List Nat) := [(1015,[])]
def knownx503 := extendKnown knownx487 12 mapsx503
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx503 : Known knownx503 := extendKnown_ok (m:=1015) validx487 lowx503 (by decide +kernel)
def x511d14 (i : Nat) : Nat := 0x6050403020100385048403828201810000aaa80ffe00ffa00
def x511l14 : Packing := (2,1,7,0,0,7,0,x511d14)
def x511h14 (i : Nat) : Nat := 0xf0264501105c1e601c0002044000910d847b17e45e1014018b123c0e101a81d7100460c005c192050000d008000105800c801280d800344b116c855002d01b4115446114ac4a2131408803e40a0002459914cc17604a854005744f11580000000000a07241fa080000d06bc490002803404f41000000000000000000205a21600000888341600045480007000148100240080080002
def x511d13 (i : Nat) : Nat := 0x20e14810100a030740100b83c0c0b0401400f0707c0c0a040103a00883c0e0a0202400c1383c0a080302c00f028181e08058018210407c0c0e010280a00983c0e04050203a0070640e04078281200781c16010701010d078140e0805801a070283c000a04071c1d0083852040a018140898380606028201600709402060f820040a07012605048041c0605340a0103820140e682012060d81000140503845501824080f0382c00f018240a06008281ce0f83c02060502024040e4c1c1f0481804040002a20702804140e04061e0f03814140900341e07028280008683c0a090300014d0502c0c1b02038101200062a140b83c100b008180910181c0a01058201cf0a8141e070082014f028282a060004c100e800c1e01030480a080544260707814020a043c6d44b424c073e53c7b9cb7ab58b3b31dafbad0aaea83a66248a191f71d51aa1839619441269090d98b309106f0488220007ff5c600ffec0c01ffd62803ffb05007ff54600ffe98c01ffd63803ffa43007ff4ca00ffcc1401ff611803ff243007fe5c600f7f33401ff963803ff2a3007fe4c600ffca0c01fde33803ff261007fe58a00ffcb0401ff932803fdc45007fe48200ffc88401ff942803ff303007f68ce00ff908c01fba44803df4cd007fa88a00
def x511l13 : Packing := (33,2,7,0,0,12,0,x511d13)
def x511h13 (i : Nat) : Nat := (if i<1 then 0x61017409b64802000000000000280f60000305e58a5c022cc0c2d08da8b0d820360f9c806b8994449b02e800004019ec63c6253611580001850a00000000680a145db00dfe05c00003c1480000407440340023222a3000028c0bc660c2a900006889881bd4009a05750c1705c6627001647829e40f5e0cb000000000825b008f60328000001dac00100005807dc20d405f6122989fa01c0800bb020c82eb4523e120204320475e0026063a01f1380501200060306da03f34061c0f4a098000bf40fac2bf014d68b8345e4a2d3a0425034d41106064e00f703104151825c80498000080de82afa001a046b8254a0380000182d0000000001029f0417c63480aa0000200b74144c202000000003819e000000007010dc4d8c017c030e8af702108128712cf00d241cbc0d79040980380000e205f005000cfc161410a104f708b34140a100f007a88a4809460be802a80252c5e7409be40d0813000000000000008b06c0e9a0d60000183440000a08c00000813d018700f8905b088b9c653a127c04ad835205c48078101588941023900c9612500002d87e0000005d8000000008210217778123c01a0000004fa3032c190402300003a0f8000040475049581ce407962ade07d2838682260206014af82afc530e2318052c82d60434201d9041b0136825d209781788000041dc000011748000000010079e0392822400000000213018b3502094016908f40a9140fc0000216ca8095848cc10dd031601c684310036308c38a6c0001c309000040bc3825e60460000603740001c00600000000005fb6058f13e000000001000c707a804480428231c811db81140000805e0000201ffc0a9a0fd000040363c1e40000f035903d8000100187084b81a6451a0000c0533098c00000000000000000000122340000000024101c121a05fa02700000a40400000801d808042da0000400f540e18077200d082680008a2280151702ca40da20fb411b481b000000085d05bf816c009c000000000000000000000000048a3280dc00002086782460173c03bb02bf80a4c023a096b03ab84978246a22411736004d002580d9c01900000000120eba1415006704600000d108a03aa4c700000d05790488c1c5e27f703e4036a01e6022a8126000008470820e9147b023b4199c056e600c8c85062ae2eae1370887e84ba611431657022b402840525013483ff806a40d2b028b84b28059c2d6201160ac0011a6024802e70be084d72201e02d108cdc1de2256d04ee82b2c17ae0e40800c01850c10ac0801c01030c384d0db1c02812c05c10430000d35530430023441496421078c01e424000001108100100f1c3302081180085214102200a820490440011052c200960011208420004018e00f2cf11304120104200708d34708100001704b08436e38000048c096042000001 else 0x2002215a60305c11720f1516c2021f8041e262202c80002c21680ec015f102c5004ee24e403b108bc00010010c03300001ac7c000050948b8fe864e806aa010800010607e0d5c101f047f024da0a3d02258315247002723111981400001629260248000245eac10fc23d8000000000000e065003a40001c0ce301cf09c480960000204ce82b5c558a117213b480200000000000006831c000120b3b206a031b860d161a00000000000000000416780002420540f0301fb040f0180c0a14041601764222e107c00030054000000000000408ff403620f7e0882807085928037000020ab88062a0a9e08a98c8000000000d06e481a341fc42ce0015384af01cf626f700280000441b6124202138ace85c842fe71211843b41c6000000000a165c19ba273e13d800000001c31d0000180e84130a0e)
def x511d12 (i : Nat) : Nat := (if i<3 then (if i<1 then 0x3ff9a560600ffb88951802ffeaa60a00ffe54d20803ff9a254600ffe4c582802ffeaa58a00ffe60532803ff9a244200ffe69532803ff8a960a00ffe60951802ffda348600ffe61521803ff98550600ffe48151803ff98150a00ffe69531803f7e5558e00ffe68930803ff93254600bff68951803ff95250600ffe68520803fee2258e00ffd54e11803ff9a454600ffe60520803ff9a548200dff2a582803ff98344200ffe54162802ffda558e00ffd4ca11803ff9a04c600ffe68532803ff92058e00ffe60930803ff9a354600ffe54d21802ffda54ca00ffe68181803ff9524c600ffd845828037fca954600eff60582802ffeaa4c600ffe69920803fdd628ce00ffd54a11803ff9a74c600ffe60121803ff53160600ffd60e11803ff98348200bffaa971803efd6258e00ffe69510802ffeaa48600ffe6a131803ff8a94c600ffe4c162803ff9a84ca00bffaa932803ff9a160a00ffe68d10803ff9514c200ffe60d71803fd9218ce009ff2a551803ff18384600ffc61611802ff9a360a00fee54644802ff9a850a00fee60a44803fd9208ce00efba2222803ef96358200ffc84530803df9875c600fde95560803ff15284600efea2141803fd9818ce00ffc54211803fb92191200ff6442338027fca960a00ffc4c521802ffaaa58a00ffa60622802ffaaa54600efea21428027fca95c600bfe69563803ff18154600bfe2a521803fe95088a00bfeaa963802ff8a94c600fbe54a66803fce228ce00ff984622803fea2250600ffa54622802ff8a960a009ff2a532803fb98191200bfe68960802ff9a048600fdb95622803fd9314ca00bfeaa981802ff9a254600bfe2a532803fb95450a00bfe68d60803fe98088a00bfeaa982803bf98160a00bfeaa941802ffaaa4ca00fee50542803fe95388a00bfe695328027fca94c6009ff2a562803fda3358200bfeaa9218027fca948600ff65c633803fea2258e00bfe68963802ff9a060a00ffa4c982803ef92099a00bfe2a551803f7a5558e00bfe2a562803ef96558200bfeaa971802ff9a85c600ff64c530803ff1814c600ffa88930802ff9a844200ff584633803e7e5599a00fbe4ca66803ff18084600bfe68582803ef95099a00bfe68530802ff9a24c200bfe68542802ff9a550a00bfe2a563803ef93099a00ffc44151802ff9a550600bfe681518027fca958e00bfe69560802ffaaa50a00ffa88960802ff8a960600ffa44222803fe98588a00fdd95611803ede3399a00bfeaa931803fe92048600fbb88a66803f7a5550a00ffc48211803ef96258e00ffa54920803f7a5550600bfe68532803ef95399a00ffc60a11803fd9828ce00bfe68d518027fca960600ffc84542802ff8a95c600efaa2222803eda3399a00f9e95666803f725584600fec84644803faa2291200ff484633803eea2299a00 else (if i<2 then 0xe8f2b1d7a38ec6be8cbf18022d0c54c89db123a212c3ee876f0d3a172c286849f079a0cdc14681cf01fa014bfde7f4efd99f7ebeb27d1ef899ef2bd7c7a3af371e5cbc5a77f6ee99db2bb2475b2ea11d12b9da730ae4e9c6db87c7026df71bb9b7466e0adb61b3cb61a6b76d549a74b4806842cf099bbb3186586c969911b1c462dec469858b048600ebea179faef45d2ab8d96ffad965a5ab339637ac1a57b2adc158daad0550aa8c14e8a9725226a2f942fa8144f6a9d5938fa6e84d8a9a39317a60c4b4695b129aa4d6493e90d91e6a382466e8bb1150a24c441687010bfa13e41fa82f103da03a3fca7e68fa29efa3d5e7968f0c9dc43af274e0e769ca238867030de09b8036926c20d639a6834266748cc3993231e26270c2d98062f765d98b9296da2d325938b0695cc2b165528a7a94b428e650f09fd93ba26de4c4096c9284249a48588db914e221a433084090361fd63e307aa8f141da63a487288e101b9e35e869c8cee1946318860b8bcc17022cb05708aa014be28504e48988127a23f04588870104a1f903d187580e2e1b3033b862c0bc216302a08500096a11a820f83de073a0d2018382c604e208e80fc81ae02c6048806b808c00960003ffd5358a00fff69521803ffda14ca00fff54981803ffda360a00fff68931803ffda74c600fff4c582803ffda84ca00fff68951803ffda54c600fff60951803ffda848600fff68d51803ffda54ca00fff60d71803ffd8348600fff6a131803ffd5360600fff4c951803ffd5348600fff69d81803ffd5258e00fff68981803ffd8548600fff68d81803ffda560600fff68582803ffda64ca00fff60532803ffeaa60a00fff68d21803ffeaa4c600bffaa951803ff9a760600ffeaa982802ffda258e00ff74c532803ff9a054600ffe60171803ffaaa54600ffe69182803ff98550a00ffe54163803ff9a548600fbf54a66803ff9854ca00ffe68981803ff93244200ffe4c960803fdd718ce00ffb54e22802ffeaa58e00ffd4c521803fdd518ce00ffb4c622803ff95150a00ffe6a121803fdd828ce00ffd60551803ff9a04ca00ffe54d60803fdd218ce00ffe48530803efd6558a00ffe6a110803ff95258200ffe54d62802ffeaa60600ffe69932803fdd818ce00effa2171803ff58584600ffe68182803ff9a64c200ffe6a120803ff91060a00ffe54910802ffda558a00ffe69121803ff9305c600ffe54981803fed8188a00dff2a531803ff9a348200bff68d82803fed3260a00ffb61622803ff98250600fbf4ca66803efd5399a00ffe68d21803ff9a744200ffe54963803ff9a460600ffe2a551803ff93148200ffe68530803ff9814c200ffe54121803ff9a360a00ffe68121803f7e5558a00ffb60e22802ffda160a00ffe68931803ffaaa4c600ffe68d81802ffda354600ffe54d1080 else 0x38b010058060903a060d1c0bc1300c1e03408d83e0581a00071707c1604c090040cd00e09806060d0246c13020082040019c0e0581d28fe0183a0704c0b012088c0f0581f0241300360f8160682c08076007c0a0dc0e054120003a0746058040983a0a819b0501407c0c1840204809007e0782a0181018642f04c0d058020a81d02400b8380f81c0082034707307c0b03816044000e460f82c0981207801b02c0f0006407416043e158260f8060605980dc0b0080f0781504381f81e0a80604061809c1604c09030a0d00e0900606838346c1707c0e0440102301b8283181e0183c0901200bc0f00c1e04414d8141582606140226c0f05c0302030b8160682c08070506c17008130241d03301f82e010260503a067c13020082081f0306605401383e070120007160fc130341e0180a008151816078060e071707c0b034000e2a1d802008a60481c0e82a08984b008020fc0d0481e0503202560181a09038180d1b05c1f0381202400d82e078003002404839f07c0e05402020450438278260f8140b01a00784b008020fc120540e07809383e0701200071707c110380026068d056058060e0d81c682b00817074082a300f8160981a0b00180bc1300c0e07408d81e0b006048240e60500bc1f048170340a0046058240f81a0b801b07c120240e05097003e0181c0a83a09012187c1f048170340102301b81e0082e0f024047c1f04815008081140ce0a6058240f81a0b001c0fc0f0581f024120003118100581a0b0201c141e09c1604c09030a0d8260680403028246c1303402018160241cf8260f8102602c06801f0401302815030a0c09e0983e0502c06801f04c0d0080605048d8200983c008184c0d1f0382705c080d030d07e0f81c0482401029c14c1f04c0d0002cd83e0581a010220a6c170740f0040a04494f8260583c0a81e0068070441e05c0e02c00f82041816000ce0702c0e8c0b07c0c048140e400f83e0702a090101d801f058370240e008260481d183e0581a0102822821f00c0d0481c0c068c0260e0fe0b81400819f0483702801038160738338160181a0b03c087c03048150341e0236078040b83a08811818c1700c0e074100c4091826018140b01a0e605307c13034000b360706e0482c090001d03a307c0a034000e2e0b81e0183c08811a01c13008170341e023c138260102e0f012067c1302c0307815033605056090060682c0e7c0e09c1600c090481cf816098060703a0a682703c030781504808f79aaf0fddcaba7373bae56dc6cb7f36ee2db1db2cb58769bad11d9e2b2df63f2c58d83eaf975d3ab7cd67cac4f5682aaad50aa97f51d2a00d3aca6d74c82960d26ca44347aa8cfd172a2134322839d00a9f433d82785ceac9cc3380a6cccd3a99cb3292627cbfa97372cca578ca92948f28424d3c94891bf22a2433c7f)) else (if i<4 then 0x881600941707c0c168120203b0046008040a8240e0c9b0040e0581c12064c824058020081a0e059f040130241e0580c16c01102208810228384702a0700250441e02c010040c0b3e0f03e050120902c07802007c17030620480b0038470283883a0409207024009c1d07c0902c010080e0541120c0330020101a0682c090120eac1f0306b00038a05c00804068181882c0f02204a0390407011220b8020081a04061a0480900060809a0e0c4008020902a0501a41905b02c0d078160403b004a0f02c00802061181d022049096044100d814118010381d02503809c0e83c048140702a0880280b80d030340c4160081e04409582209812058020102c0e81a61283f04812078150380b004a0b00206062048202a78090280013031048150780d38100583c061140a826008046024080d40c1f8020581d04501d0220b00038584a0fc0e0381e0541202c013822098120483c0a81e008c1104c090241e0580d00403903a0f01a06810170040882ab054170741c1fc09028120040d582c090104e8003064101140a0340c1880107815209c0e8381f0201d0120102a06a80802c120740f00068e866048160681a0f02a09802704c090281f0340c19815004e008020a0c81850720340e070480f8150480900503102a0b01a070002a8220503ab044130240b004020580d074a05002000720611c0a83c089c081a40f0581e0408b0042090120e81a00059819809028010040c1f81607411583c0f81c0682c09016008c0b07816034001604ce0582d83e070220b801f040830281f0306605c01183a0f81a06072050240082a50f43b0340e0740904417004a3f83a0f812048240a81e009c0902c010040e0581d04440e83a060f01d02c0881200902f04c0d0705a02c00e886088260681c0a83a0580260580d030710704902812004e0f810378001c5c0e0741300068a81826088f07c0b03c000e2e088240b8020181a0703a049815000646074068181e8002b0140902a0eac010040818030b81e0b8160006170741f0340e02c0100811054a0e81a0482022504e0240a044101581d03416005121002000a40a0740683a05022b02c0f004150481d0e38278260f8140b01a007c1102c030341e05448f8260e8160081c0a929c18c1700c0e0441c0c8091826050040e82a066c140501f03811020a0f82e07002088140e6c0f054030281d04360b83e0702205801b04c0e0000507068d816090060682c0e602b00817074082a341f8260f002070104d02a11fc0b0041307815033e0906e06814010540b03a10bc13004170381d023e0983e0502a0008a067c0902c0e004150481d0e46058240f81a00829b0501407c0c18812024011816078003202a0f021e09c0f00c1c1a038c85e078020b83c08811c0dc130204f07816033e0b02c1b81c0f02400814189c1f0280d000 else (if i<5 then 0x101d802f05c0d0203300060d02e0e83c068260009844881f0240f00058a0b60e83826822040c40b01e00a40b0340c19c010003816440b01845800268382c70b019c0902c000c32240941c0a40a8381d01a0502600b44b0380d03059070481940a04c01703a0581e00088240b1f048102208e0b0580b41d0380b005a0f81404110268203302c0607600b08c1683b024081f0382241e0581300660e83c05802008181614a02247e120480f40c1f81e0580904c01883c0580206122000582c80892505a0ec1d078150308c0e81102c01b0160081848800160b1e0241f000910002c16384383e060c40882e0070770340d0540b00030e85e0701a070382c0583302205802f05c0d038120203b00061083e07816000c82c601c05c0f02c0017058f8200983e0502c078002c09a50780b004010a4110302d18020081c090101c0c1f0381d04c001a282d816060ca0b0260074020580c13203d03a0e0702902c088020501a82504c0e41c2d0acd82a0b81a06804090120e808e054140d8100c8010281d0350270220807c0e0940a8020701290740b0040d00038c8fe0e83a0702c04826008815054001e8100c40e07409283c058020680208059d0280d03062000450441e05481901a0607c0008c048220f02a91443b0240a0740d05413004e0a82e048140883a07802201c1303c001a048d816060b20e0c80b026008c1104c090281d0540f0040338120581a0683c0882e00904e024080c0360481d0580103520e8120780200071818c1505c0d0381d0440b0048178260e0b4068160074150340102030a11c08824000881f02a0683c04a43b0240b0340e0741504c0120ac04814068181d0020a8240eac1e0440f00068a8220e810168182260460741c0f4101f80a0040e055047002000701f0240a83a07012b07c1303c000b2a078020082a0406190bc1104c0d034160740b004c290760f03a0501c0b026009497044130741e0540d02c01382a0b83e06818310240480250440e000490140905055182a0b83a0f81a070220500260780d03046020610081105483f03a0f0120408a070040a822b0781103c001a2a0481a008381c50560240814039078120580d00503f03a0e05c008040a81a0901290bc1d07c0d034160440b004e0581c0a800325c1505c0d030330240a0081107503182e0683c0901600706305c0d070100c80b00424b82a0b83a0f022068160090620340c11036058010440a07521981a0683c0b012098023044120541e0240f003e008020e0c81c541d020390440c1130250020007a060fc0b03c04822904809034010a41c0b3c0a800563070198090280d0341d058120052088140081a0a0a98158110402e0340d058010281d503a0e8103d0201c8040a81a7004020441e02060c0e200070e0f83b0781d0380a04817004a2582a0b81a0683c0 else 0x2208e0e0380f811078150380b005e0f816008005e0702c706702c0303401050302e40448f83e0b41783c0e8381702a0682405803b0541f0381202c00183a0981607800320b190481f02c0103058d81c06818300c82c83c090)))
def x511l12 : Packing := (305,3,7,0,0,15,0,x511d12)
def x511h12 (i : Nat) : Nat := (if i<3 then (if i<1 then 0x9902e9a0368603fc865390528f0099e10e8000010b8a919c9e103d0479703f0701b2205964632d0364416bd63425842d481ad2133c00000c0088810f00000012c2c5e1800005094c426940000381830000100fcc817580000619a8c028b01a1b8a876174be064cc19bc015a0000182594828b800000000000000861df03ba9004b60ff40000084e1c0792e320c42267049f0162d20e4f845ab84a22018522a3c0000303a49070f83423c577e047d6078d225ee01f2483c060172621bfc60bc033ab010c431364116792b090828206610530500f200001a07e6000e289a20000000000c009183c8000014330c000060244502c06229a41a080000208bae0b8c000048a9fc03618062680556896fd084de0a434003c0ac6c09c7c107fc49a501c0203d682f0004f668bae808eb631e545d608cea1067740f3fc0fe38262b0179800aa426d4834a208aba025444f6a09ffb1235831b89077c03725021c212c4c521d0b8c018f9806718620783c721a49205a2c041403a3203a8a0c00450ed8836a0398e1115c09b603e7b06e8000004256382fa0000000003c17a00102408a9a34130156a82a481633c0a2e45b42803400001c1222c128880a300001e32e9011a1036b21961a10e5c65fb287f3071e88101063030708781b23e04c047c787800c0010106104123a24381140005708183800238081222428009246ca084c483020070b0a004840a6c7000a140004e4b40b000071504059010238d0f001c180180818016a818806d86100004003021c00108701031c104023c111810644805040800902284861c1460000142801e640100c30482043c10116283810c08e89242c0020050700028079f003862a0608911022001a0a4c20504152a40a780010c10482000408518101021404112025cb00120848e020079c0a3c0071410007003c609001090b0e0c58100041100a081090a783891e147080c30000020040016001095c60c800c0d11c28a422206252000628c87041c0030028401005c084001c5805e00202120c108063430028001010a00f0b421c39b00480881000a82061138a080020002003864a18101000418100340090068002007440b02000002a0c10006000831270036180c09f001c1150c1830100000000c0c1000010c890614082100d98622000010e001030a50201020c600260068b0218083041c08000285810028112000c202000850300000110004004080800d04000000204080000c3120000080021040b0c0860000141000014180020000b0009211044c60d0a34100060c3001c1018300080005600401000c5001600280082c006083800d1248089020822130040000804204040021700041810000088141472000042800c00d02000000400000041200000020000b0018001020c087000430000001870010186060c7810204195 else (if i<2 then 0x200000141136c12b80b6dc19ff4026841a4a807600000a03b40000704496159ac020082818000000000000000000000002a00c00ec400006086b0000000003016180000b0905a2081019928bebb038aa136100cd00512000004112bc6958000000001412334506800000006382de2c5a950074106a7810ac4456703366108a6139f014b988399007502e81806d98cf4f024200003de45d8adc105fe404c9861328a7f00000402be01fc00000000000000201ad10bb2d128be135481c94817000001e0eb940d0000000000060a34000000000202fce20c50157889a85062f20250c2294039430827e24418037482e5d063d20cc2424e782e2006b3811210034a04cea0491a293500b50841e7169b80695d20bc8444a1562c26d8c17be038e412ea207968639e2007e00bec0e6dc24ae04c0d06aae0bc2c15fe0815504c880b1b824ba01f84032400001816880000b04ff2258c0072f89070000080b848031685230000120da841f880000e013ac088581934827b40295a0d1ac619883f400000404a4000050b5400001630040000383b4000000000000005035d30392000000000180c9b0a160000000000000000001c03a4000000000103634276444e9e01769188323296c279d01bd61913e0fb6c5d2509670000000c97409698a52308e4000000000683ccb081aa063720baf08bd809d7ac604c006e8256a065043448000050003108bfa0a1845128000000001014a5819e0000000000209c7c4298000000000400e7865a881ece088c00001081e80000b1657e01adc250b815de084b82e6000003818bf0633e03010033b006dc025ca0754455afb006a0089202fec0501049df008600001422828505f02f680ee680b60000041078e1392029780000000000000181c08000000000c2e6fc4d18000090423c338781df91030a15740000204f0f815c00000e02380000000e40000060dfc0000600d3c1661610f0427b1095d01617c128f00dd2837000a1c00000c1e9d0ac70000040f41c01590ab0d010780514867800000a166f011b1c0be40128416c842583c09e7841900001403780000201470000121470021b1001f0004ca0ea2c0c39807000000a0be084e138098007322204c4275681e881677c0aa544a7583d4361ec00003c40b28284701336045bc6830000011a452328ec61b000000000061060053a081c870297e2205063400000412d68074c000064030c0546e2324000020301000014c0eb413c40484802dae118d0541a8476b048a42dc0c4c9b8b733170aa0377022f5000e1190bc0fbc41c6a880d11801e01d680788000031444000038427103c11097400002c19a000000114e00003c10ec81db604b8801a0815e084fde0967a30a0c26e6892e00000628e7821538115806f800003c020e826ac04a80000000000000060562626ba467 else 0x16ac0a33c5b3981e2c01c32327a810358bdda175a421a5018ea81f4c047f6267d8236901ea0000160b59055008460302af223dc420a904c900000a038000000000040a3ee23c1c07d68c3402046a22198696e01d02017c202b40000280eed033dc26cc0000002d2500c800000461558c08207e4c02ba811308442402f20000000000000000000800a7051e880eb0024f62645412718cd9f876b60420c09500000707c4603d18296800000000060ffec024e00176095c41206018100000b131800803012930d282057cc057d40a088342805d160fb244fe5015b706c420a85413d68833a08a3402070578e831371112a2e0dc1a5e0266900340093f007f1838cb049b200fc000035c17c0198000010205800000000000003c230800000000000000000000000907ec00000000038422013c7800148431c01a13028dc223dc42d88ba1000000000000000020ad026b8238d82952010bf10f3e0a2840b780000213c14344d451e2083000001830e942370000090031e0769c23528c5c000004045f40360002e505a9e26548134c0aa1613e7c3445c42c102c90000000000000028c6f1136481481c14f5031ab012dc0c180000500d2000000000000000000000001a0c1c0000000001188b02adec200c80400000000000000050bfb000000000101ad800009120400003c1110012ce0a03627e50188903a1602dd833b40000485090000000000025b800000000120b2e0227684b6103f7a844000000000030125a071000002033f0000000003e1c6088d9310988037284085834f9046c431980000282085099400002c68d00000500ee0000101aa284cd9183e0000180c24890ab101940137447c0000000001a10edc207283d60000080b340000200c30000000000000000000e0a27e214bc17cb0138c07be0000000004802370a0000000c1287802ff00e5c0e2984b9c8079413e2c0296c1f4c0111e081000003001ed03f97042082baf807170a88d13ae0000282704022ed0720204314582140f6e056c4012d0131a8203a089fa2b0c02398013fe15b0810d4458c60259c050a03148000020cce60a5cc303e415a3014e51566c0f2ae99c2026ca02d26085aec75182428053a20fd5000cd8b175077d40b2a80ef0000030448007c4c210c093a3145d6058dc15d902c8c19f7e096d4caab041b00001e218a041ff801de04180126c410280000006d3612fa01becc887d0365a058b421618b26e08af087fd45650000060655c2ed645c1780ab5167041171c486440aec000200003c279102edb1529e01e8463390bee90662200304059f05241039b409cdc25de85020000080c4000001837600001a06580608b8aa85198a2054bc0c2d8441c01a802dea8433e015e8167e80a9d44a0e8a42b1969a3071c00f083e54079a00002415ca892a2040ea131600d4f02)) else (if i<5 then (if i<4 then 0xd16c5a168bd4802858131c40cee1963a0948c28c88140080f3d04bee0ee2c288b8167f04d02006ec1d4e029bb065d800d8c63c70368e062b804be01d9f4086f0998625c1827c000008091de035c0000000006065800000000050a93e065e60526024580000a07f80000040b3409e75268e00000000038474315a9c04f58210301ef6097fc22974216f816b50a2bc04d040bd20ad01016380849828a60b43b02e220450043710087c0a300000242428000010739625de8262000000000020c878249f0c230000082ee800003031fb050ec005685938030ec04dec2e3a82489052b604b000e13c17228c06217cfc0e61c23e080ec00000c12b78126702a8105de20dc6c0c65811dd148ec1430c141a84e6b15cdc32cb80ee80000111da000000000790aef00e20000141e110009c01ef42113418c30a1300000601534477981aac01aac23a98657601947060a00001c083c8033407220000280288000000000e060400005837a00000c10f805943803bd120a0000000000000000000012e7c0e3530f2300ad0064400000000000000c32e30190683ce108860000342448000031446e083981998000000001806b341f0800000167800000000040b720000000002426c80000c0985632e6402d480206076000003425ea0bdfd1057c0994000060bff0000062a64000018124f41d5810fd00901821e0159d607a40125a8ad5000000000340de28024d0236829b1004d800000000061168000000000e0955c28dd817f703d2b062c20329000a3800fa159ec0f6101d58894680042004ed41e2f0405403dc6106985c3500b70000102933463af0158d034e0000000005012340933e2460011570ba70000180781c08340104470b6e0a64001c000009045000003c02f4828260a154146545fb800000000020b9b459af03393046002e48000000000406cf80a4400003020400906e2c1b01b6c09589090fe11e885fc00000100b000000000078ba8c0571a0e76c0cda81fe9042e2013d0c37d029f6053000003844400a4b0000000001c4add80f99041b41394402ef0bf0318e1630b40000302b5a0800003bc000078412d061343140000008073f09e800001025a3803ca05ce82f5fc01f48bf610820a107440cbf81c15036ea03f6858f081c38195800003c1db001307143e2293cc66998060702e4a07494196e034490822c08f7801ba034c11898a13be065240272f00fa4311340d468ac86013ee027b0214c1b065048ec294cc149c80cbe09bbc0bf001e1c0178b023280f6b81d7d80b2001762146bc1b078ac9c1357424758293c90f6e1702633df4125000ce6057aa0bce80242825d4021be2a49c60610d26f0914c27bb452b40c3fc07f600000c13b6034d9097141475c136e99f3e0a3da2f610287d020f80711a00194016e8a49a1a1cc827205b6703dbd0 else 0xa4f980000505bc0000000001807c0034c0000340aa884af209a08014c0066b0b29d088e60319c04e183e080538009fb027e682886018fe0ac9c43abc3470000116440000010c2f4017400000021a700a880366c1167447a00000e10aea0403c486800003038e0000344f420109309e3423700000001050000000000000050267209a60000000000000000001a0d97006800000d08f600000004580000b0188000000000782c1705afc09de8053080a9a0207a1237c5b2a89d200000209e605270a009709b6c12a3c27f4038561210c24cd853f381aed08c848db14533e8377303b9203d96cab803d1060b740a5240a230125517662318f010cf0a40518ae40a274288782dd503010d08d0581d03ea117cca31ab04c28043311095c00c8000048350208fc60c70000000000000002255f0099b118300000000000000000009148b42807400200000107f400000020500000900f000003c23c3895e8170800002c25af027d901ea000000000383a60000120290000040a3100000000034111d084d81756204ea001878a61000000000040aa18c5300000c03f080a610ba60000000002c101101ed6042a6101e819118093c00b8000038625f006f3075800000024f682c2b024cc133c000000000713760000180a8981220000000001c27ae84a5f0656c0d22011c8000050952000000000309260000002b300000788f6d039f6090ec255f8357000000000000006034720920c008a011938c3cc14a8a126142065018f5187a807d6003f28b88e06bda28cc000018b7f11a00000020238e837300000805cd458d1848fe153a208a5806fd83a5403a2213440000001e400001a12810117a0d2500000c0d4b8489c89e960a44c0ba80000000000000122cc485e4801ab41a2e207dac0d2404c8b108ec328784acd828f2037c60f1300bb808de40744c458c81f180213a0016a2d17416e60cf94001120d8f0089c81d630466c004f450b0039f00001e036a0120800005161e000020062e80c100000413efc10a00000f002d80b3a0232b8395f14e70149545ea80000e08b000ecbc18500000e19094326c00006842f509a80000245b0480e3f08040000000000000001843011e40000000004126be0028028b78494c023d224008204f884f708ce40eb7c4bd38335606f0823e6c0f3382dbf0142611ac00002849250860a02b205cb702b7d08076067d0618e02f2b02b361420c4d53052c41076c0aac00dc183a770001c2a9f4265a8953a14dd60d71c02cf04f7804c2411a6c0ebd8182301cf60ef4058ff8aae306dc00535005850ab25008b6137d021ec84c3f0287621444225e8270b137000897049bc8088c02fe0000000001022d306198801984ce601df410d140ea8820b80438303b32e01e447e902ee006dec143504109096ad03ce60b304068b8383807afc) else (if i<6 then 0xd032300000000000000000007067bc13b000482808fe06a2e06bdc26b2020b204e800000000020249605b4000010030c812b4056680148000000000618ace0eecc61048199e047700c5000001002c0000000000c22df8bc53054080463819238140c058b42f680113e826e904300000080bec818e3168f8340f01dbe01ced055d6018c80ca80000c03c3c04fbc0dad836610397c061bc0c44037b1090c409ac0000282ac000000000240fe80000b07784c8b3463580000b012f22ce781afe027c00001e2a3941ef0889d00000000030421300d8b130000003c4118000030435e0ac0c098801a3603fe80fdc44c0800007080d36e13c50e00000207b2a0522c20b680b8905c1001fc40a9f83dc91a184212f007c284b23199800002c40d389cc60413212f00000689d8d13b70015c0000003eb603e4a33064178800007054402444000040521c00a12040742697830fa047c4309241ff4098da010860a5980c520065505f701389c23830b5b717f2c10a1467d084ed107ab6022884b9183b5e11a5e0f9b04cc00c5a00001007c0801458d2f80502009d4069018b9990610365564167811758098d8137b817e902d0a09fe0341c80640043100000000000000382f50000143394000008504f0436a09780000000000000120b55c260b02c4c507a2109c00002039600000000030401b08828090181012014d00000a0169e252c00005042e30395013a5c23bc881c0046e000005803c0ce2307d00000000005021c10479830a7819c510ac000012115901203039ab06d800000000000000d61b7811ffc4fc00000c023400001410fc89879072e408acc4a8f81f770344c146e411c1034e702e882c0600db0b8f2c0123006eec067884a7f0384e13c14545f08ae80864a331f816c4097e014f0028f9c63ff811c0000101092002ac8a9cd017bc055b44eb481120071720de5802db80fbe0608c21ec0000784531014e2004000a7f849a5051de04e4c510382a6c413b42284c04618b340000030ea081528000060581a0a57c54ac80b6a1a3b413e5802358ce8c181420c2e408fe8b90f05d860df8807330327371f10453c0000704d7e201200000000070329000000000140c8000001453d205d5c5348011000001c0f2d049138389203e6e11a0c16fb83ee000014108d417b78437d1895c2f1ec0fd003126037e0249c000000000000000000000000030300001e011d411d00000b17e600000000000000000018119a864c000000000000000000040ba240700c095784aa18161b15f6000000000002aaa18bea22f140ec00000000000000300b2000006011a0013a02932025aa0463226dc0000184e8000000000240a8400f0b01ad00214c421a0c0b609dda125ac5c6a8a636190200003c0010841c000018098101a0000004046a8141b023168375d14b600002 else 0x101ac40a3a3021420b1c441220b49c088120e804123182d300001e20a0401a881e3e1588e0c3785464833e41887a0ae98100d046fa04a6c01088655d88d1006c3c04dc000030c93d00940000201eeb039e20a0ea0e1a803d88b7100001e3150000030089901d5a06e581ab58b5a900cc20c6dc074782d900001c0e08c0350000000000213e80000000000004e00002414900b4800000827230551)))
def x511d11 (i : Nat) : Nat := (if i<9 then (if i<4 then (if i<2 then (if i<1 then 0x681518035fd44152b8c011ff2e5a558a008ffb6254a650047fdb82a571803f9d2aa82a1401bde954a958a00ff8c6708c45006bfa88aa9418027fcd9152c0c013fe2e93160a00def4aad12c1007b7a88955428027fd5db4a994015bf2e56258e009ff36a54b03004ff8b9689518031fec0952c1401efc6013160600def4ab552c7006ff211aa98280277edb554c0c01fba5422299a00dfd444d2ac7005ff1b354211802ff55daa711401bfa88aaa50600d7f511552e3006ff181aa931802f7cd8265334011ff2e5a54ca00def4aad0a850057f8b968530802ff8d830708c01ff4482118ce00bdf576994cd0047fdb22a581803fd4c2c45224013feaeda160a00ff926299305007f6a55889418027fcda95290c019fe680a960a00fee4aa98a43006ff2116a1428027fd5db44a8c01f9b9562299a00dfd44454aa30047fcb968d82803f6ca9467334017ee6c95191200bfb360c0c670047fdb32a562803ff0a8a2111401bfc6a13148600bdf172a94cd006fea2269541802bee5caa319c017eeaed8291200cdf952b2ac50063fe882a5718023feda95298c013fe2e5a160a00bfb36a90c67005ef9b254266802bfc5cb4a884013fe6c1a54ca00fee2412ac23004ff9b12a5328033ef19952c0c01df64c0a94c600ff630508c89006ff211681828023fed8952c14019f78cca948600bfe172a9423007bd688846338035fcc0b40c14017fc6c95084600ffa220a8c67005fb9b160a448027fc5cb4a99401bfc546aa60600f7d28344445005ef8b94ca668037f888554a8c01eee6058291200cefcaa54a65007fb152846448023fed9152b1c011ffaeca94c600fed2a4902a30047fdb52a5638023fe5cd54c0c017fc6e11054600cfdc4454aa3006fda33aa9718027fcd8952c14019fe4c0a954600dfd305552650063fe882a5218037ecd0262994017fc6c13284600dfb466d2ac10057bdb42a582803df8c0b04a8c01fdc54d52846008ff972d1a430047fdb52a5328027fd5db46a8c013fe6e0a95c6009ff36355305006fe8a988963802fec5cb0519c01fd988a55846009ff57654a63004ff9b32a5828027fcda95298c01fda5422254600bfe364c2c23004ff9b22a563803df8c030b08c017be2e55399a009ff174c12a3006bfa882a532802fdd5da43224019df954a960600cef9532aac5007bba88551428023fe5cb44a8c01bf64c4a94ca00f6f4ab44283006f7a5568d60803fb8a8aa4884013fe2e6aa4ca009ff362d1b05005ff2bb4c521802ff45cb03114017fc6c185846008ffb7054a43007fe1204c5218037f555264c1401efa4428888a00f7548944445007bd28884633803fe11142319c011ef6d0a960a00fd9467114cd007bca33a2222803f992ac23224011fe2e5a550600fe54ab11489007fa21188a448027dcda152c14013be6daaa60600 else 0x1afe604a960a00dfe422d2a850047fdb32a5218027fc5cd54c0c017f62e5818ce00bfb57698a65006fea22695608037ec9855498c01fea60622912008ffb7054a630063fe882a531803ff0c0423114013fe6e0a94ca00d7f30355305006ff18168d51802ff4dc22111401afe60aaa60600df736854b05006f7a552a521802b7e5ca65334011ff2e5a558e009ff36654a43004ff8b968d518035fcc0554c0c019f78cca95c600f77510a0a85005fe8b954e22802f7c5cac4b1c01ef6601818ce00ffa30298a65005fbabb546448027fcda952b1c01efc609814c600d7f510d0a65007be9814c982803f6ca846733401fda54d8588a009ff36454a630047fcb968d51803f75112cab0401fec6161191200bf7576c0c89005fe9b54c982802bfa5ca6508c017fc2e58384600f7d300c0c45007be98254981803fb4884ab114011ff6cca960a009ff172d42e3007fc93054e228037ed19b50b8c013fe6e98048600dfd444d1ac1004ff9b3aa951802f7cd9aa133401bfcaa93148600fed4452aac1006fda332a5718035fd44342a1401ef6605828ce00fed3012ac45007fd15284633803f749844533401ef98468888a00ff922111467007f5a5548633803f75112c6b04017fa6cd5088a00bfd576a8c450057f8b96a120803fad2ac66b04013fe6e0a94c6009ff36654ae3005fe9b161622803f6719c45334013fe6d4a94ca009ff360d1a43006f7a55aa9418037ec98346a8c017f66c1828ce00fed2612ac450047fdb32a5818027fc5d2a690401ff2481218ce00fcf4aab1ac10047fdb22a5518023fe5cb42c14015bf2e55299a00bfb576c1467004ff9b32a551802f7d5daa7334013fe2e5a14ca009ff174902a3006ff131aa9818037ed19952a8c01ff24c13188a009ff172d2ac7006f7a55689638033fb08952c1401efca221150a00fee2612ac23004ff8b9aa9218027fcdc55498c01bfc844a94ca008ffb6454a63007ee95388a66803f3ca9aa5334019ef6d0a960a00dfb466d12c1006ff1512a581803fe511466b04013fe2e6aa4c600ffc2a490423005fdabb486338027fcda952b14013fe6e0a9486008ffb6a54b030057dcb958a33803fe8a842319c0177e2e5875c600ffc2a108c45007e7a55589638027fcd955498c01bfa888a94c600def4aa54a63004ff8b968963803bf888152a8c017be6d53299a009ff576d1b050067ee222a5818027fcd9952b1401afea22aa50a008ff972d12c7007bf18260e118037f490344a8c017fcaed8584600ffc26108c45006fda332a5628033ee9895299401fba5492099a00fdb466b2ac1007e5e558ce66803f3c984ab334017faaed8188a00cefcaa54ac70047fdb52a562802ff4d830b114017f66c1218ce009ff57654b05004ffabb2a551803df498d1111401ff84c58188a00bfb17290c670067f8a9) else (if i<3 then 0x41553050057fcb9689818033fe5cb46a8c01bfe4caaa54600ff730aa0a85006ff9a8691218037fcd1b5088401fb78cd6558a00ffe37098a43006ff951681828037fcc1554a0c01ff66e1314ca00dff340d2a63007fd9528cd608037fcd134ac0c01bfe609a354600dff576d12a3006ff9a3685208037fcc2d5499401bfe6d5a14ca00bff370d1a43006ff9b169532803fec9834498c017feaed524c600dff374a9283007fe9b1602228033fe54b4e98c01affa22aa5c600ffb466a9221006ff98169542802ffcd834a90c01bfe681a24c6009ffd76d2a65007f795254d108033fe5cd54c14019ff608a954600bfdb62c1c45006ff9ba54163802bfe5cb4a98c017fe6c5824c200ffd240d42430077f8b9685308037fc90346a8c01bfe2a5854ca00fdf2a4984cd004ffdb568d218037fcd2b4c904017feaeda64ca00fef4aad1a41007ff131541218037fcd134a88401bfe4c1a558a00dff36ad1261007fea2261541802bfed9952a8c01fee505a460a00ffb466d1221007ff13168981802ffcdc34a88401efe609a84c600ff7302aa285007ff211689308037fcdd30aa0c01fee6c98191200bff17355305005ff9b5689318037fc98952c14017fe6e1305c600dfdc45552c70057fcb968d51803fecd2a6299401bfeaa95048600bff364a82c7007f6e55889638037fcd030a90c01bfe68ca954600ffc422a9c45004ff9ba61521803fe908b0519c01f9e4ca5599a00dfd24155243007fd13054e11803fe898b02984017f6aed818ce00bdf576a94cd0057ecb960e228033f711152b1c013feaeda054600fdb2a6984cd0067f5512a5818037f908b46c1401bf64c6aa4ca00bfe576a94230057f4b954e118027fc5cb46c1401bfc844a960a009ff365552a3005fb9b42a582803fb8a8aa4c0c01efa4c28888a00ffa30108c67006bfa882a521802ff4d8263114011ff2e6aa60a00d7f510d2a850067f9a02a531803fd8c0aa3224015f72e5828ce00fee2652ac23007fd13148530803eed19b0eb8c01bfa889a354600aff172d1a21007f7142956118037f8c0d54a8c013fe2e93148200ff52a3114890047fdb32a551803fe4a844519c01fec8455450a00bfd576c2c450047febb2a582803fb52ac44b1c01bfa889a054600adf972a9ccd004ffabb685328027fcd9346a8c011ff6cca95c6008ff973552a3007be980616228027fd5db40c14013fe6d6aa4c600bfd360c1c45007ed9208ce668027fcd9b40a8c013fe6cca960600def4ab55285007e7920956668033bf2a95290c01bfc846aa50a00aff172d22a3006f7a552a563802ff95db0708c011ff6d4a948600feac672ac23004ff9ba60930803de719d1111401bf68cda0546008ffb7054a65004ff9b22a5518023ff5d952a8c015fb2e53188a009ff364d02a3004ff9b3aa982803fe4c044519c else 0x2802bfe5caa690c01bfb60aaa4ca00ffe302d22a3007fda336a1208037fc54aa6b1401bfe6818348600fef3052aa83007fe9b5481218037fc54b0a90c01ffa6022254600ffe2a2c0a41007fd93069d31803fed19b4a88401ffa54d1088a00dff342c1261006ff9a4aa9518037fcdc344a8c01bfd6a13148600dfbc67552c5007f7a55691218037fc98554b1401ffc441a354600bff576a8a85007fe9504c622802bfe5cb4ec0c01ffa481a254600dff36254b05007fe95268582803ff8d9aa108c01fde955a24c200fdf172a9ccd006ff952aa9418037fca9952c0c01ff66c1828ce00f7f30688305007fe95268520803f7cdb2a6b14017bf6d53299a00f7bd1090c67007fe58254a11803df6c12a4c0c01ffa4815260600dff346d3a21007fd55284633803ff8982a508c01ffa54d8088a00ffe262c0a41006ff9ba54d62803feb08b0519c019ff60ca95c600bff360d12a3006ff9a16a132803ff8a8b4488401bfe689a360600f7f300d2b03006ff9322a551802ffd5daa4b0401fbe5416258e00d7fb0555303006ff581aa9518037fcd434290401ff66d5218ce00dff340d2b03007ff11068951802ffd5db5098c01fbe6d53299a00ffe2a2c0a85005ffabb69d318037fcd1346a8c01bfe60eaa5c600dff34ad1261007bed31a2222802bfe5cb44a8c01efea20a94c600bfed76a9423007fd53160532803ff4c1264a8c01bfe541a348600bff366d0a41006ff9a069d318037fcd2b42904017fe6cda244200bff576d2a41007ff2112a5828037fcdc15298c019ff2e5a160a00bff36ad1261006ff9a5685828037fcd434e98c013ffaeda254600defcab552c5007fb952606448037fcd0b48c14017feaeda744200cff972d12a3007fe952481638033fea9952b1401bfe6cda844200bff360d0a65006ff9b068d21803f7ca92c6b04017bfaed3299a00bff364d2a21007ef9b3482668037fc98d54c1401fde545a548200ffd444d1aa3005ff9b068d51803fbcd2aa498c01ffc845a060a00ffe2a2d1a21007bf98269181803dfcc0344c0c01fdd54d8584600bff172d2a63006ff980aa9218037fcda342c14017feaeda54ca00fef4aad4265006ff9b0695328037fcd426488401bfe6cda060a00cffb6a54a63007f5e5558a33802ffd5daa6b0401efea21a244200ffe302d12a3004ffebb68d82803ff4d2a64c1401ff654d214c200ffe302d1aa3006ff9a7aa931803ff8dc24108c01bfe2e6aa60a00fedaa6c2c45007fd93069531803dfb4426508c01bfe6e9305c600dff36e54a63007fda3360520803ff8d826290c01bfe6c9a844200dff2a0d12c70067fd512a532802ffcd9152a8c01fbe6c15299a00bff576a9a21007f7a55601218037fcd934298401ffc4c5a048600ffd444d22a3007ff18254211802bfeda95298c017feaeda848600dff3)) else (if i<6 then (if i<5 then 0xb4c65588a00bff576a9ac5007bf98268181803ff8c02a708c019ff6dca94c600dff350d1263007fda3369520802ffc5cb5090c01bfe682aa4c600bff366a8243006ff982aa931803ff8a8b40c0c01bfe2a5524c600bfbd7690c67005ff9b068d21803fbac14ab08c017fe2e6aa4c600ffb262d4265006ff9b76a110803f7cd92a1334013ff6caaa4c600bff576a9a41007fe9b54c982803ff51134c984015ff2e5a74c600ffb466a82c5006ff9a869531802ffd5db44c0c01bfe681a360600ffb466d4221006ff9a3549108033fe5cb4a99401bfe6a0a94c600ffd2a4d1a41005ff9b068d81802ffb5da6290c01ffa4815348600dff2a254b05007ef9b548266802ffcdab5099401efea21a448600dff347552a30067fd832a521803ff8c0a64a8c01fde955a64c200dff30b55283006ff981aa932803fbaa9aa508c01fb754a3399a00bff576d2243007fd930aa9318037fcdab42c1401affa22aa48600ffe2a288305007ef930595628037f699554c1401ffa889a054600dff340d2a43007ff18168151803ff511554a8c01bfe6e9835c600ffe360a9c23005ff9b1691828037fb55262c0c017fe6c98550600bff36254b05007ff1a54c521803fed19d54a8c01df72e5518ce00bff374c1a410077f8b954530802ffc5cb5098c017feaeda344200aff972d4243007ef93259560803fbaa8aa4c0c01bfe681a360a00dff350a8243006ff9a3699208037fcd2b0090c01ffc6d53148600fef4aa902c7007fe9b054e22803fbd2ab4298401ffc6c98584600ffe36098b03006ff9a054981803fed19b40c0c01bfe4c2aa5c600dff350d1221006ff9516a1428037fcd2b4c99401ffa4c18588a00ffe422c1261007ff1812a531802ffcdd24298401bfe2e6aa4c600dff307552430077f8b968d10803dfac0b04a8c01bfe542aa4ca00ffb30090c67007fe9b3606228027fed8d54c14019ff6c4a960a00dff26454b03006ff9b868530802ffd5daa690c015ff2e5a548600dff340d1303007ff131695818035ff4434690c01bfe688a954600fedb032ac45005ff8b954d21803ff5112a0b1c017f7aed518ce00aff972a9ac5007ef9b3542668037fcdd260b1401ff654d3058a00fef4aad02650077f8b96a120803dfac1262c0c01bfe689a454600fef4aad4241007fe95388960802ffcda95298c01bfe6d5a14c200bff364a8a61007ff18168931802ffcdab4690c017fe2e5a760600febcaa90c67007ff130616118033fe54b46a8c01bfe604a94ca00dff34b55263006ff9a069d81803fed19b4ec0c01bfe685a360a00dff261552430057fcb968d81802ffd5db0290401bfe6c9a354600dff2a4d1ac1005ff8b969932803dfcc1346c0c017fe6c1a260600dff172d12a3005ffabb61542802ffc5cb4e98c01bfe481a558e00bff576c1261007fe9b84422 else 0x303007fe9526a1208033fe54b4a98c017fe6cca954600f7f300d3b03005ff9b068931802ffcd834a99401bfe60ca948600dff368d12a30067fda12a5828037fcd1b5090401ff954e1188a00dff2a654a43007f7a5569920802ffc5cb44c0c01bfe681a254600ffd304d0a65006ff611aa9828037fcc2b4299401ffc6d58284600aff972d3265006ff9a1aa982803ff2c2c2311401efea215048600dff30b55285007fb9b254644803fed19aa090c01ffa6c58588a00ffd2a6c0c45007ff13154981803bbf2a95298c017fe6e0a94c600cff952d12a3005ffabb60530802fef5db0319c01ffc545a360600ffcb0298c45005feebb54e22802ffb5da62c0c01cffa20a94c600bff366d2a41005ffabb60532803ff8a8b5088401efb609814ca00dff374a9a43005fddb2546338035fec0d54c1401efea21a544200ffb262d0265007ff1b04ca118037fcd0952c1401ffa6e15188a00bff576d2b03005ffabb4c5208037fcdd240b1c01fde955a460600bff362c2a85006ff9a06a131802ffb5daa708c01bfe442aa60a00bff576d32410057fcb9aa931802ffd5da64b0401ffc6c95084600dff34ad42430057fcb960d218037fcd1b4488401ffa4418388a00bfdd76c1c45006ff9a168182803ff89930b08c019ff4c8a960600bff576d3261005ff8b94c951802bfedc15298c01ff6481518ce00dff366d0b05005ff9b160d208037fcd2554c1401ffa481a348600ffe36a90423007fd9b54c532803feca9b4298401fbe6d92058e00bfbd76c1467006fdd31aa932803fec98b0498401bfe68d5260600ffe366a9423006ff952aa963803dfd44260b8c01fee6d58191200dff345552a3007f7a554c960802ffc5cb4ac0c01bfeaeda160a00fcfaa6a94cd006ff9a569121802ffcd835090c01bfeaa98548600cff952c2a43005ffabb68951803fe6a9b0711401efea21a348600f7bc67442e3007ff153482118037fc90554a8c01bfe6e95150a00dff370d2a65005ffabb60542803dfcc0b46c1401ffa6cd8088a00dff2a7552c5005ff6bb605518037fcc1554a8c013ffaeda354600ffd304a9283007fb9b548644803fbca9aa4b0401bfe6e95358200bff360d2a63006fee2268d51803fdcdc24322401ffc605a54c600bff576d0a61005ff9b72a531802ffadaa6508c01bfe681a84ca00ffb220c1467007fd931615328037fca8b46c1401bdf956aa58e00dff374c0a85005ffabb60d20803ff898b0090c019ff4c4a960a00ffb2a6d3261006f7e5568963803ff4d830311401bfe6e1a24c200cff97355263006ff8b9695328037fca8d54a1401ff3606228ce00f7f510d1263005ffabb691818037fca8554b1401ffa481a548600ffb466c02e3006ff9b0689518037fcdc342994017feaed3244200cffaa654b03007f7a5568d218037fc54b4e98c01fd) else (if i<7 then 0xfdd22554a8c01ffa6cd1088a00ffd260c0c450077f5812a551802ffd5db42c1401bfe6e9805c600bff362d1b05006ff980aa9718037fc98b40c1401ff96093284600bff172c1ae3005feebb60622802ffcd835099401bfeaeda14c200dff576d2a65007fe98254931803f7cd82a733401f9f4ca5599a00dff576d4221007bfa88681218037fcd1b4ec0c01bfe441a360a00ffb362c1467006ff9b368951802ffc5caa6b1401fde955a148200dff34ad3261005ffabb691518037fca8d5499401fee6d15150a00dff34ad2303007fe9824c9108033fedc15298c015ff6dca94c600ffd262c2c45007ff15168981802bfe5cb4ac0c01dfe2e5a454600dff2a454ac7007fe92060d21803dfcc02a6c0c01bfe2a5835c600f7f510d1261005ffabb68d518037fcd2b4690c01bfe4c9a558200f7f302d0305005ffabb54963802ffcd834c99401ff3889518ce00ffb466d3a21006ff9b2681518037fd5db44984017feaeda848200dff362d1261006ff9a269181803ff8d82a508c017fd6c98584600f7f510d3a21005ff9b868931802ffc5cb46c0c01bfe6d5a844200feea652ac23006ff9a869520803fbd2aa64884017bfaed5399a00ffb2a6d1261007ff18054a118037fca8554b1c01ffc6161150a00ff7362c14890057fcb969532803fec98b4498401ef7605828ce00bff172d2a43004ffdb168d82802bfe5cb42c14013ffaeda160a00dff554a9303006ff9b8681218033fec115298c013ff6d6aa4c600affb6454aa3006ff98568542803ff8d9a4108c01ffa889a544200fddaa7114cd007fda3368520803ff4d826311401ffc8458348200bff370d2243007e7e5558963803fbd2ab4c99401bfe695a14ca00cffb6654aa3007ef932542668037fcc115298c017fe6c1a760600bff576c12830067fd812a532802feed8b0519c01bfe6e95258e00dff340d2a65006ff9ba60532802ffd5db46904013ff2e93160a00bff172d2a65007fba44aa9828037fcdb34a99401bfe482aa58e00dff36ed0a61005ffabb68d81803ff8a9b0508c01ff68cda648200fbf36ec02e3006ff9b32a5518037fcd8b46c1401bfe6a2aa4c600dfbc66d2ac5006ff9a060532803fec98346a8c01ffc606aa54600bff374c1261005ff9b16a132803dfcc134ac0c01ffc606aa4c600dff34ad4265007efabb54e668037fcc1152a8c01ffc6a13148600ffd36690243006ff9a068d21803ff908b46c1401bfe609a550600bff364d1aa3007f7a5568910803bfac095298c017fe6d53258200ffe2a299221005ff9b3541628033fe54aa4c0c017feaed5244200ffb2a6c1a41006ff9a8695108033fea9152b1c01ffc846aa60a00ffd360c1c45007ff1812a551803bfb08952c14015ff2e5835c600dff344d3261007ef9b54c266803dfd4455498c01ffc5413284600ffe262d0 else (if i<8 then 0xa460a00ffb260a9b03007fd9306a1318037fd5db46a8c017fe6e9514c200dff304d02a3005ff9b360121802ffd5db4ec0c01bfe689514c200ffd2a4d3241005ff9b5685328027ff5db4690c017feaeda54c600dff300d1a43006ff9a068d518037fcd42a690c01bfe4c2aa54600f7f302c1261006ff9b3681518037fcdd30090c01fee6152191200f7f510d0a61006ff95368960802ffcdc344a8c017fe6cda544200dff172d0b050067fd322a551803ff8c0aa298401dfb888a954600dff360d0b05007fda3368121803ff8c026508c017fe6c1a560600fdf360994cd0057fcb954963803fed19b40a8c01fde9553058a00dff346d2a41006f7e55aa932803dfcd430290401ffa5418188a00bff366d2b03005ff8b968d518037fcdd304a8c01bfe695a24c600fdf364a9ccd006ff9a868d21803dfd44346884017fe6c1a84c600ffd30098c45005ffabb69182803f7cd9aa5334017fe6cda844200dff36cd1261007fd55360e11803feca8b0519c01bfeaa9524c600ffe422d2305006ff9b068d518037fcd034299401ffa5418388a00dff36a54a63005ff8b968951803ff4c134099401bfe6895344200ffb306a9a21006ff951aa9828037fd5db40c1401bfe681a64ca00bff576d1261006ff9b368121802fef5da62994017feaeda844200ffb364c0c67005ff9b54c910802ffc5caa4b1c01efb5468888a00ffd444d0a61004ffdb8aa931803ff4a930690401bfe6c8a954600cffb6454aa3005ff9b5685208037bf2ad5490c01bfe6a1a744200dfeb02d1aa3007ff15169181802ffb5da6508c01efd60e1160a00ffcb0708c45007ff131685828037fcd42a688401bfe6c5a060a00dfea6355243006ff9a52a531802bfe5caa6c0c01ff95458188a00bdfd76a94cd005feebb4c622803f7ca9a4133401bfe6e95260600dfec22d1b05007bfa8869531803ff898b4ec0c01ff66c1314ca00ffe262c2a43007bfa8854542803fe6c126299401efea21a74c600bff576c1ae3007f798195542803dfcc0952c1401fde954a94c600f7f510d0a41004ffdba61521803fdca8b0522401ffc605a74c600ffd304a9221005ff9b868910802ffcdc342904017feaed5250600dff36ad0243005ff9b161532802ffc5cb42c1401fbe6c93099a00dfdc44d2ac7007fea2254530803ff511348c0c01ff5605518ce00bff362d0305005ffabb615418037ef19d54b8c01bfb609a54ca00ffb2a4c0c67005ffabb695218037fc54aa4c0c01cff604a960a00dfdc45552a3006ff9ba61521803fecd1a62904019ff544a960a00dff360d1b05006ff9a369510803dfca9510a0c01efe601a360600dff374a82c50067fd532a5218037fc99340a8c01fbe6d95358200fef4aad0243006ff953aa921802bfed8952c14017fb6c58588a00defcaad1a43007f79504c951803 else 0x322b31e431a83161314630ff30ad307c30402ff92fd32f812f242ee82ec22e862e552e032dd22d8b2d5a2d132ccc2c852c542c0d2bd12bab2b592b122aec2abb2a952a592a332a0229dc29952964291d28d628a5285e281727e627b5276e272726eb26a4265d261625f025ca25992568250b24c4247d2441241023c923a32372232b22e42292222a21f921c8218c214520fe20d820912055200e1fc71f801f391f131eed1ebc1e6a1e0d1dd11dab1d591d121ce11c9a1c481be01b991b471b161ae51abf1a781a1b19d41998195c191518c31871182a17f917d317a21766172a16e316a71676162415e815a11544151e14d71490146a1439141313c1137a131d12f712d1128a1264121d11f711a5115e114310fc10d610a5107410430ffc0fb50f630f1c0ebf0e620e310df50dcf0d930d620d3c0d160ce50ca90c6d0c1b0bdf0bb90b720b200ae40aa80a610a3b09ff09b809870956091a08e908a20871083507ee07bd07a20771074b071a06d30681065b060905cd0591054a050e04dd04b70470043403ed03bc0375032302dc028a024e01fc01aa0163012700d5008300470000dffa63553050077fd512a5828037fea9b42c1401bff546aa4ca00f7fb04a9b03005ffebb69932802fff5da62c1401bffaa95260600bffb62d4265005ffebb60d71802fff5daa690c01bff685a360a00ffba62d2a65006ffdb168d82803ff699342c1401bff6e98348600bffd76c0a650077fd822a551803dfec0b46c1401bff695a84ca00bffb6ad0b05005ffebb60d218037fed0b5099401bffaa9814ca00dffb4ac1a43007ff531685828037fea8b46c14017ffaeda54ca00bffd76a9b03007fed824c951803feea9b0690c01bff695a160a00dffb07552e3007ff531549818037fec1554a8c01ffb549a160a00dffb04d1aa3005ffdb568532803bfe5caa690c01eff606aa60a00effa6454aa3007ff53161521803ff6c1342994017ffaed5258e00dffb46c2a43006ffd83aa9218037fea9554b1c01bffaa98548600fbfb0ed3a63006ffd53aa9628037fed2b4299401bffaa95360600eff972a9ac5005ffebb54d62803dfec1b42c1401ff74c5a84ca00bffb6ad3265007ff551605328037fea9d5490c01bff686aa60a00dffa65552a3006ffda569932803ff6c134a99401bff68d5260600bffd76d0b05006ffd51aa982802ffed8b46c1401ff6615218ce009ffb6755305007f7950689518037fc5cb46a8c01ffc5498384600dff340d4243006ff9a868951803dfcc0d54c1401ffa4c9a060a00dff350d12610076fcb954e66803ff511152a8c01bfe606aa50a00dff346d2b03007fe9b848121803fed19952a8c015ff2e6aa60a00ffd34299305005ff9b068d82803ff49030a90c01bfe695a14c200aff972d42630067fca96a1318037fcd0b4498401efe605)))) else (if i<13 then (if i<11 then (if i<10 then 0x8558853d85228512850d84fd84ed84d284ac849c8481846684408430841583fa83ea83c483a98399837e834d833282f682db82b5828f8269824e82338223820881f881dd81b7819c8176815b812a810f80f480d980be80a3807d8062804780217ffb7feb7fd07f947f6e7f537f2d7f077ed67eb07e8a7e6f7e5f7e447e297e0e7ddd7d6a7d5a7d3f7d247d147d047cd37cb87ca87c8d7c727c577c317c217c067beb7bd07bb57b8f7b747b597b3e7b2e7b137aed7ab17a8b7a7b7a4a7a3a7a147a0479e979c379b37982795c794178d978c978ae7893786d78527837781177f677f177d677bb77ab779b7775775a7734770376d276c2769c768c76667656761a760a75fa75df75cf75a97599757375587548752d751274f774dc74c174a6745f74447429740e73e873d873bd73a273927356733b7320730572df72b9729e7278725d724d7227720c71fc71d671bb71957185716a71447129710370dd70c27091708170667035701a6fff6fd96fb36f986f726f576f476f376f116ef66ed06eaa6e586e276e016ddb6dc06d8f6d746d226cfc6ce16cc66cab6c856c6a6c4f6c346c196c096bee6bd36bce6bb36b986b726b416b316b166afb6ad56ac56a9f6a796a5e6a386a286a0269e769cc6985696a694f69346919690968f968c868b868a8688d687d68626847682c680667eb67d067b5678f677f675967496739672966f866d266b7667b6655662f661465f965d365ad6592657765516536651b64f564cf64b464836468644d643d6422640763f763d163c163a663806365634a631962fe62e362916276625061f361d861b2616b6145612a610f60f460e460be608d606760416026600b5ff05fbf5f995f7e5f4d5f325f175ef15ed65ec65eab5e855e6a5e4f5e295e195dfe5dd85dbd5d8c5d715d565d255d0a5cef5cdf5c985c515c0a5bc35ba85b775b3b5b0a5ace5aa85a775a3059f459ad5971594b592558de58ad5866582a57f957c85781573a571456cd56705634560e55dd55a1555a551354cc5485546a542353f253ab5359530752c05279524851f651a45168512150da509e50574fef4fbe4f824f3b4ee94ea24e664e354e0f4dbd4d974d714d1f4cf94cd34c8c4c454bfe4bb74b7b4b344af84aa64a754a3949f249ab4985493e490248c6489548644828480247bb4769471746d046aa466e464845f645d045aa45844553450c44e644aa448f445e441743d043aa436e433242eb42ba427e4242420641bf41994168411640e5409340574031400b3fe53fa93f783f313eea3eae3e7d3e413e053dbe3d773d303d0a3cc33c923c563c303be93ba23b5b3b143acd3a863a4a3a0339bc398b394438fd38cc3885383e380d37c637a0376f372836e1369a365e362235e635943537350634bf3483343c340b33c433a9336d333132f532c4327d else 0xc31fc304c2dec2adc287c256c23bc1ffc1d9c1bec1a3c17dc157c13cc12cc111c101c0e6c0b5c09ac07fc064c012bff7bfe7bfd7bfc7bfb7bfa7bf97bf50bf4bbf25beffbed9bebebea3be93be78be5dbe42be32be17be07bdecbddcbdb6bd9bbd80bd65bd4abd3abd14bd04bcf4bcd9bcc9bcb9bc9ebc83bc68bc4dbc27bbf6bbdbbbb5bb9abb8abb6fbb54bb2ebb08bae2babcba80ba65ba55ba2fba14b9f9b9deb9adb992b977b95cb94cb93cb916b906b8f6b8e6b894b863b848b82db828b80db7f2b7e2b7c7b7acb791b776b72fb71fb6f9b6d3b6c3b6b3b698b65cb657b631b616b5fbb5ebb5c5b5b5b58fb57fb559b528b50db4fdb4ccb4b1b48bb470b434b40eb3e8b3cdb3a7b376b35bb340b304b2e9b2ceb2a8b28db267b220b205b1eab1dab1bfb18eb168b14db132b117b0fcb0d6b0b0b08ab06fb054b02eb013aff8afd2afb7af9caf6baf3aaf1faf0faeffaeceaebeae98ae7dae6dae52ae2cae11adebadc5adaaad8fad5ead43ad1dace1acd1acb6ac7aac5fac44ac29ac03abe8abc2ab9cab81ab5bab40ab1aaaf4aaceaab3aaa3aa7daa62aa3caa16a9fba9e0a9c5a9aaa98fa969a959a93ea92ea908a8e2a8c7a8a1a886a876a850a81fa804a7f4a7b8a792a74ba725a715a6e4a6b3a682a65ca641a631a616a5fba5e0a5d0a5aaa584a574a559a533a523a513a4f8a4d2a496a47ba460a43aa42aa40fa3bda3ada392a377a351a336a2faa2f5a2daa2b4a2a4a294a279a253a22da21da202a1e7a1cca1b1a196a17ba160a145a12aa104a0e9a0d9a0b3a098a07da057a031a0169fe59fa99f839f689f4d9f119ef69ee69ecb9ebb9e8a9e649e499e2e9e1e9e039de89db79d9c9d819d669d4b9d3b9d2b9cfa9cdf9cc49cb49c999c7e9c6e9c5e9c439c289c189bf29bd79bbc9bac9b869b769b669b569b3b9b209b059aea9ac49a9e9a839a5d9a2c9a0699e099c599aa9984995e991798fc98d698c698b6989b988b987b986b982f981497f997e997b89792976c9746972b96ef96c996ae96889657963c962c9611960195f195c0959a958a955995549539951394f894e894cd94b2948c9466944b943b941593ef93d493ae9388936d93529337931c92eb92ba929f9284925e922291fc91e191d191b691a6918b91709155912f911f910490de90c3909d906c905190419026900b8ff08fca8fba8f9f8f6e8f538f388f1d8f0d8ef28ed78ebc8ea18e868e6b8e248dfe8dd88dbd8d978d5b8d408d1a8cff8cef8cbe8c988c7d8c628c528c428c278beb8bdb8bcb8bb08b8a8b648b548b2e8b138af88ae88ad88ab28a978a718a568a3b8a208a1089ea89da89bf89a4895d8937891c890188d088b5889a885e8838881d87f787d187c1879b878087708755873a871f870486f486d986a8868d8672864c862685f585da85b485998573) else (if i<12 then 0xa0981701303e00660806302e03a005c04c03020370305600c1302d07c04c0cd40f00000a0b81c09304390ba0b81c95300019408e00f01307079400071b0250020ac0c9811815071e026018148f9281e05804c12141703818a0b40d801481e0002341303d023707a06c000d00e2802c0740207100c5006078141160702c7a0a08f02602600560640282e07025410c47d82107a0780b02d00c028a06800168c07e04c0e02e81b003307a0649702b00608660a0300c8e0a007a0102c9814800191d0560780008b04c0ec08f01f01403c09401829982f0304780b0203ea00059001e8040e1e0560047c7c1282e07e06c0b801b0250060a323ec1302d0022540cc41681b001b05a0580013504c0f824e03f0260701740d80198180b150224ac030230560e6c05814860d80205c0604c98028260760a481e00e8040c230460580282e0760660074030283c608048d8178183b04b4001b819381c03e04f02d002086045c1002605a00c0c1c81242110540580603a6000e40d2005d0060580c8c100c605c07400ac1e1540e1b0504780b025002813c0b80d8391810180183005402070c06604a0ac00843302d0424b41cac1e81e00019068a43702602070400138183813031410816032e0560f4107c0b02b00c080dc0c9807b03a0002c1b822018700006302e03a0e500ec0b01d0001c5030c17020030180d8d41302a121828a09409800182f07e04c1302d03e006c0b400128192604c054000c1303818c0ac0e801682605406c00981582128a04046819801e05608048849702902a06c00b41f02e02a06039801a8100d0560608c0a060b00125c0e4388c0e8040b1803c04c0107130240460540e01c283707e0541302e03600058e0658280c1e04a0500b00303c0b81cf41d81e00819068a07c09e0040b410a8540680f00602c061982e04a0e09b01170250780a06498118010b1925a0540d8010cc0a660408e8002401c503806683c05408c00d41f014040304a04c0c0c604600c14dc1781b07c08c01065023f04e0141781e076046e05c0381d0560843b039f82f03c0980814178050460fc0f0290cc047e0bc0381e0460e832811e82f04e0581e08b033704e05816818282e09e0b41300702c0ec0cec1682702e07800876073f05e07813010282f0ae09c1f807030166d191d181d150d11fd0f9d0c8d0a2d07cd056d025cfffcfd9cfbecf98cf5ccf36cf10cedfcec4ce9ece83ce52ce21cde5cdb4cd99cd5dcd2ccd11cce0ccbacc94cc63cc27cc01cbe6cbaacb84cb5ecb38cb12cad6cabbca95ca6fca49ca18c9f2c9c1c990c96ac944c913c8edc8bcc8a1c870c83fc824c7f3c7cdc7b2c78cc75bc72ac6eec6c8c6b8c671c656c646c62bc61bc5f5c5dac5bfc599c57ec56ec548c517c4fcc4ecc4b0c48ac47ac45fc439c408c3e2c3bcc396c37bc360c32f else 0x360420443406505a066a0581100018250781980981e00c0a60298170381f605400c00b01b0701c460b81086d03019408dc0d83e05a0980b80180780b606030806683e05c08095801981c288223c0a41f01b00210520606282502c0e660b40d80125c08c1ccc1c15703a00110059807d03c00070119487100c0e412829683c076078020d1582018c07816800400447e0608e82e02c080f9800164602c0ac008f9303926a0940887018330703181701d00290420181681e02a0e6a0b811800192605a000340d504026660e02c4c1c0c605c07400a06483e04a0ac00a01303d03600068b41303b03834460b00c0cd00c09808d41602e03605803026073b02c0b40d8020e60e6006c000900e038503381d8100301810ccc16060b81703c0ac12800193504208c0302e0260ec0cf81701307a08420180b02037030580b8028240360f068d4018180b1d0780f80d82602c01814e85508b000540a302825c0e823e41302d00606524b81c870c03b03c05400071581023a000389c1c060166074001c80b3807a04c00871303b024194158030336056000a812930230241941580303350480981e03b038346c0ac130380004a064d81582500032480981f02b0304b400d81c01d04600068b80c8002d1d0460640302d07c05804f81283e0204c0380c198250081630078098380e230281b030600e82607072068b815825071e03c0a41180130290c24a3604c0d80505c08c1cc01f0150081c4a00c178101906e030c47c82602c0b401819983d03c010689c1283e05c04c0f801982300c0b40f013073103c08030859280303c0b0488c0f83e02a000f4071892d03033409806043125a0b410876072e04c0400e800110306c0b80c0150001804cd40980125c08c15839b02307a04300ec00870f02e0320004c800a8060381c4045c1c03d036018101c81a470260b4000c837018600ec0b01d00048038d81282c046070a0a00f0150081c4e05c0d83d05c09c00d82a144111d00084c100593025070540a2828183405a0901f003038346c0b40e01b02c01813039c0a41f01f0300060401781e81a41e6070340389400063030164a0806302e03600502d40182834c080dcc0780c80ba0ec01011981c1a824381ac1603813c09808dc1f82703017c00b41086602c0ac01819b01402a0781d8241a33072058168180ea006c084008d00ea0f40ccc12144111e0a855038606502e076044a0e40c86602c0b413049c07b0001740c1be04c0e089181282b0304b0a0b415000191912c0b41c9550201cc00ec0981e07a0ac01821881e05c04430801f81b04a00100059a8260040043b03b03604701a03e05c0e0074140ae04c0490320620210760b808d41202602c00c0f02e073b03031400071302602200060901683e041c07a0581201b05850602907e0700dc0604b02d044707)) else (if i<15 then (if i<14 then 0x303a005e0e05981d0007202cd80b0250784cc14ac140c80c1e0522447c641081300c0b40e839b026026000608c1601819a01813011809e05608048159480604c04060807c05d04c04460ac0d80604a04c1cd41581e0721cc0181180150081c303341c92d05c08c00c0900981806f813013000668c08c0a81c0e8505c0a4000c8f00607a06c0880a282502600060ac0a81813c0ac1183981420703241682600360580ac1e81402854680580e00605a0ec10c0440c8a81925c0ac0182307301340b80d81100a505c0811c0d019350460580023e0760ac0ce06018d00c0b80d838163d04c0e060873006066c0901182d038070a0c4170210724a4c0400e80011c080dc0c1e82404c00c0f02e07c047c07816804126085208c0302e02a0741cd417026070000940c998201ec0b41f019583802c060c68000e37070318170180e044c000b013492520540d801001819a01813011702e07000c0c128193018a0e40f0250201cc00ec0e83e02c0ac01821983818c0b80e80140a01f60e02c982606c0c1b07a0640f01605600c10e00e8040e1b0581b030605b82702c0b41e84e033b03c0b04878148f91218026060668003d01c6e09c0983e05a07c00c06303813a0940b001b82f0360f81281700350003181701b072f05e0740181018018660806302e03a005e0e0b40c03ca000a4159e82e046000648c1302d0002580cb81183e0204c0380c1982b03c0f41180302350060b810781201305a0603a141b81703a0006407150882a6000300d148a00760042c981282c07032460940f0000c8345c0ac01038d82e0044d41303b023605055c0e80302c0e058f05181002a0107f02e073d056060670230060466040300c0c0c30500b811011701d07604321741481e04a00031811d820040163c098080c0c01d0081c360180b0290c2022e0940f038390346a000380c8e83818c0b80d80158000b1007c07402071282c05c09011814283604a0e46a8180e6006c0e0380d0c85e07204c0282940580c80f81181148260008d81e82d033004c0ac0c09100c81860981c811682e04c0f09981140580c80941d82968390cc0581580303360460f408781582500032460006011605c0741c0b1d82503c0106894170020021d81d81b023e0ac0047f0390b2d07c04c0c6c030290c191400a448642e82e04600408a07c05e05a06460f40c92e04600c14dc1781e04c054000c1b02807a04c00151702107a06c00981583d020250a8b81411e04a01408b41e01b04c000320d1809e05008c1c0902b3307c0b80a8180ea006a0e064070d8220cc0540f006053007a0180e071282e04604096141703d0460a3c08c1d07503600c08cc0182505c0e849819981b00c0b413013073707e06c1702502e006c0ec0c0c504600c14cc0e80125c0f416821a83c076098020d170230723540c075 else 0x41c06c004034066001b00081c804c0007900a818c003216c08440819822a0f8168183a01cc0134002c0881080c502100f01cc006061800908a0d101fc0a03860398008040f000a82300150309110818c008006000098b01a036043605c0e83816240f81cc02001280040780e60036001027800060c0c87013002000e00b14098582858182513070c0cc010546c00207c08b03180ba002030140f40040380e0811a02160024c2a09400440f00088fa0be0f81681f003100c042206c1c4c1180088fd0360032001205800540c128a800583824c07402071401b001502030201c070480a8380e1a0220002c603280080880fc00380ec0054002c0b01d001b020382606160040c058e01b001018a040686c0c240f00080600ea06320ec104060076031c006060306c1d800980112026058940024008f8906703a040a4840b01880cb001019c00000741081b001b030382033800000c0982a15000b020e02042058640f000882c026063a0840d810c17814a09c1c0003d02c781f03980400210ba04c0c641501507182601c2c06c00178222500200201e03a80100c0ac0c189e8110260e36004004065800a00303110cc00400640f0008863071019030203e070541c2c00800a8201910008813130401c2404400058d83d022058008c0020780e0983b091023a060a87408340c81b00180c405800606183898183702c3a00101f800088e07504130204a2e0600c1980ee00060d41c060b00200130220420060644c082c002c1e81102c0046001a0014094004c0c340a058b0200c1304a04202603d800e0603715000562a0647c408c09e001c0e081960980060703400204c34000901902c40314080d0c000181602600400108162822600058604c066031c048002200c08441d005021c0f806c007810070809d001011c000347810070881b00121141ec0c680a8180e1818c06202603815603230703820460604c0c2c08810982d0310190819a0607c740c242d82880c83302c3829038504681880680b806c08840d800980019101402dc1702000c0e088e41f000819818048360e0c809b02a000c414e0346002222405400000f81102a06c00800163015025800640007080ca00101c6002030123ec0e800f02c0c04c088941481303181201d4087032838903d001503026202a03e01b002600400c0c70360888811070260588060838a07504160220e02c640b00080c8601b02140cc01054600b000a8110b101e038060741020a00c080a500060382503c44088381302c4a0a038404c0e080900f207400980b000811b0010130e04a0407182d07a066c0b81000028a0540ccc1681911c0f412811a81926c0b80982307330001c2c0a41e81b00202801681e816002903c0e030859304e0520f8088f95806042243a00c1302c122605c074000100c0266c0a41f01) else (if i<16 then 0xe83e026003a00400580006080580ca043016044098f8183440981e82f0035030062609800930e800681848280c110c0b050b02082503404f01503281c0322a000445424203406102c004a04409800e83e002003026061800c0880e10136000a0170162811019800647d820a81102606301d811800342307038203012000604c142430203182500068401a044090c0c84818120860588060f80840708160018000302032123ec0c58100c8b0010302a301c071028c80018100c0e00800800607c075031d0323e202403d818e0a40ea003a0442c4010158a07c0c160260020300380d602250460e41f0010803031102600204a03a818e83d02044c010714075040543207800541c380f00080e040e0131003c00260540c402c066001818081860e201cc0c078f0180b101303180c60028383d02c42078004c0c241f000b0001213002002a0ec02000d810581102100da0a04f001280019160024c26000604060281281880c303141281e240f40840700c0903d00102803181280034062602440c0a8e07b008003a0442c4061816001a15422064170162d036002019800068d813001504081a02204a84900780e6003200038503a0a0b01858104098191304062c0e8040b2d0708190b07600201f40c070d8220201c320016060cc0b0d81019141fa0626001600101d400800c0c818160220602c607e818880019130020026001026064140c0c0581b01111f6082033c0b8180002c0b8c08c0e6001a0201828254244c008003302c481f038440d81080d018a0803b0115801070163817408407c065031d030580886c082031818261900c0420321600800406280088fb0313032062a00100e04c403b025000684c0680c504a848806811c003016031810e8230720f8008c1180080880ca00300e0645809013031c0081c2a00400500d800a8004140c204c3016018902002c0636001a00048541c058806e00060360a120e0385016018980040c60000030268004c00341c1409801000420589802000a82707c040f40b15800181013405400741481307181e407400701c0c8a0940f13000e0082a26081c04048407d015031e02816202a039800d8101c101380f80006908130311256002c0105454000c880ce001215422c0060600c880b5071707c06058604c06300190e0d022162e07c001301802c560a0d01c8c065001600400c08608c075031b002000bc0b120130001c3c0441c058d80400102b0b02600201cc00504a078a82d03c00400808b02507c040380d5030758158029838502d001500200281810301031c0e8381621006082a04142283c54000c8981e00101520780060642c0c818b013001504a00224ac0040f409816180c60420060645404070a808582818101501cc00780980100068058a0730000b1b04081f01f00181918005011040163c else (if i<17 then 0x1038440d810b01b02a0e058840c0588800191207a0026001030104680b000d82840c86800681b0040002f02e040487a04c0c81e00210023e22000644040540c4c02000a81848380b1604018240f40c5032068b81816408c081a7003504081801d80c6835063021b050d000c0ea0a2a040301201102c50504604408640f0008816001505081f0238006c0c2030815031b00090ca00454780a0140081e485180054242c0a81903c004005400403408e001c1481c2031c14016070445217409818c09d03054301740c5812800341e05c06c02001281825100c03820620630160406e5030c004c1c098906a11606320002c481401d00182460ec081150081c6019400408d010a0704118191305c094001a128160022236010004c01000a02c03101960e2217409800e8001302c301d4140d0e800251602004201cc000a0c0cd001102c002028039800c8010b130020020260641460020230180aa81928190313000b00081e03404c0592070483d0101c3030c004c142c1f01880730001e381d414440e848121826a00044604c0c89000131103a004000590816001302068058645280033032058a064240c058b013002000f00b140b100101260626008004c0100100180e60028198020a8c11819a0e3606064403c066001b0520a202403e818c82b002003a0b40e800e075031304081c050030607a81080cb05c003405400070e8191f160024c281d40c4c08810b013001502204c0c6c00240a818a060683e00200301840c0a8e8191f101201ec0068350609828487b000583019800828152104c0026001e0600e0901102c5c08c001a0c1100fc0409006816301f01740c6c08206280034080404c0641102e250020e0ac11101280dc003218c1c540c2c1d800a0750510196002824120e40a800e07c076003a04160606440f409816190c08190903c042031800088c06302c094001a17001111202a062a0640d800e81041400c1022a0fc0c1502806c0b8ec003012010981301101260003c6c1185080d019a0e0630114103a82881281e406360e160a100410c503d804261a00017408604c201409880c6001502204260803840140c898181811072062031400441c0708066050223600064541c20630000d1e03006281d41054000c816180fc00114780100080780ea00400941c19b00a0682ca07c09e001903c00260404c580809303a000ccb012010889068001311000814c084481c91005020183a004545016038886048380b130320626010480c8162500026220002c4c0080098000c10190b0a0a02c094001a108130713076002032181d4145809800a82040c8580400101960626061c08c001a0c028361302600281c101a033000d8206070582868110b1202a062a004005400218a8382b044302a02f000c8010b160220602c741d81102c004a0f8008 else 0x1800330320608060208d800240444606c001b819220404805860481983401c40620640b0e8202202c3e000d0888f01e000720589810110161833068c1464440609010330683069009015000305e000d1088c0583402c304404e80016250003020300cd818c1980e103401d8000c100cb0002c06080d005d02a00060a0630222602c4e000604c1581b0006e058a08c160330544046088581481603c004c0840f000e8002502c38290001c816250460f809010162c0006e0586088058811018a0e0c40b160670024c30460880c8c12002030302605a800f0230740f40a801680019103c0440cc74080f016183402c064703c1e0226084a040880b0c82607204104903d8383f02c4a000640b0c110160483044c0011a0f203f062058600a8003401c4a0006050308170024c4a04c0c81e002016032204201412036240006e05860cd8188810330183a088081781620210480700d1182b036000d40b1780034222321c1e0600c1980ee00060c00d800980048930315020904806c0860080c090101814006040306c01000a80040580c604320f40c8180b24000382a00103c0900e01806658048080c0e83858020014006060446c008003402c4a040d00b0c08d040183408416838c806021502600204604c0ce0326000818a00201d400800c1281a01d404804f00200180ea0ac0c81918190317030000c40c816282302740c6065800980013102340540c604d800281904c00260e1005400443838020a8811c05c0003c980c070b00000160260026080c411605018122801c81e0015000e020c0e090c0e02090c0e0701f8158060223e6040f81d400641d005031c0c60100074140e0885d0216020b000262c060384c0c0c8982058101915070b0002420321024032800e8191f1600022260ac24440f00080c040f819a063a0e1600160006440602c0c2c0009888100c101cc002207800404c0c303181e038062801081300101c01a030606583880c840f01a1502216202640f000c0900f600360ac0d800c0ce0082a3605c0c2182605c5c008004c102c1c158221903c0028)))))
def x511l11 : Packing := (1328,4,7,0,0,16,0,x511d11)
def x511h11 (i : Nat) : Nat := (if i<2 then (if i<1 then 0xa247c8172627380001e148504a6000000842000000000e2d188e39c109d00a120d38000022228856b204180000000040d9d40ec885e6c1bc18af0c23fdd65067bfdc1f362cb281a20000000006110f0cb4a219a000880ba600cf414038c92204440ddfc3000816b6161000000000086ca23d0a822b418c80000e17f08432000078017250de05a1007af051a031e80000a14a30282404a000000000603fee150105f400007007a0000386e322ca385544037f02f4000000000000050f33e348d041342db80001c2a3f0491a000184bde073a094e0000000406155f045c60ed68dbfe12a00cd0423bb03dca0dbb8246a0c5409e1004d6047bc20e6880460b1f831e238b10459a3c2e8c1f20543855e000078481001ab86358143083106077405c7a0f68000120ce609cbc031f0291672a00000e0f9b068200000000000cda8c0ba0ea60da015a15860cc0d4000000000383f00000385344371004d38140a06e400e590ba8e0529814220c5f81a88c0438649605b58355619060e97622588ad642d7a070f4149800000095803e560a320c6e010e500d660fdf8c07818760ecc4166206eaa199c82aa000000000a334f02140000082686094859aee3cda0bcde1899080dc369286d000003b124a0cc981aa401670294000040132e25410654a36bc40d6e121304a5a10680c17503c88d6000006803c00005051162c71044a615180000208220550000000000960b04c6f61823898f2006b8436c18a28966c002a801e6120d030fa39210161602ae8b2502ff88df4825e7011da3433838d835ad865940b83846720d82067d40384836c623d705a460d1d061581ce3042f839f3073ec09788102e0123034a24247461c00a06001031a15f0c02382173a083190009732001498e281d48c0a0020200000840204a8008102a402406d60e1c080124401c2c4c780080400d06080803c2c608039400a243c011000018106c418816000010a689804a748831604381065818b08302001200634060c1130c000040000482149570400081000c101831214082080148102180000e18015063c1801000000e2001040e1068332080000010181027860a002408114f0c0800180820848480046400118a012b002c0831400040145c1061200286620001d0200a800200016007868000081000214501046818a0600784080c0ae020400018045020208801140030a000800a140c4801c0028100081000040003000ca82183818f1200192081800400100080204090062030b04100030834b091a0099400401000e000030a10500000010c0404280020c281005000400080120254700040408202000160804002001c5003814c0a020000e1e8c001060010708000b302006090624026080020f0c000031600c8514040000c1400e0244004042400000040060004082 else 0x14eb0d1cc1c4b809d4086b02f8e16228075027ef8e6f011c7870a835cd00b201050000061b740743a069500bec16e68b4a210f8000000006bc534328611ee0000604fb4212000000000481f4000000001a065a8de600005044c00000000000896802f407fb09a600000017a01ba10515619a80001e1571894721ac98387e05d0052e000028d4ea024c85620030800010009a0730c3a1401222075e0234212200001409e00001e164a04dd208760860e16a383524174f1a9c00000000141ac00000610790087a0ee7a1aee03460ab00000382fec9946873a0000201de00004045f0ba10042d8241181c7435f800012093e047e000028198000000001220480000a0f100001a09910b49e1d100000408b50e8ce2c30000120fe88b3200cd00001c004c8c3420a1c0060000000000000078530000000001c0410000120c67026d6153f8126000000001a2f280000000000000623c80001c20d8000180ac00000e04e4871be1b1205b428a1388ec00004810f40e63057be19b280800000605cbc0214861b00037872ac0dc00001215cb089981b6680f5e15270d12638ef02e3c24530616e33a502c4000020028000048864812b08ec6a07898cb20000384da0001800000000000010125e0cc0000008a98000000001811158e8e4039a0871a19818d32c063a00ed00fe4057041255854ae14c900ca212378a25e22ec0299236688383638c083ef018a902cc41b58000100fcb807fc0e815c50e19e80000232350847219d084f5c2f968986601bf8e76a0144028080882046500dd8830b20a3c82008317e8e53612e6049fe0eaf8407e10230506000068144a05f784c30384d8178829f20ca8e30b800010008db651a0eb9863d617680001c0d16864cc0b0282e5e0dab020a60dfa1560c1bd180a2210d50ddbe3c180000000000000e32f889e9802d0001800000817e00006c573a31a00bec0000583fdc3cb086390319d4444206c0027c62bff06816197f852d42b678605e0a5fbc5043722808c426d905c9626c90300c3bbf85ac209c204c5007038159091a80000a1a480001c381800000000301b8124d3859000000000042fa000006c24289efa31650321c1a878419a914252b4408cc09e5a0d0d070c413180000c0c70000023b800000000000000000018379c3ca0000002af301d3c0c258010c01b28216222d008d46262901b6000050236000050606000028cd5211880000434400000a01c801e783c24032200006814e6017289f62278d02ae200820b26000000001614f8029a00f4d31f600004cb89e370d0bb34258445dcc03fa0cc3413c0000000006089fe04bd80f1824d0021061cf20044a072f022f008e880a400003064aa16a800000000512f6000050732a243800000088e82ace3aff8db08044bd2c000000000162b180000652300000000000) else (if i<3 then 0x203c01c706c2000000001a48e586f60000504288149081da0000350a3e0f2d831be090a81200000582bf01ae10575203ce0a030273103ce0000586c6e0dcb0d578087f01a00000603560000606980000185c545bfe8025833f4069741628000062067015e0000286bc0000002a640365843a60e2186a9683ca0e91e02c0034d41bf0070420bb408cc41c9b8a3940a9580c423845840e0054b80a9ad87e8274e25cd8364810c61572c2dfe00efe16f40207228280000000000dee000008368c3ab0000180c1000000000200980066e00372b238000122f8181e8000028a0640f7e826aa0458000120c95851f0111a8b00c0b6a04ee6342d03b72010981fde0ca68965297a1840be09750715c0fac89b8000040276000063065011038f16c19c80000000008349a09cc00b60000382282197409fca1aef0826c1cd900d421c25835a55bed04f6c02eb85dc2194481f7e153484b34025d88af20d040ce42190a007de0190000000006815421a290cf2e2fac038e3475d8e5d60b570582c3bc500eae15db02fc0000189e6221d00000e0490000000006010d417800000e220d85b7a00b0000000000014c000000000210f00000e0e9385d480f5e0b7be258c849de14db0218a03a204e4c17de0bd120fd704f321016dd51430120efc0092a02d2a1359062e61b980b9a83c7595dc6083b003fe2be986520000487460039007182062a02d8e244a03120000680a7213450802e1cd3860120791898121b6a02dda0f55062c81c7e36fa308e003582115f0c3c0122b06aee5d12813ec1366091a81c8a058cc0e7e038b464d0832c42a78000000000000000006002ae0b7e8b7d40bc88d3a00004033b0046006d2a39e0039a424e0000100eff07112363c8647a3ac408e46011d84ba617e80001c37cc0362c13200000c11508e6ded2b0035e6067900c1a1b7d8940000000001c17c682c8000000001605000000a23a10954000020473a35680000000000001211deca9c0000702ee000000000000000000000000000000000000618800000000000000427cb01c800000000000000000000000000022ed80000613980001c0278025aa0ca88eb4000000000000000d2ba8a2c06180000381e00000605f2c21ae00820000000014059800000000706c000002da8480aee028ae159784dea03768474e37b70a5ba0ad88516633350326a17a68238c32c188e7c295b0eb3c29fa85c2c1123815d834148194c091606440e91786a400000000080a8b9010a231281b2a0cc00000a0f1d8b204034f0a1a606fd04aa207e80000a16c407200168802eb202e600fbe43cf8088e154b8669017a887076156584ff613a784cc4304605ae8015d027e00765063680ad504a0c0f0406bf616508380a105d812ce06118b8740ef70068416fda0a460f62003280e9b018de275780954 else (if i<4 then 0xa11831d45007c3017140b9a05a761b3f0e928f7b7088d62d4986f8c03e485c0c0244004bc033000000000105de031d000006d7b5b1ae00006067e206700001e0d9b0410f7b02842081ca3032e8ea10816200004029d8042d06efe182a8908022e7863aa143931d7c1353025101cb89c6fa09800508812bc8b6682047886d60d7204f82166800008051a88db413b38b9cc0eb5840d011e702fa00000000003c4d06a6000000000000000001831d80001419c000000000000000000606b720f200000000000000000048227a183e045a0000000000000000006234b8630000000000c339b8684a038f82b3e399c027a202b98259030d83450e073484e080f8886e001a7000018202a053d82ac80000000038424000060561400c2062200000813a000000001a12c305d600002c5e80000721c0a15108505c11f183906121f063ec0b3c065b019bd0114e3be2823c42fcc8c3180df082d021509012b42e228a23804000000415a000008195c01c52138a856c831500000000018d01615f983baa1c0805e2e33b103c3815e30597c019b0566297730c7d60522815641a42830241a50804e0000106b40000684a200004925f62c530b06e242b869f41be80dfc00000000023bcc846800008000000000000160a48810942ed0000000000000000000000121b50000000000000000001000f438100000210a8000000007833f61844898c000010ca421300000000007858e207400724207be0b79d10d9866323a8602bdc0649808be0c378c7e4373800010046b011ea147286128326d8679c201ada45414ae099220a7a0186e124f80aca016e816e811b886f28108f803ae223b82c2a1aa9855a202f1d1bac01e7857d817b19d6f01a370039825a0824ca2e6383ec2397b0393401510d76f01b0000122cef3551a27b78498407080000000040a428060401f20126f86a3c3372815a0000082a8e179683d020ec00000e1c70000000fa00000c0b5c864ee023e8f2000590000000000000100130000182b940169006080000208480000c113c05f8800500001ca7bf826781b30000123a7b8d8b8114b1d0d029650edfa07b2059de0bc600db817b88e32617fe896e2069a8ce300074837b057a30063806bc0687e0a2600c9c026a0e08803f584bf412d4046b481400e89436188ac00000401904083082b983278056ea161e85ba00006869b019dc03a282ee88a69e1b2000000173f01bac06f00001612df84ca000048aa62e7d9059fa0e76039460811841ca3565833c2f3930e826206a0953c06270b90419900001a173589acc14e48e1600007a30400b2a8efe8fb05068ea133f860362bf0000000007028501cb480f7e357806883429520a2604d80cde805de0076c06d00000000030231a371d0400000058bf8000000000000000001200100001033c00001c352d else 0x581d5c3c058374014668263a1ab78b39e0f350ca2e1c038254004f4046d00bda0e8bc3496a4ed63c67885761600093d40c1f8b8b02360000102eaf0ba2000031df3c0e108131e1d0131bac2ebd05d1020b306fe824b08dcdc294a80350189682412092104500017b8a2be22830dbc000038716413ac8402c28d008ac00007826fe17618053a33a80001e123d04fd80a87061e43b6f8e260000486ec414880c4d2388401ad414280001416c883e0a07e000012144a023e)))
def x511d10 (i : Nat) : Nat := (if i<5 then (if i<2 then (if i<1 then 0xff493054d8588a0087fdcb544a960a00c7de336d4a958a00d7e8b9481a5486008ff9c52e6aa60600b7e4c96095284600ff621154d8588a0087fdc82e5a54ca00b6ecc954e2299a00df6952aed5348200cdf9c7aeda54ca009df9c7aed5258e00bf69c04c65588a00cf7a556c4a960a008ffacc6e0a94c600cfb9c42e6aa4ca00a7f8c96e1a14c2009fe8c9aed8188a00fec92054a3399a00fbd288482118ce0087fecc2e5a254600df7151aed5244200deda332e55299a00cfd8b98cda85c6009ef9c52e53299a00cff2112e5a360a00ebf1814c5a060a00ebf1814c4a960a008ff9c0aeda3546009fe9cb4c58588a00e6dca98cd6558a00ffa21161622912008ff8c9aeda14ca00dfd181aed314ca009ef8c9aed5399a00bbe9c04c68888a00bfaacc6062291200ff61525451060a00a7f8c96e98550600de78b99556258e00fbe2114c28888a00ef7255844a94ca00cbf9b5a20a94ca008ff8c96c5a360a0087fdcb54ca94860097dcc9aed828ce0097f8c9aed824c200c77e55aeca94c600fb69806065588a00abf9c060aaa606008ff9c1aeda54ca0097ddc12e5828ce0096fdc22e55399a00e7d9302a5a54c600d7f0b9441a25460087fecc2e5a54ca00ebf181545a060a00cff2116cca960a00fbd288542118ce00cf7a556c8a94c600feca335422299a00c7f8b9681a548600ff4920955218ce00fbd131605824c200c7f8b96c1a3546008ffacc6cda054600b774c94ca5584600ffc13054e1188a00fe69309562299a00cbfa886d4a94c60097f8c96cda548200b7f0c96cd5084600ef6a22955a358200cff2116ceaa60a00f76950888a9546009ff2cc6c13284600fbb211a215450a00dfd211aed828ce00a7becc6d0a960a00cbf981aeda060a00cefa662e9534820087fdc52e5a3486009ef9c6aed814c2008ff9c32e5a160a009bf8cb6015360600b76cc96065588a00bbe8c96095260600dfe2bb4c58188a0087fecc6cca960600ef5a33954a958a00ffa1516062291200cfea226ceaa54600cf7a552e6aa4860087fecc6d4a94ca00ef6920956aa48600ebea88889a550600cff2112e5a54ca00c7f8b9681a54c6008ff9cb2a55358a00ff4a229563358200cfb9b46c4a960a00cfd9306d6aa4c600cfe920aeda254600ffc1306053188a008ff9c3aeda2546009feacc6c58588a00a7f8c9685a060a00efd130aa93160600f3d930a20a94c600dbd980aed818ce00ebf211a22aa50a00a7f8c96e952506008ff9c52e93148200a7bdc42e6aa4c600cfb2116d0a960a00c7e8b9889a5506009ed9c6aed818ce009eb9c6aed81912009df1c7aed5284600fbc2118ce8888a00fbc182605314ca00c7b6116d0a960a00fe4a558ce2299a00fb618254552606009cf9c7aed5299a00ff22229561191200fba2119128888a009ee9c6aed8188a00 else 0xc3fdb5a20a948600d7f0b9441a354600dfd1b054d8384600a7f8c96e95150a00dbda886d5218ce00d7d8b954da14c200cff211aeda360a00beeacc54e2299a0087fdc12e6aa60a00fbd181545828ce00d3f8b9601a7606009efacc2e55399a00efc930889a354600fe692054d5299a00dfd1b3605514c2008ff9c12e5a360a00d3f8b9601a560600f7e110888a954600efe1204c6aa486008ff9c3aeda060a0087fcc9aeda360a00fbe1805458188a0097becc6d0a960a00d7f0b9545a344200e3bd816d0a960a00d7e8b96c15388a00ef7150606aa54600c7f8b9681a254600dfe120aed3148600c7ddb58cca96060087fdc52e5a160a0087fcc96caaa4c600cf79b3954a958a009ef9c6aed8150a0097ecc9aed8388a00d7ce222e5518ce00ebf181544a960a0097f8c96e1a14820087fdca2e58348600d7d8b98cda54420097f4c9aed3284600ff495254d8348200bbbacc6058291200fb728850a5584600de7a552e53299a0087fecc6cca95c600fba9825498191200ffc110889518ce008ffacc6cca960600fbe18160932546008ff8c96ceaa60a0087fecc6d4a948600cf7a556cca94860087fcc9aeda54ca00b7d4c954a118ce008ffacc6cca958a009fd9c12e5828ce00cfea222e5a354600af79c5482aa54600c7bd516d0a960a00c3fe886c4a94ca00fbc581609314ca00fec9534c22299a00cf7a556e0a94ca00aef9c6aa95260600bf71c060a55846009ef8c9aed3299a00dfb1b4844a960a00c7f8b9681a35460087fdcb608a94c600fbc9304c68888a0087fecc6c8a960600cfe9b8888a954600b3f4c96093160600e7d9306cca954600d3dcb9605828ce00cbf9baa215048600ebe920a22aa4860096fecc2e55399a00ff49304c65588a00eb7a88954a9486008ff9c82e5a25460087fdc82e5a2546008ff9c22e6aa4c6008ffacc6d4a94ca0087fdc16cca960a00eb7a55a20a94ca00cfd9ba8cd5048600f77150604a95460087fdc82e5a34860087fecc6cca958a00cfda33aeda0546009cfdc7aed5299a00df5a552e5218ce008ff8c9aeda360a00ff51208ce55846008ffacc6e98548600ef6952481a354600efd1314c2aa48600ff615254d828460097f9c22e5a544200ff62554c58188a00a7f8c96d1a254600eb7a55a22aa50a0087fecc6c8a958e00ff29819562291200c3fdb3a20a9486008ff9c12e5a54ca00cfe9522e93160a009fdacc6d5218ce00aff2cc544a960600fe6a229556358200bfd1c0605518ce008ff9c52e6aa4ca00d7ccb954d8388a0097dcc96c9518ce00b7e8c96e1204860087fdc22e5a354600e7e8a9889a054600bbe9c05468888a00e774a954552606008ff9cb2a552606009fe8cb54d8088a00fb698054d8588a00aff2cc546aa60600eb7a88954a94c60087fdcb60ca9486009fe9c32e58188a00) else (if i<3 then 0xdfb181aed5191200cbfa886c8a94c600dfc9b054d8388a00cef9c6aeda160a00c3fcb9a22aa48600cfd9b58cca958a00cfda336d4a960600dfc9b0889518ce0087fdc22e5a558e00a7f8c9692aa5460087fdc12e5a54ca00c7f9b02e5a160a00ef6a55888a94c600d3f4b9a213284600bee8c954e2299a008ff9cb4c8a960600cfda332e5a160a00cbfa886cca9486008ff9cb604a94ca00bfe1c06095284600ff61515418188a00d75cb9955218ce00cfd9c3aeda354600c7ecb9889a558e00ebf1814c6aa60a00b3ecc96095260600bf72cc54552606008ff9c8aeda54ca009df9c7aed5250600b7d4c9605518ce00a7f8c96e93058a00ebf288aa93148600cbfa882e5a14ca00c7f9b24c0a954600dbda882e5218ce009eedc6aed8188a0097f9c82e5a14c20087fcc96e2aa4c60096fdc32e55299a00ebf181546aa60a00fb6a555068888a00c7f8b9681a5606008ffacc6d4a958e00a77dc32a65558a00b6f8c96cd5099a00afe9c52a62258e008ff9c52e5a160a00cfd9a0aed314ca00fbe2885421188a00df5a55aed314ca00a3fcc960aaa60600fbc9108ce8888a00d7e8b9889a544200b774c960a55846008ff9c52e6aa4c600cff1c12e6aa60600b76cc94c65588a00cfe9b8888a94c60087fecc2e5a160a0087fdcb60ca95c600d7d9306e0a94c60096fcc9aed3299a008ff8c96e2aa4c600d3f8b9601a260600dbd9812e5828ce00dbb9b4604a960a00efd131606aa4ca00d778b9541a2546008ff9c0aeda54ca00c77e556c4a94ca009feacc6c13188a00e7d9302e5a354600c77cb9955a258e00d778b9955a848200d7e8b9549a8482009ff2cc6c95084600c7dcb98cda558a00d778b9955a14c200d67e552e56258e008ff9c32e92054600dfe2bb8455388a0087fecc6d4a960600dfd2332e55284600cf79ba9553244200ef695088aaa54600cfda336c8a960600b7e4c960e1188a00c7f5b14c4a960a0097f8c96d5a148200fb3a889554150a00c77db2954a960600c77db5548a958e00d75cb9955628ce00c77cb9956aa4ca00ff51518cd52442008ff8c96c6aa60a0087fdc86c4a94ca00a7f8c96e95058e00cfe9c2aeda254600dfe182aed52846009fd8c96d5218ce00d6f8b96c15399a008ff9c82e5a14ca00a7f8c96e98048600cff1c1aeda160a00efc93160aaa4ca00efca228cda558200b3ecc95468888a008ff8c96caaa4c6009feacc6c18388a00ffa18254a1191200d7e8b9481a8486009fbacc6c5829120097edc82e53188a00c3fd81aeca960a00a7f8c96e92058e0087fdcb54ca960600ffc1324c5a160a008ff9c82e920546008ff9c22e5a558e00cfe8b9889a558e00d3dcb9a21218ce009fe9cb5413188a00cff1a8aed314860097f5c22e55384600cdf9c7aeda254600b7e4c954e1188a009fd8c9aed218ce00 else (if i<4 then 0xcff1816ceaa546008ff9ca2e532546009fd8cb481518ce00d7e8b9889514c2008ff9cb2a5854860087fdcb544a94ca00dbf1b0a213284600ebf18160aaa4c6008ffacc6d4a9606009ff1cb6095084600cdfa776e2aa4c600d6de332e55299a00c7f8b96c1a54ca00cf7a552e93160a0097f4c96d532846009fb9c2aed5191200d3f8b9a21a544200e76e22954a958e00d7d8b94c1a74c6008ff9cb2a5524c600bbe9c54c68888a00cfd9c32e6aa4ca008ffacc6e0a95c600c77e556c8a94c6008ff9cb60ca948600ebd9a88cd8148200beeacc5492099a008ffacc6c9a054600c7ddb88cca95c600cfd930aeda3546009fd8c9aed828ce0097f8c96d5a24c2009fe9c52e58188a00afb9c42e6aa4c600df59b0955218ce00c7f8b9681a74c600fe4e339562299a00be79c24c25599a00ebf18160aaa54600a7f8c96e95058a00c7f6112e5a360a00a7f8c96d5a24c200cff1ba845824c200dfd110aed518ce009fe9c2aeda74c600cf79b2954a958e00ff513054d8584600d3f8b9601a360600fbe1806053188a00dfe120aed5284600e3f581544a960a00cbfa886d6aa4c600bfe1c054e1188a00d7d9302e5a54c6008ff9cb545a360a00bed9c25423399a00cff1b14c4a960a008ff9cb608a9546008ff9c22e5a354600cf7a556c6aa60a00fbb181545829120087fecc6e0a948600c3fe88aeca94c600cfba442e98254600d7e8b9889a4546009ff1cb4c98584600fe59535493099a008ff9cb4c8a954600c7f8b9681a64ca00cfe9c2aeda54ca00eb7a55a22aa50600c7ddb28cca960600f7d1102e5518ce00efe222544a960600ffc1808ce1188a00cf78b9955a258e0097ecc96c58588a00a7f8c96e1a0486009ef8c96d53299a00c7ddb58cca948600ddda332e5875c6009ef9c6aed814ca008ff9c82e6aa4c6008ffacc6c8a9546008ff9c32e5a254600cff1b8844a94ca00ebe98268d5260600aff2cc4c6aa60600bfe1c060e1188a008ffacc6e0a948600ebf288845a550a008ff9cb6a132442009efacc6c95099a00e7d4a94c5814ca009fbacc6c95191200b3f8c96a18148200cbf9b3a20a95c600c77db3954a948600c7bdb4684a960a009df9c7aed5258200d67e552e53299a0097edc52e53188a0097f5c12e5536060097f9c12e5a848200ebf288844a94ca0087fdc26cca954600cbf9b8608a94c6009ff1c32e55284600e7f0a9845a060a00c7ee22aeca9546008ff9c52e5a258e00cfb9b4684a960a008ff9c32e5a85c6009fe9cb5418388a00dfd130aed3160600aff2cc6a131486008ff9cb608a94c6009fe9cb4418388a009ef9c6aed8148200a7f8c96c9a84420087fdc32e5a254600df3a556c582912008ff9cb548a958e00ebda884c4a94ca00ef71512a55260600bfe2cc4c58188a00e7e9202e5a254600dfaa22aed5191200 else 0xd3f8b9a21a344200c7bdb46c4a960a00c7f5c12e6aa606008ff9c12e6aa4ca0097f8c96c9514c200efd131681814ca00d3bd816d0a960a0087fdca2e55348600b7f0c96e12084600bbeacc4c68888a009df5c7aed5284600cff2bb605a3546008ff9c1aeda060a00dbd981aed828ce0097ecc96c58388a00c7f8b96c1a2546009ff0cb6015384600fb718054d8584600cf79b8954a94c600a7f8c96e9805c600fbe1806161188a00cbfa886caaa4c600fbe1105468888a0097f4c96c98584600afdacc681314ca00e3f8a9605a060a00ebf1824c6aa6060087fdc52e5a258e00dfca332e58188a00fbc980606228ce008ff9c16cca960a00fbe1824c55260600ef7151aa95260600c77e556e0a94ca008ff9c52e93160a00efc93260aaa4c6008ff9c0aeda254600ff62224c25584600d7b5b4844a960a00dbe9806c58588a00c3fe886c8a94c600ff5151549818ce0096fdc52e53299a00ef7255aa93148600cff1b5844a94ca00dfd130aed5384600cff1c1aeda354600ef6952482aa546009ef9c22e55399a00aff0ca4c58148200ebb9816d0a960a0097f8c96cda544200d7e4b95458188a00cbfa88aeda14ca00ff51534c152846008ff9c0aeda160a00ebda888ceaa5c6009ff2cc6c98584600b7ccc9606228ce0087fdc56e0a9486009fb9cb61521912008ffacc6d4a9486008ff9c02e93160a008ffacc6cca95c600cfd9b28cca954600c77e556c4a960a00cbf981aeca960a00ef7255845a850a00ff618088a5584600fe59209563399a00d3f8b9a21a14c200afbacc6d0a960a00ef6a5560aaa4ca008ff9c8aeda25460087fcc9aeda348600cfea22aeda054600ded930aed5399a00ef6a5588aaa50600a7f8c96e9305c60087fcc96c5a360a00d7f0b9605a454600bbeacc60952606008ff9cb2a5854ca00bbe8c94c68888a0097f8c96c9a544200bfb2cc54a1191200dfd151aed818ce00dfca33aed8188a00c7ddb88cca948600cfe9c2aeda060a00bee9c35422299a00cbfa886c4a94ca008ffacc6c8a96060087fcc96c6aa60a009fd9c3aeda460a008ffacc6c4a960a008ff9cb2a5835c6009ef9c32e55299a00dbe980aed8188a00ebe982606aa4ca00bf72cc54d528460097edc12e58388a00ef7255846aa50a009ff2cc6cd50846009fd9cb601218ce0087fdc32e5a160a00d7d8b94c1a84c6009fd9c52e5218ce00c3fdb3a20a95c6009fbacc6d0a960a00dfe1b05458188a00c77db2954a958e00cff211aeda060a009eddc6aed818ce00bfc9c0606228ce009feacc6d53260a00dbf180aed8154600ffc1508ce1188a00f7d130604a94c600ebe982aa95260600cf79b5548a958e008ffacc6d4a94c600fbc920a21218ce00efd1306a131486009df9c7aed524c600dbba88aed21912008ff8c96e9854860097ddc22e5518ce00))) else (if i<8 then (if i<6 then 0xc3fe886d4a94c600cff211aeca960a00dfd130aed3148600ebe981aa93260a00dfc930aed3188a009fe8c9aed5388a00ef72556a1314860087fecc6e0a95c6008ff9cb541a348600df5a55aed218ce009fd9c82e5218ce00dfe222aed8584600bf71c24c25584600ef6a552a62258e008ffacc6c8a958e00cfb9c42e6aa4c6009ff0c9aed838460097dcc9aed218ce00c7f8b9689a454600ebf180aa931606008ff9cb54ca9606008ff8c96d6aa4c600dfb151aed81912009ff1cb5413284600b6f8c96d53099a00cbfa886caaa54600cfda336caaa546009ff1c82e55284600feca228cd6558200ff4950889518ce00dfd2112e5828ce00ff31515498191200df3a55aed2191200de7abb54d5299a00eb7a88955a150a008ff9cb544a960a0087fecc6d4a958a008ff9c5aeda160a0097f8c96e1a544200c7f611aeca960a00abf9c84c6aa60a008ff9cb54ca948600ebf182546aa6060087fecc6d4a958e008ff9c82e93148200fbd180605518ce00b3ecc94c68888a00c7edb8888a954600bfe1c06161188a00c7ecb9889a354600bfd1c054a118ce00ffc1316cd2048600c7edb5888a960600ebea8888aaa50600dfc920aed218ce00fba9519128888a00fbc6118ce8888a00cf7a552e5a14ca00cbfa882e6aa48600cbfa882e5a54ca00afe8ca60222546008ffacc6c1a54ca0087fdc32e5a558a00efd233544a9606008ff9ca2e5534860087fcc96d5a34860087fdcb608a9546008ff9c82e5a54ca00ff612054d5284600cf79b8954a948600fbe18254983846008ff9c3aeda160a00df7255aed314860097dcc96c5828ce00ff61514815260600c77cb9955a34860096fcc96d53299a009fd8c9aed818ce0097f5c82e53284600ffc18588a118ce00cf79a5aed524c6008ff9c82e6aa4ca00d7d4b9845828ce009df9c7aed5244200f6d9302e55399a008ff9cb6818548600c77db3954a960600c7dcb94c6aa4ca00d7d4b954d838460087fdcb548a958e00cfea22aeca9546008ffacc6cca954600af79c52a5524c60087fcc96d6aa4c600abfacc604a960a00cfd9b88cca95c600c7edb3888a9606008ff9c32e6aa60600d7f0b96c15384600a7f4c9606aa54600ebda33a20a95c600afe9c2aa9524c600bf69c06065588a00fbd152a22118ce00cfb9516d0a960a009ff2cc6e11054600ffc12054a118ce009efacc6d53299a00fb668888a5584600eb7a55604a960a00cbfa88aeca94c6008ff9c22e6aa6060097decc2e5518ce0087fdc12e5a360a0087fdcb54ca958a00c77db8954a9486008ff8c96c9a354600c7f8b968da544200be7acc54d5299a00dbd9b0a21218ce00fbc932609a84c600eb7a55a21a14ca00ef5a33955a258200c7f8b9681a760600bfe1c154d8188a00dbf2882e55284600cbf9b5a20a948600e7b6116d0a960a00 else (if i<7 then 0xc7fcb94caaa54600c7fcb968d854860097fcc9aed8348600cfed522e93160a00a7fcc968d8548600c7fdb254ca960600f3f581544a960a0097fdc82e55348600c7fdb84c8a954600c7fd516cca960a0097fdc52e5a160a00c7fcb9695a64ca00f3ecc96095260600a7fcc96958348600d7f4b9545814ca00d7f4b94c58548600e7eca9549a160a00a7fcc954eaa4860097fecc2e55348600c7fca9aed835c600c7fca96d5a160a00d7ecb9609a54ca009efdc6aed814ca00d7dcb94c5a54ca00c7fcb9609a354600c7fcb9aa98548600a7fcc9695a84ca00c7fca9aed5360600cfed526caaa4c600a7fdc32a55260600a7fcc954eaa58a00a7fcc9aa9814ca00c7fd32aeca954600c7fdb54c8a960600a7fcc9695a14ca0097fcc96d5a14ca008ffdc3aeda160a00d7f4b94c5526060097fdc52e5834860097fdc22e55360600fbe5816093254600a7fcc968d5260600c7fcb954da160a00aefdc6aa95360600a7fcc9546aa4ca0097fdc52e5a64ca00c7fdb8544a94ca00e5fd876dca94c600c7fcb9695a160a00ff31829561191200c7fabb4c0a954600c7f8a96c1a354600ff46228ce55846009fd8cb4c5824c200dfb211aed8291200bedacc54a3399a00de7a55aed3299a008ff9c2aeda354600cfea226cca954600ebf181609a354600fb65825455260600dbf288aed3148600fbd15360983846009fd9cb615218ce009ef9cb4c95099a00b7e4c96161188a00bf71c54c55260600efb2116d0a960a00c7edc22e6aa60a00ebea88888a954600e7d8a94c1a35460087fdc56c8a960600a7edc22e6aa60a00cf7a556c4a94ca0097facc2e5a454600c7f8b9609a550600dfc9206c9518ce009fd9c3aed824c200c3fdb8608a94c600cfda33aeca9546009ff0c96c985846009fe8c96c58588a0097f8c96e9514c200abfacc60aaa606008ff9c52e5a14ca00cfe9b5888a94c600c7f6116cca960a00fbc9518ce8888a008ffacc6c9a3546008ffacc6d4a958a00e7d8a98cda054600ef5a554c4a94ca00bbe9c84815260600aff0ca5458148200dbe982aed814ca00efc9324c6aa60a0097f8c96e1a2442008ffacc6e98048600c7ee226cca954600f75930954a94c600dfd131aed814ca00a7f8c96cda84420087fdca2e55360600efca228cca9546009ff1c1aeda648200afe9c22e6aa60a0087fcc96e985486008ffacc6c5a360a00cfba446c6aa60a00c7edb5888a958e0097f8c96cda844200dfc930aed5388a0087fcc96ceaa60a00cff1816d6aa4c60087fdcb4c8a96060097f5c52e53284600cfeabb889a354600c3fcb9a21a348600ef71516815260600cf7a55aeca94c600e3de33a20a95c600efe11088aaa54600efd131604a94ca00dfd1b0845828ce00dbb981aed8291200dbba886c95191200ef7255844a960a00d7f1106c8a954600 else 0xe86b5dac66ad5ab06aada9a6995a54693da3e6885a10682d9ee67759d8674d9c266c59a0663d97e65e5974655d94664d5924641d8f663658d4630d8be62b58a8628d89e623587c61ad866618585c60cd82260157f45fbd7ea5f957d45f3d7ca5eb579c5e5d7925e3577c5ddd75a5d557445ccd7225c4570c5c1d6f65bc56e05b3d6a65a556905a2d67a59a5658594d64e58f563858cd62e5875618584d60e57f55f857cd5e2571559c562d56e554554054ed52a5495514540d4f253854d052fd4ba52a5498521d48251c5460516d43e50e5428508d41e50653fc4fad3da4f253a04e6d37e4de53684cfd32e4ca53244c7d31a4bf52ec4b9d2e24b752d84aed2aa4a6528849dd25a4925238486d20a47e51dc475d1d247051bc467d18e462518445cd162454514044bd11e446511443dd0f243850dc432d0c642d50a4424d08e4225078410d03e40b501c3ffcffa3fd4fe43f7cfce3ec4f883e0cf723d54f503cfcf2e3c44f0c3bbcede3b64ed43b3ceb23ab4e9c3a2ce7a39a4e4c391ce123834dfc37dcdf237b4db8369cd723584d5c352cd4634d4d30347ccf63394cc832dcc9a3224c78319cc623144c4030ecc1e2fd4be42f4cbb62ec4ba02e3cb662d24b442cccb2e2c44b0c2b8cad22b34ac82adcaa62a24a84299ca562914a34285ca0628049f0277c9ce26f49ac266c97e25e4974258c94624a4924244c90e23948e0236c8be22b489c222c87a21a484c211c84220c4820203c80a1fb47dc1f2c7ba1ea47a41e1c7821df47781dcc76e1d7474c1cec72a1c647141bdc6f21b846d01b2c6ba1aa46a41a4c68e1a24678196c64a18e4628185c61218045f0174c5c216c4594160c57e15e457415bc55e153453c147c50213f44ec136c4d613144c012bc4aa1294494120c47e118445c112c42e107440c0fbc3ea0f643d40edc3b20e843900e2c36e0da43640d7c3420cc432c0c6c3160c4430c0bec2ea0b642d40b3c2ca0b142a80a5c27a0944228082c1e2071419c053c12603c40a401bc046007400097fcc96d5a160a00c7fcb960aaa54600c7fcb968d5260600d7bdb4544a960a0097fdc56c4a960a00e7dca954d8348600e7f4a9545814ca00a7fcc9546aa60a00c7fda56c4a960a00c7fdb5608a94c6009dfdc7aed5258e00a7fcc954aaa58e00a7fcc9545a360a00b3fcc9609536060097fcc96d5a64ca00d7dcb954d8348600ffc5324c5a160a00c7febb608a954600a7fdc32a5854860097fecc2e55358a00c7fdb560ca948600c7fdb54c4a960a0097fdc12e5a54ca00ebed81609a54ca00c7fcb9aa95260600a7fcc9695a64ca00fbe5824c55260600c7fca9aed534860097fdc82e5a54ca00c7fdb5604a94ca00d7ed526c4a960a00e7eca96093254600c7fcb96958348600d7ecb9549a160a00aefdc6aa95260600e5fd872a5a74c600)) else (if i<9 then 0xfb00101c0020016034100c0c30001001b8110800000b1800ac002050008000e030887840d020000041ba062e000c0c80b0a0a38138087c0ba068503e0710b17057038858f81447c5c0960fa04300b019604c0701830234147027010f816c1f809c0c803e026016030c052066e09e05e0211f2682f03d818f812c1f4087c082162efffbe2ef17bb4ee5fb86edd7b58ecefb1eec07ae4eb1faaaea37a88e9dfa5ae8f7a20e80f9e6e7279b8e66f97ee587944e49f90ae3e78e8e32f8bae27788ce1bf852e0d7818dfef7dedf677bcde7f782dd97748dcdf71adc57704dbcf6d6dae769cda2f67ad97764cd8bf612d7d75d8d6ef59ed607558d4ef51ed4074e4d31f4b6d26747cd1af44ed0c7414cfdf3dacef73acce3f38acd87344ccff322cc77318cc4f302cbf72eccb0f2becae72a8ca5f292ca0727cc9af266c95722cc86f216c7e71e8c75f1c6c6a71a4c67f19ac5f716cc56f156c517140c48f112c437108c3df0dac3570d0c2ff0a2c24708cc21f076c167054c10f03ec087004bffefeebf76fd8bebefaabe36f7cbddef66bd26f44bcfef3abca6f24bc7ef0ebc26ef8bb9eed6bb46eccbb1eeb6ba96e7cb97ee5ab926e44b8cee2eb876e0cb7eedeab736dc8b6deda6b686d90b62ed86b606d7cb5aed5ab526d44b4fed3ab4d6d24b41ecf6b396cc8b30ecb2b2b6c90b1fec7ab1d6c58b14ec42b0c6c14b00ebfeafe6bf4afbebeaaf96be0af0eb9aadf6b78ad6eb3eac56b04abfeaeeaba6ad8ab4eac2aac6aa0aa3ea7ea9b6a68a98ea52a906a30a8aea0ea7f69eca76e9bea6e69a8a65e97aa5d6964a54e942a4f692ca49e916a4168f4a38e8dea3368bca2de8b2a2b689ca22e86ea146834a08e806a0067fc9fae7e69f567c49ece7ae9ea67989e4e7769d967549cde71a9bc66d49b3e6ca9ae66b49a8e69e9a3667c997e65a9926638989e622984660097ee5ea97965c8970e5b29686590962e57a95a6564954e54294c6520943e50a93e64f493be4ea93964e0933e4b2928649091fe47a91d6464917e44e912642c906e40a8fe63e88f5e3c68f063b08eae3a68e863908e2e37a8d4634c8d1e3428cc63148bde2f28b862dc8b2e2c68b062bc8a7e29a8a2628489ce2568916234885e2128836208880e1f287b61dc872e1ae8676198861e18285c6160856e14a84e613484be12a846611483de0e683560b8829e0a2824607481be05e80d6024801dfea7f65fd47f0dfb27eb5fa87e5df6e7d75f587d4df4e7cf5f207c6df167be5ee87b2deba7ad5e9879ede7679c5e60796de4a7915e3478bde1e7865e0877ddde67755dd076fddba76d5da4767dd9a75f5d6c756dd4a74b5d1c742dcee7345ccc731dc9e7235c7c71ddc667185c4470cdc2e70a5c18704dc0e7025c046fcdbe26f75bcc6f1dbb66e95b886dddb726d55b446ccdb166c15a else (if i<10 then 0xc003a0014030a8004180e1000000010701840340b805860000850206802c2016a03102c002001608000402900100c0020d00081b80b0b4003a001002b0010000050004021a1102081a00b080582090008040c32001070004c082000005820004303168005400200ee002503081c002207400205800443443c4446c001002b00100900b0940020d00088184000220c0a406c060d800200000582007600200003f4004a001002d001202840029a002402900100006e1018004002c1018004041e1300081b8500020d03080002c10000dc05850061300080b06c0c038460610180e800070800ec0040000781a00b0d400200010081840007a0020340801200100000600080b0412001028106c002029a002b0008001340c440413000807e800b00c3c0002421140814844502004800680b8114000d09c001050004008058402c100130110806420028006c00360a1b0008800400002019108907800202c103d01614810400f40040b000800582000040c2c0413000800000500c022198004000088402c10001a00100000b4004206100006001068181b881a061e000b000483c200019841c001034080681701b8e80020000b0740032001002c002000140020002c00200201040580d0400602402c30160886b0008035c00402c1058284002c17000a8004434202c130008006022281300080c003a001001b8110808001000000e02c20160e0206400200860604430206980080e0010030120161907840000000ac00406810000000d700108684c0c202c110f08815000a400241e1000016100c074002007600200040020103a0013018400900080b0440c202c1903080c840003301610005820400083800360010160801a00100de02037033200400202c1039034100002c1048004048058401a05c06e307000443580040d00080b040d00584010d60017000400001980b080a001d000f0185c00206e02c2000a006820011101a0010001051c05c0806e4500080c781c0600b10c0020d0308043420016080180900b0cc00206802c2402080c00b080582c0014030828002600100015800800004805876001d00081a00b0808061016080180900b0c0980d040e00080035c004001400fd031d8004000160c810405b80c400260341381064003600170302a108a04180011030d80058002c001018081301108000220801d800843c0a84080308000c04805860000900b09400202c1b000b00064082022044200140c2a06130008003f40046001016088784c0020016037100000034003a001700088104c002000d7001004342600106800483420b000800e0010120161300048002a00130008340c34001103a00100c84058204406e2d0008000000b054003c0010163001006e8008060017000800cc20c00080021a1c0308040000040002080900b0b800360011 else 0x700100100980b0807c08840301d0010014818640c202602c290520e100c0110b8000cc402401e2018016100c00b09c0040040018080980b08064058401e01c2018016100c80b0ac004004004100b01614819818805ac1c402c01c2b00100100b01b8806032041016039101b8740341040681013016100c80b080580b840540302019016101a00b08002c01c2016034100c00b0ac004004a0501c2018080b00c08140e1825080b00708058038403001c280e0811040d3800406e1016018100b0070a40cc0c401602c2037016100f80b0803c038441a06602c301300c100b0060a40cc0c4e00200203303415010405803840700662e03080b01c8808c0585a00048201300c1580080080580604604150580e10001e4000dc602c2002070001408000701841c06111ff07016180021c110c08140c20b00080058200001802c3b000800dc058481a11000f0004010090400000dd80050081b0008140020014e0316800400b000f0000d08000160807e800940020000b0404405840e000800dc058401fc04204800405820e040180371800d00585400101800400ec004000340020048184002c15000c00040000868601c201e04802c3b0000c100408203000834002600110d0b000405a80c40d000b80040218100000c000a80060a0200001a0010370221381840583000a002068004006e0442e0008008052002018004c0c20180382900080000000002a20d100a006d800c04408840003b00101b80b08044030058760010201041c041030006c0026001600088786800200580050a03c00105800070a4002a0016000806024881a001019081b81108080419000d80040a001068184c082e061900080c002228100016001a00081a00b0801012448052002700080b1000800019083014202c110208002001001a01c8ac00360010376001002d800a4038100d06018044200380020d00081800202c110f12a10100824281300080c002c001000c04001809220180074003a061028005c0c207000d80044002200150008280020000001030f0000d0a400202c16000800e001008a04002402c210e0e8005))))
def x511l10 : Packing := (932,5,7,0,0,14,0,x511d10)
def x511h10 (i : Nat) : Nat := 0x14130007826c23e10000701003460580b000000100e403000080060750c800382fa31f01f023c74000b094885417ce9a0e3008c1be89bb4a861819a1521a4324828c37000286fc14000a14283cc020c840390d00
def x511d9 (i : Nat) : Nat := 0xc0704030100b04000000000000001a0610000005c0020003a00100006e016173eae1df5cda57d552d04dcb48c643bab835b330ae2522a01d94920f8051ef750a96d5a160a00b9d6ea192c12a4c0c01b3e552325824c581803e6caa264b04a93030061bf2e5c6aa95260600e9dada302a8952c1401fb425584633a2222803f682a4c0aa2c14670067368cdc7aed5299a009f54eb598c0c4522401dbc182606bb4c532803f68306a92a6c14230073cc6d255844a960a00f5b0a9302a8d54c1401fb2151609526064480376c38ac1262a93030070fa2e688889a550600f5e09930298d54c1401ebc13260931aa9818033d938d19d76c0c45007ad854582aa95260600ddb0a8992c12a4c0c01ebc1814c582aa932803f644ab08c89444450071cd956116d0a960a00f5b0a9302a8b40c1401bb6182b3151549818027b63af662a508c890078d954981544a960a00
def x511l9 : Packing := (29,6,7,0,0,8,0,x511d9)
def x511h9 (i : Nat) : Nat := 0x180
def x511d8 (i : Nat) : Nat := 0x3d325526d181544a960a00
def x511l8 : Packing := (1,7,7,0,0,0,0,x511d8)
def x511samples : Array (Bits × Bits) := [(0xb66558a96d4a7d46853ec9eea97b299666573fc3ef7c4a9a1a3367fe1e8c79a18df6f8e8ae5a8d188e4d8520c0aa200e1c061b3444a8003101018dc02000241d8101d401000818c10823061814000202382707db329501a3349400c73e21f673,0x302480001a00102410402a48d40100040471800ccc011082060c0007001520804ec91200a61a891884442020d0aa200a1006091424b800211101a111280b6d00c4a0e049c18918400819065854919200082502cb223281202094200224212652),(0x801374fc24ea52069c7e3fe3a5a0e6502b9aeafe72f67bdf843ccf29b3016d396d3dde9c71cd32661a331783c7584700023d8121dcbad91a200842080131c60e14908100085020043082102a40aadc1b30c6250431183600ccff04a4c8c6487f,0x420282a1e1a148c108012402508260a080281000ae04600851e60008400f088034841051c032621a3316000010c910030900e11106929a400e18c8c754808c105c120028422125318218272020091120c2241411091c02884205a488c44829),(0x3d58a1b6faa6b7b47fef35d56f1a968cfd270142a2ff950aa1cbfcfb07bd5d532caa6de30233e9a6ec48b031321cb7ab91d094531a4101044480e037de258030100001010000c000c11c6023c8f3fee401003867c08020410318c438f1078f9c,0x8f995814180850223487448b208d008a00000240a050489446001010933010d040023a4b0033c9850048e028020e160310309e120a2161458480c50608835c7001a0418c0581c000c00c2050889b86841104110a80e660410218801071038514),(0xf4a407ca29752e570ddd2a88977ed36fe702b7d84b6dc5b94bbf969578ba4bfe5c5ef87599041850a933281c84e029f3a1090c0824033eae81350011a48808006026002bac8c010601ccff81b05022000e01c060000000780be0bb3f01f80fe0,0x3006202a04028011c148a80007002114026d0815020c320010552580480ec02082e0048419041012af030004c0e0c1f0a108600524069a022b351a4194040204e4452043e00e006600301504306478200e0380600011103205e0122f00b00ae0),(0x36e26cdf34de800fac0e1b339a0903e2a4312e0ff390eee8f7df6584bdde9cccf7a8b2ba44f136e55094da4a2f151e456c91121ac801009e842d0dc800002031180a0008bce001d900e3801000000005c001fe0004800079f000f84001fff000,0xc0894dc080a56b4a04801133200e024af180274000108070c900c8302060020e0002c95a40e126e55090daca2f151e054ed1124aca0165dc844a04ae03f090bb191a1f941c60019901c6c803800a0507f0007d1004c44849d000c940014ed000),(0xcdd62db2d326cfe0fd50b6bc94972e7196ff16e95e7890b68c0dfe11c8fd24f63fe37a5558a133c731484004288310a06a3a608e83051014b2d0900820520050894d77d41301001efe0000041f000105cff8009801c7ef860000987ffe000000,0x4111002441a0d01010401022080101148006a021008401818106090404a123100000c0548a530433108000c08001220aa38b40a9303f21caaa614c40644925c001d110612100136a42000058a404d2485900100008466820400997dda000000),(0x7bfa44f778984e6807087c2264d2d68a5344ca7e97953e5bed42f20b183088ae052956170c86890ce18a0be60de752c8ac78151eae13c8412d9b02000100538226900901527efe20000000401f0c20d8000000000ea837f9f3ff000000000000,0x1511105d0c104016202110c1a1893101023041007e50128a25ac097082000061708118050c068904e188098e0de712e8acf0351eae016c052ff1072508211202e6a16d57d3bd94c00030c0009f5474ea0004010002b463f977bd000000000000),(0xc3ba8cb2f27c8ccd6e3777901f7d5c6b4ca824a989ccceb4ddd6e9f18c47122e97abd158f74a441847971b93b935915854c361c0654418824019322e7a1400213a02203508010000001000001f0521fdcff9fe67ff4a88040800468000000000,0x6062230981e5a2d4c86832105440a244250a059042a41362a0c885440c04650aad8c4020b748041846971b93b171895844c341c064dc0ca251592a39f1382183fe42ae71e80200c10110c8027524305b6a6beef57f1998040800668000000000),(0x4e2763370385936fbc3960e543d47ed3d21047d122c7e6e4a285ace379a697dbe84fe17a8378c2b910a4d67600282415120208a262e027e11fc2c00860da19e17a6e0ae25b6efe3efec33fec20840200000000000f2840040800478000000000,0x4a40800020012240089044201042042a340004e000a389214000120c10212d0000020222a25842a80064c67002182c0750070ac040f001e01000e01a619a6da1190282a80c406a095bcf2afa408b8200300000980d4a88040800648000000000)].toArray
def x511columns : List ColumnInfo := [(529,0,494,0,11),(192,0,831,0,11),(320,0,703,0,11),(160,0,863,0,11),(132,0,891,0,11),(66,0,957,0,11),(8,0,1015,0,12),(24,0,999,0,11),(512,0,511,0,15),(80,0,943,0,11),(144,0,879,0,11),(322,0,701,0,8),(156,0,867,0,7),(513,16,486,8,9),(198,0,825,0,7),(0,64,701,258,10),(856,0,167,0,7),(595,0,428,0,7),(344,0,679,0,7),(547,0,476,0,7),(0,128,859,36,10),(537,0,486,0,8),(709,2,312,0,4),(10,0,1013,0,8),(268,0,755,0,7),(14,0,1009,0,7),(258,64,701,0,8),(32,128,859,4,9),(519,0,504,0,7),(844,0,179,0,5),(801,0,222,0,7),(164,0,859,0,8),(4,128,859,32,9),(838,0,185,0,5),(961,32,30,0,4),(296,0,727,0,7),(120,256,647,0,4),(480,0,543,0,7),(689,0,334,0,7),(868,128,27,0,4),(521,16,486,0,8),(597,2,424,0,4),(36,128,859,0,8),(162,0,861,0,7),(172,0,851,0,5),(98,0,925,0,7),(527,16,480,0,4),(679,0,344,0,4),(146,0,877,0,7),(852,8,163,0,4),(520,4,369,130,7),(202,4,817,0,4),(846,0,177,0,4),(546,1,460,16,6),(324,0,699,0,7),(626,1,396,0,4),(902,64,57,0,4),(690,1,332,0,4),(232,256,535,0,4),(282,64,677,0,4),(803,64,156,0,4),(785,32,78,128,5),(270,64,689,0,4),(697,0,326,0,4),(154,4,865,0,4),(896,8,99,20,6),(56,0,967,0,7),(74,0,949,0,7),(148,8,611,256,5),(705,0,318,0,7),(785,0,238,0,7),(533,0,490,0,7),(102,128,793,0,4),(787,64,172,0,4)]
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
  | 14 => lookupWord 29 73 6 14 6 4 x511h14
  | 13 => lookupWord 152 573 6 17 9 4 x511h13
  | 12 => lookupWord 643 2415 7 19 11 4 x511h12
  | 11 => lookupWord 459 1723 7 18 10 4 x511h11
  | 10 => lookupWord 9 49 5 13 5 4 x511h10
  | 9 => lookupWord 1 3 1 9 1 4 x511h9
  | _ => fun _ => none
def x511 : Forest := ⟨1023,14,fun j => x511samples[j]?.getD (0,0),x511columns,x511autos,x511levels,x511index⟩
set_option maxHeartbeats 0 in
theorem geomx511 : graphValid x511 (boundsBefore knownx503) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
abbrev Positive := Excluded true
def rowWitness (g : Forest) (k i code : Nat) :=
  let pos := Fin.ofNat 512 ((code-1)%512)
  let negRow := Fin.ofNat 512 ((code-1)/512)
  bit pos (targetOf g) && !bit negRow (targetOf g) &&
    (stateSet g k i).all (fun w => !bit pos w || bit negRow w)

theorem rowWitness_ok {g k i code} (ok : rowWitness g k i code = true) :
    Positive (targetOf g) k (stateSet g k i).toFinset := by
  simp only [rowWitness,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at ok
  intro gates invs _ h none
  obtain ⟨a,mem,yes,no⟩ := mono_row_difference h (none rfl) ok.1.1 ok.1.2
  have z := ok.2 a (List.mem_toFinset.mp mem)
  simp only [yes,no] at z
  contradiction

def positiveCert (g : Forest) (hint : Nat → Nat → Nat) (k i : Nat) :=
  let code := hint k i
  if code=0 then cert g k i else rowWitness g k i code

theorem positiveForest (g : Forest) (hint : Nat → Nat → Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower (varsX q) (graphGoal q) (prior q))
    (geometry : graphValid g prior = true)
    (rows : ∀ k ≤ g.cap, ∀ i < (g.levels k).1, positiveCert g hint k i = true) :
    ∀ k ≤ g.cap, ∀ i < (g.levels k).1, Positive (targetOf g) k (stateSet g k i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hk i hi
    have r := rows k hk i hi
    simp only [positiveCert] at r
    split at r
    · apply checkedNode (binaryOnly:=true) g k i (chart_pairs geometry.1.1.1 geometry.1.1.2)
        (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2 _ (cert_ok r)
      exact fun h => ih (k-1) (by omega) (by omega)
    · exact rowWitness_ok r

def witness8 : Array Nat := [0x0].toArray
def witness9 : Array Nat := [0x1a004190132404150105404150108a04150105404150105404150105404190105404150106404450108a04c90105404450100000].toArray
def witness10 : Array Nat := [0x150105404150132407150105404648385404150105404c90105404150132404150105404150100000150105404190105404450106404150108a04c90105404450111404150105404,0x1501054042281054044501054043a0485404450105404150105404150106404228485404150100000150105404150111407150105404000032404150105404450100000648385404,0x150105404150105404150105404150111404150108a04150105404000008a0d150108a22c9013240415010e80d1510c5404150100000c901054041901114041901054048a0345404,0x1501000003a034e812150108a041501000001501e2812c901114044501114043a04854041501054048a0348a04000011404190106404150105404c901054046804854043a0345404,0x15010e8121501054041501114041501114040000114041542454041501064041501114071901054041501ce80d3a0480000150105404000005404150132404150111404000005404,0x150108a0415010540415010000015010000015010000015010e80d15011920ec910d1404450105404000005404c901000004501064041501000000000064044510f2404150108a04,0x4501054041901c640715010e81200000640422810e812150108a044501000001501064043a0485404150100000450100000228106404190105404150100000154240000150111404,0x154245404150105404190105404190132404000006404c90132404150122812150105404c90105404648105404000032404228485404000005404150105404228108a0d000000000,0x540415011140419010540415013240415010640419010540715010540415010e81215010540715424e812000005404c9010540415010e80d150105404228105404648106404,0x190105404190105404c90108a221501054042288a28123a04854043a03514042288854046801000001901114041501064046481000003a04914042288800008a0348a22190105404,0x1501054041901054071501000001510c5404450105404c90108a2215010540415010540415011140464c286404150108a041501054044501c5404000000000150106443150132404,0x150105404150105404344246404190106404000005404000005404450108a04150105404190105404150108a0415012280d150105407150100000150132404450108a0d150105404,0x150108a2200001a01282888540700000e8121501000001501054042281054071501054041501054041501054041501054043a04854040000114041501054041501054043a0485404,0x150105404150105404150132404450108a0d190105404c081114041501c540415010e80d19010540415011a01215010540415010540415011a01215010540415010000015010e812,0x150105404c90105404c901d1404150105404228105404150106404150111404150132404c90119204000005404150105404150106404150105404150111404150100000154245404,0x1501054043a034540415010000015010540468048540415012280d1501114042281054041501114071501054041501054043a0488a221501324044510c5404228345404190105404,0x150105404c90106404228105407450105404190100000150106404154245404150108a2215010e80d190132404c9010640415010540415011a0123a0345404450105404150108a0d,0x190108a22150108a0464812280d150105404c901054040000054048283914041501000001501054041501054041501114041901064043a0345404150105404680480000150105404,0x150108a221501054046804914042281324041542464041510d1404150108a041501228121501064121501054041501c540415011a0121901114041901c000015011a012c9010e812,0x1501000003a01c54041501054040000000002281054046481054041501064041501c5404150108a04450132404648105404150108a04150132404150100000190132404150105404,0x1501c5404150108a041901054044501064041501054042281324046481114043a0485404228340000000008a22150105404c901064041501114048a0345404150105404150108a04,0x15010000000000540422811140415010540422810e80d3a0488a221510c64042281064044501054042281114041501054042288864192281000001501da012150100000150106404,0x450111404450105404000005404150108a04150105404150100000c901324041501c540715010540719010e8121501c54043a03454041901d1404150105404c90105404000006404,0x154245404150105404150105404450100000150132404190111404228111404190105404150108a0d1501192041501054041501054041501054041901054041901c6404190105404,0x1501054041501d14041501054040000064043a0485404000005404150105407150132407000005404000008a0415010550915011a012228345404150108a04150105404228105404,0x1501192041501054041501c54041501000001501d14040000054043a034540400002280d150105404150105404150105404228106404150111404190111404c90106412150105404,0x8a04000005404c08105404150132404c90105404150105404000005404150106404,0x0,0x0,0x0].toArray
def witness11 : Array Nat := [0x150105404150108a2222888540400000540445011140415010540415010540415010540400000e812150105404150106404190100000190106404228105404450105404150105404,0x3a04800000000054041501c64041501054041901055091501054041901000001501054040000000001501054041501054041901192043a0485404150105404150105404228105404,0x5509000005404190105404150105404228105404228345404150108a0400000e80d150108a04c90105404190105404150105404150105404150105404228885404000000000,0x150105404150100000450105404150108a04190100000150105404150111404150132404450105404150111407150100000190105404190100000150105404150105404228345404,0x15011a012150105404190105404150100000000000000450111404c08105404150105404680491404c90100000150105404000032404c90105404000005404150105404c90105404,0xe80d1901054041501114041501054044501054041501054041901054071501054040000054043a0488a041501064040000228123a036280d450105404228880000150106404,0x680480000000005443190105404c901054041904854041901054041501114042281054042281054041501054040000054041501000003a03454041901c5404228106404150105404,0x1501054041501054044501c6404150106404c901064041501192041901324041501c540415010e8128a03454041501054041901c540415011140415013240445010000015010e80d,0x150105404c90108a0d1501054041501324041501054041501054041501054041901054041501000001501c5404150105404228105404c90105404450100000150105404190105404,0x2281054041901c6404000005404000005407150105404c901054041501000001501064041501054041501054040000055096481054041501054041501054041501114041510c0000,0x150108a041501064121501000001901054044501000004501054041510c540415010000000003240415010540415012280d150105404450122812228885404150111404190100000,0x6483854041501064044501054071501c5404150100000150106404450108a0415010540415010540415010540422810540415010000015010540415010e80d228105404190105404,0x8a04854041501054041501054040000054041901054041501054041501054041501054041501054041501054041901c0000150105404150111407150105404150105404190111404,0x15010540419010540415010540415011140415013240400000d1091901054041501054040000054040000000001501c54040000054043a04854043a04854041501000003a0486404,0x15010e80d150105404150100000150105404c9013240415010540415010540400000540400000000000000540415010540415010e80d15013240415010540415010e80d150105404,0x150105404150108a04150105404c90108a0415013240415013240445010540415013240400002280d6804854041501000001501054041501054042281054041501c5404228105404,0x6481000001501054043a04854041501054043a0485404150100000150105404150100000c0888540415010540400000e8120000054041501054043a048644315012281215010e812,0x150108a041501324043a0485404228100000150105404150105404c901054046804854043a4860a04c90106404150105404150105404150105404150105404150105407000005404,0x3a04854041901054041501054041501000003a035140415010540415010540400000e81215010540415011140415010540415013240415010e8121501054433a0348a0400000e812,0x8a03454040000054041501054041901054041501000003a048540415010540415010540415011140415010e81215010540400003240715010e80d15010540445010e812150132404,0xc90105404000000000150105404c901000001501054041542454044501c540415012280d00000540415010540445010e8120000054048a0485407150105404150105404150105404,0x3a048540415010540400000e81200003240415010e812c901054048a0485404450105404150105404190105404150105404150105404150105404150105404150105404000006404,0x15012281215010540415010000015011140415010640422812280d15010540415010d1091501054041501c5404150105404150105404150105404648105404150105404190108a0d,0x15010e80d1501054041501054041501054043a03454042281054041501054041501000008a04854041501000001901054041501054041901054040000054043a048540422810e812,0x190105404150120a2215010e812c90100000150108a2215010540400000540415010640715010540415010e812c90105404150106404000011404150111407c90105404228100000,0x1510c54041501054040000054041501c54043a0348a048a048540415010540415013240415010e8071501000001501054043a0485404150105407150105404150105404228105404,0x1501000001501054041901f240415010000015010540400000e80d15010e81215010e81222810540415010e8123a034641915010540415010640415010540415011a012150105404,0x54043a03454041501f24078281055093a048540415010000015010e80d15424540415010540415010540415010e8123a04914041501054042281054043a0480000680485404,0x15010e812000005404c901054041501054041501000003a0499204150122812150105404150119204150105404000005404648105404150105404190105404150105404228885404,0x1501054041501054041501324041501054043a048540415010540415011140400000e8121501054040000114043a0485404000005404150105404228100000150105404150105404,0x150108a224501054040000054041501054041501000003a03454041501054043a048000015010540415012281215010540415010e80dc901054041501054043a0345404150105404,0x15010540415010540422810e812450132443150108a0419010540415010000015010e80d1501000000000000001501054040000000000000054042281054041501ce80d150108a04,0x15010540419010540415010540400000000015010540400000540415010e812c90105404150105404150105404c9011140415010640719010540415010e812150105404150108a04,0x450105404000005407228885404150105404150100000150132404150132404c90108a04150105407150105404c90105404150120a22150105404150105404190105404150122812,0x1501054043a04914041501054041501054041501c540415010e80d1501114043a03400001901054041501000001501c54043a048000015010540415013240415010000015010e812,0x5404c08108a046481054041501324046481054040000054074510c54078a04854042281054041501054041501054040000054041901114041501114043a0480000150105404,0x150108a04190105404150105404150105404150105404150105404150105404c901054041501054043a03454041901054041501054071501000003a048540400000e812648885404,0x15010e8121501054041501000001501054071501064042281054041501000001901114041501302223a0485404150105404150105404150105404150105404c90105404150105404,0x15010e8121901000001501054043a04854040000000001501054041501054041501054041501054041501054043a0485404000005404c90105404150105404150105404c90105404,0x6404000005404150105404150105404150132404150105443150105404,0x0,0x0].toArray
def witness12 : Array Nat := [0x1501054041501c540415010540422812280d15010e8121501d14042281054043a0491404150105404150106404150100000150105404150106404450108a04150105404190105404,0x19010540415013240415012281215011140415010e812150105404150105404150105404228120a22150108a04150105404150105404150105404150105404150105404150100000,0x1901054041501064076481054041501054040000054043a04854044501c540415010540415010540415013240415010540415010640415010540415010000000000e80d150100000,0x15010640400000540415010540415010540415010e80d1501ce812150105404680485404150106404150105404190100000150105404150105404150100000150105404150105404,0x15010e8121501054041501000001501054042281000000000000003a048e80d228105404c9010000022810e812000000000150100000150105404150105404000005404150105404,0x3a04854041501000001501054041501054041501000001501054043a0485404150108a221501054040000054043a04854072281054043a048e812000005404150100000228105404,0x15010540700000e8120000000001501c54041510c544315010540415010540415010e812150105404150105404150108a221501c00001501054041501000001501054041501c0000,0x3a048e80d1501c000000000e80d1501c540415010e80d0000054043a048e80d15010000015010e81215010000015010e80d154248a04c901054043a0485404150100000150105404,0x5404150100000000005404c901054041501054041501054041510c5404150105404,0x0].toArray
def witness13 : Array Nat := [0x150108a041501054041510c540415010540415010e80d1501054043a04854041501ce812150105404150106404150105404150105404,0x0].toArray
def witness14 : Array Nat := [0x5404].toArray
def hints (k i : Nat) : Nat :=
  let words : Array Nat := match k with
    | 8 => witness8
    | 9 => witness9
    | 10 => witness10
    | 11 => witness11
    | 12 => witness12
    | 13 => witness13
    | 14 => witness14
    | _ => [].toArray
  ((words[i/32]?.getD 0) >>> (18*(i % 32))) &&& 262143
theorem byPieces {f : Nat → Bool} {n depth} (p : listPieces f (List.range n) depth) :
    ∀ i < n, f i = true := fun i hi => List.all_eq_true.mp (listPieces_all p) i (List.mem_range.mpr hi)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem rank8 : ∀ i < 1, positiveCert x511 hints 8 i = true := by
  apply byPieces (depth:=0)
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem rank9 : ∀ i < 29, positiveCert x511 hints 9 i = true := by
  apply byPieces (depth:=2)
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem rank10 : ∀ i < 932, positiveCert x511 hints 10 i = true := by
  apply byPieces (depth:=7)
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem rank11 : ∀ i < 1328, positiveCert x511 hints 11 i = true := by
  apply byPieces (depth:=7)
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem rank12 : ∀ i < 305, positiveCert x511 hints 12 i = true := by
  apply byPieces (depth:=5)
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem rank13 : ∀ i < 33, positiveCert x511 hints 13 i = true := by
  apply byPieces (depth:=2)
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem rank14 : ∀ i < 2, positiveCert x511 hints 14 i = true := by
  apply byPieces (depth:=0)
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
theorem topRows : ∀ k ≤ x511.cap, ∀ i < (x511.levels k).1, positiveCert x511 hints k i = true := by
  intro k hk
  change k ≤ 14 at hk
  interval_cases k
  · exact fun i hi => False.elim (Nat.not_lt_zero i hi)
  · exact fun i hi => False.elim (Nat.not_lt_zero i hi)
  · exact fun i hi => False.elim (Nat.not_lt_zero i hi)
  · exact fun i hi => False.elim (Nat.not_lt_zero i hi)
  · exact fun i hi => False.elim (Nat.not_lt_zero i hi)
  · exact fun i hi => False.elim (Nat.not_lt_zero i hi)
  · exact fun i hi => False.elim (Nat.not_lt_zero i hi)
  · exact fun i hi => False.elim (Nat.not_lt_zero i hi)
  · exact rank8
  · exact rank9
  · exact rank10
  · exact rank11
  · exact rank12
  · exact rank13
  · exact rank14
theorem signedRoot (i : Nat) (ws : List Sig) (idx : indexedRoot x511 14 i ws = true) :
    Positive (graphGoal 1023) 14 ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact positiveForest x511 hints _ (before_sound knownx503 validx503) geomx511 topRows 14 (by decide) i idx.1

def roots := rootB 1023

private lemma posBinary {w a b} (d : Bool) (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ (∃ e x y, x ∈ w ∧ y ∈ w ∧ proper x ∧ proper y ∧ x ≠ y ∧ bin d a b = bin e x y) := by
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
  exact Or.inr ⟨d,a,b,ham,hbm,hap,hbp,he,rfl⟩

private lemma pullPos {w : List Sig} {z : Sig} {k t S} (h : Live target k t S)
    (hz : represented w z ∨ (∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' S', k' ≤ k+1 ∧ Live target k' t S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
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
        exact ⟨_,_,Nat.le_refl _,Live.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

def PosReach (roots : List Sig) (p : Nat) (bank : List (Wire Row)) :=
  ∀ {k S}, Live graph k 0 S → (∀ a ∈ S, a ∈ bank.map table) →
    ∃ l U, l ≤ p+k ∧ Live graph l 0 U ∧ ∀ a ∈ U, a ∈ roots

theorem PosReach.start : PosReach roots 0 (roots.map observe) := by
  intro k S h hs
  refine ⟨k,S,by omega,h,?_⟩
  simpa [List.map_map,Function.comp_def,table_observe] using hs

theorem PosReach.two {roots p bank a b} (d : Bool) (reach : PosReach roots p bank)
    (ha : Available bank a) (hb : Available bank b) : PosReach roots (p+1) (combine d a b :: bank) := by
  intro k S h hs
  rw [List.map_cons,table_bin] at hs
  obtain ⟨m,U,hm,run,sub⟩ := pullPos h (posBinary d (available_rep ha) (available_rep hb))
    (fun a ha => by simpa [List.mem_cons,or_comm] using hs a ha)
  obtain ⟨l,V,hl,live,sv⟩ := reach run sub
  exact ⟨l,V,by omega,live,sv⟩

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem bound {p bank} (reach : PosReach roots p bank) (hit : Available bank (observe graph)) : 15 ≤ p := by
  have hm := available_rep hit
  rw [table_observe] at hm
  obtain ⟨k,S,hk,live,sub⟩ := reach (Live.stop graph_proper) (by simpa using hm.resolve_right (fun h => h graph_proper))
  have same : graph = graphGoal 1023 := by decide +kernel
  rw [same] at live
  by_contra! small
  have le : k ≤ 14 := by omega
  rcases strong_split (m:=1023) (hints:=13438558465) (nb:=1) (by decide +kernel) live sub with e|e|e
  · exact root_index (g:=dead) (before_sound known383 valid383) geomdead tablesdead (k:=14) (by decide)
      (i:=0) (ws:=vars 1023) (by decide +kernel) k 0 le (e ▸ live)
  · exact signedRoot 1 (rootB 1023) (by decide +kernel) k 0 le (e ▸ live) (fun _ => rfl)
  · exact signedRoot 0 (rootC 1023) (by decide +kernel) k 0 le (e ▸ live) (fun _ => rfl)

theorem input_mem (j : Fin 9) : inputs.getD j.val zero ∈ roots := by
  exact (by decide +kernel : ∀ j : Fin 9, inputs.getD j.val zero ∈ roots) j

theorem runSigned {n : Nat} (op : Fin n → Bool) (left right : Fin n → Nat × Bool)
    (v : (Fin 9 → Bool) → Nat → Bool)
    (back : ∀ j : Fin n, (left j).1 < 10+j.val ∧ (right j).1 < 10+j.val)
    (sign : ∀ j : Fin n, ((left j).2 = true → (left j).1 = 0 ∨ (left j).1 = 9) ∧
      ((right j).2 = true → (right j).1 = 0 ∨ (right j).1 = 9))
    (inp : ∀ x (j : Fin 9), v x j.val = x j) (cst : ∀ x, v x 9 = false)
    (gate : ∀ x (j : Fin n), v x (10+j.val) = if op j = true then
      (v x (left j).1 ^^ (left j).2) && (v x (right j).1 ^^ (right j).2) else
      (v x (left j).1 ^^ (left j).2) || (v x (right j).1 ^^ (right j).2)) :
    ∀ p ≤ n, ∃ bank, PosReach roots p bank ∧
      Available bank (observe seed) ∧ ∀ w < 10+p, Available bank (fun r => v (sample r) w) := by
  intro p
  induction p with
  | zero =>
    intro _
    refine ⟨_,PosReach.start,Or.inl (List.mem_map_of_mem (by decide +kernel : seed ∈ roots)),?_⟩
    intro w hw
    by_cases h : w < 9
    · let j : Fin 9 := ⟨w,h⟩
      have eq : (fun r => v (sample r) w) = observe (inputs.getD j.val zero) :=
        funext fun r => inp _ j
      exact eq ▸ Or.inl (List.mem_map_of_mem (input_mem j))
    · have eq : w=9 := by omega
      subst w
      exact Or.inr ⟨false,funext fun r => cst _⟩
  | succ p ih =>
    intro hp
    let j : Fin n := ⟨p,by omega⟩
    obtain ⟨bank,reach,seedIn,old⟩ := ih (by omega)
    let read := fun (w : Nat × Bool) (r : Row) => v (sample r) w.1 ^^ w.2
    have readOk (w : Nat × Bool) (hw : w.1 < 10+p) (hs : w.2=true → w.1=0 ∨ w.1=9) :
        Available bank (read w) := by
      obtain ⟨w,phase⟩ := w
      cases phase with
      | false => simpa [read] using old w hw
      | true =>
        rcases hs rfl with e|e
        · change w=0 at e
          subst w
          have eq : read (0,true) = observe seed := by
            funext r
            simp only [read,Bool.xor_true,observe,seed_table]
            exact congrArg Bool.not (inp (sample r) (0 : Fin 9))
          exact eq ▸ seedIn
        · change w=9 at e
          subst w
          exact Or.inr ⟨true,funext fun r => by simp [read,cst]⟩
    let out := combine (!(op j)) (read (left j)) (read (right j))
    have eq : (fun r => v (sample r) (10+p)) = out := by
      funext r
      have h := gate (sample r) j
      cases e : op j <;> simpa only [out,combine,e,read,Bool.not_false,Bool.not_true,
        Bool.false_eq_true,ite_true,ite_false] using h
    refine ⟨out::bank,PosReach.two _ reach (readOk _ (back j).1 (sign j).1)
      (readOk _ (back j).2 (sign j).2),available_cons _ seedIn,?_⟩
    intro w hw
    by_cases h : w = 10+p
    · subst w
      rw [eq]
      exact Or.inl List.mem_cons_self
    · exact available_cons _ (old _ (by omega))

end PEqualNP.Outside.L_meta_4269

theorem PEqualNP.Outside.L_meta_4269 : ∀ (x1 : ℕ) (x2 : Fin x1 → Bool) (x3 x4 : Fin x1 → ℕ × Bool) (x5 : Finset ℕ) (x6 : (Fin (9 : ℕ) → Bool) → ℕ → Bool),   (0 : ℕ) < x1 →     x5.card ≤ (3 : ℕ) →       x1 + x5.card ≤ (14 : ℕ) →         x5.card ≤ (1 : ℕ) →           x5.card = (0 : ℕ) →             (∀ (x12 : Fin x1), (x3 x12).1 < (10 : ℕ) + ↑x12 ∧ (x4 x12).1 < (10 : ℕ) + ↑x12) →               (∀ (x13 : Fin (9 : ℕ)), ∃ (x14 : Fin x1), (x3 x14).1 = ↑x13 ∨ (x4 x14).1 = ↑x13) →                 (∀ (x14 : ℕ), x14 ∈ x5 ↔ x14 ≠ (0 : ℕ) ∧ x14 ≠ (9 : ℕ) ∧ (Bool.false = Bool.true ∧ x14 = (9 : ℕ) + x1 ∨ ∃ (x15 : Fin x1), x3 x15 = (x14, Bool.true) ∨ x4 x15 = (x14, Bool.true))) →                   (∀ (x15 : Fin (9 : ℕ) → Bool) (x16 : Fin (9 : ℕ)), x6 x15 ↑x16 = x15 x16) →                     (∀ (x16 : Fin (9 : ℕ) → Bool), x6 x16 (9 : ℕ) = Bool.false) →                       (∀ (x17 : Fin (9 : ℕ) → Bool) (x18 : Fin x1),                           have x19 : ℕ × Bool → Bool := fun (x19 : ℕ × Bool) => x6 x17 x19.1 ^^ x19.2;                           x6 x17 ((10 : ℕ) + ↑x18) = if x2 x18 = Bool.true then x19 (x3 x18) && x19 (x4 x18) else x19 (x3 x18) || x19 (x4 x18)) →                         ∃ (x18 : Fin (9 : ℕ) → Bool), (x6 x18 ((9 : ℕ) + x1) ^^ Bool.false) ≠ [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x19 : ℕ) => x18 (Fin.ofNat (9 : ℕ) (x19 / (10 : ℕ))) && x18 (Fin.ofNat (9 : ℕ) (x19 % (10 : ℕ))) := by
  intro n op left right paid val hn _ budget _ empty back _ membership input constant gate
  by_contra noMismatch
  have sign (wire : ℕ × Bool) (used : ∃ j : Fin n, left j = wire ∨ right j = wire)
      (negative : wire.2 = true) : wire.1 = 0 ∨ wire.1 = 9 := by
    by_contra! bad
    have mem := (membership wire.1).mpr ⟨bad.1,bad.2,Or.inr (by simpa only [←negative,Prod.mk.eta] using used)⟩
    rw [Finset.card_eq_zero.mp empty] at mem
    exact Finset.notMem_empty _ mem
  obtain ⟨bank,reach,_,wires⟩ := PEqualNP.Outside.L_meta_4269.runSigned op left right val back
    (fun j => ⟨sign _ ⟨j,Or.inl rfl⟩,sign _ ⟨j,Or.inr rfl⟩⟩) input constant gate n le_rfl
  have out := wires (9+n) (by omega)
  have eq : (fun r => val (PEqualNP.Outside.L_meta_4269.sample r) (9+n)) =
      PEqualNP.Outside.L_meta_4269.observe PEqualNP.Outside.L_meta_4269.graph := by
    funext r
    let y := PEqualNP.Outside.L_meta_4269.sample r
    have h := Classical.byContradiction fun mismatch => noMismatch ⟨y,mismatch⟩
    rw [PEqualNP.Outside.L_meta_4269.observe,PEqualNP.Outside.L_meta_4269.edge_table]
    change val y (9+n) = PEqualNP.Outside.L_meta_4269.edge y
    simp only [List.any_cons,List.any_nil,Bool.xor_false,Bool.or_false] at h
    exact h.trans (by simp only [PEqualNP.Outside.L_meta_4269.edge,Bool.or_assoc]; rfl)
  rw [eq] at out
  have lower := PEqualNP.Outside.L_meta_4269.bound reach out
  omega
