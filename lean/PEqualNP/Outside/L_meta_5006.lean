import Mathlib
import PEqualNP.Defs

-- This file reuses, unchanged, the accepted proof L-meta-1938 (whose own credits follow),
-- then reads the offered OR(x_0, x_j) as an extra first gate, as L-meta-1938 does.

-- The live-wire calculus and the ordinary induced-graph certificates are from
-- PressF10’s L-meta-1667. The gate-pair test is adapted from L-meta-2303.
-- Runs omitting the complement of vertex zero obey the ordinary bound.
-- For the remaining runs, restricting inputs gives smaller graphs with
-- either both signs of that vertex or just its complement. The tables
-- certify each surviving gate and its retained inputs. The resulting
-- fifteen-gate bound applies before the offered OR is added.
namespace PEqualNP.Outside.L_meta_5006
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Bool) (a b : Sig) : Sig := if d then a ||| b else a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
private theorem bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]

inductive Live (target : Sig) : Nat → Nat → Finset Sig → Prop
  | stop (hp : proper target) : Live target 0 0 {target}
  | unary {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live target k t (insert (neg a) U)) :
      Live target (k+1) (t+1) (insert a U)
  | binary {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live target k t (insert (bin d a b) U)) :
      Live target (k+1) t (insert a (insert b U))

private lemma live_proper {k t S} (h : Live target k t S) : ∀ a ∈ S, proper a := by
  induction h with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {k t S} (h : Live target k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h with
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

inductive Reach {R} (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | start : Reach roots 0 roots
  | one {p bank a} : Reach roots p bank → Available bank a →
      Reach roots (p+1) (inv a :: bank)
  | two {p bank a b} (op : Bool) : Reach roots p bank → Available bank a →
      Available bank b → Reach roots (p+1) (combine op a b :: bank)

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

inductive Run {R} (goal : Wire R) : Nat → List (Wire R) → Prop
  | stop : Run goal 0 [goal]
  | perm {s xs zs} : xs.Perm zs → Run goal s xs → Run goal s zs
  | one {s a rest} (save : Bool) : Run goal s (inv a :: kept save a rest) →
      Run goal (s+1) (a::rest)
  | two {s a b rest} (op ka kb : Bool) :
      Run goal s (combine op a b :: kept ka a (kept kb b rest)) →
      Run goal (s+1) (a::b::rest)

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
  induction h generalizing p bank with
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
  induction h with
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
  induction h generalizing v with
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
  induction h generalizing k t S with
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
  induction h with
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
def seed : Sig := 0x88888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888

def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem seed_table : ∀ r : Row, bit r seed = (sample r 0 && sample r 1) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem seed_nonzero : seed ≠ zero := by decide +kernel
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
  induction h with
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
  induction h with
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
  cases h with
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
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero
def vars (m : Nat) :=
  let raw := (selected m).map Prod.snd
  if m.testBit 13 && m.testBit 0 then raw.drop 1 ++ [neg (vertex m 0)]
  else if m.testBit 11 then raw ++ [neg (vertex m 0)] else raw
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

def polarPairs (m : Nat) (xs : List (Sig × Row × Row)) :=
  if m.testBit 13 then xs.map (fun (a,r,s) =>
    (if a == inputs.getD 0 zero then neg a else a,r,s)) else xs

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
def chartGoal (m : Nat) : Sig :=
  if m=1023 then graphGoal m &&& ~~~seed else graphGoal m
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (chartGoal m)
  let xs := polarPairs m (supportPairs s)
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
  let xs := polarPairs m (supportPairs s)
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

-- Bit eleven supplies the complement of vertex zero. Bit twelve of a
-- restriction selects the bound with that extra signal available.
-- Bits thirteen and fourteen select the corresponding bounds in which
-- only the complement is supplied.
def poolMask (m : Nat) (c : ColumnInfo) :=
  if !(m.testBit 11 || m.testBit 13) then m
  else if c.1.testBit 14 then m % 512 + 8192
  else if c.1.testBit 12 then m % 512 + 2048 else m % 512

def poolColumn (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) :=
  (chartGoal (poolMask m c) == chartGoal m) && colCheck (poolMask m c) c prior

theorem poolColumn_sound {m} (c : ColumnInfo) (prior : Nat → Nat)
    (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (ok : poolColumn m c prior = true) :
    Slice (vars (poolMask m c)) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  obtain ⟨same,h⟩ := Bool.and_eq_true_iff.mp ok
  rw [←beq_iff_eq.mp same]
  exact col_sound c prior low h

def relabelOK (old rep : Nat) (swaps : List Nat) :=
  properB (graphGoal old) && properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (vars old) (graphGoal old) (vars rep) (graphGoal rep)
theorem relabel_of {old rep L swaps} (ok : relabelOK old rep swaps = true)
    (h : Lower (vars rep) (graphGoal rep) L) : Lower (vars old) (graphGoal old) L := by
  simp only [relabelOK,Bool.and_eq_true] at ok
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


structure BoundPool where
  domain : Sig
  bound : Nat
  paid : Nat
  wires : List Sig

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
    cases h
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


inductive IndexTree (α : Type) where
  | leaf (items : List α)
  | fork (pivot : Nat) (left right : IndexTree α)
def IndexTree.read {α} : IndexTree α → Nat → Option α
  | .leaf xs,i => xs[i]?
  | .fork pivot a b,i => if i<pivot then a.read i else b.read (i-pivot)
def IndexTree.values {α} : IndexTree α → List α
  | .leaf xs => xs
  | .fork _ a b => a.values ++ b.values
theorem IndexTree.read_mem {α} (tree : IndexTree α) {i x} (e : tree.read i=some x) :
    x ∈ tree.values := by
  induction tree generalizing i with
  | leaf xs => exact List.mem_of_getElem? e
  | fork pivot a b ia ib =>
    simp only [IndexTree.read] at e
    split at e
    · exact List.mem_append_left _ (ia e)
    · exact List.mem_append_right _ (ib e)

structure Forest where
  mask : Nat
  cap : Nat
  samples : Nat → Bits × Bits
  cols : IndexTree ColumnInfo
  autos : Array (List Nat)
  levels : Nat → Packing
  index : Nat → Nat → Option (Nat × Nat)

def wiresOf (g : Forest) :=
  let ws := rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  let nonedge := dneg (dbin false (ws.getD 0 defaultDecor) (ws.getD 1 defaultDecor))
  if g.mask=1023 then ws.map (fun w => dbin false w nonedge) else ws
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a := by
  have base := raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  intro a ha
  unfold wiresOf at ha
  split at ha
  · obtain ⟨w,hw,rfl⟩ := List.mem_map.mp ha
    exact faithful_bin false (base w hw) (faithful_neg (faithful_bin false
      (faithful_get base 0) (faithful_get base 1)))
  · exact base _ ha

def targetOf (g : Forest) := chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) :=
  if m=1023 then liftGoal m v &&& ~~~(v 0 &&& v 1) else liftGoal m v
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  by_cases e : m=1023
  · have u := asRow_bit v i (0 : Fin 9)
    have w := asRow_bit v i (1 : Fin 9)
    have h := bit_liftGoal m v i
    change (inputs.getD 0 zero).getLsbD (asRow v i).val = (v 0).getLsbD i.val at u
    change (inputs.getD 1 zero).getLsbD (asRow v i).val = (v 1).getLsbD i.val at w
    have seedEq : seed = inputs.getD 0 zero &&& inputs.getD 1 zero := by decide +kernel
    simp only [chartGoal,chartSamples,e,ite_true,bit,seedEq,BitVec.getLsbD_and,
      BitVec.getLsbD_not,(asRow v i).isLt,i.isLt,decide_true,Bool.true_and,u,w] at h ⊢
    rw [h]
  · simpa only [chartGoal,chartSamples,e,ite_false] using bit_liftGoal m v i
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
  (g.cols.read idx).bind fun ci =>
    materialize (vars (poolMask g.mask ci)) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2

theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols.values, Slice (vars (poolMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : buildRule g ops depth bank i paid = some c) :
    ValidPool (vars g.mask) (targetOf g) c := by
  unfold buildRule at h
  cases e : g.cols.read i with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    exact materialize_sound (raw:=vars (poolMask g.mask ci)) (cols ci (g.cols.read_mem e)) h

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
    (cols : ∀ ci ∈ g.cols.values, Slice (vars (poolMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
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
    cases h
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
  g.cols.values.all (fun c => poolColumn g.mask c prior) &&
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
      (fun x hx => poolColumn_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact block_at (rows 0 hk) i (by omega) (by omega)
  | succ k ih =>
    intro hk i hi
    apply nodeVerified_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => poolColumn_sound _ prior lower (geometry.1.2 x hx)) geometry.2
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
def extendKnown (old : List (Nat × Nat)) (L : Nat) (relabels : List (Nat × List Nat)) :=
  relabels.map (fun v => (v.1,L)) ++ old
theorem extendKnown_ok {old L m relabels} (previous : Known old)
    (main : Lower (vars m) (graphGoal m) L)
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
abbrev Memo2303 := Sig × Nat × Nat × List Sig × List Sig

def memo2303 (ws : List Decor) (k : Nat) (p : BoundPool) : Memo2303 :=
  let d := p.domain
  let av := p.wires.map (masked d)
  let clean := fun (w : Sig) => let y := masked d w
                                y==zero || y==d || av.contains y
  (d,k+p.paid,p.bound+ws.countP (fun w => isMaskedConstant d w.1),
    av,(ws.map Prod.fst).filter (fun w => !(clean w)))

def worth2303 (cap n : Nat) (cov : CovPair) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let un := op==2
  let len := 1+(n-(if ka then 0 else 1)-(if un || kb then 0 else 1))
  if len>cap then false else
  let d := len==cap
  (restCov (getCov cov d) (column d a.2) (column d b.2) un ka kb ||| column d z.2) == BitVec.allOnes 768

abbrev Ax2303 := Decor × Decor

abbrev Four2303 := Nat × Nat × Nat × Nat

def couples2303 : List Decor → List Ax2303
  | [] => []
  | a::l => l.map (fun b => (a,b)) ++ couples2303 l

def liftSig2303 (w : Sig) : Bits := BitVec.ofNat 768 w.toNat

def laneEq2303 (r full a b : Nat) := fullMarks r (full ^^^ (a ^^^ b))

def zeroFour2303 (x : Four2303) := (x.1 ||| x.2.1 ||| x.2.2.1 ||| x.2.2.2)==0

def wideWorth2303 (n cap op r full : Nat) (v : CovPair) (a b : PackedSig) (ka kb : Bool) :=
  let un := op==2
  let len := 1+(n-(if ka then 0 else 1)-(if un || kb then 0 else 1))
  if len>cap then 0 else
  let d := len==cap
  let c := getCov v d
  let cover : PackedCov := (r*c.1.toNat,r*c.2.1.toNat,r*c.2.2.toNat)
  fullMarks r (takePacked cover (packedColumn d a) (packedColumn d b) un ka kb |||
    packedColumn d (packedOp full op a b))

def include2303 (r full z : Nat) (wires : List Sig) (seen : Nat) :=
  wires.foldl (fun m w => m ||| laneEq2303 r full z (r*w.toNat)) seen

def maskKeep2303 (r full a b : Nat) (un ka kb : Bool) (miss : List Sig) :=
  miss.foldl (fun m w =>
    let target := r*w.toNat
    m &&& ((if ka then 0 else laneEq2303 r full a target) |||
      (if un || kb then 0 else laneEq2303 r full b target))) r

def shade2303 (r cost top cv free : Nat) (ready : Bool) (loss : Nat) :=
  if ready && cost+loss+1<top then r else
  if cost+loss<top then free else if cost+loss==top then cv else 0

def wideRule2303 (r full a b z : Nat) (un : Bool) (ps : Memo2303) (todo : Four2303) : Four2303 :=
  let (dom,cost,top,av,miss) := ps
  if cost>=top+1 || miss.length>(if un then 1 else 2) then todo else
  let d := r*dom.toNat
  let cm := fun m => laneEq2303 r full m 0 ||| laneEq2303 r full m d
  let zm := z &&& d
  let cz := cm zm
  let free := include2303 r full zm av cz
  let shade := shade2303 r cost top cz free miss.isEmpty
  let ca := cm (a &&& d)
  let cb := cm (b &&& d)
  let step := fun (t : Nat) (ka kb : Bool) =>
    if t==0 then 0 else
    let ca := if ka then 0 else ca
    let cb := if un || kb then 0 else cb
    let kill := (((r ^^^ (ca ||| cb)) &&& shade 0) |||
      ((ca ^^^ cb) &&& shade 1) ||| ((ca &&& cb) &&& shade 2)) &&&
      maskKeep2303 r full a b un ka kb miss
    t ^^^ (t &&& kill)
  (step todo.1 false false,step todo.2.1 true false,step todo.2.2.1 false true,step todo.2.2.2 true true)

def wideRules2303 (r full a b z : Nat) (un : Bool) (todo : Four2303) : List Memo2303 → Four2303
  | [] => todo
  | p::ps => if zeroFour2303 todo then todo else wideRules2303 r full a b z un (wideRule2303 r full a b z un p todo) ps

lemma keyFold2303 (ws : List Sig) (c : Nat) :
    ws.foldl (fun v w => v+keyWord w) c=c+(ws.map keyWord).sum := by
  induction ws generalizing c with
  | nil => simp
  | cons w l ih => simp [ih,Nat.add_assoc]
lemma keySum2303 (ws : List Sig) : keySet ws=(ws.map keyWord).sum := by
  simp [keySet,keyFold2303]
lemma keyPerm2303 {ws vs : List Decor} (h : ws.Perm vs) :
    keySet (ws.map Prod.fst)=keySet (vs.map Prod.fst) := by
  rw [keySum2303,keySum2303]
  exact ((h.map Prod.fst).map keyWord).sum_eq
lemma keyCons2303 (a : Sig) (ws : List Sig) : keySet (a::ws)=keyWord a+keySet ws := by
  simp [keySum2303]
def deltaKey2303 (total : Nat) (a b z : Sig) (un ka kb : Bool) :=
  total+keyWord z-(if ka then 0 else keyWord a)-(if un || kb then 0 else keyWord b)
lemma deltaKey_ok2303 {ws : List Decor} {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (un ka kb : Bool) (ne : un=false → a≠b) (z : Sig) :
    deltaKey2303 (keySet (ws.map Prod.fst)) a.1 b.1 z un ka kb =
      keySet (z::(opKeep un ka kb a b ws).map Prod.fst) := by
  have first := keyPerm2303 (delOne_perm a ha)
  have second := keyPerm2303 (delOne_perm b hb)
  simp only [List.map_cons,keyCons2303] at first second
  cases un
  · have both := keyPerm2303 (delTwo_perm a b ha hb (ne rfl))
    simp only [List.map_cons,keyCons2303] at both
    cases ka <;> cases kb <;>
      simp only [deltaKey2303,opKeep,delOne,delTwo,Bool.false_or,Bool.false_eq_true,
        ite_false,ite_true,keyCons2303] <;> omega
  · cases ka <;> cases kb <;>
      simp only [deltaKey2303,opKeep,delOne,Bool.true_or,Bool.false_eq_true,ite_false,
        ite_true,keyCons2303] <;> omega

def linked2303 (ws : List Decor) (links : Nat → List (List Sig)) (a b : Decor) (w : Sig)
    (un ka kb : Bool) :=
  let other := (opKeep un ka kb a b ws).map Prod.fst
  let st := w::other
  let tag := if un || a.1!=b.1 then deltaKey2303 (keySet (ws.map Prod.fst)) a.1 b.1 w un ka kb else keySet st
  (links tag).any (fun v => v==other++[w] || sameWords st v)

lemma linked_ok2303 {ws links a b w un ka kb} (ha : a∈ws) (hb : b∈ws)
    (ok : linked2303 ws links a b w un ka kb=true) :
    let st := w::(opKeep un ka kb a b ws).map Prod.fst
    (links (keySet st)).any (sameWords st)=true := by
  let rest := (opKeep un ka kb a b ws).map Prod.fst
  have key : (if un || a.1!=b.1 then deltaKey2303 (keySet (ws.map Prod.fst)) a.1 b.1 w un ka kb
        else keySet (w::rest))=keySet (w::rest) := by
    split
    next h =>
      apply deltaKey_ok2303 ha hb
      intro hu eq
      simp [hu,eq] at h
    next => rfl
  change (links _).any (fun v => v==rest++[w] || sameWords (w::rest) v)=true at ok
  rw [key] at ok
  obtain ⟨v,vm,hit⟩ := List.any_eq_true.mp ok
  refine List.any_eq_true.mpr ⟨v,vm,?_⟩
  simp only [Bool.or_eq_true] at hit
  rcases hit with eq | yes
  · rw [beq_iff_eq.mp eq]
    simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq,
      List.mem_cons,List.mem_append,List.not_mem_nil,or_false]
    exact ⟨fun _ e => e.symm,fun _ e => e.symm⟩
  · exact yes

def wideFamily2303 (c : NodeContext) (ps : List Memo2303) (op : Nat) (ops : List Ax2303) :=
  let (cap,n,ws,cov,_,links) := c
  let r := units ops.length
  let full := r*(BitVec.allOnes 768).toNat
  let sa := packedSig (fun e : Ax2303 => e.1.2) ops
  let sb := packedSig (fun e : Ax2303 => e.2.2) ops
  let a := combineLanes (fun e : Ax2303 => liftSig2303 e.1.1) ops
  let b := combineLanes (fun e : Ax2303 => liftSig2303 e.2.1) ops
  let un := op==2
  let z := if un then (r*one.toNat) ^^^ a else if op==1 then a ||| b else a &&& b
  let worth := wideWorth2303 n cap op r full cov sa sb
  let todo : Four2303 := (worth false false,if un then 0 else worth true false,
                       if un then 0 else worth false true,worth true true)
  let left := wideRules2303 r full a b z un todo ps
  let verify := fun (ka kb : Bool) (t : Nat) => if t==0 then true else
    onMarks (fun e : Ax2303 =>
      let w := (movedDecor op e.1 e.2).1
      if !properB w || ws.any (fun v => v.1==w) then true else
      linked2303 ws links e.1 e.2 w un ka kb) t ops
  verify false false left.1 && verify true false left.2.1 &&
    verify false true left.2.2.1 && verify true true left.2.2.2

def wideNode2303 (T : Sig) (c : NodeContext) :=
  let ws := c.2.2.1
  let ss := c.2.2.2.2.1.map (memo2303 ws (c.1-1))
  let bs := couples2303 ws
  prelim T c && wideFamily2303 c ss 2 (ws.map fun a => (a,a)) &&
    wideFamily2303 c ss 0 bs && wideFamily2303 c ss 1 bs

lemma xorHit2303 (a b : Bits) :
    (BitVec.allOnes 768 ^^^ (a ^^^ b) == BitVec.allOnes 768) = (a==b) := by
  by_cases eq : a=b
  · simp [eq]
  · rw [beq_eq_false_iff_ne.mpr eq]
    apply beq_eq_false_iff_ne.mpr
    intro h
    apply eq
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have v := congrArg (fun x : Bits => x.getLsbD j) h
    simp only [BitVec.getLsbD_xor,BitVec.getLsbD_allOnes,hj,decide_true] at v
    cases ha : a.getLsbD j <;> cases hb : b.getLsbD j <;> simp_all

lemma eqLanes2303 {α} (a b : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (laneEq2303 (units xs.length) (units xs.length*(BitVec.allOnes 768).toNat)
      (combineLanes a xs) (combineLanes b xs)).testBit (769*i) = (a xs[i] == b xs[i]) := by
  simp only [laneEq2303,broadcast,lanes_xor,mark_at _ _ _ hi,xorHit2303]

lemma liftEq2303 (a b : Sig) : (liftSig2303 a==liftSig2303 b)=(a==b) := by
  by_cases e : a=b
  · simp [e]
  · have neq : liftSig2303 a≠liftSig2303 b := by
      intro h
      have H := congrArg BitVec.toNat h
      have la : a.toNat<2^768 := lt_trans a.isLt (by decide +kernel)
      have lb : b.toNat<2^768 := lt_trans b.isLt (by decide +kernel)
      apply e
      apply BitVec.eq_of_toNat_eq
      simpa [liftSig2303,Nat.mod_eq_of_lt la,Nat.mod_eq_of_lt lb] using H
    simp [neq,e]

lemma lift_toNat2303 (a : Sig) : (liftSig2303 a).toNat=a.toNat := by
  have lt : a.toNat<2^768 := lt_trans a.isLt (by decide +kernel)
  simp [liftSig2303,Nat.mod_eq_of_lt lt]

lemma bitEqConst2303 {α} (a : α → Sig) (v : Sig) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (laneEq2303 (units xs.length) (units xs.length*(BitVec.allOnes 768).toNat)
      (combineLanes (fun x => liftSig2303 (a x)) xs) (units xs.length*v.toNat)).testBit (769*i) =
      (a xs[i]==v) := by
  rw [←lift_toNat2303 v,broadcast (liftSig2303 v) xs,eqLanes2303 _ _ _ _ hi,liftEq2303]

lemma worthAt2303 (n cap op : Nat) (v : CovPair) (xs : List Ax2303) (i : Nat) (hi : i<xs.length)
    (ka kb : Bool) :
    (wideWorth2303 n cap op (units xs.length) (units xs.length*(BitVec.allOnes 768).toNat) v
      (packedSig (fun e : Ax2303 => e.1.2) xs) (packedSig (fun e : Ax2303 => e.2.2) xs)
      ka kb).testBit (769*i) =
      worth2303 cap n v op xs[i].1 xs[i].2 (movedDecor op xs[i].1 xs[i].2) ka kb := by
  let len := 1+(n-(if ka then 0 else 1)-(if (op==2) || kb then 0 else 1))
  by_cases big : len>cap
  · simp only [wideWorth2303,worth2303,show 1+(n-(if ka then 0 else 1)-
        (if (op==2) || kb then 0 else 1))>cap from big,ite_true,Nat.zero_testBit]
  · let d := len==cap
    simp only [wideWorth2303,worth2303,show ¬1+(n-(if ka then 0 else 1)-
        (if (op==2) || kb then 0 else 1))>cap from big,ite_false]
    have cp : (units xs.length*(getCov v d).1.toNat,units xs.length*(getCov v d).2.1.toNat,
        units xs.length*(getCov v d).2.2.toNat) =
        packedCov (fun _ : Ax2303 => getCov v d) xs := by simp only [packedCov,broadcast]
    rw [cp,packed_op (fun e : Ax2303 => e.1) (fun e : Ax2303 => e.2),packed_column,
        packed_column,packed_column,takePacked_ok,lanes_or,mark_at _ _ _ hi]

lemma includeBit2303 {α} (f : α → Sig) (vs : List Sig) (xs : List α) (i) (hi : i<xs.length)
    (seen : Nat) :
    (include2303 (units xs.length) (units xs.length*(BitVec.allOnes 768).toNat)
      (combineLanes (fun x => liftSig2303 (f x)) xs) vs seen).testBit (769*i) =
    (seen.testBit (769*i) || vs.any (fun w => f xs[i]==w)) := by
  induction vs generalizing seen with
  | nil => simp [include2303]
  | cons w l ih =>
    change (include2303 _ _ _ l _).testBit _ = _
    rw [ih,Nat.testBit_or,bitEqConst2303 _ _ _ _ hi,List.any_cons,Bool.or_assoc]

lemma keepBit2303 (xs : List Ax2303) (i) (hi : i<xs.length) (miss : List Sig) (un ka kb : Bool) :
    (maskKeep2303 (units xs.length) (units xs.length*(BitVec.allOnes 768).toNat)
      (combineLanes (fun e : Ax2303 => liftSig2303 e.1.1) xs)
      (combineLanes (fun e : Ax2303 => liftSig2303 e.2.1) xs) un ka kb miss).testBit (769*i) =
      miss.all (fun w => (!ka && (xs[i].1.1==w)) || (!(un || kb) && (xs[i].2.1==w))) := by
  let r := units xs.length
  let full := r*(BitVec.allOnes 768).toNat
  let a := combineLanes (fun e : Ax2303 => liftSig2303 e.1.1) xs
  let b := combineLanes (fun e : Ax2303 => liftSig2303 e.2.1) xs
  let f := fun (w : Sig) => (if ka then 0 else laneEq2303 r full a (r*w.toNat)) |||
       (if un || kb then 0 else laneEq2303 r full b (r*w.toNat))
  have get (w) : (f w).testBit (769*i)=
      ((!ka && (xs[i].1.1==w)) || (!(un || kb) && (xs[i].2.1==w))) := by
    cases ka <;> cases un <;> cases kb <;>
      simp only [f,r,full,a,b,Nat.testBit_or,bitEqConst2303 _ _ _ _ hi,
        Bool.false_eq_true,ite_false,ite_true,Bool.false_or,Bool.true_or,
        Nat.zero_testBit,Bool.not_true,Bool.not_false,Bool.false_and,Bool.true_and]
  have aux (l : List Sig) (m : Nat) : (l.foldl (fun q w => q &&& f w) m).testBit (769*i)=
      (m.testBit (769*i) && l.all fun w => (!ka && (xs[i].1.1==w)) || (!(un || kb) && (xs[i].2.1==w))) := by
    induction l generalizing m with
    | nil => simp
    | cons w l ih => rw [List.foldl_cons,ih,Nat.testBit_and,get,List.all_cons,Bool.and_assoc]
  exact (aux miss r).trans (by simp [r,unit_bit _ _ hi])

lemma liftedAnd2303 (a b : Sig) : liftSig2303 (a &&& b) = liftSig2303 a &&& liftSig2303 b := by
  apply BitVec.eq_of_toNat_eq
  simp only [lift_toNat2303,BitVec.toNat_and]

lemma liftedOr2303 (a b : Sig) : liftSig2303 (a ||| b) = liftSig2303 a ||| liftSig2303 b := by
  apply BitVec.eq_of_toNat_eq
  simp only [lift_toNat2303,BitVec.toNat_or]

lemma liftedNeg2303 (a : Sig) : liftSig2303 (neg a) = liftSig2303 one ^^^ liftSig2303 a := by
  have eq : neg a=one ^^^ a := BitVec.allOnes_xor.symm
  apply BitVec.eq_of_toNat_eq
  simp only [eq,lift_toNat2303,BitVec.toNat_xor]

lemma maskedLanes2303 {α} (a : α → Sig) (xs : List α) (d : Sig) :
    combineLanes (fun x => liftSig2303 (a x)) xs &&& (units xs.length*d.toNat) =
      combineLanes (fun x => liftSig2303 (masked d (a x))) xs := by
  rw [←lift_toNat2303 d,broadcast (liftSig2303 d) xs,lanes_and]
  simp only [masked,liftedAnd2303,BitVec.and_comm]

lemma opLanes2303 (xs : List Ax2303) (op : Nat) :
    let a := combineLanes (fun e : Ax2303 => liftSig2303 e.1.1) xs
    let b := combineLanes (fun e : Ax2303 => liftSig2303 e.2.1) xs
    (if op==2 then (units xs.length*one.toNat) ^^^ a else if op==1 then a ||| b else a &&& b) =
      combineLanes (fun e : Ax2303 => liftSig2303 (movedDecor op e.1 e.2).1) xs := by
  by_cases un : op=2
  · simp only [un,beq_self_eq_true,ite_true,movedDecor,codeDecor,dneg,liftedNeg2303]
    rw [←lift_toNat2303 one,broadcast (liftSig2303 one) xs,lanes_xor]
  · have ne : (op==2)=false := beq_eq_false_iff_ne.mpr un
    cases b : op==1 <;>
      simp only [ne,Bool.false_eq_true,ite_false,b,ite_true,movedDecor,codeDecor,un,dbin,bin,
        liftedOr2303,liftedAnd2303,lanes_or,lanes_and]

def absent2303 (p : BoundPool) (ws : List Decor) :=
  (ws.map Prod.fst).filter (fun w => !availableB p.domain p.wires w)

def payable2303 (cost top : Nat) (zc free ready : Bool) (loss : Nat) :=
  if ready && cost+loss+1<top then true else
  if cost+loss<top then free else if cost+loss==top then zc else false

lemma scalar_fast2303 {p : BoundPool} {ws : List Decor} {k op a b ka kb}
    (nd : (ws.map Prod.fst).Nodup) (ha : a∈ws) (hb : b∈ws)
    (keep : (absent2303 p ws).all (fun w =>
      (!ka && (a.1==w)) || (!((op==2) || kb) && (b.1==w)))=true)
    (test : let const := fun w : Decor => isMaskedConstant p.domain w.1
      let z := choiceVal (movedChoice op a b)
      payable2303 (k+p.paid) (p.bound+ws.countP const) (isMaskedConstant p.domain z)
        (availableB p.domain p.wires z) (absent2303 p ws).isEmpty
        (constantLoss const a ka+constantLoss const b ((op==2)||kb))=true) :
    scalarPoolCut p k ((opKeep (op==2) ka kb a b ws).map Prod.fst) (movedChoice op a b)=true := by
  let z := choiceVal (movedChoice op a b)
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let rest := opKeep (op==2) ka kb a b ws
  let miss := absent2303 p ws
  let loss := constantLoss const a ka+constantLoss const b ((op==2)||kb)
  have failed {v} (hm : v∈ws.map Prod.fst) (no : availableB p.domain p.wires v=false) : v∈miss := by
    simpa [miss,absent2303,List.mem_filter,hm,no]
  have known : (rest.map Prod.fst).all (availableB p.domain p.wires)=true := by
    apply List.all_eq_true.mpr
    intro v vm
    obtain ⟨member,ia,ib⟩ := (kept_value nd ha hb (op==2) ka kb v).mp vm
    cases ev : availableB p.domain p.wires v
    · have bad := List.all_eq_true.mp keep v (failed member ev)
      simp only [Bool.or_eq_true,Bool.and_eq_true] at bad
      rcases bad with ⟨no,eq⟩ | ⟨no,eq⟩
      ·
        have vv : v=a.1 := (beq_iff_eq.mp eq).symm
        exact False.elim (by rcases ia with noeq|on <;> simp_all)
      ·
        have vv : v=b.1 := (beq_iff_eq.mp eq).symm
        exact False.elim (by rcases ib with on|noeq|on <;> simp_all)
    · rfl
  have all_of_empty (empty : miss.isEmpty=true) (w) (hm : w∈ws) :
      availableB p.domain p.wires w.1=true := by
    cases ev : availableB p.domain p.wires w.1
    · have bad := failed (List.mem_map_of_mem (f:=Prod.fst) hm) ev
      have nil : miss=[] := List.isEmpty_iff.mp empty
      rw [nil] at bad
      contradiction
    · rfl
  have counts := keptCount const ws a b (op==2) ka kb
  change ws.countP const - constantLoss const a ka - constantLoss const b ((op==2)||kb)
        ≤ rest.countP const at counts
  have mass : ws.countP const ≤ rest.countP const+loss := by dsimp [loss]; omega
  change payable2303 (k+p.paid) (p.bound+ws.countP const) (isMaskedConstant p.domain z)
    (availableB p.domain p.wires z) miss.isEmpty loss=true at test
  unfold payable2303 at test
  have cheap : k+p.paid+(!availableB p.domain p.wires z).toNat <
      p.bound+rest.countP const+(isMaskedConstant p.domain z).toNat := by
    split at test
    next h =>
      simp only [Bool.and_eq_true,decide_eq_true_eq] at h
      have le := h.2
      cases availableB p.domain p.wires z <;> cases isMaskedConstant p.domain z <;> simp <;> omega
    next =>
      split at test
      next le => simp [test]; omega
      next =>
        split at test
        next eq =>
          have e := beq_iff_eq.mp eq
          have av : availableB p.domain p.wires z=true :=
            by simp only [availableB,isMaskedConstant,Bool.or_eq_true] at test ⊢; tauto
          simp [av,test]; omega
        next => contradiction
  have buy : (!(!availableB p.domain p.wires z) || choiceOK p.domain p.wires (movedChoice op a b))=true := by
    cases az : availableB p.domain p.wires z
    · have zc : isMaskedConstant p.domain z=false := by
        have ac := az
        change (isMaskedConstant p.domain z || _) = false at ac
        simp only [Bool.or_eq_false_iff] at ac
        exact ac.1
      have empty : miss.isEmpty=true := by
        cases m : miss.isEmpty
        · simp [payable2303,az,zc,m] at test
        · rfl
      have all := all_of_empty empty
      simp [choiceOK,movedChoice,all _ ha,all _ hb]
    · simp
  simpa only [scalarPoolCut,z,rest,known,Bool.and_true,Bool.true_and,Bool.and_eq_true,
    decide_eq_true_eq,List.countP_cons,List.countP_map,Function.comp_def,
    show (if isMaskedConstant p.domain z then 1 else 0)=(isMaskedConstant p.domain z).toNat by cases isMaskedConstant p.domain z <;> rfl,
    Nat.add_assoc] using And.intro cheap buy

def partFour2303 (x : Four2303) (ka kb : Bool) :=
  if ka then (if kb then x.2.2.2 else x.2.1) else (if kb then x.2.2.1 else x.1)

lemma shadeAt2303 {r i cost top cz free ready loss} (unit : r.testBit i=true) :
    (shade2303 r cost top cz free ready loss).testBit i =
      payable2303 cost top (cz.testBit i) (free.testBit i) ready loss := by
  simp only [shade2303,payable2303]
  repeat' split
  all_goals first | assumption | rfl | exact Nat.zero_testBit _

lemma chosenShade2303 {r i a b s t u : Nat} (unit : r.testBit i=true) :
    ((((r ^^^ (a ||| b)) &&& s) ||| ((a ^^^ b) &&& t) ||| ((a &&& b) &&& u)).testBit i) =
    (if a.testBit i then (if b.testBit i then u.testBit i else t.testBit i)
     else if b.testBit i then t.testBit i else s.testBit i) := by
  simp only [Nat.testBit_or,Nat.testBit_and,Nat.testBit_xor,unit]
  cases a.testBit i <;> cases b.testBit i <;> simp

lemma killedBit2303 {t k i : Nat} (start : t.testBit i=true)
    (finish : (t ^^^ (t &&& k)).testBit i=false) : k.testBit i=true := by
  simpa [Nat.testBit_xor,Nat.testBit_and,start] using finish

lemma dropLoss2303 (const : Decor → Bool) (w : Decor) (keep : Bool) :
    constantLoss const w keep = (if keep then false else const w).toNat := by
  cases keep <;> rfl

abbrev lanes2303 {α} (f : α → Sig) (xs : List α) := combineLanes (fun x => liftSig2303 (f x)) xs

def constantMask2303 (r full x d : Nat) := laneEq2303 r full x 0 ||| laneEq2303 r full x d

lemma wireEqSym2303 (a b : Sig) : (a==b)=(b==a) := by
  by_cases h : a=b
  · simp [h]
  · simp [h,Ne.symm h]

lemma constantAt2303 {α} (f : α → Sig) (xs : List α) (i : Nat) (hi : i<xs.length) (d : Sig) :
    let r := units xs.length
    (constantMask2303 r (r*(BitVec.allOnes 768).toNat) (lanes2303 f xs &&& (r*d.toNat))
        (r*d.toNat)).testBit (769*i) = isMaskedConstant d (f xs[i]) := by
  dsimp only
  have z : units xs.length*zero.toNat=0 := by simp [zero]
  simp only [constantMask2303,Nat.testBit_or,maskedLanes2303,←z,bitEqConst2303 _ _ _ _ hi,isMaskedConstant]

lemma freeAt2303 {α} (f : α → Sig) (xs : List α) (i : Nat) (hi : i<xs.length)
    (d : Sig) (vs : List Sig) :
    let r := units xs.length
    let full := r*(BitVec.allOnes 768).toNat
    let zm := lanes2303 f xs &&& (r*d.toNat)
    (include2303 r full zm (vs.map (masked d)) (constantMask2303 r full zm (r*d.toNat))).testBit (769*i) =
      availableB d vs (f xs[i]) := by
  dsimp only
  let r := units xs.length
  let full := r*(BitVec.allOnes 768).toNat
  let zm := lanes2303 f xs &&& (r*d.toNat)
  have I := includeBit2303 (fun x => masked d (f x)) (vs.map (masked d)) xs i hi
    (constantMask2303 r full zm (r*d.toNat))
  rw [←maskedLanes2303] at I
  refine I.trans ?_
  rw [show (constantMask2303 r full zm (r*d.toNat)).testBit (769*i)=isMaskedConstant d (f xs[i]) from constantAt2303 f xs i hi d]
  simp only [isMaskedConstant,availableB,List.any_map,Function.comp_def]
  congr 1
  congr 1
  funext v
  exact wireEqSym2303 _ _

lemma memoAbsent2303 (ws : List Decor) (k : Nat) (p : BoundPool) :
    (memo2303 ws k p).2.2.2.2=absent2303 p ws := by
  simp only [memo2303,absent2303,availableB]
  congr 1
  funext w
  congr 1
  have same (l : List Sig) (w : Sig) : l.contains w=l.any (fun v => v==w) := by
    induction l with
    | nil => rfl
    | cons a l ih => simp only [List.contains_cons,List.any_cons,ih,wireEqSym2303 w a]
  simp only [same]

lemma partStep2303 (todo : Four2303) (step : Nat → Bool → Bool → Nat) (ka kb : Bool) :
    partFour2303 (step todo.1 false false,step todo.2.1 true false,
      step todo.2.2.1 false true,step todo.2.2.2 true true) ka kb =
      step (partFour2303 todo ka kb) ka kb := by cases ka <;> cases kb <;> rfl

lemma killedRule2303 {p : BoundPool} {ws : List Decor} {k op : Nat} (xs : List Ax2303)
    (i : Nat) (hi : i<xs.length) (ka kb : Bool) (todo : Four2303)
    (nd : (ws.map Prod.fst).Nodup) (ha : xs[i].1∈ws) (hb : xs[i].2∈ws)
    (beginning : (partFour2303 todo ka kb).testBit (769*i)=true) :
    let r := units xs.length
    let full := r*(BitVec.allOnes 768).toNat
    let a := lanes2303 (fun e : Ax2303 => e.1.1) xs
    let b := lanes2303 (fun e : Ax2303 => e.2.1) xs
    let z := lanes2303 (fun e : Ax2303 => (movedDecor op e.1 e.2).1) xs
    let cut := wideRule2303 r full a b z (op==2) (memo2303 ws k p) todo
    (partFour2303 cut ka kb).testBit (769*i)=false →
      scalarPoolCut p k ((opKeep (op==2) ka kb xs[i].1 xs[i].2 ws).map Prod.fst)
        (movedChoice op xs[i].1 xs[i].2)=true := by
  let r := units xs.length
  let full := r*(BitVec.allOnes 768).toNat
  let a := lanes2303 (fun e : Ax2303 => e.1.1) xs
  let b := lanes2303 (fun e : Ax2303 => e.2.1) xs
  let z := lanes2303 (fun e : Ax2303 => (movedDecor op e.1 e.2).1) xs
  let const := fun v : Decor => isMaskedConstant p.domain v.1
  let dom := r*p.domain.toNat
  let am := constantMask2303 r full (a &&& dom) dom
  let bm := constantMask2303 r full (b &&& dom) dom
  let zm := constantMask2303 r full (z &&& dom) dom
  let av := p.wires.map (masked p.domain)
  let fm := include2303 r full (z &&& dom) av zm
  let miss := absent2303 p ws
  let sel := maskKeep2303 r full a b (op==2) ka kb miss
  let sh := shade2303 r (k+p.paid) (p.bound+ws.countP const) zm fm miss.isEmpty
  let aa := if ka then 0 else am
  let bb := if (op==2)||kb then 0 else bm
  let kill := ((((r ^^^ (aa ||| bb)) &&& sh 0) ||| ((aa ^^^ bb) &&& sh 1) ||| ((aa &&& bb) &&& sh 2)) &&& sel)
  let step := fun (v : Nat) (x y : Bool) =>
    if v==0 then 0 else
      let ax := if x then 0 else am
      let bx := if (op==2)||y then 0 else bm
      let kx := ((((r ^^^ (ax ||| bx)) &&& sh 0) ||| ((ax ^^^ bx) &&& sh 1) ||| ((ax &&& bx) &&& sh 2)) &&&
        maskKeep2303 r full a b (op==2) x y miss)
      v ^^^ (v &&& kx)
  let t := partFour2303 todo ka kb
  have unit : r.testBit (769*i)=true := unit_bit xs.length i hi
  have ca : am.testBit (769*i)=const xs[i].1 := constantAt2303 (fun e : Ax2303 => e.1.1) xs i hi _
  have cb : bm.testBit (769*i)=const xs[i].2 := constantAt2303 (fun e : Ax2303 => e.2.1) xs i hi _
  have cz : zm.testBit (769*i)=isMaskedConstant p.domain (choiceVal (movedChoice op xs[i].1 xs[i].2)) :=
    (constantAt2303 (fun e : Ax2303 => (movedDecor op e.1 e.2).1) xs i hi _).trans (by rw [moved_full])
  have free : fm.testBit (769*i)=availableB p.domain p.wires (choiceVal (movedChoice op xs[i].1 xs[i].2)) :=
    (freeAt2303 (fun e : Ax2303 => (movedDecor op e.1 e.2).1) xs i hi _ _).trans (by rw [moved_full])
  have lose (n) : (sh n).testBit (769*i)=payable2303 (k+p.paid) (p.bound+ws.countP const)
      (isMaskedConstant p.domain (choiceVal (movedChoice op xs[i].1 xs[i].2)))
      (availableB p.domain p.wires (choiceVal (movedChoice op xs[i].1 xs[i].2))) miss.isEmpty n := by
    rw [show (sh n).testBit (769*i)=_ from shadeAt2303 unit,cz,free]
  have amount (w sw : Nat) (flag : Bool) (prop : Bool) (e : sw.testBit (769*i)=prop) :
      (if flag then 0 else sw).testBit (769*i)=(if flag then false else prop) := by
    cases flag <;> simp [e]
  have notzero : t≠0 := by intro h; have := beginning; change t.testBit _=true at this; simp [h] at this
  dsimp only
  have memoE : memo2303 ws k p=(p.domain,k+p.paid,p.bound+ws.countP const,av,miss) :=
    congrArg (fun v => (p.domain,k+p.paid,p.bound+ws.countP const,av,v)) (memoAbsent2303 ws k p)
  rw [memoE]
  dsimp only [wideRule2303]
  by_cases skip : (decide (k+p.paid≥p.bound+ws.countP const+1) || decide (miss.length>(if op==2 then 1 else 2)))=true
  · rw [if_pos skip]
    intro f; exact False.elim (Bool.noConfusion (beginning.symm.trans f))
  · rw [if_neg skip]
    change (partFour2303 (step todo.1 false false,step todo.2.1 true false,
      step todo.2.2.1 false true,step todo.2.2.2 true true) ka kb).testBit (769*i)=false → _
    rw [partStep2303 todo step ka kb]
    change (if t==0 then 0 else t ^^^ (t &&& kill)).testBit (769*i)=false → _
    simp only [beq_eq_false_iff_ne.mpr notzero,Bool.false_eq_true,ite_false]
    intro h
    have v := killedBit2303 beginning h
    change ( _ &&& sel).testBit (769*i)=true at v
    simp only [Nat.testBit_and,Bool.and_eq_true] at v
    have yes : sel.testBit (769*i)=true := v.2
    rw [show sel.testBit (769*i)=_ from keepBit2303 xs i hi miss (op==2) ka kb] at yes
    apply scalar_fast2303 nd ha hb yes
    have pick := v.1
    rw [chosenShade2303 unit,amount 0 am ka _ ca,amount 0 bm ((op==2)||kb) _ cb] at pick
    simp only [lose] at pick
    have clear (f : Nat → Bool) (u v : Bool)
        (eq : (if u then (if v then f 2 else f 1) else if v then f 1 else f 0)=true) :
        f (u.toNat+v.toNat)=true := by cases u <;> cases v <;> exact eq
    dsimp only
    simp only [dropLoss2303]
    exact clear _ (if ka then false else const xs[i].1) (if (op==2)||kb then false else const xs[i].2) pick

abbrev wideArgs2303 (xs : List Ax2303) (op : Nat) :=
  (units xs.length,units xs.length*(BitVec.allOnes 768).toNat,
    lanes2303 (fun e : Ax2303 => e.1.1) xs,lanes2303 (fun e : Ax2303 => e.2.1) xs,
    lanes2303 (fun e : Ax2303 => (movedDecor op e.1 e.2).1) xs)

def runRules2303 (xs : List Ax2303) (op : Nat) (todo : Four2303) (ps : List Memo2303) :=
  let (r,full,a,b,z) := wideArgs2303 xs op
  wideRules2303 r full a b z (op==2) todo ps

def runRule2303 (xs : List Ax2303) (op : Nat) (todo : Four2303) (p : Memo2303) :=
  let (r,full,a,b,z) := wideArgs2303 xs op
  wideRule2303 r full a b z (op==2) p todo

lemma finishedRule2303 {ps : List BoundPool} {ws : List Decor} {k op : Nat}
    (xs : List Ax2303) (i : Nat) (hi : i<xs.length) (ka kb : Bool) (todo : Four2303)
    (nd : (ws.map Prod.fst).Nodup) (ha : xs[i].1∈ws) (hb : xs[i].2∈ws)
    (beginning : (partFour2303 todo ka kb).testBit (769*i)=true)
    (done : (partFour2303 (runRules2303 xs op todo (ps.map (memo2303 ws k))) ka kb).testBit (769*i)=false) :
    ∃ p∈ps, scalarPoolCut p k ((opKeep (op==2) ka kb xs[i].1 xs[i].2 ws).map Prod.fst)
      (movedChoice op xs[i].1 xs[i].2)=true := by
  induction ps generalizing todo with
  | nil => exact False.elim (Bool.noConfusion (beginning.symm.trans done))
  | cons p ps ih =>
    let next := runRule2303 xs op todo (memo2303 ws k p)
    change (partFour2303 (if zeroFour2303 todo then todo else runRules2303 xs op next (ps.map (memo2303 ws k))) ka kb).testBit (769*i)=false at done
    split at done
    next => exact False.elim (Bool.noConfusion (beginning.symm.trans done))
    next =>
      cases he : (partFour2303 next ka kb).testBit (769*i)
      · exact ⟨p,by simp,killedRule2303 xs i hi ka kb todo nd ha hb beginning he⟩
      · obtain ⟨v,vm,cut⟩ := ih next he done
        exact ⟨v,List.mem_cons_of_mem _ vm,cut⟩

def familyCheck2303 (c : NodeContext) (op : Nat) (e : Ax2303) (ka kb : Bool) :=
  let w := (movedDecor op e.1 e.2).1
  if !properB w || c.2.2.1.any (fun v => v.1==w) then true else
  linked2303 c.2.2.1 c.2.2.2.2.2 e.1 e.2 w (op==2) ka kb

def todo2303 (c : NodeContext) (op : Nat) (xs : List Ax2303) : Four2303 :=
  let r := units xs.length
  let f := wideWorth2303 c.2.1 c.1 op r (r*(BitVec.allOnes 768).toNat) c.2.2.2.1
    (packedSig (fun e : Ax2303 => e.1.2) xs) (packedSig (fun e : Ax2303 => e.2.2) xs)
  (f false false,if op==2 then 0 else f true false,if op==2 then 0 else f false true,f true true)

def testMarks2303 (c : NodeContext) (op : Nat) (xs : List Ax2303) (ka kb : Bool) (m : Nat) :=
  if m==0 then true else onMarks (fun e => familyCheck2303 c op e ka kb) m xs

lemma todoAt2303 (c : NodeContext) {op} (xs : List Ax2303) (i : Nat) (hi : i<xs.length)
    (ka kb : Bool) (same : (op==2)=true → ka=kb) :
    (partFour2303 (todo2303 c op xs) ka kb).testBit (769*i)=
      worth2303 c.1 c.2.1 c.2.2.2.1 op xs[i].1 xs[i].2 (movedDecor op xs[i].1 xs[i].2) ka kb := by
  cases ka <;> cases kb <;> cases un : op==2 <;>
    first | exact False.elim (Bool.noConfusion (same un)) |
      simpa only [todo2303,partFour2303,un,Bool.false_eq_true,ite_false,ite_true] using
        (worthAt2303 c.2.1 c.1 op c.2.2.2.1 xs i hi _ _)

lemma familyBranch2303 {c : NodeContext} {op} (xs : List Ax2303)
    (pass : wideFamily2303 c (c.2.2.2.2.1.map (memo2303 c.2.2.1 (c.1-1))) op xs=true)
    (ka kb : Bool) :
    let done := runRules2303 xs op (todo2303 c op xs) (c.2.2.2.2.1.map (memo2303 c.2.2.1 (c.1-1)))
    testMarks2303 c op xs ka kb (partFour2303 done ka kb)=true := by
  obtain ⟨cap,n,ws,cov,ps,links⟩ := c
  simp only [wideFamily2303] at pass
  rw [opLanes2303] at pass
  let c : NodeContext := (cap,n,ws,cov,ps,links)
  let done := runRules2303 xs op (todo2303 c op xs) (ps.map (memo2303 ws (cap-1)))
  change (testMarks2303 c op xs false false done.1 && testMarks2303 c op xs true false done.2.1 &&
    testMarks2303 c op xs false true done.2.2.1 && testMarks2303 c op xs true true done.2.2.2)=true at pass
  simp only [Bool.and_eq_true] at pass
  cases ka <;> cases kb
  · exact pass.1.1.1
  · exact pass.1.2
  · exact pass.1.1.2
  · exact pass.2

lemma evalDone2303 (c : NodeContext) (op : Nat) (a b : Decor) (ka kb : Bool)
    (ha : a∈c.2.2.1) (hb : b∈c.2.2.1)
    (checked : worth2303 c.1 c.2.1 c.2.2.2.1 op a b (movedDecor op a b) ka kb=true →
      familyCheck2303 c op (a,b) ka kb=true ∨ ∃ p∈c.2.2.2.2.1,
        scalarPoolCut p (c.1-1) ((opKeep (op==2) ka kb a b c.2.2.1).map Prod.fst)
          (movedChoice op a b)=true) :
    evalMove c op a b (movedDecor op a b) ka kb=true := by
  obtain ⟨cap,n,ws,cov,ps,links⟩ := c
  let z := movedDecor op a b
  let len := 1+(n-(if ka then 0 else 1)-(if (op==2)||kb then 0 else 1))
  let d := len==cap
  let bits := restCov (getCov cov d) (column d a.2) (column d b.2) (op==2) ka kb ||| column d z.2
  let skip := !properB z.1 || ws.any (fun v => v.1==z.1)
  let st := (opKeep (op==2) ka kb a b ws).map Prod.fst
  change (if len>cap then true else if bits != BitVec.allOnes 768 then true else
    if skip then true else closeChild ps links (cap-1) st (movedChoice op a b))=true
  by_cases long : len>cap
  · rw [if_pos long]
  rw [if_neg long]
  by_cases notfull : (bits != BitVec.allOnes 768)=true
  · rw [if_pos notfull]
  rw [if_neg notfull]
  by_cases short : skip=true
  · rw [if_pos short]
  rw [if_neg short]
  have w : worth2303 cap n cov op a b z ka kb=true := by
    change (if len>cap then false else bits==BitVec.allOnes 768)=true
    rw [if_neg long,beq_iff_eq]
    exact Classical.byContradiction (fun e => notfull (bne_iff_ne.mpr e))
  rcases checked w with link | cut
  · change (if skip then true else linked2303 ws links a b z.1 (op==2) ka kb)=true at link
    rw [if_neg short] at link
    have link := linked_ok2303 ha hb link
    simp only [closeChild,Bool.or_eq_true]
    left
    simpa only [z,moved_full] using link
  · simp only [closeChild,Bool.or_eq_true,List.any_eq_true]
    exact Or.inr cut

lemma wideFamily_pass2303 {c : NodeContext} {op : Nat} (xs : List Ax2303)
    (nd : (c.2.2.1.map Prod.fst).Nodup)
    (pass : wideFamily2303 c (c.2.2.2.2.1.map (memo2303 c.2.2.1 (c.1-1))) op xs=true)
    {e : Ax2303} (em : e∈xs) (ha : e.1∈c.2.2.1) (hb : e.2∈c.2.2.1)
    (ka kb : Bool) (same : (op==2)=true → ka=kb) :
    evalMove c op e.1 e.2 (movedDecor op e.1 e.2) ka kb=true := by
  obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp em
  subst e
  apply evalDone2303 _ _ _ _ _ _ ha hb
  intro w
  let before := todo2303 c op xs
  let ps := c.2.2.2.2.1
  let done := runRules2303 xs op before (ps.map (memo2303 c.2.2.1 (c.1-1)))
  let last := partFour2303 done ka kb
  have first : (partFour2303 before ka kb).testBit (769*i)=true := (todoAt2303 c xs i hi ka kb same).trans w
  cases h : last.testBit (769*i)
  · exact Or.inr (finishedRule2303 xs i hi ka kb before nd ha hb first h)
  · left
    have run := familyBranch2303 xs pass ka kb
    change testMarks2303 c op xs ka kb last=true at run
    have nz : last≠0 := by intro e; simp [e] at h
    simp only [testMarks2303,beq_eq_false_iff_ne.mpr nz,Bool.false_eq_true,ite_false] at run
    exact marked_ok _ _ _ i hi h run

lemma wideNode_sound2303 {T : Sig} {c : NodeContext} (h : wideNode2303 T c=true) :
    (prelim T c && testAll c c.2.2.1)=true := by
  simp only [wideNode2303,Bool.and_eq_true] at h
  have good := h.1.1.1
  simp only [prelim,Bool.and_eq_true,decide_eq_true_eq] at good
  let ws := c.2.2.1
  have unary {a : Decor} (am : a∈ws) (keep : Bool) : evalMove c 2 a a (movedDecor 2 a a) keep keep=true :=
    wideFamily_pass2303 _ good.1 h.1.1.2 (e:=(a,a)) (List.mem_map_of_mem am) am am _ _ (fun _ => rfl)
  have binary {a b : Decor} (am : a∈ws) (bm : b∈ws) (inPairs : (a,b)∈couples2303 ws) (d ka kb : Bool) :
      let op := if d then 1 else 0
      evalMove c op a b (movedDecor op a b) ka kb=true := by
    cases d
    · exact wideFamily_pass2303 _ good.1 h.1.2 inPairs am bm ka kb (by simp)
    · exact wideFamily_pass2303 _ good.1 h.2 inPairs am bm ka kb (by simp)
  have all (l : List Decor) (sub : ∀ w∈l, w∈ws) (prs : ∀ e∈couples2303 l, e∈couples2303 ws) : testAll c l=true := by
    induction l with
    | nil => rfl
    | cons a bs ih =>
      have am := sub a (by simp)
      have rest (b) (bm : b∈bs) := sub b (List.mem_cons_of_mem a bm)
      have subP (e) (em : e∈couples2303 bs) := prs e (List.mem_append_right _ em)
      simp only [testAll,testRow,Bool.and_eq_true,List.all_eq_true]
      refine ⟨⟨⟨unary am false,unary am true⟩,?_⟩,ih rest subP⟩
      intro b bm
      have im : (a,b)∈couples2303 ws := prs _ (List.mem_append_left _ (List.mem_map_of_mem bm))
      have p (d : Bool) : testPair c a b d=true := by
        simp only [testPair,Bool.and_eq_true]
        exact ⟨⟨⟨binary am (rest b bm) im d false false,binary am (rest b bm) im d true false⟩,
          binary am (rest b bm) im d false true⟩,binary am (rest b bm) im d true true⟩
      exact ⟨p false,p true⟩
  simp only [Bool.and_eq_true]
  exact ⟨h.1.1.1,all ws (fun _ => id) (fun _ => id)⟩

def triangle2303 (f : Decor → Bits) : List Decor → Nat × Nat × Nat
  | [] => (0,0,0)
  | x::xs =>
    let (suffix,left,right) := triangle2303 f xs
    let m := xs.length
    let v := (f x).toNat
    ((suffix <<< 769)+v,(left <<< (769*m))+units m*v,(right <<< (769*m))+suffix)

lemma lanesAppend2303 {α} (f : α → Bits) (xs ys) :
    combineLanes f (xs++ys)=(combineLanes f ys <<< (769*xs.length))+combineLanes f xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons x l ih =>
    simp only [List.cons_append,List.length_cons,combineLanes,lanePlace,ih,Nat.shiftLeft_eq,
      Nat.mul_succ,Nat.pow_add]
    ring

lemma lanesMap2303 {α β : Type} (f : β → Bits) (g : α → β) (xs) :
    combineLanes f (xs.map g)=combineLanes (fun x => f (g x)) xs := by
  induction xs with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons,combineLanes,ih]

lemma triangle_eq2303 (f : Decor → Bits) (xs) :
    triangle2303 f xs=(combineLanes f xs,combineLanes (fun e : Ax2303 => f e.1) (couples2303 xs),
      combineLanes (fun e : Ax2303 => f e.2) (couples2303 xs)) := by
  induction xs with
  | nil => rfl
  | cons a l ih =>
    simp only [triangle2303,ih,combineLanes,couples2303,lanesAppend2303,lanesMap2303,
      List.length_map,←broadcast,lanePlace,Nat.shiftLeft_eq,Nat.mul_comm]

def packedFamily2303 (c : NodeContext) (ps : List Memo2303) (op : Nat) (ops : List Ax2303)
    (sa sb : PackedSig) (a b : Nat) :=
  let (cap,n,ws,cov,_,links) := c
  let r := units ops.length
  let full := r*(BitVec.allOnes 768).toNat
  let un := op==2
  let z := if un then (r*one.toNat) ^^^ a else if op==1 then a ||| b else a &&& b
  let worth := wideWorth2303 n cap op r full cov sa sb
  let todo : Four2303 := (worth false false,if un then 0 else worth true false,
                       if un then 0 else worth false true,worth true true)
  let left := wideRules2303 r full a b z un todo ps
  let verify := fun (ka kb : Bool) (t : Nat) => if t==0 then true else
    onMarks (fun e : Ax2303 =>
      let w := (movedDecor op e.1 e.2).1
      if !properB w || ws.any (fun v => v.1==w) then true else
      linked2303 ws links e.1 e.2 w un ka kb) t ops
  verify false false left.1 && verify true false left.2.1 &&
    verify false true left.2.2.1 && verify true true left.2.2.2

def triangleNode2303 (T : Sig) (c : NodeContext) :=
  let ws := c.2.2.1
  let ss := c.2.2.2.2.1.map (memo2303 ws (c.1-1))
  let bs := couples2303 ws
  let (_,pa,pb) := triangle2303 (fun w => w.2.1) ws
  let (_,na,nb) := triangle2303 (fun w => w.2.2) ws
  let (_,a,b) := triangle2303 (fun w => liftSig2303 w.1) ws
  let family := fun op => packedFamily2303 c ss op bs (pa,na) (pb,nb) a b
  prelim T c && wideFamily2303 c ss 2 (ws.map fun v => (v,v)) && family 0 && family 1

theorem triangleNode_ok2303 {T : Sig} {c : NodeContext} (h : triangleNode2303 T c=true) :
    (prelim T c && testAll c c.2.2.1)=true := by
  obtain ⟨cap,n,ws,cov,pools,links⟩ := c
  apply wideNode_sound2303
  simp only [triangleNode2303,triangle_eq2303] at h
  exact h

def span2303 (p : Nat → Bool) : Nat → Nat → Bool
  | 0,_ => true
  | n+1,i => p i && span2303 p n (i+1)
theorem span2303_at {p n i} (h : span2303 p n i=true) (j : Nat) (l : i ≤ j) (u : j < i+n) :
    p j=true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    simp only [span2303,Bool.and_eq_true] at h
    by_cases e : j=i
    · simpa [e] using h.1
    · exact ih h.2 (by omega) (by omega)

def treeCheck2303 (p : Nat → Bool) (start len : Nat) : Nat → Prop
  | 0 => span2303 p len start=true
  | h+1 => treeCheck2303 p start (len/2) h ∧ treeCheck2303 p (start+len/2) (len-len/2) h
lemma tree_at2303 {p start len height} (h : treeCheck2303 p start len height)
    (i : Nat) (lo : start ≤ i) (hi : i < start + len) : p i = true := by
  induction height generalizing start len with
  | zero => exact span2303_at h i lo hi
  | succ n ih =>
    change _ ∧ _ at h
    by_cases first : i<start+len/2
    · exact ih h.1 lo first
    · exact ih h.2 (by omega) (by omega)

def wideCheck (g : Forest) (k i : Nat) :=
  triangleNode2303 (targetOf g) (contextOf g k i)

theorem wideBlock {g k start count depth}
    (h : treeCheck2303 (wideCheck g k) start count depth) :
    block g k start count = true := by
  apply makeBlock
  intro i hlo hhi
  have checked := triangleNode_ok2303 (tree_at2303 h i hlo hhi)
  rw [from_context]
  by_cases hk : k=0
  · simpa only [hk,if_true,Bool.and_true] using (Bool.and_eq_true_iff.mp checked).1
  · simpa only [hk,if_false] using checked
def complement := neg (inputs.getD 0 zero)

theorem suppliedRun {raw : List Sig} {T k t S L} (hp : proper T)
    (bound : Lower raw T L) (run : Live T k t S) (sub : ∀ v ∈ S, v ∈ raw) :
    L ≤ k := by
  have supplyRaw : supply (raw.map observe) (S.toList.map observe) := by
    intro a ha
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp ha
    exact Or.inl (List.mem_map_of_mem (sub v (by simpa using hv)))
  obtain ⟨q,W,reach,hit,budget⟩ := contraction (observe_proper hp)
    (list_run run S.toList (Finset.nodup_toList _) (by simp)) _ Reach.start supplyRaw
  have le := bound q W reach hit
  omega

-- A witness pair forces each remaining ordinary input into the live set.
-- When the complement is live, the positive input can be either live or absent.
theorem signedLower {T x e k} {rest : List Sig} (hp : proper T)
    (old : Lower (x::rest) T (k+1))
    (essential : ∀ a ∈ rest, Essential T (x::(rest++[e])) a)
    (without : Impossible T k (rest++[e]).toFinset)
    (both : Impossible T k (x::(rest++[e])).toFinset) :
    Lower (x::(rest++[e])) T (k+1) := by
  intro p bank path hit
  obtain ⟨n,t,S,le,run,sub⟩ := reach_live hp path hit
  by_contra! small
  have required (a) (ha : a ∈ rest) : a ∈ S := by
    obtain ⟨r,s,diff,iso⟩ := essential a ha
    exact raw_required run _ a sub r s diff iso
  by_cases he : e ∈ S
  · by_cases hx : x ∈ S
    · have eq : S = (x::(rest++[e])).toFinset := by
        ext a
        simp only [List.mem_toFinset,List.mem_singleton,List.mem_cons,List.mem_append,
          List.not_mem_nil,or_false]
        refine ⟨fun ha => by simpa using sub a ha, ?_⟩
        rintro (rfl | h | rfl)
        · exact hx
        · exact required _ h
        · exact he
      exact both n t (by omega) (eq ▸ run)
    · have eq : S = (rest++[e]).toFinset := by
        ext a
        simp only [List.mem_toFinset,List.mem_append,List.mem_singleton]
        constructor
        · intro ha
          have h := sub a ha
          simp only [List.mem_singleton,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at h
          exact h.resolve_left (fun eq => hx (eq ▸ ha))
        · rintro (h | rfl)
          · exact required _ h
          · exact he
      exact without n t (by omega) (eq ▸ run)
  · have keep : ∀ a ∈ S, a ∈ x::rest := by
      intro a ha
      have h := sub a ha
      simp only [List.mem_singleton,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at h ⊢
      rcases h with h | h | rfl
      · exact Or.inl h
      · exact Or.inr h
      · exact False.elim (he ha)
    have budget := suppliedRun hp old run keep
    omega

theorem countImpossible {T : Sig} {S : Finset Sig} {k : Nat} (small : k+1 < S.card) :
    Impossible T k S := by
  intro n t budget run
  have h := (live_size run).2
  omega

def minusZero (m : Nat) := vars (m-1) ++ [complement]

theorem orderCut {T : Sig} {ws : List Sig} {cap : Nat} (r s : Row)
    (size : cap+1 ≤ ws.toFinset.card)
    (direction : bit r T = true ∧ bit s T = false ∧
      (ws.all fun w => !bit r w || bit s w) = true) : Impossible T cap ws.toFinset := by
  intro n t limit run
  have h := (live_size run).2
  have no : t=0 := by omega
  obtain ⟨a,ha,p,q⟩ := mono_row_difference run no direction.1 direction.2.1
  have pair := List.all_eq_true.mp direction.2.2 a (List.mem_toFinset.mp ha)
  simp [p,q] at pair

theorem signedInduced {m k hints} (old : Lower (vars m) (graphGoal m) (k+1))
    (root : vars m = inputs.getD 0 zero :: vars (m-1))
    (full : vars (m+2048) = inputs.getD 0 zero :: minusZero m)
    (hp : properB (graphGoal m) = true)
    (ess : checkEssential (graphGoal m) (vars (m+2048)) (graphPairs (m-1) hints) = true)
    (all : (graphPairs (m-1) hints).map Prod.fst = vars (m-1))
    (without : Impossible (graphGoal m) k (minusZero m).toFinset)
    (both : Impossible (graphGoal m) k (vars (m+2048)).toFinset) :
    Lower (vars (m+2048)) (graphGoal m) (k+1) := by
  rw [full] at both ⊢
  rw [root] at old
  apply signedLower (proper_of _ hp) old _ without both
  intro a ha
  change Essential _ (inputs.getD 0 zero :: minusZero m) _
  rw [←full]
  apply essential_ok ess
  rw [all]
  exact List.mem_toFinset.mpr ha

theorem signedCircuitSize (C : Circuit) (fan : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0]) = edge x)
    (bound : Lower (inputs++[complement]) graph 15) : 15 ≤ C.size := by
  have eq : (execute C.gates (inputs++[complement])).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    change bit r _ = bit r graph
    rw [←b_read,execute_bits _ _ _ (fun g hg => (fan g hg).1)]
    simp only [List.map_append,List.map_singleton,←sampled,complement,bit_neg]
    exact (computes (sample r)).trans (edge_table r).symm
  have avail := get_rep (execute C.gates (inputs++[complement])) C.output
  rw [eq] at avail
  obtain ⟨k,t,S,le,run,sub⟩ := extract C.gates _ fan graph_proper
    (avail.resolve_right (fun h => h graph_proper))
  exact (suppliedRun graph_proper bound run sub).trans le

def g15d3 (i : Nat) : Nat := 0xf
def g15l3 : Packing := (1,0,0,0,1,0,0,g15d3)
def g15samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbaf3ea78de4d799d,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff450cc90c3c245919),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdf7ff8fe9f9b7ed5,0x20812421801324c4),(0xefbdbf97f9f6bf6a,0x102a401415600a0a),(0xf3a9d7437375f5ba,0xfc028ab620235b0),(0,0),(0,0),(0,0),(0,0),(0,0)]
def g15columns : IndexTree ColumnInfo := (.leaf [])
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
def g31columns : IndexTree ColumnInfo := (.fork 2 (.leaf [(1,0,30,0,4),(2,0,29,0,4)]) (.leaf [(4,0,27,0,4),(8,0,23,0,4),(16,0,15,0,4)]))
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
def g47columns : IndexTree ColumnInfo := (.leaf [(8,0,39,0,4)])
def g47autos : Array (List Nat) := #[[],[83,32]]
def g47levels : Nat → Packing
  | _ => emptyPacking
def g47index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g47 : Forest := ⟨47,4,fun j => g47samples[j]?.getD (0,0),g47columns,g47autos,g47levels,g47index⟩
def g55samples : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbfffffdf7defdfafbfd3fcebcfdeffcebffefe76de77fed7f1773f95eb2ebeb,0x400028000010005000000400701010180030103060043200102204010904888),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdb7fbfbb9ad3afd94caf0b9db5bbdf7f7d39bfcdadcf77ec9eccd2fb9cf16b5,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2484444214284026a4e002420468a8a43140a00408d944460a4082569431231),(0xeda5e7e7b2fc29de4ffc371dba2bf0775ff12db9b18bb528fedad96afcd3c5e,0x12589919410293410206d0396285445a082c5d2bf0022b20f0895d2048c2c4e),(0,0),(0xf1cd79264efe956afa7a64bb677ab40beba463600362eda36f3357b7d763926,0xe3a8651b1a36a0acc57538a080f6ea703078a0c13c28dc34c91f3868663126),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe05fe74eda341d5872cbf684d5e2ed19e7e3bba5e964550dd792aec724f479,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01fb53db1204342a549861b60b6727a22d48ac0b14da4445855161ae724b471),(0,0),(0,0),(0,0)]
def g55columns : IndexTree ColumnInfo := (.leaf [(16,0,39,0,4)])
def g55autos : Array (List Nat) := #[[],[84]]
def g55levels : Nat → Packing
  | _ => emptyPacking
def g55index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g55 : Forest := ⟨55,4,fun j => g55samples[j]?.getD (0,0),g55columns,g55autos,g55levels,g55index⟩
def g63samples : Array (Bits × Bits) := #[(0xdabffdfdbdf61bfbfc7dcbe34f7f1b17917df75df7edd9eff77b6dbd3dcebed3cfbfaddba50fcabded46bc9b579eb7bd3d92776566ad4ad3debe36d74deb7f9faf189ad76da7dc1a6b4eaf21eb254de4ae1f7451bb34d9456fd18e934db17349,0x4400202400040800310000100084000ac0000102800a1100490002240004b2800a001b4000190000008108000574009200040400000594000190004218c0010840002890800550053044a00410008802d0060013000c004400188120c206208),(0xb6678efeffcbf5a9cad5bfd527a7a5bd74d1314b7915f5b2ffdec2fc5d978f8ab3b44b2b5add5b771711b15ce99bf2b3f5bce975ef94cd59a34e76ab937848a94ef6be6c9579db5905539ea703c87a7d4ae11fe2ae423fade4a3c3299b0724e7,0x499461811a200a55004cf88854029340027a680613c002ec00233c1096d01045025d0203d400243150030b7e4900b00499e023395882049d0206ec00041398010bbb1000b7310ad00cc0858112c8207810e917400e423d0034024309910504e5),(0xbfdd27bedf8fade4776ebf9d185bc5bd76aeffb29711f77d628e86e5fffdff6d1a52bff6da987348e3e147dcecdbcc68d1accc4e7d7d77b9734cfbbcefbc022d72eff5a31a72e32584dd5a72accb1256ede309af577ea6b3ab2be572a2769632,0x20983204990108b1910222a2810c12a8041040402e00006394000908008912a582448429aad10a21a0240190b504314209040621245140c82010e8812042049440841100c0c52080310832a5111106e902488a012c82618908a42202729212),(0x77ddb87389d95f9f7bbe7e8eb89e6e76fbf75ca7fd5bb3758b555b578affe964ae7e7fa493e06d03bebc4fb5cff51e46b2dd5bdbb1eab66f60f7d916b9c6944fd85b6f0fc30a2ae7d2afc9dc369ef80bb1b0b2dd52e9331e786f7a5d38e8c8b4,0x1482478012444200420888514440810c402202189081ecc814422aa4c048408050190921c0450c000a080254044021081134422900082c11250884167012813a48094aca870a3283708e41084282480000c012150640581c30655a55288040a4),(0xdca768aafb78ce8d2db2ec3fbdddfa4ec963339dbac7a8e05eccbf0bb99ddf5febcef6dc7762a4a79d9ad8f70324ba6e724754bded1eed86f695f276b70acbd73dc66e39a88d0cfed920a0ee10b5a4dd5893bba709bff6dc1ece388c561e1ed5,0x210938550593284a984457082a220ca002159526023c0223a02100100d271046aa46f2022bb0201ea5730921b3008e848a002106a7520082d20653c8040064810364a00030c5086c0c2084761035a077101508a009ba22e00b822088521e1c51),(0x77dad76bd4ced656e7ec247a694c9eb5b66dc4de71aac18acebb177a9bac7a62d6f3e3996dd9d62d6ecf7b18557229a30b5ebb1ef46b568a8f3400a7c2d3365caade63d0f2234a24623735bcfaee29c0664eddfc63b2a86915f817ca03dc41fa,0x88252894b2b3256598a758928465236453b27d28c68c4c28a24dcc0d24d500d4a845700845b04bd175706d345a20a0a24d641d897dd822a1d52444cad2629c8e732b305273362844202335b73c8d8150424e93e44a78286995ec17c803dc01f2),(0,0),(0,0),(0,0)]
def g63columns : IndexTree ColumnInfo := (.leaf [(32,0,31,0,7)])
def g63autos : Array (List Nat) := #[[],[50,65]]
def g63levels : Nat → Packing
  | _ => emptyPacking
def g63index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g63 : Forest := ⟨63,7,fun j => g63samples[j]?.getD (0,0),g63columns,g63autos,g63levels,g63index⟩
def g111d6 (i : Nat) : Nat := 0x120ff
def g111l6 : Packing := (1,0,2,0,1,0,0,g111d6)
def g111samples : Array (Bits × Bits) := #[(0xeafcc7b96fc59ffd26c5e2bb3d7bd378fb35ff5dcb26f92afa5f57eff59a73b7aaa379b2fc8d7a99e2ef9efcf4defd4efabc9c89733cebade5579ad5abbcd64d8557ad3d63bd1c6a75510ce3b9bf05e462ee0edf6dfb2914efc74c7d31727465,0x4d00310a2003881269402d0c00406ccc142a8012908082d00025ac006a88036948003229000032d4001bf20024ec2018680000aaf2500325400423a6f02003840040a8016ea8106822700071012c01d500600ad401ea0010f407087831504444),(0xf771ad34ff2bcf4fbd7f5f5de52efaeb7ebbabfffefbf2eab7c7cf56f8ecea565ddfabcf87cb61db9d6ef4aecff7cebd76fe679cfb9935e6adabc77cdcdb677ed3da5e4f56b4cbe39cfd7aed1f519a6b999796b48a51f4f7b8ad91a66cc6d9cb,0x1204940050200482000010001c10308054448009004424020800871400ac0690000402004e0508404004081210450414000904018220d090010808000a44280600460810104d92040818880c1010088d8400200a10a1400808810604821909),(0xf5be76df5e79b8b5d13f5f6e3ecd176fbeee538a7cfb9f7f6b7fad9b13bb7fed97560ecd71f29f3f1e3ef959a338e3a9e32bd5e7cfc7b51df73d7e9e165479b3baa9a0d59e62e11eead3ad5c624777de8699f96d3766d64d1f3fa2ca8f3d2e52,0x8e4d19200884440101e4a802e100a0c04000830eb000289800c49240c1c411082c325a6812b0485430294040c52402008322a4b0e00c0021216842103a050a9080848145264020288841a770220547500211500d95204c05521120880b352452),(0xde2ebbc73c1cf83c4cedbed77297d7f5b666582db23d5c5d7bf4a54b37a75f4992f88d683d388ea5bafb57791a5deb9b257390777cf70e9d329773c24416edd93fe3d2909bc3b81d7e62dd94d70a759eb42b6b51587d63da2e7eea6ce78912bc,0x10b22099c5638280b403142808691e02bd9d04d1097a9640ce2041351e20e64283892100494815238b12089820999d9858901b4e1903515e001721098578a5416f515492d981d895722018845902b08a5c4a2a2248dd03d08c66ca64e48812ac),(0,0),(0x4a99db5e74fdf3bbfb83b4b12e735e58f515867b75942dba656f9eeac55739b971685432ece5b39368c30fbbb9f895ca9efa5eceda2fea7be4766f052ba5def635ccf928215f7640050f6846acafb2ca6efbba0bffbfdb9043d87d111c3c3ebd,0x12d68401de50564414b80023f49c0203c0413d800068400bbb08034f0177ac0427f40400f6de0023bcc009fc1201950403ff4900082ea08a2fc908010c8a4053de0011e801464d050407f806ac13f8026d9b800bfa055d40038875010c2c3ab9),(0x107b7e8791b6519a9ebd6f37d374faa298392ebad8b5e4afe6bd267679568b3365bebaabdf6ef4e9035a918e8ca50ef74769b2b74aea726a09a6c5e9463715fb76745a9b1b6212a1b9add6dec52a9ba55b57e399ab660ca6d0f217384af881fe,0xadc48a6a24248ac9294916cc74a18dce4988890976a839d0a90054480a8f001149b409fd5690d8d50882129489ae3083c83b5253565cd02541ca4550f495b985581508b28aaa022919a1e755a00eaaa54243a315f06a0c87d4f216384a7880f6),(0,0),(0,0)]
def g111columns : IndexTree ColumnInfo := (.leaf [(4,8,99,0,4),(1,32,78,0,4),(64,0,47,0,5)])
def g111autos : Array (List Nat) := #[[],[83,32]]
def g111levels : Nat → Packing
  | 6 => g111l6
  | _ => emptyPacking
def g111index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | _ => fun _ => none
def g111 : Forest := ⟨111,6,fun j => g111samples[j]?.getD (0,0),g111columns,g111autos,g111levels,g111index⟩
def g119samples : Array (Bits × Bits) := #[(0xfab75f3dfbfa3756f92d9ff7baf5ff7dbfebb9b33bef7dcdf77fbffe7bbbf75546cedccfd6f7eb762bef3ffdd2ede7abbef7e4e4b775eb9be6ab6f4d5fde77f2b955ece57b3feb97c6d99b5cdd2fdd2ea315de5f3efbf8d44ddcaa7566eda9cd,0x20100000802449000a820000c1900042800052080010000098c000620802429000050a2000012e00000be20013404000082000047420011240000c8b8000110080002480036500158018000c4009400c9000c0062803a0400e00885042a10888),(0xaf7efcd6de9febfb57d6f5ddedde36f3db7fffeed79fdbfafcf255738c743cbbbff3e3b86b8f9fb9f5bdf54fbff79bd74f5afb3f7fba34f5bf5f9afae879ab5feefe93fa9ee6566f7bbee6bf67d426d75cfb2bace9344fabf72bd58e999b76b3,0x9300010000091004000400382060802420900110020801010208161810541520000000800198110400c004084880812115000049028020c0800220200009220a01801050108206a8408406120184808104430800802442850101410609083421),(0xd3aee9d1a16b8afb579b1b1a2ede96c634714fced4ed35afb8d86696aabedb2eada373270f48f3a9b93de8a90d87d8f6684756adef8eb40bf672fc78b9342c9c7aaa652b2aec9422dd38b32b2a5255bdcc3d35b2da5f372953f3c4ba3a70d996,0x2c07b23e74020fd2aa41748155856818d263d681015680dac92709c7448b08586eaf3a512642c64b613a9091954b38c222671d26711d023332d48951dd0691952839212f8b6888039910b9ac2a42653c283c65315b1b95185ae084b83270c996),(0,0),(0x759a506bc07865de6f37bc2fabe39a5e2705b6a3eec6bd3cca572e3ed72f0325f632aa43d8e0e833eaeab6f86ad5fa72dbaf9c83b9e70faa212acf122e177ae733d8fa39a0b0bb12b7915f7134c3b9a9ed98d75362b1d9c725676c3caf04637c,0x16e5f59c6d01a255c44806523c0cddb5529a2196d082e7c24415d298c0f10d071e6090549dc090f8ed501938009f3fb2169588d90b0b506d102e01343cb84ad135f45369a498be0a36011e712702bb816af81651c4b05c0701a6642cad046374),(0x6339c3e76f77dc41ec6c9766b8b0f93592cd6e58a17db2abb9eea5cd269eeae2dc2c1c9ec755bae6a2821f6b678c3538a75edaf56c57e97ff4e8b90d55c4e75ce36b37ac511be4c610c6f229b9ab77956345b3a117ef6f3608dd37697870ba61,0x84ef690f5888a6bc0049f9381c0ba0115db000874a075d2102333605e754184fe100105f739880fb92c019ec481f2d2102dbf2480954a0ad3f922114724920d57f80032e5018c6a22083e62199863ec06b43378157e41d3d00d937293850b261),(0xd5cc96ab2735f4eedbcfece9fd4d847149d75b8aa71ff3959066dc7566c66ecb75975abde9bb8d684d89311f3151135dd1ce4d97acd9737d0b4d97b62b1596cf57b51ab1b6b408593b67d5bb928b32dabad66fc43367241aeaae177095e247ea,0x481560b0cd924918c5323d4303992d88d1232e6a49f254a2454320824e8122936522ef3572424e688310332525616c12e023da92a435d213539c9243b254cc21b63548a8e4258841b361f1c95a017252ba1c47902bc1245a7a8e167094e243ca),(0,0),(0,0)]
def g119columns : IndexTree ColumnInfo := (.leaf [(4,0,115,0,5)])
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
def g189columns : IndexTree ColumnInfo := (.fork 4 (.leaf [(1,0,188,0,5),(12,0,177,0,4),(16,0,173,0,5),(17,0,172,0,4)]) (.leaf [(24,0,165,0,4),(33,0,156,0,4),(132,0,57,0,4),(160,0,29,0,4)]))
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
def g127columns : IndexTree ColumnInfo := (.leaf [(32,0,95,0,8)])
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
def g191columns : IndexTree ColumnInfo := (.fork 19 (.fork 9 (.fork 4 (.leaf [(1,0,190,0,7),(2,0,189,0,8),(3,0,188,0,5),(4,0,187,0,7)]) (.fork 2 (.leaf [(6,0,185,0,5),(8,0,183,0,8)]) (.leaf [(0,8,163,20,6),(10,0,181,0,5),(12,0,179,0,5)]))) (.fork 5 (.fork 2 (.leaf [(4,8,163,16,5),(14,0,177,0,4)]) (.leaf [(16,0,175,0,8),(0,16,166,9,6),(1,16,166,8,5)])) (.fork 2 (.leaf [(19,0,172,0,4),(24,0,167,0,7)]) (.leaf [(16,8,163,4,5),(8,16,166,1,5),(25,0,166,0,4)])))) (.fork 9 (.fork 4 (.leaf [(9,16,166,0,4),(20,8,163,0,4),(32,0,159,0,8),(1,32,30,128,5)]) (.fork 2 (.leaf [(35,0,156,0,4),(40,0,151,0,5)]) (.leaf [(48,0,143,0,5),(56,0,135,0,4),(128,0,63,0,8)]))) (.fork 5 (.fork 2 (.leaf [(130,0,61,0,5),(4,128,27,32,5)]) (.leaf [(136,0,55,0,5),(160,0,31,0,7),(128,32,30,1,5)])) (.fork 2 (.leaf [(32,128,27,4,5),(161,0,30,0,4)]) (.leaf [(129,32,30,0,4),(164,0,27,0,4),(36,128,27,0,4)])))))
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
def g251columns : IndexTree ColumnInfo := (.leaf [(8,0,243,0,7)])
def g251autos : Array (List Nat) := #[[],[84,115],[99,65],[118,84,115,65],[118,81],[118,84,99,81]]
def g251levels : Nat → Packing
  | _ => emptyPacking
def g251index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g251 : Forest := ⟨251,7,fun j => g251samples[j]?.getD (0,0),g251columns,g251autos,g251levels,g251index⟩
def g255samples : Array (Bits × Bits) := #[(0x9b665c544a8481c32c829a3849d25a0c2e734bceaece0410b1910c9246b692285657c973ca335d593cb00f0546b90059eb43e97a932728851785431870f031165ac8b80393ba6e576270cc58c906b870841734e15dc89803598ab05c2460a6b1,0x104454110880808228020a2041d8002c08600a02808c02009111060244ac12008614a1024802115108904700443200508241c8821224200116051018407029164080a01212302c0942400010c90428108414142154888803090a9048202086a0),(0xf315668af28fdb1ca228365b7ccc05a0011317731e21482f697635c521d4e57b4580944cacd08190116899ef79421d834fcee4e488905930903982805fb1c61927af17aaf49049a676974192f0d0160363a1bd03830701b0dc1f8281c2dc6123,0x83112a82400c43108201140b24040542001210600e014836084820c40800442b4181104024900000902098cc210099010006246088901220003082011981800902040620cc814002101041843090160043212902810201b054050081825c2101),(0x380526282fa13ac851f4c9c505254980d6e8ec3804b3594a769d93b950ebc251b0d8e2a15610b8154799066089743516386914b45de9a6e1e91c2d64aa4bec2945782990b2d68e61aa4d3cd1b24a6ab680984b4c1298da14a63264e421a50a46,0x184000082381184051a442400021c800c760240c008201086414493150c8805030586481420228050588002082640402084818905528808149002d00020c144045280184104604602a043c40824a60b20098024012185a048212646400810a02),(0x96903da21572f2b1f1c959078994a771bc47364121282ac5966e24786e0f6b8886ae49c27124b27b7242ff2e0094e0b4b1b582696d3c94568c371a6b03b30075a8d6353ad9672c0089eb12ba6325f80dd24d451b8459a7c113618d0b812f118c,0x86100cb01034a2a12848198388d4226018030240202c8a411a0a044824066a838a240842212092185a40cf0a0080e094a530c6680a1400448645526011312024a0c7343889210800016b021a61259805924545098441a1c11120810b812e1184),(0xca830c6ee5a1c1ac77b2c4bb013b84b271c7189edce77b42164b82b2ec44ccc2202552493f52e619512b4f09e2177ba801c291327039cbf4fba1fd7ca29d36ceca40c4508827295a1b45be11b7c00687be220f65622167c80c13fe90c415919,0x1282044674a181cc515204830038803270c71014e5265b22464b9241a4004482002443590d10ca0850630203a411b2a000c201185038c3861ba0d078200d6480c204804048212d4a89449e11258006869a220d60222163c80c12ea00c414819),(0xadcb89db333a54791fc5b16de6a74b1fbdaa5224c4caa060c8434905e130b3e50875189fa3aee40ebf67487ce98db2673644923b555505294552488c144494c2312ef3656d2d51ee39b1b44e04f3d3ec4d148000ab72771f011403179f478e82,0xa991884a13221d3803c5e045a0014312e78660240442614040424905201081f109410899826ca6043646807ca808b20b342020284941850001124c8410049440302c118d6904416438b533460072d3ec490080008b50771c0014031517470802),(0xccf1d170b069949f14600d7679a83ea985e068495997ad010287ff4ea745b576050c4fa9e8e0fabd2497448bd27a5aa8acea4ac0268e4d44dc2df9de452a225ad1457b3d721818b9bf9e05034d50ecb938aed67098a522a72856072e55b8d214,0xce85130b040942f1560095449a91aad8dc0e80b5196a18140955b282345b194266c47298868eeb9221d4601c27a00e8acf04a8036004c04cc8c58ecc43a23d68161791d311c0cb9abcc24434d40e8b9388ed67018a522072852072e55a0d214),(0x442aa5b9d884c622461c21eaaaf556fac8da8923687abbfb99c9c28096422e0eb83cb34c1d8918aec8c55d99f53bc2670104934ee2f27258616b2c55a56fa8970e02486406e9b92b5242282d15890d903f02672424a3e96d3ce1d022fa0aa8e8,0x460a679588446000a40a01aa08c414e80818810338389a92898982c08602320ec02091061180118a88016c815113416481048146a2821250206d8051a4632a958802cc600689381b004a400915810c003602652424a380613ce19002e808a0e8),(0,0)]
def g255columns : IndexTree ColumnInfo := (.leaf [(64,0,191,0,11)])
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
def g383columns : IndexTree ColumnInfo := (.fork 29 (.fork 14 (.fork 7 (.fork 3 (.leaf [(1,0,382,0,9),(0,1,332,50,7),(2,0,381,0,9)]) (.leaf [(0,2,312,69,7),(3,0,380,0,6),(2,1,332,48,6),(1,2,312,68,6)])) (.fork 3 (.leaf [(4,0,379,0,11),(5,0,378,0,7),(7,0,376,0,5)]) (.leaf [(5,2,312,64,5),(8,0,375,0,9),(0,8,99,276,7),(12,0,371,0,8)]))) (.fork 7 (.fork 3 (.leaf [(13,0,354,0,4),(14,0,369,0,5),(16,0,367,0,11)]) (.leaf [(17,0,366,0,8),(18,0,365,0,7),(19,0,364,0,5),(18,1,332,32,5)])) (.fork 4 (.leaf [(24,0,359,0,8),(25,0,358,0,5),(28,0,355,0,7),(20,8,99,256,5)]) (.leaf [(32,0,351,0,11),(33,0,350,0,8),(32,1,332,18,6),(35,0,348,0,5)])))) (.fork 15 (.fork 7 (.fork 3 (.leaf [(34,1,332,16,5),(44,0,339,0,5),(49,0,334,0,7)]) (.leaf [(48,1,332,2,5),(33,16,326,8,5),(56,0,327,0,5),(64,0,319,0,11)])) (.fork 4 (.leaf [(65,0,318,0,7),(66,0,317,0,8),(67,0,316,0,5),(65,2,312,4,5)]) (.leaf [(70,0,313,0,7),(34,64,29,256,5),(256,0,127,0,9),(0,256,23,104,7)]))) (.fork 7 (.fork 3 (.leaf [(264,0,119,0,6),(256,8,99,20,6),(8,256,23,96,6)]) (.leaf [(268,0,115,0,5),(260,8,99,16,5),(280,0,103,0,5),(272,8,99,4,5)])) (.fork 4 (.leaf [(288,0,95,0,8),(289,0,94,0,5),(40,256,23,64,5),(304,0,79,0,5)]) (.leaf [(320,0,63,0,8),(322,0,61,0,5),(258,64,61,0,5),(352,0,31,0,7)])))))
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
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem bl15_3 : block g15 3 0 1 = true := by
  apply wideBlock (depth:=0)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

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
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem bl31_5 : block g31 5 0 3 = true := by
  apply wideBlock (depth:=0)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem bl31_6 : block g31 6 0 1 = true := by
  apply wideBlock (depth:=0)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

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
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem bl111_6 : block g111 6 0 1 = true := by
  apply wideBlock (depth:=0)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

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
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem bl189_6 : block g189 6 0 3 = true := by
  apply wideBlock (depth:=0)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem bl189_7 : block g189 7 0 1 = true := by
  apply wideBlock (depth:=0)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

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
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem bl191_6 : block g191 6 0 1 = true := by
  apply wideBlock (depth:=0)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem bl191_7 : block g191 7 0 28 = true := by
  apply wideBlock (depth:=3)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem bl191_8 : block g191 8 0 100 = true := by
  apply wideBlock (depth:=5)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem bl191_9 : block g191 9 0 12 = true := by
  apply wideBlock (depth:=2)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem bl191_10 : block g191 10 0 1 = true := by
  apply wideBlock (depth:=0)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

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
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem bl383_8 : block g383 8 0 25 = true := by
  apply wideBlock (depth:=3)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem bl383_9 : block g383 9 0 91 = true := by
  apply wideBlock (depth:=5)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem bl383_10 : block g383 10 0 41 = true := by
  apply wideBlock (depth:=4)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem bl383_11 : block g383 11 0 6 = true := by
  apply wideBlock (depth:=1)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem bl383_12 : block g383 12 0 1 = true := by
  apply wideBlock (depth:=0)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

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
def deadcolumns : IndexTree ColumnInfo := (.fork 63 (.fork 31 (.fork 15 (.fork 7 (.fork 3 (.leaf [(1,0,510,0,12),(0,1,460,50,8),(2,0,509,0,12)]) (.leaf [(0,2,440,69,8),(3,0,508,0,9),(2,1,460,48,7),(4,0,507,0,12)])) (.fork 4 (.leaf [(0,4,369,138,8),(5,0,506,0,8),(6,0,505,0,9),(4,2,440,65,7)]) (.leaf [(2,4,369,136,7),(7,0,504,0,7),(5,2,440,64,6),(8,0,503,0,12)]))) (.fork 8 (.fork 4 (.leaf [(0,8,227,276,8),(9,0,486,0,8),(10,0,501,0,8),(12,0,499,0,9)]) (.leaf [(8,4,369,130,7),(4,8,227,272,7),(14,0,497,0,7),(10,4,369,128,6)])) (.fork 4 (.leaf [(15,0,480,0,4),(16,0,495,0,13),(0,16,486,9,10),(17,0,494,0,11)]) (.leaf [(16,1,460,34,7),(19,0,492,0,8),(16,4,353,138,7),(21,0,490,0,7)])))) (.fork 16 (.fork 8 (.fork 4 (.leaf [(21,2,424,64,5),(24,0,487,0,11),(8,16,486,1,9),(25,0,486,0,8)]) (.leaf [(9,16,486,0,8),(27,0,484,0,5),(11,16,484,0,5),(24,4,353,130,6)])) (.fork 4 (.leaf [(29,0,482,0,5),(26,4,353,128,5),(32,0,479,0,12),(0,32,94,385,8)]) (.leaf [(32,1,460,18,7),(1,32,94,384,7),(35,0,476,0,7),(34,1,460,16,6)]))) (.fork 8 (.fork 4 (.leaf [(36,0,347,0,8),(39,0,344,0,4),(40,0,471,0,8),(49,0,462,0,8)]) (.leaf [(48,1,460,2,6),(50,1,460,0,5),(56,0,455,0,7),(64,0,447,0,13)])) (.fork 4 (.leaf [(0,64,189,258,10),(66,0,445,0,11),(2,64,189,256,9),(67,0,444,0,8)]) (.leaf [(66,1,396,48,6),(70,0,441,0,8),(69,2,440,0,5),(74,0,437,0,7)]))))) (.fork 31 (.fork 15 (.fork 7 (.fork 3 (.leaf [(74,4,305,128,5),(80,0,431,0,11),(83,0,428,0,7)]) (.leaf [(96,0,415,0,9),(96,1,396,18,6),(98,1,396,16,5),(128,0,383,0,13)])) (.fork 4 (.leaf [(128,1,332,50,7),(3,128,344,36,6),(132,0,379,0,11),(4,128,347,32,9)]) (.leaf [(133,0,378,0,7),(134,0,377,0,8),(132,2,312,65,6),(133,2,312,64,5)]))) (.fork 8 (.fork 4 (.leaf [(136,0,375,0,9),(128,8,99,276,7),(140,0,371,0,8),(132,8,99,272,6)]) (.leaf [(138,4,369,0,5),(144,0,367,0,11),(152,4,353,2,5),(160,0,351,0,11)])) (.fork 4 (.leaf [(160,1,332,18,6),(162,1,332,16,5),(164,0,347,0,8),(36,128,347,0,8)]) (.leaf [(172,0,339,0,5),(176,1,332,2,5),(180,0,331,0,5),(192,0,319,0,11)])))) (.fork 16 (.fork 8 (.fork 4 (.leaf [(198,0,313,0,7),(256,0,255,0,12),(258,0,189,0,8),(260,0,251,0,8)]) (.leaf [(264,0,247,0,9),(256,8,227,20,7),(8,256,151,96,7),(268,0,243,0,7)])) (.fork 4 (.leaf [(260,8,227,16,6),(273,0,238,0,7),(280,0,231,0,8),(276,8,227,0,5)]) (.leaf [(288,0,223,0,9),(256,32,94,129,7),(32,256,151,72,7),(257,32,94,128,6)]))) (.fork 8 (.fork 4 (.leaf [(296,0,215,0,7),(40,256,151,64,6),(304,0,207,0,6),(288,16,198,9,6)]) (.leaf [(273,32,78,128,5),(56,256,135,64,5),(320,0,191,0,11),(256,64,189,2,9)])) (.fork 4 (.leaf [(322,0,189,0,8),(258,64,189,0,8),(324,0,187,0,7),(324,8,163,16,5)]) (.leaf [(321,32,30,128,5),(388,8,99,16,5),(168,256,23,64,5),(224,256,23,8,5)]))))))
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
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem alldead8 : block dead 8 0 2 = true := by
  apply wideBlock (depth:=0)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem alldead9 : block dead 9 0 25 = true := by
  apply wideBlock (depth:=3)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem alldead10 : block dead 10 0 156 = true := by
  apply wideBlock (depth:=6)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem alldead11 : block dead 11 0 183 = true := by
  apply wideBlock (depth:=6)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem alldead12 : block dead 12 0 32 = true := by
  apply wideBlock (depth:=3)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem alldead13 : block dead 13 0 4 = true := by
  apply wideBlock (depth:=0)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem alldead14 : block dead 14 0 1 = true := by
  apply wideBlock (depth:=0)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

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


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ordinaryFull : Lower (vars 511) (graphGoal 511) 15 := by
  apply lower_impossible (proper_of _ (by decide +kernel)) _ _
  · intro a ha
    apply essential_ok (xs:=graphPairs 511 13438558465) (by decide +kernel)
    exact List.mem_toFinset.mpr (show a ∈ vars 511 from ha)
  · rw [show vars 511 = inputs by decide +kernel,show graphGoal 511 = graph by decide +kernel]
    exact dead_start (prior:=boundsBefore known383) (before_sound _ valid383) geomdead tablesdead

def knownFull := extendKnown known383 15 [(511,[])]
theorem validFull : Known knownFull := extendKnown_ok valid383 ordinaryFull (by decide +kernel)
end PEqualNP.Outside.L_meta_5006
namespace PEqualNP.Outside.L_meta_5006.Negative15
open PEqualNP.CircuitLowerBounds

def liveData4 (i : Nat) : Nat := 0xfa00

def liveLevels : Nat → Packing
  | 4 => (1,1,0,0,0,0,0,liveData4)
  | _ => emptyPacking

def liveIndex : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none

def orSamples : Array (Bits × Bits) := #[(0xff00ff00ffff00ffff00ff00ffff00ffff00ff00ffff00ffff00ff00ffff00ffff00ff00ffff00ffff00ff00ffff00ffff00ff00ffff00ffff00ff00ffff00ffff00ff00ffff00ffff00ff00ffff00ffff00ff00ffff00ffff00ff00ffff00ff,0x525252525252525252525252525252525252525252525252525252525252525252525252525252525252525252525252525252525252525252525252525252525252525252525252525252525252525252525252525252525252525252525252),
  (0xffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffff,0x848484848484848484848484848484848484848484848484848484848484848484848484848484848484848484848484848484848484848484848484848484848484848484848484848484848484848484848484848484848484848484848484),
  (0xffffffff00ffff00ffffffff00ffff00ffffffff00ffff00ffffffff00ffff00ffffffff00ffff00ffffffff00ffff00ffffffff00ffff00ffffffff00ffff00ffffffff00ffff00ffffffff00ffff00ffffffff00ffff00ffffffff00ffff00,0x181818181818181818181818181818181818181818181818181818181818181818181818181818181818181818181818181818181818181818181818181818181818181818181818181818181818181818181818181818181818181818181818),
  (0xffffffffff000000ffffffffff000000ffffffffff000000ffffffffff000000ffffffffff000000ffffffffff000000ffffffffff000000ffffffffff000000ffffffffff000000ffffffffff000000ffffffffff000000ffffffffff000000,0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0),
  (0x0,0x0),
  (0x0,0x0),
  (0x0,0x0),
  (0x0,0x0),
  (0x0,0x0)]

def orSymmetries : Array (List Nat) := #[[],[48,33]]

def orCols : IndexTree ColumnInfo := (.leaf [(0,0,15,0,4)])

def orForest : Forest := ⟨8207,4,fun j => orSamples[j]?.getD (0,0),orCols,orSymmetries,liveLevels,liveIndex⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem orGeometry : graphValid orForest (boundsBefore knownFull) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem allAt4 : block orForest 4 0 1 = true := by
  apply wideBlock (depth:=0)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

theorem orTables : checkedTables orForest 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block orForest 0 0 0 = true)
  · exact (rfl : block orForest 1 0 0 = true)
  · exact (rfl : block orForest 2 0 0 = true)
  · exact (rfl : block orForest 3 0 0 = true)
  · exact allAt4

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withoutPositive : Impossible (graphGoal 15) 4 (vars 8207).toFinset := by
  exact root_index (g:=orForest) (before_sound _ validFull) orGeometry orTables
    (k:=4) (by decide) (i:=0) (by decide +kernel)

end PEqualNP.Outside.L_meta_5006.Negative15
namespace PEqualNP.Outside.L_meta_5006
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem negativeBound15 : Lower (vars 8207) (graphGoal 8207) 5 := by
  apply lower_impossible (proper_of _ (by decide +kernel)) _ Negative15.withoutPositive
  intro a ha
  apply essential_ok (xs:=polarPairs 8207 (graphPairs 15 8449)) (by decide +kernel)
  rw [show ((polarPairs 8207 (graphPairs 15 8449)).map Prod.fst).toFinset = (vars 8207).toFinset by decide +kernel]
  exact List.mem_toFinset.mpr ha

def entries8207 := extendKnown knownFull 5 [(8207,[]),(8221,[50,65]),(8327,[115,99,83,67]),(8357,[114,33,97,82,50,65]),(8473,[131,115,99,50,82,65]),(8545,[130,33,113,99,82,65])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound8207 : Known entries8207 := extendKnown_ok validFull negativeBound15 (by decide +kernel)
end PEqualNP.Outside.L_meta_5006
namespace PEqualNP.Outside.L_meta_5006.Negative23
open PEqualNP.CircuitLowerBounds

def liveData4 (i : Nat) : Nat := 0xfa00

def liveLevels : Nat → Packing
  | 4 => (1,1,0,0,0,0,0,liveData4)
  | _ => emptyPacking

def liveIndex : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none

def orSamples : Array (Bits × Bits) := #[(0xff00ffffffff00ffff00ffffffff00ffff00ffffffff00ffff00ffffffff00ffff00ffffffff00ffff00ffffffff00ffff00ffffffff00ffff00ffffffff00ffff00ffffffff00ffff00ffffffff00ffff00ffffffff00ffff00ffffffff00ff,0x121212121212121212121212121212121212121212121212121212121212121212121212121212121212121212121212121212121212121212121212121212121212121212121212121212121212121212121212121212121212121212121212),
  (0xffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffff,0x444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444),
  (0xffffff0000ffff00ffffff0000ffff00ffffff0000ffff00ffffff0000ffff00ffffff0000ffff00ffffff0000ffff00ffffff0000ffff00ffffff0000ffff00ffffff0000ffff00ffffff0000ffff00ffffff0000ffff00ffffff0000ffff00,0x989898989898989898989898989898989898989898989898989898989898989898989898989898989898989898989898989898989898989898989898989898989898989898989898989898989898989898989898989898989898989898989898),
  (0x0,0x0),
  (0xffffffffff000000ffffffffff000000ffffffffff000000ffffffffff000000ffffffffff000000ffffffffff000000ffffffffff000000ffffffffff000000ffffffffff000000ffffffffff000000ffffffffff000000ffffffffff000000,0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0),
  (0x0,0x0),
  (0x0,0x0),
  (0x0,0x0),
  (0x0,0x0)]

def orSymmetries : Array (List Nat) := #[[],[16,66]]

def orCols : IndexTree ColumnInfo := (.leaf [(0,0,23,0,4)])

def orForest : Forest := ⟨8215,4,fun j => orSamples[j]?.getD (0,0),orCols,orSymmetries,liveLevels,liveIndex⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem orGeometry : graphValid orForest (boundsBefore entries8207) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem allAt4 : block orForest 4 0 1 = true := by
  apply wideBlock (depth:=0)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

theorem orTables : checkedTables orForest 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block orForest 0 0 0 = true)
  · exact (rfl : block orForest 1 0 0 = true)
  · exact (rfl : block orForest 2 0 0 = true)
  · exact (rfl : block orForest 3 0 0 = true)
  · exact allAt4

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withoutPositive : Impossible (graphGoal 23) 4 (vars 8215).toFinset := by
  exact root_index (g:=orForest) (before_sound _ sound8207) orGeometry orTables
    (k:=4) (by decide) (i:=0) (by decide +kernel)

end PEqualNP.Outside.L_meta_5006.Negative23
namespace PEqualNP.Outside.L_meta_5006
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem negativeBound23 : Lower (vars 8215) (graphGoal 8215) 5 := by
  apply lower_impossible (proper_of _ (by decide +kernel)) _ Negative23.withoutPositive
  intro a ha
  apply essential_ok (xs:=polarPairs 8215 (graphPairs 23 257)) (by decide +kernel)
  rw [show ((polarPairs 8215 (graphPairs 23 257)).map Prod.fst).toFinset = (vars 8215).toFinset by decide +kernel]
  exact List.mem_toFinset.mpr ha

def entries8215 := extendKnown entries8207 5 [(8215,[]),(8219,[50,65]),(8231,[84]),(8249,[65,33,82,49]),(8291,[66,100,82,50]),(8355,[114,33,97,82,50,65]),(8369,[114,33,97,82,49]),(8497,[130,114,33,97,82,49])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound8215 : Known entries8215 := extendKnown_ok sound8207 negativeBound23 (by decide +kernel)
end PEqualNP.Outside.L_meta_5006
namespace PEqualNP.Outside.L_meta_5006.Negative31
open PEqualNP.CircuitLowerBounds

def liveData7 (i : Nat) : Nat := 0xa8645fa00

def moveIndex7 (i : Nat) : Nat := 0xebc200002a1640000000000000c25e5400986e21b8ea1ce3307030a1100

def liveData6 (i : Nat) : Nat := 0xad27209424140210c03018a011c04280b2559705ba83c3c07e95600fca9401f932803f2a3007e50600fc98c01f921803d445007c84600

def moveIndex6 (i : Nat) : Nat := 0x108e000000000059683b5010a00

def liveData5 (i : Nat) : Nat := 0x2942786550600f48ce11803e22284600

def moveIndex5 (i : Nat) : Nat := 0x90

def liveData4 (i : Nat) : Nat := 0x11e9dc6550600

def liveLevels : Nat → Packing
  | 7 => (1,1,3,0,0,0,0,liveData7)
  | 6 => (9,2,3,0,0,7,0,liveData6)
  | 5 => (3,3,3,0,0,4,0,liveData5)
  | 4 => (1,4,3,0,0,0,0,liveData4)
  | _ => emptyPacking

def liveIndex : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 10 22 4 9 4 1 moveIndex7
  | 6 => lookupWord 5 10 3 9 2 3 moveIndex6
  | 5 => lookupWord 1 2 0 4 0 0 moveIndex5
  | _ => fun _ => none

def orSamples : Array (Bits × Bits) := #[(0x7ff001fffff800fffffc007ff001ffc007ff001ffc007ffffffffff800ffe003fffff001fffff800ffe003ff800ffe003ff800fffffffffff001ffc007ffffe003fffff001ffc007ff001ffc007ff001ffffffffffe003ff800fffffc007ff,0x290520a4148290520a4148290520a4148290520a4148290520a4148290520a4148290520a4148290520a4148290520a4148290520a4148290520a4148290520a4148290520a4148290520a4148290520a4148290520a4148290520a414829052),
  (0xff800001ffffffffffffffff800001fffff800001fffff800ffe003fffff000003ffffffffffffffff000003fffff000003fffff001ffc007ffffe000007fffffffffffffffe000007ffffe000007ffffe003ff800fffffc00000fffffffffff,0x42284508a1142284508a1142284508a1142284508a1142284508a1142284508a1142284508a1142284508a1142284508a1142284508a1142284508a1142284508a1142284508a1142284508a1142284508a1142284508a1142284508a1142284),
  (0xfffffffe003fffff001ffffffffffe00000000001ffffffff000003ffffffffffc007ffffe003ffffffffffc00000000003fffffffe000007ffffffffff800fffffc007ffffffffff800000000007fffffffc00000fffffffffff001fffff800,0xc4188310620c4188310620c4188310620c4188310620c4188310620c4188310620c4188310620c4188310620c4188310620c4188310620c4188310620c4188310620c4188310620c4188310620c4188310620c4188310620c4188310620c418),
  (0xffffffffffc00000001fffffffffffffffffffffe00000000000003fffffffffffff800000003fffffffffffffffffffffc00000000000007fffffffffffff000000007fffffffffffffffffffff80000000000000fffffffffffffe00000000,0x700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e0),
  (0x1fffffffffffffffffffffffffffffffffffc0000000000000000000003fffffffffffffffffffffffffffffffffff80000000000000000000007fffffffffffffffffffffffffffffffffff0000000000000000000000,0x80700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700),
  (0x0,0x0),
  (0x0,0x0),
  (0x0,0x0),
  (0x0,0x0)]

def orSymmetries : Array (List Nat) := #[[],[65,50],[16,66],[16,32,48,64],[32,67],[32,49,64,16],[48,33],[48,65,32,33],[64,16,33,50],[64,49]]

def orCols : IndexTree ColumnInfo := (.fork 3 (.leaf [(0,0,31,0,7),(1,0,30,0,4),(16386,0,8221,0,5)]) (.leaf [(16388,0,8219,0,5),(16392,0,8215,0,5),(16400,0,8207,0,5)]))

def orForest : Forest := ⟨8223,7,fun j => orSamples[j]?.getD (0,0),orCols,orSymmetries,liveLevels,liveIndex⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem orGeometry : graphValid orForest (boundsBefore entries8215) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem allAt7 : block orForest 7 0 1 = true := by
  apply wideBlock (depth:=0)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem allAt6 : block orForest 6 0 9 = true := by
  apply wideBlock (depth:=2)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem allAt5 : block orForest 5 0 3 = true := by
  apply wideBlock (depth:=0)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem allAt4 : block orForest 4 0 1 = true := by
  apply wideBlock (depth:=0)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

theorem orTables : checkedTables orForest 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block orForest 0 0 0 = true)
  · exact (rfl : block orForest 1 0 0 = true)
  · exact (rfl : block orForest 2 0 0 = true)
  · exact (rfl : block orForest 3 0 0 = true)
  · exact allAt4
  · exact allAt5
  · exact allAt6
  · exact allAt7

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withoutPositive : Impossible (graphGoal 31) 7 (vars 8223).toFinset := by
  exact root_index (g:=orForest) (before_sound _ sound8215) orGeometry orTables
    (k:=7) (by decide) (i:=0) (by decide +kernel)

end PEqualNP.Outside.L_meta_5006.Negative31
namespace PEqualNP.Outside.L_meta_5006
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem negativeBound31 : Lower (vars 8223) (graphGoal 8223) 8 := by
  apply lower_impossible (proper_of _ (by decide +kernel)) _ Negative31.withoutPositive
  intro a ha
  apply essential_ok (xs:=polarPairs 8223 (graphPairs 31 8449)) (by decide +kernel)
  rw [show ((polarPairs 8223 (graphPairs 31 8449)).map Prod.fst).toFinset = (vars 8223).toFinset by decide +kernel]
  exact List.mem_toFinset.mpr ha

def entries8223 := extendKnown entries8215 8 [(8223,[]),(8359,[115,67,100,83]),(8505,[131,115,65,50,98,81]),(8547,[131,50,66,116,99,82])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound8223 : Known entries8223 := extendKnown_ok sound8215 negativeBound31 (by decide +kernel)
end PEqualNP.Outside.L_meta_5006
namespace PEqualNP.Outside.L_meta_5006.Negative47
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withoutPositive : Impossible (graphGoal 47) 5 (vars 8239).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=8239) (16392,0,8231,0,5) _ (before_sound _ sound8223) (by decide +kernel))
    [] (pool:=(vars (poolMask 8239 (16392,0,8231,0,5)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end PEqualNP.Outside.L_meta_5006.Negative47
namespace PEqualNP.Outside.L_meta_5006
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem negativeBound47 : Lower (vars 8239) (graphGoal 8239) 6 := by
  apply lower_impossible (proper_of _ (by decide +kernel)) _ Negative47.withoutPositive
  intro a ha
  apply essential_ok (xs:=polarPairs 8239 (graphPairs 47 8449)) (by decide +kernel)
  rw [show ((polarPairs 8239 (graphPairs 47 8449)).map Prod.fst).toFinset = (vars 8239).toFinset by decide +kernel]
  exact List.mem_toFinset.mpr ha

def entries8239 := extendKnown entries8223 6 [(8253,[50,65]),(8343,[115,99,83,67]),(8373,[114,81,98,50,65]),(8531,[131,50,114,82,99,66]),(8561,[130,50,81,115,98,65])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound8239 : Known entries8239 := extendKnown_ok sound8223 negativeBound47 (by decide +kernel)
end PEqualNP.Outside.L_meta_5006
namespace PEqualNP.Outside.L_meta_5006.Negative55
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withoutPositive : Impossible (graphGoal 55) 5 (vars 8247).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=8247) (16400,0,8231,0,5) _ (before_sound _ sound8239) (by decide +kernel))
    [] (pool:=(vars (poolMask 8247 (16400,0,8231,0,5)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end PEqualNP.Outside.L_meta_5006.Negative55
namespace PEqualNP.Outside.L_meta_5006
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem negativeBound55 : Lower (vars 8247) (graphGoal 8247) 6 := by
  apply lower_impossible (proper_of _ (by decide +kernel)) _ Negative55.withoutPositive
  intro a ha
  apply essential_ok (xs:=polarPairs 8247 (graphPairs 55 257)) (by decide +kernel)
  rw [show ((polarPairs 8247 (graphPairs 55 257)).map Prod.fst).toFinset = (vars 8247).toFinset by decide +kernel]
  exact List.mem_toFinset.mpr ha

def entries8247 := extendKnown entries8239 6 [(8307,[98,50]),(8371,[114,81,98,50,65])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound8247 : Known entries8247 := extendKnown_ok sound8239 negativeBound55 (by decide +kernel)
end PEqualNP.Outside.L_meta_5006
namespace PEqualNP.Outside.L_meta_5006.Negative79
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withoutPositive : Impossible (graphGoal 79) 5 (vars 8271).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=8271) (16448,0,8207,0,5) _ (before_sound _ sound8247) (by decide +kernel))
    [] (pool:=(vars (poolMask 8271 (16448,0,8207,0,5)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end PEqualNP.Outside.L_meta_5006.Negative79
namespace PEqualNP.Outside.L_meta_5006
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem negativeBound79 : Lower (vars 8271) (graphGoal 8271) 6 := by
  apply lower_impossible (proper_of _ (by decide +kernel)) _ Negative79.withoutPositive
  intro a ha
  apply essential_ok (xs:=polarPairs 8271 (graphPairs 79 16785665)) (by decide +kernel)
  rw [show ((polarPairs 8271 (graphPairs 79 16785665)).map Prod.fst).toFinset = (vars 8271).toFinset by decide +kernel]
  exact List.mem_toFinset.mpr ha

def entries8271 := extendKnown entries8247 6 [(8519,[131,115,83,67,98])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound8271 : Known entries8271 := extendKnown_ok sound8247 negativeBound79 (by decide +kernel)
end PEqualNP.Outside.L_meta_5006
namespace PEqualNP.Outside.L_meta_5006.Negative143
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withoutPositive : Impossible (graphGoal 143) 5 (vars 8335).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=8335) (16392,0,8327,0,5) _ (before_sound _ sound8271) (by decide +kernel))
    [] (pool:=(vars (poolMask 8335 (16392,0,8327,0,5)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end PEqualNP.Outside.L_meta_5006.Negative143
namespace PEqualNP.Outside.L_meta_5006
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem negativeBound143 : Lower (vars 8335) (graphGoal 8335) 6 := by
  apply lower_impossible (proper_of _ (by decide +kernel)) _ Negative143.withoutPositive
  intro a ha
  apply essential_ok (xs:=polarPairs 8335 (graphPairs 143 536879361)) (by decide +kernel)
  rw [show ((polarPairs 8335 (graphPairs 143 536879361)).map Prod.fst).toFinset = (vars 8335).toFinset by decide +kernel]
  exact List.mem_toFinset.mpr ha

def entries8335 := extendKnown entries8271 6 [(8335,[])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound8335 : Known entries8335 := extendKnown_ok sound8271 negativeBound143 (by decide +kernel)
end PEqualNP.Outside.L_meta_5006
namespace PEqualNP.Outside.L_meta_5006.Negative173
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withoutPositive : Impossible (graphGoal 173) 5 (vars 8365).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=8365) (16392,0,8357,0,5) _ (before_sound _ sound8335) (by decide +kernel))
    [] (pool:=(vars (poolMask 8365 (16392,0,8357,0,5)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end PEqualNP.Outside.L_meta_5006.Negative173
namespace PEqualNP.Outside.L_meta_5006
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem negativeBound173 : Lower (vars 8365) (graphGoal 8365) 6 := by
  apply lower_impossible (proper_of _ (by decide +kernel)) _ Negative173.withoutPositive
  intro a ha
  apply essential_ok (xs:=polarPairs 8365 (graphPairs 173 536879877)) (by decide +kernel)
  rw [show ((polarPairs 8365 (graphPairs 173 536879877)).map Prod.fst).toFinset = (vars 8365).toFinset by decide +kernel]
  exact List.mem_toFinset.mpr ha

def entries8365 := extendKnown entries8335 6 [(8365,[]),(8493,[135,50]),(8523,[130,114,98,33,81]),(8537,[130,50,98,82,115,66])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound8365 : Known entries8365 := extendKnown_ok sound8335 negativeBound173 (by decide +kernel)
end PEqualNP.Outside.L_meta_5006
namespace PEqualNP.Outside.L_meta_5006.Negative185
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withoutPositive : Impossible (graphGoal 185) 5 (vars 8377).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=8377) (16392,0,8369,0,5) _ (before_sound _ sound8365) (by decide +kernel))
    [] (pool:=(vars (poolMask 8377 (16392,0,8369,0,5)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end PEqualNP.Outside.L_meta_5006.Negative185
namespace PEqualNP.Outside.L_meta_5006
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem negativeBound185 : Lower (vars 8377) (graphGoal 8377) 6 := by
  apply lower_impossible (proper_of _ (by decide +kernel)) _ Negative185.withoutPositive
  intro a ha
  apply essential_ok (xs:=polarPairs 8377 (graphPairs 185 1342193668)) (by decide +kernel)
  rw [show ((polarPairs 8377 (graphPairs 185 1342193668)).map Prod.fst).toFinset = (vars 8377).toFinset by decide +kernel]
  exact List.mem_toFinset.mpr ha

def entries8377 := extendKnown entries8365 6 [(8377,[]),(8419,[99,50,33,65])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound8377 : Known entries8377 := extendKnown_ok sound8365 negativeBound185 (by decide +kernel)
end PEqualNP.Outside.L_meta_5006
namespace PEqualNP.Outside.L_meta_5006.Negative63
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withoutPositive : Impossible (graphGoal 63) 8 (vars 8255).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=8255) (16416,0,8223,0,8) _ (before_sound _ sound8377) (by decide +kernel))
    [] (pool:=(vars (poolMask 8255 (16416,0,8223,0,8)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end PEqualNP.Outside.L_meta_5006.Negative63
namespace PEqualNP.Outside.L_meta_5006
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem negativeBound63 : Lower (vars 8255) (graphGoal 8255) 9 := by
  apply lower_impossible (proper_of _ (by decide +kernel)) _ Negative63.withoutPositive
  intro a ha
  apply essential_ok (xs:=polarPairs 8255 (graphPairs 63 8449)) (by decide +kernel)
  rw [show ((polarPairs 8255 (graphPairs 63 8449)).map Prod.fst).toFinset = (vars 8255).toFinset by decide +kernel]
  exact List.mem_toFinset.mpr ha

def entries8255 := extendKnown entries8377 9 [(8255,[]),(8563,[131,84,115,98])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound8255 : Known entries8255 := extendKnown_ok sound8377 negativeBound63 (by decide +kernel)
end PEqualNP.Outside.L_meta_5006
namespace PEqualNP.Outside.L_meta_5006.Negative95
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withoutPositive : Impossible (graphGoal 95) 8 (vars 8287).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=8287) (16448,0,8223,0,8) _ (before_sound _ sound8255) (by decide +kernel))
    [] (pool:=(vars (poolMask 8287 (16448,0,8223,0,8)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end PEqualNP.Outside.L_meta_5006.Negative95
namespace PEqualNP.Outside.L_meta_5006
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem negativeBound95 : Lower (vars 8287) (graphGoal 8287) 9 := by
  apply lower_impossible (proper_of _ (by decide +kernel)) _ Negative95.withoutPositive
  intro a ha
  apply essential_ok (xs:=polarPairs 8287 (graphPairs 95 16785665)) (by decide +kernel)
  rw [show ((polarPairs 8287 (graphPairs 95 16785665)).map Prod.fst).toFinset = (vars 8287).toFinset by decide +kernel]
  exact List.mem_toFinset.mpr ha

def entries8287 := extendKnown entries8255 9 [(8287,[]),(8423,[67,116,83]),(8551,[131,67,116,83,98]),(8633,[98,134,114,81])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound8287 : Known entries8287 := extendKnown_ok sound8255 negativeBound95 (by decide +kernel)
end PEqualNP.Outside.L_meta_5006
namespace PEqualNP.Outside.L_meta_5006.Negative119
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withoutPositive : Impossible (graphGoal 119) 6 (vars 8311).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=8311) (16388,0,8307,0,6) _ (before_sound _ sound8287) (by decide +kernel))
    [] (pool:=(vars (poolMask 8311 (16388,0,8307,0,6)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end PEqualNP.Outside.L_meta_5006.Negative119
namespace PEqualNP.Outside.L_meta_5006
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem negativeBound119 : Lower (vars 8311) (graphGoal 8311) 7 := by
  apply lower_impossible (proper_of _ (by decide +kernel)) _ Negative119.withoutPositive
  intro a ha
  apply essential_ok (xs:=polarPairs 8311 (graphPairs 119 16777473)) (by decide +kernel)
  rw [show ((polarPairs 8311 (graphPairs 119 16777473)).map Prod.fst).toFinset = (vars 8311).toFinset by decide +kernel]
  exact List.mem_toFinset.mpr ha

def entries8311 := extendKnown entries8287 7 [(8311,[])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound8311 : Known entries8311 := extendKnown_ok sound8287 negativeBound119 (by decide +kernel)
end PEqualNP.Outside.L_meta_5006
namespace PEqualNP.Outside.L_meta_5006.Negative159
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withoutPositive : Impossible (graphGoal 159) 8 (vars 8351).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=8351) (16512,0,8223,0,8) _ (before_sound _ sound8311) (by decide +kernel))
    [] (pool:=(vars (poolMask 8351 (16512,0,8223,0,8)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end PEqualNP.Outside.L_meta_5006.Negative159
namespace PEqualNP.Outside.L_meta_5006
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem negativeBound159 : Lower (vars 8351) (graphGoal 8351) 9 := by
  apply lower_impossible (proper_of _ (by decide +kernel)) _ Negative159.withoutPositive
  intro a ha
  apply essential_ok (xs:=polarPairs 8351 (graphPairs 159 536879361)) (by decide +kernel)
  rw [show ((polarPairs 8351 (graphPairs 159 536879361)).map Prod.fst).toFinset = (vars 8351).toFinset by decide +kernel]
  exact List.mem_toFinset.mpr ha

def entries8351 := extendKnown entries8311 9 [(8351,[]),(8367,[84,115]),(8509,[131,65,50,114,81]),(8569,[130,114,98,81])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound8351 : Known entries8351 := extendKnown_ok sound8311 negativeBound159 (by decide +kernel)
end PEqualNP.Outside.L_meta_5006
namespace PEqualNP.Outside.L_meta_5006.Negative187
open PEqualNP.CircuitLowerBounds

def liveData7 (i : Nat) : Nat := 0x54c9fa00

def moveIndex7 (i : Nat) : Nat := 0xb02e0

def liveData6 (i : Nat) : Nat := 0x2921028fe99a00fc58600

def moveIndex6 (i : Nat) : Nat := 0x0

def liveData5 (i : Nat) : Nat := 0x6f26658600

def liveLevels : Nat → Packing
  | 7 => (1,1,3,0,0,0,0,liveData7)
  | 6 => (2,2,3,0,0,3,0,liveData6)
  | 5 => (1,3,3,0,0,0,0,liveData5)
  | _ => emptyPacking

def liveIndex : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 4 0 5 1 0 moveIndex7
  | 6 => lookupWord 1 2 0 4 0 0 moveIndex6
  | _ => fun _ => none

def orSamples : Array (Bits × Bits) := #[(0xfffe0001fffc00007fff00003fff80000ffff00001ffff00000ffffe00001ffffe00000ffff800007fff800007fffffffffffffffffffff00003fffe00003fffffffffffffffffffffffffffffffc00001ffffe000007fffffffffffffffffff,0x12022000280c48020a0104000a0189002240512010480a1200a120142400024024240121204890040902890090902848122409090091005000214014200204014600924024a0121004848024280484002428024240090a00909002490090a012),
  (0xfffffffe000000007fffffffc00000000ffffffffe000000000fffffffffe0000000000fffffffff8000000007fffc0000fffffffffffffffffc000000003fffe00007fffe0000ffffc00001fffffffffe00000000007ffff800001fffffffff,0xa55d4d55428292a854b4a955a09452550c9aaa4d649150a4a90a4aa9495554950949524a4e952569521452452527529244c972527526aa8ad5482aa14554aaaa90aa24aac91524e559292a895569295549429494955254b52525549255254ea4),
  (0x0,0x0),
  (0xffffffffffffffff80000000000000000ffffffffffffffffff00000000000000000000ffffffffffffffffff800000000ffff800007ffffffffffffffffc000000007ffffffff0000000001ffffffffffffffffffff80000000001ffff80000,0x3866718670c8e0c3182030610c211c18470cc38638e19c3831c38330706187063070638384e1c18e1c271c11c1c060e018719c1c21c330e318718c38718700c30430c70c71c638418e0e0c30618e0e187070c707061c1821c1c1871c61c18438),
  (0xfffffffffffffffffffffffffffffffff00000000000000000000000000000000000000fffffffffffffffffffffffffff0000000007fffffffffffffffffffffffff8000000000000000001ffffffffffffffffffffffffffffffe000000000,0xc18986198313030c60c6c18630c6606188100c08410200c0c20c0c01818618184181840c0b0606306058606606058303608020604604c30c618230c18618330c18c3003080184086103030c18630306181831818186060c606061800060608c0),
  (0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000007fffffffffffffffffffffffffffffffffffffffffffe0000000000000000000000000000000000000000,0x1f007e003e003f000f801f800f8007e001f000f8003e000fc000fc001f8001f8001f8000c0007c000600078000600038001c0007800fc007e003f0007e003f000fc003f001f8007e0003f0007c0007e0003e0001f8000f80007e00078000f00),
  (0x0,0x0),
  (0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0xfe01f801fc03fc007f00fe003f007f800fe00ff001fc00ff000ff001fe001fe001fe000ff007f8007f807f8007f803fc00fe007f8007000f8003c001f8003c001f0007c001e000f8003fc001f8003f8001fc001fe0007f0007f8001f8007f000),
  (0x0,0x0)]

def orSymmetries : Array (List Nat) := #[[],[115,84]]

def orCols : IndexTree ColumnInfo := (.fork 3 (.leaf [(0,0,187,0,7),(16386,0,8377,0,6),(16392,0,8371,0,6)]) (.leaf [(16408,0,8355,0,5),(16514,0,8249,0,5),(16544,0,8219,0,5)]))

def orForest : Forest := ⟨8379,7,fun j => orSamples[j]?.getD (0,0),orCols,orSymmetries,liveLevels,liveIndex⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem orGeometry : graphValid orForest (boundsBefore entries8351) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem allAt7 : block orForest 7 0 1 = true := by
  apply wideBlock (depth:=0)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem allAt6 : block orForest 6 0 2 = true := by
  apply wideBlock (depth:=0)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem allAt5 : block orForest 5 0 1 = true := by
  apply wideBlock (depth:=0)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

theorem orTables : checkedTables orForest 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block orForest 0 0 0 = true)
  · exact (rfl : block orForest 1 0 0 = true)
  · exact (rfl : block orForest 2 0 0 = true)
  · exact (rfl : block orForest 3 0 0 = true)
  · exact (rfl : block orForest 4 0 0 = true)
  · exact allAt5
  · exact allAt6
  · exact allAt7

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withoutPositive : Impossible (graphGoal 187) 7 (vars 8379).toFinset := by
  exact root_index (g:=orForest) (before_sound _ sound8351) orGeometry orTables
    (k:=7) (by decide) (i:=0) (by decide +kernel)

end PEqualNP.Outside.L_meta_5006.Negative187
namespace PEqualNP.Outside.L_meta_5006
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem negativeBound187 : Lower (vars 8379) (graphGoal 8379) 8 := by
  apply lower_impossible (proper_of _ (by decide +kernel)) _ Negative187.withoutPositive
  intro a ha
  apply essential_ok (xs:=polarPairs 8379 (graphPairs 187 1342193665)) (by decide +kernel)
  rw [show ((polarPairs 8379 (graphPairs 187 1342193665)).map Prod.fst).toFinset = (vars 8379).toFinset by decide +kernel]
  exact List.mem_toFinset.mpr ha

def entries8379 := extendKnown entries8351 8 [(8379,[]),(8435,[99,65])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound8379 : Known entries8379 := extendKnown_ok sound8351 negativeBound187 (by decide +kernel)
end PEqualNP.Outside.L_meta_5006
namespace PEqualNP.Outside.L_meta_5006.Negative189
open PEqualNP.CircuitLowerBounds

def liveData8 (i : Nat) : Nat := 0x1518cbfa00

def moveIndex8 (i : Nat) : Nat := 0x7cd264c15600000000a1c91d07288b09d5a520bdee767870425

def liveData7 (i : Nat) : Nat := 0x16988610c0210c0628042518e0314082810638146391877d73645a4637281400fe99a00fe58e00fe50e00fe58a00fe54a00fe50a00fe58600fe4c600f68ce00fa88a00fc84600

def moveIndex7 (i : Nat) : Nat := 0x90b0340000972e400244002c12

def liveData6 (i : Nat) : Nat := 0xfa509f0eca1c01e691233803b52ac45007d23384600

def moveIndex6 (i : Nat) : Nat := 0xd

def liveData5 (i : Nat) : Nat := 0x23ea207650e00

def liveLevels : Nat → Packing
  | 8 => (1,1,3,0,0,0,0,liveData8)
  | 7 => (11,2,3,0,0,8,0,liveData7)
  | 6 => (4,3,3,0,0,4,0,liveData6)
  | 5 => (1,4,3,0,0,0,0,liveData5)
  | _ => emptyPacking

def liveIndex : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 6 20 4 9 4 1 moveIndex8
  | 7 => lookupWord 4 10 1 10 2 4 moveIndex7
  | 6 => lookupWord 1 2 0 4 0 0 moveIndex6
  | _ => fun _ => none

def orSamples : Array (Bits × Bits) := #[(0xffff0001ffff00007fffc0007fffc0001fff00007fff80007fff80003ffff00003fff80001fff80001fffe0000ffffffff80001fffe00007fffc0001ffff0000ffffffffffff00007ffffffffffffffffc0000ffff80001ffffffffffffc0000,0x500b4014a016500928069402280594025415500a28152809280d28029402a500a940aa8054a0b28054a054a00a500a941528054a054a015280a90054a01640124034c02aa02aa015500a98054a015280a9402a501528054c02a500aa80a9402a),
  (0x0,0x0),
  (0xfffffffe000000007fffffff800000001fffffff800000007fffffffc000000003fffffffe00000001ffffffff00003ffffffffffffffffffffffffe00000000fffe0000ffffffff80003fffe00007ffffffff000000001ffff00003ffffffff,0x4a20946094404a20253012b02510128814604a302460242025602530128c04a3016302518022025180b18094c04a300c6025180d18094604a302518094409441298128c128c094604a302518094602630128c044602518128c04a302a30128c),
  (0xffffffffffffffff80000000000000001fffffffffffffff800000000000000003fffffffffffffffe0000000000003fffffffe000000007ffffffffffffffff00000000ffffffffffffc000000007ffffffffffffffffe000000003ffffffff,0x610c6218c218610c30841840308618431898610c3098308c3088308418430610c188c30860c4c30860c060c210610c191830860c060c218310c18860c218621804208430c430c218610c10860c218308c184306118308608430610c310c18430),
  (0xffffffffffffffffffffffffffffffffe000000000000000000000000000000003ffffffffffffffffffffffffffffc00000000000000007ffffffffffffffffffffffff0000000000000000000007fffffffffffffffffffffffffc00000000,0x86308c610c6086304318218c4318218c010086304300431043104318218c086302130431810b0431810d810c60863020604318109810c604630231810c608c6098c118c018c00c600630231810c604330218c086604318118c086300230218c0),
  (0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0000000000000000000000000000000000000000000007fffffffffffffffffffffffffffffffffffffffffffff80000000000000000000000000000000000,0x7c00f800f8007c003e001f003e001f001e007c003e003e003e003e001f0007c001c003e000c003e000e000f8007c0018003e000e000f8007c003e000f800f801f001f001f000f8007c003e000f8003c001f00078003e001f0007c003c001f00),
  (0x0,0x0),
  (0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff800000000000000000000000000000000000000000000000000000000000000000000000000000000,0xf800f001f000f8007c003e007c003e001e00f8007c007c007c007c003e000f8003e007c001f007c001f001f000f8003e007c001f001f00078003c001f000f000e001e000e000f00078003c001f0007c003e000f8007c001e000f8003c003e000),
  (0x0,0x0)]

def orSymmetries : Array (List Nat) := #[[],[115,84],[32,67,117],[32,83,116],[48,82],[48,82,112,66],[64,114,50,48,80],[64,114,83],[80,50,116],[80,50,66,32,114],[112,66,48,82],[112,66]]

def orCols : IndexTree ColumnInfo := (.fork 3 (.leaf [(0,0,189,0,8),(1,0,188,0,5),(17,0,172,0,4)]) (.leaf [(16396,0,8369,0,5),(16408,0,8357,0,5),(16516,0,8249,0,5),(16544,0,8221,0,5)]))

def orForest : Forest := ⟨8381,8,fun j => orSamples[j]?.getD (0,0),orCols,orSymmetries,liveLevels,liveIndex⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem orGeometry : graphValid orForest (boundsBefore entries8379) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem allAt8 : block orForest 8 0 1 = true := by
  apply wideBlock (depth:=0)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem allAt7 : block orForest 7 0 11 = true := by
  apply wideBlock (depth:=2)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem allAt6 : block orForest 6 0 4 = true := by
  apply wideBlock (depth:=0)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem allAt5 : block orForest 5 0 1 = true := by
  apply wideBlock (depth:=0)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

theorem orTables : checkedTables orForest 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block orForest 0 0 0 = true)
  · exact (rfl : block orForest 1 0 0 = true)
  · exact (rfl : block orForest 2 0 0 = true)
  · exact (rfl : block orForest 3 0 0 = true)
  · exact (rfl : block orForest 4 0 0 = true)
  · exact allAt5
  · exact allAt6
  · exact allAt7
  · exact allAt8

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withoutPositive : Impossible (graphGoal 189) 8 (vars 8381).toFinset := by
  exact root_index (g:=orForest) (before_sound _ sound8379) orGeometry orTables
    (k:=8) (by decide) (i:=0) (by decide +kernel)

end PEqualNP.Outside.L_meta_5006.Negative189
namespace PEqualNP.Outside.L_meta_5006
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem negativeBound189 : Lower (vars 8381) (graphGoal 8381) 9 := by
  apply lower_impossible (proper_of _ (by decide +kernel)) _ Negative189.withoutPositive
  intro a ha
  apply essential_ok (xs:=polarPairs 8381 (graphPairs 189 536879876)) (by decide +kernel)
  rw [show ((polarPairs 8381 (graphPairs 189 536879876)).map Prod.fst).toFinset = (vars 8381).toFinset by decide +kernel]
  exact List.mem_toFinset.mpr ha

def entries8381 := extendKnown entries8379 9 [(8381,[]),(8539,[130,50,98,82,115,33,65])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound8381 : Known entries8381 := extendKnown_ok sound8379 negativeBound189 (by decide +kernel)
end PEqualNP.Outside.L_meta_5006
namespace PEqualNP.Outside.L_meta_5006.Negative207
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withoutPositive : Impossible (graphGoal 207) 6 (vars 8399).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=8399) (16448,0,8335,0,6) _ (before_sound _ sound8381) (by decide +kernel))
    [] (pool:=(vars (poolMask 8399 (16448,0,8335,0,6)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end PEqualNP.Outside.L_meta_5006.Negative207
namespace PEqualNP.Outside.L_meta_5006
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem negativeBound207 : Lower (vars 8399) (graphGoal 8399) 7 := by
  apply lower_impossible (proper_of _ (by decide +kernel)) _ Negative207.withoutPositive
  intro a ha
  apply essential_ok (xs:=polarPairs 8399 (graphPairs 207 553656577)) (by decide +kernel)
  rw [show ((polarPairs 8399 (graphPairs 207 553656577)).map Prod.fst).toFinset = (vars 8399).toFinset by decide +kernel]
  exact List.mem_toFinset.mpr ha

def entries8399 := extendKnown entries8381 7 [(8399,[])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound8399 : Known entries8399 := extendKnown_ok sound8381 negativeBound207 (by decide +kernel)
end PEqualNP.Outside.L_meta_5006
namespace PEqualNP.Outside.L_meta_5006.Negative215
open PEqualNP.CircuitLowerBounds

def liveData7 (i : Nat) : Nat := 0x8d09fa00

def moveIndex7 (i : Nat) : Nat := 0x3bf0000016b80b620003

def liveData6 (i : Nat) : Nat := 0x4302081008820b5e64f140f658e00ee50a00fa88a00de54600f64c600fc84600

def moveIndex6 (i : Nat) : Nat := 0x1

def liveData5 (i : Nat) : Nat := 0x300d687254600

def liveLevels : Nat → Packing
  | 7 => (1,1,3,0,0,0,0,liveData7)
  | 6 => (6,2,3,0,0,6,0,liveData6)
  | 5 => (1,3,3,0,0,0,0,liveData5)
  | _ => emptyPacking

def liveIndex : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 5 10 2 7 3 0 moveIndex7
  | 6 => lookupWord 1 2 0 4 0 0 moveIndex6
  | _ => fun _ => none

def orSamples : Array (Bits × Bits) := #[(0xfffe0000ffffc00003fffe0000ffffffff00000ffffc00007fffe00001fffc0001ffff800003ffffffffffff800007ffff800001ffffffff0000fffffffff800007ffffffff00000ffffc00000ffff80001ffffffffffffffffffc00001fffff,0x425280804451508a1108c284004231225942288445291144212948450489141010888521104908121184a14921209212892114248589250902084942909452028124509529240a1244a4908a12128900825250a4462484509494490942488a12),
  (0xffffffff0000000003ffffffff00007ffffffff0000000007ffffffffffffffffe0000000003fff800003ffffffff80000000001ffffffffffff00003fffffffff800007ffffffffffffffffffffffffffe0000ffffe000007ffffffffffffff,0x1404280910000500405014280a14000c02140120800020010a028280485040a04450100a011050a0a0110a120a0220a0020a00882822002250220008050120a012000220004180441809050044a0222808880202808828022300905008850044),
  (0xfffffffffffffffffc0000000000007fffffffffffffffff8000000001fffffffffffffffffc000000003ffffffffffffffffffe00007fffffffffffc000000000000007ffffffff0000000000fffffffffffff00000000007ffffffffe00000,0x16a02d20165802c980280015000a400ec00b2c01670059600310016100398059802e6005a6001000526006c0074c0072c005930010c164c0b4c05930058400b240164c0b3802c9802c6002c980b4c02d30164c015300164c039600393002c98),
  (0x0,0x0),
  (0xffffffffffffffffffffffffffffff8000000000000000000000000001ffffffffffffffffffffffffffc000000000000000000000007ffffffffffffffffffffffffff8000000000000000000fffffffffffffffffffffff800000000000000,0x998d331c99862630e26319319c98c6488098c309184246184c4213186162e2c6e163384c638263c4c6380c304c4704c4304c61c130305870ec70961c266184cc38498700c20930e093082630e0cc70731c0d870b19c13187022182621c1630e0),
  (0x0,0x0),
  (0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffe000000000000000000000000000000000000000000000000007fffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000,0xe1f1c3e0e1f8383f0383e1c1e0e0f870f0e0fc0e1f8387e0707c1c1f818303070183c0707c03820707c0304070780707c0707e01c1c07f808f80e7e0387e070fc071f806fc0e3f00e3f0383f000f8043e011f80c1e01c1f8043e0383e0183f00),
  (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff800000000000000000000000000000000000000000000000000000000000000000000000000000000000,0xfe01fc00fe003fc003fc01fe00ff007f00ff000fe003f8007f801fe001fc03f801fc007f8003fc07f8003f807f8007f8007f8001fe006000f000f8003f8007f0007e0007000fc000fc003fc000f0007c001e000fe001fe0007c003fc001fc000),
  (0x0,0x0)]

def orSymmetries : Array (List Nat) := #[[],[32,116]]

def orCols : IndexTree ColumnInfo := (.fork 2 (.leaf [(0,0,215,0,7),(1,0,198,0,4)]) (.leaf [(1,16,198,0,4),(16464,0,8327,0,5),(16576,0,8215,0,5)]))

def orForest : Forest := ⟨8407,7,fun j => orSamples[j]?.getD (0,0),orCols,orSymmetries,liveLevels,liveIndex⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem orGeometry : graphValid orForest (boundsBefore entries8399) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem allAt7 : block orForest 7 0 1 = true := by
  apply wideBlock (depth:=0)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem allAt6 : block orForest 6 0 6 = true := by
  apply wideBlock (depth:=1)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem allAt5 : block orForest 5 0 1 = true := by
  apply wideBlock (depth:=0)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

theorem orTables : checkedTables orForest 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block orForest 0 0 0 = true)
  · exact (rfl : block orForest 1 0 0 = true)
  · exact (rfl : block orForest 2 0 0 = true)
  · exact (rfl : block orForest 3 0 0 = true)
  · exact (rfl : block orForest 4 0 0 = true)
  · exact allAt5
  · exact allAt6
  · exact allAt7

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withoutPositive : Impossible (graphGoal 215) 7 (vars 8407).toFinset := by
  exact root_index (g:=orForest) (before_sound _ sound8399) orGeometry orTables
    (k:=7) (by decide) (i:=0) (by decide +kernel)

end PEqualNP.Outside.L_meta_5006.Negative215
namespace PEqualNP.Outside.L_meta_5006
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem negativeBound215 : Lower (vars 8407) (graphGoal 8407) 8 := by
  apply lower_impossible (proper_of _ (by decide +kernel)) _ Negative215.withoutPositive
  intro a ha
  apply essential_ok (xs:=polarPairs 8407 (graphPairs 215 553648385)) (by decide +kernel)
  rw [show ((polarPairs 8407 (graphPairs 215 553648385)).map Prod.fst).toFinset = (vars 8407).toFinset by decide +kernel]
  exact List.mem_toFinset.mpr ha

def entries8407 := extendKnown entries8399 8 [(8407,[]),(8629,[134,81,114,49]),(8689,[118,33,129,82,49])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound8407 : Known entries8407 := extendKnown_ok sound8399 negativeBound215 (by decide +kernel)
end PEqualNP.Outside.L_meta_5006
namespace PEqualNP.Outside.L_meta_5006.Negative349
open PEqualNP.CircuitLowerBounds

def liveData7 (i : Nat) : Nat := 0x5149fa00

def moveIndex7 (i : Nat) : Nat := 0x41065006a00820

def liveData6 (i : Nat) : Nat := 0x10804100c3ecbd40be18e00f68ce00be58a00fa88a00fc4c600

def liveLevels : Nat → Packing
  | 7 => (1,1,3,0,0,0,0,liveData7)
  | 6 => (5,2,3,0,0,5,0,liveData6)
  | _ => emptyPacking

def liveIndex : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 3 8 2 7 3 0 moveIndex7
  | _ => fun _ => none

def orSamples : Array (Bits × Bits) := #[(0xfffc000fffc0001ffff80001ffffe00003fffc0000ffff00001ffffe00000fffff800001fffe0000fffc0001fffffffffffff00000ffff800001fffc0000ffff00003fffffffffffffe00001ffffe00001ffffc00001ffffffffffffffc00000,0x2aac8406594448851a2942885151c515014aa8854a655628aa4515345150a28a95145454532a501429a8a024514d28c54556a2942a2ad5145454952c1514151605448a5469151552a548545452a5442854458a8a2c5451a3462a2a554a8a2a2a),
  (0x0,0x0),
  (0xfffffff00000001ffffffffe0000000003ffffffff000000001ffffffffff00000000001ffffffff00000001ffff00001fffffffff0000000001ffffffff000000003ffffc00007ffffffffffffffffffe0000000001ffffe00000ffffffffff,0xb4d6d145102912164cb5932d646496464b930ed1934184b2309646596464cb2306591919658d64c6b002c88965a6b2119618cb268cb086591919c64ac646464491912d1930464668c99d191968d1968d1911232c891964c9948c8ce9a32c8c8c),
  (0xffffffffffffffe0000000000000000003ffffffffffffffffe000000000000000000001fffffffffffffffe000000001fffffffffffffffffffffffffffffffffffc0000000007ffffffffffffffffffffffffffffe0000000000ffffffffff,0x3080610618060c01000040001810018100c30060c061800c30018200181000c18006060023001180130023000080086006300183003180060601830181818180606006040181803060060600306003060060c0030600102003030060c003030),
  (0xfffffffffffffffffffffffffffffffffc00000000000000000000000000000000000001ffffffffffffffffffffffffe0000000000000000001ffffffffffffffffffffffffff8000000001ffffffffffffffffffffffffffffff0000000000,0xc41318698231831860c618318606186062100318108800c30018604186060c302061818184c18660c2430cc18630c31818000c20c0c02061818160436060e060d81831818260600c081181818c1818c181983030c181860c18c0c0883030c0c0),
  (0x0,0x0),
  (0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe00000000000000000000000000000000000000000001fffffffffffffffffffffffffffffffffffe0000000000000000000000000000000000000000,0x7e01f81fc01fc007f001fc007f8007f801fc01fe00fe003fc007f8007f8003fc001fe000700078003800f0007c003e0007c003f0003c001fe007f807f807f801fe001fe007f800ff001fe000fe000fe001fc000fe0007f000ff000fc000ff00),
  (0x0,0x0),
  (0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0000000000000000000000000000000000000000000000000000000000000000000000000000,0xf803e00e003e001f8007e001f8001f8003e003e000f000fc001f8001f8000fc0007e0001f801f800fc03f001f800fc001f800fc000fc007e0001800380008000e0003e0003800070001e0001f0001f0001e0003f0001f8001f0000f0003f0000)]

def orSymmetries : Array (List Nat) := #[[],[96,132]]

def orCols : IndexTree ColumnInfo := (.fork 3 (.leaf [(0,0,349,0,7),(0,1,332,16,5),(1,0,348,0,5)]) (.leaf [(16,1,332,0,4),(16388,0,8537,0,6),(16640,64,8221,0,5)]))

def orForest : Forest := ⟨8541,7,fun j => orSamples[j]?.getD (0,0),orCols,orSymmetries,liveLevels,liveIndex⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem orGeometry : graphValid orForest (boundsBefore entries8407) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem allAt7 : block orForest 7 0 1 = true := by
  apply wideBlock (depth:=0)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem allAt6 : block orForest 6 0 5 = true := by
  apply wideBlock (depth:=1)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

theorem orTables : checkedTables orForest 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block orForest 0 0 0 = true)
  · exact (rfl : block orForest 1 0 0 = true)
  · exact (rfl : block orForest 2 0 0 = true)
  · exact (rfl : block orForest 3 0 0 = true)
  · exact (rfl : block orForest 4 0 0 = true)
  · exact (rfl : block orForest 5 0 0 = true)
  · exact allAt6
  · exact allAt7

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withoutPositive : Impossible (graphGoal 349) 7 (vars 8541).toFinset := by
  exact root_index (g:=orForest) (before_sound _ sound8407) orGeometry orTables
    (k:=7) (by decide) (i:=0) (by decide +kernel)

end PEqualNP.Outside.L_meta_5006.Negative349
namespace PEqualNP.Outside.L_meta_5006
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem negativeBound349 : Lower (vars 8541) (graphGoal 8541) 8 := by
  apply lower_impossible (proper_of _ (by decide +kernel)) _ Negative349.withoutPositive
  intro a ha
  apply essential_ok (xs:=polarPairs 8541 (graphPairs 349 13019128580)) (by decide +kernel)
  rw [show ((polarPairs 8541 (graphPairs 349 13019128580)).map Prod.fst).toFinset = (vars 8541).toFinset by decide +kernel]
  exact List.mem_toFinset.mpr ha

def entries8541 := extendKnown entries8407 8 [(8541,[]),(8557,[84,131,98]),(8605,[118,130])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound8541 : Known entries8541 := extendKnown_ok sound8407 negativeBound349 (by decide +kernel)
end PEqualNP.Outside.L_meta_5006
namespace PEqualNP.Outside.L_meta_5006.Negative429
open PEqualNP.CircuitLowerBounds

def liveData8 (i : Nat) : Nat := 0x11447fa00

def moveIndex8 (i : Nat) : Nat := 0x2f3837de9385cad41dda741000000000e2d43cc47d58a4d800100118000100011

def liveData7 (i : Nat) : Nat := 0x110c4310c4a28862410831088248880188621877d73645a4b41372d1e140a00fe55200fe50e00fe8ce00fe54600fe50600fe4c600fe0c600fe48600fe84600ee91200be18e00f68ce00fc84600

def moveIndex7 (i : Nat) : Nat := 0x16851bdc01864cc295705126c5191aa9484018761302533457251a0

def liveData6 (i : Nat) : Nat := 0xc2000010000080000027437ce57294864a0f1414073a55912009f4ee31c013e5d0638035d220c7004f87650e00f348919c01b618e338027c3b263007725584600f648908c01bc18e11803e919c23007e22284600

def moveIndex6 (i : Nat) : Nat := 0x4

def liveData5 (i : Nat) : Nat := 0x23ea217418e00

def liveLevels : Nat → Packing
  | 8 => (1,1,3,0,0,0,0,liveData8)
  | 7 => (13,2,3,0,0,8,0,liveData7)
  | 6 => (13,3,3,0,0,7,0,liveData6)
  | 5 => (1,4,3,0,0,0,0,liveData5)
  | _ => emptyPacking

def liveIndex : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 15 29 4 9 4 1 moveIndex8
  | 7 => lookupWord 7 22 4 9 4 1 moveIndex7
  | 6 => lookupWord 1 2 0 4 0 0 moveIndex6
  | _ => fun _ => none

def orSamples : Array (Bits × Bits) := #[(0xfffc000ffff0000fffe0003ffff00003fffc00007fff80001ffff00003fff80003ffff00007fff80007fffe00003ffff80000ffffc00007fff0001fffc0007fffe0000ffffc00007fffe00007fffe00003fff80003fffffffffffffffff80000,0xad1e940b50b9508aa8b5212aa1aaa82aaa56aa15554b55455551aaa82b50ad40aaaa2aaa09558d550555855550aaaa155542aaa8aaaa157a151429685a509554354a0ab50aaaa15554554a1555455550aad15550aba855ac2aaa855aa155542a),
  (0x0,0x0),
  (0xfffffff00000000fffffffc000000003ffffffff800000001ffffffffffffffffc000000007fffffff8000000003fffffffff0000000007ffffffe00000007ffffffff0000000007fffffffffffffffffffffffffc0001ffff00001fffffffff,0x3048c0920222022302c6058c04c30130c018c046180218018604c3013182318230c08c3022182618261811860230c0461808c30030c0462046408c011002218098604c20230c0461809860461811860233046602310118c08c30118c0461808c),
  (0xfffffffffffffff00000000000000003ffffffffffffffffe000000003ffffffffffffffff800000000000000003fffffffffffffffffffffffffffffffff8000000000000000007ffffffff8000000003fffffffffffe000000001fffffffff,0x690192064c064c030004800c90032400ce00c98019c019600610032401cc014c00d30034c0148004801260064c00c9801930032c00c980c981930326064c019200c90064c00c98019600c9801860064c0698064c032600930032600c9801930),
  (0x0,0x0),
  (0xfffffffffffffffffffffffffffffffc00000000000000000000000003fffffffffffffffffffffffffffffffffc0000000000000000007ffffffffffffffffffffffffffffffff8000000000000000003ffffffffffffffffffffe000000000,0xe001c00700070003000e000e000380008000e00010001800060003800700070001c0007000700070003800070000e0001c00030000e000e001c00380070001c000e00070000e00018000e000180007000e000700038001c00038000e0001c0),
  (0x0,0x0),
  (0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffc00000000000000000000000000000000000000000000000000007ffffffffffffffffffffffffffffffffffffffffffffffffffc000000000000000000000000000000,0xc7031e0c780c780c3c187030f00c3c030f030f0061e061e018780c3c02180618030e00c3806180618061c01878030f0061e00c3c030f004f009e01bc0378061e018f00c78030f0061e018f0061e0187800700078023c010e00c3c010f0061e00),
  (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000000000000000000000000000000000000000000000000000000000000000000000000000000000,0xf803e00f800f800fc01f803f000fc003f003f0007e007e001f800fc003e007e003f000fc007e007e007e001f8003f0007e000fc003f0007000e001c0038007e001f000f8003f0007e001f0007e001f800380078003c001f000fc001f0007e000)]

def orSymmetries : Array (List Nat) := #[[],[50,135]]

def orCols : IndexTree ColumnInfo := (.fork 3 (.leaf [(0,1,396,32,5),(1,0,428,0,7),(5,0,424,0,4)]) (.leaf [(32,0,396,0,4),(16512,0,8493,0,6),(16648,0,8357,0,5)]))

def orForest : Forest := ⟨8621,8,fun j => orSamples[j]?.getD (0,0),orCols,orSymmetries,liveLevels,liveIndex⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem orGeometry : graphValid orForest (boundsBefore entries8541) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem allAt8 : block orForest 8 0 1 = true := by
  apply wideBlock (depth:=0)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem allAt7 : block orForest 7 0 13 = true := by
  apply wideBlock (depth:=2)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem allAt6 : block orForest 6 0 13 = true := by
  apply wideBlock (depth:=2)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem allAt5 : block orForest 5 0 1 = true := by
  apply wideBlock (depth:=0)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

theorem orTables : checkedTables orForest 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block orForest 0 0 0 = true)
  · exact (rfl : block orForest 1 0 0 = true)
  · exact (rfl : block orForest 2 0 0 = true)
  · exact (rfl : block orForest 3 0 0 = true)
  · exact (rfl : block orForest 4 0 0 = true)
  · exact allAt5
  · exact allAt6
  · exact allAt7
  · exact allAt8

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withoutPositive : Impossible (graphGoal 429) 8 (vars 8621).toFinset := by
  exact root_index (g:=orForest) (before_sound _ sound8541) orGeometry orTables
    (k:=8) (by decide) (i:=0) (by decide +kernel)

end PEqualNP.Outside.L_meta_5006.Negative429
namespace PEqualNP.Outside.L_meta_5006
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem negativeBound429 : Lower (vars 8621) (graphGoal 8621) 9 := by
  apply lower_impossible (proper_of _ (by decide +kernel)) _ Negative429.withoutPositive
  intro a ha
  apply essential_ok (xs:=polarPairs 8621 (graphPairs 429 13421781765)) (by decide +kernel)
  rw [show ((polarPairs 8621 (graphPairs 429 13421781765)).map Prod.fst).toFinset = (vars 8621).toFinset by decide +kernel]
  exact List.mem_toFinset.mpr ha

def entries8621 := extendKnown entries8541 9 [(8621,[])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound8621 : Known entries8621 := extendKnown_ok sound8541 negativeBound429 (by decide +kernel)
end PEqualNP.Outside.L_meta_5006
namespace PEqualNP.Outside.L_meta_5006.Negative455
open PEqualNP.CircuitLowerBounds

def liveData7 (i : Nat) : Nat := 0x14c9fa00

def moveIndex7 (i : Nat) : Nat := 0x6c0000000c62080288000000040

def liveData6 (i : Nat) : Nat := 0x4200404189b8a0be58a00fa88a00be18600ee50600fc84600

def moveIndex6 (i : Nat) : Nat := 0xf0000e

def liveData5 (i : Nat) : Nat := 0xc06827d3b8c3005a87250600

def liveLevels : Nat → Packing
  | 7 => (1,1,2,0,0,0,0,liveData7)
  | 6 => (5,2,2,0,0,5,0,liveData6)
  | 5 => (2,3,2,0,0,4,0,liveData5)
  | _ => emptyPacking

def liveIndex : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 11 16 1 7 3 0 moveIndex7
  | 6 => lookupWord 2 5 0 5 1 0 moveIndex6
  | _ => fun _ => none

def orSamples : Array (Bits × Bits) := #[(0xfff8000ffffc00003fffc0001ffffc0000ffff0000fffff000007fffffffe0003ffff00000ffffc00007ffffc00000ffffc0001ffffffff80003ffff00001ffff80001ffff80001fffff000007ffffffff80001ffff800001ffffc00000fffff,0x527a910555554a55154a51490a55594a48535952205295a52949294b4cb52495295aa52952553a948512955494a552526c94890a5549cac84aa2b2aa52550995522544a65902524aa552552a92a9694da9222a4d9a9294aa4cd5494a55265552),
  (0xfffffff0000000003fffffffe000000000ffffffff00000000007fffffffffffc000000000fffffffff80000000000fffffffffffffffffffffc000000001fffffffffffffffffe00000000007ffffffffffffffffffffffffffffffffffffff,0x84842418000210802210a210508002108284828442842008420242109100510042000840048841211024200121080484812120508812101490080400808052202488090882488090080480402442021002488092202421009120121080488804),
  (0xffffffffffffffffc00000000000000000ffffffffffffffffff80001fffffffffffffffff00000000000000000000ffffffffe00003ffffffffffffffffe000000001fffffffffffffffffff800007fffffffe0000000001ffffffffff00000,0x1828c1a181986019840004020301906010181c180c1806c1806c0c01061986198c0cc181981012060640c0660601981836060d83006083610330c0cc18198006400190301c101b030198180cc0804c60cc3033040cc0c0330606606019830198),
  (0x0,0x0),
  (0x0,0x0),
  (0x0,0x0),
  (0xffffffffffffffffffffffffffffffffff00000000000000000000001fffffffffffffffffffffffffffffffffffff00000000000003fffffffffffffffffffffffffe0000000000000000000000007fffffffffffffffffe000000000000000,0x33019c019e0031e006300638019e0031c0110008800c7000c700062003e003e006f000de0019c00278006780031e00038000e001180638063c018f0031e00c78031e00310031c0031e0018f000c7006f0033c00cf00063c004780031e0011e0),
  (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffe000000000000000000000000000000000000000000000000003ffffffffffffffffffffffffffffffffffffffffffffffffff8000000000000000000000000000000000,0xe3c71e0e1e0383e0387c387c1c1e0383e0e1e0e0f0e0f80e0f80707c1820182030700e0e00e1e03838070780383e00e0c038301c1e037c067c031f00e3e01cf8073e01c3e063e01c3e00e1f0070f80070043c018f00707c018780383e00c1e00),
  (0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0xfc07e00fe003fc003f803f801fe003fc00fe00ff00ff000ff0007f801fc01fc03f800ff000fe003fc007f8003fc000ff003fc01fe00380078003e000fc001f0007c001fc007c001fc000fe0007f00078007c001f0007f8001f8003fc000fe000)]

def orSymmetries : Array (List Nat) := #[[],[98,135]]

def orCols : IndexTree ColumnInfo := (.leaf [(0,0,455,0,7),(1,0,454,0,5),(16512,0,8519,0,6),(16448,256,8327,0,5)])

def orForest : Forest := ⟨8647,7,fun j => orSamples[j]?.getD (0,0),orCols,orSymmetries,liveLevels,liveIndex⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem orGeometry : graphValid orForest (boundsBefore entries8621) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem allAt7 : block orForest 7 0 1 = true := by
  apply wideBlock (depth:=0)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem allAt6 : block orForest 6 0 5 = true := by
  apply wideBlock (depth:=1)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem allAt5 : block orForest 5 0 2 = true := by
  apply wideBlock (depth:=0)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

theorem orTables : checkedTables orForest 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block orForest 0 0 0 = true)
  · exact (rfl : block orForest 1 0 0 = true)
  · exact (rfl : block orForest 2 0 0 = true)
  · exact (rfl : block orForest 3 0 0 = true)
  · exact (rfl : block orForest 4 0 0 = true)
  · exact allAt5
  · exact allAt6
  · exact allAt7

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withoutPositive : Impossible (graphGoal 455) 7 (vars 8647).toFinset := by
  exact root_index (g:=orForest) (before_sound _ sound8621) orGeometry orTables
    (k:=7) (by decide) (i:=0) (by decide +kernel)

end PEqualNP.Outside.L_meta_5006.Negative455
namespace PEqualNP.Outside.L_meta_5006
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem negativeBound455 : Lower (vars 8647) (graphGoal 8647) 8 := by
  apply lower_impossible (proper_of _ (by decide +kernel)) _ Negative455.withoutPositive
  intro a ha
  apply essential_ok (xs:=polarPairs 8647 (graphPairs 455 26323452161)) (by decide +kernel)
  rw [show ((polarPairs 8647 (graphPairs 455 26323452161)).map Prod.fst).toFinset = (vars 8647).toFinset by decide +kernel]
  exact List.mem_toFinset.mpr ha

def entries8647 := extendKnown entries8621 8 [(8647,[])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound8647 : Known entries8647 := extendKnown_ok sound8621 negativeBound455 (by decide +kernel)
end PEqualNP.Outside.L_meta_5006
namespace PEqualNP.Outside.L_meta_5006.Negative127
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withoutPositive : Impossible (graphGoal 127) 9 (vars 8319).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=8319) (16416,0,8287,0,9) _ (before_sound _ sound8647) (by decide +kernel))
    [] (pool:=(vars (poolMask 8319 (16416,0,8287,0,9)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end PEqualNP.Outside.L_meta_5006.Negative127
namespace PEqualNP.Outside.L_meta_5006
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem negativeBound127 : Lower (vars 8319) (graphGoal 8319) 10 := by
  apply lower_impossible (proper_of _ (by decide +kernel)) _ Negative127.withoutPositive
  intro a ha
  apply essential_ok (xs:=polarPairs 8319 (graphPairs 127 16785665)) (by decide +kernel)
  rw [show ((polarPairs 8319 (graphPairs 127 16785665)).map Prod.fst).toFinset = (vars 8319).toFinset by decide +kernel]
  exact List.mem_toFinset.mpr ha

def entries8319 := extendKnown entries8647 10 [(8319,[]),(8439,[84,115]),(8567,[131,84,115,98]),(8691,[98,99,81,131,114,65])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound8319 : Known entries8319 := extendKnown_ok sound8647 negativeBound127 (by decide +kernel)
end PEqualNP.Outside.L_meta_5006
namespace PEqualNP.Outside.L_meta_5006.Negative223
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withoutPositive : Impossible (graphGoal 223) 9 (vars 8415).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=8415) (16448,0,8351,0,9) _ (before_sound _ sound8319) (by decide +kernel))
    [] (pool:=(vars (poolMask 8415 (16448,0,8351,0,9)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end PEqualNP.Outside.L_meta_5006.Negative223
namespace PEqualNP.Outside.L_meta_5006
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem negativeBound223 : Lower (vars 8415) (graphGoal 8415) 10 := by
  apply lower_impossible (proper_of _ (by decide +kernel)) _ Negative223.withoutPositive
  intro a ha
  apply essential_ok (xs:=polarPairs 8415 (graphPairs 223 553656577)) (by decide +kernel)
  rw [show ((polarPairs 8415 (graphPairs 223 553656577)).map Prod.fst).toFinset = (vars 8415).toFinset by decide +kernel]
  exact List.mem_toFinset.mpr ha

def entries8415 := extendKnown entries8319 10 [(8415,[]),(8697,[118,130,81])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound8415 : Known entries8415 := extendKnown_ok sound8319 negativeBound223 (by decide +kernel)
end PEqualNP.Outside.L_meta_5006
namespace PEqualNP.Outside.L_meta_5006.Negative251
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withoutPositive : Impossible (graphGoal 251) 8 (vars 8443).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=8443) (16392,0,8435,0,8) _ (before_sound _ sound8415) (by decide +kernel))
    [] (pool:=(vars (poolMask 8443 (16392,0,8435,0,8)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end PEqualNP.Outside.L_meta_5006.Negative251
namespace PEqualNP.Outside.L_meta_5006
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem negativeBound251 : Lower (vars 8443) (graphGoal 8443) 9 := by
  apply lower_impossible (proper_of _ (by decide +kernel)) _ Negative251.withoutPositive
  intro a ha
  apply essential_ok (xs:=polarPairs 8443 (graphPairs 251 1358970881)) (by decide +kernel)
  rw [show ((polarPairs 8443 (graphPairs 251 1358970881)).map Prod.fst).toFinset = (vars 8443).toFinset by decide +kernel]
  exact List.mem_toFinset.mpr ha

def entries8443 := extendKnown entries8415 9 [(8443,[])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound8443 : Known entries8443 := extendKnown_ok sound8415 negativeBound251 (by decide +kernel)
end PEqualNP.Outside.L_meta_5006
namespace PEqualNP.Outside.L_meta_5006.Negative381
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withoutPositive : Impossible (graphGoal 381) 9 (vars 8573).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=8573) (16388,0,8569,0,9) _ (before_sound _ sound8443) (by decide +kernel))
    [] (pool:=(vars (poolMask 8573 (16388,0,8569,0,9)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end PEqualNP.Outside.L_meta_5006.Negative381
namespace PEqualNP.Outside.L_meta_5006
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem negativeBound381 : Lower (vars 8573) (graphGoal 8573) 10 := by
  apply lower_impossible (proper_of _ (by decide +kernel)) _ Negative381.withoutPositive
  intro a ha
  apply essential_ok (xs:=polarPairs 8573 (graphPairs 381 13019128580)) (by decide +kernel)
  rw [show ((polarPairs 8573 (graphPairs 381 13019128580)).map Prod.fst).toFinset = (vars 8573).toFinset by decide +kernel]
  exact List.mem_toFinset.mpr ha

def entries8573 := extendKnown entries8443 10 [(8573,[])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound8573 : Known entries8573 := extendKnown_ok sound8443 negativeBound381 (by decide +kernel)
end PEqualNP.Outside.L_meta_5006
namespace PEqualNP.Outside.L_meta_5006.Negative471
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withoutPositive : Impossible (graphGoal 471) 8 (vars 8663).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=8663) (16400,0,8647,0,8) _ (before_sound _ sound8573) (by decide +kernel))
    [] (pool:=(vars (poolMask 8663 (16400,0,8647,0,8)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end PEqualNP.Outside.L_meta_5006.Negative471
namespace PEqualNP.Outside.L_meta_5006
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem negativeBound471 : Lower (vars 8663) (graphGoal 8663) 9 := by
  apply lower_impossible (proper_of _ (by decide +kernel)) _ Negative471.withoutPositive
  intro a ha
  apply essential_ok (xs:=polarPairs 8663 (graphPairs 471 26323452161)) (by decide +kernel)
  rw [show ((polarPairs 8663 (graphPairs 471 26323452161)).map Prod.fst).toFinset = (vars 8663).toFinset by decide +kernel]
  exact List.mem_toFinset.mpr ha

def entries8663 := extendKnown entries8573 9 [(8663,[]),(8693,[134,81,114,49])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound8663 : Known entries8663 := extendKnown_ok sound8573 negativeBound471 (by decide +kernel)
end PEqualNP.Outside.L_meta_5006
namespace PEqualNP.Outside.L_meta_5006.Negative493
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withoutPositive : Impossible (graphGoal 493) 9 (vars 8685).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=8685) (16448,0,8621,0,9) _ (before_sound _ sound8663) (by decide +kernel))
    [] (pool:=(vars (poolMask 8685 (16448,0,8621,0,9)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end PEqualNP.Outside.L_meta_5006.Negative493
namespace PEqualNP.Outside.L_meta_5006
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem negativeBound493 : Lower (vars 8685) (graphGoal 8685) 10 := by
  apply lower_impossible (proper_of _ (by decide +kernel)) _ Negative493.withoutPositive
  intro a ha
  apply essential_ok (xs:=polarPairs 8685 (graphPairs 493 13555999493)) (by decide +kernel)
  rw [show ((polarPairs 8685 (graphPairs 493 13555999493)).map Prod.fst).toFinset = (vars 8685).toFinset by decide +kernel]
  exact List.mem_toFinset.mpr ha

def entries8685 := extendKnown entries8663 10 [(8685,[])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound8685 : Known entries8685 := extendKnown_ok sound8663 negativeBound493 (by decide +kernel)
end PEqualNP.Outside.L_meta_5006
namespace PEqualNP.Outside.L_meta_5006.Signed15
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withoutPositive : Impossible (graphGoal 15) 3 (minusZero 15).toFinset := orderCut 3 2 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withPositive : Impossible (graphGoal 15) 3 (vars 2063).toFinset := countImpossible (by decide +kernel)

end PEqualNP.Outside.L_meta_5006.Signed15
namespace PEqualNP.Outside.L_meta_5006
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem signedBound15 : Lower (vars 2063) (graphGoal 2063) 4 :=
  signedInduced (m:=15) (k:=3) (hints:=8449) (before_sound _ valid383 15)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) Signed15.withoutPositive Signed15.withPositive

def entries2063 := extendKnown entries8685 4 [(2063,[]),(2077,[50,65]),(2183,[115,99,83,67]),(2213,[114,33,97,82,50,65]),(2329,[131,115,99,50,82,65]),(2401,[130,33,113,99,82,65])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound2063 : Known entries2063 := extendKnown_ok sound8685 signedBound15 (by decide +kernel)
end PEqualNP.Outside.L_meta_5006
namespace PEqualNP.Outside.L_meta_5006.Signed23
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withoutPositive : Impossible (graphGoal 23) 3 (minusZero 23).toFinset := orderCut 3 2 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withPositive : Impossible (graphGoal 23) 3 (vars 2071).toFinset := countImpossible (by decide +kernel)

end PEqualNP.Outside.L_meta_5006.Signed23
namespace PEqualNP.Outside.L_meta_5006
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem signedBound23 : Lower (vars 2071) (graphGoal 2071) 4 :=
  signedInduced (m:=23) (k:=3) (hints:=257) (before_sound _ valid383 23)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) Signed23.withoutPositive Signed23.withPositive

def entries2071 := extendKnown entries2063 4 [(2071,[]),(2075,[50,65]),(2087,[84]),(2105,[65,33,82,49]),(2147,[66,100,82,50]),(2211,[114,33,97,82,50,65]),(2225,[114,33,97,82,49])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound2071 : Known entries2071 := extendKnown_ok sound2063 signedBound23 (by decide +kernel)
end PEqualNP.Outside.L_meta_5006
namespace PEqualNP.Outside.L_meta_5006.Signed31
open PEqualNP.CircuitLowerBounds

def liveData6 (i : Nat) : Nat := 0xa4188254a0e6817c0fe00fa00

def liveLevels : Nat → Packing
  | 6 => (2,1,4,0,0,5,0,liveData6)
  | _ => emptyPacking

def liveIndex : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none

def orSamples : Array (Bits × Bits) := #[(0x7ff001fffff800fffffc007ff001ffc007ff001ffc007ffffffffff800ffe003fffff001fffff800ffe003ff800ffe003ff800fffffffffff001ffc007ffffe003fffff001ffc007ff001ffc007ff001ffffffffffe003ff800fffffc007ff,0x290520a4148290520a4148290520a4148290520a4148290520a4148290520a4148290520a4148290520a4148290520a4148290520a4148290520a4148290520a4148290520a4148290520a4148290520a4148290520a4148290520a414829052),
  (0xff800001ffffffffffffffff800001fffff800001fffff800ffe003fffff000003ffffffffffffffff000003fffff000003fffff001ffc007ffffe000007fffffffffffffffe000007ffffe000007ffffe003ff800fffffc00000fffffffffff,0x42284508a1142284508a1142284508a1142284508a1142284508a1142284508a1142284508a1142284508a1142284508a1142284508a1142284508a1142284508a1142284508a1142284508a1142284508a1142284508a1142284508a1142284),
  (0xfffffffe003fffff001ffffffffffe00000000001ffffffff000003ffffffffffc007ffffe003ffffffffffc00000000003fffffffe000007ffffffffff800fffffc007ffffffffff800000000007fffffffc00000fffffffffff001fffff800,0xc4188310620c4188310620c4188310620c4188310620c4188310620c4188310620c4188310620c4188310620c4188310620c4188310620c4188310620c4188310620c4188310620c4188310620c4188310620c4188310620c4188310620c418),
  (0xffffffffffc00000001fffffffffffffffffffffe00000000000003fffffffffffff800000003fffffffffffffffffffffc00000000000007fffffffffffff000000007fffffffffffffffffffff80000000000000fffffffffffffe00000000,0x700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e0),
  (0x1fffffffffffffffffffffffffffffffffffc0000000000000000000003fffffffffffffffffffffffffffffffffff80000000000000000000007fffffffffffffffffffffffffffffffffff0000000000000000000000,0x80700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700),
  (0x0,0x0),
  (0x0,0x0),
  (0x0,0x0),
  (0x0,0x0)]

def orSymmetries : Array (List Nat) := #[[],[65,50],[16,66],[16,32,48,64],[32,67],[32,49,64,16],[48,33],[48,65,32,33],[64,16,33,50],[64,49]]

def orCols : IndexTree ColumnInfo := (.fork 5 (.fork 2 (.leaf [(0,0,31,0,7),(1,0,30,0,4)]) (.leaf [(4098,0,2077,0,4),(4100,0,2075,0,4),(4104,0,2071,0,4)])) (.fork 2 (.leaf [(4112,0,2063,0,4),(16386,0,8221,0,5)]) (.leaf [(16388,0,8219,0,5),(16392,0,8215,0,5),(16400,0,8207,0,5)])))

def orForest : Forest := ⟨2079,6,fun j => orSamples[j]?.getD (0,0),orCols,orSymmetries,liveLevels,liveIndex⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem orGeometry : graphValid orForest (boundsBefore entries2071) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem allAt6 : block orForest 6 0 2 = true := by
  apply wideBlock (depth:=0)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

theorem orTables : checkedTables orForest 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block orForest 0 0 0 = true)
  · exact (rfl : block orForest 1 0 0 = true)
  · exact (rfl : block orForest 2 0 0 = true)
  · exact (rfl : block orForest 3 0 0 = true)
  · exact (rfl : block orForest 4 0 0 = true)
  · exact (rfl : block orForest 5 0 0 = true)
  · exact allAt6

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withoutPositive : Impossible (graphGoal 31) 6 (minusZero 31).toFinset := by
  exact root_index (g:=orForest) (before_sound _ sound2071) orGeometry orTables
    (k:=6) (by decide) (i:=0) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withPositive : Impossible (graphGoal 31) 6 (vars 2079).toFinset := by
  exact root_index (g:=orForest) (before_sound _ sound2071) orGeometry orTables
    (k:=6) (by decide) (i:=1) (by decide +kernel)

end PEqualNP.Outside.L_meta_5006.Signed31
namespace PEqualNP.Outside.L_meta_5006
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem signedBound31 : Lower (vars 2079) (graphGoal 2079) 7 :=
  signedInduced (m:=31) (k:=6) (hints:=8449) (before_sound _ valid383 31)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) Signed31.withoutPositive Signed31.withPositive

def entries2079 := extendKnown entries2071 7 [(2079,[]),(2215,[115,67,100,83]),(2361,[131,115,65,50,98,81]),(2403,[131,50,66,116,99,82])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound2079 : Known entries2079 := extendKnown_ok sound2071 signedBound31 (by decide +kernel)
end PEqualNP.Outside.L_meta_5006
namespace PEqualNP.Outside.L_meta_5006.Signed47
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withoutPositive : Impossible (graphGoal 47) 4 (minusZero 47).toFinset := orderCut 3 2 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withPositive : Impossible (graphGoal 47) 4 (vars 2095).toFinset := countImpossible (by decide +kernel)

end PEqualNP.Outside.L_meta_5006.Signed47
namespace PEqualNP.Outside.L_meta_5006
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem signedBound47 : Lower (vars 2095) (graphGoal 2095) 5 :=
  signedInduced (m:=47) (k:=4) (hints:=8449) (before_sound _ valid383 47)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) Signed47.withoutPositive Signed47.withPositive

def entries2095 := extendKnown entries2079 5 [(2199,[115,99,83,67]),(2229,[114,81,98,50,65]),(2387,[131,50,114,82,99,66]),(2417,[130,50,81,115,98,65])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound2095 : Known entries2095 := extendKnown_ok sound2079 signedBound47 (by decide +kernel)
end PEqualNP.Outside.L_meta_5006
namespace PEqualNP.Outside.L_meta_5006.Signed55
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withoutPositive : Impossible (graphGoal 55) 4 (minusZero 55).toFinset := orderCut 3 2 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withPositive : Impossible (graphGoal 55) 4 (vars 2103).toFinset := countImpossible (by decide +kernel)

end PEqualNP.Outside.L_meta_5006.Signed55
namespace PEqualNP.Outside.L_meta_5006
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem signedBound55 : Lower (vars 2103) (graphGoal 2103) 5 :=
  signedInduced (m:=55) (k:=4) (hints:=257) (before_sound _ valid383 55)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) Signed55.withoutPositive Signed55.withPositive

def entries2103 := extendKnown entries2095 5 [(2103,[]),(2163,[98,50]),(2227,[114,81,98,50,65])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound2103 : Known entries2103 := extendKnown_ok sound2095 signedBound55 (by decide +kernel)
end PEqualNP.Outside.L_meta_5006
namespace PEqualNP.Outside.L_meta_5006.Signed185
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withoutPositive : Impossible (graphGoal 185) 4 (minusZero 185).toFinset := orderCut 17 16 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withPositive : Impossible (graphGoal 185) 4 (vars 2233).toFinset := countImpossible (by decide +kernel)

end PEqualNP.Outside.L_meta_5006.Signed185
namespace PEqualNP.Outside.L_meta_5006
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem signedBound185 : Lower (vars 2233) (graphGoal 2233) 5 :=
  signedInduced (m:=185) (k:=4) (hints:=1342193668) (before_sound _ valid383 185)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) Signed185.withoutPositive Signed185.withPositive

def entries2233 := extendKnown entries2103 5 [(2233,[]),(2275,[99,50,33,65])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound2233 : Known entries2233 := extendKnown_ok sound2103 signedBound185 (by decide +kernel)
end PEqualNP.Outside.L_meta_5006
namespace PEqualNP.Outside.L_meta_5006.Signed63
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withoutPositive : Impossible (graphGoal 63) 7 (minusZero 63).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=2111) (4128,0,2079,0,7) _ (before_sound _ sound2233) (by decide +kernel))
    [] (pool:=(vars (poolMask 2111 (4128,0,2079,0,7)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withPositive : Impossible (graphGoal 63) 7 (vars 2111).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=2111) (4128,0,2079,0,7) _ (before_sound _ sound2233) (by decide +kernel))
    [] (pool:=(vars (poolMask 2111 (4128,0,2079,0,7)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end PEqualNP.Outside.L_meta_5006.Signed63
namespace PEqualNP.Outside.L_meta_5006
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem signedBound63 : Lower (vars 2111) (graphGoal 2111) 8 :=
  signedInduced (m:=63) (k:=7) (hints:=8449) (before_sound _ valid383 63)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) Signed63.withoutPositive Signed63.withPositive

def entries2111 := extendKnown entries2233 8 [(2111,[]),(2231,[115,84,99]),(2419,[131,84,115,98])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound2111 : Known entries2111 := extendKnown_ok sound2233 signedBound63 (by decide +kernel)
end PEqualNP.Outside.L_meta_5006
namespace PEqualNP.Outside.L_meta_5006.Signed95
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withoutPositive : Impossible (graphGoal 95) 7 (minusZero 95).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=2143) (4160,0,2079,0,7) _ (before_sound _ sound2111) (by decide +kernel))
    [] (pool:=(vars (poolMask 2143 (4160,0,2079,0,7)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withPositive : Impossible (graphGoal 95) 7 (vars 2143).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=2143) (4160,0,2079,0,7) _ (before_sound _ sound2111) (by decide +kernel))
    [] (pool:=(vars (poolMask 2143 (4160,0,2079,0,7)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end PEqualNP.Outside.L_meta_5006.Signed95
namespace PEqualNP.Outside.L_meta_5006
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem signedBound95 : Lower (vars 2143) (graphGoal 2143) 8 :=
  signedInduced (m:=95) (k:=7) (hints:=16785665) (before_sound _ valid383 95)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) Signed95.withoutPositive Signed95.withPositive

def entries2143 := extendKnown entries2111 8 [(2143,[]),(2279,[67,116,83]),(2407,[131,67,116,83,98]),(2489,[98,134,114,81])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound2143 : Known entries2143 := extendKnown_ok sound2111 signedBound95 (by decide +kernel)
end PEqualNP.Outside.L_meta_5006
namespace PEqualNP.Outside.L_meta_5006.Signed119
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withoutPositive : Impossible (graphGoal 119) 5 (minusZero 119).toFinset := orderCut 3 2 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withPositive : Impossible (graphGoal 119) 5 (vars 2167).toFinset := countImpossible (by decide +kernel)

end PEqualNP.Outside.L_meta_5006.Signed119
namespace PEqualNP.Outside.L_meta_5006
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem signedBound119 : Lower (vars 2167) (graphGoal 2167) 6 :=
  signedInduced (m:=119) (k:=5) (hints:=16777473) (before_sound _ valid383 119)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) Signed119.withoutPositive Signed119.withPositive

def entries2167 := extendKnown entries2143 6 [(2167,[])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound2167 : Known entries2167 := extendKnown_ok sound2143 signedBound119 (by decide +kernel)
end PEqualNP.Outside.L_meta_5006
namespace PEqualNP.Outside.L_meta_5006.Signed159
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withoutPositive : Impossible (graphGoal 159) 7 (minusZero 159).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=2207) (4224,0,2079,0,7) _ (before_sound _ sound2167) (by decide +kernel))
    [] (pool:=(vars (poolMask 2207 (4224,0,2079,0,7)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withPositive : Impossible (graphGoal 159) 7 (vars 2207).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=2207) (4224,0,2079,0,7) _ (before_sound _ sound2167) (by decide +kernel))
    [] (pool:=(vars (poolMask 2207 (4224,0,2079,0,7)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end PEqualNP.Outside.L_meta_5006.Signed159
namespace PEqualNP.Outside.L_meta_5006
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem signedBound159 : Lower (vars 2207) (graphGoal 2207) 8 :=
  signedInduced (m:=159) (k:=7) (hints:=536879361) (before_sound _ valid383 159)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) Signed159.withoutPositive Signed159.withPositive

def entries2207 := extendKnown entries2167 8 [(2207,[]),(2223,[84,115]),(2365,[131,65,50,114,81]),(2425,[130,114,98,81])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound2207 : Known entries2207 := extendKnown_ok sound2167 signedBound159 (by decide +kernel)
end PEqualNP.Outside.L_meta_5006
namespace PEqualNP.Outside.L_meta_5006.Signed187
open PEqualNP.CircuitLowerBounds

def liveData6 (i : Nat) : Nat := 0x105fe00

def moveIndex6 (i : Nat) : Nat := 0x0

def liveData5 (i : Nat) : Nat := 0xbd58600

def liveLevels : Nat → Packing
  | 6 => (1,1,1,0,0,0,0,liveData6)
  | 5 => (1,2,1,0,0,0,0,liveData5)
  | _ => emptyPacking

def liveIndex : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 4 0 0 moveIndex6
  | _ => fun _ => none

def orSamples : Array (Bits × Bits) := #[(0xfffe0001fffc00007fff00003fff80000ffff00001ffff00000ffffe00001ffffe00000ffff800007fff800007fffffffffffffffffffff00003fffe00003fffffffffffffffffffffffffffffffc00001ffffe000007fffffffffffffffffff,0x12022000280c48020a0104000a0189002240512010480a1200a120142400024024240121204890040902890090902848122409090091005000214014200204014600924024a0121004848024280484002428024240090a00909002490090a012),
  (0xfffffffe000000007fffffffc00000000ffffffffe000000000fffffffffe0000000000fffffffff8000000007fffc0000fffffffffffffffffc000000003fffe00007fffe0000ffffc00001fffffffffe00000000007ffff800001fffffffff,0xa55d4d55428292a854b4a955a09452550c9aaa4d649150a4a90a4aa9495554950949524a4e952569521452452527529244c972527526aa8ad5482aa14554aaaa90aa24aac91524e559292a895569295549429494955254b52525549255254ea4),
  (0x0,0x0),
  (0xffffffffffffffff80000000000000000ffffffffffffffffff00000000000000000000ffffffffffffffffff800000000ffff800007ffffffffffffffffc000000007ffffffff0000000001ffffffffffffffffffff80000000001ffff80000,0x3866718670c8e0c3182030610c211c18470cc38638e19c3831c38330706187063070638384e1c18e1c271c11c1c060e018719c1c21c330e318718c38718700c30430c70c71c638418e0e0c30618e0e187070c707061c1821c1c1871c61c18438),
  (0xfffffffffffffffffffffffffffffffff00000000000000000000000000000000000000fffffffffffffffffffffffffff0000000007fffffffffffffffffffffffff8000000000000000001ffffffffffffffffffffffffffffffe000000000,0xc18986198313030c60c6c18630c6606188100c08410200c0c20c0c01818618184181840c0b0606306058606606058303608020604604c30c618230c18618330c18c3003080184086103030c18630306181831818186060c606061800060608c0),
  (0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000007fffffffffffffffffffffffffffffffffffffffffffe0000000000000000000000000000000000000000,0x1f007e003e003f000f801f800f8007e001f000f8003e000fc000fc001f8001f8001f8000c0007c000600078000600038001c0007800fc007e003f0007e003f000fc003f001f8007e0003f0007c0007e0003e0001f8000f80007e00078000f00),
  (0x0,0x0),
  (0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0xfe01f801fc03fc007f00fe003f007f800fe00ff001fc00ff000ff001fe001fe001fe000ff007f8007f807f8007f803fc00fe007f8007000f8003c001f8003c001f0007c001e000f8003fc001f8003f8001fc001fe0007f0007f8001f8007f000),
  (0x0,0x0)]

def orSymmetries : Array (List Nat) := #[[],[115,84]]

def orCols : IndexTree ColumnInfo := (.leaf [(4104,0,2227,0,5),(4226,0,2105,0,4)])

def orForest : Forest := ⟨2235,6,fun j => orSamples[j]?.getD (0,0),orCols,orSymmetries,liveLevels,liveIndex⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem orGeometry : graphValid orForest (boundsBefore entries2207) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem allAt6 : block orForest 6 0 1 = true := by
  apply wideBlock (depth:=0)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem allAt5 : block orForest 5 0 1 = true := by
  apply wideBlock (depth:=0)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

theorem orTables : checkedTables orForest 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block orForest 0 0 0 = true)
  · exact (rfl : block orForest 1 0 0 = true)
  · exact (rfl : block orForest 2 0 0 = true)
  · exact (rfl : block orForest 3 0 0 = true)
  · exact (rfl : block orForest 4 0 0 = true)
  · exact allAt5
  · exact allAt6

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withoutPositive : Impossible (graphGoal 187) 6 (minusZero 187).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=2235) (16386,0,8377,0,6) _ (before_sound _ sound2207) (by decide +kernel))
    [] (pool:=(vars (poolMask 2235 (16386,0,8377,0,6)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withPositive : Impossible (graphGoal 187) 6 (vars 2235).toFinset := by
  exact root_index (g:=orForest) (before_sound _ sound2207) orGeometry orTables
    (k:=6) (by decide) (i:=0) (by decide +kernel)

end PEqualNP.Outside.L_meta_5006.Signed187
namespace PEqualNP.Outside.L_meta_5006
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem signedBound187 : Lower (vars 2235) (graphGoal 2235) 7 :=
  signedInduced (m:=187) (k:=6) (hints:=1342193665) (before_sound _ valid383 187)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) Signed187.withoutPositive Signed187.withPositive

def entries2235 := extendKnown entries2207 7 [(2235,[]),(2291,[99,65])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound2235 : Known entries2235 := extendKnown_ok sound2207 signedBound187 (by decide +kernel)
end PEqualNP.Outside.L_meta_5006
namespace PEqualNP.Outside.L_meta_5006.Signed189
open PEqualNP.CircuitLowerBounds

def liveData7 (i : Nat) : Nat := 0xc846b0c84a83fc01fa00

def liveLevels : Nat → Packing
  | 7 => (2,1,3,0,0,5,0,liveData7)
  | _ => emptyPacking

def liveIndex : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none

def orSamples : Array (Bits × Bits) := #[(0xffff0001ffff00007fffc0007fffc0001fff00007fff80007fff80003ffff00003fff80001fff80001fffe0000ffffffff80001fffe00007fffc0001ffff0000ffffffffffff00007ffffffffffffffffc0000ffff80001ffffffffffffc0000,0x500b4014a016500928069402280594025415500a28152809280d28029402a500a940aa8054a0b28054a054a00a500a941528054a054a015280a90054a01640124034c02aa02aa015500a98054a015280a9402a501528054c02a500aa80a9402a),
  (0x0,0x0),
  (0xfffffffe000000007fffffff800000001fffffff800000007fffffffc000000003fffffffe00000001ffffffff00003ffffffffffffffffffffffffe00000000fffe0000ffffffff80003fffe00007ffffffff000000001ffff00003ffffffff,0x4a20946094404a20253012b02510128814604a302460242025602530128c04a3016302518022025180b18094c04a300c6025180d18094604a302518094409441298128c128c094604a302518094602630128c044602518128c04a302a30128c),
  (0xffffffffffffffff80000000000000001fffffffffffffff800000000000000003fffffffffffffffe0000000000003fffffffe000000007ffffffffffffffff00000000ffffffffffffc000000007ffffffffffffffffe000000003ffffffff,0x610c6218c218610c30841840308618431898610c3098308c3088308418430610c188c30860c4c30860c060c210610c191830860c060c218310c18860c218621804208430c430c218610c10860c218308c184306118308608430610c310c18430),
  (0xffffffffffffffffffffffffffffffffe000000000000000000000000000000003ffffffffffffffffffffffffffffc00000000000000007ffffffffffffffffffffffff0000000000000000000007fffffffffffffffffffffffffc00000000,0x86308c610c6086304318218c4318218c010086304300431043104318218c086302130431810b0431810d810c60863020604318109810c604630231810c608c6098c118c018c00c600630231810c604330218c086604318118c086300230218c0),
  (0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0000000000000000000000000000000000000000000007fffffffffffffffffffffffffffffffffffffffffffff80000000000000000000000000000000000,0x7c00f800f8007c003e001f003e001f001e007c003e003e003e003e001f0007c001c003e000c003e000e000f8007c0018003e000e000f8007c003e000f800f801f001f001f000f8007c003e000f8003c001f00078003e001f0007c003c001f00),
  (0x0,0x0),
  (0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff800000000000000000000000000000000000000000000000000000000000000000000000000000000,0xf800f001f000f8007c003e007c003e001e00f8007c007c007c007c003e000f8003e007c001f007c001f001f000f8003e007c001f001f00078003c001f000f000e001e000e000f00078003c001f0007c003e000f8007c001e000f8003c003e000),
  (0x0,0x0)]

def orSymmetries : Array (List Nat) := #[[],[115,84],[32,67,117],[32,83,116],[48,82],[48,82,112,66],[64,114,50,48,80],[64,114,83],[80,50,116],[80,50,66,32,114],[112,66,48,82],[112,66]]

def orCols : IndexTree ColumnInfo := (.fork 3 (.leaf [(0,0,189,0,8),(17,0,172,0,4),(4108,0,2225,0,4)]) (.leaf [(4256,0,2077,0,4),(16396,0,8369,0,5),(16400,0,8365,0,6),(16544,0,8221,0,5)]))

def orForest : Forest := ⟨2237,7,fun j => orSamples[j]?.getD (0,0),orCols,orSymmetries,liveLevels,liveIndex⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem orGeometry : graphValid orForest (boundsBefore entries2235) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem allAt7 : block orForest 7 0 2 = true := by
  apply wideBlock (depth:=0)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

theorem orTables : checkedTables orForest 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block orForest 0 0 0 = true)
  · exact (rfl : block orForest 1 0 0 = true)
  · exact (rfl : block orForest 2 0 0 = true)
  · exact (rfl : block orForest 3 0 0 = true)
  · exact (rfl : block orForest 4 0 0 = true)
  · exact (rfl : block orForest 5 0 0 = true)
  · exact (rfl : block orForest 6 0 0 = true)
  · exact allAt7

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withoutPositive : Impossible (graphGoal 189) 7 (minusZero 189).toFinset := by
  exact root_index (g:=orForest) (before_sound _ sound2235) orGeometry orTables
    (k:=7) (by decide) (i:=0) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withPositive : Impossible (graphGoal 189) 7 (vars 2237).toFinset := by
  exact root_index (g:=orForest) (before_sound _ sound2235) orGeometry orTables
    (k:=7) (by decide) (i:=1) (by decide +kernel)

end PEqualNP.Outside.L_meta_5006.Signed189
namespace PEqualNP.Outside.L_meta_5006
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem signedBound189 : Lower (vars 2237) (graphGoal 2237) 8 :=
  signedInduced (m:=189) (k:=7) (hints:=536879876) (before_sound _ valid383 189)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) Signed189.withoutPositive Signed189.withPositive

def entries2237 := extendKnown entries2235 8 [(2237,[]),(2395,[130,50,98,82,115,33,65])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound2237 : Known entries2237 := extendKnown_ok sound2235 signedBound189 (by decide +kernel)
end PEqualNP.Outside.L_meta_5006
namespace PEqualNP.Outside.L_meta_5006.Signed215
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withoutPositive : Impossible (graphGoal 215) 6 (minusZero 215).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=2263) (16448,0,8343,0,6) _ (before_sound _ sound2237) (by decide +kernel))
    [] (pool:=(vars (poolMask 2263 (16448,0,8343,0,6)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withPositive : Impossible (graphGoal 215) 6 (vars 2263).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=2263) (1,16,198,0,4) _ (before_sound _ sound2237) (by decide +kernel))
    [] (pool:=(vars (poolMask 2263 (1,16,198,0,4)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end PEqualNP.Outside.L_meta_5006.Signed215
namespace PEqualNP.Outside.L_meta_5006
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem signedBound215 : Lower (vars 2263) (graphGoal 2263) 7 :=
  signedInduced (m:=215) (k:=6) (hints:=553648385) (before_sound _ valid383 215)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) Signed215.withoutPositive Signed215.withPositive

def entries2263 := extendKnown entries2237 7 [(2263,[]),(2485,[134,81,114,49]),(2545,[118,33,129,82,49])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound2263 : Known entries2263 := extendKnown_ok sound2237 signedBound215 (by decide +kernel)
end PEqualNP.Outside.L_meta_5006
namespace PEqualNP.Outside.L_meta_5006.Signed349
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withoutPositive : Impossible (graphGoal 349) 6 (minusZero 349).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=2397) (16388,0,8537,0,6) _ (before_sound _ sound2263) (by decide +kernel))
    [] (pool:=(vars (poolMask 2397 (16388,0,8537,0,6)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withPositive : Impossible (graphGoal 349) 6 (vars 2397).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=2397) (0,1,332,16,5) _ (before_sound _ sound2263) (by decide +kernel))
    [] (pool:=(vars (poolMask 2397 (0,1,332,16,5)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end PEqualNP.Outside.L_meta_5006.Signed349
namespace PEqualNP.Outside.L_meta_5006
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem signedBound349 : Lower (vars 2397) (graphGoal 2397) 7 :=
  signedInduced (m:=349) (k:=6) (hints:=13019128580) (before_sound _ valid383 349)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) Signed349.withoutPositive Signed349.withPositive

def entries2397 := extendKnown entries2263 7 [(2397,[]),(2461,[118,130])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound2397 : Known entries2397 := extendKnown_ok sound2263 signedBound349 (by decide +kernel)
end PEqualNP.Outside.L_meta_5006
namespace PEqualNP.Outside.L_meta_5006.Signed455
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withoutPositive : Impossible (graphGoal 455) 6 (minusZero 455).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=2503) (16512,0,8519,0,6) _ (before_sound _ sound2397) (by decide +kernel))
    [] (pool:=(vars (poolMask 2503 (16512,0,8519,0,6)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withPositive : Impossible (graphGoal 455) 6 (vars 2503).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=2503) (1,0,454,0,5) _ (before_sound _ sound2397) (by decide +kernel))
    [] (pool:=(vars (poolMask 2503 (1,0,454,0,5)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end PEqualNP.Outside.L_meta_5006.Signed455
namespace PEqualNP.Outside.L_meta_5006
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem signedBound455 : Lower (vars 2503) (graphGoal 2503) 7 :=
  signedInduced (m:=455) (k:=6) (hints:=26323452161) (before_sound _ valid383 455)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) Signed455.withoutPositive Signed455.withPositive

def entries2503 := extendKnown entries2397 7 [(2503,[])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound2503 : Known entries2503 := extendKnown_ok sound2397 signedBound455 (by decide +kernel)
end PEqualNP.Outside.L_meta_5006
namespace PEqualNP.Outside.L_meta_5006.Signed127
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withoutPositive : Impossible (graphGoal 127) 8 (minusZero 127).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=2175) (4128,0,2143,0,8) _ (before_sound _ sound2503) (by decide +kernel))
    [] (pool:=(vars (poolMask 2175 (4128,0,2143,0,8)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withPositive : Impossible (graphGoal 127) 8 (vars 2175).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=2175) (4128,0,2143,0,8) _ (before_sound _ sound2503) (by decide +kernel))
    [] (pool:=(vars (poolMask 2175 (4128,0,2143,0,8)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end PEqualNP.Outside.L_meta_5006.Signed127
namespace PEqualNP.Outside.L_meta_5006
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem signedBound127 : Lower (vars 2175) (graphGoal 2175) 9 :=
  signedInduced (m:=127) (k:=8) (hints:=16785665) (before_sound _ valid383 127)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) Signed127.withoutPositive Signed127.withPositive

def entries2175 := extendKnown entries2503 9 [(2175,[]),(2295,[84,115]),(2423,[131,84,115,98]),(2547,[98,99,81,131,114,65])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound2175 : Known entries2175 := extendKnown_ok sound2503 signedBound127 (by decide +kernel)
end PEqualNP.Outside.L_meta_5006
namespace PEqualNP.Outside.L_meta_5006.Signed191
open PEqualNP.CircuitLowerBounds

def liveData10 (i : Nat) : Nat := 0xdc8804ccb0b006e6c887c5b40ff803fa00

def moveIndex10 (i : Nat) : Nat := 0x3910015cb2000e096b6ba9b2568535d16dcb099ebb16974d62de4149ad90d470030a53db4cb18c1668114d40000b7e6800a60008d678810ce0400000000002948180001480280e5a80a11000900000

def liveData9 (i : Nat) : Nat := 0x5c2b11c88021f079c6423200a24439008cc589118a244011c8b03e7168d42a0c1508c02711c88022c9983cc250a888722a99804588180a2440199cb04671588a66010703cc270a88c1e281cccc022216282a0c114b2662a009c5733008381e5008a245330a8b01e711054192211cce5801408a5f26008581c6020540416998045871fc8a662c20102a080105a660116207722998b081a0308c04411d8542c0c99cb002c00848400a119500411dc884733961c0815064cc452c009c71339608880121908584228b07e31bc0080391b00446471e248001230fc4451bcda893e00946f809b5127c5de5a732c614bb3632a450d95d1aa1c3f474edb1942ff564a250c1e63445789a90c1d825832032001ff55200ffac7007fd53803fe39401ff50a00ffa65007fe22803fea0c01ff4c600ffa43007fd40803fe98401ff48200ffa21005fd74803df224017f5ce00fbc67005fd72802fe39401fb88a00bfae3007f611803fca0401fe4c200ff241007f910803fcb9401fa88a00

def moveIndex9 (i : Nat) : Nat := 0xcbf04755d478c0641c2808f1085a3b6509c9455e6790e000f5f000e5776e311c6f4397a28e1700c1bd75840698c5b469713fcefaf000535ed23430a0000859bbb73d7b0001000a8e610f46c140000c1000ddc963000000000f58b28d4f8a1000725b9139bec2372b3344d51e6dd162802b0f0000000940e9766904fdb0000000000160002cfc810007eb417c5295442b20c515eb8537099945a2c0d5e2d000d93a87c6dc1fb2ee3ca2441d0000ee9bc3383085685c4512b48921e4267a73250b000051faaf41326830e27007f7445a722f4ed9fb79e8f903c86cae23a744c97d1ae771e37d8234736d3e63181910dfa5c23773b49c3f8c0b091f07bda0acefd95e60690329a704c7dedab4c64c6c371a9298d34ac5c6d7d2f00516a000d61e2034c0006539186b124b6569e500002a3bea7665e4a9e6b5655f62e41ae118200c06881c1000000011003a402003000000c40cb850000180000dc000e44582007410100403025800b883c000002274204307828c0000122

def liveData8 (i : Nat) : Nat := (if i < 1 then 0x8c014bc2c1858078801481c20900310460088260044138202090202042200440c01e2004200042128420e8c1707c400840008410d25820061a102407892b08120908040828058360510230081f03c20048c1a062078c010d8402024078c040b00f18080788190502504c0a2846100420004201043b10600a0161403c0884670051a4186008401080210300e10320a0140304a089a230180f18360a0160510150301b0288008400084000a34830c0408018004097040910411e863d0c7a1c003a146c100431b052b0c6c1c0029105220830008018004010812b0824118141001e5a32a2da149f19e29d39ba9b59a698d97496594c93d92490b8fc8e38ca8bb88e87585c8398207fd7ee7d57d07b779e78576275373a7216fe6db6c26bd6a468b6726596406316226095f05e15dc5cd5aa59158257d56e56955053751e50f4f64e74ba47945643d41a3f73de3a739838938437537035730c2e92da2cb2bc2a326223f2121e51d61d11c21bd19a18b18618117216d15e15914a1451361271180ff0f00e10d20c30b40a509608708207306e06905a04b046037000bfe8858e00bfc8758e00dfd635ca00dfd541ca00bfd831ca00bfd811ca00bfe884ca00bfc874ca00bfd864ca00dfd764ca00dfd754ca00fdd634ca00dfd724ca00dfd7488a00dfd635c600dfd325c600dfe225c600dfc7250600bfe884c600bfc874c600bfd864c600dfd764c600dfd754c600dfd724c600fdd324c600ff5514c600bfe8848600dfd8748600bfc8748600dfd7448600bfd8348600dfd7348600dfd7248600fec7248600ff53148600dfc7250200bfd864c200fdd634c200fdd314c200bfe8848200bfd8348200ff48148200fed2148200ff93048200bfd8344200bfd8244200dfc7244200ff920442009fc8755200dbd7591200f3e5591200d7e555ce009fc8758e009fc8754e00ddd768ce00ede668ce00ddd758ce00f5e558ce00dbe445ca00dde335ca009fd841ca00dbe441ca009fd831ca00dde331ca009fd811ca009fd801ca00bbd841ca00bf9801ca009fc8750a00dbd7450a00dec7250a009fc874ca00dec8788a00ded7488a00fae4488a00ded7388a00fce3388a00fe88088a009fc8788a00ded7288a00dbe445c600dde335c600dee225c6009fc87506009fc874c600df5714c6009fc8748600dec7248600df57484600fb64484600df57384600fd63384600df57284600df47284600fe62284600efa6650200bf98550200f7a5550200fb95450200fea2250200fb94150200ff21150200efa664c200f7a554c200ff2114c200bf98448200fba4448200df97348200fda3348200fe94248200fea2248200ff08148200df97148200fe92148200ff21148200bf98444200fba4444200fda3344200bf98244200df97244200fea2244200ff141442009bd841ca00 else 0x21288000838201015030693052208021288000840102440081224bc28d44c203420083820a803124610380c100212880f080297c4c11900101c40381e24682a03c611054203d2e89860084310a8400040510021508010a8400862150c01081e15080c01041905c15)

def moveIndex8 (i : Nat) : Nat := 0x7a10216204bd05d2651ee4b01f3000c4271e15c4500370c839e3b937070000000040f914c094aa9df00000d5b259368250cc11c2ca6a85e3431a84880097670010822c2008

def liveData7 (i : Nat) : Nat := 0x42000000000048c20038103888c40882000000000008020800204020402040206118400102092c82371688c320f027ebb5d0d85eab550a34f265288f3f9bcd45a250e8541a0a814011fd9221d638023fb2243ac7004fd6448758e00cfa48b00394011fc97619328033b90eb1a650047f6448788a00cfac890f114011fc985d2228023f931112e30055f65472506008fe4bb0c98c019f5865c531803baa64b8a630067d21d514c6008fe4bd1090c0157d951c9408027eb23442410047f6607244200adeca0e4884015f5911c910802bf320392210047d6448758e008df4cb083940193d85910728032bb0b198e500667612331ca00af2c890f114011f59121e22802b6b2839423004fc2621148200

def moveIndex7 (i : Nat) : Nat := 0x3b6

def liveData6 (i : Nat) : Nat := 0x2887d684985d2228021f5a125e8848600

def liveLevels : Nat → Packing
  | 10 => (2,1,7,0,0,6,0,liveData10)
  | 9 => (29,2,7,0,0,11,0,liveData9)
  | 8 => (123,3,7,0,0,12,0,liveData8)
  | 7 => (31,4,7,0,0,9,0,liveData7)
  | 6 => (2,5,7,0,0,3,0,liveData6)
  | _ => emptyPacking

def liveIndex : Nat → Nat → Option (Nat × Nat)
  | 10 => lookupWord 20 53 5 10 5 1 moveIndex10
  | 9 => lookupWord 68 211 7 12 7 1 moveIndex9
  | 8 => lookupWord 13 43 6 11 5 2 moveIndex8
  | 7 => lookupWord 1 3 0 5 1 0 moveIndex7
  | _ => fun _ => none

def orSamples : Array (Bits × Bits) := #[(0x9c078081e01c00f8000781e001f80018fc03f8007f80000c301e03fc00701fc03ffffe0fe007ff803ff00003ff8100e01f0003e01ffffffe01fc007fffff801ffffffffff00fc00fe001ff000007e007ffffffffff007f00003ffff00003ffff,0x10040000200000400005c08400a90000c6110800510900243206005c491009400498d405c4a24b0024512020520000000100082000c0006000140101e05080005404c014900a814080010a100290a0045202300d29005520051491920020a02a),
  (0x1ff800fe001fff0000f801fffe00001f0003ffff8000000fc01ffc00007fe0003f803ff00007ffffc0000003fffe00ffe00003ffe03fc00ffe00007f800fffe00ffc00003ff0000ffffe00000007fff80ffe00007fff8000003fffffffffffff,0xfd820ea001eae244ae809796d02494d0002d5bba052290b48195e82906b60282b402b680904b4f3480a460aa4be50fae0291109402aca0b9a00446a088a35400bbb14812ad0000f3d6a20a2942515480dad452042ec80c308232e2d694b4f44),
  (0xe00000ffffe0000000fffe000000001ffffc00000000000fffe00000007fffffc0003ffffff807fffffffffc00ffff00000003ffffc0000fffffff80000ffffff00000003ffffff0000000000007fffff00000007fffffffffc00ffffffc0000,0xc0000014e5600000900002000000021234d80000040042200040000000108383400000106008010481e009b000418700104242f2b5901000214511800204c892e00021061504dc600000000420c2c293604008460c012604518000c092301008),
  (0xffffff000000000000ffffffffffffe0000000000000000fffffffffff80000000003ffffffff8000000000000fffffffffffc000000000ffffffffffff00000000000003ffffffffffffffffff80000000000007ffffffffffff00000000000,0x351eb2000000080000beedae37db8c6080000111401c0c05e32c64e8e18200000010b3ae8e37382130038240c0121843250c1c000000004fcc9a66334ce81104011186182a6b2185c98d8c38c70000000008610870b658718e3bc30620418470),
  (0xffffffffffffffffff00000000000000000000000000000fffffffffffffffffffffc000000000000000000000fffffffffffffffffffff00000000000000000000000003fffffffffffffffffffffffffffffff800000000000000000000000,0xca6144db965b33b6e300001040041000208086220060704a0c518b03026cd233b263000010000042008c0c8300e5e2bc5af0635cd93cbc800101804010006018822238200584160a163070c738071be389718e700000008610000408c3821980),
  (0xfffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffc0000000000000000000000000000000000000000000000000000000,0xec71871cc78c3c38fc300e2078101f9b38e0e03c06007f800000000000000002000200000000200401000f0000f9fccf9c7f839f1e1f1f0cf1e1f87c1f0f7e1f03c03fc00600180007c04007c000030201800f8000382007e0020800fc001e00),
  (0x0,0x0),
  (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x138678e11813c0c700c771df81e7e004c30307c0787f800fbf9ff3f3fc4f1c3c3c7c3dcf1fc7c6783e0ff003f8000010008000000020200100020000600000000c03c0000808200c180180f800041c040e01f00000c040f8003c000f0003e000),
  (0x0,0x0)]

def orSymmetries : Array (List Nat) := #[[],[115,84],[32,67,117],[32,83,116]]

def orCols : IndexTree ColumnInfo := (.fork 36 (.fork 18 (.fork 9 (.fork 4 (.leaf [(0,0,191,0,11),(1,0,190,0,7),(2,0,189,0,8),(3,0,188,0,5)]) (.fork 2 (.leaf [(4,0,187,0,7),(6,0,185,0,5)]) (.leaf [(8,0,183,0,8),(10,0,181,0,5),(4,8,163,16,5)]))) (.fork 4 (.leaf [(12,0,179,0,5),(14,0,177,0,4),(0,16,166,9,6),(1,16,166,8,5)]) (.fork 2 (.leaf [(17,0,174,0,5),(19,0,172,0,4)]) (.leaf [(9,16,166,0,4),(25,0,166,0,4),(26,0,165,0,4)])))) (.fork 9 (.fork 4 (.leaf [(20,8,163,0,4),(28,0,163,0,4),(0,32,30,129,6),(1,32,30,128,5)]) (.fork 2 (.leaf [(35,0,156,0,4),(40,0,151,0,5)]) (.leaf [(48,0,143,0,5),(0,128,27,36,6),(128,0,63,0,8)]))) (.fork 4 (.leaf [(134,0,57,0,4),(136,0,55,0,5),(152,0,39,0,4),(160,0,31,0,7)]) (.fork 2 (.leaf [(129,32,30,0,4),(36,128,27,0,4)]) (.leaf [(168,0,23,0,4),(4098,0,2237,0,8),(4100,0,2235,0,7)]))))) (.fork 18 (.fork 9 (.fork 4 (.leaf [(4102,0,2233,0,5),(4096,8,2211,20,6),(4104,0,2231,0,8),(4106,0,2229,0,5)]) (.fork 2 (.leaf [(4100,8,2211,16,5),(4108,0,2227,0,5)]) (.leaf [(4110,0,2225,0,4),(4112,0,2223,0,8),(4120,0,2215,0,7)]))) (.fork 4 (.leaf [(4116,8,2211,0,4),(4128,0,2207,0,8),(4224,0,2111,0,8),(4100,128,2075,32,5)]) (.fork 2 (.leaf [(4230,0,2105,0,4),(4232,0,2103,0,5)]) (.leaf [(4256,0,2079,0,7),(4132,128,2075,0,4),(4260,0,2075,0,4)])))) (.fork 9 (.fork 4 (.leaf [(16386,0,8381,0,9),(16388,0,8379,0,8),(16390,0,8377,0,6),(16384,8,8355,20,7)]) (.fork 2 (.leaf [(16394,0,8373,0,6),(16388,8,8355,16,6)]) (.leaf [(16398,0,8369,0,5),(16400,0,8367,0,9),(16408,0,8359,0,8)]))) (.fork 4 (.leaf [(16404,8,8355,0,5),(16384,128,8219,36,7),(16388,128,8219,32,6),(16518,0,8249,0,5)]) (.fork 2 (.leaf [(16416,128,8219,4,6),(16544,0,8223,0,8)]) (.leaf [(16546,0,8221,0,5),(16552,0,8215,0,5),(16560,0,8207,0,5)]))))))

def orForest : Forest := ⟨2239,10,fun j => orSamples[j]?.getD (0,0),orCols,orSymmetries,liveLevels,liveIndex⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem orGeometry : graphValid orForest (boundsBefore entries2175) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem allAt10 : block orForest 10 0 2 = true := by
  apply wideBlock (depth:=0)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem allAt9 : block orForest 9 0 29 = true := by
  apply wideBlock (depth:=3)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem allAt8 : block orForest 8 0 123 = true := by
  apply wideBlock (depth:=5)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem allAt7 : block orForest 7 0 31 = true := by
  apply wideBlock (depth:=3)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem allAt6 : block orForest 6 0 2 = true := by
  apply wideBlock (depth:=0)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

theorem orTables : checkedTables orForest 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block orForest 0 0 0 = true)
  · exact (rfl : block orForest 1 0 0 = true)
  · exact (rfl : block orForest 2 0 0 = true)
  · exact (rfl : block orForest 3 0 0 = true)
  · exact (rfl : block orForest 4 0 0 = true)
  · exact (rfl : block orForest 5 0 0 = true)
  · exact allAt6
  · exact allAt7
  · exact allAt8
  · exact allAt9
  · exact allAt10

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withoutPositive : Impossible (graphGoal 191) 10 (minusZero 191).toFinset := by
  exact root_index (g:=orForest) (before_sound _ sound2175) orGeometry orTables
    (k:=10) (by decide) (i:=0) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withPositive : Impossible (graphGoal 191) 10 (vars 2239).toFinset := by
  exact root_index (g:=orForest) (before_sound _ sound2175) orGeometry orTables
    (k:=10) (by decide) (i:=1) (by decide +kernel)

end PEqualNP.Outside.L_meta_5006.Signed191
namespace PEqualNP.Outside.L_meta_5006
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem signedBound191 : Lower (vars 2239) (graphGoal 2239) 11 :=
  signedInduced (m:=191) (k:=10) (hints:=536879361) (before_sound _ valid383 191)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) Signed191.withoutPositive Signed191.withPositive

def entries2239 := extendKnown entries2175 11 [(2239,[]),(2367,[135,50,65]),(2427,[130,50,81,115,98,65])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound2239 : Known entries2239 := extendKnown_ok sound2175 signedBound191 (by decide +kernel)
end PEqualNP.Outside.L_meta_5006
namespace PEqualNP.Outside.L_meta_5006.Signed223
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withoutPositive : Impossible (graphGoal 223) 8 (minusZero 223).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=2271) (4160,0,2207,0,8) _ (before_sound _ sound2239) (by decide +kernel))
    [] (pool:=(vars (poolMask 2271 (4160,0,2207,0,8)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withPositive : Impossible (graphGoal 223) 8 (vars 2271).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=2271) (1,0,222,0,7) _ (before_sound _ sound2239) (by decide +kernel))
    [] (pool:=(vars (poolMask 2271 (1,0,222,0,7)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end PEqualNP.Outside.L_meta_5006.Signed223
namespace PEqualNP.Outside.L_meta_5006
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem signedBound223 : Lower (vars 2271) (graphGoal 2271) 9 :=
  signedInduced (m:=223) (k:=8) (hints:=553656577) (before_sound _ valid383 223)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) Signed223.withoutPositive Signed223.withPositive

def entries2271 := extendKnown entries2239 9 [(2271,[]),(2553,[118,130,81])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound2271 : Known entries2271 := extendKnown_ok sound2239 signedBound223 (by decide +kernel)
end PEqualNP.Outside.L_meta_5006
namespace PEqualNP.Outside.L_meta_5006.Signed251
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withoutPositive : Impossible (graphGoal 251) 7 (minusZero 251).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=2299) (4104,0,2291,0,7) _ (before_sound _ sound2271) (by decide +kernel))
    [] (pool:=(vars (poolMask 2299 (4104,0,2291,0,7)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withPositive : Impossible (graphGoal 251) 7 (vars 2299).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=2299) (4104,0,2291,0,7) _ (before_sound _ sound2271) (by decide +kernel))
    [] (pool:=(vars (poolMask 2299 (4104,0,2291,0,7)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end PEqualNP.Outside.L_meta_5006.Signed251
namespace PEqualNP.Outside.L_meta_5006
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem signedBound251 : Lower (vars 2299) (graphGoal 2299) 8 :=
  signedInduced (m:=251) (k:=7) (hints:=1358970881) (before_sound _ valid383 251)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) Signed251.withoutPositive Signed251.withPositive

def entries2299 := extendKnown entries2271 8 [(2299,[])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound2299 : Known entries2299 := extendKnown_ok sound2271 signedBound251 (by decide +kernel)
end PEqualNP.Outside.L_meta_5006
namespace PEqualNP.Outside.L_meta_5006.Signed351
open PEqualNP.CircuitLowerBounds

def liveData10 (i : Nat) : Nat := 0xea518300a862b6c5a00ff803fa00

def moveIndex10 (i : Nat) : Nat := 0xe4d80000b74b5766dfa206da274017b29be6f5003f152605f3e06f7f001c4b66b4977400ce41801d96729c001841410202

def liveData9 (i : Nat) : Nat := 0x9d332907258c34e9014039812c61c78b41e960838c4e1c480e663a4b1880e1d073021258c3838f52c61038927498cc9630e1c3a60424b1861d1c9da58c28e010683907696301c81c08394b180e69d258c1ce92c60c140c5810246830f3b4a69184a51d8c18b89060e127694c630858187232d0c371999a990610e4dc7430854606838701862d0c3918655db179200aa08bcb4e4c5e55576c185808c2aabb6297d555865b1600b6aa32aed8d005519576c5aa745a70c9c8bf0e9febc8736dd9a8b1c5feb8952a804c68f90c9fc3be6e8ca960286478748bc11e18816800ffac7007fd53803ff19c01ff58a00ffaa5007fd32803feb0c01ff54600ffa63007fc31803fe90c01ff84600dfccd0077e55802fe39c01f78ce00fdc45005fc71803fb08c01fe58200ff2a1007f930803fc90401fe44200ff0e7007f943803fd19c01fe50600ff263007ba44803ed19c01fc84600

def moveIndex9 (i : Nat) : Nat := 0xf42c0e712e16f5790f953978d6381eb0976b840074445b2ac0a636319523344f4da0400ba6fc5f21845a043c3f762165560e77834c1c33c000075903221000a2b000130000f0120002ff56d2d86487b44905828173e91a532371d0d36d43bf02f08f5043115dc70d4f525b14161a7631b955a28151c1da4a954f15e6935b84cf38d35479811a5eb4674b92712062697200000023d94ed7a01f00082900003a40c000267e59000033837766248000852006247d2e173f07441c1341786a000968b39000000a2c000124000c5c21066e822a0546c10a02434178000a086088200540b401822410020030020c200010d1c16502430c1

def liveData8 (i : Nat) : Nat := (if i < 1 then 0x8186015281860908114a203840811228c4020208040410063a10180842201004404081031d08141a1a186c34201043417100820f0a82618407c082a0d206c1a20d03440e08000e06880410c83441905848613078241a400004100582e1a18082120b88041098142219861404109c302407200821706883012068c260f410348110a834780084c240b0390081000041000020710000043030c080430c0c30201060a04186040086041020c0820003002e103001000081000430c082820c004021c00ac52b081032b0a3020000020cd5cab6c5c06af6c3c06af6c38a088987286484d83681f8087f17da7cc7b579e78777976274272b7147066ef6e16c16a169367c66e66064963261b5fb5e45cd5bf5b15a358356c55e5475395104e74d04b94ab4a64a148a47c46544541c4174124043ff3df3d13ba3ac37a36c34333531e2fe2d52b52a727e27026b26625825324e23723222d2282232152071f91eb1dd1c61b81aa1a51a019218d17f17116c16716214b14613813312e12011b10d0ff0f10ec0de0d00b90ab09d08f08107c077072040020000bfe8858e00bfe8854e00bfe8858a00efd6358a00bfe8854a00dfc7354a00f7d5354a00bfe884ca00bfd864ca00bfd854ca00fed624ca00dfd631c600dfe331c600dfd621c600dfd321c600bfe8858600efd6258600bfe8854600dfc7354600f7d5254600bfe884c600dfc874c600bfd864c600bfd854c600dfc734c600fdd534c600fec824c600fdd324c600ff5614c600bfd860c600bfd850c600bfd8648600bfd8548600bfd8348600dfc7348600fed5248600ff531486009fe881ce009fd861ce00cfe661ce009fd851ce00d7e551ce009fd821ce009fd811ce009fc8758e009fc8754e00ddc878ce00ede668ce00f5e558ce009fc878ce00ddc738ce009fc8758a009fc8754a009fc874ca00eee6688a00f6e5588a00dec7388a00fce3388a009fd861c600cfe661c6009fd851c600d7e551c6009fd831c600dde331c6009fd821c600dee221c6009fc87586009fc87546009fc874c600ddc734c600bf9800c6009fc8748600df48784600ef66684600f765584600df47384600fd63384600fe622846009fc8784600fea2258200ff21158200fda3354200fea2254200efa664c200f7a554c200df8734c200fda334c200fea224c200df8714c200fd9314c200ff2114c200efa6648200f7a5548200bf98348200fda3348200fe96248200fe92148200ff21148200efa6644200f7a5544200bf98344200fda3344200bf98244200fea2244200ff21144200bf9811ce00fd8878ce00bf8878ce00bfa8850600df88750600fda3350600bfa884c600bf8874c600bf9844c600fba444c600fd8734c600fda334c600ff1414c600ff07384600ff14384600ff233846009f88750600fb24484600fd23384600 else 0x84420107c402110a3a10107c40907883a251008022010044010a084610980c40e01882617100c202110808254e8c041f103c08202040401101020112)

def moveIndex8 (i : Nat) : Nat := 0x368130841e22c8aa8a512c14c909d63f63800506521e7a10593d37e074d00072ea004600080800000000b0e000002180066704a41938800048d960242010c761044020802

def liveData7 (i : Nat) : Nat := 0x8201041908000000a1000a1000a10000000041000a100101010200042007001004209147631097d3adcce16e35d90c35a2bd409b4b24518873c1ccc85f28104782d1408c28050047f6488758e0097ecb510a9c011fd9221d538023fb2643ac50047f64c8754a00cbe43aa6a94019ec87589328023fd32c18e30067b249831c6008fecc26438c019dd834c8718026fb2b442c30047f64c87586008fec910eb0c011fd9321d518027db25442630047f648874c600aeec90e698c019ec8720931803b98e6412630047f64c87486008fecc0e690c015f5911cd21803ba8e698a4300567650878ce008deca10eb14017999421e338027732843c670047ea648750600cec43c66a0c013e992a21318023f12ec2263007e49123384600

def moveIndex7 (i : Nat) : Nat := 0x9

def liveData6 (i : Nat) : Nat := 0x21eda2a65831c600

def liveLevels : Nat → Packing
  | 10 => (2,1,6,0,0,6,0,liveData10)
  | 9 => (32,2,6,0,0,11,0,liveData9)
  | 8 => (124,3,6,0,0,12,0,liveData8)
  | 7 => (33,4,6,0,0,9,0,liveData7)
  | 6 => (1,5,6,0,0,0,0,liveData6)
  | _ => emptyPacking

def liveIndex : Nat → Nat → Option (Nat × Nat)
  | 10 => lookupWord 12 38 5 9 5 0 moveIndex10
  | 9 => lookupWord 44 141 6 12 7 1 moveIndex9
  | 8 => lookupWord 16 43 5 11 6 1 moveIndex8
  | 7 => lookupWord 1 2 0 4 0 0 moveIndex7
  | _ => fun _ => none

def orSamples : Array (Bits × Bits) := #[(0x4c0f0303f00e07e0027fc0e1fc01e07fe001fc01ffc000083f00c07f007e007ffffffc3f007f007ff00007f003ffdfe00407f807c01fffc007fffc3fc00fe007fe03fe0000307e001f01fe00001f003fffffffffffc1ff80007fffe00007ffff,0x44050001500003200275d4a15549405d68a0784196c48a800d00402d001020152851ac2b4234104ab12524c240a6c5a1040171014012894001c74c2ad50aa52352816a4540901402840094250445000d2808ce0d6a41da928a54f32460415c2a),
  (0x8ff003fc000ff800038000fe0001ff800001fffe0000000fc000ff80007fff80fc003fc0007fff80000007ffffffe00007f80007ffe003fff801ffc0000fffffffffffffffff80001ffe0000001fffc007f800007ffe0000007fffffffffffff,0xab00264000b500800000016000088000001828600110023c040aa80402a8980952000c00049a290044041148a49000000580000104000a0b010104000415048041604a01926800019aa40802888424004b200501092002010090c4902928144),
  (0xf00003fffff0000003ffff000001fffffffe00000000000fffff0000007fffff00003fffff800000000007fffc007ffff8000007fffffc000001fffffff00007fffc0000003fffffe0000000001ffffff80000007fffffffff807ffffff80000,0xf000919bfab0021112c66600021176e65dcc11010426230c2b9c00009055365b22413731e48000602989066b10823179a0044445aabb2c110480668c6610000599c8415182186758c00001314116b4abb104a4866325635ce3005196b4652808),
  (0xfffffc000000000003fffffffffe0000000000000000000fffffffffff80000000003ffffffffffffffff80000007ffffffffff8000000000001fffffffffff800000000003fffffffffffffffe00000000000007fffffffffff800000000000,0x457040000000000411898ec646200080000201418800c204001008e02800000000008420b1e0703c0067000000446020d1199880000000421059970986d8672000188060c2318230e0c98060e000000002008181c188c031c6e060040801070),
  (0xfffffffffffffffffc00000000000000000000000000000fffffffffffffffffffffc000000000000000000000007ffffffffffffffffffffffe00000000000000000000003fffffffffffffffffffffffffffff800000000000000000000000,0xbb28dbdeacdfbc5d9800000000000400110902002038300eb2eeb340e567c762c78602008000c0000e08800c0308385c326606163ccc32b9c61802002000080401100198100c61cc10f161d87018df32c7c730e0000000642000081887062180),
  (0x0,0x0),
  (0xfffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000007fffffffffffffffffffffffffffffffffffffffffffffc00000000000000000000000000000000000000000000000000000,0x54461d10c0e42061e39f1fc8787c670f81f03c183f003fc00008000806000400000400000c100403000f000000007f8fc787e7e7cf0fc31e07e1e3bf3f8e0f87e1e1f01fe00000700000801f8000180302003f002020f007c0701000f8003e00),
  (0x0,0x0),
  (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0xab88e2e30f09c79e00602011838198701e01c3e1c03fc00f3cf0fc70f879f87cfbf833bcf060f87c0ff0078fe3f0001000000000301000200000000000001000000201e00000418000c101e00000e03c0407c000400100780000601f0007c000)]

def orSymmetries : Array (List Nat) := #[[],[64,49,134],[96,132],[128,49,100]]

def orCols : IndexTree ColumnInfo := (.fork 29 (.fork 14 (.fork 7 (.fork 3 (.leaf [(0,0,351,0,11),(0,1,332,18,6),(1,0,350,0,8)]) (.leaf [(2,0,349,0,7),(2,1,332,16,5),(4,0,347,0,8),(5,0,346,0,5)])) (.fork 3 (.leaf [(7,0,344,0,4),(9,0,326,0,4),(12,0,339,0,5)]) (.leaf [(1,16,326,8,5),(16,1,332,2,5),(17,0,334,0,7),(18,1,332,0,4)]))) (.fork 7 (.fork 3 (.leaf [(9,16,326,0,4),(0,64,29,258,6),(65,0,286,0,5)]) (.leaf [(2,64,29,256,5),(70,0,281,0,4),(0,256,23,72,6),(257,0,94,0,5)])) (.fork 4 (.leaf [(8,256,23,64,5),(320,0,31,0,7),(258,64,29,0,4),(322,0,29,0,4)]) (.leaf [(324,0,27,0,4),(72,256,23,0,4),(328,0,23,0,4),(4098,0,2397,0,7)])))) (.fork 14 (.fork 7 (.fork 3 (.leaf [(4100,0,2395,0,8),(4108,0,2387,0,5),(4096,64,2077,258,6)]) (.leaf [(4098,64,2077,256,5),(4166,0,2329,0,4),(4096,256,2071,72,6),(4352,0,2143,0,8)])) (.fork 3 (.leaf [(4104,256,2071,64,5),(4416,0,2079,0,7),(4354,64,2077,0,4)]) (.leaf [(4420,0,2075,0,4),(4168,256,2071,0,4),(4424,0,2071,0,4),(16386,0,8541,0,8)]))) (.fork 7 (.fork 3 (.leaf [(16388,0,8539,0,9),(16390,0,8537,0,6),(16396,0,8531,0,6)]) (.leaf [(16404,0,8523,0,6),(16408,0,8519,0,6),(16384,64,8221,258,7),(16386,64,8221,256,6)])) (.fork 4 (.leaf [(16454,0,8473,0,5),(16384,256,8215,72,7),(16392,256,8215,64,6),(16640,64,8221,2,6)]) (.leaf [(16704,0,8223,0,8),(16642,64,8221,0,5),(16708,0,8219,0,5),(16456,256,8215,0,5)])))))

def orForest : Forest := ⟨2399,10,fun j => orSamples[j]?.getD (0,0),orCols,orSymmetries,liveLevels,liveIndex⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem orGeometry : graphValid orForest (boundsBefore entries2299) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem allAt10 : block orForest 10 0 2 = true := by
  apply wideBlock (depth:=0)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem allAt9 : block orForest 9 0 32 = true := by
  apply wideBlock (depth:=3)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem allAt8 : block orForest 8 0 124 = true := by
  apply wideBlock (depth:=5)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem allAt7 : block orForest 7 0 33 = true := by
  apply wideBlock (depth:=4)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem allAt6 : block orForest 6 0 1 = true := by
  apply wideBlock (depth:=0)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

theorem orTables : checkedTables orForest 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block orForest 0 0 0 = true)
  · exact (rfl : block orForest 1 0 0 = true)
  · exact (rfl : block orForest 2 0 0 = true)
  · exact (rfl : block orForest 3 0 0 = true)
  · exact (rfl : block orForest 4 0 0 = true)
  · exact (rfl : block orForest 5 0 0 = true)
  · exact allAt6
  · exact allAt7
  · exact allAt8
  · exact allAt9
  · exact allAt10

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withoutPositive : Impossible (graphGoal 351) 10 (minusZero 351).toFinset := by
  exact root_index (g:=orForest) (before_sound _ sound2299) orGeometry orTables
    (k:=10) (by decide) (i:=0) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withPositive : Impossible (graphGoal 351) 10 (vars 2399).toFinset := by
  exact root_index (g:=orForest) (before_sound _ sound2299) orGeometry orTables
    (k:=10) (by decide) (i:=1) (by decide +kernel)

end PEqualNP.Outside.L_meta_5006.Signed351
namespace PEqualNP.Outside.L_meta_5006
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem signedBound351 : Lower (vars 2399) (graphGoal 2399) 11 :=
  signedInduced (m:=351) (k:=10) (hints:=12901687553) (before_sound _ valid383 351)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) Signed351.withoutPositive Signed351.withPositive

def entries2399 := extendKnown entries2299 11 [(2399,[]),(2415,[84,131,98]),(2479,[98,118,81,130,50,65]),(2493,[118,130,81])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound2399 : Known entries2399 := extendKnown_ok sound2299 signedBound351 (by decide +kernel)
end PEqualNP.Outside.L_meta_5006
namespace PEqualNP.Outside.L_meta_5006.Signed381
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withoutPositive : Impossible (graphGoal 381) 8 (minusZero 381).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=2429) (4100,0,2425,0,8) _ (before_sound _ sound2399) (by decide +kernel))
    [] (pool:=(vars (poolMask 2429 (4100,0,2425,0,8)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withPositive : Impossible (graphGoal 381) 8 (vars 2429).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=2429) (4100,0,2425,0,8) _ (before_sound _ sound2399) (by decide +kernel))
    [] (pool:=(vars (poolMask 2429 (4100,0,2425,0,8)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end PEqualNP.Outside.L_meta_5006.Signed381
namespace PEqualNP.Outside.L_meta_5006
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem signedBound381 : Lower (vars 2429) (graphGoal 2429) 9 :=
  signedInduced (m:=381) (k:=8) (hints:=13019128580) (before_sound _ valid383 381)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) Signed381.withoutPositive Signed381.withPositive

def entries2429 := extendKnown entries2399 9 [(2429,[])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound2429 : Known entries2429 := extendKnown_ok sound2399 signedBound381 (by decide +kernel)
end PEqualNP.Outside.L_meta_5006
namespace PEqualNP.Outside.L_meta_5006.Signed471
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withoutPositive : Impossible (graphGoal 471) 7 (minusZero 471).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=2519) (4112,0,2503,0,7) _ (before_sound _ sound2429) (by decide +kernel))
    [] (pool:=(vars (poolMask 2519 (4112,0,2503,0,7)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withPositive : Impossible (graphGoal 471) 7 (vars 2519).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=2519) (1,16,454,0,5) _ (before_sound _ sound2429) (by decide +kernel))
    [] (pool:=(vars (poolMask 2519 (1,16,454,0,5)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end PEqualNP.Outside.L_meta_5006.Signed471
namespace PEqualNP.Outside.L_meta_5006
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem signedBound471 : Lower (vars 2519) (graphGoal 2519) 8 :=
  signedInduced (m:=471) (k:=7) (hints:=26323452161) (before_sound _ valid383 471)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) Signed471.withoutPositive Signed471.withPositive

def entries2519 := extendKnown entries2429 8 [(2549,[134,81,114,49])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound2519 : Known entries2519 := extendKnown_ok sound2429 signedBound471 (by decide +kernel)
end PEqualNP.Outside.L_meta_5006
namespace PEqualNP.Outside.L_meta_5006.Signed487
open PEqualNP.CircuitLowerBounds

def liveData10 (i : Nat) : Nat := 0x121f02300054b05a5a00ff803fa00

def moveIndex10 (i : Nat) : Nat := 0x8e80000000a285d0000000000af64f01ba65a58e801a0000000000000009632e4a625fe0f828054401515000005680000000ab8006a90b5948dc1c880a3ed99c00003388d40000001f08c56303000

def liveData9 (i : Nat) : Nat := 0x221623061c271f248149304030e13920fc0a04882907e04a3b493f024011612251d0635200938f831480a04a920418d483f023070fa401101706395d24f944094cc04b86545e5864025a901312e200e014d8569600a604c4b8b00510353615a6ace6e9061c79dba615684acfe384b423c620d400ffac5007fd42803fea8c01ff4c600ff863007fd21803ff08c01fb88a00bf8e3007f611803fc90401fe44200ff0e3007f931803fd08c01fc84600

def moveIndex9 (i : Nat) : Nat := 0x3810f40e886ec645e000000000265000025292d884a2a8a2018b800080c000565204061b68aacbc00101df86a80ca6c000000104ac7e000a4b000382800089ed872026e9d712001f84301a84d703640dc3ac8a2ed0851921913f6da01280bf0cb80503062991ae8f482e4b4000709a809c10e99000106963215938dba78c11601185a72fb12700308f66249205dd6ca561e3060a947572a68f921183c00042d00002a7a3943cd9de8e3854839420f83907d633905000237943b00f20c6c3fa37616729ac0ae2b311020028001004cc92160418802102110800104a63830a0c0830004040802600202022c515

def liveData8 (i : Nat) : Nat := 0x43620086c410098a0210084480410843e212040f1f1004281080429e08044a205040218f83440303884810101c41a4086071f4086060001c04170810260f05c042050084260b0c04202503040401084c12810810021f104c120e0c204a1505815024c0042611048188020800210001819030c0210010e1027c20c00400010602102a6022000700240840819488002080129d86b4780d86b472ce4e4858ef1a62943b85b05a043fa7d8f79e3bb9756e51beb6f6b0ce18c31361cb9559aa54e69712722541c770d99a52f85b8b495b2ac5449892323c464859061f03cc728e01b63345f8ba146278438790e81742c04a08a10010000bfe8858a00bfe8850a00dfd651c600dfd831c600bfe8854600bfd8654600f7d6554600f7d5454600dfc7354600bfe884c600dfc874c600dfc714c600ff5514c600bfd840c600bfd8648600bfd8448600bfd8348600dfc7348600fed4248600dfc73846009fc8758a009fc8750a00eee6688a00fae4488a009fe881c6009fd851c600d7e551c6009fd831c6009fd821c600dee221c6009fc8754600f7950546009fc874c600df4714c600bf9800c6009fc8748600df48784600f765584600df47384600fd63384600fe622846009fc8784600df47184600efa6648200fba4448200df87348200fda3348200bf98544200f7a5544200bf98344200fda3344200fea2244200df87144200ff13144200ff21144200bf9831c600fda331c600bfa884c600bf8874c600df8874c600ff0714c600ff08784600bf88784600fda3384600ff131846009f8874c600fd23384600

def moveIndex8 (i : Nat) : Nat := 0x3ccf079e85538970100182081b9c000603456b332e03d06f93c215fb4b253c3067a8dfa60000000010400000186000b3b0164700081385708b82f3402d4331405d05031423001502

def liveData7 (i : Nat) : Nat := 0x281aa42078420080000682003c206040003c200000000000000210001e1d7cdaf9173554b4137190ef0d2c8bea0968c82786e645a50463c1e140a011fd9121d628023fb2643a850047f6448750a00cbec2aca38c011fe9960c718023fb2ac18e30047f25e88546009f6c9510a8c011fd9321d518023f92ec32a30055f25d6554600abe4baa8a8c011fd981cd51802beb2239aa30047f25e884c6008ff4c90e98c011fd9521d31802beb2a38a630057d25d514c600eea39aa298c011fd9321d218023f92ec32430047f25d84486008fe4bb0690c015ec97509218033f53243a63004fea64874c600afd4c90e98c011f89760d108023f53243a630057c25d3184600

def moveIndex7 (i : Nat) : Nat := 0xf0

def liveData6 (i : Nat) : Nat := 0x21faaa25d8344200

def liveLevels : Nat → Packing
  | 10 => (2,1,6,0,0,6,0,liveData10)
  | 9 => (16,2,6,0,0,10,0,liveData9)
  | 8 => (67,3,6,0,0,11,0,liveData8)
  | 7 => (31,4,6,0,0,8,0,liveData7)
  | 6 => (1,5,6,0,0,0,0,liveData6)
  | _ => emptyPacking

def liveIndex : Nat → Nat → Option (Nat × Nat)
  | 10 => lookupWord 29 57 2 10 4 2 moveIndex10
  | 9 => lookupWord 41 123 7 13 7 2 moveIndex9
  | 8 => lookupWord 17 46 4 11 5 2 moveIndex8
  | 7 => lookupWord 1 2 0 4 0 0 moveIndex7
  | _ => fun _ => none

def orSamples : Array (Bits × Bits) := #[(0x631f010ff01fc01fe00338381fc00ff007fc001ff07e0407f803c0ff801f807fc0000fc0fc00f00ffe0001ff007fe0f01c0fe003e01ff8003f0031f007f01ffc0001fe01fff00001fffe0ffffc01ffffc03fc0000f007ffffffffff80001ffff,0x411e010b540ad116a90138120a928555055d404960460004480280b5c507087754a28a40ae82a00ea6a520cc483540d81a0d7002701db90527200194251019095220dc016b554910b24a0945a42198b648165a14210054ac5d98974b2410daca),
  (0x83e001f0001fffe00003c03fe0000ffff800001fff8007f80003ff00001fff8000000fff0000fff0000001ffffffff001ff00003ffe000003ffffe0007ffe0000001fffe00000001fffff000fffe003fffffffffffff801fc00007ffffffffff,0x2c080b0001424601002842cf0240828680204128400071800091000001850802100249200085c501108091191488900049004108420004008c8da0002aea202040923621008102544801000090a0000a168a48144890012a002209450452414),
  (0xfc0001ffffe000000003ffc000000fffffffffe03ffff8000003ffffffe0000000000fffffff0000000001ffff803fffe0000003ffffffffc0003ffff80000000001fffffffffffe001fffff0000003fffc000000fffffe0000007fffffe0000,0xe8000102764000000010114000000191818461e03af7b0810092edd96e422022060b096cdb3300840430b06662112632a00001404148d21640002451b000002040b08c0c42e183d8001d65960080521b1c84085889726ec00854c5618e984188),
  (0x0,0x0),
  (0x0,0x0),
  (0xfffffe00000000000003fffffffff000000000003ffffffffffc00000000000000000ffffffffffffffffe0000003ffffffffffc0000000000003ffffffffffffffe000000000000001fffffffffffc0000000000ffffffffffff80000000000,0xac010600000000000020004820003000000000801318d8d190dc080008000200000c218f103c11e05800dc000000252324508198000000180002b661c0c0c07000dc0008008002600011b61848cc6300110000610e5c0b030067008008e00110),
  (0xfffffffffffffffffffc000000000000000000003ffffffffffffffffffffffffffff000000000000000000000003fffffffffffffffffffffffc000000000000000000000000000001ffffffffffffffffffffff00000000000000000000000,0xbc251401e163418321b800000000200000100900139ce0e1e1e0ce1e0f838307803fc008002001006001e000000036bfd366d9e37986e19fb233000100000c4018e0480023006380181fcfe0f2f17c3c1e17037e00600c04017801002f0009e0),
  (0xffffffffffffffffffffffffffffffffffffffffc0000000000000000000000000000000000000000000000000003fffffffffffffffffffffffffffffffffffffffffffffffffffffe000000000000000000000000000000000000000000000,0x13b6d8dd899bb9dbddc3eeb75cf8ce2e361b8e1cc00002000500000000104044383000000000880881c10180806018cc1b8f1e039e1705e03cbc098e070b1f839f0171b1bc0e7c019f0008008301802020183380000000183180000630018e00),
  (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x43d8e1ee0e1c3e1c1e03f7379f3f0fcfc7e3f01f2c610706060330e0701c7c783fc00e30e3c0ee0f01fe01f8fc7e0000000800000018060000c00108040c1003e00181c1c00f8001e00000000000000000203c00008070003e000607c001f000)]

def orSymmetries : Array (List Nat) := #[[],[98,135],[81,114,134],[81,130,118]]

def orCols : IndexTree ColumnInfo := (.fork 26 (.fork 13 (.fork 6 (.fork 3 (.leaf [(0,0,487,0,11),(1,0,486,0,8),(3,0,484,0,5)]) (.leaf [(0,4,353,130,6),(5,0,482,0,5),(2,4,353,128,5)])) (.fork 3 (.leaf [(7,0,480,0,4),(32,0,455,0,7),(33,0,454,0,5)]) (.leaf [(0,64,165,258,6),(65,0,422,0,5),(2,64,165,256,5),(128,0,359,0,8)]))) (.fork 6 (.fork 3 (.leaf [(129,0,358,0,5),(128,4,353,2,5),(132,0,355,0,7)]) (.leaf [(130,4,353,0,4),(134,0,353,0,4),(161,0,326,0,4)])) (.fork 3 (.leaf [(0,256,135,96,6),(260,0,227,0,5),(32,256,135,64,5)]) (.leaf [(289,0,198,0,4),(258,64,165,0,4),(324,0,163,0,4),(352,0,135,0,4)])))) (.fork 13 (.fork 6 (.fork 3 (.leaf [(388,0,99,0,4),(4096,4,2401,130,6),(4098,4,2401,128,5)]) (.leaf [(4128,0,2503,0,7),(4224,0,2407,0,8),(4228,0,2403,0,7)])) (.fork 3 (.leaf [(4226,4,2401,0,4),(4352,0,2279,0,8),(4356,0,2275,0,5)]) (.leaf [(4128,256,2183,64,5),(4416,0,2215,0,7),(4418,0,2213,0,4),(4420,0,2211,0,4)]))) (.fork 6 (.fork 3 (.leaf [(16384,4,8545,130,7),(16386,4,8545,128,6),(16416,0,8647,0,8)]) (.leaf [(16384,64,8357,258,7),(16386,64,8357,256,6),(16512,4,8545,2,6)])) (.fork 3 (.leaf [(16516,0,8547,0,8),(16514,4,8545,0,5),(16416,256,8327,64,6)]) (.leaf [(16704,0,8359,0,8),(16642,64,8357,0,5),(16708,0,8355,0,5),(16736,0,8327,0,5)])))))

def orForest : Forest := ⟨2535,10,fun j => orSamples[j]?.getD (0,0),orCols,orSymmetries,liveLevels,liveIndex⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem orGeometry : graphValid orForest (boundsBefore entries2519) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem allAt10 : block orForest 10 0 2 = true := by
  apply wideBlock (depth:=0)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem allAt9 : block orForest 9 0 16 = true := by
  apply wideBlock (depth:=2)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem allAt8 : block orForest 8 0 67 = true := by
  apply wideBlock (depth:=5)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem allAt7 : block orForest 7 0 31 = true := by
  apply wideBlock (depth:=3)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem allAt6 : block orForest 6 0 1 = true := by
  apply wideBlock (depth:=0)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

theorem orTables : checkedTables orForest 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block orForest 0 0 0 = true)
  · exact (rfl : block orForest 1 0 0 = true)
  · exact (rfl : block orForest 2 0 0 = true)
  · exact (rfl : block orForest 3 0 0 = true)
  · exact (rfl : block orForest 4 0 0 = true)
  · exact (rfl : block orForest 5 0 0 = true)
  · exact allAt6
  · exact allAt7
  · exact allAt8
  · exact allAt9
  · exact allAt10

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withoutPositive : Impossible (graphGoal 487) 10 (minusZero 487).toFinset := by
  exact root_index (g:=orForest) (before_sound _ sound2519) orGeometry orTables
    (k:=10) (by decide) (i:=0) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withPositive : Impossible (graphGoal 487) 10 (vars 2535).toFinset := by
  exact root_index (g:=orForest) (before_sound _ sound2519) orGeometry orTables
    (k:=10) (by decide) (i:=1) (by decide +kernel)

end PEqualNP.Outside.L_meta_5006.Signed487
namespace PEqualNP.Outside.L_meta_5006
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem signedBound487 : Lower (vars 2535) (graphGoal 2535) 11 :=
  signedInduced (m:=487) (k:=10) (hints:=22028484865) (before_sound _ valid383 487)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) Signed487.withoutPositive Signed487.withPositive

def entries2535 := extendKnown entries2519 11 [(2535,[])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound2535 : Known entries2535 := extendKnown_ok sound2519 signedBound487 (by decide +kernel)
end PEqualNP.Outside.L_meta_5006
namespace PEqualNP.Outside.L_meta_5006.Signed255
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withoutPositive : Impossible (graphGoal 255) 11 (minusZero 255).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=2303) (4160,0,2239,0,11) _ (before_sound _ sound2535) (by decide +kernel))
    [] (pool:=(vars (poolMask 2303 (4160,0,2239,0,11)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withPositive : Impossible (graphGoal 255) 11 (vars 2303).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=2303) (4160,0,2239,0,11) _ (before_sound _ sound2535) (by decide +kernel))
    [] (pool:=(vars (poolMask 2303 (4160,0,2239,0,11)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end PEqualNP.Outside.L_meta_5006.Signed255
namespace PEqualNP.Outside.L_meta_5006
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem signedBound255 : Lower (vars 2303) (graphGoal 2303) 12 :=
  signedInduced (m:=255) (k:=11) (hints:=553656577) (before_sound _ valid383 255)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) Signed255.withoutPositive Signed255.withPositive

def entries2303 := extendKnown entries2535 12 [(2303,[]),(2555,[99,81,115,130,65])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound2303 : Known entries2303 := extendKnown_ok sound2535 signedBound255 (by decide +kernel)
end PEqualNP.Outside.L_meta_5006
namespace PEqualNP.Outside.L_meta_5006.Signed383
open PEqualNP.CircuitLowerBounds

def liveData12 (i : Nat) : Nat := 0x7b369a8b2542d9344883d9b4b64d2c950ee78803ff007fa00

def moveIndex12 (i : Nat) : Nat := 0x3c26769e0032f00000c4398004a74180032b5f138a144eeeb108b250018a9e416985d6000068a400000004830a6e8e5cad62000002e3e3a8d48ad620c85290a282c8

def liveData11 (i : Nat) : Nat := 0x1f00696c52090a260fc3d4d4010d828cb32dca83449b1234021be021a05728be260043e0fa37c052dcb22ba85d09042f8de3e804264a926cb72c8ae17ac021f07e01a029645517502f8a2011063780d2cca9120baa17c161305101a5b9342440be2880f2dc9a028ba1220330105196e4d090c014b72c8ae49ee6a9524d9665b890574066064b7268ba121a599502417493dcdb2dc9b2cca9120ba81b47b1a802934529525b9647f50d43d8db2dc9b2cca8120ba996e829d46e090a010fd268d935108399e7b9b4770908010de3d8fb2c8ea399e5b9d659a10732cf736cb32a0ee5da392b09daab2347a64c60816ed9bab485e6ac942a3038e5a0988e61721b81b800ffc83803ff5ce00ffc73803ff8ce00ffc81803ff4c600ffc31803ff84600ffd30803ff44200bfd83802ff20e00fde33802ff60600bfc81803fd84600ff930803fe44200ff983803fe5ce00ff981803fe4c600fda33803fc84600

def moveIndex11 (i : Nat) : Nat := 0x5893306ea4ae247f838005f446b4ab218d8131617a8878000a0080003c14288804a0a1c80005065c0058546c463988a044e5c80001924d2b500c6c24119300004166881c948000065780004c57104cc0f280f000070c1455604bd88252be000101df8404047465c000781c62e304ec4a04123f0eac1f94082851000261264bc2879704025d4c883f57212200010330000000080f6035702522140000427700f20b921b902fd12a508a0002cb7a02bd0238669c109833221ca02d4280000000000b5840000020f100a4892800000006542438700eb02ae1bc00059690001a5ed040d884f0b0000283618080001614e84a185a308624f0803202e8069606c88cc07a131ca26ac33b130107fe23d447207f280184bfc2ba0077228a030825114de06de6500007890b0ad22284abc874713c052bc30a1707031e427c292824c073a26c435a01d609861de001d05de07420a9c32209d110fbd02c36f817c13344e50138863d1386109c23898f70d2258209ba9922097c50d402d809b05805a102db08680e33101c4f814c101481ee09fa832801a004f81a895bc025260143e716782c600680004016e033e1d9445e952709e218881f1995f12d444d034711b22a984008c63089127ac1cd4bcd892308c221700a684476a1e136c41d144612b007c8a2c030e0fa0156082f0548000c237c20a3540c107180da22040004326000910401d010e44d0730001070e28001063d334186c2011003e00140468a00001811ed81070c0818108200020400083229c70200381870400000

def liveData10 (i : Nat) : Nat := (if i < 1 then 0x185fc97a05d3971d5c356a559d164e58495cb55e553d545d4db52a948450f53f64e653684d093274c052e64b2d2bb4a8127a497d22347c91d746f1196459513f44390e842dd09c42050454050ff93ef4fa23e1cf773d70f363c6cf003b68ea939e0e4738b0e113780dc5367cd4d33ecca9315cc262e74b6c2cecb0a2b64a872958a2526f499724bc8e822dc87020fc7f81f1c73e1bb06a519a462217c45c015b855313d84c511f845810443d50e6433c0c00298094422b08141d406b817d053012603d40c4024c05700c4000fff4cae7007ff26173803ffb22b9c01ffc915ce00ffec82e7007ff21e33803ffae640c01ffc7320600fff19903007ff25d31803ff90e98c01ffe774c600ffeb9a63007ff9dc31803ffae708c01ffc7384600fff19c23007ff9dd30803ffae698401ffd714c200ffe98a61007ff5cd10803ff8e688401ffe3344200bfecb907006ff21c83802ffb2241c017fe995ce00dfecc2e7005ff261738037f930b9c01bfd835ce00bfec88e7005ff64073803fb93119c01fdc978ce00fee43c67007f7246338037fb0f19c01bfc878ce00dfeb9b03006ff1cd818037fc66c0c01bfd7320600dfe39903006ff8cc81802ffb2640c01bfc8320600fef19903005ffa65318037fb3098c017fc984c600dfe4c263005ff65d318037fb0e98c01bfc874c600eff3ba63006ff60d31803fb90698c01fde334c600dfec0a63007fd5c531802ffb2e18c01bfd870c600dfe438630077f9dc31802ffb2018c01ff49884600ffa49c23007fd20e11803feae708c01ff47384600ffb19c23006ff60e118037f90708c01fde3384600ffc48a61007fe20530803ff2e298401ffa114c200bff4ca61005ff65d308037f90e98401dfe774c200fef19a61006ff20530803fba6298401ff6114c200ffcb8261007fea6510803ff32688401ff89344200ffc41a21007fe5cd10803ff0e688401ffa3344200ffc98a21005ffa6510802ffb2688401bfc8344200fef19a21007fd84510803ff26088401ff97360600ffcc3a63004ff65c838027fb2241c013fd9020e00bbeca907005fe640838027f930b9c017bd941ce00bf6c90e7005fd64473802ff32039c01bdc988ce00deec3c67006f721e33803bbcef19c01fd8908ce009fe4c467006f760e338037bc66c0c013fd9320600def19903004ff64081802ff32040c013fc984c600dee41a63005df65431802ff32018c01bf49884600dfac1c23006fd20e11803fac6708c01ff090846009fe4c423006fd60611802ff32e98401bf9874c200efd3ba61007f68cd30803fb26298401ff2114c200bfcc9a21007f68cd10803fe422884017fa995ce00bfc4c2e7007f661e33803fb466c0c017fa994c600bfc4c263005fe65d31803bf4ee98c01ff1714c600ff8c1c23007fc5ce118026fb2a41c01fd23384600 else (if i < 2 then 0x630060a504c601e2600180440a60140b00120010a601c0b100284c0c41eb2d85284874ce0e0128c3600200c0bc818828e590fd96f2a03cc9a0bc030690c8891a82102007cb68780b9b2de4d0d880812942806c00212c1d95042040580fd0f03a30020de1942a82f285100206461b501090107c4be30f8808480926091400c02001c3e84243c06500cc3000c0960e8a00f2de4d06d1761218010034d006480f01a80c8b90780c981900100402f2ce5485c70029a00d0c0604006800b2cc2a03470be1842984d0d9090179c020340600949008200830e540981bf2c8580d80bd20d726a2405e40d8014128c0664d0d80401794360630cc1741202f305f4511343e80c4480bcf1340100548c0e8b9360107d1c4d06a0291202f286c00c8901790364020a4306a0f22680c4480bcc1443e07d0c619817982f0620f59640101f0aa17500081ec5c03248a2104128e0144c104c00e09461a901090125112020c4d4042098809288d01251104000a84e2e82028368b883812920144c16540d820021b0380c41a5bca81f49800288701c020da0040c902ec2404a38a80dd1f825245182620a304c41022a00b45c094a14402c0204a48a304c41b02f851048094a00826092a64d1600086c4a220d81fb000c01251106c4a220d81b4278e0106a002080817c2b82f04a406d96d07025244c804209800841b02881309840fd008400b26879180406d9672dc1e08a15ce0cc01005cb396c0f85738330080d40365b03c15ce9643e006cb611c290243e5b0ea0903f90060330081e80106cca99372ce5b07609581bc088680ae40d605834057206f00a1a02b90350060d015c88cd022020f996f2c8573e4d41596d12100664dca89a081f03ee6a8a396f2ce544d1935396d0f07f18334040103e035cb396c0f8574a33cb61f115052448686796f26c242033cb3952120390ba60199672a45d2033018004038240ba60fa1f01205d20330080300106c00b96f26e59ca80c012b00800200d96f2c82b0ae70b41f04283c0aa174c1e83de590aa174a8cd06659ca88902e9919e5bc9a89080132de594ae4cf69462665bcb3953269c2ea24103301880800e59ca80982ea119a0c0ba89081f8408540eb9643f9b2d81e0fe38db96f2ce5410c1fcd96f2cc750aa1fca1b72d86acb21fcb1b601083cb71472ce4dca880df96c39e590fe58d50083e07dcb79372cc5dca890051ee36e59ca8174d9344407f1e4d11020068093ac7310e40fb1de120c3ce590fa1d081e83ce590e84cb31dc3f8e36e598ee1fc81b7268870fe44f69b63ba242202c011a942273281ecb615c79ef2cc754e64828209081aa0448079ff87f49fac7e19f557cbdefe7b35ea77a05e5b78d5e047779d9775c5d40743dcde7231c6670d5ba16d69b1e6b89a9b697da3968799f867759c2659592963898b161a98 else 0x1442f8500c4440414b6934280d010070c430c4005120c0100102c300a006010c0b00500230040040b0c30e4d00a14c802403005185f89a13030900284c0a0148801c3003c180600b130614c02806180500c14c6058300018264002146098c0b0604b60160980))

def moveIndex10 (i : Nat) : Nat := 0x8538000c230268400039aa604f42234ce0000400a827c8be00a840f982bdc41104d70423d8b8222091f0544107859d0b70000a414000485ba0e38077c5a505550fc65f4089c85ee11941ff49060347048826a43b6014416182514a4d01e822904ff44e4012482320d6c3360360162a0ba354e0187152c03080308a1108d42b801ef121e116806720fa1b0113c2420824a1ab9543a0b144ee91130d084f2407308e504aa29244b600f202e219501688112358c69f81d304a60a68465c118030202dc0e6c5c31a800a92e8601ff16c9008a6760188152a86e8042042e848d0b96034020204734e78236c046045a12a66cacb7b195000180bd456a09952d2e056cae01407864b111ccfa0ab3145a0000005801c0c7402800020a3f09ee24cc591809f00521e80007842000000a105d39846108f0cf845097b0000e224000285fc13000014bc72621100000142ba8aaa0e6e578d1288b9000042180000000625161befa20000804400f2c99a159000000024561870b00f2644caed00b614b626c03a987bd07d060d8305851000084d6849002bc026a080437303892ace1f449a081aa0d4612f40d9970d10300cc435985270ada07c49df0b57064821d49d2037a25da1e543c38839120000284b8000d3270681c32157e503821a40006850000000000338000414de130000300362ca000042c00009252d19083629b7c0c441674d7c0b6d2f30280c27583b730a000245dc92dc04d61dec3a000000e5e168036e02990c2617504780435e04f1aa8300004a0020120d40129c321000000a9f0e383010c14c013a14d8e0400b810028a811a5019b0c0c7800230502004018c200000276000270e0018100140000054285080010700040030430002

def liveData9 (i : Nat) : Nat := (if i < 1 then 0x7344200bfb6887344200cdfaa99520e00cdf69d9520e00cdf29d9520e00cdf6859520e00cdf2859520e00cdf6819520e00af768c8720e009dfaa99520e00cdf21d9520e00dde6819520e00cf78cc985ce008ff684985ce009fdaa9911ce00cfd6a1911ce00cfd2a1911ce00dfc681911ce008ff2a1911ce00af769c988ce00ee7690988ce00af7684988ce00be7690988ce00af72a5878ce00af7684878ce00be7690878ce00e77262778ce00be7690918ce00bf6680918ce00bf6684908ce00cef690988ce008ff2a5878ce00aef690878ce00af768c878ce00e779dd838ce008ff2a57360600aef6907360600afb6887360600afd6847360600afe6807360600cf72a63360600e779de33606008ffaa993206008ff6a573206008ff6a47320600aef6907320600afb6887320600afd6847320600afe6807320600cf765e3320600e779de3320600cf764e3320600cf78cd9020600adf6948320600cf764c8320600afd6848320600df68cd90206008ff2a2994c6009fb68a994c6008ffaa8984c6008ff69c984c6008ff2a1974c6008ff2a5874c6008ff6a4874c600aef690874c600afd684874c600c7f262774c600cf7a64834c600e779dc834c600af72a2334c600cf7262334c600ef520d714c6008ff2a1970c6008ff6a4870c600c7f65c870c600aef690870c6009dfaa9950c600cdf6a1950c600cdf61d950c600cdf21d950c600d5f9dd950c600dde681950c600cfe61d900c600d7e9dd900c600afd68c9884600bbd6989384600bfc6809384600afd2a58384600afd69c8384600afd6808384600bdd6948384600bfc6808384600afd2a17384600bed6907384600bf96887384600bfc6807384600ef52a23384600ef52623384600ef561e3384600ef521e3384600f759de3384600ff42823384600afd2a23384600ef560e3384600bfc68c9084600ff48cc90846008ff68c98846008ff2a58384600adf6948384600afd6848384600ef54c48384600cf72623384600ef58cd8184600bde694914c200dfc2a6114c200dfc65e114c200efc61e114c200f7c9de114c200ff428e114c200ff48ce114c2009fe2a6114c200ff44c6114c2009ef692994c2008ff2a1974c200aef690874c200af768c874c200afe680874c200af768c814c200df664c9344200bde6948344200bfc68483442009fe6a47344200bee6907344200bfa6887344200bfc6847344200f769de3344200afe2a13144200dfc64e1144200ff48ce11442008ff2a193442008ff6a48344200adf6948344200afd68483442009fe684985ce00f769de33606009fe2a1974c600d7e262774c600bfcaa97384600bfc2a17384600ff461e33846008dfaa99520e00ae7690988ce00ae7690878ce00bf2688908ce008ef690988ce00add69483846009fa68a994c600f749de3384600 else (if i < 2 then 0x64402043989a00a00c500601910308036268c0cc004406810050381028008080081784008006200700110038018008c13820180022016228c5400120008038814c044409c02c201b02510258110810c964084094803e07c200604a01a180a81380a0c10c094403c1043038025181205934200604a2051082300c880400bc5c00100c005025180b0402c202c100d0805840cc202610026040000100f100580c880d406440661a08082181c0128c118064408c0322046019102300c8802c2001002f102300c0178c0300400bc6092034204901a1008017881000c008c685410205040082068060046300102f101584005206e04a3061e5905602f202300d080a00900bc600a04a200501a10040120178f1341200e8601989a05e3a4d080604030200c1a4d081a017881000e0094608007004a3041025102480c88130203e07c201d02a019182001c0128c1303c00100708001c20a210001840302426101e092a0713420a210510828840062808000de10510b0404950200440201001810080d80c00946018100c0826041ca8102120418a8102388780020d4100d025102181c0128c0540580946000074200c025100001d08000218020f00078003c00125108000428e610002812881180600e86078062046300002d1002840002100008ea1e5b857172df2c82b8f9349a040fa0f043c0e84e59039e5b0250572f2d92b881f41db9641c89c00d094e638e1c69a31316c8a7c4ca22b0f8867c2ca12b084839c15a072ff87edbec9f2af847b3bd29e5af10779bb29d72e9c733b929c5ae106f9b759b42d846adb4c9a2ad0466db329972c9c645b1b98a2c4060bb0197eabe45e9af09762ba05cdae2970ab805b1ad19652b18583ab79582aa4543a9a94b2a5451ba8393ca9c84d5a6392ca9544a7a4f925a904473a3591a28a8439a15905a8103f99f28f427783b39d58e8a7343919c18dba6b434b99e8cd264c31197e8bd25d82e39708b625a02cd9628af25682ab9518a6a52428994089fa4f827393889ba4cc25d92a893249423b91688624202078ff87f23e81f18f4879a3bc1db8e9872a3841b38cf862a2f816d8af85722a814b8a184ea264129893847a22c11388283c21b80cd862830a1740b785a82ca15409b84381e20bc03d81780520009ffaa99720e00aff684985ce00aff2a1915ce00cff261915ce00aff684878ce00affaa97360600affaa97320600cff5cd9020600cff1cd9020600cff8cd9020600aff69c8320600bef6907320600bfb68873206009ff69e994c600bef690974c600aff680874c600bef690874c600aff2a2774c600cff262774c600ef79dc834c600aff2a1734c600cff261734c6009ffaa9970c600aff69c8384600cff2617384600cff2607384600bfb6887384600cff2623384600aff69c814c200aff69c8344200bef690 else 0x61080181b0814000454b749a200c035100100308014010400200e200c0030011806003880140104022101608010308814c0))

def moveIndex9 (i : Nat) : Nat := 0x206ba309a005281219a29000399609a82f954c018a48903a339685d88000000081d80507000200a83a08b0272a486204c1080020308400786812a44430420

def liveData8 (i : Nat) : Nat := 0x389a10009420008040014080024100001610000000000550dfd6d44b48bfbd3431a8a6239a981593108e0b890053edb21cd902060096fb6a544ee98c018fb261a21ce1180293edb14eca90700533db429d9520e00a6db6453b2a41c014dd6c4a7654838029bcd814eca90700533db421d9520e00a6bb6643b2a41c012e7aeda421e33802cceda1313bc6700539db42a6336060087db655532640c010fb6c8a8a65318030decbb484386300533db421d950c60096ed76d290708c016e56d0a88ce11802dcada10f19c23004bb5b42a23384600

def liveLevels : Nat → Packing
  | 12 => (2,1,8,0,0,7,0,liveData12)
  | 11 => (24,2,8,0,0,11,0,liveData11)
  | 10 => (160,3,8,0,0,14,0,liveData10)
  | 9 => (188,4,8,0,0,13,0,liveData9)
  | 8 => (21,5,8,0,0,8,0,liveData8)
  | _ => emptyPacking

def liveIndex : Nat → Nat → Option (Nat × Nat)
  | 12 => lookupWord 19 47 3 10 5 1 moveIndex12
  | 11 => lookupWord 81 264 7 15 8 3 moveIndex11
  | 10 => lookupWord 92 294 7 15 8 3 moveIndex10
  | 9 => lookupWord 11 37 5 12 5 3 moveIndex9
  | _ => fun _ => none

def orSamples : Array (Bits × Bits) := #[(0x10200c100800f021e034f03f8038f8000030303802042f0303c000044218ffff9c1c0780001c07e80c081f067000ff07fc03fb807841ff80ff9e00f80e078000043030183ffe1e1fff81fffffffcc601c0000207ffffff83e00007fc0001ffff,0x40008005000a034d42da218f10a8000001002002a4103050c040200281996140592285482800000040010002502a80079805a4055001b9a28aa0a0691600000100002000601488188123038c2008450100229130d8364c041748600530a),
  (0x4030203003003e000700c0003f000000c03fc004383003fc0000087c1f0700e01ff800001ffff0300fe1f9800f03f81ffc0407807e03ff01e000fffffffffff83fc01fc1c3e01f03fe03f0000307fe000003f8070003fc000007ffffffffff,0x10003002003a080100800024020030403ac404381002b41203406c0a0540200b6824068925200000202880030008043800018002008d002000106009280fd83ac00a01436016011603a40a0105ea100a42900640c2640818860121daa0f4),
  (0x9f80403fc013ffc0003800ffffc0000004ffc00007c03ffc0000000f801ff800ffe00000001ff81fc00ffe01fff003ffe00007f8007ffc0001ffff000ff800001fc0001ffe03ffe003fffc000003f800000003fff80003fffffff83ffffe0000,0x9f88403ec111fb8010100076f740854304bec00043402dfc0224440e8015b090db2000588816ca1dc20dde003a5003f7608126e8006d6c4040cccd000fd4544007400214f6108a8002e9ec0b1092600026108167f09928885663103ad2254908),
  (0xe0007fc0001c0000003fff00000000000700000007ffc0000000000fffe00000ffffffffffe0001ffff00001fffffc00000007ffff80000001fffffff00000001fffffe00003fffffc0000000003fffffffffc00000003ffffffffc000000000,0x20003ec002040000002f7e000000202c11000000049740002000298004200000244c718073e0000214b00001c4afbc0001104112eb000000113332df70000384881374800003353bec100100a3208e4cc163180000064373818ce7800c880650),
  (0xffff8000001fffffffc000000000000007fffffff80000000000000fffffffff000000000000001ffffffffe00000000000007fffffffffffe000000000000001ffffffffffc0000000000000003fffffffffffffffffc000000000000000000,0xddfd8004001badf75d4000004400064026ff7f6ee80000800038420b795ec7e2000200608403041ceb0ef3fe080000800222066d04378aeee00040000080640917ac8b3f79b800000020420d0c0331b13a8ce3fdc6e8b0001a11000311318880),
  (0xffffffffffe00000000000000000000007fffffffffffffffffffff000000000000000000000001ffffffffffffffffffffff8000000000000000000000000001ffffffffffffffffffffffffffc000000000000000000000000000000000000,0xf6eefb7753a00100000008000000007035d79388f4df8118384073e00000000000004000c700001f7fdf7bb7ef3acadc57ff804000000008800180044100060e1fff2fdfbdffd9dcb37c73c1cfc000c0030f0040840cc040031e040019c00ce0),
  (0xfffffffffffffffffffffffffffffffff8000000000000000000000000000000000000000000001fffffffffffffffffffffffffffffffffffffffffffffffffe000000000000000000000000000000000000000000000000000000000000000,0xf76f6fb783dd31c461be6f470789387fc00400008002001000007c000000000000000100f800001fbfef9dc57fccf3e79bc3f7f677f9f370fdddfce78de607f002000c0020200000c0408001f000000003f00001000f000203e000001e000f00),
  (0x0,0x0),
  (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x81000082c02ce399e0080b87836c78002282c3703203ee3c3bf800ff39ffefcdb93867f001bf7c000000000000000000000000000000000000000000000780000000000000000000001000e000001003c00018600f000001c000023e001f000)]

def orSymmetries : Array (List Nat) := #[[],[98,131,84],[16,66,101],[16,82,131,100],[48,129,82],[48,129,98,16,66,84],[128,49,100],[128,49,66,16,82,98]]

def orCols : IndexTree ColumnInfo := (.fork 68 (.fork 34 (.fork 17 (.fork 8 (.fork 4 (.leaf [(0,0,383,0,13),(0,1,332,50,7),(1,0,382,0,9),(0,2,312,69,7)]) (.leaf [(2,0,381,0,9),(1,2,312,68,6),(2,1,332,48,6),(3,0,380,0,6)])) (.fork 4 (.leaf [(4,0,379,0,11),(5,0,378,0,7),(6,0,377,0,8),(0,8,99,276,7)]) (.fork 2 (.leaf [(8,0,375,0,9),(9,0,358,0,5)]) (.leaf [(12,0,371,0,8),(13,0,354,0,4),(10,4,369,0,5)])))) (.fork 8 (.fork 4 (.leaf [(1,16,358,8,6),(16,1,332,34,6),(17,0,366,0,8),(18,1,332,32,5)]) (.leaf [(24,0,359,0,8),(9,16,358,0,5),(20,8,99,256,5),(28,0,355,0,7)])) (.fork 4 (.leaf [(13,16,354,0,4),(26,4,353,0,4),(0,32,94,257,7),(32,0,351,0,11)]) (.fork 2 (.leaf [(1,32,94,256,6),(33,0,350,0,8)]) (.leaf [(34,1,332,16,5),(39,0,344,0,4),(44,0,339,0,5)]))))) (.fork 17 (.fork 8 (.fork 4 (.leaf [(17,32,78,256,5),(48,1,332,2,5),(49,0,334,0,7),(50,1,332,0,4)]) (.leaf [(51,0,332,0,4),(41,16,326,0,4),(64,0,319,0,11),(64,2,312,5,6)])) (.fork 4 (.leaf [(66,0,317,0,8),(65,2,312,4,5),(67,0,316,0,5),(68,2,312,1,5)]) (.fork 2 (.leaf [(70,0,313,0,7),(69,2,312,0,4)]) (.leaf [(74,4,305,0,4),(78,0,305,0,4),(0,256,23,104,7)])))) (.fork 8 (.fork 4 (.leaf [(256,0,127,0,9),(8,256,23,96,6),(256,8,99,20,6),(264,0,119,0,6)]) (.leaf [(260,8,99,16,5),(268,0,115,0,5),(272,8,99,4,5),(276,8,99,0,4)])) (.fork 4 (.leaf [(284,0,99,0,4),(257,32,94,0,5),(40,256,23,64,5),(273,32,78,0,4)]) (.fork 2 (.leaf [(320,0,63,0,8),(258,64,61,0,5)]) (.leaf [(262,64,57,0,4),(72,256,23,32,5),(328,0,55,0,5)])))))) (.fork 34 (.fork 17 (.fork 8 (.fork 4 (.leaf [(336,0,47,0,5),(96,256,23,8,5),(352,0,31,0,7),(321,32,30,0,4)]) (.leaf [(353,0,30,0,4),(290,64,29,0,4),(104,256,23,0,4),(360,0,23,0,4)])) (.fork 4 (.leaf [(4098,0,2429,0,9),(4100,0,2427,0,11),(4098,4,2417,8,6),(4102,0,2425,0,8)]) (.fork 2 (.leaf [(4096,8,2147,276,7),(4104,0,2423,0,9)]) (.leaf [(4108,0,2419,0,8),(4106,4,2417,0,5),(4112,0,2415,0,11)])))) (.fork 8 (.fork 4 (.leaf [(4120,0,2407,0,8),(4122,0,2401,0,4),(4124,0,2403,0,7),(4122,4,2401,0,4)]) (.leaf [(4128,0,2399,0,11),(4130,0,2397,0,7),(4160,0,2367,0,11),(4162,0,2365,0,8)])) (.fork 4 (.leaf [(4166,0,2361,0,7),(4096,256,2071,104,7),(4352,0,2175,0,9),(4104,256,2071,96,6)]) (.fork 2 (.leaf [(4352,8,2147,20,6),(4360,0,2167,0,6)]) (.leaf [(4368,8,2147,4,5),(4372,8,2147,0,4),(4384,0,2143,0,8)]))))) (.fork 17 (.fork 8 (.fork 4 (.leaf [(4136,256,2071,64,5),(4416,0,2111,0,8),(4448,0,2079,0,7),(4200,256,2071,0,4)]) (.leaf [(16386,0,8573,0,10),(16386,4,8561,8,7),(16384,8,8291,276,8),(16392,0,8567,0,10)])) (.fork 4 (.leaf [(16396,0,8563,0,9),(16394,4,8561,0,6),(16402,0,8557,0,8),(16408,0,8551,0,9)]) (.fork 2 (.leaf [(16410,0,8545,0,5),(16412,0,8547,0,8)]) (.leaf [(16410,4,8545,0,5),(16450,0,8509,0,9),(16448,4,8497,10,7)])))) (.fork 9 (.fork 4 (.leaf [(16454,0,8505,0,8),(16456,4,8497,2,6),(16458,4,8497,0,5),(16384,256,8215,104,8)]) (.fork 2 (.leaf [(16640,0,8319,0,10),(16392,256,8215,96,7)]) (.leaf [(16640,8,8291,20,7),(16648,0,8311,0,7),(16660,8,8291,0,5)]))) (.fork 4 (.leaf [(16668,0,8291,0,5),(16448,256,8215,40,7),(16704,0,8255,0,9),(16642,64,8253,0,6)]) (.fork 2 (.leaf [(16736,0,8223,0,8),(16674,64,8221,0,5)]) (.leaf [(16738,0,8221,0,5),(16488,256,8215,0,5),(16744,0,8215,0,5)])))))))

def orForest : Forest := ⟨2431,12,fun j => orSamples[j]?.getD (0,0),orCols,orSymmetries,liveLevels,liveIndex⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem orGeometry : graphValid orForest (boundsBefore entries2303) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=5) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem allAt12 : block orForest 12 0 2 = true := by
  apply wideBlock (depth:=0)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem allAt11 : block orForest 11 0 24 = true := by
  apply wideBlock (depth:=3)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem allAt10 : block orForest 10 0 160 = true := by
  apply wideBlock (depth:=6)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem allAt9 : block orForest 9 0 188 = true := by
  apply wideBlock (depth:=6)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem allAt8 : block orForest 8 0 21 = true := by
  apply wideBlock (depth:=3)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

theorem orTables : checkedTables orForest 12 := by
  intro k hk
  interval_cases k
  · exact (rfl : block orForest 0 0 0 = true)
  · exact (rfl : block orForest 1 0 0 = true)
  · exact (rfl : block orForest 2 0 0 = true)
  · exact (rfl : block orForest 3 0 0 = true)
  · exact (rfl : block orForest 4 0 0 = true)
  · exact (rfl : block orForest 5 0 0 = true)
  · exact (rfl : block orForest 6 0 0 = true)
  · exact (rfl : block orForest 7 0 0 = true)
  · exact allAt8
  · exact allAt9
  · exact allAt10
  · exact allAt11
  · exact allAt12

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withoutPositive : Impossible (graphGoal 383) 12 (minusZero 383).toFinset := by
  exact root_index (g:=orForest) (before_sound _ sound2303) orGeometry orTables
    (k:=12) (by decide) (i:=0) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withPositive : Impossible (graphGoal 383) 12 (vars 2431).toFinset := by
  exact root_index (g:=orForest) (before_sound _ sound2303) orGeometry orTables
    (k:=12) (by decide) (i:=1) (by decide +kernel)

end PEqualNP.Outside.L_meta_5006.Signed383
namespace PEqualNP.Outside.L_meta_5006
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem signedBound383 : Lower (vars 2431) (graphGoal 2431) 13 :=
  signedInduced (m:=383) (k:=12) (hints:=12901687553) (before_sound _ valid383 383)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) Signed383.withoutPositive Signed383.withPositive

def entries2431 := extendKnown entries2303 13 [(2431,[]),(2495,[98,118,81,130,50,65])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound2431 : Known entries2431 := extendKnown_ok sound2303 signedBound383 (by decide +kernel)
end PEqualNP.Outside.L_meta_5006
namespace PEqualNP.Outside.L_meta_5006.Signed479
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withoutPositive : Impossible (graphGoal 479) 11 (minusZero 479).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=2527) (4224,0,2399,0,11) _ (before_sound _ sound2431) (by decide +kernel))
    [] (pool:=(vars (poolMask 2527 (4224,0,2399,0,11)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withPositive : Impossible (graphGoal 479) 11 (vars 2527).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=2527) (4224,0,2399,0,11) _ (before_sound _ sound2431) (by decide +kernel))
    [] (pool:=(vars (poolMask 2527 (4224,0,2399,0,11)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end PEqualNP.Outside.L_meta_5006.Signed479
namespace PEqualNP.Outside.L_meta_5006
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem signedBound479 : Lower (vars 2527) (graphGoal 2527) 12 :=
  signedInduced (m:=479) (k:=11) (hints:=13438558465) (before_sound _ valid383 479)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) Signed479.withoutPositive Signed479.withPositive

def entries2527 := extendKnown entries2431 12 [(2527,[]),(2557,[118,130,81])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound2527 : Known entries2527 := extendKnown_ok sound2431 signedBound479 (by decide +kernel)
end PEqualNP.Outside.L_meta_5006
namespace PEqualNP.Outside.L_meta_5006.Signed495
open PEqualNP.CircuitLowerBounds

def liveData12 (i : Nat) : Nat := 0x6068c14085933ffa00

def moveIndex12 (i : Nat) : Nat := 0x15801012388019001d22a458c0000c71400b0000

def liveData11 (i : Nat) : Nat := 0x931b8b10919f08382868d87c10f099c164c346e0a307ce0b311519052622705150e988211133cc46c145899662322a0a4c44d568cb713e621a803fe91200ff972803fe5c600ff941803fe48600fea22803fc84600

def moveIndex11 (i : Nat) : Nat := 0x132e0894ef3c40c0c3c682425c0038571683e8d40711a52749e01ca683a8100003225b0604a937a26d0290f3ec766281c0008856f000c000008afc8328935a1686000813053081c89c202710218508e0020c0

def liveData10 (i : Nat) : Nat := 0x2c8cc583c9800681461bc00707804988340fc506c98006a4c60e0ae00615428a270d8408c9800e8906820de2d2616286f04210a11308dc5c4d105c606c40306e082423205a1b8249c7ca17c503a201ac660a22801e63278ac6444d18898403b11041a318288a4c982c6260464c5854283c102f14121194370dc127a2650c03223820a161a0fc1057189f3261269088a20a85c127c284c126316930a171b824f44c805cc6331593889b270dc16313e5c56333085c9c44d98c1445264b6b656bad5ea6b4567acde96b25631c3a810fa1dfb8d680c15652a14f0961131f438461caa92c1f43444b064052003ff284b8c01ffa9950600ffcba283007fe64941803ff2e4a0c01ff94250600ffcba243007fe91121803bf4ef22401fb97491200fdca1489005fea6572803fd489114017fa995c600efcb92e3007fa88971802ff532a0c01bf89850600fdd22283007fa88941803fe2e2a0c017fa9948600bfccba430077e9dd21802ff32890c01ff17484600ff922423007fc5ca11803fe28508c01dea7788a009fc4c2830077c9de11803f648908c01fe22284600

def moveIndex10 (i : Nat) : Nat := 0x821cab4b141774000007937938178f3b2e905388ba83271c6f9f0800024c800b26c53e8f1b4aaa5d80522d0985800000f3b6424334f803e25cc691643f0ed1d25000000000008b48a65428300129bc700033d15b4d58c824c1503f8a1a850304403802a401040000108c20

def liveData9 (i : Nat) : Nat := 0x28c08000004071006c60802018071d041010200006410803a305450404a30481040000003a605c001e286020830286040005141a3034604006282205060df180c8f8c0078ae4c09c44c04421888e93c44400e220a0f8ba4c5c5d262b2ec6b06bca8e8a99e58926448fe26835fe795d6745cc71dc26a5906057c5b55e5655453d404c522475183d4d22446e1543206400f6e9dd4291200f7a9de4488a00fea5d24488a00dfaa66225c600cfeaa89850600cfe6889850600afeaa89850600cfea649850600cfe2617450600eee2624450600f6e9de4450600afe2a19250600cfe2619250600cfe2617250600cfe2614250600dfaa662250600efa2622250600f7a9de2250600fea9122250600dfca657150600efc2617150600fec5097150600ff88897150600d7ea667748600d7e9dd9448600dee6524448600bfcaa97484600f7c9de4484600fec5d24484600fec9117284600f7c9dd4284600fec9114284600ff85d22284600ff891222846009f668e995ca009de696995c6008feaa89850600cee2624450600cfa26222506008fe2a19448600f789de2284600fe89122284600

def moveIndex9 (i : Nat) : Nat := 0xf380001e6e17074165b230c016a00002d20044258000000102

def liveData8 (i : Nat) : Nat := 0x3450412082090410000000244366b8f19283c505014feaec985c941802bb4dad33112e30053babb2624450600e371313bc88a0c014faaec98889418038f44c4ef112830073a898912225060087f5765432890c0187e2a277651218029dc5c32922243007da2779122284600

def liveLevels : Nat → Packing
  | 12 => (1,1,6,0,0,0,0,liveData12)
  | 11 => (7,2,6,0,0,9,0,liveData11)
  | 10 => (34,3,6,0,0,11,0,liveData10)
  | 9 => (42,4,6,0,0,10,0,liveData9)
  | 8 => (11,5,6,0,0,7,0,liveData8)
  | _ => emptyPacking

def liveIndex : Nat → Nat → Option (Nat × Nat)
  | 12 => lookupWord 7 17 3 8 3 1 moveIndex12
  | 11 => lookupWord 16 51 6 11 6 1 moveIndex11
  | 10 => lookupWord 24 67 5 11 6 1 moveIndex10
  | 9 => lookupWord 11 21 1 9 4 1 moveIndex9
  | _ => fun _ => none

def orSamples : Array (Bits × Bits) := #[(0x20f8761f000463038c07f80e1e0f8c101034f00fe0387e00004085e0c0f80001383807e00003c0f93c0e17c0fe3806701e0383c018703800011e03fe3fe00007f3800ff87fc0ff3c03f00e0f800008787fff07fffffff81f80001ffc0003ffff,0x20dc721b400422438405da46170484001034d20b72187cd02840055040e2a8412c2806ea508ad0a1360a1650de2406749a01034008203ac0401e42923eca8882908009282a803f34a3520a0eb40c0018069106417443981db84109759081b08a),
  (0x30087e001887c040ff8000fe00fb02060070030003f800000870600ff000001c03ff8000003fff9c0001800803fff801ff3fc00e07fc00001e003ffc0000007fc00f01f81ff03c003ffffffffffff807c07f81f00003fe000001fffffffffff,0x2008540818854840ad8048920091000600100200026010402870200ad0444284016e81088512448400008000008a8000452d414a05ec41429a0812d401030452400300080460040002060114981ed805802581a88202720441216022c764c74),
  (0xf800000f8007f000000ffff0403f8038003fffc0000000f807ff00000001ffc000000003ff06000fe000ffc007ffe00c0000ff80000001fffc07fffffff80fff001ffe0003fffc000ff000000fff8007ffe000003fffffffe03ffffc0000,0x500000018001200000024450403d8210001dbb404041306805bf00408141b6400003028259800007600002000291c00400005a800080d002040290e301b001a5001f7610919934000fa41028022a0005a7602149084110e44038c1888188),
  (0xc3ff000001f00007fffffff000007fc0003fffc00000000000fff80000000001fffffffffffc0007fff00000fffff800000fffff0000000001fffff8000000000fffffe0000003fffffff00000000ffffff8000000003fffffffffc000000000,0xc16e000009b000009068e8e000003ec0042f7f40000008164292e80008000e304898f0e01d7c0007fff00420edfed808110bfafe0004005921f9ebc80400a2460e4afde000242266cbbf700005514cd4efd840101a32379e0f1b9f801a501a50),
  (0x0,0x0),
  (0xfc00000001fffff80000000000007fffffc000000000000000fffffffffffffe0000000000000007ffffffff00000000000ffffffffffffffe000000000000000ffffffffffffc000000000000000fffffffffffffffc0000000000000000000,0x44000000009084000000000000007b76a740040000000003829bf0260e0803bc00004000066000024855a08500000001000c9c8773108001bc000000000003600f73a655c57fc0030004410000618f677166f19c03bc0200019c040003600360),
  (0xfffffffffe0000000000000000007fffffffffffffffffffff000000000000000000000000000007fffffffffffffffffff000000000000000000000000000000ffffffffffffffffffffffffffff00000000000000000000000000000000000,0xed77322d0e0000000000800000006fb707be6f91c3889e1bfc00400400000bc00000004017800007af6fd7fef77717dffb80002000001061c01102000880c3800bfccf9e79b8fbbbf3cf8dce067e00000180820013c0000809e0000013801380),
  (0xffffffffffffffffffffffffffff8000000000000000000000000000000000000000000000000007fffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000,0xbbffafbeed6e7beedf76f7fdb98f8000000008000004119c0000000000870c000004849c18002005b3881f38f9bfe56e1de36338846f3f7e01ddf3f52f1cfc07c000080000000000020800086780000002000000dc0004106e0018031c031c00),
  (0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x1280cdd0f04f7bf76f87070fdfee00085800802e1c3761e0006407d8f0f7f001b727071fe003bef00000000000000000000000000008278000000000301f00000000000000000000000000007800000000000400e000000070000023e003e000)]

def orSymmetries : Array (List Nat) := #[[],[81,130,118],[48,33,133,118],[48,129,82],[96,115,133],[96,129,82,115,33,48],[112,33,99],[112,81,130,99,33,48]]

def orCols : IndexTree ColumnInfo := (.fork 18 (.fork 9 (.fork 4 (.leaf [(0,0,495,0,13),(0,1,460,34,7),(1,0,494,0,11),(1,2,424,68,6)]) (.fork 2 (.leaf [(1,32,78,384,6),(33,0,462,0,8)]) (.leaf [(34,0,460,0,5),(69,2,424,0,4),(161,0,334,0,7)]))) (.fork 4 (.leaf [(385,32,78,0,4),(4104,0,2535,0,11),(4160,0,2479,0,11),(4224,0,2415,0,11)]) (.fork 2 (.leaf [(16386,0,8685,0,10),(16384,4,8545,138,8)]) (.leaf [(16386,4,8545,136,7),(16424,0,8647,0,8),(16450,0,8621,0,9)])))) (.fork 9 (.fork 4 (.leaf [(16514,4,8545,8,6),(16524,0,8547,0,8),(16522,4,8545,0,5),(16526,0,8545,0,5)]) (.fork 2 (.leaf [(16420,128,8523,0,6),(16384,256,8327,104,8)]) (.leaf [(16648,0,8423,0,9),(16650,0,8357,0,5),(16644,8,8419,0,6)]))) (.fork 5 (.fork 2 (.leaf [(16416,256,8327,72,7),(16672,0,8399,0,7)]) (.leaf [(16424,256,8327,64,6),(16704,0,8367,0,9),(16712,0,8359,0,8)])) (.fork 2 (.leaf [(16650,64,8357,0,5),(16708,8,8355,0,5)]) (.leaf [(16480,256,8327,8,6),(16488,256,8327,0,5),(16864,0,8207,0,5)])))))

def orForest : Forest := ⟨2543,12,fun j => orSamples[j]?.getD (0,0),orCols,orSymmetries,liveLevels,liveIndex⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem orGeometry : graphValid orForest (boundsBefore entries2527) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem allAt12 : block orForest 12 0 1 = true := by
  apply wideBlock (depth:=0)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem allAt11 : block orForest 11 0 7 = true := by
  apply wideBlock (depth:=1)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem allAt10 : block orForest 10 0 34 = true := by
  apply wideBlock (depth:=4)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem allAt9 : block orForest 9 0 42 = true := by
  apply wideBlock (depth:=4)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem allAt8 : block orForest 8 0 11 = true := by
  apply wideBlock (depth:=2)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

theorem orTables : checkedTables orForest 12 := by
  intro k hk
  interval_cases k
  · exact (rfl : block orForest 0 0 0 = true)
  · exact (rfl : block orForest 1 0 0 = true)
  · exact (rfl : block orForest 2 0 0 = true)
  · exact (rfl : block orForest 3 0 0 = true)
  · exact (rfl : block orForest 4 0 0 = true)
  · exact (rfl : block orForest 5 0 0 = true)
  · exact (rfl : block orForest 6 0 0 = true)
  · exact (rfl : block orForest 7 0 0 = true)
  · exact allAt8
  · exact allAt9
  · exact allAt10
  · exact allAt11
  · exact allAt12

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withoutPositive : Impossible (graphGoal 495) 12 (minusZero 495).toFinset := by
  exact root_index (g:=orForest) (before_sound _ sound2527) orGeometry orTables
    (k:=12) (by decide) (i:=0) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withPositive : Impossible (graphGoal 495) 12 (vars 2543).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=2543) (1,0,494,0,11) _ (before_sound _ sound2527) (by decide +kernel))
    [] (pool:=(vars (poolMask 2543 (1,0,494,0,11)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end PEqualNP.Outside.L_meta_5006.Signed495
namespace PEqualNP.Outside.L_meta_5006
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem signedBound495 : Lower (vars 2543) (graphGoal 2543) 13 :=
  signedInduced (m:=495) (k:=12) (hints:=13438558465) (before_sound _ valid383 495)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) Signed495.withoutPositive Signed495.withPositive

def entries2543 := extendKnown entries2527 13 [(2543,[])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound2543 : Known entries2543 := extendKnown_ok sound2527 signedBound495 (by decide +kernel)
end PEqualNP.Outside.L_meta_5006
namespace PEqualNP.Outside.L_meta_5006.Signed503
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withoutPositive : Impossible (graphGoal 503) 11 (minusZero 503).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=2551) (4112,0,2535,0,11) _ (before_sound _ sound2543) (by decide +kernel))
    [] (pool:=(vars (poolMask 2551 (4112,0,2535,0,11)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withPositive : Impossible (graphGoal 503) 11 (vars 2551).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=2551) (4112,0,2535,0,11) _ (before_sound _ sound2543) (by decide +kernel))
    [] (pool:=(vars (poolMask 2551 (4112,0,2535,0,11)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end PEqualNP.Outside.L_meta_5006.Signed503
namespace PEqualNP.Outside.L_meta_5006
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem signedBound503 : Lower (vars 2551) (graphGoal 2551) 12 :=
  signedInduced (m:=503) (k:=11) (hints:=22028484865) (before_sound _ valid383 503)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) Signed503.withoutPositive Signed503.withPositive

def entries2551 := extendKnown entries2543 12 [(2551,[])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound2551 : Known entries2551 := extendKnown_ok sound2543 signedBound503 (by decide +kernel)
end PEqualNP.Outside.L_meta_5006
namespace PEqualNP.Outside.L_meta_5006.Signed511
open PEqualNP.CircuitLowerBounds

def liveData14 (i : Nat) : Nat := 0xa92548c2208627c9806504a9184c1105a8044f9324926f80ffe00ffa00

def moveIndex14 (i : Nat) : Nat := 0x830af3218633800aca1329e617280062f2090f11cc38148c29a03ea5081000094a1c735480000000c9a2de1400e9000ab20f0034d212098311100707410010

def liveData13 (i : Nat) : Nat := 0x92b232430b5141064c23e54c9590c2324c0a0832816d2564648810d27c5ac194026953232440a4133064f2a64ac8811927c4cc193ca992b2304c8a0151064f2a64ac8890c2324fc988328953256464869302820c9e54c959192224f89983279532564449800527e4c89344a992b2324c499032280f2a64649f9492800c89938a01e324a010e31be2d47420778e38043124c0df30981e83be010c493f2487ca06b8f480431249493148265032c4cc9f9490087c8931d081f238e010c99243a0c3be4fc8680529049c981be814126064cb580438e490e840f993f23252402133248742365e6ec236feb6d1b97d1b20d3bd6d6c655e2754306ecaf117174174007ff60a00ffe99401ffd81803ffaa3007ff4c600ffe90c01fde33803fdc45007fd84600ffc98401ff920803ff221007fe60a00ffc99401ff981803ff2a3007fe4c600ffc90c01fda33803fd445007fc84600

def moveIndex13 (i : Nat) : Nat := 0x482df8843006100f60a6a8c44841c801a0b5c009f00d403c90518820382548b6a050902d204668b2f0b9980e18c500960000000000aca8a1d0429817f031f88aa100488e70cff83800ba60026046d85058212856e8b480b20055004ba82e5008f01f285208227015e8a2482c28b55000a0c08037b08d481a00007810e84f0804883e60af800000002095989468892892903b5031584838ae504a183d00b8209e68d5c01578ca0000782f8a076085604c98b3901c201958100000203bd0340099602370323832c0510039d014f843800000275c009002f02280001049b83a502b3033481dd812b0a06902a80308a4f8998000000048565900a81b0b00f8449826b81350c640180811880a30cce0473053400fe892604b00c06093b8c3e8349827c01fd00c1023d83df0cd780be083581af0be000000000000104d701c905480001038b05458b1404c4030603fb901e8b900000000080c8000000068a9800000004845a816e880c09700001896c028f805182ce84e900100006285c007000030188000605290d0a088b8c9b036180b4007e80ae09ba055f84e00001040cc01a88d901e1025980d983548286029a8111013a024e01b80000000482bc849000020296840502a58427035984af091f0859d05903f702ac098b0146819f804600ee82ee817008668b6282668822882c036981670a3f897d0aa984fa8488809258770a7d02f0039480010436830d83a9053d824281d38122847800000000003a833c09020bd9808403c30375b0b602198412380a402c820e845181ef8a0d03e98440000704db0a8709af80580ae9806a0a9111ed0a812a2010c1a00b881202d123d1c1020c123820250308285800606180002400584160461d04151111a181861e2b18004000000a45a000244780122c00d2a181990c2020002001800200002260d103

def liveData12 (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0xd5165325470508d3ca4d953244b2d27e48951cc459d11a4305068406cfc23d14ee03a1ce2e3754d64342ccb23164c002e9cb362ba4a9028dc9ea267495023dc8aa21447f81eac7521be46a0194c5ee162453c13bc4a211243e40e5c3320b942a4092c1fe066414003fc0a60134000fffaa982803ffda360a00fff68582803ffda84ca00fff69532803ffda14ca00fff69581803ffda360600fff68981803ffd5260600fff4c981803ffda354600fff68951803ffd8254600fff4c951803ffeaa4c600fff6a131803ffda54c600fff68931803ffd824c600fff54931803ffda848600fff69521803ffd8548600fff68d21803ffd8348600fff54d21802ffeaa60a00dff2a582803fde3360a00ffe68182802ffeaa4ca00bff6a132803fed824ca00ffe68132803fed8388a00bffaa981803fde3360600eff60981803fee2260600ffe68181802ffeaa54600dff2a551803fde3354600ffb88951803ff58154600ffe68151802ffeaa4c600dff2a531802ffda84c600effa2131802ffda54c600ff74c931803fee224c600ffd60531803ff9a04c600bffaa921802ffda848600effa2121802ffda548600bff68d21803fde3348600ffd4c521803ff9a048600ffd61611803ff58384600ffd54e11803ff58284600ffd54a11803ff53284600ffe68930803ff9824c200ffe68530803ff9814c200ffe54530803ff9214c200ffe6a120803ff9a548200ffe61520803ff9a348200ffe60d20803ff95348200ffe68520803ff98148200ffe54520803ff93148200ffe6a110803ff9a544200ffe61510803ff9a344200ffe60d10803ff95344200ffe68910803ff98244200ffe54910803ff93244200ffe68582803ff95260600ffe4c981803ff9a354600ffe68951803ff98254600ffe4c951803ff9a84c600ffe69531803ff9824c600ffe54931803ff98548600ffe60d21803ff953486009ff2a5828027fca94ca00efba2222803fce3388a009ff2a5818027fca9546009ff2a5318027fca948600efda2211803f765584600ff58ce11803fe62284600ffa88930803fd9314c200ffc84530802ff9a848200efea2120803f7a5548200bfe68d20803fda3348200ffa54920803fe92148200ffc84520802ff9a844200efea2110802ff9a544200fde95510802ff9a344200ff68cd10802ff9a244200ffa88910803ff15144200bfeaa982802ff8a960a00bfe6a132803fe9824ca00ff68cd81803bf98260600ffa88981802ffaaa54600bfe2a551803fda3354600ffc60551802ffaaa4c600bfe2a531802ff9a84c600efea2131802ff9a54c600ff64c931803fea224c600ffc60531802ff9a848600efea2121802ff9a548600bfe68d21803fda3348600ffc4c521803ff18384600ffc60a11803ff15284600ffc4ca11803bea8888a00ff48ce11803fe22284600 else 0xc8c4958198994a04861003a54e4a878c01250249c4ca43ed2183a042098059249c71f21d05c028994df0ff207a06260107124986b9b00836b2483a881861ae9181e18041e39241e81d090efc020e38994df286da5a87e8819031929040c619710c1fc1c0480249f8994e30e02e0164927a4741031300300837c3fca18e1f21eb8041c69271d0700fc95c860638b58a04193831e4a80aa0164c0519b25723321a2812d7064d95392b90c9199311418327c95c8cc88c9f4190b63013654e4664445244ca0c9c0272a725623327c056265065195392a02a8321505c95c8cc884a9c9f899c193e54e4664425244ce0c9b2a725722123327e267064f95392b91894113215183278a9c98c9588cc994a0819103404664ae4fa4cc0c8819b2a727f29200b28126624ce12a18c1eb14103296a1c07c95c8cc864b58198a03654e4664c24ae4cc0cc501c32423d2303e72572622803fa064381510c91992b93114196b0321c080a5088ca9c988194a40e03845654e4a85040ca4c8701e2332a7256281266064380e1f216c95219f93f9410331322109c8cc9fca44a9ca08198993813654e4664425244cc0c9f2a7233221292064156264e9181d992b93f1330322067ca9c9fca4802ca04938993862045046654e4aa5040cc4c870272a7257232065282264d95391991004c13294903278a0c020fa8e3c928e80f13c5007d47188920c878983cf00830c3c52d437cc1e38041c618696a1be6898c9f111c024934df8f9387607ce4960107c0741a26138f24b00928137e3e4f1e804d9251899271481ae70e2c8c1148e34190d7346b87b601249c5226fc4c9c3e43130084532483e044cf80592a1a912793f20219670fdc95c9f0d44190cb307ee4f870c43601087c6d080a03f727e2183b944300a36840501d980512713294820660cbc024e30ee8990df3078601271865c4c86f983e43f727f008444430404e1f61f212a1e39258321f01d080f98e3c02c924f28e8307284664927a60ca4a867074203bb00a38e26437c32cc1e38051c69271d05c000cbc028e30f00d30df387ca7a60164fc6d280983ec3e430d3d324b0093c83a1093e9e98041959251329c670ffc024e38994df2c50601462649471c6fa5a9d3bf27f29300a2663a124cf1f29c78041979241d06f307c5cefdfb9eed17ae0ea1fa2ee75794ce33f876e0777acdcef6d6da2763cd78f566d377484d0af3bacd872e4c96f1eac677138c43f0c2c176fecbedef52bc16e94b8bedd6b656d24b32ec7eb0c6bccae5eb1aab36a5ca7de992a4b68c8a12e80a9f267649c2e6a698a65c4951e51e9316460904e3ba8d562f08a5e24a87f6174843e092817601c7eadf527b55e40782dd9a74a5ce8723dc666fd5ba86cddac66a45a2066bd93e64258c8624d84660457a05d7d72a5c056cc5a2d65658555bc558) else (if i < 3 then 0x2dc0dce0180d014a94b16d91910c92a94116b832b00c08f8b648cc958860914a08b5c19544ac4324660103f01301b9e257233009282264098200e01815604d918910953133149832900c48c026ca98950914a0899c194e0105604304665206284681ba22303152d700b2900dcd11995218b80494806e60acc95c024a00c5091037386505787864ac46006048a5aa5060ca82942472a40303281a1296232265283065695392a12380418415006e7ca908e052c020c20a10373806811802e4625944525ac5060ca70082ef2900343082440dce00a01a95212291992a15f133141832a00502300d029091ca949548c8998a0c19584607607864ae43057c5ac5060ca42122801c02050642bcc15e19192b90c91916b14183284021050e01e4ae4c65ae4ce01051983082bf25721a2312d6283065015e18592b90d11814014496b83290e30fc0a30e02057863e4ae4324645025ae0ca323327f2932830642d8d16c1db92b91091915393f13383290b60eb00cc95c8c4a0899c19445b64ae4644325045ae0c9c4262643682dc420a1af91195391913383314806e04c9068c8c4190398a40370263e54e4424645244ce0c9b2a7231222266293064c16d9101e791801914896b83284198998a40262044063065654e4ac4664f848c4ce0ca81cb25727c0c9064244c18b91192a01895311993f13383290eec95c884a988cc9f899c194062e54e4444625244c841e0ca32a4030317254246265283065012218f95392b11894113383280b6c880ed0eec9fca488c0444b5c19506dc4365220c881972a72572330642a0a18400b92b918953141133832888ac95c8c8864b58a0c193861654a4ae4603444cc5060ca02443080172a72552322822642a3065412219195392a91914113383280c70c8ca9c9500548c0910998a0c19504d0068700d2cb2332222192912d7064e95b92b91091910d93e96b8328ca9c8848c8994a4c193061e4ae4644325025ae0c9d29430f2a7231256265283065012218795392a919132941832808f0db8194864a401e103387186200e88640c8819836e06521929007840cc1dc1d603a1f392b91100490d93e96b126b0f401d0e50f088c4a4499819406386100e862654e4ac0124ca50449aa00b2552d438081a214b96a9481c050eb00a0f90f60ca4954b58a08194847868a4664ae5ac0c8701c3203140292552332183d92d6282065419018a0149521ea91990c1ed93092b141032c08a49900d0e02006a54a4a87c86507ac0cc5024ca40352a435c3d8329256065266281218c1ed0049321c054a949548c4880b6c9f0363a5201b0130c3ac01d2312a72203da065292265295292a91891193e06c64a949500d0f30f1802c9f4938994a5487aa4600686787844ca5240ca42292800340d889529181e004c1e61e303294113290c20070e3ca9 else 0x30b25721a2822d70642bce16291811218514116b83215e80b9c8c0c2c950af8a0499c19464a84486125a85160c8579c2bf26029830b26700828ce12215992a18493380414404088990760bfc020eb0b70373c4ca46601075e5205b81b9e2672330083af290))

def moveIndex12 (i : Nat) : Nat := (if i < 1 then 0x16f42135013c4231c02164067c0894421ff056b860e15006c19e801d4c149417fb822b914854500906b304d7d069600711045dc239504740145f00c380eda11658446a035d45ece16e084dc30889411ef037540be7081841e63184680dab13dc0000f17fd40ae908a90157906ac81c30000241d1000024169b80180000d05c340c3f1529e0070000242190000140b400003852de0504000000002863c60562818520480c022000000000d191140b3000000000a0440010c20414c0f7703a9c148000000000e05bb4805605440000000000000d80300000000000000107a0000070591014ce04880000d01c300de80270000000003818d000000000d002f0496f1239402e9086ac508d00e6010a615a3813f917f4446a000030087707cc000000002c1bf7064a9023c061245667075741f5407bdc45ee022d41d6415fec1dce13fdc61b813bd8474b08ca859441578813b30179c5c01062c4086a01b3013c1102f051e100f3853ba148c0457a081101a792025c14f5039e44e410398023d618ac044b800b6c243f020ec04c1000a416af00a9447a20668021ba13b0c19784074847fa189305850072f00a7b189bc45210666008fd00acc1ea22033414730768461701015c187e0110c43f910de015da04e78137a017641afe060285c34103d80c8822a5c1a8906938042704b44047f04f401fec07dfa00b7036004ca0018e0023a000cc22f9054f01c8307e088011179240d1f01738215410f700315141b8226b03d045e0ea025c1bb218c3c1e0509160490c042485d9f15a7c806000010135600778533f029ac223708f800002176240f1602904526e036f0026103b9c588c04afc80ac160c80aa0076200fa508cfc15900001021ec146941cda05a00000718044051002c2424060557c48d012b684bfc08744129e07dac1ff501d0c131b01a880e2000d040ba8002284b1b1247c481f1314461a20510c198f05dd457cb187440045058d808ee0681c418604110247401e1823ce136a004b02004a03a9061b290028031d4c1a56390c400000002d01301701332d040000000b0012042d000b080903147d7000030a0f40031e0b0c8402130d1a07070f0300030b371a0617000359d6200a000b0004000d4b000e1801000b25011d0d01000d030512060006131a250e16421d2d010c0e0c000d3f000001090a1808021f025a30040b062518021e071b6303044c0009021100047e0a2786010c0208013a0300090202011400000d003f020623000418002000000500040100010a030069006505100000021d19017a05642b3301030000040008450e08333f01003c010d0101ae690802002142010301070500020024043e00020a3f550a000002500600001600000d000b002800000e030a0700020a2e0013000004040e1e0215154100000b1200000506071604 else (if i < 2 then 0x17b816de4101b1414880e3063280fc604e001a91050a05b3a03d800000092385a0e04d8820100000856100003c58a00002c563a00580000d103940353004f580c511cf051b606cfc10ed07c9440c810fac4d1108474133215cd458c2179f40f000000c19f0000241e92042c01e2602c681aec043c84cb1164885e2e019b80d3d0037c103b07b7c80b307d2c14ec06fb00bc004abc0f21033a801ca0676807cc025dc59b018534027f11500000811bec55900003409f7191e00eb912509c0dc131840d0f03254608f02de4179602e0003270386c20c210cac0ffb055000000000201c9d0408061880090c4db8168d40e3406b6c186262a440a0000000000b046c5c32801e602346111744fb810400000a03b30244c032a81a1b182e008a101fd8648b05f8c0567046bc053000014140e188c4143f07f0000000001c0bbb160740960000141c761480000051324c50c5016581b471929010731560000080007c436a0586450901671405a301b81006106de021c314fb8183611cbc0e900052847631337c212f1552c547102d6c20e4075241fd710280000f018bc06500003c56cd16900000f0462c0296005400000000340a50059c4121215836811d1526e00af02ad0072804c38565e059a0098db0180447500bf863d900840000b079d854400001c408715458229802ca0005f024ec01e0124e85a6205c7c56df033ec1ce6113f844c80797409ed0221020970837d418a05c880dcb0309c18900003c57e5183d84ab0000300c19163e413af104d0439b110981dd1117204f1d05b2d80d92022417d013cc4210602544055c080d0054a03f441f0b01a5823f00003857b907b2c0bd2045800520060400000006e0246e15d54007406c0c16b30689c5a2b080b423b406ab0190e05cf00a9a11d40010804970048c1600c025a109645305024250003003181b8c1340c4cfa0277c4fc20490c1088152380c7f010c0064f12e2012ce063c40c5a077f8471c8042c0b61138f40df8179a80c01119fa00e008de00367117cc504a10890194c066f0431a03d605e1f0549415f315150584410cc003f009060236e056c4470701d981e170891422d904bcc1dbd06388057c604f44d8806f5c2275070a403b0024b04e70048d003e10418455520312c63ec074e821701051c09ba002480d660047423ab1436421630453c00ac0579817a515ae842020062022cd03bec2187035045bca160bc587d092cc060e0435011c7014145a9806cb056761446006d6111200201187dc616d0392016f605db4230805b780b9508a380380045501eba10554156b016001d7e15e7c113b049944fd30698863b60226008c3052a413e60102c0a16074b844ad162500e5b026ac50b8020bc235702ffc22e71635816230536c54d01254803300581c552a082a045060543c2082131f00c611 else 0x9007e4084b06f24000b0128c6159072800d98062ba009a059680a8b032e8591d020501a3b0644405f2044740e8a05d2458e90710000081493062ac03f9051f101dd804eba32880a2906c6c207515e90479e046581e3814f40000b15ddc5f4003818175706d40000f016c45f2b0742200dd0881804191331c200c01f6850e601ecc556f108dc0060000240d5d16684028701240000b80200000601cc4100000030195a141f844330716c543d03ee801ad06e641e47047dc182a02bc0000400dd01c0702b282492081501f19013785dab0886c00e20064c112b003c0000a07640000e01be061e50732c1fbc131381cf801840000115700000000000000f11580000000000000305e2c0d211218c14b00000060610706003a105fc000091194447bc01140000e140d45e86090901b600001c08d00000462000000059f51590c06800003058bb03e3c06be02028590e0620820ff057200a35005f00f9c03300000d164f44fe81705c1f9f04a38193c03cfc03d1092841faf227d8094b02b680cd907b98046b18b744f4902640401a05188127601f905572024741dea06704132206e9c62f5082d8553a177d012e4004b844d200b302148133881c6304d1c07a508e10196d05f20))

def liveData11 (i : Nat) : Nat := (if i < 4 then (if i < 2 then (if i < 1 then 0xa21218023fe5cb4a90c011ff2e5a348600cfb95319a430057f4b961611802bfa5cb0708c015fd2e55384600f7ad1119c23007f56558ce11802bfa5cb0508c015fd2e55284600afe97299423007be68888a11803fb32ac4508c01ff18ce2284600f7d511112610057f8b968530802bfc5caa2984017f6aed314c200efb17298a61007bda884c530802fecdaa6298401ff2889314c200ffa30298a61007fd13148530803df94442298401fdc956114c200ffa2a708a61007fe222845308033fc5cb50904015fe2e5a848200f6f5112aa41006bfa8868d208037bd2ab46904013fe6e98348200dfb35119a41007bda888cd20803fad2ac66904017faaed5248200f7d510a9241007f695354920803fe519aa490401afe6a18148200fed2a4a8a41006fd9a34c520802ff55da4290401efaa212148200bfd36a90a41007f6a5548520803fe519a4290401ff84c52148200dfe35108a41007bf28884520803fb92ac2290401bfc68e1148200ffa46708a41007fe152845208033fc5cb4a884015fe2e5a544200def3512aa21007b7a88955108033fc5cb4688401afea21a344200def4aad1a210057f8b968d108027fcdd306884013fe6e95344200dfb35119a21007bda888cd108037ecd2c6688401fd69563344200d7f510d1221006f7a55689108037ed19b44884013fe6e982442009ff374a9221004ff9ba4c9108037f4d444488401efaa222244200dfd34b11221007f6a55889108037f4d1c4488401ff28ce2244200bfe576a8a210077f0b9545108037f8d42a288401efca215144200ffa466a8a21007f715254510803ff1112a2884013fe2e6aa60a009ff36254b05005bfabb60981802dfc5cb04c0c01efa6095260600f7d30499303004ff8b9aa9518037f511554a8c013fe6cca9546009ff36454aa3006fea222a5518037ed55466a8c01bf62a63354600dfe554c0aa3007fd23360551803df8c1302a8c01fdc54981546009ff17355263004ff9b82a5318027fcda95298c01bde954a94c6009ff576d4263004ff8b96a1318035fd5551098c01afe2a6884c6009ff576d2a63004ff8b9695318035fcd430498c01ff2609324c600f7d51111263006fe9a5889318037f95530298c01bfc695814c600f7e304c0a63007fd13260531803ff11130298c013feaeda8486009ff172d4243004ffabb695218027fc5cb4a90c01afea21a5486009ff374c2a43006bfa8868d218027fcdd30690c013fe6e95348600dfb34b19a43006ff1a84c521803df94426290c017fcaed8284600bfe172c1423007bf18360a11803fe919b0508c01ff48cd5284600ffc304a9423005ff1b84ca11803df94426508c017fc6d53284600ffc30499423007fe18388a11803ff0a9c4508c011ef6d0a960a009f736854b05007bd2888ce11803df14444508c01ff08ce2284600 else 0x1bfe6cda544200dff364d2a21006ff9a869510803dfd4434a884017feaed8544200bff374c2a21007f79a8955108037fcc2b46884017feaeda344200eff172d1a21006ff9a868d10803dfd4434688401bfe695a344200fef4aad1a21005ffabb60d10802ffcdd30688401fde9558344200bff576a9a21005ff9ba54d10802ffcdc2a688401efea215344200fef30aa9a21007fd98354d10803fecd446688401ff66963344200ffb30b19a21006ff985689108037fcc1b4488401bfe54da244200dff350d1221007bfa88689108037fcd2b4488401fde955a244200dff346d1221007fda3368910802ffd5db04884017fe6e98244200dff34ac1221007f7a5560910803dfcc1b0488401ff68cd8244200bff576a9221005ff9ba54910802ffcdc2a488401bfe6a15244200f7f510a9221006ff9a354910803fbca9aa488401ff68cd5244200ffd304a9221005ffabb4c910802ffcdd264884017fe6e13244200dff35099221007bfa884c910802ffcdaa6488401bfe6953244200fef4aa99221007fe9824c910803ff4d444488401ffa6962244200ffd30b11221007fe9a388910803ff4c1c4488401ffa54e2244200ffe370a8a21007ff1a854510803ff8d9aa288401ffc68d5144200ffe306a8a21007ff1b254510803ff8d12a288401ffc6095144200ffe264a8a21007fda3354981802ffd5db46a8c017fe2e5a354600ffd444d1aa3006ff9a868951803dfd44344a8c01bfe68da254600ffb466d12a3005ffabb60951802ffcdd304a8c01bfeaa98254600bff172c12a3006ff8a960951803fed19b04a8c017fe6e93254600dff554992a3006ff8a94c951802ffcdc264a8c01ffa6093254600ffe346c0aa3007ff1a260551803ff899302a8c01fde955a84c600dff172d2a63005ff8b9695318037fcd42a498c01efea21524c600ffe2a4c0a63006ff9a560d21802ffd5daa690c017fe2e55348600bff370a9a43007bfa8854d21803fecc1aa690c01ff66163348600ffe30a98a43007ff15360a11803ff8c1aa508c01ffc61532846008ff973553050047febb2a5828033deda152c14011ff6cca960a008ffb6254b050057bdb42a5828033ee54c66c14011ff6e0a94ca008ffb6a54a650047fdb12a5328023fe5cb50994015fb2e58388a00f79d1119c45004efdb6aa9818023feda952c0c011ff6cca9606008ffb6454b030067dca98cd818029fe5cb04c0c019fb2a622606008ffd7654aa30047fdb32a5518023fed9152a8c019f72a63354600cfd953112a30057f4b9605518023fe5cd5498c011ffaeca94c6008ffb7054a630047fdb52a5318023fed915298c011ff2e5a84c600c7f953442630047fcb969531802bee5ca6498c019fb2a6224c6008ff973552430047fdb82a5218023feda95290c011ff6cca9486008ff972d42430063fca9) else (if i < 3 then 0x6a54a63004ffebb6a1318033fe5cb5098c015ff2e5a84c600cff952d4263006bfeaaa21318039fe54d1098c013ffaeda54c600cff972d2a630057fcb9695318033fe54b4a98c013ff2e9824c600aff972c12630067fca9609318035fed430498c015ff2e5524c600cff952a9263005fdebb4c9318037ef5526498c01ef7a21324c600ff9b0499263006feeaa889318037f6d444498c01efba22224c600dfdb4b11263005ff6bb605318037fb5530298c01dfd2a5814c600dfeb4ac0a63007bf58260531803fea9930298c01ff9889814c6009ffd76d42430067fcb96a121802bfe5cb5090c01affaaa88486009ffd76d2a430067fcb9695218035ff4434a90c015ff2e5a5486009ffb74c2a430067fca9615218027ff5db4690c01affa21a3486009ffb74c1a430057fcb960d218033fe54b0690c013ff6e95348600aff972a9a430067fca954d218037ef5546690c01bf76a23348600f7bd1119a43006fdda58cd21802ffb5da6290c01bfdaa93148600dfeb5098a43007bf6884c521803dfd4434090c017fdaed8584600ffe360c2c23005ff6bb60e11803ff8d830708c017fdaed5384600efe972a9c23005ff5b854e11803dfb442a708c01fdd6155384600ffab06a9c23007ff1b054e11803feac2c6708c017fdaed8284600efe972c1423007f765560a11803dfac1b0508c01ff58cd8284600bfed76a9423005ff5b854a11803dfb442a508c01fdd54d5284600ffac66a9423007fe58254a11802ffb5da6508c017fd6e13284600f7ed1099423005ff5b54ca11803fbb2aa6508c01ff96093284600ffcb0b11423007fe58388a11803ff2a9c4508c017feaed814c200f7f304c0a61007fea2260530802ffd5daa298401bfe6e9514c200eff172a8a61007fd9b354530803ff5112a298401ffc605514c200ffb2a498a61005ffabb48530802ffcdc24298401efea21214c200bff36a90a61007fd95348530803ff8d442298401ffc696114c200ffe30b08a61007ff1a284530803ff8c142298401ffc54a114c200f7f510d2a41005ffabb61520803fbcd44aa90401bfe615a348200f7f510d1a41007f7a5568d20802ffd5db0690401fde9558348200bff576a9a41005ff9b854d20803dfd442a690401fde6155348200ffb306a9a41007fd9858cd20803ff4c1aa490401efea21a148200fef4aad0a41005ffabb60520803fbd2ab0290401bfe68d8148200ffb466c0a41007fe95260520802ffd5daa290401bfe6e95148200bff370a8a41006ff9a854520803dfd442a290401bfe68d5148200ffb466a8a41007fe9b254520803ff8c0aa2904017fe6e13148200f7f51098a41005ff9b54c520803fbd2aa6290401ffc6053148200ffd30a90a41007fe98348520803ff4a9a4290401ffc6161148200ffe30708a41007ff15384520802ffd5db50884 else 0x603cbf197c42f165d14b7f96c62d1a5950b0d95ef2b52558ca9b94f1293c51c8a1c940027744dd098a12c124a8479c8d71175225e43d884490361fc63e747ab8f111db03ab07400e471c1c37206c78d631a6e342c66f8cb3190e310460a8be9177a2e445ac0b1215e62ae85470a551438278c4c8094a12082360456088010741f683d087820eac1ca837f06d20d4c19e832706080bb8168c2b5052409f013302498467085c10081eb03aa06fc0d4819302ed05820a5412e02230408072c0c2813f01d802640230000bffd76d0b05006ffeaa685828037fed2b42c1401bff68da160a00dffb62d4265005ffebb695328037fed434a99401ffb6d5824ca00ffdb4ac1265007fedb1609328037fed434299401bff695a14ca00ffdb04d0a65007bfebb60981803dfedab04c0c01eff6cd8260600dffd54a9303005ffebb4c9818037fedd264c0c01bffaa93260600bffd76c12a3006ffdba609518037ff55304a8c01dff2e58254600eff952c12a3005ffebb4c9518037fedd264a8c01bffaa93254600eff952992a3005ffdb84c951803ff6c1264a8c01ffd4c98154600bffd76c1263006ffdba609318037ff5530498c01bff695824c600ffeb62c1263005ffebb549318037ff552a498c01bff6a1524c600ffdb04a9263007fddb84c931803feedaa6498c01ffd549814c600dffd54c2a43005ffebb60d218037fedd30690c01bffaa98348600dffb4ac1a43005ffebb54d218037ff552a690c01dff2e55348600bffb70a9a43006ffda854d21803feec1aa690c01ffd6153148600cff97355305004ffdb3aa9828027fed8d54c14015ff2e6aa60a00cffb6254b050057fdb12a5828037ef55466c14015ff2e5a160a00cff952d0b05004ffebb6a132802bfe5cb4a994017fbaed824ca00dfdd54c1265005feebb60e22802bfe5cb4ac0c015ff2e5a360600dfbd5519b030057fcb968981802dff5db04c0c01affaa98260600e7f972c1303007bde33609818033fe54aa4c0c01efb6095260600aff972993030067fca94c981803df6c1264c0c01bfbaaa2260600ff9c6711303007fea22681818033fed9952a8c019ff6c8a954600affb6654aa30057fdb22a551802bfe5cb46a8c019ff2a5a354600dfbd5519aa30077dca98cd51802bfe5cb44a8c019ff2a5a254600aff972c12a30067fca960951802bfe5ca64a8c019ff2a53254600dfdd55112a30077eca988951803df744444a8c01ff38ce2254600bfed76c0aa3006ff6aa60551803bfa54b02a8c01ff58cd8154600f7eb04c0aa3007f755260551803ff311302a8c01bfe68da054600ffb466d02a3006ff9a268151803ff511340a8c01ffc605a054600cff97355263004ffdb8aa9318027fedad5498c013ff6caaa4c600aff973552630067fdb82a5318033feda95298c015ff6e0a94c600affb)) else (if i < 6 then (if i < 5 then 0xfb0700c224c1907f8f8004f20748f8000ff0700f8010e8a7183809c0028303807c0007f83807402e0003fe9be407c83499480e0232d41c0260170021b4d01230091f24e3c4c937cbc95e4362d714001d2e2801f411508900601e2647cf0089edc9fc6d1404c8f9e01538f924cf2874181ffc02a71e2649be5e291c43f871f0b7e117c14b8136feddf83be237a7ef23de09bb6375cee9adcddb8a36fe6dd0db15b5af69fed2dd9e9b2ef64e6c70d889affb5e2eb99d6c1acd35846ac2d547a9df52c6a1fd3e7a7534dae97cd2a1a45f475e8bfd127a16b41de80fcfad9e773b8e738ce199b1b346e647cc37978b2e1e58acaa3946326fe4cdc977927322b6410c7e38eaf1c6636dc6698c57167e26fc46d87f70d5618bc2d98537090e0e8c15f81db01ee011bfb17f1afc6df54be1d7a1ef345e08bb9f76f6ec8dd65ba73746ae775cc2b913710ee125c12b81b6feedfb5be4b73d6d62d8fdaccb50d696ad1759e8b35f650ac84d8d0b14961aec265806af9b5e1eb9a56baaccf58baaf455a2aa9f54f6a8f54ffa9595236a30d435a8134f769d8d378a6314b1693fd253a3cd46b68b3d148a19d425683b50309fbb3e5e7a24f259dbf3a9a73d4e349b75359e6a44d1c99fb3346652cc86988130526014be397a32eca5d04b7496c52d42598cb1296012bba567cab0952329fe536ca4e945f280e4f249b8931925b64a7492f923b23c646fc8cd915d227243ec8519065201a3ed47c88f531e5e3b5c74c8e5b1c0636ac6a98cfb19ae31fc6208c0317562db458a8ad7153229d450e89df1342258c49288cd10ea20dc40987ef0f621e343a787110da619ec31185e50b4e153c29584d308c210f41f283a707060cac169827b044607940b9814f0256041c064808b009a003bff57fc6ff11fd93f937f02fd89f9b3f177df0fb65f63bea87d2cf9ddf32be467c34f821eee3dbd7b56f665ebd3d687a92f475e78bcc5794cf21de343c497854f02ddefbbcd7742ee09db83b517664ec81d7a3ac87552e9f5d35ba3f745ae839cf7b9c3732ee5e1ca63920721ce3f1c6eb8cb7172e269c3db85c707ae045bffb7e06f9cdebdbc8377e6ed8dd01b8a37026de0db45b5fb6a06d1cd955b1b360a6bd6d6fdac9b5816aaad4a5a7eb4de697ed281a40b46f68bad12da0fb40067a8cea19be33506648cc15979b2d46584ca8d93bb25863bcc5f989c30e560f0c0617e92f7f5e3ebb317432e5a5c0eb6d16b0ad01595cb1d560aabe95712aca5564aa83547aa7a94a4a8e950f8a0713e4a74f4dde9a09317a5f64b46957528524c4489490791d8a35e46648c19166a27a4434871d0b3a13b421e82f1034a0163fa07e90fb59f323e0c7b34f4a1e5b3c5e780ced19d503a2e7344e529c8638666fe8dc01b5436506b54d341a3c33ec66f4cc2194b323e6398c63988e30aa else 0xa5200dd0073c4cb06714003b0489801ec194540c008c192600c008c02e4f92f4845c204b00b1334a4a499b92bc88654d23393f899e0c9f953c88a463293133c19362188440c300830669414b53e2658324a51b00b1324a31f257918ca9a5062678326e54f23192b4a0c4cf064dca9e4ab232941899e0c982190e386d6064206506d80402063000d2929338932036e00f08c081901b60100818e11810ba43040c9486c0132902064846037290c103203f793e1031832e9401031d21b93f8e1c01436996b8933a3d1949499c0103ab12664465265949819263d3005499650624ca0f3038038060700700a92a0f608a32d70338a03042f0321140819192b0c984783ce919c98c5004530329c0c84141c03c01041c1c0307b23e7004cb5a49e280cc9507a83db93180246bd24f140806882941c03852c22196b819a521419e0e6e4c0380908806ad2541c04c01036690c108203969320e01e0081dd4990701019c0a81422a141499c0c901a2c95c0103808c9584542829338192c2229320e01e0641d22c01225596a0e0232a51ed499c0ce280ac9547b52670338a02834920d81907013005499c830380888806932541c0402700e50320262013803409d1e00821e0e4c4c8420aca9478d2930338992836c0201031842f10c110c0c840ca0f3a463293132115c0c9b93e0360488f03210fc4c840c9886c0cd2902064c0104281bb8990841793e0f508660671325c0103b41900f165262669267a4603d61e2ca4c0ce264d0c484503bb10c0f6c0cd28196a886242281e748807b6067132ca44600b13310607013005899a500420980205483469480e0282541b3819081911f28b6654831c1cd819a5062650ca907823db0334a0c4c9992a0c7078e0671334a0332551ed819a506264a0dcc4303930321032e0091ed4a0649e264b819a52426404c4027206413a3c0152902103654c266949819203d61334a4c0c9000e0e3c0cc265940564460661334a42300820a0e01d0671400ff1f0001ee0e9184498320ff192201ee0e9192201f00e91835d8320e20820098bc9287903a87402071040c6ca0075038060c7a0c83a87493c5204391ae407683211c549346b97924114143e78000f8889901aeca00840c1e1c9287ca38c801806de2182064084e2641ee0ff203ac1520d4652032e8326079c351949419865941a00f3c4303781fe5e4fb0641fe3e0004341fe307ff27c2043001623310d4a4081941d788c06103b294989960c9c1e60caa50040c8cb50700b80010e07f8c196ca40818f80010d07f8e9521110818d9400f807f8c1b489307f8f11810e07f8c0040d0c4304141c0508930641fe306c621819c0ea203ac18ac19075101dd01d27a724a1d05c43144c1c03c5003fc206307fe2191d01082030e948103183bd92a8e8070101eb4930748f8010df07f8f8) else (if i < 7 then 0x1061154861422a90c207592d85498079c3e47c0008003f070f906b0b0040d21035c0158881e28020c2005526460d7e00030c1e6408a041860d7c0c8e1ae0ca1009820d7079d254600ae00035860fd80103b8600ae00032870c68010818dc00077032898020e00838020830d1e8206523bc400d065080ba0b61324c2ca00925596a28038400e069120b828b6417081dc0f4c0c8e00e01d10068020265ad24c501a09256926280d0400e4ad120d820f307b0819e007e000d0341062801f800307703d8548c0d25428b64170900e107683d840c207a700060c8077f00060c8067f000648865a8a1150071522001a28450098448864988123007103b000fc001a0b820c2076700060f30130a910106403c440072528a9401061001e940307183469483871d27c40e306652807488083221c749f1d25420070488812281a1030800fc00183b4193899183b81e22061001e94030610327800386486918145b20b8400d0a3d0209140d0818e0f11031c01a204ce00840b6017009878020a06692a2c01041c74a41022801a2c01070041871d27c1ac3063033e9183601041961654c3a041140f0009ba286d041d9c0006183cc9c00073881ae0ece000c1ae025103081aec02183c41940f51d28020d7064f00060c2064b00860c306bf00060f5a460b8000f617002220207ae25450d40b0082c020838e9400d61c38c2182e000430194306403bf140306783138003061031180430638313800307803d85495083201962c44041fe0ca1138e93e0ca1830c196201100500200f0c5ab0640f18a001e240e0022a0c80d314003c0579c832070c5000f015e5e4a81cf1418b5a0c82bcc022643018c04b419c5ae28006e8c5001c082e08420c820415e700e628316ac19057940ca015a01018d96a0a33325793006fa0101d40740a33818d93340201d01241226a5ab06714003c057958058a025e8f92bc86a46628196bc1937257919c88e4f82ab8326e46722194941902a02d8dc9f646010394941902382d8e00fe4ab28283204805b1801fc9f60ca2d8800c061b067132073a5000f0f4a060ca2d8605c02772339414190400274e05e031500b132c93c5200dce05cc4af232832ca0c4c8200f48c031e293132c192d2200c78a4c4cb064bc8c006629183208005b180b9c9f00ba07500e040065729183207cc4c8081803201172d6833c9f01d8244eca9028623393f899a0c821406e8004f2a6805899c49b29006e7039f255941899a0c8244cc02062814393f88602652d71260374b0081dd4a9e4fa1431338933b00818a05e03462671274a401ba180589900a81cc0740a335283132c1904893953c9560cf24c01a0a8332a404f41903682a0a05c64a805683206c054180c1c95a0c81681225011030b919886012b06696b8a001ba40b8c194540c185ca9e466223132c19 else (if i < 8 then 0x80e2037282a41d8205483ac40c3a5030640e640656218548c004306694886f2929516c090061e266949c193e26088cc19039900274a060c81cc80b305d9282919899e0c990048b6162d7004285b6264406802700dc68a402880e41004207917009c0372103c8820390401081e02501300dc806802700dc7895c43235f80446010481202501300dc90a402880e41004013018a9534a001e14018026a54818a918008031b06714989951118078201180380ec063a5062658327c4ae2181cbc02230083895c4360087895c436008789507982d874a9c4a8904402601b8e9520f5c4a8c1660f3c5200dc94a9e4632200d805b2d2a712a2646040ca008004c1403a07418c003010159520be04d8134040504680f4106020202bb92a0c6001016c0406003831803a01f01b940e403201b8c02002401b8c8b80ee22580c806e522e112c020037200f80460fda5482d80040bf01ba31320c503900dc80c560101c806e484c81c806e3c4603f41ddc02230081dc2062e23004c07e01b9501e0c503f00dc9ca906281869480372d2a693e80f062804006e604f008c18208d078528003a0b8010240c607b00e30080e6074300558040730251011188c05f02bc06e5c54803b132c1922816952033a52014180404a3023c20c5048881dd88617254018cb525002f3832606382444898063f008788cc0103c0788c063f00860b6076e23074a90776230680f077004006e401f62301ea0eea5482d006e705703281e00bfc4600dcc09107772929520372d2a41e188c1d2a407c09701183ec17e00d01ba31320c203880dc845c038830a1420372a009114200101a013c08ec44039418405201ba71400c2028820098a0e0108844051061428406e503402301840bf02b80dcd4a900a808583285a282b392a0cb00101640406077700840c2a5a82fc09a0372802f140c1903991086c190398e9180c2018815c100500181a80e2023a4601af1338a060ca40d54a9a4a803983285a30320122244c03238043c44600858a0064700860c7065024460c8048899520f005fd23006e5a4603c31103845048044b2112c824efe01089601a46133f8043601078041a4650084ca9a460a92a124985952c02103ef804202f030c54020d22020caa01081864a51127c187c021d2828042646032a9103a5050081943061d25440cbe0108187c0215008249f061f00874020d2302ca9601098041646300840f900ee06478190780a1f389207f0c1af81900e8f0321012e2484026083971240c71e0641dc2c01037040c400ee064601dc4983f870c4c4903c0601d06de06478020a2b503b8191a077032247a62484091c0ca07860cd40e891c6c9f0668e14b4a4100280d22654841dc0f4c0c8c15f4931423e926200502bc40f307b0819e00ae000c1840f6e000c1dc0f6152303495083201ec2c0 else 0xb9043803416c404302e410e0b82500807d4991821c177499192d410e0bb180a410e0a60529015e087a520e152c02057828884a904382886c0205d82be96a4a4302bc10e0912024410eca41d008122204482a41563006d2804c020578a9108b60220c16d80205de26015e500602ed05a305b00301763002e25710c025e011410e8a71200801802518178206801330080184c01625404a0912021c9442401003004a300600998043002e25710c025e0114919802c4ae2188c02a54e25460afc01024003e400602ec0dc304882b80183055e2300d00ae006140180af1007c0a4090182440882052d0080714a0212540d00901b00815e2010028854a964462300884a5481a401a3006e0081760af202ec1164ba182b401a0bb181900d18a01801401b888e011000a0911009c0460151801401b888e011005340201c02cc8495c0162206c02654d233110403282e00943062f293933c1905794005ca405780dc800a032817417004a281780e605618178103419039901e3c0210308102c190399216a08160c81cc9ca4e4cf06415e40617261832053202202088083c78042c4c83ad80407601b971320eb60101c806e5076a2d85899075b0))))

def moveIndex11 (i : Nat) : Nat := (if i < 1 then 0xa063f0951033181c52123c063a8293449cc0ed5009a8b0cc69d00b2b8a300001400381182b0340904a8176137f35f02b100000c098214ec801bc1eea0506122800000001620c21bf6049dc690a204b0a1604b4829c62a9a0a46033d844e803c5060800000001e17db11e585ba427d800790af5ab8242b58129d08298a704250614fc04bf012080e80000a04788a30c12820b7918568930000022aa603e505a6404902ced0159b29c003e20b000000000282d1009b00005043f44fce10bf12820a84409ac065110910971c4a36200000070218c6be60a6c078c8032c111c042e0b500000003d80e790680201545eba117b1501044a85664023c01bd009842a162848161404db415e0000303798a200001cab6215b704ed86ec827d81b9b0aa0c2680000b04080002469e0000719fa80fe427e0000000078231c18da152f05008074450563079177902248101e4f65300609ef0420c09a22a01047d04aa80c90000284c94067009c709600003813ce178506ed05dc42628043e0a5f83a74168e30d1078000010271002a9122002f1c15a00001068e8a28413a00000000000014619c06420618000000006295b1900000000000000000078ad482560000311a000020191a32ce0758000386c40000e041488c40648626f000030cc8c14241150000285b400000000a093301dc0001e041a173080ebc5770321e038d85440000237f000008d2b015c815d0138d023b51a654fc0012f80b3406d0106b062f091cc50760660087109b642ffe8d9b00c2009c80ad44dc618358554020220a7203b784454629c01cd06ac83a880516149a03760a1600fb4016c056282ef86a3a0904010b00e31a82610dd0b9c355e44eb20fde15ec8308000170f6c0b8f82a141b9801ad00a183cb0301611ba02cd03f8000060b19125389dd81b4e2f3e099c0467028ca072000078a6c00000179d1435a06b00762078b034b002c054980df90010000342ac0000101741b1341954ec1315900807c80f604b2046b821e84770093086fa018002f6c04a90be68125c49e61025030e827d023be0bfc02e80002067b8099a06588a02c0d50120d104a08ad01bcc0a922aba89cc0001e2bc30230089800014052208000a8b00228cf6310458dd5c27b400400342e340006023f010a002997040204270a014223012323000001195d04015c0fd00036eb0682004c002501231b0a0316114801032004000002e2460d14130008030000200a031b10cd000106694400010f631d650109ab07112b130e048a06022c6c000100000003000a1c180605000c000e203a00160008026e04013300010012058202062c04670e080e06331a0b100016250b0108010717020104093b010d00001200000b100c00000045030e1d000100631701020709050000040100011a18022001020915020201000103 else 0x169001077800008e83a23ec06a00000000022eb0000000000001e044103980000c2cc0000d00da017b02e8a0fca04b00003852e61760000603340001c1720000000000000c3348144a81ae85038029705f10153c2d96040613225bb142afa170607fca29c041aa32d509aa13808682821c901a505f8c0e0233bc081e81ed463e40d8b036203e9c173c2cb7157f815541f78091180328935444b20686097f028b457f40e87009480fa0575e0b3615bb0ad1c16ca0f810b3b8caf42b3235b70bd185bc82156342609e6036ec57304060007a83bb408f2cbe30a2680148180e00eb004b81390014a16b11179902b80a302a3c202e029642138323608b58cdbe9ff2003100ba88b0c6606045f197f09210000c30e2084104c300be8121c01ca024901a5e160307a989e30249a364c04a980c3440f20e0a0b2e857c023d2238902bd8d2d8670224b204560313c2c2a20fc146b03d9006a228ba070c8cd6c46a42ac50a550536c2c74d16f0426844f01c6e242940368ae1468ae2900082604b8c146e2adb13e1045306ef211000baa836440214354302c28997c010213a2045980f5448d8122e02dc90004475805cd017890228235405a906760b0382836153a11eb8055058861259006d8472c0ffa70130a6703e442b6808540103020f528c02ab3069a00b704b7e053705d18592861ec162103ac81b6809e86fe6055a02d7848062395083984e6c1d8c14320189039400ce60e6205ee0390c6b0207ae147d83d141e7c10c70a00035e42b9628ef10548af980f3e0d60157485178065a0b8d158b0d83828fa062b011585506983c25960260056380334257b0554895280fc)

def liveData10 (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0x9ef9c6aed8148200df6abb5495148200fb6a885495148200ff61526055148200ef5a5568d3148200dbeabba212148200dbea886d52148200df6abb9552148200fb6a889552148200fbca888cd2148200ff4a558cd2148200fbe2884c52148200ff62554c52148200ef71a89561148200fb72889561148200ebf28868e1148200ef725568e1148200fbd2888ce1148200ff52558ce1148200fbe28854a1148200a7f8c96cda544200c7f8b96cda544200a7f8c96c9a54420097f9c22e5a544200d3f8b9a21a54420097f8c96e98544200e778b9955a344200eb7a88955a344200d3f8b9a21a344200a7f8c9695a344200d778b9955a34420097f8c96e9834420097f8c96e95344200e7d8c96963344200b7d8c96963344200fb5a889563344200eb7a88955a244200ebda888cda244200ef5a558cda24420097f8c96e982442009df9c7aed524420097f8c96e95244200cf79ba9553244200e7e8c96962244200ebea886962244200b7e8c96962244200afe9ca6162244200ef69a89562244200fb6a889562244200ef6a5568e2244200efc9a88ce2244200fbca888ce2244200efc9a58ce2244200ff4a558ce2244200b7f1c22e55144200b7f0c96e15144200cff2bb6a15144200dbf2bba215144200f3f0b9a215144200b7f0c96cd5144200b7f0c968d5144200dfd2bb8cd5144200f7d0b98cd5144200fbd2888cd5144200b7f0c96c95144200bf72cc5495144200df72bb5495144200f770b95495144200ef71a85495144200fb72885495144200ff52335495144200ff61825495144200dfe2bb8895144200f7e0b98895144200efe1a88895144200fbe2888895144200ffc2338895144200bbe8c96095260600cfe8b988aaa54600ebea8888aaa54600cfe9b8888a954600ebea88888a954600afd8c9aaa3354600efca22aaa3354600efca222a633546008ff9ca2e582546009fb9c42e58254600efe222aa98154600efd2aa8cd8154600ebf2aa6098154600bbf0c96098154600ef72aa5498154600ff523354981546008ff9c52e6aa4c600cf7a552e6aa4c6008ffacc6d4a94c6008ff9c52e5a84c600abf9c52a6884c6008ffacc2e5a54c600afe8c9696224c600ef7255aa9814c600ff6255889814c6008ff9c52e5a848600cf7a552e5a848600cbfabba21a548600cbf8b9a21a5486008ff8c96e985486008ff8c96e95348600afd8c969633486009ff1c52e58284600df72552e58284600fbd18354d8284600ff515360d5284600fbd2888cd5284600bfe0c960952846009ff0c96d53284600dbf2886d53284600bfe2cc54e2284600bfe0c954e2284600bfe1c854e2284600fbe28854e2284600ffc18354e2284600ffc1858ce228460097b5c42e58284600fb61825498154600fbc1824c9814c6009fb1c42e58284600ff42558ce2284600 else 0x87fecc6e0a94c60087fecc6d4a94c60087fcc9aeda84c60087fecc2e5a84c60087fdc52e5a84c60087fdc22e5a84c600a3fecc2a6884c600a3fdc52a6884c600a3fdc22a6884c60087fecc2e5a54c60087fdc22e5a54c6008ff9c02e9824c60087fdca2e5824c60097f5c12e5824c60087fdcb2a5824c600a3fdc82a5824c60087fdca2e5524c60087fdcb2a5524c600a77dc52a5524c60097dcc9aed324c600d3dcb9a21324c600a7edc82a6224c600a7edc52a6224c600a7ecc96a2224c600e3eca9a22224c600a7ecc9696224c600b3f4c9609814c600b7d4c94c9814c600fbc5824c9814c60087fecc6e0a94860087fecc6d4a94860087fcc9aeda84860087fecc2e5a84860087fdc52e5a84860087fdc32e5a848600a3fcc9aaa8848600a3fdc52a68848600a3fdc32a6884860087fecc2e5a54860087fdc82e5a54860087fdc32e5a548600c3fcb9a21a54860087fcc96e9854860087fdcb2a5854860087fcc9aeda34860087fdc82e5a34860087fdc52e5a348600c3fcb9a21a34860087fcc96e9834860087fdca2e5834860087fdcb2a5834860087fcc96e9534860087fdca2e5534860087fdcb2a55348600a7ddc82a63348600a7ddc52a63348600a7dcc96a23348600e3dca9a223348600a7dcc9696334860097f4c9aed858460097f5c32e5858460097f5c22e5858460097f4c9aed838460097f5c52e5838460097f5c22e5838460097f4c9aed538460097f6cc2e5538460097f5c82e5538460097f5c22e5538460097f4c96e15384600d3f4b9a215384600b7d4c960d5384600b7d4c9616338460097f4c9aed828460097f6cc2e5828460097f5c52e58284600d7b5c42e5828460097f5c32e58284600b7b5c42e58284600d774b99558284600d7d4b98cd82846009df5c7aed528460097f5c82e5528460097f5c32e5528460097f4c96e15284600d3f4b9a215284600d7d4b98cd5284600b7e4c9609528460097f4c9aed328460097f5c82e5328460097f5c52e5328460097f4c96e13284600d3f4b9a21328460097f4c96d53284600d774b99553284600b7e4c96162284600fb66889562284600b7e4c960e2284600b7e4c954e2284600fbc6888ce2284600ff46558ce22846009ef9c6aed814c20097facc2e5514c200d7d9c32e5514c20097f9c22e5514c200d7d8b96cd514c200d7e8b9889514c2009fd9c5aed314c200bfd2cc605314c20097f8c96d5214c200dfd2bb4c5214c200b7f0c9696114c200bfd2cc54e114c200f7d0c954e114c200fbd28854e114c200ff518554e114c200ff515354a114c200fbe28888a114c200ff625588a114c200ffc15388a114c200b778c96a25548200eb7a88955a348200fb5a889563348200dbeabba215248200bf6acc54d5248200fb6a8854d5248200ff498354d5248200fbca888cd5248200) else (if i < 3 then 0xa7fdc52a5a160a00c7fcb9695a160a0097fdc82e5a54ca0097fdc12e5a54ca00c7fcb96a1a54ca00b7ecc96d5824ca00b7ecc9695824ca00a7fcc9695a14ca00b3fdc52e58260600b3fcc96d58260600d3fcb96d58260600aefdc6aa95260600c7febb2a55260600a7fdc32a55260600f3ecc96095260600aefdc6aa9326060097fdc52e53260600a7fdc52a53260600a7fcc96e9825460097fdc32e58254600a7fdca2e58254600c7fdba2e58254600b7bdc42e58254600a7fecc2a58254600c7febb2a58254600a7fcc96e9325460097fdc82e53254600a7fecc2a53254600c7febb2a53254600a7fdc82a53254600c7fca96e13254600e7eca96093254600f3f4c96098154600b7f4c94c98154600d7f4b94c98154600fbe5824c9815460097fdc52e5824c600a7fdc52a5824c600a7fcc9695824c6009dfdc7aed524c600a7fcc9aa9524c600afedc2aa9524c600c7feaa2e5524c60097fdc82e5524c600a7fdc82a5524c600a7fcc96a1524c600c7fcb96a1524c600afecca609524c600b7ecc9609524c600ebeda8609524c600b7dcc96d5324c600ffc5c1609324c600b7f4c9549814c600fbe582549814c6008ffdc3aeda848600c7febb2a58548600a7fdc32a58548600a7fcc9aa9834860097fdc52e58348600a7fdc52a58348600a7fcc96958348600c7fcb9695834860097fcc9aed5348600a7fcc9aa9534860097fecc2e55348600c7feaa2e5534860097fdc82e55348600c7febb2a5534860097fcc96e15348600c7fca96e15348600a7fcc96a15348600b7dcc960d5348600e7dca960d5348600b7f4c96153148600c7edc22e6aa60a00a7edc22e6aa60a00a7becc6d0a960a00c7bdb46c4a960a0097becc6d0a960a00a7ddc12a63360a00a7bdc42a5a160a0087fecc6d4a94ca0087fdc12e5a84ca0097edc52e58388a0097edc12e58388a0087fecc6d4a96060087fecc6cca96060087fecc6c8a960600aeddc6aaa3360600a7ddc52a63360600a7ddc22a6336060093fcc9aed826060093fecc2e58260600c3feaa2e58260600d3bdc42e58260600b3bdc42e58260600d3dcb98cd826060087fdcb2a55260600b3ecc9609526060087fdca2e5326060087fdcb2a53260600aeedc6aaa2260600a7edc52a62260600a7edc32a62260600e7cca98ce226060087fecc6cca954600a7decc2a63354600a7ddc22a6335460087fdca2e5825460097bdc42e5825460087fdcb2a5825460087fdca2e5325460087fdcb2a53254600a7eecc2a62254600a7edc82a62254600a7edc32a62254600e3eca9a222254600e7cca98ce2254600c7f6aa2e58154600d7d4b98cd8154600b3f4c96098154600d774b95498154600fb65825498154600d7e4b98898154600c7bdc42e6aa4c600a7bdc42e6aa4c60087fcc96d6aa4c60087fcc96caaa4c600 else (if i < 4 then 0x1340371804801b880150809a01b8804d00d44041006e20004037100ae0400807900dc44180400b0a804102804101a420338447d0815a20b88061080c2160084171004e101ac2e500406b0800610818020d8321a008202f04063080bc100838102582028040500b00410020880811e20b88013080261018c20600820000000038190f1260140800108024100143c490400000789210000011e810038920f1241238c20c248200000f60f800103d83e000400f0000c31410c1040041021f2143e4380104000028920d12410008f40800210004819100021001420000420c248200005019100001080021000000000010f8001000428490400011301626020a2482c4c04000000a10014200000050800a10000f60800a100000c0c92a1003c000800071860e30c1c6100942002130100000001420128400000181001941007c300c040050800a10000210020c90800a1021b010000210004200000ca081941d27c200493e100000138c20d2d74a01074606be10c07b81d24044689303fc620c694007f8f899937c5facfc5fdabeaff44f98fc7be17ef8f72fb4bd7fe9ef3ef973c93e28f03f79bba7db2ecff633af3d58e9bf493a07ce2e60f2838ffc6ce33f15389fc3ce0defeb7b3bb8dc4eda368fb26d7beb5b56ba94d39e98349ba3ad13e81b3cb9c4cd1e60b2c3940c8fe3fb1bb8bcc4de1eb0b3838c0bdfdafab7d0bdedeaaf2f784bb8dd42e7b72ab76db32d57698b42d992c87622b07d7f2bd35d6ae1d6c2b03552a9fd4429df4c0a4fd2328f3466a30d0ca83f40c9f5ceba6ff35e99eccaa62f30497fcbea5cf2d4959ca824c7250917c83a3db1be8c7c5ba263110877c33a1770a884ac1d20a704080fbff9f9efae7c6bd79e7af2a78bbc11de2ede76cbb19d4ae92731b8d1c26de46e1b689b02d6e6adb521a4ecf866bb311946c74622b0597eabe25e0ae816feb5e59eac71612af6571ab79596ab8552aa494e2a5e525a8a942ea044f8a7793b29c64e0a6b93369884baa58929e94a49ba4912228fe475a3991c28ce456a26910e874437a1710ae852426a12108683e41ca09900a7f23ef9f30f727b43d79e38f127843bf9de8ece7623ae9d28e6e72438f9c30e0e70237e9ba8dae6c43589ab0d4e68633999b8cb665632198c0c3a6183099838c125f62f19778bb25c62d99648afe56c2b39550a9e53c29b9458a224fe27593989c24dc26b934899a4ba253925090247c23b91c88be44c22390d084241c20b90487fe3ec1f38f887ba3ca1db8ec875a39a1c38e086fa36a1ab8d4869a33a19a8cc063a30a17b8b905be2da1638b0857a2b81598a8051a28814189f84d6266129890045a21a10388083de1ea0f2874837e1ba0d3868831e17c0bb85c82da15a0a384d025e12a08b844821a10808183c01d60bc03f814004200097fdc52e5a160a00 else 0xb0082611010825010081158041b0083a4a870a9080d01b254202f04006081021d00b4a0100a0037880440140402f0740202704033007420030013138041000c026158041629c202f040260178402f004c270082032804c20098013100260130801300bc4002804c2923020018c2002cc20310020201780141001802f0b8020240440b80840480c0240110400800a02017c0101693e02800663003004c10018016080a50240401280c4202203047840ae0e118100300901000404708067002c403000ce2003406110006005880660184403400c2201a004f1000600d8800d009c401380162002c0271000600588027002c400180162001400b1000a01388124a8406b080ba10174220c840730158402f064020e16a04098320399002100f04026806e2018420308400500f0402a80e6201c40371012e101bc203784c020a152142a4201f80c601d0cc19d2800731c1521000804500d460278074200ac04d00dc6026806a2025c20378406f08002301e80371804c172802012806e210734a9d28003c2001e041006a30094037100b0040080260f1321900820000de101bc20128062201f82034018604a00b6401bc200880b62000c0161010401008017007c03c1805402a80e6300900371005400b80fe01b9005501cc401e806e201340351002019008200a8400500f0402b81002f0002026806e2003c03110056026806a300240771005a0400805c00f40351801203f08c02080261e264320105402081402080c4018880370815e05f806e300a807100dc6012006e200a807f00dc602a80e6200900371009a01b8800d080161002c20028078200ac07f00dc603e806e230082000806e200ac04500dc600b81040100c02b0)))

def moveIndex10 (i : Nat) : Nat := 0x2814a92ba1ecc25199c0118cda13d7290300000218c0001

def liveData9 (i : Nat) : Nat := 0x1782e29c200000c08025008820000060400917d69645f4b28231e0a0500a2feebd7654aa4c0c0173add432582549818030f7b74e2172c12a3005ced750c96098154600f9b26cb04a9302a8c0173e4d96095260531802e6c9b2c12a4c0aa30055cd750b99558284600f5b155304a9302a8c017b60d960952605518033e64aae2172c1423007ed0a22558ce2284600

def moveIndex9 (i : Nat) : Nat := 0x1

def liveData8 (i : Nat) : Nat := 0x2f325e4365825498154600

def liveLevels : Nat → Packing
  | 14 => (2,1,9,0,0,7,0,liveData14)
  | 13 => (21,2,9,0,0,11,0,liveData13)
  | 12 => (174,3,9,0,0,14,0,liveData12)
  | 11 => (588,4,9,0,0,15,0,liveData11)
  | 10 => (385,5,9,0,0,13,0,liveData10)
  | 9 => (12,6,9,0,0,8,0,liveData9)
  | 8 => (1,7,9,0,0,0,0,liveData8)
  | _ => emptyPacking

def liveIndex : Nat → Nat → Option (Nat × Nat)
  | 14 => lookupWord 16 44 4 10 5 1 moveIndex14
  | 13 => lookupWord 93 296 7 16 8 4 moveIndex13
  | 12 => lookupWord 296 980 8 18 10 4 moveIndex12
  | 11 => lookupWord 206 669 8 17 9 4 moveIndex11
  | 10 => lookupWord 8 20 3 9 4 1 moveIndex10
  | 9 => lookupWord 1 2 0 4 0 0 moveIndex9
  | _ => fun _ => none

def orSamples : Array (Bits × Bits) := #[(0x4041d9800230081ff0f898380810200339c230000220000446300000043fff91e0000c780518e060c47f41e1800044080600000f043f9e1fdf0000780071b071f80e187c1e60c10c00014011ff61fc7ffffff41c0000fffff1e0003e0003ffff,0x400159800024080160ba9c100000000339c23521000000006224c88000089ed1e92228500508e060403f41e18000040806a8080b00019e085e54102800201020f002182c0660910951000000002024442a883415510022a221ea881ca8815425),
  (0xf800e03cfc0711c1f00e038100001c1c003c000003f009807c00001c7c3001e00000ffa4601018107907f01f8f07830f80000301830601fe00000790f8e419e1ff12083e180fffffffe781e31819f83800007e0000718001e00003fffffffff,0xd800643cf8871141f0060200000018040010810303b809805c804614283400e101186a8020100010080120038a96910e902873058344093a0830c400082408008600000e0804416087a681421810883c105034208e11c119c1046210476231a),
  (0x8001001040041e06000ffc5e01c7e0201fc00000bc000e07800000607fc03e000000f83801e0001f81f81fe0300003f000000001fc07fe0ffffff860ff07e1fe001c0fc01ff01f00003801fc1fe1ffc000018000007e0001fffffc7fffc0000,0x60200009c5e01c7602017c03098bc0082078028284056c1360030a0942801e0000100001260300002e0060280000c00200533053860b703a1fa109c0f6112d01a0c50181098808177418481800c506e18a004629466288c0a4),
  (0x9001e00208007e007fff000600e04003fe0000000c0000ff80000007f80003fffffff00407e001fe001ffe001c007fc00000003fe0007fff00000007f0007fe00001ff0001fffe000003ffe001ffe00000001ffffff800001ffffff800000000,0x9001a008080002000213000000e00001de000036100000d700800d30000000866034f00007e090e8001bfe0110007fc0400b121a600179dd08062400700045e00240150000d2fe001a200a4001f3e001032184741a4800349f80d2b00d200648),
  (0x1ffe0003f0007fff80000007ff007ffc000000000fffff0000000007fffffc0000000007f80001ffffe000001fff80000000003fffff800000000007ffff80000001fffffe0000000003fffffe00000000001fffffffffffe000000000000000,0xffa0003f10075de80004107ff007b6c00100a482ffddd00000b1247ffb3600012490007f8000113bec000100fff80048154242496fe000000a849058ddf88080401e2c3d8040002a453f5bffc00022254460b8aa4b7dd494015240152528890),
  (0xe0000003ffff800000000007ffff8000000000000ffffffffffffff80000000000000007fffffe00000000001fffffffffffffc00000000000000007fffffffffffe0000000000000003ffffffffffffffffe000000000000000000000000000,0x4000000000000006bdbd80000400000c3ace1eff88d0037800000004000dc006da540400000000040a33c877080037800000000000006e07dfdbefdd0ffc0000801820000663ffdfffdddbbb8077c00006c4000d80003700036000d8),
  (0xfffffffc0000000000000007fffffffffffffffff0000000000000000000000000000007ffffffffffffffffe0000000000000000000000000000007fffffffffffffffffffffffffffc00000000000000000000000000000000000000000000,0xd04df88c0000000000000006ded9424b9658506fc080100200001b8000000000006e0007f5feffdeff7de5bfc00202000018380800801100000c7007ee6d3f7fd78fbffb1d7fb9c83780060100000040067800003700806e0001b8001b800ce0),
  (0xfffffffffffffffffffffff8000000000000000000000000000000000000000000000007fffffffffffffffffffffffffffffffffffffffffffffff8000000000000000000000000000000000000000000000000000000000000000000000000,0xfeeffdefaffeef9b5bdff6380000000000000c7000000000000c1c00220080015c7002012581d9fde7fef8d9f4cc3780f79fc03fff2ffdfeaccf8070000000000000040000000003380000000000000067800013380016700919c0019c030f00),
  (0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x2f300773b7ff7dfffce4ffb900023db021a3af800530e000772fe007b7fefb799f800ff000000000000000000000000005e000000008000010f00000000000000000000000000003c00000000000000078000203c0000780001e0001e003f000)]

def orSymmetries : Array (List Nat) := #[[],[81,130,118],[16,82,131,100],[16,32,48,128,100,80,116],[32,83,116],[32,49,128,81,116,100],[48,33,133,118],[48,129,82],[80,16,33,50,116,131,100],[80,129,50,116],[128,49,100],[128,81,32,49,100,116]]

def orCols : IndexTree ColumnInfo := (.fork 139 (.fork 69 (.fork 34 (.fork 17 (.fork 8 (.fork 4 (.leaf [(0,0,511,0,15),(0,1,460,50,8),(1,0,510,0,12),(0,2,440,69,8)]) (.leaf [(2,0,509,0,12),(1,2,440,68,7),(2,1,460,48,7),(3,0,508,0,9)])) (.fork 4 (.leaf [(0,4,369,138,8),(4,0,507,0,12),(5,0,506,0,8),(6,0,505,0,9)]) (.fork 2 (.leaf [(5,2,440,64,6),(7,0,504,0,7)]) (.leaf [(0,8,227,276,8),(8,0,503,0,12),(10,0,501,0,8)])))) (.fork 8 (.fork 4 (.leaf [(11,0,484,0,5),(8,4,369,130,7),(12,0,499,0,9),(10,4,369,128,6)]) (.leaf [(14,0,497,0,7),(15,0,480,0,4),(0,16,486,9,10),(1,16,486,8,9)])) (.fork 4 (.leaf [(17,0,494,0,11),(19,0,492,0,8),(6,16,480,9,6),(8,16,486,1,9)]) (.fork 2 (.leaf [(9,16,486,0,8),(25,0,486,0,8)]) (.leaf [(11,16,484,0,5),(15,16,480,0,4),(0,32,94,385,8)]))))) (.fork 17 (.fork 8 (.fork 4 (.leaf [(32,0,479,0,12),(1,32,94,384,7),(32,1,460,18,7),(34,1,460,16,6)]) (.leaf [(35,0,476,0,7),(40,0,471,0,8),(50,1,460,0,5),(41,16,454,0,5)])) (.fork 4 (.leaf [(0,64,189,258,10),(64,0,447,0,13),(64,1,396,50,7),(65,0,446,0,9)]) (.fork 2 (.leaf [(67,0,444,0,8),(64,4,305,138,7)]) (.leaf [(70,0,441,0,8),(69,2,440,0,5),(74,0,437,0,7)])))) (.fork 9 (.fork 4 (.leaf [(74,4,305,128,5),(82,0,429,0,8),(81,2,424,4,5),(83,0,428,0,7)]) (.fork 2 (.leaf [(85,2,424,0,4),(65,32,30,384,6)]) (.leaf [(98,0,413,0,7),(98,1,396,16,5),(112,1,396,2,5)]))) (.fork 4 (.leaf [(114,1,396,0,4),(129,0,382,0,9),(129,2,312,68,6),(130,1,332,48,6)]) (.fork 2 (.leaf [(4,128,347,32,9),(132,0,379,0,11)]) (.leaf [(132,2,312,65,6),(134,0,377,0,8),(133,2,312,64,5)])))))) (.fork 35 (.fork 17 (.fork 8 (.fork 4 (.leaf [(136,0,375,0,9),(140,0,371,0,8),(148,8,99,256,5),(152,4,353,2,5)]) (.leaf [(156,0,355,0,7),(154,4,353,0,4),(160,0,351,0,11),(160,1,332,18,6)])) (.fork 4 (.leaf [(161,0,350,0,8),(162,0,349,0,7),(162,1,332,16,5),(36,128,347,0,8)]) (.fork 2 (.leaf [(38,128,345,0,5),(39,128,344,0,4)]) (.leaf [(44,128,339,0,5),(145,32,78,256,5),(177,0,334,0,7)])))) (.fork 9 (.fork 4 (.leaf [(178,1,332,0,4),(193,0,318,0,7),(194,0,317,0,8),(193,2,312,4,5)]) (.fork 2 (.leaf [(198,0,313,0,7),(197,2,312,0,4)]) (.leaf [(256,0,255,0,12),(257,0,254,0,8),(260,0,251,0,8)]))) (.fork 4 (.leaf [(8,256,151,96,7),(256,8,227,20,7),(264,0,247,0,9),(260,8,227,16,6)]) (.fork 2 (.leaf [(268,0,243,0,7),(265,16,230,0,5)]) (.leaf [(32,256,151,72,7),(256,32,94,129,7),(288,0,223,0,9)]))))) (.fork 17 (.fork 8 (.fork 4 (.leaf [(257,32,94,128,6),(289,0,222,0,7),(40,256,151,64,6),(296,0,215,0,7)]) (.leaf [(273,32,78,128,5),(56,256,135,64,5),(321,0,190,0,7),(258,64,189,0,8)])) (.fork 4 (.leaf [(324,0,187,0,7),(262,64,185,0,5),(266,64,181,0,5),(270,64,177,0,4)]) (.fork 2 (.leaf [(340,8,163,0,4),(320,32,30,129,6)]) (.leaf [(291,64,156,0,4),(104,256,151,0,5),(120,256,135,0,4)])))) (.fork 9 (.fork 4 (.leaf [(384,0,127,0,9),(384,8,99,20,6),(388,8,99,16,5),(404,8,99,0,4)]) (.fork 2 (.leaf [(416,0,95,0,8),(385,32,94,0,5)]) (.leaf [(168,256,23,64,5),(401,32,78,0,4),(390,64,57,0,4)]))) (.fork 4 (.leaf [(480,0,31,0,7),(449,32,30,0,4),(356,128,27,0,4),(232,256,23,0,4)]) (.fork 2 (.leaf [(4098,0,2557,0,12),(4096,4,2417,138,8)]) (.leaf [(4100,0,2555,0,12),(4098,4,2417,136,7),(4102,0,2553,0,9)]))))))) (.fork 69 (.fork 34 (.fork 17 (.fork 8 (.fork 4 (.leaf [(4096,8,2275,276,8),(4104,0,2551,0,12),(4106,0,2549,0,8),(4104,4,2417,130,7)]) (.leaf [(4108,0,2547,0,9),(4106,4,2417,128,6),(4110,0,2545,0,7),(4112,0,2543,0,13)])) (.fork 4 (.leaf [(4120,0,2535,0,11),(4122,4,2401,128,5),(4128,0,2527,0,12),(4132,0,2395,0,8)]) (.fork 2 (.leaf [(4096,64,2237,258,10),(4160,0,2495,0,13)]) (.leaf [(4162,0,2493,0,11),(4166,0,2489,0,8),(4170,0,2485,0,7)])))) (.fork 8 (.fork 4 (.leaf [(4108,64,2225,258,6),(4194,0,2461,0,7),(4096,128,2395,36,10),(4224,0,2431,0,13)]) (.leaf [(4228,0,2427,0,11),(4230,0,2425,0,8),(4236,0,2419,0,8),(4252,0,2403,0,7)])) (.fork 4 (.leaf [(4256,0,2399,0,11),(4132,128,2395,0,8),(4140,128,2387,0,5),(4288,0,2367,0,11)]) (.fork 2 (.leaf [(4294,0,2361,0,7),(4352,0,2303,0,12)]) (.leaf [(4354,0,2237,0,8),(4356,0,2299,0,8),(4352,8,2275,20,7)]))))) (.fork 17 (.fork 8 (.fork 4 (.leaf [(4360,0,2295,0,9),(4356,8,2275,16,6),(4364,0,2291,0,7),(4376,0,2279,0,8)]) (.leaf [(4128,256,2199,72,7),(4384,0,2271,0,9),(4136,256,2199,64,6),(4392,0,2263,0,7)])) (.fork 4 (.leaf [(4416,0,2239,0,11),(4354,64,2237,0,8),(4418,0,2237,0,8),(4420,0,2235,0,7)]) (.fork 2 (.leaf [(4358,64,2233,0,5),(4424,0,2231,0,8)]) (.leaf [(4366,64,2225,0,4),(4430,0,2225,0,4),(4440,0,2215,0,7)])))) (.fork 9 (.fork 4 (.leaf [(4256,256,2071,72,6),(4264,256,2071,64,5),(4576,0,2079,0,7),(4452,128,2075,0,4)]) (.fork 2 (.leaf [(16384,4,8561,138,9),(16386,4,8561,136,8)]) (.leaf [(16390,0,8697,0,10),(16384,8,8419,276,9),(16394,0,8693,0,9)]))) (.fork 4 (.leaf [(16388,8,8419,272,8),(16392,4,8561,130,8),(16396,0,8691,0,10),(16394,4,8561,128,7)]) (.fork 2 (.leaf [(16398,0,8689,0,8),(16400,4,8545,138,8)]) (.leaf [(16402,4,8545,136,7),(16408,4,8545,130,7),(16424,0,8663,0,9)])))))) (.fork 35 (.fork 17 (.fork 8 (.fork 4 (.leaf [(16384,64,8381,258,11),(16448,4,8497,138,8),(16450,4,8497,136,7),(16454,0,8633,0,9)]) (.leaf [(16458,0,8629,0,8),(16456,4,8497,130,7),(16458,4,8497,128,6),(16482,0,8605,0,8)])) (.fork 4 (.leaf [(16384,128,8539,36,11),(16514,4,8561,8,7),(16518,0,8569,0,9),(16512,8,8291,276,8)]) (.fork 2 (.leaf [(16516,8,8291,272,7),(16524,0,8563,0,9)]) (.leaf [(16528,8,8291,260,7),(16540,0,8547,0,8),(16538,4,8545,0,5)])))) (.fork 9 (.fork 4 (.leaf [(16416,128,8539,4,10),(16546,0,8541,0,8),(16420,128,8539,0,9),(16548,0,8539,0,9)]) (.fork 2 (.leaf [(16422,128,8537,0,6),(16428,128,8531,0,6)]) (.leaf [(16578,0,8509,0,9),(16582,0,8505,0,8),(16586,4,8497,0,5)]))) (.fork 4 (.leaf [(16486,128,8473,0,5),(16384,256,8343,104,9),(16644,0,8443,0,9),(16392,256,8343,96,8)]) (.fork 2 (.leaf [(16640,8,8419,20,8),(16648,0,8439,0,10)]) (.leaf [(16644,8,8419,16,7),(16652,0,8435,0,8),(16664,0,8423,0,9)]))))) (.fork 17 (.fork 8 (.fork 4 (.leaf [(16416,256,8343,72,8),(16672,0,8415,0,10),(16424,256,8343,64,7),(16680,0,8407,0,8)]) (.leaf [(16432,256,8327,72,7),(16440,256,8327,64,6),(16642,64,8381,0,9),(16708,0,8379,0,8)])) (.fork 4 (.leaf [(16646,64,8377,0,6),(16704,8,8355,20,7),(16650,64,8373,0,6),(16708,8,8355,16,6)]) (.fork 2 (.leaf [(16654,64,8369,0,5),(16658,64,8365,0,6)]) (.leaf [(16728,0,8359,0,8),(16666,64,8357,0,5),(16724,8,8355,0,5)])))) (.fork 9 (.fork 4 (.leaf [(16732,0,8355,0,5),(16480,256,8343,8,7),(16736,0,8351,0,9),(16488,256,8343,0,6)]) (.fork 2 (.leaf [(16504,256,8327,0,5),(16512,256,8215,104,8)]) (.leaf [(16520,256,8215,96,7),(16768,8,8291,20,7),(16772,8,8291,16,6)]))) (.fork 4 (.leaf [(16784,8,8291,4,6),(16788,8,8291,0,5),(16544,256,8215,72,7),(16800,0,8287,0,9)]) (.fork 2 (.leaf [(16552,256,8215,64,6),(16774,64,8249,0,5)]) (.leaf [(16864,0,8223,0,8),(16802,64,8221,0,5),(16740,128,8219,0,5)]))))))))

def orForest : Forest := ⟨2559,14,fun j => orSamples[j]?.getD (0,0),orCols,orSymmetries,liveLevels,liveIndex⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem orGeometry : graphValid orForest (boundsBefore entries2551) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=6) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem allAt14 : block orForest 14 0 2 = true := by
  apply wideBlock (depth:=0)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem allAt13 : block orForest 13 0 21 = true := by
  apply wideBlock (depth:=3)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem allAt12 : block orForest 12 0 174 = true := by
  apply wideBlock (depth:=6)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem allAt11 : block orForest 11 0 588 = true := by
  apply wideBlock (depth:=8)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem allAt10 : block orForest 10 0 385 = true := by
  apply wideBlock (depth:=7)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem allAt9 : block orForest 9 0 12 = true := by
  apply wideBlock (depth:=2)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem allAt8 : block orForest 8 0 1 = true := by
  apply wideBlock (depth:=0)
  simp only [treeCheck2303]
  repeat' apply And.intro
  all_goals decide +kernel

theorem orTables : checkedTables orForest 14 := by
  intro k hk
  interval_cases k
  · exact (rfl : block orForest 0 0 0 = true)
  · exact (rfl : block orForest 1 0 0 = true)
  · exact (rfl : block orForest 2 0 0 = true)
  · exact (rfl : block orForest 3 0 0 = true)
  · exact (rfl : block orForest 4 0 0 = true)
  · exact (rfl : block orForest 5 0 0 = true)
  · exact (rfl : block orForest 6 0 0 = true)
  · exact (rfl : block orForest 7 0 0 = true)
  · exact allAt8
  · exact allAt9
  · exact allAt10
  · exact allAt11
  · exact allAt12
  · exact allAt13
  · exact allAt14

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withoutPositive : Impossible (graphGoal 511) 14 (minusZero 511).toFinset := by
  exact root_index (g:=orForest) (before_sound _ sound2551) orGeometry orTables
    (k:=14) (by decide) (i:=0) (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem withPositive : Impossible (graphGoal 511) 14 (vars 2559).toFinset := by
  exact root_index (g:=orForest) (before_sound _ sound2551) orGeometry orTables
    (k:=14) (by decide) (i:=1) (by decide +kernel)

end PEqualNP.Outside.L_meta_5006.Signed511
namespace PEqualNP.Outside.L_meta_5006
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem signedBound511 : Lower (vars 2559) (graphGoal 2559) 15 :=
  signedInduced (m:=511) (k:=14) (hints:=13438558465) ordinaryFull
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) Signed511.withoutPositive Signed511.withPositive
open PEqualNP.CircuitLowerBounds

theorem signedPetersen (C : Circuit) (fan : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0]) = edge x) : 15 ≤ C.size := by
  apply signedCircuitSize C fan computes
  have raw : vars 2559 = inputs++[complement] := by decide +kernel
  have goal : graphGoal 2559 = graph := by decide +kernel
  simpa only [raw,goal] using signedBound511

end PEqualNP.Outside.L_meta_5006

namespace PEqualNP.Outside.L_meta_5006
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Prepending OR(x_0, x_j) as gate zero keeps every later index and the output.
theorem offeredOr (j : Fin 9) (hj : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 6) (C : Circuit)
    (fan : FanInTwo C) (small : C.size ≤ 13)
    (computes : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0, x 0 || x j]) = edge x) :
    False := by
  let gate : Gate := ⟨.or, [0, j.val]⟩
  let joined : Circuit := ⟨gate :: C.gates, C.output⟩
  have legal : FanInTwo joined := by
    intro g hg
    rcases List.mem_cons.mp hg with rfl | h
    · exact ⟨by simp [gate], by simp [gate]⟩
    · exact fan g h
  have pin : ∀ x : Fin 9 → Bool,
      GateOp.or.eval ([0, j.val].map fun i => (List.ofFn x ++ [!x 0]).getD i false) =
        (x 0 || x j) := by
    intro x
    rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      simp [GateOp.eval, List.ofFn_succ]
  have same : ∀ x : Fin 9 → Bool,
      joined.eval (List.ofFn x ++ [!x 0]) = C.eval (List.ofFn x ++ [!x 0, x 0 || x j]) := by
    intro x
    unfold Circuit.eval Circuit.wires
    simp only [joined, List.foldl_cons]
    rw [show gate.op.eval (gate.inputs.map fun i => (List.ofFn x ++ [!x 0]).getD i false) =
      (x 0 || x j) from pin x]
    simp
  have bound := signedPetersen joined legal (fun x => (same x).trans (computes x))
  change 15 ≤ C.gates.length + 1 at bound
  change C.gates.length ≤ 13 at small
  omega

end PEqualNP.Outside.L_meta_5006

theorem PEqualNP.Outside.L_meta_5006 : ∀ (x1 : Fin (9 : ℕ)), x1 = (1 : Fin (9 : ℕ)) ∨ x1 = (2 : Fin (9 : ℕ)) ∨ x1 = (3 : Fin (9 : ℕ)) ∨ x1 = (4 : Fin (9 : ℕ)) ∨ x1 = (6 : Fin (9 : ℕ)) → ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (13 : ℕ) → ∃ (x6 : Fin (9 : ℕ) → Bool), x3.eval (List.ofFn x6 ++ [!x6 (0 : Fin (9 : ℕ)), x6 (0 : Fin (9 : ℕ)) || x6 x1]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro j hj C fan small
  by_contra! computes
  exact PEqualNP.Outside.L_meta_5006.offeredOr j hj C fan small computes
