import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_3366
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Bool) (a b : Sig) : Sig := if d then a ||| b else a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
private theorem bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]

def Live (target : Sig) : Nat → Nat → Finset Sig → Prop := fun k t S =>
  ∀ (M : (Nat → Nat → Finset Sig → Prop)), (proper target → M 0 0 {target}) →
  (∀ {k t : Nat} {U : Finset Sig} {a : Sig}, proper a → neg a ∉ insert a U → M k t (insert (neg a) U) → M (k+1) (t+1) (insert a U)) →
  (∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}, proper a → proper b → a ≠ b → bin d a b ∉ insert a (insert b U) → M k t (insert (bin d a b) U) → M (k+1) t (insert a (insert b U))) →
  M k t S
theorem Live.stop {target : Sig}  (h0 : proper target) : Live target 0 0 {target} := fun M stop unary binary => @stop  h0
theorem Live.unary {target : Sig} {k t : Nat} {U : Finset Sig} {a : Sig} (h0 : proper a) (h1 : neg a ∉ insert a U) (h2 : Live target k t (insert (neg a) U)) : Live target (k+1) (t+1) (insert a U) := fun M stop unary binary => @unary k t U a h0 h1 (h2 M stop unary binary)
theorem Live.binary {target : Sig} {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool} (h0 : proper a) (h1 : proper b) (h2 : a ≠ b) (h3 : bin d a b ∉ insert a (insert b U)) (h4 : Live target k t (insert (bin d a b) U)) : Live target (k+1) t (insert a (insert b U)) := fun M stop unary binary => @binary k t U a b d h0 h1 h2 h3 (h4 M stop unary binary)
theorem Live.induct {target : Sig} {M : (Nat → Nat → Finset Sig → Prop)} {k t S} (h : Live target k t S)
  (stop : proper target → M 0 0 {target})
  (unary : ∀ {k t : Nat} {U : Finset Sig} {a : Sig}, proper a → neg a ∉ insert a U → Live target k t (insert (neg a) U) → M k t (insert (neg a) U) → M (k+1) (t+1) (insert a U))
  (binary : ∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}, proper a → proper b → a ≠ b → bin d a b ∉ insert a (insert b U) → Live target k t (insert (bin d a b) U) → M k t (insert (bin d a b) U) → M (k+1) t (insert a (insert b U))) : M k t S :=
  (h (fun k t S => Live target k t S ∧ M k t S)
  (fun h0 => ⟨@Live.stop target  h0,@stop  h0⟩)
  (@fun k t U a h0 h1 h2 => ⟨@Live.unary target k t U a h0 h1 h2.1,@unary k t U a h0 h1 h2.1 h2.2⟩)
  (@fun k t U a b d h0 h1 h2 h3 h4 => ⟨@Live.binary target k t U a b d h0 h1 h2 h3 h4.1,@binary k t U a b d h0 h1 h2 h3 h4.1 h4.2⟩)).2
theorem Live.recurse {target : Sig} {M : ∀ (k t : Nat) (S : Finset Sig) (proof : Live target k t S), Prop}
  (stop : ∀ (h0 : proper target), M 0 0 {target} (@Live.stop target  h0))
  (unary : ∀ {k t : Nat} {U : Finset Sig} {a : Sig} (h0 : proper a) (h1 : neg a ∉ insert a U) (h2 : Live target k t (insert (neg a) U)) (ih : M k t (insert (neg a) U) h2), M (k+1) (t+1) (insert a U) (@Live.unary target k t U a h0 h1 h2))
  (binary : ∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool} (h0 : proper a) (h1 : proper b) (h2 : a ≠ b) (h3 : bin d a b ∉ insert a (insert b U)) (h4 : Live target k t (insert (bin d a b) U)) (ih : M k t (insert (bin d a b) U) h4), M (k+1) t (insert a (insert b U)) (@Live.binary target k t U a b d h0 h1 h2 h3 h4))
  {k t S} (h : Live target k t S) : M k t S h := by
  have r := Live.induct (M := fun k t S => ∀ hh : Live target k t S, M k t S hh) h
    (fun h0 _ => @stop  h0)
    (@fun k t U a h0 h1 h2 h3 _ => @unary k t U a h0 h1 h2 (h3 h2))
    (@fun k t U a b d h0 h1 h2 h3 h4 h5 _ => @binary k t U a b d h0 h1 h2 h3 h4 (h5 h4))
  exact r h



theorem Live.zeroSet {T t S} (h : Live T 0 t S) : S = {T} := by
  have hh := h (fun k _ W => k = 0 → W = {T}) (fun _ _ => rfl)
    (@fun _ _ _ _ _ _ _ e => by omega)
    (@fun _ _ _ _ _ _ _ _ _ _ _ e => by omega)
  exact hh rfl

private lemma live_proper {k t S} (h : Live target k t S) : ∀ a ∈ S, proper a := by
  induction h using Live.recurse with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {k t S} (h : Live target k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h using Live.recurse with
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

def Reach {R} (roots : List (Wire R)) : Nat → List (Wire R) → Prop := fun p bank =>
  ∀ (M : (Nat → List (Wire R) → Prop)), (M 0 roots) →
  (∀ {p : Nat} {bank : List (Wire R)} {a : Wire R}, M p bank → Available bank a → M (p+1) (inv a :: bank)) →
  (∀ {p : Nat} {bank : List (Wire R)} {a b : Wire R} (op : Bool), M p bank → Available bank a → Available bank b → M (p+1) (combine op a b :: bank)) →
  M p bank
theorem Reach.start {R} {roots : List (Wire R)}   : Reach roots 0 roots := fun M start one two => @start 
theorem Reach.one {R} {roots : List (Wire R)} {p : Nat} {bank : List (Wire R)} {a : Wire R} (h0 : Reach roots p bank) (h1 : Available bank a) : Reach roots (p+1) (inv a :: bank) := fun M start one two => @one p bank a (h0 M start one two) h1
theorem Reach.two {R} {roots : List (Wire R)} {p : Nat} {bank : List (Wire R)} {a b : Wire R} (op : Bool) (h0 : Reach roots p bank) (h1 : Available bank a) (h2 : Available bank b) : Reach roots (p+1) (combine op a b :: bank) := fun M start one two => @two p bank a b op (h0 M start one two) h1 h2
theorem Reach.induct {R} {roots : List (Wire R)} {M : (Nat → List (Wire R) → Prop)} {p bank} (h : Reach roots p bank)
  (start : M 0 roots)
  (one : ∀ {p : Nat} {bank : List (Wire R)} {a : Wire R}, Reach roots p bank → M p bank → Available bank a → M (p+1) (inv a :: bank))
  (two : ∀ {p : Nat} {bank : List (Wire R)} {a b : Wire R} (op : Bool), Reach roots p bank → M p bank → Available bank a → Available bank b → M (p+1) (combine op a b :: bank)) : M p bank :=
  (h (fun p bank => Reach roots p bank ∧ M p bank)
  (⟨@Reach.start R roots  ,@start  ⟩)
  (@fun p bank a h0 h1 => ⟨@Reach.one R roots p bank a h0.1 h1,@one p bank a h0.1 h0.2 h1⟩)
  (@fun p bank a b op h0 h1 h2 => ⟨@Reach.two R roots p bank a b op h0.1 h1 h2,@two p bank a b op h0.1 h0.2 h1 h2⟩)).2
theorem Reach.recurse {R} {roots : List (Wire R)} {M : ∀ (p : Nat) (bank : List (Wire R)) (proof : Reach roots p bank), Prop}
  (start : M 0 roots (@Reach.start R roots  ))
  (one : ∀ {p : Nat} {bank : List (Wire R)} {a : Wire R} (h0 : Reach roots p bank) (ih : M p bank h0) (h2 : Available bank a), M (p+1) (inv a :: bank) (@Reach.one R roots p bank a h0 h2))
  (two : ∀ {p : Nat} {bank : List (Wire R)} {a b : Wire R} (op : Bool) (h0 : Reach roots p bank) (ih : M p bank h0) (h2 : Available bank a) (h3 : Available bank b), M (p+1) (combine op a b :: bank) (@Reach.two R roots p bank a b op h0 h2 h3))
  {p bank} (h : Reach roots p bank) : M p bank h := by
  have r := Reach.induct (M := fun p bank => ∀ hh : Reach roots p bank, M p bank hh) h
    (fun  _ => @start  )
    (@fun p bank a h0 h1 h2 _ => @one p bank a h0 (h1 h0) h2)
    (@fun p bank a b op h0 h1 h2 h3 _ => @two p bank a b op h0 (h1 h0) h2 h3)
  exact r h



def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

def Run {R} (goal : Wire R) : Nat → List (Wire R) → Prop := fun s ws =>
  ∀ (M : (Nat → List (Wire R) → Prop)), (M 0 [goal]) →
  (∀ {s : Nat} {xs zs : List (Wire R)}, xs.Perm zs → M s xs → M s zs) →
  (∀ {s : Nat} {a : Wire R} {rest : List (Wire R)} (save : Bool), M s (inv a :: kept save a rest) → M (s+1) (a::rest)) →
  (∀ {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op ka kb : Bool), M s (combine op a b :: kept ka a (kept kb b rest)) → M (s+1) (a::b::rest)) →
  M s ws
theorem Run.stop {R} {goal : Wire R}   : Run goal 0 [goal] := fun M stop perm one two => @stop 
theorem Run.perm {R} {goal : Wire R} {s : Nat} {xs zs : List (Wire R)} (h0 : xs.Perm zs) (h1 : Run goal s xs) : Run goal s zs := fun M stop perm one two => @perm s xs zs h0 (h1 M stop perm one two)
theorem Run.one {R} {goal : Wire R} {s : Nat} {a : Wire R} {rest : List (Wire R)} (save : Bool) (h0 : Run goal s (inv a :: kept save a rest)) : Run goal (s+1) (a::rest) := fun M stop perm one two => @one s a rest save (h0 M stop perm one two)
theorem Run.two {R} {goal : Wire R} {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op ka kb : Bool) (h0 : Run goal s (combine op a b :: kept ka a (kept kb b rest))) : Run goal (s+1) (a::b::rest) := fun M stop perm one two => @two s a b rest op ka kb (h0 M stop perm one two)
theorem Run.induct {R} {goal : Wire R} {M : (Nat → List (Wire R) → Prop)} {s ws} (h : Run goal s ws)
  (stop : M 0 [goal])
  (perm : ∀ {s : Nat} {xs zs : List (Wire R)}, xs.Perm zs → Run goal s xs → M s xs → M s zs)
  (one : ∀ {s : Nat} {a : Wire R} {rest : List (Wire R)} (save : Bool), Run goal s (inv a :: kept save a rest) → M s (inv a :: kept save a rest) → M (s+1) (a::rest))
  (two : ∀ {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op ka kb : Bool), Run goal s (combine op a b :: kept ka a (kept kb b rest)) → M s (combine op a b :: kept ka a (kept kb b rest)) → M (s+1) (a::b::rest)) : M s ws :=
  (h (fun s ws => Run goal s ws ∧ M s ws)
  (⟨@Run.stop R goal  ,@stop  ⟩)
  (@fun s xs zs h0 h1 => ⟨@Run.perm R goal s xs zs h0 h1.1,@perm s xs zs h0 h1.1 h1.2⟩)
  (@fun s a rest save h0 => ⟨@Run.one R goal s a rest save h0.1,@one s a rest save h0.1 h0.2⟩)
  (@fun s a b rest op ka kb h0 => ⟨@Run.two R goal s a b rest op ka kb h0.1,@two s a b rest op ka kb h0.1 h0.2⟩)).2
theorem Run.recurse {R} {goal : Wire R} {M : ∀ (s : Nat) (ws : List (Wire R)) (proof : Run goal s ws), Prop}
  (stop : M 0 [goal] (@Run.stop R goal  ))
  (perm : ∀ {s : Nat} {xs zs : List (Wire R)} (h0 : xs.Perm zs) (h1 : Run goal s xs) (ih : M s xs h1), M s zs (@Run.perm R goal s xs zs h0 h1))
  (one : ∀ {s : Nat} {a : Wire R} {rest : List (Wire R)} (save : Bool) (h0 : Run goal s (inv a :: kept save a rest)) (ih : M s (inv a :: kept save a rest) h0), M (s+1) (a::rest) (@Run.one R goal s a rest save h0))
  (two : ∀ {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op ka kb : Bool) (h0 : Run goal s (combine op a b :: kept ka a (kept kb b rest))) (ih : M s (combine op a b :: kept ka a (kept kb b rest)) h0), M (s+1) (a::b::rest) (@Run.two R goal s a b rest op ka kb h0))
  {s ws} (h : Run goal s ws) : M s ws h := by
  have r := Run.induct (M := fun s ws => ∀ hh : Run goal s ws, M s ws hh) h
    (fun  _ => @stop  )
    (@fun s xs zs h0 h1 h2 _ => @perm s xs zs h0 h1 (h2 h1))
    (@fun s a rest save h0 h1 _ => @one s a rest save h0 (h1 h0))
    (@fun s a b rest op ka kb h0 h1 _ => @two s a b rest op ka kb h0 (h1 h0))
  exact r h



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
  induction h using Run.recurse generalizing p bank with
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
  induction h using Run.recurse with
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
  induction h using Live.recurse generalizing v with
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
  induction h using Reach.recurse generalizing k t S with
  | start => exact ⟨k,t,S,by omega,run,sub⟩
  | @one p bank a h ih ha =>
    rw [List.map_cons,table_inv] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩ := pull_cons run (inv_rep (available_rep ha)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩
  | @two p bank a b d h ih ha hb =>
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
  induction h using Live.recurse with
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
def oldSeed : Sig := 0x88888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888

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

def neighbor (i : Fin 9) : Nat := [4,2,1,2,0,0,1,2,3].getD i.val 0
def absentRow (i : Fin 9) : Row := Fin.ofNat 512 (1 <<< neighbor i)
def presentRow (i : Fin 9) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< neighbor i))

theorem seed_witness : ∀ i : Fin 9,
    (bit (absentRow i) graph != bit (presentRow i) graph) &&
    ((inputs++[seed]).all fun w => w == inputs.getD i.val zero ||
      bit (absentRow i) w == bit (presentRow i) w) = true := by decide +kernel

theorem all_roots {k t S} (h : Live graph k t S) (sub : ∀ v ∈ S, v ∈ inputs++[seed]) :
    S=inputs.toFinset ∨ S=(inputs++[seed]).toFinset := by
  have all (i : Fin 9) : inputs.getD i.val zero ∈ S := by
    have cut := seed_witness i
    simp only [Bool.and_eq_true,Bool.not_eq_true',bne_iff_ne,List.all_eq_true,
      Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq] at cut
    apply raw_required h _ _ sub (absentRow i) (presentRow i) cut.1
    exact fun v hv hne => (cut.2 v hv).resolve_left hne
  have needed : inputs.toFinset ⊆ S := by
    intro v hv
    have hm := List.mem_toFinset.mp hv
    rw [←input_list,List.mem_ofFn] at hm
    obtain ⟨i,rfl⟩ := hm
    exact all i
  by_cases hseed : seed ∈ S
  · right
    ext w
    constructor
    · exact fun hw => List.mem_toFinset.mpr (sub w hw)
    · intro hw
      have hx := List.mem_toFinset.mp hw
      simp only [List.mem_append,List.mem_singleton] at hx
      exact hx.elim (fun h => needed (List.mem_toFinset.mpr h)) (fun e => e ▸ hseed)
  · left
    exact Finset.Subset.antisymm (fun w hw => by
      have hx := sub w hw
      simp only [List.mem_append,List.mem_singleton] at hx
      rcases hx with hin | rfl
      · exact List.mem_toFinset.mpr hin
      · exact False.elim (hseed hw)) needed

theorem initial_live (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (first : ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 4))
    (computes : PEqualNP.MetaComplexity.circuitFun 9 C = edge) (small : C.size ≤ 15) :
    ∃ k t, k ≤ 14 ∧ (Live graph k t inputs.toFinset ∨ Live graph k t (inputs++[seed]).toFinset) := by
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
    refine ⟨k,t,by omega,?_⟩
    rcases all_roots run hs with h | h
    · exact Or.inl (h ▸ run)
    · exact Or.inr (h ▸ run)


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
  induction h using Live.recurse with
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
  induction h using Live.recurse with
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
  induction h using Live.recurse with
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
def chartGoal (m : Nat) : Sig :=
  if m=1023 then graphGoal m &&& ~~~oldSeed else graphGoal m
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


abbrev BoundPool := (Sig) × (Nat) × (Nat) × (List Sig)
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
  | none => simp [he, Option.map] at h
  | some pool =>
    rw [he] at h
    change some _ = some c at h
    injection h with h
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
    rw [h.zeroSet] at he
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


def IndexTree (α : Type) := List α
def IndexTree.leaf {α} (xs : List α) : IndexTree α := xs
def IndexTree.fork {α} (_ : Nat) (a b : IndexTree α) : IndexTree α := List.append a b
def IndexTree.read {α} (tree : IndexTree α) (i : Nat) := (show List α from tree)[i]?
def IndexTree.values {α} (tree : IndexTree α) : List α := tree
theorem IndexTree.read_mem {α} (tree : IndexTree α) {i x} (e : tree.read i=some x) :
    x ∈ tree.values := List.mem_of_getElem? e

def Forest := (Nat) × (Nat) × (Nat → Bits × Bits) × (IndexTree ColumnInfo) × (Array (List Nat)) × (Nat → Packing) × (Nat → Nat → Option (Nat × Nat))
def Forest.mask (c : Forest) : Nat := c.1
def Forest.cap (c : Forest) : Nat := c.2.1
def Forest.samples (c : Forest) : Nat → Bits × Bits := c.2.2.1
def Forest.cols (c : Forest) : IndexTree ColumnInfo := c.2.2.2.1
def Forest.autos (c : Forest) : Array (List Nat) := c.2.2.2.2.1
def Forest.levels (c : Forest) : Nat → Packing := c.2.2.2.2.2.1
def Forest.index (c : Forest) : Nat → Nat → Option (Nat × Nat) := c.2.2.2.2.2.2


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
    have seedEq : oldSeed = inputs.getD 0 zero &&& inputs.getD 1 zero := by decide +kernel
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
    materialize (vars g.mask) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2

theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols.values, Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : buildRule g ops depth bank i paid = some c) :
    ValidPool (vars g.mask) (targetOf g) c := by
  unfold buildRule at h
  cases e : g.cols.read i with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    apply materialize_sound _ h
    exact cols ci (g.cols.read_mem e)

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
    (cols : ∀ ci ∈ g.cols.values, Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
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
    rw [h.zeroSet] at he
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
  g.cols.values.all (fun c => colCheck g.mask c prior) &&
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
def g15samples : Array (Bits × Bits) := Array.mk [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbaf3ea78de4d799d,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff450cc90c3c245919),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdf7ff8fe9f9b7ed5,0x20812421801324c4),(0xefbdbf97f9f6bf6a,0x102a401415600a0a),(0xf3a9d7437375f5ba,0xfc028ab620235b0),(0,0),(0,0),(0,0),(0,0),(0,0)]
def g15columns : IndexTree ColumnInfo := (.leaf [])
def g15autos : Array (List Nat) := Array.mk [[],[33,48]]
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
def g31samples : Array (Bits × Bits) := Array.mk [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdafffab2d55fb9f999d9ceeefacb357b78f9ce2bb554a3bac97b2a9d65,0x250142092220460600407048c382809c2160e048740030a88143281c44),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffef5dfed46f26fea572a7ba9effd7341aff97ad1ab5bd2d547d6793334b,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff90aa211010d10141c4300836206168204010183680184d04682483210b),(0x73ef3f3c8ff8df3fe567b556c9567ffcd665219778a6bd6e36bfd946ac,0xc10d0c3000214920a0d648109801012344d60802686b04210115006a4),(0x7c7fd57b7ffa3476e74d6f3fc4bddbd44dc213c5eb8bdea95bf6ee7492,0x38022048645c06490200044a25241818912934541000824c322ae5002),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8fe76ff6451fda6ff84b6daf38f5bb6f6a5ee88a4d6be3f71c64aa3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8076989008882001270e063010011622500c04308a174300141c40a239),(0,0),(0,0),(0,0),(0,0)]
def g31columns : IndexTree ColumnInfo := (.fork 2 (.leaf [(1,0,30,0,4),(2,0,29,0,4)]) (.leaf [(4,0,27,0,4),(8,0,23,0,4),(16,0,15,0,4)]))
def g31autos : Array (List Nat) := Array.mk [[],[50,65],[66,16],[67,50,33,16],[67,32],[67,66,49,32],[33,48],[67,50,65,48],[67,66,65,64],[49,64]]
def g31levels : Nat → Packing
  | 5 => g31l5
  | 6 => g31l6
  | _ => emptyPacking
def g31index : Nat → Nat → Option (Nat × Nat)
  | 5 => fun _ => none
  | 6 => lookupWord 5 25 2 10 2 4 (key31l6)
  | _ => fun _ => none
def g31 : Forest := ⟨31,6,fun j => g31samples[j]?.getD (0,0),g31columns,g31autos,g31levels,g31index⟩
def g47samples : Array (Bits × Bits) := Array.mk [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffddffff5cfaafae7dd35b9ce7bbffd6b6b7b7cfbb8d3b7ad85ddf257b56b575,0x2200a042011011800c00803812181c2009c1061c0107200c09440143143444),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeebefed537937fcb8ab173daa7df7f7691aff9776b2b7dcb92a3f3678b2b59,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9149112428688034a38448020d64a21d120601022ea84882b022a624830919),(0x77db9fef67fc77f3ffe6e3dd55f86b6fffcab66472f7c57fb768dabfad4eae,0x820641080010508440806b120004c020121a4ec1002247c020840112806a4),(0x78ebe4ae9ffd0d576de696b3cff805db7d426c00d8ded437ed436ff6f66c92,0x71419416322f057a950700411b6b328381c4110e8d4580325370f22d66812),(0,0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0bf9ebdb2287acd4afec26dbb6d98eabb3768bb508ca4b7f1fdd1c709a3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80f74f1424444852a26637058ca3a012d22680c12e48c8e17411561c608a3b),(0,0),(0,0),(0,0)]
def g47columns : IndexTree ColumnInfo := (.leaf [(8,0,39,0,4)])
def g47autos : Array (List Nat) := Array.mk [[],[83,32]]
def g47levels : Nat → Packing
  | _ => emptyPacking
def g47index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g47 : Forest := ⟨47,4,fun j => g47samples[j]?.getD (0,0),g47columns,g47autos,g47levels,g47index⟩
def g55samples : Array (Bits × Bits) := Array.mk [(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbfffffdf7defdfafbfd3fcebcfdeffcebffefe76de77fed7f1773f95eb2ebeb,0x400028000010005000000400701010180030103060043200102204010904888),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdb7fbfbb9ad3afd94caf0b9db5bbdf7f7d39bfcdadcf77ec9eccd2fb9cf16b5,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2484444214284026a4e002420468a8a43140a00408d944460a4082569431231),(0xeda5e7e7b2fc29de4ffc371dba2bf0775ff12db9b18bb528fedad96afcd3c5e,0x12589919410293410206d0396285445a082c5d2bf0022b20f0895d2048c2c4e),(0,0),(0xf1cd79264efe956afa7a64bb677ab40beba463600362eda36f3357b7d763926,0xe3a8651b1a36a0acc57538a080f6ea703078a0c13c28dc34c91f3868663126),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe05fe74eda341d5872cbf684d5e2ed19e7e3bba5e964550dd792aec724f479,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01fb53db1204342a549861b60b6727a22d48ac0b14da4445855161ae724b471),(0,0),(0,0),(0,0)]
def g55columns : IndexTree ColumnInfo := (.leaf [(16,0,39,0,4)])
def g55autos : Array (List Nat) := Array.mk [[],[84]]
def g55levels : Nat → Packing
  | _ => emptyPacking
def g55index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g55 : Forest := ⟨55,4,fun j => g55samples[j]?.getD (0,0),g55columns,g55autos,g55levels,g55index⟩
def g63samples : Array (Bits × Bits) := Array.mk [(0xdabffdfdbdf61bfbfc7dcbe34f7f1b17917df75df7edd9eff77b6dbd3dcebed3cfbfaddba50fcabded46bc9b579eb7bd3d92776566ad4ad3debe36d74deb7f9faf189ad76da7dc1a6b4eaf21eb254de4ae1f7451bb34d9456fd18e934db17349,0x4400202400040800310000100084000ac0000102800a1100490002240004b2800a001b4000190000008108000574009200040400000594000190004218c0010840002890800550053044a00410008802d0060013000c004400188120c206208),(0xb6678efeffcbf5a9cad5bfd527a7a5bd74d1314b7915f5b2ffdec2fc5d978f8ab3b44b2b5add5b771711b15ce99bf2b3f5bce975ef94cd59a34e76ab937848a94ef6be6c9579db5905539ea703c87a7d4ae11fe2ae423fade4a3c3299b0724e7,0x499461811a200a55004cf88854029340027a680613c002ec00233c1096d01045025d0203d400243150030b7e4900b00499e023395882049d0206ec00041398010bbb1000b7310ad00cc0858112c8207810e917400e423d0034024309910504e5),(0xbfdd27bedf8fade4776ebf9d185bc5bd76aeffb29711f77d628e86e5fffdff6d1a52bff6da987348e3e147dcecdbcc68d1accc4e7d7d77b9734cfbbcefbc022d72eff5a31a72e32584dd5a72accb1256ede309af577ea6b3ab2be572a2769632,0x20983204990108b1910222a2810c12a8041040402e00006394000908008912a582448429aad10a21a0240190b504314209040621245140c82010e8812042049440841100c0c52080310832a5111106e902488a012c82618908a42202729212),(0x77ddb87389d95f9f7bbe7e8eb89e6e76fbf75ca7fd5bb3758b555b578affe964ae7e7fa493e06d03bebc4fb5cff51e46b2dd5bdbb1eab66f60f7d916b9c6944fd85b6f0fc30a2ae7d2afc9dc369ef80bb1b0b2dd52e9331e786f7a5d38e8c8b4,0x1482478012444200420888514440810c402202189081ecc814422aa4c048408050190921c0450c000a080254044021081134422900082c11250884167012813a48094aca870a3283708e41084282480000c012150640581c30655a55288040a4),(0xdca768aafb78ce8d2db2ec3fbdddfa4ec963339dbac7a8e05eccbf0bb99ddf5febcef6dc7762a4a79d9ad8f70324ba6e724754bded1eed86f695f276b70acbd73dc66e39a88d0cfed920a0ee10b5a4dd5893bba709bff6dc1ece388c561e1ed5,0x210938550593284a984457082a220ca002159526023c0223a02100100d271046aa46f2022bb0201ea5730921b3008e848a002106a7520082d20653c8040064810364a00030c5086c0c2084761035a077101508a009ba22e00b822088521e1c51),(0x77dad76bd4ced656e7ec247a694c9eb5b66dc4de71aac18acebb177a9bac7a62d6f3e3996dd9d62d6ecf7b18557229a30b5ebb1ef46b568a8f3400a7c2d3365caade63d0f2234a24623735bcfaee29c0664eddfc63b2a86915f817ca03dc41fa,0x88252894b2b3256598a758928465236453b27d28c68c4c28a24dcc0d24d500d4a845700845b04bd175706d345a20a0a24d641d897dd822a1d52444cad2629c8e732b305273362844202335b73c8d8150424e93e44a78286995ec17c803dc01f2),(0,0),(0,0),(0,0)]
def g63columns : IndexTree ColumnInfo := (.leaf [(32,0,31,0,7)])
def g63autos : Array (List Nat) := Array.mk [[],[50,65]]
def g63levels : Nat → Packing
  | _ => emptyPacking
def g63index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g63 : Forest := ⟨63,7,fun j => g63samples[j]?.getD (0,0),g63columns,g63autos,g63levels,g63index⟩
def g111d6 (i : Nat) : Nat := 0x120ff
def g111l6 : Packing := (1,0,2,0,1,0,0,g111d6)
def g111samples : Array (Bits × Bits) := Array.mk [(0xeafcc7b96fc59ffd26c5e2bb3d7bd378fb35ff5dcb26f92afa5f57eff59a73b7aaa379b2fc8d7a99e2ef9efcf4defd4efabc9c89733cebade5579ad5abbcd64d8557ad3d63bd1c6a75510ce3b9bf05e462ee0edf6dfb2914efc74c7d31727465,0x4d00310a2003881269402d0c00406ccc142a8012908082d00025ac006a88036948003229000032d4001bf20024ec2018680000aaf2500325400423a6f02003840040a8016ea8106822700071012c01d500600ad401ea0010f407087831504444),(0xf771ad34ff2bcf4fbd7f5f5de52efaeb7ebbabfffefbf2eab7c7cf56f8ecea565ddfabcf87cb61db9d6ef4aecff7cebd76fe679cfb9935e6adabc77cdcdb677ed3da5e4f56b4cbe39cfd7aed1f519a6b999796b48a51f4f7b8ad91a66cc6d9cb,0x1204940050200482000010001c10308054448009004424020800871400ac0690000402004e0508404004081210450414000904018220d090010808000a44280600460810104d92040818880c1010088d8400200a10a1400808810604821909),(0xf5be76df5e79b8b5d13f5f6e3ecd176fbeee538a7cfb9f7f6b7fad9b13bb7fed97560ecd71f29f3f1e3ef959a338e3a9e32bd5e7cfc7b51df73d7e9e165479b3baa9a0d59e62e11eead3ad5c624777de8699f96d3766d64d1f3fa2ca8f3d2e52,0x8e4d19200884440101e4a802e100a0c04000830eb000289800c49240c1c411082c325a6812b0485430294040c52402008322a4b0e00c0021216842103a050a9080848145264020288841a770220547500211500d95204c05521120880b352452),(0xde2ebbc73c1cf83c4cedbed77297d7f5b666582db23d5c5d7bf4a54b37a75f4992f88d683d388ea5bafb57791a5deb9b257390777cf70e9d329773c24416edd93fe3d2909bc3b81d7e62dd94d70a759eb42b6b51587d63da2e7eea6ce78912bc,0x10b22099c5638280b403142808691e02bd9d04d1097a9640ce2041351e20e64283892100494815238b12089820999d9858901b4e1903515e001721098578a5416f515492d981d895722018845902b08a5c4a2a2248dd03d08c66ca64e48812ac),(0,0),(0x4a99db5e74fdf3bbfb83b4b12e735e58f515867b75942dba656f9eeac55739b971685432ece5b39368c30fbbb9f895ca9efa5eceda2fea7be4766f052ba5def635ccf928215f7640050f6846acafb2ca6efbba0bffbfdb9043d87d111c3c3ebd,0x12d68401de50564414b80023f49c0203c0413d800068400bbb08034f0177ac0427f40400f6de0023bcc009fc1201950403ff4900082ea08a2fc908010c8a4053de0011e801464d050407f806ac13f8026d9b800bfa055d40038875010c2c3ab9),(0x107b7e8791b6519a9ebd6f37d374faa298392ebad8b5e4afe6bd267679568b3365bebaabdf6ef4e9035a918e8ca50ef74769b2b74aea726a09a6c5e9463715fb76745a9b1b6212a1b9add6dec52a9ba55b57e399ab660ca6d0f217384af881fe,0xadc48a6a24248ac9294916cc74a18dce4988890976a839d0a90054480a8f001149b409fd5690d8d50882129489ae3083c83b5253565cd02541ca4550f495b985581508b28aaa022919a1e755a00eaaa54243a315f06a0c87d4f216384a7880f6),(0,0),(0,0)]
def g111columns : IndexTree ColumnInfo := (.leaf [(4,8,99,0,4),(1,32,78,0,4),(64,0,47,0,5)])
def g111autos : Array (List Nat) := Array.mk [[],[83,32]]
def g111levels : Nat → Packing
  | 6 => g111l6
  | _ => emptyPacking
def g111index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | _ => fun _ => none
def g111 : Forest := ⟨111,6,fun j => g111samples[j]?.getD (0,0),g111columns,g111autos,g111levels,g111index⟩
def g119samples : Array (Bits × Bits) := Array.mk [(0xfab75f3dfbfa3756f92d9ff7baf5ff7dbfebb9b33bef7dcdf77fbffe7bbbf75546cedccfd6f7eb762bef3ffdd2ede7abbef7e4e4b775eb9be6ab6f4d5fde77f2b955ece57b3feb97c6d99b5cdd2fdd2ea315de5f3efbf8d44ddcaa7566eda9cd,0x20100000802449000a820000c1900042800052080010000098c000620802429000050a2000012e00000be20013404000082000047420011240000c8b8000110080002480036500158018000c4009400c9000c0062803a0400e00885042a10888),(0xaf7efcd6de9febfb57d6f5ddedde36f3db7fffeed79fdbfafcf255738c743cbbbff3e3b86b8f9fb9f5bdf54fbff79bd74f5afb3f7fba34f5bf5f9afae879ab5feefe93fa9ee6566f7bbee6bf67d426d75cfb2bace9344fabf72bd58e999b76b3,0x9300010000091004000400382060802420900110020801010208161810541520000000800198110400c004084880812115000049028020c0800220200009220a01801050108206a8408406120184808104430800802442850101410609083421),(0xd3aee9d1a16b8afb579b1b1a2ede96c634714fced4ed35afb8d86696aabedb2eada373270f48f3a9b93de8a90d87d8f6684756adef8eb40bf672fc78b9342c9c7aaa652b2aec9422dd38b32b2a5255bdcc3d35b2da5f372953f3c4ba3a70d996,0x2c07b23e74020fd2aa41748155856818d263d681015680dac92709c7448b08586eaf3a512642c64b613a9091954b38c222671d26711d023332d48951dd0691952839212f8b6888039910b9ac2a42653c283c65315b1b95185ae084b83270c996),(0,0),(0x759a506bc07865de6f37bc2fabe39a5e2705b6a3eec6bd3cca572e3ed72f0325f632aa43d8e0e833eaeab6f86ad5fa72dbaf9c83b9e70faa212acf122e177ae733d8fa39a0b0bb12b7915f7134c3b9a9ed98d75362b1d9c725676c3caf04637c,0x16e5f59c6d01a255c44806523c0cddb5529a2196d082e7c24415d298c0f10d071e6090549dc090f8ed501938009f3fb2169588d90b0b506d102e01343cb84ad135f45369a498be0a36011e712702bb816af81651c4b05c0701a6642cad046374),(0x6339c3e76f77dc41ec6c9766b8b0f93592cd6e58a17db2abb9eea5cd269eeae2dc2c1c9ec755bae6a2821f6b678c3538a75edaf56c57e97ff4e8b90d55c4e75ce36b37ac511be4c610c6f229b9ab77956345b3a117ef6f3608dd37697870ba61,0x84ef690f5888a6bc0049f9381c0ba0115db000874a075d2102333605e754184fe100105f739880fb92c019ec481f2d2102dbf2480954a0ad3f922114724920d57f80032e5018c6a22083e62199863ec06b43378157e41d3d00d937293850b261),(0xd5cc96ab2735f4eedbcfece9fd4d847149d75b8aa71ff3959066dc7566c66ecb75975abde9bb8d684d89311f3151135dd1ce4d97acd9737d0b4d97b62b1596cf57b51ab1b6b408593b67d5bb928b32dabad66fc43367241aeaae177095e247ea,0x481560b0cd924918c5323d4303992d88d1232e6a49f254a2454320824e8122936522ef3572424e688310332525616c12e023da92a435d213539c9243b254cc21b63548a8e4258841b361f1c95a017252ba1c47902bc1245a7a8e167094e243ca),(0,0),(0,0)]
def g119columns : IndexTree ColumnInfo := (.leaf [(4,0,115,0,5)])
def g119autos : Array (List Nat) := Array.mk [[],[84],[98],[84,98],[101,66,16],[101,100,66,16],[101,84,82,16],[100,82,16]]
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
def g189samples : Array (Bits × Bits) := Array.mk [(0x76b7b935ad7f6fd4d735f26d2df10ff4361bcad97bdde979efcd6e58b7554d7ea7eff73e73de92e56562d7533a4ef3de34b1f6acf1d6e216666babd43dbaabce3ad8d545ed4e53771cb4e6d84ab365f9722155b0decf672135d0ab0e8aab3265,0x8404642124899480a2a81184400c4494a40542200633c0114901482008a100b4c40690c02a500485280025a8300be5004d078022244028e4a0122910034dd0088624c002500565400b4701a401901a06a801c60d40e430038408b0c08aa0264),(0,0),(0xb725f7b34edfbeffaf8e64c99fca263eeb8ebd6e6efba6759d07fff35f0d57cf0f1af1c8e8596f2d9f9a363b65aade972ff9af593499366f72b4e55d5e6f961954d5fce693a74e66d370dbbd59357a0ab5d8c2e2b4913d9ddc0ac963246654eb,0x2019084c910042485050a84580141012107000421c10cd02a29a004c0424911090cb1414ac1a4012048a60a1130c00921224ba8854044c203120d1318881010110848d88109408245548f0845c253042044cc0e02091152804424943044214c9),(0x6b3b37beb0d3b3db67cafb77eb9e1dd789aebdb18d1db77732f653e35977f97f4dd313687fb67a399a5d29e7c5c2df2ae361e9d1a8a6a7bdf9b41bf76bf3c59c972736ba642a6ec8e10ddd388a5d8a2fef454b2f6c5cd8cb4dafd1a5458caf32,0x84c42401462a8882042c15880121e0040f09501440a3008044047580824b00c92204cb801220a2e8d004050a8c13a8082552010080e322ce0002224042220e86c96110212062d680201609100358082de8010e0a0c4e080169249024018caa32),(0xeed4ecfef66eeb7efebdd9aee7077cf1671b7b7a97dfdfd372d0ed94ede3ade9c50737565e265d36d07689d4ac4faafe5abbfdc5676e89f79f8f9a623b38502f3db98ff0fa982b81b88d0790fae9d8d74f74351d5187af7a955e769667c1914c,0x112b0124099000041080680538580102a03620812918016ca82b084951200b0011391441e40a1406003a00a460640102802906c05910d52121d05c00b8012058249003c452192901d049060038a0e052051c011422a1a0780618649266411108),(0xd9cafe65094bbf5f7264b7bbce3ffbefdc6762cbb35969c8ac2ddbae62ff5a5f3ee2cea13be5ccd265ed5a725a1921f7f9e712e69e98fb2d45e97fd5f2e0abe4f3f7676b375491bf662220c7ec1235aaa52f7b260bfdf8f023b73c589c1c3f19,0x2215018860a440b0408528403b942810a5b0009c1c080302094a000184016510830b02e2ac10b810014a60046c8c012e120b028809b84c0105208c4e88802201101131880274018a550300819c02301e012cc3000b90a8a80382305084143519),(0,0),(0xe9cbc8feffb7f8e7b8d17ff4f26deb6af5fadcfef4fa8da189aed6c66eadfbba567e7aa58acda76b57bfee9d03799233ac5e277f4fab9af55d736c18d65d30adcab7ab9d1b9dcbcc02d24b67373e9182d29baedd99bcc115aa3d04dc337a48be,0x1420360100482d00252a00a2440945244a022b202187302c44004bb2035a00002400090800450025fa000d1a80010240a950404582409154ca522280124a1c0c672a40054909a2500214036203d800a092812c0514244211e81d048c33284826),(0,0)]
def g189columns : IndexTree ColumnInfo := (.fork 4 (.leaf [(1,0,188,0,5),(12,0,177,0,4),(16,0,173,0,5),(17,0,172,0,4)]) (.leaf [(24,0,165,0,4),(33,0,156,0,4),(132,0,57,0,4),(160,0,29,0,4)]))
def g189autos : Array (List Nat) := Array.mk [[],[84,115],[117,67,32],[116,83,32],[82,48],[84,115,82,48],[117,116,115,114,64],[83,114,64],[116,50,80],[117,84,67,50,80],[84,115,66,112],[66,112]]
def g189levels : Nat → Packing
  | 6 => g189l6
  | 7 => g189l7
  | _ => emptyPacking
def g189index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | 7 => lookupWord 5 18 5 10 2 4 (key189l7)
  | _ => fun _ => none
def g189 : Forest := ⟨189,7,fun j => g189samples[j]?.getD (0,0),g189columns,g189autos,g189levels,g189index⟩
def g127samples : Array (Bits × Bits) := Array.mk [(0x27ec63be833e95d9cd8b1b0f8c7b949b955ab7ff06f2f46fb53d19a8b89e2cf938ea5b637a679113a99b1a558cf5d3757100e2a2d92956b1df648864a3a84cf9f5aafcc4980f547cd2d2abacb351593072ded0ca36876c216b176a15583d3069,0x215000b22a840210400a1040082a19401000220004808d00802008c02014082088420800402688520818425544410445400040805130408104600820a3600c001020e0440008143510802b10a111102142440000168440214816081150281060),(0xd1272c7d4d43f0bd72e56dab39ddfe7c6a407c139e413a8c95b2f6c7134bd9d2e6151acc0f6f6e61aecc859cb80ab9d38d1f9c08bbd08127631b9fb156aefb042a9049abe4f27cdb8815184a3fa2b5dede495570df2830da3c38c46cf1426d13,0x806000d540888802080408280406213088804000000320c048631024209804006241648090164a10080940a08001912a8109004a2408004431a0101080453200880088a80c0004a880100481a02008819080040c10830122428406420422c11),(0x3757a63bdee4ba3fd3e2275cd925bbac4327c3605b6a92ba668b6b375f5956a61c0ee4c8b6382a0c726a8d674c1d24e187c7697b46618e9a3259ec9e635cb1935494676727a9c6a3df6b34450ca72f271676b8367562d5a985429aaa9a64d626,0xe190134200c030558e6885084d0788a40161e860830e0412a109c61098d030850809a9902628890c322a09e446182064058721691005078a1841cc5c6248a09654242521162044855722240404692506023498262462c48981029a8a9a244222),(0x7c12f7ae7cb67a121957d4766ab145360dad0baa714fd5dd4ad95b9245e39e4cff88a61691dd24ee5570ea624367b54a6aea5375c626bc6f4082772e38770d5a1955fa1dcb198b20afa8d659c70c9ab5dbb42b955b55e374e0f839c3068a9694,0x100b203118264280010702e3020864421484020c18c0438c4090018044060d7096401604915660c20151c00201478d0220604290c2020821402022221025140809114a0c4919231288809339110498f1918002911b15216460582041008a9494),(0x5f0ed2cab79191489f9794fa9f865222c0c45f4f23977137ba6ec87e2fb718cbcb3281372d8190b9e5b2713c276012285f3b185c628f375c96ee95cada25845527c7ad5b31bc018c667be7de6cdf9480211b73e5e0fc0e1e03a683a80feb2399,0x4e04900c0410144f3ce0e018c1840020605099a3823d30032c4ce03413c1e08c412481b32c810028f486342022205010179b1c44008d375c030cd5d908008055e282051134c40088667900c444ea04000013f960e0680e1a03a083a80f412309),(0x64ed11ab034e6565aa5f6f0a73fb2abb553e90eaf5f2056f4f2ad1a6a7112f3107edc462d825611a42150349a39be3bcbdfa3bf68749fd950e410251758bd0aaed7e1f93ab81b400f6cd22629068e5bc2da9dbde283bbf115009f3b1a197a662,0x46299909050b25a18c71e62a5095c63ecb8f04a3c26b60b927cda532c109201915ade64b3091412042050108b390e3bab9cb9877060097580a090251508bf2aae7571e1ba185a2088a6c00621068c596ada8d9f5a83bbf101009f3a0a197a602),(0xed72aa63cb994444b8dcf183254b4e7cee24db3ad729ab4a1ba98c700af5e5480459e832e1cc5750368c89edf172492ed4565f186db3259850f427f3943aea1f7b1d745054d56ed5059c9e36e00b68fdae413f628aa9c64ad98b04d0b38dd9ac,0x4400b2628be723745844a119668f0ccc9303b92a933d014173710ec9a0c0658c41596832a4cc13563c0629c5d4a2402c44020f584d31651810e10cda143b2c95631f726414156f15141896b3a1182c75a6e53b222aa1c648d9830490938dd1ac),(0,0),(0,0)]
def g127columns : IndexTree ColumnInfo := (.leaf [(32,0,95,0,8)])
def g127autos : Array (List Nat) := Array.mk [[],[101,66,16]]
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
def g191samples : Array (Bits × Bits) := Array.mk [(0x6acfda3c2cb83a92b793db4cbe83faea9cb2634793e21db352fb83fe8df2bc07a86d83614e9e1d6652f73c866931a299021d0d35cea03b8bca899a3ae9b0852968ae39aed598c502d3cc66c95e3918558ba9636cd1546c95b4522b12e41c6251,0x8027018c1220821109402382a0c04040242201142810004800310a01021028020024504420900008134444101889108100844480011218a0808a088000429588a002494484002118004005c4110108908c2000154441190520210a0142200),(0x7913ceb593e8bd03514889e55f4c93639759259376fb3230720c9a865196f27cc74c193b9b758265cc3f7b6a39d891145642471fe1a3e402ed12036d66f3fc532a7d00122732be1cd6f8a0d631223ddb153772d463789a2c383ce02e7842d163,0x88036081c60419a2c82401d04754b2b302101402821d5c654204040641a4c69d42c491108805a675482c4b1a3210132646402113b58224122512010966d1b044833550122312b410427aa086012a6ec1101538c042289a0c282ca02a5842d161),(0x557693cafd0fd9424efb95e75ddf8ed5bd78c8ecb52fa208a8d45cb3574ccaab77d93b1e650b4399e9518160864e914bee471a4d6078d8cd3710b8c5462d299957d5836e24a95a7b253cdb2e6196070b78eaa32a2b4a267149c447650cd138a6,0x10c082401088400012d0c4008000004018ca8080142020182010002082500860100b028600824082a011044180428040210612040030c884904098c2002801191040822880a108c8040449084010010648220108084220210140474504110882),(0x9c642d62a2f2f7ba22bc048df67d49f5212576be5994f8cdc5e270babb8959b792802cb3e87f90d4054ae918d4ab1ce241d9cf541d5d16b72277276810cef58c9e0f2a3137066d66292bcd81a96583d025d9fd03afbb585aa2b81e898b063d44,0x8024093988519a8e002822a41919198600217873085849c0c483198871885081c08060615e498874054ab3104029780240914c50140c132321226228088464808a9608100702c12708ba84812c642a102598ac01a5195852a098180889063544),(0xd23eefb5d75806b89dcda38864b64661c9f5e2babc176a70b2d3a56f26f32e727e31fe7789e6e58a36284c9dbcb30e74d59821a10b67441120e71511dbf31ab50b42210b3baf1a3e4c47734dcff8958cfd1109f7ce27c18a062741ac46d7cd91,0x7413208444084451d48501104604c068b3980408840422121160844600658c78341c18180024668a9220480b8c940760b50821038273441010c51501633a18440140258228a50a1044455344031a81ae1001013e42228188062541a446c1c891),(0x44ee3263ec00331534507b30f50239085a477dc26fc97fafdd3677e1adedabf5a6627a917685fed951e16b05c441608531a6eebab7bf0ffa2c9d6923c000425ae070ded9cbf43ff0702d561449016826463c1cddf881bbc98109fdb0912bda0a,0x5c9601812402000310c10a308504200a188ca4d220b13a418220c4ac1700cc49329049900289169c4a408a09044020043184b638a739649c2011540242004250a0701ac901871eb02048c310010048264632184cec01aac801096da0110b580a),(0,0),(0x3ab08ab4b6d74c50e56bc9651caf5894b179e03465572acbdca5615696769c27053d6dc580568c9318a62a712d4d06df8fcf0933a8a96615b24c8891d85dee28deccf746ecda09546a23c7138dbf2215a9d969340b49504d34d905859a5a4fc,0x8020482e4971b288ed202044508b9ca5050108094844412451461041282e3192c9648008d0242841110660a6538444294c484083188002614b0e00011891a8820d8e45006648e00548a230c32acf32918089829300b41504d204901848a4a474),(0,0)]
def g191columns : IndexTree ColumnInfo := (.fork 19 (.fork 9 (.fork 4 (.leaf [(1,0,190,0,7),(2,0,189,0,8),(3,0,188,0,5),(4,0,187,0,7)]) (.fork 2 (.leaf [(6,0,185,0,5),(8,0,183,0,8)]) (.leaf [(0,8,163,20,6),(10,0,181,0,5),(12,0,179,0,5)]))) (.fork 5 (.fork 2 (.leaf [(4,8,163,16,5),(14,0,177,0,4)]) (.leaf [(16,0,175,0,8),(0,16,166,9,6),(1,16,166,8,5)])) (.fork 2 (.leaf [(19,0,172,0,4),(24,0,167,0,7)]) (.leaf [(16,8,163,4,5),(8,16,166,1,5),(25,0,166,0,4)])))) (.fork 9 (.fork 4 (.leaf [(9,16,166,0,4),(20,8,163,0,4),(32,0,159,0,8),(1,32,30,128,5)]) (.fork 2 (.leaf [(35,0,156,0,4),(40,0,151,0,5)]) (.leaf [(48,0,143,0,5),(56,0,135,0,4),(128,0,63,0,8)]))) (.fork 5 (.fork 2 (.leaf [(130,0,61,0,5),(4,128,27,32,5)]) (.leaf [(136,0,55,0,5),(160,0,31,0,7),(128,32,30,1,5)])) (.fork 2 (.leaf [(32,128,27,4,5),(161,0,30,0,4)]) (.leaf [(129,32,30,0,4),(164,0,27,0,4),(36,128,27,0,4)])))))
def g191autos : Array (List Nat) := Array.mk [[],[84,115],[117,67,32],[116,83,32]]
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
def g251samples : Array (Bits × Bits) := Array.mk [(0x7c5b1073c997e37379da30f398119ee6fb6b9ec3f472bcb960b6e16b764eab308775a6f93b85666e9d3190b2b24d642ca5712b6de7ab3f7906c1699135342a691b3ae0a5aa4ef7bb316cf861cfcc30541d6a6cc4992b1a999615c8e8d911c1e1,0x2118206040004a02130d09680103a002090a061080141a8c00302460220208340600a251588102029c90b010225400202065234404234e080480294178042009180840240246b20a0024c060c50410001a48a084882a181106058840c1114140),(0xcce5a5f376b735aeaefe578ced15d32ecca61663a9af3bd1860bc21b19116b79223f9d41251db7915d2d676e62aaa4f819f9d341f91890478f7c179edecb18b88452ff03ce59b2503e9c1117dab8cd95ebc956b7a216470f30e3a2b3ec2d18bb,0x4842cb022293909020208080c0985104462050200a232050248f580a09002349282c0500277025a04229050a00aa2098018840837118b0c40a78400806c358a084123a0140090810bc8810142aa8e601010152222014470a10a222b02c2818b9),(0,0),(0x615f43b7c5899d56d0ed540d07e5651da134ed341e9bc1f74f237fc0ae8a342e74d0d54381c29b89aafb968c73300f2ad24e70d94c925aaf7c71d97b8e42ee34b1eb0d1c78f57307cdbb8ab0333b96f243ce283ea4988c525a6cf93575cb22d6,0x600508638c1a9f0381c44ce96aa5f40532886e32158a42c5402a7e6c4a89343c9410964685c08b09acb0120c353c06229a6c00c94c92de87444159522882ae0499430c1549527146cd2ac810537252985246622c84980c521a4cf835558922d2),(0x743743261165c64a5893c74b56706899b56f313d76fa70640bd59bea9f4cd6cd40c9796a92725dcea2baccf628444b5fc70e36349d152cf473b98c6d967cf8571ea4949a30a5a9a67c52f2db3fa12e66e966315b35ec80fa603e034c2e56ad7c,0x8e228200012500a04432a202145800c8c044118122412020998581138524c38140cb492802205484420a48e00002411d45001410a1402070b13084088559515204a0a28a24a10ca03050168720812c4621201151314480a8603203082a468c2c),(0xf3d9bb1a8ffcdc97c518eaf4c8cf14e122f0fafd99d5fdca7ef0f64eebb658a39d280ab679b66835384c18039df39cc970c09cab32e75b6d986af50aa1e14f67f56dcf6f41924d79e9e39f3990e7fa0a34138f4a5e417d209f607f101fc4fe09,0x9201861738918010c41062040c8818244620088911c0e1638783100880a45083c120082600262524204640020401ded90000982b30080131d06c4002816148a041658f0100904561e8880e0910f0e60220020e2216414120916065101cc4aa09),(0x8c34b489b6743f0cbbb4f14fa7d16d9fa49b993f9ba2b3789eb911d5e1cd7a6f64e2a177140a8013c504eb6dd8b5e7f7e94f5a351463882a81261e97691b96dcefd6ddbc37c1e3432aa0876640524995f6a595fd43d7d81429dbe94302afe942,0x269c30c1984c0e0408d2577d35632830a8c6a4165540daa693102041644d9ca647426045188a80110514e824d9155760ee46136c04410a2a918614976910825e2b85c52c35a0b36b4200852245520814f6b484dd43c398142959c9430287e142),(0x1bb2ab4aa0e85ba9e596de5ec3ce129b01134cce9757f2d674620576a8bd96bf3a893c9457f0a28da9ccac591d7731877093a6c205d64d4c2bcaa6363cd0b55e770f7a466dfb2a9c82572d4ce3aa90cf64d9c30549ce2fe50b809671629a567c,0xd9639e04222012901869c59f133e18908110146a61f169c201c69140019863c2e851098d7d900098988b54119762026501322c440c64c4e0e9086343c860556368a70222d632a1a145321c6e30c00cc44fdf181498e2ec50a809261621a5474),(0,0)]
def g251columns : IndexTree ColumnInfo := (.leaf [(8,0,243,0,7)])
def g251autos : Array (List Nat) := Array.mk [[],[84,115],[99,65],[118,84,115,65],[118,81],[118,84,99,81]]
def g251levels : Nat → Packing
  | _ => emptyPacking
def g251index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g251 : Forest := ⟨251,7,fun j => g251samples[j]?.getD (0,0),g251columns,g251autos,g251levels,g251index⟩
def g255samples : Array (Bits × Bits) := Array.mk [(0x9b665c544a8481c32c829a3849d25a0c2e734bceaece0410b1910c9246b692285657c973ca335d593cb00f0546b90059eb43e97a932728851785431870f031165ac8b80393ba6e576270cc58c906b870841734e15dc89803598ab05c2460a6b1,0x104454110880808228020a2041d8002c08600a02808c02009111060244ac12008614a1024802115108904700443200508241c8821224200116051018407029164080a01212302c0942400010c90428108414142154888803090a9048202086a0),(0xf315668af28fdb1ca228365b7ccc05a0011317731e21482f697635c521d4e57b4580944cacd08190116899ef79421d834fcee4e488905930903982805fb1c61927af17aaf49049a676974192f0d0160363a1bd03830701b0dc1f8281c2dc6123,0x83112a82400c43108201140b24040542001210600e014836084820c40800442b4181104024900000902098cc210099010006246088901220003082011981800902040620cc814002101041843090160043212902810201b054050081825c2101),(0x380526282fa13ac851f4c9c505254980d6e8ec3804b3594a769d93b950ebc251b0d8e2a15610b8154799066089743516386914b45de9a6e1e91c2d64aa4bec2945782990b2d68e61aa4d3cd1b24a6ab680984b4c1298da14a63264e421a50a46,0x184000082381184051a442400021c800c760240c008201086414493150c8805030586481420228050588002082640402084818905528808149002d00020c144045280184104604602a043c40824a60b20098024012185a048212646400810a02),(0x96903da21572f2b1f1c959078994a771bc47364121282ac5966e24786e0f6b8886ae49c27124b27b7242ff2e0094e0b4b1b582696d3c94568c371a6b03b30075a8d6353ad9672c0089eb12ba6325f80dd24d451b8459a7c113618d0b812f118c,0x86100cb01034a2a12848198388d4226018030240202c8a411a0a044824066a838a240842212092185a40cf0a0080e094a530c6680a1400448645526011312024a0c7343889210800016b021a61259805924545098441a1c11120810b812e1184),(0xca830c6ee5a1c1ac77b2c4bb013b84b271c7189edce77b42164b82b2ec44ccc2202552493f52e619512b4f09e2177ba801c291327039cbf4fba1fd7ca29d36ceca40c4508827295a1b45be11b7c00687be220f65622167c80c13fe90c415919,0x1282044674a181cc515204830038803270c71014e5265b22464b9241a4004482002443590d10ca0850630203a411b2a000c201185038c3861ba0d078200d6480c204804048212d4a89449e11258006869a220d60222163c80c12ea00c414819),(0xadcb89db333a54791fc5b16de6a74b1fbdaa5224c4caa060c8434905e130b3e50875189fa3aee40ebf67487ce98db2673644923b555505294552488c144494c2312ef3656d2d51ee39b1b44e04f3d3ec4d148000ab72771f011403179f478e82,0xa991884a13221d3803c5e045a0014312e78660240442614040424905201081f109410899826ca6043646807ca808b20b342020284941850001124c8410049440302c118d6904416438b533460072d3ec490080008b50771c0014031517470802),(0xccf1d170b069949f14600d7679a83ea985e068495997ad010287ff4ea745b576050c4fa9e8e0fabd2497448bd27a5aa8acea4ac0268e4d44dc2df9de452a225ad1457b3d721818b9bf9e05034d50ecb938aed67098a522a72856072e55b8d214,0xce85130b040942f1560095449a91aad8dc0e80b5196a18140955b282345b194266c47298868eeb9221d4601c27a00e8acf04a8036004c04cc8c58ecc43a23d68161791d311c0cb9abcc24434d40e8b9388ed67018a522072852072e55a0d214),(0x442aa5b9d884c622461c21eaaaf556fac8da8923687abbfb99c9c28096422e0eb83cb34c1d8918aec8c55d99f53bc2670104934ee2f27258616b2c55a56fa8970e02486406e9b92b5242282d15890d903f02672424a3e96d3ce1d022fa0aa8e8,0x460a679588446000a40a01aa08c414e80818810338389a92898982c08602320ec02091061180118a88016c815113416481048146a2821250206d8051a4632a958802cc600689381b004a400915810c003602652424a380613ce19002e808a0e8),(0,0)]
def g255columns : IndexTree ColumnInfo := (.leaf [(64,0,191,0,11)])
def g255autos : Array (List Nat) := Array.mk [[],[84,115],[117,67,32],[116,83,32]]
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
def g383samples : Array (Bits × Bits) := Array.mk [(0x22c0d3a3723e453b61b292904161c19166ba4156452239cb2ce776d1285888036922ca069735ba1c39466bb49cb80c880d6801ee650cd2ea8938a452f08d3169a1612a59384753bad95626662c63076161205bac29b905015369815a61884cb1,0x22a042a308281022412222104041018102a0455c0820218028210490004898014122a802062510400900403480940c80084001804506910881200012c0203148e041211030641239500420000c630440212052a0291101014268811220880c80),(0x3e4782180591e1e8ca415c93fb0e30440ddb7b080a80044a5e58703417b0ed0da2975b6df4e0151155ba1024096257dc7280e61c3739c9924483ab0a0d0a407f268250f5cf15b48886f76ba0ccf46838068d8de07060e07838bc1a040b61c283,0x9028018810161088ac0504223081040850928000290004c425070241b00400822080144b0c0241004a20000482053184202c40808184882448102000d0800b3040a404084018c8080110220c214483800898940502040781814120409604201),(0xc3b0d0243e2c92704a6d0bb89a642e3e324709614c855ba1b03c2574c53f0c84bca3b709607618aaaaca1686a79e094292d1a5b2e1a729d1ef4c761d2455891cd68664af136132ce19aaa19e6c55a2caed1460758145348a6cc923aa16a49516,0xc22070243c088a32102908b09820ae3610c20125cc051d809026055084360c62d8a3320940364922a8484682858e00c384d420b061233141a94434152055010c599024a50348105611a2a11e2441a2c2e41460350145348264c921aa12049512),(0x4138264952b1d12493a4452d72585b389605825093cff11edb60090262cf75191c382db2876b8a708e04945dba40fc5c0117030382d504a579e551698e39d387601c521a9a75d96750089c8958b895e01b82b803f01d0be08606741604bc230c,0x1080c0b03b031008084040c42504188060180103100c00a0a40008040890111041009902b010250040410442a404c140103030210c08ca050a00048c0a8c022200c1018d83149210000148108b815200b021800b00809600202141404b82204),(0x7a0c641d50044e150338db871c0d9c6d8b49b017941b1c71c485efc79a14e6ae159b09d8c200cd085276a758cd18f3623c4db7d00870524c281de7f5fe3e2adc1756b294808a0882ea6a1f2df107bc01d0df010f4d40469e2105ef94c107b239,0xd004201450464809021899a3188eb82288483003841b1c31c500f247991664ae92090048c000c90e723223084509b040f48cd45008304046281cf3843e140e8407928284000804822b6a8b24f004a801d0dd010f4440469e21056a80c1079039),(0xcc62da0a5fa8f5e2c996caf343c42faac6de9a345ff56a94813a6425060416282f4d23c281526277465dd835f65817a533b901ad51024edaaa84a94a69219208d911c25be8aad34a7f39eda22807bafd8e8540012ec5ecf42900c6dcd341c02,0x8452d0021128d5c8c9144a91d1c007ab845a00141d69e1982122246c02041428290423d28902225305595421e41c17a5023985a908040a15a0c4800269208200d9018058b1aa90485c38f99a2803baf58c8040010ec1ece00900c4d4d341002),(0xdaef1c77688221978d1e0c4ad4cf460c43747468370c9781a044ccfb808507cfc7550e6f05834be93d3c1e4e94918217a4e0da637baa95002472c84f89f63e421033ad28de7ab208228bfb0281a229d272553696158289b300da2c9976c32464,0x92e959624882001701040c005417432c02544069252c9701a0048cc280a00e56d4150e31071309c931151f4c9213080304e00a4233c09500a002c04d90b29c403071012c5a3a310c128ab91220a221c27244349605808983008a2c9966812464),(0,0),(0x941a1aee99450a81362f36506691ad42486aa7b56b55a36c2710c35afdccd2f0604110c2892f54d343a9228b60c516b3ea6e18394813263b179331842a516d8adc29c7c000c846f164b52014130d4016a078833106127956c94690a3b81ad1d8,0x4120210904c02803268a2402080b401402a07040a01006405204110294490a020401002d0205402c22800a1400c2280a20c04a14813021a0411310009012188c000460020c0069060300020050540108030832102126010c94480229002c198)]
def g383columns : IndexTree ColumnInfo := (.fork 29 (.fork 14 (.fork 7 (.fork 3 (.leaf [(1,0,382,0,9),(0,1,332,50,7),(2,0,381,0,9)]) (.leaf [(0,2,312,69,7),(3,0,380,0,6),(2,1,332,48,6),(1,2,312,68,6)])) (.fork 3 (.leaf [(4,0,379,0,11),(5,0,378,0,7),(7,0,376,0,5)]) (.leaf [(5,2,312,64,5),(8,0,375,0,9),(0,8,99,276,7),(12,0,371,0,8)]))) (.fork 7 (.fork 3 (.leaf [(13,0,354,0,4),(14,0,369,0,5),(16,0,367,0,11)]) (.leaf [(17,0,366,0,8),(18,0,365,0,7),(19,0,364,0,5),(18,1,332,32,5)])) (.fork 4 (.leaf [(24,0,359,0,8),(25,0,358,0,5),(28,0,355,0,7),(20,8,99,256,5)]) (.leaf [(32,0,351,0,11),(33,0,350,0,8),(32,1,332,18,6),(35,0,348,0,5)])))) (.fork 15 (.fork 7 (.fork 3 (.leaf [(34,1,332,16,5),(44,0,339,0,5),(49,0,334,0,7)]) (.leaf [(48,1,332,2,5),(33,16,326,8,5),(56,0,327,0,5),(64,0,319,0,11)])) (.fork 4 (.leaf [(65,0,318,0,7),(66,0,317,0,8),(67,0,316,0,5),(65,2,312,4,5)]) (.leaf [(70,0,313,0,7),(34,64,29,256,5),(256,0,127,0,9),(0,256,23,104,7)]))) (.fork 7 (.fork 3 (.leaf [(264,0,119,0,6),(256,8,99,20,6),(8,256,23,96,6)]) (.leaf [(268,0,115,0,5),(260,8,99,16,5),(280,0,103,0,5),(272,8,99,4,5)])) (.fork 4 (.leaf [(288,0,95,0,8),(289,0,94,0,5),(40,256,23,64,5),(304,0,79,0,5)]) (.leaf [(320,0,63,0,8),(322,0,61,0,5),(258,64,61,0,5),(352,0,31,0,7)])))))
def g383autos : Array (List Nat) := Array.mk [[],[84,131,98],[101,66,16],[100,131,82,16],[82,129,48],[101,100,131,98,129,48],[100,49,128],[101,84,131,66,49,128]]
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
theorem valid383 : Known known383 := extendKnown_ok valid255 low383 (by decide +kernel)
def hashdeadl14 (i : Nat) : Nat := 0x4592c8500000000002800049a6c68a83340e9800000aa00684000000054a001bcc7001e180000682000000000000001d46a1840000003a00000001c
def hashdeadl13 (i : Nat) : Nat := 0x301a0007b2f00e0aa2992094818000e2e0000000269e056438000000000d33e40e4a200074d00000000000003b10001e0240a9bd45d962582900000000000001430001e1400000fc03b84a000614e69108a1108000810000d04c9d0000000408800000160f24180010b9d040003080001e0c000000000001997f401183740ee12000000000080d312c00102c00000000012070000000001d35000308c000a4c0001b30000000cb3800183000070f0000001abcc008002c8cc133000000000000000000000020b000000064ec0a00000f8000cc5000105d8204160001a38001c1c467309c000000a7700000016de30f80000008380b08e000d3001
def hashdeadl12 (i : Nat) : Nat := (if i<1 then 0x7b02c3200425d610a000042a0327300000000106b33757005e04600006037d811679d009461963480703e1077f067f2582384275d80a540a20109b59b4006305d00000000ab6dfb0bf59ec084c806986b30597776440b146b100c50a956520000878e0000747c463e108bc029e7600000395ef090d06800000000f0550000d0b1e4af00000000f324d141840ca4380000000051505017000067300000e779907b0000e77730641201ea62a089a48ff0924111e9a7a041b2a180aee462f29d9b47b01eb0427030e02a5973605b9086f08d5081d04bb014363000006038c0b6d110106cc731308e0023a07fb1305601ba1839b4c088a10b88011043e427e75a600831464016903d3ba52b1ec095000ec050b011b0730478f11a0000755e331ef63db004a00a000069a91680e225f60f90092a9d0000764650a40000c591f95ac03baa33c5a1283d11871a6d2772c01c1057280f201f5012328b908232a5505e000fe02b507cf0809817c267c05c9528506d997696872194b206264030ad402d007d586d7228701d30605840f67838625a51443ce034d47ed45f704cb08730a1794e1252000070330000b56f0000b0b4000000000000a842e047609d406ae26b67b08a4de12aa0a34019000000000000b664342c50b50000c0af924dc9aa401870366002b26d00000000841e0000000060986614000000000000783ae10d980ee051d0ab4022a615808f0000a0832619a148d81500007000e007d616b032d01b483f163f00104028276b2015141030631049a027580cd0a7a05ab977802fb09ff07a97899053b0a80816e83be0790a1b809b8b460a4f0000178b0000847be03cf139a1170000b07850b3605408416262696b908af0aa7b1f5b446070d024601a42492101d496f4b4e035922127ab0000e18600008284831c00440000f031500310656013b071b045b25b4113766b5b4c6b0800008291b4888a50000000000000e38b0000225eb04d807230618425c0b097ae226f809e00000000f00d93480485e88728040000b11c3039204e9432711f445c905f004a300b97ada05680211292f09a7b1a696f3106704f19748066703f00000204d074ba20a118f025458794596091a06f000065946020913b783e342dd08c819b5b452076c21dc075e0991a4a183c3b19d7a750a68058c8379643a487b408d0523762d062b422e0b2d47fc0ac224a46231a5dca3b6069a4390000768a5433e07e0000da410b00003102090604000a010a1f88080000080d030b0c310304001300040113030203141f0c0001000232030b0801010a010007110002020208010605020401010119010b0304070203070506000210070d110100150b0a0504051d050002020b05000c0402003d0e1500260200020108040b03090500060204000d0602010100180501000001030f04 else 0xe0a0512830933085c048e216509713746026a02ec09cb040548400000268f701103ac254729fc29e8096145a39ab47552144806e00019612b7b4491ea44bc1)
def hashdeadl11 (i : Nat) : Nat := 0x5b144463e05aea749a36008e0000f05f008fc82400000000057a08357304bb42c02b0000807cd1701823000007095811411b96631031e07218223334c77b980e8010305dd000180820521064ca3ef0420000409b626cd483a833f03ac022e048a008f80a513f0000db73410f3393ca38834018881012b081c465a02c6142704300002631809700000000715300007115b00dd054b2886014000054161b183099000000000129f0870000a24110110427972915960000477d5b457113518aa01a00007134a023d08a1053002d678ef06b604a6076520f5468b025698fe62d5060c1370000e07eb793c95be02a510198285417000000000000000000005b72220ea00f9098e036e09602120000503908396112556c56084a3a211d0342f0784635707b4293308d0624205556235211962a72516903a0190235010e7765e07d5784f16feb3c248834149073d088b0134091f720f0803275f0052809446ed494b01b1b0305939136b20cf495111aba390000db890950e9807026e609a0205015880ba66b8778d4967988f077f007110cd289d0160000e278401d0000000000000000f032027400000000a08c6209804c4030102eb368a33f3b1d798e0000538a70215061a44e228300000000000000000000d01710838075e4517067406f00000000609a00003253a089a4002093b00a8125000090790000c0599583180c00000000c0411830f1160047224900000000906992725046700b000050511a67544b00000407c35bb06d0000504d3821ca470002762e0000cb1760948827b10a603b4009e06552019464444f9688a0286169097ab82524185057db2feb3d000e6303670ac01e70822426b090d664c05cf764008be03c365d6a2549347068706a71244461f086277c5780380d698dd120b27c20626037d807f403502fe1110000ea6e5071301cb0388044704f411c809595011003b20deb1a98372208b0561092820a91190049704bb03ec070670890335001a03f64504063613c50294b430832441aba46e146c8120193598c103df8314066401fd460e0745084044c100c7760b24b824f4006205b0000563070507a7c9058000000006a440000506e3040e97d006cd027646a6207807fb0450138e56fa018704e8482e0356085662f762c5b3be05eb81f1004f836000000000000000046203a6ac89692730000b034807a613d00008145702433536a79b0407805012a04e80082c50a0c0e782286421a0e4c00400004833a1491a02243880c0851202004211c6408c1835c192e081800c39681005000c04e408002001860c34c8040000000400008087400400100892c38005148410524200800478080001438126000000020022
def hashdeadl10 (i : Nat) : Nat := 0x1c05302000382d2ecf474c3a08f618409ea54931a0a2272b385214e934380040192451090d15cc0564307983441ce005970002c06068f08a82680cc070001a2c5d4a1440400018207150002808001022205d856c41e1700072d518800084a2900000a334a12801820030b1a27
def hashdeadl9 (i : Nat) : Nat := 0x202e0
def deadsamples : Array (Bits × Bits) := Array.mk [(0xf854605d026923a5a16008862c9d18d42fd85e54d221898f1e440284a107a02910c3e03c06c40d2642ca74f54627022c11e389d9b43b30c961ca72386ce81500aa210d1ba1a121108a6c99348979d054ac200727ac054c0970110780155ad581,0x6844620d0040231585204884208800c4270824141201090814040082a10700282003e02402c4084602ca04a440240a1091218919100a2084314a220840a00480aa210819a02120100a4409048968c05484200702a805440920100380144a9480),(0x80b20c31f72bfc4e1481d27000d43c9c5bd438a9c5e0286040f054f111d001ce10920229bde170b8d339029e2bcac4cd494fb74d1052452141a61c5b9ca1e642f40c600258428f0e5c00df481e03202a204cd465e10fe01206e82c7b03150603,0x80100c30e6089040109182600012282018c41889c5e0204002b0604000c009861080028b1c2120a0d12000120908c00d005a724402504200402010501c01c208540860025840090e1400964816012008204cd0254102a00206a0247b01150201),(0x12ce100c308544478a85796a2341d206e4242e31335abb35943abb40be28c8e05c4c115123137950052a02a9ba0d31c096458c656cc338623e92230683d8962194d5145c2aa62229438824d8e06246d0cd124850733918c390189888a426380a,0x10ca0000108540870900790a0240900460282200221a991490081a0028289000cc41010021184410080a0a28a20020c0200184206c0128621092200a03d8103080d5145c02a2022143880090804206d04d100840322918c190088800a4221002),(0x8628ebbd17000228c83c0291b729e17b3643984a392a815889878936d04e41b82b8e28807cc302855ead3105d9868885c748c2b0724ae81086518e259124cd4278a18b4aa01db88524c3a3435a0814469349110c18f0c24c2a8052bd88818268,0xc2206a1d05000020401c0090e509051303449848110100480001811490070429238c000818c508010485900541c68805c240409012420000024186258024450270208b02a00da0842041a3414a08100690490104085040042a8052bc00818028),(0xbc8ccda8781e4d8151cd3cf93a4a0a01509a42078c1bc4a783ea4aec6c7bbbd02ef85be130b1750bcd872a062d01842a34826040203d5b99ac8899721d47b82106b4f88001d04ee6f42e103eb14e0a090b95e84905a08ef7a2230402e2b14bc5,0x148981a0109a5c8210c1a4690a42220050930202c418c4a7837a48680e50b9d00c601bc02020f518c9002a002c1124282402304220255b598c9019921c51b8010494708001d04e62d42a103a30060a090b94e84905a08af280230402e2304b45),(0xd3b19712becef4647857054f8773c68492608a46265cd6cd0106c449284294958830b40e8328a4102841c46a63b66493288c7290c714876750b08cb0eb0a532e014ce7e24f9c08720240400006971f885be46b00080a21145aa7f52cf42a8012,0x92218c003e8654007015040a0c73c50280c0084821449285810a8400004080918c301008002824100801c000230200c0688c40804110046300b00cb28307502a0004c5624f9c086200004000021315805bc46800000a00145205f42ce0200002),(0x3145d24845746a93b60987114c89950ee90ab5809889781e716b0d141d9e036fea797f20c896480c8b565809c5575a81eabcad03980701be24b7e8d7401960b32336416db2f0c4c050f169960250e8b311988b92828b0074bd455ad232c2112c,0x2307720c00346283a400011d4c09950fa108a4001a095004514a0014181e2261ab3d3060c0d6480a2ac41009e4571880ea848181d90321bc24d38a860208103323340169a2b084c040f169960050c8b211800b9082890074b8455a803282012c),(0x49615339cc24bb41a658244591d020101222d0f578b5376254a121290a30cd5c4e2ad1d6dabfa9e032f022500c91031b32331a7a9ace0ca4e96243014a4009cd0d2a3210b66014de852533c420acc80ff443ad9cc5d0f4808cd621151170ac54,0x4900539a4030aa408668006591882010120251355ca1242200a1212102144d6e020a42d6d2878b6832b420400cb9813312321a4a924e408ce04943054c0001c10d2a2200b040149c8425334420acc80fa003859cc5d0e4000cd201111150ac54),(0x2108654280dbc21c532263cad6a2ab60a053058994f658a43b3dd89384745a04932387065124c385d01899e2cc083e3c1e3327061d61ca921a4965c8583262f4485320b5c04953298d1f02098424a39520b6148b236021a80528c3236c545ab4,0xc0001428049001c03a04a4012802a200013019184320c200a34088304a0580410028702010083a440180cc2080827381411260a0400ca0098085048489022c408432094004053098d0e0008842422012032140b21202188052801030c545a90)]
def deadcolumns : IndexTree ColumnInfo := (.fork 63 (.fork 31 (.fork 15 (.fork 7 (.fork 3 (.leaf [(1,0,510,0,12),(0,1,460,50,8),(2,0,509,0,12)]) (.leaf [(0,2,440,69,8),(3,0,508,0,9),(2,1,460,48,7),(4,0,507,0,12)])) (.fork 4 (.leaf [(0,4,369,138,8),(5,0,506,0,8),(6,0,505,0,9),(4,2,440,65,7)]) (.leaf [(2,4,369,136,7),(7,0,504,0,7),(5,2,440,64,6),(8,0,503,0,12)]))) (.fork 8 (.fork 4 (.leaf [(0,8,227,276,8),(9,0,486,0,8),(10,0,501,0,8),(12,0,499,0,9)]) (.leaf [(8,4,369,130,7),(4,8,227,272,7),(14,0,497,0,7),(10,4,369,128,6)])) (.fork 4 (.leaf [(15,0,480,0,4),(16,0,495,0,13),(0,16,486,9,10),(17,0,494,0,11)]) (.leaf [(16,1,460,34,7),(19,0,492,0,8),(16,4,353,138,7),(21,0,490,0,7)])))) (.fork 16 (.fork 8 (.fork 4 (.leaf [(21,2,424,64,5),(24,0,487,0,11),(8,16,486,1,9),(25,0,486,0,8)]) (.leaf [(9,16,486,0,8),(27,0,484,0,5),(11,16,484,0,5),(24,4,353,130,6)])) (.fork 4 (.leaf [(29,0,482,0,5),(26,4,353,128,5),(32,0,479,0,12),(0,32,94,385,8)]) (.leaf [(32,1,460,18,7),(1,32,94,384,7),(35,0,476,0,7),(34,1,460,16,6)]))) (.fork 8 (.fork 4 (.leaf [(36,0,347,0,8),(39,0,344,0,4),(40,0,471,0,8),(49,0,462,0,8)]) (.leaf [(48,1,460,2,6),(50,1,460,0,5),(56,0,455,0,7),(64,0,447,0,13)])) (.fork 4 (.leaf [(0,64,189,258,10),(66,0,445,0,11),(2,64,189,256,9),(67,0,444,0,8)]) (.leaf [(66,1,396,48,6),(70,0,441,0,8),(69,2,440,0,5),(74,0,437,0,7)]))))) (.fork 31 (.fork 15 (.fork 7 (.fork 3 (.leaf [(74,4,305,128,5),(80,0,431,0,11),(83,0,428,0,7)]) (.leaf [(96,0,415,0,9),(96,1,396,18,6),(98,1,396,16,5),(128,0,383,0,13)])) (.fork 4 (.leaf [(128,1,332,50,7),(3,128,344,36,6),(132,0,379,0,11),(4,128,347,32,9)]) (.leaf [(133,0,378,0,7),(134,0,377,0,8),(132,2,312,65,6),(133,2,312,64,5)]))) (.fork 8 (.fork 4 (.leaf [(136,0,375,0,9),(128,8,99,276,7),(140,0,371,0,8),(132,8,99,272,6)]) (.leaf [(138,4,369,0,5),(144,0,367,0,11),(152,4,353,2,5),(160,0,351,0,11)])) (.fork 4 (.leaf [(160,1,332,18,6),(162,1,332,16,5),(164,0,347,0,8),(36,128,347,0,8)]) (.leaf [(172,0,339,0,5),(176,1,332,2,5),(180,0,331,0,5),(192,0,319,0,11)])))) (.fork 16 (.fork 8 (.fork 4 (.leaf [(198,0,313,0,7),(256,0,255,0,12),(258,0,189,0,8),(260,0,251,0,8)]) (.leaf [(264,0,247,0,9),(256,8,227,20,7),(8,256,151,96,7),(268,0,243,0,7)])) (.fork 4 (.leaf [(260,8,227,16,6),(273,0,238,0,7),(280,0,231,0,8),(276,8,227,0,5)]) (.leaf [(288,0,223,0,9),(256,32,94,129,7),(32,256,151,72,7),(257,32,94,128,6)]))) (.fork 8 (.fork 4 (.leaf [(296,0,215,0,7),(40,256,151,64,6),(304,0,207,0,6),(288,16,198,9,6)]) (.leaf [(273,32,78,128,5),(56,256,135,64,5),(320,0,191,0,11),(256,64,189,2,9)])) (.fork 4 (.leaf [(322,0,189,0,8),(258,64,189,0,8),(324,0,187,0,7),(324,8,163,16,5)]) (.leaf [(321,32,30,128,5),(388,8,99,16,5),(168,256,23,64,5),(224,256,23,8,5)]))))))
def deadautos : Array (List Nat) := Array.mk [[],[118,130,81],[100,131,82,16],[118,133,100,131,50,33,16],[116,83,32],[118,116,83,130,49,32],[118,133,33,48],[82,129,48],[118,133,116,83,82,81,80],[116,50,129,80],[100,49,128],[118,100,83,130,81,128]]
def dead : Forest := ⟨511,14,fun j => deadsamples[j]?.getD (0,0),deadcolumns,deadautos,fun _ => emptyPacking,fun _ _ => none⟩
set_option maxHeartbeats 0 in
theorem geomdead : graphValid dead (boundsBefore known383) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=5) ?_⟩,listPieces_all (d:=3) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

def ImpossibleU (T : Sig) (cap tm : Nat) (S : Finset Sig) : Prop :=
  ∀ k t, k ≤ cap → (tm = 0 → t = 0) → ¬Live T k t S

theorem imp_to_impU {T cap tm S} (h : Impossible T cap S) : ImpossibleU T cap tm S :=
  fun k t hk _ => h k t hk

theorem rotate_excludedU {T n tm} {ws : List Sig} (hi : ImpossibleU T n tm ws.toFinset)
    (p : List Move) (ok : autoOK T p = true) : ImpossibleU T n tm (ws.map (movedWord p.reverse)).toFinset := by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p) := fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  intro k t hk ht h
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
    · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩; simpa only [inv] using hw
    · intro ha; exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
  rw [goal,back] at run
  exact hi k t hk ht run

def childU (tm cap len : Nat) : Nat :=
  if len == cap || tm == 0 then 0 else 1

theorem enum_stepU {T : Sig} {cap tm : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (oneStep : tm > 0 → ∀ a ∈ ws, ∀ keep, neg a ∉ ws → proper (neg a) →
      (childOne ws a keep).length ≤ cap →
      ImpossibleU T (cap-1) (childU tm cap (childOne ws a keep).length) (childOne ws a keep).toFinset)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      ImpossibleU T (cap-1) (childU tm cap (childTwo ws a b d ka kb).length)
        (childTwo ws a b d ka kb).toFinset) :
    ImpossibleU T cap tm ws.toFinset := by
  classical
  intro k t hk ht h
  generalize he : ws.toFinset = S at h
  induction h using Live.recurse with
  | stop hp =>
    exact out (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  | @unary k t U a ha hf tail _ =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have fresh : neg a ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let keep := decide (a ∈ U)
    have er := erase_fin hn a
    have rest : (kept keep a (ws.erase a)).toFinset = U := by
      rw [kept_fin,er,he]; by_cases hm : a ∈ U <;> simp [keep,hm]
    have nd : (childOne ws a keep).Nodup := by
      have na : a ∉ ws.erase a := hn.not_mem_erase
      refine List.nodup_cons.mpr ⟨fun h => hf (Finset.mem_insert_of_mem (rest ▸ List.mem_toFinset.mpr h)),
        kept_nd keep a (ws.erase a) (hn.erase _) na⟩
    have eq : (childOne ws a keep).toFinset = insert (neg a) U := by simp [childOne,rest]
    have sc := (live_size tail).2
    have len : (childOne ws a keep).length ≤ cap := by rw [←List.toFinset_card_of_nodup nd,eq]; omega
    have htm_pos : tm > 0 := by
      by_contra h0
      have := ht (by omega); omega
    have ht' : childU tm cap (childOne ws a keep).length = 0 → t = 0 := by
      intro hcu
      unfold childU at hcu
      by_cases hlen : (childOne ws a keep).length = cap
      · rw [←List.toFinset_card_of_nodup nd,eq] at hlen; omega
      · have hne : ((childOne ws a keep).length == cap || tm == 0) = false := by
          simp [beq_eq_false_iff_ne.mpr hlen, beq_eq_false_iff_ne.mpr (by omega : tm ≠ 0)]
        rw [hne] at hcu; cases hcu
    exact oneStep htm_pos a am keep fresh hz len k t (by omega) ht' (eq.symm ▸ tail)
  | @binary k t U a b d ha hb hab hf tail _ =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest=(ws.erase a).erase b by rfl,erase_fin (hn.erase _) b,erase_fin hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kept_fin, kept_fin, er, he]
      ext j
      by_cases hja : j = a
      · subst j; by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> simp [ka, kb, aa, bb, hab]
      · by_cases hjb : j = b
        · subst j; by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> simp [ka, kb, aa, bb, hja]
        · by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> simp [ka, kb, aa, bb, hja, hjb]
    have rn : rest.Nodup := (hn.erase _).erase _
    have ar : a ∉ rest := fun h => hn.not_mem_erase (List.mem_of_mem_erase h)
    have br : b ∉ rest := (hn.erase a).not_mem_erase
    have nk := kept_nd kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept,ar,hab]
    have nd : (childTwo ws a b d ka kb).Nodup :=
      List.nodup_cons.mpr ⟨fun h => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h))),
        kept_nd ka a _ nk ax⟩
    have eq : (childTwo ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b::kept ka a (kept kb b rest)).toFinset = _; simp [ke]
    have sc := (live_size tail).2
    have len : (childTwo ws a b d ka kb).length ≤ cap := by rw [←List.toFinset_card_of_nodup nd,eq]; omega
    have ht' : childU tm cap (childTwo ws a b d ka kb).length = 0 → t = 0 := by
      intro hcu
      unfold childU at hcu
      by_cases hlen : (childTwo ws a b d ka kb).length = cap
      · rw [←List.toFinset_card_of_nodup nd,eq] at hlen; omega
      · by_cases htm0 : tm = 0
        · exact ht htm0
        · have hne : ((childTwo ws a b d ka kb).length == cap || tm == 0) = false := by
            simp [beq_eq_false_iff_ne.mpr hlen, beq_eq_false_iff_ne.mpr htm0]
          rw [hne] at hcu; cases hcu
    exact twoStep a am b bm d ka kb hab fresh hz len k t (by omega) ht' (eq.symm ▸ tail)

theorem closeChildU_sound {raw T pools links k tm rest op}
    (pValid : ∀ p ∈ pools, ValidPool raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → ImpossibleU T k tm (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild pools links k rest op = true) :
    ImpossibleU T k tm (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]; exact lValid _ _ hx
  · exact imp_to_impU (scalarPoolCut_sound (pValid _ hp) nd ok)

abbrev LinkFn := Nat → List (List Sig)
abbrev NodeContextU :=
  Nat × Nat × Nat × List Decor × CovPair × List BoundPool × List QuickPool × LinkFn × LinkFn

def ctxWireU (c : NodeContextU) (i : Nat) : Decor := c.2.2.2.1.getD i defaultDecor

def evalMoveU (c : NodeContextU) (op : Nat) (a b z : Decor) (ka kb : Bool) : Bool :=
  let (cap,tm,n,ws,cov,pools,qpools,l0,l1) := c
  let un := op == 2
  let len := 1 + (n - (if ka then 0 else 1) - (if un || kb then 0 else 1))
  if len > cap then true else
    let ct := childU tm cap len
    let d := ct == 0
    if (restCov (getCov cov d) (column d a.2) (column d b.2) un ka kb ||| column d z.2) != BitVec.allOnes 768 then true else
    if !properB z.1 || ws.any (fun v => v.1 == z.1) then true else
    if qpools.any (fun qp => fastCost qp (cap-1) a b op ka kb) then true else
      let rest := (opKeep un ka kb a b ws).map Prod.fst
      let links := if d then l0 else l1
      closeChild pools links (cap-1) rest (movedChoice op a b)

theorem evalMoveU_sound {raw T r s ws pools l0 l1 cap tm a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : (op == 2) = false → a ≠ b) (hcap : 0 < cap)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv0 : ∀ tag xs, xs ∈ l0 tag → ImpossibleU T (cap-1) 0 (List.toFinset xs))
    (lv1 : ∀ tag xs, xs ∈ l1 tag → ImpossibleU T (cap-1) 1 (List.toFinset xs))
    (pro : proper (movedDecor op a b).1) (fresh : (movedDecor op a b).1 ∉ ws.map Prod.fst)
    (test : evalMoveU (cap,tm,ws.length,ws,preCov ws,pools,pools.map (summarizePool ws),l0,l1)
      op a b (movedDecor op a b) ka kb = true) :
    ImpossibleU T (cap-1) (childU tm cap (moveFront ws op a b ka kb).length)
      (moveFront ws op a b ka kb).toFinset := by
  let z := movedDecor op a b
  let rest := opKeep (op==2) ka kb a b ws
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := keep_sub _ _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm), nd.sublist (sub.map _)⟩
  have val := moved_full op a b
  have fr : ws.any (fun v => v.1 == z.1) = false := by
    apply Bool.eq_false_iff.mpr; intro hh
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hh
    exact fresh ((beq_iff_eq.mp he).symm ▸ List.mem_map_of_mem hx)
  have pp : properB z.1 = true := by simpa [properB,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if (op==2) || kb then 0 else 1)) = child.length := by
    change _ = (z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,len_keep _ _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k t hk ht h
  have hsz := (live_size h).2
  change child.toFinset.card + t ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold evalMoveU at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  let ct := childU tm cap child.length
  have ht0 : (ct == 0) = true → t = 0 := fun hct => ht (beq_iff_eq.mp hct)
  have sep := cover_sound h rfl (pair_sep pairs) (ct == 0) ht0
  let d := ct == 0
  have g : (coverage d rest).1 = covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz := rest_coverage ha hb (op==2) ka kb d ne
  have hf := moved_faithful (faith _ ha) (faith _ hb) op
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) (op==2) ka kb ||| column d z.2) != BitVec.allOnes 768) = false := by
    rw [sep, bne_self_eq_false]
  change (if (_ != _) then true else if !properB z.1 || ws.any (fun v => v.1 == z.1) then true else if _ then true else _) = true at test
  rw [be, pp, fr] at test
  simp only [Bool.false_eq_true, ite_false, Bool.not_true, Bool.false_or] at test
  have nd' : (choiceVal (movedChoice op a b) :: rest.map Prod.fst).Nodup := val ▸ ndc
  have h' : Live T k t (choiceVal (movedChoice op a b) :: rest.map Prod.fst).toFinset := val ▸ h
  by_cases hq : (pools.map (summarizePool ws)).any (fun qp => fastCost qp (cap-1) a b op ka kb) = true
  · obtain ⟨qp,hqp,hfc⟩ := List.any_eq_true.mp hq
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hqp
    exact scalarPoolCut_sound (pv p hp) nd' (fastCost_good ha hb hfc) k t hk h'
  · have hqf : (pools.map (summarizePool ws)).any (fun qp => fastCost qp (cap-1) a b op ka kb) = false :=
      Bool.eq_false_iff.mpr hq
    change (if ((pools.map (summarizePool ws)).any fun qp => fastCost qp (cap-1) a b op ka kb) = true then true else _) = true at test
    rw [hqf] at test
    simp only [Bool.false_eq_true, ite_false] at test
    by_cases hd : d = true
    · dsimp only [d, ct] at hd; rw [hd] at test; simp only [ite_true] at test
      exact closeChildU_sound pv lv0 nd' test k t hk (fun _ => ht0 hd) h'
    · have hdf : d = false := Bool.eq_false_iff.mpr hd
      dsimp only [d, ct] at hdf; rw [hdf] at test; simp only [Bool.false_eq_true, ite_false] at test
      exact closeChildU_sound pv lv1 nd' test k t hk (fun h0 => by cases h0) h'

def testPairU (ctx : NodeContextU) (a b : Decor) (d : Bool) : Bool :=
  let op := if d then 1 else 0
  let z := movedDecor op a b
  evalMoveU ctx op a b z false false && evalMoveU ctx op a b z true false &&
    evalMoveU ctx op a b z false true && evalMoveU ctx op a b z true true

def testRowU (ctx : NodeContextU) (a : Decor) (bs : List Decor) : Bool :=
  let unOk := if ctx.2.1 == 0 then true else
    let n := movedDecor 2 a a
    evalMoveU ctx 2 a a n false false && evalMoveU ctx 2 a a n true true
  unOk && bs.all (fun b => testPairU ctx a b false && testPairU ctx a b true)

def testAllU (ctx : NodeContextU) : List Decor → Bool
  | [] => true
  | a :: ws => testRowU ctx a ws && testAllU ctx ws

theorem all_unaryU {ctx} {ws : List Decor} (h : testAllU ctx ws = true) (ht : ctx.2.1 > 0) {a : Decor} (ha : a ∈ ws) (keep : Bool) :
    evalMoveU ctx 2 a a (movedDecor 2 a a) keep keep = true := by
  induction ws with
  | nil => cases ha
  | cons x xs ih =>
    simp only [testAllU, Bool.and_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | hm
    · have hr := h.1
      simp only [testRowU, Bool.and_eq_true] at hr
      have hne : (ctx.2.1 == 0) = false := beq_eq_false_iff_ne.mpr (by omega)
      have hu := hr.1
      rw [hne] at hu; simp only [Bool.false_eq_true, ite_false, Bool.and_eq_true] at hu
      cases keep <;> [exact hu.1; exact hu.2]
    · exact ih h.2 hm

theorem all_binaryU {ctx} {ws : List Decor} (h : testAllU ctx ws = true) {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws) (ne : a ≠ b) (d : Bool) :
    testPairU ctx a b d = true ∨ testPairU ctx b a d = true := by
  induction ws with
  | nil => cases ha
  | cons x xs ih =>
    simp only [testAllU, Bool.and_eq_true, testRowU, List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
    · exact False.elim (ne rfl)
    · left; cases d <;> [exact (h.1.2 b hb').1; exact (h.1.2 b hb').2]
    · right; cases d <;> [exact (h.1.2 a ha').1; exact (h.1.2 a ha').2]
    · exact ih h.2 ha' hb'

theorem testPairU_at {ctx a b d} (h : testPairU ctx a b d = true) (ka kb : Bool) :
    evalMoveU ctx (if d then 1 else 0) a b (movedDecor (if d then 1 else 0) a b) ka kb = true := by
  simp only [testPairU, Bool.and_eq_true] at h
  cases ka <;> cases kb <;> simp [h]

theorem nodeU_sound {raw T r s ws pools l0 l1 cap tm}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv0 : ∀ tag xs, xs ∈ l0 tag → ImpossibleU T (cap-1) 0 (List.toFinset xs))
    (lv1 : ∀ tag xs, xs ∈ l1 tag → ImpossibleU T (cap-1) 1 (List.toFinset xs))
    (checks : cap = 0 ∨ testAllU (cap,tm,ws.length,ws,preCov ws,pools,pools.map (summarizePool ws),l0,l1) ws = true) :
    ImpossibleU T cap tm (ws.map Prod.fst).toFinset := by
  rcases checks with rfl | checks
  · intro k t hk _ h
    have hk0 : k = 0 := by omega
    subst hk0
    generalize he : (ws.map Prod.fst).toFinset = S at h
    have eqS : S = {_} := h (fun k _ S => k = 0 → S = {_}) (fun _ _ => rfl)
      (fun _ _ _ hn => False.elim (Nat.succ_ne_zero _ hn))
      (fun _ _ _ _ _ hn => False.elim (Nat.succ_ne_zero _ hn)) rfl
    exact out (List.mem_toFinset.mp ((he.trans eqS).symm ▸ Finset.mem_singleton_self _))
  by_cases hc : cap = 0
  · subst hc
    intro k t hk _ h
    have hk0 : k = 0 := by omega
    subst hk0
    generalize he : (ws.map Prod.fst).toFinset = S at h
    have eqS : S = {_} := h (fun k _ S => k = 0 → S = {_}) (fun _ _ => rfl)
      (fun _ _ _ hn => False.elim (Nat.succ_ne_zero _ hn))
      (fun _ _ _ _ _ hn => False.elim (Nat.succ_ne_zero _ hn)) rfl
    exact out (List.mem_toFinset.mp ((he.trans eqS).symm ▸ Finset.mem_singleton_self _))
  have hc' : 0 < cap := by omega
  apply enum_stepU nd out
  · intro htpos v hv keep fresh pro len
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hv
    have hf := unary_front nd ha keep
    have hev := evalMoveU_sound (op := 2) pairs faith nd ha ha (by simp) hc' pv lv0 lv1 pro fresh (all_unaryU checks htpos ha keep)
    have hlenEq : (moveFront ws 2 a a keep keep).length = (childOne (ws.map Prod.fst) a.1 keep).length := by
      have nd1 : (moveFront ws 2 a a keep keep).Nodup := by
        unfold moveFront
        have sub := keep_sub ws a a true keep keep
        exact List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm), nd.sublist (sub.map _)⟩
      have nd2 : (childOne (ws.map Prod.fst) a.1 keep).Nodup := by
        unfold childOne
        have na : a.1 ∉ (ws.map Prod.fst).erase a.1 := nd.not_mem_erase
        refine List.nodup_cons.mpr ⟨fun hm => ?_, kept_nd keep a.1 _ (nd.erase _) na⟩
        rw [keep_mem] at hm
        rcases hm with ⟨heq,_⟩ | hm
        · exact fresh (heq.symm ▸ List.mem_map_of_mem ha)
        · exact fresh (List.mem_of_mem_erase hm)
      rw [←List.toFinset_card_of_nodup nd1, ←List.toFinset_card_of_nodup nd2, hf]
    rw [hf, hlenEq] at hev
    exact hev
  · intro a ha b hb d ka kb ne fresh pro len
    obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
    obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
    have ab : a ≠ b := fun e => ne (congrArg Prod.fst e)
    have one (a b : Decor) (aa : a ∈ ws) (bb : b ∈ ws) (ne' : a.1 ≠ b.1) (ka kb : Bool)
        (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
        (test : testPairU (cap,tm,ws.length,ws,preCov ws,pools,pools.map (summarizePool ws),l0,l1) a b d = true) :
        ImpossibleU T (cap-1) (childU tm cap (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).length)
          (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
      have hf := binary_front nd aa bb ne' d ka kb
      have eq : (movedDecor (if d then 1 else 0) a b).1 = bin d a.1 b.1 := by cases d <;> rfl
      have hev := evalMoveU_sound (op := if d then 1 else 0) pairs faith nd aa bb (fun _ e => ne' (congrArg Prod.fst e)) hc' pv lv0 lv1
        (eq ▸ pr) (eq ▸ fr) (testPairU_at test ka kb)
      have hlenEq : (moveFront ws (if d then 1 else 0) a b ka kb).length =
          (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).length := by
        have nd1 : (moveFront ws (if d then 1 else 0) a b ka kb).Nodup := by
          unfold moveFront
          have sub := keep_sub ws a b ((if d then 1 else 0) == 2) ka kb
          exact List.nodup_cons.mpr ⟨fun hm => (eq ▸ fr) ((sub.map _).subset hm), nd.sublist (sub.map _)⟩
        have nd2 : (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).Nodup := by
          unfold childTwo
          let r0 := ((ws.map Prod.fst).erase a.1).erase b.1
          have rn : r0.Nodup := (nd.erase _).erase _
          have ar : a.1 ∉ r0 := fun h => nd.not_mem_erase (List.mem_of_mem_erase h)
          have br : b.1 ∉ r0 := (nd.erase a.1).not_mem_erase
          have nk := kept_nd kb b.1 r0 rn br
          have ax : a.1 ∉ kept kb b.1 r0 := by cases kb <;> simp [kept,ar,ne']
          refine List.nodup_cons.mpr ⟨fun hm => ?_, kept_nd ka a.1 _ nk ax⟩
          rw [keep_mem] at hm
          rcases hm with ⟨heq,_⟩ | hm
          · exact fr (heq.symm ▸ List.mem_map_of_mem aa)
          · rw [keep_mem] at hm
            rcases hm with ⟨heq,_⟩ | hm
            · exact fr (heq.symm ▸ List.mem_map_of_mem bb)
            · exact fr (List.mem_of_mem_erase (List.mem_of_mem_erase hm))
        rw [←List.toFinset_card_of_nodup nd1, ←List.toFinset_card_of_nodup nd2, hf]
      rw [hf, hlenEq] at hev
      exact hev
    rcases all_binaryU checks haW hbW ab d with hh | hh
    · exact one a b haW hbW ne ka kb pro fresh hh
    · have hsw := childTwo_swap (ws.map Prod.fst) nd a.1 b.1 d ka kb
      have hlenSw : (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).length =
          (childTwo (ws.map Prod.fst) b.1 a.1 d kb ka).length := by
        have ndA : (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).Nodup := by
          unfold childTwo
          let rA := ((ws.map Prod.fst).erase a.1).erase b.1
          have rn : rA.Nodup := (nd.erase a.1).erase b.1
          have ar : a.1 ∉ rA := fun h => nd.not_mem_erase (List.mem_of_mem_erase h)
          have br : b.1 ∉ rA := (nd.erase a.1).not_mem_erase
          have nk := kept_nd kb b.1 rA rn br
          have ax : a.1 ∉ kept kb b.1 rA := by cases kb <;> simp [kept,ar,ne]
          refine List.nodup_cons.mpr ⟨fun hm => ?_, kept_nd ka a.1 _ nk ax⟩
          rw [keep_mem] at hm; rcases hm with ⟨heq,_⟩ | hm
          · exact fresh (heq.symm ▸ List.mem_map_of_mem haW)
          · rw [keep_mem] at hm; rcases hm with ⟨heq,_⟩ | hm
            · exact fresh (heq.symm ▸ List.mem_map_of_mem hbW)
            · exact fresh (List.mem_of_mem_erase (List.mem_of_mem_erase hm))
        have ndB : (childTwo (ws.map Prod.fst) b.1 a.1 d kb ka).Nodup := by
          unfold childTwo
          let rB := ((ws.map Prod.fst).erase b.1).erase a.1
          have rn : rB.Nodup := (nd.erase b.1).erase a.1
          have br : b.1 ∉ rB := fun h => nd.not_mem_erase (List.mem_of_mem_erase h)
          have ar : a.1 ∉ rB := (nd.erase b.1).not_mem_erase
          have nk := kept_nd ka a.1 rB rn ar
          have bx : b.1 ∉ kept ka a.1 rB := by cases ka <;> simp [kept,br,Ne.symm ne]
          refine List.nodup_cons.mpr ⟨fun hm => ?_, kept_nd kb b.1 _ nk bx⟩
          rw [bin_comm d b.1 a.1] at hm
          rw [keep_mem] at hm; rcases hm with ⟨heq,_⟩ | hm
          · exact fresh (heq.symm ▸ List.mem_map_of_mem hbW)
          · rw [keep_mem] at hm; rcases hm with ⟨heq,_⟩ | hm
            · exact fresh (heq.symm ▸ List.mem_map_of_mem haW)
            · exact fresh (List.mem_of_mem_erase (List.mem_of_mem_erase hm))
        rw [←List.toFinset_card_of_nodup ndA, ←List.toFinset_card_of_nodup ndB, hsw]
      rw [hsw, hlenSw]
      exact one b a hbW haW (Ne.symm ne) kb ka (bin_comm d a.1 b.1 ▸ pro) (bin_comm d a.1 b.1 ▸ fresh) hh
abbrev PackingT := Nat × Nat × Nat × Nat × (Nat → Nat)
def emptyPackingT : PackingT := (0, 0, 0, 0, fun _ => 0)

def deadWires : List Decor := wiresOf dead
def deadSigs : List Sig := deadWires.map Prod.fst

def decodeSigs (n : Nat) (bits : Nat) (ws : List Sig) : List Sig :=
  match n with
  | 0 => ws
  | k + 1 =>
    let a := ws.getD (bits &&& 15) zero
    let b := ws.getD ((bits >>> 4) &&& 15) zero
    let op := (bits >>> 8) &&& 3
    decodeSigs k (bits >>> 10) (ws ++ [if op = 2 then neg a else bin (op == 1) a b])

theorem decodeSigs_eq (n bits : Nat) (ws : List Decor) :
    decodeSigs n bits (ws.map Prod.fst) = (decodeBank n bits ws).map Prod.fst := by
  induction n generalizing bits ws with
  | zero => rfl
  | succ k ih =>
    simp only [decodeSigs, decodeBank]
    have hget : ∀ i, (ws.map Prod.fst).getD i zero = (ws.getD i defaultDecor).1 := by
      intro i
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
      cases ws[i]? <;> rfl
    have hcode : (if ((bits >>> 8) &&& 3) = 2 then neg ((ws.map Prod.fst).getD (bits &&& 15) zero)
        else bin (((bits >>> 8) &&& 3) == 1) ((ws.map Prod.fst).getD (bits &&& 15) zero) ((ws.map Prod.fst).getD ((bits >>> 4) &&& 15) zero)) =
        (codeDecor ((bits >>> 8) &&& 3) (ws.getD (bits &&& 15) defaultDecor) (ws.getD ((bits >>> 4) &&& 15) defaultDecor)).1 := by
      rw [hget, hget]
      unfold codeDecor dbin dneg
      split
      · rfl
      · split <;> rfl
    rw [hcode, ← List.map_singleton, ← List.map_append]
    exact ih (bits >>> 10) _

theorem selectLive_map {α β : Type} (f : α → β) (bits : Nat) (ws : List α) :
    selectLive bits (ws.map f) = (selectLive bits ws).map f := by
  induction ws generalizing bits with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, selectLive]
    split <;> simp [ih]

def readNodeT (levels : Nat → PackingT) (slot i : Nat) : Nat × List Decor × List Decor :=
  let raw := deadWires
  let (_, depth, _, _, data) := levels slot
  let len := 10 * depth
  let width := len + raw.length + depth
  let recp := packedAt data (i * width) width
  let ops := recp &&& ((1 <<< len) - 1)
  let bank := decodeBank depth ops raw
  (ops, bank, selectLive (recp >>> len) bank)

def stateSetT (levels : Nat → PackingT) (slot i : Nat) : List Sig :=
  let (_, depth, _, _, data) := levels slot
  let len := 10 * depth
  let width := len + deadSigs.length + depth
  let recp := packedAt data (i * width) width
  let ops := recp &&& ((1 <<< len) - 1)
  selectLive (recp >>> len) (decodeSigs depth ops deadSigs)

theorem stateSetT_eq (levels : Nat → PackingT) (slot i : Nat) :
    stateSetT levels slot i = (readNodeT levels slot i).2.2.map Prod.fst := by
  unfold stateSetT readNodeT
  rcases levels slot with ⟨num, depth, cw, offw, data⟩
  dsimp only
  have hlen : deadSigs.length = deadWires.length := by simp [deadSigs]
  rw [hlen]
  dsimp only [deadSigs]
  rw [decodeSigs_eq, selectLive_map]


def linkedSetT (levels : Nat → PackingT) (slot : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (levels slot).1 then none else
    (dead.autos[pair.2]?).map fun perm => (stateSetT levels slot pair.1).map (movedWord (perm.map swapRows).reverse)

theorem linkedSetU_sound (levels : Nat → PackingT) (k tm : Nat)
    (names : ∀ x ∈ dead.autos.toList, autoOK (targetOf dead) (x.map swapRows) = true)
    (earlier : ∀ i < (levels (3*k+tm)).1, ImpossibleU (targetOf dead) k tm (stateSetT levels (3*k+tm) i).toFinset)
    {pair out} (h : linkedSetT levels (3*k+tm) pair = some out) :
    ImpossibleU (targetOf dead) k tm out.toFinset := by
  unfold linkedSetT at h
  split at h
  · cases h
  next valid =>
    cases e : dead.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact rotate_excludedU (earlier _ (by omega)) _ (names _ (by simpa using Array.mem_of_getElem? e))

def contextOfU (levels : Nat → PackingT) (idx0 idx1 : Nat → Nat → Option (Nat × Nat)) (k tm i : Nat) : NodeContextU :=
  let slot := 3 * k + tm
  let raw := deadWires
  let (num, depth, cw, offw, data) := levels slot
  let (ops, bank, ws) := readNodeT levels slot i
  let start := num * (10 * depth + raw.length + depth)
  let pos := start + num * offw + packedAt data (start + i * offw) offw
  let nr := packedAt data pos 5
  let st := pos + 5
  let rules := (getPairs data cw depth nr st).filterMap (fun (a, b) => buildRule dead ops depth bank a b)
  let ls0 := fun tag => ((idx0 slot tag).bind (linkedSetT levels (3*(k-1)))).toList
  let ls1 := fun tag => ((idx1 slot tag).bind (linkedSetT levels (3*(k-1)+1))).toList
  (k, tm, ws.length, ws, preCov ws, rules, rules.map (summarizePool ws), ls0, ls1)

def prelimU (T : Sig) (c : NodeContextU) : Bool :=
  let ws := c.2.2.2.1.map Prod.fst
  decide ws.Nodup && !(ws.contains T)

def nodeVerifiedU (levels : Nat → PackingT) (idx0 idx1 : Nat → Nat → Option (Nat × Nat)) (k tm i : Nat) : Bool :=
  let c := contextOfU levels idx0 idx1 k tm i
  prelimU (targetOf dead) c && (if k = 0 then true else testAllU c c.2.2.2.1)

theorem nodeVerifiedU_sound (levels : Nat → PackingT) (idx0 idx1 : Nat → Nat → Option (Nat × Nat)) (k tm i : Nat)
    (samples : properPairs (targetOf dead) (asRow fun j => (dead.samples j).1) (asRow fun j => (dead.samples j).2))
    (cols : ∀ ci ∈ dead.cols.values, Slice (vars dead.mask) (targetOf dead) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ dead.autos.toList, autoOK (targetOf dead) (x.map swapRows) = true)
    (prior0 : k > 0 → ∀ j < (levels (3*(k-1))).1, ImpossibleU (targetOf dead) (k-1) 0 (stateSetT levels (3*(k-1)) j).toFinset)
    (prior1 : k > 0 → ∀ j < (levels (3*(k-1)+1)).1, ImpossibleU (targetOf dead) (k-1) 1 (stateSetT levels (3*(k-1)+1) j).toFinset)
    (checked : nodeVerifiedU levels idx0 idx1 k tm i = true) :
    ImpossibleU (targetOf dead) k tm (stateSetT levels (3*k+tm) i).toFinset := by
  rw [stateSetT_eq]
  simp only [nodeVerifiedU, prelimU, contextOfU, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at checked
  have hN := checked.1.1
  have hT : targetOf dead ∉ (readNodeT levels (3*k+tm) i).2.2.map Prod.fst := checked.1.2
  by_cases h0 : k = 0
  · subst k
    intro k' t' hk' _ h
    have hk0 : k' = 0 := by omega
    subst k'
    generalize he : ((readNodeT levels (3*0+tm) i).2.2.map Prod.fst).toFinset = S at h
    have eqS : S = {_} := h (fun k _ S => k = 0 → S = {_}) (fun _ _ => rfl)
      (fun _ _ _ hn => False.elim (Nat.succ_ne_zero _ hn))
      (fun _ _ _ _ _ hn => False.elim (Nat.succ_ne_zero _ hn)) rfl
    exact hT (List.mem_toFinset.mp ((he.trans eqS).symm ▸ Finset.mem_singleton_self _))
  apply nodeU_sound (raw:=vars dead.mask) samples _ hN hT _ _ _ (Or.inr (by simpa only [h0,ite_false] using checked.2))
  · intro v hv
    apply decode_faithful _ _ _ _ _ (wires_faithful dead) v
    exact (selectLive_sub _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hp
    exact buildRule_sound dead cols h
  · intro tag xs hx
    have e : ((idx0 (3*k+tm) tag).bind (linkedSetT levels (3*(k-1)))) = some xs := by simpa using hx
    obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
    have h0' : 3*(k-1) = 3*(k-1)+0 := by omega
    rw [h0'] at h
    exact linkedSetU_sound levels (k-1) 0 names (by simpa [←h0'] using prior0 (by omega)) h
  · intro tag xs hx
    have e : ((idx1 (3*k+tm) tag).bind (linkedSetT levels (3*(k-1)+1))) = some xs := by simpa using hx
    obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
    exact linkedSetU_sound levels (k-1) 1 names (prior1 (by omega)) h

def blockU (levels : Nat → PackingT) (idx0 idx1 : Nat → Nat → Option (Nat × Nat)) (k tm start : Nat) : Nat → Bool
  | 0 => true
  | n + 1 => nodeVerifiedU levels idx0 idx1 k tm start && blockU levels idx0 idx1 k tm (start + 1) n

theorem blockU_at {levels idx0 idx1 k tm start n} (h : blockU levels idx0 idx1 k tm start n = true)
    (i : Nat) (lo : start ≤ i) (hi : i < start + n) : nodeVerifiedU levels idx0 idx1 k tm i = true := by
  induction n generalizing start with
  | zero => omega
  | succ n ih =>
    simp only [blockU,Bool.and_eq_true] at h
    by_cases eq : i = start
    · exact eq ▸ h.1
    · exact ih h.2 (by omega) (by omega)

theorem blockU_merge {levels idx0 idx1 k tm start a b}
    (ha : blockU levels idx0 idx1 k tm start a = true)
    (hb : blockU levels idx0 idx1 k tm (start + a) b = true) :
    blockU levels idx0 idx1 k tm start (a + b) = true := by
  induction a generalizing start with
  | zero => simpa [blockU] using hb
  | succ a ih =>
    simp only [blockU,Nat.succ_add,Bool.and_eq_true] at ha ⊢
    exact ⟨ha.1, ih ha.2 (by simpa [Nat.add_assoc,Nat.add_comm 1] using hb)⟩

theorem makeBlockU {levels idx0 idx1 k tm start n}
    (h : ∀ i, start ≤ i → i < start + n → nodeVerifiedU levels idx0 idx1 k tm i = true) :
    blockU levels idx0 idx1 k tm start n = true := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih =>
    simp only [blockU, Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega), ih (fun i lo hi => h i (by omega) (by omega))⟩

def checkAtU (c : NodeContextU) (i j op : Nat) (ka kb : Bool) : Bool :=
  let a := ctxWireU c i
  let b := ctxWireU c j
  evalMoveU c op a b (movedDecor op a b) ka kb

def combFieldU (c : NodeContextU) (d un ka kb : Bool) (op i j : Nat) : Bits :=
  let a := ctxWireU c i
  let b := ctxWireU c j
  restCov (getCov c.2.2.2.2.1 d) (column d a.2) (column d b.2) un ka kb |||
    column d (movedDecor op a b).2

def fallbackFastU (c : NodeContextU) (i j op : Nat) (ka kb : Bool) : Bool :=
  let (cap,tm,n,ws,_,pools,qpools,l0,l1) := c
  let a := ws.getD i defaultDecor
  let b := ws.getD j defaultDecor
  let un := op == 2
  let len := 1 + (n - (if ka then 0 else 1) - (if un || kb then 0 else 1))
  let ct := childU tm cap len
  let z1 := choiceVal (movedChoice op a b)
  if !properB z1 || ws.any (fun v => v.1 == z1) then true else
  if qpools.any (fun qp => fastCost qp (cap-1) a b op ka kb) then true else
    let rest := (opKeep un ka kb a b ws).map Prod.fst
    let links := if ct == 0 then l0 else l1
    closeChild pools links (cap-1) rest (movedChoice op a b)

theorem fallbackFastU_sound {c i j op ka kb}
    (hlen : ¬(1 + (c.2.2.1 - (if ka then 0 else 1) - (if (op == 2) || kb then 0 else 1)) > c.1))
    (h : fallbackFastU c i j op ka kb = true) :
    checkAtU c i j op ka kb = true := by
  rcases c with ⟨cap, tm, n, ws, cov, pools, qpools, l0, l1⟩
  dsimp only [checkAtU, evalMoveU, ctxWireU]
  dsimp only at hlen
  rw [if_neg hlen]
  dsimp only [fallbackFastU] at h
  have hz1 : (movedDecor op (ws.getD i defaultDecor) (ws.getD j defaultDecor)).1 =
      choiceVal (movedChoice op (ws.getD i defaultDecor) (ws.getD j defaultDecor)) :=
    moved_full op _ _
  set len := 1 + (n - (if ka then 0 else 1) - (if (op == 2) || kb then 0 else 1))
  set ct := childU tm cap len
  set d := ct == 0
  by_cases hcomb : ((restCov (getCov cov d) (column d (ws.getD i defaultDecor).2) (column d (ws.getD j defaultDecor).2) (op == 2) ka kb ||| column d (movedDecor op (ws.getD i defaultDecor) (ws.getD j defaultDecor)).2) != BitVec.allOnes 768) = true
  · simp only [hcomb, ite_true]
  · simp only [hcomb, ite_false, hz1]
    exact h

def makeBatchU (k n : Nat) (xs : List NodeContextU) : Batch :=
  (k, n, units xs.length,
    (List.range n).map (fun i => packedSig (fun c => (ctxWireU c i).2) xs),
    packedCov (fun c => c.2.2.2.2.1.1) xs,
    packedCov (fun c => c.2.2.2.2.1.2) xs)

theorem laneWireU_at (k n : Nat) (xs : List NodeContextU) {i : Nat} (h : i < n) :
    laneWire (makeBatchU k n xs) i = packedSig (fun c => (ctxWireU c i).2) xs := by
  simp [laneWire, makeBatchU, List.getD_eq_getElem?_getD, h]

def batchMoveU (b : Batch) (tm : Nat) (xs : List NodeContextU) (i j op : Nat) (ka kb : Bool) : Bool :=
  let (k, n, r, _, u, v) := b
  let un := op == 2
  let len := 1 + (n - (if ka then 0 else 1) - (if un || kb then 0 else 1))
  if len > k then true else
    let d := childU tm k len == 0
    let a := laneWire b i
    let b' := laneWire b j
    let z := packedOp (r * (BitVec.allOnes 768).toNat) op a b'
    let cov := if d then v else u
    let mask := fullMarks r (takePacked cov (packedColumn d a) (packedColumn d b') un ka kb ||| packedColumn d z)
    onMarks (fun c => fallbackFastU c i j op ka kb) mask xs

theorem batchMoveU_at (k tm n : Nat) (xs : List NodeContextU) {i j op : Nat} {ka kb}
    (hi : i < n) (hj : j < n) {q : Nat} (hq : q < xs.length)
    (budget : xs[q].1 = k) (ht : xs[q].2.1 = tm) (arity : xs[q].2.2.1 = n)
    (pass : batchMoveU (makeBatchU k n xs) tm xs i j op ka kb = true) :
    checkAtU xs[q] i j op ka kb = true := by
  let len := 1 + (n - (if ka then 0 else 1) - (if (op == 2) || kb then 0 else 1))
  let d := childU tm k len == 0
  have eval : checkAtU xs[q] i j op ka kb =
      if len > k then true else if combFieldU xs[q] d (op == 2) ka kb op i j != BitVec.allOnes 768 then true
      else fallbackFastU xs[q] i j op ka kb := by
    rcases hxq : xs[q] with ⟨cap, tmm, nn, ws, cov, pools, qpools, l0, l1⟩
    rw [hxq] at budget ht arity
    dsimp only at budget ht arity
    subst budget ht arity
    unfold checkAtU evalMoveU combFieldU fallbackFastU ctxWireU
    dsimp only [len, d]
    have hz1 : (movedDecor op (ws.getD i defaultDecor) (ws.getD j defaultDecor)).1 =
        choiceVal (movedChoice op (ws.getD i defaultDecor) (ws.getD j defaultDecor)) := moved_full op _ _
    rw [hz1]
  by_cases small : len > k
  · simp [eval, small]
  · let r := units xs.length
    let a := laneWire (makeBatchU k n xs) i
    let b := laneWire (makeBatchU k n xs) j
    let cov := if d then packedCov (fun c : NodeContextU => c.2.2.2.2.1.2) xs
               else packedCov (fun c : NodeContextU => c.2.2.2.2.1.1) xs
    change (if len > k then true else onMarks _ (fullMarks r
       (takePacked cov (packedColumn d a) (packedColumn d b) (op == 2) ka kb |||
        packedColumn d (packedOp (r * (BitVec.allOnes 768).toNat) op a b))) xs) = true at pass
    rw [if_neg small] at pass
    have chosen : cov = packedCov (fun c => getCov c.2.2.2.2.1 d) xs := by
      dsimp only [cov]; cases d <;> rfl
    have ca : a = _ := laneWireU_at k n xs hi
    have cb : b = _ := laneWireU_at k n xs hj
    dsimp only [r] at pass
    rw [ca, cb, packed_op, packed_column, packed_column, packed_column, chosen, takePacked_ok, lanes_or] at pass
    by_cases hit : combFieldU xs[q] d (op == 2) ka kb op i j = BitVec.allOnes 768
    · have hlenq : ¬(1 + (xs[q].2.2.1 - (if ka then 0 else 1) - (if (op == 2) || kb then 0 else 1)) > xs[q].1) := by
        rw [budget, arity]; exact small
      apply fallbackFastU_sound hlenq
      apply marked_ok _ _ _ q hq _ pass
      rw [mark_at _ _ _ hq]
      exact beq_iff_eq.mpr hit
    · rw [eval, if_neg small, if_pos (bne_iff_ne.mpr hit)]

def batchPairU (b : Batch) (tm : Nat) (xs : List NodeContextU) (i j op : Nat) : Bool :=
  let f := batchMoveU b tm xs i j op
  f false false && f true false && f false true && f true true

def batchRowU (b : Batch) (tm : Nat) (xs : List NodeContextU) (i : Nat) (js : List Nat) : Bool :=
  let unOk := if tm == 0 then true else
    batchMoveU b tm xs i i 2 false false && batchMoveU b tm xs i i 2 true true
  unOk && js.all (fun j => batchPairU b tm xs i j 0 && batchPairU b tm xs i j 1)

def batchRowsU (b : Batch) (tm : Nat) (xs : List NodeContextU) : List Nat → Bool
  | [] => true
  | i :: js => batchRowU b tm xs i js && batchRowsU b tm xs js

theorem batchRowsU_at (k tm n : Nat) (xs : List NodeContextU) {q : Nat} (hq : q < xs.length)
    (budget : xs[q].1 = k) (ht : xs[q].2.1 = tm) (arity : xs[q].2.2.1 = n) (js : List Nat)
    (bounds : ∀ j ∈ js, j < n) (allRows : batchRowsU (makeBatchU k n xs) tm xs js = true) :
    testAllU xs[q] (js.map (ctxWireU xs[q])) = true := by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [batchRowsU, Bool.and_eq_true, batchRowU, List.all_eq_true] at allRows
    simp only [List.map_cons, testAllU, testRowU, Bool.and_eq_true, List.all_eq_true, List.mem_map]
    have hi := bounds i List.mem_cons_self
    have check := @batchMoveU_at k tm n xs
    have hun : (if xs[q].2.1 == 0 then true else
        evalMoveU xs[q] 2 (ctxWireU xs[q] i) (ctxWireU xs[q] i) (movedDecor 2 (ctxWireU xs[q] i) (ctxWireU xs[q] i)) false false &&
        evalMoveU xs[q] 2 (ctxWireU xs[q] i) (ctxWireU xs[q] i) (movedDecor 2 (ctxWireU xs[q] i) (ctxWireU xs[q] i)) true true) = true := by
      rw [ht]
      cases htm : (tm == 0)
      · simp only [Bool.false_eq_true, ite_false, Bool.and_eq_true]
        have h1 := allRows.1.1
        simp only [htm, Bool.false_eq_true, ite_false, Bool.and_eq_true] at h1
        exact ⟨check hi hi hq budget ht arity h1.1, check hi hi hq budget ht arity h1.2⟩
      · simp
    refine ⟨⟨hun, ?_⟩, ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j, hj, rfl⟩
    have hj' := bounds j (List.mem_cons_of_mem _ hj)
    have both := allRows.1.2 j hj
    have opCheck (d : Bool) (pass : batchPairU (makeBatchU k n xs) tm xs i j (if d then 1 else 0) = true) :
        testPairU xs[q] (ctxWireU xs[q] i) (ctxWireU xs[q] j) d = true := by
      simp only [batchPairU, Bool.and_eq_true] at pass
      simp only [testPairU, Bool.and_eq_true]
      exact ⟨⟨⟨check hi hj' hq budget ht arity pass.1.1.1, check hi hj' hq budget ht arity pass.1.1.2⟩,
        check hi hj' hq budget ht arity pass.1.2⟩, check hi hj' hq budget ht arity pass.2⟩
    exact ⟨opCheck false both.1, opCheck true both.2⟩

def runBatchU (k tm n : Nat) (xs : List NodeContextU) : Bool :=
  batchRowsU (makeBatchU k n xs) tm xs (List.range n)

theorem runBatchU_at {k tm n} {xs : List NodeContextU} {q} (hq : q < xs.length)
    (hb : xs[q].1 = k) (ht : xs[q].2.1 = tm) (ha : xs[q].2.2.1 = n) (hn : xs[q].2.2.2.1.length = n)
    (pass : runBatchU k tm n xs = true) : testAllU xs[q] xs[q].2.2.2.1 = true := by
  have all := batchRowsU_at k tm n xs hq hb ht ha (List.range n) (fun _ => List.mem_range.mp) pass
  have eq : (List.range n).map (ctxWireU xs[q]) = xs[q].2.2.2.1 := by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2
      simp [ctxWireU, List.getD_eq_getElem?_getD, h2]
  rwa [eq] at all

def contextsU (levels : Nat → PackingT) (idx0 idx1 : Nat → Nat → Option (Nat × Nat)) (k tm start n : Nat) : List NodeContextU :=
  ((List.range n).map (start + ·)).map (contextOfU levels idx0 idx1 k tm)

def chunkCheckU (levels : Nat → PackingT) (idx0 idx1 : Nat → Nat → Option (Nat × Nat)) (k tm start n ar : Nat) : Bool :=
  let xs := contextsU levels idx0 idx1 k tm start n
  xs.all (fun c => c.2.2.1 == ar && prelimU (targetOf dead) c) &&
  let b := makeBatchU k ar xs
  (List.range ar).all (fun i => batchRowU b tm xs i (List.range' (i + 1) (ar - (i + 1))))

theorem chunkBlockU {levels idx0 idx1 k tm start n ar}
    (h : chunkCheckU levels idx0 idx1 k tm start n ar = true) :
    blockU levels idx0 idx1 k tm start n = true := by
  unfold chunkCheckU at h
  rw [Bool.and_eq_true] at h
  let xs := contextsU levels idx0 idx1 k tm start n
  have hrun : runBatchU k tm ar xs = true := by
    have go (lo num : Nat) (eq : lo + num = ar) :
        batchRowsU (makeBatchU k ar xs) tm xs (List.range' lo num) = true := by
      induction num generalizing lo with
      | zero => rfl
      | succ num ih =>
        simp only [List.range'_succ, batchRowsU, Bool.and_eq_true]
        refine ⟨?_, ih (lo + 1) (by omega)⟩
        have ok := List.all_eq_true.mp h.2 lo (List.mem_range.mpr (by omega))
        simpa only [show ar - (lo + 1) = num by omega] using ok
    unfold runBatchU; rw [List.range_eq_range']; exact go 0 ar (by omega)
  apply makeBlockU
  intro i lo hi
  have hm : contextOfU levels idx0 idx1 k tm i ∈ xs := by
    apply List.mem_map.mpr
    exact ⟨i, List.mem_map.mpr ⟨i - start, List.mem_range.mpr (by omega), by omega⟩, rfl⟩
  obtain ⟨q, hq, e⟩ := List.getElem_of_mem hm
  have one := List.all_eq_true.mp h.1 _ hm
  simp only [Bool.and_eq_true, beq_iff_eq] at one
  have hb : xs[q].1 = k := by rw [e]; rfl
  have ht : xs[q].2.1 = tm := by rw [e]; rfl
  have ha : xs[q].2.2.1 = ar := e ▸ one.1
  have hn : xs[q].2.2.2.1.length = ar := by rw [e]; exact one.1
  simp only [nodeVerifiedU, Bool.and_eq_true]
  refine ⟨one.2, ?_⟩
  split
  · rfl
  · exact e ▸ runBatchU_at hq hb ht ha hn hrun

def cellsU (levels : Nat → PackingT) (idx0 idx1 : Nat → Nat → Option (Nat × Nat)) (k tm start n ar : Nat) : Nat → Prop
  | 0 => chunkCheckU levels idx0 idx1 k tm start n ar = true
  | d + 1 => cellsU levels idx0 idx1 k tm start (n / 2) ar d ∧ cellsU levels idx0 idx1 k tm (start + n / 2) (n - n / 2) ar d

theorem kU {levels idx0 idx1 k tm start n ar}
    (h : chunkCheckU levels idx0 idx1 k tm start n ar = true) :
    cellsU levels idx0 idx1 k tm start n ar 0 := h

theorem cellsBlockU {levels idx0 idx1 k tm start n ar d}
    (h : cellsU levels idx0 idx1 k tm start n ar d) :
    blockU levels idx0 idx1 k tm start n = true := by
  induction d generalizing start n with
  | zero => exact chunkBlockU h
  | succ d ih =>
    have v := blockU_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v

theorem forestU_all (levels : Nat → PackingT) (idx0 idx1 : Nat → Nat → Option (Nat × Nat)) (top : Nat)
    (prior : Nat → Nat)
    (lo : ∀ m, Lower (vars m) (graphGoal m) (prior m))
    (valid : graphValid dead prior = true)
    (tabs : ∀ k ≤ top, ∀ tm ≤ 1, blockU levels idx0 idx1 k tm 0 (levels (3*k+tm)).1 = true) :
    ∀ k ≤ top, ∀ tm ≤ 1, ∀ i < (levels (3*k+tm)).1, ImpossibleU (targetOf dead) k tm (stateSetT levels (3*k+tm) i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at valid
  have pairs := chart_pairs valid.1.1.1 valid.1.1.2
  have cols : ∀ ci ∈ dead.cols.values, Slice (vars dead.mask) (targetOf dead) (subcube ci.1 ci.2.1) ci.2.2.2.2 :=
    fun ci hc => col_sound ci prior lo (valid.1.2 ci hc)
  have names := valid.2
  intro k
  induction k with
  | zero =>
    intro hk tm htm i hi
    have hb := tabs 0 hk tm htm
    exact nodeVerifiedU_sound levels idx0 idx1 0 tm i pairs cols names
      (fun h => False.elim (Nat.lt_irrefl 0 h))
      (fun h => False.elim (Nat.lt_irrefl 0 h))
      (blockU_at hb i (Nat.zero_le i) (by simpa using hi))
  | succ k ih =>
    intro hk tm htm i hi
    have hb := tabs (k + 1) hk tm htm
    exact nodeVerifiedU_sound levels idx0 idx1 (k + 1) tm i pairs cols names
      (fun _ j hj => ih (by omega) 0 (by decide) j hj)
      (fun _ j hj => ih (by omega) 1 (by decide) j hj)
      (blockU_at hb i (Nat.zero_le i) (by simpa using hi))
def f3366uL24F (i : Nat) : Nat := 0x9e404182837b81d8504b2549314c140df6075d412c9524c5305033d91d7506cc549314c140
def f3366uL24 : PackingT := (3,7,7,5,f3366uL24F)
def f3366uL27F (i : Nat) : Nat := 0xb0707c1c130d00b84070707c1c1078383e0e00688000027ba1002752104ea433a908013860800000090209c30670c19db04009e28403e11e4007c5bc508275210003041f0707c1c124706b6c1000060e0833041cc3041e0e0800000f841e0e0f838261ade28803e1078383e0e0801e0e0ee7b0e859ee578ce29815c76f5b36a59f5ed7159d434e5153c4e7374b92bca526c911b4630fc1afdbecf8bbee6b5cce32ec2b00bdad2aba8a99a428e22e892007d9d26b9a4601765b1624f934440ec2b88a2005c0e02e0900196f9c664abb605305023df3ad66370b8a60a05bec369b4605514c140abf86db24c0aa2982813f99d3b3182505305027f63a3662c4a0a60a07f4654cc7549414c1409edcebd98a9282982813eb9d6b3181505305037f2282e397098a60a06fe4505c52e1314c140dfc8a0d98c3a6298281bf9141721764c530503fb2282c3aec98a60a06fe4505c82d5314c140dfc8a0b845aa6298281fd914161d754c5305037f2282e3aca98a60a07fa450586595314c140ff48a0aecb2a62982817f88d26dd544c5305037f2282e296498a60a07ee450587609314c140fdc8c0aa8c126298281bf9141714824c5305037f2382aa10498a60a06fe4505c85c9314c140dfc8a0b90b126298281bf914171d624c530503fd2282bb2c498a60a07fa450565589314c140ffc0a0b04b126298281bf914171d524c530503fb228263aa498a60a06fe4505c6549314c140bde4ec164a9262982817dc9d72c9524c530503ff0282592a498a60a057f236d82549314c140ffc0a0b04a9262982813dd9d7b31524c5305037f2283662a498a60a07f645c587505314c1408f7ceb598dc242982811df9d7b31b548530503bf2262dc2a890a60a077c6551b854d214c1409bec6e330a9a4298281df19546dd5348530503be32a8db2a690a60a07df04c598589214c140ffc098aa8b124298281ff095454d6248530503fe22a8a9ae290a60a077c655153aed214c140fc74bb304c3ac498281bbd1c84c56260530503bf836498ac4c0a60a07ef060931589814c140fde0c1262a930298281fd49535c9525c530503f5c2c4c0b04b0a60a07f1c595715d9514c140a7dc6d368d92a298281fb61526058254530503be9366a92e4a8a60a07f58549715c9514c140fe70b12e2bb24298281fec1624c57648530503fd82c498aca90a60a047be758cba22114c140
def f3366uL27 : PackingT := (71,6,7,10,f3366uL27F)
def f3366uH0_27F (i : Nat) : Nat := 0x6080680006610
def f3366uH0_27 (h : Nat) : Option (Nat × Nat) := lookupWord 1 5 3 10 2 4 f3366uH0_27F h
def f3366uL28F (i : Nat) : Nat := 0xe07608402c30349e1af8a3c10f038f0c3e076084f0c3e076084f0c3e076084f0c3e076084f0c30386ac1c621cc312c35a0e910b618961a910b6187221b0d6839b0c4b0d683a442d862586b41d2216c31380010001c000800000000e000400000181daf55cff29c4efdb9ee5322ac25879974408de350ca3009c248881f8741a860158320a01e0500a0053e6369b46cd514c140bec8eb970a0a62982817f80d26dd414c530502f723b05928298a60a05f6475cb2505314c140bf48eb164a0a62982817f11d52c9414c530502fd23ac2928298a60a05fb0758c24c5214c140cf8ce2386da842982819f19cb55153085305039e3374aa2a610a60a076c66e15454c214c140ee8cdbaa8a984298281de19b655153085305026db1b8cc2a733260a06f86552cc54e664c140df48a0d9898ccc98281fc91414c677999305026f91b8cc2a711260a06fc2552cc54e224c140dfc0a0d9898c4498281fb81414c68888930503fa12a8a9cef11260a07f60505319de224c140ff04aa2a73344498281fe81414c666889305026fa1b8cc2a708a60a06fc4552cc54e114c140fd88aa2a74442298281fd115454e7784530503fc22a8a9ccd08a60a07fc05515388a114c140
def f3366uL28 : PackingT := (33,6,7,10,f3366uL28F)
def f3366uH0_28F (i : Nat) : Nat := 0x6080601806610
def f3366uH0_28 (h : Nat) : Option (Nat × Nat) := lookupWord 1 5 3 10 2 4 f3366uH0_28F h
def f3366uL30F (i : Nat) : Nat := (if i<2 then (if i<1 then 0xff9953506224c140ff99544c6224c140fee9625d9824c1409ff8cb6a1624c1409ff8cb69d624c1409ff9cb61d624c1409ff8cb61d624c140fcf97661d624c140fbe98261d624c140bfd9c32d5624c140def8b66dd814c1409ff8cb69d814c140ffd13161d814c1409ff8cb699814c140ddf9b75d9814c140ffd1315d9814c140def8b66d5814c140bfd9c32d5814c140ffd1312d5814c1409ff8cb695814c140def8b66c9814c140def8b62c9814c140ffd1315c9814c1409ff8cb589814c140bbf9c8589814c140dfe9b2589814c140fbe982589814c140fef161589814c140ffd131589814c1409ff8cb549814c140fbe982549814c140ff7151549814c140ffd131549814c140bef9c6aed814c140def8b6aed814c1409ff9cb5c8814c140ddf9b75c8814c140dfd9b35c8814c1409ff9cb548814c140ddf9b7548814c140df79b5548814c140dfd9b3548814c140dfe9b2548814c140bdf9c7619714c140fcf976595714c140ff7151595714c140dbf9b8609714c140bdf9c7609714c140f9f987609714c140bdf9c7589714c140def9b6589714c140fcf976589714c140ffe121589714c140df79b5549714c140ff5953549714c140fde972549714c140bff1c1549714c140ff7151549714c140ffb141605714c1409ff9cb61d614c140ddf9b761d614c140fee962609614c140fbf181609614c140ff5953549614c1409ff9cb5d9514c140dfd9b35d9514c140fdf1715d9514c140dfb9b46c9514c140fbf181609514c1409ff9cb209514c140bff1c1209514c140dfd9b35c9514c140ff69525c9514c140fdf1715c9514c140def9b6589514c140bf79c5589514c140fe7965589514c140dfd9b3589514c140ffb141605514c1409ff9cb608514c140dfe9b2608514c1409ff9cb208514c1409ff8cb6a1214c1409ff8cb69d214c1409ff9cb61d214c1409ff8cb61d214c140fdf17161d214c140ffd13161d214c1409ff8cb699214c1409ff9cb619214c140ffd131619214c1409ff9cb5d9214c140fee9625d9214c140fdf1715d9214c140ffd1315d9214c140bfd9c32d5214c140ffd1312d5214c1409ff8cb695214c1409ff9cb615214c1409ff8cb615214c140ffd131615214c1409ff9cb5d5214c140ffd1315d5214c1409ff9cb595214c140fee962595214c140ffd131595214c140ffd131589214c140ff5953549214c140ffd131549214c1409ff9cb605214c140ffb1415c5214c1409ff9cb545214c1409ff9cb614214c140cff9ba614214c140dbf9b8614214c140ddf9b7614214c140def9b6614214c140df79b5614214c140dfd9b3614214c1409ff8cb616224c1409ff8cb606224c1409ff8cb61e114c1409ff8cb616114c140ff5953616114c1409ff8cb54a114c140ff595354a114c1409ff8cba22114c1409ff8cb88a114c140 else 0xfdb9875d9414c140fdb9875d5414c140bfb9c7595414c140feb986595414c140feb976595414c140fbb987609414c140bfbacc609414c140bfb9c5209414c140bfb9c1209414c140bfb9c85c9414c140bfb9c8589414c140bfb9c7589414c140feb976589414c140feb965589414c140ffa982589414c140bfbacc589414c140bfb9c7549414c140fdb8c7549414c140bfb9c6549414c140ffa982549414c140bfbacc549414c140bfb9c8149414c140fbb982605414c140bfbacc605414c140bfb9c85c5414c140fdb9875c5414c140fdb9725c5414c140ff3952545414c140bfd9c72e1314c140bfd9c52e1314c140f7d99861d314c140bfdacc61d314c140bfd9c85d9314c140f7d9985d9314c140fdd9875d9314c140bfd9c82d5314c140bfd9c22d5314c140fdd9875d5314c140bfd9c7595314c140fed986595314c140fed976595314c140ff99b8551314c140ff99b7551314c140ff9987551314c140ff99b6551314c140ff9986551314c140ff9976551314c140ff99b5551314c140ff99546c9314c140bfd9c62c9314c140bfd9c52c9314c140f7d987649314c140f7d986649314c140f7d976649314c140fbd987609314c140ff9954609314c140bfd9c5209314c140ff9954209314c140bfd9c85c9314c140f7d9985c9314c140ff99545c9314c140bfd9c8589314c140f7d998589314c140bfd9c7589314c140fed976589314c140fed965589314c140ff9954589314c140ffc982589314c140bfdacc589314c140f7d998549314c140bfd9c7549314c140fdd8c7549314c140bfd9c6549314c140ff9954549314c140ffc8b2549314c140ffc982549314c140bfdacc549314c140f7d998605314c140ff9954605314c140ffd0b5605314c140fdd9875c5314c140ff9987505314c140ff9982505314c140ff9952505314c140def8c66e1214c1409ffacc6e1214c140d7f9986dd214c1409ffacc6dd214c140d7f9986d9214c1409ffacc6d9214c140d7f9986d5214c140ddf8c76d5214c1409ffacc6d5214c140dfb9b8551214c140dfb9b7551214c140dfb9b6551214c140dfb9b5551214c140dfd9b854d214c140f7d99854d214c140dfd9b754d214c140dfd9b654d214c140ff995454d214c140f7d953649214c140f7e998589214c140ffa954589214c140ffc953589214c140f7f1985c5214c140ffb1545c5214c140ffd1535c5214c140dfb9b8505214c140dfb9b7505214c140dfb9b5505214c140ff9953505214c140f7d9984c5214c140ff99544c5214c140ffd0c54c5214c1409ff9c8aed214c140d7f998aed214c1409ff9c7aed214c1409ff9c6aed214c1409ff9c5aed214c140dfb954aed214c140dfd953aed214c140dfb941aed214c140dbf9c56e0214c140df79c86d4214c140dfb9b8550214c140ff995454e224c140) else (if i<3 then 0xc17070861b8385c1c1e0e08c3707080753c1c21c5e0e17070671783aed87c1c1e0e1df1707078382001ae0e1000bb8384c01c1d78a301f080d7070861807c40e0e0f070461b8384305c1c2e0e98210106b8380b80349c1c11c2182e0e170707c603c1c1e0e1b608e1f070561b83840f180691707047081c1c1e0e0f0704002210f070406b8387146d8238bc1c1000d707080035c1c38a3582e0e10004c20bc508db04700f8f83a6184035c1c38a3e0e06912090348b8381a45c1c0d22e0e0691707034898381a45c1c0d2201f0800f070b8383a301e0e080fe8c0b8383c1c1d61ea9b52ba84d33e95b48ba34d0be81b3eb9d8ce3e6db34b994cc1e5cb2c3950c9fe48b20b8e8c65e2bb123880c37e17b09b83cc0fe00af9b7b0bcfde3aefb76cba7dccae43704b73db2ad43690b39d95ac5b610af9d72ab5b590abfd5baa8b528a8bd3ba98b4a8a3fd18a873410a05cfba78b3c09ddce7a71b3889c1cdca6db35c9a5ccea66b324989cc3a6132f8979cb8a58b2b4951ca4a503264929c90a463214907c7fa3c31dc8e5c6ea36b1a48c9c57a2b314889bc46a1fb0ec873c2fa14309083fc18a05b0047f3bf29f72fa87cbbe19ebaf40791bbe9dd2ed8757ba49d02e7c73bb969c7ae20701b7c9baadb86d3b5c9aaad2068db3f99dacdc665b2e9952c98643b1d98e2c5461bb0697e2bc85d5ae396fab6c5adacf9642b04579abb95baacc557aa194d2a64523a8794029f04e9a6a934a9704a9a4d924a908481a3c91c28d0459a25910a87442ba1490528003f19f18f5278c3b19d48e6a71837d9b78d826b034f9a08cfa66032198c8c125f82ed9728b725b42cb9648aea54c29d9478a024fc275936897a4a024191f889242c2078ff87da3dc1d98e8870a3801b18d1868233018f8c386123041798b8854229014589b84d2240111887841a2080fb87383621880b5853826211407b836817a0a004781c80c205001f80880220009ffacc6c4824c1409ffacc6e1624c140d7f9986dd624c1409ffacc6dd624c140f6f9985d9624c1409ff9c8aed624c140d7f998aed624c1409ff9c7aed624c1409ff9c5aed624c1409ff9c1aed624c140f6f8b6649814c140faf8b6609814c1409ff9c7aed814c140def9c6aed814c1409ff9c6aed814c1409ff9c5aed814c1409ff9c2aed814c140d7f992aed814c140ddf9c26dc814c140def8c66e1714c1409ffacc6e1714c140f5f99861d714c140f5f9985d9714c140d7f9b8649714c140f5f987649714c140f5f976649714c140f5f9985c9714c1409ffacc6e1614c140d7f9986dd614c1409ffacc6dd614c140d7f9b8649614c140d7f9b7649614c140f6f998589614c140fef0c6605514c140ffb1b4605514c140f7f192605514c1409ffacc6c8514c140d7f9b8648514c140bfbacc61d414c140bfb9c85d9414c140 else 0xe0e0f07034898383c1c198660e1707058383c1c101ae0e17070407c330403e2e0e0f07078383c1c1e0e0b07078383c1c1e0e0cc13070a609838541cb6c2582a0e12c15070a6098385c1c160e0f0706838341c198260e102180f898038380b8034935203e2e0e0d07078383c1c1e0e3dd11d4f070b8382753c1c23a9e0e11c37070805b8381a47c1c1e0e00d17071470b838a386087c1c3042386e0e11c37074c10cedb8385c1c07a2e0e0f0707838f146086753c1c2e0e0802f070348c60b8380347c1c01a2e0e3b600d18c17070860b8380346305c1c01a3000f98c8903819108460020721088f742001d484075213a90bdb040752121a08004341001e8407c094504218210c1084e18204a632201f098c84090281c84220012050390844038609c304076c103d0a075e2834a109000e413c50de28160af1407c40d2102075db2108eed80344842118208068c1080900146080348f8a30401a3e2001f1707034898383c1c160e0f070419d83a7147c35c1c2001e0e17072db2470f8383c1c1e0e5c502c181aadb088842000160d4888388845304c1c2982e0e14c106619838530dc1c29860f072db247006938380344035c1cb8a01a401071108803424421e0e0b07078383c1c1e0e0f07041c1c01a2e0e06917070348b83a8841a46835b0c352381a5a9120d4c10b8383c1c1e0e0f07047080078385c1c3ba2e0e0838383c1c1064bc517075110348c6db83840a1a01f130702180f8c07c8845c1c1a8e01f1510f074c10c0003c1c30436c4182e0e10db7070b838236dc1c2070707838203e1bc501f10db00f8b8383c1c1182e0e1038387141a460afc1c0d23e0e06915e28348b8381a44305c1c23a9582e0e1f070461b8384305c1c2e0e98610))
def f3366uL30 : PackingT := (296,5,7,13,f3366uL30F)
def f3366uH0_30F (i : Nat) : Nat := 0x11c023981c008e011d809382b008e011c0098040008e6004023d025a062011c023d83f703400180238047008e011c0238047008e011f8010047501142b6c1c903e008e011e0026845008e011c0238047405d20884038047702cc0a9c458047102e2090821080b5076c09a2c5083840236228414201e7a1c2087c02e83a704060dc0068803f014e0308163046c053e0f38183009b15e20000238047008ec0c940f9010c04620628168047f068011d00ed819b06640bd40dc036401d609c00a0047907ba110420b815b086011c0238047601e011c0238047008fc0d47020208306001c0000a101850e1048100100800258105
def f3366uH0_30 (h : Nat) : Option (Nat × Nat) := lookupWord 26 117 7 15 7 4 f3366uH0_30F h
def f3366uL31F (i : Nat) : Nat := (if i<2 then (if i<1 then 0xeed931aaa664c140f4f9929de664c140fcb9419de664c140fcd9319de664c140ecfaaa9de664c14097f8cb662224c140ff195454e224c140f7c95364a224c140ff495354a224c140f7c9924c6224c140ff91414c6224c140ffc131486224c140f6e99299a224c140bde9c72e2224c140b7e8cb662224c140bfc9c32d6224c140afe9ca216224c140bde9c7216224c140bee9c6216224c140bfc9c3216224c140bfe1c1216224c140f7c99854e224c140ff48b554e224c140ff498554e224c140ff895454e224c140bfcacc54e224c140bfc9c32c6224c140bde9c7206224c140bfc9c3206224c140bfc9c3146224c140ff8953506224c140f7c9984c6224c140bfc9c54c6224c140ff89544c6224c140ffc0b14c6224c140ffc1814c6224c140ff89414c6224c140bfcacc4c6224c140efc953aaa224c140efc931aaa224c140f3e998a22224c140fba941a22224c140fbc931a22224c140ebeaaaa22224c140f5e9989de224c140fda9549de224c140fdc9539de224c140fda9419de224c140fdc9319de224c140edeaaa9de224c140f6e99899a224c140fea95499a224c140fec95399a224c140fea94199a224c140fec93199a224c140eeeaaa99a224c140faea8899a224c140fcea7799a224c1409fd8cb54e114c140ff195454e114c140ff9153506114c140f7d1984c6114c140bfd1c54c6114c140ff91544c6114c140f7d1924c6114c140efd131aaa114c140fbb141a22114c140fbd131a22114c140fdb1419de114c140fdd1319de114c140ffa14188a114c140ffc13188a114c140bef1c62d6114c140bfd1c32d6114c140aff1ca216114c140bdf1c7216114c140bef1c6216114c140bfd1c3216114c140bfe1c2216114c140bfb0cb552114c140bfd0cb54e114c140f7d19854e114c140ff518554e114c140ff915454e114c140bfd2cc54e114c140f7d15364a114c140ff515354a114c140bef1c614a114c140bfd1c314a114c140efd153aaa114c140f3f198a22114c140fbb154a22114c140fbd153a22114c140f3f192a22114c140ebf2aaa22114c140f5f1989de114c140fdb1549de114c140fdd1539de114c140f5f1929de114c140edf2aa9de114c140f9f2889de114c140f6f19899a114c140feb15499a114c140fed15399a114c140f6f19299a114c140eef2aa99a114c140faf28899a114c140fcf27799a114c140ff3154956114c140ff5153956114c140f77192956114c140ef72aa956114c140fe7266956114c140f7e19288a114c140f7e19888a114c140ffa15488a114c140ffc15388a114c140efe2aa88a114c140fbe28888a114c140fde27788a114c140fee26688a114c140ff625588a114c140df9141aed314c140fe195454e664c140fe91414c6664c140ff095454e224c140ff81414c6224c140ff115454e114c140 else 0x9ef9c6aed814c1409dfacc6dc814c140d5f9b7648814c140d7d9b3648814c140afb8ca6d1514c140df99b46cd514c14097f8cb649514c1409fdacc6cc514c140d7d9b3648514c140beb9c6149414c140bf99c3149414c140bdd9c72e1314c140bfc8c26dd314c1409fdacc6d5314c140bbd9c82c9314c140bdd9c72c9314c140bed9c62c9314c140bf59c52c9314c140d7d9b5649314c1409fd8cb609314c140bfd1c1209314c1409fd9cb149314c140bed9c6149314c140bfd1c1149314c140fbd0b8605314c140f7d198605314c140fed0c6605314c140fbd186605314c140dfd1b5605314c140ff9154605314c140f7d192605314c140fbd182605314c140bfd2cc605314c140df99b5505314c140ff9181505314c140ff9171505314c140ff9151505314c140ff91b8505314c140ff90b8505314c140ff91b7505314c140ff9187505314c140ff91b6505314c140ff9186505314c140ff9176505314c140ff91b5505314c140ff90b5505314c140ff9175505314c140ff9165505314c140ff91b2505314c140ff90b2505314c140ff9182505314c140ff9082505314c140ff9172505314c140ff9162505314c140ff9152505314c140ff9052505314c140ff9141aed314c140d7d998aed314c1409fd9c5aed314c140df9954aed314c140d7d992aed314c140dfd181aed314c140df9941aed314c140ff195454d214c140ff91414c5214c140dfd1b84c5214c140f7d1984c5214c140ff91544c5214c140ffc0c24c5214c140f7d1924c5214c140ffc1624c5214c140bfd2cc4c5214c140dfd131aed214c1408ffacc6e8214c140d3f9c96e0214c1409bfacc6e0214c140c7f9ba660214c140d3f9b8660214c140d5f9986dc214c140d6f9986d8214c140d779986d4214c140df39c46d4214c140df59c36d4214c1409f7acc6d4214c140cfb9ba550214c140dbb9b8550214c140ddb9b7550214c140deb9b6550214c140df39b5550214c140d7d9986cc214c140df99546cc214c1409fdacc6cc214c1409fd9cb54c214c140cfd9ba54c214c140dbd9b854c214c140ddd9b754c214c140ded9b654c214c140df59b554c214c140ff195454c214c140adf9c7206aa4c140afd9c3206aa4c140afd9c3146aa4c140afd9c54c6aa4c140efd1814c6aa4c140afdacc4c6aa4c140efd131486aa4c140abf9c8086aa4c140adf9c7086aa4c140aef9c6086aa4c140af79c5086aa4c140afd9c3086aa4c140f6d99854e664c140fe598554e664c140fe995454e664c140bedacc54e664c140f6d95364a664c140fe595354a664c140bed9c314a664c1409ef8cb606664c140fe9953506664c140f6d9984c6664c140bed9c54c6664c140fe99544c6664c140f6d9924c6664c140fed1814c6664c140bedacc4c6664c140fed131486664c140eed953aaa664c140) else (if i<3 then 0x8c002cc1158380bbc60016608ac4500ac42058c4130d304706902e02cf1898698237070c10ac640ae881619608b63205d440b0cb045b1902ea205865822d8c8175102c32c11500688a8840b2882c65619609041c05c44200b3045a0e02502c80598698235070c1081a40b3c61619608a0d2057e30b0cb04506902ef18586582283481778c2c32c1141a40bbc61619608a0d205c058a33e30b0cb047069221dc8db8d86d8236000700038001c000e000608c38001c000e000700038001c000910e000b000380010107110e000f00038001e0e0e000483888700078001c000910e000b00020c0009118488c2c1c1e0e08004420d3e3002c403502261a41aa0eddfdc5db6221d86d825907110e000f0002443800200d02241aa0eddfdc5db6d86da92215600058383c1d30c25860b074c3088630005c1d8002e0ec0013076000b83b00044438002221586160007000201820f076000b0002c1d8002c000907110e000f00038001221182160007000202230911858383c1c10018383c1c10707040060e0f07041c1c10038383c1c102e01f582181a81130d5076efee2edb6c16c3110ab000241d8002c000e000700020e0e08383820e0e08383a60853041218c0017076000b83b0004c1d8002e0ec0017072c10960824438002c000e0004041c4438003c000f076000b0002446160e0f07040c1c10307078382060e0838382c1c1e0e08183820e0e0f07078382060e0838382c1c160e0f070400e0e0f07078383c1c142361a1111b0d0888d8684446c34222361a1111b0d0a3188bbe2d28a76268889e1ce860616484be0fa83760b481ce0628085fe07e7df5e7ca5edc7a9de727895dcc771dd7a7515d2873fdcd67285c78719dc326f35b8c6d5daf26ac5a6467cd99a656591862fd88a612582c5eed76e5d457045b0d68e58455d0566d572558555054cd5225445494508d3e24e853844dfd34a4c853104bfd2ee4ab5290493d20e473518c452d0f24295088411d0063f14f843c7cede3a44e7438ccdf236c4d7034bccd63224c78319cc563114c34308cc123004bf02f7cbce2ef4ba02e3cb7e2de4b502cfcb2e2c74b0c2b8cad22b04aa42a4ca8e29f4a6c296ca4a28e4a3428bc9fa25c494824dc91a227488c21ec85e2134830204c7f61f647bc1e7c7821d947541d0c73e1cb47101bfc6e21b446a81a5c68619a4658191c64218c4620183c5fe17e45f4178c5d217345bc16dc5b21684590162c57a15d4570157c54e14944a8125c47a11a4458111c44210c442c106c41610144000f8c3d20ed43980dec35e0d043240c4c2f60b942d40b3c2a60a54278099c256091423408bc21e086420807dc1f207841dc072c1ba06a41a4064c18e05f416c056c156051414004bc11e04340fc03dc0f203840d002fc0ae0244074015c03a00740009fd9c3aed824c140 else 0x34f8c00980f90193c6007c7c1c3042a0e02ef185822017002910ac11011286a88015c0b8a445400c0141c44205801a7064f1802d01622101f35070c108838014885608875384784001a400d42310128120348c1a6f1407fc60034be30102501ff1800d386281280ff8c0069c31409407fc60034e18a04a03fe3001a70c540082101f00d203908c81284701203498f7c07fc60e18805c75203e01a402e3a901ff1800d386300f81700698cf8c1d49c31c081c0d205de308420c86c220647b601f23db78c081a41b407c60da846842301ff18421016200ff8c00b0c608303981d04201a402201cc0e8217c51b87a900d402bc108dc017006948680b86e0034843581cfbf042f8af6cf5201a83197f40690160242d0d034bdb3d4be28069809008b0381a5ed9ea5e1a085f15243581cfbf042f8af5201a700d005c0e8217f42806802e07410bee9486b039f7e085f15ed8034efaa08802c048400d005c0e8217d5280682209800057039f7e085f15ed9ea403520380d3042f9007af0c63190691002e07410be401ebc31801703a084035f20a00b81d04207a4024005022c0e7df8217c57b600d0165034c10be401ebc314045084090034881c84330430240cc10508660843041182081601a91181130d5076efee2edb110a807008a83b77c8877176a46e0035211c0c803fe30026520e064f18221013291191088041de30442026401f7b6f1818c1046082002160e02ef180059822f070c1080440afc60005608b41c05de3000ab04560e02ef180059822b070177))
def f3366uL31 : PackingT := (257,5,7,14,f3366uL31F)
def f3366uH0_31F (i : Nat) : Nat := 0xa06da034023fc09207c011c0238047e04bc0c4021e8c4a00fe0bc81c8047c1309628023882b008e80540238047c07641094093046008e011c023f801d06a2258023f021008e40900238047008e011c0141044b12520640006085940880f08081823e065c076805c82a4019821c0238047804e222a01ef016917e80e8a870047c070a30284f1830112aa0a741170144005a0700238047008e011d448e0181067c07c81b981330404046016c8c25068011f8070047008fe0ba8167826002801c0000182060000600104892014085100c100
def f3366uH0_31 (h : Nat) : Option (Nat × Nat) := lookupWord 24 100 7 15 7 4 f3366uH0_31F h
def f3366uH1_31F (i : Nat) : Nat := 0xb038021207a414400fc1c0084021206002100840210084021e120021008740d00840212109049008705000840210084021008680f008402100840213110021a07e81bb04c0210084021206b41251308196014021008402100840210084021503002100440210085c000087c170084c0900840210084021008440790200210086c200084021701802100840210084021105b804c1280210085c1d0084021010c80ac00a01000840210084021a00600bc0540216138021008402100840210084500000010000044000000000
def f3366uH1_31 (h : Nat) : Option (Nat × Nat) := lookupWord 14 109 7 14 6 4 f3366uH1_31F h
def f3366uL33F (i : Nat) : Nat := (if i<1 then 0xac1c1a4661821c1ac1c6d8a61a0d1df76c07ca618dc41ac1c6d8a6181721a8346a51081f398202d839108692982c1c7168c48e2982c1d462471034805c1c77e8c28e91c730c0170751891c5304723071c5a31238c60b073c53534624718c121ac1d4624714c1016c1d46247164f525f91747f63af1b18cb45c22ab12f88fc3ba1910ad843c15a03500a7f23ea1ed8f3077a3ae1cf8e3570d37a5b86da86c13571a6cd0565f32618e4c2b5fd2f51772b935b6ad1d642af056aab15554a8453a28e143a9f74e326ad32095f4a224791da8c744021110267d73cd9d7ce5c7133769b1cd5869c33b196cc9663030a97e8ba85b92c415e0aba53727d932894847e23190f482e3e61e00e686d23431838b2c51e23d100871432814208302fc0f003c0007ff97668930503ffcdb30498281ffe5d9824c140fff362c1260a07ff9a85c930503ffcd32e498281ffe619724c140fff374b1260a07ff9b858930503ffcd42c498281ffe6dd624c140fff34eb1260a07ff98758930503ffcdaac498281ffe2d5624c140fff344b1260a07ff98258930503ffcd8ac498281ffeaed624c140fff30ed0a60a07ff98668530503ffcbb34298281ffe5c9a14c140fff2c4d0a60a07ff9ba60530503ffcd430298281ffe6dd814c140fff34ec0a60a07ff98760530503ffcdb30298281ffe699814c140fff2ecc0a60a07ff9b560530503ffc5ab0298281ffe695814c140fff364c0a60a07ff8b260530503ffcd130298281ffe609814c140fff2e4c0a60a07ff96260530503ffca930298281ffe685814c140fff576c0a60a07ff97220530503ffca910298281ffe6e1714c140fff36cb8a60a07ff9865c530503ffcb2ae298281ffe6c9714c140fff304b8a60a07ff9625c530503ffca92e298281ffe605714c140fff30eb0a60a07ff97558530503ffcc12c298281ffe5c9614c140fff2a4b0a60a07ff97654530503ffcd92a298281ffe609514c140fff104a8a60a07ff97254530503ffcb12a298281ffe605514c140fff30428a60a07ff88214530503ffcdd24298281ffe6e1214c140fff17090a60a07ff9a848530503ffcdba4298281ffe69d214c140fff30e90a60a07ff9b648530503ffcd324298281ffe619214c140fff2ec90a60a07ff9b548530503ffc5aa4298281ffe695214c140fff30a90a60a07ff97548530503ffcb2a4298281ffe689214c140fff30490a60a07ff96248530503ffca924298281ffe685214c140fff30290a60a07ff97148530503ffca8a4298281ffeaed214c140fff30a10a60a07ff98688930503ffcc2c4498281ffe596224c140fff30311260a07ff96188930503ffca8c4498281ffe146224c140fff30f08a60a07ff98584530503ffcc142298281ffe20a114c140fff2e508a60a07ff95284530503ffd4442298281ffe88a114c140 else 0x413e0ea304027880477610e0e91c4026edb100692001391c606004e471819c8c1c2c1cc60dc0f0728e100136dc60783820070731830c4c1c714db0f073c5160e30c88460041160e6304b6c77cdb28e0265c1c1c1c618db0c00824c1d462119400824c1d462119400824c1d462119400824c1d462119412001c1d4621195113b6076c600f9411005b6dc60c106933b603e2c1d6d98c069206478b6d86ed80f88db7180d233bb838db0d0d3b603e3c1c10d109df260e3bf6d98c2230d2676ca380f8d1098203e304f83adb3183041a4c192db28e0d2439183adb0f071b6160e78b6d876d911e1a19823be07c660b074211e0e78b0843493073b6160e0857c1c2c1c110db0f07042ba21c1ca38c3142be0e1057c1c7147714e2bb603e437183846e30708dc221c1ca3886e30708dc60e78a305d06b07421261a78a07c68860d60e842a383498c32218350840f941741ac1d08480ba0d60e842608b068173b684207ca0170742151c1a4a017074210d2463007c4ed94701f1a21c1c1a47c6034880f87073180d23c1c714407c3c603488fa60e11ddc1c2434f140f8f07221160e63088c34930704eae0e1043c1c6d878398c0053041a4a04f0728e0d2476c608098cc160e78a34478684619db01f1bc530c07c66190d22103e43046180f8f074210d2330c7d20d60e241)
def f3366uL33 : PackingT := (111,4,7,13,f3366uL33F)
def f3366uH0_33F (i : Nat) : Nat := 0x128e03668064007801280094004a0025001280094004a0025001280094004a0025001280094301ac025001280094004a3c00c0128009470128c04c01280094004a0025001280094004a002500128403d8817c02506065a01ea01bcc08801289030004a080860128002f2007a006001283007480b402500128009400108025001280094500a7405d40166027804a1008a01289028004a00250012800941016e800180151037500cc025001280094080e6007001280094004a00251202f0094004a002500128f02b004a002500128009428094025020210029004a0c0e3e23d403520145c0140128a039804a00251202a0094380d4025001280094004a0808001280094004a2c04f423b0094004a00250401f0094004a000f201280094004a2c0ec01280094004a002506032801dc005380400128401a5818802500128c0348000e001e01280094004a140e5c0610094004a0025001280094004a002500128009430043c003003e6005d001c0250a002211cb0125c048204d2029804a3004420595018804a002500128e01b804a380240128300bb804c0250804c0094004a00251206d0094004a1001201280094004a00250601a009460074c08ee063602a804a380e80128910d901d740af8210a02d700168023604b0094004a0025140230094409f500f1a046a016004a00251807000943013802500018d03d004a1c0cc01280094580d9800801280094004a002500128802c301510038a0680094004a002500128009420106045f001b00140812000c9207c0094004a1c0eea05c201fb01f5c019005de0069897dc0ce0008001d400ac025001280094004a0025000008080808010040000048000c01008180000000000200000080c000180004010101000000100016000000c00000000c0000
def f3366uH0_33 (h : Nat) : Option (Nat × Nat) := lookupWord 45 284 9 17 9 4 f3366uH0_33F h
def f3366uL34F (i : Nat) : Nat := (if i<2 then (if i<1 then 0x8530502ffcdc04298281dfe660214c140bff36a10a60a07fb95408530503feca984298281bfe5daaa4c140dff30555260a06ff882aa9305037fcb955498281bfe58aaa4c140dff30355260a06ff881aa9305037fcb8d5498281bfe586aa4c140dff2a355260a06ff851aa9305037fc90d5498281bfe086aa4c140fdf35133260a07ef9a799930503f7cc3ccc98281fbe696664c140fdf30b33260a07ef97599930503f7cd14cc98281fbe60a664c140fdf2e533260a07ef95299930503f7c294cc98281fbe686664c140fdf30333260a07ef97199930503f7ca8ccc98281fbe486664c140eff33111260a07fb95488930503feca9c4498281ffa68a224c140ffd30511260a07fe96288930503ff4a944498281fee506224c140ffb26311260a07fe921889305037fd5544498281fbe99a224c140ffd17111260a07fe9a888930503ff4d3c4498281ffa61e224c140ffd34d11260a07fe98688930503ff4bb44498281ffa2d6224c140ffd34b11260a07fe98588930503ff442c4498281ffa5d6224c140ffd2cb11260a07fe8b188930503ff4d0c4498281ffa606224c140ffd10311260a07fe97188930503ff4b0c4498281ffa546224c140ffd0a311260a07fea8888930503bfccc42298281fee552114c140ffb2a708a60a077f99284530503ff8d0c2298281ffc606114c140ffe2e308a60a07ff15184530503ff890c2298281bfeaaa114c140f7f51108a60a07dfa7784530503ff51142298281ffc2e2114c140ffe35108a60a07ff1a784530503ff8c3c2298281ffc69a114c140ffe30d08a60a07ff17684530503ff85ac2298281ffc696114c140ffe30b08a60a07ff08584530503ff8bac2298281ffc596114c140ffe16508a60a07ff1a284530503ff8c142298281ffc20a114c140ffe2e508a60a07ff16284530503ff8a942298281ffc14a114c140ffe51108a60a07ff25584530503ff9114229828177e6dc814c140bfb36640a60a05fd9b314530503beccc262982817f66d5314c140ff32a898a60a077d9924c530503fe8c0a6298281fe6505314c140bfb57698a60a07fd131485305027fcdd042982816fe6e0214c140bbf36e10a60a05ef9b608530502fbcda842982817f66cc214c140dfb26355260a076f99899930503f5caa4cc98281fb654e664c140edf32533260a07eb94199930503f6c98ccc98281bbeaaa664c140f9f4ef33260a077e99288930503bf4cc44498281fea552224c140ff92a711260a07fa94188930503fe498c4498281bfaaaa224c140f7d51111260a07dea7788930503f753344498281fec506114c140ffa26308a60a077f19884530503fd8aa42298281ff454e114c140efe32508a60a06ff2aa84530503df94442298281f7c9de114c140fde4cd08a60a07f725584530503ff11142298281fe4505314c140 else 0x29cc409850303e6010bf497b82f3a5d2cb6c16702c945864aff15d82aca53c8a6b94b129165194a25142428124fb89e993b827244d849a3131525f44b7c95c928824c448f0910920623aa46bc8c49121217241447f48fc31f3a3e087a88f361e203b7c7570e7d1cae38f070b0dfb1bc037146d50d841aa634e06838cec19a232ac6428c54185c304c5fc0bd217582e185aa8b2f15a4297c50689791222224c3ff878c0e321ba033a86180b76157828084a4088e10841fd83d5075e0e501b1833d06440c1c17082c6054009e812a022e042607e00ee81c20322055409d011401dc034c05c009d0104019c026003100017feaeda64c140bff374bb260a06ff9a768930502ffd5db4498281dfe5d9924c140bff374c1260a077f9b960930503bfcc9304982817feaed824c140bff37441260a05ff9b120930502ffcdd2e498281dfe661724c140bff374b1260a05ff9b858930503bfccc2c4982817fe6dd624c140fdf2ecb1260a077f99258930503ff4c12c4982817feaed624c140dff34cd0a60a06ff9a268530502ffd5db42982817fe6e9814c140eff330c0a60a07ef8b660530503dfcc330298281dfe649814c140f7f304c0a60a05ffabb60530502ffcdd102982817fe6dc814c140bff36a40a60a05ff9b220530503bfcc9102982817fe6e9714c140bff370b8a60a077f9985c530503efcc3ae298281f7e5d9714c140eff324b8a60a07df9725c530502ffd5dae2982817fe6e9614c140bff370b0a60a077f99858530502ffcdbac298281dfe649614c140fdf2c4b0a60a07ff18158530502ffcdd2a2982817fe6d9514c140ff7368a8a60a07fd9b354530503bfcc92a298281ffc605514c140ffe2e2a8a60a05ffabb54530502ffcdd0a2982817fe6c8514c140eff32428a60a07fb98750530503fdcc328298281fee5d9414c140ff72eaa0a60a07fb96550530503fdcc128298281fee209414c140ff72e4a0a60a07fb96250530503fdca928298281fee149414c140ff7302a0a60a07fb97150530503fdca8a8298281ff66e1314c140ffb17098a60a07fd9a84c530503fecdba6298281ff669d314c140ffb30e98a60a07fd9b64c530503fecd326298281ff6619314c140ffb2ec98a60a07fd9b54c530503fec5aa6298281ff6695314c140ffb2ea98a60a07fd9654c530503fecd926298281ff62c9314c140ffb34498a60a07fd9824c530503fec4126298281ff65c9314c140ffb2c498a60a07fd9524c530503fec2926298281ff6605314c140ffb2e298a60a07fd9514c530503fed5da62982817fe6e9214c140bff37090a60a077f99848530502ffcdba42982817fe6d9214c140bff36a90a60a07fb95448530503feca9a4298281dfe649214c140ffd2c490a60a07ff17148530503fdca0a4298281ff64c5214c140bff57690a60a05ff9ba) else (if i<3 then 0xb5360910869381ac1d77ee2db635288d10d86b04a835716db1a90d3c600fd86b049c1cc62000d10e0e51d000983a000b073c5800303577ee2db6b53618c1223440035506834dc5b6d6a4c101fe30036c32b07400141a446800706b072001a21c1c6187c62000b073188003c1d0005c62000b07400160e8002c1c884c30f07318447000983a0008c360e443000983a000b07400160e44260878398c2238004c1ceda000f072218003c1d000583a00090d60e443000983910c001a1ac1d0006838efdc5b6d4601758644360920cb075dfb8b6d81758644360920d70d5dfb8b6db8c58605d609283aefdc5b6d4601718644360938398c4001e0e76d000783a00090d60e443000983a000a8c2234003c1d46247200260ea3123900130751891c8008887071821f188002c1cc62000f0740017188002c1d000583a000b072213043c1cc6111c00260e800230583910c00260e8002c1d0004887071821e0e63100068870728e800444383a000f07400160e8002c1cf16000f07221800343583a000f0731851d000886b074001857c3477cdc02ec401a4c1202b868c3477fe29b805dc6034982561a3aa6e0d4f180d2608e044073f408815edc023f8bed8177180d3609a1cb0d069f8bed9d4f1803f60921102bdb805c09411a1af8bed9d4d8258110ae1100f8160461a7e2fb605dc61c3582688e7e81a61161a7bff17db71803ea04815c26823435f14dc02e01a60940461161a840411c88ae401fc341a7e2fb6e316195868349c83700af1018630480d3868e41b805d880c318241c8c341a4dc02ec40618c120dc61a0d27201762030c60900bb0d0693906e3101863048c341a4e41b805dc60c31824023c35c60688cfa6201a23434880688b0d7181a23c402446869101b8261ae306e0688f0d0b0d6201223391880688f100911a1a440344586b8c0d11a1a440344586b8c0d11e1a161ac402c35880586b100911a1a37088080891061a371c60a88f100911a1a440344586b8c0d11e201223c342c35880586b100b0d620161ac402c35880408d0d7c5f6c485170912109c1b682df04a206b40798022ff29fb6bf267dbefa35f0d3db27a7ef439e4dbc5f7796ee11d9ebaeb7532e8c5cea39b9728ce429c35b8246fbade2dba236dc6d14d831aedb5946adcd4f5a8634af68bacf519cc331a65bccab593e321f63dcc6718b5b1196178c259811afdc5ebcbbad74cae685c6eb8196f02d995aa4b48566d2c935882afbd5df2b775660aba55462a4553e6a5d549ca8e75156a1bd41427d64ef29d2139126db4cd098012ed25724a5692e1217a3c747008d3d17ea2cc44f4881d0cfa12141308010fd91f343d827a98f401e2e3bb874f4e759c8e384c6f50dbb9b1a36146b90d649ab935526a38d399a6334a668b4d091a0233b86704ccd9980329e64d0c8c98f331846 else (if i<4 then 0x31838dc1820d2641c14adc11902c0bb8c013b0493be6d815f1830c014009c08001034190db1a9c4023b8c18603eb0c98838c05721823beea710718b0c6753c60dc0d077180ae14898838c01f39043be6d84771830c15c0f98241df38a0af8c18600a004e0400081a0c8714d4e2011dc60c31b803ec41c111109f4b7050200040d1df3538804771830c6e00faf10044e3005adc171071802c6e087d2db620e3043be714db02be3061802801401ac41c60221110a1a0880351005705c7c341101601f20442338838c0160ae0b8e77cd4e1a05c1bf10072e308353c602b8c8c9df38a6d84771830c0b80f9825024353c60c318200260200040d1dfc4023b8c0133aa6e0c12d070010a56e08c816b53c6009d8253b6752e19e2982847080f08e101b87e84847080dc3dd251984015dea928cc20088378aed9d4982847080cf21fa423840035c31a11c2009af208f7de2ba9847080dc19efbc576c60a11c2033c80880ba11c2001ae18ef15d4b868466e21018239b801b0802b900d1b801a15e1002e321a0d2f15db3a903e67e80841288e0d2090cf15db3a96306081186900a8c341a5db3a978a07cced9d4b1830408c3480538240450000286976cea5e281f305c61686834bc575207caf15d4f1830408c34805381f00bc60dc3f4281f00bc60dc3dd2a1a0d3f17db3a903e67aa111d482104a058121e073c576cc60c10230d2015007f8c0577aa403fc60220c0a86978aed9d481f301c0d2f201082511c07f8c00d70ca81cf15db3a96306081186900a904207c348c02c00042f21fa01fe30035c3260000503fc6026bc83024044015efbc503eea40b718370a04808a000057bef15db07202c6080ff18606979011010ba903fc6006b86482278a6e1d481f304637015cc101f24204346e01082e30407ce0441288e03e43be714db02be30014009c08001034190e29b635204f1001f5001044190efdc5b6d6a510e204810002068ef9b63538804771802607d60400081a3be714d4e2011dc60099b803ec0020430d01a3be714db62011c1cb8c01303edbbf716db1a9446885101c1a82b04586a8cdc5b6c1c8d4f1803eb41c08aefdb6b528878c1c802c04d5880dc0b107183903bbf716d49b8446880c11c115dfb8b6a4dc01f30470200040d1df38a6d8d4e2011dc600998603e609c0911102be30618c10013919c31838029c837060834a0325c8b704671002ee30016c124e41b82338838c18605c7233722dc31905c882c358245c8b701a41082ee3161ac122000510a8e8003443000500030002eda000910c0014000c000a1a4430006886000a0004112218003e3100058398c4001e0e8002c1cc6111c00260e8002c1d00058398c4001a21c1ca3a001307400160e78b00066db072218004c1cc6111c00260e8002c1d000486b072218004c1d000483ae2db6 else 0x8c0af8c4230741a40280141df057c60c3005002678a0af8c005202723207815f1802001400a000c0ee3072210bdd31c536c0af8c00500260a488710069e30058099d071c844323834f1802c04d006b0c60e38a6d8d49820d2619209c15f1830c0140098080010346a4e41f4c4007d077cdb02be300140099070010c9c6110dc831df38a0af8c18200a004e0400081a0c8714d4e20e3004cc12907001045716d4f183e960910a40800103477cd4e2011dc600998251ddc41c60e41107022bbf6d8e45a9443c600b01350133e96db107182810002068ef9c53538804771836c04cc1186681c6314601582300a6038c628c02b046014d8380202b04908c0280139c536c0af8c18600a004e838115c5e31618fa06f442191388b0d064f8a10cdc62003e8c406e04004115c5b6d6a4c30164438800fa8c318202d8800f9408001034190e29b63538804771830c77c0f9827024057c60c318200263be6e3107180aef14c6a42b9b82338838c02e3919c)))
def f3366uL34 : PackingT := (273,4,7,15,f3366uL34F)
def f3366uH0_34F (i : Nat) : Nat := (if i<1 then 0x55a83800250012800944834002500128e028d019c02500128f10b88b5c025001281162804a0c21080b20094383ac025000a19085804a00250e0df0094004a002510123d052004a0025001280094182e00250012800941047c043160040094004a002500128009470075802c40c4009440024025001288101004a0025001280094004a0025100e3c088220dfc0c9e0416064804a2454a006300946846080560128009400ae40251a2c38001004a002500128a03b804a0449001280094004a0025001280094180db804a01280094004a301fc60f33b240826402500128e14a004a002500128907b3827402500128009428160025120b50094699280250e2384066004a002500128a170602c7004842a0117e804a3016740e1f092804a005fe01280094004a2824ea02fd073804a180a80128a14f804a0025001280094004a1c10401280094004a1453a012800945030c025001280094004a0025162990094004a280d4210dc188804a002500128303ed88cc025142ed0094004a0811e01280094004a0025060485045004a04118012800942813c0251c0190094004a0025001280094402e802500128300c282ba81e9c035805f98a4fc106607e606e004a00251e09a106d703168492e2b400944041941a60128512a004a00251a23c009430409812a0128b232104718534c103511a804a1008ee29bc072903500250610f7180004a002500128d07df03b002512112602c804a2c0b800840094282240251c0aa0094004a002500128305630329c14f80de008aa8aeb4236628f009450c48411722fc009400c3c025001280094004a0025001287054004a0023a70649007e82198456012800942824802500128807c004a002502011b04b004a0025001280094002d802500128e036c8b2c025001283030004a3407a0128601f804a00251e0c04073004a00250a2c7a159d82048144e04c0094004a2c23201280094004a381280128009468141801801280094004a002500128009428175856c0128b079004a0025001280094004a1416022f2f04e1035cc1684240009410118025001280094004a00250012860534841c048940c100943833bc140a10e4068804a105a40128703d004a0025001280094004a14035e043b088b831802500128e03c004a0025001280094004a002511041009470bb8025122710094004a00251a0c700946819ac15a0128000020000000004004000000100802000030000201400000000000200011000000000200800014000080000c000000000401000000040100003004050000800400000010180300803018000000000003000000000100000004000000000001024040080000c01000060140000000000020000100001000010000000c0201005004000040000005000000000001400004020140100000014030040502003 else 0x4a0025001289086004a24097a0380094004a3c1e201280094004a2015e01280094601fc0251e10a0094004a00251a04e1b1b804a002500128a127804a144346109009458c8c025001288064004a0025001280094004a2010fe0bef067a83d705f562bda121f8b66410001284022804a1022fc2dd0094004a00250025000940014c05fd80280094004a0417a01280094004a0025001280094004a085ec01280094004a002500128217df0294025061210094004a00250a2329140004a00250012800946806c02500128815b804a0804601280094004a00250403b009440c2f05bc0128c07fc8ac4803e60750094004a10178006f3021004a1c06001280094004a341114013613fe03f00250e2a20094004a0025001280094004a0025001280094004a002500128f184804a1419601281177c910402510069009448240025143100082703c0025000cd9038d030945be0128108a004a101b60128e007004a0025001280094004a00250e03a0094483f402500128b014d8a5c025001280094004a00251a2d1c0753027c025001280094004a080c36301716c004a0058c012800947809b804201280094004a00072012800943086e85c36085a077804a1c0b401280094004a00598a0ed009470918025020dd0094004a00250e03ec01e004a002500073101898478025023250094004a041b001280094004a3053c01280094004a0c02822a1b074802780250008e0094004a0c0178093b0911834885900128902208851013001280094004a2c0d6e0e4802bf0b90c177a05200945828c02500128f15f004a381b3a1160094004a114cf011a817600404025162d44102004a00251c05fd04d804a0052c01280094004a0025001280094004a00251801500940815402500128009420414820001280094004a34044a251c15c402a7446e60d6e077782e440140128c093004a00250a0320094004a0025001280094303e6816e01280094004a002500128206a804a00250012850925005fd0900128614e50c1402500128907bf03a340ac01285026c023604940128107d20480025180970094004a080e1e05b4032804a0c5f201280094004a0025143025089d8b26401a01280094004a002500128009418244025162ebd0712d19d85f00128f16d208d1c5d40128e)
def f3366uH0_34 (h : Nat) : Option (Nat × Nat) := lookupWord 126 799 10 17 9 4 f3366uH0_34F h
def f3366uH1_34F (i : Nat) : Nat := (if i<1 then 0xd30268e1270040402020101507bd834301c5420f1028b81c80202010160148887040d20101500d48967c0cb203731280020d847620910080f83d0804d82260080e00d284dd60036052e88d3049f225770746011884da0101701660897c474a233d015c8b88020201010080804040084010100208040784c3a016c03400404020201011121804040202a09b703f2016a817e0101200cb813c0203c0ae306f0040401ac01010080f81a9415942f5b068d8060020201018007188c40203003e901d804040203e0c3704480405404a4251214800404020302110080e81038110a21e00808040502000228313cb8166c0ef404dc123d880802020101f10ab83940203c200013be01d3c008206e0080c0bab406b60eb0080988a74042010100808040400204066c0338040540c00101e066103b341e66036e0600040540be01012012101200202a01300640040402020101a136600bec0460101b00478ba34464c2f7e009381334176e0ba008090a3740b0010120790040401da010110678040780a0004b600a804040202e25600808040402034057600e901740203a2229007e810c81bb40d900809017b81340101008080404444e0101405b08b02c11801014038603540203821f912900405c1ce406f202a409f8018c203c3045701d5444260f9705c20849c167c00071164803481af20e40080b83bbc17d00c7806ff8a74c519e0ce602488190c50c8267a147d08f40203209d008080404401500dc003db834804aaa27d600678007015e623c0018004040202805c804b8040402022084006480406440c01010080e03f402020101008080407c0660045e13e202aec5016047007800407815a0101e10d8040402020101d051783850124e0f801446831080f3e00b008080407c1b022ed0080b094e414f80a40080e0316800e01017010004064440c055906980406017a00ff911190184c0d64027b1099027a4133208f2019500aa81d240fb801e80404c005c0b72031b898b01e2a0fe1041201f100e2226a0080d02c1045c607ad171902c78413a04a004b68813c03840cda0028836f0120a017501c500c402020101507ae83f3c18401012145c09bdc088a0bcf0700040501d40101905a8040785bc010100808040600b60101e051c891b0428806d40401024c007e801fb11ad02500203008b606a00404020222660080802c802034009c05ce8079c151e0a981224823b400de08d9040a036b04d7e09f31158040408010200402070e8100c080b0000404010000001030002e020503c00030080c12020301400020280402020103c160001008000200804040201004020f058000002098000e000101c0603018000201010440800020400800028140200000042e110684c000000800020103000060112080003a00000140300810060000068140a008080000 else 0x100442087d014082180203c0780080b828002038056008080407c4496053700a004040202e0110080b01b1c12a010100808040401ede28a5050b80b7c1cc0101f071c81fc02032073a03e8040581f40101c0550040402020101f077a02700202010100809030480742278910ea0907810a604e917b208ab81696039700dd018a414d622d0080d00bb4194e098403b0032e00a4225f0080a8a3885)
def f3366uH1_34 (h : Nat) : Option (Nat × Nat) := lookupWord 118 492 9 17 9 4 f3366uH1_34F h
def f3366uL37F (i : Nat) : Nat := 0xefb52c33042b85c118450d78adb057100d202bddd88a1a7d1c56d9d5881c86e14efb5221b90c10ae1d85c118450d0d3e2f6c15c40c300b2085f46a5c86086988a1a77fc5eda20619a108d311434e43e91030c888a1aed9d5881c83352e44450d3e9e2b6d1030cdc29df6a443618576e02e08c2286bc5ed82b8806960a0db3e8d4b0cdc4450d3bfe2f6d10304c15c21869dff15b80ba201a58253bedc0af11434e2f6ceac40e4304b88a1a7d3c5112206e0eef88810b0c2bb70174450d78bdb35310304e086220161a755b86a6206092efb52e437111435e2f6d1030cc12c2186869721b80ba20619824bbed4b051143434b91db440977da915d8688a1af15b80ba20539011f8bdb440c319b808c1af17b6081823b7011435e2f6d8c304708e20a3bc5eda1a336d11434fa78b10370761a2286bc5eda20330511435e2f6d101a5823de0f9eddd89c85ae184d6594b52e91bcf78dfcc30ab4938794690564438334208104003ff9a64c140ffe5d930503ff9a24c140ffe60930503ff8824c140ffe5c930503ff9624c140ffe68530503ff9814c140ffe20530503ff9714c140ffe58530503ff9514c140ffe14530503ff9214c140ffe08530503ffa224c140ffe845305037f9924c140fee50530503fd9314c140bfeaa930503efa664c140ffa88930503ff2114c140
def f3366uL37 : PackingT := (25,3,7,12,f3366uL37F)
def f3366uH0_37F (i : Nat) : Nat := 0xb01e209182fe00b00dec21bc02385a719000aec75b06e108bc163871e031506801bfc51806f902a4199c42180300df0030037f89f311f00e7856982a00dfc108807006f509201bc037806fc09401bc037806fd03001be431006f1021c15904b806fe12ae1b4037806f00dfa224037806f603601bc037806f8015a0cd01680b700df63a8c0ea8996198c000037a03200df6008037806f80a5c078037c00630a1218786f30410047c206804006fb04201bec50285d60c9a15241828b53059e2ccc1f806f3139c0340379065b022e068037d09af1b601bc03790eee08de365020006f40d980bd02f006f602c01bc034806f00de01bc037806fe09f22ba86a806f00df8088037806f603e2154017283ab163a16f826006f406f2098037806f00de602580e1007309001bd409f88d718360d8037806fb02e01bf846006f00de01bc037c8b9714da144037d03bf17680e3014881900de615e069f06a104f8048037806fb1b401bc037806fa08e8238c2c806f00de00f6056582000de812e835d863008601be0300087a07d80a04729025609ac2f94271044f06a20f1452680500de2004c695014f0ce03b4037806f00dea21403798cfb0b801a0037a89100df414d044006f00dfe208037806f0201000319260908000000000100000614000200000303010200030004010400000c0a020000050c0400000105010000020000000000
def f3366uH0_37 (h : Nat) : Option (Nat × Nat) := lookupWord 54 244 8 15 7 4 f3366uH0_37F h
def f3366uH1_37F (i : Nat) : Nat := (if i<1 then 0xfbc17a0256008888c154409c280f15300445448401110088b092c84120111606b0044580c20111f01d988c802220111f029788b441ae60ee9028e02c1408803019073c8289c09d010700889827dc04d60a95129f0c01452b60da0088d80cb4479e0a0b14410244802f8064008880446c499a06ff0528044581000111008880446450ec2c9b13b100dec07c80293018a8b23421d02853066e0220c47e606d00888044400fde21d915180444022200b50088883db01f36102e0688005340c0c309d06480444009560274067583b541bb8022c07a2038a405d02155070e02dfc469206ac078b005b85d802350080a03620184230e3031a843f41482081f015f8b310564428c911c58218022242b7700d00444022240b85004804474194403d70682836c0506011100888044744fd401ee02380445420601110088d081704fa80ec50151008101ca407aa02f4010181d0e0a80088c82168619e2c591045898344e60111504bb0348022360a7f063004460107e2c2506c8044745ff6240e15ff88194544207d802ac007281a780a3b003c0aefc004a22b8053401e381d742d1712370320c0ac40ea00888024ec0e6a09d912700444022202e1813548165c01cc053e10a109d68164a0e9404b283dd05eb6076c10c281ec441d2255015b3087081b8a108713448a6044cb026d4062708f9048601113011a8264818f02846033281c7811900330034f02e800728286c02fa02bbc09760b67171e001180e8c0a1505e288ccc55cc279a077c0bf7c0ca40fae00cf02ee44bfe00d5039783018137e0d44001e0c0941676028c009502e6851fa049114690ab5804a80af702d58a470082203c0088d00d4022360ccb021804464221e015806ff8989003002e2003e502410128200ce034580ea4042a046e016c030f8058c3060088d00db054280422026681880223a0bf6055f8a5b80f3a0f24079f839240ff82b1d009e0272c13560c5c138d0b0340dd60de3148080be40b7808df153d8ba4c5a6800a517418117c4a8a0ade16c90a27009f22ebd10510020807e01110088909298197c0ff00889087f811d02cda02e004448112010de15c2884d801f628e008898356c0680111a03640043c1ea0111905610136c20b82aa7071b81c1859e011190820044405b8c2d4f047e0279c04962102179d0014c13160e090786842484d32257903bf014141ccc277615e503f3c5f00d06800081609004181a000300603010001214000001a000400440120000800070281c04000b00804160b00802020000c020100094020b0902c1c00028000402150100202028540603058240201038c0120000800000702000020b0a02c260100024000d190180810000c40a1700064000000084001b0b8102819028a40e000c0101e0200824240e018000a290001c4007208000000040040c09 else 0xe057910f0044741838030716c1004444730082613180445409121060085a0963c47bc2d70088b8bdc41fa00955067b81d40223010ae1750044445a420b1404380446c5a1c0b4b00ee02298000e08b700ff021100bae092f13340007c20120f8d00300445c17d624581820019cc59c4058c07dc8151c0d78282100db802dc07001110088e091c415522611086383)
def f3366uH1_37 (h : Nat) : Option (Nat × Nat) := lookupWord 137 476 9 17 9 4 f3366uH1_37F h
def f3366uL40F (i : Nat) : Nat := 0x8835c5db080a07fe4c140
def f3366uL40 : PackingT := (1,2,7,6,f3366uL40F)
def f3366uH1_40F (i : Nat) : Nat := 0xc8064033e1300cf8ce41601900c806403201900c8066c4b003a04006780001900c806403201900c809803201900c806700201980a601605ee0c908a81c405815303383c032019e140064032c0ec09006403223801840c504201900cb82403201900c8064032c0400b88c803201980c006584e01900ce88803201940b783781401900c98b4032a2e00c806546c01900cf0a803201900c806403201900c984144801900c908345214182001400102000080200001
def f3366uH1_40 (h : Nat) : Option (Nat × Nat) := lookupWord 15 103 7 13 5 4 f3366uH1_40F h
def f3366uLevels : Nat → PackingT
  | 24 => f3366uL24
  | 27 => f3366uL27
  | 28 => f3366uL28
  | 30 => f3366uL30
  | 31 => f3366uL31
  | 33 => f3366uL33
  | 34 => f3366uL34
  | 37 => f3366uL37
  | 40 => f3366uL40
  | _ => emptyPackingT
def f3366uIdx0 : Nat → Nat → Option (Nat × Nat)
  | 27 => f3366uH0_27
  | 28 => f3366uH0_28
  | 30 => f3366uH0_30
  | 31 => f3366uH0_31
  | 33 => f3366uH0_33
  | 34 => f3366uH0_34
  | 37 => f3366uH0_37
  | _ => fun _ => none
def f3366uIdx1 : Nat → Nat → Option (Nat × Nat)
  | 31 => f3366uH1_31
  | 34 => f3366uH1_34
  | 37 => f3366uH1_37
  | 40 => f3366uH1_40
  | _ => fun _ => none
abbrev bkU := blockU f3366uLevels f3366uIdx0 f3366uIdx1
abbrev bmU (k tm s a b : Nat) := @blockU_merge f3366uLevels f3366uIdx0 f3366uIdx1 k tm s a b
set_option maxHeartbeats 0 in
theorem c24_0 : bkU 8 0 0 3=true:=chunkBlockU (ar:=9) (by decide +kernel)
theorem a24 : bkU 8 0 0 3 = true := c24_0
set_option maxHeartbeats 0 in
theorem c27_0 : bkU 9 0 0 48=true:=cellsBlockU (ar:=10) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c27_48 : bkU 9 0 48 23=true:=cellsBlockU (ar:=10) (d:=1) ⟨kU (by decide +kernel),kU (by decide +kernel)⟩
theorem a27 : bkU 9 0 0 71 = true := (bmU 9 0 0 48 23 c27_0 c27_48)
set_option maxHeartbeats 0 in
theorem c28_0 : bkU 9 1 0 33=true:=cellsBlockU (ar:=9) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
theorem a28 : bkU 9 1 0 33 = true := c28_0
set_option maxHeartbeats 0 in
theorem c30_0 : bkU 10 0 0 48=true:=cellsBlockU (ar:=11) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c30_48 : bkU 10 0 48 48=true:=cellsBlockU (ar:=11) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c30_96 : bkU 10 0 96 48=true:=cellsBlockU (ar:=11) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c30_144 : bkU 10 0 144 48=true:=cellsBlockU (ar:=11) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c30_192 : bkU 10 0 192 48=true:=cellsBlockU (ar:=11) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c30_240 : bkU 10 0 240 48=true:=cellsBlockU (ar:=11) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c30_288 : bkU 10 0 288 8=true:=chunkBlockU (ar:=11) (by decide +kernel)
theorem a30 : bkU 10 0 0 296 = true := (bmU 10 0 0 144 152 (bmU 10 0 0 48 96 c30_0 (bmU 10 0 48 48 48 c30_48 c30_96)) (bmU 10 0 144 96 56 (bmU 10 0 144 48 48 c30_144 c30_192) (bmU 10 0 240 48 8 c30_240 c30_288)))
set_option maxHeartbeats 0 in
theorem c31_0 : bkU 10 1 0 6=true:=chunkBlockU (ar:=9) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c31_6 : bkU 10 1 6 48=true:=cellsBlockU (ar:=10) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c31_54 : bkU 10 1 54 48=true:=cellsBlockU (ar:=10) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c31_102 : bkU 10 1 102 48=true:=cellsBlockU (ar:=10) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c31_150 : bkU 10 1 150 48=true:=cellsBlockU (ar:=10) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c31_198 : bkU 10 1 198 48=true:=cellsBlockU (ar:=10) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c31_246 : bkU 10 1 246 11=true:=chunkBlockU (ar:=10) (by decide +kernel)
theorem a31 : bkU 10 1 0 257 = true := (bmU 10 1 0 102 155 (bmU 10 1 0 6 96 c31_0 (bmU 10 1 6 48 48 c31_6 c31_54)) (bmU 10 1 102 96 59 (bmU 10 1 102 48 48 c31_102 c31_150) (bmU 10 1 198 48 11 c31_198 c31_246)))
set_option maxHeartbeats 0 in
theorem c33_0 : bkU 11 0 0 48=true:=cellsBlockU (ar:=12) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c33_48 : bkU 11 0 48 48=true:=cellsBlockU (ar:=12) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c33_96 : bkU 11 0 96 15=true:=cellsBlockU (ar:=12) (d:=1) ⟨kU (by decide +kernel),kU (by decide +kernel)⟩
theorem a33 : bkU 11 0 0 111 = true := (bmU 11 0 0 48 63 c33_0 (bmU 11 0 48 48 15 c33_48 c33_96))
set_option maxHeartbeats 0 in
theorem c34_0 : bkU 11 1 0 1=true:=chunkBlockU (ar:=9) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c34_1 : bkU 11 1 1 48=true:=cellsBlockU (ar:=10) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c34_49 : bkU 11 1 49 48=true:=cellsBlockU (ar:=11) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c34_97 : bkU 11 1 97 48=true:=cellsBlockU (ar:=11) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c34_145 : bkU 11 1 145 48=true:=cellsBlockU (ar:=11) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c34_193 : bkU 11 1 193 48=true:=cellsBlockU (ar:=11) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c34_241 : bkU 11 1 241 32=true:=cellsBlockU (ar:=11) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
theorem a34 : bkU 11 1 0 273 = true := (bmU 11 1 0 97 176 (bmU 11 1 0 1 96 c34_0 (bmU 11 1 1 48 48 c34_1 c34_49)) (bmU 11 1 97 96 80 (bmU 11 1 97 48 48 c34_97 c34_145) (bmU 11 1 193 48 32 c34_193 c34_241)))
set_option maxHeartbeats 0 in
theorem c37_0 : bkU 12 1 0 7=true:=chunkBlockU (ar:=10) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c37_7 : bkU 12 1 7 18=true:=cellsBlockU (ar:=11) (d:=1) ⟨kU (by decide +kernel),kU (by decide +kernel)⟩
theorem a37 : bkU 12 1 0 25 = true := (bmU 12 1 0 7 18 c37_0 c37_7)
set_option maxHeartbeats 0 in
theorem c40_0 : bkU 13 1 0 1=true:=chunkBlockU (ar:=10) (by decide +kernel)
theorem a40 : bkU 13 1 0 1 = true := c40_0
theorem tables3366u : ∀ k ≤ 13, ∀ tm ≤ 1, blockU f3366uLevels f3366uIdx0 f3366uIdx1 k tm 0 (f3366uLevels (3*k+tm)).1 = true := by
  intro k hk tm ht; interval_cases k <;> interval_cases tm
  · exact (rfl : blockU f3366uLevels f3366uIdx0 f3366uIdx1 0 0 0 0 = true)
  · exact (rfl : blockU f3366uLevels f3366uIdx0 f3366uIdx1 0 1 0 0 = true)
  · exact (rfl : blockU f3366uLevels f3366uIdx0 f3366uIdx1 1 0 0 0 = true)
  · exact (rfl : blockU f3366uLevels f3366uIdx0 f3366uIdx1 1 1 0 0 = true)
  · exact (rfl : blockU f3366uLevels f3366uIdx0 f3366uIdx1 2 0 0 0 = true)
  · exact (rfl : blockU f3366uLevels f3366uIdx0 f3366uIdx1 2 1 0 0 = true)
  · exact (rfl : blockU f3366uLevels f3366uIdx0 f3366uIdx1 3 0 0 0 = true)
  · exact (rfl : blockU f3366uLevels f3366uIdx0 f3366uIdx1 3 1 0 0 = true)
  · exact (rfl : blockU f3366uLevels f3366uIdx0 f3366uIdx1 4 0 0 0 = true)
  · exact (rfl : blockU f3366uLevels f3366uIdx0 f3366uIdx1 4 1 0 0 = true)
  · exact (rfl : blockU f3366uLevels f3366uIdx0 f3366uIdx1 5 0 0 0 = true)
  · exact (rfl : blockU f3366uLevels f3366uIdx0 f3366uIdx1 5 1 0 0 = true)
  · exact (rfl : blockU f3366uLevels f3366uIdx0 f3366uIdx1 6 0 0 0 = true)
  · exact (rfl : blockU f3366uLevels f3366uIdx0 f3366uIdx1 6 1 0 0 = true)
  · exact (rfl : blockU f3366uLevels f3366uIdx0 f3366uIdx1 7 0 0 0 = true)
  · exact (rfl : blockU f3366uLevels f3366uIdx0 f3366uIdx1 7 1 0 0 = true)
  · exact a24
  · exact (rfl : blockU f3366uLevels f3366uIdx0 f3366uIdx1 8 1 0 0 = true)
  · exact a27
  · exact a28
  · exact a30
  · exact a31
  · exact a33
  · exact a34
  · exact (rfl : blockU f3366uLevels f3366uIdx0 f3366uIdx1 12 0 0 0 = true)
  · exact a37
  · exact (rfl : blockU f3366uLevels f3366uIdx0 f3366uIdx1 13 0 0 0 = true)
  · exact a40
def or04 : Sig := bin true (inputs.getD 0 zero) (inputs.getD 4 zero)
def or03 : Sig := bin true (inputs.getD 0 zero) (inputs.getD 3 zero)
def live3366 : List Sig := inputs.drop 1 ++ [or04, or03]
def bank3366 : List Sig := zero :: live3366

def wit3366 : Nat → Row × Row
  | 0 => (⟨1, by decide⟩, ⟨3, by decide⟩)
  | 1 => (⟨2, by decide⟩, ⟨6, by decide⟩)
  | 2 => (⟨5, by decide⟩, ⟨13, by decide⟩)
  | 3 => (⟨1, by decide⟩, ⟨17, by decide⟩)
  | 4 => (⟨1, by decide⟩, ⟨33, by decide⟩)
  | 5 => (⟨2, by decide⟩, ⟨66, by decide⟩)
  | 6 => (⟨4, by decide⟩, ⟨132, by decide⟩)
  | 7 => (⟨8, by decide⟩, ⟨264, by decide⟩)
  | 8 => (⟨10, by decide⟩, ⟨11, by decide⟩)
  | 9 => (⟨16, by decide⟩, ⟨17, by decide⟩)
  | _ => (⟨0, by decide⟩, ⟨0, by decide⟩)

theorem wit3366_ok :
    (List.finRange 10).all (fun i =>
      let p := wit3366 i.val
      (bit p.1 graph != bit p.2 graph) &&
      live3366.all (fun w => w == live3366.getD i.val zero || bit p.1 w == bit p.2 w)) = true := by
  decide +kernel

theorem live3366_len : live3366.length = 10 := by
  rw [live3366, List.length_append, List.length_drop, ← input_list, List.length_ofFn]; rfl

theorem no3366 : ImpossibleU graph 13 1 live3366.toFinset := by
  have hall := forestU_all f3366uLevels f3366uIdx0 f3366uIdx1 13 (boundsBefore known383)
    (before_sound known383 valid383) geomdead tables3366u 13 (by decide) 1 (by decide) 0 (by decide)
  have htgt : targetOf dead = graph := by decide +kernel
  have hs : sameWords (stateSetT f3366uLevels 40 0) live3366 = true := by decide +kernel
  rw [htgt, sameWords_sound hs] at hall
  exact hall

theorem bit_or04 (r : Row) : bit r or04 = (sample r 0 || sample r 4) := by
  simp only [or04, bit_bin, ite_true, sample]; rfl

theorem bit_or03 (r : Row) : bit r or03 = (sample r 0 || sample r 3) := by
  simp only [or03, bit_bin, ite_true, sample]; rfl

theorem edge3366_eq (x : Fin 9 → Bool) :
    ([((0 : Fin 9), (1 : Fin 9)), ((1 : Fin 9), (2 : Fin 9)), ((2 : Fin 9), (3 : Fin 9)), ((3 : Fin 9), (4 : Fin 9)),
      ((4 : Fin 9), (0 : Fin 9)), ((0 : Fin 9), (5 : Fin 9)), ((1 : Fin 9), (6 : Fin 9)), ((2 : Fin 9), (7 : Fin 9)),
      ((3 : Fin 9), (8 : Fin 9)), ((5 : Fin 9), (7 : Fin 9)), ((6 : Fin 9), (8 : Fin 9)), ((8 : Fin 9), (5 : Fin 9))].any
      fun p => x p.1 && x p.2) = edge x := by
  unfold edge
  simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc]

theorem bank3366_map (r : Row) :
    bank3366.map (bit r) =
      List.ofFn (Function.update (sample r) (0 : Fin 9) false) ++ [sample r 0 || sample r 4, sample r 0 || sample r 3] := by
  have hdrop : (inputs.drop 1).map (bit r) = (List.ofFn (sample r)).drop 1 := by
    rw [List.map_drop, ← sampled]
  have hupd : List.ofFn (Function.update (sample r) (0 : Fin 9) false) = false :: (List.ofFn (sample r)).drop 1 := by
    apply List.ext_getElem
    · simp
    · intro i hi1 hi2
      simp only [List.getElem_ofFn]
      cases i with
      | zero => simp [Function.update]
      | succ k =>
        simp only [List.getElem_cons_succ, List.getElem_drop, List.getElem_ofFn, Function.update]
        have hne : (⟨k + 1, by simpa using hi1⟩ : Fin 9) ≠ 0 := by intro h; cases h
        simp [hne, Nat.add_comm]
  have hbz : bit r zero = false := BitVec.getLsbD_zero
  simp only [bank3366, live3366, List.map_cons, List.map_append, List.map_nil, hbz, hdrop, bit_or04, bit_or03, hupd]
  rfl

theorem main3366 : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x2 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x1 x2.1 && x1 x2.2; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size ≤ (13 : ℕ) → (∀ (x5 : Fin (9 : ℕ) → Bool), x2.eval (List.ofFn (Function.update x5 (0 : Fin (9 : ℕ)) Bool.false) ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)), x5 (0 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ))]) = x1 x5) → False := by
  intro x1 C legal hsz hcomp
  have goalEq : (execute C.gates bank3366).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro m hm
    let r : Row := ⟨m, hm⟩
    change bit r ((execute C.gates bank3366).getD C.output zero) = bit r graph
    rw [← b_read, execute_bits _ _ _ (fun g hg => (legal g hg).1), bank3366_map r]
    exact (hcomp (sample r)).trans ((edge3366_eq (sample r)).trans (edge_table r).symm)
  have out := get_rep (execute C.gates bank3366) C.output
  rw [goalEq] at out
  have targetIn := out.resolve_right (fun hn => hn graph_proper)
  obtain ⟨k, t, S, hk, run, sub0⟩ := extract C.gates bank3366 legal graph_proper targetIn
  have sub : ∀ v ∈ S, v ∈ live3366 := by
    intro v hv
    have hm := sub0 v hv
    rcases List.mem_cons.mp hm with rfl | hm
    · exact False.elim ((live_proper run zero hv).1 rfl)
    · exact hm
  have hreq : live3366.toFinset ⊆ S := by
    intro v hv
    have hm := List.mem_toFinset.mp hv
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hm
    have hi10 : i < 10 := by rw [← live3366_len]; exact hi
    have hget : live3366[i]'hi = live3366.getD i zero := (List.getD_eq_getElem live3366 zero hi).symm
    have hh := List.all_eq_true.mp wit3366_ok ⟨i, hi10⟩ (List.mem_finRange _)
    simp only [Bool.and_eq_true, bne_iff_ne] at hh
    have h2 := List.all_eq_true.mp hh.2
    have hmemS := raw_required run _ _ sub (wit3366 i).1 (wit3366 i).2 hh.1 (fun w hw hn => by
      have ha := h2 w hw
      have hne : (w == live3366.getD i zero) = false := beq_eq_false_iff_ne.mpr hn
      rw [hne] at ha; simp only [Bool.false_or] at ha; exact beq_iff_eq.mp ha)
    exact hget.symm ▸ hmemS
  have eqS : S = live3366.toFinset :=
    Finset.Subset.antisymm (fun v hv => List.mem_toFinset.mpr (sub v hv)) hreq
  exact no3366 k t (hk.trans hsz) (fun h0 => by cases h0) (eqS ▸ run)

end PEqualNP.Outside.L_meta_3366

theorem PEqualNP.Outside.L_meta_3366 : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x2 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x1 x2.1 && x1 x2.2; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size ≤ (13 : ℕ) → (∀ (x5 : Fin (9 : ℕ) → Bool), x2.eval (List.ofFn (Function.update x5 (0 : Fin (9 : ℕ)) Bool.false) ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)), x5 (0 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ))]) = x1 x5) → False :=
  PEqualNP.Outside.L_meta_3366.main3366
