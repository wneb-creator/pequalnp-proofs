import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3863_aux
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
  | 0, t, S => t = 0 ∧ S = {target} ∧ proper target
  | k+1, t, S =>
    (∃ u U a, t = u+1 ∧ S = insert a U ∧ proper a ∧ neg a ∉ insert a U ∧ Live target k u (insert (neg a) U)) ∨
    (∃ U a b d, S = insert a (insert b U) ∧ proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live target k t (insert (bin d a b) U))

private lemma Live.stop {target : Sig} (hp : proper target) : Live target 0 0 {target} := ⟨rfl, rfl, hp⟩

private lemma Live.unary {target : Sig} {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
    (hfresh : neg a ∉ insert a U) (tail : Live target k t (insert (neg a) U)) :
    Live target (k+1) (t+1) (insert a U) := Or.inl ⟨t, U, a, rfl, rfl, ha, hfresh, tail⟩

private lemma Live.binary {target : Sig} {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live target k t (insert (bin d a b) U)) :
    Live target (k+1) t (insert a (insert b U)) := Or.inr ⟨U, a, b, d, rfl, ha, hb, hab, hfresh, tail⟩

private lemma live_proper {k t S} (h : Live target k t S) : ∀ a ∈ S, proper a := by
  induction k generalizing t S with
  | zero =>
    obtain ⟨_, rfl, hp⟩ := h
    simpa using hp
  | succ k ih =>
    rcases h with ⟨u, U, a, rfl, rfl, ha, _, tail⟩ | ⟨U, a, b, d, rfl, ha, hb, _, _, tail⟩
    · simpa using And.intro ha (fun x hx => ih tail x (Finset.mem_insert_of_mem hx))
    · simp only [Finset.forall_mem_insert]
      exact ⟨ha, hb, fun x hx => ih tail x (Finset.mem_insert_of_mem hx)⟩

private lemma live_size {k t S} (h : Live target k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction k generalizing t S with
  | zero =>
    obtain ⟨rfl, rfl, _⟩ := h
    simp
  | succ k ih =>
    rcases h with ⟨u, U, a, rfl, rfl, _, hf, tail⟩ | ⟨U, a, b, d, rfl, _, _, _, hf, tail⟩
    · have ht := ih tail
      have hu : neg a ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
      rw [Finset.card_insert_of_notMem hu] at ht
      have hc := Finset.card_insert_le a U
      exact ⟨by omega, by omega⟩
    · have ht := ih tail
      have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
      rw [Finset.card_insert_of_notMem hu] at ht
      have h1 := Finset.card_insert_le (a := a) (s := insert b U)
      have h2 := Finset.card_insert_le (a := b) (s := U)
      exact ⟨by omega, by omega⟩


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
  | 0, bank => bank = roots
  | p+1, bank =>
    (∃ b a, Reach roots p b ∧ Available b a ∧ bank = inv a :: b) ∨
    (∃ b a c op, Reach roots p b ∧ Available b a ∧ Available b c ∧ bank = combine op a c :: b)

theorem Reach.start {R} {roots : List (Wire R)} : Reach roots 0 roots := rfl
theorem Reach.one {R} {roots : List (Wire R)} {p bank a} (h : Reach roots p bank) (ha : Available bank a) :
    Reach roots (p+1) (inv a :: bank) := Or.inl ⟨bank, a, h, ha, rfl⟩
theorem Reach.two {R} {roots : List (Wire R)} {p bank a b} (op : Bool) (h : Reach roots p bank)
    (ha : Available bank a) (hb : Available bank b) :
    Reach roots (p+1) (combine op a b :: bank) := Or.inr ⟨bank, a, b, op, h, ha, hb, rfl⟩

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

def Run {R} (goal : Wire R) : Nat → List (Wire R) → Prop
  | 0, xs => xs.Perm [goal]
  | s+1, xs =>
    (∃ a rest save, (a::rest).Perm xs ∧ Run goal s (inv a :: kept save a rest)) ∨
    (∃ a b rest op ka kb, (a::b::rest).Perm xs ∧ Run goal s (combine op a b :: kept ka a (kept kb b rest)))

theorem Run.stop {R} {goal : Wire R} : Run goal 0 [goal] := List.Perm.refl _
theorem Run.perm {R} {goal : Wire R} {s xs zs} (hp : xs.Perm zs) (h : Run goal s xs) : Run goal s zs := by
  cases s with
  | zero => exact hp.symm.trans h
  | succ s =>
    rcases h with ⟨a, rest, save, p, hr⟩ | ⟨a, b, rest, op, ka, kb, p, hr⟩
    · exact Or.inl ⟨a, rest, save, p.trans hp, hr⟩
    · exact Or.inr ⟨a, b, rest, op, ka, kb, p.trans hp, hr⟩
theorem Run.one {R} {goal : Wire R} {s a rest} (save : Bool)
    (h : Run goal s (inv a :: kept save a rest)) : Run goal (s+1) (a::rest) :=
  Or.inl ⟨a, rest, save, List.Perm.refl _, h⟩
theorem Run.two {R} {goal : Wire R} {s a b rest} (op ka kb : Bool)
    (h : Run goal s (combine op a b :: kept ka a (kept kb b rest))) : Run goal (s+1) (a::b::rest) :=
  Or.inr ⟨a, b, rest, op, ka, kb, List.Perm.refl _, h⟩

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
  induction s generalizing ws p bank with
  | zero =>
    have hgoal : goal ∈ ws := h.mem_iff.mpr (by simp)
    have hmass : mass ws = mass [goal] := by simpa only [mass] using (h.map cost).sum_eq
    exact ⟨p, bank, hp, hs goal hgoal, by rw [hmass]; simp [mass, cost, nc]⟩
  | succ s ih =>
    rcases h with ⟨a, rest, save, eq, hr⟩ | ⟨a, b, rest, op, ka, kb, eq, hr⟩
    · have hs' : supply bank (a :: rest) := fun v hv => hs v (eq.mem_iff.mp hv)
      obtain ⟨r, T, hT, hz, inc, le⟩ := extend_one roots hp (hs' a (by simp))
      have ht : supply T (inv a :: kept save a rest) := by
        intro v hv
        rcases List.mem_cons.mp hv with rfl | hh
        · exact hz
        · exact inc v (hs' v (List.mem_cons.mpr (mem_kept hh)))
      obtain ⟨q, W, hW, hv, hl⟩ := ih hr hT ht
      have hlen := mass_kept a rest save
      have hmass : mass ws = mass (a :: rest) := by simpa only [mass] using (eq.symm.map cost).sum_eq
      rw [hmass, mass_cons]
      rw [mass_cons] at hl
      exact ⟨q, W, hW, hv, by omega⟩
    · have hs' : supply bank (a :: b :: rest) := fun v hv => hs v (eq.mem_iff.mp hv)
      obtain ⟨r, T, hT, hz, inc, le⟩ := extend_two roots op hp (hs' a (by simp)) (hs' b (by simp))
      have ht : supply T (combine op a b :: kept ka a (kept kb b rest)) := by
        intro v hv
        rcases List.mem_cons.mp hv with rfl | hh
        · exact hz
        · apply inc v
          apply hs'
          rcases mem_kept hh with rfl | hh
          · simp
          · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept hh))
      obtain ⟨q, W, hW, hv, hl⟩ := ih hr hT ht
      have hlen := mass_kept a (kept kb b rest) ka
      have hlen' := mass_kept b rest kb
      have hmass : mass ws = mass (a :: b :: rest) := by simpa only [mass] using (eq.symm.map cost).sum_eq
      rw [hmass, mass_cons, mass_cons]
      rw [mass_cons] at hl
      exact ⟨q, W, hW, hv, by omega⟩

def restrictRows {R S : Type} (rows : S → R) (a : Wire R) : Wire S :=
  fun r => a (rows r)

theorem restrict_kept {R S : Type} (rows : S → R) (k : Bool) (a : Wire R) (ws) :
    (kept k a ws).map (restrictRows rows) =
    kept k (restrictRows rows a) (ws.map (restrictRows rows)) := by
  cases k <;> simp [kept]

theorem restrict_run {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws) :
    Run (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction s generalizing ws with
  | zero => exact h.map _
  | succ s ih =>
    rcases h with ⟨a, rest, save, p, hr⟩ | ⟨a, b, rest, op, ka, kb, p, hr⟩
    · have ih' := ih hr
      simp only [List.map_cons, restrict_kept] at ih'
      exact Run.perm (p.map _) (Run.one save ih')
    · have ih' := ih hr
      simp only [List.map_cons, restrict_kept] at ih'
      cases op
      · exact Run.perm (p.map _) (Run.two false ka kb ih')
      · exact Run.perm (p.map _) (Run.two true ka kb ih')

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
  induction k generalizing u S v with
  | zero =>
    obtain ⟨rfl, rfl, _⟩ := h
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | succ k ih =>
    rcases h with ⟨u', U, a, rfl, rfl, ha, fresh, htail⟩ | ⟨U, a, b, d, rfl, ha, hb, hab, fresh, htail⟩
    · let rest := (U.erase a).toList
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
      have progress := ih htail (neg a::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
      rw [List.map_cons,map_kept,obs_neg] at progress
      have perm : (a::rest).Perm v := by
        apply List.perm_of_nodup_nodup_toFinset_eq (List.nodup_cons.mpr ⟨hm,hr⟩) hv
        simp [er,eqv]
      exact Run.perm (perm.map _) (Run.one save progress)
    · let rest := ((U.erase a).erase b).toList
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
      have progress := ih htail (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
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
  induction p generalizing bank k t S with
  | zero =>
    subst h
    exact ⟨k,t,S,by omega,run,sub⟩
  | succ p ih =>
    rcases h with ⟨b, a, hb, ha, rfl⟩ | ⟨b, a, c, d, hb, ha, hc, rfl⟩
    · rw [List.map_cons,table_inv] at sub
      obtain ⟨k',t',S',hk,run',sub'⟩ := pull_cons run (inv_rep (available_rep ha)) sub
      obtain ⟨l,v,U,hl,hr,hs⟩ := ih hb run' sub'
      exact ⟨l,v,U,by omega,hr,hs⟩
    · rw [List.map_cons,table_bin] at sub
      obtain ⟨k',t',S',hk,run',sub'⟩ := pull_cons run (bin_rep d (available_rep ha) (available_rep hc)) sub
      obtain ⟨l,v,U,hl,hr,hs⟩ := ih hb run' sub'
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
  induction k generalizing t S with
  | zero =>
    obtain ⟨rfl, rfl, _⟩ := h
    exact ⟨_, by simp, diff⟩
  | succ k ih =>
    rcases h with ⟨u, U, a, rfl, rfl, _, _, tail⟩ | ⟨U, a, b, d, rfl, _, _, _, _, tail⟩
    · obtain ⟨v, hv, hd⟩ := ih tail
      rcases Finset.mem_insert.mp hv with rfl | hu
      · refine ⟨a, by simp, ?_⟩
        exact fun he => hd (by rw [bit_neg, bit_neg, he])
      · exact ⟨v, Finset.mem_insert_of_mem hu, hd⟩
    · obtain ⟨v, hv, hd⟩ := ih tail
      rcases Finset.mem_insert.mp hv with rfl | hu
      · by_cases aeq : bit r a = bit s a
        · refine ⟨b, by simp, ?_⟩
          intro beq
          exact hd (by rw [bit_bin, bit_bin, aeq, beq])
        · exact ⟨a, by simp, aeq⟩
      · exact ⟨v, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu), hd⟩

theorem raw_required {T k t S} (h : Live T k t S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def graph : Sig := 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
def seed : Sig := 0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00
def seed01 : Sig := 0x88888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888
def seed02 : Sig := 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0
def seed04 : Sig := inputs.getD 0 zero &&& inputs.getD 4 zero
def seed14 : Sig := inputs.getD 1 zero &&& inputs.getD 4 zero
def seed64 : Sig := inputs.getD 6 zero &&& inputs.getD 4 zero

def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem seed_table : ∀ r : Row, bit r seed = (sample r 0 && sample r 3) := by decide +kernel
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
    (first : ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 3))
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
  induction k generalizing t S with
  | zero =>
    obtain ⟨rfl, rfl, hp⟩ := h
    simpa using Live.stop (pp _ hp)
  | succ k ih =>
    rcases h with ⟨u, U, a, rfl, rfl, hp, hf, tail⟩ | ⟨U, a, b, d, rfl, ha, hb, hab, hf, tail⟩
    · have ih' := ih tail
      have fresh : rename f (neg a) ∉ (insert a U).image (rename f) := by
        intro hm
        obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
        exact hf (inj eq ▸ hv)
      simp only [Finset.image_insert,rename_neg] at fresh ih' ⊢
      exact Live.unary (pp _ hp) fresh ih'
    · have ih' := ih tail
      have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f) := by
        intro hm
        obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
        exact hf (inj eq ▸ hv)
      simp only [Finset.image_insert,rename_bin] at fresh ih' ⊢
      exact Live.binary (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih'

theorem mono_row_difference {T k t S} (h : Live T k t S) (none : t=0) {r s : Row}
    (pos : bit r T = true) (negRow : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction k generalizing t S with
  | zero =>
    obtain ⟨rfl, rfl, _⟩ := h
    exact ⟨_,by simp,pos,negRow⟩
  | succ k ih =>
    rcases h with ⟨u, U, a, ht, _, _, _, _⟩ | ⟨U, a, b, d, rfl, _, _, _, _, tail⟩
    · omega
    · obtain ⟨v,hv,hp,hn⟩ := ih tail none
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
  cases k with
  | zero =>
    obtain ⟨rfl, he, _⟩ := h
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | succ k =>
    rcases h with ⟨t, U, a, rfl, he, ha, hf, tail⟩ | ⟨U, a, b, d, he, ha, hb, hab, hf, tail⟩
    · have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
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
    · have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
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



def apart (m j : Nat) : Bool := m.testBit 9 && (j==0 || j==3)
def word (m j : Nat) : Sig := if apart m j then inputs.getD j zero &&& ~~~seed else inputs.getD j zero
def selected (m : Nat) : List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,word m i) else none
def vars (m : Nat) := (selected m).map Prod.snd
def vertex (m j : Nat) := if m.testBit j then word m j else zero
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
  if f.testBit 9 && ((z ||| o) &&& 9) != 0 then f ^^^ 512
  else if m == 1535 || m == 2559 then f &&& 511
  else f
def chartGoal (m : Nat) : Sig :=
  if m=1535 then graphGoal m &&& ~~~seed01
  else if m=2559 then graphGoal m &&& ~~~seed02
  else graphGoal m
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
def wordCol (m : Nat) (v : Nat → Bits) (j : Nat) : Bits :=
  if apart m j then v j &&& ~~~(v 0 &&& v 3) else v j
theorem seed_word : seed = inputs.getD 0 zero &&& inputs.getD 3 zero := by decide +kernel
theorem word_bit (m : Nat) (v : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow v i) (word m j.val) = (wordCol m v j.val).getLsbD i.val := by
  by_cases h : apart m j.val = true
  · have e := asRow_bit v i j
    have u := asRow_bit v i (0 : Fin 9)
    have w := asRow_bit v i (3 : Fin 9)
    change (inputs.getD j.val zero).getLsbD (asRow v i).val = _ at e
    change (inputs.getD 0 zero).getLsbD (asRow v i).val = (v 0).getLsbD i.val at u
    change (inputs.getD 3 zero).getLsbD (asRow v i).val = (v 3).getLsbD i.val at w
    rw [word,wordCol,if_pos h,if_pos h,seed_word]
    simp only [bit,BitVec.getLsbD_and,BitVec.getLsbD_not,(asRow v i).isLt,i.isLt,decide_true,Bool.true_and,e,u,w]
  · rw [word,wordCol,if_neg h,if_neg h]
    exact asRow_bit v i j
def rawDecor (m : Nat) (p q : Nat → Bits) : List Decor :=
  (selected m).map (fun (j,a) => (a,wordCol m p j,wordCol m q j))
theorem selected_entry {m j a} (h : (j,a) ∈ selected m) :
    j<9 ∧ a=word m j := by
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
  · exact (word_bit m p ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm
  · exact (word_bit m q ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm

def liftGoal (m : Nat) (v : Nat → Bits) : Bits :=
  let x := fun j => if m.testBit j then wordCol m v j else 0
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then wordCol m v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using word_bit m v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then wordCol m v j else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
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
    obtain ⟨_, he, _⟩ := h
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


abbrev IndexTree (α : Type) := { t : (Nat → Option α) × List α // ∀ i x, t.1 i = some x → x ∈ t.2 }
def IndexTree.read {α} (t : IndexTree α) (i : Nat) : Option α := t.1.1 i
def IndexTree.values {α} (t : IndexTree α) : List α := t.1.2
theorem IndexTree.read_mem {α} (tree : IndexTree α) {i x} (e : tree.read i=some x) :
    x ∈ tree.values := tree.2 i x e
def itLeaf {α} (xs : List α) : IndexTree α :=
  ⟨(fun i => xs[i]?, xs), fun _ _ h => List.mem_of_getElem? h⟩
def itFork {α} (pivot : Nat) (a b : IndexTree α) : IndexTree α :=
  ⟨(fun i => if i < pivot then a.1.1 i else b.1.1 (i - pivot), a.1.2 ++ b.1.2), fun i x h => by
    dsimp only at h
    split at h
    · exact List.mem_append_left _ (a.2 _ _ h)
    · exact List.mem_append_right _ (b.2 _ _ h)⟩

abbrev Forest :=
  Nat × Nat × (Nat → Bits × Bits) × IndexTree ColumnInfo × Array (List Nat) × (Nat → Packing) × (Nat → Nat → Option (Nat × Nat))
def Forest.mask (g : Forest) : Nat := g.1
def Forest.cap (g : Forest) : Nat := g.2.1
def Forest.samples (g : Forest) : Nat → Bits × Bits := g.2.2.1
def Forest.cols (g : Forest) : IndexTree ColumnInfo := g.2.2.2.1
def Forest.autos (g : Forest) : Array (List Nat) := g.2.2.2.2.1
def Forest.levels (g : Forest) : Nat → Packing := g.2.2.2.2.2.1
def Forest.index (g : Forest) : Nat → Nat → Option (Nat × Nat) := g.2.2.2.2.2.2

def wiresOf (g : Forest) :=
  let ws := rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  if g.mask=1535 then
    let nonedge := dneg (dbin false (ws.getD 0 defaultDecor) (ws.getD 1 defaultDecor))
    ws.map (fun w => dbin false w nonedge)
  else if g.mask=2559 then
    let nonedge := dneg (dbin false (ws.getD 0 defaultDecor) (ws.getD 2 defaultDecor))
    ws.map (fun w => dbin false w nonedge)
  else ws
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a := by
  have base := raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  intro a ha
  unfold wiresOf at ha
  split at ha
  · obtain ⟨w,hw,rfl⟩ := List.mem_map.mp ha
    exact faithful_bin false (base w hw) (faithful_neg (faithful_bin false
      (faithful_get base 0) (faithful_get base 1)))
  · split at ha
    · obtain ⟨w,hw,rfl⟩ := List.mem_map.mp ha
      exact faithful_bin false (base w hw) (faithful_neg (faithful_bin false
        (faithful_get base 0) (faithful_get base 2)))
    · exact base _ ha

def targetOf (g : Forest) := chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) :=
  if m=1535 then liftGoal m v &&& ~~~(v 0 &&& v 1)
  else if m=2559 then liftGoal m v &&& ~~~(v 0 &&& v 2)
  else liftGoal m v
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  by_cases e1 : m=1535
  · have u := asRow_bit v i (0 : Fin 9)
    have w := asRow_bit v i (1 : Fin 9)
    have h := bit_liftGoal m v i
    change (inputs.getD 0 zero).getLsbD (asRow v i).val = (v 0).getLsbD i.val at u
    change (inputs.getD 1 zero).getLsbD (asRow v i).val = (v 1).getLsbD i.val at w
    have seedEq : seed01 = inputs.getD 0 zero &&& inputs.getD 1 zero := by decide +kernel
    simp only [chartGoal,chartSamples,e1,ite_true,bit,seedEq,BitVec.getLsbD_and,
      BitVec.getLsbD_not,(asRow v i).isLt,i.isLt,decide_true,Bool.true_and,u,w] at h ⊢
    rw [h]
  · by_cases e2 : m=2559
    · have u := asRow_bit v i (0 : Fin 9)
      have w := asRow_bit v i (2 : Fin 9)
      have h := bit_liftGoal m v i
      change (inputs.getD 0 zero).getLsbD (asRow v i).val = (v 0).getLsbD i.val at u
      change (inputs.getD 2 zero).getLsbD (asRow v i).val = (v 2).getLsbD i.val at w
      have seedEq : seed02 = inputs.getD 0 zero &&& inputs.getD 2 zero := by decide +kernel
      have ne12 : (2559 : Nat) ≠ 1535 := by decide
      simp only [chartGoal,chartSamples,e2,ne12,ite_false,ite_true,bit,seedEq,BitVec.getLsbD_and,
        BitVec.getLsbD_not,(asRow v i).isLt,i.isLt,decide_true,Bool.true_and,u,w] at h ⊢
      rw [h]
    · simpa only [chartGoal,chartSamples,e1,e2,ite_false] using bit_liftGoal m v i
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
    obtain ⟨_, he, _⟩ := h
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
def g15samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbaf3ea78de4d799d,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff450cc90c3c245919),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdf7ff8fe9f9b7ed5,0x20812421801324c4),(0xefbdbf97f9f6bf6a,0x102a401415600a0a),(0xf3a9d7437375f5ba,0xfc028ab620235b0),(0,0),(0,0),(0,0),(0,0),(0,0)]
def g15columns : IndexTree ColumnInfo := (itLeaf [])
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
def g31columns : IndexTree ColumnInfo := (itFork 2 (itLeaf [(1,0,30,0,4),(2,0,29,0,4)]) (itLeaf [(4,0,27,0,4),(8,0,23,0,4),(16,0,15,0,4)]))
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
def g47columns : IndexTree ColumnInfo := (itLeaf [(8,0,39,0,4)])
def g47autos : Array (List Nat) := #[[],[83,32]]
def g47levels : Nat → Packing
  | _ => emptyPacking
def g47index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g47 : Forest := ⟨47,4,fun j => g47samples[j]?.getD (0,0),g47columns,g47autos,g47levels,g47index⟩
def g55samples : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbfffffdf7defdfafbfd3fcebcfdeffcebffefe76de77fed7f1773f95eb2ebeb,0x400028000010005000000400701010180030103060043200102204010904888),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdb7fbfbb9ad3afd94caf0b9db5bbdf7f7d39bfcdadcf77ec9eccd2fb9cf16b5,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2484444214284026a4e002420468a8a43140a00408d944460a4082569431231),(0xeda5e7e7b2fc29de4ffc371dba2bf0775ff12db9b18bb528fedad96afcd3c5e,0x12589919410293410206d0396285445a082c5d2bf0022b20f0895d2048c2c4e),(0,0),(0xf1cd79264efe956afa7a64bb677ab40beba463600362eda36f3357b7d763926,0xe3a8651b1a36a0acc57538a080f6ea703078a0c13c28dc34c91f3868663126),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe05fe74eda341d5872cbf684d5e2ed19e7e3bba5e964550dd792aec724f479,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01fb53db1204342a549861b60b6727a22d48ac0b14da4445855161ae724b471),(0,0),(0,0),(0,0)]
def g55columns : IndexTree ColumnInfo := (itLeaf [(16,0,39,0,4)])
def g55autos : Array (List Nat) := #[[],[84]]
def g55levels : Nat → Packing
  | _ => emptyPacking
def g55index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g55 : Forest := ⟨55,4,fun j => g55samples[j]?.getD (0,0),g55columns,g55autos,g55levels,g55index⟩
def g63samples : Array (Bits × Bits) := #[(0xdabffdfdbdf61bfbfc7dcbe34f7f1b17917df75df7edd9eff77b6dbd3dcebed3cfbfaddba50fcabded46bc9b579eb7bd3d92776566ad4ad3debe36d74deb7f9faf189ad76da7dc1a6b4eaf21eb254de4ae1f7451bb34d9456fd18e934db17349,0x4400202400040800310000100084000ac0000102800a1100490002240004b2800a001b4000190000008108000574009200040400000594000190004218c0010840002890800550053044a00410008802d0060013000c004400188120c206208),(0xb6678efeffcbf5a9cad5bfd527a7a5bd74d1314b7915f5b2ffdec2fc5d978f8ab3b44b2b5add5b771711b15ce99bf2b3f5bce975ef94cd59a34e76ab937848a94ef6be6c9579db5905539ea703c87a7d4ae11fe2ae423fade4a3c3299b0724e7,0x499461811a200a55004cf88854029340027a680613c002ec00233c1096d01045025d0203d400243150030b7e4900b00499e023395882049d0206ec00041398010bbb1000b7310ad00cc0858112c8207810e917400e423d0034024309910504e5),(0xbfdd27bedf8fade4776ebf9d185bc5bd76aeffb29711f77d628e86e5fffdff6d1a52bff6da987348e3e147dcecdbcc68d1accc4e7d7d77b9734cfbbcefbc022d72eff5a31a72e32584dd5a72accb1256ede309af577ea6b3ab2be572a2769632,0x20983204990108b1910222a2810c12a8041040402e00006394000908008912a582448429aad10a21a0240190b504314209040621245140c82010e8812042049440841100c0c52080310832a5111106e902488a012c82618908a42202729212),(0x77ddb87389d95f9f7bbe7e8eb89e6e76fbf75ca7fd5bb3758b555b578affe964ae7e7fa493e06d03bebc4fb5cff51e46b2dd5bdbb1eab66f60f7d916b9c6944fd85b6f0fc30a2ae7d2afc9dc369ef80bb1b0b2dd52e9331e786f7a5d38e8c8b4,0x1482478012444200420888514440810c402202189081ecc814422aa4c048408050190921c0450c000a080254044021081134422900082c11250884167012813a48094aca870a3283708e41084282480000c012150640581c30655a55288040a4),(0xdca768aafb78ce8d2db2ec3fbdddfa4ec963339dbac7a8e05eccbf0bb99ddf5febcef6dc7762a4a79d9ad8f70324ba6e724754bded1eed86f695f276b70acbd73dc66e39a88d0cfed920a0ee10b5a4dd5893bba709bff6dc1ece388c561e1ed5,0x210938550593284a984457082a220ca002159526023c0223a02100100d271046aa46f2022bb0201ea5730921b3008e848a002106a7520082d20653c8040064810364a00030c5086c0c2084761035a077101508a009ba22e00b822088521e1c51),(0x77dad76bd4ced656e7ec247a694c9eb5b66dc4de71aac18acebb177a9bac7a62d6f3e3996dd9d62d6ecf7b18557229a30b5ebb1ef46b568a8f3400a7c2d3365caade63d0f2234a24623735bcfaee29c0664eddfc63b2a86915f817ca03dc41fa,0x88252894b2b3256598a758928465236453b27d28c68c4c28a24dcc0d24d500d4a845700845b04bd175706d345a20a0a24d641d897dd822a1d52444cad2629c8e732b305273362844202335b73c8d8150424e93e44a78286995ec17c803dc01f2),(0,0),(0,0),(0,0)]
def g63columns : IndexTree ColumnInfo := (itLeaf [(32,0,31,0,7)])
def g63autos : Array (List Nat) := #[[],[50,65]]
def g63levels : Nat → Packing
  | _ => emptyPacking
def g63index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g63 : Forest := ⟨63,7,fun j => g63samples[j]?.getD (0,0),g63columns,g63autos,g63levels,g63index⟩
def g111d6 (i : Nat) : Nat := 0x120ff
def g111l6 : Packing := (1,0,2,0,1,0,0,g111d6)
def g111samples : Array (Bits × Bits) := #[(0xeafcc7b96fc59ffd26c5e2bb3d7bd378fb35ff5dcb26f92afa5f57eff59a73b7aaa379b2fc8d7a99e2ef9efcf4defd4efabc9c89733cebade5579ad5abbcd64d8557ad3d63bd1c6a75510ce3b9bf05e462ee0edf6dfb2914efc74c7d31727465,0x4d00310a2003881269402d0c00406ccc142a8012908082d00025ac006a88036948003229000032d4001bf20024ec2018680000aaf2500325400423a6f02003840040a8016ea8106822700071012c01d500600ad401ea0010f407087831504444),(0xf771ad34ff2bcf4fbd7f5f5de52efaeb7ebbabfffefbf2eab7c7cf56f8ecea565ddfabcf87cb61db9d6ef4aecff7cebd76fe679cfb9935e6adabc77cdcdb677ed3da5e4f56b4cbe39cfd7aed1f519a6b999796b48a51f4f7b8ad91a66cc6d9cb,0x1204940050200482000010001c10308054448009004424020800871400ac0690000402004e0508404004081210450414000904018220d090010808000a44280600460810104d92040818880c1010088d8400200a10a1400808810604821909),(0xf5be76df5e79b8b5d13f5f6e3ecd176fbeee538a7cfb9f7f6b7fad9b13bb7fed97560ecd71f29f3f1e3ef959a338e3a9e32bd5e7cfc7b51df73d7e9e165479b3baa9a0d59e62e11eead3ad5c624777de8699f96d3766d64d1f3fa2ca8f3d2e52,0x8e4d19200884440101e4a802e100a0c04000830eb000289800c49240c1c411082c325a6812b0485430294040c52402008322a4b0e00c0021216842103a050a9080848145264020288841a770220547500211500d95204c05521120880b352452),(0xde2ebbc73c1cf83c4cedbed77297d7f5b666582db23d5c5d7bf4a54b37a75f4992f88d683d388ea5bafb57791a5deb9b257390777cf70e9d329773c24416edd93fe3d2909bc3b81d7e62dd94d70a759eb42b6b51587d63da2e7eea6ce78912bc,0x10b22099c5638280b403142808691e02bd9d04d1097a9640ce2041351e20e64283892100494815238b12089820999d9858901b4e1903515e001721098578a5416f515492d981d895722018845902b08a5c4a2a2248dd03d08c66ca64e48812ac),(0,0),(0x4a99db5e74fdf3bbfb83b4b12e735e58f515867b75942dba656f9eeac55739b971685432ece5b39368c30fbbb9f895ca9efa5eceda2fea7be4766f052ba5def635ccf928215f7640050f6846acafb2ca6efbba0bffbfdb9043d87d111c3c3ebd,0x12d68401de50564414b80023f49c0203c0413d800068400bbb08034f0177ac0427f40400f6de0023bcc009fc1201950403ff4900082ea08a2fc908010c8a4053de0011e801464d050407f806ac13f8026d9b800bfa055d40038875010c2c3ab9),(0x107b7e8791b6519a9ebd6f37d374faa298392ebad8b5e4afe6bd267679568b3365bebaabdf6ef4e9035a918e8ca50ef74769b2b74aea726a09a6c5e9463715fb76745a9b1b6212a1b9add6dec52a9ba55b57e399ab660ca6d0f217384af881fe,0xadc48a6a24248ac9294916cc74a18dce4988890976a839d0a90054480a8f001149b409fd5690d8d50882129489ae3083c83b5253565cd02541ca4550f495b985581508b28aaa022919a1e755a00eaaa54243a315f06a0c87d4f216384a7880f6),(0,0),(0,0)]
def g111columns : IndexTree ColumnInfo := (itLeaf [(4,8,99,0,4),(1,32,78,0,4),(64,0,47,0,5)])
def g111autos : Array (List Nat) := #[[],[83,32]]
def g111levels : Nat → Packing
  | 6 => g111l6
  | _ => emptyPacking
def g111index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | _ => fun _ => none
def g111 : Forest := ⟨111,6,fun j => g111samples[j]?.getD (0,0),g111columns,g111autos,g111levels,g111index⟩
def g119samples : Array (Bits × Bits) := #[(0xfab75f3dfbfa3756f92d9ff7baf5ff7dbfebb9b33bef7dcdf77fbffe7bbbf75546cedccfd6f7eb762bef3ffdd2ede7abbef7e4e4b775eb9be6ab6f4d5fde77f2b955ece57b3feb97c6d99b5cdd2fdd2ea315de5f3efbf8d44ddcaa7566eda9cd,0x20100000802449000a820000c1900042800052080010000098c000620802429000050a2000012e00000be20013404000082000047420011240000c8b8000110080002480036500158018000c4009400c9000c0062803a0400e00885042a10888),(0xaf7efcd6de9febfb57d6f5ddedde36f3db7fffeed79fdbfafcf255738c743cbbbff3e3b86b8f9fb9f5bdf54fbff79bd74f5afb3f7fba34f5bf5f9afae879ab5feefe93fa9ee6566f7bbee6bf67d426d75cfb2bace9344fabf72bd58e999b76b3,0x9300010000091004000400382060802420900110020801010208161810541520000000800198110400c004084880812115000049028020c0800220200009220a01801050108206a8408406120184808104430800802442850101410609083421),(0xd3aee9d1a16b8afb579b1b1a2ede96c634714fced4ed35afb8d86696aabedb2eada373270f48f3a9b93de8a90d87d8f6684756adef8eb40bf672fc78b9342c9c7aaa652b2aec9422dd38b32b2a5255bdcc3d35b2da5f372953f3c4ba3a70d996,0x2c07b23e74020fd2aa41748155856818d263d681015680dac92709c7448b08586eaf3a512642c64b613a9091954b38c222671d26711d023332d48951dd0691952839212f8b6888039910b9ac2a42653c283c65315b1b95185ae084b83270c996),(0,0),(0x759a506bc07865de6f37bc2fabe39a5e2705b6a3eec6bd3cca572e3ed72f0325f632aa43d8e0e833eaeab6f86ad5fa72dbaf9c83b9e70faa212acf122e177ae733d8fa39a0b0bb12b7915f7134c3b9a9ed98d75362b1d9c725676c3caf04637c,0x16e5f59c6d01a255c44806523c0cddb5529a2196d082e7c24415d298c0f10d071e6090549dc090f8ed501938009f3fb2169588d90b0b506d102e01343cb84ad135f45369a498be0a36011e712702bb816af81651c4b05c0701a6642cad046374),(0x6339c3e76f77dc41ec6c9766b8b0f93592cd6e58a17db2abb9eea5cd269eeae2dc2c1c9ec755bae6a2821f6b678c3538a75edaf56c57e97ff4e8b90d55c4e75ce36b37ac511be4c610c6f229b9ab77956345b3a117ef6f3608dd37697870ba61,0x84ef690f5888a6bc0049f9381c0ba0115db000874a075d2102333605e754184fe100105f739880fb92c019ec481f2d2102dbf2480954a0ad3f922114724920d57f80032e5018c6a22083e62199863ec06b43378157e41d3d00d937293850b261),(0xd5cc96ab2735f4eedbcfece9fd4d847149d75b8aa71ff3959066dc7566c66ecb75975abde9bb8d684d89311f3151135dd1ce4d97acd9737d0b4d97b62b1596cf57b51ab1b6b408593b67d5bb928b32dabad66fc43367241aeaae177095e247ea,0x481560b0cd924918c5323d4303992d88d1232e6a49f254a2454320824e8122936522ef3572424e688310332525616c12e023da92a435d213539c9243b254cc21b63548a8e4258841b361f1c95a017252ba1c47902bc1245a7a8e167094e243ca),(0,0),(0,0)]
def g119columns : IndexTree ColumnInfo := (itLeaf [(4,0,115,0,5)])
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
def g189columns : IndexTree ColumnInfo := (itFork 4 (itLeaf [(1,0,188,0,5),(12,0,177,0,4),(16,0,173,0,5),(17,0,172,0,4)]) (itLeaf [(24,0,165,0,4),(33,0,156,0,4),(132,0,57,0,4),(160,0,29,0,4)]))
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
def g127columns : IndexTree ColumnInfo := (itLeaf [(32,0,95,0,8)])
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
def g191columns : IndexTree ColumnInfo := (itFork 19 (itFork 9 (itFork 4 (itLeaf [(1,0,190,0,7),(2,0,189,0,8),(3,0,188,0,5),(4,0,187,0,7)]) (itFork 2 (itLeaf [(6,0,185,0,5),(8,0,183,0,8)]) (itLeaf [(0,8,163,20,6),(10,0,181,0,5),(12,0,179,0,5)]))) (itFork 5 (itFork 2 (itLeaf [(4,8,163,16,5),(14,0,177,0,4)]) (itLeaf [(16,0,175,0,8),(0,16,166,9,6),(1,16,166,8,5)])) (itFork 2 (itLeaf [(19,0,172,0,4),(24,0,167,0,7)]) (itLeaf [(16,8,163,4,5),(8,16,166,1,5),(25,0,166,0,4)])))) (itFork 9 (itFork 4 (itLeaf [(9,16,166,0,4),(20,8,163,0,4),(32,0,159,0,8),(1,32,30,128,5)]) (itFork 2 (itLeaf [(35,0,156,0,4),(40,0,151,0,5)]) (itLeaf [(48,0,143,0,5),(56,0,135,0,4),(128,0,63,0,8)]))) (itFork 5 (itFork 2 (itLeaf [(130,0,61,0,5),(4,128,27,32,5)]) (itLeaf [(136,0,55,0,5),(160,0,31,0,7),(128,32,30,1,5)])) (itFork 2 (itLeaf [(32,128,27,4,5),(161,0,30,0,4)]) (itLeaf [(129,32,30,0,4),(164,0,27,0,4),(36,128,27,0,4)])))))
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
def g251columns : IndexTree ColumnInfo := (itLeaf [(8,0,243,0,7)])
def g251autos : Array (List Nat) := #[[],[84,115],[99,65],[118,84,115,65],[118,81],[118,84,99,81]]
def g251levels : Nat → Packing
  | _ => emptyPacking
def g251index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g251 : Forest := ⟨251,7,fun j => g251samples[j]?.getD (0,0),g251columns,g251autos,g251levels,g251index⟩
def g255samples : Array (Bits × Bits) := #[(0x9b665c544a8481c32c829a3849d25a0c2e734bceaece0410b1910c9246b692285657c973ca335d593cb00f0546b90059eb43e97a932728851785431870f031165ac8b80393ba6e576270cc58c906b870841734e15dc89803598ab05c2460a6b1,0x104454110880808228020a2041d8002c08600a02808c02009111060244ac12008614a1024802115108904700443200508241c8821224200116051018407029164080a01212302c0942400010c90428108414142154888803090a9048202086a0),(0xf315668af28fdb1ca228365b7ccc05a0011317731e21482f697635c521d4e57b4580944cacd08190116899ef79421d834fcee4e488905930903982805fb1c61927af17aaf49049a676974192f0d0160363a1bd03830701b0dc1f8281c2dc6123,0x83112a82400c43108201140b24040542001210600e014836084820c40800442b4181104024900000902098cc210099010006246088901220003082011981800902040620cc814002101041843090160043212902810201b054050081825c2101),(0x380526282fa13ac851f4c9c505254980d6e8ec3804b3594a769d93b950ebc251b0d8e2a15610b8154799066089743516386914b45de9a6e1e91c2d64aa4bec2945782990b2d68e61aa4d3cd1b24a6ab680984b4c1298da14a63264e421a50a46,0x184000082381184051a442400021c800c760240c008201086414493150c8805030586481420228050588002082640402084818905528808149002d00020c144045280184104604602a043c40824a60b20098024012185a048212646400810a02),(0x96903da21572f2b1f1c959078994a771bc47364121282ac5966e24786e0f6b8886ae49c27124b27b7242ff2e0094e0b4b1b582696d3c94568c371a6b03b30075a8d6353ad9672c0089eb12ba6325f80dd24d451b8459a7c113618d0b812f118c,0x86100cb01034a2a12848198388d4226018030240202c8a411a0a044824066a838a240842212092185a40cf0a0080e094a530c6680a1400448645526011312024a0c7343889210800016b021a61259805924545098441a1c11120810b812e1184),(0xca830c6ee5a1c1ac77b2c4bb013b84b271c7189edce77b42164b82b2ec44ccc2202552493f52e619512b4f09e2177ba801c291327039cbf4fba1fd7ca29d36ceca40c4508827295a1b45be11b7c00687be220f65622167c80c13fe90c415919,0x1282044674a181cc515204830038803270c71014e5265b22464b9241a4004482002443590d10ca0850630203a411b2a000c201185038c3861ba0d078200d6480c204804048212d4a89449e11258006869a220d60222163c80c12ea00c414819),(0xadcb89db333a54791fc5b16de6a74b1fbdaa5224c4caa060c8434905e130b3e50875189fa3aee40ebf67487ce98db2673644923b555505294552488c144494c2312ef3656d2d51ee39b1b44e04f3d3ec4d148000ab72771f011403179f478e82,0xa991884a13221d3803c5e045a0014312e78660240442614040424905201081f109410899826ca6043646807ca808b20b342020284941850001124c8410049440302c118d6904416438b533460072d3ec490080008b50771c0014031517470802),(0xccf1d170b069949f14600d7679a83ea985e068495997ad010287ff4ea745b576050c4fa9e8e0fabd2497448bd27a5aa8acea4ac0268e4d44dc2df9de452a225ad1457b3d721818b9bf9e05034d50ecb938aed67098a522a72856072e55b8d214,0xce85130b040942f1560095449a91aad8dc0e80b5196a18140955b282345b194266c47298868eeb9221d4601c27a00e8acf04a8036004c04cc8c58ecc43a23d68161791d311c0cb9abcc24434d40e8b9388ed67018a522072852072e55a0d214),(0x442aa5b9d884c622461c21eaaaf556fac8da8923687abbfb99c9c28096422e0eb83cb34c1d8918aec8c55d99f53bc2670104934ee2f27258616b2c55a56fa8970e02486406e9b92b5242282d15890d903f02672424a3e96d3ce1d022fa0aa8e8,0x460a679588446000a40a01aa08c414e80818810338389a92898982c08602320ec02091061180118a88016c815113416481048146a2821250206d8051a4632a958802cc600689381b004a400915810c003602652424a380613ce19002e808a0e8),(0,0)]
def g255columns : IndexTree ColumnInfo := (itLeaf [(64,0,191,0,11)])
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
def g383columns : IndexTree ColumnInfo := (itFork 29 (itFork 14 (itFork 7 (itFork 3 (itLeaf [(1,0,382,0,9),(0,1,332,50,7),(2,0,381,0,9)]) (itLeaf [(0,2,312,69,7),(3,0,380,0,6),(2,1,332,48,6),(1,2,312,68,6)])) (itFork 3 (itLeaf [(4,0,379,0,11),(5,0,378,0,7),(7,0,376,0,5)]) (itLeaf [(5,2,312,64,5),(8,0,375,0,9),(0,8,99,276,7),(12,0,371,0,8)]))) (itFork 7 (itFork 3 (itLeaf [(13,0,354,0,4),(14,0,369,0,5),(16,0,367,0,11)]) (itLeaf [(17,0,366,0,8),(18,0,365,0,7),(19,0,364,0,5),(18,1,332,32,5)])) (itFork 4 (itLeaf [(24,0,359,0,8),(25,0,358,0,5),(28,0,355,0,7),(20,8,99,256,5)]) (itLeaf [(32,0,351,0,11),(33,0,350,0,8),(32,1,332,18,6),(35,0,348,0,5)])))) (itFork 15 (itFork 7 (itFork 3 (itLeaf [(34,1,332,16,5),(44,0,339,0,5),(49,0,334,0,7)]) (itLeaf [(48,1,332,2,5),(33,16,326,8,5),(56,0,327,0,5),(64,0,319,0,11)])) (itFork 4 (itLeaf [(65,0,318,0,7),(66,0,317,0,8),(67,0,316,0,5),(65,2,312,4,5)]) (itLeaf [(70,0,313,0,7),(34,64,29,256,5),(256,0,127,0,9),(0,256,23,104,7)]))) (itFork 7 (itFork 3 (itLeaf [(264,0,119,0,6),(256,8,99,20,6),(8,256,23,96,6)]) (itLeaf [(268,0,115,0,5),(260,8,99,16,5),(280,0,103,0,5),(272,8,99,4,5)])) (itFork 4 (itLeaf [(288,0,95,0,8),(289,0,94,0,5),(40,256,23,64,5),(304,0,79,0,5)]) (itLeaf [(320,0,63,0,8),(322,0,61,0,5),(258,64,61,0,5),(352,0,31,0,7)])))))
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
def deadcolumns : IndexTree ColumnInfo := (itFork 63 (itFork 31 (itFork 15 (itFork 7 (itFork 3 (itLeaf [(1,0,510,0,12),(0,1,460,50,8),(2,0,509,0,12)]) (itLeaf [(0,2,440,69,8),(3,0,508,0,9),(2,1,460,48,7),(4,0,507,0,12)])) (itFork 4 (itLeaf [(0,4,369,138,8),(5,0,506,0,8),(6,0,505,0,9),(4,2,440,65,7)]) (itLeaf [(2,4,369,136,7),(7,0,504,0,7),(5,2,440,64,6),(8,0,503,0,12)]))) (itFork 8 (itFork 4 (itLeaf [(0,8,227,276,8),(9,0,486,0,8),(10,0,501,0,8),(12,0,499,0,9)]) (itLeaf [(8,4,369,130,7),(4,8,227,272,7),(14,0,497,0,7),(10,4,369,128,6)])) (itFork 4 (itLeaf [(15,0,480,0,4),(16,0,495,0,13),(0,16,486,9,10),(17,0,494,0,11)]) (itLeaf [(16,1,460,34,7),(19,0,492,0,8),(16,4,353,138,7),(21,0,490,0,7)])))) (itFork 16 (itFork 8 (itFork 4 (itLeaf [(21,2,424,64,5),(24,0,487,0,11),(8,16,486,1,9),(25,0,486,0,8)]) (itLeaf [(9,16,486,0,8),(27,0,484,0,5),(11,16,484,0,5),(24,4,353,130,6)])) (itFork 4 (itLeaf [(29,0,482,0,5),(26,4,353,128,5),(32,0,479,0,12),(0,32,94,385,8)]) (itLeaf [(32,1,460,18,7),(1,32,94,384,7),(35,0,476,0,7),(34,1,460,16,6)]))) (itFork 8 (itFork 4 (itLeaf [(36,0,347,0,8),(39,0,344,0,4),(40,0,471,0,8),(49,0,462,0,8)]) (itLeaf [(48,1,460,2,6),(50,1,460,0,5),(56,0,455,0,7),(64,0,447,0,13)])) (itFork 4 (itLeaf [(0,64,189,258,10),(66,0,445,0,11),(2,64,189,256,9),(67,0,444,0,8)]) (itLeaf [(66,1,396,48,6),(70,0,441,0,8),(69,2,440,0,5),(74,0,437,0,7)]))))) (itFork 31 (itFork 15 (itFork 7 (itFork 3 (itLeaf [(74,4,305,128,5),(80,0,431,0,11),(83,0,428,0,7)]) (itLeaf [(96,0,415,0,9),(96,1,396,18,6),(98,1,396,16,5),(128,0,383,0,13)])) (itFork 4 (itLeaf [(128,1,332,50,7),(3,128,344,36,6),(132,0,379,0,11),(4,128,347,32,9)]) (itLeaf [(133,0,378,0,7),(134,0,377,0,8),(132,2,312,65,6),(133,2,312,64,5)]))) (itFork 8 (itFork 4 (itLeaf [(136,0,375,0,9),(128,8,99,276,7),(140,0,371,0,8),(132,8,99,272,6)]) (itLeaf [(138,4,369,0,5),(144,0,367,0,11),(152,4,353,2,5),(160,0,351,0,11)])) (itFork 4 (itLeaf [(160,1,332,18,6),(162,1,332,16,5),(164,0,347,0,8),(36,128,347,0,8)]) (itLeaf [(172,0,339,0,5),(176,1,332,2,5),(180,0,331,0,5),(192,0,319,0,11)])))) (itFork 16 (itFork 8 (itFork 4 (itLeaf [(198,0,313,0,7),(256,0,255,0,12),(258,0,189,0,8),(260,0,251,0,8)]) (itLeaf [(264,0,247,0,9),(256,8,227,20,7),(8,256,151,96,7),(268,0,243,0,7)])) (itFork 4 (itLeaf [(260,8,227,16,6),(273,0,238,0,7),(280,0,231,0,8),(276,8,227,0,5)]) (itLeaf [(288,0,223,0,9),(256,32,94,129,7),(32,256,151,72,7),(257,32,94,128,6)]))) (itFork 8 (itFork 4 (itLeaf [(296,0,215,0,7),(40,256,151,64,6),(304,0,207,0,6),(288,16,198,9,6)]) (itLeaf [(273,32,78,128,5),(56,256,135,64,5),(320,0,191,0,11),(256,64,189,2,9)])) (itFork 4 (itLeaf [(322,0,189,0,8),(258,64,189,0,8),(324,0,187,0,7),(324,8,163,16,5)]) (itLeaf [(321,32,30,128,5),(388,8,99,16,5),(168,256,23,64,5),(224,256,23,8,5)]))))))
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

def hashf3863l13 (i : Nat) : Nat := 0x107b00c80000000104770daa094c181892708a201601f086180cf61bfc42f82c60f060274473872c0d763a3c74900bd00422c20120000e0d22100000000000ad217d824800000004020815b01ed0b8000203be01f0000a03d047d0e40000000000008188128e0a54098000509601618548000000000018084897f1e1a0b7c31083d604ec0cd01c301b601aa18c0003800a01d818000058a8d088a031811b06e0000000000000000000614600d000071ca0000000187a815a015c000403f0000000240bc0410000e16c02300001155016a875b870615d20ee01d582891d4a13f42638520000e164c0e184a400cc0d7c29e8042123a0500000865b02c000000068314064000241e787300d9e178000705db09be10bc3b603600eae04985580000001015400068ec5068a1d1808800040e36121835504e004c0001052401d0001201e83c800020a0c02800028210000000202180000001c05401c800040a9000c0004068a045e25b8008820e06e0000000702e8055a066c17c06603000409010c01000006000504000001050b1c37011400020005040000000c030200000109040000000111012601060205
def hashf3863l12 (i : Nat) : Nat := (if i<3 then (if i<1 then 0x443b4032e215ce612e800002057100001606a80000000000000000000000000000e028a016d80000280580000000003c03b88de200000015ec000058d7c0000000002c06a389d06011b4031e409b08915610a0c08d70024485ec709f72073880c9705da0000000003c15f7025700100302700800400000000300100100000300a03c00204300201700100000e01400000a01e00000900f00700100600300300000400700100601200000500c01800100000200200001600700003202200200600100000000200900500300300000300000000100001800b00200400e00e00f00001c00000500100000000101a04200200000103100003800800600100000b01000200100300500500000300000000100001400000100f00100200600000000600100400a00200a00100400b00f00400200200300001000000000500300901100800e00303400000100000300400404100700300100000400000000200400201200200300000000000700f00600700200100000200000500600300000200000800000000100000200300b00001b01500300200001300100000200501000000300400300500400400100100000100001002400400200200000101300400100300100900500300000000200900700000000100000300200700401e00300f00100002500100000000000100000900100401200801a00400100b00200200800500300500a00100400400400000100000100000200000501800900100900d00400a00001200300300000a00000100001801900400400000000b01200000000c01000202402a00a00100100303200102200900000f00102c00000501900a00201400202f00200500400001700000e00e00500302000700100200000002000001701001200601800200700a00400000b00000000500200200000100400100000102400100000000103900600400100600001902a00200800900600800000800c00000100100b00100900800000502e00100400800800400000100000200600f00300002000100000000a00100a00900e00d00200800400001a00100a00500000400902600200100000300100000000200f00e00e00a00100002800900001300500100600302200400202500100001900600500801c00200900700100000c00000a01701200400100a00400200000100000500001100b00f00300000901f00100402201800300100300201601400400100600500801f00900002200000100500601c00000100000600000000300200700d01900500400500100100000400300000501f00f00100c00400400901300200000400200001c00005501e00001400100000000000100b00500800a00400000100201000001100000801c01800a00100700000000101600000400a00600b00000801500100700900d00300c00200000500100a013 else (if i<2 then 0x400f1a03ea80711414470508c029720985c03c58570212b5e16d1851bb0328602e0c0e28042c4009d7019bc06050029882d91028cc009c8024f0ae660acda0d7b818a80179f02f10269d0163101c92022ee13ea803ea0201e09a1201af0602285ee303c660a1542b628959b0a9ec114e80de6860310000a14c24124d85e6f054fe27d80227d043230a47a34ac008d209c560879e13a0026cb0d3e107ce2074781b760144508f9271c702d4e04e0d02fee062e818d383ed70b9da0cf201a0000ed70464428f7827270cfc205ebe102f01b8e85d6f07d360eb5c170302828007b402ac407ef0e0140279414170048c012dc04bac17280000301e200069a15f082558000000001a1662c01b00000f082e000000000485253035600d7341815028a0000020a1c46acc035880b1860547804a782dc00001ae74800006058200000617ee81f2000004023e0000141c00031600001c02dc00004019ee0062a018fc0c4f80ac015c021036c45440321001bf22baec025b007fa020c00d0a8065503a2e0781a08da58e88050d000000000182a2a08955097c0000000000097d002de0000181a1b846900001e0d1f82240053100001010200000285b55085de04f7c2a1101f2d05820000000003841ca00194056902d2e03c950222c0bae0109a80d9d12a280e5ec23cd045880602a082200bf681a9e068340bed421ed84a240038406b300c7c04b6d01a5a04b380dc804a8209bda14090060484a5917bc4f27400003206ea03baa03fd4104a03ca712e9e11d3443ca054c4198860af442f54848cc0bf5603a6022d9038e00000e15d202cd20241c07a121638829230407d0762000000215c800ab09412171940421833321028c091902386890a1018aa31610145e02e7e09554075490803832900000000000000583f41026f60af000000848b4021f634c7412c409c6000004113342aa8000091005815f484c61846f20149217cc0000204453038400003810cf82ca9056de0aef00333024e702a60000080f790199d007e00067c0cda89ed3034f20ddcc278202f0a0365834dec0b4205c1302bfe070e01f2b81b1504a6e17d1c2de800009042c402f60232d00b9707e34174c4189e81ba303cc8084882bc50262a085160155c256f82b7706e9e263c01b91012e0000060f490114402422077de13fe40b090995a059c3117bc012230ab90aa6a146800002861190978e1459812e602c0d0a91e0c40000020324000016158c0000000005000f40c9b01730801e0000000003c13ce80e400001810c4c0dd80000200cb40e43c26c4009c0000061425026a000000000000000000000000b073402209c29fd016b5032a000034586a83d10000041484000030b13b0a6d40e4fc282280dd2080ba337c0000000000000000c88000000000a0984210840000603ba3069c01753 else 0xbc09ef4014942d370475e009b20d9846835896880b42e046c403b20252303be0044b4693839d1105e6405f6822000000d0bb941473c28f684f49196d201c802dc1004a909948001301f780000a04cda0cc800002000370825e12370132d044aa035b42261049028131a0be58c41b80e4585aed002f6245a0198a0188904d88068c000070384d083ac05b480f9a04399091520c9700ab6022a1114de22c5409f00000801ee00002050b18143f16e280058841298d2c913520000100aec83f9005db605db426268028200886021702b3c0399b07e4e17bc826bc80ee000006039c00003852bc1640605c800002030640a88e0be484f7483570000003821c263a81f091a7000000000068519713a40000081160027e9011e61189c041000008015000002424cb802e000000000000000000060baa000018236780c60000000002c1bc2034c00000000008267c0096000000000380ef583cce05492137c0000782d30063e00000000000000c036000001012f78be9c0533a1796014af059740ac120ec0424d380b8c0b0bc09b580ad902efc093ce0c3602107825900961402da40da3038fa15c600000000038a43701f1615ce84b5800007080d807e800004837600000012df01055819f8082ba10e180c1080620067262c5241ac8002b401762016c00003833a00000015654300583c7908bc812d204b6084272035e000018211800000000060cb0000038b64b00f8c0b370140285af9024400d3d0254f0197c01df6013f04ec98d1ad09c6816c4803ac83a7b0457415fe04d07849ba0417607d0c17938263403b9e06304285a055760028013b280a95010de028f8042f04dd4818a50b60416f8016c585f86136c6348f819a48126207af22202420800000904e0c15b800000000000001814bd01dda0a0e209faa14d6c2442846a101e0000004228b8459106f4000000000481b8d020b014ee0510a85c400001c167b46814047b30b9300602e23000000c144be0a8c815f8048000001436760637800004054a0000102124038d601f9c0cbfc090f0500a0560a0cff819680000b0a80403c982a1b01bd715b3a2c0200c200000c0b29209dbc02610217d110a000000000000006024a00001818d9820000000000034023d84190091c00001007600000c0a83208fc0000182d7e0449805d240a68000000000e279000000000000001a064f051180000a0719c0b7ec1e7800000000000001c0d000000e88ba000000000380ad415dec06940000605a3f04f000000804af0c9750ade0000102915855f00000a0d13c1f8381e1b0440815524570c855e0000000002c05d3012770640010a8000000000f0307e167dc0e2f01d2c0630000030081503a3e0ba442f1400006809000000000000000680ae008a5e2b7ec168e0155e083120da806dcc036db01ecc11828034)) else (if i<5 then (if i<4 then 0x6be006dd5b70035570a8c034d00000003fe501850089d81800000000001004800000000003090e2517782cb2883181406a0b9705e9a84e5202af00a41013018225e01a16023b804c6829dc016200003807d801ff9023240b58c2f1d85d70a6ec60d59406d88268207cce347ec017800006033ac0401c094a8d3251298c07c50265a83467050700b77c1766802a105f00000200c298307000000000000003837df06a521764000000000e0bf2c07040000603f8d0771e14dc0068c858a8093b40a8000004835a00001c003800000000040ab74183d0089985cc0000000000820480000000014056242c4800000000120c3800001856180818000000000684da80882c26634127903c6100f54057183027833b60446a26c7c4fcc0552a07b622c7e814d002b900000223a844d98803e5015e00000c1256033dd084de3454458288a36e007501260426730d16802140000302ff8000000000c068841e0b02ded1ab1007d9410c78972d0b11a10a7825f80000b01000052802d42801350b320000302f2784dc90702c08b80000304a6c0072000000237480c800000000000000101fe000000000281d098c590027600002c10d581c650321e06ffc1cec852d3023d40e2f015c78996808d04124042a3a03dc3040ea161b007170367d13d120f1240aa785db003b780898014c282f650c128349802179841aa0512826958260f89663017e605dc0000601b5003c1c375380acc8b06d080000001c201000003134882d3e41bfd8141c08da4143a81de2837040b1f090ac0000583c2004074028c000000000e079a000030450784f6001d7c043b828330a3f407b00000240b898071a009c42900c44ff83a810395221fb00a06840e00001c0b100000585df50461e0d1742f0e04fcc136e61603c223585390000000000000050061215d4215e4000000000603a600002850c800008092dc06db41cf18503b0bf8208cc000000000f0a2000003402f4830b0000000001c15d300a5e0152000000000689e5e0bbb80662427880000000000000040d980000707f942534406b0000000000e12e1c0d400000b034d00fb1c509f809200001207b40000581e4900446118442c26012321b7d217fb8233000009075d80c50000000000c052da15240256003d90000140bfec00090517c0ad600000000000000f0b5600a88c22b4037c000000000000000000000001e11fc00000000000000000038045b02a6a08c60000241d2f05130000000003830380000000002017f022480000a1a4800bf1c22700000b0a9dc15340000403535048be124b820b680b5b00ac20c664011f0cf160a64609d70508e8430c00796124ec4f5383e8b038ec0f74c0d20036b6001be164b41b098073c0c1d20f214099e8162c0005c16f24240d8569001c3e01a7051110d3cc060a204e7817a1095 else 0x5f1401c004e9710f68add8010e382e150a25e0d9201e9a89a800001a1830829050128f078b411e201743858bf00a0000000000184b501bce003e700cb584c520203a011b01dbe0394c1a0a813b785033b1d4400ce00491417f6030af1482000028118c03540000100f7d804600000a0aef213200000381f7e1124c033e40b0282d200001400ca45ad104ef6063c411af80eb0000000001c031000001059b00000223d4008a80000515bc8039ac4ae303f300000000000000602ea808750090300c700000605b600000000000000d0488e27ca011c90206a0b8a00000000000000e1a76033b4000068386d484c00000000000000805c60000000000000060740a138b423940132c6a69a005400003836f406a2016800000300101004b60540811f5040f61089a1819810de0267e0476220d38059903b66083cc0e600000000005082260935429e000007040a0000000dbc0436b046f21760c2fea85b9a094762745021ba02b1808ab2106e027c2099300000000000000682c7e07f700b2cc1ed000004049820b3f808b6003b28a5fa0d82024fd82abc03d2a1746c1c400000c0c1460fdad87a885688049722890000068086b0858408b604be68591b09dc400680261885eb000008029841d61859500ab4016ce400c5030900001e1693410ee05f197a692909002b14820d003f7228aa0069982ad0000000000416480000c15b9c03390097e8277c022800001c4ea9817b0000180752c2938000000000002680000402691074d21447c21100000d06fce28cc00c36053a0000000002016a7005ca09d600c484049c05507001100b88000018135907d60000342e6f00061089bc07a0c22d5829ff0bdb015aa02d6f8501504fb807e0c4b9b00f440486e10ccc11a404842113922251023be0054000000000040f2883f7d03cf60413421f084940000000001056d783d6a00a241191028eb0292101c761742816418608f16f1e2290000000000c03fb00c11844ea0020308844074000002030f107c740aa50518a85750000000000000000000612932099040b1f053e00001a0b6800005805a702f58084000951845de04b4814f50462e03967075561671c0ec5036c313100000106aa802aaa0b86008f30149d82225058a00000812a80087c094e40f0e80e6d860250a6840530c08668108a0607c1010801600000a069480225427ce841f0000080a864680f834dd0690a121706bdb84e700b02808f5045b384c960a37616884016f096220bea40a34c1f10001100913409f0851a92438c095d413304010c02fa000006030f41b99811d90a5800f2c01a4e040af03d5414a982973011000001c05cd0258f8040000008083342b2e0a2900000604e28300d8103509fc0000382e58000000000000000000105f6607256119c0000080f5d720dc117cc14bb000f506) else (if i<6 then 0x8e90800b312ebc07640000000000000080c32404f10247003f200003c1565029c0000000003c0b20005991b62a0cdc00000000080569a032c403f000000000000000000040369000000000000000000000000a0330000060486a12c8000000000000000000000000000000000000000000042c3a0593b02cbe16e8806080000000000000142e12035b202d9815b4c28a50274111d1227c1c1bc80d39901aaa0174000000000a0a7000002400900000e0ab9809c8000000000800da40b0f00ed000006073960190000000000a01d16027f023d7844b0693800003813fb83bf708a0802f10022d03fa507abc12f5804500317404e3a16dd0079904bb5076960ef602f828281d0083811c40000083380000000002c4ca60dd6101b922a64000028330a07fa203f880df203a9004ad80426807d1811c1055d016b380a45829141b9a40a7b41e708476809b7213198159ccc6ef43734147d026b00000c043c00003818438057a0bd000002410ad0b1d2096760ed54083b835d20737428d302ac104d500001427e280b37859d6000aa173d0268d00e5e13b8234834102200a1509cc0000180a1704dd10ae523528000000d071027e00001468e0000000001a01ee109be0435504f60000141d9000007161c00003c21a4888400001a0644000028d19f7156000014095f035041a66c22af02857857600335a0aa2848d302d500b644104d01b138336148476366c003a70079700c1e0ca80000283ff40802c0265c188f09e1201b0228e7012f8000060509025a6c2ef0060b704a060f800014e82e98041e40e15c178a0097b114ee020e42520000080a1f2141c0000405900000000002c107280b2d074980fa8000018d0820a2a809a8414668251b043e611f6c05f4826bb02310007fc0ca180a200001807b00000284f3c06f740abc000068391c0b7600003047740389b067c0e3d482f4c85563030e80a18000030375000002059c00006043b000006111f42e4784a1807ea00003c5840000070453c0b9382a50000000001602d0022ba058d00000201bc00003027a000018123dc0fe68aec80981e0c71c2690000000000028ac00000000000000000000000280a0317862115100f700000000000000000000000070a50203780000100b0501b40000240a4c0294000000000000001060590087e05a40306e84959084b815fb80e600000b19aae0ebc00006816e0000100aca81c38038360a31e111042f38000000000c261b827ae01a130a6780953d8e9c891850bef0080901660000000001e08bc0000580d7b04900000081f080000a0012c63cc0000205c0f008400ad400001850c00001c12bc000008327002bda00dc4168201cb00000c37d901d5c01c0000002215e41471895720704e1245001aa052640a9660d2c0000304f200001e10500000000000000120 else 0x120fb9c0ce605c7111f360d9781dcc8238d065640a6cc1377009b2080600001c30820214c0066a0d8e0216a036860939a16a8c09800000f00d4411700000709fa00000a345c00007055101a2800000000020395509724178000e780000000004038081cff808800000000000000000000000000000000040323b05840053a82dfb813400000c14a5841f7013a00000413a9413980000f08e700a3d00366031dc090562758c013402f7e09c30120e85eaf8070c0b06008e800000000000000e157682d38818da04b7a90940000783d4c003ba01b941089814fb087e0000340eb88030d0965e02040000604970000000000000000000113f600000423f00000103d703460c2698016a5099b00f79c221a835fb04de403270c76102fdb035c00003c0ba880aa00001a28a000000000000000000000000500a7607666209c02f100000801d4a15eac110b02ee90ac8000019)))
def hashf3863l11 (i : Nat) : Nat := (if i<3 then (if i<1 then 0x1fe0b6e408c3067b30391a0508826e704bf00100000300e00b00000d00100302000f00400104901700000a00000000500a00703a01800300800100000700700000000102500f00001b00002200a00001701f00000000201f00402d00200800100402d00000000400102000100101902b00800201601d02000600800d00500200401e00000601900000100d00001201000100500900501701600d00000700000000200c00300201700c00d02400a00900300600700202c00200001500a00001b01600000601700900300003600000000200802000600001800500b00601402400304200900200100000000101400600700602700000200402300800300600200000000000300800500201600e02c03900200000100000600003200502000000000900000900300105700201700200600000400001e04b01004509c00c00600102500200700f03200100502201100503900601100300200002100200000701606700000000200b08900100100000b00d00300f00202002d00401800700b00200003300000300601c00f0940aa00000401102d00201800800000904b00700201700200501b00200601700301a00d00000300000302c00800f03400300100d00a00000002600001a00304800700200300600900c00700800800000001e00d01003d05a00200100101e00001700100c00a00001501900000d01d00201800200800300000102300100b00000c03600501300d00101d00901b02f00c00000e02c00300400100100200000200200103a00000c02000501100105800000100000800e00800904f00501502500700300a00000202d03b00200000000c00403201400300500000800000a00a00602100001200d02300000001100400201500602d01700100b01200c00904200100401403300000700100302d00202b00603d00100100000300000402500003200505800006900600800500500101500000000303904902700300100000200001400200300000103400000d00000600400700705401100401102501000000100b01d04600000500101e00000004000000304901400d00000100700000500f00600001500600002b00003b01100701904701200000002601100b00002502b00202a00401a00500600304b00501500000200901802100202000000200b03701500801100000501a00004502700701300000000c00000601602400100300200000100000900000400f01501100400000300b00200605700001704602604000100100300201900000200802601800d00000a00000d00900000000000400000000600100500100600f00300e00100901000703700102f00301d00702600100800102900003f00000000200300101c00200900300903a01c00f00400901000b00000001301500100201100000f00800000502a00100d00e000001005 else (if i<2 then 0x30b0085d05c2000002ce4c000000000d3c00e09ac40c7000000000042d6fc06a600cba0bac000000000600168043e20d8481b9b046a003e66394fc22e000000000000000000000000b0142a0f94025bb002b100ac0000000006821190697617ccc0626040c4040640c96030628384b0694025ce06bb2055e60934c0d7ac662d066950c7022d0158488021b109fac235800005824430593622a6c283c888180b87a0c7f8106884ba00289e6e490234f81e0008bb806eac0abd38618002e2cfd2413d4009310099e0f7247326017de77d42043b41ff724adb03a6610b91247908d2a061d6121a442408646805848314a8148a05b980bd4012bfc124a0b89d02504220e670068d2b5087ec20a2028e401cff0c47411eb414700000406baa37db42d4a809051ccd804519831505b400000a14e8c2fa704bd0193560c1601d0984f1b030880111c442b0444c05bd80cdec1286817320866000c8011310297e07f1603a0c093d3bed00483c09a14001a05ced03f880182c1b52cc08a1111e249105b220350e08d1405f1c06450166c06fc8012ec293701af0000002552811df818f00000e19c94284b031900001e330b0271f05b260c59e168941b918059f0beba204702ad70c88b0a64a2035431ba84268089d8006e80c298609f186400000414180000203a000aa8012b50585d0b3a00000000000000905b1e03a9400108427f091700999071a8800ff06f00000305e1d04cdf042ce076542a928368d0018418c0000048813b0165c0b7c01bfc8367f0c4ae01c4c1f7d853cf08466322bc2c568253f08f6011f40039c0467793d800002c11cd8024e0672c20740000403af20bc560e448000f8617c10560000000006045070b34800d000000000000000403d4c1b80881050208000000000500e2a062a80a2482b5f00a2802014d018c1a3ece01101da2058d02d3105ad6119000000000010121e042460b9fc20d4029881abf013a5c2a3e053d6024180ff581e790817e0b90e0efb82fd703353058da17e242a168195306b2a1536c20ef02b55088d0112c8243a81f2202c2a0a654310f08382033d8254c85ea984b5010cda377341ac0015e807bf2153c0232705be98994000034014f8aa1107ef016840000283ca203a240498c29cf85df201ef00946810b885a340befe0f0a81195039d00b26a0af80000785ae00000e391ac33000000c02812106c0000780df00001e14b540a560b53a0112803c441a0f82240000000002824f2256a818a600003855000000c060ca19bc0000504880000140c618122c02159101e0077fc29270523e085a60fd2c19168c63103d300d01c15be2539b037320d9002db68ab060bd26040f81a8881cce007e608b44066580a0908ab011998314f0c3fa1061213b581c520182b4907c0af400e248334f015ee0861400c6864a106 else 0xac382251081c407580000383b7801fa00003440f3858420027810d7416d10095b0747205d7c1db104417112a00003817d000009017ee061d4178f83e4b691e6017b42d270481404eb6131ac17e702023035b60f8fc110c80fa4044e00c9c01c7e8d68216e6e0c6a833aa00feb058a60521066c3029370b4ec19fac1bdb051e60bb10036e00a1b813e50ba1606ed005c60517d06b7cd01f982f08619f034a2150583077863a61356c0408c0ab704e7c04fe00001c2b3e04ca20967a03ac000020369c006c000034059a067d00000204b0000048ddb6110540a3400006859ed04398125581e5d0303810d8e0efec0d300000000018064f85f3f44d6209dc405a1c0cf84e0c70b10211f8c2b77846b50864292bd44baf00e7889b8e20ddc0f15045a007f3c07280276184b6618d5604f102b4a84d0b0139a2559019d38400d05e14097c41bee81a4b064ce14de81c5985c440cd04081f408be83c110690c39634114f82a9b059da15d2c272f8b88108a20068ac0e75082aa15f992e4a00178044300bc8c18adc27aa0081b15b44139b002a185e59081ba114d815340023f0724f1356419f7843e6078e431dc40c668e04c021e40ca2c0ee281886075082ce082ca2830ab080f60e9dc013b03c9a03512924180a5d03ba30c63a0f800661a8591304ec8083c4557b0151903eb803ff85513085c8180c2369c426469be0f09d44024784515a45f4083c2209f859880171906df2197ec22958042f0909004bb8335c80a85091960e91441980021000000154402b2800b1c07444067200c0e006ae0afc6030800000000010c720000000006013b089b1e0c82c2050000000001207ad00e4c820400a5f0059fc12a000004015a6177000002058600000000004223b85f1505ba00000c26480000e09240000300a3a8561e042920a7c420980000102f361066c2f30000090a040000180ba482610000000c42872f50072f16a48165681f5402d5b0aa80000200aee02a7b04df00c5800a668113a0bafa012a42f6a02ca0000100ed1826a2837af09012141b83290000000000e08e000001815b003e9a0eb1c03bd85f0b0c34000038287f033d007e58217781708000000bd86009700e1d0428a051400399c27fa803ac05f760343c1e8901b86091ec08c440459063e800a5c186c833ca00a540b8160b4682b2782f360bbc816df4011714def010fc0875af12c0189d047ee02a5c15dd0590c01ad0083205b2c0abb50bdd20a57428281c71f0582415eb4326f029e6133b017f542c0c8395b035660caf028b5b060b07b30019ec29b188b170678806a5c690a848d30ac7a029c023e0858b30c9e000024314603dd401a261286c00a8027910686007ab5211382a191553c12c6412dc806b907b0a16bd013980662308e0a106182a64066d00001c335000007027860080e1)) else (if i<5 then (if i<4 then 0x1919025700f50814900000a01b2e171400003051bf069c5724f432600000d07338306f440ad8540c1ba8e117800003022bd074a0000042bcc066e607558167c012f082a3e013241950000050331e0434402500000000000000141914c23638286f026da08eb02c90000020b9e60fb400000000040842604dc80996810d405dfc17800000684f7e08564178d82b3505bba0ca3a0787843f7bc0930a2082066043068045203b12207c0000704d300000c2d65401ce0222e0ae463305c0239051f006ac81705431a80000503844082dc6cfd8309501c22076fc22fd83da207f9c0fdb80bf23b8730560e160e005850965f0ad8c19eb40e5a80b7d0772a1844000000000e0907a019641ae104db600b6894d9c416100c3602b9a1848c17f280c5006ee830e782aab81fe60a29617a08002d02c760571492b000f72006e202ec20b64c10018c80f0a53c1745426a80000c058000003432ce044ac07fe82aa00000082a8e492a008cdc09ec855f510470184c0000101d7f1bbcc06c78259784f400001c2b5400006834900001020d242f5d895d20347e01e01e4cc856f0107700a5b057350344c0952010f000000824080b2e00003c23bf00356155740e048329b0265c0c0060eee00678000040b040190c009568371e03fa0000000002830230cf081096c0a33819771ac7616aa455f18475000000000300091058f80639c10a480da204cfd02d5a14b982bd803e8200a340abc830a483d0703c8a535bc29a6862671160e0666c21ce85f6c06e820bb7015e28627b0b7fa11db801bc03b350282292abc26ce8bc2d07652032a129d802c450a44231a4042c781c54092e40588c031b8020d0a30e1041418bb801a90adac192e8623b82dc2157b21920818ef02cb801c961694433b98234004cec01c0984a68607602ff800f18279988af00000602120152e00ba8018ce035e808ec009a00001a088e82bc10110d098bc0ebb8a6ab044880c5d6395c529bc0556f00e96129381a780ab30492460143c0360038c701b9a13fbc2d84053f90a61e0a130557600b6002e4e222780473855940378601e9c261c0333300d060a048045183de203ee805a582dd4b3774086280fa5833518033005c740542c13a402641183ac133182861820ed03c780f0f029d8036d205e4e03c902e5d0957a04da2128d0052100bd0000163913024a000000000000001c30510640e0625a03b100b7800008045000000c07a0008d00000203cc00006860400000000035a48f8260b06520000382215830bc013cc0e380000484eff01f20123a80bd50355205eb01072c1f84249300000a0423c11bf01efd0ae6203c20142c832c00000e221b41a36032ad107ee231ac2cd8030d20274a0676c28ac0545000008082700a490445a15a4c0b5fc5ebe002a407c200001830f283e2704872133b4 else 0xc0169c0fb8010cc0618e0b6a6090801fd6086ff010600001226e98465b1ae14115c000068473b156ee2327c01c482fda0125002b800cb3867c09c13a171e0024785198059000f37826380000e06be8039400aad852b4057e20d4ac08d501c6f0a22e030040d50000030104a29e241f5b08d4104d86137400005885a306ca000038251783dba09a529212424eb841700000c0a00426be033800aee00c79009c4b3f700000c0e01c03300000c02e000001c468e830c00a54009f0c0e6a001c00000c096142bf85ca8f0760000006701000000000161017c5aa800ce0071a4115282be6813ff091341186c0f3708d7307e3c036a82268828b71ba54132fc2374806400000009ca431210396e0ce12102e0665284eb8014de0cff81cde0139f05dde0a3dc2d5c01b3e0402407780215080800029f806808069784127114f20c4cc26b20664504540028e41919824be07cf20f110e39500d3f093e8054b44400044fc068bc15f507365801fb037d02b82c5d5f889c2079d60f4fc018281ed906c12103e811f3a62583c18a0ada821055ba4d011e60cc0c17ff003d0024ba0817c2453024c50bb2602580558d0485f05656027780b040649205ad6045b42e4804a8908c420e9b002300019302bee0be18020d8049a098260356c0431043d80caa406c982ccfa49190c45e01844070202e6603cb806c2c0ded818bb0528a14b0400e834051095aa0db20286a816be00ede39818320f015a409c2e0ae802de7063c90941e084c41baa834c00001ec1868287304d8b0649800fa408339e0100001009aac6e2905cc706f200036418a60d29b0b31023814230302a0a0119a0637421780000609f7e3630000018ab400000e07e10208802713381120be6c55c18194b06f800002012680000d495280e8000007060170aae60ad1c5de80000f04aa000010077583870000000000c176683074961ce171800005042c300d3203f0c24808e7b10ab18001341668000000000406d7821dd027d71b7d8180e41678000060012a05ecc20478ca8b11a0a151801a11846d00000e066101dc505d440ccf4107e80044a48970cb80046c01484025d0000000000c5db8000030ca1e022000004066ca00f6820b79df2b8491d04c7e1092825800000907aca3735c188c0463b004c0206a0238900980000180f5c01e478544d02a6e07fd42a4903c560020410d000004813536809a0444000028336a00bf80a21c2bb2016c6097800000819088674d065e8199ac1682018ac0726a064881753036250136c06fc00001039a604a42362000006863d80ba400000d251c84dad1c4de0828840b0881cf1aa5613a180ea20422603f76126c0000204e00000000001c0b272494902b3001fa81664ce0a206d66000081d4d88049108e000b781aa700dd00000203a5c0e090014e0c9d0eb7c42a70) else (if i<6 then 0x1804cec180b003bf0cc74041e00fce0456868a04152d828d30129e082de09230f03c8647e0b2c8138982c6f058ed0244e002880ed088a56000f814f84103483f5905c8802f282fd80c790070cc07a1024cd887f60c05a0bde42559828730c17003e201e9585d5f0636e08c20463d33e7c06a7c13d9c62ee012f80549811c886d550262e09f3839bac2a548503700fe40ba5421b002206689be0a33c56788236607302335ac0f60000e609760027e9e03903c6205874386c0559582f6c105220470055e504f0a005182c8fc2b898d8574956a0fcec332c099f000a62325982a180000d0955a234ec2eef865a7003d8535380ee904fc30c54000025849f305d7194ce18fc00000000050420421f38066f051d9097cc02d4c30300000b0022413e08156105b380778000008180680fb408f1613780000604f23673160361030780000407280000000000000090720411d241b33805500972409f9032f0000021547e066901c18004d900f200000000010538815a9c0f314123905508030cc06bac16990634306ae226b041fd80000a0cfe4157141cf50409112abc01f5c2d02845b00001e06b0032ed8d6604951a100f414d18b1f10aeb52c3742ed300b9807cc215aa40d3b810c50a6a00000408c803bd404b46060e012be0389a0a50616a2856750131b095881130000000000d0062e0ac5c2890000000001809c000005248b10c76c0abb83042014d40875811e44293d8097093db6037a0696d0058b0c0ac18d9833b28857503e263776c1eaeb85e80ab6c1577812e1082e8023de20e902f3983b1b0809a18834091885ac6036e8092b43399010aa0711c198400b7684a5c0572208b84197684a6b0c2c60215d85b68c27100b8c1160c6d0c00c9000000079f40719007c0093800003045eb010900000c19100000782e04067680b4b80e032c231036c804d24200804fa110c7e087b030e80000a02020000002e6c8124c05d021625411e9024f8018200000000000000a094fe142d4237d81f0802dae154e4280d061cb0157217bf4037f8c7f3023e80e14802e8857041afee25e5441aa056860c2aa0539c6028000000001a0eb542572860d00001603bc00004000b00001c2fb7430878177203ed8060000001858c50bb600002c29058105a0ce341310022cd8504000008071f8172f8246806dc022d7c17a0811590c5f422980000004b8710e000001803ad050a00001216f7407b5819000000e0ead820a4834dd07d9409b8000030438e05d6218ce414e9016580b3980018000028415c11e2211ffc14e625b9406ed614cf82dc000000000000003c0563035a000004082302d8800000000000000030fb8235d0a90b1353c16a0022c510648144c01824852554911c0e0a00161053100a018066e41cba81a1d0bc34161d454f2d4232045e417e7c2c03062d else 0x6302942ff505628047900d8e412733af900665c17ca06119865b00a10402a9832b985fc705c5e09a58561c0dbcc00af004b4c12ca04c09055781961c14db80bea03a440acd46c26039c10926820e682b02839f1055b2031e4623303c08090501959827220bb5703f480a8b821b90496a0224a0c23c2689b39f3005de10c2003158282c0b94602ee013db01547155a818cb19bf984df9080441126c6d0386420156b20ed600984006df11980016a4027f0e7c50a42405165257104b4302f04010d013bd01d5f494ee101802200049847755617fdc2e9b804e3153)))
def hashf3863l10 (i : Nat) : Nat := 0x4040f03c604bc13583f2014a08341f18160018401c41a80006086c0c4804e0258057e0d1811c81b00000000000603cc023605144f1817306e80238178046a00d0060822101fc055410901600009077801181d2832000000000006841b026c287010800000000003002800000000000000183900000002c0c80007050000201c4845001e000240eb83dd01c0001812601af04400000000000402a6cb6008000d0038402e8502803004e00004168000b004000000078000001e0da81700000001c0040000000b053e0c301986000828002000000204080000c50200080020808405
def f3863d9 (i : Nat) : Nat := 0x1c0010000000000000000000000000038002000000000000380020000000000e000801e000f8003e000f8003e000f8002070004000001e00080095e00103c001f0007c001f0007c0010001e000cab28497234831e46f1945b144470f4330a41f0540b003f6fb3e2f63b4eaba0e5b8ce0b78dbb64d6b50cb322c630ec12fabc2e6b72b8abaa4a025c8e2147c1cc7099e6518a601765b1484f9003d8d22b88a198420e02e09001d748b954d528cd208025db3ac652a719a41005a9e758caa225548200973ceb195444aa904016f60da5c52195520802fe83a650a432aa41005f5875ca14865548200a7f06db4d11422904012f71d1b31a6955208025cf3ac652a72aa41004b3e371a59de6648200967ceb99498ccc904012cf9d7b31a59992080293f1b6d2d113ba41005a3e758caa22774820096f8e8d98d34ee904012e79d632931955208029fa1b6d346708a410053dc36da6956114820096f86e34b3bc22904014df0db69a77845208025be3af6634b08a410075d82e5525461148200b574eb19544444904012fe1d1b31a6889208025db3ac6526319a41005ab6758caa223348200976ceb19544466904016fc0da5c5218cd20802fb83ae50a4319a41004bb6758ca546334820096ecebd98d2c66904012fd1d1b31a68cd20803af817298a4319a41004b76371a59de3348200b798ea5552ac22984016eb1d4aaa6684530802db63a9554ef08a61005aec752aaa22114c200b754ea55533444984016da9d4aaa7788930802d753a955511112610075f02e531486224c200b5f06d2e290d10904016cb9d4aaa77999308031f3368e1843552610063ce715b4086aa4c200c75ce336810d54984018db9c76d021aa930803177390da0435526100636e71db4206aa4c200bf60eb18498a4298401d748b954d5288930802f783a650a4344241005e7875ca1486884820094fceb99498d109040129f9d7b31a5a2120802ddc3ac6526290a41006b78329875c521482009fe16eb8650a4290401ade1c7694a148520802df43a95544508a61006af46a1c32858148200d5b8d438a50b0290401aaf1a8718a160520802be91b6b9aa6a92410077522dcb354d524820087ecedd98d1946904010f79dbb31a52952080217f3b76635054241007ad86a1526055148200
def f3863l9 : Packing := (71,6,7,0,4,10,0,f3863d9)
def f3863d10 (i : Nat) : Nat := (if i<9 then (if i<4 then (if i<2 then (if i<1 then 0xbde9c7216224c200afe9ca216224c200afe9c82ea224c200e7e8c9696224c200afe8cb696224c200bfc9c32d6224c200afe9ca2d6224c200afeacc69a224c200e7e8c969a224c200afe8cb69a224c200bde9c72e2224c200afe9ca2e2224c200afe9c12ea224c200afe9c52ea224c200afe9c62ea224c200afeacc696224c200ff625588a114c200fee26688a114c200fde27788a114c200fbe28888a114c200efe2aa88a114c200ffc15388a114c200ffc0b388a114c200efe1a588a114c200efe1a688a114c200efe1a788a114c200efe0ba88a114c200efe0ca88a114c200faf28899a114c200ff52558ce114c200fed2668ce114c200fdd2778ce114c200fbd2888ce114c200efd1a68ce114c200efd1a78ce114c200fe7266956114c200ef72aa956114c200ff50b3956114c200aff0c1699a548200ef70ba956114c200fcf27799a114c200b7f0c988a114c2008ff8cb61da5482008ff9c3aeda6482008ff9c5aeda648200cff0b32c5a6482008ff8cb61da6482009ff1c1aeda648200cff1a72c5a648200cff1a82c5a6482008ff9caaed87482008ff9c32e987482008ff9c52e9874820097f8c96e98748200ffc23388a114c2008ff9c1aeda848200cfe9c2aeda8482008ff9c3aeda848200c7f8b9aeda848200cff1b12c5a848200afb9c42c5a848200adf9c72c5a848200a7f8c96c5a848200cfd9b32cda848200aef9c62cda848200aff0c16d9a848200e5fa772e5a848200abfacc6a0a848200bfd1c314a114c200bef1c614a114c200ef71a6956114c200ff515354a114c200aff1ca20a114c200aff1ca2ca114c200bfd2cc54e114c200ff518554e114c200efd1a754e114c200f7d0c954e114c200bfd0cb54e114c200b7f0c9a22114c200bfd1c52ce114c200aff1ca5d6114c200bfe1c2216114c200bfd1c3216114c200bef1c6216114c200bdf1c7216114c200aff1ca216114c200aff2cc696114c200e7f0c9696114c200aff0cb696114c200bfd1c32d6114c200bef1c62d6114c200b7f0c954e114c200eef2aa99a114c200fed15399a114c200eef1a599a114c200eef1a799a114c200f9f2889de114c200edf2aa9de114c200fdd1539de114c200fdd0b39de114c200aff1ca14a114c200edf1a69de114c200edf0ba9de114c200ebf2aaa22114c200ebf0caa22114c200fbd153a22114c200fbd0b3a22114c200ebf1a5a22114c200ebf0baa22114c200edf1a59de114c200ebf1a7a22114c200afb1c4aaa114c2008ff1c1aeda648200aeb9c4aaa664c200aaf9c62ea88482008ff0cb69a11482008ef9c62e951482008ef9c62e953482008df9c72e931482008ef9c62e93148200bde1c72852148200bfc1c32852148200afa9c4aaa224c200afe0ca5c521482008df9c7aeda5482008ef9c62ea88482008df8cb6967748200 else 0xa7f8c96e1a148200b7e8c96d95248200dde9b82dd5248200b7e8c96a15248200b7e8c96e152482009df9c7aed524820097f8c96d9524820097f8c96e1524820097f9c12e582482009feacc6c853482008ffacc6e853482008ff9caaed53482008ff8cb6995348200bfe0c169952482008ff9cb695324820097f8c96d5324820097f8c96d932482008ff9cb6a132482009fe9c1aed5248200df6953aed5248200df6975aed5248200df68a5aed5248200dde9c7aed5248200dde8b7aed5248200bde9c7aed5248200dde8b76c55248200bf69c520d5248200bf6acc54d5248200ff497354d5248200ff498354d5248200ff48b354d5248200ef69a754d5248200fd68b754d5248200bf69c754d5248200ef68ca54d5248200afe8ca54d52482009fe8cb5cd5248200bfe1c120d5248200bfa9c420d5248200b7e8c96c55248200ede9a59de224c200ede9a69de224c200ebeaaaa22224c200fbc931a22224c200ebe9a1a22224c200ebe9a6a22224c200ebe8baa22224c200b7e8c9a22224c200bfcacc4c6224c200ffc1814c6224c200ffc0b14c6224c200bfc9c54c6224c200aff1ca2d6114c200efc8ba4c6224c200bfc9c3146224c200afe9ca146224c200b7e8c9546224c200afe9ca546224c200afe9ca586224c200bfc9c3206224c200bde9c7206224c200afe9ca206224c200afeacc686224c200afe8cb686224c200bfc9c32c6224c200efc9a64c6224c200aff2cc69e114c200aff0cb69e114c200aff1ca2e2114c200aff1c22ea114c200aff1c52ea114c200aff1c72ea114c200aff1c82ea114c2009fd8cb8ce114c200afb9c4aaa114c2008ff8cbaaa114c2009fd8cb54e114c2008ff8cb696114c200fdc9539de224c200fcea7799a224c200faea8899a224c200eeeaaa99a224c200fec93199a224c200eee9a199a224c200fec95399a224c200eee9a599a224c200eee9a799a224c200eee8ba99a224c200edeaaa9de224c200fdc9319de224c200ede9a19de224c2008ff8cb69e114c200d6f8b999a224c200afb9c4aaa224c200ffc131486224c200d7e8b9486224c200d7d8b94c6224c200c7f8b9686224c2008ff8cb686224c200ff495354a224c200d7e8b954a224c200d7d8b954e224c2008ff8cb696224c2008ff8cb69a224c200afe9ca2c6224c200fcda7799a334c200eed9a799a334c200bf59c5086334c200bed9c6086334c200afd9ca086334c200afd9ca146334c200b7d8c9546334c200bdd9c7206334c200afd9ca206334c200afd9ca5da334c200afdacc69a334c200ecfaaa9de664c20097f9c82e6224c200bfcacc54e224c200ff498554e224c200ff48b554e224c200f7c8c954e224c200b7e8c954e224c200b7e8c958e224c200afe9ca596224c200bfe1c1216224c200bfc9c3216224c200bee9c6216224c200) else (if i<3 then 0xcdf8ba61d7348200cef9b669483482008ff9c82e973482009ff2cc6c48348200dfe1c26c48348200cff1a56c48348200cff1a76c48348200cff1ca6c483482009feacc6c88348200cfe9a56c88348200cfe9a76c88348200cfb9a56d08348200cfb9a76d08348200cf79b569483482008ff9c52e97348200af7acc694a5482009efacc6d8a548200cef9a86d8a5482008ff9c1aeda5482008ff9c3aeda548200cf79c5aeda548200cdf9c7aeda5482008ff9c8aeda548200cdf8b7aeda548200adf9c7aeda548200cff1b12c5a548200aff1c1215a348200a7f8c96c5a548200cfd9b32cda548200cdf8b76cda548200a7f8c96cda548200aff0c16d9a548200cdf8b76d9a548200a7f8c96d9a548200ecf9a19de664c200cdf8b82dda548200cdf9b82dda548200cbf9b82e1a548200a7f8c96e1a548200cdf8b76c5a548200afe9c2215a348200afd9c3215a348200aef9c6215a348200adf9c7215a3482008ff9cb215a348200cf79b52d5a348200a7f8c96d5a348200aff0c16d9a348200a7f8c96d9a3482008ff8cb61da348200cbf9b82e1a348200aef9c6295a348200cfb9a86d0a548200bef0c169965482008ff9c32e965482008ff9c82e965482009ff2cc6c48548200dfe1c26c48548200cff1ca6c485482009feacc6c885482009fdacc6cc8548200cfd9ca6cc85482008ffacc6e885482008ff9c32e98548200cfb9a66d0a548200aff0c1699a3482009f7acc6d4a148200df69c26d4a148200cf79a86d4a148200cef9a86d8a148200cdf9a86dca1482009bfacc6e0a1482008ff9ca6e0a148200aff1c114da1482008ff9cb14da148200aff1c120da148200afe9c220da1482008ff9c82e95348200af79c520da148200aef9c620da148200adf9c720da1482008ff9cb20da148200aff1c1215a148200afe9c2215a148200afd9c3215a148200afb9c4215a148200aef9c6215a148200adf9c7215a1482008ff9cb215a148200a7f8c96d5a148200afb9c420da148200e3f8c96a18148200cbf8cb6a181482008ff9c32e981482008ff9c52e981482008ffacc6e98148200cef8c66e98148200c7f8c96e98148200efe152684a148200dfc9b3548a148200dfa9b4548a148200df69b5548a148200dee9b6548a148200cbf9b8694a148200dbe9b8548a148200cf79b568ca148200cef9b668ca148200cdf9b768ca148200cbf9b868ca1482009fdacc6cca148200cfd9a56cca148200cfd9a86cca148200cfb9a56d0a148200cfb9a86d0a148200cef9b6694a148200cdf9b7694a148200dde9b7548a148200bee9c620d5248200bde9c720d5248200afe9ca20d52482009fe9cb20d5248200bf69c528d5248200bee9c628d5248200bde9c728d5248200dde8b72cd5248200b7e8c96cd5248200fd69875d55248200bf69c32955248200 else 0xeee8ba5962258200afeacc6962258200afe8cb6962258200bee9c62d62258200afe9ca2d62258200afe9c32ea2258200afe9c52ea2258200afe9c82ea22582008ff8cb6962258200fd5a779563358200fb5a889563358200fe59619563358200fe69855962258200fe69619562258200ef69a19562258200fe69639562258200ef68ba9562258200ef68ca9562258200fe69659562258200ef69a59562258200f9ea889de2258200fce9619de2258200ede9a19de2258200fce9639de2258200fce9659de2258200afe9ca5462258200fae961a222258200ebe9a1a222258200fae963a222258200fae965a222258200ebe9a5a222258200ebe9a7a222258200ebe8baa222258200fec9634c62258200bee9c64c62258200fe69655462258200ef69a55462258200bee9c65462258200ede9a59de2258200afd8cb6963358200bed9c62d63358200afd9ca2d63358200afd8cb69e3358200afd9c22ea3358200afd9c52ea3358200afd9c72ea3358200afd9c82ea3358200fcd9639de33582009ef8cb59633582008ff8cb69633582008ff8cb69e3358200ef59a19563358200fc79619de5558200ed79a19de5558200fc79639de5558200fa7961a225558200eb79a1a225558200fa7963a225558200eb78baa225558200fe59634c65558200be79c64c65558200fe71815865558200bf71c10ca5558200bf39c40ca5558200f97a889de5558200ef58ba9563358200ef58ca9563358200f9da889de3358200fcd9619de3358200edd9a19de3358200fcd9659de3358200edd9a59de3358200edd8ba9de3358200fad961a223358200ebd9a1a223358200fad965a223358200ebd9a5a223358200afdacc6963358200fe59655463358200ef59a55463358200bed9c65463358200afd9ca5463358200fed1815863358200edd9a75c63358200afd9ca5c63358200bed9c614a3358200afd9ca14a3358200afd9ca2ca3358200bedacc5963358200fe59855963358200bed8cb5963358200ebd8baa223358200cdf9b769483482008ff9cb69483482009f7acc6d48348200df69c26d48348200cf79a76d48348200cf79ca6d48348200cef9a76d883482009dfacc6dc83482008ffacc6e883482008ff9c52e983482008ffacc6e983482009df9c7aeda548200cef9b6694a348200cdf9b7694a348200cdf9b7698a3482009efacc6d8a348200cef9a86d8a348200cdf9a86dca3482008ff9c1aeda348200cfd9c3aeda348200cfb9c4aeda3482008ff9c5aeda3482008ff9c8aeda348200cff1b12c5a348200afdacc68ca348200aef9c62e953482008ffacc6e95348200cdf8c76e95348200c7f8c96e953482008ff9caaed63482008ff8cb6956348200bef0c169963482008ff8cb6a163482008ff9c52e963482008ff9c82e963482009fe9c2aed7348200)) else (if i<6 then (if i<5 then 0xffc0c24c5214c200efd1a64c5214c200dfd1b84c5214c20097f8c96d5214c200dfd181aed314c2009fd9c5aed314c200cfd9a6aed314c200b7d8c9545314c2009fd9cb545314c200bfd2cc605314c200dfd131aed214c200bcf9c65467758200adf9ca5467758200fcf18158677582009df8cb54a7758200bcf9c654e7758200bcfacc58e7758200fcd98358e7758200f4f8c958e7758200b5f8c968e7758200bcfacc5967758200fc79855967758200adfacc6967758200fb6a889562258200bbb9c40ca8858200bb79c50ca8858200b9f9c70ca8858200bbb9c414a8858200fed1634c52158200ded963aed31582008ff8cb69531582008ff8cb69d3158200de7965aed5158200cf79a5aed5158200fe71655c55158200ef71a55c55158200bbf1c10ca8858200bd79c70ca5558200bb79c80ca5558200af79ca0ca5558200af79ca2ca5558200be7acc58e5558200fe598358e5558200f678c958e5558200be78cb58e5558200b778c968e5558200be79c62ce5558200bd79c72ce5558200af79ca2ce5558200ed79a55467758200af79c32ea5558200af79c82ea55582009ef8cb58e5558200af7acc6965558200f8f961a227758200e9f9a1a227758200f8f963a227758200f8f965a227758200e9f9a5a227758200fcd9634c67758200bcf9c64c67758200fc79655467758200af79c22ea5558200de79c66d43258200cf79ca6d432582009bfacc6e03258200cbf9ca6e032582009df9c7aed5258200cdf9ba2dd5258200fad98358d82582009ef8cb58d82582009ef8cb59582582008ff8cb69582582008ff8cb69d8258200baf8c86d95358200faf18260561582009ef9c5aed6358200bedacc60d63582009ef8cb61563582009ef8cb61d63582009ef8cb59583582009ef9c3aed6558200be7acc6156558200fa798761565582009ef8cb61d65582008ff9c2aeda5582008ff9c3aeda5582008ff8cb61da558200cef8ba6d95358200bef1c10c96158200beb9c40c96158200be79c50c96158200bcf9c70c96158200baf9c80c96158200beb9c41496158200aff1c10c9a158200afb9c40c9a158200af79c50c9a158200adf9c70c9a158200abf9c80c9a158200afb9c4149a1582009f7acc6d43258200def1656c43258200cff1a56c43258200def1c66c43258200cff1ca6c43258200deb9656d03258200cfb9a56d03258200de79b55943258200dcf9b75943258200daf9b85943258200cf79b56943258200cdf9b76943258200cbf9b869432582009ff2cc6c43258200fee1815862258200bee9c614e2258200afe9ca14e2258200bee9c654e2258200beeacc58e2258200fec98358e2258200f6e8c958e2258200eee8ba58e2258200b7e8c968e2258200bee9c62ce2258200afe9ca2ce2258200beeacc5962258200be79c60ca5558200 else 0xefc9a18ce2258200fec9658ce2258200efc9a58ce2258200efc9a78ce2258200efc8ba8ce2258200efc8ca8ce2258200fec9638ce2258200fd6a779562258200bfb1c414a1158200d5fa772e5634c200d3fa882e5634c20097f9c22e5634c200d7d9532e5634c20097f9c82e5634c2008ff9c2aeda64c2008ff9c5aeda64c200e77a552e5a64c200e5fa772e5a64c200ffc23388a1158200ff625588a1158200fde27788a1158200fb72889561158200fee16388a1158200fee16588a1158200efe1a588a1158200efe1a788a1158200ff52558ce1158200fdd2778ce1158200fbd2888ce1158200fed1658ce1158200efd1a58ce1158200efd1a78ce1158200fed1638ce1158200fd72779561158200fbe28888a1158200adf9c7086aa4c200abf9c8086aa4c200cfb9b4486aa4c200afd9c3146aa4c200cfb9b4146aa4c200cfb9b4546aa4c200a7f8c9546aa4c200cfb9b4586aa4c200cfb9b45c6aa4c200afd9c3206aa4c200cfb9b4206aa4c200adf9c7206aa4c200b7d9c82e5314c200cfb9b458aaa4c200cfb9b45caaa4c200cfb9b420aaa4c200cfb9b460aaa4c2008ff8cb60aaa4c200cfb9766d2aa4c200df59b554c214c200ded9b654c214c200ddd9b754c214c200dbd9b854c214c200cfd9ba54c214c2009fd9cb54c214c200cfb9b4606aa4c200ebe9a85498148200fed131486664c200bedacc4c6664c200fed1814c6664c200bed9c54c6664c200b6f8c9546664c200aef9ca546664c200aef9ca5c6664c2009ef8cb606664c200aefacc686664c200bed9c314a664c200aef9ca14a664c200aef9c6086aa4c200bedacc54e664c200fe598554e664c200eed9a754e664c200f6d8c954e664c200b6f8c954e664c200aef9ca5d6664c200aefacc696664c200e6f8c9696664c200aefacc69e664c200afd9c3086aa4c200cfb9b4086aa4c200af79c5086aa4c200fe595354a664c200dfd1b5605314c200fbd186605314c200fed0c6605314c200fbd0b8605314c200f7d0b9605314c200bfd1c1149314c200bed9c6149314c200afd9ca149314c2009fd9cb149314c200bfd1c1209314c200afd9ca209314c2009fd8cb609314c2009fdacc6cc214c200bed9c62c9314c200bdd9c72c9314c200bbd9c82c9314c200b7d8c9695314c2009fdacc6d5314c200d7d8c96d5314c200d7d8b96d5314c200b7d8c96d5314c200bfc8c26dd314c200b7d8c96dd314c200bdd9c72e1314c200b7d8c96e1314c200bf59c52c9314c200cfd9a56cc214c200cf79b5694214c200cef9b6694214c200cdf9b7694214c200cbf9b8694214c2008ff9cb694214c2009f7acc6d4214c200df59c36d4214c200cf79ca6d4214c2009bfacc6e0214c200cbf9ca6e0214c2008ffacc6e8214c200fbd182605314c200bfd2cc4c5214c200ffc1624c5214c200) else (if i<7 then 0xf5d8b99de3348200edd8ba9de3348200ebdaaaa223348200fbc921a223348200ebd9a1a223348200fbc952a223348200eed8ba99a3348200fdc8c754a3348200f7c8b954a3348200eed9a65963348200afd8ca5963348200afd9ca5963348200afd9ca5d63348200bfd1c12163348200bfc9c22163348200bed9c62163348200bdd9c72163348200afd9ca2163348200afd8ca6163348200afd8ca5463348200bed9c62963348200afdacc6963348200edd8c76963348200afd8cb6963348200bfc9c22d63348200afd9ca2d63348200afd9ca5da3348200afd9ca61a3348200afdacc69a3348200efd0c169a3348200afd8cb69a3348200bfd0c169a3348200ef59a52963348200afd9ca5463348200eed9a65863348200afd9ca5863348200edd9a75c63348200afd8ca5c63348200afd9ca5c63348200bfc9c22063348200bdd9c72063348200afd9ca2063348200ebd9a86063348200afd8ca6063348200afd9ca6063348200efc9a754a3348200bf59c52863348200bed9c62863348200bdd9c72863348200bbd9c82863348200afdacc6863348200afd8cb6863348200bfc9c22c63348200afd9ca2c63348200bfcacc54a3348200ff497554a3348200ff48a554a3348200ff48b554a3348200efd1a12863348200cfb9c4aeda14c2008ff9c5aeda14c2008ff9c8aeda14c200c7f8b9aeda14c2008ff9cb209a14c2008ff8cb609a14c200cfe9b22c9a14c200cf79b52d5a14c200a7f8c96d5a14c2008ff8cb61da14c200afe8c26dda14c200a7f8c96dda14c200fcd9319de664c200a7f8c96e1a14c20097f8c96d9324c2008ffacc6e8824c2009fd9c3aed824c20097f8c9aed824c2008ff9caaed824c200bfd1c12cd824c200bf99c42cd824c200cfd9ba2cd824c2008ff8cb699824c2008ff8cb6a1a24c20097f8c96dd634c200cbf9b82e1a14c2008ff9cb695314c20097f8c96d5314c20097f8c96dd314c20097f8c96e1314c20097f9c82e5314c2009fdacc6cc514c2008ffacc6e8514c200c7f8b9685514c200d7d8b96cd514c20097f8c96d9514c20097facc2e5514c20097f9c22e5514c2008ff9c2aeda14c200c7f9ca2e5514c2008ffacc6e9514c200c7f8c96e9514c2009fdacc6cc814c200cfd9a56cc814c200cf79b5694814c200cdf9b7694814c2008ff9cb694814c2009dfacc6dc814c2008ffacc6e8814c2009ef9c6aed814c200cef9ba2d9814c200d7d9c32e5514c200fe71639561158200ef71a79561158200fe71659561158200ef71a59561158200f9f2889de1158200fcf1639de1158200fcf1659de1158200edf1a59de1158200bfb1c40ca1158200bf71c50ca1158200bdf1c70ca1158200bbf1c80ca1158200d77a552e5634c200ff4a558ce2258200fdca778ce2258200fbca888ce2258200fec9618ce2258200 else (if i<8 then 0x8ff9c52ea33482008ff9c82ea3348200fc7a7799a5548200fa7a8899a5548200afd8ca58e3348200afd8cb69e3348200ebd9a82a23348200afdacc6a23348200e7d8b96a23348200afd8cb6a23348200afd9ca2e23348200d7d8ba2e63348200afdacc2ea3348200afd9c12ea3348200afd9c52ea3348200afd9c62ea3348200afd9c72ea33482008ff8cbaaa3348200ef59a39563348200d778b99563348200cf78ba9563348200eed9a399a3348200d6f8b999a3348200cef8ba99a3348200edd9a39de3348200d5f8b99de3348200ebd9a3a223348200d3f8b9a223348200cbf8baa223348200c7f8b9aaa3348200afd9c82ea3348200af78cbaaa5548200bf6acc4865548200ff61314865548200ff61714865548200ff60a14865548200ef69a64865548200bf68cb4865548200bf69c20c65548200af79ca0c65548200ef59a34c65548200af78ca4c65548200af79ca4c65548200ee7aaa99a5548200af79ca5865548200af78ca5c65548200bf69c22065548200bf39c42065548200bd79c72065548200af79ca2065548200af78ca6065548200ef71a12865548200bf59c32865548200bf39c42865548200be79c62865548200bd79c72865548200ee79a65865548200fe692199a5548200ee79a199a5548200fe68b299a5548200ee79a399a5548200ee79a799a5548200ee78ba99a5548200f97a889de5548200fd69219de5548200ed79a19de5548200ed79a39de5548200ed79a69de5548200eb7aaaa225548200af79c8aaa5548200eb79a1a225548200fb68b2a225548200eb79a3a225548200eb79a6a225548200eb79a7a225548200eb78baa225548200eb78caa225548200af78caa225548200ef6921aaa5548200af79c1aaa5548200af79c3aaa5548200af79c6aaa5548200fb6921a225548200ebd9a6a223348200ebd9a7a223348200f3d8b9a223348200ebd8baa223348200ebd8caa223348200afd8caa223348200efc921aaa3348200afd9c1aaa3348200efc952aaa3348200afd9c5aaa3348200afd9c6aaa3348200afd9c8aaa3348200afd8ca61e3348200afd8cbaaa3348200bfcacc4863348200ffc1714863348200ffc0a14863348200ffc0b14863348200bfc9c54863348200efc9a64863348200f7c8b94863348200bfc9c21463348200afd9ca1463348200ff49525463348200ef59a55463348200e7d8b9aaa3348200ef59a59563348200afd8ca9563348200fcda7799a3348200fada8899a3348200eedaaa99a3348200fec92199a3348200eed9a199a3348200fec95299a3348200eed9a599a3348200eed9a799a3348200eed9a899a3348200f6d8b999a3348200ebd9a5a223348200f9da889de3348200fdc9219de3348200edd9a19de3348200fdc9529de3348200edd9a59de3348200edd9a69de3348200 else 0xafe9ca6062248200afe9ca14e2248200afe9ca54e2248200ebe9a1a222248200ff60b29561148200ff60c29561148200ef71a39561148200ef71a69561148200ef71a79561148200ef71a89561148200f770b99561148200ef70ba9561148200ef70ca9561148200ff61529561148200ef71a59561148200fcf27799a1148200aff0cb6961148200eef2aa99a1148200fee15299a1148200eef1a399a1148200eef1a599a1148200eef1a799a1148200eef1a899a1148200f9f2889de1148200fde1529de1148200edf1a39de1148200edf1a59de1148200edf1a69de1148200edf1a89de1148200faf28899a1148200fee26688a1148200fbe28888a1148200efe1a388a1148200efe1a688a1148200efe1a888a1148200ff52558ce1148200fed2668ce1148200fdd2778ce1148200fbd2888ce1148200efd2aa8ce1148200ffc1528ce1148200ffc0b28ce1148200ef72aa9561148200efd1a68ce1148200efd1a78ce1148200efd1a88ce1148200f7d0b98ce1148200f7d0c98ce1148200efd0ba8ce1148200efd0ca8ce1148200efd1a38ce1148200b7f0c98ce1148200fe72669561148200fd72779561148200fb72889561148200efd1a58ce1148200edf1a75ce1148200aff1ca5ce1148200bfe1c220e1148200bfb1c420e1148200bf71c520e1148200bef1c620e1148200bdf1c720e1148200aff1ca20e1148200aff1ca60e1148200aff2cc68e1148200efd0b368e1148200aff0cb68e1148200f5f0b99de1148200aff1ca2ce1148200aff1ca5d61148200bfe1c22161148200bfd1c32161148200bfb1c42161148200bef1c62161148200bdf1c72161148200aff1ca2161148200aff1ca6161148200aff2cc6961148200ef70b56961148200edf0c76961148200bef1c62ce1148200edf0ba9de1148200ebf2aaa221148200fbe152a221148200fbe0b2a221148200ebf1a3a221148200ebf1a5a221148200ebf1a7a221148200f3f0b9a221148200ebf0baa221148200ebf0caa221148200ebf1a8a221148200efe152aaa1148200aff1ca54e1148200ff615354a1148200ff617554a1148200ff60b554a1148200efe1a754a1148200fde0c754a1148200efe1a854a1148200f7e0b954a1148200bfe0cb54a1148200b7f0c960a1148200bfe1c52ca1148200bfe1c214e1148200aff1ca14e1148200bfe2cc54a1148200ffc1314863348200d7e8b94863348200d7d8b94c63348200afd8ca4c63348200afd9ca4c63348200ff495354a3348200d7e8b954a3348200d7d8b954e3348200afd8ca54e3348200afd9ca54e3348200eed9a658e3348200ff49529563348200afd9ca58e3348200edd9a75ce3348200afd9ca5ce3348200afd9ca60e33482008ff8cb69633482008ff8cb69a3348200c7f8b96a233482008ff8cb6a23348200)))) else (if i<14 then (if i<11 then (if i<10 then 0xbee9c62152148200bde9c721521482009fe9cb14d2148200afe9c220eaa48200afb9c420eaa48200af79c520eaa48200aef9c620eaa48200adf9c720eaa48200afe9c22ceaa48200aff1c1216aa48200afe9c2216aa48200afd9c3216aa48200afb9c4216aa48200aef9c6216aa48200adf9c7216aa48200bfe1c74c52148200aff1c12e2aa48200afe9c22e2aa48200afb9c42e2aa48200adf9c72e2aa48200a7f8c96a2aa48200dfe131aed2148200dfe171aed2148200cfe9a6aed2148200bfe2cc4c52148200ffc1634c52148200ffc1a34c52148200efe1a64c52148200afe9c22d6aa48200fbe121a221148200ebf1a1a221148200d3f8b9a221148200cbf8baa221148200bfe1c54861148200efd1a34c61148200aff1ca4c61148200ff61525461148200d7f0b95461148200aff1ca5461148200edf1a75c61148200bb79c82865548200ebf1a86061148200cff0ba6061148200aff1ca6061148200d7e8b954a11482009fe8cb54a11482008ff8cb68e11482008ff8cb69611482008ff8cb6a211482008ff9c32ea11482008ff9c52ea11482008ff9c82ea1148200ff4a558ce2248200aff1ca5c61148200bfe1c22d61148200bef1c62d61148200aff1ca2d611482009ff0cb69a1148200aff1ca61e1148200aff0cb69e1148200aff2cc6a21148200ebf0b86a21148200e7f0c96a21148200aff0cb6a21148200aff1ca2e21148200aff1c32ea1148200d5f8b99de1148200aff1c72ea1148200aff1c82ea1148200ffc1218ce1148200efd1a18ce1148200d7d8b98ce1148200cfd8ba8ce1148200ff61219561148200ef71a19561148200d778b99561148200cf78ba9561148200fde1219de1148200edf1a19de1148200aff1c52ea1148200afe9ca58e2248200bfe1c120e2248200bfa9c420e2248200bf69c520e2248200bee9c620e2248200bde9c720e2248200afe9ca20e2248200afe9ca60e2248200afeacc68e2248200afe9ca61a2248200afeacc69a2248200efe0c169a2248200feca668ce2248200fe5a669563348200fd5a779563348200fb5a889563348200ef5aaa9563348200ff49219563348200ef59a19563348200ff48c29563348200ef59a69563348200ef59a79563348200f758b99563348200ef58ba9563348200ef58ca9563348200afeacc6a22248200fbca888ce2248200efc9a18ce2248200efc9a58ce2248200efc9a68ce2248200f7c8c98ce2248200efc8ca8ce2248200efc9a38ce2248200b7e8c98ce2248200faea8899a2248200eee9a199a2248200eee9a399a2248200eee9a899a2248200eee9a658e2248200ebe9a3a222248200ebe9a6a222248200ebe8caa222248200ebe9a8a222248200efc9a34c62248200afe9ca4c62248200eee9a65862248200afe9ca5862248200ebe9a86062248200 else 0x8ff9cb6a12148200cfe9ba54881482009fe9cb5488148200cfe9a36c88148200cfe9a56c88148200cfd9b368c8148200cdf9b768c81482008ff9cb68c8148200cfb9a56d08148200cfb9a76d08148200cf79b56948148200cdf9b769481482008ff9cb6948148200ff615260551482009ef9c6aed8148200cbf9a8aed8148200bfd1c32858148200bf71c52858148200bef1c62858148200ebf1a82858148200cff1ba2858148200ffc23388a1148200b3f8c96098148200eaf9a82d98148200cef9ba2d98148200abfacc6a181482009dfacc6dc8148200ef71a56055148200ebf1a86055148200cff0ba6055148200bf6acc5495148200ff60c15495148200ef69a75495148200df69b75495148200fd68c75495148200af7acc6955148200ef70c16955148200ed78c76955148200cf78cb6955148200dde9b754881482008ff9c32e951482008ff9c82e951482008ffacc6e95148200cdf8c76e95148200c7f8c96e95148200ebf1a86056148200cdf8ba61d71482008ff9c32e971482008ff9c52e971482008ff9c82e97148200dfa9b45488148200df69b554881482008ff9cb6a15148200abfacc2ea8848200abf9c12ea8848200abf9c32ea8848200abf9c52ea8848200eaf9c62ea8848200abf9c72ea8848200baf9c62ea88482008ff8cbaaa8848200cfe8ba54a88482008ff8cb68e88482008ff8cb6968848200abf8ca61e8848200afe9ca21521482008ff9c52ea8848200efe131486aa48200afe9c5486aa482008ff8cb4c6aa48200ef6952546aa48200cff1b1606aa48200afeacc54aaa48200ef695354aaa48200cfe9b854aaa48200afe9c214eaa482008ff8cb54eaa482008ff8cb58eaa482008ff9c32ea8848200bbe9c214e8848200abf9ca14e8848200abf8ca54e8848200abf9ca54e8848200abf8ca58e8848200e9f9a75ce8848200abf8ca5ce8848200abf9ca5ce8848200ebd9a328e8848200baf9c628e8848200b9f9c728e8848200abfacc68e8848200abf8cb69e8848200abf9ca2ce8848200abf8ca5968848200abf9ca5d68848200bbb9c42968848200eb79a52968848200baf9c62968848200abfacc6968848200e9f8c76968848200abf8cb6968848200bbe9c22d68848200abf9ca2d68848200bbf0c169a8848200abf8cb68e8848200efe0ca4c521482009fe9cb5452148200bfe2cc5c52148200dfe1b55c52148200fde1765c52148200efe1a65c52148200fde1875c52148200fde1a75c52148200efe1a32852148200bfe1c32852148200efe1a52852148200bfe1c114d2148200aff1c120eaa48200bfe1c120d2148200bfa9c420d2148200bf69c520d2148200bee9c620d2148200bde9c720d2148200afe9ca20d21482009fe9cb20d2148200bfe1c12152148200bfc9c32152148200bfa9c42152148200) else (if i<12 then 0xaf7acc6865548200af78cb6865548200bf69c22c65548200bd79c72c65548200af79ca2c65548200b778c960a5548200bf69c12ca5548200ee79a658e5548200af78ca58e5548200af79ca58e5548200af78ca5ce5548200bf71c120e5548200af7acc69a5548200bf39c420e5548200be79c620e5548200bd79c720e5548200af79ca20e5548200af78ca60e5548200ef59a328e5548200be79c628e5548200bd79c728e5548200af7acc68e5548200af78cb68e5548200bd79c72ce5548200af79ca2ce5548200bf69c220e5548200eed9a34c66648200aef8ca4c66648200aef9ca4c66648200fe69525466648200ee79a55466648200aef8ca5466648200aef9ca5466648200ecf9a75c66648200aef9ca5c66648200eaf9a86066648200aef9ca60666482009ef8cb60666482008ff8cb69a5548200beeacc54a6648200fe695354a6648200fe697554a6648200fe68a554a6648200eee9a754a6648200fce8c754a6648200eee9a854a6648200bee9c214e6648200aef9ca14e6648200aef8ca54e6648200aef9ca54e6648200ecf9a75ce6648200aefacc68666482008ff9c32ea55482008ff9c82ea5548200f8fa889de6648200fce9219de6648200ecf9a19de6648200fce9529de6648200ecf9a39de6648200ecf9a59de6648200ecf9a89de6648200eafaaaa226648200fae921a226648200eaf9a1a226648200bee9c54866648200eaf9a3a226648200eaf9a5a226648200eaf9a7a226648200eee921aaa6648200aef9c1aaa6648200eee952aaa6648200aef9c3aaa6648200aef9c5aaa6648200aef9c8aaa6648200beeacc4866648200fee1314866648200fee1714866648200fae952a226648200cff0ba6053148200df69b55493148200cfe8ba5493148200afdacc68d3148200efd0c168d3148200cfd8cb68d31482008ff8cb69531482008ff9cb69531482008ff8cb69931482008ff8cb6a131482008ff9cb6a13148200ebe8ba54a88482008ff9c82e93148200aef9c62e93148200adf9c72e931482008ffacc6e93148200cfe9a86c85148200cfd9b368c51482008ff9cb68c51482008ff9cb6a05148200df6952aed5148200cf79a5aed5148200ff61525c55148200ef71a55c551482008ff9c52e931482009fe9cb21521482009feacc6d52148200dde8c76d52148200d7e8c96d52148200b7e8c96d52148200b7e8c96a12148200b7e8c96e12148200ffc1324c52148200efd1a34c521482008ff9cb68d21482008ff9cb695214820097f8c96d52148200ebf1a8605314820097f8c96e12148200df69b554831482009fe9cb5483148200cfe9a86c83148200cf79b569431482008ff9cb6943148200cbf9b86a031482008ff9cb6a03148200cfd9a3aed314820097f8c9aed31482008ff9caaed3148200efd1a36053148200 else (if i<13 then 0xede9a64867748200bde9c20c67748200adf9ca0c67748200edd9a34c67748200adf9ca4c67748200fd69525467748200ed79a55467748200adf9ca5467748200ecf9a65867748200adf9ca5867748200bde9c22067748200ebf0c16a18148200adf9ca2067748200adfacc6867748200bdeacc54a7748200fd695354a7748200dde8cb54a7748200adf9ca54e7748200ecf9a658e7748200adf9ca58e7748200bdf1c120e7748200bde9c220e7748200bdb9c420e7748200bd79c520e7748200bdb9c42067748200aef9ca5ce6648200aef8ca60e6648200aef9ca60e6648200eed9a328e6648200bcf9c728e6648200aefacc68e6648200aef9ca5d66648200aef8ca6166648200aef9ca6166648200beb9c42966648200ee79a52966648200aefacc6966648200bde9c54867748200aef8ca61e6648200aef9ca61e6648200aefacc6a26648200f9e921a227748200e9f9a1a227748200f9e952a227748200e9f9a3a227748200e9f9a5a227748200e9f9a6a227748200e9f8caa227748200bdeacc4867748200fde1314867748200ecf8c76966648200bbe9c21468848200abf9ca1468848200fb69525468848200eb79a55468848200abf8ca5468848200abf9ca5468848200e9f9a75c68848200abf8ca5c68848200abf9ca5c68848200ebf1a12868848200bbd9c32868848200bbb9c42868848200bcf9c620e7748200baf9c62868848200b9f9c72868848200abfacc6868848200abf8cb6868848200bbe9c22c68848200abf9ca2c68848200bbeacc54a8848200fb695354a8848200fb697554a8848200fb68a554a8848200ebe9a754a8848200f9e8c754a8848200bb79c52868848200adf9ca20e7748200adfacc68e7748200ecf9a65967748200adf9ca5967748200adfacc6967748200cdf8cb69677482009df8cb6967748200adfacc69a7748200edf0c169a7748200bdf0c169a7748200b5f8c96a27748200ebe921aaa8848200abf9ca4c68848200ebe952aaa8848200abf9c3aaa8848200abf9c5aaa8848200bbeacc4868848200fbe1314868848200fbe1714868848200fbe0a14868848200bbe9c54868848200bbe9c20c68848200abf9ca0c68848200ebd9a34c68848200abf8ca4c68848200abf9c1aaa8848200ef70c169a5548200af78cb69a5548200bf70c169a5548200af78ca61e5548200eb79a82a25548200af79ca2e25548200af7acc2ea5548200af79c12ea5548200af79c32ea5548200af79c62ea5548200af79c82ea5548200aef8ca5ce6648200ee79a599a5548200cef8ba99a5548200fb6952a225548200eb79a5a225548200cbf8baa225548200ef6952aaa55482008ff8cbaaa5548200af78ca54e5548200af79ca54e55482008ff8cb68e5548200ee79a65965548200af79ca5965548200fe695299a5548200 else 0x913aa258448e88d9112a214440687f90f6a1dc439686e90d4a198430e85d90b2a148426e8499090a11041fe83e906ea0d8418e830905ea0b8414e8259048a08040f681d9038a06040b68159028a040405e80a9012a01440067fc8ff69fdc3fae7f48fe09fbc3f6e7e98fd09f903efe7de8fb49f643ea67d08f9e9f383e667c88f889f0c3df67ba8f729ee03d9e7b28f629ec03d767ad8f589ea03d1e79f8f369e683cae7948f209e303c567868f0a9e043be67788eee9dd83ba67738ee49dc43b6676b8ece9d983b267608ebe9d6c3ace7588eae9d4c3a7674d8e929d143a1e73f8e7c9ce839c67348e669cc839567238e449c7838ce7128e1c9c3438467048dfa9be4378e6ea8dc69b8836ee6d98daa9b50367e6cb8d8e9b1836266c08d6c9abc35566a68d449a7834b66928d1c9a28342e67e8cf499e433a666d8cd29994331e6598ca4992c323663c8c6a98d0319662e8c54989831266208c389854306e60c8c0a98042ffe5f88be897b42f2e5e18bba97642ea65d38b9e972c2e065b68b5e96a02d0659f8b3696502c7e58b8b14960c2bf657a8aec95c82b8656c8ad0959c2b2e55e8ab495582a765478a8c950829ee5398a6a94d0297e5288a48947428ae5118a1a9424282650089f293c8276e4e989ca938426e64d889a89340265e4c7898692f025be4b3896492b8254e4a58942926824ae48e890e920023c647788e091b0232646088b29148226e449888a90f821ce435886290a8211641e8834906420a641088189020201e3ff87f68fdc1f963f187da8fa41f0e3dd87a68f3c1e563c387848f041dfe3be877a8ef01dbe3b3875e8eb81d363a2873c8e501c6638587028df41bae37186da8da41b2636086be8d6c1ab635286a28d401a7634d86988d201a1e34286768cdc199632e86548c98190e31d86328c60189e30f86168c28182e30486068c0818062ff85f68bd0177e2eb85ce8b8c16f62dd85b28b5416862cc85908b1c162e2c1857a8ae415be2b385648ab8154e2a585428a8014de29785268a3c1456286850489f813ce27584e289b4134626484c0897012d625684aa8950129625184a0893c123e243847888e0119e22f845c88b4115e2248440887010d6219842a8844107e20e841a8824102620083f887e00fb61f283e287b40f461e483c687880eee1d983aa87440e661c8838887000df61bd836c86d40d861af835086900cfe198832886400c5e184830085f00ba617082d885a00b3616282bc85680aae151829a85240a2613d827884ec09b6132825c84b409461248246848808ee11c8236846808c611482208424082610081f883e007b60f581e283b4075e0ea81cc838806ee0d981b0835006960ce81948324063e0c68184830405e60bb816e82cc055e09e812e8240042e07580d081780286040806680b0012601a801a8000))) else (if i<16 then (if i<15 then 0xc7bcef789eeebdd87b8ef6d9ed8bdac7b4ef689ecebd8c7b0ef609ebebd787ae6f589eaebd587aa6f539ea4bd447a66f4b9e8ebd0c7a0ef409e7ebcec79cef389e62bcc07976f2d9e52bc947906f1f9e3cbc7478def179e2cbc54789ef0f9e16bc28782ef049e00bbf077d6ef39dd8bba07706edc9db0bb50767eecb9d8ebb0c75deeb79d6cbad47586eaf9d5cbab4755eeaa9d52baa07536ea59d42ba8074f6e979d26ba487486e8c9d16ba28742ee849d00b9fc73eee799cf0b9d07396e719ce0b9bc7356e699ccab99072fee589ca8b94c728ee4d9c92b9207236e459c82b90071f6e3d9c78b8ec71b6e329c62b8c0715ee2a9c52b8a0711ee229c3cb86870c6e149c26b848706ee099c10b81c702ee049c06b8087006dff9bf6b7dc6faedf49be6b7c86f86def9bdcb7b46f5edea9bccb7946f06ddf9bbcb7746ededd79ba6b7486e6edcc9b96b71c6e16dbe9b7ab6f06dd6db99b6ab6d06d7edab9b54b6a46d3eda39b44b6786ce6d989b2eb64c6c8ed909b1eb62c6c4ed859b08b6006bf6d779ae6b5b06b56d699acab5906b16d619ac0b5586aa6d539aa4b5446a66d4b9a8eb50c6a0ed409a7eb4f869e6d389a68b4cc6976d2a9a52b494691ed229a3cb46868aed119a20b43c686ed0c9a16b428682ed049a06b4086806cff99fcb3e867aecf199dab398670ece099beb360669eccc9990b31065fecbb9968b2b46546ca1993ab258648ec8d990cb2086406c7998e4b1b8634ec6598c2b1686296c4e988eb0e861aec319854b08c60dec1a9826b0306026bfd97f2afc85f56be397beaf6c5ecebd597a8af4c5e76bca9792af205e36bc59788af0c5e0ebc0977eaeec5dcebb59768aecc5d8ebb09758aeac5d4eba8974eae8c5cf6b9a972cae485c86b8f971cae345c5eb8a970cae085c06b7f96fcadf45bdeb7796ecadd45b86b6f96dcada85b2eb6196c0ad705abeb53969ead2c5a4eb42967cace859aeb31965aaca4590eb1d9632ac545886b0c960aac0457ceaf595e8abcc578eaed95d2ab9456eead995aaab445666ac8958eab18560eac0957eaaec55b6ab59562aab4552eaa19540aa7054bea939524aa38544ea8594fca9e853aea6e94c8a98052dea5794a6a93c526ea49948aa90451e6a389468a8c0515ea21942ea8405046a0193f4a7d84f8e9ea93cca77c4ebe9d393a4a7384e669c89382a6e84dc69b7936ca6c84d6e9ac9356a69c4d2e9a19340a6644cbe9939324a6444c7e98b9314a6244c3e986930aa6104bce97592e2a5b44b5e96a92c6a5704ad695992b0a55c4aae95492a0a53c4a6e94c9290a51c4a2e941927aa4f049be9369264a4c44966928924ea48c48f691d9238a460489e912921ca42848168fe91f4a3d8478e8ed91d2a394471e8e291b6a35c467e8ce919aa32446268c09178a2e045b68b2915ca2a8452e8a1 else 0xfad3cda68b4c7697ad26da48b48768cad16da28b447684ad06d9fcb3ef679acf0d9d0b37f66eacd4d9a4b33f666accad984b2ff65eacb4d934b247644ac80d8fcb1ef63cac76d8e8b1c7637ac6cd8d4b18762cac56d8a8b147627ac46d87cb0ef61cac30d844b04f605ac08d80cb00f600abfed7f8afe75f8abeed7d8afa75f3abe4d7c4af7f5ebabced798af0f5daabb2d760aeb75d5aba8d74cae8f5d0ab9ed72cae4f5c8ab88d700adf75baab6cd6d4ad9f5acab56d690acff598ab22d634ac5f58aab0cd614ac1f582ab02d5e8abaf56eaad4d5a4ab3f566aacad590ab17561aac0d57caaef559aab0d55caaaf551aa9ad518aa0f540aa78d4bca957526aa4ad484a8e751baa2ed458a8a7513aa24d438a84f505aa02d400a7df4f4a9e0d3bca73f4e3a9c4d378a6e74d8a9a8d34ca68f4d0a998d32ca6374c2a97cd2f4a5df4baa972d2e0a5b74b2a962d2c0a55f4a7a93ad264a48f490a91ed220a41f479a8ded1a0a2ef45ca8b0d150a27f448a882d0dca17f42ba854d0a4a10f41da832d054a09f40fa816d01ca0173fea7e8cfb49f2f3dea7b4cf589e8f3cda792cf089dbf3b0a752ce949d1f39fa736ce509c67385a702cde89b9736ba6c8cd749aaf351a694cd0c99df337a666ccc8996f329a644cc7898cf318a62ecc40985f30aa612cc0897d72f0a5decbb897372e2a5bccb7496df2d4a59acb2496272c0a572cad495872aca550ca8494cf295a522ca34941727ea4fac9f093d7279a4f0c9dc939726ea4d4c998932725da4b2c96092b7252a4a2c91c9217241a480c8fc91d7236a464c8b89167228a442c87490c7214a420c83c906f20ca410c81c90171fea3fac7f08fd71f9a3f0c7dc8faf1f1a3dac7b08f571e9a3cac7908eff1dba3a2c7348e171bea374c6cc8d771aaa34cc6888cef199a32ac6388c4f185a302c5f48bc7174a2e0c5b08b3f163a2bec56c8acf155a2a2c5348a47144a280c4e489a7133a25ec4ac8937125a242c48088f7117a21ac40c880f0fda1f8c3ec87cf0f5a1e2c3b4875f0e7a1c6c37c86ef0d9a1aac34486670c8a188c30085df0b4a15ac2a4853f0a6a144c28484ff09ea134c26484bf096a12ac250849708ea11ac2308457086a10ac210841707ea0fac1f083d7076a0eac1c4834f068a0cec1988327063a0c4c17882cf055a0a8c14c828f050a09ec1388267048a08ec118820f040a07ec0f881e703ba074c0e481a7030a05ec0b8814f028a04ec098810f020a032c054808700fa01cc028802f001a000bff07fbeff69fdebfb87f66feb9fcebf987f26fe39fc4bf847efefdb9faebf587ea6fd39f9ebf2c7e36fc59f88bf0c7df6fba9f72bee07db6fb59f68becc7d76fad9f58beac7d4efa89f4ebe987d0efa09f3ebe787ce6f9b9f34be647cbef969f24be447c7ef8e9f1abe247c26f809ef8bde) else (if i<17 then 0x780020e000838003c00107000415041e000d5b040000000e00083800200700041c00100005041e00082ad82504107000405041055b04000cee001062f00081c001e000b62f000b80020e000f00042678005c001bc5e0010257000803380040e000f000780020e000f0007800200700043242678007c35c0020010f00078003c00108ee001700078003c001e000d62f000b80020e000b62f000b8003c00104c7362f000e63b8004d8bc002e000804562f000f717800400700078003c0010700078002193c0027c5e001032638004002105cc700080042197c0020cbe00100085a603c001e000800043c001010c98e00180464c7000f2638005931c002098e001000043c35c0020010f00041b31c002e000f00078003c00107000780020034c7000b8003c00100ce0016cc700081c001e000f000780020e0008047000b8002011c002004e001700078003c001e000f00040238004009c002e000f00078003c001e00080087800200a1e000f0007800216fc002e000800841c001e000f0007800378bc002e000dcc7000ae638005731c002b98e00101f178005c0017c5e00170006f178004095c002e000f00078002021c002e000f00078002095c002886e0010038780020001080387800200e10070f0004004200210050838003c001008e0017000431426380060021001084c700080000000e000f0007800200d9e0017000780021521b3c003886e0010437000b8003c001086e00170007800200e16980b4c041c0016980b4c04000001c001298083803a6045301e98094c04a603c001e98094c0488c20e0009410488c20298080000038002133c002e000f00078003d301e980838002d301e000b4c05a6020070005a603c0010700040c0016000b0007800206000b00078003c0012980f4c05a603d301e98094c04a603d301e98094c04a602142100040400000002df298174c07803a605d301e98094c0400070074c08a6024461003a602530100004461e980f4c07a603d3010700040d3016980b4c0400e980f4c07a603d301e980b4c05a603d30100371780040e98082f178005c001e00085bf000b8003c001e000edb7000b8003c001dc5e00100087a603c0010700058002f6c1e000f00040042f301e000ddb7000800e000f4c05a6020298094c04002a908000014c07a603c01d302e980f4c04a60244610038003d3010038002d3016980f4c041c001014c05a602000380020698081a602d301210e00105c87aedb70d108438005c341ee20f7bb6e1a187a825016f0d006143d412b86803081b3c3401830f504ae1a00c20250060040dc70d140301286e38688421c0020dee1a106cf0d0648c2dc12b86803081923abc349904b78f6edadd8dba0b71f6e2adbcdb68b6af6d4ada0db30b6576c9ad90db1cb6176bbad68dab4b55f6a7ad4cda94b51f69 else (if i<18 then 0x1a60200000d8a100c094c078002000000298091184000001c001000000162840000000e00081a602d8a100001ee1000b14a6040000aa43c0012a90800007000400030005800202980818002c001016294c0a639a085c00129828214c704a6025301e000f00058003c0010c5e001700040098e0800000000000b1420004cf0009a6020034c0400698081a602005430401b210000028208380020282086c94108a602001410780020000a0820000002820f00040069808000e00081a602d041015b04006980b410400000000038002d0410000000000000ad8200a108000070004a0820e0008005041a860b62840000380020e000b6284000362841c0010700040d0410001c0010700041c0010154b4108aa4258a5042003800200000504143c00300000e00080a082504100000016284a08202820941041c001000a08250412b60954840000000e00080000001c001e000f00058002131c002e000800c340022e000f0d700080043c0010010800842678005d31c002600084c7000b8002c35c0026980f000426380040021004c7000ba6000440021001083187a602133c002a98001100687a60004401c05743400a40130f0005a600044133c00261a00110260b8004b05c002a98e00104c7000ba602133c002e98e00134c700080043c00107000400e000f000400000000001c00107000400003800200000026100f0831878003c001000000038003c0010000007000400e000801c001e000f00041c001e000e47078003c00102087000b800201a1e000f00078003c001099e001700078003c001e000f00050138005c001bb6e0017000400070007a6025301298286174c0488c3c0012980f0004002a90800530122308088c3c001410e001700041c001e000f0004001a1e000f000420b8005c001e0008417000808c23b8007d301e000f0007800200a1000684034200a1e00080287800200a1e000cc134c7000d60aa638007531c002a98e00154c700082638005d301e000b4c7000ba602d31c002099e001700041c00107000423b8005d300022000000a1e000801c001055b041c007be2055b0400055b04000000003a0b9e001e41078003c0010002e78004105c00200000002ad82000380020014104a6020e0008380020e000f000415041e000801c001e000838003c001682e001700078003c001e000f00078003c00100077f8005c0011dfe001001c001e000f00078003c0010700078003c001e000f0007800270dc002e000f00078003c001e000838003c001e000f00078003c001e000f00078002b0dc002e000f0004156c1e00083800f7c40ab608000e00094c041c0010001c001000130c1e000801c001ab60f00041c001003800200700041c001e0008380020e000f000400054107800202820f000400e00080000001c001e000f000 else 0x2820f000405041298080a08219212820838003c00100000e00086494c08a39a084530504207000400014c040530100088c2001628400070004055210700041c001698081a08200001c001000a0821ea504447c0042c5094104a08200000000000e0009c10400000aa43c00100088c2552d0420c928216e2840000000014c04000000007000780020282087a94108000000000005301000a382d8a1070005b14200064f0008058a5302e000cd4b4108b14a085c00100380020000051cd04228e094c14108a3820000000000001118400070004a083b6c5042298080a083b6c504447c0042c5094104050410b70838002000005521e0009548780020db6096294c08a3820098e001700041c001070005a602000380020e000b4c05b142000000005b84000de0f00043d420b8007c0010d9e001001c35c002e00086284c7000c2e420b8006193c0020b6098e001838003c001e00084cf000a60b8004b05531c003098e00170004000d9e001700078003c00107000401c200a100508028402004b8006105c002098e001062f00080043c0010010f00078003305c002582ac5e001862f000960b8005c0010300078002105c0020b6e0012027000b8003305c002982e0012c17000aa638004131c0026c5e0017000560b8004197c0020c5e0017000780020e000f00046e38005c0015b60800905c002e000800105c00202de00107a8417000c000d9e001700078002000257000812b8005c001e000f00043278005c0010010f0007800210dc002dc5e001700078003c0010c50b6e00195b040000000e000f00078003c00100417000b8002007000401bf76dc003e0008000e000f00078003c001007a84b14a60451c128e094704a602000088c202980954840000000070004b142000380020e000f000432c20b8007c0010080c8e001f00078002f8bc002e000f00078003c001e000f00078002105c002e000f00078003c001e000f00078003c001e000f00078003c0010700078003c001e000f00078002011c002e000838003c00160008003020005cf000802004b8006104173c0030700040007000660825301030004b143304104c106ed8256c16000f00078003c001e00084c700083178005c00100380020000aa42000000014c04000700040007000400070004058a1298282100000000530122309410400000000700040068208000000006c50b41040069808000698080a39a084d30168208005041298094104050412b6080b14a6040001a602000000070005b14200038002d3016c508000e000b4c0400000006980800000000e00080)))))
def f3863l10 : Packing := (1664,5,7,7,4,15,0,f3863d10)
def f3863d11 (i : Nat) : Nat := (if i<11 then (if i<5 then (if i<2 then (if i<1 then 0x88930803fe498c4498401bfaaaa224c200f7d51111261007eea6688930803ef53bc4498401ff454e114c200bfb36610a61004ff9ba5d520802ff8d890a904017fa6c88548200bfb36642a41005fb9b421520802f7cdb10a9040177e6dc85482009ff37442a41004ff8ba61520802fdcda14a90401bde694a548200bdf36c52a41004ffabb69520803f6d3346698401bbe696664c200dbf16ed2a41007ed9539993080377cd0ccc984013fe6e97648200fdb26333261004ff9ba619208027fd5db4c90401bfc2c5a648200ddf55533261007cfa77999308037ecd3466984017fc2c5a6482009ff174c3a41006ef9a799930803e7cb0ceeb0401e7ea227758200def34b2aac1007e7965955608027fc5d51090401bfa486aa482009ff36355241006fe952aa9208037bc5d4aab04013fe6ceaa48200fcf2c72aac1004ff9b5aa9208027fcdb554904016fe6e0a148200def3432aac1005feabb48520803ff098a4290401f9e5865558200ffc2e290a41007fe0a148520803dbd444aab0401f5e9de5558200fdb2c719ac1005fe9b5485208037ec5d466b0401bfa6992148200dfb34f19ac1006fd9a58cd608027fcdc55490401bbe69e6648200ddf35133241005ef9b64c560803cfd444ee90401f7a4867748200fdb2c698ac1006df9a19dd20803ef4a94ee90401b7e68e7748200dbf34b3ba41006df9a69dd208035fd5551090401efa4868848200dbf3433bac1007af965a2160803d7cb1d10b0401afe6868848200f7d2a544241006bf9a1a2160803d7cb0d10b0401afe68e8848200dbf34b3bac1007cf9659dd608035fcd2d1090401f3e58e7758200d7f34d44241006bf9a7a21208035fc5d51090401afe6968858200fde2cb08ac1006ef9a658520803f78b1c22b04013fe6e96148200f7e51108ac1007df27784560803fb92ac22b0401b7e69d7148200ffa46708ac1004ff8ba5c5208027fcdd2e290401ff888a1158200bfd36440a41005fb9b420520803f6cb2c66b040177e6dc81482009ff576d3261004ff9ba205208027fcdd2ec984015fe2e5634c200d7f350c0a41004ff8ba605208027fcdd30290401bfc684a148200bfb36650a41005fb9b428520802fbcda942904013fe6e8824c200bdf36c50a410067f8b9699308037ecd0c66b0401fb65863358200bfd36418a41007bda888cd60803eed3bc66b0401fd695633582009ff37418a41006fd9a34c5208037f45d444b0401bfa69e22582009ff17498a41004ff9ba4c5208037f4d2c44b0401bfc6961158200fdd2cb112c1004ff9ba14520803f74b1c44b0401fda5495148200dfd343112c1007ee961889608037bcd2aa290401efaa222258200fbd4ef112c1007f6a5588960803fe519c44b04013fe2e951482009ff374a8a41006ff1a784560802ff4d90a2904013ee6d2aa4c200 else 0x1efca221148200def5552aa41006ff2aa84520803ef93bc2290401bde6865548200f6f5112aa41007d7a7795520803f3d334aa90401bf66963348200ddf34733241004ff8ba8cd20803ff0a9422904017fc6c43258200aff17319a41006f79a554560803fb490caa90401fba54a6648200bdf36ca9ac1005ef9b654560803f3cb2aa2b0401bfa6a222482009ff374292c1005ef9b614d608037ecd446690401fd69563348200dfe34d08a41004ff9ba5c560803ff090c2290401bfc69e1148200bdf36c292c1006ff1a8845208036fcd3ae2b0401bfc68e1148200dfb17519a41007eda668cd20802fdcda0a4b0401bde2ea5548200def34d2aa41007fc9218cd20803eed3bc6690401dbe2e56358200efe17308a41006f79a795520803ded4446690401bf6aaa3348200dfe17508a410077d8b98cd20802bfc5cc2290401fda2ca55482009ff374a8ac1006fd9a18cd20803f7490ccc90401bfa68e2248200fde302b0ac1006efaaa99920803d7d444cc904017beaed6358200f9f4ef33241004ff8ba955208037ecd3c6690401bfc6861148200fdb306b1ac1004ff9ba0c9608037ecd1c66904013fe6e85358200def34b2aa41005efabb595608037f8d2c2290401bfa69a2248200dfb34d19a41006f79a395520802bfc5cb46b0401fda54a5548200fcf30ab2ac1006df9a75cd208027fc5d2e6904013fe6e97348200bfe36241a41005fe9b220d20802fdcda106904017de6d48348200dfb34c98a61005ef9b620d20802efcdb906904013fe6e88348200bfb36a98a61004ff8ba60d20802efcdb94290401bf668ca348200bdf36c51a41005df9b728d208027fd5db4690401ff4605314c200bfb57698a61007fd131485308027fcdd04298401bbe6996548200b7f37010a61005df9b708530802f7cdb042984013fe2e965482009ff374b2a41004ff9ba60d20803fe919c22904013feaeda148200cff172d0a61005feabb54920803fb4a9aa4904013feaeda14c200fed2eaa9241007f68a5549208037f4d3aa490401f7a2dd52482009ff37440a61005df9b720530802fecd990298401df62e5314c2009ff374b0a610057f8b960920802ff4d90a6904013fe6e9514c2009ff37429a410057f8b9545308027fcdd0a2984013fe2e95348200bfb36628a61004ff9ba54d20802bfc5ca6298401bbe69963482009ff174b1a41004ff9ba58d208027fcdd2e298401afe6a0a8482009ff576d42410057f8b9889308033fc5cb5090401ff888a114c200ffa46708a61007f725584530803f793342298401f7c9de114c200f7e51108a61006ff2aa845308037f45d44498401bfa69e224c200bef36a10a61006fe9a688930803fe859c2298401bfa696224c200dfe34b08a61006ff1a6845308037f8d3c2298401ff254e224c200dfe17508a61006fe9a1) else (if i<3 then 0xcd11261006ff9ba60d60803fecbb46698401bfe6958358200fdf2cac1ac1005ffabb60d60802ffcdc2e6b0401fbe486664c200fbf30eb9ac1007fd9818cd308037fd5544498401bfe6958558200ffd24311261005ffabb61560802ffcdc2eab0401f7e61d7558200ffb26311261007ef98759560803f7c59acab0401fbe6156558200ffd26511261007fe95288930803ff4b144498401ffa68a224c200ffb2a711261006ff9a5889308037fcd344498401bfe686224c200bff37098a61007bf98760960802ffcd90a298401bfe6958258200fdf2cac12c1007bf98360960802ffcd98a298401fbe58d8258200ffb36e98a61005ffabb54530803ff8b8aa298401ffc605514c200dff342a8a61007fd9b3545308037fcd32a2984017fe6d9514c200bff576c12c10077f8b954530802ffcdd0a298401ff66a1314c200ffb17098a61007fd9b84c5308037fcdd304b04017feaed314c200ffe30298a61007fd9324c530803feca9a62984017fe6dd314c200ffb2c698a61007fd9734c530803fecc1a6298401bfe695314c200dff34ac0a61006ff9a7609608037fcd3262984017fe6d9314c200dff34e98a61006ff8ba60960803efcb9ae4b04017fe6e9714c200bff36440a61007ef9635c960802ffcd990298401bfe694814c200bff36a40a61006ff9a720530802ffcdc2e4b04017fe6dc814c200bff370a92c1005ff9ba20530802ffcdbaa4b04017feaed814c200fbf16ea92c1006ff9a160530803dfcc130298401bfe619a14c200dff374a92c1005ff9ba545308037fcdd2a298401ffc605614c200dff34ab92c1007ef962585308037fcd2ac298401bfe69d614c200bff36eb0a61005ff9b85c530803f7cb2ae4b04017fe6e9614c200bff576b8a61006ff9a15c530803efcb92e298401bfe695714c200fbf2ecb8a61006ff9a65c530803efcc3ae2984017fe6e1614c200fdf2caa9ac1007fd9524c530803fecb126298401ff6619314c200fdf2c6a9ac1007fd9764c530803fecc1aa6b0401ff65c9314c200ffb36a98a61007fd97354d60803fecd326298401ff6209314c200ffb34a98a61007fd9754c530803fecb2a62984017feaed5358200ffb30498a61005ff9b54c530803fecd926298401ff62c9314c200ffb34498a61007fd8b54c530803fecc3a62984017fe6e05358200ffb2e298a61007f798554d60803feca8a6298401ff669d314c200ffb36c98a61005ff9b214d60803fec29262984017fe6c45358200ffb30298a61006fe9a188920802efcdb864b0401ff888a11482009ff576d2ac1004ff8ba84520803f793342290401ff254a3348200f7d51111241007eea6688920802f7cdb064b04017ee6d03258200ddf34333241007f72558452080377cd2ccc904016fe6e03258200ff946711241007fe0b284520802fbcda864b04 else (if i<4 then 0x803fbc994aab0401fde5ca5558200fdf30ab0ac1007f798295560803f7cbaac2b0401fde68a5558200fdf306b0ac1007f78b2955608037fcd0c66b0401fde5ce5558200fef3072aac1007ef95358560803fbcd1caab0401fde2ce5558200fef30f2aac1007f79a795560803fbcd44aab0401fbe14d6158200fdf2e6b0ac1007fd9328cd60803efcc3ae2b0401ff65ce3358200ffb30719ac1007fd9a38cd60803f7cb2c66b0401bfe6963358200dff34f19ac1007f783295560803f7cb2ae2b0401fde4865558200fef2632aac1007ef9635c560803efcb92e2b0401fde5c65558200bff576b8ac1007f798195560803f7cc3ac2b0401bfe6957158200fdf30f33261005ffabb5cd60803f7cd3ccc98401fbe6a2664c200dff04355261007ef98758d608037fc90d5498401fbe2d56358200ffb57698a61006ff951aa9308037fcb0d5498401fbe6156358200dff2e355261006ff881aa9308037fcc0d5498401bfe58aaa4c200dff2e555261006ff851aa930803f7ca8ccc98401fbe5c6664c200fdf30333261006ff9a55cd60803f7cd0ccc98401fbe4ca664c200fdf0a533261007ef95299930803f7cd2ccc98401fbe60a664c200fdf34533261007ef9655cd60803f7ca9ccc98401fbe5ce664c200fdf30733261007ef97599930803f7cc2ccc98401fbe5ca664c200dff34aa9ac1007fd93148530803ff898a4298401ffc5c5214c200dff34290a61007fe96248530803feca9a42984017fe6cd214c200dff10555261005ff9b5485308037fcd3242984017fe6d9214c200dff34e90a61005ff9b748530802ffcdc242984017fe6e9214c200dff37490a61006ff9a548530803f7cbaac6b0401fbe60d6358200dff30555261007ef97358d60803f7c592c6b0401bfe5daaa4c200dff374a9ac1007fd95308530802ffd5da42984017fe6cc214c200dff34a10a61005ff9b854d60802ffcda842984017fe6dd5358200fdf36ca9ac1005ff9b808530802ffcdd04298401bfe2e95358200ffd2cb11261007fe97588930803ff442c4498401ffa616224c200dff166d2ac1007fe9a5889308037fc5934ab0401ffa2d6224c200fdf26333261007fe98688930803ff4d344498401ffa61e224c200dff374c2ac1007fe9a788930803ff4d444498401ffa2e2224c200f7f30ec2ac1007fe976889308037fc59b4eb0401ffaa22224c200dff174c3ac1007fe93188930803ff428c4498401ffa546224c200ffd2c311261007fe97188930803ff4c1c4498401ffa606224c200ffd34311261007fe8b188930802ffd5db0eb0401ffa54e224c200ffd2c711261006ff98769560803ff4b9c4498401ffa206224c200fdf164b2ac1007fd8218cd30803fec90c6698401ff6146334c200ffb2a319a61007fd9618cd30803fecb8c6698401ff6206334c200fdf4 else 0xe2c9a14c200fdf2caa92c1006ff9b2685308037fcb1b4298401bfe5cda14c200fdf2c6a92c1006ff96268530803ff4c12a4b04017fe6cc824c200ffd2e4a92c1005ffabb54960802ffcdd104984017feaed824c200bff370292c1007fd8b360930802ffd5da6498401bfe2e9824c200bff374c1261006ff9ba60930802ffd5db4498401bfe699a24c200dff34ed1261006ff9a868930802ffd5dac698401bfe699824c200ffd30499261007fd9734c9308037fcd3264984017fe6d9324c200dff34e99261005ff9b74c930802ffcdc264984017feaed624c200bff36241261007ef96358930803f7cbb2c498401bfe69d624c200bff36eb1261005ff9b858930802ffcdd2c498401f7e5cd724c200dff34cb9261005ff9ba5c930803ff4c12c498401f7e54e7758200fbf3073bac1007df9a39dd608037fcdd2a2b0401f7e6167758200fbf34b3bac1007df9a89dd60802ffcdc2a2b0401fbe5862258200f7f263442c1007bf951a2160802ffcdbaa2b0401efe5c68858200dff34ea8ac1007bf832a2160803dfc99510b0401efe14a8858200f7f243442c1007bfa8895560803f7cb0caab0401bfe6865558200fdf2c72aac1007ef97258560803f7ca92c2b0401fbe1496158200fef30b2aac1007df9a29dd60803f7c992c2b0401f7e4867758200fbf2633bac1007df9519dd60803f7c192c2b0401f7e6067758200fbf2653bac1007df9529dd60803efcc14eeb0401fde6965558200bff36e90ac1005ff9b8485608037fcdd242b0401ffc6055158200bff57698ac1007ff1814c560803fec99262b0401ffc5c55158200f7f2a5442c1007ef9654c5608037fcd2a62b04017feaed5158200bff36a98ac1006ff9ba4c560802ffcdc262b0401fbe6d93158200bff36e98ac1007ef9634c560803f7cdb2a2b0401efe5ca8858200f7f0a7442c1007bf953a2160803dfcb9d10b0401efe5d68858200dff34aa8ac1005ffabb485608037fcd3a42b0401ffc4c52158200ffe2e290ac1007ef96348560802ffcd9a42b0401fbe58d5158200fdf2ca90ac1006ff9a548560802ffcdaa42b0401fde5495158200fdf2caa8ac1007fd9728cd60803fecc1466b0401ff668a3358200ffb16519ac1007fd9758cd60803fecc2c66b0401efe6098158200ffb34b19ac1007ef98258560803fecc3c66b0401ff669e3358200ffb35119ac1005ff9b85c560803fbd2ac66b0401f7e9de3358200f7f51119ac1007ef9618cd60803fec5ac66b0401bfe6862258200ffd265112c1007fe9a288960803f7cb1c44b0401fbe5962258200dff304d0ac1006ff9a588960803fed2ac66b0401ff654a3358200dff2a4d0ac1007fd9218cd608037fc29342b0401ff65463358200dff264d0ac1007fd9718cd60803fecc0c66b0401bfe0c9a158200ffb0a519ac1006ff9726856))) else (if i<8 then (if i<6 then 0xa41007df9839dd20803efcd1cee90401f7e5967748200fbf30b3ba41007df9a59dd20803efcc34ee90401f7e6067748200f7f35144241006ff931aa9208037fca8d5490401bfe586aa48200dff30355241006ff853aa9208037fca9d5490401bfe58eaa48200dff10755241007bf9a3a21208037fc59d5490401bfe596aa48200dff10b55241006ff985aa9208037fc5ad5490401bfe61aaa48200dff17155241007fe952aa9208037fcd1d5490401bfe696aa48200dff30755241007bf8b3a2120803dfcb2d1090401efe5d68848200f7f14b44241007bf9a5a2120803dfc5ad1090401efe5da8848200f7f34d44241007bf9a7a2120803dfc5d51090401bfe69e8848200ffd24344241007bf981a21208037fcd0d1090401ffa54a8848200f7f30544241007bf983a21208037fcd1d1090401efe6168848200dff34b44241007bf987a21208037fd5551090401ffc88a1158200fdf2c6992c1007ff23384560803ff4c1264b04017feaed3258200ffe4ab08ac1007ff03284560803ff899422b0401efe619814c200ffe2a508ac1007ff17284560802ffcdc064b0401ffc60a1158200ffe0a708ac1007ff15384560803ff8b9c22b0401ffc60e1158200ffe0a508ac1006ff9a758d30802ffcdbac6984017fe6cc5258200fdf2c6292c1005ff9ba5d930802ffcd88a4b0401bfe6e93258200bff370992c1007fd9734c9608037fc5ab4c984017fe6dd3258200dff34e992c1005ffabb699308037fcd3b4c984017fe6d53258200eff172d3261006ff9a54c960803f7cb2a64b0401bfe2c9a64c200ffd2eb112c1006ff98568560803ff4c2c44b0401bfe5d5a158200ffd34b112c1006ff98368560803ff45ac44b0401ffa61e2258200ffe2eb08ac1007fe9a788960803ff4d4444b0401bfe54da158200ffb467112c1007f7a5588960803dfd44444b0401ffa4862258200dff0a6d0ac1006ff97368560803ff8c2c22b0401ffc61e1158200ffd467112c1005ff9b50c960803ff52ac44b0401ffa4c62258200ffd2a3112c1006ff9a50c9608037fcc3b42b0401ffa6062258200fdf2ca192c1007fe85388960803ff4a9c44b04017fe6c43258200ffd2e7112c1007fe98388960803ff4d1c44b0401ffa2ce2258200ffd2e3112c1006ff8b5685308037fcdab4298401bfe5d9a14c200dff34e98ac1006ff9b6685308037fcc3b4298401bfe6dda14c200dff170d0a61007fd97358d30803fbca9aa4b04017feaeda14c200dff344d0a61006ff9a5685308037fcd334298401bfe69da14c200dff350d0a610077f8b9685308037fcdc34298401fbe2d9814c200dff34aa92c1006ff9a760530802ffcdd30298401bfe6e9814c200fef2eaa92c1006ffabb685308037fc9934298401bfe60da14c200dff2e4d0a61006ff882685308037fcc134298401bf else (if i<7 then 0xfecbac6690401ffa8ce2248200ffb30b19a41007fd8a58cd20803fecd2c6690401ff62d63348200ffb2ed19a41007fd9868cd20803fecd346690401ff661e3348200ffb34f19a41007fd8a88cd20803fec42c6690401ffaa222248200ffd26311241007fe96188920803ff4c0c4490401ffa14e2248200ffd2a711241007fe96388920803ff441c4490401ffa60e2248200ffd34711241007fd8818cd20803ff4d344490401ffa6a22248200ffb4ab19a41007fda888cd20803fed5546690401ff64863348200ffb0a319a41007fd9518cd20803fecb0c6690401ff65c63348200ffd30d11241007fe9a648520803ff4db24290401ffa61d2148200ffd34e90a41007fe9b748520803ff4d424290401ffa6e12148200ffe26290a41007fe93248520803f7cd2ccc90401ffa5892148200ffd30490a41006ff9a348520802ffcd9a4290401bfe6952148200bff36a90a41006ff9a648520802ffcdb24290401bfe6a12148200bff37090a41007fe952485208037fcd455490401ffa4c52148200ffd2a290a41007fe97148520803ff4c0a4290401ffa14d2148200ffd2a690a41007fe96348520803ff4b9a4290401ffa6192148200ffd30690a41007fe9a348520803ff4d9a4290401ffa5952148200ffd2ea90a41007fe88548520803ff4c2a4290401ffa6952148200ffd36a90a41007fe97648520803ff441a4290401bfe2e93148200bff37498a41006ff9ba4c5208037fcd18a2904017fe6cc5148200dff35028a41005ff9b814520802ffd5daa290401ffc5c55148200ffd2a418a41006ff9a154520803fbca92a290401ffa5495148200ffd364a8a41006ff9a354520803fbcb2aa290401bfe6955148200fef34aa8a41006ff9a654520802ffcdb2a290401ffc6055148200dff34a18a41005ff9b50c5208037fcd3862904017fe6dc3148200dff35018a41005ff9b80c520802ffd5da6290401ffc6053148200dff34298a41007fd9324c520802ffcdc26290401ff658d3148200dff34698a41007fd9a34c5208037fcd2a62904017fe6d53148200dff34c98a41005ff9b64c5208037fcd3a62904017fe6dd3148200dff35098a41007fe9524c520803efcd44ee90401efeaaa8848200f7f24344241007bf831a2120803dfc98d1090401efe1468848200f7f2a344241007bf961a2120803dfcb8d1090401bfe69aaa48200f7f34344241007bf8b1a2120803dfc9951090401efe54a8848200f7f2c544241007bf853a2120803dfca9d1090401efe58e8848200f7f2e744241007bf8a3a2120803dfc50d1090401fbe61e6648200fdf34f33241007ef9a899920803efd444ee90401f7e0c67748200fbf2633ba41007df9519dd20803efcb0cee90401f7e2067748200fbf34d3ba41007df9a19dd20803efca9cee90401f7e58e7748200fbf1073b else 0xa348200dff170d1a41006ff9b868d20802ffd5db4690401bfe295a348200dff34ad1a41006ff9a668d208037fcd3b4690401bfe2a1a348200dff34cbaa41005ffabb59520803fbcc2aca90401bfe6956548200fdf2ecb2a41007ef98659520803f7cd32ca90401bfe69d6548200bff36eb2a41005ff9b859520802ffcdd2ca90401bfe6a1a348200fef5112aa41007f7aaa95520803fbc90caa90401fde0c65548200fef2632aa41007f796195520803fbcb8caa90401fde2065548200fef3032aa41006ff9a754520803fbcd0caa90401fde2c65548200fef2652aa41007f796295520803fbcc14aa90401fde58e5548200fef2e72aa41007f788395520803fbcc1caa90401fde28e5548200fef1432aa41007fd8b88cd20803fec5d46690401fde9563348200fdf4cd19a41007dfa778cd20803dfd4446690401bfeaaa3348200ffd24319a41007fd9318cd208037fcd446690401ff64ca3348200ffd2a519a41007fd9538cd20803fecb1c6690401ff65ce3348200ffb30719a41007fd9a38cd208037fcd2c6690401bfe69a3348200dff34f19a41006ff9a18cd208037fcd34aa90401fbeaaa6648200fdf24333241007ef93199920803f7ca8ccc90401fbe5c66648200fdf30333241007ef9a199920803f7c994cc90401fde68e5548200fdf30533241007ef85399920803f7ca9ccc90401fbe5ce6648200fdf30733241007ef8a399920803f7cd1ccc90401fbe5d66648200fdf30b33241007ef8a599920803f7ca94cc90401fde2ce5548200fef2ed2aa41007f798695520803fbcd34aa90401fde61e5548200fef34f2aa41007f78a895520803fbcd44aa90401fde2e25548200fef34b2aa41007efa6695520803dfd444aa90401bfeaaa5548200ffd2432aa41006ff9a195520803fbca94aa90401fde54e5548200dff3472aa41007f796595520803fbcc2caa90401fde2ea5548200ffe2ed08a41007ff18684520803ff8d342290401ffc61e1148200ffe34f08a41007ff1a884520803ff85c42290401ff68ce1148200fef4ab08a41007fd9a88cd20803dfd4442290401ffc4c61148200ffe2a308a41007ff17184520803ff8c0c2290401ffa54a1148200dff34708a41006ff9a5845208037fcd3c2290401bfe6a21148200fbf4ef08a41007ff23384520803ff92ac2290401ffca221148200ffe26508a41007ff15284520803ff8b142290401ffc60a1148200ffe0a708a41007ff15384520803ff85ac2290401ffc5ce1148200ffe10708a41007ff18384520803ff8d1c2290401ffc2ce1148200ffe2cb08a41007ff17584520803ff842c2290401ffc6161148200ffe34b08a41007ff16384520803fecc0c6690401ff62863348200ffb34319a41007fd8b18cd20803feca946690401ff658a3348200ffb30519a41007fd9658cd20803)) else (if i<9 then 0x6ff962685208037fcc134290401bfe14da148200dff2a6d0a41006ff963685208037fcd2942904017fe6e98648200dff166d3241006ff8b5699208037fcc3b4c904017feaeda648200ffe162d3241006ff9a7699208037fcd434c904017feaed8748200bff370b1a41005ff9ba61d208037fcd434e904017fe6cca848200bff36a54241006ffabb6a1208037fc58b5090401bfe6c5a848200dff166d4241006ff9b36a1208037fcdb35090401bfe2e98748200dff362d2a41006ff8b3695208037fcd9b4a90401bfe5d9a548200dff30cd2a41006ff9b6695208037fcc3b4a90401bfe6dda548200dff170d2a41006ff9a761920802ffd5db4a90401bfe699a548200dff34ed2a41007df8b7695208037fc5434a90401bfe6a1a548200fbf30ebb241006ff9a85d920802ffcdc2ec904017fe6e97648200dff370d2a41007ff1a584530803ff85ac2298401ffc5da114c200ffe30d08a61007ff1a684530803ff8c3c2298401ffc69e114c200ffe35108a61007ff0b884530802ffd5db5090401ff68ce114c200fbf4ef08a61007bfa88845308037fd5542298401ffc486114c200ffe2e308a61007ff18184530803ff8d0c2298401ff654e114c200dff34b08a61007fea2284530803bfc5cb5090401ffc88a114c200ffe4ab08a61007ff28884530803ff89942298401ffc14a114c200ffe2a508a61007ff16284530803ff8b942298401ffc616114c200ffe30508a61007ff1a284530803ff85942298401ffc54e114c200ffe2c708a61007ff17384530803ff8c1c2298401ffc596114c200ffe2eb08a61007ff08584530803ff84142298401bfe69d8348200bff374c1a41006ff9ba60d208037fcd2946904017fe6d4a348200dff34c51a41005ff9b628d208037fcd4146904017fe6e0a348200dff162d2a41006ff8b168d208037fcd8b4690401bfe595a348200dff2ead1a41006ff88568d208037fcc2b4690401bfe2d5a348200dff36ad1a41006ff97668d208037fcc334690401bfeaeda348200dff174b1a41005ff9ba58d20802ffd5dae690401bfe68d7348200dff34ab9a41006ff9a65cd20803efcc3ae690401f7e69d7348200bff370b9a41006ff9a660d20802ffcd8906904017fe6c88348200dff34a41a41005ff9b520d208037fcd3906904017fe6dc8348200bff37441a41005ffabb60d208037fcd1b0690401bfe6958348200bff374b9a41007df9875d520802ffcdc2ea904017fe6e97548200bff36242a41005ff9b221520802ffcd990a904017fe6e88548200bff576c2a41006ff9a5615208037fcdb34690401efe61d8548200dff34ec2a41005ff9ba615208037fcdd30a904017fe6cca548200dff34c52a41005ff9b6295208037fcd414a904017fe6e0a548200dff576d2a41006ff9a6615208037fcc3b4690401bfe6dd else (if i<10 then 0x42a490401bfe69e114c200ffd170a9241007fe9b854920802ffd5daa490401ffa5895248200ffd304a9241007f7953549208037fcd1aa490401bfe6995248200bff36ca9241005ff9b854920803ff4d42a490401ffa5493248200ffd30499241006ff9a54c920802ffcdaa6490401bfe6993248200bff36c99241006ff9a84c920802ffcdc26490401ffaaed5248200ffd2caa9241007fe9b154920803ff4a9aa490401ffa58d5248200ffd2e6a9241007fe88354920803ff4c1aa490401ffa28d5248200ffd346a9241007fe8b354920803ff4d9aa490401ffa2c55248200dff346a9a41007f798554d208037fcd2aa690401bfe6995348200bff36ca9a41006ff9a754d20802ffcdbaa6904017fe6e15348200dff174a9a41005ffabb589208037fcdd2a6904017feaed6348200ffb306b1a41006ff9a358d208037fcd2ac690401fbe6196348200fdf34cb1a41006ff9a758d20802ffcdbac690401bfe6a16348200bff374a9a41007fe98258920803f7cb1ac490401bfe68d6248200fdf2cab1241006ff9a5589208037fcd42c4904017fe6e16248200bff576c1241007bf98360920803fecc1aa690401bfe6958248200dff34cc1241005ff9b114d20802ffcd90a690401bfe6985348200bff36c29a41005ff9b814d20802ffcdd0a6904017feaed5348200ffb2e6a9a41006ff9a360920803efcbb2e290401bfe6997148200fbf30eb8a41007df9a75c5208037fcd42e2904017fe6e17148200bff374b8a41007fe952205208037fcd1902904017feaed3248200dff34a40a41005ff9b5205208037fcd3902904017fe6dc8148200bff576c0a41007ff0a1605208037fcd0b0290401ffa5498148200f7f304c0a41006ff9a360520802ffcd9902904017fe6dd5148200dff350a8a41005ff9b854520802ffcdd2a290401bfe6e95148200ffe302b0a41007fe95258520803f7cb12c290401bfe68d6148200dff34ab8a41007ef9a6585208037fcd3ac2904017fe6dd6148200dff350b0a41005ff9b858520802ffcdd2c2904017feaed7148200dff342b8a41007fe9525c5208037fcd1ae290401bfe6956148200dff106d0a41006ff983685208037fcd9b4290401bfe595a148200dff2ead0a41006ff885685208037fcc2b4290401bfe6d5a148200dff2ecd0a41006ff9a5605208037fcdb34290401bfe61da148200dff36ed0a41006ff9b868520803ff4a934290401bfe68da148200dff34ad0a41006ff9a6685208037fcd3b4290401bfe6a1a148200dff30cd0a41007bf98660520803f7c5b30290401bfe69d8148200dff350c0a41007bf9a860520802ffcdd30290401bfe6e98148200ffd2a450a41006ff9a328520802ffcd994290401bfe5cda148200bff36a50a41006ff9a828520802ffcdc14290401bfe4c9a148200dff2a4d0a410 else 0x55c7e9c751c68dc5f5c55dc4f1c459c395c2fdc291c1cdc161c0f5c089c01dbf85bf19beadbe41bdd5bd11bc79bc0dbb75bb09ba71b9adb941b8d5b83db7a5b6e1b675b5ddb519b4adb415b3a9b369b2a5b1e1b149b0ddb045afd9af41aea9ae11ad79ad0dac75abddab45aad9aa15a9a9a969a879a7e1a749a6b1a645a581a4bda425a3b9a321a231a199a12da0959fd19f0d9e1d9d599cc19bd19b399a7599dd98ed988197bd97259661962195b5951d94859445938192bd9225913590718f818e918df98d618c9d8c318b6d8ad58a118979890d88a18809877186d986158551848d839d8331829981d5813d80a57fb57f1d7e2d7d957cd17c0d7ba17b357af57a3179f1798579457905789977a9776976a576657625756175217489741d73597269722971e9712570b9704d6fe16f1d6eb16e196dad6ce96c256b8d6a196981689167a166596595644d630561bd601d5ed55d615c195aa5595d58c5575156095495532151d950914f1d4dd54c614b1949d148b547c54651458d44f54431436d42a94211414d3fd93e913d753c2d3ab9399d388137e936a13559343d334d320530bd2f492e012ce52b712aad296528a1280926c1254d23d92341227d21b9212120051ebd1df91c851bc11a4d18d917e916a115b1146913d1130d11c510250edd0d690c790b310991081d06d506110521045d036d027d01610018fea4fd30fbe8fb50f9dcf868f6c8f65cf56cf47cf3b8f2c8f204efe0eef0ee2ced10eb70ea54e8e0e76ce5f8e508e3ece278e104dfbcdef8de34dd44db20da30d96cd8d4d810d670d4d0d3b4d2f0d1d4d0e4cfc8ce80cce0cc48cad4c9b8c870c728c638c548c458c33cc220c130bf64be74bdb0bc3cbb78ba04b8bcb748b600b48cb420b330b1bcb074afdcaec0ada4ac88ab14aa24a9b8a870a780a60ca498a324a1dca1189f789e049cbc9b489a0098e49770962894b493c49300923c914c8f548e388d1c8bd48b1089c8888087bc86748584846882c881547f887ef07e2c7cb87c4c7aac790c77c477007668752074307398727c716070446efc6e0c6cf06c846bc06b546a38697467d4668c654464d8646c63d4623460c05fa45e5c5d145c7c5b345a44598058385774562c54b8534451d050e04f984f004e684d204c5c4b144a7c493447c046a4455c4440432441dc40c03fd03f383ea03e083cec3ba43a5c3940385037343670355434383348325831102ff42ed82dbc2ccc2c342b702a802938284827582668257824302340227c216020f420041e641cf01b7c1a60197018d817bc16cc155813e412c8115410380f1c0e000ce40c4c0b5c09bc0874072c05b80470032801e000c40003ff4c2aa490401ffa5d95248200ffd30ca9241007fe9a654920803ff4db2a490401ffa61d5248200ffd34ea9241007fe9b754920803ff45)))) else (if i<16 then (if i<13 then (if i<12 then 0x32d7f2d786d6c2d656d5ead552d4bad422d38ad2c6d22ed1c2d12ad0bed026cf8ecf22ceb6ce4acddecd72ccdacc42cbaacb12ca7aca0ec9a2c90ac872c7dac716c6d6c696c656c5eac526c4bac47ac40ec3fac38ec34ec2b6c276c20ac172c082c016bfaabf96bf56beeabeaabe3ebdfebd92bd26bcbabc4ebbe2bba2bb62bacaba5eb9f2b9b2b972b8dab89ab802b7c2b782b716b6d6b63eb5d2b53ab476b3b2b2c2b22ab1beb126b08eb022afb6aef2ae5aadc2ad56acbeac52abbaaaf6aa32a99aa92ea8eea8aea86ea802a7c2a756a6eaa67ea63ea5a6a566a4a2a40aa3caa332a2f2a25aa21aa182a142a0d6a06a9ffe9f669efa9e629dca9d329cc69c2e9b969b2a9a3a99a2993698ca985e97c6975a96c2965695be952694ba9422938a92c6925a91c2912a90928fce8ede8e1a8d828cea8caa8c128ba68b0e8aa28a0a899e890688c6882e87c2875686ea865285e6857a850e84a2840a837282da824281aa80e6804e7fe27fa27f0a7e727dda7d6e7d2e7cee7c2a7bbe7b527ae67aa67a0e79a27936787277da7716767e75e6757a74b6744a735a726a717a708a6f9a6eaa6e126d7a6ce26c1e6b2e6a9669fe699268a2680a677266ae661665aa653e647a63e2634a62b2624661826116607e60125f7a5ee25e4a5d865d1a5c825c425baa5b3e5a4e595e586e577e56ba5622558a549a53d6536a527a51e2514a50864fee4f2a4e924da24cde4bee4b564abe49fa496248ca488a481e47b247724706469a462e456a44fe446643fa436242ca4206416e41024096402a3f923f263e8e3e4e3e0e3da23d363cca3c323bf23bb23b463b063a9a3a0239c23982391638aa3812374e370e36a235b2351a348233be3326326231ca3106306e30022f3e2ea62db62cf22c862c1a2bae2b422ad62a6a29d2293a28a2280a274626ae2616257e24e6244e238a231e2286224621da2142210220c220561fea1f7e1f121ea61e3a1dce1d0a1c721bda1b421ad61a6a19d2199218fa188e1822178a171e1686161a15561516147e143e13a6133a12a2120a119e110610c6105a0fee0f820f420eaa0e3e0dfe0d660cfa0c8e0c220bb60b4a0ab20a4609da096e092e08ee0856081607aa071206d2066605fa0562049e045e03f2035a02c2022a016600ce0061ff71ff05fe6dfdd5fd3dfca5fc39fba1fb61fa9dfa05f96df901f869f7d1f70df675f5ddf545f4d9f46df401f33df2a5f1e1f149f0b1f045ef81eee9eea9ede5ed21ec5debf1eb85eb19ea81e9e9e925e88de7f5e75de71de685e5ede529e465e3a1e2dde219e129e091e025df8ddf4dde89ddf1dd59dceddc55dbbddb51da8dd9c9d905d841d77dd6e5d6a5d5e1d51dd4ddd471d3d9d341d2d5d269d1fdd191d125d035cfc9cf5dcec5ce59cdc1cd29cc91cc25cb8dcb21ca5dca1dc92dc8c1c8 else 0x1be357e293e1cfe163e123e0b7e01fdfb3df1bde83ddebdd53dc8fdbf7db33dac7da2fd9c3d8d3d83bd7a3d70bd69fd633d5c7d55bd4efd457d367d2fbd263d19fd107d09bd02fcfc3cf2bce67cdcfcd0bcc73cbdbcb43ca7fca13c9d3c90fc8a3c80bc79fc707c66fc5abc53fc4a7c43bc3a3c2b3c247c1afc143c0abc03fbfd3bf3bbefbbe63bd9fbcdbbc43bbabbb13ba7bb9e3b977b8dfb81bb7afb6ebb627b5bbb54fb48bb3c7b32fb2c3b257b1bfb127b037af9faedbae43adabad13ac4fab8baac7aa03a96ba8d3a80fa777a687a5efa583a517a4aba46ba3d3a33ba2a3a20ba1cba15fa0f3a05b9fc39f579eeb9e7f9dbb9d4f9cb79c4b9bb39ac39a2b999398fb986397cb9733969b9603956b94d3943b93fb938f934f92b7921f91b3914790db90438f7f8ebb8e238d8b8cf38cb38c1b8baf8aeb8a5389bb894f888b881f878786ef865785eb857f8513847b83e3834b82df824781af811780ab7fe77f237e5f7dc77d5b7cef7c577bbf7b7f7ae77a2379b778f3782f776b76a7763b75a3750b749f7433736f72d7723f717b70b76ff36f2f6e976e2b6d936cfb6c636bcb6b5f6af36a5b69c3692b68eb687f681367a7670f664b658764c3642b63bf63276263619f608360175f7f5ee75e235d5f5c6f5bab5ae75a235933589b5803576b56d3563b557754df544753af5317527f5213517b510f50774fdf4f474eaf4e174d7f4ce74c7b4be34b774b0b4a7349db49434903489747d346e3461f455b44ef445743bf43274237417340af40433f7f3ee73e4f3db73d1f3c873bef3b2b3a9339fb3963389f385f37f3372f36c33683364336033597352b3493345333e7334f32e33277326331f7315f314b310b309f305f2ff32f872f1b2e832e172dab2d3f2cd32c672bcf2b632b4f2b3b2aa32a6329cb2933286f27ab2713264f25e3251f24df24cb245f23f3238722ef228321eb217f216b20ff20eb207f20131fd31fbf1f531e631df71d8b1d4b1cdf1c731c071bf31bdf1b9f1b071a9b1a2f1997192b189317a3178f16f716b71677160b159f153314c7145b13ef13af136f12d7123f11ff116710fb10bb104f0fe30f770eb30def0d2b0c930bcf0b370a9f0a33099b08ab081307a7073b06fb06bb062305b7057704df0473040703c7035b031b0283021701ab013f00ff0092ffa2ff36fe9efe8afe4afdb2fd9efd32fcc6fc5afc1afbdafb6efb2efac2faaefa42f9d6f96af92af892f826f7e6f7a6f73af6faf636f5caf532f49af42ef3eef382f2bef252f23ef1fef1bef17ef0e6f07af03aefa2ef36eecaee5eedc6ed02ec96ebd2eb66eaceea62e9cae932e89ae82ee7c2e72ae60ee576e4dee446e3aee316e2d6e296e22ae1bee17ee13ee07ae00edfa2df62df22dee2de1edd5add1adcdadc6edbd6db6adad2da66d9fad98ed8cad8) else (if i<14 then 0x3230d14eae1a47431bfed854cc8c34030cf7d1d38ed04adb0d186ffb611d3230d00c30a911c3d6643b6c34030e128dc61a010608a3651d28e50d8695c1b0d00c100990c0330d130d2b810cb010024643c5c346018128dc61a25a95e9f15efe8ed0da0b5b61a49d5dbfa3b43682d6d868e8e81f3df31da095b61a3c86c342c348e843df0d1b81d8e5beaa5432825baf175b61a4d8e484b7fe2a86505adb0d205b0a911d3230d00c35b65beaa547282c34b20e1e3e2aa951ca08fa61a38f5c342e06f7fdb6a9d1da0b0d4c83a09094e086461a283a1ef8685c1104adff6caa54761a99071b0320eae1a22125bfed954a82c35320e3616ffb651ca08eae1a9908478b7d54a8e504edb0d4c840f5f6caa54728259186b002104a861eee0b0d16e2a3a552a394361a57077538687b8dc761a1ee3413f147afb6552a3b0d1d2c28675386888e954a8e1eaa1b0d2b838f5c34ae0684be28f5f6caa54161a3a425bea3943282d6c7570d21213dfd04ad8eae1a325858a3d7db28e505868ef7d1d38ed04adb0d1be2aa951ca0b0d0f730f5f6caa547282c34b20ff1554a8e5047d30d1be2a8e50d8687b95d48f7c3431eb868dc0dc70f7c343f8a2a4470f5c346e0d0eb54e8e1efa1b5b61a3bc5875aa747686d6d868eea61d68ed0dadb0d18415821b38686415c743ad53a1b5b61a30821bd86806106ffb611c3670d4c83386875aa7476b6c34601877cdc61a30453be6e01180c3045484f7d1d3a9d04adb0d1c649df3718680618230c90470e87ae1a172619277cdc61a018608c3d46ce1a1922e4b2390d03e188217360b0d104104a1ed868061464fc516e2d85488ec347018128dc61a01050946e30d00830450946e01180830450946e30d00830451242a4411c83e9868c31cdc04ac34020c1147aa1a07c2e496391d2a950d8695c1b0d2b8100c371868c71822d8e5e9f15efea9d0da0b5b61a4bc5b1db7f54e86d05adb0d21d4d8edbff1743682d6d8690324dc61a31c030c1184101217360b0d14e461a47435bea39416b61b3868c2dc4104ac34030a0546f8c9f8a2dfdb0a9c348484b7c64fc551ca0b5b61a47c551ca187beb6c346484f7c6ca3a753a095b61a41d53706a70d00c30467be8e9c768256d868c218168080b0a1b0d1864a3a552a3b0d2b8323ac34ae062082c0b9b05868b6197a7c57bfaa747682d6d86927236fea9d1da0b5b61a3edf1b3f1747682d6d868ee3ac36dff8baa7416b6c34816e2081184a05b868061c6f8c918a2dfdb08ec347552a39430f778badb0d1c061d53706a70d1823010f8bedb0013fa03f9c3f983f8ebf87ff813f77bf70ff6cff637f5cbf55ff4c7f42ff397f2fff23bf14bf0dff073f007ef6feeabee13eda7ece3eca3ec37ebcbeb07ea9bea03e9c3e983e917e8d7e897e857e793e727e6bbe64fe5b7e54be4b3e4 else (if i<15 then 0x8a2482561a018416e12b0d18e0185095868c700c20df193f145bfb615208c0442202020b0d304701091c3df0d1647422b0586882384481002aa3b0d18088df153a38e41b8c34618c12454da95043d70d0b930f6d53a38e41b8c34618c1236fea9d1c720dc61a30c6091b7f54e8e3707230d18630481521286161a018518a238410f5c342e4c19464fc516fed854882c34871d60b6ffc5f6daa74361a40dff8bed85488ec34030e0f90d01502241b321ad4e1a20860101624361a28df193f145bfb615208e020868440430d306c1d5190f170d141784ac340308364eae1a18af1907570d10088c9f8a2a4431df371868c124648cbd53a3b431df371868c12408a8e3be6e30d182303e4340540893e28a910c3d70d1b834c80f086832c86289250c754d4e1a31c61be327e28b7f6c21b0d1c490df16fed8411d5353868c72747001434302237c431d53706a70d18240b711c2a42561a0186022a38ea9b8353868c11c6f8c918a2dfdb082c34791c0f90d015022511ca087ae1a172511c12adb61a0185f8a2a4410f5c342e4c37fdb0861b386864983084a3e98680614040c9f8a2dfdb0a911c19c4161a5008d1c7210d20028784341943091c3582dbff17db6a9d1d869160911686c34475360b6ffc5f6da3b4361a46dff8baa4dc68ed0d868ef16c16dff6daa747686c348f8a3dfdb6a9d1da1b0d1d6ffc5f6caa511286c35801072111096ffb65043670d1416edfd1c720dc61a30c6090b7c64fc5552a09db61a3a8e3718686b7c64fc5f6ca0b0d196ffc5173ed94361a37c5552a187bbb6c34649cb7c5cfb6552a19e2e1a428e1b2889d4e1a29b8444202ab7c64fc5f6caa70d1c0aa8e444e0b0d156ffc5f6caa511282c358010f7ec37c5f6daa747682c34876d61b6ffc5d53a3b4161a41c8dbfedb54e8ed05868ea39113a9c344022a3b6fea93906e30d18630491bfed8470821927570d4c8402dd1da18ea9f4353868e0bd4368ed04754fa1a9c3481c5a1b411d53e86a70d1f436823aa7d0d4823368ed0da08fa1df3aa6a70d2347686d04754fa1a9c34705e23b430823aa7d0d4e1a40b70943ab0d00c284a35208c06101784ac3403082dc251a9c34030a37c64fc516fed80408e8640b44161a5bb6845a1a47682c346b6cb7fe2a86505868c363db0ce1967570d2c83a8e444ea70d101f2dff8aaa54361a370711c2087a8d9c353205c9c1f28ec346e09f145488e1047d30d0b938c98743d70d0b92fc505a6e07adb6c346b6cb7fe2aa950c8894161ac00978b6db6fea9d1da1b4161a423a07cb7fe2aa950ca0a473b6c34ab6d868060c5bdc5c3403096d9272df552a19413c5c348c34ae057157a3dfd53a3b43682d6d86928e8612df51ca19411d5d6d86928e8613dfd04ad8eae1a384a3e986806106461a01831bfed85488e991868061c6c008752 else 0x302b80040101188ec004025868c1022c005c001c00116e0eb5b6002022c0021eb800408b00082739830580080fb00085b892c00304780040b45ba82c004044ed8c160024c8c340307b7f54e82391adb0d18e30c8018b230d0c64c3a1eb8685c94251b8c3402300176ffc5d53a38dc686c3474b0a19d4e1a23dff6daa747682991868eedb6fea9d1da0a6461a3ea91ea7230d18e30c2e4fb7f54e82c00680e46b631c61928256ffc5552a3b0d1b83ba9b05b7fe2fb6d1da1b0d22db2585beb1547282c3471c5aa7411c8d6d868c7186438edbfedb54e82991868eb20dc61a18d8dbfa08e46b6c34638c323e28f7f6daa747686c347b52b7fdb28e504b230d60042dff6caa40628e59186b0022c16dff6daa74761a5907412b7c6cfc5f6ca3b0d1defda9f8bedb47686d0586907576ffb6d1da0b0d2c83bb6b53b7fe2e8ed0da0b0d22c72585beb17db282c347b6c8496ffc5552a0b0d1c5b98e09586b0000c325850c031d4e1a2889dbfaa4e46b6c34638c3234302243480083df0d4b81a0950ce0b0d112c286753868877c7ae1a17241eb8685c0c168f7c342e0819c30fb6552a39414c8c34811c3d4e41a9c346185c9c7a9d5353868c70b9358e0cbf17db2a9505868eea6c76dff8bedb43682c348f8aaa5470f776d868c2387a8d9c343265c18061b8c3435be2e7db2a951d869641f470f53906a70d1861727f8a2e7db2a951d868c3dc6ce1a1932e0a8496ffc5173ed954e1a3adff8bed95498e505868eedac76dff8baa743682c348dbfa08e46b635208cc31d6ffb651ca08eae1a323c5be367e2a8e504edb0d2104a86705868963b6ffb6d53a0b0d2c838f54340f85c90dc21a01835bfed9472821b3869641defd8ef8bedb54e86d0586916396ffb6552a096461ac008371868060f4302231c86886e10d00c4004352b230d0fe288e10c3d70d4b8358e412b7fe2fb6553868e8254361a37040202496ffb6552a0a6461a40f71703d30d12db2df552a39412c8c3580107d2db7c5d53a3b43682c348b1c3d70d4b61725b6db7f54e8ed05869641c5b9a90958680616c72dff6caa54161a5907371868060e5b0e2c343dc82a47a9c8c34638c30b93808124b7fe2fb6552a08c761a48861ea754d4e1a31c2e4e02017adff6ca39411d5c348b523d65b61a17254b0b7d628b9f6ca3b0d1d1d0bc5beaa547282990edb0d26c723c5bff1554a8276d86908496f8d9f8bed94161a38f54340f85c900402f50c7570d165b0eac343dc823ac70d9c34320a2385be1a19c030a37fdb0821b386a64187b7c5d53a18fa61a31c7124a1be2ea9d047d30d18e47c5d53a1b416003407d0c720757c5d0da08fa61a31c71ef868dc0fe2ea9d0da08fa1dfc346390324676a9d0da08fa61a31c8124327e28a9d0c208fa61a31c991d86842dc2561a1c4030a128dc61a01060))) else (if i<19 then (if i<17 then 0x60488b4c085b8ceb8b80080fb0d2221e00425a614312db223d303444f174c0d1161a1222c01a6147110961a4443c001c0088b4c28e260049c88b4c1300262445a60888b4c09116981222d30216e23b000c44982c003021a61476002186d318006a60436001982d31800780020574c600181070d8006040e2e98c00416e2254c60020b7021a63001064889531800832408698c0040206db4c08ec00502b86b000d4c6001089531800780020e8ef98ec00402123b000c1d18ec00316f8004041eee001adf531800608f000844810d3180080474c28ec004b04a6011e0020b7075adb0010082a9d3180082dc1d6001e0008105bfa63001008e8ec358009800288b4c0864a22d30330c88f4c0d1169810b7c00244586842df000911698160007da61472822a22d3024458684325116981eb6c00249c88b0d0d31222c3434458034c0cd4e0010c9445a6062df0009113dfc01a60980038000ae9851ca08ae0b4c09116981222d30219288b4c0f00262445a608889db6981815c348886e0b4c081d0b7c003c0088b4c28e2600445a6062df000b0024e445a60888f4c08196001423d302021a605239c16981810d302021a6040434c0a11e981422d3161b00135b298c003021a6042dc7160018f5c0020742df000c5b83ad6d800888b4c08c7600101076da60688ac360018b71bfadb001044e98103a16f80062dc1d6b6c0043538004088c160018b7c002c00107477cd4e00260002024b4c11113c5d303445a6040404961a19a9c00253161b000d4c586c00353161b000cdb698c00330d80042274c60018b71bf80062dcefe001986c002023a614760020b7c002c00105a0434c08ec005353a63000cd4e98c003152a63000c16e0010b705aa6300105b810d3180080e85be001e9805a202386b000c3102273060b00141188ec00376d8005ad9416001e9891d20b00100869891d800860809698905800a60811698c004d3061b000c1f022d3060b0014c104ec00330418811600229810580063d86fdb6531800a2df00085ba9810580080fb4c60018c953020b00130004c3600161a30d80062274c6001e000811d30a3b0012c129804780080434c6001d82192a6011e0028b7075adb0010080c978ba6300145b83a38badb001408e1ac00316e0eb000c7b010d3180082bf00086fdb6531800860b4c60018b77e9263001162a82c003c358004a63000adb698c00316f723000cc1698c00316f6e14c60020b7b70a6300105b810d318008324081b6d31800a2df00081f61ac0031960434c60025c5531800660b4c60018c91977154c6002982d3180062dc65a98105800a60b4c60018b7021a6300115b03a3538008f1700085ce0016000ab607463b001300047ae0016000e0009a9c00207c08b0d182c005c001045868c160026000e0008b7075adb001300074c48ec00 else (if i<18 then 0x6c00284786a02422c005731660c3182c005352e62cc182c00576ce62cc182c00578ae62cc182c0053bee62cc182c005434044008ddb61ac0031c1a63000c5bdc510d80083247b5b6531800a6db0d6001ab6531800661b000811e1a80804300164c086c0031bf263000c64bc89318008e1a4c6001c98c002c3580040eae29a9c00402b86b000ddb498c00378b263000ee2e0010b71792630010d4e001092d3180066a700085b83ac00312586b000c08698c00316e0eb5b6002698c002d3121b000f000432e1ac003531800508f0d008845800aed9cc59830d800af15cc59830d800a77dcc59830d800b6da11698c00416ea63000c08698c003045a60c3486c00516ea60436002698c002390f154c086c0051a1a63000c32e98c0031780434c6002089d3180060434c28ec00430da63000c5b8bc53021b00145b810d3180082dc0869811d800b868c16001810d3180062dee4298c0041a186b000edb698c0034741475ad84e611d0b00051d6b6124247425e88e850eb5b0f7c00447580048e87ba821a3a1ee216f0eb000d1d0f7504305a2e46ce002386c003d463d51d09c30f5123a1ee2875adad48d5c600123ab53800780038002f1700085be00123ad6c24788e95c0f00051d051d282123a08b7c0024758035b0d1d051d051d6b6123a184216f0eb000c5bc3ad6d800980023df00085bc3ad6d20b00141d0f7c00317320b000cd483a1b380083d51d3c518b707520b00105b882c00305b0eb5b600243a16f8006a63000a1d6b61ef80080ea4160018b787461a41600283a31d20b001016e0010f5474271c3d448e87a887aa3a10f5474216e20b000c44c3ac003112327000cc303ac00330c0e864e00203a17380062de1d60018b707580060e85ce0018b711380062de1d1c5c0041738004ad816e001a3a0a3ad6c24788e95c0dc3051d051d6b610b9c0024848e852e300091d6b612dd47425e88e842de1d6b6c004875adac70e1d6b6b1c3875adac70d5c60013a9046247561b000c49051d0bc570307580040eb00085bc3ac003b0d80048eb5b3a91a3a78a216f0e9e2e00223a0b8616f80068e822dc496001a3a50424758035b0dc30b7c00370c08c42de1d6001a3a08d9474297180048eb5b0b00051e23a57039718004e1828eac760018d94742475ad842df0009cc23a138ec0021b28eb5b0d6ea3a12f4474216f8005800224822e6416001a3a0a3ad6c24740f9cc0f0006c7600158ec002352e1b000c1d0b990580088e828e941081d482c00317320b000d1d0d9504316e32641600223ac01ad872e300085b8cbb8a20b00151169810b707580069391161a1a624458686e0a11e0019dfc002020227000f0006c101191d800804016e00181077180063d70008080cbc00370508f000c080f676d80080405e60018107918006041c16001a22d302445a else 0x752a184f7c2a1b000b0020950ca088e0b00080ee03800202022f0dc60018bcc002c00119060b000c65e001182c00276d800402243600198202520b00112c3c510bc01920b0010c160012981058006057000962882c00338b21b000c5b882c003179800420b0008db482c0030b0025e280c905800cf7c04600180c3058006030c1600180c3058006031db6001e000e0008b9c002019800580038002049cc182c00402b80042e7000b0007000700042c3c53058008025e280cc004c001c0011058004054cc6001a98c002b04a63000c046001582c00201180040b404086c004352367000f00040660010080b0a1b001016e00102dc00205aa63000cc10b9c00358a20b000c04058c00305a2e441600200816f80066a7000ac12c5c003011800560864e001808193800760b0008046001008c00231d8004033000804012c0030106db000cc10b9c00353020b000c04012c00358b800402300085c882c0030102df000c250c9c0030103244360026000e00084a0a86c002c00825432822382c002c001705800407703d4580022f0066001a090e007042c00849470f0025878aaa543151e3b6138ec00200f50e0050c2c0013bf8004f142b21e2883c1f4104a7be2705800412b00082505dc06e2b82c003478ed84824250825042506e2b8ec0030941424e60250c250425046c04a104a084a76ca08602030880408ec0030100b454e002008770edb0010040f61beedb00140438ec0030118004021db600180871d8006849cc08046001008184edb0010043a9c0030103ab000c0460010087e98006023000843008c003124e600460020d878a0230010040e2c00371d80043d42f5438002961e289d4847abdd123c76c2590f14477c212aefe001e0008f63beed94110065dfc003c001c00020308c7106efa98c0031d41bbeb17000de286efe00143a70c212580050eb5b38e198ec0021240eb000e1d6b6752370d8005c8c5cc3a1182d3180062e61d3c518b9874216e0e96feb6c0051730eb5b0dc70b9143a17221730e850eb5b0f71b861722b6ca63000f4c600109216f80062dc11e001e1ac0021122df000d4c282c00316e0eb5b6002186c00216f86b000c5b83ac00316e24b000e11e1a8758008f16db398b31800a2dc1d1c5c004044868008c5b892c003c001c342df000c64a3a10b787580068eb5b085bc3ac0034848e842de1d6001ba908c9475ad862e61d096ea3a12f4474216f0eb000e1d586143ab0c28756184224c3085bb8ec00316f0eb000e1d6b61ee31730eb5b0d1d6b671c30742dd54e00223ad6cea468e941091d06c30b7c00316f0eb000d1d600d6c316f8004e3828e822245ba82c0041928e848eb5b09cc23a138e0a3a192a08786b000b0d60010b77bb26300105b882c00307cedb0d60020c99318006f170d6001e1ac002b6c08b4c600218)) else (if i<20 then 0x88b4c0911600d30a38884b0d2221b86c01a6078011169851c4c000f911698260049c88b4c1300262445a6082e5116981a22d30230488f4c0dc3600d30319212b000c32998c0035318004f17000819008c00316e033000c5b808c003c001011800432f000b0d6001015c3580062dc61498c004192f564c60023a9047263001075498c003c358004f170d60018b77bb26300105bbf4931800824811e1a0100430018476001198305800633864e001dc553121b0010648ceb8b80082dc67486505800a63864c86c0040103224360020c901021b0010713b61eaa0b001404282c003124a1b000ec72c5c003010aa7000ec70c9c003010325e2e002092d0d80063880460018df531800638962e0018d03318006757000864808c0031b1800402141600182f50d800602147600182fd0d80063a80460018df58b8006edb0d6001bc5c00219212b000ce2e0012c5c002044023000c5b80cc00316e023000f00040460010d80100b70010753b61eaa0b001464bc59318008341e2e1ac004c3580041970d6001823021800608ecc6001bc5353660c76002bb6b3063b0011e2d9831d800966300085bdd550580083085be001db61eb8006b16db60019a916f80066a45be00180807980063085b8a9c00416e023000c5b808c00338a60b000cefd9831d8008f7c2a1b000b0020950ca088e0b000b0005dc046c85c160013b6504205a367000d0485c16001600424a3868f1db0b002df1006ca8611a971d80060c0013538004f7c263b430ac7600158ec00209563b000ec7600158ec002305800463b000ac7600160001024866a700080019d801430c710404092730358b63b000ddb58e5058008129e2d8ec00401963b000ddb5a95058008a1b000b0020950ca089800201bd80043d94109049b81600424a386849cc0b000785be371d80040c00a1840b6d8004849cc09ea8416db000b0025878aaa54315c760010d97ba27e81478ed84365e289643c51000f7c202017bc51da990c2b5321856a543600180cc0020196a7000f0000805ef15431416a54c60018c208ea09a9c00217203042e406085e00c100c78a259003040302030321ac16001c86b058006194321ac1600180cc00201810198004031db08d4e00129831d60b0011629a9b058008129e2d82c0043bf60b000c25486b058008031c7600180c752a186031ef8b002120183c00961e280c50c5c002f0060f0000c100cc00201810181019801430c06600100c0a1273003060330008060b9100c080cc00201814b0f14060c060b913b6504204780048242e08118b0025878aaa543151e3b616000cab7c607aa1010e3b000c008f00092c3c513a904627ba17e81478ed84f142b21e2880ea41188043df1008c0020101010ed9410c04600100808080808c0020101020249cc008238204624742f0060c338610103 else (if i<21 then 0x3538007714d4e00180890d800771454a98c00416f71454a82c00538b80047170008d4e00101235380066396fc8ec00458a23b000ce2e0010b711ca0b00130004476001065c002b520be4360020c2c0020b0f17000f000700046ce0016000e000e000812352e6300104360013c5c00210d80042a54c600198ec00258a23b000c5ba82c00301077c5be00204a15236700106480810d8008023000b0006db60012c553180062df000adb0f5c003b6ca63000c5bac5c00331c2df000c0403c31d80082dc2560018b701021b00105be0011c533180076db00080403c31d21b0016db298c0030100f3000d62db6c003b6d80041e3000a6fe001008c002353800437d62e0018b71beed9416002808c002124a1b000ec70b750580080205be001808c00212580040230008d48d9c0031bea60c76002182173800632c5c882c004304327000c040c8c003196327000c6480836d800832f000b0006c1298047800923b000ac12c5c003011800560864e0018c901980063d804482c004b6d8004032db6001db6c00201120b000c7b5b653020b00140460010c901180060b70008041b6c00338b8004b170008dc0f5c003c0013042f3000c5bdb8531800832465dc5c0040102f3000c5bdb8c00316e023000c5bdb8c00316e023000c5e60010cb193800771406182c0041b3800432465a98c00416f6e162e00200cc0020198004055cc00cc00416e031db60020c9019800603300080660013c501980062dc0660018f658b6d84160028bc0198006324063c5c004196033000c063b6c003012033000dcc00c3058008f1406182c00476c030c160023c501860b001006182c00316e033000cc10b990580083824160018c90956d8416002db610580060230008db60012b6c002c00173008f000c11008c003192033000c04032c003c00101180040330009e280cc00376c033000c06600100cc00201980042dc063b6c00478b80041e0c160018b7c00216e0b7000c5bbc5b6d20b0016db43ac003178033000de2db6c0033bf6db000c045c5c00316e023000ee29a9c003095717000c11008c003064023000c04067c003c00176d80058002195cc600187876d80077170009e2e0010cec00278ae63000c5bbdd78b80082ddfa4c5c00478aedb000c64bc5c0031b0f17000f00045b84ac00305b8005715db1a9c00478a6a7000c6c04ac003b8b800477ee29a9c0043bb80042deeee0018b70118006378c16001bc5c002445868488b4c085ca22d30317288b4c0c1f222c343445a6049391161a1a62445868688b006981867c002021a61475822422d3123ac1121169891d608888ac16001889d302445a604889db698181002386878002a62c16001c22d3123ac110308011222d30e1b0011113a9d30a388889efe00d304c0084b4c2862223d302444f174c0c5ca22d303445a604 else 0x3ab000b000700041e1a9c00378b800436700086404ac0031b180058002a62c16001832c00278b80052a643600183c)))))
def f3863l11 : Packing := (1554,4,7,11,4,16,0,f3863d11)
def f3863d12 (i : Nat) : Nat := (if i<1 then 0xd64019e2f6d0d50ca0f0a923ac8208f72ddf4f15b686a866e1b54d0cc74757a78b5b4355c245837cc57548eb2082f17b66a61aa1994750cd4c757a78b5b4355c25c5a3a3abd2b67561a722b84d53471e87ad0cefc75e2d6d0d570b048df2a6c820bc5eda1a63a8650747a78b0d17050e886bd3c5868b830b0433abe2f6cd4c347024df2a48eb21b8033c5eda1aa198265534730d1d5e9e2d6d0d5709c5970fcc1af020bf56f58bcaeeb8b98ee0eb6bed50b4b6d00b286c24aec6b52ab56a58a80e986a4ee8aaa0b67d89d6e6de99ae62097a65b294fe4fe92064368ebe3328a8626a891e1c084e60b280adfd67d8dedc7955e0a774dd7473b5c5c701db8a6cfdacc69659c8655590061e58245f157345b5563a579555e535d4784f4d3744bdd2a2495d1da463d130427d0223f34f783b74e88382cd8434bccd031c4bfe2e7cb2c2b5ca7827ec9a6251c8e8222483e1f547761cd46d619dc60e1694546141449c10543b60ce42da09ec208067c168049c0dc017c000ffe28d20803ff9a348200ffe59520803ff97548200ffe21520803ff98548200ffe29520803ff9a548200ffe5d920803ff98648200ffe69920803ff8814c200ffe69d20803ff8a848200ffe6a120803ffa114c200ffe88930803ff8214c200ffe48530803ff9314c200ffe14530803ff9514c200ffe58530803ff9714c200ffe61d20803ffa1148200ffe8cd20803ffa5548200ffea2120803ffaaa48200ffe48520803ff83148200ffe4c520803ff85148200ffe54520803ff96148200ffe5c520803ff98348200ffe60520803ff8a148200ffe68520803ff93248200ffe54920803ff96248200ffe60920803ff85348200ffe54d20803ff96348200ffe5cd20803ff88348200ffe20520803ff85358200ffe8cd60803ff98558200ffe5d560803ffa5558200ffe68d60803ff92158200ffe4c560803ff98358200ffe54560803ff9a558200ffe5c560803ff98158200ffe0c960803ff93258200ffe14960803ff95258200ffe5c960803ff95358200ffe60960803ff9a258200ffe5cd60803ff9a758200ffe88960803ff9a24c200ffe20930803ff9634c200ffe5c930803ff9764c200ffe58930803ff9324c200ffe69930803ff9a14c200ffe61d60803ff9a858200ffe60930803ff9814c200ffa88920803ef96358200ff68cd20802ff9a758200fbe99920803ef96558200f7e9dd20803bfa8848200bfe69560803fe92148200bfeaa920803f7a5548200bfe68530803fd9314c200bfeaa930803efa664c200ff68cd30803fea224c200ffc84530802ff9a848200bfe69930802ff9a748200ffc84560803ff21148200bfe69920803fda3358200bfe69520803f7a5558200f7e9dd60803bfa8858200bfe68d20803ef96158200bfe68560803fe95248200bfe68520803fea2258200 else (if i<2 then 0xb7fc5ed98ea3a866a58286996ff8b54d1d43434dc1cc932c0877edfed9a9aa58ea3982868c869c40478bdb35354bbec750cc15050d3008f15b63dfb66a6a963a8ea188277d82869c253710d010c114098680c1824efdbfdb3535481047305411910d10cd161dfb7fb6020a963a8e60a823221a219a1e3bf6fb5354b1d4730541190db434433461020dfed9a9aa58ea3982a08c8868866dbfdb50d413aad4c34c7200877edff17b66a58ea1982a0a1a596e043bf6ff8ad4d52c750cc1504db434d324ce021dfb7fb66a6a963982a0a1a321be2d5343504fa434c71ddf6e21a03182296f6fd0d413ab5b3530d31c90e9dfb7fc56a6a961a8660a8263ab6869a5b9d41d78ad4b1d4730d43305411e95b434e2dedfa3a86a0ab67561a4074efdbec751cc350cc1504ead6d0d33c56a5860e8f5868b93bbfe2874d4d52c751c5cb0d0d170b77fc50e9a9aa4b963986a1a1a2e165b9c41d78ad4d52c730d43305411e95b434e77fc50e8b96a58ea3986a1a1a2e162178ac730c1d1eb0d1728325df0e8b96a6a963a8e61a867161a2e1a1d5534750c7b9e90d17082dedfaa682722b68698e61925b9241d3bf6ff8ad4d52c730cc15055b434e2dedfa3a82722b66a61a61925b874efdbee29b3e2b1d47352c33054156d0d3cb7b7ea9a3a82ada1a72105b874efdbfe2b52c730d433054156d0d34b70ebc56a6a963a8e61982a08f4ada1a6879e2b52c70745c1eb0d1729324b73383a77edf6a6a963986a1982a09c5ada1a81bad4b1cc30747ab8b0d17290e9dfb7da9aa58ea3982a09c8ada1a6024eff8bdb3530d3041122a9a3a82721f486986387ceff8ad4844c350cc1504db4344732dfedaa9a3a82869c83dbf54d1d43504eeb8adb43492dcbc089dfb7fc56a6a9a398660a826da1a7024eff8bdb3521102043305414344731dff15a986986609b60890eff8bdb3530d30d000448324b70e9a9aa58ea3986a1982a08f4716b6869fe2b52c730c1d1e90d172808bc5ed9a9aa48ea39df61982a0a1a6045e2b6c7bf6cd4d534730d433bec1434db7ea9a3a82323b68680c40747b96e5b1e9e2c34c71709b7ea9b218ea0bc5eda1aa192471b27b9bb7a38b5b3ab0d3915c2ea96da8eb21f4f161aa19b84884ea8747b96e5b1e9e2b530d170bb7e8e12a82ed9d5868c8455347590efd05e2f6d0d50c9109d5238863dcb7bd3c5ad9a986ab86012433700678bdb434c120df2a48e208c8eda1a8000c4dbf47590d4d05e2f6d0d50c937ca9219b8f17b686a8e6092473701178bdb434c11cdf2a4860888223bc5eda1a801554b6d43444fa78b0d51cdc242204282f17b6868d6fd52c35051178bdb4354726dfaa582a1a22f17b686a8e4be85491d64104eff8bdb4354328a9218f72ddf4f15b686a8e6e146f91c648944176ceac3464243aa1af4f16b6868cc15bf54d1 else 0x4a8698e0308093bfe2f6cd4810c750cc1434a2dcc2021dfb7fc56a58ea3a8660a826da1a75bfdb51d413ab0d1907a3a86a09d57d1a9868e75011e2f6cefb52c751d4330541434c129a98680c20b0efb8be2f6c04352c750cc1434bb7ea9a3a82775b6868c8478b54d1d43504fa36d0d203c7d3c56a58ea19b86da1a4f8b548474750cefb710d304912a1a3206253e90d0184021dff17b66a58ea19828692113bf6ff8ad4d524751cc350cdc434c089dfb7fb66a6a9a3982a09c886976fd5211d1ce43710d30cc12489089dfb7fc5ed9a9aa68e61982869808bbfe2f6cd4844c350c081050d11ccb7e8ea19d56e1a986982405a113bf6ff8bdb51cc350cd4b050d32dff16a9a3a86869b8399265844efdbfdb35354d1cc350cc138b0d38c9021dfed9a9aa58ea3982a0a1a3218eff8ad4b1c433710d0188021dfb7fc5ed9a9aa68660a8263a1a6010efdbfdb31d4710d43305413ab0d3008f15a9aa58ea3a8660a827d21a5bbfdb352c71910d0187024823221a030adc434c7018c1140877edff17b66a6a9a198e60a1a5baadc3530d018c1182d021df))
def f3863l12 : Packing := (124,3,7,11,4,14,0,f3863d12)
def f3863d13 (i : Nat) : Nat := 0x2a51c861d3d38ab60d2e12df54a190422e2ed8348e4b7d528e6420b8bb60d219358ac01ff960803ff261007fe48200
def f3863l13 : Packing := (3,2,7,7,4,8,0,f3863d13)
def f3863levels : Nat → Packing
  | 9 => f3863l9
  | 10 => f3863l10
  | 11 => f3863l11
  | 12 => f3863l12
  | 13 => f3863l13
  | _ => emptyPacking
def f3863index : Nat → Nat → Option (Nat × Nat)
  | 9 => fun _ => none
  | 10 => lookupWord 25 109 7 15 7 4 (hashf3863l10)
  | 11 => lookupWord 671 2255 12 19 11 4 (hashf3863l11)
  | 12 => lookupWord 610 2343 12 19 11 4 (hashf3863l12)
  | 13 => lookupWord 49 201 8 15 7 4 (hashf3863l13)
  | _ => fun _ => none
def f3863 : Forest := (511,13,fun j => deadsamples[j]?.getD (0,0),deadcolumns,deadautos,f3863levels,f3863index)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_9_0 : block f3863 9 0 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_9_36 : block f3863 9 36 35=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allf3863_9 : block f3863 9 0 71=true := (@block_merge f3863 9 0 36 35 sf3863_9_0 sf3863_9_36)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_10_0 : block f3863 10 0 16=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_10_16 : block f3863 10 16 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_10_52 : block f3863 10 52 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_10_88 : block f3863 10 88 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_10_124 : block f3863 10 124 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_10_160 : block f3863 10 160 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_10_196 : block f3863 10 196 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_10_232 : block f3863 10 232 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_10_268 : block f3863 10 268 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_10_304 : block f3863 10 304 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_10_340 : block f3863 10 340 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_10_376 : block f3863 10 376 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_10_412 : block f3863 10 412 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_10_448 : block f3863 10 448 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_10_484 : block f3863 10 484 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_10_520 : block f3863 10 520 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_10_556 : block f3863 10 556 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_10_592 : block f3863 10 592 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_10_628 : block f3863 10 628 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_10_664 : block f3863 10 664 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_10_700 : block f3863 10 700 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_10_736 : block f3863 10 736 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_10_772 : block f3863 10 772 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_10_808 : block f3863 10 808 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_10_844 : block f3863 10 844 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_10_880 : block f3863 10 880 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_10_916 : block f3863 10 916 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_10_952 : block f3863 10 952 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_10_988 : block f3863 10 988 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_10_1024 : block f3863 10 1024 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_10_1060 : block f3863 10 1060 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_10_1096 : block f3863 10 1096 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_10_1132 : block f3863 10 1132 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_10_1168 : block f3863 10 1168 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_10_1204 : block f3863 10 1204 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_10_1240 : block f3863 10 1240 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_10_1276 : block f3863 10 1276 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_10_1312 : block f3863 10 1312 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_10_1348 : block f3863 10 1348 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_10_1384 : block f3863 10 1384 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_10_1420 : block f3863 10 1420 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_10_1456 : block f3863 10 1456 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_10_1492 : block f3863 10 1492 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_10_1528 : block f3863 10 1528 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_10_1564 : block f3863 10 1564 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_10_1600 : block f3863 10 1600 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_10_1636 : block f3863 10 1636 28=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allf3863_10 : block f3863 10 0 1664=true := (@block_merge f3863 10 0 808 856 (@block_merge f3863 10 0 376 432 (@block_merge f3863 10 0 160 216 (@block_merge f3863 10 0 52 108 (@block_merge f3863 10 0 16 36 sf3863_10_0 sf3863_10_16) (@block_merge f3863 10 52 36 72 sf3863_10_52 (@block_merge f3863 10 88 36 36 sf3863_10_88 sf3863_10_124))) (@block_merge f3863 10 160 108 108 (@block_merge f3863 10 160 36 72 sf3863_10_160 (@block_merge f3863 10 196 36 36 sf3863_10_196 sf3863_10_232)) (@block_merge f3863 10 268 36 72 sf3863_10_268 (@block_merge f3863 10 304 36 36 sf3863_10_304 sf3863_10_340)))) (@block_merge f3863 10 376 216 216 (@block_merge f3863 10 376 108 108 (@block_merge f3863 10 376 36 72 sf3863_10_376 (@block_merge f3863 10 412 36 36 sf3863_10_412 sf3863_10_448)) (@block_merge f3863 10 484 36 72 sf3863_10_484 (@block_merge f3863 10 520 36 36 sf3863_10_520 sf3863_10_556))) (@block_merge f3863 10 592 108 108 (@block_merge f3863 10 592 36 72 sf3863_10_592 (@block_merge f3863 10 628 36 36 sf3863_10_628 sf3863_10_664)) (@block_merge f3863 10 700 36 72 sf3863_10_700 (@block_merge f3863 10 736 36 36 sf3863_10_736 sf3863_10_772))))) (@block_merge f3863 10 808 432 424 (@block_merge f3863 10 808 216 216 (@block_merge f3863 10 808 108 108 (@block_merge f3863 10 808 36 72 sf3863_10_808 (@block_merge f3863 10 844 36 36 sf3863_10_844 sf3863_10_880)) (@block_merge f3863 10 916 36 72 sf3863_10_916 (@block_merge f3863 10 952 36 36 sf3863_10_952 sf3863_10_988))) (@block_merge f3863 10 1024 108 108 (@block_merge f3863 10 1024 36 72 sf3863_10_1024 (@block_merge f3863 10 1060 36 36 sf3863_10_1060 sf3863_10_1096)) (@block_merge f3863 10 1132 36 72 sf3863_10_1132 (@block_merge f3863 10 1168 36 36 sf3863_10_1168 sf3863_10_1204)))) (@block_merge f3863 10 1240 216 208 (@block_merge f3863 10 1240 108 108 (@block_merge f3863 10 1240 36 72 sf3863_10_1240 (@block_merge f3863 10 1276 36 36 sf3863_10_1276 sf3863_10_1312)) (@block_merge f3863 10 1348 36 72 sf3863_10_1348 (@block_merge f3863 10 1384 36 36 sf3863_10_1384 sf3863_10_1420))) (@block_merge f3863 10 1456 108 100 (@block_merge f3863 10 1456 36 72 sf3863_10_1456 (@block_merge f3863 10 1492 36 36 sf3863_10_1492 sf3863_10_1528)) (@block_merge f3863 10 1564 36 64 sf3863_10_1564 (@block_merge f3863 10 1600 36 28 sf3863_10_1600 sf3863_10_1636))))))
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_11_0 : block f3863 11 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_11_1 : block f3863 11 1 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_11_37 : block f3863 11 37 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_11_73 : block f3863 11 73 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_11_109 : block f3863 11 109 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_11_145 : block f3863 11 145 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_11_181 : block f3863 11 181 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_11_217 : block f3863 11 217 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_11_253 : block f3863 11 253 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_11_289 : block f3863 11 289 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_11_325 : block f3863 11 325 2=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_11_327 : block f3863 11 327 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_11_363 : block f3863 11 363 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_11_399 : block f3863 11 399 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_11_435 : block f3863 11 435 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_11_471 : block f3863 11 471 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_11_507 : block f3863 11 507 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_11_543 : block f3863 11 543 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_11_579 : block f3863 11 579 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_11_615 : block f3863 11 615 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_11_651 : block f3863 11 651 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_11_687 : block f3863 11 687 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_11_723 : block f3863 11 723 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_11_759 : block f3863 11 759 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_11_795 : block f3863 11 795 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_11_831 : block f3863 11 831 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_11_867 : block f3863 11 867 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_11_903 : block f3863 11 903 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_11_939 : block f3863 11 939 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_11_975 : block f3863 11 975 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_11_1011 : block f3863 11 1011 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_11_1047 : block f3863 11 1047 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_11_1083 : block f3863 11 1083 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_11_1119 : block f3863 11 1119 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_11_1155 : block f3863 11 1155 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_11_1191 : block f3863 11 1191 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_11_1227 : block f3863 11 1227 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_11_1263 : block f3863 11 1263 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_11_1299 : block f3863 11 1299 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_11_1335 : block f3863 11 1335 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_11_1371 : block f3863 11 1371 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_11_1407 : block f3863 11 1407 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_11_1443 : block f3863 11 1443 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_11_1479 : block f3863 11 1479 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_11_1515 : block f3863 11 1515 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_11_1551 : block f3863 11 1551 3=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allf3863_11 : block f3863 11 0 1554=true := (@block_merge f3863 11 0 759 795 (@block_merge f3863 11 0 327 432 (@block_merge f3863 11 0 145 182 (@block_merge f3863 11 0 37 108 (@block_merge f3863 11 0 1 36 sf3863_11_0 sf3863_11_1) (@block_merge f3863 11 37 36 72 sf3863_11_37 (@block_merge f3863 11 73 36 36 sf3863_11_73 sf3863_11_109))) (@block_merge f3863 11 145 108 74 (@block_merge f3863 11 145 36 72 sf3863_11_145 (@block_merge f3863 11 181 36 36 sf3863_11_181 sf3863_11_217)) (@block_merge f3863 11 253 36 38 sf3863_11_253 (@block_merge f3863 11 289 36 2 sf3863_11_289 sf3863_11_325)))) (@block_merge f3863 11 327 216 216 (@block_merge f3863 11 327 108 108 (@block_merge f3863 11 327 36 72 sf3863_11_327 (@block_merge f3863 11 363 36 36 sf3863_11_363 sf3863_11_399)) (@block_merge f3863 11 435 36 72 sf3863_11_435 (@block_merge f3863 11 471 36 36 sf3863_11_471 sf3863_11_507))) (@block_merge f3863 11 543 108 108 (@block_merge f3863 11 543 36 72 sf3863_11_543 (@block_merge f3863 11 579 36 36 sf3863_11_579 sf3863_11_615)) (@block_merge f3863 11 651 36 72 sf3863_11_651 (@block_merge f3863 11 687 36 36 sf3863_11_687 sf3863_11_723))))) (@block_merge f3863 11 759 396 399 (@block_merge f3863 11 759 180 216 (@block_merge f3863 11 759 72 108 (@block_merge f3863 11 759 36 36 sf3863_11_759 sf3863_11_795) (@block_merge f3863 11 831 36 72 sf3863_11_831 (@block_merge f3863 11 867 36 36 sf3863_11_867 sf3863_11_903))) (@block_merge f3863 11 939 108 108 (@block_merge f3863 11 939 36 72 sf3863_11_939 (@block_merge f3863 11 975 36 36 sf3863_11_975 sf3863_11_1011)) (@block_merge f3863 11 1047 36 72 sf3863_11_1047 (@block_merge f3863 11 1083 36 36 sf3863_11_1083 sf3863_11_1119)))) (@block_merge f3863 11 1155 216 183 (@block_merge f3863 11 1155 108 108 (@block_merge f3863 11 1155 36 72 sf3863_11_1155 (@block_merge f3863 11 1191 36 36 sf3863_11_1191 sf3863_11_1227)) (@block_merge f3863 11 1263 36 72 sf3863_11_1263 (@block_merge f3863 11 1299 36 36 sf3863_11_1299 sf3863_11_1335))) (@block_merge f3863 11 1371 108 75 (@block_merge f3863 11 1371 36 72 sf3863_11_1371 (@block_merge f3863 11 1407 36 36 sf3863_11_1407 sf3863_11_1443)) (@block_merge f3863 11 1479 36 39 sf3863_11_1479 (@block_merge f3863 11 1515 36 3 sf3863_11_1515 sf3863_11_1551))))))
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_12_0 : block f3863 12 0 36=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_12_36 : block f3863 12 36 36=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_12_72 : block f3863 12 72 36=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_12_108 : block f3863 12 108 16=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allf3863_12 : block f3863 12 0 124=true := (@block_merge f3863 12 0 72 52 (@block_merge f3863 12 0 36 36 sf3863_12_0 sf3863_12_36) (@block_merge f3863 12 72 36 16 sf3863_12_72 sf3863_12_108))
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3863_13_0 : block f3863 13 0 3=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allf3863_13 : block f3863 13 0 3=true := sf3863_13_0
theorem tables3863 : checkedTables f3863 13 := by
  intro k hk
  interval_cases k
  · exact (rfl : block f3863 0 0 0 = true)
  · exact (rfl : block f3863 1 0 0 = true)
  · exact (rfl : block f3863 2 0 0 = true)
  · exact (rfl : block f3863 3 0 0 = true)
  · exact (rfl : block f3863 4 0 0 = true)
  · exact (rfl : block f3863 5 0 0 = true)
  · exact (rfl : block f3863 6 0 0 = true)
  · exact (rfl : block f3863 7 0 0 = true)
  · exact (rfl : block f3863 8 0 0 = true)
  · exact allf3863_9
  · exact allf3863_10
  · exact allf3863_11
  · exact allf3863_12
  · exact allf3863_13

theorem deadReady : Impossible graph 14 inputs.toFinset := by
  have noRun := root_index (g:=dead) (before_sound known383 valid383) geomdead tablesdead (k:=14) (by decide)
    (i:=0) (ws:=inputs) (by decide +kernel)
  have tgt : targetOf dead = graph := by decide +kernel
  exact tgt ▸ noRun

theorem geom3863 : graphValid f3863 (boundsBefore known383) = true := geomdead

def s0 : Sig := neg (inputs.getD 0 zero)
def sj (j : Nat) : Sig := bin true (inputs.getD 0 zero) (inputs.getD j zero)

theorem s0_table : ∀ r : Row, bit r s0 = !(sample r 0) := by decide +kernel
theorem sj2_table : ∀ r : Row, bit r (sj 2) = (sample r 0 || sample r 2) := by decide +kernel
theorem sj3_table : ∀ r : Row, bit r (sj 3) = (sample r 0 || sample r 3) := by decide +kernel
theorem sj6_table : ∀ r : Row, bit r (sj 6) = (sample r 0 || sample r 6) := by decide +kernel

theorem table_eval_gen (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (w : List Sig) (i : Nat) (r : Row) :
    bit r ((execute C.gates w).getD i zero) = (C.wires (w.map (bit r))).getD i false := by
  rw [←b_read, execute_bits _ _ _ (fun g hg => (h g hg).1)]
  rfl

theorem inputs_witness : ∀ i : Fin 9,
    (bit (absentRow i) graph != bit (presentRow i) graph) &&
    (inputs.all fun w => w == inputs.getD i.val zero || bit (absentRow i) w == bit (presentRow i) w) = true := by
  decide +kernel

theorem no_from_inputs {k t S} (hk : k ≤ 14) (h : Live graph k t S) (sub : ∀ a ∈ S, a ∈ inputs) : False := by
  have hS : S = inputs.toFinset := by
    apply Finset.Subset.antisymm (fun w hw => List.mem_toFinset.mpr (sub w hw))
    intro v hv
    have hm := List.mem_toFinset.mp hv
    rw [←input_list, List.mem_ofFn] at hm
    obtain ⟨i, rfl⟩ := hm
    have cut := inputs_witness i
    simp only [Bool.and_eq_true, bne_iff_ne, List.all_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at cut
    exact raw_required h inputs (inputs.getD i.val zero) sub (absentRow i) (presentRow i) cut.1
      (fun w hw hne => (cut.2 w hw).resolve_left hne)
  exact deadReady k t hk (hS ▸ h)

theorem valid_col_at (g : Forest) (prior : Nat → Nat) (hg : graphValid g prior = true)
    (i : Nat) (c : ColumnInfo) (hr : g.cols.read i = some c) :
    colCheck g.mask c prior = true := by
  simp only [graphValid, Bool.and_eq_true, List.all_eq_true] at hg
  exact hg.1.2 c (g.cols.read_mem hr)

theorem slice_x0_0 : Slice inputs graph (subcube 1 0) 12 := by
  have hv : vars 511 = inputs := by decide +kernel
  have hg : chartGoal 511 = graph := by decide +kernel
  have hs := col_sound (m:=511) (1, 0, 510, 0, 12) (boundsBefore known383) (before_sound known383 valid383)
    (valid_col_at dead (boundsBefore known383) geomdead 0 (1, 0, 510, 0, 12) (by decide +kernel))
  rwa [hv, hg] at hs

def essNbr (j : Nat) (i : Fin 9) : Nat :=
  if j = 2 then [4, 6, 7, 4, 3, 7, 8, 5, 6].getD i.val 0
  else if j = 3 then [4, 6, 7, 8, 3, 7, 8, 5, 6].getD i.val 0
  else [4, 2, 7, 8, 3, 7, 8, 5, 3].getD i.val 0

def essBase (j : Nat) (i : Fin 9) : Nat :=
  (if i.val = j then 1 else 0) ||| (1 <<< essNbr j i)

def essRowA (j : Nat) (i : Fin 9) : Row := Fin.ofNat 512 (essBase j i)
def essRowB (j : Nat) (i : Fin 9) : Row := Fin.ofNat 512 (essBase j i ||| (1 <<< i.val))

theorem ess_wit_2 : ∀ i : Fin 9, i.val ≠ 0 →
    (bit (essRowA 2 i) graph != bit (essRowB 2 i) graph) &&
    ((inputs ++ [s0, sj 2]).all fun w => w == inputs.getD i.val zero ||
      bit (essRowA 2 i) w == bit (essRowB 2 i) w) = true := by decide +kernel

theorem ess_wit_3 : ∀ i : Fin 9, i.val ≠ 0 →
    (bit (essRowA 3 i) graph != bit (essRowB 3 i) graph) &&
    ((inputs ++ [s0, sj 3]).all fun w => w == inputs.getD i.val zero ||
      bit (essRowA 3 i) w == bit (essRowB 3 i) w) = true := by decide +kernel

theorem ess_wit_6 : ∀ i : Fin 9, i.val ≠ 0 →
    (bit (essRowA 6 i) graph != bit (essRowB 6 i) graph) &&
    ((inputs ++ [s0, sj 6]).all fun w => w == inputs.getD i.val zero ||
      bit (essRowA 6 i) w == bit (essRowB 6 i) w) = true := by decide +kernel

theorem imp_main_2 : Impossible graph 13 (inputs.tail ++ [s0, sj 2]).toFinset := by
  have noRun := root_index (g:=f3863) (before_sound known383 valid383) geom3863 tables3863 (k:=13) (by decide)
    (i:=0) (ws:=inputs.tail ++ [s0, sj 2]) (by decide +kernel)
  have tgt : targetOf f3863 = graph := by decide +kernel
  exact tgt ▸ noRun

theorem imp_main_3 : Impossible graph 13 (inputs.tail ++ [s0, sj 3]).toFinset := by
  have noRun := root_index (g:=f3863) (before_sound known383 valid383) geom3863 tables3863 (k:=13) (by decide)
    (i:=1) (ws:=inputs.tail ++ [s0, sj 3]) (by decide +kernel)
  have tgt : targetOf f3863 = graph := by decide +kernel
  exact tgt ▸ noRun

theorem imp_main_6 : Impossible graph 13 (inputs.tail ++ [s0, sj 6]).toFinset := by
  have noRun := root_index (g:=f3863) (before_sound known383 valid383) geom3863 tables3863 (k:=13) (by decide)
    (i:=2) (ws:=inputs.tail ++ [s0, sj 6]) (by decide +kernel)
  have tgt : targetOf f3863 = graph := by decide +kernel
  exact tgt ▸ noRun

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem imp_full_2 : Impossible graph 13 (inputs ++ [s0, sj 2]).toFinset :=
  poolCut_sound slice_x0_0 [] (by rfl) (ws:=inputs ++ [s0, sj 2]) (by decide +kernel) (cap:=13) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem imp_full_3 : Impossible graph 13 (inputs ++ [s0, sj 3]).toFinset :=
  poolCut_sound slice_x0_0 [] (by rfl) (ws:=inputs ++ [s0, sj 3]) (by decide +kernel) (cap:=13) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem imp_full_6 : Impossible graph 13 (inputs ++ [s0, sj 6]).toFinset :=
  poolCut_sound slice_x0_0 [] (by rfl) (ws:=inputs ++ [s0, sj 6]) (by decide +kernel) (cap:=13) (by decide +kernel)

theorem in_inputs_0 : inputs.getD 0 zero ∈ inputs := by decide +kernel
theorem proper_in_0 : proper (inputs.getD 0 zero) := by unfold proper; decide +kernel
theorem witness_s0 : witness inputs s0 := Or.inl ⟨inputs.getD 0 zero, in_inputs_0, proper_in_0, rfl⟩

theorem witness_sj_2 : witness inputs (sj 2) :=
  Or.inr ⟨true, inputs.getD 0 zero, inputs.getD 2 zero, in_inputs_0, by decide +kernel,
    proper_in_0, by unfold proper; decide +kernel, by decide +kernel, rfl⟩
theorem witness_sj_3 : witness inputs (sj 3) :=
  Or.inr ⟨true, inputs.getD 0 zero, inputs.getD 3 zero, in_inputs_0, by decide +kernel,
    proper_in_0, by unfold proper; decide +kernel, by decide +kernel, rfl⟩
theorem witness_sj_6 : witness inputs (sj 6) :=
  Or.inr ⟨true, inputs.getD 0 zero, inputs.getD 6 zero, in_inputs_0, by decide +kernel,
    proper_in_0, by unfold proper; decide +kernel, by decide +kernel, rfl⟩

theorem mem_tail_iff (w : Sig) : w ∈ inputs.tail ↔ ∃ i : Fin 9, i.val ≠ 0 ∧ w = inputs.getD i.val zero := by
  have h0 : inputs = inputs.getD 0 zero :: inputs.tail := rfl
  have hnd : inputs.Nodup := by decide +kernel
  constructor
  · intro hw
    have hmem : w ∈ inputs := by rw [h0]; exact List.mem_cons_of_mem _ hw
    rw [←input_list, List.mem_ofFn] at hmem
    obtain ⟨i, rfl⟩ := hmem
    refine ⟨i, ?_, rfl⟩
    intro hi
    rw [h0] at hnd
    have hne := (List.nodup_cons.mp hnd).1
    have eq0 : inputs.getD i.val zero = inputs.getD 0 zero := by rw [hi]
    exact hne (eq0 ▸ hw)
  · rintro ⟨i, hi, rfl⟩
    have hmem : inputs.getD i.val zero ∈ inputs := by
      rw [←input_list, List.mem_ofFn]
      exact ⟨i, rfl⟩
    rw [h0, List.mem_cons] at hmem
    rcases hmem with heq | htail
    · exfalso
      have hdiff : ∀ k : Fin 9, k.val ≠ 0 → inputs.getD k.val zero ≠ inputs.getD 0 zero := by decide +kernel
      exact hdiff i hi heq
    · exact htail

theorem solve_case (j : Fin 9)
    (htab : ∀ r : Row, bit r (sj j.val) = (sample r 0 || sample r j))
    (hwit_sj : witness inputs (sj j.val))
    (hess : ∀ i : Fin 9, i.val ≠ 0 →
      (bit (essRowA j.val i) graph != bit (essRowB j.val i) graph) &&
      ((inputs ++ [s0, sj j.val]).all fun w => w == inputs.getD i.val zero ||
        bit (essRowA j.val i) w == bit (essRowB j.val i) w) = true)
    (hfull : Impossible graph 13 (inputs ++ [s0, sj j.val]).toFinset)
    (hroot : Impossible graph 13 (inputs.tail ++ [s0, sj j.val]).toFinset)
    (C : Circuit) (hfan : PEqualNP.MetaComplexity.FanInTwo C) (hsz : C.size ≤ 13) :
    ∃ x : Fin 9 → Bool,
      have x7 : List Bool := List.ofFn x ++ [!x 0]
      C.eval (x7 ++ [GateOp.or.eval (List.map (fun k => x7.getD k false) [0, j.val])]) ≠ edge x := by
  by_contra hcon
  simp only [not_exists, ne_eq, not_not] at hcon
  have hmap (r : Row) :
      (inputs ++ [s0, sj j.val]).map (bit r) =
      (List.ofFn (sample r) ++ [!sample r 0]) ++
      [GateOp.or.eval (List.map (fun k => (List.ofFn (sample r) ++ [!sample r 0]).getD k false) [0, j.val])] := by
    have hor_eq : GateOp.or.eval (List.map (fun k => (List.ofFn (sample r) ++ [!sample r 0]).getD k false) [0, j.val]) =
        (sample r 0 || sample r j) := by
      have g0 : (List.ofFn (sample r) ++ [!sample r 0]).getD 0 false = sample r 0 := by
        rw [List.getD_append _ _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]; rfl
      have gj : (List.ofFn (sample r) ++ [!sample r 0]).getD j.val false = sample r j := by
        rw [List.getD_append _ _ _ _ (by simp [j.isLt]), List.getD_eq_getElem _ _ (by simp [j.isLt]), List.getElem_ofFn]
      simp only [List.map_cons, List.map_nil, g0, gj, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
    rw [hor_eq, List.map_append, sampled r, List.map_cons, List.map_singleton, s0_table r, htab r]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  have goalEq : (execute C.gates (inputs ++ [s0, sj j.val])).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    let r : Row := ⟨i, hi⟩
    have h1 := table_eval_gen C hfan (inputs ++ [s0, sj j.val]) C.output r
    rw [hmap r] at h1
    exact h1.trans ((hcon (sample r)).trans (edge_table r).symm)
  have out := get_rep (execute C.gates (inputs ++ [s0, sj j.val])) C.output
  rw [goalEq] at out
  have targetIn := out.resolve_right (fun hn => hn graph_proper)
  obtain ⟨k, t, S, hk, run, sub⟩ := extract C.gates (inputs ++ [s0, sj j.val]) hfan graph_proper targetIn
  have hk13 : k ≤ 13 := le_trans hk hsz
  by_cases hsj : sj j.val ∈ S
  · by_cases hs0 : s0 ∈ S
    · have htail_in : ∀ i : Fin 9, i.val ≠ 0 → inputs.getD i.val zero ∈ S := by
        intro i hi
        have cut := hess i hi
        simp only [Bool.and_eq_true, bne_iff_ne, List.all_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at cut
        exact raw_required run _ _ sub (essRowA j.val i) (essRowB j.val i) cut.1
          (fun w hw hne => (cut.2 w hw).resolve_left hne)
      by_cases h0 : inputs.getD 0 zero ∈ S
      · have hS : S = (inputs ++ [s0, sj j.val]).toFinset := by
          apply Finset.Subset.antisymm (fun w hw => List.mem_toFinset.mpr (sub w hw))
          intro w hw
          have hm := List.mem_toFinset.mp hw
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm
          rcases hm with hin | rfl | rfl
          · rw [←input_list, List.mem_ofFn] at hin
            obtain ⟨i, rfl⟩ := hin
            by_cases hi0 : i.val = 0
            · rw [hi0]; exact h0
            · exact htail_in i hi0
          · exact hs0
          · exact hsj
        exact hfull k t hk13 (hS ▸ run)
      · have hS : S = (inputs.tail ++ [s0, sj j.val]).toFinset := by
          apply Finset.Subset.antisymm
          · intro w hw
            have hm := sub w hw
            simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm
            rw [List.mem_toFinset, List.mem_append, List.mem_cons, List.mem_singleton]
            rcases hm with hin | rfl | rfl
            · left
              rw [←input_list, List.mem_ofFn] at hin
              obtain ⟨i, rfl⟩ := hin
              have hi0 : i.val ≠ 0 := fun e => h0 (e ▸ hw)
              exact (mem_tail_iff _).mpr ⟨i, hi0, rfl⟩
            · exact Or.inr (Or.inl rfl)
            · exact Or.inr (Or.inr rfl)
          · intro w hw
            have hm := List.mem_toFinset.mp hw
            simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm
            rcases hm with htl | rfl | rfl
            · obtain ⟨i, hi0, rfl⟩ := (mem_tail_iff w).mp htl
              exact htail_in i hi0
            · exact hs0
            · exact hsj
        exact hroot k t hk13 (hS ▸ run)
    · have sub' : ∀ a ∈ S, a ∈ inputs ++ [sj j.val] := by
        intro a ha
        have hm := sub a ha
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
        rcases hm with hin | rfl | rfl
        · exact Or.inl hin
        · exact False.elim (hs0 ha)
        · exact Or.inr rfl
      obtain ⟨k', t', S', hk', run', sub''⟩ := pull_gate run (Or.inr hwit_sj) sub'
      exact no_from_inputs (by omega) run' sub''
  · have sub' : ∀ a ∈ S, a ∈ inputs ++ [s0] := by
      intro a ha
      have hm := sub a ha
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
      rcases hm with hin | rfl | rfl
      · exact Or.inl hin
      · exact Or.inr rfl
      · exact False.elim (hsj ha)
    obtain ⟨k', t', S', hk', run', sub''⟩ := pull_gate run (Or.inr witness_s0) sub'
    exact no_from_inputs (by omega) run' sub''

theorem main : ∀ (x1 : List ℕ),   x1 = [(0 : ℕ), (2 : ℕ)] ∨ x1 = [(0 : ℕ), (3 : ℕ)] ∨ x1 = [(0 : ℕ), (6 : ℕ)] →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           ∃ (x6 : Fin (9 : ℕ) → Bool),             have x7 : List Bool := List.ofFn x6 ++ [!x6 (0 : Fin (9 : ℕ))];             x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x8 : ℕ) => x7.getD x8 Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro x1 hx1 x3 hfan hsz
  rcases hx1 with rfl | rfl | rfl
  · exact solve_case 2 sj2_table witness_sj_2 ess_wit_2 imp_full_2 imp_main_2 x3 hfan hsz
  · exact solve_case 3 sj3_table witness_sj_3 ess_wit_3 imp_full_3 imp_main_3 x3 hfan hsz
  · exact solve_case 6 sj6_table witness_sj_6 ess_wit_6 imp_full_6 imp_main_6 x3 hfan hsz

end PEqualNP.Outside.L_meta_3863_aux

theorem PEqualNP.Outside.L_meta_3863 : ∀ (x1 : List ℕ),   x1 = [(0 : ℕ), (2 : ℕ)] ∨ x1 = [(0 : ℕ), (3 : ℕ)] ∨ x1 = [(0 : ℕ), (6 : ℕ)] →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           ∃ (x6 : Fin (9 : ℕ) → Bool),             have x7 : List Bool := List.ofFn x6 ++ [!x6 (0 : Fin (9 : ℕ))];             x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x8 : ℕ) => x7.getD x8 Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) :=
  PEqualNP.Outside.L_meta_3863_aux.main
