import PEqualNP.Defs

-- The Live/Run/Forest verification framework and subgraph lower bounds
-- (known383 and dead) are adapted from PressF10, pequalnp-proofs PR 4332,
-- licensed under Apache-2.0.
namespace PEqualNP.Outside.L_meta_3929
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

def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
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
def vars (m : Nat) := (selected m).map Prod.snd
def vertex (m j : Nat) := if m.testBit j then (if m.testBit 9 && j == 0 then neg (inputs.getD 0 zero) else inputs.getD j zero) else zero
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

def supportPairs (baseRow mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) => (a,Fin.ofNat 512 baseRow,Fin.ofNat 512 (baseRow ^^^ (1 <<< i)))

def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  let base := if m.testBit 9 && m.testBit 0 then 1 else 0
  (selected m).map fun (i,a) =>
    let r := base ^^^ (1 <<< ((hints >>> (4*i)) &&& 15))
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ^^^ (1 <<< i)))

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
def colFree (m z o : Nat) := (m &&& 511) ^^^ ((m &&& 511) &&& (z ||| o))
def chartGoal (m : Nat) : Sig := graphGoal m
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (chartGoal m)
  let baseRow := if m.testBit 9 && free.testBit 0 then 1 else 0
  let xs := supportPairs baseRow s
  let count := (xs.map Prod.fst).toFinset.card
  let drop := colFree free q 0
  let lz := if m.testBit 9 && drop.testBit 0 then drop &&& (511 ^^^ 1) else drop
  let lo := if m.testBit 9 && drop.testBit 0 then 1 else 0
  properB G && checkMap ms (vars m) (chartGoal m) (vars free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (vars free) xs && decide (L ≤ count-1)
     else properB (graphGoal q) &&
       checkLift (fixRows lz lo) G (vars free) (vars q) (graphGoal q) xs &&
       decide (L ≤ prior q+count))

theorem col_sound {m : Nat} (c : ColumnInfo) (prior : Nat → Nat)
    (valid : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (ok : colCheck m c prior = true) : Slice (vars m) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  obtain ⟨z,o,q,s,L⟩ := c
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (chartGoal m)
  let baseRow := if m.testBit 9 && free.testBit 0 then 1 else 0
  let xs := supportPairs baseRow s
  change (((properB G && checkMap ms (vars m) (chartGoal m) (vars free) G) &&
    (movedWord ms (subcube z o)==one)) && _) = true at ok
  simp only [Bool.and_eq_true,beq_iff_eq] at ok
  apply slice_correct ok.1.1.2 ok.1.2 (proper_of _ ok.1.1.1)
  intro p bank hr ha
  have hh := ok.2
  by_cases hq : q=0
  · simp only [colCheck,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lower_count (proper_of _ ok.1.1.1) _ hh.1 p bank hr ha)
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
  let x := fun j => if m.testBit j then (if m.testBit 9 && j == 0 then ~~~(v 0) else v j) else 0
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then (if m.testBit 9 && j.val == 0 then ~~~(v 0) else v j.val) else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · by_cases hf : (m.testBit 9 && j.val == 0) = true
    · have hj0 : j.val = 0 := by
        simp only [Bool.and_eq_true, beq_iff_eq] at hf; exact hf.2
      simp only [vertex, hh, hf, ite_true, bit_neg, BitVec.getLsbD_not, i.isLt, decide_true, Bool.true_and]
      exact congrArg Bool.not (asRow_bit v i ⟨0, by decide⟩)
    · simpa [vertex, hh, hf] using asRow_bit v i j
  · simp [vertex, hh, bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then (if m.testBit 9 && j == 0 then ~~~(v 0) else v j) else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
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
  rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a :=
  raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)

def targetOf (g : Forest) := chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) := liftGoal m v
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val :=
  bit_liftGoal m v i
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
abbrev knownPrev_g527 := known383
def keyg527l4 (i : Nat) : Nat := 0x3000
def g527d3 (i : Nat) : Nat := 0x7a00
def g527l3 : Packing := (1,1,0,0,0,0,0,g527d3)
def g527d4 (i : Nat) : Nat := 0xf
def g527l4 : Packing := (1,0,0,0,0,0,0,g527d4)
def g527samples : Array (Bits × Bits) := #[(0xf060607000df8e18,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2f5edbfdb4e94e39),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff83fff1ff71f87f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0258101094094831),(0xfffc7e7e3fdf8f9c,0x440300a42102950c),(0xffff807fc78e0fe0,0x88105d49061d6ae0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g527columns : IndexTree ColumnInfo := (.leaf [])
def g527autos : Array (List Nat) := #[[]]
def g527levels : Nat → Packing
  | 3 => g527l3
  | 4 => g527l4
  | _ => emptyPacking
def g527index : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 1 5 3 4 0 0 (keyg527l4)
  | _ => fun _ => none
def g527 : Forest := ⟨527,4,fun j => g527samples[j]?.getD (0,0),g527columns,g527autos,g527levels,g527index⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geomg527 : graphValid g527 (boundsBefore knownPrev_g527) = true := by
  unfold graphValid
  refine Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨by decide +kernel, by decide +kernel⟩, ?_⟩, by decide +kernel⟩
  apply listPieces_all (d:=0)
  simp only [listPieces,IndexTree.values,List.length_append,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceDiv,List.take,List.drop]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg527_3_0 : block g527 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg527_3 : block g527 3 0 1=true := sg527_3_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg527_4_0 : block g527 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg527_4 : block g527 4 0 1=true := sg527_4_0
theorem tablesg527 : checkedTables g527 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g527 0 0 0 = true)
  · exact (rfl : block g527 1 0 0 = true)
  · exact (rfl : block g527 2 0 0 = true)
  · exact allg527_3
  · exact allg527_4
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low527 : Lower (vars 527) (graphGoal 527) 5 :=
  lower_forest (g:=g527) (i:=0) (hints:=8449) (before_sound known383 valid383) geomg527 tablesg527 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps527 : List (Nat × List Nat) := [(527,[]),(541,[50,65]),(647,[115,99,83,67]),(677,[114,33,97,82,50,65]),(835,[131,115,98,83,66]),(865,[130,33,113,99,82,65])]
def known527 := extendKnown known383 5 maps527
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid527 : Known known527 := extendKnown_ok valid383 low527 (by decide +kernel)
abbrev knownPrev_g535 := known527
def keyg535l4 (i : Nat) : Nat := 0x3000
def g535d3 (i : Nat) : Nat := 0x7a00
def g535l3 : Packing := (1,1,0,0,0,0,0,g535d3)
def g535d4 (i : Nat) : Nat := 0xf
def g535l4 : Packing := (1,0,0,0,0,0,0,g535d4)
def g535samples : Array (Bits × Bits) := #[(0xe00060700041cc18,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff5efbdffdb6fdadb9),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff1e7ff1ff71fc9f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff04c088109204a891),(0xffe07e7e3f41cf1c,0x881d10a4251b570c),(0x0,0x0),(0xffff807fc78e0fe0,0x10905d49061dada0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g535columns : IndexTree ColumnInfo := (.leaf [])
def g535autos : Array (List Nat) := #[[]]
def g535levels : Nat → Packing
  | 3 => g535l3
  | 4 => g535l4
  | _ => emptyPacking
def g535index : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 1 5 3 4 0 0 (keyg535l4)
  | _ => fun _ => none
def g535 : Forest := ⟨535,4,fun j => g535samples[j]?.getD (0,0),g535columns,g535autos,g535levels,g535index⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geomg535 : graphValid g535 (boundsBefore knownPrev_g535) = true := by
  unfold graphValid
  refine Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨by decide +kernel, by decide +kernel⟩, ?_⟩, by decide +kernel⟩
  apply listPieces_all (d:=0)
  simp only [listPieces,IndexTree.values,List.length_append,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceDiv,List.take,List.drop]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg535_3_0 : block g535 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg535_3 : block g535 3 0 1=true := sg535_3_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg535_4_0 : block g535 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg535_4 : block g535 4 0 1=true := sg535_4_0
theorem tablesg535 : checkedTables g535 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g535 0 0 0 = true)
  · exact (rfl : block g535 1 0 0 = true)
  · exact (rfl : block g535 2 0 0 = true)
  · exact allg535_3
  · exact allg535_4
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low535 : Lower (vars 535) (graphGoal 535) 5 :=
  lower_forest (g:=g535) (i:=0) (hints:=257) (before_sound known527 valid527) geomg535 tablesg535 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps535 : List (Nat × List Nat) := [(535,[]),(539,[50,65]),(551,[84]),(569,[65,33,82,49]),(595,[98,82,50]),(611,[66,100,82,50]),(689,[114,33,97,82,49])]
def known535 := extendKnown known527 5 maps535
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid535 : Known known535 := extendKnown_ok valid527 low535 (by decide +kernel)
abbrev knownPrev_g543 := known535
def keyg543l5 (i : Nat) : Nat := 0x39006660000720000010
def keyg543l6 (i : Nat) : Nat := 0x5f80000218800000000000000000000000006dc3e11f50db0fcd000000000000029d020600174e40d8029175006bf8c009480000000000000000000017250050010000010c0000
def keyg543l7 (i : Nat) : Nat := 0x514018400000000000000aae8da19b06000061c0000748000000101cd2c00b080000000000000000004b4511000002002000
def g543d4 (i : Nat) : Nat := 0x9e99850506786550600ba18931802f06154a00
def g543l4 : Packing := (4,3,3,0,0,0,0,g543d4)
def g543d5 (i : Nat) : Nat := 0xac2a084200000000008c00193c0005140fca9401f951803f283007e4ca00fc98c01f921802f4ab006791233d722445ba44803b467007388a33db08c896c524c6d8a4985e14141
def g543l5 : Packing := (16,2,3,0,0,6,0,g543d5)
def g543d6 (i : Nat) : Nat := 0x2ea610a04098482975305e74d34d2bae2640fe00fd41fd32fd31fd21fd20fd10be44de33fa00
def g543l6 : Packing := (10,1,3,0,0,6,0,g543d6)
def g543d7 (i : Nat) : Nat := 0x1a209f
def g543l7 : Packing := (1,0,3,0,0,0,0,g543d7)
def g543samples : Array (Bits × Bits) := #[(0x7f800fe01f80701f8000007f00e001c00fc7038038101ade1fe1f60e18,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeb7d6cdfd57b6f797777d7f2fedffbbefff7dbedbcdd9dbd99d9f6de39),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0001fff801fff81fc7fff007ffff1c71f8ff8eeec6001fec6487f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff82284c9480022650226480a0444b20140041088498c4818c88d8c44831),(0x7fffffffe000001ffffe007fffff81ff8e07e3f1ff0ef8c01fe1078f9c,0xc418101164c49820401194488104c2012024121250a2231332303850c),(0x7fffffffffffffe00000007ffffffe000ff803fe3ff0f29e1e01f80fe0,0x300e06060810021c3838e20810020087249002480a60c1464c4ca80ae0),(0x7fffffffffffffffffffff80000000000ffffc003fff031fe001fff000,0x4070081810600c0040410070e09c713849249000348c00b9919156d000),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g543columns : IndexTree ColumnInfo := (.fork 2 (.leaf [(2,0,541,0,5),(4,0,539,0,5)]) (.leaf [(8,0,535,0,5),(16,0,527,0,5),(0,1,30,0,4)]))
def g543autos : Array (List Nat) := #[[],[50,65]]
def g543levels : Nat → Packing
  | 4 => g543l4
  | 5 => g543l5
  | 6 => g543l6
  | 7 => g543l7
  | _ => emptyPacking
def g543index : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 2 12 4 7 2 1 (keyg543l5)
  | 6 => lookupWord 12 55 6 9 4 1 (keyg543l6)
  | 7 => lookupWord 8 40 6 9 4 1 (keyg543l7)
  | _ => fun _ => none
def g543 : Forest := ⟨543,7,fun j => g543samples[j]?.getD (0,0),g543columns,g543autos,g543levels,g543index⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geomg543 : graphValid g543 (boundsBefore knownPrev_g543) = true := by
  unfold graphValid
  refine Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨by decide +kernel, by decide +kernel⟩, ?_⟩, by decide +kernel⟩
  apply listPieces_all (d:=2)
  simp only [listPieces,IndexTree.values,List.length_append,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceDiv,List.take,List.drop]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg543_4_0 : block g543 4 0 4=true := by
  apply cellsBlock (ar:=5) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg543_4 : block g543 4 0 4=true := sg543_4_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg543_5_0 : block g543 5 0 10=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg543_5_10 : block g543 5 10 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg543_5 : block g543 5 0 16=true := (@block_merge g543 5 0 10 6 sg543_5_0 sg543_5_10)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg543_6_0 : block g543 6 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg543_6_3 : block g543 6 3 7=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg543_6 : block g543 6 0 10=true := (@block_merge g543 6 0 3 7 sg543_6_0 sg543_6_3)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg543_7_0 : block g543 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg543_7 : block g543 7 0 1=true := sg543_7_0
theorem tablesg543 : checkedTables g543 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g543 0 0 0 = true)
  · exact (rfl : block g543 1 0 0 = true)
  · exact (rfl : block g543 2 0 0 = true)
  · exact (rfl : block g543 3 0 0 = true)
  · exact allg543_4
  · exact allg543_5
  · exact allg543_6
  · exact allg543_7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low543 : Lower (vars 543) (graphGoal 543) 8 :=
  lower_forest (g:=g543) (i:=0) (hints:=8449) (before_sound known535 valid535) geomg543 tablesg543 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps543 : List (Nat × List Nat) := [(543,[]),(679,[115,67,100,83]),(867,[131,50,66,116,99,82])]
def known543 := extendKnown known535 8 maps543
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid543 : Known known543 := extendKnown_ok valid535 low543 (by decide +kernel)
def g559 : Forest := ⟨559,5,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low559 : Lower (vars 559) (graphGoal 559) 6 :=
  lower_discard (g:=g559) (ci:=(8,0,551,0,5)) (hints:=8449) (before_sound known543 valid543) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps559 : List (Nat × List Nat) := [(559,[]),(573,[50,65]),(663,[115,99,83,67]),(881,[130,50,81,115,98,65])]
def known559 := extendKnown known543 6 maps559
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid559 : Known known559 := extendKnown_ok valid543 low559 (by decide +kernel)
def g567 : Forest := ⟨567,5,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low567 : Lower (vars 567) (graphGoal 567) 6 :=
  lower_discard (g:=g567) (ci:=(16,0,551,0,5)) (hints:=257) (before_sound known559 valid559) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps567 : List (Nat × List Nat) := [(567,[]),(571,[50,65]),(627,[98,50])]
def known567 := extendKnown known559 6 maps567
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid567 : Known known567 := extendKnown_ok valid559 low567 (by decide +kernel)
def g591 : Forest := ⟨591,5,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low591 : Lower (vars 591) (graphGoal 591) 6 :=
  lower_discard (g:=g591) (ci:=(64,0,527,0,5)) (hints:=16785665) (before_sound known567 valid567) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps591 : List (Nat × List Nat) := [(591,[])]
def known591 := extendKnown known567 6 maps591
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid591 : Known known591 := extendKnown_ok valid567 low591 (by decide +kernel)
def g603 : Forest := ⟨603,5,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low603 : Lower (vars 603) (graphGoal 603) 6 :=
  lower_discard (g:=g603) (ci:=(8,0,595,0,5)) (hints:=16793601) (before_sound known591 valid591) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps603 : List (Nat × List Nat) := [(603,[]),(697,[118,81,33]),(739,[67,116,83])]
def known603 := extendKnown known591 6 maps603
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid603 : Known known603 := extendKnown_ok valid591 low603 (by decide +kernel)
def g669 : Forest := ⟨669,5,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low669 : Lower (vars 669) (graphGoal 669) 6 :=
  lower_discard (g:=g669) (ci:=(128,0,541,0,5)) (hints:=536879876) (before_sound known603 valid603) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps669 : List (Nat × List Nat) := [(669,[]),(857,[130,114,98,82])]
def known669 := extendKnown known603 6 maps669
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid669 : Known known669 := extendKnown_ok valid603 low669 (by decide +kernel)
def g607 : Forest := ⟨607,8,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low607 : Lower (vars 607) (graphGoal 607) 9 :=
  lower_discard (g:=g607) (ci:=(64,0,543,0,8)) (hints:=16785665) (before_sound known669 valid669) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps607 : List (Nat × List Nat) := [(607,[]),(743,[67,116,83]),(995,[99,33,129,115,82,65])]
def known607 := extendKnown known669 9 maps607
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid607 : Known known607 := extendKnown_ok valid669 low607 (by decide +kernel)
abbrev knownPrev_g623 := known607
def keyg623l7 (i : Nat) : Nat := 0x1f0080b100000000000000000
def g623d6 (i : Nat) : Nat := 0x4ad0d42818d2240fb08fe8037a83bd40
def g623l6 : Packing := (4,1,3,0,0,6,0,g623d6)
def g623d7 (i : Nat) : Nat := 0xa993f
def g623l7 : Packing := (1,0,3,0,0,0,0,g623d7)
def g623samples : Array (Bits × Bits) := #[(0x1fff800000007ffff00000fff8000fffc0001fffe00007f80007fffc00001fff8000000000003fff800000000000001ffff00001fc0000000ff8000001ff83c1c0fc1c381fc007007000e00e07fff8e3001ff0fc067c1fe3c999adc60e18,0x6dfdd4f575fd6ff5f2fd6fdfd6bf37ffee7abdfedcfe5eff77a7ffafab5bd5fadab37abfdeaf6f5efab97abeeedf7eaf5ffeaf2f57fdbbf7ffd7dee7b7f7ffffebf5eeff1ebcdff3b7db79b6f96f865bb9f7b73f91f4cde739a7dbb9adeede39),(0xf0001ffffffff0007fffffffff0000000fffffffffffffffffffffffffffffffe00000001ffff0003ffffffff0001ffff01ffffffffe000007fffffffffffe0f83c1f8e01ffffe03c7e3fe3fe1fe187fff03201003fffffc00fcc981ff26487f,0x40a8802000884261009040128425204a401000908094004a2000250000100050803200348000400c80100024401640020120020004882804b001000004a0000180404820048846018141181220420010312521108130c0042124810109244831),(0xffffe000000000007ffffffffffffffff00000001ffffffff8000007ffffffffffffffffe00000003fffffffffffe000001ffffffffffffff8000ffffffc01f003fe00ffe03f1ffc07fc7fc7fe301f8c01e3c01ffcfe06001fe30e1e31c78f9c,0x800106462621848624218484180842108b2316230020881042324832306118830304230108c9899303022300808008c46448c444611001210262600221009250019600452015085402a822844a34aa8c8242c24524ca10a94aca0e143083850c),(0x7fffffffffffffffffffffffe000000000000007ffffffffffffffffffffffffc000000000000000001ffffffffffffffffff000000001fffc0000ffffc01ffff8007ff8ffc01ff001fc001fff0000001f03f01fc1f80fe0,0xece18b858ce0b3848c60918e0318463004420c416c7136384c4b1c4c182611c0c184c26130202042c3c4c370b1b930b8993088986200246248404b4c63924a6ac0000aa4ac012aad0004d20b5cb557115bd249acb106756b535f00bc1780ae0),(0x0,0x0),(0xffffffffffffffff8000000000000000000000000000000000000007ffffffffffffffffffffffffffffffffffffffffffe000000000000000000000000001ffffffff0000001fffffff8000ffffe00001ffffe000000003e003ffe001fff000,0x8f000c060f003c070f80e1f00be077c0c7838f818f81c7c07073e07020381e0102070381c0c0c18302070380c1c1c0c001c0f0e07c13387c70788c707c2393b4ae4aa0000001d3324d20000f96f865a21f7b713016085e739a7dba001eed000),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffff80000000000000000000000000000000000000000000000000000000000000000000001ffffffffffffffe00000000000fffffffffe0000000000007c0003fffffe000000,0xf001f007f000c007f000fe000c007800f803f001f001f800007c007fc03fe001fc07fc01ff00fe03fc07fc00fe01ff00e1ff00ff801c3f807f80f07f803c1cc733934d39326800000000000dfbdffefc6dad80c0e8307fbdedb7efef6000000),(0x0,0x0),(0x0,0x0)]
def g623columns : IndexTree ColumnInfo := (.fork 3 (.leaf [(32,0,591,0,6),(64,0,559,0,6),(4,8,611,0,5)]) (.leaf [(72,0,551,0,5),(0,1,78,0,4),(0,33,78,0,4)]))
def g623autos : Array (List Nat) := #[[]]
def g623levels : Nat → Packing
  | 6 => g623l6
  | 7 => g623l7
  | _ => emptyPacking
def g623index : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 2 15 4 6 2 0 (keyg623l7)
  | _ => fun _ => none
def g623 : Forest := ⟨623,7,fun j => g623samples[j]?.getD (0,0),g623columns,g623autos,g623levels,g623index⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geomg623 : graphValid g623 (boundsBefore knownPrev_g623) = true := by
  unfold graphValid
  refine Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨by decide +kernel, by decide +kernel⟩, ?_⟩, by decide +kernel⟩
  apply listPieces_all (d:=2)
  simp only [listPieces,IndexTree.values,List.length_append,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceDiv,List.take,List.drop]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg623_6_0 : block g623 6 0 4=true := by
  apply cellsBlock (ar:=6) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg623_6 : block g623 6 0 4=true := sg623_6_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg623_7_0 : block g623 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg623_7 : block g623 7 0 1=true := sg623_7_0
theorem tablesg623 : checkedTables g623 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g623 0 0 0 = true)
  · exact (rfl : block g623 1 0 0 = true)
  · exact (rfl : block g623 2 0 0 = true)
  · exact (rfl : block g623 3 0 0 = true)
  · exact (rfl : block g623 4 0 0 = true)
  · exact (rfl : block g623 5 0 0 = true)
  · exact allg623_6
  · exact allg623_7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low623 : Lower (vars 623) (graphGoal 623) 8 :=
  lower_forest (g:=g623) (i:=0) (hints:=16785665) (before_sound known607 valid607) geomg623 tablesg623 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps623 : List (Nat × List Nat) := [(623,[]),(855,[131,115,83,67,98])]
def known623 := extendKnown known607 8 maps623
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid623 : Known known623 := extendKnown_ok valid607 low623 (by decide +kernel)
abbrev knownPrev_g635 := known623
def keyg635l6 (i : Nat) : Nat := 0x60
def keyg635l7 (i : Nat) : Nat := 0x3080010800000
def g635d5 (i : Nat) : Nat := 0xee80140
def g635l5 : Packing := (1,2,3,0,0,0,0,g635d5)
def g635d6 (i : Nat) : Nat := 0x15029cb182c507f803f401bd40
def g635l6 : Packing := (3,1,3,0,0,5,0,g635d6)
def g635d7 (i : Nat) : Nat := 0x3a8ff
def g635l7 : Packing := (1,0,3,0,0,0,0,g635d7)
def g635samples : Array (Bits × Bits) := #[(0x1fff000000007fffe00000fffc0001fffc00000000fffc0001fc0001fffc00003ffe000000000000000000000000001fffc00007f00000000000000001ff87c1c0fe1c0e03fc00007000f00f0f9ffc78001ff800007c1f03d99b36f00f00,0x6fffd9faf7fedffdf5fedfbff6bfdbfffdcfebdffb7ffbefebfffdf3fffbf5dbebfdbaedf5ffbebf6f5fbfaff7dfff5fbfff5ebebff6efdfffd7f7fffbffffffeff5eeff9eef5bff7ddb7db6fddfcdd7bdff7bbfeb6aefef7baffbbb76fedf55),(0xf0001fffffffe0007fffffffff00000001ffffffff8000ffffffffffffffffffffffc00000003ffff0000ffff8001fffe01ffffffff8000007fffc01fffffe0f87c1f8f01f8fffe071e3fe3ff1ff119fff8030180207f9fc001cd9833fca4c4f,0x416a8050029485690150802aa42ad02aa805400a920ab209401548001550001000a900e801d50022401720092016c00502a004002a20a0157002a02a0250000180c04830048248e030c11c1230930084399a70986222e20c632c910224ca4c45),(0x0,0x0),(0xffffe000000000007ffffffffffffffffe000000000000fffffffe000001ffffffffffffffffc00000000fffffffe000001ffffffffffffff8000001fffc01f007fe00ffe00fe3ff81fc7fc7fe701e1c01f9c01ffc0600001f031e1c38f38f8c,0x80430c9c58c7098e2863090c380c610c316671631c531c0211061099261c9861310e0c30988613338999c4c040808989c8c989130c4004862263394c9080925003560052a0056125816826845675763c8aa9d14ab41636b5ad561e1438a38a8c),(0x7fffffffffffffffffffffffffffff00000000000001fffffffffffffffffffffffff00000000000001ffffffffffffffffffffe000001fff80000fffff003fffe007ff8ff801fe001fe001ffff806001fe3e01fc0fc0ff0,0xd8c1160a318163041841230c0308230c008020c200c20ac625861225861208242301041211824040202090d851b1216131210243080091844840001231924a6a80000a50aa0024a54004920a98a89c1115622154360414a52a9e00b405c0550),(0xffffffffffffffff80000000000000000000000000000000000000000001ffffffffffffffffffffffffffffffffffffffe000000000000000000000000001ffffffff00000003ffffff8000ffffe00001ffffe000000003e003ffe000fff000,0x9f00180c3e007c071f81c3f00bf03bf018f838fc06fc0cf839f81c39f81c10383c02081c1e038380c1c0e0e061c1c18001c1e383f04ce1f8707c271c3e2393b4da4aa000000039369920000fddfcdd621ff7b99824287ef7baffba000fed000),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe000000000000000000000000000000000000000000000000000000000000000001fffffffffffffffc0000000000fffffffffe0000000000007c0003ffffff000000,0xe001e00fc0018007e001fc000c003c001f003f0007000f003e00003e001fe03fc003f01fe003fc00fe00ff007e01fe01c1fe03fc0070fe007f80381fc03c1cc763934c9d349900000000000cf6cff7bc2658c06058505f39cd36efddb000000),(0x0,0x0),(0x0,0x0)]
def g635columns : IndexTree ColumnInfo := (.fork 3 (.leaf [(8,0,627,0,6),(32,0,603,0,6),(64,0,571,0,6)]) (.leaf [(2,64,569,0,5),(16,8,611,0,5),(24,0,611,0,5),(66,0,569,0,5)]))
def g635autos : Array (List Nat) := #[[],[99,65]]
def g635levels : Nat → Packing
  | 5 => g635l5
  | 6 => g635l6
  | 7 => g635l7
  | _ => emptyPacking
def g635index : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 5 3 5 0 1 (keyg635l6)
  | 7 => lookupWord 2 9 4 7 2 1 (keyg635l7)
  | _ => fun _ => none
def g635 : Forest := ⟨635,7,fun j => g635samples[j]?.getD (0,0),g635columns,g635autos,g635levels,g635index⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geomg635 : graphValid g635 (boundsBefore knownPrev_g635) = true := by
  unfold graphValid
  refine Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨by decide +kernel, by decide +kernel⟩, ?_⟩, by decide +kernel⟩
  apply listPieces_all (d:=2)
  simp only [listPieces,IndexTree.values,List.length_append,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceDiv,List.take,List.drop]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg635_5_0 : block g635 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg635_5 : block g635 5 0 1=true := sg635_5_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg635_6_0 : block g635 6 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg635_6_2 : block g635 6 2 1=true := by
  apply cellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg635_6 : block g635 6 0 3=true := (@block_merge g635 6 0 2 1 sg635_6_0 sg635_6_2)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg635_7_0 : block g635 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg635_7 : block g635 7 0 1=true := sg635_7_0
theorem tablesg635 : checkedTables g635 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g635 0 0 0 = true)
  · exact (rfl : block g635 1 0 0 = true)
  · exact (rfl : block g635 2 0 0 = true)
  · exact (rfl : block g635 3 0 0 = true)
  · exact (rfl : block g635 4 0 0 = true)
  · exact allg635_5
  · exact allg635_6
  · exact allg635_7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low635 : Lower (vars 635) (graphGoal 635) 8 :=
  lower_forest (g:=g635) (i:=0) (hints:=16793601) (before_sound known623 valid623) geomg635 tablesg635 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps635 : List (Nat × List Nat) := [(635,[]),(699,[118,81])]
def known635 := extendKnown known623 8 maps635
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid635 : Known known635 := extendKnown_ok valid623 low635 (by decide +kernel)
def g671 : Forest := ⟨671,8,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low671 : Lower (vars 671) (graphGoal 671) 9 :=
  lower_discard (g:=g671) (ci:=(128,0,543,0,8)) (hints:=536879361) (before_sound known635 valid635) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps671 : List (Nat × List Nat) := [(671,[]),(687,[84,115]),(875,[130,50,33,97,115,82,65]),(889,[130,114,98,81])]
def known671 := extendKnown known635 9 maps671
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid671 : Known known671 := extendKnown_ok valid635 low671 (by decide +kernel)
abbrev knownPrev_g701 := known671
def keyg701l6 (i : Nat) : Nat := 0x480000
def keyg701l7 (i : Nat) : Nat := 0x2562100000340000003d8680000000a7fc8038142470000000a32f8000000000000086800000000002860035003eed4daf9193760000000c5000000040140001040000
def keyg701l8 (i : Nat) : Nat := 0xc9802976a8a803ae56a1800a4000000000000000000a60000000006200000c5008000067000000000000880000b0000002804c601000000041000
def g701d5 (i : Nat) : Nat := 0x4fa7718143
def g701l5 : Packing := (1,3,4,0,0,0,0,g701d5)
def g701d6 (i : Nat) : Nat := 0x2a1202a0400a4144280411c03178018a6006c0100000280fe58a00fe58600fe54a00fe50e00fe50a00fe4c600be99a00d795633de95600ed91211ee91200e78ce44db88a55fc84600be18143
def g701l6 : Packing := (15,2,4,0,0,7,0,g701d6)
def g701d7 (i : Nat) : Nat := 0xbd103010230988319cc2384c4126b6ba286f1a79f3d37efcb78c9180ff007f54bfa87fd42fe98ff4c3fa41fd10bf2aef913ec23fa00
def g701l7 : Packing := (12,1,4,0,0,7,0,g701d7)
def g701d8 (i : Nat) : Nat := 0x32ba13f
def g701l8 : Packing := (1,0,4,0,0,0,0,g701d8)
def g701samples : Array (Bits × Bits) := #[(0x3ffe0000fff0001fffc0001ffe000fff8000fc001fffc0001ffe000fff0000003ffe000fc003ffe0000fff00000000007ff800000000007ffc0007e00000003f000ff3e383e38381f80700e003aaafaa2fa8802f80fb5f33f33fbb659cc0e0c,0xaabd5afea9eabfd55fabbfd57d5ffacf96ff6ebfeabfabbfd4fd5ffa9f2bfdbfd6fe5ffef3ff75d5afead6ad7f5af6d7aeb96bfddfbafbfebcb5ff5ddfdd7dfeeeffff7f3bbf3bbcdfdf7b6f6dbbe6ba70bbdcb6eade9b555ebafbb6d9fd5e5c),(0x0,0x0),(0x3fffffff0000001fffffffe000000fffffff00001fffffffe000000ffffffc003ffffffffffffffffff0000001fff0007fffffe001ffe07ffffff80000fff03ffff38303e303e3ffc1c7c7f8fe333033bff2e83020fd130330382067f2cc8cf,0x30018028c0cc15181230251859854c02204448898c2430251895894c04412112989484a400940018028c06c0698004033012024816c020480901221412e01024009418100a100a084c0c182304a183102931ba9322462455514582041528c8ca),(0xfc00000000000001ffffffffffffff000000000001ffffffffffffff0000000003ffffff00003fffffffffffffe0000007ffffffffe00007fffffffffff00003ffffc03fc03fc03f1fe07f8ff1fc3c03c303cf03fc0fc50330331c3861cf0f0f,0xc3260c430d30c86080c1086002001064c31183123108c10860220210c98c46246021010819219860c4306106020c9864c3043010800c4d131218440084062688042080234023401500a02504a10c3c8586864508942952aaa4921c2860870505),(0xfffffffffffffffe00000000000000000000000001fffffffffffffffffffffffc00000000003ffffffffffffffffffff800000000000007fffffffffffffffc0000ffc0003fffc01fff800ffe3fc003fc03f003fff00603c03ce03f81f00ff0,0x8108c004011811b0231816c16608b04660c2cc031023180c40c601001881882c61630a2c6208108c082084c102081043843611b10b0642021880118884000a8c6694000141280155500094833c222701198a262c209555a28e01681700a50),(0xfffffffffffffffffffffffffffffffffffffffffe00000000000000000000000000000000003ffffffffffffffffffffffffffffffffff800000000000000000000ffffffc000001ffffff0003ffffc0003fffc000028cc0cc0ffc001fff000,0x3000f001801e001c003e007007800c0078000f003e003e00f80f801e01f01f00f807c0c0f801000f0004007000c006002003801c00c0003c01f0181f007830c0f87254128000001a5a4a400029a6302023dcb2428412555492d30001fd5000),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0000000000000000000000000000000000000000000000000000000ffffffffffffe0000000003ffffffffc0000000030f00f00fffffe000000,0x3c01f000e00e001e003c001801800f00780003001c003c001001000e00e00200300180003003e01f000f80f801f00f807c07c01e01f0187c03e0061e00f80c30f0084a9a529a52680000000001658c7d6c40140850849aaaa282cfbea000000),(0x0,0x0)]
def g701columns : IndexTree ColumnInfo := (.fork 5 (.fork 2 (.leaf [(4,0,697,0,6),(32,0,669,0,6)]) (.leaf [(128,0,573,0,6),(0,1,188,0,5),(12,0,689,0,5)])) (.fork 2 (.leaf [(24,0,677,0,5),(132,0,569,0,5)]) (.leaf [(160,0,541,0,5),(16,1,172,0,4),(32,1,156,0,4)])))
def g701autos : Array (List Nat) := #[[],[84,115]]
def g701levels : Nat → Packing
  | 5 => g701l5
  | 6 => g701l6
  | 7 => g701l7
  | 8 => g701l8
  | _ => emptyPacking
def g701index : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 5 3 5 0 1 (keyg701l6)
  | 7 => lookupWord 11 53 6 9 4 1 (keyg701l7)
  | 8 => lookupWord 9 46 6 9 4 1 (keyg701l8)
  | _ => fun _ => none
def g701 : Forest := ⟨701,8,fun j => g701samples[j]?.getD (0,0),g701columns,g701autos,g701levels,g701index⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geomg701 : graphValid g701 (boundsBefore knownPrev_g701) = true := by
  unfold graphValid
  refine Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨by decide +kernel, by decide +kernel⟩, ?_⟩, by decide +kernel⟩
  apply listPieces_all (d:=2)
  simp only [listPieces,IndexTree.values,List.length_append,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceDiv,List.take,List.drop]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg701_5_0 : block g701 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg701_5 : block g701 5 0 1=true := sg701_5_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg701_6_0 : block g701 6 0 9=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg701_6_9 : block g701 6 9 6=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg701_6 : block g701 6 0 15=true := (@block_merge g701 6 0 9 6 sg701_6_0 sg701_6_9)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg701_7_0 : block g701 7 0 4=true := by
  apply cellsBlock (ar:=6) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg701_7_4 : block g701 7 4 8=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg701_7 : block g701 7 0 12=true := (@block_merge g701 7 0 4 8 sg701_7_0 sg701_7_4)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg701_8_0 : block g701 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg701_8 : block g701 8 0 1=true := sg701_8_0
theorem tablesg701 : checkedTables g701 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g701 0 0 0 = true)
  · exact (rfl : block g701 1 0 0 = true)
  · exact (rfl : block g701 2 0 0 = true)
  · exact (rfl : block g701 3 0 0 = true)
  · exact (rfl : block g701 4 0 0 = true)
  · exact allg701_5
  · exact allg701_6
  · exact allg701_7
  · exact allg701_8
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low701 : Lower (vars 701) (graphGoal 701) 9 :=
  lower_forest (g:=g701) (i:=0) (hints:=536879876) (before_sound known671 valid671) geomg701 tablesg701 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps701 : List (Nat × List Nat) := [(701,[]),(859,[130,50,98,82,115,33,65])]
def known701 := extendKnown known671 9 maps701
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid701 : Known known701 := extendKnown_ok valid671 low701 (by decide +kernel)
abbrev knownPrev_g847 := known701
def keyg847l6 (i : Nat) : Nat := 0xa800000
def keyg847l7 (i : Nat) : Nat := 0xb00000892000015401e3f640000348000000fc79800880000156000000001d7000e8000000317ec00000000000d1b080001040000001
def keyg847l8 (i : Nat) : Nat := 0x194002180000000024000c9802420000000000084003aa0022108ce0051800010900158000000717e400000000000000
def g847d5 (i : Nat) : Nat := 0x4fa7759010
def g847l5 : Packing := (1,3,3,0,0,0,0,g847d5)
def g847d6 (i : Nat) : Nat := 0x408021faaaaaaaaa00be99810db95622dd95611de95410ed91211ee91010d78ce55eb88a44fc84410be58810be18131be18121
def g847l6 : Packing := (12,2,3,0,0,4,0,g847d6)
def g847d7 (i : Nat) : Nat := 0x2811c0a02214a532fa652483fc23fd53fea17f4d3fa63fd21bf2aef913ec23f810
def g847l7 : Packing := (10,1,3,0,0,5,0,g847d7)
def g847d8 (i : Nat) : Nat := 0x680ff
def g847l8 : Packing := (1,0,3,0,0,0,0,g847d8)
def g847samples : Array (Bits × Bits) := #[(0x7ffe0007fff80003ffc003fff80007e003fffc0000fffc000fffc0007f000fff8000000ffff00007ff8007ffc000fffc0007f8003fff80007e000001fe00001fc3e0e0f0e0e07c1c7038001b37e34f9277c7e1e03fffe3fcb39798cd6e18,0x6d6b54ad77b296b75b5a99bbba5355aeb55fad555baad6aa9babe952ad5b6af5b5596addab5b156b76b5935bf5a2ad76b4cad776a5bd6d515aaf55ddedab69d6dfffd3f4e6f8e6f37f1e79b9b6190da33a8a0b4f21a0460003ffb39799cd6e39),(0xffff80000007fffffffc000003fffffff80003ffffffff0000000fffffff80000ffffffffffffffffff8000007ffffffffffffffffffffffffff80003fffffffffe20300f880f8ffe01ffffe3f1dc803b01f9ff803ffd80c7c6f02061f0ff87f,0x4042108842200422021211211002000420490800110084809202400000020241201000880202004204211211210008042080822001080800100204818800008080000000200020210004108812190803300a08080000060003ff020611084831),(0x7fffffffffffffc000000000003fffffffffffffff000000000000ffffffe000ffffffffffffff8000000fffffff800003fffffffffffc001fffff01c03ff00ff00fc7fe07e3fc7e1f003c01be40ffdf80a03e01c3c181cf18f9c,0x860c663198c420c41060020023186630c1923218620c180c20308c63318c4c98c1820c11306c218c20c6046046333198c01300443611b06260c4010830cc0104093403350099005425202a1284a0f494c854a51555d8b166f4003c180ca1850c),(0xfffffffffff800000000000000000000000003fffffffffffffffffffffffffff0000000000fffffffffffffffffffff0000000000003ffffffffffffffe0000001ffc0000ffff007fff803ff8fe0003ffe3f80ffe0022338190c01fe0fe0fe0,0x87000c00300c7006380dc0dc06380c70605c0618030e030c0c3018406100021061c30e0c3804600470018018004002006e01b80c02e01840308001101004c18e24a540000224a004a4a8025204e010913235a2a8a010c9908b5c005405e0ae0),(0x0,0x0),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffc0000000000000000000000000000000000000fffffffffffffffffffffffffffffffffc0000000000000000000001fffffff0000007fffffc000fffffc0003fff0000015cc0260ffe000fff000,0xf8007001c00f8007c00e00e007c00f80006007e003f003f00fc01f807e0703e07e03f00fc00780078002002003801c007001c00003001f803f0181e01f0701f038e99464a00000073934d00006651cc0221f7b30e8a28ddac00e94000f7b000),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000001fffffffffffff8000000000fffffffffc0000000025f00380ffffff000000,0xf0007801e007000780030030038007000018038003c000c003000e00380000c008004001000f800f8007c07c07c03e00f803e00707c03e007c0061e03e0181e00c11229894cc949a000000000091ae12ec5c000411141322534a16babf000000)]
def g847columns : IndexTree ColumnInfo := (.fork 2 (.leaf [(0,1,334,0,7),(1,0,332,2,5)]) (.leaf [(12,0,835,0,5),(320,0,527,0,5),(2,0,332,0,4)]))
def g847autos : Array (List Nat) := #[[],[131,98]]
def g847levels : Nat → Packing
  | 5 => g847l5
  | 6 => g847l6
  | 7 => g847l7
  | 8 => g847l8
  | _ => emptyPacking
def g847index : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 5 3 5 0 1 (keyg847l6)
  | 7 => lookupWord 9 45 6 9 4 1 (keyg847l7)
  | 8 => lookupWord 8 37 6 9 4 1 (keyg847l8)
  | _ => fun _ => none
def g847 : Forest := ⟨847,8,fun j => g847samples[j]?.getD (0,0),g847columns,g847autos,g847levels,g847index⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geomg847 : graphValid g847 (boundsBefore knownPrev_g847) = true := by
  unfold graphValid
  refine Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨by decide +kernel, by decide +kernel⟩, ?_⟩, by decide +kernel⟩
  apply listPieces_all (d:=2)
  simp only [listPieces,IndexTree.values,List.length_append,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceDiv,List.take,List.drop]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg847_5_0 : block g847 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg847_5 : block g847 5 0 1=true := sg847_5_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg847_6_0 : block g847 6 0 12=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg847_6 : block g847 6 0 12=true := sg847_6_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg847_7_0 : block g847 7 0 4=true := by
  apply cellsBlock (ar:=6) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg847_7_4 : block g847 7 4 6=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg847_7 : block g847 7 0 10=true := (@block_merge g847 7 0 4 6 sg847_7_0 sg847_7_4)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg847_8_0 : block g847 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg847_8 : block g847 8 0 1=true := sg847_8_0
theorem tablesg847 : checkedTables g847 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g847 0 0 0 = true)
  · exact (rfl : block g847 1 0 0 = true)
  · exact (rfl : block g847 2 0 0 = true)
  · exact (rfl : block g847 3 0 0 = true)
  · exact (rfl : block g847 4 0 0 = true)
  · exact allg847_5
  · exact allg847_6
  · exact allg847_7
  · exact allg847_8
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low847 : Lower (vars 847) (graphGoal 847) 9 :=
  lower_forest (g:=g847) (i:=0) (hints:=12901687553) (before_sound known701 valid701) geomg847 tablesg847 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps847 : List (Nat × List Nat) := [(847,[]),(941,[98,118,81,130,50,65])]
def known847 := extendKnown known701 9 maps847
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid847 : Known known847 := extendKnown_ok valid701 low847 (by decide +kernel)
abbrev knownPrev_g861 := known847
def keyg861l7 (i : Nat) : Nat := 0x3a80e78000000004822800000000000021
def g861d6 (i : Nat) : Nat := 0x22d468110906cb1b48903bc67ee22fd007d4c7f241f830
def g861l6 : Packing := (6,1,3,0,0,6,0,g861d6)
def g861d7 (i : Nat) : Nat := 0x218ff
def g861l7 : Packing := (1,0,3,0,0,0,0,g861d7)
def g861samples : Array (Bits × Bits) := #[(0xffe00003fffe0000fff8000fe0007fffe00001ffff0000000000007fff80003fe0003fffe00003fff800000000001fff8000ffff00001ff0000000007f8001ffc3f0e01f800e03f800707000c18fff827f831ffc001fc7fff07feccc2ce0ce0c,0x5d5efbab9cd5defab397ef6e9ffaaead5dd5d53aaadeaf5eadbd5add597eafbb9fd77a2d5d7baba9575bebabb75ebd5975fed6a2ebabdb4ebd6f6d7fed7befffebf4f4dfcd6f1bfe6b7c79b6d5856e8b5a9293f5553e44526a53eccd6ce5ce5c),(0x0,0x0),(0xfffffffc00000000fffffff000007ffffffffe000000001fffc0007fffffffc000003ffffffffc00000003fff8001fffffffffffffffe0000007ffc07ffffe3e0380ff1c0f8fe3c07c7ffe3fde77800c601c1f01e01ff800007f0f0b308cf8cf,0x91949232d6996b4c02248448d66348c1891919a32ce8c988c13193119248c912d665ac41961232cd659d32c0258cd612592460c4b230926b26720824805248160280350c058320c02c149a12dfd7a25fe856b711e156aff76ef70f0b308ca8ca),(0xffffffffffffffff0000000000007fffffffffffffffffe00000007ffffffffffffffffffffffffffffffc0000001ffffffffffffffffffffff800007fffffc003ff001ff00fffff807fffc7e078000e7fff1ffe001fff83f07c300c3ff0ff0f,0x60020c00020001018c03183008c03060060600c1003020306060c0604030200008000860020c0008000400cc01300040008030800c100000800318900008040011500009004490a80292484202804200329482a00891008910830000a505505),(0x7fffffffffffffffffffffffff800000000000003fffffffffffffffffffffffe0000000ffffffffffffffffffff800001fffc00001ffff003ffff807ff8ff80000f801fe3ffffe001807f83c00fc0ff0ff0,0x1818c30318c18c60a306c60c1b300c0811818030208c0c0c08181058186c0c231b06300818430301061183010604185861b08400c302000c3044400049630daa680000154920025449004920d585480b501293d1550204526a53c00d40a50a50),(0x0,0x0),(0xffffffffffffffffffffffffffff80000000000000000000000000000000000000003fffffffffffffffffffffffffffffff00000000000000000000000001ffffffffe0000003ffffff8000fffffff0001ffc000000007c0003fff000fff000,0xe000fc001f000f803c00f80003c00ff001fe003fc00ff00ff01fe01fe00ff03c03f800f0007c000e001e000e0018006001c007f003fc03803f807e0e0e03f0cc8da64640000003a7724e000066b98f30023ffd62660c1e9cb39ebaa000fff000),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc000000000000000000000000000000000000000000000000000000001fffffffffffffffc0000000000ffffffffffe000000000067f8003ffffff000000,0x1f0003e001f000c00700001c0070001e0001c000f0001000200060007000001c003f001f8003f007e003f007e01f807e00f800fc001c0fc0078030707c01313248989a6e499000000000009946704ffc400281981021634c61455ff5000000)]
def g861columns : IndexTree ColumnInfo := (.fork 3 (.leaf [(4,0,857,0,6),(0,1,348,0,5),(1,0,332,16,5)]) (.leaf [(256,64,541,0,5),(16,1,332,0,4),(17,0,332,0,4)]))
def g861autos : Array (List Nat) := #[[]]
def g861levels : Nat → Packing
  | 6 => g861l6
  | 7 => g861l7
  | _ => emptyPacking
def g861index : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 3 18 5 7 3 0 (keyg861l7)
  | _ => fun _ => none
def g861 : Forest := ⟨861,7,fun j => g861samples[j]?.getD (0,0),g861columns,g861autos,g861levels,g861index⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geomg861 : graphValid g861 (boundsBefore knownPrev_g861) = true := by
  unfold graphValid
  refine Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨by decide +kernel, by decide +kernel⟩, ?_⟩, by decide +kernel⟩
  apply listPieces_all (d:=2)
  simp only [listPieces,IndexTree.values,List.length_append,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceDiv,List.take,List.drop]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg861_6_0 : block g861 6 0 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg861_6 : block g861 6 0 6=true := sg861_6_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg861_7_0 : block g861 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg861_7 : block g861 7 0 1=true := sg861_7_0
theorem tablesg861 : checkedTables g861 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g861 0 0 0 = true)
  · exact (rfl : block g861 1 0 0 = true)
  · exact (rfl : block g861 2 0 0 = true)
  · exact (rfl : block g861 3 0 0 = true)
  · exact (rfl : block g861 4 0 0 = true)
  · exact (rfl : block g861 5 0 0 = true)
  · exact allg861_6
  · exact allg861_7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low861 : Lower (vars 861) (graphGoal 861) 8 :=
  lower_forest (g:=g861) (i:=0) (hints:=13019128580) (before_sound known847 valid847) geomg861 tablesg861 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps861 : List (Nat × List Nat) := [(861,[]),(925,[118,130])]
def known861 := extendKnown known847 8 maps861
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid861 : Known known861 := extendKnown_ok valid847 low861 (by decide +kernel)
abbrev knownPrev_g967 := known861
def keyg967l6 (i : Nat) : Nat := 0x20000
def keyg967l7 (i : Nat) : Nat := 0x5900c8058000000000
def g967d5 (i : Nat) : Nat := 0xbe99810
def g967l5 : Packing := (1,2,2,0,0,0,0,g967d5)
def g967d6 (i : Nat) : Nat := 0xd460147d847f401f810
def g967l6 : Packing := (3,1,2,0,0,3,0,g967d6)
def g967d7 (i : Nat) : Nat := 0x48ff
def g967l7 : Packing := (1,0,2,0,0,0,0,g967d7)
def g967samples : Array (Bits × Bits) := #[(0xf80000fffc0000000ffffe00001fffc0007fffc00007f0007fff00000001ffffc00003fff8000fffe0000ffff80000fe0000003fffe00007fc0003fe000001ffc1fc00fc1c0e03f070e00e0080e39ffc307ffc07f3f007ffff839c3398cdc2d8,0xb7ad56aa9bdd75b56cacadbadadab1b76f52d2b5b5b6afedcb52db5776abac95b5bb5b5a36b7eac95adb6ad296b5aed5f7bdb575ac5ad6f7535bb769badbffffe9ff1afe9e6f9bfa7cf36f36849207b42817d423d3d2884212439c7399cdc6d9),(0xffffff00000007ffffffffffffe00000007ffffffff800007ffffffffffffffffffffc0000000fffffffffffffffff00000ffffffffffffffffffffffffffe1e01e01fe01f8fff807ffc7fff871c64003f9c003fffffff801ffe10c21f0f0fff,0x2108048813102000480809108092212442008020202429410200820204010801211012122424408010804080042004852221002108108420021100011080000a00600a4006028900143022128492048028144022818280421242104211090491),(0xfffffffffffff8000fffffffffffffffff800000000000007fffffff8001fffffffffffffffff00000000ffffffffffffff0003ffffffff8000003fffffe01e001ffe0ffe00fe3ff80ff8fc7f81ff80031e7ffc403fc0183e3801f3c1cf1f31c,0xc201980320064619810130201300020004181b0606c0c20e0064006420cc30260602606040c0830d830d830320c0c80041061986008300421860380020108aa0008520a6a0052092804505442804f91152a11944466c1214a5940a3c0ca0a30c),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0xfffffffffffffffffffffffffffffff800000000001fffffffffffffffffffffffff000000000000000003ffffffffffffffc00000001fffe0000fffff003ffff000ff8ffe07fffc1f80007fc00067c1c03e03fe0fe03e0,0x31e033c06780de0031c0031c00c40188031c00c70000880c780c7818f00138002380008001000e000e001bc006f01805c03e00310018800002204c031c2c644a000028c8a002ab290009a019202838c1e890cd6c44208c6c8d402940f60360),(0xfffffffffffffffff0000000000000000000000000000000000000000001ffffffffffffffffffffffffffffffffffffffffffc00000000000000000000001ffffffff00000003fffffff000ffff800001fffff800000003e003ffc000fffc00,0x43e003c027800e00e3e01c3e01cf839f063e038f8070cf06f80ef805f01c1c0383c038307060c101c100c1c07070001860820383e1c1f046383c271c3e13156ad2a53000000034c4e9a4000d7fb0622ad5ee2b98880c5eb5a6bf5c0005f5c00),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe000000000000000000000000000000000000000000000000000000000000000001fffffffffffffffc0000000000fffffffffe0000000000007c0003ffffff000000,0x7c000c0038007000fc001fc001f003e007c003f00000f007000f0006001fe003fc003fc07f80fe01fe00fe007f800e1f80fc03fc01fe00783fc0381fc01c19931d39cd31349d00000000000e6dfd7c33e170332030b07739372bfd6bf000000)]
def g967columns : IndexTree ColumnInfo := (.leaf [(0,1,454,0,5),(4,128,835,0,5),(64,256,647,0,5)])
def g967autos : Array (List Nat) := #[[],[135,98]]
def g967levels : Nat → Packing
  | 5 => g967l5
  | 6 => g967l6
  | 7 => g967l7
  | _ => emptyPacking
def g967index : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 5 3 5 0 1 (keyg967l6)
  | 7 => lookupWord 2 10 4 7 2 1 (keyg967l7)
  | _ => fun _ => none
def g967 : Forest := ⟨967,7,fun j => g967samples[j]?.getD (0,0),g967columns,g967autos,g967levels,g967index⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geomg967 : graphValid g967 (boundsBefore knownPrev_g967) = true := by
  unfold graphValid
  refine Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨by decide +kernel, by decide +kernel⟩, ?_⟩, by decide +kernel⟩
  apply listPieces_all (d:=0)
  simp only [listPieces,IndexTree.values,List.length_append,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceDiv,List.take,List.drop]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg967_5_0 : block g967 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg967_5 : block g967 5 0 1=true := sg967_5_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg967_6_0 : block g967 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg967_6 : block g967 6 0 3=true := sg967_6_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg967_7_0 : block g967 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg967_7 : block g967 7 0 1=true := sg967_7_0
theorem tablesg967 : checkedTables g967 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g967 0 0 0 = true)
  · exact (rfl : block g967 1 0 0 = true)
  · exact (rfl : block g967 2 0 0 = true)
  · exact (rfl : block g967 3 0 0 = true)
  · exact (rfl : block g967 4 0 0 = true)
  · exact allg967_5
  · exact allg967_6
  · exact allg967_7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low967 : Lower (vars 967) (graphGoal 967) 8 :=
  lower_forest (g:=g967) (i:=0) (hints:=26323452161) (before_sound known861 valid861) geomg967 tablesg967 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps967 : List (Nat × List Nat) := [(967,[]),(997,[134,81,65,114,49])]
def known967 := extendKnown known861 8 maps967
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid967 : Known known967 := extendKnown_ok valid861 low967 (by decide +kernel)
def g639 : Forest := ⟨639,9,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low639 : Lower (vars 639) (graphGoal 639) 10 :=
  lower_discard (g:=g639) (ci:=(32,0,607,0,9)) (hints:=16785665) (before_sound known967 valid967) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps639 : List (Nat × List Nat) := [(639,[]),(759,[84,115]),(887,[131,84,115,98]),(951,[134,81,114,50,65]),(955,[98,134,114,81]),(1011,[98,99,81,131,114,65])]
def known639 := extendKnown known967 10 maps639
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid639 : Known known639 := extendKnown_ok valid967 low639 (by decide +kernel)
abbrev knownPrev_g703 := known639
def keyg703l9 (i : Nat) : Nat := 0xc400000025800001900000006000
def keyg703l10 (i : Nat) : Nat := 0x35ac00000030800000000000000000
def g703d8 (i : Nat) : Nat := 0x277ac1301c6f43a7a80fdc01117f972802feb9401fa88a00
def g703l8 : Packing := (4,2,3,0,0,5,0,g703d8)
def g703d9 (i : Nat) : Nat := 0x948ba2c0dd21462e893174486a8a80ff803fd20fb88bfa00
def g703l9 : Packing := (4,1,3,0,0,7,0,g703d9)
def g703d10 (i : Nat) : Nat := 0x21a27f
def g703l10 : Packing := (1,0,3,0,0,0,0,g703d10)
def g703samples : Array (Bits × Bits) := #[(0x1ffffc0000000000000000001fffff000000ffe0000000001ffc00000000ffff1ffc3f381ffc3f801f80700fff1f007f003807e703807001f71f0f7ffd8760dbf871c0c70017ffdc006fe1fc061dffe1f87fc137fdf7b8c70fe38c1f60e18,0xfff7dbfcbdbffbbdbff7dbff5fffdbff2f6fffeefdfbffffbffbdf3dbffefffffffbffebf7ddfff3fdddfcd7b6fffdfff7fddbfb7f7dbfb7b6df7ff5b7f7db6ea9bbb7ff7cf77b7ff5deeefabfeeffa6fafbddff607fdf7bdcf1fffddbf6de39),(0x1ffffffffffc00001fffff001fffffffffff00000000ffffffffffffffff00f803e0383f03e03c0f1c0ffc70f81f1c781e3e3f07e3e3fc7ef763707801b8831c03f63107b007801ec0700ffff80600000007fe1b30c6249c366a4c8c6487f,0x526491282914912929649092045311120a4524445551496911200029149400000580160280d00e014050c05182038050c180c0a1301c0a11824f5775a7909b6ca988336d34b30878314c2608b5ae7f867879ccef60330c6248c164a488c44831),(0x1fffffffffffffffe00000001fffffffffffffffffff00001ffffffff8000f001c003fc01c003ff01ff07f8f001fe07fe03fc7f803fc7f8f0783818001c0f3fffc7839e7c018001f007ff1fc061c01e0007fc134010038e7c8738f1078f9c,0x849800410021020002000224608402244008488000021200224c000021200290300040011400400089000802103000a60214014843001482109028801801000302430492ca4c118040b041300a000038828211101fc01001002883107103850c),(0xfffe000000000000000000000001fffffffffffffffffffffffe00000000000f0001fffc0001fffc0001fff800fffe0007fffc007fffc007ff1f803fe0001ff03e0007fc1f8001fffe0007ffe0000188001f87800203e07c0f80f83f01f80fe0,0x1820e18e0e061c0e0c38e0c38918604083818100006060420400898e060724250001aa6c00009254000155980044960004ab680014a68004e405803fe2a22db07c9059241591242a9a0016cde0832e432d2ca6a5a003e0540f80502f00a80ae0),(0xfffffffffffffffffffffffffffe00000000000000000000000000000000000ffffe00000001fffffffe000000fffffff80000007ffffff8001fffc000001fffc00007ffe00001fffffff80000000608001ff800047c007ff000ffc001fff000,0xe0c102003038203030410304000183870c0e0e089983838c38711230383848cada9a0000000164a2d59400000099293b5000000069492720001a7fc01544124e812126db6866415561dee010030451a4d2d3595a407c002bd000afc00156d000),(0xffffffffffffe00000000000000ffffffffffffff80000000001fffffffffe000000007fffffffe000000000000001817e1e00000087fff800000fffffe000000,0xff0003f0003fc0003f8003f801e003f8000ff000e003fc003f801c003fc00f036322cc89a51400000000000000ee4dcda74d92720000000000133ad131878002000207ff7cf7791980d482602c0862a0e2e3999c606a9a000000fffdda000000),(0x0,0x0),(0xfffffffffffffffffffffffffff0000000000000000000000001ffffffffffffffffff800000000000000000000006017fe000000107fffffffff000000000000,0x1fc003fc0003fc001fc000e01fc000ff0000f01fc000fc001e03fc000700c8c4d31324a69b93b26e9a6e4e40000000000000000000000000cc52ec6783ffcfdbc780001008066030b0481d0301d471d1c6663801565feffd7000000000000),(0x0,0x0)]
def g703columns : IndexTree ColumnInfo := (.fork 2 (.leaf [(2,0,701,0,9),(4,0,699,0,8)]) (.leaf [(24,0,679,0,8),(160,0,543,0,8),(0,1,190,0,7)]))
def g703autos : Array (List Nat) := #[[],[84,115]]
def g703levels : Nat → Packing
  | 8 => g703l8
  | 9 => g703l9
  | 10 => g703l10
  | _ => emptyPacking
def g703index : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 2 16 4 7 2 1 (keyg703l9)
  | 10 => lookupWord 2 16 4 7 2 1 (keyg703l10)
  | _ => fun _ => none
def g703 : Forest := ⟨703,10,fun j => g703samples[j]?.getD (0,0),g703columns,g703autos,g703levels,g703index⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geomg703 : graphValid g703 (boundsBefore knownPrev_g703) = true := by
  unfold graphValid
  refine Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨by decide +kernel, by decide +kernel⟩, ?_⟩, by decide +kernel⟩
  apply listPieces_all (d:=2)
  simp only [listPieces,IndexTree.values,List.length_append,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceDiv,List.take,List.drop]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg703_8_0 : block g703 8 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg703_8_1 : block g703 8 1 3=true := by
  apply cellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg703_8 : block g703 8 0 4=true := (@block_merge g703 8 0 1 3 sg703_8_0 sg703_8_1)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg703_9_0 : block g703 9 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg703_9_2 : block g703 9 2 2=true := by
  apply cellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg703_9 : block g703 9 0 4=true := (@block_merge g703 9 0 2 2 sg703_9_0 sg703_9_2)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg703_10_0 : block g703 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg703_10 : block g703 10 0 1=true := sg703_10_0
theorem tablesg703 : checkedTables g703 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g703 0 0 0 = true)
  · exact (rfl : block g703 1 0 0 = true)
  · exact (rfl : block g703 2 0 0 = true)
  · exact (rfl : block g703 3 0 0 = true)
  · exact (rfl : block g703 4 0 0 = true)
  · exact (rfl : block g703 5 0 0 = true)
  · exact (rfl : block g703 6 0 0 = true)
  · exact (rfl : block g703 7 0 0 = true)
  · exact allg703_8
  · exact allg703_9
  · exact allg703_10
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low703 : Lower (vars 703) (graphGoal 703) 11 :=
  lower_forest (g:=g703) (i:=0) (hints:=536879361) (before_sound known639 valid639) geomg703 tablesg703 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps703 : List (Nat × List Nat) := [(703,[]),(831,[135,50,65]),(891,[130,50,81,115,98,65])]
def known703 := extendKnown known639 11 maps703
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid703 : Known known703 := extendKnown_ok valid639 low703 (by decide +kernel)
def g735 : Forest := ⟨735,9,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low735 : Lower (vars 735) (graphGoal 735) 10 :=
  lower_discard (g:=g735) (ci:=(64,0,671,0,9)) (hints:=553656577) (before_sound known703 valid703) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps735 : List (Nat × List Nat) := [(735,[]),(751,[84,115]),(1003,[99,33,129,115,82,65]),(1017,[118,130,81])]
def known735 := extendKnown known703 10 maps735
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid735 : Known known735 := extendKnown_ok valid703 low735 (by decide +kernel)
abbrev knownPrev_g863 := known735
def keyg863l7 (i : Nat) : Nat := 0x70
def keyg863l8 (i : Nat) : Nat := 0x26540f0000000010
def keyg863l9 (i : Nat) : Nat := 0x12c019000002d00000000088a0400
def keyg863l10 (i : Nat) : Nat := 0x3b700000014002800000000
def g863d6 (i : Nat) : Nat := 0x67a801829dd31
def g863l6 : Packing := (1,4,3,0,0,0,0,g863d6)
def g863d7 (i : Nat) : Nat := 0xbfa884c600fd233846009ed829dd31
def g863l7 : Packing := (3,3,3,0,0,0,0,g863d7)
def g863d8 (i : Nat) : Nat := 0xedb0350738e8f279400002ff3ba63fe4c600bf8e098fd633847ed19c01fc84600
def g863l8 : Packing := (6,2,3,0,0,6,0,g863d8)
def g863d9 (i : Nat) : Nat := 0x3a948d324c5d3e9e70e3b4d970da5aed8c80ff4c7de33fd847fa00
def g863l9 : Packing := (4,1,3,0,0,7,0,g863d9)
def g863d10 (i : Nat) : Nat := 0x2163537f
def g863l10 : Packing := (1,0,3,0,0,0,0,g863d10)
def g863samples : Array (Bits × Bits) := #[(0x1ffffc000000000000000001fffffc000003ff80000000007ff00000000fffe1fe1f8381ff1f000f870380ffc3c1c0f838e07c707007001dc1c53fff19605dfce45989eff9efee0003f87f007f97fffe07fe1f7ece7c1798e999adf60e18,0xb7af7b6acbdbabbbedbbedd5d7ffedd5cbdbabfbb77efbff6f5eeecfddbefffffff5fe9fd3cdff9fd6efc79be6fff3f5eefe3cf37e7b7db736ddebc42bdd1dfb57d4d655c91bd9ffaf5acfc87d24d17e999da5351ffece7db799ebb9adf6de39),(0x1ffffffffffc0000fffffc01fffffffffffc0000000ffffffffffffffff00f00301c03f0381f078c07e3ff0e03c1f8c03fffe07c7e3fc7e5c206c200199c6600fc678e3fff300e100400ffff98e001e0003fe990082c861f0981fec6487f,0x20064200811001124032080081028800811001110524016440080004801400000500200800c0180502840180a2020040480008212018141102448284024009a94640504108121130841044002424011a090880111f9008288611010108c44831),(0x1fffffffffffffff00000001fffffffffffffffffff000007fffffff8001f001c01ffc01c01ff80ff803f8f003fe00ffc0fc7f807fc7f8f9fc38fc001e1c7800e7860fcc01c00fe007ff7fc00180000007fe0360f04f181c8e1e31078f9c,0xc4c98c0c126230208100b1191a25311912623220004892098993000911202290b0014014d400c00a5808c80148300196004a405446802a8250997d68fc84b656b882ae96d34c42c10be092d55ac17e65b4b56f6ea060f047180c8e143103850c),(0xffffe00000000000000000000001ffffffffffffffffffffffff80000000000e0001ffe00001ffe0000ffffc00fffc0000ffff007fff8007ff1e003f00001fe07fff07f80ff001fff00007ff800067001e1e07c0160300701fe0f01fc1f80fe0,0x1020030e000c1c0061c0060e04800602000c040000020400200046006070422000092a00000012000011228004454000094950009250004a402001700084100421901682cb085125000252280020098424210805f8300000540500bc0a80ae0),(0xfffffffffffffffffffffffffffe00000000000000000000000000000000000ffffe00000001fffffff0000000ffffffff0000007ffffff8001fffc000001fff800007fff00001fffffff80000000608001ff800047c007fe000ffe001fff000,0x60c1040038302030820c1810001c181c38303822670c38e0c1c488e183848cd5b34000000016a9394a00000009aa2e4aa000000724a4d20001debc02b101cfb1500d615c10910ed8f5ac0400c045166999da535007c007da000aba00156d000),(0x0,0x0),(0xffffffffffffe00000000000000ffffffffffffff80000000001fffffffffe000000007fffffffe000000000000001817e1e00000087fff800000fffffe000000,0x7f0007f0003fc000fc001fe007001fe0003fc003800fc000fe00f001fc00f066246d4c5191400000000000000ed3b3934e7269a00000000000a4c5b4c1e6000001107bef7ede64612630183904862a0e2e639c6604ba5000000fefef6000000),(0x0,0x0),(0xfffffffffffffffffffffffffff0000000000000000000000001ffffffffffffffffff800000000000000000000006017fe000000107fffffffff000000000000,0xf8001f8003fc0003f000fe000381fe0003fc0003c07f000ff000700fe00070098c99291a6269b4dce74e64d27400000000000000000000000015b3a0b3e09effbde2f801000200a80d9c020460b01d471d19c63980345afffabf000000000000)]
def g863columns : IndexTree ColumnInfo := (.fork 4 (.leaf [(4,0,859,0,9),(16,0,847,0,9),(0,1,350,0,8),(2,0,861,0,8)]) (.leaf [(8,0,855,0,8),(320,0,543,0,8),(16,1,334,0,7),(28,0,835,0,5)]))
def g863autos : Array (List Nat) := #[[]]
def g863levels : Nat → Packing
  | 6 => g863l6
  | 7 => g863l7
  | 8 => g863l8
  | 9 => g863l9
  | 10 => g863l10
  | _ => emptyPacking
def g863index : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 5 3 4 0 0 (keyg863l7)
  | 8 => lookupWord 2 9 4 6 2 0 (keyg863l8)
  | 9 => lookupWord 3 18 5 7 3 0 (keyg863l9)
  | 10 => lookupWord 2 15 4 6 2 0 (keyg863l10)
  | _ => fun _ => none
def g863 : Forest := ⟨863,10,fun j => g863samples[j]?.getD (0,0),g863columns,g863autos,g863levels,g863index⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geomg863 : graphValid g863 (boundsBefore knownPrev_g863) = true := by
  unfold graphValid
  refine Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨by decide +kernel, by decide +kernel⟩, ?_⟩, by decide +kernel⟩
  apply listPieces_all (d:=2)
  simp only [listPieces,IndexTree.values,List.length_append,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceDiv,List.take,List.drop]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg863_6_0 : block g863 6 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg863_6 : block g863 6 0 1=true := sg863_6_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg863_7_0 : block g863 7 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg863_7_2 : block g863 7 2 1=true := by
  apply cellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg863_7 : block g863 7 0 3=true := (@block_merge g863 7 0 2 1 sg863_7_0 sg863_7_2)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg863_8_0 : block g863 8 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg863_8_3 : block g863 8 3 3=true := by
  apply cellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg863_8 : block g863 8 0 6=true := (@block_merge g863 8 0 3 3 sg863_8_0 sg863_8_3)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg863_9_0 : block g863 9 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg863_9_3 : block g863 9 3 1=true := by
  apply cellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg863_9 : block g863 9 0 4=true := (@block_merge g863 9 0 3 1 sg863_9_0 sg863_9_3)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg863_10_0 : block g863 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg863_10 : block g863 10 0 1=true := sg863_10_0
theorem tablesg863 : checkedTables g863 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g863 0 0 0 = true)
  · exact (rfl : block g863 1 0 0 = true)
  · exact (rfl : block g863 2 0 0 = true)
  · exact (rfl : block g863 3 0 0 = true)
  · exact (rfl : block g863 4 0 0 = true)
  · exact (rfl : block g863 5 0 0 = true)
  · exact allg863_6
  · exact allg863_7
  · exact allg863_8
  · exact allg863_9
  · exact allg863_10
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low863 : Lower (vars 863) (graphGoal 863) 11 :=
  lower_forest (g:=g863) (i:=0) (hints:=12901687553) (before_sound known735 valid735) geomg863 tablesg863 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps863 : List (Nat × List Nat) := [(863,[]),(879,[84,131,98]),(943,[98,118,81,130,50,65]),(957,[118,130,81])]
def known863 := extendKnown known735 11 maps863
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid863 : Known known863 := extendKnown_ok valid735 low863 (by decide +kernel)
def g893 : Forest := ⟨893,9,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low893 : Lower (vars 893) (graphGoal 893) 10 :=
  lower_discard (g:=g893) (ci:=(4,0,889,0,9)) (hints:=13019128580) (before_sound known863 valid863) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps893 : List (Nat × List Nat) := [(893,[]),(927,[98,118,81,130,50,65])]
def known893 := extendKnown known863 10 maps893
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid893 : Known known893 := extendKnown_ok valid863 low893 (by decide +kernel)
def g975 : Forest := ⟨975,9,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low975 : Lower (vars 975) (graphGoal 975) 10 :=
  lower_discard (g:=g975) (ci:=(128,0,847,0,9)) (hints:=13438558465) (before_sound known893 valid893) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps975 : List (Nat × List Nat) := [(975,[]),(1005,[118,81,130,65])]
def known975 := extendKnown known893 10 maps975
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid975 : Known known975 := extendKnown_ok valid893 low975 (by decide +kernel)
def g983 : Forest := ⟨983,8,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low983 : Lower (vars 983) (graphGoal 983) 9 :=
  lower_discard (g:=g983) (ci:=(16,0,967,0,8)) (hints:=26323452161) (before_sound known975 valid975) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps983 : List (Nat × List Nat) := [(983,[]),(1013,[134,81,114,49])]
def known983 := extendKnown known975 9 maps983
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid983 : Known known983 := extendKnown_ok valid975 low983 (by decide +kernel)
def g989 : Forest := ⟨989,8,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low989 : Lower (vars 989) (graphGoal 989) 9 :=
  lower_discard (g:=g989) (ci:=(64,0,925,0,8)) (hints:=13555999492) (before_sound known983 valid983) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps989 : List (Nat × List Nat) := [(989,[])]
def known989 := extendKnown known983 9 maps989
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid989 : Known known989 := extendKnown_ok valid983 low989 (by decide +kernel)
abbrev knownPrev_g999 := known989
def keyg999l7 (i : Nat) : Nat := 0x180000
def keyg999l8 (i : Nat) : Nat := 0xa6c00000141a2f10000001000060000001
def keyg999l9 (i : Nat) : Nat := 0x596020061988000070493640083000000000000000000000
def keyg999l10 (i : Nat) : Nat := 0xa900003000000000b200110000
def g999d6 (i : Nat) : Nat := 0x47e65e884c600
def g999l6 : Packing := (1,4,3,0,0,0,0,g999d6)
def g999d7 (i : Nat) : Nat := 0x2808000ad705ad60bfa884c600dfa881c131bfa881c1319fe881c1319fa881c131fd200846339f9809dd31
def g999l7 : Packing := (7,3,3,0,0,5,0,g999d7)
def g999d8 (i : Nat) : Nat := 0x873630203cd8a51e6c996f950cb205fe774c7fc98c01fe1c131bf8e098fda33803eb08c677e1c131
def g999l8 : Packing := (7,2,3,0,0,6,0,g999d8)
def g999d9 (i : Nat) : Nat := 0x140e59660b2cb521965c9903fd31f78cffa00
def g999l9 : Packing := (3,1,3,0,0,6,0,g999d9)
def g999d10 (i : Nat) : Nat := 0x22232ff
def g999l10 : Packing := (1,0,3,0,0,0,0,g999d10)
def g999samples : Array (Bits × Bits) := #[(0x1fffff000001ffc00001fffff00000000000000000007ff00000000fffc1ff1fc00ff8fc1c0fc38380ffc3f070f8e0e00e0e0e07001901e4c78cfff85dfcc459fefe7fe0243fe4007f007edffffff83c1d7370f39bd8ecdf70996c18,0xb6f6d6ef7ad6bad6b7fdd735bbfbad6d2d6b75edd6efad6eb7ffedadd6f7ffffffe9ff9ff1affafe9e6febdbe6ffebfa7cfaf6f36faf6f37b6d90926a4ac5ee84fdca548afee7da136afa68afd28813c533150aa1ff371f39bd9ecdf71bb6db9),(0xffff00001ffffffffffffffffffffffffffffff00001fffffc007ffffffffff01e00381e01f0c0e01f8e03e3ff0e03807fc0f8fc7e0f8fffc7e90e27388b10006600fc663b004001fe3ffe007fff86e00000783fe5c24302031f00ec4399fc9f,0x2004844250841084204800211021084008420048840d084000908008840200000a00180600a08040060400c0a2040100148030302002021102490926a40812004640a0402b204401220a02003028011c111040221fc241020311008c41104891),(0x1ffffffffffe00000001fffffffffffffffe000000007fffffff8001e001c01ffe0f00ffe00ffc03f8f003ff80ff00ff8ff00fc7f8f1f0383ff3e0007800c787cc007ffe383007c07fc000c8001f803c01007cbc1c1c8f107ce18f1c,0x758180d830024180490858602cc3006418058810040300b3905000100a42150a000c008520b00a6a00a6c0148300092804b004506b00542d090500809f7e422b8894d8ac40411ca1cf08dc34ec13a2166259adca00028bc1c0c8a1028e1870c),(0x0,0x0),(0x0,0x0),(0xffffffffe0000000000000000001ffffffffffffffffffffffff80000000000e0001ffe0000fff00000ffffc00fffc0000ffff000ffff007ff1e003fc0fc00007fff07f80fff80003fc007ff800079001fe007c01a0380c01fe0f01f80fe0fe0,0x46000060000b80006e0060003700008000061000088000c2000012000c702620000410000054a000002890800524800005242000b252004a410000400ac40404a1805488d0c008036a1068a04000038422110881f8000c01280c01a00ba0da0),(0xfffffffffffffffffffffffffffe00000000000000000000000000000000000ffffe0000000ffffffff0000000ffffffff0000000ffffff8001fffc000ffffff800007fff00000003ffff80000000617e0007800047c00ffe000ffe000fff000,0xc78000880018c000c70000002380018f800c7e0018f0018fc02609c018f80b86644a000000065328c8a0000000eaaeab290000000dc9c9a00012324000b560f1881007bfd44889065df5dccc08426860e263b9cc602800e94000ff6000efb000),(0xffffffffffff000000000000000fffffffffffffff0000000001fffffff000000000007ffffffffffc00000000000180801ff8000087fff000000ffffff000000,0xf800e0f01c1f00e0f80118383c01c1f00e0f800e1f01c1f002384e0e1f004c0d56ad2ab2a530000000000000008d334c4ea49c9a40000000000faff3f60018850502b23532f1ee15c1061010100c45c699da6523407fd700000035e5d7000000),(0xfffffffffffffffffffffffffff0000000000000000000000001ffffffffffffffffff800000000000000000000006017fe000000107fffffffff000000000000,0xff001fe000ff0001e03fc001fe000ff0000fe001fe0003c0700fe00070099931b4dd39c8a4d3134d3272740000000000000000000000000dcdbbff429f0635e3f800228170198008012060b017871d9c46338057ff16ad7f000000000000)]
def g999columns : IndexTree ColumnInfo := (.fork 2 (.leaf [(0,1,486,0,8),(2,0,997,0,8)]) (.leaf [(32,0,967,0,8),(132,0,867,0,8),(320,0,679,0,8)]))
def g999autos : Array (List Nat) := #[[],[135,98],[134,114,81],[118,130,81]]
def g999levels : Nat → Packing
  | 6 => g999l6
  | 7 => g999l7
  | 8 => g999l8
  | 9 => g999l9
  | 10 => g999l10
  | _ => emptyPacking
def g999index : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 5 3 6 0 2 (keyg999l7)
  | 8 => lookupWord 4 19 5 9 3 2 (keyg999l8)
  | 9 => lookupWord 4 23 5 9 3 2 (keyg999l9)
  | 10 => lookupWord 2 15 4 8 2 2 (keyg999l10)
  | _ => fun _ => none
def g999 : Forest := ⟨999,10,fun j => g999samples[j]?.getD (0,0),g999columns,g999autos,g999levels,g999index⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geomg999 : graphValid g999 (boundsBefore knownPrev_g999) = true := by
  unfold graphValid
  refine Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨by decide +kernel, by decide +kernel⟩, ?_⟩, by decide +kernel⟩
  apply listPieces_all (d:=2)
  simp only [listPieces,IndexTree.values,List.length_append,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceDiv,List.take,List.drop]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg999_6_0 : block g999 6 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg999_6 : block g999 6 0 1=true := sg999_6_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg999_7_0 : block g999 7 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg999_7_3 : block g999 7 3 4=true := by
  apply cellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg999_7 : block g999 7 0 7=true := (@block_merge g999 7 0 3 4 sg999_7_0 sg999_7_3)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg999_8_0 : block g999 8 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg999_8_3 : block g999 8 3 4=true := by
  apply cellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg999_8 : block g999 8 0 7=true := (@block_merge g999 8 0 3 4 sg999_8_0 sg999_8_3)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg999_9_0 : block g999 9 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg999_9_2 : block g999 9 2 1=true := by
  apply cellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg999_9 : block g999 9 0 3=true := (@block_merge g999 9 0 2 1 sg999_9_0 sg999_9_2)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg999_10_0 : block g999 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg999_10 : block g999 10 0 1=true := sg999_10_0
theorem tablesg999 : checkedTables g999 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g999 0 0 0 = true)
  · exact (rfl : block g999 1 0 0 = true)
  · exact (rfl : block g999 2 0 0 = true)
  · exact (rfl : block g999 3 0 0 = true)
  · exact (rfl : block g999 4 0 0 = true)
  · exact (rfl : block g999 5 0 0 = true)
  · exact allg999_6
  · exact allg999_7
  · exact allg999_8
  · exact allg999_9
  · exact allg999_10
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low999 : Lower (vars 999) (graphGoal 999) 11 :=
  lower_forest (g:=g999) (i:=0) (hints:=22028484865) (before_sound known989 valid989) geomg999 tablesg999 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps999 : List (Nat × List Nat) := [(999,[])]
def known999 := extendKnown known989 11 maps999
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid999 : Known known999 := extendKnown_ok valid989 low999 (by decide +kernel)
def g767 : Forest := ⟨767,11,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low767 : Lower (vars 767) (graphGoal 767) 12 :=
  lower_discard (g:=g767) (ci:=(64,0,703,0,11)) (hints:=553656577) (before_sound known999 valid999) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps767 : List (Nat × List Nat) := [(767,[]),(1019,[99,81,115,130,65])]
def known767 := extendKnown known999 12 maps767
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid767 : Known known767 := extendKnown_ok valid999 low767 (by decide +kernel)
def g895 : Forest := ⟨895,11,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low895 : Lower (vars 895) (graphGoal 895) 12 :=
  lower_discard (g:=g895) (ci:=(4,0,891,0,11)) (hints:=12901687553) (before_sound known767 valid767) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps895 : List (Nat × List Nat) := [(895,[]),(959,[98,118,81,130,50,65])]
def known895 := extendKnown known767 12 maps895
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid895 : Known known895 := extendKnown_ok valid767 low895 (by decide +kernel)
def g991 : Forest := ⟨991,11,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low991 : Lower (vars 991) (graphGoal 991) 12 :=
  lower_discard (g:=g991) (ci:=(128,0,863,0,11)) (hints:=13438558465) (before_sound known895 valid895) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps991 : List (Nat × List Nat) := [(991,[]),(1021,[118,130,81])]
def known991 := extendKnown known895 12 maps991
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid991 : Known known991 := extendKnown_ok valid895 low991 (by decide +kernel)
abbrev knownPrev_g1007 := known991
def keyg1007l8 (i : Nat) : Nat := 0x1800
def keyg1007l9 (i : Nat) : Nat := 0x1f90000281ba00000000034bdc9000324d40000510000000000000000c199c000000001f000000014c008084d6800000000002000
def keyg1007l10 (i : Nat) : Nat := 0xb300000040b9000000020c23734800000000e7000000000f3000013000e9307a06000003438004320019000000000000000000754000000120000000000000000144000f380000083d68cf14c300000000000b140000000058a000002e00000000000000165000000000000000006b6003818000000000021791a000005c200087c00000fc9e134e8007a80009080004578c0000092a06900888520b84828009240380042522ce44188000000200180000800104000000000000020000080
def keyg1007l11 (i : Nat) : Nat := 0x1d48012271a00000000000000011800a2bde00000002580000000000000000000000000000000068656deed7719a580144001e780118801c3800003920000000000001a4e56848be2be77b000520002e7d50820000000128000016b00000001340000000043000200000000008102000000400100
def keyg1007l12 (i : Nat) : Nat := 0xc401f20000000000000000000067c802d601800a000000000001f094200400
def g1007d7 (i : Nat) : Nat := 0x43f8baa658220141
def g1007l7 : Packing := (1,5,5,0,0,0,0,g1007d7)
def g1007d8 (i : Nat) : Nat := 0x1600f8c3c40f843a0083dbef8530050000009feaa89061d14cfea659220141cfea658220141deea652420114cfe5ca99201418feaa89060574c7ea667720114c3f9dd96a2124c7e9dc9061121e7a88a7720114f69846449de22
def g1007l8 : Packing := (11,4,5,0,0,6,0,g1007d8)
def g1007d9 (i : Nat) : Nat := 0xe3e1c912273f0f45064e59a8034810e0b88784227c02e30e2041c01600f0f6097465e49b8f81c47c397923e2e0d01f109f0281388584f8140a254d93a04c2c763b108ec778f92c2de23b6baf4be2110884be212fa8d46792f8ec8a3b108844206ce58a50ee5212803ff532402837ee995d222bfb4cae908d7fa65419def7d32a0a497ee9945e22dfd4c900a0dfea64805077f51040283dbe7750524efd3b9008a4ff66174486f7b2e90c895fd94486779fec9510ba4ff64a885c67fb2544283bf992201419fec8d10ba6fe60880507f6ae508c89bf97220141fdab8a829277d50a77847bda83114effb92420114ede90cef224ff261744867f930b92833fc985c524bfc48304a0cfea6480507b6cef224239fa7720114ed7224ef114bf65a884927bb27442e53f89061121
def g1007l9 : Packing := (38,3,5,0,0,9,0,g1007d9)
def g1007d10 (i : Nat) : Nat := 0x891b00f02a1600e12780b131e2c04c98f00fa24c45b050265c780b51267cb865e0926898cb606250d9d3509380b9b260c4c0b171a4d580b31326c9826b02e549815d12e2c04e811516c124a97324c1358173c6c0a58173e5c32e4972e4c12d8971eb89ab031366c9826b02e7c3a304b526cf8744b925e5b83ddf56cd714bb2cba726d8fa1679dbf65d76539263f8d62b87f15c28003ffa2141ffd82507ff5d121ffd72507ff5c524bfe885d2ffa2172bfe885c6ffa2141bfd87486ff61121fbd72913ef5c644dfd429df7f50677fbd414937f49d71dfd219dfef48644ff8805076f9de44df6778477b88a77fb611912fe20141
def g1007l10 : Packing := (25,2,5,0,0,10,0,g1007d10)
def g1007d11 (i : Nat) : Nat := 0x9264e035034f0d101649a2b4e1a98103ce74d01281a48ebaa044d2c50d306259f66c20560bc03feb97fd41ffa49ff486ff3bfbe44
def g1007l11 : Packing := (6,1,5,0,0,8,0,g1007d11)
def g1007d12 (i : Nat) : Nat := 0x720d6110208ff
def g1007l12 : Packing := (1,0,5,0,0,0,0,g1007d12)
def g1007samples : Array (Bits × Bits) := #[(0x1f0ef83e1df7c3f1c03be00e000fbe07838077c1f0e01fc001c01c0002cd41ba1e0e1fd191fff89bffe3fff31ba9aa6d9dfff93ffc0e01c3bbffce60007ff87fc003fff3cfafffffffff03ffc0b9bce1ece7bd798dd6cdefb1c3c999adc60e18,0x1f8ebd2f9df5ebf5e9baf1af0c6fbed7ebd375f17af0dff38df6de18dacc453a565a93f590bde8b9fbe1fbd29b9da14dfdfefb3fb45fb5f33afddfea5cffc9ff4a64e8ce7009a79ef9bd35db65b9bce3ece7bd799dd6cdefb3c7dbb9adeede39),(0x1fff003fe1f80381f83c01ffc1f03f0783f07801fffffe03c1f8ff83fc4e463a6670e0d0062000a4c005c003e3c8338fe0e00270007e37c43ffff062006001fffffd0030f0900000003f000fff21308600843061f0070f86270cc981ff26487f,0x504000280b00280681800a300200600809010001220460180504600484c453a565a9040002400a8c841c8428280210df4e213308052104028a192a2046041b30a60e04e000821969931051a6521308200843061100409862304810109244831),(0xe00fffc01e0003fe003ffe0ffe0fc007fc007ffe00fc1ffc01ff1ffc1c9078038780ff1e67c000c7000600031c0e3cf1810003bfff8fc607c3001e7c007ffe7ff00100c3c12000000fc003ffc00000f88f01c181c118f00839f30e1e31c78f9c,0x209400400011600002204440280032c0020520054085400aa0888108018008080251ee7c82347108e1005280e84e0010020043984c69d8304245c0912964cb0081f101002ca2022c65a658a0000508f01c180c100a00800a20e143083850c),(0xfff000001ffffc00003ffff0000ffff800007fffff001ffffe001fffe31f803c07ff03e0780000f80007fffc1ff03f01fe0003c0000ff807fc001f80007fff8000000c03042000fc000003f000c03f01300601fe0e1f01f03e03f01fc1f80fe0,0x6bb080201b5e6c00022f553010855b5800045ea5ab0112aaf400137383170058021302e1180040b84100c3e017f17b17fe6443d1001b39627c089ba2126d61810033e0c46ff1051cd119259245c02a01300600540e1f01f03e01f00bc1780ae0),(0x0,0x0),(0x1fffffffffc00000000fffffffff800000001fffffffe00003e0003ff80003ff800000fffff800001fffc001fffffc00000ffff800001fffff8000000002330c02403f03f000fc000001c001c007fe000fe001ffc003ffe001fff000,0xc6089a4888000000009ac95c951000000001d330934800002800008000003f5908080b943c04080199d8040ad20f000100fb5f31a111fea5c218086004048c07001870c708d34d141000001c00728000980014d0003dba001eed000),(0xffffffffe000000000000000000fffffffffffffffffe0000000000003ffffc0000003ffffffff00000000001ffffffe00000000000fffffffffe000000000000000c030088fc000003f000000fe0001fff800000ffffe000003fffffe000000,0xb2dbd5b52004000004020000210e71e6726e6f39cc9b80001000002103930840000103b7bac1f111020001001d7fdef20b0880c2208defbfd75e2d4c6006020810831d807ff1c60860ce38e182d40001fa5000000ffbf60000037efef6000000),(0xfffffffffffffffffffffffffff0000000000000000000000000000003fffffffffffc0000000000000000001ffffffffffffffffff000000000000000000000000003c003000003ffc0000000fffffe000000000ffffffffffc000000000000,0xdcede639d38f3249373799c9b9c00000000804010002000020000042017fe7f77f7fd80008310400a011a20ac6607b1f52df07fbc270080064600000804801100303a02f8ffc30d38d30810a34ffffae00000000067f5eb2ff5c000000000000),(0x3ffffffffffffffffffffffffffffffe0000000000000000000000000000000000000000002fc000c0ffffc0000000000fffffffffffffff00000000000000000000000,0x68f7a7fdecfc08453e0646bc1f3c0fe00000080090042c0360000000800011001004602c00023b800e38e30e20c20c382bd5fe05a8d7abf00000000000000000000000)]
def g1007columns : IndexTree ColumnInfo := (.fork 12 (.fork 6 (.fork 3 (.leaf [(0,1,494,0,11),(8,0,999,0,11),(64,0,943,0,11)]) (.leaf [(128,0,879,0,11),(2,0,1005,0,10),(4,0,1003,0,10)])) (.fork 3 (.leaf [(32,0,975,0,10),(256,0,751,0,10),(12,0,995,0,9)]) (.leaf [(66,0,941,0,9),(132,0,875,0,9),(160,0,847,0,9)]))) (.fork 6 (.fork 3 (.leaf [(264,0,743,0,9),(320,0,687,0,9),(0,4,865,138,8)]) (.leaf [(0,256,647,104,8),(140,0,867,0,8),(328,0,679,0,8)])) (.fork 3 (.leaf [(1,0,460,34,7),(2,4,865,136,7),(8,4,865,130,7)]) (.leaf [(8,256,647,96,7),(32,256,647,72,7),(128,4,865,10,7)]))))
def g1007autos : Array (List Nat) := #[[],[118,130,81]]
def g1007levels : Nat → Packing
  | 7 => g1007l7
  | 8 => g1007l8
  | 9 => g1007l9
  | 10 => g1007l10
  | 11 => g1007l11
  | 12 => g1007l12
  | _ => emptyPacking
def g1007index : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 1 5 3 5 0 1 (keyg1007l8)
  | 9 => lookupWord 8 41 6 9 4 1 (keyg1007l9)
  | 10 => lookupWord 26 122 7 11 6 1 (keyg1007l10)
  | 11 => lookupWord 17 81 7 10 5 1 (keyg1007l11)
  | 12 => lookupWord 5 29 5 8 3 1 (keyg1007l12)
  | _ => fun _ => none
def g1007 : Forest := ⟨1007,12,fun j => g1007samples[j]?.getD (0,0),g1007columns,g1007autos,g1007levels,g1007index⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geomg1007 : graphValid g1007 (boundsBefore knownPrev_g1007) = true := by
  unfold graphValid
  refine Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨by decide +kernel, by decide +kernel⟩, ?_⟩, by decide +kernel⟩
  apply listPieces_all (d:=4)
  simp only [listPieces,IndexTree.values,List.length_append,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceDiv,List.take,List.drop]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg1007_7_0 : block g1007 7 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg1007_7 : block g1007 7 0 1=true := sg1007_7_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg1007_8_0 : block g1007 8 0 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg1007_8_6 : block g1007 8 6 5=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg1007_8 : block g1007 8 0 11=true := (@block_merge g1007 8 0 6 5 sg1007_8_0 sg1007_8_6)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg1007_9_0 : block g1007 9 0 7=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg1007_9_7 : block g1007 9 7 30=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg1007_9_37 : block g1007 9 37 1=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg1007_9 : block g1007 9 0 38=true := (@block_merge g1007 9 0 37 1 (@block_merge g1007 9 0 7 30 sg1007_9_0 sg1007_9_7) sg1007_9_37)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg1007_10_0 : block g1007 10 0 5=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg1007_10_5 : block g1007 10 5 15=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg1007_10_20 : block g1007 10 20 5=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg1007_10 : block g1007 10 0 25=true := (@block_merge g1007 10 0 20 5 (@block_merge g1007 10 0 5 15 sg1007_10_0 sg1007_10_5) sg1007_10_20)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg1007_11_0 : block g1007 11 0 2=true := by
  apply cellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg1007_11_2 : block g1007 11 2 4=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg1007_11 : block g1007 11 0 6=true := (@block_merge g1007 11 0 2 4 sg1007_11_0 sg1007_11_2)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg1007_12_0 : block g1007 12 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg1007_12 : block g1007 12 0 1=true := sg1007_12_0
theorem tablesg1007 : checkedTables g1007 12 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g1007 0 0 0 = true)
  · exact (rfl : block g1007 1 0 0 = true)
  · exact (rfl : block g1007 2 0 0 = true)
  · exact (rfl : block g1007 3 0 0 = true)
  · exact (rfl : block g1007 4 0 0 = true)
  · exact (rfl : block g1007 5 0 0 = true)
  · exact (rfl : block g1007 6 0 0 = true)
  · exact allg1007_7
  · exact allg1007_8
  · exact allg1007_9
  · exact allg1007_10
  · exact allg1007_11
  · exact allg1007_12
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low1007 : Lower (vars 1007) (graphGoal 1007) 13 :=
  lower_forest (g:=g1007) (i:=0) (hints:=13438558465) (before_sound known991 valid991) geomg1007 tablesg1007 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps1007 : List (Nat × List Nat) := [(1007,[])]
def known1007 := extendKnown known991 13 maps1007
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid1007 : Known known1007 := extendKnown_ok valid991 low1007 (by decide +kernel)
def g1015 : Forest := ⟨1015,11,fun _ => (0,0),(.leaf []),#[],fun _ => emptyPacking,fun _ _ => none⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low1015 : Lower (vars 1015) (graphGoal 1015) 12 :=
  lower_discard (g:=g1015) (ci:=(16,0,999,0,11)) (hints:=22028484865) (before_sound known1007 valid1007) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps1015 : List (Nat × List Nat) := [(1015,[])]
def known1015 := extendKnown known1007 12 maps1015
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid1015 : Known known1015 := extendKnown_ok valid1007 low1015 (by decide +kernel)
abbrev knownPrev_flip0 := known1015
def keyflip0l9 (i : Nat) : Nat := 0x34ca400000000
def keyflip0l10 (i : Nat) : Nat := 0x14b33a2d000000000000000000da259e00054eebf000000565b0705c0003e36d975e0000005705648b188ca98502cc5fe2d71faea43000d4f000000852000000000a2b00052a00000000038d000e5b0002cf00000083000000000096f1310000000000003ad000c09000747da50000000002b313c0000005320000004290000000000000000000003462e40000006b00820009030000004161860000004e800000065f00043f0000004d84d305300000000000000000000025d74532004a000000111000000000000fe500000021200000000091500000000072c0000000040006a3000000000000000000000c010002cbec149d29b0000000007ea0a6948f6a40f1a400086183ee60eeca36d0e70a00093dc55000000d9c000000000705000ada00000000000000072e000f4266c926119000000000000000449000000000000000238362a44000437228d27100000000000aa10000001be000000000000000000000b34000d170000000000009ac03900053b00000000016b00000000000000000000000000000000096346d0c26d6c080000000cc000000000b3a000000000c4db0b000000c670000001d7000640413000000000b66000000000000b2f000b6e854b1f51a000550a69668710551000000335000008040201000040000000040000008000803008000200010000600018040400000000001010000000000040001000040402000000000000000200000000000000000000000040000000000202
def keyflip0l11 (i : Nat) : Nat := (if i<2 then (if i<1 then 0x3033615603f861b2c4780005b54000000079ee000061ff85ef148cb146060000748e000000000007de20001e383a668000610e000000000008128000000000000001826c00051c6808d860711e0000b14997ce30e8000000000000000000f1a4000023ca58351069763aee0000000000000000000a99200026c4b811000000000004581fb3a0000000457d000000001130000000154f4000000060c890968fb0000d950000382470c39158d62d8258000000000016c10000c33c0000000085f000000000002820000061138996080d2980001e43fdff0000d0480000000000176900006de6000000000000000c3c060680000000000000024b800009387f1c18a3800051222515ecb8000940200000148000000000000000000524800005118919000000000000000f07c0002215800000000000000000043ae0000cd6e0d5000000004468000d2d40000000640911311580edc80000000d217e5980008b400000000000000000000000000000000000000219b10e8448c00000f8b209c5b800000000001358400060a0b463c0ff03e0982000000000000000000000000000000216200000000000000000000000000737600000000000ba80000000061e1000187e00000000000000002368000936b45400000000000000800000002004000000000000300000000c0000000601400000000000000000080000000000400000000008014008070000080000000000c00801000000000030120000100000200400004000010000000020140080100000c0000600600003000000000008000000040000000a0040000100000400002000000000010040180180100000000000002000000030040000280400a01c00000002004008000000000000000000000000000000020020000000000000800000802000004000070000000200000000000800006000010010000100080000000000000000020000000020040080000600800001000000000000000000000200200000000000000010000000040000100200c0080100000000803000000000000000080000000000c0000200000000002000000000020040000000200001400800002000000000000000000200000000001008004000000000000000000000004000000000000010060040080000200000800000000000010060000000100200000001000000000020000000000000000401000000000000000000000000000000c00002000004000010000040000000200000000000000000010000000000100000000000000000010000000000000000a00400000002000000000000000080000200001000002000008000040000000000000000800000000000000020000000000200000000000000010000000080000200000800801000000000000080080000000000800000 else 0x529c69000100dc000014eb378000000049a3211c000000000000000000000000000000000000000000001170e0c880000000000000000000000000242a222f000154a1e4a7935000078780000000000000000000000000048868c3789692bb434000014630042062440b00000001561000000000001b230000000000000000000613330d6d0440000000e92e000348c0000000000000000000000168600000000d0ae0001adfc9c2a459e39c000713f8360d2e000000001aa00003eaf8000939ad30b45b80000bf243f809b8000fb660003a4c000052bc00000000000000165040003804711600004f9800000000000000000000000001c936934d3fc00000000000004a00000126593b0d000000000000000015140005e2800000001af680000000214a496800000000001a4e00000000000000044c0c87600000000000000000026fc2959000000000000000305f813c0000000601e00030308000814d667447b00004244000000061df0001e1e00006ddd514a021000000000000a8180000000000116200000000000000016448000000000000003cbda2c5517df0000000000000044d0000f196a62f02ebe2ed191a208f12e0b65b0c85f4e623915000000000000000000000020050000e09b05dbcfa0000e2aec8aa018800000002850013750ddc2802b40005c2962d1879841a12270000000000078fd00000000000000020bd87e800000000000854c000000051452040000342700000001e0b0000ab80000000075e500000001708a44a000000000000000e43200000000000000000000000000000000000000000000000000000d8d627a0000000000000004703edb19af000000000000000000000004f600000000c545ccd258f000000010f404b9b1e4000000000000000000000072384a7c08c80000000a34e0001e58000010ec00010638000f092000000009800000e1000004cbee34a0001a1211cfa0f318c8000000062de00000000000000134fc0005d9499b600032ef80000000000287e45f1fc5a45cc0000000b91000018aa8000d42720e1aae5997432c000000079c45965589000000000000000000000000000000000000008326000000000000000c47dc0f00000000013270d440b6420000000000009a16e8a0d10000073c8d6780000000000154982fba98d00000000c3eea35b0c790e80004987000000000003604201ca6e6b0b88d9d28d65916f4c092000044500000000000000000000000ebb600000000000c21e92b40001890c31e00000000000000000000000000cad0000286c0085826ca3140000000d39600038768000a1b516e000070df000000006800000d3a6c50e2ac555ed1b6174782c0000719f21c400000000000000000062340000000000000002365e170000000000000000000094963380000000347e00) else (if i<3 then 0x8600008ca0000834000000000814000000020b8e001000177f40000000410c00000000000000143a0000420c42706638000000002340000000000051880001114b9f5c3a200000000000120e00000000000000000000000000d457d24000048f1000000038a90000000162840000000fb6400000000000d29e0002b01511b000164b2a2db88a20d4329000071e3e9e8000000000000000000000000fb000000000000000000000000000000000000000000000000000000000000600000000000000000021440000000cc68a8c189d29d00000000184c9462102e63710c56413836cb21000069bf000000000000000000000000001239000000000000000cbc1c0a2ce5000000000001accfdc7bb2be1dc0000000396c0003b1c80000000e2cc0000000000000020fbc200124f0513c9580afc1d435e94ccfcf131a925ddcbdece2f0769598ab180004ab378e80000000ec060000000285331a67234000000018de0000000000000012612481b89ef92a000020e0000000000000005e070000000000010e400000002c160000000000008ad80000000000329e000000000000000157e8350a6ead1b80000000000000061110000d021e0a522e644a681c0000000000000000db80000000000000000000000000382b0000000000036abf400ac12000000000000000000000002029b58c4a00000000d263d23c0000000000000000007db5e05b7322c90e4860000616a2080000ebd60002ea700004a7246d090ab21d21c3310c0006a0f000020ccc09b9164a54000000000000000e8e889000004c02000000000000000000000000009a4e00000000000000000028e280000000082328531c1000000000000000000031d285c8000000156a681900006b1c00000000000000000028896d4731aef0578c2bcbbe3aa000000000000000000301c8000000086f90eb00000000000287a68e30000000000000005837e690e0ff1300000000310291580000c585c3d8000000022a4000000000000000000193e000007bc00000008004000366f8000d253f5d0000000000000002a871d9802e580f0430000000014778000000092a917c86d3298890e60000000000082720003060800000000000000000000000001d1f6827000000000006df50000000000000000001941400000000001743c0000000000107c38760000000000000000000803be0eaa8929060000e19400001ed4477a74b8d719b1000000010ec8000000180700440000000000000000000000000008ca800000000000000000000000001a3ee4fa000043740000000000000006848000903707e400000004b618870000000052800000000000000000000000000072c1d5f225a0000a324000000000000000000010900000001c7278fd98e6000168102a48000b060827750561c8fb68c13a6 else 0x12838000000059320000079800000000000000000000000003ee300000000000000014ff00008630000000000011328000320d31dd1318000412f00000002478000000000000ef52513000165a400af16c733f43a400039fd330600000000000000000000000000000083940005c820001845c09dea360000000000000005be800000000000d239e79c00000003a2f65ac000245e43b40003af18000d27875fc00014aa00000000000000000000002c898000297f807c0006e130001a5e3ceee0a3a18cd01c0000000e1d7c7ff08800000000000000000000000000000000000000c794cb6c14a83e38662833800000000000cb1a84569d6000000000001ab7c1080000000e87a000181b315cd47a00000000000c8e2a86d50588badc6a0002d0180000000000109779f230d20000000145c4a4a00026db8000000000000000000000051776e810de000075b6ef080000001873000000000000000102388f9000000000000000000000000000000000000000000000000000000000000000000000001c06e1de00034018000000000026d580000000000000071796a2c000000071d488e7359c0000000000114300002089000000000000000000000000001420f93a0000000107ee083238822d462212840000881000070f5c16ec2aecced8180001c49800000000000000192a000000000000000000161b666a3e05207a0000a37256cc343b79043a81ce00000001d198000a3b80000000000000000001ec91610000000000004125601a000350880000000825c28088cc9902b47a05380000000000342c80000000000144f800000000000000350800000001e65ddfa1367485d4ba00000000c2300000000000036f8cbfd881000000020150000000000006608000437a10a10ec000088d54594000782e5956000000008227296000080cf89500000000000000000000000ced8000000000000000000000000024ad2a1f9c43526c08ea823938e000000000000000000000000007370b3dc0000000000000000000000b2f4776750d6dde000000000006050602456ea85e00000000000000059a2000000018b300000000000146b5209ac7d001400048f5000000000000000000000028688000000001c96c60000f3c5418a2e124ef000000020c80000000042b80004035f095327d4d3402bc29a000000078b5c2ea000000000000001288800000000001a8580000000c))
def keyflip0l12 (i : Nat) : Nat := (if i<1 then 0x1e01a9f40cb00000000000a034def8be14fb61b40d00000000000000172e80000000000000756ff22800140780000000000000000000000014af80000000000e43d81400000000000001fc4800036a000000900014130000000457e00000007c280000000001a30ed061c1b2a0841f138000504527152466a4dd74e95da29a73ed5292b960f083000000000000000001e18800128709e7f1f4c960005ce717c4c5c000000154f746078b0000a0b800000000004820000a193c590a9000000000000000000000491c2770000000222400000000000000e6ff9300000412000000000000009ab800102e39ae0000000000000000000fc00000000002eca0000001a160000000000000058417954cac00012380000000000329a2768000000000000059b5229000000000004bab319264a41600000000001946000169800000f52c6800000005b80000000000717600028760006aaa00000000000000000182ce2f5a76abfc65d044f0b000054cb8b8b4fc000000069f00000002a0fa5380000000000000000039268c0e32d2e14570000000000129780000000001fb3800000000000000001888000000000000006687a7fe8cc000000000011ea000000000000000000001a8e80018940001b7c8000000000118080000000000000000000021f200061a800000000000000000000000000000000001f5a00010760000000000000010d400000000000001ec16f2e0000000d500001e3c000000000000000000000000000000000000001acc0ad6000152f29b96da6b700000007ad1a4a800000012b20000000000133b5d0fec46a088800003816000108b20c0000000000000000000000000ecf0000000003000000000020000200000700000000000008000000010000000000000200000801000000000000020140080000800000800000004010000000000000100400c0180900601c000000020040080000000001002000014008000000000000000200c010000040000000300000402002002000020010060040000000400000001000000030050000000080300000000803006000000000000000000a00000000004002000000000000040280300000000000002018000010000000000600000400800000000010010000080000000200002809004000000050000080000100a0040100000a000000000000100000000200001001002004008000140000000100000400000000000008000000040200000201000001006000000000020000000000000000000000004000030060000000200000000001000010000000000100080000000000001002000000030040000000201c0040080100000c00000002000000000000040000300200000000000000008010000000000000000000800002008018000000000000200a00800000 else (if i<2 then 0x1a7934c8fc98f25a238001450800000000015bbe29051e0000944d2c0793bdba4ccc1ed0ac0000000000000000000000000a4ccd7385a0000000000141780000000001dcdc1e800071f8000000000000000000ccc000425400000016788000000000000000000000000ccf8000000797206f79b60007a220007520e216ca1c6221fda2b6525a720000000000000006c12524f0c4c4faf1d9300000000000000197d013800000000000001ce40000000a34800000000000000a48000000000002040003262815b099b06c870c460000000000060848920002a8707d940e000688600000000000000000000000000010b1e58d00224de0004827b2129f00003a5d64fb5840000001d3a00000000000c32109dbb200000000001c048000000000000000004428000000000000045aa00000000000000e6180000003ab60000001c800000f2700000000001a1a7928e87ae3f27300000000d3a0000001884e0460000001381800000000000007e8ed88f85c810986a0000001a2a5499893000000071e06b20240857fcc1abf457000000000000000c70912200000000006958000000000000000000000000000000000012b2800000000018b900000000000000000000000002bcda66000589600000000000000000023da128000000000000000000004324000100f294db3926b1902934a93569b706fc3e1d631152ce200000002c1e59696c0000f078000e850000c8c8000000000000000016aa250e00059369aa00000000000000000000040780001a1000071b800035f7b662ea40000001e4100000bd800146c0000ea60000000516444bd8fa704620686ee98c3178000000000024ed472f2c0000000000000000000000000cc80000000000000060b40000000000000000060d8033e4aad2d800089d000000000000000000000014c00010b7e682ae9828f02b84782ba735800000051d751180000001ac2000000000000000000000c55903c0000000000000000000017ce00000000000000000142ed30d789015000000000000000000000098301a60c59b40000001a000000037b532f8af000140c8a8800000be00000000000001865ea3600000000002c0c0003a5a0221638d4d800000018f6000617000018c4c0a4984a14407a4a300000000000000000000043002a88000000615ada50000b7fe87385b991b8bb1daef5792d4594f216aa5e24afa31a1bcc0a1a2353159c0000001419800109e00000007e60000000000028ea0000000099000000000000000000000647e0000000000000000000000006dfa000000056780000006a3e00000000000000000232b1368000000000000049600000001e0e8000289922a000017bf2a0000f6f80005c88000000000000000000000000000117e00000016a280018498001254bcd9a9a66900003090000 else 0x3f460000000000000055f0000b24d18000030493a74875571df0442562d869accc6890d80a4a7c8e199a8001c0d00000004175ea380000000000f2f72cf3ca00fe00018ec0002801723714a2370000663c68b4c400002c2000000065e4d2c8000000744929f80012d1000000000000000000855000000049900000000000000000061d000000000000108a27cd0800000018860001972e415420a860696000002ae0b323780008ab000000000000000000000000000000000002a80000000000000000000000000703e56c956515a800025e385427024cee75461c7168000a28071d2d08000cc38000c9c455603900000000000c0700000005d760000000000000000010f36510000000000040e7d8a00000016016022d117af4120c85a71580012268001614c10c000000000048c60005dde00000000000810000000000074b487ec9401060000a65000044f00000003d17b8800000000000000000168d00000000000000287e69c8000000000000058a7e8bcab809e800140d80000000000000424e0000000000000000000000003a2c000000000000000000000000000147b83220002d9a52f869a0be80000000000000000000000008404910000231e0005e37e697a02000549e0004d2c0000000000000099f80000007534000000141f000000000000007e2e000000000072e600000000000000000000057e22d20000000ead40ee000000000073360000ac4458b16c00000012cd555800000000000000000000000050ae00000001a04a31352220bf5ea71fe9872a60005c020003ea600000000000000000000000076ec0000000000753000000003868000000000000000016b3000000018186abfa85b8154d0c59dadfc2379d206280000000001a450000000000000000000000000000000000000001ab0000ac50000e60800000000000000000291000))
def keyflip0l13 (i : Nat) : Nat := 0x7d11ca80000000000000000010579d00000000000000000000000048e50380000000008d82400000022db22da58000000000001088000000000000003604d4a2a0000004048e5220d824978031dd6c280000069290d2ac00000000058a80009e8000000000001d700000000042c80000000058bd5c0000000003490000000000000006e588062f00000000000000045600000059636b80079200024f542000558c940000003ae000004000000015c02fa700000078080000000000000000000000000049500000000000069040eeae8000000000000000000000000000000003974818006624068001cb80035844480000079c80000000010122680000019b48c8000000c530f8004d9c54000000248e1980000061a80000000032b9a78000000000000000000000110007236919704419a389e0e8bafba882a98a00000061f069e996528000000003a600015b0000002dbb94ba87ddb4b00052500000006420780061300000000000021800000000000000060980000000000000000000014c0004a18004cce138072890003c3788620000498e550000007c40001a98000001e7ba900051a04380000000000070b653e8f6e169c48658c2a4db080000000035780000000000000000000000055fa968000005ea8000000000000001ab0001d900071bf9ddd0cad505818060400014000104000000300010040000004000000000000b010000003000040000000000000000000200038080008000000201000000000008000200000000400000000007008000005008000001
def keyflip0l14 (i : Nat) : Nat := 0x1d000000018b67600000000dbc2c2bf0614300000d200000000000000ee0000000000006593160000227ec00046e800000000001957398c0000000019a9c000180000002040040
def flip0d8 (i : Nat) : Nat := 0x44908051db62006cd814558249715f38d00174a9a50c0e1ee712002e98265531
def flip0l8 : Packing := (3,6,6,0,0,3,0,flip0d8)
def flip0d9 (i : Nat) : Nat := (if i<1 then 0x804020109584020108d84216fb081142010080402010083ac20100836c20100804020100832d96bb55840209b45a2c20100804020100804020100804020100804020103295420100804020100804020452284020100811420451a8404a100a8402010080402010080402010080402000c7fabb800a960525db7a006e2aa4d585cf7a006d6aa66115c7fa006d5a1a6582df6a006caaa54d25c7fa006c6aa66132c7fa006c6aa64d85c7fa006c6aa64d25c7fa006c6aa64985e5fa00699a7a6525e6fa0068da6a6581e6fa00689a6a6581e5fa00685a7a6525fb6a0060d1560925ef7200545a1a6525ef5a004d5a3a6525c7fa002e982a6551c7fa002e98265531cbfa002e9534a181c7fa002e92564d818ff9cb60aaa4d6008ff9cb4caaa606008ff9cb44da2616009df9c7aeda254600bd79c7aa95349600bd79c7aa951496008ff9c6aeda3496009f79c5aeda3456008ff9c3aeda2616008ff9c3aeda1616008ff9c2aeda54c6008ff9c2aeda3616008ff9c2aeda3606008ff9c2aeda161600bf69c14d58249600cbf9b8606aa4d600d5f9b7800a960931cdf9b758eaa49600cdf9b744eaa49600cef9b654aaa60600cef9b64caaa60600d7b9b4800a960951d7b9b4800a960931c7f9b3801a1a6582c7f9b3801a1a6525c7f9b3800a960525df71b36055149600c7f9b2801a5a6581c7f9b2801a5a6531c7f9b2801a1a6535ebe9a35492860600fb69814d582496008ff8cb60aaa4d6008ff8cb606aa4d6008ff8cb54eaa606008ff8cb54aaa606008ff8cb546aa60a008ff8cb545a84ca008ff8cb4c6aa60a008ff8cb44da261600bb4ecc4d5524a138db66bb6051560925dbc6bb4c51860932eb66aa6051560925eb4eaa4d5524a138f36699495514a181f9d2889de118ce00fb52888ce0095611fb4a558ce00a2222fb46554c51860932fb463384655a2222fb46336051560925e73611955a424128fb620084655a2222fb62006051560925fb4a004d5524a13889fdc7aeda54ca8889fdc7aeda5486888dddc7aeda5486338df9c7aeda5486008df9c7aeda3496008dddc7aeda2616338df9c7aeda26160099ddc7aed52a223399f5c7aed52a221199f9c7aed52a22009dd9c7aed258ce008cfdc6aeda84c6778e7dc6aeda84c6558e7dc6aeda8486559cddc6aed819de339cf9c6aed819de009e5dc6aed81956339e79c6aed81956008afdc62e9534a1819addc62e9534a13887bdc42e98265531ab9dc42e9534a13887bdc42c1a2a65359f1dc42c18295633c1fdb7a20a0a6525c5ddb78cca0a6525c4fdb69dca0a6581c67db6954a0a6581c3bdb4a20a0a6535c3bdb4a20a0a6531c5bdb49dca0a6531c73db4954a0a6531db65b36051560925eb4cca4d5524a138bb4cca4d5524a138f364c9495514a181db64ba6051560925eb64a06051560925 else 0x1c2021843d0c3b08373429242f383b34330c3708218c2f07874cd1e4e0fc0084908120dc1081e08420102284020100804020100804020100)
def flip0l9 : Packing := (114,5,6,0,0,9,0,flip0d9)
def flip0d10 (i : Nat) : Nat := (if i<3 then (if i<1 then 0x6909060b3dec8b4848305cfb645524a138fbe3073bc23007b798360a55803db6c1a2ac124bfd660a558ce00feab0519c232aff7182802119571fec13474cb03fda6093295600fe9b04992632afdd9819de33803facc0cab19c01aef605a424182feab02a8a4b19ff718154525803bbac0aa24824bedb6053560925fbe30298cef007f71814c655803df8b9d1108c01ef65c6888ce00feb2c52ac67007bf153a2211803dbaa9aa544423ede54d52a2200f7b2a544467007bd552a22118cfdf8a951108c019df549a1a6535f79aa49430319fbe9524a181803deca8d1119c01ef35463388a88f7d2a3004454476f55169a996073dea8b4848305bdd545a1a6525feb2a292c670067f551282996075de9c348482519df4d5a8a6525cefa6ad2920946f5d3568e99497fb49ab0492c01edd4ca8895611f6f265444ab007bf132a2211803fb89940108cabed74c931a2255f7b26498d11007f59324c655803cfc98d113bc01ede4c68895600f6da632ad11117be93180222a23b7a98b4d4cb03edd4c521a2255f7e26290d11007f713148655803dec9430319c01edd4a13895611f7b2509c26b00677d25694904c7dae90d112ac67ede4868895600f7b24344467007f5921956338023fe5d3054caa31ff2e982a65358ff974c132a98cfdcba609518ce7fc5d304a8c013df2e9824c6559ff174c12630047fcba606994d63fe5d2a74cb032ff2e9534a181d7b974a9a509c5bdcba54d284e23fe5d2a54cb032ff2e9524c6888ff974a8d32c147fcba545984ca3fe5d2a248305bdb2e93560925bed9749ab0492c7fcba4c69960a7fc5d26292c011ff2e931241828ff9749892092c7fcba49593606fb65d22ac124b1ff2e91364985e7d972a9250c0f774b9495156073fc58554483055fe2c2aa24182cff16155120c0d7f8b0aa8906063fe58350caa431ff2c1a864d218ff960d2b2690c7fcb068e9960a3fe583474cb031ff2c1a2a65818ff960d15329ac7fcb06869960a3fe583434ca6b1ff2c1a1a6525beb960c14ab19df74b060a11956eee583033bc677d72c18195633b7e960a9d1108dbdcb054a888cedfa582a5444236f72c151a2233b7d960a8c454459fcb04c6889dedbe58263444ab6fb2c13188a88b7b9609430319c7fcb02a5814975f6502a494303bdb2813560925ded9408ab0492f9da889de33803ceb444ef08c67e7ca227784600f6b5112ac67007b56888ce55847de94442319c01edca220095611fba4ef08c67007b4e558ce8888bdb52ac01444459cf955a424128f7946700445447f523380211957db308cab4444517f6deaa655218bfb6f5532692c5fdb7aa9926164fedbd54a95113776deaa496339bf36f5524b0045fdb72829949667edb554c0cef39f6daaa606558f7b68505329ae79da48cc9060bdb2c0a2ac124bed34d5524a138 else (if i<2 then 0xa39f78cca066121cfbc665032a90f6ee2269a996073f7111414cb039fd844a0a6535edf400d3532c0e7fa0068e9960b3fd003474cb039fe801a2a6581cff400d15329ae7fa006869960b3fd003434ca6b9fe801a1a6525feb40092a709afbea00461824cbfb50022ac124b9fe800a9605258ffb74c15329ac7fdba608905463fedd304482631ff6e932a65818ffb7499120a8c7fdba48c906063fedd226c930badf6e2aa4d585b6fb715526ac2cfddb8695218ce7fcdc34a90c013df6e1a3486559ff370d1a43005f79b84ca55802fbadc26508cab4ff6e131a6582bbf37098cef005f79b84c655802faedc2432ac677de6e12195600bfb37090c67004dfdb7aa992546cfedbd54a95117776deaa49633bbf36f5524b005d7db7a6553496ebedbd32a8a4b57f6de9924125b7f36e98d110055fdb72a5824c63fedb554c9a4b73f6daaa60677bcfb6d553032acff9b6aa9358027eedb55492c673fe6daaa496008ffb6d5512092cff9b668d25802fbcdb2652ac017f66d9258ce008ffb6c505329ac7fdb6282994963fedb140c9a4b3df6d6aa661159efb6b553268af775b5a65156065fedab4690d113fe6d5a3486008ffb6ad0d32c147fdb56849060adfadaa65444236fe6d532a2200b7f36a98d11005bedb54c622a22deedaa43444676fe6d521a2200bfb36a90c670057bdb42a582546bdeda152c12631ff6ceaa649858ffb6755322c2c7fdb3aa89060a3fed9d5448303df56ce9944d818ffb66d0d32c147fdb3686994963fed9b42483051ff6cda124125bef366a8a4b005b7db348688956dfcd9a43444017de6cd2195600bedb668ab0492c7fdb32a5814963fed99414cb051ff6cca0a65818ffb6650532a8c7fdb3281984863fed9940caa431ff6caaa655318ffb6555326c2c7fdb2aa9936063fed9554c8b0bbdb6caaa54d25bedb65552a692cf7db2aa9319567fcd955498c011ff6caaa241818ffb64d2d32c0c7fdb2696994c63fed934a483031ff6c9a5241318ffb64d0d329ac7fdb2684904d63fed91414cb031ff6c8a0a65518ffb64505329ac7fdb2282994c63fed9140caa631ff6c8a064d858ffb6450326c0c7fdb2281916163fed8d54cc2651ff6c6aa64d858ffb635532692c7fdb1aa9926163fed8d54483051ff6c6aa24125b6fb62a9aa54447fdb12829960a3fed89414ca6b1ff6c4a0a65258ffb62503309947fdb1281936163fed8940c9a4b1ff6c4a064985c7fb50c112098e3fda8606994d77bad426290cab8ff69e8824131cbfb4eb1d3292e5fda744e994973eed34664824b97f699a7a6525cdfb4ca9532c0e6fda64ca996073bed29529426bcef6918124182cf7b4898920c166fda369a996073ded1b4848305bdd68d8154525d7f346943030066fda269a996077bcd126ac2c0197f685a7a6525cf7b42d2120c167bd93 else 0x76c0a633bdf76bb605319569ff5db02483056fdaed53a2211b7f576a9d11005b7ebb54d52a22def5daa6942717deaed5349600b7bd76a8d1119dbfabb54688802fed5daa319c016fbaed5188a88bebd76a8a4b19df7abb54525802bbf5daa24824b6fbaed35a2222bfe5769ac23005f76bb4d585846fbd5da6ac2c017dbaed3560925b3fd7698d113bdb7ebb4c688956dfd5da634440177eaed319de00b7ed7698a43445bdebb4a1818cedfd5da50c0c017dbaed1888a55bf9d768c44519dfeabb46222802df75da30c12657dbaed15609258ffd7654b0292c7febb281984ca3ff5d940caa631ffaeca064d858ffd7650326c0c7febb281926163ff5d940c8b0badfaaa8854525c7fd55441209ae3feaaa20904972ff554ee48303bdbaaa5560932d6fd552aa50c0eb7eaa955284e33bf554aa483039dfaaa5524128cfbd5519920c167deaa8cc906075fd55400942719efaa9a424182cefd54c926ac2ef76aa605514976fb5530298cef8ffaa98124182d7bd54a9a509c6beeaa549286077eb552709ac23bf6aa9384d600dedd549ab0492ebdeaa4c931a235ef55250c0c67afeaa92860600deed5492a6b08ebeeaa461824cb7b75522ac124bbf5aa91560633dfe5548ab030067f6aa454906077f955226c0c01bf9aa91346222e6fd332aa50c0f7e699889156073df4cb48483059fda65a345581e7dd32a9250c0f3f699545286079fb4ca6294303dd7a65254e135eeed3292a2ac0e3fe88696994c71ff4434a482638ffa21a3a6525c7fd10d192092e3fe8868c904571ff443454ca6b8ffa21a224151c7fd10d11209ae3fe88688904c71ff443434ca6b8ffa21a1a6525c7fd10d09209ae3fe8868490497daf442a292c67edea215149600e6fd10a892092e3fe88282994d71ff441414ca638ffa20a0a6515c7fd105032a90e3fe88281934971ff44140c9a438ffa20a064535cbfceed453298e5fe776a0904c7a7f3bb4d4cb0397f9dda3a6581cbfceed1920c0e5fe77282996072ff3b9414ca6397f9dca064d81cefcaad453298e77e556a0904c7b3f2ab4d4cb03dcf955a424128de7caad212094677e5568e996073bf2ab474ca519df955a324181cefcaad192094677e5568a996073bf2ab44483039df955a224131cefcaad0d32c1677e556849060b9bf2ab2294271fd5955814c931e6fcaac0920c17b76554c528607daf2aa50c0c67ede9552860600f6dcaa8c30499677e55282996073bf2a9414ca519df954a066121cefcaa50326c0e77e55281934873bf2a940c9271db78cda6a6581ef3c66d2120c16f9e336909060b3ef19b454cb039f78cda224181cfbc66d1120a8e7de336869960b3ef19b434ca4b9f78cda124182cfbc66d092092f75e3354490497fa719a2ac124b9f78cca960525cfbc6650532c167de33282996073ef199414ca)) else (if i<4 then 0x168133933933933aad20aaa5a9e29e29e29e29e29e29e13613622b133a96a96933933a8f28f133a0aa0a933a0a933a7d933a6c133a0aa0aa5fa58133977133933933933933a2b133a50a50a44133a32a0a933a2b22b133933933933977177223a23a23933933a12133933933933a0a933a031339f69339ea1339d89339339339339d11d11d11339339339339339771771771d11c99a919c93393393393393398d93399519516096098d93618618617e93617716816f96f93393396816095915913393395913393395194a13d93612c12c12c12c12c12c12c12c12c12c13393393393393393393393393393393393393392c12c12c12c1158ff0ff0ed8cf8e10cf8b90a78a789107f86e05c84d84d84d85505505504d84604603e83701b8005ffabb6a115802ffd5db46a8c01fdeaed5349600fef5769ab0b007ff2aa45581803ff955226c0c01bfe801a3a6582dff400d1d32c0effa0068a996077fd003434cb05bfe801a1a6525eff400cc324a8f7fa0064d92547bfd00152c12a3dfe800a960931dff40054a6292f7fa002a525606ffcdd30692c01bfe6e98254600bff374c12a3006ff9ba60931802ffcdd30498c01bfe6e9514ca00dff37498a4b005ff9ba4c5258037fcdd24ac0c01bfe6e91361600dff3715526b007f79b854d25803fbcdc2a292c01bfe6deaa60600dff36d5526b005ff9b6aa925803fbcdb2a692c01bfe6d6aa60600fef36a98a4b007f79b54a1358037fcd9d54c1401bfe6ceaa60600fef366a8a4b006ff9b2aa9818037fcd95549ac01fde6c93561600dff36355305006ff9b1aa935803fbcd8aa692c01fde6c53561600f7f350c1263007f79a854d25803fbcd42a292c01fde6995349600fef346a8a4b007f79a154d25803fbcc1aa292c01bfe60aaa54600dff3055526b006ff982695318037fcc0d549ac01fde6055349600dff2e755303006ff962aa9358037fca9d54c0c01efe54d2860600dff2a555303006ff951aa982803dfca8c0094271bfe545a84ca00dff26555303006ff932aa9518037fc98d54c1401bfe495a360600dff246d0b0b006ff921aa9358037fc90b46c2c01ff6485384d600fef2429ab0b006ff913689858027bf5db50994ab3feaeda84ca009bfd76d42633bcf7ebb6a1319565ff5db4a98d113feaeda54c6008ffd76d2920c0c7febb694904c63ff5db4a482515efaeda4241829f7d76d2120c14feebb68d8588a7fb5db46c2c233feaeda3616009ff576d1b03004f7ebb68d514967ef5db44c2c673fdaeda2616119ff576d130b004fdebb685858ce7f75db42c2c453feaeda1616009fdd76d0a7111577ebb64935616faf5db052ac677deaed8295600bfb576c1467005f76bb60a11956eef5db033bc6777eaed819de00bebd76c0cab19df7abb60655802fed5db0319c017f5aed814c931bbed else (if i<5 then 0xf86670c8b620ac497c5216902b1223884762447c88ec3e36231d85118ac28878e1e9d688b160f1c1b3b4d10c217203a1d9a274743138a1d10e31388173b4816901b0d621585a70ac4d3853487437344e53b82725d813ac19a5d6169ae709d6b344ea87450f03a75a3a60c25b3f8bd346225801d474fe2c622691c5e9a311351d3f8b1849a7f17668c6492c367878d0e841e09cb88c6e0f9fe6d991115c1f1bc5f3acc888ce0f8de2f99674426f23d072ed5884b6178be2397c8f1c6f23c37078fe32cd3791e270b66b97c71b4872ece1e1dc259a3b09c1d470e2789c769ae5e2a5d3b4d1703a769be60c25d343a6f9fc58c24b342e384540928132824504090b8c13243a707c8d3bd0e2c612d9c12903c0e9c2d2c3a186c10a14142436769a6b0f8b73a5e1b9ba08a430b9a170b411702e8e9c3b102e70781d35cf1e8217083c1e8227134117026f49c3b082e184e3989c33464cd3cce1e8221a421107080d081b0c214842108ce109c2a087c00a82928823081c10da167f8167134db3fc0b38967ba3e00ecdf005a7f1be00ecd73fc07389c76a3e00e26e478e8909a7723e00f8fd37c01f1ce6f803128205044908241098254f81e0e1c669711f03c147a4e2efbef46e7edb6ceeceebd6abe9a68de7c66faeb933e68660aebaebe4ce5434d34d2ebaebaebe4cb2f6452a5e38b27afaaf362c624aa5e18610e10aa59c99c9e04203250aa5dfcdf05d75e3dd75e3dd71d15cf9c9933a50dc35b6daa133cbca23933aa5933da2d96203589d7d575d75d6e22b2c8933d52933933933d3c20aa0aa0ad34933933933d1e507933933933cf1133933cda93393393394a14a13393394a13394a14a13393393393393394a13393394a13394a14a13393394a13393394a13394a13393393394a14a13393394a13393394a133933933a9e29e29e29e29e29e13393393393393393393393394a14a13394a4d313393393393393393393394a13393393394a13393393393394a13394a133933933a0a933933933933933933ccb933933933933933ac8ac8933b2f1339339339d11d1133933933933933933933933933cc4133933933933933933933cc4133933933933933933933933933933933933aa5933933933cbccbc933933933933933933933933933933933933ac8933933933933933933933933933933933933933933933cab48fc6f44ec33412bf23d1bc03aeb9837c96816816816816820a968133933b70354b4d33694a133933b2f32f32f32f32f055327b27b20318b18a0ab11309b022faafa84613384620a84614a2f329e29e29e14a159133aebad0133a0aac8ac894a133ac8ac8ac8ac12c118d98daad2ad13398d98da0aa0aab493394a14a13398da9e29e29e29e29e168168168168133933933960a0a96816816816816816829e29e29e29e16816829e else 0x12)))
def flip0l10 : Packing := (575,4,6,0,0,12,0,flip0d10)
def flip0d11 (i : Nat) : Nat := (if i<2 then (if i<1 then 0x6bfeaa54688bf7aa9518ceffaaa54600bdfaa951496ff6aa4d611bfeaa935802f7eaa4d585affaa931a22dfeaa4c677affaa928606bfeaa4a138bfbaa91888a7feaa241829ffaa8906077de994e135cffa65286077f69945581dfda6513607b7e8854525cffa20904d73fe8824131cffa20904973fe8824115d7f9dc906075fe7724131fdb955824cbb7e554a181edf955284e377e5524181ddf954904c777e5524128df78cc9060b7de3324151df78cc90497bfa004a1389ff6a1954867fda864d21bdf6a132956ff9a84ca00b7f6a1319def7da84c655bdf6a121956fdda848633bfe6a121802dfda7a6525aff69d31a236fda6a65819ff69a994d67fda6a65259ff69993496ff9a64d600bdf69932956ff9a64ca00bf7699258ceff9a6496009ff698904d67fda6241259ff69593486bfda54ca88aff69531a22ff9a54c600aff69521a22fdda548633bfe695218037bda424182bef6909060a7fda3a65829ff68e99606f7da354525bfe68d25802bfda348688bdf68d21956ff9a3486009ff68c9060a7fda3241519ff68c904967fda2a65819ff68a994d67fda2a65319ff688906067fda2241519ff688904d67fda2241319ff6869960a7fda1a65359ff686994967fda1241829ff684904d67fda124125ddf649356173fd914a138f7d60e77847df9839de00fde60e55803f5d8295633fde60a55803fd9828ce00fdd60a11957ddd819de33f7e60677803f5d8195633fde60655803f758154525f7d605319dff75814c655cff6049060bbf573a2211efe5ce88803bdd71a2233efe5c688803fd9658ce00fde58e55803f5d6295633fde58a55803fd9628ce00efd54e88847bf953a2200edf54d52a23bdd534a138fde54d25803bdd52a2233efd54a88847bf952a2200efb54928607bdd51a2233efe54688803fd9518ce00efb54622a23f5d5149633fde5452580377d5124125fde4d585803f6d3560925edf4ca88957bf532a2211efe4ca88803f793295600fdd4ca11957bdd324c688fd74c931957fd9324c600e7f4c6889dfb7d31a2255efe4c688803df9319de00fde4c655803bed3188a88efd4c521a23f753148655ef74a1818cfbf92860600ff649633803f5d254e135edf48688957bdd21a2233efe48688803f5d2195633fde48655803fd9218ce00efb461824cbf6d15609259ff2a5825467fca9609319ff2a5814967fca94c5259ff2829960a7fca0a65819ff282995467fca0a65359ff281984ca7fca0661219ff281954c67fca0655219ff281934967fca064d21e77a22778cf9f6889de11e7ea2277803b5e8895633edda2255847b7a8895600ef6a2233803bd68884633efca2211803dda778ce00f759de118cfdf27784600edb9568888bf5a558ce00ef38ce22a23f563384655efa80222a23f72008465597f69e994967bda424182 else 0x1dff6a5136177fda8a6535fdf6a153497f7da854525f7f6a1319dff7da84c655ffe6a131803fdda849633ffe6a1258037fda824125dff69e99607bfda74c688ffe69d318037fda6a6535bff69a99497f7da654d25ff7699258cfff9a649600dff69890496ffda624125dff69699607bfda54c688ffe69531803f7da54c525fdf695284d7fbda424182dff68e9960affda3a6582dff68e99606ffda3a6581fdf68d82957ff9a360a00f7f68d819dff7da360655eff68d52a23bfda354688ffe68d51803f7da354525ffe68d258037fda324182bff68c9060b7fda324125bff68c904977fda2a6581bff68a996077fda2a6535fdf68981957bfda254e88eff68951a23fdda254633ffe68951803f7da24d585eff68931a23f7da24c655ffe68931802ffda224181dff6869960affda1a6582dff686994d6ffda1a6525fdf68582957fdda160a33ffe68582803bfda154e88fdf68553497bfda154a88fdf68535617fdda149633ffe685258037fda124182bff6849060b7fda124125bff684904977fd9864951eff661824c7f7d9854d25fdf661514977fd9824125fdf659534977fd9624125dff64d92547f7d9354525dff64c9060b7fd9324125fdf645534977fd9124182dff64490497ff9874c600dff61c904c7fdd8548633ffe615218037fd8524131fdf60d51497f7d8348655ffe60d218037fd8324125dff60a995477fd82a6535dff609954c7fdd8254633ffe60951803f7d824c655ffe609318037fd8224151dff608904c77fd81a6535fdf60553497f7d814ca55ff7605258cfff98149600dff604904977fd73a6581ffe59532803ff96349600dff58c904977fd62a6535dff54e99607bfd534a181eff54d21a23ff95348600dff54a99607bfd524c688dff548904c77fd51a6582dff545984cbbfd514ca88ffe54532803bfd514a138dff5449060b7fd32a6581dff4ca995477fd3224151dff4c69960bff93149600dff4c49060b7fd3124125dff495936077fd2364585ffe48d818037fd21a6535dff48593617fdd214e135fdf485356177fd1364985dff2a5825477fca960931bff2a5314977fca949581dff281984cb7fca066121bff281964d6ffca065925dff281954c6ffca065531dff28195486ffca064d82bff281935477fca064d25bff281934977fca064d21bff28192606ffca064951bff281924d6ffca064931bff2819160affca064525fdf28182957fdca060a33f7f281819dff7ca060655eff28153a23bfca054a88ffd28131487bfca04a181eff281284e3fdca049633ffd28113607fec9060925fdf24153497f7c90545259ffaa9984ca7feaa655319ffaa9936167feaa64d819ffaa9926167feaa64585bdfaa982956fdeaa60a33bfeaa982802dfeaa60677bdfaa981956fdeaa60633bfeaa981802bfeaa54e88bdfaa95349) else (if i<3 then 0x978da71f89c2a7b47174e370f85c1a7b471866470386dee5d3f1a7e270f854f68e2cdc2e7d139cd1c59b9ec8e0b7f9d4dc61f9edee7537165685799fcdc5b38dc8e0b3e9b8c671b91c467d3716ce370385cc62f2f1d513f46adcd67e2cbc5e17069d91661b91c3e0e3e9acc371789c2a7645966e4713878fa6b2cc0a0f178541c889b1c6ddff768dd47751dc1366dd9b766ddb276b2da6f684d9b765fd97eb04d923631d86b603d7b35c7d71f5d5d71f5b9a9435b9d71f5c7d6e75a2c2bf58bd5f757dd50b52bd3c34d9d32ec0ed26748b710f474d19b42bd051c43d01b3f8cf1b3b8ce86b04ce2b36acd7333ccb73301cbab2eabf872dcca870afc99b24fc93f24fc8bf12fc83f201c7aac0eb03ac0ec6bf198ba3ae8ec57713dc4bf118b72b0f8b72adcac2f6b56c2bf098b1cf098c177046c11b046c09b00fbfe2fb3bf2af9cbecef9cbf86fcaac12f9cbeced33be72f6abd2ac57bc62f01bbcec57bb06eaaba72e8ea9b2a6cb92aa6cb81adefb762dcab6ced9cb616d4ab4ced1cb3aacb8b262c81b1cec65b15ec1cb03ac0eafbaa6ca9b2be0aebaba0ac12b92adeeb64ad5ab12ac12b04abb6ad6aa6ea8daa36a7fa9c6a42a9b2a5ea942a42a762a14a7629fda7629d8a7f6a2ba7629fda7f69d8a8529d8a7629d8a7629fda7629d8a79a9e6a7629931a8a9c1a6aa9931a8a97ca596945a44e8e1a2be87da10a8079f0e7889d367099b3a693996261d97f65c2961e54394464d6926e47291024058f4e3a18d763228b9e2b58a32263890e21a877e1bf861215b84820ee83160a581ce038803dfd47e65f677cb1edf7a6de577871dd87651d597455cda7259c8871e9c5170d5c3570d5c43710dc43710dc4370d5c356fe9bbf6e11b406bf1ac169f5a42681d9c3662195f64498d7627185860757e25e9d7635ca06a25b916a959b962a57995ab559d52c53c54b6523545b50813ee4f1538a4d3d3144b6529e498d22847b51c4466d17b454912043b90bc42f108a416102640990263facfb03e40f433c44ed63a6ce6038dcdfc3704d863508d22339ccbe31e8c483058bdb2ec8b922d80b372cdcaf32ae0a7d292ca10275499a25c493f247c8e422c8880213881c1fcc7c11e607661cd06f91bac6a21ac06a219c0650180c5e316a056d14c84f712f048111184020f1c38c0d2030d0b4828e097022107981ab059c13503e80bf021004900ec000bffaa998456ffeaa64d51fdfaa982957fdeaa60a33ffeaa982803dfeaa60677fdfaa981957fdeaa60633ffeaa981803bfeaa54e88fdfaa953497f7eaa4d585ffbaa91888b7feaa24182bffaa89060b7feaa24181bffaa890607ff69945581ffda65136077fe9924182dffa6490606ffda960d25dff6a582546ffda960951dff6a5824c6ffda960931dff6a5514cb7fda94c525bff6a5314977fda94958 else (if i<4 then 0xc719cd4ee045622232d3b811111c58b42e2f1383c0c7544fc5e270b238ea59b11c5e273b1b4b308aa38fe0478bc0a708f1a4e053e1b1f27021b1e1f029b8e8a9309c3e163da34b334697271e1789c2c7346966c7b469729262388cec6b3e966c6b3d9d4b93978151874589c0a763471ea770223162e2389c3c6b3e966c6b3e9727271307c2c8b3e966e2f098991c752cd41c7e3599292b130adee6e3a966e2c8f84c18f4469d8c432381c4e5d3f1a213b231dc1e7d331a213d0f85c168d331e6e2987854468d3b1676450b838fa663b2076470f834cc7d34cc8e250f83c0c7d34ec8e2f069d8ca69991c531b7a9d8ba69c281250781c14888c84908243c8e0d331acf10998bc2e0d33234e370e85c167d33226a2720c55667d3716762f1285c1e06469c7e4317834dc6538cc530f11bf4dc5d38fc5e270a8391c71b8bc4e1646838e36478bc1e6e3998223f1783ce66634446e0d35998e27458945af98b9b8ba7238b42e0b329d91372287c1665371e662714c4dea7537167e2f0b238e1152cdc8e1e3f1a22a59b9185e6e38454b371781c4e5b3b1a213f2383cdc663c426c433b89cfc6886967e47131b8f10d2cdc8c27371e21a59b90cec273f1a21a59f8bc4e030b978ec89f91c3e0e3d9b8c37238985e072d9b8e3e238bc466e3a966e4613878f66d2cdc8c2f119b8ea59b8391675309c111e319b4e2f07814fc6d39bc6a853f174e6f169ed1c5b789c2e0d1718d1671b89c2a2e2da2ce37178544c5b459c6e27053fc0a6b38cc2e0d3b194f689991c4a762e9ecd370f82c8a7e319a664713874fc5b34dc0e0b471c4c7e3a98d1263e98d11e3a96cd4a931bc067371ae5687019cdc6b959bc06736dae567f01a2da69969fc068b65a65677019ad86e9787c1a46359ecc370f8581a8b3d986c8b329c30f48d45c1e04458b4e474589cdc5d38ac5e1706a38c671b89c12ff031ace331789c2a8e2d9c6e07059f8d270f8348c633d9a6a470ebccfc5b34d44e45599f8b669a87c1c455b80cf669f18cda70cd3c8e2337174e33371d4b4a9189c22fb589f8ba89ea3c0e0c38bc5e0d47818f6b1691c1c6b3b80d635459d8b6b129f8b6b0f834de063dac5677029a56215b91c53153716ce3b0b838fa8e39986e1b0b838fa8b30dc5e717b16cd2f21894fc5d399a6e4313874fc5b34d88e0e7e9ccd661a9c4d66154855a77009a562e319d4d1f178863c5b3a9a6e4734ad8b6796a3c1e033a3c5e0f02a38f6a97838c67545aa56762ea2d5270718cda7b54acdc5d3daa4a23359d8b6a9781c1873362c554f03834847b34c290f1381cba8e3e2a613844391c732c465c6b2c463e429789c35463f1acb463d96221f1709c2a8e39966a4717898ec6b2cdc8c270e9f8d659b9145e263b1acb37230b44e6e39966e4716898ec6b2cdc2e0d3da38ca71991c06f53f else 0x11f0c9e882a1d205c5e2708c34ec5d44c68e2f3abd8ba698cd44a28a0b1615123e2a154454b0e3682286c7c50d8f084341108e822a76344210888384110a9b8313443c5e734716673119914e160591cce6d38c26645044c70b5fa38b67188ac60b47062680703c866f31a061331a8224f858a1e8f3b16673114ce1c218c42310898823108d3c16208f223c09879fcd6618ccc4a689881e470e9b4f34e2cd81e43339b4e30998941163989411b0f1a231a582c3a68b91c434d359d8b333b102c0f479f4c33988d8d61d046230b08462610871c3c09879fcc6698cd830b0a9c2c0f2398cda7184cc2a08b1cc2a08da34e12894e26253858ea10b1d44163a82267d3716e06a15c141650e9b4ec5b7eaa56fd045420d3a9b8baab78adea08a5216186d3c4a2d09a2cec59ecfc5a1511a2cec59e5341149e822668706cd15599a2a73345c4a1b2316cda7999b411329b8267b4717566995a38ba7365a6564b6682364b605880e083550f21894d67e2eaa667064f41670eac1e433d9b8bab168616b0652d6135a8226105cf45afb119b8ba71e821c6b384d6a68b8b486762e9ad633543850d10208b071c1a70688c11635822c730454d6089821c13044c1c20a9cc113071e260c5858e60c5478ee0d4718212f07194fc6888bc0e0e471e222f038223c6888b91c2f03834e119b1fc0e0d363e23371385c1c2f02a34e3f1785c1c65469c6e2f138551c5d38d42e2707818ec7d44fc4e0d57818fa89a85c5e0f3b1951373cc75ee762e9a6e1f0b8391a7d30dc087c587c0e1f329f91349b91c3a6e329e69372389c3a6d3f16693f029a2987c54bc8e1f071b4fa61b87d1c0f369f4c3647810f8f138bcee0644ce5e463e9bc)))
def flip0l11 : Packing := (420,3,6,0,0,14,0,flip0d11)
def flip0d12 (i : Nat) : Nat := (if i<1 then 0x2e3738a504587a3839b1f18721c5c2c1518c8e3a410afe02f65c746a0242459187829f1b1874521c4c05fcb8d8e410e8e0c2e6a6471c87231705323a34f8583211f811cbc7c3c2c151c08f5e3a1ab602ae5a8c79f170b05453a30d8b8984a3169c648c0425ecb8f8e9042461e02f65c7a69d7307093a45315cf80b78311989c9aae85ac1c3518c4f533e261a8c5a7a99967070d463d314cea19f02a39c98a67c058c185cc4d4e5d42c60e2a6c6272e9f1711362d3974d8785829f22986d1c1cd4c8e2e0616622e5c8a71da623030e7b2d3d350d39187829f189a769c8c4c34f4d8b394e0646665a6c71f0f0b047c3d3244f8b85829d8122ac7d1c1cdc08f56362e8e6a745ab189c8b2317045b0235392cf9f82859c9922767c8c18f4d4c8e3b3e461e0a6c7a61d9f233d1339362cf818b9847969d1a723c5c2c11e114e8c468e0a2e6c6271b134517362d38d8b8199969d22aa7c8c0cccb4d8f553e462e0a726c62a9f231711353a2d54f8b8985231c966c8c4c38f8d4b293e467e746a5939b13461736392cd8185991f96a31c7c3c0c2cccb8f513e167e0e728c619233f017b3b2e34f89859f9ca316650d1c14fcd8c4e3e0646627e5c6a71f2311413f362d38f87a3839a9f186c4c3d1cd4f8b3686768e7ab66c59f17030b332d3a44f91818799971e9a7b1b57c6b6956fa95535692144ba074f4672934f9854b1652125b91347a634916789543b61710838234024740fd47c7bd29e0aec8745b919c72e3971cb7f1b6ed7a69eb401986c86628b0717aeb9a5aeac615b6aa6534a8b13ce9aa4baa5012268d6448a15102e7da3ce9d80e566f635499b0c5e5f22da95e0a664fe264923089e4121ea8e806c632e17c8af04fe24a106876033615e09083b016e07a01e8003ffd32c17ffa6581ffecc263ffd98497ffb2e98fff65925ffecaa63ffd9360bffb26a8fff64d25ffec92a3ffd924c7ffb22c17ff64525ffec3a63ffd85487ffb0690fff60951ffec1263ffd81497ffaca997ff58d25ffea9a43ffd514cbffa6292fff48d81ffe48305ffc90496ffd32c15ffa6581bff4caa37fe994d6ffb30995ff66121bfecb26b7fd964caffb2c92dff65531bfecaa437fd93496ffb2690f7f60e77fbec1cabf7d82957fbb0519ffe60a00efec0ceff7d819577fae7446ff5c688feeb2c67ff965803efac72affe58e00fbeb14abfdd628cfff2c5006ff54e88fbea9a4bbfd52a237faa3447f754633ffca8c01f7d51497efa6ac2eff4ca88fbe994abff932803fba6498eff4c688efe98ceff7d31957ff263006ff4a181dfe94271fdd258cfff24b006ff48688fbe90cabfdd218cfff243005ff24182bfe482a37fc904c6ff92092e7fa2277dbf444abbde888cf7ed1108efea2200eef3bc67df677847bf4ef007d795633fbd2ac01fda338037dc45447dd84655 else 0x62e2616011e5c8c710a60b1713033b2e448d18b839d80a24e44785c0c1c2cc518e2146460c6abe0271391214617020f067f3135408559187831a9f804e44891c1c523cd8e4c2146461e0c6c7a6149e17072335323884f918981971a9c527c8c5c18d4e8c272246060e291e6472690a217030723313638851829f1b18c0a86c0c18d8e5f95360e04746af4a9aa713032c7d3a34f4f8b82909d811a2c8c4c08542cb518e3e0c76028ad4b299e17032d4639654cf91831a9e992a6c8c1c04f4d96333e442e0a6a6471f160b053b024558f0b91899a971c621c5c0c2cccb918e411e267e0416765c8a303223f33)
def flip0l12 : Packing := (98,2,6,0,0,13,0,flip0d12)
def flip0d13 (i : Nat) : Nat := 0x22c085325911c735021c19844793410333e0ce22309a0c408b0660d1c750a6440873258f1a88b460cd1d00b1d3c89f0670d18789460059b2c71e445813258e1a5511214f813a591390894600f9b2c722243a3026cb1e7a1467c19d3461e844a33e74d167ba2ab9ba317d1be62152454df2886c0d800ffd82ffd65ffd63ffd62ffd51ffd32ffd31ffd25ffd21bfe88dfe77f7e55fde33ffa00
def flip0l13 : Packing := (14,1,6,0,0,10,0,flip0d13)
def flip0d14 (i : Nat) : Nat := 0x101113c038d2d1ff
def flip0l14 : Packing := (1,0,6,0,0,0,0,flip0d14)
def flip0samples : Array (Bits × Bits) := #[(0xe3f2e6fffe4e03fff99dbaead6b254dbf79dfffdb709fff06f49c139698ddfff73c330001ffff80007ffc3ff80036ffffc71f8ffff38f3ffffffffc0fc0fff03dcf7c79c3ffb39ffbdf05e63eede5b37fdf7b8c70f6f2674ccd6fe38c1f60e18,0xa3fbeebf7e6f52fde91dfee6d67b429bfffdfefdf7b9fdd0ffefed7d6bc9cfef7ffff32f3fffbcd5cffe4ffe94e5dfaceb8edfbd6d6d7965d77d6ecbfd5b6b2fdcf7ef9c7ffb39ffbdf6de67eededb37fdf7bdcf1fff6ef5dcd6fffddbf6de39),(0x1e32930004bc4c001e130f00723671fd9e1c001c4930001ce6d8db80d91ffffec6433000e00188006000ffffffc30001c003f0007003c0000000fc000003ffe10a52610c040206430b2187c00061c3b30c6249c31632604c0ff66a4c8c6487f,0x1a36a31040a40c4200010a00202420bdbf5c209d49904008644841800814a0e6dad73010e01888046020d9614e0ce88608a409524242800c52c24c32c124b2e10a526104040206430a218440004102330c6248c10420400808464a488c44831),(0x27c31c0007387000191c303183c79e061800001071dfffe7071f1c18e1e100070773c0010001f0007fff3ffe0006000e001f8003800f0000003f000000fff000001c01f2583c181c13c6072081863c4010038e7c98c38470f188738f1078f9c,0x8e5c91c208f59f0803b148030014094020000010020041e6513a51c38e34102090500c0250021700912cb269600910570e300428494951961801911481acb4500000800a2583c181c11c60320810028401001002898838470a1883107103850c),(0x3803e00007c07fffe1e03fc1fc07e0381fe0001f81e00007f81fe01f01fe0007f87c0001fffe00007fffc00000140380071c0060038c0003f000000fc0fc000600607e0080c000601c07f8070e07c003e07c0f80e0fc0780fe0f83f01f80fe0,0x802e10100000c1f00603fc6b80f62e81ff4421581f0800aa81ae2c300be0422687d1048a54c00026d30c0200322a80a08e094292928421473426493403492460000540080c00060000150070a07c003e0540f80407c02805e0502f00a80ae0),(0x3ffc000007ff800001ffc001fff8003fe000001ffe000007ffe0001ffe000007ff800001ffffffff800000000000000007e0000003f000000000000fff0000380c7f80031f001f801ff800380ff8007c007ff000ff0007ff000ffc001fff000,0x37bc0a4206f52100119fc02947b00917e008840a7a01040556e41514bc000845978220815ab1cd5c004000c0041d52c4b00d6bd6d6d794490494882c958220b80c7e80031f001f801f68003805e8007c002bd000bf00055d000afc00156d000),(0x3ffffffff800000001fffffe0000003fffffffe000000007ffffffe000000007fffffffe000000000000000000281c703800019c0c0000fc0fc003f0000000000f800003e0001fffe000003ff000007fff800000fffff800000fffffe000000,0x1b16e307c00004040155a6640100001eaacc0f8000000807fefed7d2a88c1087ffff32f060c08810218043000811608e006492849495021c31c02cb1c11430c000000003e000157280000034c000006a9a000000fff6e800000fffdda000000),(0xfc00000000000000001ffffffffffffc00000000000000007fffffffffffffff80000000000000000000000000000e001c0000e0070003f000000fc000000003ff0000003ffffe0000000003fffffff8000000000fffffffffff000000000000,0xc410040040000000801fef5ffdfdbdf4240a10802926210279bb7be7ff7eb5f09252843000300106006010402103317181149b6adbdbd47102505b0c506184116a0000003f2e940000000003fffbefd8000000000fbdfbff7f7b000000000000),(0x1fffffffffffffffffffffffffffff800000000000000000000000000000000000000000000007e0000001f800000000fff00000000003ffffffffc000000000000003fffffffffffffffff00000000000000000000000,0x10020008010a60a1044aa598bfebf6be15533f03fdffbe0980000200514326000000004008c00018048008800602e9a011c9b2d7b6b6ae4824e26c20624208a3ffff7ff5c000000000000000b3effd79565feffd700000000000000000000000),(0xffffffffffffffffffe00000000000000000000000000000000000000000000000000000000000000000000000030ff8000000fe000003ffff00000000000003fffffffffffffffffffffffc0000000000000000000000000000000000000000,0x1a4e91cf81ffff3e07e00000000200001000200286c0c00d00000000000008000000088011001660010023005800c0061e61249524242b8e38838030838c30c295fffabfc0d16aa8d7ffeafc0000000000000000000000000000000000000000)]
def flip0columns : IndexTree ColumnInfo := (.fork 21 (.fork 10 (.fork 5 (.fork 2 (.leaf [(16,0,1007,0,13),(0,1,510,0,12)]) (.leaf [(2,0,1021,0,12),(4,0,1019,0,12),(8,0,1015,0,12)])) (.fork 2 (.leaf [(32,0,991,0,12),(64,0,959,0,12)]) (.leaf [(128,0,895,0,12),(256,0,767,0,12),(0,64,701,258,11)]))) (.fork 5 (.fork 2 (.leaf [(0,128,859,36,11),(16,1,494,0,11)]) (.leaf [(24,0,999,0,11),(66,0,957,0,11),(132,0,891,0,11)])) (.fork 3 (.leaf [(160,0,863,0,11),(192,0,831,0,11),(320,0,703,0,11)]) (.leaf [(0,16,486,9,10),(2,64,701,256,10),(4,128,859,32,10)])))) (.fork 10 (.fork 5 (.fork 2 (.leaf [(6,0,1017,0,10),(12,0,1011,0,10)]) (.leaf [(32,128,859,4,10),(68,0,955,0,10),(72,0,951,0,10)])) (.fork 2 (.leaf [(96,0,927,0,10),(130,0,893,0,10)]) (.leaf [(136,0,887,0,10),(256,64,701,2,10),(264,0,759,0,10)]))) (.fork 5 (.fork 2 (.leaf [(288,0,735,0,10),(384,0,639,0,10)]) (.leaf [(0,4,881,138,9),(0,8,739,276,9),(0,256,663,104,9)])) (.fork 3 (.leaf [(0,17,486,8,9),(2,1,508,0,9),(8,16,486,1,9)]) (.leaf [(10,0,1013,0,9),(32,1,478,0,9),(34,0,989,0,9)])))))
def flip0autos : Array (List Nat) := #[[],[81,130,118]]
def flip0levels : Nat → Packing
  | 8 => flip0l8
  | 9 => flip0l9
  | 10 => flip0l10
  | 11 => flip0l11
  | 12 => flip0l12
  | 13 => flip0l13
  | 14 => flip0l14
  | _ => emptyPacking
def flip0index : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 2 9 4 7 2 1 (keyflip0l9)
  | 10 => lookupWord 68 314 9 12 7 1 (keyflip0l10)
  | 11 => lookupWord 395 1820 11 15 10 1 (keyflip0l11)
  | 12 => lookupWord 289 1332 11 14 9 1 (keyflip0l12)
  | 13 => lookupWord 71 327 9 12 7 1 (keyflip0l13)
  | 14 => lookupWord 12 58 6 9 4 1 (keyflip0l14)
  | _ => fun _ => none
def flip0 : Forest := ⟨1023,14,fun j => flip0samples[j]?.getD (0,0),flip0columns,flip0autos,flip0levels,flip0index⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geomflip0 : graphValid flip0 (boundsBefore knownPrev_flip0) = true := by
  unfold graphValid
  refine Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨by decide +kernel, by decide +kernel⟩, ?_⟩, by decide +kernel⟩
  apply listPieces_all (d:=4)
  simp only [listPieces,IndexTree.values,List.length_append,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceDiv,List.take,List.drop]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sflip0_8_0 : block flip0 8 0 3=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allflip0_8 : block flip0 8 0 3=true := sflip0_8_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sflip0_9_0 : block flip0 9 0 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sflip0_9_32 : block flip0 9 32 22=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sflip0_9_54 : block flip0 9 54 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sflip0_9_86 : block flip0 9 86 28=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allflip0_9 : block flip0 9 0 114=true := (@block_merge flip0 9 0 86 28 (@block_merge flip0 9 0 54 32 (@block_merge flip0 9 0 32 22 sflip0_9_0 sflip0_9_32) sflip0_9_54) sflip0_9_86)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sflip0_10_0 : block flip0 10 0 27=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sflip0_10_27 : block flip0 10 27 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sflip0_10_59 : block flip0 10 59 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sflip0_10_91 : block flip0 10 91 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sflip0_10_123 : block flip0 10 123 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sflip0_10_155 : block flip0 10 155 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sflip0_10_187 : block flip0 10 187 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sflip0_10_219 : block flip0 10 219 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sflip0_10_251 : block flip0 10 251 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sflip0_10_283 : block flip0 10 283 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sflip0_10_315 : block flip0 10 315 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sflip0_10_347 : block flip0 10 347 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sflip0_10_379 : block flip0 10 379 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sflip0_10_411 : block flip0 10 411 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sflip0_10_443 : block flip0 10 443 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sflip0_10_475 : block flip0 10 475 23=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sflip0_10_498 : block flip0 10 498 32=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sflip0_10_530 : block flip0 10 530 32=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sflip0_10_562 : block flip0 10 562 13=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allflip0_10 : block flip0 10 0 575=true := (@block_merge flip0 10 0 562 13 (@block_merge flip0 10 0 530 32 (@block_merge flip0 10 0 498 32 (@block_merge flip0 10 0 475 23 (@block_merge flip0 10 0 443 32 (@block_merge flip0 10 0 411 32 (@block_merge flip0 10 0 379 32 (@block_merge flip0 10 0 347 32 (@block_merge flip0 10 0 315 32 (@block_merge flip0 10 0 283 32 (@block_merge flip0 10 0 251 32 (@block_merge flip0 10 0 219 32 (@block_merge flip0 10 0 187 32 (@block_merge flip0 10 0 155 32 (@block_merge flip0 10 0 123 32 (@block_merge flip0 10 0 91 32 (@block_merge flip0 10 0 59 32 (@block_merge flip0 10 0 27 32 sflip0_10_0 sflip0_10_27) sflip0_10_59) sflip0_10_91) sflip0_10_123) sflip0_10_155) sflip0_10_187) sflip0_10_219) sflip0_10_251) sflip0_10_283) sflip0_10_315) sflip0_10_347) sflip0_10_379) sflip0_10_411) sflip0_10_443) sflip0_10_475) sflip0_10_498) sflip0_10_530) sflip0_10_562)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sflip0_11_0 : block flip0 11 0 20=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sflip0_11_20 : block flip0 11 20 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sflip0_11_52 : block flip0 11 52 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sflip0_11_84 : block flip0 11 84 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sflip0_11_116 : block flip0 11 116 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sflip0_11_148 : block flip0 11 148 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sflip0_11_180 : block flip0 11 180 30=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sflip0_11_210 : block flip0 11 210 32=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sflip0_11_242 : block flip0 11 242 32=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sflip0_11_274 : block flip0 11 274 32=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sflip0_11_306 : block flip0 11 306 32=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sflip0_11_338 : block flip0 11 338 32=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sflip0_11_370 : block flip0 11 370 32=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sflip0_11_402 : block flip0 11 402 18=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allflip0_11 : block flip0 11 0 420=true := (@block_merge flip0 11 0 402 18 (@block_merge flip0 11 0 370 32 (@block_merge flip0 11 0 338 32 (@block_merge flip0 11 0 306 32 (@block_merge flip0 11 0 274 32 (@block_merge flip0 11 0 242 32 (@block_merge flip0 11 0 210 32 (@block_merge flip0 11 0 180 30 (@block_merge flip0 11 0 148 32 (@block_merge flip0 11 0 116 32 (@block_merge flip0 11 0 84 32 (@block_merge flip0 11 0 52 32 (@block_merge flip0 11 0 20 32 sflip0_11_0 sflip0_11_20) sflip0_11_52) sflip0_11_84) sflip0_11_116) sflip0_11_148) sflip0_11_180) sflip0_11_210) sflip0_11_242) sflip0_11_274) sflip0_11_306) sflip0_11_338) sflip0_11_370) sflip0_11_402)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sflip0_12_0 : block flip0 12 0 13=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sflip0_12_13 : block flip0 12 13 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sflip0_12_45 : block flip0 12 45 25=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sflip0_12_70 : block flip0 12 70 28=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allflip0_12 : block flip0 12 0 98=true := (@block_merge flip0 12 0 70 28 (@block_merge flip0 12 0 45 25 (@block_merge flip0 12 0 13 32 sflip0_12_0 sflip0_12_13) sflip0_12_45) sflip0_12_70)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sflip0_13_0 : block flip0 13 0 5=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sflip0_13_5 : block flip0 13 5 9=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allflip0_13 : block flip0 13 0 14=true := (@block_merge flip0 13 0 5 9 sflip0_13_0 sflip0_13_5)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sflip0_14_0 : block flip0 14 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allflip0_14 : block flip0 14 0 1=true := sflip0_14_0
theorem tablesflip0 : checkedTables flip0 14 := by
  intro k hk
  interval_cases k
  · exact (rfl : block flip0 0 0 0 = true)
  · exact (rfl : block flip0 1 0 0 = true)
  · exact (rfl : block flip0 2 0 0 = true)
  · exact (rfl : block flip0 3 0 0 = true)
  · exact (rfl : block flip0 4 0 0 = true)
  · exact (rfl : block flip0 5 0 0 = true)
  · exact (rfl : block flip0 6 0 0 = true)
  · exact (rfl : block flip0 7 0 0 = true)
  · exact allflip0_8
  · exact allflip0_9
  · exact allflip0_10
  · exact allflip0_11
  · exact allflip0_12
  · exact allflip0_13
  · exact allflip0_14
theorem flip0_start : Impossible (graphGoal 1023) 14 inputs.toFinset := by
  exact root_index (g:=flip0) (before_sound known1015 valid1015) geomflip0 tablesflip0 (k:=14) (by decide) (i:=0) (ws:=inputs) (by decide +kernel)

def flip0Vec (x : Fin 9 → Bool) (i : Fin 9) : Bool :=
  if i = 0 then !x 0 else x i

theorem flip0Vec_inv (y : Fin 9 → Bool) :
    (fun i : Fin 9 => if i = (0 : Fin 9) then !(flip0Vec y (0 : Fin 9)) else flip0Vec y i) = y := by
  funext i
  by_cases h : i = (0 : Fin 9)
  · subst h; simp [flip0Vec]
  · simp [flip0Vec, h]

theorem goal1023_table : ∀ r : Row, bit r (graphGoal 1023) = edge (flip0Vec (sample r)) := by
  decide +kernel

theorem goal1023_proper : proper (graphGoal 1023) := by
  unfold proper; decide +kernel

theorem goal1023_ess :
    checkEssential (graphGoal 1023) inputs (graphPairs 1023 13438558465) = true := by
  decide +kernel

theorem goal1023_pairs_fst :
    (graphPairs 1023 13438558465).map Prod.fst = inputs := by
  decide +kernel

theorem main_3271 :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo x1 →
      x1.size ≤ (14 : ℕ) →
      (List.filter (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => x4.inputs.contains (0 : ℕ)) x1.gates).length ≤ (1 : ℕ) →
      (∀ (x5 : Fin (9 : ℕ) → Bool),
        x1.eval (List.ofFn fun (x6 : Fin (9 : ℕ)) => if x6 = (0 : Fin (9 : ℕ)) then !x5 (0 : Fin (9 : ℕ)) else x5 x6) =
        (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)))) →
      False := by
  intro C hfan hsize _honce heval
  have hgoalEq : (execute C.gates inputs).getD C.output zero = graphGoal 1023 := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j, hj⟩
    have hr := heval (flip0Vec (sample r))
    rw [flip0Vec_inv (sample r)] at hr
    exact (table_eval C hfan C.output r).trans (hr.trans (goal1023_table r).symm)
  have hout := get_rep (execute C.gates inputs) C.output
  rw [hgoalEq] at hout
  have targetIn : graphGoal 1023 ∈ execute C.gates inputs :=
    hout.resolve_right (fun hn => hn goal1023_proper)
  obtain ⟨k, t, S, hk, run, hs⟩ := extract C.gates inputs hfan goal1023_proper targetIn
  have hk14 : k ≤ 14 := le_trans hk hsize
  have hS : inputs.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_, hs a⟩
    have hess : Essential (graphGoal 1023) inputs a := by
      apply essential_ok goal1023_ess a
      rw [goal1023_pairs_fst]
      exact List.mem_toFinset.mpr hm
    obtain ⟨r1, r2, hd, iso⟩ := hess
    exact raw_required run inputs a hs r1 r2 hd iso
  exact flip0_start k t hk14 (hS.symm ▸ run)

end PEqualNP.Outside.L_meta_3929

theorem PEqualNP.Outside.L_meta_3929 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (14 : ℕ) → (List.filter (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => x4.inputs.contains (0 : ℕ)) x1.gates).length ≤ (1 : ℕ) → (∃ x5 ∈ x1.gates, (x5.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x5.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ x6 ≥ (9 : ℕ), x5.inputs = [(0 : ℕ), x6] ∨ x5.inputs = [x6, (0 : ℕ)]) → (∀ (x6 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn fun (x7 : Fin (9 : ℕ)) => if x7 = (0 : Fin (9 : ℕ)) then !x6 (0 : Fin (9 : ℕ)) else x6 x7) = [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x7 : ℕ) => x6 (Fin.ofNat (9 : ℕ) (x7 / (10 : ℕ))) && x6 (Fin.ofNat (9 : ℕ) (x7 % (10 : ℕ)))) → False := by
  intro C hfan hsize honce _hgate heval
  refine PEqualNP.Outside.L_meta_3929.main_3271 C hfan hsize honce (fun x => ?_)
  rw [heval x]
  simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc]
  rfl
