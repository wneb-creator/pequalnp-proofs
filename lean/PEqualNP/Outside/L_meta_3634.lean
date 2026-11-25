import PEqualNP.Defs

-- The pair bound below is reproduced from the checked L-meta-2834.
-- Adapted from JLDC's Apache-2.0 proof of L-meta-1676 in PR 6373.
-- The new proof prepends the two OR gates supplying the tail inputs.
-- The live-set calculus and induced-graph certificates are from PressF10, L-meta-1667.
namespace PEqualNP.Outside.L_meta_3634
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
def orSeed : Sig := inputs.getD 0 zero ||| inputs.getD 4 zero
theorem seed_table : ∀ r : Row, bit r orSeed = (sample r 0 || sample r 4) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem seed_nonzero : orSeed ≠ zero := by decide +kernel
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
    ((inputs++[orSeed]).all fun w => w == inputs.getD i.val zero ||
      bit (absentRow i) w == bit (presentRow i) w) = true := by decide +kernel

theorem all_roots {k t S} (h : Live graph k t S) (sub : ∀ v ∈ S, v ∈ inputs++[orSeed]) :
    S=inputs.toFinset ∨ S=(inputs++[orSeed]).toFinset := by
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
  by_cases hseed : orSeed ∈ S
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
    ∃ k t, k ≤ 14 ∧ (Live graph k t inputs.toFinset ∨ Live graph k t (inputs++[orSeed]).toFinset) := by
  have headEq : (execute C.gates inputs).getD 9 zero = orSeed := by
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
    have eq0 : gv inputs g = orSeed := by
      rw [hgs] at headEq
      change (execute gs (inputs++[gv inputs g])).getD 9 zero = orSeed at headEq
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
  if m.testBit 11 then raw ++ [vertex m 0 ||| vertex m 4] else raw
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
  if m=1023 then graphGoal m &&& ~~~seed else graphGoal m
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


-- The low nine bits select vertices. A set bit at position eleven supplies
-- the disjunction of the two surviving endpoints as an additional input.
def poolMask (m : Nat) (c : ColumnInfo) :=
  if m.testBit 11 && !c.2.2.1.testBit 11 then m % 512 else m

def poolColumn (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) :=
  if m.testBit 11 && !c.2.2.1.testBit 11 then
    (chartGoal (m % 512) == chartGoal m) && colCheck (m % 512) c prior
  else colCheck m c prior

theorem poolColumn_sound {m} (c : ColumnInfo) (prior : Nat → Nat)
    (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (ok : poolColumn m c prior = true) :
    Slice (vars (poolMask m c)) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  unfold poolColumn at ok
  unfold poolMask
  split <;> rename_i tag
  · rw [if_pos tag] at ok
    obtain ⟨same,check⟩ := Bool.and_eq_true_iff.mp ok
    rw [←beq_iff_eq.mp same]
    exact col_sound c prior low check
  · rw [if_neg tag] at ok
    exact col_sound c prior low ok

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


-- If the supplied wire vanishes from the live set, its original circuit
-- lower bound applies. Otherwise the raw input witnesses force the entire
-- augmented starting set to be live.
theorem augmentedLower {raw : List Sig} {e T : Sig} {k : Nat} (hp : proper T)
    (old : Lower raw T (k+1))
    (must : ∀ a ∈ raw, Essential T (raw++[e]) a)
    (no : Impossible T k (raw++[e]).toFinset) : Lower (raw++[e]) T (k+1) := by
  intro p bank hr ha
  obtain ⟨n,t,S,hn,run,sub⟩ := reach_live hp hr ha
  by_cases he : e ∈ S
  · have eq : (raw++[e]).toFinset = S := by
      ext a
      rw [List.mem_toFinset]
      refine ⟨?_,sub a⟩
      intro hm
      rcases List.mem_append.mp hm with hw | hw
      · obtain ⟨r,s,hd,iso⟩ := must a hw
        exact raw_required run _ a sub r s hd iso
      · have same : a=e := by simpa using hw
        exact same.symm ▸ he
    by_contra! small
    exact no n t (by omega) (eq.symm ▸ run)
  · have supp : supply (raw.map observe) (S.toList.map observe) := by
      intro a ha
      obtain ⟨v,hv,rfl⟩ := List.mem_map.mp ha
      have mem : v ∈ S := by simpa using hv
      apply Or.inl
      apply List.mem_map_of_mem
      rcases List.mem_append.mp (sub v mem) with hw | hw
      · exact hw
      · have eq : v=e := by simpa using hw
        exact False.elim (he (eq ▸ mem))
    obtain ⟨q,W,reach,goal,budget⟩ := contraction (observe_proper hp)
      (list_run run S.toList (Finset.nodup_toList _) (by simp)) _ Reach.start supp
    have bound := old q W reach goal
    omega

theorem augmentedGraph {m k hints tagged}
    (hp : properB (graphGoal m) = true)
    (rawEq : vars tagged = vars m ++ [orSeed]) (goalEq : graphGoal tagged = graphGoal m)
    (old : Lower (vars m) (graphGoal m) (k+1))
    (ess : checkEssential (graphGoal m) (vars tagged) (graphPairs m hints) = true)
    (all : (graphPairs m hints).map Prod.fst = vars m)
    (no : Impossible (graphGoal tagged) k (vars tagged).toFinset) :
    Lower (vars tagged) (graphGoal tagged) (k+1) := by
  rw [goalEq,rawEq] at no ⊢
  apply augmentedLower (proper_of _ hp) old _ no
  intro a ha
  rw [←rawEq]
  apply essential_ok ess
  rw [all]
  exact List.mem_toFinset.mpr ha

theorem countImpossible {T : Sig} {S : Finset Sig} {k : Nat} (small : k+1 < S.card) :
    Impossible T k S := by
  intro n t budget run
  have h := (live_size run).2
  omega
-- For an induced graph containing edge (0,4), supply the OR of its
-- endpoints for free. Each bound can then be reused on a smaller set of
-- rows when the same two endpoints survive a restriction.

namespace Free23

theorem noRun : Impossible (graphGoal 2071) 3 (vars 2071).toFinset := countImpossible (by decide +kernel)

end Free23

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound23 : Lower (vars 2071) (graphGoal 2071) 4 :=
  augmentedGraph (k:=3) (m:=23) (hints:=260) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (before_sound _ valid383 23) (by decide +kernel) (by decide +kernel) Free23.noRun

def entries23 := extendKnown known383 4 [(2071,[]),(2077,[49,64]),(2225,[114,33,97,82,49]),(2329,[130,114,98,82,49,64]),(2353,[130,114,33,97,82,49])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound23 : Known entries23 := extendKnown_ok valid383 seededBound23 (by decide +kernel)
namespace Free27

theorem noRun : Impossible (graphGoal 2075) 3 (vars 2075).toFinset := countImpossible (by decide +kernel)

end Free27

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound27 : Lower (vars 2075) (graphGoal 2075) 4 :=
  augmentedGraph (k:=3) (m:=27) (hints:=16388) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (before_sound _ valid383 27) (by decide +kernel) (by decide +kernel) Free27.noRun

def entries27 := extendKnown entries23 4 [(2075,[]),(2105,[49,81,33,64])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound27 : Known entries27 := extendKnown_ok sound23 seededBound27 (by decide +kernel)
namespace Free31

def liveData6 (i : Nat) : Nat := 0x1103fd40

def moveIndex6 (i : Nat) : Nat := 0x1690a11080000203e018

def liveData5 (i : Nat) : Nat := 0x1008041db920bf2aa817d52502faa2a07e4c140

def liveLevels : Nat → Packing
  | 6 => (1,1,2,0,0,0,0,liveData6)
  | 5 => (4,2,2,0,0,5,0,liveData5)
  | _ => emptyPacking

def liveIndex : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 3 8 2 10 2 4 moveIndex6
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

def orCols : IndexTree ColumnInfo := (.leaf [(2,0,2077,0,4),(4,0,2075,0,4),(8,0,2071,0,4)])

def orForest : Forest := ⟨2079,6,fun j => orSamples[j]?.getD (0,0),orCols,orSymmetries,liveLevels,liveIndex⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem orGeometry : graphValid orForest (boundsBefore entries27) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked6At0 : block orForest 6 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked5At0 : block orForest 5 0 4 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

theorem allAt6 : block orForest 6 0 1 = true := checked6At0
theorem allAt5 : block orForest 5 0 4 = true := checked5At0
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

theorem noRun : Impossible (graphGoal 2079) 6 (vars 2079).toFinset :=
  root_index (g:=orForest) (before_sound _ sound27) orGeometry orTables
    (k:=6) (by decide) (i:=0) (by decide +kernel)

end Free31

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound31 : Lower (vars 2079) (graphGoal 2079) 7 :=
  augmentedGraph (k:=6) (m:=31) (hints:=8452) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (before_sound _ valid383 31) (by decide +kernel) (by decide +kernel) Free31.noRun

def entries31 := extendKnown entries27 7 [(2079,[]),(2361,[130,114,49,98,81,64])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound31 : Known entries31 := extendKnown_ok sound27 seededBound31 (by decide +kernel)
namespace Free55

theorem noRun : Impossible (graphGoal 2103) 4 (vars 2103).toFinset := countImpossible (by decide +kernel)

end Free55

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound55 : Lower (vars 2103) (graphGoal 2103) 5 :=
  augmentedGraph (k:=4) (m:=55) (hints:=260) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (before_sound _ valid383 55) (by decide +kernel) (by decide +kernel) Free55.noRun

def entries55 := extendKnown entries31 5 [(2103,[]),(2163,[98,50]),(2227,[114,98,50,81])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound55 : Known entries55 := extendKnown_ok sound31 seededBound55 (by decide +kernel)
namespace Free61

theorem noRun : Impossible (graphGoal 2109) 4 (vars 2109).toFinset := countImpossible (by decide +kernel)

end Free61

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound61 : Lower (vars 2109) (graphGoal 2109) 5 :=
  augmentedGraph (k:=4) (m:=61) (hints:=8964) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (before_sound _ valid383 61) (by decide +kernel) (by decide +kernel) Free61.noRun

def entries61 := extendKnown entries55 5 [(2109,[]),(2233,[114,83,98,64])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound61 : Known entries61 := extendKnown_ok sound55 seededBound61 (by decide +kernel)
namespace Free151

theorem noRun : Impossible (graphGoal 2199) 4 (vars 2199).toFinset := countImpossible (by decide +kernel)

end Free151

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound151 : Lower (vars 2199) (graphGoal 2199) 5 :=
  augmentedGraph (k:=4) (m:=151) (hints:=536871172) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (before_sound _ valid383 151) (by decide +kernel) (by decide +kernel) Free151.noRun

def entries151 := extendKnown entries61 5 [(2199,[]),(2229,[81,114,49]),(2387,[135,98,82,50]),(2393,[130,114,98,82,49,64]),(2417,[130,114,33,97,82,49])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound151 : Known entries151 := extendKnown_ok sound61 seededBound151 (by decide +kernel)
namespace Free433

theorem noRun : Impossible (graphGoal 2481) 4 (vars 2481).toFinset := countImpossible (by decide +kernel)

end Free433

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound433 : Lower (vars 2481) (graphGoal 2481) 5 :=
  augmentedGraph (k:=4) (m:=433) (hints:=22817013764) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (before_sound _ valid383 433) (by decide +kernel) (by decide +kernel) Free433.noRun

def entries433 := extendKnown entries151 5 [(2481,[])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound433 : Known entries433 := extendKnown_ok sound151 seededBound433 (by decide +kernel)
namespace Free63

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem noRun : Impossible (graphGoal 2111) 7 (vars 2111).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=2111) (32,0,2079,0,7) _ (before_sound _ sound433) (by decide +kernel))
    [] (pool:=(vars (poolMask 2111 (32,0,2079,0,7)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Free63

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound63 : Lower (vars 2111) (graphGoal 2111) 8 :=
  augmentedGraph (k:=7) (m:=63) (hints:=8452) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (before_sound _ valid383 63) (by decide +kernel) (by decide +kernel) Free63.noRun

def entries63 := extendKnown entries433 8 [(2111,[])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound63 : Known entries63 := extendKnown_ok sound433 seededBound63 (by decide +kernel)
namespace Free95

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem noRun : Impossible (graphGoal 2143) 7 (vars 2143).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=2143) (64,0,2079,0,7) _ (before_sound _ sound63) (by decide +kernel))
    [] (pool:=(vars (poolMask 2143 (64,0,2079,0,7)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Free95

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound95 : Lower (vars 2143) (graphGoal 2143) 8 :=
  augmentedGraph (k:=7) (m:=95) (hints:=16785668) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (before_sound _ valid383 95) (by decide +kernel) (by decide +kernel) Free95.noRun

def entries95 := extendKnown entries63 8 [(2143,[]),(2365,[130,114,49,98,81,64]),(2489,[98,134,114,81])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound95 : Known entries95 := extendKnown_ok sound63 seededBound95 (by decide +kernel)
namespace Free119

theorem noRun : Impossible (graphGoal 2167) 5 (vars 2167).toFinset := countImpossible (by decide +kernel)

end Free119

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound119 : Lower (vars 2167) (graphGoal 2167) 6 :=
  augmentedGraph (k:=5) (m:=119) (hints:=16777476) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (before_sound _ valid383 119) (by decide +kernel) (by decide +kernel) Free119.noRun

def entries119 := extendKnown entries95 6 [(2167,[])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound119 : Known entries119 := extendKnown_ok sound95 seededBound119 (by decide +kernel)
namespace Free159

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem noRun : Impossible (graphGoal 2207) 7 (vars 2207).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=2207) (128,0,2079,0,7) _ (before_sound _ sound119) (by decide +kernel))
    [] (pool:=(vars (poolMask 2207 (128,0,2079,0,7)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Free159

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound159 : Lower (vars 2207) (graphGoal 2207) 8 :=
  augmentedGraph (k:=7) (m:=159) (hints:=536879364) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (before_sound _ valid383 159) (by decide +kernel) (by decide +kernel) Free159.noRun

def entries159 := extendKnown entries119 8 [(2207,[]),(2425,[130,114,49,98,81,64])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound159 : Known entries159 := extendKnown_ok sound119 seededBound159 (by decide +kernel)
namespace Free183

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem noRun : Impossible (graphGoal 2231) 7 (vars 2231).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=2231) (16,0,167,0,7) _ (before_sound _ sound159) (by decide +kernel))
    [] (pool:=(vars (poolMask 2231 (16,0,167,0,7)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Free183

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound183 : Lower (vars 2231) (graphGoal 2231) 8 :=
  augmentedGraph (k:=7) (m:=183) (hints:=536871172) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (before_sound _ valid383 183) (by decide +kernel) (by decide +kernel) Free183.noRun

def entries183 := extendKnown entries159 8 [(2231,[]),(2419,[135,98,50])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound183 : Known entries183 := extendKnown_ok sound159 seededBound183 (by decide +kernel)
namespace Free187

def liveData6 (i : Nat) : Nat := 0x105fd30

def moveIndex6 (i : Nat) : Nat := 0xe0

def liveData5 (i : Nat) : Nat := 0x102f54c530

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

def orCols : IndexTree ColumnInfo := (.leaf [(10,0,2225,0,4),(16,8,163,0,4)])

def orForest : Forest := ⟨2235,6,fun j => orSamples[j]?.getD (0,0),orCols,orSymmetries,liveLevels,liveIndex⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem orGeometry : graphValid orForest (boundsBefore entries183) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked6At0 : block orForest 6 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked5At0 : block orForest 5 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

theorem allAt6 : block orForest 6 0 1 = true := checked6At0
theorem allAt5 : block orForest 5 0 1 = true := checked5At0
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

theorem noRun : Impossible (graphGoal 2235) 6 (vars 2235).toFinset :=
  root_index (g:=orForest) (before_sound _ sound183) orGeometry orTables
    (k:=6) (by decide) (i:=0) (by decide +kernel)

end Free187

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound187 : Lower (vars 2235) (graphGoal 2235) 7 :=
  augmentedGraph (k:=6) (m:=187) (hints:=1342193668) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (before_sound _ valid383 187) (by decide +kernel) (by decide +kernel) Free187.noRun

def entries187 := extendKnown entries183 7 [(2235,[])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound187 : Known entries187 := extendKnown_ok sound183 seededBound187 (by decide +kernel)
namespace Free189

def liveData7 (i : Nat) : Nat := 0x83fd30

def moveIndex7 (i : Nat) : Nat := 0xd16f801819ec827900

def liveData6 (i : Nat) : Nat := 0x2100c920bf58930bf58530fe48130

def liveLevels : Nat → Packing
  | 7 => (1,1,2,0,0,0,0,liveData7)
  | 6 => (3,2,2,0,0,5,0,liveData6)
  | _ => emptyPacking

def liveIndex : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 3 8 3 9 2 3 moveIndex7
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

def orCols : IndexTree ColumnInfo := (.leaf [(8,0,2229,0,5),(12,0,2225,0,4),(17,0,172,0,4)])

def orForest : Forest := ⟨2237,7,fun j => orSamples[j]?.getD (0,0),orCols,orSymmetries,liveLevels,liveIndex⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem orGeometry : graphValid orForest (boundsBefore entries187) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked7At0 : block orForest 7 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked6At0 : block orForest 6 0 3 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

theorem allAt7 : block orForest 7 0 1 = true := checked7At0
theorem allAt6 : block orForest 6 0 3 = true := checked6At0
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

theorem noRun : Impossible (graphGoal 2237) 7 (vars 2237).toFinset :=
  root_index (g:=orForest) (before_sound _ sound187) orGeometry orTables
    (k:=7) (by decide) (i:=0) (by decide +kernel)

end Free189

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound189 : Lower (vars 2237) (graphGoal 2237) 8 :=
  augmentedGraph (k:=7) (m:=189) (hints:=536879876) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (before_sound _ valid383 189) (by decide +kernel) (by decide +kernel) Free189.noRun

def entries189 := extendKnown entries187 8 [(2237,[]),(2395,[135,98,82,33,49,64])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound189 : Known entries189 := extendKnown_ok sound187 seededBound189 (by decide +kernel)
namespace Free215

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem noRun : Impossible (graphGoal 2263) 6 (vars 2263).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=2263) (0,16,198,1,5) _ (before_sound _ sound189) (by decide +kernel))
    [] (pool:=(vars (poolMask 2263 (0,16,198,1,5)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Free215

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound215 : Lower (vars 2263) (graphGoal 2263) 7 :=
  augmentedGraph (k:=6) (m:=215) (hints:=553648388) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (before_sound _ valid383 215) (by decide +kernel) (by decide +kernel) Free215.noRun

def entries215 := extendKnown entries189 7 [(2263,[]),(2397,[130,114,98,49,64]),(2461,[134,49,64]),(2485,[134,81,114,49]),(2545,[118,33,129,82,49])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound215 : Known entries215 := extendKnown_ok sound189 seededBound215 (by decide +kernel)
namespace Free243

def liveData6 (i : Nat) : Nat := 0x1fd20

def liveLevels : Nat → Packing
  | 6 => (1,1,0,0,0,0,0,liveData6)
  | _ => emptyPacking

def liveIndex : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none

def orSamples : Array (Bits × Bits) := #[(0xfffe00007fff800007ff80000ffff00000fffe00003fffffffe00000ffff00003ffff800007fffc0000fffff000003fffffffffffffffff00003ffffffff00000fffffffffc00001fffffffff000003fffffffffffffffffffffffffffffffff,0x42208000221021080224210804422421004242840010844844484202440104001108121001424090802422024210090809088090a024201008012202920240402508090880900804908091102421008440521014880908804888090840244202),
  (0xffffffff8000000007fffffff000000000ffffffffc0001fffffffffffffffffc0000000007ffffffff00000000003fffc00003ffffffffffffc0000fffffffff00003fffffffffe00003fffffffffffffe00007fffc00001ffffc00000fffff,0x1416282a88040a02a0c38a03608001405214142816850002818280d428aa282a840540a054142b05154140a414055051d05025050d420aa282a800a820ac1815400290502d0502a800250606c14055282a880aa302b0502a85055050154280d4),
  (0x0,0x0),
  (0x0,0x0),
  (0xfffffffffffffffff80000000000000000ffffffffffffe000000000ffffffffffffffffff80000000000000000003ffffffffc0000fffffffffffff00000000000003ffffffffffffffc0000000003ffffffff8000000001ffffffffff00000,0x995b32b34ca6cc5334924c524914898a649899315b26299309131498b1ccb173265664c566183226198988c898a6626362633626098b4ccb533254cc08c892998853226536265331253624a4898a6632b30cacc22322623316366262998b1498),
  (0xffffffffffffffffffffffffffffffffff0000000000000000000000fffffffffffffffffffffffffffffffffffffc0000000000000ffffffffffffffffffffffffffc0000000000000000000000003fffffffffffffffffe000000000000000,0x19c033c00c70063c01b00638018c00c780000019c003100100018e001f001bc006780067800bc003e000cf000c78001800238000e018f0063c018f00cf0031e0063c006380063c0063800c7000c78033c00cf0033c0033c002780031e0018e0),
  (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000fffffffffffffffffffffffffffffffffffffffffffffffffffc000000000000000000000000000000000,0xe1e1c3c070f8707c071c707c0e1f0e0f80e0e1c1e0383e1c1e1c1f00c100c1c0387807078060c038200e0f00e0f803820383c038300df00c7c039f00cf00e3e00e7c0387c0387c01c7c038f80e0f8003c010f0043c0383c018380383e00c1f00),
  (0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0xfe01fc007f007f8007e07f800fe00ff000ff01fe003fc01fe01fe000fe00fe003f8007f8007f003fc00ff000ff0003fc03fc003fc00e000f8003e000f000fc000f8003f8003f8001f8003f000ff0003c001f0007c003fc001fc003fc000fe000),
  (0x0,0x0)]

def orSymmetries : Array (List Nat) := #[[],[81,118]]

def orCols : IndexTree ColumnInfo := (.leaf [])

def orForest : Forest := ⟨2291,6,fun j => orSamples[j]?.getD (0,0),orCols,orSymmetries,liveLevels,liveIndex⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem orGeometry : graphValid orForest (boundsBefore entries215) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked6At0 : block orForest 6 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

theorem allAt6 : block orForest 6 0 1 = true := checked6At0
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

theorem noRun : Impossible (graphGoal 2291) 6 (vars 2291).toFinset :=
  root_index (g:=orForest) (before_sound _ sound215) orGeometry orTables
    (k:=6) (by decide) (i:=0) (by decide +kernel)

end Free243

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound243 : Lower (vars 2291) (graphGoal 2291) 7 :=
  augmentedGraph (k:=6) (m:=243) (hints:=1358954500) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (before_sound _ valid383 243) (by decide +kernel) (by decide +kernel) Free243.noRun

def entries243 := extendKnown entries215 7 [(2291,[])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound243 : Known entries243 := extendKnown_ok sound215 seededBound243 (by decide +kernel)
namespace Free127

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem noRun : Impossible (graphGoal 2175) 8 (vars 2175).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=2175) (32,0,2143,0,8) _ (before_sound _ sound243) (by decide +kernel))
    [] (pool:=(vars (poolMask 2175 (32,0,2143,0,8)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Free127

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound127 : Lower (vars 2175) (graphGoal 2175) 9 :=
  augmentedGraph (k:=8) (m:=127) (hints:=16785668) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (before_sound _ valid383 127) (by decide +kernel) (by decide +kernel) Free127.noRun

def entries127 := extendKnown entries243 9 [(2175,[])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound127 : Known entries127 := extendKnown_ok sound243 seededBound127 (by decide +kernel)
namespace Free191

def liveData10 (i : Nat) : Nat := 0x24508ffd40

def moveIndex10 (i : Nat) : Nat := 0x12b03e000017680069749a9f1873ec6edf06e77428e12ac5e4408fc19418ef6000e062e75b9a2f64c00588e130a0044b4d095884b28a00103000005d2ac292aef03d56100783205a4200016100063180a1

def liveData9 (i : Nat) : Nat := 0xb0d122010ec09087940a04843c8043b0242245020b81211228289878c4c7c08520448844501e320502281c2242805020181a10f30e810709906a143c783884c2f0b02481e1c427110281a11228788048750889874142452843808e021c1e30e1c02911d1201214070c010bc8808910a004384861e2004121d42022280e01a1091228586010ec0c8909c2c300a064484c2622243850201810ca11138709082c04386160442001c24600020191a1120e382810ec089109a0644846052302244258191211888040891096068400448042302254228681a111180828140d08918202c1c903808c0302054322505020e01a11230880075080891a864404622002811214a111280c0d08048960c6011f7dec9e15da1c8db79aa5a1193d8497956c15cd5594453312bd1a90f5000f2ceb8dc4d70cfcc28b34a609ec9388c481077c6a863456048c3d83042301bc1680b4003ff3ba81ff5d940ffaeaa07fd64503feaa281ff5cd40ffac6a07fd53503feb9281ff1c940ffac4a07fd52503fea1281ff4c940ffc44a07fd71503feb0a81ff54540ffa82a07fd31503fe90a81ff58140ffaa0a07fd30503fe90281ff08140ffa20a07fe00502ff3ba817f5d940dfccca05fd75503bf2aa81ef55140f7c88a05fd73503ef19a817f5c940bf8e4a07ee22502feb8a81ef50540fec22a07bc40503fc98281fe80140

def moveIndex9 (i : Nat) : Nat := 0x2447205d11fd61e9462c0e4922ba30745d98ada0c6c2944087850604d540543a78da2037a0d685b78ed203962fc48c389dc09063cb428f0120202000205cc01fc003135a81484e0ca076036c21c0cc80e4032a811fd02c08c6138832591060cd23e5c4570dee0b1044f805b904000000944750000c1e0836c00078d362168171c40587e7001c386864a02d00000003047e0c3614d6110004890900010438000707f0dd880c902ca01ae0b4000244220af11a24101c44000000002055c7c306180abc25c078f0d9412041e547408a0b135412e065f0cf022ea15c43da85ea1044080c1a409e900c4062883c86f0000e0a988400a190d0000205720132139e30004c28520000e4588428000e12a224fc8cc83b50c000034739814217982e2c3c286cd062a1db85d28fad1ece38a022e807014e7adb05f58d49547237e434d112f02e62dc017906d118da128848c01d2049820582168b200be9c3340500006099e3cf46ed05b00000002e5880990001633607a184d507c40bac20e8a200000003c64509bb204c1d686270870001c15a87060aad112000000020b1c149804441ed82bc01ec03145a210090fa834a86e003a00000000c29910c9146838e8328073a1ea215303768eb104f20e506b8000000001c4c72b8869228044587e5ac6506f61f04140000715142cf43810ace12de429811000081aca00b87712c9a15722d6881d0d09107627cc61782c51d30125280204fc08ea1dcc04289201b0439bc54d8ff818ea43dc77800040d5a0cf85e9003806ca3f4c0738b0e116e339402c0ec41294086c83401ea008e3eec86d08c91efe23680c906b20798ad1c18010590c5c35701fc016c0ce1b6d41c0c08040803028a891800902680c0033e05d87362d00400b4e2b800414f6e003838c0150150008031050002000afa0d2107805e09b835a3421202c40872c090820038507004c00302100015c08200000401a1a184010200d82

def liveData8 (i : Nat) : Nat := (if i < 1 then 0xd7158140efd6158140fbd4158140dfe7754140dfd7354140dfc7254140fbd4154140ff9624c140ff9524c140ff9614c140ff9514c140ff9214c140bfd864c140bfd854c140fdd634c140fdd534c140fdd314c140ff9604c140ff9504c140bfe8848140dfc8748140dfe7748140bfd8648140dfd7648140bfd8548140dfd7548140fbd5448140bfd8348140dfd7348140dfd7248140fed5248140ff48148140dfd7148140fbd4148140fed2148140ff96048140ff93048140bfd8608140bfd8508140bfd8644140dfd7644140bfd8544140dfd7544140fbd5444140bfd8344140dfd7344140bfd8244140dfd7244140ff55144140ff93044140ff920441409fd869dd409fd859dd40dbd849dd409fd839dd409fd829dd409fd819dd409fe885d940cfe77999409fe885d540d7e7795540bf88059140bbe8855140dbe7755140fb88055140bf88055140dbe7791140dbd7691140ebe6691140dbd7591140f3e55911409fe885cd40cfe665cd40d7e555cd409fd8758d409fc8758d40cfd7658d409fd8754d409fc8754d40f3d5454d40dde778cd40ddd768cd40ede668cd40ddd758cd40f5e558cd40f9d548cd409fe885c940cfe665c940d7e555c940dbd545c940dbe445c940ddc835c940dde335c940df4815c9409fd861c940cfe661c9409fd851c940d7e551c940dbe441c9409fd831c940dde331c9409fd811c940ded721c9409fd87589409fc87589409fd87549409fc8754940f3d54549409fc8750940dec7250940bf880509409fd874c9409fc874c940dec8788940dee7788940ded7688940eee6688940ded7588940f6e5588940fad5488940fae4488940ded7388940fce33889409fc8788940ded72889409fe885c540cfe665c540d7e555c540dbe445c540dde335c540dee225c5409fd87585409fc87585409fd87545409fc8754540bbe8850540dbe7750540ebe6650540bbd8550540f3e5550540f9e3350540dbd7250540fae2250540fb56150540fb88050540bf880505409fd874c5409fc874c540fb5414c5409fd87485409fc8748540df67784540df57684540ef66684540df57584540f765584540fb55484540fb64484540df57384540fd63384540df57284540df47284540fe62284540f3d5454140dbe7710140ebe6610140bbd8510140f3e5510140dbd7210140fae2210140bbd8110140fb61110140bfa884c140dfa774c140efa664c140f7a554c140fb9544c140fd9634c140fd9534c140df9724c140fea224c140fb9414c140fd9314c140ff2114c1409fd8748140dec7248140fb54144140dfa7780140df97680140efa6680140df97580140f7a5580140fb95480140fba4480140bf98380140df97380140fda3380140df97280140df87280140fea2280140df97180140fb94180140ff21180140b3d8510140bb58110140 else (if i < 2 then 0x23050384010804201080420108580a24188c261e07103c0f1000262318042010c0420080888244808602108c042438086228200a848000840e20d0541a0920040c1181048a051083c6150f03412407054210058204b0400508202851008200005c4212200000044200000a102860a1828422a1090c1e05508508960a080a14090e0a108a0424302a0428382840a011183c800700024306054210058204b040050814200621502301040010a042008800411000af31781bb55d4ee79725b7e5b4ed796aeb4bda4acf7664b26d8b6c2d5f6aefd6feb51588ab8d546a75523a8653fa9e14d9a61528a917474a2ed11a84d40f9fc4f867833aa9c54daa6a7345992cc165dd2d795bca164cb24e91bc85e3ef1e08e046a63371848b6c53625b11688443c61b50c385642320eb05e82840e603300b7fa3f75f8cfb87d0be4def8f5c7a2bc71e0aeee76bbb01d64e9273db991c9ae3f7143821bbedbf6cfb5d9abed486943445a06cec66ab31d960c99645b1d18a8c3d6133061802bea5ee2f1574ab975c02da5692b2958dac115daacd55b2aa1522a8353f29c14c4a5d52c2929478a37514a89141a9ff4f8a7453629884b8a569286935493a48922890f480a36117089843c218508282a4099ff0fdc7d73e49eecf487963b69da0e7e71f37b1b58d6c69f34d1a54cea64c31f18c0c4461d3079828bf85f72f49790b645922bd95b4abe5512a194d4a2a4ec26a92d494e49924591888a844621310607de3ea1f28f3874a3731a98ca863830e1848bec5ec2e81718b545a02b91558a984fa27813989b84d225b12b094449823e11808884281f40e586d03281860b3051827010f08503a81b80ce06482ec16c0a8051825410e082031015009e04101980b802e000dfc825d540fbc8255140bfe8858d40dfe7758d40bfe8854d40dfe7754d40dfd635c940dfd535c940dfd541c940bfd861c940bfd851c940dfd751c940fbd541c940dfe7758940dfd7358940efd6358940bfe8854940dfe7754940f7d5454940dfd7354940f7d5354940dfd7254940dfe774c940bfd854c940dfd754c940fdd634c940dfe7788940dfd7588940fbd5488940dfd635c540dfd535c540dfd525c540dfe225c540bfe8858540dfe7758540dfd7358540dfd7258540bfe8854540dfe7754540dfd7354540dfd7254540dfc7254540f7d5254540fbd6350540fbd5350540fbd6250540fbd5250540fbe2250540ff56150540bfe884c540dfe774c540bfd864c540dfd764c540bfd854c540dfd754c540fbd544c540dfd724c540fdd324c540ff5514c540bfe8848540dfd8748540dfe7748540bfd8648540dfd7648540bfd8548540dfd7548540fbd5448540bfd8348540dfd7348540dfd7248540ff56148540ff53148540bfe8858140dfe7758140dfd7358140efd6358140dfd7258140df else 0x2f16107c202078104190808260f103e021f0a101f010c8508020b893610ba58400685c40d05080e131068288518902e2054842a30588440709c846050a090a81908c260f10343617183c1020d87440205080414b041e1f103c1c2050394230103841c0d081c0a10103820ea143c30c05c40e050808131214141818082a2008842e307404223074045010a842f0118380682182c0220304040f0704c60d8280a0210283d42061834202078184960883c60f0a0246010488260f828c060d102420e0188341e10743ca1185c1a1b18280624b042009101c1228082441b0f080a14048c1622103642290844291121503211c842214089032110581a248842a02105c21482894214828e0a10104e0a0f08102905105a2220944441208882410983824382a844128888160a103820c07083416070c180250c0481b0b83860c01404696064042e40803850148892281808c2e96103820c07081881100421d4d8a0291126c20c4b08340b0b0c1818105c16280841c0c10492228084140b12141901183021248881d011014480e182c1222180020f0a084c0e10384a1318902428d8440121458200b042c10001415084016080261210142050858022418144c0e181442121210380710384c20788840f0a84200b0409608682a0d09113705808d2d05808c2296090e02911027420f183e022d083c41e12080411208840208082080a080410a8781c092000a160083c813128386050d8041e4098901c34888444306848400004460418682a0d049004105054210058204b040050803a150103826501215))

def moveIndex8 (i : Nat) : Nat := 0x888c7cc008c90868c00014200cc8360d901283e0148aa454000c914d64e2c414ae42b047cbe86f88c00000349600f43b8ddc708d14760e4c534258b044c083cec00541e464cbb8ea44845a87a41a8326cb4a28a5c0b4b400382c003c9b461c6805c0c400000289f23802500591440c13c4181153080489

def liveData7 (i : Nat) : Nat := 0xa10142000091484400001b0802108c171002888a010820184502040800812201029089112844088202042208081103c409c0a078d052844002420004200000000004081e10000a080000022100000002210001208220a0243b56d0b2ebcab6a8a8e9ea16809ee7699e588fe2685e12795cc71dae6557c5dd5e51522425043d4f0384dc35cd2334c830cbe2bca026c9621c821f4781cc6417c5a1545012c3c0dc3208c008fec8d10bb2811fd92a21755023fb23442eaa047f6488758d408fec910ea9a811fd91a21725025fb2d442a4a055f25d5354940e9eaa2e4a92819dc8758d325023f930bac44a066f21d5488940afac8ceeb0a811fd9221d515032f90ea92a2a076d5c96150540f5ab12c2a0a819bc875513150376b0ca0a62a07e54c9414c5409becad10b0281eb56150560503e72a8a9260a07e658d414c140fcca9a8298281fb16150530503f32a898a60a07f4545314c140f6cb1ac0982813f591a21205033eb0e40a40a06ed6194144140fd8a0a408828117d95a21765027b326402c8a05e664c80551409ecc9900aa2811bd94a21735023bb27442e4a047d646885c9408ee4c466b92819d48320572502f332640282a04f664c80505408fa4c2e508a811bd989dc4050267d32c2880a064f9dd8510140d1f3330a2028193d855c84050365b0b11080a04eda658110140cdb3bb0220281ab6666044050366caac0880a066d5c98110140dd31130220281b358584440503e32a8a9a60a07e4505314c140

def liveLevels : Nat → Packing
  | 10 => (1,1,6,0,0,0,0,liveData10)
  | 9 => (46,2,6,0,0,12,0,liveData9)
  | 8 => (282,3,6,0,0,13,0,liveData8)
  | 7 => (60,4,6,0,0,10,0,liveData7)
  | _ => emptyPacking

def liveIndex : Nat → Nat → Option (Nat × Nat)
  | 10 => lookupWord 19 55 5 10 6 0 moveIndex10
  | 9 => lookupWord 101 329 7 15 9 2 moveIndex9
  | 8 => lookupWord 21 69 6 12 6 2 moveIndex8
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

def orCols : IndexTree ColumnInfo := (.fork 19 (.fork 9 (.fork 4 (.leaf [(1,0,190,0,7),(2,0,2237,0,8),(4,0,2235,0,7),(6,0,2233,0,5)]) (.fork 2 (.leaf [(0,8,163,20,6),(8,0,2231,0,8)]) (.leaf [(10,0,2229,0,5),(4,8,163,16,5),(12,0,2227,0,5)]))) (.fork 5 (.fork 2 (.leaf [(14,0,2225,0,4),(0,16,166,9,6)]) (.leaf [(16,0,175,0,8),(1,16,166,8,5),(17,0,174,0,5)])) (.fork 2 (.leaf [(19,0,172,0,4),(8,16,166,1,5)]) (.leaf [(16,8,163,4,5),(24,0,167,0,7),(9,16,166,0,4)])))) (.fork 10 (.fork 5 (.fork 2 (.leaf [(25,0,166,0,4),(20,8,163,0,4)]) (.leaf [(0,32,30,129,6),(32,0,2207,0,8),(1,32,30,128,5)])) (.fork 2 (.leaf [(35,0,156,0,4),(40,0,2199,0,5)]) (.leaf [(0,128,2075,36,6),(128,0,2111,0,8),(130,0,2109,0,5)]))) (.fork 5 (.fork 2 (.leaf [(4,128,2075,32,5),(134,0,2105,0,4)]) (.leaf [(136,0,2103,0,5),(128,32,30,1,5),(160,0,2079,0,7)])) (.fork 2 (.leaf [(129,32,30,0,4),(162,0,2077,0,4)]) (.leaf [(36,128,2075,0,4),(164,0,2075,0,4),(168,0,2071,0,4)])))))

def orForest : Forest := ⟨2239,10,fun j => orSamples[j]?.getD (0,0),orCols,orSymmetries,liveLevels,liveIndex⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem orGeometry : graphValid orForest (boundsBefore entries127) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked10At0 : block orForest 10 0 1 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked9At0 : block orForest 9 0 18 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked9At18 : block orForest 9 18 28 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked8At0 : block orForest 8 0 2 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked8At2 : block orForest 8 2 56 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked8At58 : block orForest 8 58 56 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked8At114 : block orForest 8 114 40 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked8At154 : block orForest 8 154 56 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked8At210 : block orForest 8 210 56 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked8At266 : block orForest 8 266 16 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked7At0 : block orForest 7 0 27 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked7At27 : block orForest 7 27 33 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

theorem allAt10 : block orForest 10 0 1 = true := checked10At0
theorem allAt9 : block orForest 9 0 46 = true := (@block_merge orForest 9 0 18 28 checked9At0 checked9At18)
theorem allAt8 : block orForest 8 0 282 = true := (@block_merge orForest 8 0 114 168 (@block_merge orForest 8 0 2 112 checked8At0 (@block_merge orForest 8 2 56 56 checked8At2 checked8At58)) (@block_merge orForest 8 114 96 72 (@block_merge orForest 8 114 40 56 checked8At114 checked8At154) (@block_merge orForest 8 210 56 16 checked8At210 checked8At266)))
theorem allAt7 : block orForest 7 0 60 = true := (@block_merge orForest 7 0 27 33 checked7At0 checked7At27)
theorem orTables : checkedTables orForest 10 := by
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
  · exact allAt8
  · exact allAt9
  · exact allAt10

theorem noRun : Impossible (graphGoal 2239) 10 (vars 2239).toFinset :=
  root_index (g:=orForest) (before_sound _ sound127) orGeometry orTables
    (k:=10) (by decide) (i:=0) (by decide +kernel)

end Free191

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound191 : Lower (vars 2239) (graphGoal 2239) 11 :=
  augmentedGraph (k:=10) (m:=191) (hints:=536879364) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (before_sound _ valid383 191) (by decide +kernel) (by decide +kernel) Free191.noRun

def entries191 := extendKnown entries127 11 [(2239,[]),(2427,[130,114,98,81])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound191 : Known entries191 := extendKnown_ok sound127 seededBound191 (by decide +kernel)
namespace Free223

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem noRun : Impossible (graphGoal 2271) 8 (vars 2271).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=2271) (64,0,2207,0,8) _ (before_sound _ sound191) (by decide +kernel))
    [] (pool:=(vars (poolMask 2271 (64,0,2207,0,8)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Free223

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound223 : Lower (vars 2271) (graphGoal 2271) 9 :=
  augmentedGraph (k:=8) (m:=223) (hints:=553656580) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (before_sound _ valid383 223) (by decide +kernel) (by decide +kernel) Free223.noRun

def entries223 := extendKnown entries191 9 [(2271,[]),(2429,[130,114,49,98,81,64]),(2463,[134,49,64]),(2553,[118,130,81])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound223 : Known entries223 := extendKnown_ok sound191 seededBound223 (by decide +kernel)
namespace Free247

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem noRun : Impossible (graphGoal 2295) 8 (vars 2295).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=2295) (16,0,231,0,8) _ (before_sound _ sound223) (by decide +kernel))
    [] (pool:=(vars (poolMask 2295 (16,0,231,0,8)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Free247

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound247 : Lower (vars 2295) (graphGoal 2295) 9 :=
  augmentedGraph (k:=8) (m:=247) (hints:=553648388) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (before_sound _ valid383 247) (by decide +kernel) (by decide +kernel) Free247.noRun

def entries247 := extendKnown entries223 9 [(2295,[]),(2423,[135,98]),(2547,[118,130,50,81])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound247 : Known entries247 := extendKnown_ok sound223 seededBound247 (by decide +kernel)
namespace Free251

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem noRun : Impossible (graphGoal 2299) 7 (vars 2299).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=2299) (8,0,2291,0,7) _ (before_sound _ sound247) (by decide +kernel))
    [] (pool:=(vars (poolMask 2299 (8,0,2291,0,7)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Free251

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound251 : Lower (vars 2299) (graphGoal 2299) 8 :=
  augmentedGraph (k:=7) (m:=251) (hints:=1358970884) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (before_sound _ valid383 251) (by decide +kernel) (by decide +kernel) Free251.noRun

def entries251 := extendKnown entries247 8 [(2299,[])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound251 : Known entries251 := extendKnown_ok sound247 seededBound251 (by decide +kernel)
namespace Free319

def liveData10 (i : Nat) : Nat := 0x7040bfd40

def moveIndex10 (i : Nat) : Nat := 0xd1c00064487d11659cf212d4546c002d7912742aa6136145604051831841411e9dfaa83d10bd900000a8a447889e5ec82a0000170c21033330058590dc398180059f58b1692319100185627b1a08700046200d9d61

def liveData9 (i : Nat) : Nat := 0x9c881ce00440c92722042e16013910500199c8820b8005ce44145c02227030a173810316000b1c08285804e041034002e7020b381021500171c0828900018e0414000e70208060019381051119041d090034e44088474302400a17381039c0810801ce4400140802722080539100049c881000e44108c86180a7220617381039c08101ce040c000e702093810200087067220405380110494f20a36c40836fb9e0ba46eed4992b105c6ad948a6445e868f69d0376638b494425e3e86e8c01562383485408e0e812800ffceea07fe44503feb9a81ff1cd40ffa86a07fc43503ff19a81ff5c940ffac4a07fd42503fe99281ff5c540ffac2a07fd51503fea0a81ff4c540ff880a07fd30503fe18281ff48140ffa20a07fe00502ff3ba81ef91140bfae6a05fc73503ef19a817f5c940fdc44a05fd71503dea0a81fd84540f7880a07f840503fc98281fe80140

def moveIndex9 (i : Nat) : Nat := (if i < 1 then 0xbe1ae21e4c112315e48bc2641938068848dc140981e15c5172e36a415f90dc609eca642a2a9c216f25ae81f3086b59345284635a746022429404de8715404456e46a502d54e725844439967d91fa5c782640fbb2bf6011c09eb6e35980ae7d7524c040db8bdcc15705a7233810449ffd0606590c6305ab0af92a34cba48282a6a25b401d4581063a1fee0c18b82891256f11240725862019388e007f089784824497146c85df67f499bc51890c4211693ee5de0940000c32000030180000e38800008beeab422032791319119ec4ec0006910415260cdc000a2c89cd4a920a218ee967c058ad2b223dc14883438b4306f1c7f024c8a76940e254ea8b8108aa8619b650b00458dc852f43d9934491a509702f6b8e80002087a941807821b61cea0d9d28a2acd264a2fd4b6c8260001a00800072ae41f200034550000f1cc09008085a29a1d92c350220000f141e4dd4b298b2f5e545b249191020000296b8440000a157456101c0000509a000186fd12ef22403d0c2f800000006330000189f00014a9487818d3000000019af8136803563f43ad5649a693e00588b68733230000cdb3629ef18982e9802fa9340f4eac6d713122607200028a1d2374de10444d7cf2a921daca8207982c8308f2419c29633b762062380a9a11f00786bbd850d03fe1cacb19860dae7e94c21ac804fadc820f4402c072a60f1d50871c411a4c30532226d7f43502411abec0007a6135db037a23a8000edcd4d2f4b5186c40b7a2d21a8916e0000000003a38ce0000e08f102421a987e0002d1f08d6e2720000000589ed0f60003d7f8000e01b090c00000000000ca68000394730ab80eb88e10a6a0adda9999b613a5090cd2a470c1411504c32985c615641d1055e45db12c963963c61178077c1ba2065870422ed24dc15e52bd824d1f9a3d416cf84f018f011982778b6d2bc00714538858163d80c987d4a9f518a02b9c3760dba0ce0214ca7c14be50e0d2095d60157186c8db11cc104d2dec0df424cacf70c3445249eda5c1062e42400060eb45f5416408f24f000018c080005320f6ceac52451195a710800000000000d1aae12952ceace000069e4c7bf898b05ea0a1d4c80350001c38c000294d213b22a1c1050f2921501dac3e5205621eabd017e9a7aa270e97919cc16912c84077524c80ac04a0002890b149f0e433794aa8896c0fd2935162f934d3f850840014374634187a06c00404a400a004c888000423f0460882029402b309cc80108c0070c2412d001240704107816228b8534204064200305574801d0a0038248781160428409021d2b000a993a082801a000528a0040f84400000a62040000a240011400904320cea52e180090a140000275d0f001410a000080a1e48e8010381840208600227c2980a001800418405020df8712041811c000010c5c080 else 0x892e6ac8016189a65e0c540889993315d260f4847d2e6b1f0eb6b058d95908166d6a09f784061b0cd7ad758000c28c61145b680000000245f89880000001e0bb0b1d8d9e5ece3458b35095e03f25170a9710bf2402b6c82e511bd084c1a600a714c2077b474c9e5012ea9c0000c818128a47f6574916b8e9b036418040b9697e601a1e1d0eb881b25e000140340ad5636e22c828891d42610a5b1226929f5e362b318ed935d556081b82f488c8179e32dc0f592b00012a22d726323552aa1d644e308d40cd6302c1a52b80124614e4482321c04ec49f83866f214ba481f96539480000000000018c20624cc9589270ef9596c1ff832108a31a408ab859e06a1433e05a841c960f21d2454c063101a2a9e1f6432c00)

def liveData8 (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0x9424c140ff9324c140ff9814c140ff9714c140ff9614c140ff9514c140ff9414c140ff9314c140bfe884c140bfc874c140dfc874c140dfe774c140bfd844c140bfc844c140fbc844c140dfd734c140dfc734c140fdd434c140dfd724c140dfd714c140fbd414c140fdd314c140ff8404c140dfe770c140bfd840c140dfd730c140bfd820c140bfd810c140ff9300c140bfe8848140dfe7748140bfd8648140dfd7648140dfd7548140bfc8448140fbd5448140bfd8348140bfc8348140dfd7348140fed6248140fed5248140fed4248140ff93048140bfe8844140dfe7744140bfd8644140dfd7644140bfd8544140dfd7544140bfc8444140fbd5444140bfd8344140bfc8344140dfd7344140dfc7344140ff55144140ff54144140ff93044140dfe7780140bfc8480140bfc8380140dfd7380140dfc7380140dfd7280140ff93080140dbd849dd409fd839dd409fc839dd409fd829dd409fd819dd409fd809dd40df9809dd40dbc8791140dbe7791140bbd8191140fb98091140bf980911409fe885cd40dbe445cd409fe881cd409fc841cd40dbe441cd409fd821cd409fd811cd40df9801cd40ddd731cd409fc8750d40bf88050d40bed8210d40bf58110d40ddd878cd40ddc878cd40dde778cd40f9e448cd40fd8808cd409fd878cd409fc878cd40ddc738cd40bf8808cd409fe885c940dbe445c9409fc835c940dde335c9409fd87589409fc8758940bf880509409fc874c940dee7788940ded7688940eee6688940fae4488940dec7388940fce33889409fe885c540cfe665c540dbe445c5409fc835c540dde335c5409fd87585409fc87585409fd87545409fc8754540bbe8850540dbe7750540dbd7650540ebe6650540bbd8550540dbc7350540f9e3350540fb88050540bf880505409fd874c5409fc874c540fb5414c540df67784540df57684540ef66684540df57584540f765584540fb55484540fb64484540df57384540df47384540fd63384540dbe7710140dbc7310140f9e3310140dbd7210140fae2210140bbd8110140fb61110140bfa8810140dfa7710140fba4410140bf98310140fd98310140fda3310140fe98210140fea2210140ff18110140ff21110140bdd8310140bed8210140bf58110140bfa884c140bf8874c140df8874c140dfa774c140bf8844c140fb8844c140fba444c140df8734c140fd8734c140fd9434c140fda334c140df9724c140fea224c140fb9414c140fd9314c140ff2114c1409fd874c1409fc874c140bbc844c140ddc734c140fd9300c140bbc8448140bbc8444140fb54144140df88780140dfa7780140bf88480140fba4480140bf98380140df97380140df87380140fda3380140df97280140fea2280140df97180140fb94180140ff211801409fc8780140bb58110140bd983101409f8874c140 else 0x1bc8be45ca21d10485941820410167fd3fc1fa8f8277d3b79cf4e287063731b60d7069834999a8cb864e3249910c6c63130417e8bd85cc2df1678afc5672a394e4a5650b27e937499e4c125e12dc92e46e227110086442d20f90688184071fc8fac7cc3e11ee0f5c7a43cd1e40f0c77c3b91da0ebc7543a51d00e6c72c3911af8cd86082f61620a48508276138898c4bc25912a091847022a10988143ee1c50c0853c2941450a004c823610d07f83c41d80de068030817a0af055027011c08902b8124076000dfd849dd40dfd839dd40dfc839dd40dfd829dd40dfd819dd40dfd809dd40dfd409dd40fbd849dd40bfd839dd40bfc839dd40bfd829dd40bfd819dd40ff9809dd40fbe8891140dfc8791140dfe7791140bfd8391140bfc8391140bfd8291140bfd8191140bfd8091140dfe885cd40dfe445cd40dfd815cd40bfe885cd40dfe775cd40dfd801cd40dfd401cd40bfe881cd40dfe771cd40bfc841cd40dfd731cd40bfd821cd40bfd811cd40ff9801cd40dfe7750d40bfe8810d40dfe7710d40bfd8210d40fed8210d40bfd8110d40ff58110d40ff98010d40fde888cd40bfd878cd40bfc878cd40dfc878cd40dfe778cd40bfd848cd40bfc848cd40bfd828cd40bfd818cd40bfd808cd40ff8808cd40dfe445c940bfe885c940dfe775c940dfd765c940bfc835c940dfd735c940bfe8858940bfd8758940bfc8758940dfe7758940bfc8458940bfc8358940bfe8850940dfe7750940bfd8650940dfd7650940bfc8350940bfe884c940bfd874c940bfc874c940dfe774c940bfd864c940dfd764c940bfc844c940fed624c940fed424c940dfd645c540dfe445c540dfc835c540dfd635c540dfd435c540dfc435c540dfe335c540bfe885c540dfe775c540dfd765c540dfd755c540bfc835c540dfd735c540dfc735c540bfe8858540bfd8758540bfc8758540dfe7758540bfc8458540bfc8358540dfd7358540bfe8854540bfd8754540bfc8754540dfe7754540bfc8454540bfc8354540dfd7354540dfc7354540fbe7750540fbd7650540fbd7550540fbc8350540fbd7350540fbc7350540fbd6350540fbe3350540bfe8850540dfe7750540bfd8650540dfd7650540bfd8550540dfd7550540fbd6450540fbd5450540fbe4450540bfc8350540dfd7350540dfc7350540fbd4350540fbc4350540bfe884c540bfd874c540bfc874c540dfe774c540bfd864c540dfd764c540bfd854c540dfd754c540bfd844c540bfc844c540fbd544c540ff5614c540ff5514c540ff5414c540dfe7710140bfd8310140dfd7310140fbc4310140bfd8210140dfd7210140fbd4210140bfd8110140ffa884c140ff8874c140ffa774c140ff8844c140ffa444c140ff9734c140ff8734c140ff8434c140ffa334c140ff9824c140ff9724c140ff9624c140ff) else (if i < 3 then 0x2c041c18042420603c023810380634e408502080c18281041803140820c01c0860307080401100c0024e408403000a0418125049c8108060e1408302080c1c201c0840c0188180310202006420023018204174e42018401850103008321030180010304200620a043803040c1010064200800c40544080a0a100020401881600100320010642000c8800b082c20005881688102d10205841610585101005c20070418881064200064200004000c8400105a204030a0806201a084190800044040682102c20504880b08101438021a7210284040014e420405010a10184042808107020004081708100c082010044030e093902100c3020800203082006281060410083041c018800181040005843218002c40a0800200084c1e0611024a210c83062006083819048c241910382000c082020839042110081c307814021a0ca20c8208643c0c18304420c841a0c10301220c8841830008200b01864a006860420c2060420c0490169c410c1020800010e008420c205c1e000c82c3e09382c2170800c000b284c1e0906121010c8304238404051c060c40000b0c013078001a48405381000161004c1e04049004101044219060c0410e0204230f8002c30c01c41f00048602080820c4e42070208003a0918303020800080e01c613078001840602012381053810070204e0410208302000000000000000000000006422040e824a110e83012402044321d04950410c2081a210615040d0b88818541041c1020820001041060510101a204880a08217058043612283c020d0ba20440c384044030ce20a0000001000244000c0820e0800018104161022020010504100640a0207088a000838219068384222061b3c19dbceb67233759b5ccf6643305974caee51b271921c89e43b2018f2c6de2ef16d8a8c51e25710f879c35e19b0b1841c1e60df053812c06dfdafad7c8bd8deb2f2b790bc5ddd2ebb74fba55cf2e4b720b84dbcada56c4b56da7ecff668b2d5932c6b61eb0cd80abfb5ddae7d6e2b4358aabe5596aaf552a9dd4b6a1b508a7d53d69cf4d9a6a52f694d498a4551ce8b944ea2050ca84941fa044fea7eb3de9eccf0a7573949c7ce066d53659a2ccba61d2ee96bcb265652a4946c9fe4bf248918c86a4071ec8ef471e3611998c5c5f62cd14f89c448622710e877435e15d08e837413a0930328124011fecff17f1bf79f8efb07ccbe2dee8f5d7ac3d05e66f1c78bbc25df6ee4766bad9d50e9a74639f9cf2e6b7333961c82e3371738a5c36e16704380dbfcdf06f1372db7ada66c7b605af8d776b93591a9ad3f69434459e2cda66632f994ec9064131d18bac4f61c3085814bf35ee2f1576eba95cdae356ecb685ad2d0d658b1e5882c2d60caf85752b4d58aab7554a9dd4aea4051028253f69ed4efa74537499a4afa54526291a48623d5 else 0x440504100001c241043210584100510080624104000e1038200704161048084040400c600c84088086420b0864200005000b100088080d04200003220007010340040a88100180310000b00083802100020058416001000a00100c0020587004305841308102420902c2069c840a10184042c05107004200142c20020280b182420504880a00127210284041a0510082002834405085c1a9c180281025020408002181004322008418102038402008938181060418104015018838100042a2002c2820b854412018800008042420))

def moveIndex8 (i : Nat) : Nat := 0x235fc66411d0b4309c89a32c6c51d11800044fc4b320d148ad47a9d34249804115400001a74ca3530000502988f0239995b08603de4bbc82d03f8b7b343cd5827cc99569f0dca36158ca2a440982154b5959f4aa661cc5d0003c63b572c3e28218c0813e00c05fb56300009a2e35bc102038d6292864cc6a3486055f780b1064000b1ff5d094434bce0cc9510000c84e2930df35a39c0ed80000f0de47c965a4de81ad98f8083193c1150c72037c79f516364624784170c34c976484ba100f5cd0003449e66483c164488de602c14b29cd021402e60134f49d4075059015e865449a42663151a53045c5a612b481b1b1c31863b59b233a82900024ae22f5018c090c36728002dd2c96405375c3ba218c581364ce075430b9059085600039b5927285ee07349000d445461308c890ab493d9930bff1d582b6348c5c32bc10f0003543818911d604e00139ed01a006c096000182f0002443000389e47800004604178b2ed83af306412e2db4da000000045800002310068b1c800004c90cdb10a094b20292a808c86ee1d155e8137527a28916976e24cbc1008aba0e60e20000d0a919c0be56340166225487338c000a41144bb43443f936c000b1209d142b40c3e25dd1c820c0000003294b0978524001d11e4fac1e333cc95323355f51c549b05b5ca630545740001c2295fc19081df06d81f486fe2a104e8017c28f534000738517082b0038630b4640002ca57469478614ec98a05c044d68c941b524000346c9050002c767346850c6534b0c02242c01cd47a422ec02f0bb8c6e2e38703184c5b045e007d1aa1e1e1ed806f17cca3107e87e5350000000188896d91cc85e70321d9352070b0500280c022e33001f2b030074010500000012000b0b0107090014040103002a070c0208090603020705460806046705080104050100030d080504020007031a01060a3c030505000110045c0406110b010000080001011c000000030210000409030b0003

def liveData7 (i : Nat) : Nat := (if i < 1 then 0xa884c5408fe4bb0c98a811fc97615315033790eaa262a057d25d614c540afa4baa298a81db576505315027e930a0a62a047f6627710140cef3bb06202817ad9210c405033dceec1080a067b5cd8210140c7ec32e4202819dd835c84050373b06a1080a067d9dd8110140cfabb30220281bb564604405033eae6c0880a06ed10d8110140cfab930220281bb54260440502f732944260a067ea64874c140cfcc890e982819fa8821d305033f10f3ba60a05f664e774c140edc4390898281f999321130503f532442260a05ee644844c140fd8c8908982817e99221130502fe32242260a05f624e444c140cfc43ae698281f988450d30502fd32421a60a05fc644434c140afc4bb04982817b89460930502bf130b9260a076e211724c1409fc4c2e4982817d89358930502bf12ec0a60a067e21d814c140bdc4a302982813f8985c5305033f10eb8a60a057e25d514c140cfc43aa2982817b898505305037710ea0a60a076e21d414c140edcbb282982817b99550530503f6302a0a60a07e650d414c140eec43a6298281dd9764c530502fb32a98a60a05f6651314c140fcc4226298281f99544c530503fa2c298a60a07f4545314c140fe8a0a6298281fb1414c53050277b2944260a047fa65874c1408ff4c90e982813bc9421d30502b792843a60a057764e774c140cdf3b90898281b9d932113050375b2442260a06ed644844c140ddcc810898281bb930211305027db2442260a04fd644844c1409fcc8108982819bc8721130502f6b2242260a066f211734c140afcc80e6982811fc985c93050337908b9260a047f261714c140cde422e2982813bc98505305033790ea0a60a05f664c404c140bf4c9080982817f191101305023fb313b860a04fd64688481408fe4bb0c902811fc9760d2050277928c1a40a047f25d86441408fe4bb0a882811fc9760d1050277928c1a20a076d5d94144140eda39a82882815f8974c110503f628298220a047f65c83801409deca107002813f59120e005027f32041c00a047f2617280140afc4ba61002811f59120e7750237b29442e6a046f262445cd408f6c910839a811f591210735023f320420e6a047d646885c9408ee49b0eb128179993201415027b32640282a046f66277101409db4cb02202819b6776044050336aecc0880a06ad9998110140cda39b0220281b96336044050336ae4c0880a06e98898110140d9ac2c22202811f897a20405023f3313b880a04f6a658310140ced3bb0620281b9a4460c4050379306c1080a06f260e2210140de8c1b0220281be182604405037a30708880a047ea64874c140cdc43908982817b191211305033710f22260a067621d434c140cec43c66982811f8985c9305033d10f11260a066e21d414c140fc8a0a62982819f087845305023792843a60a04ed644844c140 else (if i < 2 then 0x2058400000205840c0818100000030206040608000000030484064102000000000a081410002007820004001820202820004080040e0820008000c8419081c01881908161064205840002c205840b0816106420c840b0816103020701a20642058400004007040c081c1030200020018c880800c081810000308061000610018440802080008006200041002001880018400c84000000006420c8409a2040704007020018c0e0832102c20c8400000a1000001840308000104000082002c2040600080000840e10021038400680c10000000000000000000000000000058422038401840e0800b083206042302c2070182208091018103820c812295b95695194c94793892992491f91090b8fc8ed8de8cf8ca8bb8b68b18ac8a78a289d89889388e88988487f87a87587086b85c84d84883982a82582081b81681180c8078027fd7f87f37ee7e97e47d57c67c17bc7ad79e78f78077b77677176c75d74e73f73a73573072b72670d6f46ef6ea6e56e06db6d66c76b86a96a469568668166865964a64563662762261360e6095fa5eb5d25c35b45a559659158c57d56e55f5505415325235145054ec4dd4ce4c94ba4b54a649748847945644744243342441f41a40b3fc3f73e83e33ca3bb3b63b139839338437f36636135234d33e33933432f32a3253203113022e92da2d52b22a329428527627126c26725825324e24923a22b22622121220d2081f91f41e51d61c71c21bd1b819f19a18117c16315e15915414f14a14514013b13613112c12712211d11811310e1091040ff0fa0f50e60cd0be0af0aa09b0780690500370280190008fec81073ba819dd8320e77502beb2241ceea04fd644839dd40ddcc23013ba811fc9760e445027f32041c88a047f652885cd40cdeca510b9a815bd94a21735023f931222e6a057764e775cd408fec810839a815dd939dd435023f92f44086a047f6627710d40cf73bb0421a81aed86608435033eceec0886a06bd6198110d40dbac2b0221a81be582604435037d304c0086a06fc6058010d40cef4410f19a811fe9921e335023f92ec1466a047f25d818cd408fe4bb0119a811fd90a21725027eb23442e4a04f724d87589408fec990eb12811fd9720d6250277b2841ac4a04fd64483589409fcc8106b12813f990a21425027b926c3284a04bf65883509409beca906a12813f59120d425023f92ec3264a04fb261424c9408fec9d10b8a814fd9610d71502afb2a21ae2a057b648435c5408fe4c466b8a811fd9321d615023fb2e41ac2a04df65483585409deca106b0a813f99020d615023fb2643aa2a047f65c83545409deca106a8a813f99020d51502e7b2a41a82a05ee6408350540adecb0e6a0a819bd851cd41502b792eb1a82a04df6548350540b5ecb086a0a8173d9510d41502f5b2421a82a04fb64 else 0x1c100820000410004103820104000818008000000000000000000001610002002c2010400000000000000000))

def moveIndex7 (i : Nat) : Nat := 0x40264e05fe1e34225d70cc0db1d81351ab62110940a1f54580310e716543c00a49805000011508c48409919b0af06d1455500000081c01bb21644d5b000b18000c22c1230fe1730b000120e1500020700004f904f01ad9a58c5e6593992810490f40c12c000c018280040081

def liveData6 (i : Nat) : Nat := 0xc840064206420642064200321032100007040704100020380688000c20000c0800000000642000014fa55166b309044200f075b6d96c660ac5429c461c4d85c2b948843d1c0cc5c29120501e0a02802ab5a610d8110140ae968843604405029b9a4a20874c140de264d92211305035b087644844c140dac659912113050373195644844c140de464d91211305037a192644844c140be46848450d30502d39a5211724c140b6c684845c930502799a424d624c1409f46849358930502739a5261414c140e6c68487505305023b8a8655414c140c6e21d95505305039b087605414c140bc6694844c530502dd0a7545314c140be42a1414c530503d9087505314c140f645d9414c5305021bda4a65874c140ce364d92211305032b596644844c140ccd65591211305033a592644844c140cec64590211305033b1914c0844c140c6d21d912113050293da5211724c140d6c25d414c1105031b087644844c140

def moveIndex6 (i : Nat) : Nat := 0x25d

def liveData5 (i : Nat) : Nat := 0xa20dc5b950caa82982813c46d4a8505314c140

def liveLevels : Nat → Packing
  | 10 => (1,1,6,0,0,0,0,liveData10)
  | 9 => (36,2,6,0,0,11,0,liveData9)
  | 8 => (370,3,6,0,0,13,0,liveData8)
  | 7 => (228,4,6,0,0,12,0,liveData7)
  | 6 => (35,5,6,0,0,9,0,liveData6)
  | 5 => (2,6,6,0,0,3,0,liveData5)
  | _ => emptyPacking

def liveIndex : Nat → Nat → Option (Nat × Nat)
  | 10 => lookupWord 16 56 4 11 6 1 moveIndex10
  | 9 => lookupWord 184 608 7 15 9 2 moveIndex9
  | 8 => lookupWord 106 349 8 14 8 2 moveIndex8
  | 7 => lookupWord 20 62 6 12 6 2 moveIndex7
  | 6 => lookupWord 1 3 0 5 1 0 moveIndex6
  | _ => fun _ => none

def orSamples : Array (Bits × Bits) := #[(0x3080e060f803c03e000201f007e00fc1fc003801fe000041f80601f803f003ffffffe1f807e007fe0000fe007ff8100700f8001f007ffffff01fe003fffff001ffffffffffc07e003e001fe00003f003ffffffffffe03f80003fffc00003ffff,0x100020206100001a1002809004a80a40aca090018e240100680200a8008100a9414d615a228204962404984814d0000000080041000300030010a0080c0a100140a02600524014050800014200885000c5008c0355202a900509c6480060a02a),
  (0xc0ff007f0003ffc0001c01fff8000ffe00003ffe0000007e0007fe0003fffc07f001fe0007fff8000000ffffffffe007ff00001fff80ff007fe00003fc01fffe001fe00000ff80003fffe0000003fffc00ff80001fffc000003fffffffffffff,0x40f7114b0003adc0a214116b5201249400022d6a2088a41e02055a0201546c04b48006000534e90088c82291492be287d70148882500ab5059a0022351114b54001dc852049680003356a408a51084a400eb21480856402308323892d2894f44),
  (0xff00007ffffc0000001ffe0000000fffffffc0000000007ffff8000003fffff80001fffff80000000000ffff800ffff80000001fffff00007ffffffc0001ffffffe0000000ffffffc00000000003ffffff0000001fffffffffc0fffffffc0000,0xbf000034d5dc0011044be60000100969daccc011053108615ce0000482a992d90909b98f480006053100cd6210441c3800821217cad64080021a388c00409489a5c01484186867718000001308236b4ab6104a119180b35c5180832d24329008),
  (0xffffff8000000000001ffffffffff000000000000000007ffffffffffc0000000001ffffffffffffffff0000000fffffffffffe0000000007ffffffffffe00000000000000fffffffffffffffffc0000000000001fffffffffff000000000000,0x84618000000000001418719bc1b000000000200800310200080230140000000000421031c0b038006e0000008120c2192860e0000000027cc4c331999d011008088018609318061c18c18031c00000000200420e1b0c018e3c0c0040c00470),
  (0xffffffffffffffffffe0000000000000000000000000007ffffffffffffffffffffe00000000000000000000000fffffffffffffffffffff80000000000000000000000000ffffffffffffffffffffffffffffffe00000000000000000000000,0xed599a5e9e6af6a5c7612002000200010308064001c1c07597759d072b3e3b163e10100400180001c1900180610e5f15e2d7831af364f2e400080c0202000600311118e0802c61d821e31e1dce038df338dc739c000000661000103187031980),
  (0xffffffffffffffffffffffffffffffffffffffffffffff800000000000000000000000000000000000000000000fffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000,0x69e43871870c70407983c43e303c18e100f087c3001fe000040100030002000200000004000c02001e00000000f97e67ce3fc1c7c787cf86f0f0fc3e3e1e7e03e1e00ff00300060007c0801f0020180206003e0001c1007e0202001f8001e00),
  (0x0,0x0),
  (0x0,0x0),
  (0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0xf8609c78e7833839f803c18c041c0e31e3f03781c1fe0079e787e1c7c3cfc3e7cfe19de7861f07c1fe00f1fc7e00080080040000800080000010100000000801c0001f00000041800180101e00000e03c0807c00100020780000c03e0003e000)]

def orSymmetries : Array (List Nat) := #[[],[81,130],[48,33,133],[48,129,82]]

def orCols : IndexTree ColumnInfo := (.fork 17 (.fork 8 (.fork 4 (.leaf [(1,0,318,0,7),(0,2,312,5,6),(2,0,2365,0,8),(1,2,312,4,5)]) (.leaf [(3,0,316,0,5),(0,4,2353,10,6),(2,4,2353,8,5),(4,2,312,1,5)])) (.fork 4 (.leaf [(6,0,2361,0,7),(5,2,312,0,4),(7,0,312,0,4),(8,4,2353,2,5)]) (.fork 2 (.leaf [(10,4,2353,0,4),(14,0,2353,0,4)]) (.leaf [(18,0,301,0,5),(0,32,30,257,6),(1,32,30,256,5)])))) (.fork 9 (.fork 4 (.leaf [(33,0,286,0,5),(38,0,2329,0,4),(0,256,2071,40,6),(256,0,2111,0,8)]) (.fork 2 (.leaf [(258,0,2109,0,5),(262,0,2105,0,4)]) (.leaf [(8,256,2071,32,5),(264,0,2103,0,5),(280,0,39,0,4)]))) (.fork 4 (.leaf [(32,256,2071,8,5),(256,32,30,1,5),(288,0,2079,0,7),(257,32,30,0,4)]) (.fork 2 (.leaf [(289,0,30,0,4),(290,0,2077,0,4)]) (.leaf [(292,0,2075,0,4),(40,256,2071,0,4),(304,0,15,0,4)])))))

def orForest : Forest := ⟨2367,10,fun j => orSamples[j]?.getD (0,0),orCols,orSymmetries,liveLevels,liveIndex⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem orGeometry : graphValid orForest (boundsBefore entries251) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked10At0 : block orForest 10 0 1 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked9At0 : block orForest 9 0 14 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked9At14 : block orForest 9 14 22 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked8At0 : block orForest 8 0 3 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked8At3 : block orForest 8 3 56 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked8At59 : block orForest 8 59 56 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked8At115 : block orForest 8 115 25 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked8At140 : block orForest 8 140 56 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked8At196 : block orForest 8 196 56 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked8At252 : block orForest 8 252 56 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked8At308 : block orForest 8 308 56 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked8At364 : block orForest 8 364 6 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked7At0 : block orForest 7 0 43 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked7At43 : block orForest 7 43 56 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked7At99 : block orForest 7 99 56 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked7At155 : block orForest 7 155 56 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked7At211 : block orForest 7 211 17 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked6At0 : block orForest 6 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked6At1 : block orForest 6 1 34 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked5At0 : block orForest 5 0 2 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

theorem allAt10 : block orForest 10 0 1 = true := checked10At0
theorem allAt9 : block orForest 9 0 36 = true := (@block_merge orForest 9 0 14 22 checked9At0 checked9At14)
theorem allAt8 : block orForest 8 0 370 = true := (@block_merge orForest 8 0 140 230 (@block_merge orForest 8 0 59 81 (@block_merge orForest 8 0 3 56 checked8At0 checked8At3) (@block_merge orForest 8 59 56 25 checked8At59 checked8At115)) (@block_merge orForest 8 140 112 118 (@block_merge orForest 8 140 56 56 checked8At140 checked8At196) (@block_merge orForest 8 252 56 62 checked8At252 (@block_merge orForest 8 308 56 6 checked8At308 checked8At364))))
theorem allAt7 : block orForest 7 0 228 = true := (@block_merge orForest 7 0 99 129 (@block_merge orForest 7 0 43 56 checked7At0 checked7At43) (@block_merge orForest 7 99 56 73 checked7At99 (@block_merge orForest 7 155 56 17 checked7At155 checked7At211)))
theorem allAt6 : block orForest 6 0 35 = true := (@block_merge orForest 6 0 1 34 checked6At0 checked6At1)
theorem allAt5 : block orForest 5 0 2 = true := checked5At0
theorem orTables : checkedTables orForest 10 := by
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
  · exact allAt9
  · exact allAt10

theorem noRun : Impossible (graphGoal 2367) 10 (vars 2367).toFinset :=
  root_index (g:=orForest) (before_sound _ sound251) orGeometry orTables
    (k:=10) (by decide) (i:=0) (by decide +kernel)

end Free319

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound319 : Lower (vars 2367) (graphGoal 2367) 11 :=
  augmentedGraph (k:=10) (m:=319) (hints:=12884910340) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (before_sound _ valid383 319) (by decide +kernel) (by decide +kernel) Free319.noRun

def entries319 := extendKnown entries251 11 [(2367,[])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound319 : Known entries319 := extendKnown_ok sound251 seededBound319 (by decide +kernel)
namespace Free351

def liveData10 (i : Nat) : Nat := 0x1a830ffd40

def moveIndex10 (i : Nat) : Nat := 0xac00c44421c6a000500152f24628247bc4bbc24286dc7c44a3dbd958004200236a601000008c0

def liveData9 (i : Nat) : Nat := 0xd14041948c620281948c51a281948c5280e30e30710a065231008a0652307301150c307286291840450305503181c6101861aa0b2818c2150c1540c5da632c94a9bc59ceb8529d8c63b14003fea9281ff58540ffaa2a07fd31503fe18a81ff48540ffc22a05fd75503bf2aa817f5c940fdc44a05fd71503fb08a81fe4c140

def moveIndex9 (i : Nat) : Nat := 0x4c8a224f4d3830de1548ea80001e30c624e0c32b249304cc00010f81a90143ad17e89075cde60fef4cba09326bebc003437499c140000000a40000000000024fa545b31e52822c70096506cad29363c636ec6264089537344c010d140c6f946850b52452c0018fc0008ec07a24cc05e06cd611f4b0cbe408003b08ed37358862b8e102b205ec6fceaa266c3ae105709e42d81d044e8400185044c64a6fd0b7c127390f14aad4b0a1459e7a91bf2193ec3e92bd234429426e7c814c28c4864000001e54ce52a507e04882742b4db66d51000d969c4c415e00530d01700a10e0050450011012000001302820421050432c2

def liveData8 (i : Nat) : Nat := 0xf061000b08383c42a0c2020c941ca010a8c500852810f061010608083c40614608003090c21a221230e83010a022e3042824087068c21112103010818084080c2008030a0c081041a0c2020f10003080810428183081844822ea8143120a10043081420ca8243860a185430e18214260e31205060b20483880c20c2e16301150a183040100e20608304145c2060c1140317183010b8c58284062c00308021030108502840c10030400c10018400c10608386182140e2860c3041c30c102060b1c3038a18384afede8ba76daccd84aef58aa6d38a5747a84cfc9bf2ca52c888e717a24c3483f069febe87a6ef9d4b9470ede9b6b60686cb98cb0c5deb8962ab85369d930a5446e86906a083e6798ec9bc35e648ba9602864b88c9041ee3c8728e01a6338608bc15e2884a8880e61982c84c07e08806800bfe8854940dfd625c540dfd525c540bfe8858540dfd7358540dfd7258540efd6258540dfd7158540bfe8854540dfd7354540dfd7254540f7d5254540dfd7154540bfe884c540dfd874c540bfd854c540dfd754c540fec824c540dfd724c540dfd714c540ff5614c540bfd850c540bfd820c540bfe8848540dfd8748540bfd8648540dfd7648540bfd8548540dfd7548540bfd8348540dfd7348540fed5248540dfd7148540ff53148540ff9634c140ff9534c140ff9624c140ff9524c140ff9324c140ff9614c140ff9514c140ff9314c140ff9214c1409fe885d5409fc835d5409fe885c940d7e555c9409fc835c9409fd8754940ded7588940f6e55889409fe885c540cfe665c540d7e555c5409fc835c540dee225c5409fd8758540cfd76585409fd87545409fd874c5409fd870c540bf9800c5409fd8748540df57684540ef66684540df57584540f765584540df57384540fd63384540df57284540fe62284540df57184540bfa884c140df9764c140efa664c140df9754c140f7a554c140fda334c140df9724c140fea224c140fb9414c140fd9314c140ff2114c140

def moveIndex8 (i : Nat) : Nat := 0x84000c1b9fe488e42f8374b98a7000810012342045e1bc2680a50000000018049a80

def liveData7 (i : Nat) : Nat := 0xc2000000010400a08004101040410301c4070d0ce4744c23fbd3ab3b12a27a09992870047f64a885d5408fec8906baa811fd9120d725026fb2b442c2a04fb64a884c5408fe4c2ea98a819ed8720931503f912498a60a07f4585314c140fe898a429828117d9520d725023f321442e2a047e261764c1408fc4c2ea982811f8985c93050277130a0a60a07e4505314c140

def moveIndex7 (i : Nat) : Nat := 0xf

def liveData6 (i : Nat) : Nat := 0x3f8092505314c140

def liveLevels : Nat → Packing
  | 10 => (1,1,5,0,0,0,0,liveData10)
  | 9 => (14,2,5,0,0,9,0,liveData9)
  | 8 => (83,3,5,0,0,11,0,liveData8)
  | 7 => (17,4,5,0,0,8,0,liveData7)
  | 6 => (1,5,5,0,0,0,0,liveData6)
  | _ => emptyPacking

def liveIndex : Nat → Nat → Option (Nat × Nat)
  | 10 => lookupWord 10 29 5 9 4 1 moveIndex10
  | 9 => lookupWord 43 139 6 12 7 1 moveIndex9
  | 8 => lookupWord 11 25 3 10 5 1 moveIndex8
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

def orCols : IndexTree ColumnInfo := (.fork 12 (.fork 6 (.fork 3 (.leaf [(0,1,332,18,6),(2,0,2397,0,7),(2,1,332,16,5)]) (.leaf [(4,0,2395,0,8),(6,0,2393,0,5),(12,0,2387,0,5)])) (.fork 3 (.leaf [(17,0,334,0,7),(18,1,332,0,4),(19,0,332,0,4)]) (.leaf [(21,0,330,0,4),(8,16,326,1,5),(9,16,326,0,4)]))) (.fork 6 (.fork 3 (.leaf [(25,0,326,0,4),(0,64,2077,258,6),(2,64,2077,256,5)]) (.leaf [(70,0,2329,0,4),(0,256,2071,72,6),(256,0,2143,0,8)])) (.fork 3 (.leaf [(8,256,2071,64,5),(256,64,2077,2,5),(320,0,2079,0,7)]) (.leaf [(258,64,2077,0,4),(324,0,2075,0,4),(72,256,2071,0,4)]))))

def orForest : Forest := ⟨2399,10,fun j => orSamples[j]?.getD (0,0),orCols,orSymmetries,liveLevels,liveIndex⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem orGeometry : graphValid orForest (boundsBefore entries319) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=2) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked10At0 : block orForest 10 0 1 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked9At0 : block orForest 9 0 7 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked9At7 : block orForest 9 7 7 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked8At0 : block orForest 8 0 40 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked8At40 : block orForest 8 40 43 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked7At0 : block orForest 7 0 7 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked7At7 : block orForest 7 7 10 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked6At0 : block orForest 6 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

theorem allAt10 : block orForest 10 0 1 = true := checked10At0
theorem allAt9 : block orForest 9 0 14 = true := (@block_merge orForest 9 0 7 7 checked9At0 checked9At7)
theorem allAt8 : block orForest 8 0 83 = true := (@block_merge orForest 8 0 40 43 checked8At0 checked8At40)
theorem allAt7 : block orForest 7 0 17 = true := (@block_merge orForest 7 0 7 10 checked7At0 checked7At7)
theorem allAt6 : block orForest 6 0 1 = true := checked6At0
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

theorem noRun : Impossible (graphGoal 2399) 10 (vars 2399).toFinset :=
  root_index (g:=orForest) (before_sound _ sound319) orGeometry orTables
    (k:=10) (by decide) (i:=0) (by decide +kernel)

end Free351

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound351 : Lower (vars 2399) (graphGoal 2399) 11 :=
  augmentedGraph (k:=10) (m:=351) (hints:=12901687556) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (before_sound _ valid383 351) (by decide +kernel) (by decide +kernel) Free351.noRun

def entries351 := extendKnown entries319 11 [(2399,[]),(2493,[130,114,49,98,81,64])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound351 : Known entries351 := extendKnown_ok sound319 seededBound351 (by decide +kernel)
namespace Free471

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem noRun : Impossible (graphGoal 2519) 7 (vars 2519).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=2519) (0,16,454,1,6) _ (before_sound _ sound351) (by decide +kernel))
    [] (pool:=(vars (poolMask 2519 (0,16,454,1,6)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Free471

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound471 : Lower (vars 2519) (graphGoal 2519) 8 :=
  augmentedGraph (k:=7) (m:=471) (hints:=26323452164) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (before_sound _ valid383 471) (by decide +kernel) (by decide +kernel) Free471.noRun

def entries471 := extendKnown entries351 8 [(2519,[]),(2549,[134,81,114,49])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound471 : Known entries471 := extendKnown_ok sound351 seededBound471 (by decide +kernel)
namespace Free255

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem noRun : Impossible (graphGoal 2303) 11 (vars 2303).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=2303) (64,0,2239,0,11) _ (before_sound _ sound471) (by decide +kernel))
    [] (pool:=(vars (poolMask 2303 (64,0,2239,0,11)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Free255

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound255 : Lower (vars 2303) (graphGoal 2303) 12 :=
  augmentedGraph (k:=11) (m:=255) (hints:=553656580) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (before_sound _ valid383 255) (by decide +kernel) (by decide +kernel) Free255.noRun

def entries255 := extendKnown entries471 12 [(2303,[]),(2555,[118,130,81])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound255 : Known entries255 := extendKnown_ok sound471 seededBound255 (by decide +kernel)
namespace Free383

def liveData12 (i : Nat) : Nat := 0x112433062c2ffd40

def moveIndex12 (i : Nat) : Nat := 0x1c19a00a0d99f1429cbaa88ef89eb20e569dabb9035f88000000496039600003a58a000008d7454fb80000003b10000100010351100

def liveData11 (i : Nat) : Nat := 0x400600c0b06998785880983007118344cb2720074071102c1a661e1624260320032232499c1a5890e87040592100061909c92672c102080160641a661e1c8b10130610007119241a672c48580b11260e4a1320030072488cce0d2c48580b240d8e4a13200300b2488cb07280600e225002c1a662c410007110e01667061620800c0005a2333830e4589200300733830b0c0c0184e672488c18b2883148583924466659834b0c4001832232499c1858808ccc1c2c2446481b99c1a58620030273383446483940e4582924ce0c391616491199c18732c3032491199c1858699c18583d819f3135d0b4f56a86cb790b0bdfebb06c6c5960285470860ee9902ce4b06f8c812c16c10000ffd87503ff9dd40ffd83503ff5cd40ffc73503ff8cd40ffd81503ff5c540ffc71503ff4c540ffc31503ff84540ffd70503ff4c140ffd10502ffa2140bfd87502ff21d40dfe77502ff60d40bfc83503f78cd40bfd81502ff20540fbd41503fd84540ff930503fe80140

def moveIndex11 (i : Nat) : Nat := 0x412800f2422761452046213540b2a12f21f58191414da0992182c041e07aa193c033413800b80001a03c210702236218a0e4000161ae221c01ba41858235e163608c412ca0fc0001a0eba147e07c000041e4000180f1e045410b40f901f0816f81fe0000610f20360001617a0000c00ea156412a60dc4255804f201ea1de20ca608f00c8623d21fc21c4c1f2416b0203e01141c62238805cc09e20e381eb21b2001c211f00a8e006c1cba23f220e41960001c083403fe1ab203920c3e2116100414fa09de154e06da1da00d6000100bd616800018114f00c20180001c0cce1c20001c15fc05be18781d000000001e050e0d480a0013701ee424a10f40001618f211c0000802ce0e6e0888031e08100926180c02be21fe1d96059c062a00d024c0105e0296132c120c24e010801a441030152c259e124c18d008be0cfd1dca15b625a01e0e1e68061e1600111c13d0252a1d2e224c001e198224440907104e130e0b4c1c100faa003418b821260fea071204ca053801210b0024021596027c03a00b741bce188e0f6611620a2004ae20be176e0224034e1f700ad209a40c741dc0001c1b6000a0001209642490178a1f8e216000161a86078212700e8000100edc10da005a19d6200014901cf401b4069611860db0112013e8220022ba1ade247e0bf622821e210430233a02141a1800860d22195c0d8c1e9c0c4e014e19a00008215a237c22cc1b0c1d40000c13bc1c80000a20dc14a60d04074a12242568142c140a073c094e0760001c206219f80a60001817c82310054025141cd207f8042e15120a4e0c0008461bfe15d6205c1a7e1d6c0e0616dd02ca02ec0b1a0bac23ac1b4a05e0000e1a3e016000060de000160560001220881ed62432067206a2049c174e086c0f5017000000172c11b41b8c02441fa0000c22fa0aa20ae20ee8064a21ac16411da8166417e206e0ce803c759846e2c58e2c640021009c9300246800e140800600021ac0139e401810402252020018000000039300104b90a00107163c0010200c8f0030805001c0060e8800a002448f4a0c2800c0c68900302033200000201c007

def liveData10 (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0xec1b02a07f78cd815037fcee40a81bfd7320540dfe39902a06ff8cc81502ffd32b8a817fd985c540dfecc2e2a06ff261715037fd10b8a81bfd875c540eff3bae2a06ff60d715037f906b8a81fde335c540dfec0ae2a05ff660715037fd1038a817fd931c540dfec18e2a06ff20c71503fbc6638a817fd901c540fdf4ca82a07ef65d41503f792ea0a81fbd8750540fdf3ba82a07ef64d41503f7926a0a81fbd8350540fdeb9a82a07ef1cd41503f7c66a0a81fbd7150540fdec8282a05ffa6531502ffb3098a81bfd984c540dfe4c262a06ffa2131502ffb2e98a81bfd874c540dfe43a62a077f9dd31503fbc6698a81bfd814c540ffab8a62a07ef50531502ffb3018a81bfe880c540bfecb862a06ff61c315037f90e18a81dfe770c540bfec8062a07fd25e11503feb0f08a81ff67784540ffa49c22a07fd60e11503feae708a81ff47384540ffb19c22a06ffa22115037fb0f08a81bfc8784540eff3bc22a06ff60e115037f90708a81fde3384540ffac0c22a07fd5c611503fea6308a817fe995c140eff3bae0a06ff60d70503fbc66b8281bfd815c140efeb8ae0a07ef50570503fec22b8281ffa994c140ffccba60a07fe25d30503ff30e98281ffa774c140ffcb9a60a07fe64530503ff12298281ff9814c140ffcb8a60a07fe1c530503ff26298281ffa114c140bff4ca60a05ff65d305037fb0e98281dfe774c140fef19a60a06ff60530503f7a8298281fdd314c140ffb08a60a07fe5c130502ffd32882817fd9744140dfec3a20a077f9dd10502ffb2688281bfd8344140fef19a20a07ef50510503fec2288281ff93044140ffd3bc00a07fe5ce00503ff0e700281ffa3380140ffcb8c00a07fe1c600503ff26300281ff83180140ffd08c00a04ffa65875027fb2643a813fd9121d40cfe4c4eea067fa22775033fb0f3ba813fe9960d409fecb906a067f9dc835027fb2241a813fd981cd40b7ecb0e6a05df65473502f7b2839a817ed921cd40bfac88e6a05fe640735037b93119a81bde888cd40deec3c66a06f721e33503bbcef19a81fd8908cd409ff4cb02a067f9dd815037bc66c0a813fd9720540cff3b902a04ff64c815037bc6640a813fd985c5409fecc0e2a05ef65071502f7d32a0a81bbc9850540ddf44282a06ef61d41503b7ceea0a81bbc8350540fcf19a82a07ee241415027fb3098a81fb5414c5409fecc062a05df65431502f7b2818a817f9900c540dfa4c422a06fda22115037eb0f08a81bf48784540efb3bc22a06fd60e115037e90708a81fd63384540dfac0c22a07ed50611502ff53298281bfa884c140dfcc3a60a077e9dd30503fb46698281fb9414c140fec98a60a07fc84530503f6a8288281bf98780140efd3bc00a06fe60e00503fb46700281bf98180140fdca0c00a07fc846005025fb2c41a813bc9850540 else 0x593d573525d40b4dfd2f347bd13b417cfab3b3cdf3359cc8b2ffcb23291c9bb24bc87b1f1c7131abc623165c4bb101c3a30b1c23b061c0d3011bfbafcbbe7af71bd12f17bb82eb3ba1ae77b9a2e1db83ade1b6d2d91b592d23b452cddb1d2c51b042bedaeb2b6bad4ab39ac5aac1aa52a85a9daa5da93aa17a73299fa61a977a57a931a4128d7a25a85fa0f27d39ec276f9d0a7159c1a6cf9b02689997263997e2585958a52b94224c79242477903a3cd8ed23738d6a3378bb22c98a7228d89aa24788921e3870217f854a11b83ba08f81b20358021fe57dc9f457c61eeb7aa9e417739d9775f9d657491ccf7261c7f7171c116fb9bcb6ef1b8f6e01b716d61b496ce9b216c21aef6ae1a6d6901a2767c19b9668199165e195f64c991963898c9622186560b98155f797a75dc17435c316d55aa167159115ef570958b557953154114cd52d149b519144150794054f393a14da93294c412d94a89289494923948311f347911d546f11a3465117b45b115343a90a941a10454038fcd3d68f193b88ea139d0e473868ded3700d9335c0d4d3458cd532a0c673110bc72e18b452c60af52b20aa52918a0f276099725a8933235089d217081b1fb878f1ce86ef1ae067718d861d17985a515e053713d84bf11f843d10183c50e603430c082d509d8221078019f05a013b03e80cd023005f00c80190003ffceec1a81ffe995cd40ffecc2e6a07ff61d73503ffb06b9a81ffd915cd40ffe48ae6a07ff64173503ffcef19a81ffe7760540ffeb9b02a07ffa6571503ffb30b8a81ffd875c540ffec9ae2a07ff24d71503ffb06b8a81ffd735c540fff19ae2a07ff60571503ffb20b8a81ffe331c540fff4ca62a07ff66131503ffb2e98a81ffc974c540ffec3a62a07ff9dd31503ffb0698a81ffd734c540ffec0a62a07ff5c531503ffb2098a81ffe770c540fff3bc22a07ff5ce11503ff8e708a81ffe3384540ffeb9ae0a07ff8cd70503ffae2b8281ffd315c140fff3ba60a07ff5cd30503ffae298281ffd314c140fff3ba20a07ff5cd10503ff8e688281ffe3344140ffeb8a20a07ff4c5105037fd32c3a81bfd9361d40dfe49b0ea06ff645875037f922c3a817fe9961d40efe49ceea077f246775037fd113ba81dfd879dd40dff4cb06a06ff645835037f922c1a817fe9960d40dfec3b06a077f9dd835037fcee41a817fe995cd40bfecc2e6a06ff661735037f930b9a81bfe885cd40dfec3ae6a077f9dd73502ffb3039a81bfe881cd40bfec88e6a05ff64073503fb92f19a81fdd878cd40fef3bc66a07f7246335037fd1119a81bfd878cd40dfe43c66a077f9de33503fbb0719a81fdd738cd40dff4cb02a06ff65d815037f92ec0a81bfe7760540dfec9b02a06ff24d815037fae6c0a81bfc7360540dff19b02a05ffa65815037fb0ec0a81dfe7760540df) else (if i < 3 then 0x13060f52c08c8218a19987b832586c460310804003241202cccf065018010a0210200e0900ae679260cb818025492c128b09e0c284c0e10872040c960181d180cc4440c904e12333c19120020160121d141607851b258108c3f11013c902806c39384e2e842300c5b088701841606c280848a0052c0a26a0090c0a2618191310068609134304280331ca2616944049211040198e42d38262247217121380c42988606472169444446364802e2c270188130a261b09130244204262805a41022c14671221c2905a5c462c14482103820272169b3384c2d1a220e0721605a5c462c101809e220e05a5c4533490200b4a06622a90941895330382c0b480282708ab2251724845360b04a2e22a90401693114d8130842d2c22a901c1690131081cc184ac9333c45108a6c2505a44cf240b00e128b08aa41005a4030008b02126221cc581691330b00c0842d2e2309880c84c508aa40604216941c04c2d1e0d0985a3c461316229981c1605a500e130582d2622060731605a5430520b0210e42d3623098b111003984c2d2a812901c1c85a5c4613102c020261c85a500e1312232904016914084c50986130a19098813ccc4818413c18509850384c40600709e23926678305a2e842a00c0bc18130885930180b60c040262c9852c192c1e668660c9ca58504d0c40f11c1859308001e2309c37920878366616842b00c3f113330382c308108e6707458510002ccc0e0f42c3006028402c901d0702016480e838100b240741208059203a0e0402c901d070201648028402c8f330392c1a8199e0c9ca58503333c1b114e7243019832a496114083333c1b11c90d9981c960c161000c0531184c02c9306ccc2d085820623066679260c603240c4733c93063018210581c90408e62c1880218581c900c8e62c1e2206005836499985a108ba9033110704c0e4a008280e0981c9611ccf24c181484cc0c828160724ccc1bc18030b0aa003609807836499985a10a603ccf2484f0628320882d9984016181b80f33c9213c18d99e0c1602841031100333c9306128310e92088379222799e0c188748100160032406c310e4e138a00d8621c94160172406c310e4c0002d920361887260e52c12808666783258500d0cccf06c47243007832a496114080f33c1b24c44c01a8188e679260c600d11ccd0e4b0a8640799e0d92622604d40c450cc903932220a648898725cce0cc1a13c931136678301816104203311c1b24ccc4a0b5199c1909e0d926226ccc13c902020280da2383027926661085a904e13c9311c1b330b44a4667064278364988981607333c183a0b0c8666783272161540ccf068b080da8199e0c9c858643333c1a2c2028a021999e0c161814ccf060b0881e678345840382c1072160b7a5dde3769dd43737dc2b6f1db636b5da73683d933633d8435e3d6db else 0x5001d10182003422112c083296081944c489a6683034401444103496080c108481a800b0819058401e66200082997334b0402c66960d13ccc040e4821666200a648cc05074601a2709c661f963300c4207513280919a263013334b0602832240c03c180c01010068c89a0c0283c444d3301306068a0860c0609041400c0152c078a89c0c018a024140504c1e180689c27030345014130786062270987202151301005c1b1128880b0a030585314060282d01c2640401d46c0520200ea360b103f8b0428237160d330fe2c18a188a0d1600a51001c12213203509881cc453384c0528420d42635031105850202d8880109901c0011b18380b23634cc0484c68300a02426404f241402120a39203c141056c905008489980b9202e2e97244e4500b482042628042443028185131081915209948503a58104c1b0742d220d998502291360a0221c260d83a109133492061480e0a0d0984408460e1585028882060c02e67920ba0f0949628394b0281a488180a0e03e2c191312c5e1a060288999e0c9619240310982413174c8342620741e14a496042304c000401d0101c080594036028b21091400a58144d40120611400c8d92c084a9202002826060ba109c0c10d59088909c18204c303226204c14058212266922b20f1043c19520b880c8862160c0b2b26500434182f0e0b9985c108c161100210c4205706ccf240854012b2108d4010c2f03236084d098280b0424490361641e2426150252038390a0b098440040438e450287e05c7316100316c221818280841946c111b3310000c180414f240644e8e52c58669603c3ccf111640a174b99a582a0c4206706153334b0d030b2098122e961314840e88401086298399260c16e66a8cc024450e44c5d3427998a33844420bc4c0e8c0b03c244e390b4788820098340a8981c9c438e42d18880a07a1712030e220b05a304414084699858108c030515205b060b4c1b058108c1314019c1816564ca0072160424ccc2d04414084aa00581b042404e1306c05ccf24c183a0b92022b2108d4006c2c0d82128321b0581d1003058211881830019980808033920911ca58b100394b01e2649830901d))

def moveIndex10 (i : Nat) : Nat := (if i < 1 then 0xd0f651a1a09761739025905ea018a13390e800000000f160f04f90e0609e31b74184d02360a3b14fd04c0000e009000040080000607540489080818dd0840134d193409030b631d381271186405650bb40da50f50000b83710c28119f135302410e27116f1400039b142480dc12f000080370000e00b2181b1516078406de02cb170814411d250ca805181c60000301960b4211881b3a19460d5000001560000a1a0e16ff1a96020618a912d0000902651d1e17df0cc4093311fd161000000008012f05c10520113a04bb0740000c0626028605b40ef61908073811a0000000000d7006801473136110d812a30d460fe20c8c19a4050e111a0343152511c70fb10220000918f00891146e02d30e9c040e15ed1af900a90f871aed0d3d0a8b1bef1a740bde03c20911105816231b9e01d003641d020a4b041d1bab0f411a400000000b04d11cf00000000704a000000000000c15741ce707a6199813b418be128e03f101c8045314e1198d08761a500d6706a713a715900009115b0e391b6310440cb11c350b9c0dda1b521556197612300004188a007012660a220d900000158e0cf50c62038c16be00d2029e0e6c14c0000b13c7079419e51450000e02b0000007b910ea1d50000c02a80e151a39016605a01b2215b810c906930a150965067416761214117e07f51c40000d0a7e1b1d0886180b09ab0ce9014c01520f3c0b560bed0afc0bf6065911ea08a0000000020b0317831b8219b20468083a14d50f0c164e05d10d190e4d11d71630000d166300ec1ad21a82095000070c7a10a0000000071483191012420b801923196c0d0c03d0000c0d8f12e508200003064600cf0b7f09920de20779102a09fe1c8a0dfd1d40000f0d290ac4066d1c90000c0b2316c0000c0ae101fe17bb1d620ff50760000117ac1cb5005207e7108b0710013706c28918168e12c00006004613f0054a0f1a0c5a0ee7109f0f2314b50bcb09ca081d02fe0e5718570fae01a71ca8003d072b1bf582c9058710fb189813171a22035d02eb13830dc11c01055a17e908600ba1107f0335125d0530101608b01cce1003057008c716da103301b20ebb0c490e710a60001a0430070b06b70f9f18c5130203160c0417c2085814a40c3d06f6021209d0171e04ec049d08ed122c0abd07c2129215d40175114c0f780aa7112f169917441b47098e12bb0db00001902052005000029130d61c64509005c020006030b05120d17120a0b1d3f0523024e0504006202010d20011d001c13431e110b0003071d0005003d190d010e0f16001346050407130e030a080c190304000a010002080105000f040111571e0504050204020811040007050001011b1e0b0f491b00005e17011f0b080502012c18001201032805000f180b000104090a00160600020900040602010d2e0b06040106 else 0xe19ca044310b607dd0a56042000011c7e01070ad00008137418300002154e1397195e03ac1a681abb03b9011c150f094f176513d21c56172d1bcf0cd5092b059615c108fe14351c2d1bd71aae954d0b350edb0b1716a60ea6032e182b15fb04781bb408da16e90618179f86fb13ec19d80fc117fa000f0c970a0482b4110d0a9f177406ec88ce00fc05fc0ec7002118ef00628148120815ad15311acc027113220fdf1cd201ed19f6060b141f1c130302106103e51b0d1658187a063f82ab11b009b00008149317560c1)

def liveData9 (i : Nat) : Nat := (if i < 3 then (if i < 1 then 0x9784540bf96889784540afdaa98784540afd2a58784540afd68c8784540e7d2a27784540e7d2627784540e7da227784540e7d61e7784540afd6a09384540bbd6989384540bfc6809384540afdaa98384540afd2a58384540e7d9dd8384540afd69c8384540e7d9dc8384540afd6a17384540afd6a07384540bbd6987384540bdd6947384540bed6907384540bf96887384540bfc6807384540ef52a23384540ef52623384540ef5a223384540ef561e3384540ef521e3384540f759de3384540ff428233845408ff2a688845408ff2a58784540afd68487845408ff2a58384540abf6988384540afd6848384540afdaa98184540e7d9dd8184540ef58cd8184540afd6a17184540eeda214184540eed61d4184540f6d9dd4184540eed20d4184540fe58cd4184540afd6a131845409df696995c1409ef692995c1409ef2a5415c140dee692994c140bee692994c140cfea66884c140bfa688974c140afeaa9874c140cfe2a5874c140cfea65874c140ef628d874c140d7ea66774c140e7e2a2774c140e7ea22774c140e7e61e774c140ef6a22334c140ef661e334c140f769de334c140bde694914c140bee690914c140afe6a0714c140bee690714c140bf668c714c140beeaa9414c140bee2a5414c140deea65414c140eeea21414c140eee61d414c140f6e9dd414c140fe668d414c140fe68cd414c140fec645414c140bf6aa9314c140df6a65314c140ef62a1314c140ef6a21314c140ef661d314c140f769dd314c140ff4245314c140ff45c5314c140fe6505314c140fec505314c140dfca66114c140efca22114c140efc61e114c140f7c9de114c140ff428e114c140ff48ce114c140fec506114c140ff44c6114c1409ef692994c1409ef2a5414c140fe5505314c1409ef69299441408ff6a587441408ff6a58344140bedaa94144140deda654144140eed61d4144140f6d9dd4144140ded64d4144140fe58cd4144140fec5053044140afeaa98780140cfe2a58780140e7e61e7780140afeaa98380140e7e9dd8380140afe6a17380140afe6a07380140bbe6987380140bde6947380140bee6907380140bfa6887380140bfc6847380140df62a63380140ef661e3380140f769de33801409fe2a63380140ef660e3380140afeaa98180140e7e9dd8180140ef68cd8180140afe6a17180140afe6a07180140bee6907180140beeaa94180140eee61d4180140f6e9dd4180140fe68cd4180140afe6a13180140fec5053180140afe6a03180140bde6943180140bee6903180140efc61e1180140f7c9de1180140efc60e1180140ff48ce1180140efc6061180140fec50611801408df6969961d408ef6929960d408bfaa99620d40c3f9dd9620d40c6f2627750540aaf6988350540ce72623350540be668c9050540abd6988384540fe4505314c140 else (if i < 2 then 0xcfea21901cd40af769c988cd40af7684988cd40af76a0978cd40af7aa9878cd40af72a5878cd40af7684878cd40e772a2778cd40e77262778cd40e77a22778cd40e7761e778cd40af76a0918cd40be7690918cd40ef661c908cd40f769dc908cd408ff2a6888cd408ff2a5878cd40af768c878cd408ff69e9960540cef69299605408ff68e9960540cfe6829960540aef6929960540c7f65c9760540c7f2a67760540c7fa6677605408ff2a67760540cf764c93605408ff2a573605408ff6a47360540abf6987360540adf6947360540aef6907360540afb6887360540afd6847360540afe6807360540cf72a63360540cf7a663360540e779de33605408ff2a633605408ffaa99720540c7f65e77205408ffaa99320540c7f9dd93205408ff6a57320540c7f65d73205408ff6a47320540abf6987320540adf6947320540aef6907320540afb6887320540afd6847320540afe6807320540cf765e3320540e779de3320540cf764e33205408ff6a2995c5409bf69a995c5408ffaa9985c5408ff2a6885c540c7f662775c5408ff2a5835c5408ff6a4835c540a7f69c835c540abf698835c540afd684835c540cf7662335c5408ffaa9981c5409efaa9941c540cefa21941c5408ff6a5831c540cef651831c5408ff6a4831c540abf698831c540cef650831c540cf7662331c540de7652331c540aef69c9850540cefa668850540cef2619750540aefaa98750540cef2a58750540cefa658750540eed2858750540d6fa667750540e6f2a27750540e6f2627750540e6fa227750540cef2627750540e6f61e7750540cef2619350540bcf6949350540bee6809350540cefa648350540aef69c8350540e6f9dc8350540cef26173505409ef6a47350540aef6a07350540cef2607350540baf6987350540bcf6947350540beb6887350540bed6847350540bee6807350540de7a663350540ee72623350540ee7a223350540ee761e3350540f679de3350540fe52863350540fe62823350540cef2623350540dee65c9050540eee61c9050540f6e9dc9050540bee68c9050540fe68cc90505408ff6a2994c5409fb68a994c5408ffaa9984c5408ff2a6884c5408ff6a5874c5408ff2a5874c5408ff6a4874c540afd684874c540bedaa9414c540deda65414c540eed2a1414c540eed261414c540eeda21414c540eed61d414c540f6d9dd414c540fe528d414c540fe58cd414c540fec281414c5408ffaa9980c5408ff6a5870c540c7f65d870c5408ff6a4870c540c7f662770c5409dfaa9950c540cdf6a1950c540cdfa21950c540cdf61d950c540cdf21d950c540d5f9dd950c540dcf691950c540cefa21940c540cef61d940c540d6f9dd940c5409feaa9900c540cfea21900c540cfe61d900c540d7e9dd900c540afd69c9884540afd68c9884540afd6a0 else 0x4000c402a40780174000aff6849361d40aff68c9161d40aff69c9160d40cff9dd9120d409ff686995cd40aff684985cd40cffa66885cd40cff261915cd40aff6a0915cd40bef690915cd40dfdaa9911cd40dfd681911cd409ffaa9911cd40cffa21911cd40aff684878cd409ff2a6778cd40aff68c9760540cffa667760540aff69c9360540affaa97360540cffa657360540affaa97320540dbf69a995c5409ff68e995c540bbf69a995c540aff68c985c540cffa66885c540cff261935c540aff6a0935c540bdf694935c540bef690935c540bfe680935c540affaa9835c540cffa65835c5409ff2a6335c5409ffaa9931c540cffa21931c540bef68c9750540eef2627750540bef69c9350540eef9dc8350540befaa97350540eef2a17350540eef2617350540eef61d7350540eef61d7150540eef20d71505409ff69e994c540dfb68a994c540bfb68a994c540aff69c984c540cffa66884c5409ffaa9974c540cff2a1974c540cffa21974c540cff261974c540aff6a0974c540bef690974c540affaa9874c540cffa65874c540ef728d874c5409ff2a6774c540efd2a1714c540efd261714c540efda21714c5409ff6a5714c540fed29d414c540fed25d414c540fed9dd414c540fed5cd414c540eef61d414c5409ffaa9970c540cffa21970c540cff662770c540def9dd940c540dfe9dd900c540aff68c87845409ff2a67784540aff69c83845409ff2a57384540bbf6987384540bdf6947384540bef6907384540bfb6887384540bfd68473845409ff2a63384540f7d5c5315c140fed505315c140bfe684974c140bfe69c914c140bfeaa9714c140fee9dd414c140fee5cd414c140fee5c5414c140ff65c5314c140fee505314c140ff55c5314c140bbf6987344140bdf6947344140bef6907344140bfb6887344140bfd6847344140fed9dd4144140fed5cd4144140cdf6969961d40cef6929961d408ff68e9961d408ff6869961d408ff6829961d40cfe6829961d40adf6969961d40aef6929961d40afe6829961d40abf6989361d40cf764c9361d40cfd6449161d409df6969961d409fe6829961d408ffaa99321d408ffaa99121d40a7f68c989dd40a7f684989dd40a7f6a0939dd40b7e680939dd40a7f6a0919dd40b5f694919dd40b6f690919dd408ff2a6889dd40a7faa9879dd40cef6929960d408ff6869960d40aef6929960d40cfd6449160d408ffaa99720d40c7f65e7720d40cbfaa99620d40cbf69d9620d40cbf29d9620d40cbf9dd9620d40cbf6859620d40cbf2859620d408ffaa99120d40c7f9dd9120d408ff6a2995cd408ff2a6885cd408ffaa9981cd40cbfa21961cd40cdfa21951cd40cefa21941cd40cfba21921cd409fdaa9911cd40cfd6a1911cd40cfd2a1911cd40cfda21911cd40ded691911cd409feaa9901cd4)) else (if i < 4 then 0x3040c1820302502d1b060839273309430080b448440d0211801419060b088406070885888683050981e141305a200a0e840180c881982a0ba30800a81c0c0986098401c1100a084904c304c0a8a09848882d160608000b240e0608116040604060406048604060406040c90200181060608004cd160801848184040e088a0986098783050884018401848185920400000818492711e67c180285d0b408504479270608bccc1680f3c0e858281d0b048e516080c8530400f416151ca2c1733e0c0b00a108712c1014426c4783733e4812810a29cba69698aa5be954a4e691ea40e8e8a3628bda28a887a1b2851a0da81ba0027e59f2a7af9e527799d7a7389c4a6f79b9e6c19a6e680999663f989260997ba5d396e259d95de551950653c948650693da4d092d649a91a644390a240d8fca3cc8ef23968dc23558cbe3098bba2d38ae22a88a0a2678932231885a1f087561ba867e18f85fe164852612e844e0f883760c2829e08c81c6061811a02080420007f69fbf7e65f7e7db9f5e7d0df287c35ef27b5dec77adde9c7a31e717959e3b78ade0577a9dcf76a5da4767dd8475a5d4e74cdd23744dd0373cdce3734dcc372a1c9871f5c6270f1c377071c0c6fc5bd66ec1b956de9b546ce5b296c0dadd6b09aa76a31a716959a4668ada1067d59e567559ba66a999a662997a65a995a6555950652d93b64ad91b642d90663ad8d063018a5625587a61a984f612983a60a98045ffd7d95ef97a35e2176d5d4972c5c457015bc56ec5b456b65a9968b59ed65558e961f58115e957395b3566157d55b5568556153d54054db53014b0525546f515143950794034fa13d84ef53a24df13564cc12ff4bbd2df4b112b44a3927e4961248490d23e48b921e48651fe478d1bd468918745dd13b44ad11043d50da42fd0af427d08f41fd06f41a905a415503a40d50254054ffa3fd4ff03facfe63f84fbb3dfcf4e3c74ef73b44eab3a40e8039c0e4a38bce1f37b8dde3764dc93710da9360cd683534d3d34b4d1233dccd132d8ca63200c703154c4530d4c253028bfa2fa8bda2f28bba2ea8b9a2e28b852e00b7b2dacb5b2d2cb3b2cacb1b2c58b062bd8ae62b58ac62ad8aa62a58a862a04a7c29dca672988a5d2960a3d2888a1227dc9d127049b126b09a7263098725dc967253093c24b091123d88f123848c622d8890220085a2128845210083020ac810202c7fb1fac7d01ed479a1dfc76f1d7c7441cd07241bf86ee1b4c6c31aa06981a2068319cc64d18f463818485f717445cc171c5ac167058c15f056c1570541149850b13c04ca12904941210453110c42810603fd0fb43dd0f343bd0ee03a80e603880de03680d603480d0c3330cb831e0c643090c102ff0b902d40b102bf0a902940a1027409902540910234089021f08682150840200068c15104d811b else (if i < 5 then 0xb998888f33100200b8cc60002108210131010026202601440541188280141013028054604c29c1118050800a0191013406286c10a74cd088c08013100d008200c0340201a2042e0c040604c0008000131733e0c20270cc0b8c1f040281003c3020078240c0581e10000914907c900281e184802620a7ccc404383080c8402013072303205441200c888984811130342c0c014080c22013101300a208010841082108200c0108298131003092200004c40400e880801d101003a200e0744040020808013100508050622e22070240c2107088409c1109038220685045998041b330082040100a1036070406c0e080911b101b0382036070404c204c211c108800040c84a10050a02024128400020902381e1806032200c0705c902801e18000ac0f080301c100b04420040b8404c204c20302430200c200c240c2140108b03040e8211059044200c074168c00fc280806041e054105706e22661402a0c21054103d0a822660b82a0c0102e100c080600a17860142f021181d042203a084407410880e821101d042201810b2078416c11080e821101c080c081d0422026102612981c0c1016102610000c90200c240c204c2003a084402c108809841f02e1000081905c2028100c0644007e1a0c1e0c158170c015c2302e185903c20b207841640f082c81e105903c20181781c0c2c821100b0d0608005821103f0a020061016088400c20cc1481f18030b022b2088416c11082d822105b04420b6088416c11082d82210030800184178541706e481082683a28020b0084616c108a2c842d82210330600e8600c2e882985d100c0742467c904058108801840b021105505020800e4168c0603d05c30680b8118c2211107a0b8800c280c200c0e0809841b05c04234221e481400f0d08840002610061003e0a0282280c40241181818140622028070584420500cf330400b0b84428e516080081c100303820b6084407020702070207020702000610411406200030813085c042200000004004c0f47ccc02724076128a10c1a828042407e0f41402120330540e060f428023180609e0e860301d08888488840c81407430200e8444420400df330424222101110800b0211024012174600c0c882d82210030803082e03c202c084409c2801e185b0442006104e094188c0184018191403080308030803038280612581806108010801c0c1004102610000c9020302030243038182008200181a221e4810181018101812181018121810000c90200000b021100205a2026100a088414c1002e180c0e0608004cf9208100c300c200e888a01860484158281006032200000b1105a24221e22120188d830792050050360c1000098414190608103038443c4416898882d100c05a24220b440b4344434441688888488840d8050623a221028070406c3444168983058 else 0x50e480647c9028005180503a2080108401009880104410130002a6741840642208220408004101b008202004c40740c880604310440262032058410000080c816100001620160644110018820804101a0262066010208c21053e6630260004154201429f3318420a1ccc610)))

def moveIndex9 (i : Nat) : Nat := 0x20a3c261066806511b41ca0b6c3320d6c05200f0400000e10b0a701e605200a10ff011e03b834709f81790c50253087809207c0000002c3e0000000a00143d705ac2a90cb815e090000e03e42200000005048000e06a600308d437f02c0000000c04b0ee80d00024429009039e01ec2fd076810a06d83650b241360e384180f0c20c004000c0eb04580c182b1113008310cc0cf06079ec0b8d417300102049941109000100040081008002084043

def liveData8 (i : Nat) : Nat := 0x1c661000000038183a48105b019100d8400e1108189020a6101c08080414c207a1002984040202010530829840c4810000078101308098404c202610000000000000000000c48161108000261d1102d100c44262210188840622101b0211188840580b44c4816110e7d96e5191e3d8ce2987dfd76da15fd755ad494fd1d3ecd92dc951cc6911c2500be0efbb4e4b88dfb74d4b30c3aecb2ac0adaaca8a98a3a849ea7099a5c94a488fa34849f0799dc6e9805d9544c928418fc368a01f844088014bf6da99a21715025deda554c1ae2a052fdb6a65835c540c77d544c2e6a0a8166f6dc835c5415029f6d953344262a046fdb6aa9974c5408fdb655532e98a812df6d6aa61d315029f6d9532c3a62a05addb628d874c540b76b6e4c28298a811bf6d8a99de115023f6d915319c22a04ef9b6aa9714c14086fb6a54d113ba8125f6d6aa61e7750293eda94ecb106a052bdb429d9620d40a5db6453b2c41a814bd6c4a76588350297cd814ecb106a060feaa9dd9620d40a1fb6e50b2c41a8149f6d4a16588350295eda142cb106a052edb22859620d40a5f36050b2c41a814ed2e1a4644735025aedad54c3c66a043bdb42a6888cd4085fb6d55330b8a810df6d6aa6617150217e5cb4c41ae2a062bda6650831c540957d76d3106a0a818afa65a620d4150345f3bb4c41a82a043bdba2607350540c57930d30e6a0a818eb261a21cd415031da4c34239a82a063b8986807350540e339313bc66a0a813e6aeda3241415033cccbb4648282a06b998768c9050540db34eed1920a0a81be46c5a3241415021deda554cc262a043edb2aa9984c540bf236051a8298a817e46cca0505315025badad54c3c22a04bb5b4aa9838454095ed76d310708a81a3d9dda620e11502d5adb106a0c22a04f39b52a5414c140bf236848a62982817e4aed414c5305037c95528298a60a05f90b9505314c140ef2532a0a6298281ee42a1414c530503dc94428298a60a07b9187505314c140fb24eea0a62982811cf6d4a9505305025bcdad54c3c00a04bb9b4aa98380140

def liveLevels : Nat → Packing
  | 12 => (1,1,7,0,0,0,0,liveData12)
  | 11 => (28,2,7,0,0,11,0,liveData11)
  | 10 => (302,3,7,0,0,14,0,liveData10)
  | 9 => (471,4,7,0,0,14,0,liveData9)
  | 8 => (71,5,7,0,0,10,0,liveData8)
  | _ => emptyPacking

def liveIndex : Nat → Nat → Option (Nat × Nat)
  | 12 => lookupWord 19 41 4 9 5 0 moveIndex12
  | 11 => lookupWord 103 342 7 16 9 3 moveIndex11
  | 10 => lookupWord 162 532 8 16 9 3 moveIndex10
  | 9 => lookupWord 29 87 6 14 7 3 moveIndex9
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

def orCols : IndexTree ColumnInfo := (.fork 47 (.fork 23 (.fork 11 (.fork 5 (.fork 2 (.leaf [(0,1,332,50,7),(1,0,382,0,9)]) (.leaf [(0,2,312,69,7),(2,0,2429,0,9),(1,2,312,68,6)])) (.fork 3 (.leaf [(2,1,332,48,6),(4,0,2427,0,11),(2,4,2417,8,6)]) (.leaf [(4,2,312,65,6),(6,0,2425,0,8),(5,2,312,64,5)]))) (.fork 6 (.fork 3 (.leaf [(0,8,99,276,7),(8,0,2423,0,9),(10,0,2417,0,5)]) (.leaf [(12,0,2419,0,8),(13,0,354,0,4),(10,4,2417,0,5)])) (.fork 3 (.leaf [(16,0,367,0,11),(1,16,358,8,6),(17,0,366,0,8)]) (.leaf [(18,0,365,0,7),(18,1,332,32,5),(19,0,364,0,5)])))) (.fork 12 (.fork 6 (.fork 3 (.leaf [(4,16,354,9,6),(5,16,354,8,5),(8,16,358,1,6)]) (.leaf [(16,8,99,260,6),(24,0,359,0,8),(9,16,358,0,5)])) (.fork 3 (.leaf [(25,0,358,0,5),(12,16,354,1,5),(20,8,99,256,5)]) (.leaf [(28,0,355,0,7),(13,16,354,0,4),(29,0,354,0,4)]))) (.fork 6 (.fork 3 (.leaf [(26,4,353,0,4),(32,0,2399,0,11),(1,32,94,256,6)]) (.leaf [(32,1,332,18,6),(34,0,2397,0,7),(34,1,332,16,5)])) (.fork 3 (.leaf [(35,0,348,0,5),(36,0,2395,0,8),(17,32,78,256,5)]) (.leaf [(49,0,334,0,7),(50,1,332,0,4),(51,0,332,0,4)]))))) (.fork 24 (.fork 12 (.fork 6 (.fork 3 (.leaf [(40,16,326,1,5),(56,0,327,0,5),(41,16,326,0,4)]) (.leaf [(57,0,326,0,4),(64,0,2367,0,11),(2,64,2109,256,6)])) (.fork 3 (.leaf [(64,2,312,5,6),(66,0,2365,0,8),(6,64,2105,256,5)]) (.leaf [(68,2,312,1,5),(70,0,2361,0,7),(69,2,312,0,4)]))) (.fork 6 (.fork 3 (.leaf [(74,0,2353,0,4),(72,4,2353,2,5),(74,4,2353,0,4)]) (.leaf [(78,0,2353,0,4),(0,256,2071,104,7),(256,0,2175,0,9)])) (.fork 3 (.leaf [(258,0,2109,0,5),(8,256,2071,96,6),(256,8,99,20,6)]) (.leaf [(264,0,2167,0,6),(260,8,99,16,5),(268,0,2163,0,5)])))) (.fork 12 (.fork 6 (.fork 3 (.leaf [(273,0,78,0,4),(272,8,99,4,5),(280,0,103,0,5)]) (.leaf [(276,8,99,0,4),(284,0,99,0,4),(288,0,2143,0,8)])) (.fork 3 (.leaf [(290,0,2077,0,4),(40,256,2071,64,5),(304,0,79,0,5)]) (.leaf [(273,32,78,0,4),(64,256,2071,40,6),(320,0,2111,0,8)]))) (.fork 6 (.fork 3 (.leaf [(258,64,2109,0,5),(262,64,2105,0,4),(326,0,2105,0,4)]) (.leaf [(72,256,2071,32,5),(328,0,2103,0,5),(96,256,2071,8,5)])) (.fork 3 (.leaf [(352,0,2079,0,7),(321,32,30,0,4),(290,64,2077,0,4)]) (.leaf [(354,0,2077,0,4),(104,256,2071,0,4),(360,0,2071,0,4)]))))))

def orForest : Forest := ⟨2431,12,fun j => orSamples[j]?.getD (0,0),orCols,orSymmetries,liveLevels,liveIndex⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem orGeometry : graphValid orForest (boundsBefore entries255) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked12At0 : block orForest 12 0 1 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked11At0 : block orForest 11 0 13 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked11At13 : block orForest 11 13 15 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked10At0 : block orForest 10 0 2 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked10At2 : block orForest 10 2 56 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked10At58 : block orForest 10 58 17 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked10At75 : block orForest 10 75 56 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked10At131 : block orForest 10 131 56 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked10At187 : block orForest 10 187 56 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked10At243 : block orForest 10 243 7 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked10At250 : block orForest 10 250 52 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked9At0 : block orForest 9 0 10 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked9At10 : block orForest 9 10 56 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked9At66 : block orForest 9 66 56 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked9At122 : block orForest 9 122 56 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked9At178 : block orForest 9 178 56 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked9At234 : block orForest 9 234 56 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked9At290 : block orForest 9 290 56 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked9At346 : block orForest 9 346 21 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked9At367 : block orForest 9 367 56 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked9At423 : block orForest 9 423 48 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked8At0 : block orForest 8 0 56 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked8At56 : block orForest 8 56 15 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

theorem allAt12 : block orForest 12 0 1 = true := checked12At0
theorem allAt11 : block orForest 11 0 28 = true := (@block_merge orForest 11 0 13 15 checked11At0 checked11At13)
theorem allAt10 : block orForest 10 0 302 = true := (@block_merge orForest 10 0 131 171 (@block_merge orForest 10 0 58 73 (@block_merge orForest 10 0 2 56 checked10At0 checked10At2) (@block_merge orForest 10 58 17 56 checked10At58 checked10At75)) (@block_merge orForest 10 131 112 59 (@block_merge orForest 10 131 56 56 checked10At131 checked10At187) (@block_merge orForest 10 243 7 52 checked10At243 checked10At250)))
theorem allAt9 : block orForest 9 0 471 = true := (@block_merge orForest 9 0 234 237 (@block_merge orForest 9 0 66 168 (@block_merge orForest 9 0 10 56 checked9At0 checked9At10) (@block_merge orForest 9 66 56 112 checked9At66 (@block_merge orForest 9 122 56 56 checked9At122 checked9At178))) (@block_merge orForest 9 234 112 125 (@block_merge orForest 9 234 56 56 checked9At234 checked9At290) (@block_merge orForest 9 346 21 104 checked9At346 (@block_merge orForest 9 367 56 48 checked9At367 checked9At423))))
theorem allAt8 : block orForest 8 0 71 = true := (@block_merge orForest 8 0 56 15 checked8At0 checked8At56)
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

theorem noRun : Impossible (graphGoal 2431) 12 (vars 2431).toFinset :=
  root_index (g:=orForest) (before_sound _ sound255) orGeometry orTables
    (k:=12) (by decide) (i:=0) (by decide +kernel)

end Free383

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound383 : Lower (vars 2431) (graphGoal 2431) 13 :=
  augmentedGraph (k:=12) (m:=383) (hints:=12901687556) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (before_sound _ valid383 383) (by decide +kernel) (by decide +kernel) Free383.noRun

def entries383 := extendKnown entries255 13 [(2431,[]),(2495,[118,130,81])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound383 : Known entries383 := extendKnown_ok sound255 seededBound383 (by decide +kernel)
namespace Free479

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem noRun : Impossible (graphGoal 2527) 11 (vars 2527).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=2527) (128,0,2399,0,11) _ (before_sound _ sound383) (by decide +kernel))
    [] (pool:=(vars (poolMask 2527 (128,0,2399,0,11)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Free479

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound479 : Lower (vars 2527) (graphGoal 2527) 12 :=
  augmentedGraph (k:=11) (m:=479) (hints:=13438558468) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (before_sound _ valid383 479) (by decide +kernel) (by decide +kernel) Free479.noRun

def entries479 := extendKnown entries383 12 [(2527,[]),(2557,[130,114,49,98,81,64])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound479 : Known entries479 := extendKnown_ok sound383 seededBound479 (by decide +kernel)
namespace Free503

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem noRun : Impossible (graphGoal 2551) 11 (vars 2551).toFinset := by
  exact poolCut_sound (poolColumn_sound (m:=2551) (16,0,487,0,11) _ (before_sound _ sound479) (by decide +kernel))
    [] (pool:=(vars (poolMask 2551 (16,0,487,0,11)))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Free503

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound503 : Lower (vars 2551) (graphGoal 2551) 12 :=
  augmentedGraph (k:=11) (m:=503) (hints:=22028484868) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (before_sound _ valid383 503) (by decide +kernel) (by decide +kernel) Free503.noRun

def entries503 := extendKnown entries479 12 [(2551,[])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound503 : Known entries503 := extendKnown_ok sound479 seededBound503 (by decide +kernel)
-- Setting inputs zero and four to false makes three live wires
-- constant. The remaining seven-vertex graph needs eleven gates. The
-- nine-vertex search below combines this restriction with the preceding
-- induced-graph bounds and the automorphisms of the target.

namespace Free511

def liveData14 (i : Nat) : Nat := 0x6e160280a02260f02c8ffd40

def moveIndex14 (i : Nat) : Nat := 0x62de32dd079fc4211200000ace2800007ba180139750039b51b9bc2ca530ac9cd023b300000400

def liveData13 (i : Nat) : Nat := 0x8b20a8088a13a16301f37459010151e09d0b208b8b20a8146e9303e859137415028b21f42c69ba2c8140a9303e858e044dd164142707d0b1e2c8f205a281302a4c8f8164cdd1640b01015264790b200a9ba2c808168f01f139137459054051e09d0b1c0a9ba2c814160f81f930454cdd1640a0e4981f02c22a26e8b20a8164c0fa16383f3745902c780b4991f03c9866f79c4b485faac9299fe3525787f8aa0be003ffb04a07ff4c940ffec0a81ffd51503ffa62a07ff48540bfec9a81fde33502ffb24a07fb88940bfec8a81fbd41503fec22a07fe4c140

def moveIndex13 (i : Nat) : Nat := 0xe02c89309624208252eca6585f60aba061427d854428ba4cf01ce064e2740473c91e83e70e9c1194100827006ae4bd8291109c0a2a1358a76183c063a485c9a383690d7c038830c117d0a0006c0001111c28c000000078437105e03182418321206213003ac85ce0dc021408b502fa09c0000c22385ed27660e202030290001403f081000040ad458ec3de11fb0d9620343e502b000000000003042b01a0002ca8391440340002c22e17810d3a1e9b84a83cd09521758334030807ac029308f84b602400034008028a055e195c0e2819228e00010175859d1038162495a8670001a090000102d426e00000346814200400020a7800000000003f29285af218c099038992db03da1cf809ff11a0f1a4ba00a8000a0e524054bb000032b220cd8b8585b82502089c9ce805a26de00ec427810926000b0c3f411a521561fec1a1070821124c54afd01f2287c5ad0abf047b10621de83c887dc02e05c7836e16a907f2019c02695a00c600eb01dc95b4c132474886b138d023a4a4c314016106e60760a128002047a1d9ca6b86f70922580403e06a9042615f8800060c2c201064048008b04bc14e4870712a51012801abe2608a000a241804e00083001484d0614f00020056a00103122c14a800278300421c98d085809008080b6080438a26004180200008

def liveData12 (i : Nat) : Nat := (if i < 1 then 0xb1d0566ec588590fa4e87c7cdd8b30524e87c1a70b1f3762cc0b8f32663e03e70159bb1663cc7c9380f9e0fe6ec598f20563e49d05900533764ccb39391f01f381fcdd9332ce4e47d058f07f3764ccb305b2723e83c8b1a2c2caf96ba9ad32b10ab26a77a8969b2a4fe903a34a896a0ba7bb9dfe72d9b9a6aa9886598954650a925e4668fce3758c8e2bb89a6222876e17e84b20cf822202b7ee1f5b7c51eb778e5dbb7579ce07265c526fa9b986d19ad36a05a0366f1980648d8c661a58175ebd7525ba968258c15d355d9524531d47550b93e74ead3644c1d29449351f0462112b433905b4024fb73dc0f1e3b5ce903924e023694d4833acc833098bc92db0b252b78a9729149fe26b096523f48b621648121f5878f1d206f61abc66818845cf162053613bc49211003e30e703550be02a6095020206c015e04040af0174000fffaa982503ffda360940fff68582503ffda84c940fff69532503ffda14c940fff69581503ffda360540fff68981503ffd5260540fff4c981503ffeaa54540fff68d51503ffda254540fff60951503ffd3254540fffaa931503ffda84c540fff69531503ffda24c540fff60931503ffd524c540fff6a121503ffda548540fff61521503ffda348540fff60d21503ffd5348540bffaa9825037fda960940ff78cd82502ffeaa4c940dff6a532502ffda84c940dff66132503fed824c940ffb60e225037fd8364540dff609915037fd3264540bffaa9815037fda960540dff655815037fd9360540ff78cd815037fd9260540eff60981503fee2260540bffaa9515037fda954540fef691515037fd9354540ff78cd515037fd9254540ffb88951503ff58154540fef60d41503fbd8250540fef54941503fbd3250540bffaa9315037fda94c540bff6a1315037fd984c540effa2131502ffda54c540dff65531503fbd544c540dff64931503fdd324c540ffb88931503ff5814c540bffaa9215037fda948540bff6a1215037fd9848540effa2121502ffda548540dff65521503fbd5448540bff68d215037fd9348540ff78cd21503ff53148540ffd61611503ff58384540ffd54e11503ff58284540ffd54a11503ff53284540ffe68930503ff9824c140ffe68530503ff9814c140ffe54530503ff9214c1409ffaa9935027feaa64940df78cd925027fda960940dfb66222503bee8888940ff38ce225027feaa64540cffa21915037de3364540dfb889915027fda9605409ff6a551502fbeaa50540def66141503bbe8850540bef69541503f9e3350540def64941503fae22505409ff6a531503fb5414c5409ff6a5215037f59884540efda22115037f59584540fdd95611503fb55484540dfd64e11503fd63384540dfd64a11503fe62284540bfeaa9305037f9924c140ffa88930503fb9414c140ff64c530503ff2114c140 else (if i < 2 then 0x8590090548a89d858f9bb1663cc7d8582a983ae2cc798f80f85530750278b30140a51513b0b2007e02c580a62728a03e70eb8b30104e81414545616422c40482a2728ac2c60e621f266594dd93a1f01f40130301d71641680507d4524e88aa02203f3762c49d0f83481f460ac9996727616116687c8b10564cc9c8585308c401306a82a45e0542d1b92ca1f87c981604c1048bc9996509c6e4159390b43e581c8590163720ac990fb0b200981941422f1640242c87d2748a08cbc5982a1f61649c118d0b20546e49d0fb0b1809805cdc0c30501b8b30fb0b2702e6ec150f90b4590d47c0b9b90e43e8b2858351c180130419bb02a1687c87a2c84a546e80a8280e45987d858e0c00ca0a0279b902a1c42d0fa2c8465c6e8148161f459c2c6c158594545908c545905937605c9821e1f01f4013c5900a0e28a82c93a22a12ee6e4590721f41649d11500460b66ec5893a1f01f381300b9bb1640ac980461f6164e6ec998145065987c1a00fa009805c589b80dc0ac990fb0b240600a0539332cc02c9ca280fa6164054dd02b2643ec2c70260173701b8149661f61640350198173702987c9640fa202e6e42c0a61f25903e702206f3762c87c9383481f466ec580461f61649c118f1ba1640a49d0fb0b1b1664c81585945046366ec5982b0b0692a0acdd8b0072160d260278b00be0a4dd13a1f61640080ec0440e62c80485a2728a054a8590293744e87d858c04c3760a1090161f259c2c806a0440e66e80a85a1f259054906a0733740542d0f92c82a4013cdc05f1620a89d0fb0b20040130419bb1620a42d13a1f02a501c8dd0b10544e87d858f9bb1603e41585a270463a0a40a9ba1f259c2c64588160120ac98a2b0b1d372054150f92ce16322c4150092728ac2c64dc82902c3e4b3858c9b91620a87c93b0b1916202c79a2a0b24e09207d007f16602814a292741613084dc8172665982c28d1f01f428b83f9332ca6e82d9391f41e481fcdd8160b23e4b307825200fe6ec590592741e47c0a919bb1660504180b2663c03e8cdd8b30163c89c07cd8f31668ac7d1380f980562cc0522a2701f320ac598090b21f515138f8b30560289ca2b0b1b3762cc0482b1e44ec2c7cdd9332ce4e038114d02b1660580505a0fe4c51511539bb26659c9d0f80f9a0566ec5905a1f41f49d11519332cc6ec9d0f80f9b376058b30f80f973764ccb39380e045364ccb29bb2743e03e6c599313741cc9d0fa0b1f376050009661f01f366ec999672743e03e6cdd8b12743e0d207cd9bb1624e87d07034c163e6ec999672743e03e642d9bb26659c9c0f80f9f3762c89d0f83481f320ac599313721cc9c85a1f231660ac0a9bb2643ec2c74159bb02a164b287e1f260466ec158152cc3ec2c6cdd8150e43e4b2858d9bb2665942682b2721687c8cdd8b302a0ac990fb0 else 0x22c40513a456160ea641513a456160ea5c5982836c4e47d858c07145051c2c1d4a0700226e4048b31e6160aa80388fb0b051054542d0f905259118118c85b2643e4b2828460463a1649d0f905259118118e06c4208b0bb82902c6e4b30fb0b280d88b03803f1646e41493a1f61650020600d4178462e1641429c23130b60a49c11853940d82f0e182902a6e8b30fb0b240d82f01f9b80e42c41493a1f616500c03007010846281cc9985a0528acb2118e0730b66e81496423180e2050220a42314088750380403d81bc589ba0524e87d85980cc0881c0201773701b45902a1f24ec2cc42c9b91620a0d2118c8593720a45814023180b8330109b80888180a9661f61652160100a423100b81c4580213708141513a1f61650170660c80e008cdc8b10543e89d8596073166020eb22a276163a0a10182b0162c89d2290b06c481c))

def moveIndex12 (i : Nat) : Nat := (if i < 1 then 0x99a5a9b24e800018440000000b6000000000000000000000183a60000b020000020372e11f9095305140001a1a4723f60779c0648015b0a10000383b400ab00005834b021c000032672965840e004d200000000303f2000062ca086d780cc000080bb48316b13464e2f28779057028ec2150000015adc9c344a110898049bc1e400f7b0d4d916509cfa4dee047c884a40da000080836063bc27a651c02def8808c1ea0000000069500829985e972a9607fa032420972215c84cb3c1660f6330880000000060ba507d315fe4ab26136000021634491f01ccc0fc00001003ea53a8005800000867c5959028085b4c82f6028a2c8115cc000000000000501968439e0c3a093e82c1442d85ac0084403a400ce000010de9804202a9a01ad055011273041c41000004927e03da620aa073f12954843a0aff006f078e82dc9832000051180c16c4124402e601fac1a9441210dd815dc0001049780d6387240001658e62cbf9821c1c825e690b00000380c400007017990780331413af080806d0000000000000383b5880b8089e0cb392d4822a80181cb1e00ce8011808d82237840dcadc044200003876340b341df12e89087f498cc201400c8036a82522520f0a58000242bf0024d079e8783c015621822f86068a4991c079b10f101cd4042e4dc106e00341823a84a070eb80003c224054ba094007e902df0123b26d1966b80ef41fc32c478452c233a01d22dc0841e89adc59342d8a0286088ec14e1022982fc026a2219b267b97568aa6e5e7b2152003c094fc17c4108891c54388a408f064e9152c335e14ae07a51540895d808502a570590407b60c15202182e54364c46b0000605e2f199a1d66028814fa8271a047706508629c35e808e601e39738831b41dc4291201f008be25cdc08e682e389240000500f30309c408c159d0f5a86648b8c0080825b184448909209590af117ffc10ec0c000002977c4a8ce0b3b069a0266c1a20000f2121061401c681f5c0ea808878412a1462251c946f423161c2045109201b150aa8493d0109000000180100050202070000271400120124190b0f0f01061a07008b02730c06000e09131422070f034c0c010700000109020b0d0d11004606010b000e010a0500111e030300010407010019020005021c2d21120f0002000258070100072309530609000b0501035b0500050b552d0000020c15000c0409010011022c150a02001a0806080f25010a02001e1413001b061300070112010f11011e000300000b16150101050007011e010503030000050105000f000404040209000300000005010004051900020301021321100019000004010200420102001304090500080000010701000c0023060000010010070a17032201030301030801000007753502000b0007000202001002250008020008010a18080500 else (if i < 2 then 0x848258c968249120f7011d0000000005050000010bac0000a0a7b031d4a8519cb5cb2318818039d91652117880d8aea45c9103708833ca34c20560b0e03fc83ba017270b821250034e40d70000191758921c0a5f20dc05fc8366a13420a0c92a5ca3e782e6280793a242b605d9929c812a1c30e44d5000028625c245440ea2f758355c20aa1e600a26043e03d4009cd0420874740ff400ea0e2c00e8838e00fd501f887a6497241d980cab17074858801422f52068cca68a001907cb16fd4bb9814d125c186844319a54dd2a1907228a1120fbde8c79750004f002e929e90500899b8006b21a605e982046517c066404580000416b022d80002f85f615170488060cc2b4e554503c6184249de1cb7f0625846dc35ac4d4d04ef87ce0af2047d4088585c74997209a9208913940000000080e7e01ec000060bb408bd97130063c5c39261915790c0f204de303580a9c02cc499f07c208384243a0cd7239306228428e0221046114418128602b53049906140b4004930ce60734719ec0b2a2e4301ca8382600c50fbe01524323c5aeb24d396e5c9676093c2ba016100131a43ac0d5182b5c0aea21bf00938483017d04c70103582f1cbc1e053d03a082c54200620f80fe891cc4041413750dfd086bc3e87c3270637808c43fe00e1d022083998427448ea21b605a3c8e1801b80526168800844498b30f6879c0a0e01f6d09da0738033a60d6a02740321c25aa425c08d20221434b80370024117d189b724aad21710699c0b7453592ac0000000000060b0d58827b8258e09fa0860922b805a021722aed042c4370000000e8692bc41c440cb92ed987a18959a01310abe050e43b6209b000019418000000006040f867c0000c169c2da8000000000000e018000000001659c225bd054f88cfe182f0410000000000000101dc901e407021790098000994267046d00853929a4396c0d8b100301c600f5e0dd52049170a0c32c04f70ca280a40b224005a08268397ba93221d9c18200010121a041b0bf5943d80bee5eb9255d054182ce00000000692b7c939806b403ec0790034181d400005858e08a16131907e30605025ce15cf0c9a90ca8362d96280a4a837e4a92a18b20d4684f9493ce0b4502f506db036f61c392277863c884d6190d29189173c30cc1e2221ae024a019d843740c2483a142e9e1090029281a8f944406ce045504bd4960e1e54086800008022a06812ad8000141e220040000580fb82ada1f12309a18774394e035a041f859ac1bd04cc82ddc038082abe148e021896e9433d460a003b705d6c00541ec90df0152300ada4feb054d123083e0e1d20231f028dca0b20b73cff104fd040e4025620e2871a82568461023248298819e25e8c075380260a7180fef0b2c64628a9f020d105a805cc82d560640000580d182b1e0db30bd8870340 else 0x5d50f080000c9360000d034d9074027881ae7309682b843e40482a0a950497c32ec55a30250882e02bba21090fdc110e41516453f234714f202efa075d08f592ca8272647b71040829c4bd8a4c40000203b8f144000070767028ac963e0eb702c106f10be5a537000000002c0de00000000087bd802f2046000011316800e00006001a82b3c2c40000e030803c240ab05bc0000103640000000090dd000d9410c0000e21c800000000402ce214780e7c8c5a17df031d02f4c09685ef2216983bdc871e08bf22f2137d4a2c000052ff491608300a19b30d))

def liveData11 (i : Nat) : Nat := (if i < 4 then (if i < 2 then (if i < 1 then 0x54a11503fbaa9aa508a81ff58cd5284540ffcb04a9422a05ff6bb4ca11503bfadca6508a817fd6e13284540efeb3099422a07bf6884ca11502ffadaa6508a81dfd6553284540feecaa99422a07fb5544ca11503ff2c126508a81ff96162284540ffcb0711422a07fe55388a11502ffd5db44982817feaed824c140bff374c1260a06ffaaa60930503bfcdcb0498281ffa6a2224c140bff576d0a60a07bfa88685305037fcd134298281ffa889a14c140bff576c0a60a05ff9ba605305037fd5530298281dfe649814c140f7f304c0a60a07fea2260530502ffd5daa2982817fe6e9514c140dff554a8a60a07fb9b454530503fecd9aa298281dfe649514c140ffd444a8a60a07ff18154530503fdcc128298281fee549414c140ffb57698a60a07fd9b84c530503fecd426298281ff66d5314c140ffb34a98a60a07fd9b24c530503fecd126298281ff6609314c140ffb2a498a60a05ffabb48530502ffcdd24298281bfeaa9214c140bff37090a60a077f99848530503dfd44242982817fe6d5214c140ff72a890a60a07fd95348530503ff8d442298281ffc696114c140ffe30b08a60a07ff1a284530503ff8c142298281ffc54a114c1408ffb7155324a047fdb5aa9925023fed8d54c92815fbaed9888940ef9b3119c44a07bce888ce225031ff55510c8a81cf7a223364540cfdd5511322a073ee8888991503be719c44c8a813bf6daaa60540cfdb5311302a047fcba649515033f6d4c44a8a81aefaaa8850540f73d1119a82a073be88649415037d755444a0a81deb6622250540f75d1111282a06fada588941503fc719c44a0a811ff2e9984c5408ff974c9262a06fb6aa50531503ddb4428298a81fe54c9414c540ff4c44a0a62a063fda9a2121502bfb5db3108a815fdaed9584540e7ed10cac22a057f5b961611502fdb5daa908a81ded6615484540f76d10aa422a057f6bb64e115039fb4432708a81ddd9559384540afeb72c1c22a057f5b954e11503f9aaa2a708a81df56623384540f7ad1119c22a077d5958ce11503fab2ac6708a81fe55523384540afed76c9422a073f68864a11503bbb2ab2508a81ded5519284540efac66c9422a057f5b960a11502bfadcaa508a815fd6e53284540efcb3111422a07be68888a11503bf2cac4508a81fd99562284540ff4aa911422a077e59388a11503fe319c4508a81bfaaaa224c140efd33111260a07bea8888930503ddd4428298281fea889414c140bfb57698a60a06fdaaa4c530503beccc26298281ef6a21314c140bfb36a98a60a07f99544c530503becc926298281ff2889314c140ffa30298a60a07fd131485305037f95542298281dfc662114c140f7e51108a60a07f725584530503fd8aa42298281ff454e114c140efe32508a60a07fe222845305023deda554c9a81fe4505314c140 else 0x81eefa213250540ff5b0499282a07fad83889415027fedc55498a813ff6d6aa4c5409ffb6555262a067feaa6a5315027ff5db5098a819ff6e5a84c540cffb52d4262a067feaa661315035ff5551098a81cff6a6884c5409ffd76d2a62a067fdb9695315033fed4b4a98a819ffaa9954c540cffb50caa62a073fe88655315037df552a898a81bef6a1544c540f77d10aa262a067fda9689315033ff5532498a819ff6a1924c540e7fd10c9262a067fda5649315027fe5d30498a819ff6a5824c540d7fb50c1262a067fda954931502fef5da6498a81bf7aa9324c540efbb7299262a077dda94c931503beecc26498a81ef7a21324c540efbb2a99262a07f9d544c931503fe6c126498a81bfbaaa224c540efdb5311262a06feda888931503bf6cc44498a81efba22224c540dfdb4b11262a077ed9588931503fd6aa44498a817fdaed814c540dfed54c0a62a077f5b960531503bfad4b0298a81bfd695814c540efeb2ac0a62a07fb55460531503bfac930298a81efd609814c540ffaa64c0a62a07fe62260531503fdb5528298a81fed6a1414c540ff6b4aa0a62a07fb5a250531503fdac128298a81fed549414c540affd76d4a42a04ffebb6a1215033fedcb5090a819ff6a5a848540affd76cc242a057fdba661215033ff5533090a81affaaa8848540e7fb5344242a04ffebb695215033fedcb4a90a819ff661a548540d7fd10d2a42a067fda969521502bff5db2a90a815ff6e99548540cffd54caa42a067fda8655215039ff4432a90a813ff6e98548540cffb52c2a42a05fbebb551215037df552a890a81bef6a15448540ef7b30aa242a07bbe88551215027ff5db4690a819ff6e5a348540cffb30d1a42a06bfe8868d215033fecab4690a81bef551a348540cffb52d1a42a057febb64d21502bfedd32690a819ffaa99348540cffb4ac9a42a04ffdba60d215027fedd2a690a815ff6e55348540fe7aa8a9a42a06fdeaa8cd21503beed4c6690a81bf76a23348540efbb3119a42a07bde888cd215037eed2c6690a81df76563348540ff3aa919a42a05ff6bb4c5215037fb5526290a81dfd6e53148540efeb5298a42a06ff5a84c521503bfacc26290a81efda213148540efeb2a98a42a07fb5544c521502ffb5db0b08a81dfd6e58584540efeb0ac9c22a05ff6bb60e11503bfadcb0708a81dfd6558384540ff6aa8c1c22a05ff6bb54e11503bfadcaa708a817fd6e15384540efeb30a9c22a07bf68854e11503fbac2aa708a81ff560d5384540ffab0b19c22a077f58564a11503bfac1b2508a81dfd54d9284540bfed76c1422a077f5b960a11503bfacab0508a81fdd9558284540ff6aa8c1422a077f59360a11503dfac1b0508a81ff58cd8284540bfed76a9422a077f5b954a11502ffadc2a508a81dfd6615284540f7ed10a9422a077f593) else (if i < 3 then 0x50caa42a06ffeaa61521503bfed4b0a90a81fef6a15448540effb4ac9a42a077fd8564d21502fff5db0690a81bff6e98348540dffd54c1a42a077fdb960d21503bfed4b0690a81bff6958348540effb2ac1a42a07fbd5460d21502fff5daa690a81bffaa95348540effb72a9a42a077fda954d21502ffedc2a690a81bff6a15348540effb30a9a42a07fdd8354d21503ffac2a6290a81ffe6c5824c140fff374c0a60a07ff9b560530503ffcd2b0298281ffe6c9814c140fff344c0a60a07ff95260530503ffcd92a298281ffe609514c140fff37090a60a07ff9a848530503ffcdaa4298281ffe695214c140fff30a90a60a04ffdb3aa9825027fed8d54c12815ffaeda960940cffd54d4b04a077dcb36a5825033fed4b46c1281bf7aaa3360940efbb5319b04a067fda9685825027ff5db50992819ff6e5a84c940cffb52d4264a067feaa661325033fed4b4a992817fbaed824c940dfdd54c1264a077edb960932503bf6d4b04992819ff6a5a14c940bfdd76c1c44a077edb960e22502bff5db06c8a815ffaed8264540cffb74c1322a067feaa609915039fec1b04c8a81df78cd8264540affd7699322a057fdb84c9915039ff44264c8a81dfb6093264540efdb0711322a057febb6a5815033fed4b4ac0a815ffaed9560540affb74cab02a067feaa655815033fed4b46c0a815ffaed9360540affb74c9b02a067feaa64d815037ef55466c0a81df76a63360540efbb2b19b02a067fda968981502bff5db24c0a815ff6e99260540cffd54c9302a077de3364981502dff5db04c0a81affaa98260540e7fb72c1302a073fda9609815039fecab04c0a81ef78cd8260540cffb52a9302a07bed8254981503df6c1264c0a81bfbaaa2260540efdb5311302a077ed9588981503fe719c44c0a813ff6ceaa545409ffb65552a2a057febb6a5515033ff55352a8a817efaeda454540df7d54d22a2a067fda968d515037ded2346a8a815ffaed9354540affb74c9aa2a067feaa64d515037ef55466a8a81df76a63354540ff3b4919aa2a067fda9689515037ded2344a8a815ffaed9254540affb74c92a2a067feaa64951503bded2324a8a81df78cd92545409ff974c12a2a057fdb9609515033fed4b04a8a81bfbaaa2254540efdb53112a2a077ed9888951503df744444a8a81feb6922254540ff9c67112a2a05ff6bb605515037fb55302a8a81dfd6e58154540efeb52c0aa2a07fb5a460551503bfac9b02a8a81ff58cd8154540efeb24c0aa2a07bf58260551503fbaa9302a8a81ff98898154540bf7d76c1a82a05fbebb609415037df55304a0a81def6e58250540df7b4ac1282a07bbd8360941503fcf19b04a0a817efaed5250540df7d54a9282a077bd9854941503ddf442a4a0a81fe78cd5250540ff5b04a9282a05fbebb4c941502fdedc264a0a else 0xfb0ca615ac1e1821b0325ffabef17bdaf525e0abae1741ae2a5beab7016b9ad3e5a12b3b166dac9a58e2b0c1603abd2573aadd159faada5562a9c1517aa1e53eaa6714b9a962525aa44145ba89a509aa0613f1a7a24f0a9d11369a6864c8a97e12dba59a4b1295812a1a52649fa9381267a4be495a921122da42647ca8f511cfa36a469a8cf1189a2f645ca8b2115ba29a451289b112da24a447288a1105a1e2438a86a10c5a16e428a84d108ba0ee41ba8301051a09240d281010119ffa3fd27f00fd79f923f027d90fa39f363e1a7bc0f6f9ece3d7a7ab0f4d9e8a3c927850ef59dda3b4a7650ea99d363a027390e579c7a38d270a0df99bd6372a6d80da19b0e35ca6ac0d499a5234226740ccd995a324a6390c51987a30726010bdb978e2eb25d20b7d96c62d6a59a0b1995e62baa56b0acd958a2ada5540a759486287250409e7939a26e24c9097d92ae24da48808ef9186228a447087390b2211241508158ff61f9a3e007998f0a1daa39f07238e061ba236a06ad8d1a19e232f06498c5e180a2ee05b58b2a15ea2aa05398a3213fa27204cf8952120a231044188360fea1f003b9873e0de21af034986460c2217a02d9857e0a921450269849e087210401e7838206520c001538242043207900d7817a028a047007380b200b20002fff5db42c1281bffaa9a160940dffb4ad0b04a06ffda3685825037fed8b50992817ffaeda54c940dffb50d2a64a077fd9869532503ff6dab0499281ffb695824c940ffdb62c1264a06ffda8685325037fed2b4299281ffb609a14c940effb64c1b22a077febb60991503bfedab04c8a81dff6cd8264540effb7099322a077fdb54c991503bfecab46c0a81dff655a260540effb26d1302a07bfebb60981503dfedab04c0a81eff6cd8260540dffd54a9302a077fda954981503bfec9aa4c0a817ffaed3260540dffb7499302a06ffeaa4c981503bfedca64c0a81dff6a53260540effb2a99302a077fd9368951502fff5db04a8a81bff6e98254540dffd54c12a2a077fdb960951503bfed4b04a8a81fef6918254540effb26c12a2a05ffebb4c9515037fedd264a8a81bffaa93254540effb72992a2a077fda94c951502ffedc264a8a81dff6613254540ff7b48992a2a07fed824c951503ffa99302a8a81fef6c98350540ff7d76c1282a07fbdb560941503fded9b04a0a81fef6e15250540ff7b66a9282a07fbd8354941503fdedc264a0a81fef6d53250540effb30d2a62a077fda865531503fded42a898a817ffaed824c540dffb74c1262a06ffeaa609315037fed2b0498a81dff655824c540ff7aa8c1262a07ff5b160931502fff5daa498a81bffaa9524c540effb52a9262a06ffda854931503bfecc2a498a81ffb609524c540ffbb7099262a07fddb54c931503ffaa930298a81dff661a548540effb)) else (if i < 6 then (if i < 5 then 0x31a2a07c9cdc013c5802307cc9c03e7a1664e83e81f253721662761f20f9685b9330f887c987c4384c0366ea05273a16a59c3e353761f52c83490f970f898087c6cdd87d4b243e4c3ea59a161f2661f11010f919ba82a817932858a930f8f4dd41540b42ccb387c6a6ee4c22cc3e06921f313761f52c83490f9585b0f896487c8cddc98c58c9d87c43e6273e4cc3ee16233761f32ca3490f968299670fb8588c2d87ccb243e4c3ea4e21f1b37516139d0b52761f1a9ba82a8168599670f8d40a42d87ccb243e5a6ea2ca4ec3e21f2d3711610552761f10f989ba8b30fa93887cb87d49c55243e466e62c60a616a4ec3e333752761f70b119b98b182985a93b0f8cc5949d87dc2c4c3e6596161b3731630530b52761f1982a93b0fb8589c7949c83e340aa4e68a41f252734560560b1393205a8fa07c9028c9d47d03e400ce4cc16a3e81e281072651f00f900300280bd9bb9328f826007d1c9947d82c3a3ec166590610982a0b737014d1f32c80f980440bc1ee8f99381b007cec9d47d82c381fe4c017e5968ac16098380ff1600b91f60b52701504c239328f907c7c98d1583c83e4c16e4c68ac1e260b32cd1f60f110528f996507c947ccb382c3a3ec1e64e41f260b51f32760f139bb8b38178f39338f802ce82dcddc99cb247dc9c03e7c6f38d13187e2e6c57b8a2312fe236c40387330d1e17ac2a384d308be0e2c173827303fe056c05b8012feddfb2bf137db2f9bdef6bd3b7972f19de0abbab7682eb5dd42ba3373c2e5ddc7ab8a37072df3dbbeb72b6db2da1db1ab5cb6af2d49da6ab49b68f2d09d9f6b3b366f2ccfd976b2cb6522c8fd8f6b1b36292c3dd846aff35f42bd9d78aaec35cb2b81d6b6acd35932b17d606aba356a2abfd556aa5b5442a73d4b2a9135182a15d402a7b34ec29c3d36aa6834c62977d2c6a5234972919d20aa3c346e28c7d166a2634422869d09ea0eb40d2805cfe29f733e127b3cf1a9dcb3a92737ce469c2337d26f1cdae9ac334e2681ccc2991b31f2635cc4298332f925e3cbb696eb2c72579cabe94fb298250fc9d2936b25d24abc90a91ab228243bc83690031ed23c5c73e8e431c42373c6b28ce318f2303c5de8b9b16f22c9c56a8a3b1432265c48a887b1082207c3e6877b0df21a3c31285d30b02145c262845b07e20e7c18e82e305820a7c12681cb02c203dc04680230001fe5bf7e7e92fcb1f8dbefe7ddafb71f5fbeae7d3af9a1f1fbe167b92f6e1ec7bd667a92f4e1e81bcb6794af191e17bbfa77baee71dc5bb567672ec71d6dbab274e2e981d15ba1a73cae691cb7b94671c2e2e1c41b8367032e021be3b7aa6f02dd01b79b6d66d42d981b27b61a6bcad691ac9b55e6a22d311a47b44e687ad0b1a01b3da671acdf19a3b3126572ca71945b262648ac8d190bb1fa63d2c7618e3b19262d2c4d187 else 0x2201307cc9d03e601801902b046200980b01d819d376270231d82b0f805c2b48c5846b5140d64076008084c4ea8a02a3116105220835901db8b11a40a88811c2c2008080980b025853823171380982a860ec03989d87c14e5813816c4e1f3710b52c835900230f89800a884dc8a00d63e6e03546902a251650b04704000e62703061f2100a04e020602c0c803814e08c501307ec4ec3e0882a01068582a40a8606acdd80a0394b387d42c768aa5902a1d0b0404c05805c0a880560cc2013011c4e08465968a02a3c09f0b0804c0d59bb0f99640a8d87ccb2c2c054401302b011066200461f627110015140ac19840401020568d20545013a0a02005e084a16c3e097c4e4809e275455050300231804c14e82811829ca0260104dd87d4b2054602d616c3e25902a280e70b08020203882d87c301121c140e60b0807105b13860224382616080104008205780a0d4302ba0a06a1b37627505023118b082b139a280a8b80a166ec4e83e02a262741f30b015109fb85840fc121322080a1939f0b08070246a43826160909f0b080702427c2c221c0d0b068283458121c616110993f4028c9cc87044144382213e161402b050884c8d6014742c121361611099104028e814243942c225de1615270484c85a93864264bb4b23a16a4c11099105270e814243942d4983a2c0808f0b0803c2427c2c201121c150b0484c85a93860224382a160b0b068282c2c16160b0b0702806407009c128a4058280c01304c0a25204a1a0f850290701ec160982c1c0a01802281f04a2c0fe0b0880807c0800d8903f82c222c056c1628b260511e02a825128f82815458c9d47c83e501064ea3ec1e260a51f080730509b8154128b8144dc0aa094402041f120e02e20b025130580bc1186814838c9c094481cc16160500bd2ce0b345160518b193a8fa07cb028cdd47ccb303e500c01c01702a220b33751f23004c1407c06028c128882cc5802e8c0130580a64c01801f098281480884c0e02807c06028c128a038147404130402a62c07ba3ec1664e360a1548150f0289b89481288404166e020a4e05aa3ec1e320552734501513028340a03a0f347ccb382c6414a3e65902a201cd0283dd1f32ce0b1b058381483e8403c0a0e0b050730285828c9c202c01b68ac4ee3e01c0ad019403771e00db2cf1f00e05400ca39bb1380739658f8064d89d51443e362cc4e68a46921f2d0562734570b139310711146cddc9985989d87d03e6a4e41c4451e1660560160b5273451b1bb0b293b0f907cbc59c14037c99c2c0de6c6e42ca4ec3e41f280981402d82405580c8181e8151bb1670f907cbc9883888a3c16e4cc3e81f233752761f40f929390711146cdd49d87c83e4a4ec3ec161b2ce1f60b20f9293b0f907c6108039c980860220ec609101c062a4e043019372641f40f8e85b9) else (if i < 7 then 0x411880320ed42c1320b0501607c07506c200a8410360c04c1f01d41b08039c2c28050b0510b51f0569313aa280b01978581d4c0f80ea0ce301362c075067200783b54572c815140541e296419c800a100508406050360d8b29b81b060260560220ce4075e16100e040631901d41a4220a05c0e987c03813808b49c70904180ad1d1652720e2229293b0b02870f9070a0ea838200f01829a02b0562d2771661f03ac34c0f981d6070585849c14387d038507541c100c045e1f03b04a023182328b02181a8980b87c4384c04c3e08606a1d2cf05727030245942301f28781a89c9985989c44187c43e6c3e08606a1810726502f2c82ba4598073858587c101c435c3e1c1f020b0b056900670f3164870118b87c41491815a4019a4e48b046200e445e1f0c1b820dc160ac020ad18455028568c06d85801824d9670f8d804105dc6ec3ea5941f280303e52ce1f70b140181c493a82b85b0f8c917c2c2c3e0a09a1ae1f0d07305b0f060260dc09dc2c094501301601b04a200c01a81b823100580dc1a8742c03006a301403001704a203ed0f0350c87029585811880260b8440094426e02f06a181073700e72702514073858500416160f0f5270550e16407010985829ca03202605e08c405920a02f0aa200980c80d825108580c00bc1188438105b01307504a201810553710e527025181c31670f907c8827c2c28020c012098b0582c2c1c1641c100104008207c1018580d4460aa6e06a1d3730b0230d82826c06d85b166a28d8581a6ec59046183e62c8230c29c11858581013c02069088200e527001830d4560b1904c280483c09282a0b05400659c3e41f260b52761f20f90073008587c03812b82c4ba5a4e0b3752761f20f9300a938580549c200666ec16c3ea5928089548150f05a9381830fa07cb82c1c1624ec3e81f260b0404c2a78580a8802602c0c814e054501301601b02a200b0118350c04c0580ec0ce9bb933028119187c1040d4362c034a8a06a203b40e045021f2c8151904f85840381013016c0a0a7046283c035081e28b01a8606a13e0861520545035405093a59c3e81f341ac0e0804e8582a40a8880b42d4b387d03e5a1608098158088351006607006c1b080328788b303808c581c080ca4f40e0231010c0cc0701378580a8c0e085980482a1401306010a4ec0a046273702ee1f52720f940282014102bc020981815d2704c0c03d8b0072939a280a8d804166ea4ec3e02a252761f30b0151001806c1e09399bb0fb858e023c2c201c0a09a0b61f0c045070582c1413e161008a0e0985820041002081f040605035118b29b81a860dd81414e08c4659093a8a41f231630b41f20f910701184020c9d81408c407864ea6e0462605040080300fc0a8903942ccb2d1408c521666e64c81c04628148088230d8b00440260f993a07cccdc else 0x2001023822c8004009c2c11a444e004e16a3e2002049d1f0ca2801024c60640080be0ba4004e16a59183c02f82a0e1b985801014484dcc2c0080a24420004a8a180b8020088c0138599646008022281c0751102937003038109380182b0600c0ea2006075100302f82a0c05c2470f8602e11d87c3017093c3e1b0b0370380c019062938600c0ea248ba4c03301b261f03e04a04d0279484c88104d0821769330f0e02205387812805650110044441a0b24580d8c0ac01804423c80e212987c00e421cc3c093029200b82f02e0c05c0bf8586009c2c8c8301b41302fe162017a09b0500303e141f40dc01c6c2c0fe05e012422007442002f2017f0b0148d058010944604805fc2c302b00602918088038178c05c0bf85a0708438108052302961601b190560b40e0e0b18584126120526e006192700309058018400d49c2c16a4e1043d2660b0c24c249d82c241c00c0781a1f00b8488d0fa85840eb82c0460f6400407b4441808a0b00800d901c105a07021006c1ecc8381260523029616120500703d8c0309740407498066020036402ba0504f1a09c0e52621e00d831180a5028976938211070c458108200607510030158288e02907193006c80bc02f0a0308e017441184180d70b0c0ac004068602e87c202b00e450180d015841844900ac1dc24c682c03a520301c02907a02b204980683b8c0ac0380a460ee1088a6301c0930291814b0b080680e38586071c2c052301100d03818158070088c05c06821f858802e064100888401c084029191600e60b0e0140a5858601c131814323e096c161a0b51f00b8d07ca2f058258947c12002e302ac0a018096212ee0a32651e1096405f058605f02d0398140f6523e40a0171e050128158d05893805c781405404a0564011c141627046816032f0b03a9b1381801d)))

def moveIndex11 (i : Nat) : Nat := 0x3cb0006071bc06644efe047216f21aa4b2e83510086420070b83c4c0b8055c33afe7705542ba052f88e1198a3698b148793133dae982ae9d430826747c65d11792bb62ebc0c98d903a6a04648fd9d9136f84f5839707a829366c7863097203cdc091c73f12b217ca259046c9f5e255a4400518858b3acc0630e6808fe21800038b98000000000000000000000102010480000e33ce78ecac8000000120c7442a0a721a865a4000000000000003c2911b830c7672f41be8755114c13683f002f618e815dc1330e8000182460b6b9ce43d7e06e8ab0000722200028408000000165ac00068dc00000002804d91200000002886f9bcb06022f7807e96a000147d082ff87802c3e20b47258dbe0d7e0874a10807212f01c48aba10993db002142050ea7007808ac68c1e2f1b0e2a836b5006504e9b5041410acc01c2052c87696800000001898b8c57383e0b800000009053a04b469700d414c0003473381a5201e624444e8cd43cec1f58d7d9a98191a56306570d07356a2800b8b12f8021c37d08380006260000000000000000000000029acb047e0740000843000083768ef39b2e13c00030aa400110642269c29a098834f87cb07a1174034dc15b87490bc61d840ae4ddb09d71a6c126049f1a8c35b61b48492ee5b07a613835f986990dc61c005d88f320cde222c37a95b2015c6604ce79d801186688c77d06c11ebe0f8c3d9f5c10d0e54b4f7e002a165621e0a54913e13fa16545138a1e2a01c1581d1844f163805eca9c0e0e018420cc12e03bd0bd843c41001a040c5c4dc42ee914b085230d422a8e5e20a61cc02451d2c3c082e7c1b096ca02cc38bc6b58bf92c9a1fcc4268d7d000e2e3009b82cb1c70653879200541dc63b4c57c9158116c07205af1e81182019602a58b012e0e2d2c9cae8d338960b4cc2e8c2c10ca257327909ce26d069405411da80b940780ce81be11e3c11a85b3877e0c96302025f94bc19e00cdca7784cc188c16d8522196c0f87afa8af2e50d3740144454e84a41d762ccc30c04fa15a614301cc8ce31e0641980fb03f230480d343a30ab91abc25232de1b90017253203b4038f0b5626f8b1a0c93a0a0400310300038303d60d9f484502020f079f00020e293108013f0602230016050004080001070c020100170108203d210900050200110b0813110b2800301f5204050606030000290a19070e0c060407010006242a050b291d2d070006001800050700020008030e0100030c030b07020014041408042a0000000002120d

def liveData10 (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0x87fdc52e9924c540c3fcbaa21924c540a7f4ca649814c540fbc5824c9814c540ebb6aaa21414c540bf96cc4c9414c540ef96aa4c9414c540fb96884c9414c540ff85824c9414c540efa6aa889414c540fba688889414c54097bdc4aed934854097f5c5aed988454097f5c2aed9884540d3f6bba219584540dbb6bba215484540d3f6bba219384540d776bb955938454097f4cb6615384540df36bb5515384540fb36885515384540ff155460d5384540f3d6886563384540fb9688552338454097f5c8aed928454097f5c5aed9284540d3f6bba219284540d776bb9559284540f3b688551928454097f4cb54d9284540f3d6888cd9284540f756558cd9284540d775b995582845409df5c7aed5284540d3f5b9a215284540d3f5b9a213284540d775b99553284540b7e6cc6622284540b7e6cc6562284540f3e6886562284540b7e5c96162284540f765989562284540fb66889562284540bfa6cc5522284540f7a5985522284540fba6885522284540b7e6cc64e2284540f7665564e2284540b7e5c954e2284540ff255454e2284540f7c5988ce2284540fbc6888ce2284540f7c5958ce2284540ff46558ce2284540ff85548ce22845409fd9c3aed824c140ebeaaaa22224c1409ef9c6aed814c140afb8ca6d1514c140df99b46cd514c14097f8cb649514c140fbaa88889414c1409fd9c5aed314c140cfdabbaa9314c140d7dabb661314c140dbdabba21314c140ebdaaaa21314c1409fdacc6d5314c140cfdaaa6d5314c140df9abb551314c140fb9a88551314c140d7dabb649314c140f3da88649314c140d7d9b5649314c1409fd8cb609314c140dfcabb889314c140efcaaa889314c140f7c998889314c140fbca88889314c140dfc9b5889314c140ff8954889314c140bfd2cc605314c140dfd2bb605314c140efd2aa605314c140dfd1b5605314c140ff9154605314c140f7d192605314c140fbd182605314c140ffc222605314c140ff92bb505314c140ff91b8505314c140ff91b5505314c140ff91b2505314c140ff9182505314c140ff9152505314c140afb8ca551214c140ff195454d214c140bfd2cc4c5214c140dfd2bb4c5214c140efd2aa4c5214c140dfd1b84c5214c140f7d1984c5214c140fbd2884c5214c140ff91544c5214c140ebf2aaa22114c140ef72aa956114c140fbb288552114c140bfd2cc54e114c140efd2aa54e114c140f7d19854e114c140fbd28854e114c140ff518554e114c140f3f28864a114c140f7725564a114c140f7d15364a114c140ff515354a114c140efe2aa88a114c140f7e19888a114c140fbe28888a114c140ff625588a114c140ffa15488a114c140ffc15388a114c14097b5c4aed9384540df92bb505314c140fb9288505314c140ff8222505314c140afb0ca552114c140ff115454e114c140 else 0x252728a940c9e24df26012508ea46322890947d83c01d08dd465e32a1788b7c59a2bb147898c4a223211688a042c2110ff87b43d01d60e206c83261810be05a82b014609a04bc2060d704f019407200097fdc5aed826454097fdc3aed8264540c7febbaa9826454097fecc6e13264540c7febbaa99560540c7febbaa99360540b3fecc6558260540aefdc6aa95260540c7febb6a55260540aefdc6aa93260540f3ed956093260540a7fcca6e58254540c7febb6a58254540a7fcca6613254540b7f6cc64d8154540f3f5936098154540f775935498154540fbe5824c981545409fbdc5aed82505409fbdc3aed8250540cfbebb6958250540d7bebb6615250540fbad8360952505409fbecc6e1325054097fccb661a54c540a7fecc6a1954c540afbecc6a1544c540e3fda8655824c540ebbda8551824c5409dfdc7aed524c540afedc2aa9524c540c7febb6a5524c540afecca609524c540e7eda9609524c540ebeda8609524c540f7cd95609324c540ff8d54609324c540ffc5c1609324c540f3f595609814c540fbb554609814c540fbe582549814c540f7d5954c9814c540ff95544c9814c540bfb6cc609414c540bfb6cc549414c540ffa582549414c540ff95c84c9414c540ff95c54c9414c5408ffdc3aeda84854097fdc5aed98485408ffdc3aeda548540a7fecc6a19548540c7febb6a19548540afbecc6a15448540a7fecc6959348540c7febb6959348540a7fdca6159348540c7fdba6558348540cfbdba5518348540c7fdb96a1534854097fccb6615348540ef3da85515348540ff1d5460d5348540e7f5a86553148540efb5a85513148540d7fabb649814c140fbe982549814c140dfb9b46c9514c140ffb1b4605514c140f7f192605514c140fbf182605514c140ff7152605514c140bfbacc609414c140bfbacc549414c140ffa982549414c140ff99b8551314c140ff9954609314c140bfdacc549314c140f7d998549314c140ffc982549314c140ffd152605314c1409ffacc6e1214c1409ffacc6d5214c140d7f9986d5214c1409ff9cb615214c140dfb9b8551214c140dfdabb54d214c140dfd9b854d214c140f7d99854d214c140ffd1854c5214c14097ddc3aeda96094097dccb6a6336094097edc5aed988894097edc1aed9888940e3eeaaa222264540f3ce888ce2264540a6fdc6aa9956054097bdc4aed9360540a6fdc6aa99360540aeddc6aaa336054097f5c1aed9260540a6fdc6aa99260540aeedc6aaa226054097f9c0aeda95454097bdc4aed935454087fdc82e9925454087fdc32e99254540c7dcba8cd9254540a7ecca6622254540e3eda9a222254540a7f4ca6498154540fb658254981545409dbdc7aed5250540ebaeaaa222250540ebae886962250540fb8e888ce225054087fdc52e9984c54087fdc82e9924c540) else (if i < 3 then 0x2620098060403500988040013160083a16d26080260401685820018104c00c07c2004c00820148010582c08000e0b040201e0b06804100804126103c1070401301a90ec601300b90ec68050a0140362e0b074b210098040405d081c24582002840e16080182000d8403610006c221603d88062c0a8582a1602a8801c01d101d801020098058401301a90ec603501e8802e43b1004c04044b180800b8200980808c8301a80f440170220807409210004010261e04001c0807002e2a0507828192cb058522c60b005c722c00d88036100d840f601016050262cc0a0947c101484080a40e028c607b0828c3c1411d8074601ce0a092c607660549307c14126011c6a3ca0f08052101928f040290800e80581003820130804c2006967415a4e23793c99c2ce2770f84165f2668b349c46f200ec3c8a021088dfa4e0230c07610178118420b02e0128609b04e880500981087020302098800020390118600605381187c3e118f05860a00078041042829c400a03e024c606205388018103e907008c3327001808c300070201c08070200932760fb42d01c2801c3ee27004860130804c20000001c080001c082c2c100984026100245921610064200282820310a93020000000000031606c2c1000000000070b0403a0751004dfc161012683c0611b05805e046181c403802f0159302813160603e180540704040f85014140504038100e06038180e0403202f03d8c06601c0110c081f0a029038204028201c08808220208808208404c09c5923e40f8d0380981026022020803000602a19059d140630231082c0a20230c0220981028c0380981804647c098727407ca0012e8f8cb202a20808220208808200a03d8118640a014826062020c8f8054200282810107c241c0820141a050681412051070480a0818141e0a07828160a041e4ce1f082c7e4c91f407c7416f263a2a03e4a0b48f9c9d01f268f88c041f1b058cb3a3e20f92c69615afb575eb71599ac3d5a2a93537a9953e69b54bba54d29293f49aa4451da8c9452a2050ba81f3e39dbce9670d3749b14d0e6633129804bee5d32d79694b0255d2a994bc9e24e7261927c8c24231f28e9c69e31116989ec47a1e50d385a42560ed06482fc13605d01c8053fadf7efa07c73df1ebaf4b7963c69e10f0376bbb15d66e8772db8bdc06de46e936cdb42d9c6beb5adab2d476a134f5a08cbe642b1cd8a8c2860b2fdd796bac5c6aded6b8b57595abfd5a6ace55e2aa9516a5f52028b94049d64e8a6fd35a99b4aaa54129691f486a3ed1ec8f1476239d1aa8d0465a2e51688a244821f90f287442aa10d07c839413a0550067fe3fc9fd0fde7ea3f29f80fb67d63e21ec8f5a7a83d19e78f327943c79e28ef07593aa1cd4e126dd3521a48d0066e3279928c7062630a1808be05de2e61680ae856f2ae94f8a7 else 0x1300c08030075100600))

def moveIndex10 (i : Nat) : Nat := 0x380a4bf02420c014d02325bd308001bc80100005e7483f61c111b0784420003310002825216e0d000383640af028000889814611099102a20c200d9490ab44380be00eccb4190000000000a13e03082ec08c408d0a175cb4056204413d04f40e512e83745101db07b01e04dc20e04a15c07c708213a2010082013432cb201143

def liveData9 (i : Nat) : Nat := 0xd0f03c16041a010400006c20d1303a0504c16c9645916182c2000361e0503c0a040000036101c58168f0200e0400000000000000000db6c75999c3606dd69b2546993993415c8df662e54ca14e25d087f361648c411e0dc642d1408c3c190a03c14050061bfaedc6aa99560540a3deea57755326c0a8186febb71aaa64d815028bfbaf5db52a9302a04ded752cc64d8154540f9b2c9b04a9302a8a8155bdd7aed98549415028bfbaf5db52a9262a07cf1655824c9814c540fdc2aa3049930298a813db5d7b3152505315028f7ba95db4ac9a42a055be75abb649814c140a7dc6d368d92a2982816fb0da6d18154530502afe1b6c9302a8a60a07ed860952605514c1409fcce9d98c1282982813db9d7b3152505305027bb3af662a498a60a057f236d82549314c140fdc8aa304c0a6298281fbc182549814c530502ff25baa928298a60a07fe060952505314c140ef8cdc2a8a9a4298281df91b85513148530502a76ba95dd10c9c22a055cd752bb95593845409bd2ea598c9c4508a814f98da6d1b354530503b725774428298a60a077e0aee22505314c140fdc144444a0a6298281abb0caa2154845305026fa1b8cc2a708a60a06fc4b315454e114c140fd89442a8a9c229828137d0dc54d9284530502df41b4aa44508a60a07fc05515388a114c140

def moveIndex9 (i : Nat) : Nat := 0x1c1

def liveData8 (i : Nat) : Nat := 0x28a1af792bb71aaa64d815027d91e7b7552505314c140

def liveLevels : Nat → Packing
  | 14 => (1,1,8,0,0,0,0,liveData14)
  | 13 => (14,2,8,0,0,11,0,liveData13)
  | 12 => (134,3,8,0,0,14,0,liveData12)
  | 11 => (546,4,8,0,0,15,0,liveData11)
  | 10 => (246,5,8,0,0,13,0,liveData10)
  | 9 => (41,6,8,0,0,9,0,liveData9)
  | 8 => (2,7,8,0,0,3,0,liveData8)
  | _ => emptyPacking

def liveIndex : Nat → Nat → Option (Nat × Nat)
  | 14 => lookupWord 10 29 5 9 4 1 moveIndex14
  | 13 => lookupWord 69 226 7 15 8 3 moveIndex13
  | 12 => lookupWord 290 929 8 17 10 3 moveIndex12
  | 11 => lookupWord 128 418 8 15 8 3 moveIndex11
  | 10 => lookupWord 21 69 6 13 6 3 moveIndex10
  | 9 => lookupWord 1 3 0 5 1 0 moveIndex9
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

def orCols : IndexTree ColumnInfo := (.fork 87 (.fork 43 (.fork 21 (.fork 10 (.fork 5 (.fork 2 (.leaf [(1,0,510,0,12),(0,2,440,69,8)]) (.leaf [(2,0,2557,0,12),(1,2,440,68,7),(0,4,2417,138,8)])) (.fork 2 (.leaf [(4,0,2555,0,12),(2,4,2417,136,7)]) (.leaf [(4,2,440,65,7),(6,0,2553,0,9),(5,2,440,64,6)]))) (.fork 5 (.fork 2 (.leaf [(8,0,2551,0,12),(9,0,486,0,8)]) (.leaf [(10,0,2549,0,8),(4,8,227,272,7),(8,4,2417,130,7)])) (.fork 3 (.leaf [(12,0,2547,0,9),(10,4,2417,128,6),(14,0,2545,0,7)]) (.leaf [(15,0,480,0,4),(0,16,486,9,10),(16,0,495,0,13)])))) (.fork 11 (.fork 5 (.fork 2 (.leaf [(1,16,486,8,9),(17,0,494,0,11)]) (.leaf [(17,2,424,68,6),(19,0,492,0,8),(21,0,490,0,7)])) (.fork 3 (.leaf [(6,16,480,9,6),(21,2,424,64,5),(8,16,486,1,9)]) (.leaf [(16,8,227,260,7),(24,0,487,0,11),(9,16,486,0,8)]))) (.fork 5 (.fork 2 (.leaf [(25,0,486,0,8),(10,16,484,1,6)]) (.leaf [(11,16,484,0,5),(27,0,484,0,5),(12,16,482,1,6)])) (.fork 3 (.leaf [(20,8,227,256,6),(24,4,353,130,6),(13,16,482,0,5)]) (.leaf [(29,0,482,0,5),(14,16,480,1,5),(15,16,480,0,4)]))))) (.fork 22 (.fork 11 (.fork 5 (.fork 2 (.leaf [(31,0,480,0,4),(32,0,2527,0,12)]) (.leaf [(1,32,94,384,7),(32,1,460,18,7),(34,1,460,16,6)])) (.fork 3 (.leaf [(35,0,476,0,7),(36,0,2395,0,8),(40,0,2519,0,8)]) (.leaf [(17,32,78,384,6),(48,1,460,2,6),(49,0,462,0,8)]))) (.fork 5 (.fork 2 (.leaf [(50,1,460,0,5),(51,0,460,0,5)]) (.leaf [(40,16,454,1,6),(41,16,454,0,5),(57,0,454,0,5)])) (.fork 3 (.leaf [(0,64,2237,258,10),(64,0,2495,0,13),(64,1,396,50,7)]) (.leaf [(66,0,2493,0,11),(65,2,440,4,6),(64,4,2353,138,7)])))) (.fork 11 (.fork 5 (.fork 2 (.leaf [(70,0,2489,0,8),(69,2,440,0,5)]) (.leaf [(74,0,2485,0,7),(81,0,430,0,8),(83,0,428,0,7)])) (.fork 3 (.leaf [(85,2,424,0,4),(89,0,422,0,5),(98,0,2461,0,7)]) (.leaf [(98,1,396,16,5),(114,1,396,0,4),(0,128,2395,36,10)]))) (.fork 5 (.fork 2 (.leaf [(128,0,2431,0,13),(4,128,2395,32,9)]) (.leaf [(132,0,2427,0,11),(132,2,312,65,6),(134,0,2425,0,8)])) (.fork 3 (.leaf [(140,0,2419,0,8),(144,0,367,0,11),(145,0,366,0,8)]) (.leaf [(140,16,354,1,5),(156,0,355,0,7),(141,16,354,0,4)])))))) (.fork 43 (.fork 21 (.fork 10 (.fork 5 (.fork 2 (.leaf [(157,0,354,0,4),(154,4,353,0,4)]) (.leaf [(160,0,2399,0,11),(160,1,332,18,6),(162,0,2397,0,7)])) (.fork 2 (.leaf [(162,1,332,16,5),(36,128,2395,0,8)]) (.leaf [(38,128,2393,0,5),(44,128,2387,0,5),(177,0,334,0,7)]))) (.fork 5 (.fork 2 (.leaf [(178,1,332,0,4),(53,128,330,0,4)]) (.leaf [(169,16,326,0,4),(192,0,2367,0,11),(194,0,2365,0,8)])) (.fork 3 (.leaf [(193,2,312,4,5),(194,4,2353,8,5),(196,2,312,1,5)]) (.leaf [(198,0,2361,0,7),(197,2,312,0,4),(200,4,2353,2,5)])))) (.fork 11 (.fork 5 (.fork 2 (.leaf [(202,4,2353,0,4),(0,256,2199,104,8)]) (.leaf [(256,0,2303,0,12),(258,0,2237,0,8),(260,0,2299,0,8)])) (.fork 3 (.leaf [(8,256,2199,96,7),(256,8,227,20,7),(264,0,2295,0,9)]) (.leaf [(260,8,227,16,6),(268,0,2291,0,7),(273,0,238,0,7)]))) (.fork 5 (.fork 2 (.leaf [(264,16,230,1,6),(272,8,227,4,6)]) (.leaf [(265,16,230,0,5),(281,0,230,0,5),(276,8,227,0,5)])) (.fork 3 (.leaf [(32,256,2199,72,7),(256,32,94,129,7),(288,0,2271,0,9)]) (.leaf [(257,32,94,128,6),(40,256,2199,64,6),(296,0,2263,0,7)]))))) (.fork 22 (.fork 11 (.fork 5 (.fork 2 (.leaf [(48,256,135,72,6),(288,16,198,9,6)]) (.leaf [(273,32,78,128,5),(305,0,206,0,5),(56,256,135,64,5)])) (.fork 3 (.leaf [(296,16,198,1,5),(297,16,198,0,4),(313,0,198,0,4)]) (.leaf [(320,0,2239,0,11),(258,64,2237,0,8),(322,0,2237,0,8)]))) (.fork 5 (.fork 2 (.leaf [(324,0,2235,0,7),(262,64,2233,0,5)]) (.leaf [(320,8,163,20,6),(328,0,2231,0,8),(266,64,2229,0,5)])) (.fork 3 (.leaf [(324,8,163,16,5),(270,64,2225,0,4),(275,64,172,0,4)]) (.leaf [(339,0,172,0,4),(336,8,163,4,5),(329,16,166,0,4)])))) (.fork 11 (.fork 5 (.fork 2 (.leaf [(340,8,163,0,4),(96,256,2199,8,6)]) (.leaf [(352,0,2207,0,8),(291,64,156,0,4),(104,256,2199,0,5)])) (.fork 3 (.leaf [(120,256,135,0,4),(384,0,2175,0,9),(384,8,99,20,6)]) (.leaf [(388,8,99,16,5),(396,0,2163,0,5),(400,8,99,4,5)]))) (.fork 5 (.fork 2 (.leaf [(404,8,99,0,4),(416,0,2143,0,8)]) (.leaf [(385,32,94,0,5),(168,256,2071,64,5),(401,32,78,0,4)])) (.fork 3 (.leaf [(448,32,30,1,5),(480,0,2079,0,7),(449,32,30,0,4)]) (.leaf [(482,0,2077,0,4),(356,128,2075,0,4),(232,256,2071,0,4)])))))))

def orForest : Forest := ⟨2559,14,fun j => orSamples[j]?.getD (0,0),orCols,orSymmetries,liveLevels,liveIndex⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem orGeometry : graphValid orForest (boundsBefore entries503) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=5) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked14At0 : block orForest 14 0 1 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked13At0 : block orForest 13 0 8 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked13At8 : block orForest 13 8 6 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked12At0 : block orForest 12 0 38 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked12At38 : block orForest 12 38 56 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked12At94 : block orForest 12 94 12 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked12At106 : block orForest 12 106 28 = true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked11At0 : block orForest 11 0 2 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked11At2 : block orForest 11 2 56 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked11At58 : block orForest 11 58 30 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked11At88 : block orForest 11 88 56 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked11At144 : block orForest 11 144 56 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked11At200 : block orForest 11 200 56 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked11At256 : block orForest 11 256 56 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked11At312 : block orForest 11 312 56 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked11At368 : block orForest 11 368 56 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked11At424 : block orForest 11 424 3 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked11At427 : block orForest 11 427 56 = true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked11At483 : block orForest 11 483 56 = true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked11At539 : block orForest 11 539 7 = true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked10At0 : block orForest 10 0 6 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked10At6 : block orForest 10 6 56 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked10At62 : block orForest 10 62 56 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked10At118 : block orForest 10 118 38 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked10At156 : block orForest 10 156 56 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked10At212 : block orForest 10 212 34 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked9At0 : block orForest 9 0 14 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked9At14 : block orForest 9 14 27 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked8At0 : block orForest 8 0 2 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

theorem allAt14 : block orForest 14 0 1 = true := checked14At0
theorem allAt13 : block orForest 13 0 14 = true := (@block_merge orForest 13 0 8 6 checked13At0 checked13At8)
theorem allAt12 : block orForest 12 0 134 = true := (@block_merge orForest 12 0 94 40 (@block_merge orForest 12 0 38 56 checked12At0 checked12At38) (@block_merge orForest 12 94 12 28 checked12At94 checked12At106))
theorem allAt11 : block orForest 11 0 546 = true := (@block_merge orForest 11 0 256 290 (@block_merge orForest 11 0 88 168 (@block_merge orForest 11 0 2 86 checked11At0 (@block_merge orForest 11 2 56 30 checked11At2 checked11At58)) (@block_merge orForest 11 88 56 112 checked11At88 (@block_merge orForest 11 144 56 56 checked11At144 checked11At200))) (@block_merge orForest 11 256 168 122 (@block_merge orForest 11 256 56 112 checked11At256 (@block_merge orForest 11 312 56 56 checked11At312 checked11At368)) (@block_merge orForest 11 424 59 63 (@block_merge orForest 11 424 3 56 checked11At424 checked11At427) (@block_merge orForest 11 483 56 7 checked11At483 checked11At539))))
theorem allAt10 : block orForest 10 0 246 = true := (@block_merge orForest 10 0 118 128 (@block_merge orForest 10 0 6 112 checked10At0 (@block_merge orForest 10 6 56 56 checked10At6 checked10At62)) (@block_merge orForest 10 118 38 90 checked10At118 (@block_merge orForest 10 156 56 34 checked10At156 checked10At212)))
theorem allAt9 : block orForest 9 0 41 = true := (@block_merge orForest 9 0 14 27 checked9At0 checked9At14)
theorem allAt8 : block orForest 8 0 2 = true := checked8At0
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

theorem noRun : Impossible (graphGoal 2559) 14 (vars 2559).toFinset :=
  root_index (g:=orForest) (before_sound _ sound503) orGeometry orTables
    (k:=14) (by decide) (i:=0) (by decide +kernel)

end Free511
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem liveSeedImpossible : Impossible graph 14 (inputs++[orSeed]).toFinset := by
  have target : graphGoal 2559 = graph := by decide +kernel
  have roots : vars 2559 = inputs++[orSeed] := by decide +kernel
  simpa only [target,roots] using Free511.noRun
end PEqualNP.Outside.L_meta_3634

namespace PEqualNP.Outside.L_meta_3634

theorem parentBound : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 4)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size := by
  intro C legal first computes
  by_contra! small
  obtain ⟨k,t,budget,without | withSeed⟩ :=
    PEqualNP.Outside.L_meta_3634.initial_live C legal first computes (by omega)
  · exact PEqualNP.Outside.L_meta_3634.dead_start
      (PEqualNP.Outside.L_meta_3634.before_sound _ PEqualNP.Outside.L_meta_3634.valid383)
      PEqualNP.Outside.L_meta_3634.geomdead PEqualNP.Outside.L_meta_3634.tablesdead k t budget without
  · exact PEqualNP.Outside.L_meta_3634.liveSeedImpossible k t budget withSeed

end PEqualNP.Outside.L_meta_3634

namespace PEqualNP.Outside.L_meta_3634
theorem pairBound :
    ∀ (x1 x2 : Fin (9 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), x1 ≠ (0 : Fin (9 : ℕ)) → x1 ≠ (4 : Fin (9 : ℕ)) → x2 ≠ (0 : Fin (9 : ℕ)) → x2 ≠ (4 : Fin (9 : ℕ)) → x1 ≠ x2 → PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (13 : ℕ) → (∀ (x11 : Fin (9 : ℕ) → Bool), x3.eval (List.ofFn x11 ++ [x11 (0 : Fin (9 : ℕ)) || x11 (4 : Fin (9 : ℕ)), x11 x1 || x11 x2]) = (x11 (0 : Fin (9 : ℕ)) && x11 (1 : Fin (9 : ℕ)) || x11 (1 : Fin (9 : ℕ)) && x11 (2 : Fin (9 : ℕ)) || x11 (2 : Fin (9 : ℕ)) && x11 (3 : Fin (9 : ℕ)) || x11 (3 : Fin (9 : ℕ)) && x11 (4 : Fin (9 : ℕ)) || x11 (4 : Fin (9 : ℕ)) && x11 (0 : Fin (9 : ℕ)) || x11 (0 : Fin (9 : ℕ)) && x11 (5 : Fin (9 : ℕ)) || x11 (1 : Fin (9 : ℕ)) && x11 (6 : Fin (9 : ℕ)) || x11 (2 : Fin (9 : ℕ)) && x11 (7 : Fin (9 : ℕ)) || x11 (3 : Fin (9 : ℕ)) && x11 (8 : Fin (9 : ℕ)) || x11 (5 : Fin (9 : ℕ)) && x11 (7 : Fin (9 : ℕ)) || x11 (6 : Fin (9 : ℕ)) && x11 (8 : Fin (9 : ℕ)) || x11 (8 : Fin (9 : ℕ)) && x11 (5 : Fin (9 : ℕ)))) → False := by
  intro a b C _ _ _ _ _ legal small computes
  let addWire (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]
  let first : PEqualNP.CircuitLowerBounds.Gate := ⟨.or, [0, 4]⟩
  let second : PEqualNP.CircuitLowerBounds.Gate := ⟨.or, [a.val, b.val]⟩
  let full : PEqualNP.CircuitLowerBounds.Circuit := ⟨first :: second :: C.gates, C.output⟩
  have fullFan : PEqualNP.MetaComplexity.FanInTwo full := by
    intro g hg
    change g ∈ first :: second :: C.gates at hg
    simp only [List.mem_cons] at hg
    rcases hg with rfl | rfl | hg
    · simp [first]
    · simp [second]
    · exact legal g hg
  have keep (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (i : ℕ)
      (hi : i < w.length) : (gs.foldl addWire w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      · exact List.getD_append _ _ _ _ hi
      · simp [addWire]
        omega
  have firstValue (x : Fin 9 → Bool) :
      addWire (List.ofFn x) first = List.ofFn x ++ [x 0 || x 4] := by
    simp [addWire, first, PEqualNP.CircuitLowerBounds.GateOp.eval]
  have readInput (x : Fin 9 → Bool) (j : Fin 9) :
      (List.ofFn x ++ [x 0 || x 4]).getD j.val false = x j := by
    rw [List.getD_append _ _ _ _ (by simp)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, j.isLt, dif_pos, Option.getD_some]
  have secondValue (x : Fin 9 → Bool) :
      addWire (List.ofFn x ++ [x 0 || x 4]) second =
        List.ofFn x ++ [x 0 || x 4, x a || x b] := by
    simp only [addWire, second, PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons,
      List.map_nil, List.any_cons, List.any_nil, id_eq, readInput, Bool.or_false, List.append_assoc]
    rfl
  have wireNine (x : Fin 9 → Bool) : (full.wires (List.ofFn x)).getD 9 false = (x 0 || x 4) := by
    change ((second :: C.gates).foldl addWire (addWire (List.ofFn x) first)).getD 9 false = _
    rw [keep, firstValue, List.getD_append_right _ _ _ _ (by simp), List.length_ofFn]
    · rfl
    · rw [firstValue]
      simp
  have fullComputes : PEqualNP.MetaComplexity.circuitFun 9 full = (fun x : Fin 9 → Bool =>
      (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
      (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
      (x 6 && x 8) || (x 8 && x 5)) := by
    funext x
    change C.eval (addWire (addWire (List.ofFn x) first) second) = _
    rw [firstValue, secondValue]
    exact computes x
  have lower := PEqualNP.Outside.L_meta_3634.parentBound full fullFan wireNine fullComputes
  have sizeFull : full.size = C.size + 2 := by
    simp [full, PEqualNP.CircuitLowerBounds.Circuit.size, Nat.add_assoc]
  omega

end PEqualNP.Outside.L_meta_3634

theorem PEqualNP.Outside.L_meta_3634 :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Finset (Fin (9 : ℕ))), PEqualNP.MetaComplexity.FanInTwo x1 → x2.card = (2 : ℕ) → x2 ≠ {(0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))} → Disjoint x2 {(0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))} → x1.size = (13 : ℕ) → (∀ (x8 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x8 ++ [x8 (0 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)), Decidable.decide (∃ x9 ∈ x2, x8 x9 = Bool.true)]) = [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x9 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x8 x9.1 && x8 x9.2) → False := by
  intro C s fan card _ disj size agree
  obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp card
  have apart (i : Fin 9) (hi : i ∈ ({a,b} : Finset (Fin 9))) :
      i ≠ 0 ∧ i ≠ 4 := by
    constructor <;> intro eq <;> subst i <;> exact Finset.disjoint_left.mp disj hi (by simp)
  obtain ⟨ha0,ha4⟩ := apart a (by simp)
  obtain ⟨hb0,hb4⟩ := apart b (by simp)
  apply PEqualNP.Outside.L_meta_3634.pairBound a b C ha0 ha4 hb0 hb4 hab fan size.le
  intro x
  have seed : decide (∃ i ∈ ({a,b} : Finset (Fin 9)), x i = true) = (x a || x b) := by
    simp
  simpa only [seed, List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc] using agree x
