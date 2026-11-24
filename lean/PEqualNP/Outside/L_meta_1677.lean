import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_1677

-- Adapted from jfsantoropereira, project PR 6642; certificate checks use smaller normalization blocks.
-- The live-wire extraction and restriction checker are adapted from L-meta-1667.
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

def firstWire : Sig := (inputs.getD 0 zero) ||| (inputs.getD 6 zero)

theorem firstWire_table : ∀ r : Row, bit r firstWire = (sample r 0 || sample r 6) := by decide +kernel

theorem firstWire_nonzero : firstWire ≠ zero := by decide +kernel

def neighbor (i : Fin 9) : Nat := [4,2,1,2,3,0,8,2,3].getD i.val 0

def keepSeed (i : Fin 9) : Nat :=
  if i.val = 0 then 1 <<< 6 else if i.val = 6 then 1 else 0

def absentRow (i : Fin 9) : Row := Fin.ofNat 512 ((1 <<< neighbor i) ||| keepSeed i)

def presentRow (i : Fin 9) : Row :=
  Fin.ofNat 512 ((1 <<< neighbor i) ||| (1 <<< i.val) ||| keepSeed i)

theorem firstWire_witness : ∀ i : Fin 9,
    (bit (absentRow i) graph != bit (presentRow i) graph) &&
    ((inputs++[firstWire]).all fun w => w == inputs.getD i.val zero ||
      bit (absentRow i) w == bit (presentRow i) w) = true := by decide +kernel

theorem all_roots {k t S} (h : Live graph k t S) (sub : ∀ v ∈ S, v ∈ inputs++[firstWire]) :
    S=inputs.toFinset ∨ S=(inputs++[firstWire]).toFinset := by
  have all (i : Fin 9) : inputs.getD i.val zero ∈ S := by
    have cut := firstWire_witness i
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
  by_cases hfirstWire : firstWire ∈ S
  · right
    ext w
    constructor
    · exact fun hw => List.mem_toFinset.mpr (sub w hw)
    · intro hw
      have hx := List.mem_toFinset.mp hw
      simp only [List.mem_append,List.mem_singleton] at hx
      exact hx.elim (fun h => needed (List.mem_toFinset.mpr h)) (fun e => e ▸ hfirstWire)
  · left
    exact Finset.Subset.antisymm (fun w hw => by
      have hx := sub w hw
      simp only [List.mem_append,List.mem_singleton] at hx
      rcases hx with hin | rfl
      · exact List.mem_toFinset.mpr hin
      · exact False.elim (hfirstWire hw)) needed

theorem initial_live (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (first : ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 6))
    (computes : PEqualNP.MetaComplexity.circuitFun 9 C = edge) (small : C.size ≤ 15) :
    ∃ k t, k ≤ 14 ∧ (Live graph k t inputs.toFinset ∨ Live graph k t (inputs++[firstWire]).toFinset) := by
  have headEq : (execute C.gates inputs).getD 9 zero = firstWire := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C legal 9 r).trans ((first (sample r)).trans (firstWire_table r).symm)
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
    exact False.elim (firstWire_nonzero headEq.symm)
  | cons g gs =>
    have eq0 : gv inputs g = firstWire := by
      rw [hgs] at headEq
      change (execute gs (inputs++[gv inputs g])).getD 9 zero = firstWire at headEq
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


def sixScore (a b c d e f : Bool) : Nat :=
  let x := b.toNat+c.toNat
  let y := (!e).toNat+(!f).toNat
  if a then if d then y else max x (max y (x+y-1))
  else if d then 0 else x

set_option maxRecDepth 20000 in
theorem sixScore_and : ∀ a b c d e f g h i j l m : Bool,
    sixScore (a&&g) (b&&h) (c&&i) (d&&j) (e&&l) (f&&m)
      ≤ sixScore a b c d e f+sixScore g h i j l m := by decide +kernel

set_option maxRecDepth 20000 in
theorem sixScore_or : ∀ a b c d e f g h i j l m : Bool,
    sixScore (a||g) (b||h) (c||i) (d||j) (e||l) (f||m)
      ≤ sixScore a b c d e f+sixScore g h i j l m := by decide +kernel

def scoreRow (code j : Nat) : Row := Fin.ofNat 512 ((code >>> (9*j)) &&& 511)

def wireScore (code : Nat) (w : Wire Row) : Nat :=
  sixScore (w (scoreRow code 0)) (w (scoreRow code 1)) (w (scoreRow code 2))
    (w (scoreRow code 3)) (w (scoreRow code 4)) (w (scoreRow code 5))

theorem scoreCombine (code : Nat) (a b : Wire Row) (d : Bool) :
    wireScore code (combine d a b) ≤ wireScore code a+wireScore code b := by
  cases d
  · exact sixScore_and _ _ _ _ _ _ _ _ _ _ _ _
  · exact sixScore_or _ _ _ _ _ _ _ _ _ _ _ _

theorem run_length {R} {target : Wire R} {k ws} (h : Run target k ws) :
    ws.length ≤ k+1 := by
  induction h with
  | stop => simp
  | perm p _ ih => rw [← p.length_eq]; exact ih
  | one s _ ih => cases s <;> simp_all [kept] <;> omega
  | two _ ka kb _ ih => cases ka <;> cases kb <;> simp_all [kept] <;> omega

theorem run_score {target : Wire Row} {k ws} (h : Run target k ws)
    (bound : ws.length=k+1) (code : Nat) :
    wireScore code target ≤ (ws.map (wireScore code)).sum := by
  induction h with
  | stop => simp
  | perm p _ ih =>
    rw [← (p.map (wireScore code)).sum_eq]
    exact ih (p.length_eq.trans bound)
  | one s h _ =>
    have hn := run_length h
    cases s <;> simp_all [kept] <;> omega
  | @two n a b rest d ka kb h ih =>
    have hn := run_length h
    cases ka <;> cases kb <;> simp_all [kept] <;> try omega
    have hb := scoreCombine code a b d
    omega

def scoreBelow (code : Nat) : Nat → List Sig → Bool
  | acc,[] => acc<3
  | acc,w::ws =>
    let acc' := acc+wireScore code (observe w)
    if acc' ≥ 3 then false else scoreBelow code acc' ws

theorem scoreBelow_sound {code} (ws : List Sig) (acc : Nat)
    (ok : scoreBelow code acc ws=true) :
    acc + (ws.map (fun w => wireScore code (observe w))).sum < 3 := by
  induction ws generalizing acc with
  | nil => simpa [scoreBelow] using ok
  | cons w ws ih =>
    simp only [scoreBelow] at ok
    split at ok
    · contradiction
    · have h := ih _ ok
      simp only [List.map_cons,List.sum_cons]
      omega

def readOnceReject (T : Sig) (codes : List Nat) (k : Nat) (ws : List Sig) : Bool :=
  (ws.length == k+1) && codes.any (fun c =>
    wireScore c (observe T) == 3 && scoreBelow c 0 ws)

theorem readOnceReject_sound {T codes k ws} (nd : ws.Nodup)
    (ok : readOnceReject T codes k ws=true) : Impossible T k ws.toFinset := by
  simp only [readOnceReject,Bool.and_eq_true,beq_iff_eq,List.any_eq_true] at ok
  obtain ⟨hlen,c,_,t,hc⟩ := ok
  intro l n hl run
  have h := list_run run ws nd rfl
  have hlen' := run_length h
  have he : ws.length=l+1 := by simp only [List.length_map] at hlen'; omega
  have sc := run_score h (by simpa using he) c
  have low := scoreBelow_sound ws 0 hc
  simp only [List.map_map,Function.comp_def, Nat.zero_add] at sc low
  omega


def keyWord (v : Sig) :=
  let n := v.toNat % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
def keySet (xs : List Sig) := xs.foldl (fun v x => v+keyWord x) 0

def closeChild (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  pools.any (fun p => scalarPoolCut p k rest op) || (links (keySet ws)).any (sameWords ws)

theorem closeChild_sound {raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild pools links k rest op = true) :
    Impossible T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨p,hp,ok⟩ | ⟨xs,hx,ok⟩
  · exact scalarPoolCut_sound (pValid _ hp) nd ok
  · rw [sameWords_sound ok]
    exact lValid _ _ hx

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

abbrev NodeContext := Nat × Nat × List Decor × CovPair × List BoundPool × (Nat → List (List Sig)) ×
  (Nat → List Sig → Bool)
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links,extra) := c
  let un := op==2
  let len := 1+(n - (if ka then 0 else 1) - (if un || kb then 0 else 1))
  if len>cap then true else
    let d := len==cap
    let rs := restCov (getCov cov d) (column d a.2) (column d b.2) un ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 768 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (opKeep un ka kb a b ws).map Prod.fst
      extra (cap-1) (z.1 :: rest) || closeChild pools links (cap-1) rest (movedChoice op a b)

def moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (movedDecor op a b).1 :: (opKeep (op==2) ka kb a b ws).map Prod.fst
theorem evalMove_sound {raw T r s ws pools links extra cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : (op==2)=false → a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible T (cap-1) (List.toFinset xs))
    (ev : ∀ k ws, ws.Nodup → extra k ws = true → Impossible T k ws.toFinset)
    (pro : proper (movedDecor op a b).1) (fresh : (movedDecor op a b).1 ∉ ws.map Prod.fst)
    (test : evalMove (cap,ws.length,ws,preCov ws,pools,links,extra) op a b (movedDecor op a b) ka kb = true) :
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
  simp only [Bool.false_eq_true, ite_false, Bool.not_true, Bool.false_or] at test
  simp only [Bool.or_eq_true] at test
  rcases test with other | close
  · exact ev _ _ ndc other k t hk h
  · rw [val] at nd' h
    exact closeChild_sound pv lv nd' close k t hk h


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

theorem node_sound {raw T r s ws pools links extra cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible T (cap-1) (List.toFinset xs))
    (ev : ∀ k ws, ws.Nodup → extra k ws = true → Impossible T k ws.toFinset)
    (checks : testAll (cap,ws.length,ws,preCov ws,pools,links,extra) ws = true) :
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
    exact evalMove_sound pairs faith nd ha ha (by simp) hc' pv lv ev pro fresh (all_unary checks ha keep)
  · intro a ha b hb d ka kb ne fresh pro len
    obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
    obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
    have ab : a≠b := fun e => ne (congrArg Prod.fst e)
    have one (a b : Decor) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
        (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
        (test : testPair (cap,ws.length,ws,preCov ws,pools,links,extra) a b d = true) :
        Impossible T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
      rw [←binary_front nd aa bb ne']
      have eq : (movedDecor (if d then 1 else 0) a b).1 = bin d a.1 b.1 := by cases d <;> rfl
      exact evalMove_sound pairs faith nd aa bb (fun _ e => ne' (congrArg Prod.fst e)) hc' pv lv ev
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
    (if k=0 then true else testAll (k,ws.length,ws,preCov ws,rules,ls,fun _ _ => false) ws)

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
  apply node_sound (raw:=vars g.mask) (extra:=fun _ _ => false) samples _ hN hT _ _
    (fun _ _ _ hf => by cases hf) (by simpa only [h0,if_false] using checked.2)
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
  simp only [checkAt,evalMove,closeChild,cut,Bool.true_or,Bool.or_true]
  repeat' split
  all_goals rfl

def fallbackAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  checkAt c i j op ka kb

theorem fallback_sound {c i j op ka kb} (h : fallbackAt c i j op ka kb=true) :
    checkAt c i j op ka kb=true := h

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
      then true
      else xs[q].2.2.2.2.2.2 (k-1) (moveFront xs[q].2.2.1 op
          (contextWire xs[q] i) (contextWire xs[q] j) ka kb) ||
        closeChild xs[q].2.2.2.2.1 xs[q].2.2.2.2.2.1 (k-1)
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
  (k,ws.length,ws,preCov ws,rules,ls,fun _ _ => false)


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
def deadsamples : Array (Bits × Bits) := #[(0xf854605d026923a5a16008862c9d18d42fd85e54d221898f1e440284a107a02910c3e03c06c40d2642ca74f54627022c11e389d9b43b30c961ca72386ce81500aa210d1ba1a121108a6c99348979d054ac200727ac054c0970110780155ad581,0x6844620d0040231585204884208800c4270824141201090814040082a10700282003e02402c4084602ca04a440240a1091218919100a2084314a220840a00480aa210819a02120100a4409048968c05484200702a805440920100380144a9480),(0x80b20c31f72bfc4e1481d27000d43c9c5bd438a9c5e0286040f054f111d001ce10920229bde170b8d339029e2bcac4cd494fb74d1052452141a61c5b9ca1e642f40c600258428f0e5c00df481e03202a204cd465e10fe01206e82c7b03150603,0x80100c30e6089040109182600012282018c41889c5e0204002b0604000c009861080028b1c2120a0d12000120908c00d005a724402504200402010501c01c208540860025840090e1400964816012008204cd0254102a00206a0247b01150201),(0x12ce100c308544478a85796a2341d206e4242e31335abb35943abb40be28c8e05c4c115123137950052a02a9ba0d31c096458c656cc338623e92230683d8962194d5145c2aa62229438824d8e06246d0cd124850733918c390189888a426380a,0x10ca0000108540870900790a0240900460282200221a991490081a0028289000cc41010021184410080a0a28a20020c0200184206c0128621092200a03d8103080d5145c02a2022143880090804206d04d100840322918c190088800a4221002),(0x8628ebbd17000228c83c0291b729e17b3643984a392a815889878936d04e41b82b8e28807cc302855ead3105d9868885c748c2b0724ae81086518e259124cd4278a18b4aa01db88524c3a3435a0814469349110c18f0c24c2a8052bd88818268,0xc2206a1d05000020401c0090e509051303449848110100480001811490070429238c000818c508010485900541c68805c240409012420000024186258024450270208b02a00da0842041a3414a08100690490104085040042a8052bc00818028),(0xbc8ccda8781e4d8151cd3cf93a4a0a01509a42078c1bc4a783ea4aec6c7bbbd02ef85be130b1750bcd872a062d01842a34826040203d5b99ac8899721d47b82106b4f88001d04ee6f42e103eb14e0a090b95e84905a08ef7a2230402e2b14bc5,0x148981a0109a5c8210c1a4690a42220050930202c418c4a7837a48680e50b9d00c601bc02020f518c9002a002c1124282402304220255b598c9019921c51b8010494708001d04e62d42a103a30060a090b94e84905a08af280230402e2304b45),(0xd3b19712becef4647857054f8773c68492608a46265cd6cd0106c449284294958830b40e8328a4102841c46a63b66493288c7290c714876750b08cb0eb0a532e014ce7e24f9c08720240400006971f885be46b00080a21145aa7f52cf42a8012,0x92218c003e8654007015040a0c73c50280c0084821449285810a8400004080918c301008002824100801c000230200c0688c40804110046300b00cb28307502a0004c5624f9c086200004000021315805bc46800000a00145205f42ce0200002),(0x3145d24845746a93b60987114c89950ee90ab5809889781e716b0d141d9e036fea797f20c896480c8b565809c5575a81eabcad03980701be24b7e8d7401960b32336416db2f0c4c050f169960250e8b311988b92828b0074bd455ad232c2112c,0x2307720c00346283a400011d4c09950fa108a4001a095004514a0014181e2261ab3d3060c0d6480a2ac41009e4571880ea848181d90321bc24d38a860208103323340169a2b084c040f169960050c8b211800b9082890074b8455a803282012c),(0x49615339cc24bb41a658244591d020101222d0f578b5376254a121290a30cd5c4e2ad1d6dabfa9e032f022500c91031b32331a7a9ace0ca4e96243014a4009cd0d2a3210b66014de852533c420acc80ff443ad9cc5d0f4808cd621151170ac54,0x4900539a4030aa408668006591882010120251355ca1242200a1212102144d6e020a42d6d2878b6832b420400cb9813312321a4a924e408ce04943054c0001c10d2a2200b040149c8425334420acc80fa003859cc5d0e4000cd201111150ac54),(0x2108654280dbc21c532263cad6a2ab60a053058994f658a43b3dd89384745a04932387065124c385d01899e2cc083e3c1e3327061d61ca921a4965c8583262f4485320b5c04953298d1f02098424a39520b6148b236021a80528c3236c545ab4,0xc0001428049001c03a04a4012802a200013019184320c200a34088304a0580410028702010083a440180cc2080827381411260a0400ca0098085048489022c408432094004053098d0e0008842422012032140b21202188052801030c545a90)]

def aliasDomain : Sig := (inputs.getD 0 zero) ||| ~~~(inputs.getD 6 zero)

def aliasInputs : List Sig := inputs.map (· &&& aliasDomain)

def aliasGraph : Sig := graph &&& aliasDomain

def clipBy (m : Sig) (r : Row) : Row := if bit r m then 0 else r

theorem clip_general (a m : Sig) (origin : bit 0 a = false) :
    rename (clipBy m) a = a &&& ~~~m := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let r : Row := ⟨j,hj⟩
  change bit r (rename (clipBy m) a) = _
  rw [bit_rename]
  have e : (a &&& ~~~m).getLsbD j = (bit r a && !(bit r m)) := by
    simp only [bit,r,BitVec.getLsbD_and,BitVec.getLsbD_not,hj,decide_true,Bool.true_and]
  rw [e]
  by_cases h : bit r m=true
  · simp only [clipBy,h,ite_true,origin,Bool.not_true,Bool.and_false]
  · have v : bit r m = false := Bool.eq_false_iff.mpr h
    simp only [clipBy,v,Bool.false_eq_true,ite_false,Bool.not_false,Bool.and_true]

def aliasRoot6 : Sig := aliasInputs.getD 6 zero

theorem alias_cofactor : Lower (vars 447) (graphGoal 447) 13 := by
  apply relabel_of (old := 447) (rep := 383) (swaps := [65,50,131,84,118,135]) (by decide +kernel)
  exact low383

theorem alias_lower : Lower aliasInputs aliasGraph 14 := by
  have pG : proper (graphGoal 447) := proper_of _ (by decide +kernel)
  have pA : proper aliasGraph := proper_of _ (by decide +kernel)
  have s := lower_slice (T:=aliasGraph) (G:=graphGoal 447) (roots:=aliasInputs)
    (other:=vars 447) pA pG (movedRow (fixRows 64 0)) (by
      rw [← moved_eq_rename]
      decide +kernel) (by
      have h : aliasInputs.all (fun a => freeWord (vars 447) (movedWord (fixRows 64 0) a)) = true := by decide +kernel
      intro a ha
      rw [← moved_eq_rename]
      exact freeWord_ok (List.all_eq_true.mp h a ha)) {aliasRoot6} (by
      intro a ha
      rw [Finset.mem_singleton.mp ha]
      exact witnessB_sound (rs:=(257,321)) (by decide +kernel)) (by
      intro a ha
      rw [Finset.mem_singleton.mp ha, ← moved_eq_rename]
      refine ⟨false, ?_⟩
      have h : movedWord (fixRows 64 0) aliasRoot6 = zero := by decide +kernel
      rw [h]
      exact funext bit_zero) 13 alias_cofactor
  simpa using s

theorem alias_slice : Slice (vars 511) graph aliasDomain 14 := by
  let r := clipBy (~~~aliasDomain)
  have formula (a : Sig) (h : bit 0 a = false) : rename r a = a &&& aliasDomain := by
    rw [show r = clipBy (~~~aliasDomain) from rfl, clip_general a _ h, BitVec.not_not]
  have geom : restrictRows r (observe graph) = observe aliasGraph :=
    (observe_rename r graph).symm.trans (congrArg observe (formula graph (by decide +kernel)))
  refine ⟨r, aliasInputs, ?_, ?_, ?_, ?_⟩
  · intro i
    have negs : bit i (~~~aliasDomain) = !(bit i aliasDomain) := bit_neg _ _
    by_cases h : bit i aliasDomain = true
    · have hn : bit i (~~~aliasDomain) = false := by rw [negs,h]; rfl
      simp only [r, clipBy, hn, Bool.false_eq_true, ite_false]
      exact h
    · have hn : bit i (~~~aliasDomain) = true := by
        rw [negs,Bool.eq_false_iff.mpr h]; rfl
      have hz : bit 0 aliasDomain = true := by decide +kernel
      simpa only [r, clipBy, hn, ite_true] using hz
  · intro a ha
    have inputs_eq : vars 511 = inputs := by decide +kernel
    rw [inputs_eq] at ha
    have origins : inputs.all (fun w => !(bit 0 w)) = true := by decide +kernel
    have origin : bit 0 a = false := by simpa using (List.all_eq_true.mp origins a ha)
    rw [← observe_rename, formula a origin]
    exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem ha))
  · rw [geom]
    exact observe_proper (proper_of _ (by decide +kernel))
  · rw [geom]
    exact alias_lower

def aliasColumn : ColumnInfo := (0,0,0,0,14)

def columnDomain (ci : ColumnInfo) : Sig :=
  if ci = aliasColumn then aliasDomain else subcube ci.1 ci.2.1

theorem chart_full : chartGoal 511 = graph := by decide +kernel

theorem column_sound (c : ColumnInfo) (prior : Nat → Nat)
    (valid : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (ok : (if c = aliasColumn then true else colCheck 511 c prior) = true) :
    Slice (vars 511) graph (columnDomain c) c.2.2.2.2 := by
  by_cases h : c = aliasColumn
  · subst c
    rw [columnDomain, if_pos rfl]
    exact alias_slice
  · have hh : colCheck 511 c prior := by simpa only [h, ite_false] using ok
    rw [columnDomain, if_neg h, ← chart_full]
    exact col_sound c prior valid hh

theorem completedRoots (plain : Impossible graph 14 inputs.toFinset) (seeded : Impossible graph 14 (inputs ++ [firstWire]).toFinset) :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 6)) →
      PEqualNP.MetaComplexity.circuitFun 9 C = edge → 16 ≤ C.size := by
  intro C legal first h
  by_contra! small
  obtain ⟨k,t,hk,hdead | hlive⟩ := initial_live C legal first h (by omega)
  · exact plain k t hk hdead
  · exact seeded k t hk hlive

-- The certificate stores circuit prefixes, restrictions and links to smaller live sets.
-- Transition checks recover each state from its initial segment and compare the full truth tables.
def seedReversedBytes (i : Nat) : Nat := 0xff7fbf3fdf5f9f1fef6faf2fcf4f8f0ff777b737d7579717e767a727c7478707fb7bbb3bdb5b9b1beb6bab2bcb4b8b0bf373b333d3539313e363a323c3438303fd7dbd3ddd5d9d1ded6dad2dcd4d8d0df575b535d5559515e565a525c5458505f979b939d9599919e969a929c9498909f171b131d1519111e161a121c1418101fe7ebe3ede5e9e1eee6eae2ece4e8e0ef676b636d6569616e666a626c6468606fa7aba3ada5a9a1aea6aaa2aca4a8a0af272b232d2529212e262a222c2428202fc7cbc3cdc5c9c1cec6cac2ccc4c8c0cf474b434d4549414e464a424c4448404f878b838d8589818e868a828c8488808f070b030d0509010e060a020c0408000

def seedGatePairs (i : Nat) : Nat := 0xfefdfcfbfaf9f8f7f6f5f4f3f2f1f0edecebeae9e8e7e6e5e4e3e2e1e0dcdbdad9d8d7d6d5d4d3d2d1d0cbcac9c8c7c6c5c4c3c2c1c0bab9b8b7b6b5b4b3b2b1b0a9a8a7a6a5a4a3a2a1a0989796959493929190878685848382818076757473727170656463626160545352515043424140323130212010

def seedColumnWords (i : Nat) : Nat := (if i<1 then 0x24e004c1500d1820a850052d003450153002b0580138409150054d002c50054c00ac500565002650853002a25015840898504584089251053002925005c4088a5204e0048550063800715802708023580294801a5006982049500ea004545026a004515006c4004e5802c4800e5006e004455006e0004750071820295007300232540584081a500f80200e500788200d500790001b500790200b5206a0041562405e00a0600978418063005e008860a18c11806001dc018860425e006061421e00506012d4810861025e00486012e48104640938411062421e0030604b18212062025e0028640178410163021e001860238c111060838c1104680938409060254d0028602565002260953002a0680178408168218c10906055840890611530029068818c10846015c40888620ce004846045c40882618530028261256100036224e00481600678006160963002606c007840416812708021602ea0045060469820416812c4800c6414c408486802d4800a6802e48006600ee004446026e00441600f1820286017300230608730022268038c10146415840818600f90200a620ea00414644584081261073002126405c4080a6206e0040571425e004072425e0020740978410073025e000870a38c1100780978408071252d001078a18c10807055c4088071953002807812d480087812e48004702ee004407c01784001709730022078238c1010745584081071173002107415c4080878838c10047445c40802720ee0040471873002027226e0040183425e00008c0978400088a38c10008455c40800822ee0040081973002007002ec01447002f8014170035c012870037801217003b801117003cc010c7004f800c170057400a27005b400927005e800857006d4004a70071c003870077000237007c4000e7007e000078003ec01048003f8010180075c00288007d4000a8007e8000570007c01e070029c01587004e400c670053800b170058c009c7006b000538000fc01c080017c01a080027c01608002bc01508002dc01488002f4810280039c01188004f400c280056d002480056c00a480057800a180059c00988005cc008c8005e400868006b800518006e400468006f000438007380031800798200980079800199001fc01809012f4810090037c01209003dc010890256d00209005dc008891056d00049005f400829005f8008190067c00609802f480029006f800419007780021900f9820089007b4001290479820019007cc000c9007e400069007f00003a1256d0000a812f48000a04f982000b002fc0140b004fc00c0b0057c00a0b005bc0090b005ec0084b006bc0050b006f40042b0079c0018b007b80011c003fc0100c0077c0020c007dc0008c007ec0004c007f40002c007f80001d005fc0080d006fc0040d007bc0010e000000000 else 0x40005e00e840005c01e840006c01e440006d016440007481a240007841c140007801e14000e4818640018c119440018c019c40021e007840027001634002708123400294811a40029821494002b001534002c4810e400318212940031801394004e004c54004e000c740051820a940053002b240056000a7400584089a40063000734006a004554006a00057400780001f400780200f50405e00e051005e00c85010e4818451006d01445000f4818252005e00a850017841815001cc018c50818c118450421e007050025e00685012708121540078414151021e005850429821415012b081115012c4810c5002d4810a5002e481065002f0810352021e0038500b1821285043182121540138411150038c1114500398210958007480a250047800e158007840c1500ce004c45004f000c350)

def seedScoreWords (i : Nat) : Nat := (if i<1 then 0x120b068982001150e052116422a034081b288a54142a07055683208a5526b606914229b68b3489451a0d36a4588a54341a8f0550a0145438148551382c0e27078a81404130a84c0e090260b158706380ca0944831ca0501341a8d303380ca0340819cb038268345a583450a88ac532aa90205142a05885381a08a55269e203104532935111a0c8d04d350d86914683c3a134383422934ca3c0683268311a4361a0c8904c250da0980341b1d1848a44992cd65c58c86868351b06c453220303a0b288250150ac7451190d0d06a260d9149280d06229a80824894426424d04941289066904c04884ca24242001140e0521104010241a0b030281240a15061604914643a1b0345088028950aa88a0d1a1d0784d124d080c0e82d2493422916aa348a845340e0525568305149a45b446832341a4d436440a00a8512aa004010a0582a0308004141a0584414092a158aa0b229270385c4935248ac0e47129a8102869241e4285024190686c2c0a2404426512501301229368b0905024c0623082c92684522d5469190d0d069360db05818a45a2b8380081930974c82002044c25532045224e8763aa2e040a22d149b0a410880a8512a88642a229549a3a14090241a0b03205013a1d8eb0368322031184b60643468349a83605408643a9942904813a1d8ea836422a29158b32b0104343a0d98482409a0d469418e06880c46127845609a0d8e8628d0648142a0c6c3412514aa459a48a648a456686545224d06a34a2c6512452ab1532090280a150686b048a68741b18a2a114543a159548a54341acf055808248b4426c246028028541a3824915a0d86a13428120483416160a2406436592506434341acd836681c229949a3c12014142a058940a014141a0585624324562955328102865321d42990d0c0e2722d8601808ac532b80926868345e0691a0c8d04c350d81409120984a0b80080930934c83058168349a38345225a0d268a2ce03280d06067214090241a0b0b1908a80d0606ca3211629348a994d06448261286c4081444a213216020922d149b0905024d06a3482e040a12490590a80080130914c8205018a45a2b03120a064361d0b0c845683c1a2650a0145038148541301229368909894530383c2c584822048341626190d0d06a360d89245c0e270a4d1a4508a65a2cd1a054343a0d8d48240992cd65c18d06468361a86c22950d0693c154683240a1506360502428160a82c683268351a436281208a5526962283422d14cb346824a034181b492014192c86c9404814241a0b0362912c0e17071668304d07834b46050168349a30380c0a29158b40ca041150e85651683230391c4b61002002a144aa01a0c8d06c350d82008028541a1814090643a1b0b008020483416064805044a213250d049683c1a26905024a0522882ca845341e0d255 else 0x32114192c86d940a04980c4610586512683c3a13204828d0693502ce068229568a7809051028342858281224834961644e04e87cba62704813a1d8ea838141182c362c188a64884466065229922915981944404341a8980622992050391196251468349a91681088130914c89243222b14cab232015a0f048894c0c0229958ae0381a20211849e11381229368b8922991a0d178196050464b2d9b0682090930934c900a811109944852a114503884156040a1a4c0710a641a08ac5a23a20241194c8e541482208a5526a604828190d8342c80c41148b4d444a845341e0d655190d1a0d36a0d8d04948281226914090643a1b0b49245c0e230a4d249170383c29341205090682c2932116291c8a9944828190dc742c249a1148b541a4280505060161581411a0d26a4188a648a45648658140628368ac0e02c144c84c34132124d04c34994440928148a223820908b0732c80a001341e0d21104c0a030981c28e0328a1562c72c12270383c4e28d0c804ca310e80482868351b42a200922d109b18c102464b21d6201301229b689093a114d07834954926868345c0692a1160311a09546832341b0d63634191a0586a1b069142299e8b34c1604e8763ae0cd0498148a0669321160522819962912c0a17071601004a0522880d82d04522d34d1890c91188544c8c845482c1226534190643a1b1b30581341a8d383112080a2542a8b058168349a303241408a4f2a96114893a1d8ea0b22925a0d46c1348a54144207055241408a4d2a960c868190d8746c3412514a8459a513012213289090502428060a82cc86868350b06c249a10483511a6040a22d109b0a44c048a4da24249268456295469190d0d069268d8d04968381a269303008a6762b80643468345a836890c9a0d1784c22905341e0d3152491520984a136040a184c0710a80100653239500d049482c122691109)

def seedAutos : Array (List Nat) := #[[], [118, 130, 81], [100, 131, 82, 16], [116, 80, 100, 128, 48, 32, 16], [116, 83, 32], [100, 116, 81, 128, 49, 32], [118, 133, 33, 48], [82, 129, 48], [100, 131, 116, 50, 33, 16, 80], [116, 50, 129, 80], [100, 49, 128], [116, 100, 49, 32, 81, 128]]

def seedLookup14 (i : Nat) : Nat := 0x2

def seedRuleCodes14 (i : Nat) : Nat := 0x120018002800480050008080c0018001000400200038006

def seedHeaders14 (i : Nat) : Nat := 0x800000000000000000

def seedNodes14 (i : Nat) : Nat := 0x7400010800

def seedRules14 (i : Nat) : Nat := 0x141ef2d66a0d516e

def seedScores14 (i : Nat) : Nat := 0

def seedLookup13 (i : Nat) : Nat := 0x6aac66e56244c94914600000024008840048450017024640880018000422000006c8360c099806ee000072c958c001c00f02b800d0005d00000092602280035700a93020219a047803b04a003410f40021d08183302c1004a00023000100000056001204e80001001444f00212e652277ec57be04a60ad54008b500c98160070f850cf0070212cf0802c00020000040030c400b081040003040041

def seedRuleCodes13 (i : Nat) : Nat := 0xaa0108020803e0072008c00c0016041e00340010601000200000200034006400a400c80150412080420204000812100c2008009000a00b801e8008000e00180020037003a0048101800c003c1014013800a002800b01080206040e0838104020b080c103020404070c061008209040a

def seedHeaders13 (i : Nat) : Nat := 0x200000174e00b800004400000164000b800008800000000000000000

def seedNodes13 (i : Nat) : Nat := 0x232ce04857c094a781114703127e0564dc0549781e90f04920e0763fc0cc7b8130ef0401ce04a35c0d8678210c702517e0862dc0e85781806f03e0ce06417c1002b81884f04308e0260fc0e41781b02703e03e07605c0dc0780c00701a2960304ec0509981486b0258c60530ac093e98187cb038f8e061f140767300d40602aaca0795740b6a681c54503aa7a05b4d40ba96814ca502393a05b25407a4281c7d2027fa004df38093e50167c8024f8c049f100b3e1015fc003d03e06a03c0f80381a3c0

def seedRules13 (i : Nat) : Nat := 0x16f07003b7d177a15b7c1ef10adb1e6cada3d831fdcd815b5db7bbb82b6bb95ee317b41f55500dff2b683bf1eaa2f360658e56d0541950eff1cac2f2aae00e42d57f0139585ed06aacff943c8a1ca048e4d88b8c54efbebf8f3f2688b949e8645115023b3c5e0a623eda0e8fd85e361dea5bd0b1e741851a2811e45ef7be22a7200bda0a62d883ad8bda09bec25bd0b9968d8c2a7663fe656360c5e8e2f706cee39fe6568519c812b68293465a0ecad5e826c657a50b2b0bdea62d0747e56178b3612e42c3b854e703c539c619303b939d07c29226c8a1409676641f0a471b34fe56d1e317b41850246395b410f85621a39585e85203955c2f8716e3bdb7596ace0079dbacb4fea027df9eb2d3a4413ced969d0d83953ced969f3e64c04f3b75a747026dd65a63380ea7b66e7104c7361536fa7d66e78604d21e641dcedd65a70c44fb90b4aae0062f622a0720b50acb024b46c1b10bdcb50acf024850ac082485a4c5b80ec85a36311256f2d566e65eba57b7908d2f34ae5dbc85a4f9d742e3f6f2168dceba17

def seedScores13 (i : Nat) : Nat := 0

def seedLookup12 (i : Nat) : Nat := (if i<2 then (if i<1 then 0x797962adb29cb40464e1a3eb2389d45d29471b1445549d9f8006932752aa9d800173a7eb1400139a5c741a52003dea4ea6a5868a32c6380e7ec7f9770b2a3afaa69ce9a9521e55b2c34526d065003feba00185d9c64aa9bb7a4fe7cc84add59527812b90118b828918804e8889124877100a09ba999c6306b1d1041301393016a4ac808344a64f354103c518ef8c4d481aabcc5c51f01c9f628b978fe23c808da0ad0bcf4904a14e8229237426bd10b2146009a4c92ec50636c298e70033e0cd2ce4548c87532c9d30f00028f9d14e518b1a0060fa8d1fa001340d321f523124004078645b43e8bd3f88900022e36e0265db011db080c8a62a3ce4ddebc663acc5118e55d4f79fa2c439c959b40005cea75784125ec40048cc58cc3c827a4f5c25a92b9d47ae3fc4a3ab03a7029ed066f046a152858aee45b251b3e0bf49339617f39a57054358761164a041a94d7e0cf4fe56e07ca4192d3c784f714cb1d50bef9ce1456b25a21f25076a800547ae2523d82e7314ac239de52c0924c0441053a3d321c465788439068e67e03d436208ee41995e49e2d80a1888f2812f48da120b8ccd25a2ecdf15a2f91608a85c3f00480f0160f60b4b300100e1b029016068448110130120e404952000000040530905b401863014620151b805c0083900020a188600462620b4160062c800012808032000bb8090001c8030112164300d030000100000000901085212a0be0700a8190142f8078000ee002048920180140805d12a588c685e1ae1a4328000d48740821f0205ec088560161bc3100e12a00c2a0070100643b94108e0003308a3bc054de8070623840186222c02c138fb0761504c01a1380052d0f40ee12c0303c02a0dc0000f030000178010220c402000086204008440500040000016e02ca10400020cc0601b0cc25c2f0000140401380a0000005080303e6708102d00c1d00703400a0880f80808202c0805c0100342000a044000220130260386a03900025c3d02c05e59c170050040500805a0100640f8db1221a80000700c05c0d00208210c0380b0b42083103100e09c2100a0020040301b0420140182102e0fc0682a0520441880f0480001985800404c128790b80401b00607e01c020060000ec2f80a00803c0180c03e06c01002002288000b90040284b81301e1800080200624c09003068000180460a63148f82c00207c0900207c2ac4003d0120002d82216a0d41981e00e0000986f01002c020e40080081900c02c0240c803060304000280500401806809c000010550380000200f0322e8010790000282a80102a0580880e00c0040682b1401d40f05700600c1881803e018060030640200004004c0d00400b01a0140b80404203c010030040940d8080040602b8100120100b00300a0000082404c03c1104108a0000280202c0002c000 else 0x49a445a9c4f703fa74ef2269f41365204aa73043220379f29a875ce91f65452f05b8c4000109e720f97a5554dcb80011d073544808a8c96453261426583129d72d1fa0fe21800299c930003ec715234aa6e4891ea00038577aaa94c4ec771ba09c8487d4c64462cc722b73e112cc11296b8c59dd17e26892d52a96984a3a9e4f66bb02d78a018aa7e43180f0005e8aa1af0562bcb3b842320b6538f964f16803c244cc2f4442874ca099eea770264f0fa82837900d7339c67ce9501b4605f2a9864b96a8d6819b552660000a807187154003f16be21cbfa1526ad567f377834c9074ae5475505642e96b23d5c90b139ec850888a67b1a59fa67748c6489cca86ef690eaf942e6286739a5daa4193bd184236647b152ae7ee8bbb073b1b93da92a18ffcd91903b2458039fd1981b929c4696cb9dfd4d79b4be110c5e53cac26106d2e0864350003ce62d760a9000bad4e11b5681eda8ad17aa9c1044c844b32de518706c374070007667569ccb58c83ac4bc537f61499cac090d1b0b722956a0011f0500b249ca6004675109fc1cd5fd09c41c72646370a38f20f8dc43e3e36123017fafa4a8a6d9e15f992679feb8748e816734ed0c41623643a57e8d83a53b69ad89eeb8623c809a81ad2169158b8f17d2c1e7a0ec6e61d89b21f81d27267a06a0eaeccc02c19ab79414448874da6ea7e274ed0000b674e7c0d845f340cc1049f127222e383bf4f35390f07802e881f085b2fa9de6f23560af21054a3242c718a52915000261870608ca627ad5470b9a19a4236a2b0f3382000c36843818e72c679ac64a2bc99aa712d8f041947784a349218ab6d8c79833e84e61fdbf1e0001440401603393567d8fc9c815e7601a0c03d17c19b5ea4a0c1b947e63be110bea7edb63e9689acab8ac9e25c816999ac391a34e062976bc4f8a33b24dd07407a8430a02197c1b6de59589a61820c10e28580bc45091cd71a32385e467022071aba3f1dab4d683d84fb0c04e4faa5477a7128193e9c5c2c3176ceb0a88043a7494260a36a30ed3fae7908a290e4fd6ecb3235885100129d713fa071e9ee47516b460a989f530032963e590e1f8993794065707b1c82a053d2e8372dec2d1b11d95111d718d24a5020629109302b4f206b1cb50d254125708ec5fc8a00d32e1326fa5e321b00451de970320968f64cd3d00d35134c07cba3b4c2d84072a1e039f337ba333ca7825f20e119a38a653b2b49886838f36e608472374c40539832e50a6fc56502b5cbab0363e59a689189a86856fbb15b41ea0a82966e01ceecff28293ccb108194cad3a54783c569f804ba8b340b6bfc25e35de200983f248078ae850d0a3424c05c6c6228e89ca0d1ecaf056c6188a207a0f38565abd78ed00511623930d6313105666393f21a0c513913a635f33822b4c83ac8ec3300f52e9c10c4) else (if i<3 then 0xa020c4041002807e2861000101e0000000040772021430001c44086080006c4090144001988904103005f020080010170400080800590d9810040145104a20840492091c484010113000248039d400300300c49003205002a1a000080009a2028460001f8d04202b00548100018001109016040002e40008008007000040000018a205010000018ce0133bf579802e4ccbf1be47d1bc2d86c304432e601d1494d15d215121c53581e4c6d39c110994351a0d66ac71264abe9420c1501370d0a1a44c5d7bea90deb383ee31558b0e6549c107cd96b66524837f26a5b20510396ea99e61587ee269d0c8244ca21cc8a47101248347e0d89e1813aa172f00e315e028ab10e20b2d6c800b1847dd2ca959808d5288053a3142abe980e47b6bb545d05112f3e0085f4d4064e185c664a323e326352f262a0843b6204551e86693164881875045e282e88ca3ccc7b0c4e539c3dbd47a41640dcc391853c71c603021ccdfbd12c8edcbc3536e11e2655280d81aa8ac398a4a649000399c1ac6143e0c2810203c399a344732ad0d0fb4bb48b28a704efb958de3362603a5d4ba44e8397c0bba2010e44a1de9aac141ce38bda8d5d0191cdcea82c9da001f835749db5af112e8c252af2644362824d813c7997bc9512cc190ea4e4e8cb8000004410143c87a4833580033b1cd2699b389274c20668f80f2c29b71eb2567097b0007fcefc9ea074f813463865270001722cf7069003aca94f0338a950b9a5344020c71e531c502c946819c04125698504f546e1fb3c57db25008d25273de12748474244a4918e414099a34f8bcce80af31e4b131574340d52539c6eb4cfaa8558918b48062225c8b9af465a9e95e27c3ec2d27d29a5eaa7e0680514aae4c6a056c68420c11228052432c141e2250d727984a5ca871759dcbd96d898194d0d19a804a06cca71e16eb184a5007a26001a08b0394c60490eb4da29e20b61870cb8d3d1c814c0d363480146edf941c25cca1a59e86fb5325f0e536d1c46a4065cb1002aae2784f887030d6f8fe97c4cc6d47002b00f5b80eea58552e8ff1fcaf390ae78a69992c2924868e64e4b3639cb333ab512dad21d2aa5f23ec858732692f3a84ed434ab08b34e26ab2d2ace892694334a4923b0071eebe51780011a509f380b268359f22c295879c6bad95c248a158021af5013f3748b951a1fcc49b90a41c38b010dc8f18237726e0474c10888ad7138f3cae7c0026d9ea6541ad345b0290bba284469b9dd9d90ff4810d52d04920587ccc5ee9ae8b5494bc455b300050600da710234600024ccf0e27b288a5992ec259427d85c98105aab03e7b52881e1204d89da061bcb688e2aa9f26fdc63c56ceebd411b46d322ca250c54e4140024b89d4884cbd05130b5eb268a02bacae0482c6c461e84789f2028a23b84499018953258e98f else 0xa7441779347514659627169177237923317437979199a64919b5415326196a373378458824394948b9ab929293371b4b931121127273354712479a9b3b721731775687215a27351963a21311737b6676613317b9a23123796164471355557316b2992193453734793293271318569349b5366977956a6792a35b3142361923516775656477364426914a63527697316366597b561b31799555365730000000104d801a0ab0012e2011820804a1000020001268400000904880045020011e22301800046080808018113411f04210426924a20840ffb008200003e8110830000f50448702003b800100c840e9441818c00385008006000ddc05029a2034c008121040ce10860308031c022700040c10411c24002e8400091000b68880800002c9008800000af2002090c02a4222010040a40c400440027eb0048a2409511880591023020104000089004a02))

def seedRuleCodes12 (i : Nat) : Nat := 0x3c807600e701ca032c06380be017602e805100a101340258048808f011801f0029003b107420e401b042b0050003c004820504020304054040e020a03d407400d4019a030005f80b4013a027004a009001140204039807100d401a40268046088010e41130026044a0068208820f0018041808180ee01cc036406c00c90190031805680a90136026404a809300f201d40298441107c10cc0178428042e104c006800201f803d006f00da01a2033805e00b5016202b004f007e00f001dc03b004b086c08c011180211032106040b0001020203fc06b80d601a602480278442007800c04118023002e005820188010212027c03d806200c208d8419002b104c109841280250846106420a8811020403c40750056007220d8414842510300860406880001f0010c4108817102a033005e804c108010d0419840d000803a407082240040007c10480b3008e0888022003e007400d4507800a01c002e400e0802080001640250049008220d00190813000a100806e80060406014002400450c1e001c02d005400a208f810a800800bc0108119802d01e6006020080fd002608d000a843d007010b00400040006610b841700fb10120310047001b01de02140148c04083a033c0120104016e20f42020097006803d80110057101002d820a020b100801982048807040e01f420400db081820182030837080a03e410808050c02300000c8089040c10dc2138055041000f4413841e080e037c1070605005c3804416081d002820785008c0c08241028304802a1420204840a060b1806281400f060e1412184050580270c0c00743018c01006e00b06090c061018280c3038608141c301c6050a06140e30245040c081c0630144050c02

def seedHeaders12 (i : Nat) : Nat := 0x6b1302b6021004000f8d56c054c141f40001d128a40a4d803d00003734dc814137076e00066493a026d600e7c000c451ea04b94c1c4000178a21c0921483710002e2402811b3f06b20005847900223ca0d04000a44e5c041e0c1950001411a8007f26031200026130900f4b405f60004a456301da4e0b8c0008c8a8e039c981658000fb14a006ff982af0001a329400da4e052c0007a450001a0f809f8000e4899a0320401330001b9927405ff4024d00033223680b6bf046a0006024130157220878000bc47d60285e41038001710e6c04c3801ef0002b21a6808efb03ae00052231b01099a0700000a0456601ec040d480013089a0038ca8192000252108806a3502f40004641fe00c8a405880008483d80171b40a50000f9871802a3681310001a20a8004b0802320003060c900867c040000050c0ea00e60c07380007a00740194f00cd000076000002a08016200002a0000048ee02580008d0000007e8803e0000c9000000d1c80640001630000012fc0096000226000001aca00c800034c000001c0400c800031800000000000000000

def seedNodes12 (i : Nat) : Nat := (if i<2 then (if i<1 then 0x13fa6b8ac5f2c55af8a4a10cf24e8bdaaacf151319fe4c0ccf259637927313c8f1b0669efc745648fa2b243c56920e8a68ff55747b89ea35c4d119e6ae8c733c45fab1a1bd5650ce24684f155423aaf20bc5417966a2bc73515e2aae9f144f421e2560d713e8f2c50a3c5332733d571fc543e647d4dd90f342641d0d98ff53763dccdd8d7334633d9098c752e62fd92587744261bd8e986732a613cd0584754460bd0edbcb43c6f1d509bc50293f4c0689b302e260c0cc97b0292f4c1247cb01106cc0b419302e05ec0a43d30471bcb01915b3032159302d158302917d304717cb04717c704513cb04513c704613c50480fcb04e0fc70490fc5145097725908ef15005af2430587336057716204ef252046f06a042724207d523e0187236017f35f00ff35f00f7260006735f002f025edb0036e9b4023e9b003be5b0038b36805b66c00faada00e5564022ab6005726d01022da012c5b002c7b6804cf5700a9ed8022b5b001c636005ab6d00a96ce016adb00344b6804096700d50da00b21b00343b68052751004ce4e0199db0047336803c66c00f8ada017959c0362b6005836d00b46d800e014c01ca29008653c021925006e13403076d0099d9c02b66d009d99c03266300bd5b403356b00c15a402b56700cd59403056300c957403055b006cdb002326c00685b001a053406813d03204340f810501b03b404c0a501d027407409501b02140c43d40210f480bc3ce028fca031fc8028fc6028fc401bfc201f85e01a83e01b9ad01a93501b8a501a89d022895013bd4013bd201cbd002ebce027bca025bc8027bc6027bc402c7d40367ce03f7ca0397c80407c603f7c40327c20417c00373d404c3c80533c60343c4034be102bdf001127a80773c80419e2015cf0811a780046fd40277e801e3f38139f94084fc604e7e2013bf080dd31404489d0485ea0242f3810d7900a2bc403b5e10252f00068ae40744950423ea0191f400e8f900827c602a3e10221f0004c7a80603d003b9e70224f2806a79008b3c60449e200ccf000a9fa4060fc80497e200dbf080e9f8003e9060205e900baf400c579c066bca0295e3019af1005d7840607d20433e701d1f20118f880407c203e3e000f03b806426a0263d20181e801a0f380b47940463c8034fe3016ff1009ff800339ad02dcd2816e6540bf31a06798502ecbe809e5d406afa408b3d20349e801e36c8139fa4066fd002d7e7014af480ed7a006ebce0365e501d16c8140fa40667d00313e70181f280ecf900761b204e1e90198f400ac79c0703ca03ade40186f1804efa40497d0039be701c5f2806af900717c6038be201ccf400da79c06b3ca0359e301acf100e678405afd40477e101e20780f135a08abd403c5e801daf1811978407c40e03b2c282315f40d4fa808e7c60483e201c8f180e87880743c2 else 0x188532d85d54cbd4447bd204dbd002cbce049bca05abc605bbc402bbc21575a544b56535055d3307d20317d00357ce03f7ca0407c40147c23440ce44d1ad33d1a546116524595d45a94d4508a5351bd434fbd2054bd005ebce062bca04fbc605ebc403bbc223355d24553d13b53531f49531b44500e7ce00f7c60187c458d1b643e0f65541ad55319565e16564d15d56514d16614536b0a514709d5583d45783d205e3d0057f9c0d9f2817fe402e7c605df880bdf0818be013d1b635333c68e3b84bcd91ac9ad55534a4b6654cf8c6ab21652562ba894534520a292413543c14a274275524169bf3d412f7a409cf4014de702ebca02f7900aef18161e2016bc05659ccaaf2b8d0a372af5ad149b4ac956555aab2932d5d662a9aacd4d44fa96b2fca553992aa712150aa12a2dfd454efa409bf40143e7028fca056f8c0b7f100afe121a9b646304c6b66b4cf8d293599532131a6c0615d48b291615d644a9a2a75159729ea98ca513a93aa7f255533ea09d7d2053fa0051f38183e500ffc805ff8c05ff1015be01a90e623e15c8821991b00f1aa1ad24234a2ac654524c28b31651502ba6c8534db49e8a292d66c14a69a2550fc4299a815469bd4446bd204dbd0042bce05abca05abc6048bc402bbc25484e64494ae42545e54c45654141e44340e34e5ad54a5a534b59554658543f57d54356533855d52c54d44053d43553551f4a552f4950187d00187ce0187ca0187c60187c412b0e612e9ad13798513497d13396512793d12f93512189501dbd0025bc6025bc412e4e61325ad1395a514559514557d13c56503955d13654d1395351304a50137d001b7ce01b7ca01b7c402f0e60301ad13a19513518503716503714d13113d0310a512089501cbd001cbca01cbc602a4e602c4061495ad24957d05357524a56d03b56504c53503c52d02c4850687d20267d00357c40287c20327c00360e623400624f1ad05218d34d18514817514816d04f16505d14505b13d14012d04309d26e095131a428ae5f480aefa00637c8038be3016df080c6f802630e613e8031a0c6b491e32a4771751378b699ec594cfa29a47512d346852919c2149827a404b3d00339e5013cf080c67806b8bd20485e81bb1f48118fa00927ce0433e52b18f4811c7a00883ca04abc8044bc634e5a747a59747158f46d58738e57f17a5775304d75304cf6414c74294bf64c4b745947764746f54446753f45f53d44f44044742743f33942f44242764341734259323058303657b37e7d54527cb3487c733e7c544d1af5431a763d8cbaa0c61d4e22fec8511f739887a23441d4e61fec730f743186ba9b433d4d618ea690bf64583ba9ac1be0d20cea5904f442823a1cc0bd4d67966793c744a9e2894b64c4adb0606cd7b2607e5b313f1d535f8a05c9835685e399d95ed13cf8a29010f) else (if i<3 then 0x7453c0d89fd4911fa8821faee3fe98c7b90d0ef3408d7c898c72278b7b8886fa7486712385fa7582f428827625817336993834983137bd5153bcbb75bc774251f42150f92a4ff72a4f73214d7b474c76214bf63446f647467b2c42f03d7cb8317c73347c511d0ff2230f742d02f12b3c73323c511fd1f121d0f222cf7129cd722bcbf13cc67122fcb12afc512a90f12b8ff12f86f02986b223bcb122bc702c56703453702e52f1374f702f4ef13c4e712e41723640f13740703f7d312b7c502916703214704113f02712f36e1072430ff0280ef13214e7255144f127143f02e1427135141f133140703a153b03817d313c17c703a1167030114f124112f555110f12510ef32b10e722a105f3521057233100702d114b03d13d324c13cb0400bd303e07d326407cb03f03d336f03cb04903c702ea7ce027a7ca02da7c8027a7c6027a7c4033de0018df280bef9005b7c6031be201c5f000ca79c06f3ca0279e40164f180be78806f3c002c7e700f3f28079f8c03cfc403d5e7019af280bd79006cbc60365e201b2f000d8f9c0647ca02d3e40191f180f0f880787c00151e700a8f2805478c02a3c4336db6450fd4447fd2032fce03bfca059fc8061fc6063fc404efc2058fc0348bd2060bce06abca06bbc404cbc24505b614054513c49d4597d43437d20587ce0627ca03b7c803b7c60637c404e7c20587c02791b632c1b233315d14b1454480fd13b89d467bd4443bd204ebce057bca056bc8059bc6058bc404bbc2055bc03484f502b7ce02d7ca02f7c802d7c602e7c40157c034714d34913d44b13515f12d44310d3290ed43e0a554d09553b0854663d43303d20433ce03d3ca03d3c603d3c40299e11243594d41fa4058fd00327e401cbf180e9f8805cfc20327e0121259452129a26e8a53365e901a2f4010d79405cbc60425e200c2f0851c93aac87d20603e50379f20188f840cc7c05370b2a1f053450028aaa213d438052896027551012aaa03d202bfd003afca031fc8038fc602dfc2031fc044291e3629ad15396524694d14794514f93d2468a513a89d552895257bd4139bd2056bd0060bca038bc806fbc6030bc4066bc02595354424b575549543e4853377d20507c60427c40297c25b51b6472b3c89f43912a7f1265b255db5aaa56959deb28b5d4514493a8b5f50de7e902efd0055f9c0bbf28183e402f7c6062f880a7f0815fe01c31b64381ec67a3590f85f1a81a256435a8c6695988b28b014596427a2762751644aa2606d557fa88d3f48183e802efce05cf940cbf201b7e302e7c4060f840c9f00958db12899e4401dc2646c8990d69351a53502ca47e5744a8a292713d12a13a88a2549183293ebd41387a40a0f40161e702bbca01f7900b8f18159e2012bc04578e65539ad13c9a546896567093d47093515092d53b8a586389554 else (if i<4 then 0xc1bccba09e2733cb1399e388db35c89d98e238cbf221637990b19c47985e05cfcb02d7e3817bf150d931e48c9872314bf81825dc07d2deafebc76765e2c31135d5f8f96b167c55510d3aaa065c8d02fe454177a200b7a33035cc8419e7163cb34bfc56309a777099775998f53098742d977a4e96f6728d78828cf79886f86c84f13b9b323d993440983456bd548cbcb449bc75334d773a4cf7604c72274bf55746f35446763844f32944743842f44c7cb4407c703b7c51361a70261970301871308bf81945dc4a21aed270c7b5685f99c42dd8ba0dea7706702882fdb5c0bd18204eea10170439e5b9b4f1e16a78a050d670357e9a2a3f1c0852ce86294f95348782016dc9c4b2e68e56f5432a7918951d5f4a1e2625b32433e9921059c8c429e25214713f93f64a90f7749076678ff78086f54a84f137bd3548bc703d5af03959713058f33c58713f56f34650f48e5073984ff7a746f56146755d44f5404475807c713917f14217713613f1391379950f721a0ef13705fc9302f6320276220177713c703fb6e4856bc902d3a1b58f233afe26d5dd4d6b7815567035abe07f53c8aea38ab53f250a1eabf3fdd866789e5b3692af64adf540d3e9c437c503e36e4786bc878d391e98f23c30e47a5dc910b781b96702f2be07e53ccaca3a2c93f361a6e48943e6b683b49cff6869eee8133c8f637bc044f22cb66c7d60c87fea81d7d367ff8e03a6bc0ccd389398f23630e4805fc0bcb781e90f36320e6fa3fd5d47bb960cf7b218e6622fc9143791e86763709e49011d6481791818313397b03cbd556bbc7236bc50355af13658713757f02557704956703755f04153f04953762a51f02a50fa844ff97f4f761a4ef76f4c79454bf6384b743146f43146702745fe8b42f85d4279674178747c756a7c501e16723415f32f14fa7510f83fcd7755fcb353fc503196744b95f44194f03d93f4309376b391f7798d7772bcb2544ff5284f72454c741f4bf95146733542f22a7c53421b72331af4371a768519743018f23417745916f24916724415f24014f12814724113f2491374ae11f79ca1e4793fcd067bb34cd743c99eb371bd68e338975b3128b2627df544ebe9abafcb02635e48669c91ccb81518f0222fe4725bd2708fa4590f23b20e4683fd4d07bb300d734919e4862fdd603ba4306f7a50ce47411c8f01789f99313b97b032bd556dbcb043bc50385af0315a703c59703857f03757703e56702f55f03a54f03e53789251f98450fa204ffc794f792c4ef2394d765e4c7b4e4bf6314b796146f88646733145fd6742fa37427b5e4171547cb6697c50321af22d197233b1e04f61d4a6b7aa251f588a1eb0d41d4de7fa194f75319aec5333d98263ebb4778978deac919d50e279a0c2f46ff96683f1c8dcd791d1a724132e26a61c494bb81f1670332be else 0x115f2c10af8e2717c50329e38183f1c0c5f8a24c8d70305e5818af144f89ae0584cf13a3e589d9f144cc1ae4700cf4428639a)))

def seedRules12 (i : Nat) : Nat := (if i<5 then (if i<2 then (if i<1 then 0x1a8508da1cd5d1d544b93c86a897287287caed51340143544f943943544cd439433b439ab201d79ae40686b3b439aa23cd6a9d39ad4068a9aced005ad5950d68a9aced15757592938f55c4a72a1cab8bd7e40686aa72a3cab894e544d57131c4f46886f71f474113a1e4237c707044d0e6885ce0c4c103421633b738382268f344216e7c7044d136885cf8e0e843a5e73e3831b044d0c5089f77e8b0d85de3db9c1ee84003fa5bb19d9edce0f742079a7e96e7be3dd069fa96e7c7061685bd46b9edcf8e0f77f4b7ddec44f198e279dc3a2d78f707ba00387f58859ef8f741361d3f78e0e770e9509e7be383dd061fd6342d7a77e5ce0f6a2151ef741d1db1efd80d9ee0f741b50e3eff607b7383dd0510fd9d859edcf741b5133eff60e707b510a90fc3f469acc6f51a6b31bc47198e279da36d16bc7bddd3fb00e3da75fa7b7383dd051a7fac42cf6e7bba7f6a01369fae707a7e776a34a88e7b7383dd90147eb1b34435b767457d2c02b5eb38cc713ced9a2d79cf8f7676cd2a3db9ee800d9fac6767b73dd079669fae7c73b669559cf6e7c7ba0b3f58d0b3573e383a22d16b3c7d6504ed0f4437c707660e5439a45901a1acedce0ecc1ca8f34882dcf8ecc1ca89b48b2a1894373b874bcb5c4790387f58a5dce644eea7361d3f54f0e9509f7113a361fd63e7f454476a16bde76a2157476c7a1fa1bdf7b39443f437bec37d1fa45f7b4d443f437ed442a9dced1b69796bb8c85338f6da75fb7115bf9a34ff58ddc644eea746d369faa746da5447b889d1a4a3f58b9fd1a547b4896a166b46912d67a427413da45650c1a1cd2253420686a46ca183479a45650c1a26d221a0a1a18c547958a15f2f2163650aeebe5e4e291775f2a276522eebf995057945c57cbc9e2a8abcced1a542795f74c360168547302c3344e9671ca06faa7065473d1b13ca06fba51c2d051cc4a689a38d389991e120d0f48c0f2da86ac24fb13376a21c48eb23b601e855a4465b50e021564606fb4032c3e9cec4c8c0df74a245a0a3b094d13449a71eb2384c9a1e025909728934030911931a01a74723cafaa7c81478a16264795f74a145a0a3b064d13429a713323848348a9666425ca14d00c10068064a31a3b1909f2853405153560c4a8d2ab26759293b43d11895953950e691640686ac25654e5479a44c19654e544da44c189199a268871308eb23807acc0c488ca8701660c244654780b3060c232a2605983062464ae54410c461223f01b6231c6929b4fbf805bc4608cad03f41b6d8308138353fc0684b5ec1844183f34a6c18441a98983f34230441a9e507e68460c837d5307e6b57118300f77f01ad5c4612cbbaa7f80d08c1807baa7f80d6ae230625f80d59f1184b754f2fe076fb423066ea981fe076fb4230911954ff01a1183080353fc068460c49f54ff01a else 0x55e85adfe06f1edcdcddadcbfc167e8133c5ff738fc3dd69165f5baffc7e41cdd5efa4597d629cdc839a6ff7bc0d11315bf7b9b907361d1a44d7eb19f4794e6e71f87b48b0d6b3c7a723d97a44709f238f0195dacef4f3ec7c8e3d06cf4062b3a78f23a0e911e55ca1b9de9d20e6ca0d9380c417a78fce80f6723a0e87a213e54016b37e162771b7f2037bcf350b9db9b9674fa72027b48b0ca83c7e41cd67293d2238a82e6e41cd951670e203660b9b9c7e159698711ec313c6b9cfc214daf8d3f4f79ff9374ebfcf0a8f06fdbf6073af99f7b43f4379d863383bda1fa1bcf5c41c7a57fd2386d6471ae738c853db4fd3c67b9e1eeb4f3c4b793757be9e78967266df7bc0d113159c9a8c3d2b789633dcf0f698712d674a13dbbd22390a99c780caed48d90284e3d07ad22b284e83a447a5ffd3329a1037bce6a474cd6508182769179d59427413da45a54d0d005afdfb8a686f7813cd48e9a2e59027b48b0e0f93594347a44741a2e4d459c3880d98345cf0ad30e23c573b95fdcdfd9ee1ccc448801e813310c21aea03c573bcd2bfb12899e2531017c820769e1ccc44880699c662304034cf15cef34afec4a294c4052dc8e4077ee2e1ccc430868115c3311820114095cee57f7344a26784052da8e407094587080a5b5280015225133c4a672544729128b0e253505440548945870cf1c9511e12899e25310146040e128b0e25310146a010f04a2c3867840518103c2606d30fbf8177edb6db0909f1bea981afcb4b7c1b0610a746260fcd7efa9b040907941f9aa311f58301f9ad5ed7d4c182706faa60fcd2d1bf55ed788411c1e55307e6b0fb5e23106fb954ff01afdf1bf75ecf118301f9ad5c4f3612cbf80d59f100d833f01ad5f37fef612dd5313cbf80d76fd1f67d8314f744c0ff340edf03d9f10c23dd0353fc06bfffd3d9f118caa607bad7e03ffecbf9b7fca45dd7a10c2f4ed8f42bfe532ec7a5e8f3fbca45c578decd10de63d887cd2e522e2bbaf421d34c51bd1a54c78a8f354161b0bbd3bddedbfb2c37a05decb0f98be50af10de8b05c6fa058dd51be5872ffcb1d1715ecfc3e5972b2f207285775f0c5a2d67e1d12feb31ecfcb0c5e51775e8d35a17a8d3bd059178de0b597a7791487a2eebd114169dc6f43ef3baa8a88b1f2da88a157f45e376df9ddac5b4bd9792a2fa2eebb6fed445a2d67d1b6897f598f67e5444dbf945c57b22d168ddb7cbce5fac7b7bc9ead7bcd0b0da77a8d3586bd156bde5d7adde3dd35ab6b1ee9de15faded22ac675bda455b0f83213d48c545eb77a2e9acc56c04713174d8ad83213174d8adde8ba6b01eb60c84c5d362b60c84c5d362b60b3e5174d86d83213174f2f27a531f2a34cacbcc5290b93aa43401a86b3c481cade76dfe561d1206873e768735393aa03439f571f401aa87286b2989ab439) else (if i<3 then 0xf17a87649c74c21cff4e97b160f1da1f8c401772eb478a44746c84e925c1a758b7a3a21947a748bd6f6ce61167e79030ec62eeed795f54fa7863f88dfb28ff489e57d009f85ac7afd8444df54fa40d7c0f0b58fb04f2c9e9d38c343b30c774b5b1e16b9f65ef86d6474a3948d256b780397d947a74e30d0ec1b489e57db393d30c1c51ec308696e38d9044308070c6c8226521a23c02c10c6af708764110c238031b1613374fb38ed0ff2b95ec3d887b69601344def4e291c6ade9c80e013174d2b0574e5878ba767b3608c814715b6475bd2264ff1b361371f74d6c0b6cd88ccf4e58743b36a2415e9708eb6b6cd8cf8e9c3d887b5eecc6d22646fb5b5a0c3d9b3042d671da08846475059b08c5eb10f68223044806366913932a806fba49ad051f0cd32449421f1973c70def0f489f046a01bed6dae802dc3ed358e125087c668e3b09731c24a10f8cf40d84b925087c65ca01b6913e08e4cafb67a61816d1ec9ac7064843e32e78d825c64843e32e3905825cc7064843ef2063609731c10f8cf8e41639e0573a7e7ba03f43d63bd6fd7637affc982aee9fa5380fd0e9f96bbf2e79305e9dff1debb468477e9f96bb1ae4c15740d14686f63bf4ff2d6fd7687f4635cf02aee9e780fd0e9fa7f96b7ee79363fd0e67477a1fd466a7cf1c84ce66780cae84cee0d13d1e03550a9f384d57284f0d5bfb9e2ef53a78cf561f982f43561d029575099e61ab1c26a814a854ff9d0d72a8972790f58df26e97675299ea584d157d79be840b9e0d135574f21bdfae04cf535337028d3c050ded9f8d7269da00ded435cf3a9d737ab7fa96b3f4ff5d0b1e70d590d096f408d733a97d7bd3c3576b39e4c16cfe97477a543ebe581f8dabe4c157528d9bec7a13aab9305e86a9fbd4206ab9e051ae6f509ec7f73c9ba9d13fab2daabffc9deb2f338f35a3e4d3a749c4fdab9e4dd4e89fe596d75773c8b23d96d577b9e1e0755797eaf26ea4e0abcbf53937af9bf8e81a2a6ae4d45e82adafea5dee78781577b519e47b2eae23b2f5e71e032bb50391ca4f75155e427e729ab88f61fbd37afc808e9cd6f4d9015274557e7591ca4f45577bd7e54016bdffb9ebf21d0279a99d17009eab8af54f9365275711ca68b935166f6202529a2e790ffbdab88f7ae37ef1c37b6968bc046fafdb4ae6f1e1a946c1e3f20e61237f463d09c360b9b907309add14fed68408d82e6e71f82746b427961b0bbc04d7c36b35cf6e707bb5b081fa5b81ede9dcad3ffde3d867be3f37786b069fa7baff07375d7f6cbf0a84e7bdd01eda1fa775ff27b839b740fbda1fa7619edcdcdd079da1fa3b3cb7cce7bdd01c7a57fd22c7d0f039172b0fff78f1edcdcddd3f201afe9fa7bf7b9b9bb860d2c6bfa8cf3bc4e7bdd01c062b1fd95d571b9d9ef4eed9a00e03fa273db9d9ba09dec7f40f1f else (if i<4 then 0xd8ea936914640cbb2dbe08d403ca815f2e17b28cb1c24a10fbf05c70e2644b98e125087dc7d020644b925087df82e3720012e63849421f7e08663040c89731c01b690fbf05c6085dc2814ec0a23cb109fd2a8395edb9132231798c0820f7a3b2bc61d63a98c60d2f6c1dd5647749991ca7483a5a91d318ed71b4e4e6960ee2ebeb95845a95edb8eb1d74e4301b22bd1db9fe08e4ca135e9c62fbcd7974a92e0ee7e4cb3ad676917d47bb9fe08c2a3f0317b1a88b9fe08c253ceb581d22faa42b6b3b483d47bf1204d70763511e0ac26b03a41eab2a58ea6318d9697b0743f1204d717d4d58e0c914ff04d499dd5f508c18d2983eaf12eea649f826a4a9329715dc481353225cc7197f04d4953abc8c504460c6a2d9c4b98e0c93f04a46d5ec62cb5df1241be1b63ef47c58308c80fbd1c58b10c212c6381bb875e5aed8e32c190336e563eedb051e5aeccb1d4c63136428f898c6709c814716116bb318ed74bc84d9460875e5aed8ea27ccac051c32d7617c11c995d71a26ca387113932bef981d78b5b04ba30bd2272657d75c0758b60bb5dd185e913e08df7c75c1665ad86ae17c48879590cb2ad7a589f464211fee0d3b62d86eed791e8f040d3be58b61abf124ef1b21bb2b24343eaf0dd956bcce963a98c706272b01970b363fe08e4cb9590cb28cb1c19210fbf05070e225cc7064843e04229912eea6490643efc125c00644b98e32b190fbf05070009731c19210f860422ddc4814ec0a73c9baf5e35f7cba8a73cddf3c8f759bbee576f170eb2a8f9375e7bb27cddf729c9badd6de596fb95abb9e653a7b2df72b1ffab1b6daf170cba8a57ff5636d8baca1c72bb7e3d8db4e8a2e1d6575f1b6d78b8b2cb815abf5638b23d0cb288f28199fcbe30bc511e503ea017955650388e8545118199f8bccb815511e58b2cf42a2b74e854565fbbe510a8a8a1559ea2859722859f228599a2859d3d6f25611b7b5bc9ec1e571edba7cdecf4a636dc9cfe4f4af2693fc70def3378b61bde50fc996c37bcf97b0ade5f7856b2a7e3ef0d95399f786ce1a5a162b61b869685b4c8e54de56bf1cad335f8f6db5fb74f3fe995c7f56db5f0cf7f4ca726ed8d4714b7b6726e96197ffbdb76f6e63865af6dc7d0dc3cb0d7b6eded9cb0db5ed96b2a7d6d654dcdaca9cdb594b86b792ac1a970d6f25451bd58f2ed73f98a571fd58f0fcc529cf12f6f8d97bcf6f6fc716b2f7963ee78b597bcf6f6dcbd62de7cbd62de5f762d65c7dd967c7dd9664d6bdc3c76bd277b850f648873f93e9bdd33d238da72135bd3834cf6f70f49b721b4d1a1e99ede96c448801eb16393eee06fb27a5af8e1d84eb7a5f64f8f816e1d84c0f4c9e1a1e1db4d1e1e143d9ad68da44c0df6b727860c3e1d92216e387682201b6900c3b0895ec287b41112224031c2c7adc719bf65ec9dea3 else 0xdf70f8b51702ee17bd18de9c2272657d5a8b80f2ee17b8ddd228179a1def023e551204f18f60b77723eef454202bdc6f08fad865f748a0417bdc8fc0aedd0e2e1d6518c6936919590424f9bc995403cbb70c39fca3264892843efc139c388862440219b89719224a10f86040f4c897656349421f7e09ce003225ce6648da43efc125c01748a053b02bd71bab691d640d3abe38efae4607a44d037e1c7613899181bef4082d0bf6d24607951b3561223f2d0e3b411184888740da08847d5223f401b41118036d23f401b5ed9afafcff9191c06b148bed8eac63499a26ce247d7188381955c522342f82343c4e24cf6b38c3d7137d43c13bfb2d8258589c4df50f01d3bfb58b609627d123cd93bfb1cb61ebb04691de5241633f9167f13f04726487d97b6a65376389087c12d57fc60660a6e25cc71210f90f045819829b897759087c125d5f820644b98e087c149021e44cc14dc4b98e2421f21e08b0bc9bddc48169f6a4607d6c17d4d7823500eaff419ea224794cf99e77d4d78528a88e4788b5eaac8d581b6d5bdfc7fe173b1323914f63e829ffa41fad25c8b0452fb51a71bda5c758ea36913b59a71bd1dd2d74bd390c26c06dd6342e77c11e9f489dacd38b5e9c4df70c04badd1ad2c2e77a44df6cdb0c1a75a768d7a713e08c2051fad25c4b1c39da59113c6a246459b15e1ad3b46b25f8c3fdb9f62d6b223ac751b4e4264b34012f7a1634ec4f8237dade9f0f65b6028ed6c7122843efc135256329bf8c112e63821f3524cc5f0458225dd645087df826a4a5994de08225cc7043efc1794dec41a7044b98e087df8233a7501a7044b98e087cd4932c7a704512e638914fc13526f149bd0e089731c48a10fbf04326f031c7f87ff37e4606a74be2a341bfdbfa9af6dd2ba3417fa5ff7f511612fd3b7b17b0eea2bca37a1b76a331d526dbd8b1d051b0eea1dd3d5b46e94e5b71e21dc5a91d49b721b49db45d63beadb6be517a63ad78ff0fe08d4038df6a34e2d779af0f23038df4eb60be2eae3fc3d4038b63b46bab852373de89dd1fd4d78238df0f8b3da4efa94dd2be3f3b46bab8514e7bd0d646a8b11869b7bc7af621dd9fe1ea4758ea936c5e9c86a361dc57bc28135c5d4d58e38d2514ff04d498aa12e638e34946a4a933d4425c47d78d253f04d4952662bb853742d36b87c112e638494fc119d3884b98e1b7f04d495265b78aee14dd0989596bb6387125048da1b6fbd1f193c6738c8c8f36c0fbf546224436c6381bb875e5aed8ebc693689a2147c6f7d5b4893aa3cac838f05da4db9093a4a3043af2d77c118aea018d125be8a387135c4c8c57037d91685f4702bfaef489a806fa2b828cb79cb60bba3d227c11c8fa2b80f65ad870a045bd0f2cb8148ff6d89f45420e18b7ad86ee891248e350b5b7c28116fe3bb815921c5eee052ee8))) else (if i<8 then (if i<6 then 0xd051ec60c21a5b8d83704430868f41641118308031b2088c6521a220b0460c6af21d904460c200c6c70c512f81f169c7aafff1877a98c6da3b005a71ea932a8bbf842d22fe267bd26553d77ec5de87b5287baef810b0c5ec6a514e4577f084062f33d46be4dd53ecdde87b5287be102141d8d527e454dd2bc2042d20f53bfd498c7658f874c8cf0791443e10a2fa9a9af638324494536a4c41546bc4b8c91251a92a4c8d9ec4abeee24537426a6bccaaf12e638ca928d495244288460c682d4c1cd7aaf12e63832449452304c628b13932e17d051ad8b0b7f81f27f1321e50e3944793c6a3c11678111f5b0e240bf1b0223f02b2cde586c8146b89731c656349421f050009731c19210f8108b771228140a7bfc3fa7fddfedfd5f1b9dc806faa713c3a033ff5beff9ffeab91a2456f5ffda578765b0fecb915b44bcf344edc66d975b44a6e1135bf1eb1b2b07f3bf7df051d9765c774e89368d86689db8cd8eb1f4d390c7848363d4b4fe35571b9da807269c2274e237fad57f226a01bef5fc20dffd8ad9da813affdb9e67eb48aae3ba24dba72184e106dd6ab8d8d3b13500df6b7a56e1d8147ebe2449421f7e09a9265975b8c112ee349421f3524c80f5578225c92843e6a4999007b044b925087df827dff20d363044b925087df8255ccf5069c112ee1b487df826a499912c025c929f826a4f1215790e089724a10fbf043712018e1f89f83f13e3299f7d5b66806fff8ffbe625cdc2274e3d6218e73d009d22a510c7380f44e917acd7739807c8f402748a952c77498c76b8dc4d13669c66c758e631b9c6d391e804e91528d0bd32650b8039989b34e3d61627137d08007c207f76315a442f489be84a70381061d2c5a139f840feec5ac48e446a394808af081b345a474118d2db44d8003d63a6318da72e04d9a038e942c613932be8407d385b6028fd65bf0648a10f9a92b190bcfe3044b8c9087cd4903998a03d8225c64843e6a481cca803d2de089770648a10fbc85e781896e6608977195421f3524223e782089719210f9a9267a81c114b712ee0c9146a4de08af3d0cb78225dc1922843e182f3c0c71ff940e2a26ff4a32ffea17fd195d1a7dff6f0ff549cc4a2f44b8477546e5767915f6b271874c6349b62c1dba611dd457c758e6318da4f6996ee23d1df6f265500f0e897899ef15fdbc997463ea4b5008ef0d4d7b722a01a9eb784099ea5008ef0b1aa4fc8a857a610397d4a4431a4bbc7877175c5f6ea474c6349b46d390ef4c3d7119e8e453b70c5d4d5ccc912514ff04d499da8af89719224a35254993d8bb78225c648928d49327b15d2281353225ce795253f04d495246212e3246dfc135254994b8ae9140989464892810d1297377dd77c4c6349b7afc4f6e182ef898479e47810b39b8d1b45e4caa018425291f5dc38d18de913500 else (if i<7 then 0x854f1228121623299276c7354f54e1b0085558a9c3601c85554c93b85cd58aa78914abbbd88ca649d3ce6a9ea91a45275cd53d53228155f2a78528039aaa78927687355489f2281556232938f6dd558299355f6a64d57da99355f6a64733a71eea4d553228e68049aaa74f8502abe548dc293b455d353c48e67689355491f8502aac46531493a739ab154c5229401cd55317120557ca98b8528039aaa468b89275cd58aa6cf1712055588ca62ab57155ab8aad5c556af281819ffa55e7d2631a4dbda309d24fe71b1a450201bffa4dd504c4885ddaf3c1312217768f60f8264892843efc17943ec5099839525087df826a4a1f22850fc13246d21f7e09a92652d099224a7e09a92521f05504c9125087df8243e3314227e14d7fe77f6a3cd4660a6ec71224a10fab7f4860660a6e47d6449421f7e0ab7a1819829bb1c4806da43efc156f430298e24494fc156f042a2303ad99f011fd5faab7c32303ebf431aab775fe7f87411aab7bde963aa4da309add17b5b8d3be14a0187a5eea82c7092843e6a481f33d218247d525087df826a481f32860b0911f977635bc161223f2efa64782c7006da43efc135240f9942c70929f826a49407c154163849421f7e080f8cc50d7ff27c9fe9ff91e57da01a11f89fa82c02ff47a5e8f932e1e952599f47f9e08c0d986c6aa5c8b0436e80b2b7bd33f891cfb30d8d4bbe8f1d63a98c6309d366886f4cf0b1b892c0698754163832421f3524cc54307a99210fbf04d493296860b1c1924190fbf05e58a133058e087df826a4d2e450d1f058e0c9087cd4933150b1c19241fe09a92502a82c706490643efc10cc50aef8b60c6807af477530624d740fdea625f9a07eb0625fbcb1fd612fcd1107eb0636fe681fac4afd932a807e787e84e85437823500e8f10e5c2a1bc11c995f509ecb854cfff047265500c6d087970586312206f9fb410dd8d8b86eea2b6ff2292787e742abdedff8fe14a3cbde157122810d43ddc165de9eac6db4ffded2a1a28e036f6956cb814358e0c9125087dd41099224a10fa8720858e125087d479042c7064843ea26821e245028545657d53e9a7fb0cfc70b1c4f2bee99762d051f098910d2dc70c110c488031c3044ca910d110610b822184351418443126af21e182218910063848df74d9b40cfc7f71389be82cd8f60b7f7a2459b1ec16fee27970d97bfddab062442d0e3fb8dc110c4883d803f711848807ee442e088c18445803f7bdfbb533f194c2e7844bad233b137dadf9f63e1b36004b68f044b925087cd491b0be6407a17d57c112e63849421f79d3004c55789731c24a35242fde2824355f044b98e125087c17c6080c74e5c224cf4e366913cafa0d0f56d827137d06102c56d847489bea9c18745beb6cd3448f3e87ab6cc2058ad73ec234729057840e8b6c6389e57d8bd30a else 0x745c9ba9286db290fe7751e1c0ba8bf6dcec0a184ba8a4a4dc6db800ea312ea2c70e10f82d98dc6db040f14e78bb07a90e55ea3e41cf7bd45cf1ac1d0e55eb3a1ef6263abc1d0fd653065aed41ea5de87324f3f05d01a92ba541f1bfeafedb3d487f2531c39e7e0ba05efd1f1dd5f6763559c8b1f9a2aabd73ec34545aaf4431abdbb3a0f78765783b523784a2c38d2ebef288f5307ed43a58edd464f02eaf45fe1fbded50fabc4ba8f5cbf82e9a92ba454a5d9cabddb10ef784a2678d2e81ca53145b3a1c76ee0213f780b5237b4f130d59e2de89751324f1a92ba6757d9caa388e6decec39fba280de99e41d1270e21710cea4e003bf85ccf3a8393ca88002fe41e5449c001784e95abc9f1f279441b4a8d272799422951a4e4f32a20da5469363ca86d8151a4d2fa5f858cc70e1927843e0be7d76647c38c583e3192790643e0bf82ebcfb60f4bb3871198e1c21f05fc175e79be0c8f670e3478cc70e1927843e0b6708bc6052d8b0b12e3243a2c01bb0b184ba8b1c3843e0be6fbf77ecc8f042285c20f67bb184ba8f5cac70643e0bf82ebcfb52ece001dccc4ba89927843e0bd6cc0e08459d81547663b99897516387087c158ecf4e0845a2e148708b438b0b3d9886369c086af273adbe40efec7e218dbf810d5e4c612ea2649e41b6c0e051897516387087c17f05d5af1a0e00f31773c9bae2ea1559aa285993b9375142ab2e79d450aacde845672ef1efc5e8b9345d42cde8acc22e8cdd5eed8a1642fe3dea3e75db142cdea2e75142cd1f2681d149d9cbe8b9375143cb345cf2281eb36786cad7bf1f7856b3a68a9bef0d9994fcc366f747c53e1f67aced656e7f9b6b2b4da5d96b387a54ceb3b25d2a737b1eb3c7f4a9f5376764aa7b59392b8a7b1eb387e3eecb2b76a5b1f6b59c363fa5f766c4ae69b00d9c37dd8e594ae5806ce1f9edc7095edf9a1ed37095ede143da6e1fb7274b86eb6d86f437bd27db0dea53b856918f5fd1b6f477b6c37a25103c2c64051e1bcc50f0f2727c3b15cef34a96fb657c35ec7b0fb7c6c2a87e3bc319b615edf99173c2ecdb0af6ec439b47edb5f330bff080b677beb0ef1c58d9274b910dda5ace2f437bd60eef4c598f1b28ef7b3826621137c7588380365e1db2cd8f22dbdeb2cef4889472b105946649de4363649c8f057a6c0387c3b0ae779a57f7db22561bf0d7601c34b27fcdce366c57b7cdc9b66c56c43c3ed37efe66405edb365d6b38ed606fb2db34b66b71b2f7db46f59b59f6894480b67e6472310597ac910d8e1eccaf4b987b2f7db615cee54b7b4d12890174f932d82c7362b22857244e12dcd2bc2856109d8b7344ba8a4a4c43e0ba7992d80ed8af1215c913616e689751324f087c15a92ba64b6072c638714cac376bb00e1c871ee9ca15322943942a78914090f953c2943942a7892872)) else (if i<9 then 0xb0e3540a93e2e662514a6202dae36fbc6043371b3310c222c103d9bdae36870cdca5d8d30581eeee946f02c0f7774a7a86525cbd2c63312ea243e0bf82e9cfb7771df8df0021eea2a4c175da97eee870290e9775193c0baed8bfdde7605097514949887c17f05d0ce7bbc01e09751324f087c16cc673dde003dc762bebcd9c7a1d15da6f6cdd15f3b4d67f8e99a531017f75dbe60fad0e3b0ec13311220103b6822514a6202cdf803cec759c1128b0e101600f27b61bc0527c95bdcd9ae4bc93b69b17c95edeb20524979be4af0e36c9a26f922550e4c5f3359fc7687a5fc5ccd3763872421f055bfe560b1deb25f8c228ec2ccc1334dc4ba421f21e3b141038cc14dc4ba8c843e0be6afc97040e638494fc106e4ffd6f51173ce876aab9df78f7d1726e88d5de1dab8b0bf8f78768f9db07fd55dea2e7507e46ae8b9e1eabb34371cced0ba566f6c8b1f9aa5f8de859988c11d0097ede5d2c896f4e66e515be877c84b9003f88c10ba0224b914363f34dbdec9f2e3b96d873213469d8812f9b97b1b439e257b737e66b9ce7a9a57b7dbe63394399a57b6bb34afefb7e6338db415d39bdbf3190dc637316695eda5f2dc6fc5ccd8e1c21f056a4aeac16f7f17c8f5c5e29644cc87c17f05d352575683e5b83d37c6fede2b69d8fc47e3a77a456618daa5f8c5bd22166625c43e6a4e5998bf140741cbf88c100224baaf04cc4ba890f82fe0bae5d2cb7a7ebdada0d30391826625d47a90f82b52574772de9fb58dce08bda7bffbc3e1c9b8d64be1b0e31b695b592f87da573bcd2bfbed8975121f056a4aec9992da6f8de038a894feab3e5cabdbb91c7bf567cb94e6edec8af3decf76f35b3b3fbcdba1ef64ca7322be26366874bd2f9497f8bb1c39c69293352577ac8c5d54874bcae34949bf05d3525760ff6c1e462a9b7eee9d4d48d9ffef63f45a755e94458fcd4555ea1c889771a4a3526f19ddc474efdbfbb853765722d6af91bd771bb24f45f6a5f751526dd0bac3e45ae1e25d452526fc175cbaaea4cf52af69c49785fc72af097516d6a4ae91e94d9f6fef95fb9e2bb8dd094ed488eef30dbf9b78b4ef68f0fbdc7ed6729f913cc787de53fb3298f0f894fecc4ba8f1a4a4cd495d4bcc954711cdb94e31aec47acef6094d405f8b6e4e191e0b81b72704a6ca893036c2f003ca80b81b7270a3374521b6e4f8f526a18e054693c8f31c0a8d26a4d950c702a349a1b6e5431c0a8d2697e7bf1763871252621f05f31b8fadb7d438a4a4c43e0bf82ebce0f8dfc6e3ed6dc38c9e247bdb1c39c643e0bf82ebcfb78d4bb6e1c7cf8502814b44b9250ee304377e7c4a2c3894c4051a057f6d89731c10fa2fcf8e003cdbb9443815bbe5ccc4a294c40555c6a2006d85fc712ea243e0be6371f5dadb2bf73820dbb949d815bbe5c633128b0e1017f75a7801b else (if i<10 then 0xbeb66f8be3676911b8266251202b4ba77f57e2c07b6458ec13311821882c02573bcdcdb3f6560894587080a5b05804cf0a724781f529f27e501e47eecf7dd53da91f1ff2a2d123c0f53cf7a3e6e91ec4a53d7651896eb5bb03ea77ff928d7e2ec70e7892935efd1f03c762098d4bb6bf9afc5d8e1c49499a92ba07959bc8c4154079afc5c4ba8a4a4cd495d3bfed5378a2237bb3d8b2fef09719235240f33bb8b8f3bc7557e2f770a6ede080b52af36a9c2c760e3b55e25d458e1c4949a5fe07a932505101a3e424f53cd70bd1f267d849ea795e7466ddf02a6bc9a1d1f2031535e4cdffdbe4f1b173363870c93c21f05eb8b8718b0296c5cdc9f3b02a8caf9b93c6c5ccc4ba8b1c3843e0a3bf1be2c108b27d170a43845daf08395e25d458e1c4949887c164f18100bcbbff199cae959b37cbccebd9712e78cdf2e3667e784b9e92ccfbe258cd914bcbcdd09733696cf9799ccda1a5e5e6133a958cdf15248d2bd6a4935cf66959b19499c95633d9bdaa04ba57f7358ff9f0a4d3a351d4ae9cd65d47d25d7adc4f60fede5d25087d34cd0cbadc74c8f044b925087cfbfe410ff2b9163fea5737fbc3a5b3edbbfaae44cfa91a7b1fc98dcb1f839fe7b97121bb9e7faae47acda52aa1589fdcd9b8225d458c87c15a92bac7cb7d41fecc079efe87e74e4acd9b1dc0fe7425cf19b0be9ce947703f4240a563363b81fce84b94b363b81fce9ca5439b1dc0fe7426752b19be3d640a48d2bd66bcdeb8e566c693c7255b4f66f6c8ba14dfd951b8f14a1764c222e5cf34af1ff34393c9d738ce7acd8a540eb48fa4f13d83fb5b796fc7330bf33c21f05a3fe561d092ebffcf73f1625bf1cc9990f82b525748eb66f088f9ee74bc56325b324f087c1477edfd6b6079ae78c58221840eb104afc703be0ac6e5b4f5296fc71d826625c43eed13fe42f3c0c409affbc3b9d2bdfccc46d20005cfd5b5ce94ac856109fdcd9b2de089751ea43e0bc7cc96c2f3dce0025556727bdd252bf27f6696f3563eccaf2f15e7ba5b34b2af79459f494f7eda32a243e5f2281bc93d83eaed6dfe29305d29fb7a3e3a96a6a539a4a4df82e9a92ba47cde0a32296a28c93c53fc174d495dede960a34b55e1dcbfb533a1cafeefde327bf1712ea292933525768df794454c47b7ae9249e3d8b2949a4aede6388f52957a4f1b5cc47a9476e502edbc05af6a5deb94e4bb51d1d9446f09751fc174d495d4b526477e37f6d1c5dba57b76064ec7f6e7af59c9f2fedebdb948763c4ba8b9a4a4df82ebb75264a8809575193cea78766259bc3885ef7ca94d94019b85ccf00f2803370bc277ccacbf8f93c526a21d7cc62b47c9a1e6366e558d49b2a3ac3cc62a87278db9510ebe63151b1810cdfacf78c1fdb2718cd252621f05fc1759bdafee7bba587118cdccc93c21f05fc175dbd2f774 else 0x846b8a52c9fe1c1b40142a7b7c3835ca13ca7b616135ead8054f0351540a9ed8dc39aa794f6cf6ca60755f269354e7da973c9354f3ed49191cc99e92a4eaa71eab2b9152a4d26419cd5394f0e491a47354f298a4394c5aa8ff14ae06ac5528ffe710c7393df5316ac526339e2943953562e0253e40d58a4f1419cd5394c5c38a0d45502a623aad5c4e4dd55ab88f55ab8a6eaad5c5e7556ae2edd5ab8bc9974eb3562726e80d9ab139e2e9eb3556f260a063e7ed65d69828175d7f9fb56f028177cfdbe4c05df3d5da0f3f6c9feff05252621f05fc17464b6cbc1e840c1324f087c15a92ba87cb76707a13c660a6f224a10fab7ac3a860736f33053791252621f05adf47fca181cd7db7c14dd8e1c9087c16ceb7d1ff2860783ff540b16cf79c24f56fcbd54a658b6844d0cbd6f4bacc7e056f7ac7e0555bdefef620bd91f9149421f35272d603e6509de48caf7b07fb2e929310f82b525764cc96dd791d09d4b91d870ada5d427af42d833a680bbfb6a96dc33ce96ad8ee268722fe86ab0e7ed61dc481a1afb142b31f9aa5c17ac35521aefbd932db0e19e51e2686284dfe47e166664843e6a4e5998a84e27f858ec13363832421f2dff3158a195d2e0f521f05fc174d495dede44b6b49fbbf4a860b1c10fbf0427e97f23ab31420560dd2feccfc3e1c9d1e0696c3389fe8f61b40b19e049fe8f61c6d2b03958cfc327f07ff6f324f087c15a92ba2ff2664b6da84ea5d871b4aff74840de9892eed6ecefd1d60c4bcb195ff48e2ec3894cbbb4ba53efebf7dfebbfec5914a6fdd2eed2e94cba5fde399e2eed2e95d252bffd1d612fde5881fd1d53b5fd1d94458fcbbb555e99e2532eed2ed19477eb0e7ee977fd280de94e78bbae9efdb3f26ea12684685e035085ef71aba1743277bf3a0bc108d93f26e86d502a4d63a0852eefccf7e2ec70e24a4c43e0bd6b3efddf1bd21879b1c19210fbae2d68213c07c8a3ec2a2b773051ab21875add7c0bd0d430eb1b02aa4bbb4be6c70e10f82ac3bf1be81a860950fe7c38a4cfa352fa2151487f3e1c93c4b459e151467894c36084ea3bddc982f4350f97b63870c93c21f05b31b0427b8e12a951fca8c573be19bdb044a294c40553e5b06103c7f72b7bb3681ecdfdca8d8ec133312203787efe7adaec8e48f2b354fede5fcf96c0a7eb667f939127a4796fcfe4248fddec54ff3ddf1a4b1c953d9bc28ba115fdcd238bc13349421f5ae1bb5246c2f99f38ef9bfde1cf7f850ae779b08afee6fafe7e75e173c6c2be7e393d9b615c2058cdb0af991f1ce15d9b6158b1b82666101bb5679d6f9985fb0e784058bbdf58778b1b0899b0e1015a5da))))

def seedScores12 (i : Nat) : Nat := (if i<1 then 0x70007100007000700100a001013000700070007000316060425031606040d031606040e2c03130704091a1806110e031606040e03181316071e04090305060f4607060e031606040e1606040d300c020750760702070410028012100214100216300c10024750102e021426100214260214260214497677491a1202142602142c082f39150e080200194a02001c690040051e300c08022b00351159475076352e02430a0035020000253b080200253b0802000327030200030200001902002537090200001e02073e03ba022b001a473703020a001a003703020000513b080200030200002808030704250e2807040e607258080307040d0e690340fb04280803070447490e28032e070425281a081c270e2835030704310e080704252808031c1208031c0e2807040e2808070426490639370802000e020002001600070214450200042877022bb900064976262802430a0600776b4913430a2628020006003b08021300262802000600090806251c379a07062528081c190806229b00002b11372e062c081311379a35091c0631081309081c0609080609081c0609081c0609080305062505060f38031d06090305060f252808031c09081c06190805572905060f571e06086403450f0e0806040908030506351a05350903050609080313091a0806350903050631080318130b0000000c0100000b000000000c000000000001001c00060e06250f02043a0204020401020402020303030016002d030004030016030a1611010300160300001600140408000426280200060b14060b031406410b0307410b03070b08060b0b171406040b091007040b0917140704410b1706410934170573410b03040b03171405040b1707050610031707060b08340704410b1014410814050b0817081003174109081745060b03060b730b03060b0314060b1707410b0609080305572905060f09570305060f086403450f090829060f44533417050f0910031705060f6f08050f4e100329173b09081745062617060f3b0910050f446f0964176f2526170644263b03050f100329170512260953170545061225080334442608103b570817100317060f032917260817060c0c0c00300c032b0004280c0200061a115000042e020a2e020a06000000006b012c012c49130a019c1a020018021a001a021a00251a00112f2701112f270101112f270154112f27010101112701112701112f275f01112f4327010101112f27660101112f011127012628020006000000000207043b0802130002001c0f1003001c0f02050f080302003b0802000626000f02050f4425090d0200262802000644263b03050f10030005122628000506120302261002253b0802001003000f250803002628020006270e4911112b992b1c2b9911112b450f290f4e03290845060545695708 else (if i<2 then 0x3e01041a0300143e01040c02010200521402005214632602004b0200521401260c0200521401260c100052140102141b3b022305440226024922123726772b22070545027605024902001502000c000a010c7069000a010c0043010200590043660c0002000200000001020002000a01250c000a14011508000802000c0d001401150c021e010c69000a01120c000a01000800000c00140115000a000a03ba02001c0f03003e0f021e03001b08020045370d00523e2737021e000a37191a034727040347000a1237000a0745274702080003003703003e27b84d00651c0f27040d4700651c070f27040e191a0d0803470027041b1f0e4d190d084700074527460e4d190d00651c0707042564001c2704312558284d2e1c401607273125284d1c161a0d034700331e27041228001d071e452738071e250e19350d6908472e1c1e270425191a0d080347001e040e58280d08490040160704045828082e4027000a024328b91343064b020006044c00140604823b4c020758080200040e0200060d000a140681366b0d0207090d02000a040e63372641773b0d4c02001604608102000a40390412000a45060d02760007080200000a143908000419130913131e08134b0953112c2e13001c04112c4c2e13001c9b06043553112c084c2e2b22001c07041b0e112c082e13001c06001c09131c3125190953112c2e2b000704131c1b193609112c4c2e0040041228112c2e2b13004006131235112c082e2b001c4037082b0028082b13000625131c9a261953082e2b1e131325193511082e2b220007044b4e091c060f041c050f044e190803294a051e041b0e084a05450618050f4e31251909642a1d051e0428092a130506191a032305041228130545063825353657084a2a17000525191a0803291e04281306001f000c000115000c000100001b00000c000000000000000001000e06061c060606fa0201020404020102043a0400000a16010400110316000a110316032d000100010c00010c2e04001c1404001c14040207042f2b0104000008030004080004300e0e6701bb4750000e080200000e0200060e0200060e02002e16042c0704091a080611031606040e08053516060419081307040908030506080306040806040c000014040c02020202070400090d020004280c0200062e020a06002c49130a0128020006006f31021300262802000602001c0f4d020030020a002f020000311802130002000025182505060f310e18133f07042505060f250e042c2f490a0500140504001405040300140411004c001405040902000504300c001405040000001405040014040705210e00230600070526000706000705fc0007050622000705300c2b00070500772c2f13430a07270100121300071b0033052600070506260007060a07000703001c0f0000 else 0xc0000010100810d090d02001a02000d02000000000900000023120005009c0f01040001000150000a01040c4c000a060118022214070f010418140f0104823b4c02010d000a010450000a0104190019000e9c190d0803470027040d0001040201040001045802001b1f190222001b121f0e000a011b1f0e500200011b1f1902001f0e0200bb1b1f0e198c542200061f0e0d0014011b1f81360d0207011f0e1902000a011b1f0d5002000701000e021f0e8c001f0e02001f0014011b1f19000e510d00140e51360d3d0207460e19090d020002000e19020023510005460e0d020007100200460802000e510014460e19000419040e1909112a0458602809112c2e2a1316060916060e191a1105046011070506253536112c082e2a17000409080304586028081606040e191a11080304586028112c2e13060d000104360d3d02360d3d1816070f01040001300d27090d0200040900090d0001040009000c00020000004c009b160601826f4c02220701580222000a0182600c020040010c02220701000c22000a0102302f001800160f8202070f290200302f020023056230122f00053002001d0730632f0200302529000a3f180409301b1f0e190d2f22060e0d07305a31250e190d572f2e17005a3125376b0d28096b0d130630250d2f292204000100011a0205010001001a05725f04002300000150000a01040c3323051e01040002000a7201040001600c8102000a40010001000100010001000a004312001d12001d011226000001122b221d0733051e01000a1d0721011b12000a0601120c1d07051e010001120c22001d07010001120c001d07010001120c000a1d0107000a000a10071e00071e3b1000066738360d3d10071e38090d000a071e10000a000a000a381a0d10000710003857000a3938000038000a071e000a041e4b4d11180f040e191a110d0300071e041f0eb84d19110d00060e514d190d0009112a00071e044d09112c2a134016064d091816060f1a1105041107050646250e511936110d2c69572a00043719091a0d0300040e370d1300401606041a110d0300071e04112c13400602000d02001a0d03500014073e01040c22001407))

def seedLookup11 (i : Nat) : Nat := (if i<10 then (if i<5 then (if i<2 then (if i<1 then 0x807800000b81b8046008049800006800e04200402160000c98004016003000010c13e00004a800001007701c80a800200e05e002c0e200000101c0002061009000000c003000826003200200000f8060005001003c058004005003c05201403702480060cb01d000405e0700008c6c14801902b82cc1640070010030012002062008800004b01082dc036003000017008600b06380c800000a023026c00200000400b004403b014817804007e00e800000a01c084000402200f01800f80080a9007821c1040020030064020030000808c06c05a025009003e00000280e41480f5007079c01600e04e000002401f001800019a010003000405e00002e802404c004003804400216001c001001603401580d001400100c004009a02600c000c01e029000023400603000c80fc00201800380a80f40030ce8014002006001008003e00101f800400400c000007c17a00c022000c0800a7014800803800100000040ac01000580e000c00007c0000014006000023c25801600380f40a410e00000000f817b00000ac00000f0528014014036022800000200102c800c056001001006404a0150a7000409600300980001cc0d700f00b800a00700d800805e00001b8158000000001002402004a006805c054000004009400600001b0018000012006068c02809700002e809000c01d815c1f80020af800001000502900002d6006005000000000b009803801002300380f800200001880f007401200a048400e013005000004e0240048008000001013812000000103680d4302038008001801c00000001bc03800100500000d60080000044052001000008c00400203e000000200000880f0028001014800004c09a0540338116014000800c01800d02b80181e6000000001c06e01301a00bc00c05c002800000600004007740b401200100001b202800585600e200c009006c0020010100078016007029816419003a00201d007223a03d00a008e009001800801a08d00001b40080070048004000085002009c368040050819c00e036097006400601702a003401e022000000403404b00701a80dc011001800004000a00080c00740070030024028036003000800200c000808c12e016000802809c00500180e400000c004018402003000102fc00000200080000380100000008010006002800001a001019803c08013700d817c02e000004001c00000000702c40080060030094016040016800401201600500c003001800a01e00580200480220014000019800000007201100ac006006000002406800403d00b801800004c001c028033022007400003203b00880ca007037008804401401d80000000130130594062002006800000200100080580e2003000017000000e027800000403400c0034006000008010c0da00f006800801e08700681c413c001 else 0xb00e06d8030686000001811201d00980b44f00840010048b6412100c008810e458020801405200c0040b3006606803980006520200bc001c2ca06f0068350030069065004000611c03980040b801f002800000c004005039c02c0d8091003000e040060941806802205904340420f200b00001444a00af000c00000003c003000c00000002307340c307d02bc00c03e0078004002040004010c0be0070130008040000003807401602700f0a44166011000005c50000100581146be06501703a406a06200d033017a00421b803803402900d85fc00e0cd049024c00204b015001023401904601503540e7028002c00a04e00a828c0840050f981105f00a4006829800a03900a02bc01008f001805800a0030000068000018031002c004027022800015c000006000403e09503002980860b3001801016a01a06a8224000034016800400209700d840c46e026010830041c004001839803e064001803406e07102d041809818206100002c6045009000411001d002000000003f000011801c03f138808822e00219b81800b6008030800435600908f80080b410713d80b4000058065032811606900e800029000104e82681fe00a04b81740bc000009000005e000011807804208f00183a406c00e01c802c0a8055031816c00000800580b000431a0000ccc11c00200082c800200002b81a400a00a014801800006001c81f80f6004000829003c011081826402a0000ae02d00a4280012809c0061c701a001001a07a05500dc08800c09083f000c0000538a00116000056067804a0040030960000001025864440c00403a037c00200300187c40ca01e1e980280e603605d801c07a029021008c01c06f05780e42f200400500240ea068006800400000102580000c400500183c400200200200600060000000004042005007002c0b41f302f812401e01d00d0548044002001005013e02411780b80a000501c842007400500381c80040780088188182007019804c00c00501c8054280024005802806600400180e00ec00500e80040aa000030807825c0010118004036071010036830400f0008100010006000002000807604d80380420020060004028021001013c000178033805814600102b802c10e11e00001080a60f300400040020020020000108003001008800405400982dc00003000d00c002c03e03b00101b810300d80ac1a2003006800801406700481a80060d6003806000a118000000000208000209ac04000000000040640a400a801803403701a81100a200904803f8000001004800000c00007d800c0060150350074ae200b0270030012002005001402c0f7005000000a00000280682be00a0078834000000001809004c04c000000000006200280280380760cf800000601607580180440a5007809c06401e02d01d800000f016061) else (if i<3 then 0xe02e66e210201986384a800f817807a002076809c0f2000245001805c00801b89f8001464001905803000100a021403c0080008ee815205910f814002832600100cc06e44600e001876602e008056c2c0004053011800e07b16f800002201f01fa9f802a0460ea187800200005a004c00801917a80bca280bf2c1866401e0d807b868801602e0e584440e2002011010c0c21150759dc402e6ec09e80343c602c00b86d80ce9ad009025813812e00b812800809d0840cc4fb42361c9028000005c00000dc02479b01f001812201200d27344c43f0108000117410850a82b814c450017819000000a081000000029504a000006400100681c802400003e8494000243000015406214f0040fd07860140c502f400005405101bc3b20760079ce86360120a4800404013900b01001160011fd005000200b01504e8056002003837c03205f00282a40f20ca013807c22e05c01e000000000300b01c800c4080d400880000c4000800c1260000190330596356004000007e12308e01f426c8ac022800453e12a00a058c73200000200985782e4127802805205700181f402a01b19180040101af01b802002a3fa000004005800804e0e2027c0e6070041462811b003002c00c044014800001805600005d401400c205030c02800000f00100ca8970310028082181069016c03a0230208f7867a0760ca05f4000152000001805c07d05602e426e0ce030802819410703b01a807c0000381968fc20011c0005c27c01300505e40026aa00f01900360bf05000000a600006100a400804d011819418e67b05390640360130040c0401a06f0348544052094002018860a00d00900680320080328088018001093802019800706c811c1521dd125005841e005023002802e000014800034e008003801401200000b00e83100af12a8084586002026021c00428600e80c035006729a04240000010398524050158004803803a1af01a0c202480020000a6405a0a915a82b000e00008b9b1c00400000406c40fe0450438058caa207000833446a00d000003839c0060820c241a200100114387bc04c00001bc5c012200c001000801500104a812021c000033000000d00280045e000a01d805c0e81f8059007c0ba0210ed000cb5e064015837010200400e803800000600600300b201406781e01360ac004800011a00604a00dc56a00c00081d400616c0ff000c5c004e03180000a4016000801401005a07c800400000100f850cf660a7003814404e09d4cf019c42c0ac100802411e05300002dc00611726a00301ca1520fc00c80c622b000809c04200e075817c06003d0290094014319001003004e0360b2832c00c12d02284a80ba245000003c2701821d0004819a00000107782fa0e10220b0c4b82af03d800c00200f1e380101ca0090cf802001e002000034c06a04 else (if i<4 then 0xc64b75d319333f1c291c049aa90c1ed40ac422d0889a83982201faac430b8bdb02626abd5efbf1c251d246cd1e449104076a4790b492d07c8c38a346efb5756e90033aae2e47aea22517b2c6f949d11a8d77e15072a382980291073084f2d1e50c3fb4e6bd2dd9400d50ca421cfe13b6ff87b868886f3064a49d9c97238dbc7d9757df1485389fe50a77fc1ad2d228b681e513a3310c70a79ee4806b4091f1ab2af31de09519cd1ccd1496d45353b28eb42fa589c187e885e5f222f25f1034aed64f41567801370906eab30f21f6894dc2c0d18753021e108647a22bd346b7da9395df0a53abd3670b85ec358dff99a2f37a3b3ad678462c1bc35faaf76903de91ba478e04746ae34900b04887c7611b13c5b70b1b4763109b8162ee7e076546a58e8f97553bf6c64432f51b9b81002189141174846898f57f67844dd7a358175cc27f1cb4b96265f08bd657d473606539249abced0e6a0727145005f0a1ed7217e2a9e868f7118136db1feecfa97097c9c1841bef2e6c02ee6e01cd1893c629fa032836044959205953890a9be2a7d0964529bf14ad19e2e01bba4fce5177614d3a20cf978a0a6527db306523eb6eb8151c275b519457d9b2f73faf22eee900a122fa46d1ae969d8f60fc46a56be3815fd8ff8af070badf5b757f1c770b5994097f4de5225caa76ea5f567c1ed7e66c5053a2683e50f057d673ccc35551806bcac77708d876226b753030358b5e2eba1fc7feac15133635d885a8e5c4aad19c46d7da428c93f05ca5e09d85d2b2016202892412d61097a48f3d41113004d01656bb3e46e14e0228a7ce71fbbc440caa08ba232805e3e863990940265ab0e51a10e22bfc17dcaeafcb407aca3f169ead1c72b9e45c7c3a240ac9d5ce26d51bc85bdfda6f40b64d00912a13a7c1cc41ce28c6d1806002400a022309000076a00187fc11c05504904a9b9c0b90001d9cb100810cc00380000360db017c2fa0ac00100481c60010001601b8e09f05daac00000a00218c959f060a1df000808819605b803001c00002304601243b200180b80fc00b68d096c98a04c0370f4009a0328439034026111006003803621400002201bc0f008580a05b80005d180201b200f4efbe9004a1900018ef40081bc00d063c150006025000837811f00001f93d600017f81d9c2012500085f066c00302b84858940162ce00082ce04642a000460c04207b004001e3ea03807c41040000450c8400c01600f809ca947d401f87ac3122591a6a2d827801800f25e411407f02983cc08a51d02193b803000d077001829600202f82dc1f4073102800000003300000006ae4060429dd0adc44006981382b02b60690344948016011800002600704d8b60a7a000002801c0565da0eb00e05b01bc0008000a665a500a8130136068007800041e0ff07b804015c3e832f80 else 0xbe40e287e0e93f6c5530548d32e680004817864629c1e2e9bdb99695820003a03875dccde92c9e0eb02b7e48030000c9f26ba9c5e4ccc0d8005452293920829a8578890a6288884fd2c3350784a4f3f0fe7e02bf3ce4a8edac7bb8da21ed7d624b317e16f80ac0f9851d68bf04bb033de7a81f9ac2852a2d0a96121a0a9397066cb04d0c2445132719e8a896364a1005a518c3678e5e670228d8bd700495f882840f2b3dd4390d780d348d18ca68daa5d620e191076a296e257b39af2cba15f73849195f30df49763d8176d6ac938e498a0daf109a41df457ef8af98a3106c1c2535ac18d454c28045b60ee49f0ae05f2348f908c9784ca765c4e28c445a81c2d14f01b61c826d16773adbf5d5e62b73334eb166bef2314759968c03770560d38efb922437c00723c3928132142c4d822038dc4ac6f7aea0cb88016cd3570b38c465be44f6204ea385f201a75031828686ad67509af329802339aeefbd9fc10009a6f273c23b4090ce6c6e6e4015ac67d4e018eee9c22fc2d21246c6ba24a3425946524874dcbea45e14751ca63cdb712c01c62a225010463033d424376351245951146dc54fbaf28f73640765ae1be0e97c0495de662098ab10ae6a351ed74a411ddd848759d4f0268e51827ca30cdc614d4982e60b6eccc3ea23a14d80783538b4062a63382dbd649eafdc603bb4635451080422adf0d242677c3d597805ba8e917c3fc5d27c89069845770073628992449fa39aa6cca4189a1558ea4315eebd10c11b491857251d408e6d8088b0d162006241a49f20b1ec8a5511fad4a33912f3b35408e11c7bb409027aa289f1354a89a6806ab5369a69455c850cb26154832ae0c1a3977b090d40b2570310bb089bec6e29932db6f119043d61e187004c968bf5c7561f226374000cc03d68d32de3e217c3814fa179685911e1a3ad98a9e0247af3c88ebec315d4a40e0621ed81dc3f80072e09d2cf1e41e0663949d5a202cfc5adb3f639e6d685d225681f8f0595909ef2efa70f40c5db54dfb2f03c162da82e3c0aad42cf0248439236bb4cae3c3b200ee4d0d02aa02e3738e9c1a467714123bb0d35e2126a1d1c2052deca788ac390293660fa1a24d740144025fa9f0a877727a390cd71f3432088b3ede727162c84fac0226af655b91d46f2568d9285c31adc479e1885cad436c042466280ae11d5c36ca4977c1decd4dbb2cb716f85e521d34413e95ee9a347b42a0d8ebfb4ef4db9da975e037a5ea885bfc1255d8d23d65ada08e9cdba3ed401bbd04f97ca865b7ba608736ae65753d21add45f3ffcb8f1da74aacf473166615c3fcab2499ca807e9d21cc0e1e7788cba9e616b7c2609966045e886a63a94dd4f46bd85757e98f79498ca90c352c409b620e9c1d008c39ff07c4a40d1d270d648a1b6c380a300247b20e2651c8c6669380fe9fa9))) else (if i<7 then (if i<6 then 0x8064c9ca257061b628e0816c632a33900a21f98158c62abd8fee07a3c50d69754d661c83499006ae739f56bc04e1ee0e4b71acbaa969b0a37c9c57403d3a18d63c5e097ad7a2e786462fb2e25a3092b79f3ad22116ac7161d9b1ef50b1d127e02a901c1c5ad404b2f9a3ceb6204186c400d2a14a44be88c860c304588b8f8e229397888b051878176ea16e2e055baa57c0cab019028fdb139cbd924a8e31313cca33495a6fad1da50a2d262abfd2cb8c5a184cb4a02adb92d02d360c2194244c430bc464c2f187ae5317453170880120feb753a5bebda0f3496c7e091c717a4b52aa7347796f5c658635728b57ace21302f87c260914ca30b428151e2567da3f252b84644760185c76aec796127a23e64108d738bafeb0a9447d91eb5ba146c3bc0e1a27a01c64d8bd624a8ae8ae2f5e900b76ac68e854e000d7be97a0b82708a4c3ca49b741d34e410918aa952bfba2d894d857f3bc929a06a583a63760ac70f4098e9899f152af8008f0b3265572566ab0e1757b7d98903abdba651adad615ae8e1d594246a2442c93a6bd6514290990d72e7e05acb8623eb3ad5b9947667c8831ff206e24e37e82508694eb2b686c000170957c87a04a1e6927ec71ac00b9247c77abf992001ea0bd5e1c0995fe64210f9eb634c478dd622d34929c491799463218f137f464127f8e2936ecf723a48d44ce8882d766abcd01d690d6c7cf7400102183b0ce90e9102888dcf70730f9920d1a49d459a8039c40cd71201dfac366f54870642c0d9ff4a771c37a1ab50d1325a211f5e13f545057f0ec431c1400628a0d3864ebd90fdad5855d62b0602d36b1f37487a32ff1f4bc5a90b26a34b1fc2eb898c6bcd15ac1b614043ad5198c8b825eaba5b461eabb5b14899541c759c305b020e45f99e26d28e6dbf520705fd8b16c13b180012a548341c0204e8505e964af270fd81ca7306195669e54f70ca383f44c5bcedd4579c479156f7c171a4a5506ba49c949e208a2a144e8a544be5d6b3db23df22c10dab38698f9d8ae2a72cbff1ff45750d6afb05d08306d7e14308a57178c3bec9fd1ce7c45eaedaf7826e1b57e625150397c6b08f002005ca1dd915182135222449b29640e9c6c9cf674605bf390543265bfa6b5b3a08d53259f9bc8b6412189cb018ddb7b260149614a6a2559026ee0fc78ed940e876962198210e817439059b0299848f7a30ed701a2bb98bccc97db2494723c0c78ec395304228efd381372cf590438878395f3085a97e56ccf449116dcb5e3db49ba18904f44e106d83744811948fb83da821cba59648a4340ecf1e54d5649e101b7cc8d60606fe4bb7541a0b87573e4549c9456155e79e24f262d36496449b826d4791e095da8d2e06c297453fe52f221731682522e8f6a68e80ea26e18588ca2e91c8291c3519ec80a609441c6922af78006c5 else 0xd1846cd7aa6caa67d2303a5115be09b87108668553a2880f180ee079ae2f734271542af826090baf82ae283a4db3cdedf95891790afde5b4df8dba9ead96649a27c8640285fcbe1867deff5de62c319efda8f713fc2c3044c143e40d7dec96b23d60ddd29f24500f1f2a2795f250f89945f440d34085fecca1bc52452f1c169b8a305195ca97985ded83096d197c072b22366ff8195cee1ae02e879e591a31680a40361183b80056fd384a7eab2abcb1c3d98d29a2fb08d4f7604f9209ec182098e79c9976fd4d07adba5146030e0be7a305fc13ce60fa8689fcc7618ebf96f4055530ee0fa776db51153d3ce2a5bb9d222a672d7261291d52208488a3ac1611c29b467c2a96abe816165c7f8bfacec453b6a4f9f69c7c105a5cd08bb48ba8da6dac509423c0d4252af9872e75eef1733af3699aecaa9086b8a45e2a0356e30368df19214547210122cc30f89d54b4c4f23414d97f6da7789d9d8930a4b00c0781e882387ce0e8933b52d88e8545e8745e98d91fcfd34142a02fdf0bc9bd74ccb3afcf86851fdd9993a70b00c00c1b4452da980f11abb62e678c6d153cadb6d2cb9a74f489a4f09d97ba87a5cf55a1f233d0b0f2d3efc862ba95a38cdf7063b92530833d58a9c6247994a9154261b84e4ad262413fa02bf67d0ad28283fb7cd33737225117d215abd9a8fa72258f9915a48ed36745d6ac577c4c0b10864407bf1ff5e929e60cdaa1a1de84e04e083ba00005114a8ca1cda3b4748f2be8a4f74f6b0bdbb99160b25a50d07138853579632b1e6fbf4f7235d38af4b71dc402fb98bb4ca32129c39043cb9688a52c722fa845ea0314396a438ea2ea598e540306506155a498f93390e989c16f44732c4236beb0e746aba7587347dab9b0cba99e0d97c65012178eb86eb26a43f42276e68db5110bcd5f48d54feb02684762c242a148ed92520d00ff54202c2a55f042d63c18bb5e956f5f4e796fd5dcd032da09b567236cba42a355381cea5dd14d3f281143c39fae14ff3512d8a90ff1b12000916936c87729af313545ff46b480cfa14255ea50146b630503d8b4210056c8d2c289d4c2c0b22a5a6236742adb35f2e547a83e31b25a451dc6d9a75694981a3f1d75d34924e6565164102da57f6140993145306ab58510e622ab300e0e853b43c218c5fb33871f5dc51a7d376105a7b4bf13515b7510d1fe66d71d3e4dcd8ce162ce295346e9e6875706b798f56139aa05a70c56c30001d70a22893a3766b21b78891a8c4b690b4dbbb871cf6ad6b03e2a35c59411da2e10ab4964b3c518ecf04b0c52df2ac68816a303968f845963849821d03407425498bea0abb49e3045fe31140139983c894c575be5a03cbf897803c23a088e3a6866aa2415426c056cfb6692790de84ec537caa78c5899acde95c9b16f4a0d9aa5912b0a23296435c72ded) else (if i<8 then 0x51d03ad5df859edd266a45340be5c16011204740d8758a21d9fd56ce6aa3b3a6f0348a501d8422e4774eb1b65ffd7c7c20a7285b6a878e303a0a8836101297485f4bc2ae729080690fb466357ee0a111460cbed40caff8128cbca822fd792dc658bc5d84e0b23025f7a59a2dd5a9236e74e924aafaee92842526eb188f3176acee622e4c2ac37b215ad2a292b9c9b421eb059a475b6e8a05619cbcc4e4f4b1a00187e33014e1b424c910f34e253a25f87095421f023373d4bf91419650330b95298defe8d9958558432d50224539007fab636dc3966a38f23716b0860353a15b2a7eb06a39fc670e093e230a35fd0dabd4a36b8f1fb03fa5dc007c8008b8a5c6658aa15852f7a1449887be00032b132e8e284f7529239ade6580855de08d4db01fa927693a00977bc55aac6acd7b3b78df8c62456f5d1a08d8a5a88a9283184fbb138480bb4b7904e8ef0a6030d4895e3de4c3132b805c1fe2495b740f56974e545afb9c2d6c11d1ca625ac51495bdc2a64d0ee1c011178f02e542b46171cc5549736e5e59d23206a803e05b3b0ff59923110b74e79a1a0c508aebbbda1e840c69c40eb1cb5c6b2bd381335889781f89e0518086385318441a19c29ac625e8128332d88c1b4a1e74b8699e138c527fd6e550e837aae0987bd62ed415ca25e00c0c92a47523cc70f6ee548144f17894ef4554c2145739041915709ff23b6ec570822b211681a39d4e404883d007ecdc3f36ea9785c38535b132c4af25155535452187580750a910e6eb0fbc3bd77216278f2aeb445c2544f146b26ae5c9e7508cd5c1ba471b28c0a8ce330d199cb5804cc1920a8e560024e833cd08540efb82c0b31658c6ee2410c9ce7ac2fa45af8e470ace1a2364d3bc50112a5db07f5077ab4386141c1de7cfa251e8f71f85eb9568d8719c0e4f1a3e8e7e3474c4dfdc63c521265ae1f818a41180292d523b0da79d2f456d7e70d0c5634815ef3190c398f423a310c8b69b81d3bc84d22b2593a07a613900230e1518e344914d3bb7a2cd12aadf97022f0fb56778598dc0c7e9489ec991eb779bce0622430a1c34a0b5e3a14fa42a0eee96545624c539f0343a50e5fca11062322b00f5020000c17d3b4f936c951c43352be3aa05b94d0d988a653da9cc6000006d586fadb62fd53fbd368b28b44fa5045f3d4b41c703794a133f22eda24c497bd0002342df06b8057875281c7f627c0f6e6fc08e6ddb9148d83ff0bb8e84cce2660fdc8a05308794bdda3e1fe80534f203e9ea9dda1b63b9100e691448de303a4d127bba6d76e19953121902ca8931d835357ab6c8a2437b6fbd4bfa1a162d1fb126c1681a26785234c49b6537b135c6f2c823c34372609625a8280d2e233f03bf8619f742cda2cead8f3d31ca094783ddaa9a4840013fd85b6aa31602015e4a2489b25a34a1d4e874c739 else (if i<9 then 0x4131c15c4a108dc540c8afad9d5e279c9efab2e5a3952c079a518515c4ae6b7568143689361f7885958c3e4a23e146d460f2b4bc31d6cfd80530d64cc17a6c695978fa99fafe58b59c2ecc2bc6c33404a4676671ffa06c3d306b8aba4953724fa32734b80406d116f56c45367dd966a681ddc3a43a822c1a60b4ea65e4258021069d962fa388b1130f2dc9d094500d8def21e45d9730b6ab1d18f3b049be05a2f4792689396968d14d54a5cdb677c8e3812469731f5d4453c9ec8dc03bb135b4883e68c886eb2d884731a4ca1b30852033b50064b0755b13b9ff43e7c3fa86c7462fca52d664d2accd92daaf172b0fc2a947e9eba83540618d87a543780f852d23a339043449ab18e9f8c3625dca5386a6c3be27b64d77cca15d3945d122927f71921878373321abc4da40b173d4305125b483a2a1401b7f0d1ff07618eb2ab1ac298f0fc79008a21b2788369961ba20e46c6da19afd8391e11222f4e63e263641a9917a0674aa4a5da5dca171c849d975903f440cc8c70aafe593dd8968e4784526920152a6a00ea77d3b041ec1551898a1689de5e6954b544d5d3608ad8436a0d1a1864d9071dfae246ab481b5e512f01c4044a37e13124c17795d64390f701595451d86381e432e1e61112bfdc78618cb907eb328933784d2c8ca891eef0d38ebd119d8cc56e89bd8b8543ebf926b1a8acdfab2c94f217800c41a570c5a3cf784629caa0a41b98aa25f926c34ec454602ee894eba3341aec460c83d55fa0f1a1210c12156a7e9a64f0651ac9422549a02029e055829354a65d8816ac751f6404a9eca50e7e49c3efa4d4aa627181047262504928b4c348b3e89d8459580b740a7a4ecc31c5f5f73f760dc926d7f1d3d11e44ae6b46a03a6c82c850fe1d580dadce178c6890f8e810659f88db51d77ffa1805ed8632c03360efd49a45160f6b0547d284578cc3cf69c6186e63f60359cea8607980fe30f4851ffd3c368916f127665e9678546455605c4fa43290822381314ae0c00041bcdb3eecb1c19f937017901579ae33026526d5c6d39ed9253c4c8601ccdbc82976ac5117cf85735d135a90c3a701a8abd11aeba47d510a2fd8b8b4f0fe612b72b51c3478335240b77d22c4962748bd633e9f74d0905365ed14d6d2c65dfe994538bc8177a5bb6b404b244ed24d87b8898905faff2490beee7b201010fc2ec194dd0183908249b099a998fe187e9b1c42212b0bad390992f70fbe342805bf88a60be1547d759cdc65c356b2b4e7ec257196260e3e045856881dd7213c268195f1024223c63d85ad4cd28d5c6f46f063441001a9f6d71a0e5b8baffb062438af2482e4611f194243c4cb360e497098ae7439036c0a8c4758f4893462470d02b13ad51eb184ac3624cd45137e0bc5595555724d831d5ca0d73283e586d2ae339be2e830c63a99403859e else 0xa6add017b9959c54b67f41d22e2cb10a700ea2a310501462d5636f567540c26a3c88890cc382854b2e73c40a10b6cfb7b61a20b0080d062ba5ec91b59ba0f32416c01ec7243246fc6a5875b92e6030e6326251eeccd05178d2cf99345ff40148560f235e523b076f0a01643500a4796388c35abe9bcd223b364ea94ee9d08ccbcbce5073870992f26962ec83dd555648a8bbfcce7179c10b313b8a035e7f36731ba40e9704473227201170d3dd058f0cf2ecc03df946818759ef5171a08325b72d266abd6a47a09c4d70eed8a05c3fa3a81581a6ce390dad069ffc9854291322ffc3be7af8cd65dc7f6e009b10008a197ac60413cd0a56c290e6960c904dd652a811d2e35685c98c5f56f104ee3a39070cb20173365e35c72a318a983cc50b7c968d220a66e1082ecbb9eabd87da9527b2e72e6254892bd27f1b3a4e3d4c6494f19740dd25a6954bd98ea2590a90bc01911f0f52521712c69b0647ab752315da4c96aa8a0da46079a2e3c5c2de6df9961ed9f86ec768099008e0ba0a796079f1c65399ec39eef2fbe9a79b1ec30cf72bc2a74bc9542882510d1a778691b86a5a1c7ab1f88d66e640a4ba24aa634eeac0729e0cdf54c6010d1dcf155b4b53aac5080fda058be91cb6b8e5332648ee6e646e39c91be493143fc28c38451b75b0f030e054963c50c31cc2e364b08a694775b8c1d5146ef82619d9fd944c159106b843102e1b08943fdd197b1947268a87224425350e1ecc7a67bea54d768001657ab15f0a1602d6af628338c099aa92ef34ae8bf31f147d17bfa9a02d4023510841d3c8f1b1f234cbdca6cb64b5a1210cee0df40693d01ff4940073a5df1376f94c73fce79a17dbe3c44444cb572349b68e7347052b608c92a743bc2537dc121c1050dd823b70a6ba0878d9934720c90bf84789ffc05bd2ab741c757cb3120425952dcac6e0ce2037c963c52923dd0c82620c5ea458b88fd6ae86fe8c68be91c01ffa49959e72b1b0b39a9b9ed6c3b90611adf50f33c5751f8ff67d92d3c57dda17ccc6c10d8f2a5c3925a72101b12216ea04957e57a0610c8aa2aa94898955129a6d212a25741525a66baba92d3512a59ecbbc7c541b8825ead178392869b50306463864f08ec9e15b39385f62deaba3bd7caf870167aa324e6013f19da691b22ee52ae7f11bd6f582c9768c04ea2ec37bf7c8d88bf4242e522041604cbc38aa464c800e374111d19121d7c7a8c23b379a0abd6b4cbae21c4283d43647f1be008c53d47e1aa04c419b4139a2f5fd66c48b7acbc42e2b4c05a22a1fad5047307757bc7c026893e3f45972c2c760bf705e93ac6ee49644048d6896366dfa4375530b672fcab1612c071a87e74c7a487ceb0426723728f5dfd4c9643c6f9aca7779bd8c661ca52c8ef98b2f52f02704455dc34e0128232d46ff7b6a48bef2f9d4310a)))) else (if i<15 then (if i<12 then (if i<11 then 0x132cf1795856c36c419104cb23eb3545d64118a1151c8e58cc812a88fc23c86e504a96dcad7d366eaac9970f3a9da84a6f5028e5c937fe64a16e5fd0215c84f0e52612803c4926459e2191bca04be3da5d660efa73e56e17ec3551573364a629af5e3c0a289d50e688a5d15bc343a9921a6f7358a550a614510d178a0860aedc8925054589b374952a103f6a0c1d8020d3e8d123dcc70d3b842648f812b2c226828f6bbc3c66e76e9ac5be0ee8e60046f60fe156dbf0b14aa99851eb262159b1f95e612495946246219b91c013eee7221be2d17560958a3a6ad1737d9162b570b6051735e99de8613075dd33b863c23f611e3ee924dcca012739d449ef1c18cca22b4709479618bdc68d0a04330317226c8156068093ed81f5fcdce8099bdf982121388c11e8179af123e5100f6091747eae1c8f45c23bba5f12313772bf589db00e197b2c80ae950d843950586967625f20133c44f823f96863380e3d7e796c03e13091d435dd68afcecf9469a88cde5479698aefc0017be4ee61961d511ac1d1f0ca7c3ff2759b5cac25ac4e73284d54d210a133aaefb17d15b984085368b7ec4822da899a1fb9db65f4c300e7a9adad637a6cc9fbaede819c81de6ca7203c1ae26944cd80a1780af8ad230e5a2bb74eb20320873d8d49b13a54353958f88c5bbaa9e66ac9ad23d3cfc7dec8e5711cd1bac3503333cfa2d0ee9a2c2f68d3465085c08f88c02f93e69ea64c75c97f3842de3930407a2e4504c7607dd2cfe91427bb76c52620f13dc5f92ca2755526375e6e05379dba784363f8e9887c9d362854de24f26e97275c08f0403598e7adb575d25da53e14d61c1a27a5741a0cef02575a973cc774300c0f93b18c49462f8132641579aff4a2944dab42c98be0a55a3533b91752d899e61950005269de543da59c736cd0b27948389688c7dc9f39d4c33c0dc7c5804c61e8036f719711c46e49d0397cffc1f75d9d7cd9937869b1a325764798ae656248b856faad1ef4896466c10b0a02a72446400d51a98c8c72d327e2e5632399cfbcf732bc0a1d1a29757fa16350908b123f00053b80b83130f94bc5aa0e34a27a3016905762c20578000a9713b9892cbcd1f1dc30ced886568eb2004b46df8c2011bdc97570293d67219545a64728696bc1158129b9a44f3051d7cba8d0c5e5c2a33faa99829c7b1e316ac57b517609c80d8ad6bc8a79ae3441631ac2c6e2ecb42c26363cd3b9519c00087019c81ac3ee46a8153849d55f303a138a3f79f840329342806fd2f4c65700707383d00a3ce7c03ed4932acf4e06510d011dd90d7301f2390ab002f5501231f85d3020abc658103f44a53bd50329d2d69968c4b2420d67ae8c5dc6361de4393338df300d72c025e11c1f661e8c49b4636da2eb70599e37b1c6185c22d4b1026bfe716d154ae23e0ea9020f2155bc4b else 0x23c3d626d2a8f004bc12b99d4a835776b9a62ad44a2eb36f091ee2ad1a378e2defef85b46d97c20cce510f41fae2a91d31060d19c1ce8722b2dec1c0fa328fdc30884e7785608dc5d888858dccd17872816c65b4ac22bee17344daca65267cad4e84cf143bd69c8e98271e51d472645a8bb4c3d26133c6a488ee22a13a4d0b42603ef9e2ee0500a84fbc577060239635e7f02a09b0666ce8859aa3e4294e645201265c2b7894d72d34262d8a8b539248778cc8c44e0ef70deabb3c9b699a6a6ac958d708520257ce24405014e0d58fc08293097a1887864602e1cd306030901eb7fde067a6269bf0070cdc0d82817c7ddd6b31d69fb8222ece9a463cf69d4331a2f4b865216b187399b41dbe7a219a342d86a662a2d990e48418668c154843a88b6c30776ad71ef96496225945dd7efc1a03e62a71f3a7901d862f4d7d80cc2d3666350039a4a7c28130c093b40aa5ce44c4a977911ffe2120bc3f194fb2f89cc68a09218b099208fb273f79f0095e60218616e0f748bf81d483a87b56a1c723434d77f7bc59d867101a7819703527d0379025705094c155d4618410f1a1d145ffac82c14804a4f2646734a4ba8870fc2c6c42e8f2ea42553e55240f1ec4d937157a52a99380d2978f04b1c40ba69ad2063fde8f0b16f0be6b24004c5f46622a0933aaaca2a5da5511725475196ef3d5649f98a5110d4d56f9b08706c03e0c71e0916af1e0e629f2645139c476242fa18bd5a918b873c418228360c4826281322c1895834810543e29feb9760b0f9a7aa29710a42b0c80576ab91d9dc6148a40f980a48c12d60d32a1b127f720645b9e768f574d43e14e17534e6c176e5348c3c03fd8d9c55e5b60d91c1d34e0628bf0444d15c85c4da3968fec215406459536857ab5498d4a003650c4a8b18c3782461360a35196b40046119e8fd9dc4c140df51ee0e2252f350da57546790973bfde7177d63c7ae35b05906357ebb9f4a86ae61c6a27cf4087488a9fc706cf6823147aa3b0d48804c5c4e088af7e44a70f124d7b881895b68360465c6eeb6153e0002ab82d782c0c7c5181fe5d533414da8d6fffa46a0600b0bcb849411038045b71b31891c56bd806e37c5e746f4e29c3b1051b857f18c9cf4eff7a0b02428011a488b565a531c40a9d9119b6f3b2a43c8a1f42b869b84b26928c0b6b16a5994e092b71f7a5f278b004c36893e1ef8265f1a3ab43d0c208faadb239a2a0658732640be1adaef6afe641a1af8188a430002cc4110ee3a6e2112cb579f74821c1b2987909bc426f748db4cb85153a6afb9d722670491226f0b9ecf80494a7314f6350ed65e86040c4237d8e560e643742dc2a892a9c7549b599348c77209a292da0ab21b84cabbaaab891c52f814001a6513c3d0a2b4b5052c0504023f4c03fc40fe89061191fa0fc8332691b2c999b227185) else (if i<13 then 0x40c444090f0de59180ba20a8c62178bce5987b539180050fa1f08cf93bd4ae8837fba7a27be03215e28003ab4a9b8431becded90075ccb8c1e4288513aced0f1a634c38011d6ec97be45c8fce3ee22d3aa9778be6617402d98a6cd3251b9d0004e55230a682a635d70bd6ada9f81431f86a0c8445d625bc91e90df67a296a854832c0f0c988e078bc341a1ac90e2214be0230c3eac4629b5d55347644a93c621f05d472d621714cbfdabc1430e1d75717fdcc82c27b8a5959c84bd6a3bf60b54ea97a64c8bd16a4800f4b6d0b5b511f3bca807151937f6c2bdc2e42342419d6c9a96270a9fd92844f3d20bd9f5c49281248e4b7da210e1b7224050718ef3c997a8f68e4e476a1d47e4e16a0429c4970afa64aa0427261fe4f5b5b2afcd2592a335b0ae8fc2c1cff16f54665f520c97d2a74211abd4d9eff6c23822adf56d9c7ec294fcd6f4a1a53acac713a21627219101c505a302aa1f15d1008085e62161a4fcb9ae5b90c754b815e0c9df8d1833229c4443baa7a5d44b0a16148bab4c0d4319439999147a29fd1084789146b980ddd46b8ac591661a33781b0e4a6d0a4ea0a831ad417961000000202d47a5a6bba801c5586a2d26d99ec1507ef94ed1c32586be8fe805a6414fdd63e6cee934910fb26554327b65529fd264d09a85549a43988d7a0006b16774a897ceee72827890b972178c2320e2aa88011e4b8003c920721b0346fc4baceb3e2559e3ed2ac622984ca3c4c54d0ba19fab4628a2b216cc023a0a240459d6c5482cddd98b8a4465c889055652016ec9ddf4c3186202721e553b38ca53588364ccbf86074fd4ffdb99b0a84d817870f3e756997e001786c29a203a26f3f8ddf91dac44e2c106c1938f1b6691a2452268d062d8c61b4089ddac0e84898f14544daff040d38826b71c2796864abcf643b530c450df0e221a349e230a5557628dde4738d6e9ae1ada37ee7a84b4227d0dd373d8f0c40156077858203afa993184cec4850bc5ac4ca8c2fa53ca472cfb108c0818a1d890e7052e81883232ee5b1956034d6540a42bc475b14ec325285a2867642b494ac5ed2db18096035d88390fa8b4c077f124903841461ed255a071a78d64955b8a46f92fd5498f28e0e17300b99016e2c979ec321864a958442a30842c965c715a09f99544ad63488c1c4c36d04721122eeb96c8edc6072b2519d324f3f26e7cbc4319588ef4803d88520d2b925893141948f1fe3ad95076ca56c0510cff05a9c24a56c9038f3298d29ead2a87858dac0c0e4d17dc3d225eef0011c4a470e338141134d0484be22b9376dbcec2a9e24fa214046950279a5844de41e3e519b97e8a4a3224af06604e5e04a2ec95c331b088545339c5227f27d584f3f6ad4e8a047e7b050f1067488703b8992ee3100dac4b677ee6f50ac995e09585c1461eae4082b55c271d else (if i<14 then 0xa0a563b31fc0856883a8802384636d42b9eadafe380b0d2ebae9ec5b00a7aa2cecb4a2bd66c0d9c6075b96b11db29ee9f037290ca3a42e02998f16b16537bd7d26c7e440837319c2da65b3632d23a45744bbe2a56ca8026a339066e5ca4b53585ee2af40f70fdb8c68eec7a2810b355fb766867b34e9da1d1310221a2001aa31652508da9bf7fbb45d47ecbab4fbc5290491a8ac437d800ea57da01ae8d41ffa7b85488e043c09fd4a1b314fe590a1c10822d800a3e16b00f4c0bf50cc96689102d3f9287022c227cc18dad1ccb19d482048aadaf037aef5a9f3a1790c0ac852e5d707c4284413ae787207a8b6d85ad15cb6b1022fc9970ccabb9086379da384a50cc138d4393978a55d74224528a1e432c2bd822b2f96f220d082317ab19b5d1cab9f2699e700dbb264849ac001814ebb706630eeadec84d2e38d79ccb04e0f89269009dac9813f901da630824ec01201efafe3522945cede2983471e98cf4e6d00c715a88dbba40e018bac13b6bf2a8a3d4a8dcf2b16f405227f124b3c8ee47e6bcf4c03ec71042045e94ced43653f64bd0d6fe8af8a84d2b4bfd0347d831e4c547cc7a50d4c9777dbbaf9ef9cbd5d9ae52bcf1c88b16810c503ea7f5009d0a421ed0ab40ce8da86d0fa3437aa13719b3ce2aacb5113ea665bb2fd9140064b234a5f6202a6bf2eb4800b5f59ff5fc950405b2c9a89b82b4ae8684b902636fbdb0a204ef9461a7026df2f370a0e81e376ab9aa3cd953177453c09be06002249c08f5eeae416d957413ab0fc87bb23ed54c0e9450cdedc0adca36c0e2b30acba98c6555482b4b9ad5d545497d5949f4cc4cf7b933b0b5f8f6637fabd8895d20e0d9b888c7f19a7ee9ef28febe4bbdaee1c4954d9725f3e2a6f7a644962aafb1846cf33aad5278683c0a2e580c9c342a764bac0346e20576ad4ba479d61b8dff15b899d09ce247e222644dd4268c21c51559d6340a792631dd3a7d20efa4d089a2e46306349c8d2db6e5dd4092890d34a2845b1ce81b2bd3f02cc4247b04ff865404489700d59403b4b35d16e0e643a51f19102b2f0faa33cf1b3f0a08d91c20dbae1a537b57ae2ec007bc365846f368a304ad49b31d28485a22adef40a9480b17438dc177901e69e7f29e92a38f214472bd0799f94c44ad405321c8f2ca26b8125af5597198f199361521171ffab266efc25c90c8d8791c0bc9cc6ed57f3548c597b2e7c514b69e3638d3184ce20b423277c809a034920d350c00299c8460ebb414ba970e5ff88e963524eb63dc05ab6907c099d3c8e347972e36859ca62b6d62db0b022cb7663eb959863e87f41f96d41f1a26636513771b49b5bea9c50dc202d35a09e35730eaf2c33b207774580298afe3b2de08ef96323449c8d07e74f374e15ac52ce2eac40fe10e5833a38d1620df02370a641e0d38493fadb5689616d else 0x333a20de586293436d722c7ab9615697158fb4812af406ee0e345a33447a0b96c108a51f07e8ebe47c06201752f4413afe24bc5e518413bc1d47b11f2362daf55a3a2a8249ff7801b3fd352ff0061b1283e5fbb0aa65ea58623ec28b508c283e15ec16533b57816e3313491e93ac382f79898186d0d4210bc95a31ce1d3250d3871034ebd08e4440d98a1219a37496897c4471b3071c9f280a9e84d4253eb6722691814ff366a9e247988a57180ce6240ed8860e501881828074c9189d74fd734a0f0d7a7094c8cea7ff26a266da76cb6981b9b4906e0f747445ce6acdc456d7e643cb0c0c199849683787f4e080da6572c1e092192b156c205e8cb1d5fb6489400f36d92359d84cedf5846fe06169a667e403d0b15517d49afcda6ebd03715b4944072e6abcf2d05e677dd6c1d454db10f057a1b60dd5371499ab5d5cb00518a94641d4cad60ae0946e733a31a48931d6562857107c9f007d474c7446acd4a653d38dddee6b0fc003e8772f95f12466aacc818d024410f4484be28e45472c9c9f4b264ed282f90b0076f92e6002509f220261f19b22b0b2e65fbd9dae5e6c2f95963c7ce354987379799a284e14dad58827d44ca5f83a5a3f4633941665700d35a72355cb77827a443021c04ab718460646c872717bc14ef4a2c36fcae30bb07866ba0672a3d5732ad31d1ca05d5391c61dfd49e28bad2c12ac9c544423694593a2b62c302b769b472bb665b03829a6db0d123f11b75ea4167933d0c682370c3566986b348d67546944be20149331661f3a3c9f8df164b5aeeac249ca5dba0dcb62a08246228bc3341844d4bc6e4551350322d42d2648a7ba79012a1f59a46d28791f75b0de2858f56ca49b7b8bbc948a0000c1d4113e10913f59c14845bf09a504140dc3e3c1d25f7188e18498eb0b889d4e3ead2a72b9f1c8f69f28bf6f01692900d01010a28ecda31172c0ff49f96d986f98e6aba4011240fd8d794518643769072adfc4ad8fd43c63aa515b88c96b6739112848c090407a22583409ba641849eb8f2e984a9d24e15323c7c01480630bf9e45cbd8c355b81ed2dddc547a4b9d4d4bb6bad0984d207ed5953d783ec7594744473170d368675f8cbec5b406e2bc0fc5f060832d725423c45df46d35f05361655c5c325b7b19c8b25cb823255b5653835fa87f49fb251dc16dd47e007b2eef77117c17184200931c9a814aaed32516c3c0c6032bc0b614ccbc44ea6f1789b3c025263b4a1236e3d177301058855fa7d015c27b622673d04dc14a3e5bc2878c8543b130cd55932a43450c5b184026cad0036abc2f793713778c525dd1b79ccb00c3f25d6010064c96c8dc48c0a82983c7260f0bb4f8c2d948c4ed163e50bcef4f4900c8e092a51db7a73f542d961eda938ea9490baaf1ae5995102e4bf98aa660dbf17bac24b1e232f028d75bc))) else (if i<17 then (if i<16 then 0x46e1653c8ab08a161304e48b3a1532081422c02b2462f903a898b6044c682bc8ed85cf05f4d98a3c3c77bd563ca64cbe0b8bd349cac9b73b3dbb54d4326dd8430fcb10488565f88e44f44464ccd2bc83ca6d16555f70c16a5a3999f2e6100fc65c8bd0f62dc0dd34c6c7202c8eba2f8d3ab4ca3c3cd60132507b30e757f9097a294f982ed47c66b8db834f783bdd8339f9a1f97d0805ace35d3847cd6895b10e048d1b69056647a34c720878d570ada8843950d3a313c0ef62346271c8801c31c13f35a2b1d0413c90acd1c35861a29991b4d4f02cb44b4244389848a43e31ca3c68de1e2902a4038cd33cbe64264704cada3d250261055524edaeba5305c4016468de580a0ae50301d592665f101a86464c5f693a0380ef8560808b68638041ac42253cee80ec0101d7306e92141f8e327e0efb3e88b788952c73f731bdc8a716b6f6521e2ebf07a344922c8466ca93d73f6acf90f6bdaa21287b4860b61104282c83851c4202e426b2655fa0c3c9248c7a73286621588534429864531281d05b2712a2bed1d71352de052bc648567f225bd23588e00c2b52202e583a991957c59294cd657a911482e96b1ea05eb8ac118b5221dec524980517430364e4207cebcb704841b2b1b0c2812e26408b547647b7f615a2a7265283219a6f48b05792c5655a659eb2241018a292912d5b697cd1fcb0b233e950d1b7668401bc52a70a1c7148ceeeda69ac55e028238828f65a432c15103db98bb0101750b7127a281349c6269ba1054a526e53772b10c5374f13545d96e2fe62e6f849108f342753a69e5ca02cb307d671ae1638e40138c2c6626b38a5598ae9af514c5fde1b300c5fb700936698424ab6e992028d01e76422d093ae760a4822de2ad0f67943414a89e179c59d5a5ea739261836f8ce436cfa709bcb8441e0ce09856138b008bc1d2a8a4ac8c9b30e624b8b0bcb983cdb114e2c5ce835083e0b5728a78380a74d34a2ccc7832e3b118cffb6b84da80ff4cb649e248b396996bddda1afe09c46cdf0209234e2792355167554c518f34ee953745e98f5de87efa8b20e1f126a256026f292a0e2701ad6a21c0bfc7f0b651ec5f7752df21314d3d60958554ec14191a0f4235a6299531362d00e107723098a1d71abf4de5629089e29a497db40b94425a61b04054e4f9034dfb459b78514fae478a6b07c9009db17c477373e93c1505ccca781b153b2c12908765503540bd69297096c6b2e055e6ffc5b50e5c2d04a08f762371a8862320c2aa1e50ed9255bf81a387e78dd0487c35fa732e422f8a9d80214f3affe2920ecaafa88c18ba204dd029e74e0510c40cf06d0232009e6c09e5a60bcf6dbef207431ee291cd7dbf193b0820f2d89c9891e510fd7d0150cf865876d794152582aa7354ccc5c53e083fdec0432ded151c4fdec73245d85ae8a7558 else 0x8013d6214202004d8044840241302000498004ae8c110900123b062900404691000030011600300c480443a101008010955d00a000402418006800f9c321041803c0104908100ea18008dc003889c4260100d92013011603444001a0000cd0e8d0411030c002000000c20008215902ee84d208080b210850a1302a6e51d000809e01b805400258a008835008ea00116e102100002b38807c1202028001dc0a0a99e806ba448104e01864844030005a302c7100014409d060480480a7e408000f8b080c08003712d002f400b0200380440266a18094100700940440c0150040c080004705204044009000cc658000150762371e1da67f69c29244ab472d45697f000518f3cc1dd044ebbb84a01540829d801b1e70089c194732789bf67a2c8195986043ca8bfb22c3acc0a9668592eda20aba6bb692a0e4c3fd9729a223c6a5e77e9f4682a70c70fb7242b6bdf59bde2ce978db80b59aaa42a10bd79ef297a08013761d2eab4e0a17547f06b678941ce6ddec89083acc86f8460bb10b975f9eff20d129a67509f5aec1bcdbe464c0390f7901d89498c918c41d6eb58e549d2d4e23be0b48079c1f43c28d8aad287c3c73eaa99ec71a8ccdb2d362096445e85fc2e064d4c92a0d56424f2d058b9b10f73e8c7e04475da22becd5a46ed9b5b912abee2739e4adec84cc118a23d710e9301909ff049801508816c5f88b8f2bf10468078ffa7b55f8fde9391b53b6ed078c842d125d9c98f8b4280b0032c32337c69e9d4a1db2c3d0a8951ac159445a09a4354a75190df87ba58700d86e184892aae2537ccb0479495a71ed73902c746ab09f62cecb548def618b19f0ebd373a4462c8b00f2c59e783b84a20adaa39eccd20cfa3fd283d38d5bea38e24c33ec5626b49be70b00e21fad70582a2189da43d33a82570cbe3686e1ef5341002c538432fd066e8135a7c428d0aea4cfeb164066b547073a2ac22616697000d0bf18d2e74655f89943426b94a84282e9b520b278ee6f6709fe988e4d2abb3ead849b626cb00b9ea8e772663a781f2f0400764120b15eeb51950b3644b8b02a7504509beff575bacd8dd8ef3aedc2e6e277096d6d22e0e26c23e3b44abfe2784b5b35ed305d3176b16cea74c42f3a4a276c0f08761731db4fe073c1e66684cf4bd09331cd08f43f2812cafe1d375405922a43c9bf69246fc30a4c54bdf0ec650a9beb51c67e785b9b35101825117a8cd4a408eae5ff4481ccf5778982ae6e8454c5809866c17326741b7be5c314b8fcc736b00b437e78c898eb081513bdf888af9b895831a5e4e2d7002b690090332e7006e95988081d399e24a69fab046b42c626b0c6c66448186222f327e7d851a7bbdac41e4add279ba09e9c2f992b952aa313388e7a2a145e9a8345de39fd57fcab251a9312da874135ca04e6ca25d353a8985c88f863) else (if i<18 then 0x2a06970a1815631a3022080ce4683a000010819fd2a0619106750400800819c8105a000466c24005200199c4464206465e0422014819624131852064e8405170219176c91005063a7950642618b6a40400806270a0d54b4186c4000208c61600a4049018404001004060d3028d0031810045900205fe1e0c000017e107c085805eea040a844179900a008145e0b18050a0175e209860205cfaa4c0020171cc36340585bb6085806016cd406982205aa046940b016841021304059b2091580016528130264458a0108820a1612061840d057b0110050115da3012952056c08362049158c0822045055d0208815c15544c00030c54e104050031520000824005452aa016b414e4490409c05310204054214ac8001920052656827830146821a006405130600205c14329026b0345000811048113ea456854484ee0520005413a0e8120c104df02080844136b4ea0c4144cd903134001314831804804be10f4a62512c5964810c04a70a18c420127c0008380449a052086a0124825209b6048780028008120c5804027047b0102420211da044000d446f0020509011a8508230884624410002011782000108045b044a40001158c024321c44c84c00002111c860220204410209160110e8a401e9c042f14020e44109ea84ca04041da0234f021048eb1a8a2040500ce220b0fed403a88b03f0280093000fa8013040083e5218030080f7e080882043d9800001080f58000488043d2409100e10f2ac4221a903bf04c062100ee0521501103b0115007090e9c059080083a1121144810e65600001c839242a803c00e24c8140b0838008086cb40ddb8910200036f044500080da805301018363082043420d72b0019038352200601340d2c00801504346000159080d020408020033c108080310cd80250e0b032d0709b08f0c80a018080831a203601800c4c55185600309000b08280c0c30a010102fdea4085300bc8095009002ec88a409420b8cd6c080002db388124090b496c1518702c5a000b3ac0ae8028462842b2809280710aa4a94024002a26038b15c0a5691626a0028a02a506240a061c8220402790092085109c90880005826c4801200009a08020094426228809801096c0090085825581004e02093a07890218244000c00d208f80082200423a8041a05108c9ce000b20228118800ce087c2300858c216028c021008410810004020c0d802504081341ccc0001fa3108010307cc4984d0801eaf3302134077448b246881d2003301200730084800401c8012204860704950020801bb542100a006d0a93470081a9018008ed06801000080019e80640046065e1682010418fa8e201a8061201040800180000f300005e8404aaa241702200204005b0051028801664043080205806440c2a81560046038005438014020014a188474800505000201 else (if i<19 then 0x963b477964a98977896674175136414344197647992977b9a997477917244ab63341787b641793491423179977776827b2191969479a92939999669443a2771656772967614974949797394957174774977465951a6535517b797833739891725b694445a94b957b4619983175b9a915711a597666357a76479619399794965599682a533977651b22457968931a93535494779a962959992a772791b959839744b19618b7b455a17965765137671797a491794749693462675952b545333733799786199997767977977477447337766769179b78514b97b79544734935152b59211153a919979b741714441864471716316767448773143496674747776711579634962a952799179a957944393b7278797782397a99726571529736877138196779997235371593141211197979777593539a71793399572b744775479996a9272279194214931579977a4769999b147a63572b8524941112195536774b948517472913579941921622876467697745b6413911879217979a47b8367777795978811a64453173534961739714327413597a9a13956b2779317958299499171a296951774a9973863777799b425a2586b7166b77916ba71375429396627773622818414295757611757212341414917362311772a992517735846777845942746415249971551b4361472b7156794499916b337997717173471898647779499819993442692792379737979173b597567476237619952795493579127271719649377391b95a4773947915935176b97573467794479144946414971319497652797437273979747612a984817885394977a5472491394b517a53357362a737952175395496191779859769971497b675864719419956159563941a179955679574777392929b475132997a71a97378247695973174525331477974949a9b955b6148449857975743741624797599277375723467678162a946237337494777719499961b49a194929935b763933168741914647b31444551956993a1976414576976559795764915344419376417491713a499951317a417748000000011f882088b2207dac00908101f51024006007cf800209401f28830045647c144e00a3a1eda0a86a0487ac120444001e9d4810019479f621141401e5c10080810793004106801e3a00c0004078a04c096f41df902005f04775000854001dc500c0010c76b003dc8021d880100880075f402c45881d5a1240405874e002401021d28c10a8000744034700501cf001002010739440201191cca805471a0727818050021c840004022071e50000c391c581830a19470c0900092c1c16400811686fd0ca2844c1bce0108c2006ed0ca620b01b8c0000d1086dea84012111b59215138c06cb8063e0001b0c004128506bd004223201ade4c8236f86a8684104011a8703450 else 0x9579649378a118bb9916415997597a7799991643b163973645137964747411a3218178a31117397779379559497915779977767493a99447376737754276994369263a6166131a1274347aa12725a9366a1a1449747242536194b575974937473711979b95b75214381778196749699919948697b543171979451736159995272475277497456522329442741479756329259717957b463926144496b77271a724577627827b667387773729371272513774142432b97713381677194262416119227997bb99774746969298791b23b97917b2a43999175764442111613426113597772a792632a4452895197719744448514922493964)))))

def seedRuleCodes11 (i : Nat) : Nat := (if i<1 then 0x6680ca018402b805600ab0142028004d00980120021c03f807c00d4019082a84420882410081d883b087600ec21c8039206408c4617042d185810ac2128024082e0840907800e1016001000100d601a6032005380a6012a023003a006f00d041248210840007e10d811b0035006820cc019182c1056089841282250846085cc08901100200838406820b2000036006880ce018e02c4054807b00da0194421083a087410cc0180028104c088c309860f001a002c405010202000350069009400f410e041a88322050408c010841f10381060707880f001e000007a80e501bc0370060008200f201e00360041286e00d88180230105e40ac0111020103e20608090012101c041807480b40164022c041805c0098010000d001110201034e050005100403e0071809700ac10d0010001b08245044c0682050804000404c808800e201a481c101f183a086040b960f0018181420000c5017e02a8048806b009a012c81b082d00461088a0f0c14301e602c20500ad00ee01c8017840c01e2035c0618096107030dc41a1427204c3034073009200be017401d102d1052309c0049a05013c00acc081010301c03f406d00ba011c011880d00ea0188014881f0424183c2058a0a100b000602ec02c003e004a403407f8060087a40a4810901c201e503440190020212033003b0073008e028c038004f004c409000b880c01b2031805a902f1044007007b00dd2c20032404d8081206600a481282131002038005c8075008840d04120e0500a240380218415042a581405e8042047c3838b0580b328583840079882a0836206408200450030405807780852032104c80180530444402410080fb004e206c200802d00c6007c003007e1818382c4028203200208d01198013342068200281c0c10120824902903d08544060003809f0092405cb071a07100058244098404105c007881104193416682402a0224002c4054e030a0500c201209049c043004300805208152c100820b038206240202dc80d9a06001001882028609040e02000339c12242058185008c06007048200250807080c00f40199c070806033c41600f901c2107420a06011c1240209038806107a0064504805b002a10242038a1010102010204140838100168a09100c3c0260248029403280410b8d07060e200e3010f0198032406401806d902a1824381c30394060c0601640170c07180228189030a03181402d8a048c050c1630247040c030c1058040448a0b381218405041808340260043030e06181040105038e01380a0154817041e300e40280161812084e5014a02002a280e10b040f1013241600dcd019c03086e6018507007d28185028e00960328026010701805e241c40b040e80143000037c40a0057104e409cc029400203c20dc80e801d301860280331c02206e4050e000c00 else 0x42008380f001d803ac07400e701aa030405f00b8016002a005280a201380a40043008404f2216822c885508aa0944827804e20942104220083e087800f041c8031106010982108221303a10686098812182220442081a0f001403904100103020203f807e00fa01ee03d007900ee01da034)

def seedHeaders11 (i : Nat) : Nat := (if i<1 then 0x10291b840f6040ab400203235d81e79415380040066af03c8382a0c007e8cd46078448535000fb11a200ee570a52001f4233901d7e11474003e4466703a7182888007bcccc2073e34504800f5999480e60389f0001e6432381c8c913ac003b68640038ad026f000748cc7c0705a44d1800e6218e40defd8989001c1431b81bacc12de003726637036d142558006d0cc6e06cb0c49e800d6918c40d7448925001aa331781a98d12180034c662f034ac423cc006850c5e06881046c800cc998800cec408c0001953309019948114e00320860c03273a2234006190c16063984439800be9182c0c5a8885b0017a23058187841086002f045f203091a20ac005d48b84060454409800b9916dc0bec607fb0017122be81791e0fc6002de453b02ea081f2c005b48a3805c5e83d9800b5913c40b66a879b0016822658167f20f06002cc64c802ca001da800580897c0589383a9000ae992cc0af808739001582241015b880e42002aa445d02b0c81c240054c882c054d7c378800a890f880a76186d90014f21d7814b9f0d820029863ab0290701aa0005190752050fb03470009e18e6c09f0c86750013731cb8139c40cb8002626388026a36190c004b086cc04be5c3158009490d1c0948b06130012631a00125530bf4002406340024596178400464c668047e202e40008a10c8808e1d85b000111218401185f0b300021c62f8022a1215fc0042905f0044aa42b28008118be008836854c000fc417c010d330a64001e462ee020e4a1464003acc5aa0400f02800007220ae007c1004e6000d7415100efe1099800192828301d13a12c8002fd04e8038e7824c000591897406ebf047f000ab312600d6fc08cc0014e423101a37c113800290c4080334ec21a8004f107ac06468841d0009a20cb00c291080a001308170017a900fac0023542e002eb541e80003da85a805b6803b50005e50b400b3e90734000928138015f2e0e00000f9427002b7dc1b28000f284d40558d034a0000ea08c80a3d406540000d20fe01392a0c2c00661818a02546c177800b6382900471e82d2000fd504e8087d4056e001bc809a0104ca0a7400358c12801f54c142000682023003bf7026a000c8304400727b04a200186808400dba208dc002e4c0ec019b7c10f000591016402ff28206000af3028805b7c03da00152604900b050075000290c07a0155980dd8004e900880290481a30009a300c004fab031400128801700993e05c000225002e01180c0ab000402005401fef013c000754009003a030244000d6800e0067da042000189001c00bc880770002d200380158200d40004f400580270c01740008c800b004a300280000f54016007f94042800161802c00cd3006c0002440058013c300a400034800b001d8e00e0000490006001c5000f000044000000000000000000 else 0x4aed81b7b113ca003dcb5c7036a2a2752001c8cb7906c6464e340145d16980d70d49b980284bac641ab211356004c2557f834d5126760094caada068ccc4c800121d957c0d001498200233b2a8419c6c12e8004375546033217259a00844aa800658524ac80101d94bc0c919c94b001ee2a91c18f53127b003cb551b0319f124c000768aa3606283a491400e84d4640c39c4916001cd2287c184aa121200391350003030f23f20071a89fa06004c477c00dfd13f40bfb888e2801b8a27e817ea191ab0036544fd02fa8a2322006b269fa05f0c045e000d4913f00bd5188af001a49a7d01798511450034324f002ef25225a0068069d905d43a445000ce8d3ae0ba1bc87d8019aa27541730210e10032c34e902e33121900064e89d105c0ee42b800c7d13a00b755484a0018ba272416d19907a0030c34df82d60f20c20060c69b705a63e412000c0513660b40388170017c9a6c8165f39015002f444d902c8501ff6005d669990587da3f8800b98d3080aff6c7e4801701260415e3b8fb1002de24b682b8991f32005b649670569063e0400b60d2a60abb787b4001699a54c156930f4f002cd249c02a9261e6e00596490d054aea3c7c00b2091b40a7e4c78380163122c414cd20eef002c324448294151dae00580486b051e203afc00af4d0d60a32287530015b9a1a8145248e8d002b3342c8286571ce80055e68530505e6396c00aa8907e09fab8721801541a0fc13e730e2a002a0241e0279531c240053a483504e83237e800a64904a09c33c6f10014b1a088136d40dc90028e440f826a521b5e0050a681004cbdc3658009fccff00985f06be8013c99fe012f400d640027233f9825b171a96004d647dd04ad2234cc009a4cfa80945e468d0013299f34126a98d010026133e5824aee19d0004b467ca04910a333c009588f6c090f8865b8012999ed011f970c9e0024f33da023a8d190a0049647ac046c2e31b400920cf5608cb8862a0012091e60116fe0c3c0023e23c7822ae11848004766789044d42302c008d88f000885305f98011a11db410e660bdb0023143b68219921782004524767042b442ea4008988ec00845a45c88011199d7c106870b780021f33ad0208dd16be004368754040c142d140084c8e940808ec5968010811c880fe980b150020e137e01f8d915fc0041a66f003e8ee2b9400824cdd407c2945660)

def seedNodes11 (i : Nat) : Nat := (if i<10 then (if i<5 then (if i<2 then (if i<1 then 0x2e4f380ccfd00143f3804cfca01a2828040bd402c2f400d8bce0392f28044bc801118280407d402d1f400bc7ce0391f280487c803a1f180cc3d00340f380603ca0170f180603c4024a73409e7d40179f480867ce02588080aa3d40278f480da3ce02c8f200fe3c60167f38059fc80157f18055fc40276f50059bd00326f380edbca0386f180edbc40166f080657ce0195f280657c40182f48034bd00181f480647d00121f380743d20170f400503ce0149f280623d200d8f4004a3ce0128f2805a3c600c7f38061fca0187f18031fc402467340957d201f4f480813ce02d38080a8fd40253f480a0fce02b3f28084fc80152f38054bca0162f20054bc40271f500587d00381f380e07ca0391f180e07c40161f08cf00f50119f3803e7ca0199f2003e7c60119f1005e7c00158f200363c60158f000417d200d5f400413d200d4f400193ce0143f40040fce0103f28040bd200d2f40038bce00e2f28040bc801118080407d200d1f400387ce0061f280407c80101f180503d000d0f380343ca00d8f8c01d1f100e12fa819a5e50354bba06697540d52e680c21fd03443ca06a87740cd0ea81921cd010438a0307f48100cfe80f19dd03e33aa07c6734050ce281a1bd603037a003057f40b4aee81595d502b2b9a02057140609e90208fd20321fa00221f480c41e901c03d0011f010157f480e7fa006dfce03ecfe81be7d40f33ca0779cd01ace281a6f580c77a006dbce039de500c57f40c2bea0575e502bae680857140627a4092fd20387e801ca8081357a4072bd00365e701a1f480e4fa007c7ce03e3e501f07f40f03ca0381dd03ca75404a9c5032af580bebd0035af2804abc8037af180625fd02b97940d65dd02b97540665c50178f480f9fd20307f400dda0204a6f480c9bd00356f380ad7d20385f400d97ce0395f280e120204b4f480dd3d00354f380e13ca03e4f200407d20351f400442020108f480ba3d002f8f380c5fd00117f38045fca0116808041bd202e6f400d9bce0366f28045bc801158080417d202d5f400bd7ce0325f280457c80365f180e0fd001728080e4bd00362f3803c6020381f400f47ce03d1f2805c2020380f400d83ce0390f280f43c60319f400de7ce0159f280567c60169f100f5fd40437f40111fca0467f1095d86e15861980f99ad158609407dbd60366f500b1bd00246f280b1bc20645f581117c204147f44dd1d5141471411cfd40482f50108bd00432f280e87d40431f401107c615c019856405e14d0861407823d601e08f5009023d002408f280b023c617807f581101fd004507f2811c1fc413806f581101bd004606f1811013d404204f401100fd404303f401100fca04403f180829e00024a54100928cec01e9a290086649c0306f7700e1b60802c677100858e080491077011807d004600f1811c03c4 else 0xd001a9e7010cf280a1bfa078de513b6ea80fbf4007df9403efc600d5ea00c2f38061794020bc80105e30082f10d58a1a01a7d40103e70081f28058f900307c60103e20088f580787a80383d200abe70175f280a2f900517c6020be2010df0809e7a80393d20219e7010cf280867880453c200e7ea005bf38031f94028fc80147e3005bf104a941201abd40105e700caf2806579000cbc60065e219f9434038fa80227ce0113e500c9f18044f8889a10d126f0480b7f5003ff9c033fca01bfe40107f1803ff88e7190d443c8280aef5003b79c01dbca00ede40076f1803b7880395ee007ae2811c79408e3aa01efd400f7e900828080657a801ebd20105e700d1f5005cfa40107ce0083e5008080803c7a801e3d2008fce008fca010fc800fbd400fbd2008bce008bca008bc8008bc600d7d400b7ce00c7ca00c7c800c7c600b7c434d1ee01d20214c1ad44b1354310a543009d73f0954360650293d60093d40113d20143d00273ce02a3ca0093c801c3c60143c4126a9aa90d25509288a0137ce011be3004df100367ac0173ce00c9e50064f2003278c0173c400f7ea00b3f38031f9401efc800c7e300b3f1003d7a803abce0205e500b2f2005578c02abc400f3e70079f2805cf8c01e7c400f1ea00a8f3805479403c3c8020bf18056fc400f8f50025fd40107f48031fd00096f50041bd200d6f40019bce0165f400417ce0105f280253d40104f480353d00064f380193ca0104f20044e020093f50040fd200c3f40038fce0063f28040fc80063f185989e507027541989cd0241f500fc20a02b9f500ba7ce0258f500d23ce0378f28101e0a02b7f500d9fce0397f280d9fc803f68280b1bd402f6f380e5bca0386f200e9bc60355f380b97ca0365f200b97c602f5f100d13ce0374f280d93c60384f100d93c204137540f0bd403c18281087d403d1f200843d0030bf200a2fc6021af280b6bc8025af18086bc403c9f180c27c402d9f08a861cd0267f500d5fce03e68280f9bd40376f380ddbc80396f180997ce0255f200757c601e5f100993d40254f401053ce0464f281053c60434f100953c20221f500ac7d001108280883d4024af400cebce02c9f400ee7ce0349f2804620a0228f500963d00348f380fa3ca0368f180a9fce00f7f280adfc600f7f100e1bce0316f100757ce01d5f10df91cd0353f500c0a090272f500ecbce03e18280f47d402e1f380e07ca03f1f200903ce01d0f280b43c801e9f100be3d40258f400fe3ce0428f281323c60438f100963c223376040a1fc801f7f1809dfc00246f38075bca0256f20075bc60246f10095bc028b5754098fd402d3f400d0fce03f282810cbd402c2f400d8bce0392f280d8bc80261f200907c60260f500b43d003f8f3810a3ca0418f181163c40268f080417d40335f4004520a0104f500b13d) else (if i<3 then 0x1ac23d91a423d919423d918c23e917423489ac23489a42348994234898c235897434045e023119fc22719043371a0866a150c15b0dfc1500cec13501fc22d01043420200250da761996b7d0ccb5bb8665add4332d6e61996b7100975a18461a9f4129cf00015e68008e65410269260803f910402146820de22410896f6080527504131b78200c52c002707e0002a15020238a7d00a853d803e29bc0341302014858100a42bd805e15dc0320902010828000c8040805001ec028f408051e7b008b9000126e0002e74100b4d820531306027220c14b341806057540bcae681317c60272f8806c4f380c09e501893c41461bca29437340787e70128fca0261f8826827944d04e68120bce02b17940582f100e83e401a07c603a0f800ac07944ac0ea80f03ce0298f2808a3c60208f100f9fce0387f280fdfc80397f180e5fc403f7f00039bce00c6f28059bc800c6f18039bc40166f005455e515357545255cd01f5f380997ca0265f1809d7c403c3f200a8fc00382794090bca0311f200ac7c60311f000a03c80200f180a03c002cafe893d7944bebaa2474a512ca4a80d5f4008ef940477c612a8fe82547340a67a00413ce0299e5014cf180ee78805adfd02b6ea8123f40089f8c060bce0305e5017af200a578c052bc402f5e00109f38084f940307c80183e300c1f10060f8028e1fd156875455a1cd12282540663d001f8f3807e3ca0288f180a63c40347f380bdfc401c6f38071bca01c6f100d57ce02f5f280d57c402647f40951e501d4f4006d3ca0343f38064fc401d2f38074bca0202f100387ce00e1f105a81d514e07344f409524201140883ce022be30155f100c279c0553ca0439e4018cf180c27880633c00326fe817b794099fa0048fca02f5e7014af28109790060bc602a5e20182f00060f9c0307ca0203e40101f18060f880307c014b0fe8a207944dc39a2700a50191e80108f380a07940523c602aaf100c27c802a9f180c27c013180980b21fd12e87944961d5037829448e09501a8f4008e3ca0238f1807dfc601f7f1007dbc601f6f100757ce01d5f280757c401d4f380753ca01d4f10074fca01d3f1807cbc40302f0009c7c40281f000b83c802e0f180b83c002fde4016ef180bf78008756502ebeb0295f480fefa005d7c6041be10175f0008e79405f3c033e70309d36f80a5fac4b2fd202f7e50163f080e5f806769652535e90142f400b5794054bc20375e00129f280bcf802762061510f709e85940b87ac0b23d2029fd002bfc2038fc033b96534194d34c8a5253bd2028bd002dbca02abc2036bc02406062365ee1405be23c56524354d24c4a502a7d62587d20297d002e7ca0387c002e16513714d13012d1590a51280850303d61473d20283d002d3ca02a3c212dafe81c57544d2b9a0477d00428fe8a7c79452639a0473 else (if i<4 then 0x28a31cc92877342a1bc86a84f037af2c50abc7032969c07a5971379f1c8ea7c5119835c1123cb0288f14cb1da7327765d0c9d8721d735c481ccf535731c4a9c7713d7f2c8e9fc500d274c0349cb0201f2c0341e300d93960412f2c0362f1806c5d30208f9602f1f1c021d0580ab9d30157396032df2c02190580ab1e30156396032cf2c02170580aade30155ba6032bf2c0657e380cabcb019578e020af140613e580c27c70184f8a010682c048be380813c701a1f8e010082c0540e980803c7010e78e021cf140437e38086fc5017bb960376f2c05eaf180cd7cb019a7960334f141167e281ecbc5008741603ae78c061de580c37cb0186f8a030cf2c0619e28182ccf34e58de456b13c5017e3815a8cf04c5796010682c070cf18101bcb0192f8e0404f2c0809e380a81d3015ab960334f2c0566f180acdcb0199f9602b278c0564e980ccbcb019978e0311f2c0623e380c47c500c741600ee80c04dce98073bc700e6f8e02cdf1403d9e380b33c522359ae08ebf2c0e97e28069dcb01d3796028578c070be580e13cb00f278a01a082c03010180981e300ebf2c03abcb016af1403e7cb0169f1509a0d7526833d8e20c721e82fdcc207753081bccc2067423813cc7604731980bc54e3cb1448f1c10e3c5024733ccf9c6f122713c0f1fc7013374c04cdcb0192f2c04c5e3013172c0647cb013078c04c1d30190f2c0643c701aff96035ff1c05bfe280451ff011a3ae013473c0323e9804b5cb00863fe00ec7dc0258f3804b1cf01767960189f4c04d105804220300943960188f4c040fe580419ff00933ce012675c05cde580b9bc700c1fa6012282c02050180409d300c17a60201f2c028105804020300883c60190f4c0461e580831d30116396022bf2c0414f1808a9cb0115796020978c0412e9808a7cb0114f8e022674c024ce580815e30092b9601e5f2c0208f180411d300f279601e4f1c03c7e58078fc70101f8a05e07fc0c40f381e01c7031035e064065c0780bb9ab80ef22b0205f024023d503d01dc704b01fd7019017d5019013d5028009ff039009e7028009d7038009af017009970330098734e0090f44e008ff2560086f035005ff034005e7035005cf04c007d7034001ff034001d7024d9e0803ccf208225c8a08129c8608435c80ec14cba5c426fb65f801cb599c144b4e0818eb09b4562ae5f404b924102991b59007234ce0a345e0823d8b41029d14820d457cb2097afa0001a5eb380a4b88201156f040282da082535a410260af7109a130ee00c9ae08024354106525d530ca4ba522169705c13424358052236b00dc44ba01d051ac03b0a318070136308f026ba02202d8c04305318068086300f00ec600f8020c137b1ac136b1a403db194136b18c138b174125ae0c141adac13fada413fad9413fad8c13fad7433f99ac23f9 else 0x268d794583595343df5003b7ca056cf1416efcb05cbf144ba8d7125af2c496bc5134935c1763c7132735c0c9c6f14c7f2c171bcb05c6f1c175bc50355f2c0d57c70365f14cbd0d7352431c4ed0bf22e41bc8d106712840bccb93cb1464f1c4fd3c5032143c1743c703bdf1c4bf10f12cc3fc4cf06f140cf1c0fecc713cbf1406e8ff057af1c1767c705e9f141063c70478f148b9d0f23773fc535cf7152731c911cbf14071bc8d9c6725470bc975fc72577f14185bc50375f2c0cd7c505d4f2c0b8fcb04f2f140dc7cb03f1f140943c534f93fc53a4f7243931ccae4bf03f919cce642f32e9f1415a3cb033743c0f9fcb05e6f2c17dbc50475f2c11d7c5144447c4e110f23b43fc4cd0f7130435ccd10bf03a41bc12d0671534f2c178fc722a243c4a88ff03321bcd34bcb00f1f1c0007c500d0f1c0343c5000c35c0033cb000cf14042cd700ebf2c03afc5000a1bc002bcb000af1c0f27c503a8f140e5fc703a6f1c0b956702e5f4c0d93cb037381d14cde701b371cca4dbf02e3f4c97cfcb033259c0b8bd32552f2c0dc7cb028081c8c81ff01e071c8dc1bf035059c0b0203222feb8177f4c0cf2ce05b94f452c878176f4c95779606b60701caff910d79c4beb7e06b56702faa79abd43c082fa64b37cb0268ff81dc79c0b638e05116702d8a780ec4bd13221e0330ef01782f8144f4c0d6796240bcb2423e58199f1c0d434e0463d50309e389ccf140edb4e070d9702f6c7892b35c08999e044c770277ea818bf2c4c9f8a27e9df1424eb89ba73c10538e05e9a70274cb8162f5452d78e8a0bc503a2d381d165c4549ae0747d50383e5a319f140d034e0621970390c7818861c0b02fe22a0d7318ccf311cc7217cbf12ec7721cc6f338c67219c4f31fc4711dc2f023fd502efcb02efc7035fc502a9a701a997023bd5031bc722fbc50365a703b5972254d70247d503b7cb13b7c50391a703019704018f03f1871220d71300cf0220770203d5038de589f6f144deb4e077597038ac781dd61c0ceafe2234d7411a67b1e531d87e97e623477434a3799a519d47e89e879447516a178155f540cef9626f7c713dbe2806478c03e3a60191cb0155ea80f982c020c060185d30052e580a9f540547aa03e3cb01fe0b008e0300cde3005dcb015fd5020fcb005a0b008a0300c9e300c9d3015bd5020bcb017bc70167d50157cb0157c700e7c50311ff0261f71351df1501d71481cf0371af1311a701d19713618713917f52911f02e10f44110754b0ff5430f772a8cf65e8c751c8bf23587733186f32886762f84f22384764c82f2299d31289cb02fbd7350bc723abc55274ff7314f753c4c77164bf43546763542f2417c502b1f70311e70311df0291d70291cf1281e30341d302e1cb04b3d70313cb02c3c703cbf140ca9a702ea65c09a987120a35c0868cf2))) else (if i<7 then (if i<6 then 0x35e40179f5805cf9c02e7ca0173e300b9f100107a40183d000cfe30067f10033f84025bd201ade80025f48032fa00197ca00cbe30024f4802e7880173c20077ea005bf4804df9008cbd60145e500a2f2005178c028bc40165e00211f58050f9c0287ca0143e400a1f18050f8802c7c00241eb00b8f3805c79402e3c6017be20204f5805279c0293ca0149e400a4f1805278802d3c021f67e8213f58051f9c028fca0147e400a3f18051f8802cfc01274fe8022f4802d7a0016bc800b5e3005af1003578004c5fd00b3e80059f2802cf8c0167c432708f19b07f48a819a2b43d6004fd200bfd000bfca00bfc800bfc600bfc400dfc01229fd3218c5004bd200bbd000bbca00bbc800bbc600dbc001e5061244ce02f5fd1255f511c7d60197d00197ce0197ca0197c60197c404420e31610e3140fe1361fd3471f51603d600b3d2011fd0011fce011fca011fc8011fc6011fc4013fc041f8f63198d63158be33f9f24369fd1479f543d86d163bd600bbd2012bd000bbce012bca012bc8012bc6012bc4014bc001e50602e5fd1425f51405e50117d00117ce0117ca0117c41240ce32683b01747f44be3ea2771e512282688ecf5802e7a00173ce00b9e5005cf1802e78843ecf611e6fe8a3b7d514dbca284ddd0307eb0023f4802dfa0016fce00b7e5005bf2002df8c016fc400d7e00082f4805d7a00207d20173e800a1f38050f940203d20158f4004a3ca0128f2004a3c600867f40699d50116734025bd001757f406d5cd01f57140155bd0175f480417d002047f40811dd01b47540711c500546f405d3d20104f4006cbd20112f400385fd01317d40485e501117340247d00091f380247ca01707f405c1cd017ce2802e6f405f7a4023bd0017afe80fd794072b8a00b5bd017be90085f40022f94042fd20117e800427f40453ca0229d50085e80042f2802178c02e5fd0172ee80b975407cb8a00a5bd0173e90089f40024f900127c60170fe80b879407c38a01c1bd017af48042bd0008af280863d20118f40085fd20107f40041fce0107f28045bd20176f400457d20165f4003d7ce00f5f2806d3d20164f4003d3ca00f4f2003d3c60103f4003cbd000f2f3803cbca00f1f4003c7ca00f1f1815c1ad04d065415817d04a0f5803c3d000ffe5007ff1012741a889bd401fde2024df5812afa80117c6008be1022c6b40f232a0873d60409ea007cf4003e79401f3c20446d681db614021fa0010fc604e50701726b813941a856bd60545ea0092f18110c1a50e7d400d3e101306f811841a0841e5057fea0027f28166b5a0737d600fbe8007df2803ef8808f1ad0218ca82346140227a00113ca0089e3025b835139fa801cfc4049507025a83457d32a28298547b5eb2a72f5003979401cbc604c3072ac13d8124c1a2e858523f3eb1241f50058f8c09620d else 0x3214754697d600b7d400d7d20127d00127ce0127ca0127c80127c60127c461e0f640e0d660e0be6411f212d20d4471fd3501f523f1ad1361352350a522089d72d89552986d46bbd600bbd400bbd2012bd000bbce012bca012bc8012bc6012bc411e5061375fd24b5f52535e531b5ad51f4a50127d00127ce0127ca0127c42230ce31f07613e1fd2371f52421e531b1ad13013532f0a513609522204d11afd600bfd000bfce00bfca00ffc600bfc45198f660e8c6416846125a0d31f9fd4489f55539e524b9dd2159ad13893561b8a542189d51d895230bd6004bd4004bd200bbd000bbce00bbca00bbc800bbc600bbc40167d40107d20167d000c3d4010de900b6f4004f79c027bca00cbea0095f48056fa00257ca012be40095f181163ba2531d51338e68034f2001a78c00d3c412a6fa810b7944a1b9a00cfce0067e50033f100c13ca08a9dd0564ea8032f2801979000cbc60283ea0268f5005079c0283ca14d9f500327ca00c9f200327c60447f500e99dd04c6754019bca0066f20019bc60066f000f560905f5f500317c804a4f5805d3ce0174f2805d3c60174f104b0fd40173f4005cfc60173f1005cfc20392f50060bd00381f5005c7d00141f280687c603e0f5005c3c4017be10a7479404679400d3c800e9e30074f0006dc122aafd400c7e402eaf5808179c040bca0205e40122f18081788040bc002e3ea00f1f40078f8c02e7c206f1071a187b89241fc2c01fd0241049de8f58dd07a80343d001d1e400d8f180287840223c022bbea00f5f4007af9c03d7ca01ebe200bdf0810e3ea2971e50069e70034f2803e78800d3c00267048aebf50079fa0036fce0745eb00baf2805d79002ebc60175e200baf00170fac02a7ce0153e500a9f20054f8c02a7c40153e001a8f5807479c03a3ca01dbe300edf101727ac0293ce0149e500a4f2005678c0293c40149e011bb3f416dfac022fce0117e5008bf20045f8c022fc40127e008d2f500557a002abc80155e300aaf100557800825fd0173e800b9f2805cf8c02e7c445708f1b207f4cb819a5303d6229fd4017fd0017fca017fc8016fc6017fc4017fc01499fd119bd4014bd0014bca014bc8014bc6014bc006660e43c50e3394fe1565fd47f5f52a97d63207d40117d00117ce0117ca0117c80117c60117c40127c004620e4420f654d0d64460be45adf2462dfd27adf5568c6d28cfd6320fd4018fd0011fce018fca018fc8018fc6018fc4019fc004f9fd2459f5017bd0017bce017bca017bc421a4ce0525fd22b5f502f7d601d7d001d7ce01d7ca01d7c601d7c405320e2370f61451fd27f1f5486cf292267741737ac235bd4013de8009ef3804f794027bc8014de300a6f1004f7800697d4017be8019cf5005a7a00273ce0139e5019bf50059fa0026fca0137e4009bf1801d7a8016bd201) else (if i<8 then 0xb3d40143d20123ce0123ca0123c80123c60123c4013bc202e57e5154d65194be5335f202d60d52b5f544053d33b50d76950553749d44249542346d7227d600b7d400b7d200b7ce0127ca0127c80127c60127c40127c20281fe02617612b0b603520d01e1f501f10d22110511706502e3d60063d400dbce012bca00dbc800dbc600dbc402b60d5475f51245e531c54d41c50d3124a500b7d400d7d20127ce0127ca0127c40137c251d0ce52707602b20d5361f533f1e564514d13913d75310d6450a513c09551904d6313d60043d40043d200b3ce00bbca00bbc600bbc400bbc201e58e02560d01f5f50335e522e50d11744500e7d400d7ce00d7ca00f7c600d7c403720d6471f54391e55471dd22b14d64f10d2200a522c09d1323d60043d40043d200b3ce00b3ca00b3c800b3c600b3c400b3c221d83e036a0d3429f512d9e513e9dd55690d42d90521482d13dbd6006bd400dbce00dbca00dbc8012bc600dbc432642602d60d22c5f51305e51355dd1255d564e50d6555051407d60047d400b7ce00b7ca00b7c800b7c600b7c40201dd33e1d553b9cd3269c523898513097523893d23d9051348ed23289d23789532388561b86501dbc801cbc601cbc4015bc22335f50285e51255cd12f5c503357502f54d12a50d0364ed0254a512f4850147ce00c7ca00c7c400d7c21171e51241dd1271d5034ce281665d40bf29a06393d21bc86896e4140bf1da04b8a502cc4e81be2540c710a00bbca005de4002ef180177840193d400f9e90063f5003dfa4026fce0137e50022f500117a4016bca00b5e4005af180b4fac00a7ce0053e50029f18014f880501ad141fd6005fd0005fca005fc6005fc402f9ad1189a502dbd6005bd0005bce005bca005bc6005bc40265ad1175a502b4a523d7d600d7d000d7ce00d7ca00d7c600d7c40261ad1171a51171850340a52360951183d60053d00053ce0053ca0053c6005be201948344da7ac0193d40139e5009cf2004e78c0273c403270689ebf58039fa802afce0137e500abf20055f8c02afc411c5eb00aaf3805579402ebc60155e20151834478a0a26a7d600e3ea00a9f38054f9402a7c80133e300a9f100a841ac2c11d426cfd242fd600cfd4013fce013fca013fc8013fc6013fc431591e136a0d2319fd1259ad004bd4004bd200bbd000bbc800bbc600bbc412e5fd41a5ad4294a500b7d000b7ca00b7c600b7c452611e12520d53f1fd31b1ad4290cd5350a543109d866bd6004bd4004bd200bbd000bbca00bbc800bbc600bbc412560d5235fd21d5ad4164c54234a541949d51d4950047d40047d200b7d000b7ca00b7c800b7c60221060200ce0361fd0211f51301ad32a0a50233d60193d00193ce0193ca0163c6019bc433b5ee21550e4144fe6194c612d60d1475fd3535f51265ad2354a522849d42e495 else (if i<9 then 0x489d05a5eb00daf20065784042bc00412d68159634118b0a04a7d60123e800d9f20048f8c0247c002508301a86b40547a40363d001b8f1806e3c20127f4806dfc80127f0806dfc002f63b80bd9ad02866340d99850126f48049bd001b6f20049bc60136f000a15fd02f57740f95d502157140553d201e3f4805cfd00162808054bd200e2f40040bc80151f480387d00171f200387c600e0f4003c3c600f9e10113838499b2a266d7502b6a6896b4340899da044ca522a642809bf58049fa4034fca0137e100ea8384d10bc05c9fd2324d68aba65489114a028bd60125e900daf4006979426e7d201b3e500d9f0808cf8004a20611d0f701005948807ac0823d201abe81145f2806af840357c02408b291945348e214a0473d20139e8009cf2805e78003ed650216a681134b448194a036c8501e7e9002bf40015f9400afc203d5eb00d2f2806d784036bc00473eb00d9f0806cf804721ad25d0ca8908f5806c7a00343ca01baf0004a7d201b9f080727c012f83b88ba1ad24b865404a3d201b8f4006a3ca01c8f000e5dfd02a77940a9dc501e6f4805d60201e5f4805d7d001f4f4805d3d00164f28058fd00173f2805cfc204027f41bc9dd06527541949cd16e27140687d204007f41d01f506397941925cd16d971406a3d20207f48045fd00156808081bd20116f40045bce06657f418d5e506e57741915d506e571405d3d2015380805cfd20073f40060bd200f2f4003cbca015180805c7d20071f4001c7ca0101f200cc1e20420f5802c3d400e0f480143ca005fc8005fc6005fc4005fc20279a502ebd600bbd4014bd2005bce005bca005bc8005bc6005bc4005bc203a54d03750d0394a502f7d600b7d40147d20057ce0057ca0057c60057c40057c201c1da0351a501b18d03a14d04a10d0340a503509d02fbd6013bd401cbd200dbce00dbca005bc800dbc600dbc400dbc202c5a502d58503c54d03153d03050d03550502c4a502c49d0314950457d600b7d40147d20057ce0057ca0057c80057c60057c40057c202f1a503219503218d03418502c17d047d0d03ad0502dfd6014fd4005fce005fca005fc8005fc6005fc402e9a602fa0d004bd4004bd200bbc800bbc600bbc400bbc202b60d42c54d41450d4234a50047d40047d200b7ca00b7c600b7c400b7c212e1a603f20d31c14d32010d6200cd3128a524a89d237bd6004bd4004bd200bbca00bbc800bbc600bbc400bbc202d60d32954d32653d52350d64650542b4c53204a532549d22a4950047d40047d200b7ca00b7c800b7c600b7c22281a603520d41c10d32510531a0bd0373d60043d400bbca00bbc800bbc600bbc401d58e0204ce02b60d0255f50237d60127d40157d201b7ce0197ca00f7c60127c40137c203d2060341ee0251863240c603f20d2191f512f10d41b09d1493d600 else 0xfc403d4d2822a65413d30a00cbce0065e50032f180197880665a501b2ca80a9f38054f9402a7c60153e229b0694c9c32ae6a1850151e700a8f2805478c02a3c400c9f400323d000c8f38031fd000c7f38031fca00c6f40031bce00c6f28031bc612a56144d157d00e5f180397c40164f180593c412a37b850cd651403f58034fd00153f18034fc413c25944e493d1282254cb0bd600f2f4003cbc600f2f100187c60061f1010818500e9f1803a7c415986140e217d00d8f180363c412a7614039fc600d7f1001d7d00074f4001d3c613936940b8d9512735f44a8d0d00e3f38038fca00e3f10040bce0102f28040bc4139159401c7d00071f2801c7c403c07b807c16503305744dc3d600d0f400383ce015de5006ef1051eaca06755d049aa681d52940bafac02b7d0008be700adf2803ef8800d3ce0069e50034f10019f9400cfc40414d2820a65402d79c016bca00b5e20291694538b2a08257d0123e70091f28048f880601a50300ca8098f3804c7940263c40079f4001e3d00078f3801dfd00077f3801dfca02d66544bd9851306434039bca00e6f1803d7ca00f5f180c11652204f580413d000f4f280413c60513594128d4d03a32940d4fd60163f40058fca00f3f18010bca0042f180d45950041f280107c613706540f818500c8f280323c60217654031fca00c7f184999951306614035bca00c6f1801d3d00073f40000fca019283809497d02f25d40c08ed033221402cbd60122f48048bc40132f0807860e02f17f409c5ad02615f40d853500b1f5802c7d20121f400487c40340f480443c4011be1008df000d640c0731650309eb01d4f4804e7a00293c40139e1009cf000d5c0c038dee0396b281a34d4145fac03cfd20197e800cbf10065f8006896504149a811a4b406d10a034bd20055e8002af1001578407a7d60123e20091f08048f800681c2047ed6824ff5806bfa0025fc201afe001c66b40df2fa05bbd6012de80096f1004b7800734ee027ad6813d5f40d2a6a0177d2012be80095f1004ef800551fd02a8e6816c714055fa401ca020155e9007af40054fa401e7d000f3e20078f400207880203c2024a0e01898d03098502897502e93d02e9050238ed04089d02a89502288500bbd6012bd201bbc8012bc6013bc202260e32f43e02f5fd12f5ad01958d13358503749d13249500b7d60127d20127d001b7c80127c604b3d20113c80113c60113c20119e00183594151fa4030fd00187e101328184913dc0849650334a2815a2740ad7ac09abd20135e8009af2005178c026bc20135e00259594108a8a08853d02a24e81e925408cfa40267d00133e40099f1804cf8006a16502809e81104b44d012a03608501abe9002df40016f8c00b7c20359eb00dcf2004a78c0253c20129e001736b40edfac034fd001a7e300d3f080c93b406)))) else (if i<15 then (if i<12 then (if i<11 then 0x36f3806de500ebc601f9e200dcf08941fac060fd20057e7002bf28015f8c00afc40057e1099a5944e57ac270bd20055e8002af2801578c00abc21412f90a715944f0fac0747d200d3e80029f38034f9401a7c600d3e20069f084f42ca07c15d0490a691882945807ac06e3d200e9e80074f3803a79401d3c600e9e20074f080b5fac470fd40077e7008bf28045f8c020fc40117e101da6b41697a800ebd00075e3003af08024b9409e5ad05d2ca8a49f5893cfa80247d00073e70091f28048f8c0107c40123e100787280d435a27a1a5036995066985058bd6147bd4019bd000ebce019bca019bc600fbc4019bc21194660445ad12e5a50375950345850177d400f7d000f7ce00f7ca00f7c60107c402e1ad23a1a505119503a16500c3d642f3d40073d20183d00173ce0173ca00d3c6016fc400efc242f9ad54f9a544e99514798533e96500cbd6855bd4007bd2016bd0011bce00dbca016bc6016bc400ebc22264ee31a4660315ad11a5a513659512558501f7d40167d00167ce0167ca0167c601d7c432e02611d1e513316503115d135ca6895e4f44a714a64d89500cdeb0096f500337a0019bce00cde50066f184dabfa2895f513baf291fd75449eb8a0473d401e7ea0083f480797a8020bd200c5e80101828038c0401c5ca01e3ea0081f48030fa00187ce02010500288080787a80203d200c9e80064f38032794030fd200c7e80063f28031f8c03cbd400c5e80062f38031794018bc600c5e201291780a4b4a0625950292c281495f4490a1a0387d60063e70031f28018f8c00c7c421f02f09d07f44cc35a23a19521b0c288d85f44b026a4380d58378c51318a5643895122bd601abd001abca01abc601abc40296060225ee01f5ad1325a502756502b55d04254d12e53d0285350204a552049522746500c7d60147d000c7ce0147ca00c7c600c7c402005e0331fd1221f50331ad11d1a502516502995d04093502f8a532a895029bd601cbd001cbce01cbca01cbc601cbc421c46e23045e02b5fd1255f512d5e502a5ad11d5a511d57d02556503353503f4a56334950167d60247d00247ce0247ca0247c60247c422206612305e02b1fd2251f512dde5125dd5036dad12ada511fd85035d65039d5d035d4d030d3d035ca553dc9511dfd6017fd0017fce017fca017fc6016fc4029bd6005bce005bca005bc6005bc40555651317d600c7d000c7ca00c7c600c7c405c16503d15d01f3d60053d00059e7002cf2801678c00b3c40666b282ab574149a9a070ca523d7eb00abf40055f9c02afca0157e300abf101712ca07a95d0564a682b24f40b914a66889511c5eb002af4001579c00abca0055e3002af10018f9c00c7ca0063e30031f1001879400c3c6006be201ec69401a79c00d3ca0069e30034f10105b4a08ad9500d7e7006bf28035f8c01a else 0xc401abc211346e0445ad02b5a50345950197d40177d00177ce0177ca0187c60177c402e1ad2311a503a1650133d611b3d40173d2017fd0017fce01efca016fc6017fc4017fc24479a501dbd201cbce01cbc401cbc26354ee21f46e0315ad1255a523659502e53511b7d401d7d001d7ce01d7ca01d7c601d7c40351ee0280ee0251e514116502315d14214d01d1351250a50143d601a8f500523d00148f380523ca0148f101b1bd401f5f500617d201f4f500613d20154f40084e0a0163808038dd201f3f50060fd20153f40054fce01f2f48050bd00142f38050bca015182803460201f1f500607d20151f400547ce0151f280507c601f0f500543d0015fce015fca014fc6015fc4004bca004bc8004bc6004bc00486060245ee0385b60095ca0205ad34d56502655d14654d0355451334a502c49d02642d00d7d600b7d40207d20107d00177ce00c7ca0157c80157c60187c40137c012e20205f3d6011fce011fca011fc8011fc6011fc4011fc014e965027bd2011bd0011bca011bc8011bc6011bc003f6062406022375f20345652447d60317d20197d00117ce0197ca0197c80197c60197c40197c004216504315d03114d0270a50133d00133ce0139e5009cf10111c0c2a2d6503d6ae82635340a5a8a082ca502264e8103f580c5fa4022fd00117e7008bf28045f90022fc60117e2008bf001717a8026bce0135e5009af2004d78c02abc40135e00091f20048f8c0247c00430d282a0f5004c79c0263ca0139e4009cf180567880273c001d6d28143654175fa802afce0157e500abf1805df8827a9a54554ca82aaf5006979c034bca0135e400d2f18071788034bc00272d28219f5006cf9c01e7ca0173e40079f18060f8802e7c00230d281386540bc7a80163ce00b8f2802e3c600b8f10891da5439765410dfd401b7f3803dfca0177f20041fc60187f1005dfc00445f500353d401e3f48044fd00182828044a020152f50078bd20072f40030bce0151f5003c7d00081f380207ca01808280442020150f500783d20070f400303ce000fca009fc8017bd2010bd0009bca009bc8009bc60157d400e7d00077ce0077ca0077c600c7c412506613519512d18503415d03914d03813d02a12d25010d0270ed0270a523e09502808513e0150133d62383d400c3d201b3ce01b3ca01b3c601cbc401bbc212a4661305fd1225ad12a58512456512453d11d52d13f4d58494c512d4b524e4a5b4249512c4852224150137d600c7d411d7d201b7d001b7ca01b7c601b7c20452061180d61221f211d1ad1281a511f16503f14d12a13d0420a582d92aa371b402feb005fd4015fa4017f4002fe7005fca00bf8c017f090cc3712286612d3fa2707d44f4d691a1a51372ca0685740fca680f12d24314b0722548804281382512202a026f5804dea00f3d201b7a00) else (if i<13 then 0x8ff500577a802bbd2015bea00adf4804efa003120a01190100acf500567a400f3d000f9e700abf50055fa401efd00087e70043f280557a802abd20105e8004af3802579402a7d40153e90081f40024f940127c800a3e300a8f500547a401c3d000e9e70074f2803a7900273c60139e200abf50039fa000efce0077e50063f18031f8801efc205a5ea005af3802d794020bc800f5e3005af1002d78006e5a503a3ea0099f3804cf940207c80163e30069f1003cf8001c19511907a80800b40187a800c3ce006fca00efc8014fc6006fc400ffc01258ee2369fd02c9f51409e513e9ad3439a504c9951318a5008bd0014bce014bca1396020317d600d7ce00d7ca00d7c80117c600d7c400d7c01252022341ca5801652433d60393d20203d00203ca0203c80209e300c4f1008278008ee060406f709e38080c1aca066d5d1447eb01c3f48045fa0022fce0117e5008bf20045f8c022fc40117e002aa5941612ba0628a50115e8008af38045794022bc40643ea0079f3803cf9401e7c80143e30081f1005cf800aa3d40129e50094f2005278c0273c401c9e00253694171fa8024fce0127e50093f20051f8c026fc40127e001ba69408132a08abd40205e70102f280817880c45a50272ca82d1634144fa801e7ce00f3e50079f20050f8c0207c400f3e001786941347a80323ce019fca021fc8019fc6019fc4021fc002e9a501f995046bd4016bce016bca016bc40556060405b602159e3304f623656511b55d13b54d0275451304a502149d0147d60127d40187d20127d00127ce0127ca0127c80127c40127c001f2020611fd03defa82b7794537b9a081dbd03adea00a5f500727a801f3d200e9e8009b828031c04038fd400f7e90073f4001df9c038bd40165e8007af3803d79402e7d20163e80079f3803cf9402620a01610100a07480707a801e3d200e1e80038f3801c7940203c8009fc601cbd4015bd000ebce00ebca017bc600ebc402646e14759504a54d04053503b52d15a50d1304ed0274a533549502848512742501e7d60207d401f7d201e7ce01e7ca0257c601e7c401e7c223313533f0b543a09532008502a0250143d4014fd2023fc6024fc4024fc232b9ee41790e13ba0201d9ad01f9a501696500bbd600bbd4015bd200bbd000bbce00bbca00bbc400bbc20347d602c7d200e7ce00e7ca00e7c600e7c400e7c21523d602d3d200e3d000e3ca00e3c600e3c400e3c21458b2922cf580da7a401d3d000e9e70074f2803a78c01d3c400e9e1016bf580d1fa8032fce0197e500c3f18065f88032fc203c5eb01a2f5006978c038bc401c5e100497480fcb5a2947d60343ea00d1f40068f9c0347ca0103e300d1f10068f8446a06e0099d20399c20499ad1489a515b99504b97d03d8a5334895050bd6040bd4022bd0022bce022bca018bc6022b else (if i<14 then 0x537d401b7d00117ce0107ca01b7c601b7c40137c20561ad022da501bfd4010fd0010fce010fca010fc6010fc4015bd2015bc4015bc23295ad4335a532f56500b7d60457d400f7d200f7d000f7ce00e7ca00f7c600f7c400f7c25240ee0391ad1231a503713501b3d40153d00153ce0153ca0153c60153c4028ef700df3b84f796c077d6502be9e81574d485b92a019fd6012fea0067f40033f9c019fc600cfe2039df5007e7a80213d20107e9006bf4005d7a4018bd0021305002980807cfa80207d200d3e80069f38030f9402a20a00510100f8f500407a401a3d000d9f380327ca00d9f1807e3d400d8f400363ce00c8f280363c600d8f10d61d650717f4804dfd00137f2804dfc40137f080b1bd60176f3805dbca0176f1005dbc20405f5805d7c40175f0805cfd20172f4804cbd001c180805c7d20131f400307ce01c080805c3d2013de80066f380337940277d0013be7009df2804ef8864d16542d8a699742940be7a402f3d00179e500bcf08199fa4048fce0247e50123f10091f8466e9650535e9009af4004d794026bc202e3eb1229f5005cf9c02e7ca0173e300b9f1005cf840b21ad02edea00bef4005f78c02fbc2125b0522556951b2fac6bd7d4017be800bdf3805ef9402f7c6017be200bdf08d1634a0093d63519ea0024f480327a00193ce00c9e50064f180327880193c21316fe91837d40e9bca65cdc50385ea00f9f5005cfa403e3d4017fe90097f4004f41403fa0201fdea00bef4803f7a001fbce017be900a5f40052f9c0297ca0179e90094f4002e79402b3c601f7ea00b3f40059f9c02cfca0197e300b3f1005d79402ebc60175e20091f38048f940247c40610d280b8f3805c79402e3c6017fe2009ef3804f794027bc4035aae807d29405afa002d7ce016be500b5f10021fa0010fce0075e80002f38001794014bc60312ed0a217085b4fac0667d40133e80099f3804cf940307c80133e30099f1002cf840267c003e10302686d80003a464e19502d95d3359453228fd31b89d004bd6004bd4339bd200dbce00dbca00dbc800dbc600dbc200dbc005060604c7d624a7d20117ce0117ca0117c80117c60117c40117c20117c005e2061252022341f234f1652573d605b3d20193d00113ce0193ca0199e400ccf180667880333c20199e002f383453dfac092fd40137e7009bf2804df90028fc60147e2009bf0804df800789ad0525ea009af4004d790028bc60135e1009af0013cc140d460d3543eb0251f5004cf900287c40133e10099f004c035a8b819504e9ea00acf4005679c02b3ca0169e200acf080f1fa8008fd200c7e40063f10031f8401afc01244d6a1f26540a17a8008bd200b5e8005af3802d794016bc400b5e100918080d0bfa0565f502a2f281997140e4b7a04620d12a0fe8a707941243aa09a1cd121ee28a else 0xbbca01cbc801cbc601bbc401cbc201cbc074b4d604f60d4435ad57d5a532a7d65967d401c7d00147ce01c7ca01c7c601c7c401c7c211b20a33e1da06a20d6761a532809d372fd658efd401afce01cfc8022fc4023fc2023fc03259065218d642a9ad3469a535ebd400cbd2013bd000bbce013bca013bc6013bc4013bc24645a557e7d400c7d200c7ce0147c80147c40147c20157c00542061381ee0501b63130fe12d20222cdca22ddad32ed6544dd45430c9d004fd6004fd403afd200cfd000cfce00cfc800cfc600dfc400cfc200cfc02119f6037a022189fd2229f535f9d53369c51439bd03f60d0325fd0405e50335dd0435d503b5cd12a5c51527d40153d401d3d200ab0480fdf50056fa40237d00159ea00ecf480667a002afd401d7e900bbf40021f9c020fca01350500a28080153c402abd401d5e9007af4003579c02abca0115e400a9f50074fa40327d00113e50089f20048f8c02a3d401d1e900b0f4003879c02c3ca0169e400b4f1805a78802afd40167e8003bf3803df9401efc600f7e200bbf081517a8008bce0085e50022f2001178c008bc40045e001e96940f0fa801e7ce0153e50049f20030f8c0187c40083e008b83d40400ca00c3d40061e700a0f2801879000c3c60069e20034f004919dc446dfd3416ea913b7344b1b5a28ad8523b6be917b2548d98ca010fd00147e300a3f104fd404040bd600d5e7008af2803579001abc600d5e2006af00094aca0627d60323e90089f40044f900227c60113e20089f001587a80243ce013be5003df2001ef8c00f7c4010be0020cf5004a7900253c601b9e001036940b9fa8028fce0147e500a3f18051f8847c9a50465ea00e2f38069794014bc80115e3008af1006978003e5a50333ea0089f38044f940227c60113e221606940e87a80243ce012bca01abc8012bc6012bc401abc00446060415b602459e11d4f62144be2155f22195a501256521154543153d21949d50f49500d7d600b7d40107d200b7d000b7ce00b7c800b7c600b7c400b7c001a20205e1fd04f1f50701d50671cd04f1bd035fea006ef50056fa801f7d2007be800bcf480427a002afd400f7e80043f38045f94036a0a00c50100aaf5003d7a400ebd00005e7004af2802579002660a00c3010069788054fa801e7d20073e80001f38024f940127c80003e300a8f500387a000e3ce010fca007fc6007fc405293d04893503a92d02290d1398ed02a8a522b89503188502a85d00dbd602bbd401fbd2016bce01dbca016bc6016bc4016bc20467d60397d20057ce0057ca0057c60057c40057c201e3d20053d00053c60053c40053c2037fd6047fd4009fce010fca012fc6012fc4012fc200f9e20499ad163bd603bbd401abd0010bce00fbca01abc601abc401abc20125e21415c205a5ad14e5a50314a533c49515a7d6))) else (if i<17 then (if i<16 then 0xa01508080783d40220f480383d00110f280403c80229e9009cf4004e7940333c80139e300f3f50055fa0030fca00e7e300c3f104a53840b09ad54c462a2022544b17ac284bd40105e80082f2804178c010bc20392d681a14d410c94ac864950163eb00d1f50050fa00287ca0143e300a1f11d3418a0163d6451dea0086f480437a0021bca010de30086f100437848534ee141ad689754d4c7a9aae5d4c5022bea00adf40056f9402b7c6015be20083808089fa403ebd40225e9006af4003578c03e7d400d3e80069f28034f8c01a7c404a0fd01b87681407ac2ac3d400bbd0013bce013bca018bc8013bc6013bc4013bc2013bc002f60213d5fa0005ba0355ad13e5a50335650177d614d7d400b7d200d7d000c7ce0177ca0107c80187c600c7c400c7c200d7c00352060381b603919e00b3d60043d40113d200b3ce00bfc800bfc600bfc4015fc200bfc002ea060379b613e99e24b94522389d00bbd6004bd4212bd200bbce00bbca00bbc800bbc4015bc200bbc013c4c63365cd4275c512c5a513357d03c57512a56d00c7ce00c7c400c7c200d7c003b2062553d6030fd2011fce011fca011fc8011fc6011fc4011fc2011fc011ba02021965250bd605dbd2011bd0011bc8011bc6011bc4011bc2011bc004960d0217d60597d400a7ce0147ca0167c80147c600a7c400a7c20127c024510e1341ad0623d40143d0014be700a5f28052f880297c221a88708fc6b48aa34a26f3d400b9e9008cf4004679c0233ca0119e2008cf08519c044d8dfd23c6faa65b73497db8a2b2dbd03550681527f40fd3ca07c9d50394e689127145617a802a7d40153e900a8f500547a400e3d0015bea00adf48042fa002b3d40159e9007cf4002279c0113ca0157ea00abf48041fa0000fce00a7e5009a82803140400a9e20155ea00aaf4801d7a0000bce0005e5004af2000178c02a7d40153e90071f40038f9c01c7ca00e3e40071f18038f8802a3d400ebd0007bce007bca007bc6007bc400fbc20545f204a5c20507d60397d40147d00187ce0117ca0147c80147c600f7c400c7c20147c00362060471b631c0d63142021311e25371456690fd52609d32906d0043d60043d411d3d200d3ce00d3ca00dfc800dfc600dfc200dfc00469b631b965004bd4026bd200cbd000cbc800cbc600cbc200cbc00335b641a56574154584a53d51a49d62a49521c46d0047d41297d200c7d000c7c800c7c600c7c200c7c003b1b63220f604b1b523b1ad23218d23798523297512796d33696576994587393d55289d65989522a86d21bbd413cbd200ebd000ebc800ebc600ebc200ebc004f6063456022425f225b7d60327d20117ce0197ca0197c80197c60197c40197c20197c033a16521a3d605f3d20113d0011fc8011fc6011fc2011fc01209e204fa0d033bd6335bd4013bce01 else 0xf0889c40401a3d600b1e70058f2802c7900163c600b9f1002e7c000c7808025fce0086f38021bca00c58080257ce0095f280257c800c48080253ce0094f280253c80094f1801cfce0073f2801cfc60073f10140bd40082f38020bca0082f18020bc412f14341387d400f1f3803c7ca00f1f1803c7c413d043415c3d4010be70085f28042f8c0217c41368868314f5004679c0233ca0119e3008cf1002dfac016fd401f7e9005bf3802df94016fc600b7e2007bf080497a8018bce00c5e50062f180317880747d400a3e700b9f28034f8c01a7c422a0868208f5005879c01e3ca0128f1805a3c411e74340fdfd40157f38055fca0157f18055fc40204f500453d2026382803ce020203f50044fd200e3f38098a0a0052808080bd40112f48038bce00e2f2806860a00518080807d40111f480387ce00e1f280387c60200f500383ce00e0f280383c600e8f1009dfd60157f20055fc60157f10055fc20157f000f99fd02d67740b19d502c673448d9c501c5f480713d20124f40068e0201c3f48048fd000b3f20070bd20142f40050bc80142f180707d20121f400487c80121f180487c40120f4002c3c60150f1004c3c202baf5805ebca017af1805ebc4017af0914a7d60179f1005e7c20048f480323c400c8f08075bd201d5f4805d7d001d4f480553d00154f28074fd20153f40054fca0163f1804cbd00132f28058bc60132f105207d40041f4802c7d000b1f2802c7c400b1f0890c1fd249cf281fe75450f39a4699c52bbdea00bdf5005efa40177d00179e90094f2805dfa802efd200e7e80073f28039f9001cfc40175ea0072f4004579400ebc60115e2007af08548fac0287ca0143e400a1f18050f840287c02531eb00a0f400507900283c6014be100a5f004aa7ac02d3d00169e500b4f1805a784264dda12864e92cbf5806dfa0036fca0147e400dbf1806df84036fc000b5eb006af480497a0024bc80125e30092f0804d78044a5060043e90059f4002cf940167c600b3e109405140107ac0083d200c8f400323ca00c8f200323c600c8f080363c013b77f44cdde51357774121dd51277714071bd201c5f480597d001c4f480493d00154f28068e0201c3f48048fd00153f2802cfc801c2f48048bd00122f28048bc80122f180487d00151f2802c7c60131f080503d6014bea00f5f2807af9003d7c601ebe200f5f004be4040733d60119e5008cf2004678c0233c40119e0038bf50061f94030fc80187e300c3f10061f80058bd40155e400aaf1805578802abc00663ea00b9f2805cf8c02e7c405f1ea00e0f280547900383c601c9f100727c001d8f5007a3c80168f1806e3c401e8f000c9fd400b7f2802dfc600b7f10119bd40136f2806dbc80136f18061bc401b6f001b53d401e3f50078bd40222f48048bd001e1f500587d00191f2806820) else (if i<18 then 0x25e5ac12f2d209796504a0b1826257401f2b601408300843980581ac02ce6900bf994034e6300af974028e5b001f94c007e29008b20022e98200f66002187820915e0004068200d9a0000848280392020084f38020fce0083f28020a0a00e2808020bce0082f28020bc800818280146020081f380207ca0081f200207c60080f380203ca008ef18023bc4008cf28022e0a005b808022fca008bf20022bca008af20022bc60159f280567c60159f10025bce0076f2802160a00558080257ce0075f280257c800848280152020094f3801d3ca0094f200013c60153f38044fca0133f1804cfc40081f380203ce008cf28022fce008bf28022fc600898280366020089f380223ce0088f2803dfce00f7f28021a0a00d6808021bce0086f28021bc800f6f1806d7ce01b5f280617c601b5f10020e0a0143808034fce00d2f38038bca008182805060200d1f380187ca00f1f200343ca00dcf200373c6018bf38062fca018bf1805efc40069f3801a3ce0068f28019fce0067f28019fc60066f20019bc60066f10019bc003a483410d1e503847741211d5048473406d3d400e3f48054bd20151f500387d20081f380587ca013082803020200c07880543d400efe900bff3805bf94013fc8013d0500668080577a801dbd2017de700b6f28027790013bc600dbea006df38076f9401b7c800dbe3006df100567a800f3ce0079e5003cf1801e78801d3c20277ea00caf4807cc040327d20113e700a88080647a40223ce0119f280663d40158f380563ca0198f180563c400d7f38035fca00d7f10035fc00116f38045bca0116f100697ce01a5f280697c404c38340d0df513a37940d8dd513437340bcfd40152f50038bd2013182803060200c17480547d400e1f480247ce00e0f480203ce008de500adf4804ef9c0277ca01390500648080567a801d3d20099e7004cf2802679002d3c600d7ea006bf38035f9401afc801d7e3006bf100557a800ebce0075e5003af1801d78801cbc20623ea0071f38038f9401c7c800e3e300b1f10038f808561e5222ddd12ddc502dda522cd95131d8d136d75248d6d137d1d004fce004fca004fc8004fc2004fc0045bd400abc8014bc6014bc004a7d40147ce0147ca0147c60147c40352060451b633814531c09d0043d60043d44383d200c3ce00c3ca00c3c800cde3006ef10043784019bc0030bea00b5f3805af9402d7c6016be201dc7b814a40407b1f503d8f28a6c7541a638a0931bd02d706928b794921bba086dd503e6e6929bf500557a802abd20133050061808014b9402a7d40153e90049f380547a802a3d2008be70045f2804e4140192020058e500acf500567a40133ce0099e5004cf20055fa4012fca0097e4009bf180557a801cbce00e5e50072f2003978c01cbc40153ea0039f3801cf9400e7c60073e20079 else (if i<19 then 0xa0803a7db40377a0812f69b412e699c231694421a689c32d65b442f6544418649c05955b403251b40734db41234e0006349b405845b405b3608032260025a220c12f220004b15b403911b40350e002300a0c14505b4029020402801ec02101b4000ab2804948000c65041194a0004a83680450720121eda0183d9c04b7368060e67014dada01d359c0396338084b8300dd6d2019aa0c1223b584d478204d0d060a099b432d333805a56d0098ace0a091b422c234824846700c86ce1a305b43320b38258165011030401e81b402adb38079b8200c72da01b659c000cb2823b87f04770fa00ee1e401dc3b823b86f04e30da099e19c000c2f801580b010ad04010d60813a5c18290a830125502024220404f3c0825e75904fcd06021120403c1c08068357011c30218d846c047040806007b00ec0a601100a4047aa04624a5ec03da204225a02405691b40478db405089b4040820c0337e0c033760c22f6e0c02f69b433465b41445e0c35a5db413555b4141220c14a1e0c04a1e0413d1a0c0411a04050120401711ac02611641460e0c13d0a0c44309a41400a0813205a414f020c04a020444c01ec14c8c10090f8100a5ef60903d9403d7a98034f290475e32099be08051740807ed810c91af600e35840256a78440d250511b0401badec02d5bb8000b65000163229729f423353d8000a61004d40e09ea2082353c1008068300f0b0601e120c03c1c1827628304e4306099020c137b41826f58304ba906091c20c122830826cf8308adebe11eba0c000729800ee2900b57060162da40355418032a6500c930601625ac11f4af804488308b0f061111da40003a7802072500f8d060151994007327802a62500c87060188a0c02b135826018304a42ca010020c0009a6805ed8300f1b0201035ac0206af8056c8300ed90200c317403462c806ac8000d97060142dac03f5ad8040a8300c5502012297403f4c1807096d00d52ce01b257c03a4ad805888300990ba016216c021340007236300c04c6019860403a0c0007c08300bc0d6019018c12cec201ae8300fb4080219ac01ccc600ce5d00df2c8067a0002db06017d6b0096b1806b56c03a902018c7b00be36805f19c031702017b510065938090e0002050602128100d53d803498c01f4c200e25d04f4c180785b40352ce09716104e0ad803c20c01f963007e57402c95b009a20c00884f006a09403468000e55ac03046b00bd1a40304650070dac01c3690070d9401c3630074d7423a28311609ac45226908e899403218300bc60401916b00705a401c165007058c01b15d00c856413118000b020c32a06b0c881a422e8ca195463048e2e804f16c02b70601838100d5bd8448dac2206d2012b650881b18442d7403b70002228300f13686b29ac3504d202226708cd32869298c1584ba02425b00acc18 else 0x452348681cb9dad03c7335a0608c5940d1189a80ca30a51194612a0568cf580a119ea011233d202a150dc22e007b8834008700d000fe1345f0d2817af85944857c14a632be09501d5f1eb0942f8f500857c7a404a80cff0284027f8171bb0bc070d905e24c4b06f1252567f89492b1bcc90948de24c4746f023238378189123fc4a48805e25c4386f11f10cd380f86c35c1182999e07c148d701e0566bc1d80d19cca4048de8260086f62b0027f99100043c126334100911960801eb20802fae0802aa20802c9e0801e9608027920804469b41356a0004d65b404c61b413062002255e0012a560023152001334db406341b4036420005a3db405939b4231360021a2600027220004d1db40341e0005c19b432f1a0004115b4126160043115d006011b412c0e0003c01b4041d6d11eb4fc167d82011b60003cc6d01269dc038a6d000299434397d08fe5e44389770ce25c423f96f04f65b4000961002a4fc04688000e9e0823b7800129a0802b68004e15b411b5590d051b441b4590cf8db431835905049b411c25908f05b412c1590d5c1b443f8eb2326473d050e336823119642398ada10e4559053a236843b1164421887a09a40781491ba18038d5fc01f6a76099b33b04a964000649e000324b0401e226d04ccdc0825e6e00142350011d997b04e0cc00260620412730f6097168000c85b6806c2d5c12304f608f822d14c003e884c01ec220e1280a786d0172eda0155e00066b3682a366701b6ada0a4559c02cac000c946d00b28ce09dd20023f9b38262a6d04a54ce19d26043344bd86b2977015d2da129259c0004af808c8800e2cd040941a00066236828448000e86da03689b412f14000fa16d00d830003101b422efc0008d9820cced020175a00035ac00065480013a50019846043278bd827906d00a1f021113dec0457b68432f610865e361a93da021b73e809ae8010fd904018320005a536807296d00c12ce02aa1b4038433809676d00e8ece00b999c03a141067616d10b82ce1aa81b4544819c02c82081397db42347d9c13b71b432c719c22e6db44246d9c0256e0814669b4235699c0226a0802665b402e659c000658402261dc02f61b402d619c000617c00060642455a0802a560813b320c0532a0405b2604062220413821640440e0403009ec0510604051020432f01ec139c13c431c094050be040228e080328)))))

def seedRules11 (i : Nat) : Nat := (if i<14 then (if i<7 then (if i<3 then (if i<1 then 0x78d28f343adb1e901e8eb41a3db9af7328f2c23db9af294225cf0ddec8fbaf2accd918893d5b7bee766ef647dd115ae766c3646212ab5cead6ccd86ef7baad6c0dd98ed579560906ecc709295827663b54449ead2a9d6ccd95def49f6ccddef7656d99b0deecadb334aff623358bf00fc466d3fd9a13eadd735eb469e6c407e2234ff7436203f119e8b4a4ffec406b75cd7b9ad3cb0b75cd7ad5088ad62fc03d1a1eebeb735ee6567974c3f5b9af4a5611d30bf5cd7b99584e1e1b4d91bf6f3cb8766d364623f7cb904f43f8766c364623f7cb950f66c369b2bcad81aed1da9e7904c35da3b509cb950f0906c76a09c4e52a9d6ccda6f7656d99b0deeef5b04ecd86f76da54c6cd2a5ba19ac5fba7c466d3c84fa8f57ad7279b1e936f888d343630de9f119e8b496e20f57b9ad62ef2c23d5eb543184b17ee9d1a1ff51ea65ee674f2c3f51eaf0919d308f57b9bd7ba12c5fbc74442ddc6c5fbc467a2d25b84e27d5d932f735a7961fabb2f5a8c230bb2f735af5e224b0fd532f733889ad59f51edccd5a42ca1d6acd68f6e7cd68458c23db9daa1d3ea3db9f33a59a25b7e2db8d7566b7eb73e6b422c61fabb5ced4ad185f9dae7cd6b476d6f2eb75ab3ea3de6b4858c3f51edae5d1847bcd6b67f4d9d6b0fd7a7679ad69f51edcd78d28f342a5741a3db9af7328f2c23db9af5088a295dfabb5cd7b9947961fabb5cd7a508a30bf3b5cd7b99413954aefd47bb2bdcca3cb0fd47abdca228c23d5ee6d9f11461faf4ecaf7308a7d47b73e6519987ea3db9ca53d3f28cba5464035191b78d36c773094bf05b9358c77308aad2d532a7e8ee611bad2d705b8071dcc22ab563bcf230af261399fad6ce7aa3615e76b4fc2734843ec533b5ae610878625c530fd5378f309b3b4b3e61136aef3df09ccec9ad5889cced69309cced6937889cced69306f471b85f4ca824373096b7b84bb59532af1e612d58e8e37cd6840dacd87ebd3cc25a59b0fd47be3cd68479f1a7d4cdd8489cd6951b78d4cddbb09cd69560a6b962ec22ae6b4b54d71d9f8455cd68dbc69f44e6b4b3c16e4d631c22ae6b4b5c14dd31c2735a54c2c3c7aabf7eb82496b9966c32bc7b7d7ed9e612d48b361fadc05d3b22735a5989cd6967cc25a59f309b36ae73096b66e74f309b36ae68f1de2fd1af6ecaae496b98421eebbb5da16e2ab1e612d60eed0b7153f73096b0776bb5c5403e612d30fd47bcc25a59bb59766e2ab1e612d60eedd9b8aba7984b46de35d8dbcc25a09f829ae58bb2ae612d1b78d3eecf3096827e0b75cb1d9e65425a5ab75cd97ee65425a5ae0dce9d9e65425a9e251996c5f2596f66de4bb596412af658965bd97a4a03ccfb2d5a4a24763bf6ef5881501d17d9681545f9661fadcd79ba3be61157d47abd63b2ab984b4c3f5b9f4c72ae612d30fd47a038e55cc25a else (if i<2 then 0xf86dcbfedb9362a8b16adc9ae08a50a9829b1559628b5c14d7250963516a9ae628963e5d6fc36e5ff782dd8aa2c5ae0b75c114e55ae35bae62894b5145ae0dcc513fbc16e4d294e0b7c29829b178782df193f4ead29d3cd9dbeac4ae9e6c5678eb62b3c75b3fa339b1de8c0727f67d380e73f6598f8df4a5763fe1b0efc95bbfe1b14d5be3a36565ae0a6b824a752b36f1add882bf2c6fa45395af7f0d96b8370481e55ae36e62d2e044e15ae0dcc5129693829a540f09b16078e1c14d8a93c60e2c0f0315a53f8e8db05362ba58e3eb5c14d70494e9c7d6a9ae62888bbafe8c5ae0a6b98a21f3a71f5ae0dcc510b775829b15d2cbed8ffbb01fd7dd92a4fa784bb579eafa4a93e9e46b8f19765c78cbb126e3c71d971e38ecb919e32ecb892f19765f6339b1da2fe8ce6c7a8fbb65e5fc0763fa453f8e8db05bae62ba58b5c16eb8246745336f1addff711c6fbe914e571b13e1b60dcc5120562d70606c772308b5c58145ec7704495ae0e2dc11c705bb15278c1c512078185375f0db05bae62ba58cbd6b82dd7048ce997ad5bb1517b823a65eb5c13ee2dc11d5f6316b82dd7048ceb05bb15d2cf9add305b931a81f943adf9add1b9362c0fc5ab72681d2874c16e4d8aebe7f72da2e5b29b8d77e6b74c14d8b03f16b829a06c7a4a5aa6c58145ec7a32eb7975bf35ba60b762c0fc5ae0b740e9cab5c6b762c0d2f4a5eb56b838b034bfef4d305b9362baf8b5c16e4d29d688bba647d74c8b774cb46038cb2dd60f4fe1b1b0cfc45af135d22fc4b7f97c7c1e9fc36def54836f96bfe545af2a26f2d16bd8ba4e2f13a2d78e060aa544de305278c155c60aae307e74dd1b60ba5963e8b5e4135d6f63116bdd326bab1f988bc15e43ab1f988b5ef5e87582e9608fe3e447f1f223f8f936e5fc5167c36e5b4fa8b1469f563653e40acf969ff9f969f36e5fc51628d3ea34fb4fc4ea70d3ea710313f0a711b01c6597fdaa41b7c563619f88b5e5675fda2fc4c7e5f1dbba7f0dbfb54836f88b5e6ee5548b5e380dca916bdc292dcab86e55c70a4f0dcab86ef9d3746cdce9638fcc45b72f21d38fcc45b72f21d7f4622d78fba6e9c7e622db9790e9b9d2c75f3a90f82aef967efc1d787ee93c1d787efc24f4f84979a3cd127479f35ba7cf9adf9a68ebe68a8b6a8b7f35bf34f9d3e7455ade5d6eb7e69f3974d156b627d1d69f1d68eb475a3a659d4d95def49f6d9d4ddef7656da1bbdeee75b04f9d0ddef76da561b4deeca80f6d2a9d6ccda6ef6549b6ccd86ef45ad82766c377a2d6d2acd86d365635b334aff743370f4ddec8dfb79c1e0c27a1fc3b377b2311fbc1f0ecda6c8c47ef0783a1ecda6ef657076cedb31da9e7072a9d6ccddef76d82766ef7bb6d2acda6f7656d99a5517119ac7a407e23369c1883db9af5ac1bcf2d9ac5fba4066b5bf51edcd else 0x790f6ac13e325d839ec5ebd973af83198d90c6547832ec5e3d83648b9af3ed7f972b4f73717af763c16aff562ee6e2fd1cc92ab3cf973cf17ab32b1eacc9e7a356641b192ee53d8be362d1905e45da35190dea33c8b87bdbc9968c7b9328d8f7264ab8a1c1f8a1c1f8c1f8c1f8c1f869fecd3a3797aef9df5e5957183f183f0e39dc60ee3c60fc0c99e879e4df9e4df9699e7abbcca14dfb5f32fb784f6b5f32f84b5f32f84b5f7c24b4f14f4dfae4df19967ef98248bf7cc1245fbe60922fde248cb4f708e04e0644e3d84e11c5cfca7cb4ceab899f8e5f43c14fdee38e11a57f99c07fcfcb577003f801fc00ff6e007f0d3f97a1fd91b33f0f9625a1e5af7e66ab899f143ccf899deff1fd99b8f133e26746f2fe80749fbbdec3ff1fd00e93aaf4f3d3cf4f3d3cf4f3d3ca1ca7ac595dc6738ba4797670caacece59439d43aacece59439c53d567670caccece71ce559d9cb33b39c739567672ccececece55c238138138138471effd1a5cd7fbe9bff9646af5bbf0f445bff5d17dd67cb06bef4f0be5debacf969286bdbed0cb776b3c37965efb22b7ebdeed6796e9d96c3aacf71efbb15ac8eabd5ecb3244b377d932844beccf9d09d57bedb1909b1909ebd6f965e92fb4b2f487d3fb2f4b7ec5b2db2e11c71a71a71a2385ef1ca6bc71a2f78e34e535e17bc68f428e347a155e312f78d1d1c68e8e0b7c705bf6e0b65be17bc68e8e347470e3897bc68ee2abc68e8e35bc6b566b50b35ab35a22cd0b622cc45bc45bd6acd688b34d316b7975badd6ac42ce5d34c5add357c6f1b5ef27c94b7b2d2ff9ecbfaafd1af793e8894b7b2ecff9e39fa0fe8e3793e8ba76586fe7a5763f38da567d36b762be75094e57a3ce366e4d72073a84a793f9c6d82dc9ae4ace74dc9ae62a2eeb38a78d36b77fdf39c4a72b8de71b60a6b90363959c9ae62c0a2f63ce49c14d731739c6578d3eb762be77294e56bde71b60b75c81cee5c6b75cc581a5e760b75cc5a5e724e0dcc581a5ff79d82dc9a540e76c6e4d8b039db305b9362e724ecc14d8b039db305bb16073b660b726b929d673726b98a8bbacec13ea6b98aeb3b05bae6296eeb3b05b9362e73a3601e77f6df65f76ede4ffc45cb7bdf9b1b78d36b762c238cae37f1172def7e6c92b5c14d70584716e81598bad5bae08938bad6e09038bb740f1ebf05b930b24f182985a0786e81f5fc2d704fa9ae3abdfad5bae08ebd7e0b7261674b36ff39f86ff7b19cd8ee3793e1d8080e83ecb6fff48a7f1d1b2d5b935c109aea566d9f5bb1057e52dfa45395af7f0d89ab56eb8240f2ad5bae62894b495adcc581a5ff6237268126f0dc9b152784d8b03c3762c0f030a7f1d1b3726c574b2c7d6adc9ae084d75bd8c5ab726b82135d58fad4fa9ae6288eac7d6add731442ddd3726c574b3e1b72ffbc16e4c6945943ad)) else (if i<5 then (if i<4 then 0x7c3cc827c64ba7b3cf5218ccf4bb178f1aeca363c6bb2d19614bb26bcd19614bb26bcd19615874979a42b0e5dbcd195872ede68cb0ac3a4bc26df1d5e136f8eaf0ea92f2f8eaf2f8eaf0ea92f1160ff34361d8ccb4f46fdd7e6af6430ef455e339df9b1b2187683fa50f8cdc876332cf3961ebe26e83d7da13479e71bbed079e6bddf683caced8594f14d8aced61de29b15b628f15b628f15b628f14769abc8db2c6a1ab0ef3658d4769abcd91ac6bdcba79478b4865ca3f17b2c9fa36593f451db0b29e58de58cb7c576963e2bb4b1f06b632df1f3c7cc6ff9ba35eec7a09af90d57e9edcdd1c6db72521a0fa9a1dfe6be4bd3fda59e7fbe4365fe9f4f6b1fa29d3de6274ff679af7a29d3dda6af23177b0d587785dec8ef85da6ac3bc49d8ed3561de70ec769abc2ee36c769ab0ef12762f795f8c9702e2d218ccafcbb178f325dfd18f325dfd1db0b28bb79a42b0e5dbc8ef4e176c2b0e92f3476c2b0fc2f3476b0e5dbcd1db0ac3a4bcbe3abcbe3abce13aa4bce1be3abcbe3abc3aa4bcc1fe6a26bfe5867d73dcdc5f63f4f5d5fe33cd85f21928cfade622e7fc9c6659e72c3d7d63f41e79e8efb41e79df70ccf5bccd6fbd63da3b595874979a3b5872ede68ed6561d25e42f90fb7fac7a583633dbe7bd643168cf6f21f6f19f588b9fcc4665ab7f5cb0cd6f2c3d5be8cd6b71e8d9a8f56ef307b079e60c7b660de0f6cc1bc1ed8f262b6c79315b63c98adb159e4cd8acf266c567933672783db393c1ed9b306acf21765b52706f2f9e60d5b63cb6e0d27632bf767249785dbf44d9c9e32ec7ef249783d7eece492f2fad3f7672783dd8fde492f24f1f97ebcf6ff271b0af08fde5ec0a0be4b6c421bf7e7944f6f8f578477ef279615e11fbcbdbb7d847a23bf790f6c2bcfd1397b09b392b3c76ecb6f24978fc33b6d7bab72fe8f7b6eafeadcbfbf55e56e5fd91f3defc33b6e24456e503aaefcbc2725655febc87b5655feabd6d13924bf0cedb0dbcf256b17ef119c486f115b940ff55e79e4acc2fcbc2725661faf21ed5987eabd6d13924df6ce4acf3ebb2dbc925e58f8890bc37f2564efdabd3da585e1bf92b4f67bedb7945c95a7ac2bc272560df3d3dfec4676d89c95911aebdc9e558d761e43dab1aec2bd6d13924bf0cedb0dbcf256b131f119881bf92b7b57a94c5f8661bf92b46f62fde2330de2728956faaf727956617e5e1392b30fd790f6acc3f55ea5e422b3f4f790db7e4ad7dcf7bcb0f92b5f6b383f21b0f92b5f6fc3365e1b79e4ad9dec4c466272561ddd7eda5317e19f2561dd87ebc95afb9efb17e19b2f6188adca0775fd5e792b3ad85f84e4aceb61fadb44e492fde2f21b92b58f8881837f2567e21c83df25621fbdfb57b577e0c1bf92b3c86e4ac3db0fd5784e5abd8bf7887061037f256faaf727956617e5e1392b30fd else 0x2881b5752675980fa9fd59df544de58bafaa26f2c5d7d4deb9c72ea980e325c4d9e9384ba4dfe92e32413849a5d23f56d4f18bbcbc17c8ad21bac62ec853ab48637a2eab64a1f1884bb7d82f098e1084f7e37b48124313fac3fc60555af109efc6f60d1390e1fe37a050d1b86ea9d6dd5ff8637f5d7db775e18d9da9bafb6eeb1b8513afb6eebc31b3b7deebeebc31b3a4392370fab5e37af794f1b87d5aebde4329e370fab5d7bc8653c6e1f56baf790ca78dc3ebcffdc43b68dc37d834676daf7e18dfd06f8f8de53fa8dc20df1e4329fd70c69ef8f2194fea370837c790ca7f51b841be3c876d1b86fbfef8f29e370faf1f7529e370faf1f7529e370faf1f7529e370faf1f75b68dc37ded6d73bcd672891fc6e2230449fda7910893fb66ff6db4f3da7fcecf7b00fcbedbf8d3d5ff44d3d3769ead1118228e9391fcb5f74de7b87a1474493cb0c426fbffe5bda379649fd97b53cb34e8897affcf28f3ded7dcba84df87cb233b1bd4f433c0bd16dfb50cf233b1bd4f433c8cec6f53d0cf233b1bd4f433dcbc07a19e434f445d719ece8c9750cf2279f2e719e8de3b2df53d0cf735c68957b8cf477b5451bef7e59e6ebae7dd67af7176c37fbdc94771b1327f1ff0559cb7ffc9477a3136bb359cb03df6339a48449f85b6ffdf131bfe692d1d8f1146b1c58fd1622320bca5d6ffd16320bca5dbdee71c1a77efee761b9af3f447115f760dc5397b06238d35fb7ea772f76f7ba85593857dcad429cc3735e1287da1b234ee556ee8dcad0db28d35fb4ee5dc2be49ca3dd0d4ee4e3dc2be49ce3dcbdcad0db5cebdb8db12e612d42d67cd24c2bdfd5db984b51cf382fadcc25dae2ae612d04e8e377156cf35a10360987eaedb371573096b6787f8c9742e66163387f9746c798ff64bd8f31fecb39476c2cad963ce521587d963ce51dac3ecb1eaff357b16e4fbbe5cdbf37464b33d3eef9758f7ef64f3d1bf7b279af6fdec817e6928c9742e17cd25192e05ec78f2aec9e7a31e55d93cd7b1e55d93b594d587ce49d8ed3561cbbced8ed653561f39276577e6d8f16e702e33ebe5dcd25192e05c7b3a33279e8c7b3993cc7817643d1817659da3b596165176c6768cb0ac3976c6768ed658561d258ced1db0ac3976c6768ed6561cbb633b476b2c2b0e92c1af1a70926bc69c1af06a93c73636bdeaf8b727d338679ba35eec798fd339578cf37471b6dc9507c665ac7e83dc3cf47a0f70f38de83dc3cd7bd07b88ef85e17749a5ec785de9693b05a43268ccafcbb463cbbecb4652ee92f297a1765dde52f4652eef12697c24d2f42efc52f42efc52d2742ef2c1b19edf3c43ede32ddc861dbd467b7934665ab70eee65866b7ade587b466b5b8f46cd6b71ee6928c9742cc7e6cccf616339bf2e79df0f42d95f0f13595f0f13616c9e77dc30b64f376b2af7) else (if i<6 then 0x523bbe146e656f1723fb82de4fc04fc5fb9fe952263c18dccae167989cff217bc5f50bde16731fe9482e71e3d9193f0889ffb7013cc7fa521c78fe945c8e3d8279cff4ade418f062732b78b91fdc1b20d907369e2386c83641cda788e1b20d907369e238d3c47144fa88508da8699cc69ce3510a11b50d3398d01442c69f5109a6731ad3387dc6b4f61f5a7b0dbb0e4f634e4f1f678e1b4e4fb4b3eec76ce1f40611f5070fa7dd86dd870fa70db2b36a3978db1caf1a8e59cc6f2f1bb3966dd9dbe627d4a1d79b3a7313ea59522f3fb600c2c6c0a204e6371b03b0db03b204e63604e1b627ef3d7f59bcc6e6a69645192ed7d3ceed25e7acde63534a432563d77771e44ff666ce6a6e52cade78ca63b0e71b7110ae34ce634fad3d971a6731b71a670fb08fa8846d4574e6361635108da8ae9cc6c2c6a211f515d398dae9c3e971cc6971c3e971c3696fd284a90a8e2ad85cab65f1c197c732711fc7ce2fffa53f72ecc78f93194fdcbbfee3e60513bf81f9850289dfc09c9dfc0ec813886e54884a90a8e2ad85cab65f1c197c72a7bf7c9f87ee9313fe0c7fa95fbef4ae1fbbc21fb9fe94fdd278fea594fdf7b8b9a57efbd2b87ee93ddf0fdde2ef7efc028611fb9fea594fdf78c7811f31a594fdf7b8052e31b994fdf79e52e6a93bcade034b2b7836f7d1e1aa4bcade62034b2b7b4b9790952212a4277547212a4425484eea8e4254884a909dd51c4eea8e277be389def8e0cbe38f3bc9d4ed2800de652753a9d4436942c769a880e94255f9e53a9d42761a84ed369427aa3d34a12afc639cbf52834dfba4d8d8075d7e7e363601d75f9f8dba4dabafd5de9e94680fd9f80749f9fba693f52e9a4fd4ba6900f442c644d68558e883f26b42ac746d0789b75792c799125a7615621a2fd69d8578da59c8f3eaf62fc29db9bc530969db9844d68366ff6a459ccfd47bcd6bc500a7b8cf91e7e612d28c51b51a70da8d39d3a216ae4963d20fda36ae02b1d10b5724e9b9a36216b664b40afb63a21bdb5f391e7f9f4827ed9e612d5c79fe6fdd20b67984b571e7f9d8f4827ed9139ad5cb1fadcf99168130bf5cf99168130fd407cc8b40897f9fb7309dde4b52bdfba745a41660ac5fb441a5660877e6c33f23bdacb71fc1776ee7ea4b4ce4aa7f65a879e96a9ea10f9768f0ecc62cdd9633fca88cf1afe7c3b45ff51d6bf88c1fffef390b49fe692b6fb7fef9e0dffef86fc1d8f4f8c0fef71117edb8fffc9847ab3eddb66339d122f88dd611eaf5a39d77fdbf889beaf457d2dea3a4f2cdde597acb8ee87e076ef75bec77b596e3ff4fdf687cc78c8eda76ef2d7d7192f0be9b96fd5ea3cb42fa6f2c5d95f5cb2f767ecbe6c764a8b6beb9ed9fc761bed65bd6edef6339b1decff6ff96f5df7cd8ef67ec7e8bf2deb31b8e582ff95b9f99e37ffeb735e219 else 0x721158530f308acb392479e4ad13cc497f25689e3ddb12f09f5e85e26485bcf2561037c4ab068989e2b4e92f61f6bf09c95833256c9d12f7d6f6dcef723165ed3195ddb291ff857f43b5e33a8de0fba1f07fe95bdc676e656f50f83ff71fd2aa62bf9383ee439fe955df83effa56efb8f12777c1f8f5f07e3dbd7c1f8f69ee446f13c7de0e73fd2b89ee78c65719dd7fa5fd0b890bf99ea70ba5fd0b95fe67a9d285c42bfccf53b9fe4689bd2d3388ff4f7428a9860d0bfa1ea73d869ea9d0f32928ff42f29a7dde7695cc2f7d2b7a268713fbfa54f7228a9ceffe953d8742a73befba4f3dab646a653e77c1fffd28673b53f5fca7d23185e544c9fc491fee3fa56f7aa9860dfd2b7838a98cff4ade0a9f01bfa554f78380dc4adea9fa0c93df719e127e2fb8ae13719ee56a4fc3efbf1c3e7ae779106948e0678e1e2867851c57b20bb534701a7bfa56f17719dfe95bc5dc67678c6e656f7113fdb599f8cef143cf68de27ba1f97ff4adee33b732b7a87fee3fa54f603f823fc5faeb9fe95c1f73d80fc9f84694fe27b29f73fd280798f053cc6e6500ffee3fb33fe95b5e33bfd2b7a87e2a7fd9998ff4af6e2a7fdfe69e9bee3c677da67c5f7bdf99c4ffdb899f1edc3d1bc54e7bfb33fe95bdc6767a6662732b7bfb8b9fe95e833c9de19b7dcff4a793bdb7dcff4ade781a77b6ffe95bcf0336fb9953bde067893bc49c54f18ff6f4af4f0574fe9e3c49e7bfa56f06f4f27ae77834af4f057aeede0a9e31b995bde9e0af40a191af27a77b6fb9fe94f2a79e31fe95ebbb793c63732b7bd7f3c47c9ef88f88df885aa8b4d19df10846fc4237e225b88e0cad4e5a68cef884237e225ad3c47119df11f108df8896b4f11c69e2388dee4622ee31177188e5ccade2e96b5e5377adfa265f764b6baf5150d96c65fb6579fe5d6bd0f67b6e7cff2e956bdcca44b28af6d7f6dca2857b6baf567b5e4f6ca428af6d793db7329457b6bc8d3a19671e85a72dabf1156dcff4abea2965ec9edfd7d2b7915f449692e6fa56f22be892cd7ff3f89ebdf7f6a5edfedef3fdf760943b284b7f3db2e877817a265fcffb7a8517cee77a85170f6588af7bb1156ec59f27b7b6fa56f6c11be8953d97dd9cfa9fa7659cfbeb4d976bacf9dd94bdbfd7d2afa2777b3db7328b94567cb09ffec5b5698dcca962dd6ff698ff4af62d96cb7e23fbfedb9945bfdff698caf62decf698dcca2e91b5ee7fb8dae925cff4adee34938b9fe95bda49fd2b8ded24b995bdc692677274713db4f36eed19d2e97567f4e839f5381f90fb9ef9a38b5ee7fa56f09c49fd2b784e33a63732b7bb7fc5af53fb901e17b25ccae2fb5ec92b8bed7b21af2f1ebf1a7af5bc1009af15bd87af78f5c104f0195bdbdcd785ef15bfdb72032b6693d84ff69880cad9a776a373fc85ef122f7892fa13d47fa))) else (if i<10 then (if i<8 then 0x9edfe625ae60936df9da6415c31c4bef35a31fe66de344e63fffa386cf5b0796bb486e77ba7652d65b985fe3585e958d6c9e5aed3165b93585e958d6e9d9737277ef11fe7efc9d918bf7f4ec997375957c9c465aed31a935a561e534fbbd8cb9bad9d93888b5e72990f3afad83cb6e616a77b27652d65b985fe39d2977bcc64f2d7698c2ff1ce958794c7772d7698b2dc9ce94bbde63a7d9fd4b2b7b40decfea595bda06cc6e4d656f6c89d6e6e993f02283ef531fe6ecad39a3dc2afe6b747b4e1377aff0f69c37666e650f69c37445e7a0f176e7fb41ec9f851bccc7fa54cd3bbe36663723dd3e9c44c4facbbecad7f83fb5da630bfc73a5c963bbf6d2ef52f4b92ef5b8f4b5afc45a68a5ab781deacb351eadd104ffb4c4d6b7eee642f86f9dbdbb249fd6f6af77dbccbb7646bc0e13ef3f6bb48616a65776cb07f690c2ff1ce958794c77783fb48596e4e74a5def31d390ff5f52ca3af76f0ea43737d2b78bbf9e1afc789b2c2317fbcd10c9681dd779dcca453343f2c3d83ef5e6fb4d6fa50f50faafe69adf74e3d17fbd597fd7c3da13514cdcdf0f13744422f579fb6fa54cd0fe83c13ea379fb487fafa569ddccd9eb7b6e57b35bede9943f83fb5da627c6b0bd2b4f5ba7fe957bfb143178627d2b629fcf307f6b2dcd4c2f4ac1aeb64ebdfda62cb27e0fed7698b2dcaf75ba7f6ff4aaed0c6c633ed31955da7f58cc657f71f2f369a235f96f6e9f8ffd97d5a62d31bfd49635fc1f6eb2ff344f6adfcdd14e9cd7d97de66b7d2911affb4c597c4f61bfd97f453a735fc1fda7d526b4bbc5de4fb359e77992ef88af7d6f6ef26f276583fb4fa17f8e74bbc5db193e0fed76989f1ce9778bb63a73efebea595bc75317875313ebe95bc5dfcf227d643f19cd96a7ff58fbfb7864b375e68bd7c31be64b6b18ef4b4c43fe6eb5f6993a2d6bee6e9d3ef765df709aa2f5b777bbcf58d6fb7a57ad12f7d6f69f7f5f6f6993ccc1fdaed31a939d2b0f298eeee47a5ab711452d5b8f175966a3debadd12f7d6f6dcd2ef6993bad8698c60630c64ec18b1fc6b0bd2bf55ba778ed49d2bc56e9f652b4dfbb39776f37ba57eece5ddbcf9edf79e513e27d2818f92fa569ece4ac62f17b98ed797f627cafcf7af42f130b56e5fd69c48ef23e251ca0789f4a063e3dd5703faf42f57f31f1392b1886cc5e792b44f89f4a063e4bd87dabd0be74c7c4e4ac637dd2ece4ac62f097ab27713e170bbcf25611e4895a267b0ba4db51c9106d3b79e4ad13e94f7fe4ac89a6ac9da289f4a063e4bc3662f3c95a279892fe4ad13c27e7bd7a178985bcf25689f4a063e4bd87dabd0be74c7c4e4ac637d98f2566192f69b0c77f6f25661a3924db566c30d9892bcab41f989292f5683f09f75befe7bd870b79e4ad4a0c325eeb7dfb0fb73a63e27256319393ceae2a461f6bf else (if i<9 then 0x63a6f66d0ffe4608d44043a28966b40540a81502a05408d0144bd1d7e27cde9ca0a81502a05408d0d03be66d16b293e6c0456b3a7ccda2c579b49d179ba9d8541c0c2a0e061507030a83818541c1e3f2d46ed53bfc4df9bd3e06d3e0a01590e92f4f9f2328446021d144bd287f23046a27202b21d144bd09030a818540c2a0615030a818540c23407b86d3e54fe5d0350e99d43b523fd4fe5d051c87496b3a7c1943ca23390e8a25e9bde8713e6ce4074a1b0f1823513901590e8a25e868151a0540a8d02a340a8d02a3408d341a38fc25a880ace9f0975bc63888d4407425d0dc44602b233425b0a818540c2a0615012ff974cdd201a5d336a272b3a7ccd8ce511a8e99ba1b0f118c59d337bdf47125a2c96bbd502a0540a815066ce7405144bd017e467288d443a2897a50d87fc8c11874512d67461e31c446a2b3a12d4456b21dd0141502a0540a81502a04681d611d557c3ac23aaaf875540755404abac957c64a8192a064a81e4e43a9d014ebf63a84ea4fe3a84ef8a23a84ea23aec9c9d8ed8889de1da5093f8ea077f8ea109ddea13b663b0de58f03447929f949db680a76db6db6c7509d4ec7509d447509d44741a9d1d42753b1d5940eff1d4213bbd4276cecc75571435541af29d294e94949494c7509d4ea23a9d44753be288ea13a88e835381a0d8ea13a9d44753be288e87509d4475d939da3aab8a1aaa0d8eaae2a6aabb2abb2abb574d81ac96574d9d992c64ecc9da3bbdaeac65b2cb6596cb2d9980d98ed31da63b4cd999b33365ea0d7ed901b379911d68104d8ec80e1bcc88eb409ea13620d7edef3223ad02eee4bf3096a4f9fcece3ad475a8eb50ddef76d3d587e978206e3764dbcd2c252f21eab0213dc67c9cc25a09518a99c5e0d76d5d47166082426641afccde643b5a1413630d4733b5a1533abab4c776145ffc241b1bd53969660b53b6a76d4ed32fdd31da2d20b30562fd1da2169660a3a3b1a7d4cabfb8ae23368f79d87c70aa5e661b4d8eeeda61f598279f9ad3352ef38371aec7de6b52c252eaa1c4cbb30835791cd68106e9704126d83639bb7abce9ac7115735a598084bef795f32cd86f7587ed2cc13cecd7e76139ad52ef3849b60dc6f35a25c4a5c347835fb6406cde643b5a044beaead7693affd4eda9db53b68f7ee9d9d16905982d9beacc168fb17ed9d10b4b305b3b3b3a3e1bbdeeb0fda09e081b8dd936f348f12d04fd1c257d57d47b72d730933a3e1b4deeda61f09e0825d8fb3209fae3af6afbcc24f7c6aab9cc25a75dd79909c186b7536e029eff3e6d912d0371aec7db53df98409fa3868e06d9f79857d58b557f333de7adcaa66c6e5a13981acd06d3587fbb6827829904126d837a6e2a9ef5fe26cdae69efcd9b4d12d3dff3df99b67dd512d3dffa3ea868f66c37bac3f682782995ab35dae027ed else 0x1c96242d610e4bf8dbc486c5b325dc87b192d6a235139c559810ebd415c6dec7105b7df48a72b290e3523228dea6df2177018fefb80c58f7018062e0311d9b3af99bf59c7dc0d671f70359c7dc0d671f70359c780ac421e4fb58c43ec042b5190e4b63bc71d8c31eb61829f51fc6defbe914f26521c6957e34e6ccb7157e5c55065e6e0a8b71ca601a9f15c0875e03ffe9fb01d3f603a7ec074fd80e9fb00dc7298071566043a5cf357f6bd80aeec05af602d7b016bd80b5ec060a6c5799b43fd96b1760cb58bb065ac5d832d62ec30545300e2acc0874b9e2cfd57601576015760247b00abb00abb019bd30407160414960a8b71ce2acc0874b87bb26019300c98064c032600b9800dfe6b5879e0c3cf061e7830f3c1879e182a29805872ef99bd681e1ad03c35a0786b40f015fe982629907039b3eff80897a60a8a601810ee7ff2ef99bf9a63adcde0f82b192f45a88f0545300c0875ea83e48b8d64d066be6b5a7ec034fd8069fb007dec034fd8069fb0008b8964b05ba07475fb5fcd6b1f3831f3831f3831f3831f384af36cda8bc67b516928aff1eb9baee9b1606c7f9248f4d8b0363fc0498071566043a4bd217f35782b192f45a88c06043af5a125db9706c5a5dec64b5a88d44e5300e2acc0875ea08bac7d1066be6b59300c98064c0326019300c9802e6005a332521ff7dae8a31ef24f76e81d27bf2e7c5b3dd16add0343cb24ccf56add0343a72ccd0b711fc87b5b9f9ee9ca0897a371ce2c087567d7cbbe029e92f9ba2d446dc73021da125ca5d63e6e97fde8b53981d980a8e7a2da592d6a23516e390159810ecc822e9ee91335f35ac98340c98064c1a064c1a064c1a064c1a02e60d060a8b2a601c5592ef84bcdee2235101944b2deb38f0d671e1ace3c359c7872af73782a2730b8ab25d977ccd88d4794b79b245d96f3607ecb58bb065ac5d832d62ec196b1760cb58bb091eb8d19ed4864a2be9339bc139c581d01411712c969838b020a0a57e4bd16a23c151810ebd6c64b94b85af5054bb192f45a88e043b32b24bb72e99a5b888d456497ad24b511e0a8e2acc0874ba4791fe6b536c026d804db009b600c7600c760136c044d07221bfcaeb276fcc9a0cd34ff2bac997e32065640cb9389c8dafe575942fc6410ac82159042c224032a80e4056797a9c08f81011f02023e04047c08040840840840808f8423e07e040840840802a054108900caa0513901158774fbfef0eaa80eaa80eaa80eaa80ea8d0390115ac8774e5ef0eaa80eaa80eaa80eaa80eaa80ea8d0d20ffcdbc3a808e75011cea0239d4047510115ac8774febc3aaa03aaa03aaa03aaa03aaa03aa3433603a0292513915ac87741ee7554075540755407554075540754680a25e9f2670540a81502a04682880e9f336a81502a05406283cde9f05288087497a7cade)) else (if i<12 then (if i<11 then 0xf4b7b7cd440567813fd57855c5c2ae2e157170ab88157171c1caca35b24b72e92dec0282efce3aa272b21d40eeaa0ab88157102ae2055c40ab8828445823390145082d6825694fac93ffd7d5acbee0188310620c41f351011167b6ad67aebd450c8facc41883106203141fb08b046801d6c8095bf351010e88b356b2fbd6f31ded3da4d1d07228a15993419ad6fb2c69e87e315bf311a88087411ad00310620c418831008ce51ad9012b4405fead616ffdb4e5911436b59adb5acf645ad600620c41883102264859ecb3a7afec2202b3f31167b7cf4f6f5c17eafd759c3f150af417ac05fa7b4f6cb662065b3106cc40bd962f665b31041fd0eba4bb542cf6116221165f7d2844602b28935a22095bf301590e88b2fb8c56fcc46021d0543a6aefbace1f268e8391450acf6419ad6acd1d06690e2b387ef69ed9d1118adf988d44e405643a0b4d811d0d98836620d98836620d98836620443b88b3974a1d087cbb581f23fe942233942ceb641104adf99c87564458315bf3e5119c874150e889b7e0a2722690b347fdf59cba6f7934789c8a285644cd6b5668f23ec690b37bfb1c80e822c3c62b7e623513901590e82d0d01a035883101ac406b101ac406b102b5c4459f3510159115ab2b78cf9b888d4407456f0f1118e2230159f9e8add5ace1ebd434eb36620d98836620d98839497fa7b00d774f6f9a89cacc888b3d867cf9446a3a7b08b0f1823f9ace9edab58b3cdb95bb59fbdd46266b12f5668f9334e2859edbdd5ba38e2f659f88310620c5ed883d9e4bba72ef69ec235946b6404ad10ba315bf3e511a887416822c3c62b7e6230e8259d1878cf9b888d456745682417747c9f2b76b3f7e4438d67b38f5ab10e2e359f351590ea0ba0188310620c41883102b6aa0aa6cab8962a82a9b2ae258ab8815710170476bacb12c658819620658827bad80f764bbc4bd84ba1d93c1b0ec6e1ba19ed8c30c2271d93d83f63920da244e3b27a4761860e5643b3dd88a7bada8f764bbc4bd88bfb3d25e76d4c7e5d923b0c31a355841b44a329a0c38d6734e6c1b5506555065d9caf27130e91ce36b5842842842e5ff0ef88b96e6cd3a4fbb2579bdb0962d044bda98ef397648ec30c30a339dafc36e5f1fd996fd295bf6261d23f0dad610adc72980715646757fc5afd60aefac16bf582d7eb01b7f61bfce5eb3cf0d679e1acf3c359e782ad07b386ffdf2c79dbf15793d9ed7fdf2c7a17e0f0428f42ff697f9cffe48f9b7ceb040fd6081e0947ecf6a63e7af397664f6186385849f9b331f1be94af276d0e91f86d6b085c15109dc15e2acc087567fc2af7155e2af7155e2af7155e48f62e2a82af7155e2af7155e477f0dbd7cdfad03ee06b40fb81ad03c2db36cc63325da8b5bbfee2bfc7a98ee0cc976b63fc36933b91f7314481b1d64c82b98ab3021d2 else 0x3fbcc40bf17b3cc41dd881d736c943ffac85e3de5b47eb1e7e80d3c8a7b59c57ddc7a980ac87643ec4158915f7f9f01e84473becb3e7fe7c0787d643a333b3a0f064743103cc40f3103cc40f3103cc41dd9d5144f688362948b12cb8ed3edbdae2948a43ed651531473c3e1dc48a7a45d793d8db34b24a1e27b3c8d08894f994bfd9de7f27f348a7b1378a7c4e7b346bd64f50fed2d91359d58eb80e271d5aa389c7340683101ac406b101ac406b101ac40225d2c1986a28969ed124f896659c790e405678f47df189124f432c1844456cb24f8b871ce405644e2a7e3170f31062e31718b8015991c441433c62880f0fb8e72b67b395bc3cdb59c3e900fc3d670f7811d079881e62079883bb1012ff3bd8065ffe77b1cacc9ec20a19e314787f3bd84787e17accf677b0ef051335439b722b27b266a44db59ed13d9d1a6947904687911217c853e266a8791593d2dc99abdff658adce71441d51c1677b00620c41883106209ef5ec180567dbd48304f649c440566791c7b45fd5a24b24fc7b2f67b8c5c62e317b62e2a6b21d90fb10577756a8f0f874122ceeefc3eb21dc4e38cf18a3c3eb2e2adce1de08db580bed4b67469a919046871217c80ab0fbf60535eb067a8ac87505d00c4188310620c41883791ed2dc00ac874fbf520256a8ca0ea20147002b21dc5c2219e314405650ade047d9068d352317fa1c4963ed12dec8ff9751c0cf510159e0447ff8c5c62e3170f31062e3d8065905de0e5664f47da204ad47ffc1cac877170e38cf18a2b28f6e110256a0ba2313469a918bfd0e24b1f653e97f933527f137a5867a89cac8778bdfc310620c418831009bded53dcfd11bc76867b3a8cec6f6ded68678b9142b2a70defb78036767bce86f7c0b27beee1b9b77cb27b0dd003ab77b3b53d4f3c1bdf2cce9af5686eb2e7e1bcb6fb3ab30fc37bef953a2854ffbe0ebc41cdf3c400df3c45f23b9147e89c679a7a23b9d45cb80a27141763a5d1edc4e7b4f69c3bb3a5d0536da75947ed3c0769ce7975a7cf34eb33a0ad3aca3f058eb4e3df2eb2f10f10f11dc842239e851d5b87e845cb039761ff2ef28f673cbab3ed6073c16d66dac79fdacdb59cbf5fed688e7c3ff6bc3f81cbb3d6b51ce782dad63cfed63ffd65cfc16d72de5d661f82daf971ef0fd0842027957e04f2afc55c40ab8800310620c413c88edaedbf4210889a0d62f6490b6b3e88eadff6ba108444d066962f64a104bdcdcb77d04b3a108421066962f64595ec8833485eac9207f574491d2ddaf22891448a2451228899a5eac91657b200af6459c4cd217ab2459e4ce4d217ab0b722cd084211c289c80a35b27cce4043bc49feaa0ab88157102ae2055c41c1c80aca35b27cce405643babfe157855c5c2ae2055c5c2ae2e15717087ffb70ab8b855c5c2ae2f655c5c7002b28d6c826) else (if i<13 then 0x61f66cedae246e1668df9d5ef11b5e110ca78dc3ea415462d9be61b06420969c0d8427036088c6689c99a0798c04893180910630134a278ab2763bd7a17a773d24883631593b44321a48876df25611980d061a6c2b2768a603418180d0611027e79e4addccbc5a0b92b32f66a1c94bc95afb6618cbd99860eb601d6c3ad8a593910f1563c8878a29b60443fda821e187b154b810f056c842014f0cfe2c57b836430a0c429cc1885468302d0453f4ea70af762e14e60c42a3418040df5c3193a3786c178f169221cf4a7f51b84553adb172d85060861418854683030901cc3818468ac1815c594fa752e2b8637a4efe8af1f43257529e370fa184825a1c0c10870308d158302249e61a2b6d8b1692b61581c4716cc9d15a5333909266d4527e9c84fd4df292b67214b536c214db135f7c214d7c9af8d8d66345e821da727516cd35d34c7bd45f23e9a4877c3a2d9a7c63dea2f91a0bf61da7516cd35d36a517c8d05fb0ed3acb45b34d74d31ef505fb1ec3b4ee37a69ded98d178b62d393a8b66fb70d31ef517c8d57744b9f168b669098f7a8be462dddc5a7516cdf6e1b528be462dddc5a75968b66fb70d31ef45bba3de2d3a7de9a742e99c3ef4dba920fb0ba670fbd36ee9b77b70d35d3517c8d05fb01c553a8b66909ae9a8be4682fd8aa7516cdf6e1a6ba6a2f91f4d24578745b37db869f22f91a0bf62a9d65a2d9bedc34d74d417ed3a2b2be11c36d241b611c36a6846d951e4c3c9a920db08e1b5326e5a6b59f62b3a86a67d8a59f8ea2a74ff81c8ea10842107da286a628fb159bd4e870391d380842108444d066a4777d648833522a272a61b97c4d066a45649ec17fe41453c0e474e02108420522079246a62a51f62482847190fb419a91f22b249ed068d34a32272a61b97a0cd48ac9efd9066b17d64f7aba248e8a81e440e47644e048a2450891448a24507d8a948a9c87d8a01454e4e5e6dc4cd1f6b2436cd7f64587d9a9ed44e54c31a0e9c9df539ef97c4cd2c9ee2668d7ac9effb2d3522b33b03e33d121f71d15530391d38084210847f4aa99f7ea4b9fe95bdc49eb8b9fe95bdea4e3fa56f1f7ea4e2e651f7ea491068d352271465aa72c8335eb7aa73dfce3a8a9b6ff892790842113d86a1422ced0809f68a98a00c418831062051011427b4808dba191f5933a4f24cf23eb00310620c418810647e739d9da9a880874fb142486dacbefe3e6769e63bd9decb2fb94f35f93419a23ff658300787c3b9d7dc0310620c4188310289f7222a62811b7436b5808db584ffa6f25ae6727fe97e9b9f626f5aea6ebfb72e74933dad61f66bed6b2a7ed2db5ac00c4188310620e1073bfd06e144e4064f47dccf2c93d2fc49649c572a383901c553f8effe188310620c40a227b065913d927015993d8415a7f13d92705e27b54ef017cf4741e62d else 0x3110c11de4c778e791b48e2d1823ef1cfce46d23d0c4719cbe1b48e938dd7683b205b6826eda09b18720113d9e45e2762d00e1ecde28c619d993d9cd3c71d1f7ac884883cd9434ec3803838719e0cec18e319e68fec04d8707cf9c3438a938504d2ec2384de10c5d146d8b40765d15083bc58f60a0f06420380f0e01b09c20afa0b662c3b4174170884d2e82470934bac3c107723c5b36c0841b0e06c38032411995b060ac04c602630032c5a707e3a3f32639291e55b06e3243159c7830518481c722b60c1536c018ec026d804db016203d156bee8f6615f7d25212ef2ad8371c84bab60f7bb30c24c3addcc2783f4ac186120cc3991c0c4c8e06064703003d169b6a0f1563e3a2234db5078ab6a0fb6043d8ae5d07db0242100a7b17dd750ee47650619418650626410763de2d3a3817e451f093637b34c82bdfd3a9c1de2fb99638186506196381891e4bd49c24d0531c97a93849a0a9c1de2eda47619418650619403bc594ff2ecc0a1b849be814370937d02b0f141dfac5a71206038180e060560483bc5db02920ef176c0acd8b0ed3ae3a47211f5148e426ef948e426ed8ddb1bbe37371b1f62aa74389ed53ab4e428d9d2ec23918bb53f771566b34f62a03ab73b53d4e2acd9d3ed5a2bed9af6605f61511b367414553aa7078321040ce03c380f0e01b50f1012cecb56fb62b43e7b1561f66ceab48648cf25df5ed3dab6149188505d568afb743d99c6e3f61538ccb386c19080e06c819c0d8703665fe30477ec827266056026301318098c00cf105fcbe4aff2533b1d1ab7e2fdf295f999a84799a847d1f88cfdddfa0a33b8c4731da6425c836e34924338dfd37e49c633e6c15fae31833828c09c4709093f417938d360c26c1831c184d8309b06047cee49a64797ef271e778ef4693c99937e23e8e4d9b4f265ecd2bf249667188eeba559f93338c632f6661bac1875830eb061d60c44ff4b4f241e2ac793a41e28a507db02cddd74f2fc9671ec552e83c15b21089e91eea2bdd3dc2c0c1885062141885062bbba8ccc37f19f6d39d7704e2ac4286b310a1acc4286b38fb6929ddc2be3b8a7248af73d412cffe53bc3fb69ddc2b0b03062175031ed0ba818f1c96a93d1afe302bf743e2703ff1cc725aa4f4431814553a87c8f0a0c42c0c18850621418c5f1566cdcaf8bf8ce998146008e23ea06047d40c08fa818184803a060c07031ec2b0601454a7d3977f8e421a37a05a9d57e3aeff1c91f068de81461200e0603a060c070302b06094a8adb06c904e2b6d97fc4e4b46fd8adb3aecc2b2ae3a472152f19c849bc7f3d8da8a472126f89a0748e424db1340f626d89be7b264c6d246e1105709c848b3a8aa71b86fbd985716cd66cea74571603e745716cd9d15c5b367450a8f69d8b9e0783210109c078700d84e1916623dc2acbc5dae2b8b)))) else (if i<21 then (if i<17 then (if i<15 then 0xe2285c39d3a32ca4aff6862ea5d2724b448afced44997497dbe65a293a6faa4b6cfd8f480f45485fa1c803d1becb2925f5f597244fb4ba872174b28b3b2d144a8dd18844c969889885198898890b84567587202b35da495c0a8ffa44d066ab9122ca1aed011b436bb49367eba874590d89809a6eeba459f3aeb9266eb337b95cb167aecdf404b3ab6170e2b6170e2b6170e2b6170e2b6170e5cae6522ad066ab8b832c0159aed241180d769208c0566bb491066915cb24e1d769270ebb490da9b5da494d0134b2bb49357f9a0cd5cae5927cfdb91b8b357d357915b910b8715b910b8715b910b8715b910b8715b910b87315732b9fd9ae44912b0e566bb49046735da48233959aed2411acd769244cd6aebb6564813ceeb8b8104eb8ba436e9d1aedee9202e9595dbdd367ec7a746bb7ba48dde8ef6b9649133589675d22c59e4fa4e4d22b96095d22cf655b46cab68d956d1b2ada062b6871f92896dfa10845b7a4a406ddf7637d4369016a12d012dff7117117117110db6f49480d174637d436054bf6de95012cd9f240992ce8421087ebf534a406dda2e8c6fa86c09fafd4d2901b774bea2c054d2901b768ba3bda8b016f6528a9dd45922b7e67392d149226e78d173c68b9e345cf1a2e78d0fd7eb6f4ef5174637d436054bf6de95012cd9f49db7a51747b7f9dd45809fafdc345d1edfe775012cb6a2ef6a48b1fbd28a8fea8b1459b291084211a69a69a69a3b1f54fd4def3be34d34d387b353aba9fa9c490dd9a9d5c9fea80b8d5a6ad3569ab404ec7d53fdae77c3b1f04f57254be82e01a434d35d5c9bed405c69a69a1f54dcded4e24524bef0173470b9a385cd1c2e68e42ed53fd3aa9c29fd76e16721a9c9393aa9c05cd1c2e68e173470b9a3dc45c45c45c45c45c45c45c45c45c42b49a5cf33a33f3a324d2e7871e1c78f04babc12ea3307f0d8c788ffdbc30e7066c1bd6e3613cee0d918f6263030e5899addc86c0706326cf5b901f9831936b9c1fc1936d6f863c9db229985330600b0c20ea51bb09af1c5eb22c48b133e3fa09c8c0c61cbc26ecf5139179b13b99f4c7a609a72f3618f0e62631f3e2a44dd9ee12e78edd4e4f0973c448a7b84b8171789900edd38f0e3c38f1e5d5e5d5e5d5118ff3cab3b66c68d1af1f25dafc19433624a21b443147e2b1b66fd27f47abeacc9131318a118c28b13110c3194f202ac6d238c01f8ac6d9bf1682c64a0156f86d23d0c16315a47f86c9341e77d90294826f94a41363005861861841d4a3565e7082f620ea51bb28785e0b5502a0541e9572dc9908ce1e521f67a3592a321c628bce1d9eb266a45e68fccecf4a83d2a0f4a82a51bc2f017b2a606f28687b150702a0e0541c1f3e2af8a951f0cc62e788917f466317028f0ae26403889c7871e097512eb6df1f25136443cc93b44fd983145fb else (if i<16 then 0xc1a37fb7a5793741aaef6a2d710f86aed53ee1b571006ad71a2e9117106aa2e20d545c41aa8b88356879dd8f8a9a2a361ea22a9f3d5046a7a893441816a24dba1afa7a88358f4f8e8a8bdd0e4b1b9f9ea81b7b19ed5e46c943a1a1fb7a5790a21444dd181300648221302604c098130630f3089ab8331fc6308973eed5c18262933cd748c2ec1312bb3b14edc34dcd5c29e64e1e8d73b0920a29d1aea69b4549626daea6faf156253a3257534da28a6b8ba4d5cb7ca7fed29ae0dedf6d7bfa8ae39f694d706f1ae2e890d33eb8b833b0264c0ec535c5d21483b26290764c520ec98a4e0c4c13c431d8a41d930cf39c7a9b98948a5d4512b6a2f8ebb22108422dbd2f2a49c85308f44501603e2ab7f99db7c75d910842197e3d4c43a15041525b7a4dba2a43515e4566e73b8fc9282911299db7c68b5d048a8422a11508a8454534da8ba323ca82a67634da5f53d78a2533b145d1decc75054cfda8bbda819e7d5d5a739261e69136a082894cdfa8aa02aef8d1e3478d1e3478d1e341ac594ee9e91da07e4baa90a2a342dd616eb3d530b75a5f763e5013362e132d763e8e39d2fa803f8bf2e5ca3bbdb35d8fa175725466905a132d763e8e39c2d0a880533bddce6b164e53ba41682f7b0976d51148514c042c6602158085a96021548ec2eae4ff546690265bc3d5c919414482727fb3d5053d4265a0d218e39eae4c2a140533fd18adb9eda2c9ca7748f5fe848903f242a8298d410baa331a82158d410baaa58d410aa32b9f66bb1f42eae4a9ea4f52d3e81b293d4b4fa0792c817a9690e4a8c812cd90285f50bea17d42fa2ea9decfb2549199572d3e05ef6a0655cb4f978e6a6ae86872434d62c33ea77484900b55eac92818672fbe44cf7c8deef917c818879d0b32176c9fea8cc495642ecbc734dd1fd52864956ecbc73c947f5455cb4869abc73c9429eddb45a9a33ea771242ac85d978e79288925fd5067f6f9003e8be47f6f9031e742cd05ca0cf90faad4a9e23e7d92a2706f443e1a872d3e5327d0a96e4fa50312f42a973adf20eb7c83adf20eb7c81875be40a79e62883ee3146186eee999f9dd40c29b7f3b9f766a1d8f4e775267d8ccfceea0618eb52a7b30c75a9d2cc31130214c44c44c44c424f8603ea3cb6ec23d2bfea2cc1703e31847bcc228b391ea335b49a803edba8487b618698491236f08e6ad31b694239ab4c6da49909aa417d06d41b5108e6ad31b6926426426a905f42211cd5a636d24c84c84c838bde298898898884735699321321321322922b8e4b220c7d535c8e243ea9c9ae471254e4a2bb890fb26b91c498a5ab99495dc493da69a695c5d23756289c809aaed2489a0cd57216495d43a02355da486abb49226b396bb493fabb49067cf2673fd5da28dcaea3fac9167f2672833572b96576947f048a170e2285c388a17 else 0x6cc62c53ea3350d5619411fa9c94e5034b6a7d281a872da9c9f4a0aa9918b289c19561a979d6f9040eb7c82075be4103adf2081d6f90412ff1ccca1752e7de928cd1222a30d9069e25de40723d15033b7e8fb86a192e0391e8b3282a17a890d1c5c19466191c8991c10a3a6223a6223a6223a620265a0d21d9a98e39eae49c994be11cd5b71f50694239ab6e3ea0d26e4143702fa0f8fa8283ea211cd5b71f50693720a1b90508272378a620a2620a2620a1b8f90828847356dc7d41a4dc8286e4143720a2920a211cd5b73720a1b9050dc828a48286e41400004af7eb6e8b4cb1b457db7d72d4bd8bf34d3797c57b2e970e5a27e5979dde5f8a745a5c79de332cfbe77f39dca745a659c69bf65e7709d97cefe4a695c72ccbb8da7372ccbbecbaa3fac290522965c494cb76f290290e59481487ac2619de914816ed361eb4bbf5498f787cd5dda41c6121dd8098c04c6026301318098c00c440847797ee96936e3ff9bc7fac61cc6026301318098c00c603478cc97476a435198f61cc96eedeb513b6cbf8c8a85979eb6a2f8cd9c799bee2e30e7248997196df1a2ac61cc61142630131845098c2284c611426308a03184507ebf1b5174678dbe5db99d8bf5fa31b7ca4cda8ba2b3e4624d17e564cd6099ac13358266b048fc33da92b490f47a205eb11c93cbf68b4b8c17ac476959ebdc62d05eb0588fa2d2b1c6331db2e9bfa1c80b1823d2ac71b4ac65dc630930cba31fa8be358c398c04c6026301318098c04c60063000d21763ed5c9d5039ebefd8eb601d6c03ad8075b019dd8075b00eba5bae96eba5bb1f237540fb782f849bb1f2375727540efbf875b00eb601d6c03ad80ceec03ad8033ff0cb8c9f64f0cb84cb41a42ec7dab9233b2fbdd7ac0ebd6075eb0677d607a82f1c1ba8cffc3d787ab030de3e4eaa1fe01a43c346eae4c0f55f7f0eb63503ad8d40eb601d6c6a0ceec6a075b1a80fa063017c24cf8391b9303bef81df0ed81db0643b6076c51f0e0182bd9ab97f865cfb564f0cb909f64df6eb8d41a83506a0f1ddb97f819c381f8eed93c10f0d1b930376bef81df0ed81db0643b67af628f8700c15ec96909f64c0d96cbefa5c52846d395bac51f84851f4528472942369c583bf4a11c1e583c3ca3f090a3e8a508e52846d38b077f974a1477e3add6eb758c847262c9932628f8c09ae4418f9349935d75149b264aeba8a6636d733417af358b334db5ccd21f0b334db5ccd21b6eb5c3dc9b7fd0fe30d62c984ae0ccd5c5d1218d62d5d2330cf11fb67c2d5ccc6b16ae4e0d33d98628fdd6b830482681f849a4aeba8a290290094c5201298a4025304f100494804a6ceebb55ba1ac42625767628d495c20ae9904ae342ba6ba4e42ac64aee42ab8d174897fd847a25710e19e761e9a95e182576765d5c2b3be5fced67cb7ca7fed355)) else (if i<19 then (if i<18 then 0x4f2af9aec35d86bb18025fd7b278d760348766a4d7540ddbe157d835060d418025d80f5bb6c1a832d49aa37bbaa07c67693d9a93546eae4ea81f0abec1a8306a0c1a83004bb01eb60d406486a4d6570a38ce4f0a3d8c86a4d72782decfc7b61ad8c7b61ad8c7b61ad8c265a0d216546ea81f2e843ec35c981f112132d0690b284f57274f1f6034851bab93aa07a71bdcd761aec35d80c12febd86bb2a6e40c6719dd4dc0e46e4c0f7be157d8b81c0c5c0e01962e07031703818b81c0318b82b021a995ab851f27570a3fce2fc86a725d70abff3ab67cead9f3ab60657fefc33696ec9563afe57bf68b4ef563afee52aef59edf5b9cd68ba29fb45a5e7471b76b137159db77a2d2e35933eddac51c36777295c6b3d9a547591db81b2e06b5644dc0d970365c0d970365c0d970361b68f55ffaa4ee613e6aeed20e3057d65cb48382c610fb3c93f5cc27cd6907aec66cf25f54980ed20e309767eb613aed2457ebb210d4e4c0f864abf729710ae1ca548dae2ca48854910ae1ca548dae2cb90ae1ca43d7160f5c1eb94a147596e7c65b8cb729221526ed17106d0ae1ca548dae2cb9739773d70ae1c1932e2c997265c987db932e4f04d7220cdd73a9e6c992baea28c60316d1669f6b99a4a9f1d1669f6b99a43e80f46eb5c3dc9ab8c6eb998f985a8712b8318c599ab8b8318c5aba46611e4d07fbabb318c5ab938378b35717060999a0a24baeae2a675c5d204a0ccd012833340c094199a02506668094199a3c443ec95c6852dff19fcdc3dd706f6e4d7bfa6ab8f87b355c1bc6b8b8fb866e0d5454104541c41aa8a820ddaa8a820ddab497937a90bde546ea4f049faec2d41149a888324d46e869e44186004c1920884c0981302604c915ae3f242a0724528aa5764f1a3c68f1a3c68f1a167d5ac2dc210e494058a25332952bb278d1e3478d1e3478d07d2901a2e8c8f2a0acdd5a73b8fc928291129994a2a95d05e3478d1e3478d1e3478d06316ee527a48dfd9d592978a6541bab2a0dd67904f99506eaca83754598d27f728ed82a5f09d992978a76d04f99507a7d9507a7e3bb353ab9323d46691ebbddce63164e53ba4dec276756978a6104195841065610419504f98410656104196c7098ed51140d1d35df64a9ca0f7204e3b57275723d46690265acb1c25f6a67628904cb5963b5724492fb50528c265b1dcacb22820a8694c70b2729dd24720a8d3bba97bd6fb1973948b2729dd25f6131daa2494bc5311c820cac4720832b11c820cb1c827cc4720832b0820caa32919acbb353ab93e9493d4b6a546527a96d4e4a8c8132054bd9507d32a0fa6541f45c827cca83eb7ba9c9519a455cb6a77b503434c62c33ea774849041574bc320810f41021e82043f7b410be410d5d04087a0810f55cb486a578e76d4291b410be41065be41065be41065bef else 0x165b20596c8165fdc0b2d903d3f583a7eb074fd60e9fb3a7ece9fb0265a0d21763e09894fffc7d81d3f583a7eb074fd60e9facc058d80b1b016365fb17ede9b7cacf9d656c3595b0d656c3595b0f9f95913eefe43ee19e6647a8cc864bb51ee66bffc832e71992ed5ea9d33fdd3230241b1c33bd63b50476a08ed4133f1c11da823b506a08ed40a37ef1693ebefb36bff7ef119b35a599f7fbbcceb6e3fcb482f1fd9a7b98efda3c2cdf5e6e12e9afe1660045f2dbffd802b35b42da16d0e185b42da123f788cc4da92b4db733f549f357769071848ba2208b719fd88e23302b01318098c04c6026301318098c00c7a90fc4664bb5b1d169b6e65dbfefb744f576edbdac644f5999efec92b68be371d86f599c5d3b18739295d10c247d36ab7e28be36944dd98c2284c6026308a131845098c2284c611426308a031845091eaab86c8c67b5257efba651029eb9f8781fbaeb23920690eae4ea81cf38d36c026d804db0063b0063b009b60136c00276fc7d4cd8b8284cb638e7aa06edcefe2e9b60136c018ec026d804db000bdec678e4bb54eee91dea43c9c8c664bb566f75fbee99168229fa76e7e1d3bba47249346eae4ea8182b8d36c018ec026d804db00320dd574cc0acbba0996c71cc4c919edec6132d0690c71cc66c633a6f58137ac09bd6031f58137ac0930e46e4c0c15c601c01c01c02b0c5fb33a05252d39b2f9203fe48725c6e8143506a0d41a83504cc8ff5498c7919dc6338c7182c15f8638c67051893f119d860ac3adc89224ef8a7accc8f6c2263cadb028b516cd2116eeca98f6dedc345bbabdf0db77745b37db86cac68dccdb08b34ab8e976324439303380a31c74a11ca508e52847294238bbff337e12337d14a11ca508e7c3bff4a11ca508e0f7c1e1ea508e528473e26d369ba508e528473e26d369b31e942394a11c65b196c65b196cd99bfb337c64239f264c999bf9be6d301a63b3fdab2b793ba857f8d41a8267c35176a0d405c621d2b7b8a5cc7fa56f277815fb81c170382e2f447c970f5dc2e89e25a24bbc28fc71c4af07d079c2778b1fae58fba2b9e5bd6bdd9e93c97def3ef73b361bdd16af7d7633169ef7ae58fbfb4c438b66b2bd6c349ecbb19a874adef5a21149ebd9673fcb0701a8701aeafb4cfbeb65a244461cf2bc4f133899c4ce1809933819c7f7a02d0fdea43b80be565d1029e7ebf00dbb35e36911ca50fde4d9eb37fc95c21c16cbf35fa526bc6b2266305370263053702630537026305370263170063053701eb6233da92b490e57f8fd0e94976ab057bd527d292c4eb514f14a2f8cd913b733f1ecf9f77adf491f7891889971118528be358c3980c4c06260313018980c4c0606030fd7e3e9480d174678d84799d8bf5f8fa520376cd8471893294511d64c06260313018980c0348766a4d75727540f6) else (if i<20 then 0x1ef0c421ea759c61261d6fa6e613e6aed0712a759c61261d6c7bc301f3576254fadf0c275da0e8055d59cfaa72607c320d4b8847295236594a1475dbf211ca43cb0787b1bed4910a92211ca548d96637974910a92106d08e52a46cb31bcb847064c5932663664cc69f18c062da2cdae919b1bd353e3a2cdae919ba407a375ae1ee4184d11e5cd6631666ae2e0dbdd7499bb308fa6bb97663598c5ab93834cfae662e0c128aecdc24572efdae2e9025fa8181293404bf5012fd404bf503db9f35a71f9215cb92b694a2f8c157508421007f82aea10841acc62ca774f028df76d9d5d4ed1513e4d9e2176dd5db7576dd548ef0f66a75726bba809985bfd18adb9eda63164e53b817f42767554c9f8a63503b75137510b1a81dac6a076b1a81db7d8e9aca496faa270f609d8f8271dab93abaeea02660996bb1f04e394109a2948e4e9327fdca38e529a9d13fdc2dbec65ce6b29164e53b815f612ed1daa26a768a89f62381db1c4d8e2162381dac4703b58076b35daec7db353ab92a7a05e867ec8132c9f8276fa76fa2e2176fa76fad185f03b6f81db7dfd51d99b9755bb2f125067ea53467e27fb89012e1d4e4c0ddb9759d078020f041e19b820f041e083ca7d466e5c47cfaa72544e14a2ac67e28d75323165138566e2b973adf01d6f80eb7c075be03adf00af2e0ca331f76689899dfe628899ee3f73cf480efaa4cf01df599499fd2a5f667b3285ccc31130214c44c44c44c404cb5d8fb66a638e7ab927149993f847357838da58da582839a3c531182420be844239abc1c6d2c1460a2923048508847357838da5828c1452460a211cd5e0e0a3051491828c1466fbbff1dbf4a55b34ad1b9299d8bf5f8fa520356fc7ba23f2e66b04cd6099ac1335823b45f96f8df59c786b38f0d671e1ace3c23b49fdca2762f7bf59c786b38f0959c852b390bbbfe4acb7f44ace42eeff9ddf2b2dfd12b390bbbfe777f77f77eceefd9ddfb3bbf678ff97cc6f63e2dbff2f96dffdabdcbe6c5fbc46797cc0f45081e8a103d1409335fafd6d36ab7e28ba3cbf9d6b6c084cd6b6c084cd6b6c084cd6b6c084c51efd56f97cc6e4a6762fd7e56fc7972fe666b04cd6099ac1ed8b477dd03a299a59251d06278df58147eb064fd6051fac0a3f58327bb60d213e8e399769d4b89c263bc7c5c67d60c9fac0a3f5832782d3bbb57d4784cb638e7abf1a27b3fc5b329db9dfa6b164e8ed4ee16cc82e96131daa82a39289f58327eb028fd60c9fac0a3f58147eb064f18ab96af1cf7b8d13850f1705aad7a06a39289c038038038038038038167aef191b8ce335bf605ddfeb3c654faef19d16b693f119f5a30241bab13ddff0a57027211c95c295c09c847257f327d2848a52b15d10a57027211c95fc8187ff08e4aec793ec6a3ec793e11c95fcc9f93ffb51f0a57027196c8 else 0x3667636de956fc7c6d33d1198c04c6026301318018c01345fff70b557231992f776bdca39e358b20f738f333de390cf5c76027b3d60581816035d816035d81609eb02c06bb02c06ba8e2d9e84bb47135d4616c8c664a43eef704f3232ec7dab93ebee999979ef35d04cb5d8fa38e621363b8c322c9ddc13cab2e2da5c76132d21763ea98e39e48932333d743dac2c03dac03dac2c03dac2c03dac2c03dac2c09ddc63c945a6ff714e49ee21c4e463325da8b59bdd7efba65ea0b9a4d0996c71ce071b51231f3d16714e49ee16acfd3b73f0e8326ce645be53bb85af5a584cb486a638e79303990426a31f3d9eb1a80d7605827ac0b6a035d816d406bb02da8317c599b36a3aadd4a3e01f92e9989135d4b4f8e6cb80fa192752d213ea939e4b2e03c5805b506a016d402da805b500b6a0184d8cab5e398740fc725fd76a1a8c62ac8578e61d9303f1c954ff5d8580380385803858038580562c143b1b6f885fcdad3b31df6d31d2a6f1185f43ceca5a547e3a34d1dfb371c27a5ede1623b3dadafc644eba8f86f2dd51ecc272971d4773fec7b1f1499e84ea3daffb77b36014d2936f8b4a26e94814814814804c0a40a413b443bf4ff51b0fcec62768864639dc77ab0eb7d2bd53e25a41c6276335be1f8a76cbb0eb63de1a4889d8a16bb643eeed6d9466b1641b64e6e9ae9b2abd936d877b76d85a7a13a23e16417ed14f6d9ba8b66cae8e35b28cd62d2accdd61f8e4885da3b5229eb76942394a10b1c4ee942aece528470d7f94a11ca50858e1aff05a942394a10b1c1ef82c3c3c2d4a12290b2114a11ca50858e7c1663fb1fc5b962d4a11ca50858e1aff05a7a2dcb1635c5a942394a10b1c65b05996c65b05996c1665b05996c161908e7c982d3260b4c16982c6d305863b5cecff6acad5bd7de00b800028773fdbcddf815f73fd2937fdebef00ddc47efabd0e00e02e452d13c26fc718d079c71c70bd2ef2d12bd966ee899b4ddebd5bbaf6fabdceedde26e5bb96e5a25eacb350e445b6ef1333726a1c5b6ee899ffaf6589ffb0f2d9a87377452c6a1c06a1c063d172569eb65a246711273e670c04c99c4ce26703386ee6d53d154fe69261d6ff9b6d29f1ac1198c04c6026301318018c03b1f6cd4eae4ea81cf6c0cddf65f580d9b365f763b6ec7daa07c62e18bbec2efb2fa5df60c9f70a39f54e4f05b0c3dac03dac03dac03dac0f56efe3eceae2a7f0f66a7572607ab80cddd8d417d6350300c6a063505f58d407dab851cfaa72407f153b1a818d40c6a063500cf1ddb8adfd4e4c0ffaedc2cec070301c032c070301c0c0700c605619d92e8ed686b34def43e96995fbd5817fa54deb29739f58e3b8e9be9ca8b9547446ce3ac51f677d0cd33d58d2a3ace9591d0d80b1ba1b03606c0d81b0361b68f0c3de1dcc27cd5dda41c65f562ce31875b))) else (if i<24 then (if i<22 then 0xd9c4fabbbea009d4013a8267c240275004ea009d4013a83b7daf742d37f8fc2f6bdc33e9bffb7a1623664de9dfe5e85f783a17f8fed6c7eea3ffe86f69be27215e4dfc90742f24010b0e0fe858e1fdfbd858e1c01c02b001f8b49f667a180fc686d3750bf8f7dac2c46cc9bde00273741e03c0780f0dada00f3c7471b7bfb3f1d16975fdd7663de8fe16236679fc8f4901f8e8d8f7599ff635e92ccf00139c70780f01e03c367e803cede161dfde93edd89de89fdf0bedee791c2e87d8c3a17db88d8c3a542c47b72ef630e95bd0b89feb64985b7438038038056033136a4ad36decd86f543f8c95fe7c95d5ba528be318cc22c04c6026301318098c04c602630033fbedd14f12d5e8986f5252bf6fff7f90e8b9a48fa520356fc7bbe36945318098c04c6026301318018c00b467b5ba92bf76dece7896af444b66a638e7ab93aa073c1b062c7063fbc18b1c18060189e062c7aefb31daae9e6c632eb6755986ff1d84cb766a638e7ab9232e7f8f6b00f6b00f6b00f6b00f6b000f74cc03d9be7d972403feff195273c901ff3e4818d40c6a0635031a818d40c3f5fbaff66250fbba4fb0fbb8c39c94af6293b5f1117aff3b6be30876eb0e6417af1873caec3ada4d7aa7f9abbb483e7496cc0446d7c449f184b5baed07cedaf8f712c3adb75cc27cd5dc82248a1690edb2595d998d06d939ba63decac6c9b6c3bc5bbbddf87476db3255363caa2b66e98e5599bac3f1c910b2ecc76a4431bb08e52a472142394a91c85f211ca548e4285fc847295239087be0f0f42394a91c850bf963d2442a48442394a91c85f39708e52a472132d8cb632d8cb632d8cb642383267c993264c986c2dedffbf21cadaf7277322dede332192ed47b518ce1c976a9cdbf43ee518c0976d51c9d8b63b541b7e382389b1daa11daa11d1b5423b543c5a5f7f1acca3f119e8b4b3546ccfbefbe4d440bb8f24f6d02934771ef3dd27a67acc897be2f9d84d7ad02a8c1735c41ee6bd2599d7519cfb8e003dd99c77e824c1fa0fd07e83f41f7f3bb1e969f13543ddff2441d3e2d3c9122822822822822858f8b4a8cd30fc6f271e667a9363d3e383e4abe4999ed8f8e0da797b52707ed5ea5e9c1aafe4e3874f8b4f271d141141141141142c7a5a45be29dccccdb78344a31efdbb9dac4fe44bddbb985f79e7908bb7730ba4f245ebf76e17dee489dbb9de1ef922b94942299f83f6ded67bc914cbefed7ff06210fbb9edb693ca67077233136b73e436955f3db6f93eff3def23df766bd270783b9a5dabb73def23df4f255f3db9e489db449dbb73de9b6f6bc911ae06b81ae06b81ae12bfe2332513476b6da8cc7bb75deeb6ded5baedb2fedbdadd6308b0e671743f8c39e57257511b6a2f8c6333758098c2284c611426308a131845098c2284c6114064f495b55bf1f245cd4ed17 else (if i<23 then 0xf3c1879e0f34ddebf76c1d88ef646138768b7afddb0768a9afddb0768b9a1db30894c97ce14c97ce7cf9e5325f414c97ce7cf9ff3ca64be7297f3e97f3e97f3ca64be7367cfd9f3f67cfd9f3fe7cff9e5bfcf36f9f1df8ffd781f5a0786b40f0d681e1ad03c32fe73f8ed3b06a7745ffd681e1ad03c003803825613f392b09f9c2ee3df2b09f9cb18f7d8c7be5613f394b1efa58f7ff63dfb07bf60f7ff63dfb07bc62ae5a435273f9fdfc3506a0d41a80fbe1bbd6edb4ae0fa2d9a63dedb1f793657db86f77e116b6d99f7b361addb69541ff6cc6dd166695c1f116182b1f8e132d0690ecd4c71cf540dea4907c60b08538470a708e17729c2383c8b94e11c29c238cb632d8cb632d8538473e4c45e64c2de61b4c8dd5782e6f0ee3dd457b98f9c18f9c18f9c18f9c18f9c1578229ff37874ec18af731f3831f3831f3831f3831f3827770a84f2badf386b7ce1adf386b7ce01da4a7388af724a70ab8f70259ffca779bc3ecd3857b98f9f5031f3ea063e7063e7d40c7cfa818f9f50120298301c0c070301c0c070302b015c5f66cd86a0d41a835024a70ab8f7000700700700700700ac1e61b4d6eca8adb3369b2a4d15b666c35ba138adb44f5bfc35fb6edb3cfb7655982ff2986f9c2986f9c2ef73ca61be73e5cf45ee794c37d0530df39f2e7a2f73ee794c37ce6cb9fb2e7ecb9fb2e7fcb9e8bdcfb9e6d73ee04779b701e7715b079dc56c1e7715b079dc56c1e7715b031f2c4382f5bf51eda2443cfff6026301318098c04c60067375b0690bb1f6cd4a37540e67fb0307bcc307bcc307bcc307bcc307bcddb5719dccfd80c1ec060f60307b0183f9a132d0690bb1f6cd4bad933fd60c1fac183f58307f341a43c3d9a946c0f54cff8635060f60307b1a8307b1a8307b1a830789ff3be066e076cb81db03877f60cb82bd8427d5227f75c6a0d41a808787528d81bb09ff8b81c03370382e0700700ef8cb82b024132d0690bb1f6cd4ea81b299fc2b870a70ae1c2994e17f73970bbc2b870a63d7160f5c45e942b88a4829c2b870a65385fdce5c597117e5dc29c2fee72b7a5d6f4be5dca5d6f4b8570e14e65c5932e22f32e4cb85bc75416918fc110bb1f476ac57fb566cedb7093e0110fbe394cefdb3e8ea6f24e53b94b1fcd918ff9a12ed1c26a19f8a8e168e168e161614431cc88705b30ae9a9fa99db30659f18431cab3b66c1e33dbe941c728cdcd8e44c8e0851d3111d3111d3111d3107deabf6ff97bfa30e54240ab76a95e399f753fa33fadf00adf0adf0adf0adf0adff1ea0cf90f88f909f548b289c18d7238ca270655ff281867b67dfde9425e8525fceb7c075be03adf01d6f83fba0a7fdce628473578a53fee73162a315108e6af171518a8c5462a05bbbe33b6c976af3b3ddfb6c95253b6632e725daf74cfd0d3b6608604c709ebf else 0x2c2c2c2c2c7bf163df8b1efc589b48e504da5cb014136972ec7c9bbd8cb1f9963f310505050505054505082acad310662080a0a1050786920b8fcc4171f9883fd1882e3f310547469a23691b41ed0e7469a2369a72f499a4cd2668cbe368cbe668cbe6697d8cd34d34d34d04104129bbd7ec5b6bfb6a6ef5fb268b4d7f6c63dedb57709dba7c63dea0bf75ded9ba039ae9b532b5ded9ba6bfe04697c8472952390a97c1ee5ff4e12295247c452390a97ca3ffa7cbfe9f2e942422952390a97ca3ffa7cbfe9f2fa74b8e1972ff674f865c32e190c390a64c993164c7bfe3dc44fd395fca52b15d1d395fce9c0cad14ba72bf9d381e9c0c0c2f1e0786503c32816513c0f0cb509a84d426a115778abbc55de08fd5f223f57c88fd5f32bf0ddec8fbb1bdeb2b23ed927ef7c0f23f7bdd1df6d03c37bbc36d1bf676c03c8f452a0a3086a727881e91c854be42452a48f88a472152f9d3a5f0787a11ca4abf4d57e9d2848452a472152f9d3e9f2e0ffd3a5c70cb865c3283fece9f0c861c853264c98b26034c5dae63b5656ade4e9cff11c247091c247093d1c24709c3f2f05fd7f87a1ff3f6df43c1705f82fce7cffd7e1795bc0bb768782eefffe7f4b319543c1761afffa598ca44920bdb02fce7cfc17f5f00000763ed50376f8c5c7bb000bb00edb000d21763ed5c919e07b8f6b00f6b00f6b00f6b078e8b49b7fabdd4653e3a2d34d965ef23dfb467bcb04f2c6bf3601f25b84e5212c0a5205205205201302996290213ec975c0f711fa8047ea011fa8047ea0a525dac4face7ffa7fb0ff85bd2a8ce7d7b8f7876907180b1dc670ebb41c9088eff549f4f35763096d477faa4c7bc3f1e6aeed20e30e7d60f787cd5dc8292503dc976abded946426ba68b77477cacf7b6f6e1a2ddd453ded8279ef13c35fb456cf3fedc3656362fb651baf4b213ec9819c19c0f7a472142394a12295242291c8508e52e9d2390a11ca43c3d0914a921148e428472974fa7cb8472974f960bf4e91c85b196c65b196c65b190c390a64c9930da66b77bc178908e86c0d81b03606c0d88a5d31e1e452e9f4f968a5d3e9f2fa73264c99bdbb1f6cd4eae4a943f19d9d9d9db3ab5de594901a43b353ab93fd527b8d59dab3b5676ace768ed512bbcb29203485d8fa3b5726fb527b88ece8ece8ece8ece76d9d5aefe94901a42ec7db353ab9223ea3c9ec1fd60feb07f583fa019300071920884c098130264b4c9810a622622622620faa72607aba1f899f7bbe45f22f9143bb292dcb90f0ea72607ab9ee2677c8450f33feccef9003fa503109f54e4c0fd3c9e3adf01d6f80eb7c075be0847356b536e92d65a0bea26da211cd5ad4dba4b542d65a0be728847356b536e92d50b542d65a028847356b536e92d50b542d5108e6ad6ab542d50b542d51cdddffae89879e0c3cf061e783)) else (if i<26 then (if i<25 then 0xe184ebb41c157784984ebb41f8ae8249f0ebb41c15778a1d6f8643a95d05addc0982d4ae82d6f86a02eba0b5b09d76852bb26b7c34295dd764d6ebb4295d909b5d7903f2c9b5d792bf0d0726bcaef2e264d795d7a92d6e67964dae9249a0e43bcaef0c1643bcae84ebb41ebaf046baf1ba227392e1ae82a221f8407aea2e1aebc21ebbc28b975be105d779784175d856bcdfcc92aeebbc28946ddaef0a2343211ae1a0f1abaf0444494af1aba0a8bc78c03d75ea4b975d8c8b67cbaec64519c6ba0a0890ce1269766415d6461de2fba4e1269764e126976bb41c63344822575f58b0ee47556689158b91876cce365a77161dfa2edcf9907cea871573e6feba0d73e63e6efbae6e28612619766417a0ed3b17eb09b0cbac3adec9f3a26882be1f3a5ec9a6c0b7b35f1d1f1b48c3cc218ee8f8330887cddfb24d147c8757db6047ceada4be9f377facdc172e2ed8141790fb3af8cbdf13fac3fc675f7575a3ee09c540756fb6a7f15b6044a57b4323109764f1ed46212e82eab1887d8bb242b51884bbc3aed0718ccc30575d1c8e48540fd9a2554f7e26a586cc57f8a1591f706d97ed8afa952e8f6d4640ae5c60f633a0dcba237b50e187adde1318572f1db8e8d39d770acaee3dce85539d109b4669fe3a21368cd3fcf4eb469c138ac8dbbd9854271566cdb2d5b23158ae3fe77f8c24c32ebd417cfad1bf69c2b23fc8a8ad3a97f5c497617a892edf6c32eb0eb6ec4319d0828e7c218dc6746c0b7bf8ed19d1b48c3cc218ee83308919bbdd88452015b2cfedea429dd496cb3b77fa056cb392718d6c0beded1d31fb7b62ae36cebaf7c9ed637f57bf264abdfc23df26ebe370af78c75e9df0af7fa29c7bfa29dd7fa29dd7fa29dd7df76cebc612a9fbac6e1119257fc7af6cf130be18dfd09ff1ebdb3c4c2eeb1b86170b67bac6e11149a0e3233330c17ac592150dff59a2554f7e2554f7e2554f7e26fb61b30a15c5c8fb836229d15f58b663e9235d5d0a1189fec681e26eb1a0789ba9f3a8c8a26ea7d1a3761dd6340f246baeae28612f51b8510b417a154ec5d0c57162b4ea5c0ff1b8625571b862614645c312ab8dc312ab8dc2c365af72315d0fc0f230eb60d3e8ce841470fbe3ad1c6046d07f03faf6cf120d3e751846155af6cf120d3e75184cdc1a7cebe1b4689f19b3ba3e44644c2ab5ed9e241b1b84451f7dfb0aad860d3e751849185560d3e6ef8c20a3e43a59db4853c6f47cea24a78de8f9d4494f1bd1f3a8929e37ae1898ce8fadafb61eafeada424a36d1a07518d6d038764ca78d038764ca78d03871229e370a20ec99f14f1a370ec9b0e340e2bb68d240e4895b288ac0ec324328785128d1663ced0e2ed862768b67c3a2cd682a22b6c4bea931919c5c60beda0bae2b6d23a8b4d19d9d9c72d3467676700a33b3b3b3b3b3b3b3858e50 else 0xbe631666f4a0a61974728ccb39ae9a522dddf4a68d381770f270ce223dec9ddc339b7251bbf81bff6b3d8649778ce894c6fcd3fbb5a36d69de27f8dddae17eb3fbb5ac89cd68a4f7e7f6dd9a85facfecd2c89f26fde21c6b4645a59aeb3362fc6bc4677a9255d8ece1da2ab22f5f134d30d9986cadb76ef555d8e4dfb6735a2abe2ea65eb937e0e35a322ccd3ea677b1873caf9325daf768fa77223feda5637ef599c5c612a9f41ebbba88c2e66548ffb67afcb7727215fe06e6c6de35bb91f36f9868ae16ad6ddb8c2553fcb8517c8f662737bba77d38128f7270cf228a7770cfe20a3386952523f77044945c63382bd517332b436d937e9115ed2b3a7e579af5b0cbba071ad1916986ac95e5d4a6a45652f937e4180cd68bf7f2b0bb268334b3e726fc1c6b4645a77ab3479764e94d488af59934bfa7758ea976e09da41c163087e1baa6e5a0590fc04ebb41c670c39609c49744411cff5e184f9ad1cfab457f87a8c0990ecba27afce86d90570dfe7ca353b86ff31a6df923ff29de47fe7c82f9c6ecf415fe5af6613b80b51fe51bf087d061c693bfcf99193666857f9d27bf11b226be53bfcd984dbaa3a2052b84ee5a249decfc9e355b34a3fe7ce4cd277f9f223f5b84bd867d9e0be563486ee389ff90de95638c97d9f124becf8925f67c492fb3e2497d9f120be5fadad2b2d7f36bb6d2aca5c97192bda71862543b3c61289d9e936e21d405dd45375cc27cd5dc8a5d454ccc7bd16eec6d4ee9266532316eec6d4ee9094ccc7bd16eefa8da9218e462ca330661d6db887a15041453234e8da4f53b81276f7fa8da893c122f7bfd2893c514c8c593bbb1b53ba442251ba63de8b777d46d3949357318b27281a877d31b37a526798d466a9ecd86f7505eb2321e09b7a89c43ca45bbbea369ca4930fba1489d227d21d22d3cbf0d59a3f26fd13e9e5f58eb47e4df83a45a797e9ab3478f7869ad20e3017c70d07195df0c349d76838ce18630970f92265fc7fa7cf5f37823efd31bf337bd66717184abb44cb94871afef222bc8a3d2c7f9a22ff1aebe66f498f786994ba82c5483de1f362f5da975153335d345bbaa2f7dd23b26e6aee452ea2a676d16eeaf6a77484a666ba68b777d28bdc81a2599491f7448661d6c7bc34d42a0829875b764c0b50414c2ecbc270d77ea02c4786d3d97ea726dd77ea4732058a91875b76e6c5ebb504148bb68b7759abda9dd23ce237edb45a87dca2762e73a4d367444928db9ae9a2dddf4a2f69d23ce9ca52e194f51333e877d35a9236699ea2224308a9121831cead24c8e7ccfb70db6c8d3b929dc0ada2dddf4bda72923cea2710fa9e8344c291a9121a394664dc449291c03e1365b3c7bccf2a773cf230f309ecb391310e850e5b7faa8729c03fdc09099847a13e611459c82213395007db7e127c309a80bae82) else (if i<27 then 0xdfea23afb88ee08a7c507da7581b01ee7e1ed946039cfaf705252b8ca1111ddd735cce74ad0db088239c97d7986388eee2f3e8ad81496efcdba6aff5d27d357c779de3f3e9b74f5dbb5893823ef246d15f4d5e2b4d5e0b3b1a7d15f4856b6ecd937b1c91b64d35796f8eeaf0da16f899f43a445790d67693d848a26dd87488634b110ee1b3b1e896957eb23b45f9b7fbe8e8b7bad0b7c778dce74a3c0fdbb3651c118e4b1bfdc57ced24714b3471fd79ad175434a7fe70ae5e401d0a3754960cca7834b449f719f4949689b6e6b88768b07f87b639fb795e77d3bbb57fe53887deee4e82eeaea1bdc2a13f35ba2aa7fb6f9e6f0edd5dfc56dbe4462bc1f70aa77378715db0aa4fba86a738f70abaee15714ee6b75c6d9e7f445dd7c2dda769dbb745bac45d44e03fc3299d9706018e501643b259f513887e394664dd06030e35a322ccd37516d8a0c07b3f8c8b4d0fa7fbbdb70e6bb7442df9b14180f67f135a2aaebbbff7fca7506bdb39a750bc5a4ac767f10ed1559134d3bdeee9bd3abdb3c8d29a85fc3ef6dbb745628301871ad19116c8da5eacc83a5914deccdbbd4572a8bd37506bdb39c4deea17bcff774aa73767a57b939ba33936b63f772a70cf6b63f772a778fecec78921db6267797d85a0be4958daedad307eebd0fe495adfb4b6d83f1ee2db9c912db6ce57bbb0c14aec3adaf54f896907ceecc612b5fe57acadb72a2cee27d3b38748b4f89ad1ba8b4c7bb75de56daeaddb1e934d3e29d8b73b55d8c4fa7675516f89ad17532eddb48cdfe885b9d9255d8ece1cab22d3e26b469b32edf0f4db6edd167713e90e916916b31ad1f532edf0fea87d17f464af13daf72769c2d75753dee09e645ad94fedde1c5906d8176e82f2b6dcaea2333c38ad06da9b8385888b38a74f5d770b38f73a4eeeb9951ed3b4e1193b9c5393b4e71ee4ec114f8b4e9ffd3bdeee29da2714ed11f7615e69f03e2136334f5da768877bb6dbe4b87b64ed46c304c2bc212714ee6459bb6ce2885b13e94180e45a5674f8af89f49ad158ea579744cd3a594b8b5060335a322d34d582bcb9074a6a4686b227d3a322d26b7ab0579744e9644d2c15e1afab0e7e6b4ad257d05d0fa6dc1baf923f834eeea47fe02419b43a4457d0fbf07f0320c391b229df07f3f7f253be73c11f457c1e9f2d6191b834ef6bf82dd0dbfddd7c69e869ddd34ff05ae947fc03fa1a37e2ef099219ce78b4118ffdc57d3e48e1a868d4eff2472433df415634f23d4f91da7a55953c35f56789bec8f6b5807f23dae9562ef18ad39ee7cc49c4e7ace30944d4e3de190f8352ea2a676d31ef45bbba353b814ccd74d29918b7754d1f702253335d34c7bd16eefa534608d663918b28cc1bb99b4d5247dd41e0b06dbe8683d3ada532316eea768d4ee056d31ef45bbbeb469ca02cddb7a89d13e2 else 0x2499488799a3e428a09130e7218e142becc83d27ef20b1ba3f0b1be20a9b266e8dd1f49f8ccdf47e3a8999beac14241f8d0549ea6380df5246a2869c8452272007e624dbb202d106e7a3af3250d1b234c6235a6f38218879e66ac14236b6f2088a991d49999ff6df7c28666e12fd0481593fbecec89c12891710cd5040866ab773b04329a52859c76f9018352be4772cfb4f11c04b0166eade2380966315b3646cfa9f08d8ad71c5fdf9d84fc97f718cd92e16b12fb8f71b84b61c552afc87d2fd15581550df0cd4b86dd75dff4709faa93fd1c27ecfdb09929b7c7133fd47edf0f6bf0db97c7d2708464f813f1f3631e232bf2f8db8c39e57f8dba4e108c867fb8fc6de27d28301ac99dd0b445fbb6b3f83fe83018748b4ccf4d582d89f48748b4acdecce2db6e1f7b67f11959611b3f98f3ad9c5bb9c6b95e5b611369b299c1bff72bf937e4180c3a45634f4fbd7bb6dcffcaffff4180c38d68aac8b4c3563d726fc1c6b455645a77ab1eb2d73a2f52a5db6a181f9514adb02e4dfbc43a45a7a7d628fbb2af3f6cfffe57fc43b455645a4d435628dd786cadb7aff89ad1555eee9628dfb456df3f05febcc23a2ee4dfbc438d68aac8b4d366562205fcafa2ee778fdbbf5cdb37d8eddc8a3d5e6c5bd7bc2f3bf6e1af735a45b305c07c5c44408e7d6d27cd695a4b87638ef3373f0e2b1641b60da2fdbb759bcd8b7c93df77f95c405a11dce7fc4379ed606e7bfeffea210ee23bc2e7b8889d7dc4779eff511d7dc4779eff511d7dc477053)))))

def seedScores11 (i : Nat) : Nat := (if i<1 then 0x182d7d190b103a032d0f1002630b10101002002d7d0b1063102d0f101002101b0842174025360942170038253502294a2a05182a00057085002305000f7d0b42352a4217050f2a421705298518421708420c0c0c0c0c0001321a02001a00001a00151a0200021e00211b01014b092f014b5301090132013209010101115e23015e2301012fa5011501155e23011b120501122f05011512050115120501157e1bef010115125e23050101151205010132013201321b01010132702305010132011b00004b09004b5300090200000922000f0d0f00230503002300340005001b1200051200051200051200057e1b12000012002305000d0202631014020002021b0000007000230500460e49072b1c2139113908034a0532274e0506321b084a05061b124006272724271205240532084a051515326801010e21150e0921210e218f15210e21152121152121216800150007000054000000155400000754000207218b02070c8b020c8b020c8b020000002121008a002100966674967466000a160111031600010001000111550001000a16010001000a0303000a000a11000f041500152007200f050503200b24060720410b240b0e363d0e0b090e0b0b0ba2200b050e0b0e0b100b200b07042007040b0905363d103a09103a2a34052009102a05063b102d2305622d20052d103a032d0f20102d0f84082a050f032018033c1803294b4e3c060f1003050f4e034a423c3b104a420638363d103a180f4e38093a2a3c09102a130610181a03053c0506381a103a030f100f384a2a42dc0f38063a381a0313064e08034a051b913b084a2305444e2a5d05446f3191262a0512265d052535084a2a0526080b180918633b181a18171a181a0326060529183f0329187803293f1813187818173f3c181808131a02001a02002200510d000f51360d3d02461f090d02000200513b0d1002000f0200230562510005460d020010020046020051461a0200022e651c2e1c2c4c1c084c4890994cec06eb1f0803050a00050021220007050600000007390302008f1a000aa000e0031d9f031d46033c060b030f030303030f03035503030300161101110111011101030a030003000055030003000b14060be9410ba40b030b03171405040b170b410541081437100b0306410b030b03170b08062403060b73890c0a2f2e02212c0339152c15002715321568680121152121152121685415000032211402148a210000967466740300160300160300160016555555030016030a160300160016030a0300030300030a030003000411040f040c213215159514070b0b07040b1407040b8409100305060f4108340503423cdd091a42061003420613423c051003291813423c423c05061a3108183f5d260810db0c2e212c2f151a002c151f0200111c65f9153948902c2715 else (if i<2 then 0x3402020c028a024339151b00011b1f001b1f001b1f001b000a000a660001240c0100010c02430a007000239700700023970c0a0a0a1f21b2212121b2002100213030005c8830b009300000001b020030024702020004040e194f04085a315a3128312917045a311c1a03721a031c27110d0400042e921a0d1a311a0d5e0d3435300d00ad460d00651c0503050d05711c083535082b003737745c0067000a000a5c59b1590a072200b1001d074f1e4f4fac4f1e084f86074f1917882c1113881909112c179404131c568819934f13179456071e0409091309070719072b12124f2b13561d076a112c6a332392111c04126a4f93195a310835873119934f87086a04081c0819005c2222000000003500002b002c1943ae191250e72219350056e61922005c2200ad3fe5e41300005c2b00194f292b22130056001c12560622000037082b072b37083708130719220000432905181d09191e3164040918055b1909641d051e04095b31183f1e0418183838031813073c1d1818032918030538033f032904310386293f04121313093f29861308088629133f13181903220004040d291822130d001e310d087803001e0b0b000c000c01000c000100000b0b0b0c000c00040400010100003a3f0f0f3a3f04042d0303032d03032d2d032d0000000100010300030a0300351101110101000300002d0a0a363d1604363d1604363d1604090989040b09040e24091002040b09040b040904208916209507200b24160620410b2416070b240900200b16200b070b070906091605064134162009060b050405040533231e04052024000705200b240006a3240007052024000705201d073324070520241d0733051e201d07331e1d07331e0b00330520240007052d1e06071e200e240d3a042d143e0403143e04143e042024100280200b241014202410021620002d20521480163e202410521480163e20521480163e140b24100214202410031416143e20e80b242a00040b00051e0b24003e0f893e840b24173e040b3e0b1e0b08030934041e3e0903173e0408341e040817030908172004202004201714160604204108160704200b0334200b2422060305060b830b95330b330b0b330b33030506200b248333050b730b730b732020047f047f181829030f2929293f290f0f0f03034b441b0917061b08421708064b050f18050f0b0f7d19363d363d103a4b093c5d053f4b4e532a05190b090910023c09103a2a5d442a3c05444e09df173c5d053f91092a05067d0b440917002609102a442a1305311813173f0b10052d23056223050317230509175d23056203051834050b052d2305038518171a62de1a0340051b12402305061213000512260913000512531300052d297e1b12051800050b0506052d120512298518133c5d12170023055313000503030d3a else 0xea0004e31c220400330456e1ab56876a04234623090e0b49651d0739272b1c39f840230512481d052715053215150100151500150c00210a211b1f01321b1f0e02740e000a01721f19000e8c1f0e8c001ff3001f0e4d1f0a0124b63d010b24363d092f010e240901245e01244805010b2448051b121f0e00670124ee012410010b241b1f0e00041a11ac050403150c32682200681500327f185b5ab0092f44310d710d180200001a0500000200040200f6000a017204000a0100010100660c481d481d1512001d0a001d00010001001d0100010c009701b63d32360d3d02092f32090d02007f320200320d0200523202005214320200ed000d0e0d0071af0d18af0015002bb42200481d15482bb40512220005b700011500010a0c0a1f080000010d00710130000012b30112b3000000003701000d040e0d920527310d0803007135085900092f1500aa5e151522000000005c5022ae0422008722005604000700080056ab00e219092e2b1e00070000430d0d221e00000000001b1f0c001b0c000c000000020404040001000a1601000a1601000121110316110316115511031603000a000a000a000a110316110316112d110316030303550303000100010c0a0a000e5467321f1554541532671b0ef41b1f001b1f001b1f000a191f0a1b98980a1f67041a114f04050a360d3d02000c09090a00090a000a0c020a000101013222006c0c0a980a2f09305b5a092f5b310d1809185b311822130744305b78229404307c18041f0d1c0f090905710f445a1f09227f050a000000000023002300045f1100155e235f155f5f1100015f0001002300002300340000b700010001000af701000a040a001b00011b5415f01b1ff1001d1b121f000a011b121f001d1b00011b750c0130750c010c6e4817001d15127b2f137a1d0115126d17001d120c13006c1d0001001b0001000100010001000a00a80c010c6e4817001d15127b137a0a1d0115126d17001d120c13006c1d000100010054011500010001750c01000148750c010c6e4817001d157e1bf2000c6e17001548001d0c6e17001501121d017b597c7a0115121d01121d017b137a011522001d126d17001d7e1b12006d17006d17000c7c006c0c13006c1e000033015f00010001240c0148007923120079230001000100010c00010c00011e0a001f3900393807390039390000393800003939b559b50d00071b000a000a5900001d120a1d07001d1238001d070e1e042c1a0d1a0d182c0d0004300d7c00300004510d00050f0d183807f50c01750c010c3402320c3402750c010c8a430c340232024352140c02430c34020c))

def seedLookup10 (i : Nat) : Nat := (if i<5 then (if i<2 then (if i<1 then 0x30000010120210ce0020003e002f2650790374cf0080030270020300030040000870cf07100f00e04300000734203d0c20030840000010020011df3f90100020014983490021bf3e100000000300600a00203a0940231bf00215a0230c101702806600607004b0000003b313913a00001d00d03f00418000000a19802500200903100101c25801d38600e0042590b107409f07001102a00001506701c00400703100a00c0d903208701700100101004b2fb0b70090720420ec03f02800203903303600002100001703e01600701b01f05a01a17e42a01100502c0b900900104600100e0db01300000100a0100010190000200610040000e501f00100209501202801c04d0da2301a220f00f03401d0130bc0000bf00104300106700100410300002725100a11d00a0140040c300611e0000000dd00802800300500000204810400000000000431e0090000030000040370001d804f00807104e0bc0150050001d700c0ba0470010000fc0251ce0fa00102a00400300103918f06000602a00006101702a05900409700224b01d01300b05c02d00001002b0650000230ae01903907904800100000002a1210100df01d02001502a00917d04301502500000800002800200400200100300200700e07c00105206a00000e04403d0000b502900c0600d50c900009d05e00417d00100501412000200c17100000302e00608e01a00a01101e00c00101d07101302100d0001a201609a00e00b00000101e00b02900805e01100223e00900800406000b00301204508102e00e01c06701000f0040b90d800100001e09900305004601400f01f0270ec07400800100022e00300001102a01600300501f06603a03800400500208800500e0200080000140ba0180000570780010160001c800700d06f00300f02800900400b0020ea00c06403d00000710c0000000020250b62810d801e01002701c0300000740030000200220000140670591060160010d000005401700000c00600605a00300300a02c0410020350600020e30050050000710040120260730060010010220940360df00201f0f100c02d04500407105b0060010180460230070150130950b40240070c60e417606f00203101a00200000800e00202600300500101b00201f0070040020060440080160a000005700e01701903d07900106402903d0100001dd01700100001400001305901900c13f01c00e00402c00005c03615a02202207c00400200c00700500000001701a01502601d00000d0010080ae02900d08b0140020350100090a200500723900a01e02600109a03300000b00e08d00b0000120090000071ba00900406e1d602701106c00f00f04607b00300804902500505f00200000000000601500501a00600003701e00400906100f00501c00200101506c00303800000100000500a else 0x919d0539ff36f13b671c9e2d059c828bd8a42339191a774ab5491109f6a8ea564f58ce9ef8c73e338722487d35b36ecfb7567ca3802766c6bb6c548d81d78c271f33c515bce84a5e23422a29738cb1f10df262420766821a7a2f463a7723df7024c50927146d2aa983d9462f345aa3211d40e0b2adc07d43b2e696515a1d2c044b8cfebf0495454394b562401abb529839895c4c2034d4be9f12d0c9b2690a42e43431ec59651a2b46ba5aec967a7b9524d0e3c06087c9a3502d10ddbcb53ea7d9e94ce5a6a398155bbb835c902f9479f2710a43bcd86799b7310b6593c599be06387b2408f6602d0356009b991640632be4bbd60000b9953b05323195cb40f32fbd02e359937c18d50dbd463c2ef711852a3f8064f762228fabf7e370b9ba59e38f9528004e17338a114c51f94a0f66eda9fae6af64a46f37278e3bb07529ae65714a5c6cd4561b28960c6761b4c93f9cc75448c86ff4bc9c262ea4807aca034a8c4b2d3ef3d2a60c1e56c46fbb51a142341bbc650a939c657245c145b400aa672498c089b8f0ca522923caca3d86f99f0cc1ca3683f31d82bcb64b4800001d0a9a0c0101bf5b003a000a1408500445d1dc00197a0000090010ec009d756fa07106200008b1f13be03168485c02d4780081a105c00134211a0ba7e103d8bf2b21f20140bb075012a900c201102188005a1d00030002ba6600040002db02e00002300e1c90040110780003cc0e11b6005074d470020001b70060010d70050e200f1a432620c20619112808400302f00744502100100202725e0d04f408b00e0080090ba18232501437e13e2a40022e702731a0140270977650a917a34a0000950050150012485960030004f201424b0ca0b108000f00f00b07913f10703904b04d00e13203b00100b06400216900400208912c0ab5654222251cb05f14f02500503b2940020003c30036a928902802604100500662621400041300c1d257b0e607d04504a0260966720030340100300e65240020d10233d604e18408805525d0760061be06204822c02200000d0210c700a05a54e01a00906500d0880040e63d70900ba0100fc00000e02a00100117722f01a0a240700005c8cf0100c00090040060000030da36600a0003e702e0000000020120000880400000090070fb12005400910301601400b0730bc00000003b03311d10700000801a00105000024f00f04b09100900d00000702e0ef01400508527b0544462680b301a0140f300900001500503200800b0010e401e1100fd02d0121270c51ce01508f00701e1c900102600900c0090ac0780120005b901924a00301b00006119e01f00f0000a204c08876b0070092c819402a1f10020430080683cd0820be31211f02a01309801011a06108900001301000909105700001300107603201800021500c0d605d01a2d70) else (if i<3 then 0xcdbeba1e8510442e5ad043b0a0b1e18c78eb4989a72e996bad40192b73359c1fe8f1c1271db8616546d80f4314b2a588bf2cd1f28d5ca855277943968006b4a13a39df36384d46a270a86a8fa4d2be6f2316740a704ac8de4762b16e663646b7d5a885ff3eb8762303ad4d5568a9e8c59fb54ca65434238812a07bda7c337776ab5079b9502558ea58ab3376c75a661b9b854b069b06bd4307bf0b509c7379b22086a002e74acbd069215c64cabaa4065bb491a8ac58f4021e79b43f13eeb738ee49e1052b93481e905cb311e00fb3b7c1005f6a17a01bd6243476921da5f63398612c12ec9db02420b8cd5824e4a520f7a2298e36a69c95500bc5f80caef25285ab5a5df84fb272155ab6c4d05cd30792b8249c0721e0353fbbfa2660b20902aeac82dea26cdb038ab70f4c761b73133819cd27f7959ee5916b00cb51500177fccaa4e6ef209441c3b76606d5da4f3536557af440d0a3a0553532037e28aad90fcbb86a9a8b5cd0b072b48896294fc24bb758959fae369e57c6832864bdadb39da234fcc0e51d48cbc92a8b468cda4150168d5b10ad0e088006fa2c2edbf6a502d466477cb0699a92f21f7f257e7dca66986a4a34c6f6872293944c896d370080108a8ca2606188c35d2ba50b4ce0a2e2cca85c8741550707403f2800342ebb240a33ddafc804484c2f6341fc3c9ae347f29f8895374706514c890b3307f177f451239bdbaaa01e78a9638d17dabfc4357543c6048781144114ac166a8eba747754ae8478bc15654e1f600c40c8a45886c3cd066e11e15408c2f89014a958b2a2231c0524472ebacce62ee566a38237a6c3bf11c5a04fe74e2039c66098028350840792c36fa66976c42e9428c094c73a462103c7cccdbfbc63c706f956a0460880a671a2853972a7c83375b4f5eb05fd065a87124735f7b4076ac482f21e1425abc5835e09d890c1ff5ce1a84a78ba09a2b2d09c8f0bc74370a6653ca53c88a619cc22c27f4a57babae769822a9880002bd76ba454803403555948763412423de2a19d02e34a624a7e709e09925141d0b65cf7af67c86e80509e6e80b6ae941377a23c2dc04f2044a0605777a5bae014d86c51ba3e32e2ff3f961051ba81af9c030afad870dc5e06a3be09590dbe49ec3213d90ab89431192cc1fb99511c8b2bd6536d77f836198643a35c4c22324cf869c015381f91c965448a20cbf7b665966ea2d07ac24e483705211948b398d22d67258903fad048c49d65f570c59b07ad087ff7988e10a06e002e8c68fc07808abd763154b9bc4b9bcacf3b14c09c6b75056003482b24956e29a5c06a48375120454879d291c6d567ea905c8a541e30932273b57007ef17aaef41747b3901b13da7f95161ad64d109c4e9a311578b69ac585b3405b387e57462204698e79728a1b902b509c786ab865809546824e8f else (if i<4 then 0x93c1350c3ed7a89042908a15844c68662b65fd994c8e762421257b4aa002db5248076f771623f461b59033956844c9e82265f3579989dd47724c3e2ae398d8816b1bf86e34a58a9a192000cf11947a03dbc5a2ba858387117112815f06486f4abeae33bbcf2c521f83052e6ced2f777145914f96d2f37ee06a65a23b1df2563cc2cf069785a8758f53fb5553b776728cb473d2be0476117356758a659a59859570667abe2414c812d57bd383606c5a3ba41898c0680e41782bfa98b0f662cec43c7655459260002d407c4862649afad35873d54d922b76b471a552dec127685e5bcc6d964a173753c210876938beb1aa826c21ed5e393695bb0ba5b8718c6059a339a095a1813794529de7b5be973c02c0d11126c58170b20a90a20974811cca564995e85995fe78dc150e7613cee853b3a3c058dc302418a849434216aca66fc8622a92df8fa29e9d32ab672b881c753d9cfaba2d9c1116336184ba2d33534d8958c3776464b445e4a4008307e8c97585d5c993f5690406ac3b6c591b2963d9e35054c0915b62536a13466b6b70f3502f5a1c23d305bdd9e82f9abd4e9caf9b53236592ee43c55bc7d5eacd83fea8d2e94757aa61230eaf83ac4e865c6dc4e0b1579950ac66b9a11b5a227394b6633f45260f3bf3a7c42a5e7a0451698b8fdad644235979db225a365bb0b4bba83142392b4dbfc1d9c98aaf98088c25d117098aee6014fc95c553732bae25d938c2d52bbe0ba799339a54f41fc1d0aa7a8c501797f06b727487eba031d4110933d6cb188270c1a4598c6a5a90fa7e6a51b2069516bbd6207a781cd00f0e5642a0210039e92c3eaa22c229d473411a5b4c08a6790f0896432cba7fb1646733d8e877b7294a3c90b58032a618b91137904afa62990b658560c468ba647671b44decea36508451072f5921b843e63959454351d73f9099fb48617b91367b6ad18b3824fa6270a01437ba092b74a0c71e2ed43793729c3434c4bb25fc2c4cf91f457b14b60fb57b71430b3699163651270f40e03ca95a472892e173715c260c29c7399e2d641a729cf7192ce549b1bc1dc74942b8b56b21eb7c5a06aeb2a007569da2a33b1649536207b2241628898cdca6694f9340e25ef50f25434c7d01c8222b3525a36e31aade6040721500b47a98dd2918ca80ab89221b0e08e31469160600a02425938e40c3545dc77d360116ca5baab18a685fccb955e04e5db1347a39198154f1ba1bc7075b0513220204468c5bcc8d6562ba16d2ff0039da70f701c40b564dfc205812925782716f2b9889abf2bdf0325081ce9b79fd48286398fc683a80c32d64d75a45a58ca5c2c5c1a96238744da16c6b6891131ccfc557fa5551ddae470232a05a085a0b42732c95e6fe5304fe3c8c88007c3d3f69c025b0710aea463a50e67d6bc36cd9284d844d6fab01cd50de else 0x21a3a9baf0402c694eb0f80fe3f60b8bc16c2b6360a4ed02a14628385c9b19840749ab6dd15b09d3bc1f36ae15d49f3dc9543f852812f1404b70016ca51039874190986832552c1e2102b6fc147e469470e4c3c7fbaa1db49690062c0279e12d224bcb860523369797c81a169bcfa89559bf464b06ccc32d5987bb156b021b9f719621324c84352597b54a9931ec5ba543d1af10204115ff08344f474cb31725dc47899221b444094a7170a4dc1c23f7adf9a87122755aa07c6c842c60792712164c5631416fb8886cf4c101112713821a72728d029813a8fafd73bb1350337493358a5ca086bc0b964ef0ba2875a8a64aa16451beba7bad4fdc0b7c75184f038490a89b6888f21a286d170040839537834b1d82acf10ed43412436915f3a60ac9dc43f27b76e166a141238dc7dd5fabe390f6f793519cb1837acb2cba60244c8abb61b320ce7be0ff50d9d170d1ff59208699d3f871e7fccb2a610dbad5365532caa33a1e6970315b23500b6d015c51be8b009e02d1078af7c020ec1ba738c0f060ba1b1bbed841b7a11f31761c0af1510e80d38cc23e5de9087cd7803694410634938259b378f4e282383149a0360550f969933809d638a5d4367c6bd32450ab3b69585dd4d3432a1a407af52ad0423363496290096ff7a484c08d0f58d67bb6beb25916c574038b41fb08f3f0205c2babb2bf5144cd78258c98a6ea294331243771c1974f976bd4ac5b0a744c455a308111152e8c951742955c05b49d8035584e62776e806a0490133188c848b1207d84508938f7bd21cf9f82c779c573bd2c39b0dbe70037e861fb1c2574b191f3f3ab155181bae17b028b7305208bfb47bd0c3c7a839f7089c54094169975da20c38a1aa5588b07203cfbc232d6a6817cc8c25b2c3c4177a9625f02014e8c5ae784b5e670aa3c1a6956b7b5d0796b4b1826676a7c178e52a5535c160a87b34489993512f96f52008a38efccb6f07742163b306c288b844793742340fd1e85175546e9aceb597c0588b6a2b14885aa2af83a8573bdcd9ac7aac87909d18ec49c9a80bb2f7a23c5b023e19950d9b8d26b1fa61450e60477ecbe1808ae72aa8a06e68653dc6ec6134f1bf34aa4f7577707dba6955f2ec373ce7ba66d6c42b2e2e837d49893bba669f0be47e01741a70c62e7ad9507f60733dba6007808110f957cf0359002c53363aed69b682a37c716689f44222a3b67118ca3cbf2dba6da6b2462652aab91a1d33a86ba9a7a622823ac8279eb0348497e91d9cb4376667910222a86ee96858e4fa9d759d8655db4f84900016c724f66d879885999c8075c355a1109020f46521bd0b193c32808ce281307bb3460c773a2eacf595ccc2f61a0b5f576c92b5d6160300ac6e6608405647474aee6ef892a6399b48e6d8029c8640b3d08c988e019ab4cff2d2ba508dbbf7eaa))) else (if i<7 then (if i<6 then 0xc6c5afb3eb2589f2cf25059006763f000a284ff0000a18b7039a4b3af45c2aa0002c83890e1a5c7cc460c4150c3b925893f7df4921906528bb95e2ca4f62688ad46d36492d8430838c258d48765534888384e5d109a301000565aff000c473e729655e96125e2e9aa89fdcc6bfaba47f00006e1929b3640a09994e5ec8a06fe05fc56bc42cd89b8d46ec989c819111845756ecb37026761c26a25057018108000a3098520a9517230000008eccfd020afb02bb1297d2ae8874586ce02b14923f7815215bdb6d47dcdfa25473793b687a7818794cc4b073d4c9d518bfc8781d6be572183fb6e21d2e0000608ac2769b09c3330d68124f97a3ff70da1b0007e935654a827c0c4aa77e8fb0a0a2f1539203025e99b6cf48963ab5e70b32592fba292d3c312016f572f26d73d53ebd6a7d54022c0002f7a3600024ca39ad255531280e577ba96c52a43a19f04ea04cc158d008ca5abaf4062255ba1fd39350287f41443193a48d01e1b30002561e2c6b53a0a5a635a485f8150569eb71a4ba6607d376f9033e5000261707214b43c27630b6074b0b06771013e80acaa79902a0372412cda9121a720e0000002d73ce00071570444b8df67045e2ea282aa360965d2bb345b7ca3c6aa7b420e1e19f5158104a2125075d245be65402c512c8a270e1222f276389c2b79417a68a5c9477440b62d8d9afa4fdca02d741c0c73340c512581589747c00c7a5be143533ebbe5e889cb3f2d80a8c348b6a24c36c74c913075802cb3225d9b764161e450e47978276d0017689c7530c9bc6f03ec6543f404713c1b9e20b739c43d2a1ae46c47402c973eb57cc03c16a599c7a66dbb3ba493d7b6b2cecae01a68901c21984947600e5d68b88e298d428c1a41c52300586ea01a5159ab3e162ba82424b43106257a7a8a9f808d2a659f1065fb9e520f66c1673f025c7603449313e98298cb6e408b7147f397f52a32b08689989c43dabc6b8332352c2ac695ac0b3a4c247bda2197175619a551a8b3080a7ba4fbb796a31b5e583e2cf13d0b4557a0213ea503ef5b749153a788a7950612d40f97671421e1764f2ab2a9d168aa035eae586017d9052aca17ca1975af083bacacef65e03e253014a3364653cc4ac99676aec1b23a94dd33c06cccf0a776fc4b5561752fba187678cbaaea2a27ab797fb0417aba8059009b09c13c71b6bb44e709096391370b6998eb6ca5f8e93a25a2ad192ec722b32ea061a36a5e8f89f75b5c60cdd7b6bea036c0d1fd60193dcb03e66fd212cfca590650d69fc73224673508c1df7122daa26c750eb7343151875341f52675396736b330b0d2bd95be8d74811b920a89ea8b85b3173ec0985d75e69984fb12e9cc5a1d070c685d1e463436d1262ce54d3fb3714ad7ebbaba6f7b991ec3eb8a701c64ad426e30b3ee33f9c37426c728c89e44908 else 0x182eb51c64fcfa7192d371359ecd63b841b44503370bd0867dad70ae05db5e00d7f299078caf31c32262a58cc0231f72c029f25e6151390693274390008e61de51989d9367a5c2c12a8fe0c830f7102449ce5d4949cd7850a6ac82966ab1cce9ed4462dd9bdafa1b570334bcc50ab0317595d3514bfe5cc76e9a175531f05ec2e870a58902463ac94403a7094af95adbf9650060b8abde5131ac0288d32cba356bf35819627d0009068c1985a87bd36a73ed0002b219a98f8c768a284bdc2fa96e70e2b08e4c79a1617e2fa88d34e3d868f7e28426df6e247f7263a4bbc4b60ef204b2a0003f76e9b705ab189797b173042d50d524788bc9d016346a3d41e0f07b14f996799381e7ab73d0e9507635b5b7d99b805297b301c9569666f45dbc85c7ce159d44a9bb347b9d58e84a217c5da0e16eae6ae88775a6579b7e815a2781c2d130abba1357c256967841053343e0b97090607bc6c37f1d01c236a858619f4d07898984a28a008ac46bf55de8af4c70ae97826c4d692136c00427827e2e288655d9c474562db217515420588c572d2f16009aa71d9326d00376cc0691d41475749824ecab60ad3cb1b6c446f46749105e11336444d2a867b890753309764e39634b9794178405132c0accc13b7ca59a845a706612818fc9c6b99ca40a1450917131fe1eabb3333a5ace42e2000b7728e917824ac77f7b9c2097a5326b8719e7288321e0bfd4431c48151971859f9b2f27c68581f214d0038b4cc2580a20aa96f1c14395416324d109a12bbbb90e5704470373667ce338a65c3a930062641b8496b5f1ae489f8a07f5572aa533e4386bccb33c3cb6cd210d6d1a622fe8a75e07c1b85370848a3b0105316f80707de63781304b000c14a347fd2f42e751ea5dbd80ea008845c389a7b1924d8730bf6f994d39536c408000895b4c0d006910a42e4bf026b3c0f1b0c0005b8a7e29800032855b75b8ff6a2424c77a9704a710b8c1c0ac08da0642636318c87fe000107212345b8b6da61db162c6bf1a4433b9d96334f485556d9bfc8535772270b992b7881a35d41582c41363e60396c1c59221526b45097922fd977b925bfaadc93136c7ec35c9fb080088a20007ed19462fb7acc94040d421ca1048fa15c1c9348334a8a080423fc79f7c974513060da2fb7f8f445fa9cb195a77780503e02955629e40356f054885e89b5b61ee9a98c1a4e4ca09830c5b9279386b5c16137f5045534560eeab5bff5346143fa50ba6ec0a62f3f44579f352fbfa0b215e525000066b7b7e16f887a3068bdbb405121881dc7b1f06ad1d1a017213446798db974a8c0042107d73d38be1d510b19802d9b92f6ac45f97735f29c1cf15f84537477230bb020217cb7210ac6c4d33fc9c778408a21c78186cadc430c0b8b206abbba83cd00d8582b75a16a93622ab362777043819) else (if i<8 then 0x850401511600800004f1800220a0125802d040004204c1000200f4954015000350400004400ca0424032002b008198a8008e8a41002801b084152c2004900a1012000c000915a80010141400000005fb29906c375b751c68178e0b42aab46e63b50fce3054266a7362b088412482626bbc9812cc09f0660742d491862a2d295d20206a36813f403cd73e45e95a560b36a3aa3135566fcb1f509a768f5c974891742975f442d7d1ae222d30320d01dbd185933db7d199547a7ac4f71800906725f432743022593a0db0174c649af23854e3ba09257c8742472ce95384e5183becb0453b08e367bb107e3f2539511ca42e843a03a1600007e030047819574849c17148309b20db824191ef272a20aa2b92455251c8a6fb99488fb24a010c1b516abae67093b44eea7c8aa9fa0f26b5a241d30842138165fdacbb265ee329c1856fbac08c0bd6cb2f5a232ceb115c355a34f0318197799242b833779a57a0daacd25a75e31c8112e700648a000cbb8144ff20116fc114775270ac89d59786d6a308999608bc372b93fd1cb5460aa59b012969000cc19646edd024d419b58789db939d567f89600aa912f07d2b5c541ce842677a6f3571741875589b177a10a61b08f05a026a01b4db92a2ca4fb92aab38462ac56472d39b8f308a61a7ec826a0377d30808583c2a61bb9436f148935f4b56eb764c6a94036b5c5a539f946b42fb94769b80025ab0b2373e24b8cfa727f420b9fe18a021c00cd12ad7cf40d6e50b3ab86335df50882f8c371f4190a4787cf668483ec7a77081095f2dab9e2071aeceb303a31aea687b26d0aca78848ed51c9a61a5bd507f25c22ec4c29bafe3787c41af6ac10c73ea3b0232a72037750aa0279ea9fc2af9c9235a5eb45243c3fadd864809a2dc9f53f91431158b41d38da92ba4772cb5353c1635a9e73092654108b1c6dca92fc485a79000736b30bd5433a5c46ccbcb3db971599453c260361e0767b76f62fe309afb25550b51901f74d17fbee8b23582fc35106686b1d00b606057f3a040980dbb9cde2b45a90b1bdb08160ea12213c280991551485b01e55850c222071cbefa94376836ba393e30400018830053113ab2b000b938c007b34051e7cb006ab95b23f115766b2527aeb7203b2240d79c8aea93c6176afb58550a7558c62c830990ada0003f51294404cb77b06c86a91b5f33080a1a0a7efa3e813a355d829d3c789f75f3b182038c4b00383b297182d9e6a5fca2137b38b41b8e0250dc1fc784485cf50c96c96eb9a4254a1fb4e26f22fb53236b816de3aeb7982eb6a4976356c1529ba26e76e721d6f176504d4e756717c57d37b223a0995968e71851fc8c87c4809ac4363532082298c2077399607b3ba3ac626d44b38c472c7390d80a75eda78248000388783cf87d452dbd9b10a0f6c09ad4759a224a10ea2c4 else (if i<9 then 0x25e4d0e6de865ddde666465d89e5c5e5ddc9e5e5225c9252a44d11e6525c666a5d0ca69a5d124a50a514e6525dd1d08a65e9dd1251d664aa6a59c5265de26665de65e665e91dd1d291c909e51e5dd09c99de5d1d25c85265ca8c86a5de5d1dc9e465d15da50a58a1ea5c9e5e6521e9dd125e05e46845e5e51e5ddcde652525de5e666665dc511d1251ea45d05e66669e5dcea6665e625d09e5cd1da65109dd265111e512649261c84525de5252251e6665ddca9e666452a89111de51e04a4a51dde511ca665250925e45252665e69649d9ddde65e69691e9e9c8a5c90865de5e665e489c485e5d1165e65e491dd99265dee5de66a525e526452925d266629d1dd1d1e5e50e65d11de49d108491ca551d2512665e51111d925e6645dda4de51de9d0889ea65dd11dc90925d269e629d250a5e5265d0e65e5246524e66511de48ddea5261e5d091441200403a7882880000e8840c6820839a032430e80e4043090340388318301140dfc84302040379c84020880dc8a402600c36a2a8822a50d7c0215094035807a800220d40d18704043461a0070400cff0800010c339524408210cc50942000832b004000420ca100308800323100009000c80982823283163c1884120c3100080100309d0f802800bfc04810e042f8048040410bcc248039002ec0a0412100b9a008110202e101b820800b68011004442d5468261280b2e000422082c60001a0000b0c0040c5202bd000400440ae80c2010102b5060402800ac0033008002ab110482400a96c2a0119829a0f8282000a480301e80028b02a8e0330a005004000427c6488389009c81200620826ca21910200990c212604025c20020d100958009040802522131e10409232411808423fc2c8290008d8007006082300020a10508a9442404182220000081008818462542021650160240083c55012520206038010420802068500001fa2200118107d0810000a01f0a1090c680799048202001e1441880440768152201201d380b1b2480720101028201c36000210806f9090112b01b5200cc13006b4002224001a9880800060693b6014584197120136160634001e124018688110c8405f80000400017d4801890005dc8040003c1710444307205a0200049341618080408205711498a320151c4222018052489e04210140a000d92404dc080000541331841500804b19007020012500802040048800b5800411b00626070044e0210004010f40068260042008c00234101008a000003fb004204000f90238c4a003c2a604c0200e7028a80120380214220000db0021a1240350010421100cf0a0009140324245086600c08422100002ec4204c6580b1a5082332029a5a0622c009b005009810254900c97700894060820002110000360007f2000101601e8009c24c00721406321001a84f28262005fb170 else 0x244de510645e6511e66659c9de69d25e1dc9e649dda65d1d09d9e9ca5e650911d1de5de5d125c9d1e1dd2525125e5e665e5d2a65dde49e6486609c9e5e64a5d0e99e5e49ca9a5111646124d1ca4526dde52491e61e51dd25dddd0655e46a4a64a8a91126095ddd12665cca1e5e66a665e0a45d9c649e61ddd9de6a65de65d1de5ce65e1e49de65dd25065c926911d0a1d))))

def seedRuleCodes10 (i : Nat) : Nat := (if i<1 then 0xc06a80d20198032406300c4018002f405d00af0156026404c00940520023c046807808de01b8032025f08b2216012c00500098012c4248247008a210d0209041088280f891f043d207080cc8198833086600c90181030005e90b8617302c505820b1015902b085660a8814a026044c409021200230844207c20fb01d103a0070c0d8c190032806080c2017202cc05480a8615682840501098412642078417079e0e241cd034a06800c6c16882d405240a3814e025704aa094c1278249048a091012f0216042408300e381de033806480c401840318052c0a401470284052406b0082013a0154026004800a400280001d80348445047c10ec118302a084c109400b04152010101ca028c03020803dc07780de01b4036006700c3017602e502a905504a801440210041007e80f411da03a007480e101b2034086880bc417042e1056c09c01320242044206c20d0018402aa0506098a130c26f0486093610081af030e062e0b141660286052209341220201043607540e981ca039007480a7010c0204041c06d008e012601480238042008c0001fe03e407980cf016e02b4048807700e801a042d8455009001100218436006600b9016902d485810a801498271444307c80d801a0832605040a34127420a8417072c0d381ae825404a4090812d821a043008780ee01d0039a07180e981870300f608b60150119801f003c507500d24143420d838507000e181a1030005b40a7812602590416080c10e81d7038807740cb818d033c046806038006e00db0136022c041007000de40f411a142c205830b00158829504e009520f041b1032804c708300c2818582db04aa082810d814f02900410060009a0080dd016a029c051809e20ae01480230c37105a0890c0f2016042a404c4098c0c7416701d602a8041008700d0000109018a027c04b007300c6017c8178222283c107400b8c144c2090353043606600c3009700a00110020000039005d00a640a84152c120c203838a049c083410d01da03340500c0013d213ba0e1c127821903080500e2012401c1437005a907400a04133812c81d803bc053802036401eb037205c209c213881e68127014a0224026c0202cc03aa01470243011d01be011802020403600614058509c0448080184e4074705b80a7c06c00160200df016c0161017002a20321051904a006183ca839305b603181090100023c0310040290c1b8037341cc024f03bc0100fc015d41ba60e58183024704001d48183015a021e01009400b100c8005203c807500200624054809ca0a2e036004107921b883740040178216201e60147819505b00100b83075c061e0358000384813b80100aad030003800600fa0055c02a00500b410dde0100677008004c03300090010c82cd058059206ec83802d8003700000058023005406ed001e001c00 else 0xfe01f603e007680ea01c4035)

def seedHeaders10 (i : Nat) : Nat := 0x684d0056010af2003f1709580a6da15aa030a0e12301460c2ae005f46023e0279d054d00b7cb047c04daf0a7e016d8a08e8099a214bc027d90102012b0c290004bd201f4024d3051100926483e00480e8a03010428078808c1d13ca01f0700eb011294271c03a8e41cc02164c4d400671483940408d898900b4e606e007dc712da01622e0d800f38e254002a82417c01d6dc498804bcb82a40392789140092fa044006d1411e800c28c08800d0602360017ad810e018da045e002d9b821002fb5889f0056b703c805c041104009fce06800b2d42194012adc0ca015fb04240022a3818802b7b882b003ea402f8055971022007c4805f00a6b61fdc00f68c0be0146683ef001e998170027fa87c5003cc302e004edb0f580078a605c009b2e1e4c00ef8c0b0012f1c3bd001dc9815c025028761003b3302b0048a10e90007586056008edc1cbc00e98c0ac01167838b001d11813c021ec86fd0039c30218041de0dc8007308043007d4c1b2800e3d408600f558357801bea810c01d8c86940036c5021803a760cf2006b48043007362197c00d41408600de383220019ea810c01b5086290032940218035ba0c1e0063e804300691e17d400c4d408400ca902ed00180a81080189b05bf002f14021002fd40b4a005cc8042005ddc162c00b6d408400b8342b800160a0104016690556002b24020802b660a780054e80410053e0148800a79008200a2a42840014a980fc0136804ef0028f401f80252809aa0050c803f0046ea12ec009e9407e008a6425000135200fc010fc04860025e401f80219708d8004ac803f0041ee114800935007e0082f021c00120a00fc00fb5041e00238501f801f2008060044e803f003e080fa400865007e007a3c1e780108180fc00ead83b60020c301c001c70073a0040c60380037de0e10007fd0070006b881b5000fa200e000d2a0350001e5501c0019e6066a0039c80380032b80c6c007010070006418180800daa00e000c7d02e7001a8501c0018d405980032a80380031540ac800615407000620014b800baa80e000c0d827c00161401b8016d804c4002ac8037002b7c092000525006e0055441170009da80dc00a8d82130012b401b80150a03f200236803700292c077c0042d406e004f400e200078a00dc009b081aa000e2401b8012940320001aea0370023ec05d400305406e0046180ad00052280dc008aa813f00093401b801120024a0010480370021ee042c001cd006e00436807880034200dc0086880d700059401b8010be017a000968037002168028c000f1006c00408804480017a00d400789806f0001f501a800da000a80001a40160010a200f00002a800a000cc400e000023000000000000000000

def seedNodes10 (i : Nat) : Nat := (if i<5 then (if i<2 then (if i<1 then 0xe5500078d4001e2d0007874001bd20005f480017d00003f48000bd20002f4000065a0001f480007d00001f3800025500008f402821d0000f600003d0000ff38003fca000e954003a3d000e8740037d2000cf480033d0000b968002fd2000bf40002fce000af48002bd0000af38002bca0007954025e2d0007894001fd00004f480013d00002f400007d00001f38000255000093400023d00008940003d00000f380003ca000bf48002fd0000a968002bd2000af40002bce0009f400027ce0009f2802a25500088f400222d0008f400023ca0008f180017d20005f4000125a0004f480013d00004f38000fd00003f38000fca0002968000bd20002f40000bce0002f28000bc8000095402422d000f894003fd0000df40003255000c93400323d000c8940033d0000cf380033ca000af4000265a0009f400027ce00a895400223d00088b40023d00008f280023c60006f4000165a0005f400017ce00049680013d00004f380013ca0002f400007d00001f380003d0000df380037ca000cf400033ce000cf280033c6000af500027d40008f500223ca0037f5800dfd40037f0800dbd60036f5000dbd00036f0800d7d80035f580397c212143b806123d0034f5800d3d40034f28020a5500d2f580007d60001f500003d60000f500283d0000ff58003fd400aff4002bfca004e8580cba1d008df580037c600698b401a61d00e895401a23d0068874001fd40006f50001bd00004f50000fd40003f40000fca036261448486d0032f6000cbd60032f5000cbd00032f180946260031f5800c7d40031f1800c3d800397ac0192f400325e50003fd60007fa8000ef58001dea0033bd00006fac000df50019be800337ca02a646c008c85814d92a819b23d034644a024bf580495eb0042bd00124fac0109f400213e50041fd600837ac0006f40000de500013d400017a80001f500001ea00003d0000fca0289a703299702898702d97f0198d731a8c722d8bf01986f13c86732582f027bcb032bc7137bc50305a703859712d4d70317d504f7cb04f7c502f1a703919703818f03018703017f11d0d74110cf4120c75230bf21e07721d06f2340673130184f31b018475200182f03601bd503e01bcb03e01bc703e01bc501b0160f03b015f7035015a702e017d7032017c703a017c5050013c5009003c7139f6a60228e8904133e7104134e6e5801de610c12a8f26801a82dec02282ca402859e3402858a3402957e6001f5726001e5221c0135121c01e4f61c0134de6001f0da3426ed46c1608064238323d01933d400f33ce00f33ca00f33c600f33c400e2fd40182fce0182fca0182fc40062bd400e2bce00e2bca00e2bc800e2bc600e2bc401427d600f27d401d27ce00f27c801427c601427c401a23ce01a23c402b1bce01313c800613c601707d001703d001703c6 else 0x17ca0005f18000e2d0001f480442550000f600003d40000f200003c6000f8b40037d4000df480033d4000cf4801f3ce000bf4801efc80079f380022620078f3801e3c8000796801dfce0077f2001dfc600068b40013d40064f40000a620002f50018bd00062f3800065a0001f500187d00061f380187ca0061f180183ce0060f280183c6006d7880218f38042fe70085fca00097a40112f40001fe90043fd000077a4010ef40021de70002fd20085fa0000af480215e80042bce0004fa40109f400213e700427ca0083f9c0106f38020de500417ce0082f940105f1800071280007d201004aa0000f600001ea00003ca000ff20003a3d000cf500033d2000bf4801efce000af50002bd2007af3801ebca000898801e3ce0077f3801dfca000696801dbce0076f2801dbc800058f4000fd40063f40000a620002f50018bd00062f380187ce00009680003d40060f400183ce0060f280183c6006af3801abca006af1801abc40039f6000e7ce0039f2800e7c80039f1800e7c40039f00021fce0086f38021bca0085f380217ca0085f2003125a0084f380213ca0084f200213c60083f38020fca0083f18020fc40062f380187ce0061f280187c80060f380183ca006b78c00d6f100023e9003c7d00077fa000eef4001dde70002fd20075fa0000af4801d5e8003abce0074fa000e9f3801d3e500023d000047940008f18000be900397d000027a400e4f4001c9e70038fd00071f9c00e3f280005e90038bd0007179c00e2f2801c5e400303d0006e7a000dcf3801b7e80036fce006df9400daf4001b5e70036bca006d78c000e8f4001d1a8003a2d000744a008df600019e80022e3200d5fb0018bf400115ec0002bd00094fa00007f58010b3080212610041cc200018d4000316800062500004aa00008d400011680002250008c3a0010f48001be9000325500a645a000c8940019e80002bd20004fa40009f400111ec00023ce00047940007f40010dec0001bd0000379c0006f28010bec00017d00002f9c0005f280249e800493ce00927940002f580003eb00007d000004d40000f580001e800003ce004f984037a61004d984002e4d000b8f4002e25000a954002a3d000a894002a1d0009f48002255000889402a21d0008f600023d00007954001e250007874001bd20005f480017d00003f48000bd20002f4000065a0001f480007d00001f380103d80090f280243c8009ff18013bd8000ef40003bca000ef20003bc6000df400037ca004cf600033d0000cf280033c8000cf18002fd0000bf28002fc60009f5803226a0008f580023d00007f40001fca00069a8001bd60006f40001bca0006f200112610043984010a6100008f4000235000b8b4002a55000a8f4002a35000a8b4002a1d0009f4800225500088d402622d00a88740023d80008f40001) else (if i<3 then 0x1b23d006c8b4002fd4000a988002bd4000af380027d40009f380027ca00089880023d40008f380023ca0008f20001a620006f380017ce0005f280012620004f380013ca0004f20000e620003f38000fca0003f20000fc600019880007ce00009880003ce0009f9400129880025e70004bca000978c0011f380023e500047c60008f8800cf8b4011d128063a1d00477b0000cf500015e800026620004fa00009f20000fe50001a6200037940006f20000be400017c600024c40003f400007e30000bca000178c0002f100181168030225000ff50033a55004e8b4013a1d004ef60003bc8000ef1801b62d000cf50002fd4000bf38002bd4000af200023ce0007988001fce0007f20001a620006f38001bc80006f1801962d0065894000fd40003f40000bd400019880007d40001f400007ce00009880003d400087a00010f380021e500043c60007f9c000ff28001fe30003fc400464aa01cc8b401191280033d00004fa80009f40000fe80001a6200037a00006f38030b2a802163d0042c5a0005f40000be500017c600017a80002f4000033100007d40000fa00001f380001e800003ce000a7940012f380023e700047ca000879c0010f280021e30023a62000779c000ef280219e700433ca006544a0009f380191128069fd400c34aa00868f4010d0e8021bd800037940006f20018b1e80013d40001fa80103f380005308050bd4000179c0002f2800013100403ce000af38002bca00099880227ce0089f280027c800688f401a2250096f50021bd000059880257d40085f400217ce0094f500213ce0003988024fd40083f40020fce0083f28020fc60082f38020bca0082f18020bc4046193450863d0091f380247ca0091f000003ce010c9880033ce000cf280033c8000bf38002fca000bf18002fc400b99a80427ce0108f380423ca0127f38049fca0106f28041bc80136f180417ce0105f2804d7c60105f10018e3d00638b40007d40071f4001025500e08f403021d0040f600003d00000f380003ca006d8f4002fd4007bf40002bd4007af400027d40079f4001e7ce0079f280023ce0007988001fce0007f28001fc800668f4019a2d0004f5001d3d00003988000fd40073f4001cfce0002988000bd40072f4001cbce0072f280007d40071f4001c7c60000f380003ca000878c0010f10011b2a807362d0046c4a000df400015ea0002bd000047a00007f40000fe70021a55004347a0086894000de80001bce00037940003f500007e80000a6200017a80002f400005e700007d00000f9c0001f2803012a802023d004045a0000f400001e500003c6000df500037d0000c9880033d4000cf400033ce000bf40002fce000bf28002a62000af50002bd0000af38002bca000af200023d00007f40001fce0006f40001bce0006f280017d00005f3800 else (if i<4 then 0x5a000af50002bd2006af3801263d0009f600027d40009f380027ca000891800221d00078f4001bd40006f4800165a0005f500017d20065f380013d40004f480193ce0064f28000e460003874000a3d00028b40007d40001f4800025a0009f500027d20069f380023d40008f4801a3ce0068f28001e5a0007f50001fd20067f38019fca0067f200017d400049680013d40064f38000fd40063f38018fca0002968000bd40062f38018bca0062f200007d40061f380187ca0061f200187c600d0f580203d400c9e700acf2802679001b3c600d9e2000389402dbaa016c9500a6328043f40029f8c014fc401c53500428e80197b000cbd60065e7001af2801979000cbc60065e20079f58020fa801e7ce00a3e50079f2003cf8c01e7c40031eb0018f5000c7900063c6003de2001df5800ef9c0077ca003be3001df1000e7ac0073d40039e7001cf2800e7900073c60039e201037b844d9ec418cbe215725009b6b40a1a6a20ec9d10b64a801bf6000dfac006fd40037e9001bf4000df9c006fc80037e3001bf10000fac0103d6006deb0036f50002fac0017d4008be9003df400027a80013d20009e80003f5801dfa0000fce0007e50002f580017a8010bd20075e80002f38001794000bc800432d00618e8000fac0007d40083e90039f40000f9c0007ca0003e40001f1808c3ca01c3ce00ebf2803afc600ebf1000ebce003af2800ebc404294d407e4a50039f4000e7ce0039f2800e7c40087f40021fce0076f40001bce0006f28029bc600458780013d60003f58024fce0002f58024bce0092f280007d60091f380247ca0091f200003d60090f380243ca009ff20027fc6000df500033d4006cf3801afce006bf28002bd4006af3801abca006af200027d40069f2801a7c80069f18001fd40006f500197ce0065f2801126a0004f500193ce0064f280193c80043968000fd40063f38018fca0063f20018fc60001f380203ce008bf940016f38002de50055bc6000a7a800939a80027ea0034fce006979c00d2f280023ea00347ce0068f9400909680021ea00343ce006879400d0f2001a1e300033d40004fa80008f500011e900323d000637a000c5f40018be70000bd40000fa80001f480183e800003d4000ef4801bbd0006ef3801b7d0006df3801b7ca000cf400033ca000cf180027d40008f500023d20068f40001fd40007f48019fd00067f38019bd00066f38019bca0005f500017d20065f400197ce0065f280197c800618f401862d006189403822d004089403021d004bf6001aa2d006a8940027d400688f401a22d0068894001fd40006988001bd40006f3801163d004589403161d0045f600017ce0005f2801923d0064894000fd40002988000bd40002f380007d40001f380007ca00408f401022d00408740103d80000f280003c8000df180 else 0x65bca228ca50037ec001bf4802dfa0016fca0274ff01029b40ad7b0006bd60035e5001af00074bcc04066d0333ec0019f5800cfa00067ca0033e0009079806c4da0063d800c9f5800e7d200c9f400327ca00c9f00099e6d02879540a1e3d0037f58001bd60086f4801165a0005f580217d20005f400013d60004f400013ca0283f6000cfd600c3f28030fc20352f6000cbd600c2f40030bca00c2f080447d80031f580307d000c1f28074165003cf6002f3d6003cf4802f3d000bcf2802f3c2025b3b802efd6003bf4802efd000bbf280ea65503498f40ea61d0039f580023d60088f48011e5a0007f58021fd20097f40001bd60086f48025bd00096f280353d00033f4000c7ce0031f280e83d80030f4000c3ce0038794006ff4000dfe7001bfca0006fa0000cf400019e7005afca00b5f8c074af6000d5e8001abca003578c0749f6000d3e8001a7ca0034f8c0007f40000de80001bca00027a80003f500005ea0040bce008179400819a80003ea00407ce0080f940101f200001ea00403ce008cf280233c8008cf1800efd8003bf5000efce003bf2800efc8003bf1800efc40009f5001226a0008f500223ce0007f50021fce0087f28001bd40086f38021bca0005f500217ce0085f280217c80085f18000fd600b28f4034a2d0082f580007d40081f480003d40008f48001fd60007f50021fd20007f38001fca0046968031a3a0006f58001bd40086f48001bce0006f28001bc80005f580017d40085f480017ce0005f280017c80005f180193d60064f500193ce0004f280193c80064f180193c40092f580007d40081f4801025a0009f500227d20009f380023d40088f480023ce0008f28025fd60067f50019fce0067f28029fc60067f100017d400d49680013d40004f38024fd40093f38024fca0042968000bd40002f38000bca0092f200007d40001f380007ca0091f200007c602408b400c3c6003cf10002bd40009f500023d40008f380023ca00479a8001fd40007f38001fca0007f20001bd40006f38001bca0006f20001bc60035f6000d7d40035f3800d7ca0035f1800d7c40003f50000bd40002f380207d40081f380207ca0000f500003ce0000f280283c60088f6004a3d40148f380423ca0148f200463c60088f10095da500f7f3803dfc40095f5004526a0094f500253ce0093f50024fce0093f28024bd40092f38024bca0091f500247ce0091f280247c80091f1800c3d80030f5000c3ce0030f2800c3c80030f1800c3c400f87b00170f5002e1e7005c3ca00b878c0170f10001dea00037d40006f9c000cf500019e700033ca0005fa8000bf380017e50002fc800057a8000af380015e50002bc8000578c0005918000b0e800123d000245a00838b40007ec0000fd4000143a00018b40001ea00003d2000d874002fd4000bf48002a))) else (if i<8 then (if i<6 then 0x6f40031bce0066f280317d000c5f380197ca00c5f18010e6a0003f38000fca00419a80187ce0060f380183ca00484d400d0f38019fe5001bbca0256fb0006df4000dbe50002fd00004f9c0009f28018fe70031bce00637940004f380009e502c0fd800d1fa001a3f380347e50068fc401f112a0a82f600285e80050bce00a17940142f180285e200487ce0090f940121f104cc0f280e00a500387a00070f3800e1e5001c3c400c77a0018ef38031be800637ce00c6f94018df180117350072fce010579c020af280393e700727ca00e47940208f200391e30071fce00e3f9401c7f18038fe20019bca03f2fb00065f4000cbe50000fd00040cd40101f380281e700503ca008af38022bca00499a80227ce0089f2802a7c80089f180223ce0088f280223c60088f10011a6a0066f380197ce0065f280193ce0064f28010e5a0063f38018fca0063f20018fc60082f38020bca0082f18020bc400b1f3802c7ca00b1f1802c7c402c08b41583d8003bf4000efce003bf2800efc6003bf1007a8a500aaf4002abce00aaf2800e7ce0039f2800e7c60039f10031fd000c6f40031bce0065f400197ce0065f280313d000c4f380313ca0003f38010a6a0002f38000bca0002f200007ce0001f280007c60001f100c41fd01dd14a011af4002b5e5005e7ca00bcf8c0998f6000f1e8001e3ca003c78c0077f4000efe5004dbca009b78c0135f2801a7e80034bd000697940010f18001de300033ce0005f9c000bf280013e700023ce00047940006f28010b3500013c40041cb40102f1001013500003c8000ef1801326a004c96801b3c8008bf180d6bd8003af5800ebc6003af0800ebc001189540c222d013887400e3d60007f58021fd20086f48001bd00005f580217d20005f400017c60004f400013c200439a8000bca02a1f6000c7ca0031f0800c7c011907940941c5003bf6000efd200bbf2802efc202699b40a263d021987400e7d600489680023d60088f48001fd60087f48001fca0006f58001bca0006f080ad7d80035f2800d7c20035f000a925502a48f409921d0083f48010a5a0082f48000bd00081f480007d00001f280003d00009f280027c200489a801225a0087f2809dbd80036f5800dbd00036f0800dbc000058480955fd020559400d7d800c5f5800d7d200c5f400317c200c5f0008126d0284f6000d3d60034f0800d3c00043968098a6d0112954084a1d0032f580007d60081f480003d60089f480027d00008f580023d00008f080adfd80037f2800dfc20037f000cdbd80036f4000dbca0036f0800dbc00035f6000d7d200c5f400317ca00c5f080317c002a49540a923d0264874020fd20042968020bd20002f400207d20001f400007ca0000f400003ca000de1009df6000efa00077ca003be001347f400e7a40193d000c9e50064f004 else (if i<7 then 0x43e20021f080944bc24c24611d84e8024f600127900093c40049e100f361406da7a03ad0501b64e80e3254011fb0008fc80047e30023f080714ac228a461264c288d24f449520a23e89d12044aa91a1940117b0008bc80045e30022f10020f900107c60083e20051f080107b00083ca0049f100127c203288b4099e3d0037f3800dfca02668b4099a25027687409563d025589409961d0035f3800d7ca02448f409122d025487400d3ca0034f2000d3c6026389409ce1d02b2954090a2d025287400cbc802b195409063d025187400c7c802c08740303ce00c97840192f000b232a812c63d0268c3a0071f4000e3e7010425500387a8058f95400dfea00037d80046fa4000df400017ec0002fd200d5fa00087f48000fe80061bca0062caa00c5894000be800013c8000278c0103f200207e30060bca0080f9400c095404811680003d000684aa00d08f40021e800043ce000879407ce8f40a1de502437d80176f88092cf600359e30242fd800d5f94006af100f93ec001a7c60034f880007f18010b3500017ce00424d40004f380009e50180fd80031f9c0063f2800c7e20180bd8003179c0062f2800c5e200003ce0008f9c0011f2800e1e7001c3c40037f9c006ff28001be700033ce000679400cbf380115350032bce006579400caf200193e700327ca0064f8c00c9f101351ec001a3ce00347940068f1800d1e20019fce0033f940005f380009e700013ca0001f9400819a80003e700003ce000af2801266a0009f380027ca0009f2001226a0008f380023ca0008f200023c60007f38001fca0007f18001fc40065f380193ce0064f28018fce0063f28018fc800429a8018bce0062f28018bc80062f180187ce0061f280187c60061f1013c3d800b0f3802c3ca00b9f8c0173f1013e5ec005cbce00b97940172f1802e5e2027c7d80128f9c0251f2804a3e300947c400e7f9c01cef38039de500737ce00e6f9401cdf180217e30192bd800357a00009f40010f350001fc8000378c00c4f200187e30058bca00b178c0061f4000c3e301f03d8003a7a00074f2800e9e3004cfc600397940072f1801a1e80033fd00067f94006ef3800dde2021b7d80036fa0006df3800dbe5001b7c60036f88010b2540197e800327ce00647a000c8f380191e500323c60033f8c0646f6000cde80019bc600027a00001f380003e5002026a000af38002bca000af2001266a0009f380027ca0009f200027c60008f380023ca0008f180023c40065f380197ca00449a80193ce0064f280193c80043968018fce0063f28018fc80063f18020bce0082f28020bc60082f1002c7ce00b1f2802c7c600b1f101643d8003cf4000f3ce003cf2800f3c6003cf1004ac95058bf6002afd000abf3802afca00abf1802afc4003af3800ebca003af1800ebc400c8f40019fd000c else 0x8000fc402828b40d0a250032f2000cbc60032f1009c62d0141f200507c602b089400c3c8003fe3001ff1003f7a801fbce00fde5007ef2002b78c01fbc400fde0017589409e85a01b7d400dbe7006df28046f8c01b7c40009e70004f2808dc7a006fce0037e5001bf2009d47a006bca0035e40019f3800cf940067c80033e001400f80a047a0103ce008fe50047f20023f80007bd40009168004f4800278c000e3d0007e90003f2808d34a006bd600a5e70052f180297880365a50033eb0019f3800cf8c0067c402912300d06b449034a0461650240ae81104d486012a0063d80131eb0058f4002c79c0163c600bfe20076f1803b7880077d6003be9001df1000ef840352460178fe80c44d40267b00073d60039e9004cf40026788006fd60037e9001bf2000df8c006fc20095ec001af5800d7a4012bc60095e100d17f4024fb00067d60033e90049f40024f8c0241fd01ce4e80df25400ffac007fd2003fe8001ff2000ff8c04da6902edeb0086f0800efb00257d6003be8001df1800ef800073d200b9e1005bf6000dfa4016fd000b7e30063f0000d7b0006bd200d5e5006af0800cfac0067d20093e50049f0800c7ac0063d2009be5004df0809a4bc23525601b923004cf6000e7ac0073d20099e100db53446da1a022ca50037eb001bf48025f94012fc201e537009295846d48c03694d11b486808a2940257b0006bd60035e9004af2800cfb00067d200d3e80069f280644dc0123d8003deb001ef480277940335fd003beb001df48026fa00137ca01c92301148780663fa0133d80039eb001cf480267a0032dfd115652801bf5800dfa4012fd00097e500ea7f407d14a006bd60035e9004af400257940647d600c3e50061f08030f8004626e003fec0097f5800ff94007fc0013deb001ef4000f794007bc0023b37001df6004afac0077d0003be0009cf5800e7a00073ca0039e0008bf58031fa0018fca00c7e000fa87846542c016bd80035e9005af280317800067d200b3e80059f28030f8003826e00bdec001ef4802f7a0019bc0003be9005df4002ef940197c00039e9005cf4002e7940193c00037ea001bf48011f90008fc60047e20023f0800d7a8016bd200b5e7005af2802d788016bc20083ea0091f48050f9c0247ca0083e20041f0806c43a0123c600b9e2005cf08091c0c078dee00b7ec001bf5802dfa8016fd200b7e7005bf2002df8c016fc400d7e1016a9680197b001cbd400e5e7005af2803979001cbc600e5e200d1194018fac00c7d40063e70059f28018f9000c7c60063e20080f5004079c0203ca010de2007df50022f9c0117ca008be209548f449e45a44110d222822805cf3802e7940133c600b9e200cb79404985a00cfd60067ea0033f38019f94024fc800b7e30033f10011790008bc60045e20022f08010fb00087c60)) else (if i<9 then 0x100612680353e2141183764c10736a684401223442b0d24401b0ce1c22e03e4c02502a6c02b01a6802b0166802c0026802a9e6c01c9de403c966803b926803c8e68011826802e726c01c71e401b71d40316e6c0296dcc02c6a6c02169cc0245a6c02a566802e4e6c0184dfc0274a6c027466c01d45d40343c94024366c02c2e6802d2a6801b26680311a6c01c19d402a166c01715cc02711d401b0dcc033026c028d668025ca6802cb26c01cb1d402dae6c024adcc033a26c02ca1cc02c9e6c1199dcc027966802a926c02d8a6802d866801f8268031766c01375e40296e6c01a6dfc0186dcc0315e6c01d5de402c5668027526c0314e6c01b4dfc0214a6c01d49e402c0e680280a5802b066802b02580268b3400dc28104ce14b0054fe58028792c0113b960081c408030e1ec037712c00035810001abd8044d25802c5d2c0952c9600d15cb005e96580203d2e0101d970084eac82507658020392e00f9c9100c8e4b00226a580082934014928e003c5cd001826580000f2c0118696008414b00600238021cf1c0194f8e00ce4c7004f0e601277f1c010b6950081b208252da601206a860113341001164a8008ae54004552a0022a8f001154680089a640044d260021f950010fc6800c7258004372600219950018b4b000c56580291cf60168e2900dc694808230a4039105202007291090094887c00a4324a452093512900ee81480773ca43239c5210a4d29109261480572ca4032951a0134a29000250c844d0c9c223844e0153f8e000144d003a9a68000433400e9a9a0010c4c8008624c0042b1a002158700109438008364c00f1b0a0030b9800104c6800c1e600060730003029800180cc000c0260006ad300035198001a84c000d326000697300034a98001a4cc000d226003083300033d980019e4c000cee600067530003399800a9bcc0068d6600246734005b18d005d8c4800cc2600065f300032e9800196cc0008b24c004531a0031c980018dcc000c666000617300030a98001844c063000f4207ce7a005df930042fc2801772340009d2e00045970001e498000ea5c0007526004ba910031d428000d65c0096b22000358d00019cb0000ca4c00c650a0002f8d000144b8000a24c00a51220002797000134b80149a440084b2e000239700291c880128a5c00a4522010166b0514acc000003ce0008f2800dfc811f68b400dbc60036f100c14ae0035f3800d7c40034f5000d3ce0034f2800d3c60034f1000cfd41422694508bd40032f4800cbce0032f2800cbc80032f1800cbc40032f0800cbc00001f600007ce0001f100007c20001f0008c22502508740303ce00c8f100323c203378680d1fd800d7f40035fc800d7f1800dfc200d7f000f1a5a01359780257d20005f400213d40114f3802d3ca0084f200213c60084f100413c00003f1 else (if i<10 then 0x9e862402ba087002a6e680499894001e5dec022779a0109da68022699a007da26802c679a01019a6801f45870010fa1c01135870010ce4c00433850058ca6400d328b0044c21c00d29870010926400d248b0044861c03d154300583a6802a0c3b00782cec021098d118800c4226d894000359ec02eb28d00d6ae34021a58b00c29234009a09a000276680009b740066522c035948700fa4e340098f9a005a3668015888d046dfa341186b8d003d9164000609a00017e68056578d00195a34006548d00193a34006448d0018fa3400031850000c5ec02e0d81087c2e4c00a089a008c0268042d04d003b919a00e72134004e366800cb64c801b6c890032c532006d8a24116a3cd0055453b008a852a09b4ecd400789cc0031121b00021330010c142414575c98014e89a00859112004b0a680195dc48012b59a00391ad60102053c01d40928256452900b0465201c048a401a03c682440079008400a601d000a4118ca0c8033026500b1453200e28974035514b0042a16b00e14276013a0a1c034384c806a70870024dd3400216a6402526b5804c4d630060973200892d8c01a25ae80484b9600a894d60181290402424b5804a4963009090d60121218c03c241d8050412700607efe00f8ed8c02501cc8064019900bc031a00b0026800fa1ac01aa18c00462640202a0c02429ac01b29a402529941212664015260c11825a412325940182264025220c01121a40112194011218c01a217402222580161e0c0111dac0101da40191d940171a0c12119ac11819a41181994118198c11a197402718ec02e026402d020c11a01ac11ae2d20117165046b8b18059c4a4016df3600eef7f006b6c18229b5ac113dad200d6d65009b44a804d823c022bd2c013588700ce3cc8050ee6401876d600d3b690069db28034ed8c011613201d269800e104c00667e60009331601d149800dc9cc00744a600001f12000098900941c780180268039864700330898007e0d1a008c06680197bcc0060f64100a5d71c093b2e382325aa0845aad8e007d288619524d0c11b47a1866e7c411470f3260079da681232a4c04422696002c0e86094011f4023023b8230037d008c06ee08c00dd401801b98236027d009c04ee012809d400b01218256017d045c00fa00b801dc11794ea00bca730062538823725f40009286114c941049a43e804d21dc12790ea005c843044e3be804f1ddc1138eea009c773046e3b880011d0c22e8e7630d467d10a633a8032f5f401c78fa0093b7d006ddbc8040e9f401874e200e397d0071c3e806ce0ec02a5082015263b00000cd00300234120c421c553aaa5031aa224c106a1268009822600588123400a80e6004080a6002b7ee1c00b7e2603417da500457ca600327c66c4437c61c00b7b6601297ae1c00b79a6005a77a1c03862e0c24c61e4c else 0x17a88ca04255002504569f51c0a353ce6811150248c03824f6b4044000870870000fe025a714c80494e199009a9b53201253666403ae6da0136c990073644805da9b4038ceda096666d04db2b6828391b4036c6da00060790076fca804d7664025b732092d19a005d91482a4aa501405128000276700e92ca0230919c23f47280179e6d0070f338066725001b351e00f9a8b0090c4c8040326402519120138b9900d0040805401ec31cfe3600c7d8f0067ec4804bee64026f712000602900bafb6803f7d9c0217332013b799006d6c58036b624026573201c296d00dcec9802876140241b0a0000a2504b44b6825c21b402c0eda00e876700b83368020199c0210ada088856704701bf82340df400702fe003817700ac04980420214032989300717d640355d9900d175740274e9900952a64027428100450964011415900acfe6403a3f6300c8ce640252f810070bdec0232099008c42040250f8100443d6401b0e81004439640260d81004435640230c81007831640260b8300c02a641380a6b049c29a402e0a65049c298c12a0a5d006801ac01985a402382040257e04026760401c75ec023720401b71ec0366e640176e240286dac0376da40376d940296d8c02c6d7403125ac02f25a4035258c000154c00014a402f11cc000114c00010a40170dcc0000d4c0000ca40000a0c00009ac00009a4000060c00005ac00005a40220264012baa2c006ba224006b9a24000a92600049da6400c9ba640048ee1400e8ea6400c8ba640047a65401b7a5ec00476a640047426400c6c66400d6c65400c6b66400d6b65400c6a66400d6a65400457a4c12f3aa3400939e68009256680101fe1c0101de1c0101ce1c1351961c009182680420d6540090ce6800009e580000019c000f7670012f63c004bd8b001276640408387011a0a4c01580980025ee68230713f007dc66802b4f6d00b9226402f479900cd1a6421d429b00b4e60421e38930028da68025258f0c5c924c009239800488a6854917930400566002a0f8200cc2e6432f0b8d15242a4c0450a9a04282660012089a0c68024c10aa59810d27e4c1089d9804ee5e50000947b00964e0401d937b048a4668004838f00120e24033837d010dda4c00675930019be4c0066c930001a66000e669900659a240066493000186600065e930019624c00055980019424c0004e98004ce564019393d0044c5fc0002e670000a59c040039a00240268024f9c0805bf1980013c70e00b7466400de8c78009c9990037931e01b6ccec017d91d8033948f0027213400ce1a3c041c3438013829a0026ff340105716401c563b008cab870025473400027e4c0004fc380548481086905260051fe6803132cc808e649a001091160021222400e1acc805c0a88006004b200f00164040bf3d006addfc12ca38008))))

def seedRules10 (i : Nat) : Nat := (if i<3 then (if i<1 then 0x3f456ab55aad56ab55aad56ab55aad5680000287c748e91d23a4748489228a28a28a28a28a28a28a28a28a25ec0c8e5fcfe6526bd85ec2f75eebdaaaf6bdc0d3fb654d96582cb2cacc2c35986b0acc35986b308000000000000f6f57f8a156bf6bf1de5f15cbe03e87e2b142905000000061b2ca9142aa45254a548a6136acf4207b81ee07b81ee0015f4f2eab78a59e255bd054480044c48a3ad33b9dcee773b9dcee773b9d71c71c71c71c72289228a248a28a289893ad228a28a248a28a28a28a28a28a28a28a28a28a28a28a230c321b44b54430c30c3112d510c311110c30c4b54430cb5444430c3121b44b54444414130c3efdaa22218bd0daf2f2f1861b578dabcbc6d5e36af2f2f2f2f2f2f2f50c97f383956eee59e4ab3f076dedd09f9d0e8743d6f46c8d9a6d9a6d9a643db10f6cd9a6d9a69ded9b34db34d3bdb366998636489d2d510c6cd9b366c618d9b366cd9b366c90da22225aa224efd03060c183060c1bcf3cf3cf3cf3cf3cb141b141b1415e5e5e5e5e5e5e5e5e5e5e5e5e5e5e5e51f40c183060c183060de79e79e79e79e79e7800000b1b1b1b1b1b1b14b1b1b1b1b1b1b1b171c71c71c71c0c183060c183060c183060c183060c18306f3cf3cf3cf3cf3c4499a4b7a48d113fb44491c8e469334426d2472391a258fa2200c9b26c064d80c9b5e000000043c0cd332b0d958638000b23fa6e9ba6d0d2e4824cd3edbe30cb530c30fbc96ca3f75656cca7dba800015a69987f800096896871c71d532aee83b46528d4e2adb06754cca0b6a72413851acad1a09c2759d2807be01ef90407be4141bebe217e35768e7ee42fcedb0d485f8d5da3987efc6aed1d62f5bbdced6ec45dbebecfef61f7af1dcafcb38bf67af5e88bb63790bf3b6c3e217ed6f59b0f8f62f95f966c0e90bf582dc4d2c0f90e4efd131d8b74b652fe2717ca42fd608e23f290e4efc122df4e2c4716f17cb93bf0490f490bf2c8eb9358efca42fcb3608c77e5217e59b07477217e59b07477e57e59b0706ff16eec0dfe2dd88dce2fecb90de9bdbbf14de7ae7956473f59e29bee446d788dcd8ebe2f9485f966c3c7b9485f966e71761ec590bf2cdcf2d87ae717cafcb24361f7ccba19e5215949aec8dca42962b749bae5217e59b26485f965266ce599e57e59419b085b7eebfa9fe2f95fba48686e38767ffcb559901f3d6db9fe1c74baab6d3d1bd57fbb7793f33f359ebaf67d55e7f969355e5a4d5667c663f63b9fc663f63b9ffbbefdef4d7dfbde29fbf6fe37efc6fdfb7f1fb751754c030cb7f25fe7f03fbb7a9a4df533ab2ccb9fddbb0f15876999597ba9ae79fbc2fdcddf0eedb1db658ed76d8edb2c8916ec8916ec8916ec89b2e6cb9b2e6cb9b2e6c41d2c49d9cb41d2c49d883a5883a596449cfd91273e73dcff67e9967f658ea9995d5332baa665 else (if i<2 then 0xa66da353bdacd2de9704a28b69a422c8b69705ed450cbd1a094516d3484c916d1a0bda8a277aa4128fb686286286197634928b36d34a4cd6568d25ed6681e319453c3c7331981e7826f7d23be28834365bc362e6f8a28974e69f548270beb91fa1cb6b06528c655b67559fa2546fbb0c8b18f2b6ceacab325eec40b22af2b6cea9bd12a36016ede972417efcfa0224aed392e9f3e80197634974f9f400000e238e38e38e385bc7fb7a5d39208867d00001111c71c71c711c71c71c71c70b4aede974e48221ff14c88911222443295dbd1a9c90443fe2991122244488645bb7a34b920887fc535a44569115a4456910e58b962e58b962e58b9628303ead0467f3e8471c91122008165ead1a08a4a7c00e001c71c0207b7ab4128fa2f3e8000bef3cf3cf3c103ead0517f3e8089e789e79e279e79e64e4e4e4c889112224440caa5fdbd5a353920bf8a40001af15025b5bedead1a5c905fc5358561585615800039e78e78e79e39e39e78e7889e79e238e081b47dabf80e38e40b295dad1a9cd2960a6aea3611b08d846c1755248a81645ba7f6b469725fd5dac2b0ac2b0ac1c0e07073fcd7e5dfe89b5f8a8900073c73c73c73c73c73c47104e770e771c417105c4101dc7105c417105c41710440f6f56920a37e7d01104e739d0505105040741414141414f3cf3cf13cf3cf32727272644488911223d52f9aa145a0654cf6f56974e482fe29000123f0bc556158560000e78e78e79e79e39e39e39e229fc0755eefcfba53eaaab58488911025bb7ab4b9208a7d7e0001c0e07038e388992889e64df7d1b75af90b40007a0275829a39e4022d0ec5f5f5f23cd3be5a85a0001d46380ff7ea31c0be17c234e796a0105ce796a01e5d3168084bebe16ea5af9176008d39cefa80414e73bea01058dd5c806f92faf913247b1b96a1680046e503f61d17e0f8b427404e84e8c1839e5a95b64b5f2d42d002029cf2d4023d01e5d316808bebe16ea5af9176001eccf01e5a85a000027427427460c469cf20ee020a73c83b8082c6eae4037c97d7c3db1c008b26c7af584e84e8c18d48b9eea4c9817c2f86af3de9fcf8de5a95bf6ea5af917600c9cf7e782f2d4adfb66780f2d43d0009ee4ce7831e84e809d09d18300b1bab900eb71bcb500eb60bcb5008be4be74b5f2d42d12d12d03d99e6df2d42d12d12d12d1c23d12d12d183f1a2d01a00680d01a045164db0e1a00680d04a0bc69cf2d46d92829cf239e6d92eb60b1bab91b62f92fb3b7d9dcea36001032bb5a9c96a3e80001222444096f569705c8fa008165ead1a0b91f4002a2a82a2a2a2a2a2a2a00000415151515151515151556f63f09dede4de4dedeb2cb2cb2c36ef26f6f1b6cb2c3aeceea3b5daed40984fe7c47b0f80400002262624eb09bac2767c25f7e1e7c25e61212fd75d837f5ef0bde15a5 else 0xe4552acfa659f55357ef47f6eb8a08cd7e757b8c4fe4d617ee2abff31356b8c0cd7e62713eadb6c4dc427fe757ef6e79dacf6ededaf74f713e13e3b6bddbdbdb9bb73a222222221888618338ff39f8a16e28ba93fed3771c6d064546a5c5be36832e22a32b7a6ee282926e997ab716ee29314ea324c512fe33aa6f8da4cb88a8ce90504f9ad2362e2907a6f8da4d62a320e2df1b49ae30a8c937ef14283ff19d20a75eebdfbc567fc750f80f4d1ff75e13c570c57147584f7114758ae4b0389fcff37477e2be6a5afe888889cdd0c430c30c30c30c30c30c33e487fbc35df4c30c30c59f9bfdeb1fe6dbdbbbc93b9b00ff7aa5b20f7b6430c30c4430c30c30cd1c70a14193dbd03260d9bf06cdf3dcf6733d80e7b2ad9530e05ff613fdefd594978f9feffd803f5d67de33f60000004f721a9e4eb2d3f8c4353c9df9667bc2f800000247aefe2b482313c1dd0c50c50c1dfffbe063d4d491ef0fc616f2dec6f637b037b0effd7f9af21e5ff03e8d7ac3cb61990c2c2c332c29053393efb6977a85cb94c200f50ac69f2ce3ec2e3ec2bbd42e5d928015986b30d661acc3585661acc25da5e6daaa4a3feb49fecad656b2b58bab0ad62417ccf32007a85654fb20000137cd7bc1fe77aa4158c98585858472fddf5ac158561587778cba0008cf58cd0a88cc8ea2f5d08cc8f63a19991e86a7e654686479951a11951053e20a4148290520c0930240030697e6aef4cd8372626000c06000006000c06069ee7b8c00180c00bf31cd87f374e4a660000d3ef79b6def5a7e6c4db647f03c597000d91b206c8d90a3007763bb00180c00180c02bf07abb9a8f057b82a3dccc00183ab3eb9cf7c13e3eb98060304afc9d0f3dc9e0d0fbdeacfb273df04f8fb266000c007763bb063e0ee300060fedcf700603046c14b9c6b6f07fbfdb9ee300060fedcf760a5cc03018257e605f1b04e79803018397e9df3706db968968968a9f9b83e23c597037acb803abe6e0f88f165c0deb2e00e1decb44b44b42afde6c3c1dda3ec81b214606c8d90a3133a8f7bb206c85181b236428c0d91b2146004444192324648c91923a4f788b9fe9c5fa7a7a457feeadb72464867fa4fd47d1f27f03ced454709002478809012024048b6c58e5d15d54d6c29b0a6c29053614d85367f7b23b6596048b2cb0a7a4a7a4a7a4a7a4f74f4f4f4ee2e88cf7d7badaabf5fcf2ad0af6cd1fdd6dc91922db923870ed966afd9659664fd8122c44444444b5edbead2fafcdf0fabcdb8fd544443e1c9a96dbead2b8febf0dc7d2eacf79f6aa2221e0e8afecfe19f0e594d4b6de94738eb3ebf0dc7ecfe1cf79f0afa0766bc5f4444090909b6d1113c7c870bc679b7ee0b8cb3409cd211696d734852a5b5d382f6cb739a5264cd34d294a669a9c97b59a02e69099229a6908b229a5c17b5140168d34c)) else (if i<4 then 0x7af39a7a3b07aafd10ee8877443ba343cf7352efbcc7ca9d68e631cfb45528fa2a8732dc6aa15e6aa1596aa1596aa1596aa8765d2efb11f3e8df3aa26f2bc1fe4dd32a75f3aafefceabfb1aa7aafefceabfb19d5f699a96eb4772f7f37f5d2a4d154993549a3195268c69cf2d4020a73cb500f2d5f592e0b1bab900ef77971ca98aa26e13b2deb1179e691b0f4646c3d191b0f4447e9032ad4e6efc2f3c0da3dfaefd570c0caede95709601c096f5697052bc302cad1a79e57860597ab468295e1751da1a8892a3888cc1135f98ed444774e935b44537e823513e81f29d376ba571358ef77cb3643f955f8ed3bd7751dae26cda6f9d5e38f47696da6b9db8a6a5f1f1223a77a54d51dad7aa390e3b17f5362f6d4d1f55b6f773e1d8da6a516f4d6d1d8b0b4a2deeb1617161697161694c7e2d29b75b98fc5b5cc7e2d2f7771d31bf5f867b14f8f629f1ec53e3d8a7c783aa3e3e97153ba8a0fed7d3f819f62eb7e1edb8bebeb7e1f17bbc2fc3c3f9b6171d0bf0e17e18cc2fc3e1a0ff9ddcf926b45fb5d17e6b21c77161467baf14d437f15e86f1d3c6b8a7a7aa233dd78a33c286fbff75de7ea21bed75dd447feebd770ded7db7f9d12f415dd5fff578cc7f2ec0d2c64b5e8affa259ff7d3c8fe994fb29a6decdff6cbb7a34904737915e3b1d7fd97ca7b376d8dcbb03b192e0597b4e6f3dbd262ccad7aa411ccb22f653446e926c7e329f63f6fe365f29ebdfa791e8bd94d36f11b77db771fdf7ea7b8b2ed33fe1f43e9b5e7eaffc46e7ff21fe30aff8308fcaffb75a1e1932ccc6eacac3b49a6fe23f2b65417fda06d2089654ea919fb3b2355233c6b65d8d2552dd694817c265887dd95cb4a59fa5d382d9d94aecb3353926eb22cb3f46970435d4876734a413219621f76570990efb6977a8497f327ea75c4524da34904ffa524a75fa282d3fd2ecb7af7f63edd5dea17b7fcc8d2a82cd05ddf6cb5a0bbbed96f6c26ab9afbef9d71b7f8417fa5cb4aed392de6e96f4b82de1ad676eef1a9dea905fc59a709df57241776c817ed892ab84e27df7fa27a496b469209ff4a646b7aa46bdea919fb39a9c97f574b5b56bbe9af54827b125fbefdb12595a5c9577fa57f74f715ea4da349577fa57f60bf7d05bd53b3a4106fe97652bd4e0b7b6765e8d05bc358afd67de5d3bd520bf997765734905dd95626f9a77f37ed96977a8497f4afafbb2bb2ec692de6eae0bbbedb2353bd520bf8b7cd553bb5ed84cb777ebf6f78dbd4ea1acd6f0d7aaa6a4dbef726ed49b7e4dddea9f9e5ab7a17a69d80f2d47233f93f931f96a25fe4fb96a25ea5396ade8dc8e587e5198705c6c1f285d403cb57d64b92ff3d3e4e380f2d40bf260bd6f07a93577edf93ee5a804e55be5aa355be5a8774e145a23cb542b0e0aadf2d4fdbb78f416edfca1750e36dd1f0ab89ac4f else (if i<5 then 0x4fe3cdc1c1fcf4c75b4d83d3b652aa8e79ac7d9aa8ef954bfe6d9caaadda2cb672aab768ece5556ed1d9caaaf9f9ae43747b90d6582fcdc1f1eaf3be0f8f57cd0efe333a8f7bd5f8f3704e6a3dec0eb6b3546dd76fffaee043556eaec164dc3556e37f82e306caee55b30586aadd5d82c3554cf5d98e5df9b54f3cf8bbf36a9e7977e6f07bcf71cf8bbeb7c19ee0bae1b4905c2eb9be28a24b54486d2d5137bbef1a25aa42d2d521696a90b4471b4f3179e973399c4e644e644e658f96fcaba62eb5ac807f1b97606e3beeb5111910fe372ec0cc527efe7dcc655f8e95b23ee95eb526fad3fcbc7757f1dc9a4e8c15874d41e033956d3415079cf0fa68f4e414069a2dec8bf8e9f6e253d1ef5dbc9ebd81e720f97caf2bb4763bad41b2ec63e1e55d3695bf69fee331a5f64d3ea124f3948371bce62d3d97631f0fa6d2b7ef8f02cbdaf379f49bb4af1e66838dd388fc78c93d3d4f64abd9e5fd366f5325e763329f37ebe6eaea3877cbcbfe89f593fd24fb8adfa632ae9b4afc75e9861913a0f7a0d0c30c32a7fbc745075543b2bb7a9c904f37915338dc3fd571bed8d6b99e5a4f76a90b4485a4b766e83a111cc22339aba4a63adae9298d8f96e8b41d74c4975bad3199b911859457f745887f1b97606632b5ae233d194e51676e3b03da34d2904f32a04b7b77bbcf6f49a5224369b2e2f580f899ea90ed4acfabe0bf13f754ccbf315f39eaa96fff8874ff9676c8725f0145a6a887703c63db7f2ec0ec64b7acf72fe851af2bb7a9c905bdde457ae5c558fdbd58e29976b9fdfe29976f469208e6f2283b13fa8a7373112d61b485a7373171890b4e6e64631fbaa6bef423b350ba66e83a1cc3a8730c8e7498e788bc8cfe4790d4d07f13cf77f43530d9d9afe568ddd22e237398da795ba113179ae9298f2b46e8b88eb41b252d63d168331aeba31a568dd33a45c475badfef92f1ffa745c722e3b75c8e05f98c47b4f2b4ad1bf6fcc30c30c199f6e253c1ddb8e92fc0fd8eb5135cb76f4b920b7bbc8a154bf5db2ede8d2410aa1e676a90b4b5485a66a1752dd074398732fa1746aedd87a6a1e5c73aa15e8e7ae846473b761fa3f4d5d21c460779ae9298eb41b2595ad1d9846bb739bbadffcd186686cfeea8466b7ee94633369b32a342e8e7ff3a8d427d91e350ccc8f19bbd36668545d50af5d2aa5c2615e6ab54abf875499846c77da24f8def355c2aa1149efddf799d765fa2fa602737971b7731552895c693cc6fbd6a1b547a4f98db55e8fd179cd3d0ee8cf687cc93f4bcc7cc3f33fe3f34769df352ee79b527baf31b6abbaf44da93c2b8cdb55c2b2dd711a5bf623f6bf2ff9ae7d2f334fb8db55a68d56cb95f9de6e395f4637d71bce62d3e972bf9988e691b0f451d2a05f4457a8f559b479f688af55a3f45e632a55e9950ed9aa3ea9e1aa9 else 0x10be919e52743589fb737f5b3351e1be4b19271c7bec341ee46b939a5264cd5cd2132459cd214b658d34845917547bd188cbbd3b482befc32b86fbbf4fbd180e5bd5496af46ebecdd58dd18f6cdd5496af463db375417b3dab1eca6729292d5e8c7b66ea8372b77d705c32a5b34970ca668af5abbe7864c4746d9b375329f653496dbfb3a994e9a2325e76799b4d119892e31ecd9db375329cc1192f3b19e8c7b01dafabc4e8eb3aefd3d5cd7c1b64abba06d916b4d2116454b17f0cac5e83e17e845be970ca8dff5f19f7bcddee77c4fb6c67e6c741b94ca5323ef6b85294cd2ef41f0bf4667d80d170781e1dfaa10eff0ca482adfe1949bf2b8787b7e55ae10a5b94f5b569a53d581f43db3290eedc4dd244edaebfa77c15ab4529e0e336aca68b838ce3514a783b0c3bf5466d5a280f0789d519a294dd60f553ac3d1d3ac3c56cdbc7ecaedcaff371dbdfd2b6521ddb95faefb93194ddf764f546ba4ecdbbaa99f340a2aae149e195c5e6be77e2fcdf1dc5dcf4c4b4aa4fe60edf7d4ad561ddda2b3f52bfff3fff57cdc5fc66751ef657859b6bd4fe3cdc1a9f3be0f8ee2ef0517f8ee2eea7e6877f1dc5dd)))

def seedScores10 (i : Nat) : Nat := 0x6a0409d604d57c4dd1a50200001a05cecdcc01013f000021212121a76b000100010001a80c010c6e17001561d01da77ba67a0115616d1700610ca6006c6100cf00010c5c005b7817041a03c0a05900bf07001d29132d032d2d03550303039e03039e090b0709060b0504231d0733a324000705100803830b3433330b34330b3333340534050506200b24833305c2c13305292305622d0fbd0005611a0200aad3a9d2a90115610061460eda392b1c213924272121210e091023363d103a093a2a3c09102a10103a0f100f9f2a420f26051205cb1f001f00d8ca00001838be550303030303140414042014343405a1799d05792024a1790514030303bc09133c05053c8fd7d4c78ec68e8d0b8ec58d8d0705363d103a1f093a2a09102a0506102da205052d103a0f102d0f84082a050f00a40bc4c30b11d990c9c8

def seedLookup9 (i : Nat) : Nat := 0x84532f252e2d3288f2529332f3125332e84928f052f29328532e5283332f1340010220201d83800296006602440010017a3190006004e2a1a204800f44802612002c043e080a006b0810004001002f880400000000388e06359dd32c1e85c103af3e5b00424da8d6ced180178018bda3c7b48f33283b9b201343b1d5d7d4804850005c2300003520c745001b91a703354f005705c6db803a3937d2ae5800003a4a8b9980081e9ca98049bc382d36062e802b24a5b8004f474e003d5d100049004f80432b803e099fbdbeb40ccca288b2bc943fc0a6078313873f12d22516822caf211f06aa2fcddab09f2791099d82c1a2950c3ad55144b9c5d0cfb3802224cd59cea5489ac8ae08dca953d400d6184e0e8d9d40273e9db28504a4044c26a0ca0b238f9e050041ad84a1841fa21e9c592fb21915b6bb0183b1164790801246004b44000058819a5a25b72ecb8d4cd03035170a89082000148ab88a3c4281233c86aa8a3f8007090780357220507803801e920109a8d18603682db881810015021408ce81078200241802a0008b016088332381080e10095067558318552830004780020c00000ac0865218006

def seedRuleCodes9 (i : Nat) : Nat := 0xd9014e01c8237806b00d0017822d8046807a80dcc1bc82e105a807880c8c1448279036e06340ce41708279037e03ec07700bb0080980102018412f8254009e012901c3037486ea0b4415c82ae04ec09c80f6a0e641d3037a066c0ce40f681f70080b60148020803b006700ba216f01b9437c05460a8e06ba0b3c12e821b0400c500aa78230025e0301c201f403a8437740f20de01bfc02f801303221bbc00

def seedHeaders9 (i : Nat) : Nat := 0x2400a000b38048805aed0004000b2807100870c000000090009e0005e800000004a00d40007d000000001000d800082800000000000000000

def seedNodes9 (i : Nat) : Nat := 0x1daaac004f536800ae32b00109d3580233a69004274c60094d62401c6e560034c9b000547d620050f97400d18d880243163002054c600388ec401b08d8801e1183002822d200a0459400a08b18018115d002c0d6200401a0c00803348010066500200cc6005800a4008bb264008bb20c007bb1ac008bb1a4000ad10c11aaa9f4000a9d0c000a8d0c110a7df4009a7ddc109a7dd4009a7dcc009a51f401b866840158227c015821040007ced000b79ca40005decc0085b2cc0085b27c0085a2d00155162400f32e5400e2fab800f2f65400b29a4400e1e61c1160a23c00003d0c01601d0400e0025410e83d410061946b80105e57900011aca400046a2900011a1ec018412b40000b66940002d8a50000b2ec00002999f0000a3e7c00028d9f0000a2e7c0002809f00009f67c0002799f00009d67c00008aa5000022694000088a500541f1ac01a02fa600500a23c022022a6004c07298000007b4000c007c8003001f1800c007c4003000f1000c003c2016f8f4027fce009ff28027fc400de0b4017bd6005ef50017bce005ef2800fbc6005ef1000365e000d9180037d8000df200037c4000df0802f3c4000bf18002fc4000af18002bc40007f38001fca0006f38001bca0002f38000bca0002f18000bc40030f5800c3d4003ff0800fbda003ef5800fbd4003ef1800f7da003df5000f7ce003df2800f7c6003df10002fd4000af50002bce0009f500027ce0009f280023d40008f380023ca0008f18001bd40005f500017ce0004f500013ce0004f28000bd40001f500007ce0000f500003ce0008794000ff50001fe70003fca0007f90000ef50001de70003bca0007790000ef180019eb0002fd60005fa8000af580015e700027d60004fa80009f380013e400222ba00047ac0008f500011e700023c8000478c0006f38000de500013ce0001f9c0003f280007e400003ca

def seedRules9 (i : Nat) : Nat := 0x2adb79adc17a99b289b2a3d944ed51357ac3328d46f5d9d2ac8e9a7699a989ef29d679d9e44fb2d8913ef8ec2b8989898842c9090392194fda78a4d86c361b0cf033b75dad278deb3297becfeeeeaafa78bfff279528baf7624e3e5ee7cf7dce7c9babbf8bafc787b7b5ba7c11a9517b13f052dba21411a88000e7c6fe11088467eb5ad686a5c00000000002

def seedScores9 (i : Nat) : Nat := 0x330534149d

def seedCount : Nat → Nat
  | 9 => 187
  | 10 => 3340
  | 11 => 6414
  | 12 => 1359
  | 13 => 68
  | 14 => 2
  | _ => 0

def seedLookup : Nat → Nat → Nat
  | 9 => seedLookup9
  | 10 => seedLookup10
  | 11 => seedLookup11
  | 12 => seedLookup12
  | 13 => seedLookup13
  | 14 => seedLookup14
  | _ => fun _ => 0

def seedRuleCodes : Nat → Nat → Nat
  | 9 => seedRuleCodes9
  | 10 => seedRuleCodes10
  | 11 => seedRuleCodes11
  | 12 => seedRuleCodes12
  | 13 => seedRuleCodes13
  | 14 => seedRuleCodes14
  | _ => fun _ => 0

def seedHeaders : Nat → Nat → Nat
  | 9 => seedHeaders9
  | 10 => seedHeaders10
  | 11 => seedHeaders11
  | 12 => seedHeaders12
  | 13 => seedHeaders13
  | 14 => seedHeaders14
  | _ => fun _ => 0

def seedNodes : Nat → Nat → Nat
  | 9 => seedNodes9
  | 10 => seedNodes10
  | 11 => seedNodes11
  | 12 => seedNodes12
  | 13 => seedNodes13
  | 14 => seedNodes14
  | _ => fun _ => 0

def seedRules : Nat → Nat → Nat
  | 9 => seedRules9
  | 10 => seedRules10
  | 11 => seedRules11
  | 12 => seedRules12
  | 13 => seedRules13
  | 14 => seedRules14
  | _ => fun _ => 0

def seedScores : Nat → Nat → Nat
  | 9 => seedScores9
  | 10 => seedScores10
  | 11 => seedScores11
  | 12 => seedScores12
  | 13 => seedScores13
  | 14 => seedScores14
  | _ => fun _ => 0

def seedHashParams : Nat → Nat × Nat × Nat × Nat
  | 9 => (77, 278, 7, 8)
  | 10 => (1090, 4319, 12, 12)
  | 11 => (2117, 8449, 13, 13)
  | 12 => (434, 1702, 11, 11)
  | 13 => (34, 111, 6, 7)
  | 14 => (1, 2, 1, 1)
  | _ => (1,1,1,1)

def seedCodeParams : Nat → List (Nat × Nat × Nat × Nat)
  | 9 => [(3,0,1,0), (4,2,3,1), (5,10,4,4), (6,28,9,8), (7,74,40,17), (8,228,28,57)]
  | 10 => [(3,0,1,0), (4,2,1,1), (6,12,7,2), (7,38,23,9), (8,122,57,32), (9,358,67,89), (10,850,95,156), (11,1890,81,251), (12,3942,87,332), (13,8058,134,419)]
  | 11 => [(4,0,1,0), (5,2,1,1), (6,6,6,2), (7,24,27,8), (8,102,71,35), (9,346,91,106), (10,874,79,197), (11,1906,73,276), (12,3958,81,349), (13,8078,75,430), (14,16306,54,505), (15,32720,48,559)]
  | 12 => [(5,0,2,0), (6,4,26,2), (7,60,31,28), (8,182,36,59), (9,436,29,95), (10,930,51,124), (11,1962,49,175), (12,4022,51,224), (13,8146,32,275), (14,16356,28,307)]
  | 13 => [(4,0,4,0), (5,8,14,4), (6,44,13,18), (7,114,6,31), (8,240,9,37), (9,498,14,46)]
  | 14 => [(3,0,3,0), (4,6,10,3)]
  | _ => []

def seedColumnCount : Nat := 266

def seedSamples (i : Nat) : Bits × Bits := deadsamples[i]?.getD (0,0)

def posSample := asRow fun j => (seedSamples j).1

def negSample := asRow fun j => (seedSamples j).2

theorem seedPairs : properPairs graph posSample negSample := by
  rw [← chart_full]
  exact chart_pairs (by decide +kernel) (by decide +kernel)

def seedRaw : List Decor :=
  rawDecor 511 (fun j => (seedSamples j).1) (fun j => (seedSamples j).2)

def seedHeader (k i : Nat) : Nat :=
  packedAt (seedHeaders k) (75*(i/32)) 75

def unpackGate (x : Nat) : Nat :=
  if x < 960 then
    let pair := packedAt seedGatePairs (8*(x >>> 3)) 8
    pair ||| (((x >>> 2) &&& 1) <<< 8) ||| ((x &&& 3) <<< 10)
  else 512 ||| ((x-960) >>> 1) ||| ((x &&& 1) <<< 10)

def seedMeta (k i : Nat) : Nat × Nat :=
  let h := seedHeader k i
  let ofs := getFieldV h 15 20
  let pw := getFieldV h 71 4
  let w := packedAt (seedNodes k) (ofs+(22+pw)*(i %32)) (10+pw)
  (unpackGate (w &&& 1023), getFieldV h 0 15 + (w >>> 10))

def seedTrace : Nat → Nat → Nat × Nat
  | 0,i => (352, if i=0 then 511 else 1023)
  | n+1,i =>
    let (v,p) := seedMeta (13-n) i
    let (code,live) := seedTrace n p
    let lhs := if v.testBit 10 then 0 else 1 <<< (v &&& 15)
    let rhs := if v.testBit 11 || (getFieldV v 8 2 == 2) then 0 else 1 <<< getFieldV v 4 4
    let lost := live &&& (lhs ||| rhs)
    (code ||| ((v &&& 1023) <<< (10*(n+1))), (live ^^^ lost) ||| (1 <<< (10+n)))

def seedData (k i : Nat) : Nat × List Decor × List Decor :=
  let (code,live) := seedTrace (14-k) i
  let bank := decodeBank (15-k) code seedRaw
  (code, bank, selectLive live bank)

def seedLive (k i : Nat) : List Sig := (seedData k i).2.2.map Prod.fst

def seedReadColumn (i : Nat) : ColumnInfo :=
  let v := packedAt seedColumnWords (40*i) 40
  (getFieldV v 0 9, getFieldV v 9 9, getFieldV v 18 9, getFieldV v 27 9, v >>> 36)

def columnCheck (i : Nat) : Bool :=
  let c := seedReadColumn i
  if c = aliasColumn then true else colCheck 511 c (boundsBefore known383)

def allSeedColumns : Bool := (List.range seedColumnCount).all columnCheck

theorem seedColumnOK (hc : allSeedColumns=true) (i : Nat) (h : i<seedColumnCount) :
    Slice (vars 511) graph (columnDomain (seedReadColumn i)) (seedReadColumn i).2.2.2.2 := by
  exact column_sound _ _ (before_sound _ valid383) (List.all_eq_true.mp hc i (List.mem_range.mpr h))

def seedPool (k code : Nat) (bank : List Decor) (ci paid : Nat) : Option BoundPool :=
  if ci < seedColumnCount then
    let c := seedReadColumn ci
    materialize (vars 511) (chosenSteps bank code paid (15-k)) (columnDomain c) c.2.2.2.2
  else none

set_option maxRecDepth 20000 in
theorem seedPool_sound (hc : allSeedColumns=true) {k code bank ci paid p}
    (h : seedPool k code bank ci paid=some p) : ValidPool (vars 511) graph p := by
  unfold seedPool at h
  split at h
  · rename_i valid
    exact materialize_sound (seedColumnOK hc ci valid) h
  · contradiction

def reversedByte (n : Nat) : Nat :=
  packedAt seedReversedBytes (8*(n &&& 255)) 8

def seedCode (k code : Nat) : Nat × Nat :=
  let rev := (reversedByte code <<< 8) ||| reversedByte (code >>> 8)
  let check := fun (w,c,n,i) =>
    let x := rev >>> (16-w)
    if c ≤ x ∧ x < c+n then some (w,i+x-c) else none
  ((seedCodeParams k).findSome? check).getD (1,0)

def readSeedCodes (k : Nat) : Nat → Nat → Nat → List (Nat × Nat)
  | 0,_,_ => []
  | n+1,atBit,lim =>
    if atBit ≥ lim then [] else
      let code := packedAt (seedRules k) atBit 16
      let (w,id) := seedCode k code
      let r := packedAt (seedRuleCodes k) (15*id) 15
      (r &&& 511, r >>> 9) :: readSeedCodes k n (atBit+w) lim

def seedListOffsets (k i : Nat) : Nat × Nat × Nat × Nat :=
  let h := seedHeader k i
  let rs := getFieldV h 35 20
  let ss := getFieldV h 55 16
  let ofs := getFieldV h 15 20
  let pw := getFieldV h 71 4
  let row := i %32
  let w := 22+pw
  let bits := packedAt (seedNodes k) ofs (w*(row+1))
  let metadata := fun j => getFieldV bits (j*w+10+pw) 12
  let (rr,sr) := (List.range row).foldl (fun (x,y) j =>
    let v := metadata j
    (x+(v &&& 255), y+8*(v>>>8))) (rs,ss)
  let v := metadata row
  (rr,rr+(v &&& 255),sr,v >>> 8)

def seedScoreCodes (k start n : Nat) : List Nat :=
  (List.range n).map fun i =>
    let j := packedAt (seedScores k) (start+8*i) 8
    packedAt seedScoreWords (54*j) 54

def countBits32 (x : Nat) : Nat :=
  let x := x - ((x >>> 1) &&& 0x55555555)
  let x := (x &&& 0x33333333) + ((x >>> 2) &&& 0x33333333)
  let x := (x+(x >>> 4)) &&& 0x0f0f0f0f
  ((x*0x01010101) >>> 24) &&& 255

def seedHashLookup (k h : Nat) : Nat × Nat :=
  let (nb,slots,dw,iw) := seedHashParams k
  let key := h % 18446744073709551616
  let a := key %nb
  let disp := packedAt (seedLookup k) (a*dw) dw
  let row := (key/nb+disp)%slots
  let idx := packedAt (seedLookup k) (nb*dw+row*iw) iw
  let start := nb*dw+slots*iw
  let rotBlock := packedAt (seedLookup k) (start+46*(row/32)) 46
  let mask := rotBlock >>> 14
  let slot := row %32
  let ord := (rotBlock &&& 16383) + countBits32 (mask &&& ((1 <<< slot)-1))
  (idx, if mask.testBit slot then
    packedAt (seedLookup k) (start+46*((slots+31)/32)+4*ord) 4 else 0)

def seedLinked (k h : Nat) : List (List Sig) :=
  let (idx,pi) := seedHashLookup k h
  if idx < seedCount k then
    match seedAutos[pi]? with
    | none => []
    | some p => [(seedLive k idx).map (movedWord (p.map swapRows).reverse)]
  else []

def seedAutoCheck : Bool :=
  seedAutos.toList.all fun p => autoOK graph (p.map swapRows)

theorem seedLink_sound (autos : seedAutoCheck = true) {k h xs}
    (prior : ∀ i < seedCount k, Impossible graph k (seedLive k i).toFinset)
    (hm : xs ∈ seedLinked k h) :
    Impossible graph k xs.toFinset := by
  rcases hi : seedHashLookup k h with ⟨idx,pi⟩
  simp only [seedLinked,hi] at hm
  split at hm
  next access =>
    split at hm
    · simp at hm
    next p hp =>
      rcases List.mem_singleton.mp hm with rfl
      exact rotate_excluded (prior idx access) _ (List.all_eq_true.mp autos p (by simpa using Array.mem_of_getElem? hp))
  · simp at hm

def seedContext (k i : Nat) : NodeContext :=
  let (code,bank,ws) := seedData k i
  let (start,last,s,n) := seedListOffsets k i
  let pools := (readSeedCodes k 32 start last).filterMap (fun (ci,paid) => seedPool k code bank ci paid)
  (k,ws.length,ws,preCov ws,pools,seedLinked (k-1),readOnceReject graph (seedScoreCodes k s n))

def seedVerify (k i : Nat) : Bool :=
  let c := seedContext k i
  prelim graph c && testAll c c.2.2.1

theorem seedVerify_sound (columns : allSeedColumns=true) (autos : seedAutoCheck=true)
    {k i} (prior : ∀ j < seedCount (k-1), Impossible graph (k-1) (seedLive (k-1) j).toFinset)
    (checked : seedVerify k i=true) : Impossible graph k (seedLive k i).toFinset := by
  simp only [seedVerify, prelim, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    List.contains_eq_mem] at checked
  have nd : (seedLive k i).Nodup := checked.1.1
  have out : graph ∉ seedLive k i := by
    simpa [seedLive,seedContext] using checked.1.2
  apply node_sound (raw:=vars 511) seedPairs _ nd out _ _ _ checked.2
  · intro w hw
    apply decode_faithful _ _ _ _
    · exact raw_faithful 511 _ _
    · exact (selectLive_sub _ _).subset hw
  · intro p hp
    obtain ⟨⟨a,b⟩,_,hh⟩ := List.mem_filterMap.mp hp
    exact seedPool_sound columns hh
  · intro h ys hm
    exact seedLink_sound autos prior hm
  · intro _ _ nd hh
    exact readOnceReject_sound nd hh

def seedSpan (k offset : Nat) : Nat → Bool
  | 0 => true
  | n+1 => seedVerify k (offset+n) && seedSpan k offset n

theorem seedSpan_at {k o n} (h : seedSpan k o n=true) :
    ∀ i, o ≤ i → i < o+n → seedVerify k i=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    intro i lo hi
    simp only [seedSpan,Bool.and_eq_true] at h
    by_cases e : i=o+n
    · exact e.symm ▸ h.1
    · exact ih h.2 i lo (by omega)

def seedContexts (k offset n : Nat) : List NodeContext :=
  (List.range n).map fun j => seedContext k (offset+j)

def seedBatch (k offset n ar : Nat) : Bool :=
  let cs := seedContexts k offset n
  cs.all (fun c => c.2.1==ar && prelim graph c) && runBatch k ar cs

theorem seedBatch_at {k offset n ar} (ok : seedBatch k offset n ar=true)
    {i} (lo : offset ≤ i) (hi : i < offset+n) : seedVerify k i=true := by
  simp only [seedBatch,Bool.and_eq_true] at ok
  let cs := seedContexts k offset n
  let j := i-offset
  have hj : j < cs.length := by simp [cs, seedContexts, j]; omega
  have hc : cs[j] = seedContext k i := by
    simp [cs, seedContexts, j, Nat.add_sub_of_le lo]
  have head := List.all_eq_true.mp ok.1 cs[j] (List.getElem_mem hj)
  simp only [Bool.and_eq_true,beq_iff_eq] at head
  have size : cs[j].2.2.1.length = cs[j].2.1 := by rw [hc]; rfl
  have body := runBatch_at hj (by rw [hc]; rfl) head.1 (size.trans head.1) ok.2
  change (prelim graph (seedContext k i) && testAll (seedContext k i) (seedContext k i).2.2.1) = true
  rw [← hc, Bool.and_eq_true]
  exact ⟨head.2,body⟩

def seedBatchSpan (k offset ar : Nat) : Nat → Bool
  | 0 => true
  | n+1 => seedBatch k (offset+16*n) 16 ar && seedBatchSpan k offset ar n

theorem seedBatchSpan_at {k offset ar n} (ok : seedBatchSpan k offset ar n=true)
    {i} (lo : offset ≤ i) (hi : i<offset+16*n) : seedVerify k i=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [seedBatchSpan,Bool.and_eq_true] at ok
    by_cases h : i<offset+16*n
    · exact ih ok.2 h
    · exact seedBatch_at ok.1 (by omega) (by omega)

theorem seedAll_sound (columns : allSeedColumns=true) (autos : seedAutoCheck=true)
    (checks : ∀ k ≤ 14, ∀ i < seedCount k, seedVerify k i=true) :
    ∀ k ≤ 14, ∀ i < seedCount k, Impossible graph k (seedLive k i).toFinset := by
  intro k
  induction k with
  | zero => intro _ i hi; have h : seedCount 0 = 0 := rfl; omega
  | succ k ih =>
    intro lk i li
    apply seedVerify_sound columns autos
    · exact ih (by omega)
    · exact checks _ lk i li
abbrev SeedChunk := Nat × Nat × Nat

def seedChunk (k : Nat) (p : SeedChunk) : Bool :=
  let (start,n,ar) := p
  let grouped := n/16
  seedBatchSpan k start ar grouped && seedSpan k (start+16*grouped) (n %16)

theorem seedChunk_sound {k : Nat} {p : SeedChunk} (ok : seedChunk k p=true)
    {i : Nat} (lo : p.1 ≤ i) (hi : i < p.1 + p.2.1) : seedVerify k i=true := by
  rcases p with ⟨o,n,a⟩
  change o ≤ i at lo
  change i < o+n at hi
  simp only [seedChunk,Bool.and_eq_true] at ok
  have hcalc : 16*(n/16)+n %16=n := Nat.div_add_mod n 16
  by_cases h : i<o+16*(n/16)
  · exact seedBatchSpan_at ok.1 lo h
  · exact seedSpan_at ok.2 i (by omega) (by omega)

def seedPlan : Nat → List SeedChunk
  | 9 => [(0,128,9), (128,57,9), (185,2,10)]
  | 10 => [(0,49,9), (49,128,10), (177,128,10), (305,128,10), (433,128,10), (561,128,10), (689,128,10), (817,128,10), (945,128,10), (1073,128,10), (1201,128,10), (1329,128,10), (1457,128,10), (1585,128,10), (1713,128,10), (1841,128,10), (1969,128,10), (2097,128,10), (2225,128,10), (2353,128,10), (2481,128,10), (2609,128,10), (2737,128,10), (2865,128,10), (2993,128,10), (3121,128,10), (3249,83,10), (3332,8,11)]
  | 11 => [(0,13,9), (13,128,10), (141,128,10), (269,128,10), (397,128,10), (525,128,10), (653,128,10), (781,128,10), (909,94,10), (1003,128,11), (1131,128,11), (1259,128,11), (1387,128,11), (1515,128,11), (1643,128,11), (1771,128,11), (1899,128,11), (2027,128,11), (2155,128,11), (2283,128,11), (2411,128,11), (2539,128,11), (2667,128,11), (2795,128,11), (2923,128,11), (3051,128,11), (3179,128,11), (3307,128,11), (3435,128,11), (3563,128,11), (3691,128,11), (3819,128,11), (3947,128,11), (4075,128,11), (4203,128,11), (4331,128,11), (4459,128,11), (4587,128,11), (4715,128,11), (4843,128,11), (4971,128,11), (5099,128,11), (5227,128,11), (5355,128,11), (5483,128,11), (5611,128,11), (5739,128,11), (5867,128,11), (5995,128,11), (6123,128,11), (6251,119,11), (6370,44,12)]
  | 12 => [(0,3,9), (3,128,10), (131,97,10), (228,128,11), (356,128,11), (484,128,11), (612,128,11), (740,128,11), (868,33,11), (901,128,12), (1029,128,12), (1157,128,12), (1285,74,12)]
  | 13 => [(0,1,9), (1,25,10), (26,42,11)]
  | 14 => [(0,1,9), (1,1,10)]
  | _ => []

def planCovers (k : Nat) : Bool :=
  (List.range (seedCount k)).all fun i =>
    (seedPlan k).any fun p => decide (p.1 ≤ i ∧ i < p.1 + p.2.1)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem seedPlanCovers (k : Nat) (hk : k≤14) : planCovers k=true := by
  interval_cases k <;> decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem seedChecked9 : (seedPlan 9).all (seedChunk 9) = true := by
  simp only [seedPlan, List.all_cons, List.all_nil, Bool.and_eq_true]
  repeat' apply And.intro
  all_goals try simp only [seedChunk, Nat.reduceDiv, Nat.reduceMod, seedBatchSpan, seedSpan, Bool.and_eq_true]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem seedChecked10 : (seedPlan 10).all (seedChunk 10) = true := by
  simp only [seedPlan, List.all_cons, List.all_nil, Bool.and_eq_true]
  repeat' apply And.intro
  all_goals try simp only [seedChunk, Nat.reduceDiv, Nat.reduceMod, seedBatchSpan, seedSpan, Bool.and_eq_true]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem seedChecked11 : (seedPlan 11).all (seedChunk 11) = true := by
  simp only [seedPlan, List.all_cons, List.all_nil, Bool.and_eq_true]
  repeat' apply And.intro
  all_goals try simp only [seedChunk, Nat.reduceDiv, Nat.reduceMod, seedBatchSpan, seedSpan, Bool.and_eq_true]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem seedChecked12 : (seedPlan 12).all (seedChunk 12) = true := by
  simp only [seedPlan, List.all_cons, List.all_nil, Bool.and_eq_true]
  repeat' apply And.intro
  all_goals try simp only [seedChunk, Nat.reduceDiv, Nat.reduceMod, seedBatchSpan, seedSpan, Bool.and_eq_true]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem seedChecked13 : (seedPlan 13).all (seedChunk 13) = true := by
  simp only [seedPlan, List.all_cons, List.all_nil, Bool.and_eq_true]
  repeat' apply And.intro
  all_goals try simp only [seedChunk, Nat.reduceDiv, Nat.reduceMod, seedBatchSpan, seedSpan, Bool.and_eq_true]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem seedChecked14 : (seedPlan 14).all (seedChunk 14) = true := by
  simp only [seedPlan, List.all_cons, List.all_nil, Bool.and_eq_true]
  repeat' apply And.intro
  all_goals try simp only [seedChunk, Nat.reduceDiv, Nat.reduceMod, seedBatchSpan, seedSpan, Bool.and_eq_true]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

theorem allSeedChecked (k : Nat) (h : k≤14) :
    (seedPlan k).all (seedChunk k)=true := by
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact seedChecked9
  · exact seedChecked10
  · exact seedChecked11
  · exact seedChecked12
  · exact seedChecked13
  · exact seedChecked14

theorem seedChecked (k : Nat) (hk : k≤14) (i : Nat) (hi : i<seedCount k) :
    seedVerify k i=true := by
  have plan := List.all_eq_true.mp (seedPlanCovers k hk) i (List.mem_range.mpr hi)
  obtain ⟨p,hp,h⟩ := List.any_eq_true.mp plan
  have h' : p.1 ≤ i ∧ i < p.1 + p.2.1 := of_decide_eq_true h
  exact seedChunk_sound (List.all_eq_true.mp (allSeedChecked k hk) p hp) h'.1 h'.2

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checkedColumns : allSeedColumns = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checkedAutos : seedAutoCheck = true := by decide +kernel

theorem checkedRoots :
    Impossible graph 14 inputs.toFinset ∧ Impossible graph 14 (inputs ++ [firstWire]).toFinset := by
  have plain := seedAll_sound checkedColumns checkedAutos seedChecked 14 (by decide) 0 (by decide)
  have both := seedAll_sound checkedColumns checkedAutos seedChecked 14 (by decide) 1 (by decide)
  rw [show seedLive 14 0 = inputs from by decide +kernel] at plain
  rw [show seedLive 14 1 = inputs ++ [firstWire] from by decide +kernel] at both
  exact ⟨plain,both⟩

end PEqualNP.Outside.L_meta_1677

theorem PEqualNP.Outside.L_meta_1677 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 6)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size :=
  PEqualNP.Outside.L_meta_1677.completedRoots PEqualNP.Outside.L_meta_1677.checkedRoots.1
    PEqualNP.Outside.L_meta_1677.checkedRoots.2
