import PEqualNP.Defs

-- The live-wire framework and induced-subgraph lower bounds build on the checked
-- L-meta-1667 and L-meta-1920 proofs, including PressF10’s work in PR 4332 (Apache-2.0).
-- The signed rank certificate and its verifier are adapted from zakpgrove's PR 10495.
-- The cut and rewiring argument is adapted from dsgallups's PR 8990 and andybak's PR 10368.
namespace PEqualNP.Outside.L_meta_3250
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
theorem graph_proper : proper graph := by unfold proper; decide +kernel
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
def vertex (m j : Nat) := if m.testBit j then (if m.testBit 9 && j == 4 then neg (inputs.getD 4 zero) else inputs.getD j zero) else zero
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
  let base := if m.testBit 9 && m.testBit 4 then 16 else 0
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
  let baseRow := if m.testBit 9 && free.testBit 4 then 16 else 0
  let xs := supportPairs baseRow s
  let count := (xs.map Prod.fst).toFinset.card
  let drop := colFree free q 0
  let lz := if m.testBit 9 && drop.testBit 4 then drop &&& (511 ^^^ 16) else drop
  let lo := if m.testBit 9 && drop.testBit 4 then 16 else 0
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
  let baseRow := if m.testBit 9 && free.testBit 4 then 16 else 0
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
  let x := fun j => if m.testBit j then (if m.testBit 9 && j == 4 then ~~~(v 4) else v j) else 0
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then (if m.testBit 9 && j.val == 4 then ~~~(v 4) else v j.val) else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · by_cases hf : (m.testBit 9 && j.val == 4) = true
    · have hj4 : j.val = 4 := by
        simp only [Bool.and_eq_true, beq_iff_eq] at hf; exact hf.2
      simp only [vertex, hh, hf, ite_true, bit_neg, BitVec.getLsbD_not, i.isLt, decide_true, Bool.true_and]
      exact congrArg Bool.not (asRow_bit v i ⟨4, by decide⟩)
    · simpa [vertex, hh, hf] using asRow_bit v i j
  · simp [vertex, hh, bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then (if m.testBit 9 && j == 4 then ~~~(v 4) else v j) else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
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

abbrev ExtraCut := Nat → List Sig → Bool
abbrev ChildLinks := (Nat → List (List Sig)) × ExtraCut

def closeChild (pools : List BoundPool) (links : ChildLinks) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links.1 (keySet ws)).any (sameWords ws) || pools.any (fun p => scalarPoolCut p k rest op) || links.2 k ws

theorem closeChild_sound {raw T pools} {links : ChildLinks} {k rest op}
    (pValid : ∀ p ∈ pools, ValidPool raw T p)
    (lValid : ∀ tag xs, xs ∈ links.1 tag → Impossible T k (List.toFinset xs))
    (cutValid : ∀ ws : List Sig, ws.Nodup → links.2 k ws = true → Impossible T k ws.toFinset)
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild pools links k rest op = true) :
    Impossible T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with (⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩) | cutProof
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · exact scalarPoolCut_sound (pValid _ hp) nd ok
  · exact cutValid _ nd cutProof

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

abbrev NodeContext := Nat × Nat × List Decor × CovPair × List BoundPool × ChildLinks
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
theorem evalMove_sound {raw T r s ws pools} {links : ChildLinks} {cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : (op==2)=false → a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links.1 tag → Impossible T (cap-1) (List.toFinset xs))
    (cv : ∀ words : List Sig, words.Nodup → links.2 (cap-1) words = true → Impossible T (cap-1) words.toFinset)
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
  exact closeChild_sound pv lv cv nd' test k t hk h

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

theorem node_sound {raw T r s ws pools} {links : ChildLinks} {cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links.1 tag → Impossible T (cap-1) (List.toFinset xs))
    (cv : ∀ words : List Sig, words.Nodup → links.2 (cap-1) words = true → Impossible T (cap-1) words.toFinset)
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
    exact evalMove_sound pairs faith nd ha ha (by simp) hc' pv lv cv pro fresh (all_unary checks ha keep)
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
      exact evalMove_sound pairs faith nd aa bb (fun _ e => ne' (congrArg Prod.fst e)) hc' pv lv cv
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
  cut : ExtraCut := fun _ _ => false
  cut_sound : ∀ k (ws : List Sig), ws.Nodup → cut k ws = true → Impossible (chartGoal mask) k ws.toFinset := by
    intros
    contradiction

  recipes3095 : Option (Nat → Nat → Nat × Nat) := none
  rules3095 : Option (Nat → Nat → List (Nat × Nat)) := none

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
  let packet := match g.recipes3095 with
    | some reader => reader k i
    | none =>
      let recp := packedAt data (i*width) width
      (recp &&& ((1 <<< len)-1),recp >>> len)
  let ops := packet.1
  let bank := decodeBank depth ops raw
  (ops,bank,selectLive packet.2 bank)

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
  let entries := match g.rules3095 with
    | some reader => reader k i
    | none => getPairs data cw depth nr st
  let rules := entries.filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  decide values.Nodup && !(values.contains (targetOf g)) &&
    (if k=0 then true else testAll (k,ws.length,ws,preCov ws,rules,ls,g.cut) ws)

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
  apply node_sound (raw:=vars g.mask) samples _ hN hT _ _ (g.cut_sound _) (by simpa only [h0,if_false] using checked.2)
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
def contextOf (g : Forest) (k i : Nat) : NodeContext :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let start := num*(10*storedDepth g depth+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 5
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let entries := match g.rules3095 with
    | some reader => reader k i
    | none => getPairs data cw depth nr st
  let rules := entries.filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  (k,ws.length,ws,preCov ws,rules,ls,g.cut)

def prelim (T : Sig) (c : NodeContext) :=
  let ws := c.2.2.1.map Prod.fst
  decide ws.Nodup && !(ws.contains T)
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
def deadsamples : Array (Bits × Bits) := #[(0xf854605d026923a5a16008862c9d18d42fd85e54d221898f1e440284a107a02910c3e03c06c40d2642ca74f54627022c11e389d9b43b30c961ca72386ce81500aa210d1ba1a121108a6c99348979d054ac200727ac054c0970110780155ad581,0x6844620d0040231585204884208800c4270824141201090814040082a10700282003e02402c4084602ca04a440240a1091218919100a2084314a220840a00480aa210819a02120100a4409048968c05484200702a805440920100380144a9480),(0x80b20c31f72bfc4e1481d27000d43c9c5bd438a9c5e0286040f054f111d001ce10920229bde170b8d339029e2bcac4cd494fb74d1052452141a61c5b9ca1e642f40c600258428f0e5c00df481e03202a204cd465e10fe01206e82c7b03150603,0x80100c30e6089040109182600012282018c41889c5e0204002b0604000c009861080028b1c2120a0d12000120908c00d005a724402504200402010501c01c208540860025840090e1400964816012008204cd0254102a00206a0247b01150201),(0x12ce100c308544478a85796a2341d206e4242e31335abb35943abb40be28c8e05c4c115123137950052a02a9ba0d31c096458c656cc338623e92230683d8962194d5145c2aa62229438824d8e06246d0cd124850733918c390189888a426380a,0x10ca0000108540870900790a0240900460282200221a991490081a0028289000cc41010021184410080a0a28a20020c0200184206c0128621092200a03d8103080d5145c02a2022143880090804206d04d100840322918c190088800a4221002),(0x8628ebbd17000228c83c0291b729e17b3643984a392a815889878936d04e41b82b8e28807cc302855ead3105d9868885c748c2b0724ae81086518e259124cd4278a18b4aa01db88524c3a3435a0814469349110c18f0c24c2a8052bd88818268,0xc2206a1d05000020401c0090e509051303449848110100480001811490070429238c000818c508010485900541c68805c240409012420000024186258024450270208b02a00da0842041a3414a08100690490104085040042a8052bc00818028),(0xbc8ccda8781e4d8151cd3cf93a4a0a01509a42078c1bc4a783ea4aec6c7bbbd02ef85be130b1750bcd872a062d01842a34826040203d5b99ac8899721d47b82106b4f88001d04ee6f42e103eb14e0a090b95e84905a08ef7a2230402e2b14bc5,0x148981a0109a5c8210c1a4690a42220050930202c418c4a7837a48680e50b9d00c601bc02020f518c9002a002c1124282402304220255b598c9019921c51b8010494708001d04e62d42a103a30060a090b94e84905a08af280230402e2304b45),(0xd3b19712becef4647857054f8773c68492608a46265cd6cd0106c449284294958830b40e8328a4102841c46a63b66493288c7290c714876750b08cb0eb0a532e014ce7e24f9c08720240400006971f885be46b00080a21145aa7f52cf42a8012,0x92218c003e8654007015040a0c73c50280c0084821449285810a8400004080918c301008002824100801c000230200c0688c40804110046300b00cb28307502a0004c5624f9c086200004000021315805bc46800000a00145205f42ce0200002),(0x3145d24845746a93b60987114c89950ee90ab5809889781e716b0d141d9e036fea797f20c896480c8b565809c5575a81eabcad03980701be24b7e8d7401960b32336416db2f0c4c050f169960250e8b311988b92828b0074bd455ad232c2112c,0x2307720c00346283a400011d4c09950fa108a4001a095004514a0014181e2261ab3d3060c0d6480a2ac41009e4571880ea848181d90321bc24d38a860208103323340169a2b084c040f169960050c8b211800b9082890074b8455a803282012c),(0x49615339cc24bb41a658244591d020101222d0f578b5376254a121290a30cd5c4e2ad1d6dabfa9e032f022500c91031b32331a7a9ace0ca4e96243014a4009cd0d2a3210b66014de852533c420acc80ff443ad9cc5d0f4808cd621151170ac54,0x4900539a4030aa408668006591882010120251355ca1242200a1212102144d6e020a42d6d2878b6832b420400cb9813312321a4a924e408ce04943054c0001c10d2a2200b040149c8425334420acc80fa003859cc5d0e4000cd201111150ac54),(0x2108654280dbc21c532263cad6a2ab60a053058994f658a43b3dd89384745a04932387065124c385d01899e2cc083e3c1e3327061d61ca921a4965c8583262f4485320b5c04953298d1f02098424a39520b6148b236021a80528c3236c545ab4,0xc0001428049001c03a04a4012802a200013019184320c200a34088304a0580410028702010083a440180cc2080827381411260a0400ca0098085048489022c408432094004053098d0e0008842422012032140b21202188052801030c545a90)]
def deadautos : Array (List Nat) := #[[],[118,130,81],[100,131,82,16],[118,133,100,131,50,33,16],[116,83,32],[118,116,83,130,49,32],[118,133,33,48],[82,129,48],[118,133,116,83,82,81,80],[116,50,129,80],[100,49,128],[118,100,83,130,81,128]]

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
def g15 : Forest := ⟨15,3,fun j => g15samples[j]?.getD (0,0),g15columns,g15autos,g15levels,g15index,fun _ _ => false, by simp,none,none⟩
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
def g31 : Forest := ⟨31,6,fun j => g31samples[j]?.getD (0,0),g31columns,g31autos,g31levels,g31index,fun _ _ => false, by simp,none,none⟩
def g47 : Forest := ⟨47,4,fun _ => (0,0),.leaf [],#[],fun _ => emptyPacking,fun _ _ => none,fun _ _ => false,by simp,none,none⟩
def g55 : Forest := ⟨55,4,fun _ => (0,0),.leaf [],#[],fun _ => emptyPacking,fun _ _ => none,fun _ _ => false,by simp,none,none⟩
def g63 : Forest := ⟨63,7,fun _ => (0,0),.leaf [],#[],fun _ => emptyPacking,fun _ _ => none,fun _ _ => false,by simp,none,none⟩
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
def g111 : Forest := ⟨111,6,fun j => g111samples[j]?.getD (0,0),g111columns,g111autos,g111levels,g111index,fun _ _ => false, by simp,none,none⟩
def g119 : Forest := ⟨119,5,fun _ => (0,0),.leaf [],#[],fun _ => emptyPacking,fun _ _ => none,fun _ _ => false,by simp,none,none⟩
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
def g189 : Forest := ⟨189,7,fun j => g189samples[j]?.getD (0,0),g189columns,g189autos,g189levels,g189index,fun _ _ => false, by simp,none,none⟩
def g127 : Forest := ⟨127,8,fun _ => (0,0),.leaf [],#[],fun _ => emptyPacking,fun _ _ => none,fun _ _ => false,by simp,none,none⟩
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
def g191 : Forest := ⟨191,10,fun j => g191samples[j]?.getD (0,0),g191columns,g191autos,g191levels,g191index,fun _ _ => false, by simp,none,none⟩
def g251 : Forest := ⟨251,7,fun _ => (0,0),.leaf [],#[],fun _ => emptyPacking,fun _ _ => none,fun _ _ => false,by simp,none,none⟩
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
theorem s15_3_0 : block g15 3 0 1=true := by
  decide +kernel
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
theorem s31_5_0 : block g31 5 0 1=true := by
  decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_5_1 : block g31 5 1 2=true := by
  decide +kernel
theorem bl31_5 : block g31 5 0 3 = true := (@block_merge g31 5 0 1 2 s31_5_0 s31_5_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem s31_6_0 : block g31 6 0 1=true := by
  decide +kernel
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
theorem s111_6_0 : block g111 6 0 1=true := by
  decide +kernel
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
theorem s189_6_0 : block g189 6 0 1=true := by
  decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_6_1 : block g189 6 1 2=true := by
  decide +kernel
theorem bl189_6 : block g189 6 0 3 = true := (@block_merge g189 6 0 1 2 s189_6_0 s189_6_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem s189_7_0 : block g189 7 0 1=true := by
  decide +kernel
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
theorem s191_6_0 : block g191 6 0 1=true := by
  decide +kernel
theorem bl191_6 : block g191 6 0 1 = true := s191_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem s191_7_0 : block g191 7 0 13=true := by
  decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_7_1 : block g191 7 13 15=true := by
  decide +kernel
theorem bl191_7 : block g191 7 0 28 = true := (@block_merge g191 7 0 13 15 s191_7_0 s191_7_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem s191_8_0 : block g191 8 0 7=true := by
  decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_1 : block g191 8 7 61=true := by
  decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_2 : block g191 8 68 32=true := by
  decide +kernel
theorem bl191_8 : block g191 8 0 100 = true := (@block_merge g191 8 0 68 32 (@block_merge g191 8 0 7 61 s191_8_0 s191_8_1) s191_8_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem s191_9_0 : block g191 9 0 3=true := by
  decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_9_1 : block g191 9 3 9=true := by
  decide +kernel
theorem bl191_9 : block g191 9 0 12 = true := (@block_merge g191 9 0 3 9 s191_9_0 s191_9_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem s191_10_0 : block g191 10 0 1=true := by
  decide +kernel
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

end PEqualNP.Outside.L_meta_3250

namespace PEqualNP.Outside.L_meta_3250.RankBase

-- The branch-group argument and circuit simplifier are adapted from L_meta_1549.
-- The simplifier tracks the number of non-NOT gates independently of length.

namespace CircuitProof

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

end CircuitProof

namespace CircuitProof

open PEqualNP.CircuitLowerBounds

variable {n : ℕ}

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

end CircuitProof

namespace CircuitProof

open PEqualNP.CircuitLowerBounds

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

def isNotGate (op : GateOp) : Bool :=
  match op with
  | .not => true
  | _ => false

def nonNotCount (gs : List Gate) : ℕ :=
  gs.countP (fun g => !(isNotGate g.op))

end CircuitProof

namespace CircuitProof

open PEqualNP.CircuitLowerBounds

def CleanGate (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])

def CleanL (m : ℕ) (gs : List Gate) : Prop :=
  ∀ (p : ℕ) (g : Gate), gs[p]? = some g → CleanGate (m + p) g

theorem CleanGate.nok {m : ℕ} {g : Gate} (h : CleanGate m g) : NOk g := by
  rcases h with ⟨h1, j, _, h2⟩ | ⟨h1 | h1, j, k, _, _, h2⟩
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inr rfl)
    · rw [h2]; simp
    · intro _; rw [h2]; simp
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inl rfl
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inl rfl)
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h

theorem CleanGate.lt {m : ℕ} {g : Gate} (h : CleanGate m g) : ∀ a ∈ g.inputs, a < m := by
  intro a ha
  rcases h with ⟨_, j, hj, h2⟩ | ⟨_, j, k, hj, hk, h2⟩
  · rw [h2] at ha
    simp at ha
    subst ha; exact hj
  · rw [h2] at ha
    simp at ha
    rcases ha with rfl | rfl
    · exact hj
    · exact hk

theorem getD_ofFn {α : Type} (m : ℕ) (F : Fin m → α) (d : α) (j : Fin m) :
    (List.ofFn F).getD j d = F j := by
  simp

theorem split_at {α : Type} : ∀ (l : List α) (p : ℕ) (g : α), l[p]? = some g →
    ∃ pre post, l = pre ++ g :: post ∧ pre.length = p := by
  intro l
  induction l with
  | nil => intro p g h; simp at h
  | cons x l ih =>
    intro p g h
    cases p with
    | zero =>
      simp at h
      subst h
      exact ⟨[], l, rfl, rfl⟩
    | succ p =>
      simp at h
      obtain ⟨pre, post, rfl, rfl⟩ := ih p g h
      exact ⟨x :: pre, post, rfl, rfl⟩

end CircuitProof

namespace CircuitProof

open PEqualNP.CircuitLowerBounds

def vl {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) : Bool :=
  (wiresFrom gs (List.ofFn u)).getD j false

theorem vl_input {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) (h : j < k) :
    vl gs u j = u ⟨j, h⟩ := by
  unfold vl
  rw [getD_wiresFrom gs _ j (by simpa using h)]
  exact getD_ofFn k u false ⟨j, h⟩

theorem vl_gate {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u : Fin k → Bool) (p : ℕ)
    (g : Gate) (hp : gs[p]? = some g) :
    vl gs u (k + p) = g.op.eval (g.inputs.map (vl gs u)) := by
  have hlt := (hcl p g hp).lt
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  have hwl : (wiresFrom pre (List.ofFn u)).length = k + pre.length := by
    rw [length_wiresFrom]; simp
  have e : wiresFrom (pre ++ g :: post) (List.ofFn u)
      = wiresFrom post (wiresFrom pre (List.ofFn u) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn u)).getD i false)]) := by
    rw [wiresFrom_append]; rfl
  have full : ∀ j, j < k + pre.length →
      (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD j false
        = (wiresFrom pre (List.ofFn u)).getD j false := by
    intro j hj
    rw [e, getD_wiresFrom _ _ j (by simp [hwl]; omega), getD_snoc_ne _ _ _ _ (by omega)]
  have top : (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
      = g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn u)).getD i false) := by
    rw [e, getD_wiresFrom _ _ _ (by simp [hwl]), getD_snoc_len _ _ _ _ hwl]
  show (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
    = g.op.eval (g.inputs.map fun j => (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD j false)
  rw [top]
  congr 1
  apply List.map_congr_left
  intro a ha
  exact (full a (hlt a ha)).symm

theorem vl_congr {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u u' : Fin k → Bool) (p : ℕ)
    (g : Gate) (hp : gs[p]? = some g) (h : ∀ a ∈ g.inputs, vl gs u a = vl gs u' a) :
    vl gs u (k + p) = vl gs u' (k + p) := by
  rw [vl_gate gs hcl u p g hp, vl_gate gs hcl u' p g hp]
  congr 1
  exact List.map_congr_left h

end CircuitProof

namespace PetersenCutTrace

open PEqualNP.CircuitLowerBounds
open CircuitProof

def avoid {W : Type} (edge : W → W → Prop) (cut : W) (a b : W) : Prop :=
  edge a b ∧ a ≠ cut ∧ b ≠ cut

theorem difference_traces {W : Type} (rank : W → Nat) (input : W → Prop)
    (edge : W → W → Prop) (cut : W) (x y : W → Bool)
    (order : ∀ a b, edge a b → rank a < rank b)
    (localStep : ∀ b, ¬ input b → x b ≠ y b → ∃ a, edge a b ∧ x a ≠ y a)
    (sameCut : x cut = y cut) {out : W} (different : x out ≠ y out) :
    ∃ a, input a ∧ x a ≠ y a ∧ Relation.ReflTransGen (avoid edge cut) a out := by
  classical
  have track : ∀ k b, rank b = k → x b ≠ y b →
      ∃ a, input a ∧ x a ≠ y a ∧ Relation.ReflTransGen (avoid edge cut) a b := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro b hb diff
      by_cases hInput : input b
      · exact ⟨b, hInput, diff, Relation.ReflTransGen.refl⟩
      · obtain ⟨p, hp, dp⟩ := localStep b hInput diff
        have earlier : rank p < k := (order p b hp).trans_eq hb
        obtain ⟨a, ha, da, path⟩ := ih (rank p) earlier p rfl dp
        have pOff : p ≠ cut := by rintro rfl; exact dp sameCut
        have bOff : b ≠ cut := by rintro rfl; exact diff sameCut
        exact ⟨a, ha, da, path.tail ⟨hp, pOff, bOff⟩⟩
  exact track (rank out) out rfl different

theorem cut_agreement {W : Type} (rank : W → Nat) (input : W → Prop)
    (edge : W → W → Prop) (cut out : W) (x y : W → Bool)
    (order : ∀ a b, edge a b → rank a < rank b)
    (localStep : ∀ b, ¬ input b → x b ≠ y b → ∃ a, edge a b ∧ x a ≠ y a)
    (sameCut : x cut = y cut)
    (blocked : ∀ a, input a → x a ≠ y a →
      ¬ Relation.ReflTransGen (avoid edge cut) a out) : x out = y out := by
  by_contra different
  obtain ⟨a, ha, da, reaches⟩ := difference_traces rank input edge cut x y
    order localStep sameCut different
  exact blocked a ha da reaches

theorem unary_factor {A : Type} (w f : A → Bool)
    (h : ∀ x y, w x = w y → f x = f y) :
    ∃ outer : Bool → Bool, ∀ x, outer (w x) = f x := by
  classical
  let outer (b : Bool) := if hb : ∃ a, w a = b then f (Classical.choose hb) else false
  refine ⟨outer, fun x => ?_⟩
  have hx : ∃ a, w a = w x := ⟨x, rfl⟩
  unfold outer
  rw [dite_eq_left hx]
  exact h _ _ (Classical.choose_spec hx)

def inputWire {n : Nat} (gs : List Gate) (v : Fin n) : Fin (n + gs.length) :=
  v.castLE (Nat.le_add_right n gs.length)

def readEdge {n : Nat} (gs : List Gate) (a b : Fin (n + gs.length)) : Prop :=
  ∃ (p : Nat) (g : Gate), gs[p]? = some g ∧ b.val = n + p ∧ a.val ∈ g.inputs

theorem read_order {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    {a b : Fin (n + gs.length)} (edge : readEdge gs a b) : a.val < b.val := by
  obtain ⟨p, g, hpg, hb, ha⟩ := edge
  rw [hb]
  exact (hcl p g hpg).lt _ ha

private theorem gate_difference {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (x y : Fin n → Bool) (b : Fin (n + gs.length)) (notInput : ¬ b.val < n)
    (diff : vl gs x b.val ≠ vl gs y b.val) :
    ∃ a : Fin (n + gs.length), readEdge gs a b ∧ vl gs x a.val ≠ vl gs y a.val := by
  let p := b.val - n
  have hb : b.val = n + p := by dsimp [p]; omega
  have hp : p < gs.length := by have := b.isLt; omega
  let g := gs[p]
  have hpg : gs[p]? = some g := List.getElem?_eq_getElem hp
  have differingRead : ∃ a ∈ g.inputs, vl gs x a ≠ vl gs y a := by
    classical
    by_contra none
    apply diff
    rw [hb]
    exact vl_congr gs hcl x y p g hpg (fun a ha => by
      by_contra da
      exact none ⟨a, ha, da⟩)
  obtain ⟨a, ha, da⟩ := differingRead
  have ha' := (hcl p g hpg).lt a ha
  refine ⟨⟨a, by have := b.isLt; omega⟩, ⟨p, g, hpg, hb, ha⟩, da⟩

theorem circuit_cut_agreement {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (cut out : Fin (n + gs.length)) (x y : Fin n → Bool)
    (sameCut : vl gs x cut.val = vl gs y cut.val)
    (blocked : ∀ i : Fin n, x i ≠ y i →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs i) out) :
    vl gs x out.val = vl gs y out.val := by
  apply cut_agreement Fin.val (fun v => v.val < n) (readEdge gs) cut out
    (fun v => vl gs x v.val) (fun v => vl gs y v.val)
  · exact fun _ _ e => read_order hcl e
  · exact gate_difference hcl x y
  · exact sameCut
  · intro a ha diff
    let i : Fin n := ⟨a.val, ha⟩
    have sameWire : inputWire gs i = a := Fin.ext rfl
    have di : x i ≠ y i := by
      rw [vl_input gs x a.val ha, vl_input gs y a.val ha] at diff
      exact diff
    rw [← sameWire]
    exact blocked i di

theorem circuit_cut_factors {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (cut out : Fin (n + gs.length)) (group : Fin n → Prop) (base : Fin n → Bool)
    (blocked : ∀ i : Fin n, group i →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs i) out) :
    ∃ outer : Bool → Bool, ∀ x : Fin n → Bool, (∀ i, ¬ group i → x i = base i) →
      outer (vl gs x cut.val) = vl gs x out.val := by
  let Fiber := {x : Fin n → Bool // ∀ i, ¬ group i → x i = base i}
  obtain ⟨outer, ho⟩ := unary_factor
    (fun x : Fiber => vl gs x.val cut.val) (fun x : Fiber => vl gs x.val out.val) (by
      intro x y sameCut
      apply circuit_cut_agreement hcl cut out x.val y.val sameCut
      intro i diff
      apply blocked i
      by_contra notGroup
      exact diff ((x.property i notGroup).trans (y.property i notGroup).symm))
  exact ⟨outer, fun x agrees => ho ⟨x, agrees⟩⟩

end PetersenCutTrace

namespace CircuitProof.Readers

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity CircuitProof

def Reads (gs : List Gate) (p w : ℕ) : Prop := ∃ g, gs[p]? = some g ∧ w ∈ g.inputs

end CircuitProof.Readers

namespace PetersenCutTrace

open PEqualNP.CircuitLowerBounds
open CircuitProof CircuitProof.Readers

def predecessors {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (b : Fin (n + gs.length)) : List (Fin (n + gs.length)) :=
  if gate : n ≤ b.val then
    let slot := b.val - n
    have hs : slot < gs.length := by have := b.isLt; omega
    let g := gs[slot]'hs
    g.inputs.attach.map fun a => ⟨a.val, by
      have atSlot : gs[slot]? = some g := List.getElem?_eq_getElem hs
      have before := (clean slot g atSlot).lt a.val a.property
      omega⟩
  else []

theorem predecessors_values {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (b : Fin (n + gs.length)) (internal : n ≤ b.val) :
    (predecessors clean b).map Fin.val =
      (gs[b.val - n]'(by have := b.isLt; omega)).inputs := by
  simp [predecessors, internal, List.map_map, Function.comp_def]

theorem predecessors_nil_input {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (b : Fin (n + gs.length)) (primary : b.val < n) : predecessors clean b = [] := by
  simp [predecessors, show ¬ n ≤ b.val by omega]

theorem predecessors_val_gate {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (b : Fin (n + gs.length)) {p : Nat} {g : Gate} (atSlot : gs[p]? = some g) (bWire : b.val = n + p) :
    (predecessors clean b).map Fin.val = g.inputs := by
  have isGate : n ≤ b.val := by omega
  have which : b.val - n = p := by omega
  have located := (List.getElem?_eq_some_iff.mp atSlot).2
  simpa [which, located] using predecessors_values clean b isGate

theorem predecessors_mem {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (a b : Fin (n + gs.length)) : a ∈ predecessors clean b ↔ readEdge gs a b := by
  by_cases internal : n ≤ b.val
  · let slot := b.val - n
    have hs : slot < gs.length := by have := b.isLt; dsimp [slot]; omega
    let g := gs[slot]'hs
    have wire : b.val = n + slot := by dsimp [slot]; omega
    have atSlot : gs[slot]? = some g := List.getElem?_eq_getElem hs
    have valList : (predecessors clean b).map Fin.val = g.inputs :=
      predecessors_values clean b internal
    constructor
    · intro mem
      refine ⟨slot, g, atSlot, wire, ?_⟩
      rw [← valList]
      exact List.mem_map.mpr ⟨a, mem, rfl⟩
    · rintro ⟨q, h, atQ, wireQ, inside⟩
      have same : q = slot := by omega
      subst q
      have gateSame : h = g := Option.some.inj (atQ.symm.trans atSlot)
      subst h
      rw [← valList] at inside
      obtain ⟨a', mem, equal⟩ := List.mem_map.mp inside
      exact (Fin.ext equal : a' = a) ▸ mem
  · have empty : predecessors clean b = [] := by simp [predecessors, internal]
    rw [empty]
    constructor
    · simp
    · rintro ⟨slot, g, _, wire, _⟩
      omega

end PetersenCutTrace

namespace PetersenScratch

open PEqualNP.MetaComplexity

def occurrences {n : ℕ} (i : Fin n) : DMFormula n → ℕ
  | .lit k _ => if k = i then 1 else 0
  | .and p q => occurrences i p + occurrences i q
  | .or p q => occurrences i p + occurrences i q

def hasPair {n : ℕ} (i j : Fin n) (p : DMFormula n) : Prop :=
  0 < occurrences i p ∨ 0 < occurrences j p

def pairInput {n : ℕ} (i j : Fin n) (base : Fin n → Bool) (a b : Bool) (k : Fin n) : Bool :=
  if k = i then a else if k = j then b else base k

def pairValue {n : ℕ} (i j : Fin n) (base : Fin n → Bool) (p : DMFormula n) :
    Bool → Bool → Bool :=
  fun a b => p.eval (pairInput i j base a b)

def binOp (conj : Bool) (a b : Bool) : Bool :=
  if conj then a && b else a || b

noncomputable def combine {n : ℕ} (conj : Bool) (i j : Fin n) (p q : DMFormula n)
    (P Q : Bool → Bool → Bool) : Bool → Bool → Bool := by
  classical
  exact if hasPair i j p then
    if hasPair i j q then fun a b => binOp conj (P a b) (Q a b) else P
    else Q

noncomputable def pairKernel {n : ℕ} (i j : Fin n) : DMFormula n → Bool → Bool → Bool
  | .lit k sign => fun a b =>
    let bit := if k = i then a else if k = j then b else false
    if sign then bit else !bit
  | .and p q => combine true i j p q (pairKernel i j p) (pairKernel i j q)
  | .or p q => combine false i j p q (pairKernel i j p) (pairKernel i j q)

private theorem eval_agree {n : ℕ} (p : DMFormula n) {x y : Fin n → Bool}
    (h : ∀ k, 0 < occurrences k p → x k = y k) : p.eval x = p.eval y := by
  induction p with
  | lit k s =>
    have e := h k (by simp [occurrences])
    simp [DMFormula.eval, e]
  | and p q ihp ihq =>
    simp only [DMFormula.eval]
    rw [ihp (fun k hk => h k (by simp only [occurrences]; omega)),
      ihq (fun k hk => h k (by simp only [occurrences]; omega))]
  | or p q ihp ihq =>
    simp only [DMFormula.eval]
    rw [ihp (fun k hk => h k (by simp only [occurrences]; omega)),
      ihq (fun k hk => h k (by simp only [occurrences]; omega))]

private theorem absent_left {n : ℕ} {i j : Fin n} {base : Fin n → Bool} {p : DMFormula n}
    (h : occurrences i p = 0) (a a' b : Bool) :
    pairValue i j base p a b = pairValue i j base p a' b := by
  apply eval_agree
  intro k hk
  have ne : k ≠ i := by rintro rfl; omega
  simp [pairInput, ne]

private theorem absent_right {n : ℕ} {i j : Fin n} {base : Fin n → Bool} {p : DMFormula n}
    (h : occurrences j p = 0) (a b b' : Bool) :
    pairValue i j base p a b = pairValue i j base p a b' := by
  apply eval_agree
  intro k hk
  have ne : k ≠ j := by rintro rfl; omega
  simp [pairInput, ne]

def changes (f : Bool → Bool → Bool) : Prop :=
  ∃ b, f false b ≠ f true b

private theorem changes_left {op : Bool → Bool → Bool} {P Q : Bool → Bool → Bool}
    (h : changes fun a b => op (P a b) (Q a b))
    (hQ : ∀ b, Q false b = Q true b) : changes P := by
  obtain ⟨b, hb⟩ := h
  exact ⟨b, fun hp => hb (by
    change op (P false b) (Q false b) = op (P true b) (Q true b)
    rw [hp, hQ])⟩

private theorem changes_right {op : Bool → Bool → Bool} {P Q : Bool → Bool → Bool}
    (h : changes fun a b => op (P a b) (Q a b))
    (hP : ∀ b, P false b = P true b) : changes Q := by
  obtain ⟨b, hb⟩ := h
  exact ⟨b, fun hq => hb (by
    change op (P false b) (Q false b) = op (P true b) (Q true b)
    rw [hq, hP])⟩

private theorem constant_pair {n : ℕ} {i j : Fin n} {base : Fin n → Bool} {p : DMFormula n}
    (h : ¬ hasPair i j p) (a b : Bool) :
    pairValue i j base p a b = pairValue i j base p false false := by
  have hi : occurrences i p = 0 := by
    by_contra e
    exact h (Or.inl (by omega))
  have hj : occurrences j p = 0 := by
    by_contra e
    exact h (Or.inr (by omega))
  exact (absent_left hi a false b).trans (absent_right hj false b false)

private theorem neutral_right (conj c : Bool) (P : Bool → Bool → Bool)
    (h : ∃ a b a' b', binOp conj (P a b) c ≠ binOp conj (P a' b') c) :
    ∀ a b, binOp conj (P a b) c = P a b := by
  cases conj <;> cases c <;> simp [binOp] at h ⊢

private theorem bin_comm (conj a b : Bool) : binOp conj a b = binOp conj b a := by
  cases conj <;> cases a <;> cases b <;> rfl

private theorem combine_stable {n : ℕ} (i j : Fin n) (base : Fin n → Bool)
    (conj : Bool) (p q : DMFormula n)
    (hi : occurrences i p + occurrences i q ≤ 1)
    (hj : occurrences j p + occurrences j q ≤ 1)
    (present : hasPair i j p ∨ hasPair i j q)
    (dep_i : 0 < occurrences i p + occurrences i q →
      changes fun a b => binOp conj (pairValue i j base p a b) (pairValue i j base q a b))
    (dep_j : 0 < occurrences j p + occurrences j q →
      changes fun b a => binOp conj (pairValue i j base p a b) (pairValue i j base q a b))
    (ihp : occurrences i p ≤ 1 → occurrences j p ≤ 1 → hasPair i j p →
      (0 < occurrences i p → changes (pairValue i j base p)) →
      (0 < occurrences j p → changes fun b a => pairValue i j base p a b) →
      ∀ a b, pairValue i j base p a b = pairKernel i j p a b)
    (ihq : occurrences i q ≤ 1 → occurrences j q ≤ 1 → hasPair i j q →
      (0 < occurrences i q → changes (pairValue i j base q)) →
      (0 < occurrences j q → changes fun b a => pairValue i j base q a b) →
      ∀ a b, pairValue i j base q a b = pairKernel i j q a b)
    (a b : Bool) :
    binOp conj (pairValue i j base p a b) (pairValue i j base q a b) =
      combine conj i j p q (pairKernel i j p) (pairKernel i j q) a b := by
  classical
  have pl : hasPair i j p → ∀ a b, pairValue i j base p a b = pairKernel i j p a b := by
    intro hp
    apply ihp (by omega) (by omega) hp
    · intro h
      exact changes_left (dep_i (by omega)) (fun b => absent_left (by omega) false true b)
    · intro h
      exact changes_left (dep_j (by omega)) (fun a => absent_right (by omega) a false true)
  have ql : hasPair i j q → ∀ a b, pairValue i j base q a b = pairKernel i j q a b := by
    intro hq
    apply ihq (by omega) (by omega) hq
    · intro h
      exact changes_right (dep_i (by omega)) (fun b => absent_left (by omega) false true b)
    · intro h
      exact changes_right (dep_j (by omega)) (fun a => absent_right (by omega) a false true)
  have nonconst : ∃ a b a' b',
      binOp conj (pairValue i j base p a b) (pairValue i j base q a b) ≠
        binOp conj (pairValue i j base p a' b') (pairValue i j base q a' b') := by
    unfold hasPair at present
    rcases present with (h | h) | (h | h)
    · obtain ⟨b, h⟩ := dep_i (by omega)
      exact ⟨false, b, true, b, h⟩
    · obtain ⟨a, h⟩ := dep_j (by omega)
      exact ⟨a, false, a, true, h⟩
    · obtain ⟨b, h⟩ := dep_i (by omega)
      exact ⟨false, b, true, b, h⟩
    · obtain ⟨a, h⟩ := dep_j (by omega)
      exact ⟨a, false, a, true, h⟩
  by_cases hp : hasPair i j p
  · by_cases hq : hasPair i j q
    · simp [combine, hp, hq, pl hp, ql hq]
    · rw [constant_pair hq a b]
      have hn := nonconst
      simp_rw [constant_pair hq] at hn
      rw [neutral_right conj _ _ hn a b, pl hp]
      simp [combine, hp, hq]
  · have hq := present.resolve_left hp
    rw [constant_pair hp a b, bin_comm]
    have hn := nonconst
    simp_rw [constant_pair hp, bin_comm conj (pairValue i j base p false false)] at hn
    rw [neutral_right conj _ _ hn a b, ql hq]
    simp [combine, hp]

private theorem stable_pair {n : ℕ} (i j : Fin n) (base : Fin n → Bool) (p : DMFormula n)
    (hi : occurrences i p ≤ 1) (hj : occurrences j p ≤ 1) (present : hasPair i j p)
    (dep_i : 0 < occurrences i p → changes (pairValue i j base p))
    (dep_j : 0 < occurrences j p → changes fun b a => pairValue i j base p a b) :
    ∀ a b, pairValue i j base p a b = pairKernel i j p a b := by
  induction p with
  | lit k s =>
    intro a b
    by_cases hki : k = i
    · simp [pairValue, pairKernel, DMFormula.eval, pairInput, hki]
    · have hkj : k = j := by
        by_contra h
        simp [hasPair, occurrences, hki, h] at present
      simp [pairValue, pairKernel, DMFormula.eval, pairInput, hkj]
  | and p q ihp ihq =>
    have present' : hasPair i j p ∨ hasPair i j q := by
      unfold hasPair at *
      simp only [occurrences] at present
      omega
    exact combine_stable i j base true p q hi hj present' dep_i dep_j ihp ihq
  | or p q ihp ihq =>
    have present' : hasPair i j p ∨ hasPair i j q := by
      unfold hasPair at *
      simp only [occurrences] at present
      omega
    exact combine_stable i j base false p q hi hj present' dep_i dep_j ihp ihq

theorem fixed_pair_invariant {n : ℕ} (i j : Fin n) (p : DMFormula n)
    (hi : occurrences i p ≤ 1) (hj : occurrences j p ≤ 1)
    (baseA baseO : Fin n → Bool) (outerA outerO : Bool → Bool)
    (hA : ∀ a b, outerA (pairValue i j baseA p a b) = (a && b))
    (hO : ∀ a b, outerO (pairValue i j baseO p a b) = (a || b)) : False := by
  have depAi : changes (pairValue i j baseA p) := by
    refine ⟨true, fun h => ?_⟩
    have e := congrArg outerA h
    rw [hA, hA] at e
    cases e
  have depAj : changes fun b a => pairValue i j baseA p a b := by
    refine ⟨true, fun h => ?_⟩
    have e := congrArg outerA h
    rw [hA, hA] at e
    cases e
  have depOi : changes (pairValue i j baseO p) := by
    refine ⟨false, fun h => ?_⟩
    have e := congrArg outerO h
    rw [hO, hO] at e
    cases e
  have depOj : changes fun b a => pairValue i j baseO p a b := by
    refine ⟨false, fun h => ?_⟩
    have e := congrArg outerO h
    rw [hO, hO] at e
    cases e
  have present : hasPair i j p := by
    left
    by_contra! h
    obtain ⟨b, hb⟩ := depAi
    exact hb (absent_left (by omega) false true b)
  have stableA := stable_pair i j baseA p hi hj present (fun _ => depAi) (fun _ => depAj)
  have stableO := stable_pair i j baseO p hi hj present (fun _ => depOi) (fun _ => depOj)
  simp_rw [stableA] at hA
  simp_rw [stableO] at hO
  have ne : pairKernel i j p false false ≠ pairKernel i j p false true := by
    intro e
    have f := congrArg outerO e
    rw [hO, hO] at f
    cases f
  have zeros := hA false false
  have other := hA false true
  have one := hA true true
  cases hk : pairKernel i j p false false <;>
    cases hl : pairKernel i j p false true <;>
    cases hm : pairKernel i j p true true <;>
    simp_all

end PetersenScratch

namespace PetersenCutFormula

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open CircuitProof
open PetersenScratch

def negFormula {n : Nat} : DMFormula n → DMFormula n
  | .lit i sign => .lit i (!sign)
  | .and a b => .or (negFormula a) (negFormula b)
  | .or a b => .and (negFormula a) (negFormula b)

theorem negFormula_eval {n : Nat} (p : DMFormula n) (x : Fin n → Bool) :
    (negFormula p).eval x = !(p.eval x) := by
  induction p with
  | lit i s =>
    cases s <;> cases e : x i <;> simp [negFormula, DMFormula.eval, e]
  | and a b iha ihb =>
    simp only [negFormula, DMFormula.eval, iha, ihb]
    cases a.eval x <;> cases b.eval x <;> rfl
  | or a b iha ihb =>
    simp only [negFormula, DMFormula.eval, iha, ihb]
    cases a.eval x <;> cases b.eval x <;> rfl

theorem negFormula_occurrences {n : Nat} (i : Fin n) (p : DMFormula n) :
    occurrences i (negFormula p) = occurrences i p := by
  induction p with
  | lit i s => rfl
  | and a b iha ihb => simp [negFormula, occurrences, iha, ihb]
  | or a b iha ihb => simp [negFormula, occurrences, iha, ihb]

def wireFormula {n : Nat} (fallback : Fin n) (gs : List Gate) (w : Nat) : DMFormula n :=
  if hw : w < n then
    .lit ⟨w, hw⟩ true
  else
    match gs[w - n]? with
    | none => .lit fallback true
    | some g =>
      match g.op, g.inputs with
      | .not, [a] =>
        if _ha : a < w then negFormula (wireFormula fallback gs a) else .lit fallback true
      | .and, [a, b] =>
        if _ha : a < w then
          if _hb : b < w then .and (wireFormula fallback gs a) (wireFormula fallback gs b)
          else .lit fallback true
        else .lit fallback true
      | .or, [a, b] =>
        if _ha : a < w then
          if _hb : b < w then .or (wireFormula fallback gs a) (wireFormula fallback gs b)
          else .lit fallback true
        else .lit fallback true
      | _, _ => .lit fallback true
termination_by w
decreasing_by all_goals assumption

theorem wireFormula_input {n : Nat} (fallback : Fin n) (gs : List Gate) (i : Fin n) :
    wireFormula fallback gs i.val = .lit i true := by
  rw [wireFormula]
  simp [i.isLt]

private theorem wireFormula_not {n : Nat} (fallback : Fin n) {gs : List Gate}
    {p a : Nat} {g : Gate} (hg : gs[p]? = some g) (op : g.op = .not)
    (inputs : g.inputs = [a]) (ha : a < n + p) :
    wireFormula fallback gs (n + p) = negFormula (wireFormula fallback gs a) := by
  have hn : ¬ n + p < n := by omega
  have hp : n + p - n = p := by omega
  conv_lhs => rw [wireFormula]
  simp [hn, hp, hg, op, inputs, ha]

private theorem wireFormula_and {n : Nat} (fallback : Fin n) {gs : List Gate}
    {p a b : Nat} {g : Gate} (hg : gs[p]? = some g) (op : g.op = .and)
    (inputs : g.inputs = [a, b]) (ha : a < n + p) (hb : b < n + p) :
    wireFormula fallback gs (n + p) = .and (wireFormula fallback gs a) (wireFormula fallback gs b) := by
  have hn : ¬ n + p < n := by omega
  have hp : n + p - n = p := by omega
  conv_lhs => rw [wireFormula]
  simp [hn, hp, hg, op, inputs, ha, hb]

private theorem wireFormula_or {n : Nat} (fallback : Fin n) {gs : List Gate}
    {p a b : Nat} {g : Gate} (hg : gs[p]? = some g) (op : g.op = .or)
    (inputs : g.inputs = [a, b]) (ha : a < n + p) (hb : b < n + p) :
    wireFormula fallback gs (n + p) = .or (wireFormula fallback gs a) (wireFormula fallback gs b) := by
  have hn : ¬ n + p < n := by omega
  have hp : n + p - n = p := by omega
  conv_lhs => rw [wireFormula]
  simp [hn, hp, hg, op, inputs, ha, hb]

theorem wireFormula_eval {n : Nat} (fallback : Fin n) {gs : List Gate} (hcl : CleanL n gs)
    (x : Fin n → Bool) (w : Nat) (hw : w < n + gs.length) :
    (wireFormula fallback gs w).eval x = vl gs x w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hi : w < n
    · rw [wireFormula_input fallback gs ⟨w, hi⟩, vl_input gs x w hi]
      rfl
    · obtain ⟨p, rfl⟩ : ∃ p, w = n + p := ⟨w - n, by omega⟩
      have hp : p < gs.length := by omega
      let g := gs[p]
      have hg : gs[p]? = some g := List.getElem?_eq_getElem hp
      rcases hcl p g hg with ⟨op, a, ha, inputs⟩ | ⟨op | op, a, b, ha, hb, inputs⟩
      · rw [wireFormula_not fallback hg op inputs ha, negFormula_eval, ih a ha (by omega),
          vl_gate gs hcl x p g hg]
        simp [op, inputs, GateOp.eval]
      · rw [wireFormula_and fallback hg op inputs ha hb]
        simp only [DMFormula.eval]
        rw [ih a ha (by omega), ih b hb (by omega), vl_gate gs hcl x p g hg]
        simp [op, inputs, GateOp.eval]
      · rw [wireFormula_or fallback hg op inputs ha hb]
        simp only [DMFormula.eval]
        rw [ih a ha (by omega), ih b hb (by omega), vl_gate gs hcl x p g hg]
        simp [op, inputs, GateOp.eval]

theorem wireFormula_count_input {n : Nat} (fallback : Fin n) (gs : List Gate) (chosen i : Fin n) :
    occurrences chosen (wireFormula fallback gs i.val) = if i = chosen then 1 else 0 := by
  rw [wireFormula_input]
  rfl

theorem wireFormula_count_gate {n : Nat} (fallback : Fin n) {gs : List Gate} (hcl : CleanL n gs)
    (chosen : Fin n) {p : Nat} {g : Gate} (hg : gs[p]? = some g) :
    occurrences chosen (wireFormula fallback gs (n + p)) =
      (g.inputs.map fun a => occurrences chosen (wireFormula fallback gs a)).sum := by
  rcases hcl p g hg with ⟨op, a, ha, inputs⟩ | ⟨op | op, a, b, ha, hb, inputs⟩
  · simp [wireFormula_not fallback hg op inputs ha, inputs, negFormula_occurrences]
  · simp [wireFormula_and fallback hg op inputs ha hb, inputs, occurrences]
  · simp [wireFormula_or fallback hg op inputs ha hb, inputs, occurrences]

theorem wireFormula_count_gate_fin {n : Nat} (fallback chosen : Fin n) {gs : List Gate}
    (hcl : CleanL n gs) {p : Nat} {g : Gate} (hg : gs[p]? = some g)
    {b : Fin (n + gs.length)} (hb : b.val = n + p)
    (parents : List (Fin (n + gs.length))) (parentsVal : parents.map Fin.val = g.inputs) :
    occurrences chosen (wireFormula fallback gs b.val) =
      (parents.map fun a => occurrences chosen (wireFormula fallback gs a.val)).sum := by
  rw [hb, wireFormula_count_gate fallback hcl chosen hg, ← parentsVal, List.map_map]
  rfl

end PetersenCutFormula

namespace PetersenCutIndependent

open PEqualNP.CircuitLowerBounds
open CircuitProof
open PetersenCutFormula PetersenCutTrace PetersenScratch

theorem wireFormula_count_input_fin {n : Nat} {gs : List Gate} (fallback chosen : Fin n)
    (a : Fin (n + gs.length)) (ha : a.val < n) :
    occurrences chosen (wireFormula fallback gs a.val) =
      if a = inputWire gs chosen then 1 else 0 := by
  let i : Fin n := ⟨a.val, ha⟩
  have e : i = chosen ↔ a = inputWire gs chosen := by
    constructor
    · intro h
      exact Fin.ext (congrArg (fun k : Fin n => k.val) h)
    · intro h
      exact Fin.ext (congrArg (fun k : Fin (n + gs.length) => k.val) h)
  change occurrences chosen (wireFormula fallback gs i.val) = _
  simp only [wireFormula_count_input, e]

theorem cut_factors {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (cut out : Fin (n + gs.length)) (group : Fin n → Prop) (base : Fin n → Bool)
    (controlled : cut = out ∨ ∀ i : Fin n, group i →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs i) out) :
    ∃ outer : Bool → Bool, ∀ x : Fin n → Bool, (∀ i, ¬ group i → x i = base i) →
      outer (vl gs x cut.val) = vl gs x out.val := by
  rcases controlled with rfl | blocked
  · exact ⟨id, fun _ _ => rfl⟩
  · exact circuit_cut_factors hcl cut out group base blocked

end PetersenCutIndependent

namespace FirstBranchRoute

open Relation

variable {m : Nat} (reads : Fin m → Fin m → Prop) (output : Fin m)

def Branches (v : Fin m) : Prop := ∃ a b, reads v a ∧ reads v b ∧ a ≠ b

def Terminal (v : Fin m) : Prop := v = output ∨ Branches reads v

def Follow (v w : Fin m) : Prop := reads v w ∧ ¬ Terminal reads output v

lemma follow_unique {v a b : Fin m} (first : Follow reads output v a) (next : Follow reads output v b) :
    a = b := by
  by_contra separate
  exact first.2 (Or.inr ⟨a, b, first.1, next.1, separate⟩)

variable (forward : ∀ {v w : Fin m}, reads v w → v < w)
variable (live : ∀ v : Fin m, v ≠ output → ∃ w, reads v w)

include forward live in
theorem exists_boundary (v : Fin m) :
    ∃ root : Fin m, Terminal reads output root ∧ ReflTransGen (Follow reads output) v root := by
  let distance (w : Fin m) := m - w.val
  induction v using (measure distance).wf.induction with
  | h v ih =>
    by_cases terminal : Terminal reads output v
    · exact ⟨v, terminal, ReflTransGen.refl⟩
    obtain ⟨next, edge⟩ := live v (fun e => terminal (Or.inl e))
    have increase := forward edge
    have closer : distance next < distance v := by
      dsimp [distance]
      have bounds := next.isLt
      change v.val < next.val at increase
      omega
    obtain ⟨root, stopped, route⟩ := ih next closer
    exact ⟨root, stopped, route.head ⟨edge, terminal⟩⟩

include forward in
theorem boundary_unique {v a b : Fin m} (terminalA : Terminal reads output a)
    (terminalB : Terminal reads output b) (routeA : ReflTransGen (Follow reads output) v a)
    (routeB : ReflTransGen (Follow reads output) v b) : a = b := by
  let distance (w : Fin m) := m - w.val
  induction v using (measure distance).wf.induction generalizing a b with
  | h v ih =>
    rcases routeA.cases_head with h | ⟨next, edge, tailA⟩
    · subst a
      rcases routeB.cases_head with h | ⟨_, edgeB, _⟩
      · exact h
      · exact (edgeB.2 terminalA).elim
    · rcases routeB.cases_head with h | ⟨nextB, edgeB, tailB⟩
      · subst b
        exact (edge.2 terminalB).elim
      have equal := follow_unique reads output edge edgeB
      subst nextB
      have increase := forward edge.1
      have closer : distance next < distance v := by
        dsimp [distance]
        have bounds := next.isLt
        change v.val < next.val at increase
        omega
      exact ih next closer terminalA terminalB tailA tailB

noncomputable def first (v : Fin m) : Fin m :=
  Classical.choose (exists_boundary reads output forward live v)

theorem first_stops (v : Fin m) : Terminal reads output (first reads output forward live v) :=
  (Classical.choose_spec (exists_boundary reads output forward live v)).1

theorem first_path (v : Fin m) : ReflTransGen (Follow reads output) v (first reads output forward live v) :=
  (Classical.choose_spec (exists_boundary reads output forward live v)).2

theorem first_of_terminal {v : Fin m} (stopped : Terminal reads output v) :
    first reads output forward live v = v :=
  boundary_unique reads output forward (first_stops reads output forward live v) stopped
    (first_path reads output forward live v) ReflTransGen.refl

theorem first_of_follows {v w : Fin m} (step : Follow reads output v w) :
    first reads output forward live v = first reads output forward live w :=
  boundary_unique reads output forward (first_stops reads output forward live v)
    (first_stops reads output forward live w) (first_path reads output forward live v)
    ((first_path reads output forward live w).head step)

include forward in
theorem path_forward {v w : Fin m} (route : ReflTransGen reads v w) : v ≤ w := by
  induction route with
  | refl => exact le_rfl
  | tail _ edge ih => exact le_trans ih (le_of_lt (forward edge))

lemma follows_is_read_path {v w : Fin m} (route : ReflTransGen (Follow reads output) v w) :
    ReflTransGen reads v w := by
  induction route with
  | refl => exact ReflTransGen.refl
  | tail _ edge ih => exact ih.tail edge.1

theorem first_forward (v : Fin m) : v ≤ first reads output forward live v :=
  path_forward reads forward (follows_is_read_path reads output (first_path reads output forward live v))

theorem read_before {v w : Fin m} (route : ReflTransGen reads v w)
    (before : w ≤ first reads output forward live v) :
    ReflTransGen (Follow reads output) v w ∧ first reads output forward live w = first reads output forward live v := by
  induction route with
  | refl => exact ⟨ReflTransGen.refl, rfl⟩
  | tail _ edge ih =>
    have predecessorBefore := lt_of_lt_of_le (forward edge) before
    obtain ⟨tracked, label⟩ := ih (le_of_lt predecessorBefore)
    have step : Follow reads output _ _ := ⟨edge, fun stopped => by
      have self := first_of_terminal reads output forward live stopped
      rw [self] at label
      exact (ne_of_lt predecessorBefore) label⟩
    exact ⟨tracked.tail step, (first_of_follows reads output forward live step).symm.trans label⟩

theorem ancestor_first_le {v w : Fin m} (route : ReflTransGen reads v w)
    (stopped : Terminal reads output w) : first reads output forward live v ≤ w := by
  by_contra tooLate
  have earlier := lt_of_not_ge tooLate
  have same := (read_before reads output forward live route (le_of_lt earlier)).2
  rw [first_of_terminal reads output forward live stopped] at same
  exact (ne_of_lt earlier) same

theorem edge_before {v a b : Fin m} (route : ReflTransGen reads v a) (edge : reads a b)
    (bound : b ≤ first reads output forward live v) : Follow reads output a b := by
  have earlier := lt_of_lt_of_le (forward edge) bound
  have same := (read_before reads output forward live route (le_of_lt earlier)).2
  refine ⟨edge, fun stopped => ?_⟩
  rw [first_of_terminal reads output forward live stopped] at same
  exact (ne_of_lt earlier) same

def Avoid (cut v w : Fin m) : Prop := reads v w ∧ v ≠ cut

lemma avoiding_is_read_path (cut : Fin m) {v w : Fin m} (route : ReflTransGen (Avoid reads cut) v w) :
    ReflTransGen reads v w := by
  induction route with
  | refl => exact ReflTransGen.refl
  | tail _ edge ih => exact ih.tail edge.1

theorem avoiding_stays_before {v w : Fin m}
    (route : ReflTransGen (Avoid reads (first reads output forward live v)) v w) :
    w ≤ first reads output forward live v := by
  induction route with
  | refl => exact first_forward reads output forward live v
  | tail prior edge ih =>
    have label := (read_before reads output forward live (avoiding_is_read_path reads _ prior) ih).2
    have earlier := lt_of_le_of_ne ih edge.2
    have following : Follow reads output _ _ := ⟨edge.1, fun terminal => by
      rw [first_of_terminal reads output forward live terminal] at label
      exact (ne_of_lt earlier) label⟩
    have same := (first_of_follows reads output forward live following).symm.trans label
    rw [← same]
    exact first_forward reads output forward live _

theorem no_avoiding_after {v w : Fin m} (after : first reads output forward live v < w) :
    ¬ ReflTransGen (Avoid reads (first reads output forward live v)) v w :=
  fun route => (not_lt_of_ge (avoiding_stays_before reads output forward live route)) after

include forward in
theorem unique_follow_predecessor {source a b goal : Fin m}
    (routeA : ReflTransGen (Follow reads output) source a) (edgeA : Follow reads output a goal)
    (routeB : ReflTransGen (Follow reads output) source b) (edgeB : Follow reads output b goal) : a = b := by
  let distance (w : Fin m) := m - w.val
  induction source using (measure distance).wf.induction generalizing a b with
  | h source ih =>
    rcases routeA.cases_head with aHere | ⟨nextA, stepA, laterA⟩
    · subst a
      rcases routeB.cases_head with bHere | ⟨next, stepB, later⟩
      · exact bHere
      have equal : next = goal := follow_unique reads output stepB edgeA
      subst next
      have increasing := path_forward reads forward (follows_is_read_path reads output later)
      exact (not_lt_of_ge increasing (forward edgeB.1)).elim
    · rcases routeB.cases_head with bHere | ⟨nextB, stepB, laterB⟩
      · subst b
        have equal : nextA = goal := follow_unique reads output stepA edgeB
        subst nextA
        have increasing := path_forward reads forward (follows_is_read_path reads output laterA)
        exact (not_lt_of_ge increasing (forward edgeA.1)).elim
      have equal := follow_unique reads output stepA stepB
      subst nextB
      have increase := forward stepA.1
      have closer : distance nextA < distance source := by
        dsimp [distance]
        have bounds := nextA.isLt
        change source.val < nextA.val at increase
        omega
      exact ih nextA closer laterA edgeA laterB edgeB

theorem unique_predecessor_before {source a b goal : Fin m}
    (bound : goal ≤ first reads output forward live source)
    (routeA : ReflTransGen reads source a) (edgeA : reads a goal)
    (routeB : ReflTransGen reads source b) (edgeB : reads b goal) : a = b := by
  have aBound := le_trans (le_of_lt (forward edgeA)) bound
  have bBound := le_trans (le_of_lt (forward edgeB)) bound
  exact unique_follow_predecessor reads output forward
    (read_before reads output forward live routeA aBound).1
    (edge_before reads output forward live routeA edgeA bound)
    (read_before reads output forward live routeB bBound).1
    (edge_before reads output forward live routeB edgeB bound)

lemma witness_of_positive_sum {α : Type*} (weight : α → Nat) (xs : List α)
    (positive : 0 < (xs.map weight).sum) : ∃ a ∈ xs, 0 < weight a := by
  induction xs with
  | nil => simp at positive
  | cons a rest ih =>
    by_cases h : 0 < weight a
    · exact ⟨a, by simp, h⟩
    have hr : 0 < (rest.map weight).sum := by
      simp only [List.map_cons, List.sum_cons] at positive
      omega
    obtain ⟨b, hb, hbPos⟩ := ih hr
    exact ⟨b, by simp [hb], hbPos⟩

lemma sum_le_one_of_unique_positive {α : Type*} (weight : α → Nat) (xs : List α)
    (distinct : xs.Nodup) (small : ∀ a ∈ xs, weight a ≤ 1)
    (unique : ∀ a ∈ xs, ∀ b ∈ xs, 0 < weight a → 0 < weight b → a = b) :
    (xs.map weight).sum ≤ 1 := by
  induction xs with
  | nil => simp
  | cons a rest ih =>
    simp only [List.nodup_cons] at distinct
    simp only [List.map_cons, List.sum_cons]
    by_cases h : weight a = 0
    · rw [h, Nat.zero_add]
      exact ih distinct.2 (fun b hb => small b (by simp [hb]))
        (fun b hb c hc => unique b (by simp [hb]) c (by simp [hc]))
    have restZero : (rest.map weight).sum = 0 := by
      by_contra some
      obtain ⟨b, hb, hbPos⟩ := witness_of_positive_sum weight rest (by omega)
      have equal := unique a (by simp) b (by simp [hb]) (by omega) hbPos
      exact distinct.1 (by simpa [equal] using hb)
    rw [restZero, Nat.add_zero]
    exact small a (by simp)

section Count

variable (parents : Fin m → List (Fin m))
variable (reads_parent : ∀ a b : Fin m, reads a b ↔ a ∈ parents b)
variable (weight : Fin m → Nat) (source : Fin m)
variable (other_weight : ∀ v : Fin m, v ≠ source → weight v = ((parents v).map weight).sum)

include forward reads_parent other_weight in
theorem weight_positive_path {v : Fin m} (positive : 0 < weight v) : ReflTransGen reads source v := by
  revert positive
  induction v using (measure (fun w : Fin m => w.val)).wf.induction with
  | h v ih =>
    intro positive
    by_cases isSource : v = source
    · subst v
      exact ReflTransGen.refl
    rw [other_weight v isSource] at positive
    obtain ⟨a, member, hp⟩ := witness_of_positive_sum weight (parents v) positive
    have edge := (reads_parent a v).mpr member
    have earlier := forward edge
    exact (ih a earlier hp).tail edge

include reads_parent other_weight in
theorem weight_before_le_one (rootWeight : weight source = 1) (distinct : ∀ v, (parents v).Nodup)
    {v : Fin m} (bound : v ≤ first reads output forward live source) : weight v ≤ 1 := by
  revert bound
  induction v using (measure (fun w : Fin m => w.val)).wf.induction with
  | h v ih =>
    intro bound
    by_cases isSource : v = source
    · subst v
      exact le_of_eq rootWeight
    rw [other_weight v isSource]
    apply sum_le_one_of_unique_positive weight (parents v) (distinct v)
    · intro a member
      have earlier := forward ((reads_parent a v).mpr member)
      exact ih a earlier (le_trans (le_of_lt earlier) bound)
    · intro a ma b mb ha hb
      exact unique_predecessor_before reads output forward live bound
        (weight_positive_path reads forward parents reads_parent weight source other_weight ha)
        ((reads_parent a v).mpr ma)
        (weight_positive_path reads forward parents reads_parent weight source other_weight hb)
        ((reads_parent b v).mpr mb)

end Count

end FirstBranchRoute

namespace PetersenFirstGroup

open PEqualNP.CircuitLowerBounds
open CircuitProof
open PetersenCutFormula PetersenCutIndependent PetersenCutTrace PetersenScratch

noncomputable def firstInputBoundary {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (i : Fin n) : Fin (n + gs.length) :=
  FirstBranchRoute.first (readEdge gs) out (read_order clean) live (inputWire gs i)

noncomputable def firstInputGroup {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (cut : Fin (n + gs.length)) : Finset (Fin n) :=
  Finset.univ.filter fun i => firstInputBoundary clean out live i = cut

theorem mem_firstInputGroup {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (cut : Fin (n + gs.length)) (i : Fin n) :
    i ∈ firstInputGroup clean out live cut ↔ firstInputBoundary clean out live i = cut := by
  simp [firstInputGroup]

theorem wire_le_output {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (w : Fin (n + gs.length)) : w ≤ out := by
  let last : Fin (n + gs.length) := ⟨n + gs.length - 1, by have := out.isLt; omega⟩
  have top (v : Fin (n + gs.length)) : v ≤ last := by
    change v.val ≤ n + gs.length - 1
    have := v.isLt
    omega
  have lastOut : last = out := by
    by_contra notOutput
    obtain ⟨v, e⟩ := live last notOutput
    exact (not_lt_of_ge (top v)) (read_order clean e)
  exact lastOut ▸ top w

theorem firstInputBoundary_occurrences_le_one {n : Nat} {gs : List Gate}
    (clean : CleanL n gs) (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (distinct : ∀ w, (predecessors clean w).Nodup)
    (fallback chosen : Fin n) :
    occurrences chosen (wireFormula fallback gs (firstInputBoundary clean out live chosen).val)
      ≤ 1 := by
  let weight (a : Fin (n + gs.length)) := occurrences chosen (wireFormula fallback gs a.val)
  have sourcePrimary : (inputWire gs chosen).val < n := chosen.isLt
  have atSource : weight (inputWire gs chosen) = 1 := by
    dsimp [weight]
    rw [wireFormula_count_input_fin fallback chosen _ sourcePrimary, ite_eq_left rfl]
  have otherWeight : ∀ w : Fin (n + gs.length), w ≠ inputWire gs chosen →
      weight w = ((predecessors clean w).map weight).sum := by
    intro w other
    by_cases primary : w.val < n
    · simp [weight, wireFormula_count_input_fin fallback chosen w primary, other,
        predecessors_nil_input clean w primary]
    · let p := w.val - n
      have hp : p < gs.length := by have := w.isLt; dsimp [p]; omega
      have hw : w.val = n + p := by dsimp [p]; omega
      let g := gs[p]
      have atSlot : gs[p]? = some g := List.getElem?_eq_getElem hp
      exact wireFormula_count_gate_fin fallback chosen clean atSlot hw _
        (predecessors_val_gate clean w atSlot hw)
  exact FirstBranchRoute.weight_before_le_one (readEdge gs) out (read_order clean) live
    (predecessors clean) (fun a b => (predecessors_mem clean a b).symm) weight
    (inputWire gs chosen) otherWeight atSource distinct le_rfl

theorem firstInputGroup_controlled {n : Nat} {gs : List Gate}
    (clean : CleanL n gs) (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (cut : Fin (n + gs.length)) :
    cut = out ∨ ∀ k : Fin n, k ∈ firstInputGroup clean out live cut →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs k) out := by
  by_cases terminal : cut = out
  · exact Or.inl terminal
  right
  intro k member path
  have before : cut < out := lt_of_le_of_ne (wire_le_output clean out live cut) terminal
  have firstHere := (mem_firstInputGroup clean out live cut k).mp member
  have after : firstInputBoundary clean out live k < out := by rwa [firstHere]
  have blocked := FirstBranchRoute.no_avoiding_after (readEdge gs) out
    (read_order clean) live after
  apply blocked
  change Relation.ReflTransGen (FirstBranchRoute.Avoid (readEdge gs)
    (firstInputBoundary clean out live k)) (inputWire gs k) out
  rw [firstHere]
  exact Relation.ReflTransGen.mono (fun _ _ e => ⟨e.1, e.2.1⟩) _ _ path

end PetersenFirstGroup

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof CircuitProof.Readers
open scoped BigOperators

def operands (gs : List Gate) : List Nat := gs.flatMap Gate.inputs

def notGateCount (gs : List Gate) : Nat := (gs.filter fun g => isNotGate g.op).length

theorem operand_mem_of_read {gs : List Gate} {slot wire : Nat} (read : Reads gs slot wire) :
    wire ∈ operands gs := by
  obtain ⟨g, gAt, before⟩ := read
  exact List.mem_flatMap.mpr ⟨g, List.mem_iff_getElem?.mpr ⟨slot, gAt⟩, before⟩

theorem two_readers_operand_count {gs : List Gate} {wire p q : Nat}
    (neq : p ≠ q) (first : Reads gs p wire) (second : Reads gs q wire) :
    2 ≤ (operands gs).count wire := by
  induction gs generalizing p q with
  | nil =>
    rcases first with ⟨g, atGate, _⟩
    simp at atGate
  | cons a rest ih =>
    simp only [operands, List.flatMap_cons, List.count_append]
    cases p with
    | zero =>
      cases q with
      | zero => exact (neq rfl).elim
      | succ q =>
        have atA : wire ∈ a.inputs := by simpa [Reads] using first
        have later : Reads rest q wire := by simpa [Reads] using second
        have aPos : 0 < a.inputs.count wire := List.count_pos_iff.mpr atA
        have restPos : 0 < (operands rest).count wire := List.count_pos_iff.mpr (operand_mem_of_read later)
        simp only [operands] at restPos
        omega
    | succ p =>
      cases q with
      | zero =>
        have atA : wire ∈ a.inputs := by simpa [Reads] using second
        have later : Reads rest p wire := by simpa [Reads] using first
        have aPos : 0 < a.inputs.count wire := List.count_pos_iff.mpr atA
        have restPos : 0 < (operands rest).count wire := List.count_pos_iff.mpr (operand_mem_of_read later)
        simp only [operands] at restPos
        omega
      | succ q =>
        have early : Reads rest p wire := by simpa [Reads] using first
        have late : Reads rest q wire := by simpa [Reads] using second
        have different : p ≠ q := fun eq => neq (congrArg Nat.succ eq)
        have count := ih different early late
        simp only [operands] at count
        omega

theorem operands_count_length (gs : List Gate)
    (arity : ∀ g ∈ gs, g.inputs.length + (if isNotGate g.op then 1 else 0) = 2) :
    (operands gs).length + notGateCount gs = 2 * gs.length := by
  induction gs with
  | nil => simp [operands, notGateCount]
  | cons g gs ih =>
    have gArity := arity g (by simp)
    have rest := ih (fun q hq => arity q (List.mem_cons_of_mem _ hq))
    cases h : isNotGate g.op
    · simp [h] at gArity
      simp [operands, notGateCount, h] at rest ⊢
      omega
    · simp [h] at gArity
      simp [operands, notGateCount, h] at rest ⊢
      omega

theorem clean_gate_arity {n : Nat} {gs : List Gate} (h : CleanL n gs) :
    ∀ g ∈ gs, g.inputs.length + (if isNotGate g.op then 1 else 0) = 2 := by
  intro g gMem
  obtain ⟨p, atGate⟩ := List.mem_iff_getElem?.mp gMem
  rcases h p g atGate with ⟨op, a, _, args⟩ | ⟨ops, a, b, _, _, args⟩
  · simp [op, args, isNotGate]
  · rcases ops with op | op <;> simp [op, args, isNotGate]

theorem branch_card_add_wire_card_le_operands (gs : List Gate) (branches : Finset Nat)
    (twice : ∀ w ∈ branches, 2 ≤ (operands gs).count w) :
    branches.card + (operands gs).toFinset.card ≤ (operands gs).length := by
  classical
  let W := (operands gs).toFinset
  have subset : branches ⊆ W := by
    intro w wm
    have t := twice w wm
    exact List.mem_toFinset.mpr (List.count_pos_iff.mp (by omega))
  have aux : (∑ w ∈ W, if w ∈ branches then (1 : Nat) else 0) = branches.card := by
    have same : (∑ w ∈ W, if w ∈ branches then (1 : Nat) else 0) =
        ∑ w ∈ branches, if w ∈ branches then (1 : Nat) else 0 := by
      symm
      apply Finset.sum_subset subset
      intro w _ notBranch
      simp [notBranch]
    rw [same]
    simp
  have total : (∑ w ∈ W, (operands gs).count w) = (operands gs).length :=
    List.sum_toFinset_count_eq_length _
  have bound : (∑ w ∈ W, ((if w ∈ branches then (1 : Nat) else 0) + 1)) ≤
      ∑ w ∈ W, (operands gs).count w := by
    apply Finset.sum_le_sum
    intro w wIn
    by_cases b : w ∈ branches
    · simpa [b] using twice w b
    · have pos : 0 < (operands gs).count w := List.count_pos_iff.mpr (List.mem_toFinset.mp wIn)
      simpa [b] using pos
  rw [Finset.sum_add_distrib, aux, total] at bound
  simpa [W] using bound

theorem branching_budget {n out : Nat} {gs : List Gate} (clean : CleanL n gs)
    (outValid : out < n + gs.length)
    (everyNonoutputUsed : ∀ w < n + gs.length, w ≠ out → ∃ p, Reads gs p w)
    (branches : Finset Nat)
    (twoReaders : ∀ w ∈ branches, ∃ p q, p ≠ q ∧ Reads gs p w ∧ Reads gs q w) :
    branches.card + (n + gs.length - 1) + notGateCount gs ≤ 2 * gs.length := by
  let W := (operands gs).toFinset
  let required := (Finset.range (n + gs.length)).erase out
  have requiredUsed : required ⊆ W := by
    intro w inSet
    have spec := Finset.mem_erase.mp inSet
    obtain ⟨p, read⟩ := everyNonoutputUsed w (Finset.mem_range.mp spec.2) spec.1
    exact List.mem_toFinset.mpr (operand_mem_of_read read)
  have numRequired : required.card = n + gs.length - 1 := by
    change ((Finset.range (n + gs.length)).erase out).card = _
    rw [Finset.card_erase_of_mem (Finset.mem_range.mpr outValid), Finset.card_range]
  have twice : ∀ w ∈ branches, 2 ≤ (operands gs).count w := by
    intro w mem
    obtain ⟨p, q, different, pReads, qReads⟩ := twoReaders w mem
    exact two_readers_operand_count different pReads qReads
  have up := branch_card_add_wire_card_le_operands gs branches twice
  have used := Finset.card_le_card requiredUsed
  rw [numRequired] at used
  have total := operands_count_length gs (clean_gate_arity clean)
  change n + gs.length - 1 ≤ (operands gs).toFinset.card at used
  omega

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof CircuitProof.Readers
open PetersenCutTrace

theorem branch_slots_of_read_edges {n : Nat} {gs : List Gate} {w : Fin (n + gs.length)}
    (fork : FirstBranchRoute.Branches (readEdge gs) w) :
    ∃ p q, p ≠ q ∧ Reads gs p w.val ∧ Reads gs q w.val := by
  obtain ⟨first, next, pRead, qRead, separate⟩ := fork
  obtain ⟨p, g, atP, src, ap⟩ := pRead
  obtain ⟨q, h, atQ, dst, aq⟩ := qRead
  refine ⟨p, q, ?_, ⟨g, atP, ap⟩, ⟨h, atQ, aq⟩⟩
  intro same
  subst q
  exact separate (Fin.ext (src.trans dst.symm))

noncomputable def circuitBranchWires {n : Nat} (gs : List Gate) : Finset (Fin (n + gs.length)) := by
  classical
  exact (Finset.univ).filter fun w => FirstBranchRoute.Branches (readEdge gs) w

theorem in_circuit_branches {n : Nat} {gs : List Gate} {w : Fin (n + gs.length)} :
    w ∈ circuitBranchWires gs ↔ FirstBranchRoute.Branches (readEdge gs) w := by
  classical
  simp [circuitBranchWires]

namespace PetersenCutTrace

open PEqualNP.CircuitLowerBounds CircuitProof
open Relation

theorem agree_on_input_ancestors {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (x y : Fin n → Bool) (w : Fin (n + gs.length))
    (agrees : ∀ i, ReflTransGen (readEdge gs) (inputWire gs i) w → x i = y i) :
    vl gs x w.val = vl gs y w.val := by
  revert agrees
  induction w using (measure (fun a : Fin (n + gs.length) => a.val)).wf.induction with
  | h w earlier =>
    intro agree
    by_cases input : w.val < n
    · let i : Fin n := ⟨w.val, input⟩
      have name : inputWire gs i = w := Fin.ext rfl
      have atInput : ReflTransGen (readEdge gs) (inputWire gs i) w := by
        simpa only [name] using (ReflTransGen.refl : ReflTransGen (readEdge gs) w w)
      have a := agree i atInput
      simpa only [vl_input gs x w.val input, vl_input gs y w.val input] using a
    · let p := w.val - n
      have pLt : p < gs.length := by have := w.isLt; dsimp [p]; omega
      have gateWire : w.val = n + p := by dsimp [p]; omega
      let g := gs[p]'pLt
      have atGate : gs[p]? = some g := List.getElem?_eq_getElem pLt
      rw [gateWire]
      apply vl_congr gs clean x y p g atGate
      intro a inGate
      have readBefore := (clean p g atGate).lt a inGate
      let wire : Fin (n + gs.length) := ⟨a, by have := w.isLt; omega⟩
      have read : readEdge gs wire w := ⟨p, g, atGate, gateWire, inGate⟩
      apply earlier wire (show wire.val < w.val by change a < w.val; omega)
      intro i path
      exact agree i (path.tail read)

end PetersenCutTrace

open PEqualNP.CircuitLowerBounds
open CircuitProof
open PetersenCutTrace Relation

open PEqualNP.CircuitLowerBounds CircuitProof
open PetersenCutTrace

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof CircuitProof.Readers
open PetersenCutTrace PetersenFirstGroup

lemma nonNotCount_add_notCount (gs : List Gate) :
    nonNotCount gs + (gs.filter (fun g => isNotGate g.op)).length = gs.length := by
  rw [← List.countP_eq_length_filter]
  induction gs with
  | nil => simp [nonNotCount]
  | cons g gs ih =>
    simp only [nonNotCount, List.countP_cons, List.length_cons] at ih ⊢
    cases h : isNotGate g.op <;> simp [h] <;> omega

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof CircuitProof.Readers PetersenCutTrace PetersenFirstGroup
open PetersenCutFormula PetersenCutIndependent PetersenScratch
def Forbid {n : Nat} (F : (Fin n → Bool) → Bool) (i j : Fin n) : Prop :=
  ∀ a o, (∀ u v, F (pairInput i j a u v) = (u && v)) →
    (∀ u v, F (pairInput i j o u v) = (u || v)) → False
theorem forkBudget {n r : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (budget : nonNotCount gs + 1 ≤ n + r) : (circuitBranchWires (n := n) gs).card ≤ r := by
  classical
  let branches := circuitBranchWires (n := n) gs
  have h := branching_budget clean out.isLt (fun w hw hne => by
      let wire : Fin (n + gs.length) := ⟨w, hw⟩
      obtain ⟨v,p,g,hg,_,hw'⟩ := live wire (fun e => hne (congrArg Fin.val e))
      exact ⟨p,g,hg,hw'⟩)
    (branches.image Fin.val) (fun w hw => by
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
      exact branch_slots_of_read_edges (in_circuit_branches.mp hv))
  rw [Finset.card_image_of_injective _ Fin.val_injective] at h
  have count := nonNotCount_add_notCount gs
  change nonNotCount gs + notGateCount gs = gs.length at count
  change branches.card ≤ r
  omega

theorem rankCuts {n r : ℕ} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (hcard : (circuitBranchWires (n := n) gs).card ≤ r) :
    ∃ label : Fin n → Fin (r+1),
      (∀ i j, label i = label j ↔ firstInputBoundary clean out live i = firstInputBoundary clean out live j) ∧
      (∀ k : Fin (r+1), ∃ code : (Fin n → Bool) → Bool,
        (∀ x y, (∀ i, label i ≤ k → x i = y i) → code x = code y) ∧
        (∀ x y, (∀ i, label i ≠ k → x i = y i) → code x = code y → vl gs x out.val = vl gs y out.val)) := by
  classical
  let branches := circuitBranchWires (n := n) gs
  change branches.card ≤ r at hcard
  let cuts := insert out branches
  have small : cuts.card ≤ r+1 := (Finset.card_insert_le ..).trans (by omega)
  let boundary := firstInputBoundary clean out live
  have mem (i : Fin n) : boundary i ∈ cuts := by
    rcases FirstBranchRoute.first_stops (readEdge gs) out (read_order clean) live (inputWire gs i)
      with ho | hb
    · exact Finset.mem_insert.mpr (Or.inl ho)
    · exact Finset.mem_insert.mpr (Or.inr (in_circuit_branches.mpr hb))
  let embed := (cuts.orderIsoOfFin rfl).symm
  let rank (c : cuts) : Fin (r+1) :=
    ⟨r+1 - cuts.card + (embed c).val, by have := (embed c).isLt; omega⟩
  have strict : StrictMono rank := by
    intro c d hcd
    have he := embed.strictMono hcd
    change (embed c).val < (embed d).val at he
    change r+1 - cuts.card + (embed c).val < r+1 - cuts.card + (embed d).val
    omega
  let loc (i : Fin n) : cuts := ⟨boundary i, mem i⟩
  let label (i : Fin n) := rank (loc i)
  have eqv (i j : Fin n) : label i = label j ↔ boundary i = boundary j := by
    change rank (loc i) = rank (loc j) ↔ (loc i).val = (loc j).val
    rw [strict.injective.eq_iff, Subtype.ext_iff]
  refine ⟨label, eqv, ?_⟩
  intro k
  by_cases used : ∃ z, label z = k
  · obtain ⟨z, rfl⟩ := used
    let c := boundary z
    have term : FirstBranchRoute.Terminal (readEdge gs) out c :=
      FirstBranchRoute.first_stops (readEdge gs) out (read_order clean) live (inputWire gs z)
    refine ⟨fun x => vl gs x c.val, ?_, ?_⟩
    · intro x y hxy
      apply agree_on_input_ancestors clean
      intro i path
      apply hxy i
      exact strict.monotone (show loc i ≤ loc z from
        FirstBranchRoute.ancestor_first_le (readEdge gs) out (read_order clean) live path term)
    · intro x y hxy heq
      have blocked := firstInputGroup_controlled clean out live c
      rcases blocked with atOut | apart
      · simpa only [atOut] using heq
      · apply circuit_cut_agreement clean c out x y heq
        intro i hi
        apply apart i
        apply (mem_firstInputGroup clean out live c i).mpr
        exact (eqv i z).mp (by_contra fun ne => hi (hxy i ne))
  · refine ⟨fun _ => false, fun _ _ _ => rfl, ?_⟩
    intro x y hxy _
    have : x = y := funext (fun i => hxy i (fun h => used ⟨i,h⟩))
    rw [this]

theorem generalConflict {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (distinct : ∀ w, (predecessors clean w).Nodup)
    (e : Fin n × Fin n)
    (same : firstInputBoundary clean out live e.1 = firstInputBoundary clean out live e.2) :
    Forbid (fun x => vl gs x out.val) e.1 e.2 := by
  intro ctxA ctxO hand hor
  let cut := firstInputBoundary clean out live e.1
  have hi := firstInputBoundary_occurrences_le_one clean out live distinct e.1 e.1
  have hj := firstInputBoundary_occurrences_le_one clean out live distinct e.1 e.2
  rw [← same] at hj
  have controlled : cut = out ∨ ∀ k : Fin n, (k = e.1 ∨ k = e.2) →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs k) out := by
    rcases firstInputGroup_controlled clean out live cut with h | h
    · exact Or.inl h
    · apply Or.inr
      intro k hk
      apply h
      apply (mem_firstInputGroup clean out live cut k).mpr
      rcases hk with hk | hk
      · rw [hk]
      · rw [hk]
        exact same.symm
  have factor (base : Fin n → Bool) : ∃ outer : Bool → Bool, ∀ a b,
      outer (pairValue e.1 e.2 base (wireFormula e.1 gs cut.val) a b) =
        vl gs (pairInput e.1 e.2 base a b) out.val := by
    obtain ⟨outer, ho⟩ := cut_factors clean cut out (fun k => k = e.1 ∨ k = e.2) base controlled
    refine ⟨outer, fun a b => ?_⟩
    unfold pairValue
    rw [wireFormula_eval e.1 clean _ cut.val cut.isLt]
    apply ho
    intro k hk
    simp [pairInput, show k ≠ e.1 from fun h => hk (Or.inl h),
      show k ≠ e.2 from fun h => hk (Or.inr h)]
  obtain ⟨fa, ha⟩ := factor ctxA
  obtain ⟨fo, ho⟩ := factor ctxO
  apply fixed_pair_invariant e.1 e.2 (wireFormula e.1 gs cut.val) hi hj _ _ fa fo
  · intro a b; exact (ha a b).trans (hand a b)
  · intro a b; exact (ho a b).trans (hor a b)

structure Grouping {n : Nat} (r : Nat) (F : (Fin n → Bool) → Bool) where
  label : Fin n → Fin (r+1)
  pair : ∀ i j, label i = label j → Forbid F i j
  cut : ∀ k, ∃ code : (Fin n → Bool) → Bool,
    (∀ x y, (∀ i, label i ≤ k → x i = y i) → code x = code y) ∧
    (∀ x y, (∀ i, label i ≠ k → x i = y i) → code x = code y → F x = F y)

namespace RankRules

inductive Rule (n : Nat)
  | square (i j : Fin n) (a o : Nat)
  | cube (i j k : Fin n) (a b c : Nat) (bit sign : Bool)

def row {n : Nat} (m : Nat) : Fin n → Bool := fun i => m.testBit i.val

def accepts {n r : Nat} (label : Fin n → Fin r) : Rule n → Bool
  | .square i j _ _ => label i != label j
  | .cube i j k _ _ _ _ _ => (label i != label j) || decide (label k ≤ label i)

end RankRules
end PEqualNP.Outside.L_meta_3250.RankBase

namespace PEqualNP.Outside.L_meta_3250.FrontRanks

abbrev Word := BitVec 512

def fits (mono desired ground sample : Bool) : Bool :=
  if mono then if desired then !ground || sample else !sample || ground else ground == sample

def pinMask (mono desired sample : Bool) (w : Word) : Word :=
  if fits mono desired false sample then
    if fits mono desired true sample then BitVec.allOnes 512 else ~~~w
  else if fits mono desired true sample then w else 0

def mask (mono desired : Bool) : (ws : List Word) → (Fin ws.length → Bool) → Word
  | [], _ => BitVec.allOnes 512
  | w :: ws, x => pinMask mono desired (x 0) w &&& mask mono desired ws (fun i => x i.succ)

def forced (target : Word) (mono desired : Bool) (ws : List Word) (x : Fin ws.length → Bool) : Bool :=
  decide ((mask mono desired ws x &&& (if desired then target else ~~~target)) ≠ (0 : Word))

theorem mask_spec (mono b) (p : Fin 512) (ws : List Word) (x : Fin ws.length → Bool) :
    (mask mono b ws x).getLsbD p.val = true ↔
      ∀ i, fits mono b ((ws.get i).getLsbD p.val) (x i) = true := by
  induction ws with
  | nil =>
    change (BitVec.allOnes 512).getLsbD p.val = true ↔ _
    simp only [BitVec.getLsbD_allOnes, p.isLt, decide_true, true_iff]
    intro i
    exact Fin.elim0 i
  | cons w ws ih =>
    have pin : (pinMask mono b (x 0) w).getLsbD p.val =
        fits mono b (w.getLsbD p.val) (x 0) := by
      cases mono <;> cases b <;> cases q : x 0 <;>
        simp only [pinMask, fits, q, Bool.not_false, Bool.not_true, Bool.false_or,
          Bool.true_or, Bool.or_false, Bool.or_true, Bool.false_eq_true, Bool.true_eq_false,
          ite_false, ite_true, beq_false, beq_true, BitVec.getLsbD_allOnes, BitVec.getLsbD_not,
          BitVec.getLsbD_zero, p.isLt, decide_true, Bool.true_and]
    simp only [mask,BitVec.getLsbD_and,Bool.and_eq_true,ih,pin]
    constructor
    · intro ⟨h0,hs⟩ i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact h0
      · exact hs j
    · intro h
      exact ⟨h 0, fun i => h i.succ⟩

theorem forced_sound {ws : List Word} {target : Word} {mono : Bool}
    (F : (Fin ws.length → Bool) → Bool)
    (agree : ∀ p : Fin 512, F (fun i => (ws.get i).getLsbD p.val) = target.getLsbD p.val)
    (mon : mono = true → Monotone F) (b : Bool) (x) (h : forced target mono b ws x = true) :
    F x = b := by
  let bits := mask mono b ws x &&& (if b then target else ~~~target)
  have nzero : bits ≠ 0 := of_decide_eq_true h
  obtain ⟨p,hp⟩ : ∃ p : Fin 512, bits.getLsbD p.val = true := by
    by_contra! hbad
    apply nzero
    apply BitVec.eq_of_getElem_eq
    intro i hi
    have hh := hbad ⟨i,hi⟩
    simpa [BitVec.getLsbD_eq_getElem hi] using hh
  change (mask mono b ws x &&& (if b then target else ~~~target)).getLsbD p.val = true at hp
  simp only [BitVec.getLsbD_and, Bool.and_eq_true] at hp
  have fh := (mask_spec mono b p ws x).mp hp.1
  have ground : F (fun i => (ws.get i).getLsbD p.val) = b := by
    rw [agree]; cases b <;> simpa [p.isLt] using hp.2
  cases hm : mono with
  | false =>
    have eq : (fun i => (ws.get i).getLsbD p.val) = x := by
      funext i; simpa [fits,hm] using fh i
    rwa [eq] at ground
  | true =>
    cases b with
    | false =>
      have le : x ≤ fun i => (ws.get i).getLsbD p.val := by
        intro i
        have hi := fh i
        cases q : x i <;> cases v : (ws.get i).getLsbD p.val <;> simp_all [fits]
      have bound := mon hm le
      rw [ground] at bound
      cases e : F x <;> simp_all
      exact (by decide : ¬ true ≤ false) bound
    | true =>
      have le : (fun i => (ws.get i).getLsbD p.val) ≤ x := by
        intro i
        have hi := fh i
        cases q : x i <;> cases v : (ws.get i).getLsbD p.val <;> simp_all [fits]
      have bound := mon hm le
      rw [ground] at bound
      cases e : F x <;> simp_all
      exact (by decide : ¬ true ≤ false) bound
end PEqualNP.Outside.L_meta_3250.FrontRanks

namespace PEqualNP.Outside.L_meta_3250.FrontRanks
open RankBase RankBase.RankRules RankBase.PetersenScratch

def checksRule (target : Word) (mono : Bool) (ws : List Word) : Rule ws.length → Bool :=
  let checkValue := fun x b => forced target mono b ws x
  fun
  | .square i j a o =>
      [false,true].all fun u => [false,true].all fun v =>
        checkValue (pairInput i j (row a) u v) (u && v) &&
        checkValue (pairInput i j (row o) u v) (u || v)
  | .cube i j k a b c bit sign =>
      let hi m := Function.update (row m) k bit
      ((List.finRange ws.length).all fun v => v == i || v == j ||
        (row a v == row b v && row b v == row c v)) &&
      checkValue (row a) false &&
      checkValue (row b) true &&
      checkValue (hi a) sign &&
      checkValue (hi b) sign &&
      checkValue (hi c) (!sign)

theorem checksRule_sound {target : Word} {mono : Bool} {ws : List Word} {r : Nat}
    (F : (Fin ws.length → Bool) → Bool)
    (agree : ∀ p : Fin 512, F (fun i => (ws.get i).getLsbD p.val) = target.getLsbD p.val)
    (mon : mono = true → Monotone F) (group : Grouping r F) {rule : Rule ws.length}
    (h : checksRule target mono ws rule = true) : accepts group.label rule = true := by
  have evaluation {x b} (e : forced target mono b ws x = true) : F x = b :=
    forced_sound F agree mon b x e
  cases rule with
  | square i j a o =>
    apply bne_iff_ne.mpr
    intro eq
    have all (u v : Bool) := List.all_eq_true.mp
      (List.all_eq_true.mp h u (by cases u <;> decide)) v (by cases v <;> decide)
    exact group.pair i j eq (row a) (row o)
      (fun u v => by
        have both := all u v
        simp only [Bool.and_eq_true] at both
        exact evaluation both.1)
      (fun u v => by
        have both := all u v
        simp only [Bool.and_eq_true] at both
        exact evaluation both.2)
  | cube i j k a b c bit sign =>
    simp only [accepts, Bool.or_eq_true, bne_iff_ne, decide_eq_true_eq]
    by_cases eq : group.label i = group.label j
    · right
      by_contra nl
      have high := lt_of_not_ge nl
      simp only [checksRule, Bool.and_eq_true] at h
      obtain ⟨⟨⟨⟨⟨same,va⟩,vb⟩,vha⟩,vhb⟩,vhc⟩ := h
      obtain ⟨code,lower,upper⟩ := group.cut (group.label i)
      let upd (m : Nat) := Function.update (row m) k bit
      have noChange (m : Nat) : code (upd m) = code (row m) := by
        apply lower
        intro u hu
        apply Function.update_of_ne
        intro e
        subst u
        exact (not_le_of_gt high) hu
      have share {u} (hu : group.label u ≠ group.label i) :
          row a u = row b u ∧ row b u = row c u := by
        have s := List.all_eq_true.mp same u (List.mem_finRange u)
        have ei : u ≠ i := fun e => hu (e ▸ rfl)
        have ej : u ≠ j := fun e => hu (e ▸ eq.symm)
        simpa [ei,ej] using s
      have ab : code (row a) ≠ code (row b) := by
        intro e
        have bad := upper _ _ (fun _ hu => (share hu).1) e
        rw [evaluation va,evaluation vb] at bad
        contradiction
      have lift {p q : Nat} (off : ∀ u, group.label u ≠ group.label i → row p u = row q u) :
          ∀ u, group.label u ≠ group.label i → upd p u = upd q u := by
        intro u hu
        by_cases e : u = k
        · subst u; simp [upd]
        · simpa only [upd,Function.update_of_ne e] using off u hu
      have ac : code (row a) ≠ code (row c) := by
        intro e
        have bad := upper _ _ (lift fun _ hu => (share hu).1.trans (share hu).2)
          ((noChange a).trans (e.trans (noChange c).symm))
        change F (Function.update (row a) k bit) = F (Function.update (row c) k bit) at bad
        rw [evaluation vha,evaluation vhc] at bad
        cases sign <;> cases bad
      have bc : code (row b) ≠ code (row c) := by
        intro e
        have bad := upper _ _ (lift fun _ hu => (share hu).2)
          ((noChange b).trans (e.trans (noChange c).symm))
        change F (Function.update (row b) k bit) = F (Function.update (row c) k bit) at bad
        rw [evaluation vhb,evaluation vhc] at bad
        cases sign <;> cases bad
      cases ha : code (row a) <;> cases hb : code (row b) <;> cases hc : code (row c) <;> simp_all
    · exact Or.inl eq
def readFin (n x : Nat) : Option (Fin n) :=
  if h : x < n then some ⟨x,h⟩ else none

def ruleCode (n w : Nat) : Option (Rule n) := do
  let i ← readFin n (w &&& 15)
  let j ← readFin n ((w >>> 4) &&& 15)
  let k := (w >>> 8) &&& 15
  let pay := w >>> 12
  let raw := pay &&& 4095
  if k == 15 then
    return .square i j raw (pay >>> 12)
  else
    let pivot ← readFin n k
    let corner (m : Nat) := raw ||| ((m &&& 1) <<< i.val) ||| (((m >>> 1) &&& 1) <<< j.val)
    return .cube i j pivot (corner (pay >>> 12)) (corner (pay >>> 14))
      (corner (pay >>> 16)) (!(raw.testBit k)) (pay.testBit 18)

def readRules (n : Nat) : Nat → Nat → List (Rule n)
  | 0, _ => []
  | c+1, w =>
    (ruleCode n (w &&& 0xfffffffff)).toList ++ readRules n c (w >>> 36)

namespace ColorBits

def span (w : Nat) (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n+1 => span w f n ||| (f n <<< (n*w))

def Bounded (a w : Nat) := ∀ j, w ≤ j → a.testBit j = false

theorem span_out {w f} (hf : ∀ d, Bounded (f d) w) (n : Nat) : Bounded (span w f n) (n*w) := by
  induction n with
  | zero => simp [Bounded,span]
  | succ n ih =>
    intro j hj
    simp only [span,Nat.testBit_or,Nat.testBit_shiftLeft]
    rw [Nat.succ_mul] at hj
    rw [ih j (by omega),hf n _ (by omega)]
    simp

theorem span_at {w f} (hf : ∀ d, Bounded (f d) w) {d j} (hj : j < w) :
    ∀ n, d < n → (span w f n).testBit (d*w+j) = (f d).testBit j := by
  intro n
  induction n with
  | zero => omega
  | succ n ih =>
    intro hd
    simp only [span,Nat.testBit_or,Nat.testBit_shiftLeft]
    by_cases same : d = n
    · subst d
      rw [span_out hf n _ (by omega)]
      simp
    · have lt : d < n := by omega
      have lim := Nat.mul_le_mul_right w (show d+1 ≤ n by omega)
      rw [Nat.succ_mul] at lim
      rw [ih lt]
      simp [show ¬n*w ≤ d*w+j by omega]

def full (w : Nat) := (1 <<< w)-1
theorem full_bit (w j : Nat) : (full w).testBit j = decide (j < w) := by
  simp [full,Nat.shiftLeft_eq]

def plane (r bit : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | n+1, i =>
    let w := r^n
    if i == n then span w (fun d => if d.testBit bit then full w else 0) r
    else let v := plane r bit n i; span w (fun _ => v) r

theorem digit_out (w bit d : Nat) : Bounded (if d.testBit bit then full w else 0) w := by
  intro j hj
  split <;> simp [full_bit,show ¬j<w by omega]

theorem plane_out (r bit n i : Nat) : Bounded (plane r bit n i) (r^n) := by
  induction n with
  | zero => simp [Bounded,plane]
  | succ n ih =>
    rw [plane,Nat.pow_succ']
    split
    · exact span_out (digit_out _ _) r
    · exact span_out (fun _ => ih) r

def index (r : Nat) (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n+1 => f n * r^n + index r f n

theorem index_lt {r f n} (hf : ∀ i < n, f i < r) : index r f n < r^n := by
  induction n with
  | zero => simp [index]
  | succ n ih =>
    have sm := ih (fun i hi => hf i (by omega))
    have lim := Nat.mul_le_mul_right (r^n) (show f n + 1 ≤ r from hf n (by omega))
    rw [Nat.succ_mul] at lim
    rw [index,Nat.pow_succ']
    omega

theorem plane_at {r f n i} (bit : Nat) (hf : ∀ j < n, f j < r) (hi : i < n) :
    (plane r bit n i).testBit (index r f n) = (f i).testBit bit := by
  induction n with
  | zero => omega
  | succ n ih =>
    have prior (j) (hj : j < n) := hf j (by omega)
    have ix := index_lt prior
    have ln := hf n (by omega)
    rw [plane,index]
    by_cases eq : i = n
    · subst i
      simp only [beq_self_eq_true,ite_true]
      rw [span_at (digit_out _ _) ix _ ln]
      cases z : (f n).testBit bit <;> simp [full_bit,ix]
    · simp only [beq_iff_eq,eq,ite_false]
      rw [span_at (fun _ => plane_out r bit n i) ix _ ln]
      exact ih prior (by omega)

def allowed {n} (all : Nat) (cols : List (Nat × Nat × Nat)) : Rule n → Nat
  | .square i j .. =>
    let a := cols.getD i (0,0,0); let b := cols.getD j (0,0,0)
    (a.1 ^^^ b.1) ||| (a.2.1 ^^^ b.2.1) ||| (a.2.2 ^^^ b.2.2)
  | .cube i j k .. =>
    let a := cols.getD i (0,0,0); let b := cols.getD j (0,0,0); let c := cols.getD k (0,0,0)
    let diff := (a.1 ^^^ b.1) ||| (a.2.1 ^^^ b.2.1) ||| (a.2.2 ^^^ b.2.2)
    let lo := (a.2.1 &&& (all ^^^ c.2.1)) ||| ((all ^^^ (a.2.1 ^^^ c.2.1)) &&& (a.1 ||| (all ^^^ c.1)))
    let le := (a.2.2 &&& (all ^^^ c.2.2)) ||| ((all ^^^ (a.2.2 ^^^ c.2.2)) &&& lo)
    diff ||| le

def fast {n} (r : Nat) (rs : List (Rule n)) : Bool :=
  if 1 ≤ r && r ≤ 5 && n ≤ 12 then
    let all := full (r^n)
    let cols := (List.range n).map (fun (i : Nat) => (plane r 0 n i,plane r 1 n i,plane r 2 n i))
    rs.foldl (fun a q => a &&& allowed all cols q) all != 0
  else true

theorem binary_diff : ∀ a b : Fin 5, ((a.val.testBit 0 ^^ b.val.testBit 0) ||
    (a.val.testBit 1 ^^ b.val.testBit 1) || (a.val.testBit 2 ^^ b.val.testBit 2)) = (a != b) := by decide +kernel

theorem binary_le : ∀ a c : Fin 5,
    ((a.val.testBit 2 && !c.val.testBit 2) || (!(a.val.testBit 2 ^^ c.val.testBit 2) &&
    ((a.val.testBit 1 && !c.val.testBit 1) ||
    (!(a.val.testBit 1 ^^ c.val.testBit 1) && (a.val.testBit 0 || !c.val.testBit 0))))) = decide (c ≤ a) := by decide +kernel

theorem fold_bit {α} (ok : α → Nat) (j : Nat) (rs : List α)
    (h : ∀ q ∈ rs, (ok q).testBit j = true) (a : Nat) (ha : a.testBit j = true) :
    (rs.foldl (fun z q => z &&& ok q) a).testBit j = true := by
  induction rs generalizing a with
  | nil => exact ha
  | cons q qs ih =>
    apply ih (fun u hu => h u (List.mem_cons_of_mem _ hu))
    simp [Nat.testBit_and,ha,h q List.mem_cons_self]

theorem sound {n r} {label : Fin n → Fin r} {rules : List (Rule n)}
    (good : ∀ q ∈ rules, accepts label q = true) : fast r rules = true := by
  unfold fast
  split
  next bound =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at bound
    let f (i : Nat) := if h : i < n then (label ⟨i,h⟩).val else 0
    have hf (i) (hi : i < n) : f i < r := by simp only [f,dite_eq_left hi]; exact (label _).isLt
    let ix := index r f n
    let all := full (r^n)
    let cols := (List.range n).map (fun (i : Nat) => (plane r 0 n i,plane r 1 n i,plane r 2 n i))
    have ha : all.testBit ix = true := by simp [all,full_bit,ix,index_lt hf]
    have lookup (i : Fin n) : cols.getD i (0,0,0) = (plane r 0 n i,plane r 1 n i,plane r 2 n i) := by
      simp [cols,List.getD_eq_getElem?_getD,i.isLt]
    have val (i : Fin n) (bit) : (plane r bit n i).testBit ix = (label i).val.testBit bit := by
      simp only [ix,plane_at bit hf i.isLt,f,dite_eq_left i.isLt]
    let v (i : Fin n) : Fin 5 := ⟨(label i).val,by have := (label i).isLt; omega⟩
    have hq (q : Rule n) (hq : q ∈ rules) : (allowed all cols q).testBit ix = true := by
      have g := good q hq
      cases q with
      | square i j a o =>
        simp only [allowed,lookup,Nat.testBit_or,Nat.testBit_xor,val]
        rw [binary_diff (v i) (v j)]
        exact g
      | cube i j k a b c bit sign =>
        simp only [allowed,lookup,Nat.testBit_or,Nat.testBit_and,Nat.testBit_xor,val,ha,Bool.true_xor]
        rw [binary_diff (v i) (v j),binary_le (v i) (v k)]
        exact g
    have ok := fold_bit (allowed all cols) ix rules hq all ha
    change (rules.foldl _ all != 0) = true
    apply bne_iff_ne.mpr
    intro zero
    rw [zero] at ok
    simp at ok
  next => rfl
end ColorBits

namespace PackedRows

def lane : Nat := (1 <<< 512)-1
def matrix : List Word → Nat
  | [] => 0
  | w::ws => w.toNat ||| (matrix ws <<< 512)

def stride (gap : Nat) := ((1 <<< (16*gap))-1)/((1 <<< gap)-1)
def spread (x : Nat) := ((x*stride 511) &&& stride 512)*lane
def collapse (x : Nat) :=
  let a := x ||| (x >>> 4096)
  let b := a ||| (a >>> 2048)
  let c := b ||| (b >>> 1024)
  (c ||| (c >>> 512)) &&& lane

def force (g active T x : Nat) (mono b : Bool) :=
  let s := spread (x &&& active)
  let bad := if mono then
      if b then g ^^^ (g &&& s) else s ^^^ (g &&& s)
    else g ^^^ s
  let want := if b then T else lane ^^^ T
  (want &&& (lane ^^^ collapse bad)) != 0

def edit (m i : Nat) (b : Bool) :=
  if m.testBit i == b then m else m ^^^ (1 <<< i)

def check {n : Nat} (g active T : Nat) (mono : Bool) : Rule n → Bool
  | .square i j a o =>
    [false,true].all fun u => [false,true].all fun v =>
      force g active T (edit (edit a j v) i u) mono (u && v) &&
      force g active T (edit (edit o j v) i u) mono (u || v)
  | .cube i j k a b c bit sign =>
    let except := (1 <<< i.val) ||| (1 <<< j.val)
    let dif := ((a ^^^ b) ||| (b ^^^ c)) &&& active
    ((dif &&& except)==dif) &&
      force g active T a mono false && force g active T b mono true &&
      force g active T (edit a k bit) mono sign && force g active T (edit b k bit) mono sign &&
      force g active T (edit c k bit) mono (!sign)

theorem matrix_bit (ws : List Word) (i j : Nat) (hj : j < 512) :
 (matrix ws).testBit (i*512+j) = ((ws[i]?).getD 0).getLsbD j := by
 induction ws generalizing i with
 | nil => simp [matrix]
 | cons w ws ih =>
   cases i with
   | zero =>
     simp [matrix,Nat.testBit_or,Nat.testBit_shiftLeft,show ¬512≤j by omega,BitVec.getLsbD]
   | succ i =>
     rw [Nat.succ_mul]
     simp only [matrix,Nat.testBit_or,Nat.testBit_shiftLeft]
     have upper : w.toNat.testBit (i*512+512+j) = false := by
       apply Nat.testBit_lt_two_pow
       exact lt_of_lt_of_le w.isLt (Nat.pow_le_pow_right (by decide) (by omega))
     rw [upper]
     simp [show 512 ≤ i*512+512+j by omega, show i*512+512+j-512 = i*512+j by omega,ih]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem collapse_false (z j : Nat) (hj : j<512) :
 (collapse z).testBit j = false ↔ ∀ i : Fin 16, z.testBit (i.val*512+j) = false := by
 simp [collapse,lane,Nat.testBit_and,Nat.testBit_or,Nat.testBit_shiftRight,Nat.shiftLeft_eq,hj,Fin.forall_fin_succ,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]
 simp only [and_assoc,and_left_comm,and_comm]

def slowSpread (x : Nat) := ColorBits.span 512 (fun d => if x.testBit d then lane else 0) 16
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem spread_correct : ∀ x : Fin 4096, spread x.val = slowSpread x.val := by decide +kernel

theorem force_sound (ws : List Word) (hn : ws.length ≤ 12) (T : Word) (mono b : Bool) (x : Nat)
 (h : force (matrix ws) (ColorBits.full ws.length) T.toNat x mono b = true) :
 forced T mono b ws (RankBase.RankRules.row x) = true := by
 let y := x &&& ColorBits.full ws.length
 let s := spread y
 let g := matrix ws
 let bad := if mono then if b then g ^^^ (g &&& s) else s ^^^ (g &&& s) else g ^^^ s
 let want := if b then T.toNat else lane ^^^ T.toNat
 change (want &&& (lane ^^^ collapse bad) != 0) = true at h
 obtain ⟨j,hj⟩ := Nat.exists_testBit_of_ne_zero (bne_iff_ne.mp h)
 rw [Nat.testBit_and,Bool.and_eq_true] at hj
 have lim : j<512 := by
   by_contra! large
   have t := Nat.testBit_lt_two_pow (x:=T.toNat) (i:=j) (lt_of_lt_of_le T.isLt (Nat.pow_le_pow_right (by decide) large))
   have z := hj.1
   cases b <;> simp [want,lane,Nat.testBit_xor,Nat.shiftLeft_eq,t,show ¬j<512 by omega] at z
 have clear := hj.2
 simp only [Nat.testBit_xor,show lane.testBit j = true by simpa [lane,Nat.shiftLeft_eq] using lim,Bool.true_xor,Bool.not_eq_true'] at clear
 have bits := (collapse_false bad j lim).mp clear
 have small : y < 4096 := by
   apply lt_of_le_of_lt (Nat.and_le_right ..)
   have pow := Nat.pow_le_pow_right (n:=2) (by decide) hn
   simp [ColorBits.full,Nat.shiftLeft_eq]
   omega
 have matchRows : ∀ i : Fin ws.length, fits mono b ((ws.get i).getLsbD j) (x.testBit i.val) = true := by
   intro i
   have r := bits ⟨i.val,by omega⟩
   have slice : s.testBit (i.val*512+j) = x.testBit i.val := by
     have eq := spread_correct (⟨y,small⟩ : Fin 4096)
     change (spread y).testBit _ = _
     rw [eq,slowSpread,ColorBits.span_at (w:=512) (f:=fun d => if y.testBit d then lane else 0) (fun d => by
       intro l hl
       split <;> simp [lane,Nat.shiftLeft_eq,show ¬l<512 by omega]) lim 16 (by omega)]
     cases e : x.testBit i.val <;> simp [e,y,Nat.testBit_and,ColorBits.full_bit,i.isLt,lane,Nat.shiftLeft_eq,lim]
   have wire : g.testBit (i.val*512+j) = (ws.get i).getLsbD j := by simpa [g,i.isLt] using matrix_bit ws i.val j lim
   change bad.testBit (i.val*512+j) = false at r
   cases mono <;> cases b <;> simp [bad,Nat.testBit_xor,Nat.testBit_and,wire,slice,fits] at r ⊢ <;> grind
 have gate := (mask_spec mono b ⟨j,lim⟩ ws (RankBase.RankRules.row x)).mpr matchRows
 simp only [forced,decide_eq_true_eq]
 intro zero
 have z := congrArg (fun w : Word => w.getLsbD j) zero
 have t := hj.1
 change (_ &&& _ : Word).getLsbD j = (0 : Word).getLsbD j at z
 rw [BitVec.getLsbD_and,gate] at z
 cases b
 · simp [want,lane,Nat.testBit_xor,Nat.shiftLeft_eq,lim] at t
   change T.getLsbD j = false at t
   simp only [Bool.false_eq_true,ite_false,BitVec.getLsbD_not,lim,decide_true,Bool.true_and,t,Bool.not_false,BitVec.getLsbD_zero] at z
   simpa [BitVec.getLsbD] using z
 · simp [want] at t
   change T.getLsbD j = true at t
   simp [t] at z

theorem row_edit {n} (m : Nat) (i : Fin n) (b : Bool) :
    row (edit m i.val b) = Function.update (row m) i b := by
  funext j
  by_cases h : j = i
  · subst j
    simp only [Function.update_self,row,edit]
    split
    next eq => exact beq_iff_eq.mp eq
    next ne =>
      simp [Nat.testBit_xor,Nat.shiftLeft_eq,Nat.testBit_two_pow]
      cases q : m.testBit i.val <;> cases b <;> simp_all
  · have hij : i.val ≠ j.val := fun e => h (Fin.ext e.symm)
    rw [Function.update_of_ne h]
    simp only [row,edit]
    split
    · rfl
    · simp [Nat.testBit_xor,Nat.shiftLeft_eq,Nat.testBit_two_pow,hij]

theorem edit_pair {n} (m : Nat) (i j : Fin n) (a b : Bool) :
    row (edit (edit m j.val b) i.val a) = pairInput i j (row m) a b := by
  rw [row_edit,row_edit]
  funext k
  by_cases hi : k = i <;> by_cases hj : k = j <;> simp [pairInput,hi,hj,Function.update]

theorem check_sound (T : Word) (mono : Bool) (ws : List Word) (hn : ws.length ≤ 12) (q : Rule ws.length)
 (h : check (matrix ws) (ColorBits.full ws.length) T.toNat mono q = true) : checksRule T mono ws q = true := by
 have F := force_sound ws hn T mono
 cases q with
 | square i j a o =>
   simp only [check,List.all_eq_true,Bool.and_eq_true] at h
   simp only [checksRule,List.all_eq_true,Bool.and_eq_true]
   intro u hu v hv
   obtain ⟨ha,ho⟩ := h u hu v hv
   exact ⟨edit_pair a i j u v ▸ F _ _ ha,edit_pair o i j u v ▸ F _ _ ho⟩
 | cube i j k a b c bit sign =>
   simp only [check,Bool.and_eq_true,beq_iff_eq] at h
   obtain ⟨⟨⟨⟨⟨dif,fa⟩,fb⟩,fak⟩,fbk⟩,fck⟩ := h
   simp only [checksRule,Bool.and_eq_true,List.all_eq_true]
   refine ⟨⟨⟨⟨⟨?_,F _ _ fa⟩,F _ _ fb⟩,row_edit a k bit ▸ F _ _ fak⟩,row_edit b k bit ▸ F _ _ fbk⟩,row_edit c k bit ▸ F _ _ fck⟩
   intro v hv
   by_cases vi : v = i
   · simp [vi]
   by_cases vj : v = j
   · simp [vj]
   have ni : i.val ≠ v.val := fun e => vi (Fin.ext e.symm)
   have nj : j.val ≠ v.val := fun e => vj (Fin.ext e.symm)
   have e := congrArg (fun z : Nat => z.testBit v.val) dif
   simp [Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,Nat.shiftLeft_eq,Nat.testBit_two_pow,ni,nj,ColorBits.full_bit,v.isLt] at e
   simp [vi,vj,row]
   grind

end PackedRows

def rankCheck (target : Word) (mono : Bool) (ws : List Word) (r code count : Nat) : Bool :=
  let rules := readRules ws.length count code
  (ws.length ≤ 12) && rules.all (PackedRows.check (PackedRows.matrix ws) (ColorBits.full ws.length) target.toNat mono) && !(ColorBits.fast (r+1) rules)

theorem rankCheck_sound {target : Word} {mono : Bool} {ws : List Word} {r code count : Nat}
    (F : (Fin ws.length → Bool) → Bool)
    (agree : ∀ p : Fin 512, F (fun i => (ws.get i).getLsbD p.val) = target.getLsbD p.val)
    (mon : mono = true → Monotone F) (group : Grouping r F)
    (h : rankCheck target mono ws r code count = true) : False := by
  let rules := readRules ws.length count code
  have pass : (ws.length ≤ 12 ∧ rules.all (PackedRows.check (PackedRows.matrix ws) (ColorBits.full ws.length) target.toNat mono) = true) ∧ ColorBits.fast (r+1) rules = false := by
    simpa only [rankCheck, Bool.and_eq_true, Bool.not_eq_true',decide_eq_true_eq] using h
  have accept (claim : Rule ws.length) (hc : claim ∈ rules) : accepts group.label claim = true :=
    checksRule_sound F agree mon group (PackedRows.check_sound target mono ws pass.1.1 claim (List.all_eq_true.mp pass.1.2 _ hc))
  have found : ColorBits.fast (r+1) rules = true :=
    ColorBits.sound (r:=r+1) (label:=group.label) accept
  rw [pass.2] at found
  contradiction

end PEqualNP.Outside.L_meta_3250.FrontRanks

namespace PEqualNP.Outside.L_meta_3250.FrontRanks
open RankBase RankBase.RankRules

def readPrefixField (format : Nat → Nat × (Nat → Nat)) (read : Nat → Nat → Nat)
    (kind p raw : Nat) : Nat × Nat :=
  let t := format kind
  let ent := t.2 (read p t.1)
  let value := ent &&& 8191
  let next := p+(ent >>> 13)
  if value == 4096 then (read next raw,next+raw) else (value,next)

def insertZeroAt (x i : Nat) : Nat :=
  (x &&& ((1 <<< i)-1)) ||| ((x >>> i) <<< (i+1))

def expandRow (x h : Nat) : Nat :=
  let i := h &&& 15
  let j := (h >>> 4) &&& 15
  insertZeroAt (insertZeroAt x (min i j)) (max i j)

def huffCodes (n : Nat) (f : Nat → Nat × (Nat → Nat)) (read : Nat → Nat → Nat) :
    Nat → Nat → Nat
  | 0, _ => 0
  | count+1, p =>
    let item := if read p 1 == 1 then
        ((f 4).2 (read (p+1) 10),p+11)
      else
        let hdr := readPrefixField f read 0 (p+1) 12
        let base := readPrefixField f read 1 hdr.2 (n-2)
        let square := hdr.1 >>> 8 == 15
        let tail := readPrefixField f read (if square then 3 else 2) base.2 (if square then n-2 else 7)
        let z := if square then expandRow tail.1 hdr.1 else tail.1
        (hdr.1 ||| (expandRow base.1 hdr.1 <<< 12) ||| (z <<< 24),tail.2)
    item.1 ||| (huffCodes n f read count item.2 <<< 36)

def rankHuffCheck (target : Word) (mono : Bool) (ws : List Word) (r : Nat)
    (format : Nat → Nat × (Nat → Nat)) (read : Nat → Nat → Nat) (tag p : Nat) : Bool :=
  if tag == 0 then false else if tag == 1 then
    forced target mono false ws (row (read p ws.length)) &&
      forced target mono true ws (row (read p ws.length))
  else
    rankCheck target mono ws r (huffCodes ws.length format read (tag-2) p) (tag-2)

theorem rankHuffCheck_sound {target : Word} {mono : Bool} {ws : List Word} {r tag p : Nat}
    {format : Nat → Nat × (Nat → Nat)} {read : Nat → Nat → Nat}
    (F : (Fin ws.length → Bool) → Bool)
    (agree : ∀ p : Fin 512, F (fun i => (ws.get i).getLsbD p.val) = target.getLsbD p.val)
    (mon : mono = true → Monotone F) (group : Grouping r F)
    (h : rankHuffCheck target mono ws r format read tag p = true) : False := by
  unfold rankHuffCheck at h
  split at h
  · contradiction
  split at h
  · simp only [Bool.and_eq_true] at h
    have no := forced_sound F agree mon false _ h.1
    have yes := forced_sound F agree mon true _ h.2
    rw [no] at yes
    contradiction
  · exact rankCheck_sound F agree mon group h

end PEqualNP.Outside.L_meta_3250.FrontRanks

namespace PEqualNP.Outside.L_meta_3250

open PEqualNP.CircuitLowerBounds

open PEqualNP.CircuitLowerBounds

namespace FromFrontier

def good (n : Nat) (g : Gate) : Prop :=
  (g.op = .not ∧ ∃ i<n, g.inputs=[i]) ∨
    ((g.op = .or ∨ g.op = .and) ∧ ∃ i<n, ∃ j<n, i≠j ∧ g.inputs=[i,j])

def wasRead (gs : List Gate) (i : Nat) : Prop := ∃ g∈gs, i∈g.inputs

def isNeg : GateOp → Bool
  | .not => true
  | _ => false

def realization (w : List Sig) (used : Nat → Prop) (T : Sig) (k t : Nat) : Prop :=
  ∃ (gs : List Gate) (o : Nat), gs.length=k ∧
    gs.countP (fun g => isNeg g.op)=t ∧ o<w.length+gs.length ∧
    (execute gs w).getD o zero=T ∧
    (∀ p g, gs[p]?=some g → good (w.length+p) g) ∧
    ∀ i<w.length+gs.length, i≠o → used i ∨ wasRead gs i

def bank (w : List Sig) (used : Nat → Prop) (S : Finset Sig) (ix : Sig → Nat) : Prop :=
  (∀ s∈S, ix s<w.length ∧ w.getD (ix s) zero=s) ∧
    ∀ i<w.length, used i ∨ ∃ s∈S, ix s=i

theorem forward {w : List Sig} {used : Nat → Prop} {T : Sig} {k t : Nat}
    {g : Gate} {z : Sig} (eq : gv w g=z) (ok : good w.length g)
    (next : realization (w++[z]) (fun i => used i ∨ i∈g.inputs) T k t) :
    realization w used T (k+1) (t+(if isNeg g.op then 1 else 0)) := by
  obtain ⟨gs,o,hl,ht,hb,he,hg,hr⟩ := next
  refine ⟨g::gs,o,by simp [hl],?_,by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hb,?_,?_,?_⟩
  · cases n : isNeg g.op <;> simp [List.countP_cons,ht,n,Nat.add_comm]
  · change (execute gs (w++[gv w g])).getD o zero=T
    rwa [eq]
  · intro p h hit
    cases p with
    | zero =>
      change some g=some h at hit
      exact Option.some.inj hit ▸ ok
    | succ p =>
      have sub : gs[p]?=some h := hit
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hg p h sub
  · intro i hi ne
    have bounds : i<(w++[z]).length+gs.length := by
      simp only [List.length_cons] at hi
      simp only [List.length_append,List.length_singleton]; omega
    rcases hr i bounds ne with (prior|atGate)|⟨h,hh,hi⟩
    · exact .inl prior
    · exact .inr ⟨g,by simp,atGate⟩
    · exact .inr ⟨h,List.mem_cons_of_mem _ hh,hi⟩

theorem extendBank {w : List Sig} {used : Nat → Prop} {S U : Finset Sig}
    {ix : Sig → Nat} {z : Sig} {g : Gate} (b : bank w used S ix)
    (fresh : z∉U) (subset : U⊆S) (reads : ∀ s∈S, s∈U ∨ ix s∈g.inputs) :
    bank (w++[z]) (fun i => used i ∨ i∈g.inputs) (insert z U)
      (fun s => if s=z then w.length else ix s) := by
  constructor
  · intro s hs
    rcases Finset.mem_insert.mp hs with rfl|hu
    · simp
    · have ne : s≠z := fun h => fresh (h ▸ hu)
      obtain ⟨bound,val⟩ := b.1 s (subset hu)
      simp only [ne,ite_false,List.length_append,List.length_singleton]
      refine ⟨by omega,?_⟩
      simpa only [List.getD_eq_getElem?_getD,List.getElem?_append_left bound] using val
  · intro i hi
    simp only [List.length_append,List.length_singleton] at hi
    by_cases lt : i<w.length
    · rcases b.2 i lt with already|⟨s,hs,hi⟩
      · exact .inl (.inl already)
      rcases reads s hs with hu|read
      · have ne : s≠z := fun h => fresh (h ▸ hu)
        exact .inr ⟨s,Finset.mem_insert_of_mem hu,by simpa [ne] using hi⟩
      · exact .inl (.inr (hi ▸ read))
    · have h : i=w.length := by omega
      exact .inr ⟨z,by simp,by simp [h]⟩

theorem build {T : Sig} {k t : Nat} {S : Finset Sig} (h : Live T k t S) :
    ∀ (w : List Sig) (used : Nat → Prop) (ix : Sig → Nat),
      bank w used S ix → realization w used T k t := by
  induction h with
  | stop hp =>
    intro w used ix b
    obtain ⟨bound,val⟩ := b.1 T (by simp)
    refine ⟨[],ix T,rfl,rfl,by simpa using bound,val,?_,?_⟩
    · intro i g hit; simp at hit
    · intro i hi ne
      rcases b.2 i (by simpa using hi) with hu|⟨s,hs,hit⟩
      · exact Or.inl hu
      simp only [Finset.mem_singleton] at hs
      exact (ne (hs ▸ hit.symm)).elim
  | @unary k t U a proper fresh tail ih =>
    intro w used ix b
    obtain ⟨bound,val⟩ := b.1 a (by simp)
    let g : Gate := ⟨.not,[ix a]⟩
    have hv : gv w g = neg a := by
      change neg (w.getD (ix a) zero)=neg a
      rw [val]
    have well : good w.length g := Or.inl ⟨rfl,ix a,bound,rfl⟩
    apply forward hv well
    apply ih
    apply extendBank b (fun hz => fresh (Finset.mem_insert_of_mem hz)) (fun _ hy => Finset.mem_insert_of_mem hy)
    intro s hs
    rcases Finset.mem_insert.mp hs with rfl|hu
    · right; simp [g]
    · exact .inl hu
  | @binary k t U a c d pa pc diff fresh tail ih =>
    intro w used ix b
    obtain ⟨ba,va⟩ := b.1 a (by simp)
    obtain ⟨bc,vc⟩ := b.1 c (by simp)
    have unique : ix a ≠ ix c := fun eq => diff (va.symm.trans (eq ▸ vc))
    let g : Gate := ⟨if d then .or else .and,[ix a,ix c]⟩
    have hv : gv w g = bin d a c := by
      cases d with
      | false =>
        change bin false (w.getD (ix a) zero) (bin false (w.getD (ix c) zero) one)=bin false a c
        rw [va,vc]
        simp only [bin,Bool.false_eq_true,ite_false,one,BitVec.and_allOnes]
      | true =>
        change bin true (w.getD (ix a) zero) (bin true (w.getD (ix c) zero) zero)=bin true a c
        rw [va,vc]
        simp [bin,zero]
    have well : good w.length g := by
      apply Or.inr
      exact ⟨by cases d <;> simp [g],ix a,ba,ix c,bc,unique,rfl⟩
    have notCount : isNeg g.op=false := by cases d <;> rfl
    have rel : realization w used T (k+1) (t+(if isNeg g.op then 1 else 0)) := by
      apply forward hv well
      apply ih
      apply extendBank b (fun hz => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hz)))
        (fun _ hy => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hy))
      intro s hs
      rcases Finset.mem_insert.mp hs with rfl|hrest
      · right; simp [g]
      rcases Finset.mem_insert.mp hrest with rfl|hu
      · right; simp [g]
      · exact .inl hu
    simpa [notCount] using rel

theorem realize {T : Sig} {k t : Nat} (ws : List Sig) (hn : ws.Nodup)
    (h : Live T k t ws.toFinset) : realization ws (fun _ => False) T k t := by
  apply build h ws (fun _ => False) (fun x => ws.idxOf x)
  constructor
  · intro s hs
    have mem := List.mem_toFinset.mp hs
    have lt := List.idxOf_lt_length_of_mem mem
    exact ⟨lt,by rw [List.getD_eq_getElem _ _ lt, List.getElem_idxOf]⟩
  · intro i hi
    refine .inr ⟨ws[i],List.mem_toFinset.mpr (List.getElem_mem hi),?_⟩
    have idx := List.idxOf_lt_length_of_mem (List.getElem_mem hi : ws[i]∈ws)
    have eq : (⟨ws.idxOf ws[i],idx⟩ : Fin ws.length) = ⟨i,hi⟩ :=
      (List.nodup_iff_injective_get.mp hn) (List.getElem_idxOf idx)
    exact congrArg Fin.val eq

end FromFrontier

open PEqualNP.CircuitLowerBounds
open RankBase.CircuitProof RankBase.PetersenCutTrace

namespace FromFrontier

theorem realizeRank {T : Sig} {k t : Nat} (ws : List Sig) (hn : ws.Nodup)
    (h : Live T k t ws.toFinset) :
    ∃ (gs : List Gate) (out : Fin (ws.length + gs.length)) (cl : CleanL ws.length gs),
      nonNotCount gs=k-t ∧ gs.length=k ∧
      (∀ w, w≠out → ∃ v, readEdge gs w v) ∧
      (∀ w, (predecessors cl w).Nodup) ∧
      (∀ x : Fin 512, vl gs (fun i => (ws.get i).getLsbD x.val) out.val =
        T.getLsbD x.val) := by
  obtain ⟨gs,o,hl,ht,ho,val,well,reads⟩ := realize ws hn h
  have clean : CleanL ws.length gs := by
    intro p g hg
    rcases well p g hg with hnot|⟨op,i,bi,j,bj,_,pins⟩
    · exact .inl hnot
    · exact .inr ⟨op.symm,i,j,bi,bj,pins⟩
  refine ⟨gs,⟨o,ho⟩,clean,?_,hl,?_,?_,?_⟩
  · have eq : isNotGate = isNeg := by funext op; cases op <;> rfl
    have total := RankBase.nonNotCount_add_notCount gs
    rw [← List.countP_eq_length_filter,eq] at total
    omega
  · intro w ne
    rcases reads w.val w.isLt (fun eq => ne (Fin.ext eq)) with impossible|⟨g,hg,pin⟩
    · exact impossible.elim
    obtain ⟨i,hi,hgi⟩ := List.getElem_of_mem hg
    exact ⟨⟨ws.length+i,by omega⟩,i,g,by simp [List.getElem?_eq_getElem hi,hgi],rfl,pin⟩
  · intro w
    by_cases internal : ws.length≤w.val
    · apply List.Nodup.of_map Fin.val
      rw [predecessors_values clean w internal]
      have lo : w.val-ws.length < gs.length := by have := w.isLt; omega
      have hw := well _ _ (List.getElem?_eq_getElem lo : gs[w.val-ws.length]?=some _)
      rcases hw with ⟨_,i,_,pins⟩|⟨_,i,_,j,_,ne,pins⟩
      · simp [pins]
      · simp [pins,ne]
    · rw [predecessors_nil_input clean w (by omega)]; simp
  · intro x
    have legal (g : Gate) (hg : g∈gs) : g.op∈({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) := by
      obtain ⟨i,hi,hgi⟩ := List.getElem_of_mem hg
      have got : gs[i]?=some g := by simp [List.getElem?_eq_getElem hi,hgi]
      exact ((clean i g got).nok).1.1
    have init : List.ofFn (fun i : Fin ws.length => bit x (ws.get i))=ws.map (bit x) := by
      apply List.ext_getElem <;> simp
    change (wiresFrom gs (List.ofFn fun i : Fin ws.length => bit x (ws.get i))).getD o false=bit x T
    rw [init]
    change (gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (ws.map (bit x))).getD o false=bit x T
    rw [←execute_bits gs x ws legal,b_read,val]

end FromFrontier

namespace FromFrontier

private theorem increasingRun (gs : List Gate)
    (pos : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) (a b : List Bool)
    (sz : a.length=b.length) (h : ∀ i, a.getD i false ≤ b.getD i false) :
    ∀ i, (wiresFrom gs a).getD i false ≤ (wiresFrom gs b).getD i false := by
  induction gs generalizing a b with
  | nil => exact h
  | cons g gs ih =>
    apply ih (fun v hv => pos v (by simp [hv]))
    · simp [sz]
    · intro j
      by_cases eq : j=a.length
      · subst j
        rw [getD_snoc_len _ _ _ _ rfl, getD_snoc_len b _ _ _ sz.symm]
        apply Bool.le_iff_imp.mpr
        rcases pos g (by simp) with op|op
        · simp only [op, GateOp.eval,List.all_map,List.all_eq_true,Function.comp_apply,id_eq]
          intro yes p hp
          exact Bool.le_iff_imp.mp (h p) (yes p hp)
        · simp only [op, GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq]
          rintro ⟨p,hp,yes⟩
          exact ⟨p,hp,Bool.le_iff_imp.mp (h p) yes⟩
      · rw [getD_snoc_ne _ _ _ _ eq,getD_snoc_ne _ _ _ _ (by omega)]
        exact h j

theorem groupFromLive {T : Sig} {k t r : Nat} (ws : List Sig) (hn : ws.Nodup)
    (budget : k-t+1≤ws.length+r) (run : Live T k t ws.toFinset) :
    ∃ (F : (Fin ws.length → Bool) → Bool), Nonempty (RankBase.Grouping r F) ∧
      (∀ x : Fin 512, F (fun i => (ws.get i).getLsbD x.val) = T.getLsbD x.val) ∧
      (t=0 → Monotone F) := by
  obtain ⟨gs,out,cl,cnt,sz,live,distinct,ok⟩ := realizeRank ws hn run
  let F := fun x : Fin ws.length → Bool => vl gs x out.val
  have limit := RankBase.forkBudget cl out live (cnt ▸ budget)
  obtain ⟨label,loc,codes⟩ := RankBase.rankCuts cl out live limit
  refine ⟨F,⟨⟨label,fun i j h => RankBase.generalConflict cl out live distinct (i,j) ((loc i j).mp h),codes⟩⟩,ok,?_⟩
  intro tz x y xy
  have total := RankBase.nonNotCount_add_notCount gs
  have zero : gs.countP (fun g => isNotGate g.op)=0 := by
    rw [←List.countP_eq_length_filter] at total
    omega
  have pos (g : Gate) (hg : g∈gs) : g.op=.and ∨ g.op=.or := by
    have neg := List.countP_eq_zero.mp zero g hg
    obtain ⟨i,hi,eq⟩ := List.getElem_of_mem hg
    have atSlot : gs[i]?=some g := by simp [List.getElem?_eq_getElem hi,eq]
    rcases cl i g atSlot with ⟨op,_⟩|⟨op,_⟩
    · simp [op,isNotGate] at neg
    · exact op
  apply increasingRun gs pos _ _ (by simp)
  intro i
  by_cases hi : i<ws.length
  · simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem,hi] using xy ⟨i,hi⟩
  · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by simp; omega)]

end FromFrontier

private theorem signed_bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]

private lemma signed_live_proper {k t S} (h : Live target k t S) : ∀ a ∈ S, proper a := by
  induction h with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma signed_live_size {k t S} (h : Live target k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
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

def Limited (T : Sig) (cap budget : Nat) (S : Finset Sig) : Prop :=
  ∀ k t, k ≤ cap → t ≤ budget → ¬Live T k t S

def remainder (budget op : Nat) := budget - (if op=2 then 1 else 0)

theorem enum_signed {T : Sig} {cap budget : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (oneStep : 0 < budget → ∀ a ∈ ws, ∀ keep, neg a ∉ ws → proper (neg a) →
      (childOne ws a keep).length ≤ cap →
      Limited T (cap-1) (budget-1) (childOne ws a keep).toFinset)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Limited T (cap-1) budget (childTwo ws a b d ka kb).toFinset) :
    Limited T cap budget ws.toFinset := by
  classical
  intro k t hk hnots h
  generalize he : ws.toFinset = S at h
  cases h with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @unary k t U a ha hf tail =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have fresh : neg a ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := signed_live_proper tail _ (Finset.mem_insert_self _ _)
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
    have sc := (signed_live_size tail).2
    have len : (childOne ws a keep).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact oneStep (by omega) a am keep fresh hz len k t (by omega) (by omega) (eq.symm ▸ tail)
  | @binary k t U a b d ha hb hab hf tail =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := signed_live_proper tail _ (Finset.mem_insert_self _ _)
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
    have sc := (signed_live_size tail).2
    have len : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d ka kb hab fresh hz len k t (by omega) hnots (eq.symm ▸ tail)

abbrev SignedLinks :=
  (Nat → Nat → List (List Sig)) × ExtraCut × (Nat → List Sig → Bool)

def closeSigned (pools : List BoundPool) (links : SignedLinks) (k budget : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op :: rest
  pools.any (fun p => scalarPoolCut p k rest op) ||
    (links.1 budget (keySet ws)).any (sameWords ws) ||
    links.2.1 k ws || links.2.2 budget ws

theorem closeSigned_sound {raw T pools} {links : SignedLinks} {k budget rest op}
    (pValid : ∀ p ∈ pools, ValidPool raw T p)
    (lValid : ∀ tag xs, xs ∈ links.1 budget tag → Limited T k budget (List.toFinset xs))
    (cutValid : ∀ ws : List Sig, ws.Nodup → links.2.1 k ws = true → Impossible T k ws.toFinset)
    (orientValid : ∀ ws : List Sig, links.2.2 budget ws = true → Limited T k budget ws.toFinset)
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeSigned pools links k budget rest op = true) :
    Limited T k budget (choiceVal op :: rest).toFinset := by
  simp only [closeSigned,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ((⟨p,hp,ok⟩ | ⟨xs,hx,ok⟩) | cut) | orient
  · intro m t hm _
    exact scalarPoolCut_sound (pValid _ hp) nd ok m t hm
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · intro m t hm _
    exact cutValid _ nd cut m t hm
  · exact orientValid _ orient

abbrev SignedContext := Nat × Nat × Nat × List Decor × CovPair × List BoundPool × SignedLinks
def evalSigned (c : SignedContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,budget,n,ws,cov,pools,links) := c
  let un := op==2
  let len := 1+(n - (if ka then 0 else 1) - (if un || kb then 0 else 1))
  if (op==2 && budget==0) || decide (len>cap) then true else
    let d := (len==cap) || (remainder budget op==0)
    let rs := restCov (getCov cov d) (column d a.2) (column d b.2) un ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 768 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (opKeep un ka kb a b ws).map Prod.fst
      closeSigned pools links (cap-1) (remainder budget op) rest (movedChoice op a b)

theorem evalSigned_sound {raw T r s ws pools} {links : SignedLinks} {cap budget a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : (op==2)=false → a≠b) (hcap : 0<cap)
    (allows : op=2 → 0<budget)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links.1 (remainder budget op) tag →
      Limited T (cap-1) (remainder budget op) (List.toFinset xs))
    (cv : ∀ words : List Sig, words.Nodup → links.2.1 (cap-1) words = true → Impossible T (cap-1) words.toFinset)
    (ov : ∀ words : List Sig, links.2.2 (remainder budget op) words = true →
       Limited T (cap-1) (remainder budget op) words.toFinset)
    (pro : proper (movedDecor op a b).1) (fresh : (movedDecor op a b).1 ∉ ws.map Prod.fst)
    (test : evalSigned (cap,budget,ws.length,ws,preCov ws,pools,links) op a b (movedDecor op a b) ka kb = true) :
    Limited T (cap-1) (remainder budget op) (moveFront ws op a b ka kb).toFinset := by
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
  intro k t hk nt h
  have hsz := (signed_live_size h).2
  change child.toFinset.card + t ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold evalSigned at test
  have validMove : (op==2 && budget==0) = false := by
    apply Bool.eq_false_iff.mpr
    intro yes
    simp only [Bool.and_eq_true,beq_iff_eq] at yes
    exact (Nat.ne_of_gt (allows yes.1)) yes.2
  change (if (op==2 && budget==0) || decide (1+(ws.length-_ - _) > cap) then true else _) = true at test
  rw [leq,validMove] at test
  simp only [Bool.false_or, decide_eq_false (show ¬ child.length > cap by omega), Bool.false_eq_true, ite_false] at test
  let d := (child.length==cap) || (remainder budget op==0)
  have sep := cover_sound h rfl (pair_sep pairs) d (by
    intro hd
    change (child.length==cap || remainder budget op==0) = true at hd
    simp only [Bool.or_eq_true,beq_iff_eq] at hd
    rcases hd with equal | exhausted <;> omega)
  have g : (coverage d rest).1 = covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz := rest_coverage ha hb (op==2) ka kb d ne
  have hf := moved_faithful (faith _ ha) (faith _ hb) op
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
  exact closeSigned_sound pv lv cv ov nd' test k t hk nt h

def signedPair (ctx : SignedContext) (a b : Decor) (d : Bool) :=
  let op := if d then 1 else 0
  let z := movedDecor op a b
  let attempt := evalSigned ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def signedRow (ctx : SignedContext) (a : Decor) (bs : List Decor) :=
  let z := movedDecor 2 a a
  evalSigned ctx 2 a a z false false && evalSigned ctx 2 a a z true true &&
    bs.all (fun b => signedPair ctx a b false && signedPair ctx a b true)
def signedAll (ctx : SignedContext) : List Decor → Bool
  | [] => true
  | a::bs => signedRow ctx a bs && signedAll ctx bs

theorem signed_unary {ctx ws} (h : signedAll ctx ws=true) {a : Decor} (ha : a∈ws) (keep : Bool) :
    evalSigned ctx 2 a a (movedDecor 2 a a) keep keep=true := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [signedAll,Bool.and_eq_true,signedRow] at h
    rcases List.mem_cons.mp ha with rfl | hm
    · cases keep
      · exact h.1.1.1
      · exact h.1.1.2
    · exact ih h.2 hm

theorem signed_binary {ctx ws} (h : signedAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) (d : Bool) : signedPair ctx a b d=true ∨ signedPair ctx b a d=true := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [signedAll,Bool.and_eq_true,signedRow,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      left
      cases d <;> first | exact (h.1.2 b bm).1 | exact (h.1.2 b bm).2
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · right
        cases d <;> first | exact (h.1.2 a haTail).1 | exact (h.1.2 a haTail).2
      · exact ih h.2 haTail hbTail

theorem signedPair_at {ctx a b d} (h : signedPair ctx a b d = true) (ka kb : Bool) :
    evalSigned ctx (if d then 1 else 0) a b (movedDecor (if d then 1 else 0) a b) ka kb = true := by
  simp only [signedPair,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2

theorem nodeSigned_sound {raw T r s ws pools} {links : SignedLinks} {cap budget}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ b tag xs, xs ∈ links.1 b tag → Limited T (cap-1) b (List.toFinset xs))
    (cv : ∀ words : List Sig, words.Nodup → links.2.1 (cap-1) words = true → Impossible T (cap-1) words.toFinset)
    (ov : ∀ b words, links.2.2 b words = true → Limited T (cap-1) b words.toFinset)
    (checks : signedAll (cap,budget,ws.length,ws,preCov ws,pools,links) ws = true) :
    Limited T cap budget (ws.map Prod.fst).toFinset := by
  by_cases hc : cap=0
  · intro k t hk _ h
    have ke : k=0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    cases h
    exact out (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  have hc' : 0<cap := by omega
  apply enum_signed nd out
  · intro hb v hv keep fresh pro len
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hv
    have hf := unary_front nd ha keep
    rw [←hf]
    exact evalSigned_sound (op:=2) pairs faith nd ha ha (by simp) hc' (fun _ => hb) pv
      (lv _) cv (ov _) pro fresh (signed_unary checks ha keep)
  · intro a ha b hb d ka kb ne fresh pro len
    obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
    obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
    have ab : a≠b := fun e => ne (congrArg Prod.fst e)
    have one (a b : Decor) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
        (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
        (test : signedPair (cap,budget,ws.length,ws,preCov ws,pools,links) a b d = true) :
        Limited T (cap-1) budget (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
      rw [←binary_front nd aa bb ne']
      have eq : (movedDecor (if d then 1 else 0) a b).1 = bin d a.1 b.1 := by cases d <;> rfl
      have hstay : remainder budget (if d then 1 else 0) = budget := by cases d <;> simp [remainder]
      rw [← hstay]
      exact evalSigned_sound pairs faith nd aa bb (fun _ e => ne' (congrArg Prod.fst e)) hc'
        (by cases d <;> simp) pv (lv _) cv (ov _) (eq ▸ pr) (eq ▸ fr) (signedPair_at test ka kb)
    rcases signed_binary checks haW hbW ab d with hh | hh
    · exact one a b haW hbW ne ka kb pro fresh hh
    · rw [childTwo_swap _ nd]
      exact one b a hbW haW (Ne.symm ne) kb ka (signed_bin_comm d a.1 b.1 ▸ pro)
        (signed_bin_comm d a.1 b.1 ▸ fresh) hh

theorem rotateLimited {T n budget} {ws : List Sig} (hi : Limited T n budget ws.toFinset)
    (p : List Move) (ok : autoOK T p = true) : Limited T n budget (ws.map (movedWord p.reverse)).toFinset := by
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
    · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩
      simpa only [inv] using hw
    · intro ha
      exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
  rw [goal,back] at run
  exact hi k t hk ht run

structure SignedForest where
  base : Forest
  budget : Nat → Nat → Nat
  orientedPairs : List (Row × Row)

def signedLinked (g : SignedForest) (k budget : Nat) (p : Nat × Nat) : Option (List Sig) :=
  if g.budget k p.1 = budget then linkedSet g.base k p else none

theorem signedLinked_sound (g : SignedForest) (k budget : Nat)
    (names : ∀ x ∈ g.base.autos.toList, autoOK (targetOf g.base) (x.map swapRows) = true)
    (earlier : ∀ i < (g.base.levels k).1,
      Limited (targetOf g.base) k (g.budget k i) (stateSet g.base k i).toFinset)
    {p out} (h : signedLinked g k budget p = some out) :
    Limited (targetOf g.base) k budget out.toFinset := by
  unfold signedLinked at h
  split at h
  next sb =>
    unfold linkedSet at h
    split at h
    · contradiction
    next valid =>
      cases ep : g.base.autos[p.2]? with
      | none => simp [ep] at h
      | some perm =>
        simp only [ep, Option.map_some, Option.some.injEq] at h
        subst out
        rw [← sb]
        exact rotateLimited (earlier _ (by omega)) _ (names _ (by simpa using Array.mem_of_getElem? ep))
  next _ => contradiction

def orientedPairsOK (g : SignedForest) :=
  g.orientedPairs.all fun (p,n) => bit p (targetOf g.base) && !(bit n (targetOf g.base))

def orientedExcluded (g : SignedForest) (budget : Nat) (ws : List Sig) :=
  (budget == 0) && g.orientedPairs.any fun (p,n) =>
    ws.all fun sig => !(bit p sig) || bit n sig

theorem orientedExcluded_sound (g : SignedForest) (good : orientedPairsOK g = true)
    {cap budget ws} (he : orientedExcluded g budget ws = true) :
    Limited (targetOf g.base) cap budget ws.toFinset := by
  simp only [orientedExcluded, Bool.and_eq_true, beq_iff_eq, List.any_eq_true] at he
  obtain ⟨zeroBudget,⟨⟨p,n⟩,mem,bad⟩⟩ := he
  intro k t hk ht live
  have pair := List.all_eq_true.mp good (p,n) mem
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at pair
  obtain ⟨sig,has,yes,no⟩ := mono_row_difference live (by omega) pair.1 pair.2
  have h := List.all_eq_true.mp bad sig (List.mem_toFinset.mp has)
  simp [yes,no] at h

def stateSigned (g : SignedForest) (k i : Nat) : SignedContext :=
  let c := contextOf g.base k i
  let ref := fun budget tag =>
    ((g.base.index k (2*tag+budget)).bind (signedLinked g (k-1) budget)).toList
  (k,g.budget k i,c.2.2.1.length,c.2.2.1,preCov c.2.2.1,c.2.2.2.2.1,ref,g.base.cut,orientedExcluded g)

def nodeSignedVerified (g : SignedForest) (k i : Nat) :=
  prelim (targetOf g.base) (contextOf g.base k i) &&
    (if k=0 then true else signedAll (stateSigned g k i) (contextOf g.base k i).2.2.1)

theorem nodeSignedVerified_sound (g : SignedForest) (k i : Nat)
    (samples : properPairs (targetOf g.base) (asRow fun j => (g.base.samples j).1)
      (asRow fun j => (g.base.samples j).2))
    (cols : ∀ ci ∈ g.base.cols.values,
      Slice (vars g.base.mask) (targetOf g.base) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.base.autos.toList, autoOK (targetOf g.base) (x.map swapRows) = true)
    (pairs : orientedPairsOK g = true)
    (prior : k>0 → ∀ j < (g.base.levels (k-1)).1,
      Limited (targetOf g.base) (k-1) (g.budget (k-1) j) (stateSet g.base (k-1) j).toFinset)
    (checked : nodeSignedVerified g k i = true) :
    Limited (targetOf g.base) k (g.budget k i) (stateSet g.base k i).toFinset := by
  simp only [nodeSignedVerified, prelim, Bool.and_eq_true, decide_eq_true_eq,
    Bool.not_eq_true', List.contains_eq_mem] at checked
  have hN := checked.1.1
  have hT : targetOf g.base ∉ stateSet g.base k i := of_decide_eq_false checked.1.2
  by_cases h0 : k=0
  · subst k
    intro t b ht _ h
    have hb : t=0 := by omega
    subst t
    generalize he : (stateSet g.base 0 i).toFinset = S at h
    cases h
    exact hT (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  apply nodeSigned_sound (raw:=vars g.base.mask) samples _ hN hT _ _
    (g.base.cut_sound _) (fun _ _ h => orientedExcluded_sound g pairs h)
    (by
      have good := checked.2
      rw [ite_eq_right h0] at good
      exact good)
  · intro v hv
    apply decode_faithful _ _ _ _ _ (wires_faithful g.base) v
    exact (selectLive_sub _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hp
    exact buildRule_sound g.base cols h
  · intro budget tag xs hx
    have e : ((g.base.index k (2*tag+budget)).bind (signedLinked g (k-1) budget))=some xs := by
      simpa using hx
    obtain ⟨p,_,h⟩ := Option.bind_eq_some_iff.mp e
    exact signedLinked_sound g _ _ names (prior (by omega)) h

abbrev FrontierTest := Sig → Bool → List Sig → Nat → Nat → Nat → Bool

def frontierTestOK (test : FrontierTest) : Prop :=
  ∀ T mono ws r k i (F : (Fin ws.length → Bool) → Bool),
    (∀ x : Fin 512, F (fun j => (ws.get j).getLsbD x.val) = T.getLsbD x.val) →
    (mono=true → Monotone F) → RankBase.Grouping r F → test T mono ws r k i=true → False

def rankNode (test : FrontierTest) (g : SignedForest) (k i : Nat) : Bool :=
  let ws := stateSet g.base k i
  let T := targetOf g.base
  decide ws.Nodup && decide (g.budget k i ≤ 1) &&
    test T true ws (k+1-ws.length) k i &&
    (g.budget k i == 0 || decide (k<ws.length) || test T false ws (k-ws.length) k i)

theorem rankNode_sound (test : FrontierTest) (ok : frontierTestOK test)
    (g : SignedForest) (k i : Nat) (checked : rankNode test g k i=true) :
    Limited (targetOf g.base) k (g.budget k i) (stateSet g.base k i).toFinset := by
  let ws := stateSet g.base k i
  simp only [rankNode,Bool.and_eq_true,decide_eq_true_eq,Bool.or_eq_true,beq_iff_eq] at checked
  obtain ⟨⟨⟨unique,one⟩,monoOK⟩,signedOK⟩ := checked
  intro a t ak tb run
  have ht := (signed_live_size run).1
  have size := (signed_live_size run).2
  rw [List.toFinset_card_of_nodup unique] at size
  change ws.length + t ≤ a+1 at size
  by_cases noNot : t=0
  · obtain ⟨F,⟨gr⟩,ag,mon⟩ := FromFrontier.groupFromLive ws unique
      (r:=k+1-ws.length) (by omega : a-t+1≤ws.length+(k+1-ws.length)) run
    exact ok _ true _ _ _ _ F ag (fun _ => mon noNot) gr monoOK
  · obtain (zero|tooLarge)|okSigned := signedOK
    · omega
    · change k<ws.length at tooLarge
      omega
    · obtain ⟨F,⟨gr⟩,ag,mon⟩ := FromFrontier.groupFromLive ws unique
        (r:=k-ws.length) (by omega : a-t+1≤ws.length+(k-ws.length)) run
      exact ok _ false _ _ _ _ F ag (by simp) gr okSigned

def hybridNode (test : FrontierTest) (count : Nat → Nat) (g : SignedForest) (k i : Nat) :=
  if i<count k then rankNode test g k i else nodeSignedVerified g k i
def hybridBlock (test : FrontierTest) (count : Nat → Nat) (g : SignedForest) (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => hybridNode test count g k (start+n) && hybridBlock test count g k start n

theorem hybridBlock_at {test count g k start n} (h : hybridBlock test count g k start n = true) (j : Nat)
    (lo : start ≤ j) (hi : j < start+n) : hybridNode test count g k j = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [hybridBlock, Bool.and_eq_true] at h
    by_cases eq : j = start+n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)

theorem hybridBlock_merge {test count g k start a b} (h : hybridBlock test count g k start a = true)
    (h' : hybridBlock test count g k (start+a) b = true) : hybridBlock test count g k start (a+b) = true := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [hybridBlock, Bool.and_eq_true] at h'
    simp only [Nat.add_succ, hybridBlock, Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1, ih h'.2⟩

def hybridTables (test : FrontierTest) (count : Nat → Nat) (g : SignedForest) (top : Nat) :=
  ∀ k ≤ top, hybridBlock test count g k 0 (g.base.levels k).1 = true

theorem hybridForest_all (test : FrontierTest) (sound : frontierTestOK test) (count : Nat → Nat)
    (g : SignedForest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geometry : graphValid g.base prior = true) (pairs : orientedPairsOK g = true)
    (rows : hybridTables test count g top) :
    ∀ k ≤ top, ∀ i < (g.base.levels k).1,
      Limited (targetOf g.base) k (g.budget k i) (stateSet g.base k i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hk i hi
    have checked := hybridBlock_at (rows k hk) i (by omega) (by omega)
    unfold hybridNode at checked
    split at checked
    · exact rankNode_sound test sound g k i checked
    · apply nodeSignedVerified_sound g k i (chart_pairs geometry.1.1.1 geometry.1.1.2)
        (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2 pairs _ checked
      intro pos
      exact ih (k-1) (by omega) (by omega)

private lemma cutLiveSize {k t S} (h : Live target k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
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

private lemma cutBitBin (i : Row) (d : Bool) (a b : Sig) : bit i (bin d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [bit,bin]
private lemma cutBitNeg (i : Row) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
def Sensitive (T : Sig) (S : Finset Sig) (r : Row) (v : Sig) : Prop :=
  ∃ s, bit r T ≠ bit s T ∧ ∀ u ∈ S, u ≠ v → bit r u = bit s u

def Pivot (T : Sig) (S : Finset Sig) (r s : Row) (v : Sig) : Prop :=
  Sensitive T S r v ∧ Sensitive T S s v

private theorem sensitive_mem (l : Live T k t S) (h : Sensitive T S r v) : v∈S := by
  rcases h with ⟨s,d,h⟩
  obtain ⟨u,hu,hd⟩ := live_row_difference l d
  by_contra z
  exact hd (h _ hu (fun e => z (e ▸ hu)))

private theorem sensitive_unary (az : a∉U) (h : Sensitive T (insert a U) r v) :
    Sensitive T (insert (neg a) U) r (if v=a then neg a else v) := by
  rcases h with ⟨s,hd,hn⟩
  refine ⟨s,hd,?_⟩
  intro u hu ne
  rcases Finset.mem_insert.mp hu with rfl|hu
  · by_cases eq : v=a
    · simp [eq] at ne
    · rw [cutBitNeg,cutBitNeg,hn _ (by simp) (Ne.symm eq)]
  · apply hn _ (Finset.mem_insert_of_mem hu)
    intro e
    subst u
    by_cases eq : v=a
    · exact az (eq ▸ hu)
    · simp [eq] at ne

private theorem sensitive_binary (az : a∉U) (bz : b∉U)
    (h : Sensitive T (insert a (insert b U)) r v) :
    Sensitive T (insert (bin d a b) U) r (if v=a ∨ v=b then bin d a b else v) := by
  rcases h with ⟨s,hd,hn⟩
  refine ⟨s,hd,?_⟩
  intro u hu ne
  rcases Finset.mem_insert.mp hu with rfl|hu
  · by_cases eq : v=a ∨ v=b
    · simp [eq] at ne
    · rw [cutBitBin,cutBitBin,hn a (by simp) (fun e => eq (.inl e.symm)),
        hn b (by simp) (fun e => eq (.inr e.symm))]
  · apply hn _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu))
    intro e
    subst u
    by_cases eq : v=a ∨ v=b
    · rcases eq with e|e
      · exact az (e ▸ hu)
      · exact bz (e ▸ hu)
    · simp [eq] at ne

private theorem sensitive_pass {g a b : Sig} {d : Bool} (az : a∉U) (ab : a≠b)
    (law : ∀ r, bit r g = (if d then bit r a || bit r b else bit r a && bit r b))
    (l : Live T k t (insert g U)) (h : Sensitive T (insert a (insert b U)) r a) :
    bit r b = !d ∧ bit r g = bit r a := by
  rcases h with ⟨s,hd,hn⟩
  obtain ⟨u,hu,uh⟩ := live_row_difference l hd
  rcases Finset.mem_insert.mp hu with rfl | hu
  · have eq := hn b (by simp) ab.symm
    rw [law,law] at uh
    rw [law,←eq] at *
    all_goals cases d <;> cases a' : bit r a <;> cases b' : bit r b <;>
      cases c' : bit s a <;> simp_all
  · exact (uh (hn _ (by simp [hu]) (fun e => az (e ▸ hu)))).elim

private theorem two_split {U : Finset Sig} {i j a b : Sig} {d : Bool}
    (az : a∉U) (bz : b∉U) (ab : a≠b) (hf : bin d a b ∉ insert a (insert b U)) (l : Live T k t (insert (bin d a b) U))
    (p : Pivot T (insert a (insert b U)) r s i)
    (q : Pivot T (insert a (insert b U)) r s j)
    (hi : bit r i ≠ bit s i) (hj : bit r j ≠ bit s j) (ne : i≠j) :
    ∃ i' j', Pivot T (insert (bin d a b) U) r s i' ∧ Pivot T (insert (bin d a b) U) r s j' ∧
      bit r i' ≠ bit s i' ∧ bit r j' ≠ bit s j' ∧ i'≠j' := by
  let f (v : Sig) := if v=a ∨ v=b then bin d a b else v
  have lift {v} (pv : Pivot T (insert a (insert b U)) r s v) :
       Pivot T (insert (bin d a b) U) r s (f v) :=
    ⟨sensitive_binary az bz pv.1,sensitive_binary az bz pv.2⟩
  have passA {row} (pv : Sensitive T (insert a (insert b U)) row a) :=
    sensitive_pass az ab (d:=d) (fun i => cutBitBin i d a b) l pv
  have passB {row} (pv : Sensitive T (insert a (insert b U)) row b) :
      bit row a = !d ∧ bit row (bin d a b) = bit row b := by
    apply sensitive_pass bz ab.symm (d:=d) (fun i => ?_) l
    · simpa [Finset.insert_comm] using pv
    · rw [cutBitBin]; cases d <;> simp [Bool.and_comm,Bool.or_comm]
  have val {v} (pv : Pivot T (insert a (insert b U)) r s v) :
      bit r (f v)=bit r v ∧ bit s (f v)=bit s v := by
    by_cases eq : v=a ∨ v=b
    · simp only [f,ite_eq_left eq]
      rcases eq with rfl|rfl
      · exact ⟨(passA pv.1).2,(passA pv.2).2⟩
      · exact ⟨(passB pv.1).2,(passB pv.2).2⟩
    · simp [f,eq]
  have fresh {v} (pv : Pivot T (insert a (insert b U)) r s v) (h : ¬(v=a ∨ v=b))
      (fv : v=bin d a b) (hf : bin d a b ∉ insert a (insert b U)) : False := by
    subst v
    obtain ⟨row,hd,ex⟩ := pv.1
    obtain ⟨u,hu,uh⟩ := live_row_difference l hd
    rcases Finset.mem_insert.mp hu with rfl | hu
    · rw [cutBitBin,cutBitBin,ex a (by simp) (fun e => h (.inl e.symm)),
        ex b (by simp) (fun e => h (.inr e.symm))] at uh
      exact uh rfl
    · exact uh (ex _ (by simp [hu]) (fun e => hf (e ▸ (by simp [hu]))))
  refine ⟨f i,f j,lift p,lift q,by rwa [(val p).1,(val p).2],by rwa [(val q).1,(val q).2],?_⟩
  by_cases ei : i=a ∨ i=b <;> by_cases ej : j=a ∨ j=b
  · rcases ei with rfl|rfl <;> rcases ej with rfl|rfl
    · contradiction
    · exact (hj ((passA p.1).1.trans (passA p.2).1.symm)).elim
    · exact (hj ((passB p.1).1.trans (passB p.2).1.symm)).elim
    · contradiction
  · simp only [f,ite_eq_left ei,ite_eq_right ej]
    intro e
    exact fresh q ej e.symm hf
  · simp only [f,ite_eq_right ei,ite_eq_left ej]
    intro e
    exact fresh p ei e hf
  · simpa [f,ei,ej] using ne

theorem tight_no_conflict {T k t S} (l : Live T k t S) (tight : k+1≤S.card+t)
    {r s i j} (p : Pivot T S r s i) (q : Pivot T S r s j)
    (hi : bit r i ≠ bit s i) (hj : bit r j ≠ bit s j) (ne : i≠j) : False := by
  induction l generalizing i j with
  | stop hp =>
    have mem := sensitive_mem (Live.stop hp) p.1
    have mem' := sensitive_mem (Live.stop hp) q.1
    simp only [Finset.mem_singleton] at mem mem'
    exact ne (mem.trans mem'.symm)
  | @unary k t U a ha hf tail ih =>
    have hfU : neg a ∉ U := fun h => hf (by simp [h])
    have size := (cutLiveSize tail).2
    rw [Finset.card_insert_of_notMem hfU] at size
    have az : a ∉ U := by
      intro hal
      rw [Finset.insert_eq_of_mem hal] at tight
      omega
    rw [Finset.card_insert_of_notMem az] at tight
    have next : k+1 ≤ (insert (neg a) U).card+t := by
      rw [Finset.card_insert_of_notMem hfU]; omega
    let f (v : Sig) := if v=a then neg a else v
    have lift {v} (pv : Pivot T (insert a U) r s v) :
        Pivot T (insert (neg a) U) r s (f v) := ⟨sensitive_unary az pv.1,sensitive_unary az pv.2⟩
    have dv {v} (dd : bit r v ≠ bit s v) : bit r (f v) ≠ bit s (f v) := by
      by_cases e : v=a
      · subst v; simpa [f,cutBitNeg] using dd
      · simpa [f,e] using dd
    apply ih next (lift p) (lift q) (dv hi) (dv hj)
    have mi := sensitive_mem (.unary ha hf tail) p.1
    have mj := sensitive_mem (.unary ha hf tail) q.1
    by_cases ei : i=a <;> by_cases ej : j=a
    · exact (ne (ei.trans ej.symm)).elim
    · simp only [f,ite_eq_left ei,ite_eq_right ej]
      exact fun e => hf (e ▸ mj)
    · simp only [f,ite_eq_right ei,ite_eq_left ej]
      exact fun e => hf (e ▸ mi)
    · simpa [f,ei,ej] using ne
  | @binary k t U a b d ha hb ab hf tail ih =>
    have hfU : bin d a b ∉ U := fun h => hf (by simp [h])
    have size := (cutLiveSize tail).2
    rw [Finset.card_insert_of_notMem hfU] at size
    have lim := Finset.card_insert_le (a:=a) (s:=insert b U)
    have bl := Finset.card_insert_le (a:=b) (s:=U)
    have bz : b∉U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at tight lim
      omega
    have az : a∉insert b U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at tight
      omega
    rw [Finset.card_insert_of_notMem az,Finset.card_insert_of_notMem bz] at tight
    have next : k+1 ≤ (insert (bin d a b) U).card+t := by
      rw [Finset.card_insert_of_notMem hfU]; omega
    obtain ⟨i',j',pi,pj,ii,jj,z⟩ := two_split (fun hm => az (by simp [hm])) bz ab hf tail p q hi hj ne
    exact ih next pi pj ii jj z

theorem tight_no_binate {T k t S} (l : Live T k t S) (tight : k+1≤S.card+t)
    {r s i} (p : Pivot T S r s i) (hi : bit r i = bit s i) (goal : bit r T ≠ bit s T) : False := by
  induction l generalizing i with
  | stop hp =>
    have mi := sensitive_mem (Live.stop hp) p.1
    simp only [Finset.mem_singleton] at mi
    exact goal (mi ▸ hi)
  | @unary k t U a ha hf tail ih =>
    have hfU : neg a ∉ U := fun h => hf (by simp [h])
    have size := (cutLiveSize tail).2
    rw [Finset.card_insert_of_notMem hfU] at size
    have az : a ∉ U := by
      intro hal
      rw [Finset.insert_eq_of_mem hal] at tight
      omega
    rw [Finset.card_insert_of_notMem az] at tight
    have next : k+1 ≤ (insert (neg a) U).card+t := by
      rw [Finset.card_insert_of_notMem hfU]; omega
    let f (v : Sig) := if v=a then neg a else v
    have lift {v} (pv : Pivot T (insert a U) r s v) :
        Pivot T (insert (neg a) U) r s (f v) := ⟨sensitive_unary az pv.1,sensitive_unary az pv.2⟩
    have dv {v} (dd : bit r v = bit s v) : bit r (f v) = bit s (f v) := by
      by_cases e : v=a
      · subst v; simpa [f,cutBitNeg] using dd
      · simpa [f,e] using dd
    exact ih next (lift p) (dv hi)
  | @binary k t U a b d ha hb ab hf tail ih =>
    have hfU : bin d a b ∉ U := fun h => hf (by simp [h])
    have size := (cutLiveSize tail).2
    rw [Finset.card_insert_of_notMem hfU] at size
    have lim := Finset.card_insert_le (a:=a) (s:=insert b U)
    have bl := Finset.card_insert_le (a:=b) (s:=U)
    have bz : b∉U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at tight lim
      omega
    have az : a∉insert b U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at tight
      omega
    rw [Finset.card_insert_of_notMem az,Finset.card_insert_of_notMem bz] at tight
    have next : k+1 ≤ (insert (bin d a b) U).card+t := by
      rw [Finset.card_insert_of_notMem hfU]; omega
    have nz : a∉U := fun h => az (Finset.mem_insert_of_mem h)
    let f (v : Sig) := if v=a ∨ v=b then bin d a b else v
    have lift : Pivot T (insert (bin d a b) U) r s (f i) :=
      ⟨sensitive_binary nz bz p.1,sensitive_binary nz bz p.2⟩
    apply ih next lift
    by_cases eq : i=a ∨ i=b
    · simp only [f,ite_eq_left eq]
      rcases eq with e|e
      · subst i
        have pick {row} (pv : Sensitive T (insert a (insert b U)) row a) :=
          (sensitive_pass nz ab (d:=d) (fun j => cutBitBin j d a b) tail pv).2
        exact (pick p.1).trans (hi.trans (pick p.2).symm)
      · subst i
        have law (row : Row) : bit row (bin d a b) =
            (if d then bit row b || bit row a else bit row b && bit row a) := by
          rw [cutBitBin]; cases d <;> simp [Bool.and_comm,Bool.or_comm]
        have pick {row} (pv : Sensitive T (insert a (insert b U)) row b) :=
          (sensitive_pass bz ab.symm law tail (by simpa [Finset.insert_comm] using pv)).2
        exact (pick p.1).trans (hi.trans (pick p.2).symm)
    · simpa [f,eq] using hi

namespace RootFloor

def rootRules9 : Nat × Nat := (0x4e00468704e00458704d04028708a090f8604d00487604e00257604e10027604d0201760d0014f85114050f7504e00186504d00276504e08016504e00168404e00138404d04008404e00857404d02037404e00127404d00407404e00186404d00236404e00816404d10006404e00875404d08035404e0080540d0082f8304e01057304d02047304e01027304d00286304d00246304e01016304d00185304e01075304d08045304d00125304e0040531810c0f4304d04078204e08068204e00258204e00238204d020182068110f7204e08086204d10076204e00816204e00285204d00175204d00135204d10015204e00805204d00174204d00134204e080042192060f3204e00168104e00458104e00138104d02028104d00808104d02067104e04057104e001271181090f6104e00485104e04075104d08065104d10025104e00405104d00864104e04034104e00404104e00183104d01063104e04043104e00123104d100031181110f2104e01068004e00258004d04048004e00238004d00818004e00257004d00447004e01027004e01086004d10046004e010160192048f5008a180f4004e00283004d00453004e00243004e02023004d10013004e01072004d00852004d08042004e02032004d008120114180f10,105)
def rootRules10 : Nat × Nat := (0x4e20568704e00458704d24028704e20138604d20587604e3012762d0014f85305250f7504e20186504e20168404d02038404d24008404e00857404d02037404e20127404d24407404e20186404e00875404d08035404e2480542d0281f8304e01057304d02047304e01027304e20586304e00485304e01075304d08045304d20125304e2440533812c0f4304d24078204e28168204e00258204e00238204d020182268301f7204e28186204d30176204e00285204e00275204d20135204d10015204e24805204d20174204e00234204e2c0042381260f3204e20168104e00458104e20138104d02028104e24057104d02027104e20186104e00485104e24075104d10025104e24005104e24034104e24004104e20183104e24043104d010231381110f2104d24058004d24048004d24457004d24447004e2502702d0248f502682c0f4004d24453004d24443004e26023004e25072004d24852004d2c042004e26032004d24051004d240410,81)

end RootFloor

namespace RootFloor

def augmented := inputs ++ [bin true (inputs.getD 0 zero) (inputs.getD 6 zero)]

theorem rawInputsNoDup : inputs.Nodup := by decide +kernel
theorem augmentedNoDup : augmented.Nodup := by decide +kernel
theorem rawInputsLength : inputs.length = 9 := by decide +kernel
theorem augmentedLength : augmented.length = 10 := by decide +kernel

open FrontRanks

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem rootRules9Checked : rankCheck graph false inputs 4 rootRules9.1 rootRules9.2 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem rootRules10Checked : rankCheck graph false augmented 3 rootRules10.1 rootRules10.2 = true := by decide +kernel

theorem signedAtMostOneBare {k t} (budget : k ≤ 14) (run : Live graph k t inputs.toFinset) : t ≤ 1 := by
  by_contra! excess
  have ranks : k-t+1 ≤ inputs.length+4 := by rw [rawInputsLength]; omega
  obtain ⟨F,⟨g⟩,agree,_⟩ := FromFrontier.groupFromLive inputs rawInputsNoDup ranks run
  exact rankCheck_sound F agree (by intro h; cases h) g rootRules9Checked

theorem signedAtMostOneSeeded {k t} (budget : k ≤ 14) (run : Live graph k t augmented.toFinset) : t ≤ 1 := by
  by_contra! excess
  have ranks : k-t+1 ≤ augmented.length+3 := by rw [augmentedLength]; omega
  obtain ⟨F,⟨g⟩,agree,_⟩ := FromFrontier.groupFromLive augmented augmentedNoDup ranks run
  exact rankCheck_sound F agree (by intro h; cases h) g rootRules10Checked

end RootFloor

namespace O1677

structure Six3640 where
  p : Row
  n : Row
  ni : Row
  pi : Row
  nj : Row
  pj : Row

def invRows3640 : List (Row × Row) := [(320,257),(264,257),(132,129),(416,385),(176,400),(17,80),(82,50),(273,274),(160,192),(448,386),(404,402),(304,276),(44,100),(152,400),(197,201),(160,136),(28,52),(120,116),(131,386),(76,104),(6,10),(14,42),(168,138),(12,72),(262,261),(152,146),(292,261),(304,274),(304,50),(132,384)]
def sixRows3640 : List Six3640 := [⟨85,104,69,120,84,105⟩,⟨148,50,144,54,20,178⟩,⟨308,69,52,325,276,101⟩,⟨154,385,146,393,138,401⟩,⟨232,69,200,101,104,197⟩,⟨278,208,276,210,274,212⟩,⟨265,69,257,77,9,325⟩,⟨306,208,50,464,274,240⟩,⟨120,69,112,77,104,85⟩,⟨194,385,192,387,130,449⟩,⟨38,104,36,106,34,108⟩,⟨389,104,385,108,261,232⟩,⟨262,385,260,387,258,389⟩,⟨101,208,100,209,69,240⟩,⟨13,385,9,389,5,393⟩,⟨321,42,257,106,65,298⟩,⟨44,50,40,54,36,58⟩,⟨290,138,34,394,258,170⟩,⟨259,276,258,277,257,278⟩,⟨266,50,258,58,10,306⟩,⟨133,34,129,38,5,162⟩,⟨176,276,144,308,48,404⟩,⟨37,276,36,277,5,308⟩,⟨387,208,386,209,385,210⟩,⟨66,276,64,278,2,340⟩,⟨21,40,5,56,20,41⟩,⟨98,260,96,262,34,324⟩]

def inversion3640 (ws : List Sig) (rn : Row × Row) : Bool :=
  ws.all fun w => !bit rn.1 w || bit rn.2 w

def deviates3640 (p n r s : Row) (w : Sig) : Bool :=
  (bit p w != bit r w) || (bit n w != bit s w)

def pick3640 (ws : List Sig) (p n r s : Row) : Option Sig :=
  match ws.filter (deviates3640 p n r s) with
  | [w] => if (bit p w != bit r w) && (bit n w != bit s w) then some w else none
  | _ => none

def pairCut3640 (p n : Row) (a b : Option Sig) : Bool :=
  match a,b with
  | some u,some v => (bit p u == bit n u) || (bit p v == bit n v) || (u != v)
  | some u,none => bit p u == bit n u
  | none,some v => bit p v == bit n v
  | none,none => false

def sixCut3640 (ws : List Sig) (s : Six3640) : Bool :=
  pairCut3640 s.p s.n (pick3640 ws s.p s.n s.ni s.pi) (pick3640 ws s.p s.n s.nj s.pj)

def shapeCut3640 (k : Nat) (ws : List Sig) : Bool :=
  (k+1 ≤ ws.length || (k == ws.length && invRows3640.any (inversion3640 ws))) &&
    sixRows3640.any (sixCut3640 ws)

def sixValid3640 (T : Sig) (s : Six3640) : Bool :=
  (bit s.p T != bit s.n T) && (bit s.p T != bit s.ni T) &&
  (bit s.n T != bit s.pi T) && (bit s.p T != bit s.nj T) && (bit s.n T != bit s.pj T)

theorem sixRows3640_valid :
    sixRows3640.all (sixValid3640 (chartGoal 511)) = true := by decide +kernel

theorem invRows3640_valid :
    invRows3640.all (fun rn => bit rn.1 (chartGoal 511) && !bit rn.2 (chartGoal 511)) = true := by
  decide +kernel

private theorem pick_single3640 {ws p n r s v}
    (h : pick3640 ws p n r s = some v) : ws.filter (deviates3640 p n r s) = [v] := by
  unfold pick3640 at h
  split at h
  next w eq =>
    split at h
    · cases h
      exact eq
    · contradiction
  next => contradiction

private theorem pick_pivot3640 {ws p n r s v T}
    (h : pick3640 ws p n r s = some v) (dr : bit p T ≠ bit r T) (ds : bit n T ≠ bit s T) :
    Pivot T ws.toFinset p n v := by
  have good := pick_single3640 h
  have agree (u : Sig) (hu : u ∈ ws.toFinset) (ne : u ≠ v) :
      bit p u = bit r u ∧ bit n u = bit s u := by
    have hd : deviates3640 p n r s u = false := by
      cases e : deviates3640 p n r s u with
      | false => rfl
      | true =>
        have a := List.mem_filter.mpr ⟨List.mem_toFinset.mp hu,e⟩
        rw [good] at a
        exact False.elim (ne (List.mem_singleton.mp a))
    simpa [deviates3640] using hd
  exact ⟨⟨r,dr,fun u hu ne => (agree u hu ne).1⟩,
    ⟨s,ds,fun u hu ne => (agree u hu ne).2⟩⟩

private theorem six_impossible3640 {ws k t T s} (run : Live T k t ws.toFinset)
    (tight : k+1 ≤ ws.toFinset.card+t) (valid : sixValid3640 T s = true)
    (cut : sixCut3640 ws s = true) : False := by
  simp [sixValid3640,and_assoc] at valid
  obtain ⟨diff,dr,ds,er,es⟩ := valid
  let pi := pick3640 ws s.p s.n s.ni s.pi
  let pj := pick3640 ws s.p s.n s.nj s.pj
  change pairCut3640 s.p s.n pi pj = true at cut
  cases hi : pi with
  | none =>
    cases hj : pj with
    | none => simp [pairCut3640,hi,hj] at cut
    | some v =>
      have pv := pick_pivot3640 (v:=v) (show pick3640 ws s.p s.n s.nj s.pj = some v from hj) er es
      exact tight_no_binate run tight pv (by simpa [pairCut3640,hi,hj] using cut) diff
  | some u =>
    have pu := pick_pivot3640 (v:=u) (show pick3640 ws s.p s.n s.ni s.pi = some u from hi) dr ds
    by_cases eu : bit s.p u = bit s.n u
    · exact tight_no_binate run tight pu eu diff
    cases hj : pj with
    | none => simp [pairCut3640,hi,hj,eu] at cut
    | some v =>
      have pv := pick_pivot3640 (v:=v) (show pick3640 ws s.p s.n s.nj s.pj = some v from hj) er es
      by_cases ev : bit s.p v = bit s.n v
      · exact tight_no_binate run tight pv ev diff
      exact tight_no_conflict run tight pu pv eu ev (by simpa [pairCut3640,hi,hj,eu,ev] using cut)

theorem shapeCut3640_sound (k : Nat) (ws : List Sig) (nd : ws.Nodup)
    (cut : shapeCut3640 k ws = true) : Impossible (chartGoal 511) k ws.toFinset := by
  intro j t budget run
  simp only [shapeCut3640, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    beq_iff_eq, List.any_eq_true] at cut
  obtain ⟨room,s,hs,why⟩ := cut
  have tight : j+1 ≤ ws.toFinset.card+t := by
    rw [List.toFinset_card_of_nodup nd]
    rcases room with room|⟨eq,p,hp,inv⟩
    · omega
    · have test := List.all_eq_true.mp invRows3640_valid p hp
      have sign : bit p.1 (chartGoal 511) = true ∧ bit p.2 (chartGoal 511) = false := by simpa using test
      have need : t ≠ 0 := by
        intro zeroNot
        obtain ⟨w,hw,h1,h0⟩ := mono_row_difference run zeroNot sign.1 sign.2
        have wi := List.all_eq_true.mp inv w (List.mem_toFinset.mp hw)
        simp [h1,h0] at wi
      omega
  exact six_impossible3640 run tight (List.all_eq_true.mp sixRows3640_valid s hs) why

def ruleSym3095 (word : Nat → Nat) (tbl tb input : Nat) : Nat → Nat → Nat → Nat × Nat
  | 0,_,_ => (0,0)
  | m+1,base,shift =>
    let pick := (input >>> shift) &&& 3
    let x := packedAt word (tbl+(base*4+pick)*tb) tb
    let advance := x &&& 3
    let val := (x >>> 2)-1
    if advance == 0 then ruleSym3095 word tbl tb input m val (shift+2)
    else (val,shift+advance)

def ruleList3095 (word : Nat → Nat) (tbl tb : Nat) (pos : Nat) : Nat → List (Nat × Nat)
  | 0 => []
  | n+1 =>
    let x := ruleSym3095 word tbl tb (packedAt word pos 20) 10 0 0
    (x.1 &&& 255,x.1 >>> 8)::ruleList3095 word tbl tb (pos+x.2) n

def fixedRules3095 (word : Nat → Nat) (cw pos : Nat) : Nat → List (Nat × Nat)
  | 0 => []
  | n+1 =>
    let z := packedAt word pos cw
    (z &&& 255,z >>> 8)::fixedRules3095 word cw (pos+cw) n

def ruleRead3095 (word : Nat → Nat) (base start a off b tbl tb pi pb cw i : Nat) : List (Nat × Nat) :=
  let pos := packedAt word (start+i / 16 * a) a + packedAt word (off+i*b) b
  let x := ruleSym3095 word tbl tb (packedAt word pos 20) 10 0 0
  if x.1 < base+32 then ruleList3095 word tbl tb (pos+x.2) (x.1-base) else
    let pp := packedAt word (pi+(x.1-base-32)*pb) pb
    fixedRules3095 word cw (pp+5) (packedAt word pp 5)
def signedColumns : IndexTree ColumnInfo := (.fork 58 ((.fork 29 ((.fork 14 ((.fork 7 ((.fork 3 (.leaf [(3,0,508,0,9),(2,1,460,48,7),(5,0,506,0,8)]) ((.fork 2 (.leaf [(6,0,505,0,9),(7,0,504,0,7)]) (.leaf [(5,2,440,64,6),(9,0,486,0,8)]))))) ((.fork 3 (.leaf [(10,0,501,0,8),(12,0,499,0,9),(8,4,369,130,7)]) ((.fork 2 (.leaf [(4,8,227,272,7),(14,0,497,0,7)]) (.leaf [(10,4,369,128,6),(0,16,486,9,10)]))))))) ((.fork 7 ((.fork 3 (.leaf [(17,0,494,0,11),(19,0,492,0,8),(21,2,424,64,5)]) ((.fork 2 (.leaf [(24,0,487,0,11),(8,16,486,1,9)]) (.leaf [(25,0,486,0,8),(9,16,486,0,8)]))))) ((.fork 4 ((.fork 2 (.leaf [(26,4,353,128,5),(32,1,460,18,7)]) (.leaf [(1,32,94,384,7),(35,0,476,0,7)]))) ((.fork 2 (.leaf [(34,1,460,16,6),(36,0,347,0,8)]) (.leaf [(39,0,344,0,4),(40,0,471,0,8)]))))))))) ((.fork 14 ((.fork 7 ((.fork 3 (.leaf [(49,0,462,0,8),(50,1,460,0,5),(56,0,455,0,7)]) ((.fork 2 (.leaf [(0,64,189,258,10),(66,0,445,0,11)]) (.leaf [(2,64,189,256,9),(67,0,444,0,8)]))))) ((.fork 3 (.leaf [(66,1,396,48,6),(70,0,441,0,8),(69,2,440,0,5)]) ((.fork 2 (.leaf [(74,4,305,128,5),(80,0,431,0,11)]) (.leaf [(83,0,428,0,7),(96,0,415,0,9)]))))))) ((.fork 7 ((.fork 3 (.leaf [(96,1,396,18,6),(98,1,396,16,5),(132,0,379,0,11)]) ((.fork 2 (.leaf [(4,128,347,32,9),(133,0,378,0,7)]) (.leaf [(134,0,377,0,8),(132,2,312,65,6)]))))) ((.fork 4 ((.fork 2 (.leaf [(133,2,312,64,5),(136,0,375,0,9)]) (.leaf [(140,0,371,0,8),(132,8,99,272,6)]))) ((.fork 2 (.leaf [(144,0,367,0,11),(152,4,353,2,5)]) (.leaf [(160,0,351,0,11),(160,1,332,18,6)]))))))))))) ((.fork 29 ((.fork 14 ((.fork 7 ((.fork 3 (.leaf [(162,1,332,16,5),(164,0,347,0,8),(36,128,347,0,8)]) ((.fork 2 (.leaf [(172,0,339,0,5),(176,1,332,2,5)]) (.leaf [(192,0,319,0,11),(198,0,313,0,7)]))))) ((.fork 3 (.leaf [(260,0,251,0,8),(264,0,247,0,9),(256,8,227,20,7)]) ((.fork 2 (.leaf [(8,256,151,96,7),(268,0,243,0,7)]) (.leaf [(273,0,238,0,7),(280,0,231,0,8)]))))))) ((.fork 7 ((.fork 3 (.leaf [(276,8,227,0,5),(288,0,223,0,9),(256,32,94,129,7)]) ((.fork 2 (.leaf [(32,256,151,72,7),(257,32,94,128,6)]) (.leaf [(296,0,215,0,7),(40,256,151,64,6)]))))) ((.fork 4 ((.fork 2 (.leaf [(273,32,78,128,5),(56,256,135,64,5)]) (.leaf [(320,0,191,0,11),(256,64,189,2,9)]))) ((.fork 2 (.leaf [(322,0,189,0,8),(258,64,189,0,8)]) (.leaf [(324,0,187,0,7),(324,8,163,16,5)]))))))))) ((.fork 14 ((.fork 7 ((.fork 3 (.leaf [(321,32,30,128,5),(388,8,99,16,5),(168,256,23,64,5)]) ((.fork 2 (.leaf [(224,256,23,8,5),(5,16,482,8,6)]) (.leaf [(33,16,454,8,6),(10,64,181,256,6)]))))) ((.fork 3 (.leaf [(80,2,424,5,6),(97,0,414,0,6),(129,0,382,0,9)]) ((.fork 2 (.leaf [(156,0,355,0,7),(129,32,94,256,6)]) (.leaf [(161,0,350,0,8),(40,128,339,4,6)]))))))) ((.fork 7 ((.fork 3 (.leaf [(177,0,334,0,7),(193,0,318,0,7),(257,16,230,8,6)]) ((.fork 2 (.leaf [(289,0,222,0,7),(257,64,188,2,6)]) (.leaf [(321,0,190,0,7),(260,64,185,2,6)]))))) ((.fork 4 ((.fork 2 (.leaf [(72,256,151,32,6),(328,0,183,0,8)]) (.leaf [(336,0,175,0,8),(344,0,167,0,7)]))) ((.fork 2 (.leaf [(384,32,94,1,6),(416,0,95,0,8)]) (.leaf [(448,0,63,0,8),(480,0,31,0,7)]))))))))))))
def rulesWord9 (i : Nat) : Nat := 0x314001600150005934
def spentSigned9 (i : Nat) : Nat := 0x0
def rulesWord10 (i : Nat) : Nat := 0x8062315280623152229a9972229a9972023a0342023a03421112012211120122a1527292a1527292a172002aa172002a21e200ea21e200ea11e200ca11e200ca8b9281528b928152223a0032223a00321b92314a1b92314ad9caa112d9caa112c12230aac12230aa00aa412200aa412240f202aa40f202aae112b112e112b112031a20aa031a20aa80aad11280aad112012ab972012ab97240aa020a40aa020a99ba001499ba028c01a801a00198019001880180017801700168016001580150014801400138010cf11400b402bcf2949292026a9292026a5174c0ad004c034cc07a008ac07a008a02d40a740074d07c914cc2acd97432041a1c01f4024c0a3422ac42ad0014013d003c3292036c329200e401c4d17401d4b07cc9ccd9bc91549204017408dc005c0304212402349114215410ac02dcf204013001280120011800c5001a0145001a0110e07cf07c3114010802c2e97402c2010000f800f000e800e000d800d000c800c000b800b000a8028400fc016400a0016d003200990032009000880080007800700068006000580050004800400039002d002400300029000c002000180010913d18896331084801b6d1626bd3c8d3ddc4c95626904591984c01bed4e12bf2f8d421d4ce56a48fe5b1d08001becd5e2ad3a8cc01c6cd5b268ee5e18080013073a80e8490a048200e06028100602008001e0e06830160a048200e06028100602008001e0e06830160a048200e06028100602008001e0e06830160a048200e06028100602008001e0e06830160a048200e06028100602008001e0e06830160a048200e06028100602008001e0e06830160a048200e06028100602008001e0e06830160a048200e06028100602008001e0e06830160a048200e0602810060200801f6b07c314a6400700c014020030040040000f20d2c75a51853a518e91030a40a3007a5494593d2ac8154f8c9537ed48fc1aebea249f837d44e2a4c73298ea28f227366e55e0a7485871e165a89435ae30e132f8d444b059f6e110d4c370b343152825f38e482aa86d549668836aa4b344d2b3421c02c19555530094950358e10602042300d857003fb8c4ae2a59a2518441927e8ae5ebec31cb96f439cb96f438cabb14fb8cbbd5d0e1e5ed2c393d1ee91a7bb34ece916ec574bb3a26d318994e902dd36399d255d3b064ee911de83bedc5242a28e85ed0e3b477605cb6c936fcf6d6bcdcacab65a73245bb2d0959e6a2cd196c4a6a33232d884de42871a8dc1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def spentSigned10 (i : Nat) : Nat := 0xba31361680088000e14bf04005e040e00008001c000e0000
def linksSigned10 (i : Nat) : Nat := 0xa0800284000004000000c1400c040000000
def rulesWord11 (i : Nat) : Nat := (if i<2 then (if i<1 then 0xb40d7ff71f8065ba3875bb4668c7cbd47c763c05caa3b23e51c3fb4519b8fa45bf4dc9c0f231e89fa1a6f812f8f963e9faa868fdb47473fed51e9d6d51dcd39fb5b3973ff0a3d3ff7d26be95e78b74e3ed6ce56473e868fa69702816747e71f931f47d348e2c7e5a5247171fef73cb93774f8fcfc72ffb5dcdf9f8f9bad7f0100cb6f75ba8fb29db445aeefbceeddcd9788eeebe2d446d7bf3b1f0f775f3ba5cf73659dcbddc7b9b9e5dadd9db7f5fcd46118b6daed6f9d8f4694eebd6f8fce08fe1cbd7a8f6d37a2edcd786dfeb6f9d8fa61fbb377416a5ebbc5e9ddd7dae7af7778ba32f76f76aeedf8ba2f797afb5bb774f7369cbdc3efbb735deda6fa71ebddddbf17cf2f9aed476bfafdb5ee5717b7754e70f61d35eea292938dcfbcd3af167a692bac685fe73ee4da9bffdc6bca3d5a2eb3d3496342ff39f2f736e5ffb4d25fe5f2fe7fb797dcf153637e4bf574e7838a9a4b5f1a17f9cfb936a6fff71aad47ab4678a0e9a4bee37e42f9fb7fe28393f90bb68fbab0dbf7d3ef0f7dd6e9af322c24d5aef34c526afad779975e0e2c24d5aef34ebcc8b0aa4ebbcd35687edfef6f3cc30ffbedede7af267c2655c73aee6de78a4c35eae39d7736eef149afc7356ceb870714986bf1af9aae6debc59e4c2655c73aee4db8364df3ffb99d6d7e21ae4da4fff6abca3d5a24fff6aeb51ead127ffb575a8f568fb9e292ae6efaba7ee78a4ab9bbeae9fb9e292ae6efaba61f1869fe876f686da21f4fb76fa63e2abf7ce1f69e987ddd8b16a1943f795dbb0e667930ab9d7c4bdcdbcf255af8e7ea5ee61c1e7930ab8e75cbdcdb999e4c2ae39d72f736e6ee0ebadd32f90f5d6e92ffd930ff2f96efd65f93ebfcbd148782aeb74cb8baaeb74cf14c930fb573c6bdbcf77e2afbcc375d39e0e4c3ed5cf1af0f3c5324c3ed5cf1af6fcecbaddbe9b78bbceb74fb9f16649871ae5f0f3c9af8fa97cbf60f173c9871ae5f0fee2e799261c6b97c3c430869dba7c19bf5a77079ec1ab6c9834edcb6b2de38fd079f05b63c3647eb459dfe9d41d3ae2e5a6f64ac7d3a9e1f0554fcaec8f4e8a72ba775b79d3b1c7eb6f3ebc1541d2765a569e9e7fdbcbaf3fedd39ff6f2e7fdbcbfc5c749e78b68ff90628393cf16e9ff171d278e6da3fcc9593cf16d1fe293c73d6da20ffcac9e78b68ff3220c9e39b68f03607179fa3b40d3a23dd481a7e9db97af01baa7eda7970eeb4edd32e0edde822d4072d5845cfee9e5ab08b9fdd3cb858fad3d2c74fadba400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 else 0xa0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040091ca1c67939b7d5d2534e3cb4b6d1fb84d10f003b00e803900e003700d803500d003300c803100c002f00b802d00b002b00a802900a0027009802500900230088021008001f007801d007001b00680190060017005801500500130048011004000f003800d003000b0028009002000700180050010003000800100000dd416b97bf3720b7beaee9e8ff3fb65a6f96fd2f869bffb9dfda52795a806416a01f7f2b5e161e9bf7f2f7fdfb3947fdf40e56ff7a412ff7ddf29bb5a56174d0b21782e5d8f8f977682ceffda537cb81602e033ed3f8df192fb6f1e74feb4f1d7a77d9f1f1495f5fd855c73afb8d3eb8e1f50dcf38c9dfbd98f8e3ec68a7c96c75c7e786b1fa86963cf98cbe98ecd2adb39f8c74b7e18fd4bda78fad3e09bf3fa377323f00e78) else (if i<3 then 0xee1a1c06480a3184a01c400a90aaa03d42aa80f5a729ce569ca7394c72c03131cb00c40dab889036ae2240e50082010c045806b016e5204b128079016a031404b98292cde00cce40825ea4b9097a92e5c5d400d317500348549155215245540d28114034a0440086053a02100418082010001f803e0056807d015a01f428cb8e60a32c2e802a852200aa027a00e8092803a03d0078402e6114a22a00c815580320554454b94a115203b0074402a016c143807200e001b8036201280b1804a02c406a00d00198032006200c0017802e005a00b0015802a005200a00138026000b208a429c255908101410b9405040b0b44902c2d12442b303d3894c0f6008994a802282980d70094012002300440084010001f003c0074015401c0036006800c80180481005c00b00150028004c0090011002040160078253801c0034111402684a508a6804400c001600280048008000e001800280040006400500110014a4224550d000a32729463f875fc769be675754ccf631c8e19000d1efdb3a9b9be45861e96d9794e8e12e0790fc00abe8c9b64c825eb7058f5a147448e42c4770f400f73a2dc731bb6bc9d228769985610e3008c0ac00edb57c6ec3a32708b1cd6413a404d72b8700fc00f8fb2dff35bb2a79760c6b1744ed023108612000e675ac02b69c626771b462d5846cf23288210c00cdf0eb969f9ba27785b86114a460e02dc680b400bcaaaa427095a3c819c66415b4a0f22e8700e0003b4ae1fc500b40a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0 else 0x200488f5801223d4084802102120084006811d001a0474826914d209a453526ea05549ba815601a84dd806a13740ba816502ea059541ea955507aa55425c81bd097206f48de9055237a41550e0a8a54382a294c528cb9314a32e4a5c884d297221350c49199431246640cc8171033205c407c858901f21625880a0156202805409e8035027a00d522489b9489226e403aa05100ea8144878803121e200c40ce80d9033a036447880f511e203d4e5c8129397204a5a6e904169ba41040e881c103a2070505ea031417a80c4828801920a200658a481c5629207140888131022204c48468195211a065527290c549ca431481e84c9207a1324044801d01120074022817d008a05f54a5108a311405380c704f559cc13d409c88910272224408c80590232016402e815d00ba0575054b4b94152d2e5c24a0917092824405080bd014202f40d0019c03300651c1ea8b9707aa2e407ea14901fa852565c8cdd597233740c8018c031006100c0017c02f005d00b8016c02d005900b0015c02b005500a8014c029005100a0013c027004d0098012c02500490090011c0230018800514e6026c1398625284a39bc0498a25))
def spentSigned11 (i : Nat) : Nat := 0x2e2e200048f0118207800e00001e0000004015031074e6010b0407c000ff5eee00c4403fa1a0120830f9190804400088003013f3800bff8b6b8b08100100100000fa400400004021204400010804080010000390802014000080c000000820190000100010800000403ca0000000081000000000000000104804080020080000c000801008005000000000
def linksSigned11 (i : Nat) : Nat := 0x520f0a31000018126843c00d9006a040113cd0420000085c000000002021b055000000000000480e684ff817e05c8d5fe81c80003802080ca029c009182d08326819b0012815f1455232043df02e54040833b84c001fd85130281256c03e400509d4e82bb849e81930545022905e70629215182890df802600006857d25ef863c83de02ac00ed00f181c481400000000202080000000000020df0000204f0813b8462036d80ae246c851c830781ae04100000000515d00000000703b083c0000000028030000000000000000403a0000183b800040447833444db05b8000404a8000381ed05fe80c40531841c000633e301700000000553e404900002038284b781f304bb85f79020000305d0000000040188000320f80005860000060565a145a567852b84e0000382d9858b35d6055801280000000000000000000681bf0082801f811800020dd00000000401b683ce03eb84cf05a42a68000684d331d5046b81e203518099824e8364844e8398000404090244037805aa82ea000a859082c902fe01d200a28431830a006681a385d80000000184500005835800000000000000000004004b023c02c0000384a00001003b0102815702f0000784d8000300bf060800000004838f8538000382140470000785080002232e052185830599210253f000050070000683180000000000000000000000000000000000068348000000000000048800018278000000078428000180280004011003a800d205b000000000000681d80000810800000007dd480000000000000001a2e2231a8167808a0611031000590620861d016c056e33d80005022582940483a14e013402010232045883f8814993f5818202b100fd25c74bd00003a2d7c4e000028270000000000000000000b000045de923d3147a0501a548032c8bf9cd49233186372303047804ee8be483708577839403d202a702548346825a007800000000d0b084841e0c581325851600140000a3c00c300860006102800428101005c02b1a302030a10282000050308000800000283000408614241070000004000000204000030000002
def rulesWord12 (i : Nat) : Nat := (if i<2 then (if i<1 then 0x8577fb3bcb99cf1b257ba730f130561abdfb6f1eec3f28989835fab9bd8caf75bfca25eadd57b5e30784ad0e1cd0fbee72f9a4596f5d343ab398705af8eb1daba57ceafcf1e4bfb4c46176dc4b9f0d2df6ac7edff4c1ad12e78223fa0d6d3d5a7920ecff06b4a587689cea5fd66be26bbc7d58ee7e61ef2f0ebd1d907fe26d5efe9f1e4bfbf3088bb6e251373a47ef3bdad576c9cbbedcffd239a0c15b1e229f0959158f2e96f1e0cd07fadc9e7eeef35690f61ff64d076effed90ffeb41c3b53e10fe3d36ed8372e2b63cf973ef586ca1c6b41869cfcd226b2dcfc7adf9c441cfbdfdbbf16175ffc9ef8785d3062e8dee4e737c3e26d71abaffdebf3fd577de69bdb5f79a6f6cbe7ae96cbc7d3062daae3fef4fce8f2f1a75bba1c9ebd3ab7627995ed20fffde989ef4f8f041d26ff85de9e0e7eaad32b6e0bae3396fcf053598c67d6555defc3eb85938d59a0bb53dd9b0b8c757ac176c3c2e26e558f5bba37c3c2e3adbfb9b7afe60e995b2df655aef184f7f7f7ba2b2bbb7ce4eda7d333fc82d26ee16d3e1e3bea4c1a2de582f15b1efe4e18dbb1e5bb5afa9f9fbafe583d165f718f6efeff17a0c1c1f76615768d3bf0e4f3c5e7675aedcf4efbb1333d313a4ddc2dafc21fc7a3d3a2dd278cb056c7bf32c2c7a3836e6cb056c6267e741d38dba5585def89cfdd7f2fee2ad10f6718f6efe4c1d3dd668c2ae83bf089c65fdb232e6baefbeec4fbbd498364adde8aeeee60cba77c2ae26ebcebc4fa56d3f137e6bd23b7b4adc3b17e4dc6aeba1afbb371d7575d0d7c26f41e4b63ff60e73c6737f57a560f1de3fef9bd0765f7abdfb661dd8fad1defde7b3b3bb1a7bebdcd9dd2beb3fcde9583d78d7e279bdfbaf1aceda7e7f6f41db1fcdefdc4d7567aebf5284ffde1e3f3b987b65e773c5b2e3fcc7786d8f8fcdcfddb1f9f9dcf5b63f33c9e9c8b1791f2ada7f4f25cac591722dafb4ed8cf731ec519ee47ef37d25e90fbee5e64f0db2fd391efa4bfbcfda7a9e594bd7307655b2ebaee9ff0fbfacfd1475871f7f58f1da6f2e3f79a6f2f1bcd37979f820b53b63f3f3b17083fef5f6ffbf2effdfd62ccaff04dbfab707fde5f31fb7733f160d378fe7456ee67d762e983fef5fa9e5d16e6bffbc3cbceffbc3cbfbc96ee6bebff7975d07fef2ef32786d979fc75f379a6dafd723dfc36c7c8f4ded979f9dae0ffbfac78df7253c91da5bfdeb91766de5dbfbc77979dbdc67378f8fd86ee3bc7e7e75bbbc77f51d36f6cbc5bb35bbc7ebeb6ef2f178ded97cc74d6cbcf7262e922e45beb3dcf6000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 else 0x800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e01802804006008008008c65df262a14593c08ba6235065a0f383100c002f00b802d00b002b00a802900a0027009802500900230088021008001f007801d007001b00680190060017005801500500130048011004000f003800d003000b0028009002000700180050010003000800100000e5116f3fdd6cd2730ecff938e2b56683b4144d34a94e4792d9acc941da25f9c463e139fd8f6c709c9641ff5a0ed6961cf8f63cbfde39bf3fddad13b648fef61efdac2ab7fc2ef9f3f6f1a78b268b4d9456e592bbc72776a87091edafcfbf4a94f1f49a0f6dede7cbae0f6ebff7afeba74de863f2f1e2d7a7ac95feeef139cbf962e26d59b543ae26164d1058f6f58589dbdedd1ebefad614d6e27a37b70e0d5aaca682df396a2d44e136f7f5e5cfb26e7af655fc6257f2df5905eb86892b1bbcfcd7f2d9c5878ac7cd5f44cfd7f2c65e2a2bd2bbc2e193c6ef272ebb39b359f37682bf8f3f3c58bb6ba1f57d05416f5e76e0f0c70f3f05d357d26b1e673b759de7a3bfd9f1ab1d1ad1de95b7dd863) else (if i<3 then 0x11a04e81be00381a622e81d213d409d13d409d02b41b902b41b902144dd02144dd80e40b180e40b1005510100551010134449013444904d013004b012804901200470118011905601d80fe03a803a27081c2464a03e06180c2253414125341410450110043010804109be04009d203f00f803d00f005780a22738952073408d073408d06241010624101052406d052406d60f40ec60f40e801f807a808a01a80c883e80980f66128901039090132e515632e484a024408a02440e0640888912e888903700d803500d042260154226015033202a03218ba51240c451240c002f14e542a94e522998e501498e50584955058495542e802600f8cde026a012537819a053602d053602d80740b880740b402c00ac02a00a4028009c026009402401ae023114a03b408803b48aa0210156020007c01e007402a807001b00680190060652903e017005801500500130c4a01200566228044010003c00e0034339894a00c14ba00b002800900200070018005001000320050022005a2931a183d7708c813f2223d4700b811d1d62e0360009b11fa14bb36b8ca96da6a3f66aca90f815020c1d0009d323e2f40c766d497ea9c4b27ccc91521f82a028000804f21c5b6a694c1d4aa534286dcb51291c426831000a2333232423788d8187ad14c2850e11582142e42080062ab655027347c84cf09b12da4ec800bd12414c11800562a0d2c22d3be66cbc956264458788cb11c1a41b8004ae8cd091e33545e0a292420e374600860c81040e8004d491d111e9378668b494f2363e06b0a90f81281480013a1f02d85103a04c0480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c016028048 else 0x32a80520500841f85105268134159813415913c458913c458946b518546b5185814510581451050334069033406902d405d02d405d26e488526e488523148bd23148bd0544031054403100d400500d4005063446d063446d2434539243453962941b162941b11724521172452103540490354049004417900441792414059241405906a41b506a41b502e604102e604180d509180d509102f40f102f40f11396086139413804150510415051215819e41288e60298))
def spentSigned12 (i : Nat) : Nat := 0x2000200000000128bf02000010000000a108100410020f02024000482002200810400804ff410200802008080900801080800881080000202001000100082040008811002ae81a404222f1080111040488048fe50080808804090400802100160108020108880084040400000408107a40000
def linksSigned12 (i : Nat) : Nat := (if i < 3 then (if i < 1 then 0x180464417ca8051902c700f6ac08700000000016aa1b0015e80a1506492ce83c200700c1d201ac0e64a49e800005473a2094c0007203a3d93f956a7300df40002c08ad610f800000000000001801e00000583d80350f000ec00006217f0000000000000075bc900001a0a5a412eb01f090268681d140c880000c081e80b68d22a5bae09022a0000380db2a91bc075f40a0800002214d00000000000000000000000000001820b00000507e00000281a54a227e06c6468f8000000000c05f400000000000000b049fe0c2cc0d79c456c037e000010156b8225100d880eb641c6e82850000000003c11860053e020200000c20480000b04160000000000034e20358a0e380000680e0201c3e03a1154b981868058aa028980064834500001e4eb8402d18445a18710099500d68020700001e0737c0f0e01b22060cc0a5180770817ce72ee206f401b9d845ad01b7c8e0c0000448ee8004a2817081aad3ab2002040000000000000000000000000000400b740748000000000381692076560efe021b583c800001605224815983e7d20076009c40f1983f10089c00002a4b5fca721081580da500dd8820d90400684fd01cf8042bb06dbc2e2101d4d84070472c000004459480a500000284580000003b400001909209cf8c8008204ad210c00000401f1304f0e00d5edc4e215300001e08b1401f203c06418d200abc1a9f42422048b0c2ef85d73c9004021960a4dc109901671770c0000290a8ddabf80754607240000202d500000000000000000000000040aa4000000000c07000e44c00000000000000808d140ad80000d02c0a00e800000803f0000000003405c8000000041801e1800012000801e197020c4c7001a1c2800c264000402e8206300800808d073800000081008904005800844a040000a054205201000030002001002630088280018004001003e1cc8c0c2408116000080e00680001400e1809507000050d040c5002e0069f2c0028900109830201f803430100020060b02243800008404140830706100800000a850200201700058002019803e002800214000061c180321000a140000002001804000b000600186180400a020840000001800c005802c00100040c5001a082002c00480220c10022001810228a800a0000106286802400180022408300089810e00b000234500020029538042000a00000100010004144800a10100100060000002800e04080000cc030e081070e0c0001a040000008701000c5030600303025c1950200780020038000082801800100000028000006800000680080078000381801c00500160028006002001e0008000003021a00200020018000240020a044000a005800000481060000104007000e04381242c28d16002800c01901000c504040439822000010408a80040000708001060c01300 else (if i < 2 then 0xc0c42ed5f0000000000209a681e780000800ae00002005a649206a31800000992428197c02a860036c1de453e4003aa946680000082615049842468406182c604027d20b0c00002218400000000000000000000000000003a440a01b729015c07df80f4b03d0000000000000006022b00000000000000000000000140edc000000000403b200003400b0810b400e40000181407810000000008f000000000000001a85240000400ce00001c049400001006bf010a00000000078325000008039d58c948288c92452051b020f00000d052340568808c00000e04cc8047d0060001c380850a0cfb9d52303fc300de000000000080612116da0cdfc09af83ea4875a00000000058244000006e040821e700b500001a0c7000000000000000a2e75c4598000000000c105511cba846100000aaae94188902760000100cf0c9d5d02e5c04da8105c0000583e10000184e19409900000605efc409fed19b01f940677003af012a48279548462ce7bc46390161942ce6e8d500bfd02b36a72ee08a40218f80633087a228ca24b07029df072c00000803e9b17c5083a6a23b448dd004650766000024146603c4105e4000000000683eb0000000001401358043d046a40fe40000000006061f810e8000002442005da0062280426c8f4a04cfc405c0000000000000120b6000007830e0000000000418400000f0339e48ef29d2cb92700000004dae49c30440003a18117cc1670000000000200ce01a7b094300001a0263cc2f00000000014f0c9008780087c087600000411d00000403fde11248071200cd803c800000c4b7100706003c68c6a0034e82e920398000000000241920000180ade402800000f021000000000060bc7552f000000000068060402c52111281ac88193000002c9cd40f39044a7474e0000201bec8397000000000000004801fa045b605cdc1f280000b47fc00ffcc219e00d1100fe60749c09e7bb85946f680c75800c00000902ada06e8c0b694244d008ba007000001004f2025000000000000000407eac04fc0041701dcc00500000245d669b882604400000000000000907354083064b1bbaa200001e054dece2e809fc013a000000000280f7807c94092e29c4e01bc50362a00249d1b603dda073600000c0f7800003124b76af0000000000f05ac0014800006018e606c8c062b40a8800007074c0000000000216ac088600425810300000e04fe407f1816430332000000000000000000000001c4df800004a17600001c0c16410700000d02bee808100d738322e001720068000000000a013400000020900000788a8000000000080c2904b6009b8013a800003045ec07bb109a80000742ea6094440f2800004884aa0c800000000004028060874c082b02abf077dc016f4231d83e6607d00090d41ff504233470d802000000300dc0 else 0x901fb00000600ec8049800004830000000a11608930b03460000080b93c05e421501032130a44420680000d07c0c0e521d34b3a3f1175364f8000e0180d7302aba1193c195208af103a82100880b8181a7018a9c07b6823178038e12c2401500000403df106915671801db582fce464720d88c0c1480ca44302a0ef40000000000031a00000000063b280000000003c144801c89948a81157414abc91dd07aba087c011fa82d43074a503e40000080970000000003cc3f80000e02aee0d028197a82e16461f409ebc011a84324009a00074000028006807021403a40180000000000c114f01e1f81d744565800485c5c984135462d2edf341484026421247e0a35c227d804900000c0b7b5c44a03a700833a040e80bcd0441706020000099d641b96a771d831050000881e6903d6c068941cf28414f07c48057a8052008b0b055db087c00000000000000000000000000003007800000000000000600caee46201e6e03950249d031801d355004c7039562583c00a13b2710561406a5c0fb00000e06d1c05ef59c4082dd504c5a1174000038426300dbc0c1c0000102ec5019000001021230352f05c4c00808045801270000000003810a800312045c0000000a28000000000601d465bd8000000000c0840000018241406ca00001c1bb00000f72f400001e49e0000000001e0de8c19b00000802b36eea000000000000000809d180fc182489021442303594f20367d067562ed40000000000000060f2a41ec80000505a32ea8c00000000000001809be00cdc831a00001e0db1017a882cf2a84d485bdc4937017100000000021c907a39000000000000027000000000040a8c00000000000001c001000007033f70370000010054700904068e000008179b393b505cde012c0000000000000060fc800000840b000000000059c9e00f6f074210663ddd57822ab01c8000000000608dd0000000003611e80000f061b4001f80a813aa10000000001413400000407a5e034800000000000000a041cd2158013b507ae00002410d80000600fda047700ef9017e2051f2076da48fe0379e8487d245018d8bd9483020996e4441c20000010667a0a4882161012900001c048380a70bb2a506bc00003413d8000048472ec90b817f000000000100ba9946038446eb720e00540000000000000160fdc000058c27000000000240112045e40844e106b5c55b092776853eea820009f83efc0573a0b1200f968408f011400002c056800002013980dac0000689781028600000000010144a06b60000280a0882231034a00001812538247a11ac0000280ce8845200000000018077d81e80000000cd681dde00e630103802ff247fd81876026620d9bc14c71397a066100d3380c4b816c707638094b80e1081b9301d8c6222808a502e8301dbb2408c0028000000000)) else (if i < 4 then 0x49825ab05480045a81382844c80350000024112282ca5588e0088081b8f836e7054e00001803c80000000008107fc05d100d4c30e640dd701ce80000f05a04033d00ae103cca0170808a3403dd8358128902f124000018250e739d00d35c929400425202da0f040000201ce0000000000415a80442d036bac8e7c1ab3811b0051d6028081c508165d0297802b0000000106c05f720b6e011c2c389d017d684200065d020492702a860e51d0f02815044c20cae6221b1018e079700b05991e8825f00000c016000004834b000000000100388803200001809f59c7f480e9500220065800000000000000a0850000000000301ba000005921a81cbc648900e20a61cf01660770440c0c00000000000000000000000000000000080aec00007c14300000e0cf4000028317b274ae90ab006281260b081840b2440fa5814c2040580e828055402b10000160230818d901d6000018492c00000000000000002f61839601cfa02380000181be00000000000000340cfd0420c92a16083d4054b04270000100279420ddb90ec63f6eedec0000000000000000dd000005030c000000000341108000000001800e4000050326d059b961768185202d73723e0000150b9000000075840173c1bb800000000000003c0c2800000000000002c20e00000000000000000000000000000000000000302ff00001002afd8fd0028bf0106a0340c1d1580f3f042e80cb7402a80000000012f0d400007424a000000000310a50806a4b55800001816cb821e2043980e08000040421b04fc00000000008331000000000304a44002c000008c614807c0000000001e0041007f90059305d60000141d720319604ee40776cc48800000000000000003e0000000000a034d0000000007022600000000000000b0080e0da80000180de5a7be2b10541e76027c7a37a40c6040cc800000000020e1b41f6302f810668c096681b96812ba0318e10de41a080077308b30249001938000000000811408cf86212c703020000000006924f20659810a9ad5ec012ad0672804e300c598460600bfe0909418ad0349a27ce00003c216ca310306288000c00000000040083404c4000048064075a3c07cc00000000000000000000000581f52065c2038c5c648000000000000000000281b0000018c53a5888000000085ca053e4033381a6f06de000000159508d9e00ba402ec00006816ec032800003008960096778b680924c01e8000000001c08c7c17000000291e7b4f80c09780000907d2000000000682ef4038860d80c9ef80000b05e2c06540000082aa000006497c0000483ba00001a04880202a81aa0000000000adc400000400880000000000000044842e0d70c0f600000607180000104bf2893a90198000031a11000000000000000007e682c0d0569e0f50acd3b80c4203b4f70a else (if i < 5 then 0x4026c000000000d004283098000031250f05dd08c5c00007817a705ec6035ac098000000000160ee4000000000f7646000000000100360000000f79c1fa00000b01240000000001037b00000000000000480f9000000000000000000000001c0120000000000c064200001c1fd0000000001481c7420c3842f5078c000011d4fe824e5034760aa381a25d386300dc40dc28039e825ca0249ee86a892f0031f2232d2eeb3404a000000000100b3181c4800000000120d7ec16e0000000001202d81dd3783130000040fbb41b0c812d40324000000000404250000000003640050239c18b2e0ea0c0ff89890b04114031a4007cb945101fae0900c11de818300000000000000703f8712a8000000000002d2a06fc00003010b41380902e8000000000380e5401b00000001418db8f0000024012c053200fa10605a00a541fd80000702fa4ce4844c06808600001005aa014d9d1a06053e2e4b98063b1426592733111e401bf03c2d070b4082b8203303f300001809b2011bc023d00000e04b840bb000ae2744424f3dc14d0000000000022ff0173e82fdd07ac62ec00000001d1e03d4606ac81658000000000e0bd3113e3019a8067154e47c0bac01b358343440a9020723944e026e80956c21c28219b03c5c6ab0000078378000002047a021a001de000002e5a1518a90024263fbc00b80000480fec00e900863c201fb8efb04e4a0ff400004009900000a080790a9000000000140c7800001a31400000a088b006ce028a00001606808169d01210000048424c2149214b60111c116d01f680000e988d4101180a100000990d3e0760017180000e04c000001c926d0158b05854024f41f1d937ce0036a0686813890383706a2803c641e9a82460674200002481600000f7298c02bd990fe02a02014ec254b002b0b1459078a4095d1d94b04355038fa0b1ac2008b87c8028ec037c00001a42d4089000d08400b8000000001c046ac191bdac5d1151e019d81a8702a5771e1e0a134088e83dba0162a012b8184e843f942e1c0a994113d03b500000000000000402af8011f4c7fb0182780a3a755920bc2c22bb844dd038d4036b0135c9be40000000000c467c8203b0368630dc000000000841f4000000000700f27056c0078141ad382b8107a22104220bef018fa01d522577c0a54019e4005ec8f366a18e922100000a0d5e80e9800004012a000008102b8299d06fe44e5840d200000e075600000000040387f0730000d2c1ee7925c00001606600000483b8808a920d778064e8211824b100227c08ba84510000000002c0239418200000e05acc1639020900001c0707c208d00d5f911bc112c0000000003a6f8e0c48000050123300c5206108086f814de71fa00003010900000801eae409b0016d045cb088e00001c0b200000c04c6c0e2d061 else 0x150110000000b7f412c000004b2dc00002ddcbaa22620652001a3a9d480000000000000000004c3885003200001c1aa080fb00001604b3c1ce0000000001e89f40000000000000160d0e003d000)))
def rulesWord13 (i : Nat) : Nat := 0x37b0190dec0643820d10e0834413218904c86243221990c8866404a1ad01286b604a064812818020d02102940840b805802a02fa03b02980ec0a41ec8a50e9229606a05581a815497210225c8219202050480839807a14a01e81291ca089472822417404c024011117300545cc016064849049212414c4de817010007814e81d405807003401800b08944e64a52228050024010007107c0aa0ab006002801000600236bd4b15b668d95e357d9b45e13c414d0240460031ebdab2a02688d5fb6c9784bce728c8b154240027190613785b9649694c50d370ad2004d0c8180004b118410f0370c82d0a023078190500f0280500326ae90a0003abf7e24dcdc10052bc5fe4a7c441d4be2ff37bf2b14d6a7dfc96ae086ec27840f26aefe378851bc3d042ad5a9ff25bc9d257a9e3aa8af9abe597eb531ff9bf65f8a6bb540e7e7f35166b33f24d0e378e455a9f14be993a353e2fb7c7bb7e26bbbd5025ec13e9be5884cf6ed7135ff8b08e1b981aeab47f37cb380e65cef116b0ee717f434edbe383617b3f1d2422d0f400d3acff7c34845a785fd70d3b635a9f17f922ec1bbcf0857149bf9d56f7a232f67e5b3cb6ba761098eb3f23c76db6de10dcca3ae23fd6fde106d8e00994fc8ef7cf0376dad31f257d732b17b79ac59e47785a58fe96e7c4d6d43fcb30535b163fa59b481b0623be789ac3fa5588b672c77ac45ac5f7a50dd184230f5d3189ac5dfd2ede20d9c71defec4d6c58e32fe26b62f07f47b481b7c038037749c0da0e004a5294a5294a5294a529
def spentSigned13 (i : Nat) : Nat := 0x4000000010000882
def linksSigned13 (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0x5a4ec07c000000000a07fb40a400348000000003d4f7000000000000000000f0c25005b89100c16f3037f40dc00000c04900002416ab0679817002dee8369000018333a061090b690e1d433d300640000d082841e5767f40000a0e30423dd065b401f000001c08300d6c082403e48028c17afd339ca848c178a0d1c000000c6c000000000c2bc80c88000050a53822b70089820800001117df0762806c00003889a60d8c0000000000000000000000c034480040000000000000021b2000000000a0a80000010270000050caf9370c09c202b850092c2f500000426b000039e6e00002408480e2442b1b0e100000e080fc0210000182df00000000050e06824a707fd5cba000008112705540000306d08157000000000009400000000008273b95b2c28a00164c2bab3351677f002ff00cee0b7200fa6018e0259906329c0ad0378434520708023b000000000600e80000d08b25f55e07ab01aad0c2fc31800000000000003828200002c455000000000901c800010000181cad081a0161f1c900000000000000000000000000000000b04bf82f2604edc2d2393cf43ab00002022f4005c0000406f3c05d80298db00e05a642660000282791677841ddc091dc14e5089c0000972efc0230000000004006add2ae072d81f8000011c1450a9b6b954078800000000108aa00002806400002407300000000006bf28015106232cdec2df00000402840000000000000e01fbc37c00003c0cd206b980d3d026d2f3690e98c0760041f021e0000268ea00003c2b450c2aa372000035f3d60b16a5a80096901a200000c29700002c36c40ddd80c2f095800006036d4371b01d5811460a2742eb101e29f77000010088d0a588006104aa00620075a022a40639437984dd9425200000000000000000000000c2688049400002b44982b600000000000000104000050a1200b80060168c0404100a0181062830a0018089871a0049dc0000001200e800400c801800001060000506000011e000000214f00020000306000000200b810a003830604180200000a1c04a0014046000c00307040010602008010a009000600980280010094002000600180040c58a02004001e180070a0028e001c10200000021e04e800e0400004103800000201100c08000047801e0018000002000200181600c803020000000002002c00200000ce012c001802c081002e0410034582152800a000a096000a001801404d000000507120400008102800000200040060108040000e00000006800000001011c1890322080010c082800000001020000f02000040c0c1800c8c18000000800a006811a00d8012001000601a001a002820200780021000e043c48024000800c2c28902004020001f01184c380260428304081800e1cb00120400008281000c00100760008008000832c01585 else 0x8762a01404731a0cd6c13a604c8000000002c276000000000e02ce9334605b000008049cc32500002834bf0dfc000090404000000000c35ea047b60c220d40a2558aea000000000042f11038c0000000010103000004237000000000000000000f0d11435b300f40000901fc0000d08089f260000000004639c00a9000038251608cec1e4c0d93423590128c13de09b9d2bad03ce81b3a044c00d7f0e0ac38368dff818f60d98ee60000000000803d0dac200000801c411055356b01aa9b56c04c0000000000000070049c1f430c91826c00000029800000c027000026380e0d700000b0d4740c620e9d834e00000c39900003c319a25dc0000000034218000000000d0e7e41150000282e9404580000307340000101469a68e0278000010635c03e1903240b5106900000000019c034038642e4b03a280a0b076d03038066801dce0a480000646e40000302040000a0133c0cc70268016270b39c11110a15411f2051d01ab60cfd02f3000018086606736555a08f00000c09ec0000000000000902e842100000360f730d03808c10cde8108007248329db5e60002d053c417cf05f5e1cf10d3d82a790172c2c831dc38220f0733815e20063c03740b46e8d6d00ad802500661832c0000100fc00db880a5f0410c37bb03560354600f204a579006c13fd0b58000070dbfc374000014258000000000a02f6436500003c0900000141d23718c0000806c70058a83cc000080b6443070000000000000000000000083af4042d0228000020e2909cb880fd083c8c0f5206d740bb0000182a551c8ec0b700001c2480000310a857242004500001677ac8de4812612e5400000070441190000000009073d829be22df80d8f01f541bdb0a20000046205033a000011d54c0cd2429f083c40000b08118065915fc000060833827d45e71c1f1b01b6c1e1f0b53c11800000000050e01428710540e4b2302440000c0b880000000000000509e1008b00002009700002e09d00003446600001dc64f03bc428fd971580b1402bf813c00000c27700000811c9724501afb5e010066d09e9c21b309a801b700000000050d68c22e00003c06b5055a8016b0a1382cc21e81832100002836000001411a0000003acb0db6414dc0c1980d0d0aec02e7421c64275e0503a33210ab202c076bf4000090369443430d488c2c708c140dd201eb402c104b40000606740000104ac0000003cac18b207bc837620d080000d0c580000e06c8c51700000000000000000000001c109641880000d096f40b9508c40000303c000004028b81a70000000003089600a800001c39860a56816090e22a43f00000035700003c17370267024c64c7c00000000243230071a031e7011a00ff20ea140472028c408e0000000009016800000b8e8826200391c38ee074400003579b8269e6d5400009) else (if i < 3 then 0x90b60000050b6f40ad20d2ac0360000364fdc0c47c071e8963406954151008a908528b7d00001004f10c215d322058c000000001e0b7a6be8000076541c02e0071ec46e602610b52e07ea02c3000000000109700000306480000b0937c2feb0d240000f02f000c7403839afe60798000090553c378a0aa3025700003426500002497610e2ec36b0073a41f00000001a32097dc0f79928b1a44d077981e7204d400000000000004656b1cef6864dc26dc8e5000000000305e721160806010df80000d0aa801360000380aea0608000020b291f56009854a337928e814ce755e825ed065640a76020180838585a82f8305dce0f090e5da728b0eb400e9005d20183d0024000070315112d10834818115369835d10510000000002410a00000815db04dec2f490755c2830895e6f83000001cf09076bc191807b0c15380eb8dc6e00002c0b0d010c000000000000019d21004b30b8c000000001c11b6057cc0ec67c820291db452c10580e52c2fce0028000064d484370b0e7a82a3d113d0216200b6ab5f490148229c0519c301000000000d0d60000010440000000002010e0000382fa0000140f1302d0c03f000011f98808e000003050d1944008e541230000202cda0982c20e0000081bfa0c4a41d9604764193c04bb01f2d0aa400003021fdf66b09030315011a3034130bc00102e09c9d85860d9f81b90000042ff00000000000001400e00002c1a9000000a34c8944000000001402f109bfef82000000000101000000f07a64056a067c000000002636f401340000c07cdc05270bb40000d77700000e078c000000000000070a8980d9b03940000607da82ea76e600000605ffc04e30491431720d65cc840052dc31cd0b09c234200d14094000028732e0e76c29d70e90029a80a0102bde07d5e03a407de03a1d0bbd813800780000000000dc4c30a70000020dcc000066de40000283db021950d8980f60000000009045c00000000380eec075c000000d340000d06c000009924b40293077ec28c00000838a7082d42ae60044c25dc093f42dd90b068057000000000000000000b0cc40000a08740000000018e10605d6c32fc090b808500000cba65039c0000808e8000010950000080c12012020e88000000002c180e0d325c3d00003c0920017c0000d83d5e493006400000204c4c755a0ca902cb000c7a535000008314200ec80c400002815ca0b1cc10ca0076417b102240000a0d1a01c0a03ef197a0000082869066e94ee00003d8d230b82024e70516cb55ca9640000d024c000050717253680a35437a50740832d0000000000000382be700a8022370108958e30a40812c80254434810a8701861039ac100106b4410df06678798b0c175c3e304d145eab0cec000010358000000000420f106ef010f30e15021c903f94179644bcc0b200b27 else (if i < 4 then 0x6e39810c0ac32e70082028e8072082b75081e039260389c09fb0ca341a5e0154000028d540000a08b76c7710855c2af20ccb01fce000281b67018783399056782bfb45e3c2d0d727c0000000000000000006d78000038267000000000000000000a01dd41eb365fcc30e6023c0000000002259000024171000000000b04a0000030d0c00000000080449065e4005000000000800980000c0598000060e68c23670e8101ba0000000000000000009b8734a3054cd80000000000000000000000640f0c37d60cd94226503500000000024033f25e40000e0990000090e6d438dd015280ac00001c16700003c2c6f027502f76061ec24b50acf1130000000000000000000607f4000000000000020e5b23a2000000000c0868000000910000000000000030a4c000047df00000e05db03270000302d5705afae9990687c32010c4f0053e1dbc000000000000000a64000072cac000000001407b0000344b400000000040e3d633100001c0075070d43a5b03b64375a05b480b600001c2460000000000000081ed317a540ab1098c00002b08c0000c0904000030cf0000040be69989301d2800800000000040b7800008b45c0000e75fc0000c084b043a000004353701bf80320000342b9000000000c0300dcf940b9b19a50000280cf4050600c1d00c3414287df65da3f0ad6c08d9061400000000000000062a42e5f03256d186475483a3006a2c3aa604a4000000000000020527046f10d8681d40000301d370bb3c224609f3831d000008249b0c332f7bc08fe4310f00e7c15b90e4dc2d3f0c68c1a694e5e0133a0d58252bb082740cbc7ce400000000103917032000008b4572979501780000b084c81c47ae080014205a1dcfa00cf80000409fc00006896e0221ab26881fb00002c3a939e0c0000a04e5c0c382d5000002693c000000000000020e1b05ec20ba0000000002446d000016d13901a0831f000000000d0ac8000080bf4000070258000071441c2170000000003048ac3260000282ad30c03c0aac0a049a34106e141a000544000000001416e0000145f01945482550000282d700ac00000e0e42000f70804c8b600003015a728bd80ea000000000506500000f08f98245e05fa8205d0aac0000917b4000000003e76700000000087e5c0000a0cc1c0ca000022252644b3839540bb8844aa1e67c003a0da981218002ed959707b981060000282da70040c07040032035f000000338000000000c03e0001e000000000f0bd882cfd913400002094f97a540b1242fb00003428b001e45d31507e5c038304f800000019e296931d58404160847e4fc009fa0152c0c3f02a4503ac815800003414a150c780be00000000000000c0b8000000355000018232000000000000000000c83bc000000002c21f2088a430db06b3829e509d2c368c004f806e else 0xb07a0000027cd0579e999c941bec25e9d82ae0dc9839c9090cc2e1625d40172a06240000200340000e052240484080000009006f027109168a76da0590c17ae059)))
def rulesWord14 (i : Nat) : Nat := 0x2e80f822a0982945242945243784060a840439412439412405004003002230261e8bd99dca0f7b5
def spentSigned14 (i : Nat) : Nat := 0x0
def linksSigned14 (i : Nat) : Nat := 0xd00000000000823309ac01000000040b0000b0e0000801400010448215076e22e0540000001413109c032000000fb05dd9f8b7c000a06e16200000000003221898a8a10000000000051f000102570ff62d37800000031c0060ebc1ca060000204242fa0f6c1600028300000000f28b831a0f302e704bee26088c2900031a0102406050d4000a02f1a2c78843ec0e50060003c08a08340a2a89004038800010ac000000000000006f0a00eea0f06b82ab064828107c85f401f837e0d8ca0400a9df0001c14c09040e40ec00020b400050d00000000062f488000e07b43301bda130030504905000100214d20
def signedLevels : Nat → Packing
  | 9 => (3,6,0,0,0,0,0,fun _ => 0)
  | 10 => (200,5,0,0,0,0,0,fun _ => 0)
  | 11 => (1125,4,0,0,0,0,0,fun _ => 0)
  | 12 => (944,3,0,0,0,0,0,fun _ => 0)
  | 13 => (64,2,0,0,0,0,0,fun _ => 0)
  | 14 => (2,1,0,0,0,0,0,fun _ => 0)
  | _ => emptyPacking
def signedIndices : Nat → Nat → Option (Nat × Nat)
  | 10 => lookupWord 1 15 0 10 2 4 linksSigned10
  | 11 => lookupWord 81 349 7 16 8 4 linksSigned11
  | 12 => lookupWord 476 2013 7 19 11 4 linksSigned12
  | 13 => lookupWord 402 1693 7 18 10 4 linksSigned13
  | 14 => lookupWord 29 127 4 14 6 4 linksSigned14
  | _ => fun _ => none
def signedBudgetData : Nat → Nat → Nat
  | 9 => spentSigned9
  | 10 => spentSigned10
  | 11 => spentSigned11
  | 12 => spentSigned12
  | 13 => spentSigned13
  | 14 => spentSigned14
  | _ => fun _ => 0
def signedRules : Nat → Nat → List (Nat × Nat)
  | 9 => ruleRead3095 rulesWord9 16384 6 0 6 2 12 17 80 0 14
  | 10 => ruleRead3095 rulesWord10 8192 2182 11 2325 9 4125 16 7517 0 13
  | 11 => ruleRead3095 rulesWord11 4096 9526 14 10520 10 21770 15 28010 0 12
  | 12 => ruleRead3095 rulesWord12 2048 10358 14 11184 11 21568 14 26007 15 11
  | 13 => ruleRead3095 rulesWord13 1024 2522 11 2566 10 3206 13 4506 0 10
  | 14 => ruleRead3095 rulesWord14 512 66 0 66 6 78 12 318 0 9
  | _ => fun _ => []
def rawRecipe9 (i : Nat) : Nat := 0x17ad88d5b1534c120583c7a314c0a62982408054ee5749b6114160160
def getRecipe9 (i : Nat) : Nat × Nat := let a := packedAt rawRecipe9 (i * 75) 75; (a &&& 1152921504606846975,a >>> 60)
def rawRecipe10 (i : Nat) : Nat := (if i < 1 then 0xa7bd4caa9814c10096fd6caed8148100a7f51caa98148100e7d98a4c53048100f7d1814c53048100f769535492044100f7e1c25452044100ae7ecc6cda521960ae7dc22cda521960ae7ecc6c9a521960ce7db36c9a521960ae7d3c2c9a521960aedecc6d5a321960aeddc22d5a321960aedecc6c9a321960aedecc6c1a32196087fecc6c8a961560ae7dc521aaa54d60aeddc321aaa54d60aef5c121aaa54d60aafc8c5a8a254d60aafc8c5a9a154d60ae7dc5219a214d60aeddc3219a214d60aef5c1219a214d60d6decc6cc8664960d6ddc56cc8664960d6dcc56cc8664960d6ddc26cc8664960d6ddc06cc866496096fdcb2195364960b6ddc32195364960b6f5c1219536496087fdc12ad5364960b2fc8c5ad5364960b6ddc32185364960b6f5c12185364960b6ddc321a3364960de5dc56cc8654960ae7dc521aaa54960aebdc421aaa54960aeddc321aaa54960aef5c121aaa549609e7dcb2195354960be3dc42195354960be5dc32195354960be75c12195354960ba7c8c5ad5354960ae7dc52193a1496087fecc56c9a5096087fdca2e5874c960ce7dca6d4864c96087fdca2e5854c960ae7dc52195a4c960aebdc42195a4c960aef5c12195a4c960ae7dc521aaa4c960aeddc321aaa4c960aef5c121aaa4c960a6fdc2269635056087fdbc2698250560a7edc22698250560c6fd656c89a4c560bb78c569d8460160be78c569d6460160fab9a76116460160fab8a56116460160fab9756116460160af78c569da360160bd78c569d7360160b778c569d9360160be78c569d6360160cef9a72ad6360160fab984591a260160fab9845917260160fab9845915260160fab9845922260160af78c569da160160bb78c569d8160160be78c569d6160160fab9845516160160d3f8c962d5160160fb71526055160160dbf15b6053160160fbd1326053160160b67dc52199254160b6ddc32199254160b6f5c12199254160ce7dca6d4864c160ae7dc52195a4c160aef5c12195a4c160ae7dc521aaa4c160aeddc321aaa4c160aef5c121aaa4c160be5dc5219534c160b67dc5219924c160b6ddc3219924c160b6f5c1219924c160ce7dca6d48648160de6dc26d48648160ceddca6cc8648160ded9c06cc8648160ae7dc52195a48160aeddc32195a48160aef5c12195a48160ae7dc52193a48160aeddc32193a48160aef5c12193a48160ae7dc521aaa48160aebdc421aaa48160aeddc321aaa48160be6dc52195248160beadc42195248160becdc32195248160bee5c12195248160be79c52193048160bed9c32193048160bef1c12193048160ff49535493048160ee75655e95144160def16b6d15144160fe716b5495144160fe71635495144160feb1645c94144160feb1645494144160cbb8ab6115460160b3f0c96053160160d6f09b5ad5144160 else 0xbf78c569d3160160de7dc36d48648160deddc56cc86481609efdcb2195348160bef5c12195348160bafc8c5ad5348160fed96354d3048160fed96c54d304816087fd1caed8a48100e3f98a605304810095fd7caed524410087fecc62d3a4410087fecc62d2a4410087fd5c4ed2a4410087fecc4ed2a44100e7e9524e92044100ceddb56c1a321960cafc8b5e96a54d60aafc8c5aaaa54d60aebdc421aaa54d60aafc8c5a9a454d60aafc8c5a9a254d60aafc8c5a9a054d6087fecc6d4a96096087fdcb2a55360960a77dc52a55360960b67dc521a3364960b6f5c121a3364960ceddca6cc865496087fecc6cc9a549608dfdcb1eaaa5496087fdca2e5835496087fdbc2698354960aebdc42193a1496087fd8c56c9a4c96087fecc56c9a4c960aeddc32195a4c960aebdc421aaa4c960fabaaa6116460160fab9a56116460160faba556116460160fab984590a260160fab9845905260160bd78c569d7160160fc75655c5515c160ceddca6cc8654160de5dc36d4864c160aeddc32195a4c1609eddcb219534c160bed5c1219534c160badc8c5ad534c160aebdc42195a48160aef5c121aaa48160baf88c5ad5344160fe71645495144160feb1641494144160feb1648894144160f749535493048100f761525452044100ae3d4c2c9a521960ae3dc52194a14960d3b89b6114160160c7fd5b6293148100f7f1835452044100de7dc06d4864c960deddc26cc8654160be7dc52193254160beddc32193254160bef5c12193254160be7dc52195348160beddc32195348160fb798554d8048160)
def getRecipe10 (i : Nat) : Nat × Nat := let a := packedAt rawRecipe10 (i * 64) 64; (a &&& 1125899906842623,a >>> 50)
def rawRecipe11 (i : Nat) : Nat := (if i < 4 then (if i < 2 then (if i < 1 then 0x481105837fcbd240882c1bfe4e92044160ffe2a290220b05ffabb61110582ffcc5ae8882c1fbe5d56444160fdf4aab2220b05ff98b55110583f7cb2aa8882c1fee6115444160f7f308c1a20b07df9875cd10583f7cb2ae6882c1fbe5917344160fdf2eab1a20b07efa5558d10583f7cba2c6882c1fbe5516344160fdf2e6b1a20b05ff98b54d10582ffcbdaa6882c1fbe5ad5344160bff576a9a20b07f798554d10583f7cb2aa6882c1fbe5915344160fef2a8a9a20b07fd98354d10583fecb9aa6882c1fbe58d5344160bff316a1a20b05ff95b50d10583fdcc2286882c1fbe5917244160fdf2c6b9220b077f97564910583bfd2ab24882c1dfe5d19244160eff2a8c9220b077f97364910583bfca9b24882c1dfe14d9244160eff286c9220b05ff98b54910582ffcbdaa4882c1f7e1ed5244160bff576a9220b07f797554910583f7cb2aa4882c1fbe5915244160fef2a6a9220b07fe98254910583ff4b92a4882c1dfe6495244160fdf2c829220b07ef96314910583f7cb2a84882c17fe62d4244160bff2b6a1220b07fb95450910583f7cb1a84882c1dfe6494244160fdf2c899220b05ff95b4c910583f7cb1a64882c1dfe6493244160fdf2c911220b07ef963889105837fca9b14882c1bfe5498a44160fdf2c6bd220b077f9925e910583f7cb1ab4882c1dfe6495a44160bff2b69d220b07ef9634e910583bfcc9274882c1fbe58d2a44160bff2b695220b07ff18754510583ff8c5aa2882c1ffc5ed5144160ffe576a8a20b07ff18554510583ff8ba2a2882c1ffc6d15144160ffe2a8a8a20b07ff18354510583ff8b9aa2882c1ffc6cd5144160ffe166a8a20b07ff15354510583ff8a1aa2882c1ffc8cd5144160ffe304a8a20b07ff17254510583ff8d92a2882c1ffc2c95144160ffe2a4a8a20b07ff14254510583ff8992a2882c1ffc0c95144160ffe444a8a20b07ff18a54510583ff8bd2a2882c1ffc5695144160ffe274a8a20b07ff12a54510583ff8c1a82882c1ffc5cd4144160ffe304a0a20b07ff17250510583ff8a9282882c1ffc1494144160ffe264a0a20b07ff222505105823fe5d262902011ffaed3a44100ddb964d190cb047fdb52a57358337e4d2d4a9ac19fd28ca164960cbf8f4cd2a4b05eddb321852582f7ad890c292c179f6d4860c960bdbb6643064b05ef5b121832583d7ac1302b0ac11ff6cc9a505608ffb644d282b067bc9a50941582bfa5cb0298ac1cfd625814c560cdfac64d242b05ef8ab59580582dfcc5aa8c02c1ebe6156360160f6f30aa9b00b07af98458580582bfc4da82c02c13bf2e965481609df974b1a40b07e756554510583bf84daa2882c1fbc5955144160efe324a8a20b07f7152545105837f8c52a2882c1dfc6494144160ff6284a0a20b053f8b960580583d78c0ac2c02c1f9c5955144160 else 0xc1dfea65804c160f7f30ac0260b077f99560130583f7cb2b00982c1bfe569804c160dff554c0260b07ef96360130583feca9b00982c1dfe649804c160f7f302c0260b077f99160130583f7cb0b00982c1ff64c5804c160fdf2c6b8260b077f9925c130583efcb8ae0982c1fbe585704c160ffb262b8260b076fd8959520583b7ec4ac6902c15ff66d5348160bdfad6a9a40b04ffcba54d2058377eb2b14902c1bbf58d8a481609ffb16bd240b06efd655e92058377eb1af4902c19ff54d9a48160cff8a6cd240b067fe336692058377e432b4902c1bbf5955a48160ddfac6ad240b06efc864e92058377eb2a74902c19ff66d3a481609ffab69d240b06efd634e92058377e43554902c1bbf596aa48160ddfac755240b057febb64920583b7eb1b24902c19ff4e99248160cffd54c9240b077ed8954920583bf74caa4902c1fbb2195248160fbd8f6a9240b077ed9b54920583fb6baaa4902c1dfb6555248160fddacaa9240b077ed9354920583f76b1aa4902c1bfb6295248160dfdaf4a9240b057fd9b4c9205836febd2e2902c1dfb5499148160ddfb14b0a40b07eed5258520582f7eb5aa2902c1ddf6555148160fcfacaa8a40b07f6d5254520582f7eb5a62902c1df764d3148160fdbac698a40b07eed6548520583f76b1a42902c17fb56d2148160eff2f2c0240b07bf98560120583bfccab00902c1fbe5958048160eff326c0240b07ef963601205837fcad300902c1bfe4e98048160dff554c0240b07fe95260120583dfcc0b00902c1dfe6458048160fdf2c2c0240b07fe92160120583bfcc4ae0902c1dfea657048160fbf2eab8240b07df9735c120583bfcc9ae0902c1fbe58d7048160dff314b8240b06ff93a5c120583ff4a92e0902c1f7e5c57048160eff322b8240b07ef9615c120583ff490ae0902c1dfe6253048160eff2f298240b07ef8864c120583bfccaa60902c1fbe5953048160bff31698240b05ff97b4c120583bfcc9a60902c1bfe6293048160dff2f498240b077f9924c120583ff4a9260902c1dfe6453048160fdf2c298240b07fd9314c120583ff490a60902c13ff62d7a44160ddfacabd220b067fd925e91058377eb2a74882c13ff62d3a441609ffaf69d220b04ffd5b4e91058377eb1a74882c1bbf5952a44160ddfac695220b06ff97a601105837fc9d300882c1bfe4a98044160bff316b8220b07ef9655c110583bfcc92e0882c1bfe6297044160dff274b8220b06ff92a5c110583f7cb2a60882c17fe56d3044160fdf2c698220b07fd9534c1105837fcc5260882c1bfe5e93044160dff25498220b077f98948110583bfcbca40882c1dfe6552044160fdf2ca90220b077f99348110583f7cb1a40882c17fe62d2044160bff2f690220b05ff95b48110582ffc9da40882c17feaed2044160ffd2a490220b06ff98a) else (if i < 3 then 0x26a9300b07ef96354980583fbca9aa4c02c1ffa6895260160ffd2e4a9300b07bf98414980583f7cb18a4c02c1fbe5954260160bff2b6a1300b07ef96350980583fdca1a84c02c1fbe5953260160bff2b699300b07ef9650c980583f7cb2c44c02c1efe6122260160fdf2c711300b06ff9a768580583dfcc2342c02c1efeaa98160160f7f34ec0b00b07bf9a560580583dfc52b02c02c1efe5d58160160f7f4aac0b00b07bf9a460580583dfcba302c02c1efe5518160160f7f346c0b00b07bf8a360580583dfcb9b02c02c1efe54d8160160f7f0a6c0b00b07bf94360580583dfd19b02c02c1efe6898160160f7f144c0b00b07bf97260580583dfca9302c02c1efe1498160160f7f284c0b00b07bf93260580583dfc19302c02c1efe8898160160bff356b8b00b05ffabb5c580583dfcc2ae2c02c1efe6117160160fbf2e4b8b00b07ef9a758580583f7ca9ac2c02c1fbe5496160160bff2f6a8b00b07bf98454580583fbca92a2c02c1ffc5c55160160bff2f6a0b00b07fb94250580583dfcc2a62c02c1efe6113160160bff35698b00b05ff97b4c580582ffcada62c02c17fe52d3160160bff57698b00b07fd9324c580583ff8a0a62c02c1efe6112160160bff2f690b00b05ff95b48580582ffc9da42c02c1ffc4c52160160cffd54c92e0b057febb64970583afeb9b24b82c1dbf58d925c160efe962c92e0b07cfd635c570583afec92e2b82c1bbf629615c160edfb24b0ae0b05efd6b54570583efab8aa2b82c177f5ed315c160bdfad698ae0b07edd634c570582f7ed990ca82c13ff62d7a54160ddfb14b1aa0b057fd8b64950583b7e43324a82c19ff6299254160cffaf4c92a0b076fd6564950583b7eb1b24a82c1dfd2c59254160affb36a92a0b067fd9a4c950582bfecda64a82c19ff6683254160cffb35112a0b076fd9258550582f7eb5aa2a82c1fb758d3154160affb3690aa0b077f99260150582bff5daf2982c17bf6cc864c160edfb12b2a60b06efd65629305827fec5af4982c1bbf5957a4c160ddf90cad260b04ffd8b569305827febdab4982c1bbf21aaa4c160ddfacb55260b06efd7a58d30583beec4aa6982c1df7a65534c160efb936a9a60b07f5d8554d305837eec52a6982c1bf75e9534c160affb16c9260b057fd7b64930583b7e43324982c1dbf595924c160cffb14c9260b067fd7a649305833fead324982c1dbf58d924c160efbaa6c9260b077f4b164930582bfecdaa4982c19ff669524c160febaa6a9260b067fd9a14930582bfecda64982c19ff66a224c160ebfaf2b8a60b057fd7b64530583beea9b22982c1fb754d614c160edfb24b0a60b05efd6b54530583bbecaaa2982c1f9f595514c160bdfad698a60b077dd794c530583beecaa62982c1fb7595314c160bfbab698a60b07fd5814c530582bfecda42982 else 0x1583f3eb1aa4a8ac1fdb6095254560ddfad4a12a2b06efd6a4c95158377eb5064a8ac1bbf5aa2254560f7eb04c0aa2b067fc9a60d415833fe4d2e6a0ac19ff6697250560cff934b9282b06efd6a5c941583bdeca2e4a0ac1faf5917250560cffaf4c9282b067fd9a549415833fe4d2a4a0ac1def6515250560fd7ac8a9282b067fd9a149415833fe4d0a4a0ac1def6505250560fd7ac829282b077bd7950941583f5eb2a84a0ac19ff2693250560cffb3511282b067fc9a8894158377eb5444a0ac1def6522250560fd7ac911282b04ffd8b5e9315827ff5daf498ac19ff6257a4c560cff972bd262b067fe995e9315833fecaaf498ac19ff6517a4c560ddfac8bd262b06fecb25e931583b7eb293498ac19ff61c9a4c560ddfae8b5262b06efd545a9315827febdab498ac1bbf5915a4c560ddfacaa5262b06efd65aa9315836febd2e498ac19ff5e9924c560cffab4c9262b067fd9a5493158377eb52a498ac1bdf569524c560ddfad4a1262b077dd794c931583f6eb2a6498ac1dfd269814c560dfeab4c0a62b07bf58260531583fea9930298ac1bbf5957a48560ddfac6bd242b067fd74669215833fea9b3490ac19ff14d9a48560cffa86cd242b067fe33669215833fea993490ac13ff62d5a48560ddfac8ad242b06efd635692158377eb2a9490ac1bbf5953a485609ffaf69d242b04ffd5b4e92158377eb1d5490ac1fbd5953148560dfeb1498a42b07afd8558d80583dbec2aa6c02c19ffaa99260160e7fb0ac9300b07bf5814c580582ffd5db4ec02c1fde2d5a760160dff34ed2b00b07bf9a761580582ffcd5aeac02c1f7e69d7560160eff34ecab00b07efaaa59580583f7cd3acac02c1fbe6956560160fdf2cad2300b07bfaaa61180583dfcd3b08c02c1efe6958460160f7f14ac2300b07bf97561180582ffcd5ae8c02c1fbe5957460160fdf34eb2300b06ff9a768d80583f7cb2b46c02c1fbe594a360160bff356b9b00b07df9a75cd80583bfccaae6c02c1fbe5957360160fbf2e8b9b00b07ef9645cd80583bfcd3b26c02c1fbeaa96360160fdf34eb1b00b07ef9a558d80583f7c52ac6c02c1fbe5d56360160fdf4aab1b00b07ef9a458d80583f7cba2c6c02c1fbe5516360160fdf346b1b00b05ff9ab54d80582ffcbdaa6c02c1dfe66d5360160fdf2d6a9b00b05ffabb54d80583dfcc2aa6c02c1fbe5915360160ffb346a9b00b07fd97354d80583f7cb2a86c02c17fe56d4360160fdf2cb19b00b06ff9a768980583f7cb2b44c02c1efe611a260160fdf2c6d1300b07ef96528980583dfcc2144c02c1fbe58ca260160bff356b9300b07ef9655c980583dfcc22e4c02c1fbe58d7260160bff356a9300b05ff97b54980583efc3daa4c02c17feaed5260160fef14aa9300b07bf98554980583fbcbaaa4c02c1fbe5915260160eff3)) else (if i < 6 then (if i < 5 then 0xf1eaaa54960ddf90d552a4b057fcb961152582bfec5b28a92c15ffaed9454960ebf8f4ca2a4b06efd8a5915258377ebd2c8a92c1f3f1e96454960ddfd54b22a4b07e7d75591525836fe3d348a92c15ff2e58354960cff934c1aa4b075fc7a64d52583bde5a326a92c1dbf5919354960ddfaf4b1aa4b06efeaa58d525836fe3d346a92c1b7f1e8a354960eefb12a9aa4b0777e9954d52583f3e432a6a92c1ddf66d5354960eef936a9aa4b07e7d6b54d525837bec52a6a92c1f5f1e95354960eefb34a9aa4b0777d9454d52583f3eb22a6a92c1fd760d5354960feb946a9aa4b07f6cb254d52582bfecda86a92c17bf5ad4354960cff93519aa4b057fcb960952583bf6dcb04a92c1dfb2e58254960efdd32c12a4b07dec7a60952583bf6cd304a92c1fdb2d58254960fedaeac12a4b077ed9460952583f76b2304a92c1efb60d8254960fedaa6c12a4b07eed645c952583f76b1ae4a92c1fdb54d7254960dbf8f4d0aa4b06dfc7a68152582bfea5d32292c15ff4ee9914960bdfb66430a4b057fd8b65052583bde5a326292c1dbf5919314960affb36a18a4b05efd6b50c525833febcb14a12c19ffa658a50960ddfacabd284b067fd75669425833ff2ab34a12c1bbf596aa509609ffb1755284b04ffd7baa9425827feadd54a12c13ff46eaa50960fd7acaba284b057fcb961d32582bfeadd32992c15ff4ee994c960affa574ca64b05efdb521932582f7ed990c992c15ff2e5854c960cffaeacd264b067fd74669325833fec2934992c1bbf2195a4c9609ffb16ad264b06efd64569325837f6ad304992c13ff6e9524c960affab74c864b05efdb521832582f7eda90d112c17bf6cc8688960aff972c2c44b057fd8b65222583f5ec22c9112c1def2d19388960edfb28b1c44b057fd9b54e22582f7eb5aa7112c15ff66d4388960bdfad6a1c44b073fd895cd81583df6c12a4c0ac1cff6254260560ddfd54b2ae2b075fd7950d71583afebcc66b8ac19ffaa97564560ebfb0eb9b22b067feaa5cd915833ff552a6c8ac1df760d5364560cffd5429b22b067fd7a50d915833febd466c8ac19ffaa97264560cffd54a9322b075fc7b54991583bbea9aa4c8ac1dfb6095264560cffd5429322b057fd8b509915833ff55264c8ac19ffaa83264560fd7b08aa2c2b07cfd875cd6158377ed5aa6b0ac1fb760d5358560bdfd76c12c2b07afd8360961582f7ec5ae4b0ac1dbf5d19258560edfaa6c92c2b076fc5364961583b7ea1b24b0ac1dbf8cd9258560bdfb16a92c2b07cfc7b54961583f3ea9aa4b0ac1fbb6095258560bdfb16a12c2b05efd8b4c961583f76c1264b0ac1bbf5a974545609ff974b9aa2b06efd6a5cd5158377eb5286a8ac1bbf5aa33545609ff974c12a2b067fc9a6095158377eb52e4a8ac1f5f1ed5254560fcfac8a92a2b0777d935495 else 0xa408057fd3b68520403bfcb2a6090201dfe62d3048100eff2b6982408077f98a4c120403bfcad26090201dfeaa93048100eff302982408077f9514c120403bfcd8a6090201dfe6853048100affd76b9a208075fd875cd10402bff5db04882015ffaed5244100efdb04a92208057fd8b4e9104033fec2a74882019ff62d3a44100cffab69d2208067febb4e9104033fec1274882019ff5493a44100cffb649d2208067fd834a9104033fea9a54882019ff62d2a44100cffa76952208067fd83aa9104033feb9d54882019ff60aaa44100cffaa5552208067fd32aa910403bfcc2a4088201dfe60d2044100eff2a6902208077f98b48110403bfcada4088201dfe4ed2044100eff314902208077f95a48110403bfc9d24088201bbf6cda521960ddfb64d290cb06efdb568c8658377ed9346432c1bbf6c1a321960affab74cb0ab057fd4ba6585582bfe9dd32c2ac15ff4ae9961560affa974caeab057fd3ba6575582bfe95d32baac17bf6cc8695560cffb14bab28b067fd8a95594583f5ebab08b22c15ff5ee9960d60affab74cb06b057fd3ba6583582bfe95d32c1ac19ff2a57560d60affab74cae6b057fd3ba6573582bfe95d32b9ac19ff2a5855cd60affab74caa6b057fd3ba6553582bfe95d32a9ac17bf6e88654d60bdfb6a432a6b05efdb321953583d7e45ad4a9ac1dbf6256a54d60edf972b52a6b06efd8a5a95358377ebd2d4a9ac1bbf2696a54d60ddfad5552a6b06efc86aa953583f3eb530aa9ac1bbf6296454d60ddfaf4b22a6b06efeaa59153583f3ec2ac8a9ac1bbf5a9a454d60efbb72c1aa6b077de9960d53583beecd306a9ac1fb75a98354d60efbb28c1aa6b07edd6460d5358377eb5344a9ac1bbf5a8a254d60ddfad4d0aa6b06efd6a68153582bfe95d3229ac15ffaed7950d60bdfb6a43466b057fd5ba6582582bfea5d32c12c15ff4ee9960960affa574cb04b067fca95d5825833fe54caac12c19ff2a553609609ff956a9b04b057fc9b54d82583deec1aa6c12c15ff56e995c960affa974cae4b057fd8b65172582bff5db28b92c1faf611645c960aff972c1ae4b077bcb464d72583b7eb2326b92c1dbf651635c960affb36a1ae4b05efd6b50d725833fec52e8c92c19ffaa97464960edfae8b1b24b067fd8a54d925833ff552a6c92c1dbf2195364960affb16a9b24b067fdab54d92582bfe55aa6c92c1dbf5ad5364960affd76a9b24b077dd8354d925833fec50a6c92c1dbf2185364960cffb14a1b24b076fd6550d925833fec5466c92c1dbf21a3364960efeae850b24b077f55328592583bfa29942c92c1dfd50ca164960efec6650b24b057fd5ba6552582bfea5d32a92c15ff4ee9954960affa574caa4b05efdb521952583afec48f4a92c1d7fa647a54960dbfb143d2a4b06dfc7a66952583afe3d334a92c1b7) else (if i < 7 then 0xbf6caa42902c17fe62d7048160fdf2cab8240b077fa994c120583f7cb1a60902c1ff654d3048160eff466c9220b07ef96354910583ff8c22a2882c11ff2e953481008ffd76c52408047fd8baa9204023fe9dd54902011ff46eaa48100efb2a6982408067f98a4c120403bf4a926090201df64c530481008ffb169d2208047fd8b4a9104023fe9da54882011ffaed2a44100efd2a4902208067f93a48110403bf8a8a40882011ff4eeaa5e560dcfd76d290cb06e7db36948658373e59b4a432c1b9f6c9a521960dcf964d290cb06e7db06948658376f5db46432c1bb76d5a321960ddb96ad190cb06eddb268c8658376ed8346432c11ff6cca9615608ffb6454b0ab05e7db521a55582f5eda10d2aac17b76cc8695560bdeb62434aab047fdb52a5835823fed9152c1ac13bf6e88654d60bcfb6a432a6b05ebdb421953582f6ed990ca9ac17bd6c48654d60b5f916b52a6b05e7db521853582f6ed990c29ac17bd6c48614d60bcfb6a43466b05eddb321a33582f7ad890d19ac11ff6d4a9609608ffb6654b04b056fdb3219925823fe55aa6c92c179f6d48654960bd7b68432a4b05eddb321952582f7ad890ca92c11ff62c9a549608ffb664d2a4b05e7db521852582f5eda10c292c11ff62c9a509608ffab64d284b05e7db521932582f5eda10c992c17b76cc864c960bdeb6243264b047fd8b269325823fead934992c179f6d48688960bd7b6843444b05eddb321a22582f7ad890d112c19bf2a5655c560cdf934b1a82b066fd6526931582fbc5ab4ec02c1eee6115460160bdf156b1b00b05bf98b54580583df8c0aa2c02c16fe62d4160160f77308a0b00b07bf1814c580582f3eda90ca82c17af6d08654160bdbb66432a0b05ef5b121950582f3eda90c982c17b76cc864c160bdeb6243260b05e7db521920582f5eda10c902c17b76cc8648160bdeb6243240b07ef16b54510583f78b22a2882c1fbc58d5144160fde2c6a0a20b047bd4baa930402b6ed990cc92c15bd6c48664960f57308b2300b07eb16450510583bfea9b0488201dff60d5244100dffb14992e0b07dfd835c570583bfec4a64a82c1dffa653254160fdf90c992a0b06ffeaa4c950583f7eb2a64a82c17ffaed3254160fdfac6992a0b077fd924c950583f7e992c2a82c1ffe4c98054160ffbaa699260b077fd8954d20583bff4caa6902c17ffaed5348160fefb0aa9a40b07fdd8354d205837fea9af4902c1bff54eaa48160fdfaa6b0a40b07fed5348520583ffcc1ae0902c1ffe60d7044160fff264a8220b067feaa60530402bff5dae2982019ffaa9714c100affb16d0a608057febb58d204033fed8b14902015ff56d3a48100cffac7552408067fd53aa920402bff5db02902019ff6e98148100e7fb14c0a408067feaa605204033ff5526290201dfe6c13148100affb16d0 else 0x1dff549814c100effaa6c0a408077fd7454d92583ffcd3a62c02c1bff629315c160fdf90ca9a40b07efd6b54d20583f7eb2aa6902c1fbf58d5348160effaa6c9240b07ff95360120583ffca9ae0902c1ffe54d3048160fff2a690220b075fd875c5304033ff5db14902019ff6293148100cffd54bab28b07ebe5561164582bfe9dd32b92c17bf6cc8654960fd7b08b22a4b07cfc7a58d52582bff5db28292c1faf6116414960cffcaa4d284b067fe5526932583b7eb2327112c19ff2698250560dbfb0ebd262b06efd655e931583dfd2ab08c02c1efe6115260160fbf34eb8b00b067fd8a649705836fec52e2b82c1f3f595715c160bdfb6a43260b07edc8654d30583f6eb5aa6982c17bf6d48648160bdfb6643240b07f6d5354920583)))
def getRecipe11 (i : Nat) : Nat × Nat := let a := packedAt rawRecipe11 (i * 53) 53; (a &&& 1099511627775,a >>> 40)
def rawRecipe12 (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0x2ffd7a54560dff669515837fc9a54560fbf5a951582ffeaa54560dff65151583efd6454560dff64d51583efd6354560fdf54951583ff58154560bff5e9415837fd9250560dff625315837fd794c560dffa65315837fd954c560dff65131583efd644c560bff629315837fd9a4c560dff26931583efd6a4c560bff56931582ffd4a4c560bffaa9315837fd924c560ff74c9315837fd8948560dff5e5215837fe9948560dff65521583efd6548560dff65121583efd6448560dff64d21582ffd8a48560bff5e9215837fd9a48560bff56921582ffd4a48560bff4e921582ffeaa48560ffd4c521582ffeaa60160dffa6580583bfd8560160dff65580583efd6560160dff64d80583efd6360160eff605805837fd9160160fbf58580583ffaaa60160ffe69580583ff8a560160ffe5d580583ff89560160ffe95580583ff9a460160ffe5d180583ff95460160ffe68d80583ff8a360160ffe5cd80583ff89360160ffe14d80583ff94360160ffe8cd80583ff9a260160ffe28980583ff97260160ffe24980583ff85260160ffe50980583ff93260160ffe0c980583ffa2260160ffe68580583ff95160160ffe50580583ff92160160dffa6570583efd635c160fbf585705837fd8954160dffa6550583efc8654160bff62950582ffd7a54160bffaa9505837fd9554160fbf595505837fd9354160fbf58d505837fd9254160dff64550583efd6154160fdf54550583ff98054160dff625305837fd794c160dffa65305837fd954c160bff62930582ffd7a4c160bff56930582ffeaa4c160dff64d305837fd924c160dff64530583efd614c160ff74c5305837fd8948160dff5e5205837fe9948160dff655205837fd9348160bff62920582ffd7a48160fbf1a920582ffd5a48160bff4e920582ffeaa48160dff64520583efd6148160ffb485205837fd8944160dff5e5105837fd9544160fbf595105837fd9344160fbf58d105837fd9244160bff62910582ffd7a44160bff56910582ffd3a44160bff4a910583ff55144160ffe60110583ff97044160ffe54110583ff93044160ffe61d10583ff98544160ffe5d510583ffa5544160ffe5d110583ff95444160ffe60d10583ff97344160ffe14d10583ff94344160ffe8cd10583ff98244160ffe5c910583ff85244160ffe50910583ff93244160ffe0c910583ffa2244160ffe62910583ff97a44160ffe56910583ff93a44160ffe4a9105827feaa625609ff62a995827fd1aa65609ffaa9955827fca9611609ffaa993583ef8a058d609ff269535827feaa649609ff2a5815833fd89605609ff2a5715827fd8a64560fbd605615827fd9a545609ff269515827fd9a4c5609ff26931582efd6a4c5609ff26921583bf98560160dfe65580583ef96460160dfe64d80583ef96160160fbe59510582ff98a44160 else 0xfff5c910583ffd5244160fff14910583ffd3244160fff0c910583ffe2244160dff685304037fd8a48100dff4e9204037feaa48100dff685204037fd7344100dff609104037fd5244100dff4c9104037fd3a44100dff4a9104037fca562560dff28d895837fca262560bffaa9855837fda961560dffa65855837fd895d560dffa65755837fca265560dff62655583efc8695560dffa65845837fd895d160dffa65745837fd955d160fbf595745837fd8565160dff5d594583efd8559160fbf5d564583efe5559160bffaa9835837fda960d60dffa65835837fd9460d60fbf591835837fe995cd60fbf591735837fd7464d60dff289935837fd7924d60fbf59493583efca258d60dff625535837fe9954d60bff62953582ffd7a54d60dff669535837fc9a54d60bffaa953583f7d8554d60dff651535837fd8914d60dffa6453583efc8614d60dff625435837fd7950d60dffa6543582ffd7a50d60dff626335837fd798cd60fbf21a33582ffeaa60960dff6a5825837fca960960dff5e5825837fe9960960dff65182583efd6460960eff60d825837fd895c960dffa65725837fd955c960fbf595725837fd945c960fbf591725837fd935c960fbf58d725837fd8364960dff28d925837fc5364960dff50d925837fe3364960fbf59492583efd6324960dff625525837fe9954960bff62952582ffd7a54960dff66952582ffeaa54960fdf5d5525837fd9454960dff64d52583fed7254960dff624525837fe9914960fbf218525837fd9414960fbf590525837fd9314960fbf58c525837fd8950960dff5e5425837fe9950960dff65542582ffd7a50960bffaa942583fbd7450960dff625325837fd794c960dffa6532583efc864c960dff65532583efd654c960dff65132583efd644c960bff629325837fd9a4c960bff56932582ffeaa4c960ffb609325837fd890c960dffa6432583efc860c960dff65432583efd650c960dff62622583efc8688960dff65622583efd6588960fbf592225837fd9388960fbf58e22583bfd8260560bff62971582ffeaa5c560dff625715837fe995c560dff655715837fd945c560fbf591715837fd935c560fbf58d715837fd8764560dff615915837fd7564560dff955915837fd8464560dff5d1915837fd8364560dff5cd915837fd5364560dff14d915837fd4364560dff8cd915837fd8264560dff5c9915837fd5264560dff149915837fd4264560dff4c9915837fc3264560dff88991583efd8758560fbf61561583efd7558560fbf95561583efd8458560fbf5d161583efd5458560fbf60d61583efd7358560fbf54d61583efc5358560fbf50d61583efe3358560fbf5c961583efd5258560fbf14961583efd4258560fbf4c961583efc3258560fbf889615837fd8954560dff5e5515837fe9954560bff6295158) else (if i < 3 then 0x83ffd8554560fff5d151583ffda454560fff60d51583ffd7354560fff68d51583ffca354560fff54d51583ffd4354560fff8cd51583ffd7254560fff68951583ffca254560fff54951583ffd4254560fff4c951583ffc3254560fff88951583ffda054560fff60d41583ffd7350560fff5c941583ffd5250560fff14941583ffd3250560fff88941583ffd854c560fff5d531583ffe554c560fff61131583ffd744c560fff55131583ffd8a4c560fff5e931583ffd5a4c560fff16931583ffd4a4c560fffaa931583ffd834c560fff54d31583ffd824c560fff5c931583ffd524c560fff14931583ffd424c560fff68931583ffca24c560fff4c931583ffe224c560fff68131583ffd8748560fff61521583ffd7548560fff95521583ffd8448560fff5d121583ffd5448560fff60d21583ffd7348560fff14d21583ffd4348560fff8cd21583ffd8a48560fff56921583ffd4a48560fff4e921583ffd8248560fff54921583ffd3248560fff68121583ffda760160fff69580583ffd7560160fff95580583ffda360160fff5cd80583ffc5360160fff8cd80583ffda260160fff5c980583ffd5260160fff14980583ffd3260160fff0c980583ffe2260160fff68580583ffd5160160fff48580583ffd935c160fff8cd70583ffd825c160fff68970583ffd925c160fff4c970583ffd815c160fff68570583ffd515c160fff48570583ffd8754160fff62550583ffd7954160fff62950583ffd8554160fff65550583ffd6554160fff60d50583ffd7354160fff64d50583ffd6354160fff68d50583ffd5354160fff8cd50583ffd8254160fff5c950583ffd9254160fff58950583ffda254160fff54950583ffc3254160fff88950583ffd8154160fff5c550583ffda154160fff54550583ffd3154160fff48550583ffd894c160fff5e530583ffd854c160fff5d530583ffd954c160fff59530583ffe554c160fff62930583ffd7a4c160fff56930583ffd834c160fff5cd30583ffd934c160fff58d30583ffd824c160fff5c930583ffd924c160fff58930583ffd524c160fff14930583ffda24c160fff4c930583ffe224c160fff60530583ffd714c160fff54530583ffda14c160fff4c530583ffd214c160fff62520583ffd7948160fff61520583ffd7548160fff65520583ffd6548160fff95520583ffd8348160fff5cd20583ffd9348160fff58d20583ffc5348160fff8cd20583ffd8a48160fff5e920583ffd5a48160fff16920583ffd3a48160fff0e920583ffeaa48160fff60920583ffd9248160fff58920583ffd5248160fff4c920583ffd8148160fff5c520583ffd5148160fff4c520583ffda148160fff48520583ffd8744160fff61510583ffd7544160fff95510583ffd8344160fff5cd10583ffc5344160fff8cd10583ffd824416 else (if i < 4 then 0x60fff69d83583ffda560d60fff5d583583ffc9560d60fff95583583ffd7460d60fff68983583ffda160d60fff68183583ffda95cd60fff2a573583ffe995cd60fff61573583ffda55cd60fff65573583ffd945cd60fff5d193583ffd7364d60fff61493583ffd8954d60fff5e553583ffe9954d60fff62953583ffd7a54d60fff66953583ffc9a54d60fff5a953583ffeaa54d60fff61553583ffd9554d60fff65153583ffda454d60fff60d53583ffd9354d60fff68953583ffca254d60fff68553583ffda054d60fffa6453583ffd8950d60fff5e543583ffd8550d60fff5d543583ffd9550d60fff95543583ffd798cd60fff61633583ffeaa60960fff69d82583ffca960960fff69582583ffca560960fff5d582583ffc9560960fff95582583ffda460960fff5d182583ffda360960fff28d82583ffc9360960fff14d82583ffd4360960fff8cd82583ffda160960fff68182583ffe995c960fff61572583ffd845c960fff65172583ffd835c960fff54d72583ffd435c960fff5d192583ffd7364960fff54d92583ffd4364960fff61492583ffd8324960fff54c92583ffd5358960fff14d62583ffe3358960fff62552583ffd7954960fffa6552583ffd8a54960fff5e952583ffd9a54960fff26952583ffd6a54960fffaa952583ffd8554960fff65552583ffd7454960fff65152583ffda454960fff64d52583ffc9354960fff68d52583ffca354960fff54d52583ffd4354960fff8cd52583ffd9254960fff68552583ffda054960fffa6452583ffd8414960fff65052583ffd8314960fff58c52583ffd4314960fff62542583ffd7950960fff5d542583ffd9550960fff95542583ffc5a50960fff64d42583ffd9250960fff61d32583ffd894c960fff5e532583ffe994c960fff61532583ffd754c960fff65532583ffc954c960fff59532583ffe554c960fff5d132583ffd944c960fff62932583ffd7a4c960fff66932583ffc9a4c960fff5a932583ffd5a4c960fff16932583ffd4a4c960fffaa932583ffd834c960fff64d32583ffd534c960fff60932583ffd924c960fff54932583ffda14c960fff68132583ffe990c960fff61432583ffd650c960fff61622583ffd6588960fff61222583ffd9488960fff60e22583ffd6388960fff54e22583ffd4388960fff5d581583ffe5560560fff5d181583ffd7360560fff54d81583ffc5360560fff50d81583ffe3360560fff5c981583ffd5260560fff14981583ffd4260560fff4c981583ffc3260560fff88981583ffd8a5c560fff61571583ffda55c560fff61171583ffda45c560fff60d71583ffda35c560fff54d71583ffd435c560fff8cd71583ffd525c560fff50971583ffda05c560fff5cd91583ffd5364560fff54991583ffd3264560fff62951583ffd7a54560fffaa9515 else 0xfff5d153583ffd5360960fff61152583ffd8354960fff58d52583ffd8254960fff61d42583ffd8454560fff60951583ffd8250560fff61d31583ffd5348560fff54d80583ffd7160160fff4c580583ffd315c160fff4c950583ffd874c160fff54d30583ffd8748160fff54d20583ffd5344160dff605304037fd714c100dff58d204037fd5348100dff605204037fd3148100dff60d104037fca35e560dff95594583efd7458d60fbf21953583efd6a54d60fbf59153583fdd8354d60dff5d1925837fd5364960fbf21952583dfc7a54960fbf59152583efd6354960fdf54d52583fed8254960fbf59542582ffd8a50960dff65222583dfd875c560fbf59571583efd8258560dff64d41583efd6350560fef50941583efd654c560bff5e931583ff5814c560fbf58d215837fd9260160ffe69d80583ff95360160ffe54980583ff97160160ffe4c5805837fd925c160f7f5c570583efc864c160fbf59530583efd634c160ff754d30583ff9804c160ffe5c130583efc8648160fbf59520583efd6348160dff64920583fed5248160ffe60120583ff97048160ffe4c120583ff92044160ffe61110583ff95344160ffe549105827feaa58100dbf595604036fd63581009ffaa9304027fd8a481009ffaa9204037f930481009ff4e9104027fd2a441009ffaa9104037f920441009ffaa9795827fd7aa65609ff56a995827fd4aa65609ff4ea995827fd2aa6560bbf69486582efda3219609ff2a585583ef8a0595609ff629945827fd7a651609ffaa994583ebd84591609ff2a5835827fca95cd609ff5e9935837bca464d60dbf591935827fd9a50d60bbf5a9435827fca9609609ff629925836fc8664960dbf58d925837f4a1649609ff269525827fd9a509609ff269425827fd9a4c9609ff269325835fd795c5609ff5e9915827feaa64560dbf64961582efd6a545609ff669415827fc9a50560def65141583ebd64505609ff66921583ef96560160efe61180583ef96360160efe605805827fd9a541609ff669305827fd9a48160fbe59110583ef96344160dfe64910583ff15144160ffc50510582e7da521960baf69086582edda321960bbd68486583ffda461560fff68d85583ffda261560fff68585583ffda061560fffa6575583ffd7561160fff95584583ffd895d160fff61574583ffd955d160fff5d594583ffe55651)))
def getRecipe12 (i : Nat) : Nat × Nat := let a := packedAt rawRecipe12 (i * 42) 42; (a &&& 1073741823,a >>> 30)
def rawRecipe13 (i : Nat) : Nat := 0xffebcac1ffe99583ffb0ab07ff59560ffec22c1ffd74583ffb28b07ff60d60ffeb9ac1ffd63583ffaa6b07ff50d60ffec12c1ffd62583ffaa4b07ff50960ffe992c1ffd81583ffae2b07ff54560ffea0ac1ffd31583ffa42b07ff60160ffeb82c1ffd50583ffa60b07ff48160ffe882c17fd60402ffa60805ff48100bfe882017fd89582ffaf2b05ffa6560f7e432c17fd95583dfacab05ff65160f7eb22c17fd93583dfac6b05ff64960bfec8ac1efd61583ff300b07fe44160ffec4ac1ffd75583ffb2ab07ff25560fff2aac1ffd93583ff926b07ff14d60fff19ac1ffd72583ffb24b07ff24960ffe292c1ffc32583ffc44b07ff64560
def getRecipe13 (i : Nat) : Nat × Nat := let a := packedAt rawRecipe13 (i * 31) 31; (a &&& 1048575,a >>> 20)
def rawRecipe14 (i : Nat) : Nat := 0xffd607fd00
def getRecipe14 (i : Nat) : Nat × Nat := let a := packedAt rawRecipe14 (i * 20) 20; (a &&& 1023,a >>> 10)
def opsAndMask : Nat → Nat → Nat × Nat
  | 9 => getRecipe9
  | 10 => getRecipe10
  | 11 => getRecipe11
  | 12 => getRecipe12
  | 13 => getRecipe13
  | 14 => getRecipe14
  | _ => fun _ => (0,0)
def requestedBudget (k i : Nat) : Nat := 1 - packedAt (signedBudgetData k) i 1
def signedBase : Forest := ⟨511,14,fun j => deadsamples[j]?.getD (0,0),signedColumns,deadautos,
  signedLevels,signedIndices,shapeCut3640,shapeCut3640_sound,some opsAndMask,some signedRules⟩
def signedCertificate : SignedForest := ⟨signedBase,requestedBudget,[(17,272)]⟩

def rankDictionary (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0x8052046610270046410653624400f83046408164046708052046410563046704053049720271049701253046404643046008462046008162049010231c88c00f85c22800f72046010273049440084046401864209400f8504d600450641600f84514100f93049101642e09000f21168120f9404d600410046680862430400f83211000f61046010573046601865046201684046601831046e04687046a046870465029420493040640493202710494404807c0700f21ad0240f50812800f32046c08754046508054049410231612400f3204d600075524400f10049010362046e08054046c0485304681075304680485304661065304e600586090000f32046640431049680420224000f83a09000f85a48800f2104d200410c12800f32701600f61528500f40049104064046010753305000f43049e04074049e08520049640287046340042049020384046a01684046c08574e41c00f85e44c00f83d80c00f3204982038404920407404960407404950015204d600283049204470046410753046680042049700142046408462205000f43a28200f40302000f64222000f62432420f3204ea00586c22000f72302000f32046210720548100f94605400f7504600857420a200f86046310620046410273382000f54105000f65046402582049604470702400f64e68240f40750500f50046408574046008754049080453049900152049d00152046520230046540931150100f50550100f50528100f40049708520049704530605400f43011000f61046610720049201742046604053046410573046004587e05800f75046402342c24000f83728100f40222000f72049240480482400f5004ea00386704400f74a68240f40046410680690600f50049700241049420384424400f83046110620049604530049601742049640840e28a00f40049104460046708054046608054412000f32046408754c24c00f83e28200f40702000f32205000f7504e200586049604430628600f40612600f32049c20384046e08052049080354228200f40049601253030000f83301200f61049304560049820473550500f50424000f83728300f40049480453501400f61049a80420046e04053046c04587024000f83009000f21049a40480c24800f83049608081422400f7204de0045004964008404924008460a400f86046301264422000f72049420374049608520e05000f43290200f50049020473049020374682600f50605000f75628200f40212000f32e05000f75049608580049640782212200f32049c80453049480354609000f21101000f61e09800f85609400f21022000f72209000f85305000f65605000f43049420473412400f32c32c20f32702000f64609400f85209000f21704000f74049e0125304ee00386e09000f85012000f32609000f85 else 0x104650494104630805404ee00850e81c00f21046001384046601681241000f8504950057040a400f40049601752049601853504400f61705600f6504930446004e600386710600f50514500f93782400f54046700163046220230046001231046208054312300f32049c20382046804587046e80682046810573830800f83046e01831049440287046402852049020182046404853049410631046201381622000f620496081800466045816a8480f84322200f72414400f10049301642046440571524000f1004e600750205400f4304e700340049680140049604078582500f90046002382046280862e68a40f40e90a00f50046510260046401384046520640046640571049601352046408162046004463046304053046a80042046c10753046802382e05c00f75046c08752046c02752046605863046408654046210163046402382046410860046702576660600f10781601f32049700672705400f65046402752046004643a90200f50824800f83e28600f40049640480046640341268240f400460045814c8080f8460a600f80548500f94114100f93508000f21046604051046640751128100f40046440751350300f50049280420505000f43705400f43424000f73046204687046240571049204430046210160049e40782049a40580049a40782049880354046c0258204944078204e104497046102942690200f50124000f10728500f40049520176049180531022000f62046110260612000f32046601684702400f32049020271049240287046610160046604863382000f32049700631049201253049208120046010160049c10231046c10573046a80682049880453f81e01f3204928082004600275204640485104d40087504960286304970135204e300650722600f7204e100475049680820049410362046002852046002342014000f100a4000f10049900251822000f72f01800f4304ec00832e05800f4304950076240a000f86049104560046120320482000f50049202364046120230049502963049440243046c10853a41800f85046c023822d0240f50668240f4004660856404e40057204661068004da00410a09800f8540a400f78046208052046240341a05000f7504604898404600a896049208520209200f21244000f83780600f32409000f21a90a00f50049a40084049c2018204612064004614093140a400f86c30c00f83049e0175204640186560a000f86428400f40046240431049540420046404587046201274049304430411400f61049440342049204570224000f73214200f10049604876109000f7504920236804940a968049510291282200f50409000f85049404876046604687046140042049500672046601274304000f740491086910462800420a8080f40c12c00f32e45c04f85046c023420466) else (if i < 3 then 0xc20f21e09800f21049108570e09400f21622400f86750300f5004e300275424400f7320a200f80409400f2104d600180049501253309200f21018000f72046101374049208081014000f5104da00540e48400f2104d004470205400f75082000f50049508520049601342046201231494080f83182000f64241200f84282080f28011000f51c88400f85049c80354049e08580049a04470049c0858704620405104650294004620183104e500475049100460501000f7504930046004918014204918024104e120397046408642611000f610460012710460a003104e20148704900812000a000f40a05000f430496c042004e600861046608164049404470046610860046244053134120f3920a200f7804620238004970013004930013004e500390049402463046520320422000f62046500276049240782046401684622400f78049500470046408982046602430046504491049701342049620281721600f74049620463722200f72412400f7269a608f08049040480046008164049204530182000f32046204643046004543046208654f81880f43432410f7804620127104604805404661075304660234220a200f400460487810464488710467007200497007420465049434a8080f480467047415a0500f900b0080f9004620234204624805404ec0057204d8008750464101604d0440f50046280082049202765645404f85049680651141000f21046240751632620f3204d600243046602830049408120049420671049104430049504430049040342049380142505400f91582100f90028000f40049281542046701273090000f50046a04041a05800f75c22c00f72049605876049644580534120f39049202863046201865682200f50049500460222200f7204970456004d4006754e80a0f8460a600f86328300f40505400f65645601f8304640168104d600132222200f62505000f6530a400f703c0300f21580000f64534120f93321300f74611400f6169a090f28049300762049020281009000f85281000f21328100f40301000f61305200f65046250270028000f72046204041049100152046201681049608120046620230046210270104000f75094080f30046680682109000f21e48c00f21812000f3204680275204964443004e10039004610239204650405304e600850024000f7304934042004940818004e700275046640872409400f85046401381046502396049620671049500251046502492049500276046408892722700f7204660484104930014204e200432e90200f50049c20473046c02852824000f83049820374046660230682400f50046101264049420281049680354049208580049500064049201352049720176049401853049010160701400f61046202830049220374624000f73411000f6104630407 else (if i < 4 then 0x8240a000f4004610173104e008164432402f83046282385046201384684200f81701000f750240907610460a083104610407134a308f07088000f8504920a857049081532a05800f43694410f81505400f43049240580568120f94605440f75046202582049402863049220182488400f85701200f61049500074046600741046201641049608681049610631046308052046500651750700f50309000f75694210f81509000f750497805410495206710494204630466012316a8480f48568120f49384000f6460a200f80648400f21311000f51049090560581000f21704400f100a0000f21046002582046004851083000f32112000f62a28a00f40046c10273504000f75046d0027304681027304648068204600247604621068020a201f86046201471046604041049700031046210860046640185049404430622600f7804650805204660487604661018304620257204e20008304662032004654039104660816804e60008304672023004640486304e40078104641016304610449104660865404e600340049700460046502496046640831412000f7204674057104654057104e100490046604543046210263046004576046010680046208164046004541d04800f75b01800f43890800f3204ec00583d80400f32049d0025104d100510450401f83046648052490440f50049120370049480651490400f3204660258004962017604d004876049140420046004853049220172046610120009400f8504962017260a200f8604d208087049408641049504560614400f10049410750049402765224200f73582400f50682600f08682080f2804d300450049280651112100f3260a600f40046700273049044074049244470088200f82f01c00f43046a40751046a01681e09c00f8504dc00875049a01742c8a402f85ed0240f50046a40571049e04570822800f7204680857404dc00732a50800f83e41800f85046808754049500031049500130049504064049420182046010263049604570046202576046202852049001342049001742046001681228600f40046720430046001684050000f1004640238004640458104674004204960268504d60054004940407404d600186628400f40046410853049700276641400f850496203740497007620495086915a2500f920c8080f84488600f82582000f32049602368148100f94049408580049408587049420382046301731430000f83308200f2104920175220a200f28405000f75049520379049280354046202652705500f6504d60006104d200132046404463548100f49694080f38049680041694280f3804d400621049604018049001853005000f43105000f43005000f7504e3000730460086420492202810493002511a8080f40304000f63184100f91388080f400462c0042e68 else 0x609600f85049504530644400f83049420176602000f6204e700650049404530049220473046202372708200f2104d5006940496048703e0380fa10495013526c0200f21049280140704600f1004e50027504618062004e080380049504419049120176046700573694480f3804e08026a384100f1004d400132534522f3904d60062104904008400a000f86083000f54046001541309000f21390080f52046201864290080f30285000f54085100f54049e0174204d20051004d600510049602765049402364728600f21430000f73014000f61049020261049604830780000f6404620a78004600164104600a7800466480546d0240f50108000f2104624004104e200386046601471046410270444401f83046204053049040287046410720049610231046480042048000f2160a600f78248000f2104964038260a400f7804970047004660186404962038204640405304601498104660146804629021804604043130a300f70046004041301000f75046010270185000f54046448984046160391046701264594480f300465c0591046448981046310260325301f7a360100fa1046682842046282a650467047430460885200490a0310049081531049084950049181531049181241049181542049c20374049a04074049820182049a4028704e800583468440f4004e4107800492c042004e21078004e2081640462023)))
def prefixTable0 (i : Nat) : Nat := 0x2800401d21086af832800401099eeaaf4028003bdd20e84af7228004060a1f00e38228002bc415e43005328002bcca1f24af43280040a060682ef63280033d89c462ef702800420c60708af8328003858a0e40af402800405ca02caaf722800419c5c4e2c43028002bc415e42cf6128002bcc99ea0af4328004118e0086cf64280033dce0460cf85280043d9608c0af8328003898d9eeaaf40280041601cae0af72280040dd1c8a6e16028002bc415e42e85328002bcc9c082af43280039d49c684e051280033d8a04a6e320280043e4e1ea8af83280043e1202a4af4028003bd45c240af72280039d4e0ca4c43028002bc415e42cf6128002bcc99ea0af43280038151c4e6cf64280033dcdde60cf85280041d460840af83280041d519eeaaf4028003bdd21f0caf722800415c606c8e38228002bc415e430f8128002bcca06a4af432800421460a40ef63280033d89c462ef702800414c20c82af8328003858a08e0af402800410420c62af72280041909c4e2c43028002bc415e42cf6128002bcc99ea0af43280040e061ea4cf64280033dce06a8cf8528004090e06e4af8328003898d9eeaaf402800409d9cae0af72280040191c8a6e16028002bc415e42e85328002bcc9c082af43280039d49c684e051280033d8a0862e3202800409460aecaf8328004014a04c2af4028003bd45c240af72280039d4e0b0ec43028002bc415e42cf6128002bcc99ea0af43280038151c4e6cf64280033dcdde60cf85
def prefixTable1 (i : Nat) : Nat := 0x400030181010081807060b0280e000e044709030009020080c0608438308e000a14040002870101008180604430410e000c101502038141020080c0601030010e000e04140003044101008180604230608e000c19060c0b0241020080c0707030020e000a14040002870101008180604130040e000c188502030409020080c0818030204e000c1844000301810100818080b030280e000e14170d030009020080c0608438120e000a14040002870101008180604430410e000c101502038109020080c0601030010e000e15040003044101008180604230608e000c19060c0b0241020080c0710030020e000a14040002870101008180604130040e000c188502030409020080c07000b0204e000c184400030181010081807060b0280e000e044709030009020080c0608438308e000a14040002870101008180604430410e000c101502038141020080c0601030010e000e04140003044101008180604230608e000c19060c0b0241020080c0707030020e000a14040002870101008180604130040e000c188502030409020080c080e0b0204e000c18440003018101008180801830280e000e14170d030009020080c0608438120e000a14040002870101008180604430410e000c101502038109020080c0601030010e000e15040003044101008180604230608e000c19060c0b0241020080c0710030020e000a14040002870101008180604130040e000c188502030409020080c07000b0204e000c184
def prefixTable2 (i : Nat) : Nat := 0x202488118c09c2046202488119009a2046202488118c09c204620248811920002046
def prefixTable3 (i : Nat) : Nat := 0x50c2c0290a000e0628032b8624a000c1e080a0b8348a000a1c170f0b0514a000c0e1704a30714a000e08980d440660a000e16160ca30708a000c0a1707138630a000e1b450c2b0648a00100d4608a38360a000e1ca6042b8720a000a1c1706140330a000c04560d0b0314a000c1a46082c0260a000c0c181c2c0740a001007280a538014a000e08a50c2b87c0a0010149708938668a000c1e07030c03c0a000a1c170e230514a000c0e1808630714a000e0e08084c06c0a000e01460ca30708a000c0a170f138428a000e1e850c2b0648a000e1cc608a40460a000e1d26042b8628a000a1c1809138618a000c04560d0b0314a000c1a46082b860ca000c0c180b140128a000e19c8010b8230a000e1e450c2c0318a000e06280dc38624a000c1e0800538348a000a1c170f0b0514a000c0e1704a30714a000e089805440550a000e16160ca30708a000c0a1707138630a000e1b450c2b0648a0010058608a38360a000e1ca6042b8720a000a1c1706140520a000c04560d0b0314a000c1a46082c0094a000c0c180d2c0288a0010018800938014a000e08a50c2b87c0a00101a2708938668a000c1e07030c0548a000a1c170e230514a000c0e18064b0714a000e0e080a14000ca000e01460ca30708a000c0a170f138428a000e1e850c2b0648a000e1cc608a40418a000e1d26042b8628a000a1c1806238618a000c04560d0b0314a000c1a46082b860ca000c0c180494018ca000e19c8068b8230a000e1e4
def rankFormat : Nat → Nat × (Nat → Nat)
  | 0 => (8,prefixTable0)
  | 1 => (8,prefixTable1)
  | 2 => (4,prefixTable2)
  | 3 => (8,prefixTable3)
  | _ => (0,fun _ => 0)
def rankHeader9 (i : Nat) : Nat := 0xa26b1515805
def rankPayload9 (i : Nat) : Nat := 0xccfc033310088fdcb63f7c3e8efb9058c4211f62057bb6
def rankMode9 (i mode : Nat) : Nat × Nat := let v := packedAt rankHeader9 ((2*i+mode)*11) 11; (v &&& 7,v >>> 3)
def rankHeader10 (i : Nat) : Nat := 0x94b252938e52714a333946652854e50a949fc393f85278ce4f1949d0393a0526dce4db9499839330525f8e4bf1496530000123e9c00004868900001200a23f69c722a8e167191aa3149c545b8a52711fe4000043e49879c70d3e4000042b29854e70942211a9c182a00001046de0809c09d800001003a400003f7c900000fbd6400003e49900000f799c00003d3aa7a466f301de549bc4b878806eede5dce9bb2a8763e6eb2dc00003a428746e6e65e9cc39b8d8a718e6e0b29c0d9b7a686f366dc8e9b829b68a76ce46d74e5ae41b55da6a8c6d2629a429b3e4a67b26cdca0000032e88659a6c8e60000031a3900000c39680000303ca00000bf75d7e91af7b85ece6bc45577d1ae6d85cb46b76616e29ad4b85a746b27a800002c46958766af6655e39ab5d9568e6ab0ed5591aa49954626a7a554e99a92fb00000a28a40000281a9000009f21d3d99a75084e7669bba136e9a67784cd8697b292ec1a56d74ab06924ad2391a40f747e268d0e91961a284944e06881a10f91a154a427a6832a505a9a0208402c280304ffb99f40a3e4e679f24f3299dcd800000748e4e8799ca683912671254e1a99b64b36a8669cecd2f19a5413484666e60cce1994f53266662420c3e197b7a2f3e65be64b739964892c5e657164ad61954492a5e651f2c000013db9000004d7e4000012e29259064945c91b1919d823246447a0885990998211c64109c81398f9881ef663c91c78818e8781cf8637ea46f018d5891a84633c9c66b98c79718b862e9ac5c898b0c9000002ad5c00000a1d900000266204c21890c711ea622b14447987f580fac61cc243899868480cd26174202de1853280a24610fa820e983c95077c60c2e81761826e7049e6068e40c2180f6701ae600da00168802410036200484004880001
def rankPayload10 (i : Nat) : Nat := (if i < 1 then 0x97e24cb6da49eb4ca63112bb2308b9c45653793bd23a7d0f256e91d31a1fb653df0959163e5563d7cb6bd2c9efc08b26e952f9d2a5f2f452baad0c58e4660b793bd2ec7af96df09de4257fa0e109210d31a061268ba9d9b0603f8937cce373b9a62ae0e81c23bfb464e63befef60c64fa888c610913d064fa8847900c3a4bf2b06d33186c48ba1e141361ca29dccec853f1ab6c3dad508c919ff41ce4ac9b7029239d2c16681145d56862c3832a3ba54be7cc02088c3a7088db0f9c9732674217c3e997dae47ef57d5aa7b8e8151b08c9ee38e2fe1f0f22862244b13ed50b416489264d32ffa161a4a89d2a7c3e6bfc8141954db11950c989d438feb3988424f7ed64b723f61516437427456c264cb798d677c8e431df3cdfbd2f1084a6fb8e740dea1848a9e6a4e59cdcc84843431da667e02d849a867ea12a02d74aad1048ded451d0654aea0fcc254c1af955a20be7b5ccf4197d9d07ef0d53ff91da3496d84a286d6169dcd7623d8a676818ea737252a9bfa3c0c85954ce8a24b29a488a286437d67188b2bdbc31d14d62f672444d433ac511187088fd3212fa22e928e22afd3f6a9ffa16144839c1f6a9ffa16169258d1df49c5ffed38bffda71dfeb3aa2c86e44e8a621092d941965dd66fca8194fe9d09d15d65e119761e23efc4735fbf100df3a9fad1a93963c3f35577462a7a8aa57d09020b5f93c9f7b2b16f6621cb3d148dbee3a19df27da12bedfefda37b581a8aeb1e2cd685aa16b27d0ec09094c60f3408a469ea107593e85a46c55dc1a6da4f55d6c6cfb4b4e2761c5fbed3b7ffb4e472c3b58967431d1581c47d9e74b0ed733fb4c20d8c96ab7b219533b5abc4d84e468c54ce8afb3a1b094a5c3a9bfdfb4e6c8cfb5896761e236569d676da53693b0eb077a44ca8581be746de4f55bd0e4b6c8650c788b876ae8cbeab2eb04283f44a3a08cfa9a47f90c189f22490de88a87bd994a711f8059dc8c605b2943db2963da6390d21c421b3c59e8a464fe4fbe1fdc72cf45682af85290e647d14c8fa28118fd6761fd2c87fd6736596decd23961fdc76ca55f433bf2fb21ff59d94d7f2faebcb6e3291db2157d4f7e5f533f8be6cd25991f2ce47fd6774ca4774d64b53ca966c7e68d0479c8ffaceb6ff53ca6b27adbfd4f5d359db81931c6832a3ad27c8e717d0c4ff53c21282717d0dc0818e6c7e7370283e1a7f31a7a748d693e637ed9c354496dba1946cd22d21bd13fa4ef24fec196289f41c0c7f71cb0fe839094f47dc14ef2cd330bed6450d280cfb04f07de41746cad94361ee792b7936b24a45593be8bac92bc9b75a92b68adbc5fbc1b75a9359d1b5827f47d3f22be511572d2b3a2eb24a457a2b7936a663f76c922c4f9d12bc9b37df71c922e2d9c55bdc72c0a496cee547221fe477c2be575a3fa16c873229a0d0613098244 else (if i < 2 then 0x94c8c605035143b1256cea4889a867d8a01a18385318bb6a0d1882e9851bc67762d049d14f0127b28e5364464835a3fc86fefb0341250df2390d57ffbe02d2943c77cf11229606f9d133f014a544a858c2454f1a0818e06f50e18c964455832a16d2238632495f7c465929834d0505fb1557c992b3b7d4831097171398ea7432decce7aaefdfa1f0ed6fff69c28e533c232e93c4694a1e3be79d6757988fd12bc46af39f911bd2a08196f924063bf8a56e991e80b70ff05bdd8909286eb589e8d037a0496374df5bffddf2318121fc650618b698e031cf646302d2fd6934266fe21513fc16c3c4118b58d6361e23a13065bda9dbc54682dd0f48ac3c47b57b684dd09842deec48519761e2204fc99584759c5e817453e66770f1204b8b907a5947f69db2963cc827219becf3918c09a98cb04845431909086e777e321d911ec35319633318107758282fa1d6ca1d24a25b18e57e6e8c713212a49f8197192b26141260c6432274638957f622ca43e79941962da6390c73fdbe94a1ed2694d2788544fd2d62fc7213859097d69251531b5ac4d040cb7c92431df3ca51ca6fef80b70fd27e4f82cb0304194ca035b1404fc9f05aa141e511832dfdf61490b2a09f456b1ca6b47f90dce5e024f4327b3e7d2c39b230e9d95d33a794c8c7f71db6caf92be7495f3a32290d488b2bfbe0277f4521b3cc90f62f58afbf10ee788469d4abe4cfc04d86f58a5340d854d02acb925627cd4431face86df56d023f96c62a4f14ca437f4a96b62808c5d9e09c7eb39f93a58fe68e04843621404a78470255730196c7f3589f3470281d12b0b9b14ccfca1c0a0188a57cf687091dce609f457cf6b212a85a41f18c96ca0beb07bad5075cb3279250e3f40ec0745395fe9895ab9e5f501168c8d02d74aad1048dad451d0654aea101b756b707b95f50ac66e18f53757f01c89d757c46b06be556882f876b99e832fb3a1f6ca7476cf1313e44427f69df698455bd1a4b6c251436b0b4ee6bb11ec533b40c7539b9a0fd32421844fb5fcaca7e8afefb0da0beb64e83a81f691232e90e209949ecf4cce9a9ac13ed11a79d6554532417f92b6a320c62682ff2caf2471d0b87c949e48f7abd0eb26b55848f1047a9a3eb7fe1a031e5de0ce814050e7acc4c828128e0282fc15ab26dc3c4157dc6a4ff05b683cc1dc106157dc7db899949f521db2becfec19f6bc03161dc286289680d891a2b6428c3bc9cdf058504abc93fc16641e625f6fed6266f82c582fcfe6538b192664c341581d3f03aec43fc166fed38bf12db142cb830c397df41ce82b039bfb5d8fceabf142e2c7dc40f81c1c4260c32070858fb9e5d51f7151f70e05953f3a150e09f2aa7e693e521cf09d4fbfbc5f8081dc1f84c31da782a40e110f7313328112e61908f200a59c3251fd830a09b0e517dcaa288f15 else 0x20cb1fc9f7255f69d3afb4ebb7d6b6838871a79d7253fb569cfed5a65f59d20fe0d0a76301b8623a1ec84e1084d3bd9a573828a75d1a7c23bffbcebf4b96c1ab219f02dff8226094e55a2161791d41861dd93da34429ecfa74c9f2a3be6fad91b12114be033cf3a14454a32c694286d277081ba1d4518bfe85b3b7d79054a3743f78a4dff53d3d3a46937fd4f0ecd43744415f1929c6cec8df4ea2c61da996034f87d872f07c747e2db06e0da0f7c1f2992beb07dc2f4457884087213a8a78083c4d7223041ad1fc4c8f582a092865c3f88425c5c4e639ddfb339eabb4afa08dad323d61490b2909f456b6ead1fc5911850cf01079b0deb14a680a682acb9253612fff68c3840ec88c286427d148ded642550b2e1fc5c7e4ca0bebe4701ab18f0647a02d2fd1dfc6fff68c2b746d19737f11a5fa3bf8f6bd6e83981f691232e6fa205a912b67596ce99445))
def rankMode10 (i mode : Nat) : Nat × Nat := let v := packedAt rankHeader10 ((2*i+mode)*19) 19; (v &&& 15,v >>> 4)
def rankHeader11 (i : Nat) : Nat := (if i < 3 then (if i < 1 then 0x832465c82461432451c7244f0324338b242e83241c07241943240a0724044323f10823ee4323cd8b23c78323a38a239f03238d87238ac3237248236dc3235a892357c3233b4b2336832327872323032312c700000022ef4b22e9c322cac822c80322b48822b1c3229fc8229d03228b4822874322728700000022528b224fc322384922338321fecd00000021d18b21cec321a84a21a5832187492181032163c8215bc3214307213ec32113ca21110320e1cc20df0320cf8520ccc320a94a0000002083ca207c43205889205343203b47203883201b492016031ff8491ff3431fd8491fd2831fa50a0000001f8b491f86031f5c0b1f59431f328a1f2fc31f0f091f07031eea881ee3431ebf091eb6c31e8d491e8a831e688a1e65c31e4e881e49431e32491e2bc31e018a1dfc831dd04b1dc8831dabc81da9031d794d0000001d55ca1d51831d2f891d2b031d14871d0fc31ce00b1cdb831cbac91cb8031c950a1c92431c630c1c60431c51471c4c031c34c81c2c831c11080000001becca1be7431bc08a1bbdc31baa071ba5831b95451b8e031b4ecd1b4ac31b140c1b10031af5481af1031ac44a1abf031a91ca1a8a031a60091a5a431a32cb1a2cc31a0e0a1a0b4319f5c719f04319d58719d2c319be8719ba4319a087199dc3196e0c1969431946cc1944031908cd19060318eec700000018d80700000018b38b18afc31896c918940318798918738318518a184ec3182a0a18274317fb4b17f68317e14717dc8317cec717cc0317ae0917a803178549178283175d8a175ac3174d071749031726091721c316f9cb16f4c316d30900000016b54816b14316854b168083164d0c16494316248a1621c316064816018315d1cc15cc0315a30a15a0431589c715844315508d154dc31528c91520c314f10c00000014cb4914c88314a54a149d03148808148543146c481468431445ca14430314268914208313f68a13f3c313d9c813d50313b749000000139748139203137309136ec31329cf132703130b4813068312e88912e3c312ae0d12a783127ac9127503124bca124583121a4a1214c311f24911ec0311c2ca11be0311a0c8119a4311764800000011478c1136c711099000000010b31910850c1015990ff4490fbe930f9d490f9ac10f6dca0f2a120ef48d0eba8f0e9e490e4b130e3a070deb930dd2480d80130d51cc0ce0990cc4890c56190c32080bc3160ba60a0b65950b4f890b1b510b03c70aa6950a87480a2e140a03c909a2d40984490951900932ca08cd5808a3cb084357081a8907de4c07a5cc07099d06f147069f11068388063e94061d09061a8105fa0a05f78105d189057892055a87055801053b4804d454049e4b043557041bc703b21503980703385502ff4b02c88d02a3c8023d93023b4102390101ed52014b6200ccd6000025 else (if i < 2 then 0xc2483abe833a950a3a92433a7c893a77033a68073a65433a51083a4e433a37883a34c33a24483a21833a13c73a0f4339ff0739f8c339e10839de4339b14a39acc3398b893986c33970c9396b833956c93950433925493920c339098a39044338e78c00000038cc8938c70338a6c938a1433888ca38860338554b384d033827c9382503380ec838098337f34837ed0337c38a37bb83378bca378903377588376e4337498a37448337188b3711c336e80936e54336c5c836bd83369f47369c8336854a000000366149365a833644c736420336218a361bc335f08b35edc335d40b00000035b80935b54335a048359d833582c7358003356149355d033537c9353303352087351b4334f4cb34ee0334bdca34b983349a09349743348148347c43346787346183344308343e833424073421433403c934010333db4b33d6c333ba0b33b4c333a008339d433385c93380c3336ac93365033349ca334543332f4a332c8333128a330b0332ed0a32e84332d68832d1c332bf8800000032af0832a9c332884c328243326f09326a8332508b324dc3322f0b322c43321249320e0331f44b31efc331dc8931d9c331c68900000031b78700000031a44800000031928700000031784a317203315c083157833145c8000000312f88312ac33104cb00000030e14930dd4330c64730c0c330a308309ec3306b8c306503303f88303b4330138a300f032ff1892fecc32fd1882fcec32fa18b2f9b832f84872f7c832f5e482f5b832f3d4d2f37432f118a2f0d032edfca2edd032ecac72ec2c32e8a0c2e84c32e638a2e5c432e47472e3f432e078b2dff432dd5092dd2432da88e2da0832d790a2d71032d3c0b2d38032d13892d0f032ce08b2cdb432cb3c92caf032c96492c93832c85852c82c32c67092c64432c3b8a2c38c32c144c2c0e032be50b2bde032bcac92bc8032bb3090000002b908a2b8a032b68882b65c32b4a482b47832b2d4a2b2a832b11882b0ac32ae5882ae0c32ab60c0000002a90ca2a8e032a67892a60432a374a2a32832a1a882a17c329f58929f10329ddc829db0329c94829c2c329878c297f83295a0a295743293d09293a4329188a2913c328f38828eb0328d24828cf8328c04728bd8328a408289f432887ca288203286748286483284f48284c83283908283643282288281d4328018927f8c327d4ca27d20327bd4827b6c327790c277643276288275fc3273b8a2738c3271c072717432702c527000326f24726ed4326dd0726da4326c78826c30326a98a26a5432694c8269003268247267d4326674a2664832656c726540326450726424326148d260fc325ff8725fcc325e70925e44325c90b25c643259ecb259c03256b4b2568832554082551432535492530c3251dc8251b0324f28c24ed8324d64824d1c324a70d24a443248d47248a else 0x527983526a875266435248885242c352140c520e0351f14951ea8351bdca51b78351890a518443515e0b000000513d4a5139435123c7511e0351050751024350d88b50d48350af09000000508f0850894350668950608350310a502ac350010a4ffc834fe1084fdc834fc10c4fb8434fa10a4f9e434f83484f7d834f61890000004f37cc4f33034efd0d4ef9034ed8c84ed2034eb2484eacc34e87094e84434e550c4e4f434e2a8c0000004dfa8b4df5834dd64b4dd0434da1cd4d9d834d6e4b4d68034d46494d40434d2ac84d24434cf80b4cf2034cd6c94cd0c34cb98a4cb6c34c98894c92034c604b4c5b834c3c084c35034c198c4c14c34bf90b4bf2c34bddc70000004bca884bc7c34baa894ba4c34b8d084b88034b5b4a4b56434b2cca4b28434b0bc84b07434aee484aea034ad4084acc034aa78a4aa2434a684c4a65834a394b4a33c34a18894a15c349f0ca49eb0349d40a49cdc349b10949abc3497a8b497603495cc84957c34941ca493cc349250700000049068800000048d70b00000048b9c848b7034895ca48918348748700000048518b484d03483dc748394348004e47fbc347cc0c47c7c347a30b00000047760c4771c347440b473fc3472ac74725c34701c946fd0346cfcb46cb4346a70b46a44346844a467e43465e09465903463fca463d03462807000000461088460bc345f10945ee4345d50a45d08345a84b45a3c3459b85459703457dca457b0345538a454d834543854540c34534450000004507cb45050344e84c00000044cf0944c88344b8c544b203448f88448cc3446f88446a43444e4944498344134d44108343ee0b43e9c343d94843d2c343ae0943a983438a89438643436b8743658343478b43424343160a43134342d20e42cf4342bd0742b783429c4b4297834285084282434270c8426e03425c0800000042404a423983420a8a42064341ea4741e78341bd0a41b643419acc419503417f09417a8341558e414f4341148c00000040fb8a00000040eb4740e6c340d14740ce8340b2c940ad834091c8408cc3406dc9406903404949404683402a0a4027434010c7400c433feeca3fe6c33fc3093fbec33fa6c83fa2033f77cc3f6fc33f4d483f4a833f324a3f2f833f198a3f15433f03c73eff433eeac93ee6033ed3073ece433ebb093eb8433e9f8b3e9a033e81093e7d033e54cb3e4e833e37073e31433e130d3e0d433df8083df3833dde493dd9033dc4c90000003daa0a3da7433d860a3d81033d558e3d50033d26c93d22433d024d3cfc433ce7c90000003cca8a3cc5033cb4c73cb2033c7b4c3c78833c5e083c59833c3fcb3c3b433c1f0b3c19c33bff4a3bfac33be4ca3bde033bc80a0000003bacca0000003b97c93b95033b80083b78c33b45cb0000003b1e0a3b1a433b02873afc833ae9053ae1033a)) else (if i < 4 then 0xc3691c0c0000006906c800000068e78a00000068d1c800000068bc4800000068834c00000068658900000068380b000000681dca000000680d4800000067ec4c00000067db8767d48367c30767bc83679688678e83676f490000006754c9674dc3671ecc00000066f14c00000066e10766dc4366c04800000066ad87000000668c4b66844366668800000066448b663fc366254a000000660c0a00000065f00a00000065cd0b65ca4365a54a659c83656f4a656b83654d48000000652b4b652343650ac900000064e90b00000064caca64c6436493cb648f0364568d6453c3642bcc64268364094800000063f0c863eac363af4c63ac8363894c638683636e08636943633d4b63388363260863214363084900000062f34862f08362d18a62cb0362a10a629a43626d8b626903623b4b62388362180a6215436204c862000361cbcb61c90361b94761b68361a60861a1036187c7618503616c090000006157886154c36147076144436131c8612f03610ccc6104c360e8c860e48360c8c860c1c360a5c8609f0360750a606d436053c7604ec3603b8860364360274760248360064b0000005fea4a5fe3c35fc7c75fc2835fa3ca5f9f035f810a5f7c435f628a5f5fc35f4c885f48035f294a5f24035f0b485f04035ec4ce5ebec35eac885ea6435e93095e90435e7ec75e79435e4f8a5e4b435e37455e34835e0e0d5e0b435de58b5de0835dc6c75dc1435d9a495d95c35d74895d70435d330e5d30435d17890000005cf68c0000005cdbc90000005cc6080000005c9b0a0000005c74ca5c70435c5fc80000005c4d485c47035c2b4a5c26835c0f080000005bf8095bf3435bd84a5bd3835bbe095bbb435ba08a5b9ac35b77c95b73035b4a0a5b44c35b35c75b33035b19495b16835ae9cc5ae4c35aca4b5ac5035aaaca5aa5835a89cb0000005a78085a73435a56c85a54035a42485a3d435a27485a20035a11875a0cc359ee4a59eb8359bc0c59b94359a388599e435977ca5971c3593c4b593683591c0759164358e60b58de4358b58958af03587e4a587b8358640a58614358494a584483583048582bc3580ace58050357e3cd57e10357c98a00000057b24a57af83579309578e83577b49577343576088575bc357394c5734835714cc57100356f9c956f70356e10a56dc8356c68a00000056b60856af4356838a567cc3565d485658c3563a09563743560fc900000055fe0855f94355d80a55d38355bac700000055a10b559e435584885581c355620b555f4355338b5530c355150b55124354fe8754fbc354d88b00000054b10954ae43547dcc5478435449ca544703542c0a000000540c4954070353df8a53dcc353aecc53ac03538c895389c3537008536d4353454f53428353044e52ff8352df4852d88352c48852be4352a64752a103528249 else (if i < 5 then 0x8fc97e8b437e74087e71437e54c97e52037e3ec97e3c037e2b887e25c37e13480000007dfb480000007ddc0a7dd7037db7887db4c37d9ec97d99837d7b0a0000007d59ca7d51c37d104f7d0c437cfbc87cf9037cc74c0000007cacc87ca8037c8b087c85837c5c8a7c57437c3cc77c34c37c0bc97c09037bf7487bf4837bd34c7bd0837bbd497bb9437ba4c90000007b8a0a0000007b6a8a0000007b56880000007b46870000007b2a890000007b15880000007b07c77b05037ae50b0000007ac14c7abd437aa9487aa6837a98c77a96037a61d07a5c437a220c0000007a118800000079fa8879f54379e30800000079c9ca79c203797dce797903795e0a7958437937c87930c3791409790e8378f08878ec4378d28a78cb8378b3c978adc3788dcc0000007873ca786d43784dca784903783389000000781c0878194378068878004377efc877eb4377ca4e77c58377a40d779f03778b880000007778497772037750c8774e03773e07773b437720ca771c43770ac87705c376ee0900000076cacd00000076b58876af83768d8a7687037667c87661437643c8763f43761b0900000075ffc800000075eb4800000075d34900000075b84b00000075a149759e837590c7758e03756a8a00000075484a754583752ec8752c037516887511c374f34900000074dd4800000074b80b74b3c3749a887496837484880000007471c77469c3744ac874480374128d740a8373e28c73da8373bb8800000073928d738d03736d08736703735288734e4373324a732f83731a4873140372f24972ebc372ca8972c283729c4a729503727b890000007260c9725b837246087241c372210a721bc371f2cb00000071d44871d00371ba4871b603719049718c437176c77171437152c8715003713049712d8370ef0d70e90370ce4870c98370a5c970a0c3706c4d706583703ec9703803703541702ec3702c017027037013c9700cc36ffa470000006fe3c96fe1036fc9886fc5036f9d8a6f97036f7dc70000006f64076f5d836f288c6f22036f07886f00036efd416ef6c36ed9476ed2c36ea10b6e9e436e754a6e6d836e42096e3d036e018c6df9836dd8c86dd6036db2086dad036d71cc6d6f036d59486d56836d41080000006d2d080000006d138a6d10c36cfc486cf7036ce3c96cdd036cbaca6cb6436c9e486c99436c72cd6c70036c4d4a6c48036c34880000006c20486c19836c05096c00836bebc90000006bd2890000006bb8c90000006ba4080000006b810a0000006b70880000006b51cb6b4c036b200a6b1a836b02890000006ae9080000006aca4b0000006ab24a6aaf836a90ca6a8e036a6f8b6a6ac36a52486a4d836a3b476a36836a27076a24436a088b6a034369eb4969e68369d08a69cac369a40d699fc369714b696c43695bc80000006946086941 else 0x896ec28966c38966c2896143896142895cc3895cc2895a03895a02895583000000895103895102894cc3000000894783894782894203000000893f43893f428939c38939c2893543893542892ec3892ec2892883892882892303892302891c83000000891643000000891383891382890c03890c028904838904828901c300000088fc4388fc4288f48388f48288ebc388ebc288e40388e40288df8388df8288d94300000088b44c0000008898c8000000888188887c0388630a000000883fcc883bc3881f0c881c43880e8700000087fe8700000087e0ca00000087c68987c1c387aec887a783878f4800000087774800000087500b874a83873147872c4387180987138386ff4986fc8386e94886e68386cfc886cb0386b58886aec386914a868e83866d8a000000864bca864643861b0b86184386094786068385f68785f3c385cd4b00000085bc0785b583859609000000858348000000856bca8569038547088542c3853248852d83851b8785174385004a84fc0384e50a00000084cec984cc0384af0a84aa43849947849503847e0a8479c384684884658384448e8441c384208d841dc383fc8d00000083d54c00000083c30800000083a0cb000000837e8a00000083620a835dc383400983390383078f83034382e08882dc0382c70882c2c382a60b82a343828d49828743827009826bc382414c823e83822d87822ac38218488215838207c78203c381ed4981ea8381c78b81c20381ad48000000819408000000817b49000000816549000000815388000000813a49000000811d4b00000080fd8c00000080de8a80da4380c00900000080a70980a1c3807d880000008062c900000080428b0000008020cc00000080018b7ffec37fde8c0000007fbe4b0000007fa4090000007f878a7f84c37f6b0b0000007f54080000007f2d0c0000007f070b7f04437ef1097eecc37ed8497ed4437ebb4a7eb6c37e)))
def rankPayload11 (i : Nat) : Nat := (if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then 0xc99da98ec90ab0e138c20a08ab6392f76caafb83b153c4796680e39f249e191375ca82aabd1904ca084c46fe570ecdc76244934993e980dd81541cf924f5ea1d3648418749c4cb1b593c951fb062a14094397c869da23cb03045433e983c2a2470c8cbae04b039830b0a2ead886d1955f70b0654353df58c282f21b2afd045d7535327e75f0fdd82228e5b283448a2ceb9285d87193f3a511782def74a65e0564cc9c0ebf76d4d73b142d70c7d99d920e0bad921b213e2338a16f3370fcd07274c5af4a49e8427c41656ca4c3a62be6a2acb3c69c9d77f328e35fe672bdc0ba33fd9a171f1a11bce77ff78c4532ed80df5d602589d20365b1ea4fddffde36520989f5d603a83c0a42907a9fa2910a167c3cf9ed0375e918da41ec67f17c4a2477e049f030c49e061982cb3fd076057cc678943da253ec236925818ed8d051f7cf68cdf5191f244b648815f673fe4fb35f1e0f884cedf4dfdce0bc8fe062fb5d09247cdfdcfa257cc0ec18c5f6a4e0cfb5931f0ab6f91f93e6e7f07dfc1038ef2c121620de21750dfcac3b4c02fb0702f9b9fc527287c9420afb390bc9f66bd12e44fab98240f9d23169f994f188b4be995d6eb3a05e142bec2217d74a633a1a68b279f4c0eeb560df4cad90996524f907692fc5a6b032e2655533f4bf03cd0a476cd7119f31d93d67693223cb1c964758bed49ca1f7c805f54590c2d6477c8e268ad3b2230adb4ccafbe47e4f999a0703efacec50a67f2b0ec13c1f2995682a1ac5f6b0d708f2cf10da3f218249291d9cb2e940bbd0b262c4e1b4673dd81065ce918b3f698fa6521e4bb26453f61b24392a981784ca65886c1bb02a81882cfa9ed012fb809cc76e2179bec2357dd81540c8cf98429730cc528cf918405f66bd385fae7b1b2e467cc2fa4be979b6c127fa9e26531df406391bf21c9201290e327d14a64a1bb14f07de21057d06f963431c47c2adbf96076802fb64c519ec95f699963650615f4a033ef20ecba14f07d3d408604a43be4ea19a18fc9f41be5864fa290884fe653c65f69c0823e7ce4e91750de1fb01b27711f6ab305f5f7f724c7d7d93f189de987646f4592a2219cc70714208b9b728d6e60be931993a864455e6483d4aa12e1f0044b8b3040c7061653c65f6b3044c3650a9961123c667e0c1873cf8d17650b07c8af9e12ae5930fc2915c42658cbe84ef389590f921f744b9b6f21e6750eb1489b8ee89716c3b482c3b147de6246c30450b54455cb197dada3f1abed4fde91b1337936a60bf128b99662e6f37db1fbddb7f617f3206fc6b07706b80f482840db089750cf8e03051620deca2d9b018e6495e4d860bf20cfe6fbf94db13398e263d0c1842c65f6a4ede170ec51f7e28bf1e4fe132da2202db620fddb7052f87cc929144c90398b1f836863fa4662c781e6246cc5f707655c1f02 else 0x605040bf04c2094b2476395ad8d59201a00075b543cf10bb749d70ae54ef08298530c9cf82be8904fca24301905f6c697e08160d5428c87361d18122344e062275d4ecc0831b49a7cc15788030a067c09162bd96583552240f6063d4ef066c1a0fd4aca6c51d128fc20798d30aab5238c9f0d4ccc0cdcaf050be60f76cd4a625e6d656bac833f02e19810301b8ea73fcb2f0123427255ac994951f0881f0494fc8c831d62b8d5873c485143503ed7b7e7ed918b6445143191486248b3819fe921f3c60294ca3fda73550f73fc90f60e7c9e20e8fd5e85040cb7b7aca95e2349d358eafd23e6425143213ff23b9ee7390d9c24f642501f8e950b58e54a0e44325b9d89090869eb04fb473c7091dce75ba1feb39b2c969062824a187091cd90cb12954dc6acf58b2924f23951c496536b743fd6723e536592d20e09f45263317d0d2b4e168d5074fd11812e4cb6934a693c4693f35bb7f9e695a36397da4ec3a7e8b2228a191cb0e6d2659ac5a4d29a4f11adfd99d3693a0ee2791dcfdbfcf1b233ee2192d94285b8d5873d13fda77d5ea52e4251437c1317d444c5a494fc652e54abeca941d909450dcf454ba6109153df06f8cbe317d46990e14f29913173bd24a887cb1f8e7490c3a2ce44f25941ff91d9c24f4f51a1450da2a0ef153dc749bf3a20ba63c4ef0fe083c4174cdf6684d67224d43084c39ed2a172254c70e2561fc90bbf92035b27b8e164a029d521d297912a838287142e10b49bea49bf3ade5b8942fc81e07d44c03d674af92513279281ed9db243f5fed535afd312b574db63019585363ad27bd3281d03e0347288bbe70d873ac30ef0355f8b9241822ef9c361fe7cca0c0d30e070cb9afc91150ee18ee090f84097fb1e315c4b2b5f812468d76e0f33396f0488624091b41fc0774fe3660ff44ca49d490cf055c4b221306cec6590f1090f84863c4097fb121f30062c791300a031cd9843233e0583de650b4678c51578843fb1e318d80e349ed86c091b077a6d0219b3a461d1c760d74a3f0467c0b06701b4cb2e48831e121643dcc1310c54f984a160837c45735817425594ce8152d21f6808fbb03021b47e1b850dac107848590f54581c46cd010b1ed1d0761423e8853c5d877ee181fdc740bfcb590449a8beab653c89e4817e12af2ee1252bf457ed7a516ad0217df37ea889e49b182fc17d420fdc46a81a54b65d2a16934b49287ba1f8108e130a30af910396fc2c0ef6d9693a86d2a17bfd92c26448a5857f2548f794821f709d90c2e94b46d1e082861c741fb9d66c58504abaf9959fe1ae69f2763c036850838c6aa0a075ba25ff208c3617085876c1d0ecd1edcc3788749d630194d19a0a0627f0e3e02c0ef3cde8a4636114e01240e9e7f41d62d399a43ac8fa0d16998c3697c12954dec18762a7908f23679665045d76485) else (if i < 3 then 0x39a38e9c60559b462d36882ca61dab4897a133cf951a0854c8f794170cf68c3ae4092e067de760bf4166bee8adce873692e8d58c434878b298023fcfa3de772264a989ed507417f33e23551c228e38bf4b3e4a6782aa341088d23dc237c23101386d024710ab0723188f7299e8fb8c1cc05273c2361334aa9c298c68d477f32a42fd4c187640a5f30dfdac2b900d1b141862d31e8dda48aa76f846dc123b42b442b8941820c47b9960319989c37f32b69da311ee51d67e4b109852df53061320d3c96237c234e83c6c8c2c6718d7055a98494621b0638a9edc8a7b94f7368d971a5533f243bbd58c5931cbc7b32258ffcc33f254f708c1900b188df08c27e4b5cf302a819f0d37514c7a0e630cbb462c71b3e7b3204fc95e1cda38970d31e8da769d155483b2952a60dde474e83ce9638570985060834c7a2701e30a5f31d785af699e8d34b46a3b3a0f388f71bfb5884c29616a6581f7220985060834c7a0d3c969d298ccc4e1a9be11a2af356fc23537c234d0f28d5c702d2b990d9f7582c6d15cf6d3b46fa98d0134634aa07cc8233c236bba70f28c941820daee8efb38c6d28bbb65134496d77c84c29690ace597946ae34cf46b9d77475483b2827ff31d1231b09ce14c6c0b4d77ff31af7af09f0d17f240978bf9807dc8cec1974b1c2b749e73a791daef5cf448c638ab8c8c48db3c234c24a357120b4ed013469c810dff31810c1a09e159d298ccafbb65613e42614b764c822f0e0fb5b732db1e6bd07dc813f254df08d343ca34552f0e1a70a63290764097dc34f25b7511c4b8604bee4d0a091532b5fcc32bda365c70b4e0d0e3b69da7561e4f1cc61b941560c702ced013467b72372b9e9a146bb9a146e086353dcd761a1c72907654bb726851ddb2b5c9c4b86c0996e091ccae976e6442bed77342816a63ba24634e03ce385a71c6c1bac4cb03ee432b6ffea78b4386683be11b072b19bffa9e9d398cd04fe718e1cc31a1fc8f3434e50bc343f91f4073a5594f455db860c08da35a5a32359ce75d379da3fd4f6c418668270921671c2355350c867cc6c39ceae3ae718e1341261b1b3c2318870d6968c820b4ef34b46b42b91810c1b2cf08c909de17e62b8fcfc823042f3047b93a0f39d3c8e237e4368ff53c5cda334138487fc838730cd04fe71b2cf08ca17808da37c7875c8cb7c23375f53c73053dcdd45b4e31bd9d9701d18bf0eb4fc5e2fe56f0ee31657a0be812404833d9aa26d6981b14eb6c11ebe1759382556ae785075531b28e36229df27bd329f67115116b03b06d285bca637d21ed13ddb2a61d2b4e168d5074fd11814d065b49a1337f11a4fcd6edff8d2b46c70fb49d874fd1644514323861cda0cb0ec5a4d099bf88d6fecce9b49d07713c0ee7edff86c8cfb8bc994285b8d5873d13fda37f5e920e0031d70ca124a1c12f else 0xcbda0eb88bbd1f5faf3d2719d13eefee2486a6b9c97cb3a2bbb1c220e3886a83a5cf4b8e129cdc310d15f725f2c11aa34eaf123b68b7b14c3bfd1c371a71f46692c7e7bceb0970d5fe71da717691dfb3d53dfa34e6e19c7e98d632a338e136215f725f2c7c2a7b5fb93a0e71f606e1b641740d5c8e7be6c179539facef9ae3ea5386d87a0c69e871f9ef58e32f28c091871c71243a87a0e190c684ee798863457ba3dfda76b93ce94763d43d1c2f49a97da762830c5b681368df4651e8f6a83be11418ca8e0bbda2beaf3aff63a993ea0846eed214ec59e7399e7d9f57cda49f72cd8bc9a889f3f3fd4f38fa7370d8b3ea36800c7145384e88628f54a80df351f7536eac3a2cd7fc4323e22ea28eda054b04729d65a6760d4c61e7191aa98f675907c008a580cfd991c20bb17602d245d2c247109c33bf3f3e536dcc63613c967b5a9f7ae725ae13aefa659418ad0a64fdf94d62523a46b4f50b841d968318eabdad75efa46562519d2183c5115ff4552f61a476d3edf3ca4eb45c275dd5251b16f9c6d6873c7efca6917aef2595abc674860db0c601fa562d18b6f2bee2df38c5b4c0bbe2928cd7be9189b2a77d744ef41f5a20496017f42edb001e700618daef25abd68937e5300b4cc2efcb69811a677b3975d0ef82a547e811a7d4108ddda429d8b7ce7371cde71947db68816a4b1932e7cac7a07c4d090760a3033b6e633b2d0a73bdfe7009ebd8b1f89c4e51999fce354a80ca3df03969c3a8cf7854f7e8d797ce9f2328c5be228f81f138d1082fb3ed029d871979c6350e3ba21968db4e3189347999fce3796801e4f70dc68fcf79d38751b197dab71ed539406e50618b78364fc7f28d380b38dc1e7485419915cb278869e8e3da5dc886657ae3459b5496e3da8ae0be8b8749b5a9e356cf48d8dbd9b60f5b6ffaaa70197dfa3d437dac6657c82fb3eca768c497cb3efaa088c20efbb9181187531879c6d07732384e8450632e1fd231453f62885d0f53a40647de75d1792e96188546374395564c0114b36b2df13e7e35a8c02468d5dd46dd480d47d979ba331b1cf938cbd9fce0ceedff45d1e3611f8843555da59385723581d53cbea7a0dc1b168cb87bbdae8bf4b017d126fd2637ea044f5817d1447fb362f65d93a069120188a23083b21a5282e1a9d203608e4ea90e9aa1067596a8df3b404374e037d1bce71b2ce0ac1b9c521d94eb19a23083a0dfc8d636a22b171c23904863640cb2a15f17e9601102326fd2694e091ab7f7e8f70df694d8833d8c9df627cd90f05dc220e3b4c6b19ed15f741aeb5165affe9c68aa45e63e59d333608720e4b419c8192c2342b99b5f78d8797061b54f769762b58bf4b0d026e3a43f9de878f67597e9deb9d16adce876c1fe7d1ed63e1f9f499b4ca7d7fb7863db408a0690f05ded18754480d50dc371a2)) else (if i < 6 then (if i < 5 then 0xf247d274e21ced73d79e93ac480b50e81a541876e5d1772ef2e190ab780da011233cd6af12926283572d1ee4abe29718c6690c0869c15adf408b46b8c31aab3e87205c82ef2d5c229985cdb9c550747bf77aab026add3541c381a61d1647ba3d89b17f3931b2ee3f231ffa9edcc758c2fb56c7f9156beb1b8ff53d1053ce30190321546089502ef7b88bd562bdb101aba74003fc6c3b955649fde4064e2d03b3903a5e66d425f568496e0b7e3203a4498d107231c34bb5e8202bc42a8c702be860067c0a8a102e75c2484510a43de2d85e1a06c87d8305b4f5c9ede17ef037fb65150317d9c632db3760f5755eb70d7ba71c2df82d326a041bda0ef432a1747dc089bda7eb022e454cf9ba38d78223577f9b0011b9ba7867dcb397f783c90c0ce39a8069c105ab8e176bbc161bbfce046a8f2c0d30e53620dfb672d920445f10c82e6386134c1be7e83b802c46fd3aa8eb805eb2553b11bfa54238e166a1d077dc5035412cf350a1ba32a0f9ffe719a4b3e67fe7002ff01651dfa7ee281beea570e03581cca59ef3cb2bbf979e5921d4c5437cd6d689d47d5c59e73a59a8dd7e048a99f011e30ab9f3c28c0cef3be65224be58a62a187bf33b9f9ce6a0dd52c3b291a69dc1dc365f6ad3057e8753bb89b60798fc62cc0880bd7202ea0a8471ca945589f1df236adc6247d5635e60e3b5ccb50222ce46965a046e09b2aee47d4469a476c90c058ef2ee236e3a4616690cd4216e204a9f9cd5f95f0d36b6f0c9a74795ca919b5aa452db7d516f89d166cd402202f25e473d0d0e87baa621efe6d254a8791aa9e69489d46090232cc10c5b62e2369dfd34d7e7ebbdc380df7ff9c32d017e9c6055f9da0ef04305513a80dea533e6152cc05e8483be8c676cb21554082cef7b48273f669847cc71ed4b8ca33155aa0c31640b91847cc177ccaabd5f77f18b3af5a046c0fa04680bafa3bcfa81122fe6e86ce7d811533ff31e784ed723fe63aad30f6b7a5a33bf51bf87efab169c6754d1905413ce8c06cc7f748d7259a6904f8fa511cb96db728d5d71ea92812faa8aa6488c20ecbef8a94228e3b64e93bce3641f2eca4dc6d18e065d742478a591f104954b27c97741d7057b31679ced8fd17278c6744094e967ef7eeac382234cb9b9dc2df13e7fdbf7af67a9e61b167bcc8a7b44355318cb10cd875e1cfe53302eba929b335fa4c497cc5217d8a78954eb2613267808396c1913e21067c621743d43f66c933624c1d936c95374e83fb672d30367dbced1b212b6dca341b8365057d9f019fb2bafd9af271c23487f4e3ea2c3b1c82251b1ea88f14aa23083a44f5b4bae85d9740631892a967614f48d226a29fb3e4831ae804bc52c38457dca0fe9ef31070a839f0a86f9aed67579e595d740631becd799135bc196c83e733b9275082eba1df5f72cda762df39c else 0xb990ef9f87a9c3db7141c98f6b60e1c959681a5e5b04f1b6a9bc10e9c128d6ef05c3ded64f74fb1cd54ea938ca6063b10b8a22b99190e2e527a9ea0d2f4a1ce7f45ab9d031df40c4f3ba2ef602fa0697a4bdc51e094379bd8c893cda83519b6f0d3845c29b4ce19d333593df5f95de20a9cddb33953cb254be87b1b1572a4c823b624be5194be859bf45b6a0876dd9eb42138b22a24a8f78bc964e39cfca329d10e4514794be2219df67c497ca33a321d4e4d394e5ab1bd6715346b86be0f507916807a3ce4f4391798e960ea8bcf0c6f7acb24e2c9825796d3133f08e546f5ade3174d68b0c26993686527ae5f59ce457d6b4a15f6ac381a62cb87522cfbfa2c8457dab37bf45892f9469565ade430ea32d46b18d8037bbf88b598ef20bee2d1b6684b4df70c871b9036b1e348def5a9fd87049ae4939e11db10267d7ce76095e597888d237b56f3943d70e4b5cbe73b43249de72a7b62165add67bb265d860d2cec3d4c3d4f34af3a12a452cb077ca77359d686a93b4788ea938db89a70b648dcd54f3a14e2946f36968f100fbeb1b10fd18d2438bb51e9526ac34be539e5f91dc5473a9ea70f12b84eb950d38525fcc46cb591ea3e08a4f14789af4846b3c176bb63b42378524a412a543451e8f627c8d5f5a3b5f80ab0efc0450b7c891b596810bb81138919e08fabc0754a65f41a66806df85245b8884f33e298a9eb0210c8d54de057cee81d0ae9a0f8f7099233c78f50d4691948a235b681178f54ad28d2329154cb6d090cc0e562d19c8ba391d514cd8b396ce5e9ad5e2e8810d0357c631c345af17c5ed451b8f6947e3f10e492db28f92453e5345b51ef069d1872ef48b9ae2d81111aa768a3d503965374774051e8f6216811f3bc6b556f8d6fa045ab20d30d94c71a0694771fea78d9d46e328d2832d0515c493cf8ed3c32ffb9755b3e530b3b17fdf38de61586b4109c31090b994696c1e328f95694ca924b627c4d60618f57a4f147e6832d1abda4679e2558d19729ab1e7caa74cda757a4f154a1eb6f11c0c4b4144a114cc35a247be83585fcef9ddbc31e95362d5c47191aa99095aa0fe913a8d0516b2554311b2cc5980bfa72cc37a94c80bfbb4d6af140d5f18cbb931cf0146ad5c347af7716a830c5a04a794697349e40b91d1e1ab48cf3a68d3947f89563465ca6ac7b62aa943d5e93c2efb80a37f3668185fb5ff3ce308dd8b4ed4191d3a6d5e63f9b1749d0b5f67ca3f1fe420aaa23e62c6e2780a356aadf1ad8ff22c648fa4e02270e8194228ed8f060b3c2e5de5a80b91a6ddf2343dc7bda468d0332941e459e9920ee332523552e631df07481f82cc80a3ef3a6d7283cda2681997e02285ad23404459811ea476d558d1191565dd21f523b60163bd4c9f52ee9b5c229985cdb9c545dd98dd92a0c3859eb9d9ea1d037dd4942c9e) else (if i < 7 then 0x67a10348b2075555c04b8d4180049677265de97de723a92df5f69dfdd50eb548ded5ae5f59db20d32e95569c2a68b55daa775afb5666a15913e470d77185db6fb9f0d03796fa2f20e071ce771972464a23a9d976e071dd16184cbc9e71cb251066fbce3a6557791c4269ca875b8942d32f22df12caf79d6e465df7562cb077a5655674cf7da76864939d12cee92813560ca445f128bd9e6672d6057e8b7c5f7f238862b381bfd4f09f96745df91c4531cbdd0d83b5e20c41ce090f266f125bb2e157aa6a20ff25d0ca98932069d075c61df459c8a85d609510697dc1db03c166e713a6389c34bfeacf90d234c25123d1f79d74377450cdaddd5037e02483b47b88d22571356b47699bbcd66edb46f97fafaa30877febce74d44105e997934a0e2064955c1ef877dfca8b86d1ee51b1eff9cdc56b747dd0698717e58633dab3c130941a1d1bea9422bac3530045e0368fb1c188ca0ed0350e175239f2b90de631f88780b0437980227af50de60b3932e91d388a115f6dd5875a3b516742b98747ba348861d871877b56288a32e2fcb31ffa9eb4e9932ee4c74a2c9e319ed58dc56b68f7347b8e6fa6a83b6eac3bcee50a069d48016f2e5c320166c7a08cbe834fa9b4a1187631da8b3b1710f11f0d3694220e39765568ed18761d0e789a15ce3f23b6fb56cd069876e63add1f8fc86eaad5932edd138dc13a976df3598964c2156ac7bcb26e0a94728c65b59c5acc545e576a1fcf91010c3a73375c870c9436cd630e1bbb3be6f316f38b79046ed63af304ed78495b506d7e64d48f40a0cfec2595dc3a9f4253d05abd538f0de9a9c632ce4a5b365eb3158ffb502136bf08d480bc9042c6c508690324fce483732065ca81869d3ddb24ffb0f089258f28a81a7c5043a2cd1a7b408615b085e0fd4659fb9f6806eb2c217807b6cffdaa04f22a1dcac9a11928cec98ad2f6f96b430e3f320589cef3202d91947ad8c27f8e7da9fd469b739024fc1686ba37ca11e11725284a12db98d50d72f40de5430e4dec4f58f406e7799b5f0cd91b06bcffaac1d5360f53e84d874373f6b0edbdbff884bb52215c43b9909adafc015042775b882f30a29f8684b03708d37e710e61ad0d42048358be76d0d405efef06ade848bfb84a17b3aa91772c4255817e2363f7af0a2d94e92666ea79121a6cc77904e85096f312c79d7e3b698f0721e760290d8376ce66a9a90842666663db7144b995175d63772b1442d401d80b238c77aa9ea565a251f44b3ca319054802600f8d8d8278d87a82c8e358dcb821d87a94f5b0f15043c5d10c87e229fd3add2699a06c3d4adf43d8d8db93ce259e51b1948755ca53719d2391c733321d2e4e090967946f218709462472115f69d46698dc52d1994eb62b7d0f6b62ae5298e476d636b7d0b37a597043b6ecf3ab7c4184d31eb1b5be23 else (if i < 8 then 0x1d2bcc2b56a8bc89fd69cfe8740f89fd2d58da93ae98733d1043269d827dac3f973543c62c3f9331e9ff269420d41453a82c6ef45a70d8b20425ebd5083aa395ab48b563c691bdab0b462de6d49a75e968f1134bed5b0c1a69cb5c39ad76768dc8ca3a0286bc23ddca98790062148d8171d21569fb576a19ecb256fd51538a834cd40cff797f112ee5464ee6c4677bf5427fb9b13cd8cc1d502a44381931e05c8eb6f43a2146691b7ee05c569d7126066b0f840d634cdaefd509fbdd92b0f849f143108ebc672c1acdae81c5845482ca9ba8ec4a1f9369f66186fa86ed3f6aa07d6994e98c72ba86fd4de755aa0642bbcbffecd660b7793a1d5f5c042ba6203fd40438979d7e0c2857fe38ddcc300d1c47eef1867ae743295937a2df6cdcbde4dbe5ea00d73c827da7142f59264ac9b23df29fee148daa960ca1b109452b21a6e68b598c1e1aacee719d76772fa1afaa1c72712b569aa1d2bf320601f017d9e759889a86eecd836643d83950f3cbd06fd4de755aa0642bbcbf5a019acc16ef5a5e30f1c46bcdfd7825b6bdb42c0943c763e5bb608ba814a2ff82e392ff26d22f4337b406d50b756d5259dc69b204d39b4d16bdc6575db7c6328ed6196b530e2b5f91d60ee1bd6b2aa74e5aa0fb40b59e846d7a0ac97a23ba0558cad304e407fd9cb219c4259da837574e84df6188358d5dfec2073d67142d21face9847e4ca677fcf919f02a2840b9d709211442bde50922a61e40a88523605c7485584768e4a9cad1e967c4d924e67d6e0f5ff475835cba56dc9f0d85737b41bce0646f5dac4475fde73bab966d123803ace9352c433bf05a748e34a8bae333de718464a2cb48ee49f964a1556dd6760174ba2a6064152a7b5b7cc23dad0a90cefc163877304fa2b04fa2a20ef4908aface8739fd166d5238c1d0e0d265973dafacf0697a54f6beb3c981886317de71c4b9edcfabdce5353da67002853dd5bd9fd01e667182675a2c54ea09addd0d8213378037b9b136e81b4dfb21d6d76ebb8f4bccdab3384b64514dd01cb7b0f366407839ff6006cc801202de7fdff3e4347602850a1b9f68ea3ee2751d889c40d9b1d4b98cb70de93b40d396adb12e13264319d50d5b78da319bef5b8cfa2c77f67e11db7ec50b763d1fb5d30df110754ed1daf400f6ee19a07101ff262567a3b6030f9a341a19e1399f3f4012cf82d5cd419c82143ab828b0ba61dba0d316e8bbed5806b45bd81e179f9c7829fb5a198c765cac030ce4ef84d0726257c999c3194360c4bc70c5502283b10ae78bde4192302fd2e0ea4abd2e174a5ba216ada74812dc12165dd5c6a80ed788312038243c99bc749337deb18464a91c624bf05b715520a033dd38e388e2cdfa2cf17dfd162cce5876f25b207936fb3ee35a1dcb1652f456d3fcad4b12e0c14da7e1b210dc35f28bc8daaf3 else 0x6c8e7617c8c20396c44618f7f2a944cf4731885279089f8edbd27c8e54290dd84f612253150dd774fedbd277ed31787f115c0e78fabb56ad386891db2e674226cf9fcdcec077ed776aab4309a6e140d3ee1fc42145e1b3ed721d54aba43e77ed6cb994061b7e0b2df77ed764e9317a23bf05aae90f9242f039179877ed175d52eda87551dab5dd8a167dae55d21f1909a10398eb8905b7295b238141874c4c70dadb5c9ffa3a06acb486d2b158627b0aae50f96fbed70fada37b730dc2a95c73716dae1909a7e348a6c124d22308391798ec9d29e7406d2cffef748649ec861b431b46ed5af97d20f3298c387d8e3bf69fcbba98b43ddaaae7603f9e9eed5ab02fb1cfc059475a7f473ce80da59ffdee90c93d90c36b93034740d2456ff76285942290dae4c093855a18751172605a1c0748ed91c9e7406d2cffef748649ec861b431a23bf05a8450f98bf48230da48cb9c435c981056b8e6e291da38755290e0359ea1313f04c70d9243fa3ea921781d300af8aa5a184d1dfb48bcc2194e6da44f9b30ae99ee6e877add11a83ed62d19d1c8e737b0db68cfec9f45a089f89524457e0b7e1cd344079a6d025438138a46a0b76dfa2dfd485ad0dc93c4b438255a2627e365c1dc08c97bb08bc023a07495c4cf94480da4b26b88bcb1243fa028bc2e9d170c8bcb3e709b00af95312a3050c38ec4a4380d68712a33c421c0604348d73843f1c7ce997b2ec94317432794fb9071bbd93e8b6c83cc535a1c9816676dfa2c5412a54bae02747c70a42817e264cfb188f8e5a10436a4f11bfb578bf41b02fb9d20950e6fed30ab54d0233fe73b810996ea693ee7138667fd3758e39d746598d2bf132654a759f632d49e22c4519743ffa9e9f357287ccce63a720cb4f97c8c01085862350dac1217392d362b5118b3e0b641b16a43b8fa41186d4856f98d81ae6b7096765e45d6e8112060f374b3efa85121bc33b80cd903e15483274dc8a8c2a86c5ccd9118c6b773e9ba30b3d43ce6f1e5ab9f04aa63ccca0a165b70ffea78e46333fc16c8189c0a1873db2732d5c70d8c67b4e2a27e17f25e60b3812f17f255857e4337ff53d0c5c22b4d88b49bfa90b542a5c2b5ac7e23aed0c6fd16bbc07c46cc8bcb573f52732cfd1deb64fad35a9c4865fee1ca63375f477bcd9a852cfa990ae71386d6fd26d97f675e1b9f3ee5ff0ff53d87fa9e0cd2c23a4b493adf2a70ca41539cf650bb429857de60b5bf9ef588f905fec5309281b9a151663ffb84656662a542f1ce087024dbd930fe5cd50eb509c3740c52a8e7b77f36810ce1acc563b0df52ea3ae61bea3dab9e45ea3bfb29de8fbe59554347df2c2ef1b1666aa6e6295c62278444f094fea9bb666aa00679dddcb96da6b25e990846fc9b7083a779964564f795938c947913c203d592897deb506e447460ac5ea84)))) else (if i < 13 then (if i < 11 then (if i < 10 then 0xbf72c2c8018ba11357df804cbf0ff3a5cf7146bd591a9b4f2b175f72fdb6b917bca1f94d18f34e81e9a66c6ff0aa3379f390c02190319dea081debdc2d7c5874068ff719918fe4563470fc2a3c445606edc084d59320634725baca4739b022b74164f33fe50c0535a1d606ebbcb8c46a1b4e70525fc340ec8081c87ef5065b089f83fdcc970367961fee22861c7643a869cc21f58dbbc020a2163ee2fe59dda90edb150d4361800df6055291c67b8a248724864831cd21a709a770bd2682001cb3bc206f9079907e1d674ee8a1b2ffc83c087cd038e81b534cdd4832618f14466991679f40e40cb663adb65c74f919e216813621721d9818ce618e234cba683d485d72e77890feec23752596e9a4a2c9a4facc311b8340b87eb9877ccf8a254c54f7c8d5f5c451db45b5d76e8de10360e727418729d106ae2a5d3eee15260168633e8b63f10e115a6ce546c01ee5a043f5c320b98ec6730df2357d52c90d7e0948d51d5f9679d0a549370184fa2c3bbd7442d0394822cfa488cf0a0b206c8f80b7f80a06953ddaa3787505c0a47f8581dc277815f5616ee4c35bb73749a5e388d48e485a0a33c43f5c7c4c1beddc451db451e4e8c27d16401cb203cd2c12176e140d616c31bf45be812a1d71f0152eb85fc11de10313061d35a3cd20fe3d9d39242e099233c51af5646a6d3cac5d7dcbf6da7dee4f10ddafb6a4bfe40c963eee7e5a99b72bf603970691f851ef9d1e49e23d519fdb28ccba5688650fa89723d3e7475278871f014aeb8a3f0e80d49c2947a1f54bae70d91c7c038cb8fb6f81cb5a21986db9a4b5c269cea4f13af3e2722782c8edb87eb972e03f9684bd0698033e46788e11672cfa983188506b82d410f8c428c6830c5af1f5f11c870ef8283e7eb86e54681c7167082b1a158d6ee0667e212ecbddcc83b57d0e91f3430340e2183438e39195c15600e5b8f691fd81a0892d31f0024255d12219f038ea7280cda68b640c567e3fc16bc5fa0c97c777ae885a07290459f49119e141640d91f016ff0140df636051bc3a82e0523fc2c0ee13bc0af9a0c1febd71a0a0901a48087c4a1871d875dd50353519c5184b6de3a99aee37d9796746ad9675eb8e490b812a0ee03b34b07be1dd638e6d42bedcb0397d2c0a09a86a7073d8ffd4f14260c3713a1f00e438340e38fd720fed3986f3670fc5e54e4bf2cf18f61d4315666c90d5f96633986a4659c220b8139843ed31abe340e3bd79621981b4e61be8127e241d5c0e78029324c031a581bd2844e1b70a30cfbe688389c17457cd21fd7d027cd9d5a49a08d951917eb9f40e9136c8f5ba713863820b60e7152eb9f40950e77ed18cfa2ca7441ba41e65b238a6c07d4d9fc5107b0a91bb569f39c51349406da17dae22f31b94bbdf77285abea145e1b1c52791798ae290d73b0298c38aba43eb4f else 0xd93bfb49287f6c60352592b40c7e8010032bfa08a1a6b198f68a78cd094752639da1925076be601251fd3d964064e9824b340cd02bff06c6e08095902abc6d791d3bbb25ef78c6c9153d3794c53e36b6c56d4e3196ce25f439e8796f51d4342358f4de4f571219e36b472b0efdebce5b97d72634cadce5846fe6e45ebdd927d087e437a392a61e40a83723605c748556c6e06881506e3a47c9010d225c4daa11aa2656686bb1bde75d84a286963df0690e2bee642190eb1ab3ac5b12b1cb39c3e4779cb8e3d7e4706479d5157b37286749c8ded123dfaa395d411bdaa22b7c7585b0e2106bb265de0c967b5a1caa7dac22bed38b034c3bfb8b909e0770962c9837c1d506ea0b4fb40177b274c73516b57fdaa18f81e60c59a0378881e630121b321070df8c7a16ce911d1747a5c8a2351e95ee6d03b29d1e761d885c81744685dcd323c55921a0253e4db8b3e8f2a9b43f40948e396435a7b0073ca113d25fca1815c52bb76c9e08ddafb6a4bfe40c963eee7d36b6d4be176e4c227702329e297c469c4986951928de3496cf7270a4f3a1442236531abefbcc0160b98ec8150df384f4a59731b8eb42bb960d5c4d3976e927b8a9e0b2f008941de0b071d3c51c2223bb88bb153dc28c2bef5e595dbae885c8e11485cbc022905cc700dc3adae0ff13e0219507567abf2c4079a76de96d02523ab6f05a79d0104261dd238a435d0c0f844d9f57039e0a0955a7f8874897c0680782ce47f01651ce41167c03402316e9f69d21308192f80d53371c4290cfa483567edbd24be71f012fa85d284520779da1f701a821345526dde1f9b07d3532b6f709f73ea45d39a6dae085cd0400396eec9075c154d217dc37540cd076b646f8283ff20a42ea8701b621581c8fa52b899f65ec9c22ce5aedc05d9306470897688f8936ff38fd3afc0b766d51cae781287dcfc046487d4d88323489217dcf33e43ace9f0a9eabf2cf34a9528a64f7943f298818370add3eecddf62854140ca18070e61a5c14f013d3ed51ede9a581524c1461a70a8f540a5c6ea0b75acd064e83d84ae354c6bf04340a30ff71a0cb7854d97ce1f8fb3d8734d18643ad4925aad7e471e2fca6c8f80d41c158039e7d8a595ab0325c098033e3fdc740b50eec279a7985031e069c753a406755b4f56b824b5c093cacaa55ff3e431c49b3dc9b543d5c37c15cc8cc78a1b952a3387e3228527b996e049ee16d691ea8bc022a9e9ac8750d57e5996e07442e493dca36e8ab1ea9a624084c18694283c2c1c72a393dc5ce124f7321d03384520721b805b5af907c958613431fc3d5cd029290455f43fcebadd4302552cd53d34e914343fcea4f728dfe02483ba2f442b03bb0a4d3cca5584f34460c3a6c8740c6cb3a5208abe428bc2eab52cb2a5e000452d90ea1942a0e160e3b2dc03659d00542c5b5a6) else (if i < 12 then 0x488a189bd86606b995ab7b8b3e8b79928ccfa4d897e8b64151e91bea4d1f684491a0b6de1122a457307dad9a0016c1f8024559ed170eb383f004682c8aeabda3de24347a82073a70cee8d4203c2df606d8f362281a0b57de55bee190c6483cb1f1b75a2d7aa2d9b1aea871c6d4729b54d73e527c65c3a96557fd90307b5694996a127cd4450181dfa3cf016539230e460c526408d70068d1450478297e47511b95bbdc828a80695560a5d630b4b5451b6f1a2e8dbe8672a2544dac49a035b8016847bc55a081c8288650eb190150d9177b11c0b38cc312f8ae870884fed58c0efd1e05f902555343ee8f53bc31684fea6a1bd75184df61ca0d0079ed1feae1983ed364844d0fb8de0b12210d036affb0b5e31a0c357af8998246a82b85a1835bc691ad0c7872230a1b25e02438a668b192be740bc25455c25c3cea59184c20154d57fd986bc90234521a65d4e6d5902347314aab26f904652ea2c5f90d21c56e731c83be0a6ca03b32c45e12c1f3dfbc437943e4b6ec4a4ee68021e85e20a76dc9470765545dc834c92bc8b876680d6755ed6588497c0de6892bc6c29dea068d8b3c5b10e18bd105cde322743d8d061818e845df221294e81d613230e54ba2046a03b461d8b3b850054c7aff1f2474079a174ad8daf090e50daebc05c15f6dcaa98529f1cebce3720a6a107e015a0e2246a195bc612c35f928ca46208a769c41d657fff0745f12154004d5273e385e4c24057992e8be17edb52fba15f4c41d1d4d54f5d8ad13b959d5a1262ee798ea9de296a6b257996586a9e6073c621c5145fec7e3811b7c436f8974deb683194ee6589a9cb49dd0f291c26a6c4e3f877d8a600eb692c154bd862d1ab6ece3a1e1b3d7496a8d1ec8be972dc2f23522d8191a568d2456f84b54932fa24b7a18016914e24cac987a2a02105b315a5e5f2b5a7fc43c1ed0fb7496a931f0cf51611bf9bd1d70ce74f90ae5bcfa1035b75db256c01c355522e6321f5fa5db4b419bff2ac72534a108ef1531eaed96cc5483770334371b01463fb6ce39969f6852b8e7305434aa1037d1a2706e6f954750c8b69bc807936288e489b1ac53e9e4bce2486667c3cb4f358a4152f4bef399b49ee8865c37a7a0af6c403621d0d48a75096c4e66057782a2ae0020831cc87b6af5800c7a8a055b224b1ef84eb1cefb99004605f08a406e90654f7dcd834fbed18e543d2c7be0e453b1e149b10a3b6723bd855e234928c13534c471ced5abb4d163c32d9422a47afd0e333b144242191798372282058094d9e190f0aa96c666302217e5348df103463c3167b5691bfea7a86af9469c268dd50a5bea8e3636e46ca8cb0063ade951bb7536b2df2074bd416fa51d7fb59db732fb3e283ecec21ae796483ad6137682d60721f03af0545038ce7bcaa8452425a42be2707704441a1909458632 else 0xf42f102d76e4a383b2aa5ace3b0b7f1772c42c17f4bbad495350b0fb905b5e79f2388c3505ba2e4d2bc5518c43485ae152624bf4599497f4bae8395a581c706847419e8f56fd1e73bb9aa2eda712dc0eb8dcaa79d4258a3ddb6e417afe443730ce81217c422e1b73eb58f53a7c7ed5042ee7d5cf047c7a215266195f9817764ce4ae5b9b8c3f7a909503c6e9c0d04ef3b360641164dcf507b41a0e60e3e04ca5279204a98543cf4ca3b8de0b1e3f073341d68f031ae07baab7698e73fa2ce4a426620cf77a653f100d30ba4c9a4ae63299d97931b28eb1ea812d2b50ff0e7eee0019dfd045dbb13a9dfbc34516f57a00a3a93126d0c9283b2f30c5731040e936ccfd9c40940d04ef95b99c5fb6cc4aa9886037b6317f70129c127ffc063bfbf8642c7980dc337398604081f03e28f943f218d3d0ee8845c329045534e25066072647c0f5f7acdce594f50e741da0e587238e972f67d0ec01a5d2573194cecbc98d94758f5409695a87f87b270a5d4f2d18b4f1eb691d6ab749f8d2fee28b96c207496551fcd0aff84af9f38b1c31692b4829f80975aa1ad133715bec113eceac1d8f3188c43d9f7442cb193030e5be11674c23481d8b20cc8f885d8729909dde177cac98ced24261937766441990eef62ea1a88b2a348838cfb145b49078ecbc53b67d145a65680793b980f80b9fe2226a1821342653e8adfe646053814826dbf887fc6124c98a29e1f89742364aab47ae1cc62d9f2f870c64b909953d2a9278f540e22535641a70d52fbfec330079377f168f79d14431ff9b1aa8e7c67d50c5be4e1b16387b7911bb385e008993686c36c41b4fe5e9e4b037b5bc862dbef3a7d8870bc03db6322a8872b493675fef93e29dc6e62842cd2847ee63e9b179690ea7d508efa55eab250985d51e8bc8e269c70fbc9a572c5adcab77cfc3b0ec68d39253ee56991cf431fd9f6d0368a57d0baaf6ac64787442ec3bf8c86e80dd029f48e21d6619fd9f2346b9e086292b034d8ff514cc605b4547a6cfa1cf80c77f18862a7087735521e035b1d1fb8910d9da785cf2c48434fc6d8dfa525af469ff3a52095069b3e8704851431b543d7068b3e541db7ec2998c08ff9d29d932dfd628ebf75e48743d9053a249c8f84941d047bb256d09b4907a4d7de361a80eb995aee64ddece0438e0d72bcca6726ea6a4456fcc74a75718410f62e4d0b6322a3fca087d07e4544ff90eb6ff6c743916776ebb0cc26f363435fdd793956fda30d0794ea51ad4450295f41c92aaca346aa3406aba8ea800ef8537da36e71582fde700783d611a3f7de333509a516e3d5cdfb46a5b40e9d659d4df68da0cb4b4a5ac96468d75efb4e732242047fa8a680497e8b638c0b68a8f3aae23db11c9af3cba6a456c6e1af82f4699da80990de51779c426e1599914b5055a6fe86db1af965f0d)) else (if i < 15 then (if i < 14 then 0xd995b07e8098d88a8cad22a1d4c3951d6e0ce06381f5a5fdc05a54403b0391cb745776008607e3629ea51950267855c30991cd7d2442a19dfdcf6031c55e047f9622150cefee40df0293cb09018e4735f4ad3465d7a562dbc0de94fe93d6d3640cf150476df91d96527b0f50fa412c010c0efa12ce96d149e50814f53a2e7b56303517a6c4c6621bdf5b0d50f143c604a21083d8e6be92a150c895c25bd2e9055871ea59b5043a8ca8117683cf6fc8eea3376681a7e5601eb636a087751dc2f19df0b85f71d6e45040ad3a40d4377e47312874b8253745cfa4c4a41d2f0d4e259d295d6a34e8ac6f7d6c5a74c9ba2e7b56090818e284e3263310d616c878c0ab4e7ecf91d396e905d0d97d9f7355298fc439a8b751b331814f9f05b9aa9f80bea7e340db40841e259d2e4461834e1346c50418f43c60539c0c1147bc65ad51a834aeb5180f7dab1f1d0f86f2edad02ddbc216984fc5b931797ef205bfba11f1496d83e034e2b95fd5c37a292da6cecd448e12f24ee0556b8eca3b2df1cc87aad7a0b56f00872f3dd18a769619d0196f7d06d9fd808dc771920e05a10de2806a89eb3d6cfe4018836cfe48afc362a15fef835428a9a1f747a9de18b427f52865eba8c26fb0e506945a78a3cf15f539645a18f5c1a0b753b4654335ddc5262dc5b31ccb839a57374c925d2d7b2838a29f97740df1baee1d2f536b975c982d5d6410e80f693b1e49329d50fe6d46c757f1c30bfc414def5e3f7d6171253e00dbd09965f1a3cf4180c407f856b2c9115909a55b586d8c7643c16d03813a958803ef24e7448f8495960df511480c24c7483702e25696e31b5a0531fc853250d2dc30dd1477e02ac5a98fe468a65ac222901da9c3e4a1ba3d5289cad221ff7f314ae85065906e35b1e49c2e292b49a5a6998097ff86732507c05295e8dc9ffc283c7f04a804d0ff10f8a2f45edd732dfb4aceac1d4b14d91720a00bdc5f08cd8eb2999fb4defb3c2ea0a36c4ff96fde00ed8c87c02fee1b58a6e43661a4ff6f06e18f0751fa4366305c3b74fb90531001b2b57ff5f5fbefe627781a041aea4bdbe40b53797ef2627ac7ad674c322b368cf81514205ceb85508a0dd86d6d5cc603689e0ac414b6e2d1a63ee754f31611cbda54a28871515e5cc9cc4333d45ca535193816d026e1b681073deaa002841095502a3442aeeb9a07c11da22bc97ff836fe86f6b1e29db109ab4cf520a0f4a665d58d7ceacbe18834b768e0d50d409bc95accb737b443e9bc9b3f0dedf0c419cbd3785ae40c7528de3749e63abffa9b3125e20de712e069deceb208b86488cb0e06f6be4ae99d02ec5a7e561877b3e41f618151cc6d53e4fa034c0ec62e710ffed4f279772e58f33de74ae95f40b8a87e596ca4fc4fb9012fb08e781dc99b82d17ff978816bffa265ec86bdb3b762527734010 else 0xddfba1b0a2344c7bd4510e633b3d2aa114909690ae1341da5310610bc09ab5e1220afdcc59fb0ee504e8837576c389b0756a7c52f513c43322f5b3dcb0a23c466877033d8704426620ccc065bf00c7b4c6c1ab1e2333817872fd066182df48a0381250ca089b1ea544ea2d13d7e0690a83587c5b8837ef8b4324650be5c9a98a7b21af61043af71146f28afcc0a3a9368614440503b564870443acd6264977907380b95e12d4e6221d443c1558608d8ed68315a1549f6d47c29ce0027860f02a98058f619cc519381798c43539c004464e04f054524ed7981cf10df529de5fd8a21c5288580800c751980157dc3398d01886a1282f62847e8a216aaffa1aa1871bffb99cc988c1f1ac5a20fbfc98001f1a87a94763c8a1ffee3d710734e5dc677b1a4a228eb692b8e326707c0d1f531a49fb93a722f4fcac9fbac8992b257306a8371da21c944248d4a120fcc0a52e3bd14983482a197b8a114aec6b2432b96d0bc8d95a02a5b57893f16e4c5e5fbc816fee847c773c202731db9e109f82b276468ed70c4254a5f8e64d9f9b5db2b96f7a4c53048e4ded1c954994f03549f94e97c3106d9ee7b431e2a2068c7757503eb5bb7f0730fd4d5aa2bdb79f8024c0086714eda70402c3c90bddb1dae63df76ce490add832b670ce85096d5e8861a700783df7991a568c5ace25c768fe1e8449e5dcc16dcd25b64adef195bc1eda785d6c5e9cd1e885a8b58eb2b679bef19e4adecf899587607be633b5e6b478653c547f21e0688891e9e53a693b01eb25b42ed6712a149adcf8cc14e9d3066bfc836d47a9bed59caea1f46472adf272b86f236487c7a6d50b427e1d8fdfcc563e25d287d6e02a2bfb97160d4975f4c3ecb25ff0b16e57c723b5c81beed816936c5c31a058013b2692ad57c76535c50eb5a06f2934b0139252903019fb364bdef3bcdac320956d838e399802731d7621b9a1263b5d4790549f14dcd545e441f43721beed40a1ec20b618b4a180f53b10d6c617b7c85b931797ef205bfba16196fe8539bb66c7a3d689e118349c678e65dbdaafeee4e034e3900c340e511239b0ca1f0e415b3e4364ae65ee125296c5c356df90dffc24cf79d8d1abd6294d01c929b0a9a0ab3469c3f3c46e2b1b021c360038e2cbc998a8690aa5887b8f054bfe0ca4ed21ee13297197295be29e02838cb94780a0008f0708a57a7b8f21999f092f531420f412e18f5f79cd87309968d86fb4e60894da90c306ac42105ab6d27b3b3229a00b691cea4ed55990ae2c50f4defe6f2cbee8a1beb8165e4733c1442555b3e436945b8253335c2c1da3f7de700ef829e0a5016368e8a680216133ba9537da76969c651401df038894c004840a50e4360150e72a32d5c1258967d162167800ed00121024104b3cab102eaa385aa28db78d1746df433a27bde308301e4eade7e) else (if i < 16 then 0x89a386eeeaea9dee555bd1faab0a20bbc514887a565018df88a012310b58b1e04b96637c9fba8ff24070cb812a8774fc7e0d4011885c7b58b1e40209401cade3bd7f4ac079de06807ed63b9e8355a9eea8abff83c0e82fdc98df5b08e7ae6dc71078d502f81d8b3c0e896ed93d03ae8777ad54e3c2e03864c81683c6b17a76ee489b14b19c418bda7ed347286a7ea62b19c8117b37b443ced8d54de8de5019729f17bdbe254265d884a90c82ac9b111bd676faedf11d8c7876f899ecf7d2bb14d85c828071704c39ec0dc49ed58336144c418efc04c86b8ce20c5289bb9276c5ec69b9220c6a899db22f51cd6a0d5b4e2597416d8521fd08a886b048d1a57ad5291d6f649329e0964c53006a0514acac601b01df00a0fd2dde2b1417d3c050519828023c267e8f00f07a36db199f51f87d0df6a3396ba1bed06572d4f5b151f499c4278ec1ebd33290d627537b7d84e4be11bd6a9afdc7451320d2a6dcfce032c0657daa0be94f9472d0e3108516943e00eb09fa843037b537b41af6c883132f66e4eaf37572d715e31ea59b86036e7d12cf82c402a9a8a0536722e48be7009c9b4b1b4eb1a4f2c9b7961fc488bed17e61e032d45020c55c67c1601dc0ba417e0a5f6b7fcad161fa2bf017d284550b008c08e6605fce368e0333502d7832c4b7e0b699abdc724849437243d8e9beb909532c4ca8580770286f45469bb1017a34c419b592e517828861361bf6df531961831b46b94314b1a45e88392ea7ca1e3368f37b5fd59d883d8740d6d1c6a96bc9b07c11db7370c0bc9b2d5034339fa92d95f4c4ea67ce25b180d4ac7d83527e4de5ec63db12e28a52e378b64c6845b125b7ee4b70ed853f230c98024c0092c5cf1bd487f824f8d82914692c68dc572b247f85614ac901354379dfb3406f157b527a2fa81ed1167be85ed8c06a6f031d4bfe0984120e37d2ff875f05b02c4581f816a5d3cc071fe27fc9b0e8dac1b2aac24572b48ac2873dd683d06a4a08a3d55c5834541a31c78e9b5c5a9c06bf47bbb91101d0eeba63d459e1c53b5984b19604aa1ee2e23666d2ee68256968371aadda4d03e3ade2434501b30c6681e8b1fec78ada1915f671222f1bbc12d3187d069ef221abc74dae5fa3d27997a42eb3900a1da1ad16fb3ceae33863a85b20d21e98ea7bf9851327927eab055921155f79120c6aade007b816bf418991c73304adb3fb36c5c358cfe47339421771e9869dabb10108310e84ac384b02ff2fa058b23df2ec43e81413c0ebef20347a82073a70cee8d4203c2df513def188ed05d8414c508eb1fb09c97515b93ad14e4e7f9867b2f54e1b76bab57169cf123100baa75d3a2ec1fe4a60dd17af92e362ccc46cb133fff25e77722ea28a60a28b73e259ef7d9d68b6aa8aaad8affe04b5447f4e37d4c181250d4f9dbdc3c4c670279e60a8 else (if i < 17 then 0x87d964cf048b645add6887a717f3ff802f19228d90e129ff89c3d2cc51d35c63bfe639501f42517e8618df4bba116a7bff972fe55a04b8829b1ba0535ff856c010950f64119442c49ef5d59c6242109842ba615fffc212f274d78bab3c42210317478c02cf5f48de860071b30da1b01e70506bef9c6e0e3661b436004e0a517df07650642ad4ed08cc1d1de5dc599c35743d0fcf48c40596cc0084dae114c6fe48db9c545dd9d08f62ef55b97404459919970c94223a2eef066acb5708a64e21cea1ba3c908bad9e93884218c02c63f7d2341d202dd493bdec9423d1d862f65c472d5b840ed174f91a77b28323f7d2358308683acfc1cc1d2f6e4980e41c9e0cc2e70d402de080b2ef2e193c06d2b67a4ea1b85c423cee8654c06684817cc14ea34ab19eed9c590dcc310cdc37849d78128725cf5032782f46012e0ec8c3022c1483dd2e51d99993dac64b9d072ceefb1a6031ddd9a8693988621a702fb480d1a4e64cb5e0b9b2e8b701df56b8404bb56dd23ed21fc431cc99a4f8244180fc17f690fe218e64cd27c1220c07e0bcad7110cd7743b6a52550fc71fa176dba6d7a5307383cfc695343e745b8f63525cc61083fea1f690fe218e64cd27c1220c00e0bf97800f09a09a8f198911681681c673de554229212d215d0283b82220c1c9dd142645c1ed3885634d1765e0bcda1341c9dd142645c1ed3885634d1765e0bcda8167ba840358a52b83f6bd9d974c6ca39d3f1b4454557df109a7ea412ae5686d8747b642e0090aad0a48b8befe62d5cfbc17ee38504b27bd01c32603de4c4103a7ce146131f2fdc2f10a8727bd0257c8d107c9794ab3a6dc260eff0508d23b6b05fa46233a2eb2a5a317279c8d7f2ad3c9793dfcc35b7d23111aac6b2fe5d08c9869d590dfd2a7961c97f7ce7680b38b3a8aac6808ce0cab2ee5d1b143f9637367eae46eec22df40ef43f908d0178dd4ceec2aac6808c8d0174d5c50046ea30efc716d7788d37b42df4117dc32a6eee4834d5398434e8cbfeac1d6b88121de5dd4cfe5fa75eb465fc96be7560ea58ccedad717b1a564d397262f62ecded6333b730065c26d1bccf17a2f77b58ed622a1d653326568defb3c2ee1a36f92ff2f4360ca18decded4215425ce036c6eab70c7b13f1b9f38c4f71a1723387739fa9f389a74bc60c3bab8a5f3971b02a5fb901e5dd73c4fa56e181ef2e6afd1220f84a25fb9c6d289a582d1bf77c6338205763756b7611cf7ab877d8c12a5150e5aa171c0db73d6667d4ca98a605f676685dfb4b83924578ffef3f63c9266721d7219cdb278eafe38617f8829b6f3811bed393b0e7d821d02d09b19fdc7184f67c6f0e9b017589fdccb6301938fe171543bddc36215d33fb14a4a1a99af280fffc281fff08ca20e4bdcc54e241ef031855157ff08ca20e81d73b8b07b3b0c545492ca else 0x542d004950aee18ea8149c7543fd729d420ac36bcc530033a12ad752f1a1386d4929373c155ab0526630a7dd40071c9fb56c727f47aa7d06fb5852bef1b0670fca7760d005ac7ce3c249a9d5bc7588bfae77fc1b4a6dc91f52e7c53f64003e02ba81cfb432e93943e1da0b12c129d0da8bb07f92c42780b2eea67277c2683959f8d0cb97cb4598d8b8d51b78b9d225a5212c04fb77f0f36fdce34bdc641ce0f40ce997336dedda915eea450da517de70572e912f10ffe09)))))
def rankMode11 (i mode : Nat) : Nat × Nat := let v := packedAt rankHeader11 ((2*i+mode)*24) 24; (v &&& 63,v >>> 6)
def rankHeader12 (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0x48448c94000000445ed244388a4406d043d58a435b1843434943075742f6c742a8db000000427712424eca420dd741f08a41bf1141a6c84163d941438a40ce1e40b7c7407697405f884039104022893ff3133fe1c73fa6953f92c73f66d23f45093f14923f05073ed0d50000003e9a543e7e483e2a930000003df2940000003dba133d99083d3e573d1c093ce5543cc4c93c85543c64493c1e983c04493bd4503bb3c93b62543b4d483b0b563ae70a3ab0d00000003a6cd53a4a0a39fd5d39e34839ab553998c8396054393d0a38fcd500000038a99838844b38311d38100837d81037ad0a375bd937304c36e71936c5c936765636504a360dd635f50b35ab9a3586ca353d5a35274834f89200000034c09334a888346955344e8b34051a33ef4833905c337647332cda331d8732d41a32b888324d21323b0731f69731e08731815a00000031201b310fc730d61430b08a3065173051c73006962fe88a2f8e5d0000002f4ed42f2f492eed152edb872eaa102e8ec82e55560000002e16d12e08072dbd582dacc82d86502d6bc82d3d130000002d09912cf7872cb4582ca1482c61562c424a2c02562bf0072bc2112ba1c82b6e932b56c82b10d82affc72a86a02a670829f71829e947298a98296e0a293c9229220828f013000000289d57288e87285095283d082800d727eb0827ad57279409275917000000271f9527070a26e24f26ce4826a68f269747266e0f26560826095425f407259f9225798a2537d725130a24e053000000249ed424800a24469524228a23e4d723cd08239cd3238109234cd52333882330c123198822dd9722bf09228197000000224a9522228b21e21721c4092162da21410820e91420d108208fd7207f472042d62026ca1fe01a1fd2471f9ad31f86091f48561f33c81efb131ee4c71eab531e844b1e5bd01e40481e17111dfa491dd3d01dbc481d8d931d7d871d4fd21d2a091cd5551cc7871c87141c6f491c171b1c04c81bbf551ba9491b4fda1b3d871afc131ae5c71aa4941a8e071a291c00000019df9719c1c8196eda1954c8191e501906c718b696188fca185dcf184009180cd217ff0717a99a000000175519173ec816dc9916c189166419165008161cd216068815bd9415a607156054154fc714d65e0000001472dc1457491428501414c713bb5913a707134cdc13350812ed9512d549128f970000001210a400000011ae190000001137e100000010b3271077940ffd650000000f75270f02d50f00410eb1160e38250000000dc9630d9a510d425e0d0c120ca6620c7c900c209e0bcb190b64670b14530a97e00a3dda09d467099ad309489b08ea9b0882a708658c080d5d07d35107642207399106e1dd06a5d106236005b75a053fde04fb50045b2503d51d0324e902a41d01db6b01861200d367006f96000021 else 0x42918017cc7fd5937fb6487f74180000007f3b947f1f0a7eead57ec28a7e8f547e76487e211d7e034a7da65c0000007d76127d5a887cebdb7cc1cb7c741a7c5cc97c20950000007bd5d77bbacb7b7e127b69877b32147b1c087ada570000007a97577a7f497a51920000007a081900000079c357000000798f110000007951577935ca78f85578d34a789654787b88784a12000000780e9577fa8777c31477988a77429877298776c8d876b048767953000000763c15761aca75e8d375d8c7759996757c0975439375314774d31a74b8c974701974584874189574058773dd1073cbc7739c127386c973569273418873029700000072cb5572bac8728f1172728972319672198871d81600000071a452718bc8715a54713d89710d1370ea8970cbcc000000708e96707dc77010d96ff3096fbed36f9dca6f63546f4b886ed0da6ea98b6e6d550000006e22976df90c6dbc526da4c86d565c6d384a6cda576cc2c86c77da6c51ca6c10d66bf8476bb4d76b83cc6b4b940000006af9996ad6096a99d56a6a4c6a38d400000069fe1369e0c8696c9a6954c869149868ee0b68b4d40000006890cc68830768565068404867f65967e8876792586775c96736d7671ac966d19666b5886684146672476634556613cb65e11400000065955b65780764e61e64c10d649fcc0000006451d964360a63cadd63920e63439b63220b62d3d900000062871b000000624f91000000620e1600000061d392000000617f570000006133d900000060f19560cb8960685860484a6010560000005fd7145fa28c5f69950000005f30505f16495ee1135ebb8c5e81d45e6e875e2e955e068b5dcd145da60b5d63155d3fc95d03d65cf3875ca65b5c840c5c53130000005c019b5bec075bbecf5b980a5b58575b48875b0b165af5475ac5d15a970b5a491c5a35c959f3da59d3c959959700000059581459284d58ee5458dc07588edc58708a5842925827ca57e5da57cc485796135783c7574615572d4a56ea9900000056a5995696075631da561b8955c11a55b147553ae000000054fad354e148548a57547548543295540cc953d48f53c6c7537b56536348531c9553024952b0d65296495256d452468751e9da0000005196d7518847513a975129c750ecd350d18a509214507c475029585015084fb05b4f95094f36da0000004ec39e4ea6884e75124e56c84e10d90000004ddc114dc0094d8bd54d74484d58cc4d47074cef1a4cd8484ca6504c8cc94c57d30000004c16164c00c74bae594b98c74b6f904b58484b09184aeb894ab1544a798d4a29144a0e0849a6974998c74963544945c8490c5248ecc948ae56488b4a4842d900000047f25747d089477f194768084722d847014946a819468d49465a94463e0845f45845cccb458fd5457a48452c5845148844de1544c0) else (if i < 3 then 0x9b7d099b75439b5ec79b5c039b3c889b39c39b2c070000009b13499b0b839af5099aef039adc489ad4839abe899abbc39aae079aab439a8ccb9a89039a6c8a0000009a448a9a41c39a30c79a29039a18879a15c39a08079a054399f14800000099d48999cc8399a48c99a1c3999407999143997b48997883995a49995283993809993543992307991b4398f9c998f70398e30898e04398cd0998ca4398bc8798b4c398a189989ec3988b899888c398628e985fc3984c899849c3983448983183982108981e4397ff0a97fc4397e90997e64397c98a97c6c397b38997b0c397944b000000977ac9977803974f4d974c8397324a972a8397194797118396f78996efc396dc8996d9c396c94896c58396b24900000096938a968bc39675879672c3966507966243964f09964c43963349963083960c8c9609c395f30995f04395dfc895d8c395c58895c2c395b50795b24395a187959ec39588c89582c3956ec70000009555c9955303954288953b83952b089528439515889512c394fb0994f6c394d94a94d68394c60894c34394b58794ad839499889496c3948148947983946389945d83944c47944483942a889427c3941748940f8393ff0893fc4393ebc800000093d94893d34393be0793bb4393ad8793aac3939008938d43937a889377c3936a07936743935507935243933f099338039324c9931ec393014992fe8392ea0992e74392d40992d14392b90900000092a64792a383929049928883927347927083925d49925583923bca9239039225c90000009215879212c391fc8991f9c391dc8b91d48391c14991be8391ae0891ab43919809919543918687000000916b49916883915808915543914209913f439129489126839118c791160390fdc990fb0390e50a90df0390d14790ce8390ba4790b78390a4c890a203908ec9908c03907b889078c3906548906283904c8a9049c3903948000000902508902243900ec8900c038ff7498ff4838fde8a0000008fc4c88fc2038fa98a8fa6c38f8fc88f8d038f7f478f7c838f668a8f63c38f48c98f46038f2b4a0000008f118a8eec8a8ebe518e930c8e385c8e1d498ddfd50000008d97958d79898d4b518d35478d12cc8cf5498cb6d78ca6078c73128c65478c161a8bf9898bb6588b9fc98b5e588b40098b09548af1c98aae588a854c8a51150000008a1c148a080789ba5b000000896ad889564889071c00000088a9da8890898846590000008813d100000087da510000008794d387660b871e5800000086d99686b18b86685886434a85fb1585e189859f96858e8785555685380984c85d84b5c88462d700000083fb9b00000083ae198390c983509600000083025782ee4882cb8d82ac8882779100000082401182234881d79481b28a8174d5815ac9810cda80e40c808f9d806e4b80 else (if i < 4 then 0x43ac72c8ac6c03ac5b88ac5783ac3a0bac3743ac1e88ac1bc3ac0b48000000abeb4aabe883abd508abd243abc487abc1c3abb148000000ab9ac8ab92c3ab7f89ab77c3ab5e8aab5bc3ab45caab4043ab2d08ab2a43ab078cab04c3aae9c9aae703aace49aac843aab208aaab03aa8f0a000000aa6f8aaa6ac3aa5a48aa5783aa4708aa3f03aa2fc7aa2d03aa0d8caa0ac3a9ec0ca9e943a9d34a000000a9b809a9b543a98e0ba98b43a96fcca96d03a9544aa95183a941c7a93f03a92bc8000000a91488a90c83a8fc08a8f943a8e34aa8db43a8c54aa8c283a8ac8aa8a9c3a893caa89103a87b0aa87843a8624aa85a43a8408aa83dc3a827caa82503a80f0a000000a7f408a7f143a7d849a7d043a7ba4aa7b783a791cba78f03a77949a77683a76188a75ec3a748c9a74603a7300aa72d43a7138a000000a6ea8ca6e7c3a6d1c9a6c9c3a6a5cb000000a69289000000a66e8c000000a64f4b000000a63808000000a61d09000000a5ffc9000000a5ed48000000a5dc87a5d683a5b648000000a5a587a5a2c3a58cc9a58a03a57588a572c3a55f88a55cc3a54c48a546c3a530c9000000a51589a512c3a4f68aa4f3c3a4e347a4e083a4d008a4cd43a4bcc8a4ba03a4a607a4a183a48bc8000000a47908a47103a4558ba452c3a44207a43f43a41a8ba417c3a3fbc9a3f903a3e2c9a3e003a3c909a3c143a3b387a3b0c3a398c8a39603a37a0b000000a35b4aa35883a33f08a33c43a32909a32643a31887a310c3a2f78aa2efc3a2df48a2dc83a2cc08a2c6c3a2b0caa2a903a2930aa29043a27d08000000a26847a26583a257c7a25503a23c09a23943a223c8a22103a20a09a20743a1f109a1e943a1d588a1d2c3a1bf89a1bcc3a1a989a1a6c3a19408000000a18387a180c3a17247a16a83a1548aa151c3a14187a13ec3a12b88a123c3a11348a11083a0eb4ba0e883a0d987000000a0be0aa0bb43a0aac7a0a803a08c0aa08943a07507a07243a055c9a04e03a03908a03643a02309a02043a012870000009ffac99ff8039fe20a9fdc039fba4c0000009f9c8a9f99c39f88479f80839f69489f66839f4a499f47839f37089f34439f21099f19039f08889f05c39ef5489ef2839edf490000009ec5c89ec3039eb5479eb2839e990a9e91039e7dc99e7b039e6a889e67c39e4b499e48839e38089e35439e22089e1f439e11879e0ec39e01079dfe439df0870000009dd84a9dd5839dc7c79dc0039dacc99daa039d99889d95839d738b0000009d588a9d55c39d44479d41839d2a889d22839d00cb9cfe039cea489ce7839cd9c79cd7039cc6889cc3c39cab490000009c878c9c84c39c6e499c67439c4e8a9c4bc39c3b489c38839c22889c1fc39c0e889c0bc39bfb489bf8839be1899bdec39bcb899bc8c39bb8489bb5839ba7c79ba5039b9747 else 0xb807c3b7f1cab7ef03b7d60ab7d343b7ba8bb7b7c3b79ecab79c03b7834b000000b76588b762c3b74289000000b72d47b72583b706c9b70403b6e149b6de83b6c2c9b6be83b6acc8000000b69988b69183b6690db66643b6404bb63d83b61bcbb61903b60888000000b5ec49b5e443b5c04cb5bd83b59d0ab59a43b589c8b58703b5694bb56383b54a8ab547c3b530ca000000b51608b51343b4fa89b4f2c3b4df89b4d9c3b4c3c9b4be03b4a50ab4a243b48c49b48803b46ecab46c03b4560ab45343b43709b43443b423c8000000b40d88b40ac3b3fa48b3f783b3e108b3de43b3cdc8b3cb03b3ba88b3b7c3b3a748000000b38409b38143b370c8b36e03b35d88b35783b34708b34443b32a89b327c3b30f0ab30c43b2f909b2f143b2d8cab2d603b2c00ab2bd43b2acc8b2aa03b28d8b000000b27708b27443b26109b25e43b2414cb23e83b2260ab22343b21009b20d43b1f24a000000b1db49000000b1b1cb000000b190cc000000b17509b16d43b1520ab14f43b13c09b13943b115ccb11303b0f9cab0f703b0e6c7b0e403b0d108000000b0bac7b0b803b0a788b0a4c3b08e88b08bc3b07409b06f83b05f08b05c43b04909b04643b03309b02e83b01a09000000afffc9affd03afe18aafdec3afbe4b000000af9accaf9803af7d0aaf7a43af590aaf5103af220eaf1f43aefe0caefb43aede4aaedb83aec988aec6c3aeaac9aea303ae8bc8ae85c3ae7288ae6fc3ae5789ae54c3ae3ecaae3c03ae260aae2343ae1008ae09c3adebcaade583add7c7000000adb9c9adb703ada947ada683ad98c7000000ad8349ad8083ad72c7ad7003ad5dc8ad5b03ad4a88ad47c3ad3448ad3183ad2108000000ad0748ad0483acf6c7acf403ace388ace0c3accf47acc943acb5c8acb303aca288ac9c43ac8609ac83)))
def rankPayload12 (i : Nat) : Nat := (if i < 12 then (if i < 6 then (if i < 3 then (if i < 1 then 0x66e8d528f923642fb34961114558f1f9fdfd76169c5a0448641c138b3b50b226fc8ad94f7c99443c6d943e43867f7fee8476c16e5bc2ed0d866527f5dcb783da2ca04eddfdb487ae5df92f26eb9503ff1516ca57b2934f14c3ed6f0bf0353280318a22f5afb2003f5b78bf800dc2d69ce6418bc6faadf0351fd11431e8a771f06d2e2b6265ba3d6c90632989a69c2fa5ffe557c9d8f69b2641167d59c76c028382f10e9080e58c6ca90ba6bfb0f59b16844fc0b486c0a10330398636a4953270afc340e9e3f8071c63476c1b8f4c6cf8d7f5840ec063bde797203964be1749fcd36542287d911863d4f4436540f80174e064c72b406ce6bd187b1d7e404b70b2b244163c8c23431be21091d502572c0a32850818bde8aa2d7a6817e115cf16380c41f67b82d746d18b56c21f18dd3d4ad01cbecf71af6682e10b4a7db681c0a1037a0748ad9030b486c41c5840e37fa6cabef15170b83add3ad83b1e8a7a202efcf9d39241672485cd028cb4934d2997bf541de51bd24e1487f4a23085b1f4a7506848a2f0bb4938c4beff80f5d09d4186a870da8dbe260dd3d53970633c4370e5aa133ef10ac0e723d02457ca43fa3b700b7f1d2286b479a7dbeb750dd1158f9f3af10b93add032a0ef34a6559fcdf1393dca8127928518b248f072455036c4658f50f53d554395c33d4dc82e1071c0c98e23d39230c7888ab406cf7a387c2c2072c2c97304f88c2a4e14a4362d7af0bbcbf153ad4a812595a0764a0bdd6c21f1b521bb4721d084c4a6048cb9824c33bdeb560d47cdfe814206565474c84e197df90d8490dba6ca38da3162d842e107545ebe60b482db3dc19ee6c5840ebd1c3e205109d36b042e07d6bf94888aa0ef3e7ce9d2a06f33a1e44a85b1fd11a0519d3561ce8a97f824eb8869ff692688a6578519c3790798f9d2adfca6bc4ea134e44c4fa5934ac0afb08f52a7a7aaf9f3af932ce01b280cf9131611e944be153db2f254370dd319188cb2e26385d509a73a540db2743d4d514396748064e639f4b1efe52340b48ea7b2625234a694397dd6ea1998dc7190abe4c4fc539326935c448a588d27b19e265b986d6057cb9c2655952a42a85944610b3208ac6521452d8fa9d306175d0948550f75b494461073edf91946e9920ed7f693d234a9d0da31b542cc185c4e51ad27a466e7738a2e31998dc74a9f01eb222b1c26755934a2ba6eb4ad339867c55b68cb9f0a8632158dd95487f4fb607c47ce8c032641128df66a2cbada5afc5aa0ed6857c8a65a47f38d8f675f2458c922923b4d90722259498650f1375c29476c4a328589465072e9c750465b02741d7a497de21681de8fa230c78ca8ac2130bb083afbc3e1eb0aed32761f82468ce918d974444d79e955f9cc16d02d25b22892cab70b818a8ac2db476ddefd1bc4a1ea3e27bd916d6ce8aa else (if i < 2 then 0x4a4052d0faeadcff8b63862c29f931b15cdf671156b407061890b1e15ca241841697b659de88693de83e7327c350f83694115fdc85bcb76cafe2528e70dc12cf103274d2792d11a73e540da51750d65083cec82305e137c8d6768813bf00cf967883031c186321943da49e73845fec3c29307bd8900ef5693d2742fc043c211017d208a15534f7e6904ed947241c0063b922ca47aa4f200f8c54323b431607ee6cf704a03543a610bf3bc2eb655681c430181fa2bebf2b543b29e3651ce178bf99dd8b07d03e09738986242c780d19c6fa18b07a4a7bf63eb78c40e8034c207061ab6dd1e3ab8543eb306a09524d876cb3df07429e2ade941c2eab573d96516c825d010b506c91c5fceb609065e330698984d7dd15ff093c90bbebf83691411ce62c01dd18a61f6b4d6df66a07a4b05137d97817c62a2210dc5fcd66ff4d6803ba314d70d69adbecd55bd94a22ae2b644d6c904833d9040b81bd7cd3dcf70a8d28aba508d171e05c11ae467ef4c28ffa4c845c01391c4c1c123bd0c95855fe076bf1847cd65ecd01adc089307f84151639c459152ae504c5a34a3a3a5444c0109fa5a1c8e6fde16187b7ba234e483072fb207e75b7919a78a69e47ffb35003ba207f8de0b71be801d6de2fe1416928a6b4a22a52fd6fd96583a140d89b2bdc2e0d311fd00f8ff0bf14c62920c34fec80a0c11e3bc915e43fbd6ab88d0bd3f22c49305038a222d265a7601aeb61b0b010067418728b0fb36e690b85877546584f64f1ac72bfb49287dcbb01452d8c8291fa4b25515c9da07a1907eabd743044f788bdda2e5ffc738021d5449fb3c7b88211316d04c43535d24ad626422a1be0b33f017905d361281e21465c6438ad269655c84e13bfb46d49a495a2486121150d90940e7a898a7aefd108a65911ec6da32eab64461d2974495c8914b3f1d02531b192c73ddfdaf83909c2cabd6e9ac4832a6a0b62228ab9e3f742c5dc3dc1f06d6d40392ca8c3ba1e3e0905ac30858c295692b0575b045124d858004d522c4972f92c3baa32c27b278d7f4c4fed24a1f72ec0514b6320a47e92c9545727681e8641faaf5d0c113debef2dda2e5ffc731761d5449fb3c6ca5c2ce3f81ad47f4c6200c2f9a7f0660460db13050359bfd7e607f81b2970a0bf047f4f8bc68a1b1880303274c3fc2f9a7256cf6417475abf3eb607d3ca2d90c5e07c6195b45dd0b04e43b8ecf42eda39c9d9e99474d2170315cbabde47d11412e5a174c86cc65795b4822e01bfb5410a603bcb7161dd519613d93c6bfa627f69250fb976028a5b190523f4964aa2b93b40f4320fd57ae86089ef117bb45cbff8e62ec3aa893f678c01d6918a17f1881dc1a632934e07e29f1bc16444218d6d6d006e151152e1ce3c18a17eb7ac181a8fe9d6fd9075f44344cb745a7f15b090644d01b0ca288a249205 else 0x5cc21bd4205a702741d30c8d4eff5a103535cfe7090c8b82478c9ac8c19a74d9117daa31a02cd040e04347e84e6904f3eebbc85c171203118e24537fa2ee83be9dc490d50a97ce04f89af678b33a3bcdd18191db415260994e022c5446e51f26fee5d2b329ccbf2e0c358111b505af7d27571c2e36204734e32f61bfd369b0572c73a86dba3ce37081cbef0091a351fc6c70faf9a5cf243f2450a708d3ab37ebbe17022f569056cb5f78ba901816f9ce38ab6c1e309fcb830cf1287befd4385c754dd18acca708d3f6689af31a43cce4573c75483a2f5549dc66bc83c5b01b4964ef9b484d91d5d20ad42635dfe8235c2307a228d3b6386f5011cce7576d1e75393ae23a86af65d755cc40b4e0235021766754bc90c0ce0dea82aa111d6cf62e754d9ae15bd277a228d3a2081196604768ca7654b4601fa71ad7be93805f9857f7854a091e3573048d1837aa0aa99a3f4ef482a2d9d559ea2b169d3a301b0b81d040ed155f4544270d9868fbe7216de1093e9498aa6b6bdf49c091e302321c8bd5947c3aaf8f121819df85a0eb997061a4e82df39d4267a526dea94241d39b49627cdd35f83ebfd39455243fd371243659b4e4d227e9ae17478dbd2d185999da6a2350827a6aa30a7d4c571aaf428d66bf67a311bafc1fce0d240e77fd9cb2811d27401fa33bdeeb288d158402ddfe899711e9c60139c4e1b5de0b2a591f504d040e77b42e4f1b65d393aed20afbe5d7427ff9c3bfd1d08bb2e04f05767b6f5663017e44a566766bf6798508d9c349df7fcf80fd119fae99f7a1a74f9a83e2d46827167e61423765ff382ee838e2afaae375de0b1a481d30ec480bf173e4539ac6abd0f01b4fbeef69afc1e614682070112e4f1ae240638a8ce975d57dfe7003f55eb46cb532abd4084d88a735e9c6333e90545b11ba415504d240e8b62ace2a62e674469cc0eff5f82b297478db2f28f827c0597a2fbe086edc02b9455ad563b0f3dec4225ff0a0e544287b173f3bb16e2081c292216f2250c1a762a6ca09452942d42eae5e300e19352f72abfb80905c705b62b495ff0e765e1a20e8ced042922762aced8b3b473d0a3e468835071fc33bb24f76cb834cb8b3b350ae55d193735ce1f2508a40ab5a72a92639dd55614142345648fd581a0b5cf097402ff8607029687c4164d92860c09043f93c9385056c0707452fce6485bca16a171f783e257c0f7528de1cba1ed029f8d940da91ea81fe0da4294816f17a5776665da14b385c0f61c12c9c4c342d42a42c7ae6cc6face225ff09ee43656fe3b036a44936ee8a87a906569d6ad961b01f18a29f8f64e9970e31f6765dc0e7b83f4ca174019af80f5a608e56905307b3b2e0fa0ff882072cb80ed3c8d05a7898b7ebece20be4361d1e2557b6308ab64803e0680938cb097dc03380d0b700075bc2e935a57c)) else (if i < 4 then 0xa605f51829edf337058190ae1140794768e0d6c1dd94e3e63a377b36199c3097fbf021072c55e739cc5522a7b6541ab477b195d318a0041c893fbc8079343a17774c5094737d556154d0fb7897dd0c70f229f1d82900261468e796f212c87a905d00dd85ba084aa39e97a43c5a63d8c9b55023b374de717ed3b3c34ec2d9ab1d819c39a2bd13457501ca504298c9d76d6824b0ef0c5b1de790020e47cd5386ca9a1f29b6f6ac40cccd0efa1bb16d0ca1f7a18012321b41630bc54541a8024e41f98b01e39d1a5224c1fe63c72c0107255c0c81976bd1f1b97123645e2851573c154798015e20649a8791824049c85f23a05c14895f8dc836a145e8a57d0c03911621e667c4a91d1823a6eb8c712612442b1920221c0ca145601cf15e246c8007e3203a569aff002c64548d107231c3491d30a0849181531e314368010f234ba8bfcfe83d032284288011cbb7b607d07e3c436b510721540ae023b6dc25947317466764e3b26c43e60e12e4922bd8cc262e9f3909930d7e21f305c5ab1f5faaf62c7852fd0e7b24ccffcca3b5de8b7985609f6986fa859406d2511a637eeecfb0574c04647e6391bb8cd7aef545fae00d365a14223a207e1a0580d898dfa6235ea82741c465dfe8017545936e5d0ddb8109881f8dbd49a535fe1b13f4ddfe8a82cb5eda806bbda5c239da6cbf5cd9e02c46d81264cf369133b6901b99e7cfd51566bc77ed1b4ea7275ce340688219cda733930ea4e88129c2cee324e667e4f92febecc6bc07542acbb80b023a6765da84cec8d0166cb43db54c1568e7a7e1faf504d040e156f9c94d7247e023ce31a09d0726bd37f777a5e35259be41f491329c036746036dcc6765c18620f9a70497a2c2e03eabef123da96801b96853bb4b2d235c882cc1129c2c1931c41c069058f6c7ebb3ebbc162eba9f7a2a8323b635f549d300d1debef045e59f8b9f241d583263a20907d244ca700da125d75808f3b6e633b0b83cdd08ae78faaa5cd3390c9ae9c06ece3757de007e8a4fd18b7ce711ae3e362e2ce0a9ba33c599df3f5eff9c58949425d1cc1f7ce2ad27451aac8672432cb950d399697a202202f6298042a641389465073bdd8fa48a0ced2450a736f527baf7f4a5fce2e1c0654bb2c13936490f8552ea406cc3d9c4ff9f235c0c8eda4d441d5d37056c4b90ea54e622a4de1cfb157ab33975d3ed549d261d5c15ec264cccec5c13b33f037aa4d444f9a7275c63570ade93b71911d4451a779fd7e0562d3b2a5a36e391ba6963d74e03341d70e2ad155fde35bf52bac2dbc31b47cd240e532085e0214d07fb26a865931f5367f46f3ae8f7a220f0aa341fec91ad4b432d3f66923fcfdd480d82407ebfbc6bf036f5149fa371ea101a60418518b111dc66bc83c5b01b4964ef9b484d91d5d20ad42635dfe8235c23018ddc602c88fd else (if i < 5 then 0xf3e50a743287c005bceb52022da072e54cb9c782258da9b0f3ad4c98973da0c4138c11a254c5688500209c23f0c384c6486ff3e5fcd002ac6c5482714255561b711d332c4bef053dd14e03c6484908a9dd788d19e920336719a32c3dd2d05e3cf8885592da88ef850da2547c9396a26857ba380493c83107313c3cc294360ed3cacf0738243cbf96725da80faf904fd622002de558e05e8853d62233783bedef51b79072dc558a1bc133ad00058c839dff444f5eeb3540766d31678392050797f2ce4bb56ffa17c8215e3bfe21c25d0ec81b78bed47d505b3bba7a2dbdacde861ddcf6b9b917dc5a34af31dc6176f332656b7fc41e2976f5165b0374fec3bc422f881949fc6caa72598c879123b67b747ba73df7349c19481a5cb53fb0ef11aee9599a34e409ab5815fa2c8be218bef5bd21085d6324497a43fc317e2218e71cbe48af064bbeaa71b8330a7b95c6a8a6cc9d27aa70d845b0e0a917de28f36b9901f8f5b7d3b985efc90ae8f109a130c58ba3182e1aeea0324d48ed270f231e69f1aa0e92a24e449801b8ae5906901312476b69214fcb1eaaa42c7b432496d431c74829f1f38696d58d0333380f25af3b1af7de7478c3792e643a7fe24d77544f0325f74475c1d270f2788534d66a87b4ebcffc017127dd5cca0d01e62400f912a218c49e21324548ba3112eeaa546068e1b66a47693879052788486c28e6f18e7049cacf733755cb0475220041cb6bf157386deaa00a6da681902a5b51480f1ca0841f8a71424e53b9230332baceea3fc1cb7b0ee007d21075c1e621bde4892cde8d48093579208417b1b3ae0a46391d5ce0648d8772da48c0a93f78bed4ca620364958f7ed28c055ce1b29b0321324700daf940ab1b15208450a013bbe347482f12fbc14f743680f19215422a7754980641cb6bf0007d115934d0992387a43fcb02aa2c1152084509553badc47482f12fbc14f745380119215422a775e23457f8a9556afcaab6766625460bd8500d3a27ed10893c620dd42f1ebd7bc43bc2b0c398cfa421098a8a25dd573163c064289bf2a20e430ebd6b9959aa1b116ef1ff1841f941c3600674f5dd58cb4b34cc036499534fb362c12c9f92653d958c07ae9d2d8ce9b161ea175d37accc60f7ee445de976db67676104b3e28b6eabd600f47b29880d93f53a72dfba12c1d536bfa124f58e134c5ab2f35fcab621fa0efecca3e1caf594e99745bd20a76bed3833a4ea788623b6a7a8597f74858efec4d7ae475ac0af956c43f40d2f94e072de7808beef0b8c5c915f82f442ec739df073b878e0cdf5446f5198b16986141ee6f0327f4ded01a8ad68a3d85dd4a6d828190bfa8c9a8353af708430a103382e409df983b4e20be3e426b452a6dad09cf4bf01110cd8c67798353121b4f17751896f60d418bdf46cb09b80a494cbd117dd6796 else 0x6f492f8ca9b1d3d44574d5273ee7f3ef39021846ad9a1aa30be11765c7354d5363196b281162a4573cb74849777518f35ee134725a5ad77a92f6d0582795f98fee1bbdfdabdec65ce03465d0c955ec56829d28efd705728b6ca19b16fdc89b2b96e1a6d7a8c14e0144dd3ced021995acc2211f8c78d9c9dc5639ca52a8e790c29d54662f67618b86ad7dae195cb3db444825557910213db1820f44ab3184cf4f3b95ab44ff7a8b19e0f22d35bb45461b58341604f2457e001b431462858cb350f20675a8bfbcbb6ff104e4944b80308ad4c428bbffeccd7eb9015ab3a861824a11a1305e83e4a82ae9a4b59496cafee1385e5a260f914c639089f803d6861c7e531a6fe2de363d3959fe64050e7ecf07bc8ca3d6c61b24f6dd13fbb27c61680321e11fbb8194022840199f006475318e9bae31c4984910ac648088703200ef0a93aeb9ab9e43aca5daf407900611c4291b01e474438cd0623e49c85538e4050eb2974325b508b07b5bec0691823e420a1ad16b0c0f6cce7a7d4968001b2960a78bbaa7fe0dfa9b99a0044b540cdd777862cf2ccffff66a49660b77c16de4c4831c4621e9fce4e4fde93f408400deec9fd7aa1073734c64fc4c80346ef7643f2e4f1b741ada3dd97b371ccef148d537388e48afc1e2152a30c17a9a07027ddaf2f65b35fe3832442ba66ee6183611cf1bf04e34711b7b08b82f1bad3c77fde4b5e5edd041aa0a204221eb1d1b86b1abf08a066e89bc39c0537b2f44cb6aa1b9c0bd157386c43682d95fc25042a68aea1255ce065bceb6e87c8a1c76f77b6ceb4045bae21f2bf810ad4f65eb70151b98b1e12a897751bf537334d8896a819baeef0c59e599ff5a019a925982ddf059b583120c711ab7a7f797ed289feff88256ecf713648f14fcfeda551d43636eb6ebdd3a6cefb7168ccef728863923e4caea871d844ad5a7168b6e2bd62fde5bfe209574f45b14990500e52d8861d0b7d3f9441a5cb611f098637bce428bc9ef2c8202937d7dab373f95106672c7833496d72a3c6e9db611f0971a836b9d16672c999a60141a94dfdd9b49e525f79de97deb09527e3d49e6ca17554a4d11a68e9b2a9b84e9ab73a7d8b3e8f1af91aa111d7dd34943b679bc63659b444e352691e6928b05d72a41c681bd18d365a158af7ab9c366f36a687d0a627839eea9e4feca8c364a77040798552e6670a4704f1aa01f04eddec2eea6a7a8f43762c4336605e831261213284dd661e57cc0f3378062d3c1380b430a1141d80175294e92e3540b4b4afcc63432ecad7300940ab5b863ce8453f079a8b214b43eb1c31641aad43b96ed8def7997a204e1240799bc3776a619a07101ff2625678316f2a47baaf94a6a9a1f4e0a868c2134ad7501cc6b40289181f0d31ac7c87901e7b5b8815ff65b474f6f7dea6d4b8f36a20e4608d1583ed7))) else (if i < 9 then (if i < 7 then 0x940c15fcd832125b1e2882076a5053121954ec37208b469f6a61640d727895437ad53988433f10840e53724fb20bd6424b6a9279cf2a85d74c5db6e1f93b2e4f6aa50cfeb2138622fd5d9fb2fd8678a21c8bd5f8842071cae988cb9045a301178373bc47138691eb744f9cea198bd7d395d31cd415c08e09cfacd7a8c723d7dc8d35c0a65eaa6da86a3573dcfa840daa08cb6222654e4f16c42d03867e0a32d185a496747239824c32ef62a41c888cf8b6b67cc8486607335e8d7d9dd6840c896a28b496cd81391d0667eb37560c98e7cf28e81d92b0704a30b40d45014c486786cdd21d37d0b2344fcd13373f670f437cee020771c8770aa05df33d55089b162a4460cb372dbc41e9358abe33a70fd56c752f7b6d039129af55e33c81488d9f9e95b2f86e842620e175cdfd42068ea9079120e19e641168c444e4f116de20f49ac55f19d387eab63a97bdb681c894d7aaf19e40a446cfcf4ad97c3742131070ba33dcdfd29337deac91491c4448b9e58c615cf3ec3eae845cd903f32cdea18b496c33e6ad771de71261b40f570593c4e79f44faef79a7dd6de6920bd125570e60dcba0232dc187211a3772cfd5461d947c242936e0426cd316f70a1162a91d8b9c10584696766bd2dd023e64814e6c2e99519fd5554984a0b6f107a4d62af8ce9c3f55b1d4bdedb40e44a6bd578cf20522367e7a56cbe1ba10988385d4f691ea041eb93c44e011aa358e88d4530593d90306c7eb61d5461c9156cb17dc37421359fcd72d523a48624739feb392d3a507884e18fa9671dec91492c65538ad3c130ca1e11a5b7883d26b157c674e1faad8ea5ef6da0722535eabc67902911b3f3d2b65f0dd084c41c2e97b0bb3c7b250aa4b6f107a4d62af8ce9c3f55b1d4bdedb40e44a6bd578cf20522367e7a56cbe1ba10988385dad2338cd7af884207011423727888ea1a86d9fb535dc84e197d9f7cfa5fea042eba4e9ae6e922fd32067120579f64d956e72f98bbcd0232d72065b3c795021d19761d496889cb632a0460c9b32ce4854c8dfa1a466540871e7f37479b67408b35e8f2ec334725b76126736666d42e8e4f10cf5cf73621681ce6cd88cfa8aac5a3537bbba6ca9ed14c16423d6725b5bf53a7a736b3d42ce43a1f8b396c91c243123882c7888ce941eacaf5763f4e366b291c2d24b69a58f2f9e2ccb7021339172fdb2820bd4d191f3568092fab82172ad5b730d9ba1996c20709fef746ee1b738a9e0b15fa0749595e03aaf47825369675f6d974a37bd9af02240c05963188d2889cb6f374160c98e8334d6a738312aeaae4459cb6090c48ee3a66f4d2c7aa48df4cee918a6e47c3e6c0424721d3912cfa2a99f902883a19288a4b66cbadebe8c88d615732065b2af2239cf4f51036cba340bf08ae9ba62edbac64b54967ec748bfa3f3602f6864c25004 else (if i < 8 then 0xa00aad440c815033f6b01461f4f6893a3f5671b00ca7328ff5c0f0bad24b0b543b8a309b2ec9adc321dba658e66ac21acd45fe1b5d66d6c1bb611cfe86d1521540a9232aa40414b4d02e066d7f12364428bd01cf1228e79f2b287b1f190182bc748440e414aff02a5b40b8d169b54ad06ddea20aa31db1b8dee005a6a3b2da28c439c71e2b941c869152ea47982102e24c538411820dc688e9f5aafc56bff01a71eb7b298b0842817052ccf189f350bc26300797f630df114e590163f2e2cb0366c0ae7957a99449af72f422b2510e2bf66c1b10e98a327026390ef9031eaf5a186f88168ed8a89f0cbfb155bf706e05e968a9172ccc36e12c04792d64306c42292d005505e24f16ce8a06743b8794b50d5a2db25a018231c4991d46e4666157fae0157ba31c00ca4fb4436a2d573a6c8ebfd1e5e24fcbb526aa72b8c4352fae1d366d67898ed5803293ed6dde8b049552a7832c967d4469c0b9ad317e8f6115e5c30aabfcb42618b51e30efda007e84bc166960a4d3ff9322a931cc8e98c39d5dfb571a170034c60bc808190935737ad77b09a1b396b2ab5cc534ed801dc37ad7650561ccf422f54c612eca9c37bb22d7310d3b65e6aa4400cddccf27e8c124fbc81ee573028e7930294efda072475f78f96724e468861d1ee55abb870b8ebbba518559eefdac766fc148397326670a459da1849c5aa0a2d766ac9ae821b3581a1cade62f42b5d0c26d5466ac9bea64792950ac70371a469e70a2b2fb9e3462d1261dfcbc1e10e8834a967b274c62fd1edbbd160cb25bf7ea2e749b9ab5004b69a7dc54f9497e570e52af34b3c27ede61498bf425e0b0958025f75b70c0c3a9c150c64d48ef5169718269c7fbb568cde04a991802d2c17b99032629a76cf74eb80dfec904addec25d9ab9bd6cac612564c25729044994f20ac38b68c1bb256ad28f8806d14889f9dbe2ba109a96925a9692d8b3fd292438c7a169a881bec763acfb22f5f48199ba6aa3c10bb5c107be81d27c226d1a47dcef139151b7374c75eaa6d3ca9a5998245d7735ebed6ea7397edb770b91cd691cfa9e736eaa66a8ef98672788a13061883d4083c9ec9c07a4e993654dc83d45da074891f42b9b9e33f4b2f1d5521759f8cf41e40aec9405d55241e78cf172e79740f4d337a140531219144962f641d54f1d1bb3f59fd450bb5021714260c310722b9e393c5d9284f64e03d279577b35e908a479d283d59507a7b74109958b4619e6c58af1da8a41d1bc467f36e68e4b5f12878e6a1bb6a408825531a4e9593206aee0b278f553692179a59481d8948851896ca6455b9bb9de26d233f6f0818e082df089b4602279cdbbc37368446ffd353272ba65b633c08a693ea90c8bafbb81099d02fc5ba9b4d7036991aaa735bd5debf4a5aa7310a61640d0d6a31ea08cb6cfea175742131f76 else 0x80dffc0d0c25e5401a28274d233517df93df422876589ec007a8274c6121a9dd832c5af238e81e72cefe84bab15f328549756f138043a60b4534af2defa266bf92f2c515808f60004d2ba2f815f8cd5605038c538eeb6e629d3e379caf2d413a630c0be6e99848db95001b17f1c5db7fe285da37922d0bb6bec97bde32a7dcf2dcfff4237a77782d75ccb4c5409a375684dce93eee8f504f4b86c8f50bb92ee148a9e71d0f10f3b331d543b621d10c115069e4d064032196116124938a931ec6ec796db66b4c79fd0603718e0840a88b182344f0093285212824e19d34e0457be85fb6e5a9ccdc052f022163be88573deaee41960031be73fd709cbd59c04d7be82f2ac76375a48eea4bfd11449257d6917065827e1d6d3497c783b9e2ec62b9503b5a677f5c6f05bd9aae9ba5b0eeefe98b2b78fe31351586f74d04a0adfc4cf922c58cc4dbbbc16b8865a62cb72879c769e170dbdadd3c5d84172592f417b98bd34ae5a71d0f347dce2b36824ef055db6c6e06b3502489723f2bfa1536cc188155fe3e465af133e3a41bacb14ea54420ea132d34371c60f90b6f183cc1553430418b511532a7c1d332c349f310804b88502a54c7c801556124288ad23621c7c9c524ab9da686d05f72d0d6844200c0cf5888bc91455cf041b0d4450562c8a2b09a4be3ac45394bcdb5fbbe8d2f7db16a09d3097e84c9d68942a4800e8a34e7baa1063d1a46f7ac85164adc489b5638c80b1fe5e23a21063ca9d277d7ce76e250b4ab496f3973ca211d557a2dbc4d3ac25d73190f3346ad34bef5b1fee18cb65e21b5f79dd08de8414862a27c310ac46670263e065f2994700e41fb287b01f4d1db740ee77e3cc9d3366ce0ee1e7f1c706a440cedf146eb4a382d527628754c9032c14a8c39fae02bc64b8308e2028bc9c6cda714c10529cc2695175b5874be2d203a4c816f1db8e43bf8e3333fc94c1ade20dc29c12ed411e4d817ffe06931eca24b8cd614b43e5070b8d1f302c5bccf28754ffc25055cf7f1cdbe68c26cbbe3ac7e7008714705ad0ecda937a2a459864c19ff8fae1a0d0396fe0ceba1a945f884c9a062b06e4f798b73f98eb803ae5e66e59ab267266ec6bc3527ec0cfc86f46086336a072ca1ec641fbc8147fe39eae1c8a370680c688c7dbf74c8704734a714a8d4d0536add6dd30730df8ea905953681c406cd9268319314dcdd04284f49b621a68d80ed5839ca2886377b9a0b5d621c3d41eb0ba2cf88f14b80df257ba71d6f46cef20803d1e389a32c7fa1e423d8861d8be63cd8d836222d43a8f0839f145d972079c732d58ee9fc7d322d9932426817193fc735a89d68d130c051e1be833c366c32196d0fd40f5dc2807e0641c8551823fc738195e262c7283f1461ec7881509fe4d71930500b924b01dc9a8795563041781719a7148d87b24a0a55)) else (if i < 10 then 0x3b957745ab462dfaccccb785c35e2e84710309ad8e8b2a8fd08deb78f45b7de36e148dac4df2aa4464140495930f585a89e11c5e8b2cb783cdfd02328e9de665314dd1eb207898cb65eeb2d89baa20f729c5e0917d0b46683ad652096892563c42111486dde2f2d1a8891548bf6ca3396b8f238a1b03da783dd10b51c4ba628b81bc137b0cc3fe82df14eef315c579db7168d6f76dda73d34261765b50a12f0a9c36d1870ac1a0b035755b5e1d413a6177d1ea9ca94f51b1f346707be9a72fd0f03a441adb5b143ab05141c1b351a0a5a1f6e1d8b6a334b194bc835903f5c36b1877edc9a35265447cb5310f49d255741d6d0174e75a026dcf98df5ffc257e732635b8fe240c9d378340b41f8de0b253796834e851240927ef911415111b911506e49cfe8a71961a7759232af704b68931d23cc8aa77d33b0454a1dbb6a4300428ac3a9759b40c78891512f6cd0eabf06e03c5697e8465fbd831f9ff87bb6e442c35399b708433d8d7ddf5df7611cf6d432e53bb86b600d22137a12beb8253350a59efa158b1f2fd0e3782c2ec1aeb51151755b40d7d96469fc1b852a38bf0e3782d5b40c9d35cfe37d7b20177aa5ae47fd53d39f245059eeb5dd98bf8a719ec0c9a3ee717a772b61c4f14e214d8d39353b5accc85138b5b1a26310e3e54b9255cf3161589609ca85e017819551558cdb9609d0d686525802de418a2b0c7ca896a8321d01b50cb972bf72a2cd6e93ae5fb39674db57476b440b1e10ae795343e563d094a76a6b1f176a77c61c2dc2565042c56d107d2eeb2154f6b4f8cc58baa74ec9ffdf243f59d1a98b4cb058092e1d76f11776e5a9d6d013b0eb8aa887a2b1b8421b489c17b5af025da8d296a8335d8473c2d33a3d5f5c0bc8bb21e6675497ca4b765cf172820d5051e2ee12b73f5ef27573aecb8ec8b4cdf31744dcb76d543b62973890f17be633bff22274991eaf79d8637bd6a33516e9464c37964f4eb24e32c3c3d1c81e9d497deb519e8b79447afbcef358cde8f611f08ccf8519e4777f92ea9e4f799645afcdfce70f91dded0192cc471db94ccec54345a53e25a2bc34fbc06c1b72b3018ef02aac06536c151e333b3add1e5fa1d90147afc8e21bea18848432a192ddef592988e3b7b81d9c217fc9ba56ce3351598505e3cf7a882a91d04231d6985f12b445791fd03aad5cf23050114234b178285268d146908bf8d9b56ae799e0a77f561d5ac2a1a58bb2e334c551b5a32bf83c3c88acb921fe58b08f60ade9cc0be85dce93b81413a62f362ff8c6f776be6c3f7df1339fadb951fd75b6d45d8b4c01eac503f777a3de2468d052d0fb051458a1d4c6f5b74be61ccc1efaeef2b787f26122dcf89c0529ce9cda984d9dfd6a30ae5e7eb84eb4656b8070cba608858ce6492caa83e39f8b4bdd3887a78340a215cf3034163fc9173 else (if i < 11 then 0x564ed031faaf4f788bdda2e43a839d3bf40943ebaac514c759d1fd71f78513c74df1682b64e0a06dc183f4d333368759760761ee0f12722c481c826afad83f93fa34552605700275c6488712fbc1409abfb80a15832ae65bfae0396d6803b32f02aeb6049603b83d1761dcfdd0f64f0f43a9e3db550b99ae414c38cbcafc74c587d176a54135125803b25434a93b5a009318e5da999a9dede49d6994707721253efc1655414fab95780ba85f4b5c5fc9795ae16d4bdbde5919de62130bb77f34cbcad65de572b183ddc6e3c0e48f810e3958c265a3de46ce8acdb841de04ab58c06347a3ff594278129bf883ecbed6bcf61aca1d4786760ca1883213670cccaa1d6d3c2e85635f021c745f377de77122db8b46db841cdfc4de3d1bf26de15910d74e44fc256b3f32aecb883e9b70e3958c1ed1ac8668ef38981d913921825d3035e43b94432ee24b1ffd866108435f60646eee2bcebc5e5375b5898a48a5a2c8dde0b42138264dbe6c52249b52653cc8523ee1294284ac830b5e51ebb8931861b4c6cb1455cb11d18ec514c53af9ee484c2eaaae7b85e436526aa24349893d772e5bc0d2543a53b94e9a3cdde575c781db9a4b6b33147c437e41eaf6e68bd7ca9670f46a3d72456f888924bd51f0509eda905583687b624c21b27fcdd9cca394e9a9162f3d7645bf8942379cf9ee4cdd18a299345ebe08a65db3374922b7c74f2594ebc4bb65448b16e9bcede3d37f1343670bc8d488879bd1ebd2d669c4ba628684c1eb90e7ae2bce3b6cdd37988d2609bbc5e5e63a1aec0fa216adf25ac879991ebd77789345954b584d910770996f0bb45672116994a46c9c592b2842dfa35236fbc62297ed1ae41f422462fd6871dd76e48fb7561ad8a2958e7351bf89618a3b65af19e8acd8a23b95a2c840c26da483d6b180dfb4079314caa39e388411cb6fbc6baf0386ba416515e56b26e1af459222406b5af298b29040d5ede999476ccc9431b7a3396d3f8f1d81364958f2d151f122f8f5cb62d31bf89b4fe85a36b0cbf6ed3de62ee27293a872d25ce2116bcb685da28863867fcb6fbc6d6a2377b4f07aa3d862b78f411ca2907d1909ffbba64195457730594ed21e032a2424abc898c3066e96c51489e9a8589b9a4b42b58a5de5754b85ae2f46a3d7dff619997ba01e4d3f9bcc4b47f2cddd14431ff3241b84a9b1a44f096b180c4e52c9aa2641836423dd572592a89162edc38ebaf03a6c6884292e4e565bc1ec52ac6134dd59211f90ac52d635e2e9f906be04a24ca7b436141ad6b36b5e531652081abdbd3328ed99928636f4672da7f1e3b026c92b1e5a2a3e245ffa04d9084f5bace2314645d08de86cbdf58bb70e3a73998d8d4ddd127acdfc996f0baeef713522ddfcd21d77f7a7accc982a06842c0fe213268d4b3435ed3d1594a766dac6034ab196 else 0x1f75e844e99fb8310fa215af092631a207d65a79e2457983c05cb0fc48b288a2480d7491473cd81e57e020638bf40d2b835caa86966de891bb6e68cbf41cecf8e293d22cc30a3bad06a80ebff084a8201250c19c2b4903864d62863de3c53a059d904b6301b7eb92332836b3c11a52fd073b5ef60c7c05a18506a15d49e799f1cdbf3804399e08bc947b2efe43684de4e7865bab1d1ec9a1d417da8369d14215ec7c40b1e0bf0e4f0a079922be7c7172f4508a3b8340668cc896a86dcaaa6bdb3d7f40b1650438590f596f37f26e12b0379a4f28f411fc142dcacdf2a9e0f29ddcf5462e94598ef6f0688b8787d2152b37ec0a09b02422de4275f4509019e19f1c09a21e966cd2cec3ae40ee0f3c9a32d5063f80a4e77488a77bf4172821d460a496ecbb8053145953703d0dfa7f4a6542a75d97137a0a37ed1c9237d0fb0826ff755eb3053a6b0b3aa85bf7c8d7bc3a421a5c261a75a087045575b0fc0421376fdb551ef048255ee96c69ce1df85cdb25510a2b22a5ce0311b7070bc1a83502edfd0457092823e579c085d65f2f18a25ff8c99c76af74c6592ab571bc2f9760edbded432ec727bcbb52bd06a9255eed1d5643f92cab4ebaf9b6bad81872d2474178970764e4669154ea71407c95549811c8de396d682f44fbc34e6da93d01fb452d7dbeacfc28ea4d39d2787725bb2e8cb0bc1ca85a2b18d1a5c29607a4e7e81287cf9e00893045c01d9ae3ef4438e65d9e63a8b306e9457c280a1fb50cb8f1f922ecb886d05863fd0250f82fdd3759d0d4f72a1e644e2e9321f338de5d637968876a250f8fd87ae5cdda07516b0389c82f53a22f21c03916242ec079a582c9cdc19b2a85f83c3c9913c6626cccd9aab07845dd52d763cf7e39fad81eb12f2bcfba0d09407bd5e857dac6515030bfdc273cc11721d5fff5af061f4327d6c1eda0b4b45578761874e67ca40b262c13a9d7e39cd4a067ee54f8a5486c3de554229690aef2e55e174c17ea05f1383b82271e4b96bb2feaf4fb7f47b9703bc5cbce143a22d4aac351775427b278d6fed24a2143e8a48291fa4b2564ed031faaf4f788bdda2e43ae8530ed94a9609d4dfd0509862c007788010ae116b18c769a3164e8a7de3b7c86c68a9ce399e30ea2b5a6fe8feb983cd09539291cf0f1d2ed0ceb83b53abe60d8f6c603101146a168350a58288a1d0dd8b4e830ebd6a87fde171086614b41e31639c1cb4d033dbcacefd701353438e7ada4b5fb6ba24b25774fd0bb65ceaf5b1c6b3c6bad80190480f58902987a06685b1b35c01a414d033fa1d74322d3048063ca9e9f7bf9d960764ab0126a924eb901db5d249d3a61e21ce48a286033978c5d6c316f7f87e8a45482412572b8190da1d4b5bd8d3499763f66d86d72e92645891875d6c092c2c351775427b278d6fed24a2143e8a48291fa4b2)))) else (if i < 18 then (if i < 15 then (if i < 13 then 0xff4cc611e360e1a86f132a9f803ae60a74dc14430d3132f66e3a84f4b9bfd3dbae658fcbde106f36b3e842fbb07a3b501ab70deb0bd676792222801e245d977be66320b3b64371926945befde0f6db5b5a68c78eb0549aba8bcafd10e71d488a1d06774178b727182cce245e176fb93fc9437bde16dbb86f5be4bcc8e621a76c64140aff4f7a98d996f865ecdc762f6276140dec42d5b5c1c90e88541a95da5b4544cb370a05487906e2841781708a10460887146494148f10aad4468815baff6b007225d1da24fe4008bf8837b0ae004eb8c910e25f60294357d70142ce671ccb61f072f651eaa00a93023c4321a1e427ca941efe680a10425540a8a90f24e468ef0559729675c1b85533e11453887a1f8c64a473c6847f8f3ab10893915d66b9d15b1b6a200d3180d1ce1246399115b5bd9159536661c57d026c199cb202a7882e2cb0e02938b9526a6a9b9740b293988638963d29d9ea38755157b052fd0e2ed47b69283172a3db818f57869f6801cf55192ccc8c3aab516dc6c1a849904c873f1c08c80c73b5fa6c7afc8e562d4c0ff243fc2820fc7fa3050477c8bd1ea67aa8a83240b7c66a52e9e642fb407ec5e2b75241550ea132de27d4829b875bc0f783bfa18f54541a612f24969dc0bf83b8e3cf069906ad65388c8332b183d4a0ad16fe81eb6fe80e426c6f1b2b5996fdb74505b2196bb23d73a886e2871c93dd592183c641952180d547d9a171ebca6671ccb8a1071db14aa846df243fc95085dcc0b125055cf70117bbc60e1a0b4773cc164f89ccb04967be05cec27508023ce5e2732c194ac9bd13be1921be9adf52d4d06d9b7ae127a13250a92563324ecf0510dd08deb884cb06f8da517d296f3b3c144309be2132c1bf6dcc5d9acd5935398da35fd296f78a87298064a41406b4ccccf14bb8910bbb5150852e8cdbe0d428beffe20ed5aba64efdbe7195904e25f489bea9bcfff9ca2d308d8318bead94f13756ac9be4ca717ad8c59b0b487a4f9c0d24350436f850ff9edf9825ea17041adadcf209e4c8459cbb08e79d38adc161920bce5347aa684c7bb26d99c0a48bf30672c2158f14346ede842b686a01af10e597c132d1f610472b0e34ad18e3b02bc6c21b7c46f48780ca7487e588099b7f96f618ac2ca2886ee352f4cbce846f45e39dacc5502288574c0ec42b9e2f794990c90147f9831cf30bda2ce5322e0fd680ba7bc4c49dca8bb9621388e78adcb84ab5a3544d89996eb3435b67e4a288637bdc66f6a9bc83e9413c39897a22b21bb21fe23d5f2b8b8e6c072a39a7c648378e9310e8aaed23a8c74581e83f525fa5cf7c73dc596d5564f1a1392e78d6e3d597f25a2a965f4d2fd1e592d09de3b851c2888891a90c0079f155166142ad996e22a48d97a25e203c7998f4423e5f7aab04225573db33123240caa828c28817 else (if i < 14 then 0x670c7b64d0eac3f786a6ad579e2bdb79fa006488b618925aa2fdbbfadc1a0ca8c4360a8ed8016cc6c67322f5040ef7a8c61f3c4234683433c27992f5ded68cf9fa00c4dc432cfdfa949be98601a32e7ac2b1f82fa19cb20267ab71b06a8e81b2e887229a3c77d38a9e719190ea7a8189e718868833f1c0b785eb00690c07bd8c145b9718a4f4a2b2c065302fa0697a434bf45a2bf981cf241829a15e15386df7b6003bbfe1e3bd5685c6b719945fa0cc333a8b7ed71e4d6e91f1280fa1a40f433f47abbeb3d006cf041a4524152b4d9663176d3b32ac7aa9ef26f8dd07c0e0a11a253793097902515caa5e5fb892ccc9ad302122ae5892b268bec06e3bc88db781a1f1f2200de3b091f3a88649b545ed92183d94cc3d636fd9e173c0d07731cd8f4784b79012ac7ca8a41829a1461872b3d03bcfc36e8c2fb4bfbbe833a65406ca55881f504e9a66f425650576bf02254f097916ecc60f2411111e49f3d6255bfa790dea9e0f633c2e1e28f36913c577872c426ad5444a8d977782d26bef194bbedfc5346ca746cae5b7a1872a13d6a21620c5bd84635185d0953468510c9e1672f3dde18b671e0a77ae11ff9a1902ecc32319ee558b0cf65c5b96a83fd23a81cf10b59a9055832d7510b106e0a21b8e6530065c1bf6db6aa37fa0a76def9329656b10c26ce4c8e36e94ef2099ba6dbf433477cf1cc96bfc8332c0db5a60d10394d35d12a30d99ce3d6868cceea8de55386cfbf0fb9d3222058f7e30cea4f16c3779ef44e0fa42aa79f1170e8756f36a0c316c0db4e41680d3f7736411e4e6b1ebef19320bc9c8b7ac3b78538e65b169e1ac6ce74997e320254763c98ac0f798b7c7eef04a92c5c81c32e38b73770f275503080af72429687d40deca0e0a51ffb869336dccb6f3755d1ea0bc16e0226a0ab9e9ff867309d46f080ff919b3ff0b3d03bdb408163df8c9cec7924ce1f7aef4506a1c1aca21b0960fa9af24579e4d852d0f836d08e1b3305f84053bdc138ae94109232daaac649dd05e1b40a85519a2240eea22901a4add1fb3a32ae969153e64144b9a706f8c5af09285e24269049f18cb31d01784219bce2d9139f79e7d02ce5b18f875d118091c75e8c5100bc21c4c198e9f809b08118717379da0970dc65482ba2d910e620d5b849617eaaff459e75eb37a50f761d695aba66e0e039f44564b3e3b831b6a28dddc392aa03c3cff5077d506786f3e703c5ca8c9c7ba0c4b8b705e697798b581cb3da82ae98d18016fbb9dddebdfb9834a2dd9c857c3f1e45b30788ad684b867c05d045fae04071e80b477d524bffb927506e342922c7a86aa5b25953d9407303636dc5c09c33b5f58f406dddb9509728cd926b3a1da85858466c751164e87542740feef18de65e56a97dd00111d7fae002d148901fea0b3c4386712fb015285494799f78c3f5 else 0x118281b57230cd916b0380b9ed40611cf2937b0d224eb091b1a2a1a81c8b716fcb9be4981185c891568cf17a6b7d8b727c82d0590216cd1b2ee30bb7790b7fd4cb23ccad8f92f3e11bd5cc60320a5bce203d68a2ef3120917558b2c760606cefe5b88ac8f0e62424eb8e6c1815e97e5778265a4eac2d521bc991dfcb621fe1a1392dba506fdfabcd65f19353dd161ad5150127e0f277581a599486bf922bc460861797b789645e4f1e59867d313d17460659a0670c7901b4363e19da5b6ae0af3dca31f41dd3e2bb8b27130cccda1c9970ab040e19700117179c20957ce49466998fe245c47948d2ef2b1829e60f778c57bd81a56d5c6fa46e13cd351bcf52f5f11a0d322a1047905a19c0c93fa72a4141e94a2a042412025c811d7974ad8d3a7af632d84116f4e24fd0526e77158b0fb6ea35db03aa3ca52aace4fd6f128f3ef998346ce18f47916b03868a036618e759a03c2c7c33b4b6d5c15e7b9564f891785c7adbfc9f1d656fe8796ff7a1c716fd16e41260d31563fefd26e21620d3b684b54ea726bef1b23fee4421d19bc1eec2724514f5c0534a8f512fbc87922bcb36e7722b1f1e2eb5bebef73bb2c51b30c3cc05e8ab080b47f2785ebd276f66629387a19adab82b5afa0505417e81626fe3aee821386c596384b93ab2d1c94f8a08741f634c6bfd0f0b78732b6810938b3b26ffb570964a01d8f117802a0658939f6843763c909dc0de407d996338246888bd21108bc015163c0088b26a1edb1ba5196ad01270ee47c8f40a098b2700419f68085e022f8891543a504f987bfed50279150827edfa87720aac294a87d57e32ec7efda321801116a5700543d9648e389738a22486cb98a152b9ed991b18e21519f6d10827da2c79533314002aac638e738a564d0a9b0a28ced5db3b262b417dcbdf94125d211087032b14b7b7f1a61bca2e2178a29437803387765b1ea19ffda7eaa4533e15ac5037a071505d020b40c5c11cf5d041b551bfd053b6f7c994b2b5886136726471b74a77904cdd36dfa19a3be78e64b5c0cbaada75f7848a2948e6b50bcc81c3e6241686779e699954e1b33863c7e0000b0fdfb6c797b5a696c7e139c187a294ae683e34e1402c251667bbf63c9ff724bf633832600106ee1421452886ef05239660a00c124a404638556a2fdc5496d45376c8e94b0320df608a702af792249d7a1452886dcc2ae6480643c81508e0dc8d80f23a21c668311f24e42a9c7202d7fc2fff1855509e7fe19822c980cb30458f7bb0600cf7f7b1ac3f25f16f5290835081bed59f8d9f18dcb30a14573a2badec813a97956ccd42f047d7f89523622f282841fa75cf09e1eb8c8f5278c348eb8f41a4082da7219e8779bf9d10cb863f2b9e10404a6aaf4d999f0f0644ffd2fbce54f47a8cf25b6813d49d58ca75a32213a35fb09fdf331f79)) else (if i < 16 then 0x432dace2d6414ea39ebb50d6c62792c944e51084a848a295359f11cd6a047b0660a0e605f45555bd2dcc392d3ac15e259ec815a6ef68c6c1699f1776d5515065208afdc13867ab62841bf7a0e3bfa635f8be27c0e732783cb381fb6bcb425340bffc086ed15283c11f918cb81757de2393f60a4799fd1a247c2483701e67c8281769a21c0ab510a274418bde509221b42ea8670db861c2f24594435b87009cb48a712671ce2d1501f22105b30ab664668311d20bc5691b02bf7b0c0528d3e9a739817d0840cf7eefad80a84e1166483b10725caa9213be6faa2f36b44b84d2ed5b1e404e94defa1699c7b84eb98dc79b9f359f1983caeb698427e02ef8df541c0c9d34e9f3c18e6c4c280422969a6fada49d785c09075bfe303dd52612ceec58e3c8105badc11cf2c8bb03864c1449282f028a50875163c46685f1f2d8ee5aab435a00c895160fd32c17d1c6586c95864a5ef440526f1d2559e7333e130910d53140aa47186a1c26e7124379643b05e38852d56a7c0028b70192c19e4b02d3b67207f77560aa537d7da76b704f77d7be661d7e39ad4660f2a7304f868c23d84e5872554b488574da8c4208cf1e7c0ae57476d7611cf33d25aa0af4a6a8ab5a885df47aa64d4d6e0e3cfbbea212abc3e1c01e3328bf4198667516fdae3c9add23e2501f43481e867e8f577d67a00d9e08348a482a569b2cc62eda766558f553de4df1ba0f81c142344a6f2612f204a2b954bcbf71258a5444800e2f9db9f0a1b693e04f91006f1d848f9d44324daa2f6c90c1eca661eb1b7ecf0b9e0683b98e6c7a59f62e7839c88b53dbc4833e1f16e0b6e0bf75238b549864830a425eaac3677b410a8cc07e3de02259f828a0befc800bfddfbc6a381f82c42b9e0ae54cefe1f5ca81da2a732d7904d526b9ee6283385136b0af633ffdc4032595083b58b1eb9a68452471f9f38982816abff70173e3c27ddb8ff6cc63b567c9c08e9e7dd01263047c8a77021457f8e90d20568a80850aa25c42038a54e1bd7e6051d49eb5105105eac281dab2424b1bfb7939466706d1bc37b438d83348dff790f11e2215cf31bdc64ddb73c1147fe720778cca127264519ed2f308de0647491b543406b08e7050825fc979a6651314c32eacd0e63ee02937b0a0d4932a66522a7c2cab18205ca9885adec9699273e62b418bfdf5a17f3e13dd102712a28f9b9a1ca0643ec773dca710954e6b0a09d76d5c406064668b72f44cd01e2107d10143c5679f8d4251427b954f3006656a3b6038d94723d51b583cc29684c3951eaa95e569389542b955fee2920c50ed8740f69e60fd81b54ef14fc1168c17a730364de7cc0a39e0d2065b57269b398f2405a58476faa101bf733d4a40a4f240193dca497dfe128cbb8a24e4e84738b263431f70f2708cde36ccee2b965080572bef21c9f20a3043 else (if i < 17 then 0xc7e6b20ccbbd2ef81a1da837349a87b1098a61a7f6a1975ea18b1a582c2982afdc687b879ba6501d1b900088a95a0aa79aea976b30039daad0bb68a8c36e24579cfa41b02a53e02281af0cd41cb56a4ff993956ae7b6fa77ed66faac5b1bde8edc3172bada6a15561b067cdf2050cd5ab854ad0a7e3ebff15dc13fc97f709d8a812cc1050f63074203de27730f7ad55571725ae465e4eb755d0e7487ba6a093865070b836bdbc4903c99d8a243271466bd75a60bf708bad493db4679752f2fa1a58dcc8dc275c836ad5c3cc0e41560dc01d73c5590fa058875baae22c5a5338ceb89bbdd91bfe8d6c7aa7ef6c4d862c3501d6b16e132e720ab06972a067b3ff72e835db55612510cd8035759006a12480afa86e9db556c6e8f7abf5967ef6e18af580837076bc5a6976ac24a06b3810bb88c9681759043a8e50eef0500f06e6ca914b49bb64e41d84f7eeb4d3ab7938e034f7e390abb7bcdabf40b8bf694ac60f4cf3910d1e01e4f7ed287de5d508c48e4260f7de650af45cc01d728465c75bd544930510dd10c34e0d67e5f684b34ad1a67835dcd0588a476a018f472204e55bf3f21adf6cabb2eb7efb74597190cae581adbd3b50dc125ac6037d02fadea21334f5b1a2b06fde2f2d2c81ac4fc268952f767e4d8d8bb1048f7c0d2dfdad95368bf846f471854ff49ec20be2132686a4d67124d2d7a4ec372b290301be1141d84e496abfd1f217c78f8d03a4d417c85425a63fcb68a198d8aecb0384adcb41aad5db8051d6da1f019e4456479480f80b4fbd836d39400c7ff34b05939b8354550bf1e8793222dcc4e408a6cdc583d62c30e841a7967b8e4d2c168356a60edd8877f45f104e6064e9bc0e864496e9fff8080a84bca03f892508d297855149162d67c85f6b20e4366d4cf55152cfac2a1a85ba79b1607d4bc85f6b891685dcc08b46e3059882b0edf63d46ce47f42efe426486d2254f1b4ffe3342e642195a34cad85423d65b180c8a6e3c9fba80e1935cdffe1f148c4260a7350e5fb8805af3841d0493e851871def72b58d41783c1a1c76936ffd84e48c255d732d73180d91fde95ab604cec3149afbc6e39913242a7c6785d41406ff05c40fd24579cf6050fae0c25847d81c006ed8c06c05d6fde0c8c0f956e9e98850ff0b82c7ec3bd9ae50b0ea598144ae12c91a74c0b8de5b84366182ba552a47fdcfd312b574db70ed9a7bfb75aa0ea075d2196c1e4164aa01b0ea447e88bfea0ffcc3b2990af12660bd034fdca99c97df97762619328031f2a20c306529938f457de166818cd534f1994b84148b7e8691bfbbfad4feb7d0ce785b5a103f6bb8600ff6d45a62e50be5d960a74cb14deccf007885e28a50de00ce1dd96c7a867ff69faa914cf856b14cce9430c388a2ad1b8c78da45a239eb9108daa87aeb95ebaad94f7a18dad95cb16 else 0xfc0123112065c18210be48cc28011e6225598e1abe160cfa82b0daf44c00431ca3fe70f58e1f528331ce10c21f06e1b48f4a48011c2e04e13b3bca10c9495d766ecdc18210be48cc28011e622419871f626a78370da9c3132c955d88017067ab41dc3419621b0c28495fe08d83b55a9ff2680c5f93e578f8a1db205073e90b28ec6865ce9a7018a380499ca051cd80e567e3432e5f2bc5e4bf98c25da81d821092de4eed3cc2919d7e35d4432f7e3176d61a25e84bc16b864381e939b76c6450e092fbaaa70db706079437eb56a8a39c6dbce0f18bb6116cf6c6712a8c8fb3b2e0334f3161a2575fda197039a79834cc003ececb9bce5690bee91ea8688a33db6edb7ee321c1dc1894519ad5192a4400e3432ec258debc1b1110a6377a8bc3547f67cffcb29d24451b64f4f05a96ba16962d98684bee864fc4219e88a406002066c3448e3618bc3686c0080116ef9ff84a2fbe70f56ad8c879072e0487bae7dd0fbac5a187128578876e0415b0beea8a837912f307fb85a961b07d69ac29684d1c40caa683c0e5bdc253f1a46bbb0adbedae8c4e0f07e9243ee791ca5e881edd5143ba40cb4d8e38e735036d9703303dd52566de8c1c4436fb9bac21b6d4924b4987f35e858753fb1cc1ca050020ad88167397dd1fdbaa78ee1086158d026a0eb097e920bd10396f2eb5580a4344e38a7d18365bfbfb48125d42fba89e0058a248e97e023ce71a28055273271bc8e976a2d6007059530ae25e6c8e6c076a6cd4296c72f7d006492ea17dd44f0025043683d9ce0647cd273271bca0976a2d6007059530ae25e6cccd076a6cd4296c72f2d061ff82e100de1d386c4577a39a48a009f3ef06ca980bffd2aafe6bce8c36692c9c3ae9f0067be8591506f1ad3cea22d422f7a38a5c13b67db5526351639cfd9f357a4140187d36b078c5cab370c78f180d3de8ac1887b22a07e85de1d586cb0411c2ede8e5f721da7cc0b89ae8848ab6360278fc2abd35aafdfa87b7420f43a8cb3a27bc01b67bb3301f82974a0749a8795caff43491b0bf527a2ab1a221ee5839cda794b13d836e728c18b5a6fe702171ae09a718c3290c99c76adccc656fab571bc2f9760edbded432ec72cf4bb5479007c6e32bcb40f9d8dd4072a56b4ace3c2e34b05b70f24c8efe8064e9b8bcd384a87636873e7189c0a9ad00686785a573416f0f1be64b3db6af3f5a8aefaa2a076d2c57c7935b9e558515912eac900182fd2264531c915e21b886a9964a18328830c9457fe408b399052949903466ef9d8a960cf40ebb8dc6b122bc080a876e14a95a2fdc9886033d9401988bfeb943d4609d461e7fe1b3a8951600c8aab7a3fb24fb70ed95ebf55681ee76c6031b863d43c7e841822805949ef01aeb59e0958502d07a7141fdcc33e98866c81bb2621ed1fd401cc81b472594e203752653))) else (if i < 21 then (if i < 19 then 0xa09393ccb98116aaddaa859093c4aa012a84910240649a41e0fecd48497332eb0c5accb6aa164848a13264c584dc3275c4249d9975d2fa5859a9a46089eaa4c9791cf043303f406d84bd14ac026cc9ae2649eb31d7909710a10cc9984827a826a9fc115930b10bda3c09a021ea5f6393f1449d1da3501a31d7909727a03dee885fa02901b1278134173aa6607c6ab76aa2fc5f84325e14c4086317f4f40288f106225c0788566ad93e04093bbaed3484fc9a1c63c01c3e16402d2a4c70268ba149b4405bfa1f48a903203da686d212fa6a9ac3f1b32daa8bf212424ebbe971050174b88382142424ebae94045288d05a93832c67c809592e23c4218612c22fc07d26e439099a94fa0240392d50208f25e3d40793096ba01461f48af00252dbe7d4f92c61a5b04ffec11f75f812b192d3e80900fd22bc281046b02aa74aafc2b7e915e1605544b680540f06754c95b55f812d24327427d01201c9692b50208f1f083c9f3d1100a30c968094fa0240392d234160464ac1c90b50202726a0230a581192b3fc007f81e6121a7c7b32e7f80bc01750c0cd3c8c500a0cc9680903e9e54b83903e65fa560420104b5dbca0ce35f42936800a5d702688718c3927acaa7da3c09a2cc809e915e184833257a9fa557e2cce2893a000b09067cd3041692bf48af1cb7840f30c2f24936a14a7918a0041cffb0f38a3c09a00480725aa040292b00ad7404be700a4b419fc9f27121fc118c54b7f0aba838dc09a26fe8073d0a4da853dd7fd8010f392d2df24936b840d14cb7ce96f4849804fa0240392d2564682c01402be700aa552d8390037b5aea0230a58008334fa4a5048090860fc2c823c7a80f226a824048430e21b402fc2aea0610c6d66780210b861de00ba860b2064aff8d8f608dade4b33f84fa4a5048090861c45f823032064afa014b02aa4a9eaf18c300a4ac04b64f8fa03c00e41c809bd7a9d5a92b4ab743201e0ff00965c09dd7c0958bce0cc94a090129543885900bcab4814002809bd24a41cc93483cad52aaf726adec3c81907e1b400861186587d13002fc19b813ba4120242183f0b208c028c325682444b812d098048430eed67897042006192b41202421ea77620640c8e53fbc0f5487d00a0cc95a0901295753bb10727f4008390ee49613fcb7e089fcd54bc6d93e3d130010cb0de50661f4218610664d5048090860fc3b8050661dc5a8017025a13125808672c94961bca2fc21833bc01340c1452b80900a9542c81946a39c0c887c960e46483ff855d4002d372586deea0650415817e0664849802520e4fec93fd0396ae9fc02a7d26a8240484307e2fc028010c20cc738012c210c0c821bce065c09dd35512a424afbb1c922841087103230c0caffd96085da82312bcac19a827c005b12c23d07208ce4a55293ca7e04ac4a1792e0c79d4f3 else (if i < 20 then 0xa05178ed216ed484a3d30282d41c49c691b85105a941b11e624ec47bb50474993ae352195d93a28034e5f8a80380050b689cbaaf1092d76e049801178d3041a24449f2352007959c75087644254a909b86865a70ff4edd7fe30af022d20a0b10223c11d15703bdc4498748282c47b81e25c08803a2415fa88f24e4251d9d120a47c1b92709222cf9a4100a82f9888b13ac45421d9513c5401c397bb2740495e212445d11046425839d123e4c49dd264eb88488fa958108006e47420ab90528fd13a3909e0c400db306e63c76da00c2861028ff1857895fd08f572004e890523e0dc938492eaacf95801c615e0d4a4144e104b8d1344e23d1c8933e622c1b841476104478b900a58d87a0b5c9f23e68549889d0b689d87a2700a31505dd0c807802b79d1e81910e325768b103230caf871252164cfe00a8716b354c874d0041d721322711ccfe2d4b0d93e28c980cd2a83dd56734ba861b8126001cbb50aa076e1b90eca7832aa447d5648ef0610203c6b070e3892b44e19f0eedc093002fd7f8b1e8436cbc60e489a2f0825d489b81ca2bb6f381909e0640e8876c61ecba94f1e6a20862edd5aa20a039a1866362d5630dc114842711c5f8e79e00ab019fc115e1410661ec9e8e70878f811e413d5ca3ff822809e8bf2be44c198712beec52a83356a0cc27a5529ff045028821844c198331fe10c3e87b5680e596117e2e42791347e53c309610b253ee1b90e42711c19983066c1ce688929e58401b5b0066b403f7725a00ef88e118696fbbf77bda06531ea5006d56ec98e04a309683329a864e8e95e04f05cf810e1160fb44b7e80f04a14b2808a5524fb549a196520484a40f2a14ac12460e40ff771c210c1c9b4fa7810e10c31ffd2bc09e0a6fb14023ffe04b4821973e955f8927acf62804b994d08707304150c2a9b2e6dc421f48af0537bbac12460e40ff7706771a170335824b7e04ac00729a60d2bd3d06c865a9e80ff0729e514960fb48065cec5a576925bbe37802d0bbe04ac524fb5f27c8ab957067f025a462e00d34c105a34e96d0114a032fa419be73160cef697300ad3d7095d00abaf2449a8a08b40e216977968e30726d7a2603a5604202f4a022b03ba149b40a4ae983bcae04b42621610c218090eec340297308642c21b812d09892c0050ee0157594d9262659411681ca40e172d16bf0b201692e929d21260071819e8526d357086025f485f404560b005a69820b4c35011852dc20798820ac14d7d3a424c03b30025cf96d266438aebb3032c344282740200f4cde709210c0bfb1006127b47813400332e6045aab76aa1b484803eee6045aab76aa16413861bdec35dbcf00421716104ec2c409253261648480332e6045aab76aa2fc5fde00ba865d2494b88f161612480ae91e2124ebb7b94376daaa59752a40f28cbd2706590114 else 0x955832de8980073457e04ac17108249411e3e1a15c3481242442d80700a4cc0487f42e3b49dd4f9a0083aebe36802ea18a5e24ad023c509cb0661851f893108031e3aa00cc1996327a277e08a0c754076b5f7f6615b8bebc515e12b8051222e40380530e0243f84100a24402abb013c1b86d5e958311c27faf2e1d25c0844cb1648271dc1abcb76cd4b7b6058e37621c52ec49b05f4205d4ad40797041114d0042175ebe23124af85b861fe038ae52a630574827326ccfa08af0c990904eba587da20a016390bd44c424caba1e7cfc2dad024269027ea1c24a0e8bd0aaf20564c68570d09c3483d42b8681712934b6fd849a5b42b86813115aa10f63a08af0b1ae921249ca991f90bd412462d2d5e3c4aa031a46e14211a5264eb9421d942893a14416a42ee1fa04a564fdfaa1650d195ff94dd0a416b3123ea0b156b465769139c3483c96458acb23e49c65c28fd044cab87b24efd6008cb20b0a3f435944052b56e4f116194afc948e787fc48fa912676cc6c57de768e1a4d5cb387892a15c09a256b3b458949e822827691339255c3d9277eb004659052eabb513d1360f4ccd4a27a234650214c851274227e70697ff139963d5a31e124bd11f35c9f242e6ad20a0bd21c088016a8bd041582664543df310b65c44a91b22a44d441c109543b7e58782b64613fa08b2b067d4510704a108d2f9a2bfa02fae82283067d4f0aee69981d05688699fd010c6cf945dc8b121745c99a2f05724d20f6fdc69c08f044ddce51702d5c589c99267c510500a49135105014ffa02fa29216d87d174ebab50a94f646ecc150070b5e090afd017d3a52bb3b5441c17081e0292a10f61d9a3f03a4cc44bb90b6075d995d9db3b49a82b29e17fe86403c2598f67f80bc69ff6f6c5d21470e6082a2e932646ca9e99a9eecc21de50a64a431bb37b6092eb5ce01c02a9b0121fc56e28e04783a2164ab90522a4c4d582b43a905419a9c19f515ba1d6c9f1a4458854efdc3501554aa8c112a45760df5ca2c4741ec1f103446a7067d417e2fe499f015e0cfa88f4d58ed926507afcefd356124a48cbbeb4c5d48b5503e40562f3d19c51c08f0904d5859567e20798faefa86d6a25b7758f3753b040994923f4c4829c950a23c24bb7927fa99652424859befa94d4e0cfa93b51c88407241bced2938338415142d113566a5f5b0747a2fc8a8172af8494dfd04547688f9dab97a08a07d67271a608342b317e90775f2b3537d5c81c2a23d02529f5c93732c9d5c81e5519dfa8e6c9db323d0153bae8bcf4f05941ae4d01020acd590917e2ffa08a01022767684945fbd4554ad28423419ab4c45ab3be6ee7a04ac6f7ea127c381be6e10ecba04d0ac9bb903a527a08b561cc1054426ecd811581c8fcae9497663140e89574222fc2b6744ebad1395d29ed766132217d82ad277b82)) else (if i < 22 then 0x8333064bde0136387067387acc9282419c7d27a825c3a0152052021da009a06066c08b30561b5b098005e13d008e16931f7d78198fa60c5ab0fb401685cd5d858f9be642dad90160456073022cc043f024c037bee1a4092502518a4090891a902a460d3b8b5576a0ca7d4f9a00a886f2633517a3d50277440489edc339494b3d5a1633867c236a40f2866caeb0a5d4f22653e575953c809235a6c6c36b882d4d37e8086653002967a87097d0c80784b3b7b675093e028a7f3fc0738b181d71e2ba4a9e28ad028402f18f00702c74553f8056ae4a4018b530238e248035d66b40683916b7f471f29816c3517a5d16244ca59d1596ffe837daed16f430938b3401075c4ec89deb1438a2b4768b7a02087b5ce075b1aa4cd211359c91551041581870c3fc10d6be5b42c815a6210ecb96d0da05698b5f403e3dd79cd7b0da0b210dafa850b2face68130864bc29f110c6d7fc0130864bc298810c62fc86819e8550014c548630da04c2192f0a7c44318bff93411d404b48a18548c96c9f004c0cec14023040a8430864bc298810c62fe38e0caa9b04c6106dbb78739a9d0aa02cbb4da63704368134aa4bc298810c62ffa56a00d7efea813bc16b4c42ca571da066d799f15232436e3e10504aa4bc298810c61648f401bf50996453b7b619f1825b6d7d31026e20a04e19f1c41c11c939a23e38ba9a636bcb08596bf832aa558842fd0afd01b63d86d12f08764c318430a62a6c9f42a80396d7d428bf7d67340984325e14c4086317ec344c1c11732e1d2457575de0c20402314ba38c32aeda660369c69038065e813427d3ab588871bd607e058b5bfa38f94c0b61a8bd2ed06fb422d4410cdfa7cc20a7f2eb1ad3caeb11253c8d05a837da927fa7f61c419abbfc0250f82aa813bc1f3f2c2c94f1e7d82ad0c3740689e4b5129fda3535e20689daf60ab511d09a2fc7a80f2e082225765b7e58c3bffd82ad0bfa34296bfaa17b070da778740b529e0cf054d1dd1120e48e81d0da53cfeabb2c253c2a859ee1a4092b260ced994fd21117506e52f65ae59c3483da0d0aa57a4e085928332c64f52b823bde8c44efc096954f00a29c2d80700a4cc0487f42f3862658561b5e3d0994b12213701da186d006143493785de2042861863122346aa1961daaec9dc7b0464c410b07297a6447b25c515e02d8070464cc0487f42faa54bc06a95e21549cb25c495a18493118623ef7d193023bbc3a019817c7c343546103c8e38315aa0057682100a29c2d80700a4cc0487f42fc4b821002442d8070464cc0487f082e04488b900ee04c38090febb4028910b601c029330121fd0b80514e2e5b880130e1e4e384100a2442d80700a4cc0487f083c4b8210024411abb013c1b86d5e9be311d1d8a7172dc4009870f271c2080512216c038052660243faed95da4dad07f7e4f else (if i < 23 then 0x585be912349406c0b00e60c70b0b2e6247810e140baaac2cd4def0c2385dbf8f122536aa80730638585957123c08708a6803616426f78611c2ede25891eef90e5b83ae35049c3447328764f784806ab3520523c40f3006fc0e180646a108d10c9d089e8349b5764c52f523409e1c416a2bbf404334457922ff0554191895a4ce1706150768030a1b4470f92843d85d625678020eb9d9895646c3d94f4115e7d841b8a9b1a267f021d74817a2e0cf1f0d005611f447083c804bc026cd578f8683812d09a249c9bf623cb88654b6e26f00561b163f812d2bf60aef005a0f35b39a3b6f00561b16d6b77fcba31f3df9bf750bed0ed0d366468ea9dd60a6a149b48c6e6f4c5401c39786544faa3081e4dc407ded792a10ec9add5583d7c4e3d42fb43b6f6fc096928124e9847dfbc7c3432684111763c93a5b11623cf9a2705689f26da00ba8676aaccb19cdbf750be0300df9a85f005c415ab913a855c0d1504eae0449869dee0dc27d5ce1b484c0530d0057d787c1871da52c478275cb550cb782aa0307e87403c02b57213cb188fc028ffe861c02b572854b189df055411fd42f80c029d6a17c0171056ae44ea15002005b8b5bc9155187eab14e7f80c031ecff005c415eded8ba42882716a60471c49006bacd680d64a05460a8124e982486551049c309d21a27518b110cb12ccb84dc0a5d579e9f5e3c513688488f29674565bff8163b6f00714195c4140734479c902627518b110cb12ccb90d11e52ce8acb7fe09c84acb3f6745fa90911ea0493a64395508514aa26ec9d01971500700272741390920a7444781313a8c58886589665f0e735118c4b622274cb86532ee40f2832997462276f007147260593b3a247d9ad5275c4c42488f64bcbd18c4b32e196fb89de0dc20b53867c27614f98df7a266a447c0b81625c7494b596ffc65837212745659cdaa6a1447813bee8c498b07b864eb88493b32e275868983822e65c3a48aeaeb32e31dae8e31237fd1381f00b7fd848a72160154099795fd5fd76e96d1eae52a7387fa5d2244c982704e08cb1851a2bfed7482b32fc63c01c28a8236120547c8814b754d138056f0f881e8f6e6481b50214c7405c97ae8355a7205f93081473c3cd85a1338a18f1256812a33541d18e61a642cfc9a057cfea3a80d5aa20867c9f2f85d00b49fdc09a2c92e1e70f5830fd884308675c1ca350fa064c58e508657fe80db3d8a2927ae2489fd01084c4bdc381907259207f87b296ada8f569bd8b156aa20a02260650b8b1d523fc3e8195105011305401c019fc11595ac3176833c9282419b878fab0638dffca7d0aad7a014cb5e184e5b8124e9819c7d56a955aca7fe706ad9daf0f6b9c3e8418e275c1ca350fa064c58e507275c1ca350fa064c58e5e70693b9593d5a0736bdbd9ddf822bc2be0a803813d1ce10c61 else 0x1f480730638)))))
def rankMode12 (i mode : Nat) : Nat × Nat := let v := packedAt rankHeader12 ((2*i+mode)*24) 24; (v &&& 63,v >>> 6)
def rankHeader13 (i : Nat) : Nat := 0x8a31284ca181f507c6e178555729a36f713691e500000626e55e695575eb545934cfeb49bd14262b000003e15b3c28c3642332a122eb582b2d423d2b1f5d71802b156d00ffa0000000a163070d00002b
def rankPayload13 (i : Nat) : Nat := (if i < 1 then 0x1f221aad985543a9d55fb291e60dc74d992a7a0d31ef5100f15a0340182f660922d30a3b0ac7ca98c36ceb5ca11fca81708c61e88b53db04813819fb7e4ca45487932621c0185105e54c5192518e714428ad08ad35d48272aac648d86d09298c0c83154989dc4b985d3203d0087d07b00c06a7931755df98e5660a0671e11519600d4b81f0066b41babf7fa995faa29e065048ab49d6a034c5fd062b6a3f6add430e552fa0c2fa630fa4140f8cb9963fc6294b7e613cd3ce9bb429607e5b4e3603926a345e486981e0f548991a9120c150bc0f15cb527a34f52e08466dcb6e248d5580110e86b476f142054eef7508c60ebcc24605d4a4e3a5a821503d943b26f24e4c298bf000573bfd03e0e4c99530f38ec2284710a46c50fad30a05c0091d6e2b544392506224c7c939baeb840fa6532271df783914ed3e74bfd5362b58d9dd31209c6885f1cfbdc459352823fcd3a7903f81462cffeb91a39476004a5acb51600d1083d0f674465fafa160fc0e941f1b43d5f92774a39cd3a953e6b840fa6564e8ac8d0584585f69f761873fd30e10560ac387a0348aea22d48e71884f70245465eb0219bdc943b218a8ed0e81fd245014b596a2c01a2107a1ece88cbf5f42c1f81d283e3687abf24ee94739a752a7cd7081f4cac9d1591a0b08b0bed3eec30e7fa61c20ac15870f4069150dabc48d8ff0a275c178f369a7147cb63202b9c56855442066eb8cdb96684438953fbbdc9af9324b01dc0c81d260a05c71fdb1b7b182d24b24135f1e7753b94b5fe4960bd10f903a05410a351e23349281974aad0291556224509010f65b43bfb9f445a89a9d703381751f2b504281c8e5650ecbca846300ef49c17e05e826a2146682f15a75ce28f927225c728a1032dad021f1d8390ee32418aa4c0039c78d241ea974f200c1c94169e39571b287b0314d3fa22b203a07c2f94b596a2c01a2107a1ece88cbf5f42c1f81d283e3687abf24ee94739a752a7cd7081f4cac9d1591a0b08b0bed3eec30e7fa61c20ac15870f406915aaf817491404a11a2e3997aca21a4ea2907a13c5c80d0da0fca09154829a2ca4771fc0e94b596a2c01a2107a1ece88cbf5f42c1f81d283e3687abf24ee94739a752a7cd7081f4cac9d1591a0b08b0bed3eec30e7fa61c20ac15870f40691509e8ec65ae3c0bbdc0f9287649940ec7f1167ed4abff35a3141eb6832cca41f81d1cb02d4b9fb0f703c7391f34ea545c9054f222c3b9d103e4d55a00825048f41a88c70520c696d0f0a21a474955c632134860a85e08fbff5fe24c56953637eb59984502e46c4280f57e09c2498512be88b51d7032305f29a7072395943b2f2a118c321bdb04a009932a61e44a84507a2148d8a1f5a6141f801282dc56a88724a0c4739a727375ee0c016a2644e3bef07217eedce9246a6c56b1b3ba62410819 else 0x5e50428be54c662fc4eb07be541f84630f445a9ed82407c0c839b2e2a4ba31e499310e00c2882f07e54c519c510a2b422b4d63609caa92323629d3181f0320c44b985d3203f59586b6ed84f4c64550ee9228006cebf1e00db03f447246c18b5135a71cc2471123a13c8a897)
def rankMode13 (i mode : Nat) : Nat × Nat := let v := packedAt rankHeader13 ((2*i+mode)*20) 20; (v &&& 63,v >>> 6)
def rankHeader14 (i : Nat) : Nat := 0
def rankPayload14 (i : Nat) : Nat := 0
def rankMode14 (i mode : Nat) : Nat × Nat := let v := packedAt rankHeader14 ((2*i+mode)*2) 2; (v &&& 1,v >>> 1)
def rankModeData : Nat → Nat → Nat → Nat × Nat
  | 9 => rankMode9
  | 10 => rankMode10
  | 11 => rankMode11
  | 12 => rankMode12
  | 13 => rankMode13
  | 14 => rankMode14
  | _ => fun _ _ => (0,0)
def rankWords : Nat → Nat → Nat
  | 9 => rankPayload9
  | 10 => rankPayload10
  | 11 => rankPayload11
  | 12 => rankPayload12
  | 13 => rankPayload13
  | 14 => rankPayload14
  | _ => fun _ => 0
def rankCount : Nat → Nat
  | 9 => 2
  | 10 => 138
  | 11 => 970
  | 12 => 793
  | 13 => 16
  | 14 => 0
  | _ => 0

def testPacked : FrontierTest := fun T mono ws r k i =>
  let chunk := rankModeData k i (if mono then 0 else 1)
  FrontRanks.rankHuffCheck T mono ws r (fun kind => if kind == 4 then (10, fun j => packedAt rankDictionary (36*j) 36) else let f := rankFormat kind; (f.1, fun j => packedAt f.2 (17*j) 17))
    (packedAt (rankWords k)) chunk.1 chunk.2

theorem testPackedOK : frontierTestOK testPacked := by
  intro T mono ws r k i F agree mon group checked
  exact FrontRanks.rankHuffCheck_sound F agree mon group checked

abbrev auditBlock := hybridBlock testPacked rankCount signedCertificate

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem joinBlock (k start a b : Nat)
    (left : auditBlock k start a = true) (right : auditBlock k (start+a) b = true) :
    auditBlock k start (a+b) = true :=
  @hybridBlock_merge testPacked rankCount signedCertificate k start a b left right

-- Balance the certified row intervals so each leaf replays a similar amount of work.
theorem splitAudit (k start n : Nat)
    (left : auditBlock k start (n / 2) = true)
    (right : auditBlock k (start + n / 2) (n - n / 2) = true) :
    auditBlock k start n = true := by
  have recover : n / 2 + (n - n / 2) = n := by omega
  simpa only [recover] using joinBlock k start (n / 2) (n - n / 2) left right

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem level9 : auditBlock 9 0 3 = true := by
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem level10 : auditBlock 10 0 200 = true := by
  iterate 3 (all_goals apply splitAudit)
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem level11 : auditBlock 11 0 1125 = true := by
  iterate 5 (all_goals apply splitAudit)
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem level12 : auditBlock 12 0 944 = true := by
  iterate 5 (all_goals apply splitAudit)
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem level13 : auditBlock 13 0 64 = true := by
  iterate 1 (all_goals apply splitAudit)
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem level14 : auditBlock 14 0 2 = true := by
  all_goals decide +kernel

theorem tables : hybridTables testPacked rankCount signedCertificate 14 := by
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
  · rfl
  · exact level9
  · exact level10
  · exact level11
  · exact level12
  · exact level13
  · exact level14

theorem geometry : graphValid signedBase (boundsBefore known251) = true := by decide +kernel
theorem pairChecks : orientedPairsOK signedCertificate = true := by decide +kernel

theorem checkedRoots :
    Limited graph 14 1 (inputs ++ [bin true (inputs.getD 0 zero) (inputs.getD 6 zero)]).toFinset ∧
      Limited graph 14 1 inputs.toFinset := by
  let g := signedCertificate
  have checked := hybridForest_all testPacked testPackedOK rankCount g 14 (boundsBefore known251) (before_sound known251 valid251) geometry pairChecks tables
  have tgt : targetOf g.base = graph := by decide +kernel
  constructor
  · have h := checked 14 (by decide) 1 (by decide)
    have budget : g.budget 14 1 = 1 := by decide +kernel
    have eq : sameWords (stateSet g.base 14 1)
        (inputs ++ [bin true (inputs.getD 0 zero) (inputs.getD 6 zero)]) = true := by decide +kernel
    rwa [tgt,budget,sameWords_sound eq] at h
  · have h := checked 14 (by decide) 0 (by decide)
    have budget : g.budget 14 0 = 1 := by decide +kernel
    have eq : sameWords (stateSet g.base 14 0) inputs = true := by decide +kernel
    rwa [tgt,budget,sameWords_sound eq] at h

end O1677

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev targetFn := edge

def firstOr : Sig := bin true (inputs.getD 0 zero) (inputs.getD 6 zero)
def augmentedInputs : List Sig := inputs ++ [firstOr]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem rowSemantics :
    ∀ r : Row, augmentedInputs.map (bit r) =
      List.ofFn (sample r) ++ [sample r 0 || sample r 6] ∧
      bit r graph = targetFn (sample r) := by decide +kernel

def essentialRow (i : Fin 9) : Row :=
  Fin.ofNat 512 (([96, 1, 2, 4, 1, 1, 257, 4, 8] : List Nat).getD i.val 0)

def toggleEssentialRow (i : Fin 9) : Row :=
  Fin.ofNat 512 ((essentialRow i).val ||| (1 <<< i.val))

set_option maxHeartbeats 0 in
theorem essentialRaw :
    ∀ i : Fin 9, (bit (essentialRow i) graph != bit (toggleEssentialRow i) graph) &&
      (augmentedInputs.all fun w => w == inputs.getD i.val zero ||
        bit (essentialRow i) w == bit (toggleEssentialRow i) w) = true := by decide +kernel

theorem noTail (C : Circuit) (fan : FanInTwo C) (small : C.size ≤ 14)
    (correct : ∀ x : Fin 9 → Bool,
      C.eval (List.ofFn x ++ [x 0 || x 6]) = targetFn x) : False := by
  have outputTable : (execute C.gates augmentedInputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    let r : Row := ⟨i,hi⟩
    change bit r _ = bit r graph
    rw [← b_read, execute_bits _ _ _ (fun g hg => (fan g hg).1),
      (rowSemantics r).1, (rowSemantics r).2]
    exact correct (sample r)
  have supported := get_rep (execute C.gates augmentedInputs) C.output
  rw [outputTable] at supported
  obtain ⟨k,t,S,le,run,sub⟩ := extract C.gates augmentedInputs fan graph_proper
    (supported.resolve_right (fun h => h graph_proper))
  have bound : k ≤ 14 := le.trans small
  have allRaw : inputs.toFinset ⊆ S := by
    intro w hw
    rw [List.mem_toFinset, ← input_list, List.mem_ofFn] at hw
    obtain ⟨i, rfl⟩ := hw
    have h := essentialRaw i
    simp only [Bool.and_eq_true, bne_iff_ne, List.all_eq_true, Bool.or_eq_true,
      beq_iff_eq, decide_eq_true_eq] at h
    exact raw_required run _ _ sub _ _ h.1 (fun v hv ne => (h.2 v hv).resolve_left ne)
  by_cases h : firstOr ∈ S
  · have eq : S = augmentedInputs.toFinset := by
      apply Finset.Subset.antisymm (fun w hw => List.mem_toFinset.mpr (sub w hw))
      intro w hw
      rcases List.mem_append.mp (List.mem_toFinset.mp hw) with hr | he
      · exact allRaw (List.mem_toFinset.mpr hr)
      · exact List.mem_singleton.mp he ▸ h
    exact O1677.checkedRoots.1 k t bound (RootFloor.signedAtMostOneSeeded bound (eq ▸ run)) (eq ▸ run)
  · have eq : S = inputs.toFinset := by
      apply Finset.Subset.antisymm _ allRaw
      intro w hw
      rcases List.mem_append.mp (sub w hw) with hr | he
      · exact List.mem_toFinset.mpr hr
      · exact (h (List.mem_singleton.mp he ▸ hw)).elim
    exact O1677.checkedRoots.2 k t bound (RootFloor.signedAtMostOneBare bound (eq ▸ run)) (eq ▸ run)

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w
theorem run_len (gs : List Gate) (w : List Bool) : (run gs w).length = w.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton l a ih =>
    simp only [run, List.foldl_append, List.foldl_cons, List.foldl_nil, List.length_append,
      List.length_singleton] at ih ⊢
    omega
theorem run_old (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    refine (ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (by simp; omega)).trans ?_
    exact List.getD_append _ _ _ _ hi
def bw (y : Fin 9 → Bool) : List Bool := List.ofFn y ++ [y 0 || y 6]
-- Apply the augmented-input bound at the cut.
theorem base (gs : List Gate) (o : Nat) (legal : FanInTwo ⟨gs, o⟩)
    (small : gs.length ≤ 14)
    (correct : ∀ y, (run gs (bw y)).getD o false = edge y) : False :=
  noTail ⟨gs, o⟩ legal small correct

def step (w : List Bool) (g : Gate) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)
theorem run_cons (g : Gate) (gs : List Gate) (w : List Bool) : run (g :: gs) w = run gs (w ++ [step w g]) := rfl
theorem run_app (as bs : List Gate) (w : List Bool) : run (as ++ bs) w = run bs (run as w) := by
  simp [run]
theorem step_congr (w w' : List Bool) (g : Gate) (f : ℕ → ℕ)
    (h : ∀ i ∈ g.inputs, w'.getD (f i) false = w.getD i false) :
    step w' ⟨g.op, g.inputs.map f⟩ = step w g := by
  unfold step
  rw [List.map_map]
  congr 1
  exact List.map_congr_left h
theorem run_set (as : List Gate) (w : List Bool) (j : ℕ) (v : Bool) (hj : j < w.length)
    (hA : ∀ g ∈ as, j ∉ g.inputs) : run as (w.set j v) = (run as w).set j v := by
  induction as generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, run_cons, ← ih _ (by simp; omega) fun g' hg' => hA g' (List.mem_cons_of_mem _ hg'),
      List.set_append_left _ _ hj]
    have e : step (w.set j v) g = step w g := by
      have := step_congr w (w.set j v) g id fun i hi => by
        have : j ≠ i := fun e => hA g (by simp) (e ▸ hi)
        simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne this]
      simpa using this
    rw [e]
def re (j n i : ℕ) : ℕ := if i = j then n else if i < n then i else i + 1
theorem run_re (j n : ℕ) (hj : j < n) (bs : List Gate) (s t : List Bool) (hs : n ≤ s.length)
    (hl : t.length = s.length + 1) (h : ∀ i, t.getD (re j n i) false = s.getD i false) (i : ℕ) :
    (run (bs.map fun g => ⟨g.op, g.inputs.map (re j n)⟩) t).getD (re j n i) false
      = (run bs s).getD i false := by
  induction bs generalizing s t with
  | nil => exact h i
  | cons g gs ih =>
    rw [List.map_cons, run_cons, run_cons, step_congr s t g (re j n) fun i _ => h i]
    refine ih _ _ (by simp; omega) (by simp [hl]) fun i => ?_
    rcases Nat.lt_trichotomy i s.length with hi | hi | hi
    · rw [List.getD_append _ _ _ _ hi, ← h i]
      refine List.getD_append _ _ _ _ ?_
      unfold re
      split_ifs <;> omega
    · have e : re j n i = t.length := by
        unfold re
        split_ifs <;> omega
      rw [e, hi]
      simp [List.getD_eq_getElem?_getD]
    · have e : re j n i = i + 1 := by
        unfold re
        split_ifs <;> omega
      rw [e, List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
theorem key (j n : ℕ) (hj : j < n) (w : List Bool) (v : Bool) (hl : w.length = n) (i : ℕ) :
    (w ++ [v]).getD (re j n i) false = (w.set j v).getD i false := by
  subst hl
  unfold re
  split_ifs with h1 h2
  · subst h1
    simp [List.getD_eq_getElem?_getD, hj]
  · rw [List.getD_append _ _ _ _ h2]
    have : j ≠ i := fun e => h1 e.symm
    simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne this]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
theorem rd (y : Fin 9 → Bool) (j : Fin 9) : (bw y).getD (j : ℕ) false = y j := by
  fin_cases j <;> rfl
theorem ins (j : Fin 9) (C : Circuit) (n : ℕ) (g : Gate) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (small : C.size ≤ 13) (hn : 10 ≤ n) (hn' : n ≤ 10 + C.size)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hA : ∀ a ∈ C.gates.take (n - 10), (j : ℕ) ∉ a.inputs)
    (h : ∀ y, C.eval ((bw y).set j (g.op.eval (g.inputs.map fun i =>
      if i < n then (C.wires (bw y)).getD i false else false))) = edge y) : False := by
  obtain ⟨gs, o⟩ := C
  change gs.length ≤ 13 at small
  change n ≤ 10 + gs.length at hn'
  simp only at hA
  have hj : (j : ℕ) < n := by omega
  have lA : (gs.take (n - 10)).length = n - 10 := by
    rw [List.length_take]
    omega
  have hgs : gs = gs.take (n - 10) ++ gs.drop (n - 10) := (List.take_append_drop _ _).symm
  have lr : ∀ y, (run (gs.take (n - 10)) (bw y)).length = n := by
    intro y
    rw [run_len, lA]
    simp [bw]
    omega
  refine base (gs.take (n - 10) ++ g :: (gs.drop (n - 10)).map fun g => ⟨g.op, g.inputs.map (re j n)⟩)
    (re j n o) ?_ ?_ fun y => ?_
  · intro a ha
    simp only [List.mem_append, List.mem_cons, List.mem_map] at ha
    rcases ha with ha | rfl | ⟨b, hb, rfl⟩
    · exact legal a (List.mem_of_mem_take ha)
    · simpa using hg
    · have := legal b (List.mem_of_mem_drop hb)
      simpa using this
  · simp only [List.length_append, List.length_cons, List.length_map, List.length_drop, lA]
    omega
  · rw [← h y, run_app, run_cons]
    have ev : g.op.eval (g.inputs.map fun i =>
        if i < n then ((Circuit.mk gs o).wires (bw y)).getD i false else false) =
        step (run (gs.take (n - 10)) (bw y)) g := by
      unfold step
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with hi
      · change (run gs (bw y)).getD i false = _
        conv_lhs => rw [hgs, run_app]
        exact run_old _ _ _ (by rw [lr]; exact hi)
      · exact (List.getD_eq_default _ _ (by rw [lr]; omega)).symm
    rw [ev]
    change _ = (run gs ((bw y).set j (step (run (gs.take (n - 10)) (bw y)) g))).getD o false
    have er : ∀ w, run gs w = run (gs.drop (n - 10)) (run (gs.take (n - 10)) w) := fun w => by
      conv_lhs => rw [hgs, run_app]
    rw [er, run_set (gs.take (n - 10)) (bw y) j (step (run (gs.take (n - 10)) (bw y)) g) (by simp [bw]; omega) hA]
    refine run_re j n hj _ _ _ (by rw [List.length_set, lr]) (by simp) (fun i => key j n hj _ _ (lr y) i) o
end PEqualNP.Outside.L_meta_3250

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_3250

theorem PEqualNP.Outside.L_meta_3250 :
    let F : (Fin 9 → Bool) → Bool := fun x =>
      ([(0,1), (1,2), (2,3), (3,4), (4,0), (0,5), (1,6), (2,7),
        (3,8), (5,7), (6,8), (8,5)] : List (Fin 9 × Fin 9)).any fun e => x e.1 && x e.2
    ∀ (j : Fin 9) (C : Circuit) (n i : Nat) (b : Bool),
      j ≠ 0 → j ≠ 6 → FanInTwo C → C.size ≤ 13 → 10 ≤ i → i < n → n ≤ 10 + C.size →
      (∀ g ∈ C.gates.take (n - 10), j.val ∉ g.inputs) →
      (∀ x : Fin 9 → Bool, let y := Function.update x j false
        F y ≠ F (Function.update x j true) → (C.wires (bw y)).getD i false = !b) →
      ∃ x : Fin 9 → Bool, let w := bw x
        let a := (C.wires w).getD i false
        C.eval (w.set j.val (if b = true then x j || a else x j && a)) ≠ F x := by
  intro x1 j C n i b _ _ legal small h1 hi h2 hA _
  by_contra hne
  refine ins j C n ⟨if b = true then GateOp.or else
    GateOp.and, [(j : ℕ), i]⟩ legal small (by omega) h2
    (by cases b <;> simp) hA fun y => ?_
  by_contra hh
  refine hne ⟨y, fun e => hh ?_⟩
  have ev : (C.wires (bw y)).getD (j : ℕ) false = y j := by
    refine (run_old C.gates _ _ (by simp [bw]; omega)).trans ?_
    exact rd y j
  have hj : (j : ℕ) < n := by omega
  simp only [List.map_cons, List.map_nil, ev, hj, hi, ite_true]
  refine Eq.trans ?_ (Eq.trans e (by simp [x1, edge, Bool.or_assoc]))
  cases b <;> simp [GateOp.eval, bw]
