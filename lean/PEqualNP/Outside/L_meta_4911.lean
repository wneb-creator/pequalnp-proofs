import PEqualNP.Defs
-- First-wire certificate from leoli001031-blip, PR #8875, revision 6da144a3e698b7fa294b1c1a701734123a016ddf.
-- Earlier live-set and graph-certificate work appears in PRs #6373 and #4332.
namespace PEqualNP.Outside.L_meta_4911_aux
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Bool) (a b : Sig) : Sig := if d then a ||| b else a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
private theorem bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]

-- A live state records exactly the wire values still needed to reach the target.
-- The truth table has one bit for each of the 512 input assignments.
def Live (target : Sig) (k t : Nat) (U : Finset Sig) : Prop :=
  ∀ P : Nat → Nat → Finset Sig → Prop,
    ((hp : proper target) → P 0 0 {target}) →
    (∀ {k t : Nat} {U : Finset Sig} {a : Sig}, (ha : proper a) → (hf : neg a ∉ insert a U) → P k t (insert (neg a) U) → P (k+1) (t+1) (insert a U)) →
    (∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}, (ha : proper a) → (hb : proper b) → (ne : a ≠ b) → (hf : bin d a b ∉ insert a (insert b U)) → P k t (insert (bin d a b) U) → P (k+1) t (insert a (insert b U))) →
    P k t U
theorem Live.stop {target : Sig}  (hp : proper target) : Live target 0 0 {target} :=
  fun P f0 f1 f2 => f0 hp
theorem Live.unary {target : Sig} {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a) (hf : neg a ∉ insert a U) (tail : Live target k t (insert (neg a) U)) : Live target (k+1) (t+1) (insert a U) :=
  fun P f0 f1 f2 => f1 ha hf (tail P f0 f1 f2)
theorem Live.binary {target : Sig} {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool} (ha : proper a) (hb : proper b) (ne : a ≠ b) (hf : bin d a b ∉ insert a (insert b U)) (tail : Live target k t (insert (bin d a b) U)) : Live target (k+1) t (insert a (insert b U)) :=
  fun P f0 f1 f2 => f2 ha hb ne hf (tail P f0 f1 f2)
theorem Live.induct {target : Sig} {P : ∀ (k t : Nat) (U : Finset Sig), Live target k t U → Prop}
    (stop : (hp : proper target) → P 0 0 {target} (Live.stop hp))
    (unary : ∀ {k t : Nat} {U : Finset Sig} {a : Sig}, (ha : proper a) → (hf : neg a ∉ insert a U) → (tail : Live target k t (insert (neg a) U)) → P k t (insert (neg a) U) tail → P (k+1) (t+1) (insert a U) (Live.unary ha hf tail))
    (binary : ∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}, (ha : proper a) → (hb : proper b) → (ne : a ≠ b) → (hf : bin d a b ∉ insert a (insert b U)) → (tail : Live target k t (insert (bin d a b) U)) → P k t (insert (bin d a b) U) tail → P (k+1) t (insert a (insert b U)) (Live.binary ha hb ne hf tail))
    {k t : Nat} {U : Finset Sig} (h : Live target k t U) : P k t U h := by
  apply Exists.elim (h (fun k t U => ∃ w : Live target k t U, P k t U w) (?_) (?_) (?_)) (fun w pr => pr)
  · intro  hp
    exact ⟨Live.stop hp, stop hp⟩
  · intro k t U a ha hf tail
    obtain ⟨tail, ih⟩ := tail
    exact ⟨Live.unary ha hf tail, unary ha hf tail ih⟩
  · intro k t U a b d ha hb ne hf tail
    obtain ⟨tail, ih⟩ := tail
    exact ⟨Live.binary ha hb ne hf tail, binary ha hb ne hf tail ih⟩


theorem live_zero {T k t S} (h : Live T k t S) (eq : k=0) : S={T} := by
  induction h using Live.induct with
  | stop hp => rfl
  | unary => omega
  | binary => omega

private lemma live_proper {k t S} (h : Live target k t S) : ∀ a ∈ S, proper a := by
  induction h using Live.induct with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {k t S} (h : Live target k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h using Live.induct with
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

def Reach {R : Type} (roots : List (Wire R)) (k : Nat) (ws : List (Wire R)) : Prop :=
  ∀ P : Nat → List (Wire R) → Prop,
    (P 0 roots) →
    (∀ {p : Nat} {bank : List (Wire R)} {a : Wire R}, P p bank → (ha : Available bank a) → P (p+1) (inv a :: bank)) →
    (∀ {p : Nat} {bank : List (Wire R)} {a b : Wire R}, (op : Bool) → P p bank → (ha : Available bank a) → (hb : Available bank b) → P (p+1) (combine op a b :: bank)) →
    P k ws
theorem Reach.start {R : Type} {roots : List (Wire R)}   : Reach roots 0 roots :=
  fun P f0 f1 f2 => f0
theorem Reach.one {R : Type} {roots : List (Wire R)} {p : Nat} {bank : List (Wire R)} {a : Wire R} (h : Reach roots p bank) (ha : Available bank a) : Reach roots (p+1) (inv a :: bank) :=
  fun P f0 f1 f2 => f1 (h P f0 f1 f2) ha
theorem Reach.two {R : Type} {roots : List (Wire R)} {p : Nat} {bank : List (Wire R)} {a b : Wire R} (op : Bool) (h : Reach roots p bank) (ha : Available bank a) (hb : Available bank b) : Reach roots (p+1) (combine op a b :: bank) :=
  fun P f0 f1 f2 => f2 op (h P f0 f1 f2) ha hb
theorem Reach.induct {R : Type} {roots : List (Wire R)} {P : ∀ (k : Nat) (ws : List (Wire R)), Reach roots k ws → Prop}
    (start : P 0 roots (Reach.start ))
    (one : ∀ {p : Nat} {bank : List (Wire R)} {a : Wire R}, (h : Reach roots p bank) → P p bank h → (ha : Available bank a) → P (p+1) (inv a :: bank) (Reach.one h ha))
    (two : ∀ {p : Nat} {bank : List (Wire R)} {a b : Wire R}, (op : Bool) → (h : Reach roots p bank) → P p bank h → (ha : Available bank a) → (hb : Available bank b) → P (p+1) (combine op a b :: bank) (Reach.two op h ha hb))
    {k : Nat} {ws : List (Wire R)} (h : Reach roots k ws) : P k ws h := by
  apply Exists.elim (h (fun k ws => ∃ w : Reach roots k ws, P k ws w) (?_) (?_) (?_)) (fun w pr => pr)
  · exact ⟨Reach.start , start ⟩
  · intro p bank a h ha
    obtain ⟨h, ih⟩ := h
    exact ⟨Reach.one h ha, one h ih ha⟩
  · intro p bank a b op h ha hb
    obtain ⟨h, ih⟩ := h
    exact ⟨Reach.two op h ha hb, two op h ih ha hb⟩


def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

def Run {R : Type} (goal : Wire R) (k : Nat) (ws : List (Wire R)) : Prop :=
  ∀ P : Nat → List (Wire R) → Prop,
    (P 0 [goal]) →
    (∀ {s : Nat} {xs zs : List (Wire R)}, (p : xs.Perm zs) → P s xs → P s zs) →
    (∀ {s : Nat} {a : Wire R} {rest : List (Wire R)}, (save : Bool) → P s (inv a :: kept save a rest) → P (s+1) (a::rest)) →
    (∀ {s : Nat} {a b : Wire R} {rest : List (Wire R)}, (op : Bool) → (ka : Bool) → (kb : Bool) → P s (combine op a b :: kept ka a (kept kb b rest)) → P (s+1) (a::b::rest)) →
    P k ws
theorem Run.stop {R : Type} {goal : Wire R}   : Run goal 0 [goal] :=
  fun P f0 f1 f2 f3 => f0
theorem Run.perm {R : Type} {goal : Wire R} {s : Nat} {xs zs : List (Wire R)} (p : xs.Perm zs) (h : Run goal s xs) : Run goal s zs :=
  fun P f0 f1 f2 f3 => f1 p (h P f0 f1 f2 f3)
theorem Run.one {R : Type} {goal : Wire R} {s : Nat} {a : Wire R} {rest : List (Wire R)} (save : Bool) (h : Run goal s (inv a :: kept save a rest)) : Run goal (s+1) (a::rest) :=
  fun P f0 f1 f2 f3 => f2 save (h P f0 f1 f2 f3)
theorem Run.two {R : Type} {goal : Wire R} {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op : Bool) (ka : Bool) (kb : Bool) (h : Run goal s (combine op a b :: kept ka a (kept kb b rest))) : Run goal (s+1) (a::b::rest) :=
  fun P f0 f1 f2 f3 => f3 op ka kb (h P f0 f1 f2 f3)
theorem Run.induct {R : Type} {goal : Wire R} {P : ∀ (k : Nat) (ws : List (Wire R)), Run goal k ws → Prop}
    (stop : P 0 [goal] (Run.stop ))
    (perm : ∀ {s : Nat} {xs zs : List (Wire R)}, (p : xs.Perm zs) → (h : Run goal s xs) → P s xs h → P s zs (Run.perm p h))
    (one : ∀ {s : Nat} {a : Wire R} {rest : List (Wire R)}, (save : Bool) → (h : Run goal s (inv a :: kept save a rest)) → P s (inv a :: kept save a rest) h → P (s+1) (a::rest) (Run.one save h))
    (two : ∀ {s : Nat} {a b : Wire R} {rest : List (Wire R)}, (op : Bool) → (ka : Bool) → (kb : Bool) → (h : Run goal s (combine op a b :: kept ka a (kept kb b rest))) → P s (combine op a b :: kept ka a (kept kb b rest)) h → P (s+1) (a::b::rest) (Run.two op ka kb h))
    {k : Nat} {ws : List (Wire R)} (h : Run goal k ws) : P k ws h := by
  apply Exists.elim (h (fun k ws => ∃ w : Run goal k ws, P k ws w) (?_) (?_) (?_) (?_)) (fun w pr => pr)
  · exact ⟨Run.stop , stop ⟩
  · intro s xs zs p h
    obtain ⟨h, ih⟩ := h
    exact ⟨Run.perm p h, perm p h ih⟩
  · intro s a rest save h
    obtain ⟨h, ih⟩ := h
    exact ⟨Run.one save h, one save h ih⟩
  · intro s a b rest op ka kb h
    obtain ⟨h, ih⟩ := h
    exact ⟨Run.two op ka kb h, two op ka kb h ih⟩


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
  induction h using Run.induct generalizing p bank with
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
  induction h using Run.induct with
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
  induction h using Live.induct generalizing v with
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
  induction h using Reach.induct generalizing k t S with
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
  induction h using Live.induct with
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
  induction h using Live.induct with
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
  induction h using Live.induct with
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
  induction h using Live.induct with
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


abbrev BoundPool := (Sig) × (Nat) × (Nat) × (List Sig)
abbrev BoundPool.domain (v : BoundPool) : Sig := v.1
abbrev BoundPool.bound (v : BoundPool) : Nat := v.2.1
abbrev BoundPool.paid (v : BoundPool) : Nat := v.2.2.1
abbrev BoundPool.wires (v : BoundPool) : List Sig := v.2.2.2


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
    have hz := live_zero h rfl
    rw [hz] at he
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
def IndexTree.leaf {α : Type} (xs : List α) : IndexTree α := xs
def IndexTree.fork {α : Type} (_p : Nat) (a b : IndexTree α) : IndexTree α := a ++ b
def IndexTree.read {α} (a : IndexTree α) (i : Nat) := a[i]?
def IndexTree.values {α} (a : IndexTree α) := a
theorem IndexTree.read_mem {α} (tree : IndexTree α) {i x} (h : tree.read i=some x) :
    x ∈ tree.values := List.mem_of_getElem? h

abbrev Forest := (Nat) × (Nat) × (Nat → Bits × Bits) × (IndexTree ColumnInfo) × (Array (List Nat)) × (Nat → Packing) × (Nat → Nat → Option (Nat × Nat))
abbrev Forest.mask (v : Forest) : Nat := v.1
abbrev Forest.cap (v : Forest) : Nat := v.2.1
abbrev Forest.samples (v : Forest) : Nat → Bits × Bits := v.2.2.1
abbrev Forest.cols (v : Forest) : IndexTree ColumnInfo := v.2.2.2.1
abbrev Forest.autos (v : Forest) : Array (List Nat) := v.2.2.2.2.1
abbrev Forest.levels (v : Forest) : Nat → Packing := v.2.2.2.2.2.1
abbrev Forest.index (v : Forest) : Nat → Nat → Option (Nat × Nat) := v.2.2.2.2.2.2


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

-- Each induced subgraph in this search retains the edge between vertices zero and four.
-- Its initial bank offers their disjunction at no cost.
def edgeBank (m : Nat) := vars m ++ [bin true (inputs.getD 0 zero) (inputs.getD 4 zero)]
def poolRoots (m : Nat) (c : ColumnInfo) := if c.2.2.1 < 1024 then vars m else edgeBank m
def ordinaryCol (m : Nat) (c : ColumnInfo) (p : Nat → Nat) := decide (c.2.2.1 < 1024) && colCheck m c p
theorem ordinary_sound {m : Nat} (c : ColumnInfo) (p : Nat → Nat)
    (lower : ∀ q, Lower (vars q) (graphGoal q) (p q))
    (valid : ordinaryCol m c p = true) :
    Slice (poolRoots m c) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  simp only [ordinaryCol,Bool.and_eq_true,decide_eq_true_eq] at valid
  obtain ⟨hc,ok⟩ := valid
  rw [poolRoots,if_pos hc]
  exact col_sound c p lower ok

def buildRule (g : Forest) (ops d : Nat) (bank : List Decor) (idx paid : Nat) : Option BoundPool :=
  (g.cols.read idx).bind fun ci =>
    materialize (poolRoots g.mask ci) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2

theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols.values, Slice (poolRoots g.mask ci) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
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
    (cols : ∀ ci ∈ g.cols.values, Slice (poolRoots g.mask ci) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
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
    have hz := live_zero h rfl
    rw [hz] at he
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
  g.cols.values.all (fun c => ordinaryCol g.mask c prior) &&
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
      (fun x hx => ordinary_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact block_at (rows 0 hk) i (by omega) (by omega)
  | succ k ih =>
    intro hk i hi
    apply nodeVerified_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => ordinary_sound _ prior lower (geometry.1.2 x hx)) geometry.2
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
def g15columns : IndexTree ColumnInfo := (IndexTree.leaf [])
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
def g31columns : IndexTree ColumnInfo := (IndexTree.fork 2 (IndexTree.leaf [(1,0,30,0,4),(2,0,29,0,4)]) (IndexTree.leaf [(4,0,27,0,4),(8,0,23,0,4),(16,0,15,0,4)]))
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
def g47columns : IndexTree ColumnInfo := (IndexTree.leaf [(8,0,39,0,4)])
def g47autos : Array (List Nat) := #[[],[83,32]]
def g47levels : Nat → Packing
  | _ => emptyPacking
def g47index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g47 : Forest := ⟨47,4,fun j => g47samples[j]?.getD (0,0),g47columns,g47autos,g47levels,g47index⟩
def g55samples : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbfffffdf7defdfafbfd3fcebcfdeffcebffefe76de77fed7f1773f95eb2ebeb,0x400028000010005000000400701010180030103060043200102204010904888),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdb7fbfbb9ad3afd94caf0b9db5bbdf7f7d39bfcdadcf77ec9eccd2fb9cf16b5,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2484444214284026a4e002420468a8a43140a00408d944460a4082569431231),(0xeda5e7e7b2fc29de4ffc371dba2bf0775ff12db9b18bb528fedad96afcd3c5e,0x12589919410293410206d0396285445a082c5d2bf0022b20f0895d2048c2c4e),(0,0),(0xf1cd79264efe956afa7a64bb677ab40beba463600362eda36f3357b7d763926,0xe3a8651b1a36a0acc57538a080f6ea703078a0c13c28dc34c91f3868663126),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe05fe74eda341d5872cbf684d5e2ed19e7e3bba5e964550dd792aec724f479,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01fb53db1204342a549861b60b6727a22d48ac0b14da4445855161ae724b471),(0,0),(0,0),(0,0)]
def g55columns : IndexTree ColumnInfo := (IndexTree.leaf [(16,0,39,0,4)])
def g55autos : Array (List Nat) := #[[],[84]]
def g55levels : Nat → Packing
  | _ => emptyPacking
def g55index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g55 : Forest := ⟨55,4,fun j => g55samples[j]?.getD (0,0),g55columns,g55autos,g55levels,g55index⟩
def g63samples : Array (Bits × Bits) := #[(0xdabffdfdbdf61bfbfc7dcbe34f7f1b17917df75df7edd9eff77b6dbd3dcebed3cfbfaddba50fcabded46bc9b579eb7bd3d92776566ad4ad3debe36d74deb7f9faf189ad76da7dc1a6b4eaf21eb254de4ae1f7451bb34d9456fd18e934db17349,0x4400202400040800310000100084000ac0000102800a1100490002240004b2800a001b4000190000008108000574009200040400000594000190004218c0010840002890800550053044a00410008802d0060013000c004400188120c206208),(0xb6678efeffcbf5a9cad5bfd527a7a5bd74d1314b7915f5b2ffdec2fc5d978f8ab3b44b2b5add5b771711b15ce99bf2b3f5bce975ef94cd59a34e76ab937848a94ef6be6c9579db5905539ea703c87a7d4ae11fe2ae423fade4a3c3299b0724e7,0x499461811a200a55004cf88854029340027a680613c002ec00233c1096d01045025d0203d400243150030b7e4900b00499e023395882049d0206ec00041398010bbb1000b7310ad00cc0858112c8207810e917400e423d0034024309910504e5),(0xbfdd27bedf8fade4776ebf9d185bc5bd76aeffb29711f77d628e86e5fffdff6d1a52bff6da987348e3e147dcecdbcc68d1accc4e7d7d77b9734cfbbcefbc022d72eff5a31a72e32584dd5a72accb1256ede309af577ea6b3ab2be572a2769632,0x20983204990108b1910222a2810c12a8041040402e00006394000908008912a582448429aad10a21a0240190b504314209040621245140c82010e8812042049440841100c0c52080310832a5111106e902488a012c82618908a42202729212),(0x77ddb87389d95f9f7bbe7e8eb89e6e76fbf75ca7fd5bb3758b555b578affe964ae7e7fa493e06d03bebc4fb5cff51e46b2dd5bdbb1eab66f60f7d916b9c6944fd85b6f0fc30a2ae7d2afc9dc369ef80bb1b0b2dd52e9331e786f7a5d38e8c8b4,0x1482478012444200420888514440810c402202189081ecc814422aa4c048408050190921c0450c000a080254044021081134422900082c11250884167012813a48094aca870a3283708e41084282480000c012150640581c30655a55288040a4),(0xdca768aafb78ce8d2db2ec3fbdddfa4ec963339dbac7a8e05eccbf0bb99ddf5febcef6dc7762a4a79d9ad8f70324ba6e724754bded1eed86f695f276b70acbd73dc66e39a88d0cfed920a0ee10b5a4dd5893bba709bff6dc1ece388c561e1ed5,0x210938550593284a984457082a220ca002159526023c0223a02100100d271046aa46f2022bb0201ea5730921b3008e848a002106a7520082d20653c8040064810364a00030c5086c0c2084761035a077101508a009ba22e00b822088521e1c51),(0x77dad76bd4ced656e7ec247a694c9eb5b66dc4de71aac18acebb177a9bac7a62d6f3e3996dd9d62d6ecf7b18557229a30b5ebb1ef46b568a8f3400a7c2d3365caade63d0f2234a24623735bcfaee29c0664eddfc63b2a86915f817ca03dc41fa,0x88252894b2b3256598a758928465236453b27d28c68c4c28a24dcc0d24d500d4a845700845b04bd175706d345a20a0a24d641d897dd822a1d52444cad2629c8e732b305273362844202335b73c8d8150424e93e44a78286995ec17c803dc01f2),(0,0),(0,0),(0,0)]
def g63columns : IndexTree ColumnInfo := (IndexTree.leaf [(32,0,31,0,7)])
def g63autos : Array (List Nat) := #[[],[50,65]]
def g63levels : Nat → Packing
  | _ => emptyPacking
def g63index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g63 : Forest := ⟨63,7,fun j => g63samples[j]?.getD (0,0),g63columns,g63autos,g63levels,g63index⟩
def g111d6 (i : Nat) : Nat := 0x120ff
def g111l6 : Packing := (1,0,2,0,1,0,0,g111d6)
def g111samples : Array (Bits × Bits) := #[(0xeafcc7b96fc59ffd26c5e2bb3d7bd378fb35ff5dcb26f92afa5f57eff59a73b7aaa379b2fc8d7a99e2ef9efcf4defd4efabc9c89733cebade5579ad5abbcd64d8557ad3d63bd1c6a75510ce3b9bf05e462ee0edf6dfb2914efc74c7d31727465,0x4d00310a2003881269402d0c00406ccc142a8012908082d00025ac006a88036948003229000032d4001bf20024ec2018680000aaf2500325400423a6f02003840040a8016ea8106822700071012c01d500600ad401ea0010f407087831504444),(0xf771ad34ff2bcf4fbd7f5f5de52efaeb7ebbabfffefbf2eab7c7cf56f8ecea565ddfabcf87cb61db9d6ef4aecff7cebd76fe679cfb9935e6adabc77cdcdb677ed3da5e4f56b4cbe39cfd7aed1f519a6b999796b48a51f4f7b8ad91a66cc6d9cb,0x1204940050200482000010001c10308054448009004424020800871400ac0690000402004e0508404004081210450414000904018220d090010808000a44280600460810104d92040818880c1010088d8400200a10a1400808810604821909),(0xf5be76df5e79b8b5d13f5f6e3ecd176fbeee538a7cfb9f7f6b7fad9b13bb7fed97560ecd71f29f3f1e3ef959a338e3a9e32bd5e7cfc7b51df73d7e9e165479b3baa9a0d59e62e11eead3ad5c624777de8699f96d3766d64d1f3fa2ca8f3d2e52,0x8e4d19200884440101e4a802e100a0c04000830eb000289800c49240c1c411082c325a6812b0485430294040c52402008322a4b0e00c0021216842103a050a9080848145264020288841a770220547500211500d95204c05521120880b352452),(0xde2ebbc73c1cf83c4cedbed77297d7f5b666582db23d5c5d7bf4a54b37a75f4992f88d683d388ea5bafb57791a5deb9b257390777cf70e9d329773c24416edd93fe3d2909bc3b81d7e62dd94d70a759eb42b6b51587d63da2e7eea6ce78912bc,0x10b22099c5638280b403142808691e02bd9d04d1097a9640ce2041351e20e64283892100494815238b12089820999d9858901b4e1903515e001721098578a5416f515492d981d895722018845902b08a5c4a2a2248dd03d08c66ca64e48812ac),(0,0),(0x4a99db5e74fdf3bbfb83b4b12e735e58f515867b75942dba656f9eeac55739b971685432ece5b39368c30fbbb9f895ca9efa5eceda2fea7be4766f052ba5def635ccf928215f7640050f6846acafb2ca6efbba0bffbfdb9043d87d111c3c3ebd,0x12d68401de50564414b80023f49c0203c0413d800068400bbb08034f0177ac0427f40400f6de0023bcc009fc1201950403ff4900082ea08a2fc908010c8a4053de0011e801464d050407f806ac13f8026d9b800bfa055d40038875010c2c3ab9),(0x107b7e8791b6519a9ebd6f37d374faa298392ebad8b5e4afe6bd267679568b3365bebaabdf6ef4e9035a918e8ca50ef74769b2b74aea726a09a6c5e9463715fb76745a9b1b6212a1b9add6dec52a9ba55b57e399ab660ca6d0f217384af881fe,0xadc48a6a24248ac9294916cc74a18dce4988890976a839d0a90054480a8f001149b409fd5690d8d50882129489ae3083c83b5253565cd02541ca4550f495b985581508b28aaa022919a1e755a00eaaa54243a315f06a0c87d4f216384a7880f6),(0,0),(0,0)]
def g111columns : IndexTree ColumnInfo := (IndexTree.leaf [(4,8,99,0,4),(1,32,78,0,4),(64,0,47,0,5)])
def g111autos : Array (List Nat) := #[[],[83,32]]
def g111levels : Nat → Packing
  | 6 => g111l6
  | _ => emptyPacking
def g111index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | _ => fun _ => none
def g111 : Forest := ⟨111,6,fun j => g111samples[j]?.getD (0,0),g111columns,g111autos,g111levels,g111index⟩
def g119samples : Array (Bits × Bits) := #[(0xfab75f3dfbfa3756f92d9ff7baf5ff7dbfebb9b33bef7dcdf77fbffe7bbbf75546cedccfd6f7eb762bef3ffdd2ede7abbef7e4e4b775eb9be6ab6f4d5fde77f2b955ece57b3feb97c6d99b5cdd2fdd2ea315de5f3efbf8d44ddcaa7566eda9cd,0x20100000802449000a820000c1900042800052080010000098c000620802429000050a2000012e00000be20013404000082000047420011240000c8b8000110080002480036500158018000c4009400c9000c0062803a0400e00885042a10888),(0xaf7efcd6de9febfb57d6f5ddedde36f3db7fffeed79fdbfafcf255738c743cbbbff3e3b86b8f9fb9f5bdf54fbff79bd74f5afb3f7fba34f5bf5f9afae879ab5feefe93fa9ee6566f7bbee6bf67d426d75cfb2bace9344fabf72bd58e999b76b3,0x9300010000091004000400382060802420900110020801010208161810541520000000800198110400c004084880812115000049028020c0800220200009220a01801050108206a8408406120184808104430800802442850101410609083421),(0xd3aee9d1a16b8afb579b1b1a2ede96c634714fced4ed35afb8d86696aabedb2eada373270f48f3a9b93de8a90d87d8f6684756adef8eb40bf672fc78b9342c9c7aaa652b2aec9422dd38b32b2a5255bdcc3d35b2da5f372953f3c4ba3a70d996,0x2c07b23e74020fd2aa41748155856818d263d681015680dac92709c7448b08586eaf3a512642c64b613a9091954b38c222671d26711d023332d48951dd0691952839212f8b6888039910b9ac2a42653c283c65315b1b95185ae084b83270c996),(0,0),(0x759a506bc07865de6f37bc2fabe39a5e2705b6a3eec6bd3cca572e3ed72f0325f632aa43d8e0e833eaeab6f86ad5fa72dbaf9c83b9e70faa212acf122e177ae733d8fa39a0b0bb12b7915f7134c3b9a9ed98d75362b1d9c725676c3caf04637c,0x16e5f59c6d01a255c44806523c0cddb5529a2196d082e7c24415d298c0f10d071e6090549dc090f8ed501938009f3fb2169588d90b0b506d102e01343cb84ad135f45369a498be0a36011e712702bb816af81651c4b05c0701a6642cad046374),(0x6339c3e76f77dc41ec6c9766b8b0f93592cd6e58a17db2abb9eea5cd269eeae2dc2c1c9ec755bae6a2821f6b678c3538a75edaf56c57e97ff4e8b90d55c4e75ce36b37ac511be4c610c6f229b9ab77956345b3a117ef6f3608dd37697870ba61,0x84ef690f5888a6bc0049f9381c0ba0115db000874a075d2102333605e754184fe100105f739880fb92c019ec481f2d2102dbf2480954a0ad3f922114724920d57f80032e5018c6a22083e62199863ec06b43378157e41d3d00d937293850b261),(0xd5cc96ab2735f4eedbcfece9fd4d847149d75b8aa71ff3959066dc7566c66ecb75975abde9bb8d684d89311f3151135dd1ce4d97acd9737d0b4d97b62b1596cf57b51ab1b6b408593b67d5bb928b32dabad66fc43367241aeaae177095e247ea,0x481560b0cd924918c5323d4303992d88d1232e6a49f254a2454320824e8122936522ef3572424e688310332525616c12e023da92a435d213539c9243b254cc21b63548a8e4258841b361f1c95a017252ba1c47902bc1245a7a8e167094e243ca),(0,0),(0,0)]
def g119columns : IndexTree ColumnInfo := (IndexTree.leaf [(4,0,115,0,5)])
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
def g189columns : IndexTree ColumnInfo := (IndexTree.fork 4 (IndexTree.leaf [(1,0,188,0,5),(12,0,177,0,4),(16,0,173,0,5),(17,0,172,0,4)]) (IndexTree.leaf [(24,0,165,0,4),(33,0,156,0,4),(132,0,57,0,4),(160,0,29,0,4)]))
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
def g127columns : IndexTree ColumnInfo := (IndexTree.leaf [(32,0,95,0,8)])
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
def g191columns : IndexTree ColumnInfo := (IndexTree.fork 19 (IndexTree.fork 9 (IndexTree.fork 4 (IndexTree.leaf [(1,0,190,0,7),(2,0,189,0,8),(3,0,188,0,5),(4,0,187,0,7)]) (IndexTree.fork 2 (IndexTree.leaf [(6,0,185,0,5),(8,0,183,0,8)]) (IndexTree.leaf [(0,8,163,20,6),(10,0,181,0,5),(12,0,179,0,5)]))) (IndexTree.fork 5 (IndexTree.fork 2 (IndexTree.leaf [(4,8,163,16,5),(14,0,177,0,4)]) (IndexTree.leaf [(16,0,175,0,8),(0,16,166,9,6),(1,16,166,8,5)])) (IndexTree.fork 2 (IndexTree.leaf [(19,0,172,0,4),(24,0,167,0,7)]) (IndexTree.leaf [(16,8,163,4,5),(8,16,166,1,5),(25,0,166,0,4)])))) (IndexTree.fork 9 (IndexTree.fork 4 (IndexTree.leaf [(9,16,166,0,4),(20,8,163,0,4),(32,0,159,0,8),(1,32,30,128,5)]) (IndexTree.fork 2 (IndexTree.leaf [(35,0,156,0,4),(40,0,151,0,5)]) (IndexTree.leaf [(48,0,143,0,5),(56,0,135,0,4),(128,0,63,0,8)]))) (IndexTree.fork 5 (IndexTree.fork 2 (IndexTree.leaf [(130,0,61,0,5),(4,128,27,32,5)]) (IndexTree.leaf [(136,0,55,0,5),(160,0,31,0,7),(128,32,30,1,5)])) (IndexTree.fork 2 (IndexTree.leaf [(32,128,27,4,5),(161,0,30,0,4)]) (IndexTree.leaf [(129,32,30,0,4),(164,0,27,0,4),(36,128,27,0,4)])))))
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
def g251columns : IndexTree ColumnInfo := (IndexTree.leaf [(8,0,243,0,7)])
def g251autos : Array (List Nat) := #[[],[84,115],[99,65],[118,84,115,65],[118,81],[118,84,99,81]]
def g251levels : Nat → Packing
  | _ => emptyPacking
def g251index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g251 : Forest := ⟨251,7,fun j => g251samples[j]?.getD (0,0),g251columns,g251autos,g251levels,g251index⟩
def g255samples : Array (Bits × Bits) := #[(0x9b665c544a8481c32c829a3849d25a0c2e734bceaece0410b1910c9246b692285657c973ca335d593cb00f0546b90059eb43e97a932728851785431870f031165ac8b80393ba6e576270cc58c906b870841734e15dc89803598ab05c2460a6b1,0x104454110880808228020a2041d8002c08600a02808c02009111060244ac12008614a1024802115108904700443200508241c8821224200116051018407029164080a01212302c0942400010c90428108414142154888803090a9048202086a0),(0xf315668af28fdb1ca228365b7ccc05a0011317731e21482f697635c521d4e57b4580944cacd08190116899ef79421d834fcee4e488905930903982805fb1c61927af17aaf49049a676974192f0d0160363a1bd03830701b0dc1f8281c2dc6123,0x83112a82400c43108201140b24040542001210600e014836084820c40800442b4181104024900000902098cc210099010006246088901220003082011981800902040620cc814002101041843090160043212902810201b054050081825c2101),(0x380526282fa13ac851f4c9c505254980d6e8ec3804b3594a769d93b950ebc251b0d8e2a15610b8154799066089743516386914b45de9a6e1e91c2d64aa4bec2945782990b2d68e61aa4d3cd1b24a6ab680984b4c1298da14a63264e421a50a46,0x184000082381184051a442400021c800c760240c008201086414493150c8805030586481420228050588002082640402084818905528808149002d00020c144045280184104604602a043c40824a60b20098024012185a048212646400810a02),(0x96903da21572f2b1f1c959078994a771bc47364121282ac5966e24786e0f6b8886ae49c27124b27b7242ff2e0094e0b4b1b582696d3c94568c371a6b03b30075a8d6353ad9672c0089eb12ba6325f80dd24d451b8459a7c113618d0b812f118c,0x86100cb01034a2a12848198388d4226018030240202c8a411a0a044824066a838a240842212092185a40cf0a0080e094a530c6680a1400448645526011312024a0c7343889210800016b021a61259805924545098441a1c11120810b812e1184),(0xca830c6ee5a1c1ac77b2c4bb013b84b271c7189edce77b42164b82b2ec44ccc2202552493f52e619512b4f09e2177ba801c291327039cbf4fba1fd7ca29d36ceca40c4508827295a1b45be11b7c00687be220f65622167c80c13fe90c415919,0x1282044674a181cc515204830038803270c71014e5265b22464b9241a4004482002443590d10ca0850630203a411b2a000c201185038c3861ba0d078200d6480c204804048212d4a89449e11258006869a220d60222163c80c12ea00c414819),(0xadcb89db333a54791fc5b16de6a74b1fbdaa5224c4caa060c8434905e130b3e50875189fa3aee40ebf67487ce98db2673644923b555505294552488c144494c2312ef3656d2d51ee39b1b44e04f3d3ec4d148000ab72771f011403179f478e82,0xa991884a13221d3803c5e045a0014312e78660240442614040424905201081f109410899826ca6043646807ca808b20b342020284941850001124c8410049440302c118d6904416438b533460072d3ec490080008b50771c0014031517470802),(0xccf1d170b069949f14600d7679a83ea985e068495997ad010287ff4ea745b576050c4fa9e8e0fabd2497448bd27a5aa8acea4ac0268e4d44dc2df9de452a225ad1457b3d721818b9bf9e05034d50ecb938aed67098a522a72856072e55b8d214,0xce85130b040942f1560095449a91aad8dc0e80b5196a18140955b282345b194266c47298868eeb9221d4601c27a00e8acf04a8036004c04cc8c58ecc43a23d68161791d311c0cb9abcc24434d40e8b9388ed67018a522072852072e55a0d214),(0x442aa5b9d884c622461c21eaaaf556fac8da8923687abbfb99c9c28096422e0eb83cb34c1d8918aec8c55d99f53bc2670104934ee2f27258616b2c55a56fa8970e02486406e9b92b5242282d15890d903f02672424a3e96d3ce1d022fa0aa8e8,0x460a679588446000a40a01aa08c414e80818810338389a92898982c08602320ec02091061180118a88016c815113416481048146a2821250206d8051a4632a958802cc600689381b004a400915810c003602652424a380613ce19002e808a0e8),(0,0)]
def g255columns : IndexTree ColumnInfo := (IndexTree.leaf [(64,0,191,0,11)])
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
def g383columns : IndexTree ColumnInfo := (IndexTree.fork 29 (IndexTree.fork 14 (IndexTree.fork 7 (IndexTree.fork 3 (IndexTree.leaf [(1,0,382,0,9),(0,1,332,50,7),(2,0,381,0,9)]) (IndexTree.leaf [(0,2,312,69,7),(3,0,380,0,6),(2,1,332,48,6),(1,2,312,68,6)])) (IndexTree.fork 3 (IndexTree.leaf [(4,0,379,0,11),(5,0,378,0,7),(7,0,376,0,5)]) (IndexTree.leaf [(5,2,312,64,5),(8,0,375,0,9),(0,8,99,276,7),(12,0,371,0,8)]))) (IndexTree.fork 7 (IndexTree.fork 3 (IndexTree.leaf [(13,0,354,0,4),(14,0,369,0,5),(16,0,367,0,11)]) (IndexTree.leaf [(17,0,366,0,8),(18,0,365,0,7),(19,0,364,0,5),(18,1,332,32,5)])) (IndexTree.fork 4 (IndexTree.leaf [(24,0,359,0,8),(25,0,358,0,5),(28,0,355,0,7),(20,8,99,256,5)]) (IndexTree.leaf [(32,0,351,0,11),(33,0,350,0,8),(32,1,332,18,6),(35,0,348,0,5)])))) (IndexTree.fork 15 (IndexTree.fork 7 (IndexTree.fork 3 (IndexTree.leaf [(34,1,332,16,5),(44,0,339,0,5),(49,0,334,0,7)]) (IndexTree.leaf [(48,1,332,2,5),(33,16,326,8,5),(56,0,327,0,5),(64,0,319,0,11)])) (IndexTree.fork 4 (IndexTree.leaf [(65,0,318,0,7),(66,0,317,0,8),(67,0,316,0,5),(65,2,312,4,5)]) (IndexTree.leaf [(70,0,313,0,7),(34,64,29,256,5),(256,0,127,0,9),(0,256,23,104,7)]))) (IndexTree.fork 7 (IndexTree.fork 3 (IndexTree.leaf [(264,0,119,0,6),(256,8,99,20,6),(8,256,23,96,6)]) (IndexTree.leaf [(268,0,115,0,5),(260,8,99,16,5),(280,0,103,0,5),(272,8,99,4,5)])) (IndexTree.fork 4 (IndexTree.leaf [(288,0,95,0,8),(289,0,94,0,5),(40,256,23,64,5),(304,0,79,0,5)]) (IndexTree.leaf [(320,0,63,0,8),(322,0,61,0,5),(258,64,61,0,5),(352,0,31,0,7)])))))
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
def deadcolumns : IndexTree ColumnInfo := (IndexTree.fork 63 (IndexTree.fork 31 (IndexTree.fork 15 (IndexTree.fork 7 (IndexTree.fork 3 (IndexTree.leaf [(1,0,510,0,12),(0,1,460,50,8),(2,0,509,0,12)]) (IndexTree.leaf [(0,2,440,69,8),(3,0,508,0,9),(2,1,460,48,7),(4,0,507,0,12)])) (IndexTree.fork 4 (IndexTree.leaf [(0,4,369,138,8),(5,0,506,0,8),(6,0,505,0,9),(4,2,440,65,7)]) (IndexTree.leaf [(2,4,369,136,7),(7,0,504,0,7),(5,2,440,64,6),(8,0,503,0,12)]))) (IndexTree.fork 8 (IndexTree.fork 4 (IndexTree.leaf [(0,8,227,276,8),(9,0,486,0,8),(10,0,501,0,8),(12,0,499,0,9)]) (IndexTree.leaf [(8,4,369,130,7),(4,8,227,272,7),(14,0,497,0,7),(10,4,369,128,6)])) (IndexTree.fork 4 (IndexTree.leaf [(15,0,480,0,4),(16,0,495,0,13),(0,16,486,9,10),(17,0,494,0,11)]) (IndexTree.leaf [(16,1,460,34,7),(19,0,492,0,8),(16,4,353,138,7),(21,0,490,0,7)])))) (IndexTree.fork 16 (IndexTree.fork 8 (IndexTree.fork 4 (IndexTree.leaf [(21,2,424,64,5),(24,0,487,0,11),(8,16,486,1,9),(25,0,486,0,8)]) (IndexTree.leaf [(9,16,486,0,8),(27,0,484,0,5),(11,16,484,0,5),(24,4,353,130,6)])) (IndexTree.fork 4 (IndexTree.leaf [(29,0,482,0,5),(26,4,353,128,5),(32,0,479,0,12),(0,32,94,385,8)]) (IndexTree.leaf [(32,1,460,18,7),(1,32,94,384,7),(35,0,476,0,7),(34,1,460,16,6)]))) (IndexTree.fork 8 (IndexTree.fork 4 (IndexTree.leaf [(36,0,347,0,8),(39,0,344,0,4),(40,0,471,0,8),(49,0,462,0,8)]) (IndexTree.leaf [(48,1,460,2,6),(50,1,460,0,5),(56,0,455,0,7),(64,0,447,0,13)])) (IndexTree.fork 4 (IndexTree.leaf [(0,64,189,258,10),(66,0,445,0,11),(2,64,189,256,9),(67,0,444,0,8)]) (IndexTree.leaf [(66,1,396,48,6),(70,0,441,0,8),(69,2,440,0,5),(74,0,437,0,7)]))))) (IndexTree.fork 31 (IndexTree.fork 15 (IndexTree.fork 7 (IndexTree.fork 3 (IndexTree.leaf [(74,4,305,128,5),(80,0,431,0,11),(83,0,428,0,7)]) (IndexTree.leaf [(96,0,415,0,9),(96,1,396,18,6),(98,1,396,16,5),(128,0,383,0,13)])) (IndexTree.fork 4 (IndexTree.leaf [(128,1,332,50,7),(3,128,344,36,6),(132,0,379,0,11),(4,128,347,32,9)]) (IndexTree.leaf [(133,0,378,0,7),(134,0,377,0,8),(132,2,312,65,6),(133,2,312,64,5)]))) (IndexTree.fork 8 (IndexTree.fork 4 (IndexTree.leaf [(136,0,375,0,9),(128,8,99,276,7),(140,0,371,0,8),(132,8,99,272,6)]) (IndexTree.leaf [(138,4,369,0,5),(144,0,367,0,11),(152,4,353,2,5),(160,0,351,0,11)])) (IndexTree.fork 4 (IndexTree.leaf [(160,1,332,18,6),(162,1,332,16,5),(164,0,347,0,8),(36,128,347,0,8)]) (IndexTree.leaf [(172,0,339,0,5),(176,1,332,2,5),(180,0,331,0,5),(192,0,319,0,11)])))) (IndexTree.fork 16 (IndexTree.fork 8 (IndexTree.fork 4 (IndexTree.leaf [(198,0,313,0,7),(256,0,255,0,12),(258,0,189,0,8),(260,0,251,0,8)]) (IndexTree.leaf [(264,0,247,0,9),(256,8,227,20,7),(8,256,151,96,7),(268,0,243,0,7)])) (IndexTree.fork 4 (IndexTree.leaf [(260,8,227,16,6),(273,0,238,0,7),(280,0,231,0,8),(276,8,227,0,5)]) (IndexTree.leaf [(288,0,223,0,9),(256,32,94,129,7),(32,256,151,72,7),(257,32,94,128,6)]))) (IndexTree.fork 8 (IndexTree.fork 4 (IndexTree.leaf [(296,0,215,0,7),(40,256,151,64,6),(304,0,207,0,6),(288,16,198,9,6)]) (IndexTree.leaf [(273,32,78,128,5),(56,256,135,64,5),(320,0,191,0,11),(256,64,189,2,9)])) (IndexTree.fork 4 (IndexTree.leaf [(322,0,189,0,8),(258,64,189,0,8),(324,0,187,0,7),(324,8,163,16,5)]) (IndexTree.leaf [(321,32,30,128,5),(388,8,99,16,5),(168,256,23,64,5),(224,256,23,8,5)]))))))
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


def rootCheck (m hints : Nat) :=
  let pairs := graphPairs m hints
  checkEssential (graphGoal m) (edgeBank m) pairs &&
    sameWords (pairs.map Prod.fst) (vars m)

theorem edgeBankLower {m cap hints} (hp : proper (graphGoal m))
    (check : rootCheck m hints = true) (normal : Lower (vars m) (graphGoal m) (cap+1))
    (both : Impossible (graphGoal m) cap (edgeBank m).toFinset) :
    Lower (edgeBank m) (graphGoal m) (cap+1) := by
  intro p bank reached hit
  obtain ⟨k,t,S,hk,run,sub⟩ := reach_live hp reached hit
  by_contra! small
  have bound : k ≤ cap := by omega
  simp only [rootCheck, Bool.and_eq_true] at check
  obtain ⟨checks,eqs⟩ := check
  have need (a : Sig) (ha : a ∈ vars m) : a ∈ S := by
    obtain ⟨r,s,hd,iso⟩ := essential_ok checks a ((sameWords_sound eqs).symm ▸ List.mem_toFinset.mpr ha)
    exact raw_required run _ a sub r s hd iso
  let g := bin true (inputs.getD 0 zero) (inputs.getD 4 zero)
  by_cases hg : g ∈ S
  · have hs : (edgeBank m).toFinset = S := by
      ext a
      rw [List.mem_toFinset]
      refine ⟨?_,sub a⟩
      intro ha
      rcases List.mem_append.mp ha with ha | ha
      · exact need _ ha
      · exact List.mem_singleton.mp ha ▸ hg
    exact both k t bound (hs.symm ▸ run)
  · have only : ∀ a ∈ S, a ∈ vars m := by
      intro a ha
      rcases List.mem_append.mp (sub a ha) with h | h
      · exact h
      · have eq : a = g := List.mem_singleton.mp h
        exact False.elim (hg (eq ▸ ha))
    have lower := subsumed hp run only normal
    omega

def augmentedTest (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) :=
  let (z,o,q,_,L) := c
  let b := q-1024
  let ms := fixRows z o
  checkMap ms (edgeBank m) (chartGoal m) (edgeBank b) (graphGoal b) &&
    (movedWord ms (subcube z o) == one) && properB (graphGoal b) && decide (L ≤ prior b)
theorem augmentedCol_sound {m} (c : ColumnInfo) (p : Nat → Nat)
    (lower : ∀ q, Lower (edgeBank q) (graphGoal q) (p q))
    (high : ¬ c.2.2.1 < 1024) (ok : augmentedTest m c p = true) :
    Slice (poolRoots m c) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  obtain ⟨z,o,q,s,L⟩ := c
  simp only [augmentedTest,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at ok
  rw [poolRoots,if_neg high]
  exact slice_correct ok.1.1.1 ok.1.1.2 (proper_of _ ok.1.2)
    (fun a b c d => ok.2.trans (lower _ a b c d))

def goodCol (m : Nat) (p n : Nat → Nat) (c : ColumnInfo) :=
  if c.2.2.1 < 1024 then ordinaryCol m c p else augmentedTest m c n
theorem eitherCol {m p n} (c : ColumnInfo)
    (a : ∀ q, Lower (vars q) (graphGoal q) (p q)) (b : ∀ q, Lower (edgeBank q) (graphGoal q) (n q))
    (h : goodCol m p n c = true) :
    Slice (poolRoots m c) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  unfold goodCol at h
  split at h
  · exact ordinary_sound c _ a h
  next e => exact augmentedCol_sound c _ b e h

def augmentedGeom (g : Forest) (p n : Nat → Nat) :=
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 768) &&
  (chartSamples g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.values.all (goodCol g.mask p n) &&
  g.autos.toList.all (fun a => autoOK (targetOf g) (a.map swapRows))

theorem augmentedRoots (g : Forest) {p n}
    (a : ∀ q, Lower (vars q) (graphGoal q) (p q)) (b : ∀ q, Lower (edgeBank q) (graphGoal q) (n q))
    (geom : augmentedGeom g p n = true) (rows : checkedTables g g.cap) :
    ∀ k ≤ g.cap, ∀ i < (g.levels k).1, Impossible (targetOf g) k (stateSet g k i).toFinset := by
  simp only [augmentedGeom,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geom
  intro k
  induction k with
  | zero =>
    intro hk i hi
    apply nodeVerified_sound g 0 i (chart_pairs geom.1.1.1 geom.1.1.2)
      (fun x hx => eitherCol x a b (geom.1.2 x hx)) geom.2 (by omega)
    exact block_at (rows 0 hk) i (by omega) (by omega)
  | succ k ih =>
    intro hk i hi
    apply nodeVerified_sound g _ i (chart_pairs geom.1.1.1 geom.1.1.2)
      (fun x hx => eitherCol x a b (geom.1.2 x hx)) geom.2 (fun _ => by simpa using ih (by omega))
    exact block_at (rows _ hk) i (by omega) (by omega)

def augmentedKnown (e : List (Nat × Nat)) := ∀ a ∈ e, Lower (edgeBank a.1) (graphGoal a.1) a.2
theorem augmentedPrior {e} (h : augmentedKnown e) (q : Nat) :
    Lower (edgeBank q) (graphGoal q) (boundsBefore e q) := by
  unfold boundsBefore
  cases eq : e.find? (fun a => a.1 == q) with
  | none => exact fun _ _ _ _ => Nat.zero_le _
  | some a =>
    have key := List.find?_some (p:=fun a : Nat × Nat => a.1 == q) eq
    have he : a.1=q := beq_iff_eq.mp key
    simpa [he] using h a (List.mem_of_find?_eq_some eq)

theorem augmentedCons {old m L} (p : augmentedKnown old) (q : Lower (edgeBank m) (graphGoal m) L) :
    augmentedKnown ((m,L)::old) := by
  intro a ha
  rcases List.mem_cons.mp ha with rfl | h
  · exact q
  · exact p _ h

def chunkOK (g : Forest) (k : Nat) (v : Nat × Nat × Nat) :=
  header g k v.1 v.2.1 v.2.2 && rowCut g k v.1 v.2.1 v.2.2 0 v.2.2
theorem chunkBlock {g k v} (h : chunkOK g k v = true) : block g k v.1 v.2.1 = true := by
  simp only [chunkOK,Bool.and_eq_true] at h
  exact cutsBlock h.1 h.2
def chain (j : Nat) : List (Nat × Nat × Nat) → Nat → Bool
  | [],e => j==e
  | v::vs,e => (v.1==j) && chain (j+v.2.1) vs e
theorem chunkChain {g k} (vs : List (Nat × Nat × Nat)) (a e : Nat)
    (hc : chain a vs e = true) (ok : vs.all (chunkOK g k) = true) : block g k a (e-a)=true := by
  induction vs generalizing a with
  | nil =>
    have eq : a=e := beq_iff_eq.mp hc
    subst e
    simp [block]
  | cons v vs ih =>
    simp only [chain,Bool.and_eq_true,beq_iff_eq] at hc
    simp only [List.all_cons,Bool.and_eq_true] at ok
    have bound (j : Nat) (l : List (Nat × Nat × Nat)) (h : chain j l e = true) : j ≤ e := by
      induction l generalizing j with
      | nil => exact Nat.le_of_eq (beq_iff_eq.mp h)
      | cons u us qi =>
        simp only [chain,Bool.and_eq_true] at h
        have := qi _ h.2
        omega
    have le := bound _ _ hc.2
    have b := chunkBlock ok.1
    rw [hc.1] at b
    have more := block_merge b (ih _ hc.2 ok.2)
    simpa only [show v.2.1+(e-(a+v.2.1))=e-a by omega] using more

theorem chunkLevel {g k} (vs : List (Nat × Nat × Nat)) (hc : chain 0 vs (g.levels k).1 = true)
    (ok : vs.all (chunkOK g k)=true) : block g k 0 (g.levels k).1=true := by
  simpa using chunkChain vs 0 _ hc ok
def f31S : Array (Bits × Bits) := #[(0xbce40177f101076b7a930efbf4751ebce40177f101076b7a930efbf4751ebce40177f101076b7a930efbf4751ebce40177f101076b7a930efbf4751ebce40177f101076b7a930efbf4751ebce40177f101076b7a930efbf4751ebce40177f101,0x27855113c101076858119804e0080927855113c101076858119804e0080927855113c101076858119804e0080927855113c101076858119804e0080927855113c101076858119804e0080927855113c101076858119804e0080927855113c101),(0x95901cad978ae172ddef649cd2772695901cad978ae172ddef649cd2772695901cad978ae172ddef649cd2772695901cad978ae172ddef649cd2772695901cad978ae172ddef649cd2772695901cad978ae172ddef649cd2772695901cad978a,0xc8222ea41682b012858400100cf506c8222ea41682b012858400100cf506c8222ea41682b012858400100cf506c8222ea41682b012858400100cf506c8222ea41682b012858400100cf506c8222ea41682b012858400100cf506c8222ea41682),(0x4310fd5803efd49def4d354da22bec4310fd5803efd49def4d354da22bec4310fd5803efd49def4d354da22bec4310fd5803efd49def4d354da22bec4310fd5803efd49def4d354da22bec4310fd5803efd49def4d354da22bec4310fd5803ef,0x32d9915801684d0560011c6c02026032d9915801684d0560011c6c02026032d9915801684d0560011c6c02026032d9915801684d0560011c6c02026032d9915801684d0560011c6c02026032d9915801684d0560011c6c02026032d991580168),(0x420be384ccf5be9ff220f300fbbed1420be384ccf5be9ff220f300fbbed1420be384ccf5be9ff220f300fbbed1420be384ccf5be9ff220f300fbbed1420be384ccf5be9ff220f300fbbed1420be384ccf5be9ff220f300fbbed1420be384ccf5,0x45244604c49510a08630a000f0f81345244604c49510a08630a000f0f81345244604c49510a08630a000f0f81345244604c49510a08630a000f0f81345244604c49510a08630a000f0f81345244604c49510a08630a000f0f81345244604c495),(0x286f02f26c5aaec6a1f1cfe36f903d286f02f26c5aaec6a1f1cfe36f903d286f02f26c5aaec6a1f1cfe36f903d286f02f26c5aaec6a1f1cfe36f903d286f02f26c5aaec6a1f1cfe36f903d286f02f26c5aaec6a1f1cfe36f903d286f02f26c5a,0x985aa8e0284ac802204447b10e0044985aa8e0284ac802204447b10e0044985aa8e0284ac802204447b10e0044985aa8e0284ac802204447b10e0044985aa8e0284ac802204447b10e0044985aa8e0284ac802204447b10e0044985aa8e0284a),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def f31C : IndexTree ColumnInfo := (IndexTree.leaf [(16,0,15,0,4),(8,0,23,0,4),(4,0,27,0,4),(2,0,29,0,4)])
def f31A : Array (List Nat) := #[[],[64,49]]
def f31d5 (i : Nat) : Nat := 0x988001db920bf2aa817d52502faa2a07e4c140
def f31l5 : Packing := (4,2,2,0,0,5,0,f31d5)
def f31d6 (i : Nat) : Nat := 0xa63fd40
def f31l6 : Packing := (1,1,2,0,0,0,0,f31d6)
def f31h6 (i : Nat) : Nat := 0xb42a380008fc18
def f31levels : Nat → Packing
  | 5 => f31l5
  | 6 => f31l6
  | _ => emptyPacking
def f31index : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 3 8 2 7 2 1 f31h6
  | _ => fun _ => none
def f31 : Forest := ⟨31,6,fun i => f31S[i]?.getD (0,0),f31C,f31A,f31levels,f31index⟩
def f31c5 : List (Nat × Nat × Nat) := [(0,4,6)]
def f31c6 : List (Nat × Nat × Nat) := [(0,1,6)]
def f189S : Array (Bits × Bits) := #[(0x597c38123874388d27fcd16e63d48b5fec44fb9ebe746a2a5092092ac6b88d1597c38123874388d27fcd16e63d48b5fec44fb9ebe746a2a5092092ac6b88d1597c38123874388d27fcd16e63d48b5fec44fb9ebe746a2a5092092ac6b88d1597,0x495018922864d8c02094847203d009410608419402566801d74069024698091495018922864d8c02094847203d009410608419402566801d74069024698091495018922864d8c02094847203d009410608419402566801d74069024698091495),(0x0,0x0),(0x631aaaf8e8919756b2a5c4a56e2dd436a4dbcdfd4b88cc50ab00d28b9f01772631aaaf8e8919756b2a5c4a56e2dd436a4dbcdfd4b88cc50ab00d28b9f01772631aaaf8e8919756b2a5c4a56e2dd436a4dbcdfd4b88cc50ab00d28b9f01772631,0x430a8068201000520201c800ec2921276049ada908805e30476215889501670430a8068201000520201c800ec2921276049ada908805e30476215889501670430a8068201000520201c800ec2921276049ada908805e30476215889501670430),(0x4e61ddf7fd8b7e06213b8642c47874fc32be512cc7b385850241d6c74b5602e4e61ddf7fd8b7e06213b8642c47874fc32be512cc7b385850241d6c74b5602e4e61ddf7fd8b7e06213b8642c47874fc32be512cc7b385850241d6c74b5602e4e6,0x860599780857f2c212a0402111054180610500404172089b019e8434a5400e0860599780857f2c212a0402111054180610500404172089b019e8434a5400e0860599780857f2c212a0402111054180610500404172089b019e8434a5400e086),(0x3c45bf4d35ba04907d525b6ac4b7ae037ae4b8d1d59f2c8f504304fc31c2c593c45bf4d35ba04907d525b6ac4b7ae037ae4b8d1d59f2c8f504304fc31c2c593c45bf4d35ba04907d525b6ac4b7ae037ae4b8d1d59f2c8f504304fc31c2c593c4,0x340d26401608001018411b80c40da20279c5ac40e180043608a616bc3102c40340d26401608001018411b80c40da20279c5ac40e180043608a616bc3102c40340d26401608001018411b80c40da20279c5ac40e180043608a616bc3102c40340),(0x84aa760e467c6eabc8ca2817776b33f809b4efce3ce053a004bc2938ed3c6ac84aa760e467c6eabc8ca2817776b33f809b4efce3ce053a004bc2938ed3c6ac84aa760e467c6eabc8ca2817776b33f809b4efce3ce053a004bc2938ed3c6ac84a,0x84292209c018043800021805482a30ba09a4a42a3ca01638203b9438892462884292209c018043800021805482a30ba09a4a42a3ca01638203b9438892462884292209c018043800021805482a30ba09a4a42a3ca01638203b94388924628842),(0x0,0x0),(0xb1d6567a13c9e3f4fa56acb91b8710e89d4196474a9bf9d0ad2c2016305d707b1d6567a13c9e3f4fa56acb91b8710e89d4196474a9bf9d0ad2c2016305d707b1d6567a13c9e3f4fa56acb91b8710e89d4196474a9bf9d0ad2c2016305d707b1d,0x30d015001380fb84e05007b81314484084001244424aa18798846a06205810730d015001380fb84e05007b81314484084001244424aa18798846a06205810730d015001380fb84e05007b81314484084001244424aa18798846a06205810730d),(0x0,0x0)]
def f189C : IndexTree ColumnInfo := (IndexTree.leaf [(24,0,165,0,4),(17,0,172,0,4)])
def f189A : Array (List Nat) := #[[],[64,114,83]]
def f189d6 (i : Nat) : Nat := 0x80c100bf58930bf58530fe48130
def f189l6 : Packing := (3,2,1,0,0,5,0,f189d6)
def f189d7 (i : Nat) : Nat := 0x43fd30
def f189l7 : Packing := (1,1,1,0,0,0,0,f189d7)
def f189h7 (i : Nat) : Nat := 0x356e01866c89900
def f189levels : Nat → Packing
  | 6 => f189l6
  | 7 => f189l7
  | _ => emptyPacking
def f189index : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 3 8 3 7 2 1 f189h7
  | _ => fun _ => none
def f189 : Forest := ⟨189,7,fun i => f189S[i]?.getD (0,0),f189C,f189A,f189levels,f189index⟩
def f189c6 : List (Nat × Nat × Nat) := [(0,3,7)]
def f189c7 : List (Nat × Nat × Nat) := [(0,1,7)]
def f215S : Array (Bits × Bits) := #[(0x3d0a71dbafe226df14c676af3096713f92cbccdef181d85d8db95a4d0759fd60e91e8538edd7f1136f8a633b57984b389fc965e66f78c0ec2ec6dcad2683acfeb0748f429c76ebf889b7c5319dabcc259c4fe4b2f337bc607617636e569341d6,0x1e0240278200060ea444742b20124802800a0cce2c88347d091158400659d0202e0f012013c100030752223a15900924014005066716441a3e8488ac20032ce8101707809009e0800183a9111d0ac8049200a00283338b220d1f424456100196),(0xd6bfec4a6f499de7c7fdb954ed4d6dc99cf88bafcbdabd8e7a49ad6e7180410e95eb5ff62537a4cef3e3fedcaa76a6b6e4ce7c45d7e5ed5ec73d24d6b738c020874af5affb129bd26779f1ff6e553b535b72673e22ebf2f6af639e926b5b9c60,0x8980403503100040008114084c218124e08121d15400007008850e01802004808044c0201a8188002000408a042610c092704090e8aa00003804428700c0100240402260100d40c400100020450213086049382048745500001c0221438060),(0x68dd9fbeb014f97eec3338cb8268c76f7716766b046c07a350363ef0cabfd29d4eb46ecfdf580a7cbf76199c65c13463b7bb8b3b35823603d1a81b1f78655fe94ea75a3767efac053e5fbb0cce32e09a31dbddc59d9ac11b01e8d40d8fbc32af,0x50141d8c0010e1508c1030090310406e1a1312ca02093b3300362ae04a0a162906280a0ec6000870a846081804818820370d09896501049d99801b157025050b1483140507630004385423040c0240c4101b8684c4b280824eccc00d8ab81282),(0x0,0x0),(0x656f7f9910abaad819aac661f09ed1944c43e759f0014053f5a4423f3c4f3e75b9b2b7bfcc8855d56c0cd56330f84f68ca2621f3acf800a029fad2211f9e279f3adcd95bdfe6442aeab6066ab1987c27b4651310f9d67c005014fd69108fcf13,0xa11dbf98100b29c059a28250d28cb1004de5f2001377cb82f4a4023f38062c4691508edfcc080594e02cd141286946588026f2f90009bbe5c17a52011f9c03162348a8476fe60402ca701668a09434a32c4013797c8004ddf2e0bd29008fce01),(0x0,0x0),(0xcb3069d2437d1c582709e73aed3d5cf0dd6373e40a1220082ec4cbb2727a4b1a7f659834e921be8e2c1384f39d769eae786eb1b9f205091004176265d9393d258d3fb2cc1a7490df471609c279cebb4f573c3758dcf9028488020bb132ec9c9e,0xcb30651300606c583a493421f532de32991972c00eabfff80ec44ab07278c31a5f659832898030362c1d249a10fa996f194c8cb9600755fffc07622558393c618d2fb2cc1944c0181b160e924d087d4cb78ca6465cb003aafffe03b112ac1c9e),(0x2ce5f3749874402c3bf5e48eca2b9b23e3e4b777642402244c5694979f76fadb421672f9ba4c3a20161dfaf2476515cd91f1f25bbbb2120112262b4a4bcfbb7d6da10b397cdd261d100b0efd7923b28ae6c8f8f92dddd90900891315a525e7dd,0x2560e0701c65062c31e141a284cb8b0161e40d355df6c4c44c4094179574e816d012b070380e32831618f0a0d14265c580b0f2069aaefb626226204a0bcaba740b680958381c0719418b0c785068a132e2c05879034d577db13113102505e55d),(0x0,0x0)]
def f215C : IndexTree ColumnInfo := (IndexTree.leaf [])
def f215A : Array (List Nat) := #[[]]
def f215d6 (i : Nat) : Nat := 0x1fd30
def f215l6 : Packing := (1,1,1,0,0,0,0,f215d6)
def f215levels : Nat → Packing
  | 6 => f215l6
  | _ => emptyPacking
def f215index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def f215 : Forest := ⟨215,6,fun i => f215S[i]?.getD (0,0),f215C,f215A,f215levels,f215index⟩
def f215c6 : List (Nat × Nat × Nat) := [(0,1,7)]
def f243S : Array (Bits × Bits) := #[(0x85a23f367e9af3dabf02c7feda2151f6b8373f7ebed653372bd20d6aa8f83e7456c2d11f9b3f4d79ed5f8163ff6d10a8fb5c1b9fbf5f6b299b95e906b5547c1f3a2b61688fcd9fa6bcf6afc0b1ffb688547dae0dcfdfafb594cdcaf4835aaa3e,0x86802800069c02122102922882004050802e0050004809252890046080500c0012c3401400034e01091081491441002028401700280024049294480230402806000961a00a0001a700848840a48a20801014200b8014001202494a2401182014),(0x6991e2ca896de6869ff34417a5fce62b6a4e98ec1911aa2b919df80d15cef7dedfb4c8f16544b6f3434ff9a20bd2fe7315b5274c760c88d515c8cefc068ae77bef6fda6478b2a25b79a1a7fcd105e97f398ada93a63b06446a8ae4677e034573,0x2110c342014120848a31241404ba942d2a0018a059863482810ce80d1488b235c0108861a100a090424518920a025d4a1695000c502cc31a41408674068a44591ae0084430d080504821228c4905012ea50b4a80062816618d20a0433a034522),(0x0,0x0),(0x0,0x0),(0x2522b519dd92377c9efdacf87065cd5c39f322bd64c240049748d0f2afaa81e62812915a8ceec91bbe4f7ed67c3832e6ae1cf9915eb26120024ba4687957d540f3140948ad4677648ddf27bf6b3e1c1973570e7cc8af5930900125d2343cabea,0x213a4553d9223d68dc59201079e107043b50128f5fb7f6d09748d0922fab81f628109d22a9ec911eb46e2c90083cf083821da80947afdbfb684ba4684917d5c0fb14084e9154f6488f5a371648041e7841c10ed404a3d7edfdb425d234248bea),(0xbb4fcaf7a612087ded6dff023e7e1e859790e54be22c15d0ef62a79d4715ea83735da7e57bd309043ef6b6ff811f3f0f42cbc872a5f1160ae877b153cea38af541b9aed3f2bde984821f7b5b7fc08f9f87a165e43952f88b05743bd8a9e751c5,0x190ac2d7a0010045c451640608053a051080270b348132d08362a39c01042007090c85616bd0008022e228b20304029d02884013859a40996841b151ce00821003848642b0b5e80040117114590182014e81442009c2cd204cb420d8a8e70041),(0x5e7cf0adc1e54cd8a5df82abff8da709f8ca8484a101a80d92ad55347336f5c8bcaf3e7856e0f2a66c52efc155ffc6d384fc6542425080d406c956aa9a399b7ae45e579f3c2b707953362977e0aaffe369c27e32a12128406a0364ab554d1ccd,0x866a3ca8c0244d3b258e808bbb05220010eec515a679cb7d12a11530633440c81c43351e546012269d92c74045dd8291000877628ad33ce5be89508a98319a20640e219a8f2a3009134ec963a022eec14880043bb145699e72df44a8454c18cd),(0x77fd0af1bde42fa568afb9c1105a0d1bb7b65c61402804c874a4eef16ec14fe3353bfe8578def217d2b457dce0882d068ddbdb2e30a01402643a527778b760a7f19a9dff42bc6f790be95a2bee7044168346eded9718500a01321d293bbc5bb0,0x421508204eac1ba008a499d8924a056aa27650e04b7ecd2874844c616ec147e8b4210a841027560dd004524cec492502b5513b287025bf66943a422630b760a3f45a1085420813ab06e8022926762492815aa89d943812dfb34a1d2113185bb0),(0x0,0x0)]
def f243C : IndexTree ColumnInfo := (IndexTree.leaf [])
def f243A : Array (List Nat) := #[[],[81,118]]
def f243d6 (i : Nat) : Nat := 0x1fd20
def f243l6 : Packing := (1,1,1,0,0,0,0,f243d6)
def f243levels : Nat → Packing
  | 6 => f243l6
  | _ => emptyPacking
def f243index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def f243 : Forest := ⟨243,6,fun i => f243S[i]?.getD (0,0),f243C,f243A,f243levels,f243index⟩
def f243c6 : List (Nat × Nat × Nat) := [(0,1,7)]
def f191S : Array (Bits × Bits) := #[(0x660a58c1431d42c9a8ccda20f41d148e32900a63502714a87bcf0ca05332a8e1af312ee03c2042a376f4bce6230fcc6481e773fe1e0c47c6e4fc2c38c15ad19fcc1982963050c750b26a3336883d0745238ca40298d409c52a1ef3c32814cca,0x2200010c10150018984008a00c808b51c0046230010040428338f04a010300080262100201000c02008d008e01104000401216026008c02c440f84410c19840920088000430405400626100228032022d47001188c00401010a0ce3c128040c0),(0x1d8a609463682e223336cb8fa2200028890c04f377949c0112d61455a69c1ce4f0579d2984ef25f5dd067596af85b671c078417edf317a3e23292a2a9a86a1a6608762982518da0b888ccdb2e3e888000a2243013cdde5270044b5851569a707,0x1d8a6492c36025a26306c307235f64262ff99ccb7694940110c60410a49c1ce260158d2020a321a544225c50a485b7208429c1748e013a102290130a80a471804007629924b0d8096898c1b0c1c8d7d9098bfe6732dda5250044318104292707),(0x35518315686c625f0eb33e6570a00e2618d40f59002d4b98580afa1dd22a5540d73cbfc7ec5ce5925a11b41919f85e3d6e641a43567f81ca94208f4055a264d0c50d5460c55a1b1897c3accf995c280389863503d6400b52e61602be87748a95,0x600340200042550030083008209a89500641240020098848083a0d42224200920022c5085040101a10a00b492800016a440803103401ca140084003040004105001800d008001095400c020c020826a2540190490008026212020e83508890),(0xc80f636f98ee47f3bd6b458cc48c260010c2e008c6dc02714b5fc32280c5e9160d49f1803913f0fe63c8562994efdb5081d0bbe0a808ef88c77031384ec9e71c227203d8dbe63b91fcef5ad163312309800430b80231b7009c52d7f0c8a0317a,0x28a1004986f05821c4a670c64994554a698a652c4dc02510317c0228005a916094a900223a0106e218846a01041db50819813602208e401802231388899e1140000a28401261bc160871299c31926515529a62994b137009440c5f008a0016a),(0xdb6be46a9e92aac303541918870d31006022e000aa50ade32ce10b9e14e41519b7b5c748d40b333f526b2a05ca2fa78ea387a2940d556fd05d5ca096537d98871636daf91aa7a4aab0c0d5064621c34c401808b8002a942b78cb3842e7853905,0xc861ac6240000a4503149051836630aa1963198c2a00ada02cc00b9414e014a034954718cc0a21105a608811ca2e048e0205a8940d51121239504004526418c21432186b189000029140c5241460d98c2a8658c6630a802b680b3002e5053805),(0x48a4bac35351f9c5e59c10327c52c0d1060110054cea8daca54206312d17e2f37fc4c3143f351b75a1a0f2681c370c1b9879755a31a691631a87727f228433aa0d52292eb0d4d47e717967040c9f14b03441804401533aa36b2950818c4b45f8,0x8022a8534040e88544881014202d10a817b31d0f04ea0da8244206310c1462a2158483013e3542358530b2400c2e0c110b6d6138013703538200723222002a00086008aa14d0103a2151220405080b442a05ecc743c13a836a0910818c430518),(0x0,0x0),(0x29dd1900bf68092bfc4cf67a9212089704101b0078a5c6c721116ce079c8982160dc761240babfc5a0dfcdb1be1780ef7ea3d7d1208e5c01508f9c3c31305662eb0a7746402fda024aff133d9ea4848225c10406c01e2971b1c8445b381e7226,0x298510209e2a0522a046a64a91d26556a848a2d07805c247011140c031c8980940505832018abdc020c349901251c04e040092440c887c04408f080109315422f20a614408278a8148a811a992a4749955aa1228b41e017091c04450300c7226),(0x0,0x0)]
def f191C : IndexTree ColumnInfo := (IndexTree.fork 12 (IndexTree.fork 6 (IndexTree.fork 3 (IndexTree.leaf [(176,0,15,0,4),(168,0,23,0,4),(164,0,27,0,4)]) (IndexTree.leaf [(162,0,29,0,4),(161,0,30,0,4),(160,0,31,0,7)])) (IndexTree.fork 3 (IndexTree.leaf [(160,0,1055,0,7),(134,0,57,0,4),(129,32,30,0,4)]) (IndexTree.leaf [(36,128,27,0,4),(35,0,156,0,4),(28,0,163,0,4)]))) (IndexTree.fork 6 (IndexTree.fork 3 (IndexTree.leaf [(26,0,165,0,4),(25,0,166,0,4),(24,0,167,0,7)]) (IndexTree.leaf [(20,8,163,0,4),(19,0,172,0,4),(14,0,177,0,4)])) (IndexTree.fork 3 (IndexTree.leaf [(9,16,166,0,4),(4,0,187,0,7),(2,0,189,0,8)]) (IndexTree.leaf [(2,0,1213,0,8),(1,0,190,0,7),(0,0,191,0,11)]))))
def f191A : Array (List Nat) := #[[]]
def f191d6 (i : Nat) : Nat := 0x61001e08880f03040f3778502795a324961505409ec6809258541502ba4a2619414c540aad6988250531502bb1a0209414c540
def f191l6 : Packing := (5,5,5,0,0,6,0,f191d6)
def f191d7 (i : Nat) : Nat := 0x210784020f100020108000012189c30000000040030800203080c10203840610100d1c20801c40f088800f06081e10006290e078c200f060c2011100088612388c24711840e078810e07881c1210361c121801810040200000000000f08482000482000000e080000001c10001e10703c243e97a0e6f96e237ad8f55d1f42cf738c6313c3b09c12f6bc6e3b56c7ac2a2a2e74976469062a8720e7b9ce6ddb266d845b5565453a48d033f8f03acdd360d3338c9310bf2e8b529c992508f2047c1dc721b45f168551404b118380cc2e080008fec8d10bb2811fd92a21755023fb23442eaa04df65482591408fec910eb1a8137d95209635027eb22412c6a04fe6408258d408fec910ea9a811fd91a21725025fb2d442a4a055f25d5354940e9eaa2e4a92819bc87551325033b90eb1a64a047f2617588940cde43aa9112815f5919dd615026fb2a412c2a04f764c82585409fcc8104b0a811fd9221d515032f90ea92a2a05ed6462250540bda492c2a0a81db57258541503d6ac4b0a82a04fb249864c540cde43aa898a812fd96209315026fb2a41262a04fe640824c540ddac328298a81bb48250531503f2a64a0a62a04df6568858140f5ab0a82b0281ed96358130503e72a8a9260a07e658d414c140fcca9a8298281fb16150530503f32a898a60a07f4545314c1409fac8d10902819f5872052050376b0ca0a20a07ec50520441409beca9050028117d95a21765027b326402c8a04f664c8055140bccc9900aa2811bd94a21735023bb27442e4a047d646885c9408ee4c466b92819d483205725027b32640282a05e664c80505408fa4c2e508a811bd989dc4050267d32c2880a064f9dd8510140d1f3330a2028193d855c84050365b0b11080a04eda658110140cdb3bb0220281ab6666044050366caac0880a066d5c98110140dd31130220281b358584440503e32a8a9a60a07e4505314c140
def f191l7 : Packing := (76,4,5,0,0,10,0,f191d7)
def f191h7 (i : Nat) : Nat := 0x5cb381d332
def f191d8 (i : Nat) : Nat := (if i<1 then 0xc8254140dfd7254140dfc7254140dfd7154140f7d5154140fbd4154140bfd864c140bfd854c140fdd634c140fdd534c140fdd314c140ff9604c140ff9504c140ff9624c140ff9524c140ff9614c140ff9514c140ff9214c140bfe8848140dfc8748140dfe7748140bfd8648140dfd7648140bfd8548140dfd7548140fbd5448140bfd8348140dfd7348140dfd7248140fed5248140ff48148140dfd7148140fbd4148140fed2148140ff96048140ff93048140bfd8608140bfd8508140bfd8644140dfd7644140bfd8544140dfd7544140fbd5444140bfd8344140dfd7344140bfd8244140dfd7244140ff55144140ff93044140ff92044140bfc82801409fd869dd409fd859dd40dbd849dd409fd839dd409fd829dd409fd819dd409fe885d940cfe77999409fe885d540d7e7795540bf88059140bf88055140bbe8855140dbe7755140fb88055140dbe7791140dbd7691140ebe6691140dbd7591140f3e55911409fe885cd40cfe665cd40d7e555cd409fd8758d409fc8758d40cfd7658d409fd8754d409fc8754d40f3d5454d40dde778cd40ddd768cd40ede668cd40ddd758cd40f5e558cd40f9d548cd409fe885c940cfe665c940d7e555c940dbd545c940dbe445c940ddc835c940dde335c940df4815c940ded721c9409fd861c940cfe661c9409fd851c940d7e551c940dbe441c9409fd831c940dde331c9409fd811c9409fd87589409fc87589409fd87549409fc8754940f3d54549409fc8750940dec7250940bf880509409fd874c9409fc874c9409fc8788940ded7288940dec8788940dee7788940ded7688940eee6688940ded7588940f6e5588940fad5488940fae4488940ded7388940fce33889409fe885c540cfe665c540d7e555c540dbe445c540dde335c540dee225c5409fd87585409fc87585409fd87545409fc8754540bf88050540bbe8850540dbe7750540ebe6650540bbd8550540f3e5550540f9e3350540dbd7250540fae2250540fb56150540fb880505409fd874c5409fc874c540fb5414c5409fd87485409fc8748540df67784540df57684540ef66684540df57584540f765584540fb55484540fb64484540df57384540fd63384540df57284540df47284540fe62284540f3d5454140dbe7710140ebe6610140bbd8510140f3e5510140dbd7210140fae2210140bbd8110140fb61110140bfa884c140dfa774c140efa664c140f7a554c140fb9544c140fd9634c140fd9534c140df9724c140fea224c140fb9414c140fd9314c140ff2114c1409fd8748140dec7248140fb54144140dfa7780140df97680140efa6680140df97580140f7a5580140fb95480140fba4480140bf98380140df97380140fda3380140df97280140df87280140fea2280140df97180140fb94180140ff21180140b3d8510140bb58110140 else (if i<2 then 0x714b7fdb8ad8b6b0b4dda1ace366cb2bd90ac5b620b05d7babb35c4ad3d64aafb568aa5d4daa4350ca7bd38a97b4a0a45d1da8c344ca1bd06a80b3e89e9ceda74338c9b7cd6a68b330989cbba5a32bc953ca2a4cb248919c85a4031f48efc72a35b1908bdc5ba2b3144897c46a1fb0e8865c2da13308482fc12a05b018801bfb9fb2fc47d3be49efaf707b1bd19e62f1c787bbc9daaeb874db9d9cc2e3c70fb829bfade86e5b699b12d6c6a3b4c9a2acf866db339972c9c647b1c98aac40615b0397f2be45e7aee974ab905bdad796a2b3458fac295daad0561aab9532a7c533a96948aa38519a8b9442a14507a8093da9e84eda7593829b44d3a6292da948499a4792128fc473a3891aa8d045da2590f285c41ba068ffa7e83e99f38f727ac3cb9e28efa7683ad9cd8e226f43679ac8d2a68033d99d8cb263430397a8bba5d02dd96d8b525a42c79628afa5782b19558a9253c2979488a0a4e826992d89624a424b92088ba44821990387f23dc1eb8f0872a3701a98cd86523141878c085fa2e81718b585a22bc1578aa850a28013d89d84e226412f89684aa24811d88984221f40e786e833a1880b5853827211408783c81ca0d006582f81720a404f824810a08003181580a204401780a802a000bfc825d940bfc825d540dfc825d540bfc8259140bfc8255140fbc8255140bfe8858d40dfe7758d40bfc8258d40bfe8854d40dfe7754d40bfc8254d40dfd635c940dfd535c940bfd861c940bfd851c940dfd751c940fbd541c940dfd721c940dfd541c940bfe8858940dfe7758940dfd7358940efd6358940dfd7258940bfe8854940dfe7754940f7d5454940dfd7354940f7d5354940dfd7254940bfe884c940dfe774c940bfd864c940dfd764c940bfd854c940dfd754c940fbd544c940fdd634c940dfd724c940dfc8788940dfe7788940bfd8688940bfd8588940dfd7588940fbd5488940bfd8388940dfd7288940bfd8188940bfd8088940dfd635c540dfd535c540dfd625c540dfd525c540dfd325c540dfe225c540bfe8858540dfe7758540dfd7358540bfc8258540dfd7258540efd6258540bfe8854540dfe7754540dfd7354540bfc8254540dfd7254540dfc7254540f7d5254540ff56150540fbd6350540fbd5350540fbd6250540fbd5250540fbd3250540fbe2250540bfe884c540dfe774c540bfd864c540dfd764c540bfd854c540dfd754c540fbd544c540bfc824c540dfd724c540fdd324c540ff5514c540bfe8848540dfd8748540dfe7748540bfd8648540dfd7648540bfd8548540dfd7548540fbd5448540bfd8348540dfd7348540dfd7248540ff56148540ff53148540bfe8858140dfe7758140dfd7358140efd6358140bfc8258140dfd7258140dfd7158140efd6158140fbd4158140bfe8854140dfe7754140dfd7354140bf else 0x940844a0420001288349444a001030109100878894043c48802102080110789082650043c82528021e4250210104080041021108004080824412042090212707890e19381c604102028608186830822180861a1e24e5486022058688342c4121a20b450918692840c202c48a10225091470888004242020d1010688082044a20d0b0f1868888341c4044a1a30901104008824084108c0430f0b10108080c2441206209031081289019025380c6200e203081040188200c4202424e1203181040840182064a28210940e18804081c4048c201031110108038830344181e1a30d8e940f204a2860c343c410182450e1218807890610483c306202220d8e1218386893821a0e2090710483a28c2034946100e24508786883c1c424222250710687888c00104010c123048610903270c089449ca8090c40486106832a0c121840008200081430208940849c241430802143020848210109250d186840848384241120e0d186c7230d16384871c1a1e38e460d0f24707883638483c91c1a1e300121080408404124a2030913459521284080c204e5468a252a1044e1012706ca8d39525464a8a10310089080950484061a12545091caa7068c9408404102090d25184850820284101424508106890938284241a24e0a121890538344871c202120210804868c402c206081120f101868840083461224286089040a182001284942086092a28804a100906891828c105030918708008c3818482480e1021001109040a1824a8a20128404a8a208091012223474a0d1a3a5060a8c1c244460e9418600890d1a5040624200104880820410202081042c3c404108111007202870a04901c340860a1c28104100d021a703040c2c484000a01878c24202c408122410201a5864e54186861824a8a20128404a8a204304024202460a3051828c14608285848c1c340c616102160d031811828c1469410b4a8409111a5048d282140e95122234a0a38551860020f10488868406145030384881c02243080d071c30495144025080951440860821938404100b040309100000038200011828c1468e12347083918486241c8c1e4460f10707890d1a3841caa243550e0f1a3470838500c48801016121c304951440250809514400d0c30410c9ca83020821830ca820070b08385859f4cefe76b38b9b0cc9e5fb2d3944c97e46b20b8e0c5de29b12388cc3be1ab0ab840c15e05aff37dcbe3deaaf2b778bb1dcfae53))
def f191l8 : Packing := (317,3,5,0,0,13,0,f191d8)
def f191h8 (i : Nat) : Nat := 0x2428000018c0997c54724800e3101966859e212f686e0c8e9a85ae0edd127603f28854abe8e0018cd26c50cfa59b16d010200052598507a4200071c6881b2c900106c0000000043400000a8827c21824f3b02c00695b472fc00000d620015bb93b5cc3287a822590efca0000014d4a0786e5fca78bec667a003038892551202081800520328004e0012440ce000f4c180089240183
def f191d9 (i : Nat) : Nat := 0x5870d2441242a862452154312209a8403122d5203831228e1a48606a121e4030e381a8487901c18e3aaa58c549184901a39c248120e3431c44ea8401121a1915080f1c962923921e962912038e44825124c3921a3d2548121ce121c90d2a18f38188245468639520486309258a3c6951c88a45295241c69c94e1242a0e0c7253880a1c18c347121ce27512c52a4872081210e2a406392962048a589940b3871025186a87132826a920c7a93830c713293aa920c7a93830cb0eaa48316a452c3884ca550a3a30d1e8a91470e7051c52ac62471c3c8091a4cddc313a9167187130a563102472c388462a48d1671518e2c2aa487c61c5a914b4e1c5f61e23b3f3fe2fbf763e91cc5923095d5b3f5a692d0b9ab27e42c48824f71d6b936acd0d94b0156ca013323042c7b8e69902ec500888e21581f431850050003ff3ba81ff5d940ffaeaa07fd64503feaa281ff5cd40ffac6a07fd53503feb9281ff1c940ffac4a07fd52503fea1281ff4c940ffc44a07fd71503feb0a81ff54540ffa82a07fd31503fe90a81ff58140ffaa0a07fd30503fe90281ff08140ffa20a07fe00502ff3ba817f5d940dfccca05fd75503bf2aa81ef55140f7c88a05fd73503ef19a817f5c940bf8e4a07ee22502feb8a81ef50540fec22a07bc40503fc98281fe80140
def f191l9 : Packing := (46,2,5,0,0,11,0,f191d9)
def f191h9 (i : Nat) : Nat := 0x724edf72c1f83000000000077e80000000000000001011ce400002271bc000000311000129980c800053db030000c5c4ab64d0000000001c3d996f831464000d1531278578dbd5264791ff86fe37139d91eaebc2c32e7c0e6b6d5e000396aa6401a9c17970684f2d895c0c684552702b0196514811a8d164e0ef210000097500bc10890c8025230003bd000087d576e3b8001628351eb0aa7600020c6a1426703923c2c2c00124b60aca528908a9e6f813e6126bd941dafd8d6a1f550ac4961ee17000083862a50aa471a940012e3000033e58aad2000481680c6d65735b28001322f236808875adde70e0470f400094b0002de70cc41b8000000b38e1b000359c21044e700d8d00000000003d760008417b1ecfc0000006930001e982872a98d3ab0d20a625ca720000000003d7c66077e0000001677548acd99aae1373ab268e312f7c1160f11036f03602b97c70ed90000221e50cd0c288003917226f557128435d1c017347656f847b3804641e40add3a7410e353374986965c7741bb979b45cffcb1495b21a1c092a7842c9b604c61d093c40000ed3b7d31cd1b4000a1f8003603f3400000039c5ae912b5c7c8d8c42f53ccf0e42513519c1a811a00042e81d80006ab0002b52a5c8f144979ca64013aa34f2834f3c04b631abda58a50633b9525b9125a14ba01a3722d013d8c74caaae83e41880017070002b6240068ca4844cb59a8ea37f014f081a7b259e027d924b0a0f20c0000cf9a7a8cd6df08d7612807450e716561fcc54e349f37b016ba5270cf641a57951711e6220b0cbfc41a2f505a4a56b2a4d81734cc300736883f45f68a47428fb015324e767090544c0d0000000d6901c0100030b010535130204051400052d2b0118010300070001000007080606000904001f00074a01020b04230609050011071600000c04151d1b01000300190a00030026008d000004064e00030d19030001150004022b030c1e030103010e05040100000b00090b0a44000020
def f191d10 (i : Nat) : Nat := 0xa9c30ffd40
def f191l10 : Packing := (1,1,5,0,0,0,0,f191d10)
def f191h10 (i : Nat) : Nat := 0x3c424f920021b001d583aa2e0eebca85fb4185eb0009798f445e322800d9498685297b400475c2d269938187b33061726400200a3400099da5a00075301000000026732c9655e88170a00156411c25001e2
def f191levels : Nat → Packing
  | 6 => f191l6
  | 7 => f191l7
  | 8 => f191l8
  | 9 => f191l9
  | 10 => f191l10
  | _ => emptyPacking
def f191index : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 2 6 2 7 3 0 f191h7
  | 8 => lookupWord 26 94 6 11 7 0 f191h8
  | 9 => lookupWord 108 381 8 13 9 0 f191h9
  | 10 => lookupWord 16 57 5 10 6 0 f191h10
  | _ => fun _ => none
def f191 : Forest := ⟨191,10,fun i => f191S[i]?.getD (0,0),f191C,f191A,f191levels,f191index⟩
def f191c6 : List (Nat × Nat × Nat) := [(0,5,7)]
def f191c7 : List (Nat × Nat × Nat) := [(0,24,7),(24,3,7),(27,24,8),(51,24,8),(75,1,8)]
def f191c8 : List (Nat × Nat × Nat) := [(0,2,7),(2,24,8),(26,24,8),(50,24,8),(74,24,8),(98,24,8),(122,24,8),(146,8,8),(154,24,9),(178,24,9),(202,24,9),(226,24,9),(250,24,9),(274,24,9),(298,19,9)]
def f191c9 : List (Nat × Nat × Nat) := [(0,18,8),(18,24,9),(42,4,9)]
def f191c10 : List (Nat × Nat × Nat) := [(0,1,8)]
def f319S : Array (Bits × Bits) := #[(0x9d1dc550dca6770db27eae90123930a260858f228c9387020171efa4d359059403a4c2b58522de1b674099782443a4bdd9b8c0aa25cb67265ccaa76c7885c35c872747715437299dc36c9faba4048e4c28982163c8a324e1c0805c7be934d641,0x39194040948746098000a80010c60188a100ad08008083000160e680d111048002140011812040000400081808412098410a1000000224440442895c3084c008844e4650102521d18260002a000431806228402b42002020c0005839a0344441),(0x96d2397c5870bf652ac32178e804040101e30b23cdf82c8d48b250e06a06dbf0618670c4402a80270f973363e8ea47d70cc43af0d67a1a18273770a6e0ff8b6d74a5b48e5f161c2fd94ab0c85e3a0101004078c2c8f37e0b23522c94381a81b6,0x8442190c0860910468c3003009312c740caf50c3cd782c89489210602204110065c02140400a80e189903565240a03458ac00ab0d4598b1803346082c07a2ba46921108643021824411a30c00c024c4b1d032bd430f35e0b2252248418088104),(0x2bfa30cee1550c36abb6797aaa8484010162504c61813ad785c80015cdafce74f207dc3a32c408047c15caaadb88b2f8604457d8e984702e8c699cc886fb05c5decafe8c33b855430daaed9e5eaaa121004058941318604eb5e1720005736bf3,0x2a8820806101043203347b47b24cd28bd2500e3c2081121681480015cdaace501807d432b3644600442d8202d9c030b80105104d2180602694088c4804810441928aa208201840410c80cd1ed1ec9334a2f494038f08204485a0520005736ab3),(0xe98e5a6523fba8cbe01854063bc2c35c020850dd0464d161decc525a867112c994398d8b7ad381a094fa7f8f023d534f1a0b69181c666345cfdc420e27205db2687a63969948feea32f80615018ef0b0d7008214374119345877b31496a19c44,0x140184000702841e0c000000c830104292ce1030444414154804248025100010418018900110028101050d800044206120840100c620b404a804202320441b20840500610001c0a10783000000320c0410a4b3840c111105055201092009440),(0x422b4d3b43ac90d0080c92f58a1121ce42008091880e2b3aab19b84e0c8eb37f062d2f437158af76e1e3250e73aa67a181398b837bc944ed2298b7403b4ba62ff3908ad34ed0eb2434020324bd628448739080202462038aceaac66e138323ac,0x2205bb63089180080c03958338fe7356d312f4880a283aaa1918060c8eb37400230e421a049f47e1e32506d2aa0d2180918183521140bba0281481800b2e05730008816ed8c22460020300e560ce3f9cd5b4c4bd22028a0eaa8646018323ac),(0x15a3a79bc40a4edb15e54ff1ce281820bc142401b709101dfc03052f31d4a50a4841f5f9a41ef86801f1d4333734887a66c04c77db55af92f3815c71cc026593a00568e9e6f10293b6c57953fc738a06082f0509006dc244077f00c14bcc7529,0x482011b4340084008c007f10e1940744cfe521787091005fc03012f00c480081148c1a0240fb8685060542227b0896606c4cc540b450912d18110228c1007a32001208046d0d00210023001fc4386501d133f9485e1c244017f00c04bc03120),(0x0,0x0),(0x0,0x0),(0x2424bb8fa086d690c517d88f55424a109c1820007268e41a73162e91ed803b03e8f32a664d2d62f5a00fd28159150cab3e4a2657363a8cb5654ec89f458b7c4fe589092ee3e821b5a43145f623d5509284270608001c9a39069cc58ba47b600e,0x2824a284bc8606b00016700c5164be8b92010ce87020a41a03142c90ed003b02c823281459204395a80ba20108023489281222033018840c244809954103284cd78a0928a12f2181ac00059c0314592fa2e480433a1c08290680c50b243b400e)]
def f319C : IndexTree ColumnInfo := (IndexTree.fork 10 (IndexTree.fork 5 (IndexTree.leaf [(304,0,15,0,4),(296,0,23,0,4),(292,0,27,0,4),(290,0,29,0,4),(289,0,30,0,4)]) (IndexTree.leaf [(288,0,31,0,7),(288,0,1055,0,7),(280,0,39,0,4),(262,0,57,0,4),(257,32,30,0,4)])) (IndexTree.fork 5 (IndexTree.leaf [(40,256,23,0,4),(38,0,281,0,4),(18,0,301,0,5),(14,0,305,0,4),(10,4,305,0,4)]) (IndexTree.fork 3 (IndexTree.leaf [(7,0,312,0,4),(6,0,313,0,7),(6,0,1337,0,7)]) (IndexTree.leaf [(5,2,312,0,4),(1,0,318,0,7),(0,0,319,0,11)]))))
def f319A : Array (List Nat) := #[[],[81,130]]
def f319d5 (i : Nat) : Nat := 0xa20dc5b950caa82982813c46d4a8505314c140
def f319l5 : Packing := (2,6,5,0,0,3,0,f319d5)
def f319d6 (i : Nat) : Nat := 0x200040008001000200000038407080006040008213080010000d100120800068400a2d02773698cb24f228ec6212fa75b719ac861af972aa4da592282399b8be501b8c8461e0c8280a00aad6984360440502ba5a210d811014086f6929961d305031b487644844c140ce364d92211305032b596644844c140ccd65591211305033a592644844c140a4f694845c9305029b9a4a20874c140de264d92211305036b196644844c140dcc655912113050379193644844c140de864991211305033b087644844c140d6c21d9121130502f89a2211434c140be46848450d30502d39a5211724c140b6c684845c930502799a424d624c1409f46849358930502739a5261414c140e6c68487505305023b8a8655414c140c6e21d95505305027b0a9605414c140e6c21d8150530502f19a5211314c140b7429d514c530502f90a8505314c140f6421d414c530503d9176505314c140d6c25d414c1105031b087644844c140
def f319l6 : Packing := (36,5,5,0,0,9,0,f319d6)
def f319h6 (i : Nat) : Nat := 0x93b
def f319d7 (i : Nat) : Nat := (if i<1 then 0x1414c540edabb28298a811fd989dc405033bceec1880a067760d7310140bd6c9086202819ee77608405033dae6c1080a063f6197210140ceec1ae420281b9d83508405033eceec0880a067d5d98110140ddab2302202819f5736044050376886c0880a067d5c98110140ddaa1302202813bd94a21305023fd32c3a60a04ef250874c140ade4a10e982811fe9921d30502bbb273ba60a04fb648844c1409fac8908982813f990211305033790e42260a05ed644844c140cdf3b90898281b9d932113050375b2442260a06ed644844c140cde422e6982815f9901cd305023f930b9260a066f211724c1408fe4c2e2982819bc845c53050277930a0a60a066f21d414c140bf4c9080982817f19110130502f732944260a05ee250874c140cfd4410e982819fa9921d305033f32243a60a067e21e774c140becc9cee982817e99221130502fe32242260a06ee21c844c140edc4390898281f999321130503f532442260a05ee644844c140fd8c8908982817d893911305033f10eb9a60a05f6261434c140eec43a8698281f988450d30502fd32421a60a05fc644434c140afc4bb04982817b894609305027f130b9260a057e261724c140edc422e498281dd9435c930502fb126b1260a07e650d424c140afc4bb02982819f88760530502f7128c0a60a04fe261714c140cfc43ae2982815f897545305033f10ea8a60a07e650d414c140bdc4c28298281bb88750530503b710ea0a60a076e5d9414c140bdccaa8298281fb18150530503f628298a60a077621d314c140eecbb262982817d9954c530502fb32898a60a07e6211314c140fccaa26298281fd1614c530503fa2a298a60a07f4505314c1408fecc4ee182813f591a21205023f92ec3240a047f25d83481409de4a306902811fc97619105023f92ec2a20a047f25d83441409de4a30688281db57650510503b68e6a0a20a057e25d3044140fd8a0a60882811fd9720e0050277b2841c00a04fd64483801409fcc8107002811fc985ca00502bf12e98400a047d644839dd408deca510b9a811bc98911735023db24420e6a047d644841cd408fcc810839a811f591a21725023b926c3ac4a04f664c8050540bccc9900a0a811bd989dc4050276d32c0880a066d9dd8110140cdabb30220281ab66660440503368e6c0880a06e58cd8110140cdab930220281ba6226044050366b0b08880a047e25e88101408fccc4ee202813da9960c405033b4eec1880a06e69118310140de4c1b0420281bc983888405037a306c0880a06f86098110140de8c1c22202811bc9421d3050276b2242260a047ea64874c140cdc43908982817b191211305033710f22260a04f6261434c140cec43a8698281b988450d305033b10f19a60a047e261724c140cf443c44982819b88750530503f228298a60a067c21e114c140 else (if i<2 then 0x800000000909080120800010004240c100020060242430604001000400008126100062610000200080000080020c090800100040000800200004001000400100040e1038400108000100034400080020098400060418106041a10982424328841a51103020d0800120848200904000000010000000848200000200000200004041898400003000200001820034022000000000000000000000000000000103fd02430004180010482000800000040e0d008c00106830412288800191791290d9089038f58e78d98cb8c68c18bc8ae8a089288d88887a87587086b86686185c85785284d84884383e83983482f82a8258178098047f67e87e37de7d97d47cf7ca7c57c07bb7b67b17ac7a77a279478678177c76e76075b74d73f73172371571070b7067016fc6f76f26ed6d66d16ba6b56b06ab6a66a169c68e68067266d65f65164c63562761960b6065ef5ea5e55d75d25cd5c85c35be5b95a259d58f58a57c56e5575495445245165084fa4f54e74e24d44c64b84b34a549749248d47f47145a44c43e43942b41d41840a3fc3ee3e03d23c43b63b13a339e39037936b35d35834a3453403323243163082e82da2c32b52a72a229d28f28127c26e26926425f25a24c24724223d22f22121c2172092041ff1f11ec1de1d01c21bd1b81b319c19718017b16415f15a15515014b14614113c13713212d12812311e11911410f10a1051000fb0f60e80c80ba0a309508708207d07806a04a03c02500e0009fac89073ba81bb984602775033bb0641ceea057d644839dd408fec81073ba811fc9760e445027f32041c88a056f652885cd40aeec9d10b9a811fd94a217350337b29442e6a047f262445cd408fec810839a815dd939dd435023f92f44086a047f6627710d40d76c330421a819ee77608435033dae6c1086a06bd6198110d40dbac2b0221a81be582604435033eceec0886a067d5cd8110d40df4c130021a81bf181600435023fd3243c66a047f261738cd408fe4bb0519a811fc97606335023f92ec0466a04fd646885c9408fec8510b92813dc9361d625023fb2643ac4a047f65c83589409deca106b12813f59120d625027f32041ac4a04fe64288509409ee49b0ca12812fd9620d425026fb2a41a84a04fd64483509408fe4bb0c992813ec98509325023fb27442e2a053f658435c540abeca886b8a815ed9210d715023f93119ae2a047f64c87585408fecb906b0a8137d9520d6150277b2841ac2a04fe64083585408fec990ea8a811fd9720d5150277b2841aa2a04fe64083545409beca906a0a816bd9610d41502e7b2a21a82a05eb6484350540b9eca906a0a817b99020d41502b7b2c39a82a066f6147350540ade4bac6a0a813ed92a21315023f92ec3262a047f25d854c540cde43aa898a815f49758531502be92ea8a62a04fd26 else 0x2000800200080000004001000400698400000000000000000000001080420000400100000000000000000002100040000840010030209083020908302000000000012058811106880000000060418102040000800200902440c0810200080121210))
def f319l7 : Packing := (236,4,5,0,0,12,0,f319d7)
def f319h7 (i : Nat) : Nat := 0xb18da001550e818f722f5a415980b6e2c004595be78089307f0c000af14dc9d8520f28c01bb20600007bb55ca50005b1810003955a2443cda1913e6036378860aa88000001c32590e7496a400381a45000a81a9fa3f02e4c028103004150488058a00008410b
def f319d8 (i : Nat) : Nat := (if i<2 then (if i<1 then 0xa774c140ff8844c140ffa444c140ff9734c140ff8734c140ff9434c140ff8434c140ffa334c140ff9824c140ff9724c140ff9624c140ff9424c140ff9324c140ff9814c140ff9714c140ff9614c140ff9514c140ff9414c140ff9314c140dfe770c140bfd840c140dfd730c140bfd820c140bfd810c140ff9300c140bfe8848140dfe7748140bfd8648140dfd7648140dfd7548140bfc8448140fbd5448140bfd8348140bfc8348140dfd7348140fed6248140fed5248140fed4248140ff93048140bfe8844140dfe7744140bfd8644140dfd7644140bfd8544140dfd7544140bfc8444140fbd5444140bfd8344140bfc8344140dfd7344140dfc7344140ff55144140ff54144140ff93044140dfe7780140bfc8480140bfc8380140dfd7380140dfc7380140dfd7280140ff93080140dbd849dd409fd839dd409fc839dd409fd829dd409fd819dd409fd809dd40df9809dd40bf98091140dbc8791140dbe7791140bbd8191140fb980911409fe885cd40dbe445cd40ddd731cd409fe881cd409fc841cd40dbe441cd409fd821cd409fd811cd40df9801cd409fc8750d40ddc7350d40bf88050d40bed8210d40bf58110d409fd878cd409fc878cd40ddd738cd40ddc738cd40bf8808cd40ddd878cd40ddc878cd40dde778cd40f9e448cd40fd8808cd409fe885c940dbe445c9409fc835c940dde335c9409fd87589409fc8758940bf880509409fd874c9409fc874c940dee7788940ded7688940eee6688940fae4488940ded7388940dec7388940fce33889409fe885c540cfe665c540dbe445c5409fc835c540dde335c5409fd87585409fc87585409fd87545409fc8754540bf88050540bbe8850540dbe7750540dbd7650540ebe6650540bbd8550540dbc7350540f9e3350540fb880505409fd874c5409fc874c540fb5414c540df67784540df57684540ef66684540df57584540f765584540fb55484540fb64484540df57384540df47384540fd63384540bdd8310140bed8210140bf58110140dbe7710140dbc7310140f9e3310140dbd7210140fae2210140bbd8110140fb61110140bfa8810140dfa7710140fba4410140bf98310140fd98310140fda3310140fe98210140fea2210140ff18110140ff211101409fd874c1409fc874c140bbc844c140ddc734c140bfa884c140bf8874c140df8874c140dfa774c140bf8844c140fb8844c140fba444c140df8734c140fd8734c140fd9434c140fda334c140df9724c140fea224c140fb9414c140fd9314c140ff2114c140fd9300c140bbc8448140bbc8444140fb541441409fc8780140df88780140dfa7780140bf88480140fba4480140bf98380140df97380140df87380140fda3380140df97280140fea2280140df97180140fb94180140ff21180140bb58110140bd983101409f8874c140 else 0xa3a51027593589724ac24b92488ea450219909882240c1ff8fe87ca3e01e98f187823941b78d0867a3381998cb865232418f8c6862a3101858c186022fc17b8bc85da2c013d8918482234103876839a1c00dd86b83521a40cf864830a1780b1855829214409f84c823a0f007183581920c405b82a813a09804181f80e205c02b812807a000fbd849dd40bfd839dd40bfc839dd40bfd829dd40bfd819dd40ff9809dd40dfd849dd40dfd839dd40dfc839dd40dfd829dd40dfd819dd40dfd809dd40dfc8791140dfe7791140bfd8391140bfc8391140bfd8291140bfd8191140bfd8091140bfe885cd40dfe775cd40dfe885cd40dfe445cd40dfd825cd40dfd815cd40bfe881cd40dfe771cd40bfc841cd40dfd731cd40bfd821cd40bfd811cd40ff9801cd40dfd801cd40bfe8850d40dfe7750d40dfd7350d40bfe8810d40dfe7710d40dfd7310d40bfd8210d40fed8210d40bfd8110d40ff58110d40ff98010d40bfd878cd40bfc878cd40dfc878cd40dfe778cd40bfd848cd40bfc848cd40dfd738cd40bfd828cd40bfd818cd40bfd808cd40ff8808cd40bfe885c940dfe775c940dfd765c940bfc835c940dfd735c940dfe445c940dfd435c940bfe8858940bfd8758940bfc8758940dfe7758940bfc8458940bfc8358940dfd7358940bfe8850940dfe7750940bfd8650940dfd7650940bfc8350940dfd7350940fbd4350940bfe884c940bfd874c940bfc874c940dfe774c940bfd864c940dfd764c940bfd844c940bfc844c940dfd734c940fed624c940fed424c940bfe885c540dfe775c540dfd765c540dfd755c540bfc835c540dfd735c540dfc735c540dfd645c540dfe445c540dfc835c540dfd635c540dfd435c540dfc435c540dfe335c540bfe8858540bfd8758540bfc8758540dfe7758540bfc8458540bfc8358540dfd7358540bfe8854540bfd8754540bfc8754540dfe7754540bfc8454540bfc8354540dfd7354540dfc7354540bfe8850540dfe7750540bfd8650540dfd7650540bfd8550540dfd7550540fbd6450540fbd5450540fbe4450540bfc8350540dfd7350540dfc7350540fbd4350540fbc4350540fbe7750540fbd7650540fbd7550540fbc8350540fbd7350540fbc7350540fbd6350540fbe3350540bfe884c540bfd874c540bfc874c540dfe774c540bfd864c540dfd764c540bfd854c540dfd754c540bfd844c540bfc844c540fbd544c540dfd734c540ff5614c540ff5514c540ff5414c540dfe7710140bfd8310140dfd7310140fbc4310140bfd8210140dfd7210140fbd4210140bfd8110140bfe884c140bfc874c140dfc874c140dfe774c140bfd844c140bfc844c140fbc844c140dfd734c140dfc734c140fdd434c140dfd724c140dfd714c140fbd414c140fdd314c140ff8404c140ffa884c140ff8874c140ff) else (if i<3 then 0x494c0613221a312133018244485221a22509289088c442007080244841c1e20e0c10204304840e10001c201308000e1130872808482a024230125118004044c400013100044c00400108384002260220e5110728882821c10d0a884014100604354440000383441a2420108007880a44386144a6030f4591187c8884c28b2220e3010098083e4444a222250898888c03a446001e203121051288283d146121090f109844826024201301488788480444a122130984808000108384124c0461e11308204483828241c3c04e0e1a023020e10681890c3400400100060c1820618260100451230485070389019d1820000f0118680080421a1c20d1210380868c4c3848241ca0005070086902804384880a201a0240a0e0c1312090f0444304042121424261c50145501fa06182013084850787111a4040e1a0234690102880705104c20086010030e185098486921824a8a2002182021004850789111828c1070d011a30414082862610063011210589818c08c146087082348911a40426241230d0a34808020042430a13090d20708890e1824a8a20128404a8a204304042007000c091228004870910001c3c2448a000000000000000000000090a0e12032848909fa05070006a024004bd01f40c0460a305070086951834280038a8c10008118200011821c14608928894428c10004c2262420e13070c002800618200100986182021043280810c186501004c2001000cf40e070a0d3e93b483a34d0fe82b3fb9f8cf9e7bb3c39d4ce7e70b37b9b0cd1e63b2e396ccafe54b28b940c99e49b233904c7fe3eb1cb8d0c65e2fb153894c47e1cb0cb860c25e11b06382cc13e04b00b800bf9df7afb37d4bdfdeaaf1b780bb9dd5ae73724b87dbeadbb6c8b59dabad33694b3bd98acab640b15d83abf35e4ae3d6cab4b5a0ac5d5faac354caa3d4caa4b520a85d3da9c34cca5bd28a93b488a3dd1da8c344ca1fd0ca83b410a05cfda7e33dc9e3ceca75b3a09c5ce1a6d335499bcc8a61b2f896dcb1a56329493bc98a49b238911c81a3e31d48dbc68a31b1788b1c55a27312488bc44a1eb0e085dc27a10306482fc12a06b028805bff9ff2fec7f3bf49f7afa87cdbe19ef2f747b7bd89ebaf507a5bd19e72f2c78bbc29deaed8765bad9d62e9c747b9e9ceae6872db939c72e24707b809beade86edb759b92dc46dbb689b3ad986c9b5f9ad2d5c6a3b4a9a1acf066db339972ca4647b1e98cac58621b099822bfc5f3af2977aba85cdae396f2b645a7ace964ab18581abf95f2aec56fab0956aaa854da979482a2c507a7e93da9d04e1a6d93529944aba52928a928489a4191e28dc45fa24911a888431a0f90327d43e39ee8f1a7703b19d58ea274438f9c28dda6d83599a58d226743279908c5a6283119858c126042ef9748b8a5a82cd95f8ac254c29794a8 else 0x11820e10108107083c4848c10000a2151080002000080843cc041e60243003840420e102885442261530110001c1a20d121001c2080e204011004c94c06a61007068801824200094c0426100084044c400008988044c4024a60301087843a443c64a8d223300111848883c3041c0f203020a112980801404201812808c280841e10e0f10509882841146026020e1011807480c343846010070688282141a8a30e13100383444a100786080c4844a8c24625118008a44c0404600107840140221207109040420614225080280c40012510501880c2440130848188002604a3090310084890c10304062420a1310506228c244c412182259046192a2848c4830402602910c1090608c04a40618242910c1219848a30cc0244241823091106890a40260241a30d121180401b222430a3010522c886902))
def f319l8 : Packing := (383,3,5,0,0,13,0,f319d8)
def f319h8 (i : Nat) : Nat := 0xa5f29dc00076be60cda67a200075b8001e230387b8df540000a3cc151b714349161d7c6317badaf44675c60a000e6b21eb64f3bb0c68001e07d2ca576f83b7e000c2380000013ad0006dd4198564ec38489e1853d2b449172ac1be284a5eb8ec4a5f29fccaaa1c1f00035e2bbb2670001e6e6834b90c9d834ba436a0d4ecaf40990f08cc45f6c1530e40f9872163454699b50000000d2b800062df534d44727a3f7b212d1f6a881f4e43759f00008d8cd8c0dfafe0000006e0253061c51b6664000000b84000328f784f14800f65000035b2c4bb2a000821000243decf0005d37322000ae9800354476d2102f28228a1dc224d97a2bc4815d7aec000000000000287874b5000a64000b610055ad0cd3430c532762a8c0000002898000fc509a0d62bc3d8900008b9ede90db9cc44e7c98353610ef00b7a550bb0eb987c000b4b959ceb52713956931205d9c594edf03bffc8e280f0db8f478c10ba4382441a254ebac8ad2581f4d1041d1492e5ae9ee68764ad099a827a91c653ccf37cbfd8c21a3af1bcdb3f58e00041556d99081939a5b9a1b19ea7c000cd5000000000019878e80032cc4cb307e76c00130a00000000000000002480d8d5256673152f2c0006c40e0c0019ea01d888ff3558a497879ff0ac110000000556e939c36e5ed88000f26a10d6c66962ad9d8af3c000760562c0fac87ea26ae0000b81ed2226a89f970cc94183a62eafd696dcc7b3aa794a052234fe8f8f14530000aac4acc9762d8b7e9c74f94ee95ebbd84e5123c42c35680000000000001c3a0503777120000001c9bd0dd77aedc5dcdf441a0001b52000217073a551ee81f8e0320004b900033670025407c00c920008d06254909706e83a97820150008c61070400132d40c70000c518800408201004600016310900b2c00440864633040d83c41000430034c000400700d10504358604e00001a00000430e6c101400bc0000319218018108020804b180
def f319d9 (i : Nat) : Nat := 0x963136144a1d2b0a04c0192c661448287134a0580d3c526958500e614389a502c069c50e26940b01a71c96311208263831128e269629128e269628d2264b1888c193141889419324188949924b188949134b146913000e304922664ac235120a123891328e4b148912c52231e112b0242499c985e8463513740d168132f40a42351293e81480e0e286a3a068b408147462248a44414946224264a3112452222610018d4441a293a04a3b3ba66c978d10c9fe3db766e2dae342634bc96529b4d892d11a023d06c8c195b2663d86a8b41422002f84c0800d010800ffceea07fe44503feb9a81ff1cd40ffa86a07fc43503ff19a81ff5c940ffac4a07fd42503fe99281ff5c540ffac2a07fd51503fea0a81ff4c540ff880a07fd30503fe18281ff48140ffa20a07fe00502ff3ba81ef91140bfae6a05fc73503ef19a817f5c940fdc44a05fd71503dea0a81fd84540f7880a07f840503fc98281fe80140
def f319l9 : Packing := (36,2,5,0,0,11,0,f319d9)
def f319h9 (i : Nat) : Nat := (if i<1 then 0x40000001a0c0000000ea4c0000000000c3d00000002b130000000000184aada54d03c1b0110ce8e7d2d70aa23815f3781f2c85bab7ad36c47d1b4d6113020e993200fa0f570feedc000084e12c10fc32b2d544d14000828deef5b576a3f4d0f63f297c6b9dace41e3c400000036f89d9ce0d8c3e11e000086a5d79ca07a49618ea9b271f3daec5505e2fa0a4712328b4f6d68e40007b30000994312c50d5756d27233199d5c0428a1687781b2ce6854c133c70000dc0e6790000000000126e00011750000cf0a194ac0137a47691166b6880d68d14d94fa893bcedd465047d49d649b8430e1b1f4c5cdb3c4488a5333878c86880001af790eee6639dcc0200002bbdbd8000ad45a7a40aa26dc44c000cac124d22c80008af9214e2fe768fb6911fd8f00000000e6168e9cfee25eacba85b716551800000000006ab00008bc06964d5e155f5816570000000e870000491775a00020290cb4000651c000ad84a247d64000000022200018190001056ab1c9384a30000000390a0000f3d0000000bd0a007a119522ec1f1575a82c2c1412ce00b486174a14cafb8d52f562ebe9d6896a9b7266c439a28834912ed5600003529adea3d9b65b250bf3766a4032332cfbee9ca3a65c000145e0af145988ab901abb5d2519e10d12a57921cdf0e9ae100f62cbce778699e31b44a6a0bcd0ce04f8b8b50a4a8220c86beee2586a821d50d28bc22477922fa8003ade028507a085a272a13c8000033fc0000003ce76800000b87c000000000000002a94b07e4f1b7b85dc41c0003bf994b718400000036b8f45a0f200033710d38000000133c7278f6fda2ce7e0000000a29bc51c3f4000c9a8000c0daf488ac6f7b3df6684f9db12dd30fc4494e7c554ca5ecd0002690ddab509849bcc4a1a0b36c46ad184977f0db97bec65af474ce8bde3192d92aa090beaf89f182b6168656fd4e32c9cb836ce1488150001e43f3aaec2da9323fa3068698caaa8f994c0009b4020adc7d74a00032b900003760001c1664d735d400cd1d7c4ae1b818b5141b7623b534ee30dcfc000fb6caf100000000002c0541332a89b873793b8ca37a125b006d9000028d0340d13c000c3b0000592dc91000163efd1b52f00036861c14000ac38000d88fb22000272422d474b5d96adf05ebb7514080004de8000787509b0000000983f05f0864000a2300008824000000008e0a10697002c0000d25085001400c04d0c82143400b20181000800002741c003142011d006a38104181814464480001c08f0a0029702401801c201092e08805140411500043810600002181c48710004030000003148010126346005600002742008b0a0011e1009b0200000855400000000000a02401000230198002410932001280409303203031e0050483084c0000050a81022470d0220203000000a066060a else 0xe81c529a7b29bcb6e181c89d7d275051b10000dceec64fd6e755fb4570c89688ad4b818bd3b2a91c5befad8ebfc0003dce96d00014a20003659827db214ad7463f37ee2b13e01449b5fb60f2cf71dd14309a4b89b33489e62c7bf5eec545df1845bace93d3fe54c8a5ab2142069e70cc000d98b27f0dfbf1053a28416ddeabf42ed2c9159ba46e8040002a0f260b9b3cbe2c106647dd07416ba943da3de2700002b2f82ac69963e4221b2600f3000129735d3b4d0000673cb93057d9114589dc0cfb283ad2b1508eb4c4cf4ef197c000f060ca86b9d6e50000000359e6bac8e08ae9cd1120ec2d3728c240004c68a400c9840605ef6c8cb5a4a9487bcaaf930e6858d9ac3616d0c0339bd1539d375ff89b302829d8a4250dcd20002a72904a6d424c)
def f319d10 (i : Nat) : Nat := 0xc88bfd40
def f319l10 : Packing := (1,1,5,0,0,0,0,f319d10)
def f319h10 (i : Nat) : Nat := 0x8300000113e60cd532bd2f6a0009a1070000000000034384619010ae689701f852226c0730786acddd9bc001a5000dbe0018235c7b4b60000005860003180078e066a66d20000006da08c21716f045750a00268bd669294c00000534002310ce1142023752022902300
def f319levels : Nat → Packing
  | 5 => f319l5
  | 6 => f319l6
  | 7 => f319l7
  | 8 => f319l8
  | 9 => f319l9
  | 10 => f319l10
  | _ => emptyPacking
def f319index : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 3 0 6 1 1 f319h6
  | 7 => lookupWord 19 66 6 11 6 1 f319h7
  | 8 => lookupWord 109 386 6 13 8 1 f319h8
  | 9 => lookupWord 186 658 7 14 9 1 f319h9
  | 10 => lookupWord 19 71 4 11 6 1 f319h10
  | _ => fun _ => none
def f319 : Forest := ⟨319,10,fun i => f319S[i]?.getD (0,0),f319C,f319A,f319levels,f319index⟩
def f319c5 : List (Nat × Nat × Nat) := [(0,2,6)]
def f319c6 : List (Nat × Nat × Nat) := [(0,1,6),(1,24,7),(25,11,7)]
def f319c7 : List (Nat × Nat × Nat) := [(0,24,7),(24,21,7),(45,24,8),(69,24,8),(93,24,8),(117,24,8),(141,24,8),(165,24,8),(189,24,8),(213,23,8)]
def f319c8 : List (Nat × Nat × Nat) := [(0,3,7),(3,24,8),(27,24,8),(51,24,8),(75,24,8),(99,24,8),(123,21,8),(144,24,9),(168,24,9),(192,24,9),(216,24,9),(240,24,9),(264,24,9),(288,24,9),(312,24,9),(336,24,9),(360,23,9)]
def f319c9 : List (Nat × Nat × Nat) := [(0,14,8),(14,22,9)]
def f319c10 : List (Nat × Nat × Nat) := [(0,1,8)]
def f351S : Array (Bits × Bits) := #[(0x7b0c1ace37e6fd2090969605c00c4488202407df3b1cda89270d681fc0201357a664381809a5b172a4ef25e2f43bdd323f745dae2648ba42a03f98424b85fe32701ec306b38df9bf482425a58170031122080901f7cec736a249c35a07f0080,0x7184584c67a09c62809e934c5f03c899c04e116639145a892708600f40200394a410210801252102006e090230021c80393015ae066890428031106541c52c02401c61161319e82718a027a4d317c0f226701384598e4516a249c21803d0080),(0x98e00b789a2e966c7c0ec1cb06d40447010bf0ac6874e186488d3b2f4920c6a6b5d562506562e46c9d44897183f1e69342726e7482307c187ce56699ae716b0fb1263802de268ba59b1f03b072c1b50111c042fc2b1a1d386192234ecbd24831,0x90602a481104142010000081200d031002cb1448002480024889310d092084862520604a2240240c0940086100e4c013442004000810601004806010a040080f0124180a920441050804000020480340c400b2c5120009200092224c43424821),(0xc4edcac67643930b12c6d53e9217208301288501a6d93604a046228ea6eada91bf99d79ddd6114627724d3a8741009c42a0873fa50318b896ebe107825a5a779ceb13b72b19d90e4c2c4b1b54fa485c820c04a214069b64d81281188a3a9bab6,0x408e01056601c20a4a82802e11b2f4e7f5346ab1a0d9360480460282a2ca5a01989915b09510007026a4d28824121a848b08e2d960208acd683d116001a5a770ce902380415980708292a0a00b846cbd39fd4d1aac68364d81201180a0a8b296),(0x712f54d4c80019b586e17e31f40b31b03ca40f020f0313f221eb045115eb255acb8e188e38e330b0e9fb47c97cdd612dee1b3c07c928403ba28284734dced04071dc4bd5353200066d61b85f8c7d02cc6c0f2903c083c0c4fc887ac114457ac9,0x33006408808015584415410e04409080ac385060f0201e021090401142024404206000c00221000004a010148c14129341300060008200202820416460048003040cc019022020055611055043811024202b0e14183c0807808424100450809),(0x1556b428691474abd5a220684800d018a680025390cc8a6b909c5dd48059eb017468a903b9cd4ac75219786f4cbe19998423efeb23cdd5dedd78895d89d095896ec555ad0a1a451d2af568881a1200340629a00094e433229ae427177520167a,0x9042b0202185502841a20042080bc27661381ae9904c8a03008459d40059c902342895430dc904c75201084c843610168020eca107015059d570a8490882a50d42a410ac080861540a106880108202f09d984e06ba64132280c0211675001672),(0x0,0x0),(0x6ec06537bcc18145e1395ea483e00a0440513080089c64e17f45c9b036d41800d807a6608f16b38a24158b068be05374d9e5b29c9497f6d27ff8db6dd39c14b6f89bb0194def306051784e57a920f8028110144c20022719385fd1726c0db506,0x4f80453328e1814d6020522482708c8e5c20ab36089864e0374448b016d00041900f82040c160103203223068a0013049051b21481028e827a0e814d439c10c02253e0114cca38605358081489209c232397082acd822619380dd1122c05b400),(0x0,0x0),(0xea0aa04f74c1993003773bcf69280b2058540801716b961d8fa0810c33151cda27328cf213964b34f2c38c351712ecf05985c49c5ceb8377d5593642f86ac2b28dba82a813dd30664c00ddcef3da4a02c8161502005c5ae58763e820430cc547,0xb00ab80c561410020184294a018b7271a11c50c97061921d88a0810c2105183e21200df213884a78d081802035322cd0490c44881ca1017504412200b863002a89ac02ae031585040080610a528062dc9c684714325c18648762282043084146)]
def f351C : IndexTree ColumnInfo := (IndexTree.fork 10 (IndexTree.fork 5 (IndexTree.leaf [(328,0,23,0,4),(324,0,27,0,4),(322,0,29,0,4),(320,0,31,0,7),(320,0,1055,0,7)]) (IndexTree.leaf [(273,0,78,0,4),(258,64,29,0,4),(72,256,23,0,4),(70,0,281,0,4),(25,0,326,0,4)])) (IndexTree.fork 5 (IndexTree.leaf [(21,0,330,0,4),(19,0,332,0,4),(18,1,332,0,4),(17,0,334,0,7),(12,0,339,0,5)]) (IndexTree.leaf [(9,16,326,0,4),(4,0,347,0,8),(4,0,1371,0,8),(2,0,349,0,7),(2,0,1373,0,7)])))
def f351A : Array (List Nat) := #[[],[64,49,134]]
def f351d6 (i : Nat) : Nat := 0x3f8092505314c140
def f351l6 : Packing := (1,5,5,0,0,0,0,f351d6)
def f351d7 (i : Nat) : Nat := 0x42000000038400608018106041810683040c0d0ce4744c23fbd3ab3b12a27a09992870047f64a885d5408fec8906baa811fd9120d725026fb2b442c2a04fb64a884c5408fe4c2ea98a819ed8720931503f912498a60a07f4585314c140fe898a429828117d9520d725023f321442e2a047e261764c1408fc4c2ea982811f8985c93050277130a0a60a07e4505314c140
def f351l7 : Packing := (17,4,5,0,0,8,0,f351d7)
def f351h7 (i : Nat) : Nat := 0x1f
def f351d8 (i : Nat) : Nat := 0x105103808818044040a20784021c203810c10304050820205103010818084141840210602894020c461430691120f0c285043c2830618172232307100030814304100a200382918c1c1440c0a206081060288302044610c081048400200881e3070f106468a34212880e3098d104c6a88790263441e0c1830e0d000f20605091021e1400312060f19184018162440a20438002c688103010718686038c3818420021830c091098608003c5081230808c208408210204408605123441e182448d1224688302891a20c0d0f1c68609123459cb2ee48c6785afcde4b9f6ead2d90b075baacd4ca5f40a7acd897729a48c7c8cf18a22c30837019f8bdc79eee9d6ba0706db9acb4c65ec697aae0586a7944a7c4be9091aa30436839009e43ae6e8ce9882d6558a092c23e448869001f63b8748dc1ae3285e8a81261f83485c08e0a80a800bfe8854940dfd625c540dfd525c540bfe8858540dfd7358540dfd7258540efd6258540dfd7158540bfe8854540dfd7354540dfd7254540f7d5254540dfd7154540bfe884c540dfd874c540bfd854c540dfd754c540fec824c540dfd724c540dfd714c540ff5614c540bfd850c540bfd820c540bfe8848540dfd8748540bfd8648540dfd7648540bfd8548540dfd7548540bfd8348540dfd7348540fed5248540dfd7148540ff53148540ff9634c140ff9534c140ff9624c140ff9524c140ff9324c140ff9614c140ff9514c140ff9314c140ff9214c1409fe885d5409fc835d5409fe885c940d7e555c9409fc835c9409fd8754940ded7588940f6e55889409fe885c540cfe665c540d7e555c5409fc835c540dee225c5409fd8758540cfd76585409fd87545409fd874c5409fd870c540bf9800c5409fd8748540df57184540df57684540ef66684540df57584540f765584540df57384540fd63384540df57284540fe62284540bfa884c140df9764c140efa664c140df9754c140f7a554c140fda334c140df9724c140fea224c140fb9414c140fd9314c140ff2114c140
def f351l8 : Packing := (83,3,5,0,0,11,0,f351d8)
def f351h8 (i : Nat) : Nat := 0x71fec000000010d00000a140052446c2dc28200094203002a1b3e0e5a960003a900184512c
def f351d9 (i : Nat) : Nat := 0x61a2c8890934e1c68a121269830d142424d3231a442cd28d123068c88d121669898a128c6cd187204a88f1a3021c24d112063c88c8834e46688851063620b1e7084a68c4d119106960f781b16256f5010a350c122c7810828003fea9281ff58540ffaa2a07fd31503fe18a81ff48540ffc22a05fd75503bf2aa817f5c940fdc44a05fd71503fb08a81fe4c140
def f351l9 : Packing := (14,2,5,0,0,10,0,f351d9)
def f351h9 (i : Nat) : Nat := 0x36af2df16a9bc49c98c41f7e00020f47483400152f4a4d69b04000001f78063a73047884d9c76238a77d743427e1827d724c7158557306d86ef60e5e959600000e5937b42a309a4379b307c92e45669198582022f5d29eb5fd10430136b1a89523200181f189da2b2989cb3c68db03c3c8a2001f70c02000000e1692a000a4df0af4ab34d33180077e4ea5d43ab1271c224c1cf86250855e1080b8612866a0c06296064667c0862179287e000a36000000000a52a8f60c85a00045600000000000161400074909187bc38228b23119f44001f9000174000115243e00000001200180280478b05040830e2800600244804e044000460004142000104a02160e082920061302
def f351d10 (i : Nat) : Nat := 0x88868ffd40
def f351l10 : Packing := (1,1,5,0,0,0,0,f351d10)
def f351h10 (i : Nat) : Nat := 0x7bb1c36261064e2c0000002d0001e00125e1a615557e2d800375a500660009d000039a39b8d51e010020
def f351levels : Nat → Packing
  | 6 => f351l6
  | 7 => f351l7
  | 8 => f351l8
  | 9 => f351l9
  | 10 => f351l10
  | _ => emptyPacking
def f351index : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 2 0 5 0 1 f351h7
  | 8 => lookupWord 8 28 2 10 5 1 f351h8
  | 9 => lookupWord 43 149 7 12 7 1 f351h9
  | 10 => lookupWord 10 34 3 9 4 1 f351h10
  | _ => fun _ => none
def f351 : Forest := ⟨351,10,fun i => f351S[i]?.getD (0,0),f351C,f351A,f351levels,f351index⟩
def f351c6 : List (Nat × Nat × Nat) := [(0,1,7)]
def f351c7 : List (Nat × Nat × Nat) := [(0,7,7),(7,10,8)]
def f351c8 : List (Nat × Nat × Nat) := [(0,24,8),(24,16,8),(40,24,9),(64,19,9)]
def f351c9 : List (Nat × Nat × Nat) := [(0,7,8),(7,7,9)]
def f351c10 : List (Nat × Nat × Nat) := [(0,1,8)]
def f383S : Array (Bits × Bits) := #[(0x45d1830271014506932243be8409db65144e962aa6c1511945835860040800cf330d6c5fac0892681c6791daaf60a50a4519e2c1190f5cd281be24817a00cdac58f6980f0343030217100489410445fc242f42c0692344243281292bfa625307,0x44d083a001010100400240840010800510400eb8b501011005821820009800423b000447880882200c2300c00a00200a0019f0d00803401201ac0020c2000488585111340640a684045fc24d20044130200c4080682004043280292bba000305),(0xbe68c01f1e9e9488111829e89795291c0250656b4642af1012b8231b8a5379587e913a4042d6bc2ba10e488ff5f11e506044850bf6cbe1bb8ce1dac7a50c1a3c68d40b10c85286729980540120b91403b92e7c8f928fc048e12a178008d84820,0x8128400a0c84908815980108874a28000000200002460200002004180240601c4011b8000246180aa000080735611840e144010352c881a08800da4401880a242004268891b1104ba3003ca248a9040191222807820fc008812a120000c84000),(0x4a588255f2689ce3686efced88e113a84c1041c465388844ef696a13e4d33bfa75341010f302665192f1f7b35ae687ee2a2561720011882b5ec6440ca727a440407842100810d4680842801008107118d104d84045f82a96dd11ccd5cbb08a6e,0x2a508205f2682e374040fce000a11338141841446530c046ed414203249313e0152604109000664112503080488ae78e028162f00113080b53460400a02184484069d8736e0c2f2054bec251301071184004504045e02a124c11ccd5cb308a2e),(0x447cd844526958658f9f557f72c045ed2305b53d3a1234895d9b8072244660232ac1677d3a113d8265b4435a510331135d7c672ee4a674c288be5e418a3a558d81406004a4580c2046a0369a81270032f08617985c25af1ad82b242701a0d8,0x2079d805024080250703153c524045a0410481180a0010101e190040000000e200200169221130802480430250001011521c060c04a48480882016488022043882010480d3d0972841098c8701040030308614981c05a512882320040120c0),(0x3b8e270712e2fa7298f0dc6ae68f62e4752ff0057a9f7c4d8125dbe50d236faa10e24dbc0b3001cff74201f0a00bb21f4e843021bbacd96d3c5099c80385d7a38c2a8061058500040610202802e27074cfc2217305e20a42c24fb282442bd899,0xbb07040010e0ba5298f0986ac20d008044baf00442847cc42021c2cb15216d88046248300251084f43500930848b82c46e840021b38808694e5109c8016cd1638428eecb792c0968d3a0343258e23044cfc2216305c20a42c0479080402ad818),(0xab1b226465d50f6c0e5e2172cc62d5418aa5134b0af03fcc5e8c151a690eb795c304128137a87ae9e9d40214015ad0a539f00ba6d5d927e90214284e5c25bc433624340e0208010040090a804585088a4da103701b0e83a1412ed07d915c9cfe,0xb909684460308e4d0d0c3163c46245402aa5110302b01e0c5a0c859b09431305c044000027800489a15402100153582521e00b26c1082ee90200081e1c35fb4220268e0af9bf581ba90029908781008a0da10270130e83a1410ed04401549cfa),(0x7071ab189d3748415213f3f77a94a7d6b3d3afa2ca26be6af3abd93f0aaa93008ac2001387d540c64678593580045e2ec4e3961ccf00360c37cb0b2650532106e5bc0180f000209180a05140206a91ab0848a668fc649d5446128540d91733d8,0x38519f501132484362023275489483dcb1d31da20821b80adf8fd927098a83018ac600030d91c0c0005071108006462206b31e688500360406c100000013210085d29926684ece940855c35c870291aa084886687c60054446108540d91730d8),(0x0,0x0),(0xc612d8a9a8e50b390cc5aa8c43250ca384a12c50a1a4c1f66012646411ac81f280688eaf90c349906d9902e827be40cedcebcd9fc0f96715b94e57b0a179a49b8309248030282881602d0b46944baa504016392666007f19a4e4d0db222c2700,0x42840021004d1130808088880201002004004054210441e020402000142440f20019868c10440a02448900a82ca800c8c800809100e14112312216a0a1480439000160d10600216056aa142378482a504006390200007818a060009b22280300)]
def f383C : IndexTree ColumnInfo := (IndexTree.fork 24 (IndexTree.fork 12 (IndexTree.fork 6 (IndexTree.fork 3 (IndexTree.leaf [(368,0,15,0,4),(360,0,23,0,4),(356,0,27,0,4)]) (IndexTree.leaf [(354,0,29,0,4),(353,0,30,0,4),(352,0,31,0,7)])) (IndexTree.fork 3 (IndexTree.leaf [(352,0,1055,0,7),(344,0,39,0,4),(326,0,57,0,4)]) (IndexTree.leaf [(321,32,30,0,4),(305,0,78,0,4),(290,64,29,0,4)]))) (IndexTree.fork 6 (IndexTree.fork 3 (IndexTree.leaf [(284,0,99,0,4),(276,8,99,0,4),(273,32,78,0,4)]) (IndexTree.leaf [(262,64,57,0,4),(104,256,23,0,4),(82,0,301,0,5)])) (IndexTree.fork 3 (IndexTree.leaf [(78,0,305,0,4),(74,4,305,0,4),(71,0,312,0,4)]) (IndexTree.leaf [(70,0,313,0,7),(70,0,1337,0,7),(69,2,312,0,4)])))) (IndexTree.fork 12 (IndexTree.fork 6 (IndexTree.fork 3 (IndexTree.leaf [(65,0,318,0,7),(64,0,319,0,11),(64,0,1343,0,11)]) (IndexTree.leaf [(57,0,326,0,4),(53,0,330,0,4),(51,0,332,0,4)])) (IndexTree.fork 3 (IndexTree.leaf [(50,1,332,0,4),(49,0,334,0,7),(41,16,326,0,4)]) (IndexTree.leaf [(36,0,347,0,8),(36,0,1371,0,8),(34,0,349,0,7)]))) (IndexTree.fork 6 (IndexTree.fork 3 (IndexTree.leaf [(34,0,1373,0,7),(32,0,351,0,11),(32,0,1375,0,11)]) (IndexTree.leaf [(30,0,353,0,4),(29,0,354,0,4),(28,0,355,0,7)])) (IndexTree.fork 3 (IndexTree.leaf [(18,0,365,0,7),(16,0,367,0,11),(13,16,354,0,4)]) (IndexTree.leaf [(5,0,378,0,7),(4,0,379,0,11),(4,0,1403,0,11)])))))
def f383A : Array (List Nat) := #[[]]
def f383d8 (i : Nat) : Nat := 0x1d642000000002c0ea5080b04020241000080404182034202c202c202c202c202c20016101610161016101610000001a140c100000840584058405840584000000000000000000000585030406840003607840a80f08003420342001a1000d0829058201a140c101a1d1735cc32bc9b21c7317c1ef7b72ccb1ec2acaada768d9f66d9764d8f6388a218821f87a1e3779d9751c46d1af6a99a6297a5a95a5555052d465053c4dd324b52848d1e4651443d0a3e8ea368d5340b526895214751c06016c4b0c02004000a5fb6d4cd10b8a812ef6d2aa60d7150297edb532c1ae2a063beaa2617350540b37b6e41ae2a0a814fb6ca99a213150237edb554cba62a047edb2aa9974c54096fb6b5530e98a814fb6ca9961d31502d6edb146c3a62a05bb5b7261414c5408dfb6c54cef08a811fb6c8a98ce1150277cdb554b8a60a0437db52a6889dd4092fb6a54d113ba8146f6d2999dd8350293eda94ecb106a052bdb429d9620d40a5db6453b2c41a814bd6c4a76588350297cd814ecb106a060feaa9dd9620d40a1fb6e50b2c41a8149f6d4a16588350295eda142cb106a052edb22859620d40a5f36050b2c41a810df6d6aa661735021deda554cc2e6a053b4b8691911cd40877b6854d1119a812e76d0a9a22335025aedad54c3c66a042fdb6aa9985c54086fb6b55330b8a810bf2e5a620d7150315ed3328418e2a04abebb6988350540c57d32d3106a0a81a2f9dda620d415021dedd13039a82a062bc986987350540c67930d28e6a0a818eb261a21cd415031da4c34239a82a063b8986807350540e339313bc66a0a813e6aeda3241415033cccbb4648282a06b998768c9050540db34eed1920a0a81be46c5a3241415021deda554cc262a043edb2aa9984c540bf236051a8298a817e46cca050531502d5adb106a0c22a04b75b5aa98784540976b695530708a812bdaeda620e1150347b3bb4c41c22a0473db52a5414c1409e736a54a82982817e46d0914c530502fc95da8298a60a06f92aa505314c140bf2172a0a6298281de4a65414c530503dc85428298a60a07b9288505314c140f7230ea0a6298281f649dd414c5305025bcdad54c3c00a04bb9b4aa98380140
def f383l8 : Packing := (76,5,6,0,0,10,0,f383d8)
def f383d9 (i : Nat) : Nat := (if i<3 then (if i<1 then 0x8384540afd6848384540e7d9dd8184540ef58cd8184540afd6a17184540eeda214184540eed61d4184540f6d9dd4184540eed20d4184540fe58cd4184540afd6a13184540afd69c9884540afd68c9884540afd2a68884540afd6a09784540bf96889784540afdaa98784540afd2a58784540afd68c8784540e7d61e7784540e7d2a27784540e7d2627784540e7da227784540afd6a09384540bbd6989384540bfc6809384540afdaa98384540afd2a58384540e7d9dd8384540afd69c8384540e7d9dc8384540afd6a17384540afd6a07384540bbd6987384540bdd6947384540bed6907384540bf96887384540bfc6807384540ef560e3384540ef52a23384540ef52623384540ef5a223384540ef561e3384540ef521e3384540f759de3384540ff428233845409df696995c1409ef692995c1409ef2a5415c1409ef692994c1408ff6a5874c1409ef2a5414c140fe5505314c140bee692994c140dee692994c140cfea66884c140bfa688974c140afeaa9874c140cfe2a5874c140cfea65874c140ef628d874c140e7e61e774c140d7ea66774c140e7e2a2774c140e7ea22774c140ef6a22334c140ef661e334c140f769de334c140bde694914c140bee690914c140afe6a0714c140bee690714c140bf668c714c140beeaa9414c140bee2a5414c140deea65414c140eeea21414c140eee61d414c140f6e9dd414c140fe668d414c140fe68cd414c140fec645414c140fec505314c140bf6aa9314c140df6a65314c140ef62a1314c140ef6a21314c140ef661d314c140f769dd314c140ff4245314c140ff45c5314c140fe6505314c140fec506114c140ff44c6114c140dfca66114c140efca22114c140efc61e114c140f7c9de114c140ff428e114c140ff48ce114c1409ef69299441408ff6a587441408ff6a58344140bedaa94144140deda654144140eed61d4144140f6d9dd4144140ded64d4144140fe58cd4144140fec5053044140afeaa98780140cfe2a58780140e7e61e7780140afeaa98380140e7e9dd8380140afe6a17380140afe6a07380140bbe6987380140bde6947380140bee6907380140bfa6887380140bfc68473801409fe2a63380140ef660e3380140df62a63380140ef661e3380140f769de3380140afeaa98180140e7e9dd8180140ef68cd8180140afe6a17180140afe6a07180140bee6907180140beeaa94180140eee61d4180140f6e9dd4180140fe68cd4180140afe6a13180140fec5053180140afe6a03180140bde6943180140bee6903180140efc6061180140fec5061180140efc61e1180140f7c9de1180140efc60e1180140ff48ce11801408df6969961d408ef6929960d408bfaa99620d40c3f9dd9620d40c6f2627750540aaf6988350540ce72623350540be668c9050540abd6988384540fe4505314c140 else (if i<2 then 0xaf7684988cd40af72a6888cd40af76a0978cd40af7aa9878cd40af72a5878cd40af7684878cd40e7761e778cd40e772a2778cd40e77262778cd40e77a22778cd40af76a0918cd40be7690918cd40ef661c908cd40f769dc908cd40aef69299605408ff69e9960540cef69299605408ff68e9960540cfe6829960540c7f65c97605408ff2a67760540c7f2a67760540c7fa667760540cf764c93605408ff2a573605408ff6a47360540abf6987360540adf6947360540aef6907360540afb6887360540afd6847360540afe68073605408ff2a63360540cf72a63360540cf7a663360540e779de33605408ffaa99720540c7f65e77205408ffaa99320540c7f9dd93205408ff6a57320540c7f65d73205408ff6a47320540abf6987320540adf6947320540aef6907320540afb6887320540afd6847320540afe6807320540cf764e3320540cf765e3320540e779de33205408ff6a2995c5409bf69a995c5408ffaa9985c5408ff2a6885c540c7f662775c5408ff2a5835c5408ff6a4835c540a7f69c835c540abf698835c540afd684835c540cf7662335c5408ffaa9981c5409efaa9941c540cefa21941c5408ff6a5831c540cef651831c5408ff6a4831c540abf698831c540cef650831c540cf7662331c540de7652331c540aef69c9850540cefa668850540cef2619750540aefaa98750540cef2a58750540cefa658750540eed2858750540cef2627750540e6f61e7750540d6fa667750540e6f2a27750540e6f2627750540e6fa227750540cef2619350540bcf6949350540bee6809350540cefa648350540aef69c8350540e6f9dc8350540cef26173505409ef6a47350540aef6a07350540cef2607350540baf6987350540bcf6947350540beb6887350540bed6847350540bee6807350540cef2623350540de7a663350540ee72623350540ee7a223350540ee761e3350540f679de3350540fe52863350540fe62823350540dee65c9050540eee61c9050540f6e9dc9050540bee68c9050540fe68cc90505408ff6a2994c5409fb68a994c5408ffaa9984c5408ff2a6884c5408ff6a5874c5408ff2a5874c5408ff6a4874c540afd684874c540c7f662774c540cf7662334c540bedaa9414c540deda65414c540eed2a1414c540eed261414c540eeda21414c540eed61d414c540f6d9dd414c540fe528d414c540fe58cd414c540fec281414c5408ffaa9980c5408ff6a5870c540c7f65d870c5408ff6a4870c540c7f662770c5409dfaa9950c540cdf6a1950c540cdfa21950c540cdf61d950c540cdf21d950c540d5f9dd950c540dcf691950c540cefa21940c540cef61d940c540d6f9dd940c5409feaa9900c540cfea21900c540cfe61d900c540d7e9dd900c5408ff2a688845408ff2a58784540afd68487845408ff2a58384540abf698 else 0x9911cd40dfd681911cd40aff684878cd409ff2a6778cd40aff68c9760540cffa667760540aff69c9360540affaa97360540cffa657360540affaa97320540bbf69a995c540dbf69a995c5409ff68e995c540aff68c985c540cffa66885c540cff261935c540aff6a0935c540bdf694935c540bef690935c540bfe680935c540affaa9835c540cffa65835c5409ff2a6335c5409ffaa9931c540cffa21931c540bef68c9750540eef2627750540bef69c9350540eef9dc8350540befaa97350540eef2a17350540eef2617350540eef61d7350540eef61d7150540eef20d7150540bfb68a994c5409ff69e994c540dfb68a994c540aff69c984c540cffa66884c540cff261974c5409ffaa9974c540cff2a1974c540cffa21974c540aff6a0974c540bef690974c540affaa9874c540cffa65874c540ef728d874c5409ff2a6774c5409ff6a5714c540efd2a1714c540efd261714c540efda21714c540eef61d414c540fed29d414c540fed25d414c540fed9dd414c540fed5cd414c5409ffaa9970c540cffa21970c540cff662770c540def9dd940c540dfe9dd900c540aff68c87845409ff2a67784540aff69c83845409ff2a57384540bbf6987384540bdf6947384540bef6907384540bfb6887384540bfd68473845409ff2a63384540f7d5c5315c140fed505315c140ff55c5314c140bfe684974c140bfe69c914c140bfeaa9714c140fee9dd414c140fee5cd414c140fee5c5414c140fee505314c140ff65c5314c140bbf6987344140bdf6947344140bef6907344140bfb6887344140bfd6847344140fed9dd4144140fed5cd41441409df6969961d409fe6829961d40adf6969961d40aef6929961d40afe6829961d40cdf6969961d40cef6929961d408ff68e9961d408ff6869961d408ff6829961d40cfe6829961d40abf6989361d40cf764c9361d40cfd6449161d408ffaa99321d408ffaa99121d408ff2a6889dd40a7f68c989dd40a7f684989dd40a7f2a6889dd40a7f6a0939dd40b7e680939dd40a7f6a0919dd40b5f694919dd40b6f690919dd40aef6929960d408ff69e9960d40cef6929960d408ff6869960d40c7f65c9760d408ff2a67760d40c7f2a67760d40c7fa667760d40cfd6449160d408ffaa99720d40c7f65e7720d40cbfaa99620d40cbf69d9620d40cbf29d9620d40cbf9dd9620d40cbf6859620d40cbf2859620d408ffaa99120d40c7f9dd9120d408ff6a2995cd408ffaa9985cd408ff2a6885cd40c7f662775cd408ffaa9981cd40cbfa21961cd40cdfa21951cd40cefa21941cd40cfba21921cd409fdaa9911cd40cfd6a1911cd40cfd2a1911cd40cfda21911cd40ded691911cd409feaa9901cd40cfea21901cd408ff2a6888cd408ff2a5878cd40af768c878cd40e779dd838cd40af76a1738cd40af769c988cd4)) else (if i<4 then 0x61f081a4a881608aa103822a92a2012a147c2000006eaf9aebc1e0402c02500ff4dd783dcd01a0d9cd98a61f19b314c3e30551547c61003a1481e0f94154551f1f35d783e1511592a49f18540fa3ed5f4dd7f341001a9a8369eaa7469b8a67e986a5b6954a4ee922a44e8faa3868c8a2be896a1f6864a12e832a0668009f9e7c49eae7929dbe7569d1e7249c066e89b3e6ac9a4e67a998664898be61697ce5d097065bc968e58a95c654e948650893be4cc92ce4a4922e472913e42c90263f08f363aa8e4636e8d5633c8cb630a8bc62d88afe2a68a36274896e24c88f6224882e1f287661c0869e18e85d615c850e134846e10c83a60da832e0a8823e06c817604480ae0127fbdfd67ef5fae7e7df867db5f407c9df0e7bd5ee67b35eb47a6de8c797de5a7955e3c788de0a77eddec7775dce76d5da6765dd7e756dd4274a5d10742dcf2738dcd4733dcb6729dc8e71d5c4870bdc166fa5bd06f05b9e6dedb586cfdb266c35af46b6dac26acda9a6a05a686965a4a68c5a1867fd9f067ad9d2670d9b4669598c65f596e657d950652d9466505932646590a64158ec634d8c462ad89c625d8746195856614582e60557fc5f8d7ca5ec578e5dd575c5d3573e5ce57205c456f85ba56c65ab568a59c565858fd62658355f457955d657455b8560555e54ed52254254e653354b4526d48251a545a510542850153e24f2539c4e353744d6d34c4ca531a4bdd2e84b8d2ca4ac52ac4a7528e4a2525c490d22a48451da470519445ed162452513a44ad11c44350fe43950e043450cc42cd0ae427d090422d086420507c41dd0544074ffa3f5cfb43e6cf783d7cf463cb4f1e3c3ceec3b4cec43a5ce883a0ce7439bce5638cce1037b4dde373cdb63674d70355cd483494d1633f4ce43354cc632b4c9431ecc62314cc3a305cc08300cbfe2f94be02f1cbb82e7cb902ddcb5e2d14b362c9cb182c24afa2bacadc2b5cad22b34abe2abca962a1ca7829cca642954a3c28b4a1e283c9f6279c9ce27249c426fc9ba26ac9a6268499c260c96a259493824548f223648c022c48a221fc870213483e20e4820206c80c201c8021fa47da1f047a81e3c7761d9c74e1cac71c1c346ea1b446b81aa4686198c654191464018c460e17fc5fa175c5be1694596164458c15cc564155454614b450a139c4d812fc49211e445610f442410544060fdc3e80f8c3ca0eec3ac0e743840dd43660d5c3520d3433e0ce432a0c943200c1c2f80b7c2da0b042b20a8c28a09ec26c097424408fc230088421c085c21206f4172053c12c04240d202bc082017c000aff6849361d40aff68c9161d40aff6849760d40aff69c9160d40cff9dd9120d409ff686995cd40aff684985cd40cffa66885cd40cff261915cd40aff6a0915cd40bef690915cd409ffaa9911cd40cffa21911cd40dfdaa else (if i<5 then 0x6880102840500220001010201040201802200c0a100603881e004401814200c0a100605080302840181420480a103c107820103c1eac200346080410083f1581a30a40d10544b02e30a424b02e202820101410080a08017181410080a08040e841d08140f08050784028580f020401420100a0f080a0b0402042003440f01420800010001e980a0b01020000d81a207417103c050a060c0c1418303060627c50304060c0c4a880506c1e18100d881e06c40f0362001a080886081a10020050801080205880102c46c8140601640400b10240588d903c1d00480e82e204820603c008c0b0341e18580083c381805103c05082002841001420800a104005084508020b88120284100142080222840a07840f03620800a10021040c42880a082e103422290a28182050403090a100002a84552544050400284020481d102810801d1022100260e820321830b0400603a008c0105c40105820082c100a1608020804148020b8c050b041001a203430b04008014200c20d81a203420a008068c1f040414850018c1202840901420480a10240508120284090142034201840160062ebfa60400305ca080400b8c200201e1c0c02882800c40c0360b8c15040405820201417140c82881e028422841e02840403c2054080786060020e8c0a0484150180083a4114222a0a20a820142a10602005c64304230281e190c1004e02088645440218208840168081002e40a82010541008120a84058400f0520f94128ac4050288aa3e406020102a10082800c410042008401080210040806c40044202191510055082e100000001a0f0243e6817e9812034a068400b8c100481e18420a82030480a105a0502e301417101a8a880d45440b041608541002e327c17102c10a79a04c2c202c1002c1003c0d882302010182a0f02030201d00462a840e082404881e0384118580f02040201b101c10900908062a842908042ac2a215422a841507842ac2a207417103c050803083c0b882903c1d18241002062144005506142a10482a142a103415101442880d05448b0445088a18182050401090a100010b04160c2c4f880d0a2c100021aac30310a21142228445088a428845088a428800001a5080000281e100a1008002a3e0f036408c0807860d83e0f0c1e05c4d583c203420f87ab03420190c1e980a078643040432522010c1000860a451487ab07841503c20a41e10540f081e092c150aab07c1e192c125821483c100c968ac41504020a420fd560f0c290342c181a10342003421481a0f0c0d083a6e680d182e0f08960a840684002192916561258294841808041082a080c210540d182c105a1f102a0f8580f101687c40f8580f0c1687c40f83c28182000485081a1040c428845088a111422290a2114222840d08008f8410b040081885108a1114851009541850f8 else 0x2ba6080611814068c0d00c443006200010100205080d00440081a20040c101a008801083c05080a00c4018142028171002018801028406802200010110c008801034406802200403108a08006300c10100605080d00f9a1806080808082001f34304003e68601f34200f9a102001eb2300c101020018801028405002207827100608881d0a81e182405c5630782004420103e8a8803218405824150c550481703480801420480d110bd782430280d102410780a17340e082c07216181a0905830282c03460685820400aa947d303c160c0d0284160382a8c03e6840575e281830b03c090c16034406840227c0d113e)))
def f383l9 : Packing := (486,4,6,0,0,14,0,f383d9)
def f383h9 (i : Nat) : Nat := 0xb172d5d6000484e6c004caf5de0607a0930969800000000001923229872ec5c31e0006adcaa18c4a00181e08000113605c907b0309f000790e6810a11282e4000497d5f60a9b80000187e02a34f39c67d9a2827908396d9de260035fa86563e2840536c0eca8d800028c64ba390e000002dd13948bac8004a7d9600000596046434ca22908108110104008508200704e2cf04410084e580
def f383d10 (i : Nat) : Nat := (if i<2 then (if i<1 then 0xe39902a06ff8cc81502ffd32b8a817fd985c540dfecc2e2a06ff261715037fd10b8a81bfd875c540eff3bae2a06ff60d715037f906b8a81fde335c540dfec0ae2a05ff660715037fd1038a817fd931c540dfec18e2a06ff20c71503fbc6638a817fd901c540fdf4ca82a07ef65d41503f792ea0a81fbd8750540fdf3ba82a07ef64d41503f7926a0a81fbd8350540fdeb9a82a07ef1cd41503f7c66a0a81fbd7150540fdec8282a05ffa6531502ffb3098a81bfd984c540dfe4c262a06ffa2131502ffb2e98a81bfd874c540dfe43a62a077f9dd315037fb0698a81fde334c540dfec0a62a07fd5c531503f7a8298a817fd980c540dff44062a05ff65c315037fb0e18a81bfc870c540eff3b862a05ff640315037fd1108a81bfd8784540dfe43c22a077f9de115037fb0708a81bfc8384540fef19c22a07fd60611503feae308a81ff53184540ffa4bc22a07fd61e11503fecef08a81ff49384540ffac1c22a07fd5ce11503fe8e708a81ff63384540bff4cae0a077f9dd705037fb06b8281fde335c140dfec0ae0a077f5c570503f7a82b8281ff6115c140bff4ca60a05ff65d305037fb0e98281dfe774c140fef19a60a06ff60530503f7a8298281fdd314c140ffb08a60a07fe5c130503ff53298281ff9974c140ffc4ba60a07fe61d30503ff4ee98281ff9734c140ffcc8a60a07fe24530503ff30298281ff9714c140ffc38a60a07fe4c530503ff422982817fe9944140bfecba20a06ff61d10503bfcee882817fd9344140dfec1a20a07f78cd10503f7a8288281ff61144140ffc98220a07fe9de00503ff2e700281ff87380140ffd19c00a07fe5c600503ff0e300281ff93180140ffc18c00a07fe846005027fd32c3a813fd9321d409fec890ea067f61e775033f9313ba819fe889dd409ff4cb06a067f9dd835027fb2e41a819fe7720d409fec8906a04ff661735027fb3039a816fd961cd40bbeca8e6a05ef65073502fdb2439a817f5911cd40bfcc80e6a06f760e335037b93119a81bde888cd40deec3c66a06f721e33503bbcef19a81fd8908cd409ff4cb02a067f9dd815037bc66c0a813fd9720540cff3b902a04ff64c815037bc6640a813fd985c5409fecc0e2a05ef65071502f7d32a0a81bbc9850540ddf44282a06ef61d41503b7ceea0a81bbc8350540fcf19a82a07ee241415027fb3098a81fb5414c5409fecc062a05df65431502f7b2818a817f9900c540dfac0c22a07ed506115037e93108a81bf68884540dfac3c22a06fd21e11503becef08a81bf58384540dfa41c22a07f58ce11502ff53298281bfa884c140dfcc3a60a077e9dd30503fb46698281fb9414c140fec98a60a07fc84530503f6a8288281bf98780140efd3bc00a06fe60e00503fb46700281bf98180140fdca0c00a07fc846005025fb2c41a813bc9850540 else 0x5322bc80b1d9c6c3187c557123c3eb0c8c27f05bc11302dc05afedbecaf9bbdcaf49bca6ef7bb3aeaeb9cee0bb78ada7b61ed3ab3fece8b2dac9fb1b6c20b002bbcade2b46ac9ab18ac06aeaab4eab3aa72a73a906a2aa7e29e1a6e2986a576919a39e8c7a1a282d9fee7c09e167659caa6c29a6666798fa5e896da59f94de4ea932a48f91e2446900a3d98ec23998dc23508cc22f58b5629a89c623f885a1c9868216e851612582f6094818a0427fb1f7b7c05ebd7a75e62792de10770dd9175e9d487411ce47311cad7235c497015bd36ecdb816d3db2f6c85b0a6bcdadc6b15aa56a39a776981a4068819ee673999365cd938643d8dd62f5894618983060417f95f1d7a75df975e5cb16fa5b2169659b563b58255e056dd58e54bd50653514ab520945050553f54f0d3914dc533f4c7d2f64b592bf4aa128849a125148c521a47e9189453911343610b841f50033efcf843d24f0e3ae0e8f3998e3d3850deb3708da2359cd473430cbf3234c403080b9d2d64b152bb0ac32a68a71286c9e926dc973252891822e487e210c7ff1f587771ca86ef1b18694198862717b05d5166854d146c4ce122844f10083be0e543480bec2d209cc226076419e05b013a03fc0cd022406000b80170003ffceec1a81ffe995cd40ffecc2e6a07ff61d73503ffb06b9a81ffd915cd40ffe48ae6a07ff64173503ffcef19a81ffe7760540ffeb9b02a07ffa6571503ffb30b8a81ffd875c540ffec9ae2a07ff24d71503ffb06b8a81ffd735c540fff19ae2a07ff60571503ffb20b8a81ffe331c540fff4ca62a07ff66131503ffb2e98a81ffc974c540ffec3a62a07ff9dd31503ffb0698a81ffd734c540ffec0a62a07ff5c531503ffb2098a81ffe770c540fff3bc22a07ff5ce11503ff8e708a81ffe3384540ffeb9ae0a07ff8cd70503ffae2b8281ffd315c140fff3ba60a07ff5cd30503ffae298281ffd314c140fff3ba20a07ff5cd10503ff8e688281ffe3344140ffeb8a20a07ff4c510502ffd32c3a81bfe9961d40dfec9b0ea06ff24d875037fb22c3a81bfc9161d40dff444eea077f61e77503bf9273ba81dfc919dd40bff4cb06a06ff61d83503bfceec1a81bfe9960d40dfecbb06a06ff25d835037fceec1a81bfd9160d40dfe48b06a06ff9dc83502ffd32b9a817fd985cd40dfecc2e6a06ff261735037fd10b9a81bfd875cd40eff3bae6a06ff60d73502ffb3039a81bfe881cd40bfec88e6a05ff640735037fd1119a81bfd878cd40dfe43c66a077f9de33503fbb0719a81fdd738cd40fee4bc66a07f761e33503fbcef19a81fdc918cd40bff4cb02a06ff61d81503bfceec0a81bfd8360540fef19b02a06ffa65815037fb2ec0a81bfc9760540dff3bb02a06ff64d815037f926c0a81bfd7360540dfe39b02a06ff8cd815037fcee40a81bfd7320540df) else (if i<3 then 0x2c2c0d9420030fe983c290b1c462c080c3e080d8cab1510a43c1d18a93f061407c3c1d3848461f228b02a1e387c362a04074a558fc54603830a02a1e28283e2a09074a558fc5461f0a7c2c24f85844542880c9f11153e8518593e2aca7c4064f882c45428eb2a94f8c54068f8283c50fc7c0c3142543f1602878c06d5c7c7290faa42e050f183f9a8f8788ab1485c3e1e281b571f18a63e1b0f13560614c7c3c5430a43e2c0f15b3ab8f8c3e29107d0a2916078a200f8787af0fc7c3c46ceae3e3d5a58521f0f143e29d58803c50fead2c290f175629430344054b0a43e1e225a561f43034ba614a583e0d2ead0c290f13561f4b07881f430a43c4080a256d9d5ebf35a61003542a4b0343c4d32583e29069454861487891f150743c4d5818531f0f1552451607c2a1e305b571f1eac8a298f878a85830b02a1e285b571f187c2e1d0b078a1f8f85861f830a43c40fc7d0a30307c4450f883ea98f8c0c1f6c8c8a8510583eee19543e28f87d2a314c7c201e0f85757afd3668580a60541baf0f8a00c6148775e170f818c1f54ebd2bab031b5e064f8eb39ad7aa52a9f307c2b298feac0a29d36bc3d9a0686dad9d5e680ba6d7c54e150866802290f99b20595e6a531f30142f9a148483e6d58842015d7e9b340d0f242a1e14818820050a40c4100285206208014290310400a14818820050a40c40f0a40c30fa5735a6428a4d9a14a7c759cd2175e954f980c29cd2975fab4ae9900514ebd0a9f2b640c85d7eaf3529d32334294f8c0a291547c3c15d587f4c1dcd6bc4017705b579ad34a40baf385b579ad30a60baf38a4201f0b102a058ac7c8050687c2c40a8a62b1f20a43d9ad78174dab0b841229d58800c162860542003058b1fcd69b5f2b1507ce201507c2c4cd6bc522a0f9452860f85735af0f69a2c20505a2b9ad36be3e6158803b9a1487cc1614c5735a6d7c7cf9ad787c544d58780a15cd6bf4c0d1005d4290fe993f9ad78802e80287b4c290d858c24148382c40f698521b0b143da61486c2c50fead5285d3058cab4f8a83fa60b182c9f156735af42aa53e6032a734a5d785757a640142baf42a7ca16032162b9ad7e9b568aceaf3485d30575e7ac855579a54a7cc16acc55539ad7e9b568cd4a63fabd787f4c7cd6bc521f204053abd7e9b340d0f21b39a95ca75f1fd36ad19a0fe98524150ad5629d787f4d9a1607951f0fe9b57afcd0781a86ce6a5729d7c7f4dab40775f9a1605c3e654e6b5e950f95b285cd6be3e514a1735af4a87ccd954e6b5f1f28a90aa9cd2575e1f38ab35af0f91b295cd6be3e51487c4150f8b939e443902e38b8cbe28b88be1d3854e0f7826dfd37d4ded378bdd8b742dc436dedafb695d9d763ad8475dfd6db584d54b532d4034e0d2bb47cd17343cd04f3f3cf4f3b3ce4f373cd07321cc072cfca9b27dc9 else 0x3c1b106c8a0d00913e1080293e30f06c49f030a41a40f00440d4f882001050c3c1d10783a22ae688a100197349f030c3c0a030d3f9a08058810cd018064ac8783630b27e3e060816b2160806d3e50b0783a3cd018209f2004400a19575e1b0b8481a64f8581a2c227f5e170b034a0ad78a41a44f8a43c0a16153f6e0b0281a5068a05830327e3e2906943c1d160c0c9f8f8582e54febc2e290694021b070c3a03050c3d150ec7c803050786120d87461e050186100d82860a0f0187ab7702a3e1e28281a1b1c7c1a1b1eadb31f0d878a1b0f08052442eac3a0a26ae3e1e0e91520a100788a90d8803a48f8742c17205c3a160f100d1f0507881fd30781410281b4c2c0f040ba6050b0204d30780c2c08174c96050788074f86c0a088b028e1f03080c9f10192a28f8a4361e207d2c2c030a43c66cc7c41f1486c1a40fa181a1e2218360d180d2c1b02834a290f2581a40f2583630287e572908028c100fe680daf0f698022c050356222aa7c3c402a543c9f06840c9f0600461fcd6bd2b16038713e8030a52b160f840c068f892b160d8141a50d8784290fc18580a28783e031005c14290320520a0f0c529f054583e2c0d9d4a120f07c522c081c521f428343656cca63e30f840c9f11150a20327c4454fa146554a8a3e2a0e87881f160182c20285a3e24341852160f142d1f107c541d0b903e860b0802e506ebd0c1d26bc1a0c160740a863a182c0d1005cb9a160746100f08335a606ebc3a010ba852a90ba180420321802292a880a0d0f86c0a080518200d0f8522b1f30a4240a18403e0a14848366cd0783e10d7e982c2c0585c14b110593e2026683c050b840b9a0427c064acaa43f16d7e68101b4fa45806050542058f818410105641baf0be985003cd07975955aa42e1f4f8702080347eb2354858401e0285cc1d0f08541f8b078145100483e0d0f0182c7830543c0d200454120e908b05107c2c0a0f103e2a100c3e16100f5e16152183a1e30583e20183b5e1f160750c64307c2c2026683e2c15080a860f8584048f8a43f9ad36bc3c17405d0c2c10110c1f14858405100583e17207c3a201ebc3c1fcd05c2da61604c140d59142c9f0f102baf4f85c1a5d7a7c2438b0343f9ab76bc240a4fa62a1e0f8402e200b69b5f9a0e035829b705d4ba6cd040580d0704b5e1e6db82e850fa7c080d385a3f6e1c5846290d8541a68f8a45060b214521f0b98522003698200dcd6bd1061487c2c17286c3c21487e))
def f383l10 : Packing := (310,3,6,0,0,14,0,f383d10)
def f383h10 (i : Nat) : Nat := (if i<1 then 0x38c0004a381d68f48122c7337cceb862634eeb3de8187280e6aa72890466609675dd40d4711d175710911362b14e720ae7da21938305fab6385d6eefd154be362269f684fafe2080000000000000001c5e00000000021f00000007a14001537a440000001f2903706740006760001be8b29bc70916472205422c2e060812db6f6b41b8935bfccf65b6facd31559608536d6197f8e4f8dc1ddf00666ed9400085400007340010278226023a626720b73070ba045119da092d409860000002603f1d00015da6da8f1953341de99740ce7f0ba648adbfb562708923a367446eb343cde346f1385b34f64ef44f974acdfd6bfe0080e8e5e433080f8b4a445a28f9d4b0a963bdd0da2bf7b30583638ace25921e8d860b1332cf69af6e0e4b66998d6baea387addde7fbaf95ecd9addc2a41493f8c6dd0e87b0232632b2c521f68ab19dc81563b88000d1d8173c4f83cbb0abf24d39639cecaa0ed99e40000009318003335b6b0002815ab42420005478000000000000097a28b00074b40000000004ae000085f0005c4eb03d277c7f83467340a9de7c1385828900026ad4044730000001943097000109a2959d397de61c0003666a2e9d49ac9444200702834000d798d52af0372d2d7aac21c000000003b216173e49932005501b34a5bf0000000b09118000105555d8001d8a73c7ea7d84001c650003b329184c9ef275656fafc653c00000000000000001d5d584111cb521d4f483278d43bc7210c7bd20e2642a7ccf965c2e875d2d07c3262dc048238002861c7a7695a88786000858be2ad67d20ae12265726c180000e415085a9edbc4507165bfe76440fd643461d8760e0537d29a0b0f2bc5308c3f487b066351aac16612242010af64618c97bd61446144b21c4749000000132af30abd4f5c5a644f0c2bec947400cad7ce8e098f6d0b715238ca379794fb48c11bc6952623438e5ab9cbf9589536c4400d7b29918b4d33ff977286d9d436eceec26e744d492bb2585e51b63ca5d500051740018628343887a1200000040ae42773d77f62d90fa0005482c40000d2e15c800000000000000000000000000003b3247ca958f20876000fbf1cffe472a80006ea9099a520006df0000a6740e800000000078b800377200042f0a7dd9ceaf52db6a2782de06dc000236d5b14f0adb00010e16787bb400068179c1a3ff240001ef800000000022500037a203fe8ca0b5a69e1f51c8a74389123cab70808203281580015383a52a00488060800c06b01032005f080a60083025c200022008f04000100824200080428616144951c105800008502027838000580911e10003040c050002880e0a00805042558c081c082104431d0400a82006810c020020214f88000050087060c98000011900220087020c0f31a18081060428e06a8289105410230c0e800000002 else 0x149b450883000264c975f7c80024e0ce00002d2f4d59b417a63ff69d3b5822eeb0ac155235ad770dcd8dda77800361e11ffd90bad8d9f30000205955a4c0f4de446e9f8e97683)
def f383d11 (i : Nat) : Nat := 0x291e160aaf9a2c1f4148b0fd58557831c1aac587abe68a07d02c3e0d56534d355f3e9200a29062030b100fd34d0d94a018a476be68b0587d0b2523e0d574d5f342d3ea1e0aab0616283370f94d355cd578b4fa8786e98a458a0c523c3f574c3a2c82916ab0a1eaf9a1f4030b558f57cd140fa018a47aac766abc587d20a522b355e3e62529151f9aa6abaf064d7830f8d669aae6abc1a7ce0a2b56534d355e3e82b9a291f22cd5d357cd14cf9c14a6ae9a6abc7c5902a3e2a69aaf161f2acd355cd578b4f9caca69aae6abc7cf355e3e3c7f80aded70a9741a60c6c87efa9deb78666bb950a6c43e808e29802b64786c8c412e1680e800ffd87503ff9dd40ffd83503ff5cd40ffc73503ff8cd40ffd81503ff5c540ffc71503ff4c540ffc31503ff84540ffd70503ff4c140ffd10502ffa2140bfd87502ff21d40dfe77502ff60d40bfc83503f78cd40bfd81502ff20540fbd41503fd84540ff930503fe80140
def f383l11 : Packing := (28,2,6,0,0,11,0,f383d11)
def f383h11 (i : Nat) : Nat := 0x155f8e331d94be08f8a75089250d2e6eae6f1490a138240000001d7e0003534ab6d398f1436c8ffdfd68c267c30800009835b800000000031050e600e00021f00009106fd46e18345f2cda677690486f40ab40ac08d1763ac7b9a8c480a48e22ca1c26b11d90bfbe0cd889398b5a0b4ae823d5b08f78ffd0669603a70bd12af6e899222082ff3f1346c34ee0954faee8a1d0500c830046292e3218cc38b2ea2f10b27e0d6654c144c7c9518d020a406d15da865210820000274b5c19554b7c7095f113a5d9cd90268390000c83f596ac7c206ef30180010b8000186723d5a7a9555a8211994928176fa464dc6a50002a15099a3c00073c920388a002009e80c6c50001c205cb50f0007b2220f6b400030c102509e5520001466722c8551d68f272df63800344587a9006c9401ca2ad0593d392d520000695b0262e7f250002a2ac60c7a8001cf608e13e8000e308514758000000000c38889400000000052680006bd98f430fc96000a7ddace5ae467e6d8ae7864e5a98a4b2400142e939118a08c000090f1602686fa0000002d79929c6c0a81a1600000033fe9d000096644cc0018abf04cb2ecd00009079a64913280978601460102bb88ca428c39045818002e2462c91c026fd9c4d5571180ac1942681b712400149d000048c000b1b166c49fde7e16d95f465cee444d3500004a6018c008003154126814d148dcc67c000000205a000b2f8003a6400024688776340000000001d8347800000039c2000d6fc19922fcb0c5d0a495a400065600014e6ec4c32d0d543c0008870003c38a69c31e1bf58c30d798abdadada1f727bbf042a00063b2c4c000c340000000da86a142ea470180180048d0600206080805504f00961a0c8090014004000021b14540800e6c1800108007003020000019830e00f12144c08202004a602082800690500007452c24003003080280e2000bf072400406000050268000000003d0070180
def f383d12 (i : Nat) : Nat := 0x2b4c6979f2ffd40
def f383l12 : Packing := (1,1,6,0,0,0,0,f383d12)
def f383h12 (i : Nat) : Nat := 0xe5f000088760800043820075401c63a0000000000007600f6800000000527f000b38000099e462824affb845c68e5d52da6ec0800014d4001840
def f383levels : Nat → Packing
  | 8 => f383l8
  | 9 => f383l9
  | 10 => f383l10
  | 11 => f383l11
  | 12 => f383l12
  | _ => emptyPacking
def f383index : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 26 96 6 11 7 0 f383h9
  | 10 => lookupWord 166 584 7 13 9 0 f383h10
  | 11 => lookupWord 106 376 7 13 9 0 f383h11
  | 12 => lookupWord 12 45 5 9 5 0 f383h12
  | _ => fun _ => none
def f383 : Forest := ⟨383,12,fun i => f383S[i]?.getD (0,0),f383C,f383A,f383levels,f383index⟩
def f383c8 : List (Nat × Nat × Nat) := [(0,24,8),(24,24,8),(48,13,8),(61,15,9)]
def f383c9 : List (Nat × Nat × Nat) := [(0,10,8),(10,24,9),(34,24,9),(58,24,9),(82,24,9),(106,24,9),(130,24,9),(154,24,9),(178,24,9),(202,24,9),(226,24,9),(250,24,9),(274,24,9),(298,24,9),(322,24,9),(346,24,9),(370,11,9),(381,24,10),(405,24,10),(429,24,10),(453,24,10),(477,9,10)]
def f383c10 : List (Nat × Nat × Nat) := [(0,2,8),(2,24,9),(26,24,9),(50,24,9),(74,4,9),(78,24,10),(102,24,10),(126,24,10),(150,24,10),(174,24,10),(198,24,10),(222,24,10),(246,12,10),(258,24,11),(282,24,11),(306,4,11)]
def f383c11 : List (Nat × Nat × Nat) := [(0,13,9),(13,15,10)]
def f383c12 : List (Nat × Nat × Nat) := [(0,1,9)]
def f511S : Array (Bits × Bits) := deadsamples
def f511C : IndexTree ColumnInfo := (IndexTree.fork 64 (IndexTree.fork 32 (IndexTree.fork 16 (IndexTree.fork 8 (IndexTree.fork 4 (IndexTree.leaf [(480,0,31,0,7),(480,0,1055,0,7),(450,0,61,0,5),(448,32,30,1,5)]) (IndexTree.leaf [(418,0,29,0,4),(416,64,29,2,5),(400,32,78,1,5),(400,8,99,4,5)])) (IndexTree.fork 4 (IndexTree.leaf [(396,0,115,0,5),(390,0,57,0,4),(388,8,99,16,5),(385,32,94,0,5)]) (IndexTree.leaf [(360,0,151,0,5),(344,0,167,0,7),(337,0,174,0,5),(336,8,163,4,5)]))) (IndexTree.fork 8 (IndexTree.fork 4 (IndexTree.leaf [(332,0,179,0,5),(330,0,181,0,5),(329,0,166,0,4),(328,16,166,1,5)]) (IndexTree.leaf [(326,0,185,0,5),(324,8,163,16,5),(324,0,187,0,7),(322,0,189,0,8)])) (IndexTree.fork 4 (IndexTree.leaf [(322,0,1213,0,8),(321,32,30,128,5),(321,16,166,8,5),(320,0,191,0,11)]) (IndexTree.leaf [(320,0,1215,0,11),(305,0,206,0,5),(296,16,198,1,5),(296,0,215,0,7)])))) (IndexTree.fork 16 (IndexTree.fork 8 (IndexTree.fork 4 (IndexTree.leaf [(289,16,198,8,5),(281,0,230,0,5),(280,64,165,2,5),(276,8,227,0,5)]) (IndexTree.leaf [(275,0,172,0,4),(273,64,172,2,5),(273,32,78,128,5),(273,0,238,0,7)])) (IndexTree.fork 4 (IndexTree.leaf [(268,64,177,2,5),(268,0,243,0,7),(268,0,1267,0,7),(265,16,230,0,5)]) (IndexTree.leaf [(262,64,185,0,5),(258,64,189,0,8),(224,256,23,8,5),(200,256,23,32,5)]))) (IndexTree.fork 8 (IndexTree.fork 4 (IndexTree.leaf [(200,4,305,2,5),(198,0,313,0,7),(198,0,1337,0,7),(196,2,312,1,5)]) (IndexTree.leaf [(194,4,305,8,5),(193,32,30,256,5),(193,2,312,4,5),(192,0,1343,0,11)])) (IndexTree.fork 4 (IndexTree.leaf [(178,0,332,0,4),(177,0,334,0,7),(176,1,332,2,5),(172,0,339,0,5)]) (IndexTree.leaf [(169,0,326,0,4),(168,256,23,64,5),(168,16,326,1,5),(166,0,345,0,5)]))))) (IndexTree.fork 32 (IndexTree.fork 16 (IndexTree.fork 8 (IndexTree.fork 4 (IndexTree.leaf [(164,0,347,0,8),(164,0,1371,0,8),(162,1,332,16,5),(162,0,349,0,7)]) (IndexTree.leaf [(161,16,326,8,5),(160,0,351,0,11),(160,0,1375,0,11),(156,0,355,0,7)])) (IndexTree.fork 4 (IndexTree.leaf [(153,0,358,0,5),(148,8,99,256,5),(146,4,353,8,5),(146,1,332,32,5)]) (IndexTree.leaf [(145,32,78,256,5),(144,0,367,0,11),(141,0,354,0,4),(140,16,354,1,5)]))) (IndexTree.fork 8 (IndexTree.fork 4 (IndexTree.leaf [(138,4,369,0,5),(133,16,354,8,5),(133,2,312,64,5),(132,0,379,0,11)]) (IndexTree.leaf [(132,0,1403,0,11),(128,0,1407,0,13),(113,0,398,0,5),(112,256,135,8,5)])) (IndexTree.fork 4 (IndexTree.leaf [(104,256,151,0,5),(98,1,396,16,5),(98,0,413,0,7),(98,0,1437,0,7)]) (IndexTree.leaf [(89,0,422,0,5),(84,2,424,1,5),(83,0,428,0,7),(81,2,424,4,5)])))) (IndexTree.fork 16 (IndexTree.fork 8 (IndexTree.fork 4 (IndexTree.leaf [(78,0,433,0,5),(74,4,305,128,5),(74,0,437,0,7),(73,16,422,0,5)]) (IndexTree.leaf [(69,2,440,0,5),(66,0,445,0,11),(66,0,1469,0,11),(64,0,1471,0,13)])) (IndexTree.fork 4 (IndexTree.leaf [(57,0,454,0,5),(51,0,460,0,5),(50,1,460,0,5),(49,128,330,4,5)]) (IndexTree.leaf [(41,16,454,0,5),(36,128,347,0,8),(35,0,476,0,7),(29,0,482,0,5)]))) (IndexTree.fork 8 (IndexTree.fork 4 (IndexTree.leaf [(27,0,484,0,5),(26,4,353,128,5),(25,0,486,0,8),(24,0,487,0,11)]) (IndexTree.leaf [(21,128,330,32,5),(21,2,424,64,5),(21,0,490,0,7),(19,64,172,256,5)])) (IndexTree.fork 4 (IndexTree.leaf [(17,0,494,0,11),(15,0,480,0,4),(14,16,480,1,5),(14,0,497,0,7)]) (IndexTree.leaf [(14,0,1521,0,7),(13,16,482,0,5),(11,16,484,0,5),(9,16,486,0,8),(7,16,480,8,5)]))))))
def f511A : Array (List Nat) := #[[],[81,130,118]]
def f511d8 (i : Nat) : Nat := 0x28a1af792bb71aaa64d815027d91e7b7552505314c140
def f511l8 : Packing := (2,7,8,0,0,3,0,f511d8)
def f511d9 (i : Nat) : Nat := 0x141400020001c20002c200014200007a100000508100d0800070a01a1001b6371000c009880013044290809410000011840003840220800c10040210034200000000011008400049522c8116c350ac04febd4f2ba4e6b90dab60d5b30c9b00bdad0aaa6889a1c7d9d06a9a06598c5995c4d9103a8e02e894228801d86c1885813844078140280186febb71aaa655815028f7ba95dd54c9b02a061bfaedc6aa9936054099deea598c9b04c0a8145fdd7aeda9549815028dfbad5537299302a04ded752cc64d8154540f9b2c9b04a9302a8a8155bdd7aed98549415024dfbad66350caa62a04baf75acc6a1544c540a2feebd76d4aa498a81f3c5956093260531503f70aa8c1264c0a62a04f6d75ecc549414c540937eeb598d432a90a812ebdd6b31a8551215024dfbad66350c9a42a051ef752bb6a1934854092feebd98d2b2690a8147bdd4aeda564d21502adf3ad5db24c0a60a053ee369b46c9514c140b7d86d368c0aa29828157f0db6498154530503f6c304a9302a8a60a04fe674ecc609414c1409edcebd98a9282982813dd9d7b31524c530502bf91b6c12a498a60a07ee455182605314c140fde0c12a4c0a62982817f92dd549414c530503ff0304a928298a60a047be75acc6e1214c1408efcebd98daa429828137d8dc6615348530503be3370aa2a690a60a077e46e1544c5214c140a9d6ea577443271128153b5d4aee8864e11502ae6ba95dcaac9c22a04de9752cc64e2284540a7cc6d368d9aa298281db92bba21414c530503bf05771128298a60a07ee0a2222505314c1409be86e330a9c2298281bf12cc5515384530503f62510aa2a708a60a07fc05515388a114c140
def f511l9 : Packing := (51,6,8,0,0,10,0,f511d9)
def f511h9 (i : Nat) : Nat := 0x1c1
def f511d10 (i : Nat) : Nat := (if i<2 then (if i<1 then 0xebb6aaa21414c540bf96cc4c9414c540ef96aa4c9414c540fb96884c9414c540ff85824c9414c540efa6aa889414c540fba688889414c5408efdc6aeda8485408dfdc7aeda54854097bdc4aed934854097f5c5aed988454097f5c2aed9884540d3f6bba219584540dbb6bba215484540d3f6bba219384540d776bb955938454097f4cb6615384540d3f5b9a215384540df36bb5515384540fb36885515384540ff155460d5384540f3d6886563384540fb9688552338454097f5c8aed928454097f5c5aed9284540d3f6bba219284540d776bb9559284540f3b688551928454097f4cb54d9284540f3d6888cd9284540f756558cd9284540d775b995582845409df5c7aed5284540d3f5b9a215284540d3f5b9a213284540d775b99553284540b7e6cc6622284540b7e6cc6562284540f3e6886562284540b7e5c96162284540f765989562284540fb66889562284540bfa6cc5522284540f7a5985522284540fba6885522284540b7e6cc64e2284540f3e68864e2284540f7665564e2284540b7e5c960e2284540b7e5c954e2284540ff255454e2284540f7c5988ce2284540fbc6888ce2284540f7c5958ce2284540ff46558ce2284540ff85548ce22845409fd9c3aed824c140ebeaaaa22224c1409ef9c6aed814c140afb8ca6d1514c140df99b46cd514c14097f8cb649514c140fbaa88889414c1409fd9c5aed314c140cfdabbaa9314c140d7dabb661314c140dbdabba21314c140ebdaaaa21314c1409fdacc6d5314c140cfdaaa6d5314c140df9abb551314c140fb9a88551314c140d7dabb649314c140f3da88649314c140d7d9b5649314c1409fd8cb609314c140dfcabb889314c140efcaaa889314c140f7c998889314c140fbca88889314c140dfc9b5889314c140ff8954889314c140bfd2cc605314c140dfd2bb605314c140efd2aa605314c140dfd1b5605314c140ff9154605314c140f7d192605314c140fbd182605314c140ffc222605314c140ff92bb505314c140ff91b8505314c140ff91b5505314c140ff91b2505314c140ff9182505314c140ff9152505314c140ff195454d214c140bfd2cc4c5214c140dfd2bb4c5214c140efd2aa4c5214c140dfd1b84c5214c140f7d1984c5214c140fbd2884c5214c140ff91544c5214c140ebf2aaa22114c140ef72aa956114c140fbb288552114c140bfd2cc54e114c140efd2aa54e114c140f7d19854e114c140fbd28854e114c140ff518554e114c140f3f28864a114c140f7725564a114c140f7d15364a114c140ff515354a114c140efe2aa88a114c140f7e19888a114c140fbe28888a114c140ff625588a114c140ffa15488a114c140ffc15388a114c14097adc4aed938894097b5c4aed9384540df92bb505314c140fb9288505314c140ff8222505314c140ff115454e114c140 else 0xc7febb6a55260540f3ed936095260540aefdc6aa93260540c7feaa6e53260540f3ed956093260540a7fcca6e58254540c7febb6a58254540a7fcca6613254540b7f6cc64d8154540f3f5936098154540f775935498154540b7f5c94c98154540fbe5824c981545409fbdc5aed82505409fbdc3aed8250540cfbebb6958250540d7bebb6615250540fbad8360952505409fbecc6e1325054097fccb661a54c540a7fecc6a1954c540afbecc6a1544c540e3fda8655824c540ebbda8551824c5409dfdc7aed524c540afedc2aa9524c540c7febb6a5524c540afecca609524c540e7eda9609524c540ebeda8609524c540f7cd95609324c540ff8d54609324c540ffc5c1609324c540f3f595609814c540fbb554609814c540fbe582549814c540f7d5954c9814c540ff95544c9814c540bfb6cc609414c540bfb6cc549414c540ffa582549414c540ff95c84c9414c540ff95c54c9414c54097fdc8aeda94854097fdc5aeda9485408ffdc3aeda84854097fdc5aed98485408ffdc3aeda548540a7fecc6a19548540c7febb6a19548540afbecc6a15448540a7fecc6a19348540c7febb6a19348540a7fecc6959348540c7febb6959348540a7fdca6159348540c7fdb96958348540c7fdba6558348540cfbdba551834854097fccb6a55348540c7fdb96a1534854097fccb6615348540ef3da85515348540ff1d5460d5348540e7f5a86553148540efb5a85513148540d7fabb649814c140fbe982549814c140dfb9b46c9514c140ffb1b4605514c140f7f192605514c140fbf182605514c140ff7152605514c140bfbacc609414c140bfbacc549414c140ffa982549414c140ff99b8551314c140ff9954609314c140bfdacc549314c140f7d998549314c140ffc982549314c140ffd152605314c1409ffacc6e1214c1409ffacc6d5214c140d7f9986d5214c1409ff9cb615214c140dfb9b8551214c140dfdabb54d214c140dfd9b854d214c140f7d99854d214c140ffd1854c5214c14097ddc3aeda96094097bdc4aed936094097dccb6a6336094097edc5aed988894097edc1aed9888940d3eebba219388940e3eeaaa222264540f3ce888ce2264540a6fdc6aa9956054097bdc4aed9360540a6fdc6aa99360540aeddc6aaa336054097f5c1aed9260540a6fdc6aa99260540aeedc6aaa226054097f9c0aeda95454097bdc4aed935454087fdc82e9925454087fdc32e99254540c7dcba8cd9254540a7ecca6622254540e3eda9a222254540a7f4ca6498154540fb658254981545409dbdc7aed5250540ebaeaaa222250540ebae886962250540fb8e888ce22505408efdc6aeda84c54087fdc52e9984c54087fdc82e9924c54087fdc52e9924c540c3fcbaa21924c5408dfdc72e9824c540e3eda9a22224c540a7f4ca649814c540fbc5824c9814c540) else (if i<3 then 0x150051001414008401c10001a4600890600124f2a8138078272e0e17caa00920c001081170f0700fe0641e95000441803a9022e101c002c42720350164084403b01b805e30378028561c03f8a00247f10000e05a03a8e88ca1c01e81d404c5e3309078f03051e03c650f9540ea12d003817ca01d005880e40110170c01c0600058c02287f101ac0f420000c8fe01103a90ca803450e01d48070e05c38170e074f005232a01c5c38500025bc5402f8c0e802602f8f8cdc5403c8d0021007040000200210000001082c8a10098400610004001006040053987838110004000000000002400d91420000000000003914202a011880218e39880b2042a3981a88c7802c81d4602f03f81400d44c268404c183f8400e06283f8c087f0801c20070b8702e1c0b8720fe270e41fc40420118804c02303f81f88043f8400e04743f8c00070d87020070801c20070809801e0231802ec3887f1a1fec38023198700462003840f8023110e40bc0231817806c023181f0046272a38700fe023201c24cc02b03241fdca8663c003c8ffa6632301e8ce1c0b8702e1c081fc04605f1811dc3807a01191c381d2a49988fe300289a1011fc220123f8802010903434730e8708e647f1e870202238789a1e268589a10799f8a82721f9578cc2721817bcab26683f928f1e5570e41fc947893339520fe463c191b4cc47f26743363992cb9e55326b916c7be3971a78b4c4ae2430fd85fc2d60870057e3be8df32f8f7a8bd1de12ee5753ba0dcbee216e4b62da9ad29675b31d912c4b613afa578abbb5cbadcd6d2b45590ac5d5e6ab5555aa1d4c6a254f3a6a52d692d477a2c50e684f4089f4cf2a75737f9b04d066453039724b165672ae94e49f64d725991d483a3df1dd8e5c6b233517b8b4c55e2a5119883c3a21930aa83f414a0670218013fc1fd6fcc7c9be05edef5d7ac3d4de9cf15767ba59d08e5870fb835bdcdb56c4b5a9a96d2c693b3ed96ac8964231c98c0c1a5fdaf3d746b845b2ad8164eaee574ab5d58aab3536a9a14c6a37505a77d39a9bb4db26c53589a74caa6413169864ba25bd2ba94b49ca4d125e91d485a4192028ef46ea32d18c8c145e22dd1648ad454228d13c88c43d21d50e086b43321850b8857429213509083640ba048fe67ba3c71d54e8673138f9bccddc6dc3651ae0d4c69433a9958c6e5fe2fc979cb765b62d21648b0056e2ae14c0a084d825c929c91045c21810447b03851990c8061c2fc1680a5c50a25912a093c47a238113081c4041f00ef073034018e0c485dc2ca1530a084f02200e405581c80720009efdc6aeda1609409dfdc7aeda54c94097fdc5aed826454097fdc3aed8264540c7febbaa9826454097fecc6e13264540c7febbaa99560540c7febbaa99360540b3fecc6558260540b3fecc64d8260540aefdc6aa95260540 else 0x5c0091001c04c200180b8402f004080100131002000e2001000c40020038a082100504048a371004c006200090200201708000823f80d005c400180b8404f0180800e100008600710004e00b101402026a3c08016102804026034111fc0220071800c00e200980b848320a0c805c201304201a371001c00620b68402c007100c8207228405e1000f42026081c8a111c808c4000684852142f011c400001708000003100bc00e2001805040070070800601d1015800620170400e0211017001e2003800c4048003880b800f2008c0420071015800620170158403000608028003100c0018200084080d0803406c28068407a1b1bb1e04c7800980986075011880ea10130404605010128200d02509c38103d040047003808d0fe40118400e023100bc00e200980184021003080460060068120603d006880f4100f0804407a080014050100e8024))
def f511l10 : Packing := (267,5,8,0,0,13,0,f511d10)
def f511h10 (i : Nat) : Nat := 0xdaf8a00ed4ac5a5b28d5c2c180010400000000094800d4a3ab37b040000a80c01334db6000160a8206f02d47000c34520000004c4ae12f00000000000c6439708d5e943daf0142c60280c0039f000b58a6b0e000002085b004154fca467db39b94ab5402527005000944c3c0baaee4e27bd1a49b000038b00000176de5800680001c3008008e62508221008629c011ac0a480e6
def f511d11 (i : Nat) : Nat := (if i<4 then (if i<2 then (if i<1 then 0x4ca11502ffadc26508a81dfd6613284540f7ed1099422a05ff5b54ca11503bfacaa6508a81fdd9553284540ff6aa899422a07fe5824ca11503ff2c2c4508a81ff960e2284540ffcaa711422a05ffabb68930502ffd5db04982817fe6e9824c140dff554c1260a077f9b960930503ff4d4444982817feaeda14c140f7f510d0a60a06ff9a268530503ff511342982817feaed814c140bff374c0a60a06ffaaa60530503bfcc930298281efe609814c140ffd444c0a60a05ffabb54530502ffcdd2a298281bfeaa9514c140ff7368a8a60a07fd9b354530503bfcc92a298281ffa889514c140ffe302a8a60a07fb98250530503fdca928298281ff6aed314c140ffb37098a60a07fd9a84c530503fecdaa6298281ff6695314c140ffb36498a60a07fd9a24c530503fecc126298281ff6549314c140bff57690a60a05ff9ba485305037fd55242982817fe6e1214c140eff33090a60a07bfa8848530502ffcdaa4298281fee551214c140ffb2a690a60a07ff1a884530503ff8d2c2298281ffc616114c140ffe34508a60a07ff18284530503ff8a9422982811ff6e2aa649408ffb6b55324a047fdb1aa992502bf75db31112815fbaed9388940e7dd10c9c44a057edb960e22503be6cc46711281ef3a223388940c7fd5544322a073de888cd915033f755444c8a81cfba222264540ef9c6711322a04efdb6aa9815033f6d4c44c0a811ff2e99254540cfdb53112a2a06bbeaaa2141503dcf44466a0a81cefa219250540df5d5511282a077ad9888941503dd744444a0a81beb6962250540ff1c6711282a047fcba661315031fed4d1098a811ff2e9924c540cfdb5311262a06fb6aa50531503ddb4428298a81fe54c9414c540ff4c44a0a62a063fda9a2121502bfb5db3108a815fdaed9584540e7ed10cac22a057f5b961611502fdb5daa908a81ded6615484540f76d10aa422a057f6bb64e115039fb4432708a81ddd9559384540afeb72c1c22a057f5b954e11503f9aaa2a708a81df56623384540f7ad1119c22a077d5958ce11503fab2ac6708a81fe55523384540afed76c9422a073f68864a11503bbb2ab2508a81ded5519284540efac66c9422a057f5b960a11502bfadcaa508a815fd6e53284540efcb3111422a07be68888a11503bf2cac4508a81fd99562284540ff4aa911422a077e59388a11503fe319c4508a81bfaaaa224c140efd33111260a07bea8888930503ddd4428298281fea889414c140bfb57698a60a06fdaaa4c530503beccc26298281ef6a21314c140bfb36a98a60a07f99544c530503becc926298281ff2889314c140ffa30298a60a07fd131485305037f95542298281dfc662114c140f7e51108a60a07f725584530503fd8aa42298281ff454e114c140efe32508a60a07fe222845305023deda554c9a81fe4505314c140 else 0x813ffaeda84c540cffb72d4262a067feaa661315035ff5551098a81cff6a6884c540cffb52d2a62a04ffebb695315033fedcb4a98a819ffaa9954c540cffb50caa62a073fe88655315037df552a898a81bef6a1544c540f77d10aa262a067fda9689315033ff5532498a819ff6a1924c540e7fd10c9262a067fda5649315027fe5d30498a819ff6a5824c540d7fb50c1262a067fda954931502fef5da6498a81bf7aa9324c540efbb7299262a077dda94c931503beecc26498a81ef7a21324c540efbb2a99262a07f9d544c931503fe6c126498a81bfbaaa224c540efdb5311262a06feda888931503bf6cc44498a81efba22224c540dfdb4b11262a077ed9588931503fd6aa44498a817fdaed814c540dfed54c0a62a077f5b960531503bfad4b0298a81bfd695814c540efeb2ac0a62a07fb55460531503bfac930298a81efd609814c540ffaa64c0a62a07fe62260531503fdb5528298a81fed6a1414c540ff6b4aa0a62a07fb5a250531503fdac128298a81fed549414c540affd76d4a42a067fda96a1215027ff5db5090a819ff6e5a848540affd76cc242a057fdba661215033ff5533090a81affaaa8848540e7fb5344242a067fda9695215027ff5db4a90a819ff6e5a548540cffb30d2a42a06bfe8869521502bff5db2a90a815ff6e99548540cffd54caa42a067fda8655215039ff4432a90a813ff6e98548540cffb52c2a42a05fbebb551215037df552a890a81bef6a15448540ef7b30aa242a07bbe88551215033fed4b4690a813ffaeda348540cffb72d1a42a067fd9868d215035ff4434690a819ff655a348540df7aa8d1a42a057febb64d21502bfedd32690a819ffaa99348540cffb50c9a42a073fe8864d215033fed2b2690a813ff6e98348540affb72c1a42a04ffdba54d21502bfedcaa690a81fcf5515348540dfbd5519a42a077dda98cd215037eed446690a81df76623348540f7bd1119a42a06fdda58cd21503beecac6690a81fe75523348540bfed7698a42a06ff6aa4c521503bfadca6290a81dfd6a53148540dfeb5098a42a077f5984c521503dfb4426290a81dfd6553148540ff6aa898a42a05ff6bb61611503bfadcb0b08a81dfd6159384540bfed76c1c22a077f5b960e11503bfacab0708a81fed5518384540bfed76a9c22a077f5b954e11502ffadc2a708a81dfd6615384540f7ed10a9c22a07f758554e11503feac1aa708a81ff56163384540efeb0ac9422a077f58364a11503bfaa9b2508a817fdaed8284540efeb72c1422a077f59560a11503fbb2ab0508a81fed5518284540efeb26c1422a07bf58360a11503feb19b0508a817fdaed5284540efeb72a9422a05ff5b854a11503bfacc2a508a81efda215284540efeb26a9422a07f755354a11503feb19aa508a81ff96095284540bfed7699422a077f5b9) else (if i<3 then 0x52a9a42a05ffdb854d215037fed42a690a81dff6615348540ffbb06a9a42a07ff5854c521503ffcd8b0498281ffe6e9814c140fff36ac0a60a07ff9a560530503ffcd930298281ffe689814c140fff2a4c0a60a07ff9b254530503ffcc12a298281ffe6e9214c140fff37090a60a07ff9a848530503ffcdaa4298281ffe695214c140fff30a90a60a04ffdb3aa9825027fed8d54c12815ffaeda960940cffd54d4b04a077dcb36a5825033fed4b46c12815ffaed9360940affb74c9b04a067feaa64d825037ef55466c1281df76a63360940cffb52d0b04a067fda96a1325027ff5db50992819ff6e5a84c940cffd54cc264a067fda969532502ff75db0499281bfbaa9824c940efdb72c1264a077eda9609325033fed4b42992817fbaed8388940efdb72c1c44a057febb60d91502bff5db04c8a819ff6e98264540cffd54c1322a073fd8360991503bef19b04c8a815ffaed3264540affb7099322a073fe884c991503bf6c1264c8a81dfb60e2264540affd76d4b02a067fda969581502bff5db2ac0a815ff6e99560540cffd54cab02a067fda968d81502bff5db26c0a815ff6e99360540cffd54c9b02a06fdeaa8cd81503beed4c66c0a81df76563360540cffb52d1302a057febb64981502bfedd324c0a819ffaa99260540efbc66c9302a05bfebb609815035ff55304c0a81cff6e58260540e7fb52c1302a073fd95609815039fec9b04c0a81ef78cd8260540cffb52a9302a07bed8254981502bfedca64c0a81efb6093260540dfdd5511302a077eda988981503bf6cac44c0a81dfb64e2260540ff9c6711302a04ffdb3aa9515027fed9554a8a815ffaeda954540cffd54d4aa2a05fbebb691515037df55348a8a819ff6a5a354540df7b48d1aa2a057febb64d51502bfedd326a8a819ffaa99354540dfbd5519aa2a077dda98cd51503fced2466a8a819ff6a5a254540df7b48d12a2a057febb64951502bfedd324a8a819ffaa99254540ef7b48c92a2a077de33649515027fe5d304a8a815ff6e58254540cffb52c12a2a057fdb94c9515037f755444a8a81dfb6a62254540efdb31112a2a07bee8888951503fd6d2444a8a81dfb64e2254540ff9c67112a2a05ff6bb605515037fb55302a8a81dfd6e58154540efeb52c0aa2a07fb5a460551503bfac9b02a8a81ff58cd8154540efeb24c0aa2a07bf58260551503fbaa9302a8a81ff98898154540bf7d76c1a82a05fbebb609415037df55304a0a81def6e58250540df7b4ac1282a07bbd8360941503fcf19b04a0a817efaed5250540df7d54a9282a077bd9854941503ddf442a4a0a81fe78cd5250540ff5b04a9282a05fbebb4c941502fdedc264a0a81eefa213250540ff5b0499282a07fad83889415027fedc55498a813ff6d6aa4c5409ffb6555262a067feaa6a5315033fed4b5098a else 0x22142fa84e504aa0213fba7da4f7a9e813bba74e4e4a9bf136fa6b64d4a99f1329a6364c3297c12e3a59e4ad2953128ba4fa49a292d124ba48648ba90d1211a3fa47a28f011cba37a46d28d611a3a30645a28a7113fa23e442a87210c9a15e425283d105fa0a240928020fef9f9e3ed27d00f7f9ed63d127950f039dae3ac274b0e7b9cb639027100e0b9bca372a6cc0d7d9ac6356a6970d0d99fe33326560c8598e2315a6240c33983e302a5e90b9f96e62d6259f0b1795ee2b5a55e0aa194f6299a5200a1f93f2274a4d3098592d62542498091b91f6238246008ab910a217a41c081d90061fa23de07a18f021d823a607258e0a1bc236806b58d3619ba32406218c02179a2e005998af2157a2a5052f8a06135a25b049588de1122217040187ce0f021d3038b86be0d12198031585f60b6a160029984fe0932116020583be06ca0cc01658266047a07f00dd818602a2047007380b200b20002fff5db42c1281bffaa9a160940dffb4ad0b04a06ffda368582503bfec9b42c1281bff6c5a84c940bffd76d2a64a06ffda869532503bfecc34a99281ffb6d5824c940ffdb4ac1264a07fedb1609325037fed434299281bff695a14c940ffdb04d0a64a077fdb260d91503bff5db04c8a81dff6d58264540effb66c1322a077fdb84c991503bfedaa64c8a81dff655a360540effb4ac9b02a077fd9568981503bfec9b44c0a81effaed8260540f7fb6ac1302a07bfdb3609815037ff552a4c0a81dff6a55260540effb26a9302a05ffebb4c9815037fedd264c0a81bffaa93260540effb7299302a077fda94c981503bfecaa64c0a81dff64da254540bffd76c12a2a06ffdba609515037ff55304a8a81dff6e58254540effb52c12a2a07fbda460951503bfec9b04a8a817ffaed3254540dffb74992a2a06ffeaa4c951503bfedca64a8a81dff6a53254540bffb70992a2a077fd984c951503fded2264a8a81ffb6093254540ffea64c0aa2a07fbdb260d41503fdf5db04a0a81fef6d58250540ff7b66c1282a07fbdb854941503fded9aa4a0a81fef60d5250540ff7b7099282a07fbdb54c941503bfecc34a98a81dff6a1954c540ff7b50aa262a05ffebb609315037fedd30498a81bffaa9824c540dffb4ac1262a077fd9560931503fdeaa30498a81ffd6c5824c540bffd76a9262a06ffeaa54931503bfed4aa498a81bff6a1524c540effb30a9262a07fed8254931503feedc26498a81ff76d5324c540ffeaa4c0a62a077fd9869521503bfed432a90a81bffaa98548540effb52c2a42a07fbda855121503bfed432690a81dff6959348540effb0ac9a42a05ffebb60d215037fedd30690a81bffaa98348540effb72c1a42a077fda960d215037fed2b0690a81dff6558348540ff7aa8c1a42a05ffebb54d215037ff552a690a81dff6e55348540effb)) else (if i<6 then (if i<5 then 0x8c48b4a98cc4fe5a4520da54c6627f2d0e139d2a10063313f980c691a9508031989fcd4a98cc4004fe461c240247678a54031c663b0e52a63373c1295105d9e01ef199918d4a8c8d8cdcf04a54c66646678220b920339b3c52a018e331d9ce95319b9e09ccf4a88fe304761ca5447f2639d2a30e63c139558721e299a1fcb0e6ca94cd0fe4062e55c78072a66873372a83953303f901881cf95699808c1098701fd1caac390e54cd8f05039646c78a66023042323c70e03d53332303f981f010995299808c8c81fcf0e4ca94cd8f0407f872e55075e46c7861c023403f91913372363c02fd2a011a39569991fc7caac388e74cc8fe5e55a66c7861cc732e3c323533639911ce9999191fc88e54ccc8d8f04473654a6647f263c53332a6399391b95399f8739579981c8e8f1c39cabc8c4cdca80fe7f3fbe6f3cbdf946f23be3a3c59f87ef0abe083bf5f7b6ef1bdd63b9df71eedd3dad3b4bf67aeca3d873aedf5a6eae3d523a89f4f6e983d1d3a0df3cee74bcdc399df2eee55bca1392df226e3e3c6c38c3f152e23bc3a385ff08ae0c3c0e3801efdadf63be237b5ef4ede4bbc23775eec2dd1bb96371dee12dbd3b7036d1ed6eda8bb443661ec9ad8e3b12360febead76bad73587eaf2d5abaab353bea4ed44ba7c34e3e9aad303a563491e8eed173a21342de832d0139f533d5e776ce839c6337de6c6cd2399a331fe616cbc396b32c1e542ca339393257e486c88b90a31ffe3cac7438d831a1e2f6c5838a03125e222c3db86b30c1e12ac21b83f3057e07ac05b8012fcfdf5ebe9b7cf2f83ded2bd2379d2f31de16bb337592e8bdccab9437152df1dbbab6db6d12d75daaab4bb6872cdbd976b2236342c2fd836b01b5f62bcbd74aae135b22b49d682ace358c2b03d5aeaaab54e2a63d486a82b4f229cfd376a6834c32971d2a2a4db48e2907d1e6a36345f289dd0faa1a341e2827d03ea0433f527c9cf5e9e533bd2765ceae9cf338826d7cd569a5b347267fccee99a332a2645cc7a98d330d25ffcbd696cb2d22589cade95532a32525c9f293ab2622497c8ee918b2212433c80e8fcb1ef23b7c7468df31b42347c6668c4b17922d7c5868a73135224fc452885310621f1c38a86db0c82157c286848b07e20e7c18e829b03d206bc096807affc1fd1bf3e7e5afc71f6dbea67c9af8c1ef1bda27a92f4b1e8dbcf27992f2e1e47bc66787af0b1e0dbbe67762ed91d8bbad67542e981d15ba0e73b2e631ca5b922717ae1c1c1db7ee6f42dd51b7db6ba6cf2d941b1fb5f26b62d5f1a91b4fa695ad1e1a1bb3ba6722cce1975b2da654ac931905b1ee635ac5e18a1b0de616ac17180dafce5f4abd61767aea65c22b6e16afad125972b1e162dac4a5842afe15edabb25712adb15adab4a5612ab21543aa2e5422a6e14bba94e527aa451475a8da5162a else 0x4686607a27f288010011c8c40024fe400802300d20d2391803849fc8340046002c8a4723c1c27f2391801840049fc8e460024fe285e080c0008806000444fe8bc227f200401193f906a068f0709cc9fc72364fe472391b673113f91c8008c8e42002c8a4fe327f27200a1819006889fe17858384804723003031a46180093f91c8c9fc0068dc90090bd46e227f240c1ca37201960e089fe17a8dc6030002223907c1003840349fc8e464fe48e01a385e0e0e13f91c8c9fc8e707064721c1c645239180c0068917828bc145e083b63983f83e835140a810817808c98e600e0bc0d4400d07f163981501e8118389401c11f1cc60bd0ff8f00fe0e00d46007c7387f00d202383f8390351001f1ce1fc11c84038e60de4304c7300d04706a2006d0e080349059501f41429991fce08e0a0ca94cd8e6500dc4da1c183fe39900823835171cc03c11c1a88c380e40fe347f05904247806a2e3c02c83a8d1cc1fd9501671cc108cc390e589b0fe400d026c78a46c7361c3021439b2a11953303fc3f9e1cc8629981f991a1fcc01a0f40f8046405f43905e023203f82481182f0351417991817c08c90e60920fe0bc046507a07c0231c3983f82481182f035181fd95299808c8084c8c0e04314cc0eb8f0ca8806fc7320107a2639803806835118702c380e54a807401b4cd8e67047a5461c47f07a2b0e626880369500e401e99808591b1e108e74ccc8c8fe0f45a54068007646a66c783003b26e398c01f1cd1fd934840389a2007c7364d1806e26a3f8e8731358dc602f8a800007a0eac380fe05e0ec9043e6700064607507f003076470e62a00002103fb3303b1c0c71528709fc9ccf8a84fe4e44a73200a78c5461c831310050e62a01893f951018731510c49fcb4e78a8c39cf04e55a1c47f45e272aa0030e423e3343f9a9511fd1786c388018f00534a98cc640d840a54c6647f2f2373983af2af3c00c1906f07319a9510011fcc0ffc380de0b40860ec0dc7c46c66a5440047f2f2ad0e23fa2f1395587319a1fc98cd4a802ec390fe5a5447f45e1b0e018e3352a23f9587295319b1e08c8c8f18cd4a88fe5a54c6647f180e83ff2a83d8310139b95510319a8710c51fcdc8c0220ff4a80c40ec6c66a5440047f272a82f43343f939569e18721fc9c39c8c0a40f90ccca80fe7a7886665487f263362a50e00023f940c79568731989fcb8cc4fe4723c6620da78a4661c831350e52363301893f971988e49fc6c3848b48d8cc4fe561cc66a46a78272ae3313f939129cf9571988029e18720c4f4e64014f0c8d8cd0626e55a1c240c6603127f310052363301893f959e31989189fc9caac38c8a8638cc4fe661ca73e5520dc66e783106b2363321893f969cd91b19b9e098ccc8c4fe305ec66a5427f200b90030e106d3c52a6331e05e9cd91880319a9529e0ec) else (if i<7 then 0x48fe0a0647864607fc6605900b47f381963c52a63323f940601ff19478cc0560bd8f0482561ca371018b0e03f63300d52323f9d8731968dc6c398cb46e301805061cc78a46c66303e10083e8e9501dc0e71e00da1fccc390bd8ca3018047254c6687f2806a2f6328c0381f00e41c01e8a01c0f807204c0f4502707c07507a202f0380050c0341fc0808001780ccc0fe04e04dcab4380eb8e60be800da1c07502e243fd2281383108003d1a8711fc09c600e167824505f00a203f81383a82663982f8131c17c02850620fe0220320720f4605e03983107f16dc6601103587f4b0e43fc1c8c1fe9e01e84001f8a0bc2db8cd4f006b0fe661ca45839192000383f83e01b141d81f21fc1d4140b8cc0fe0ec0400650fe0ea761c87f103f83b200c3f83a941ac0980941fc1d81c01e8e08007402c0ff8cc0146a54050032c66c73075303f80b03863300d02052323fa18702c38124004700f07c007292052a018811900601ee9509001fd8701e8ec380302041c6604264641707a3020e3352a33c03d1403c1d40d095187319b9e0e8720f820070806a3fa2f0c0341ed1fc78f01a1c47f4391d0e23fa1c8e8719150e4601a100d080c01e806832128700348001908002c8c0be00e04c0ea600307f00a011a1c47f3000805b3c50e23f941fe8711fc1d480a0ca98e64380ea500a654a1c0752006c8d881781f01901f880574f00bc4730fe0c8605e02b03687f064283e03d0320c1fc1481f18719501b00da1fd00f90cc0c8056ca90fe605e076080030200b83f81010002f018181fc09c09a87315017cc02ece74380340ae05e607f027026c5427fa1c080380b900023840018140fc09c0c44001e8b43886204e3a1c090000d02052311c818181fc09f15017c098a06348c04c060407f03902702fc54c660263b0e43fc1c8c1fc0e71989fc8e4200c08e41a100060401401903103907a2b0e01d03f82f523028031e3300a01ca98721fe0c460ea0bc04c0fe0720be098707f020000c54c6601e330e042029e04001e88c380bd8a98cc0d006b4f0706d61ca4627807a2b0e522891008341fc1f00d8a04e0f80be0f4444000707a036262a03f81381313fa2030e03d218721fc09c78cc0740fe07282ec8c0f47c6603964667807a283f83963362a139040188002000c0607e0280e4062802100603a07f07205e00ac5402e05cc660140445b0e43fc188c01e05c1fc1c80e410b1980fc1200d1918069805e0fe0bd8a800e0720be703f07fc5427fa1c031080383fe2a00381c82f813180501ff1989fc0c6918200e0178cc48ccf00f4543907c150e040601fd17860300fe862387f872150e03fa1c8e8701fd0c47438c8a261c0b0e051031500280c4190a88041a0640f806c507f61c023c5405f283f823e2a22033c30e03d1d87003440fe02b8a80150cccf00f470416 else (if i<8 then 0x8700c0050686406007e320007a83101e211c80983d0109001c83517804c80260420f40be4007021013190681803d0c04c0990e4641a8620f4026400d645239183d11c80f0131007809817c1e880060d003c303007c103d11c80f013101a017c0f5178803c04c0f4301801e026180683d02f0c0bc08c0371cc88e40be01e01a4a1c05e05f1e3990c23f8068079687003417c78e64300bc01e4218c4d637a1c263c01c8130e1cb1361fd1fc08ca08e0be261c04705f1810823e39811901788c817c64658e68fe08e0465201c4d162a01602f01cf3c0151b1500e40a817c80ec04f4f00ae0a0502706102a03d200d02b8280e9cc1840a80f480fe0e402a4e4014503400a02e1c2003f83901000a02f0051d0e40a852361673017a6627804a058310003f81501a131500a017b9e00e40a8c06805405c303b02701d02a00f07a00e04f402052300391c81a14034201a1c7302a058050210002381501a111001fc9781f001ca4720542007082880f80402f01c809980280e81fc0f69500cb198078020179403401a0940b0407f06ca5405e47f45e352a42003f80463323f980601fc0a460760fe0200400bc09e6a5484007fc6605e02000803687f4b0e43f8148c07c9501fc02319a1fcc41a8fe81a302d05ec1c027057052058382f33c00003a817941fc1f40e70709fc8e4c06383805c0ea05e5a4601401107f07d002039418403f82900682f017179541fc1c81be0e70709fc9c9006383805e0ea05c5e5580001407f072441002048418488ba0ba1c8c45c03707060020fe82f838407f02e03105e02f283f83b01f60e13f83a9b07012c034148160b4a80ec02e8300ea541807fc1c817200c040602ce78cc02e0940b05018031058181982102f02800a3236331c11c1099cc0ba950053198e03008e207f04203103dc6601a040a4647f481e81a73c633523169501fc14410c14011005f0709fd205e0684a94e7cf18cc6117417439188ba0be0e0c0051fd05f070801a8fe82f838447f472c1c182882d813834821141b809c1d410880bc0720d201640390690031d3c02f01c8c0e41b80981a88cf04e60ba016427f67805e052026283f83902c939021140cc16402c70620fe0e40a302e01a0847a1c07f43918018402d9e0448e0620fe0720ba016602b67805ea54026283b03f82c83a900009fc16402c80fe0ec0ea08440430590751b0e03f881641fc0a810884e60b54a84fe0ff438084700807fc46069063c6601600b47f482180b93fd2a03f82c8211e8711fd0e46006100147f163c0402d9e054388fe8e4347247f100084004203007a0000c84a1c20d000064233c50e03a8c03405c10c01c0019e31180ce871200201a291bc46a1c075201e90e62303a928711181d40988003236201e00dc7813102b280c03650e52a02902f63c1c0601fc405a8e604003 else 0x4c40b805045c822e02923605c054525e02602e646001293902f817006900b805005468e405201a00e414000703b01e2439015003d231001c0ec13c60028e405e08e447202a007047200c2390178069017c01c1f064bc00e04c064400707c1003804084c48040b802088bc02c06405c402e00810038040801c0ec13c600383805c022427201700dc1c02e2800e0e01700a100370700b805080020ea054304102e45e03220170150905e8dc09817c822f83848005c000066627f24047f417818a37c1c388b814813827e0e037980a401d178622e82e8720be403407c41700f201488b806e0e017819989fc0a505f07013ca00607e0843c78042026181322f017000911fc10809809c80548fece606805c50030690331b3c005821029109c91c810802880840de0d209e402600743918278210348379001c1bc13c60060d2084387204202687f20210130278d9e01a409860030e50fe300d0261114e3c084c48040d06064068222903410058195230c02c0e6918904801a0738cb46e4229c78122f01a0238d1fc18801c6c3800e0223a7805e102f828038011900b802917860e004e0a00ea402a02787f026075023321c80503d0d9150e41e8605e054046324005f0261d1b81302803a901f295090002888ff0ff46e0ec2800be0647a3724002684147f05030068130801c0a8400e8bc08e347f637075026241901801f8d8700c0050603c03a0f40be420003007a181b30e09))))
def f511l11 : Packing := (566,4,8,0,0,15,0,f511d11)
def f511h11 (i : Nat) : Nat := 0x716640a08da502615e765d40b92f3c83368bcec183b85e20de81600069d118080000001df670b2c5fa69d82ff2b586ee05715c5628e057700d7986e6c1d96700528190000000000000014d372a5427444800041e298bc18c04301604900006574000241a07a301b73000000000c600006de4422f48e564052992e80005378001679d10844d8000e3f0001a4351c0d375073d5171048283d84e3460a2e7248ee927655cd0bfd36528748df4eadc556e2421a1a984b80cc56d252894c24c61b4e6b20b006f0001547acaff770001824841f415209765648f0945000112189dd52480004318000c75f1fb481c802e492ce40000973a459d93f0000000003804e159caa000243e0000001616800007fa98746870a746969c4a11810f67625daf52d049c13e174633ea02660000147b398428538e90840999d77f42b3362952c2088f2429790284e2ca3b32640ef26c4e021f89600388000322587c05f651a049915000041ce00004e9472bd200000001b258001e7e602600010c205dc58f43100000000001735f5fec0918f996d00000005df260c0001f72fd606668000274800000020c8160047600039be71d583db78dce3662486874fade16244010a674548004ec6be53f182e2b91a3234b410950498c82f3906a82a8eda2e31e5f61a8bbf08d1f1355b8618103554c3da1c6c01b565b03017be4440d63844ded808098ee5b71c384b4c6c46cfc78e465dce20f94be00060df12ce11c939a12214ae13cc2de9b057c15c777a894052d64ca000000166a80f4a56f1a8000116a67d8000d36a957c5c70fe0002577f5a8000e27696597bd03942af5fc80d09de0006512a3701b7673720f039000000015d3c075453304b01e0003c70676b90a0003d5385a609855a0000e6bac5da6e800053090fab095009813686d55310b222f9582e3a9419e4d0000e03b5f40000001358fa0800000000004080a0aea0c0002d8ce4c912e884f4b0c2a75c3951b8cbc170001e3300000006101182b000d29996381c34c64813067f33217f957adba026a01990a2cd587ba07ba4ee1e20214505c364120a0e9c95065080c34624eae678001950800000000002147823b5c7a00000209e174756ee2d0196675000152e2cc5e2500000007992a398001250dc55a02bd4f835584455480022800002703020054500120908700042100200f830010d001648080083048200017902c05c080000002003500c0c00198080800a1a1800202281150010002001818d2e0099e0e181040420c07040c7033e413001404083085079300002001c1c0800e0458224209200008b1c141844d0084780
def f511d12 (i : Nat) : Nat := (if i<1 then 0x1f23654ccf8732ae660fe70e791b33e1cccc9503f9f23472ccf87239e664a91e1187039e55c8d9513307f3e1c0e5957236544cd1e0f8723c655c8d1ff2a2668e68de8f767dbff6c3d96f614d70b565d44f47fcfaf3afcd7730bca0b1eec6cb14ac38b0a6bff2f5dbc5aecfb8eee0ab5dace2b1bebe6acf2adfaa0aa25a6ca93fa35e885a01e77e9bd669898c259193464698f2a36d8c6e29d88aa1d884e60dc80f5fe07e39f1b7aa1e357709d447319c3d6ed1b4c6b65a6667f997564358b0614d8015e917315aa164b578d55a53c947f4f813834c412be498520f46f516b44650a640a0fb53cb0eae38c0dd33630d24331cc6a3008bbb2cc8ae02a64a1b26cc940236088620fc7ed1e6c7541c346bb19a460c16e856813d44a310c03e90e883190b1c25408081b0057810102bc05d0003ffeaa60940fff68d82503ffda160940fff6a132503ffda54c940fff68532503ffda560540fff68d81503ffda260540fff54981503ffd3260540fffaa951503ffda354540fff68951503ffd8254540fff4c951503ffeaa4c540fff6a131503ffda54c540fff68931503ffd824c540fff54931503ffda848540fff69521503ffd8548540fff68d21503ffd8348540fff54d21502ffeaa60940dff6a5825037fd9360940ff78cd82502ffeaa4c940dff6a532502ffda84c940dff66132503fed824c940ffb60e225037fd8364540dff609915037fd3264540bffaa9815037fda960540dff655815037fd9360540ff78cd815037fd9260540eff60981503fee2260540bffaa9515037fda954540fef691515037fd9354540ff78cd515037fd9254540ffb88951503ff58154540fef60d41503fbd8250540fef54941503fbd3250540bffaa9315037fda94c540bff6a1315037fd984c540effa2131502ffda54c540dff65531503fbd544c540dff64931503fdd324c540ffb88931503ff5814c540bffaa9215037fda948540bff6a1215037fd9848540effa2121502ffda548540dff65521503fbd5448540bff68d215037fd9348540ff78cd21503ff53148540ffd61611503ff58384540ffd54e11503ff58284540ffd54a11503ff53284540ffe68930503ff9824c140ffe68530503ff9814c140ffe54530503ff9214c1409ffaa9935027feaa64940df78cd925027fda9609409ff6a5325037ed9888940efba22225037ed9388940ff38ce225027feaa64540cffa21915037de3364540dfb889915027fda9605409ff6a551502fbeaa50540def66141503bbe8850540bef69541503f9e3350540def64941503fae22505409ff6a531503fb5414c5409ff6a5215037f59884540efda22115037f59584540fdd95611503fb55484540dfd64e11503fd63384540dfd64a11503fe62284540bfeaa9305037f9924c140ffa88930503fb9414c140ff64c530503ff2114c140 else (if i<2 then 0x11a33278016701a11c0b8430ff8732a0310e49e2234664e6109c0342387f4e61ca23466cf08a369cc0be1c4fe1d82d0750ff1193c2548cc109d46e3c0764a91ca33446cf080720073987588c8733c1c2f039ca91e10e032caa07a3307f50398bc1ff2305e4391fe3c2548cca0301ff0e2410bc91a3fc664a91e140602f039c399183e2548cc0c83fa83f827c38107234730bd9543e466cf0b01a9170e654caa0c4056468cc0cc3fac3f8760bd9190e0398e61d406e558cd9e1891439d530c591a330310039543d21c0fecaa71e006e554391ce1cc66cf090fe09c1907507209a39a468cd9e1400420e1c0f605c1c87a8cc9183fa800841c389e01c87a8cc9183fa68da4502e0e70e6460ea1f2332540641fd817b0e6460641d43d2548cd9e1346e3c0478e70e52a466cf080e40372ae468e61d50e678461c01b9183d039cf00c8e05c2007cc399193fa7806480fe17b236730be0e50e4548cd9e141003d839c8c1fc138318cc9e22a21c0f4c8f11ca1ca1c04f15233678407fce60341cc5404d1992367848010f605f0e07f8a80c41ca788cc9183d300087fc391501cc664f09183d243f80dc399182f8394e715233678500d08005c1c87fc39918392780629ce2a466100e01a1fe1ca730e5152336784153c399182387a0be9cc33454cf0a0649c90e05e8cc91b3c1c1905ecab19939a394399e10060192738cc179236783a724731982f2544399e0e061392548cc1792367838184729cc2f4664a99e0e0e406c730bd99c0787f0b295039281c87f0bd91b330728e68712a478046b07203639847caa1c8118424cc1fd40e7230728e595023a184391e32aa668e6c0fe03423e1cca81ca3c2464cd1cc212c1c80dc3991a3c0728e51cd2a2660f4bc3991b2a6670ff95733072461cc8d99b33c540fe601b1170e465c8d99f334540fe90001cf236660630722a07f4017c3991b33800ccd1503fa020047c8c0c7332784fe8722a2723673ccd1510e678321b081873236664fe0c539a72cce9e22a330e646ccc9cf33c54cf07c3991b2ae540fe178c03629e46ca80023c466cab1fd0e45e580d88b87023e46cab9523307f4c1b081873230478f119a3fa548bca036103236550630732a4660fe901b8732a03188d1983f9f0e655c8d9503f85e36550cb9190e6548cc1fcf957234668ff9510e4783878c39951234660fe6c39957236548cc1fcc1970e6464a91981907f3e1cc8c9523347f0651e0e0c70e646caa0032a4660fe84f18732ae46ca81983f9f0e000c8d152330320fe748a9cf23031ca88713fe554f1199591b39e548cd9550e67838174e78732a0314f09193fc66472ac399cf2a2468cd9e0d8732a27f48d1993c180ba45c3991b2a27f0629cd396554f11999873236544e795633678381748a9cf0e6464fe95233278064ac3991b39a548cc0cb3c else 0x4f01da2a41c0308e73c02a42738a90733c02a2e46ce69e13902f47315133678487f43811f3c02a282a0fe1c803a46cce97b3c047487f0f899823e780f468cc9c82f07548c0602f9f2ac1c0bc8e53987503017d11993905e4729500c05f3a720bf1c8131404a80620e05e07291a33678685f4721fc394390310713985e0de95233678685e0dc0e4210262839cf01d4262730be098f9cd39039cf017d2a0263a7204d1e03482a4a88701383988d19b3c302382a0e40983fa540b29cc1c86f88d19b3c343905e0f817c3d172a87f0bd9e32323900e8703aa40687f0bc09b3c0070be9183aa52a07f0f81e82f942807f4731e0118750e00a90e4390bd1cd2a466cf0f0301403f83948c1d438473082178134664a99e1c8713905e4720c82f980c2720bc9181905f32720bf1c81c8264380ca2a05e03a91a336786a730f81e82f902fa390fe1ca1ca1c0649cc2f0218a919b3c340c05f0fe0980f0328a89cc2f0398cc91b3c348d87f0bd91b330390550722a6785000c8d9cf330504e60c62a41c07a9e01a302005e0720a83fe4602e1cb3327308f1520e278014f0ff17a1ca730e50722a67846460020ab3305eccf9e023a020031c8c0a83e6670fe11d01ff2305e0559981cc734391533c28200310739180c0470f51510e07f56462360ab330548e611d0e6784a780649cd1cc544399e0e1781ce5400087014832caa07a3307f58390819183f8290bd1fe334784389522f30200290301781ce1cc8c1f12a4660641fd991823e730ea0e72ae780308000036330310a59553c03d030901a10418e548301fc0b8398389fd3c246473199c000238720621ff230170739520e4184fe9cf2a80d4f119a211c3fc1c0e595539c398cd9e1200006876c8c1043f8178cc9fc2f2784a90703ab8a9e460eb9cc0c2548cd9e111e023c1c87295233678387f0ed9cc3a80d0dc0e4134468cd9e1600139e5406387339c6688c9e019ab0e273ca9))
def f511l12 : Packing := (137,3,8,0,0,14,0,f511d12)
def f511h12 (i : Nat) : Nat := (if i<1 then 0x5d3a8462d204aa2cd2702d81c24000130eb8f709081384c51b917904820c1958c000381e29dc30ab41648f0b381d5a1e3af958d94e92582223dd2e0a3a2ae25800d7745923bd8727c30aae8000122912263ab0b7b9502f5ce60400003d16e4aafc6488a00001a00f2820001ca500000000414d513956fc20e000368f00b20000b6fa318261ad0e6a38d49bb879d9a300e6c83081d5344d6f34677d6b83af780f81f6a29c3b4000344bd60d000000000002837e08d1754e24c084f93e446b4f680000ba108a848080006ac2c5f5c65f91282aa71f243900000001813f48f80000001065280d001b000153740000000b0ed71dc203c0feaabc08c802905a712f3335744b49754066e62f818800062a0000000009b980d6e256081f09200000003a65dce4013400000000db769c604fdeb4cd7169cf8428000000002cde60b8f59003c218f1e584c99be13bad2916dcd891724a1506c7695ac61b3121e8bc41e1fbd6d28f495e48b6127d0a3a9f960ac251e7f825df0094195e79c464ede883020002654114b505fc50fe1b0213f1fa05480fa3a112bdad2f8ec89c2c69da7010c52804ea3c4000186a00002102e77a4e40000332ff05800060c60000065aa4a0000f3a2000360800000000009564500c80c23e177c78c9f90000d7e00003604e0431802456897bf3e7210d70770824ab687aa6f3b9ce427013720210000d8c04021b11adafcb6c25e847df16700015612259f985eaffa3e6c38247e7264358126484a1d092378085e6e34b04f859786f7da4d13c5872469648f8434284380628f4dc59383cee311a90aa7b07a88f79833321f70dd092dfb5120c415a88703a28aa303ce55a9bc202164e5d0a6992f06a08574f4f9930000c6be20a80000000000387b642f02b7c88c0000425a9de75b9c5898a61b93e0980000000196536880007234c09722d00d415df9a9c81c6cc57c31000000028266de31200112c0006dc17b638089c88711dea88e1020c7e066e88361dce3300000001e3af4fc1933621e678fa1bb80a0001418c25e98b90000000000000008a9682b1ab6acba0000681e0e7d551e0aa004885a3c0060039802003030640145000c3000300480800012280000028400107810a1d5a5043020b322000014000010020a87001408000580804e2c097022cd00022018d5c08008085028004389130824c0210b110f022c400041848e1a144030c0400f02194c2000060d0c200161cac30300001040e00101083c112020420200000000c04002161421d0020000001448202180021e483001818188061c08234202030004006201008018000850081d0008d42800c0c001061ca890e04008060400000007000008004ac0c0000a0000c001071206040090070022061c68100b43300e083001a040024c24680040070602108891a0c305061400b else (if i<2 then 0x4fd80ba1de304a10b5a9c3e0320d628000000000000ce2b8a212888192885855d11cfe437af8acccc2ba78960f029ec58c782730e851fbd322216fca9d05c110c0001441a4b9215ef50804c44a5d0294344c93d1572b5b15cf4c27457228550a5a16a445b269817e460194c2240b2a4cf429a6e13e4342c66b575ec2f5523aab858c54382057eddb56a9b700460000685000000003e07684dc00057f400000004b46e0d0705d088000035da24650cc3212481800050bac9783809a0b8000000020eea4ec0bfd27c253800058f2b44bc061208f0bbb3b285670e210e9e803d34fe5a0000000170cccfd28568311967821c80002831b728a8f80008b67f06f0e3a1aa4a4e24562ac991b51eea064eb649ff0825525cccd0000507bc5f250ddc8d000073a2286d1179a8e0002415e96851dc672b4d700004b364760318f8df0000e3fe4dea4ca501b866c80b80000000c2390cce0ae00000003304dd460000161a8a8c03611c40002312599f3a57e89143168381971480648b2977b1ac477c0002a1910240000e9e80000000367461114d60000000000000007a30000109afc59000060ab4a00000d32a00028228ce95430b190cc04cac8bae28c400070aaf8d0f7f3115f567490057c8e1901486147f2b6c348000a3c800008d5f123445c972c2a2906c0001a4888140000a8ce109800000001c2107f690f000081abd89a6918000933a255a6fd743581ea434dc53e8a8502267940000000000066300006c5e99a122d40003469f0f1a88424a8000000000004aa7c06027960f1eea0d0800d067cb6ff1a1d6c3143e0ecd24b7000071e000018bed160000000000000000000000000000001e19c00000000000d2b8aa0647da223c292e5ab2220001404dc308000927b87f30eb76060001c160a31542ee3407184294352e2a78000000021641277e8200006874fbb7f1776910000000183980001458908e000000020c3b1c1d288ae678a1b331b350070a06f70b5400ba711162739a07d5ee6d06ad96da1280001cf7c3cc0883c8a00002b42872ccc71087430d51b62aaf007933c82f6ca798c2ec3331976579c34da2e0000c98e21f738d8011cf880000000c73000018fa7a5a0626ed9198db856d5418a2cd5f00000000000480b41d835280ea50dda0ffb24f842a83f4ac8727b0b1d09b98f4d8050ae49dcfa9a322642098cfe3a5044e8fb401c4ba7020083ad1a1b0da11c222419d5111ff1cb2ad6823818eb49349679a4e46b15730981562b34f907323619f77bb255e6cd1960c137e45ff6bf592f5167b596caf2c76b1b476d400020dc700a70e3efcf9d30001a6942a9413a000148580002119d05d84a587e0506c089e2d80007cd789400000000258169b4720bef318dba8a8760b84a71029242c224037610400017480ef7e9879238a0b684e8ce671d else 0x5189343c6b80000016e576950121361392e361add019cc9b65656eda0230b8f7649b472d8a0280b407db0dd00e1c67b5cb4191ca6d9a4000045c010e80b2c492a2b00007a5400018a48dc280caf021c12212a283a13200000cb19923c3cdc2f54cdeb417264e0))
def f511d13 (i : Nat) : Nat := 0x781c85e91a730e666070549e148d8f01cc392308e2f4cc39cce2a4f0c54c781ca469ce54060390725519a786236a98f10e4e6394a8230cd3c291b54c78872460e6541ce5519a785a363c0e50e48d398722a0cc194f0b06c458705319646952661fc731ca67954787439234a9330e72accf3c201b114731961c91a661e2671fc545c39234e7334ce2a4f0706c451ce1c14e4695078954661fc5e6439234a83fcaa330f02f221c91a739525519a783c8c3c4a933c383fcab330e69ad33b237c06726c8147a3a38e5f07f8aa0be003ffb04a07ff4c940ffec0a81ffd51503ffa62a07ff48540bfec9a81fde33502ffb24a07fb88940bfec8a81fbd41503fec22a07fe4c140
def f511l13 : Packing := (14,2,8,0,0,11,0,f511d13)
def f511h13 (i : Nat) : Nat := 0x8a48d9945fb4ff012188a0404ddaa5132c6327e3c3fcef891c2a495510400044e9136d3443be68708d1d4000000000617886d47b0003510efa53a0007dff26788243c2929ae192d0071021e49b74e1a71266cb10c5b994e400180600025a66d7f040005196656000eab045388af206913160001a14840d80e43e000b0be0dcab7e71641bcf30b6000d8741e5896e12a8b311f65263d543742400054789b2941eda17a00038ac000c3e22180336625597117967500428e3b58c8001260d9288e32a1562d0f7d74000000627d17428d00d0008986c8577b18d15870c983fd91999c000563504c88d00e0003023c0d63e000936800000000068aad1400000028bdd4fe166160004d4aa140009198002eaef6a5288000001e139991110eddc5ae8044a006b53df2e0cc387981c0002d71271b1c997e61a8de505c08000000154860d8002c80c7478ed97f05a0005b6249c4e517c23180008748730005d91f1000068ce14a202b4e4bcf0e7e4202e1888000000a00112f86241f0309372c3483568559aa8ef21080a1a8e080909877eaab4b0300060028c200008f0802285180c4000010000000020006700194e18a3c082c00030000035c0440014180830644a050050284001810802140881018080
def f511d14 (i : Nat) : Nat := 0x1c231cca8662a99cf08ffd40
def f511l14 : Packing := (1,1,8,0,0,0,0,f511d14)
def f511h14 (i : Nat) : Nat := 0x335702283480000007842fd5002e000513b29150c5002cc00002e0000059fe8d000497d4ef0600000000c02241
def f511levels : Nat → Packing
  | 8 => f511l8
  | 9 => f511l9
  | 10 => f511l10
  | 11 => f511l11
  | 12 => f511l12
  | 13 => f511l13
  | 14 => f511l14
  | _ => emptyPacking
def f511index : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 1 3 0 5 1 0 f511h9
  | 10 => lookupWord 27 96 5 11 6 1 f511h10
  | 11 => lookupWord 135 475 7 14 9 1 f511h11
  | 12 => lookupWord 287 1013 7 15 10 1 f511h12
  | 13 => lookupWord 70 246 7 13 8 1 f511h13
  | 14 => lookupWord 10 41 3 9 4 1 f511h14
  | _ => fun _ => none
def f511 : Forest := ⟨511,14,fun i => f511S[i]?.getD (0,0),f511C,f511A,f511levels,f511index⟩
def f511c8 : List (Nat × Nat × Nat) := [(0,2,9)]
def f511c9 : List (Nat × Nat × Nat) := [(0,12,9),(12,24,10),(36,15,10)]
def f511c10 : List (Nat × Nat × Nat) := [(0,6,9),(6,24,10),(30,24,10),(54,24,10),(78,24,10),(102,24,10),(126,24,10),(150,15,10),(165,24,11),(189,24,11),(213,24,11),(237,24,11),(261,6,11)]
def f511c11 : List (Nat × Nat × Nat) := [(0,2,9),(2,24,10),(26,24,10),(50,24,10),(74,19,10),(93,24,11),(117,24,11),(141,24,11),(165,24,11),(189,24,11),(213,24,11),(237,24,11),(261,24,11),(285,24,11),(309,24,11),(333,24,11),(357,24,11),(381,24,11),(405,24,11),(429,14,11),(443,24,12),(467,24,12),(491,24,12),(515,24,12),(539,24,12),(563,3,12)]
def f511c12 : List (Nat × Nat × Nat) := [(0,24,10),(24,16,10),(40,24,11),(64,24,11),(88,21,11),(109,24,12),(133,4,12)]
def f511c13 : List (Nat × Nat × Nat) := [(0,8,10),(8,6,11)]
def f511c14 : List (Nat × Nat × Nat) := [(0,1,10)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem f31ok5 : block f31 5 0 (f31.levels 5).1=true := by
  apply chunkLevel f31c5 (by decide +kernel)
  apply listPieces_all (d:=0)
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem f31ok6 : block f31 6 0 (f31.levels 6).1=true := by
  apply chunkLevel f31c6 (by decide +kernel)
  apply listPieces_all (d:=0)
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
theorem f31tables : checkedTables f31 6 := by
  intro k le
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact f31ok5
  · exact f31ok6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem f189ok6 : block f189 6 0 (f189.levels 6).1=true := by
  apply chunkLevel f189c6 (by decide +kernel)
  apply listPieces_all (d:=0)
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem f189ok7 : block f189 7 0 (f189.levels 7).1=true := by
  apply chunkLevel f189c7 (by decide +kernel)
  apply listPieces_all (d:=0)
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
theorem f189tables : checkedTables f189 7 := by
  intro k le
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact f189ok6
  · exact f189ok7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem f215ok6 : block f215 6 0 (f215.levels 6).1=true := by
  apply chunkLevel f215c6 (by decide +kernel)
  apply listPieces_all (d:=0)
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
theorem f215tables : checkedTables f215 6 := by
  intro k le
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact f215ok6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem f243ok6 : block f243 6 0 (f243.levels 6).1=true := by
  apply chunkLevel f243c6 (by decide +kernel)
  apply listPieces_all (d:=0)
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
theorem f243tables : checkedTables f243 6 := by
  intro k le
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact f243ok6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem f191ok6 : block f191 6 0 (f191.levels 6).1=true := by
  apply chunkLevel f191c6 (by decide +kernel)
  apply listPieces_all (d:=0)
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem f191ok7 : block f191 7 0 (f191.levels 7).1=true := by
  apply chunkLevel f191c7 (by decide +kernel)
  apply listPieces_all (d:=3)
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem f191ok8 : block f191 8 0 (f191.levels 8).1=true := by
  apply chunkLevel f191c8 (by decide +kernel)
  apply listPieces_all (d:=4)
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem f191ok9 : block f191 9 0 (f191.levels 9).1=true := by
  apply chunkLevel f191c9 (by decide +kernel)
  apply listPieces_all (d:=2)
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem f191ok10 : block f191 10 0 (f191.levels 10).1=true := by
  apply chunkLevel f191c10 (by decide +kernel)
  apply listPieces_all (d:=0)
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
theorem f191tables : checkedTables f191 10 := by
  intro k le
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact f191ok6
  · exact f191ok7
  · exact f191ok8
  · exact f191ok9
  · exact f191ok10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem f319ok5 : block f319 5 0 (f319.levels 5).1=true := by
  apply chunkLevel f319c5 (by decide +kernel)
  apply listPieces_all (d:=0)
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem f319ok6 : block f319 6 0 (f319.levels 6).1=true := by
  apply chunkLevel f319c6 (by decide +kernel)
  apply listPieces_all (d:=2)
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem f319ok7 : block f319 7 0 (f319.levels 7).1=true := by
  apply chunkLevel f319c7 (by decide +kernel)
  apply listPieces_all (d:=4)
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem f319ok8 : block f319 8 0 (f319.levels 8).1=true := by
  apply chunkLevel f319c8 (by decide +kernel)
  apply listPieces_all (d:=5)
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem f319ok9 : block f319 9 0 (f319.levels 9).1=true := by
  apply chunkLevel f319c9 (by decide +kernel)
  apply listPieces_all (d:=1)
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem f319ok10 : block f319 10 0 (f319.levels 10).1=true := by
  apply chunkLevel f319c10 (by decide +kernel)
  apply listPieces_all (d:=0)
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
theorem f319tables : checkedTables f319 10 := by
  intro k le
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact f319ok5
  · exact f319ok6
  · exact f319ok7
  · exact f319ok8
  · exact f319ok9
  · exact f319ok10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem f351ok6 : block f351 6 0 (f351.levels 6).1=true := by
  apply chunkLevel f351c6 (by decide +kernel)
  apply listPieces_all (d:=0)
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem f351ok7 : block f351 7 0 (f351.levels 7).1=true := by
  apply chunkLevel f351c7 (by decide +kernel)
  apply listPieces_all (d:=1)
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem f351ok8 : block f351 8 0 (f351.levels 8).1=true := by
  apply chunkLevel f351c8 (by decide +kernel)
  apply listPieces_all (d:=2)
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem f351ok9 : block f351 9 0 (f351.levels 9).1=true := by
  apply chunkLevel f351c9 (by decide +kernel)
  apply listPieces_all (d:=1)
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem f351ok10 : block f351 10 0 (f351.levels 10).1=true := by
  apply chunkLevel f351c10 (by decide +kernel)
  apply listPieces_all (d:=0)
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
theorem f351tables : checkedTables f351 10 := by
  intro k le
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact f351ok6
  · exact f351ok7
  · exact f351ok8
  · exact f351ok9
  · exact f351ok10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem f383ok8 : block f383 8 0 (f383.levels 8).1=true := by
  apply chunkLevel f383c8 (by decide +kernel)
  apply listPieces_all (d:=2)
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem f383ok9 : block f383 9 0 (f383.levels 9).1=true := by
  apply chunkLevel f383c9 (by decide +kernel)
  apply listPieces_all (d:=5)
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem f383ok10 : block f383 10 0 (f383.levels 10).1=true := by
  apply chunkLevel f383c10 (by decide +kernel)
  apply listPieces_all (d:=4)
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem f383ok11 : block f383 11 0 (f383.levels 11).1=true := by
  apply chunkLevel f383c11 (by decide +kernel)
  apply listPieces_all (d:=1)
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem f383ok12 : block f383 12 0 (f383.levels 12).1=true := by
  apply chunkLevel f383c12 (by decide +kernel)
  apply listPieces_all (d:=0)
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
theorem f383tables : checkedTables f383 12 := by
  intro k le
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact f383ok8
  · exact f383ok9
  · exact f383ok10
  · exact f383ok11
  · exact f383ok12
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem f511ok8 : block f511 8 0 (f511.levels 8).1=true := by
  apply chunkLevel f511c8 (by decide +kernel)
  apply listPieces_all (d:=0)
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem f511ok9 : block f511 9 0 (f511.levels 9).1=true := by
  apply chunkLevel f511c9 (by decide +kernel)
  apply listPieces_all (d:=2)
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem f511ok10 : block f511 10 0 (f511.levels 10).1=true := by
  apply chunkLevel f511c10 (by decide +kernel)
  apply listPieces_all (d:=4)
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem f511ok11 : block f511 11 0 (f511.levels 11).1=true := by
  apply chunkLevel f511c11 (by decide +kernel)
  apply listPieces_all (d:=5)
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem f511ok12 : block f511 12 0 (f511.levels 12).1=true := by
  apply chunkLevel f511c12 (by decide +kernel)
  apply listPieces_all (d:=3)
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem f511ok13 : block f511 13 0 (f511.levels 13).1=true := by
  apply chunkLevel f511c13 (by decide +kernel)
  apply listPieces_all (d:=1)
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem f511ok14 : block f511 14 0 (f511.levels 14).1=true := by
  apply chunkLevel f511c14 (by decide +kernel)
  apply listPieces_all (d:=0)
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
theorem f511tables : checkedTables f511 14 := by
  intro k le
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact f511ok8
  · exact f511ok9
  · exact f511ok10
  · exact f511ok11
  · exact f511ok12
  · exact f511ok13
  · exact f511ok14
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem normalGraph : Lower (vars 511) (graphGoal 511) 15 :=
  lower_forest (g:=dead) (i:=0) (hints:=13438755073) (before_sound known383 valid383)
    geomdead tablesdead (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def allKnown := (511,15)::known383
theorem allValid : Known allKnown := by
  intro e he
  rcases List.mem_cons.mp he with rfl | he
  · exact normalGraph
  · exact valid383 _ he

theorem fromForest (g : Forest) (e : List (Nat × Nat)) (pr : augmentedKnown e) (hints : Nat)
    (normal : boundsBefore allKnown g.mask = g.cap+1)
    (geom : augmentedGeom g (boundsBefore allKnown) (boundsBefore e)=true)
    (tables : checkedTables g g.cap)
    (same : targetOf g=graphGoal g.mask) (prop : properB (graphGoal g.mask)=true)
    (check : rootCheck g.mask hints=true)
    (ib : indexedRoot g g.cap 0 (edgeBank g.mask) = true) :
    Lower (edgeBank g.mask) (graphGoal g.mask) (g.cap+1) := by
  have roots := augmentedRoots g (before_sound _ allValid) (augmentedPrior pr) geom tables g.cap (Nat.le_refl _)
  have ix (j : Nat) (ws : List Sig) (ok : indexedRoot g g.cap j ws=true) :
      Impossible (graphGoal g.mask) g.cap ws.toFinset := by
    simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at ok
    rw [←same,←sameWords_sound ok.2]
    exact roots j ok.1
  apply edgeBankLower (proper_of _ prop) check (normal ▸ before_sound allKnown allValid g.mask)
  exact ix 0 _ ib
def prior0 : List (Nat × Nat) := []
theorem sound0 : augmentedKnown prior0 := by simp [augmentedKnown,prior0]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem geo31 : augmentedGeom f31 (boundsBefore allKnown) (boundsBefore prior0)=true := by
  simp only [augmentedGeom,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,by decide +kernel⟩
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem augmented31 : Lower (edgeBank 31) (graphGoal 31) 7 :=
  fromForest f31 prior0 sound0 8452 (by decide +kernel) geo31 f31tables
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def prior31 := (31,7)::prior0
theorem sound31 : augmentedKnown prior31 := augmentedCons sound0 augmented31
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem augmented313 : Lower (edgeBank 313) (graphGoal 313) 7 :=
  lower_map (ms:=([81, 98, 118, 135] : List Nat).map swapRows) (by decide +kernel) (proper_of _ (by decide +kernel))
    (proper_of _ (by decide +kernel)) augmented31
def prior313 := (313,7)::prior31
theorem sound313 : augmentedKnown prior313 := augmentedCons sound31 augmented313
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem geo189 : augmentedGeom f189 (boundsBefore allKnown) (boundsBefore prior313)=true := by
  simp only [augmentedGeom,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,by decide +kernel⟩
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem augmented189 : Lower (edgeBank 189) (graphGoal 189) 8 :=
  fromForest f189 prior313 sound313 536879876 (by decide +kernel) geo189 f189tables
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def prior189 := (189,8)::prior313
theorem sound189 : augmentedKnown prior189 := augmentedCons sound313 augmented189
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem geo215 : augmentedGeom f215 (boundsBefore allKnown) (boundsBefore prior189)=true := by
  simp only [augmentedGeom,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,by decide +kernel⟩
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem augmented215 : Lower (edgeBank 215) (graphGoal 215) 7 :=
  fromForest f215 prior189 sound189 553648388 (by decide +kernel) geo215 f215tables
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def prior215 := (215,7)::prior189
theorem sound215 : augmentedKnown prior215 := augmentedCons sound189 augmented215
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem geo243 : augmentedGeom f243 (boundsBefore allKnown) (boundsBefore prior215)=true := by
  simp only [augmentedGeom,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,by decide +kernel⟩
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem augmented243 : Lower (edgeBank 243) (graphGoal 243) 7 :=
  fromForest f243 prior215 sound215 1358954500 (by decide +kernel) geo243 f243tables
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def prior243 := (243,7)::prior215
theorem sound243 : augmentedKnown prior243 := augmentedCons sound215 augmented243
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem augmented347 : Lower (edgeBank 347) (graphGoal 347) 8 :=
  lower_map (ms:=([81, 82, 101, 118, 135] : List Nat).map swapRows) (by decide +kernel) (proper_of _ (by decide +kernel))
    (proper_of _ (by decide +kernel)) augmented189
def prior347 := (347,8)::prior243
theorem sound347 : augmentedKnown prior347 := augmentedCons sound243 augmented347
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem augmented349 : Lower (edgeBank 349) (graphGoal 349) 7 :=
  lower_map (ms:=([64, 49, 98, 118, 135] : List Nat).map swapRows) (by decide +kernel) (proper_of _ (by decide +kernel))
    (proper_of _ (by decide +kernel)) augmented215
def prior349 := (349,7)::prior347
theorem sound349 : augmentedKnown prior349 := augmentedCons sound347 augmented349
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem augmented413 : Lower (edgeBank 413) (graphGoal 413) 7 :=
  lower_map (ms:=([64, 49, 134] : List Nat).map swapRows) (by decide +kernel) (proper_of _ (by decide +kernel))
    (proper_of _ (by decide +kernel)) augmented215
def prior413 := (413,7)::prior349
theorem sound413 : augmentedKnown prior413 := augmentedCons sound349 augmented413
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem augmented497 : Lower (edgeBank 497) (graphGoal 497) 7 :=
  lower_map (ms:=([49, 82, 131, 133, 118] : List Nat).map swapRows) (by decide +kernel) (proper_of _ (by decide +kernel))
    (proper_of _ (by decide +kernel)) augmented215
def prior497 := (497,7)::prior413
theorem sound497 : augmentedKnown prior497 := augmentedCons sound413 augmented497
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem geo191 : augmentedGeom f191 (boundsBefore allKnown) (boundsBefore prior497)=true := by
  simp only [augmentedGeom,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,by decide +kernel⟩
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem augmented191 : Lower (edgeBank 191) (graphGoal 191) 11 :=
  fromForest f191 prior497 sound497 536879364 (by decide +kernel) geo191 f191tables
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def prior191 := (191,11)::prior497
theorem sound191 : augmentedKnown prior191 := augmentedCons sound497 augmented191
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem geo319 : augmentedGeom f319 (boundsBefore allKnown) (boundsBefore prior191)=true := by
  simp only [augmentedGeom,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,by decide +kernel⟩
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem augmented319 : Lower (edgeBank 319) (graphGoal 319) 11 :=
  fromForest f319 prior191 sound191 12884910340 (by decide +kernel) geo319 f319tables
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def prior319 := (319,11)::prior191
theorem sound319 : augmentedKnown prior319 := augmentedCons sound191 augmented319
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem geo351 : augmentedGeom f351 (boundsBefore allKnown) (boundsBefore prior319)=true := by
  simp only [augmentedGeom,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,by decide +kernel⟩
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem augmented351 : Lower (edgeBank 351) (graphGoal 351) 11 :=
  fromForest f351 prior319 sound319 12901687556 (by decide +kernel) geo351 f351tables
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def prior351 := (351,11)::prior319
theorem sound351 : augmentedKnown prior351 := augmentedCons sound319 augmented351
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem augmented379 : Lower (edgeBank 379) (graphGoal 379) 11 :=
  lower_map (ms:=([81, 98, 118, 135] : List Nat).map swapRows) (by decide +kernel) (proper_of _ (by decide +kernel))
    (proper_of _ (by decide +kernel)) augmented191
def prior379 := (379,11)::prior351
theorem sound379 : augmentedKnown prior379 := augmentedCons sound351 augmented379
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem augmented445 : Lower (edgeBank 445) (graphGoal 445) 11 :=
  lower_map (ms:=([81, 130, 118] : List Nat).map swapRows) (by decide +kernel) (proper_of _ (by decide +kernel))
    (proper_of _ (by decide +kernel)) augmented351
def prior445 := (445,11)::prior379
theorem sound445 : augmentedKnown prior445 := augmentedCons sound379 augmented445
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem geo383 : augmentedGeom f383 (boundsBefore allKnown) (boundsBefore prior445)=true := by
  simp only [augmentedGeom,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,by decide +kernel⟩
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem augmented383 : Lower (edgeBank 383) (graphGoal 383) 13 :=
  fromForest f383 prior445 sound445 12901687556 (by decide +kernel) geo383 f383tables
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def prior383 := (383,13)::prior445
theorem sound383 : augmentedKnown prior383 := augmentedCons sound445 augmented383
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem augmented447 : Lower (edgeBank 447) (graphGoal 447) 13 :=
  lower_map (ms:=([81, 130, 118] : List Nat).map swapRows) (by decide +kernel) (proper_of _ (by decide +kernel))
    (proper_of _ (by decide +kernel)) augmented383
def prior447 := (447,13)::prior383
theorem sound447 : augmentedKnown prior447 := augmentedCons sound383 augmented447
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem geo511 : augmentedGeom f511 (boundsBefore allKnown) (boundsBefore prior447)=true := by
  simp only [augmentedGeom,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,by decide +kernel⟩
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem augmented511 : Lower (edgeBank 511) (graphGoal 511) 15 :=
  fromForest f511 prior447 sound447 13438558468 (by decide +kernel) geo511 f511tables
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem finish (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (first : ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 4))
    (computes : PEqualNP.MetaComplexity.circuitFun 9 C = edge) (small : C.size ≤ 15) :
    False := by
  have headEq : (execute C.gates inputs).getD 9 zero = bin true (inputs.getD 0 zero) (inputs.getD 4 zero) := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C legal 9 r).trans ((first (sample r)).trans (bit_bin r true (inputs.getD 0 zero) (inputs.getD 4 zero)).symm)
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
    exact False.elim ((by decide +kernel : bin true (inputs.getD 0 zero) (inputs.getD 4 zero) ≠ zero) headEq.symm)
  | cons g gs =>
    have eq0 : gv inputs g = bin true (inputs.getD 0 zero) (inputs.getD 4 zero) := by
      rw [hgs] at headEq
      change (execute gs (inputs++[gv inputs g])).getD 9 zero = bin true (inputs.getD 0 zero) (inputs.getD 4 zero) at headEq
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
    have gu : graphGoal 511 = graph := by decide +kernel
    have xu : edgeBank 511 = inputs ++ [bin true (inputs.getD 0 zero) (inputs.getD 4 zero)] := by decide +kernel
    have lower := augmented511
    rw [gu,xu] at lower
    have b := subsumed graph_proper run hs lower
    omega

theorem publishedLower : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 4)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size := by
  intro C legal first computes
  by_contra! small
  exact PEqualNP.Outside.L_meta_4911_aux.finish C legal first computes (by omega)


theorem old_wire {α : Type} (f : List Bool → α → Bool) (gs : List α)
    (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl (fun s g => s ++ [f s g]) w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (gs.foldl _ (w ++ [f w g])).getD i false = _
    rw [ih _ (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

end PEqualNP.Outside.L_meta_4911_aux

namespace PEqualNP.Outside.L_meta_4911_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
lemma pairBound (C : Circuit) (a b : Fin 9) (fan : FanInTwo C)
    (correct : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 4, x a || x b]) = PEqualNP.Outside.L_meta_4911_aux.edge x) :
    14 ≤ C.size := by
  let I : Gate := ⟨.or,[0,4]⟩
  let J : Gate := ⟨.or,[a.val,b.val]⟩
  let D : Circuit := ⟨I :: J :: C.gates,C.output⟩
  let step (w : List Bool) (g : Gate) := g.op.eval (g.inputs.map fun i => w.getD i false)
  have basis : FanInTwo D := by
    intro g hg
    change g ∈ I :: J :: C.gates at hg
    rcases List.mem_cons.mp hg with rfl|hg
    · simp [I]
    rcases List.mem_cons.mp hg with rfl|hg
    · simp [J]
    exact fan g hg
  have one (x : Fin 9 → Bool) : step (List.ofFn x) I = (x 0 || x 4) := by
    simp [step,I,GateOp.eval,List.getD_eq_getElem?_getD]
  have first (x : Fin 9 → Bool) : (D.wires (List.ofFn x)).getD 9 false = (x 0 || x 4) := by
    change ((J :: C.gates).foldl (fun w g => w ++ [step w g]) (List.ofFn x ++ [step (List.ofFn x) I])).getD 9 false = _
    rw [PEqualNP.Outside.L_meta_4911_aux.old_wire step _ _ _ (by simp),one]
    simp [List.getD_eq_getElem?_getD]
  have bound := PEqualNP.Outside.L_meta_4911_aux.publishedLower D basis first (by
    funext x
    change (C.gates.foldl (fun w g => w ++ [step w g]) ((List.ofFn x ++ [step (List.ofFn x) I]) ++ [step (List.ofFn x ++ [step (List.ofFn x) I]) J])).getD C.output false = _
    rw [one]
    have two : step (List.ofFn x ++ [x 0 || x 4]) J = (x a || x b) := by
      simp only [step,J,GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,Bool.or_false]
      have rd (j : Fin 9) : (List.ofFn x ++ [x 0 || x 4]).getD j.val false = x j := by
        rw [List.getD_eq_getElem?_getD,List.getElem?_append_left (show j.val < (List.ofFn x).length by simpa only [List.length_ofFn] using j.isLt)]
        simp only [List.getElem?_ofFn,dite_eq_left j.isLt,Option.getD_some]
      simp only [rd a,rd b,id_eq]
    rw [two]
    exact correct x)
  change 16 ≤ C.gates.length+1+1 at bound
  change 14 ≤ C.gates.length
  omega

end PEqualNP.Outside.L_meta_4911_aux

theorem PEqualNP.Outside.L_meta_4911 : ∀ (x1 : Finset (Fin (9 : ℕ))),   x1.card = (2 : ℕ) →     Disjoint x1 {(0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))} →       ∀ (x4 : Fin (13 : ℕ) → Fin (3 : ℕ) × Fin (3 : ℕ) × Fin (25 : ℕ) × Fin (25 : ℕ)) (x5 : Fin (25 : ℕ)),         have x6 : Fin (3 : ℕ) × Fin (3 : ℕ) × Fin (25 : ℕ) × Fin (25 : ℕ) → PEqualNP.CircuitLowerBounds.Gate := fun (x6 : Fin (3 : ℕ) × Fin (3 : ℕ) × Fin (25 : ℕ) × Fin (25 : ℕ)) => { op := if x6.1 = (0 : Fin (3 : ℕ)) then PEqualNP.CircuitLowerBounds.GateOp.and else if x6.1 = (1 : Fin (3 : ℕ)) then PEqualNP.CircuitLowerBounds.GateOp.or else PEqualNP.CircuitLowerBounds.GateOp.not, inputs := List.take ↑x6.2.1 [↑x6.2.2.1, ↑x6.2.2.2] : PEqualNP.CircuitLowerBounds.Gate };         have x7 : PEqualNP.CircuitLowerBounds.Circuit := { gates := List.ofFn fun (x7 : Fin (13 : ℕ)) => x6 (x4 x7), output := ↑x5 : PEqualNP.CircuitLowerBounds.Circuit };         ∃ (x8 : Fin (9 : ℕ) → Bool), x7.eval (List.ofFn x8 ++ [x8 (0 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)), Decidable.decide (∃ x9 ∈ x1, x8 x9 = Bool.true)]) ≠ [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x9 : ℕ) => x8 (Fin.ofNat (9 : ℕ) (x9 / (10 : ℕ))) && x8 (Fin.ofNat (9 : ℕ) (x9 % (10 : ℕ))) := by
  intro S pair _ code out decode C
  by_contra! correct
  obtain ⟨a,b,_,rfl⟩ := Finset.card_eq_two.mp pair
  have basis : PEqualNP.MetaComplexity.FanInTwo C := by
    intro g hg
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hg
    simp only [decode]
    split <;> first | (split <;> simp) | simp
  have bound := PEqualNP.Outside.L_meta_4911_aux.pairBound C a b basis (by
    intro x
    have ed (y : Fin 9 → Bool) : [1,12,23,34,40,5,16,27,38,57,68,85].any (fun t : ℕ => y (Fin.ofNat 9 (t / 10)) && y (Fin.ofNat 9 (t % 10))) = PEqualNP.Outside.L_meta_4911_aux.edge y := by
      simp only [List.any_cons,List.any_nil,Bool.or_false,PEqualNP.Outside.L_meta_4911_aux.edge,Bool.or_assoc]
      rfl
    rw [←ed x]
    simpa using correct x)
  change 14 ≤ (List.ofFn _).length at bound
  simp at bound
