import PEqualNP.Defs

-- Adapted from the locally checker-accepted L-meta-1677 source, SHA-256
-- 65e331d2ceb61e70d00216f4e25e753032e13f5d57dbb21bf4de214e1b5b6854.
-- Specializing the extraction to AND and OR removes all NOT branches from the certificate.

-- The live-wire framework and induced-subgraph lower bounds build on the checked
-- L-meta-1667 and L-meta-1920 proofs, including PressF10’s work in PR 4332 (Apache-2.0).
namespace PEqualNP.Outside.L_meta_4362
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

def witnessMono (w : List Sig) (z : Sig) : Prop :=
  (∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)

private lemma bin_repMono {w a b} (d : Bool) (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ witnessMono w (bin d a b) := by
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

private lemma gate_repMono (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length≤2) :
    represented w (gv w g) ∨ witnessMono w (gv w g) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  cases l with
  | nil =>
    rcases ho with rfl | rfl
    · exact Or.inl ro
    · exact Or.inl rz

  | cons i l =>
    cases l with
    | nil =>
      rcases ho with rfl | rfl
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using Or.inl (b := witnessMono w (w.getD i zero)) (get_rep w i)
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using Or.inl (b := witnessMono w (w.getD i zero)) (get_rep w i)

    | cons j l =>
      cases l with
      | cons a l => simp at hl
      | nil =>
        rcases ho with rfl | rfl
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using bin_repMono false (get_rep w i) (get_rep w j)
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using bin_repMono true (get_rep w i) (get_rep w j)


-- Remove a last computed signal from a backward derivation. A gate whose value
-- is already available, or is unused by the suffix, needs no entry in the plan.
private lemma pull_gateMono {w : List Sig} {z : Sig} {k S} (h : Live target k 0 S)
    (hz : represented w z ∨ witnessMono w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' S', k' ≤ k+1 ∧ Live target k' 0 S' ∧ ∀ a ∈ S', a ∈ w := by
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
        have ht : Live target k 0 (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
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

private lemma extractMono (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length≤2)
    (hp : proper target) (hout : target ∈ execute gs w) :
    ∃ k S, k ≤ gs.length ∧ Live target k 0 S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,T,hl,hu,hT⟩ := pull_gateMono ht (gate_repMono w g (legal g (by simp))) hs
    exact ⟨l,T,by simp; omega,hu,hT⟩

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
theorem s191_7_0p0 : block g191 7 0 4=true := by decide +kernel
theorem s191_7_0p1 : block g191 7 4 4=true := by decide +kernel
theorem s191_7_0p2 : block g191 7 8 4=true := by decide +kernel
theorem s191_7_0p3 : block g191 7 12 1=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem s191_7_0 : block g191 7 0 13=true := (@block_merge g191 7 0 8 5 (@block_merge g191 7 0 4 4 s191_7_0p0 s191_7_0p1) (@block_merge g191 7 8 4 1 s191_7_0p2 s191_7_0p3))
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_7_1p0 : block g191 7 13 4=true := by decide +kernel
theorem s191_7_1p1 : block g191 7 17 4=true := by decide +kernel
theorem s191_7_1p2 : block g191 7 21 4=true := by decide +kernel
theorem s191_7_1p3 : block g191 7 25 3=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem s191_7_1 : block g191 7 13 15=true := (@block_merge g191 7 13 8 7 (@block_merge g191 7 13 4 4 s191_7_1p0 s191_7_1p1) (@block_merge g191 7 21 4 3 s191_7_1p2 s191_7_1p3))
theorem bl191_7 : block g191 7 0 28 = true := (@block_merge g191 7 0 13 15 s191_7_0 s191_7_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem s191_8_0p0 : block g191 8 0 4=true := by decide +kernel
theorem s191_8_0p1 : block g191 8 4 3=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem s191_8_0 : block g191 8 0 7=true := (@block_merge g191 8 0 4 3 s191_8_0p0 s191_8_0p1)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_1p0 : block g191 8 7 4=true := by decide +kernel
theorem s191_8_1p1 : block g191 8 11 4=true := by decide +kernel
theorem s191_8_1p2 : block g191 8 15 4=true := by decide +kernel
theorem s191_8_1p3 : block g191 8 19 4=true := by decide +kernel
theorem s191_8_1p4 : block g191 8 23 4=true := by decide +kernel
theorem s191_8_1p5 : block g191 8 27 4=true := by decide +kernel
theorem s191_8_1p6 : block g191 8 31 4=true := by decide +kernel
theorem s191_8_1p7 : block g191 8 35 4=true := by decide +kernel
theorem s191_8_1p8 : block g191 8 39 4=true := by decide +kernel
theorem s191_8_1p9 : block g191 8 43 4=true := by decide +kernel
theorem s191_8_1p10 : block g191 8 47 4=true := by decide +kernel
theorem s191_8_1p11 : block g191 8 51 4=true := by decide +kernel
theorem s191_8_1p12 : block g191 8 55 4=true := by decide +kernel
theorem s191_8_1p13 : block g191 8 59 4=true := by decide +kernel
theorem s191_8_1p14 : block g191 8 63 4=true := by decide +kernel
theorem s191_8_1p15 : block g191 8 67 1=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem s191_8_1 : block g191 8 7 61=true := (@block_merge g191 8 7 32 29 (@block_merge g191 8 7 16 16 (@block_merge g191 8 7 8 8 (@block_merge g191 8 7 4 4 s191_8_1p0 s191_8_1p1) (@block_merge g191 8 15 4 4 s191_8_1p2 s191_8_1p3)) (@block_merge g191 8 23 8 8 (@block_merge g191 8 23 4 4 s191_8_1p4 s191_8_1p5) (@block_merge g191 8 31 4 4 s191_8_1p6 s191_8_1p7))) (@block_merge g191 8 39 16 13 (@block_merge g191 8 39 8 8 (@block_merge g191 8 39 4 4 s191_8_1p8 s191_8_1p9) (@block_merge g191 8 47 4 4 s191_8_1p10 s191_8_1p11)) (@block_merge g191 8 55 8 5 (@block_merge g191 8 55 4 4 s191_8_1p12 s191_8_1p13) (@block_merge g191 8 63 4 1 s191_8_1p14 s191_8_1p15))))
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_2p0 : block g191 8 68 4=true := by decide +kernel
theorem s191_8_2p1 : block g191 8 72 4=true := by decide +kernel
theorem s191_8_2p2 : block g191 8 76 4=true := by decide +kernel
theorem s191_8_2p3 : block g191 8 80 4=true := by decide +kernel
theorem s191_8_2p4 : block g191 8 84 4=true := by decide +kernel
theorem s191_8_2p5 : block g191 8 88 4=true := by decide +kernel
theorem s191_8_2p6 : block g191 8 92 4=true := by decide +kernel
theorem s191_8_2p7 : block g191 8 96 4=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem s191_8_2 : block g191 8 68 32=true := (@block_merge g191 8 68 16 16 (@block_merge g191 8 68 8 8 (@block_merge g191 8 68 4 4 s191_8_2p0 s191_8_2p1) (@block_merge g191 8 76 4 4 s191_8_2p2 s191_8_2p3)) (@block_merge g191 8 84 8 8 (@block_merge g191 8 84 4 4 s191_8_2p4 s191_8_2p5) (@block_merge g191 8 92 4 4 s191_8_2p6 s191_8_2p7)))
theorem bl191_8 : block g191 8 0 100 = true := (@block_merge g191 8 0 68 32 (@block_merge g191 8 0 7 61 s191_8_0 s191_8_1) s191_8_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem s191_9_0 : block g191 9 0 3=true := by
  decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_9_1p0 : block g191 9 3 4=true := by decide +kernel
theorem s191_9_1p1 : block g191 9 7 4=true := by decide +kernel
theorem s191_9_1p2 : block g191 9 11 1=true := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem s191_9_1 : block g191 9 3 9=true := (@block_merge g191 9 3 4 5 s191_9_1p0 (@block_merge g191 9 7 4 1 s191_9_1p1 s191_9_1p2))
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

end PEqualNP.Outside.L_meta_4362

namespace PEqualNP.Outside.L_meta_4362.RankBase

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
end PEqualNP.Outside.L_meta_4362.RankBase

namespace PEqualNP.Outside.L_meta_4362.FrontRanks

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
end PEqualNP.Outside.L_meta_4362.FrontRanks

namespace PEqualNP.Outside.L_meta_4362.FrontRanks
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

def covered {n} (mask : Nat) : Rule n → Bool
 | .square i j .. => mask.testBit i.val && mask.testBit j.val
 | .cube i j k .. => mask.testBit i.val && mask.testBit j.val && mask.testBit k.val

def coords (n mask : Nat) := (List.range n).filter mask.testBit

def col (r : Nat) (s : List Nat) (i : Nat) :=
 let u := s.idxOf i
 (plane r 0 s.length u,plane r 1 s.length u,plane r 2 s.length u)

def fast {n} (r mask : Nat) (rules : List (Rule n)) :=
 if 1 ≤ r && r ≤ 5 && n ≤ 12 && rules.all (covered mask) then
   let s := coords n mask
   let all := full (r^s.length)
   let cols := (List.range n).map (col r s)
   rules.foldl (fun a q => a &&& allowed all cols q) all != 0
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

theorem sound {n r mask} {label : Fin n → Fin r} {rules : List (Rule n)}
    (good : ∀ q ∈ rules, accepts label q = true) : fast r mask rules = true := by
  unfold fast
  split
  next bound =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at bound
    let s := coords n mask
    let f (i : Nat) := if h : s.getD i n < n then (label ⟨_,h⟩).val else 0
    have hf (i) (_hi : i < s.length) : f i < r := by
      unfold f
      split
      · exact (label _).isLt
      · omega
    let ix := index r f s.length
    let all := full (r^s.length)
    let cols := (List.range n).map (col r s)
    have ha : all.testBit ix = true := by simp [all,full_bit,ix,index_lt hf]
    have lookup (i : Fin n) : cols.getD i (0,0,0) = col r s i := by
      simp [cols,List.getD_eq_getElem?_getD,i.isLt]
    have use (i : Fin n) (hit : mask.testBit i.val = true) : i.val ∈ s :=
      List.mem_filter.mpr ⟨List.mem_range.mpr i.isLt,hit⟩
    have val (i : Fin n) (hi : i.val ∈ s) (bit) :
        (plane r bit s.length (s.idxOf i.val)).testBit ix = (label i).val.testBit bit := by
      have atI : s.getD (s.idxOf i.val) n = i.val := by
        simp [List.getD_eq_getElem?_getD,List.getElem?_idxOf hi]
      rw [plane_at bit hf (List.idxOf_lt_length_of_mem hi)]
      simp only [f,atI,dif_pos i.isLt]
    let v (i : Fin n) : Fin 5 := ⟨(label i).val,by have := (label i).isLt; omega⟩
    have hq (q : Rule n) (hq : q ∈ rules) : (allowed all cols q).testBit ix = true := by
      have g := good q hq
      have pass := List.all_eq_true.mp bound.2 q hq
      cases q with
      | square i j a o =>
        simp only [covered,Bool.and_eq_true] at pass
        have hi := use i pass.1
        have hj := use j pass.2
        simp only [allowed,lookup,col,Nat.testBit_or,Nat.testBit_xor,val i hi,val j hj]
        rw [binary_diff (v i) (v j)]
        exact g
      | cube i j k a b c bit sign =>
        simp only [covered,Bool.and_eq_true] at pass
        have hi := use i pass.1.1
        have hj := use j pass.1.2
        have hk := use k pass.2
        simp only [allowed,lookup,col,Nat.testBit_or,Nat.testBit_and,Nat.testBit_xor,val i hi,val j hj,val k hk,ha,Bool.true_xor]
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

def nibbleD (u : Nat) := ((u * ((1 <<< 1533)+(1 <<< 1022)+(1 <<< 511)+1)) &&&
  ((1 <<< 1536)+(1 <<< 1024)+(1 <<< 512)+1))*lane
def nibble (u : Nat) := nibbleD (u % 16)
theorem tab : ∀ u : Fin 16, nibbleD u.val = ColorBits.span 512 (fun d => if u.val.testBit d then lane else 0) 4 := by decide +kernel
theorem bd (u : Nat) : ColorBits.Bounded (nibble u) 2048 := by
  rw [nibble,tab (⟨u % 16,Nat.mod_lt _ (by decide)⟩ : Fin 16)]
  apply ColorBits.span_out (w:=512)
  intro d j hj
  split <;> simp [lane,Nat.shiftLeft_eq,show ¬j<512 by omega]
def spread (x : Nat) := ColorBits.span 2048 (fun n => nibble (x >>> (n*4))) 3
theorem atLane (x i j : Nat) (hi : i<12) (hj:j<512) :
 (spread x).testBit (i*512+j) = x.testBit i := by
 have h : i*512+j = (i/4)*2048+((i % 4)*512+j) := by omega
 rw [h,spread,ColorBits.span_at (fun d => bd _) (by omega) 3 (by omega)]
 unfold nibble
 rw [tab (⟨_,Nat.mod_lt _ (by decide)⟩ : Fin 16)]
 rw [ColorBits.span_at (w:=512) (fun d => by
   intro l hl
   split <;> simp [lane,Nat.shiftLeft_eq,show ¬l<512 by omega]) hj 4 (by omega)]
 simp only [Fin.val_mk]
 have hm : ((x >>> (i/4*4)) % 16).testBit (i % 4) = x.testBit i := by
   rw [show 16 = 2^4 by decide,Nat.testBit_mod_two_pow,Nat.testBit_shiftRight]
   simp [show i % 4 < 4 by omega,show i/4*4 + i % 4 = i by omega]
 rw [hm]
 cases x.testBit i <;> simp [lane,Nat.shiftLeft_eq,hj]
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
     change (spread y).testBit _ = _
     rw [atLane y i.val j (by omega) lim]
     simp [y,Nat.testBit_and,ColorBits.full_bit,i.isLt]
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

def rankCheck (target : Word) (mono : Bool) (ws : List Word) (r code count scope : Nat) : Bool :=
  let rules := readRules ws.length count code
  (ws.length ≤ 12) && rules.all (PackedRows.check (PackedRows.matrix ws) (ColorBits.full ws.length) target.toNat mono) && !(ColorBits.fast (r+1) scope rules)

theorem rankCheck_sound {target : Word} {mono : Bool} {ws : List Word} {r code count scope : Nat}
    (F : (Fin ws.length → Bool) → Bool)
    (agree : ∀ p : Fin 512, F (fun i => (ws.get i).getLsbD p.val) = target.getLsbD p.val)
    (mon : mono = true → Monotone F) (group : Grouping r F)
    (h : rankCheck target mono ws r code count scope = true) : False := by
  let rules := readRules ws.length count code
  have pass : (ws.length ≤ 12 ∧ rules.all (PackedRows.check (PackedRows.matrix ws) (ColorBits.full ws.length) target.toNat mono) = true) ∧ ColorBits.fast (r+1) scope rules = false := by
    simpa only [rankCheck, Bool.and_eq_true, Bool.not_eq_true',decide_eq_true_eq] using h
  have accept (claim : Rule ws.length) (hc : claim ∈ rules) : accepts group.label claim = true :=
    checksRule_sound F agree mon group (PackedRows.check_sound target mono ws pass.1.1 claim (List.all_eq_true.mp pass.1.2 _ hc))
  have found : ColorBits.fast (r+1) scope rules = true :=
    ColorBits.sound (r:=r+1) (label:=group.label) accept
  rw [pass.2] at found
  contradiction

end PEqualNP.Outside.L_meta_4362.FrontRanks

namespace PEqualNP.Outside.L_meta_4362.FrontRanks
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
    (format : Nat → Nat × (Nat → Nat)) (read : Nat → Nat → Nat) (tag p scope : Nat) : Bool :=
  if tag == 0 then false else if tag == 1 then
    forced target mono false ws (row (read p ws.length)) &&
      forced target mono true ws (row (read p ws.length))
  else
    rankCheck target mono ws r (huffCodes ws.length format read (tag-2) p) (tag-2) scope

theorem rankHuffCheck_sound {target : Word} {mono : Bool} {ws : List Word} {r tag p scope : Nat}
    {format : Nat → Nat × (Nat → Nat)} {read : Nat → Nat → Nat}
    (F : (Fin ws.length → Bool) → Bool)
    (agree : ∀ p : Fin 512, F (fun i => (ws.get i).getLsbD p.val) = target.getLsbD p.val)
    (mon : mono = true → Monotone F) (group : Grouping r F)
    (h : rankHuffCheck target mono ws r format read tag p scope = true) : False := by
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

end PEqualNP.Outside.L_meta_4362.FrontRanks

namespace PEqualNP.Outside.L_meta_4362

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
def signedColumns : IndexTree ColumnInfo := (.fork 43 ((.fork 21 ((.fork 10 ((.fork 5 ((.fork 2 (.leaf [(2,1,460,48,7),(5,0,506,0,8)]) (.leaf [(7,0,504,0,7),(5,2,440,64,6),(10,0,501,0,8)]))) ((.fork 2 (.leaf [(12,0,499,0,9),(8,4,369,130,7)]) (.leaf [(14,0,497,0,7),(10,4,369,128,6),(0,16,486,9,10)]))))) ((.fork 5 ((.fork 2 (.leaf [(17,0,494,0,11),(19,0,492,0,8)]) (.leaf [(21,2,424,64,5),(24,0,487,0,11),(8,16,486,1,9)]))) ((.fork 3 (.leaf [(25,0,486,0,8),(9,16,486,0,8),(26,4,353,128,5)]) (.leaf [(32,1,460,18,7),(1,32,94,384,7),(34,1,460,16,6)]))))))) ((.fork 11 ((.fork 5 ((.fork 2 (.leaf [(36,0,347,0,8),(40,0,471,0,8)]) (.leaf [(49,0,462,0,8),(50,1,460,0,5),(0,64,189,258,10)]))) ((.fork 3 (.leaf [(66,0,445,0,11),(2,64,189,256,9),(67,0,444,0,8)]) (.leaf [(70,0,441,0,8),(69,2,440,0,5),(74,4,305,128,5)]))))) ((.fork 5 ((.fork 2 (.leaf [(80,0,431,0,11),(83,0,428,0,7)]) (.leaf [(96,0,415,0,9),(96,1,396,18,6),(98,1,396,16,5)]))) ((.fork 3 (.leaf [(132,0,379,0,11),(4,128,347,32,9),(133,0,378,0,7)]) (.leaf [(134,0,377,0,8),(133,2,312,64,5),(136,0,375,0,9)]))))))))) ((.fork 22 ((.fork 11 ((.fork 5 ((.fork 2 (.leaf [(144,0,367,0,11),(152,4,353,2,5)]) (.leaf [(160,0,351,0,11),(160,1,332,18,6),(162,1,332,16,5)]))) ((.fork 3 (.leaf [(164,0,347,0,8),(36,128,347,0,8),(176,1,332,2,5)]) (.leaf [(192,0,319,0,11),(198,0,313,0,7),(264,0,247,0,9)]))))) ((.fork 5 ((.fork 2 (.leaf [(8,256,151,96,7),(280,0,231,0,8)]) (.leaf [(276,8,227,0,5),(257,32,94,128,6),(296,0,215,0,7)]))) ((.fork 3 (.leaf [(273,32,78,128,5),(56,256,135,64,5),(320,0,191,0,11)]) (.leaf [(256,64,189,2,9),(322,0,189,0,8),(258,64,189,0,8)]))))))) ((.fork 11 ((.fork 5 ((.fork 2 (.leaf [(324,0,187,0,7),(324,8,163,16,5)]) (.leaf [(321,32,30,128,5),(224,256,23,8,5),(10,64,181,256,6)]))) ((.fork 3 (.leaf [(129,0,382,0,9),(156,0,355,0,7),(129,32,94,256,6)]) (.leaf [(161,0,350,0,8),(177,0,334,0,7),(193,0,318,0,7)]))))) ((.fork 5 ((.fork 2 (.leaf [(289,0,222,0,7),(257,64,188,2,6)]) (.leaf [(321,0,190,0,7),(260,64,185,2,6),(72,256,151,32,6)]))) ((.fork 3 (.leaf [(328,0,183,0,8),(336,0,175,0,8),(344,0,167,0,7)]) (.leaf [(416,0,95,0,8),(448,0,63,0,8),(480,0,31,0,7)]))))))))))
def rulesWord9 (i : Nat) : Nat := 0xa300090028c0026

def rulesWord10 (i : Nat) : Nat := 0x582d4c99582d4c9901110125011101250065408900654089602e686e800e6106002c0028002448fa00f200e9801600e918f9009518f90095702d0146702d800a80120020001c001800140052001000928005000c80050008bba99685736458483313003f2c0d0c0b0a090807060504030201000f0e0d0c0b0a090807060504030201000f0e0d0c0b0a090807060504030201000f0e0d0c0b0a090807060504030201000f0e0d0c0b0a09080706050403020100934030201000aa42ba060e10c1d01ce1703b90d742750d76133aa6c5564a00b751997504cecc9a9925fffffffffffffffffff

def linksSigned10 (i : Nat) : Nat := 0x90
def rulesWord11 (i : Nat) : Nat := (if i<1 then 0x3008010000f0380d0300b02809020070180501003008010000f0380d0300b02809020070180501003008010000f0380d0300b02809020070180501003008010000f0380d0300b02809020070180501003008010000f0380d0300b02809020070180501003008010000f0380d0300b02809020070180501003008010000f0380d0300b02809020070180501003008010000f0380d0300b02809020070180501003008010000f0380d0300b02809020070180501003008010000f0380d0300b02809020070180501003008010000f0380d0300b02809020070180501003008010000f0380d0300b02809020070180501003008010000f0380d0300b02809020070180501003008010000f0380d0300b02809020070180501003008010000f0380d0300b02809020070180501003008010000f0380d0300b02809020070180501003008010000f0380d0300b02809020070180501003008010000f0380d0300b02809020070180501003008010000f0380d0300b02809020070180501003008010000f0380d0300b02809020070180501003008010000f0380d0300b0280902007018050100300801003b3edf9f18f14b00ac0a80a40a009c09809409008c08808408007c07807407006c06806406005c05805405004c04804404003c03803403002c02802402001c01801401000c008004000200169b88d04636a0df261608033941bbf4187d06188433f01bb4a3466946fedda0c3d683fb711bfa96eb1fcc9b891751819fdf3741a3f3ad30aad6ad619fae07af43aabb3c3d219912722306b4eb5665063e2156753c52aa9585653ca736b0b82396f90ac521070c83a78b1483ccb797abb4852d4a825a3406c5a0a2676fd40f39116a147d1f41c81940f6e9f448fac58d4a44bb46a993b46a42626b4a5ba25cc9aa62ebd007ae113964155694b73f723242d411600dd5131f81638aa5d105a03e4ea823ca29e1d76a9079b53a7a8a4dac53e679ae639892b5429b3152cd3368337cc4822ae9b469b35f31142d1566b4f84988a5f761c89093c089595f08454f0e4484044acaf80a437872f764484be044acaf842297765e03292ac52f9e0e6508939118437afbb0e78ca1127223084558528134f10aa6be70f908a8439e322511870290de5e1cf1912722301486f421cf1912722301486f14d7139b64c468e5e5424c44e387282970a034da34db806a758436f5513ac2275812899d4e5c1b412eed0202272c51704dd978089cb2097768100e45628ba17002272c517977002272c51742f180722b149ce34f58d6361e31a736b267ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else 0xa5c84b9297212e40948c39025230e4a1c8cd928723365a4c906d693241b4658ac391962b0e48449cb1211272c544c81255132049584cb8f96132e3e601481158052045402f18ba70dc80b9c1d34ba01ecd2c804f389a01bc039881938d202bc410800f0016119500d824d1046229c62182592906505c526864d28d261a425280092cba00dcb2c800280e9000a03a4028a8f900a2a3e4422a105108a841582098996082626405ac009016b002402704ee31f4241a0088135802204d60171c3a09b50078022808d008a023407000dc01b003500680082012ce2e806600c801880301069403241f4035803c810500f2041405e00b8016802c005600a80148028004e00980128024164d0885028c2214088886d022221b5a1cc0266872023183688fd60da23f600ac00e802a81d9045004a705c01d826488890992222424f110649340438067208641fc81b803e813e00fa0220042008000f801e003a007000d801a0032006000b8016002a08d200a00130024008a11f401100200066007900698170038804400d0018286e01e4024801600280048008000e001800280042002800c800a0021875c14148cf535cc0288931d0550dc1e0032cbc28d972187b1bf61d33434d2274610fc1d00395d5739c2ee8ade8c9521c75d8a5290d2c45c003c9df72ab3e838d9ea6e98e5111a3c4aa1d435000d2278680c00b02809020070180501003008010000f0380d0300b02809020070180501003008010000f0380d0300b02809020070180501003008010000f0380d0300b02809020070180501003008010000f0380d0300b02809020070180501003008010000f0380d0300b02809020070180501003008010000f0380d0300b02809020070180501003008010000f0380d0300b02809020070180501003008010000f0380d0300b02809020070180501003008010000f0380d0300b02809020070180501003008010000f0380d0300b02809020070180501003008010000f0380d0300b02809020070180501003008010000f0380d0300b02809020070180501003008010000f0380d0300b02809020070180501003008010000f0380d0300b02809020070180501003008010000f0380d0300b02809020070180501003008010000f0380d0300b02809020070180501003008010000f0380d0300b02809020070180501003008010000f0380d0300b02809020070180501003008010000f0380d0300b02809020070180501003008010000f0380d0300b02809020070180501003008010000f0380d0300b02809020070180501003008010000f0380d0300b02809020070180501003008010000f0380d0300b0280902007018050100)

def linksSigned11 (i : Nat) : Nat := 0x3406304b78a20000015fa16107660aa0210000b19000034128000c0b4a06240b9852e0920000000000030a22065826b80300000002417b835847a21638003001a0946084000580e200fc02050c780df0814012c2ad841448cc11c00a782280a1a85c0006859801e000000041010000014d01d503e5016c014000281d647c008001c2043901520d9819800040500d2240d0000907b631e81cd0340001c110816b81500012079412581f000000000005010000000000000000e090c045027901220a9215d8180000705200000000000105cc51cda38000e98d606d59480000000611481e381c802d1520c2600003046000301f8000000081380000000100d204c00000000058000201bc856b004e026c1358273064e0c4b8d30471480002c21810810035830020410c008100700a040000
def rulesWord12 (i : Nat) : Nat := (if i<1 then 0x8a4d4142852028013809804a024011808804202000f807803a01c00d806803201800b805802a0140098048022010007803801a00c0058028012008003801800a004001800800200004ee14196dd39a4bfd7cd9e463defbfd86be1dd26fba286c883e9a5b86be6dfb856fb5ff6e29dc87489a5e7cb86b9b76996fb95f6ef3ec1cf3f2eed7237fcfe7ffb3cf72e7dba4cd4c18c94d916ce3cd5ef3b2de9cc16b3b5da1b2cefdd5bee8ade4fa5ebea0995e2cbd74f3f5774e3c9d5ac8abe34d8b1e9cfb9e7f5bb2af838ac7ef7e676b1777ac893c3ceb9bdffe71d41266fce99fafdc7e49ea0af978cf1dfb0e32867f8ff21d050ce57d59bbf4f6933ef33e665395e6c71ddef378f5776a672bddb4daf76de9bfda0b99f9faf166cb71e37ed784e73332c715ae2dacdeadbbdfa9cae3b36e6bf53df9c7abd8f9cbdde2b1f2a4d0c7b98f7231d7ea7df12bb739ed0c7b2ee5eef337dcadfebe956efa3a903c732bb6bbba9568f51e5539fb95e35dddc3171a7eff792ee51e0de4b76e3e16d3f8e6ccda4e391dbebcf1e5e5e6ccc30b6e5e5926e91c8ec9b3cbcb88f6d7bb2847b7345c7ee96fefef99974cbbf0e2d7e6c33e3f7bd0c7bc96ede0ed853f8e6ee876e1c0e53fd873e6bff4d7336e1bf4bc32dbe168dbefc5b95e4e2de5fd867cb9fcbcfa4c393a71d9e6fb0d74303374e7cb2f6d7a36e9bc8fc41873b8e5e6657c6d4c74d6bce5c369264fe07a5377f173c1755fbf8f867499fc15ffaafc7e8bd0e9e7eaeead93a82df6f1f0cea878e7eb4655faf8c94fa5ac1458fef3ff3eda927667f38ff9d68b7c25c9f67dff5a25e3721c7fbe3869f34ef53387e9b98874fc1cfd55f4fd6463eff70ebd13fef5c79f7a7c3aebfd71fac1f34e7c9eabfd71a7c79fdd5de52e3fdcdc683cbd39876aa19fc9c77a7194141a248560f7e3f3f68346d79ab1fc24f15fbf8e5e7567f6e78dcaf3f2eae8cbce72bf6499b571e75eaa1c6a4becc3ce6f5ac9326adb3f963ca9a9d643b26a9fba151ff23f3f682ef6e9bcafc793c47f1af865e757dbb6e57e5f1f57c32f3bb1b20e5c7e78e07b4fd5bb2f39caf0340e4f4cd8f3af567e5c7959a4fad661ab6dd8d7819aedcab3a6a9fbbcea47e5cdf7d24d64ae5857935603c7ea7945a56db068c7ec18b27bfa9b60afc560fd8fbc5b5bb9ff634fde2daddd4fbece7a9154819b695e66f56a6534afdcdc2a458bc59dd6c0383458a47fdcef175b05dc9d3d6536286f525beb27c7cfd3d4de75fdcf87dd4dea798b955b1e0bbe71eb29d148f7c906dcdf1e7cf56fce9ff41d48b3b1ea0b7e5effa0b7ffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 else (if i<2 then 0x548810af0f8128004f593b125eb38069ac0148a253a85f0918e81140c80049787cf71c4b275caa05111e33204f0770a10ce10800473866fd5ccb4c618b153ea463ce694b10fd17e18c0044f826e99adb0753e9490198d29a414648900c80cc0022e3d4730d297227c40c738b211e1942101e0280280000f01c0340600b0140240400700c014020030040040000f01c0340600b0140240400700c014020030040040000f01c0340600b0140240400700c014020030040040000f01c0340600b0140240400700c014020030040040000f01c0340600b0140240400700c014020030040040000f01c0340600b0140240400700c014020030040040000f01c0340600b0140240400700c014020030040040000f01c0340600b0140240400700c014020030040040000f01c0340600b0140240400700c014020030040040000f01c0340600b0140240400700c014020030040040000f01c0340600b0140240400700c014020030040040000f01c0340600b0140240400700c014020030040040000f01c0340600b0140240400700c014020030040040000f01c0340600b0140240400700c014020030040040000f01c0340600b0140240400700c014020030040040000f01c0340600b0140240400700c014020030040040000f01c0340600b0140240400700c014020030040040000f01c0340600b0140240400700c014020030040040000f01c0340600b0140240400700c014020030040040000f01c0340600b0140240400700c014020030040040000f01c0340600b0140240400700c014020030040040000f01c0340600b0140240400700c014020030040040000f01c0340600b0140240400700c014020030040040000f01c0340600b0140240400700c014020030040040000f01c0340600b0140240400700c014020030040040000f01c0340600b0140240400700c014020030040040000f01c0340600b0140240400700c014020030040040000f01c0340600b0140240400700c014020030040040000f01c0340600b0140240400700c014020030040040000f01c0340600b0140240400700c014020030040040000f01c0340600b0140240400700c014020030040040000f01c0340600b0140240400700c014020030040040000f01c0340600b0140240400700c014020030040040000f01c0340600b0140240400700c014020030040040000f01c0340600b0140240400700c014020030040040000f01c0340600b0140240400700c014020030040040000f01c0340600b0140240400700c014020030040040000f01c0340600b0140240400700c014020030040040000f01c0340600b0140240400700c014020030040040000f01c0340600b0140240400700c014020030040040000f01c0340600b0140240400700c0140200300400400634e6eae else 0x28ba03e0400681983d0426031410903141091384039138403913141211314121435513d435513d1486051148605144740a944740a9015409501540952274899227489901348a501348a52524869252486900f405900f4059050411905041191165885116588504e415d04e415d0404021040402104940ed04940ed00944ed00944ed0544029054402905148d505148d50124099012409944a401944a401981045558104555821812d04e012d4104069410406903544b903544b980e409180e409132c601532c601504d094e211895e22e8036240805e0438082256800a411811e033813280f80be028895203c415903c415903e88fd52c88fd01844b101844b104c012c04a0124048011c0460114044010c042010404000fc03e00f403c00ec03a00e40276012027604e10e50d110e50d140e400d40e400d01c413501c4135034408503440850536019053601903800dc03600d4441807520b807503408d180a88d160b543960b543903300c803100c004f8042422909a02f00b802d00b0241506d241506d20e8886808a01e6348c9902b0c9904454b904454b902a00a4028009c03280c102600c143e807a80d983a80b406e80b409401f814a023907612658b912658b9626a03100ba0310194090019408c022088a02104ca80940fd80940fd020007c01e007401c006c01a0064018005c016005440b8cba014004c30e88fa012186e011004000f004604198fa00e003421b949a00c008a00b00280090020007001800500100032005002200593f145de365628ac1071b52fa))

def linksSigned12 (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0x40084f09ac000060353005100536406b8149540068055c00003059480dc406340000000000000b0aab0ad8d018bc2bb20892010420987cc1cb0028c30d00001d16c0000381a960be8825a0000101756a0714176813480000000000000c0a4b42d5701758ab200383420f809ab2ae4000000000000014197503880000000000000807f95cfa278f45143b00e341e90000342ede08cd413ac283c00000000000000000000001035d0234602b482b7b03cc0000a9aa88702000028033603600000a06e81cb600000807bb04d38057e2090c2af000000000000000c770000000002621c22ac907a8000070c28000000000000020a0442cd7098841f5e0670000000002c14ff09640000674bf41ee207f3824900000000060a5c000060ae442da50484c1f100000000030873884da091a1d280000000000000164feb01c800008075c826600000000040339c16fb77971e86902a682d9d05fc000070248c8170000000000000302520000102600000180af30af5019a404acc2cb10459415588bffceb100001828000002c0a290467eab2000020c88340d24147306080000b32830823e064f0110d019c00000000101ae000000000000000000e0720029e4058544bd304a2c2a150178c258000000000e04f9c0d0903ed86ac91533c1899097502e00000180ff60b84c1f0b0bfd2ead000000000d055b5ab8e07ac40c470264000004b9b8abf301b8000000003c08ec781501c1c0450000000000000080b3b81230000042f500001822b000028081313900000008e801d0e041f9846500a3400d904d4000000000000000002c26d0030e4a1890333c0b70000024fd000019d44004b00000c0305019e04ade01acf08370029c034d4035e077059939046e40edb054c0000715800000c00d80000c948540264043fc0cad4ac9809460498851b01adc001a88597020760518e5200000000ae2012e401720827414ce026a405b00010006000000560000001f006200010007006e000f003500120004000000070000004500080072000c0008000c003500290004001e00250003001c0015006a0007001700090002002200210000000b0001004400ba004200190000000e000900000027000d001200b6002e00ff000c001100170002003a0017002200030000000900a9000a0001000d001c00010000000900010021000e0003000000040071002f0007002c000a000600800089000d000f004200080000000c004300020025000c000e000400c0001e0008002600010062003300010020001b0015000c001700010002000b002b00ad0003000d00120023000100420005000000030002001800440000000000240000000e000c00000019000c0022003500180000002c00000006001100000002000a000100030072002400020056001d000000a5000e000000090011 else 0xeb0ba8425f403b80000801620122e02a29cf917aa8c24f80c046c47904280000f58c4003f7444100e500000052490aff251700bf446e4103ca02990000100c0da67400007077e04ca90021c0a6da5fc000000000000080604c0def015682fee5c264127b07dec16b00001818f0000000008025ce2096044800000000102e800001402c0000181b500000028d40788000030a9c000050219884fa030a41ef9093b801471528422aa45266e47c0405c2cc0000202de000020078d74800000505e9c10070a6a024a594e882c0000000000404268025d0b97c0e9bb7eb406dc06cdc194f0b400000a08ff82f490614000070bba407dc08a602f950056029b440180000b07480000a0718424d30bce01b7804600000f032d46e500003ca1160a0b00d2904798212c056180f7205e28074b0a50c1e090a800000c0078c061a04c1408be0551c139902f162f900000c24400000000000be000002bab08808e38ca41330000300f150224000000000428a606c941fbf0390000000a1680cfd051400006076000000000182d1f4447417cd0a45127fd0a1a11048ab9da9850067d5d08274580000105b142c6000000000e00f40000000000000e000400000000100e800000000000000c2e226500000000003c1063071c0000f003b4090306652da232be901796b5088060000000000501301042706c00000208b480ec00000802110601c07900003006411bae02e4e07a1c124b6aeb01adc02a9810de05df42dc000000000f02e00000c035bc30c4046a010cc06100216a087580f4d0944821f56729005f74573c03c80c0140070000150d10000000007a5cac02a0000101503031816f9425ec000000000000000b6c84bb107fc0000a0c2d82f6405a40000b009c000066590de5a10b0eead500003c0405023c00007061fcad4007b5051c70b178e3d50973000000000821700001650cd01f880bac095cc276508315c9a00000000000a1c0032504f3c4c1e77f40000b01539eb20000301d60000000006043ac10b7004fc30900000000000000c2280000240190000000005787502f2000008173e920441b940198000000c15c2cf8062c000000001ed8a90355c15b7904201ec306616e39301700000000009047b0adae81d7040c0000467250219f05880000805100000000000279b00dc0000e1c254091504bc000030195406300001c0b5d09dc00000000142ec00000828fd03740000b771a04ba408dd82010000282ebb0a63deea007cc00005064ae13f7947bc6c934bf80000706a3826e000000000a07d2c28e00002c096a0aac416dd682541950000000002073c027200002408c000000000c0860c07600000000000000000040695026300000c1cdd0658000000000000030294000000003409be00140000000000000a0bf00000709a1814eb08fb817110a9) else (if i < 3 then 0x361145c0953412a000020073904454dc50000201d19086a650a500f90024d089d0243000000000a00e8000040a121deca0ac6056620710000083ab00000709bd80fd705740000704f502039039a2401000000000f041400000000000009068400005056680b0505920215000029ee800003c0cd00000000000001514b00002a536000000000902d800000000002000000143063014fc19b0000082080000000000000199cd0000000005988da16a909a5c4e700001c2484038c0265a04c4c30372ac5c00390164000000000000000002dd21f099c000000000000000000000090009250900002404ae06e3414800000000010b7c217d00000825e909044206000000000801e800000000000000000000009039e004f00000814254bd400000000280a48008c8052006f542bad0b06c0b9076a80000c0784000070384000031b0d81f6d05f9c1d4908080000a0568000017238000000003421350b4800a3eb68f824500003c24c0000382c40000101bb80bc2c17d00001830400001a2f6365dc807fa03d6c1700000105f982b2ec242000000000f1559825b40159c1e38790a42a3d0121801c000038247b01040000d0409c0f9006f1853fc3812d12da07cac12de08b88236e086d40ea90ac29d074005b024020139e2adc081642b3d12cc0000108280000a0a58812ee00bcc27820116c0a1409d4422000001401dc095b009f000019ebdd32640000b0755c02e00003c24bc0a704253d28500000968340000000000000b06c4000040aa30225385dde49c30a214143109435843a0633418e80674c8250000104da400b40000000000000eaaf9c30800000c01200001aaad000014c9f90a302ad4805d000006070c0000d006281da40b7400000000000000000012aa4b1d800000058f404300000c15eb0b20000000002dc1b31bfb8255b01240000a07e0000000000da0a00002c03900169e20d6031400008149a412920838000015bd3811c273124108e14e25d198047cc527f0525800f103aec12500000000000001003400003c0680000000008212ac13660bc40000a06af854200001c0df50a7c000020b5c0000fbb280000a061b81c00036e4069c007cc28b60993c2b5c7aad418800000cc910000082b800002d27e00000220a3757c0000000000000000000000000000000000018117a0ac80000506440000202c865480079e008d000000000565180000a031c00008201c00000000100936032043022044c000030a26055556ab05dfcb861800000527702b4fa06440f0e09b000000000300800069840b3709f000713750242a2007080000807740000a94ef802bf079182d8000018020000000000e972c81bf80256c29540887806f812f800b18048000009062bc151300240000709f552b100003c00c1285d8031615a00000908d5420bb02b3816 else 0xd0228eeae80ba701af31af942ef00003de1ef924fe4f8d00c000000000141b6b0b990172f074c809e20bde4167508b19d1210347c4cbe09ef40bf809eac2e700000c230b4909655500002803b90a764210e06d242d640b8ec18300000000024a180000d0764000000002660b0000102d3d002c0000a01aa02bcf06aa82beb1548814149be3422f506400050a01f2908661bd1c1beb09c40000f213aa4f76029c000010aa402739735142c7b02ac000000000c022f032400003138401de0000281e600000027090c1e01dbf94dec083558e2c27f502d240462452000f6a036880d9000000000900100000e0a4dc09830474c2fbb0a4101ce4069c82a4002169089214a1806c674e780477089a996d00000c1a460a0ec011668ef416a0020980ef2111a9f0400002d044e41d7c132d045602c2908f00000000000000000020222501c00000a09d141a0e013400000000201cb0000342a6000000000f673242d4d8bf906ec0000300fc879))
def rulesWord13 (i : Nat) : Nat := 0x48403212100c84b605212d81484f425213d09481800b805802312c41fa4b107e82780840d604d408910a15e44282e604a0b9812c0d603b03580e853815c15206501500a004c03b22e505a8b941680b40da02d03684151a210546881a41f206907ca26507289941c812008804081940e810d02e01d40581a203c06880e006803001610e805049a25d009004100600e23e90dc018045005002000c0044f9183f6deafca120e69114228018ddaf525172c43aeab3aaaa1e659663f09a138007b1a0508e42b87a120400e0300a02006010020001e0701a06016050120400e0300a02006010020012a0b104000047f35bb0a5cde492df3763517efb9fa831d461734370de89e5b6ec0d6a9aa13adf3e53b09a16424b60b76fcb24332467b9eb6bb0a1649e5be6c34d6a44643dcb7853458d0bc77aff97465da13f0b23db97f9e5aec685d93edbd1ae7f39bebe6b11e6be40b38b6f758e5304737f0699b2eb0f8f304736b6b171e6be0496f9add8bfaf1dd4189736318fe7dc889dbdd681eb4e5f7e18ece5d68d03839fb8623db4e5d1a1fc6b863833869b6eba7b9140bf1cfe6c1ec5d4edb903f732be139140655a4f725cfe77f5e708195027b93973539a413c32e6a48bce1a0ef3568399c345555555555555555555555555

def linksSigned13 (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0x65000000000000010021800000000000000e16183be000000000e10b7020640e600000000000000e085bc56b0045c5a70000000000636c00000608fc0478a002303d3570300000af6be81de00000b27a000000000c0a4802858174a01a20113c028721760049c40968000000006815e0000000000000500f8725080000000000000000060598000000001801cf0351656ac056ff46eea5af00fb341da46eb08472000060a7be100203a2212d74a07609de8153613a78180c0cf70123a16d501180000184c6a111f0151e1608c3fce01a300e380aad0322000018422000008074a067d048460285850a0000383f8000000000000000001c06a7807c000000000c0a42c5a9d6825118420301047d6e11783c360f380000209a6992a0000405be0137883b8000038574000020449a0f18000001010000000000000000c3a8435405fa021ec0ba000008010800cc0000103a9c0dc2001000001034600000000000007caf780370000000000000000000000000005c2d400004044b80198834a000000000a4420c95c0000000012151e8140000050252cd6c00000000068516000000000601538dbec097e13bc30fc8048ee0f28837600ae70001209d503e400000000000001035e00000000000000000000004051800000000000003ab36e138701966a790812a000020102c09e2b4f202ce7835d807d3c1df414b800000000000000000780a220f58000041209d2710cefaa0056136084ba928cc0409c091d80ba000060464600f18436000000000405598303a042f0058804c58431e03d0000180320000020a37004d08c5a006400005805ea460881ee000000000000000000000000000e10c80001c15e3837c80c9a227600001b0de00006bd2b04607c571c04f80000aa7580001e0275801ac04ee93be00000000080def82cca0f9b05956036d0463e17280000e0ef1824e00000000000002256c307800001a11de833b2233c802f81030027be40a285d6720b500c28b620035400bb195ca48b800000000000001807738b3c0c01d0018393160c387003c702060400d860c58404301060c3414b1008f07060cc00302c10408000820428086081c00b02340130400003000810f100410f001000a2e2410e04405840a0010108003000a0008616008000c00753140833b0418207000050000a41830204b800e040000608189021880d0a20301081800000040041e0c101060400106040010018083000c007000408000082000000000003400132080091a28416120018000001820404300000000600000800220080001400004080812a0c1800204000000850704ac41200082000a00000000c000002010208100000a1c00504180060494083040010d0008000000008700080030008a810810002020078222000020a000800218300021820104080230204381 else 0x700618128c02640000000000150d83d88176e01e000000d5ce60ed60019a1097045820ad00000000000000000000001213b78504001d800008169702be689b80000c1755815de07000001008b400f760528035360a9284a8000008585206af020bc06ec38ae0000000000121f802340c91053600000000193630000000007406d9077104dc0073a04fa00005820f40811802c80eb189ffe0ac0000000004027d016cc8474caa4d0467c13bf0154c06c3b25881598853c000000001a058e0084000050101204b882411644e08a8c0ba98375d0fe18414a01750097e06fa836be115a008240f42988f40d590310a06420309cc9358227215280000000045b94c09800001814ea85082e3d582d1613d9010fe099bcac1c156b85ce6130805c2212f300e62152505cc7170f824b094d00000000002dbde0030000000003328a213c0000081555831800ae80001411800000000000001c0b63587fe10f4811a000000000e14a2006d40d8329c190c2801b7800e00000620ef83d40000303f3c126500940132f836de12780000209a80000003460596000060313a0d958214e0b8d3820c0cc800002146bb3eee02c301120000504daf681905ab00f8800000000383ee000040453e05d0341a00004844400001030b80a2881daf680c02a14102920f00000138f20000703a060498000000000000000005808f00b79825c40bfd84aa120648237c07908230a041c80400002c8288403a080144128501c314748000124530054420a9800000000004a40000041e3a07f83a22000000001c0b54c29c000000001e0cc00000c0490000020ac800000000000004124f05a0612000000000070224a134102a20000620d82812000006048602c8810470561a13500000800ac02f5002b283380000605922237d0494516180001d763400ae0000382620000000000000000008071c029d0c6c80406486000001a00f8000000000816a00007844d406d384e6407600001204b00001c16000001612b980b6807b0b86c0000000000000583730154d0280000000000d65f8051c0d27cb814809500000000010012000000001c14780233601c484c9136073db181492cd86000000000000000000156a80001c8112838c0000504f2005f30006888a8000000007b4ee802a7058e608d3c40502d1382f372892828e00310554a80455004ac034ecd5a016a2808cc08480000e0096823c8063e81ac415b4038f40cf800000000000000000480034141d021a4041784d2700eb8057520c00001a07d983dc000000001d69b80000d22c80455ac496816c215ad08fa0000103dfa14e0000000000000000000000002032004900511042a00000000000007d385e04cf8250000000000c03af01838139285620000538120000785ac0000101fcc0fc08078c153a852c60) else (if i < 3 then 0x4780000c169f3ab84c9c80000805b80000416c28558000000001e14d48391e07a985c1a10a38021c07400000000030221414c680be000a00000a0fa100b8e14828358b2950000000002843e4350000cf811b109040000705778e9e800000000000018078980466c730820300bef042721039158320e50820d6031c0451409f98050000000001a12b00000000078199200e800000000000002068085d1916c684200000000000000249454133905c486e06815a6b6e00000e11bd0d6a600c0859f80d200001a15f283040000000008107a394080860038ae0c69036f8889b845a40b100001cc9070b438231a0111a0cdf83ebce63000010b72781380000000018e8b800007682cb2bde0c77838441240000080a0800016e608c809c05a084020000000018038383c14d50780fe20b3f841362369b3da00006007a1500083a5c0fd0ac540000385c6000000001e03f281a4a088a80fa80c7a0341216f1b8cb40f1000000000000000000182e5a0cb804b160b9d019a0000705730131080ed4027e03af8f60d04eb815fe8192016ec80330cd780389615a6b9d80090b8a085100505418e55d829981622816700d30053e5257d3855a0d0884f92f5020570616e2b93f800da848aa06ce0164001fedd8ac12e282a9a0d1285010110f05036240a855d6037fa579008af0129a0356558a005eb822f00537d9c4b21974d31c2cffb98ae0e58848920bf3917e406b9032be013b014600000000020e0703c8e072585dcc66d800008074881368166a3d59416de0591408e800018026e041800000000020840000000000858a0000000000000401b80000182c7c11a1047e8135c91684061c845ce02f20511807280001a88b503060022c818cc0e9f02f683540000160c8080340000703fbe25e8000180b6903b201306bd7a0000000000000000010026680888061703db20d680000000078026000000000a0752832c20ed80000000000000000000001812f800010258000000000485140000302d20000402c0606980000d0fd382f0ac1b00000000000001213d180900000302aca13300001d15f882f8000000001805c101e6000000000415310189d1626000420f86052a20da62b8a000000000c2277021c000000000021b00000000000001007a5216640d3d83ba210e8029ac0ffe0159807ed837e804d4005aee2c0017600000bd342e94e8b48414cd018b4125f01bc00002831661720000100ca5000f307670081a09600001814380001a0e6a05aea0e71055f60b08000000005023840ec00000a067681730110000000000633278ec8b01420000584b26126d824800004289741230000140d9b01f28129d039e204200000d238800016007c831480bb8000000007850c000070378601af824420b8100b52024fa068213f3826d81632029781540000056f200 else 0x5852760058000184edf817920e0a8522802ad81c4a0cd3830ca095d01f8482b503fd00a5534f4813fe84388032f0209e03c103ab00070000000006811d2d3d9057be03ca846a0000181f140d88000120af4c97800006042ed2780000109504006e6d5f80000e03bd841a000000000000008044c0ad88301422de816141389b905ae09285a2008a783874c22b8471835b580d80000182d70105f48cc004f581cc0000284b7808000001615960db2000000001e02900001a0148000000000045f42d0703cc9359800018144e83f6c039180d6c043000b2e0937041d60b280000000000000f22d40148c11eb82ae0053f806200003059c00e4800000000682dca155d05868029e829fa))
def rulesWord14 (i : Nat) : Nat := 0x2680b81ba0982143e42143e42c83460a83442e40e42e40e405004003002230261e8bd99dca0f7b5

def linksSigned14 (i : Nat) : Nat := 0xc61406daa300101e100014310001c110002186b070000400b10600029a30000000a074022703c00020bc000b0dc81ffb8c02500000000002807000000000140000000000a00400030c9033858c00030580004034000000340052880005057c0be718c217050435c8b8000b0b80005042c19904c0000000000000382d0039ea1000000000011e30001a22000000000038e300000000003e23c023c3a0002003d0932630003c1a000000012840000001027f0e2c0a0000000e05d0392b1842c60240000002423a080000903142be0d2828001a03610a4000000000000000000001c46207b92360c0000d099da1a0a90a3d060000000000000000002048000000306300036f10000d0000404002000050100003c1302004
def signedLevels : Nat → Packing
  | 9 => (1,6,0,0,0,0,0,fun _ => 0)
  | 10 => (91,5,0,0,0,0,0,fun _ => 0)
  | 11 => (782,4,0,0,0,0,0,fun _ => 0)
  | 12 => (751,3,0,0,0,0,0,fun _ => 0)
  | 13 => (59,2,0,0,0,0,0,fun _ => 0)
  | 14 => (2,1,0,0,0,0,0,fun _ => 0)
  | _ => emptyPacking
def signedIndices : Nat → Nat → Option (Nat × Nat)
  | 10 => lookupWord 1 2 0 8 0 4 linksSigned10
  | 11 => lookupWord 35 149 6 15 7 4 linksSigned11
  | 12 => lookupWord 324 1383 8 18 10 4 linksSigned12
  | 13 => lookupWord 323 1357 7 18 10 4 linksSigned13
  | 14 => lookupWord 28 149 5 14 6 4 linksSigned14
  | _ => fun _ => none

def signedRules : Nat → Nat → List (Nat × Nat)
  | 9 => ruleRead3095 rulesWord9 16384 2 0 2 0 2 17 70 0 14
  | 10 => ruleRead3095 rulesWord10 8192 356 8 404 8 1132 16 1836 0 13
  | 11 => ruleRead3095 rulesWord11 4096 4210 12 4798 10 12618 15 15978 0 12
  | 12 => ruleRead3095 rulesWord12 2048 7612 13 8223 11 16484 14 20923 15 11
  | 13 => ruleRead3095 rulesWord13 1024 1889 11 1933 10 2523 13 3771 0 10
  | 14 => ruleRead3095 rulesWord14 512 66 0 66 6 78 12 318 0 9
  | _ => fun _ => []
def rawRecipe9 (i : Nat) : Nat := 0x5eb62356c54d3048160
def getRecipe9 (i : Nat) : Nat × Nat := let a := packedAt rawRecipe9 (i * 75) 75; (a &&& 1152921504606846975,a >>> 60)
def rawRecipe10 (i : Nat) : Nat := 0xbf78c569d3160160de7dc36d48648160deddc56cc86481609efdcb2195348160bef5c12195348160bafc8c5ad5348160fed96354d3048160fed96c54d3048160ceddb56c1a321960bd78c569d7160160de5dc36d4864c1609eddcb219534c160bed5c1219534c160badc8c5ad534c160c7fd5b6293148100be7dc52195348160beddc32195348160fb798554d8048160e7d98a4c5304810087fd5c4ed2a44100f769535492044100ce7db36c9a521960cafc8b5e96a54d60aafc8c5a9a454d60aafc8c5a9a254d60aafc8c5a8a254d60aafc8c5a9a154d60aafc8c5a9a054d60d6ddc56cc8664960d6ddc06cc866496096fdcb2195364960b6f5c12195364960b2fc8c5ad5364960ceddca6cc8654960de5dc56cc86549609e7dcb2195354960be5dc32195354960be75c12195354960ba7c8c5ad5354960ce7dca6d4864c960ae7dc52195a4c960aeddc32195a4c960aef5c12195a4c960a6fdc2269635056087fdbc2698250560a7edc22698250560bb78c569d8460160be78c569d6460160af78c569da360160bd78c569d7360160b778c569d9360160be78c569d6360160fab9845915260160af78c569da160160bb78c569d8160160be78c569d6160160d3f8c962d5160160dbf15b6053160160fbd1326053160160fc75655c5515c160ceddca6cc8654160ce7dca6d4864c160ae7dc52195a4c160aeddc32195a4c160aef5c12195a4c160be5dc5219534c160b67dc5219924c160b6ddc3219924c160b6f5c1219924c160ce7dca6d48648160de6dc26d48648160ceddca6cc8648160ded9c06cc8648160ae7dc52195a48160aeddc32195a48160aef5c12195a48160ae7dc52193a48160aeddc32193a48160aef5c12193a48160be6dc52195248160becdc32195248160bee5c12195248160be79c52193048160bed9c32193048160bef1c12193048160ff49535493048160baf88c5ad5344160fe71635495144160f749535493048100d3b89b6114160160b3f0c96053160160
def getRecipe10 (i : Nat) : Nat × Nat := let a := packedAt rawRecipe10 (i * 64) 64; (a &&& 1125899906842623,a >>> 50)
def rawRecipe11 (i : Nat) : Nat := (if i < 3 then (if i < 1 then 0x58d10583f7caa2c6882c1fbe5cd6344160bff316a9a20b05ff97b54d10583f7cb5aa6882c1fde6155344160fdf2caa9a20b07ef96454d10583fbcaa2a6882c1ff660d5344160ffb2e6a9a20b07ef96354d10582ffcc5a86882c17fe56d4344160ff7308a1a20b07ef9635c910583bfcba324882c1dfe5519244160eff2e6c9220b077f95364910582ffcc5aa4882c17fe5ed5244160fbf0f6a9220b07f797554910583f7cb2aa4882c1fbe5915244160fef2a6a9220b07fe98254910583ff4b92a4882c1dfe6495244160fdf2c629220b07ef96550910582ffcc5a84882c17fe56d4244160ff72a8a1220b07ef96350910583bfcc9284882c17fe56d3244160fdf2c699220b06ff953629105837fca9314882c1fbe58d7a44160fdf2c6ad220b05ff95b4e910583f7cb1a74882c1fbe58d2a44160bff2b695220b07ff18754510583ff8c5aa2882c1ffc5ed5144160ffe30aa8a20b07ff17454510583ff8da2a2882c1ffc5515144160ffe306a8a20b07ff17354510583ff8d9aa2882c1ffc2cd5144160ffe2a6a8a20b07ff14354510583ff8c12a2882c1ffc5c95144160ffe364a8a20b07ff0b254510583ff8a92a2882c1ffc5095144160ffe264a8a20b07ff03254510583ff8c52a2882c1ffc5e95144160ffe2b4a8a20b07ff13a54510583ff8952a2882c1ffc60d4144160ffe2e6a0a20b07ff18250510583ff8b9282882c1ffc5494144160ffe0a4a0a20b07ff132505105823fe5d2a6902011ff2e93148100cff314982408077e9524c120403bec98a6090201dfa5492044100cff274902208077f1514811040373e59b4a432c1b9f2c9a521960dcfb60d290cb06edcb568c8658376ed9346432c1bb72c9a321960bcfb6a432a6b05ebdb421953582f6ed990ca9ac19bf2696a54d60bcfb6a430a6b05eddb321853582f7ad890c29ac15bf6cc86649608ff956a9b24b05ebdb4219525832fe3d334a92c179f6d48614960bdbb66430a4b05ef5b121852582f3eda90c992c17b76cc864c960bdeb6243264b05e7db521832582f6ed990c192c17bd6c4860c960cdf952b2ae2b07af582605615823fed9934a0ac11ff6c89a50560cf7934a1282b066fd6526931582bfa5cb0298ac1cfd625814c560cdfac64d242b05ef8ab59580582dfcc5aa8c02c1eee6115460160f5f30ab1b00b07b798554d80583d7cc22c2c02c1efc6055160160aff136a0b00b05e7db521950582f6ed990ca82c17bd6c48654160bd7b6843240b04efcba5952058277e5d2c6902c1f9d5955144160efe136a8a20b07ef16b54510583f78b2aa2882c1fbc5915144160efe324a8a20b07f7152545105837f8c52a2882c1dfc6494144160ff6284a0a20b056ddb321992582b7ad890cc92c1eae6116460160a7f172c0b00b07af18158580583f38b2aa2882c1fac5914144160 else (if i < 2 then 0xc1ff5605314c160f7f30ac0260b077f99560130583f7cb2b00982c1bfe569804c160fdf2c6c0260b07fd95360130583bfcc9300982c1efe605804c160eff322c0260b07ef96160130583fec98b00982c1fbe58d704c160eff324b8260b07df9715c130583f7cb0ae0982c1ff64c5704c160edfb12b2a40b076fd8958d20582bfecdaa6902c17bf5ad53481609ff974a9a40b06efd656292058377eb1b14902c13ff62d7a48160ddfacabd240b06efd635e9205833fea9b34902c1bbf2195a48160ddfacaad240b06efd635692058377e43274902c1bbf5953a481609ffab69d240b06efd634e920583b7eb1b24902c19ff4e99248160efdb12a9240b07eec8654920583ef63daa4902c1dfb66d5248160fedaeaa9240b077ed9554920583f76b2aa4902c1dfb64d5248160fddac6a9240b06fed8a549205837f6bd2a4902c15ff66d3248160dbfaf4b8a40b077ed526452058377ec52c2902c1fbb5496148160bdfad6a8a40b0777d9554520583f3eb2aa2902c1fdb5495148160bdfad698a40b077dd934c520583f6eb1a62902c1dfb6552148160fddaca90a40b07eed6348520582ff6ada42902c1dfe5e58048160f7f30ac0240b077f99560120583f7cb2b00902c1dfe64d8048160fdf2c6c0240b06ff95a601205837fc9d300902c1ffa5498048160f7f302c0240b077f99160120583f7cb0b00902c1ffa4858048160eff312b8240b07df9755c120583efcb9ae0902c1dfe64d7048160fdf2c6b8240b06ff98a5c1205837fc9d2e0902c1ffa5497048160fbf2e2b8240b077f9915c120583f7cb0ae0902c1ffa4857048160eff31298240b077f9794c120583f7c43260902c1dfe6553048160fdf2ca98240b05ff98b4c120582ffcbda60902c1dfe64d3048160dff31498240b06ff97a4c120583bfcc9260902c1ffa5493048160eff32298240b07ef9614c120583fec98a60902c1ffa48530481609ffb16bd220b06efd655e9105833fec92f4882c1bbf5953a441609ffb169d220b04ffd7b4e9105827feada74882c1bbf58d3a44160ddfaca95220b06efd634a9105837fcbd300882c1bfe4e98044160dff254c0220b05ff98b5c110583f7cb2ae0882c1dfe6497044160dff314b8220b06ff93a5c1105837fc952e0882c1fbe5953044160bff2b698220b07ef9634c110583feca9a60882c1bfe6293044160dff2f498220b06ff92a4c110583bfcc4a40882c1dfe5e52044160eff32a90220b07ef96548110583bfcc9a40882c1fbe58d2044160bff31690220b05ff97b48110582ffcada40882c17fe4ed2044160ffd2a490220b06ff98a481105837fcbd240882c1bfe4e92044160ffe2a290220b05ff98b5d110582ffcc5aa8882c1fbe5955444160ff7308aa220b07bf98460d10583efcc3ae6882c1fbe5957344160fdf2eab1a20b07ef974 else 0xca51b00b05ff9ab5cd80583efcd3ae6c02c1dfe6557360160fdf2cab9b00b07df9745cd80583f7cb22e6c02c1dfe69d9360160fdf34eb1b00b07ef97458d80583f7caa2c6c02c17fe6ad5360160bff2f6a9b00b077f99b54d80583f7cb5aa6c02c1efe6155360160fdf2c8a9b00b07fd9a354d80583fecb9aa6c02c1fbe5954360160bff2b6a1b00b06ff9a768980583f7cb2b44c02c1efe611a260160fdf2ca51300b07bf98428980582ffcd5ae4c02c1fbe5957260160f7f308b9300b05ff9ab54980582ffcbdaa4c02c1f7e1ed5260160fef14aa9300b07bf98554980583fbcbaaa4c02c1fbe5915260160eff326a9300b07ef96354980583fbca9aa4c02c1ffa6895260160ffd2e4a9300b07bf98414980583f7cb2a84c02c17fe56d4260160fdf2c6a1300b07fb94350980583f7cb2a64c02c17fe56d3260160fdf2ca19300b06ff9a768580583dfcc2342c02c1efe69d8160160f7f34ac0b00b07bf8a560580583dfcbab02c02c1efe6918160160f7f2e8c0b00b07bf95460580583dfcd1b02c02c1efe28d8160160f7f2e6c0b00b07bf95360580583dfc29b02c02c1efe50d8160160f7f344c0b00b07bf8a260580583dfcb9302c02c1efe5498160160f7f0a4c0b00b07bf94260580583dfc99302c02c1efe0c98160160bff356b8b00b07bf9855c580583dfcc22e2c02c1f7e5c97160160fdf34eb0b00b07ef95358580583f7ca92c2c02c17fe5ed5160160f7f308a8b00b07f795254580583ff8b8aa2c02c17fe5ed4160160ff7284a0b00b07bf9854c580583dfcc2262c02c17fe6ad3160160bff2f698b00b05ff95b4c580582ffca5a62c02c1ff64c93160160ffe28298b00b07bf98448580582ffcbda42c02c17fe56d2160160bff27690b00b07ff13148580583afeb9b24b82c1dbf58d925c160efe962c92e0b07cfd635c570583afec92e2b82c1bbf629615c160edfb24b0ae0b05efd6b54570583efab8aa2b82c177f5ed315c160bdfad698ae0b07edd634c570582f7ed990ca82c13ff62d7a54160ddfb14b1aa0b067fd8a649505833febd324a82c1dbf5959254160edfac6c92a0b077f99260150582f7ed990c982c1dbf625654c160ddfacac5260b04ffd8b5e93058377eb2af4982c1bbf2195a4c1609ffb16ad260b04ffd7b5693058377ebd2c6982c1df7625534c160efb936a9a60b07f5d8554d305837eec52a6982c1bf75e9534c160affb16c9260b057fd7b64930583b7e43324982c1dbf595924c160cffb14c9260b067fd7a649305833fead324982c1dbf58d924c160efbaa6c9260b067fd9a54930583faea9aa4982c15ff66d324c160ebfaf2b8a60b077dd5364530583f6ea9ac2982c17bf5ad514c160eefb2aa8a60b07e7d6554530582f7eb5a62982c1df75e5314c160efbb2a98a60b07edd654c530582feeada62982)) else (if i < 4 then 0x25836fe3d346a92c1b7f1e8a354960eefb12a9aa4b07e7c8654d52583bbecdaa6a92c1ddf26d5354960fcfad6a9aa4b06f7d8a54d52583ebe3d2a6a92c1ddf6695354960eefb28a9aa4b07e7d6454d52583faec1aa6a92c1fd728d5354960fed964a9aa4b05efd6b50d52582bfe5cb04a92c1dfb6e58254960efd972c12a4b07dec7a60952583bf6cd304a92c1fdb2d58254960fedaeac12a4b077ed9460952583f76b2304a92c1efb60d8254960fedaa6c12a4b07eed645c952583f76b1ae4a92c1fdb54d7254960dbf8f4d0aa4b06dfc7a68152582f7ed990c292c1faf6116414960cffaf2c5284b06efd655e942583f5eb2ae8a12c17bf6d4864c960bdfb6643264b067fd746693258377e432b4992c13ff62d5a4c960ddfac8ad264b06fed5a609325827fedd2a4992c17bf6d4860c960e7fb12b9b02b07bed82549815839fec4a84c0ac1d7f61d7364560efbb06a9b22b075fc7b54991583bbea9aa4c8ac1dfb6095264560affb16a1322b07ebd8455161583e7ec3ae6b0ac1bbf6ad5358560fdbb06a9ac2b07afd8360961582f7ec5ae4b0ac1dbf5d19258560edfaa6c92c2b05efd8b54961583e7e3daa4b0ac1f9f54d5258560fddb04a92c2b05efd8b50961582f7ec5a64b0ac1fbb6093258560ddfad4b9aa2b04ffcba609515833fe4d304a8ac1f5f1ed5254560fcfac8a92a2b0777d9354951583f3eb1aa4a8ac1fdb6095254560ddfad4a12a2b07bf582605515833fe4d306a0ac19ff2697350560cff934b9282b067fd7a649415833fe4d2a4a0ac1def6515250560fd7ac8a9282b067fc9a14941583bdebca84a0ac1faf5954250560cff93499282b04ffd8b5e9315833fec4af498ac19ff2e57a4c560cffb2abd262b067fd945e93158377eb22f498ac1bfb2c97a4c560edfaca4d262b067fd872693158377eba2d498ac1bbf5516a4c5609ffaf6ad262b06efd645693158377eb2a9498ac1b7f5e9724c560cffaf4c9262b067fd5a649315833fecd2a498ac1bbf5a9524c560defab4a9262b06efd6a50931583beebca6498ac1fb7595324c560efe934c0a62b06ff55a60531583dfac130298ac1ff54c9814c560ddfacabd242b06efd635e9215833feba33490ac19ff54d9a48560cffaa64d242b04ffd8b5692158377eb22b490ac1bbf58d5a48560ddfacaa5242b06efd654e9215827febda7490ac13ff56d3a48560fdeaca98a42b06ff58a4c521583d7ec2ac6c02c1edf6155360160e7fb0ac9300b07bf5814c580583fbc5ab4ec02c1bfe69da560160f7f34ec2b00b05ff9ab5d580583efcd3aeac02c1dfe69d9560160fdf34eb2b00b07ef9a559580583f7cb2b48c02c1efe69d8460160f7f34ac2300b07bf8a561180583dfcbab08c02c17fe6ad7460160fdf2caba300b07ef9a7591805837fcd3b46c02c1fbe595a360160fdf2 else (if i < 5 then 0xf54d9248160fff2a6c0240b07ff9535c120583ffca9a60902c1ffe54d2044160ebfb0eb8a608067fd8a4c520402f7ed990ca92c1faf6116454960f9f8f4b1aa4b067fc9a609415836fec3af498ac1bbf5957a4c560f7f308a9300b07df9a75c5805833fec5324b82c1b7f629715c160f9facab8ae0b05efdb521930583f6e432a6982c1fb75ad534c160bdfb6a43240b05efdb321920583fb6a9aa4902c17fe62d7048160fdf2cab8240b07ef9634c120583feca9a60902c1fbe58d5244160ffe308a8a20b077d9534c1204023fec5a74882011ff62d2a441008ffa7695220806e7db36948658373ed934a432c1bb76d5a321960ddbb60d190cb04efdba21953582f7ad890ca9ac16bf22d6a54d60bcfb6a432a4b05eddb321952582f7ad890ca92c19bf2696350560bef16ad3b00b05bf98b54580582dfcc5a82c02c1eee6114160160f7e30298b00b05e7db521930582f6ed990c982c17bd6c4864c160bcfb6a43240b05eddb321920582f7ad890c902c1fbc58d5144160fde2c6a0a20b077fd53609104037fec5264b82c1f7f60d715c160ffbaa699260b077fd8954d20583fbec2aa6902c1ff760d5348160dffaa6bd240b07efd5358520583ff6a9a42902c1ffe60d7048160affb16d0a608067fdb162920402bfeada74902019ff6e98148100e7fb14c0a408077f9b04c520402bfec5b42902015ff4eda148100eff2ca982408077f98b4c120403bfcada6090201dfe6293048100eff2b4982408077f9814c120403bfca8a6090201dfe6c53048100eff342982408077ed82549104033fec1274882019ff5493a44100cffaa6952208077f9534811040377ed9b4a432c1bbf6c9a521960ddfb6ad190cb06efdb268c8658377ed8346432c1faf5d58459160bdfb74432a6b05efdb521953582f7ed990ca9ac1ebf22d6a54d60edfb12b52a6b076fcb95a95358377ec52d4a9ac1bbf5e96a54d60ddf934b52a6b07e7d6a6155358377ec52c8a9ac1bbf5e96454d60fcfb0ab22a6b06efd6a69153583beedcb06a9ac1df76698354d60fdbad4c1aa6b077dd9460d53583f6eb2306a9ac1bbf5a9a254d60ddfad4512a6b06efd6a6855358377eb5340a9ac19ff2a553609609ff956a9b04b057fc9b54d82583deec1aa6c12c1faf611645c960cffb14ba324b076fd7458d925833fec52a6c92c1dbf2195364960affb16a9b24b067fdab54d92582bfe55aa6c92c1dbf5ad5364960efbb06a9b24b076fd6550d92583bfaba142c92c1dfd54ca164960bdfb6a432a4b075fd891e9525836fec50f4a92c1b7f1e99a54960ebf8f4cd2a4b057fcb961152582bfec5b28a92c1d7f1e99454960ddfb14b22a4b06efd7a59152583e7e3d2c8a92c1f9f5d56454960dbf8f4d22a4b057fcb960d525833fe4d306a92c1d7f1e99354960edfac8c9aa4b06efd7a58d5 else 0x3bfea930298201dff54d8148100effae8a9b24b07ff9a74c5805837fec5262b82c1fbf2195348160fdfad6a9a40b07efd6554d20583f7eb1aa6902c1df)))
def getRecipe11 (i : Nat) : Nat × Nat := let a := packedAt rawRecipe11 (i * 53) 53; (a &&& 1099511627775,a >>> 40)
def rawRecipe12 (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0x2ffd7a50560dff64d415837fd9250560fef509415837fd894c560dff5e5315837fd954c560dff65131583efd644c560bff629315837fd9a4c560dff26931583efd6a4c560bff56931582ffd4a4c560dff64931583fdd324c560dff625215837fd7948560dff65521583efd6548560dff65121583efd6448560dff64d21582ffd8a48560bff5e9215837fd9a48560bff56921582ffd4a48560bff4e921583ff53148560eff615805837fd9560160fbf595805837fd9360160fbf58d80583bfd8160160dff64580583efd6160160ffe69580583ff8a560160ffe5d580583ff89560160ffe69180583ff97460160ffe55180583ff9a360160ffe28d80583ff97360160ffe24d80583ff85360160ffe50d80583ff9a260160ffe28980583ff97260160ffe24980583ff85260160ffe50980583ff93260160ffe0c980583ff9a160160ffe54580583ff94160160ffe48580583efd635c160fbf585705837fd8954160fbf21950582ffd8a54160bff5e9505837fd9554160fbf595505837fd9354160fbf58d505837fd9254160dff64550583efd6154160fdf54550583ff98054160dff625305837fd794c160dff65530582ffd8a4c160bff5e930582ffd5a4c160dff64d305837fd924c160dff64530583efd614c160ff74c5305837fd8948160dff5e5205837fd9548160dff64d20582ffd8a48160bff5e920583efc6a48160bff56920582ffd3a48160dff64520583efd6148160ffb485205837fd8944160dff5e5105837fd9544160fbf595105837fd9344160fbf58d105837fd9244160bff62910582ffd7a44160bff56910582ffd3a44160bff4a910583ff55144160ffe60110583ff97044160ffe54110583ff93044160ffe61d10583ff98544160ffe5d510583ff97444160ffe55110583ff98344160ffe5cd10583ff85344160ffe50d10583ff98244160ffe5c910583ff85244160ffe50910583ff93244160ffe0c910583ff98a44160ffe5e910583ff95a44160ffe4e910583ff92a44160dbf595604027fd3a441009ff4a9104037f920441009ff2a585583ef8a0595609ff2a5845827fd8a651609ff2a5835827fca95cd60dbf59193583ef8a058d609ff26953582efd6a50d609ff2a5825827fd8a64960dbf219925837f4a1649609ff269525827fd9a509609ff269425827fd9a4c9609ff269325827fca960560cff625815827fca95c560d7f5e5715827fd8a645609ff5e9915836fd9258560fbd605615827fd9a545609ff26951582efd6a545609ff669415837bd9450560faf591415827fd9a4c5609ff26931582efd6a4c5609ff669215827fc9a48560efe615805837f99560160fbe591805837f99360160fbe58d80583ef961601609ff669505827fd9a4c1609ff66920583ef96544160fbe591105837f99244160bfe62910582ebda421960 else 0xfff5c550583ffda154160fff54550583ffd3154160fff48550583ffd894c160fff5e530583ffd854c160fff5d530583ffd954c160fff59530583ffd8a4c160fff5e930583ffd5a4c160fff60d30583ffd734c160fff64d30583ffd634c160fff60930583ffd724c160fff64930583ffd624c160fff54930583ffc524c160fff68930583ffd324c160fff60530583ffd714c160fff54530583ffda14c160fff4c530583ffd214c160fff62520583ffd7948160fff61520583ffd7548160fff65520583ffd6548160fff60d20583ffd7348160fff64d20583ffd6348160fff14d20583ffd8a48160fff5e920583ffd5a48160fff16920583ffd3a48160fff0e920583ffd8248160fff64920583ffd6248160fff54920583ffd3248160fff60520583ffd7148160fff54520583ffd3148160fff68520583ffd2148160fff61d10583ffd8544160fff5d510583ffd8344160fff5cd10583ffc5344160fff60910583ffd7244160fff54910583ffc5244160fff4c910583ffc3244160dff685304037fd8a48100dff4e9204037fda148100dff5cd104037fd8244100dff549104037fda961560dff625745837fd955d160fbf595745837fd8565160fbf61564583efd7559160dff6a5835837fd9460d60fbf59183583efd645cd60dff5d193583efd6524d60fbf289635837fd8954d60bff62953582ffd7a54d60dff669535837fc9a54d60fdf615535837fd9454d60fbf21853582ffd7a50d60dff6a5825837fca960960dff5e5825837fd9460960fbf59182583bfd8360960fbf59572583efd645c960fbf58d725837fd8364960dff28d925837fc5364960dff50d92583efd6524960fbf58c925837fd8954960bff62952582ffd7a54960dff66952583f7d7554960dff651525837fd9354960ffb5c952583efc8614960fbf59052583efd6314960dff625425837fd7950960dff65542582ffd7a50960fef5d1425837fd894c960dff5e532583efc864c960dff65532583efd654c960dff65132583efd644c960bff629325837fd9a4c960bff56932583fed824c960fbf21832583efd650c960eff60981582ffd8a5c560dff625715837fd955c560dff65171583efd645c560dff64d71583efd635c560dff61d915837fd8564560dff611915837fd7464560dff60d915837fd7364560dff54d915837fd8264560dff549915837fd4264560dff4c991583efd8758560fbf61561583efd7558560fbf61161583efd7458560fbf55161583efd8358560fbf5cd61583efd5358560fbf14d61583efd4358560fbf5c961583efd5258560fbf14961583efd4258560fbf4c961583efc3258560dff625515837fd7954560bff62951582ffd7a54560dff669515837fc9a54560fbf5a9515837fd9454560fbf591515837fd9354560fbf58d51583f7d5254560ffd6055158) else (if i < 3 then 0x83ffd7954960fff62952583ffd7a54960fff66952583ffc9a54960fff5a952583ffd8554960fff65552583ffd7454960fff65152583ffda454960fff64d52583ffc9354960fff68d52583ffca354960fff54d52583ffd4354960fff64952583ffda154960fff68152583ffd8414960fff60c52583ffd6314960fff62542583ffd7950960fff5d542583ffd9550960fff16942583ffd9350960fff64942583ffd874c960fff62532583ffd794c960fff61532583ffd754c960fff65532583ffc954c960fff59532583ffd744c960fff65132583ffd8a4c960fff5e932583ffd9a4c960fff26932583ffd6a4c960fff56932583ffc5a4c960fff52932583ffd834c960fff64d32583ffd534c960fff60932583ffd924c960fff54932583ffda14c960fff68132583ffd850c960fff5d581583ffd7460560fff5cd81583ffd5360560fff14d81583ffd4360560fff5c981583ffd5260560fff14981583ffd4260560fff4c981583ffc3260560fff62971583ffd855c560fff69571583ffd845c560fff69171583ffd835c560fff68d71583ffd535c560fff50d71583ffd525c560fff50971583ffda05c560fff5cd91583ffd5364560fff54991583ffd3264560fff62951583ffd7a54560fff61551583ffd7454560fff69151583ffd8354560fff5cd51583ffda354560fff28d51583ffd5354560fff50d51583ffd7254560fff68951583ffca254560fff54951583ffd4254560fff4c951583ffc3254560fff68151583ffd8350560fff5cd41583ffd7250560fff54941583ffc5250560fff4c941583ffd854c560fff5d531583ffd844c560fff5d131583ffd544c560fff62931583ffd7a4c560fff56931583ffc5a4c560fff52931583ffd834c560fff54d31583ffd824c560fff5c931583ffd524c560fff14931583ffd424c560fff68931583ffca24c560fff4c931583ffda04c560fff61d21583ffd8548560fff5d521583ffd8448560fff5d121583ffd5448560fff60d21583ffd7348560fff14d21583ffd4348560fff62921583ffd5a48560fff52921583ffd3a48560fff60921583ffd5248560fff4c921583ffda048560fff69d80583ffda560160fff5d580583ffda360160fff5cd80583ffc5360160fff68980583ffd7260160fff54980583ffc5260160fff4c980583ffc3260160fff68580583ffd5160160fff48580583ffd935c160fff60970583ffda25c160fff64970583ffd325c160fff60570583ffda15c160fff54570583ffd215c160fff61d50583ffd8954160fff5e550583ffd8a54160fff61550583ffd9554160fff59550583ffd8354160fff5cd50583ffd9354160fff58d50583ffda354160fff54d50583ffd8254160fff5c950583ffd9254160fff58950583ffda254160fff54950583ffd3254160fff0c950583ffd815416 else 0x3ffd7454d60fff54d82583ffd8454960fff60d52583ffd6354960fff60952583ffd8750960fff61151583ffd8254560fff60941583ffd874c560fff54d21583ffd5360160fff5c580583ffd3160160fff4c570583ffd874c160fff54d30583ffd8748160fff54d20583ffd5344160dff605304037fd714c100dff58d204037fd5348100dff605204037fd3148100fbf5d163583efc8654d60fbf5a953583efd6454d60ff760d535837fd7464960dff54d92583efc8654960f7f1e952583efd6454960fbf58d52583f7d5354960ffb60952583efd6550960bff62942583dfd875c560fbf59571583efd8258560fbf58d41583efd654c560bff5e931583ff5814c560fbf58d215837fd9260160ffe69d80583ff95360160ffe54980583ff97160160ffe4c5805837fd925c160f7f5c570583efc864c160fbf59530583efd634c160ff754d30583ff9804c160ffe5c130583efc8648160fbf59520583efd6348160dff64920583fed5248160ffe60120583ff97048160ffe4c120583ff92044160ffe61110583ff95344160ffe549105836fd63581009ff629204037f93048100bbf69486582efda3219609ff5e994583ebd84591609ff5e9935836fd63649609ff26941583ef96560160efe61180583bf98160160fbe58d10583ff15144160ffc50510582e7da521960bb768c86582ef5a121960fff69185583ffda361560fff68985583ffda161560fff68185583ffd7561160fff62574583ffd855d160fff65574583ffda760d60fff69583583ffd7560d60fff25583583ffd7460d60fff68983583ffda160d60fff68183583ffda95cd60fff2a573583ffd855cd60fff69573583ffd955cd60fff65173583ffd7464d60fff5cd93583ffd8524d60fff62553583ffd7954d60fff62953583ffd7a54d60fff66953583ffc9a54d60fff5a953583ffd8554d60fff65553583ffd9454d60fff69153583ffd8354d60fff64d53583ffda254d60fff28953583ffda154d60fff68153583ffd8550d60fff69d82583ffca960960fff69582583ffca560960fff5d582583ffc9560960fff69182583ffd7460960fff68d82583ffca360960fff24d82583ffc5360960fff50d82583ffda160960fff68182583ffd855c960fff61172583ffd835c960fff54d72583ffd7464960fff5cd92583ffd5364960fff61492583ffd8324960fff54c92583ffd5358960fff625525))
def getRecipe12 (i : Nat) : Nat × Nat := let a := packedAt rawRecipe12 (i * 42) 42; (a &&& 1073741823,a >>> 30)
def rawRecipe13 (i : Nat) : Nat := 0x1ffd85583ffb08b07ff5d160ffec1ac1ffd73583ffac6b07ff54d60ffec12c1ffd52583ffa84b07ff4c960ffec0ac1ffd71583ffaa2b07ff50560ffe98ac1ffd21583ffb00b07ff5c160ffea82c1ffd30583ffa40b07ff44160bfeb02017fd30402ffa40807bf21960f7eb2ac1efd64583dfac6b05ff64960f7eb0ac1ff980583ff220b07ff62560ffebcac1ffd75583ffb2ab07ff25560ffeb2ac1ffd94583ffb26b07ff24d60ffe29ac1ffd43583ffae4b07ff64960ffe492c1ffd62583ff8a4b07ff0c960ffec8ac17fd10402ffb12b05ff5e560bfecaac17fd94582ffb26b05ff64560
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
def requestedBudget (k i : Nat) : Nat := 0
def signedBase : Forest := ⟨511,14,fun j => deadsamples[j]?.getD (0,0),signedColumns,deadautos,
  signedLevels,signedIndices,shapeCut3640,shapeCut3640_sound,some opsAndMask,some signedRules⟩
def signedCertificate : SignedForest := ⟨signedBase,requestedBudget,[(17,272)]⟩

def rankDictionary (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0x25820462405710492407820495001524c8080f84548100f94114100f93550500f50049020384049604530046102392222000f62011000f61046201681049300460046210160049a4058004988035404e104497049440480049520176049101642049204470046604053046008754046140042049410231128100f40046601865305000f43046280862e48400f21046e04687049640084322200f7204e60038604e300650212000f3204948045304d60045004e100475514100f93049410362105000f6504920812004601075304ec00832411400f61524400f10049202368490400f32046410653660600f10049708520049700142705400f65049701253309200f21641600f84702000f3204e100390d80c00f32046c02342049420374222000f72046410273046410753046408754046008574049604074049300762046004581049e04074049a40782049d00152e05800f43430400f83e48c00f21f01800f4304d200410046240341049640287046640431049680420728300f40049104460049e08520046a04687046c08754049020182482400f5004d60007504940a968049510291046680042049640840702400f64049108691049320271209200f21e41c00f85046c04853046520230046410563046408462112100f32a48800f2160a600f80780600f32705400f43704400f74046010273049201352c24000f83424000f83049280420046408574046601274046204687609000f21049900152c22800f72c12800f32046502942046540931305000f6504982038404982047304920407404908045304660805404d600283049020374049604430690600f50046401864049640782046601831049704530722600f72046004587049084450046201684049700241205000f43046208054e05000f75046201274728100f40030000f83612600f32e05800f75528100f40605400f43150100f50046208052046210720049420384049304560049a80420046a01684049c20384704000f74046280042009000f21a28200f40049608081a41800f8504ea00386550100f50214200f10282200f50049080354812800f32049480354422000f72049608520702000f64049a40480046e08052c24c00f8320a200f86049240084424400f83046301264049240480049420473049020473e28a00f40605400f75046e0405304e2005860a8080f40049201742049c80453046c04587049608580628200f40e28200f40628600f40301200f61e05000f4304de00450605000f75212200f32205000f75228200f40049601742e44c00f83c24800f83e09000f85422400f72049601253209000f21024000f83209000f85e09800f8560a400f86609400f85290200f50605000f43609400f21022000f72412400f32012000f32609000f85049e0125304ee00386 else 0x2488600f82710600f50424400f7330a400f7004d600180046088520046002342388080f40f01c00f43488400f85728500f40046402752049440342694080f38241200f840b0080f90049204570049a40084c88400f85049c20182049c0858704d800875049104560049020271049720176049220374049180531605600f830465049410460a00310460a003204600a780046a04041046a80042046c10753046802382812000f32046c08752701600f61046408654046201864028000f72046204041682400f5004e200432622400f78224000f7304d400675046120230046504491046610653046502492049700672005000f43046002582211000f61014000f10049202364046004643046308052328100f40e90a00f500465206400460487810464488710464081625a0500f90046002752a09000f85824800f83e28600f40046680862049202863046604863622400f8604924028704930164204640458740a400f7820a200f28409000f21722200f72505400f910462202300492012530490a0310022000f62049081532312300f32184100f91049304064049c20382049c10231a90200f50046a80682046804587046810573049880453046c0285204982037404960487604e60085004920487604610294204e60058604644057104960135240a400f86046304071304000f74049680140049604078702400f3220a200f80049280820046120640049208520049110259094080f30e09000f21822800f72046240431049100152046402342049700631282080f28412000f32046201231046e08054046c02752046802752046c02382046408164046210680428400f40046110620109000f7504954042004944008404670257604660856404e600750409400f21046408892049501253412400f72049e40782e90200f50046c02582049900251e44400f8304604898404e210780049208580049202765612400f32046202830c88c00f85c30c00f8304960447020a200f78046240751046201271046708054046010573046604051224000f835a2500f92501400f61046604687046704053046410573782400f54046210270049204430382000f5404600446304600816204901023104da00410e05c00f75514500f93090000f32a90a00f50046c08574822000f72046e8068204e600861046140931046210163624400f83682600f50302000f3204940487604e700340049500672049502963049680820582500f900491040640490815420a4000f1020a200f4004611026004908153104600a896046201865046502940046601681046610720049601752046640571046002852049181542046c10853046810753046804853046608052046208164046410680049720271a09800f85c12c00f3204ea00586049e0175204650805404d6004100464) else (if i < 3 then 0x300f40504400f61602000f6204e40057204922086104d60013204e700650360100fa104952067104952037904d500694411000f6104e500275049120176628400f7204e08026a3c0300f21049010968105000f4304900267304901073104600805404600404104630273004610494304618015020a000f86046190210046104071049110169a05000f75d80400f32824000f8304d100510049440782082000f50049280651622000f62501000f75644400f83222200f62582400f5004620a780e09c00f8560a600f86046280082049604570046504053141000f21049420382046720430750500f50241000f85046600741046640751046340042049701342046404463321300f740460101600492804530460102630462102630460086420465102600465c0591046448981046504943046282a65046704741046502970046502730049084350049181241049d0025104e80058304620405104628068204640238204641085304e60148704918014204918024104d20808704e120397684200f8104938014204e20148704928154204918056104920a857046e01831e41800f85049640480049108570046004851049608681505400f65049620671049780541424000f73049280354049620463049500276049420463302000f64009000f85084000f91109000f2104930003104d400875046d00273046640341046610860046402852046008462046201831046210653049202785049202783049300064046440751046520320046280165049220382046410860628400f4004662032004640898204960812060a600f78046502396046680165046208654308200f2104660865404650249604640464304654057104d20013204660146804622032000a000f40185100f5404dc0087504ec0058304dc00732505400f43049208081049002765024000f73414400f10690200f50124000f10305200f65224200f73721600f7440a400f9204670072060a200f80682600f08682080f28046204053049208180046310620088200f8204630405304da00540a05800f75d04800f75b01800f43c22c00f72049e04570049c2047304ee00850c22000f72830800f83a50800f83046401865046610270046404851049440287046601684046201381046680682049220182046101264622600f78422400f78049201752224200f83222200f7204d600186641400f850c8080f84049602863049602368046708052049408587701400f6104630173104970135204930443004e600340505000f43624000f7304d60006104970074204944024304e080380382000f32611400f61049604018049140420046002382101000f61046120320005000f75049204530049010362049008120046108564049300251049104694090000f50290200f32e81c00f2104950076 else (if i < 4 then 0x8304982018204d80048304e410780222200f86684400f81049501652049120073046602342049088186049780651482400f64049401918582100f9004918095300a000f92049084053160100f9204ee00586a05800f43046802342e81800f2104de0008504e210180046404853049420271049480651046602430046404863046500276046010270049100251046604041309200f75701200f61046640051046480042701400f43046620430049700276049500470049500570048000f21488200f82049408120046620230046601271705600f6560a400f782c0200fa2049440453405400f187c0700f21046702752708200f21049040342384100f10611000f61311200f51049004470049300631222200f63082200f5030a300f7004920134230a100f70046001231281000f21328100f62a05000f43890800f32049e01742049408580409000f8504962028104942028104d600510428400f72049220176049504430049404074405000f75049520970049080152409400f85049508520209200f85650600f10046401684484400f65541400f9104e70027504e300275030000f73305200f43509400f79046500651524000f10049410750049420671049402765049500251628200f72049304460309000f75284200f81382000f53046700273049604830790400f636c0200f21182000f64046604843514100f39282200f080490905602a0080f38046001274049004074049001853049208681304200f10049204830049100762085000f5904908041004902028104d300450049220364285000f4304908232004e200861046a08052046a2043004930013004660186404620147104660448104e10049004621086004930014204664018504608016504934042004e200732046540391046601231046640872614400f10046610680781400f3204660484104620146804e20038004d400132046404871046201478088000f2104600454304600246704ea0085004da00075ac0800f85c88800f8504ee00750612000f32244000f8304e200386046480682148100f49046001384514100f30046610160314100f30494080f83148100f9404964038204960185360a400f28414180f93049220473046640831514500f39046408642046240831046601641205200f83704400f10205200f43185000f54194080f30580400f32046088150049a04430046c10573049c20374046a40571e09800f21504000f7504d600085049504064648400f2104e600210046202576049500460046002372046101731049220172049002785422000f6204922067104960278504d60054004620138404950007404d60073204962017204d60024304970076204e300073049508691548500f941a2100f922a4200f1004e600083508000f2104902026104e30037a328 else 0x4ec00572046a01681046a40751ec0400f21049e80054046a20230046a10720049a04470049e04430049810231046a40341046802852046808754e09c00f21528500f40049208871490400f5004d60002104960268504d600621046301371046480165522400f72049280140049104430046300276049010631049001742046120371e09400f2104941063104e50039004620243004948486904922028160a400f40584080f3004930125304962016804d100310049401853049602483049040782230200f8304660138404d600743612200f3204d5004900495089700466026520495081966a8480f840462823850493a02a1049580142049488186780400f3204920884104d60036204940884104644018504950194204901016004960882104944035404e60032104958124904978014204d600632046301a7104640164104944881904960487004950135204e600380704600f10418400f72340200f1004950441904618015304e100370682400f64049510192046002380028000f40046101974046090520049002674049020741049040941046001541049210263390080f300493085201a8080f40046380320184100f1004921025804e180590046104465285000f54304000f63381100f64185100f43049010761046102542049040291046308054094080f83190100f50309000f21f01400f43049a40287c30400f)))
def prefixTable0 (i : Nat) : Nat := 0x180033cc86000e753180038e086000c1201800385886000ef85180033d886000e4311800388c46000c3421800389846000e47018002bc846000cf73180033d006000c041180033c406000e75218003bd846000cf501800395d86000cf64180033dc86000c27318003be0c6000e4531800399046000e65218002bc846000e043180033dd46000e384180033cc86000ef741800389c46000c12018003bd446000e580180033d886000ef521800395c06000c34218003898c6000ef6318002bc846000cf73180033d006000c041180033c406000e8531800385806000cf501800390c06000cf64180033dc86000c27318003bd0c6000e3721800391806000ef3018002bc846000e742180033dd46000e374
def prefixTable1 (i : Nat) : Nat := 0x4000204010100c19080b01c001c088c18250c038309c220804080141c0010180c0424000204010100c10250e01c0018308c18180a830241c240804060101c0010180a0824000204010100c08160a01c0018208c00850c0304218004804060421c0010180c0e04000204010100c1a050e01c0018020c1886030302818008804060441c0010180a0824000204010100c19070241c001c182c18250c0380c1c202804070281c0010180c0424000204010100c10250e01c0018308c1817020b0241c002804060101c0010180a0824000204010100c08160a01c0018208c00850c0304218004804060421c0010180c0e04000204010100c1a050e01c0018020c1886030302818008804060441c0010180a0824000204010100c19080121c001c088c18250c038309c220804080681c0010180c0424000204010100c10250e01c0018308c181810030241c240804060101c0010180a0824000204010100c08160a01c0018208c00850c0304218004804060421c0010180c0e04000204010100c1a050e01c0018020c1886030302818008804060441c0010180a0824000204010100c19070241c001c182c18250c0380c1c202804070281c0010180c0424000204010100c10250e01c0018308c1817020b0241c002804060101c0010180a0824000204010100c08160a01c0018208c00850c0304218004804060421c0010180c0e04000204010100c1a050e01c0018020c1886030302818008804060441c0010180a082
def prefixTable2 (i : Nat) : Nat := 0x202488118c09c2046202488118c09a2046
def prefixTable3 (i : Nat) : Nat := 0x1800301146000c1941800307106000a1921800303146000c0a11800286146000a1a41800287046000c1051800301886000a1c21800286846000a1e01800303806000a0851800303046000c1611800305146000a1921800303846000c00a1800286146000a1a41800287046000c0c21800303886000a1c21800286846000a1e01800307146000a085
def rankFormat : Nat → Nat × (Nat → Nat)
  | 0 => (7,prefixTable0)
  | 1 => (8,prefixTable1)
  | 2 => (3,prefixTable2)
  | 3 => (6,prefixTable3)
  | _ => (0,fun _ => 0)
def rankHeader9 (i : Nat) : Nat := 0
def rankPayload9 (i : Nat) : Nat := 0
def rankMode9 (i mode : Nat) : Nat × Nat := let v := packedAt rankHeader9 ((2*i+mode)*2) 2; (v &&& 1,v >>> 1)
def rankHeader10 (i : Nat) : Nat := 0x50ce3a12c74198e81c1ce9ca9b55b2ffae5af44a06c915d91cd323343c5a88883190b9aa0f844132a80912fc029ec563c6a877950ea821cd3438a886f7d2dbba5ad463454b67010cb9a19064313675f656bb6216be52c82956cd0a8c214bc428fc54ed569d58535c2a5828474d888c310a34a07693e618770ace7239bda83615068820ccd3988a82face5b1a0ae4494fc928a4e4eb1c967591cc921e0e3f42075748d98818dd02d3a04de50798d0c9920bb50009980001
def rankPayload10 (i : Nat) : Nat := (if i < 1 then 0x659cdbcc9823229074c793a1ec4948202500832942894ee7ab6a8c3eca5efaa5a6d0945a66db38b0504110280bc24886347e0aa2507289419546882058b77a0b7f76b040a42c7952bc248818f7e4ec4c7eb36347e4a3822109ca48810dc382e159819450e61c1163a498959c43347f87046411895805e198c6c4d52a2e992971d4a5e8e0f50ec63626a954861e3c75398b09461265185129ca8f99eefb21bb97890cdb7e4e5b78b495b0a450a8dcc3d89029c6218c74f9b0a53181ae1d82a502507e1263ec3641cd3d80733520df4d31ccbdff31420a53f13106398c837441aa9f056d08a0636820857ef23e9f806ca4132d3d828faf20c51b4284514d01396360d91230df27b8547442a0c2f924167de34f54fbc38252088ea85444610763188e6a5075219e29f3f210351d79c18c95431e787c923ef78114e617d1a801533844b4f609e66c328fde74c7d96a314ad668628e4a60af2efc95d91be5ae7fe1c28efc9214f30edcc632ffc44c72092893e8d401899c6a3ab05e0c616249d0e799b0ca3479b6e0239ab44440c7e06a28fb8db03e1e48a627b544d05245132533ff4286a4e4e98fc3ca44f256e291cad035286fff18895ced0253bc63f2f2913c9c4591e22acf012804194a144a773d5b5461f652f7d52d3684a2f336d9c05e198c6c4d52a2f992971d4a5e8e0f50ec63626a955e61e3c75398b09461265185129ca8f99eefb21bb978bccdb7e4e33fe46c5a4ad85228546e61ec4814e310c63a7cd85298c2490670f9867fa140249469df49b27fed36dfeb373be4a303110495f9cb2d47540880215d1460b47ce56f5130d97ea18ffea911fb1aa8d8f11ccc660cd60c3605805faaac56ab10d17b05177dc686ef93d892bdcde2bac1864a345a600a85760b8080c1c7314888d083597c73623f030f526d277352a6cf63d98aec364f7da6472c32a34aa3073386f121878c98c94b6f77a8621895fc98cc188c1cc761561629f2efaa35bd46efb2d1b97e5fbef969379396de27256ef512a99162865d19791a9e4f549ee345ec188abc254862ab2d6ab48d127b8dbb957a1bbf2f647fd66baf2d72bdd8abc66fcbc6278bc55a4a64fb668148da0b25549529b23986844a3727fd6620b27787fd4eba6b36e0a4c6342951b623f23397fd4e10a3549c7e39b820319b23bcdc116119d22d88fcc5b9670a8a4b5ba29469a49a42f4a7a4de54f60b4a4c2f166ea938c750524e83191321db12417b2246af18522b4184e631b1b0cd3f6cc3642b99d1ab0a7a3c4745794495ca333a2d6525834c708308902c71fd96e98fd2236860b6608b3824288da1c2624d024891af11fe1e3687188e2ed11c21670404b7292c28ffd0a39ff208a9b2cabe90958c694625d0e124ceb62ab9c4bfea70c93eed58c9d22ac651b0aa58aec5628a946c8e321f9817ed8c2 else 0x4df269ed5789ed523bd66ea1430da51f68a223ecf1d327953be6f7847e062e14bda34f9386d8453166b58d90181ea3cfc9aba4246748a4ffea71b1a85d120578ed4e2db11bc7516236532b463f0f51a23a0902c6feed616ed426598480f57375798c2c07e052a64788ec37048415426598480f57375798c2c07e052fe4788ec37048416c28d4a4701cdf8239df9731aa433614c850f5d892905d0f224ac12e12b20718d812ffd961ea684594788e86c2c6d9082d851a941e039bf0473bf2e6355e66c2990a1ebb125209b23c43d9285867046340b73258b410825bfd18d83a3f3739684ba150857463603da32cb7a8e8b87f0eee6a87dccee9562b6768f9f5a3990d9120539ab1b65a1c85321447)
def rankMode10 (i _mode : Nat) : Nat × Nat := let v := packedAt rankHeader10 (i*19) 19; (v &&& 31,v >>> 5)
def rankHeader11 (i : Nat) : Nat := (if i == 0 then 0x875d518eb1f21d57e53a99ca75060ee9bf25d2b85ba3d89742996e80125cf843b9b9cc734610e6292dcb7a5b9580a728414e4b029c8ac438e34b71948ee2db15c4cc4386d8a70b112e1251dc1a64381e48701b90e0001dbf8a3b7d9486f5894de5325bb584b74dcc6e5592dbf12db6bc4b6c2086d3b14d9b929b2dc436340a6c1596d7a025ae5c435ac876b310ed5dc29aa5c5b5318b6a3490d3fe1da7084b4bb0969508ed2052da2b05343549683c90d01a1d9f40433cdc7675f12ce2f2d9b7c5b35c08668192ccac259898532fd0a65bd94caf729956a4328c0c64f092c97a2d91fa5b22589642492c7fc258f60431d948636416c6781d8c0c4314b4c624c10c3f32986f64b0bec8612516c1f91d830843041cd603094bfc4297eea3afa94c5f1094bdcb1d79de5af13895dda1cbb142974a85ae53d05c5812b7f72d6ebc4adbb095b548ab627256b2652d3b8c5a1e96b3f02567344acc8c8595a10b24e2963c642c5488585298b018255efc52bc588574292ae38215bd242b468c564514ac072556d652ab808553990aa331d538e42a58ca548110a8ab2150bc42a068853d712a720294d9e429784c52ce90a4fd2949363a91305520a8ea3d51d4714428c8ca517090a2aa1d44a452884c750ea0ea1313541ec3a828095019969fae2d3dde5a7a3084f0e929dd1213a8462738084e231a9beb1d36ba426c6c74d56969a611d34403a675084ca91698ab2930c23a5fe084bd592973b2d2dfe3a5b0074b251095f4212b5042558484a850e94b325284e524ea8949931092c71d243a524510c485994900a251f4e3a3c6c94762128e55251b4a523408b4641948c0325172a422c10945331289d229130a4224b094448148811210f1e4a1ce474341968606250b9e3a1608842869084792908503a0fa85417a9a82193103644203eca402d927faf2cfe6851fb7473f338e7e181cfb6239f4ccc3e269a7bea24f73a49ec44a3d34167a311cf35249e448a3c6d8e786024ef7059dcc093b3f9675c830ea5e51d33c83a0718737728e64839c988d38ec92711530e10451c094837e4106f4028ddb049b8c4a36e3906d4924d9b449af64f35b2906aef24d45c69a67c9347d94685728cf98499c94a335790664020cac89192850318934615e58c0548179a562e53bc5aae6cb220c15dc982b09aa54db4ca78489490192870aa4fcd3c9cbcb139501266f304bbd4c954699277d1244a344709548c507912c9821c8a642774c824e98fddda1ec7b63c5a4c75aac8e4a591be82a360d586a3ea8d14d1196f2a319158604ea0ba79416ea202c0f605520b8a2fd713ed18257e744864888ab1410cda81fe8603e986077c140e3c2a1c6e0438c8086c5920d86021903642efea0589d30a3b2e12f85422cca8420cd077f260d4564174ac82272504498205f48805a72800020 else if i == 1 then 0x3cb718796c80f2d4e1e5a183cb3d87965e0f2c701e58683cad61595343329d83e524c8ca169193c41f26dc4e4c1c9c95e91925823241446464cac88c1590702f20683e3fa07c7a7178ed5231cdc5638a07c6c99d8d1b23199e46324c7c61d138ba92f1694462ae88c536938a1a27137056244c9c44b918814270f8e4e1de88c3951186a5230c9c4e1780ac2641f847b230760660ce88c1459582261f03064e04e48c05a99806827002c4dff108bfc68f7ebc42fba665f320ebe18997bb12af6ae4dec548bd69917a4f3af38e6de5ec8bc7e11789626f00855de3c8bba98f76c52aecd445d87c8bad113753422e9d645d1b48b9d21b731032e52c45c8488b8e09171502ae1fe45c1d89b7e9956f6326de3045ba88ab6f8976da122da104db2d87b61a116bc626d5ae6da9888b4e91368fe36d0bc4da14c1b4240367fc1ecf46459bf8ab34d8f65c932ca8a4594e81b2618f64032ec6ae558ac89b0e899615622c19e457fdccafca915f4a22bdf84576b10aeab915d0626b8aa556f78aadb6175b141eb57a4d6994aace41b59342eb1e4456120cabfe8f576022adc44d59c08aafb11555c2aa94c5550cc8a9ec9353092ea4406d4628ca892915036329f2c653cf48a742974e0b2a9ae25532a4ba5f9174b852a9666452990ba50b8f49d51e931245247c8a452914837228f26551cc87a37591467c1e8c26551684aa2a811450a2289903d1058aa1e40b433b2e855e4d06d4ea0ac93411722814c55012889ff3953f88267e1a54fa6c99ef8953db01e7aaa4cf2ecc9e2c173be82a76ea5cebf889d5c113a6d2274563ce69ca9c841938b722703a54dd18b9b6a0f36112e6b024cd314a9a2f1533fc2a675a44cc60e995493325c26641844c618c98819930ab2660a654bfeca97a0952ed5225c944cb6c89969e152cd01e58b844af6cb9592172ac12e54e63ca788b948d99285e2a4fe2549d3ca9356992644264bb44494c8f921b9d23ab2246be448bfc7913b93223a1e4382448414c9043131fc32a3e0c5479acb8f038f1d422a3920547088c8de5151b572235b44c6820d8cc11118ff2230d04c5e64c8b8d9916a02e2bce6c54b8b8a6611141f2e2784544cd49893e97120f3223585c455c7887693109d221fc8543ce8a875f110e59221bf04435a0a8642990bd82e168a542b90a85369309bd2e12ac4423f8a844e8f08142a0f703c1db4783479d05d4320a885c1224b82160f03bb2606265c0a1cb810a1501842602585403387803693001529feea5bfd2857f7914fe7629fc962bf89057ed418fd6515f9b243f1a487dfa12fb1a35f5185be92887cdc12f92625f1703be0b8b7bbb94f66f39ec683bd718b7ac090f53a21e9dc43d0c4a79df0ef31429e52c63c8f8978d31cf0be31e0c43bbfa0977b910eeea25dcd84bb7f8a76d58eed3b29d94a4bb0e4 else 0x1971a0f2e061e5be)
def rankPayload11 (i : Nat) : Nat := (if i < 6 then (if i < 3 then (if i < 1 then 0x3923c4304b3257d8399c3772e78cacb15ce653fed36ff60a8305192b1094b1490a8dc7fa3fbbd43120429e6628ec81417cc65a28dd9a9495fc8c119663a7aa495f6cc74108cc94ed8558d55749629f184a516709a7ea28ea8107dce73b0a243933ea057fb8d5114a3228868b9c666c55a36018026907149e2f18891bf224f031449c0c530545fe832c4fcc54971b01f709a494c74f81b1147aaf30cfff08479ac85b7b610350beccaf3cc982d05638d854a31f99c9f88144e413b58f110995e4264788e52d151f93de22241b21442f7302a42658676531b2a3ea715bead735c30fde6312bc4eec118fcc280cf735c07156aa8fc9e61a783d8e1036ded87b620bc44ea14a3f0017b4b02f30d3e022850f145439d8d064c08d63ab1dcc2948d93f13c444837ded9e221528e32a40d942ab7d5a522620a51d8f4c5bde61bacda5f7215edc217ae94c41814ac564e0f30361ab058ca416ec4ca52a286dac3f3d9cc0cb306318c4f92bf24a36252344f5e237ed0a143df6017b9d80b23551e4c55a6c8942b5e0caf551f93c66d034977d66c515c4a3587c1e21c31150ac7e62daf1ef6ca30b24989c2c59ceec1032c1918ac6eda632905f7b0d28a8540538a828cecc6313a984c14ca09b05d82540822cf19a9027ef327af354d9646fda0358632985a669a7fa9cc14c6c6031a8bea0ec0a33463c81c55ac7581b1017b76c511c92bde0cb17e70af11067bc84e417447c1e23408471486fb3a84d18fc9e83fb6197d83f3862bc0e0208f931886c431dbf4ec962d8684b0fd43833d9285a150651fd0f11316a53e0a6a3a31b018ffb447b4658f62897fea97df3833f9150e856e4d74bf50ab1988ffea9619d12053823a3ffc3d8a94b8ece9ee23428d42d0a541b15196d1214558db36150fafe7a9e14ca73cf86f6a816c8ff0d1d941ca49d923b281a8e6cf05ffa0da15306650107b01e40851a2c64a1920eac57c10b241d0caacd9c2e38d87c1238c6be39f043096516a628a04470859852b04f3051bc49503f7bda985b3031b4c7f65b0fcccc2dc42169390952d28e8a20458a9a0c8a730908270276ea105e1b3483a924a758a7b84228d92cc2031831329c67e66610985944a6508a2518cdd461850e707345b288d2a17d96f0a57298ed44b062899467e390e4e4950c7640bf22e51b41ac4ace30a20368453a841ce020a4c416aa8b4540c66527c9a184ea321a79bd8ea6d30731980c0c28428cfcc2d9e1636147bf2e9f9182b1c4cad12016b652fbb5c2c7c3cca4b03048198e3f06a553d22638fdc2d99234c7ef0db870f8801a6508613a8d6325781ffd06c5635b1d45a07f10c8a236b44951ecc2e19a97dda638fdc2db228dc3ef04512858aa6d78398c42891ae38fd5a36037b308086278fc1a238abc2294826925834ae2d7e449ef072190d3dc66927c9a else (if i < 2 then 0x91c0ba7251914905cb711e30a0474aa3030541b762a56c48528d9116626f2764cabdbb25396dec2b70a490d47f1392b77a8954c8624085681295d197b43909e550ed852085b0a420823a551b2d0bcc9422048c550ca312a9623f6632524e472a3185948a3e662546683155929b7c17d81c098fc7363b0a9cbdcbcfba0ad472c3159329b31b0d2969ea0a3e6751e9f8af2338361ffc9d77f1464ac9142b1184718ffb4d8c297872655ee9b90a45097189974842854e23ffaa57c65e31ffc6990c25e520b307d762c447db150e8921111660af25287fe46d024e6a7a33acc8ce1b8c99f88760a96ce600eeccd923b563b4ac853c829daa59aa2813419d292807c9ecb09344fc8c7083822e930f7e1208b95c8a350842a1ced8253b914a630e49898e90b63a405e11f7185a4881d521af0f2295060a2880210a93ffc93ffaa45bf4f618857395051919b936433741aba503c1a014ae8c399e503202c0ea310ab4ac16df38689fb6d2db2045592c32d51f6029c4e8676218468aabe9b3672b4f22118048b43f108a98e4ed69610e60c851d4909e7862e804982d18cafbd4247e42553204fde01becb0594600f04663ac3d172bdacd5140ab0db8a2105e1eb3ad09f9136e94c7d06ac969590adc90363a5831b245a2798803fa8fbde1e518e2a07169ff0315048b4a28560422ae91111c6d2ca0a7e2237c434a70178687429042a6e8850243d8823dd82810b175189c285cc1071ed90ea2b033dbf091c163b1741b7211e888fc05a7e53b1164f719d0cd9d3a8c448ea8a2e58760bff65a53bf063ec052c67e25a5fbfdc205a48c2942bc141cafcac0daae416c3a85b04a774bddac241514a120e955ff11796021e79c18dbb185af084fdb1191841450e310fde2a11905d24fdf90861a0210a3634e8efc2549fc44ce3618c0440e06c4502083a5a6d60a0c6a038c063f0919c389034a739b38df9152bc2320e6ec77609506fb3ab4b04f033de6514788a4f53a8c0c97e4542c662089d4c62c2350a93ad1fb04a250eb7ded86c0c30afde1b0a9df46a113f6cfcc5d6ded5c6db298dbdab0d898e43cc55ad98f768d8dc6c497c622a507980bb04a8307493a8d0e96f60c31413289ac9c4b8fd822a2320889cbc87431ef6c0c215083cc1c262461929758e2c0c4fb9852756826d12afde1614a8466fac4f379084491cafcdd11499d64a27618cbfea92893c15c8f6054ad3ab2462f461fbb4a7b66d850ab8c6f1b62418c702aec305cc231f99d128608a828c7b056b11571a51914420e02a675b61f68b224b9e1df80bef6045df71827ef19b1a4213a498514a8910bea1cfe9961588b766e935dced4275b1d9464564b2931f781fcd7a334180393693b9aec491422a6cf14197b1354b1ec30a254b15d863c66094e229216e4e4a65f8e381c9efb4c408c2db7d6633d8 else 0xf45e61d1599e519ea23016edd8a42ef8c5e00d15877e46db4215ab2d121d3ca2c854a118a62e6569b13f69ab02f63924447f50c2b0e232c14039f102881bacdb3671b80aa9a6b811a623a9797528384081be7173588b5814f05a66fca6720c87650040d31df80b14e9be9169ee31950e01d0654f53cc040298d154f27b0d15e0b1c41d90a527127a4c74a5e33054b2659e0a34cc9df47b76ec53ca33d8e491618994004517d461baa5a8f2250a1326389f7fac455a0a0b0cb71940da7283b4d42ad0f1d842493ff68ba98ad58a7c05c6305686a952f3fb4b77b860803de3c894284c98e27dfeb11568282c32dc650369ca0ed350ab43c7610924ffda2ea62b5629f01718c15a1aa54bcfed2ddee18200f78c34002186c6628b404a146c928512a467b023e0c360d612e894284e049b41dcd79234400f93df68b1ece8916154628569d94046116206ffc15f7ce13942429ff6888a87383dfa11d87ea0382158e28d459318810042942894ee7bcde2bac04220e4a12db673a150657d9202bbe87b450ba3a91410411f63b0a9c3dcbcfba0ad470c3158328931b0d0930fd4147ccea3d3f15e06706c3f9cbbf8a305648a1588c238c7fda2c7140f2a3733c8c2b47ad5e61dcaa5478864efacc762e700b25623e767dd19082526fff97419e60857e684119ec0117392bbecf189f11cb0c1391a2a9f2f14543a527517fdc679172b766c51b388a7b4d8632f04e4698ad462f3151e2e631088ddf606621bbf253211c84b7cfba6ee58efccc8294a7b4c95f60e8ec3df93902c894a85498e26252ad2505965b95e9ca4ef750ab4bc7612924ffda6ea62b5b7f18c95e9aa54bcfed2ddee58200f78caa3142b4eca42308b36fffbfe4e27294853fed33550e707bf423e9ea040e30a351a4c621b048764291428feb8f4390b4093b0caa1d825388fff3a6851928fa9ec8426a705f3023e9e408ebab7bc26953ff884a4f35876b9d54b889333bca58a89d8728e18ad586580ea290a2a9448d29272605929beea78d946c4e02dd3929c0c2bd1ab8da84c1c0192bfdc679172833ca4470648229ed323631b6ff938872323931aa4331d0422348dbbd4513e5e2048c6cf565ce3222308c4f9f917089cb09cdc62700c7d0d3fc725a62c202a7e47c91126810ec152c894a85498e26252ad2505965b95e9ca4ef750ab4bc7612924ffda6ea62b5b7f18c95e9aa54bcfed2ddee58200f78caa3142b4eca42308b36fffbfe4e27294853fed33550e707bf423e9ea040e30a351a4c621b048764291428feb8f4390b4093b0caa1d825388fff3a6851928fa9ec8426a705f302394532b198642094b6452c11851b25cc711936938a09941c946c4a2836f622092b1362b27fed3102309bf84a46d854a15121977d51e9ea377d968c2a87397c5cc6db7e4ed8529948d146ddca9db1235)) else (if i < 4 then 0xcac92945291ae2bf929bdedcc80a56ea404dc5588c381ba1bbce879e1ab953cc8439423c4e0a63182d6c9c7943582165b1dea7583ea004659179cca6a9d37e922610709ea467d2513ef054d57a95d6ec01b7af18de66aa9add79ba90d92eb1344a106b07d47d8d62d448e02490e42218b23532615ed53a9615fb4bd2414ba80dc8392bad9510f65d6d4c17c52fb15ab549ccdc69964f51334adf5494aa1d990c76e62814cb9c2728c351480a89b844d51e18bc2e7aad4a80d55a445c23946182190560cf13d44e17113a1d902a5199839541a70eb121de2f7c709238daa4b9baf52a034a8e397393858848c1e1a59189ef7862242cd0a5bf84504dc318c6e53138351b1d4826132eb414fed0c3f320ae40345f9c3148449ad9c6c00311993858ea417c3b44f7bc527d7b0c42a14a975a38792b1c9d078b2373b1c62b878c2dc94413608be18d5077bcf83659c318dd7b03614b18b245a9858ba84bed3af60ef78134c8058b1cda7e6095020e0a56b7442242d8c27da31459b3d8ba8313ec264a1127c3b4dc0d484e414abd6831e463a0f3415826f382090890dc1e2c3dcc6e6224f09689499d0799ef7861f99885429402995a8de70412112387928e94c4664e13b7c22e06edf0890df944eb7a7b0f310c1367b0c162c55cef8768a5d68a4f55c62c5d3fb520984494e799c854294c25d698892d3b9e629352139052fb4e0b04cdca62e9ec73ccc6f87b81c14a07b038a6103ed351ed819682b749e60cf2339e65a7e0a5f0a96fe1116e4a275a1169be72688de04297da74c305054e94c4807fb520a09f2150a5054c2387ccd3152b4c946c6fa8d89f60e1e4ad6e932413f7886d218e080500fc1b2c58b4d79fe1da6be3c9c5b185ca12b04582cdf393458d50d6ae721b4886d274144313bde39e65e7521390486d27f6a415a7993d22a56b091900e442bce79886d200a63705370798b1698b360b0c4cad4680534384d0ef845a59588c3ff538e9cc58d663ece1a6355308d1f50c60398f329dc0f4e182386d17339cd74de673fd4efc8309a1490c24ddc22bc6a17e39cceb6d3f42923e7930ba1bf844f21c208b4db3968ad1e50e98609abf84490a831acfb475a13402fed1ef78741e60cf233dbf21283689a149162fa84c7c6ad5fc22017a9c3785720990a0fc7319a3042894b00cf59d430e5838377e0e9e3084b18e2f13a2bf8d20241f8e182ca57aab8e55d1c81eaf41e84752ea30c981463a0eb12a32c95481e3298b4c32040c162d37d2209a6211a51481270b25502a6ba7b0c44cac561e0aaf0dda22262f7247ce24627808cd9262009783418411909e5922f0967b7316983b085458de7604788321d934f70ba3aa0e1f8887f501c52eb2042248cb6e2a1cc8408f68d3cde8bd4019a84c44e611ab7bd41c9abd8833d991f70aaff53b215041624a else (if i < 5 then 0x5559c2dd0f050cf6ae544b054c310620b72ce53432215fc864273186154c1537711e1512d5cebc8eb083e6b00cfa4ede6a8e30eb35741bca2813852ce30e0670b915abdb32ced5c41f09edfe5140bcb03b5bb97812b8c59eac1d2a4fdb26590150b56a35a776c535a95e8f440a5cfa51e2153aaf852819b670093f6c202a122ff0d1e16d416ccb0d949534c447952f7b5530f7d0c2c515fb4c823ac32da7106e14d51c633e2a48490776f06761b99ac0e35a75d63addbe2bc90a8e476ea545c23b4ed4419072a36ee910eb76ae210a236c13696b9db7321923a4a355aa448d4ca295982cb62bf91a25085065106d7042dd527158666117eb1a946550ef17be6b58c8e1953580dd5ec2ca896ae7177c8b9903b5f696aeabc418a9d6ec20e035d7ac0855bac81358832798566512ec636a850c5643c27ed1e04ae31908a7b90475f67457d215110738c83b751efaca910ed786555badb912f284bed367b16f30e8c051069ee2b4d680c6ca8741ae1e78b63f9087282788a988129935f95586089532dcff15fc94dc3b105c8d7362b71ba83bcc705318cbb194e0a36189e536529aebbe9224fed31ff7b1534172649e040e56d37c9f11033c6227439c8f10dc85b764bb16fd2220a8e22743b72ce516cd9efabb4591634dca2766dcf6490d2284395ad46dbc39084a22b7e5629e915468f1f6418826e4527cd8a0a457b9428439414a83523d5b12f7aa549fb67ce6313b36e758a7a454c832b2090ef0d1e5ab20f38f01b4d8ed58f65ec7a8dfd262a6426f7dba484ed79d1ade1c240e338295062b75482491d7dc148af727ed8ad6d8d251afef356e5c287e6eed328691b7230557afab5f03589acec923f215ee4fdb3b0bb3a0cad6b66e16c84e8155a39dab670ead56b469c2fc7a09c3d0c6bfbd409287194152433912163211a28f3664312e9e827988bb1ce4484ef92aa9ef69bf3862b7336888baa472a837c248313599c2728af37364fdb156b7501a33fe10a6b634ef66ce35af4d6c2f83eab56bd7f19bfd45f3818c51a48e88a28ea35016adf17be15bea964121ca514a68d1e1a4918840108360418959e34cd477d220625175d867d26c3cf0e11dab5f4e6dc9d6d9928b19df38b9a1ce36fca533fa1e4a06af113618b1e83168ad6ce3c677ce2c576d0a9c3db5641dd79516ea03467fc214d8edd8bc3aa00642ac64cb07563915fc98ae51749e7151a809d8870728dcea239dc2aadcc3aa7d8ca2c57f23b126a8fbbd9ed045e1c438dd114b45f0e310668ee93ce2efd8a5e4ee1ee61afef31b9d45d0f7b5550a02e50a18ad3b904c6a79446e0b30c079984fa3750ab593887448fb910900f40d1456a4a2798ba6dce92e6a78b91bfa45d0ebc6983d5990875e38081bf47388f1a491d0920c458a7a4451a3c2889d0ea8901344a10ae4f5b0c44a314cd3 else 0x916fd15e07319ea5050019f871349f0477a428860b147523f910ddf67adc86321aa134c425aa262e562d3444a83978a97a39ddfc1521ad58b0efc2b2ef54140182f04f898ebe47798d05a286154c97c1452705deb3393deb54a3ded50e0a98a2c53e213ded5453bf455b93ccb577861ad8b5172b7f81b583a4bc504f7ff28b452142b97fefa8e4668ed77bc282be3a0926794769cf712ef39b05e08d7a8d6943adce4a0bbce6ef7ad2a76c44cb55a3fec996c30a96688658215acc82fc178b5bb2ca454a25db1dca0b031b5a084bbee940c5cd414ea92dff35ac6b129c6514a5877ca6f0fbd52f829526d9938b5934c032457c75894e37528b58d4a73d424bbeb176490ca1a8e3c4d541bde5363be46c5a399dff2dc9d6320a5139876298454575c198247e4e762c4f7c94588c2320a73c286151273052170320a578bb93ec6af362867e04ac3779fb7c235b0640652fe0b1184dd5e042cb2adf85b30b19047549cc35890e202a756c842f17be7d415e65320b6aae938745ec9d38a952b6814a8a2364fb0f18a54ada0555a88f6b0216b72c68aa4fbe02d5a2889e615ea1d925ac9243a491f94b57bb1a88c331940b117578652a243b0c8394415194c82763e2ee4b0646c3be357d042d57a3b68554c639d28c4ff53b599444753e774b7493be1431378d1d729c8dfe521d679a52329251cbf93582863adbbb1cd0a5a2ef62c68cb10563be1ef9a06d35b7332873c3ea3e7745095c52bc920cfc2d9940c9ea33218e3c6c55591c5e2f7cc8b1aa1421df3ba73584e2545358eb2d5ce4d6b02156883a7baddf72633c091aaab1a3ae5364b542862a051f288ada4ec8751f411a6763dec58d19620ac7393ea0cca1d6df58145d8a6116320a8199053a57f388a8d46a091d3a44afe4780e9393ea36152cef679d89b631a89fb4b19b24f0246ab61df1a8af500caa0a74094248ed3a82a43ae81aeb106edceafc22622f6c44c398a9444946953a04833b733f10483d3573ba8c3ac26a35224a348f398a95de5b113075865d9476b61b9856c54bb5d947684190755add458eb3a06754be1ad4f030c3aed3d4535740bcb00d740dd0e6b4fa8dfd26a8620cd5d023c0c36b94d6a57a82a5e05d8194ada92a282ab5a3b93ef808acc6269140846e2b57d042d15bb0c5b0dfe86c86baf59d033aa5f0a6bfd8b2d5b26ab415061c1530d2a517f8bb91c9f50c0d9627a8649d6c7574bded5427deb113fd4e8847ce201e0854ba910a6c9646e37217d0ca96d645b5b07f12d0803d03e4561592ae15f31d91224178df28225418a372f6135bb82146e024bc80905214c6e8690ce0e6438120ef08334d882f2aaeef4f70018d62455025b3dde42fe0c5d57a9de13ba80ea3017033b083aedee65a46765410cb4fd56eb2a3552a2c6758d032dbc026f2d259c68f712d700e9610))) else (if i < 9 then (if i < 7 then 0x12bf880148efca3d4ee47863349d615b194ef09b9d395c8ee4b72648da31db30d57d4da286fbd44bfd157d45cab747a6ad0317936f455b504e420a1aac28a02986dd0a98ae8f7daaf274c57682c0a83131e57e179c5723bc1f913e1e7a580a52ba225ca4fc239b61d057c437dea787031e238b0def82b5f0a41405dd79917916fd14999ca36792b2094646fb3c4d30da58aa47d81dc10ab959eb642c90c8acb76a0948494ca4cb65f475254bbda6aa266b02ef59b642a658f2b4c2668ab4354da8f7b54664a75928a1e1f2eebd778419a16b3995bcd7a0560a335ca365d96d60e3746dc447046b94437de62c54ab43c8c12698cd67854704c57f26b465bcaac56fbb2fbd52eb7da6ef618966364d52c642a15fc8ee78d9b395aedc142b318ffea7313ed9d1efc8c1531a9ff73c17941a7ef0d8d32d964e9164e132bcc6ff213b7e945241999aca8a123565540bf022419cf79e28e4ab26a9b143227e5b4463ec68ce335dc20f5072cf4b3c2e139ef013f6c45e3056aa8fba1530d67b674b7f6aba5148e2b226a84a5295eb40caf02ec1894a0df3b50c0548df0f3c257ed0af50f02340caea284afda16761286a8af662b0cd8a192a5ce7996517f8a391e3b0c512465acf6cc9350a649f726311593ba5bfb543056a73de783d0541b3158627a8c91408e828d244af5041d4a890adfc2d986a8c3742864a9727d41ca9914240e33ef8362863c761ac54c8e73c6977daacd0a986d6c7554727a8035649f6a8f0ee14f816fb2dcd30ef41ab1ddc035a0896458cac3bcd30ee08168e04d5958f1eeb90c66477a73caf9575cfd4d92efe3e476959546ec01ae0e3227c21b77bc70b6bc5d759e6c82aa0bd92bc3eeeed0242ce54123b7589be0a9e1372980d3ce0a4bd80f2c1464720582b540859955ec56c0c68ed22a81797f82151b11602cf73054994a3308a2872883d1c3535e08162049d281a10c49897cc8c718da922cf278160c682f23f4170fbb40a9615f2795d23f397261862ff0279860669d281b26c1f892566a4ac3bf3f063cd91f8a88e40480d4766045b8b50b215c66d052ff11c4591f166827bfba22c35c8edfcf425e0c40ffe201df074f0bacbbf5a084a225cf2571002388b0877fc008e25df820865bfe64b78f54323f9080215d24a06812dff317f81b309e6c36fe5176290d68294897f928b4718b190d075415f1de186129448c84f7b4d6c698b165a26577e06c6fc0d682948b476977f23e922df92b0410d98cf30c2a98e5dfc8fe465321a9badff25597718df819414ae3723c920de09f84f10c8218dc4a2bf64614ab39593b4014ebe3b3271100319749d990ca0a4e77fc83756e81160852c279ba3d78467d241b36b91c77bbf57250758a2b7be6e2cbdd27e11414ce916593a5df2b77354aa1bb45a54e77b8bfc0d682a48da3b56e691f4 else (if i < 8 then 0xc34dff93509243410fb8451058bff2c5e5162ffc81770653cb37a32c764e3f61fc2f63d70a1e617e458695b88410fb84ebee0b8db17be40b8bfe72779e58b1c4262187b2e76f0041c78951825272aff844f7c15e8a7c25b9950c36452550534bbf4563d21572a64b17fe60bc6727ddfa7705a806e43a099c6ab2678b781d51fa6bc491421c0527858e8b850afb649247e02bc6661ac828a1c695e1380a57f8a990270100db8204906bbc0ea981c82616bb48696941a33f642281882d0c9828519a5dfa28a85c2af8d929119054726483a31da5dde58bff006daa99293efa0b03f79d21150c61f98bf0102d1009235b84243c5019692c9c23073470e8ca5cd4aa39324654ea0e8c75aa9916248cb58bfea75a0a1e337318de0cad561ce06530850c4aa1aada42cecb4d50bca319bfc15906c51c94f238fcdfb1f92a59d588f71e2195ce69aca8f35daa6f2fd0ba9bdf1e4169f9aee2716165d7628f1aba30e062ce9c4b381ba4f82b20626051439dbb732aace1ae96fed3152939ac0b31c53081ec2b1ef908c3ff539c24b4d05692c7a42a8952d83e9857a8c3ece977e8a8863dd75b5dccaf02571a56907376dd5da8d1b73948bace320f13de6aad0f659385cd0870b16576fd37b5d2d23456ff53961a9584eb0c64eafb5384a425398e4a16d0aa15ed605aa57f7ab6fe330016f09e1f0e6a3d23e7983c8e76b074b730549de11048edba8eb30fff0e55ce0a11b7bc033e92cbe1c73fd960243ea6c575df35cc1e463b31a6dbc6ed75df14b3cdfdcb9549f84bee1e02630578d3a50344977b147b128ecc62fddec2bdef514352f237c49e281a85e31dc10c6a2bf931e5aa26c8561d30dd6a8705134d82f99e1f0e77985bc2209d0074a31e9042a0a18f4578b37c0c97c4b89a178c5e23b40462b59a92f3be4a73d4463ded561854d308bab6bd53a8594684247f0f92103e01c1c90b0a637c1085a38e4223093584a77e37911a2f40792f0a650dc58393d642f61853176374a080f23e2ccaba53bf0c69c80563f20c4559dd9ca23e55fe7364b0fa909952ea77239023272a313ea0e474478d485642aca3cc19ab84ad494ca34d1b2698acd15728cac16fb2cbb28dcda9cd4c350bdf2355778a429caa87cc05fd6c857bb051d8095733a46c84da0f11c2be61d7e195273fe4c11f2ba22f0ed55363cca987fa2af52f2024148531ba1a43383924207c0483921614c6f8219268f30dca82b51e5c4bd91955ca2b12329759a45e6c4377e0a3a4711e175a17f799e1c0da65033de663c10ddf82b9947982fb0443bf25213deb315a919e1d0cb24ca2c7cc977c9d06e5df2716cc42877bcca0a973b5a105729ca4ef33a6c42de9e95e604e179cc8f4e40ad531de0361b38d4ee462e334bfeeeb326eb182b255fa490f08fc20a87a40fbc90260c683bc900a136ddd07 else 0x88c2ad839df0dfe35dee116c19e37bc741350dd8a7c25b31408f054e354480b33d584956e12703e0e8657f908bf844fde237e35bee169ef315d33c5df806e46ce05629f09230a1d2c8740aa5ef5494842af2149e1684f9b14a29590ea11aaa0c0038cd6fb8552f7aa4a550ac574c52b99ddb8b121ac2d3bb2b4474ff62db3bf7344ba8fbf1f96f20d04320454f64206c4fde59df011bde199c0d14f07b99cca4e359c448e082d0d5b3759a78c4aa1a37f451ff9681b2020620346832b0949c6bbdc244fdb0def11450e3643a84560879cee82cfbc07b67f6a43698a8543b7ee15e291a1ef0d648649149045b4846e4d313be4a520e532c205f21140ce1ec5ef5499514252a877c85e8405c038d96d48526175db6733c87dfbf36c4511901d7b84ea4a1e2e128a406dd62a95136bccb3ac48716f202a77d8d5eb7451a47a35ab80190811d0618851055654b5afb72a494f674b7fa28af50e125a6ae0b5984fdb35894eabfe30f43614e889a065210b3cc34d7bcd902693dc237fb62814551e36f0080d9395165a307c54c86d781c9820ec415ba28d23fc5bfaa46c1caf453e12ada42dac502adb474bbf45795093dc2abea5733bb716243585a7765688cb48cf9c759468f5b2d2d757597576f4665271d887547953216f76180ea8eaa64d36a5ebc7625103b120357f6dc82d361d8820e0e55a22986b5b4956e4d33aa99351bfc4c15e0a36bc0bbdc28a6d0a7a08b60cf78a991c24ce507a609c7a56421ee95b49d906159d392ef809948c270e6d7833838071ac49183dccd7e9d24e54bbf3aca0683286fdc2f9dc42bce59c0d5682b60e513ccf9e24a427b847be1b591083838d50a022b345640c54c6a7c1549f7d046c29d11340ca421679869af79b204d27b846ff6c50270fa8ebcf326d20224043c4a2871b2cb2aa046bb958d93aadcc803ed58967d475e3b242c7150694289eb622fcb3f10af6b58181ad8f3350aa039d924a15061797727b84e01c636bc70ff0e61501e6527195967d8b05d388a92ea307b1cc2b836248fbbdc22b043c7b5193d79f41338c2c60c8f12c9c22c20aabfe5625f33a5bfd14428822dea3c0ed8bff3e1d79ae06c9fee50a9c68527868b293a15fb4ab290825fb854cb7392d51fe9f0e703041cac44a18ec76318b7918e620949c84a4e561a252169f75dc857ad289bad34eb0c4be630bfed8c6b45bf84b58a056bec5f50852786be1d7962f7c96bbb281a5992bbf051bf897cc617b1e5aa489e06857ed225f32d5d8bdf225e33c9fc3af25ac1bf849cee635ba415ae03ce1d26070d3c3af258e2e814d7c7ef4516baee5a0a1e37ff0ebc6eae3693f8f7875e41bf84bf2ce3103461e912841a15fb494f2cde8cb1d938fd87f0b71b12f197a7a42281a996e7229cd38978c773f0dde70947f29e59bd1963b271fb0fe178ba04)) else (if i < 11 then (if i < 10 then 0xe1ef36c5b8b3e9cebbae39b60c92f9ab88103076b410b31d91b36b8b336f3cd6367a0b6fce1e6228828fde2e1d4bf92e9bd5f3a31d51cca614e514743a91491f13b5b57ab807646608c2fc98c5718bfa50eaf784f471243cb944e09e77f351c2b459afd188f80f1251110b25055e8abda7b465b8bbfc004f621e0e015ca62fe8d99c1fd96f2e77b2f3a487493913e6c823f2efa5be168230fc27228c231e9050c97836896e2341ecedfc404bff3d2b7e515ee9e4d4b2ce8825508d1750978bb4229182bf1d0b05191732b6f0df43d244efd9dc5ca52140cbe59a4ef3fcadccc6e419a2153cef9d2367ddf4a8fa2298208b643be053a418e77087237c8758e6f28325e4c621f092405d214a9de5360bcdf688b543a59cb11e590ad8891da7275e007f50cc8a45d1c68978caacd14ea32d284a01bbe8685de144442142bf69d294d3cb21c26a5ab42f77ca523fa81a638923ffa9d43f79446e4d16cc2958d471743aa1bba3294b1d49d75f9579139158c9417c63f2358af5c9eb67cbfc81a5ee09706ee649f600b031010326aeb587324619c609110f78aefc3483c9d89b460856a7c661a4b1616320a19f881355e8096eef4ca1a3b27f0de5da1366b31fc00eef11d6c88b015ca91345d42a0a3b5da1197f43a616ac3003056644ad97762cd94ecb47227ce403cd90f04dc92103e0241e90b0a637c108950120f46f94509a5ec61f6148a14b3962348a23ca0c904c86b1fbd52c67727228d9ad2e3669588f3547cf13ad63a4c70529df8e5e8e28be6513decb06dcfc3649f64cb771928e5686557ccc27bda62c1530d5449d415944299c93a45b5155a5c992f877c2463fa8457ed3a521a5e10612fde6e6e411d251b4fec44ae307f0ff6ce0c8a9183694a7858e337fa3a11fd0452316b2123fad839ca12183f6d37ee15594adadc8219f38eb28d1eb65a5ae8b14461fee56f27705a8e74fda82a4c23da8a549ac113f786e5270e754a545f72c155934cfb54d3de1978280dc84a1418c0038ce77c56f23ec54ee14a15ec4fdb2ae03a225719c2490b01b90a42731b2ca3570fe5e50ac541ab3c27ed859484137ee17c246cf55839cf3e08ffe226718fda9782a9ff097210b3c0754a31534d1fa42a1023f640dc6094841e482acf584fde9bee6a12481b5bb0b481df45bf848eaa6fd6342d5ce55b58e4a9696ea3dde78b1ab085948395fd920d6e2a9487ef062a05e67e1c8218461387f909216a27016c44b0355933d81c82709339416fb84fb260bc56f20b16afdbfa3d078a37e4a3ef3f02d420241882f14726b121d62f7aa5d8613f6cd6b157fc0a2a539cd24a8f12d396ca8464134dfb8531cad03c0863e1df960f3027a308dca8ea214b13a82b51ef848ccc57fcb04df8733818def3cc93215252a87732938ecd7321ab2925427df2368bdf29349ee1350 else 0xd500ae52da11a5d3017e9ee017002b8d5ff6d82ff6acc48ca305accee5c6add0965793af53a6ab68d374b2bc982962b10ab1885121ca0a2598ca32cf19cae44a542a65bfa094f60c5fd9eb8a44c08519e39ed8c79e6bfd758c94abcd97760bc812844c05486228df812b154cfa862a6572a2c1e8a1827efeee6c6882112056d892e42320abfd052759930a36b17975f68489395e21b58661aa5acb1d71c05e5ff6dc09e618e65483e5e4048290a63741086707b56180840c1db68211b81ecd99d716f3b3682ce5511442e983bec5708505295c7dccdc2dcc1ce0520349180912a087ea2e53cd3b4126aabda908b231f90675f0897d1042d47983b47245eb2c8b2462a82ba3bfc257a9544622a42adca92c37be8a09b7978581908d70e82ceb98efd1debcc842c9787a387258e25a6c911840766429831047228cafe468c625d264b1c0c6c70748ec58e273708c34b4272cf92233170f4374442e12908552374a089d5c669221bbdea30d1b0b7419c46c2d1c683b8bfd0dd234b639229e01c6bcc5fdb26b99e6faa55b7639798e95bf67ba2265893050e57c24ce915173bb15f113b0c438195e16fb001486242a192fec192f46ea0cd763d1cd4494821375aff1d3d6a0779a7683c5148e3148c15af5c1cc5085129ccafb02df84621d09005e5a3adce62c56ff2f0e31b0e42a54e3c9271b8714151295642a70ba773f2146523056b0748c8c51c54424f68b98e27cdf90ef65bc5961cc901f270992c49da26c41620e9519e4a07b43790b15df79bcdc86e616712ee085934c58628b857292bfe5d86284c76b01cd06f04738954f67b73ecc3708e27444ec363832430b061905519c67110b954aa7b3de2898bb2157c1a68dff14d8c43e0a8e45fe860e0636398844875ae521e02d9ef7f88875aef8ec89b4498fbce695d4440a52908a8245fe863da2844d50eb71a283aa0d980a729b1881bfd523900e47647ad7bab68e01105615513ee814a4fcb686f0a229d89f083423419d51335122cc36ed61bfd1680b9ae97c39e4e588edf68b59b24a5e0ee544c36fbc5d748c5d358c50340c7596676fb458ea63d940b2578a266a3bed31bfe741c37be8a2a310f82a3b1b91dd9599b3e7767ecec42ff49633df4564151d23ffc0932ef4f70c7012330f999c41798e1a7613992e21ff44bb123b0f98f6c9ac3d20417834262faebacb36997b84a1ad209338d37a22e82fbc040c6d442357588d8a8591ebc78adb612f1319ef809114f6a8c1dfa3919f50d3b14c939987cc2a0a305687bd598210a40d47d10ac946d9d07970e7154a13f78a5782148a996a86d57a226173079592f90b50add319f50691446b731bd1cb108290470c16ee1c36d7b2f5e51f6002497cb928a50c099d77aa48de40cdfa8de735963b4701965737b473d4ee1c2a3ec243ee802b717379a1da) else (if i < 12 then 0xe342081f129482f05a02f4bb5f60e4fd89f0856b099c13e0e6453e4b38c0d0197bad07087cc09de012a1518cea74d5bad4cd1f7d1dfdc839ce86c3a639ddf271c6866614c651cb2215ea74d05df4714152bd227598d850df052d150dedd9c22c94ed90a90e427c66e16492f629848f679de3868c829d09f3c9d2566c52090eb0253dfd94c2fee43a91f99f4b138509f6ad398b26781ff3ee6574abab62a0f7618ef30a25497d85ad709c918671824443d81541ee3c4d9b7546ec047ec348a2844e96d1020f41b43e13ee9ffa94c86744fb06208cc0cafc831de06c1722993a4109e34622ff91ffc354a77b523f2c5e50f3c2b646154a867cf10e77cb5f54a447934d3b18c4e2c752a96971f6662118d7764e0027de0f97418586b9e0f5353719c6c2288be2a9e90b15ca738254bc6009326ddc0571abfedb05fed5989c7319a9f90634e0034a266daf0c45c35618e4824a70329df0d24ba63e3beabe5219d77166bf46daf0adf769d814606ec1036709d1161ef54bc1de51529c2b4495d4152e33df9566e24e7dcc15ada4a06f07577d9f7de30f444b895e77b29d177de260ac32c9ecb14866cfb1e594e2a7d4342982547d409b51cedf6a9cbd1cc60649adada109fc331d05caaa278283fb4f778b2937e2ea4107bc10f9852963ba9c1f133dedaf115df768e338da62e11ccd0e3b247e7662e5190b869838dccde21c73182b8e353b21086797f9ad71dc11ce085239372168e00ae357fdb60bfdac1fa86ed5834fb98c9d9c6b039dda5f30dc1a62cc8278d031ac48cb748921c5967237f909ae794688e82ed616e902c6fe6bfc0430562e9870ba41c6c578216150a43e6c79e00f88caa19f7bc61029910f022ce357f1e046417931c470958b7790ba489c368c409bcf26ef79b30a96896df6989e252d48a182ac4410554da4edb0325d0406919d5431bf9abaa5f5074beba1e5450bdce2bc11445c391bfc858ba6b094bae89caa186df7988118444162c553a08858499603b7da6c7b38d1f9e4e588a0a894889c85d25433b51955612561b7fa29eef93bc943104102136a460ad9831b58f138bba018c92e980f780bd20968e5746b78f25b886bfc0ceff946f0816dcab184828a84a7bcd5031807f1037b6541196a32b15bc10a100429a9d4190278c5434bbf236029396ff9e4b710b042b0dbfc95f05271a9904eff8604c6621507bf03552dfc05edd44410719150a15e7986efc95d212b0c6e6cf0346f0828683b1bf231fb34088e821347bf03781b372886b178997709dee3542902a1f7e465d2862b094ba3bfd241a418f51a98d0b511d158a83df81aa14c97477f6a8f6063142918e3198855b68f6e8e9cae90952a5ef67af8d33f90b6a2acd8c43cbfc157c7f0242088e6816e610772250c11b9345f9831dedcdfd09e28eeecb5516a08d0b51347be else 0x150e804c385f0e0d3f07c658367b4e16cfed570b67fa3be2e15ef78b06e00bca6ec3402315da0b02a0c631f6432c57fa4602f87ac19232e2fc07edd78ef56baafb5f63be15ff869f2a112c7d8a610c5503b5b1678e7424b93dfb6b5e13916d811bf998dfe0211081284788419bbd222c9dacaa3bc09a1156ef94b276b2a8ef00a84615ff869f291d415243b0add3520e3ad414b9b57548d7f48826aaf163accc3f60754be1ad5f62cb6b940ca3acad95ea284ab35afc15d7accdd0e63dee7b005bc8dfd26873c5ba3954c081b194f844cc0a4750dbe9156d8423060c69a90376b8062ea0a95035052e083107ad4af51e05d9c8dfd263df40c423cdb56549c46cfec14ef0031bfb350bd890e821a076cbd371e0c6869ae619687b173386bcdc1372d1c3575ac399230ce3048887bc57fe1a41e4ec4df4252611d590b80c48c25be73620b3688211203ab32b56c4fbbd270077627f3fbab32a5b06588ea75af627fea2e544bd90cd664c28c8e31e5d7d7784127566b6ca13cb4798d7fb2cb85d9d86f86ea1d04d09149ee374a3ecf0c8748cacf123a9feb589b13f42cff9f7a310eac0b027cd89952ba5fd3a910658fb89fa24cb6214c851909592c448536c84134bf91d98e239088c275042aae216eb908c82e67a239088c268d6c0e55825ba15882dbe2247ad626d3f91d9e26544fcf113657523f62b6027caeb62b613641781206c5e60855fb88fcd0827811651adfcf26388f7d4bc1d3d767d7b7132aeb5a57a1fcc58ae564b71380cbe094a642a54b5ba8db7a9d2caf6a84841103418b5a18c4414511243bc91a211e84231fcc23fd8ad809b48f7fe788c572add5e237366b180b5a10586dfe0a738aa4ee1045c228f888fcc505033a8194ee1059c097f82ba42751853f316f9e74a57d83f024209424a85793188357f8380bae10e8832b0ddf8292444a172440a7682105c852995cb7c9ca204afb00571c13e2cc4d957e1bb6a2111d373977658ca52f3d44b9ff4fe27c4df0d3ee7fdd5d0ba92bd44dfe2a11fa165758efbf))))
def rankMode11 (i _mode : Nat) : Nat × Nat := let v := packedAt rankHeader11 (i*23) 23; (v &&& 63,v >>> 6)
def rankHeader12 (i : Nat) : Nat := (if i == 0 then 0x9c7a7938efc271d5e4e396c9c6fe938da91f1ab84e3410ac65b938c5f2717d65e2e789c5a8118b032715903e2a188c51c9389e22313563e252c9c4799588bc1f10d43e20688c3e693878b230e7c461b98ac352118656230c064e16acac29b1584e92309643e1168ac1fd1383942b058e8e05d5cc03a2b7f9446fe1a65f8617bea6a57bf16ef540c5e5418bc0bab771c5aeadeedd0957b9842d727e36e3568dc2854b7d02b6ed546db989db2d58b5f22b6b1e52d364eda139cb34d3765516ac8b8958eb12b1552b61ac52c17c957f494af3c315cf162b7ceb56965aacad2b58bd42b000955d0d2ab262f558146a8f6b54d316a93d2951b44ea254653e599a758274dac5297b8d52b9d2a4c52f48845a8eb8bd19894a29fab446f52853ed5067d8a05d29400b427dd6ccf6f189e5daf3b905a7594a4e76559c872936d97a6a4aeccf819992ab131795a6110acbebd39764292db3565988a4aea9595582d296b6e514e7c9e817934fad25d54648fae48e694916ea521f34e4202ac7dc5a8f16b51c498235c4bc677558c849f17db5a2d60ac55e168a332912f16a2366bc4355387e1a90e616219a0dc2d51a8539a509416610ccac1fe0c834a3505d74209f69c0e69981752101a762016ca3fd6d47ee3aefcf751f762cbeae927c493af78159ecbacbd46d979f430f29465e386a3c1bd877beaaee5b61db00abb2c1475f4a0ea0761d20abb9ec5b734b2ee5c645c92ecb8b29e70e12ee12841c0d29b7d9d56f55a4dde749ba2cab6f9136d3daed98751b130a35de186b56a0d56251a8a6b34db90691bbad14455a0aea33d59566f9bacd1a4197a6cb2ab9964bcacc86b598eb0d31915a62bba4c4785586cad307adc606c34bfc5697c1f0af41975dcab4ba9d5172e4bae11965b64bab5a75569ae82cf5965953b0b20d4162a49ac0918579f2cae28595ad48ab269355b530a985814fa8c29999852cb24a4d14d479eaa8b7d750f7aea1035d40e07a7f40f4f941e9dec51395c926e8574d63a699d55531b6ba605934ba2aa973a052c94ba557974a252e92d86922f0a241dd747b9ac8e5c691af49a31f9645c7a68ab14d14208225ad14468a088164d0ec29218115427e28838e6d04ceaa03e5a4000267efe50fb06e1f119a3db6207a5558f32079e2c923bb534760164e942c9cf0d2394ca871b050e00cf1bd7903705b26cb170d75aa9aa8d7345f48671d90cb0d398c62630864c610204be4b29778de2e04c659c79cae07415be412a894a52fe94a1e3313d1a6270b324c6e64956d2125d5e23c94445db9887333908e9e205d443f4c78797528ec8e71cc3ce3707986a0500cd9a718f8362fde9c5c8f38afe62147ecc27669c4c1ae8917e211644e2151743e6f007595e0d544a17f0a42a21304822b084c460f00981be6c82c72704215005a3ac07c70800035 else 0xf9ff15f3a62be6805fcba0af93d97f1f627e3264fc44c9f85093efe737debe5fbba0bf75311ee2433db2857b5488f66e17ec782bd83657af109f5bb93eb2a27d58c57a9909f50095e9a92bd2744fa3e08f45b11e85c23d034479f608f3cb11e75423ce24479b408f33293e6032bcb304f9484af26495e48723c80a5f8e68af19215e2d727c496678784af0d50fe16823c24c4783388f03813e02e23bfc24f7e509efa193dec72bbc805f7754aeea595dcc333b89c576fa89edc691db4023b5d0576a40aed2211d9d02bb3323f65887ec958fd8dd23b1364761348ec0591d7d41faf24475d007eb7411d6a623ac904f58188eae211d5512fa9b44752608ea1f11d4071fa78a474de09e99015d2cd23a4ba4f48149e8db91d14d2ba2164743248e83d8fcff6339eec673c78ae74c17ce2a339b8c57360c7e69b11ccf4239938573110ae5f615cb942b9678572b90ae54615ca342b93b85725889e48515c8892f90604f1f888e3c493c7312b8db2571a009e30b11c5be278ad24714708e26d11c46f2787fc570f1c7e1c291c3432385e43f0a848e11997c1fc1f82f85f04489e06293c06627805e3eff388df9997bed4237d0e4ef9407def695bdab237ad246f444ade5c95bc6c23786a3eef449ddbb11bb1b2775844ee9b88dd1093b9d427730846e5347dc7a95b8b31f70e246e0bc8dbcb97b74d1f6e2c3edad0adb2e0fb5d4276b0246d4d09da7e8fb4a52b683c66cf9c7d9cb11b3232765aa46ca0c9d92091b1ff2363644ec5ec7d88a95b0c827610c46c0bc9d7f691afab235ee83ebcf47d7830faecf1f5d044eb9008d6e697ad961f5a5846b2acbd62e91ac261f57c846adc89d58993aabb2b54f246a8988d4f011a99e23527c4ea3c49d45291a8641f50463e9f587d3b891a7301f4da24e9a048d31a13a5f31f4af25e941cad25f0fa4871f48a03e8ffc8d1b799a3381f45c24689a89d10e93a1d51f42d64e846c8d06713a0971f40944e7fcc9cfb79d9f22273dc0467a788cf16159ddf273af65674b89ce5c179c0937374a566d547cd75939a9e2734b84667a8accce93994c1f322a3e63209cc2c9397dd332f044e5d008cb7f1196c71f2d083e59088cb040f95c6232b084655088ca7a9394972b28aa4650787c9ee1193812326684e4bb87c94611924a2324104647188c8bc8f91421f21cc4642908c8368f90361f1fd24e3e70)
def rankPayload12 (i : Nat) : Nat := (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then 0xc669e10728fd87f083a58b9055c287b2250c719aa34cfc9ee101284d18aa9843cc7f10887695627ef2a3bf090108513643b169c840b7367181b20402434834008189c21da66d4aabdcf4e938669a544866a80fe8a4f0b66467257f4b943864a706830a89c3413f6c0e4c1680b2cede85264270e551267bc44b033b0c1c457948a10edb7dc24c0e906450b629f0907620b0dd42e891c55fea978895c6c3740950a0c6d8152ab3d01f2fa7bca212543bd28a42075308789b2144fb1dab042a252388cb13c9858170d5826e24e10e3908103e041424e1037e42dc486b41946268c526dc02106557865030090544fde1aff060040d46387828024e973042d25d331e048309fb66edd0ec3750bedf70842a0c20dc1d9e65271e70630623089aa1de42182b715d2d0241bf2ae3787c7c7052785b670032284c0e1633381b0cd4ae60578ec55e27304d50ad3de34fc37409629f096cc50233043c56fcabfd520248abfd52fb32cc0748833c16637060b7f61dd8c1544dc2d0d4312965981c2d449a60ca816edd0e53db02c39418c823b73183cb1d8ec851cda46a8012bc2d2911397b0dd42f8e762af727a84c969af02a29416938a4c981cc2e605780920aaa0d57fc2deb959c80714e6b463ac1352f9d19c0f916e8509cbd0ba7c408d792761154dba97b61cc0e94706e9046d83420e9032715f3855317b7cecbd9102d6dd081d14a8ccb792705a0dd738ab0e2c849cda527d8a6473a63407f07c54d87392e1759c9f9056e4c2d8a702260e05093f13a23c1a05ee8c55299b08af6c16ca75245d4b606452e26d11354289f7315ca2d88fa45cff8a4e317c7abfe69c6322470f38318eab24455d2c3b1e0e6107e1a68cb5233b1589908862522843a3ec57f2075427d46421289d9d1d0c3352b27ed802a0dcd0af05152b329e7115bea97d9162c0caf30692bedf678a0b85b02a564bb4559d27ed98c2cb6ce013ea7909d0e112841b437038acd8cae31d90c44e8c311097aa2405d251cb958eb231b4b8dcfe91d4d0c3b099d86d3b395c8d4fc9509a60fc1468f1e0ec115bf193ea3164a2a8efa44121082e414d7c08312590cfa4497811a20fc61ba16529e13402e2d683578b02d8792e98bf740ea5ba8eb0424a8aeda03128b61050048d4cc1bf2713843b261a6d9ca04ace41e329a6fca48349f620db526cf0d00294c0c9257eded0c70315949068acb29a3012468cea40125a0b1252bfdcf445a27734d1dad92a7da5256e389d78d5e6ef5295542b561ce2a6c51b431433ea1b1a88cd8624c11a062a8af15461b4eb0562bc0dd3f761096c1c5605c253d80392bc66d093cbb2c5650f60850ad114f688f71178c2a32da31c4c93588f66416f6284173b61d46633d44cc20a0e4a16891605172b11c2ffc470e909174944f67944f8791ee29fa84bff54bef9cabfdc6 else 0xb95e3480ae4e96e11821402c9f81beae2be958e9d52c06b0763c318531354b4de1adc84282ec51c765b1278b9920e3850902ba4e8c582b958828c17e161b478a726e1429caefbb5e220719ed6113f098120239f0237fe6a45e788a00a706ce11c67489bb1d29df8286dd8708a16cc5a4b18a6b58d9014aa84c938a511e66d479f9122924d5c650ba6a47393b0e60b5f18556729659d8372de284388dbb0e1142d98b497374d6b1b2029550992714a23ccda8f3f2245249ab8ca174d48e72761cc1a11f1855672965eb8372de284388919b26194e05775e4614a1051b03cac71e16e6180b10da60c90a787731d61b1589810a5cb43190973d4c64a94ee4e6420a2bbef303260b4d7372431682a27e1253bf302b05a77108481fecb1c874b3193642b62c6292159dc32b8c2cc35394ea80a2a5644814ed346596d85186bc38a4ac1514a543884a44c64a08ea79847ff54b215b855506e9247ff81d453db233b906dd8708a16cc5a4b9ba6b58d9014aa84c938a511e66d479f9122924d5c650ba6a47393b0e60d08f8c2ab394b251c1b96f1421c5d4dc98cfc446085718425c68a1053800f8cc9f81b1d261a354b34b6190a27c26e1016c1c2b9042bd23fd1c60a93230828cc84461331a6312498c151afa2f2936375e06d88b04ba0d58e0063da995e674c3a5f634e24ed19d11719ded0953704007831d062ac5f726a5421fb29844e009346dd8708a16cc5a4b9ba6b58d9014aa84c938a511e66d479f9122924d5c650ba6a47393b0e60b5f18556729659d8372de28438da9dc68289d604982c5219fc9b9e919df808182444e20e2bc5a1d88ec8cb304728e1bc41750b1058935c731b45ccce513f8d3ba60d13008e6870b9a10e0cfc841a1620a27ef1b0a80f51f6674b98d22e8c713a250a13b3b0db9582b1068b6d9cc62658e62e51ecc823dc41376581a2c5b3142b2156181b15bd8a20dc85121d8cac526672a8b3844d9ce25ffaa419f60f213a0dd12830b1dc0cfa8143ee33094e8a1819829fa8d2efb3c36ec38450b662d25cdd35ac6c80a5542649c5288f336a3cfc8914926ae3285d35239c9d87305af8c2ab394b251c1b96f1421c7abfab0a42122964601ee485e04e76f8af0378bce2c81460856e1d52ca521414a3cba5b045715a295b9503a105199088c2e539862493182a35f4536224cffa5d83e00c7b532a0be34e24ed19d6c2f7848cf8e831562fb93528b8cd9fb2984935ad8dbb0e1142d98b496314d6b1b2029550992714a23ccda8f3f2245249ab8ca174d48e72761cc16be30aace52cbd706e5bc50871643aa5802d91e3100f725d1e80c90afe3420b17c814608505863bab92b425a5352b15a0f2e96c6e1a56ea5ca8e9037866c542527004868e42044ee6113642aaff85107e5a0673bf907198f9b1a1c94f0367915e1840d02cda0) else (if i < 3 then 0xa8c70a72a0a300b252c18e11427ef3ac82f62007c5e1fcdbd0fc58062cd59f18caf6415c5d38602c528a1f9ba772504111b623cbee713368c4488715062ac9c31dc56d2c2b46ae33df68ea77092c18415c82a56e7495735618ec5681895d1182144ed22ba30364b06309751b6f80b2b5937f4b718c58ef598721fe878afa5215a1e2b59f278c212470c50975186292b40daa6c907f258308c0b1c24d06a5615c82d4fa661c85052895d3414d019253fe1a9bfa5352b13b1d7464578d202a530ac05ba773b8ce87c0d26f2763a191296889cdc64fb8b395537169289e5c679052833c95f9170b1276996ae10c3056e68c7157518b8d59d3fc2a524630b4c93478986426425649468c3c386ce546c4022bbef33dbf2304d0627560a3ed81c0d2b11006e1c87fd330ef146020a22469498164a6fba9e3651ae4e31c4e1bc05ba7d04c2302c7129c0dc68410afd424ae8278370853803201d8e92c184c8f4b6183e24ed24d6423208018e6354b1682b15c0ab0c4e1dad8a300c30b35b27f1b9352b4dda26be679936417c6b5b2b8434394974aba8d9857a9710f0361cef07e33bde1115a3571a6ff1b28d0af1420612ea301bf97c6841694d4a6474ad90ee10de01c74e9494e2b58e8f165005981639efb4252c17f8bf4b618eea9b242ae1cc812568a1f9c462aa52db1b4538a54261c49ac3c9240851837c11352b0518a330a317c159c31ce2fc1bd73102a0c4887305eb9decca75202d0680ff96d23a5c5d5fcf3ee76a8a94f86453e99d32ba7903b054952993663024f62b24ce6317f4c51a820a543387a1ffe2a522050827163916867d2306109e7b29de9cc82d3a085a7360b4ec6369e510fea12a969bb74f0d0fbde1e6200dc39017ab0cb07f8778a3010510ae41299a524e66fc973cac86e4e31470c506f22ae9c57ea1257413c014e276fc9e3480b5380763a0b4c59ab3e31952082b8ba70deb8a5143f374e83410446d88f05e064cda311221c5418ab270c7715b4a02f259c646625d4685660592037aaa413a74560bd8829dced2bf5631c84ed381f963a74a4a712b40c6058ec518081ef094b02829543c0387f12698b000c9c506e70ce2e1273b22966eae535ad6c2a83573840da53565bd4d82d496b9f408ab0e24fb2b989126b0f6e1c1f10e6e4c2ebd9270c7056878ad67c9e308491c31425d4618a4ad036a9b241fc960c2302c709341a9585720b53e998721414a2574d053406494ff86a6fe94d4ac4ec75d1915e3480a94c2b016e9dcee33a1e06c5785210b18c975328a403e96c757272e8d91eaae62f75217862b43952a0a352bd52cd2f206948e9f9372632b99462b219f9dc6da38738c5d0b704fc08ae532e0b453a212da9151d810381c24b3b0b78f66c2f1ec8db05672e83a7d5f1a10401d91e312daf9c93ba30bc1afee1d4fa5253a4 else 0x8b1df908743de8782ad5dafd4ab11da457789d203a41ed48f74d6a11c6d56836b68eb5abe9479b30c66dcf4d6540ab9cdd4cfdb337864af5c3d19f6a71e94be931de2b29ec2c75baf18703284718a99508553a8efa4d8d01abf6b33f7e46c85c8276be3eea4058261e909c8b8ad623b5c1d59e0d75f50ed587165924b0acb879e185c42be91858d9337519604707d57509d6c8bd1e80c5a6a667251dbf84b1d7afb297c352cb6739a10e3c2e55ad63edc705aad01be3da1f7876f54f2455e6df84a0ce45ba901647c7b2d9ce8f439288ad06eaf03aa3d24ecd9c60b904acf6101547698fa9e931584d304ac08102d31c741a2a8572f7f34204ed78d5dda8f7bca5dc2696cf06c830e2cb31f106e020601adc75ca03329958e29772545c2dcbab385a37865b67d0f3c138438b163ab6ae516ea16623cc30206b537b5b8f43779990373d02846c20bf36a6ea4048cef9cc5f0d3078884e29a4bda689c2cacc61c0c0cca62a26df848bbc4176a725115a0dd5e07547a49d9b38c1720959ec202a8ed31f53d262b09a69a3cd509d60ba85a8efa4d6acf310c205a60cb44216857d219fee2b021d7a84ab2a2b0b5669ac32fc194d4cf1eb55b9620f5904b670cfde53cc435ed5810ebd56b71062d31d180b73d03040da971b8049c2c12dc43ab8d6b43f18d0116977b97794e190c14232490e56653f7b819be8f65c5292519df39ba3d1abe0bbdf0f5cf865d854c7a54f64cd72a22770b270ba1e0a33f065c2b8081997b1413c57e6a13adb083b4dab212d5d4f49d093b2c365d7d452a11104419b9a4dda722e3d2b7d8cb9fd61a6d56e154238ca546c8ebd640546fcb5750e8317c29db55e8782b05c55a87da597b3a3d359038081832a8278add2022f8153b5738dabe3decf7e556990801bb081c2e0bd5e2a4be0c2ca99512cd2f7f47a4d7508f15f9c9243884883d83da40688be6984fe657622c003c6bc3b36ec1f553aceb62a2104d06e6354ae9bcdd1433c948a6b8f2b139062ee041ab1c6c625c21f9e4fa81051a3eb3162b4c6d29c684c6815a1e4920fe34e85016f1020bc0c9ab67a287df8a53f2bf6909c5c1566b5cce9c0c4f31d78a3c8094706e07a3db05a36ec38450b662d258c535ac6c80a5542649c5288f336a3cfc8914926ae32d2135239c9d87305af8c2ab394b2f5c1b96f1421c702a2dba8c3701c8efa45e126169cd4aa4b826bc9c329b1dcd37d2689180787de1366a8169ee01a3c492ef59c469b02144121082e411982a5a60f3620b305050248d15f4961d302b8acd06837ce65cee7591fcbe31769d486fc5081b14602d428d5c6d04c29bfaa6c93df684ab9c60a9051d54639d096d1268343992e2ff00a3042b15a0663a79403edfb920b69487f2209de4b38c24d21586f0a38a1030e17bed08acbb73a91519ea9b2406fe6881f97a)) else (if i < 6 then (if i < 5 then 0x11df91e9c8058b7e20f277118c1885001f8a6aed42e253e90af80d0f5055e781833d15f5172beb0c36bdc9a4e43ca2d11e281bc3fd6146471894fe42452dbac2d60cdbc7252ec87054768e550e69cef29a4cb190a592e53bde36f51d0e95164698d9355aee15fc90ef7a8ccfd58e67b45aba9a0c4df8fa4e4f458bc70d0868422bedf29b5d628f1c09ee971603cdb943e8b007d1bf6231c4df837d20925282016dd5ca56e134c780ff4e50cf6f45803eebc1d88c745bf1628ddf3e7029941b7af1d5b81331e2572aa73287d1600f86b75e01de615dfa3742249631bc7baae51495f60141880932649c098c501a1442c82924afb4e080f3c2e55bd27e0c5dfd4f09a6df2980d16e79c6e86b46e50e4d80f216274c99c1012600049e711a03414a9b47773c6f8b7187f540b0c7181333208433bed337003ecf9c511a034149234766046f8b7187f540b0c2c80533208433bed6ee254c2a854820c565668578f16fc26b0f76431c4ff2b8512db954029d18b7aae7e1b885185f8654d9e74d8a2542d74dea2c3076e64143d2d9757a97b815d98af1baaf5297a3b26606698d214e57b55877e64dc92438b57a88532dabf61044bded32c7499dea174769dff1cfee690adbde0bbf411d560f795588fa4837bca6d8251ccba0b063ac9463db13485dcd48a05c0b517eefc07af319d85f707d31a0dcd36e5f46ed8905203e5788058417b9fe0d920365140af48c0448741bcfd606318f3d25f41fe3d25f902bd301c7ec1f4fb95f5853b9a1af07ee395e200f0f619c09b41d6ac1f3215979610ae00c74c20d234ac9b940c6640aabc52fb42ce751c561470214a052d0626b9932d0f00b057a746e07c2c9630d60145a895dcb6ecf239d394d8817073a914f7c2925953ea6c96b140eef085ee4851dacfcb08ddd0660e19618a2c7b940283128b78e1a32d0f3e93d344407ee313a49428a4502665d1d80b704fc978c56760c51080f04271c02b7701e6dc0fa9709a4940d9430a61ad4897952250d4b8df9f28dca0869072ae4268bd01e37e74cb900aae4468950628dcbd94316a034e080925e2bd798bf01e0a4c280518b98d01bc28a4f1c71c41882101324f3c2fb8bca07571985c22bc47ed140b54dd69d9c8b1d83f7d0c73f10afa4c7651ba1e8ad64182f98c3ffca7b516b6ae9065833105db9c94456fb165993d78077e9a84ab1ceea31ccd237b1fbc2c96b9419f6e10939dd462a1080cbbfd1a865ab9ca7a470aabce5700eb2f65b91cd83593d7951441951772c2e29d8a945641fe0da6a84eb35503a208662c58e857d230ac492204a61d76ec9319ba8daac68f83b2c551da2a6edc41fd3395c9878c2dd52fa3d8dc2b8081854875719daf20cf4a3ccc7ce3a0c5df06d3dfacbc474602cc319b14a0db6791f60ee7a375b53066a9e480770214c052981957e2b else 0xd9b3ba10920d0fe17508f7bcdacb990024e12772d357468d1085ae93a56f00814b5738de97f01eed785c82a61cbcc2e278655d7e6d939e02194418505f32967182ab47d9ef2b67808621faca913edf865331421b05dc1c95af70b9c432ebdce379af5560c5a285b76034caa90b3052a7c3392b9a10e3a31e0e2ff899c865fa01cb4cb4f71230458e90674a0e9ae8b7e82671a6bbc0859653ed3238b12ce9dcaca295d928ac32b9cd1cfec52a201cb47b89180f42ebe12c76651f65cc31c0c415c6367ac681f876aca7e59f529830a041abb6b1e79e6cd1c8301246c420de959439ba8c1574b405dac3192b329836223dd4fb4d634206bb6ae881688b49bc084544dd9ef35dcf849d962d73e0c6f510614d70ca8b42ae70f10fc5d80d8b1164ab8392975e640ccb39d83ee60a9648b9587ca4f1928c555c6d7a03b4b80791ce37b9e77c4137fff261de12ad991828df042952e2fd4896184afbde781a85e30c6eebec783978b85818da8295729cc0f80fe6749684fcf4b6a3649e8c300e19df583928f89dfa2a6bc17025ff160c6b06d6cf940d08445eabc1c42f9912f9918e27f1ab006366db31aaa01cd897900e50dc08df9f28dca0869072ae4268bd01e07c0394907242c0994317a7ac1f94524a084ed84dba2ea542be9dc6a561e48603e7cb2c315244bce277e84e64f773d5395e25bb31e0ff665043aa52b84a93e2727b8131a91c03a753900782eefb2008fd0b9b7f5d7ad6d2ba8e648df94e72bbc332215d2aa6f0d3f11ce50a3644aecca1e90cf2bc4cc176a7496396843623b53a91f2bbf091616542fe22e10bcb9ca91e29ef88e49ec9b01f6ef9a00a28292c6b0ff3d29c8679f22f531f9c072fad42be9dc64d61e48603e7cb2c315244bce27bd09cc9eee7aa72bc4267063c1fecca03754a5a135e813f890ef07726a551750bb2018b9cd3a579e06f66bd75a8845828dd17661c6c3f42f19ca578dbabd5b6d29fc8a4433d155b4c846411703f2186aabdc00405252ef6ab27fda8822d2c72c692ba0a8e274ed613f22dda82e83a28b4b25d0c479d4a5544b349d48f7bcd89f7bd4a44c692a4e7074d423b7274a9874f6337fa3915bb75095653d70943545268c769946a8376a4a0cb84a283fbb520c731463ff4edeb075e67861a71eb16060262d5afc2f38bef23937e00b1b354cc7ed73ca0564b81f2bf8861b380fc8a8d953d82d433a0f00a04e1b3954df5ac681826f945da31f18c1fdbb5f76f4afb8f32d0f1b8a8595c0a97b4965140f81358a60404d0732637f07be57d2d7ce3c71062a5c4aac3e604d01a068ea7976f8493cefa40fb2139230d6283f1b2a5c4a9211760e4028093ce2346c82924636cc08df38630fea8161859026664348677daddc4a8ef41ec1e31831c8e07e29abb50b802caf8d9c3587a1b3882cf4dcdb760c4c0d1) else (if i < 7 then 0x3a2d9b9838486274da815d126dfbeeb152943458bfa8c14525798e311a084049c124613435eed0a603de9a976efb0b0f0310d72e4049930a625776ec3c60e3dd60851b99336a2f4eda4f8ea0c4bd88dd0e71c0685328216408a9707a2549d5ce3210bba1779d7d0968288a23726c1623b6971d7721bec0c776761fd4008ed152911af786ee6354352578e5631154bd6e74d453df27381ad201ca5f3331e8a0d26654e58b2507741d214d14c3be8ec27827c30d63a7ca2ed2ff3370f1c6fe572c2c744be65bb42c01dc08b709a03c34d579b66d586eb6432570215de29613900ab6622a768ac999000e3e6bd98d286f94a2abb24a2556563a9a0d5a6dce161bacb605ac63897cc2c6a143583178f0bce2fb90acfcd9a0dae6acd5b37b914f7c2cac9630a94eb61708ed19ae0a74592a51c93a50efa3b31e8a58b256e42141d25e1f18cecc98e9d654f523df2b0c544318f7c9c637d3e602a4b2b0dc542392bef75eb03194b8e927f12f190d9c522bfd9dfc316ef1c07e4a31c61592523926a9186538dab0c64d4bcdba178c0a7f20cd0b206354adbc0311cce2c486a03333499f990115a771e2f3d95a2392b4fe22b2d6ea43ceac23f8241e2a96520a1720a16a0d557b9b38ccb6e841de0dcecad73e07a4230fe60cd7a1573a95486dfb9a25d6e841c02a89082c49440d06c2303d067cad306aac3f96521ac64cc5153b2d3a5074d742aaa4304240c5a235f1bd1681e8aad06a8bea0879d54dfe0d538fb2d5ce55a5aba558cd7865406dd5da8f74ef6e1093a09d461e22c5c7a162c73b78471173388168bb9dd0848b493ca041ef58d32125aeba6f6b2a0aa24284705c82b8d6bdce299092d66521e437b9e80bb5257ececb2a9846bb6a0849c21ee9429848c1ab182fd769f8f12125ba84c2e7196ae916b81ec32e47aba6629b160ca7776ee3d156e671629c54a963ef305296880492831c8c4f26131945a836419afd5e6ec9650f7303198a22bb7fcd08125f556024b46bb97ed5580aa2424df96ddac2dba1073b7213184bacad37181f65fa1bdb7721bc7dad42ae951694f20abf55fcfb2078b52fa2b3466bc280f99832ca6ecd9dd08490687fb5a855d2a2d29e4157eabf9f640f16a5f45668cd78501f3306594dd9b3ba10920d0ff20c7b90dd8a1ec87c174a14c24a9fc19bd2594cb69c404968d7bcdbc8c364921c305d2db84256cf57c9554e8b596b0b2c20a2a259ccc5078865b5a855d2a2d29e4157eabf9f640f16a5f45668cd78501f3306594dd9b3ba10920d0fea55889510b3052a9739a7e421d05ef230c814ddb0b92b7421279b11575b2d491448cd770ce4a3a507049c26ea59c83dad42ae951694f20abf55fcfb2078b52fa2b3466bc280f99832ca6ecd9dd08490687fb5a855d2a2d29e4157eabf9f640f16a5f45668cd78501f3306594d else 0x7613f23a4896c791ba7738699793b67a095f660e9191a289b21d8cf24bd469ed39b053accc0c6d3b18d5b194bf0a8e85de3a4e3be86c8419a487ff86222108c8c95b279ac2e8e325b5ce7ac488b516e71f758212860351bce9036a4689e08bcc0ced4d4afc681b20bf1cc6518cb43c79ca3fe40589f5f73772e64c33710ea900b051eb02ba2f71e8d0b3b0b0f5b5d1a0d5ce2c4611d843a458338320a567b9e67ae1df341a63f39a2cf3d1dd8dccc874f42d7a8a86eb794d2a3cc6513baa4a1d66fec9da32e87742910c8528a22accc0798b620b3ce1d31c49fbc77dce84a582e90699c23950cfc8cc142be767290b97e86a4e91a1cf76d73194666a57e45ed52c4e11bc21d99c179b378b251c0b802679f9a00afd85dcfb559afa98a7b5f3e96270ba60081649e7beb02a7610eb9a1ecd0fb9a7204cd49d2daefaeec19567043b6fc7b340ec21c30e8895ffbf98ece7dddcfd23012799238f49b8e299d7ec5c772fc4579db66f6f11986a9660bb5d9a1244d49d2786857c0852b6be67000b9efec9479129efa121465782afeecd364d1663b22b8b61b1a5c4e3d2c1d4950b717e82990a6f3e94d8a07666661da0d231c4692f3cef6cc9cb79d271f1815207a8dc0680905aa5c4ac5bcfafaf71f4c032e410838daa215cef8765ade0ca00b98ca308164bdcf66866379c02b8f4868688fe406850f7c928e2bdad8197467610ef57aab80429496e45b359bbea6dab95122eac8eb2bc156e8656cd9127fe23d77127f10121ff0d52e2fc3684ebd13ee15caf4b42eb886918666cf421c2365b83f0132e4a28456ee5e46f83d1c21657bed152e0fe3888d3c4870df3865edb6ed11860e40492128a01612869c3587bb340d0c59f2a1049e76ae7b35274861ed6e29cfdf00bd11031c65d269779cde14f3495ad2e7288ab2f3d15f5269ab72eb2ec871646aa31ef7ab666e17414c6535ea229ef79ba12141052115291311ec9d20806f172f55f8faffb39b76ee8d423ac94695de1ed5f603fa58c636acdda082fb8b617dc9d73327b4a48840684b276be0d92dce1ade7815482cddcceb03194f009b88a940bc0f4b7721a57792bbce963185c815d1207a1ac07dd6820bdc2c0da36e2e755f658152dcfe7ce7b98aefc75cd71d6acdb0758aca392cac93bb1f225fe125608c6b3f7826e5a0caef3e1d96b0a6d4f6a8112a8dfa58c6ba6431494f2fbd20af90d75a59b810a50317ae07a571e92d88a9a2e976a8459151087ceb682aeb10c4a838090530ed3312452c3378bf75fb61d7bfa97a38b268876e3128d417f2186afeccd17f819f8d6ff7604295f676e810a366d02a14ccccaef399d19b8957868d05ebc57d17a341882152e4fccb80f6ee9146285136a0ad2780936e07e12a9716e14cf5bef2160ac9e86b06580863880f013b60c97c3b2c593b403de7b41f7))) else (if i < 12 then (if i < 10 then (if i < 9 then 0x91918a21d71410bc6e9ec6ef70309ef91e907fdc4b2fadb2841d423a584ce99acaef24c4bf4c38df3c7cc51e23ecfc6c53f93ea304c60ad3dc89279d96738215f8418c1ca22052a6ac61fa9b24cfe24960a37552fa9775a884fb89293dfe428c1e012ff9a83e6dd5e6a4f8224d8a7b256d0c0c74063c146e616bcae7138207574a67e1c5c3617dcb95a73528cd65d3c9547be31e56b7781b5b495cd0a3053f9098c145c73585f8e1b2674e4a74295212b0402b95b3c3b81d53d8f92d946ba7e76bfa7d89259533586792ae9bccbb467e246dd379bea3114fe4c49da2704f3aa0a9748ff9b983ade1ceb75798ca9654d72e2e08ed27c135ab04bb3fe8897217a57362674b8c69c50424ba05c6730eaa0a00e47a41cbc57145df788303588977382141051abff3438cf784adc41954aeeaf1410bf1d0b341b1d0103097adddfac548c155b4f239c5f0149c577de2baf03097a639331926a917d853e0a4119533a7fc49e2ce5620e93c829c474c2b1c64429fc9f3f185a2e6d4d6349f84d73af40b801a1cae1a5f0257c0d0b62a211614f78aefbc5cce83e7e1e0e7135b88fa8c149fc7d3b9f90a3608052305620e96b9323db526e2a2127b3b2ce82ac22e6663dde13419dec993b05483afe1baf0322e607838684d068cf5b418c24935de9494bb2352b897cff4c7266324d522fb0a7c148232a674ff893c59cac41d27905388e985638c8853f93e7f424281d67bc8dfc26e503743731268818393e8c182a34d8dd7a1e77583a5b159d3b97df9a1462daa04d7fb2d8a0859ce42eef3cc651668358d015a2397cd0a346912f9fca488184b67e3a0e27a1214fa8c62bbef17414c85453d921799908ce61f8e059463a50364cc24d2e2058c5632b04005ac23b2645fe49b25a790c61689a1d3324d523226158e0f0060093352748a3ed423b341c7dcd35801728476a8e9b3c70cb905d8585f62cdcd4f2a20c23425f40b1ee7e118e4179f45cdc5482515f58875490b9238afc8ef4010a553902a0f463af30b2114bdb7b38288562c0c64ca08df38e29df6eddb162341fd7314e30e5bdd14620f4098bb5879f441c3ebdc76271733ca8416d5fc473be2196ba725791bf47616015dad8f72e3dc42958f49444d602cf1c2fba9c74e850f5c94838cfc4f56c8f19fc9e3420b54b0a3cdbf9f5b5d5fe6a50bae227cb341bf0d9290e5f022e63bbba74c4ced9c38c8ef47c432d1d761a414e7749d68b7d9a085e2ced8325f8002058e10ae719687a88ed6c5d35f26b0051dce08558d9aade7f00198ecdcff74d03a7b85e6c799533ebebe477a0ec3ac48c43aa5446c4f616211c69865c8250b89e6ce1c4e7f88e70171b508f72684a3c87e82ac571d47423e13aecb20702e217e7f23b22629ef86553fc4736227fb8c1664172b73291ef7aad8f457774377bcddc5ca2cf4 else 0x487e9d4ac3c377dca9ec5f61365a3918c5ea3d187f883ef9634f3672fac3fdbb95d27ed83ac4f4e96da8842cd23fd7ae3d2db2caadfd78273b86e4abf9b216cfe0c6612bb55c4faf57ae6653c9137b2b162cfe000b949fcc8245ef868d0c5b17a76d7d8298ae8ec5b9cee65daaff6530a89988a9da32119050fcaab8289920eb2260ffd7aff02409019bb112e64d11a07c1e82916e14c3381152e2f4da93d0d693c10c7112a02629a9587a571c3d21ec028dd3322f461fe20355cf720a55dd6fbea0c717480a4069230122340f92512bf5413cc948dd07a084bc8670b22f76c526505493b7e4ebf9f43d8a82a58e26c872e105d6547cf183f7d0ca1a8ef84a094151dac18ebd469ef9c1cebc32519a30d79a8ad66c156d1d6321190d70cec0c6897be9acd261f8e1380a9bc5922e505acd5802da550ca9b65c74510b161c66c2f84c0c1c760a9560602933aad0b27dc9851b3be2c20c6553fae112681f6d44223b8a2651b9cbbb36429656489c027a8978c7e41cb90e6cd0627d45211622933b5ed3ff1118a8e69e3b2cfa9d24e0a74b4348d6c3a285f851a47be969ee65edd65abcb27725f0ee6741410d7843226565e8c7be8e77a2d410bc930223485ec16ee04ce392f54a515f2c2501aa464dcb731e9e4f6c75320a568dcea42dea8b9b3c73d7e6fb8bd85858152682cdcbea81358053d82d4be87bb8bb9737f4b18df74b1184685a0cf38a638c0a8816380dd85d16fc7369d7cdf1d76a4a73413daa045caffb38733382f94fa72c60c15d0558e9831b01e48c149d3929dad04285e65e0eba75c64ce7ffc6cce14a81d179bc0a88754b46a793b0eb3f13dbb945cd9c386b01d303d7f6160594db9ccf203aecb4e7a123edb14609d40572bf0d52d97755ea27a748090f3be1cb85e25f07e9b18c1cfdfba1db2295e79b58411d6287e55289114ea0e022167b67e97d292766c7cf3c08c716f67266639d69db2a20c23f290f305da9fba25079e9f8865943407350b86a4bea27af1f2aa550d1a2745bfc3498d36c89127744bdf8865838cbd5fefbf11528a2c73923eef1c90dac0b79010ba7c52a93ec06e02c0c4945bdd3026e160a79e7b49f09fb4340faff0e263de4eb130af2c1c0b6c3a577b61cd4340733521efe118eda62d65b1040b25b9c2a837673a8f4e0ab8ca6ac509e24397bfcd0e648c339110f7244f3c2db9d19853c577e1a41e4ecedf0d4af3cfe1d9650714fa467b83d5ea53af0e2e3858192cd797a7a7284f4fced9d0326cd48a54961c54f0e9dc5fa49c46fbf3f2764078e306e95f1731f3e890bb2d78f94c287185aa781c6837140b582a4175c428dac501be890327c686c535e6254cdc07b00a374cc8bd187f54071725b10149c53ce654b5e031d07a70634493a5031b985b583a5e0a6153150f2b03183b5e85bbc0ccb7a61c60630) else (if i < 11 then 0x95355c06244cdf04850ebe1f58c1472f1854aa27c4feca617c2429561808dc0fa9b24d1e99f8f5c9b051aeab143b59f8cd5d0627df2b771328a20849aa42ee2a56de13622074b92e62505b908d65978ed70e5d16d3369941ee4a31d1728bd99c012e6f80d828c15c0b13be6cb29166554e753f0d52396f0cc69b8193edd58a81bafc4bb29c62519d040857d61c6396a61da7211305b3476803180dc44c411decf46e0a2649eed13dcc808542cf077628c3f1a7d843e2c76857288213628c3cbfc10a903459897c62518e588b6526f81e1af59cfac422941ca23bded8c12fd2dd813792ae72389505a0b4db82b14a96c22832c18e274cdbde385b52287d008e51056e4c2d8a70222851989d11e0d02f70de8c422bdb4a7521db186fbc24fcdb78811b26e5b90b46e0e6f9fe7a6d1ca2f6c90c2ff002c25e84958290e9fcdc8072c336ec1b2fe8494c24da6642bdc9391b14f7cd97424cacf76103245ca37b8555c6a2624f39f7f2ca9976acc6185f9dead9a102c5f531e0bd1e9a9c0ce2146bc70d168638d7e85271b0ff3d0b1a634cf866b006ad0321152e4f426a370431c76188d32649fea30514325203c1ed8b0b20240f8092920f4858132862f4f583f28a494109db09aa8fce4b901fd3b98b997d786a9e1b3004d9a9659d1095273c691adde8202c02f270058f436cc1d2f3ef04b1f9020252bcf4d74913bea18dcbe65e8eb63c95b98c14410995d30ef82faed818cbe5219a9c0c75dc59b7a0cc886831fe8e2ded89851762ba41beaebc02e55ba3d35681b36ec8c058d30bc9b7a0c7dba195b0f66059d11e1a095d66c151740b0510c1668e2c10ac5a798ecc8677fc584f3188a882b87f517a94b484d1ebc13ba4ebec29388a0855b194919f4906e0defa2974f0f217cc00ef20a732dd144274b2661498183b261464fa24ebebc82944731ac199783bb1e162451c564243b2c394126aa4ca910eacaf053dd6bf1f7f34d164aa15572beb0c32e14faa22620a29ef9b2e849959eec20648b946f70aab8d44c49e73efe59532ed598c30bf3bd5b3c30d2bbdd2e1606be68ecd60c6bc70d3e5bebebd7f88163b20a3db8aa783d735381b3aa1137172b646020160a11f02dc92913733a7b95bd4f0d17eed5de22a564109a9055d9ab40c6b06304df28bb47afcf9c8c6fc71a9040b1d90492fe0c1423e2faec8c059d55b84d7dab16067de96c069c1327094cca3b16e38c048213d61240cfd04ce57429130dd1e048c58a4394233f20b2609754fc089da73a30ca0de6cf3605485298adf216c4153024a00221fbbbe4ec3172beb287763a603f8b26d59ad8524604c0fcb473eaa3d7afe5e7127b5b333ba62b8c32262dd3ca79226aec3ddf52c680428c93f07d3061a3de9940cfee426ee953d9f560fe4de61819acd5ad8578964fe399533081214149d61a1 else 0xce42bff0d3e53718ad2ae40f831947a70dac2769c68f4fb4edd8c3dcf2d880c4f4d4b35cca9faf71eae9ca18fa1a1458d86fdca317608bfb0e0a76c80f01f484fc9c380b134ae638d9edd610b4e031b7cebf708c6d06ff800a16c7b8f4ec463b62ac8066639d6978ea20c2b3a2243cc176a7ee8941e7a7e219650d109d42e163400f5a6e2f629844941ab9dd2c633ed320a744d53c331946ceb980a947566eed1cbcb0d23d77e0585db09f3c7e223e3f1d176bef3d7b23014e916fad61ed479863526e5d0f2476a6a5660bb4bfedc9d656f09f3c753437675a739c806cb511029560d36e3727e4c2da393be46db932ce425608ad502bffd092985364be84db4bb674d8c6fc800e68c4708a1cc0548d4a1307a83dbbeed50b9a74bed8f7bea5e4edcd881b3654251231b983bca2a5493530ed16c1d65094b8df6ccfc16d442f7a47de0c7d0aee15a2af65f75b41418198560c1e7659d0408547dc742c0ac5728befdbcc3d057c6effa09082dd691f25e28210fba4f82620047d89f9189dfa1c2c14f3cf699e13f77481f5fe44cc7e42c3dac4c2b7583b3dacac136c1e13a86884e6784637326ab844d83e7b016d7e43f303ad13ab2ca305300518ac83799ea9efb1a169aab15a2e26b84b8de7c07b2fb1460f2c5fdab0c0544f91d0bdf03247fc987bb9dd8028cde7b1e16a1207607f4ca3d95ff885d0e61aa4eb8e4bd8232bc40ba6d6089ebc8da0dd31a16fe84958290e9fcdc8072c336ec1b2fe8494c24da6642bdc9391ad6def091aeaccf52aae526432b0ef31aa4751ce0b4739918e60e9ac04d060f02e12460dd52cfb61488f3202c4e142702c4e965ec3ce0bcbc9478b26782c8019f618d947a284359c75e6254cd86907a04cbc88f0a7bb45e8098e26144083f222164a09db7dfb4ca2ed196e085e49eb07e37c5b8bb21602613f95082fc406ad03067cda83c4df0d24630505c4d343f80030c0aa85cfc18286cb8fc7a49d276edc9d63ce58d3414c667490ed0a1e213b4c754d8672230b6bc9d785bdfee1b6b4874bb0c4e76c0b00be2ea5930d0114725864840525dd50f33cdd2442dc8854620e548cf1a8623be87b80164617736493fde6a7948515b63252c7928179952cc82aa2f84e54a52ef69bb342c2923222215d2b9bb46b5963432e41475db064a2cfe239d09fd19d771e678733a147da8466d5f242f9801de414e65ba2884e964cc293030764c28c9f449d7d7905288e6358352e5142cced30b2e46f97b013b4c1c821187b45f7921371728b68dd8a79e28101e7ac89ec12c58ebc01bc42049f18cd732a582975341862e01a1f92ce37cb1268343f0a7de52b9be56b05fbbed05092ae43912ea302d8a79e76231caecb1a04df86526ce886a58a15e3ecc00d6ea0a300f75341a29e7995f5898402c0c14d62a81292eb00f497b282e64858)) else (if i < 14 then (if i < 13 then 0xc128417fad1dfdef11fa3651288527a7241280753e4643b93593e396eab0127a45d27a2509ac05278691ba7a7ea30549f257a1ff5a9facf0656f5d22a7c8c87726b27c12f13ee82621a44284de321853986d53e36c3b9c393e094149c943ad0ee0089d67ee46d4fb01233f409a07f92758089da866fe4b38b95c2f820c30727276b93739b64fe09682250720d504241a3f48e296749c2f820c326e04d61839fa0490106db26466e793593e3941a8ff066214258e504bc4fba09a803b2659dcca3ce354c2a4f07e30c098394e666e1c0a74de613514fa411a03c09eed1c6d16c98dbb9e70e4f8e57ee375a2b88464130171088c205237580ef597759e0ca2f21355e91749e1047e8e502759dc866ce3540180104eb440bd17686b3c118994c200d44c77a2e2650dd0702f6f7e051c51700600530ad102f67c9aa61b3e86cda00060041394d5a205d44b650462641380300600413cbb02e534e7ad10070cff481729a18710ed722ad8d4f9bfa2eab0715e08c51827006c1daf831016a7ce6acf93a28d25ef34c6e053a0d713259c5cab26f2401a6168628ca6c777938a59d200568628cb5a61e37c208a0616bc959cc60e2bc02831a0e07c0180104eb441194d59e00d4482304e28c6bb814e88a7d2031de76f68380503f45f92b399c209d0e1a8943775c0180104e5365d82351208d7ba1b062a7567fe900a28c659cd0060d42882502e6dce680306a3247182308212d66ef1133754129dfb9ed8c0ba19a2f0f9c196734018351923940b80f3be6d059f3c31f9c4c8310068212ba51dcd294d2626fe8256e05407c0a387e632ce68032623241282304600e188cb063c64d293136e7a40f80f0a238c02b81500734018350a20940b89929a73424b814d0900306a2756689929a734018358eeb1c078c55e6247fa2c886f146534e68032631dd63af300a0c44e98381fb2745186f06a104db9cd0060d42889d0462743b8057029a1230700d4658fd93a3941ade011a04614b58030464c412d4f32e03c5ed1706266428805ddb45c71dbd4108e07280f922cfd032d79967843818bf559608cdb9cd0060d4288e50461045199700a3f41a80d7e603dc0a8093ea44efac79820a4068c901e2665cdf901ab240ba9102e52c988d397ff028e3299ed38ff14dfd0704249ed01a06ce08b500a71c248c527e70042e5391410900a332e0d7f2a871a601499b815b92741a8cb3bb454f680d0367045a80538e12464e8f1abf94e0084ca262b1cf69b8c13ab20caf9a2d434cb95778affc344276818c63ec8658afb77ca714f2ba85c41e03434f7d17e496baab905391fd3de386b582a407c77e854866d639b8b423c62ed0868d5463be5aff85603ddf690aedde4b38de9f0089536ab16bab8bd60c9211d60a942bff0d5f34866657d8052c9da48b9547780552b0f76431de7 else 0x46410d30fb84fe81210434c31b49f2046a9479a3340288dad82ff5e105e834d422053a8a87910e12533863033454eee9336e10d8281b256d8cdfd1f9d65e63430130ac04e490b243b77e283593a0cc6584ba2ac0e4d801046fa40186117620412a2111e29d0ea53086786cc8d5c1bff09add1246a5d488a7b17005a5c57b17e209d06ae0dff8394b3921c10f06ffc50e94cb3941d0d77ba530d234c22989d0e1dd68f902387e6da4f0a5304a997c41140c4b471c71326dece3e87b1634ccd98911e52d6a83b7f659e10e38634c34825da252c1ee931a6b55b2a531aa4b545a871ca14d10e9d453e905383bd271d6cd92d296994729e16f7c7c6ab905b8d97a055825a59dcca8f2e411a0cda77ba31f9c96ef78e08d6f6396cd88509fa4ce9eeb6c3c66153d73a416a654cfd028e319a3a8b3ce4ed7089c82e8144a7231f9c4ce06469f4125c6cf45581258183c9dd1a62bc0ca911ce0b608ae7607464eeb0559e73d64bf750e46528d9980aa212e59969765c8d83b59205eb393ac355bb86959f76416c89670835402f1f3b7fcd7bbf7b8024328e00a10e7f72e78e9e14a22141d817f844d18cd0124559e14a20ee7688111e8cc1d8c77ee2044799b07a31c34b6d3c208d28d9705a13dbb86905ad940ba8b10266d0e91bace4eb3f70760f4a181134e1ac3cd190b60fc02cb707a4beee8850f3c74f421c0ecd388111e66c1e8c70d29978f805e3a354f081122ffc68c83b282db41683d0220441d855046a35a4d190462bd288097e6a1c078bd332b4c078993be3246582501232566de321aedb670faffe1f38106ec831592086e009c86807837be3ff610901c1b9ea2c64e25e48700448723bbb23965cf42268fce0c43e9d30221f676c015a6fcc2d80f0322f45282b60a71d442054969d19a0144c26747e0929845b45182b26e65c1a85b34e1e7f79371ca77c3e8c93beb1c988a334a16c98b05fdea2102a41f45193f06a1bc15832c1fa3942a85b0fa1e4208fd04ac16e009c866ceffcc38a351674424b051fa86403a29002497cc04f65499899436497cc53a03dc0a084800386dfda587cc04ff40bd095ef5a4be65674329482e0fd6714e0831016497cc1e7a3d4d93ff8146a50350da59c5cad1ea6c368f306a2d5f486d3020d5308f338a7041880b24be65bb42c28ce2827f81470004799872d6550ca778e13f062c1c93961f314da21147f028d4a48acec74a1bdea03da2a8948a28d4e86d22a4e4ee8236079259fe4314049606de61acee98793ae05342473c1a80313ad1c1186d39e0d5c0a6848c1c02313ac0c7996713294126819482dce361dd318cbbae35c07ef37ea00da281b404960a046d1ff4f0822819042381e6d16eb8050dbc6eb3990c7768ab470723654d807dbafcc1a853d1e01c3480753e4643b93593e38c03925f308c87726b27) else (if i < 15 then 0x7a4518a37418d4f0de03d228c57daaf4dc60317a67a51d9871fef0113b4e44519c010b95304e6fff26e735c8a9b520814606b68046810a3ffe61c3bb49b4026859faa2528a73d0c84d6049606604a14601bf059fa0f49eb3a6a1d40a8009a1f73015297e4a4dc61c01121c42ff59eb3c2e5129f8a1f5c425cddbfde01805257d46ec095e634751679c30ab2cdfd037527b012438a7920290ee4646bc0500ec0d1481d0efff46bcbfd2ed1ce9a630fa4a4408e167341fcc686fbeed91b0fa8212ba40a714f245ae64c128093133ccc98e30126256bad504a4b4e88351fe0ceb984b2a3f380d47f83310a12c7280fe87dd00cc4684b1c60d47f833ae612c7280fb16a6d4b80906a3fc1988509639706f7cb16f37071fd460ae87dd13cf7698958b030e32623fc198850963956bffd502a0c60ee6241296b01ef4cbc88d33238c988ff0662142582507bb2265127cc682f2a5cc9bd3312e2119047004487388446114b3a20ef439897a63f412ad70960d41988d463f39d0fba16bad51ca4b4e88351fe0cc4284b1ca89d318d7112b4e0381d0efff46bcbfd2ed1ce9a6305aa2102a5bddb68115969a7f01143c08540a8318a2de904a71ffc8997409d329c7160be209d164ff97fed9ce9f042587934993bd2267fdff91ca8ec2483128606471af34d23f58282104a8c7e7051cb760bb0b0f03d2537e63a9c01241d15db596be8b003451a8d26e5ac0bbfd44e13fe051a95f142c86300208c438030c287c20ddd2cef0b7882402642585f12b790ca4d246db181743a03545929dba0ef14f4e06300205c438030c287d48ff45916ee08492e25e48d0d0e899076ff4ed83f4860156980d0b218c0082310e00c30a1f0be18c0081710e00c308110be15400ced15600c30ad30be18c0082310e00c30a1f0b2154c080515607ced8110be18c0082310e00c308110be05d34803fcb0c6cabff0b2154c080515607ced8110be18c0082310e00c30ad3f844d1f028e08b81127a05f85e008702f86300208c438030c287c8dfc5bb7656d009d422538979203b05228c20879283b4425f0be1c146a349b84ffdfc2f8716b9ad16a60496e29e9c2d617c2a8010462ac0186102217c11a69007f96189c57fe35d638c94c7016c1f8e697c2b59c9d6fe70a59d22884b887db4cb980639cf0acd893ff0d2b695a61f4e00920e256384cd8c708b0a7d207d05631d19b3b08a23d66a205628cd00a269105a224ef933aceae539180ab55c0a7434ba4c69d9bd261f4a582b18e8cd9d84511eb4e8cff151701c6ab656d28115c42967494665ce2b9946e3097869d821dce9a0847021c5382bb2e18c8b90b14e1f7faa9186ad2421b130b7d049482c1bff3fae15123f409082b37837fe4114cf01c21aa580ffdd73c014ce73fc811aa421ce9843e33bdc3ea678033b5fa94b2ce487288 else 0x987266895a285f51e074009872668943685ffdba5d128d57fa10499bfb4d002f8f300261c99a2544217ff68f344afddfe841266feda685f24be62655208146f10450301df83802e8627855c425c3bbfdf44f043a7c8589d67385820d99bbba27004114220539819e0103ad45548b13692ea7a09298400de02276984241c2f00438e053425014a5cff07645c44bf9df2a37e051a953fc21de01341c864e8ef9326867fda8381944c359ff50fcc2f6f244ad916f61acc081353b94ff9a19bcb075953b750fcc53bf028d4a50289d20773ff85e00872198117b631d0d82d076db421d198676804ea12c94caa34e8cff6fb0d6a1ff411708669c27b6bda71e6769412f78cd00f42d9290763663ade432b90a9708669c2da8d076df43c84334edad4684fe421e5bec79a87fd045c219a709edac02981433927be349610900596fad8cdfd045c21e63430130a1dc8c8d780a01d81a2903a0254ba8144e9069112a21138413c27a27696225a6a9f0764a4408e1673a5ef00a2044b884587441d94b09e89da588969aa7c1d9291023859c8d91c228440a337ee0ed248d97ee23c4083b09e89da588969aa7d13b4d69613d4f8897208d06112a7d1384fbc028829646c4099b4e7789d643a1a41df422074913b4d53e227a050404f380224388d833b2fd02823f88d5077a5c618df2523859c84507a204709d1b26b541df40a0844e87545dc0113acfdc8da9f09ea1e3a921380284398085f39236565b814e9305c89c010b94267478351ba0c6a786f01e914629dffa04d1a3c939377f21f7e8104243fdc88314c0a313f0564a41ae1b8c3d26970987d01e87ec893f0de03f0987d98273451b91ffe717fdc03e87c67a02b87a6105c0a274851fff34a4c566acb96ef4c15c9b0de0446e831a9e1bc))))
def rankMode12 (i _mode : Nat) : Nat × Nat := let v := packedAt rankHeader12 (i*23) 23; (v &&& 63,v >>> 6)
def rankHeader13 (i : Nat) : Nat := 0x17f8a1b8b95d9aa86b66474dba5a14d14d18ae4c95717e2b84bd5bfb27de5946eb1986e595b50c658b956bad2056055a654d0fef946c634276a88d452036f8e0004a
def rankPayload13 (i : Nat) : Nat := (if i < 1 then 0x876882d012294f4a977ce9814636e9a023b7da4a65c9838d825140c80901b53d279eb27a03d2d832c5f70942482909a0acc989d67a6dc1c9eb16e2ec6ebef28a494618c505203f418bd2c60c44e99907e66e0029291c2b9403aa517e0ac408453aa2146d0a2064b6dcf97a8c463a5b32e3a57bb6d27202cf298b1232ec1681b22b85d4c8ab0227146d9f103a29c0882b30b26c0c81f2da42c5f8a528a3752789d243b0b0f032c337058e7980f063a0c948e15ca01d528bf056204229d510a368510325b6e7cbd46231d2d9971d2bddb6939016794c58919760b40d915c2ea645581138a36cf881d14ece5148af17e560ca7521440c8c5d2ed7c5082bc4265ccd8e95ee15447b0705a2744080b36e0cb00896d7bc70e492103ea44338bf07242c14e8516a1440296d30290c5e93d07e65c749259f2b16066771c57f9db7ca0c40dfd460a42e705f48bb3ce8ecc780d01e2fceca59b0e29c74e9d2522be8696d38b802c14204be8193f215a1e143b87038452851356bf438a38628559ad3e3a7023de2712271a20794773207a3db4920b55281bf7e40690a8fae60dd7b8e18f788a942fe1db81142ce4169a90dd8114085189ac3d5cd728c58bedb4939ad7b2cf455ae727ec1daf8e903a16c38aa505629d608370a236d25a9b18e23df39c532e96c52c5d82202e5e99b453f3403a130e62049f02da70c2ae1148a1bc48ba11ce8c73883409559c93b156a0e3dc3b6db8118e12322c38a4b1ce4557eedf6b67649f603573a6e8e126b0f2493f20dc0ca29c0eb9653a90f8c1114aea4e1c0401c39a9935ae042e83427bf58206c0e8a72de0d5d2702db4d6891af2114fc873582386daaa587616d249d9ae68a4a3b1b06ae77bb01606353a04639c342737440ba197a23f4e51198db023efc748376722857ba9b81f046368557c60fe1eda4b1ce71645ae724fb870d6c08518cd8342241f9a96f38837548f893b85a29c038ab9778118e03a297409f15ca4e57393e18441bcbb3ca16e08a1338d04e18e0aa71700d8e7a1a5f61ddb58da1ce4bb210dd95e452aa503ad7c1ab9db7f03cbdd3631a2f8194b2a64d6ba1752cf4c58e10e224447c7b1b68cf8a8af05792819c88105aa3cd4ac15076971080b53614e24b9f197a7674e8e73ca0dd5215698d2168c706801aba416e2e8551c3b87006493c8b270c70375ca6b4c58452735cc52b218221c5f3da56be02c39c0f1020757382d463376daa9b8da5bce2e3937421776fa5b532a94cd83f8387885ecb3922a2bcfca8f06ae761106e2bc0581808528d5c0f14ace608aa5af29649f61f138aa0d9d82d976174e1c0465e3d8e94922ac389a9c454ab0e0428c406168e710284cfc97d1b7efd73855732f8fe6e4fa43bd363180cfbb5cb81c39afd0371b429c3e77432f4c589138b802c1517ce3428f2df4349da55 else 0x9e623541c0d94ce48bd00e6145b8512426d5f783917619f769e71b248ce090b0b2e040580f07e30c5aedd0267249081f00e19ca48392160a7428b50a6014a19814862f49e83f28251492cf9273a0cf2aff3b6f942681b22a85d4cbe917679d1d98f1b203c8583f8e28a4eded7ae650c2d8a718651442e4b70437463ca3175271c1e8df7924862bb81dd604c5d81d00eea44681f3922f40398516e484da93d46efbc1c8bb0cfbb7438d9246ae4858e30d2e040783f3370fb4618b5dba04c03a2907a8c54c9e546649c91fe82da29df3b2103a9171815206b82841ba84315afc57036e043788f016114e193f15e4a489f0816c74cf93b61ac948df1d22852184524630c039e7b1e664c299b80a629c5b8e12f619c349b503ae045d83d462134719c924207d488672920e485829d0a2d429805286605218bd27a0fca0e4a024b3e49c80b3cabfcedbe506206c8aa17532fa45d9e747663c6c8953924840f9630ce5241c90b053a145a85300a50cc0a4317a4f41f94128a4967c9390167957f9db7ca0c42c91542ea65f48bb3ce8ecc78d912a4a470ae500ea945f82b102114ea8851b4288192db73e5ea3118e96ccb8e95eedb49c80b3ca62c48cbb05a06c8ae175322ac089c51b67c40e8a72523857280754a2fc1588108a754428da1440c96db9f2f5188c74b665c74af76da4e4059e53162465d82d0364570ba99156044e28db3e207453b0728a1664d80511a7890e1bef200d939250ce29e843885c252465248a8c307202e4b8af6da4)
def rankMode13 (i _mode : Nat) : Nat × Nat := let v := packedAt rankHeader13 (i*21) 21; (v &&& 127,v >>> 7)
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
  | 9 => 0
  | 10 => 77
  | 11 => 715
  | 12 => 656
  | 13 => 25
  | 14 => 0
  | _ => 0

def supportMask (k i : Nat) : Nat :=
 let b := match k with
  | 10 => 0xc4404402203ce1df1bd01d07f07f0ff06501d0ff13d17407d02f07517e10d01d22d00f01d07e07e27e27f0b906705d10717718b06f18f0cb36408f08c0fb0001821d42fc17e07e07e27e27f21626507507603c0e603611a2ce27624603c2f62ce0a62e22e622622a03b3d10fa0f41f70fe000
  | 11 => 0x2101800c0060424404080061802040061e31fb14c03d0ad1911ec1ec0561b10a70f62bd1d70a60b12f702b1e601e1ff2290170990751e70671d205d05d07507501d07d05d03d06d01d1ce1be4ff03d1bf10f0bf10d03d03d07f05d07d01f0a61ff66e6ff1ef07d09705511d1ff1bd05504d03d05f04b0990bf0ae0ae09f14e1630e33ee1ed06e4590b915f0b30d309f0bd0ae0ee35f01d1a301701d29d35f0b129737f60f00000010e10f19f02b27f21d00010b36f19f61357b4cc11d56d0ae0ae0e66fd1630ec07f09f1e70390ed0bd1df29f09e4df03951452b05b0550db4b34b20e71fc1ff5de02d7b91bf06c2d53ec0de0df45f1e502d43f1981310b801f15918e36640d0ec41c16f1671ac03912c1b34481e70b74ff1ad1ac15b13917315919b09d4dc01d0bd3ee1f91bd0fd4a913918c1191a72df0ec15d3790d46d765956c0fc05f1661ff09d1ec0b90fd0ff0b90bd0bd07f29207e6665dc1520a759f2af2de04726f3cf1ba1bb2cf3f728f1563ff1bf0c518d04703e14308d53d13b29f5d32af08f1b30b72fe30f15312f5ef1a30a72471bf35b71f1bf47712e1d331d0775b72fe2de14c0cf08f3c54c718d08f10e18f7871d31b321f1b31ab18b31f1891c740700f3df3cf2ef1df1161d619f1df19f1d31d610e2671d61df10c1d61c710c10c15f10c51614e0cf1bb1cf24e52705f4073d747c5fe15215f31c24e10f3ce2294762fe25c3df7ad0b80b90bc07c2ec19e4981be6560b95de6540770bd01d1b90bd0bd0fd2dc06666648e1ee07d07d0bd0bd0673ae10722460e29f1ac14e0e50ec1ac1a809c0ec5dc1734471ef4ad58f2e60ec6e566c1e20f32f62744d422a05329747725f0b34620f66530530f767a0730d60560c744a07c0fc0ef0781b90ee05f0be03f07d09517f07d07f1ef0ed1ce0750391ac1bf10e05d3be3423d654e1a632f20e2951fd2f85d60b87ce5ec0b867c5661ff2fc67c1ff23c37c64e0ad20c02f0fe0ff0bf25e25e50725c25e0cd46a3de35c27c0a715c09e0bc75e27c12d4dd45a0f10960360f60360d60dc0a70d32db05656b0a747646812809c0cc0b80fc0b80ac0bd0e408e4ff05625e35f3af4cf0bc19310b1fb0b33de0336430d61d708709c0dc1bd1760f003c0de1bb05609c14e0b60dc05c04e1a739e46704e4520dd1dc19f1ba03311f25b3130bb2cf1ab09b4833873cc1ba21e0d658b0bc1960d43bc15a15221e07c58f14c0d07ce3ed60759919b57615b19806a0724943df1fe24e30f4fa1db04e0db0be04e38736f1c71e73cf07b1630ff2c71853ef3851ef3a718734606f38734732506f2873ef1872a73ef3a93693a938b34b2c31c91bd1b91ff3db0f93f73ff3ff1ff1ff17f17d13d1ff2bf2ce2ff0002ff27d23f2f51ff2df0bb2ff27d23f27f2ff2ff23f2ff2bf0ff1bf1bf1f93df0ff1db1fb07d1bf1df1ff0ea3ff1f61ef0ff2ff27427f0ff00000039e0002ff1e707f3ef3e70ff06b1e717d07f1ff0001ff1ff0ff
  | 12 => 0x1ee1ee1bf1ee1bf1271b91a91ad1fd17d1ee1b81ef1bd0b51bd1b91b901f1391391b91ec1b91ee09d01701701d01701709509701701701f0b50970bd0b701f0b711f0be0bc1bf0b70390b90a61a60bc1390bc0bc1e61e60bf1ec1e61bf09f1b91390951ee16e0170b510e10e10e13913913913901e13910e12e13914e13913913f01d12e13910e13903716e0b918e1a61a61ae1e81ac1a811f1bf17d1bd1b717d1a40b512717d17d17d17d17d17d1ae17d17d1b917d0b71b90b914e17d1ae0be0a51ac1390950950bd0be01d0950b51a418e1f901d1bd03d03d17813901d1bd12d1791381b901713917d1bd1ac01e09f13c1bc16e12e12e09f19c01d1ae09c01f1ac1be1381191a71291ad12e1ad1a81ec1bd1a41a519c1391790950951b91a40b51b91391390951ac0b10b11311a813d1b81bf1a40ae1fc1b113913913d0b91b90b81390b91391ae1ec14e0a609c10e01e0a60be09e15e0a61ee0be0ac09c0ac12e1fe12c17814e13e12c12e12e11f09c1ce1ce1bf1ce0b10b511e1ce1bd1ce0b71ff0b709c1b11ce1391ae1b10a61381ce09d1fd1ae16c1ac0ac12c16c18c16c1ac16c16c1a71ac0a61a60a61ac1a410e1ac16c1ac0a612c1a616c1a41a41bc1bc1a91ec1bc0bc0bc1381bc1bc1bc1bc1fc0bc1b80bc1a81b81bc17813813d0bd12c1381b81bc1b811e0be12e13c16616e0be12e13816e09e1ce1e71ff1fb1ec1391fe15b1ff1ff1ef0fd1ff3ff1ff1ef0a71771bf17f0ed0fe0ff1bd1bd1ff1ff6df1ff1af1bd0bf0ff0fb1ff17f6bf07f1ff07f1bc1bd1bd1fd0ed0ff17f1bf1bd01f6df16f17f6df1af5ef0ff1ef1af1ef1ef2df1ff1f70fc1ff4ff1fd4ff1bd1bf1bf6ff1ff0ff6ff1ff17f15f17f1bf1fb4fd17f1ff1671ef1ef15b1ff1f315f1771bf3bf1ff3ff3ef0ff2ec3fd1bf19f0fd1ff1bf19f0fd1ff1ff1ff1dd1ff1bf1391ff19d0df1ff0dd1bf0fd69f6df1af1ff1bd6ff1ff1ff1ff1ff5fd1bf1ff1bd1fd1bd1bd1b56fd17f1ff17f0f91ff5ff1ff0bd1bd1ff1be1be1bf0ff6fe1fe4fe1fe07e6be1ff07e3ff3cf38f35f3ff3533f71ff35f39f3df3df35715f3df3df3df3df3ff35f3df0ff3ef2f73ff0bf19e1bf1ff0bd1bd1ff1ff0ff07d1bd1ff5ff6dd4ff1ee16f1ef1fe1ff1ff0af1ec0af5e66dc17f1fc1fe1ff1be1bf0001ff1ff1ff5fe6fc1ff1df1ff1fe1fe0fe1fc1bc1bc0bd1be1bd4fe0f73ff2fe3f739f1de3ff3df0f63df19d0df3ff3ff3bf0df3f73de3ff15e1ff3df1df1df2ff1ff1ff3ff1ff0001ff1fd1ff1ff3ff0001ff1ff1ff1ff0fd0df1ff1fd1ff1ff1ff1bf1ff1bf1ff1ff1ff3ff27f1ff1bd1ff1ff1fd1ff1ff1bf1ff1ff1fd1df1df1ff3ff1bf3ff1ff1ff1bd1ff3ff3ff3de1ff
  | 13 => 0x1bf1ff1bf1bf1bf1bf1ff1ff1ff1ff1bf1ff1bd1ff1bd1ff1bf1ff1ff1ff1ff1ff1ff1ff1ff
  | _ => 0
 (b >>> (12*i)) &&& 4095

def testPacked : FrontierTest := fun T mono ws r k i =>
  let chunk := rankModeData k i (if mono then 0 else 1)
  FrontRanks.rankHuffCheck T mono ws r (fun kind => if kind == 4 then (10, fun j => packedAt rankDictionary (36*j) 36) else let f := rankFormat kind; (f.1, fun j => packedAt f.2 (17*j) 17))
    (packedAt (rankWords k)) chunk.1 chunk.2 (supportMask k i)

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



abbrev AB := auditBlock
theorem J {k i a b : Nat} (x : AB k i a = true) (y : AB k (i+a) b = true) : AB k i (a+b) = true := joinBlock k i a b x y
abbrev J9 := @J 9
abbrev J10 := @J 10
abbrev J11 := @J 11
abbrev J12 := @J 12
abbrev J13 := @J 13
abbrev J14 := @J 14
theorem v0 : AB 9 0 1=true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem level9 : AB 9 0 1=true := v0
theorem v1 : AB 10 0 3=true := by decide +kernel
theorem v2 : AB 10 3 3=true := by decide +kernel
theorem v3 : AB 10 6 3=true := by decide +kernel
theorem v4 : AB 10 9 3=true := by decide +kernel
theorem v5 : AB 10 12 3=true := by decide +kernel
theorem v6 : AB 10 15 3=true := by decide +kernel
theorem v7 : AB 10 18 3=true := by decide +kernel
theorem v8 : AB 10 21 3=true := by decide +kernel
theorem v9 : AB 10 24 3=true := by decide +kernel
theorem v10 : AB 10 27 3=true := by decide +kernel
theorem v11 : AB 10 30 3=true := by decide +kernel
theorem v12 : AB 10 33 3=true := by decide +kernel
theorem v13 : AB 10 36 3=true := by decide +kernel
theorem v14 : AB 10 39 3=true := by decide +kernel
theorem v15 : AB 10 42 3=true := by decide +kernel
theorem v16 : AB 10 45 3=true := by decide +kernel
theorem v17 : AB 10 48 3=true := by decide +kernel
theorem v18 : AB 10 51 3=true := by decide +kernel
theorem v19 : AB 10 54 3=true := by decide +kernel
theorem v20 : AB 10 57 3=true := by decide +kernel
theorem v21 : AB 10 60 3=true := by decide +kernel
theorem v22 : AB 10 63 3=true := by decide +kernel
theorem v23 : AB 10 66 3=true := by decide +kernel
theorem v24 : AB 10 69 3=true := by decide +kernel
theorem v25 : AB 10 72 3=true := by decide +kernel
theorem v26 : AB 10 75 2=true := by decide +kernel
theorem v27 : AB 10 77 1=true := by decide +kernel
theorem v28 : AB 10 78 1=true := by decide +kernel
theorem v29 : AB 10 79 1=true := by decide +kernel
theorem v30 : AB 10 80 1=true := by decide +kernel
theorem v31 : AB 10 81 1=true := by decide +kernel
theorem v32 : AB 10 82 1=true := by decide +kernel
theorem v33 : AB 10 83 1=true := by decide +kernel
theorem v34 : AB 10 84 1=true := by decide +kernel
theorem v35 : AB 10 85 1=true := by decide +kernel
theorem v36 : AB 10 86 1=true := by decide +kernel
theorem v37 : AB 10 87 1=true := by decide +kernel
theorem v38 : AB 10 88 1=true := by decide +kernel
theorem v39 : AB 10 89 1=true := by decide +kernel
theorem v40 : AB 10 90 1=true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem level10 : AB 10 0 91=true := (@J10 0 60 31 (@J10 0 30 30 (@J10 0 15 15 (@J10 0 6 9 (@J10 0 3 3 v1 v2) (@J10 6 3 6 v3 (@J10 9 3 3 v4 v5))) (@J10 15 6 9 (@J10 15 3 3 v6 v7) (@J10 21 3 6 v8 (@J10 24 3 3 v9 v10)))) (@J10 30 15 15 (@J10 30 6 9 (@J10 30 3 3 v11 v12) (@J10 36 3 6 v13 (@J10 39 3 3 v14 v15))) (@J10 45 6 9 (@J10 45 3 3 v16 v17) (@J10 51 3 6 v18 (@J10 54 3 3 v19 v20))))) (@J10 60 21 10 (@J10 60 15 6 (@J10 60 6 9 (@J10 60 3 3 v21 v22) (@J10 66 3 6 v23 (@J10 69 3 3 v24 v25))) (@J10 75 3 3 (@J10 75 2 1 v26 v27) (@J10 78 1 2 v28 (@J10 79 1 1 v29 v30)))) (@J10 81 5 5 (@J10 81 2 3 (@J10 81 1 1 v31 v32) (@J10 83 1 2 v33 (@J10 84 1 1 v34 v35))) (@J10 86 2 3 (@J10 86 1 1 v36 v37) (@J10 88 1 2 v38 (@J10 89 1 1 v39 v40))))))
theorem v41 : AB 11 0 3=true := by decide +kernel
theorem v42 : AB 11 3 3=true := by decide +kernel
theorem v43 : AB 11 6 3=true := by decide +kernel
theorem v44 : AB 11 9 3=true := by decide +kernel
theorem v45 : AB 11 12 3=true := by decide +kernel
theorem v46 : AB 11 15 3=true := by decide +kernel
theorem v47 : AB 11 18 3=true := by decide +kernel
theorem v48 : AB 11 21 3=true := by decide +kernel
theorem v49 : AB 11 24 3=true := by decide +kernel
theorem v50 : AB 11 27 3=true := by decide +kernel
theorem v51 : AB 11 30 3=true := by decide +kernel
theorem v52 : AB 11 33 3=true := by decide +kernel
theorem v53 : AB 11 36 3=true := by decide +kernel
theorem v54 : AB 11 39 3=true := by decide +kernel
theorem v55 : AB 11 42 3=true := by decide +kernel
theorem v56 : AB 11 45 3=true := by decide +kernel
theorem v57 : AB 11 48 3=true := by decide +kernel
theorem v58 : AB 11 51 3=true := by decide +kernel
theorem v59 : AB 11 54 3=true := by decide +kernel
theorem v60 : AB 11 57 3=true := by decide +kernel
theorem v61 : AB 11 60 3=true := by decide +kernel
theorem v62 : AB 11 63 3=true := by decide +kernel
theorem v63 : AB 11 66 3=true := by decide +kernel
theorem v64 : AB 11 69 3=true := by decide +kernel
theorem v65 : AB 11 72 3=true := by decide +kernel
theorem v66 : AB 11 75 3=true := by decide +kernel
theorem v67 : AB 11 78 3=true := by decide +kernel
theorem v68 : AB 11 81 3=true := by decide +kernel
theorem v69 : AB 11 84 3=true := by decide +kernel
theorem v70 : AB 11 87 3=true := by decide +kernel
theorem v71 : AB 11 90 3=true := by decide +kernel
theorem v72 : AB 11 93 3=true := by decide +kernel
theorem v73 : AB 11 96 3=true := by decide +kernel
theorem v74 : AB 11 99 3=true := by decide +kernel
theorem v75 : AB 11 102 3=true := by decide +kernel
theorem v76 : AB 11 105 3=true := by decide +kernel
theorem v77 : AB 11 108 3=true := by decide +kernel
theorem v78 : AB 11 111 3=true := by decide +kernel
theorem v79 : AB 11 114 3=true := by decide +kernel
theorem v80 : AB 11 117 3=true := by decide +kernel
theorem v81 : AB 11 120 3=true := by decide +kernel
theorem v82 : AB 11 123 3=true := by decide +kernel
theorem v83 : AB 11 126 3=true := by decide +kernel
theorem v84 : AB 11 129 3=true := by decide +kernel
theorem v85 : AB 11 132 3=true := by decide +kernel
theorem v86 : AB 11 135 3=true := by decide +kernel
theorem v87 : AB 11 138 3=true := by decide +kernel
theorem v88 : AB 11 141 3=true := by decide +kernel
theorem v89 : AB 11 144 3=true := by decide +kernel
theorem v90 : AB 11 147 3=true := by decide +kernel
theorem v91 : AB 11 150 3=true := by decide +kernel
theorem v92 : AB 11 153 3=true := by decide +kernel
theorem v93 : AB 11 156 3=true := by decide +kernel
theorem v94 : AB 11 159 3=true := by decide +kernel
theorem v95 : AB 11 162 3=true := by decide +kernel
theorem v96 : AB 11 165 3=true := by decide +kernel
theorem v97 : AB 11 168 3=true := by decide +kernel
theorem v98 : AB 11 171 3=true := by decide +kernel
theorem v99 : AB 11 174 3=true := by decide +kernel
theorem v100 : AB 11 177 3=true := by decide +kernel
theorem v101 : AB 11 180 3=true := by decide +kernel
theorem v102 : AB 11 183 3=true := by decide +kernel
theorem v103 : AB 11 186 3=true := by decide +kernel
theorem v104 : AB 11 189 3=true := by decide +kernel
theorem v105 : AB 11 192 3=true := by decide +kernel
theorem v106 : AB 11 195 3=true := by decide +kernel
theorem v107 : AB 11 198 3=true := by decide +kernel
theorem v108 : AB 11 201 3=true := by decide +kernel
theorem v109 : AB 11 204 3=true := by decide +kernel
theorem v110 : AB 11 207 3=true := by decide +kernel
theorem v111 : AB 11 210 3=true := by decide +kernel
theorem v112 : AB 11 213 3=true := by decide +kernel
theorem v113 : AB 11 216 3=true := by decide +kernel
theorem v114 : AB 11 219 3=true := by decide +kernel
theorem v115 : AB 11 222 3=true := by decide +kernel
theorem v116 : AB 11 225 3=true := by decide +kernel
theorem v117 : AB 11 228 3=true := by decide +kernel
theorem v118 : AB 11 231 3=true := by decide +kernel
theorem v119 : AB 11 234 3=true := by decide +kernel
theorem v120 : AB 11 237 3=true := by decide +kernel
theorem v121 : AB 11 240 3=true := by decide +kernel
theorem v122 : AB 11 243 3=true := by decide +kernel
theorem v123 : AB 11 246 3=true := by decide +kernel
theorem v124 : AB 11 249 3=true := by decide +kernel
theorem v125 : AB 11 252 3=true := by decide +kernel
theorem v126 : AB 11 255 3=true := by decide +kernel
theorem v127 : AB 11 258 3=true := by decide +kernel
theorem v128 : AB 11 261 3=true := by decide +kernel
theorem v129 : AB 11 264 3=true := by decide +kernel
theorem v130 : AB 11 267 3=true := by decide +kernel
theorem v131 : AB 11 270 3=true := by decide +kernel
theorem v132 : AB 11 273 3=true := by decide +kernel
theorem v133 : AB 11 276 3=true := by decide +kernel
theorem v134 : AB 11 279 3=true := by decide +kernel
theorem v135 : AB 11 282 3=true := by decide +kernel
theorem v136 : AB 11 285 3=true := by decide +kernel
theorem v137 : AB 11 288 3=true := by decide +kernel
theorem v138 : AB 11 291 3=true := by decide +kernel
theorem v139 : AB 11 294 3=true := by decide +kernel
theorem v140 : AB 11 297 3=true := by decide +kernel
theorem v141 : AB 11 300 3=true := by decide +kernel
theorem v142 : AB 11 303 3=true := by decide +kernel
theorem v143 : AB 11 306 3=true := by decide +kernel
theorem v144 : AB 11 309 3=true := by decide +kernel
theorem v145 : AB 11 312 3=true := by decide +kernel
theorem v146 : AB 11 315 3=true := by decide +kernel
theorem v147 : AB 11 318 3=true := by decide +kernel
theorem v148 : AB 11 321 3=true := by decide +kernel
theorem v149 : AB 11 324 3=true := by decide +kernel
theorem v150 : AB 11 327 3=true := by decide +kernel
theorem v151 : AB 11 330 3=true := by decide +kernel
theorem v152 : AB 11 333 3=true := by decide +kernel
theorem v153 : AB 11 336 3=true := by decide +kernel
theorem v154 : AB 11 339 3=true := by decide +kernel
theorem v155 : AB 11 342 3=true := by decide +kernel
theorem v156 : AB 11 345 3=true := by decide +kernel
theorem v157 : AB 11 348 3=true := by decide +kernel
theorem v158 : AB 11 351 3=true := by decide +kernel
theorem v159 : AB 11 354 3=true := by decide +kernel
theorem v160 : AB 11 357 3=true := by decide +kernel
theorem v161 : AB 11 360 3=true := by decide +kernel
theorem v162 : AB 11 363 3=true := by decide +kernel
theorem v163 : AB 11 366 3=true := by decide +kernel
theorem v164 : AB 11 369 3=true := by decide +kernel
theorem v165 : AB 11 372 3=true := by decide +kernel
theorem v166 : AB 11 375 3=true := by decide +kernel
theorem v167 : AB 11 378 3=true := by decide +kernel
theorem v168 : AB 11 381 3=true := by decide +kernel
theorem v169 : AB 11 384 3=true := by decide +kernel
theorem v170 : AB 11 387 3=true := by decide +kernel
theorem v171 : AB 11 390 3=true := by decide +kernel
theorem v172 : AB 11 393 3=true := by decide +kernel
theorem v173 : AB 11 396 3=true := by decide +kernel
theorem v174 : AB 11 399 3=true := by decide +kernel
theorem v175 : AB 11 402 3=true := by decide +kernel
theorem v176 : AB 11 405 3=true := by decide +kernel
theorem v177 : AB 11 408 3=true := by decide +kernel
theorem v178 : AB 11 411 3=true := by decide +kernel
theorem v179 : AB 11 414 3=true := by decide +kernel
theorem v180 : AB 11 417 3=true := by decide +kernel
theorem v181 : AB 11 420 3=true := by decide +kernel
theorem v182 : AB 11 423 3=true := by decide +kernel
theorem v183 : AB 11 426 3=true := by decide +kernel
theorem v184 : AB 11 429 3=true := by decide +kernel
theorem v185 : AB 11 432 3=true := by decide +kernel
theorem v186 : AB 11 435 3=true := by decide +kernel
theorem v187 : AB 11 438 3=true := by decide +kernel
theorem v188 : AB 11 441 3=true := by decide +kernel
theorem v189 : AB 11 444 3=true := by decide +kernel
theorem v190 : AB 11 447 3=true := by decide +kernel
theorem v191 : AB 11 450 3=true := by decide +kernel
theorem v192 : AB 11 453 3=true := by decide +kernel
theorem v193 : AB 11 456 3=true := by decide +kernel
theorem v194 : AB 11 459 3=true := by decide +kernel
theorem v195 : AB 11 462 3=true := by decide +kernel
theorem v196 : AB 11 465 3=true := by decide +kernel
theorem v197 : AB 11 468 3=true := by decide +kernel
theorem v198 : AB 11 471 3=true := by decide +kernel
theorem v199 : AB 11 474 3=true := by decide +kernel
theorem v200 : AB 11 477 3=true := by decide +kernel
theorem v201 : AB 11 480 3=true := by decide +kernel
theorem v202 : AB 11 483 3=true := by decide +kernel
theorem v203 : AB 11 486 3=true := by decide +kernel
theorem v204 : AB 11 489 3=true := by decide +kernel
theorem v205 : AB 11 492 3=true := by decide +kernel
theorem v206 : AB 11 495 3=true := by decide +kernel
theorem v207 : AB 11 498 3=true := by decide +kernel
theorem v208 : AB 11 501 3=true := by decide +kernel
theorem v209 : AB 11 504 3=true := by decide +kernel
theorem v210 : AB 11 507 3=true := by decide +kernel
theorem v211 : AB 11 510 3=true := by decide +kernel
theorem v212 : AB 11 513 3=true := by decide +kernel
theorem v213 : AB 11 516 3=true := by decide +kernel
theorem v214 : AB 11 519 3=true := by decide +kernel
theorem v215 : AB 11 522 3=true := by decide +kernel
theorem v216 : AB 11 525 3=true := by decide +kernel
theorem v217 : AB 11 528 3=true := by decide +kernel
theorem v218 : AB 11 531 3=true := by decide +kernel
theorem v219 : AB 11 534 3=true := by decide +kernel
theorem v220 : AB 11 537 3=true := by decide +kernel
theorem v221 : AB 11 540 3=true := by decide +kernel
theorem v222 : AB 11 543 3=true := by decide +kernel
theorem v223 : AB 11 546 3=true := by decide +kernel
theorem v224 : AB 11 549 3=true := by decide +kernel
theorem v225 : AB 11 552 3=true := by decide +kernel
theorem v226 : AB 11 555 3=true := by decide +kernel
theorem v227 : AB 11 558 3=true := by decide +kernel
theorem v228 : AB 11 561 3=true := by decide +kernel
theorem v229 : AB 11 564 3=true := by decide +kernel
theorem v230 : AB 11 567 3=true := by decide +kernel
theorem v231 : AB 11 570 3=true := by decide +kernel
theorem v232 : AB 11 573 3=true := by decide +kernel
theorem v233 : AB 11 576 3=true := by decide +kernel
theorem v234 : AB 11 579 3=true := by decide +kernel
theorem v235 : AB 11 582 3=true := by decide +kernel
theorem v236 : AB 11 585 3=true := by decide +kernel
theorem v237 : AB 11 588 3=true := by decide +kernel
theorem v238 : AB 11 591 3=true := by decide +kernel
theorem v239 : AB 11 594 3=true := by decide +kernel
theorem v240 : AB 11 597 3=true := by decide +kernel
theorem v241 : AB 11 600 3=true := by decide +kernel
theorem v242 : AB 11 603 3=true := by decide +kernel
theorem v243 : AB 11 606 3=true := by decide +kernel
theorem v244 : AB 11 609 3=true := by decide +kernel
theorem v245 : AB 11 612 3=true := by decide +kernel
theorem v246 : AB 11 615 3=true := by decide +kernel
theorem v247 : AB 11 618 3=true := by decide +kernel
theorem v248 : AB 11 621 3=true := by decide +kernel
theorem v249 : AB 11 624 3=true := by decide +kernel
theorem v250 : AB 11 627 3=true := by decide +kernel
theorem v251 : AB 11 630 3=true := by decide +kernel
theorem v252 : AB 11 633 3=true := by decide +kernel
theorem v253 : AB 11 636 3=true := by decide +kernel
theorem v254 : AB 11 639 3=true := by decide +kernel
theorem v255 : AB 11 642 3=true := by decide +kernel
theorem v256 : AB 11 645 3=true := by decide +kernel
theorem v257 : AB 11 648 3=true := by decide +kernel
theorem v258 : AB 11 651 3=true := by decide +kernel
theorem v259 : AB 11 654 3=true := by decide +kernel
theorem v260 : AB 11 657 3=true := by decide +kernel
theorem v261 : AB 11 660 3=true := by decide +kernel
theorem v262 : AB 11 663 3=true := by decide +kernel
theorem v263 : AB 11 666 3=true := by decide +kernel
theorem v264 : AB 11 669 3=true := by decide +kernel
theorem v265 : AB 11 672 3=true := by decide +kernel
theorem v266 : AB 11 675 3=true := by decide +kernel
theorem v267 : AB 11 678 3=true := by decide +kernel
theorem v268 : AB 11 681 3=true := by decide +kernel
theorem v269 : AB 11 684 3=true := by decide +kernel
theorem v270 : AB 11 687 3=true := by decide +kernel
theorem v271 : AB 11 690 3=true := by decide +kernel
theorem v272 : AB 11 693 3=true := by decide +kernel
theorem v273 : AB 11 696 3=true := by decide +kernel
theorem v274 : AB 11 699 3=true := by decide +kernel
theorem v275 : AB 11 702 3=true := by decide +kernel
theorem v276 : AB 11 705 3=true := by decide +kernel
theorem v277 : AB 11 708 3=true := by decide +kernel
theorem v278 : AB 11 711 3=true := by decide +kernel
theorem v279 : AB 11 714 1=true := by decide +kernel
theorem v280 : AB 11 715 1=true := by decide +kernel
theorem v281 : AB 11 716 1=true := by decide +kernel
theorem v282 : AB 11 717 1=true := by decide +kernel
theorem v283 : AB 11 718 1=true := by decide +kernel
theorem v284 : AB 11 719 1=true := by decide +kernel
theorem v285 : AB 11 720 1=true := by decide +kernel
theorem v286 : AB 11 721 1=true := by decide +kernel
theorem v287 : AB 11 722 1=true := by decide +kernel
theorem v288 : AB 11 723 1=true := by decide +kernel
theorem v289 : AB 11 724 1=true := by decide +kernel
theorem v290 : AB 11 725 1=true := by decide +kernel
theorem v291 : AB 11 726 1=true := by decide +kernel
theorem v292 : AB 11 727 1=true := by decide +kernel
theorem v293 : AB 11 728 1=true := by decide +kernel
theorem v294 : AB 11 729 1=true := by decide +kernel
theorem v295 : AB 11 730 1=true := by decide +kernel
theorem v296 : AB 11 731 1=true := by decide +kernel
theorem v297 : AB 11 732 1=true := by decide +kernel
theorem v298 : AB 11 733 1=true := by decide +kernel
theorem v299 : AB 11 734 1=true := by decide +kernel
theorem v300 : AB 11 735 1=true := by decide +kernel
theorem v301 : AB 11 736 1=true := by decide +kernel
theorem v302 : AB 11 737 1=true := by decide +kernel
theorem v303 : AB 11 738 1=true := by decide +kernel
theorem v304 : AB 11 739 1=true := by decide +kernel
theorem v305 : AB 11 740 1=true := by decide +kernel
theorem v306 : AB 11 741 1=true := by decide +kernel
theorem v307 : AB 11 742 1=true := by decide +kernel
theorem v308 : AB 11 743 1=true := by decide +kernel
theorem v309 : AB 11 744 1=true := by decide +kernel
theorem v310 : AB 11 745 1=true := by decide +kernel
theorem v311 : AB 11 746 1=true := by decide +kernel
theorem v312 : AB 11 747 1=true := by decide +kernel
theorem v313 : AB 11 748 1=true := by decide +kernel
theorem v314 : AB 11 749 1=true := by decide +kernel
theorem v315 : AB 11 750 1=true := by decide +kernel
theorem v316 : AB 11 751 1=true := by decide +kernel
theorem v317 : AB 11 752 1=true := by decide +kernel
theorem v318 : AB 11 753 1=true := by decide +kernel
theorem v319 : AB 11 754 1=true := by decide +kernel
theorem v320 : AB 11 755 1=true := by decide +kernel
theorem v321 : AB 11 756 1=true := by decide +kernel
theorem v322 : AB 11 757 1=true := by decide +kernel
theorem v323 : AB 11 758 1=true := by decide +kernel
theorem v324 : AB 11 759 1=true := by decide +kernel
theorem v325 : AB 11 760 1=true := by decide +kernel
theorem v326 : AB 11 761 1=true := by decide +kernel
theorem v327 : AB 11 762 1=true := by decide +kernel
theorem v328 : AB 11 763 1=true := by decide +kernel
theorem v329 : AB 11 764 1=true := by decide +kernel
theorem v330 : AB 11 765 1=true := by decide +kernel
theorem v331 : AB 11 766 1=true := by decide +kernel
theorem v332 : AB 11 767 1=true := by decide +kernel
theorem v333 : AB 11 768 1=true := by decide +kernel
theorem v334 : AB 11 769 1=true := by decide +kernel
theorem v335 : AB 11 770 1=true := by decide +kernel
theorem v336 : AB 11 771 1=true := by decide +kernel
theorem v337 : AB 11 772 1=true := by decide +kernel
theorem v338 : AB 11 773 1=true := by decide +kernel
theorem v339 : AB 11 774 1=true := by decide +kernel
theorem v340 : AB 11 775 1=true := by decide +kernel
theorem v341 : AB 11 776 1=true := by decide +kernel
theorem v342 : AB 11 777 1=true := by decide +kernel
theorem v343 : AB 11 778 1=true := by decide +kernel
theorem v344 : AB 11 779 1=true := by decide +kernel
theorem v345 : AB 11 780 1=true := by decide +kernel
theorem v346 : AB 11 781 1=true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem level11 : AB 11 0 782=true := (@J11 0 459 323 (@J11 0 228 231 (@J11 0 114 114 (@J11 0 57 57 (@J11 0 27 30 (@J11 0 12 15 (@J11 0 6 6 (@J11 0 3 3 v41 v42) (@J11 6 3 3 v43 v44)) (@J11 12 6 9 (@J11 12 3 3 v45 v46) (@J11 18 3 6 v47 (@J11 21 3 3 v48 v49)))) (@J11 27 15 15 (@J11 27 6 9 (@J11 27 3 3 v50 v51) (@J11 33 3 6 v52 (@J11 36 3 3 v53 v54))) (@J11 42 6 9 (@J11 42 3 3 v55 v56) (@J11 48 3 6 v57 (@J11 51 3 3 v58 v59))))) (@J11 57 27 30 (@J11 57 12 15 (@J11 57 6 6 (@J11 57 3 3 v60 v61) (@J11 63 3 3 v62 v63)) (@J11 69 6 9 (@J11 69 3 3 v64 v65) (@J11 75 3 6 v66 (@J11 78 3 3 v67 v68)))) (@J11 84 15 15 (@J11 84 6 9 (@J11 84 3 3 v69 v70) (@J11 90 3 6 v71 (@J11 93 3 3 v72 v73))) (@J11 99 6 9 (@J11 99 3 3 v74 v75) (@J11 105 3 6 v76 (@J11 108 3 3 v77 v78)))))) (@J11 114 57 57 (@J11 114 27 30 (@J11 114 12 15 (@J11 114 6 6 (@J11 114 3 3 v79 v80) (@J11 120 3 3 v81 v82)) (@J11 126 6 9 (@J11 126 3 3 v83 v84) (@J11 132 3 6 v85 (@J11 135 3 3 v86 v87)))) (@J11 141 15 15 (@J11 141 6 9 (@J11 141 3 3 v88 v89) (@J11 147 3 6 v90 (@J11 150 3 3 v91 v92))) (@J11 156 6 9 (@J11 156 3 3 v93 v94) (@J11 162 3 6 v95 (@J11 165 3 3 v96 v97))))) (@J11 171 27 30 (@J11 171 12 15 (@J11 171 6 6 (@J11 171 3 3 v98 v99) (@J11 177 3 3 v100 v101)) (@J11 183 6 9 (@J11 183 3 3 v102 v103) (@J11 189 3 6 v104 (@J11 192 3 3 v105 v106)))) (@J11 198 15 15 (@J11 198 6 9 (@J11 198 3 3 v107 v108) (@J11 204 3 6 v109 (@J11 207 3 3 v110 v111))) (@J11 213 6 9 (@J11 213 3 3 v112 v113) (@J11 219 3 6 v114 (@J11 222 3 3 v115 v116))))))) (@J11 228 114 117 (@J11 228 57 57 (@J11 228 27 30 (@J11 228 12 15 (@J11 228 6 6 (@J11 228 3 3 v117 v118) (@J11 234 3 3 v119 v120)) (@J11 240 6 9 (@J11 240 3 3 v121 v122) (@J11 246 3 6 v123 (@J11 249 3 3 v124 v125)))) (@J11 255 15 15 (@J11 255 6 9 (@J11 255 3 3 v126 v127) (@J11 261 3 6 v128 (@J11 264 3 3 v129 v130))) (@J11 270 6 9 (@J11 270 3 3 v131 v132) (@J11 276 3 6 v133 (@J11 279 3 3 v134 v135))))) (@J11 285 27 30 (@J11 285 12 15 (@J11 285 6 6 (@J11 285 3 3 v136 v137) (@J11 291 3 3 v138 v139)) (@J11 297 6 9 (@J11 297 3 3 v140 v141) (@J11 303 3 6 v142 (@J11 306 3 3 v143 v144)))) (@J11 312 15 15 (@J11 312 6 9 (@J11 312 3 3 v145 v146) (@J11 318 3 6 v147 (@J11 321 3 3 v148 v149))) (@J11 327 6 9 (@J11 327 3 3 v150 v151) (@J11 333 3 6 v152 (@J11 336 3 3 v153 v154)))))) (@J11 342 57 60 (@J11 342 27 30 (@J11 342 12 15 (@J11 342 6 6 (@J11 342 3 3 v155 v156) (@J11 348 3 3 v157 v158)) (@J11 354 6 9 (@J11 354 3 3 v159 v160) (@J11 360 3 6 v161 (@J11 363 3 3 v162 v163)))) (@J11 369 15 15 (@J11 369 6 9 (@J11 369 3 3 v164 v165) (@J11 375 3 6 v166 (@J11 378 3 3 v167 v168))) (@J11 384 6 9 (@J11 384 3 3 v169 v170) (@J11 390 3 6 v171 (@J11 393 3 3 v172 v173))))) (@J11 399 30 30 (@J11 399 15 15 (@J11 399 6 9 (@J11 399 3 3 v174 v175) (@J11 405 3 6 v176 (@J11 408 3 3 v177 v178))) (@J11 414 6 9 (@J11 414 3 3 v179 v180) (@J11 420 3 6 v181 (@J11 423 3 3 v182 v183)))) (@J11 429 15 15 (@J11 429 6 9 (@J11 429 3 3 v184 v185) (@J11 435 3 6 v186 (@J11 438 3 3 v187 v188))) (@J11 444 6 9 (@J11 444 3 3 v189 v190) (@J11 450 3 6 v191 (@J11 453 3 3 v192 v193)))))))) (@J11 459 228 95 (@J11 459 114 114 (@J11 459 57 57 (@J11 459 27 30 (@J11 459 12 15 (@J11 459 6 6 (@J11 459 3 3 v194 v195) (@J11 465 3 3 v196 v197)) (@J11 471 6 9 (@J11 471 3 3 v198 v199) (@J11 477 3 6 v200 (@J11 480 3 3 v201 v202)))) (@J11 486 15 15 (@J11 486 6 9 (@J11 486 3 3 v203 v204) (@J11 492 3 6 v205 (@J11 495 3 3 v206 v207))) (@J11 501 6 9 (@J11 501 3 3 v208 v209) (@J11 507 3 6 v210 (@J11 510 3 3 v211 v212))))) (@J11 516 27 30 (@J11 516 12 15 (@J11 516 6 6 (@J11 516 3 3 v213 v214) (@J11 522 3 3 v215 v216)) (@J11 528 6 9 (@J11 528 3 3 v217 v218) (@J11 534 3 6 v219 (@J11 537 3 3 v220 v221)))) (@J11 543 15 15 (@J11 543 6 9 (@J11 543 3 3 v222 v223) (@J11 549 3 6 v224 (@J11 552 3 3 v225 v226))) (@J11 558 6 9 (@J11 558 3 3 v227 v228) (@J11 564 3 6 v229 (@J11 567 3 3 v230 v231)))))) (@J11 573 57 57 (@J11 573 27 30 (@J11 573 12 15 (@J11 573 6 6 (@J11 573 3 3 v232 v233) (@J11 579 3 3 v234 v235)) (@J11 585 6 9 (@J11 585 3 3 v236 v237) (@J11 591 3 6 v238 (@J11 594 3 3 v239 v240)))) (@J11 600 15 15 (@J11 600 6 9 (@J11 600 3 3 v241 v242) (@J11 606 3 6 v243 (@J11 609 3 3 v244 v245))) (@J11 615 6 9 (@J11 615 3 3 v246 v247) (@J11 621 3 6 v248 (@J11 624 3 3 v249 v250))))) (@J11 630 27 30 (@J11 630 12 15 (@J11 630 6 6 (@J11 630 3 3 v251 v252) (@J11 636 3 3 v253 v254)) (@J11 642 6 9 (@J11 642 3 3 v255 v256) (@J11 648 3 6 v257 (@J11 651 3 3 v258 v259)))) (@J11 657 15 15 (@J11 657 6 9 (@J11 657 3 3 v260 v261) (@J11 663 3 6 v262 (@J11 666 3 3 v263 v264))) (@J11 672 6 9 (@J11 672 3 3 v265 v266) (@J11 678 3 6 v267 (@J11 681 3 3 v268 v269))))))) (@J11 687 56 39 (@J11 687 37 19 (@J11 687 27 10 (@J11 687 12 15 (@J11 687 6 6 (@J11 687 3 3 v270 v271) (@J11 693 3 3 v272 v273)) (@J11 699 6 9 (@J11 699 3 3 v274 v275) (@J11 705 3 6 v276 (@J11 708 3 3 v277 v278)))) (@J11 714 5 5 (@J11 714 2 3 (@J11 714 1 1 v279 v280) (@J11 716 1 2 v281 (@J11 717 1 1 v282 v283))) (@J11 719 2 3 (@J11 719 1 1 v284 v285) (@J11 721 1 2 v286 (@J11 722 1 1 v287 v288))))) (@J11 724 9 10 (@J11 724 4 5 (@J11 724 2 2 (@J11 724 1 1 v289 v290) (@J11 726 1 1 v291 v292)) (@J11 728 2 3 (@J11 728 1 1 v293 v294) (@J11 730 1 2 v295 (@J11 731 1 1 v296 v297)))) (@J11 733 5 5 (@J11 733 2 3 (@J11 733 1 1 v298 v299) (@J11 735 1 2 v300 (@J11 736 1 1 v301 v302))) (@J11 738 2 3 (@J11 738 1 1 v303 v304) (@J11 740 1 2 v305 (@J11 741 1 1 v306 v307)))))) (@J11 743 19 20 (@J11 743 9 10 (@J11 743 4 5 (@J11 743 2 2 (@J11 743 1 1 v308 v309) (@J11 745 1 1 v310 v311)) (@J11 747 2 3 (@J11 747 1 1 v312 v313) (@J11 749 1 2 v314 (@J11 750 1 1 v315 v316)))) (@J11 752 5 5 (@J11 752 2 3 (@J11 752 1 1 v317 v318) (@J11 754 1 2 v319 (@J11 755 1 1 v320 v321))) (@J11 757 2 3 (@J11 757 1 1 v322 v323) (@J11 759 1 2 v324 (@J11 760 1 1 v325 v326))))) (@J11 762 10 10 (@J11 762 5 5 (@J11 762 2 3 (@J11 762 1 1 v327 v328) (@J11 764 1 2 v329 (@J11 765 1 1 v330 v331))) (@J11 767 2 3 (@J11 767 1 1 v332 v333) (@J11 769 1 2 v334 (@J11 770 1 1 v335 v336)))) (@J11 772 5 5 (@J11 772 2 3 (@J11 772 1 1 v337 v338) (@J11 774 1 2 v339 (@J11 775 1 1 v340 v341))) (@J11 777 2 3 (@J11 777 1 1 v342 v343) (@J11 779 1 2 v344 (@J11 780 1 1 v345 v346)))))))))
theorem v347 : AB 12 0 1=true := by decide +kernel
theorem v348 : AB 12 1 1=true := by decide +kernel
theorem v349 : AB 12 2 1=true := by decide +kernel
theorem v350 : AB 12 3 1=true := by decide +kernel
theorem v351 : AB 12 4 1=true := by decide +kernel
theorem v352 : AB 12 5 1=true := by decide +kernel
theorem v353 : AB 12 6 1=true := by decide +kernel
theorem v354 : AB 12 7 1=true := by decide +kernel
theorem v355 : AB 12 8 1=true := by decide +kernel
theorem v356 : AB 12 9 1=true := by decide +kernel
theorem v357 : AB 12 10 1=true := by decide +kernel
theorem v358 : AB 12 11 1=true := by decide +kernel
theorem v359 : AB 12 12 1=true := by decide +kernel
theorem v360 : AB 12 13 1=true := by decide +kernel
theorem v361 : AB 12 14 1=true := by decide +kernel
theorem v362 : AB 12 15 1=true := by decide +kernel
theorem v363 : AB 12 16 1=true := by decide +kernel
theorem v364 : AB 12 17 1=true := by decide +kernel
theorem v365 : AB 12 18 1=true := by decide +kernel
theorem v366 : AB 12 19 1=true := by decide +kernel
theorem v367 : AB 12 20 1=true := by decide +kernel
theorem v368 : AB 12 21 1=true := by decide +kernel
theorem v369 : AB 12 22 1=true := by decide +kernel
theorem v370 : AB 12 23 1=true := by decide +kernel
theorem v371 : AB 12 24 1=true := by decide +kernel
theorem v372 : AB 12 25 1=true := by decide +kernel
theorem v373 : AB 12 26 1=true := by decide +kernel
theorem v374 : AB 12 27 1=true := by decide +kernel
theorem v375 : AB 12 28 1=true := by decide +kernel
theorem v376 : AB 12 29 1=true := by decide +kernel
theorem v377 : AB 12 30 1=true := by decide +kernel
theorem v378 : AB 12 31 1=true := by decide +kernel
theorem v379 : AB 12 32 1=true := by decide +kernel
theorem v380 : AB 12 33 1=true := by decide +kernel
theorem v381 : AB 12 34 1=true := by decide +kernel
theorem v382 : AB 12 35 1=true := by decide +kernel
theorem v383 : AB 12 36 1=true := by decide +kernel
theorem v384 : AB 12 37 1=true := by decide +kernel
theorem v385 : AB 12 38 1=true := by decide +kernel
theorem v386 : AB 12 39 1=true := by decide +kernel
theorem v387 : AB 12 40 1=true := by decide +kernel
theorem v388 : AB 12 41 1=true := by decide +kernel
theorem v389 : AB 12 42 1=true := by decide +kernel
theorem v390 : AB 12 43 1=true := by decide +kernel
theorem v391 : AB 12 44 1=true := by decide +kernel
theorem v392 : AB 12 45 1=true := by decide +kernel
theorem v393 : AB 12 46 1=true := by decide +kernel
theorem v394 : AB 12 47 1=true := by decide +kernel
theorem v395 : AB 12 48 1=true := by decide +kernel
theorem v396 : AB 12 49 1=true := by decide +kernel
theorem v397 : AB 12 50 1=true := by decide +kernel
theorem v398 : AB 12 51 1=true := by decide +kernel
theorem v399 : AB 12 52 1=true := by decide +kernel
theorem v400 : AB 12 53 1=true := by decide +kernel
theorem v401 : AB 12 54 1=true := by decide +kernel
theorem v402 : AB 12 55 1=true := by decide +kernel
theorem v403 : AB 12 56 3=true := by decide +kernel
theorem v404 : AB 12 59 3=true := by decide +kernel
theorem v405 : AB 12 62 3=true := by decide +kernel
theorem v406 : AB 12 65 3=true := by decide +kernel
theorem v407 : AB 12 68 3=true := by decide +kernel
theorem v408 : AB 12 71 3=true := by decide +kernel
theorem v409 : AB 12 74 3=true := by decide +kernel
theorem v410 : AB 12 77 3=true := by decide +kernel
theorem v411 : AB 12 80 3=true := by decide +kernel
theorem v412 : AB 12 83 3=true := by decide +kernel
theorem v413 : AB 12 86 3=true := by decide +kernel
theorem v414 : AB 12 89 3=true := by decide +kernel
theorem v415 : AB 12 92 3=true := by decide +kernel
theorem v416 : AB 12 95 3=true := by decide +kernel
theorem v417 : AB 12 98 3=true := by decide +kernel
theorem v418 : AB 12 101 3=true := by decide +kernel
theorem v419 : AB 12 104 3=true := by decide +kernel
theorem v420 : AB 12 107 3=true := by decide +kernel
theorem v421 : AB 12 110 3=true := by decide +kernel
theorem v422 : AB 12 113 3=true := by decide +kernel
theorem v423 : AB 12 116 3=true := by decide +kernel
theorem v424 : AB 12 119 3=true := by decide +kernel
theorem v425 : AB 12 122 3=true := by decide +kernel
theorem v426 : AB 12 125 3=true := by decide +kernel
theorem v427 : AB 12 128 3=true := by decide +kernel
theorem v428 : AB 12 131 3=true := by decide +kernel
theorem v429 : AB 12 134 3=true := by decide +kernel
theorem v430 : AB 12 137 3=true := by decide +kernel
theorem v431 : AB 12 140 3=true := by decide +kernel
theorem v432 : AB 12 143 3=true := by decide +kernel
theorem v433 : AB 12 146 3=true := by decide +kernel
theorem v434 : AB 12 149 3=true := by decide +kernel
theorem v435 : AB 12 152 3=true := by decide +kernel
theorem v436 : AB 12 155 3=true := by decide +kernel
theorem v437 : AB 12 158 3=true := by decide +kernel
theorem v438 : AB 12 161 3=true := by decide +kernel
theorem v439 : AB 12 164 3=true := by decide +kernel
theorem v440 : AB 12 167 3=true := by decide +kernel
theorem v441 : AB 12 170 3=true := by decide +kernel
theorem v442 : AB 12 173 3=true := by decide +kernel
theorem v443 : AB 12 176 3=true := by decide +kernel
theorem v444 : AB 12 179 3=true := by decide +kernel
theorem v445 : AB 12 182 3=true := by decide +kernel
theorem v446 : AB 12 185 3=true := by decide +kernel
theorem v447 : AB 12 188 3=true := by decide +kernel
theorem v448 : AB 12 191 3=true := by decide +kernel
theorem v449 : AB 12 194 3=true := by decide +kernel
theorem v450 : AB 12 197 3=true := by decide +kernel
theorem v451 : AB 12 200 3=true := by decide +kernel
theorem v452 : AB 12 203 3=true := by decide +kernel
theorem v453 : AB 12 206 3=true := by decide +kernel
theorem v454 : AB 12 209 3=true := by decide +kernel
theorem v455 : AB 12 212 3=true := by decide +kernel
theorem v456 : AB 12 215 3=true := by decide +kernel
theorem v457 : AB 12 218 3=true := by decide +kernel
theorem v458 : AB 12 221 3=true := by decide +kernel
theorem v459 : AB 12 224 3=true := by decide +kernel
theorem v460 : AB 12 227 3=true := by decide +kernel
theorem v461 : AB 12 230 3=true := by decide +kernel
theorem v462 : AB 12 233 3=true := by decide +kernel
theorem v463 : AB 12 236 3=true := by decide +kernel
theorem v464 : AB 12 239 3=true := by decide +kernel
theorem v465 : AB 12 242 3=true := by decide +kernel
theorem v466 : AB 12 245 3=true := by decide +kernel
theorem v467 : AB 12 248 3=true := by decide +kernel
theorem v468 : AB 12 251 3=true := by decide +kernel
theorem v469 : AB 12 254 3=true := by decide +kernel
theorem v470 : AB 12 257 3=true := by decide +kernel
theorem v471 : AB 12 260 3=true := by decide +kernel
theorem v472 : AB 12 263 3=true := by decide +kernel
theorem v473 : AB 12 266 3=true := by decide +kernel
theorem v474 : AB 12 269 3=true := by decide +kernel
theorem v475 : AB 12 272 3=true := by decide +kernel
theorem v476 : AB 12 275 3=true := by decide +kernel
theorem v477 : AB 12 278 3=true := by decide +kernel
theorem v478 : AB 12 281 3=true := by decide +kernel
theorem v479 : AB 12 284 3=true := by decide +kernel
theorem v480 : AB 12 287 3=true := by decide +kernel
theorem v481 : AB 12 290 3=true := by decide +kernel
theorem v482 : AB 12 293 3=true := by decide +kernel
theorem v483 : AB 12 296 3=true := by decide +kernel
theorem v484 : AB 12 299 3=true := by decide +kernel
theorem v485 : AB 12 302 3=true := by decide +kernel
theorem v486 : AB 12 305 3=true := by decide +kernel
theorem v487 : AB 12 308 3=true := by decide +kernel
theorem v488 : AB 12 311 3=true := by decide +kernel
theorem v489 : AB 12 314 3=true := by decide +kernel
theorem v490 : AB 12 317 3=true := by decide +kernel
theorem v491 : AB 12 320 3=true := by decide +kernel
theorem v492 : AB 12 323 3=true := by decide +kernel
theorem v493 : AB 12 326 3=true := by decide +kernel
theorem v494 : AB 12 329 3=true := by decide +kernel
theorem v495 : AB 12 332 3=true := by decide +kernel
theorem v496 : AB 12 335 3=true := by decide +kernel
theorem v497 : AB 12 338 3=true := by decide +kernel
theorem v498 : AB 12 341 3=true := by decide +kernel
theorem v499 : AB 12 344 3=true := by decide +kernel
theorem v500 : AB 12 347 3=true := by decide +kernel
theorem v501 : AB 12 350 3=true := by decide +kernel
theorem v502 : AB 12 353 3=true := by decide +kernel
theorem v503 : AB 12 356 3=true := by decide +kernel
theorem v504 : AB 12 359 3=true := by decide +kernel
theorem v505 : AB 12 362 3=true := by decide +kernel
theorem v506 : AB 12 365 3=true := by decide +kernel
theorem v507 : AB 12 368 3=true := by decide +kernel
theorem v508 : AB 12 371 3=true := by decide +kernel
theorem v509 : AB 12 374 3=true := by decide +kernel
theorem v510 : AB 12 377 3=true := by decide +kernel
theorem v511 : AB 12 380 3=true := by decide +kernel
theorem v512 : AB 12 383 3=true := by decide +kernel
theorem v513 : AB 12 386 3=true := by decide +kernel
theorem v514 : AB 12 389 3=true := by decide +kernel
theorem v515 : AB 12 392 3=true := by decide +kernel
theorem v516 : AB 12 395 3=true := by decide +kernel
theorem v517 : AB 12 398 3=true := by decide +kernel
theorem v518 : AB 12 401 3=true := by decide +kernel
theorem v519 : AB 12 404 3=true := by decide +kernel
theorem v520 : AB 12 407 3=true := by decide +kernel
theorem v521 : AB 12 410 3=true := by decide +kernel
theorem v522 : AB 12 413 3=true := by decide +kernel
theorem v523 : AB 12 416 3=true := by decide +kernel
theorem v524 : AB 12 419 3=true := by decide +kernel
theorem v525 : AB 12 422 3=true := by decide +kernel
theorem v526 : AB 12 425 3=true := by decide +kernel
theorem v527 : AB 12 428 3=true := by decide +kernel
theorem v528 : AB 12 431 3=true := by decide +kernel
theorem v529 : AB 12 434 3=true := by decide +kernel
theorem v530 : AB 12 437 3=true := by decide +kernel
theorem v531 : AB 12 440 3=true := by decide +kernel
theorem v532 : AB 12 443 3=true := by decide +kernel
theorem v533 : AB 12 446 3=true := by decide +kernel
theorem v534 : AB 12 449 3=true := by decide +kernel
theorem v535 : AB 12 452 3=true := by decide +kernel
theorem v536 : AB 12 455 3=true := by decide +kernel
theorem v537 : AB 12 458 3=true := by decide +kernel
theorem v538 : AB 12 461 3=true := by decide +kernel
theorem v539 : AB 12 464 3=true := by decide +kernel
theorem v540 : AB 12 467 3=true := by decide +kernel
theorem v541 : AB 12 470 3=true := by decide +kernel
theorem v542 : AB 12 473 3=true := by decide +kernel
theorem v543 : AB 12 476 3=true := by decide +kernel
theorem v544 : AB 12 479 3=true := by decide +kernel
theorem v545 : AB 12 482 3=true := by decide +kernel
theorem v546 : AB 12 485 3=true := by decide +kernel
theorem v547 : AB 12 488 3=true := by decide +kernel
theorem v548 : AB 12 491 3=true := by decide +kernel
theorem v549 : AB 12 494 3=true := by decide +kernel
theorem v550 : AB 12 497 3=true := by decide +kernel
theorem v551 : AB 12 500 3=true := by decide +kernel
theorem v552 : AB 12 503 3=true := by decide +kernel
theorem v553 : AB 12 506 3=true := by decide +kernel
theorem v554 : AB 12 509 3=true := by decide +kernel
theorem v555 : AB 12 512 3=true := by decide +kernel
theorem v556 : AB 12 515 3=true := by decide +kernel
theorem v557 : AB 12 518 3=true := by decide +kernel
theorem v558 : AB 12 521 3=true := by decide +kernel
theorem v559 : AB 12 524 3=true := by decide +kernel
theorem v560 : AB 12 527 3=true := by decide +kernel
theorem v561 : AB 12 530 3=true := by decide +kernel
theorem v562 : AB 12 533 3=true := by decide +kernel
theorem v563 : AB 12 536 3=true := by decide +kernel
theorem v564 : AB 12 539 3=true := by decide +kernel
theorem v565 : AB 12 542 3=true := by decide +kernel
theorem v566 : AB 12 545 3=true := by decide +kernel
theorem v567 : AB 12 548 3=true := by decide +kernel
theorem v568 : AB 12 551 3=true := by decide +kernel
theorem v569 : AB 12 554 3=true := by decide +kernel
theorem v570 : AB 12 557 3=true := by decide +kernel
theorem v571 : AB 12 560 3=true := by decide +kernel
theorem v572 : AB 12 563 3=true := by decide +kernel
theorem v573 : AB 12 566 3=true := by decide +kernel
theorem v574 : AB 12 569 3=true := by decide +kernel
theorem v575 : AB 12 572 3=true := by decide +kernel
theorem v576 : AB 12 575 3=true := by decide +kernel
theorem v577 : AB 12 578 3=true := by decide +kernel
theorem v578 : AB 12 581 3=true := by decide +kernel
theorem v579 : AB 12 584 3=true := by decide +kernel
theorem v580 : AB 12 587 3=true := by decide +kernel
theorem v581 : AB 12 590 3=true := by decide +kernel
theorem v582 : AB 12 593 3=true := by decide +kernel
theorem v583 : AB 12 596 3=true := by decide +kernel
theorem v584 : AB 12 599 3=true := by decide +kernel
theorem v585 : AB 12 602 3=true := by decide +kernel
theorem v586 : AB 12 605 3=true := by decide +kernel
theorem v587 : AB 12 608 3=true := by decide +kernel
theorem v588 : AB 12 611 3=true := by decide +kernel
theorem v589 : AB 12 614 3=true := by decide +kernel
theorem v590 : AB 12 617 3=true := by decide +kernel
theorem v591 : AB 12 620 3=true := by decide +kernel
theorem v592 : AB 12 623 3=true := by decide +kernel
theorem v593 : AB 12 626 3=true := by decide +kernel
theorem v594 : AB 12 629 3=true := by decide +kernel
theorem v595 : AB 12 632 3=true := by decide +kernel
theorem v596 : AB 12 635 3=true := by decide +kernel
theorem v597 : AB 12 638 3=true := by decide +kernel
theorem v598 : AB 12 641 3=true := by decide +kernel
theorem v599 : AB 12 644 3=true := by decide +kernel
theorem v600 : AB 12 647 3=true := by decide +kernel
theorem v601 : AB 12 650 3=true := by decide +kernel
theorem v602 : AB 12 653 3=true := by decide +kernel
theorem v603 : AB 12 656 1=true := by decide +kernel
theorem v604 : AB 12 657 1=true := by decide +kernel
theorem v605 : AB 12 658 1=true := by decide +kernel
theorem v606 : AB 12 659 1=true := by decide +kernel
theorem v607 : AB 12 660 1=true := by decide +kernel
theorem v608 : AB 12 661 1=true := by decide +kernel
theorem v609 : AB 12 662 1=true := by decide +kernel
theorem v610 : AB 12 663 1=true := by decide +kernel
theorem v611 : AB 12 664 1=true := by decide +kernel
theorem v612 : AB 12 665 1=true := by decide +kernel
theorem v613 : AB 12 666 1=true := by decide +kernel
theorem v614 : AB 12 667 1=true := by decide +kernel
theorem v615 : AB 12 668 1=true := by decide +kernel
theorem v616 : AB 12 669 1=true := by decide +kernel
theorem v617 : AB 12 670 1=true := by decide +kernel
theorem v618 : AB 12 671 1=true := by decide +kernel
theorem v619 : AB 12 672 1=true := by decide +kernel
theorem v620 : AB 12 673 1=true := by decide +kernel
theorem v621 : AB 12 674 1=true := by decide +kernel
theorem v622 : AB 12 675 1=true := by decide +kernel
theorem v623 : AB 12 676 1=true := by decide +kernel
theorem v624 : AB 12 677 1=true := by decide +kernel
theorem v625 : AB 12 678 1=true := by decide +kernel
theorem v626 : AB 12 679 1=true := by decide +kernel
theorem v627 : AB 12 680 1=true := by decide +kernel
theorem v628 : AB 12 681 1=true := by decide +kernel
theorem v629 : AB 12 682 1=true := by decide +kernel
theorem v630 : AB 12 683 1=true := by decide +kernel
theorem v631 : AB 12 684 1=true := by decide +kernel
theorem v632 : AB 12 685 1=true := by decide +kernel
theorem v633 : AB 12 686 1=true := by decide +kernel
theorem v634 : AB 12 687 1=true := by decide +kernel
theorem v635 : AB 12 688 1=true := by decide +kernel
theorem v636 : AB 12 689 1=true := by decide +kernel
theorem v637 : AB 12 690 1=true := by decide +kernel
theorem v638 : AB 12 691 1=true := by decide +kernel
theorem v639 : AB 12 692 1=true := by decide +kernel
theorem v640 : AB 12 693 1=true := by decide +kernel
theorem v641 : AB 12 694 1=true := by decide +kernel
theorem v642 : AB 12 695 1=true := by decide +kernel
theorem v643 : AB 12 696 1=true := by decide +kernel
theorem v644 : AB 12 697 1=true := by decide +kernel
theorem v645 : AB 12 698 1=true := by decide +kernel
theorem v646 : AB 12 699 1=true := by decide +kernel
theorem v647 : AB 12 700 1=true := by decide +kernel
theorem v648 : AB 12 701 1=true := by decide +kernel
theorem v649 : AB 12 702 1=true := by decide +kernel
theorem v650 : AB 12 703 1=true := by decide +kernel
theorem v651 : AB 12 704 1=true := by decide +kernel
theorem v652 : AB 12 705 1=true := by decide +kernel
theorem v653 : AB 12 706 1=true := by decide +kernel
theorem v654 : AB 12 707 1=true := by decide +kernel
theorem v655 : AB 12 708 1=true := by decide +kernel
theorem v656 : AB 12 709 1=true := by decide +kernel
theorem v657 : AB 12 710 1=true := by decide +kernel
theorem v658 : AB 12 711 1=true := by decide +kernel
theorem v659 : AB 12 712 1=true := by decide +kernel
theorem v660 : AB 12 713 1=true := by decide +kernel
theorem v661 : AB 12 714 1=true := by decide +kernel
theorem v662 : AB 12 715 1=true := by decide +kernel
theorem v663 : AB 12 716 1=true := by decide +kernel
theorem v664 : AB 12 717 1=true := by decide +kernel
theorem v665 : AB 12 718 1=true := by decide +kernel
theorem v666 : AB 12 719 1=true := by decide +kernel
theorem v667 : AB 12 720 1=true := by decide +kernel
theorem v668 : AB 12 721 1=true := by decide +kernel
theorem v669 : AB 12 722 1=true := by decide +kernel
theorem v670 : AB 12 723 1=true := by decide +kernel
theorem v671 : AB 12 724 1=true := by decide +kernel
theorem v672 : AB 12 725 1=true := by decide +kernel
theorem v673 : AB 12 726 1=true := by decide +kernel
theorem v674 : AB 12 727 1=true := by decide +kernel
theorem v675 : AB 12 728 1=true := by decide +kernel
theorem v676 : AB 12 729 1=true := by decide +kernel
theorem v677 : AB 12 730 1=true := by decide +kernel
theorem v678 : AB 12 731 1=true := by decide +kernel
theorem v679 : AB 12 732 1=true := by decide +kernel
theorem v680 : AB 12 733 1=true := by decide +kernel
theorem v681 : AB 12 734 1=true := by decide +kernel
theorem v682 : AB 12 735 1=true := by decide +kernel
theorem v683 : AB 12 736 1=true := by decide +kernel
theorem v684 : AB 12 737 1=true := by decide +kernel
theorem v685 : AB 12 738 1=true := by decide +kernel
theorem v686 : AB 12 739 1=true := by decide +kernel
theorem v687 : AB 12 740 1=true := by decide +kernel
theorem v688 : AB 12 741 1=true := by decide +kernel
theorem v689 : AB 12 742 1=true := by decide +kernel
theorem v690 : AB 12 743 1=true := by decide +kernel
theorem v691 : AB 12 744 1=true := by decide +kernel
theorem v692 : AB 12 745 1=true := by decide +kernel
theorem v693 : AB 12 746 1=true := by decide +kernel
theorem v694 : AB 12 747 1=true := by decide +kernel
theorem v695 : AB 12 748 1=true := by decide +kernel
theorem v696 : AB 12 749 1=true := by decide +kernel
theorem v697 : AB 12 750 1=true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem level12 : AB 12 0 751=true := (@J12 0 413 338 (@J12 0 149 264 (@J12 0 43 106 (@J12 0 21 22 (@J12 0 10 11 (@J12 0 5 5 (@J12 0 2 3 (@J12 0 1 1 v347 v348) (@J12 2 1 2 v349 (@J12 3 1 1 v350 v351))) (@J12 5 2 3 (@J12 5 1 1 v352 v353) (@J12 7 1 2 v354 (@J12 8 1 1 v355 v356)))) (@J12 10 5 6 (@J12 10 2 3 (@J12 10 1 1 v357 v358) (@J12 12 1 2 v359 (@J12 13 1 1 v360 v361))) (@J12 15 3 3 (@J12 15 1 2 v362 (@J12 16 1 1 v363 v364)) (@J12 18 1 2 v365 (@J12 19 1 1 v366 v367))))) (@J12 21 11 11 (@J12 21 5 6 (@J12 21 2 3 (@J12 21 1 1 v368 v369) (@J12 23 1 2 v370 (@J12 24 1 1 v371 v372))) (@J12 26 3 3 (@J12 26 1 2 v373 (@J12 27 1 1 v374 v375)) (@J12 29 1 2 v376 (@J12 30 1 1 v377 v378)))) (@J12 32 5 6 (@J12 32 2 3 (@J12 32 1 1 v379 v380) (@J12 34 1 2 v381 (@J12 35 1 1 v382 v383))) (@J12 37 3 3 (@J12 37 1 2 v384 (@J12 38 1 1 v385 v386)) (@J12 40 1 2 v387 (@J12 41 1 1 v388 v389)))))) (@J12 43 40 66 (@J12 43 11 29 (@J12 43 5 6 (@J12 43 2 3 (@J12 43 1 1 v390 v391) (@J12 45 1 2 v392 (@J12 46 1 1 v393 v394))) (@J12 48 3 3 (@J12 48 1 2 v395 (@J12 49 1 1 v396 v397)) (@J12 51 1 2 v398 (@J12 52 1 1 v399 v400)))) (@J12 54 11 18 (@J12 54 2 9 (@J12 54 1 1 v401 v402) (@J12 56 3 6 v403 (@J12 59 3 3 v404 v405))) (@J12 65 9 9 (@J12 65 3 6 v406 (@J12 68 3 3 v407 v408)) (@J12 74 3 6 v409 (@J12 77 3 3 v410 v411))))) (@J12 83 33 33 (@J12 83 15 18 (@J12 83 6 9 (@J12 83 3 3 v412 v413) (@J12 89 3 6 v414 (@J12 92 3 3 v415 v416))) (@J12 98 9 9 (@J12 98 3 6 v417 (@J12 101 3 3 v418 v419)) (@J12 107 3 6 v420 (@J12 110 3 3 v421 v422)))) (@J12 116 15 18 (@J12 116 6 9 (@J12 116 3 3 v423 v424) (@J12 122 3 6 v425 (@J12 125 3 3 v426 v427))) (@J12 131 9 9 (@J12 131 3 6 v428 (@J12 134 3 3 v429 v430)) (@J12 140 3 6 v431 (@J12 143 3 3 v432 v433))))))) (@J12 149 132 132 (@J12 149 66 66 (@J12 149 33 33 (@J12 149 15 18 (@J12 149 6 9 (@J12 149 3 3 v434 v435) (@J12 155 3 6 v436 (@J12 158 3 3 v437 v438))) (@J12 164 9 9 (@J12 164 3 6 v439 (@J12 167 3 3 v440 v441)) (@J12 173 3 6 v442 (@J12 176 3 3 v443 v444)))) (@J12 182 15 18 (@J12 182 6 9 (@J12 182 3 3 v445 v446) (@J12 188 3 6 v447 (@J12 191 3 3 v448 v449))) (@J12 197 9 9 (@J12 197 3 6 v450 (@J12 200 3 3 v451 v452)) (@J12 206 3 6 v453 (@J12 209 3 3 v454 v455))))) (@J12 215 33 33 (@J12 215 15 18 (@J12 215 6 9 (@J12 215 3 3 v456 v457) (@J12 221 3 6 v458 (@J12 224 3 3 v459 v460))) (@J12 230 9 9 (@J12 230 3 6 v461 (@J12 233 3 3 v462 v463)) (@J12 239 3 6 v464 (@J12 242 3 3 v465 v466)))) (@J12 248 15 18 (@J12 248 6 9 (@J12 248 3 3 v467 v468) (@J12 254 3 6 v469 (@J12 257 3 3 v470 v471))) (@J12 263 9 9 (@J12 263 3 6 v472 (@J12 266 3 3 v473 v474)) (@J12 272 3 6 v475 (@J12 275 3 3 v476 v477)))))) (@J12 281 66 66 (@J12 281 33 33 (@J12 281 15 18 (@J12 281 6 9 (@J12 281 3 3 v478 v479) (@J12 287 3 6 v480 (@J12 290 3 3 v481 v482))) (@J12 296 9 9 (@J12 296 3 6 v483 (@J12 299 3 3 v484 v485)) (@J12 305 3 6 v486 (@J12 308 3 3 v487 v488)))) (@J12 314 15 18 (@J12 314 6 9 (@J12 314 3 3 v489 v490) (@J12 320 3 6 v491 (@J12 323 3 3 v492 v493))) (@J12 329 9 9 (@J12 329 3 6 v494 (@J12 332 3 3 v495 v496)) (@J12 338 3 6 v497 (@J12 341 3 3 v498 v499))))) (@J12 347 33 33 (@J12 347 15 18 (@J12 347 6 9 (@J12 347 3 3 v500 v501) (@J12 353 3 6 v502 (@J12 356 3 3 v503 v504))) (@J12 362 9 9 (@J12 362 3 6 v505 (@J12 365 3 3 v506 v507)) (@J12 371 3 6 v508 (@J12 374 3 3 v509 v510)))) (@J12 380 15 18 (@J12 380 6 9 (@J12 380 3 3 v511 v512) (@J12 386 3 6 v513 (@J12 389 3 3 v514 v515))) (@J12 395 9 9 (@J12 395 3 6 v516 (@J12 398 3 3 v517 v518)) (@J12 404 3 6 v519 (@J12 407 3 3 v520 v521)))))))) (@J12 413 250 88 (@J12 413 132 118 (@J12 413 66 66 (@J12 413 33 33 (@J12 413 15 18 (@J12 413 6 9 (@J12 413 3 3 v522 v523) (@J12 419 3 6 v524 (@J12 422 3 3 v525 v526))) (@J12 428 9 9 (@J12 428 3 6 v527 (@J12 431 3 3 v528 v529)) (@J12 437 3 6 v530 (@J12 440 3 3 v531 v532)))) (@J12 446 15 18 (@J12 446 6 9 (@J12 446 3 3 v533 v534) (@J12 452 3 6 v535 (@J12 455 3 3 v536 v537))) (@J12 461 9 9 (@J12 461 3 6 v538 (@J12 464 3 3 v539 v540)) (@J12 470 3 6 v541 (@J12 473 3 3 v542 v543))))) (@J12 479 33 33 (@J12 479 15 18 (@J12 479 6 9 (@J12 479 3 3 v544 v545) (@J12 485 3 6 v546 (@J12 488 3 3 v547 v548))) (@J12 494 9 9 (@J12 494 3 6 v549 (@J12 497 3 3 v550 v551)) (@J12 503 3 6 v552 (@J12 506 3 3 v553 v554)))) (@J12 512 15 18 (@J12 512 6 9 (@J12 512 3 3 v555 v556) (@J12 518 3 6 v557 (@J12 521 3 3 v558 v559))) (@J12 527 9 9 (@J12 527 3 6 v560 (@J12 530 3 3 v561 v562)) (@J12 536 3 6 v563 (@J12 539 3 3 v564 v565)))))) (@J12 545 66 52 (@J12 545 33 33 (@J12 545 15 18 (@J12 545 6 9 (@J12 545 3 3 v566 v567) (@J12 551 3 6 v568 (@J12 554 3 3 v569 v570))) (@J12 560 9 9 (@J12 560 3 6 v571 (@J12 563 3 3 v572 v573)) (@J12 569 3 6 v574 (@J12 572 3 3 v575 v576)))) (@J12 578 15 18 (@J12 578 6 9 (@J12 578 3 3 v577 v578) (@J12 584 3 6 v579 (@J12 587 3 3 v580 v581))) (@J12 593 9 9 (@J12 593 3 6 v582 (@J12 596 3 3 v583 v584)) (@J12 602 3 6 v585 (@J12 605 3 3 v586 v587))))) (@J12 611 33 19 (@J12 611 15 18 (@J12 611 6 9 (@J12 611 3 3 v588 v589) (@J12 617 3 6 v590 (@J12 620 3 3 v591 v592))) (@J12 626 9 9 (@J12 626 3 6 v593 (@J12 629 3 3 v594 v595)) (@J12 635 3 6 v596 (@J12 638 3 3 v597 v598)))) (@J12 644 13 6 (@J12 644 6 7 (@J12 644 3 3 v599 v600) (@J12 650 3 4 v601 (@J12 653 3 1 v602 v603))) (@J12 657 3 3 (@J12 657 1 2 v604 (@J12 658 1 1 v605 v606)) (@J12 660 1 2 v607 (@J12 661 1 1 v608 v609))))))) (@J12 663 44 44 (@J12 663 22 22 (@J12 663 11 11 (@J12 663 5 6 (@J12 663 2 3 (@J12 663 1 1 v610 v611) (@J12 665 1 2 v612 (@J12 666 1 1 v613 v614))) (@J12 668 3 3 (@J12 668 1 2 v615 (@J12 669 1 1 v616 v617)) (@J12 671 1 2 v618 (@J12 672 1 1 v619 v620)))) (@J12 674 5 6 (@J12 674 2 3 (@J12 674 1 1 v621 v622) (@J12 676 1 2 v623 (@J12 677 1 1 v624 v625))) (@J12 679 3 3 (@J12 679 1 2 v626 (@J12 680 1 1 v627 v628)) (@J12 682 1 2 v629 (@J12 683 1 1 v630 v631))))) (@J12 685 11 11 (@J12 685 5 6 (@J12 685 2 3 (@J12 685 1 1 v632 v633) (@J12 687 1 2 v634 (@J12 688 1 1 v635 v636))) (@J12 690 3 3 (@J12 690 1 2 v637 (@J12 691 1 1 v638 v639)) (@J12 693 1 2 v640 (@J12 694 1 1 v641 v642)))) (@J12 696 5 6 (@J12 696 2 3 (@J12 696 1 1 v643 v644) (@J12 698 1 2 v645 (@J12 699 1 1 v646 v647))) (@J12 701 3 3 (@J12 701 1 2 v648 (@J12 702 1 1 v649 v650)) (@J12 704 1 2 v651 (@J12 705 1 1 v652 v653)))))) (@J12 707 22 22 (@J12 707 11 11 (@J12 707 5 6 (@J12 707 2 3 (@J12 707 1 1 v654 v655) (@J12 709 1 2 v656 (@J12 710 1 1 v657 v658))) (@J12 712 3 3 (@J12 712 1 2 v659 (@J12 713 1 1 v660 v661)) (@J12 715 1 2 v662 (@J12 716 1 1 v663 v664)))) (@J12 718 5 6 (@J12 718 2 3 (@J12 718 1 1 v665 v666) (@J12 720 1 2 v667 (@J12 721 1 1 v668 v669))) (@J12 723 3 3 (@J12 723 1 2 v670 (@J12 724 1 1 v671 v672)) (@J12 726 1 2 v673 (@J12 727 1 1 v674 v675))))) (@J12 729 11 11 (@J12 729 5 6 (@J12 729 2 3 (@J12 729 1 1 v676 v677) (@J12 731 1 2 v678 (@J12 732 1 1 v679 v680))) (@J12 734 3 3 (@J12 734 1 2 v681 (@J12 735 1 1 v682 v683)) (@J12 737 1 2 v684 (@J12 738 1 1 v685 v686)))) (@J12 740 5 6 (@J12 740 2 3 (@J12 740 1 1 v687 v688) (@J12 742 1 2 v689 (@J12 743 1 1 v690 v691))) (@J12 745 3 3 (@J12 745 1 2 v692 (@J12 746 1 1 v693 v694)) (@J12 748 1 2 v695 (@J12 749 1 1 v696 v697)))))))))
theorem v698 : AB 13 0 1=true := by decide +kernel
theorem v699 : AB 13 1 1=true := by decide +kernel
theorem v700 : AB 13 2 1=true := by decide +kernel
theorem v701 : AB 13 3 1=true := by decide +kernel
theorem v702 : AB 13 4 1=true := by decide +kernel
theorem v703 : AB 13 5 1=true := by decide +kernel
theorem v704 : AB 13 6 1=true := by decide +kernel
theorem v705 : AB 13 7 1=true := by decide +kernel
theorem v706 : AB 13 8 1=true := by decide +kernel
theorem v707 : AB 13 9 1=true := by decide +kernel
theorem v708 : AB 13 10 1=true := by decide +kernel
theorem v709 : AB 13 11 1=true := by decide +kernel
theorem v710 : AB 13 12 1=true := by decide +kernel
theorem v711 : AB 13 13 1=true := by decide +kernel
theorem v712 : AB 13 14 1=true := by decide +kernel
theorem v713 : AB 13 15 1=true := by decide +kernel
theorem v714 : AB 13 16 1=true := by decide +kernel
theorem v715 : AB 13 17 1=true := by decide +kernel
theorem v716 : AB 13 18 1=true := by decide +kernel
theorem v717 : AB 13 19 1=true := by decide +kernel
theorem v718 : AB 13 20 1=true := by decide +kernel
theorem v719 : AB 13 21 1=true := by decide +kernel
theorem v720 : AB 13 22 1=true := by decide +kernel
theorem v721 : AB 13 23 1=true := by decide +kernel
theorem v722 : AB 13 24 1=true := by decide +kernel
theorem v723 : AB 13 25 1=true := by decide +kernel
theorem v724 : AB 13 26 1=true := by decide +kernel
theorem v725 : AB 13 27 1=true := by decide +kernel
theorem v726 : AB 13 28 1=true := by decide +kernel
theorem v727 : AB 13 29 1=true := by decide +kernel
theorem v728 : AB 13 30 1=true := by decide +kernel
theorem v729 : AB 13 31 1=true := by decide +kernel
theorem v730 : AB 13 32 1=true := by decide +kernel
theorem v731 : AB 13 33 1=true := by decide +kernel
theorem v732 : AB 13 34 1=true := by decide +kernel
theorem v733 : AB 13 35 1=true := by decide +kernel
theorem v734 : AB 13 36 1=true := by decide +kernel
theorem v735 : AB 13 37 1=true := by decide +kernel
theorem v736 : AB 13 38 1=true := by decide +kernel
theorem v737 : AB 13 39 1=true := by decide +kernel
theorem v738 : AB 13 40 1=true := by decide +kernel
theorem v739 : AB 13 41 1=true := by decide +kernel
theorem v740 : AB 13 42 1=true := by decide +kernel
theorem v741 : AB 13 43 1=true := by decide +kernel
theorem v742 : AB 13 44 1=true := by decide +kernel
theorem v743 : AB 13 45 1=true := by decide +kernel
theorem v744 : AB 13 46 1=true := by decide +kernel
theorem v745 : AB 13 47 1=true := by decide +kernel
theorem v746 : AB 13 48 1=true := by decide +kernel
theorem v747 : AB 13 49 1=true := by decide +kernel
theorem v748 : AB 13 50 1=true := by decide +kernel
theorem v749 : AB 13 51 1=true := by decide +kernel
theorem v750 : AB 13 52 1=true := by decide +kernel
theorem v751 : AB 13 53 1=true := by decide +kernel
theorem v752 : AB 13 54 1=true := by decide +kernel
theorem v753 : AB 13 55 1=true := by decide +kernel
theorem v754 : AB 13 56 1=true := by decide +kernel
theorem v755 : AB 13 57 1=true := by decide +kernel
theorem v756 : AB 13 58 1=true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem level13 : AB 13 0 59=true := (@J13 0 29 30 (@J13 0 14 15 (@J13 0 7 7 (@J13 0 3 4 (@J13 0 1 2 v698 (@J13 1 1 1 v699 v700)) (@J13 3 2 2 (@J13 3 1 1 v701 v702) (@J13 5 1 1 v703 v704))) (@J13 7 3 4 (@J13 7 1 2 v705 (@J13 8 1 1 v706 v707)) (@J13 10 2 2 (@J13 10 1 1 v708 v709) (@J13 12 1 1 v710 v711)))) (@J13 14 7 8 (@J13 14 3 4 (@J13 14 1 2 v712 (@J13 15 1 1 v713 v714)) (@J13 17 2 2 (@J13 17 1 1 v715 v716) (@J13 19 1 1 v717 v718))) (@J13 21 4 4 (@J13 21 2 2 (@J13 21 1 1 v719 v720) (@J13 23 1 1 v721 v722)) (@J13 25 2 2 (@J13 25 1 1 v723 v724) (@J13 27 1 1 v725 v726))))) (@J13 29 15 15 (@J13 29 7 8 (@J13 29 3 4 (@J13 29 1 2 v727 (@J13 30 1 1 v728 v729)) (@J13 32 2 2 (@J13 32 1 1 v730 v731) (@J13 34 1 1 v732 v733))) (@J13 36 4 4 (@J13 36 2 2 (@J13 36 1 1 v734 v735) (@J13 38 1 1 v736 v737)) (@J13 40 2 2 (@J13 40 1 1 v738 v739) (@J13 42 1 1 v740 v741)))) (@J13 44 7 8 (@J13 44 3 4 (@J13 44 1 2 v742 (@J13 45 1 1 v743 v744)) (@J13 47 2 2 (@J13 47 1 1 v745 v746) (@J13 49 1 1 v747 v748))) (@J13 51 4 4 (@J13 51 2 2 (@J13 51 1 1 v749 v750) (@J13 53 1 1 v751 v752)) (@J13 55 2 2 (@J13 55 1 1 v753 v754) (@J13 57 1 1 v755 v756))))))
theorem v757 : AB 14 0 1=true := by decide +kernel
theorem v758 : AB 14 1 1=true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem level14 : AB 14 0 2=true := (@J14 0 1 1 v757 v758)
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
    Limited graph 14 0 (inputs ++ [bin true (inputs.getD 0 zero) (inputs.getD 6 zero)]).toFinset ∧
      Limited graph 14 0 inputs.toFinset := by
  let g := signedCertificate
  have checked := hybridForest_all testPacked testPackedOK rankCount g 14 (boundsBefore known251) (before_sound known251 valid251) geometry pairChecks tables
  have tgt : targetOf g.base = graph := by decide +kernel
  constructor
  · have h := checked 14 (by decide) 1 (by decide)
    have budget : g.budget 14 1 = 0 := by decide +kernel
    have eq : sameWords (stateSet g.base 14 1)
        (inputs ++ [bin true (inputs.getD 0 zero) (inputs.getD 6 zero)]) = true := by decide +kernel
    rwa [tgt,budget,sameWords_sound eq] at h
  · have h := checked 14 (by decide) 0 (by decide)
    have budget : g.budget 14 0 = 0 := by decide +kernel
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
      bit r graph = targetFn (sample r) := by
  intro r
  constructor
  · unfold augmentedInputs
    simp only [List.map_append,List.map_cons,List.map_nil]
    congr 1
    simp [firstOr,sample,bit,bin]
  · have hg : graph = graphGoal 511 := by decide +kernel
    rw [hg]
    simp [graphGoal,vertex,bit,targetFn,edge,sample]
    rfl

def essentialRow (i : Fin 9) : Row :=
  Fin.ofNat 512 (([96, 1, 2, 4, 1, 1, 257, 4, 8] : List Nat).getD i.val 0)

def toggleEssentialRow (i : Fin 9) : Row :=
  Fin.ofNat 512 ((essentialRow i).val ||| (1 <<< i.val))

set_option maxHeartbeats 0 in
theorem essentialRaw :
    ∀ i : Fin 9, (bit (essentialRow i) graph != bit (toggleEssentialRow i) graph) &&
      (augmentedInputs.all fun w => w == inputs.getD i.val zero ||
        bit (essentialRow i) w == bit (toggleEssentialRow i) w) = true := by decide +kernel

theorem noTail (C : Circuit) (mono : Monotone2 C) (small : C.size ≤ 14)
    (correct : ∀ x : Fin 9 → Bool,
      C.eval (List.ofFn x ++ [x 0 || x 6]) = targetFn x) : False := by
  have outputTable : (execute C.gates augmentedInputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    let r : Row := ⟨i,hi⟩
    change bit r _ = bit r graph
    rw [← b_read, execute_bits _ _ _ (fun g hg => (show g.op = .and ∨ g.op = .or from (mono g hg).1).imp_right Or.inl),
      (rowSemantics r).1, (rowSemantics r).2]
    exact correct (sample r)
  have supported := get_rep (execute C.gates augmentedInputs) C.output
  rw [outputTable] at supported
  obtain ⟨k,S,le,run,sub⟩ := extractMono C.gates augmentedInputs mono graph_proper
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
    exact O1677.checkedRoots.1 k 0 bound (by decide) (eq ▸ run)
  · have eq : S = inputs.toFinset := by
      apply Finset.Subset.antisymm _ allRaw
      intro w hw
      rcases List.mem_append.mp (sub w hw) with hr | he
      · exact List.mem_toFinset.mpr hr
      · exact (h (List.mem_singleton.mp he ▸ hw)).elim
    exact O1677.checkedRoots.2 k 0 bound (by decide) (eq ▸ run)

end PEqualNP.Outside.L_meta_4362
theorem PEqualNP.Outside.L_meta_4362 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → x1.size = (14 : ℕ) → x1.output = (23 : ℕ) → List.countP (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => (if x5.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x5.inputs else x5.inputs).any fun (x6 : ℕ) => Decidable.decide (x6 = (6 : ℕ))) x1.gates = (1 : ℕ) → ∃ (x6 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ))]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro C mono size _ _
  by_contra! correct
  exact PEqualNP.Outside.L_meta_4362.noTail C mono (Nat.le_of_eq size) correct
