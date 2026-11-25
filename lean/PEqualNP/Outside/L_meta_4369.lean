import Mathlib
import PEqualNP.Defs

-- Adapted from PEqualNP.Outside.L_meta_3091 by Vlad Grigorescu (pull request 8465, Apache License 2.0).
-- The statement here is a corollary: it has the same hypotheses plus extra ones that are not needed.

namespace PEqualNP.Outside.L_meta_4369
namespace CP
open PEqualNP.CircuitLowerBounds
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g=>w ++ [g.op.eval (g.inputs.map fun i=>w.getD i false)]) w
theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w=wiresFrom gs' (wiresFrom gs w):=by
  simp [wiresFrom,List.foldl_append]
theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool,wiresFrom gs w=w ++ t ∧ t.length=gs.length:=by
  induction gs with
  | nil=>intro w;exact ⟨[],by simp [wiresFrom],rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t,ht,hl⟩:=ih (w ++ [g.op.eval (g.inputs.map fun i=>w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i=>w.getD i false) :: t,?_,by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i=>w.getD i false)]):=rfl
    rw [this,ht];simp
theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length=w.length + gs.length:=by
  obtain ⟨t,ht,hl⟩:=wiresFrom_prefix gs w
  rw [ht];simp [hl]
theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false=w.getD i false:=by
  obtain ⟨t,ht,_⟩:=wiresFrom_prefix gs w
  rw [ht,List.getD_append _ _ _ _ h]
def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2
end CP
namespace CP
open PEqualNP.CircuitLowerBounds
variable {n : ℕ}
theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d=L.getD j d:=by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp;omega),List.getD_eq_default _ _ (by omega)]
theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d=S:=by
  simp
end CP
namespace CP
open PEqualNP.CircuitLowerBounds
def NOk (g : Gate) : Prop:=Ok g ∧ (g.op=GateOp.not → g.inputs.length ≤ 1)
abbrev Stat:=Bool ⊕ ℕ
def statVal (w : List Bool) : Stat → Bool
  | Sum.inl c=>c
  | Sum.inr j=>w.getD j false
def StatValid (m : ℕ) : Stat → Prop
  | Sum.inl _=>True
  | Sum.inr j=>j < m
def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | []=>(none,Sum.inl true)
  | Sum.inl c :: _=>(none,Sum.inl (!c))
  | Sum.inr j :: _=>(some ⟨GateOp.not,[j]⟩,Sum.inr m)
def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | []=>(none,Sum.inl true)
  | [Sum.inl c]=>(none,Sum.inl c)
  | [Sum.inr j]=>(none,Sum.inr j)
  | [Sum.inl c,Sum.inl d]=>(none,Sum.inl (c&&d))
  | [Sum.inl c,Sum.inr j]=>(none,bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j,Sum.inl c]=>(none,bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j,Sum.inr k]=>(some ⟨GateOp.and,[j,k]⟩,Sum.inr m)
  | _=>(none,Sum.inl false)
def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | []=>(none,Sum.inl false)
  | [Sum.inl c]=>(none,Sum.inl c)
  | [Sum.inr j]=>(none,Sum.inr j)
  | [Sum.inl c,Sum.inl d]=>(none,Sum.inl (c||d))
  | [Sum.inl c,Sum.inr j]=>(none,bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j,Sum.inl c]=>(none,bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j,Sum.inr k]=>(some ⟨GateOp.or,[j,k]⟩,Sum.inr m)
  | _=>(none,Sum.inl false)
def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and=>simpAnd m ins
  | GateOp.or=>simpOr m ins
  | GateOp.not=>simpNot m ins
  | _=>(none,Sum.inl false)
theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op=GateOp.and ∨ op=GateOp.or ∨ op=GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op=GateOp.not → ins.length ≤ 1) (hc : ∃ c,Sum.inl c ∈ ins) :
    (simplify op m ins).1=none:=by
  obtain ⟨c,hc⟩:=hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨d,l⟩⟩⟩<;>(try cases a)<;>(try cases b) <;>
      simp_all [simplify,simpAnd]
  · rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨d,l⟩⟩⟩<;>(try cases a)<;>(try cases b) <;>
      simp_all [simplify,simpOr]
  · have:=hnot rfl
    rcases ins with _ | ⟨a,_ | ⟨b,l⟩⟩<;>(try cases a)<;>simp_all [simplify,simpNot]
theorem simplify_sound (op : GateOp) (hop : op=GateOp.and ∨ op=GateOp.or ∨ op=GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins,StatValid w.length s) :
    StatValid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
    statVal (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2
      = op.eval (ins.map (statVal w)):=by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨d,l⟩⟩⟩
    · simp [simplify,simpAnd,StatValid,statVal,GateOp.eval]
    · cases a<;>simp_all [simplify,simpAnd,StatValid,statVal,GateOp.eval,wiresFrom]
    · cases a<;>cases b<;>(try rename_i c e;cases c)<;>(try cases e) <;>
        simp_all [simplify,simpAnd,StatValid,statVal,GateOp.eval,wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨d,l⟩⟩⟩
    · simp [simplify,simpOr,StatValid,statVal,GateOp.eval]
    · cases a<;>simp_all [simplify,simpOr,StatValid,statVal,GateOp.eval,wiresFrom]
    · cases a<;>cases b<;>(try rename_i c e;cases c)<;>(try cases e) <;>
        simp_all [simplify,simpOr,StatValid,statVal,GateOp.eval,wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a,l⟩
    · simp [simplify,simpNot,StatValid,statVal,GateOp.eval]
    · cases a<;>simp_all [simplify,simpNot,StatValid,statVal,GateOp.eval,wiresFrom]
def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i=>acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i=>acc.1.getD i (Sum.inl false))).1.toList)
def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc
theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length=k) :
    (L ++ [S]).getD k d=S:=by
  subst h;simp
theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1:=by
  cases o<;>simp
theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length:=by
  induction gs with
  | nil=>intro acc;simp [elim]
  | cons g gs ih =>
    intro acc
    have h1:=ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1:=by
      simp only [elimStep,List.length_append]
      have:=toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i=>acc.1.getD i (Sum.inl false))).1
      omega
    have h3 : elim n (g :: gs) acc=elim n gs (elimStep n acc g):=rfl
    rw [h3,List.length_cons];omega
theorem statValid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat,StatValid m s → StatValid m' s
  | Sum.inl _,_=>trivial
  | Sum.inr _,hj=>lt_of_lt_of_le hj h
theorem statVal_append (w t : List Bool) : ∀ s : Stat,StatValid w.length s →
    statVal (w ++ t) s=statVal w s
  | Sum.inl _,_=>rfl
  | Sum.inr _,hj=>List.getD_append _ _ _ _ hj
def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length=w.length ∧ ∀ i : ℕ,
    StatValid (n + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 y) (acc.1.getD i (Sum.inl false))=w.getD i false
theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length=n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate),(∀ g ∈ gs,Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc):=by
  induction gs with
  | nil=>intro w acc _ h;exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i=>w.getD i false)]) (elimStep n acc g)
      (fun g' hg'=>hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl,hi⟩:=h
    set w':=wiresFrom acc.2 y with hw'
    have lw' : w'.length=n + acc.2.length:=by rw [hw',length_wiresFrom,hy]
    set ins:=g.inputs.map fun i=>acc.1.getD i (Sum.inl false) with hins
    have hgok:=hok g List.mem_cons_self
    have hs:=simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a,_,rfl⟩:=List.mem_map.1 hs
        rw [lw'];exact (hi a).1)
    rw [lw'] at hs
    set r:=simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (statVal w')=g.inputs.map fun i=>w.getD i false:=by
      rw [hins,List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y=wiresFrom r.1.toList w':=by
      rw [wiresFrom_append]
    obtain ⟨t,ht,htl⟩:=wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep,hl],?_⟩
    intro i
    show StatValid (n + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) ∧
      statVal (wiresFrom (acc.2 ++ r.1.toList) y) ((acc.1 ++ [r.2]).getD i (Sum.inl false))=_
    rw [hnew,List.length_append,← Nat.add_assoc]
    by_cases hil : i=acc.1.length
    · subst hil
      rw [getD_snoc_eq,hl,getD_snoc_eq]
      exact ⟨hs.1,by rw [hs.2,hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil,getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨statValid_mono (by omega) _ (hi i).1,?_⟩
      rw [ht,statVal_append _ _ _ (by rw [lw'];exact (hi i).1)]
      exact (hi i).2
def isNotGate (op : GateOp) : Bool :=
  match op with
  | .not=>true
  | _=>false
def opCount (test : GateOp → Bool) (gs : List Gate) : ℕ :=
  gs.countP (fun g=>test g.op)
lemma simplify_same_op (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1,g.op=op:=by
  intro g hg
  cases op<;>simp only [simplify] at hg
  · rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩<;>(try cases a)<;>(try cases b) <;>
      simp [simpAnd] at hg<;>(subst hg;rfl)
  · rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩<;>(try cases a)<;>(try cases b) <;>
      simp [simpOr] at hg<;>(subst hg;rfl)
  · rcases ins with _ | ⟨a,l⟩<;>(try cases a) <;>
      simp [simpNot] at hg<;>(subst hg;rfl)
  · simp at hg
  · simp at hg
lemma opCount_append (test : GateOp → Bool) (gs hs : List Gate) :
    opCount test (gs ++ hs)=opCount test gs + opCount test hs:=by
  simp [opCount]
lemma opCount_cons (test : GateOp → Bool) (g : Gate) (gs : List Gate) :
    opCount test (g :: gs)=opCount test gs + (if test g.op then 1 else 0):=by
  by_cases h : test g.op<;>simp [opCount,h]
lemma simplify_opCount_le (test : GateOp → Bool) (op : GateOp) (m : ℕ) (ins : List Stat) :
    opCount test (simplify op m ins).1.toList ≤ (if test op then 1 else 0):=by
  cases h : (simplify op m ins).1 with
  | none=>simp [opCount]
  | some g =>
    have hg : g ∈ (simplify op m ins).1:=by simp [h]
    have he:=simplify_same_op op m ins g hg
    simp [h,opCount_cons,opCount,he]
lemma elim_opCount_le (test : GateOp → Bool) (n : ℕ) (gs : List Gate) :
    ∀ acc : List Stat × List Gate,
      opCount test (elim n gs acc).2 ≤ opCount test acc.2 + opCount test gs:=by
  induction gs with
  | nil=>intro acc;simp [elim,opCount]
  | cons g gs ih =>
    intro acc
    change opCount test (elim n gs (elimStep n acc g)).2 ≤ _
    apply (ih (elimStep n acc g)).trans
    simp only [elimStep,opCount_append,opCount_cons]
    have hb:=simplify_opCount_le test g.op (n + acc.2.length)
       (g.inputs.map fun i=>acc.1.getD i (Sum.inl false))
    omega
def nnC (gs : List Gate) : ℕ :=
  gs.countP (fun g=>!(isNotGate g.op))
lemma elim_nonNotCount (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) :
    nnC (elim n gs acc).2 ≤ nnC acc.2 + nnC gs :=
  elim_opCount_le (fun op=>!(isNotGate op)) n gs acc
end CP
namespace CP
open PEqualNP.CircuitLowerBounds
def CleanGate (m : ℕ) (g : Gate) : Prop :=
  (g.op=GateOp.not ∧ ∃ j,j < m ∧ g.inputs=[j]) ∨
  ((g.op=GateOp.and ∨ g.op=GateOp.or) ∧ ∃ j k,j < m ∧ k < m ∧ g.inputs=[j,k])
def CleanL (m : ℕ) (gs : List Gate) : Prop :=
  ∀ (p : ℕ) (g : Gate),gs[p]?=some g → CleanGate (m + p) g
theorem CleanGate.nok {m : ℕ} {g : Gate} (h : CleanGate m g) : NOk g:=by
  rcases h with ⟨h1,j,_,h2⟩ | ⟨h1 | h1,j,k,_,_,h2⟩
  · refine ⟨⟨?_,?_⟩,?_⟩
    · rw [h1];exact Or.inr (Or.inr rfl)
    · rw [h2];simp
    · intro _;rw [h2];simp
  · refine ⟨⟨?_,?_⟩,?_⟩
    · rw [h1];exact Or.inl rfl
    · rw [h2];simp
    · intro h;rw [h1] at h;cases h
  · refine ⟨⟨?_,?_⟩,?_⟩
    · rw [h1];exact Or.inr (Or.inl rfl)
    · rw [h2];simp
    · intro h;rw [h1] at h;cases h
theorem CleanGate.lt {m : ℕ} {g : Gate} (h : CleanGate m g) : ∀ a ∈ g.inputs,a < m:=by
  intro a ha
  rcases h with ⟨_,j,hj,h2⟩ | ⟨_,j,k,hj,hk,h2⟩
  · rw [h2] at ha
    simp at ha
    subst ha;exact hj
  · rw [h2] at ha
    simp at ha
    rcases ha with rfl | rfl
    · exact hj
    · exact hk
theorem clean_nok (m : ℕ) (gs : List Gate) (h : CleanL m gs) : ∀ g ∈ gs,NOk g:=by
  intro g hg
  obtain ⟨p,hp⟩:=List.mem_iff_getElem?.1 hg
  exact (h p g hp).nok
theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat) (hv : ∀ s ∈ ins,StatValid m s) :
    ∀ g ∈ (simplify op m ins).1,CleanGate m g:=by
  intro g hg
  cases op<;>simp only [simplify] at hg
  · rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩<;>(try cases a)<;>(try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    refine Or.inr ⟨Or.inl rfl,_,_,?_,?_,rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩<;>(try cases a)<;>(try cases b) <;>
      simp [simpOr] at hg
    subst hg
    refine Or.inr ⟨Or.inr rfl,_,_,?_,?_,rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a,l⟩<;>(try cases a)<;>simp [simpNot] at hg
    subst hg
    refine Or.inl ⟨rfl,_,?_,rfl⟩
    exact hv _ List.mem_cons_self
  · simp at hg
  · simp at hg
theorem toList_getElem? {α : Type} (o : Option α) (k : ℕ) (a : α)
    (h : o.toList[k]?=some a) : k=0 ∧ a ∈ o:=by
  cases o with
  | none=>simp at h
  | some b =>
    cases k with
    | zero=>simp at h;simp [h]
    | succ k=>simp at h
theorem clean_elim (n : ℕ) (y : List Bool) (hy : y.length=n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate),(∀ g ∈ gs,Ok g) → Inv n y w acc →
      CleanL n acc.2 → CleanL n (elim n gs acc).2:=by
  induction gs with
  | nil=>intro w acc _ _ h;exact h
  | cons g gs ih =>
    intro w acc hok hinv hcl
    have hinv' : Inv n y (wiresFrom [g] w) (elimStep n acc g) :=
      inv_elim n y hy [g] w acc (fun g' hg'=>hok g' (by simp at hg';simp [hg'])) hinv
    refine ih _ (elimStep n acc g) (fun g' hg'=>hok g' (List.mem_cons_of_mem _ hg')) hinv' ?_
    intro p g' hp
    have hp' : (acc.2 ++ (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i=>acc.1.getD i (Sum.inl false))).1.toList)[p]?=some g':=hp
    by_cases hlt : p < acc.2.length
    · rw [List.getElem?_append_left hlt] at hp'
      exact hcl p g' hp'
    · rw [List.getElem?_append_right (by omega)] at hp'
      obtain ⟨h0,hmem⟩:=toList_getElem? _ _ _ hp'
      have hpl : p=acc.2.length:=by omega
      rw [hpl]
      exact simplify_clean _ _ _ (fun s hs=>by
        obtain ⟨a,_,rfl⟩:=List.mem_map.1 hs
        exact (hinv.2 a).1) g' hmem
def idStats (n : ℕ) : List Stat:=List.ofFn (fun i : Fin n=>Sum.inr i)
theorem inv_id (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (idStats n,[]):=by
  refine ⟨by simp [idStats],?_⟩
  intro i
  by_cases hlt : i < n
  · simp [idStats,hlt,StatValid,statVal,wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [idStats];omega),
      List.getD_eq_default _ _ (by simp;omega)]
    exact ⟨trivial,rfl⟩
theorem getD_ofFn {α : Type} (m : ℕ) (F : Fin m → α) (d : α) (j : Fin m) :
    (List.ofFn F).getD j d=F j:=by
  simp
theorem split_at {α : Type} : ∀ (l : List α) (p : ℕ) (g : α),l[p]?=some g →
    ∃ pre post,l=pre ++ g :: post ∧ pre.length=p:=by
  intro l
  induction l with
  | nil=>intro p g h;simp at h
  | cons x l ih =>
    intro p g h
    cases p with
    | zero =>
      simp at h
      subst h
      exact ⟨[],l,rfl,rfl⟩
    | succ p =>
      simp at h
      obtain ⟨pre,post,rfl,rfl⟩:=ih p g h
      exact ⟨x :: pre,post,rfl,rfl⟩
theorem agree_except (k : ℕ) (gs : List Gate) : ∀ w w' : List Bool,
    (∀ g ∈ gs,k ∉ g.inputs) → w.length=w'.length →
    (∀ j,j ≠ k → w.getD j false=w'.getD j false) →
    ∀ j,j ≠ k → (wiresFrom gs w).getD j false=(wiresFrom gs w').getD j false:=by
  induction gs with
  | nil=>intro w w' _ _ h;exact h
  | cons g gs ih =>
    intro w w' hno hl h
    have hno':=hno g List.mem_cons_self
    have e : (g.inputs.map fun i=>w.getD i false)=g.inputs.map fun i=>w'.getD i false :=
      List.map_congr_left (fun a ha=>h a (fun e=>hno' (e ▸ ha)))
    apply ih (w ++ [g.op.eval (g.inputs.map fun i=>w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i=>w'.getD i false)])
      (fun g' hg'=>hno g' (List.mem_cons_of_mem _ hg')) (by simp [hl])
    intro j hj
    by_cases hjl : j=w.length
    · rw [hjl,getD_snoc_eq,hl,getD_snoc_eq,e]
    · rw [getD_snoc_ne _ _ _ _ hjl,getD_snoc_ne _ _ _ _ (by omega)]
      exact h j hj
end CP
namespace CP
open PEqualNP.CircuitLowerBounds
def vl {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) : Bool :=
  (wiresFrom gs (List.ofFn u)).getD j false
theorem vl_input {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) (h : j < k) :
    vl gs u j=u ⟨j,h⟩:=by
  unfold vl
  rw [getD_wiresFrom gs _ j (by simpa using h)]
  exact getD_ofFn k u false ⟨j,h⟩
theorem vl_gate {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u : Fin k → Bool) (p : ℕ)
    (g : Gate) (hp : gs[p]?=some g) :
    vl gs u (k + p)=g.op.eval (g.inputs.map (vl gs u)):=by
  have hlt:=(hcl p g hp).lt
  obtain ⟨pre,post,rfl,rfl⟩:=split_at gs p g hp
  have hwl : (wiresFrom pre (List.ofFn u)).length=k + pre.length:=by
    rw [length_wiresFrom];simp
  have e : wiresFrom (pre ++ g :: post) (List.ofFn u)
      = wiresFrom post (wiresFrom pre (List.ofFn u) ++
        [g.op.eval (g.inputs.map fun i=>(wiresFrom pre (List.ofFn u)).getD i false)]):=by
    rw [wiresFrom_append];rfl
  have full : ∀ j,j < k + pre.length →
      (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD j false
        = (wiresFrom pre (List.ofFn u)).getD j false:=by
    intro j hj
    rw [e,getD_wiresFrom _ _ j (by simp [hwl];omega),getD_snoc_ne _ _ _ _ (by omega)]
  have top : (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
      = g.op.eval (g.inputs.map fun i=>(wiresFrom pre (List.ofFn u)).getD i false):=by
    rw [e,getD_wiresFrom _ _ _ (by simp [hwl]),getD_snoc_len _ _ _ _ hwl]
  show (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
    = g.op.eval (g.inputs.map fun j=>(wiresFrom (pre ++ g :: post) (List.ofFn u)).getD j false)
  rw [top]
  congr 1
  apply List.map_congr_left
  intro a ha
  exact (full a (hlt a ha)).symm
theorem vl_congr {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u u' : Fin k → Bool) (p : ℕ)
    (g : Gate) (hp : gs[p]?=some g) (h : ∀ a ∈ g.inputs,vl gs u a=vl gs u' a) :
    vl gs u (k + p)=vl gs u' (k + p):=by
  rw [vl_gate gs hcl u p g hp,vl_gate gs hcl u' p g hp]
  congr 1
  exact List.map_congr_left h
theorem drop_core (k : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (hcl : CleanL k (pre ++ g :: post)) (o : ℕ) (S : Stat)
    (hS : ∀ y : Fin k → Bool,StatValid (k + (elim k pre (idStats k,[])).2.length) S ∧
      statVal (wiresFrom (elim k pre (idStats k,[])).2 (List.ofFn y)) S
        = vl (pre ++ g :: post) y (k + pre.length))
    (hnc : ∃ y y' : Fin k → Bool,vl (pre ++ g :: post) y o ≠ vl (pre ++ g :: post) y' o) :
    ∃ gs' o',CleanL k gs' ∧ gs'.length + 1 ≤ (pre ++ g :: post).length ∧
      nnC gs' ≤ nnC pre + nnC post ∧
      ∀ y : Fin k → Bool,vl gs' y o' = vl (pre ++ g :: post) y o:=by
  have hok : ∀ g' ∈ pre ++ g :: post,Ok g':=fun g' hg'=>(clean_nok _ _ hcl g' hg').1
  have hokpre : ∀ g' ∈ pre,Ok g':=fun g' h=>hok g' (List.mem_append_left _ h)
  have hokpost : ∀ g' ∈ post,Ok g' :=
    fun g' h=>hok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have inv1 : ∀ y : Fin k → Bool,Inv k (List.ofFn y) (wiresFrom pre (List.ofFn y))
      (elim k pre (idStats k,[])) :=
    fun y=>inv_elim k _ (by simp) pre _ _ hokpre (inv_id k y)
  have hwl : ∀ y : Fin k → Bool,(wiresFrom pre (List.ofFn y)).length=k + pre.length:=by
    intro y;rw [length_wiresFrom];simp
  have hfull : ∀ y : Fin k → Bool,wiresFrom (pre ++ g :: post) (List.ofFn y)
      = wiresFrom post (wiresFrom pre (List.ofFn y) ++
        [g.op.eval (g.inputs.map fun a=>(wiresFrom pre (List.ofFn y)).getD a false)]):=by
    intro y;rw [wiresFrom_append];rfl
  have hgv : ∀ y : Fin k → Bool,vl (pre ++ g :: post) y (k + pre.length)
      = g.op.eval (g.inputs.map fun a=>(wiresFrom pre (List.ofFn y)).getD a false):=by
    intro y
    show (wiresFrom (pre ++ g :: post) (List.ofFn y)).getD (k + pre.length) false=_
    rw [hfull,getD_wiresFrom _ _ _ (by simp [hwl y]),getD_snoc_len _ _ _ _ (hwl y)]
  have inv2 : ∀ y : Fin k → Bool,Inv k (List.ofFn y)
      (wiresFrom pre (List.ofFn y) ++
        [g.op.eval (g.inputs.map fun a=>(wiresFrom pre (List.ofFn y)).getD a false)])
      ((elim k pre (idStats k,[])).1 ++ [S],(elim k pre (idStats k,[])).2):=by
    intro y
    obtain ⟨hl,hi⟩:=inv1 y
    refine ⟨by simp [hl],?_⟩
    intro a
    show StatValid (k + (elim k pre (idStats k,[])).2.length)
        (((elim k pre (idStats k,[])).1 ++ [S]).getD a (Sum.inl false)) ∧
      statVal (wiresFrom (elim k pre (idStats k,[])).2 (List.ofFn y))
        (((elim k pre (idStats k,[])).1 ++ [S]).getD a (Sum.inl false))=_
    by_cases hal : a=(elim k pre (idStats k,[])).1.length
    · rw [hal,getD_snoc_eq,hl,getD_snoc_eq]
      exact ⟨(hS y).1,by rw [(hS y).2,hgv]⟩
    · rw [getD_snoc_ne _ _ _ _ hal,getD_snoc_ne _ _ _ _ (by omega)]
      exact hi a
  have inv3 : ∀ y : Fin k → Bool,Inv k (List.ofFn y)
      (wiresFrom (pre ++ g :: post) (List.ofFn y))
      (elim k post ((elim k pre (idStats k,[])).1 ++ [S],(elim k pre (idStats k,[])).2)):=by
    intro y
    rw [hfull]
    exact inv_elim k _ (by simp) post _ _ hokpost (inv2 y)
  have hc1 : CleanL k (elim k pre (idStats k,[])).2 :=
    clean_elim k (List.ofFn fun _ : Fin k=>false) (by simp) pre _ _ hokpre (inv_id k _)
      (by intro p g' hp;simp at hp)
  have hc3 : CleanL k
      (elim k post ((elim k pre (idStats k,[])).1 ++ [S],(elim k pre (idStats k,[])).2)).2 :=
    clean_elim k (List.ofFn fun _ : Fin k=>false) (by simp) post _ _ hokpost (inv2 _) hc1
  have hlen : (elim k post ((elim k pre (idStats k,[])).1 ++ [S],
      (elim k pre (idStats k,[])).2)).2.length + 1 ≤ (pre ++ g :: post).length:=by
    have h1 : (elim k post ((elim k pre (idStats k,[])).1 ++ [S],
        (elim k pre (idStats k,[])).2)).2.length
        ≤ (elim k pre (idStats k,[])).2.length + post.length:=elim_len k post _
    have h2 : (elim k pre (idStats k,[])).2.length ≤ 0 + pre.length :=
      elim_len k pre (idStats k,[])
    simp only [List.length_append,List.length_cons]
    omega
  have hval : ∀ y : Fin k → Bool,
      statVal (wiresFrom (elim k post ((elim k pre (idStats k,[])).1 ++ [S],
          (elim k pre (idStats k,[])).2)).2 (List.ofFn y))
        ((elim k post ((elim k pre (idStats k,[])).1 ++ [S],
          (elim k pre (idStats k,[])).2)).1.getD o (Sum.inl false))
      = vl (pre ++ g :: post) y o:=fun y=>((inv3 y).2 o).2
  cases hst : (elim k post ((elim k pre (idStats k,[])).1 ++ [S],
      (elim k pre (idStats k,[])).2)).1.getD o (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y,y',hne⟩:=hnc
    apply hne
    rw [← hval y,← hval y',hst]
    rfl
  | inr j =>
    refine ⟨_,j,hc3,hlen,?_,?_⟩
    · exact (elim_nonNotCount k post _).trans (Nat.add_le_add_right
        (by simpa [nnC] using elim_nonNotCount k pre (idStats k,[])) _)
    · intro y
      have h:=hval y
      rw [hst] at h
      exact h
theorem drop_alias (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p j : ℕ) (hp : p < gs.length)
    (hj : j < k + p) (heq : ∀ y : Fin k → Bool,vl gs y (k + p)=vl gs y j)
    (hnc : ∃ y y' : Fin k → Bool,vl gs y o ≠ vl gs y' o) :
    ∃ gs' o',CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧ nnC gs' ≤ nnC (gs.eraseIdx p) ∧
      ∀ y : Fin k → Bool,vl gs' y o' = vl gs y o:=by
  obtain ⟨g,hg⟩ : ∃ g,gs[p]?=some g:=⟨gs[p],List.getElem?_eq_getElem hp⟩
  obtain ⟨pre,post,rfl,rfl⟩:=split_at gs p g hg
  rw [List.eraseIdx_append_of_length_le le_rfl,Nat.sub_self,List.eraseIdx_cons_zero]
  have hcount : nnC (pre ++ post)=nnC pre + nnC post:=by
    simp [nnC]
  rw [hcount]
  apply drop_core k pre g post hcl o ((elim k pre (idStats k,[])).1.getD j (Sum.inl false))
    ?_ hnc
  intro y
  have hokpre : ∀ g' ∈ pre,Ok g' :=
    fun g' h=>(clean_nok _ _ hcl g' (List.mem_append_left _ h)).1
  have inv1:=inv_elim k (List.ofFn y) (by simp) pre _ _ hokpre (inv_id k y)
  refine ⟨(inv1.2 j).1,?_⟩
  rw [(inv1.2 j).2,heq y]
  show (wiresFrom pre (List.ofFn y)).getD j false
    = (wiresFrom (pre ++ g :: post) (List.ofFn y)).getD j false
  rw [wiresFrom_append,getD_wiresFrom (g :: post) (wiresFrom pre (List.ofFn y)) j
    (by rw [length_wiresFrom];simp;omega)]
end CP
namespace PCT
open PEqualNP.CircuitLowerBounds
open CP
def avoid {W : Type} (edge : W → W → Prop) (cut : W) (a b : W) : Prop :=
  edge a b ∧ a ≠ cut ∧ b ≠ cut
theorem difference_traces {W : Type} (rank : W → Nat) (input : W → Prop)
    (edge : W → W → Prop) (cut : W) (x y : W → Bool)
    (order : ∀ a b,edge a b → rank a < rank b)
    (localStep : ∀ b,¬ input b → x b ≠ y b → ∃ a,edge a b ∧ x a ≠ y a)
    (sameCut : x cut=y cut) {out : W} (different : x out ≠ y out) :
    ∃ a,input a ∧ x a ≠ y a ∧ Relation.ReflTransGen (avoid edge cut) a out:=by
  classical
  have track : ∀ k b,rank b=k → x b ≠ y b →
      ∃ a,input a ∧ x a ≠ y a ∧ Relation.ReflTransGen (avoid edge cut) a b:=by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro b hb diff
      by_cases hInput : input b
      · exact ⟨b,hInput,diff,Relation.ReflTransGen.refl⟩
      · obtain ⟨p,hp,dp⟩:=localStep b hInput diff
        have earlier : rank p < k:=(order p b hp).trans_eq hb
        obtain ⟨a,ha,da,path⟩:=ih (rank p) earlier p rfl dp
        have pOff : p ≠ cut:=by rintro rfl;exact dp sameCut
        have bOff : b ≠ cut:=by rintro rfl;exact diff sameCut
        exact ⟨a,ha,da,path.tail ⟨hp,pOff,bOff⟩⟩
  exact track (rank out) out rfl different
theorem cut_agreement {W : Type} (rank : W → Nat) (input : W → Prop)
    (edge : W → W → Prop) (cut out : W) (x y : W → Bool)
    (order : ∀ a b,edge a b → rank a < rank b)
    (localStep : ∀ b,¬ input b → x b ≠ y b → ∃ a,edge a b ∧ x a ≠ y a)
    (sameCut : x cut=y cut)
    (blocked : ∀ a,input a → x a ≠ y a →
      ¬ Relation.ReflTransGen (avoid edge cut) a out) : x out=y out:=by
  by_contra different
  obtain ⟨a,ha,da,reaches⟩:=difference_traces rank input edge cut x y
    order localStep sameCut different
  exact blocked a ha da reaches
theorem unary_factor {A : Type} (w f : A → Bool)
    (h : ∀ x y,w x=w y → f x=f y) :
    ∃ outer : Bool → Bool,∀ x,outer (w x)=f x:=by
  classical
  let outer (b : Bool):=if hb : ∃ a,w a=b then f (Classical.choose hb) else false
  refine ⟨outer,fun x=>?_⟩
  have hx : ∃ a,w a=w x:=⟨x,rfl⟩
  unfold outer
  rw [dite_eq_left hx]
  exact h _ _ (Classical.choose_spec hx)
def iW {n : Nat} (gs : List Gate) (v : Fin n) : Fin (n + gs.length) :=
  v.castLE (Nat.le_add_right n gs.length)
def rE {n : Nat} (gs : List Gate) (a b : Fin (n + gs.length)) : Prop :=
  ∃ (p : Nat) (g : Gate),gs[p]?=some g ∧ b.val=n + p ∧ a.val ∈ g.inputs
theorem rOrd {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    {a b : Fin (n + gs.length)} (edge : rE gs a b) : a.val < b.val:=by
  obtain ⟨p,g,hpg,hb,ha⟩:=edge
  rw [hb]
  exact (hcl p g hpg).lt _ ha
private theorem gate_difference {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (x y : Fin n → Bool) (b : Fin (n + gs.length)) (notInput : ¬ b.val < n)
    (diff : vl gs x b.val ≠ vl gs y b.val) :
    ∃ a : Fin (n + gs.length),rE gs a b ∧ vl gs x a.val ≠ vl gs y a.val:=by
  let p:=b.val - n
  have hb : b.val=n + p:=by dsimp [p];omega
  have hp : p < gs.length:=by have:=b.isLt;omega
  let g:=gs[p]
  have hpg : gs[p]?=some g:=List.getElem?_eq_getElem hp
  have differingRead : ∃ a ∈ g.inputs,vl gs x a ≠ vl gs y a:=by
    classical
    by_contra none
    apply diff
    rw [hb]
    exact vl_congr gs hcl x y p g hpg (fun a ha=>by
      by_contra da
      exact none ⟨a,ha,da⟩)
  obtain ⟨a,ha,da⟩:=differingRead
  have ha':=(hcl p g hpg).lt a ha
  refine ⟨⟨a,by have:=b.isLt;omega⟩,⟨p,g,hpg,hb,ha⟩,da⟩
theorem cca {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (cut out : Fin (n + gs.length)) (x y : Fin n → Bool)
    (sameCut : vl gs x cut.val=vl gs y cut.val)
    (blocked : ∀ i : Fin n,x i ≠ y i →
      ¬ Relation.ReflTransGen (avoid (rE gs) cut) (iW gs i) out) :
    vl gs x out.val=vl gs y out.val:=by
  apply cut_agreement Fin.val (fun v=>v.val < n) (rE gs) cut out
    (fun v=>vl gs x v.val) (fun v=>vl gs y v.val)
  · exact fun _ _ e=>rOrd hcl e
  · exact gate_difference hcl x y
  · exact sameCut
  · intro a ha diff
    let i : Fin n:=⟨a.val,ha⟩
    have sameWire : iW gs i=a:=Fin.ext rfl
    have di : x i ≠ y i:=by
      rw [vl_input gs x a.val ha,vl_input gs y a.val ha] at diff
      exact diff
    rw [← sameWire]
    exact blocked i di
theorem circuit_cut_factors {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (cut out : Fin (n + gs.length)) (group : Fin n → Prop) (base : Fin n → Bool)
    (blocked : ∀ i : Fin n,group i →
      ¬ Relation.ReflTransGen (avoid (rE gs) cut) (iW gs i) out) :
    ∃ outer : Bool → Bool,∀ x : Fin n → Bool,(∀ i,¬ group i → x i=base i) →
      outer (vl gs x cut.val)=vl gs x out.val:=by
  let Fiber:={x : Fin n → Bool // ∀ i,¬ group i → x i=base i}
  obtain ⟨outer,ho⟩:=unary_factor
    (fun x : Fiber=>vl gs x.val cut.val) (fun x : Fiber=>vl gs x.val out.val) (by
      intro x y sameCut
      apply cca hcl cut out x.val y.val sameCut
      intro i diff
      apply blocked i
      by_contra notGroup
      exact diff ((x.property i notGroup).trans (y.property i notGroup).symm))
  exact ⟨outer,fun x agrees=>ho ⟨x,agrees⟩⟩
end PCT
namespace CP.Readers
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity CP
def Dep {m : ℕ} (f : (Fin m → Bool) → Bool) (p : Fin m) : Prop :=
  ∃ x : Fin m → Bool,f (Function.update x p (!x p)) ≠ f x
def Least (m : ℕ) (f : (Fin m → Bool) → Bool) (gs : List Gate) (o : ℕ) : Prop :=
  CleanL m gs ∧ (∀ x : Fin m → Bool,vl gs x o=f x) ∧
  (∀ (gs' : List Gate) (o' : ℕ),CleanL m gs' → (∀ x : Fin m → Bool,vl gs' x o' = f x) →
    nnC gs' ≤ nnC gs → gs.length ≤ gs'.length)
theorem Least.hcl {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (L : Least m f gs o) : CleanL m gs:=L.1
theorem Least.hev {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (L : Least m f gs o) : ∀ x : Fin m → Bool,vl gs x o=f x:=L.2.1
theorem Least.hmin {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (L : Least m f gs o) : ∀ (gs' : List Gate) (o' : ℕ),CleanL m gs' →
      (∀ x : Fin m → Bool,vl gs' x o' = f x) →
      nnC gs' ≤ nnC gs → gs.length ≤ gs'.length:=L.2.2
def Reads (gs : List Gate) (p w : ℕ) : Prop:=∃ g,gs[p]?=some g ∧ w ∈ g.inputs
theorem dep_nc {m : ℕ} {f : (Fin m → Bool) → Bool} {p : Fin m} (h : Dep f p) :
    ∃ x y : Fin m → Bool,f x ≠ f y:=by
  obtain ⟨x,hx⟩:=h
  exact ⟨_,_,hx⟩
theorem reads_lt {k : ℕ} {gs : List Gate} (hcl : CleanL k gs) {q w : ℕ} (h : Reads gs q w) :
    w < k + q:=by
  obtain ⟨g,hg,hw⟩:=h
  exact (hcl q g hg).lt w hw
theorem vl_beyond {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (w : ℕ) (h : k + gs.length ≤ w) :
    vl gs u w=false:=by
  unfold vl
  exact List.getD_eq_default _ _ (by rw [length_wiresFrom];simp;omega)
theorem clean_with_budget {n : ℕ} {f : (Fin n → Bool) → Bool} (C : Circuit)
    (hfan : FanInTwo C) (hev : ∀ x : Fin n → Bool,C.eval (List.ofFn x)=f x)
    (hnc : ∃ x y,f x ≠ f y) :
    ∃ gs o,CleanL n gs ∧ nnC gs ≤ nnC C.gates ∧ ∀ x,vl gs x o=f x:=by
  have hok : ∀ g ∈ C.gates,Ok g:=hfan
  set acc:=elim n C.gates (idStats n,[]) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn y)) acc :=
    fun y=>inv_elim n _ (by simp) C.gates _ _ hok (inv_id n y)
  have hval : ∀ y : Fin n → Bool,
      statVal (wiresFrom acc.2 (List.ofFn y)) (acc.1.getD C.output (Sum.inl false))=f y:=by
    intro y
    rw [((hinv y).2 C.output).2,← hev y]
    rfl
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y,y',hne⟩:=hnc
    apply hne
    rw [← hval y,← hval y',hst]
    rfl
  | inr j =>
    refine ⟨acc.2,j,?_,?_,?_⟩
    · exact clean_elim n (List.ofFn fun _ : Fin n=>false) (by simp) C.gates _ _ hok
        (inv_id n _) (by intro p g hp;simp at hp)
    · simpa [nnC,hacc] using elim_nonNotCount n C.gates (idStats n,[])
    · intro y
      simpa only [hst,statVal,vl] using hval y
theorem least_with_budget {n : ℕ} {f : (Fin n → Bool) → Bool} (C : Circuit)
    (hfan : FanInTwo C) (hev : ∀ x : Fin n → Bool,C.eval (List.ofFn x)=f x)
    (hnc : ∃ x y,f x ≠ f y) :
    ∃ gs o,Least n f gs o ∧ nnC gs ≤ nnC C.gates:=by
  classical
  let admissible (t : ℕ):=∃ gs o,CleanL n gs ∧ nnC gs ≤ nnC C.gates ∧
    (∀ x,vl gs x o=f x) ∧ gs.length=t
  obtain ⟨gs,o,clean,count,he⟩:=clean_with_budget C hfan hev hnc
  have existsAdmissible : ∃ t,admissible t:=⟨gs.length,gs,o,clean,count,he,rfl⟩
  obtain ⟨gs',o',hc,hb,he',hl⟩:=Nat.find_spec existsAdmissible
  refine ⟨gs',o',⟨hc,he',?_⟩,hb⟩
  intro testGates testOut testClean testEval testCost
  have lower:=Nat.find_min' existsAdmissible
    (show admissible testGates.length from
      ⟨testGates,testOut,testClean,testCost.trans hb,testEval,rfl⟩)
  exact hl.trans_le lower
theorem drop_dead (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p : ℕ) (hp : p < gs.length)
    (ho : o ≠ k + p) (hno : ∀ q,¬ Reads gs q (k + p))
    (hnc : ∃ y y' : Fin k → Bool,vl gs y o ≠ vl gs y' o) :
    ∃ gs' o',CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧ nnC gs' ≤ nnC gs ∧
      ∀ y : Fin k → Bool,vl gs' y o' = vl gs y o:=by
  obtain ⟨g,hg⟩ : ∃ g,gs[p]?=some g:=⟨gs[p],List.getElem?_eq_getElem hp⟩
  have hpos : 0 < k + p:=by
    rcases hcl p g hg with ⟨_,j,hj,_⟩ | ⟨_,j,_,hj,_,_⟩<;>omega
  let g0 : Gate:=⟨GateOp.and,[0,0]⟩
  let gs':=gs.set p g0
  have hlen : gs'.length=gs.length:=by simp [gs']
  have hget_p : gs'[p]?=some g0:=by simp [gs',hp]
  have hget_ne : ∀ r,r ≠ p → gs'[r]?=gs[r]?:=by
    intro r hr
    simp [gs',Ne.symm hr]
  have hcl' : CleanL k gs':=by
    intro r g' hr'
    by_cases hrp : r=p
    · subst hrp
      rw [hget_p] at hr'
      cases hr'
      exact Or.inr ⟨Or.inl rfl,0,0,hpos,hpos,rfl⟩
    · rw [hget_ne r hrp] at hr'
      exact hcl r g' hr'
  have hagree : ∀ y : Fin k → Bool,∀ w,w ≠ k + p → vl gs' y w=vl gs y w:=by
    intro y w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw
      by_cases hwk : w < k
      · rw [vl_input gs' y w hwk,vl_input gs y w hwk]
      · obtain ⟨r,rfl⟩ : ∃ r,w=k + r:=⟨w - k,by omega⟩
        have hrp : r ≠ p:=fun e=>hw (by rw [e])
        cases hr : gs[r]? with
        | none =>
          have hl : gs.length ≤ r:=List.getElem?_eq_none_iff.1 hr
          rw [vl_beyond gs' y _ (by omega),vl_beyond gs y _ (by omega)]
        | some g' =>
          have hr' : gs'[r]?=some g':=by rw [hget_ne r hrp];exact hr
          rw [vl_gate gs' hcl' y r g' hr',vl_gate gs hcl y r g' hr]
          congr 1
          apply List.map_congr_left
          intro a ha
          have hlt:=(hcl r g' hr).lt a ha
          exact ih a hlt (fun e=>hno r ⟨g',hr,e ▸ ha⟩)
  have halias : ∀ y : Fin k → Bool,vl gs' y (k + p)=vl gs' y 0:=by
    intro y
    rw [vl_gate gs' hcl' y p g0 hget_p]
    simp [g0,GateOp.eval]
  have hnc' : ∃ y y' : Fin k → Bool,vl gs' y o ≠ vl gs' y' o:=by
    obtain ⟨y,y',h⟩:=hnc
    exact ⟨y,y',by rw [hagree y o ho,hagree y' o ho];exact h⟩
  obtain ⟨gs'',o'',hc'',hl'',hcost,he''⟩ :=
    drop_alias k gs' hcl' o p 0 (by omega) hpos halias hnc'
  have hkeep : nnC (gs'.eraseIdx p) ≤ nnC gs:=by
    rw [show gs'.eraseIdx p=gs.eraseIdx p from List.eraseIdx_set_eq]
    exact (List.eraseIdx_sublist gs p).countP_le
  exact ⟨gs'',o'',hc'',by omega,hcost.trans hkeep,fun y=>by rw [he'' y,hagree y o ho]⟩
section LocalSection1
variable {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}
theorem Least.ncv (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool,f x ≠ f y) :
    ∃ y y' : Fin m → Bool,vl gs y o ≠ vl gs y' o:=by
  obtain ⟨x,y,h⟩:=hnc
  exact ⟨x,y,by rw [L.hev,L.hev];exact h⟩
theorem Least.no_alias (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool,f x ≠ f y) (p : ℕ)
    (hp : p < gs.length) (j : ℕ) (hj : j < m + p) :
    ¬ ∀ u : Fin m → Bool,vl gs u (m + p)=vl gs u j:=by
  intro hall
  obtain ⟨gs',o',hc',hl',hcost,he'⟩:=drop_alias m gs L.hcl o p j hp hj hall (L.ncv hnc)
  have hcost' : nnC gs' ≤ nnC gs :=
    hcost.trans (List.eraseIdx_sublist gs p).countP_le
  have:=L.hmin gs' o' hc' (fun x=>by rw [he' x];exact L.hev x) hcost'
  omega
theorem Least.live (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool,f x ≠ f y) (p : ℕ)
    (hp : p < gs.length) (ho : o ≠ m + p) : ∃ q,p < q ∧ Reads gs q (m + p):=by
  by_contra hno
  have hno' : ∀ q,¬ Reads gs q (m + p):=by
    intro q hq
    by_cases hpq : p < q
    · exact hno ⟨q,hpq,hq⟩
    · have:=reads_lt L.hcl hq
      omega
  obtain ⟨gs',o',hc',hl',hcost,he'⟩:=drop_dead m gs L.hcl o p hp ho hno' (L.ncv hnc)
  have:=L.hmin gs' o' hc' (fun x=>by rw [he' x];exact L.hev x) hcost
  omega
theorem Least.dep_read (L : Least m f gs o) (i : Fin m) (hd : Dep f i)
    (hnc : ∀ b : Bool,∃ x y : Fin m → Bool,
      f (Function.update x i b) ≠ f (Function.update y i b)) : ∃ q,Reads gs q i:=by
  by_contra hno
  have hno' : ∀ g ∈ gs,(i : ℕ) ∉ g.inputs:=by
    intro g hg hi
    obtain ⟨q,hq⟩:=List.mem_iff_getElem?.1 hg
    exact hno ⟨q,g,hq,hi⟩
  have hoi : o ≠ i:=by
    intro e
    obtain ⟨x,y,hxy⟩:=hnc false
    apply hxy
    rw [← L.hev,← L.hev,e,vl_input gs _ i i.isLt,vl_input gs _ i i.isLt]
    simp
  obtain ⟨x,hx⟩:=hd
  apply hx
  rw [← L.hev,← L.hev]
  refine agree_except i gs _ _ hno' (by simp) ?_ o hoi
  intro j hj
  by_cases hjm : j < m
  · rw [show (List.ofFn (Function.update x i (!x i))).getD j false
        = Function.update x i (!x i) ⟨j,hjm⟩ from getD_ofFn m _ false ⟨j,hjm⟩,
      show (List.ofFn x).getD j false=x ⟨j,hjm⟩ from getD_ofFn m x false ⟨j,hjm⟩]
    exact Function.update_of_ne (fun e=>hj (congrArg Fin.val e)) _ _
  · rw [List.getD_eq_default _ _ (by simp;omega),List.getD_eq_default _ _ (by simp;omega)]
end LocalSection1
end CP.Readers
namespace CP.RunAsm
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity CP
open CP.Readers
theorem pq2f_nodup {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool,f x ≠ f y) {p : ℕ} {g : Gate}
    (hg : gs[p]?=some g) (hop : g.op=GateOp.and ∨ g.op=GateOp.or) {a b : ℕ}
    (hin : g.inputs=[a,b]) : a ≠ b:=by
  rintro rfl
  have hcl:=L.hcl p g hg
  have hlt : a < m + p:=by
    rcases hcl with ⟨h1,j,_,h2⟩ | ⟨h1,j,k,hj,hk,h2⟩
    · rw [hin] at h2;simp at h2
    · rw [hin] at h2;simp at h2;omega
  have hp : p < gs.length:=(List.getElem?_eq_some_iff.1 hg).1
  refine L.no_alias hnc p hp a hlt (fun u=>?_)
  rw [vl_gate gs L.hcl u p g hg,hin]
  rcases hop with h | h<;>rw [h]<;>simp [GateOp.eval]
end CP.RunAsm
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CP CP.Readers
open CP.RunAsm
theorem least_wire_used {n out : Nat} {f : (Fin n → Bool) → Bool} {gs : List Gate}
    (least : Least n f gs out) (nonconstant : ∃ x y,f x ≠ f y)
    (dependent : ∀ v : Fin n,Dep f v)
    (stillNonconstant : ∀ (v : Fin n) (b : Bool),∃ x y,
      f (Function.update x v b) ≠ f (Function.update y v b))
    (w : Nat) (amongWires : w < n + gs.length) (notOutput : w ≠ out) :
    ∃ p,Reads gs p w:=by
  by_cases isInput : w < n
  · let v : Fin n:=⟨w,isInput⟩
    exact least.dep_read v (dependent v) (stillNonconstant v)
  · let p:=w - n
    have wire : w=n + p:=by dsimp [p];omega
    have pLt : p < gs.length:=by omega
    have notOut : out ≠ n + p:=by omega
    obtain ⟨q,_,read⟩:=least.live nonconstant p pLt notOut
    exact ⟨q,wire.symm ▸ read⟩
theorem least_gate_inputs_nodup {n out : Nat} {f : (Fin n → Bool) → Bool} {gs : List Gate}
    (least : Least n f gs out) (nonconstant : ∃ x y,f x ≠ f y) (g : Gate) (present : g ∈ gs) :
    g.inputs.Nodup:=by
  obtain ⟨slot,atSlot⟩:=List.mem_iff_getElem?.mp present
  rcases least.hcl slot g atSlot with ⟨_,a,_,args⟩ | ⟨ops,a,b,_,_,args⟩
  · simp [args]
  · have distinct:=pq2f_nodup least nonconstant atSlot ops args
    simp [args,distinct]
theorem least_wire_readers_in_range {n out : Nat} {gs : List Gate}
    {f : (Fin n → Bool) → Bool} (least : Least n f gs out) (nonnull : ∃ x y,f x ≠ f y)
    (dependent : ∀ v : Fin n,Dep f v)
    (stillNonconstant : ∀ (v : Fin n) (b : Bool),∃ x y,
      f (Function.update x v b) ≠ f (Function.update y v b))
    (w : Fin (n + gs.length)) (notOutput : w.val ≠ out) :
    ∃ (p : Nat) (g : Gate),gs[p]?=some g ∧ w.val ∈ g.inputs ∧ n + p < n + gs.length:=by
  obtain ⟨p,g,hit,reads⟩:=least_wire_used least nonnull dependent stillNonconstant w.val w.isLt notOutput
  have bound:=(List.getElem?_eq_some_iff.mp hit).1
  exact ⟨p,g,hit,reads,by omega⟩
namespace PCT
open PEqualNP.CircuitLowerBounds
open CP CP.Readers
def prds {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (b : Fin (n + gs.length)) : List (Fin (n + gs.length)) :=
  if gate : n ≤ b.val then
    let slot:=b.val - n
    have hs : slot < gs.length:=by have:=b.isLt;omega
    let g:=gs[slot]'hs
    g.inputs.attach.map fun a=>⟨a.val,by
      have atSlot : gs[slot]?=some g:=List.getElem?_eq_getElem hs
      have before:=(clean slot g atSlot).lt a.val a.property
      omega⟩
  else []
theorem prdV {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (b : Fin (n + gs.length)) (internal : n ≤ b.val) :
    (prds clean b).map Fin.val =
      (gs[b.val - n]'(by have:=b.isLt;omega)).inputs:=by
  simp [prds,internal,List.map_map,Function.comp_def]
theorem predecessors_nil_input {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (b : Fin (n + gs.length)) (primary : b.val < n) : prds clean b=[]:=by
  simp [prds,show ¬ n ≤ b.val by omega]
theorem predecessors_val_gate {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (b : Fin (n + gs.length)) {p : Nat} {g : Gate} (atSlot : gs[p]?=some g) (bWire : b.val=n + p) :
    (prds clean b).map Fin.val=g.inputs:=by
  have isGate : n ≤ b.val:=by omega
  have which : b.val - n=p:=by omega
  have located:=(List.getElem?_eq_some_iff.mp atSlot).2
  simpa [which,located] using prdV clean b isGate
theorem predecessors_mem {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (a b : Fin (n + gs.length)) : a ∈ prds clean b ↔ rE gs a b:=by
  by_cases internal : n ≤ b.val
  · let slot:=b.val - n
    have hs : slot < gs.length:=by have:=b.isLt;dsimp [slot];omega
    let g:=gs[slot]'hs
    have wire : b.val=n + slot:=by dsimp [slot];omega
    have atSlot : gs[slot]?=some g:=List.getElem?_eq_getElem hs
    have valList : (prds clean b).map Fin.val=g.inputs :=
      prdV clean b internal
    constructor
    · intro mem
      refine ⟨slot,g,atSlot,wire,?_⟩
      rw [← valList]
      exact List.mem_map.mpr ⟨a,mem,rfl⟩
    · rintro ⟨q,h,atQ,wireQ,inside⟩
      have same : q=slot:=by omega
      subst q
      have gateSame : h=g:=Option.some.inj (atQ.symm.trans atSlot)
      subst h
      rw [← valList] at inside
      obtain ⟨a',mem,equal⟩:=List.mem_map.mp inside
      exact (Fin.ext equal : a' = a) ▸ mem
  · have empty : prds clean b=[]:=by simp [prds,internal]
    rw [empty]
    constructor
    · simp
    · rintro ⟨slot,g,_,wire,_⟩
      omega
theorem prdN {n out : Nat} {gs : List Gate} {f : (Fin n → Bool) → Bool}
    (least : Least n f gs out) (nonnull : ∃ x y,f x ≠ f y) (b : Fin (n + gs.length)) :
    (prds least.hcl b).Nodup:=by
  by_cases internal : n ≤ b.val
  · apply List.Nodup.of_map Fin.val
    rw [prdV least.hcl b internal]
    exact PEqualNP.Outside.L_meta_4369.least_gate_inputs_nodup least nonnull _
      (List.getElem_mem (by have:=b.isLt;omega))
  · simp [prds,internal]
end PCT
namespace PSc
open PEqualNP.MetaComplexity
def occ {n : ℕ} (i : Fin n) : DMFormula n → ℕ
  | .lit k _=>if k=i then 1 else 0
  | .and p q=>occ i p + occ i q
  | .or p q=>occ i p + occ i q
def hasPair {n : ℕ} (i j : Fin n) (p : DMFormula n) : Prop :=
  0 < occ i p ∨ 0 < occ j p
def pairInput {n : ℕ} (i j : Fin n) (base : Fin n → Bool) (a b : Bool) (k : Fin n) : Bool :=
  if k=i then a else if k=j then b else base k
def pairValue {n : ℕ} (i j : Fin n) (base : Fin n → Bool) (p : DMFormula n) :
    Bool → Bool → Bool :=
  fun a b=>p.eval (pairInput i j base a b)
def binOp (conj : Bool) (a b : Bool) : Bool :=
  if conj then a&&b else a||b
noncomputable def combine {n : ℕ} (conj : Bool) (i j : Fin n) (p q : DMFormula n)
    (P Q : Bool → Bool → Bool) : Bool → Bool → Bool:=by
  classical
  exact if hasPair i j p then
    if hasPair i j q then fun a b=>binOp conj (P a b) (Q a b) else P
    else Q
noncomputable def pairKernel {n : ℕ} (i j : Fin n) : DMFormula n → Bool → Bool → Bool
  | .lit k sign=>fun a b =>
    let bit:=if k=i then a else if k=j then b else false
    if sign then bit else !bit
  | .and p q=>combine true i j p q (pairKernel i j p) (pairKernel i j q)
  | .or p q=>combine false i j p q (pairKernel i j p) (pairKernel i j q)
private theorem eval_agree {n : ℕ} (p : DMFormula n) {x y : Fin n → Bool}
    (h : ∀ k,0 < occ k p → x k=y k) : p.eval x=p.eval y:=by
  induction p with
  | lit k s =>
    have e:=h k (by simp [occ])
    simp [DMFormula.eval,e]
  | and p q ihp ihq =>
    simp only [DMFormula.eval]
    rw [ihp (fun k hk=>h k (by simp only [occ];omega)),
      ihq (fun k hk=>h k (by simp only [occ];omega))]
  | or p q ihp ihq =>
    simp only [DMFormula.eval]
    rw [ihp (fun k hk=>h k (by simp only [occ];omega)),
      ihq (fun k hk=>h k (by simp only [occ];omega))]
private theorem absent_left {n : ℕ} {i j : Fin n} {base : Fin n → Bool} {p : DMFormula n}
    (h : occ i p=0) (a a' b : Bool) :
    pairValue i j base p a b=pairValue i j base p a' b:=by
  apply eval_agree
  intro k hk
  have ne : k ≠ i:=by rintro rfl;omega
  simp [pairInput,ne]
private theorem absent_right {n : ℕ} {i j : Fin n} {base : Fin n → Bool} {p : DMFormula n}
    (h : occ j p=0) (a b b' : Bool) :
    pairValue i j base p a b=pairValue i j base p a b':=by
  apply eval_agree
  intro k hk
  have ne : k ≠ j:=by rintro rfl;omega
  simp [pairInput,ne]
def changes (f : Bool → Bool → Bool) : Prop :=
  ∃ b,f false b ≠ f true b
private theorem changes_left {op : Bool → Bool → Bool} {P Q : Bool → Bool → Bool}
    (h : changes fun a b=>op (P a b) (Q a b))
    (hQ : ∀ b,Q false b=Q true b) : changes P:=by
  obtain ⟨b,hb⟩:=h
  exact ⟨b,fun hp=>hb (by
    change op (P false b) (Q false b)=op (P true b) (Q true b)
    rw [hp,hQ])⟩
private theorem changes_right {op : Bool → Bool → Bool} {P Q : Bool → Bool → Bool}
    (h : changes fun a b=>op (P a b) (Q a b))
    (hP : ∀ b,P false b=P true b) : changes Q:=by
  obtain ⟨b,hb⟩:=h
  exact ⟨b,fun hq=>hb (by
    change op (P false b) (Q false b)=op (P true b) (Q true b)
    rw [hq,hP])⟩
private theorem constant_pair {n : ℕ} {i j : Fin n} {base : Fin n → Bool} {p : DMFormula n}
    (h : ¬ hasPair i j p) (a b : Bool) :
    pairValue i j base p a b=pairValue i j base p false false:=by
  have hi : occ i p=0:=by
    by_contra e
    exact h (Or.inl (by omega))
  have hj : occ j p=0:=by
    by_contra e
    exact h (Or.inr (by omega))
  exact (absent_left hi a false b).trans (absent_right hj false b false)
private theorem neutral_right (conj c : Bool) (P : Bool → Bool → Bool)
    (h : ∃ a b a' b',binOp conj (P a b) c ≠ binOp conj (P a' b') c) :
    ∀ a b,binOp conj (P a b) c=P a b:=by
  cases conj<;>cases c<;>simp [binOp] at h ⊢
private theorem bin_comm (conj a b : Bool) : binOp conj a b=binOp conj b a:=by
  cases conj<;>cases a<;>cases b<;>rfl
private theorem combine_stable {n : ℕ} (i j : Fin n) (base : Fin n → Bool)
    (conj : Bool) (p q : DMFormula n)
    (hi : occ i p + occ i q ≤ 1)
    (hj : occ j p + occ j q ≤ 1)
    (present : hasPair i j p ∨ hasPair i j q)
    (dep_i : 0 < occ i p + occ i q →
      changes fun a b=>binOp conj (pairValue i j base p a b) (pairValue i j base q a b))
    (dep_j : 0 < occ j p + occ j q →
      changes fun b a=>binOp conj (pairValue i j base p a b) (pairValue i j base q a b))
    (ihp : occ i p ≤ 1 → occ j p ≤ 1 → hasPair i j p →
      (0 < occ i p → changes (pairValue i j base p)) →
      (0 < occ j p → changes fun b a=>pairValue i j base p a b) →
      ∀ a b,pairValue i j base p a b=pairKernel i j p a b)
    (ihq : occ i q ≤ 1 → occ j q ≤ 1 → hasPair i j q →
      (0 < occ i q → changes (pairValue i j base q)) →
      (0 < occ j q → changes fun b a=>pairValue i j base q a b) →
      ∀ a b,pairValue i j base q a b=pairKernel i j q a b)
    (a b : Bool) :
    binOp conj (pairValue i j base p a b) (pairValue i j base q a b) =
      combine conj i j p q (pairKernel i j p) (pairKernel i j q) a b:=by
  classical
  have pl : hasPair i j p → ∀ a b,pairValue i j base p a b=pairKernel i j p a b:=by
    intro hp
    apply ihp (by omega) (by omega) hp
    · intro h
      exact changes_left (dep_i (by omega)) (fun b=>absent_left (by omega) false true b)
    · intro h
      exact changes_left (dep_j (by omega)) (fun a=>absent_right (by omega) a false true)
  have ql : hasPair i j q → ∀ a b,pairValue i j base q a b=pairKernel i j q a b:=by
    intro hq
    apply ihq (by omega) (by omega) hq
    · intro h
      exact changes_right (dep_i (by omega)) (fun b=>absent_left (by omega) false true b)
    · intro h
      exact changes_right (dep_j (by omega)) (fun a=>absent_right (by omega) a false true)
  have nonconst : ∃ a b a' b',
      binOp conj (pairValue i j base p a b) (pairValue i j base q a b) ≠
        binOp conj (pairValue i j base p a' b') (pairValue i j base q a' b'):=by
    unfold hasPair at present
    rcases present with (h | h) | (h | h)
    · obtain ⟨b,h⟩:=dep_i (by omega)
      exact ⟨false,b,true,b,h⟩
    · obtain ⟨a,h⟩:=dep_j (by omega)
      exact ⟨a,false,a,true,h⟩
    · obtain ⟨b,h⟩:=dep_i (by omega)
      exact ⟨false,b,true,b,h⟩
    · obtain ⟨a,h⟩:=dep_j (by omega)
      exact ⟨a,false,a,true,h⟩
  by_cases hp : hasPair i j p
  · by_cases hq : hasPair i j q
    · simp [combine,hp,hq,pl hp,ql hq]
    · rw [constant_pair hq a b]
      have hn:=nonconst
      simp_rw [constant_pair hq] at hn
      rw [neutral_right conj _ _ hn a b,pl hp]
      simp [combine,hp,hq]
  · have hq:=present.resolve_left hp
    rw [constant_pair hp a b,bin_comm]
    have hn:=nonconst
    simp_rw [constant_pair hp,bin_comm conj (pairValue i j base p false false)] at hn
    rw [neutral_right conj _ _ hn a b,ql hq]
    simp [combine,hp]
private theorem stable_pair {n : ℕ} (i j : Fin n) (base : Fin n → Bool) (p : DMFormula n)
    (hi : occ i p ≤ 1) (hj : occ j p ≤ 1) (present : hasPair i j p)
    (dep_i : 0 < occ i p → changes (pairValue i j base p))
    (dep_j : 0 < occ j p → changes fun b a=>pairValue i j base p a b) :
    ∀ a b,pairValue i j base p a b=pairKernel i j p a b:=by
  induction p with
  | lit k s =>
    intro a b
    by_cases hki : k=i
    · simp [pairValue,pairKernel,DMFormula.eval,pairInput,hki]
    · have hkj : k=j:=by
        by_contra h
        simp [hasPair,occ,hki,h] at present
      simp [pairValue,pairKernel,DMFormula.eval,pairInput,hkj]
  | and p q ihp ihq =>
    have present' : hasPair i j p ∨ hasPair i j q:=by
      unfold hasPair at *
      simp only [occ] at present
      omega
    exact combine_stable i j base true p q hi hj present' dep_i dep_j ihp ihq
  | or p q ihp ihq =>
    have present' : hasPair i j p ∨ hasPair i j q:=by
      unfold hasPair at *
      simp only [occ] at present
      omega
    exact combine_stable i j base false p q hi hj present' dep_i dep_j ihp ihq
theorem fixed_pair_invariant {n : ℕ} (i j : Fin n) (p : DMFormula n)
    (hi : occ i p ≤ 1) (hj : occ j p ≤ 1)
    (baseA baseO : Fin n → Bool) (outerA outerO : Bool → Bool)
    (hA : ∀ a b,outerA (pairValue i j baseA p a b)=(a&&b))
    (hO : ∀ a b,outerO (pairValue i j baseO p a b)=(a||b)) : False:=by
  have depAi : changes (pairValue i j baseA p):=by
    refine ⟨true,fun h=>?_⟩
    have e:=congrArg outerA h
    rw [hA,hA] at e
    cases e
  have depAj : changes fun b a=>pairValue i j baseA p a b:=by
    refine ⟨true,fun h=>?_⟩
    have e:=congrArg outerA h
    rw [hA,hA] at e
    cases e
  have depOi : changes (pairValue i j baseO p):=by
    refine ⟨false,fun h=>?_⟩
    have e:=congrArg outerO h
    rw [hO,hO] at e
    cases e
  have depOj : changes fun b a=>pairValue i j baseO p a b:=by
    refine ⟨false,fun h=>?_⟩
    have e:=congrArg outerO h
    rw [hO,hO] at e
    cases e
  have present : hasPair i j p:=by
    left
    by_contra! h
    obtain ⟨b,hb⟩:=depAi
    exact hb (absent_left (by omega) false true b)
  have stableA:=stable_pair i j baseA p hi hj present (fun _=>depAi) (fun _=>depAj)
  have stableO:=stable_pair i j baseO p hi hj present (fun _=>depOi) (fun _=>depOj)
  simp_rw [stableA] at hA
  simp_rw [stableO] at hO
  have ne : pairKernel i j p false false ≠ pairKernel i j p false true:=by
    intro e
    have f:=congrArg outerO e
    rw [hO,hO] at f
    cases f
  have zeros:=hA false false
  have other:=hA false true
  have one:=hA true true
  cases hk : pairKernel i j p false false <;>
    cases hl : pairKernel i j p false true <;>
    cases hm : pairKernel i j p true true <;>
    simp_all
end PSc
namespace PCF
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open CP
open PSc
def negFormula {n : Nat} : DMFormula n → DMFormula n
  | .lit i sign=>.lit i (!sign)
  | .and a b=>.or (negFormula a) (negFormula b)
  | .or a b=>.and (negFormula a) (negFormula b)
theorem negFormula_eval {n : Nat} (p : DMFormula n) (x : Fin n → Bool) :
    (negFormula p).eval x=!(p.eval x):=by
  induction p with
  | lit i s =>
    cases s<;>cases e : x i<;>simp [negFormula,DMFormula.eval,e]
  | and a b iha ihb =>
    simp only [negFormula,DMFormula.eval,iha,ihb]
    cases a.eval x<;>cases b.eval x<;>rfl
  | or a b iha ihb =>
    simp only [negFormula,DMFormula.eval,iha,ihb]
    cases a.eval x<;>cases b.eval x<;>rfl
theorem negFormula_occurrences {n : Nat} (i : Fin n) (p : DMFormula n) :
    occ i (negFormula p)=occ i p:=by
  induction p with
  | lit i s=>rfl
  | and a b iha ihb=>simp [negFormula,occ,iha,ihb]
  | or a b iha ihb=>simp [negFormula,occ,iha,ihb]
def wF {n : Nat} (fallback : Fin n) (gs : List Gate) (w : Nat) : DMFormula n :=
  if hw : w < n then
    .lit ⟨w,hw⟩ true
  else
    match gs[w - n]? with
    | none=>.lit fallback true
    | some g =>
      match g.op,g.inputs with
      | .not,[a] =>
        if _ha : a < w then negFormula (wF fallback gs a) else .lit fallback true
      | .and,[a,b] =>
        if _ha : a < w then
          if _hb : b < w then .and (wF fallback gs a) (wF fallback gs b)
          else .lit fallback true
        else .lit fallback true
      | .or,[a,b] =>
        if _ha : a < w then
          if _hb : b < w then .or (wF fallback gs a) (wF fallback gs b)
          else .lit fallback true
        else .lit fallback true
      | _,_=>.lit fallback true
termination_by w
decreasing_by all_goals assumption
theorem wireFormula_input {n : Nat} (fallback : Fin n) (gs : List Gate) (i : Fin n) :
    wF fallback gs i.val=.lit i true:=by
  rw [wF]
  simp [i.isLt]
private theorem wireFormula_not {n : Nat} (fallback : Fin n) {gs : List Gate}
    {p a : Nat} {g : Gate} (hg : gs[p]?=some g) (op : g.op=.not)
    (inputs : g.inputs=[a]) (ha : a < n + p) :
    wF fallback gs (n + p)=negFormula (wF fallback gs a):=by
  have hn : ¬ n + p < n:=by omega
  have hp : n + p - n=p:=by omega
  conv_lhs=>rw [wF]
  simp [hn,hp,hg,op,inputs,ha]
private theorem wireFormula_and {n : Nat} (fallback : Fin n) {gs : List Gate}
    {p a b : Nat} {g : Gate} (hg : gs[p]?=some g) (op : g.op=.and)
    (inputs : g.inputs=[a,b]) (ha : a < n + p) (hb : b < n + p) :
    wF fallback gs (n + p)=.and (wF fallback gs a) (wF fallback gs b):=by
  have hn : ¬ n + p < n:=by omega
  have hp : n + p - n=p:=by omega
  conv_lhs=>rw [wF]
  simp [hn,hp,hg,op,inputs,ha,hb]
private theorem wireFormula_or {n : Nat} (fallback : Fin n) {gs : List Gate}
    {p a b : Nat} {g : Gate} (hg : gs[p]?=some g) (op : g.op=.or)
    (inputs : g.inputs=[a,b]) (ha : a < n + p) (hb : b < n + p) :
    wF fallback gs (n + p)=.or (wF fallback gs a) (wF fallback gs b):=by
  have hn : ¬ n + p < n:=by omega
  have hp : n + p - n=p:=by omega
  conv_lhs=>rw [wF]
  simp [hn,hp,hg,op,inputs,ha,hb]
theorem wireFormula_eval {n : Nat} (fallback : Fin n) {gs : List Gate} (hcl : CleanL n gs)
    (x : Fin n → Bool) (w : Nat) (hw : w < n + gs.length) :
    (wF fallback gs w).eval x=vl gs x w:=by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hi : w < n
    · rw [wireFormula_input fallback gs ⟨w,hi⟩,vl_input gs x w hi]
      rfl
    · obtain ⟨p,rfl⟩ : ∃ p,w=n + p:=⟨w - n,by omega⟩
      have hp : p < gs.length:=by omega
      let g:=gs[p]
      have hg : gs[p]?=some g:=List.getElem?_eq_getElem hp
      rcases hcl p g hg with ⟨op,a,ha,inputs⟩ | ⟨op | op,a,b,ha,hb,inputs⟩
      · rw [wireFormula_not fallback hg op inputs ha,negFormula_eval,ih a ha (by omega),
          vl_gate gs hcl x p g hg]
        simp [op,inputs,GateOp.eval]
      · rw [wireFormula_and fallback hg op inputs ha hb]
        simp only [DMFormula.eval]
        rw [ih a ha (by omega),ih b hb (by omega),vl_gate gs hcl x p g hg]
        simp [op,inputs,GateOp.eval]
      · rw [wireFormula_or fallback hg op inputs ha hb]
        simp only [DMFormula.eval]
        rw [ih a ha (by omega),ih b hb (by omega),vl_gate gs hcl x p g hg]
        simp [op,inputs,GateOp.eval]
theorem wireFormula_count_input {n : Nat} (fallback : Fin n) (gs : List Gate) (chosen i : Fin n) :
    occ chosen (wF fallback gs i.val)=if i=chosen then 1 else 0:=by
  rw [wireFormula_input]
  rfl
theorem wireFormula_count_gate {n : Nat} (fallback : Fin n) {gs : List Gate} (hcl : CleanL n gs)
    (chosen : Fin n) {p : Nat} {g : Gate} (hg : gs[p]?=some g) :
    occ chosen (wF fallback gs (n + p)) =
      (g.inputs.map fun a=>occ chosen (wF fallback gs a)).sum:=by
  rcases hcl p g hg with ⟨op,a,ha,inputs⟩ | ⟨op | op,a,b,ha,hb,inputs⟩
  · simp [wireFormula_not fallback hg op inputs ha,inputs,negFormula_occurrences]
  · simp [wireFormula_and fallback hg op inputs ha hb,inputs,occ]
  · simp [wireFormula_or fallback hg op inputs ha hb,inputs,occ]
theorem wireFormula_count_gate_fin {n : Nat} (fallback chosen : Fin n) {gs : List Gate}
    (hcl : CleanL n gs) {p : Nat} {g : Gate} (hg : gs[p]?=some g)
    {b : Fin (n + gs.length)} (hb : b.val=n + p)
    (parents : List (Fin (n + gs.length))) (parentsVal : parents.map Fin.val=g.inputs) :
    occ chosen (wF fallback gs b.val) =
      (parents.map fun a=>occ chosen (wF fallback gs a.val)).sum:=by
  rw [hb,wireFormula_count_gate fallback hcl chosen hg,← parentsVal,List.map_map]
  rfl
end PCF
namespace PCI
open PEqualNP.CircuitLowerBounds
open CP
open PCF PCT PSc
theorem wireFormula_count_input_fin {n : Nat} {gs : List Gate} (fallback chosen : Fin n)
    (a : Fin (n + gs.length)) (ha : a.val < n) :
    occ chosen (wF fallback gs a.val) =
      if a=iW gs chosen then 1 else 0:=by
  let i : Fin n:=⟨a.val,ha⟩
  have e : i=chosen ↔ a=iW gs chosen:=by
    constructor
    · intro h
      exact Fin.ext (congrArg (fun k : Fin n=>k.val) h)
    · intro h
      exact Fin.ext (congrArg (fun k : Fin (n + gs.length)=>k.val) h)
  change occ chosen (wF fallback gs i.val)=_
  simp only [wireFormula_count_input,e]
theorem cut_factors {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (cut out : Fin (n + gs.length)) (group : Fin n → Prop) (base : Fin n → Bool)
    (controlled : cut=out ∨ ∀ i : Fin n,group i →
      ¬ Relation.ReflTransGen (avoid (rE gs) cut) (iW gs i) out) :
    ∃ outer : Bool → Bool,∀ x : Fin n → Bool,(∀ i,¬ group i → x i=base i) →
      outer (vl gs x cut.val)=vl gs x out.val:=by
  rcases controlled with rfl | blocked
  · exact ⟨id,fun _ _=>rfl⟩
  · exact circuit_cut_factors hcl cut out group base blocked
end PCI
namespace FBR
open Relation
variable {m : Nat} (reads : Fin m → Fin m → Prop) (output : Fin m)
def Branches (v : Fin m) : Prop:=∃ a b,reads v a ∧ reads v b ∧ a ≠ b
def Terminal (v : Fin m) : Prop:=v=output ∨ Branches reads v
def Follow (v w : Fin m) : Prop:=reads v w ∧ ¬ Terminal reads output v
lemma follow_unique {v a b : Fin m} (first : Follow reads output v a) (next : Follow reads output v b) :
    a=b:=by
  by_contra separate
  exact first.2 (Or.inr ⟨a,b,first.1,next.1,separate⟩)
variable (forward : ∀ {v w : Fin m},reads v w → v < w)
variable (live : ∀ v : Fin m,v ≠ output → ∃ w,reads v w)
include forward live in
theorem exists_boundary (v : Fin m) :
    ∃ root : Fin m,Terminal reads output root ∧ ReflTransGen (Follow reads output) v root:=by
  let distance (w : Fin m):=m - w.val
  induction v using (measure distance).wf.induction with
  | h v ih =>
    by_cases terminal : Terminal reads output v
    · exact ⟨v,terminal,ReflTransGen.refl⟩
    obtain ⟨next,edge⟩:=live v (fun e=>terminal (Or.inl e))
    have increase:=forward edge
    have closer : distance next < distance v:=by
      dsimp [distance]
      have bounds:=next.isLt
      change v.val < next.val at increase
      omega
    obtain ⟨root,stopped,route⟩:=ih next closer
    exact ⟨root,stopped,route.head ⟨edge,terminal⟩⟩
include forward in
theorem boundary_unique {v a b : Fin m} (terminalA : Terminal reads output a)
    (terminalB : Terminal reads output b) (routeA : ReflTransGen (Follow reads output) v a)
    (routeB : ReflTransGen (Follow reads output) v b) : a=b:=by
  let distance (w : Fin m):=m - w.val
  induction v using (measure distance).wf.induction generalizing a b with
  | h v ih =>
    rcases routeA.cases_head with h | ⟨next,edge,tailA⟩
    · subst a
      rcases routeB.cases_head with h | ⟨_,edgeB,_⟩
      · exact h
      · exact (edgeB.2 terminalA).elim
    · rcases routeB.cases_head with h | ⟨nextB,edgeB,tailB⟩
      · subst b
        exact (edge.2 terminalB).elim
      have equal:=follow_unique reads output edge edgeB
      subst nextB
      have increase:=forward edge.1
      have closer : distance next < distance v:=by
        dsimp [distance]
        have bounds:=next.isLt
        change v.val < next.val at increase
        omega
      exact ih next closer terminalA terminalB tailA tailB
noncomputable def first (v : Fin m) : Fin m :=
  Classical.choose (exists_boundary reads output forward live v)
theorem first_stops (v : Fin m) : Terminal reads output (first reads output forward live v) :=
  (Classical.choose_spec (exists_boundary reads output forward live v)).1
theorem fPth (v : Fin m) : ReflTransGen (Follow reads output) v (first reads output forward live v) :=
  (Classical.choose_spec (exists_boundary reads output forward live v)).2
theorem fOT {v : Fin m} (stopped : Terminal reads output v) :
    first reads output forward live v=v :=
  boundary_unique reads output forward (first_stops reads output forward live v) stopped
    (fPth reads output forward live v) ReflTransGen.refl
theorem first_of_follows {v w : Fin m} (step : Follow reads output v w) :
    first reads output forward live v=first reads output forward live w :=
  boundary_unique reads output forward (first_stops reads output forward live v)
    (first_stops reads output forward live w) (fPth reads output forward live v)
    ((fPth reads output forward live w).head step)
include forward in
theorem pFwd {v w : Fin m} (route : ReflTransGen reads v w) : v ≤ w:=by
  induction route with
  | refl=>exact le_rfl
  | tail _ edge ih=>exact le_trans ih (le_of_lt (forward edge))
lemma fIRP {v w : Fin m} (route : ReflTransGen (Follow reads output) v w) :
    ReflTransGen reads v w:=by
  induction route with
  | refl=>exact ReflTransGen.refl
  | tail _ edge ih=>exact ih.tail edge.1
theorem first_forward (v : Fin m) : v ≤ first reads output forward live v :=
  pFwd reads forward (fIRP reads output (fPth reads output forward live v))
theorem rBef {v w : Fin m} (route : ReflTransGen reads v w)
    (before : w ≤ first reads output forward live v) :
    ReflTransGen (Follow reads output) v w ∧ first reads output forward live w=first reads output forward live v:=by
  induction route with
  | refl=>exact ⟨ReflTransGen.refl,rfl⟩
  | tail _ edge ih =>
    have predecessorBefore:=lt_of_lt_of_le (forward edge) before
    obtain ⟨tracked,label⟩:=ih (le_of_lt predecessorBefore)
    have step : Follow reads output _ _:=⟨edge,fun stopped=>by
      have self:=fOT reads output forward live stopped
      rw [self] at label
      exact (ne_of_lt predecessorBefore) label⟩
    exact ⟨tracked.tail step,(first_of_follows reads output forward live step).symm.trans label⟩
theorem ancestor_first_le {v w : Fin m} (route : ReflTransGen reads v w)
    (stopped : Terminal reads output w) : first reads output forward live v ≤ w:=by
  by_contra tooLate
  have earlier:=lt_of_not_ge tooLate
  have same:=(rBef reads output forward live route (le_of_lt earlier)).2
  rw [fOT reads output forward live stopped] at same
  exact (ne_of_lt earlier) same
theorem edge_before {v a b : Fin m} (route : ReflTransGen reads v a) (edge : reads a b)
    (bound : b ≤ first reads output forward live v) : Follow reads output a b:=by
  have earlier:=lt_of_lt_of_le (forward edge) bound
  have same:=(rBef reads output forward live route (le_of_lt earlier)).2
  refine ⟨edge,fun stopped=>?_⟩
  rw [fOT reads output forward live stopped] at same
  exact (ne_of_lt earlier) same
def Avoid (cut v w : Fin m) : Prop:=reads v w ∧ v ≠ cut
lemma avoiding_is_read_path (cut : Fin m) {v w : Fin m} (route : ReflTransGen (Avoid reads cut) v w) :
    ReflTransGen reads v w:=by
  induction route with
  | refl=>exact ReflTransGen.refl
  | tail _ edge ih=>exact ih.tail edge.1
theorem avoiding_stays_before {v w : Fin m}
    (route : ReflTransGen (Avoid reads (first reads output forward live v)) v w) :
    w ≤ first reads output forward live v:=by
  induction route with
  | refl=>exact first_forward reads output forward live v
  | tail prior edge ih =>
    have label:=(rBef reads output forward live (avoiding_is_read_path reads _ prior) ih).2
    have earlier:=lt_of_le_of_ne ih edge.2
    have following : Follow reads output _ _:=⟨edge.1,fun terminal=>by
      rw [fOT reads output forward live terminal] at label
      exact (ne_of_lt earlier) label⟩
    have same:=(first_of_follows reads output forward live following).symm.trans label
    rw [← same]
    exact first_forward reads output forward live _
theorem no_avoiding_after {v w : Fin m} (after : first reads output forward live v < w) :
    ¬ ReflTransGen (Avoid reads (first reads output forward live v)) v w :=
  fun route=>(not_lt_of_ge (avoiding_stays_before reads output forward live route)) after
include forward in
theorem unique_follow_predecessor {source a b goal : Fin m}
    (routeA : ReflTransGen (Follow reads output) source a) (edgeA : Follow reads output a goal)
    (routeB : ReflTransGen (Follow reads output) source b) (edgeB : Follow reads output b goal) : a=b:=by
  let distance (w : Fin m):=m - w.val
  induction source using (measure distance).wf.induction generalizing a b with
  | h source ih =>
    rcases routeA.cases_head with aHere | ⟨nextA,stepA,laterA⟩
    · subst a
      rcases routeB.cases_head with bHere | ⟨next,stepB,later⟩
      · exact bHere
      have equal : next=goal:=follow_unique reads output stepB edgeA
      subst next
      have increasing:=pFwd reads forward (fIRP reads output later)
      exact (not_lt_of_ge increasing (forward edgeB.1)).elim
    · rcases routeB.cases_head with bHere | ⟨nextB,stepB,laterB⟩
      · subst b
        have equal : nextA=goal:=follow_unique reads output stepA edgeB
        subst nextA
        have increasing:=pFwd reads forward (fIRP reads output laterA)
        exact (not_lt_of_ge increasing (forward edgeA.1)).elim
      have equal:=follow_unique reads output stepA stepB
      subst nextB
      have increase:=forward stepA.1
      have closer : distance nextA < distance source:=by
        dsimp [distance]
        have bounds:=nextA.isLt
        change source.val < nextA.val at increase
        omega
      exact ih nextA closer laterA edgeA laterB edgeB
theorem unique_predecessor_before {source a b goal : Fin m}
    (bound : goal ≤ first reads output forward live source)
    (routeA : ReflTransGen reads source a) (edgeA : reads a goal)
    (routeB : ReflTransGen reads source b) (edgeB : reads b goal) : a=b:=by
  have aBound:=le_trans (le_of_lt (forward edgeA)) bound
  have bBound:=le_trans (le_of_lt (forward edgeB)) bound
  exact unique_follow_predecessor reads output forward
    (rBef reads output forward live routeA aBound).1
    (edge_before reads output forward live routeA edgeA bound)
    (rBef reads output forward live routeB bBound).1
    (edge_before reads output forward live routeB edgeB bound)
lemma witness_of_positive_sum {α : Type*} (weight : α → Nat) (xs : List α)
    (positive : 0 < (xs.map weight).sum) : ∃ a ∈ xs,0 < weight a:=by
  induction xs with
  | nil=>simp at positive
  | cons a rest ih =>
    by_cases h : 0 < weight a
    · exact ⟨a,by simp,h⟩
    have hr : 0 < (rest.map weight).sum:=by
      simp only [List.map_cons,List.sum_cons] at positive
      omega
    obtain ⟨b,hb,hbPos⟩:=ih hr
    exact ⟨b,by simp [hb],hbPos⟩
lemma sum_le_one_of_unique_positive {α : Type*} (weight : α → Nat) (xs : List α)
    (distinct : xs.Nodup) (small : ∀ a ∈ xs,weight a ≤ 1)
    (unique : ∀ a ∈ xs,∀ b ∈ xs,0 < weight a → 0 < weight b → a=b) :
    (xs.map weight).sum ≤ 1:=by
  induction xs with
  | nil=>simp
  | cons a rest ih =>
    simp only [List.nodup_cons] at distinct
    simp only [List.map_cons,List.sum_cons]
    by_cases h : weight a=0
    · rw [h,Nat.zero_add]
      exact ih distinct.2 (fun b hb=>small b (by simp [hb]))
        (fun b hb c hc=>unique b (by simp [hb]) c (by simp [hc]))
    have restZero : (rest.map weight).sum=0:=by
      by_contra some
      obtain ⟨b,hb,hbPos⟩:=witness_of_positive_sum weight rest (by omega)
      have equal:=unique a (by simp) b (by simp [hb]) (by omega) hbPos
      exact distinct.1 (by simpa [equal] using hb)
    rw [restZero,Nat.add_zero]
    exact small a (by simp)
section Count
variable (parents : Fin m → List (Fin m))
variable (reads_parent : ∀ a b : Fin m,reads a b ↔ a ∈ parents b)
variable (weight : Fin m → Nat) (source : Fin m)
variable (other_weight : ∀ v : Fin m,v ≠ source → weight v=((parents v).map weight).sum)
include forward reads_parent other_weight in
theorem weight_positive_path {v : Fin m} (positive : 0 < weight v) : ReflTransGen reads source v:=by
  revert positive
  induction v using (measure (fun w : Fin m=>w.val)).wf.induction with
  | h v ih =>
    intro positive
    by_cases isSource : v=source
    · subst v
      exact ReflTransGen.refl
    rw [other_weight v isSource] at positive
    obtain ⟨a,member,hp⟩:=witness_of_positive_sum weight (parents v) positive
    have edge:=(reads_parent a v).mpr member
    have earlier:=forward edge
    exact (ih a earlier hp).tail edge
include reads_parent other_weight in
theorem weight_before_le_one (rootWeight : weight source=1) (distinct : ∀ v,(parents v).Nodup)
    {v : Fin m} (bound : v ≤ first reads output forward live source) : weight v ≤ 1:=by
  revert bound
  induction v using (measure (fun w : Fin m=>w.val)).wf.induction with
  | h v ih =>
    intro bound
    by_cases isSource : v=source
    · subst v
      exact le_of_eq rootWeight
    rw [other_weight v isSource]
    apply sum_le_one_of_unique_positive weight (parents v) (distinct v)
    · intro a member
      have earlier:=forward ((reads_parent a v).mpr member)
      exact ih a earlier (le_trans (le_of_lt earlier) bound)
    · intro a ma b mb ha hb
      exact unique_predecessor_before reads output forward live bound
        (weight_positive_path reads forward parents reads_parent weight source other_weight ha)
        ((reads_parent a v).mpr ma)
        (weight_positive_path reads forward parents reads_parent weight source other_weight hb)
        ((reads_parent b v).mpr mb)
end Count
end FBR
namespace PFG
open PEqualNP.CircuitLowerBounds
open CP
open PCF PCI PCT PSc
noncomputable def fIB {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length),w ≠ out → ∃ v,rE gs w v)
    (i : Fin n) : Fin (n + gs.length) :=
  FBR.first (rE gs) out (rOrd clean) live (iW gs i)
noncomputable def fIG {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length),w ≠ out → ∃ v,rE gs w v)
    (cut : Fin (n + gs.length)) : Finset (Fin n) :=
  Finset.univ.filter fun i=>fIB clean out live i=cut
theorem mem_firstInputGroup {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length),w ≠ out → ∃ v,rE gs w v)
    (cut : Fin (n + gs.length)) (i : Fin n) :
    i ∈ fIG clean out live cut ↔ fIB clean out live i=cut:=by
  simp [fIG]
theorem wLO {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length),w ≠ out → ∃ v,rE gs w v)
    (w : Fin (n + gs.length)) : w ≤ out:=by
  let last : Fin (n + gs.length):=⟨n + gs.length - 1,by have:=out.isLt;omega⟩
  have top (v : Fin (n + gs.length)) : v ≤ last:=by
    change v.val ≤ n + gs.length - 1
    have:=v.isLt
    omega
  have lastOut : last=out:=by
    by_contra notOutput
    obtain ⟨v,e⟩:=live last notOutput
    exact (not_lt_of_ge (top v)) (rOrd clean e)
  exact lastOut ▸ top w
theorem firstInputBoundary_occurrences_le_one {n : Nat} {gs : List Gate}
    (clean : CleanL n gs) (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length),w ≠ out → ∃ v,rE gs w v)
    (distinct : ∀ w,(prds clean w).Nodup)
    (fallback chosen : Fin n) :
    occ chosen (wF fallback gs (fIB clean out live chosen).val)
      ≤ 1:=by
  let weight (a : Fin (n + gs.length)):=occ chosen (wF fallback gs a.val)
  have sourcePrimary : (iW gs chosen).val < n:=chosen.isLt
  have atSource : weight (iW gs chosen)=1:=by
    dsimp [weight]
    rw [wireFormula_count_input_fin fallback chosen _ sourcePrimary,ite_eq_left rfl]
  have otherWeight : ∀ w : Fin (n + gs.length),w ≠ iW gs chosen →
      weight w=((prds clean w).map weight).sum:=by
    intro w other
    by_cases primary : w.val < n
    · simp [weight,wireFormula_count_input_fin fallback chosen w primary,other,
        predecessors_nil_input clean w primary]
    · let p:=w.val - n
      have hp : p < gs.length:=by have:=w.isLt;dsimp [p];omega
      have hw : w.val=n + p:=by dsimp [p];omega
      let g:=gs[p]
      have atSlot : gs[p]?=some g:=List.getElem?_eq_getElem hp
      exact wireFormula_count_gate_fin fallback chosen clean atSlot hw _
        (predecessors_val_gate clean w atSlot hw)
  exact FBR.weight_before_le_one (rE gs) out (rOrd clean) live
    (prds clean) (fun a b=>(predecessors_mem clean a b).symm) weight
    (iW gs chosen) otherWeight atSource distinct le_rfl
theorem fIGc {n : Nat} {gs : List Gate}
    (clean : CleanL n gs) (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length),w ≠ out → ∃ v,rE gs w v)
    (cut : Fin (n + gs.length)) :
    cut=out ∨ ∀ k : Fin n,k ∈ fIG clean out live cut →
      ¬ Relation.ReflTransGen (avoid (rE gs) cut) (iW gs k) out:=by
  by_cases terminal : cut=out
  · exact Or.inl terminal
  right
  intro k member path
  have before : cut < out:=lt_of_le_of_ne (wLO clean out live cut) terminal
  have firstHere:=(mem_firstInputGroup clean out live cut k).mp member
  have after : fIB clean out live k < out:=by rwa [firstHere]
  have blocked:=FBR.no_avoiding_after (rE gs) out
    (rOrd clean) live after
  apply blocked
  change Relation.ReflTransGen (FBR.Avoid (rE gs)
    (fIB clean out live k)) (iW gs k) out
  rw [firstHere]
  exact Relation.ReflTransGen.mono (fun _ _ e=>⟨e.1,e.2.1⟩) _ _ path
end PFG
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CP CP.Readers
open scoped BigOperators
def operands (gs : List Gate) : List Nat:=gs.flatMap Gate.inputs
def ngC (gs : List Gate) : Nat:=(gs.filter fun g=>isNotGate g.op).length
theorem operand_mem_of_read {gs : List Gate} {slot wire : Nat} (read : Reads gs slot wire) :
    wire ∈ operands gs:=by
  obtain ⟨g,gAt,before⟩:=read
  exact List.mem_flatMap.mpr ⟨g,List.mem_iff_getElem?.mpr ⟨slot,gAt⟩,before⟩
theorem two_readers_operand_count {gs : List Gate} {wire p q : Nat}
    (neq : p ≠ q) (first : Reads gs p wire) (second : Reads gs q wire) :
    2 ≤ (operands gs).count wire:=by
  induction gs generalizing p q with
  | nil =>
    rcases first with ⟨g,atGate,_⟩
    simp at atGate
  | cons a rest ih =>
    simp only [operands,List.flatMap_cons,List.count_append]
    cases p with
    | zero =>
      cases q with
      | zero=>exact (neq rfl).elim
      | succ q =>
        have atA : wire ∈ a.inputs:=by simpa [Reads] using first
        have later : Reads rest q wire:=by simpa [Reads] using second
        have aPos : 0 < a.inputs.count wire:=List.count_pos_iff.mpr atA
        have restPos : 0 < (operands rest).count wire:=List.count_pos_iff.mpr (operand_mem_of_read later)
        simp only [operands] at restPos
        omega
    | succ p =>
      cases q with
      | zero =>
        have atA : wire ∈ a.inputs:=by simpa [Reads] using second
        have later : Reads rest p wire:=by simpa [Reads] using first
        have aPos : 0 < a.inputs.count wire:=List.count_pos_iff.mpr atA
        have restPos : 0 < (operands rest).count wire:=List.count_pos_iff.mpr (operand_mem_of_read later)
        simp only [operands] at restPos
        omega
      | succ q =>
        have early : Reads rest p wire:=by simpa [Reads] using first
        have late : Reads rest q wire:=by simpa [Reads] using second
        have different : p ≠ q:=fun eq=>neq (congrArg Nat.succ eq)
        have count:=ih different early late
        simp only [operands] at count
        omega
theorem operands_count_length (gs : List Gate)
    (arity : ∀ g ∈ gs,g.inputs.length + (if isNotGate g.op then 1 else 0)=2) :
    (operands gs).length + ngC gs=2 * gs.length:=by
  induction gs with
  | nil=>simp [operands,ngC]
  | cons g gs ih =>
    have gArity:=arity g (by simp)
    have rest:=ih (fun q hq=>arity q (List.mem_cons_of_mem _ hq))
    cases h : isNotGate g.op
    · simp [h] at gArity
      simp [operands,ngC,h] at rest ⊢
      omega
    · simp [h] at gArity
      simp [operands,ngC,h] at rest ⊢
      omega
theorem clean_gate_arity {n : Nat} {gs : List Gate} (h : CleanL n gs) :
    ∀ g ∈ gs,g.inputs.length + (if isNotGate g.op then 1 else 0)=2:=by
  intro g gMem
  obtain ⟨p,atGate⟩:=List.mem_iff_getElem?.mp gMem
  rcases h p g atGate with ⟨op,a,_,args⟩ | ⟨ops,a,b,_,_,args⟩
  · simp [op,args,isNotGate]
  · rcases ops with op | op<;>simp [op,args,isNotGate]
theorem branch_card_add_wire_card_le_operands (gs : List Gate) (branches : Finset Nat)
    (twice : ∀ w ∈ branches,2 ≤ (operands gs).count w) :
    branches.card + (operands gs).toFinset.card ≤ (operands gs).length:=by
  classical
  let W:=(operands gs).toFinset
  have subset : branches ⊆ W:=by
    intro w wm
    have t:=twice w wm
    exact List.mem_toFinset.mpr (List.count_pos_iff.mp (by omega))
  have aux : (∑ w ∈ W,if w ∈ branches then (1 : Nat) else 0)=branches.card:=by
    have same : (∑ w ∈ W,if w ∈ branches then (1 : Nat) else 0) =
        ∑ w ∈ branches,if w ∈ branches then (1 : Nat) else 0:=by
      symm
      apply Finset.sum_subset subset
      intro w _ notBranch
      simp [notBranch]
    rw [same]
    simp
  have total : (∑ w ∈ W,(operands gs).count w)=(operands gs).length :=
    List.sum_toFinset_count_eq_length _
  have bound : (∑ w ∈ W,((if w ∈ branches then (1 : Nat) else 0) + 1)) ≤
      ∑ w ∈ W,(operands gs).count w:=by
    apply Finset.sum_le_sum
    intro w wIn
    by_cases b : w ∈ branches
    · simpa [b] using twice w b
    · have pos : 0 < (operands gs).count w:=List.count_pos_iff.mpr (List.mem_toFinset.mp wIn)
      simpa [b] using pos
  rw [Finset.sum_add_distrib,aux,total] at bound
  simpa [W] using bound
theorem bBudg {n out : Nat} {gs : List Gate} (clean : CleanL n gs)
    (outValid : out < n + gs.length)
    (everyNonoutputUsed : ∀ w < n + gs.length,w ≠ out → ∃ p,Reads gs p w)
    (branches : Finset Nat)
    (twoReaders : ∀ w ∈ branches,∃ p q,p ≠ q ∧ Reads gs p w ∧ Reads gs q w) :
    branches.card + (n + gs.length - 1) + ngC gs ≤ 2 * gs.length:=by
  let W:=(operands gs).toFinset
  let required:=(Finset.range (n + gs.length)).erase out
  have requiredUsed : required ⊆ W:=by
    intro w inSet
    have spec:=Finset.mem_erase.mp inSet
    obtain ⟨p,read⟩:=everyNonoutputUsed w (Finset.mem_range.mp spec.2) spec.1
    exact List.mem_toFinset.mpr (operand_mem_of_read read)
  have numRequired : required.card=n + gs.length - 1:=by
    change ((Finset.range (n + gs.length)).erase out).card=_
    rw [Finset.card_erase_of_mem (Finset.mem_range.mpr outValid),Finset.card_range]
  have twice : ∀ w ∈ branches,2 ≤ (operands gs).count w:=by
    intro w mem
    obtain ⟨p,q,different,pReads,qReads⟩:=twoReaders w mem
    exact two_readers_operand_count different pReads qReads
  have up:=branch_card_add_wire_card_le_operands gs branches twice
  have used:=Finset.card_le_card requiredUsed
  rw [numRequired] at used
  have total:=operands_count_length gs (clean_gate_arity clean)
  change n + gs.length - 1 ≤ (operands gs).toFinset.card at used
  omega
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CP CP.Readers
open PCT
theorem lREL {n out : Nat} {gs : List Gate}
    {f : (Fin n → Bool) → Bool} (least : Least n f gs out) (nonnull : ∃ x y,f x ≠ f y)
    (dependent : ∀ v : Fin n,Dep f v)
    (stillNonconstant : ∀ (v : Fin n) (b : Bool),∃ x y,
      f (Function.update x v b) ≠ f (Function.update y v b))
    (outValid : out < n + gs.length) :
    ∀ w : Fin (n + gs.length),w ≠ (⟨out,outValid⟩ : Fin (n + gs.length)) → ∃ v,rE gs w v:=by
  intro w notOutput
  have notSame : w.val ≠ out:=fun eq=>notOutput (Fin.ext eq)
  obtain ⟨p,g,atSlot,reads,bound⟩ :=
    least_wire_readers_in_range least nonnull dependent stillNonconstant w notSame
  exact ⟨⟨n + p,bound⟩,p,g,atSlot,rfl,reads⟩
theorem bsRE {n : Nat} {gs : List Gate} {w : Fin (n + gs.length)}
    (fork : FBR.Branches (rE gs) w) :
    ∃ p q,p ≠ q ∧ Reads gs p w.val ∧ Reads gs q w.val:=by
  obtain ⟨first,next,pRead,qRead,separate⟩:=fork
  obtain ⟨p,g,atP,src,ap⟩:=pRead
  obtain ⟨q,h,atQ,dst,aq⟩:=qRead
  refine ⟨p,q,?_,⟨g,atP,ap⟩,⟨h,atQ,aq⟩⟩
  intro same
  subst q
  exact separate (Fin.ext (src.trans dst.symm))
noncomputable def cBW {n : Nat} (gs : List Gate) : Finset (Fin (n + gs.length)):=by
  classical
  exact (Finset.univ).filter fun w=>FBR.Branches (rE gs) w
theorem inCB {n : Nat} {gs : List Gate} {w : Fin (n + gs.length)} :
    w ∈ cBW gs ↔ FBR.Branches (rE gs) w:=by
  classical
  simp [cBW]
namespace PCT
open PEqualNP.CircuitLowerBounds CP
open Relation
theorem aoIA {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (x y : Fin n → Bool) (w : Fin (n + gs.length))
    (agrees : ∀ i,ReflTransGen (rE gs) (iW gs i) w → x i=y i) :
    vl gs x w.val=vl gs y w.val:=by
  revert agrees
  induction w using (measure (fun a : Fin (n + gs.length)=>a.val)).wf.induction with
  | h w earlier =>
    intro agree
    by_cases input : w.val < n
    · let i : Fin n:=⟨w.val,input⟩
      have name : iW gs i=w:=Fin.ext rfl
      have atInput : ReflTransGen (rE gs) (iW gs i) w:=by
        simpa only [name] using (ReflTransGen.refl : ReflTransGen (rE gs) w w)
      have a:=agree i atInput
      simpa only [vl_input gs x w.val input,vl_input gs y w.val input] using a
    · let p:=w.val - n
      have pLt : p < gs.length:=by have:=w.isLt;dsimp [p];omega
      have gateWire : w.val=n + p:=by dsimp [p];omega
      let g:=gs[p]'pLt
      have atGate : gs[p]?=some g:=List.getElem?_eq_getElem pLt
      rw [gateWire]
      apply vl_congr gs clean x y p g atGate
      intro a inGate
      have readBefore:=(clean p g atGate).lt a inGate
      let wire : Fin (n + gs.length):=⟨a,by have:=w.isLt;omega⟩
      have read : rE gs wire w:=⟨p,g,atGate,gateWire,inGate⟩
      apply earlier wire (show wire.val < w.val by change a < w.val;omega)
      intro i path
      exact agree i (path.tail read)
end PCT
lemma nnAn (gs : List Gate) :
    nnC gs + (gs.filter (fun g=>isNotGate g.op)).length=gs.length:=by
  rw [← List.countP_eq_length_filter]
  induction gs with
  | nil=>simp [nnC]
  | cons g gs ih =>
    simp only [nnC,List.countP_cons,List.length_cons] at ih ⊢
    cases h : isNotGate g.op<;>simp [h]<;>omega
open PEqualNP.CircuitLowerBounds CP CP.Readers
open PCT PFG
theorem tFOB {gs : List Gate} (clean : CleanL 10 gs)
    (out : Fin (10 + gs.length))
    (live : ∀ w : Fin (10 + gs.length),w ≠ out → ∃ v,rE gs w v)
    (budget : nnC gs ≤ 12) : (cBW (n:=10) gs).card ≤ 3:=by
  classical
  let branches:=cBW (n:=10) gs
  have h:=bBudg clean out.isLt (fun w hw hne=>by
      let wire : Fin (10 + gs.length):=⟨w,hw⟩
      obtain ⟨v,p,g,hg,_,hw'⟩:=live wire (fun e=>hne (congrArg Fin.val e))
      exact ⟨p,g,hg,hw'⟩)
    (branches.image Fin.val) (fun w hw=>by
      obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hw
      exact bsRE (inCB.mp hv))
  rw [Finset.card_image_of_injective _ Fin.val_injective] at h
  have count:=nnAn gs
  change nnC gs + ngC gs=gs.length at count
  change branches.card ≤ 3
  omega
namespace F27
def target (x : Fin 10 → Bool) : Bool :=
  (x 0&&x 1)||(x 1&&x 2)||(x 2&&x 3)||(x 3&&x 4) ||
  (x 4&&x 0)||(x 0&&x 5)||(x 1&&x 6)||(x 2&&x 7) ||
  (x 3&&x 8)||(x 5&&x 7)||(x 6&&x 8)||(x 8&&x 5)
def valid (x : Fin 10 → Bool) : Prop:=x 9=(x 0||x 3)
def row (m : ℕ) (i : Fin 10) : Bool:=m.testBit i.val
def cube (i j k : Fin 10) (a b c : ℕ) : Prop :=
  let hi m:=Function.update (row m) k true
  (∀ v,v ≠ i → v ≠ j → row a v=row b v ∧ row b v=row c v) ∧
  valid (row a) ∧ valid (row b) ∧ valid (hi a) ∧ valid (hi b) ∧ valid (hi c) ∧
  target (row a) ≠ target (row b) ∧ target (hi a) ≠ target (hi c) ∧ target (hi b) ≠ target (hi c)
def flag (v0 v1 v2 v5 v6 v7 v8 : BitVec 2) : Bool :=
  decide (v0 ≠ v1) &&
  decide (v1 ≠ v2) &&
  decide (v0 ≠ v5) &&
  decide (v1 ≠ v6) &&
  decide (v2 ≠ v7) &&
  decide (v5 ≠ v7) &&
  decide (v5 ≠ v8) &&
  decide (v6 ≠ v8) &&
  decide (v0=v2 → v1 ≤ v0) &&
  decide (v0=v2 → v5 ≤ v0) &&
  decide (v0=v6 → v1 ≤ v0) &&
  decide (v0=v7 → v5 ≤ v0) &&
  decide (v0=v8 → v5 ≤ v0) &&
  decide (v1=v5 → v0 ≤ v1) &&
  decide (v1=v7 → v2 ≤ v1) &&
  decide (v1=v8 → v6 ≤ v1) &&
  decide (v2=v5 → v7 ≤ v2) &&
  decide (v2=v6 → v1 ≤ v2) &&
  decide (v2=v6 → v7 ≤ v2) &&
  decide (v2=v8 → v6 ≤ v2) &&
  decide (v5=v6 → v8 ≤ v5) &&
  decide (v6=v7 → v8 ≤ v6) &&
  decide (v7=v8 → v2 ≤ v7)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 10000000 in
lemma badFlags : ∀ (v0 v1 v2 v5 v6 v7 v8 : BitVec 2),flag v0 v1 v2 v5 v6 v7 v8=false:=by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 10000000 in
lemma noRanks (v0 v1 v2 v5 v6 v7 v8 : BitVec 2)
    (c0 : v0 ≠ v1)
    (c1 : v1 ≠ v2)
    (c2 : v0 ≠ v5)
    (c3 : v1 ≠ v6)
    (c4 : v2 ≠ v7)
    (c5 : v5 ≠ v7)
    (c6 : v5 ≠ v8)
    (c7 : v6 ≠ v8)
    (h0 : v0=v2 → v1 ≤ v0)
    (h1 : v0=v2 → v5 ≤ v0)
    (h2 : v0=v6 → v1 ≤ v0)
    (h3 : v0=v7 → v5 ≤ v0)
    (h4 : v0=v8 → v5 ≤ v0)
    (h5 : v1=v5 → v0 ≤ v1)
    (h6 : v1=v7 → v2 ≤ v1)
    (h7 : v1=v8 → v6 ≤ v1)
    (h8 : v2=v5 → v7 ≤ v2)
    (h9 : v2=v6 → v1 ≤ v2)
    (h10 : v2=v6 → v7 ≤ v2)
    (h11 : v2=v8 → v6 ≤ v2)
    (h12 : v5=v6 → v8 ≤ v5)
    (h13 : v6=v7 → v8 ≤ v6)
    (h14 : v7=v8 → v2 ≤ v7)
    : False:=by
  have h:=badFlags v0 v1 v2 v5 v6 v7 v8
  simp_all [flag]
end F27
namespace C27
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CP PCF PCI PFG PCT PSc
def pairs : List (Fin 10 × Fin 10) :=
  [(0,1),(1,2),(2,3),(0,5),(1,6),(2,7),(5,7),(3,8),(5,8),(6,8)]
def value (x : Fin 10 → Bool) : Bool :=
  (x 0&&x 1)||(x 1&&x 2)||(x 2&&x 3)||(x 3&&x 4)||(x 4&&x 0) ||
  (x 0&&x 5)||(x 1&&x 6)||(x 2&&x 7)||(x 3&&x 8)||(x 5&&x 7) ||
  (x 6&&x 8)||(x 8&&x 5)
def contexts (e : Fin 10 × Fin 10) : Nat × Nat :=
  match e.1.val,e.2.val with
  | 0,1=>(520,616)
  | 1,2=>(0,192)
  | 2,3=>(513,897)
  | 0,5=>(520,650)
  | 1,6=>(0,260)
  | 2,7=>(0,34)
  | 5,7=>(0,260)
  | 3,8=>(513,581)
  | 5,8=>(0,192)
  | _,_=>(0,34)
def bits (v : Nat) (i : Fin 10):=v.testBit i.val
theorem checkedContexts : ∀ e ∈ pairs,∀ (a b : Bool),
    let xa:=pairInput e.1 e.2 (bits (contexts e).1) a b
    let xo:=pairInput e.1 e.2 (bits (contexts e).2) a b
    xa 9=(xa 0||xa 3) ∧ value xa=(a&&b) ∧
      xo 9=(xo 0||xo 3) ∧ value xo=(a||b):=by
  decide +kernel
theorem bCfl {gs : List Gate} (clean : CleanL 10 gs)
    (out : Fin (10 + gs.length))
    (live : ∀ w : Fin (10 + gs.length),w ≠ out → ∃ v,rE gs w v)
    (distinct : ∀ w,(prds clean w).Nodup)
    (computes : ∀ x : Fin 10 → Bool,x 9=(x 0||x 3) → vl gs x out.val=value x)
    (e : Fin 10 × Fin 10) (he : e ∈ pairs) :
    fIB clean out live e.1 ≠ fIB clean out live e.2:=by
  intro same
  let cut:=fIB clean out live e.1
  have hi:=firstInputBoundary_occurrences_le_one clean out live distinct e.1 e.1
  have hj:=firstInputBoundary_occurrences_le_one clean out live distinct e.1 e.2
  rw [← same] at hj
  have controlled : cut=out ∨ ∀ k : Fin 10,(k=e.1 ∨ k=e.2) →
      ¬ Relation.ReflTransGen (avoid (rE gs) cut) (iW gs k) out:=by
    rcases fIGc clean out live cut with h | h
    · exact Or.inl h
    · apply Or.inr
      intro k hk
      apply h
      apply (mem_firstInputGroup clean out live cut k).mpr
      rcases hk with hk | hk
      · rw [hk]
      · rw [hk]
        exact same.symm
  have factor (base : Fin 10 → Bool) : ∃ outer : Bool → Bool,∀ a b,
      outer (pairValue e.1 e.2 base (wF e.1 gs cut.val) a b) =
        vl gs (pairInput e.1 e.2 base a b) out.val:=by
    obtain ⟨outer,ho⟩:=cut_factors clean cut out (fun k=>k=e.1 ∨ k=e.2) base controlled
    refine ⟨outer,fun a b=>?_⟩
    unfold pairValue
    rw [wireFormula_eval e.1 clean _ cut.val cut.isLt]
    apply ho
    intro k hk
    simp [pairInput,show k ≠ e.1 from fun h=>hk (Or.inl h),
      show k ≠ e.2 from fun h=>hk (Or.inr h)]
  obtain ⟨fa,ha⟩:=factor (bits (contexts e).1)
  obtain ⟨fo,ho⟩:=factor (bits (contexts e).2)
  apply fixed_pair_invariant e.1 e.2 (wF e.1 gs cut.val) hi hj _ _ fa fo
  · intro a b
    have h:=checkedContexts e he a b
    exact (ha a b).trans ((computes _ h.1).trans h.2.1)
  · intro a b
    have h:=checkedContexts e he a b
    exact (ho a b).trans ((computes _ h.2.2.1).trans h.2.2.2)
end C27
namespace B2K
def X0 : ℕ:=12297829382473034410
def X1 : ℕ:=14757395258967641292
def X2 : ℕ:=17361641481138401520
def X5 : ℕ:=18374966859414961920
def X8 : ℕ:=18446462603027742720
def X9 : ℕ:=18446744072277895850
def ALL64 : ℕ:=18446744073709551615
def IND_LOW : ℕ:=3609911
def IND_3 : ℕ:=5527622909952
def IND_SAFE : ℕ:=5527626519863
def E01 : ℕ:=8
def E12 : ℕ:=64
def E05 : ℕ:=512
def E58 : ℕ:=16777216
def R1_3 : ℕ:=18446727515178967200
def R1_4 : ℕ:=18446744072277895850
def R1_6 : ℕ:=18446687779573189836
def R1_7 : ℕ:=18442521884633399280
def R0_3 : ℕ:=5527622909952
def R0_4 : ℕ:=1381653
def R0_6 : ℕ:=4294971699
def R0_7 : ℕ:=4295426055
def bWs : List ℕ:=[X0,X1,X2,X5,X8,X9]
def pOs : List ℕ:=[12297829382473034410,14757395258967641292,17216961135462248174,17361641481138401520,18085043209519168250,18229723555195321596,18374403900871474942,18374966859414961920,18422818335611355050,18432388630850633676,18441958926089912302,18442521884633399280,18445336677350834170,18445899635894321148,18446462594437808126,18446462603027742720,18446650250148948650,18446687779573189836,18446725308997431022,18446727516610621680,18446738554676574970,18446740762289765628,18446742969902956286,18446742978492890880,18446743708637331370,18446743854666219468,18446744000695107566,18446744009285042160,18446744052234715130,18446744060824649724,18446744069414584318,18446744072277895850,18446744073423220462,18446744073625336570,18446744073692708606,18446744073703980970,18446744073708437486,18446744073709223930,18446744073709486078,18446744073709529770,18446744073709547246,18446744073709550330,18446744073709551358,18446744073709551530,18446744073709551598,18446744073709551610,18446744073709551614]
def pSafe3 : List ℕ:=[0,17361641481138401520,18446462603027742720,18446727516610621680]
def pSafe4 : List ℕ:=[0,12297829382473034410,18446744072277895850]
def pSafe6 : List ℕ:=[0,14757395258967641292,18446462603027742720,18446687779573189836]
def pSafe7 : List ℕ:=[0,17361641481138401520,18374966859414961920,18442521884633399280]
def edgesOf (z : ℕ) : ℕ :=
  (if (z&&&E01) != 0 then 1 else 0) |||
  (if (z&&&E12) != 0 then 2 else 0) |||
  (if (z&&&E05) != 0 then 4 else 0) |||
  (if (z&&&E58) != 0 then 8 else 0)
def cWF (ys : List ℕ) (F : ℕ) : ℕ :=
  ys.foldl (fun acc y =>
    let z:=y&&&F
    if (z&&&IND_SAFE)==0 then acc|||edgesOf z else acc) 0
def rR1 (m : ℕ) : ℕ :=
  (if (m&&&1) != 0 then R1_3 else 0) |||
  (if (m&&&2) != 0 then R1_4 else 0) |||
  (if (m&&&4) != 0 then R1_6 else 0) |||
  (if (m&&&8) != 0 then R1_7 else 0)
def pureValid (m : ℕ) : List ℕ :=
  let r:=rR1 m
  pOs.filter (fun p=>(p&&&r)==r)
def nested (a b : ℕ) : Bool:=(a&&&b)==a||(a&&&b)==b
def vS5 (s0 s1 s2 s3 s4 : ℕ) : List ℕ :=
  let ss:=[s0,s1,s2,s3,s4]
  (List.range 32).filter fun sub =>
    let idxs:=(List.range 5).filter (fun i=>((sub>>>i)&&&1) != 0)
    idxs.all (fun i=>idxs.all (fun j=>nested (ss.getD i 0) (ss.getD j 0)))
def cM5 (sub b0 b1 b2 b3 b4 : ℕ) : ℕ :=
  let f0:=if (sub&&&1) != 0 then b0 else ALL64
  let f1:=if (sub&&&2) != 0 then f0&&&b1 else f0
  let f2:=if (sub&&&4) != 0 then f1&&&b2 else f1
  let f3:=if (sub&&&8) != 0 then f2&&&b3 else f2
  if (sub&&&16) != 0 then f3&&&b4 else f3
def checkChainCov5 (subs : List ℕ) (b0 b1 b2 b3 b4 : ℕ) : Bool :=
  let cov:=subs.foldl (fun acc sub =>
    acc|||cWF bWs (cM5 sub b0 b1 b2 b3 b4)) 0
  cov != 15
def checkLam5Tuple (t : ℕ × ℕ × ℕ × ℕ × ℕ) : Bool :=
  let (s0,s1,s2,s3,s4):=t
  let rem4:=s0|||s1|||s2|||s3
  let rem3:=s0|||s1|||s2
  let rem2:=s0|||s1
  let rem1:=s0
  let p0:=pureValid s0
  let p1:=pureValid s1
  let p2:=pureValid s2
  let p3:=pureValid s3
  let p4:=pureValid s4
  let subs:=vS5 s0 s1 s2 s3 s4
  let finOk (rem : ℕ) (i3 i4 i6 i7 : ℕ) : Bool :=
    ((rem&&&1) != 0||(i3&&&R0_3)==0) &&
    ((rem&&&2) != 0||(i4&&&R0_4)==0) &&
    ((rem&&&4) != 0||(i6&&&R0_6)==0) &&
    ((rem&&&8) != 0||(i7&&&R0_7)==0)
  let upd (s b i3 i4 i6 i7 : ℕ) : ℕ × ℕ × ℕ × ℕ :=
    (if (s&&&1) != 0 then i3&&&b else i3,
     if (s&&&2) != 0 then i4&&&b else i4,
     if (s&&&4) != 0 then i6&&&b else i6,
     if (s&&&8) != 0 then i7&&&b else i7)
  p4.all fun b4 =>
    let (a3,a4,a6,a7):=upd s4 b4 ALL64 ALL64 ALL64 ALL64
    if !finOk rem4 a3 a4 a6 a7 then true else
  p3.all fun b3 =>
    let (c3,c4,c6,c7):=upd s3 b3 a3 a4 a6 a7
    if !finOk rem3 c3 c4 c6 c7 then true else
  p2.all fun b2 =>
    let (d3,d4,d6,d7):=upd s2 b2 c3 c4 c6 c7
    if !finOk rem2 d3 d4 d6 d7 then true else
  p1.all fun b1 =>
    let (e3,e4,e6,e7):=upd s1 b1 d3 d4 d6 d7
    if !finOk rem1 e3 e4 e6 e7 then true else
  p0.all fun b0 =>
    let (f3,f4,f6,f7):=upd s0 b0 e3 e4 e6 e7
    if !finOk 0 f3 f4 f6 f7 then true else
    checkChainCov5 subs b0 b1 b2 b3 b4
def lam5List : List (ℕ × ℕ × ℕ × ℕ × ℕ):=[(1,1,2,4,8),(1,1,3,4,8),(1,2,2,4,8),(1,2,3,4,8),(1,2,4,4,8),(1,2,4,5,8),(1,2,4,6,8),(1,2,4,7,8),(1,2,4,8,8),(1,2,4,8,9),(1,2,4,8,10),(1,2,4,8,11),(1,2,4,8,12),(1,2,4,8,13),(1,2,4,8,14),(1,2,4,8,15),(1,3,3,4,8),(1,3,4,4,8),(1,3,4,7,8),(1,3,4,8,8),(1,3,4,8,11),(1,3,4,8,12),(1,3,4,8,15)]
def isLP (a b : ℕ) : Bool:=(a&&&b)==0||(a&&&b)==a||(a&&&b)==b
def insNat (v : ℕ) : List ℕ → List ℕ
  | []=>[v]
  | y :: ys=>if v <= y then v :: y :: ys else y :: insNat v ys
def sort5 (a b c d e : ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ :=
  let s:=[a,b,c,d,e].foldl (fun acc x=>insNat x acc) []
  (s.getD 0 0,s.getD 1 0,s.getD 2 0,s.getD 3 0,s.getD 4 0)
def checkLam5From4 : Bool :=
  let xs:=(List.range 15).map (· + 1)
  ([2,3] : List ℕ).all fun m4 =>
    xs.all fun x =>
      !isLP m4 x||lam5List.elem (sort5 1 m4 4 8 x)
theorem checkLam5From4_true : checkLam5From4=true:=by decide +kernel
set_option maxHeartbeats 8000000 in
theorem test_AW0_aU5 : lam5List.all checkLam5Tuple=true:=by decide +kernel
def validBs (ps : List ℕ) (r1 r0 g0 : ℕ) : List ℕ :=
  ps.foldl (fun acc p =>
    let acc1:=if p != 0&&(p&&&r1)==r1&&(p&&&r0)==0 then p :: acc else acc
    let w:=p|||g0
    if w != 0&&(w&&&r1)==r1&&(w&&&r0)==0 then w :: acc1 else acc1) []
def checkAW1_aU4_pair (a b : ℕ) : Bool :=
  let g0:=a&&&b
  let ys:=g0 :: bWs
  let vb3:=validBs pSafe3 R1_3 R0_3 g0
  let vb4:=validBs pSafe4 R1_4 R0_4 g0
  let vb6:=validBs pSafe6 R1_6 R0_6 g0
  let vb7:=validBs pSafe7 R1_7 R0_7 g0
  let c0:=cWF ys ALL64
  let c3:=vb3.foldl (fun acc f=>acc|||cWF ys f) c0
  let c4:=vb4.foldl (fun acc f=>acc|||cWF ys f) c3
  let c6:=vb6.foldl (fun acc f=>acc|||cWF ys f) c4
  let c7:=vb7.foldl (fun acc f=>acc|||cWF ys f) c6
  let c34:=vb3.foldl (fun acc f3=>vb4.foldl (fun acc2 f4=>acc2|||cWF ys (f3&&&f4)) acc) c7
  c34 != 15
def checkPairs : List ℕ → Bool
  | []=>true
  | a :: rest=>(a :: rest).all (fun b=>checkAW1_aU4_pair a b)&&checkPairs rest
set_option maxHeartbeats 8000000 in
theorem test_AW1_aU4 : checkPairs pOs=true:=by decide +kernel
theorem pureOrs_props :
    bWs.all (fun w=>pOs.elem w)=true ∧
    pOs.all (fun a=>pOs.all (fun b=>pOs.elem (a|||b)))=true ∧
    pOs.all (fun p =>
      let b0:=(if (p&&&X0)==X0 then X0 else 0) |||
                (if (p&&&X1)==X1 then X1 else 0) |||
                (if (p&&&X2)==X2 then X2 else 0) |||
                (if (p&&&X5)==X5 then X5 else 0) |||
                (if (p&&&X8)==X8 then X8 else 0) |||
                (if (p&&&X9)==X9 then X9 else 0)
      b0==p)=true ∧
    (0 :: pOs).all (fun p=>((p&&&R0_3) != 0||pSafe3.elem p) &&
      ((p&&&R0_4) != 0||pSafe4.elem p) &&
      ((p&&&R0_6) != 0||pSafe6.elem p) &&
      ((p&&&R0_7) != 0||pSafe7.elem p))=true:=by
  decide +kernel
theorem r1_4_covers_r0_3 : (R1_4&&&R0_3)=R0_3:=by decide +kernel
def iSr (x : ℕ) : List ℕ → List ℕ
  | []=>[x]
  | y :: ys=>if x < y then x :: y :: ys else if x==y then y :: ys else y :: iSr x ys
def sUn (l : List ℕ) : List ℕ :=
  l.foldl (fun acc x=>iSr x acc) []
def wAnd (a b : ℕ) : ℕ:=a&&&b
def wOr (a b : ℕ) : ℕ:=a|||b
def aOW (S : List ℕ) (o : ℕ) : List ℕ :=
  S.foldl (fun acc a=>iSr (wAnd a o) acc) (iSr o S)
def aPO (S : List ℕ) (f : ℕ → Bool) : Bool :=
  let rec go : List ℕ → Bool
    | []=>true
    | a :: rest=>rest.all (fun b=>f (wOr a b))&&go rest
  go S
def l0_15 (w : ℕ) : ℕ:=w>>>10
def l1_15 (w : ℕ) : ℕ:=(w>>>5)&&&31
def e5_15 (w : ℕ) : ℕ:=w&&&31
def C0_15W : List ℕ:=[0,1,2,4,8,16,65,128,260,512,1061,2021,2115,4242,8460,16920]
def ow3_g1 : List (List ℕ):=[[640],[2243],[17048],[4754],[8972],[6355],[19035],[12702],[21146],[25372]]
def ow3_g2 : List (List ℕ):=[[640,19035],[640,12702],[2243,19163],[17048,19035],[17048,19163],[17048,12702],[4754,19035],[4754,12702],[4754,13214],[8972,13214],[19035,705],[19035,19163],[19035,4819],[19035,12702],[19035,21146],[19035,23259],[12702,900],[12702,17308],[12702,13214],[12702,21146],[12702,29598]]
def ow3_g3 : List (List ℕ):=[[640,19035,12702],[17048,19035,12702],[17048,19163,12702],[4754,19035,12702],[4754,19035,13214],[19035,12702,21146]]
def build15 (gs : List ℕ) : List ℕ:=gs.foldl aOW C0_15W
def Q1W : List (List ℕ):=ow3_g1.map build15
def Q2W : List (List ℕ):=ow3_g2.map build15
def Q3W : List (List ℕ):=ow3_g3.map build15
def uS15 (st : ℕ × ℕ × ℕ × Bool × Bool × Bool) (w : ℕ) :
    ℕ × ℕ × ℕ × Bool × Bool × Bool :=
  let (i18,i12,i20,s6,s7,s3):=st
  let a0:=l0_15 w
  let a1:=l1_15 w
  let (i18',s6'):=if (a0&&&18)==18 then (i18&&&a0,true) else (i18,s6)
  let (i12',s7'):=if (a0&&&12)==12 then (i12&&&a0,true) else (i12,s7)
  let (i20',s3'):=if (a1&&&20)==20 then (i20&&&a1,s3||(a1 != 31)) else (i20,s3)
  (i18',i12',i20',s6',s7',s3')
def st15 (S : List ℕ) : ℕ × ℕ × ℕ × Bool × Bool × Bool :=
  S.foldl uS15 (31,31,31,false,false,false)
def cS15 (S : List ℕ) : Bool :=
  S.any fun a=>S.any fun b =>
    let o0:=l0_15 a|||l0_15 b
    let o1:=l1_15 a|||l1_15 b
    o1 != 31&&(o1&&&20)==20&&((o0&&&18)==18||(o0&&&12)==12)
def lb15B (st : ℕ × ℕ × ℕ × Bool × Bool × Bool) : ℕ :=
  let (i18,i12,i20,s6,s7,s3):=st
  let h6:=s6&&(i18==18)
  let h7:=s7&&(i12==12)
  let h3:=s3&&(i20==20)
  if h6&&h7&&h3 then 0 else
  let req0:=(if !h6 then 18 else 0)|||(if !h7 then 12 else 0)
  let forb0:=(if !h6 then i18&&&(31^^^18) else 0)|||(if !h7 then i12&&&(31^^^12) else 0)
  let forb1:=if !h3 then i20&&&(31^^^20) else 0
  if (req0&&&(forb0|||forb1)) != 0 then 2 else 1
def lb15 (S : List ℕ) : ℕ :=
  let st:=st15 S
  let b0:=lb15B st
  if b0==0 then 0 else
  let (_,_,_,s6,s7,s3):=st
  if !s6&&!s7&&!s3&&!cS15 S then max b0 3 else b0
def sc15 (src dst : List (List ℕ)) (rem : ℕ) : Bool :=
  src.all fun S =>
    let st:=st15 S
    (lb15 S > rem||dst.elem S) &&
    aPO S fun o =>
      if lb15B (uS15 st o) > rem then true else
      if S.elem o then true else
      let S2:=aOW S o
      lb15 S2 > rem||dst.elem S2
def pop4 (e : ℕ) : ℕ :=
  (e&&&1) + ((e>>>1)&&&1) + ((e>>>2)&&&1) + ((e>>>3)&&&1)
def q3MaxOneEdge : Bool :=
  Q3W.all fun S=>S.all fun w =>
    if l0_15 w==0&&((e5_15 w>>>4)&&&1)==0 then pop4 (e5_15 w&&&15) <= 1 else true
set_option maxHeartbeats 8000000 in
theorem test_OW3 :
    sc15 [C0_15W] Q1W 2 &&
    sc15 Q1W Q2W 1 &&
    sc15 Q2W Q3W 0 &&
    q3MaxOneEdge=true:=by decide +kernel
def l0_14 (w : ℕ) : ℕ:=w>>>9
def l1_14 (w : ℕ) : ℕ:=(w>>>4)&&&31
def e4_14 (w : ℕ) : ℕ:=w&&&15
def symM5 (m : ℕ) : ℕ :=
  (m&&&1)|||(((m>>>1)&&&1)<<<3)|||(((m>>>3)&&&1)<<<1) |||
  (((m>>>2)&&&1)<<<4)|||(((m>>>4)&&&1)<<<2)
def symE4 (e : ℕ) : ℕ :=
  (((e>>>0)&&&1)<<<2)|||(((e>>>2)&&&1)<<<0) |||
  (((e>>>1)&&&1)<<<3)|||(((e>>>3)&&&1)<<<1)
def symW (w : ℕ) : ℕ :=
  (symM5 (l0_14 w)<<<9)|||(symM5 (l1_14 w)<<<4)|||symE4 (e4_14 w)
def listLe : List ℕ → List ℕ → Bool
  | [],_=>true
  | _ :: _,[]=>false
  | x :: xs,y :: ys=>if x < y then true else if x==y then listLe xs ys else false
def canonW (S : List ℕ) : List ℕ :=
  let T:=sUn (S.map symW)
  if listLe S T then S else T
def C0W : List ℕ:=[0,1,2,4,8,33,64,132,256,533,1013,1059,2114,4236,8456]
def gens1 : List (List ℕ):=[[],[3],[5],[9],[65],[133],[257],[2115],[4237],[8457],[10],[35],[66],[134],[258],[535],[1015],[4238],[8458],[97],[165],[289],[565],[2147],[4269],[8489],[320],[597],[1123],[4300],[8520],[1591],[2647],[2039],[3063],[3171],[5295],[9515],[10570]]
def gens2 : List (List ℕ):=[[320],[1123],[8520],[3171],[9515],[10570],[3,320],[3,1123],[3,8520],[3,2370],[3,4492],[3,3171],[3,9515],[3,6350],[3,10570],[3,12684],[5,320],[5,1123],[5,8520],[5,3171],[5,9515],[5,10570],[9,320],[9,1123],[9,8520],[9,2370],[9,4492],[9,3171],[9,9515],[9,6350],[9,10570],[9,12684],[65,320],[65,1123],[65,8520],[65,321],[65,8521],[65,2370],[65,4492],[65,3171],[65,9515],[65,6350],[65,10570],[65,12684],[133,320],[133,1123],[133,8520],[133,2370],[133,4492],[133,3171],[133,9515],[133,6350],[133,10570],[133,12684],[257,320],[257,1123],[257,8520],[257,324],[257,1127],[257,8524],[257,2370],[257,4492],[257,3171],[257,9515],[257,6350],[257,10570],[257,12684],[2115,320],[2115,1123],[2115,8520],[2115,321],[2115,8521],[2115,2370],[2115,2371],[2115,4492],[2115,3171],[2115,9515],[2115,6350],[2115,10570],[2115,6351],[2115,10571],[2115,12684],[4237,320],[4237,1123],[4237,1127],[4237,8520],[4237,2370],[4237,4492],[4237,3171],[4237,9515],[4237,3175],[4237,9519],[4237,6350],[4237,10570],[4237,12684],[8457,320],[8457,1123],[8457,8520],[8457,324],[8457,1127],[8457,8524],[8457,2370],[8457,2374],[8457,4492],[8457,3171],[8457,3175],[8457,9515],[8457,6350],[8457,10570],[8457,10574],[8457,12684],[10,320],[10,1123],[10,8520],[10,3171],[10,9515],[10,10570],[35,320],[35,1123],[35,8520],[35,2370],[35,4492],[35,3171],[35,9515],[35,6350],[35,10570],[35,12684],[66,320],[66,8520],[66,322],[66,8522],[66,2370],[66,4492],[66,3171],[66,9515],[66,6350],[66,10570],[66,12684],[134,320],[134,1123],[134,8520],[134,2370],[134,4492],[134,3171],[134,9515],[134,6350],[134,10570],[134,12684],[258,320],[258,1123],[258,8520],[258,328],[258,1131],[258,2370],[258,4492],[258,3171],[258,9515],[258,6350],[258,10570],[258,12684],[535,320],[535,1123],[535,8520],[535,2370],[535,4492],[535,3171],[535,9515],[535,6350],[535,10570],[535,12684],[1015,320],[1015,1123],[1015,8520],[1015,322],[1015,8522],[1015,2370],[1015,4492],[1015,3171],[1015,9515],[1015,6350],[1015,10570],[1015,12684],[4238,320],[4238,1123],[4238,1131],[4238,8520],[4238,2370],[4238,4492],[4238,3171],[4238,9515],[4238,3179],[4238,6350],[4238,10570],[4238,12684],[8458,320],[8458,1123],[8458,8520],[8458,2370],[8458,2378],[8458,4492],[8458,3171],[8458,3179],[8458,9515],[8458,6350],[8458,10570],[8458,12684],[97,320],[97,8520],[97,353],[97,8553],[97,2370],[97,4492],[97,9515],[97,6350],[97,10570],[97,12684],[165,320],[165,1123],[165,8520],[165,3171],[165,9515],[165,10570],[289,320],[289,1123],[289,8520],[289,452],[289,1255],[289,8652],[289,2370],[289,4492],[289,3171],[289,9515],[289,10570],[289,12684],[565,320],[565,1123],[565,8520],[565,2370],[565,4492],[565,3171],[565,9515],[565,6350],[565,10570],[565,12684],[2147,320],[2147,1123],[2147,8520],[2147,353],[2147,8553],[2147,2370],[2147,2403],[2147,4492],[2147,3171],[2147,9515],[2147,6350],[2147,10570],[2147,6383],[2147,10603],[2147,12684],[4269,320],[4269,1123],[4269,1255],[4269,8520],[4269,2370],[4269,4492],[4269,3171],[4269,9515],[4269,3303],[4269,9647],[4269,6350],[4269,10570],[4269,12684],[8489,320],[8489,1123],[8489,8520],[8489,452],[8489,1255],[8489,8652],[8489,2370],[8489,2502],[8489,4492],[8489,3171],[8489,3303],[8489,9515],[8489,6350],[8489,10570],[8489,10702],[8489,12684],[320,321],[320,353],[320,597],[320,1123],[320,4300],[320,853],[320,1379],[320,1591],[320,2647],[320,2039],[320,3063],[320,3171],[320,5295],[320,9515],[597,1123],[597,8520],[597,853],[597,2370],[597,4492],[597,1655],[597,9053],[597,3171],[597,9515],[597,6350],[597,10570],[597,12684],[1123,67],[1123,99],[1123,70],[1123,101],[1123,1127],[1123,74],[1123,105],[1123,1131],[1123,4300],[1123,8520],[1123,198],[1123,322],[1123,599],[1123,4302],[1123,8522],[1123,229],[1123,353],[1123,629],[1123,4333],[1123,8553],[1123,1255],[1123,1315],[1123,1379],[1123,2370],[1123,4492],[1123,1591],[1123,1655],[1123,2647],[1123,4765],[1123,8989],[1123,2039],[1123,3063],[1123,5117],[1123,9213],[1123,3171],[1123,5295],[1123,9515],[1123,5359],[1123,9579],[1123,6350],[1123,10570],[1123,12684],[4300,8520],[4300,452],[4300,1255],[4300,8652],[4300,2370],[4300,4556],[4300,3171],[4300,5359],[4300,9515],[4300,6350],[4300,10570],[4300,12684],[4300,12748],[8520,321],[8520,2371],[8520,322],[8520,324],[8520,2374],[8520,328],[8520,2378],[8520,353],[8520,2403],[8520,8520],[8520,452],[8520,2502],[8520,853],[8520,1379],[8520,4556],[8520,1591],[8520,2647],[8520,2903],[8520,4765],[8520,8989],[8520,2039],[8520,3063],[8520,5117],[8520,9213],[8520,3171],[8520,3427],[8520,5295],[8520,9515],[8520,6350],[8520,10570],[8520,6606],[8520,12684],[1591,1655],[1591,3171],[1591,9515],[1591,3703],[1591,10047],[1591,6350],[1591,10570],[1591,12684],[2647,853],[2647,2903],[2647,1655],[2647,9053],[2647,3171],[2647,3703],[2647,9515],[2647,6350],[2647,10570],[2647,6879],[2647,11103],[2647,12684],[2039,322],[2039,8522],[2039,3171],[2039,9515],[2039,10239],[2039,6350],[2039,10570],[2039,12684],[3063,3171],[3063,9515],[3063,6350],[3063,10570],[3063,7167],[3063,12684],[3171,99],[3171,101],[3171,3175],[3171,105],[3171,3179],[3171,229],[3171,353],[3171,629],[3171,4333],[3171,8553],[3171,3303],[3171,3427],[3171,3703],[3171,4087],[3171,5295],[3171,9515],[3171,6350],[3171,10570],[3171,7407],[3171,11627],[3171,12684],[5295,5359],[5295,9515],[5295,7407],[5295,10570],[9515,197],[9515,6351],[9515,198],[9515,204],[9515,229],[9515,6383],[9515,452],[9515,725],[9515,1255],[9515,8652],[9515,6606],[9515,6879],[9515,7167],[9515,7407],[9515,9515],[9515,10570],[9515,14798],[10570,321],[10570,10571],[10570,322],[10570,353],[10570,10603],[10570,853],[10570,1379],[10570,11103],[10570,11263],[10570,11627]]
def gens3 : List (List ℕ):=[[5,9515,9515],[133,9515,6350],[257,1127,9583],[257,8524,6607],[257,9515,9583],[2115,320,6351],[2115,8520,6351],[2115,321,6351],[2115,8521,6351],[2115,2370,6351],[2115,2371,6351],[2115,2371,6607],[2115,4492,6607],[2115,9515,6351],[2115,10570,6351],[2115,6351,453],[2115,6351,8653],[2115,6351,6607],[2115,6351,10571],[2115,6351,14799],[4237,320,9519],[4237,1127,9583],[4237,8520,9519],[4237,8520,9583],[4237,2370,9519],[4237,9515,6350],[4237,9519,453],[4237,9519,8653],[4237,9519,6607],[4237,9519,9515],[4237,9519,10570],[4237,9519,14799],[8457,1127,9583],[8457,8524,6607],[8457,9515,9583],[165,9515,9515],[2147,320,6383],[2147,8520,6383],[2147,2370,6383],[2147,9515,6383],[2147,10570,6383],[4269,320,9647],[4269,8520,9647],[4269,8520,9711],[4269,2370,9647],[4269,9515,9515],[4269,9647,9515],[4269,9647,10570],[320,9515,6351],[320,9515,6383],[320,9515,6879],[320,9515,7167],[597,9515,7135],[1123,1127,9583],[1123,9579,9583],[1123,9579,9711],[1123,9579,10111],[1123,9579,10239],[8520,2371,6607],[8520,2403,6639],[8520,9515,6351],[8520,9515,6383],[8520,9515,6879],[8520,9515,7167],[8520,6350,6351],[8520,6350,6383],[8520,6350,6879],[8520,6350,7167],[8520,6606,9583],[8520,6606,9711],[8520,6606,10111],[8520,6606,10239],[2647,9515,10111],[5295,9515,9515],[9515,197,9515],[9515,6351,452],[9515,6351,8652],[9515,6351,453],[9515,6351,8653],[9515,6351,6606],[9515,6351,6607],[9515,6351,9515],[9515,6351,10570],[9515,6351,14798],[9515,6351,14799],[9515,229,9515],[9515,6383,452],[9515,6383,8652],[9515,6383,6606],[9515,6383,9515],[9515,6383,10570],[9515,6383,14798],[9515,452,6879],[9515,452,7167],[9515,1255,9515],[9515,1255,9711],[9515,8652,10047],[9515,8652,10239],[9515,8652,6639],[9515,6606,9583],[9515,6606,9711],[9515,6606,10047],[9515,6606,10111],[9515,6606,10239],[9515,6879,981],[9515,6879,7135],[9515,6879,9181],[9515,6879,9515],[9515,6879,10570],[9515,6879,14798],[9515,6879,15327],[9515,7167,328],[9515,7167,460],[9515,7167,2378],[9515,7167,9515],[9515,7167,10570],[9515,7167,14798],[9515,7407,9515],[9515,9515,11],[9515,9515,43],[9515,9515,206],[9515,9515,543],[9515,9515,1023],[9515,9515,485],[9515,9515,9711],[9515,9515,15855],[9515,10570,2655],[9515,10570,3071]]
def bSt (gs : List ℕ) : List ℕ:=gs.foldl (fun S o=>canonW (aOW S o)) C0W
def P1W : List (List ℕ):=gens1.map bSt
def P2W : List (List ℕ):=gens2.map bSt
def P3W : List (List ℕ):=gens3.map bSt
def hashS (S : List ℕ) : ℕ :=
  (S.foldl (fun acc w=>(acc * 131 + w) % 65521) 0) % 32
def mkB (Ss : List (List ℕ)) : List (List (List ℕ)) :=
  (List.range 32).map fun b=>Ss.filter (fun S=>hashS S==b)
def mBk (B : List (List (List ℕ))) (S : List ℕ) : Bool :=
  (B.getD (hashS S) []).any (fun T=>T==S)
def B1W : List (List (List ℕ)):=mkB P1W
def B2W : List (List (List ℕ)):=mkB P2W
def B3W : List (List (List ℕ)):=mkB P3W
def uS14 (st : ℕ × ℕ × ℕ × ℕ × Bool × Bool × Bool × Bool) (w : ℕ) :
    ℕ × ℕ × ℕ × ℕ × Bool × Bool × Bool × Bool :=
  let (i18,i12,i20,ie15,s6,s7,s3,sZ):=st
  let a0:=l0_14 w
  let a1:=l1_14 w
  let ae:=e4_14 w
  let (i18',s6'):=if (a0&&&18)==18 then (i18&&&a0,true) else (i18,s6)
  let (i12',s7'):=if (a0&&&12)==12 then (i12&&&a0,true) else (i12,s7)
  let (i20',s3'):=if (a1&&&20)==20 then (i20&&&a1,s3||(a1 != 31)) else (i20,s3)
  let (ie15',sZ'):=if ae==15 then (ie15&&&a0,true) else (ie15,sZ)
  (i18',i12',i20',ie15',s6',s7',s3',sZ')
def st14 (S : List ℕ) : ℕ × ℕ × ℕ × ℕ × Bool × Bool × Bool × Bool :=
  S.foldl uS14 (31,31,31,31,false,false,false,false)
def lb14B (st : ℕ × ℕ × ℕ × ℕ × Bool × Bool × Bool × Bool) : ℕ :=
  let (i18,i12,i20,ie15,s6,s7,s3,sZ):=st
  let h6:=s6&&(i18==18)
  let h7:=s7&&(i12==12)
  let h3:=s3&&(i20==20)
  let hZ:=sZ&&(ie15==0)
  if h6&&h7&&h3&&hZ then 0 else
  let req0:=(if !h6 then 18 else 0)|||(if !h7 then 12 else 0)
  let forb0:=(if !h6 then i18&&&(31^^^18) else 0) |||
               (if !h7 then i12&&&(31^^^12) else 0) |||
               (if !hZ then ie15 else 0)
  let forb1:=if !h3 then i20&&&(31^^^20) else 0
  if (req0&&&(forb0|||forb1)) != 0 then 2 else 1
def cZ0 (S : List ℕ) : Bool :=
  let z0s:=S.filter (fun w=>l0_14 w==0)
  z0s.any (fun a=>z0s.any (fun b=>(e4_14 a|||e4_14 b)==15))
def cE15 (S : List ℕ) : Bool :=
  S.any (fun a=>S.any (fun b=>(e4_14 a|||e4_14 b)==15))
def cS14 (S : List ℕ) : Bool :=
  S.any fun a=>S.any fun b =>
    let o0:=l0_14 a|||l0_14 b
    let o1:=l1_14 a|||l1_14 b
    o1 != 31&&(o1&&&20)==20&&((o0&&&18)==18||(o0&&&12)==12)
def lb14 (S : List ℕ) : ℕ :=
  let st:=st14 S
  let b0:=lb14B st
  if b0==0 then 0 else
  let (i18,i12,_,ie15,s6,s7,s3,sZ):=st
  let h6:=s6&&(i18==18)
  let h7:=s7&&(i12==12)
  let hZ:=sZ&&(ie15==0)
  let b1:=if b0 < 2&&!hZ&&!sZ&&!cZ0 S then 2 else b0
  let b2:=if !s6&&!s7&&!s3&&!cS14 S then 3 else b1
  if b2 < 3&&!hZ&&!sZ then
    let req67:=(if !h6 then 18 else 0)|||(if !h7 then 12 else 0)
    let forb67:=(if !h6 then i18&&&(31^^^18) else 0)|||(if !h7 then i12&&&(31^^^12) else 0)
    if (req67&&&forb67) != 0&&!cE15 S then 3 else b2
  else b2
def sc14 (src : List (List ℕ)) (dstB : List (List (List ℕ))) (rem : ℕ) : Bool :=
  src.all fun S =>
    let st:=st14 S
    (lb14 S > rem||mBk dstB S) &&
    aPO S fun o =>
      if lb14B (uS14 st o) > rem then true else
      if S.elem o then true else
      let S2:=aOW S o
      if lb14 S2 > rem then true else mBk dstB (canonW S2)
def fc14 (src : List (List ℕ)) : Bool :=
  src.all fun S =>
    let st:=st14 S
    lb14B st != 0 &&
    aPO S fun o=>lb14B (uS14 st o) != 0
set_option maxHeartbeats 8000000 in
theorem test_OW4_step1 : sc14 [C0W] B1W 3=true:=by decide +kernel
set_option maxHeartbeats 12000000 in
theorem test_OW4_step2_0 : sc14 ((gens1.take 5).map bSt) B2W 2=true:=by decide +kernel
set_option maxHeartbeats 12000000 in
theorem test_OW4_step2_1 : sc14 (((gens1.drop 5).take 5).map bSt) B2W 2=true:=by decide +kernel
set_option maxHeartbeats 12000000 in
theorem test_OW4_step2_2 : sc14 (((gens1.drop 10).take 5).map bSt) B2W 2=true:=by decide +kernel
set_option maxHeartbeats 12000000 in
theorem test_OW4_step2_3 : sc14 (((gens1.drop 15).take 5).map bSt) B2W 2=true:=by decide +kernel
set_option maxHeartbeats 12000000 in
theorem test_OW4_step2_4 : sc14 (((gens1.drop 20).take 5).map bSt) B2W 2=true:=by decide +kernel
set_option maxHeartbeats 12000000 in
theorem test_OW4_step2_5 : sc14 (((gens1.drop 25).take 5).map bSt) B2W 2=true:=by decide +kernel
set_option maxHeartbeats 12000000 in
theorem test_OW4_step2_6 : sc14 (((gens1.drop 30).take 5).map bSt) B2W 2=true:=by decide +kernel
set_option maxHeartbeats 12000000 in
theorem test_OW4_step2_7 : sc14 ((gens1.drop 35).map bSt) B2W 2=true:=by decide +kernel
set_option maxHeartbeats 12000000 in
theorem test_OW4_step3_0 : sc14 ((gens2.take 64).map bSt) B3W 1=true:=by decide +kernel
set_option maxHeartbeats 12000000 in
theorem test_OW4_step3_1 : sc14 (((gens2.drop 64).take 64).map bSt) B3W 1=true:=by decide +kernel
set_option maxHeartbeats 12000000 in
theorem test_OW4_step3_2 : sc14 (((gens2.drop 128).take 64).map bSt) B3W 1=true:=by decide +kernel
set_option maxHeartbeats 12000000 in
theorem test_OW4_step3_3 : sc14 (((gens2.drop 192).take 64).map bSt) B3W 1=true:=by decide +kernel
set_option maxHeartbeats 12000000 in
theorem test_OW4_step3_4 : sc14 (((gens2.drop 256).take 64).map bSt) B3W 1=true:=by decide +kernel
set_option maxHeartbeats 12000000 in
theorem test_OW4_step3_5 : sc14 (((gens2.drop 320).take 64).map bSt) B3W 1=true:=by decide +kernel
set_option maxHeartbeats 12000000 in
theorem test_OW4_step3_6 : sc14 (((gens2.drop 384).take 64).map bSt) B3W 1=true:=by decide +kernel
set_option maxHeartbeats 12000000 in
theorem test_OW4_step3_7 : sc14 ((gens2.drop 448).map bSt) B3W 1=true:=by decide +kernel
set_option maxHeartbeats 8000000 in
theorem test_OW4_step4_0 : fc14 ((gens3.take 64).map bSt)=true:=by decide +kernel
set_option maxHeartbeats 8000000 in
theorem test_OW4_step4_1 : fc14 ((gens3.drop 64).map bSt)=true:=by decide +kernel
lemma bac (a b : ℕ) : (a&&&b)=(b&&&a):=by
  apply Nat.eq_of_testBit_eq;intro i;simp [Nat.testBit_and,Bool.and_comm]
lemma baa (a b c : ℕ) : ((a&&&b)&&&c)=(a&&&(b&&&c)):=by
  apply Nat.eq_of_testBit_eq;intro i;simp [Nat.testBit_and,Bool.and_assoc]
lemma bas (a : ℕ) : (a&&&a)=a:=by
  apply Nat.eq_of_testBit_eq;intro i;simp [Nat.testBit_and]
lemma boc (a b : ℕ) : (a|||b)=(b|||a):=by
  apply Nat.eq_of_testBit_eq;intro i;simp [Nat.testBit_or,Bool.or_comm]
lemma boa (a b c : ℕ) : ((a|||b)|||c)=(a|||(b|||c)):=by
  apply Nat.eq_of_testBit_eq;intro i;simp [Nat.testBit_or,Bool.or_assoc]
lemma bos (a : ℕ) : (a|||a)=a:=by
  apply Nat.eq_of_testBit_eq;intro i;simp [Nat.testBit_or]
lemma baod (a b c : ℕ) : ((a|||b)&&&c)=((a&&&c)|||(b&&&c)):=by
  apply Nat.eq_of_testBit_eq;intro i
  simp only [Nat.testBit_and,Nat.testBit_or]
  cases a.testBit i<;>cases b.testBit i<;>cases c.testBit i<;>rfl
lemma baodl (a b c : ℕ) : (a&&&(b|||c))=((a&&&b)|||(a&&&c)):=by
  rw [bac,baod,bac b a,bac c a]
lemma bo0l (a : ℕ) : (0|||a)=a:=by
  apply Nat.eq_of_testBit_eq;intro i;simp
lemma bit_or_zero_right (a : ℕ) : (a|||0)=a:=by
  apply Nat.eq_of_testBit_eq;intro i;simp
lemma ba0l (a : ℕ) : (0&&&a)=0:=by
  apply Nat.eq_of_testBit_eq;intro i;simp
lemma ba0r (a : ℕ) : (a&&&0)=0:=by
  apply Nat.eq_of_testBit_eq;intro i;simp
lemma bit_sub_of_or_zero {a b c : ℕ} (h : ((a|||b)&&&c)=0) : (a&&&c)=0 ∧ (b&&&c)=0:=by
  constructor
  · apply Nat.eq_of_testBit_eq;intro i
    have hi:=congrArg (fun n=>Nat.testBit n i) h
    simp only [Nat.testBit_and,Nat.testBit_or,Nat.zero_testBit] at hi ⊢
    cases ha : a.testBit i<;>cases hb : b.testBit i<;>cases hc : c.testBit i<;>simp_all
  · apply Nat.eq_of_testBit_eq;intro i
    have hi:=congrArg (fun n=>Nat.testBit n i) h
    simp only [Nat.testBit_and,Nat.testBit_or,Nat.zero_testBit] at hi ⊢
    cases ha : a.testBit i<;>cases hb : b.testBit i<;>cases hc : c.testBit i<;>simp_all
lemma bit_le_or_left (a b : ℕ) : (a|||(a|||b))=(a|||b):=by
  rw [← boa,bos]
lemma bit_le_or_right (a b : ℕ) : (b|||(a|||b))=(a|||b):=by
  rw [boc a b,bit_le_or_left]
lemma bit_or_le_iff (a b c : ℕ) : ((a|||b)|||c)=c ↔ (a|||c)=c ∧ (b|||c)=c:=by
  constructor
  · intro h
    constructor
    · apply Nat.eq_of_testBit_eq;intro i
      have hi:=congrArg (fun n=>Nat.testBit n i) h
      simp only [Nat.testBit_or] at hi ⊢
      cases ha : a.testBit i<;>cases hb : b.testBit i<;>cases hc : c.testBit i<;>simp_all
    · apply Nat.eq_of_testBit_eq;intro i
      have hi:=congrArg (fun n=>Nat.testBit n i) h
      simp only [Nat.testBit_or] at hi ⊢
      cases ha : a.testBit i<;>cases hb : b.testBit i<;>cases hc : c.testBit i<;>simp_all
  · rintro ⟨ha,hb⟩
    rw [boa,hb,ha]
lemma edgesOf_or (a b : ℕ) : edgesOf (a|||b)=(edgesOf a|||edgesOf b):=by
  have hbit : ∀ e : ℕ,((a|||b)&&&e != 0)=((a&&&e != 0)||(b&&&e != 0)):=by
    intro e
    rw [baod]
    by_cases ha : a&&&e=0<;>by_cases hb : b&&&e=0
    · simp [ha,hb]
    · have hne : (a&&&e|||b&&&e) ≠ 0:=by rw [ha,bo0l];exact hb
      simp [ha,hb,hne]
    · have hne : (a&&&e|||b&&&e) ≠ 0:=by rw [hb,bit_or_zero_right];exact ha
      simp [ha,hb,hne]
    · have hne : (a&&&e|||b&&&e) ≠ 0:=by
        intro h0
        apply ha
        apply Nat.eq_of_testBit_eq;intro i
        have hi:=congrArg (fun n=>Nat.testBit n i) h0
        simp only [Nat.testBit_or,Nat.zero_testBit] at hi ⊢
        cases h1 : (a&&&e).testBit i<;>cases h2 : (b&&&e).testBit i<;>simp_all
      exact Bool.eq_iff_iff.mpr (by simp [ha,hb,hne])
  unfold edgesOf
  rw [hbit E01,hbit E12,hbit E05,hbit E58]
  cases ((a&&&E01) != 0)<;>cases ((b&&&E01) != 0) <;>
  cases ((a&&&E12) != 0)<;>cases ((b&&&E12) != 0) <;>
  cases ((a&&&E05) != 0)<;>cases ((b&&&E05) != 0) <;>
  cases ((a&&&E58) != 0)<;>cases ((b&&&E58) != 0)<;>decide
lemma foldl_or_ge {α : Type} (f : α → ℕ) (l : List α) (init : ℕ) :
    (init|||l.foldl (fun acc x=>acc|||f x) init)=l.foldl (fun acc x=>acc|||f x) init:=by
  induction l generalizing init with
  | nil=>exact bos init
  | cons a t ih =>
    simp only [List.foldl_cons]
    have h1:=ih (init|||f a)
    rw [← h1,← boa,bit_le_or_left]
lemma foldl_or_mem {α : Type} (f : α → ℕ) (l : List α) (init : ℕ) {a : α} (ha : a ∈ l) :
    (f a|||l.foldl (fun acc x=>acc|||f x) init)=l.foldl (fun acc x=>acc|||f x) init:=by
  induction l generalizing init with
  | nil=>simp at ha
  | cons b t ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp ha with rfl | ht
    · have h1:=foldl_or_ge f t (init|||f a)
      rw [← h1,← boa,bit_le_or_right]
    · exact ih (init|||f b) ht
lemma cWFm (ys : List ℕ) (F y : ℕ) (hy : y ∈ ys) (hsafe : ((y&&&F)&&&IND_SAFE)=0) :
    (edgesOf (y&&&F)|||cWF ys F)=cWF ys F:=by
  unfold cWF
  let step : ℕ → ℕ:=fun w=>if ((w&&&F)&&&IND_SAFE)==0 then edgesOf (w&&&F) else 0
  have hrew : ∀ (l : List ℕ) (init : ℕ),
      l.foldl (fun acc w=>let z:=w&&&F;if (z&&&IND_SAFE)==0 then acc|||edgesOf z else acc) init =
      l.foldl (fun acc w=>acc|||step w) init:=by
    intro l
    induction l with
    | nil=>intro init;rfl
    | cons w t ih =>
      intro init
      simp only [List.foldl_cons,step]
      by_cases h0 : ((w&&&F)&&&IND_SAFE)==0
      · rw [if_pos h0,if_pos h0];exact ih _
      · rw [if_neg h0,if_neg h0,bit_or_zero_right];exact ih _
  rw [hrew ys 0]
  have hm:=foldl_or_mem step ys 0 hy
  have hs : step y=edgesOf (y&&&F):=by simp [step,hsafe]
  rwa [hs] at hm
lemma cWFp (ys : List ℕ) (F p : ℕ)
    (hbase : ∀ b ∈ bWs,b ∈ ys) (hp : p ∈ pOs)
    (hsafe : ((p&&&F)&&&IND_SAFE)=0) :
    (edgesOf (p&&&F)|||cWF ys F)=cWF ys F:=by
  have hdec:=pureOrs_props.2.2.1
  have hp':=List.all_eq_true.mp hdec p hp
  simp only [beq_iff_eq] at hp'
  set c0:=if p&&&X0=X0 then X0 else 0
  set c1:=if p&&&X1=X1 then X1 else 0
  set c2:=if p&&&X2=X2 then X2 else 0
  set c5:=if p&&&X5=X5 then X5 else 0
  set c8:=if p&&&X8=X8 then X8 else 0
  set c9:=if p&&&X9=X9 then X9 else 0
  change (c0|||c1|||c2|||c5|||c8|||c9)=p at hp'
  rw [← hp'] at hsafe ⊢
  have hstep : ∀ (x y : ℕ),
      (((x|||y)&&&F)&&&IND_SAFE)=0 →
      (((x&&&F)&&&IND_SAFE)=0 → (edgesOf (x&&&F)|||cWF ys F)=cWF ys F) →
      (((y&&&F)&&&IND_SAFE)=0 → (edgesOf (y&&&F)|||cWF ys F)=cWF ys F) →
      (edgesOf ((x|||y)&&&F)|||cWF ys F)=cWF ys F:=by
    intro x y hxy hx hy
    rw [baod] at hxy ⊢
    obtain ⟨hsx,hsy⟩:=bit_sub_of_or_zero hxy
    rw [edgesOf_or,bit_or_le_iff]
    exact ⟨hx hsx,hy hsy⟩
  have hterm : ∀ (b : ℕ),b ∈ bWs →
      ∀ (P : Prop) [Decidable P],(((if P then b else 0)&&&F)&&&IND_SAFE)=0 →
        (edgesOf ((if P then b else 0)&&&F)|||cWF ys F)=cWF ys F:=by
    intro b hb P _ hs
    by_cases hP : P
    · simp only [hP,↓reduceIte] at hs ⊢
      exact cWFm ys F b (hbase b hb) hs
    · simp only [hP,↓reduceIte,ba0l]
      have : edgesOf 0=0:=by decide
      rw [this,bo0l]
  exact hstep (c0|||c1|||c2|||c5|||c8) c9 hsafe
    (fun h1=>hstep (c0|||c1|||c2|||c5) c8 h1
      (fun h2=>hstep (c0|||c1|||c2) c5 h2
        (fun h3=>hstep (c0|||c1) c2 h3
          (fun h4=>hstep c0 c1 h4
            (fun h5=>hterm X0 (by simp [bWs]) _ h5)
            (fun h5=>hterm X1 (by simp [bWs]) _ h5))
          (fun h4=>hterm X2 (by simp [bWs]) _ h4))
        (fun h3=>hterm X5 (by simp [bWs]) _ h3))
      (fun h2=>hterm X8 (by simp [bWs]) _ h2))
    (fun h1=>hterm X9 (by simp [bWs]) _ h1)
lemma cWFg0 (g0 F y : ℕ)
    (hy : y ∈ pOs ∨ y=g0 ∨ ∃ p ∈ pOs,y=p|||g0)
    (hsafe : ((y&&&F)&&&IND_SAFE)=0) :
    (edgesOf (y&&&F)|||cWF (g0 :: bWs) F)=cWF (g0 :: bWs) F:=by
  have hbase : ∀ b ∈ bWs,b ∈ g0 :: bWs:=fun b hb=>List.mem_cons_of_mem g0 hb
  rcases hy with hp | heq | ⟨p,hp,rfl⟩
  · exact cWFp (g0 :: bWs) F y hbase hp hsafe
  · subst heq;exact cWFm (y :: bWs) F y (List.mem_cons_self ..) hsafe
  · rw [baod] at hsafe ⊢
    obtain ⟨hsp,hsg⟩:=bit_sub_of_or_zero hsafe
    rw [edgesOf_or,bit_or_le_iff]
    exact ⟨cWFp (g0 :: bWs) F p hbase hp hsp,
           cWFm (g0 :: bWs) F g0 (List.mem_cons_self ..) hsg⟩
lemma mem_validBs {ps : List ℕ} {r1 r0 g0 w : ℕ}
    (hpred : ∀ p ∈ 0 :: pOs,(p&&&r0)=0 → p ∈ ps)
    (hw : w ∈ pOs ∨ w=g0 ∨ ∃ p ∈ pOs,w=p|||g0)
    (hne : w ≠ 0) (hr1 : (w&&&r1)=r1) (hr0 : (w&&&r0)=0) :
    w ∈ validBs ps r1 r0 g0:=by
  have hfold : ∀ (l : List ℕ) (acc : List ℕ) (x : ℕ),
      x ∈ acc ∨ (∃ p ∈ l,(x=p ∧ p ≠ 0 ∧ (p&&&r1)=r1 ∧ (p&&&r0)=0) ∨
        (x=p|||g0 ∧ (p|||g0) ≠ 0 ∧ ((p|||g0)&&&r1)=r1 ∧ ((p|||g0)&&&r0)=0)) →
      x ∈ l.foldl (fun acc p =>
        let acc1:=if p != 0&&(p&&&r1)==r1&&(p&&&r0)==0 then p :: acc else acc
        let w:=p|||g0
        if w != 0&&(w&&&r1)==r1&&(w&&&r0)==0 then w :: acc1 else acc1) acc:=by
    intro l
    induction l with
    | nil =>
      intro acc x hx
      rcases hx with h | ⟨p,hp,_⟩
      · exact h
      · simp at hp
    | cons a t ih =>
      intro acc x hx
      simp only [List.foldl_cons]
      apply ih
      rcases hx with hacc | ⟨p,hp,hcase⟩
      · left
        split_ifs<;>simp [hacc]
      · rcases List.mem_cons.mp hp with rfl | ht
        · left
          rcases hcase with ⟨rfl,h1,h2,h3⟩ | ⟨rfl,h1,h2,h3⟩
          · have hcond : (x != 0&&(x&&&r1)==r1&&(x&&&r0)==0)=true:=by simp [h1,h2,h3]
            rw [hcond]
            simp only [ite_true]
            split_ifs<;>simp
          · have hcond : ((p|||g0) != 0&&((p|||g0)&&&r1)==r1&&((p|||g0)&&&r0)==0)=true:=by
              simp [h1,h2,h3]
            rw [hcond];simp
        · exact Or.inr ⟨p,ht,hcase⟩
  apply hfold ps [] w
  right
  rcases hw with hp | rfl | ⟨p,hp,rfl⟩
  · exact ⟨w,hpred w (List.mem_cons_of_mem 0 hp) hr0,Or.inl ⟨rfl,hne,hr1,hr0⟩⟩
  · have h0 : (0&&&r0)=0:=ba0l r0
    exact ⟨0,hpred 0 (List.mem_cons_self ..) h0,Or.inr ⟨(bo0l w).symm,
      by rw [bo0l];exact hne,by rw [bo0l];exact hr1,
      by rw [bo0l];exact hr0⟩⟩
  · have hp0 : (p&&&r0)=0:=(bit_sub_of_or_zero hr0).1
    exact ⟨p,hpred p (List.mem_cons_of_mem 0 hp) hp0,Or.inr ⟨rfl,hne,hr1,hr0⟩⟩
lemma checkPairs_mem {l : List ℕ} (h : checkPairs l=true) {a b : ℕ} (ha : a ∈ l) (hb : b ∈ l) :
    checkAW1_aU4_pair a b=true ∨ checkAW1_aU4_pair b a=true:=by
  induction l with
  | nil=>simp at ha
  | cons x t ih =>
    simp only [checkPairs,Bool.and_eq_true,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | hat
    · exact Or.inl (h.1 b hb)
    · rcases List.mem_cons.mp hb with rfl | hbt
      · exact Or.inr (h.1 a (List.mem_cons_of_mem _ hat))
      · exact ih h.2 hat hbt
lemma checkAW1_aU4_pair_symm (a b : ℕ) : checkAW1_aU4_pair a b=checkAW1_aU4_pair b a:=by
  unfold checkAW1_aU4_pair;rw [bac a b]
lemma kill_AW1_aU4 {a b b3 b4 b6 b7 : ℕ} {zs : List ℕ}
    (ha : a ∈ pOs) (hb : b ∈ pOs)
    (hb3 : b3 ∈ pOs ∨ b3=a&&&b ∨ ∃ p ∈ pOs,b3=p|||(a&&&b))
    (hb4 : b4 ∈ pOs ∨ b4=a&&&b ∨ ∃ p ∈ pOs,b4=p|||(a&&&b))
    (hb6 : b6 ∈ pOs ∨ b6=a&&&b ∨ ∃ p ∈ pOs,b6=p|||(a&&&b))
    (hb7 : b7 ∈ pOs ∨ b7=a&&&b ∨ ∃ p ∈ pOs,b7=p|||(a&&&b))
    (h3r1 : (b3&&&R1_3)=R1_3) (h3r0 : (b3&&&R0_3)=0)
    (h4r1 : (b4&&&R1_4)=R1_4) (h4r0 : (b4&&&R0_4)=0)
    (h6r1 : (b6&&&R1_6)=R1_6) (h6r0 : (b6&&&R0_6)=0)
    (h7r1 : (b7&&&R1_7)=R1_7) (h7r0 : (b7&&&R0_7)=0)
    (hzs : ∀ z ∈ zs,(z&&&IND_SAFE)=0 ∧
      ∃ y F,(y ∈ pOs ∨ y=a&&&b ∨ ∃ p ∈ pOs,y=p|||(a&&&b)) ∧
        (F=ALL64 ∨ F=b3 ∨ F=b4 ∨ F=b6 ∨ F=b7 ∨ F=b3&&&b4) ∧
        z=y&&&F)
    (hcov : zs.foldl (fun acc z=>acc|||edgesOf z) 0=15) : False:=by
  have hpair : checkAW1_aU4_pair a b=true:=by
    rcases checkPairs_mem test_AW1_aU4 ha hb with h1 | h2
    · exact h1
    · rwa [checkAW1_aU4_pair_symm] at h2
  have hp4:=pureOrs_props.2.2.2
  have hsafe_spec : ∀ p ∈ 0 :: pOs,
      ((p&&&R0_3)=0 → p ∈ pSafe3) ∧ ((p&&&R0_4)=0 → p ∈ pSafe4) ∧
      ((p&&&R0_6)=0 → p ∈ pSafe6) ∧ ((p&&&R0_7)=0 → p ∈ pSafe7):=by
    intro p hp
    have h1:=List.all_eq_true.mp hp4 p hp
    simp only [Bool.and_eq_true,Bool.or_eq_true,bne_iff_ne,List.elem_eq_mem,decide_eq_true_eq] at h1
    exact ⟨fun h=>h1.1.1.1.resolve_left (not_not.mpr h),
           fun h=>h1.1.1.2.resolve_left (not_not.mpr h),
           fun h=>h1.1.2.resolve_left (not_not.mpr h),
           fun h=>h1.2.resolve_left (not_not.mpr h)⟩
  have hne3 : b3 ≠ 0:=by intro e;rw [e,ba0l] at h3r1;exact (by decide : (0 : ℕ) ≠ R1_3) h3r1
  have hne4 : b4 ≠ 0:=by intro e;rw [e,ba0l] at h4r1;exact (by decide : (0 : ℕ) ≠ R1_4) h4r1
  have hne6 : b6 ≠ 0:=by intro e;rw [e,ba0l] at h6r1;exact (by decide : (0 : ℕ) ≠ R1_6) h6r1
  have hne7 : b7 ≠ 0:=by intro e;rw [e,ba0l] at h7r1;exact (by decide : (0 : ℕ) ≠ R1_7) h7r1
  let g0:=a&&&b
  let ys:=g0 :: bWs
  let vb3:=validBs pSafe3 R1_3 R0_3 g0
  let vb4:=validBs pSafe4 R1_4 R0_4 g0
  let vb6:=validBs pSafe6 R1_6 R0_6 g0
  let vb7:=validBs pSafe7 R1_7 R0_7 g0
  have hm3 : b3 ∈ vb3:=mem_validBs (fun p hp=>(hsafe_spec p hp).1) hb3 hne3 h3r1 h3r0
  have hm4 : b4 ∈ vb4:=mem_validBs (fun p hp=>(hsafe_spec p hp).2.1) hb4 hne4 h4r1 h4r0
  have hm6 : b6 ∈ vb6:=mem_validBs (fun p hp=>(hsafe_spec p hp).2.2.1) hb6 hne6 h6r1 h6r0
  have hm7 : b7 ∈ vb7:=mem_validBs (fun p hp=>(hsafe_spec p hp).2.2.2) hb7 hne7 h7r1 h7r0
  let c0:=cWF ys ALL64
  let c3:=vb3.foldl (fun acc f=>acc|||cWF ys f) c0
  let c4:=vb4.foldl (fun acc f=>acc|||cWF ys f) c3
  let c6:=vb6.foldl (fun acc f=>acc|||cWF ys f) c4
  let c7:=vb7.foldl (fun acc f=>acc|||cWF ys f) c6
  let c34:=vb3.foldl (fun acc f3=>vb4.foldl (fun acc2 f4=>acc2|||cWF ys (f3&&&f4)) acc) c7
  have hc34_ne : c34 ≠ 15:=by simpa [checkAW1_aU4_pair,g0,ys,vb3,vb4,vb6,vb7,c0,c3,c4,c6,c7,c34] using hpair
  have htrans : ∀ x y z : ℕ,(x|||y)=y → (y|||z)=z → (x|||z)=z:=by
    intro x y z hxy hyz;rw [← hyz,← boa,hxy]
  have hc0_3 : (c0|||c3)=c3:=foldl_or_ge (cWF ys) vb3 c0
  have hc3_4 : (c3|||c4)=c4:=foldl_or_ge (cWF ys) vb4 c3
  have hc4_6 : (c4|||c6)=c6:=foldl_or_ge (cWF ys) vb6 c4
  have hc6_7 : (c6|||c7)=c7:=foldl_or_ge (cWF ys) vb7 c6
  have hc7_34 : (c7|||c34)=c34:=by
    have hstep : ∀ (l : List ℕ) (init : ℕ),
        (init|||l.foldl (fun acc f3=>vb4.foldl (fun acc2 f4=>acc2|||cWF ys (f3&&&f4)) acc) init) =
        l.foldl (fun acc f3=>vb4.foldl (fun acc2 f4=>acc2|||cWF ys (f3&&&f4)) acc) init:=by
      intro l
      induction l with
      | nil=>intro init;exact bos init
      | cons f3 t ih =>
        intro init;simp only [List.foldl_cons]
        exact htrans _ _ _ (foldl_or_ge (fun f4=>cWF ys (f3&&&f4)) vb4 init) (ih _)
    exact hstep vb3 c7
  have hcov_le_c34 : ∀ F,(F=ALL64 ∨ F=b3 ∨ F=b4 ∨ F=b6 ∨ F=b7 ∨ F=b3&&&b4) →
      (cWF ys F|||c34)=c34:=by
    intro F hF
    rcases hF with rfl | rfl | rfl | rfl | rfl | rfl
    · exact htrans _ _ _ hc0_3 (htrans _ _ _ hc3_4 (htrans _ _ _ hc4_6 (htrans _ _ _ hc6_7 hc7_34)))
    · exact htrans _ _ _ (foldl_or_mem (cWF ys) vb3 c0 hm3)
        (htrans _ _ _ hc3_4 (htrans _ _ _ hc4_6 (htrans _ _ _ hc6_7 hc7_34)))
    · exact htrans _ _ _ (foldl_or_mem (cWF ys) vb4 c3 hm4)
        (htrans _ _ _ hc4_6 (htrans _ _ _ hc6_7 hc7_34))
    · exact htrans _ _ _ (foldl_or_mem (cWF ys) vb6 c4 hm6) (htrans _ _ _ hc6_7 hc7_34)
    · exact htrans _ _ _ (foldl_or_mem (cWF ys) vb7 c6 hm7) hc7_34
    · have hinner : ∀ (l : List ℕ) (init : ℕ),b3 ∈ l →
          (cWF ys (b3&&&b4) |||
            l.foldl (fun acc f3=>vb4.foldl (fun acc2 f4=>acc2|||cWF ys (f3&&&f4)) acc) init) =
          l.foldl (fun acc f3=>vb4.foldl (fun acc2 f4=>acc2|||cWF ys (f3&&&f4)) acc) init:=by
        intro l
        induction l with
        | nil=>intro _ hm;simp at hm
        | cons f3 t ih =>
          intro init hm;simp only [List.foldl_cons]
          rcases List.mem_cons.mp hm with rfl | ht
          · have h1:=foldl_or_mem (fun f4=>cWF ys (b3&&&f4)) vb4 init hm4
            have h2 : ∀ (t' : List ℕ) (i' : ℕ),
                (i'|||t'.foldl (fun acc f3'=>vb4.foldl (fun acc2 f4=>acc2|||cWF ys (f3'&&&f4)) acc) i') =
                t'.foldl (fun acc f3'=>vb4.foldl (fun acc2 f4=>acc2|||cWF ys (f3'&&&f4)) acc) i':=by
              intro t';induction t' with
              | nil=>intro i';exact bos i'
              | cons u v ihv =>
                intro i';simp only [List.foldl_cons]
                exact htrans _ _ _ (foldl_or_ge (fun f4=>cWF ys (u&&&f4)) vb4 i') (ihv _)
            exact htrans _ _ _ h1 (h2 t _)
          · exact ih _ ht
      exact hinner vb3 c7 hm3
  have hfold_le : ∀ (l : List ℕ) (init : ℕ),
      (∀ z ∈ l,(edgesOf z|||c34)=c34) → (init|||c34)=c34 →
      (l.foldl (fun acc z=>acc|||edgesOf z) init|||c34)=c34:=by
    intro l
    induction l with
    | nil=>intro init _ hi;exact hi
    | cons z t ih =>
      intro init hl hi
      simp only [List.foldl_cons]
      apply ih (init|||edgesOf z) (fun w hw=>hl w (List.mem_cons_of_mem z hw))
      exact (bit_or_le_iff init (edgesOf z) c34).mpr ⟨hi,hl z (List.mem_cons_self ..)⟩
  have h15_le : (15|||c34)=c34:=by
    rw [← hcov]
    apply hfold_le zs 0
    · intro z hz
      obtain ⟨hsafe,y,F,hy,hF,rfl⟩:=hzs z hz
      exact htrans _ _ _ (cWFg0 g0 F y hy hsafe) (hcov_le_c34 F hF)
    · exact bo0l c34
  have hc34_lt16 : c34 < 16:=by
    have hedges_lt : ∀ w,edgesOf w < 16:=by
      intro w;unfold edgesOf
      cases ((w&&&E01) != 0)<;>cases ((w&&&E12) != 0) <;>
      cases ((w&&&E05) != 0)<;>cases ((w&&&E58) != 0)<;>decide
    have hor_lt : ∀ x y,x < 16 → y < 16 → (x|||y) < 16:=by
      intro x y hx hy
      exact (by decide : ∀ a b : Fin 16,(a.val|||b.val) < 16) ⟨x,hx⟩ ⟨y,hy⟩
    have hcov_lt : ∀ F,cWF ys F < 16:=by
      intro F;unfold cWF
      have hf : ∀ (l : List ℕ) (init : ℕ),init < 16 →
          l.foldl (fun acc y=>let z:=y&&&F;if (z&&&IND_SAFE)==0 then acc|||edgesOf z else acc) init < 16:=by
        intro l;induction l with
        | nil=>intro init hi;exact hi
        | cons y t ih =>
          intro init hi;simp only [List.foldl_cons]
          split_ifs
          · exact ih _ (hor_lt _ _ hi (hedges_lt _))
          · exact ih _ hi
      exact hf ys 0 (by omega)
    have hf1 : ∀ (l : List ℕ) (f : ℕ → ℕ) (init : ℕ),(∀ x,f x < 16) → init < 16 →
        l.foldl (fun acc x=>acc|||f x) init < 16:=by
      intro l f;induction l with
      | nil=>intro init _ hi;exact hi
      | cons x t ih=>intro init hf hi;simp only [List.foldl_cons];exact ih _ hf (hor_lt _ _ hi (hf x))
    have hc0l : c0 < 16:=hcov_lt ALL64
    have hc3l : c3 < 16:=hf1 vb3 (cWF ys) c0 hcov_lt hc0l
    have hc4l : c4 < 16:=hf1 vb4 (cWF ys) c3 hcov_lt hc3l
    have hc6l : c6 < 16:=hf1 vb6 (cWF ys) c4 hcov_lt hc4l
    have hc7l : c7 < 16:=hf1 vb7 (cWF ys) c6 hcov_lt hc6l
    have hf2 : ∀ (l : List ℕ) (init : ℕ),init < 16 →
        l.foldl (fun acc f3=>vb4.foldl (fun acc2 f4=>acc2|||cWF ys (f3&&&f4)) acc) init < 16:=by
      intro l;induction l with
      | nil=>intro init hi;exact hi
      | cons f3 t ih=>intro init hi;simp only [List.foldl_cons];exact ih _ (hf1 vb4 (fun f4=>cWF ys (f3&&&f4)) init (fun _=>hcov_lt _) hi)
    exact hf2 vb3 c7 hc7l
  have hc34_eq15 : c34=15 :=
    (by decide : ∀ x : Fin 16,(15|||x.val)=x.val → x.val=15) ⟨c34,hc34_lt16⟩ h15_le
  exact hc34_ne hc34_eq15
lemma lam5_from_4 {m4 x : ℕ} (hm4 : m4=2 ∨ m4=3) (hx1 : 1 ≤ x) (hx2 : x ≤ 15)
    (hlam : isLP m4 x=true) : sort5 1 m4 4 8 x ∈ lam5List:=by
  have hc:=checkLam5From4_true
  unfold checkLam5From4 at hc
  simp only [List.all_eq_true] at hc
  have hm4_mem : m4 ∈ ([2,3] : List ℕ):=by rcases hm4 with rfl | rfl<;>simp
  have hx_mem : x ∈ (List.range 15).map (· + 1) :=
    List.mem_map.mpr ⟨x - 1,List.mem_range.mpr (by omega),by omega⟩
  have h1:=hc m4 hm4_mem x hx_mem
  simp only [hlam,Bool.not_true,Bool.false_or,List.elem_eq_mem,decide_eq_true_eq] at h1
  exact h1
lemma kill_AW0_aU5 {s0 s1 s2 s3 s4 b0 b1 b2 b3 b4 : ℕ} {zs : List ℕ}
    (hlam : (s0,s1,s2,s3,s4) ∈ lam5List)
    (hb0 : b0 ∈ pOs ∧ (b0&&&rR1 s0)=rR1 s0)
    (hb1 : b1 ∈ pOs ∧ (b1&&&rR1 s1)=rR1 s1)
    (hb2 : b2 ∈ pOs ∧ (b2&&&rR1 s2)=rR1 s2)
    (hb3 : b3 ∈ pOs ∧ (b3&&&rR1 s3)=rR1 s3)
    (hb4 : b4 ∈ pOs ∧ (b4&&&rR1 s4)=rR1 s4)
    (hfin3 : (((if (s4&&&1) != 0 then b4 else ALL64) &&&
               (if (s3&&&1) != 0 then b3 else ALL64) &&&
               (if (s2&&&1) != 0 then b2 else ALL64) &&&
               (if (s1&&&1) != 0 then b1 else ALL64) &&&
               (if (s0&&&1) != 0 then b0 else ALL64))&&&R0_3)=0)
    (hfin4 : (((if (s4&&&2) != 0 then b4 else ALL64) &&&
               (if (s3&&&2) != 0 then b3 else ALL64) &&&
               (if (s2&&&2) != 0 then b2 else ALL64) &&&
               (if (s1&&&2) != 0 then b1 else ALL64) &&&
               (if (s0&&&2) != 0 then b0 else ALL64))&&&R0_4)=0)
    (hfin6 : (((if (s4&&&4) != 0 then b4 else ALL64) &&&
               (if (s3&&&4) != 0 then b3 else ALL64) &&&
               (if (s2&&&4) != 0 then b2 else ALL64) &&&
               (if (s1&&&4) != 0 then b1 else ALL64) &&&
               (if (s0&&&4) != 0 then b0 else ALL64))&&&R0_6)=0)
    (hfin7 : (((if (s4&&&8) != 0 then b4 else ALL64) &&&
               (if (s3&&&8) != 0 then b3 else ALL64) &&&
               (if (s2&&&8) != 0 then b2 else ALL64) &&&
               (if (s1&&&8) != 0 then b1 else ALL64) &&&
               (if (s0&&&8) != 0 then b0 else ALL64))&&&R0_7)=0)
    (hzs : ∀ z ∈ zs,(z&&&IND_SAFE)=0 ∧
      ∃ y sub,y ∈ pOs ∧ sub ∈ vS5 s0 s1 s2 s3 s4 ∧
        z=y&&&cM5 sub b0 b1 b2 b3 b4)
    (hcov : zs.foldl (fun acc z=>acc|||edgesOf z) 0=15) : False:=by
  have ht:=List.all_eq_true.mp test_AW0_aU5 (s0,s1,s2,s3,s4) hlam
  have hpv : ∀ m b,b ∈ pOs → (b&&&rR1 m)=rR1 m → b ∈ pureValid m:=by
    intro m b hb hr;unfold pureValid;exact List.mem_filter.mpr ⟨hb,by simp [hr]⟩
  have hALL : ∀ x ∈ pOs,(ALL64&&&x)=x:=by
    have hlt : pOs.all (fun x=>(ALL64&&&x)==x)=true:=by decide +kernel
    intro x hx;exact beq_iff_eq.mp (List.all_eq_true.mp hlt x hx)
  have hA0:=hALL b0 hb0.1
  have hA1:=hALL b1 hb1.1
  have hA2:=hALL b2 hb2.1
  have hA3:=hALL b3 hb3.1
  have hA4:=hALL b4 hb4.1
  have hAA : (ALL64&&&ALL64)=ALL64:=bas ALL64
  have hbit_or0 : ∀ a b bit : ℕ,(((a|||b)&&&bit) != 0)=false →
      ((a&&&bit) != 0)=false ∧ ((b&&&bit) != 0)=false:=by
    intro a b bit h
    simp only [bne_eq_false_iff_eq] at h ⊢
    exact bit_sub_of_or_zero h
  have hrew : ∀ (x y : ℕ) (cond : Bool),(ALL64&&&x)=x →
      (if cond then x&&&y else x)=(x&&&(if cond then y else ALL64)):=by
    intro x y cond hx
    cases cond
    · simp only [Bool.false_eq_true,↓reduceIte];rw [bac,hx]
    · rfl
  have hAll_if : ∀ (b : ℕ) (cond : Bool),(ALL64&&&b)=b →
      (ALL64&&&(if cond then b else ALL64))=(if cond then b else ALL64):=by
    intro b cond hb;cases cond<;>simp [hb,hAA]
  have hAll_and : ∀ x y : ℕ,(ALL64&&&x)=x → (ALL64&&&(x&&&y))=(x&&&y):=by
    intro x y hx;rw [← baa,hx]
  have hstep_fin : ∀ (rem : ℕ) (i3 i4 i6 i7 : ℕ),
      (((rem&&&1) != 0)=false → (i3&&&R0_3)=0) →
      (((rem&&&2) != 0)=false → (i4&&&R0_4)=0) →
      (((rem&&&4) != 0)=false → (i6&&&R0_6)=0) →
      (((rem&&&8) != 0)=false → (i7&&&R0_7)=0) →
      (((rem&&&1) != 0||(i3&&&R0_3)==0) &&
       ((rem&&&2) != 0||(i4&&&R0_4)==0) &&
       ((rem&&&4) != 0||(i6&&&R0_6)==0) &&
       ((rem&&&8) != 0||(i7&&&R0_7)==0))=true:=by
    intro rem i3 i4 i6 i7 c3 c4 c6 c7
    simp only [Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq]
    refine ⟨⟨⟨?_,?_⟩,?_⟩,?_⟩
    · cases h : ((rem&&&1) != 0)<;>[exact Or.inr (c3 h);exact Or.inl rfl]
    · cases h : ((rem&&&2) != 0)<;>[exact Or.inr (c4 h);exact Or.inl rfl]
    · cases h : ((rem&&&4) != 0)<;>[exact Or.inr (c6 h);exact Or.inl rfl]
    · cases h : ((rem&&&8) != 0)<;>[exact Or.inr (c7 h);exact Or.inl rfl]
  have hcheck_cov : checkChainCov5 (vS5 s0 s1 s2 s3 s4) b0 b1 b2 b3 b4=true:=by
    unfold checkLam5Tuple at ht
    dsimp only at ht
    have h4:=List.all_eq_true.mp ht b4 (hpv s4 b4 hb4.1 hb4.2)
    have hEq4 : ∀ bit,(if (s4&&&bit) != 0 then ALL64&&&b4 else ALL64) =
        (if (s4&&&bit) != 0 then b4 else ALL64):=fun bit=>by split_ifs<;>simp [hA4]
    have hA_f4 : ∀ bit,(ALL64&&&(if (s4&&&bit) != 0 then b4 else ALL64))=(if (s4&&&bit) != 0 then b4 else ALL64) :=
      fun bit=>hAll_if b4 _ hA4
    have hEq3 : ∀ bit,
        (let a:=if (s4&&&bit) != 0 then ALL64&&&b4 else ALL64
         if (s3&&&bit) != 0 then a&&&b3 else a) =
        ((if (s4&&&bit) != 0 then b4 else ALL64)&&&(if (s3&&&bit) != 0 then b3 else ALL64)) :=
      fun bit=>by dsimp only;rw [hEq4 bit];exact hrew _ _ _ (hA_f4 bit)
    have hA_f3 : ∀ bit,(ALL64&&&((if (s4&&&bit) != 0 then b4 else ALL64)&&&(if (s3&&&bit) != 0 then b3 else ALL64))) =
        ((if (s4&&&bit) != 0 then b4 else ALL64)&&&(if (s3&&&bit) != 0 then b3 else ALL64)) :=
      fun bit=>hAll_and _ _ (hA_f4 bit)
    have hEq2 : ∀ bit,
        (let a:=if (s4&&&bit) != 0 then ALL64&&&b4 else ALL64
         let c:=if (s3&&&bit) != 0 then a&&&b3 else a
         if (s2&&&bit) != 0 then c&&&b2 else c) =
        (((if (s4&&&bit) != 0 then b4 else ALL64)&&&(if (s3&&&bit) != 0 then b3 else ALL64)) &&&
          (if (s2&&&bit) != 0 then b2 else ALL64)) :=
      fun bit=>by dsimp only;rw [hEq3 bit];exact hrew _ _ _ (hA_f3 bit)
    have hA_f2 : ∀ bit,(ALL64&&&(((if (s4&&&bit) != 0 then b4 else ALL64)&&&(if (s3&&&bit) != 0 then b3 else ALL64)) &&&
        (if (s2&&&bit) != 0 then b2 else ALL64))) =
        (((if (s4&&&bit) != 0 then b4 else ALL64)&&&(if (s3&&&bit) != 0 then b3 else ALL64)) &&&
        (if (s2&&&bit) != 0 then b2 else ALL64)) :=
      fun bit=>hAll_and _ _ (hA_f3 bit)
    have hEq1 : ∀ bit,
        (let a:=if (s4&&&bit) != 0 then ALL64&&&b4 else ALL64
         let c:=if (s3&&&bit) != 0 then a&&&b3 else a
         let d:=if (s2&&&bit) != 0 then c&&&b2 else c
         if (s1&&&bit) != 0 then d&&&b1 else d) =
        ((((if (s4&&&bit) != 0 then b4 else ALL64)&&&(if (s3&&&bit) != 0 then b3 else ALL64)) &&&
          (if (s2&&&bit) != 0 then b2 else ALL64))&&&(if (s1&&&bit) != 0 then b1 else ALL64)) :=
      fun bit=>by dsimp only;rw [hEq2 bit];exact hrew _ _ _ (hA_f2 bit)
    have hA_f1 : ∀ bit,(ALL64&&&((((if (s4&&&bit) != 0 then b4 else ALL64)&&&(if (s3&&&bit) != 0 then b3 else ALL64)) &&&
        (if (s2&&&bit) != 0 then b2 else ALL64))&&&(if (s1&&&bit) != 0 then b1 else ALL64))) =
        ((((if (s4&&&bit) != 0 then b4 else ALL64)&&&(if (s3&&&bit) != 0 then b3 else ALL64)) &&&
        (if (s2&&&bit) != 0 then b2 else ALL64))&&&(if (s1&&&bit) != 0 then b1 else ALL64)) :=
      fun bit=>hAll_and _ _ (hA_f2 bit)
    have hEq0 : ∀ bit,
        (let a:=if (s4&&&bit) != 0 then ALL64&&&b4 else ALL64
         let c:=if (s3&&&bit) != 0 then a&&&b3 else a
         let d:=if (s2&&&bit) != 0 then c&&&b2 else c
         let e:=if (s1&&&bit) != 0 then d&&&b1 else d
         if (s0&&&bit) != 0 then e&&&b0 else e) =
        (((((if (s4&&&bit) != 0 then b4 else ALL64)&&&(if (s3&&&bit) != 0 then b3 else ALL64)) &&&
          (if (s2&&&bit) != 0 then b2 else ALL64))&&&(if (s1&&&bit) != 0 then b1 else ALL64)) &&&
          (if (s0&&&bit) != 0 then b0 else ALL64)) :=
      fun bit=>by dsimp only;rw [hEq1 bit];exact hrew _ _ _ (hA_f1 bit)
    have hAr : ∀ x,(ALL64&&&x)=x → (x&&&ALL64)=x:=fun x hx=>by rw [bac];exact hx
    have hok4:=hstep_fin (s0|||s1|||s2|||s3)
      (if (s4&&&1) != 0 then ALL64&&&b4 else ALL64)
      (if (s4&&&2) != 0 then ALL64&&&b4 else ALL64)
      (if (s4&&&4) != 0 then ALL64&&&b4 else ALL64)
      (if (s4&&&8) != 0 then ALL64&&&b4 else ALL64)
      (fun hr=>by
        obtain ⟨h012,h3z⟩:=hbit_or0 _ _ 1 hr;obtain ⟨h01,h2z⟩:=hbit_or0 _ _ 1 h012;obtain ⟨h0z,h1z⟩:=hbit_or0 _ _ 1 h01
        rw [hEq4 1];simp only [h0z,h1z,h2z,h3z,Bool.false_eq_true,↓reduceIte] at hfin3
        simpa only [hAr _ (hA_f4 1)] using hfin3)
      (fun hr=>by
        obtain ⟨h012,h3z⟩:=hbit_or0 _ _ 2 hr;obtain ⟨h01,h2z⟩:=hbit_or0 _ _ 2 h012;obtain ⟨h0z,h1z⟩:=hbit_or0 _ _ 2 h01
        rw [hEq4 2];simp only [h0z,h1z,h2z,h3z,Bool.false_eq_true,↓reduceIte] at hfin4
        simpa only [hAr _ (hA_f4 2)] using hfin4)
      (fun hr=>by
        obtain ⟨h012,h3z⟩:=hbit_or0 _ _ 4 hr;obtain ⟨h01,h2z⟩:=hbit_or0 _ _ 4 h012;obtain ⟨h0z,h1z⟩:=hbit_or0 _ _ 4 h01
        rw [hEq4 4];simp only [h0z,h1z,h2z,h3z,Bool.false_eq_true,↓reduceIte] at hfin6
        simpa only [hAr _ (hA_f4 4)] using hfin6)
      (fun hr=>by
        obtain ⟨h012,h3z⟩:=hbit_or0 _ _ 8 hr;obtain ⟨h01,h2z⟩:=hbit_or0 _ _ 8 h012;obtain ⟨h0z,h1z⟩:=hbit_or0 _ _ 8 h01
        rw [hEq4 8];simp only [h0z,h1z,h2z,h3z,Bool.false_eq_true,↓reduceIte] at hfin7
        simpa only [hAr _ (hA_f4 8)] using hfin7)
    simp only [hok4,Bool.not_true,Bool.false_eq_true,↓reduceIte] at h4
    have h3:=List.all_eq_true.mp h4 b3 (hpv s3 b3 hb3.1 hb3.2)
    have hok3:=hstep_fin (s0|||s1|||s2)
      (if (s3&&&1) != 0 then (if (s4&&&1) != 0 then ALL64&&&b4 else ALL64)&&&b3 else (if (s4&&&1) != 0 then ALL64&&&b4 else ALL64))
      (if (s3&&&2) != 0 then (if (s4&&&2) != 0 then ALL64&&&b4 else ALL64)&&&b3 else (if (s4&&&2) != 0 then ALL64&&&b4 else ALL64))
      (if (s3&&&4) != 0 then (if (s4&&&4) != 0 then ALL64&&&b4 else ALL64)&&&b3 else (if (s4&&&4) != 0 then ALL64&&&b4 else ALL64))
      (if (s3&&&8) != 0 then (if (s4&&&8) != 0 then ALL64&&&b4 else ALL64)&&&b3 else (if (s4&&&8) != 0 then ALL64&&&b4 else ALL64))
      (fun hr=>by
        obtain ⟨h01,h2z⟩:=hbit_or0 _ _ 1 hr;obtain ⟨h0z,h1z⟩:=hbit_or0 _ _ 1 h01
        rw [hEq3 1];simp only [h0z,h1z,h2z,Bool.false_eq_true,↓reduceIte] at hfin3
        simpa only [hAr _ (hA_f3 1)] using hfin3)
      (fun hr=>by
        obtain ⟨h01,h2z⟩:=hbit_or0 _ _ 2 hr;obtain ⟨h0z,h1z⟩:=hbit_or0 _ _ 2 h01
        rw [hEq3 2];simp only [h0z,h1z,h2z,Bool.false_eq_true,↓reduceIte] at hfin4
        simpa only [hAr _ (hA_f3 2)] using hfin4)
      (fun hr=>by
        obtain ⟨h01,h2z⟩:=hbit_or0 _ _ 4 hr;obtain ⟨h0z,h1z⟩:=hbit_or0 _ _ 4 h01
        rw [hEq3 4];simp only [h0z,h1z,h2z,Bool.false_eq_true,↓reduceIte] at hfin6
        simpa only [hAr _ (hA_f3 4)] using hfin6)
      (fun hr=>by
        obtain ⟨h01,h2z⟩:=hbit_or0 _ _ 8 hr;obtain ⟨h0z,h1z⟩:=hbit_or0 _ _ 8 h01
        rw [hEq3 8];simp only [h0z,h1z,h2z,Bool.false_eq_true,↓reduceIte] at hfin7
        simpa only [hAr _ (hA_f3 8)] using hfin7)
    simp only [hok3,Bool.not_true,Bool.false_eq_true,↓reduceIte] at h3
    have h2:=List.all_eq_true.mp h3 b2 (hpv s2 b2 hb2.1 hb2.2)
    have hok2:=hstep_fin (s0|||s1)
      (let a:=if (s4&&&1) != 0 then ALL64&&&b4 else ALL64;let c:=if (s3&&&1) != 0 then a&&&b3 else a;if (s2&&&1) != 0 then c&&&b2 else c)
      (let a:=if (s4&&&2) != 0 then ALL64&&&b4 else ALL64;let c:=if (s3&&&2) != 0 then a&&&b3 else a;if (s2&&&2) != 0 then c&&&b2 else c)
      (let a:=if (s4&&&4) != 0 then ALL64&&&b4 else ALL64;let c:=if (s3&&&4) != 0 then a&&&b3 else a;if (s2&&&4) != 0 then c&&&b2 else c)
      (let a:=if (s4&&&8) != 0 then ALL64&&&b4 else ALL64;let c:=if (s3&&&8) != 0 then a&&&b3 else a;if (s2&&&8) != 0 then c&&&b2 else c)
      (fun hr=>by
        obtain ⟨h0z,h1z⟩:=hbit_or0 _ _ 1 hr
        rw [hEq2 1];simp only [h0z,h1z,Bool.false_eq_true,↓reduceIte] at hfin3
        simpa only [hAr _ (hA_f2 1)] using hfin3)
      (fun hr=>by
        obtain ⟨h0z,h1z⟩:=hbit_or0 _ _ 2 hr
        rw [hEq2 2];simp only [h0z,h1z,Bool.false_eq_true,↓reduceIte] at hfin4
        simpa only [hAr _ (hA_f2 2)] using hfin4)
      (fun hr=>by
        obtain ⟨h0z,h1z⟩:=hbit_or0 _ _ 4 hr
        rw [hEq2 4];simp only [h0z,h1z,Bool.false_eq_true,↓reduceIte] at hfin6
        simpa only [hAr _ (hA_f2 4)] using hfin6)
      (fun hr=>by
        obtain ⟨h0z,h1z⟩:=hbit_or0 _ _ 8 hr
        rw [hEq2 8];simp only [h0z,h1z,Bool.false_eq_true,↓reduceIte] at hfin7
        simpa only [hAr _ (hA_f2 8)] using hfin7)
    simp only [hok2,Bool.not_true,Bool.false_eq_true,↓reduceIte] at h2
    have h1:=List.all_eq_true.mp h2 b1 (hpv s1 b1 hb1.1 hb1.2)
    have hok1:=hstep_fin s0
      (let a:=if (s4&&&1) != 0 then ALL64&&&b4 else ALL64;let c:=if (s3&&&1) != 0 then a&&&b3 else a;let d:=if (s2&&&1) != 0 then c&&&b2 else c;if (s1&&&1) != 0 then d&&&b1 else d)
      (let a:=if (s4&&&2) != 0 then ALL64&&&b4 else ALL64;let c:=if (s3&&&2) != 0 then a&&&b3 else a;let d:=if (s2&&&2) != 0 then c&&&b2 else c;if (s1&&&2) != 0 then d&&&b1 else d)
      (let a:=if (s4&&&4) != 0 then ALL64&&&b4 else ALL64;let c:=if (s3&&&4) != 0 then a&&&b3 else a;let d:=if (s2&&&4) != 0 then c&&&b2 else c;if (s1&&&4) != 0 then d&&&b1 else d)
      (let a:=if (s4&&&8) != 0 then ALL64&&&b4 else ALL64;let c:=if (s3&&&8) != 0 then a&&&b3 else a;let d:=if (s2&&&8) != 0 then c&&&b2 else c;if (s1&&&8) != 0 then d&&&b1 else d)
      (fun h0z=>by rw [hEq1 1];simp only [h0z,Bool.false_eq_true,↓reduceIte] at hfin3;simpa only [hAr _ (hA_f1 1)] using hfin3)
      (fun h0z=>by rw [hEq1 2];simp only [h0z,Bool.false_eq_true,↓reduceIte] at hfin4;simpa only [hAr _ (hA_f1 2)] using hfin4)
      (fun h0z=>by rw [hEq1 4];simp only [h0z,Bool.false_eq_true,↓reduceIte] at hfin6;simpa only [hAr _ (hA_f1 4)] using hfin6)
      (fun h0z=>by rw [hEq1 8];simp only [h0z,Bool.false_eq_true,↓reduceIte] at hfin7;simpa only [hAr _ (hA_f1 8)] using hfin7)
    simp only [hok1,Bool.not_true,Bool.false_eq_true,↓reduceIte] at h1
    have h0:=List.all_eq_true.mp h1 b0 (hpv s0 b0 hb0.1 hb0.2)
    have hok0:=hstep_fin 0
      (let a:=if (s4&&&1) != 0 then ALL64&&&b4 else ALL64;let c:=if (s3&&&1) != 0 then a&&&b3 else a;let d:=if (s2&&&1) != 0 then c&&&b2 else c;let e:=if (s1&&&1) != 0 then d&&&b1 else d;if (s0&&&1) != 0 then e&&&b0 else e)
      (let a:=if (s4&&&2) != 0 then ALL64&&&b4 else ALL64;let c:=if (s3&&&2) != 0 then a&&&b3 else a;let d:=if (s2&&&2) != 0 then c&&&b2 else c;let e:=if (s1&&&2) != 0 then d&&&b1 else d;if (s0&&&2) != 0 then e&&&b0 else e)
      (let a:=if (s4&&&4) != 0 then ALL64&&&b4 else ALL64;let c:=if (s3&&&4) != 0 then a&&&b3 else a;let d:=if (s2&&&4) != 0 then c&&&b2 else c;let e:=if (s1&&&4) != 0 then d&&&b1 else d;if (s0&&&4) != 0 then e&&&b0 else e)
      (let a:=if (s4&&&8) != 0 then ALL64&&&b4 else ALL64;let c:=if (s3&&&8) != 0 then a&&&b3 else a;let d:=if (s2&&&8) != 0 then c&&&b2 else c;let e:=if (s1&&&8) != 0 then d&&&b1 else d;if (s0&&&8) != 0 then e&&&b0 else e)
      (fun _=>by rw [hEq0 1];exact hfin3)
      (fun _=>by rw [hEq0 2];exact hfin4)
      (fun _=>by rw [hEq0 4];exact hfin6)
      (fun _=>by rw [hEq0 8];exact hfin7)
    simp only [hok0,Bool.not_true,Bool.false_eq_true,↓reduceIte] at h0
    exact h0
  let subs:=vS5 s0 s1 s2 s3 s4
  let covAll:=subs.foldl (fun acc sub=>acc|||cWF bWs (cM5 sub b0 b1 b2 b3 b4)) 0
  have hcov_ne : covAll ≠ 15:=by simpa [checkChainCov5,subs,covAll] using hcheck_cov
  have htrans : ∀ x y z : ℕ,(x|||y)=y → (y|||z)=z → (x|||z)=z:=by
    intro x y z hxy hyz;rw [← hyz,← boa,hxy]
  have hfold_le : ∀ (l : List ℕ) (init : ℕ),
      (∀ z ∈ l,(edgesOf z|||covAll)=covAll) → (init|||covAll)=covAll →
      (l.foldl (fun acc z=>acc|||edgesOf z) init|||covAll)=covAll:=by
    intro l
    induction l with
    | nil=>intro init _ hi;exact hi
    | cons z t ih =>
      intro init hl hi
      simp only [List.foldl_cons]
      apply ih (init|||edgesOf z) (fun w hw=>hl w (List.mem_cons_of_mem z hw))
      exact (bit_or_le_iff init (edgesOf z) covAll).mpr ⟨hi,hl z (List.mem_cons_self ..)⟩
  have h15_le : (15|||covAll)=covAll:=by
    rw [← hcov]
    apply hfold_le zs 0
    · intro z hz
      obtain ⟨hsafe,y,sub,hy,hsub,rfl⟩:=hzs z hz
      have h1:=cWFp bWs (cM5 sub b0 b1 b2 b3 b4) y (fun _ h=>h) hy hsafe
      have h2:=foldl_or_mem (fun s=>cWF bWs (cM5 s b0 b1 b2 b3 b4)) subs 0 hsub
      exact htrans _ _ _ h1 h2
    · exact bo0l covAll
  have hcov_lt16 : covAll < 16:=by
    have hedges_lt : ∀ w,edgesOf w < 16:=by
      intro w;unfold edgesOf
      cases ((w&&&E01) != 0)<;>cases ((w&&&E12) != 0) <;>
      cases ((w&&&E05) != 0)<;>cases ((w&&&E58) != 0)<;>decide
    have hor_lt : ∀ x y,x < 16 → y < 16 → (x|||y) < 16:=fun x y hx hy =>
      (by decide : ∀ a b : Fin 16,(a.val|||b.val) < 16) ⟨x,hx⟩ ⟨y,hy⟩
    have hcov_lt : ∀ F,cWF bWs F < 16:=by
      intro F;unfold cWF
      have hf : ∀ (l : List ℕ) (init : ℕ),init < 16 →
          l.foldl (fun acc y=>let z:=y&&&F;if (z&&&IND_SAFE)==0 then acc|||edgesOf z else acc) init < 16:=by
        intro l;induction l with
        | nil=>intro init hi;exact hi
        | cons y t ih =>
          intro init hi;simp only [List.foldl_cons]
          split_ifs
          · exact ih _ (hor_lt _ _ hi (hedges_lt _))
          · exact ih _ hi
      exact hf bWs 0 (by omega)
    have hf1 : ∀ (l : List ℕ) (init : ℕ),init < 16 →
        l.foldl (fun acc s=>acc|||cWF bWs (cM5 s b0 b1 b2 b3 b4)) init < 16:=by
      intro l;induction l with
      | nil=>intro init hi;exact hi
      | cons s t ih=>intro init hi;simp only [List.foldl_cons];exact ih _ (hor_lt _ _ hi (hcov_lt _))
    exact hf1 subs 0 (by omega)
  have hcov_eq15 : covAll=15 :=
    (by decide : ∀ x : Fin 16,(15|||x.val)=x.val → x.val=15) ⟨covAll,hcov_lt16⟩ h15_le
  exact hcov_ne hcov_eq15
lemma mem_insertSorted (x y : ℕ) (l : List ℕ) : y ∈ iSr x l ↔ y=x ∨ y ∈ l:=by
  induction l with
  | nil=>simp [iSr]
  | cons z zs ih =>
    unfold iSr
    split_ifs with h1 h2
    · simp [List.mem_cons]
    · have hxz : x=z:=beq_iff_eq.mp h2
      subst hxz
      simp only [List.mem_cons]
      tauto
    · simp only [List.mem_cons,ih]
      tauto
lemma pairwise_insertSorted (x : ℕ) (l : List ℕ) (h : l.Pairwise (· < ·)) :
    (iSr x l).Pairwise (· < ·):=by
  induction l with
  | nil=>simp [iSr]
  | cons z zs ih =>
    unfold iSr
    split_ifs with h1 h2
    · rw [List.pairwise_cons] at h ⊢
      refine ⟨fun w hw=>?_,List.pairwise_cons.mpr h⟩
      rcases List.mem_cons.mp hw with rfl | hzs
      · exact h1
      · exact lt_trans h1 (h.1 w hzs)
    · exact h
    · rw [List.pairwise_cons] at h ⊢
      have hne : x ≠ z:=fun e=>h2 (beq_iff_eq.mpr e)
      have hzx : z < x:=by omega
      refine ⟨fun w hw=>?_,ih h.2⟩
      rcases (mem_insertSorted x w zs).mp hw with rfl | hzs
      · exact hzx
      · exact h.1 w hzs
lemma mem_sortUnique (y : ℕ) (l : List ℕ) : y ∈ sUn l ↔ y ∈ l:=by
  unfold sUn
  have h : ∀ (l acc : List ℕ),y ∈ l.foldl (fun a x=>iSr x a) acc ↔ y ∈ acc ∨ y ∈ l:=by
    intro l
    induction l with
    | nil=>intro acc;simp
    | cons x xs ih =>
      intro acc
      simp only [List.foldl_cons,ih,mem_insertSorted,List.mem_cons]
      tauto
  simpa using h l []
lemma pairwise_sortUnique (l : List ℕ) : (sUn l).Pairwise (· < ·):=by
  unfold sUn
  have h : ∀ (l acc : List ℕ),acc.Pairwise (· < ·) →
      (l.foldl (fun a x=>iSr x a) acc).Pairwise (· < ·):=by
    intro l
    induction l with
    | nil=>intro acc ha;exact ha
    | cons x xs ih=>intro acc ha;exact ih _ (pairwise_insertSorted x acc ha)
  exact h l [] List.Pairwise.nil
lemma sorted_eq_of_mem_iff {S T : List ℕ} (hS : S.Pairwise (· < ·)) (hT : T.Pairwise (· < ·))
    (h : ∀ x,x ∈ S ↔ x ∈ T) : S=T:=by
  induction S generalizing T with
  | nil =>
    cases T with
    | nil=>rfl
    | cons t ts=>exact False.elim (by simpa using (h t).mpr (List.mem_cons_self ..))
  | cons s ss ih =>
    cases T with
    | nil=>exact False.elim (by simpa using (h s).mp (List.mem_cons_self ..))
    | cons t ts =>
      rw [List.pairwise_cons] at hS hT
      have hs : s ∈ t :: ts:=(h s).mp (List.mem_cons_self ..)
      have ht : t ∈ s :: ss:=(h t).mpr (List.mem_cons_self ..)
      have hst : s=t:=by
        rcases List.mem_cons.mp hs with rfl | h1
        · rfl
        · rcases List.mem_cons.mp ht with rfl | h2
          · rfl
          · have:=hT.1 s h1;have:=hS.1 t h2;omega
      subst hst
      congr 1
      apply ih hS.2 hT.2
      intro x
      constructor
      · intro hx
        have hx':=(h x).mp (List.mem_cons_of_mem s hx)
        rcases List.mem_cons.mp hx' with rfl | hts
        · exact False.elim (lt_irrefl x (hS.1 x hx))
        · exact hts
      · intro hx
        have hx':=(h x).mpr (List.mem_cons_of_mem s hx)
        rcases List.mem_cons.mp hx' with rfl | hss
        · exact False.elim (lt_irrefl x (hT.1 x hx))
        · exact hss
lemma mAOW (S : List ℕ) (o y : ℕ) :
    y ∈ aOW S o ↔ y ∈ S ∨ y=o ∨ ∃ a ∈ S,y=wAnd a o:=by
  unfold aOW
  have h : ∀ (l acc : List ℕ),
      y ∈ l.foldl (fun a x=>iSr (wAnd x o) a) acc ↔ y ∈ acc ∨ ∃ a ∈ l,y=wAnd a o:=by
    intro l
    induction l with
    | nil=>intro acc;simp
    | cons x xs ih =>
      intro acc
      simp only [List.foldl_cons,ih,mem_insertSorted,List.mem_cons]
      constructor
      · rintro ((rfl | hacc) | ⟨a,ha,rfl⟩)
        · exact Or.inr ⟨x,Or.inl rfl,rfl⟩
        · exact Or.inl hacc
        · exact Or.inr ⟨a,Or.inr ha,rfl⟩
      · rintro (hacc | ⟨a,rfl | hxs,rfl⟩)
        · exact Or.inl (Or.inr hacc)
        · exact Or.inl (Or.inl rfl)
        · exact Or.inr ⟨a,hxs,rfl⟩
  rw [h S (iSr o S),mem_insertSorted]
  tauto
lemma pwAOW {S : List ℕ} (hS : S.Pairwise (· < ·)) (o : ℕ) :
    (aOW S o).Pairwise (· < ·):=by
  unfold aOW
  have h : ∀ (l acc : List ℕ),acc.Pairwise (· < ·) →
      (l.foldl (fun a x=>iSr (wAnd x o) a) acc).Pairwise (· < ·):=by
    intro l
    induction l with
    | nil=>intro acc ha;exact ha
    | cons x xs ih=>intro acc ha;exact ih _ (pairwise_insertSorted _ acc ha)
  exact h S (iSr o S) (pairwise_insertSorted o S hS)
def ACl (S : List ℕ) : Prop:=∀ a ∈ S,∀ b ∈ S,wAnd a b ∈ S
lemma acAOW {S : List ℕ} (hC : ACl S) (o : ℕ) : ACl (aOW S o):=by
  intro x hx y hy
  rw [mAOW] at hx hy ⊢
  rcases hx with hxS | rfl | ⟨a,ha,rfl⟩
  · rcases hy with hyS | rfl | ⟨b,hb,rfl⟩
    · exact Or.inl (hC x hxS y hyS)
    · exact Or.inr (Or.inr ⟨x,hxS,rfl⟩)
    · exact Or.inr (Or.inr ⟨wAnd x b,hC x hxS b hb,by unfold wAnd;rw [baa]⟩)
  · rcases hy with hyS | rfl | ⟨b,hb,rfl⟩
    · exact Or.inr (Or.inr ⟨y,hyS,by unfold wAnd;exact bac x y⟩)
    · exact Or.inr (Or.inl (by unfold wAnd;exact bas _))
    · exact Or.inr (Or.inr ⟨b,hb,by unfold wAnd;rw [bac x (b&&&x),baa,bas]⟩)
  · rcases hy with hyS | rfl | ⟨b,hb,rfl⟩
    · exact Or.inr (Or.inr ⟨wAnd a y,hC a ha y hyS,by unfold wAnd;rw [baa,bac o y,← baa]⟩)
    · exact Or.inr (Or.inr ⟨a,ha,by unfold wAnd;rw [baa,bas]⟩)
    · exact Or.inr (Or.inr ⟨wAnd a b,hC a ha b hb,by
        unfold wAnd
        rw [baa,← baa o b o,bac o b,baa b o o,bas,← baa]⟩)
lemma addOrW_of_mem {S : List ℕ} (hS : S.Pairwise (· < ·)) (hC : ACl S) {o : ℕ} (ho : o ∈ S) :
    aOW S o=S:=by
  apply sorted_eq_of_mem_iff (pwAOW hS o) hS
  intro y
  rw [mAOW]
  constructor
  · rintro (hy | rfl | ⟨a,ha,rfl⟩)
    · exact hy
    · exact ho
    · exact hC a ha o ho
  · exact Or.inl
lemma allPairsOk_spec {S : List ℕ} {f : ℕ → Bool} (h : aPO S f=true)
    {a b : ℕ} (ha : a ∈ S) (hb : b ∈ S) (hne : a ≠ b) : f (wOr a b)=true:=by
  unfold aPO at h
  induction S with
  | nil=>simp at ha
  | cons x xs ih =>
    simp only [aPO.go,Bool.and_eq_true,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | hax
    · rcases List.mem_cons.mp hb with rfl | hbx
      · exact (hne rfl).elim
      · exact h.1 b hbx
    · rcases List.mem_cons.mp hb with rfl | hbx
      · have:=h.1 a hax
        simpa only [wOr,boc] using this
      · exact ih h.2 hax hbx
lemma memBucket_spec {Ss : List (List ℕ)} {S : List ℕ} (h : mBk (mkB Ss) S=true) :
    S ∈ Ss:=by
  unfold mBk mkB at h
  have hlt : hashS S < 32:=Nat.mod_lt _ (by omega)
  have hget : ((List.range 32).map (fun b=>Ss.filter (fun T=>hashS T==b))).getD (hashS S) [] =
      Ss.filter (fun T=>hashS T==hashS S):=by
    rw [List.getD_eq_getElem _ _ (by simp;exact hlt)]
    simp [List.getElem_range]
  rw [hget,List.any_eq_true] at h
  obtain ⟨T,hT,hTeq⟩:=h
  rw [beq_iff_eq] at hTeq
  rw [← hTeq]
  exact (List.mem_filter.mp hT).1
def fAI (P : ℕ → Bool) (f : ℕ → ℕ) (S : List ℕ) : ℕ :=
  S.foldl (fun acc w=>if P w then acc&&&f w else acc) 31
lemma testBit_foldAndIf (P : ℕ → Bool) (f : ℕ → ℕ) (S : List ℕ) (k : ℕ) :
    (fAI P f S).testBit k=(decide (k < 5)&&S.all (fun w=>!P w||(f w).testBit k)):=by
  unfold fAI
  have h : ∀ (l : List ℕ) (acc : ℕ),
      (l.foldl (fun a w=>if P w then a&&&f w else a) acc).testBit k =
      (acc.testBit k&&l.all (fun w=>!P w||(f w).testBit k)):=by
    intro l
    induction l with
    | nil=>intro acc;simp
    | cons w ws ih =>
      intro acc
      simp only [List.foldl_cons,ih,List.all_cons]
      cases hP : P w<;>simp [Nat.testBit_and,Bool.and_assoc]
  rw [h S 31]
  congr 1
  by_cases hk : k < 5
  · have : ∀ j : Fin 5,(31 : ℕ).testBit j.val=true:=by decide
    simp [hk,this ⟨k,hk⟩]
  · simp only [hk,decide_false]
    exact Nat.testBit_lt_two_pow (by have : 2 ^ 5 ≤ 2 ^ k:=Nat.pow_le_pow_right (by omega) (by omega);omega)
lemma fAIt (P : ℕ → Bool) (f : ℕ → ℕ) (S : List ℕ) : fAI P f S < 32:=by
  have h : ∀ (l : List ℕ) (acc : ℕ),acc < 32 →
      l.foldl (fun a w=>if P w then a&&&f w else a) acc < 32:=by
    intro l
    induction l with
    | nil=>intro acc ha;exact ha
    | cons w ws ih =>
      intro acc ha
      simp only [List.foldl_cons]
      split_ifs
      · apply ih
        have hle : (acc&&&f w) ≤ acc:=Nat.and_le_left
        omega
      · exact ih acc ha
  exact h S 31 (by omega)
lemma fAIl (P : ℕ → Bool) (f : ℕ → ℕ) {S : List ℕ} {w : ℕ}
    (hw : w ∈ S) (hP : P w=true) : (fAI P f S&&&f w)=fAI P f S:=by
  apply Nat.eq_of_testBit_eq;intro k
  simp only [Nat.testBit_and,testBit_foldAndIf]
  by_cases hk : k < 5
  · simp only [hk,decide_true,Bool.true_and]
    cases hall : S.all (fun u=>!P u||(f u).testBit k)
    · simp
    · have hu:=List.all_eq_true.mp hall w hw
      simp [hP] at hu
      simp [hu]
  · simp [hk]
lemma fAIs (P : ℕ → Bool) (f : ℕ → ℕ) {S : List ℕ} {m : ℕ} (hm : m < 32)
    (h : ∀ w ∈ S,P w=true → (f w&&&m)=m) : (fAI P f S&&&m)=m:=by
  apply Nat.eq_of_testBit_eq;intro k
  simp only [Nat.testBit_and,testBit_foldAndIf]
  cases hmk : m.testBit k
  · simp
  · have hk5 : k < 5:=by
      by_contra hge
      have h0 : m.testBit k=false :=
        Nat.testBit_lt_two_pow (by have : 2 ^ 5 ≤ 2 ^ k:=Nat.pow_le_pow_right (by omega) (by omega);omega)
      rw [h0] at hmk;cases hmk
    simp only [hk5,decide_true,Bool.true_and,Bool.and_true,List.all_eq_true,Bool.or_eq_true]
    intro w hw
    cases hP : P w
    · left;rfl
    · right
      have hfm:=congrArg (fun n=>n.testBit k) (h w hw hP)
      simp only [Nat.testBit_and,hmk,Bool.and_true] at hfm
      exact hfm
lemma fAIw (P : ℕ → Bool) (f : ℕ → ℕ) {S : List ℕ}
    (hlt : ∀ w ∈ S,f w < 32) (hC : ACl S)
    (hPand : ∀ a b,P a=true → P b=true → P (wAnd a b)=true)
    (hfand : ∀ a b,f (wAnd a b)=(f a&&&f b))
    (hex : ∃ w ∈ S,P w=true) :
    ∃ w ∈ S,P w=true ∧ f w=fAI P f S:=by
  have hsub : ∀ l : List ℕ,(∀ x ∈ l,x ∈ S) →
      (∃ w ∈ l,P w=true) →
      ∃ w ∈ S,P w=true ∧ f w=fAI P f l:=by
    intro l
    induction l with
    | nil=>intro _ ⟨w,hw,_⟩;simp at hw
    | cons a t ih =>
      intro hsub ⟨w0,hw0,hP0⟩
      have haS : a ∈ S:=hsub a (List.mem_cons_self ..)
      have htS : ∀ x ∈ t,x ∈ S:=fun x hx=>hsub x (List.mem_cons_of_mem a hx)
      by_cases hexT : ∃ u ∈ t,P u=true
      · obtain ⟨u,huS,hPu,hfu⟩:=ih htS hexT
        cases hPa : P a
        · refine ⟨u,huS,hPu,?_⟩
          apply Nat.eq_of_testBit_eq;intro k
          rw [hfu,testBit_foldAndIf,testBit_foldAndIf]
          simp [hPa]
        · refine ⟨wAnd a u,hC a haS u huS,hPand a u hPa hPu,?_⟩
          apply Nat.eq_of_testBit_eq;intro k
          rw [hfand,Nat.testBit_and,hfu,testBit_foldAndIf,testBit_foldAndIf]
          have hfa32 : f a < 32:=hlt a haS
          by_cases hk : k < 5
          · simp [hk,hPa,Bool.and_comm]
          · have h0 : (f a).testBit k=false :=
              Nat.testBit_lt_two_pow (by have : 2 ^ 5 ≤ 2 ^ k:=Nat.pow_le_pow_right (by omega) (by omega);omega)
            simp [hk,h0]
      · rcases List.mem_cons.mp hw0 with rfl | hwt
        · refine ⟨w0,haS,hP0,?_⟩
          apply Nat.eq_of_testBit_eq;intro k
          rw [testBit_foldAndIf]
          have hfa32 : f w0 < 32:=hlt w0 haS
          have hallT : t.all (fun x=>!P x||(f x).testBit k)=true:=by
            rw [List.all_eq_true];intro x hx
            cases hPx : P x
            · simp
            · exact (hexT ⟨x,hx,hPx⟩).elim
          by_cases hk : k < 5
          · simp [hk,hP0,hallT,Bool.true_and,Bool.and_true]
          · have h0 : (f w0).testBit k=false :=
              Nat.testBit_lt_two_pow (by have : 2 ^ 5 ≤ 2 ^ k:=Nat.pow_le_pow_right (by omega) (by omega);omega)
            simp [hk,h0]
        · exact (hexT ⟨w0,hwt,hP0⟩).elim
  exact hsub S (fun _ h=>h) hex
lemma fAIa (P : ℕ → Bool) (f : ℕ → ℕ) (S : List ℕ) (o : ℕ)
    (hPand : ∀ a b,P (wAnd a b)=(P a&&P b))
    (hfand : ∀ a b,f (wAnd a b)=(f a&&&f b)) :
    fAI P f (aOW S o)=if P o then fAI P f S&&&f o else fAI P f S:=by
  apply Nat.eq_of_testBit_eq;intro k
  by_cases hk : k < 5
  · cases hPo : P o
    · simp only [Bool.false_eq_true,↓reduceIte,testBit_foldAndIf,hk,decide_true,Bool.true_and]
      apply Bool.eq_iff_iff.mpr
      simp only [List.all_eq_true,Bool.or_eq_true,Bool.not_eq_true',mAOW]
      constructor
      · intro h w hw;exact h w (Or.inl hw)
      · intro h w hw
        rcases hw with hwS | rfl | ⟨a,ha,rfl⟩
        · exact h w hwS
        · exact Or.inl hPo
        · exact Or.inl (by rw [hPand,hPo,Bool.and_false])
    · simp only [↓reduceIte,Nat.testBit_and,testBit_foldAndIf,hk,decide_true,Bool.true_and]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true,List.all_eq_true,Bool.or_eq_true,Bool.not_eq_true',mAOW]
      constructor
      · intro h
        refine ⟨fun w hw=>h w (Or.inl hw),?_⟩
        rcases h o (Or.inr (Or.inl rfl)) with h0 | h1
        · rw [hPo] at h0;cases h0
        · exact h1
      · rintro ⟨hS,ho⟩ w hw
        rcases hw with hwS | rfl | ⟨a,ha,rfl⟩
        · exact hS w hwS
        · exact Or.inr ho
        · rw [hPand,hPo,Bool.and_true,hfand,Nat.testBit_and]
          rcases hS a ha with hPa | hfa
          · exact Or.inl hPa
          · exact Or.inr (by simp [hfa,ho])
  · have h0 : (fAI P f (aOW S o)).testBit k=false:=by rw [testBit_foldAndIf];simp [hk]
    have h1 : (fAI P f S).testBit k=false:=by rw [testBit_foldAndIf];simp [hk]
    rw [h0]
    split_ifs
    · rw [Nat.testBit_and,h1,Bool.false_and]
    · exact h1.symm
lemma or_lt16384 {a b : ℕ} (ha : a < 16384) (hb : b < 16384) : (a|||b) < 16384 :=
  show (a|||b) < 2 ^ 14 from Nat.or_lt_two_pow (by omega) (by omega)
lemma or_lt32768 {a b : ℕ} (ha : a < 32768) (hb : b < 32768) : (a|||b) < 32768 :=
  show (a|||b) < 2 ^ 15 from Nat.or_lt_two_pow (by omega) (by omega)
lemma l0_15_lt {w : ℕ} (hw : w < 32768) : l0_15 w < 32:=by
  unfold l0_15;rw [Nat.shiftRight_eq_div_pow];omega
lemma l1_15_lt (w : ℕ) : l1_15 w < 32:=by
  unfold l1_15;have : ((w>>>5)&&&31) ≤ 31:=Nat.and_le_right;omega
lemma l0_15_and (a b : ℕ) : l0_15 (wAnd a b)=(l0_15 a&&&l0_15 b):=by
  apply Nat.eq_of_testBit_eq;intro k;simp [l0_15,wAnd,Nat.testBit_shiftRight,Nat.testBit_and]
lemma l1_15_and (a b : ℕ) : l1_15 (wAnd a b)=(l1_15 a&&&l1_15 b):=by
  apply Nat.eq_of_testBit_eq;intro k
  simp [l1_15,wAnd,Nat.testBit_shiftRight,Nat.testBit_and]
  cases (a.testBit (5 + k))<;>cases (b.testBit (5 + k))<;>cases ((31 : ℕ).testBit k)<;>rfl
lemma l0_15_or (a b : ℕ) : l0_15 (wOr a b)=(l0_15 a|||l0_15 b):=by
  apply Nat.eq_of_testBit_eq;intro k;simp [l0_15,wOr,Nat.testBit_shiftRight,Nat.testBit_or]
lemma l1_15_or (a b : ℕ) : l1_15 (wOr a b)=(l1_15 a|||l1_15 b):=by
  apply Nat.eq_of_testBit_eq;intro k
  simp [l1_15,wOr,Nat.testBit_shiftRight,Nat.testBit_and,Nat.testBit_or]
  cases (a.testBit (5 + k))<;>cases (b.testBit (5 + k))<;>cases ((31 : ℕ).testBit k)<;>rfl
def V15 (w : ℕ) : Prop:=w < 32768 ∧ (l0_15 w&&&l1_15 w)=l0_15 w
lemma v15a {a b : ℕ} (ha : V15 a) (hb : V15 b) : V15 (wAnd a b):=by
  refine ⟨by have:=ha.1;have : wAnd a b ≤ a:=Nat.and_le_left;omega,?_⟩
  rw [l0_15_and,l1_15_and]
  apply Nat.eq_of_testBit_eq;intro k
  have h1:=congrArg (fun n=>n.testBit k) ha.2
  have h2:=congrArg (fun n=>n.testBit k) hb.2
  simp only [Nat.testBit_and] at h1 h2 ⊢
  cases ha0 : (l0_15 a).testBit k<;>cases hb0 : (l0_15 b).testBit k <;>
  cases ha1 : (l1_15 a).testBit k<;>cases hb1 : (l1_15 b).testBit k<;>simp_all
lemma v15o {a b : ℕ} (ha : V15 a) (hb : V15 b) : V15 (wOr a b):=by
  refine ⟨or_lt32768 ha.1 hb.1,?_⟩
  rw [l0_15_or,l1_15_or]
  apply Nat.eq_of_testBit_eq;intro k
  have h1:=congrArg (fun n=>n.testBit k) ha.2
  have h2:=congrArg (fun n=>n.testBit k) hb.2
  simp only [Nat.testBit_and,Nat.testBit_or] at h1 h2 ⊢
  cases ha0 : (l0_15 a).testBit k<;>cases hb0 : (l0_15 b).testBit k <;>
  cases ha1 : (l1_15 a).testBit k<;>cases hb1 : (l1_15 b).testBit k<;>simp_all
lemma stats15_eq (S : List ℕ) :
    st15 S =
      (fAI (fun w=>(l0_15 w&&&18)==18) l0_15 S,
       fAI (fun w=>(l0_15 w&&&12)==12) l0_15 S,
       fAI (fun w=>(l1_15 w&&&20)==20) l1_15 S,
       S.any (fun w=>(l0_15 w&&&18)==18),
       S.any (fun w=>(l0_15 w&&&12)==12),
       S.any (fun w=>(l1_15 w&&&20)==20&&(l1_15 w != 31))):=by
  unfold st15 fAI
  have h : ∀ (l : List ℕ) (i18 i12 i20 : ℕ) (s6 s7 s3 : Bool),
      l.foldl uS15 (i18,i12,i20,s6,s7,s3) =
      (l.foldl (fun acc w=>if (l0_15 w&&&18)==18 then acc&&&l0_15 w else acc) i18,
       l.foldl (fun acc w=>if (l0_15 w&&&12)==12 then acc&&&l0_15 w else acc) i12,
       l.foldl (fun acc w=>if (l1_15 w&&&20)==20 then acc&&&l1_15 w else acc) i20,
       s6||l.any (fun w=>(l0_15 w&&&18)==18),
       s7||l.any (fun w=>(l0_15 w&&&12)==12),
       s3||l.any (fun w=>(l1_15 w&&&20)==20&&(l1_15 w != 31))):=by
    intro l
    induction l with
    | nil=>intro i18 i12 i20 s6 s7 s3;simp
    | cons w ws ih =>
      intro i18 i12 i20 s6 s7 s3
      simp only [List.foldl_cons,List.any_cons,uS15]
      rw [ih]
      congr 1;· split_ifs<;>rfl
      congr 1;· split_ifs<;>rfl
      congr 1;· split_ifs<;>rfl
      congr 1;· cases ((l0_15 w&&&18)==18)<;>cases s6<;>simp
      congr 1;· cases ((l0_15 w&&&12)==12)<;>cases s7<;>simp
      · cases ((l1_15 w&&&20)==20)<;>cases (l1_15 w != 31)<;>cases s3<;>simp
  simpa using h S 31 31 31 false false false
lemma fin32_and_eq_m :
    (∀ a b : Fin 32,((a.val&&&b.val)&&&18=18) ↔ (a.val&&&18=18 ∧ b.val&&&18=18)) ∧
    (∀ a b : Fin 32,((a.val&&&b.val)&&&12=12) ↔ (a.val&&&12=12 ∧ b.val&&&12=12)) ∧
    (∀ a b : Fin 32,((a.val&&&b.val)&&&20=20) ↔ (a.val&&&20=20 ∧ b.val&&&20=20)):=by
  decide
lemma bit_mono_zero {o0 o1 f : ℕ} (hle : (o0&&&o1)=o0) (hf : (o1&&&f)=0) : (o0&&&f)=0:=by
  apply Nat.eq_of_testBit_eq;intro k
  have h1:=congrArg (fun n=>n.testBit k) hle
  have h2:=congrArg (fun n=>n.testBit k) hf
  simp only [Nat.testBit_and,Nat.zero_testBit] at h1 h2 ⊢
  cases ha : o0.testBit k<;>cases hb : o1.testBit k<;>cases hc : f.testBit k<;>simp_all
lemma f32s1F :
    (∀ i18 o0 : Fin 32,(i18.val&&&18=18) → (o0.val&&&18=18) →
      (o0.val=18 ∨ (i18.val&&&o0.val)=18) → (o0.val&&&(i18.val&&&(31^^^18)))=0) ∧
    (∀ i12 o0 : Fin 32,(i12.val&&&12=12) → (o0.val&&&12=12) →
      (o0.val=12 ∨ (i12.val&&&o0.val)=12) → (o0.val&&&(i12.val&&&(31^^^12)))=0) ∧
    (∀ i20 o1 : Fin 32,(i20.val&&&20=20) → (o1.val&&&20=20) →
      (o1.val=20 ∨ (i20.val&&&o1.val)=20) → (o1.val&&&(i20.val&&&(31^^^20)))=0):=by
  decide
lemma bit_step1_mono {x y o m : ℕ} (hle : (x&&&y)=x) (hyo : (y&&&o)=m) (hxm : (x&&&m)=m) :
    (x&&&o)=m:=by
  apply Nat.eq_of_testBit_eq;intro k
  have h1:=congrArg (fun n=>n.testBit k) hle
  have h2:=congrArg (fun n=>n.testBit k) hyo
  have h3:=congrArg (fun n=>n.testBit k) hxm
  simp only [Nat.testBit_and] at h1 h2 h3 ⊢
  cases hx : x.testBit k<;>cases hy : y.testBit k<;>cases ho : o.testBit k<;>cases hm : m.testBit k<;>simp_all
lemma bit_step1_mono0 {x y o : ℕ} (hle : (x&&&y)=x) (hyo : (y&&&o)=0) : (x&&&o)=0 :=
  bit_mono_zero hle hyo
lemma f32s2A :
    (∀ a b : Fin 32,(a.val&&&b.val=18 → a.val ≠ 12 ∧ b.val ≠ 12) ∧
                     (a.val&&&b.val=12 → a.val ≠ 18 ∧ b.val ≠ 18)) ∧
    (∀ a b : Fin 32,(a.val&&&b.val=20) → (a.val&&&20=20) ∧ (a.val=31 → b.val=20)) ∧
    (∀ a : Fin 32,a.val=18 ∨ a.val=12 → (a.val&&&20) ≠ a.val) ∧
    (∀ a b : Fin 32,(a.val&&&b.val=18 → a.val&&&18=18 ∧ b.val&&&18=18) ∧
                     (a.val&&&b.val=12 → a.val&&&12=12 ∧ b.val&&&12=12)):=by
  decide
lemma bit_req_forb {req0 forb0 forb1 o0 : ℕ}
    (hreq : (o0&&&req0)=req0)
    (hf0 : (o0&&&forb0)=0)
    (hf1 : (o0&&&forb1)=0) :
    (req0&&&(forb0|||forb1))=0:=by
  apply Nat.eq_of_testBit_eq;intro k
  have h1:=congrArg (fun n=>n.testBit k) hreq
  have h2:=congrArg (fun n=>n.testBit k) hf0
  have h3:=congrArg (fun n=>n.testBit k) hf1
  simp only [Nat.testBit_and,Nat.testBit_or,Nat.zero_testBit] at h1 h2 h3 ⊢
  cases hr : req0.testBit k<;>cases hfa : forb0.testBit k<;>cases hfb : forb1.testBit k<;>cases ho : o0.testBit k<;>simp_all
def Reach15 : ℕ → List ℕ → List ℕ → Prop
  | 0,S,T=>S=T ∧ lb15B (st15 T)=0
  | k + 1,S,T=>Reach15 k S T ∨ ∃ a ∈ S,∃ b ∈ S,Reach15 k (aOW S (wOr a b)) T
lemma s15G {S : List ℕ} (hV : ∀ w ∈ S,V15 w) (hC : ACl S) :
    lb15B (st15 S)=0 ↔
      (∃ w ∈ S,l0_15 w=18) ∧ (∃ w ∈ S,l0_15 w=12) ∧ (∃ w ∈ S,l1_15 w=20):=by
  rw [stats15_eq]
  set i18:=fAI (fun w=>(l0_15 w&&&18)==18) l0_15 S
  set i12:=fAI (fun w=>(l0_15 w&&&12)==12) l0_15 S
  set i20:=fAI (fun w=>(l1_15 w&&&20)==20) l1_15 S
  set s6:=S.any (fun w=>(l0_15 w&&&18)==18)
  set s7:=S.any (fun w=>(l0_15 w&&&12)==12)
  set s3:=S.any (fun w=>(l1_15 w&&&20)==20&&(l1_15 w != 31))
  have hbase0 : lb15B (i18,i12,i20,s6,s7,s3)=0 ↔
      (s6=true ∧ i18=18) ∧ (s7=true ∧ i12=12) ∧ (s3=true ∧ i20=20):=by
    unfold lb15B;dsimp only
    by_cases h1 : (s6&&(i18==18)&&(s7&&(i12==12))&&(s3&&(i20==20)))=true
    · rw [if_pos h1];simp only [Bool.and_eq_true,beq_iff_eq] at h1;tauto
    · rw [if_neg h1]
      have hne0 : ∀ c : Bool,(if c=true then (2 : ℕ) else 1) ≠ 0:=fun c=>by cases c<;>decide
      exact ⟨fun h=>(hne0 _ h).elim,fun ⟨⟨a1,a2⟩,⟨b1,b2⟩,⟨c1,c2⟩⟩ =>
        (h1 (by simp [a1,a2,b1,b2,c1,c2])).elim⟩
  rw [hbase0]
  have heq6 : (s6=true ∧ i18=18) ↔ ∃ w ∈ S,l0_15 w=18:=by
    constructor
    · rintro ⟨hs6,hi⟩
      rw [List.any_eq_true] at hs6
      obtain ⟨w,hw,_,hfw⟩:=fAIw (fun w=>(l0_15 w&&&18)==18) l0_15
        (fun w hw=>l0_15_lt (hV w hw).1) hC
        (fun a b ha hb=>by
          simp only [beq_iff_eq] at ha hb ⊢;rw [l0_15_and]
          apply Nat.eq_of_testBit_eq;intro k
          have h1:=congrArg (fun n=>n.testBit k) ha
          have h2:=congrArg (fun n=>n.testBit k) hb
          simp only [Nat.testBit_and] at h1 h2 ⊢
          cases hta : (l0_15 a).testBit k<;>cases htb : (l0_15 b).testBit k<;>cases htm : (18 : ℕ).testBit k<;>simp_all)
        l0_15_and hs6
      exact ⟨w,hw,hfw.trans hi⟩
    · rintro ⟨w,hw,hw18⟩
      have hPw : ((l0_15 w&&&18)==18)=true:=by rw [hw18];decide
      refine ⟨List.any_eq_true.mpr ⟨w,hw,hPw⟩,?_⟩
      have hle:=fAIl (fun u=>(l0_15 u&&&18)==18) l0_15 hw hPw
      have hsup:=fAIs (S:=S) (fun u=>(l0_15 u&&&18)==18) l0_15 (m:=18) (by omega)
        (fun u _ hu=>beq_iff_eq.mp hu)
      rw [hw18] at hle
      exact hle.symm.trans hsup
  have heq7 : (s7=true ∧ i12=12) ↔ ∃ w ∈ S,l0_15 w=12:=by
    constructor
    · rintro ⟨hs7,hi⟩
      rw [List.any_eq_true] at hs7
      obtain ⟨w,hw,_,hfw⟩:=fAIw (fun w=>(l0_15 w&&&12)==12) l0_15
        (fun w hw=>l0_15_lt (hV w hw).1) hC
        (fun a b ha hb=>by
          simp only [beq_iff_eq] at ha hb ⊢;rw [l0_15_and]
          apply Nat.eq_of_testBit_eq;intro k
          have h1:=congrArg (fun n=>n.testBit k) ha
          have h2:=congrArg (fun n=>n.testBit k) hb
          simp only [Nat.testBit_and] at h1 h2 ⊢
          cases hta : (l0_15 a).testBit k<;>cases htb : (l0_15 b).testBit k<;>cases htm : (12 : ℕ).testBit k<;>simp_all)
        l0_15_and hs7
      exact ⟨w,hw,hfw.trans hi⟩
    · rintro ⟨w,hw,hw12⟩
      have hPw : ((l0_15 w&&&12)==12)=true:=by rw [hw12];decide
      refine ⟨List.any_eq_true.mpr ⟨w,hw,hPw⟩,?_⟩
      have hle:=fAIl (fun u=>(l0_15 u&&&12)==12) l0_15 hw hPw
      have hsup:=fAIs (S:=S) (fun u=>(l0_15 u&&&12)==12) l0_15 (m:=12) (by omega)
        (fun u _ hu=>beq_iff_eq.mp hu)
      rw [hw12] at hle
      exact hle.symm.trans hsup
  have heq3 : (s3=true ∧ i20=20) ↔ ∃ w ∈ S,l1_15 w=20:=by
    constructor
    · rintro ⟨hs3,hi⟩
      rw [List.any_eq_true] at hs3
      obtain ⟨w0,hw0,hP0⟩:=hs3
      have hP0' : ((l1_15 w0&&&20)==20)=true:=(Bool.and_eq_true .. |>.mp hP0).1
      obtain ⟨w,hw,_,hfw⟩:=fAIw (fun w=>(l1_15 w&&&20)==20) l1_15
        (fun w _=>l1_15_lt w) hC
        (fun a b ha hb=>by
          simp only [beq_iff_eq] at ha hb ⊢;rw [l1_15_and]
          apply Nat.eq_of_testBit_eq;intro k
          have h1:=congrArg (fun n=>n.testBit k) ha
          have h2:=congrArg (fun n=>n.testBit k) hb
          simp only [Nat.testBit_and] at h1 h2 ⊢
          cases hta : (l1_15 a).testBit k<;>cases htb : (l1_15 b).testBit k<;>cases htm : (20 : ℕ).testBit k<;>simp_all)
        l1_15_and ⟨w0,hw0,hP0'⟩
      exact ⟨w,hw,hfw.trans hi⟩
    · rintro ⟨w,hw,hw20⟩
      have hPw : ((l1_15 w&&&20)==20)=true:=by rw [hw20];decide
      refine ⟨List.any_eq_true.mpr ⟨w,hw,by rw [hw20];decide⟩,?_⟩
      have hle:=fAIl (fun u=>(l1_15 u&&&20)==20) l1_15 hw hPw
      have hsup:=fAIs (S:=S) (fun u=>(l1_15 u&&&20)==20) l1_15 (m:=20) (by omega)
        (fun u _ hu=>beq_iff_eq.mp hu)
      rw [hw20] at hle
      exact hle.symm.trans hsup
  rw [heq6,heq7,heq3]
lemma lb15_le_3 (S : List ℕ) : lb15 S ≤ 3:=by
  unfold lb15 lb15B
  dsimp only
  split_ifs<;>omega
lemma s1_15 {S : List ℕ} (hV : ∀ w ∈ S,V15 w) (hC : ACl S)
    {a b : ℕ} (ha : a ∈ S) (hb : b ∈ S)
    (hG : lb15B (st15 (aOW S (wOr a b)))=0) :
    lb15 S ≤ 1:=by
  set o:=wOr a b
  have hoV : V15 o:=v15o (hV a ha) (hV b hb)
  have hV' : ∀ w ∈ aOW S o,V15 w:=by
    intro w hw;rw [mAOW] at hw
    rcases hw with hwS | rfl | ⟨x,hx,rfl⟩
    · exact hV w hwS
    · exact hoV
    · exact v15a (hV x hx) hoV
  have hC' : ACl (aOW S o):=acAOW hC o
  obtain ⟨⟨w6,hw6,h6w⟩,⟨w7,hw7,h7w⟩,⟨w3,hw3,h3w⟩⟩:=(s15G hV' hC').mp hG
  unfold lb15
  rw [stats15_eq]
  set i18:=fAI (fun w=>(l0_15 w&&&18)==18) l0_15 S
  set i12:=fAI (fun w=>(l0_15 w&&&12)==12) l0_15 S
  set i20:=fAI (fun w=>(l1_15 w&&&20)==20) l1_15 S
  set s6:=S.any (fun w=>(l0_15 w&&&18)==18)
  set s7:=S.any (fun w=>(l0_15 w&&&12)==12)
  set s3:=S.any (fun w=>(l1_15 w&&&20)==20&&(l1_15 w != 31))
  have hi18_lt : i18 < 32:=fAIt ..
  have hi12_lt : i12 < 32:=fAIt ..
  have hi20_lt : i20 < 32:=fAIt ..
  have ho0_lt : l0_15 o < 32:=l0_15_lt hoV.1
  have ho1_lt : l1_15 o < 32:=l1_15_lt o
  have hi18_sup : (i18&&&18)=18 :=
    fAIs _ _ (by omega) (fun u _ hu=>beq_iff_eq.mp hu)
  have hi12_sup : (i12&&&12)=12 :=
    fAIs _ _ (by omega) (fun u _ hu=>beq_iff_eq.mp hu)
  have hi20_sup : (i20&&&20)=20 :=
    fAIs _ _ (by omega) (fun u _ hu=>beq_iff_eq.mp hu)
  have h18_info : ¬ (s6=true ∧ i18=18) →
      (l0_15 o&&&18)=18 ∧ (l0_15 o&&&(i18&&&(31^^^18)))=0 ∧ (s6=false → l0_15 o=18):=by
    intro hnh6
    have hw6_notS : w6 ∉ S:=by
      intro hm;apply hnh6
      have hPw : ((l0_15 w6&&&18)==18)=true:=by rw [h6w];decide
      refine ⟨List.any_eq_true.mpr ⟨w6,hm,hPw⟩,?_⟩
      have hle:=fAIl (fun u=>(l0_15 u&&&18)==18) l0_15 hm hPw
      rw [h6w] at hle;exact hle.symm.trans hi18_sup
    rw [mAOW] at hw6
    rcases hw6 with hm | rfl | ⟨x,hx,rfl⟩
    · exact (hw6_notS hm).elim
    · refine ⟨by rw [h6w];decide,?_,fun _=>h6w⟩
      exact f32s1F.1 ⟨i18,hi18_lt⟩ ⟨l0_15 o,ho0_lt⟩ hi18_sup (show (l0_15 o&&&18)=18 by rw [h6w];decide) (Or.inl h6w)
    · rw [l0_15_and] at h6w
      have hx_lt : l0_15 x < 32:=l0_15_lt (hV x hx).1
      have ⟨hx18,ho18⟩:=f32s2A.2.2.2 ⟨l0_15 x,hx_lt⟩ ⟨l0_15 o,ho0_lt⟩ |>.1 h6w
      have hPx : ((l0_15 x&&&18)==18)=true:=beq_iff_eq.mpr hx18
      have hs6t : s6=true:=List.any_eq_true.mpr ⟨x,hx,hPx⟩
      have hle:=fAIl (fun u=>(l0_15 u&&&18)==18) l0_15 hx hPx
      have hmo:=bit_step1_mono hle h6w hi18_sup
      refine ⟨ho18,f32s1F.1 ⟨i18,hi18_lt⟩ ⟨l0_15 o,ho0_lt⟩ hi18_sup ho18 (Or.inr hmo),
        fun hf=>by rw [hs6t] at hf;cases hf⟩
  have h12_info : ¬ (s7=true ∧ i12=12) →
      (l0_15 o&&&12)=12 ∧ (l0_15 o&&&(i12&&&(31^^^12)))=0 ∧ (s7=false → l0_15 o=12):=by
    intro hnh7
    have hw7_notS : w7 ∉ S:=by
      intro hm;apply hnh7
      have hPw : ((l0_15 w7&&&12)==12)=true:=by rw [h7w];decide
      refine ⟨List.any_eq_true.mpr ⟨w7,hm,hPw⟩,?_⟩
      have hle:=fAIl (fun u=>(l0_15 u&&&12)==12) l0_15 hm hPw
      rw [h7w] at hle;exact hle.symm.trans hi12_sup
    rw [mAOW] at hw7
    rcases hw7 with hm | rfl | ⟨x,hx,rfl⟩
    · exact (hw7_notS hm).elim
    · refine ⟨by rw [h7w];decide,?_,fun _=>h7w⟩
      exact f32s1F.2.1 ⟨i12,hi12_lt⟩ ⟨l0_15 o,ho0_lt⟩ hi12_sup (show (l0_15 o&&&12)=12 by rw [h7w];decide) (Or.inl h7w)
    · rw [l0_15_and] at h7w
      have hx_lt : l0_15 x < 32:=l0_15_lt (hV x hx).1
      have ⟨hx12,ho12⟩:=f32s2A.2.2.2 ⟨l0_15 x,hx_lt⟩ ⟨l0_15 o,ho0_lt⟩ |>.2 h7w
      have hPx : ((l0_15 x&&&12)==12)=true:=beq_iff_eq.mpr hx12
      have hs7t : s7=true:=List.any_eq_true.mpr ⟨x,hx,hPx⟩
      have hle:=fAIl (fun u=>(l0_15 u&&&12)==12) l0_15 hx hPx
      have hmo:=bit_step1_mono hle h7w hi12_sup
      refine ⟨ho12,f32s1F.2.1 ⟨i12,hi12_lt⟩ ⟨l0_15 o,ho0_lt⟩ hi12_sup ho12 (Or.inr hmo),
        fun hf=>by rw [hs7t] at hf;cases hf⟩
  have h20_info : ¬ (s3=true ∧ i20=20) →
      (l0_15 o&&&(i20&&&(31^^^20)))=0:=by
    intro hnh3
    have hw3_notS : w3 ∉ S:=by
      intro hm;apply hnh3
      have hPw : ((l1_15 w3&&&20)==20)=true:=by rw [h3w];decide
      refine ⟨List.any_eq_true.mpr ⟨w3,hm,by rw [h3w];decide⟩,?_⟩
      have hle:=fAIl (fun u=>(l1_15 u&&&20)==20) l1_15 hm hPw
      rw [h3w] at hle;exact hle.symm.trans hi20_sup
    have hf1 : (l1_15 o&&&(i20&&&(31^^^20)))=0:=by
      rw [mAOW] at hw3
      rcases hw3 with hm | rfl | ⟨x,hx,rfl⟩
      · exact (hw3_notS hm).elim
      · exact f32s1F.2.2 ⟨i20,hi20_lt⟩ ⟨l1_15 o,ho1_lt⟩ hi20_sup (show (l1_15 o&&&20)=20 by rw [h3w];decide) (Or.inl h3w)
      · rw [l1_15_and] at h3w
        have hx_lt : l1_15 x < 32:=l1_15_lt x
        have hx20 : (l1_15 x&&&20)=20:=(f32s2A.2.1 ⟨l1_15 x,hx_lt⟩ ⟨l1_15 o,ho1_lt⟩ h3w).1
        have ho20 : (l1_15 o&&&20)=20:=(f32s2A.2.1 ⟨l1_15 o,ho1_lt⟩ ⟨l1_15 x,hx_lt⟩ (by rw [bac];exact h3w)).1
        have hPx : ((l1_15 x&&&20)==20)=true:=beq_iff_eq.mpr hx20
        have hle:=fAIl (fun u=>(l1_15 u&&&20)==20) l1_15 hx hPx
        have hmo:=bit_step1_mono hle h3w hi20_sup
        exact f32s1F.2.2 ⟨i20,hi20_lt⟩ ⟨l1_15 o,ho1_lt⟩ hi20_sup ho20 (Or.inr hmo)
    exact bit_mono_zero hoV.2 hf1
  set h6:=s6&&(i18==18)
  set h7:=s7&&(i12==12)
  set h3:=s3&&(i20==20)
  by_cases hall : h6&&h7&&h3
  · have hb0 : lb15B (i18,i12,i20,s6,s7,s3)=0:=by unfold lb15B;dsimp only;rw [if_pos hall]
    dsimp only;rw [hb0];simp
  · have hreq : (l0_15 o&&&((if !h6 then 18 else 0)|||(if !h7 then 12 else 0))) =
        ((if !h6 then 18 else 0)|||(if !h7 then 12 else 0)):=by
      rw [baodl]
      congr 1
      · cases hh6 : h6
        · simp only [Bool.not_false,↓reduceIte]
          exact (h18_info (fun ⟨a,b⟩=>by simp [h6,a,b] at hh6)).1
        · simp [ba0r]
      · cases hh7 : h7
        · simp only [Bool.not_false,↓reduceIte]
          exact (h12_info (fun ⟨a,b⟩=>by simp [h7,a,b] at hh7)).1
        · simp [ba0r]
    have hf0 : (l0_15 o&&&((if !h6 then i18&&&(31^^^18) else 0)|||(if !h7 then i12&&&(31^^^12) else 0)))=0:=by
      rw [baodl]
      have p1 : (l0_15 o&&&(if !h6 then i18&&&(31^^^18) else 0))=0:=by
        cases hh6 : h6
        · simp only [Bool.not_false,↓reduceIte]
          exact (h18_info (fun ⟨a,b⟩=>by simp [h6,a,b] at hh6)).2.1
        · simp [ba0r]
      have p2 : (l0_15 o&&&(if !h7 then i12&&&(31^^^12) else 0))=0:=by
        cases hh7 : h7
        · simp only [Bool.not_false,↓reduceIte]
          exact (h12_info (fun ⟨a,b⟩=>by simp [h7,a,b] at hh7)).2.1
        · simp [ba0r]
      rw [p1,p2,bo0l]
    have hf1 : (l0_15 o&&&(if !h3 then i20&&&(31^^^20) else 0))=0:=by
      cases hh3 : h3
      · simp only [Bool.not_false,↓reduceIte]
        exact h20_info (fun ⟨a,b⟩=>by simp [h3,a,b] at hh3)
      · simp [ba0r]
    have hdisj:=bit_req_forb hreq hf0 hf1
    have hb0 : lb15B (i18,i12,i20,s6,s7,s3)=1:=by
      unfold lb15B;dsimp only
      rw [if_neg hall]
      change (if (((if !h6 then 18 else 0)|||(if !h7 then 12 else 0)) &&&
          (((if !h6 then i18&&&(31^^^18) else 0)|||(if !h7 then i12&&&(31^^^12) else 0)) |||
           (if !h3 then i20&&&(31^^^20) else 0))) != 0 then 2 else 1)=1
      rw [hdisj];rfl
    have hnot_both_f : ¬ (s6=false ∧ s7=false):=by
      rintro ⟨hf6,hf7⟩
      have e18:=(h18_info (fun ⟨a,_⟩=>by rw [hf6] at a;cases a)).2.2 hf6
      have e12:=(h12_info (fun ⟨a,_⟩=>by rw [hf7] at a;cases a)).2.2 hf7
      omega
    dsimp only;rw [hb0]
    simp only [Nat.one_ne_zero,beq_iff_eq,↓reduceIte]
    split_ifs with hcond
    · exfalso;simp only [Bool.and_eq_true,Bool.not_eq_true'] at hcond
      exact hnot_both_f ⟨hcond.1.1.1,hcond.1.1.2⟩
    · exact le_rfl
lemma s2_15 {S : List ℕ} (hV : ∀ w ∈ S,V15 w) (hC : ACl S)
    {a b : ℕ} (ha : a ∈ S) (hb : b ∈ S)
    {c d : ℕ} (hc : c ∈ aOW S (wOr a b)) (hd : d ∈ aOW S (wOr a b))
    (hG : lb15B (st15 (aOW (aOW S (wOr a b)) (wOr c d)))=0) :
    lb15 S ≤ 2:=by
  set o1:=wOr a b
  set S1:=aOW S o1
  set o2:=wOr c d
  set S2:=aOW S1 o2
  have ho1V : V15 o1:=v15o (hV a ha) (hV b hb)
  have hV1 : ∀ w ∈ S1,V15 w:=by
    intro w hw;rw [mAOW] at hw
    rcases hw with hwS | rfl | ⟨x,hx,rfl⟩
    · exact hV w hwS
    · exact ho1V
    · exact v15a (hV x hx) ho1V
  have ho2V : V15 o2:=v15o (hV1 c hc) (hV1 d hd)
  have hV2 : ∀ w ∈ S2,V15 w:=by
    intro w hw;rw [mAOW] at hw
    rcases hw with hw1 | rfl | ⟨x,hx,rfl⟩
    · exact hV1 w hw1
    · exact ho2V
    · exact v15a (hV1 x hx) ho2V
  have hC2 : ACl S2:=acAOW (acAOW hC o1) o2
  obtain ⟨⟨w6,hw6,h6w⟩,⟨w7,hw7,h7w⟩,⟨w3,hw3,h3w⟩⟩:=(s15G hV2 hC2).mp hG
  unfold lb15
  rw [stats15_eq]
  set s6:=S.any (fun w=>(l0_15 w&&&18)==18)
  set s7:=S.any (fun w=>(l0_15 w&&&12)==12)
  set s3:=S.any (fun w=>(l1_15 w&&&20)==20&&(l1_15 w != 31))
  have hb0_le2 : lb15B (fAI (fun w=>(l0_15 w&&&18)==18) l0_15 S,
      fAI (fun w=>(l0_15 w&&&12)==12) l0_15 S,
      fAI (fun w=>(l1_15 w&&&20)==20) l1_15 S,s6,s7,s3) ≤ 2:=by
    unfold lb15B;dsimp only;split_ifs<;>omega
  dsimp only
  split_ifs with h0 hcond
  · omega
  · exfalso
    simp only [Bool.and_eq_true,Bool.not_eq_true'] at hcond
    obtain ⟨⟨⟨hf6,hf7⟩,hf3⟩,hncan⟩:=hcond
    have hno6 : ∀ x ∈ S,(l0_15 x&&&18) ≠ 18:=by
      intro x hx heq
      have : s6=true:=List.any_eq_true.mpr ⟨x,hx,beq_iff_eq.mpr heq⟩
      rw [hf6] at this;cases this
    have hno7 : ∀ x ∈ S,(l0_15 x&&&12) ≠ 12:=by
      intro x hx heq
      have : s7=true:=List.any_eq_true.mpr ⟨x,hx,beq_iff_eq.mpr heq⟩
      rw [hf7] at this;cases this
    have hno3 : ∀ x ∈ S,(l1_15 x&&&20)=20 → l1_15 x=31:=by
      intro x hx heq
      by_contra hne
      have : s3=true:=List.any_eq_true.mpr ⟨x,hx,by simp [heq,hne]⟩
      rw [hf3] at this;cases this
    have ho1_0_lt : l0_15 o1 < 32:=l0_15_lt ho1V.1
    have ho2_0_lt : l0_15 o2 < 32:=l0_15_lt ho2V.1
    have ho1_1_lt : l1_15 o1 < 32:=l1_15_lt o1
    have ho2_1_lt : l1_15 o2 < 32:=l1_15_lt o2
    have hcases_S2 : ∀ w ∈ S2,
        (w ∈ S) ∨ (w=o1) ∨ (∃ x ∈ S,w=wAnd x o1) ∨
        (w=o2) ∨ (∃ x ∈ S,w=wAnd x o2) ∨
        (w=wAnd o1 o2) ∨ (∃ x ∈ S,w=wAnd (wAnd x o1) o2):=by
      intro w hw
      rw [mAOW] at hw
      rcases hw with hw1 | rfl | ⟨y,hy1,rfl⟩
      · rw [mAOW] at hw1
        rcases hw1 with h | rfl | ⟨x,hx,rfl⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inl ⟨x,hx,rfl⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · rw [mAOW] at hy1
        rcases hy1 with hyS | rfl | ⟨x,hx,rfl⟩
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨y,hyS,rfl⟩))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨x,hx,rfl⟩)))))
    have h6_cases : l0_15 o1=18 ∨ l0_15 o2=18 ∨ (l0_15 o1&&&l0_15 o2)=18:=by
      rcases hcases_S2 w6 hw6 with hx | rfl | ⟨x,hx,rfl⟩ | rfl | ⟨x,hx,rfl⟩ | rfl | ⟨x,hx,rfl⟩
      · exact (hno6 w6 hx (by rw [h6w];decide)).elim
      · exact Or.inl h6w
      · rw [l0_15_and] at h6w
        exact (hno6 x hx (f32s2A.2.2.2 ⟨l0_15 x,l0_15_lt (hV x hx).1⟩ ⟨l0_15 o1,ho1_0_lt⟩ |>.1 h6w).1).elim
      · exact Or.inr (Or.inl h6w)
      · rw [l0_15_and] at h6w
        exact (hno6 x hx (f32s2A.2.2.2 ⟨l0_15 x,l0_15_lt (hV x hx).1⟩ ⟨l0_15 o2,ho2_0_lt⟩ |>.1 h6w).1).elim
      · rw [l0_15_and] at h6w;exact Or.inr (Or.inr h6w)
      · rw [l0_15_and,l0_15_and,baa] at h6w
        have ho12_lt : (l0_15 o1&&&l0_15 o2) < 32:=by have : (l0_15 o1&&&l0_15 o2) ≤ l0_15 o1:=Nat.and_le_left;omega
        exact (hno6 x hx (f32s2A.2.2.2 ⟨l0_15 x,l0_15_lt (hV x hx).1⟩ ⟨_,ho12_lt⟩ |>.1 h6w).1).elim
    have h7_cases : l0_15 o1=12 ∨ l0_15 o2=12 ∨ (l0_15 o1&&&l0_15 o2)=12:=by
      rcases hcases_S2 w7 hw7 with hx | rfl | ⟨x,hx,rfl⟩ | rfl | ⟨x,hx,rfl⟩ | rfl | ⟨x,hx,rfl⟩
      · exact (hno7 w7 hx (by rw [h7w];decide)).elim
      · exact Or.inl h7w
      · rw [l0_15_and] at h7w
        exact (hno7 x hx (f32s2A.2.2.2 ⟨l0_15 x,l0_15_lt (hV x hx).1⟩ ⟨l0_15 o1,ho1_0_lt⟩ |>.2 h7w).1).elim
      · exact Or.inr (Or.inl h7w)
      · rw [l0_15_and] at h7w
        exact (hno7 x hx (f32s2A.2.2.2 ⟨l0_15 x,l0_15_lt (hV x hx).1⟩ ⟨l0_15 o2,ho2_0_lt⟩ |>.2 h7w).1).elim
      · rw [l0_15_and] at h7w;exact Or.inr (Or.inr h7w)
      · rw [l0_15_and,l0_15_and,baa] at h7w
        have ho12_lt : (l0_15 o1&&&l0_15 o2) < 32:=by have : (l0_15 o1&&&l0_15 o2) ≤ l0_15 o1:=Nat.and_le_left;omega
        exact (hno7 x hx (f32s2A.2.2.2 ⟨l0_15 x,l0_15_lt (hV x hx).1⟩ ⟨_,ho12_lt⟩ |>.2 h7w).1).elim
    have hpair18_12 : (l0_15 o1=18 ∧ l0_15 o2=12) ∨ (l0_15 o1=12 ∧ l0_15 o2=18):=by
      have hdis:=f32s2A.1 ⟨l0_15 o1,ho1_0_lt⟩ ⟨l0_15 o2,ho2_0_lt⟩
      rcases h6_cases with e6 | e6 | e6<;>rcases h7_cases with e7 | e7 | e7
      · omega
      · exact Or.inl ⟨e6,e7⟩
      · exact ((hdis.2 e7).1 e6).elim
      · exact Or.inr ⟨e7,e6⟩
      · omega
      · exact ((hdis.2 e7).2 e6).elim
      · exact ((hdis.1 e6).1 e7).elim
      · exact ((hdis.1 e6).2 e7).elim
      · omega
    have h3_cases : l1_15 o1=20 ∨ l1_15 o2=20 ∨ (l1_15 o1&&&l1_15 o2)=20:=by
      rcases hcases_S2 w3 hw3 with hx | rfl | ⟨x,hx,rfl⟩ | rfl | ⟨x,hx,rfl⟩ | rfl | ⟨x,hx,rfl⟩
      · have:=hno3 w3 hx (by rw [h3w];decide);omega
      · exact Or.inl h3w
      · rw [l1_15_and] at h3w
        have ⟨hx20,h31⟩:=f32s2A.2.1 ⟨l1_15 x,l1_15_lt x⟩ ⟨l1_15 o1,ho1_1_lt⟩ h3w
        exact Or.inl (h31 (hno3 x hx hx20))
      · exact Or.inr (Or.inl h3w)
      · rw [l1_15_and] at h3w
        have ⟨hx20,h31⟩:=f32s2A.2.1 ⟨l1_15 x,l1_15_lt x⟩ ⟨l1_15 o2,ho2_1_lt⟩ h3w
        exact Or.inr (Or.inl (h31 (hno3 x hx hx20)))
      · rw [l1_15_and] at h3w;exact Or.inr (Or.inr h3w)
      · rw [l1_15_and,l1_15_and,baa] at h3w
        have ho12_lt : (l1_15 o1&&&l1_15 o2) < 32:=by have : (l1_15 o1&&&l1_15 o2) ≤ l1_15 o1:=Nat.and_le_left;omega
        have ⟨hx20,h31⟩:=f32s2A.2.1 ⟨l1_15 x,l1_15_lt x⟩ ⟨_,ho12_lt⟩ h3w
        exact Or.inr (Or.inr (h31 (hno3 x hx hx20)))
    have ho1_bad : l1_15 o1=31 ∨ (l1_15 o1&&&20) ≠ 20:=by
      by_contra hok
      push Not at hok
      have hsup : (l0_15 o1&&&18)=18 ∨ (l0_15 o1&&&12)=12:=by
        rcases hpair18_12 with ⟨e1,_⟩ | ⟨e1,_⟩
        · left;rw [e1];decide
        · right;rw [e1];decide
      have hcan : cS15 S=true:=by
        unfold cS15
        rw [List.any_eq_true]
        refine ⟨a,ha,List.any_eq_true.mpr ⟨b,hb,?_⟩⟩
        dsimp only
        rw [← l0_15_or,← l1_15_or]
        simp only [Bool.and_eq_true,Bool.or_eq_true,bne_iff_ne,beq_iff_eq]
        exact ⟨⟨hok.1,hok.2⟩,hsup⟩
      rw [hncan] at hcan;cases hcan
    have ho2_ne20 : l1_15 o2 ≠ 20:=by
      intro e20
      have hle:=ho2V.2
      rw [e20] at hle
      have h2_18_12 : l0_15 o2=18 ∨ l0_15 o2=12:=by rcases hpair18_12 with ⟨_,e⟩ | ⟨_,e⟩<;>[right;left]<;>exact e
      exact f32s2A.2.2.1 ⟨l0_15 o2,ho2_0_lt⟩ h2_18_12 hle
    rcases h3_cases with e1 | e2 | e12
    · rcases ho1_bad with h31 | hne20
      · omega
      · exact hne20 (by rw [e1];decide)
    · exact ho2_ne20 e2
    · have ⟨h1_20,h31⟩:=f32s2A.2.1 ⟨l1_15 o1,ho1_1_lt⟩ ⟨l1_15 o2,ho2_1_lt⟩ e12
      rcases ho1_bad with h1_31 | hne20
      · exact ho2_ne20 (h31 h1_31)
      · exact hne20 h1_20
  · exact hb0_le2
lemma lb15R : ∀ k S T,(∀ w ∈ S,V15 w) → ACl S → Reach15 k S T → lb15 S ≤ k:=by
  intro k
  match k with
  | 0 =>
    intro S T _ _ hr
    rcases hr with ⟨rfl,h0⟩
    unfold lb15;dsimp only;rw [h0];simp
  | 1 =>
    intro S T hV hC hr
    rcases hr with hr0 | ⟨a,ha,b,hb,hr0⟩
    · rcases hr0 with ⟨rfl,h0⟩
      unfold lb15;dsimp only;rw [h0];simp
    · rcases hr0 with ⟨rfl,h0⟩
      exact s1_15 hV hC ha hb h0
  | 2 =>
    intro S T hV hC hr
    rcases hr with hr1 | ⟨a,ha,b,hb,hr1⟩
    · exact (lb15R 1 S T hV hC hr1).trans (by omega)
    · rcases hr1 with hr0 | ⟨c,hc,d,hd,hr0⟩
      · rcases hr0 with ⟨rfl,h0⟩
        exact (s1_15 hV hC ha hb h0).trans (by omega)
      · rcases hr0 with ⟨rfl,h0⟩
        exact s2_15 hV hC ha hb hc hd h0
  | k + 3 =>
    intro S T _ _ _
    exact (lb15_le_3 S).trans (by omega)
lemma uS15e (S : List ℕ) (o : ℕ) :
    uS15 (st15 S) o=st15 (aOW S o):=by
  rw [stats15_eq,stats15_eq]
  unfold uS15
  dsimp only
  simp only [apply_ite Prod.fst,apply_ite Prod.snd]
  have hP18 : ∀ a b,((l0_15 (wAnd a b)&&&18)==18)=(((l0_15 a&&&18)==18)&&((l0_15 b&&&18)==18)):=by
    intro a b;rw [l0_15_and]
    apply Bool.eq_iff_iff.mpr;simp only [Bool.and_eq_true,beq_iff_eq]
    constructor
    · intro h;constructor
      · apply Nat.eq_of_testBit_eq;intro k;have hk:=congrArg (fun n=>n.testBit k) h
        simp only [Nat.testBit_and] at hk ⊢;cases h1 : (l0_15 a).testBit k<;>cases h2 : (l0_15 b).testBit k<;>cases h3 : (18 : ℕ).testBit k<;>simp_all
      · apply Nat.eq_of_testBit_eq;intro k;have hk:=congrArg (fun n=>n.testBit k) h
        simp only [Nat.testBit_and] at hk ⊢;cases h1 : (l0_15 a).testBit k<;>cases h2 : (l0_15 b).testBit k<;>cases h3 : (18 : ℕ).testBit k<;>simp_all
    · rintro ⟨ha,hb⟩;apply Nat.eq_of_testBit_eq;intro k
      have h1:=congrArg (fun n=>n.testBit k) ha;have h2:=congrArg (fun n=>n.testBit k) hb
      simp only [Nat.testBit_and] at h1 h2 ⊢;cases hta : (l0_15 a).testBit k<;>cases htb : (l0_15 b).testBit k<;>cases htm : (18 : ℕ).testBit k<;>simp_all
  have hP12 : ∀ a b,((l0_15 (wAnd a b)&&&12)==12)=(((l0_15 a&&&12)==12)&&((l0_15 b&&&12)==12)):=by
    intro a b;rw [l0_15_and]
    apply Bool.eq_iff_iff.mpr;simp only [Bool.and_eq_true,beq_iff_eq]
    constructor
    · intro h;constructor
      · apply Nat.eq_of_testBit_eq;intro k;have hk:=congrArg (fun n=>n.testBit k) h
        simp only [Nat.testBit_and] at hk ⊢;cases h1 : (l0_15 a).testBit k<;>cases h2 : (l0_15 b).testBit k<;>cases h3 : (12 : ℕ).testBit k<;>simp_all
      · apply Nat.eq_of_testBit_eq;intro k;have hk:=congrArg (fun n=>n.testBit k) h
        simp only [Nat.testBit_and] at hk ⊢;cases h1 : (l0_15 a).testBit k<;>cases h2 : (l0_15 b).testBit k<;>cases h3 : (12 : ℕ).testBit k<;>simp_all
    · rintro ⟨ha,hb⟩;apply Nat.eq_of_testBit_eq;intro k
      have h1:=congrArg (fun n=>n.testBit k) ha;have h2:=congrArg (fun n=>n.testBit k) hb
      simp only [Nat.testBit_and] at h1 h2 ⊢;cases hta : (l0_15 a).testBit k<;>cases htb : (l0_15 b).testBit k<;>cases htm : (12 : ℕ).testBit k<;>simp_all
  have hP20 : ∀ a b,((l1_15 (wAnd a b)&&&20)==20)=(((l1_15 a&&&20)==20)&&((l1_15 b&&&20)==20)):=by
    intro a b;rw [l1_15_and]
    exact Bool.eq_iff_iff.mpr (by
      simp only [Bool.and_eq_true,beq_iff_eq]
      exact fin32_and_eq_m.2.2 ⟨l1_15 a,l1_15_lt a⟩ ⟨l1_15 b,l1_15_lt b⟩)
  have c1:=(fAIa (fun w=>(l0_15 w&&&18)==18) l0_15 S o hP18 l0_15_and).symm
  have c2:=(fAIa (fun w=>(l0_15 w&&&12)==12) l0_15 S o hP12 l0_15_and).symm
  have c3:=(fAIa (fun w=>(l1_15 w&&&20)==20) l1_15 S o hP20 l1_15_and).symm
  have c4 : (if (l0_15 o&&&18)==18 then true else S.any (fun w=>(l0_15 w&&&18)==18)) =
      (aOW S o).any (fun w=>(l0_15 w&&&18)==18):=by
    apply Bool.eq_iff_iff.mpr
    cases ho18 : ((l0_15 o&&&18)==18)
    · simp only [Bool.false_eq_true,↓reduceIte,List.any_eq_true,mAOW]
      constructor
      · rintro ⟨w,hw,hp⟩;exact ⟨w,Or.inl hw,hp⟩
      · rintro ⟨w,hwS | rfl | ⟨a,ha,rfl⟩,hp⟩
        · exact ⟨w,hwS,hp⟩
        · rw [ho18] at hp;cases hp
        · rw [hP18,ho18,Bool.and_false] at hp;cases hp
    · simp only [↓reduceIte,true_iff,List.any_eq_true,mAOW];exact ⟨o,Or.inr (Or.inl rfl),ho18⟩
  have c5 : (if (l0_15 o&&&12)==12 then true else S.any (fun w=>(l0_15 w&&&12)==12)) =
      (aOW S o).any (fun w=>(l0_15 w&&&12)==12):=by
    apply Bool.eq_iff_iff.mpr
    cases ho12 : ((l0_15 o&&&12)==12)
    · simp only [Bool.false_eq_true,↓reduceIte,List.any_eq_true,mAOW]
      constructor
      · rintro ⟨w,hw,hp⟩;exact ⟨w,Or.inl hw,hp⟩
      · rintro ⟨w,hwS | rfl | ⟨a,ha,rfl⟩,hp⟩
        · exact ⟨w,hwS,hp⟩
        · rw [ho12] at hp;cases hp
        · rw [hP12,ho12,Bool.and_false] at hp;cases hp
    · simp only [↓reduceIte,true_iff,List.any_eq_true,mAOW];exact ⟨o,Or.inr (Or.inl rfl),ho12⟩
  have c6 : (if (l1_15 o&&&20)==20 then S.any (fun w=>(l1_15 w&&&20)==20&&(l1_15 w != 31))||(l1_15 o != 31)
             else S.any (fun w=>(l1_15 w&&&20)==20&&(l1_15 w != 31))) =
      (aOW S o).any (fun w=>(l1_15 w&&&20)==20&&(l1_15 w != 31)):=by
    apply Bool.eq_iff_iff.mpr
    cases ho20 : ((l1_15 o&&&20)==20)
    · simp only [Bool.false_eq_true,↓reduceIte,List.any_eq_true,mAOW,Bool.and_eq_true]
      constructor
      · rintro ⟨w,hw,hp⟩;exact ⟨w,Or.inl hw,hp⟩
      · rintro ⟨w,hwS | rfl | ⟨a,ha,rfl⟩,hp1,hp2⟩
        · exact ⟨w,hwS,hp1,hp2⟩
        · rw [ho20] at hp1;cases hp1
        · rw [hP20,ho20,Bool.and_false] at hp1;cases hp1
    · simp only [↓reduceIte,Bool.or_eq_true,List.any_eq_true,mAOW,Bool.and_eq_true]
      constructor
      · rintro (⟨w,hw,hp⟩ | hne31)
        · exact ⟨w,Or.inl hw,hp⟩
        · exact ⟨o,Or.inr (Or.inl rfl),ho20,hne31⟩
      · rintro ⟨w,hwS | rfl | ⟨a,ha,rfl⟩,hp1,hp2⟩
        · exact Or.inl ⟨w,hwS,hp1,hp2⟩
        · exact Or.inr hp2
        · rw [hP20,ho20,Bool.and_true] at hp1
          by_cases ha31 : l1_15 a=31
          · right
            rw [l1_15_and,ha31] at hp2
            have h31 : (31&&&l1_15 o)=l1_15 o :=
              (by decide : ∀ x : Fin 32,(31&&&x.val)=x.val) ⟨l1_15 o,l1_15_lt o⟩
            rwa [h31] at hp2
          · exact Or.inl ⟨a,ha,hp1,bne_iff_ne.mpr ha31⟩
  refine Prod.ext c1 (Prod.ext c2 (Prod.ext c3 (Prod.ext c4 (Prod.ext c5 c6))))
lemma lb15Bl (S : List ℕ) : lb15B (st15 S) ≤ lb15 S:=by
  unfold lb15;dsimp only;split_ifs with h0 h1
  · simp [beq_iff_eq] at h0;omega
  · have : lb15B (st15 S) ≤ 2:=by unfold lb15B;dsimp only;split_ifs<;>omega
    omega
  · exact le_rfl
lemma sc15s {src dst : List (List ℕ)} {rem : ℕ}
    (hchk : sc15 src dst rem=true)
    {S T : List ℕ} (hS : S ∈ src) (hP : S.Pairwise (· < ·)) (hV : ∀ w ∈ S,V15 w) (hC : ACl S)
    (hr : Reach15 (rem + 1) S T) :
    ∃ S' ∈ dst,S'.Pairwise (· < ·) ∧ (∀ w ∈ S',V15 w) ∧ ACl S' ∧ Reach15 rem S' T:=by
  have h1:=List.all_eq_true.mp hchk S hS
  simp only [Bool.and_eq_true] at h1
  rcases hr with hr0 | ⟨a,ha,b,hb,hr0⟩
  · have hlb:=lb15R rem S T hV hC hr0
    have hmem : dst.elem S=true:=by
      rcases Bool.or_eq_true .. |>.mp h1.1 with hgt | hm
      · simp at hgt;omega
      · exact hm
    exact ⟨S,by simpa [List.elem_eq_mem] using hmem,hP,hV,hC,hr0⟩
  · set o:=wOr a b
    by_cases hoS : o ∈ S
    · have heq:=addOrW_of_mem hP hC hoS
      rw [heq] at hr0
      have hlb:=lb15R rem S T hV hC hr0
      have hmem : dst.elem S=true:=by
        rcases Bool.or_eq_true .. |>.mp h1.1 with hgt | hm
        · simp at hgt;omega
        · exact hm
      exact ⟨S,by simpa [List.elem_eq_mem] using hmem,hP,hV,hC,hr0⟩
    · have hab : a ≠ b:=by
        intro e;subst e;apply hoS;simpa [o,wOr,bos] using ha
      have hpair:=allPairsOk_spec h1.2 ha hb hab
      have hne : S.elem o=false:=by
        cases he : S.elem o
        · rfl
        · exact (hoS (by simpa [List.elem_eq_mem] using he)).elim
      have hP' : (aOW S o).Pairwise (· < ·):=pwAOW hP o
      have hoV : V15 o:=v15o (hV a ha) (hV b hb)
      have hV' : ∀ w ∈ aOW S o,V15 w:=by
        intro w hw;rw [mAOW] at hw
        rcases hw with hwS | rfl | ⟨x,hx,rfl⟩
        · exact hV w hwS
        · exact hoV
        · exact v15a (hV x hx) hoV
      have hC' : ACl (aOW S o):=acAOW hC o
      have hlb:=lb15R rem (aOW S o) T hV' hC' hr0
      have hfast : ¬ lb15B (uS15 (st15 S) o) > rem:=by
        rw [uS15e];have:=lb15Bl (aOW S o);omega
      change (if lb15B (uS15 (st15 S) o) > rem then true
          else if S.elem o=true then true
          else decide (lb15 (aOW S o) > rem)||dst.elem (aOW S o))=true at hpair
      rw [if_neg hfast,if_neg (by rw [hne];decide)] at hpair
      have hmem : dst.elem (aOW S o)=true:=by
        rcases Bool.or_eq_true .. |>.mp hpair with hgt | hm
        · simp at hgt;omega
        · exact hm
      exact ⟨aOW S o,by simpa [List.elem_eq_mem] using hmem,hP',hV',hC',hr0⟩
lemma C0_15W_props : C0_15W.Pairwise (· < ·) ∧ (∀ w ∈ C0_15W,V15 w) ∧ ACl C0_15W:=by
  unfold V15 ACl
  decide +kernel
lemma kill_OW3 {T : List ℕ} (hr : Reach15 3 C0_15W T) :
    ∀ w ∈ T,l0_15 w=0 → ((e5_15 w>>>4)&&&1)=0 → pop4 (e5_15 w&&&15) ≤ 1:=by
  have ht:=test_OW3
  simp only [Bool.and_eq_true] at ht
  obtain ⟨⟨⟨hs1,hs2⟩,hs3⟩,hq3⟩:=ht
  obtain ⟨hP0,hV0,hC0⟩:=C0_15W_props
  obtain ⟨S1,hS1,hP1,hV1,hC1,hr1⟩:=sc15s hs1 (List.mem_singleton_self _) hP0 hV0 hC0 hr
  obtain ⟨S2,hS2,hP2,hV2,hC2,hr2⟩:=sc15s hs2 hS1 hP1 hV1 hC1 hr1
  obtain ⟨S3,hS3,_,_,_,hr3⟩:=sc15s hs3 hS2 hP2 hV2 hC2 hr2
  rcases hr3 with ⟨rfl,_⟩
  intro w hw h0 hn28
  have h1:=List.all_eq_true.mp (List.all_eq_true.mp hq3 S3 hS3) w hw
  simp only [h0,hn28,beq_self_eq_true,Bool.and_self,↓reduceIte,decide_eq_true_eq] at h1
  exact h1
lemma l0_14_lt {w : ℕ} (hw : w < 16384) : l0_14 w < 32:=by
  unfold l0_14;rw [Nat.shiftRight_eq_div_pow];omega
lemma l1_14_lt (w : ℕ) : l1_14 w < 32:=by
  unfold l1_14;have : ((w>>>4)&&&31) ≤ 31:=Nat.and_le_right;omega
lemma e4_14_lt (w : ℕ) : e4_14 w < 16:=by
  unfold e4_14;have : (w&&&15) ≤ 15:=Nat.and_le_right;omega
lemma l0_14_and (a b : ℕ) : l0_14 (wAnd a b)=(l0_14 a&&&l0_14 b):=by
  apply Nat.eq_of_testBit_eq;intro k;simp [l0_14,wAnd,Nat.testBit_shiftRight,Nat.testBit_and]
lemma l1_14_and (a b : ℕ) : l1_14 (wAnd a b)=(l1_14 a&&&l1_14 b):=by
  apply Nat.eq_of_testBit_eq;intro k
  simp [l1_14,wAnd,Nat.testBit_shiftRight,Nat.testBit_and]
  cases (a.testBit (4 + k))<;>cases (b.testBit (4 + k))<;>cases ((31 : ℕ).testBit k)<;>rfl
lemma e4_14_and (a b : ℕ) : e4_14 (wAnd a b)=(e4_14 a&&&e4_14 b):=by
  apply Nat.eq_of_testBit_eq;intro k
  simp [e4_14,wAnd,Nat.testBit_and]
  cases (a.testBit k)<;>cases (b.testBit k)<;>cases ((15 : ℕ).testBit k)<;>rfl
lemma l0_14_or (a b : ℕ) : l0_14 (wOr a b)=(l0_14 a|||l0_14 b):=by
  apply Nat.eq_of_testBit_eq;intro k;simp [l0_14,wOr,Nat.testBit_shiftRight,Nat.testBit_or]
lemma l1_14_or (a b : ℕ) : l1_14 (wOr a b)=(l1_14 a|||l1_14 b):=by
  apply Nat.eq_of_testBit_eq;intro k
  simp [l1_14,wOr,Nat.testBit_shiftRight,Nat.testBit_and,Nat.testBit_or]
  cases (a.testBit (4 + k))<;>cases (b.testBit (4 + k))<;>cases ((31 : ℕ).testBit k)<;>rfl
lemma e4_14_or (a b : ℕ) : e4_14 (wOr a b)=(e4_14 a|||e4_14 b):=by
  apply Nat.eq_of_testBit_eq;intro k
  simp [e4_14,wOr,Nat.testBit_and,Nat.testBit_or]
  cases (a.testBit k)<;>cases (b.testBit k)<;>cases ((15 : ℕ).testBit k)<;>rfl
def V14 (w : ℕ) : Prop:=w < 16384 ∧ (l0_14 w&&&l1_14 w)=l0_14 w
lemma v14a {a b : ℕ} (ha : V14 a) (hb : V14 b) : V14 (wAnd a b):=by
  refine ⟨by have:=ha.1;have : wAnd a b ≤ a:=Nat.and_le_left;omega,?_⟩
  rw [l0_14_and,l1_14_and]
  apply Nat.eq_of_testBit_eq;intro k
  have h1:=congrArg (fun n=>n.testBit k) ha.2
  have h2:=congrArg (fun n=>n.testBit k) hb.2
  simp only [Nat.testBit_and] at h1 h2 ⊢
  cases ha0 : (l0_14 a).testBit k<;>cases hb0 : (l0_14 b).testBit k <;>
  cases ha1 : (l1_14 a).testBit k<;>cases hb1 : (l1_14 b).testBit k<;>simp_all
lemma v14o {a b : ℕ} (ha : V14 a) (hb : V14 b) : V14 (wOr a b):=by
  refine ⟨or_lt16384 ha.1 hb.1,?_⟩
  rw [l0_14_or,l1_14_or]
  apply Nat.eq_of_testBit_eq;intro k
  have h1:=congrArg (fun n=>n.testBit k) ha.2
  have h2:=congrArg (fun n=>n.testBit k) hb.2
  simp only [Nat.testBit_and,Nat.testBit_or] at h1 h2 ⊢
  cases ha0 : (l0_14 a).testBit k<;>cases hb0 : (l0_14 b).testBit k <;>
  cases ha1 : (l1_14 a).testBit k<;>cases hb1 : (l1_14 b).testBit k<;>simp_all
lemma symM5_props :
    (∀ a : Fin 32,symM5 a.val < 32 ∧ symM5 (symM5 a.val)=a.val) ∧
    (∀ a b : Fin 32,symM5 (a.val&&&b.val)=(symM5 a.val&&&symM5 b.val) ∧
                     symM5 (a.val|||b.val)=(symM5 a.val|||symM5 b.val)) ∧
    (symM5 18=12 ∧ symM5 12=18 ∧ symM5 20=20 ∧ symM5 0=0):=by
  decide
lemma symE4_props :
    (∀ a : Fin 16,symE4 a.val < 16 ∧ symE4 (symE4 a.val)=a.val) ∧
    (∀ a b : Fin 16,symE4 (a.val&&&b.val)=(symE4 a.val&&&symE4 b.val) ∧
                     symE4 (a.val|||b.val)=(symE4 a.val|||symE4 b.val)) ∧
    (symE4 15=15):=by
  decide
lemma pack14_parts (a b c : ℕ) (ha : a < 32) (hb : b < 32) (hc : c < 16) :
    let w:=(a<<<9)|||(b<<<4)|||c
    w < 16384 ∧ l0_14 w=a ∧ l1_14 w=b ∧ e4_14 w=c:=by
  have h1 : (a<<<9) < 16384:=by rw [Nat.shiftLeft_eq];omega
  have h2 : (b<<<4) < 16384:=by rw [Nat.shiftLeft_eq];omega
  have h3 : c < 16384:=by omega
  have hw : ((a<<<9)|||(b<<<4)|||c) < 16384:=or_lt16384 (or_lt16384 h1 h2) h3
  have ha_hi : ∀ k ≥ 5,a.testBit k=false:=fun k hk =>
    Nat.testBit_lt_two_pow (by have : 2 ^ 5 ≤ 2 ^ k:=Nat.pow_le_pow_right (by omega) hk;omega)
  have hb_hi : ∀ k ≥ 5,b.testBit k=false:=fun k hk =>
    Nat.testBit_lt_two_pow (by have : 2 ^ 5 ≤ 2 ^ k:=Nat.pow_le_pow_right (by omega) hk;omega)
  have hc_hi : ∀ k ≥ 4,c.testBit k=false:=fun k hk =>
    Nat.testBit_lt_two_pow (by have : 2 ^ 4 ≤ 2 ^ k:=Nat.pow_le_pow_right (by omega) hk;omega)
  refine ⟨hw,?_,?_,?_⟩
  · apply Nat.eq_of_testBit_eq;intro k
    simp only [l0_14,Nat.testBit_shiftRight,Nat.testBit_or,Nat.testBit_shiftLeft]
    rw [hb_hi (9 + k - 4) (by omega),hc_hi (9 + k) (by omega)]
    simp [show 9 ≤ 9 + k by omega]
  · apply Nat.eq_of_testBit_eq;intro k
    simp only [l1_14,Nat.testBit_and,Nat.testBit_shiftRight,Nat.testBit_or,Nat.testBit_shiftLeft]
    by_cases hk : k < 5
    · have h31 : (31 : ℕ).testBit k=true:=(by decide : ∀ j : Fin 5,(31 : ℕ).testBit j.val=true) ⟨k,hk⟩
      rw [h31,hc_hi (4 + k) (by omega)]
      simp [show ¬ 9 ≤ 4 + k by omega,show 4 ≤ 4 + k by omega]
    · have h31 : (31 : ℕ).testBit k=false :=
        Nat.testBit_lt_two_pow (by have : 2 ^ 5 ≤ 2 ^ k:=Nat.pow_le_pow_right (by omega) (by omega);omega)
      rw [h31,hb_hi k (by omega)]
      simp
  · apply Nat.eq_of_testBit_eq;intro k
    simp only [e4_14,Nat.testBit_and,Nat.testBit_or,Nat.testBit_shiftLeft]
    by_cases hk : k < 4
    · have h15 : (15 : ℕ).testBit k=true:=(by decide : ∀ j : Fin 4,(15 : ℕ).testBit j.val=true) ⟨k,hk⟩
      rw [h15]
      simp [show ¬ 9 ≤ k by omega,show ¬ 4 ≤ k by omega]
    · have h15 : (15 : ℕ).testBit k=false :=
        Nat.testBit_lt_two_pow (by have : 2 ^ 4 ≤ 2 ^ k:=Nat.pow_le_pow_right (by omega) (by omega);omega)
      rw [h15,hc_hi k (by omega)]
      simp
lemma symW_parts {w : ℕ} (hw : w < 16384) :
    symW w < 16384 ∧ l0_14 (symW w)=symM5 (l0_14 w) ∧
    l1_14 (symW w)=symM5 (l1_14 w) ∧ e4_14 (symW w)=symE4 (e4_14 w) :=
  pack14_parts _ _ _
    (symM5_props.1 ⟨l0_14 w,l0_14_lt hw⟩).1
    (symM5_props.1 ⟨l1_14 w,l1_14_lt w⟩).1
    (symE4_props.1 ⟨e4_14 w,e4_14_lt w⟩).1
lemma symW_valid {w : ℕ} (hw : V14 w) : V14 (symW w):=by
  obtain ⟨hlt,hl0,hl1,_⟩:=symW_parts hw.1
  refine ⟨hlt,?_⟩
  rw [hl0,hl1,← (symM5_props.2.1 ⟨l0_14 w,l0_14_lt hw.1⟩ ⟨l1_14 w,l1_14_lt w⟩).1,hw.2]
lemma symW_and {a b : ℕ} (ha : a < 16384) (hb : b < 16384) :
    symW (wAnd a b)=wAnd (symW a) (symW b):=by
  have hab : wAnd a b < 16384:=by have : wAnd a b ≤ a:=Nat.and_le_left;omega
  have h0 : symM5 (l0_14 (wAnd a b))=(symM5 (l0_14 a)&&&symM5 (l0_14 b)):=by
    rw [l0_14_and];exact (symM5_props.2.1 ⟨l0_14 a,l0_14_lt ha⟩ ⟨l0_14 b,l0_14_lt hb⟩).1
  have h1 : symM5 (l1_14 (wAnd a b))=(symM5 (l1_14 a)&&&symM5 (l1_14 b)):=by
    rw [l1_14_and];exact (symM5_props.2.1 ⟨l1_14 a,l1_14_lt a⟩ ⟨l1_14 b,l1_14_lt b⟩).1
  have he : symE4 (e4_14 (wAnd a b))=(symE4 (e4_14 a)&&&symE4 (e4_14 b)):=by
    rw [e4_14_and];exact (symE4_props.2.1 ⟨e4_14 a,e4_14_lt a⟩ ⟨e4_14 b,e4_14_lt b⟩).1
  unfold symW
  rw [h0,h1,he]
  apply Nat.eq_of_testBit_eq;intro k
  have ha0:=(symM5_props.1 ⟨l0_14 a,l0_14_lt ha⟩).1
  have hb0:=(symM5_props.1 ⟨l0_14 b,l0_14_lt hb⟩).1
  have ha1:=(symM5_props.1 ⟨l1_14 a,l1_14_lt a⟩).1
  have hb1:=(symM5_props.1 ⟨l1_14 b,l1_14_lt b⟩).1
  have hae:=(symE4_props.1 ⟨e4_14 a,e4_14_lt a⟩).1
  have hbe:=(symE4_props.1 ⟨e4_14 b,e4_14_lt b⟩).1
  have hhi5 : ∀ x < 32,∀ j ≥ 5,x.testBit j=false:=fun x hx j hj =>
    Nat.testBit_lt_two_pow (by have : 2 ^ 5 ≤ 2 ^ j:=Nat.pow_le_pow_right (by omega) hj;omega)
  have hhi4 : ∀ x < 16,∀ j ≥ 4,x.testBit j=false:=fun x hx j hj =>
    Nat.testBit_lt_two_pow (by have : 2 ^ 4 ≤ 2 ^ j:=Nat.pow_le_pow_right (by omega) hj;omega)
  simp only [wAnd,Nat.testBit_and,Nat.testBit_or,Nat.testBit_shiftLeft]
  by_cases hk4 : k < 4
  · simp [show ¬ 9 ≤ k by omega,show ¬ 4 ≤ k by omega]
  · by_cases hk9 : k < 9
    · rw [hhi4 _ hae k (by omega),hhi4 _ hbe k (by omega)]
      simp [show ¬ 9 ≤ k by omega,show 4 ≤ k by omega]
    · rw [hhi4 _ hae k (by omega),hhi4 _ hbe k (by omega),
          hhi5 _ ha1 (k - 4) (by omega),hhi5 _ hb1 (k - 4) (by omega)]
      simp [show 9 ≤ k by omega]
lemma symW_or {a b : ℕ} (ha : a < 16384) (hb : b < 16384) :
    symW (wOr a b)=wOr (symW a) (symW b):=by
  have h0 : symM5 (l0_14 (wOr a b))=(symM5 (l0_14 a)|||symM5 (l0_14 b)):=by
    rw [l0_14_or];exact (symM5_props.2.1 ⟨l0_14 a,l0_14_lt ha⟩ ⟨l0_14 b,l0_14_lt hb⟩).2
  have h1 : symM5 (l1_14 (wOr a b))=(symM5 (l1_14 a)|||symM5 (l1_14 b)):=by
    rw [l1_14_or];exact (symM5_props.2.1 ⟨l1_14 a,l1_14_lt a⟩ ⟨l1_14 b,l1_14_lt b⟩).2
  have he : symE4 (e4_14 (wOr a b))=(symE4 (e4_14 a)|||symE4 (e4_14 b)):=by
    rw [e4_14_or];exact (symE4_props.2.1 ⟨e4_14 a,e4_14_lt a⟩ ⟨e4_14 b,e4_14_lt b⟩).2
  unfold symW
  rw [h0,h1,he]
  apply Nat.eq_of_testBit_eq;intro k
  simp only [wOr,Nat.testBit_or,Nat.testBit_shiftLeft]
  cases (decide (9 ≤ k))<;>cases (decide (4 ≤ k)) <;>
  cases (symM5 (l0_14 a)).testBit (k - 9)<;>cases (symM5 (l0_14 b)).testBit (k - 9) <;>
  cases (symM5 (l1_14 a)).testBit (k - 4)<;>cases (symM5 (l1_14 b)).testBit (k - 4) <;>
  cases (symE4 (e4_14 a)).testBit k<;>cases (symE4 (e4_14 b)).testBit k<;>rfl
lemma symW_addOrW {S : List ℕ} {o : ℕ} (hV : ∀ w ∈ S,w < 16384) (ho : o < 16384) :
    sUn ((aOW S o).map symW)=aOW (sUn (S.map symW)) (symW o):=by
  apply sorted_eq_of_mem_iff (pairwise_sortUnique _) (pwAOW (pairwise_sortUnique _) _)
  intro y
  simp only [mem_sortUnique,List.mem_map,mAOW]
  constructor
  · rintro ⟨w,hwS | rfl | ⟨a,ha,rfl⟩,rfl⟩
    · exact Or.inl ⟨w,hwS,rfl⟩
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨symW a,⟨a,ha,rfl⟩,symW_and (hV a ha) ho⟩)
  · rintro (⟨w,hwS,rfl⟩ | rfl | ⟨b,⟨a,ha,rfl⟩,rfl⟩)
    · exact ⟨w,Or.inl hwS,rfl⟩
    · exact ⟨o,Or.inr (Or.inl rfl),rfl⟩
    · exact ⟨wAnd a o,Or.inr (Or.inr ⟨a,ha,rfl⟩),symW_and (hV a ha) ho⟩
lemma stats14_eq (S : List ℕ) :
    st14 S =
      (fAI (fun w=>(l0_14 w&&&18)==18) l0_14 S,
       fAI (fun w=>(l0_14 w&&&12)==12) l0_14 S,
       fAI (fun w=>(l1_14 w&&&20)==20) l1_14 S,
       fAI (fun w=>e4_14 w==15) l0_14 S,
       S.any (fun w=>(l0_14 w&&&18)==18),
       S.any (fun w=>(l0_14 w&&&12)==12),
       S.any (fun w=>(l1_14 w&&&20)==20&&(l1_14 w != 31)),
       S.any (fun w=>e4_14 w==15)):=by
  unfold st14 fAI
  have h : ∀ (l : List ℕ) (i18 i12 i20 ie15 : ℕ) (s6 s7 s3 sZ : Bool),
      l.foldl uS14 (i18,i12,i20,ie15,s6,s7,s3,sZ) =
      (l.foldl (fun acc w=>if (l0_14 w&&&18)==18 then acc&&&l0_14 w else acc) i18,
       l.foldl (fun acc w=>if (l0_14 w&&&12)==12 then acc&&&l0_14 w else acc) i12,
       l.foldl (fun acc w=>if (l1_14 w&&&20)==20 then acc&&&l1_14 w else acc) i20,
       l.foldl (fun acc w=>if e4_14 w==15 then acc&&&l0_14 w else acc) ie15,
       s6||l.any (fun w=>(l0_14 w&&&18)==18),
       s7||l.any (fun w=>(l0_14 w&&&12)==12),
       s3||l.any (fun w=>(l1_14 w&&&20)==20&&(l1_14 w != 31)),
       sZ||l.any (fun w=>e4_14 w==15)):=by
    intro l
    induction l with
    | nil=>intro i18 i12 i20 ie15 s6 s7 s3 sZ;simp
    | cons w ws ih =>
      intro i18 i12 i20 ie15 s6 s7 s3 sZ
      simp only [List.foldl_cons,List.any_cons,uS14]
      rw [ih]
      congr 1;· split_ifs<;>rfl
      congr 1;· split_ifs<;>rfl
      congr 1;· split_ifs<;>rfl
      congr 1;· split_ifs<;>rfl
      congr 1;· cases ((l0_14 w&&&18)==18)<;>cases s6<;>simp
      congr 1;· cases ((l0_14 w&&&12)==12)<;>cases s7<;>simp
      congr 1;· cases ((l1_14 w&&&20)==20)<;>cases (l1_14 w != 31)<;>cases s3<;>simp
      · cases (e4_14 w==15)<;>cases sZ<;>simp
  simpa using h S 31 31 31 31 false false false false
lemma uS14e {S : List ℕ} {o : ℕ} (hV : ∀ w ∈ S,w < 16384) (ho : o < 16384) :
    uS14 (st14 S) o=st14 (aOW S o):=by
  rw [stats14_eq,stats14_eq]
  unfold uS14
  dsimp only
  simp only [apply_ite Prod.fst,apply_ite Prod.snd]
  have hP18 : ∀ a b,((l0_14 (wAnd a b)&&&18)==18)=(((l0_14 a&&&18)==18)&&((l0_14 b&&&18)==18)):=by
    intro a b;rw [l0_14_and]
    apply Bool.eq_iff_iff.mpr;simp only [Bool.and_eq_true,beq_iff_eq]
    constructor
    · intro h;constructor
      · apply Nat.eq_of_testBit_eq;intro k;have hk:=congrArg (fun n=>n.testBit k) h
        simp only [Nat.testBit_and] at hk ⊢;cases h1 : (l0_14 a).testBit k<;>cases h2 : (l0_14 b).testBit k<;>cases h3 : (18 : ℕ).testBit k<;>simp_all
      · apply Nat.eq_of_testBit_eq;intro k;have hk:=congrArg (fun n=>n.testBit k) h
        simp only [Nat.testBit_and] at hk ⊢;cases h1 : (l0_14 a).testBit k<;>cases h2 : (l0_14 b).testBit k<;>cases h3 : (18 : ℕ).testBit k<;>simp_all
    · rintro ⟨ha,hb⟩;apply Nat.eq_of_testBit_eq;intro k
      have h1:=congrArg (fun n=>n.testBit k) ha;have h2:=congrArg (fun n=>n.testBit k) hb
      simp only [Nat.testBit_and] at h1 h2 ⊢;cases hta : (l0_14 a).testBit k<;>cases htb : (l0_14 b).testBit k<;>cases htm : (18 : ℕ).testBit k<;>simp_all
  have hP12 : ∀ a b,((l0_14 (wAnd a b)&&&12)==12)=(((l0_14 a&&&12)==12)&&((l0_14 b&&&12)==12)):=by
    intro a b;rw [l0_14_and]
    apply Bool.eq_iff_iff.mpr;simp only [Bool.and_eq_true,beq_iff_eq]
    constructor
    · intro h;constructor
      · apply Nat.eq_of_testBit_eq;intro k;have hk:=congrArg (fun n=>n.testBit k) h
        simp only [Nat.testBit_and] at hk ⊢;cases h1 : (l0_14 a).testBit k<;>cases h2 : (l0_14 b).testBit k<;>cases h3 : (12 : ℕ).testBit k<;>simp_all
      · apply Nat.eq_of_testBit_eq;intro k;have hk:=congrArg (fun n=>n.testBit k) h
        simp only [Nat.testBit_and] at hk ⊢;cases h1 : (l0_14 a).testBit k<;>cases h2 : (l0_14 b).testBit k<;>cases h3 : (12 : ℕ).testBit k<;>simp_all
    · rintro ⟨ha,hb⟩;apply Nat.eq_of_testBit_eq;intro k
      have h1:=congrArg (fun n=>n.testBit k) ha;have h2:=congrArg (fun n=>n.testBit k) hb
      simp only [Nat.testBit_and] at h1 h2 ⊢;cases hta : (l0_14 a).testBit k<;>cases htb : (l0_14 b).testBit k<;>cases htm : (12 : ℕ).testBit k<;>simp_all
  have hP20 : ∀ a b,((l1_14 (wAnd a b)&&&20)==20)=(((l1_14 a&&&20)==20)&&((l1_14 b&&&20)==20)):=by
    intro a b;rw [l1_14_and]
    exact Bool.eq_iff_iff.mpr (by
      simp only [Bool.and_eq_true,beq_iff_eq]
      exact fin32_and_eq_m.2.2 ⟨l1_14 a,l1_14_lt a⟩ ⟨l1_14 b,l1_14_lt b⟩)
  have hPe15 : ∀ a b,(e4_14 (wAnd a b)==15)=((e4_14 a==15)&&(e4_14 b==15)):=by
    intro a b;rw [e4_14_and]
    exact Bool.eq_iff_iff.mpr (by
      simp only [Bool.and_eq_true,beq_iff_eq]
      exact (by decide : ∀ x y : Fin 16,(x.val&&&y.val=15) ↔ (x.val=15 ∧ y.val=15)) ⟨e4_14 a,e4_14_lt a⟩ ⟨e4_14 b,e4_14_lt b⟩)
  have c1:=(fAIa (fun w=>(l0_14 w&&&18)==18) l0_14 S o hP18 l0_14_and).symm
  have c2:=(fAIa (fun w=>(l0_14 w&&&12)==12) l0_14 S o hP12 l0_14_and).symm
  have c3:=(fAIa (fun w=>(l1_14 w&&&20)==20) l1_14 S o hP20 l1_14_and).symm
  have c4:=(fAIa (fun w=>e4_14 w==15) l0_14 S o hPe15 l0_14_and).symm
  have c5 : (if (l0_14 o&&&18)==18 then true else S.any (fun w=>(l0_14 w&&&18)==18)) =
      (aOW S o).any (fun w=>(l0_14 w&&&18)==18):=by
    apply Bool.eq_iff_iff.mpr
    cases ho18 : ((l0_14 o&&&18)==18)
    · simp only [Bool.false_eq_true,↓reduceIte,List.any_eq_true,mAOW]
      constructor
      · rintro ⟨w,hw,hp⟩;exact ⟨w,Or.inl hw,hp⟩
      · rintro ⟨w,hwS | rfl | ⟨a,ha,rfl⟩,hp⟩
        · exact ⟨w,hwS,hp⟩
        · rw [ho18] at hp;cases hp
        · rw [hP18,ho18,Bool.and_false] at hp;cases hp
    · simp only [↓reduceIte,true_iff,List.any_eq_true,mAOW]
      exact ⟨o,Or.inr (Or.inl rfl),ho18⟩
  have c6 : (if (l0_14 o&&&12)==12 then true else S.any (fun w=>(l0_14 w&&&12)==12)) =
      (aOW S o).any (fun w=>(l0_14 w&&&12)==12):=by
    apply Bool.eq_iff_iff.mpr
    cases ho12 : ((l0_14 o&&&12)==12)
    · simp only [Bool.false_eq_true,↓reduceIte,List.any_eq_true,mAOW]
      constructor
      · rintro ⟨w,hw,hp⟩;exact ⟨w,Or.inl hw,hp⟩
      · rintro ⟨w,hwS | rfl | ⟨a,ha,rfl⟩,hp⟩
        · exact ⟨w,hwS,hp⟩
        · rw [ho12] at hp;cases hp
        · rw [hP12,ho12,Bool.and_false] at hp;cases hp
    · simp only [↓reduceIte,true_iff,List.any_eq_true,mAOW]
      exact ⟨o,Or.inr (Or.inl rfl),ho12⟩
  have c7 : (if (l1_14 o&&&20)==20 then S.any (fun w=>(l1_14 w&&&20)==20&&(l1_14 w != 31))||(l1_14 o != 31)
             else S.any (fun w=>(l1_14 w&&&20)==20&&(l1_14 w != 31))) =
      (aOW S o).any (fun w=>(l1_14 w&&&20)==20&&(l1_14 w != 31)):=by
    apply Bool.eq_iff_iff.mpr
    cases ho20 : ((l1_14 o&&&20)==20)
    · simp only [Bool.false_eq_true,↓reduceIte,List.any_eq_true,mAOW,Bool.and_eq_true]
      constructor
      · rintro ⟨w,hw,hp⟩;exact ⟨w,Or.inl hw,hp⟩
      · rintro ⟨w,hwS | rfl | ⟨a,ha,rfl⟩,hp1,hp2⟩
        · exact ⟨w,hwS,hp1,hp2⟩
        · rw [ho20] at hp1;cases hp1
        · rw [hP20,ho20,Bool.and_false] at hp1;cases hp1
    · simp only [↓reduceIte,Bool.or_eq_true,List.any_eq_true,mAOW,Bool.and_eq_true]
      constructor
      · rintro (⟨w,hw,hp⟩ | hne31)
        · exact ⟨w,Or.inl hw,hp⟩
        · exact ⟨o,Or.inr (Or.inl rfl),ho20,hne31⟩
      · rintro ⟨w,hwS | rfl | ⟨a,ha,rfl⟩,hp1,hp2⟩
        · exact Or.inl ⟨w,hwS,hp1,hp2⟩
        · exact Or.inr hp2
        · rw [hP20,ho20,Bool.and_true] at hp1
          by_cases ha31 : l1_14 a=31
          · right
            rw [l1_14_and,ha31] at hp2
            have h31 : (31&&&l1_14 o)=l1_14 o :=
              (by decide : ∀ x : Fin 32,(31&&&x.val)=x.val) ⟨l1_14 o,l1_14_lt o⟩
            rwa [h31] at hp2
          · exact Or.inl ⟨a,ha,hp1,bne_iff_ne.mpr ha31⟩
  have c8 : (if e4_14 o==15 then true else S.any (fun w=>e4_14 w==15)) =
      (aOW S o).any (fun w=>e4_14 w==15):=by
    apply Bool.eq_iff_iff.mpr
    cases hoe : (e4_14 o==15)
    · simp only [Bool.false_eq_true,↓reduceIte,List.any_eq_true,mAOW]
      constructor
      · rintro ⟨w,hw,hp⟩;exact ⟨w,Or.inl hw,hp⟩
      · rintro ⟨w,hwS | rfl | ⟨a,ha,rfl⟩,hp⟩
        · exact ⟨w,hwS,hp⟩
        · rw [hoe] at hp;cases hp
        · rw [hPe15,hoe,Bool.and_false] at hp;cases hp
    · simp only [↓reduceIte,true_iff,List.any_eq_true,mAOW]
      exact ⟨o,Or.inr (Or.inl rfl),hoe⟩
  refine Prod.ext c1 (Prod.ext c2 (Prod.ext c3 (Prod.ext c4 (Prod.ext c5 (Prod.ext c6 (Prod.ext c7 c8))))))
lemma s14G {S : List ℕ} (hV : ∀ w ∈ S,V14 w) (hC : ACl S) :
    lb14B (st14 S)=0 ↔
      (∃ w ∈ S,l0_14 w=18) ∧ (∃ w ∈ S,l0_14 w=12) ∧
      (∃ w ∈ S,l1_14 w=20) ∧ (∃ w ∈ S,e4_14 w=15 ∧ l0_14 w=0):=by
  rw [stats14_eq]
  set i18:=fAI (fun w=>(l0_14 w&&&18)==18) l0_14 S
  set i12:=fAI (fun w=>(l0_14 w&&&12)==12) l0_14 S
  set i20:=fAI (fun w=>(l1_14 w&&&20)==20) l1_14 S
  set ie15:=fAI (fun w=>e4_14 w==15) l0_14 S
  set s6:=S.any (fun w=>(l0_14 w&&&18)==18)
  set s7:=S.any (fun w=>(l0_14 w&&&12)==12)
  set s3:=S.any (fun w=>(l1_14 w&&&20)==20&&(l1_14 w != 31))
  set sZ:=S.any (fun w=>e4_14 w==15)
  have hbase0 : lb14B (i18,i12,i20,ie15,s6,s7,s3,sZ)=0 ↔
      (s6=true ∧ i18=18) ∧ (s7=true ∧ i12=12) ∧ (s3=true ∧ i20=20) ∧ (sZ=true ∧ ie15=0):=by
    unfold lb14B;dsimp only
    by_cases h1 : (s6&&(i18==18)&&(s7&&(i12==12))&&(s3&&(i20==20))&&(sZ&&(ie15==0)))=true
    · rw [if_pos h1];simp only [Bool.and_eq_true,beq_iff_eq] at h1;tauto
    · rw [if_neg h1]
      have hne0 : ∀ c : Bool,(if c=true then (2 : ℕ) else 1) ≠ 0:=fun c=>by cases c<;>decide
      exact ⟨fun h=>(hne0 _ h).elim,fun ⟨⟨a1,a2⟩,⟨b1,b2⟩,⟨c1,c2⟩,⟨d1,d2⟩⟩ =>
        (h1 (by simp [a1,a2,b1,b2,c1,c2,d1,d2])).elim⟩
  rw [hbase0]
  have heq6 : (s6=true ∧ i18=18) ↔ ∃ w ∈ S,l0_14 w=18:=by
    constructor
    · rintro ⟨hs6,hi⟩
      rw [List.any_eq_true] at hs6
      obtain ⟨w,hw,_,hfw⟩:=fAIw (fun w=>(l0_14 w&&&18)==18) l0_14
        (fun w hw=>l0_14_lt (hV w hw).1) hC
        (fun a b ha hb=>by
          simp only [beq_iff_eq] at ha hb ⊢;rw [l0_14_and]
          apply Nat.eq_of_testBit_eq;intro k
          have h1:=congrArg (fun n=>n.testBit k) ha;have h2:=congrArg (fun n=>n.testBit k) hb
          simp only [Nat.testBit_and] at h1 h2 ⊢;cases hta : (l0_14 a).testBit k<;>cases htb : (l0_14 b).testBit k<;>cases htm : (18 : ℕ).testBit k<;>simp_all)
        l0_14_and hs6
      exact ⟨w,hw,hfw.trans hi⟩
    · rintro ⟨w,hw,hw18⟩
      have hPw : ((l0_14 w&&&18)==18)=true:=by rw [hw18];decide
      refine ⟨List.any_eq_true.mpr ⟨w,hw,hPw⟩,?_⟩
      have hle:=fAIl (fun u=>(l0_14 u&&&18)==18) l0_14 hw hPw
      have hsup:=fAIs (S:=S) (fun u=>(l0_14 u&&&18)==18) l0_14 (m:=18) (by omega) (fun u _ hu=>beq_iff_eq.mp hu)
      rw [hw18] at hle;exact hle.symm.trans hsup
  have heq7 : (s7=true ∧ i12=12) ↔ ∃ w ∈ S,l0_14 w=12:=by
    constructor
    · rintro ⟨hs7,hi⟩
      rw [List.any_eq_true] at hs7
      obtain ⟨w,hw,_,hfw⟩:=fAIw (fun w=>(l0_14 w&&&12)==12) l0_14
        (fun w hw=>l0_14_lt (hV w hw).1) hC
        (fun a b ha hb=>by
          simp only [beq_iff_eq] at ha hb ⊢;rw [l0_14_and]
          apply Nat.eq_of_testBit_eq;intro k
          have h1:=congrArg (fun n=>n.testBit k) ha;have h2:=congrArg (fun n=>n.testBit k) hb
          simp only [Nat.testBit_and] at h1 h2 ⊢;cases hta : (l0_14 a).testBit k<;>cases htb : (l0_14 b).testBit k<;>cases htm : (12 : ℕ).testBit k<;>simp_all)
        l0_14_and hs7
      exact ⟨w,hw,hfw.trans hi⟩
    · rintro ⟨w,hw,hw12⟩
      have hPw : ((l0_14 w&&&12)==12)=true:=by rw [hw12];decide
      refine ⟨List.any_eq_true.mpr ⟨w,hw,hPw⟩,?_⟩
      have hle:=fAIl (fun u=>(l0_14 u&&&12)==12) l0_14 hw hPw
      have hsup:=fAIs (S:=S) (fun u=>(l0_14 u&&&12)==12) l0_14 (m:=12) (by omega) (fun u _ hu=>beq_iff_eq.mp hu)
      rw [hw12] at hle;exact hle.symm.trans hsup
  have heq3 : (s3=true ∧ i20=20) ↔ ∃ w ∈ S,l1_14 w=20:=by
    constructor
    · rintro ⟨hs3,hi⟩
      rw [List.any_eq_true] at hs3
      obtain ⟨w0,hw0,hP0⟩:=hs3
      obtain ⟨w,hw,_,hfw⟩:=fAIw (fun w=>(l1_14 w&&&20)==20) l1_14
        (fun w _=>l1_14_lt w) hC
        (fun a b ha hb=>by
          simp only [beq_iff_eq] at ha hb ⊢;rw [l1_14_and]
          exact (fin32_and_eq_m.2.2 ⟨l1_14 a,l1_14_lt a⟩ ⟨l1_14 b,l1_14_lt b⟩).mpr ⟨ha,hb⟩)
        l1_14_and ⟨w0,hw0,(Bool.and_eq_true .. |>.mp hP0).1⟩
      exact ⟨w,hw,hfw.trans hi⟩
    · rintro ⟨w,hw,hw20⟩
      have hPw : ((l1_14 w&&&20)==20)=true:=by rw [hw20];decide
      refine ⟨List.any_eq_true.mpr ⟨w,hw,by rw [hw20];decide⟩,?_⟩
      have hle:=fAIl (fun u=>(l1_14 u&&&20)==20) l1_14 hw hPw
      have hsup:=fAIs (S:=S) (fun u=>(l1_14 u&&&20)==20) l1_14 (m:=20) (by omega) (fun u _ hu=>beq_iff_eq.mp hu)
      rw [hw20] at hle;exact hle.symm.trans hsup
  have heqZ : (sZ=true ∧ ie15=0) ↔ ∃ w ∈ S,e4_14 w=15 ∧ l0_14 w=0:=by
    constructor
    · rintro ⟨hsZ,hi⟩
      rw [List.any_eq_true] at hsZ
      obtain ⟨w,hw,hPw,hfw⟩:=fAIw (fun w=>e4_14 w==15) l0_14
        (fun w hw=>l0_14_lt (hV w hw).1) hC
        (fun a b ha hb=>by
          simp only [beq_iff_eq] at ha hb ⊢;rw [e4_14_and,ha,hb];decide)
        l0_14_and hsZ
      exact ⟨w,hw,beq_iff_eq.mp hPw,hfw.trans hi⟩
    · rintro ⟨w,hw,hwe,hw0⟩
      have hPw : (e4_14 w==15)=true:=beq_iff_eq.mpr hwe
      refine ⟨List.any_eq_true.mpr ⟨w,hw,hPw⟩,?_⟩
      have hle:=fAIl (fun u=>e4_14 u==15) l0_14 hw hPw
      rw [hw0,ba0r] at hle
      exact hle.symm
  rw [heq6,heq7,heq3,heqZ]
def Reach14 : ℕ → List ℕ → Prop
  | 0,S=>lb14B (st14 S)=0
  | k + 1,S=>Reach14 k S ∨ ∃ a ∈ S,∃ b ∈ S,Reach14 k (aOW S (wOr a b))
lemma reach14_symW : ∀ k S,(∀ w ∈ S,V14 w) → ACl S → Reach14 k S →
    Reach14 k (sUn (S.map symW)):=by
  intro k
  induction k with
  | zero =>
    intro S hV hC hr
    have hVs : ∀ w ∈ sUn (S.map symW),V14 w:=by
      intro w hw;rw [mem_sortUnique,List.mem_map] at hw
      obtain ⟨u,hu,rfl⟩:=hw;exact symW_valid (hV u hu)
    have hCs : ACl (sUn (S.map symW)):=by
      intro x hx y hy;rw [mem_sortUnique,List.mem_map] at hx hy ⊢
      obtain ⟨a,ha,rfl⟩:=hx;obtain ⟨b,hb,rfl⟩:=hy
      exact ⟨wAnd a b,hC a ha b hb,symW_and (hV a ha).1 (hV b hb).1⟩
    simp only [Reach14] at hr ⊢
    rw [s14G hV hC] at hr
    rw [s14G hVs hCs]
    obtain ⟨⟨w6,hw6,e6⟩,⟨w7,hw7,e7⟩,⟨w3,hw3,e3⟩,⟨wZ,hwZ,eZe,eZ0⟩⟩:=hr
    refine ⟨⟨symW w7,by rw [mem_sortUnique,List.mem_map];exact ⟨w7,hw7,rfl⟩,
              by rw [(symW_parts (hV w7 hw7).1).2.1,e7];exact symM5_props.2.2.2.1⟩,
            ⟨symW w6,by rw [mem_sortUnique,List.mem_map];exact ⟨w6,hw6,rfl⟩,
              by rw [(symW_parts (hV w6 hw6).1).2.1,e6];exact symM5_props.2.2.1⟩,
            ⟨symW w3,by rw [mem_sortUnique,List.mem_map];exact ⟨w3,hw3,rfl⟩,
              by rw [(symW_parts (hV w3 hw3).1).2.2.1,e3];exact symM5_props.2.2.2.2.1⟩,
            ⟨symW wZ,by rw [mem_sortUnique,List.mem_map];exact ⟨wZ,hwZ,rfl⟩,
              by rw [(symW_parts (hV wZ hwZ).1).2.2.2,eZe];exact symE4_props.2.2,
              by rw [(symW_parts (hV wZ hwZ).1).2.1,eZ0];exact symM5_props.2.2.2.2.2⟩⟩
  | succ k ih =>
    intro S hV hC hr
    rcases hr with hr0 | ⟨a,ha,b,hb,hr0⟩
    · exact Or.inl (ih S hV hC hr0)
    · right
      refine ⟨symW a,by rw [mem_sortUnique,List.mem_map];exact ⟨a,ha,rfl⟩,
              symW b,by rw [mem_sortUnique,List.mem_map];exact ⟨b,hb,rfl⟩,?_⟩
      have hoV : V14 (wOr a b):=v14o (hV a ha) (hV b hb)
      have hV' : ∀ w ∈ aOW S (wOr a b),V14 w:=by
        intro w hw;rw [mAOW] at hw
        rcases hw with hwS | rfl | ⟨x,hx,rfl⟩
        · exact hV w hwS
        · exact hoV
        · exact v14a (hV x hx) hoV
      have h1:=ih (aOW S (wOr a b)) hV' (acAOW hC _) hr0
      rw [symW_addOrW (fun w hw=>(hV w hw).1) hoV.1,symW_or (hV a ha).1 (hV b hb).1] at h1
      exact h1
lemma reach14_canonW {k : ℕ} {S : List ℕ} (hV : ∀ w ∈ S,V14 w) (hC : ACl S) (hr : Reach14 k S) :
    Reach14 k (canonW S):=by
  unfold canonW;dsimp only;split_ifs
  · exact hr
  · exact reach14_symW k S hV hC hr
lemma canonW_props {S : List ℕ} (hP : S.Pairwise (· < ·)) (hV : ∀ w ∈ S,V14 w) (hC : ACl S) :
    (canonW S).Pairwise (· < ·) ∧ (∀ w ∈ canonW S,V14 w) ∧ ACl (canonW S):=by
  unfold canonW;dsimp only;split_ifs
  · exact ⟨hP,hV,hC⟩
  · refine ⟨pairwise_sortUnique _,?_,?_⟩
    · intro w hw;rw [mem_sortUnique,List.mem_map] at hw;obtain ⟨u,hu,rfl⟩:=hw;exact symW_valid (hV u hu)
    · intro x hx y hy;rw [mem_sortUnique,List.mem_map] at hx hy ⊢
      obtain ⟨a,ha,rfl⟩:=hx;obtain ⟨b,hb,rfl⟩:=hy
      exact ⟨wAnd a b,hC a ha b hb,symW_and (hV a ha).1 (hV b hb).1⟩
lemma lb14Base_le_2 (st : ℕ × ℕ × ℕ × ℕ × Bool × Bool × Bool × Bool) : lb14B st ≤ 2:=by
  unfold lb14B;dsimp only
  by_cases h1 : (st.2.2.2.2.1&&(st.1==18)&&(st.2.2.2.2.2.1&&(st.2.1==12)) &&
      (st.2.2.2.2.2.2.1&&(st.2.2.1==20))&&(st.2.2.2.2.2.2.2&&(st.2.2.2.1==0)))=true
  · rw [if_pos h1];omega
  · rw [if_neg h1];split_ifs<;>omega
lemma lb14_le_3 (S : List ℕ) : lb14 S ≤ 3:=by
  unfold lb14;dsimp only
  have hle2:=lb14Base_le_2 (st14 S)
  by_cases h0 : (lb14B (st14 S)==0)=true
  · rw [if_pos h0];omega
  · rw [if_neg h0]
    set b1:=if decide (lb14B (st14 S) < 2)&&!(st14 S).2.2.2.2.2.2.2&&!(st14 S).2.2.2.2.2.2.2 then 2 else lb14B (st14 S)
    have h1 : ∀ (c1 c2 c3 c4 : Bool),
        let x1:=if c1 then 2 else lb14B (st14 S)
        let x2:=if c2 then 3 else x1
        (if c3 then (if c4 then 3 else x2) else x2) ≤ 3:=by
      intro c1 c2 c3 c4;dsimp only;cases c1<;>cases c2<;>cases c3<;>cases c4<;>simp<;>omega
    exact h1 _ _ _ _
lemma s1_14 {S : List ℕ} (hV : ∀ w ∈ S,V14 w) (hC : ACl S)
    {a b : ℕ} (ha : a ∈ S) (hb : b ∈ S)
    (hG : lb14B (st14 (aOW S (wOr a b)))=0) :
    lb14 S ≤ 1:=by
  set o:=wOr a b
  have hoV : V14 o:=v14o (hV a ha) (hV b hb)
  have hV' : ∀ w ∈ aOW S o,V14 w:=by
    intro w hw;rw [mAOW] at hw
    rcases hw with hwS | rfl | ⟨x,hx,rfl⟩
    · exact hV w hwS
    · exact hoV
    · exact v14a (hV x hx) hoV
  obtain ⟨⟨w6,hw6,h6w⟩,⟨w7,hw7,h7w⟩,⟨w3,hw3,h3w⟩,⟨wZ,hwZ,hZe,hZ0⟩⟩ :=
    (s14G hV' (acAOW hC o)).mp hG
  unfold lb14
  rw [stats14_eq]
  set i18:=fAI (fun w=>(l0_14 w&&&18)==18) l0_14 S
  set i12:=fAI (fun w=>(l0_14 w&&&12)==12) l0_14 S
  set i20:=fAI (fun w=>(l1_14 w&&&20)==20) l1_14 S
  set ie15:=fAI (fun w=>e4_14 w==15) l0_14 S
  set s6:=S.any (fun w=>(l0_14 w&&&18)==18)
  set s7:=S.any (fun w=>(l0_14 w&&&12)==12)
  set s3:=S.any (fun w=>(l1_14 w&&&20)==20&&(l1_14 w != 31))
  set sZ:=S.any (fun w=>e4_14 w==15)
  have hi18_lt : i18 < 32:=fAIt ..
  have hi12_lt : i12 < 32:=fAIt ..
  have hi20_lt : i20 < 32:=fAIt ..
  have hie15_lt : ie15 < 32:=fAIt ..
  have ho0_lt : l0_14 o < 32:=l0_14_lt hoV.1
  have ho1_lt : l1_14 o < 32:=l1_14_lt o
  have hi18_sup : (i18&&&18)=18:=fAIs _ _ (by omega) (fun u _ hu=>beq_iff_eq.mp hu)
  have hi12_sup : (i12&&&12)=12:=fAIs _ _ (by omega) (fun u _ hu=>beq_iff_eq.mp hu)
  have hi20_sup : (i20&&&20)=20:=fAIs _ _ (by omega) (fun u _ hu=>beq_iff_eq.mp hu)
  have h18_info : ¬ (s6=true ∧ i18=18) →
      (l0_14 o&&&18)=18 ∧ (l0_14 o&&&(i18&&&(31^^^18)))=0 ∧ (s6=false → l0_14 o=18):=by
    intro hnh6
    have hw6_notS : w6 ∉ S:=by
      intro hm;apply hnh6
      have hPw : ((l0_14 w6&&&18)==18)=true:=by rw [h6w];decide
      refine ⟨List.any_eq_true.mpr ⟨w6,hm,hPw⟩,?_⟩
      have hle:=fAIl (fun u=>(l0_14 u&&&18)==18) l0_14 hm hPw
      rw [h6w] at hle;exact hle.symm.trans hi18_sup
    rw [mAOW] at hw6
    rcases hw6 with hm | rfl | ⟨x,hx,rfl⟩
    · exact (hw6_notS hm).elim
    · refine ⟨by rw [h6w];decide,?_,fun _=>h6w⟩
      exact f32s1F.1 ⟨i18,hi18_lt⟩ ⟨l0_14 o,ho0_lt⟩ hi18_sup (show (l0_14 o&&&18)=18 by rw [h6w];decide) (Or.inl h6w)
    · rw [l0_14_and] at h6w
      have hx_lt : l0_14 x < 32:=l0_14_lt (hV x hx).1
      have ⟨hx18,ho18⟩:=f32s2A.2.2.2 ⟨l0_14 x,hx_lt⟩ ⟨l0_14 o,ho0_lt⟩ |>.1 h6w
      have hPx : ((l0_14 x&&&18)==18)=true:=beq_iff_eq.mpr hx18
      have hs6t : s6=true:=List.any_eq_true.mpr ⟨x,hx,hPx⟩
      have hle:=fAIl (fun u=>(l0_14 u&&&18)==18) l0_14 hx hPx
      have hmo:=bit_step1_mono hle h6w hi18_sup
      refine ⟨ho18,f32s1F.1 ⟨i18,hi18_lt⟩ ⟨l0_14 o,ho0_lt⟩ hi18_sup ho18 (Or.inr hmo),
        fun hf=>by rw [hs6t] at hf;cases hf⟩
  have h12_info : ¬ (s7=true ∧ i12=12) →
      (l0_14 o&&&12)=12 ∧ (l0_14 o&&&(i12&&&(31^^^12)))=0 ∧ (s7=false → l0_14 o=12):=by
    intro hnh7
    have hw7_notS : w7 ∉ S:=by
      intro hm;apply hnh7
      have hPw : ((l0_14 w7&&&12)==12)=true:=by rw [h7w];decide
      refine ⟨List.any_eq_true.mpr ⟨w7,hm,hPw⟩,?_⟩
      have hle:=fAIl (fun u=>(l0_14 u&&&12)==12) l0_14 hm hPw
      rw [h7w] at hle;exact hle.symm.trans hi12_sup
    rw [mAOW] at hw7
    rcases hw7 with hm | rfl | ⟨x,hx,rfl⟩
    · exact (hw7_notS hm).elim
    · refine ⟨by rw [h7w];decide,?_,fun _=>h7w⟩
      exact f32s1F.2.1 ⟨i12,hi12_lt⟩ ⟨l0_14 o,ho0_lt⟩ hi12_sup (show (l0_14 o&&&12)=12 by rw [h7w];decide) (Or.inl h7w)
    · rw [l0_14_and] at h7w
      have hx_lt : l0_14 x < 32:=l0_14_lt (hV x hx).1
      have ⟨hx12,ho12⟩:=f32s2A.2.2.2 ⟨l0_14 x,hx_lt⟩ ⟨l0_14 o,ho0_lt⟩ |>.2 h7w
      have hPx : ((l0_14 x&&&12)==12)=true:=beq_iff_eq.mpr hx12
      have hs7t : s7=true:=List.any_eq_true.mpr ⟨x,hx,hPx⟩
      have hle:=fAIl (fun u=>(l0_14 u&&&12)==12) l0_14 hx hPx
      have hmo:=bit_step1_mono hle h7w hi12_sup
      refine ⟨ho12,f32s1F.2.1 ⟨i12,hi12_lt⟩ ⟨l0_14 o,ho0_lt⟩ hi12_sup ho12 (Or.inr hmo),
        fun hf=>by rw [hs7t] at hf;cases hf⟩
  have h20_info : ¬ (s3=true ∧ i20=20) → (l0_14 o&&&(i20&&&(31^^^20)))=0:=by
    intro hnh3
    have hw3_notS : w3 ∉ S:=by
      intro hm;apply hnh3
      have hPw : ((l1_14 w3&&&20)==20)=true:=by rw [h3w];decide
      refine ⟨List.any_eq_true.mpr ⟨w3,hm,by rw [h3w];decide⟩,?_⟩
      have hle:=fAIl (fun u=>(l1_14 u&&&20)==20) l1_14 hm hPw
      rw [h3w] at hle;exact hle.symm.trans hi20_sup
    have hf1 : (l1_14 o&&&(i20&&&(31^^^20)))=0:=by
      rw [mAOW] at hw3
      rcases hw3 with hm | rfl | ⟨x,hx,rfl⟩
      · exact (hw3_notS hm).elim
      · exact f32s1F.2.2 ⟨i20,hi20_lt⟩ ⟨l1_14 o,ho1_lt⟩ hi20_sup (show (l1_14 o&&&20)=20 by rw [h3w];decide) (Or.inl h3w)
      · rw [l1_14_and] at h3w
        have hx_lt : l1_14 x < 32:=l1_14_lt x
        have hx20:=(f32s2A.2.1 ⟨l1_14 x,hx_lt⟩ ⟨l1_14 o,ho1_lt⟩ h3w).1
        have ho20:=(f32s2A.2.1 ⟨l1_14 o,ho1_lt⟩ ⟨l1_14 x,hx_lt⟩ (by rw [bac];exact h3w)).1
        have hPx : ((l1_14 x&&&20)==20)=true:=beq_iff_eq.mpr hx20
        have hle:=fAIl (fun u=>(l1_14 u&&&20)==20) l1_14 hx hPx
        have hmo:=bit_step1_mono hle h3w hi20_sup
        exact f32s1F.2.2 ⟨i20,hi20_lt⟩ ⟨l1_14 o,ho1_lt⟩ hi20_sup ho20 (Or.inr hmo)
    exact bit_mono_zero hoV.2 hf1
  have hZ_info : ¬ (sZ=true ∧ ie15=0) →
      (l0_14 o&&&ie15)=0 ∧ (sZ=false → cZ0 S=true ∧ cE15 S=true):=by
    intro hnhZ
    have hwZ_notS : wZ ∉ S:=by
      intro hm;apply hnhZ
      have hPw : (e4_14 wZ==15)=true:=beq_iff_eq.mpr hZe
      refine ⟨List.any_eq_true.mpr ⟨wZ,hm,hPw⟩,?_⟩
      have hle:=fAIl (fun u=>e4_14 u==15) l0_14 hm hPw
      rw [hZ0,ba0r] at hle;exact hle.symm
    rw [mAOW] at hwZ
    rcases hwZ with hm | rfl | ⟨x,hx,rfl⟩
    · exact (hwZ_notS hm).elim
    · refine ⟨by rw [hZ0,ba0l],fun _=>?_⟩
      have ha0 : l0_14 a=0 ∧ l0_14 b=0:=by
        rw [l0_14_or] at hZ0
        have:=bit_sub_of_or_zero (c:=31) (by rw [hZ0,ba0l])
        have h31a:=(by decide : ∀ x : Fin 32,(x.val&&&31)=x.val) ⟨l0_14 a,l0_14_lt (hV a ha).1⟩
        have h31b:=(by decide : ∀ x : Fin 32,(x.val&&&31)=x.val) ⟨l0_14 b,l0_14_lt (hV b hb).1⟩
        exact ⟨h31a.symm.trans this.1,h31b.symm.trans this.2⟩
      rw [e4_14_or] at hZe
      constructor
      · unfold cZ0
        rw [List.any_eq_true]
        refine ⟨a,List.mem_filter.mpr ⟨ha,beq_iff_eq.mpr ha0.1⟩,
          List.any_eq_true.mpr ⟨b,List.mem_filter.mpr ⟨hb,beq_iff_eq.mpr ha0.2⟩,beq_iff_eq.mpr hZe⟩⟩
      · unfold cE15
        rw [List.any_eq_true]
        exact ⟨a,ha,List.any_eq_true.mpr ⟨b,hb,beq_iff_eq.mpr hZe⟩⟩
    · rw [e4_14_and] at hZe;rw [l0_14_and] at hZ0
      have ⟨hxe,_⟩:=(by decide : ∀ x y : Fin 16,(x.val&&&y.val=15) ↔ (x.val=15 ∧ y.val=15))
        ⟨e4_14 x,e4_14_lt x⟩ ⟨e4_14 o,e4_14_lt o⟩ |>.mp hZe
      have hPx : (e4_14 x==15)=true:=beq_iff_eq.mpr hxe
      have hsZt : sZ=true:=List.any_eq_true.mpr ⟨x,hx,hPx⟩
      have hle:=fAIl (fun u=>e4_14 u==15) l0_14 hx hPx
      have hmo:=bit_step1_mono0 hle hZ0
      exact ⟨by rw [bac];exact hmo,fun hf=>by rw [hsZt] at hf;cases hf⟩
  set h6:=s6&&(i18==18)
  set h7:=s7&&(i12==12)
  set h3:=s3&&(i20==20)
  set hZ:=sZ&&(ie15==0)
  by_cases hall : h6&&h7&&h3&&hZ
  · have hb0 : lb14B (i18,i12,i20,ie15,s6,s7,s3,sZ)=0:=by unfold lb14B;dsimp only;rw [if_pos hall]
    dsimp only;rw [hb0];simp
  · have hreq : (l0_14 o&&&((if !h6 then 18 else 0)|||(if !h7 then 12 else 0))) =
        ((if !h6 then 18 else 0)|||(if !h7 then 12 else 0)):=by
      rw [baodl];congr 1
      · cases hh6 : h6
        · simp only [Bool.not_false,↓reduceIte];exact (h18_info (fun ⟨x,y⟩=>by simp [h6,x,y] at hh6)).1
        · simp [ba0r]
      · cases hh7 : h7
        · simp only [Bool.not_false,↓reduceIte];exact (h12_info (fun ⟨x,y⟩=>by simp [h7,x,y] at hh7)).1
        · simp [ba0r]
    have hf0 : (l0_14 o&&&(((if !h6 then i18&&&(31^^^18) else 0) |||
        (if !h7 then i12&&&(31^^^12) else 0))|||(if !hZ then ie15 else 0)))=0:=by
      rw [baodl,baodl]
      have p1 : (l0_14 o&&&(if !h6 then i18&&&(31^^^18) else 0))=0:=by
        cases hh6 : h6
        · simp only [Bool.not_false,↓reduceIte];exact (h18_info (fun ⟨x,y⟩=>by simp [h6,x,y] at hh6)).2.1
        · simp [ba0r]
      have p2 : (l0_14 o&&&(if !h7 then i12&&&(31^^^12) else 0))=0:=by
        cases hh7 : h7
        · simp only [Bool.not_false,↓reduceIte];exact (h12_info (fun ⟨x,y⟩=>by simp [h7,x,y] at hh7)).2.1
        · simp [ba0r]
      have p3 : (l0_14 o&&&(if !hZ then ie15 else 0))=0:=by
        cases hhZ : hZ
        · simp only [Bool.not_false,↓reduceIte];exact (hZ_info (fun ⟨x,y⟩=>by simp [hZ,x,y] at hhZ)).1
        · simp [ba0r]
      rw [p1,p2,p3,bo0l,bo0l]
    have hf1 : (l0_14 o&&&(if !h3 then i20&&&(31^^^20) else 0))=0:=by
      cases hh3 : h3
      · simp only [Bool.not_false,↓reduceIte];exact h20_info (fun ⟨x,y⟩=>by simp [h3,x,y] at hh3)
      · simp [ba0r]
    have hdisj:=bit_req_forb hreq hf0 hf1
    have hb0 : lb14B (i18,i12,i20,ie15,s6,s7,s3,sZ)=1:=by
      unfold lb14B;dsimp only;rw [if_neg hall]
      change (if (((if !h6 then 18 else 0)|||(if !h7 then 12 else 0)) &&&
          ((((if !h6 then i18&&&(31^^^18) else 0)|||(if !h7 then i12&&&(31^^^12) else 0)) |||
            (if !hZ then ie15 else 0))|||(if !h3 then i20&&&(31^^^20) else 0))) != 0 then 2 else 1)=1
      rw [hdisj];rfl
    have hnot_z0 : (decide (1 < 2)&&!hZ&&!sZ&&!cZ0 S)=false:=by
      cases hhZ : hZ<;>cases hsZf : sZ<;>cases hnc : cZ0 S<;>try rfl
      exfalso;have:=(hZ_info (fun ⟨x,y⟩=>by simp [hZ,x,y] at hhZ)).2 hsZf |>.1;rw [hnc] at this;cases this
    have hnot_67 : (!s6&&!s7&&!s3&&!cS14 S)=false:=by
      cases hf6 : s6<;>cases hf7 : s7<;>try rfl
      exfalso
      have e18:=(h18_info (fun ⟨x,_⟩=>by rw [hf6] at x;cases x)).2.2 hf6
      have e12:=(h12_info (fun ⟨x,_⟩=>by rw [hf7] at x;cases x)).2.2 hf7
      omega
    have hnot_e15 : ∀ c : Bool,(c&&!cE15 S)=true → (!hZ&&!sZ)=true → False:=by
      intro c hc hzs
      simp only [Bool.and_eq_true,Bool.not_eq_true'] at hc hzs
      have:=(hZ_info (fun ⟨x,y⟩=>by simp [hZ,x,y] at hzs)).2 hzs.2 |>.2
      rw [hc.2] at this;cases this
    dsimp only;rw [hb0]
    simp only [Nat.one_ne_zero,beq_iff_eq,↓reduceIte]
    rw [hnot_z0,hnot_67]
    simp only [Bool.false_eq_true,↓reduceIte]
    by_cases h3' : (decide (1 < 3)&&!hZ&&!sZ)=true
    · rw [if_pos h3']
      by_cases h4' : ((((if !h6 then 18 else 0)|||(if !h7 then 12 else 0)) &&&
          ((if !h6 then i18&&&(31^^^18) else 0)|||(if !h7 then i12&&&(31^^^12) else 0))) != 0 &&
          !cE15 S)=true
      · exfalso
        have hzs : (!hZ&&!sZ)=true:=by simp only [Bool.and_eq_true] at h3' ⊢;exact ⟨h3'.1.2,h3'.2⟩
        exact hnot_e15 _ h4' hzs
      · rw [if_neg h4']
    · rw [if_neg h3']
lemma s2_14 {S : List ℕ} (hV : ∀ w ∈ S,V14 w) (hC : ACl S)
    {a b : ℕ} (ha : a ∈ S) (hb : b ∈ S)
    {c d : ℕ} (hc : c ∈ aOW S (wOr a b)) (hd : d ∈ aOW S (wOr a b))
    (hG : lb14B (st14 (aOW (aOW S (wOr a b)) (wOr c d)))=0) :
    lb14 S ≤ 2:=by
  set o1:=wOr a b
  set S1:=aOW S o1
  set o2:=wOr c d
  set S2:=aOW S1 o2
  have ho1V : V14 o1:=v14o (hV a ha) (hV b hb)
  have hV1 : ∀ w ∈ S1,V14 w:=by
    intro w hw;rw [mAOW] at hw
    rcases hw with hwS | rfl | ⟨x,hx,rfl⟩
    · exact hV w hwS
    · exact ho1V
    · exact v14a (hV x hx) ho1V
  have ho2V : V14 o2:=v14o (hV1 c hc) (hV1 d hd)
  have hV2 : ∀ w ∈ S2,V14 w:=by
    intro w hw;rw [mAOW] at hw
    rcases hw with hw1 | rfl | ⟨x,hx,rfl⟩
    · exact hV1 w hw1
    · exact ho2V
    · exact v14a (hV1 x hx) ho2V
  have hC1 : ACl S1:=acAOW hC o1
  have hC2 : ACl S2:=acAOW hC1 o2
  obtain ⟨⟨w6,hw6,h6w⟩,⟨w7,hw7,h7w⟩,⟨w3,hw3,h3w⟩,⟨wZ,hwZ,hZe,hZ0⟩⟩ :=
    (s14G hV2 hC2).mp hG
  unfold lb14
  rw [stats14_eq]
  set i18:=fAI (fun w=>(l0_14 w&&&18)==18) l0_14 S
  set i12:=fAI (fun w=>(l0_14 w&&&12)==12) l0_14 S
  set i20:=fAI (fun w=>(l1_14 w&&&20)==20) l1_14 S
  set ie15:=fAI (fun w=>e4_14 w==15) l0_14 S
  set s6:=S.any (fun w=>(l0_14 w&&&18)==18)
  set s7:=S.any (fun w=>(l0_14 w&&&12)==12)
  set s3:=S.any (fun w=>(l1_14 w&&&20)==20&&(l1_14 w != 31))
  set sZ:=S.any (fun w=>e4_14 w==15)
  have hb0_le2 : lb14B (i18,i12,i20,ie15,s6,s7,s3,sZ) ≤ 2:=by
    unfold lb14B;dsimp only;split_ifs<;>omega
  have hclA : ¬ (s6=false ∧ s7=false ∧ s3=false ∧ cS14 S=false):=by
    rintro ⟨hf6,hf7,hf3,hncan⟩
    have hno6 : ∀ x ∈ S,(l0_14 x&&&18) ≠ 18:=fun x hx heq=>by
      have : s6=true:=List.any_eq_true.mpr ⟨x,hx,beq_iff_eq.mpr heq⟩;rw [hf6] at this;cases this
    have hno7 : ∀ x ∈ S,(l0_14 x&&&12) ≠ 12:=fun x hx heq=>by
      have : s7=true:=List.any_eq_true.mpr ⟨x,hx,beq_iff_eq.mpr heq⟩;rw [hf7] at this;cases this
    have hno3 : ∀ x ∈ S,(l1_14 x&&&20)=20 → l1_14 x=31:=fun x hx heq=>by
      by_contra hne;have : s3=true:=List.any_eq_true.mpr ⟨x,hx,by simp [heq,hne]⟩;rw [hf3] at this;cases this
    have ho1_0_lt : l0_14 o1 < 32:=l0_14_lt ho1V.1
    have ho2_0_lt : l0_14 o2 < 32:=l0_14_lt ho2V.1
    have ho1_1_lt : l1_14 o1 < 32:=l1_14_lt o1
    have ho2_1_lt : l1_14 o2 < 32:=l1_14_lt o2
    have hcases_S2 : ∀ w ∈ S2,
        (w ∈ S) ∨ (w=o1) ∨ (∃ x ∈ S,w=wAnd x o1) ∨
        (w=o2) ∨ (∃ x ∈ S,w=wAnd x o2) ∨
        (w=wAnd o1 o2) ∨ (∃ x ∈ S,w=wAnd (wAnd x o1) o2):=by
      intro w hw;rw [mAOW] at hw
      rcases hw with hw1 | rfl | ⟨y,hy1,rfl⟩
      · rw [mAOW] at hw1
        rcases hw1 with h | rfl | ⟨x,hx,rfl⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inl ⟨x,hx,rfl⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · rw [mAOW] at hy1
        rcases hy1 with hyS | rfl | ⟨x,hx,rfl⟩
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨y,hyS,rfl⟩))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨x,hx,rfl⟩)))))
    have h6_cases : l0_14 o1=18 ∨ l0_14 o2=18 ∨ (l0_14 o1&&&l0_14 o2)=18:=by
      rcases hcases_S2 w6 hw6 with hx | rfl | ⟨x,hx,rfl⟩ | rfl | ⟨x,hx,rfl⟩ | rfl | ⟨x,hx,rfl⟩
      · exact (hno6 w6 hx (by rw [h6w];decide)).elim
      · exact Or.inl h6w
      · rw [l0_14_and] at h6w
        exact (hno6 x hx (f32s2A.2.2.2 ⟨l0_14 x,l0_14_lt (hV x hx).1⟩ ⟨l0_14 o1,ho1_0_lt⟩ |>.1 h6w).1).elim
      · exact Or.inr (Or.inl h6w)
      · rw [l0_14_and] at h6w
        exact (hno6 x hx (f32s2A.2.2.2 ⟨l0_14 x,l0_14_lt (hV x hx).1⟩ ⟨l0_14 o2,ho2_0_lt⟩ |>.1 h6w).1).elim
      · rw [l0_14_and] at h6w;exact Or.inr (Or.inr h6w)
      · rw [l0_14_and,l0_14_and,baa] at h6w
        have ho12_lt : (l0_14 o1&&&l0_14 o2) < 32:=lt_of_le_of_lt Nat.and_le_left ho1_0_lt
        exact (hno6 x hx (f32s2A.2.2.2 ⟨l0_14 x,l0_14_lt (hV x hx).1⟩ ⟨_,ho12_lt⟩ |>.1 h6w).1).elim
    have h7_cases : l0_14 o1=12 ∨ l0_14 o2=12 ∨ (l0_14 o1&&&l0_14 o2)=12:=by
      rcases hcases_S2 w7 hw7 with hx | rfl | ⟨x,hx,rfl⟩ | rfl | ⟨x,hx,rfl⟩ | rfl | ⟨x,hx,rfl⟩
      · exact (hno7 w7 hx (by rw [h7w];decide)).elim
      · exact Or.inl h7w
      · rw [l0_14_and] at h7w
        exact (hno7 x hx (f32s2A.2.2.2 ⟨l0_14 x,l0_14_lt (hV x hx).1⟩ ⟨l0_14 o1,ho1_0_lt⟩ |>.2 h7w).1).elim
      · exact Or.inr (Or.inl h7w)
      · rw [l0_14_and] at h7w
        exact (hno7 x hx (f32s2A.2.2.2 ⟨l0_14 x,l0_14_lt (hV x hx).1⟩ ⟨l0_14 o2,ho2_0_lt⟩ |>.2 h7w).1).elim
      · rw [l0_14_and] at h7w;exact Or.inr (Or.inr h7w)
      · rw [l0_14_and,l0_14_and,baa] at h7w
        have ho12_lt : (l0_14 o1&&&l0_14 o2) < 32:=lt_of_le_of_lt Nat.and_le_left ho1_0_lt
        exact (hno7 x hx (f32s2A.2.2.2 ⟨l0_14 x,l0_14_lt (hV x hx).1⟩ ⟨_,ho12_lt⟩ |>.2 h7w).1).elim
    have hpair18_12 : (l0_14 o1=18 ∧ l0_14 o2=12) ∨ (l0_14 o1=12 ∧ l0_14 o2=18):=by
      have hdis:=f32s2A.1 ⟨l0_14 o1,ho1_0_lt⟩ ⟨l0_14 o2,ho2_0_lt⟩
      rcases h6_cases with e6 | e6 | e6<;>rcases h7_cases with e7 | e7 | e7
      · omega
      · exact Or.inl ⟨e6,e7⟩
      · exact ((hdis.2 e7).1 e6).elim
      · exact Or.inr ⟨e7,e6⟩
      · omega
      · exact ((hdis.2 e7).2 e6).elim
      · exact ((hdis.1 e6).1 e7).elim
      · exact ((hdis.1 e6).2 e7).elim
      · omega
    have h3_cases : l1_14 o1=20 ∨ l1_14 o2=20 ∨ (l1_14 o1&&&l1_14 o2)=20:=by
      rcases hcases_S2 w3 hw3 with hx | rfl | ⟨x,hx,rfl⟩ | rfl | ⟨x,hx,rfl⟩ | rfl | ⟨x,hx,rfl⟩
      · have:=hno3 w3 hx (by rw [h3w];decide);omega
      · exact Or.inl h3w
      · rw [l1_14_and] at h3w
        have ⟨hx20,h31⟩:=f32s2A.2.1 ⟨l1_14 x,l1_14_lt x⟩ ⟨l1_14 o1,ho1_1_lt⟩ h3w
        exact Or.inl (h31 (hno3 x hx hx20))
      · exact Or.inr (Or.inl h3w)
      · rw [l1_14_and] at h3w
        have ⟨hx20,h31⟩:=f32s2A.2.1 ⟨l1_14 x,l1_14_lt x⟩ ⟨l1_14 o2,ho2_1_lt⟩ h3w
        exact Or.inr (Or.inl (h31 (hno3 x hx hx20)))
      · rw [l1_14_and] at h3w;exact Or.inr (Or.inr h3w)
      · rw [l1_14_and,l1_14_and,baa] at h3w
        have ho12_lt : (l1_14 o1&&&l1_14 o2) < 32:=lt_of_le_of_lt Nat.and_le_left ho1_1_lt
        have ⟨hx20,h31⟩:=f32s2A.2.1 ⟨l1_14 x,l1_14_lt x⟩ ⟨_,ho12_lt⟩ h3w
        exact Or.inr (Or.inr (h31 (hno3 x hx hx20)))
    have ho1_bad : l1_14 o1=31 ∨ (l1_14 o1&&&20) ≠ 20:=by
      by_contra hok;push Not at hok
      have hsup : (l0_14 o1&&&18)=18 ∨ (l0_14 o1&&&12)=12:=by
        rcases hpair18_12 with ⟨e1,_⟩ | ⟨e1,_⟩<;>[left;right]<;>(rw [e1];decide)
      have hcan : cS14 S=true:=by
        unfold cS14;rw [List.any_eq_true]
        refine ⟨a,ha,List.any_eq_true.mpr ⟨b,hb,?_⟩⟩
        dsimp only
        rw [← l0_14_or,← l1_14_or]
        simp only [Bool.and_eq_true,Bool.or_eq_true,bne_iff_ne,beq_iff_eq]
        exact ⟨⟨hok.1,hok.2⟩,hsup⟩
      rw [hncan] at hcan;cases hcan
    have ho2_ne20 : l1_14 o2 ≠ 20:=by
      intro e20
      have hle:=ho2V.2;rw [e20] at hle
      have h2_18_12 : l0_14 o2=18 ∨ l0_14 o2=12:=by rcases hpair18_12 with ⟨_,e⟩ | ⟨_,e⟩<;>[right;left]<;>exact e
      exact f32s2A.2.2.1 ⟨l0_14 o2,ho2_0_lt⟩ h2_18_12 hle
    rcases h3_cases with e1 | e2 | e12
    · rcases ho1_bad with h31 | hne20
      · omega
      · exact hne20 (by rw [e1];decide)
    · exact ho2_ne20 e2
    · have ⟨h1_20,h31⟩:=f32s2A.2.1 ⟨l1_14 o1,ho1_1_lt⟩ ⟨l1_14 o2,ho2_1_lt⟩ e12
      rcases ho1_bad with h1_31 | hne20
      · exact ho2_ne20 (h31 h1_31)
      · exact hne20 h1_20
  set h6:=s6&&(i18==18)
  set h7:=s7&&(i12==12)
  set hZ:=sZ&&(ie15==0)
  have hclB : ¬ (hZ=false ∧ sZ=false ∧ cE15 S=false ∧
      (((if !h6 then 18 else 0)|||(if !h7 then 12 else 0)) &&&
       ((if !h6 then i18&&&(31^^^18) else 0)|||(if !h7 then i12&&&(31^^^12) else 0))) ≠ 0):=by
    rintro ⟨_,hsZf,hnc15,hne0⟩
    have hno15_S : ∀ x ∈ S,e4_14 x ≠ 15:=fun x hx he=>by
      have : sZ=true:=List.any_eq_true.mpr ⟨x,hx,beq_iff_eq.mpr he⟩;rw [hsZf] at this;cases this
    have ho1_ne15 : e4_14 o1 ≠ 15:=fun he=>by
      rw [e4_14_or] at he
      have : cE15 S=true:=List.any_eq_true.mpr ⟨a,ha,List.any_eq_true.mpr ⟨b,hb,beq_iff_eq.mpr he⟩⟩
      rw [hnc15] at this;cases this
    have hno15_S1 : ∀ x ∈ S1,e4_14 x ≠ 15:=by
      intro x hx he;rw [mAOW] at hx
      rcases hx with hxS | rfl | ⟨u,hu,rfl⟩
      · exact hno15_S x hxS he
      · exact ho1_ne15 he
      · rw [e4_14_and] at he
        exact ho1_ne15 ((by decide : ∀ p q : Fin 16,(p.val&&&q.val=15) → q.val=15)
          ⟨e4_14 u,e4_14_lt u⟩ ⟨e4_14 o1,e4_14_lt o1⟩ he)
    have ho2_0 : l0_14 o2=0:=by
      rw [mAOW] at hwZ
      rcases hwZ with hw1 | rfl | ⟨u,hu,rfl⟩
      · exact (hno15_S1 wZ hw1 hZe).elim
      · exact hZ0
      · rw [e4_14_and] at hZe
        exact (hno15_S1 u hu ((by decide : ∀ p q : Fin 16,(p.val&&&q.val=15) → p.val=15)
          ⟨e4_14 u,e4_14_lt u⟩ ⟨e4_14 o2,e4_14_lt o2⟩ hZe)).elim
    have hw6_S1 : w6 ∈ S1:=by
      rw [mAOW] at hw6
      rcases hw6 with hw1 | rfl | ⟨u,_,rfl⟩
      · exact hw1
      · omega
      · rw [l0_14_and,ho2_0,ba0r] at h6w;omega
    have hw7_S1 : w7 ∈ S1:=by
      rw [mAOW] at hw7
      rcases hw7 with hw1 | rfl | ⟨u,_,rfl⟩
      · exact hw1
      · omega
      · rw [l0_14_and,ho2_0,ba0r] at h7w;omega
    have hi18_lt : i18 < 32:=fAIt ..
    have hi12_lt : i12 < 32:=fAIt ..
    have ho1_0_lt : l0_14 o1 < 32:=l0_14_lt ho1V.1
    have hi18_sup : (i18&&&18)=18:=fAIs _ _ (by omega) (fun u _ hu=>beq_iff_eq.mp hu)
    have hi12_sup : (i12&&&12)=12:=fAIs _ _ (by omega) (fun u _ hu=>beq_iff_eq.mp hu)
    have h6_ok : h6=false → (l0_14 o1&&&18)=18 ∧ (l0_14 o1&&&(i18&&&(31^^^18)))=0:=by
      intro hh6
      have hw6_notS : w6 ∉ S:=fun hm=>by
        have hPw : ((l0_14 w6&&&18)==18)=true:=by rw [h6w];decide
        have hs6t : s6=true:=List.any_eq_true.mpr ⟨w6,hm,hPw⟩
        have hle:=fAIl (fun u=>(l0_14 u&&&18)==18) l0_14 hm hPw
        rw [h6w] at hle
        have hi : i18=18:=hle.symm.trans hi18_sup
        simp [h6,hs6t,hi] at hh6
      rw [mAOW] at hw6_S1
      rcases hw6_S1 with hm | rfl | ⟨x,hx,rfl⟩
      · exact (hw6_notS hm).elim
      · exact ⟨by rw [h6w];decide,f32s1F.1 ⟨i18,hi18_lt⟩ ⟨l0_14 o1,ho1_0_lt⟩ hi18_sup (show (l0_14 o1&&&18)=18 by rw [h6w];decide) (Or.inl h6w)⟩
      · rw [l0_14_and] at h6w
        have hx_lt:=l0_14_lt (hV x hx).1
        have ⟨hx18,ho18⟩:=(f32s2A.2.2.2 ⟨l0_14 x,hx_lt⟩ ⟨l0_14 o1,ho1_0_lt⟩).1 h6w
        have hle:=fAIl (fun u=>(l0_14 u&&&18)==18) l0_14 hx (beq_iff_eq.mpr hx18)
        have hmo:=bit_step1_mono hle h6w hi18_sup
        exact ⟨ho18,f32s1F.1 ⟨i18,hi18_lt⟩ ⟨l0_14 o1,ho1_0_lt⟩ hi18_sup ho18 (Or.inr hmo)⟩
    have h7_ok : h7=false → (l0_14 o1&&&12)=12 ∧ (l0_14 o1&&&(i12&&&(31^^^12)))=0:=by
      intro hh7
      have hw7_notS : w7 ∉ S:=fun hm=>by
        have hPw : ((l0_14 w7&&&12)==12)=true:=by rw [h7w];decide
        have hs7t : s7=true:=List.any_eq_true.mpr ⟨w7,hm,hPw⟩
        have hle:=fAIl (fun u=>(l0_14 u&&&12)==12) l0_14 hm hPw
        rw [h7w] at hle
        have hi : i12=12:=hle.symm.trans hi12_sup
        simp [h7,hs7t,hi] at hh7
      rw [mAOW] at hw7_S1
      rcases hw7_S1 with hm | rfl | ⟨x,hx,rfl⟩
      · exact (hw7_notS hm).elim
      · exact ⟨by rw [h7w];decide,f32s1F.2.1 ⟨i12,hi12_lt⟩ ⟨l0_14 o1,ho1_0_lt⟩ hi12_sup (show (l0_14 o1&&&12)=12 by rw [h7w];decide) (Or.inl h7w)⟩
      · rw [l0_14_and] at h7w
        have hx_lt:=l0_14_lt (hV x hx).1
        have ⟨hx12,ho12⟩:=(f32s2A.2.2.2 ⟨l0_14 x,hx_lt⟩ ⟨l0_14 o1,ho1_0_lt⟩).2 h7w
        have hle:=fAIl (fun u=>(l0_14 u&&&12)==12) l0_14 hx (beq_iff_eq.mpr hx12)
        have hmo:=bit_step1_mono hle h7w hi12_sup
        exact ⟨ho12,f32s1F.2.1 ⟨i12,hi12_lt⟩ ⟨l0_14 o1,ho1_0_lt⟩ hi12_sup ho12 (Or.inr hmo)⟩
    have hreq : (l0_14 o1&&&((if !h6 then 18 else 0)|||(if !h7 then 12 else 0))) =
        ((if !h6 then 18 else 0)|||(if !h7 then 12 else 0)):=by
      rw [baodl];congr 1
      · cases hh6 : h6<;>[exact (h6_ok hh6).1;simp [ba0r]]
      · cases hh7 : h7<;>[exact (h7_ok hh7).1;simp [ba0r]]
    have hforb : (l0_14 o1&&&((if !h6 then i18&&&(31^^^18) else 0)|||(if !h7 then i12&&&(31^^^12) else 0)))=0:=by
      rw [baodl]
      have p1 : (l0_14 o1&&&(if !h6 then i18&&&(31^^^18) else 0))=0:=by
        cases hh6 : h6<;>[exact (h6_ok hh6).2;simp [ba0r]]
      have p2 : (l0_14 o1&&&(if !h7 then i12&&&(31^^^12) else 0))=0:=by
        cases hh7 : h7<;>[exact (h7_ok hh7).2;simp [ba0r]]
      rw [p1,p2,bo0l]
    have h0:=bit_req_forb hreq hforb (ba0r _)
    rw [bit_or_zero_right] at h0
    exact hne0 h0
  dsimp only
  by_cases h0 : (lb14B (i18,i12,i20,ie15,s6,s7,s3,sZ)==0)=true
  · rw [if_pos h0];omega
  · rw [if_neg h0]
    set b1:=if (decide (lb14B (i18,i12,i20,ie15,s6,s7,s3,sZ) < 2)&&!hZ&&!sZ&&!cZ0 S)=true then 2 else lb14B (i18,i12,i20,ie15,s6,s7,s3,sZ)
    have hb1_le2 : b1 ≤ 2:=by dsimp [b1];split_ifs<;>omega
    have hA_false : (!s6&&!s7&&!s3&&!cS14 S)=false:=by
      cases hf6 : s6<;>cases hf7 : s7<;>cases hf3 : s3<;>cases hnc : cS14 S<;>try rfl
      exact (hclA ⟨hf6,hf7,hf3,hnc⟩).elim
    rw [hA_false];simp only [Bool.false_eq_true,↓reduceIte]
    by_cases h3' : (decide (b1 < 3)&&!hZ&&!sZ)=true
    · rw [if_pos h3']
      by_cases h4' : ((((if !h6 then 18 else 0)|||(if !h7 then 12 else 0)) &&&
          ((if !h6 then i18&&&(31^^^18) else 0)|||(if !h7 then i12&&&(31^^^12) else 0))) != 0 &&
          !cE15 S)=true
      · exfalso
        simp only [Bool.and_eq_true,bne_iff_ne] at h3' h4'
        exact hclB ⟨by simpa using h3'.1.2,by simpa using h3'.2,by simpa using h4'.2,h4'.1⟩
      · rw [if_neg h4'];exact hb1_le2
    · rw [if_neg h3'];exact hb1_le2
lemma lb14R : ∀ k S,(∀ w ∈ S,V14 w) → ACl S → Reach14 k S → lb14 S ≤ k:=by
  intro k
  match k with
  | 0 =>
    intro S _ _ h0
    unfold lb14;dsimp only;simp only [Reach14] at h0;rw [h0];simp
  | 1 =>
    intro S hV hC hr
    rcases hr with h0 | ⟨a,ha,b,hb,h0⟩
    · unfold lb14;dsimp only;simp only [Reach14] at h0;rw [h0];simp
    · exact s1_14 hV hC ha hb h0
  | 2 =>
    intro S hV hC hr
    rcases hr with hr1 | ⟨a,ha,b,hb,hr1⟩
    · exact (lb14R 1 S hV hC hr1).trans (by omega)
    · rcases hr1 with h0 | ⟨c,hc,d,hd,h0⟩
      · exact (s1_14 hV hC ha hb h0).trans (by omega)
      · exact s2_14 hV hC ha hb hc hd h0
  | k + 3 =>
    intro S _ _ _
    exact (lb14_le_3 S).trans (by omega)
lemma lb14Bl (S : List ℕ) : lb14B (st14 S) ≤ lb14 S:=by
  unfold lb14;dsimp only
  have hle2:=lb14Base_le_2 (st14 S)
  by_cases h0 : (lb14B (st14 S)==0)=true
  · rw [if_pos h0];simp [beq_iff_eq] at h0;omega
  · rw [if_neg h0]
    have hstep : ∀ (c1 c2 c3 c4 : Bool),
        let b1:=if c1 then 2 else lb14B (st14 S)
        let b2:=if c2 then 3 else b1
        lb14B (st14 S) ≤ (if c3 then (if c4 then 3 else b2) else b2):=by
      intro c1 c2 c3 c4;dsimp only;cases c1<;>cases c2<;>cases c3<;>cases c4<;>simp<;>omega
    exact hstep _ _ _ _
lemma sc14s {src dst : List (List ℕ)} {rem : ℕ}
    (hchk : sc14 src (mkB dst) rem=true)
    {S : List ℕ} (hS : S ∈ src) (hP : S.Pairwise (· < ·)) (hV : ∀ w ∈ S,V14 w) (hC : ACl S)
    (hr : Reach14 (rem + 1) S) :
    ∃ S' ∈ dst,S'.Pairwise (· < ·) ∧ (∀ w ∈ S',V14 w) ∧ ACl S' ∧ Reach14 rem S':=by
  have h1:=List.all_eq_true.mp hchk S hS
  simp only [Bool.and_eq_true] at h1
  rcases hr with hr0 | ⟨a,ha,b,hb,hr0⟩
  · have hlb:=lb14R rem S hV hC hr0
    have hmem : mBk (mkB dst) S=true:=by
      rcases Bool.or_eq_true .. |>.mp h1.1 with hgt | hm
      · simp at hgt;omega
      · exact hm
    exact ⟨S,memBucket_spec hmem,hP,hV,hC,hr0⟩
  · set o:=wOr a b
    by_cases hoS : o ∈ S
    · rw [addOrW_of_mem hP hC hoS] at hr0
      have hlb:=lb14R rem S hV hC hr0
      have hmem : mBk (mkB dst) S=true:=by
        rcases Bool.or_eq_true .. |>.mp h1.1 with hgt | hm
        · simp at hgt;omega
        · exact hm
      exact ⟨S,memBucket_spec hmem,hP,hV,hC,hr0⟩
    · have hab : a ≠ b:=fun e=>by subst e;apply hoS;simpa [o,wOr,bos] using ha
      have hpair:=allPairsOk_spec h1.2 ha hb hab
      have hoV : V14 o:=v14o (hV a ha) (hV b hb)
      have hP' : (aOW S o).Pairwise (· < ·):=pwAOW hP o
      have hV' : ∀ w ∈ aOW S o,V14 w:=by
        intro w hw;rw [mAOW] at hw
        rcases hw with hwS | rfl | ⟨x,hx,rfl⟩
        · exact hV w hwS
        · exact hoV
        · exact v14a (hV x hx) hoV
      have hC' : ACl (aOW S o):=acAOW hC o
      have hlb:=lb14R rem (aOW S o) hV' hC' hr0
      have hupd:=uS14e (fun w hw=>(hV w hw).1) hoV.1
      have hfast : ¬ lb14B (uS14 (st14 S) o) > rem:=by
        rw [hupd];have:=lb14Bl (aOW S o);omega
      have hne : S.elem o=false:=by
        cases he : S.elem o
        · rfl
        · exact (hoS (by simpa [List.elem_eq_mem] using he)).elim
      change (if lb14B (uS14 (st14 S) o) > rem then true
          else if S.elem o=true then true
          else if lb14 (aOW S o) > rem then true
          else mBk (mkB dst) (canonW (aOW S o)))=true at hpair
      rw [if_neg hfast,if_neg (by rw [hne];decide),if_neg (by omega)] at hpair
      obtain ⟨hPc,hVc,hCc⟩:=canonW_props hP' hV' hC'
      exact ⟨canonW (aOW S o),memBucket_spec hpair,hPc,hVc,hCc,reach14_canonW hV' hC' hr0⟩
lemma stepCheck14_append {l1 l2 : List (List ℕ)} {dstB : List (List (List ℕ))} {rem : ℕ}
    (h1 : sc14 l1 dstB rem=true) (h2 : sc14 l2 dstB rem=true) :
    sc14 (l1 ++ l2) dstB rem=true:=by
  unfold sc14 at h1 h2 ⊢
  rw [List.all_append,h1,h2];rfl
lemma stepCheck14_P2W : sc14 P2W B3W 1=true:=by
  have hsplit : ∀ (l : List (List ℕ)),
      l=l.take 64 ++ (l.drop 64).take 64 ++ (l.drop 128).take 64 ++ (l.drop 192).take 64 ++
          (l.drop 256).take 64 ++ (l.drop 320).take 64 ++ (l.drop 384).take 64 ++ l.drop 448:=by
    intro l
    have h : ∀ (k : ℕ) (m : List (List ℕ)),m=m.take k ++ m.drop k:=fun k m=>(List.take_append_drop k m).symm
    have hd : ∀ (a b : ℕ) (m : List (List ℕ)),(m.drop a).drop b=m.drop (a + b):=fun a b m=>by rw [List.drop_drop,Nat.add_comm]
    conv_lhs=>rw [h 64 l]
    conv_lhs=>rhs;rw [h 64 (l.drop 64),hd 64 64 l]
    conv_lhs=>rhs;rhs;rw [h 64 (l.drop 128),hd 128 64 l]
    conv_lhs=>rhs;rhs;rhs;rw [h 64 (l.drop 192),hd 192 64 l]
    conv_lhs=>rhs;rhs;rhs;rhs;rw [h 64 (l.drop 256),hd 256 64 l]
    conv_lhs=>rhs;rhs;rhs;rhs;rhs;rw [h 64 (l.drop 320),hd 320 64 l]
    conv_lhs=>rhs;rhs;rhs;rhs;rhs;rhs;rw [h 64 (l.drop 384),hd 384 64 l]
    simp only [List.append_assoc]
  unfold P2W
  conv_lhs=>rw [hsplit gens2]
  simp only [List.map_append]
  exact stepCheck14_append
    (stepCheck14_append (stepCheck14_append (stepCheck14_append (stepCheck14_append (stepCheck14_append
      (stepCheck14_append test_OW4_step3_0 test_OW4_step3_1) test_OW4_step3_2) test_OW4_step3_3)
      test_OW4_step3_4) test_OW4_step3_5) test_OW4_step3_6) test_OW4_step3_7
lemma stepCheck14_P1W : sc14 P1W B2W 2=true:=by
  have hsplit : ∀ (l : List (List ℕ)),
      l=l.take 5 ++ (l.drop 5).take 5 ++ (l.drop 10).take 5 ++ (l.drop 15).take 5 ++
          (l.drop 20).take 5 ++ (l.drop 25).take 5 ++ (l.drop 30).take 5 ++ l.drop 35:=by
    intro l
    have h : ∀ (k : ℕ) (m : List (List ℕ)),m=m.take k ++ m.drop k:=fun k m=>(List.take_append_drop k m).symm
    have hd : ∀ (a b : ℕ) (m : List (List ℕ)),(m.drop a).drop b=m.drop (a + b):=fun a b m=>by rw [List.drop_drop,Nat.add_comm]
    conv_lhs=>rw [h 5 l]
    conv_lhs=>rhs;rw [h 5 (l.drop 5),hd 5 5 l]
    conv_lhs=>rhs;rhs;rw [h 5 (l.drop 10),hd 10 5 l]
    conv_lhs=>rhs;rhs;rhs;rw [h 5 (l.drop 15),hd 15 5 l]
    conv_lhs=>rhs;rhs;rhs;rhs;rw [h 5 (l.drop 20),hd 20 5 l]
    conv_lhs=>rhs;rhs;rhs;rhs;rhs;rw [h 5 (l.drop 25),hd 25 5 l]
    conv_lhs=>rhs;rhs;rhs;rhs;rhs;rhs;rw [h 5 (l.drop 30),hd 30 5 l]
    simp only [List.append_assoc]
  unfold P1W
  conv_lhs=>rw [hsplit gens1]
  simp only [List.map_append]
  exact stepCheck14_append
    (stepCheck14_append (stepCheck14_append (stepCheck14_append (stepCheck14_append (stepCheck14_append
      (stepCheck14_append test_OW4_step2_0 test_OW4_step2_1) test_OW4_step2_2) test_OW4_step2_3)
      test_OW4_step2_4) test_OW4_step2_5) test_OW4_step2_6) test_OW4_step2_7
lemma finalCheck14_P3W : fc14 P3W=true:=by
  have h0:=test_OW4_step4_0
  have h1:=test_OW4_step4_1
  unfold fc14 at h0 h1
  unfold P3W fc14
  conv_lhs=>rw [← List.take_append_drop 64 gens3]
  rw [List.map_append,List.all_append,h0,h1]
  rfl
lemma C0W_props : C0W.Pairwise (· < ·) ∧ (∀ w ∈ C0W,V14 w) ∧ ACl C0W:=by
  unfold V14 ACl
  decide +kernel
lemma kill_OW4 : ¬ Reach14 4 C0W:=by
  intro hr4
  obtain ⟨hP0,hV0,hC0⟩:=C0W_props
  obtain ⟨S1,hS1,hP1,hV1,hC1,hr3⟩:=sc14s test_OW4_step1 (List.mem_singleton_self _) hP0 hV0 hC0 hr4
  obtain ⟨S2,hS2,hP2,hV2,hC2,hr2⟩:=sc14s stepCheck14_P1W hS1 hP1 hV1 hC1 hr3
  obtain ⟨S3,hS3,hP3,hV3,hC3,hr1⟩:=sc14s stepCheck14_P2W hS2 hP2 hV2 hC2 hr2
  have hfin:=List.all_eq_true.mp finalCheck14_P3W S3 hS3
  simp only [Bool.and_eq_true,bne_iff_ne] at hfin
  rcases hr1 with h0 | ⟨a,ha,b,hb,h0⟩
  · exact hfin.1 h0
  · set o:=wOr a b
    by_cases hoS : o ∈ S3
    · rw [addOrW_of_mem hP3 hC3 hoS] at h0
      exact hfin.1 h0
    · have hab : a ≠ b:=fun e=>by subst e;apply hoS;simpa [o,wOr,bos] using ha
      have hpair:=allPairsOk_spec hfin.2 ha hb hab
      rw [bne_iff_ne,uS14e (fun w hw=>(hV3 w hw).1) (v14o (hV3 a ha) (hV3 b hb)).1] at hpair
      exact hpair h0
end B2K
namespace S91
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CP CP.Readers PCT PFG
def fTarget (x : Fin 9 → Bool) : Bool :=
  x 0&&x 1||x 1&&x 2||x 2&&x 3||x 3&&x 4||x 4&&x 0 ||
  x 0&&x 5||x 1&&x 6||x 2&&x 7||x 3&&x 8||x 5&&x 7 ||
  x 6&&x 8||x 8&&x 5
lemma target_eq_fTarget (x : Fin 10 → Bool) :
    F27.target x=fTarget (fun i : Fin 9=>x i.castSucc):=by
  simp [F27.target,fTarget,Bool.or_assoc]
lemma conflictValue_eq_target (x : Fin 10 → Bool) :
    C27.value x=F27.target x:=by
  simp [C27.value,F27.target,Bool.or_assoc]
lemma isNotGate_eq_eval {op : GateOp} (h : op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    isNotGate op=(op.eval [false]&&!op.eval [true]):=by
  rcases h with rfl | rfl | rfl<;>rfl
lemma notGateCount_eq_filter_eval {gs : List Gate} (hok : ∀ g ∈ gs,Ok g) :
    (gs.filter (fun g=>g.op.eval [false]&&!g.op.eval [true])).length=ngC gs:=by
  unfold ngC
  congr 1
  apply List.filter_congr
  intro g hg
  exact (isNotGate_eq_eval (hok g hg).1).symm
lemma notGateCount_eq_opCount (gs : List Gate) :
    ngC gs=opCount isNotGate gs:=by
  simp [ngC,opCount,List.countP_eq_length_filter]
lemma elim_notGateCount (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) :
    ngC (elim n gs acc).2 ≤ ngC acc.2 + ngC gs:=by
  simpa only [notGateCount_eq_opCount] using elim_opCount_le isNotGate n gs acc
lemma drop_core_notGateCount (k : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (hcl : CleanL k (pre ++ g :: post)) (o : ℕ) (S : Stat)
    (hS : ∀ y : Fin k → Bool,StatValid (k + (elim k pre (idStats k,[])).2.length) S ∧
      statVal (wiresFrom (elim k pre (idStats k,[])).2 (List.ofFn y)) S
        = vl (pre ++ g :: post) y (k + pre.length))
    (hnc : ∃ y y' : Fin k → Bool,vl (pre ++ g :: post) y o ≠ vl (pre ++ g :: post) y' o) :
    ∃ gs' o',CleanL k gs' ∧ gs'.length + 1 ≤ (pre ++ g :: post).length ∧
      nnC gs' ≤ nnC pre + nnC post ∧
      ngC gs' ≤ ngC pre + ngC post ∧
      ∀ y : Fin k → Bool,vl gs' y o' = vl (pre ++ g :: post) y o:=by
  have hokpre : ∀ g' ∈ pre,Ok g' :=
    fun g' h=>(clean_nok _ _ hcl g' (List.mem_append_left _ h)).1
  have hokpost : ∀ g' ∈ post,Ok g' :=
    fun g' h=>(clean_nok _ _ hcl g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))).1
  have inv1 : ∀ y : Fin k → Bool,Inv k (List.ofFn y) (wiresFrom pre (List.ofFn y))
      (elim k pre (idStats k,[])) :=
    fun y=>inv_elim k _ (by simp) pre _ _ hokpre (inv_id k y)
  have hgv : ∀ y : Fin k → Bool,vl (pre ++ g :: post) y (k + pre.length)
      = g.op.eval (g.inputs.map fun a=>(wiresFrom pre (List.ofFn y)).getD a false):=by
    intro y
    have hidx : (pre ++ g :: post)[pre.length]?=some g:=by simp
    rw [vl_gate _ hcl y pre.length g hidx]
    congr 1
    apply List.map_congr_left
    intro a ha
    have hlt:=(hcl pre.length g hidx).lt a ha
    show (wiresFrom (pre ++ g :: post) (List.ofFn y)).getD a false
      = (wiresFrom pre (List.ofFn y)).getD a false
    rw [wiresFrom_append,getD_wiresFrom (g :: post) (wiresFrom pre (List.ofFn y)) a
      (by rw [length_wiresFrom];simp;omega)]
  have hfull : ∀ y : Fin k → Bool,wiresFrom (pre ++ g :: post) (List.ofFn y)
      = wiresFrom post (wiresFrom pre (List.ofFn y) ++
        [g.op.eval (g.inputs.map fun a=>(wiresFrom pre (List.ofFn y)).getD a false)]):=by
    intro y
    rw [wiresFrom_append];rfl
  have inv2 : ∀ y : Fin k → Bool,Inv k (List.ofFn y)
      (wiresFrom pre (List.ofFn y) ++
        [g.op.eval (g.inputs.map fun a=>(wiresFrom pre (List.ofFn y)).getD a false)])
      ((elim k pre (idStats k,[])).1 ++ [S],(elim k pre (idStats k,[])).2):=by
    intro y
    obtain ⟨hl,hi⟩:=inv1 y
    refine ⟨by simp [hl],?_⟩
    intro a
    show StatValid (k + (elim k pre (idStats k,[])).2.length)
        (((elim k pre (idStats k,[])).1 ++ [S]).getD a (Sum.inl false)) ∧
      statVal (wiresFrom (elim k pre (idStats k,[])).2 (List.ofFn y))
        (((elim k pre (idStats k,[])).1 ++ [S]).getD a (Sum.inl false))=_
    by_cases hal : a=(elim k pre (idStats k,[])).1.length
    · rw [hal,getD_snoc_eq,hl,getD_snoc_eq]
      exact ⟨(hS y).1,by rw [(hS y).2,hgv]⟩
    · rw [getD_snoc_ne _ _ _ _ hal,getD_snoc_ne _ _ _ _ (by omega)]
      exact hi a
  have inv3 : ∀ y : Fin k → Bool,Inv k (List.ofFn y)
      (wiresFrom (pre ++ g :: post) (List.ofFn y))
      (elim k post ((elim k pre (idStats k,[])).1 ++ [S],(elim k pre (idStats k,[])).2)):=by
    intro y
    rw [hfull]
    exact inv_elim k _ (by simp) post _ _ hokpost (inv2 y)
  have hc1 : CleanL k (elim k pre (idStats k,[])).2 :=
    clean_elim k (List.ofFn fun _ : Fin k=>false) (by simp) pre _ _ hokpre (inv_id k _)
      (by intro p g' hp;simp at hp)
  have hc3 : CleanL k
      (elim k post ((elim k pre (idStats k,[])).1 ++ [S],(elim k pre (idStats k,[])).2)).2 :=
    clean_elim k (List.ofFn fun _ : Fin k=>false) (by simp) post _ _ hokpost (inv2 _) hc1
  have hlen : (elim k post ((elim k pre (idStats k,[])).1 ++ [S],
      (elim k pre (idStats k,[])).2)).2.length + 1 ≤ (pre ++ g :: post).length:=by
    have h1:=elim_len k post ((elim k pre (idStats k,[])).1 ++ [S],(elim k pre (idStats k,[])).2)
    have h2:=elim_len k pre (idStats k,[])
    simp only [List.length_append,List.length_cons,List.length_nil] at h1 h2 ⊢
    omega
  have hval : ∀ y : Fin k → Bool,
      statVal (wiresFrom (elim k post ((elim k pre (idStats k,[])).1 ++ [S],
          (elim k pre (idStats k,[])).2)).2 (List.ofFn y))
        ((elim k post ((elim k pre (idStats k,[])).1 ++ [S],
          (elim k pre (idStats k,[])).2)).1.getD o (Sum.inl false))
      = vl (pre ++ g :: post) y o:=fun y=>((inv3 y).2 o).2
  cases hst : (elim k post ((elim k pre (idStats k,[])).1 ++ [S],
      (elim k pre (idStats k,[])).2)).1.getD o (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y,y',hne⟩:=hnc
    apply hne
    rw [← hval y,← hval y',hst]
    rfl
  | inr j =>
    refine ⟨_,j,hc3,hlen,?_,?_,?_⟩
    · exact (elim_nonNotCount k post _).trans (Nat.add_le_add_right
        (by simpa [nnC] using elim_nonNotCount k pre (idStats k,[])) _)
    · exact (elim_notGateCount k post _).trans (Nat.add_le_add_right
        (by simpa [ngC] using elim_notGateCount k pre (idStats k,[])) _)
    · intro y
      have h:=hval y
      rw [hst] at h
      exact h
lemma drop_alias_both (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p j : ℕ) (hp : p < gs.length)
    (hj : j < k + p) (heq : ∀ y : Fin k → Bool,vl gs y (k + p)=vl gs y j)
    (hnc : ∃ y y' : Fin k → Bool,vl gs y o ≠ vl gs y' o) :
    ∃ gs' o',CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧
      nnC gs' ≤ nnC (gs.eraseIdx p) ∧
      ngC gs' ≤ ngC (gs.eraseIdx p) ∧
      ∀ y : Fin k → Bool,vl gs' y o' = vl gs y o:=by
  obtain ⟨g,hg⟩ : ∃ g,gs[p]?=some g:=⟨gs[p],List.getElem?_eq_getElem hp⟩
  obtain ⟨pre,post,rfl,rfl⟩:=split_at gs p g hg
  rw [List.eraseIdx_append_of_length_le le_rfl,Nat.sub_self,List.eraseIdx_cons_zero]
  have h1 : nnC (pre ++ post)=nnC pre + nnC post:=by simp [nnC]
  have h2 : ngC (pre ++ post)=ngC pre + ngC post:=by simp [ngC]
  rw [h1,h2]
  apply drop_core_notGateCount k pre g post hcl o ((elim k pre (idStats k,[])).1.getD j (Sum.inl false))
    ?_ hnc
  intro y
  have hokpre : ∀ g' ∈ pre,Ok g' :=
    fun g' h=>(clean_nok _ _ hcl g' (List.mem_append_left _ h)).1
  have inv1:=inv_elim k (List.ofFn y) (by simp) pre _ _ hokpre (inv_id k y)
  refine ⟨(inv1.2 j).1,?_⟩
  rw [(inv1.2 j).2,heq y]
  show (wiresFrom pre (List.ofFn y)).getD j false
    = (wiresFrom (pre ++ g :: post) (List.ofFn y)).getD j false
  rw [wiresFrom_append,getD_wiresFrom (g :: post) (wiresFrom pre (List.ofFn y)) j
    (by rw [length_wiresFrom];simp;omega)]
lemma drop_dead_mono (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (hmono : ngC gs=0)
    (o p : ℕ) (hp : p < gs.length) (ho : o ≠ k + p) (hno : ∀ q,¬ Reads gs q (k + p))
    (hnc : ∃ y y' : Fin k → Bool,vl gs y o ≠ vl gs y' o) :
    ∃ gs' o',CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧ ngC gs' = 0 ∧
      ∀ y : Fin k → Bool,vl gs' y o' = vl gs y o:=by
  obtain ⟨g,hg⟩ : ∃ g,gs[p]?=some g:=⟨gs[p],List.getElem?_eq_getElem hp⟩
  have hpos : 0 < k + p:=by
    rcases hcl p g hg with ⟨_,j,hj,_⟩ | ⟨_,j,_,hj,_,_⟩<;>omega
  let g0 : Gate:=⟨GateOp.and,[0,0]⟩
  let gs':=gs.set p g0
  have hlen : gs'.length=gs.length:=by simp [gs']
  have hget_p : gs'[p]?=some g0:=by simp [gs',hp]
  have hget_ne : ∀ r,r ≠ p → gs'[r]?=gs[r]?:=by
    intro r hr;simp [gs',Ne.symm hr]
  have hcl' : CleanL k gs':=by
    intro r g' hr'
    by_cases hrp : r=p
    · subst hrp;rw [hget_p] at hr';cases hr'
      exact Or.inr ⟨Or.inl rfl,0,0,hpos,hpos,rfl⟩
    · rw [hget_ne r hrp] at hr';exact hcl r g' hr'
  have hagree : ∀ y : Fin k → Bool,∀ w,w ≠ k + p → vl gs' y w=vl gs y w:=by
    intro y w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw
      by_cases hwk : w < k
      · rw [vl_input gs' y w hwk,vl_input gs y w hwk]
      · obtain ⟨r,rfl⟩ : ∃ r,w=k + r:=⟨w - k,by omega⟩
        have hrp : r ≠ p:=fun e=>hw (by rw [e])
        cases hr : gs[r]? with
        | none =>
          have hl : gs.length ≤ r:=List.getElem?_eq_none_iff.1 hr
          rw [vl_beyond gs' y _ (by omega),vl_beyond gs y _ (by omega)]
        | some g' =>
          have hr' : gs'[r]?=some g':=by rw [hget_ne r hrp];exact hr
          rw [vl_gate gs' hcl' y r g' hr',vl_gate gs hcl y r g' hr]
          congr 1
          apply List.map_congr_left
          intro a ha
          have hlt:=(hcl r g' hr).lt a ha
          exact ih a hlt (fun e=>hno r ⟨g',hr,e ▸ ha⟩)
  have halias : ∀ y : Fin k → Bool,vl gs' y (k + p)=vl gs' y 0:=by
    intro y;rw [vl_gate gs' hcl' y p g0 hget_p];simp [g0,GateOp.eval]
  have hnc' : ∃ y y' : Fin k → Bool,vl gs' y o ≠ vl gs' y' o:=by
    obtain ⟨y,y',h⟩:=hnc
    exact ⟨y,y',by rw [hagree y o ho,hagree y' o ho];exact h⟩
  obtain ⟨gs'',o'',hc'',hl'',_,hnot'',he''⟩ :=
    drop_alias_both k gs' hcl' o p 0 (by omega) hpos halias hnc'
  have hnot_er : ngC (gs'.eraseIdx p) ≤ ngC gs:=by
    rw [show gs'.eraseIdx p=gs.eraseIdx p from List.eraseIdx_set_eq]
    rw [notGateCount_eq_opCount,notGateCount_eq_opCount]
    exact (List.eraseIdx_sublist gs p).countP_le
  exact ⟨gs'',o'',hc'',by omega,by omega,fun y=>by rw [he'' y,hagree y o ho]⟩
def MonoLeast (m : ℕ) (f : (Fin m → Bool) → Bool) (gs : List Gate) (o : ℕ) : Prop :=
  CleanL m gs ∧ ngC gs=0 ∧ (∀ x : Fin m → Bool,vl gs x o=f x) ∧
  (∀ (gs' : List Gate) (o' : ℕ),CleanL m gs' → ngC gs' = 0 →
    (∀ x : Fin m → Bool,vl gs' x o' = f x) → gs.length ≤ gs'.length)
lemma monoLeast_of_clean {n : ℕ} {f : (Fin n → Bool) → Bool} {gs0 : List Gate} {o0 : ℕ}
    (hc0 : CleanL n gs0) (hm0 : ngC gs0=0) (he0 : ∀ x,vl gs0 x o0=f x) :
    ∃ gs o,MonoLeast n f gs o ∧ gs.length ≤ gs0.length:=by
  classical
  let adm (t : ℕ):=∃ gs o,CleanL n gs ∧ ngC gs=0 ∧ (∀ x,vl gs x o=f x) ∧ gs.length=t
  have ex : ∃ t,adm t:=⟨gs0.length,gs0,o0,hc0,hm0,he0,rfl⟩
  obtain ⟨gs,o,hc,hm,he,hl⟩:=Nat.find_spec ex
  refine ⟨gs,o,⟨hc,hm,he,?_⟩,?_⟩
  · intro gs' o' hc' hm' he'
    exact hl.trans_le (Nat.find_min' ex ⟨gs',o',hc',hm',he',rfl⟩)
  · exact hl.trans_le (Nat.find_min' ex ⟨gs0,o0,hc0,hm0,he0,rfl⟩)
lemma monoLeast_live {n o : ℕ} {f : (Fin n → Bool) → Bool} {gs : List Gate}
    (M : MonoLeast n f gs o) (hnc : ∃ x y,f x ≠ f y)
    (dep : ∀ v : Fin n,Dep f v)
    (still : ∀ (v : Fin n) (b : Bool),∃ x y,f (Function.update x v b) ≠ f (Function.update y v b))
    (ho : o < n + gs.length) :
    ∀ w : Fin (n + gs.length),w ≠ ⟨o,ho⟩ → ∃ v,rE gs w v:=by
  intro w hne
  have hne' : w.val ≠ o:=fun e=>hne (Fin.ext e)
  by_cases hw : w.val < n
  · let i : Fin n:=⟨w.val,hw⟩
    have hread : ∃ q,Reads gs q i:=by
      by_contra hno
      have hno' : ∀ g ∈ gs,(i : ℕ) ∉ g.inputs:=by
        intro g hg hi
        obtain ⟨q,hq⟩:=List.mem_iff_getElem?.1 hg
        exact hno ⟨q,g,hq,hi⟩
      have hoi : o ≠ i:=by
        intro e
        obtain ⟨x,y,hxy⟩:=still i false
        apply hxy
        rw [← M.2.2.1,← M.2.2.1,e,vl_input gs _ i i.isLt,vl_input gs _ i i.isLt]
        simp
      obtain ⟨x,hx⟩:=dep i
      apply hx
      rw [← M.2.2.1,← M.2.2.1]
      refine agree_except i gs _ _ hno' (by simp) ?_ o hoi
      intro j hj
      by_cases hjm : j < n
      · rw [show (List.ofFn (Function.update x i (!x i))).getD j false
              = Function.update x i (!x i) ⟨j,hjm⟩ from getD_ofFn n _ false ⟨j,hjm⟩,
            show (List.ofFn x).getD j false=x ⟨j,hjm⟩ from getD_ofFn n x false ⟨j,hjm⟩]
        exact Function.update_of_ne (fun e=>hj (congrArg Fin.val e)) _ _
      · rw [List.getD_eq_default _ _ (by simp;omega),List.getD_eq_default _ _ (by simp;omega)]
    obtain ⟨p,g,hp,hmem⟩:=hread
    have hlt:=(List.getElem?_eq_some_iff.mp hp).1
    exact ⟨⟨n + p,by omega⟩,p,g,hp,rfl,hmem⟩
  · let p:=w.val - n
    have hp : p < gs.length:=by have:=w.isLt;omega
    have hwp : w.val=n + p:=by omega
    have hop : o ≠ n + p:=by omega
    have hread : ∃ q,Reads gs q (n + p):=by
      by_contra hno
      have hno' : ∀ q,¬ Reads gs q (n + p):=fun q hq=>hno ⟨q,hq⟩
      have hncv : ∃ y y' : Fin n → Bool,vl gs y o ≠ vl gs y' o:=by
        obtain ⟨x,y,hxy⟩:=hnc;exact ⟨x,y,by rw [M.2.2.1,M.2.2.1];exact hxy⟩
      obtain ⟨gs',o',hc',hl',hm',he'⟩:=drop_dead_mono n gs M.1 M.2.1 o p hp hop hno' hncv
      have:=M.2.2.2 gs' o' hc' hm' (fun x=>(he' x).trans (M.2.2.1 x))
      omega
    obtain ⟨q,g,hq,hmem⟩:=hread
    have hlt:=(List.getElem?_eq_some_iff.mp hq).1
    exact ⟨⟨n + q,by omega⟩,q,g,hq,rfl,hwp ▸ hmem⟩
lemma monoLeast_nodup {n o : ℕ} {f : (Fin n → Bool) → Bool} {gs : List Gate}
    (M : MonoLeast n f gs o) (hnc : ∃ x y,f x ≠ f y) (b : Fin (n + gs.length)) :
    (prds M.1 b).Nodup:=by
  by_cases h : n ≤ b.val
  · apply List.Nodup.of_map Fin.val
    rw [prdV M.1 b h]
    let p:=b.val - n
    have hp : p < gs.length:=by have:=b.isLt;omega
    let g:=gs[p]'hp
    have hg : gs[p]?=some g:=List.getElem?_eq_getElem hp
    change g.inputs.Nodup
    rcases M.1 p g hg with ⟨_,a,_,hin⟩ | ⟨hop,a,c,ha,_,hin⟩
    · rw [hin];simp
    · suffices a ≠ c by rw [hin];simp [this]
      rintro rfl
      have hncv : ∃ y y' : Fin n → Bool,vl gs y o ≠ vl gs y' o:=by
        obtain ⟨x,y,hxy⟩:=hnc;exact ⟨x,y,by rw [M.2.2.1,M.2.2.1];exact hxy⟩
      have hal : ∀ y : Fin n → Bool,vl gs y (n + p)=vl gs y a:=by
        intro y
        rw [vl_gate gs M.1 y p g hg,hin]
        rcases hop with e | e<;>rw [e]<;>simp [GateOp.eval]
      obtain ⟨gs',o',hc',hl',_,hm',he'⟩:=drop_alias_both n gs M.1 o p a hp ha hal hncv
      have hm_gs : ngC gs=0:=M.2.1
      have hm0 : ngC gs' = 0:=by
        have hs : ngC (gs.eraseIdx p) ≤ ngC gs:=by
          rw [notGateCount_eq_opCount,notGateCount_eq_opCount]
          exact (List.eraseIdx_sublist gs p).countP_le
        omega
      have:=M.2.2.2 gs' o' hc' hm0 (fun x=>(he' x).trans (M.2.2.1 x))
      omega
  · simp [prds,h]
lemma firstInputBoundary_ne_nine {gs : List Gate} (clean : CleanL 10 gs)
    (out : Fin (10 + gs.length))
    (live : ∀ w : Fin (10 + gs.length),w ≠ out → ∃ v,rE gs w v)
    (i : Fin 9) :
    (fIB clean out live i.castSucc).val ≠ 9:=by
  have path:=FBR.fIRP (rE gs) out
    (FBR.fPth (rE gs) out (rOrd clean) live (iW gs i.castSucc))
  change (FBR.first (rE gs) out (rOrd clean) live (iW gs i.castSucc)).val ≠ 9
  rcases Relation.ReflTransGen.cases_tail path with heq | ⟨u,_,edge⟩
  · rw [heq]
    have hi:=i.isLt
    change i.val ≠ 9
    omega
  · obtain ⟨p,g,_,hwire,_⟩:=edge
    omega
theorem nCE9 {K : ℕ} (hK : 1 ≤ K) {gs : List Gate} (clean : CleanL 10 gs)
    (out : Fin (10 + gs.length))
    (live : ∀ w : Fin (10 + gs.length),w ≠ out → ∃ v,rE gs w v)
    (hcard : ((cBW (n:=10) gs).erase ⟨9,by omega⟩).card + 1 ≤ K) :
    ∃ label : Fin 9 → Fin K,
      (∀ i j : Fin 9,label i=label j ↔
        fIB clean out live i.castSucc=fIB clean out live j.castSucc) ∧
      (∀ i : Fin 9,(label i).val=K - 1 ↔ fIB clean out live i.castSucc=out) ∧
      (∀ k : Fin K,∃ code : (Fin 10 → Bool) → Bool,
        (∀ x y : Fin 10 → Bool,(∀ i : Fin 9,label i ≤ k → x i.castSucc=y i.castSucc) →
          x 9=y 9 → code x=code y) ∧
        (∀ x y : Fin 10 → Bool,(∀ i : Fin 9,label i ≠ k → x i.castSucc=y i.castSucc) →
          x 9=y 9 → code x=code y → vl gs x out.val=vl gs y out.val)):=by
  classical
  let w9 : Fin (10 + gs.length):=⟨9,by omega⟩
  let cuts:=insert out ((cBW (n:=10) gs).erase w9)
  have small : cuts.card ≤ K:=(Finset.card_insert_le ..).trans hcard
  have hpos : 0 < cuts.card:=Finset.card_pos.mpr ⟨out,Finset.mem_insert_self ..⟩
  let boundary:=fIB clean out live
  have mem (i : Fin 9) : boundary i.castSucc ∈ cuts:=by
    rcases FBR.first_stops (rE gs) out (rOrd clean) live (iW gs i.castSucc)
      with ho | hb
    · exact Finset.mem_insert.mpr (Or.inl ho)
    · apply Finset.mem_insert.mpr
      right
      refine Finset.mem_erase.mpr ⟨?_,inCB.mpr hb⟩
      intro heq
      exact firstInputBoundary_ne_nine clean out live i (congrArg Fin.val heq)
  let embed:=(cuts.orderIsoOfFin rfl).symm
  let rank (c : cuts) : Fin K:=⟨K - cuts.card + (embed c).val,by have:=(embed c).isLt;omega⟩
  have strict : StrictMono rank:=by
    intro c d hcd
    have he:=embed.strictMono hcd
    change (embed c).val < (embed d).val at he
    change K - cuts.card + (embed c).val < K - cuts.card + (embed d).val
    omega
  have out_mem : out ∈ cuts:=Finset.mem_insert_self ..
  have out_max : ∀ c : cuts,c ≤ ⟨out,out_mem⟩:=fun c=>wLO clean out live c.val
  have embed_out : (embed ⟨out,out_mem⟩).val=cuts.card - 1:=by
    have hle : (embed ⟨out,out_mem⟩).val ≤ cuts.card - 1:=by
      have:=(embed ⟨out,out_mem⟩).isLt;omega
    have hge : cuts.card - 1 ≤ (embed ⟨out,out_mem⟩).val:=by
      let last : Fin cuts.card:=⟨cuts.card - 1,by omega⟩
      have h1 : embed.symm last ≤ ⟨out,out_mem⟩:=out_max (embed.symm last)
      have h2 : last ≤ embed ⟨out,out_mem⟩:=by
        simpa using embed.monotone h1
      exact h2
    omega
  have rank_out : (rank ⟨out,out_mem⟩).val=K - 1:=by
    show K - cuts.card + (embed ⟨out,out_mem⟩).val=K - 1
    rw [embed_out];omega
  let loc (i : Fin 9) : cuts:=⟨boundary i.castSucc,mem i⟩
  let label (i : Fin 9):=rank (loc i)
  have eqv (i j : Fin 9) : label i=label j ↔ boundary i.castSucc=boundary j.castSucc:=by
    change rank (loc i)=rank (loc j) ↔ (loc i).val=(loc j).val
    rw [strict.injective.eq_iff,Subtype.ext_iff]
  have atOut (i : Fin 9) : (label i).val=K - 1 ↔ boundary i.castSucc=out:=by
    constructor
    · intro hv
      have hr : rank (loc i)=rank ⟨out,out_mem⟩:=Fin.ext (hv.trans rank_out.symm)
      exact congrArg Subtype.val (strict.injective hr)
    · intro hb
      have hl : loc i=⟨out,out_mem⟩:=Subtype.ext hb
      show (rank (loc i)).val=K - 1
      rw [hl,rank_out]
  refine ⟨label,eqv,atOut,?_⟩
  intro k
  by_cases used : ∃ z : Fin 9,label z=k
  · obtain ⟨z,rfl⟩:=used
    let c:=boundary z.castSucc
    have term : FBR.Terminal (rE gs) out c :=
      FBR.first_stops (rE gs) out (rOrd clean) live (iW gs z.castSucc)
    refine ⟨fun x=>vl gs x c.val,?_,?_⟩
    · intro x y hxy h9
      apply aoIA clean
      intro i path
      by_cases hi9 : i.val < 9
      · let i9 : Fin 9:=⟨i.val,hi9⟩
        have hcast : i9.castSucc=i:=Fin.ext rfl
        rw [← hcast]
        apply hxy i9
        apply strict.monotone
        show loc i9 ≤ loc z
        exact FBR.ancestor_first_le (rE gs) out (rOrd clean) live
          (hcast ▸ path) term
      · have hi : i=9:=Fin.ext (by omega)
        subst hi;exact h9
    · intro x y hxy h9 heq
      have blocked:=fIGc clean out live c
      rcases blocked with hOut | apart
      · simpa only [hOut] using heq
      · apply cca clean c out x y heq
        intro i hi
        by_cases hi9 : i.val < 9
        · let i9 : Fin 9:=⟨i.val,hi9⟩
          have hcast : i9.castSucc=i:=Fin.ext rfl
          rw [← hcast]
          apply apart i9.castSucc
          apply (mem_firstInputGroup clean out live c i9.castSucc).mpr
          exact (eqv i9 z).mp (by_contra fun ne=>hi (by simpa [hcast] using hxy i9 ne))
        · have hi' : i=9:=Fin.ext (by omega)
          exact (hi (hi' ▸ h9)).elim
  · refine ⟨fun _=>false,fun _ _ _ _=>rfl,?_⟩
    intro x y hxy h9 _
    have hfun : x=y:=funext fun i=>by
      by_cases hi9 : i.val < 9
      · let i9 : Fin 9:=⟨i.val,hi9⟩
        have hcast : i9.castSucc=i:=Fin.ext rfl
        rw [← hcast]
        exact hxy i9 (fun h=>used ⟨i9,h⟩)
      · have hi' : i=9:=Fin.ext (by omega)
        subst hi';exact h9
    rw [hfun]
def CutK (K : ℕ) (label : Fin 9 → Fin K) (t : Fin K) : Prop :=
  ∃ code : (Fin 10 → Bool) → Bool,
    (∀ x y : Fin 10 → Bool,(∀ i : Fin 9,label i ≤ t → x i.castSucc=y i.castSucc) →
      x 9=y 9 → code x=code y) ∧
    (∀ x y : Fin 10 → Bool,F27.valid x → F27.valid y →
      (∀ i : Fin 9,label i ≠ t → x i.castSucc=y i.castSucc) →
      x 9=y 9 → code x=code y → F27.target x=F27.target y)
lemma cubeBoundK {K : ℕ} (label : Fin 9 → Fin K) (cut : ∀ t : Fin K,CutK K label t)
    (i j k : Fin 9) (a b c : ℕ) (hw : F27.cube i.castSucc j.castSucc k.castSucc a b c) :
    label i=label j → label k ≤ label i:=by
  intro hh
  by_contra hle
  have hlt : label i < label k:=lt_of_not_ge hle
  obtain ⟨code,low,high⟩:=cut (label i)
  obtain ⟨same,va,vb,vha,vhb,vhc,nab,nac,nbc⟩:=hw
  let hi (m : ℕ):=Function.update (F27.row m) k.castSucc true
  have hk9 : (9 : Fin 10) ≠ k.castSucc:=fun e=>Fin.castSucc_ne_last k e.symm
  have hi9 (m : ℕ) : hi m 9=F27.row m 9:=Function.update_of_ne hk9 _ _
  have aux (m : ℕ) : code (hi m)=code (F27.row m):=by
    apply low
    · intro u hu
      have hne : u.castSucc ≠ k.castSucc:=fun e=>by
        have huk : u=k:=Fin.castSucc_injective 9 e
        subst huk
        exact (not_le_of_gt hlt) hu
      exact Function.update_of_ne hne _ _
    · exact hi9 m
  have off {u : Fin 9} (h : label u ≠ label i) : u.castSucc ≠ i.castSucc ∧ u.castSucc ≠ j.castSucc:=by
    constructor
    · intro e;exact h (by rw [Fin.castSucc_injective 9 e])
    · intro e;exact h (by rw [Fin.castSucc_injective 9 e,hh])
  have s9 : F27.row a 9=F27.row b 9 ∧ F27.row b 9=F27.row c 9 :=
    same 9 (fun e=>Fin.castSucc_ne_last i e.symm) (fun e=>Fin.castSucc_ne_last j e.symm)
  have hab : code (F27.row a) ≠ code (F27.row b):=fun e =>
    nab (high _ _ va vb (fun u hu=>(same u.castSucc (off hu).1 (off hu).2).1) s9.1 e)
  have lift {m n : ℕ} (h : ∀ u : Fin 9,label u ≠ label i → F27.row m u.castSucc=F27.row n u.castSucc) :
      ∀ u : Fin 9,label u ≠ label i → hi m u.castSucc=hi n u.castSucc:=by
    intro u hu
    by_cases eq : u=k
    · subst u;simp [hi]
    · have eq' : u.castSucc ≠ k.castSucc:=fun e=>eq (Fin.castSucc_injective 9 e)
      simpa [hi,Function.update_of_ne eq'] using h u hu
  have hac : code (F27.row a) ≠ code (F27.row c):=fun e =>
    nac (high _ _ vha vhc
      (lift (fun u hu=>((same u.castSucc (off hu).1 (off hu).2).1).trans (same u.castSucc (off hu).1 (off hu).2).2))
      ((hi9 a).trans (s9.1.trans (s9.2.trans (hi9 c).symm)))
      ((aux a).trans (e.trans (aux c).symm)))
  have hbc : code (F27.row b) ≠ code (F27.row c):=fun e =>
    nbc (high _ _ vhb vhc
      (lift (fun u hu=>(same u.castSucc (off hu).1 (off hu).2).2))
      ((hi9 b).trans (s9.2.trans (hi9 c).symm))
      ((aux b).trans (e.trans (aux c).symm)))
  cases ha : code (F27.row a)<;>cases hb : code (F27.row b) <;>
    cases hc : code (F27.row c)<;>simp_all
lemma cube03Check : ∀ p ∈ ([(1,2),(1,8),(5,2),(5,8)] : List (Fin 9 × Fin 9)),
    F27.valid (Function.update (F27.row 513) p.1.castSucc true) ∧
    F27.valid (Function.update (F27.row 520) p.1.castSucc true) ∧
    F27.valid (Function.update (F27.row 521) p.1.castSucc true) ∧
    F27.valid (Function.update (F27.row 513) p.2.castSucc true) ∧
    F27.valid (Function.update (F27.row 521) p.2.castSucc true) ∧
    F27.target (Function.update (F27.row 513) p.1.castSucc true) ≠
      F27.target (Function.update (F27.row 520) p.1.castSucc true) ∧
    F27.target (Function.update (F27.row 520) p.1.castSucc true) ≠
      F27.target (Function.update (F27.row 521) p.1.castSucc true) ∧
    F27.target (Function.update (F27.row 513) p.2.castSucc true) ≠
      F27.target (Function.update (F27.row 521) p.2.castSucc true):=by
  unfold F27.valid
  decide +kernel
lemma cube03Same :
    (∀ u : Fin 10,u ≠ (0 : Fin 9).castSucc → u ≠ (3 : Fin 9).castSucc →
      F27.row 513 u=F27.row 520 u) ∧
    (∀ u : Fin 10,u ≠ (0 : Fin 9).castSucc → u ≠ (3 : Fin 9).castSucc →
      F27.row 520 u=F27.row 521 u) ∧
    (∀ u : Fin 10,u ≠ (0 : Fin 9).castSucc → u ≠ (3 : Fin 9).castSucc →
      F27.row 513 u=F27.row 521 u):=by
  decide +kernel
lemma cubeBound03 {K : ℕ} (label : Fin 9 → Fin K) (cut : ∀ t : Fin K,CutK K label t)
    (k1 k2 : Fin 9)
    (hmem : (k1,k2) ∈ ([(1,2),(1,8),(5,2),(5,8)] : List (Fin 9 × Fin 9)))
    (hh : label 0=label 3) : label k1 ≤ label 0 ∨ label k2 ≤ label 0:=by
  by_contra hboth
  push Not at hboth
  obtain ⟨hlt1,hlt2⟩:=hboth
  obtain ⟨code,low,high⟩:=cut (label 0)
  let ra : Fin 10 → Bool:=F27.row 513
  let rb : Fin 10 → Bool:=F27.row 520
  let rc : Fin 10 → Bool:=F27.row 521
  let h1 (r : Fin 10 → Bool):=Function.update r k1.castSucc true
  let h2 (r : Fin 10 → Bool):=Function.update r k2.castSucc true
  have aux1 (r : Fin 10 → Bool) : code (h1 r)=code r:=by
    apply low
    · intro u hu
      have hne : u.castSucc ≠ k1.castSucc:=fun e =>
        (not_le_of_gt hlt1) (Fin.castSucc_injective 9 e ▸ hu)
      exact Function.update_of_ne hne _ _
    · exact Function.update_of_ne (fun e=>Fin.castSucc_ne_last k1 e.symm) _ _
  have aux2 (r : Fin 10 → Bool) : code (h2 r)=code r:=by
    apply low
    · intro u hu
      have hne : u.castSucc ≠ k2.castSucc:=fun e =>
        (not_le_of_gt hlt2) (Fin.castSucc_injective 9 e ▸ hu)
      exact Function.update_of_ne hne _ _
    · exact Function.update_of_ne (fun e=>Fin.castSucc_ne_last k2 e.symm) _ _
  have same_off (r s : Fin 10 → Bool)
      (hrs : ∀ u : Fin 10,u ≠ (0 : Fin 9).castSucc → u ≠ (3 : Fin 9).castSucc → r u=s u)
      (k : Fin 9) (u : Fin 9) (hu : label u ≠ label 0) :
      Function.update r k.castSucc true u.castSucc=Function.update s k.castSucc true u.castSucc:=by
    by_cases hku : u=k
    · subst hku;simp
    · have hku' : u.castSucc ≠ k.castSucc:=fun e=>hku (Fin.castSucc_injective 9 e)
      rw [Function.update_of_ne hku',Function.update_of_ne hku']
      apply hrs
      · intro e
        have hu0 : u=0:=Fin.castSucc_injective 9 e
        exact hu (hu0 ▸ rfl)
      · intro e
        have hu3 : u=3:=Fin.castSucc_injective 9 e
        exact hu (hu3 ▸ hh.symm)
  obtain ⟨va1,vb1,vc1,va2,vc2,nab1,nbc1,nac2⟩:=cube03Check (k1,k2) hmem
  have h9_1 (r s : Fin 10 → Bool) (hrs : r 9=s 9) (k : Fin 9) :
      Function.update r k.castSucc true 9=Function.update s k.castSucc true 9:=by
    have hk9 : (9 : Fin 10) ≠ k.castSucc:=fun e=>Fin.castSucc_ne_last k e.symm
    rw [Function.update_of_ne hk9,Function.update_of_ne hk9,hrs]
  have hab : code ra ≠ code rb:=fun e =>
    nab1 (high (h1 ra) (h1 rb) va1 vb1 (same_off ra rb cube03Same.1 k1)
      (h9_1 ra rb (cube03Same.1 9 (by decide) (by decide)) k1)
      ((aux1 ra).trans (e.trans (aux1 rb).symm)))
  have hbc : code rb ≠ code rc:=fun e =>
    nbc1 (high (h1 rb) (h1 rc) vb1 vc1 (same_off rb rc cube03Same.2.1 k1)
      (h9_1 rb rc (cube03Same.2.1 9 (by decide) (by decide)) k1)
      ((aux1 rb).trans (e.trans (aux1 rc).symm)))
  have hac : code ra ≠ code rc:=fun e =>
    nac2 (high (h2 ra) (h2 rc) va2 vc2 (same_off ra rc cube03Same.2.2 k2)
      (h9_1 ra rc (cube03Same.2.2 9 (by decide) (by decide)) k2)
      ((aux2 ra).trans (e.trans (aux2 rc).symm)))
  cases hca : code ra<;>cases hcb : code rb<;>cases hcc : code rc<;>simp_all
lemma impossible4 (label : Fin 9 → Fin 4)
    (conf : ∀ i j : Fin 9,(i.castSucc,j.castSucc) ∈ C27.pairs → label i ≠ label j)
    (cut : ∀ t : Fin 4,CutK 4 label t) : False:=by
  let f (i : Fin 9) : BitVec 2:=BitVec.ofFin (label i)
  have inj {i j : Fin 9} (h : f i=f j) : label i=label j:=congrArg BitVec.toFin h
  have hcf (i j : Fin 9) (hm : (i.castSucc,j.castSucc) ∈ C27.pairs) : f i ≠ f j :=
    fun h=>conf i j hm (inj h)
  have hbound (i j k : Fin 9) (a b c : ℕ) (hw : F27.cube i.castSucc j.castSucc k.castSucc a b c) :
      f i=f j → f k ≤ f i:=fun h=>cubeBoundK label cut i j k a b c hw (inj h)
  exact F27.noRanks (f 0) (f 1) (f 2) (f 5) (f 6) (f 7) (f 8)
    (hcf 0 1 (by decide))
    (hcf 1 2 (by decide))
    (hcf 0 5 (by decide))
    (hcf 1 6 (by decide))
    (hcf 2 7 (by decide))
    (hcf 5 7 (by decide))
    (hcf 5 8 (by decide))
    (hcf 6 8 (by decide))
    (hbound 0 2 1 525 521 520 (by unfold F27.cube F27.valid;decide))
    (hbound 0 2 5 525 521 520 (by unfold F27.cube F27.valid;decide))
    (hbound 0 6 1 617 616 552 (by unfold F27.cube F27.valid;decide))
    (hbound 0 7 5 651 650 522 (by unfold F27.cube F27.valid;decide))
    (hbound 0 8 5 777 521 520 (by unfold F27.cube F27.valid;decide))
    (hbound 1 5 0 618 616 584 (by unfold F27.cube F27.valid;decide))
    (hbound 1 7 2 162 34 32 (by unfold F27.cube F27.valid;decide))
    (hbound 1 8 6 262 260 4 (by unfold F27.cube F27.valid;decide))
    (hbound 2 5 7 38 34 2 (by unfold F27.cube F27.valid;decide))
    (hbound 2 6 1 196 192 128 (by unfold F27.cube F27.valid;decide))
    (hbound 2 6 7 324 260 256 (by unfold F27.cube F27.valid;decide))
    (hbound 2 8 6 388 384 128 (by unfold F27.cube F27.valid;decide))
    (hbound 5 6 8 98 34 2 (by unfold F27.cube F27.valid;decide))
    (hbound 6 7 8 196 68 4 (by unfold F27.cube F27.valid;decide))
    (hbound 7 8 2 448 192 64 (by unfold F27.cube F27.valid;decide))
lemma kill_four_cuts {gs : List Gate} (clean : CleanL 10 gs) (out : Fin (10 + gs.length))
    (live : ∀ w : Fin (10 + gs.length),w ≠ out → ∃ v,rE gs w v)
    (distinct : ∀ w,(prds clean w).Nodup)
    (computes : ∀ x : Fin 10 → Bool,F27.valid x → vl gs x out.val=F27.target x)
    (hcard : ((cBW (n:=10) gs).erase ⟨9,by omega⟩).card ≤ 3) : False:=by
  obtain ⟨label,loc,_,codes⟩:=nCE9 (by omega : 1 ≤ 4) clean out live (by omega)
  apply impossible4 label
  · intro i j hm same
    exact C27.bCfl clean out live distinct
      (fun x hx=>(computes x hx).trans (conflictValue_eq_target x).symm)
      (i.castSucc,j.castSucc) hm ((loc i j).mp same)
  · intro t
    obtain ⟨c,low,high⟩:=codes t
    refine ⟨c,low,?_⟩
    intro x y vx vy rest h9 same
    exact (computes x vx).symm.trans ((high x y rest h9 same).trans (computes y vy))
lemma kill_nonNot_le_12 {D : Circuit} (fan : FanInTwo D) (budget : nnC D.gates ≤ 12)
    (agree : ∀ x : Fin 10 → Bool,F27.valid x → circuitFun 10 D x=F27.target x)
    (dep : ∀ i,Dep (circuitFun 10 D) i)
    (still : ∀ (i : Fin 10) (b : Bool),∃ x y : Fin 10 → Bool,
      circuitFun 10 D (Function.update x i b) ≠ circuitFun 10 D (Function.update y i b)) : False:=by
  classical
  have nc:=dep_nc (dep 0)
  obtain ⟨gs,o,least,bound⟩:=least_with_budget D fan (fun _=>rfl) nc
  have valid : o < 10 + gs.length:=by
    by_contra! h
    obtain ⟨x,y,different⟩:=least.ncv nc
    exact different ((vl_beyond gs x o h).trans (vl_beyond gs y o h).symm)
  let out : Fin (10 + gs.length):=⟨o,valid⟩
  have live:=lREL least nc dep still valid
  have branches:=tFOB least.hcl out live (bound.trans budget)
  have herase : ((cBW (n:=10) gs).erase ⟨9,by omega⟩).card ≤ 3 :=
    (Finset.card_erase_le ..).trans branches
  exact kill_four_cuts least.hcl out live (prdN least nc)
    (fun x hx=>(least.hev x).trans (agree x hx)) herase
def k5Ok1 (v0 v1 : Nat) : Bool:=v0 != v1
def k5Ok2 (v0 v1 v2 : Nat) : Bool:=v1 != v2&&(!(v0==v2)||decide (v1 <= v0))
def k5Ok3 (v0 v1 v2 v3 : Nat) : Bool :=
  v2 != v3&&(!(v1==v3)||decide (v2 <= v1)) &&
  (!(v0==v3)||(decide (v1 <= v0)||decide (v2 <= v0)))
def k5Ok5 (v0 v1 v2 v3 v5 : Nat) : Bool :=
  v0 != v5 &&
  (!(v0==v2)||decide (v5 <= v0)) &&
  (!(v1==v5)||decide (v2 <= v1)) &&
  (!(v2==v5)||decide (v3 <= v2)) &&
  (!(v3==v5)||decide (v2 <= v3)) &&
  (!(v0==v3)||(decide (v5 <= v0)||decide (v2 <= v0)))
def k5Ok8 (v0 v1 v2 v3 v5 v8 : Nat) : Bool :=
  v3 != v8&&v5 != v8 &&
  (!(v0==v8)||(decide (v1 <= v0)&&decide (v5 <= v0))) &&
  (!(v1==v3)||decide (v8 <= v1)) &&
  (!(v1==v5)||decide (v8 <= v1)) &&
  (!(v1==v8)||decide (v3 <= v1)) &&
  (!(v2==v8)||decide (v3 <= v2)) &&
  (!(v3==v5)||decide (v8 <= v3)) &&
  (!(v0==v3)||((decide (v1 <= v0)||decide (v8 <= v0))&&(decide (v5 <= v0)||decide (v8 <= v0))))
def k5Ok6 (v0 v1 v2 v3 v5 v8 v6 : Nat) : Bool :=
  v1 != v6&&v8 != v6 &&
  (!(v0==v6)||decide (v1 <= v0)) &&
  (!(v1==v5)||decide (v6 <= v1)) &&
  (!(v1==v8)||decide (v6 <= v1)) &&
  (!(v2==v6)||decide (v1 <= v2)) &&
  (!(v3==v6)||decide (v8 <= v3)) &&
  (!(v5==v6)||decide (v8 <= v5))
def k5Ok7 (v0 v1 v2 v3 v5 v8 v6 v7 : Nat) : Bool :=
  v2 != v7&&v5 != v7 &&
  (!(v0==v7)||decide (v5 <= v0)) &&
  (!(v1==v5)||decide (v7 <= v1)) &&
  (!(v1==v7)||(decide (v2 <= v1)&&decide (v6 <= v1))) &&
  (!(v2==v5)||decide (v7 <= v2)) &&
  (!(v2==v6)||decide (v7 <= v2)) &&
  (!(v2==v8)||decide (v7 <= v2)) &&
  (!(v3==v7)||decide (v2 <= v3)) &&
  (!(v5==v6)||decide (v7 <= v5)) &&
  (!(v6==v7)||(decide (v5 <= v6)&&decide (v8 <= v6))) &&
  (!(v7==v8)||(decide (v5 <= v7)&&decide (v6 <= v7)))
def k5Ok4 (v1 v2 v5 v8 v6 v7 v4 : Nat) : Bool :=
  (!(v1==v4)||decide (v6 <= v1)) &&
  (!(v2==v4)||decide (v7 <= v2)) &&
  (!(v4==v5)||decide (v7 <= v4)) &&
  (!(v4==v8)||decide (v6 <= v4))
def fin5List : List Nat:=[0,1,2,3,4]
def checkK5 : Bool :=
  fin5List.all fun v0 =>
  fin5List.all fun v1=>if !k5Ok1 v0 v1 then true else
  fin5List.all fun v2=>if !k5Ok2 v0 v1 v2 then true else
  fin5List.all fun v3=>if !k5Ok3 v0 v1 v2 v3 then true else
  fin5List.all fun v5=>if !k5Ok5 v0 v1 v2 v3 v5 then true else
  fin5List.all fun v8=>if !k5Ok8 v0 v1 v2 v3 v5 v8 then true else
  fin5List.all fun v6=>if !k5Ok6 v0 v1 v2 v3 v5 v8 v6 then true else
  fin5List.all fun v7=>if !k5Ok7 v0 v1 v2 v3 v5 v8 v6 v7 then true else
  fin5List.all fun v4=>if !k5Ok4 v1 v2 v5 v8 v6 v7 v4 then true else
    (v4==4&&v6==4&&v7==4&&(v0==4||v3==4))
set_option maxHeartbeats 4000000 in
lemma checkK5_true : checkK5=true:=by decide +kernel
lemma mem_fin5List (v : Fin 5) : v.val ∈ fin5List:=by
  fin_cases v<;>decide
lemma bne_of_ne {a b : Fin 5} (h : a ≠ b) : (a.val != b.val)=true:=by
  rw [bne_iff_ne]
  exact fun e=>h (Fin.ext e)
lemma imp_le_bool {a b c : Fin 5} (h : a=b → c ≤ a) :
    (!(a.val==b.val)||decide (c.val ≤ a.val))=true:=by
  by_cases e : a=b
  · have hle : c.val ≤ a.val:=h e
    simp [hle]
  · have hne : a.val ≠ b.val:=fun he=>e (Fin.ext he)
    simp [hne]
lemma imp_and_bool {a b c d : Fin 5} (h1 : a=b → c ≤ a) (h2 : a=b → d ≤ a) :
    (!(a.val==b.val)||(decide (c.val ≤ a.val)&&decide (d.val ≤ a.val)))=true:=by
  by_cases e : a=b
  · have hc : c.val ≤ a.val:=h1 e
    have hd : d.val ≤ a.val:=h2 e
    simp [hc,hd]
  · have hne : a.val ≠ b.val:=fun he=>e (Fin.ext he)
    simp [hne]
lemma imp_or_bool {a b c d : Fin 5} (h : a=b → c ≤ a ∨ d ≤ a) :
    (!(a.val==b.val)||(decide (c.val ≤ a.val)||decide (d.val ≤ a.val)))=true:=by
  by_cases e : a=b
  · rcases h e with hc | hd
    · have hc' : c.val ≤ a.val:=hc;simp [hc']
    · have hd' : d.val ≤ a.val:=hd;simp [hd']
  · have hne : a.val ≠ b.val:=fun he=>e (Fin.ext he)
    simp [hne]
lemma imp_or2_bool {a b c1 d1 c2 d2 : Fin 5}
    (h1 : a=b → c1 ≤ a ∨ d1 ≤ a) (h2 : a=b → c2 ≤ a ∨ d2 ≤ a) :
    (!(a.val==b.val)||((decide (c1.val ≤ a.val)||decide (d1.val ≤ a.val)) &&
      (decide (c2.val ≤ a.val)||decide (d2.val ≤ a.val))))=true:=by
  by_cases e : a=b
  · rcases h1 e with p1 | p2
    · have p1' : c1.val ≤ a.val:=p1
      rcases h2 e with q1 | q2
      · have q1' : c2.val ≤ a.val:=q1;simp [p1',q1']
      · have q2' : d2.val ≤ a.val:=q2;simp [p1',q2']
    · have p2' : d1.val ≤ a.val:=p2
      rcases h2 e with q1 | q2
      · have q1' : c2.val ≤ a.val:=q1;simp [p2',q1']
      · have q2' : d2.val ≤ a.val:=q2;simp [p2',q2']
  · have hne : a.val ≠ b.val:=fun he=>e (Fin.ext he)
    simp [hne]
lemma forced5 (v0 v1 v2 v3 v4 v5 v6 v7 v8 : Fin 5)
    (c01 : v0 ≠ v1) (c12 : v1 ≠ v2) (c23 : v2 ≠ v3) (c05 : v0 ≠ v5)
    (c16 : v1 ≠ v6) (c27 : v2 ≠ v7) (c57 : v5 ≠ v7) (c38 : v3 ≠ v8)
    (c58 : v5 ≠ v8) (c68 : v6 ≠ v8)
    (h03_12 : v0=v3 → v1 ≤ v0 ∨ v2 ≤ v0)
    (h03_18 : v0=v3 → v1 ≤ v0 ∨ v8 ≤ v0)
    (h03_52 : v0=v3 → v5 ≤ v0 ∨ v2 ≤ v0)
    (h03_58 : v0=v3 → v5 ≤ v0 ∨ v8 ≤ v0)
    (h0 : v0=v2 → v1 ≤ v0)
    (h1 : v0=v2 → v5 ≤ v0)
    (h2 : v0=v6 → v1 ≤ v0)
    (h3 : v0=v7 → v5 ≤ v0)
    (h4 : v0=v8 → v1 ≤ v0)
    (h5 : v0=v8 → v5 ≤ v0)
    (h6 : v1=v3 → v2 ≤ v1)
    (h7 : v1=v3 → v8 ≤ v1)
    (h8 : v1=v4 → v6 ≤ v1)
    (h9 : v1=v5 → v2 ≤ v1)
    (h10 : v1=v5 → v6 ≤ v1)
    (h11 : v1=v5 → v7 ≤ v1)
    (h12 : v1=v5 → v8 ≤ v1)
    (h13 : v1=v7 → v2 ≤ v1)
    (h14 : v1=v7 → v6 ≤ v1)
    (h15 : v1=v8 → v3 ≤ v1)
    (h16 : v1=v8 → v6 ≤ v1)
    (h17 : v2=v4 → v7 ≤ v2)
    (h18 : v2=v5 → v3 ≤ v2)
    (h19 : v2=v5 → v7 ≤ v2)
    (h20 : v2=v6 → v1 ≤ v2)
    (h21 : v2=v6 → v7 ≤ v2)
    (h22 : v2=v8 → v3 ≤ v2)
    (h23 : v2=v8 → v7 ≤ v2)
    (h24 : v3=v5 → v2 ≤ v3)
    (h25 : v3=v5 → v8 ≤ v3)
    (h26 : v3=v6 → v8 ≤ v3)
    (h27 : v3=v7 → v2 ≤ v3)
    (h28 : v4=v5 → v7 ≤ v4)
    (h29 : v4=v8 → v6 ≤ v4)
    (h30 : v5=v6 → v7 ≤ v5)
    (h31 : v5=v6 → v8 ≤ v5)
    (h32 : v6=v7 → v5 ≤ v6)
    (h33 : v6=v7 → v8 ≤ v6)
    (h34 : v7=v8 → v5 ≤ v7)
    (h35 : v7=v8 → v6 ≤ v7)
    : v4.val=4 ∧ v6.val=4 ∧ v7.val=4 ∧ (v0.val=4 ∨ v3.val=4):=by
  have hk:=checkK5_true
  unfold checkK5 at hk
  have ok1 : k5Ok1 v0.val v1.val=true:=bne_of_ne c01
  have ok2 : k5Ok2 v0.val v1.val v2.val=true:=by
    simp only [k5Ok2,bne_of_ne c12,imp_le_bool h0,Bool.and_true]
  have ok3 : k5Ok3 v0.val v1.val v2.val v3.val=true:=by
    simp only [k5Ok3,bne_of_ne c23,imp_le_bool h6,imp_or_bool h03_12,Bool.and_true]
  have ok5 : k5Ok5 v0.val v1.val v2.val v3.val v5.val=true:=by
    simp only [k5Ok5,bne_of_ne c05,imp_le_bool h1,imp_le_bool h9,imp_le_bool h18,
      imp_le_bool h24,imp_or_bool h03_52,Bool.and_true]
  have ok8 : k5Ok8 v0.val v1.val v2.val v3.val v5.val v8.val=true:=by
    simp only [k5Ok8,bne_of_ne c38,bne_of_ne c58,imp_and_bool h4 h5,imp_le_bool h7,
      imp_le_bool h12,imp_le_bool h15,imp_le_bool h22,imp_le_bool h25,
      imp_or2_bool h03_18 h03_58,Bool.and_true]
  have ok6 : k5Ok6 v0.val v1.val v2.val v3.val v5.val v8.val v6.val=true:=by
    simp only [k5Ok6,bne_of_ne c16,bne_of_ne c68.symm,imp_le_bool h2,imp_le_bool h10,
      imp_le_bool h16,imp_le_bool h20,imp_le_bool h26,imp_le_bool h31,Bool.and_true]
  have ok7 : k5Ok7 v0.val v1.val v2.val v3.val v5.val v8.val v6.val v7.val=true:=by
    simp only [k5Ok7,bne_of_ne c27,bne_of_ne c57,imp_le_bool h3,imp_le_bool h11,
      imp_and_bool h13 h14,imp_le_bool h19,imp_le_bool h21,imp_le_bool h23,
      imp_le_bool h27,imp_le_bool h30,imp_and_bool h32 h33,imp_and_bool h34 h35,Bool.and_true]
  have ok4 : k5Ok4 v1.val v2.val v5.val v8.val v6.val v7.val v4.val=true:=by
    simp only [k5Ok4,imp_le_bool h8,imp_le_bool h17,imp_le_bool h28,imp_le_bool h29,Bool.and_true]
  have s0:=List.all_eq_true.mp hk v0.val (mem_fin5List v0)
  have s1:=List.all_eq_true.mp s0 v1.val (mem_fin5List v1)
  rw [ok1] at s1;simp only [Bool.not_true,Bool.false_eq_true,↓reduceIte] at s1
  have s2:=List.all_eq_true.mp s1 v2.val (mem_fin5List v2)
  rw [ok2] at s2;simp only [Bool.not_true,Bool.false_eq_true,↓reduceIte] at s2
  have s3:=List.all_eq_true.mp s2 v3.val (mem_fin5List v3)
  rw [ok3] at s3;simp only [Bool.not_true,Bool.false_eq_true,↓reduceIte] at s3
  have s5:=List.all_eq_true.mp s3 v5.val (mem_fin5List v5)
  rw [ok5] at s5;simp only [Bool.not_true,Bool.false_eq_true,↓reduceIte] at s5
  have s8:=List.all_eq_true.mp s5 v8.val (mem_fin5List v8)
  rw [ok8] at s8;simp only [Bool.not_true,Bool.false_eq_true,↓reduceIte] at s8
  have s6:=List.all_eq_true.mp s8 v6.val (mem_fin5List v6)
  rw [ok6] at s6;simp only [Bool.not_true,Bool.false_eq_true,↓reduceIte] at s6
  have s7:=List.all_eq_true.mp s6 v7.val (mem_fin5List v7)
  rw [ok7] at s7;simp only [Bool.not_true,Bool.false_eq_true,↓reduceIte] at s7
  have s4:=List.all_eq_true.mp s7 v4.val (mem_fin5List v4)
  rw [ok4] at s4;simp only [Bool.not_true,Bool.false_eq_true,↓reduceIte,
    Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at s4
  exact ⟨s4.1.1.1,s4.1.1.2,s4.1.2,s4.2⟩
lemma five_cuts_forced {gs : List Gate} (clean : CleanL 10 gs) (out : Fin (10 + gs.length))
    (live : ∀ w : Fin (10 + gs.length),w ≠ out → ∃ v,rE gs w v)
    (distinct : ∀ w,(prds clean w).Nodup)
    (computes : ∀ x : Fin 10 → Bool,F27.valid x → vl gs x out.val=F27.target x)
    (hcard : ((cBW (n:=10) gs).erase ⟨9,by omega⟩).card ≤ 4) :
    fIB clean out live 4=out ∧
    fIB clean out live 6=out ∧
    fIB clean out live 7=out ∧
    (fIB clean out live 0=out ∨ fIB clean out live 3=out):=by
  obtain ⟨label,loc,atOut,codes⟩:=nCE9 (by omega : 1 ≤ 5) clean out live (by omega)
  have hcut : ∀ t : Fin 5,CutK 5 label t:=by
    intro t
    obtain ⟨c,low,high⟩:=codes t
    exact ⟨c,low,fun x y vx vy rest h9 same =>
      (computes x vx).symm.trans ((high x y rest h9 same).trans (computes y vy))⟩
  have hcf (i j : Fin 9) (hm : (i.castSucc,j.castSucc) ∈ C27.pairs) : label i ≠ label j:=by
    intro same
    exact C27.bCfl clean out live distinct
      (fun x hx=>(computes x hx).trans (conflictValue_eq_target x).symm)
      (i.castSucc,j.castSucc) hm ((loc i j).mp same)
  have hbound (i j k : Fin 9) (a b c : ℕ) (hw : F27.cube i.castSucc j.castSucc k.castSucc a b c) :
      label i=label j → label k ≤ label i:=cubeBoundK label hcut i j k a b c hw
  have hf:=forced5 (label 0) (label 1) (label 2) (label 3) (label 4)
    (label 5) (label 6) (label 7) (label 8)
    (hcf 0 1 (by decide)) (hcf 1 2 (by decide)) (hcf 2 3 (by decide)) (hcf 0 5 (by decide))
    (hcf 1 6 (by decide)) (hcf 2 7 (by decide)) (hcf 5 7 (by decide)) (hcf 3 8 (by decide))
    (hcf 5 8 (by decide)) (hcf 6 8 (by decide))
    (cubeBound03 label hcut 1 2 (by decide))
    (cubeBound03 label hcut 1 8 (by decide))
    (cubeBound03 label hcut 5 2 (by decide))
    (cubeBound03 label hcut 5 8 (by decide))
    (hbound 0 2 1 524 521 520 (by unfold F27.cube F27.valid;decide))
    (hbound 0 2 5 524 521 520 (by unfold F27.cube F27.valid;decide))
    (hbound 0 6 1 616 553 552 (by unfold F27.cube F27.valid;decide))
    (hbound 0 7 5 650 523 522 (by unfold F27.cube F27.valid;decide))
    (hbound 0 8 1 776 521 520 (by unfold F27.cube F27.valid;decide))
    (hbound 0 8 5 776 521 520 (by unfold F27.cube F27.valid;decide))
    (hbound 1 3 2 521 515 513 (by unfold F27.cube F27.valid;decide))
    (hbound 1 3 8 521 515 513 (by unfold F27.cube F27.valid;decide))
    (hbound 1 4 6 536 522 520 (by unfold F27.cube F27.valid;decide))
    (hbound 1 5 2 288 258 256 (by unfold F27.cube F27.valid;decide))
    (hbound 1 5 6 160 130 128 (by unfold F27.cube F27.valid;decide))
    (hbound 1 5 7 96 66 64 (by unfold F27.cube F27.valid;decide))
    (hbound 1 5 8 36 6 4 (by unfold F27.cube F27.valid;decide))
    (hbound 1 7 2 160 34 32 (by unfold F27.cube F27.valid;decide))
    (hbound 1 7 6 160 34 32 (by unfold F27.cube F27.valid;decide))
    (hbound 1 8 3 769 515 513 (by unfold F27.cube F27.valid;decide))
    (hbound 1 8 6 260 6 4 (by unfold F27.cube F27.valid;decide))
    (hbound 2 4 7 529 517 513 (by unfold F27.cube F27.valid;decide))
    (hbound 2 5 3 545 517 513 (by unfold F27.cube F27.valid;decide))
    (hbound 2 5 7 34 6 2 (by unfold F27.cube F27.valid;decide))
    (hbound 2 6 1 192 132 128 (by unfold F27.cube F27.valid;decide))
    (hbound 2 6 7 320 260 256 (by unfold F27.cube F27.valid;decide))
    (hbound 2 8 3 833 581 577 (by unfold F27.cube F27.valid;decide))
    (hbound 2 8 7 320 68 64 (by unfold F27.cube F27.valid;decide))
    (hbound 3 5 2 545 521 513 (by unfold F27.cube F27.valid;decide))
    (hbound 3 5 8 545 521 513 (by unfold F27.cube F27.valid;decide))
    (hbound 3 6 8 581 525 517 (by unfold F27.cube F27.valid;decide))
    (hbound 3 7 2 897 777 769 (by unfold F27.cube F27.valid;decide))
    (hbound 4 5 7 552 536 520 (by unfold F27.cube F27.valid;decide))
    (hbound 4 8 6 769 529 513 (by unfold F27.cube F27.valid;decide))
    (hbound 5 6 7 66 34 2 (by unfold F27.cube F27.valid;decide))
    (hbound 5 6 8 66 34 2 (by unfold F27.cube F27.valid;decide))
    (hbound 6 7 5 130 66 2 (by unfold F27.cube F27.valid;decide))
    (hbound 6 7 8 132 68 4 (by unfold F27.cube F27.valid;decide))
    (hbound 7 8 5 260 132 4 (by unfold F27.cube F27.valid;decide))
    (hbound 7 8 6 260 132 4 (by unfold F27.cube F27.valid;decide))
  exact ⟨(atOut 4).mp hf.1,(atOut 6).mp hf.2.1,(atOut 7).mp hf.2.2.1,
    hf.2.2.2.imp (atOut 0).mp (atOut 3).mp⟩
def permNat : ℕ → ℕ
  | 0=>3
  | 1=>2
  | 2=>1
  | 3=>0
  | 4=>4
  | 5=>8
  | 6=>7
  | 7=>6
  | 8=>5
  | 9=>9
  | w=>w
lemma permNat_invol (w : ℕ) : permNat (permNat w)=w:=by
  rcases w with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | w<;>rfl
lemma permNat_lt_ten {w : ℕ} (hw : w < 10) : permNat w < 10:=by
  rcases w with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | w<;>simp [permNat] at hw ⊢<;>omega
lemma permNat_ge_ten {w : ℕ} (hw : 10 ≤ w) : permNat w=w:=by
  rcases w with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | w<;>first | omega | rfl
lemma permNat_lt {w m : ℕ} (hm : 10 ≤ m) (hw : w < m) : permNat w < m:=by
  by_cases h10 : w < 10
  · exact lt_of_lt_of_le (permNat_lt_ten h10) hm
  · rw [permNat_ge_ten (by omega)];exact hw
def permFin10 (i : Fin 10) : Fin 10:=⟨permNat i.val,permNat_lt_ten i.isLt⟩
def permGate (g : Gate) : Gate:=⟨g.op,g.inputs.map permNat⟩
def permGates (gs : List Gate) : List Gate:=gs.map permGate
lemma permGates_len (gs : List Gate) : (permGates gs).length=gs.length:=by
  simp [permGates]
lemma permGates_notGateCount (gs : List Gate) : ngC (permGates gs)=ngC gs:=by
  simp [ngC,permGates,permGate,List.filter_map,Function.comp_def]
lemma permGates_clean {gs : List Gate} (hcl : CleanL 10 gs) : CleanL 10 (permGates gs):=by
  intro p g hg
  simp only [permGates,List.getElem?_map,Option.map_eq_some_iff] at hg
  obtain ⟨g0,hg0,rfl⟩:=hg
  rcases hcl p g0 hg0 with ⟨hop,a,ha,hin⟩ | ⟨hop,a,b,ha,hb,hin⟩
  · left
    exact ⟨hop,permNat a,permNat_lt (by omega) ha,by simp [permGate,hin]⟩
  · right
    exact ⟨hop,permNat a,permNat b,permNat_lt (by omega) ha,permNat_lt (by omega) hb,
      by simp [permGate,hin]⟩
lemma vl_permGates {gs : List Gate} (hcl : CleanL 10 gs) (x : Fin 10 → Bool) (w : ℕ) :
    vl (permGates gs) x w=vl gs (fun i=>x (permFin10 i)) (permNat w):=by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hw10 : w < 10
    · rw [vl_input (permGates gs) x w hw10,vl_input gs _ (permNat w) (permNat_lt_ten hw10)]
      have h1 : permFin10 ⟨permNat w,permNat_lt_ten hw10⟩=⟨w,hw10⟩:=Fin.ext (permNat_invol w)
      rw [h1]
    · rw [permNat_ge_ten (by omega)]
      let p:=w - 10
      have hwp : w=10 + p:=by omega
      cases hp : gs[p]? with
      | none =>
        have hl : gs.length ≤ p:=List.getElem?_eq_none_iff.mp hp
        rw [vl_beyond (permGates gs) x w (by rw [permGates_len];omega),
            vl_beyond gs _ w (by omega)]
      | some g0 =>
        have hp' : (permGates gs)[p]?=some (permGate g0):=by simp [permGates,hp]
        rw [hwp,vl_gate (permGates gs) (permGates_clean hcl) x p (permGate g0) hp',
            vl_gate gs hcl _ p g0 hp]
        congr 1
        simp only [permGate,List.map_map]
        apply List.map_congr_left
        intro a ha
        have hlt : a < 10 + p:=(hcl p g0 hp).lt a ha
        have hlt' : permNat a < 10 + p:=permNat_lt (by omega) hlt
        simpa only [Function.comp_def,permNat_invol] using ih (permNat a) (by omega)
lemma target_permFin10 (x : Fin 10 → Bool) :
    F27.target (fun i=>x (permFin10 i))=F27.target x:=by
  have h : ∀ (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Bool),
      let f : Fin 10 → Bool:=fun i =>
        match i.val with
        | 0=>x0 | 1=>x1 | 2=>x2 | 3=>x3 | 4=>x4
        | 5=>x5 | 6=>x6 | 7=>x7 | 8=>x8 | _=>x9
      F27.target (fun i=>f (permFin10 i))=F27.target f:=by
    decide +kernel
  have hf : x=fun i : Fin 10 =>
      match i.val with
      | 0=>x 0 | 1=>x 1 | 2=>x 2 | 3=>x 3 | 4=>x 4
      | 5=>x 5 | 6=>x 6 | 7=>x 7 | 8=>x 8 | _=>x 9:=by
    funext i;fin_cases i<;>rfl
  conv_lhs=>rw [hf]
  conv_rhs=>rw [hf]
  exact h (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9)
lemma valid_permFin10 (x : Fin 10 → Bool) (hx : F27.valid x) :
    F27.valid (fun i=>x (permFin10 i)):=by
  change x (permFin10 9)=(x (permFin10 0)||x (permFin10 3))
  change x 9=(x 0||x 3) at hx
  have h0 : permFin10 0=3:=by decide
  have h3 : permFin10 3=0:=by decide
  have h9 : permFin10 9=9:=by decide
  rw [h0,h3,h9,Bool.or_comm]
  exact hx
def permWire {gs : List Gate} (w : Fin (10 + gs.length)) : Fin (10 + (permGates gs).length) :=
  ⟨permNat w.val,by rw [permGates_len];exact permNat_lt (by omega) w.isLt⟩
lemma readEdge_permGates {gs : List Gate} (u v : Fin (10 + gs.length)) :
    rE (permGates gs) (permWire u) (permWire v) ↔ rE gs u v:=by
  constructor
  · rintro ⟨p,g,hp,hvw,hu⟩
    simp only [permGates,List.getElem?_map,Option.map_eq_some_iff] at hp
    obtain ⟨g0,hg0,rfl⟩:=hp
    have hv10 : 10 ≤ v.val:=by
      by_contra hlt
      have:=permNat_lt_ten (by omega : v.val < 10)
      change permNat v.val=10 + p at hvw
      omega
    have hveq : v.val=10 + p:=by
      change permNat v.val=10 + p at hvw
      rw [permNat_ge_ten hv10] at hvw
      exact hvw
    simp only [permGate,List.mem_map] at hu
    obtain ⟨a,ha,hau⟩:=hu
    have haeq : a=u.val:=by
      have h1:=congrArg permNat hau
      simpa [permWire,permNat_invol] using h1
    exact ⟨p,g0,hg0,hveq,haeq ▸ ha⟩
  · rintro ⟨p,g0,hg0,hvw,hu⟩
    refine ⟨p,permGate g0,by simp [permGates,hg0],?_,?_⟩
    · change permNat v.val=10 + p
      rw [hvw,permNat_ge_ten (by omega)]
    · simp only [permGate,List.mem_map]
      exact ⟨u.val,hu,rfl⟩
lemma permWire_bij {gs : List Gate} : Function.Bijective (permWire (gs:=gs)):=by
  refine ⟨fun a b h=>Fin.ext ?_,fun b=>?_⟩
  · have:=congrArg (fun x : Fin _=>permNat x.val) h
    simpa [permWire,permNat_invol] using this
  · have hlt : b.val < 10 + gs.length:=by
      have hb:=b.isLt;have hl:=permGates_len gs;omega
    refine ⟨⟨permNat b.val,permNat_lt (by omega) hlt⟩,?_⟩
    exact Fin.ext (permNat_invol b.val)
lemma permGates_nodup {gs : List Gate} (hcl : CleanL 10 gs)
    (hnd : ∀ w,(prds hcl w).Nodup)
    (w : Fin (10 + (permGates gs).length)) : (prds (permGates_clean hcl) w).Nodup:=by
  by_cases h10 : 10 ≤ w.val
  · apply List.Nodup.of_map Fin.val
    rw [prdV (permGates_clean hcl) w h10]
    have hltw : w.val < 10 + gs.length:=by
      have hw:=w.isLt;have hl:=permGates_len gs;omega
    let p:=w.val - 10
    have hp : p < gs.length:=by omega
    have h1 : (permGates gs)[p]'(by rw [permGates_len];exact hp)=permGate (gs[p]'hp):=by
      simp [permGates]
    rw [h1]
    simp only [permGate]
    apply List.Nodup.map (fun a b hab=>by
      have:=congrArg permNat hab;simpa [permNat_invol] using this)
    let w0 : Fin (10 + gs.length):=⟨w.val,hltw⟩
    have hnd0:=hnd w0
    have hndm:=List.Nodup.map Fin.val_injective hnd0
    simpa [prdV hcl w0 h10,w0,p] using hndm
  · simp [prds,h10]
lemma permGates_live {gs : List Gate} (out : Fin (10 + gs.length))
    (live : ∀ w : Fin (10 + gs.length),w ≠ out → ∃ v,rE gs w v) :
    ∀ w : Fin (10 + (permGates gs).length),w ≠ permWire out → ∃ v,rE (permGates gs) w v:=by
  intro w hne
  obtain ⟨u,rfl⟩:=permWire_bij.2 w
  have hu : u ≠ out:=fun e=>hne (e ▸ rfl)
  obtain ⟨v,huv⟩:=live u hu
  exact ⟨permWire v,(readEdge_permGates u v).mpr huv⟩
lemma first_permWire {gs : List Gate} (hcl : CleanL 10 gs) (out : Fin (10 + gs.length))
    (live : ∀ w : Fin (10 + gs.length),w ≠ out → ∃ v,rE gs w v)
    (u : Fin (10 + gs.length))
    (hfirst : FBR.first (rE gs) out (rOrd hcl) live u=out) :
    FBR.first (rE (permGates gs)) (permWire out)
      (rOrd (permGates_clean hcl)) (permGates_live out live) (permWire u)=permWire out:=by
  have path:=FBR.fPth (rE gs) out (rOrd hcl) live u
  rw [hfirst] at path
  have mapPath : ∀ a b,Relation.ReflTransGen (FBR.Follow (rE gs) out) a b →
      Relation.ReflTransGen (FBR.Follow (rE (permGates gs)) (permWire out))
        (permWire a) (permWire b):=by
    intro a b hr
    induction hr with
    | refl=>exact Relation.ReflTransGen.refl
    | tail _ step ih =>
      refine ih.tail ⟨(readEdge_permGates _ _).mpr step.1,?_⟩
      rintro (heq | ⟨x,y,hx,hy,hxy⟩)
      · exact step.2 (Or.inl (permWire_bij.1 heq))
      · obtain ⟨x0,rfl⟩:=permWire_bij.2 x
        obtain ⟨y0,rfl⟩:=permWire_bij.2 y
        exact step.2 (Or.inr ⟨x0,y0,(readEdge_permGates _ _).mp hx,
          (readEdge_permGates _ _).mp hy,fun e=>hxy (e ▸ rfl)⟩)
  exact FBR.boundary_unique (rE (permGates gs)) (permWire out)
    (rOrd (permGates_clean hcl))
    (FBR.first_stops ..) (Or.inl rfl)
    (FBR.fPth ..) (mapPath u out path)
lemma input_ne_target : ∀ i : Fin 10,∃ m : Fin 1024,
    F27.valid (F27.row m.val) ∧
    F27.row m.val i ≠ F27.target (F27.row m.val):=by
  unfold F27.valid
  decide +kernel
lemma out_ge_ten {gs : List Gate} (out : Fin (10 + gs.length))
    (computes : ∀ x : Fin 10 → Bool,F27.valid x → vl gs x out.val=F27.target x) :
    10 ≤ out.val:=by
  by_contra hlt
  have hlt' : out.val < 10:=by omega
  obtain ⟨m,hm,hne⟩:=input_ne_target ⟨out.val,hlt'⟩
  have hc:=computes (F27.row m.val) hm
  rw [vl_input gs _ out.val hlt'] at hc
  exact hne hc
lemma mono_wlog_3467 {gs : List Gate} (hcl : CleanL 10 gs) (hmono : ngC gs=0)
    (hlen : gs.length ≤ 14) (out : Fin (10 + gs.length))
    (live : ∀ w : Fin (10 + gs.length),w ≠ out → ∃ v,rE gs w v)
    (distinct : ∀ w,(prds hcl w).Nodup)
    (computes : ∀ x : Fin 10 → Bool,F27.valid x → vl gs x out.val=F27.target x)
    (hcard : ((cBW (n:=10) gs).erase ⟨9,by omega⟩).card ≤ 4) :
    ∃ (gs' : List Gate) (hcl' : CleanL 10 gs') (out' : Fin (10 + gs'.length))
      (live' : ∀ w : Fin (10 + gs'.length),w ≠ out' → ∃ v,rE gs' w v),
      ngC gs' = 0 ∧ gs'.length ≤ 14 ∧
      (∀ w,(prds hcl' w).Nodup) ∧
      (∀ x : Fin 10 → Bool,F27.valid x → vl gs' x out'.val=F27.target x) ∧
      fIB hcl' out' live' 3=out' ∧
      fIB hcl' out' live' 4=out' ∧
      fIB hcl' out' live' 6=out' ∧
      fIB hcl' out' live' 7=out':=by
  obtain ⟨h4,h6,h7,h0 | h3⟩:=five_cuts_forced hcl out live distinct computes hcard
  · refine ⟨permGates gs,permGates_clean hcl,permWire out,permGates_live out live,
      by rw [permGates_notGateCount,hmono],by rw [permGates_len];exact hlen,
      permGates_nodup hcl distinct,?_,?_,?_,?_,?_⟩
    · intro x hx
      change vl (permGates gs) x (permNat out.val)=F27.target x
      rw [vl_permGates hcl x (permNat out.val),permNat_invol,
          computes _ (valid_permFin10 x hx),target_permFin10]
    · exact first_permWire hcl out live (iW gs 0) h0
    · exact first_permWire hcl out live (iW gs 4) h4
    · exact first_permWire hcl out live (iW gs 7) h7
    · exact first_permWire hcl out live (iW gs 6) h6
  · exact ⟨gs,hcl,out,live,hmono,hlen,distinct,computes,h3,h4,h6,h7⟩
def trimNot (g : Gate) : Gate :=
  match g.op with
  | GateOp.not=>⟨GateOp.not,g.inputs.take 1⟩
  | _=>g
lemma trimNot_op (g : Gate) : (trimNot g).op=g.op:=by
  cases g with
  | mk op ins=>cases op<;>rfl
lemma eval_trimNot_step (g : Gate) (w : List Bool) :
    (trimNot g).op.eval ((trimNot g).inputs.map fun i=>w.getD i false) =
    g.op.eval (g.inputs.map fun i=>w.getD i false):=by
  cases g with
  | mk op ins =>
    cases op with
    | not =>
      cases ins with
      | nil=>rfl
      | cons a rest=>rfl
    | and=>rfl
    | or=>rfl
    | mod m=>rfl
    | maj=>rfl
lemma wiresFrom_trimNot (gs : List Gate) (w : List Bool) :
    wiresFrom (gs.map trimNot) w=wiresFrom gs w:=by
  induction gs generalizing w with
  | nil=>rfl
  | cons g gs ih =>
    simp only [List.map_cons,wiresFrom,List.foldl_cons]
    rw [eval_trimNot_step]
    exact ih _
lemma count_sum_eq_length {l : List ℕ} {N : ℕ} (hb : ∀ x ∈ l,x < N) :
    ∑ w ∈ Finset.range N,l.count w=l.length:=by
  induction l with
  | nil=>simp
  | cons a t ih =>
    have ha : a ∈ Finset.range N:=Finset.mem_range.mpr (hb a (by simp))
    have ht : ∀ x ∈ t,x < N:=fun x hx=>hb x (by simp [hx])
    simp only [List.count_cons,List.length_cons]
    rw [Finset.sum_add_distrib,ih ht]
    have h1 : ∑ w ∈ Finset.range N,(if a=w then 1 else 0)=1:=by
      rw [Finset.sum_ite_eq];simp [ha]
    have h2 : ∀ w,(if a==w then 1 else 0)=(if a=w then 1 else 0):=by
      intro w;by_cases h : a=w<;>simp [h]
    simp_rw [h2]
    rw [h1]
lemma sum_count_sub_one {l : List ℕ} {N : ℕ} (hb : ∀ x ∈ l,x < N)
    (hused : ∀ w < N,w ∈ l) :
    ∑ w ∈ Finset.range N,(l.count w - 1) + N=l.length:=by
  have hge : ∀ w ∈ Finset.range N,1 ≤ l.count w:=fun w hw =>
    List.count_pos_iff.mpr (hused w (Finset.mem_range.mp hw))
  have hsum : ∑ w ∈ Finset.range N,(l.count w - 1) + ∑ _w ∈ Finset.range N,1
      = ∑ w ∈ Finset.range N,l.count w:=by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro w hw
    have:=hge w hw
    omega
  rw [Finset.sum_const,Finset.card_range,smul_eq_mul,mul_one,count_sum_eq_length hb] at hsum
  exact hsum
lemma two_not_gates_le {gs : List Gate} {p q : ℕ} {g g' : Gate}
    (hp : gs[p]?=some g) (hq : gs[q]?=some g') (hne : p ≠ q)
    (hg : g.op=GateOp.not) (hg' : g'.op=GateOp.not) :
    2 ≤ ngC gs:=by
  have hord : ∀ (a b : ℕ) (x y : Gate),gs[a]?=some x → gs[b]?=some y → a < b →
      x.op=GateOp.not → y.op=GateOp.not → 2 ≤ ngC gs:=by
    intro a b x y ha hb hab hx hy
    obtain ⟨l1,l2,hsplit,hl1⟩:=split_at gs a x ha
    have hb2 : l2[b - a - 1]?=some y:=by
      rw [hsplit] at hb
      have hge : l1.length ≤ b:=by omega
      rw [List.getElem?_append_right hge] at hb
      have hsub : b - l1.length=(b - a - 1) + 1:=by omega
      rw [hsub,List.getElem?_cons_succ] at hb
      exact hb
    obtain ⟨m1,m2,hm,_⟩:=split_at l2 (b - a - 1) y hb2
    rw [hsplit,hm]
    simp only [ngC,List.filter_append,List.filter_cons,List.length_append,
      List.length_cons,isNotGate,hx,hy,↓reduceIte]
    omega
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · exact hord p q g g' hp hq hlt hg hg'
  · exact hord q p g' g hq hp hgt hg' hg
lemma elim_drops_at_bad_bin {gs : List Gate} (hok : ∀ g ∈ gs,Ok g)
    (p : ℕ) (g : Gate) (hg : gs[p]?=some g)
    (hbin : g.op=GateOp.and ∨ g.op=GateOp.or)
    (hbad : g.inputs.length ≤ 1 ∨ ∃ a ∈ g.inputs,10 + p ≤ a) :
    nnC (elim 10 gs (idStats 10,[])).2 + 1 ≤ nnC gs:=by
  obtain ⟨pre,post,rfl,rfl⟩:=split_at gs p g hg
  have hokpre : ∀ g' ∈ pre,Ok g':=fun g' h=>hok g' (List.mem_append_left _ h)
  have inv1:=inv_elim 10 (List.ofFn fun _ : Fin 10=>false) (by simp) pre _ (idStats 10,[]) hokpre
    (inv_id 10 _)
  have hlen1 : (elim 10 pre (idStats 10,[])).1.length=10 + pre.length:=by
    have:=inv1.1;rw [length_wiresFrom] at this;simpa using this
  have hsimp_none : (simplify g.op (10 + (elim 10 pre (idStats 10,[])).2.length)
      (g.inputs.map fun i=>(elim 10 pre (idStats 10,[])).1.getD i (Sum.inl false))).1=none:=by
    let ins:=g.inputs.map fun i=>(elim 10 pre (idStats 10,[])).1.getD i (Sum.inl false)
    change (simplify g.op (10 + (elim 10 pre (idStats 10,[])).2.length) ins).1=none
    have hlen_ins : ins.length ≤ 2:=by
      have:=(hok g (by simp)).2;simpa [ins] using this
    rcases hbad with hle1 | ⟨a,ha,hge⟩
    · rcases hbin with e | e<;>rw [e]
      · rcases hins : ins with _ | ⟨x,_ | ⟨y,l⟩⟩
        · rfl
        · cases x<;>rfl
        · have : ins.length ≤ 1:=by simpa [ins] using hle1
          rw [hins] at this;simp at this
      · rcases hins : ins with _ | ⟨x,_ | ⟨y,l⟩⟩
        · rfl
        · cases x<;>rfl
        · have : ins.length ≤ 1:=by simpa [ins] using hle1
          rw [hins] at this;simp at this
    · have hmem : Sum.inl false ∈ ins:=by
        refine List.mem_map.mpr ⟨a,ha,?_⟩
        exact List.getD_eq_default _ _ (by omega)
      have hcnt:=simplify_count g.op (10 + (elim 10 pre (idStats 10,[])).2.length) ins
        (Or.imp id (fun h=>Or.inl h) hbin) hlen_ins (by intro hn;rcases hbin with e | e<;>simp [e] at hn)
        ⟨false,hmem⟩
      cases hq : (simplify g.op (10 + (elim 10 pre (idStats 10,[])).2.length) ins).1 with
      | none=>rfl
      | some _=>simp [hq] at hcnt
  have hstep : elim 10 (pre ++ g :: post) (idStats 10,[]) =
      elim 10 post (elimStep 10 (elim 10 pre (idStats 10,[])) g):=by
    simp [elim,List.foldl_append]
  rw [hstep]
  have hpost:=elim_nonNotCount 10 post (elimStep 10 (elim 10 pre (idStats 10,[])) g)
  have hmid : nnC (elimStep 10 (elim 10 pre (idStats 10,[])) g).2 =
      nnC (elim 10 pre (idStats 10,[])).2:=by
    dsimp only [elimStep]
    rw [hsimp_none]
    simp
  have hpre:=elim_nonNotCount 10 pre (idStats 10,[])
  have htot : nnC (pre ++ g :: post)=nnC pre + 1 + nnC post:=by
    simp only [nnC,List.countP_append,List.countP_cons]
    rcases hbin with e | e<;>simp [isNotGate,e]<;>omega
  simp only [nnC] at hpre
  change nnC (elim 10 pre (idStats 10,[])).2 ≤ 0 + nnC pre at hpre
  omega
lemma elim_drops_at_bad_not {gs : List Gate} (hok : ∀ g ∈ gs,Ok g)
    (p : ℕ) (g : Gate) (hg : gs[p]?=some g)
    (hnot : g.op=GateOp.not)
    (hbad : g.inputs=[] ∨ ∃ a rest,g.inputs=a :: rest ∧ 10 + p ≤ a) :
    ngC (elim 10 gs (idStats 10,[])).2 + 1 ≤ ngC gs ∧
    (elim 10 gs (idStats 10,[])).2.length + 1 ≤ gs.length:=by
  obtain ⟨pre,post,rfl,rfl⟩:=split_at gs p g hg
  have hokpre : ∀ g' ∈ pre,Ok g':=fun g' h=>hok g' (List.mem_append_left _ h)
  have inv1:=inv_elim 10 (List.ofFn fun _ : Fin 10=>false) (by simp) pre _ (idStats 10,[]) hokpre
    (inv_id 10 _)
  have hlen1 : (elim 10 pre (idStats 10,[])).1.length=10 + pre.length:=by
    have:=inv1.1;rw [length_wiresFrom] at this;simpa using this
  have hsimp_none : (simplify g.op (10 + (elim 10 pre (idStats 10,[])).2.length)
      (g.inputs.map fun i=>(elim 10 pre (idStats 10,[])).1.getD i (Sum.inl false))).1=none:=by
    rw [hnot]
    rcases hbad with hnil | ⟨a,rest,hcons,hge⟩
    · simp [hnil,simplify,simpNot]
    · simp only [hcons,List.map_cons,simplify]
      rw [List.getD_eq_default _ _ (by omega)]
      rfl
  have hstep : elim 10 (pre ++ g :: post) (idStats 10,[]) =
      elim 10 post (elimStep 10 (elim 10 pre (idStats 10,[])) g):=by
    simp [elim,List.foldl_append]
  rw [hstep]
  have hmid : (elimStep 10 (elim 10 pre (idStats 10,[])) g).2=(elim 10 pre (idStats 10,[])).2:=by
    dsimp only [elimStep]
    rw [hsimp_none]
    simp
  have hpost_n:=elim_notGateCount 10 post (elimStep 10 (elim 10 pre (idStats 10,[])) g)
  have hpre_n:=elim_notGateCount 10 pre (idStats 10,[])
  have hpost_l:=elim_len 10 post (elimStep 10 (elim 10 pre (idStats 10,[])) g)
  have hpre_l:=elim_len 10 pre (idStats 10,[])
  rw [hmid] at hpost_n hpost_l
  have htot_n : ngC (pre ++ g :: post)=ngC pre + 1 + ngC post:=by
    simp [ngC,isNotGate,hnot];omega
  change ngC (elim 10 pre (idStats 10,[])).2 ≤ 0 + ngC pre at hpre_n
  simp only [List.length_nil,List.length_append,List.length_cons] at hpre_l ⊢
  omega
lemma dep_of_agree {D : Circuit}
    (agree : ∀ x : Fin 10 → Bool,F27.valid x → circuitFun 10 D x=F27.target x)
    (hdiff0 : ∃ x : Fin 9 → Bool,D.eval (List.ofFn x ++ [x 0]) ≠ fTarget x) :
    (∀ i : Fin 10,Dep (circuitFun 10 D) i) ∧
    (∀ (i : Fin 10) (b : Bool),∃ x y : Fin 10 → Bool,
      circuitFun 10 D (Function.update x i b) ≠ circuitFun 10 D (Function.update y i b)):=by
  have hdep9 : ∀ i : Fin 9,∃ m ∈ ([2,4,32,64,128,256,513,517,522] : List ℕ),
      F27.valid (F27.row m) ∧
      F27.valid (Function.update (F27.row m) i.castSucc (!F27.row m i.castSucc)) ∧
      F27.target (Function.update (F27.row m) i.castSucc (!F27.row m i.castSucc)) ≠
        F27.target (F27.row m):=by
    unfold F27.valid
    decide +kernel
  have hstill0 : ∀ (i : Fin 10) (b : Bool),∃ m ∈ ([0,513] : List ℕ),
      F27.valid (Function.update (F27.row m) i b) ∧
      F27.target (Function.update (F27.row m) i b)=false:=by
    unfold F27.valid
    decide +kernel
  have hstill1 : ∀ (i : Fin 10) (b : Bool),∃ m ∈ ([6,320,1023] : List ℕ),
      F27.valid (Function.update (F27.row m) i b) ∧
      F27.target (Function.update (F27.row m) i b)=true:=by
    unfold F27.valid
    decide +kernel
  constructor
  · intro i
    by_cases hi9 : i.val < 9
    · let i9 : Fin 9:=⟨i.val,hi9⟩
      have hcast : i9.castSucc=i:=Fin.ext rfl
      obtain ⟨m,_,hv1,hv2,hne⟩:=hdep9 i9
      rw [hcast] at hv2 hne
      refine ⟨F27.row m,?_⟩
      rw [agree _ hv2,agree _ hv1]
      exact hne
    · have hi : i=9:=Fin.ext (by omega)
      subst hi
      obtain ⟨x,hx⟩:=hdiff0
      let x10 : Fin 10 → Bool:=fun j=>if hj : j.val < 9 then x ⟨j.val,hj⟩ else x 0||x 3
      have hvalid : F27.valid x10:=by
        change x10 9=(x10 0||x10 3);simp [x10]
      have hlist1 : List.ofFn x10=List.ofFn x ++ [x 0||x 3]:=by
        rw [List.ofFn_succ',List.concat_eq_append]
        have h9 : x10 (Fin.last 9)=(x 0||x 3):=by simp [x10]
        have hcast : (fun j : Fin 9=>x10 j.castSucc)=x:=by
          funext j;simp [x10,j.isLt]
        rw [h9,hcast]
      have h0ne : x 0 ≠ (x 0||x 3):=by
        intro heq
        apply hx
        have hc:=agree x10 hvalid
        rw [target_eq_fTarget] at hc
        have hf : (fun j : Fin 9=>x10 j.castSucc)=x:=by
          funext j;simp [x10,j.isLt]
        rw [hf] at hc
        simpa only [circuitFun,hlist1,← heq] using hc
      have hupd : Function.update x10 9 (!x10 9) =
          fun j=>if hj : j.val < 9 then x ⟨j.val,hj⟩ else x 0:=by
        funext j
        by_cases hj9 : j.val < 9
        · have hne9 : j ≠ 9:=fun e=>by subst e;omega
          simp [Function.update_of_ne hne9,x10,hj9]
        · have hj : j=9:=Fin.ext (by omega)
          subst hj
          simp only [Function.update_self,x10,lt_self_iff_false,↓reduceDIte]
          cases h0 : x 0<;>cases h3 : x 3<;>simp_all
      have hlist2 : List.ofFn (Function.update x10 9 (!x10 9))=List.ofFn x ++ [x 0]:=by
        rw [hupd,List.ofFn_succ',List.concat_eq_append]
        have h9 : (if hj : (Fin.last 9).val < 9 then x ⟨(Fin.last 9).val,hj⟩ else x 0)=x 0:=by simp
        have hcast : (fun j : Fin 9=>if hj : j.castSucc.val < 9 then x ⟨j.castSucc.val,hj⟩ else x 0)=x:=by
          funext j;simp [j.isLt]
        rw [h9,hcast]
      refine ⟨x10,?_⟩
      have hc:=agree x10 hvalid
      rw [target_eq_fTarget] at hc
      have hf : (fun j : Fin 9=>x10 j.castSucc)=x:=by
        funext j;simp [x10,j.isLt]
      rw [hf] at hc
      rw [hc]
      simpa only [circuitFun,hlist2] using hx
  · intro i b
    obtain ⟨m1,_,hv1,ht1⟩:=hstill0 i b
    obtain ⟨m2,_,hv2,ht2⟩:=hstill1 i b
    refine ⟨F27.row m1,F27.row m2,?_⟩
    rw [agree _ hv1,agree _ hv2,ht1,ht2]
    decide
lemma branch_of_count_ge_two {gs : List Gate} (hcl : CleanL 10 gs)
    (hnd : ∀ w,(prds hcl w).Nodup)
    (out : Fin (10 + gs.length)) (hout9 : out.val ≠ 9)
    (hcnt : 2 ≤ (out.val :: gs.flatMap Gate.inputs).count 9) :
    (⟨9,by omega⟩ : Fin (10 + gs.length)) ∈ cBW (n:=10) gs:=by
  have hcnt' : 2 ≤ (gs.flatMap Gate.inputs).count 9:=by
    rw [List.count_cons] at hcnt
    have hbeq : (out.val==9)=false:=beq_false_of_ne hout9
    rw [hbeq] at hcnt
    simpa using hcnt
  have h1 : ∀ l : List Gate,(∀ g ∈ l,g.inputs.Nodup) →
      2 ≤ (l.flatMap Gate.inputs).count 9 →
      ∃ p q,∃ (hp : p < l.length) (hq : q < l.length),p ≠ q ∧
        9 ∈ (l[p]'hp).inputs ∧ 9 ∈ (l[q]'hq).inputs:=by
    intro l
    induction l with
    | nil=>intro _ h;simp at h
    | cons g t ih =>
      intro hndL h2
      have hnd_g : g.inputs.Nodup:=hndL g (by simp)
      have hnd_t : ∀ g' ∈ t,g'.inputs.Nodup:=fun g' hg'=>hndL g' (by simp [hg'])
      have hcg : g.inputs.count 9 ≤ 1:=List.nodup_iff_count_le_one.mp hnd_g 9
      simp only [List.flatMap_cons,List.count_append] at h2
      by_cases h9g : 9 ∈ g.inputs
      · have hct : 1 ≤ (t.flatMap Gate.inputs).count 9:=by omega
        have hmemt : 9 ∈ t.flatMap Gate.inputs:=List.count_pos_iff.mp (by omega)
        obtain ⟨g',hg't,h9g'⟩:=List.mem_flatMap.mp hmemt
        obtain ⟨q,hq,rfl⟩:=List.mem_iff_getElem.mp hg't
        exact ⟨0,q + 1,by simp,by simp;omega,by omega,h9g,h9g'⟩
      · have hcg0 : g.inputs.count 9=0:=List.count_eq_zero.mpr h9g
        obtain ⟨p,q,hp,hq,hpq,h9p,h9q⟩:=ih hnd_t (by omega)
        exact ⟨p + 1,q + 1,by simp;omega,by simp;omega,by omega,h9p,h9q⟩
  have hnd_all : ∀ g ∈ gs,g.inputs.Nodup:=by
    intro g hg
    obtain ⟨p,hp,rfl⟩:=List.mem_iff_getElem.mp hg
    let b : Fin (10 + gs.length):=⟨10 + p,by omega⟩
    have h10 : 10 ≤ b.val:=by change 10 ≤ 10 + p;omega
    have hndb:=List.Nodup.map Fin.val_injective (hnd b)
    rw [prdV hcl b h10] at hndb
    have hsub : b.val - 10=p:=by change (10 + p) - 10=p;omega
    simpa [hsub] using hndb
  obtain ⟨p,q,hp,hq,hpq,h9p,h9q⟩:=h1 gs hnd_all hcnt'
  apply inCB.mpr
  refine ⟨⟨10 + p,by omega⟩,⟨10 + q,by omega⟩,
    ⟨p,gs[p]'hp,List.getElem?_eq_getElem hp,rfl,h9p⟩,
    ⟨q,gs[q]'hq,List.getElem?_eq_getElem hq,rfl,h9q⟩,?_⟩
  intro e;apply hpq;have:=congrArg Fin.val e;simp at this;omega
lemma reduce_to_mono_3467 (x2 : Circuit)
    (hfin : FanInTwo x2) (hsz : x2.size=14)
    (hbound : x2.output ≤ 24 ∧ ∀ g ∈ x2.gates,∀ i ∈ g.inputs,i ≤ 24)
    (hused : ∀ w < 24,w ∈ x2.output :: x2.gates.flatMap Gate.inputs)
    (hbudg : 9 + (x2.gates.filter (fun g=>g.op.eval [false]&&!g.op.eval [true])).length +
      ∑ w ∈ Finset.range 24,((x2.output :: x2.gates.flatMap Gate.inputs).count w - 1) ≤ 14)
    (h9 : 2 ≤ (x2.output :: x2.gates.flatMap Gate.inputs).count 9)
    (hdiff : ∀ p : Fin 9,∃ x : Fin 9 → Bool,x2.eval (List.ofFn x ++ [x p]) ≠ fTarget x)
    (hcomp : ∀ x : Fin 9 → Bool,x2.eval (List.ofFn x ++ [x 0||x 3])=fTarget x) :
    ∃ (gs : List Gate) (hcl : CleanL 10 gs) (out : Fin (10 + gs.length))
      (live : ∀ w : Fin (10 + gs.length),w ≠ out → ∃ v,rE gs w v),
      ngC gs=0 ∧ gs.length ≤ 14 ∧
      (∀ w,(prds hcl w).Nodup) ∧
      (∀ x : Fin 10 → Bool,F27.valid x → vl gs x out.val=F27.target x) ∧
      fIB hcl out live 3=out ∧
      fIB hcl out live 4=out ∧
      fIB hcl out live 6=out ∧
      fIB hcl out live 7=out:=by
  have hlen : x2.gates.length=14:=hsz
  have hagree : ∀ x : Fin 10 → Bool,F27.valid x → circuitFun 10 x2 x=F27.target x:=by
    intro x hx
    rw [target_eq_fTarget]
    have hlist : List.ofFn x=List.ofFn (fun i : Fin 9=>x i.castSucc) ++
        [x (0 : Fin 9).castSucc||x (3 : Fin 9).castSucc]:=by
      rw [List.ofFn_succ',List.concat_eq_append]
      have hlast : x (Fin.last 9)=(x (0 : Fin 9).castSucc||x (3 : Fin 9).castSucc):=hx
      rw [hlast]
    simpa only [circuitFun,hlist] using hcomp (fun i : Fin 9=>x i.castSucc)
  obtain ⟨hdep,hstill⟩:=dep_of_agree hagree (hdiff 0)
  have hnc:=dep_nc (hdep 0)
  have hnot_eq:=notGateCount_eq_filter_eval hfin
  rw [hnot_eq] at hbudg
  have htotal:=nnAn x2.gates
  change nnC x2.gates + ngC x2.gates=x2.gates.length at htotal
  by_cases hnot2 : 2 ≤ ngC x2.gates
  · exact (kill_nonNot_le_12 hfin (by omega) hagree hdep hstill).elim
  have hkill_small : ∀ gs o,CleanL 10 gs → (∀ x,vl gs x o=circuitFun 10 x2 x) →
      nnC gs ≤ 12 → False:=by
    intro gs o hcl hev hnn
    have hfan_gs : FanInTwo ⟨gs,o⟩:=fun g hg=>(clean_nok 10 gs hcl g hg).1
    have hfeq : circuitFun 10 ⟨gs,o⟩=circuitFun 10 x2:=funext hev
    exact kill_nonNot_le_12 hfan_gs hnn (fun x hx=>(hev x).trans (hagree x hx))
      (fun i=>hfeq ▸ hdep i) (fun i b=>hfeq ▸ hstill i b)
  have hmono13 : ∀ gs0 o0,CleanL 10 gs0 → ngC gs0=0 → gs0.length ≤ 13 →
      (∀ x,vl gs0 x o0=circuitFun 10 x2 x) →
      ∃ (gs : List Gate) (hcl : CleanL 10 gs) (out : Fin (10 + gs.length))
        (live : ∀ w : Fin (10 + gs.length),w ≠ out → ∃ v,rE gs w v),
        ngC gs=0 ∧ gs.length ≤ 14 ∧
        (∀ w,(prds hcl w).Nodup) ∧
        (∀ x : Fin 10 → Bool,F27.valid x → vl gs x out.val=F27.target x) ∧
        fIB hcl out live 3=out ∧
        fIB hcl out live 4=out ∧
        fIB hcl out live 6=out ∧
        fIB hcl out live 7=out:=by
    intro gs0 o0 hc0 hm0 hl0 he0
    obtain ⟨gs,o,M,hgle⟩:=monoLeast_of_clean hc0 hm0 he0
    have ho : o < 10 + gs.length:=by
      by_contra! h
      obtain ⟨x,y,hxy⟩:=hnc
      exact hxy (by rw [← M.2.2.1 x,← M.2.2.1 y,vl_beyond gs x o h,vl_beyond gs y o h])
    let out : Fin (10 + gs.length):=⟨o,ho⟩
    have live:=monoLeast_live M hnc hdep hstill ho
    have hbr:=bBudg M.1 ho (fun w hw hne=>by
      obtain ⟨v,p,g,hg,_,hmem⟩:=live ⟨w,hw⟩ (fun e=>hne (congrArg Fin.val e))
      exact ⟨p,g,hg,hmem⟩) ((cBW (n:=10) gs).image Fin.val) (fun w hw=>by
      obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hw
      exact bsRE (inCB.mp hv))
    rw [Finset.card_image_of_injective _ Fin.val_injective,M.2.1] at hbr
    have her : ((cBW (n:=10) gs).erase ⟨9,by omega⟩).card ≤ 4 :=
      (Finset.card_erase_le ..).trans (by omega)
    exact mono_wlog_3467 M.1 M.2.1 (by omega) out live (monoLeast_nodup M hnc)
      (fun x hx=>(M.2.2.1 x).trans (hagree x hx)) her
  by_cases hex13 : ∃ gs0 o0,CleanL 10 gs0 ∧ ngC gs0=0 ∧ gs0.length ≤ 13 ∧
      ∀ x,vl gs0 x o0=circuitFun 10 x2 x
  · obtain ⟨gs0,o0,hc0,hm0,hl0,he0⟩:=hex13
    exact hmono13 gs0 o0 hc0 hm0 hl0 he0
  have hout24 : x2.output < 24:=by
    by_contra! hge
    obtain ⟨x,y,hxy⟩:=hnc
    apply hxy
    have h1 : circuitFun 10 x2 x=vl x2.gates x x2.output:=rfl
    have h2 : circuitFun 10 x2 y=vl x2.gates y x2.output:=rfl
    rw [h1,h2,vl_beyond x2.gates x x2.output (by omega),vl_beyond x2.gates y x2.output (by omega)]
  have hall_bin : ∀ (p : ℕ) (g : Gate),x2.gates[p]?=some g →
      (g.op=GateOp.and ∨ g.op=GateOp.or) →
      ∃ a b,a < 10 + p ∧ b < 10 + p ∧ g.inputs=[a,b]:=by
    intro p g hg hbin
    by_contra hbad
    have hbad' : g.inputs.length ≤ 1 ∨ ∃ a ∈ g.inputs,10 + p ≤ a:=by
      have hle2:=(hfin g (List.mem_iff_getElem?.mpr ⟨p,hg⟩)).2
      rcases hin : g.inputs with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩
      · left;simp
      · left;simp
      · right
        by_contra hlt
        push Not at hlt
        exact hbad ⟨a,b,hlt a (by simp),hlt b (by simp),hin⟩
      · rw [hin] at hle2;simp at hle2
    have hdrop:=elim_drops_at_bad_bin hfin p g hg hbin hbad'
    set acc:=elim 10 x2.gates (idStats 10,[]) with hacc
    have hinv : ∀ y : Fin 10 → Bool,Inv 10 (List.ofFn y) (wiresFrom x2.gates (List.ofFn y)) acc :=
      fun y=>inv_elim 10 _ (by simp) x2.gates _ _ hfin (inv_id 10 y)
    have hval : ∀ y : Fin 10 → Bool,
        statVal (wiresFrom acc.2 (List.ofFn y)) (acc.1.getD x2.output (Sum.inl false))=circuitFun 10 x2 y :=
      fun y=>((hinv y).2 x2.output).2
    cases hst : acc.1.getD x2.output (Sum.inl false) with
    | inl c =>
      obtain ⟨y,y',hne⟩:=hnc
      exact hne (by rw [← hval y,← hval y',hst];rfl)
    | inr j =>
      have hcl_acc : CleanL 10 acc.2 :=
        clean_elim 10 (List.ofFn fun _ : Fin 10=>false) (by simp) x2.gates _ _ hfin (inv_id 10 _)
          (by intro r g' hr;simp at hr)
      have hev_acc : ∀ y,vl acc.2 y j=circuitFun 10 x2 y:=fun y=>by
        simpa only [hst,statVal,vl] using hval y
      by_cases hnn12 : nnC acc.2 ≤ 12
      · exact hkill_small acc.2 j hcl_acc hev_acc hnn12
      · have htot_acc : nnC acc.2 + ngC acc.2=acc.2.length :=
          nnAn acc.2
        have hnot_le:=elim_notGateCount 10 x2.gates (idStats 10,[])
        have hlen_le:=elim_len 10 x2.gates (idStats 10,[])
        rw [← hacc] at hnot_le hlen_le
        change ngC acc.2 ≤ 0 + ngC x2.gates at hnot_le
        simp only [List.length_nil] at hlen_le
        have hnot_acc : ngC acc.2=0:=by omega
        have hlen_acc : acc.2.length ≤ 13:=by omega
        exact hex13 ⟨acc.2,j,hcl_acc,hnot_acc,hlen_acc,hev_acc⟩
  have hall_not : ∀ (p : ℕ) (g : Gate),x2.gates[p]?=some g → g.op=GateOp.not →
      ∃ a rest,g.inputs=a :: rest ∧ a < 10 + p:=by
    intro p g hg hnot
    by_contra hbad
    have hbad' : g.inputs=[] ∨ ∃ a rest,g.inputs=a :: rest ∧ 10 + p ≤ a:=by
      rcases hin : g.inputs with _ | ⟨a,rest⟩
      · exact Or.inl rfl
      · right;refine ⟨a,rest,rfl,?_⟩
        by_contra hlt;exact hbad ⟨a,rest,hin,by omega⟩
    obtain ⟨hdrop_n,hdrop_l⟩:=elim_drops_at_bad_not hfin p g hg hnot hbad'
    set acc:=elim 10 x2.gates (idStats 10,[]) with hacc
    have hinv : ∀ y : Fin 10 → Bool,Inv 10 (List.ofFn y) (wiresFrom x2.gates (List.ofFn y)) acc :=
      fun y=>inv_elim 10 _ (by simp) x2.gates _ _ hfin (inv_id 10 y)
    have hval : ∀ y : Fin 10 → Bool,
        statVal (wiresFrom acc.2 (List.ofFn y)) (acc.1.getD x2.output (Sum.inl false))=circuitFun 10 x2 y :=
      fun y=>((hinv y).2 x2.output).2
    cases hst : acc.1.getD x2.output (Sum.inl false) with
    | inl c =>
      obtain ⟨y,y',hne⟩:=hnc
      exact hne (by rw [← hval y,← hval y',hst];rfl)
    | inr j =>
      have hcl_acc : CleanL 10 acc.2 :=
        clean_elim 10 (List.ofFn fun _ : Fin 10=>false) (by simp) x2.gates _ _ hfin (inv_id 10 _)
          (by intro r g' hr;simp at hr)
      have hev_acc : ∀ y,vl acc.2 y j=circuitFun 10 x2 y:=fun y=>by
        simpa only [hst,statVal,vl] using hval y
      exact hex13 ⟨acc.2,j,hcl_acc,by omega,by omega,hev_acc⟩
  have hnot_second : ∀ (p : ℕ) (g : Gate),x2.gates[p]?=some g → g.op=GateOp.not →
      g.inputs.length=1 ∨ ∃ a,a < 10 + p ∧ g.inputs=[a,24]:=by
    intro p g hg hnot
    obtain ⟨a,rest,hin,ha⟩:=hall_not p g hg hnot
    have hle2:=(hfin g (List.mem_iff_getElem?.mpr ⟨p,hg⟩)).2
    rcases rest with _ | ⟨b,_ | ⟨c,l⟩⟩
    · left;simp [hin]
    · right
      have hb24 : b ≤ 24:=hbound.2 g (List.mem_iff_getElem?.mpr ⟨p,hg⟩) b (by simp [hin])
      by_cases hbeq : b=24
      · exact ⟨a,ha,by rw [hin,hbeq]⟩
      · exfalso
        have hnot_pos : 1 ≤ ngC x2.gates:=by
          unfold ngC
          have hmem : g ∈ x2.gates.filter (fun g'=>isNotGate g'.op) :=
            List.mem_filter.mpr ⟨List.mem_iff_getElem?.mpr ⟨p,hg⟩,by simp [isNotGate,hnot]⟩
          exact List.length_pos_iff.mpr (List.ne_nil_of_mem hmem)
        have hnot_eq1 : ngC x2.gates=1:=by omega
        have hall_lt24 : ∀ x ∈ x2.output :: x2.gates.flatMap Gate.inputs,x < 24:=by
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact hout24
          · obtain ⟨g',hg',hxg'⟩:=List.mem_flatMap.mp hx'
            obtain ⟨q,hq⟩:=List.mem_iff_getElem?.mp hg'
            have hqlt:=(List.getElem?_eq_some_iff.mp hq).1
            rcases (hfin g' hg').1 with hop | hop | hop
            · obtain ⟨u,v,hu,hv,huv⟩:=hall_bin q g' hq (Or.inl hop)
              rw [huv] at hxg';simp at hxg';rcases hxg' with rfl | rfl<;>omega
            · obtain ⟨u,v,hu,hv,huv⟩:=hall_bin q g' hq (Or.inr hop)
              rw [huv] at hxg';simp at hxg';rcases hxg' with rfl | rfl<;>omega
            · have hqp : q=p:=by
                by_contra hne
                have:=two_not_gates_le hg hq (Ne.symm hne) hnot hop
                omega
              subst hqp
              have : g' = g:=Option.some.inj (hq.symm.trans hg)
              subst this
              rw [hin] at hxg';simp at hxg';rcases hxg' with rfl | rfl<;>omega
        have hall_len2 : ∀ g' ∈ x2.gates,g'.inputs.length=2:=by
          intro g' hg'
          obtain ⟨q,hq⟩:=List.mem_iff_getElem?.mp hg'
          rcases (hfin g' hg').1 with hop | hop | hop
          · obtain ⟨u,v,_,_,huv⟩:=hall_bin q g' hq (Or.inl hop);simp [huv]
          · obtain ⟨u,v,_,_,huv⟩:=hall_bin q g' hq (Or.inr hop);simp [huv]
          · have hqp : q=p:=by
              by_contra hne
              have:=two_not_gates_le hg hq (Ne.symm hne) hnot hop
              omega
            subst hqp
            have : g' = g:=Option.some.inj (hq.symm.trans hg)
            subst this;simp [hin]
        have hpins_len : (x2.output :: x2.gates.flatMap Gate.inputs).length=29:=by
          simp only [List.length_cons,List.length_flatMap]
          have hsum2 : (x2.gates.map (fun g'=>g'.inputs.length)).sum=2 * x2.gates.length:=by
            have hmap : x2.gates.map (fun g'=>g'.inputs.length)=x2.gates.map (fun _=>2) :=
              List.map_congr_left hall_len2
            rw [hmap,List.map_const',List.sum_replicate,smul_eq_mul,mul_comm]
          rw [hsum2,hlen]
        have hsum_c:=sum_count_sub_one hall_lt24 hused
        rw [hpins_len] at hsum_c
        omega
    · rw [hin] at hle2;simp at hle2
  let gs:=x2.gates.map trimNot
  have hgs_len : gs.length=14:=by simp [gs,hlen]
  have hgs_not : ngC gs=ngC x2.gates:=by
    unfold ngC gs
    rw [List.filter_map]
    simp only [Function.comp_def,List.length_map,trimNot_op]
  have hgs_cl : CleanL 10 gs:=by
    intro p g hg
    simp only [gs,List.getElem?_map,Option.map_eq_some_iff] at hg
    obtain ⟨g0,hg0,rfl⟩:=hg
    have hg0m : g0 ∈ x2.gates:=List.mem_iff_getElem?.mpr ⟨p,hg0⟩
    rcases (hfin g0 hg0m).1 with hop | hop | hop
    · obtain ⟨a,b,ha,hb,hin⟩:=hall_bin p g0 hg0 (Or.inl hop)
      right
      cases g0 with
      | mk op ins =>
        simp only at hop hin
        subst hop hin
        exact ⟨Or.inl rfl,a,b,ha,hb,rfl⟩
    · obtain ⟨a,b,ha,hb,hin⟩:=hall_bin p g0 hg0 (Or.inr hop)
      right
      cases g0 with
      | mk op ins =>
        simp only at hop hin
        subst hop hin
        exact ⟨Or.inr rfl,a,b,ha,hb,rfl⟩
    · obtain ⟨a,rest,hin,ha⟩:=hall_not p g0 hg0 hop
      left
      cases g0 with
      | mk op ins =>
        simp only at hop hin
        subst hop hin
        exact ⟨rfl,a,ha,rfl⟩
  have hgs_ev : ∀ x : Fin 10 → Bool,vl gs x x2.output=circuitFun 10 x2 x:=by
    intro x
    show (wiresFrom gs (List.ofFn x)).getD x2.output false=(x2.wires (List.ofFn x)).getD x2.output false
    rw [wiresFrom_trimNot]
    rfl
  have hgs_count_lt24 : ∀ w < 24,(gs.flatMap Gate.inputs).count w=(x2.gates.flatMap Gate.inputs).count w:=by
    intro w hw
    have hmap : ∀ (l : List Gate),(∀ g ∈ l,g.op=GateOp.not → g.inputs.length=1 ∨ ∃ a,g.inputs=[a,24]) →
        ((l.map trimNot).flatMap Gate.inputs).count w=(l.flatMap Gate.inputs).count w:=by
      intro l
      induction l with
      | nil=>intro _;simp
      | cons g t ih =>
        intro hl
        simp only [List.map_cons,List.flatMap_cons,List.count_append]
        rw [ih (fun g' hg'=>hl g' (by simp [hg']))]
        congr 1
        cases g with
        | mk op ins =>
          cases op with
          | not =>
            rcases hl ⟨GateOp.not,ins⟩ (by simp) rfl with h1 | ⟨a,ha⟩
            · rcases ins with _ | ⟨a,_ | ⟨b,rest⟩⟩
              · rfl
              · rfl
              · simp at h1
            · simp only at ha;subst ha
              simp [trimNot,List.count_cons,show (24==w)=false by simp;omega]
          | and=>rfl
          | or=>rfl
          | mod m=>rfl
          | maj=>rfl
    apply hmap x2.gates
    intro g hg hnot
    obtain ⟨p,hp⟩:=List.mem_iff_getElem?.mp hg
    rcases hnot_second p g hp hnot with h1 | ⟨a,_,ha⟩
    · exact Or.inl h1
    · exact Or.inr ⟨a,ha⟩
  let out : Fin (10 + gs.length):=⟨x2.output,by omega⟩
  have hgs_live : ∀ w : Fin (10 + gs.length),w ≠ out → ∃ v,rE gs w v:=by
    intro w hne
    have hw24 : w.val < 24:=by have:=w.isLt;omega
    have hmem:=hused w.val hw24
    rcases List.mem_cons.mp hmem with hwo | hflat
    · exact (hne (Fin.ext hwo)).elim
    · have hpos : 0 < (gs.flatMap Gate.inputs).count w.val:=by
        rw [hgs_count_lt24 w.val hw24]
        exact List.count_pos_iff.mpr hflat
      obtain ⟨g,hg,hwg⟩:=List.mem_flatMap.mp (List.count_pos_iff.mp hpos)
      obtain ⟨p,hp,rfl⟩:=List.mem_iff_getElem.mp hg
      exact ⟨⟨10 + p,by omega⟩,p,gs[p],List.getElem?_eq_getElem hp,rfl,hwg⟩
  have hgs_nd : ∀ w,(prds hgs_cl w).Nodup:=by
    intro b
    by_cases h10 : 10 ≤ b.val
    · apply List.Nodup.of_map Fin.val
      rw [prdV hgs_cl b h10]
      let p:=b.val - 10
      have hp : p < gs.length:=by have:=b.isLt;omega
      let g:=gs[p]'hp
      have hg : gs[p]?=some g:=List.getElem?_eq_getElem hp
      change g.inputs.Nodup
      rcases hgs_cl p g hg with ⟨_,a,_,hin⟩ | ⟨hop,a,c,ha,_,hin⟩
      · rw [hin];simp
      · suffices a ≠ c by rw [hin];simp [this]
        rintro rfl
        have hncv : ∃ y y' : Fin 10 → Bool,vl gs y x2.output ≠ vl gs y' x2.output:=by
          obtain ⟨x,y,hxy⟩:=hnc;exact ⟨x,y,by rw [hgs_ev,hgs_ev];exact hxy⟩
        have hal : ∀ y : Fin 10 → Bool,vl gs y (10 + p)=vl gs y a:=by
          intro y;rw [vl_gate gs hgs_cl y p g hg,hin]
          rcases hop with e | e<;>rw [e]<;>simp [GateOp.eval]
        obtain ⟨gs',o',hc',hl',hnn',hnot',he'⟩ :=
          drop_alias_both 10 gs hgs_cl x2.output p a hp ha hal hncv
        have hnn_er : nnC (gs.eraseIdx p) + 1=nnC gs:=by
          obtain ⟨pre,post,hsp,hpl⟩:=split_at gs p g hg
          rw [hsp,List.eraseIdx_append_of_length_le (by omega),show p - pre.length=0 by omega,
              List.eraseIdx_cons_zero]
          simp only [nnC,List.countP_append,List.countP_cons]
          rcases hop with e | e<;>simp [isNotGate,e]<;>omega
        have hnot_er : ngC (gs.eraseIdx p) ≤ ngC gs:=by
          rw [notGateCount_eq_opCount,notGateCount_eq_opCount]
          exact (List.eraseIdx_sublist gs p).countP_le
        have hnn_gs : nnC gs + ngC gs=14:=by
          have:=nnAn gs
          change nnC gs + ngC gs=gs.length at this;omega
        by_cases hnot0 : ngC gs=0
        · exact hex13 ⟨gs',o',hc',by omega,by omega,fun x=>(he' x).trans (hgs_ev x)⟩
        · exact hkill_small gs' o' hc' (fun x=>(he' x).trans (hgs_ev x)) (by omega)
    · simp [prds,h10]
  have hout9 : out.val ≠ 9:=by
    have:=out_ge_ten out (fun x hx=>(hgs_ev x).trans (hagree x hx))
    omega
  have h9gs : 2 ≤ (out.val :: gs.flatMap Gate.inputs).count 9:=by
    change 2 ≤ (x2.output :: gs.flatMap Gate.inputs).count 9
    rw [List.count_cons,hgs_count_lt24 9 (by omega),← List.count_cons]
    exact h9
  have hw9_br : (⟨9,by omega⟩ : Fin (10 + gs.length)) ∈ cBW (n:=10) gs :=
    branch_of_count_ge_two hgs_cl hgs_nd out hout9 h9gs
  have hbr:=bBudg hgs_cl out.isLt (fun w hw hne=>by
    obtain ⟨v,p,g,hg,_,hmem⟩:=hgs_live ⟨w,hw⟩ (fun e=>hne (congrArg Fin.val e))
    exact ⟨p,g,hg,hmem⟩) ((cBW (n:=10) gs).image Fin.val) (fun w hw=>by
    obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hw
    exact bsRE (inCB.mp hv))
  rw [Finset.card_image_of_injective _ Fin.val_injective] at hbr
  have herase_eq : ((cBW (n:=10) gs).erase ⟨9,by omega⟩).card + 1 =
      (cBW (n:=10) gs).card:=Finset.card_erase_add_one hw9_br
  by_cases hnot1 : ngC gs=1
  · exact (kill_four_cuts hgs_cl out hgs_live hgs_nd
      (fun x hx=>(hgs_ev x).trans (hagree x hx)) (by omega)).elim
  · have hnot0 : ngC gs=0:=by omega
    exact mono_wlog_3467 hgs_cl hnot0 (by omega) out hgs_live hgs_nd
      (fun x hx=>(hgs_ev x).trans (hagree x hx)) (by omega)
open B2K
def L4 : Finset (Fin 10):={3,4,6,7}
lemma mem_L4 (u : Fin 10) : u ∈ L4 ↔ u=3 ∨ u=4 ∨ u=6 ∨ u=7:=by simp [L4]
def pt64 (i : ℕ) : Fin 10 → Bool :=
  let m:=i % 32
  fun k =>
    match k.val with
    | 0=>m.testBit 0
    | 1=>m.testBit 1
    | 2=>m.testBit 2
    | 5=>m.testBit 3
    | 8=>m.testBit 4
    | 9=>if 32 ≤ i then true else m.testBit 0
    | _=>false
def tt64 (gs : List Gate) (w : ℕ) : ℕ :=
  (List.range 64).foldl (fun acc i=>if vl gs (pt64 i) w then acc|||(1<<<i) else acc) 0
lemma testBit_one (j : ℕ) : (1 : ℕ).testBit j=decide (j=0):=by
  cases j with
  | zero=>decide
  | succ k=>exact Nat.testBit_lt_two_pow (by have : 2 ^ 1 ≤ 2 ^ (k + 1):=Nat.pow_le_pow_right (by omega) (by omega);omega)
lemma tbT64 (gs : List Gate) (w i : ℕ) :
    (tt64 gs w).testBit i=(decide (i < 64)&&vl gs (pt64 i) w):=by
  unfold tt64
  have h : ∀ (n : ℕ) (acc : ℕ),
      ((List.range n).foldl (fun a j=>if vl gs (pt64 j) w then a|||(1<<<j) else a) acc).testBit i =
      (acc.testBit i||(decide (i < n)&&vl gs (pt64 i) w)):=by
    intro n
    induction n with
    | zero=>intro acc;simp
    | succ n ih =>
      intro acc
      rw [List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]
      have h1:=ih acc
      by_cases hin : i=n
      · subst hin
        split_ifs with hv
        · simp only [Nat.testBit_or,Nat.testBit_shiftLeft,Nat.sub_self,Nat.testBit_one_zero,
            decide_true,Bool.true_and,le_refl,hv,lt_add_iff_pos_right,zero_lt_one,
            Bool.and_true,Bool.or_true]
        · rw [h1];simp [hv]
      · split_ifs with hv
        · rw [Nat.testBit_or,h1]
          have hbit : (1<<<n).testBit i=false:=by
            rw [Nat.testBit_shiftLeft]
            by_cases hle : n ≤ i
            · have hpos : i - n ≠ 0:=by omega
              simp [hle,testBit_one,hpos]
            · simp [hle]
          rw [hbit,Bool.or_false]
          have hlt : (i < n + 1) ↔ (i < n):=by omega
          simp [hlt]
        · rw [h1]
          have hlt : (i < n + 1) ↔ (i < n):=by omega
          simp [hlt]
  simpa using h 64 0
lemma tt64_and_ALL64 (gs : List Gate) (w : ℕ) : (ALL64&&&tt64 gs w)=tt64 gs w:=by
  apply Nat.eq_of_testBit_eq;intro i
  rw [Nat.testBit_and,tbT64]
  by_cases hi : i < 64
  · have h64 : ∀ j : Fin 64,ALL64.testBit j.val=true:=by decide
    simp [hi,h64 ⟨i,hi⟩]
  · simp [hi]
lemma tt64_base (gs : List Gate) :
    tt64 gs 0=X0 ∧ tt64 gs 1=X1 ∧ tt64 gs 2=X2 ∧
    tt64 gs 5=X5 ∧ tt64 gs 8=X8 ∧ tt64 gs 9=X9:=by
  have hraw : ∀ (k : ℕ) (hk : k < 10),
      tt64 gs k=(List.range 64).foldl (fun acc i=>if pt64 i ⟨k,hk⟩ then acc|||(1<<<i) else acc) 0:=by
    intro k hk;unfold tt64
    congr 1;funext acc i;rw [vl_input gs (pt64 i) k hk]
  rw [hraw 0 (by omega),hraw 1 (by omega),hraw 2 (by omega),hraw 5 (by omega),hraw 8 (by omega),hraw 9 (by omega)]
  decide +kernel
lemma vl_mono {gs : List Gate} (hcl : CleanL 10 gs) (hmono : ngC gs=0)
    {x y : Fin 10 → Bool} (hle : ∀ k : Fin 10,x k=true → y k=true) (w : ℕ) :
    vl gs x w=true → vl gs y w=true:=by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hwx
    by_cases hw10 : w < 10
    · rw [vl_input gs x w hw10] at hwx
      rw [vl_input gs y w hw10]
      exact hle ⟨w,hw10⟩ hwx
    · obtain ⟨p,rfl⟩ : ∃ p,w=10 + p:=⟨w - 10,by omega⟩
      cases hp : gs[p]? with
      | none =>
        have hge:=List.getElem?_eq_none_iff.mp hp
        rw [vl_beyond gs x (10 + p) (by omega)] at hwx;cases hwx
      | some g =>
        rw [vl_gate gs hcl x p g hp] at hwx
        rw [vl_gate gs hcl y p g hp]
        rcases hcl p g hp with ⟨hnot,_,_,_⟩ | ⟨hop,a,b,ha,hb,hin⟩
        · exfalso
          have hmem : g ∈ gs.filter (fun g'=>isNotGate g'.op) :=
            List.mem_filter.mpr ⟨List.mem_iff_getElem?.mpr ⟨p,hp⟩,by simp [isNotGate,hnot]⟩
          have hpos:=List.length_pos_iff.mpr (List.ne_nil_of_mem hmem)
          change (gs.filter (fun g'=>isNotGate g'.op)).length=0 at hmono
          omega
        · rw [hin] at hwx ⊢
          rcases hop with e | e<;>rw [e] at hwx ⊢
          · simp only [List.map_cons,List.map_nil,GateOp.eval,List.all_cons,List.all_nil,
              id_eq,Bool.and_true,Bool.and_eq_true] at hwx ⊢
            exact ⟨ih a ha hwx.1,ih b hb hwx.2⟩
          · simp only [List.map_cons,List.map_nil,GateOp.eval,List.any_cons,List.any_nil,
              id_eq,Bool.or_false,Bool.or_eq_true] at hwx ⊢
            exact hwx.imp (ih a ha) (ih b hb)
lemma tt64_gate_and {gs : List Gate} (hcl : CleanL 10 gs) {p a b : ℕ}
    (hp : gs[p]?=some ⟨GateOp.and,[a,b]⟩) :
    tt64 gs (10 + p)=(tt64 gs a&&&tt64 gs b):=by
  apply Nat.eq_of_testBit_eq;intro i
  rw [Nat.testBit_and,tbT64,tbT64,tbT64]
  by_cases hi : i < 64
  · simp only [hi,decide_true,Bool.true_and]
    rw [vl_gate gs hcl (pt64 i) p ⟨GateOp.and,[a,b]⟩ hp]
    simp [GateOp.eval]
  · simp [hi]
lemma tt64_gate_or {gs : List Gate} (hcl : CleanL 10 gs) {p a b : ℕ}
    (hp : gs[p]?=some ⟨GateOp.or,[a,b]⟩) :
    tt64 gs (10 + p)=(tt64 gs a|||tt64 gs b):=by
  apply Nat.eq_of_testBit_eq;intro i
  rw [Nat.testBit_or,tbT64,tbT64,tbT64]
  by_cases hi : i < 64
  · simp only [hi,decide_true,Bool.true_and]
    rw [vl_gate gs hcl (pt64 i) p ⟨GateOp.or,[a,b]⟩ hp]
    simp [GateOp.eval]
  · simp [hi]
def landMask (l : List ℕ) : ℕ:=l.foldl (fun acc x=>acc&&&x) ALL64
lemma tbLM (l : List ℕ) (i : ℕ) :
    (landMask l).testBit i=(decide (i < 64)&&l.all (fun x=>x.testBit i)):=by
  unfold landMask
  have h : ∀ (l : List ℕ) (acc : ℕ),
      (l.foldl (fun a x=>a&&&x) acc).testBit i=(acc.testBit i&&l.all (fun x=>x.testBit i)):=by
    intro l
    induction l with
    | nil=>intro acc;simp
    | cons x xs ih=>intro acc;simp only [List.foldl_cons,ih,Nat.testBit_and,List.all_cons,Bool.and_assoc]
  rw [h l ALL64]
  congr 1
  by_cases hi : i < 64
  · have h64 : ∀ j : Fin 64,ALL64.testBit j.val=true:=by decide
    simp [hi,h64 ⟨i,hi⟩]
  · simp only [hi,decide_false]
    have hlt : ALL64 < 2 ^ 64:=by decide
    exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega) (by omega)))
def proj15 (t : ℕ) : ℕ :=
  let bit (k : ℕ):=if t.testBit k then 1 else 0
  let l0:=bit 1|||(bit 2<<<1)|||(bit 4<<<2)|||(bit 8<<<3)|||(bit 16<<<4)
  let l1:=bit 33|||(bit 34<<<1)|||(bit 36<<<2)|||(bit 40<<<3)|||(bit 48<<<4)
  let e5:=bit 3|||(bit 6<<<1)|||(bit 9<<<2)|||(bit 24<<<3)|||(bit 20<<<4)
  (l0<<<10)|||(l1<<<5)|||e5
def proj14 (t : ℕ) : ℕ :=
  let bit (k : ℕ):=if t.testBit k then 1 else 0
  let l0:=bit 1|||(bit 2<<<1)|||(bit 4<<<2)|||(bit 8<<<3)|||(bit 16<<<4)
  let l1:=bit 33|||(bit 34<<<1)|||(bit 36<<<2)|||(bit 40<<<3)|||(bit 48<<<4)
  let e4:=bit 3|||(bit 6<<<1)|||(bit 9<<<2)|||(bit 24<<<3)
  (l0<<<9)|||(l1<<<4)|||e4
lemma testBit_bit (b : Bool) (j : ℕ) : (if b then 1 else 0).testBit j=(decide (j=0)&&b):=by
  cases b<;>simp [testBit_one]
lemma tbP15 (t k : ℕ) :
    (proj15 t).testBit k =
      match k with
      | 0=>t.testBit 3
      | 1=>t.testBit 6
      | 2=>t.testBit 9
      | 3=>t.testBit 24
      | 4=>t.testBit 20
      | 5=>t.testBit 33
      | 6=>t.testBit 34
      | 7=>t.testBit 36
      | 8=>t.testBit 40
      | 9=>t.testBit 48
      | 10=>t.testBit 1
      | 11=>t.testBit 2
      | 12=>t.testBit 4
      | 13=>t.testBit 8
      | 14=>t.testBit 16
      | _=>false:=by
  have h15 : k < 15 → (proj15 t).testBit k =
      match k with
      | 0=>t.testBit 3 | 1=>t.testBit 6 | 2=>t.testBit 9 | 3=>t.testBit 24 | 4=>t.testBit 20
      | 5=>t.testBit 33 | 6=>t.testBit 34 | 7=>t.testBit 36 | 8=>t.testBit 40 | 9=>t.testBit 48
      | 10=>t.testBit 1 | 11=>t.testBit 2 | 12=>t.testBit 4 | 13=>t.testBit 8 | 14=>t.testBit 16
      | _=>false:=by
    intro hk
    unfold proj15;dsimp only
    rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k
    all_goals try omega
    all_goals (
      simp only [Nat.testBit_or,Nat.testBit_shiftLeft,testBit_bit]
      simp)
  by_cases hk : k < 15
  · exact h15 hk
  · have hlt : proj15 t < 2 ^ 15:=by
      unfold proj15;dsimp only
      have hb : ∀ c : Bool,(if c then 1 else 0) < 2:=fun c=>by cases c<;>decide
      have hl : ∀ b0 b1 b2 b3 b4 : Bool,
          ((if b0 then 1 else 0)|||((if b1 then 1 else 0)<<<1)|||((if b2 then 1 else 0)<<<2) |||
           ((if b3 then 1 else 0)<<<3)|||((if b4 then 1 else 0)<<<4)) < 32:=by decide
      have h0:=hl (t.testBit 1) (t.testBit 2) (t.testBit 4) (t.testBit 8) (t.testBit 16)
      have h1:=hl (t.testBit 33) (t.testBit 34) (t.testBit 36) (t.testBit 40) (t.testBit 48)
      have h2:=hl (t.testBit 3) (t.testBit 6) (t.testBit 9) (t.testBit 24) (t.testBit 20)
      have hs0 : ((if t.testBit 1 then 1 else 0)|||((if t.testBit 2 then 1 else 0)<<<1) |||
          ((if t.testBit 4 then 1 else 0)<<<2)|||((if t.testBit 8 then 1 else 0)<<<3) |||
          ((if t.testBit 16 then 1 else 0)<<<4))<<<10 < 32768:=by rw [Nat.shiftLeft_eq];omega
      have hs1 : ((if t.testBit 33 then 1 else 0)|||((if t.testBit 34 then 1 else 0)<<<1) |||
          ((if t.testBit 36 then 1 else 0)<<<2)|||((if t.testBit 40 then 1 else 0)<<<3) |||
          ((if t.testBit 48 then 1 else 0)<<<4))<<<5 < 32768:=by rw [Nat.shiftLeft_eq];omega
      exact or_lt32768 (or_lt32768 hs0 hs1) (by omega)
    have hf : (proj15 t).testBit k=false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega) (by omega)))
    rw [hf]
    rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k
    all_goals try omega
    rfl
lemma tbP14 (t k : ℕ) :
    (proj14 t).testBit k =
      match k with
      | 0=>t.testBit 3
      | 1=>t.testBit 6
      | 2=>t.testBit 9
      | 3=>t.testBit 24
      | 4=>t.testBit 33
      | 5=>t.testBit 34
      | 6=>t.testBit 36
      | 7=>t.testBit 40
      | 8=>t.testBit 48
      | 9=>t.testBit 1
      | 10=>t.testBit 2
      | 11=>t.testBit 4
      | 12=>t.testBit 8
      | 13=>t.testBit 16
      | _=>false:=by
  have h14 : k < 14 → (proj14 t).testBit k =
      match k with
      | 0=>t.testBit 3 | 1=>t.testBit 6 | 2=>t.testBit 9 | 3=>t.testBit 24
      | 4=>t.testBit 33 | 5=>t.testBit 34 | 6=>t.testBit 36 | 7=>t.testBit 40 | 8=>t.testBit 48
      | 9=>t.testBit 1 | 10=>t.testBit 2 | 11=>t.testBit 4 | 12=>t.testBit 8 | 13=>t.testBit 16
      | _=>false:=by
    intro hk
    unfold proj14;dsimp only
    rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k
    all_goals try omega
    all_goals (
      simp only [Nat.testBit_or,Nat.testBit_shiftLeft,testBit_bit]
      simp)
  by_cases hk : k < 14
  · exact h14 hk
  · have hlt : proj14 t < 2 ^ 14:=by
      unfold proj14;dsimp only
      have hl5 : ∀ b0 b1 b2 b3 b4 : Bool,
          ((if b0 then 1 else 0)|||((if b1 then 1 else 0)<<<1)|||((if b2 then 1 else 0)<<<2) |||
           ((if b3 then 1 else 0)<<<3)|||((if b4 then 1 else 0)<<<4)) < 32:=by decide
      have hl4 : ∀ b0 b1 b2 b3 : Bool,
          ((if b0 then 1 else 0)|||((if b1 then 1 else 0)<<<1)|||((if b2 then 1 else 0)<<<2) |||
           ((if b3 then 1 else 0)<<<3)) < 16:=by decide
      have h0:=hl5 (t.testBit 1) (t.testBit 2) (t.testBit 4) (t.testBit 8) (t.testBit 16)
      have h1:=hl5 (t.testBit 33) (t.testBit 34) (t.testBit 36) (t.testBit 40) (t.testBit 48)
      have h2:=hl4 (t.testBit 3) (t.testBit 6) (t.testBit 9) (t.testBit 24)
      have hs0 : ((if t.testBit 1 then 1 else 0)|||((if t.testBit 2 then 1 else 0)<<<1) |||
          ((if t.testBit 4 then 1 else 0)<<<2)|||((if t.testBit 8 then 1 else 0)<<<3) |||
          ((if t.testBit 16 then 1 else 0)<<<4))<<<9 < 16384:=by rw [Nat.shiftLeft_eq];omega
      have hs1 : ((if t.testBit 33 then 1 else 0)|||((if t.testBit 34 then 1 else 0)<<<1) |||
          ((if t.testBit 36 then 1 else 0)<<<2)|||((if t.testBit 40 then 1 else 0)<<<3) |||
          ((if t.testBit 48 then 1 else 0)<<<4))<<<4 < 16384:=by rw [Nat.shiftLeft_eq];omega
      exact or_lt16384 (or_lt16384 hs0 hs1) (by omega)
    have hf : (proj14 t).testBit k=false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega) (by omega)))
    rw [hf]
    rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k
    all_goals try omega
    rfl
lemma p15a (a b : ℕ) : proj15 (a&&&b)=wAnd (proj15 a) (proj15 b):=by
  apply Nat.eq_of_testBit_eq;intro k
  rw [wAnd,Nat.testBit_and,tbP15,tbP15,tbP15]
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k<;>simp [Nat.testBit_and]
lemma p15o (a b : ℕ) : proj15 (a|||b)=wOr (proj15 a) (proj15 b):=by
  apply Nat.eq_of_testBit_eq;intro k
  rw [wOr,Nat.testBit_or,tbP15,tbP15,tbP15]
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k<;>simp [Nat.testBit_or]
lemma p14a (a b : ℕ) : proj14 (a&&&b)=wAnd (proj14 a) (proj14 b):=by
  apply Nat.eq_of_testBit_eq;intro k
  rw [wAnd,Nat.testBit_and,tbP14,tbP14,tbP14]
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k<;>simp [Nat.testBit_and]
lemma p14o (a b : ℕ) : proj14 (a|||b)=wOr (proj14 a) (proj14 b):=by
  apply Nat.eq_of_testBit_eq;intro k
  rw [wOr,Nat.testBit_or,tbP14,tbP14,tbP14]
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k<;>simp [Nat.testBit_or]
lemma proj_base_mem :
    bWs.all (fun w=>C0_15W.elem (proj15 w))=true ∧
    bWs.all (fun w=>C0W.elem (proj14 w))=true ∧
    lb15 C0_15W=3:=by
  decide +kernel
lemma pp1 :
    (∀ i : Fin 32,F27.valid (pt64 i.val) ∧
      (IND_LOW.testBit i.val=true → F27.target (pt64 i.val)=false)) ∧
    (∀ i : Fin 64,32 ≤ i.val → F27.valid (Function.update (pt64 i.val) 3 true) ∧
      (IND_3.testBit i.val=true → F27.target (Function.update (pt64 i.val) 3 true)=false)) ∧
    (∀ i : Fin 64,R0_3.testBit i.val=true → 32 ≤ i.val ∧
      F27.valid (Function.update (pt64 i.val) 3 true) ∧
      F27.target (Function.update (pt64 i.val) 3 true)=false) ∧
    (∀ i : Fin 64,R0_4.testBit i.val=true → i.val < 32 ∧
      F27.valid (Function.update (pt64 i.val) 4 true) ∧
      F27.target (Function.update (pt64 i.val) 4 true)=false) ∧
    (∀ i : Fin 64,R0_6.testBit i.val=true →
      (i.val < 32 ∧ F27.valid (Function.update (pt64 i.val) 6 true) ∧
        F27.target (Function.update (pt64 i.val) 6 true)=false) ∨
      (i.val=32 ∧ F27.valid (Function.update (Function.update (pt64 32) 3 true) 6 true) ∧
        F27.target (Function.update (Function.update (pt64 32) 3 true) 6 true)=false)) ∧
    (∀ i : Fin 64,R0_7.testBit i.val=true →
      (i.val < 32 ∧ F27.valid (Function.update (pt64 i.val) 7 true) ∧
        F27.target (Function.update (pt64 i.val) 7 true)=false) ∨
      (i.val=32 ∧ F27.valid (Function.update (Function.update (pt64 32) 3 true) 7 true) ∧
        F27.target (Function.update (Function.update (pt64 32) 3 true) 7 true)=false)):=by
  unfold F27.valid
  decide +kernel
lemma pp2 :
    (∀ i : Fin 64,R1_3.testBit i.val=true →
      (∀ k : Fin 10,pt64 36 k=true → pt64 i.val k=true) ∨
      (∀ k : Fin 10,pt64 48 k=true → pt64 i.val k=true)) ∧
    (∀ i : Fin 64,R1_4.testBit i.val=true →
      (∀ k : Fin 10,pt64 1 k=true → pt64 i.val k=true) ∨
      (∀ k : Fin 10,pt64 32 k=true → pt64 i.val k=true)) ∧
    (∀ i : Fin 64,R1_6.testBit i.val=true →
      (∀ k : Fin 10,pt64 2 k=true → pt64 i.val k=true) ∨
      (∀ k : Fin 10,pt64 16 k=true → pt64 i.val k=true)) ∧
    (∀ i : Fin 64,R1_7.testBit i.val=true →
      (∀ k : Fin 10,pt64 4 k=true → pt64 i.val k=true) ∨
      (∀ k : Fin 10,pt64 8 k=true → pt64 i.val k=true)) ∧
    ((∀ k : Fin 10,pt64 36 k=true → pt64 5 k=true) ∧ IND_LOW.testBit 5=true ∧
     (∀ k : Fin 10,pt64 48 k=true → pt64 17 k=true) ∧ IND_LOW.testBit 17=true ∧
     IND_LOW.testBit 1=true ∧ IND_3.testBit 32=true ∧
     IND_LOW.testBit 2=true ∧ IND_LOW.testBit 16=true ∧
     IND_LOW.testBit 4=true ∧ IND_LOW.testBit 8=true) ∧
    (F27.valid (Function.update (pt64 36) 3 true) ∧ F27.target (Function.update (pt64 36) 3 true)=true ∧
     F27.valid (Function.update (pt64 48) 3 true) ∧ F27.target (Function.update (pt64 48) 3 true)=true ∧
     F27.valid (Function.update (pt64 1) 4 true) ∧ F27.target (Function.update (pt64 1) 4 true)=true ∧
     F27.valid (Function.update (Function.update (pt64 32) 3 true) 4 true) ∧
       F27.target (Function.update (Function.update (pt64 32) 3 true) 4 true)=true ∧
     F27.valid (Function.update (pt64 2) 6 true) ∧ F27.target (Function.update (pt64 2) 6 true)=true ∧
     F27.valid (Function.update (pt64 16) 6 true) ∧ F27.target (Function.update (pt64 16) 6 true)=true ∧
     F27.valid (Function.update (pt64 4) 7 true) ∧ F27.target (Function.update (pt64 4) 7 true)=true ∧
     F27.valid (Function.update (pt64 8) 7 true) ∧ F27.target (Function.update (pt64 8) 7 true)=true) ∧
    (F27.target (pt64 3)=true ∧ F27.target (pt64 6)=true ∧
     F27.target (pt64 9)=true ∧ F27.target (pt64 24)=true ∧
     IND_SAFE=(IND_LOW|||IND_3)):=by
  unfold F27.valid
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩<;>decide +kernel
  · decide +kernel
lemma mbP :
    (R1_3 < 2 ^ 64 ∧ R1_4 < 2 ^ 64 ∧ R1_6 < 2 ^ 64 ∧ R1_7 < 2 ^ 64 ∧
     R0_3 < 2 ^ 64 ∧ R0_4 < 2 ^ 64 ∧ R0_6 < 2 ^ 64 ∧ R0_7 < 2 ^ 64 ∧
     IND_LOW < 2 ^ 32 ∧ IND_3 < 2 ^ 64 ∧ IND_SAFE < 2 ^ 64 ∧
     (∀ i : Fin 32,IND_3.testBit i.val=false)) ∧
    (R0_3.testBit 34=true ∧ R1_4.testBit 34=true ∧ R1_6.testBit 34=true ∧
     R0_3.testBit 40=true ∧ R1_4.testBit 40=true ∧ R1_7.testBit 40=true ∧
     R0_6.testBit 5=true ∧ R1_3.testBit 5=true ∧ R1_4.testBit 5=true ∧ R1_7.testBit 5=true ∧
     R0_7.testBit 17=true ∧ R1_3.testBit 17=true ∧ R1_4.testBit 17=true ∧ R1_6.testBit 17=true ∧
     R0_4.testBit 2=true ∧ R1_6.testBit 2=true ∧
     R0_4.testBit 8=true ∧ R1_7.testBit 8=true) ∧
    (R1_6.testBit 2=true ∧ R1_6.testBit 16=true ∧ R0_6.testBit 1=true ∧ R0_6.testBit 4=true ∧ R0_6.testBit 8=true ∧
     R1_7.testBit 4=true ∧ R1_7.testBit 8=true ∧ R0_7.testBit 1=true ∧ R0_7.testBit 2=true ∧ R0_7.testBit 16=true ∧
     R1_3.testBit 36=true ∧ R1_3.testBit 48=true ∧ R0_3.testBit 33=true ∧ R0_3.testBit 34=true ∧ R0_3.testBit 40=true ∧
     IND_SAFE.testBit 1=true ∧ IND_SAFE.testBit 2=true ∧ IND_SAFE.testBit 4=true ∧
     IND_SAFE.testBit 8=true ∧ IND_SAFE.testBit 16=true ∧ IND_SAFE.testBit 20=true):=by
  decide +kernel
lemma pair6_witnesses : ∀ u v : Fin 10,u ∈ L4 → v ∈ L4 → u ≠ v →
    ∃ m ∈ ([34,517,769,773] : List ℕ),
      F27.valid (F27.row m) ∧
      F27.valid (Function.update (F27.row m) u true) ∧
      F27.valid (Function.update (F27.row m) v true) ∧
      F27.target (F27.row m)=false ∧
      F27.target (Function.update (F27.row m) u true)=true ∧
      F27.target (Function.update (F27.row m) v true)=true:=by
  unfold F27.valid
  decide +kernel
def iKey {α : Type} (f : α → ℕ) (v : α) : List α → List α
  | []=>[v]
  | y :: ys=>if f v ≤ f y then v :: y :: ys else y :: iKey f v ys
lemma insertKey_perm {α : Type} (f : α → ℕ) (x : α) (l : List α) :
    (iKey f x l).Perm (x :: l):=by
  induction l with
  | nil=>exact List.Perm.refl _
  | cons y ys ih =>
    unfold iKey
    split_ifs
    · exact List.Perm.refl _
    · exact (List.Perm.cons y ih).trans (List.Perm.swap x y ys)
def sBK {α : Type} (f : α → ℕ) (l : List α) : List α :=
  l.foldl (fun acc x=>iKey f x acc) []
lemma sortByKey_perm {α : Type} (f : α → ℕ) (l : List α) : (sBK f l).Perm l:=by
  unfold sBK
  have h : ∀ (l acc : List α),(l.foldl (fun a x=>iKey f x a) acc).Perm (l ++ acc):=by
    intro l
    induction l with
    | nil=>intro acc;exact List.Perm.refl _
    | cons x xs ih =>
      intro acc
      simp only [List.foldl_cons,List.cons_append]
      exact (ih _).trans ((List.Perm.append_left xs (insertKey_perm f x acc)).trans List.perm_middle)
  simpa using h l []
lemma insertKey_map {α : Type} (f : α → ℕ) (x : α) (l : List α) :
    (iKey f x l).map f=insNat (f x) (l.map f):=by
  induction l with
  | nil=>rfl
  | cons y ys ih =>
    unfold iKey insNat
    simp only [List.map_cons]
    split_ifs
    · rfl
    · simp only [List.map_cons,ih]
lemma sortByKey_map_eq {α : Type} (f : α → ℕ) (a b c d e : α) :
    let s:=sBK f [a,b,c,d,e]
    (f (s.getD 0 a),f (s.getD 1 a),f (s.getD 2 a),f (s.getD 3 a),f (s.getD 4 a)) =
      sort5 (f a) (f b) (f c) (f d) (f e):=by
  have hmap : (sBK f [a,b,c,d,e]).map f =
      ([f a,f b,f c,f d,f e].foldl (fun acc x=>insNat x acc) []):=by
    unfold sBK
    have hfold : ∀ (l acc : List α),
        (l.foldl (fun a x=>iKey f x a) acc).map f =
        ((l.map f).foldl (fun a x=>insNat x a) (acc.map f)):=by
      intro l
      induction l with
      | nil=>intro acc;rfl
      | cons x xs ih =>
        intro acc
        simp only [List.foldl_cons,List.map_cons]
        rw [ih,insertKey_map]
    exact hfold [a,b,c,d,e] []
  have hlen : (sBK f [a,b,c,d,e]).length=5:=by
    have:=(sortByKey_perm f [a,b,c,d,e]).length_eq;simpa using this
  have hget : ∀ i < 5,f ((sBK f [a,b,c,d,e]).getD i a) =
      ((sBK f [a,b,c,d,e]).map f).getD i 0:=by
    intro i hi
    rw [List.getD_eq_getElem _ _ (by omega),List.getD_eq_getElem _ _ (by simp [hlen];exact hi)]
    simp
  unfold sort5
  dsimp only
  rw [hget 0 (by omega),hget 1 (by omega),hget 2 (by omega),hget 3 (by omega),hget 4 (by omega),hmap]
lemma tbP15g (t k : ℕ) (hk : 15 ≤ k) : (proj15 t).testBit k=false:=by
  rw [tbP15]
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k
  all_goals try omega
  rfl
lemma tbP14g (t k : ℕ) (hk : 14 ≤ k) : (proj14 t).testBit k=false:=by
  rw [tbP14]
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k
  all_goals try omega
  rfl
lemma bits5_vals :
    ((18 : ℕ).testBit 0=false ∧ (18 : ℕ).testBit 1=true ∧ (18 : ℕ).testBit 2=false ∧ (18 : ℕ).testBit 3=false ∧ (18 : ℕ).testBit 4=true) ∧
    ((12 : ℕ).testBit 0=false ∧ (12 : ℕ).testBit 1=false ∧ (12 : ℕ).testBit 2=true ∧ (12 : ℕ).testBit 3=true ∧ (12 : ℕ).testBit 4=false) ∧
    ((20 : ℕ).testBit 0=false ∧ (20 : ℕ).testBit 1=false ∧ (20 : ℕ).testBit 2=true ∧ (20 : ℕ).testBit 3=false ∧ (20 : ℕ).testBit 4=true) ∧
    ((31 : ℕ).testBit 0=true ∧ (31 : ℕ).testBit 1=true ∧ (31 : ℕ).testBit 2=true ∧ (31 : ℕ).testBit 3=true ∧ (31 : ℕ).testBit 4=true) ∧
    ((15 : ℕ).testBit 0=true ∧ (15 : ℕ).testBit 1=true ∧ (15 : ℕ).testBit 2=true ∧ (15 : ℕ).testBit 3=true):=by
  decide
lemma p15B6 {b : ℕ} (h1 : (b&&&R1_6)=R1_6) (h0 : (b&&&R0_6)=0) : l0_15 (proj15 b)=18:=by
  have hb : ∀ k,R1_6.testBit k=true → b.testBit k=true:=fun k hk=>by
    have:=congrArg (fun n=>n.testBit k) h1;simp only [Nat.testBit_and,hk,Bool.and_true] at this;exact this
  have hz : ∀ k,R0_6.testBit k=true → b.testBit k=false:=fun k hk=>by
    have:=congrArg (fun n=>n.testBit k) h0;simp only [Nat.testBit_and,hk,Bool.and_true,Nat.zero_testBit] at this;exact this
  have m:=mbP.2.2
  have v:=bits5_vals.1
  apply Nat.eq_of_testBit_eq;intro k
  rw [l0_15,Nat.testBit_shiftRight]
  rcases k with _ | _ | _ | _ | _ | k
  · simp [tbP15,hz 1 m.2.2.1,v]
  · simp [tbP15,hb 2 m.1,v]
  · simp [tbP15,hz 4 m.2.2.2.1,v]
  · simp [tbP15,hz 8 m.2.2.2.2.1,v]
  · simp [tbP15,hb 16 m.2.1,v]
  · have hge : (18 : ℕ).testBit (k + 5)=false :=
      Nat.testBit_lt_two_pow (by have : 2 ^ 5 ≤ 2 ^ (k + 5):=Nat.pow_le_pow_right (by omega) (by omega);omega)
    rw [hge];exact tbP15g _ _ (by omega)
lemma p15B7 {b : ℕ} (h1 : (b&&&R1_7)=R1_7) (h0 : (b&&&R0_7)=0) : l0_15 (proj15 b)=12:=by
  have hb : ∀ k,R1_7.testBit k=true → b.testBit k=true:=fun k hk=>by
    have:=congrArg (fun n=>n.testBit k) h1;simp only [Nat.testBit_and,hk,Bool.and_true] at this;exact this
  have hz : ∀ k,R0_7.testBit k=true → b.testBit k=false:=fun k hk=>by
    have:=congrArg (fun n=>n.testBit k) h0;simp only [Nat.testBit_and,hk,Bool.and_true,Nat.zero_testBit] at this;exact this
  have m:=mbP.2.2.2.2.2.2.2
  have v:=bits5_vals.2.1
  apply Nat.eq_of_testBit_eq;intro k
  rw [l0_15,Nat.testBit_shiftRight]
  rcases k with _ | _ | _ | _ | _ | k
  · simp [tbP15,hz 1 m.2.2.1,v]
  · simp [tbP15,hz 2 m.2.2.2.1,v]
  · simp [tbP15,hb 4 m.1,v]
  · simp [tbP15,hb 8 m.2.1,v]
  · simp [tbP15,hz 16 m.2.2.2.2.1,v]
  · have hge : (12 : ℕ).testBit (k + 5)=false :=
      Nat.testBit_lt_two_pow (by have : 2 ^ 5 ≤ 2 ^ (k + 5):=Nat.pow_le_pow_right (by omega) (by omega);omega)
    rw [hge];exact tbP15g _ _ (by omega)
lemma p15B3 {b : ℕ} (h1 : (b&&&R1_3)=R1_3) (h0 : (b&&&R0_3)=0) : l1_15 (proj15 b)=20:=by
  have hb : ∀ k,R1_3.testBit k=true → b.testBit k=true:=fun k hk=>by
    have:=congrArg (fun n=>n.testBit k) h1;simp only [Nat.testBit_and,hk,Bool.and_true] at this;exact this
  have hz : ∀ k,R0_3.testBit k=true → b.testBit k=false:=fun k hk=>by
    have:=congrArg (fun n=>n.testBit k) h0;simp only [Nat.testBit_and,hk,Bool.and_true,Nat.zero_testBit] at this;exact this
  have m:=mbP.2.2.2.2.2.2.2.2.2.2.2.2
  have v:=bits5_vals.2.2.1
  have v31:=bits5_vals.2.2.2.1
  apply Nat.eq_of_testBit_eq;intro k
  rw [l1_15,Nat.testBit_and,Nat.testBit_shiftRight]
  rcases k with _ | _ | _ | _ | _ | k
  · simp [tbP15,hz 33 m.2.2.1,v,v31]
  · simp [tbP15,hz 34 m.2.2.2.1,v,v31]
  · simp [tbP15,hb 36 m.1,v,v31]
  · simp [tbP15,hz 40 m.2.2.2.2.1,v,v31]
  · simp [tbP15,hb 48 m.2.1,v,v31]
  · have h31 : (31 : ℕ).testBit (k + 5)=false :=
      Nat.testBit_lt_two_pow (by have : 2 ^ 5 ≤ 2 ^ (k + 5):=Nat.pow_le_pow_right (by omega) (by omega);omega)
    have h20 : (20 : ℕ).testBit (k + 5)=false :=
      Nat.testBit_lt_two_pow (by have : 2 ^ 5 ≤ 2 ^ (k + 5):=Nat.pow_le_pow_right (by omega) (by omega);omega)
    rw [h31,h20,Bool.and_false]
lemma p14B6 {b : ℕ} (h1 : (b&&&R1_6)=R1_6) (h0 : (b&&&R0_6)=0) : l0_14 (proj14 b)=18:=by
  have hb : ∀ k,R1_6.testBit k=true → b.testBit k=true:=fun k hk=>by
    have:=congrArg (fun n=>n.testBit k) h1;simp only [Nat.testBit_and,hk,Bool.and_true] at this;exact this
  have hz : ∀ k,R0_6.testBit k=true → b.testBit k=false:=fun k hk=>by
    have:=congrArg (fun n=>n.testBit k) h0;simp only [Nat.testBit_and,hk,Bool.and_true,Nat.zero_testBit] at this;exact this
  have m:=mbP.2.2
  have v:=bits5_vals.1
  apply Nat.eq_of_testBit_eq;intro k
  rw [l0_14,Nat.testBit_shiftRight]
  rcases k with _ | _ | _ | _ | _ | k
  · simp [tbP14,hz 1 m.2.2.1,v]
  · simp [tbP14,hb 2 m.1,v]
  · simp [tbP14,hz 4 m.2.2.2.1,v]
  · simp [tbP14,hz 8 m.2.2.2.2.1,v]
  · simp [tbP14,hb 16 m.2.1,v]
  · have hge : (18 : ℕ).testBit (k + 5)=false :=
      Nat.testBit_lt_two_pow (by have : 2 ^ 5 ≤ 2 ^ (k + 5):=Nat.pow_le_pow_right (by omega) (by omega);omega)
    rw [hge];exact tbP14g _ _ (by omega)
lemma p14B7 {b : ℕ} (h1 : (b&&&R1_7)=R1_7) (h0 : (b&&&R0_7)=0) : l0_14 (proj14 b)=12:=by
  have hb : ∀ k,R1_7.testBit k=true → b.testBit k=true:=fun k hk=>by
    have:=congrArg (fun n=>n.testBit k) h1;simp only [Nat.testBit_and,hk,Bool.and_true] at this;exact this
  have hz : ∀ k,R0_7.testBit k=true → b.testBit k=false:=fun k hk=>by
    have:=congrArg (fun n=>n.testBit k) h0;simp only [Nat.testBit_and,hk,Bool.and_true,Nat.zero_testBit] at this;exact this
  have m:=mbP.2.2.2.2.2.2.2
  have v:=bits5_vals.2.1
  apply Nat.eq_of_testBit_eq;intro k
  rw [l0_14,Nat.testBit_shiftRight]
  rcases k with _ | _ | _ | _ | _ | k
  · simp [tbP14,hz 1 m.2.2.1,v]
  · simp [tbP14,hz 2 m.2.2.2.1,v]
  · simp [tbP14,hb 4 m.1,v]
  · simp [tbP14,hb 8 m.2.1,v]
  · simp [tbP14,hz 16 m.2.2.2.2.1,v]
  · have hge : (12 : ℕ).testBit (k + 5)=false :=
      Nat.testBit_lt_two_pow (by have : 2 ^ 5 ≤ 2 ^ (k + 5):=Nat.pow_le_pow_right (by omega) (by omega);omega)
    rw [hge];exact tbP14g _ _ (by omega)
lemma p14B3 {b : ℕ} (h1 : (b&&&R1_3)=R1_3) (h0 : (b&&&R0_3)=0) : l1_14 (proj14 b)=20:=by
  have hb : ∀ k,R1_3.testBit k=true → b.testBit k=true:=fun k hk=>by
    have:=congrArg (fun n=>n.testBit k) h1;simp only [Nat.testBit_and,hk,Bool.and_true] at this;exact this
  have hz : ∀ k,R0_3.testBit k=true → b.testBit k=false:=fun k hk=>by
    have:=congrArg (fun n=>n.testBit k) h0;simp only [Nat.testBit_and,hk,Bool.and_true,Nat.zero_testBit] at this;exact this
  have m:=mbP.2.2.2.2.2.2.2.2.2.2.2.2
  have v:=bits5_vals.2.2.1
  have v31:=bits5_vals.2.2.2.1
  apply Nat.eq_of_testBit_eq;intro k
  rw [l1_14,Nat.testBit_and,Nat.testBit_shiftRight]
  rcases k with _ | _ | _ | _ | _ | k
  · simp [tbP14,hz 33 m.2.2.1,v,v31]
  · simp [tbP14,hz 34 m.2.2.2.1,v,v31]
  · simp [tbP14,hb 36 m.1,v,v31]
  · simp [tbP14,hz 40 m.2.2.2.2.1,v,v31]
  · simp [tbP14,hb 48 m.2.1,v,v31]
  · have h31 : (31 : ℕ).testBit (k + 5)=false :=
      Nat.testBit_lt_two_pow (by have : 2 ^ 5 ≤ 2 ^ (k + 5):=Nat.pow_le_pow_right (by omega) (by omega);omega)
    have h20 : (20 : ℕ).testBit (k + 5)=false :=
      Nat.testBit_lt_two_pow (by have : 2 ^ 5 ≤ 2 ^ (k + 5):=Nat.pow_le_pow_right (by omega) (by omega);omega)
    rw [h31,h20,Bool.and_false]
lemma pSZ {z : ℕ} (hs : (z&&&IND_SAFE)=0) :
    l0_15 (proj15 z)=0 ∧ ((e5_15 (proj15 z)>>>4)&&&1)=0 ∧
    (e5_15 (proj15 z)&&&15)=edgesOf z ∧
    l0_14 (proj14 z)=0 ∧ e4_14 (proj14 z)=edgesOf z:=by
  have hz : ∀ k,IND_SAFE.testBit k=true → z.testBit k=false:=fun k hk=>by
    have:=congrArg (fun n=>n.testBit k) hs;simp only [Nat.testBit_and,hk,Bool.and_true,Nat.zero_testBit] at this;exact this
  have m:=mbP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have t1 : z.testBit 1=false:=hz 1 m.1
  have t2 : z.testBit 2=false:=hz 2 m.2.1
  have t4 : z.testBit 4=false:=hz 4 m.2.2.1
  have t8 : z.testBit 8=false:=hz 8 m.2.2.2.1
  have t16 : z.testBit 16=false:=hz 16 m.2.2.2.2.1
  have t20 : z.testBit 20=false:=hz 20 m.2.2.2.2.2
  have he_bit : ∀ b k,b=1<<<k → ((z&&&b) != 0)=z.testBit k:=by
    intro b k rfl
    apply Bool.eq_iff_iff.mpr
    simp only [bne_iff_ne]
    constructor
    · intro hne
      by_contra hf
      have hzf : z.testBit k=false:=by cases h : z.testBit k<;>simp_all
      apply hne
      apply Nat.eq_of_testBit_eq;intro i
      rw [Nat.testBit_and,Nat.testBit_shiftLeft,Nat.zero_testBit]
      by_cases hik : i=k
      · subst hik;simp [hzf]
      · by_cases hle : k ≤ i
        · have hpos : i - k ≠ 0:=by omega
          simp [hle,testBit_one,hpos]
        · simp [hle]
    · intro ht h0
      have hi:=congrArg (fun n=>n.testBit k) h0
      simp only [Nat.testBit_and,Nat.testBit_shiftLeft,le_refl,decide_true,Nat.sub_self,
        Nat.testBit_one_zero,Bool.and_true,ht,Nat.zero_testBit] at hi
      cases hi
  have hE01 : ((z&&&E01) != 0)=z.testBit 3:=he_bit E01 3 (by decide)
  have hE12 : ((z&&&E12) != 0)=z.testBit 6:=he_bit E12 6 (by decide)
  have hE05 : ((z&&&E05) != 0)=z.testBit 9:=he_bit E05 9 (by decide)
  have hE58 : ((z&&&E58) != 0)=z.testBit 24:=he_bit E58 24 (by decide)
  have hedges_tb : ∀ k,(edgesOf z).testBit k =
      match k with | 0=>z.testBit 3 | 1=>z.testBit 6 | 2=>z.testBit 9 | 3=>z.testBit 24 | _=>false:=by
    intro k
    unfold edgesOf;rw [hE01,hE12,hE05,hE58]
    rcases k with _ | _ | _ | _ | k
    · cases z.testBit 3<;>cases z.testBit 6<;>cases z.testBit 9<;>cases z.testBit 24<;>decide
    · cases z.testBit 3<;>cases z.testBit 6<;>cases z.testBit 9<;>cases z.testBit 24<;>decide
    · cases z.testBit 3<;>cases z.testBit 6<;>cases z.testBit 9<;>cases z.testBit 24<;>decide
    · cases z.testBit 3<;>cases z.testBit 6<;>cases z.testBit 9<;>cases z.testBit 24<;>decide
    · have hlt : ((if z.testBit 3 then 1 else 0)|||(if z.testBit 6 then 2 else 0) |||
          (if z.testBit 9 then 4 else 0)|||(if z.testBit 24 then 8 else 0)) < 16:=by
        cases z.testBit 3<;>cases z.testBit 6<;>cases z.testBit 9<;>cases z.testBit 24<;>decide
      exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : 4 ≤ k + 4)))
  refine ⟨?_,?_,?_,?_,?_⟩
  · apply Nat.eq_of_testBit_eq;intro k
    rw [l0_15,Nat.testBit_shiftRight,Nat.zero_testBit]
    rcases k with _ | _ | _ | _ | _ | k
    · simp [tbP15,t1]
    · simp [tbP15,t2]
    · simp [tbP15,t4]
    · simp [tbP15,t8]
    · simp [tbP15,t16]
    · exact tbP15g _ _ (by omega)
  · apply Nat.eq_of_testBit_eq;intro k
    rw [e5_15,Nat.testBit_and,Nat.testBit_shiftRight,Nat.testBit_and,Nat.zero_testBit]
    rcases k with _ | k
    · simp [tbP15,t20]
    · have : (1 : ℕ).testBit (k + 1)=false:=by simp [testBit_one]
      rw [this,Bool.and_false]
  · apply Nat.eq_of_testBit_eq;intro k
    rw [e5_15,Nat.testBit_and,Nat.testBit_and,tbP15,hedges_tb]
    have v31:=bits5_vals.2.2.2.1;have v15:=bits5_vals.2.2.2.2
    rcases k with _ | _ | _ | _ | k
    · simp [v31,v15]
    · simp [v31,v15]
    · simp [v31,v15]
    · simp [v31,v15]
    · have : (15 : ℕ).testBit (k + 4)=false :=
        Nat.testBit_lt_two_pow (by have : 2 ^ 4 ≤ 2 ^ (k + 4):=Nat.pow_le_pow_right (by omega) (by omega);omega)
      rw [this,Bool.and_false];rfl
  · apply Nat.eq_of_testBit_eq;intro k
    rw [l0_14,Nat.testBit_shiftRight,Nat.zero_testBit]
    rcases k with _ | _ | _ | _ | _ | k
    · simp [tbP14,t1]
    · simp [tbP14,t2]
    · simp [tbP14,t4]
    · simp [tbP14,t8]
    · simp [tbP14,t16]
    · exact tbP14g _ _ (by omega)
  · apply Nat.eq_of_testBit_eq;intro k
    rw [e4_14,Nat.testBit_and,tbP14,hedges_tb]
    have v15:=bits5_vals.2.2.2.2
    rcases k with _ | _ | _ | _ | k
    · simp [v15]
    · simp [v15]
    · simp [v15]
    · simp [v15]
    · have : (15 : ℕ).testBit (k + 4)=false :=
        Nat.testBit_lt_two_pow (by have : 2 ^ 4 ≤ 2 ^ (k + 4):=Nat.pow_le_pow_right (by omega) (by omega);omega)
      rw [this,Bool.and_false];rfl
lemma pop4_or_le (a b : ℕ) (ha : a < 16) (hb : b < 16) : pop4 (a|||b) ≤ pop4 a + pop4 b :=
  (by decide : ∀ x y : Fin 16,pop4 (x.val|||y.val) ≤ pop4 x.val + pop4 y.val) ⟨a,ha⟩ ⟨b,hb⟩
lemma edgesOf_lt16 (z : ℕ) : edgesOf z < 16:=by
  unfold edgesOf
  cases ((z&&&E01) != 0)<;>cases ((z&&&E12) != 0) <;>
  cases ((z&&&E05) != 0)<;>cases ((z&&&E58) != 0)<;>decide
lemma foldl_edges_pop_le (l : List ℕ) (h1 : ∀ z ∈ l,pop4 (edgesOf z) ≤ 1) :
    pop4 (l.foldl (fun acc z=>acc|||edgesOf z) 0) ≤ l.length:=by
  have h : ∀ (l : List ℕ) (init : ℕ),init < 16 → (∀ z ∈ l,pop4 (edgesOf z) ≤ 1) →
      pop4 (l.foldl (fun acc z=>acc|||edgesOf z) init) ≤ pop4 init + l.length:=by
    intro l
    induction l with
    | nil=>intro init _ _;simp
    | cons z t ih =>
      intro init hi hl
      simp only [List.foldl_cons,List.length_cons]
      have hlt : (init|||edgesOf z) < 16 :=
        (by decide : ∀ x y : Fin 16,(x.val|||y.val) < 16) ⟨init,hi⟩ ⟨edgesOf z,edgesOf_lt16 z⟩
      have hstep:=ih (init|||edgesOf z) hlt (fun w hw=>hl w (List.mem_cons_of_mem z hw))
      have hp:=pop4_or_le init (edgesOf z) hi (edgesOf_lt16 z)
      have hz:=hl z (List.mem_cons_self ..)
      omega
  have:=h l 0 (by omega) h1
  have hp0 : pop4 0=0:=by decide
  omega
lemma cmG {gs : List Gate} (hcl : CleanL 10 gs) (hmono : ngC gs=0)
    (distinct : ∀ w,(prds hcl w).Nodup) {p : ℕ} {g : Gate} (hp : gs[p]?=some g) :
    (g.op=GateOp.and ∨ g.op=GateOp.or) ∧
    ∃ a b,a < 10 + p ∧ b < 10 + p ∧ a ≠ b ∧ g.inputs=[a,b]:=by
  have hplt : p < gs.length:=by
    by_contra hge
    rw [List.getElem?_eq_none (Nat.le_of_not_lt hge)] at hp;cases hp
  rcases hcl p g hp with ⟨hnot,_,_,_⟩ | ⟨hop,a,b,ha,hb,hin⟩
  · exfalso
    have hmem : g ∈ gs.filter (fun g'=>isNotGate g'.op) :=
      List.mem_filter.mpr ⟨List.mem_iff_getElem?.mpr ⟨p,hp⟩,by simp [isNotGate,hnot]⟩
    have hpos:=List.length_pos_iff.mpr (List.ne_nil_of_mem hmem)
    change (gs.filter (fun g'=>isNotGate g'.op)).length=0 at hmono
    omega
  · refine ⟨hop,a,b,ha,hb,?_,hin⟩
    have hnd:=distinct ⟨10 + p,by omega⟩
    have hval:=prdV hcl ⟨10 + p,by omega⟩ (by simp)
    have hmap:=List.Nodup.map Fin.val_injective hnd
    rw [hval] at hmap
    have hg_eq : gs[p]'hplt=g:=by
      have:=List.getElem?_eq_getElem hplt;rw [this] at hp;exact Option.some.inj hp
    simp only [Nat.add_sub_cancel_left] at hmap
    rw [hg_eq,hin] at hmap
    exact (List.nodup_cons.mp hmap).1 ∘ (by simp)
lemma tbFoE (l : List ℕ) (k : ℕ) :
    (l.foldl (fun acc z=>acc|||edgesOf z) 0).testBit k=l.any (fun z=>(edgesOf z).testBit k):=by
  have h : ∀ (l : List ℕ) (acc : ℕ),
      (l.foldl (fun a z=>a|||edgesOf z) acc).testBit k =
      (acc.testBit k||l.any (fun z=>(edgesOf z).testBit k)):=by
    intro l
    induction l with
    | nil=>intro acc;simp
    | cons z zs ih =>
      intro acc
      simp only [List.foldl_cons,ih,Nat.testBit_or,List.any_cons,Bool.or_assoc]
  simpa using h l 0
lemma p15LM {S : List ℕ} (hC : ACl S) :
    ∀ (l : List ℕ),l ≠ [] → (∀ x ∈ l,(ALL64&&&x)=x) → (∀ x ∈ l,proj15 x ∈ S) →
      proj15 (landMask l) ∈ S:=by
  intro l
  cases l with
  | nil=>intro h;exact (h rfl).elim
  | cons x xs =>
    intro _ hA hM
    unfold landMask
    rw [List.foldl_cons,hA x (List.mem_cons_self ..)]
    have hfold : ∀ (ys : List ℕ) (acc : ℕ),proj15 acc ∈ S → (∀ y ∈ ys,proj15 y ∈ S) →
        proj15 (ys.foldl (fun a y=>a&&&y) acc) ∈ S:=by
      intro ys
      induction ys with
      | nil=>intro acc ha _;exact ha
      | cons y ys ih =>
        intro acc ha hys
        simp only [List.foldl_cons]
        apply ih (acc&&&y)
        · rw [p15a];exact hC _ ha _ (hys y (List.mem_cons_self ..))
        · intro z hz;exact hys z (List.mem_cons_of_mem y hz)
    exact hfold xs x (hM x (List.mem_cons_self ..)) (fun y hy=>hM y (List.mem_cons_of_mem x hy))
lemma p14LM {S : List ℕ} (hC : ACl S) :
    ∀ (l : List ℕ),l ≠ [] → (∀ x ∈ l,(ALL64&&&x)=x) → (∀ x ∈ l,proj14 x ∈ S) →
      proj14 (landMask l) ∈ S:=by
  intro l
  cases l with
  | nil=>intro h;exact (h rfl).elim
  | cons x xs =>
    intro _ hA hM
    unfold landMask
    rw [List.foldl_cons,hA x (List.mem_cons_self ..)]
    have hfold : ∀ (ys : List ℕ) (acc : ℕ),proj14 acc ∈ S → (∀ y ∈ ys,proj14 y ∈ S) →
        proj14 (ys.foldl (fun a y=>a&&&y) acc) ∈ S:=by
      intro ys
      induction ys with
      | nil=>intro acc ha _;exact ha
      | cons y ys ih =>
        intro acc ha hys
        simp only [List.foldl_cons]
        apply ih (acc&&&y)
        · rw [p14a];exact hC _ ha _ (hys y (List.mem_cons_self ..))
        · intro z hz;exact hys z (List.mem_cons_of_mem y hz)
    exact hfold xs x (hM x (List.mem_cons_self ..)) (fun y hy=>hM y (List.mem_cons_of_mem x hy))
lemma p15aLM {S : List ℕ} (hC : ACl S) (y : ℕ) (l : List ℕ)
    (hyA : (ALL64&&&y)=y) (hyS : proj15 y ∈ S)
    (hlA : ∀ x ∈ l,(ALL64&&&x)=x) (hlS : ∀ x ∈ l,proj15 x ∈ S) :
    proj15 (y&&&landMask l) ∈ S:=by
  cases l with
  | nil =>
    have hEq : (y&&&landMask [])=y:=by unfold landMask;rw [List.foldl_nil,bac,hyA]
    rw [hEq];exact hyS
  | cons x xs =>
    rw [p15a]
    exact hC _ hyS _ (p15LM hC (x :: xs) (List.cons_ne_nil x xs) hlA hlS)
lemma p14aLM {S : List ℕ} (hC : ACl S) (y : ℕ) (l : List ℕ)
    (hyA : (ALL64&&&y)=y) (hyS : proj14 y ∈ S)
    (hlA : ∀ x ∈ l,(ALL64&&&x)=x) (hlS : ∀ x ∈ l,proj14 x ∈ S) :
    proj14 (y&&&landMask l) ∈ S:=by
  cases l with
  | nil =>
    have hEq : (y&&&landMask [])=y:=by unfold landMask;rw [List.foldl_nil,bac,hyA]
    rw [hEq];exact hyS
  | cons x xs =>
    rw [p14a]
    exact hC _ hyS _ (p14LM hC (x :: xs) (List.cons_ne_nil x xs) hlA hlS)
lemma reach15_mono {k1 k2 : ℕ} {S T : List ℕ} (hle : k1 ≤ k2) (h : Reach15 k1 S T) : Reach15 k2 S T:=by
  induction hle with
  | refl=>exact h
  | step _ ih=>exact Or.inl ih
lemma vlINR {gs : List Gate} (hcl : CleanL 10 gs)
    {x y : Fin 10 → Bool} {v : Fin (10 + gs.length)}
    (hag : ∀ u : Fin 10,Relation.ReflTransGen (rE gs) (iW gs u) v → x u=y u) :
    vl gs x v.val=vl gs y v.val:=by
  obtain ⟨w,hw⟩:=v
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hw10 : w < 10
    · rw [vl_input gs x w hw10,vl_input gs y w hw10]
      exact hag ⟨w,hw10⟩ Relation.ReflTransGen.refl
    · obtain ⟨p,rfl⟩ : ∃ p,w=10 + p:=⟨w - 10,by omega⟩
      have hp : p < gs.length:=by omega
      let g:=gs[p]'hp
      have hpg : gs[p]?=some g:=List.getElem?_eq_getElem hp
      apply vl_congr gs hcl x y p g hpg
      intro a ha
      have halt : a < 10 + p:=(hcl p g hpg).lt a ha
      exact ih a halt (by omega) (fun u hu =>
        hag u (hu.tail ⟨p,g,hpg,rfl,ha⟩))
lemma tbFlt (i : ℕ) {x k : ℕ} (hx : x < 2 ^ k) (hki : k ≤ i) : x.testBit i=false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) hki))
lemma ALL64_testBit (i : ℕ) : ALL64.testBit i=decide (i < 64):=by
  by_cases hi : i < 64
  · have h64 : ∀ j : Fin 64,ALL64.testBit j.val=true:=by decide
    simp [hi,h64 ⟨i,hi⟩]
  · simp only [hi,decide_false]
    exact tbFlt i (by decide : ALL64 < 2 ^ 64) (by omega)
lemma mask4_sub (a0 a1 a2 a3 b0 b1 b2 b3 : Bool)
    (h0 : a0=true → b0=true) (h1 : a1=true → b1=true)
    (h2 : a2=true → b2=true) (h3 : a3=true → b3=true) :
    (((if a0 then 1 else 0)|||(if a1 then 2 else 0)|||(if a2 then 4 else 0)|||(if a3 then 8 else 0)) &&&
     ((if b0 then 1 else 0)|||(if b1 then 2 else 0)|||(if b2 then 4 else 0)|||(if b3 then 8 else 0))) =
    ((if a0 then 1 else 0)|||(if a1 then 2 else 0)|||(if a2 then 4 else 0)|||(if a3 then 8 else 0)):=by
  have h : ∀ x0 x1 x2 x3 y0 y1 y2 y3 : Bool,
      (!x0||y0)=true → (!x1||y1)=true → (!x2||y2)=true → (!x3||y3)=true →
      (((if x0 then 1 else 0)|||(if x1 then 2 else 0)|||(if x2 then 4 else 0)|||(if x3 then 8 else 0)) &&&
       ((if y0 then 1 else 0)|||(if y1 then 2 else 0)|||(if y2 then 4 else 0)|||(if y3 then 8 else 0))) =
      ((if x0 then 1 else 0)|||(if x1 then 2 else 0)|||(if x2 then 4 else 0)|||(if x3 then 8 else 0)):=by
    decide
  exact h a0 a1 a2 a3 b0 b1 b2 b3
    (by cases a0<;>simp [h0]) (by cases a1<;>simp [h1]) (by cases a2<;>simp [h2]) (by cases a3<;>simp [h3])
lemma mask4_disj (a0 a1 a2 a3 b0 b1 b2 b3 : Bool)
    (h0 : !(a0&&b0)=true) (h1 : !(a1&&b1)=true)
    (h2 : !(a2&&b2)=true) (h3 : !(a3&&b3)=true) :
    (((if a0 then 1 else 0)|||(if a1 then 2 else 0)|||(if a2 then 4 else 0)|||(if a3 then 8 else 0)) &&&
     ((if b0 then 1 else 0)|||(if b1 then 2 else 0)|||(if b2 then 4 else 0)|||(if b3 then 8 else 0)))=0:=by
  have h : ∀ x0 x1 x2 x3 y0 y1 y2 y3 : Bool,
      !(x0&&y0)=true → !(x1&&y1)=true → !(x2&&y2)=true → !(x3&&y3)=true →
      (((if x0 then 1 else 0)|||(if x1 then 2 else 0)|||(if x2 then 4 else 0)|||(if x3 then 8 else 0)) &&&
       ((if y0 then 1 else 0)|||(if y1 then 2 else 0)|||(if y2 then 4 else 0)|||(if y3 then 8 else 0)))=0:=by
    decide
  exact h a0 a1 a2 a3 b0 b1 b2 b3 h0 h1 h2 h3
lemma sub5_props (p0 p1 p2 p3 p4 : Bool) :
    let sub:=(if p0 then 1 else 0)|||(if p1 then 2 else 0)|||(if p2 then 4 else 0) |||
               (if p3 then 8 else 0)|||(if p4 then 16 else 0)
    sub < 32 ∧
    ((sub>>>0)&&&1 != 0)=p0 ∧ ((sub>>>1)&&&1 != 0)=p1 ∧
    ((sub>>>2)&&&1 != 0)=p2 ∧ ((sub>>>3)&&&1 != 0)=p3 ∧ ((sub>>>4)&&&1 != 0)=p4 ∧
    ((sub&&&1) != 0)=p0 ∧ ((sub&&&2) != 0)=p1 ∧
    ((sub&&&4) != 0)=p2 ∧ ((sub&&&8) != 0)=p3 ∧ ((sub&&&16) != 0)=p4:=by
  revert p0 p1 p2 p3 p4;decide
set_option maxHeartbeats 2400000 in
lemma bomb2_impossible (gs : List Gate) (hcl : CleanL 10 gs)
    (out : Fin (10 + gs.length))
    (live : ∀ w : Fin (10 + gs.length),w ≠ out → ∃ v,rE gs w v)
    (hmono : ngC gs=0) (hlen : gs.length ≤ 14)
    (distinct : ∀ w,(prds hcl w).Nodup)
    (computes : ∀ x : Fin 10 → Bool,F27.valid x → vl gs x out.val=F27.target x)
    (h3 : fIB hcl out live 3=out)
    (h4 : fIB hcl out live 4=out)
    (h6 : fIB hcl out live 6=out)
    (h7 : fIB hcl out live 7=out) : False:=by
  classical
  have hL4_bnd : ∀ u ∈ L4,fIB hcl out live u=out:=by
    intro u hu
    rw [mem_L4] at hu
    rcases hu with rfl | rfl | rfl | rfl<;>assumption
  let inU (w : Fin (10 + gs.length)) : Prop :=
    ∃ u ∈ L4,Relation.ReflTransGen (rE gs) (iW gs u) w
  have inU_first : ∀ w,inU w →
      FBR.first (rE gs) out (rOrd hcl) live w=out:=by
    rintro w ⟨u,hu,hpath⟩
    have hle : w ≤ fIB hcl out live u:=by
      rw [hL4_bnd u hu];exact wLO hcl out live w
    have hrb:=FBR.rBef (rE gs) out (rOrd hcl) live hpath hle
    exact hrb.2.trans (hL4_bnd u hu)
  have uOut : ∀ {w v1 v2},inU w → rE gs w v1 → rE gs w v2 → v1=v2:=by
    intro w v1 v2 hw e1 e2
    by_contra hne
    have hbr : FBR.Branches (rE gs) w:=⟨v1,v2,e1,e2,hne⟩
    have hterm : FBR.Terminal (rE gs) out w:=Or.inr hbr
    have hf:=FBR.fOT (rE gs) out (rOrd hcl) live hterm
    rw [inU_first w hw] at hf
    have hlt:=rOrd hcl e1
    have hle:=wLO hcl out live v1
    change v1.val ≤ out.val at hle
    have hwo : out.val=w.val:=congrArg Fin.val hf
    rw [hwo] at hle
    omega
  have uMem : ∀ {w v},inU w → rE gs w v → inU v:=by
    rintro w v ⟨u,hu,hr⟩ e;exact ⟨u,hu,hr.tail e⟩
  have uRch : ∀ {w},inU w → Relation.ReflTransGen (rE gs) w out:=by
    intro w hw
    have hp:=FBR.fIRP (rE gs) out
      (FBR.fPth (rE gs) out (rOrd hcl) live w)
    rwa [inU_first w hw] at hp
  have uLam : ∀ {w v1 v2},inU w →
      Relation.ReflTransGen (rE gs) w v1 →
      Relation.ReflTransGen (rE gs) w v2 →
      Relation.ReflTransGen (rE gs) v1 v2 ∨ Relation.ReflTransGen (rE gs) v2 v1:=by
    intro w v1 v2 hw r1 r2
    induction r1 using Relation.ReflTransGen.head_induction_on generalizing v2 with
    | refl=>exact Or.inl r2
    | @head a b hab _ ih =>
      rcases Relation.ReflTransGen.cases_head r2 with rfl | ⟨c,hac,hcv2⟩
      · exact Or.inr (Relation.ReflTransGen.head hab ‹_›)
      · have hbc : b=c:=uOut hw hab hac
        subst hbc
        exact ih (uMem hw hab) hcv2
  have aSB : ∀ {a x y},inU x →
      Relation.ReflTransGen (rE gs) x a →
      Relation.ReflTransGen (avoid (rE gs) a) x y →
      Relation.ReflTransGen (rE gs) y a:=by
    intro a x y hx hra hav
    induction hav using Relation.ReflTransGen.head_induction_on with
    | refl=>exact hra
    | @head c d hcd _ ih =>
      rcases Relation.ReflTransGen.cases_head hra with rfl | ⟨e,hce,hea⟩
      · exact (hcd.2.1 rfl).elim
      · have hde : d=e:=uOut hx hcd.1 hce
        subst hde
        exact ih (uMem hx hce) hea
  have uNA : ∀ {a : Fin (10 + gs.length)} {u : Fin 10},u ∈ L4 → a ≠ out →
      Relation.ReflTransGen (rE gs) (iW gs u) a →
      ¬ Relation.ReflTransGen (avoid (rE gs) a) (iW gs u) out:=by
    intro a u hu hne hra hav
    have houta:=aSB ⟨u,hu,Relation.ReflTransGen.refl⟩ hra hav
    have hle1 : out ≤ a:=FBR.pFwd (rE gs) (rOrd hcl) houta
    have hle2 : a ≤ out:=wLO hcl out live a
    exact hne (le_antisymm hle2 hle1)
  have inU_lt10 : ∀ {w : Fin (10 + gs.length)},inU w → w.val < 10 →
      ∃ u ∈ L4,w=iW gs u:=by
    rintro w ⟨u,hu,hr⟩ hw10
    rcases Relation.ReflTransGen.cases_tail hr with rfl | ⟨_,_,e⟩
    · exact ⟨u,hu,rfl⟩
    · obtain ⟨p,_,_,hb,_⟩:=e
      omega
  have vlIL4 : ∀ {w : ℕ} (hw : w < 10 + gs.length),¬ inU ⟨w,hw⟩ →
      ∀ {x y : Fin 10 → Bool},(∀ k : Fin 10,k ∉ L4 → x k=y k) →
      vl gs x w=vl gs y w:=by
    intro w hw hnot x y hag
    apply vlINR hcl (v:=⟨w,hw⟩)
    intro u hu
    apply hag u
    intro huL4
    exact hnot ⟨u,huL4,hu⟩
  let Uw : Finset (Fin (10 + gs.length)):=Finset.univ.filter inU
  let Ug : Finset ℕ:=(Finset.range gs.length).filter (fun p=>∃ hp : p < gs.length,inU ⟨10 + p,by omega⟩)
  let Wg : Finset ℕ:=(Finset.range gs.length) \ Ug
  let Mg : Finset ℕ:=Ug.filter (fun p =>
    ∃ g a b,gs[p]?=some g ∧ g.inputs=[a,b] ∧
      (∃ ha : a < 10 + gs.length,inU ⟨a,ha⟩) ∧
      (∃ hb : b < 10 + gs.length,inU ⟨b,hb⟩))
  let Ag : Finset ℕ:=(Ug \ Mg).filter (fun p=>∃ g,gs[p]?=some g ∧ g.op=GateOp.and)
  let Sg : Finset ℕ:=(Ug \ Mg).filter (fun p=>∃ g,gs[p]?=some g ∧ g.op=GateOp.or)
  let Wa : Finset ℕ:=Wg.filter (fun p=>∃ g,gs[p]?=some g ∧ g.op=GateOp.and)
  let Wo : Finset ℕ:=Wg.filter (fun p=>∃ g,gs[p]?=some g ∧ g.op=GateOp.or)
  have hUr : ∀ p ∈ Ug,p < gs.length:=fun p hp =>
    Finset.mem_range.mp (Finset.mem_filter.mp hp).1
  have hUi : ∀ {p},p ∈ Ug → ∃ hp : p < gs.length,inU ⟨10 + p,by omega⟩:=fun hp =>
    (Finset.mem_filter.mp hp).2
  have hUp : ∀ {p : ℕ},p ∈ Ug →
      ∃ g a b,gs[p]?=some g ∧ g.inputs=[a,b] ∧ a < 10 + p ∧ b < 10 + p ∧ a ≠ b ∧
        ((∃ ha : a < 10 + gs.length,inU ⟨a,ha⟩) ∨ (∃ hb : b < 10 + gs.length,inU ⟨b,hb⟩)):=by
    intro p hp
    obtain ⟨hplt,⟨u,hu,hr⟩⟩:=hUi hp
    let g:=gs[p]'hplt
    have hpg : gs[p]?=some g:=List.getElem?_eq_getElem hplt
    obtain ⟨_,a,b,ha,hb,hab,hin⟩:=cmG hcl hmono distinct hpg
    refine ⟨g,a,b,hpg,hin,ha,hb,hab,?_⟩
    rcases Relation.ReflTransGen.cases_tail hr with heq | ⟨w,hw,e⟩
    · have:=congrArg Fin.val heq;simp [iW] at this;have:=u.isLt;omega
    · obtain ⟨p',g',hp',heq,hmem⟩:=e
      simp only at heq
      have hpe : p' = p:=by omega
      subst hpe
      rw [hpg] at hp'
      have hgeq : g' = g:=Option.some.inj hp'.symm
      subst hgeq
      rw [hin] at hmem
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hmem
      rcases hmem with hwa | hwb
      · left;exact ⟨by omega,by convert (⟨u,hu,hw⟩ : inU w) using 1;exact Fin.ext hwa.symm⟩
      · right;exact ⟨by omega,by convert (⟨u,hu,hw⟩ : inU w) using 1;exact Fin.ext hwb.symm⟩
  have hM_sub : Mg ⊆ Ug:=Finset.filter_subset ..
  have hA_sub : Ag ⊆ Ug:=(Finset.filter_subset ..).trans Finset.sdiff_subset
  have hS_sub : Sg ⊆ Ug:=(Finset.filter_subset ..).trans Finset.sdiff_subset
  have hUc : Ug.card=Mg.card + Ag.card + Sg.card:=by
    have hAS_disj : Disjoint Ag Sg:=Finset.disjoint_left.mpr fun p hpa hps=>by
      obtain ⟨_,g1,hg1,ho1⟩:=Finset.mem_filter.mp hpa
      obtain ⟨_,g2,hg2,ho2⟩:=Finset.mem_filter.mp hps
      rw [hg1] at hg2;cases hg2;rw [ho1] at ho2;cases ho2
    have hAS_union : Ag ∪ Sg=Ug \ Mg:=by
      ext p;simp only [Finset.mem_union,Finset.mem_filter,Ag,Sg]
      constructor
      · rintro (⟨h,_⟩ | ⟨h,_⟩)<;>exact h
      · intro h
        have hplt:=hUr p (Finset.mem_sdiff.mp h).1
        have hpg : gs[p]?=some (gs[p]'hplt):=List.getElem?_eq_getElem hplt
        rcases (cmG hcl hmono distinct hpg).1 with ho | ho
        · exact Or.inl ⟨h,_,hpg,ho⟩
        · exact Or.inr ⟨h,_,hpg,ho⟩
    have hc1:=Finset.card_sdiff_add_card_eq_card hM_sub
    rw [← hAS_union,Finset.card_union_of_disjoint hAS_disj] at hc1
    omega
  have hWc : Wg.card=Wa.card + Wo.card:=by
    have hdisj : Disjoint Wa Wo:=Finset.disjoint_left.mpr fun p h1 h2=>by
      obtain ⟨_,g1,hg1,ho1⟩:=Finset.mem_filter.mp h1
      obtain ⟨_,g2,hg2,ho2⟩:=Finset.mem_filter.mp h2
      rw [hg1] at hg2;cases hg2;rw [ho1] at ho2;cases ho2
    have hunion : Wa ∪ Wo=Wg:=by
      ext p;simp only [Finset.mem_union,Finset.mem_filter,Wa,Wo]
      constructor
      · rintro (⟨h,_⟩ | ⟨h,_⟩)<;>exact h
      · intro h
        have hplt : p < gs.length:=Finset.mem_range.mp (Finset.mem_sdiff.mp h).1
        have hpg : gs[p]?=some (gs[p]'hplt):=List.getElem?_eq_getElem hplt
        rcases (cmG hcl hmono distinct hpg).1 with ho | ho
        · exact Or.inl ⟨h,_,hpg,ho⟩
        · exact Or.inr ⟨h,_,hpg,ho⟩
    rw [← hunion,Finset.card_union_of_disjoint hdisj]
  have hUW : Ug.card + Wg.card=gs.length:=by
    have hsub : Ug ⊆ Finset.range gs.length:=Finset.filter_subset ..
    have:=Finset.card_sdiff_add_card_eq_card hsub
    rw [Finset.card_range] at this
    change Wg.card + Ug.card=gs.length at this
    omega
  have hout_inU : out ∈ Uw:=by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
    exact ⟨3,by simp [L4],uRch ⟨3,by simp [L4],Relation.ReflTransGen.refl⟩⟩
  have hUwc : Uw.card=4 + Ug.card:=by
    let S_in : Finset (Fin (10 + gs.length)):=L4.image (iW gs)
    let S_gt : Finset (Fin (10 + gs.length)):=Ug.attach.image (fun p=>⟨10 + p.1,by have:=hUr p.1 p.2;omega⟩)
    have hdisj : Disjoint S_in S_gt:=Finset.disjoint_left.mpr fun w h1 h2=>by
      obtain ⟨u,_,rfl⟩:=Finset.mem_image.mp h1
      obtain ⟨p,_,hp⟩:=Finset.mem_image.mp h2
      have:=congrArg Fin.val hp;simp [iW] at this;have:=u.isLt;omega
    have hunion : Uw=S_in ∪ S_gt:=by
      ext w;simp only [Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and,Uw,S_in,S_gt]
      constructor
      · intro hw
        by_cases h10 : w.val < 10
        · obtain ⟨u,hu,rfl⟩:=inU_lt10 hw h10
          exact Or.inl (Finset.mem_image.mpr ⟨u,hu,rfl⟩)
        · right
          have hplt : w.val - 10 < gs.length:=by have:=w.isLt;omega
          have hw_eq : (⟨10 + (w.val - 10),by omega⟩ : Fin (10 + gs.length))=w:=Fin.ext (by simp;omega)
          have hmem : w.val - 10 ∈ Ug :=
            Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hplt,hplt,hw_eq.symm ▸ hw⟩
          exact Finset.mem_image.mpr ⟨⟨w.val - 10,hmem⟩,Finset.mem_attach ..,hw_eq⟩
      · rintro (h | h)
        · obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp h
          exact ⟨u,hu,Relation.ReflTransGen.refl⟩
        · obtain ⟨p,_,rfl⟩:=Finset.mem_image.mp h
          exact (hUi p.2).2
    have hc1 : S_in.card=4:=by
      dsimp only [S_in]
      rw [Finset.card_image_of_injective L4 (fun a b h=>Fin.ext (by have:=congrArg Fin.val h;simpa [iW] using this))]
      decide
    have hc2 : S_gt.card=Ug.card:=by
      dsimp only [S_gt]
      rw [Finset.card_image_of_injective Ug.attach (fun a b h=>Subtype.ext (by have:=congrArg Fin.val h;change 10 + a.1=10 + b.1 at this;omega))]
      exact Finset.card_attach
    rw [hunion,Finset.card_union_of_disjoint hdisj,hc1,hc2]
  have hM_card : Mg.card=3:=by
    let EU : Finset (Fin (10 + gs.length) × Fin (10 + gs.length)) :=
      (Uw ×ˢ Uw).filter (fun e=>rE gs e.1 e.2)
    have hcount_src : EU.card=Uw.card - 1:=by
      have hsum:=Finset.card_eq_sum_card_fiberwise (f:=Prod.fst) (s:=EU) (t:=Uw)
        (fun e he=>(Finset.mem_product.mp (Finset.mem_filter.mp he).1).1)
      have hfib : ∀ w ∈ Uw,(EU.filter (fun e=>e.1=w)).card=if w=out then 0 else 1:=by
        intro w hw
        have hwin : inU w:=(Finset.mem_filter.mp hw).2
        by_cases hwo : w=out
        · rw [if_pos hwo,Finset.card_eq_zero,Finset.eq_empty_iff_forall_notMem]
          intro e he
          obtain ⟨heU,hfst⟩:=Finset.mem_filter.mp he
          have hed : rE gs out e.2:=(hfst.trans hwo) ▸ (Finset.mem_filter.mp heU).2
          have hlt:=rOrd hcl hed
          have hle:=wLO hcl out live e.2
          change e.2.val ≤ out.val at hle;omega
        · rw [if_neg hwo]
          obtain ⟨v,hv⟩:=live w hwo
          have hvin : v ∈ Uw:=Finset.mem_filter.mpr ⟨Finset.mem_univ _,uMem hwin hv⟩
          have heq : EU.filter (fun e=>e.1=w)={(w,v)}:=by
            ext ⟨a,b⟩;simp only [Finset.mem_filter,Finset.mem_product,Finset.mem_singleton,Prod.mk.injEq,EU]
            constructor
            · rintro ⟨⟨⟨_,_⟩,hed⟩,rfl⟩
              exact ⟨rfl,uOut hwin hed hv⟩
            · rintro ⟨rfl,rfl⟩
              exact ⟨⟨⟨hw,hvin⟩,hv⟩,rfl⟩
          rw [heq,Finset.card_singleton]
      rw [hsum,Finset.sum_congr rfl hfib,Finset.sum_ite,Finset.sum_const_zero,zero_add,
          Finset.sum_const,smul_eq_mul,mul_one]
      have hfilt : Uw.filter (fun w=>¬ w=out)=Uw.erase out:=by
        ext w;simp [Finset.mem_erase,and_comm]
      rw [hfilt,Finset.card_erase_of_mem hout_inU]
    have hcount_dst : EU.card=Ug.card + Mg.card:=by
      have hsum:=Finset.card_eq_sum_card_fiberwise (f:=Prod.snd) (s:=EU) (t:=Uw)
        (fun e he=>(Finset.mem_product.mp (Finset.mem_filter.mp he).1).2)
      have hfib : ∀ b ∈ Uw,(EU.filter (fun e=>e.2=b)).card =
          if b.val < 10 then 0 else if b.val - 10 ∈ Mg then 2 else 1:=by
        intro b hb
        have hbin : inU b:=(Finset.mem_filter.mp hb).2
        by_cases h10 : b.val < 10
        · rw [if_pos h10,Finset.card_eq_zero,Finset.eq_empty_iff_forall_notMem]
          intro e he
          obtain ⟨heU,hsnd⟩:=Finset.mem_filter.mp he
          obtain ⟨p,_,_,hbp,_⟩:=(Finset.mem_filter.mp heU).2
          rw [hsnd] at hbp;omega
        · rw [if_neg h10]
          let p:=b.val - 10
          have hplt : p < gs.length:=by have:=b.isLt;omega
          have hb_eq : b=⟨10 + p,by omega⟩:=Fin.ext (by change b.val=10 + (b.val - 10);omega)
          have hpU : p ∈ Ug:=Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hplt,hplt,hb_eq ▸ hbin⟩
          obtain ⟨g,a1,a2,hpg,hin,ha1,ha2,hne12,hor⟩:=hUp hpU
          let w1 : Fin (10 + gs.length):=⟨a1,by omega⟩
          let w2 : Fin (10 + gs.length):=⟨a2,by omega⟩
          have hw_ne : w1 ≠ w2:=fun h=>hne12 (congrArg Fin.val h)
          have hedge_iff : ∀ a : Fin (10 + gs.length),rE gs a b ↔ a=w1 ∨ a=w2:=by
            intro a;constructor
            · rintro ⟨p',g',hp',hbp',ham⟩
              have hpe : p' = p:=by omega
              subst hpe;rw [hpg] at hp';cases hp';rw [hin] at ham
              simp only [List.mem_cons,List.not_mem_nil,or_false] at ham
              rcases ham with h | h
              · exact Or.inl (Fin.ext h)
              · exact Or.inr (Fin.ext h)
            · rintro (rfl | rfl)
              · exact ⟨p,g,hpg,by omega,by rw [hin];simp [w1]⟩
              · exact ⟨p,g,hpg,by omega,by rw [hin];simp [w2]⟩
          by_cases hpM : p ∈ Mg
          · rw [if_pos hpM]
            obtain ⟨_,g',x1,x2,hpg',hin',⟨hx1,hu1⟩,⟨hx2,hu2⟩⟩:=Finset.mem_filter.mp hpM
            rw [hpg] at hpg';cases hpg';rw [hin] at hin'
            have h1e : a1=x1:=by injection hin'
            have h2e : a2=x2:=by injection hin' with _ h2';injection h2'
            subst h1e;subst h2e
            have hw1U : w1 ∈ Uw:=Finset.mem_filter.mpr ⟨Finset.mem_univ _,hu1⟩
            have hw2U : w2 ∈ Uw:=Finset.mem_filter.mpr ⟨Finset.mem_univ _,hu2⟩
            have heq : EU.filter (fun e=>e.2=b)={(w1,b),(w2,b)}:=by
              ext ⟨x,y⟩;simp only [Finset.mem_filter,Finset.mem_product,Finset.mem_insert,
                Finset.mem_singleton,Prod.mk.injEq,EU]
              constructor
              · rintro ⟨⟨⟨_,_⟩,hed⟩,rfl⟩
                rcases (hedge_iff x).mp hed with rfl | rfl<;>simp
              · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
                · exact ⟨⟨⟨hw1U,hb⟩,(hedge_iff w1).mpr (Or.inl rfl)⟩,rfl⟩
                · exact ⟨⟨⟨hw2U,hb⟩,(hedge_iff w2).mpr (Or.inr rfl)⟩,rfl⟩
            rw [heq,Finset.card_pair (fun h=>hw_ne (Prod.mk.inj h).1)]
          · rw [if_neg hpM]
            rcases hor with ⟨ha1',hu1⟩ | ⟨ha2',hu2⟩
            · have hnot2 : ¬ inU w2:=fun hu2 =>
                hpM (Finset.mem_filter.mpr ⟨hpU,g,a1,a2,hpg,hin,⟨ha1',hu1⟩,⟨by omega,hu2⟩⟩)
              have hw1U : w1 ∈ Uw:=Finset.mem_filter.mpr ⟨Finset.mem_univ _,hu1⟩
              have heq : EU.filter (fun e=>e.2=b)={(w1,b)}:=by
                ext ⟨x,y⟩;simp only [Finset.mem_filter,Finset.mem_product,Finset.mem_singleton,Prod.mk.injEq,EU]
                constructor
                · rintro ⟨⟨⟨hxU,_⟩,hed⟩,rfl⟩
                  rcases (hedge_iff x).mp hed with rfl | rfl
                  · exact ⟨rfl,rfl⟩
                  · exact (hnot2 (Finset.mem_filter.mp hxU).2).elim
                · rintro ⟨rfl,rfl⟩
                  exact ⟨⟨⟨hw1U,hb⟩,(hedge_iff w1).mpr (Or.inl rfl)⟩,rfl⟩
              rw [heq,Finset.card_singleton]
            · have hnot1 : ¬ inU w1:=fun hu1 =>
                hpM (Finset.mem_filter.mpr ⟨hpU,g,a1,a2,hpg,hin,⟨by omega,hu1⟩,⟨ha2',hu2⟩⟩)
              have hw2U : w2 ∈ Uw:=Finset.mem_filter.mpr ⟨Finset.mem_univ _,hu2⟩
              have heq : EU.filter (fun e=>e.2=b)={(w2,b)}:=by
                ext ⟨x,y⟩;simp only [Finset.mem_filter,Finset.mem_product,Finset.mem_singleton,Prod.mk.injEq,EU]
                constructor
                · rintro ⟨⟨⟨hxU,_⟩,hed⟩,rfl⟩
                  rcases (hedge_iff x).mp hed with rfl | rfl
                  · exact (hnot1 (Finset.mem_filter.mp hxU).2).elim
                  · exact ⟨rfl,rfl⟩
                · rintro ⟨rfl,rfl⟩
                  exact ⟨⟨⟨hw2U,hb⟩,(hedge_iff w2).mpr (Or.inr rfl)⟩,rfl⟩
              rw [heq,Finset.card_singleton]
      rw [hsum,Finset.sum_congr rfl hfib]
      let fval : Fin (10 + gs.length) → ℕ:=fun b =>
        if b.val < 10 then 0 else if b.val - 10 ∈ Mg then 2 else 1
      have hsplit:=Finset.sum_filter_add_sum_filter_not Uw (fun b=>b.val < 10) fval
      have hz0 : (Uw.filter (fun b=>b.val < 10)).sum fval=0 :=
        Finset.sum_eq_zero fun b hb=>if_pos (Finset.mem_filter.mp hb).2
      have hge10_eq : Uw.filter (fun b=>¬ b.val < 10) =
          Ug.attach.image (fun p=>⟨10 + p.1,by have:=hUr p.1 p.2;omega⟩):=by
        ext b;simp only [Finset.mem_filter,Finset.mem_image,Finset.mem_attach,true_and,Uw,Finset.mem_univ]
        constructor
        · rintro ⟨hbin,h10⟩
          have hplt : b.val - 10 < gs.length:=by have:=b.isLt;omega
          have hb_eq : (⟨10 + (b.val - 10),by omega⟩ : Fin (10 + gs.length))=b:=Fin.ext (by simp;omega)
          exact ⟨⟨b.val - 10,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hplt,hplt,hb_eq.symm ▸ hbin⟩⟩,hb_eq⟩
        · rintro ⟨p,rfl⟩;exact ⟨(hUi p.2).2,by simp⟩
      have hsum_gt : (Uw.filter (fun b=>¬ b.val < 10)).sum fval=Ug.card + Mg.card:=by
        rw [hge10_eq,Finset.sum_image (fun a _ b _ h=>Subtype.ext (by have:=congrArg Fin.val h;change 10 + a.1=10 + b.1 at this;omega))]
        have hstep : (Ug.attach.sum fun p=>fval ⟨10 + p.1,by have:=hUr p.1 p.2;omega⟩) =
            Ug.sum (fun p=>if p ∈ Mg then 2 else 1):=by
          rw [← Finset.sum_attach Ug (fun p=>if p ∈ Mg then 2 else 1)]
          refine Finset.sum_congr rfl fun p _=>?_
          dsimp only [fval]
          rw [if_neg (by omega),show 10 + p.1 - 10=p.1 by omega]
        rw [hstep,Finset.sum_ite,Finset.sum_const,Finset.sum_const,smul_eq_mul,smul_eq_mul]
        have hf1 : Ug.filter (fun p=>p ∈ Mg)=Mg:=by ext p;simp;exact fun h=>hM_sub h
        have hf2 : Ug.filter (fun p=>p ∉ Mg)=Ug \ Mg:=by ext p;simp
        rw [hf1,hf2]
        have hsd:=Finset.card_sdiff_add_card_eq_card hM_sub
        omega
      change Uw.sum fval=Ug.card + Mg.card
      rw [← hsplit,hz0,zero_add,hsum_gt]
    omega
  have uDisj : ∀ {p : ℕ} {g : Gate} {a b : ℕ} (hp : p < gs.length),
      gs[p]?=some g → g.inputs=[a,b] → a ≠ b →
      ∀ (ha : a < 10 + gs.length) (hb : b < 10 + gs.length),
      inU ⟨a,ha⟩ → inU ⟨b,hb⟩ →
      ∀ u ∈ L4,¬ (Relation.ReflTransGen (rE gs) (iW gs u) ⟨a,ha⟩ ∧
                   Relation.ReflTransGen (rE gs) (iW gs u) ⟨b,hb⟩):=by
    intro p g a b hp hpg hin hab ha hb hua hub u hu ⟨ra,rb⟩
    have ha_lt : a < 10 + p:=(hcl p g hpg).lt a (by rw [hin];simp)
    have hb_lt : b < 10 + p:=(hcl p g hpg).lt b (by rw [hin];simp)
    have ea : rE gs ⟨a,ha⟩ ⟨10 + p,by omega⟩:=⟨p,g,hpg,rfl,by rw [hin];simp⟩
    have eb : rE gs ⟨b,hb⟩ ⟨10 + p,by omega⟩:=⟨p,g,hpg,rfl,by rw [hin];simp⟩
    rcases uLam ⟨u,hu,Relation.ReflTransGen.refl⟩ ra rb with rab | rba
    · rcases Relation.ReflTransGen.cases_head rab with heq | ⟨w,eaw,rwb⟩
      · exact hab (congrArg Fin.val heq)
      · have hw_eq : w=⟨10 + p,by omega⟩:=uOut hua eaw ea
        subst hw_eq
        have hle:=FBR.pFwd (rE gs) (rOrd hcl) rwb
        change 10 + p ≤ b at hle;omega
    · rcases Relation.ReflTransGen.cases_head rba with heq | ⟨w,ebw,rwa⟩
      · exact hab (congrArg Fin.val heq).symm
      · have hw_eq : w=⟨10 + p,by omega⟩:=uOut hub ebw eb
        subst hw_eq
        have hle:=FBR.pFwd (rE gs) (rOrd hcl) rwa
        change 10 + p ≤ a at hle;omega
  have mIsO : ∀ p ∈ Mg,∀ g,gs[p]?=some g → g.op=GateOp.or:=by
    intro p hpM g hpg
    have hpU : p ∈ Ug:=hM_sub hpM
    have hplt : p < gs.length:=hUr p hpU
    obtain ⟨hop,a,b,ha_lt,hb_lt,hab,hin⟩:=cmG hcl hmono distinct hpg
    rcases hop with hand | hor
    · exfalso
      obtain ⟨_,g',a',b',hpg',hin',⟨ha',hua⟩,⟨hb',hub⟩⟩:=Finset.mem_filter.mp hpM
      rw [hpg] at hpg';cases hpg';rw [hin] at hin'
      have e1 : a=a':=by injection hin'
      have e2 : b=b':=by injection hin' with _ h2';injection h2'
      subst e1;subst e2
      obtain ⟨u,hu,rau⟩:=hua
      obtain ⟨v,hv,rbv⟩:=hub
      have huv : u ≠ v:=by
        rintro rfl
        exact uDisj hplt hpg hin hab ha' hb' ⟨u,hu,rau⟩ ⟨u,hu,rbv⟩ u hu ⟨rau,rbv⟩
      obtain ⟨m,_,hv0,hvu,hvv,ht0,htu,htv⟩:=pair6_witnesses u v hu hv huv
      let x0:=F27.row m
      let xu:=Function.update x0 u true
      let xv:=Function.update x0 v true
      have hev0 : vl gs x0 out.val=false:=(computes x0 hv0).trans ht0
      have hevu : vl gs xu out.val=true:=(computes xu hvu).trans htu
      have hevv : vl gs xv out.val=true:=(computes xv hvv).trans htv
      let cut : Fin (10 + gs.length):=⟨10 + p,by omega⟩
      have ea : rE gs ⟨a,ha'⟩ cut:=⟨p,g,hpg,rfl,by rw [hin];simp⟩
      have eb : rE gs ⟨b,hb'⟩ cut:=⟨p,g,hpg,rfl,by rw [hin];simp⟩
      have hca0 : ∀ (w : Fin 10) (xw : Fin 10 → Bool),w ∈ L4 →
          Relation.ReflTransGen (rE gs) (iW gs w) cut →
          (∀ i : Fin 10,i ≠ w → x0 i=xw i) →
          vl gs x0 cut.val=vl gs xw cut.val → vl gs x0 out.val=vl gs xw out.val:=by
        intro w xw hw rwc hdiff hsame
        by_cases hco : cut=out
        · rw [← hco];exact hsame
        · apply cca hcl cut out x0 xw hsame
          intro i hi
          have hiw : i=w:=by by_contra hne;exact hi (hdiff i hne)
          subst hiw
          exact uNA hw hco rwc
      have hx0_cut_false : vl gs x0 cut.val=false:=by
        cases hvc : vl gs x0 cut.val
        · rfl
        · exfalso
          have hvu_cut : vl gs xu cut.val=true :=
            vl_mono hcl hmono (fun k hk=>by
              by_cases hku : k=u
              · subst hku;simp [xu]
              · simp [xu,hku,hk]) cut.val hvc
          have heq:=hca0 u xu hu (rau.tail ea) (fun i hi=>by simp [xu,hi]) (hvc.trans hvu_cut.symm)
          rw [hev0,hevu] at heq;cases heq
      have hval_cut : vl gs x0 cut.val=(vl gs x0 a&&vl gs x0 b):=by
        change vl gs x0 (10 + p)=_
        rw [vl_gate gs hcl x0 p g hpg,hand,hin];simp [GateOp.eval]
      rw [hx0_cut_false] at hval_cut
      have hxua_eq : vl gs xu b=vl gs x0 b:=by
        symm;apply vlINR hcl (v:=⟨b,hb'⟩)
        intro k hk
        by_cases hku : k=u
        · rw [hku] at hk
          exact (uDisj hplt hpg hin hab ha' hb' ⟨u,hu,rau⟩ ⟨v,hv,rbv⟩ u hu ⟨rau,hk⟩).elim
        · simp [xu,hku]
      have hxvb_eq : vl gs xv a=vl gs x0 a:=by
        symm;apply vlINR hcl (v:=⟨a,ha'⟩)
        intro k hk
        by_cases hkv : k=v
        · rw [hkv] at hk
          exact (uDisj hplt hpg hin hab ha' hb' ⟨u,hu,rau⟩ ⟨v,hv,rbv⟩ v hv ⟨hk,rbv⟩).elim
        · simp [xv,hkv]
      cases hfa : vl gs x0 a
      · have hvv_cut : vl gs xv cut.val=false:=by
          change vl gs xv (10 + p)=false
          rw [vl_gate gs hcl xv p g hpg,hand,hin];simp [GateOp.eval,hxvb_eq,hfa]
        have heq:=hca0 v xv hv (rbv.tail eb) (fun i hi=>by simp [xv,hi]) (hx0_cut_false.trans hvv_cut.symm)
        rw [hev0,hevv] at heq;cases heq
      · rw [hfa,Bool.true_and] at hval_cut
        have hfb : vl gs x0 b=false:=hval_cut.symm
        have hvu_cut : vl gs xu cut.val=false:=by
          change vl gs xu (10 + p)=false
          rw [vl_gate gs hcl xu p g hpg,hand,hin];simp [GateOp.eval,hxua_eq,hfb]
        have heq:=hca0 u xu hu (rau.tail ea) (fun i hi=>by simp [xu,hi]) (hx0_cut_false.trans hvu_cut.symm)
        rw [hev0,hevu] at heq;cases heq
    · exact hor
  let sW (p : ℕ) : ℕ :=
    match gs[p]? with
    | some g =>
      match g.inputs with
      | [a,b]=>if ∃ ha : a < 10 + gs.length,inU ⟨a,ha⟩ then b else a
      | _=>0
    | none=>0
  let uC (p : ℕ) : ℕ :=
    match gs[p]? with
    | some g =>
      match g.inputs with
      | [a,b]=>if ∃ ha : a < 10 + gs.length,inU ⟨a,ha⟩ then a else b
      | _=>0
    | none=>0
  have hASc : ∀ {p : ℕ},p ∈ Ug \ Mg →
      ∃ g,gs[p]?=some g ∧
        uC p < 10 + p ∧ sW p < 10 + p ∧
        (∃ hu : uC p < 10 + gs.length,inU ⟨uC p,hu⟩) ∧
        (∀ hs : sW p < 10 + gs.length,¬ inU ⟨sW p,hs⟩) ∧
        (∀ (hp' : p < gs.length) (a : Fin (10 + gs.length)),rE gs a ⟨10 + p,by omega⟩ →
          inU a → a.val=uC p) ∧
        (∀ x : Fin 10 → Bool,g.op=GateOp.and → vl gs x (10 + p)=(vl gs x (uC p)&&vl gs x (sW p))) ∧
        (∀ x : Fin 10 → Bool,g.op=GateOp.or → vl gs x (10 + p)=(vl gs x (uC p)||vl gs x (sW p))):=by
    intro p hp
    have hpU : p ∈ Ug:=(Finset.mem_sdiff.mp hp).1
    have hpNM : p ∉ Mg:=(Finset.mem_sdiff.mp hp).2
    have hplt : p < gs.length:=hUr p hpU
    obtain ⟨g,a,b,hpg,hin,ha,hb,hab,hor⟩:=hUp hpU
    have hsw : sW p=if ∃ ha' : a < 10 + gs.length,inU ⟨a,ha'⟩ then b else a:=by
      simp [sW,hpg,hin]
    have huc : uC p=if ∃ ha' : a < 10 + gs.length,inU ⟨a,ha'⟩ then a else b:=by
      simp [uC,hpg,hin]
    by_cases hca : ∃ ha' : a < 10 + gs.length,inU ⟨a,ha'⟩
    · have hnb : ∀ hb' : b < 10 + gs.length,¬ inU ⟨b,hb'⟩:=fun hb' hub =>
        hpNM (Finset.mem_filter.mpr ⟨hpU,g,a,b,hpg,hin,hca,⟨hb',hub⟩⟩)
      rw [if_pos hca] at hsw huc
      refine ⟨g,hpg,by omega,by omega,huc ▸ hca,fun hs hua=>hnb (by omega) (by convert hua;omega),?_,?_,?_⟩
      · intro _ w e hw
        obtain ⟨p',g',hp',hbp',ham⟩:=e
        simp only at hbp'
        have hpe : p' = p:=by omega
        subst hpe;rw [hpg] at hp';cases hp';rw [hin] at ham
        simp only [List.mem_cons,List.not_mem_nil,or_false] at ham
        rcases ham with h | h
        · rw [huc];exact h
        · have hwe : w=⟨b,by omega⟩:=Fin.ext h;exact (hnb (by omega) (hwe ▸ hw)).elim
      · intro x hop;rw [vl_gate gs hcl x p g hpg,hop,hin,huc,hsw];simp [GateOp.eval]
      · intro x hop;rw [vl_gate gs hcl x p g hpg,hop,hin,huc,hsw];simp [GateOp.eval]
    · rcases hor with hca' | hcb
      · exact (hca hca').elim
      · rw [if_neg hca] at hsw huc
        refine ⟨g,hpg,by omega,by omega,huc ▸ hcb,fun hs hua=>hca ⟨by omega,by convert hua;omega⟩,?_,?_,?_⟩
        · intro _ w e hw
          obtain ⟨p',g',hp',hbp',ham⟩:=e
          simp only at hbp'
          have hpe : p' = p:=by omega
          subst hpe;rw [hpg] at hp';cases hp';rw [hin] at ham
          simp only [List.mem_cons,List.not_mem_nil,or_false] at ham
          rcases ham with h | h
          · have hwe : w=⟨a,by omega⟩:=Fin.ext h;exact (hca ⟨by omega,hwe ▸ hw⟩).elim
          · rw [huc];exact h
        · intro x hop;rw [vl_gate gs hcl x p g hpg,hop,hin,huc,hsw];simp [GateOp.eval,Bool.and_comm]
        · intro x hop;rw [vl_gate gs hcl x p g hpg,hop,hin,huc,hsw];simp [GateOp.eval,Bool.or_comm]
  have vl_on_U : ∀ (v : Fin (10 + gs.length)),inU v → ∀ (x : Fin 10 → Bool),
      vl gs x v.val=true ↔
        (∃ u ∈ L4,Relation.ReflTransGen (rE gs) (iW gs u) v ∧ x u=true ∧
          ∀ q ∈ Ag,(∃ hq : q < gs.length,
            Relation.ReflTransGen (rE gs) (iW gs u) ⟨10 + q,by omega⟩ ∧
            Relation.ReflTransGen (rE gs) ⟨10 + q,by omega⟩ v) →
            vl gs x (sW q)=true) ∨
        (∃ s ∈ Sg,∃ hs : s < gs.length,
          Relation.ReflTransGen (rE gs) ⟨10 + s,by omega⟩ v ∧
          vl gs x (sW s)=true ∧
          ∀ q ∈ Ag,(∃ hq : q < gs.length,s < q ∧
            Relation.ReflTransGen (rE gs) (⟨10 + s,Nat.add_lt_add_left hs 10⟩ : Fin (10 + gs.length)) ⟨10 + q,Nat.add_lt_add_left hq 10⟩ ∧
            Relation.ReflTransGen (rE gs) ⟨10 + q,by omega⟩ v) →
            vl gs x (sW q)=true):=by
    intro v
    obtain ⟨vn,hvn⟩:=v
    induction vn using Nat.strong_induction_on with
    | _ vn ih =>
      intro hv x
      by_cases h10 : vn < 10
      · obtain ⟨u0,hu0,heq⟩:=inU_lt10 hv h10
        have hu0v : u0.val=vn:=congrArg Fin.val heq.symm
        rw [vl_input gs x vn h10]
        constructor
        · intro hx
          left
          refine ⟨u0,hu0,heq ▸ Relation.ReflTransGen.refl,by have : u0=⟨vn,h10⟩:=Fin.ext hu0v;rwa [this],?_⟩
          rintro q _ ⟨hq,_,rqv⟩
          have hle:=FBR.pFwd (rE gs) (rOrd hcl) rqv
          change 10 + q ≤ vn at hle;omega
        · rintro (⟨u,_,ruv,hxu,_⟩ | ⟨s,_,hs,rsv,_,_⟩)
          · rcases Relation.ReflTransGen.cases_tail ruv with h | ⟨_,_,e⟩
            · have : u=⟨vn,h10⟩:=Fin.ext (by have:=congrArg Fin.val h;simpa [iW] using this.symm);rwa [← this]
            · obtain ⟨p,_,_,hbp,_⟩:=e;change vn=10 + p at hbp;omega
          · have hle:=FBR.pFwd (rE gs) (rOrd hcl) rsv
            change 10 + s ≤ vn at hle;omega
      · obtain ⟨p,rfl⟩ : ∃ p,vn=10 + p:=⟨vn - 10,by omega⟩
        have hplt : p < gs.length:=by omega
        have hpU : p ∈ Ug:=Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hplt,hplt,hv⟩
        let vfin : Fin (10 + gs.length):=⟨10 + p,hvn⟩
        by_cases hpM : p ∈ Mg
        · obtain ⟨_,g,a,b,hpg,hin,⟨ha,hua⟩,⟨hb,hub⟩⟩:=Finset.mem_filter.mp hpM
          have hor:=mIsO p hpM g hpg
          have ha_lt : a < 10 + p:=(hcl p g hpg).lt a (by rw [hin];simp)
          have hb_lt : b < 10 + p:=(hcl p g hpg).lt b (by rw [hin];simp)
          have hab : a ≠ b:=by
            have:=(cmG hcl hmono distinct hpg).2
            obtain ⟨a',b',_,_,hne,hin'⟩:=this
            rw [hin] at hin';injection hin' with e1 h2';injection h2' with e2;subst e1;subst e2;exact hne
          have ea : rE gs ⟨a,ha⟩ vfin:=⟨p,g,hpg,rfl,by rw [hin];simp⟩
          have eb : rE gs ⟨b,hb⟩ vfin:=⟨p,g,hpg,rfl,by rw [hin];simp⟩
          have hpv0 : ∀ {w : Fin (10 + gs.length)},w ≠ vfin →
              Relation.ReflTransGen (rE gs) w vfin →
              Relation.ReflTransGen (rE gs) w ⟨a,ha⟩ ∨ Relation.ReflTransGen (rE gs) w ⟨b,hb⟩:=by
            intro w hne rwv
            rcases Relation.ReflTransGen.cases_tail rwv with rfl | ⟨c,rwc,ecv⟩
            · exact (hne rfl).elim
            · obtain ⟨p',g',hp',hbp',hcm⟩:=ecv
              change 10 + p=10 + p' at hbp'
              have hpe : p' = p:=by omega
              subst hpe;rw [hpg] at hp';cases hp';rw [hin] at hcm
              simp only [List.mem_cons,List.not_mem_nil,or_false] at hcm
              rcases hcm with h | h
              · have hce : c=⟨a,ha⟩:=Fin.ext h;exact Or.inl (hce ▸ rwc)
              · have hce : c=⟨b,hb⟩:=Fin.ext h;exact Or.inr (hce ▸ rwc)
          have hsq0 : ∀ {w : Fin (10 + gs.length)},inU w →
              ∀ {q : ℕ} (hq : q < gs.length),q ∈ Ag →
              Relation.ReflTransGen (rE gs) w ⟨a,ha⟩ →
              Relation.ReflTransGen (rE gs) w ⟨10 + q,by omega⟩ →
              Relation.ReflTransGen (rE gs) ⟨10 + q,by omega⟩ vfin →
              Relation.ReflTransGen (rE gs) ⟨10 + q,by omega⟩ ⟨a,ha⟩:=by
            intro w hw q hq hqA rwa rwq rqv
            have hqp : q ≠ p:=fun h=>by subst h;exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hqA).1).2 hpM
            rcases hpv0 (fun h=>hqp (by have:=congrArg Fin.val h;change 10 + q=10 + p at this;omega)) rqv with rqa | rqb
            · exact rqa
            · obtain ⟨u,hu,ruw⟩:=hw
              exact (uDisj hplt hpg hin hab ha hb hua hub u hu
                ⟨ruw.trans rwa,(ruw.trans rwq).trans rqb⟩).elim
          have hsqb : ∀ {w : Fin (10 + gs.length)},inU w →
              ∀ {q : ℕ} (hq : q < gs.length),q ∈ Ag →
              Relation.ReflTransGen (rE gs) w ⟨b,hb⟩ →
              Relation.ReflTransGen (rE gs) w ⟨10 + q,by omega⟩ →
              Relation.ReflTransGen (rE gs) ⟨10 + q,by omega⟩ vfin →
              Relation.ReflTransGen (rE gs) ⟨10 + q,by omega⟩ ⟨b,hb⟩:=by
            intro w hw q hq hqA rwb rwq rqv
            have hqp : q ≠ p:=fun h=>by subst h;exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hqA).1).2 hpM
            rcases hpv0 (fun h=>hqp (by have:=congrArg Fin.val h;change 10 + q=10 + p at this;omega)) rqv with rqa | rqb
            · obtain ⟨u,hu,ruw⟩:=hw
              exact (uDisj hplt hpg hin hab ha hb hua hub u hu
                ⟨(ruw.trans rwq).trans rqa,ruw.trans rwb⟩).elim
            · exact rqb
          have hval : vl gs x (10 + p)=true ↔ vl gs x a=true ∨ vl gs x b=true:=by
            rw [vl_gate gs hcl x p g hpg,hor,hin];simp [GateOp.eval]
          rw [hval,ih a ha_lt ha hua x,ih b hb_lt hb hub x]
          constructor
          · rintro ((⟨u,hu,rua,hxu,hall⟩ | ⟨s,hsS,hs,rsa,hxs,hall⟩) |
                    (⟨u,hu,rub,hxu,hall⟩ | ⟨s,hsS,hs,rsb,hxs,hall⟩))
            · left;refine ⟨u,hu,rua.tail ea,hxu,fun q hqA ⟨hq,ruq,rqv⟩ =>
                hall q hqA ⟨hq,ruq,hsq0 ⟨u,hu,Relation.ReflTransGen.refl⟩ hq hqA rua ruq rqv⟩⟩
            · right;refine ⟨s,hsS,hs,rsa.tail ea,hxs,fun q hqA ⟨hq,hsq,rsq,rqv⟩ =>
                hall q hqA ⟨hq,hsq,rsq,hsq0 (hUi (hS_sub hsS)).2 hq hqA rsa rsq rqv⟩⟩
            · left;refine ⟨u,hu,rub.tail eb,hxu,fun q hqA ⟨hq,ruq,rqv⟩ =>
                hall q hqA ⟨hq,ruq,hsqb ⟨u,hu,Relation.ReflTransGen.refl⟩ hq hqA rub ruq rqv⟩⟩
            · right;refine ⟨s,hsS,hs,rsb.tail eb,hxs,fun q hqA ⟨hq,hsq,rsq,rqv⟩ =>
                hall q hqA ⟨hq,hsq,rsq,hsqb (hUi (hS_sub hsS)).2 hq hqA rsb rsq rqv⟩⟩
          · rintro (⟨u,hu,ruv,hxu,hall⟩ | ⟨s,hsS,hs,rsv,hxs,hall⟩)
            · have hne : iW gs u ≠ vfin:=fun h=>by
                have:=congrArg Fin.val h;change u.val=10 + p at this;have:=u.isLt;omega
              rcases hpv0 hne ruv with rua | rub
              · exact Or.inl (Or.inl ⟨u,hu,rua,hxu,fun q hqA ⟨hq,ruq,rqa⟩=>hall q hqA ⟨hq,ruq,rqa.tail ea⟩⟩)
              · exact Or.inr (Or.inl ⟨u,hu,rub,hxu,fun q hqA ⟨hq,ruq,rqb⟩=>hall q hqA ⟨hq,ruq,rqb.tail eb⟩⟩)
            · have hsp : s ≠ p:=fun h=>by subst h;exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hsS).1).2 hpM
              rcases hpv0 (fun h=>hsp (by have:=congrArg Fin.val h;change 10 + s=10 + p at this;omega)) rsv with rsa | rsb
              · exact Or.inl (Or.inr ⟨s,hsS,hs,rsa,hxs,fun q hqA ⟨hq,hsq,rsq,rqa⟩=>hall q hqA ⟨hq,hsq,rsq,rqa.tail ea⟩⟩)
              · exact Or.inr (Or.inr ⟨s,hsS,hs,rsb,hxs,fun q hqA ⟨hq,hsq,rsq,rqb⟩=>hall q hqA ⟨hq,hsq,rsq,rqb.tail eb⟩⟩)
        · have hpUM : p ∈ Ug \ Mg:=Finset.mem_sdiff.mpr ⟨hpU,hpM⟩
          obtain ⟨g,hpg,huc_lt,hsw_lt,⟨huc_fin,huc_inU⟩,_,huniq_pred,hand_ev,hor_ev⟩:=hASc hpUM
          let vc : Fin (10 + gs.length):=⟨uC p,huc_fin⟩
          have hec : rE gs vc vfin:=by
            have:=hUp hpU
            obtain ⟨g',a,b,hpg',hin',_,_,_,_⟩:=this
            rw [hpg] at hpg';cases hpg'
            refine ⟨p,g,hpg,rfl,?_⟩
            change uC p ∈ g.inputs
            simp only [uC,hpg,hin']
            split_ifs<;>simp [hin']
          have hpvc : ∀ {w : Fin (10 + gs.length)},inU w → w ≠ vfin →
              Relation.ReflTransGen (rE gs) w vfin →
              Relation.ReflTransGen (rE gs) w vc:=by
            intro w hw hne rwv
            rcases Relation.ReflTransGen.cases_tail rwv with rfl | ⟨c,rwc,ecv⟩
            · exact (hne rfl).elim
            · have hcin : inU c:=by
                obtain ⟨u,hu,ruw⟩:=hw;exact ⟨u,hu,ruw.trans rwc⟩
              have hc_eq : c=vc:=Fin.ext (huniq_pred hplt c ecv hcin)
              rwa [← hc_eq]
          rcases (cmG hcl hmono distinct hpg).1 with hop | hop
          · have hpA : p ∈ Ag:=Finset.mem_filter.mpr ⟨hpUM,g,hpg,hop⟩
            have hpNS : p ∉ Sg:=fun h=>by
              obtain ⟨_,g',hpg',ho'⟩:=Finset.mem_filter.mp h
              rw [hpg] at hpg';cases hpg';rw [hop] at ho';cases ho'
            have hval : vl gs x (10 + p)=true ↔ vl gs x (uC p)=true ∧ vl gs x (sW p)=true:=by
              rw [hand_ev x hop,Bool.and_eq_true]
            rw [hval,ih (uC p) huc_lt huc_fin huc_inU x]
            constructor
            · rintro ⟨(⟨u,hu,ruc,hxu,hall⟩ | ⟨s,hsS,hs,rsc,hxs,hall⟩),hswx⟩
              · left;refine ⟨u,hu,ruc.tail hec,hxu,?_⟩
                rintro q hqA ⟨hq,ruq,rqv⟩
                by_cases hqp : q=p
                · subst hqp;exact hswx
                · exact hall q hqA ⟨hq,ruq,hpvc (hUi (hA_sub hqA)).2
                    (fun h=>hqp (by have:=congrArg Fin.val h;change 10 + q=10 + p at this;omega)) rqv⟩
              · right;refine ⟨s,hsS,hs,rsc.tail hec,hxs,?_⟩
                rintro q hqA ⟨hq,hsq,rsq,rqv⟩
                by_cases hqp : q=p
                · subst hqp;exact hswx
                · exact hall q hqA ⟨hq,hsq,rsq,hpvc (hUi (hA_sub hqA)).2
                    (fun h=>hqp (by have:=congrArg Fin.val h;change 10 + q=10 + p at this;omega)) rqv⟩
            · rintro (⟨u,hu,ruv,hxu,hall⟩ | ⟨s,hsS,hs,rsv,hxs,hall⟩)
              · have hne : iW gs u ≠ vfin:=fun h=>by
                  have:=congrArg Fin.val h;change u.val=10 + p at this;have:=u.isLt;omega
                refine ⟨Or.inl ⟨u,hu,hpvc ⟨u,hu,Relation.ReflTransGen.refl⟩ hne ruv,hxu,
                  fun q hqA ⟨hq,ruq,rqc⟩=>hall q hqA ⟨hq,ruq,rqc.tail hec⟩⟩,
                  hall p hpA ⟨hplt,ruv,Relation.ReflTransGen.refl⟩⟩
              · have hsp : s ≠ p:=fun h=>hpNS (h ▸ hsS)
                have rsc:=hpvc (hUi (hS_sub hsS)).2 (fun h=>hsp (by have:=congrArg Fin.val h;change 10 + s=10 + p at this;omega)) rsv
                have hlt_sp : s < p:=by
                  have hle:=FBR.pFwd (rE gs) (rOrd hcl) rsc
                  change 10 + s ≤ uC p at hle;omega
                refine ⟨Or.inr ⟨s,hsS,hs,rsc,hxs,
                  fun q hqA ⟨hq,hsq,rsq,rqc⟩=>hall q hqA ⟨hq,hsq,rsq,rqc.tail hec⟩⟩,
                  hall p hpA ⟨hplt,hlt_sp,rsv,Relation.ReflTransGen.refl⟩⟩
          · have hpS : p ∈ Sg:=Finset.mem_filter.mpr ⟨hpUM,g,hpg,hop⟩
            have hpNA : p ∉ Ag:=fun h=>by
              obtain ⟨_,g',hpg',ho'⟩:=Finset.mem_filter.mp h
              rw [hpg] at hpg';cases hpg';rw [hop] at ho';cases ho'
            have hval : vl gs x (10 + p)=true ↔ vl gs x (uC p)=true ∨ vl gs x (sW p)=true:=by
              rw [hor_ev x hop,Bool.or_eq_true]
            rw [hval,ih (uC p) huc_lt huc_fin huc_inU x]
            constructor
            · rintro ((⟨u,hu,ruc,hxu,hall⟩ | ⟨s,hsS,hs,rsc,hxs,hall⟩) | hswx)
              · left;refine ⟨u,hu,ruc.tail hec,hxu,fun q hqA ⟨hq,ruq,rqv⟩=>?_⟩
                have hqp : q ≠ p:=fun h=>hpNA (h ▸ hqA)
                exact hall q hqA ⟨hq,ruq,hpvc (hUi (hA_sub hqA)).2
                  (fun h=>hqp (by have:=congrArg Fin.val h;change 10 + q=10 + p at this;omega)) rqv⟩
              · right;refine ⟨s,hsS,hs,rsc.tail hec,hxs,fun q hqA ⟨hq,hsq,rsq,rqv⟩=>?_⟩
                have hqp : q ≠ p:=fun h=>hpNA (h ▸ hqA)
                exact hall q hqA ⟨hq,hsq,rsq,hpvc (hUi (hA_sub hqA)).2
                  (fun h=>hqp (by have:=congrArg Fin.val h;change 10 + q=10 + p at this;omega)) rqv⟩
              · right;refine ⟨p,hpS,hplt,Relation.ReflTransGen.refl,hswx,?_⟩
                rintro q _ ⟨hq,hpq,_,rqv⟩
                have hle:=FBR.pFwd (rE gs) (rOrd hcl) rqv
                change 10 + q ≤ 10 + p at hle;omega
            · rintro (⟨u,hu,ruv,hxu,hall⟩ | ⟨s,hsS,hs,rsv,hxs,hall⟩)
              · have hne : iW gs u ≠ vfin:=fun h=>by
                  have:=congrArg Fin.val h;change u.val=10 + p at this;have:=u.isLt;omega
                exact Or.inl (Or.inl ⟨u,hu,hpvc ⟨u,hu,Relation.ReflTransGen.refl⟩ hne ruv,hxu,
                  fun q hqA ⟨hq,ruq,rqc⟩=>hall q hqA ⟨hq,ruq,rqc.tail hec⟩⟩)
              · by_cases hsp : s=p
                · subst hsp;exact Or.inr hxs
                · exact Or.inl (Or.inr ⟨s,hsS,hs,
                    hpvc (hUi (hS_sub hsS)).2 (fun h=>hsp (by have:=congrArg Fin.val h;change 10 + s=10 + p at this;omega)) rsv,
                    hxs,fun q hqA ⟨hq,hsq,rsq,rqc⟩=>hall q hqA ⟨hq,hsq,rsq,rqc.tail hec⟩⟩)
  let Al : List ℕ:=Ag.toList
  let Sl : List ℕ:=Sg.toList
  let rU (u : Fin 10) (q : ℕ) : Prop :=
    ∃ hq : q < gs.length,Relation.ReflTransGen (rE gs) (iW gs u) ⟨10 + q,by omega⟩
  let rS (s q : ℕ) : Prop :=
    ∃ hs : s < gs.length,∃ hq : q < gs.length,s < q ∧
      Relation.ReflTransGen (rE gs) (⟨10 + s,Nat.add_lt_add_left hs 10⟩ : Fin (10 + gs.length)) ⟨10 + q,Nat.add_lt_add_left hq 10⟩
  let Aau (u : Fin 10) : List ℕ:=Al.filter (fun q=>decide (rU u q))
  let Bo (u : Fin 10) : ℕ:=landMask ((Aau u).map (fun q=>tt64 gs (sW q)))
  let Aas (s : ℕ) : List ℕ:=Al.filter (fun q=>decide (rS s q))
  let Fo (s : ℕ) : ℕ:=landMask ((Aas s).map (fun q=>tt64 gs (sW q)))
  let zo (s : ℕ) : ℕ:=tt64 gs (sW s)&&&Fo s
  have hB_tb : ∀ u i,i < 64 →
      ((Bo u).testBit i=true ↔ ∀ q ∈ Ag,rU u q → vl gs (pt64 i) (sW q)=true):=by
    intro u i hi
    simp only [Bo,tbLM,hi,decide_true,Bool.true_and,List.all_eq_true,
      List.mem_map,List.mem_filter,Aau,Al,Finset.mem_toList,decide_eq_true_eq]
    constructor
    · intro h q hq hru
      have ht:=h (tt64 gs (sW q)) ⟨q,⟨hq,hru⟩,rfl⟩
      rw [tbT64] at ht;simpa [hi] using ht
    · rintro h _ ⟨q,⟨hq,hru⟩,rfl⟩
      rw [tbT64];simp [hi,h q hq hru]
  have hF_tb : ∀ s i,i < 64 →
      ((Fo s).testBit i=true ↔ ∀ q ∈ Ag,rS s q → vl gs (pt64 i) (sW q)=true):=by
    intro s i hi
    simp only [Fo,tbLM,hi,decide_true,Bool.true_and,List.all_eq_true,
      List.mem_map,List.mem_filter,Aas,Al,Finset.mem_toList,decide_eq_true_eq]
    constructor
    · intro h q hq hrs
      have ht:=h (tt64 gs (sW q)) ⟨q,⟨hq,hrs⟩,rfl⟩
      rw [tbT64] at ht;simpa [hi] using ht
    · rintro h _ ⟨q,⟨hq,hrs⟩,rfl⟩
      rw [tbT64];simp [hi,h q hq hrs]
  have hz_tb : ∀ s i,i < 64 →
      ((zo s).testBit i=true ↔
        vl gs (pt64 i) (sW s)=true ∧
        ∀ q ∈ Ag,rS s q → vl gs (pt64 i) (sW q)=true):=by
    intro s i hi
    rw [show zo s=tt64 gs (sW s)&&&Fo s from rfl,Nat.testBit_and,Bool.and_eq_true,
        tbT64,hF_tb s i hi]
    simp [hi]
  have hsnU : ∀ {p},p ∈ Ug \ Mg →
      ∃ hlt : sW p < 10 + gs.length,¬ inU ⟨sW p,hlt⟩:=by
    intro p hp
    have hplt:=hUr p (Finset.mem_sdiff.mp hp).1
    obtain ⟨_,_,_,hsw_lt,_,hnot,_,_,_⟩:=hASc hp
    exact ⟨by omega,hnot (by omega)⟩
  have hsi : ∀ {p},p ∈ Ug \ Mg → ∀ {x y : Fin 10 → Bool},
      (∀ k : Fin 10,k ∉ L4 → x k=y k) → vl gs x (sW p)=vl gs y (sW p):=by
    intro p hp x y hag
    obtain ⟨hlt,hnot⟩:=hsnU hp
    exact vlIL4 hlt hnot hag
  have vlO64 : ∀ {i : ℕ} (hi : i < 64) {x : Fin 10 → Bool},
      (∀ k : Fin 10,k ∉ L4 → x k=pt64 i k) →
      (vl gs x out.val=true ↔
        (∃ u ∈ L4,x u=true ∧ (Bo u).testBit i=true) ∨
        (∃ s ∈ Sg,(zo s).testBit i=true)):=by
    intro i hi x hag
    rw [vl_on_U out (Finset.mem_filter.mp hout_inU).2 x]
    constructor
    · rintro (⟨u,hu,_,hxu,hall⟩ | ⟨s,hsS,hs,_,hxs,hall⟩)
      · left;refine ⟨u,hu,hxu,(hB_tb u i hi).mpr fun q hqA ⟨hq,ruq⟩=>?_⟩
        rw [← hsi (Finset.mem_filter.mp hqA).1 hag]
        exact hall q hqA ⟨hq,ruq,uRch (hUi (hA_sub hqA)).2⟩
      · right;refine ⟨s,hsS,(hz_tb s i hi).mpr ⟨?_,fun q hqA ⟨_,hq,hsq,rsq⟩=>?_⟩⟩
        · rw [← hsi (Finset.mem_filter.mp hsS).1 hag];exact hxs
        · rw [← hsi (Finset.mem_filter.mp hqA).1 hag]
          exact hall q hqA ⟨hq,hsq,rsq,uRch (hUi (hA_sub hqA)).2⟩
    · rintro (⟨u,hu,hxu,hBi⟩ | ⟨s,hsS,hzi⟩)
      · left;refine ⟨u,hu,uRch ⟨u,hu,Relation.ReflTransGen.refl⟩,hxu,?_⟩
        rintro q hqA ⟨hq,ruq,_⟩
        rw [hsi (Finset.mem_filter.mp hqA).1 hag]
        exact (hB_tb u i hi).mp hBi q hqA ⟨hq,ruq⟩
      · right
        have hs:=hUr s (hS_sub hsS)
        obtain ⟨hxs,hall⟩:=(hz_tb s i hi).mp hzi
        refine ⟨s,hsS,hs,uRch (hUi (hS_sub hsS)).2,?_,?_⟩
        · rw [hsi (Finset.mem_filter.mp hsS).1 hag];exact hxs
        · rintro q hqA ⟨hq,hsq,rsq,_⟩
          rw [hsi (Finset.mem_filter.mp hqA).1 hag]
          exact hall q hqA ⟨hs,hq,hsq,rsq⟩
  have hB_mono : ∀ u {i j : ℕ},i < 64 → j < 64 →
      (∀ k : Fin 10,pt64 i k=true → pt64 j k=true) →
      (Bo u).testBit i=true → (Bo u).testBit j=true:=by
    intro u i j hi hj hle hbi
    rw [hB_tb u j hj]
    intro q hq hru
    exact vl_mono hcl hmono hle (sW q) ((hB_tb u i hi).mp hbi q hq hru)
  have hz_mono : ∀ s {i j : ℕ},i < 64 → j < 64 →
      (∀ k : Fin 10,pt64 i k=true → pt64 j k=true) →
      (zo s).testBit i=true → (zo s).testBit j=true:=by
    intro s i j hi hj hle hzi
    obtain ⟨h1,h2⟩:=(hz_tb s i hi).mp hzi
    exact (hz_tb s j hj).mpr ⟨vl_mono hcl hmono hle (sW s) h1,
      fun q hq hrs=>vl_mono hcl hmono hle (sW q) (h2 q hq hrs)⟩
  have hpt64_L4_false : ∀ i,∀ u ∈ L4,pt64 i u=false:=by
    intro i u hu;rw [mem_L4] at hu;rcases hu with rfl | rfl | rfl | rfl<;>rfl
  have hz_safe : ∀ s ∈ Sg,(zo s&&&IND_SAFE)=0:=by
    intro s hsS
    apply Nat.eq_of_testBit_eq;intro i
    rw [Nat.testBit_and,Nat.zero_testBit]
    by_cases hi : i < 64
    · cases hs : IND_SAFE.testBit i
      · simp
      · rw [pp2.2.2.2.2.2.2.2.2.2.2,Nat.testBit_or,Bool.or_eq_true] at hs
        have hzf : (zo s).testBit i=false:=by
          cases hzb : (zo s).testBit i
          · rfl
          · exfalso
            rcases hs with hlow | hi3
            · have hi32 : i < 32:=by
                by_contra hge
                have hf:=tbFlt i mbP.1.2.2.2.2.2.2.2.2.1 (by omega)
                rw [hf] at hlow;cases hlow
              obtain ⟨hv,ht⟩:=pp1.1 ⟨i,hi32⟩
              have hval:=(vlO64 hi (fun k _=>rfl)).mpr (Or.inr ⟨s,hsS,hzb⟩)
              rw [computes (pt64 i) hv,ht hlow] at hval;cases hval
            · have hi32 : 32 ≤ i:=by
                by_contra hlt
                have hf:=mbP.1.2.2.2.2.2.2.2.2.2.2.2 ⟨i,by omega⟩
                rw [hf] at hi3;cases hi3
              obtain ⟨hv,ht⟩:=pp1.2.1 ⟨i,hi⟩ hi32
              let x:=Function.update (pt64 i) 3 true
              have hag : ∀ k : Fin 10,k ∉ L4 → x k=pt64 i k:=fun k hk=>by
                have hk3 : k ≠ 3:=fun h=>hk (h ▸ by simp [L4])
                simp [x,hk3]
              have hval:=(vlO64 hi hag).mpr (Or.inr ⟨s,hsS,hzb⟩)
              rw [computes x hv,ht hi3] at hval;cases hval
        simp [hzf]
    · have hf:=tbFlt i mbP.1.2.2.2.2.2.2.2.2.2.2.1 (by omega)
      simp [hf]
  have hz_cov : (Sl.map zo).foldl (fun acc z=>acc|||edgesOf z) 0=15:=by
    have hhit : ∀ i : ℕ,i < 32 → F27.target (pt64 i)=true →
        ∃ s ∈ Sg,(zo s).testBit i=true:=by
      intro i hi32 ht
      have hv:=(pp1.1 ⟨i,hi32⟩).1
      have hval : vl gs (pt64 i) out.val=true:=(computes (pt64 i) hv).trans ht
      rcases (vlO64 (by omega) (fun k _=>rfl)).mp hval with ⟨u,hu,hxu,_⟩ | ⟨s,hsS,hzi⟩
      · rw [hpt64_L4_false i u hu] at hxu;cases hxu
      · exact ⟨s,hsS,hzi⟩
    have ht_all:=pp2.2.2.2.2.2.2
    obtain ⟨s3,hs3,hz3⟩:=hhit 3 (by omega) ht_all.1
    obtain ⟨s6,hs6,hz6⟩:=hhit 6 (by omega) ht_all.2.1
    obtain ⟨s9,hs9,hz9⟩:=hhit 9 (by omega) ht_all.2.2.1
    obtain ⟨s24,hs24,hz24⟩:=hhit 24 (by omega) ht_all.2.2.2.1
    apply Nat.eq_of_testBit_eq;intro k
    rw [tbFoE]
    have hmem_s : ∀ s ∈ Sg,zo s ∈ Sl.map zo:=fun s hs =>
      List.mem_map.mpr ⟨s,Finset.mem_toList.mpr hs,rfl⟩
    have he_bit : ∀ z b j,b=1<<<j → z.testBit j=true → ((z&&&b) != 0)=true:=by
      intro z b j rfl hzj
      simp only [bne_iff_ne,ne_eq]
      intro h0
      have hi:=congrArg (fun n=>n.testBit j) h0
      simp only [Nat.testBit_and,Nat.testBit_shiftLeft,le_refl,decide_true,Nat.sub_self,
        Nat.testBit_one_zero,Bool.and_true,hzj,Nat.zero_testBit] at hi
      cases hi
    rcases k with _ | _ | _ | _ | k
    · simp only [List.any_eq_true,show (15 : ℕ).testBit 0=true by decide,iff_true]
      refine ⟨zo s3,hmem_s s3 hs3,?_⟩
      unfold edgesOf;rw [he_bit _ E01 3 (by decide) hz3]
      cases ((zo s3&&&E12) != 0)<;>cases ((zo s3&&&E05) != 0)<;>cases ((zo s3&&&E58) != 0)<;>decide
    · simp only [List.any_eq_true,show (15 : ℕ).testBit 1=true by decide,iff_true]
      refine ⟨zo s6,hmem_s s6 hs6,?_⟩
      unfold edgesOf;rw [he_bit _ E12 6 (by decide) hz6]
      cases ((zo s6&&&E01) != 0)<;>cases ((zo s6&&&E05) != 0)<;>cases ((zo s6&&&E58) != 0)<;>decide
    · simp only [List.any_eq_true,show (15 : ℕ).testBit 2=true by decide,iff_true]
      refine ⟨zo s9,hmem_s s9 hs9,?_⟩
      unfold edgesOf;rw [he_bit _ E05 9 (by decide) hz9]
      cases ((zo s9&&&E01) != 0)<;>cases ((zo s9&&&E12) != 0)<;>cases ((zo s9&&&E58) != 0)<;>decide
    · simp only [List.any_eq_true,show (15 : ℕ).testBit 3=true by decide,iff_true]
      refine ⟨zo s24,hmem_s s24 hs24,?_⟩
      unfold edgesOf;rw [he_bit _ E58 24 (by decide) hz24]
      cases ((zo s24&&&E01) != 0)<;>cases ((zo s24&&&E12) != 0)<;>cases ((zo s24&&&E05) != 0)<;>decide
    · have h15f : (15 : ℕ).testBit (k + 4)=false :=
        Nat.testBit_lt_two_pow (by have : 2 ^ 4 ≤ 2 ^ (k + 4):=Nat.pow_le_pow_right (by omega) (by omega);omega)
      rw [h15f]
      apply Bool.eq_false_iff.mpr
      intro h;obtain ⟨z,_,hzk⟩:=List.any_eq_true.mp h
      have hf:=tbFlt (k + 4) (show edgesOf z < 2 ^ 4 from edgesOf_lt16 z) (by omega)
      rw [hf] at hzk;cases hzk
  have hS_pos : 1 ≤ Sg.card:=by
    by_contra h0
    have hemp : Sg=∅:=Finset.card_eq_zero.mp (by omega)
    have hnil : Sl=[]:=by simp [Sl,hemp]
    rw [hnil] at hz_cov;simp at hz_cov
  have hB_R0 : (Bo 3&&&R0_3)=0 ∧ (Bo 4&&&R0_4)=0 ∧
               (Bo 6&&&R0_6)=0 ∧ (Bo 7&&&R0_7)=0:=by
    have hzero_from_x : ∀ (u : Fin 10) (R0 : ℕ),u ∈ L4 → R0 < 2 ^ 64 →
        (∀ i : Fin 64,R0.testBit i.val=true →
          ∃ x : Fin 10 → Bool,(∀ k : Fin 10,k ∉ L4 → x k=pt64 i.val k) ∧
            x u=true ∧ F27.valid x ∧ F27.target x=false) →
        (Bo u&&&R0)=0:=by
      intro u R0 hu hR0lt hpts
      apply Nat.eq_of_testBit_eq;intro i
      rw [Nat.testBit_and,Nat.zero_testBit]
      by_cases hi : i < 64
      · cases hr : R0.testBit i
        · simp
        · obtain ⟨x,hag,hxu,hv,ht⟩:=hpts ⟨i,hi⟩ hr
          have hbf : (Bo u).testBit i=false:=by
            cases hbb : (Bo u).testBit i
            · rfl
            · exfalso
              have hval:=(vlO64 hi hag).mpr (Or.inl ⟨u,hu,hxu,hbb⟩)
              rw [computes x hv,ht] at hval;cases hval
          simp [hbf]
      · have hf:=tbFlt i hR0lt (by omega)
        simp [hf]
    refine ⟨?_,?_,?_,?_⟩
    · apply hzero_from_x 3 R0_3 (by simp [L4]) mbP.1.2.2.2.2.1
      intro i hr
      obtain ⟨_,hv,ht⟩:=pp1.2.2.1 i hr
      exact ⟨Function.update (pt64 i.val) 3 true,
        fun k hk=>by have : k ≠ 3:=fun h=>hk (h ▸ by simp [L4]);simp [this],
        by simp,hv,ht⟩
    · apply hzero_from_x 4 R0_4 (by simp [L4]) mbP.1.2.2.2.2.2.1
      intro i hr
      obtain ⟨_,hv,ht⟩:=pp1.2.2.2.1 i hr
      exact ⟨Function.update (pt64 i.val) 4 true,
        fun k hk=>by have : k ≠ 4:=fun h=>hk (h ▸ by simp [L4]);simp [this],
        by simp,hv,ht⟩
    · apply hzero_from_x 6 R0_6 (by simp [L4]) mbP.1.2.2.2.2.2.2.1
      intro i hr
      rcases pp1.2.2.2.2.1 i hr with ⟨_,hv,ht⟩ | ⟨heq,hv,ht⟩
      · exact ⟨Function.update (pt64 i.val) 6 true,
          fun k hk=>by have : k ≠ 6:=fun h=>hk (h ▸ by simp [L4]);simp [this],
          by simp,hv,ht⟩
      · rw [heq]
        exact ⟨Function.update (Function.update (pt64 32) 3 true) 6 true,
          fun k hk=>by
            have hk3 : k ≠ 3:=fun h=>hk (h ▸ by simp [L4])
            have hk6 : k ≠ 6:=fun h=>hk (h ▸ by simp [L4])
            simp [hk3,hk6],
          by simp,hv,ht⟩
    · apply hzero_from_x 7 R0_7 (by simp [L4]) mbP.1.2.2.2.2.2.2.2.1
      intro i hr
      rcases pp1.2.2.2.2.2 i hr with ⟨_,hv,ht⟩ | ⟨heq,hv,ht⟩
      · exact ⟨Function.update (pt64 i.val) 7 true,
          fun k hk=>by have : k ≠ 7:=fun h=>hk (h ▸ by simp [L4]);simp [this],
          by simp,hv,ht⟩
      · rw [heq]
        exact ⟨Function.update (Function.update (pt64 32) 3 true) 7 true,
          fun k hk=>by
            have hk3 : k ≠ 3:=fun h=>hk (h ▸ by simp [L4])
            have hk7 : k ≠ 7:=fun h=>hk (h ▸ by simp [L4])
            simp [hk3,hk7],
          by simp,hv,ht⟩
  have hz_zero_at : ∀ i,i < 64 → (IND_LOW.testBit i=true ∨ IND_3.testBit i=true) →
      ∀ s ∈ Sg,(zo s).testBit i=false:=by
    intro i _ hor s hsS
    have h0:=congrArg (fun n=>n.testBit i) (hz_safe s hsS)
    rw [Nat.testBit_and,Nat.zero_testBit,pp2.2.2.2.2.2.2.2.2.2.2,Nat.testBit_or] at h0
    rcases hor with h | h<;>simp [h] at h0<;>exact h0
  have hB_one_at : ∀ (u : Fin 10) (i : ℕ),u ∈ L4 → i < 64 →
      F27.valid (Function.update (pt64 i) u true) →
      F27.target (Function.update (pt64 i) u true)=true →
      (∀ s ∈ Sg,(zo s).testBit i=false) →
      (Bo u).testBit i=true:=by
    intro u i hu hi hv ht hzf
    let x:=Function.update (pt64 i) u true
    have hag : ∀ k : Fin 10,k ∉ L4 → x k=pt64 i k:=fun k hk=>by
      have hku : k ≠ u:=fun h=>hk (h ▸ hu)
      simp [x,hku]
    have hval : vl gs x out.val=true:=(computes x hv).trans ht
    rcases (vlO64 hi hag).mp hval with ⟨v,hvL,hxv,hBv⟩ | ⟨s,hsS,hzi⟩
    · have hvu : v=u:=by
        by_contra hne
        simp only [x,Function.update_of_ne hne] at hxv
        rw [hpt64_L4_false i v hvL] at hxv;cases hxv
      subst hvu;exact hBv
    · rw [hzf s hsS] at hzi;cases hzi
  have hp2:=pp2
  have hB3_36 : (Bo 3).testBit 36=true:=by
    apply hB_one_at 3 36 (by simp [L4]) (by omega) hp2.2.2.2.2.2.1.1 hp2.2.2.2.2.2.1.2.1
    intro s hsS
    cases h : (zo s).testBit 36
    · rfl
    · have h5:=hz_mono s (by omega) (by omega) hp2.2.2.2.2.1.1 h
      rw [hz_zero_at 5 (by omega) (Or.inl hp2.2.2.2.2.1.2.1) s hsS] at h5;cases h5
  have hB3_48 : (Bo 3).testBit 48=true:=by
    apply hB_one_at 3 48 (by simp [L4]) (by omega) hp2.2.2.2.2.2.1.2.2.1 hp2.2.2.2.2.2.1.2.2.2.1
    intro s hsS
    cases h : (zo s).testBit 48
    · rfl
    · have h17:=hz_mono s (by omega) (by omega) hp2.2.2.2.2.1.2.2.1 h
      rw [hz_zero_at 17 (by omega) (Or.inl hp2.2.2.2.2.1.2.2.2.1) s hsS] at h17;cases h17
  have hB4_1 : (Bo 4).testBit 1=true :=
    hB_one_at 4 1 (by simp [L4]) (by omega) hp2.2.2.2.2.2.1.2.2.2.2.1 hp2.2.2.2.2.2.1.2.2.2.2.2.1
      (hz_zero_at 1 (by omega) (Or.inl hp2.2.2.2.2.1.2.2.2.2.1))
  have hB4_32 : (Bo 4).testBit 32=true:=by
    have hB3_32 : (Bo 3).testBit 32=false:=by
      cases h : (Bo 3).testBit 32
      · rfl
      · exfalso
        obtain ⟨hv3,ht3⟩:=pp1.2.1 ⟨32,by omega⟩ (le_refl 32)
        let x3:=Function.update (pt64 32) 3 true
        have hag : ∀ k : Fin 10,k ∉ L4 → x3 k=pt64 32 k:=fun k hk=>by
          have : k ≠ 3:=fun e=>hk (e ▸ by simp [L4]);simp [x3,this]
        have hval:=(vlO64 (by omega) hag).mpr (Or.inl ⟨3,by simp [L4],by simp [x3],h⟩)
        rw [computes x3 hv3,ht3 hp2.2.2.2.2.1.2.2.2.2.2.1] at hval;cases hval
    let x34:=Function.update (Function.update (pt64 32) 3 true) 4 true
    have hag : ∀ k : Fin 10,k ∉ L4 → x34 k=pt64 32 k:=fun k hk=>by
      have hk3 : k ≠ 3:=fun e=>hk (e ▸ by simp [L4])
      have hk4 : k ≠ 4:=fun e=>hk (e ▸ by simp [L4])
      simp [x34,hk3,hk4]
    have hval : vl gs x34 out.val=true :=
      (computes x34 hp2.2.2.2.2.2.1.2.2.2.2.2.2.1).trans hp2.2.2.2.2.2.1.2.2.2.2.2.2.2.1
    rcases (vlO64 (by omega) hag).mp hval with ⟨v,hvL,hxv,hBv⟩ | ⟨s,hsS,hzi⟩
    · rw [mem_L4] at hvL
      rcases hvL with rfl | rfl | rfl | rfl
      · rw [hB3_32] at hBv;cases hBv
      · exact hBv
      · simp [x34,pt64] at hxv
      · simp [x34,pt64] at hxv
    · rw [hz_zero_at 32 (by omega) (Or.inr hp2.2.2.2.2.1.2.2.2.2.2.1) s hsS] at hzi;cases hzi
  have hB6_2 : (Bo 6).testBit 2=true :=
    hB_one_at 6 2 (by simp [L4]) (by omega) hp2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.1
      hp2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.1 (hz_zero_at 2 (by omega) (Or.inl hp2.2.2.2.2.1.2.2.2.2.2.2.1))
  have hB6_16 : (Bo 6).testBit 16=true :=
    hB_one_at 6 16 (by simp [L4]) (by omega) hp2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.1
      hp2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.1 (hz_zero_at 16 (by omega) (Or.inl hp2.2.2.2.2.1.2.2.2.2.2.2.2.1))
  have hB7_4 : (Bo 7).testBit 4=true :=
    hB_one_at 7 4 (by simp [L4]) (by omega) hp2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.1
      hp2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (hz_zero_at 4 (by omega) (Or.inl hp2.2.2.2.2.1.2.2.2.2.2.2.2.2.1))
  have hB7_8 : (Bo 7).testBit 8=true :=
    hB_one_at 7 8 (by simp [L4]) (by omega) hp2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      hp2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 (hz_zero_at 8 (by omega) (Or.inl hp2.2.2.2.2.1.2.2.2.2.2.2.2.2.2))
  have hB_R1 : (Bo 3&&&R1_3)=R1_3 ∧ (Bo 4&&&R1_4)=R1_4 ∧
               (Bo 6&&&R1_6)=R1_6 ∧ (Bo 7&&&R1_7)=R1_7:=by
    have mkR1 : ∀ (u : Fin 10) (R1 : ℕ) (a b : ℕ),R1 < 2 ^ 64 → a < 64 → b < 64 →
        (Bo u).testBit a=true → (Bo u).testBit b=true →
        (∀ i : Fin 64,R1.testBit i.val=true →
          (∀ k : Fin 10,pt64 a k=true → pt64 i.val k=true) ∨
          (∀ k : Fin 10,pt64 b k=true → pt64 i.val k=true)) →
        (Bo u&&&R1)=R1:=by
      intro u R1 a b hR1lt ha hb hBa hBb hup
      apply Nat.eq_of_testBit_eq;intro i
      rw [Nat.testBit_and]
      by_cases hi : i < 64
      · cases hr : R1.testBit i
        · simp
        · rcases hup ⟨i,hi⟩ hr with hle | hle
          · rw [hB_mono u ha hi hle hBa];simp
          · rw [hB_mono u hb hi hle hBb];simp
      · have hf:=tbFlt i hR1lt (by omega)
        simp [hf]
    exact ⟨mkR1 3 R1_3 36 48 mbP.1.1 (by omega) (by omega) hB3_36 hB3_48 hp2.1,
           mkR1 4 R1_4 1 32 mbP.1.2.1 (by omega) (by omega) hB4_1 hB4_32 hp2.2.1,
           mkR1 6 R1_6 2 16 mbP.1.2.2.1 (by omega) (by omega) hB6_2 hB6_16 hp2.2.2.1,
           mkR1 7 R1_7 4 8 mbP.1.2.2.2.1 (by omega) (by omega) hB7_4 hB7_8 hp2.2.2.2.1⟩
  let lM (q : ℕ) : ℕ :=
    (if rU 3 q then 1 else 0) |||
    (if rU 4 q then 2 else 0) |||
    (if rU 6 q then 4 else 0) |||
    (if rU 7 q then 8 else 0)
  have hlmb : ∀ q,
      (((lM q&&&1) != 0)=true ↔ rU 3 q) ∧
      (((lM q&&&2) != 0)=true ↔ rU 4 q) ∧
      (((lM q&&&4) != 0)=true ↔ rU 6 q) ∧
      (((lM q&&&8) != 0)=true ↔ rU 7 q):=by
    intro q
    dsimp only [lM]
    by_cases r3 : rU 3 q<;>by_cases r4 : rU 4 q <;>
    by_cases r6 : rU 6 q<;>by_cases r7 : rU 7 q <;>
    simp [r3,r4,r6,r7]
  have hlbd : ∀ q ∈ Ag,1 ≤ lM q ∧ lM q ≤ 15:=by
    intro q hqA
    obtain ⟨hq,u,hu,ruq⟩:=hUi (hA_sub hqA)
    have hru : rU u q:=⟨hq,ruq⟩
    dsimp only [lM]
    rw [mem_L4] at hu
    by_cases r3 : rU 3 q<;>by_cases r4 : rU 4 q <;>
    by_cases r6 : rU 6 q<;>by_cases r7 : rU 7 q <;>
    simp only [r3,r4,r6,r7,↓reduceIte] <;>
    first | decide | (rcases hu with rfl | rfl | rfl | rfl<;>contradiction)
  have hlsp : ∀ {q1 q2 : ℕ} (hq1 : q1 < gs.length) (hq2 : q2 < gs.length),
      Relation.ReflTransGen (rE gs) (⟨10 + q1,Nat.add_lt_add_left hq1 10⟩ : Fin (10 + gs.length)) ⟨10 + q2,Nat.add_lt_add_left hq2 10⟩ →
      (lM q1&&&lM q2)=lM q1:=by
    intro q1 q2 hq1 hq2 r12
    have himp : ∀ u,rU u q1 → rU u q2:=fun u ⟨_,ru1⟩=>⟨hq2,ru1.trans r12⟩
    have hm1 : lM q1=((if decide (rU 3 q1)=true then 1 else 0) |||
        (if decide (rU 4 q1)=true then 2 else 0) |||
        (if decide (rU 6 q1)=true then 4 else 0) |||
        (if decide (rU 7 q1)=true then 8 else 0)):=by simp [lM]
    have hm2 : lM q2=((if decide (rU 3 q2)=true then 1 else 0) |||
        (if decide (rU 4 q2)=true then 2 else 0) |||
        (if decide (rU 6 q2)=true then 4 else 0) |||
        (if decide (rU 7 q2)=true then 8 else 0)):=by simp [lM]
    rw [hm1,hm2]
    exact mask4_sub _ _ _ _ _ _ _ _
      (fun h=>decide_eq_true (himp 3 (of_decide_eq_true h)))
      (fun h=>decide_eq_true (himp 4 (of_decide_eq_true h)))
      (fun h=>decide_eq_true (himp 6 (of_decide_eq_true h)))
      (fun h=>decide_eq_true (himp 7 (of_decide_eq_true h)))
  have hllm : ∀ q1 ∈ Ag,∀ q2 ∈ Ag,isLP (lM q1) (lM q2)=true:=by
    intro q1 hq1 q2 hq2
    unfold isLP
    by_cases hdisj : (lM q1&&&lM q2)=0
    · simp [hdisj]
    · have hex : ∃ u ∈ L4,rU u q1 ∧ rU u q2:=by
        by_contra hnone;push_neg at hnone
        apply hdisj
        have n3 : ¬ (rU 3 q1 ∧ rU 3 q2):=fun h=>hnone 3 (by simp [L4]) h.1 h.2
        have n4 : ¬ (rU 4 q1 ∧ rU 4 q2):=fun h=>hnone 4 (by simp [L4]) h.1 h.2
        have n6 : ¬ (rU 6 q1 ∧ rU 6 q2):=fun h=>hnone 6 (by simp [L4]) h.1 h.2
        have n7 : ¬ (rU 7 q1 ∧ rU 7 q2):=fun h=>hnone 7 (by simp [L4]) h.1 h.2
        have hm1 : lM q1=((if decide (rU 3 q1)=true then 1 else 0) |||
            (if decide (rU 4 q1)=true then 2 else 0) |||
            (if decide (rU 6 q1)=true then 4 else 0) |||
            (if decide (rU 7 q1)=true then 8 else 0)):=by simp [lM]
        have hm2 : lM q2=((if decide (rU 3 q2)=true then 1 else 0) |||
            (if decide (rU 4 q2)=true then 2 else 0) |||
            (if decide (rU 6 q2)=true then 4 else 0) |||
            (if decide (rU 7 q2)=true then 8 else 0)):=by simp [lM]
        rw [hm1,hm2]
        exact mask4_disj (decide (rU 3 q1)) (decide (rU 4 q1)) (decide (rU 6 q1)) (decide (rU 7 q1))
          (decide (rU 3 q2)) (decide (rU 4 q2)) (decide (rU 6 q2)) (decide (rU 7 q2))
          (by by_cases h1 : rU 3 q1<;>by_cases h2 : rU 3 q2<;>simp [h1,h2];exact n3 ⟨h1,h2⟩)
          (by by_cases h1 : rU 4 q1<;>by_cases h2 : rU 4 q2<;>simp [h1,h2];exact n4 ⟨h1,h2⟩)
          (by by_cases h1 : rU 6 q1<;>by_cases h2 : rU 6 q2<;>simp [h1,h2];exact n6 ⟨h1,h2⟩)
          (by by_cases h1 : rU 7 q1<;>by_cases h2 : rU 7 q2<;>simp [h1,h2];exact n7 ⟨h1,h2⟩)
      obtain ⟨u,hu,⟨hq1',r1⟩,⟨hq2',r2⟩⟩:=hex
      rcases uLam ⟨u,hu,Relation.ReflTransGen.refl⟩ r1 r2 with r12 | r21
      · have heq:=hlsp hq1' hq2' r12;simp [heq]
      · have heq:=hlsp hq2' hq1' r21;rw [bac] at heq;simp [heq]
  have hsw_R1 : ∀ q ∈ Ag,∀ u ∈ L4,rU u q →
      ∀ i < 64,(Bo u).testBit i=true → (tt64 gs (sW q)).testBit i=true:=by
    intro q hqA u _ hru i hi hBi
    rw [tbT64];simp only [hi,decide_true,Bool.true_and]
    exact (hB_tb u i hi).mp hBi q hqA hru
  have hsr1 : ∀ q ∈ Ag,
      (tt64 gs (sW q)&&&rR1 (lM q))=rR1 (lM q):=by
    intro q hqA
    have mk1 : ∀ u ∈ L4,∀ R1 : ℕ,R1 < 2 ^ 64 → (Bo u&&&R1)=R1 → rU u q →
        (tt64 gs (sW q)&&&R1)=R1:=by
      intro u hu R1 hlt hBR hru
      apply Nat.eq_of_testBit_eq;intro i
      rw [Nat.testBit_and]
      by_cases hi : i < 64
      · cases hr : R1.testBit i
        · simp
        · have hBi : (Bo u).testBit i=true:=by
            have:=congrArg (fun n=>n.testBit i) hBR
            simp only [Nat.testBit_and,hr,Bool.and_true] at this;exact this
          rw [hsw_R1 q hqA u hu hru i hi hBi];simp
      · have hf:=tbFlt i hlt (by omega)
        simp [hf]
    unfold rR1
    rw [baodl,baodl,baodl]
    refine congrArg₂ (·|||·) (congrArg₂ (·|||·) (congrArg₂ (·|||·) ?_ ?_) ?_) ?_
    · split_ifs with h
      · exact mk1 3 (by simp [L4]) R1_3 mbP.1.1 hB_R1.1 ((hlmb q).1.mp h)
      · exact ba0r _
    · split_ifs with h
      · exact mk1 4 (by simp [L4]) R1_4 mbP.1.2.1 hB_R1.2.1 ((hlmb q).2.1.mp h)
      · exact ba0r _
    · split_ifs with h
      · exact mk1 6 (by simp [L4]) R1_6 mbP.1.2.2.1 hB_R1.2.2.1 ((hlmb q).2.2.1.mp h)
      · exact ba0r _
    · split_ifs with h
      · exact mk1 7 (by simp [L4]) R1_7 mbP.1.2.2.2.1 hB_R1.2.2.2 ((hlmb q).2.2.2.mp h)
      · exact ba0r _
  have hAs : ∀ (u : Fin 10) (R0 : ℕ) (i : ℕ),i < 64 → (Bo u&&&R0)=0 → R0.testBit i=true →
      ∃ q ∈ Ag,rU u q ∧ (tt64 gs (sW q)).testBit i=false:=by
    intro u R0 i hi hB0 hRi
    have hBf : (Bo u).testBit i=false:=by
      have:=congrArg (fun n=>n.testBit i) hB0
      simp only [Nat.testBit_and,hRi,Bool.and_true,Nat.zero_testBit] at this;exact this
    by_contra hnone;push_neg at hnone
    have hBt : (Bo u).testBit i=true:=(hB_tb u i hi).mpr fun q hq hru=>by
      have ht:=hnone q hq hru
      rw [tbT64] at ht;simp only [hi,decide_true,Bool.true_and] at ht
      cases h : vl gs (pt64 i) (sW q)
      · exact (ht h).elim
      · rfl
    rw [hBt] at hBf;cases hBf
  have hnr1 : ∀ {q : ℕ} (hqA : q ∈ Ag) {v : Fin 10} (hv : v ∈ L4) {R1 : ℕ} {i : ℕ},
      i < 64 → (Bo v&&&R1)=R1 → R1.testBit i=true →
      (tt64 gs (sW q)).testBit i=false → ¬ rU v q:=by
    intro q hqA v hv R1 i hi hBR hRi hzf hru
    have hBi : (Bo v).testBit i=true:=by
      have:=congrArg (fun n=>n.testBit i) hBR
      simp only [Nat.testBit_and,hRi,Bool.and_true] at this;exact this
    have ht:=hsw_R1 q hqA v hv hru i hi hBi
    rw [ht] at hzf;cases hzf
  have hsep:=mbP.2.1
  obtain ⟨g6,hg6A,hg6_r6,hg6_z5⟩:=hAs 6 R0_6 5 (by omega) hB_R0.2.2.1 hsep.2.2.2.2.2.2.1
  have hg6_mask : lM g6=4:=by
    have n3:=hnr1 hg6A (by simp [L4]) (by omega) hB_R1.1 hsep.2.2.2.2.2.2.2.1 hg6_z5
    have n4:=hnr1 hg6A (by simp [L4]) (by omega) hB_R1.2.1 hsep.2.2.2.2.2.2.2.2.1 hg6_z5
    have n7:=hnr1 hg6A (by simp [L4]) (by omega) hB_R1.2.2.2 hsep.2.2.2.2.2.2.2.2.2.1 hg6_z5
    simp [lM,hg6_r6,n3,n4,n7]
  obtain ⟨g7,hg7A,hg7_r7,hg7_z17⟩:=hAs 7 R0_7 17 (by omega) hB_R0.2.2.2 hsep.2.2.2.2.2.2.2.2.2.2.1
  have hg7_mask : lM g7=8:=by
    have n3:=hnr1 hg7A (by simp [L4]) (by omega) hB_R1.1 hsep.2.2.2.2.2.2.2.2.2.2.2.1 hg7_z17
    have n4:=hnr1 hg7A (by simp [L4]) (by omega) hB_R1.2.1 hsep.2.2.2.2.2.2.2.2.2.2.2.2.1 hg7_z17
    have n6:=hnr1 hg7A (by simp [L4]) (by omega) hB_R1.2.2.1 hsep.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hg7_z17
    simp [lM,hg7_r7,n3,n4,n6]
  obtain ⟨g3,hg3A,hg3_mask⟩ : ∃ g3 ∈ Ag,lM g3=1:=by
    obtain ⟨q1,hq1A,hq1_r3,hq1_z34⟩:=hAs 3 R0_3 34 (by omega) hB_R0.1 hsep.1
    obtain ⟨q2,hq2A,hq2_r3,hq2_z40⟩:=hAs 3 R0_3 40 (by omega) hB_R0.1 hsep.2.2.2.1
    have hq1_n4:=hnr1 hq1A (by simp [L4]) (by omega) hB_R1.2.1 hsep.2.1 hq1_z34
    have hq1_n6:=hnr1 hq1A (by simp [L4]) (by omega) hB_R1.2.2.1 hsep.2.2.1 hq1_z34
    have hq2_n4:=hnr1 hq2A (by simp [L4]) (by omega) hB_R1.2.1 hsep.2.2.2.2.1 hq2_z40
    have hq2_n7:=hnr1 hq2A (by simp [L4]) (by omega) hB_R1.2.2.2 hsep.2.2.2.2.2.1 hq2_z40
    have hlam:=hllm q1 hq1A q2 hq2A
    by_cases hq1_r7 : rU 7 q1
    · by_cases hq2_r6 : rU 6 q2
      · exfalso
        have m1 : lM q1=9:=by simp [lM,hq1_r3,hq1_n4,hq1_n6,hq1_r7]
        have m2 : lM q2=5:=by simp [lM,hq2_r3,hq2_n4,hq2_r6,hq2_n7]
        rw [m1,m2] at hlam;revert hlam;decide
      · exact ⟨q2,hq2A,by simp [lM,hq2_r3,hq2_n4,hq2_r6,hq2_n7]⟩
    · exact ⟨q1,hq1A,by simp [lM,hq1_r3,hq1_n4,hq1_n6,hq1_r7]⟩
  obtain ⟨g4,hg4A,hg4_mask⟩ : ∃ g4 ∈ Ag,lM g4=2 ∨ lM g4=3:=by
    obtain ⟨q1,hq1A,hq1_r4,hq1_z2⟩:=hAs 4 R0_4 2 (by omega) hB_R0.2.1 hsep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    obtain ⟨q2,hq2A,hq2_r4,hq2_z8⟩:=hAs 4 R0_4 8 (by omega) hB_R0.2.1 hsep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hq1_n6:=hnr1 hq1A (by simp [L4]) (by omega) hB_R1.2.2.1 hsep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hq1_z2
    have hq2_n7:=hnr1 hq2A (by simp [L4]) (by omega) hB_R1.2.2.2 hsep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 hq2_z8
    have hlam:=hllm q1 hq1A q2 hq2A
    by_cases hq1_r7 : rU 7 q1
    · by_cases hq2_r6 : rU 6 q2
      · exfalso
        by_cases a3 : rU 3 q1<;>by_cases b3 : rU 3 q2
        · have m1 : lM q1=11:=by simp [lM,a3,hq1_r4,hq1_n6,hq1_r7]
          have m2 : lM q2=7:=by simp [lM,b3,hq2_r4,hq2_r6,hq2_n7]
          rw [m1,m2] at hlam;revert hlam;decide
        · have m1 : lM q1=11:=by simp [lM,a3,hq1_r4,hq1_n6,hq1_r7]
          have m2 : lM q2=6:=by simp [lM,b3,hq2_r4,hq2_r6,hq2_n7]
          rw [m1,m2] at hlam;revert hlam;decide
        · have m1 : lM q1=10:=by simp [lM,a3,hq1_r4,hq1_n6,hq1_r7]
          have m2 : lM q2=7:=by simp [lM,b3,hq2_r4,hq2_r6,hq2_n7]
          rw [m1,m2] at hlam;revert hlam;decide
        · have m1 : lM q1=10:=by simp [lM,a3,hq1_r4,hq1_n6,hq1_r7]
          have m2 : lM q2=6:=by simp [lM,b3,hq2_r4,hq2_r6,hq2_n7]
          rw [m1,m2] at hlam;revert hlam;decide
      · refine ⟨q2,hq2A,?_⟩
        by_cases b3 : rU 3 q2
        · right;simp [lM,b3,hq2_r4,hq2_r6,hq2_n7]
        · left;simp [lM,b3,hq2_r4,hq2_r6,hq2_n7]
    · refine ⟨q1,hq1A,?_⟩
      by_cases a3 : rU 3 q1
      · right;simp [lM,a3,hq1_r4,hq1_n6,hq1_r7]
      · left;simp [lM,a3,hq1_r4,hq1_n6,hq1_r7]
  have h4_ne : g3 ≠ g4 ∧ g3 ≠ g6 ∧ g3 ≠ g7 ∧ g4 ≠ g6 ∧ g4 ≠ g7 ∧ g6 ≠ g7:=by
    refine ⟨?_,?_,?_,?_,?_,?_⟩<;>intro h<;>have hm:=congrArg lM h<;>omega
  have h4_sub : ({g3,g4,g6,g7} : Finset ℕ) ⊆ Ag:=by
    intro q hq;simp only [Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl<;>assumption
  have h4_card : ({g3,g4,g6,g7} : Finset ℕ).card=4:=by
    rw [Finset.card_insert_of_notMem (by simp [h4_ne]),
        Finset.card_insert_of_notMem (by simp [h4_ne]),
        Finset.card_insert_of_notMem (by simp [h4_ne]),
        Finset.card_singleton]
  have hA_ge4 : 4 ≤ Ag.card:=h4_card ▸ Finset.card_le_card h4_sub
  have hbudget : Wo.card + Wa.card + Sg.card + Ag.card ≤ 11:=by omega
  have hbtz : ∀ w,w < 10 → ∀ hw : w < 10 + gs.length,¬ inU ⟨w,hw⟩ → tt64 gs w ∈ bWs:=by
    intro w hw10 hw hnot
    have hne3 : w ≠ 3:=fun h=>hnot ⟨3,by simp [L4],by have heq : iW gs 3=⟨w,hw⟩:=Fin.ext h.symm;rw [heq]⟩
    have hne4 : w ≠ 4:=fun h=>hnot ⟨4,by simp [L4],by have heq : iW gs 4=⟨w,hw⟩:=Fin.ext h.symm;rw [heq]⟩
    have hne6 : w ≠ 6:=fun h=>hnot ⟨6,by simp [L4],by have heq : iW gs 6=⟨w,hw⟩:=Fin.ext h.symm;rw [heq]⟩
    have hne7 : w ≠ 7:=fun h=>hnot ⟨7,by simp [L4],by have heq : iW gs 7=⟨w,hw⟩:=Fin.ext h.symm;rw [heq]⟩
    have ht:=tt64_base gs
    have hcases : w=0 ∨ w=1 ∨ w=2 ∨ w=5 ∨ w=8 ∨ w=9:=by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl<;>simp [bWs,ht]
  have hpb0 : ∀ w ∈ bWs,w ∈ pOs:=fun w hw=>by
    simpa [List.elem_eq_mem] using List.all_eq_true.mp pureOrs_props.1 w hw
  have hpo0 : ∀ a ∈ pOs,∀ b ∈ pOs,(a|||b) ∈ pOs:=fun a ha b hb=>by
    simpa [List.elem_eq_mem] using List.all_eq_true.mp (List.all_eq_true.mp pureOrs_props.2.1 a ha) b hb
  have hWp : Wa.card=0 → ∀ w,∀ hw : w < 10 + gs.length,¬ inU ⟨w,hw⟩ → tt64 gs w ∈ pOs:=by
    intro hWa0 w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw hnot
      by_cases h10 : w < 10
      · exact hpb0 _ (hbtz w h10 hw hnot)
      · obtain ⟨p,rfl⟩ : ∃ p,w=10 + p:=⟨w - 10,by omega⟩
        have hplt : p < gs.length:=by omega
        have hpW : p ∈ Wg:=Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr hplt,fun h=>hnot (hUi h).2⟩
        have hpg : gs[p]?=some (gs[p]'hplt):=List.getElem?_eq_getElem hplt
        obtain ⟨hop,a,b,ha,hb,_,hin⟩:=cmG hcl hmono distinct hpg
        have hor : (gs[p]'hplt).op=GateOp.or:=by
          rcases hop with hand | hor
          · exfalso
            have hpWa : p ∈ Wa:=Finset.mem_filter.mpr ⟨hpW,_,hpg,hand⟩
            have hpos:=Finset.card_pos.mpr ⟨p,hpWa⟩;omega
          · exact hor
        have hnot_a : ¬ inU ⟨a,by omega⟩:=fun hua =>
          hnot (uMem hua ⟨p,gs[p]'hplt,hpg,rfl,by rw [hin];simp⟩)
        have hnot_b : ¬ inU ⟨b,by omega⟩:=fun hub =>
          hnot (uMem hub ⟨p,gs[p]'hplt,hpg,rfl,by rw [hin];simp⟩)
        have hpg_eq : gs[p]?=some ⟨GateOp.or,[a,b]⟩:=by
          rw [hpg];congr 1;cases hgx : gs[p]'hplt;simp [hgx] at hor hin;exact congrArg₂ Gate.mk hor hin
        rw [tt64_gate_or hcl hpg_eq]
        exact hpo0 _ (ih a ha (by omega) hnot_a) _ (ih b hb (by omega) hnot_b)
  have hW1a : Wa.card ≤ 1 →
      ∃ a b,a ∈ pOs ∧ b ∈ pOs ∧
        ∀ w,∀ hw : w < 10 + gs.length,¬ inU ⟨w,hw⟩ →
          tt64 gs w ∈ pOs ∨ tt64 gs w=(a&&&b) ∨ ∃ p ∈ pOs,tt64 gs w=(p|||(a&&&b)):=by
    intro hWa1
    by_cases hWa0 : Wa.card=0
    · refine ⟨X0,X0,hpb0 X0 (by simp [bWs]),hpb0 X0 (by simp [bWs]),
        fun w hw hnot=>Or.inl (hWp hWa0 w hw hnot)⟩
    · have hWa_eq1 : Wa.card=1:=by omega
      obtain ⟨p0,hp0_eq⟩:=Finset.card_eq_one.mp hWa_eq1
      have hp0_mem : p0 ∈ Wa:=by rw [hp0_eq];simp
      have hp0W : p0 ∈ Wg:=(Finset.mem_filter.mp hp0_mem).1
      have hp0_lt : p0 < gs.length:=Finset.mem_range.mp (Finset.mem_sdiff.mp hp0W).1
      obtain ⟨_,g0,hg0p,hg0_and⟩:=Finset.mem_filter.mp hp0_mem
      obtain ⟨_,ia,ib,hia,hib,_,hg0_in⟩:=cmG hcl hmono distinct hg0p
      have hnot_p0 : ¬ inU ⟨10 + p0,by omega⟩:=fun h =>
        (Finset.mem_sdiff.mp hp0W).2 (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hp0_lt,hp0_lt,h⟩)
      have hpure_below : ∀ w < 10 + p0,∀ hw : w < 10 + gs.length,¬ inU ⟨w,hw⟩ → tt64 gs w ∈ pOs:=by
        intro w
        induction w using Nat.strong_induction_on with
        | _ w ih =>
          intro hlt hw hnot
          by_cases h10 : w < 10
          · exact hpb0 _ (hbtz w h10 hw hnot)
          · obtain ⟨p,rfl⟩ : ∃ p,w=10 + p:=⟨w - 10,by omega⟩
            have hplt : p < gs.length:=by omega
            have hpW : p ∈ Wg:=Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr hplt,fun h=>hnot (hUi h).2⟩
            have hpg : gs[p]?=some (gs[p]'hplt):=List.getElem?_eq_getElem hplt
            obtain ⟨hop,x,y,hx,hy,_,hin⟩:=cmG hcl hmono distinct hpg
            have hor : (gs[p]'hplt).op=GateOp.or:=by
              rcases hop with hand | hor
              · exfalso
                have hpWa : p ∈ Wa:=Finset.mem_filter.mpr ⟨hpW,_,hpg,hand⟩
                rw [hp0_eq,Finset.mem_singleton] at hpWa;omega
              · exact hor
            have hnx : ¬ inU ⟨x,by omega⟩:=fun h=>hnot (uMem h ⟨p,gs[p]'hplt,hpg,rfl,by rw [hin];simp⟩)
            have hny : ¬ inU ⟨y,by omega⟩:=fun h=>hnot (uMem h ⟨p,gs[p]'hplt,hpg,rfl,by rw [hin];simp⟩)
            have hpg_eq : gs[p]?=some ⟨GateOp.or,[x,y]⟩:=by
              rw [hpg];congr 1;cases hgx : gs[p]'hplt;simp [hgx] at hor hin;exact congrArg₂ Gate.mk hor hin
            rw [tt64_gate_or hcl hpg_eq]
            exact hpo0 _ (ih x hx (by omega) (by omega) hnx) _ (ih y hy (by omega) (by omega) hny)
      have hnia : ¬ inU ⟨ia,by omega⟩:=fun h=>hnot_p0 (uMem h ⟨p0,g0,hg0p,rfl,by rw [hg0_in];simp⟩)
      have hnib : ¬ inU ⟨ib,by omega⟩:=fun h=>hnot_p0 (uMem h ⟨p0,g0,hg0p,rfl,by rw [hg0_in];simp⟩)
      let va:=tt64 gs ia
      let vb:=tt64 gs ib
      have hva : va ∈ pOs:=hpure_below ia hia (by omega) hnia
      have hvb : vb ∈ pOs:=hpure_below ib hib (by omega) hnib
      have hg0_eq : gs[p0]?=some ⟨GateOp.and,[ia,ib]⟩:=by
        rw [hg0p];congr 1;cases g0;simp at hg0_and hg0_in;exact congrArg₂ Gate.mk hg0_and hg0_in
      have hp0_tt : tt64 gs (10 + p0)=(va&&&vb):=tt64_gate_and hcl hg0_eq
      refine ⟨va,vb,hva,hvb,?_⟩
      intro w
      induction w using Nat.strong_induction_on with
      | _ w ih =>
        intro hw hnot
        by_cases h10 : w < 10
        · exact Or.inl (hpb0 _ (hbtz w h10 hw hnot))
        · obtain ⟨p,rfl⟩ : ∃ p,w=10 + p:=⟨w - 10,by omega⟩
          by_cases hpp0 : p=p0
          · subst hpp0;exact Or.inr (Or.inl hp0_tt)
          · have hplt : p < gs.length:=by omega
            have hpW : p ∈ Wg:=Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr hplt,fun h=>hnot (hUi h).2⟩
            have hpg : gs[p]?=some (gs[p]'hplt):=List.getElem?_eq_getElem hplt
            obtain ⟨hop,x,y,hx,hy,_,hin⟩:=cmG hcl hmono distinct hpg
            have hor : (gs[p]'hplt).op=GateOp.or:=by
              rcases hop with hand | hor
              · exfalso
                have hpWa : p ∈ Wa:=Finset.mem_filter.mpr ⟨hpW,_,hpg,hand⟩
                rw [hp0_eq,Finset.mem_singleton] at hpWa;exact hpp0 hpWa
              · exact hor
            have hnx : ¬ inU ⟨x,by omega⟩:=fun h=>hnot (uMem h ⟨p,gs[p]'hplt,hpg,rfl,by rw [hin];simp⟩)
            have hny : ¬ inU ⟨y,by omega⟩:=fun h=>hnot (uMem h ⟨p,gs[p]'hplt,hpg,rfl,by rw [hin];simp⟩)
            have hpg_eq : gs[p]?=some ⟨GateOp.or,[x,y]⟩:=by
              rw [hpg];congr 1;cases hgx : gs[p]'hplt;simp [hgx] at hor hin;exact congrArg₂ Gate.mk hor hin
            rw [tt64_gate_or hcl hpg_eq]
            rcases ih x hx (by omega) hnx with hxp | hxg | ⟨px,hpx,hxe⟩ <;>
            rcases ih y hy (by omega) hny with hyp | hyg | ⟨py,hpy,hye⟩
            · exact Or.inl (hpo0 _ hxp _ hyp)
            · rw [hyg];exact Or.inr (Or.inr ⟨tt64 gs x,hxp,rfl⟩)
            · rw [hye];exact Or.inr (Or.inr ⟨tt64 gs x|||py,hpo0 _ hxp _ hpy,by rw [boa]⟩)
            · rw [hxg];exact Or.inr (Or.inr ⟨tt64 gs y,hyp,boc ..⟩)
            · rw [hxg,hyg,bos];exact Or.inr (Or.inl rfl)
            · rw [hxg,hye];exact Or.inr (Or.inr ⟨py,hpy,by rw [boc (va&&&vb),boa,bos]⟩)
            · rw [hxe];exact Or.inr (Or.inr ⟨px|||tt64 gs y,hpo0 _ hpx _ hyp,by rw [boa,boc (va&&&vb),← boa]⟩)
            · rw [hxe,hyg];exact Or.inr (Or.inr ⟨px,hpx,by rw [boa,bos]⟩)
            · rw [hxe,hye];exact Or.inr (Or.inr ⟨px|||py,hpo0 _ hpx _ hpy,by
                rw [boa,← boa (va&&&vb) py (va&&&vb),boc (va&&&vb) py,
                    boa py (va&&&vb) (va&&&vb),bos,← boa]⟩)
  have hk1 : Wa.card ≤ 1 → Ag.card=4 → False:=by
    intro hWa1 hA4
    have hA_eq : Ag={g3,g4,g6,g7} :=
      (Finset.eq_of_subset_of_card_le h4_sub (by omega)).symm
    obtain ⟨a,b,ha,hb,hmemW⟩:=hW1a hWa1
    let b3:=tt64 gs (sW g3)
    let b4:=tt64 gs (sW g4)
    let b6:=tt64 gs (sW g6)
    let b7:=tt64 gs (sW g7)
    have hmem_sw : ∀ q ∈ Ag,
        tt64 gs (sW q) ∈ pOs ∨ tt64 gs (sW q)=(a&&&b) ∨
          ∃ p ∈ pOs,tt64 gs (sW q)=(p|||(a&&&b)):=fun q hq=>by
      obtain ⟨hlt,hnot⟩:=hsnU (Finset.mem_filter.mp hq).1
      exact hmemW (sW q) hlt hnot
    have hr_g3 : rU 3 g3 ∧ ¬ rU 4 g3 ∧ ¬ rU 6 g3 ∧ ¬ rU 7 g3:=by
      have:=hlmb g3;rw [hg3_mask] at this;simp at this;exact this
    have hr_g6 : ¬ rU 3 g6 ∧ ¬ rU 4 g6 ∧ rU 6 g6 ∧ ¬ rU 7 g6:=by
      have:=hlmb g6;rw [hg6_mask] at this;simp at this;exact this
    have hr_g7 : ¬ rU 3 g7 ∧ ¬ rU 4 g7 ∧ ¬ rU 6 g7 ∧ rU 7 g7:=by
      have:=hlmb g7;rw [hg7_mask] at this;simp at this;exact this
    have hr_g4 : rU 4 g4 ∧ ¬ rU 6 g4 ∧ ¬ rU 7 g4 ∧
        (rU 3 g4 ↔ lM g4=3):=by
      have:=hlmb g4
      rcases hg4_mask with hm | hm<;>(rw [hm] at this;simp [hm] at this ⊢;exact ⟨this.2.1,this.2.2.1,this.2.2.2,this.1⟩)
    have hBs : ∀ (u : Fin 10) (g : ℕ),g ∈ Ag → rU u g →
        (∀ q ∈ Ag,rU u q → q=g) → Bo u=tt64 gs (sW g):=by
      intro u g hgA hrug huniq
      apply Nat.eq_of_testBit_eq;intro i
      by_cases hi : i < 64
      · apply Bool.eq_iff_iff.mpr
        rw [hB_tb u i hi,tbT64];simp only [hi,decide_true,Bool.true_and]
        exact ⟨fun h=>h g hgA hrug,fun h q hq hru=>(huniq q hq hru) ▸ h⟩
      · have h1 : (Bo u).testBit i=false:=by
          rw [show Bo u=landMask _ from rfl,tbLM];simp [hi]
        have h2 : (tt64 gs (sW g)).testBit i=false:=by rw [tbT64];simp [hi]
        rw [h1,h2]
    have hB4_eq : Bo 4=b4:=hBs 4 g4 hg4A hr_g4.1 (fun q hq hru=>by
      rw [hA_eq] at hq;simp only [Finset.mem_insert,Finset.mem_singleton] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact (hr_g3.2.1 hru).elim
      · rfl
      · exact (hr_g6.2.1 hru).elim
      · exact (hr_g7.2.1 hru).elim)
    have hB6_eq : Bo 6=b6:=hBs 6 g6 hg6A hr_g6.2.2.1 (fun q hq hru=>by
      rw [hA_eq] at hq;simp only [Finset.mem_insert,Finset.mem_singleton] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact (hr_g3.2.2.1 hru).elim
      · exact (hr_g4.2.1 hru).elim
      · rfl
      · exact (hr_g7.2.2.1 hru).elim)
    have hB7_eq : Bo 7=b7:=hBs 7 g7 hg7A hr_g7.2.2.2 (fun q hq hru=>by
      rw [hA_eq] at hq;simp only [Finset.mem_insert,Finset.mem_singleton] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact (hr_g3.2.2.2 hru).elim
      · exact (hr_g4.2.2.1 hru).elim
      · exact (hr_g6.2.2.2 hru).elim
      · rfl)
    have hb3_r1 : (b3&&&R1_3)=R1_3:=by
      have:=hsr1 g3 hg3A
      rw [hg3_mask] at this
      have hr1 : rR1 1=R1_3:=by decide
      rwa [hr1] at this
    have hb3_r0 : (b3&&&R0_3)=0:=by
      rcases hg4_mask with hm2 | hm3
      · have hB3_eq : Bo 3=b3:=hBs 3 g3 hg3A hr_g3.1 (fun q hq hru=>by
          rw [hA_eq] at hq;simp only [Finset.mem_insert,Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl | rfl
          · rfl
          · exact (by rw [hr_g4.2.2.2,hm2] at hru;omega)
          · exact (hr_g6.1 hru).elim
          · exact (hr_g7.1 hru).elim)
        rw [← hB3_eq];exact hB_R0.1
      · have hB3_eq : Bo 3=(b3&&&b4):=by
          apply Nat.eq_of_testBit_eq;intro i
          by_cases hi : i < 64
          · apply Bool.eq_iff_iff.mpr
            rw [hB_tb 3 i hi,Nat.testBit_and,Bool.and_eq_true,tbT64,tbT64]
            simp only [hi,decide_true,Bool.true_and]
            constructor
            · intro h;exact ⟨h g3 hg3A hr_g3.1,h g4 hg4A (hr_g4.2.2.2.mpr hm3)⟩
            · rintro ⟨h1,h2⟩ q hq hru
              rw [hA_eq] at hq;simp only [Finset.mem_insert,Finset.mem_singleton] at hq
              rcases hq with rfl | rfl | rfl | rfl
              · exact h1
              · exact h2
              · exact (hr_g6.1 hru).elim
              · exact (hr_g7.1 hru).elim
          · have h1 : (Bo 3).testBit i=false:=by
              rw [show Bo 3=landMask _ from rfl,tbLM];simp [hi]
            have h2 : (b3&&&b4).testBit i=false:=by rw [Nat.testBit_and,tbT64];simp [hi]
            rw [h1,h2]
        apply Nat.eq_of_testBit_eq;intro i
        rw [Nat.testBit_and,Nat.zero_testBit]
        cases hr0 : R0_3.testBit i
        · simp
        · have hr14 : R1_4.testBit i=true:=by
            have:=congrArg (fun n=>n.testBit i) r1_4_covers_r0_3
            simp only [Nat.testBit_and,hr0,Bool.and_true] at this;exact this
          have hb4i : b4.testBit i=true:=by
            have:=congrArg (fun n=>n.testBit i) (hB4_eq ▸ hB_R1.2.1)
            simp only [Nat.testBit_and,hr14,Bool.and_true] at this;exact this
          have h0:=congrArg (fun n=>n.testBit i) (hB3_eq ▸ hB_R0.1)
          simp only [Nat.testBit_and,hr0,hb4i,Bool.and_true,Nat.zero_testBit] at h0
          simp [h0]
    have hF_cases : ∀ s ∈ Sg,
        Fo s=ALL64 ∨ Fo s=b3 ∨ Fo s=b4 ∨ Fo s=b6 ∨ Fo s=b7 ∨ Fo s=(b3&&&b4):=by
      intro s hsS
      obtain ⟨hs,u,hu,rus⟩:=hUi (hS_sub hsS)
      have hri0 : ∀ q ∈ Ag,rS s q → rU u q:=fun q _ ⟨_,hq,_,rsq⟩ =>
        ⟨hq,rus.trans rsq⟩
      have hFe0 : (∀ q ∈ Ag,¬ rS s q) → Fo s=ALL64:=by
        intro hno
        apply Nat.eq_of_testBit_eq;intro i
        by_cases hi : i < 64
        · rw [ALL64_testBit i,decide_eq_true hi];exact (hF_tb s i hi).mpr (fun q hq hrs=>(hno q hq hrs).elim)
        · rw [show Fo s=landMask _ from rfl,tbLM,ALL64_testBit i];simp [hi]
      have hF1 : ∀ g ∈ Ag,rS s g → (∀ q ∈ Ag,rS s q → q=g) →
          Fo s=tt64 gs (sW g):=by
        intro g hgA hrsg huniq
        apply Nat.eq_of_testBit_eq;intro i
        by_cases hi : i < 64
        · apply Bool.eq_iff_iff.mpr
          rw [hF_tb s i hi,tbT64];simp only [hi,decide_true,Bool.true_and]
          exact ⟨fun h=>h g hgA hrsg,fun h q hq hrs=>(huniq q hq hrs) ▸ h⟩
        · have h1 : (Fo s).testBit i=false:=by rw [show Fo s=landMask _ from rfl,tbLM];simp [hi]
          have h2 : (tt64 gs (sW g)).testBit i=false:=by rw [tbT64];simp [hi]
          rw [h1,h2]
      rw [mem_L4] at hu
      rcases hu with rfl | rfl | rfl | rfl
      · by_cases r3 : rS s g3<;>by_cases r4 : rS s g4
        · right;right;right;right;right
          apply Nat.eq_of_testBit_eq;intro i
          by_cases hi : i < 64
          · apply Bool.eq_iff_iff.mpr
            rw [hF_tb s i hi,Nat.testBit_and,Bool.and_eq_true,tbT64,tbT64]
            simp only [hi,decide_true,Bool.true_and]
            constructor
            · intro h;exact ⟨h g3 hg3A r3,h g4 hg4A r4⟩
            · rintro ⟨h1,h2⟩ q hq hrs
              have hru:=hri0 q hq hrs
              rw [hA_eq] at hq;simp only [Finset.mem_insert,Finset.mem_singleton] at hq
              rcases hq with rfl | rfl | rfl | rfl
              · exact h1
              · exact h2
              · exact (hr_g6.1 hru).elim
              · exact (hr_g7.1 hru).elim
          · have h1 : (Fo s).testBit i=false:=by rw [show Fo s=landMask _ from rfl,tbLM];simp [hi]
            have h2 : (b3&&&b4).testBit i=false:=by rw [Nat.testBit_and,tbT64];simp [hi]
            rw [h1,h2]
        · right;left
          exact hF1 g3 hg3A r3 (fun q hq hrs=>by
            have hru:=hri0 q hq hrs
            rw [hA_eq] at hq;simp only [Finset.mem_insert,Finset.mem_singleton] at hq
            rcases hq with rfl | rfl | rfl | rfl
            · rfl
            · exact (r4 hrs).elim
            · exact (hr_g6.1 hru).elim
            · exact (hr_g7.1 hru).elim)
        · right;right;left
          exact hF1 g4 hg4A r4 (fun q hq hrs=>by
            have hru:=hri0 q hq hrs
            rw [hA_eq] at hq;simp only [Finset.mem_insert,Finset.mem_singleton] at hq
            rcases hq with rfl | rfl | rfl | rfl
            · exact (r3 hrs).elim
            · rfl
            · exact (hr_g6.1 hru).elim
            · exact (hr_g7.1 hru).elim)
        · left
          exact hFe0 (fun q hq hrs=>by
            have hru:=hri0 q hq hrs
            rw [hA_eq] at hq;simp only [Finset.mem_insert,Finset.mem_singleton] at hq
            rcases hq with rfl | rfl | rfl | rfl
            · exact r3 hrs
            · exact r4 hrs
            · exact hr_g6.1 hru
            · exact hr_g7.1 hru)
      · by_cases r4 : rS s g4
        · right;right;left
          exact hF1 g4 hg4A r4 (fun q hq hrs=>by
            have hru:=hri0 q hq hrs
            rw [hA_eq] at hq;simp only [Finset.mem_insert,Finset.mem_singleton] at hq
            rcases hq with rfl | rfl | rfl | rfl
            · exact (hr_g3.2.1 hru).elim
            · rfl
            · exact (hr_g6.2.1 hru).elim
            · exact (hr_g7.2.1 hru).elim)
        · left
          exact hFe0 (fun q hq hrs=>by
            have hru:=hri0 q hq hrs
            rw [hA_eq] at hq;simp only [Finset.mem_insert,Finset.mem_singleton] at hq
            rcases hq with rfl | rfl | rfl | rfl
            · exact hr_g3.2.1 hru
            · exact r4 hrs
            · exact hr_g6.2.1 hru
            · exact hr_g7.2.1 hru)
      · by_cases r6 : rS s g6
        · right;right;right;left
          exact hF1 g6 hg6A r6 (fun q hq hrs=>by
            have hru:=hri0 q hq hrs
            rw [hA_eq] at hq;simp only [Finset.mem_insert,Finset.mem_singleton] at hq
            rcases hq with rfl | rfl | rfl | rfl
            · exact (hr_g3.2.2.1 hru).elim
            · exact (hr_g4.2.1 hru).elim
            · rfl
            · exact (hr_g7.2.2.1 hru).elim)
        · left
          exact hFe0 (fun q hq hrs=>by
            have hru:=hri0 q hq hrs
            rw [hA_eq] at hq;simp only [Finset.mem_insert,Finset.mem_singleton] at hq
            rcases hq with rfl | rfl | rfl | rfl
            · exact hr_g3.2.2.1 hru
            · exact hr_g4.2.1 hru
            · exact r6 hrs
            · exact hr_g7.2.2.1 hru)
      · by_cases r7 : rS s g7
        · right;right;right;right;left
          exact hF1 g7 hg7A r7 (fun q hq hrs=>by
            have hru:=hri0 q hq hrs
            rw [hA_eq] at hq;simp only [Finset.mem_insert,Finset.mem_singleton] at hq
            rcases hq with rfl | rfl | rfl | rfl
            · exact (hr_g3.2.2.2 hru).elim
            · exact (hr_g4.2.2.1 hru).elim
            · exact (hr_g6.2.2.2 hru).elim
            · rfl)
        · left
          exact hFe0 (fun q hq hrs=>by
            have hru:=hri0 q hq hrs
            rw [hA_eq] at hq;simp only [Finset.mem_insert,Finset.mem_singleton] at hq
            rcases hq with rfl | rfl | rfl | rfl
            · exact hr_g3.2.2.2 hru
            · exact hr_g4.2.2.1 hru
            · exact hr_g6.2.2.2 hru
            · exact r7 hrs)
    exact kill_AW1_aU4 (a:=a) (b:=b) (b3:=b3) (b4:=b4) (b6:=b6) (b7:=b7) (zs:=Sl.map zo)
      ha hb (hmem_sw g3 hg3A) (hmem_sw g4 hg4A) (hmem_sw g6 hg6A) (hmem_sw g7 hg7A)
      hb3_r1 hb3_r0 (hB4_eq ▸ hB_R1.2.1) (hB4_eq ▸ hB_R0.2.1)
      (hB6_eq ▸ hB_R1.2.2.1) (hB6_eq ▸ hB_R0.2.2.1) (hB7_eq ▸ hB_R1.2.2.2) (hB7_eq ▸ hB_R0.2.2.2)
      (fun z hz=>by
        obtain ⟨s,hs,rfl⟩:=List.mem_map.mp hz
        have hsS : s ∈ Sg:=Finset.mem_toList.mp hs
        obtain ⟨hlt,hnot⟩:=hsnU (Finset.mem_filter.mp hsS).1
        exact ⟨hz_safe s hsS,tt64 gs (sW s),Fo s,hmemW _ hlt hnot,hF_cases s hsS,rfl⟩)
      hz_cov
  have hk0 : Wa.card=0 → Ag.card=5 → False:=by
    intro hWa0 hA5
    have hdiff_card : (Ag \ {g3,g4,g6,g7}).card=1:=by
      have:=Finset.card_sdiff_add_card_eq_card h4_sub
      rw [h4_card] at this;omega
    obtain ⟨g5,hg5_eq⟩:=Finset.card_eq_one.mp hdiff_card
    have hg5_mem : g5 ∈ Ag \ {g3,g4,g6,g7}:=by rw [hg5_eq];simp
    have hg5A : g5 ∈ Ag:=(Finset.mem_sdiff.mp hg5_mem).1
    have hA_eq : Ag={g3,g4,g6,g7,g5}:=by
      ext q
      simp only [Finset.mem_insert,Finset.mem_singleton]
      constructor
      · intro hq
        by_cases h4m : q ∈ ({g3,g4,g6,g7} : Finset ℕ)
        · simp only [Finset.mem_insert,Finset.mem_singleton] at h4m
          rcases h4m with rfl | rfl | rfl | rfl<;>simp
        · have : q ∈ Ag \ {g3,g4,g6,g7}:=Finset.mem_sdiff.mpr ⟨hq,h4m⟩
          rw [hg5_eq,Finset.mem_singleton] at this;simp [this]
      · rintro (rfl | rfl | rfl | rfl | rfl)<;>assumption
    have hlam5_mem : sort5 1 (lM g4) 4 8 (lM g5) ∈ lam5List :=
      lam5_from_4 hg4_mask (hlbd g5 hg5A).1 (hlbd g5 hg5A).2 (hllm g4 hg4A g5 hg5A)
    let sorted:=sBK lM [g3,g4,g6,g7,g5]
    have hperm : sorted.Perm [g3,g4,g6,g7,g5]:=sortByKey_perm lM [g3,g4,g6,g7,g5]
    have hlen5 : sorted.length=5:=by have:=hperm.length_eq;simpa using this
    let q0:=sorted.getD 0 g3
    let q1:=sorted.getD 1 g3
    let q2:=sorted.getD 2 g3
    let q3:=sorted.getD 3 g3
    let q4:=sorted.getD 4 g3
    have hsorted_eq : sorted=[q0,q1,q2,q3,q4]:=by
      rcases h : sorted with _ | ⟨a0,_ | ⟨a1,_ | ⟨a2,_ | ⟨a3,_ | ⟨a4,_ | rest⟩⟩⟩⟩⟩
      all_goals try (rw [h] at hlen5;simp at hlen5)
      simp [q0,q1,q2,q3,q4,h]
    have hq_mem_A : ∀ q,q ∈ Ag ↔ q=q0 ∨ q=q1 ∨ q=q2 ∨ q=q3 ∨ q=q4:=by
      intro q
      rw [hA_eq]
      have hiff : q ∈ sorted ↔ q ∈ ([g3,g4,g6,g7,g5] : List ℕ):=hperm.mem_iff
      rw [hsorted_eq] at hiff
      simp only [Finset.mem_insert,Finset.mem_singleton,List.mem_cons,List.not_mem_nil,or_false] at hiff ⊢
      exact hiff.symm
    have hq0A : q0 ∈ Ag:=(hq_mem_A q0).mpr (Or.inl rfl)
    have hq1A : q1 ∈ Ag:=(hq_mem_A q1).mpr (Or.inr (Or.inl rfl))
    have hq2A : q2 ∈ Ag:=(hq_mem_A q2).mpr (Or.inr (Or.inr (Or.inl rfl)))
    have hq3A : q3 ∈ Ag:=(hq_mem_A q3).mpr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    have hq4A : q4 ∈ Ag:=(hq_mem_A q4).mpr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
    let s0:=lM q0;let s1:=lM q1;let s2:=lM q2;let s3:=lM q3;let s4:=lM q4
    let b0:=tt64 gs (sW q0);let b1:=tt64 gs (sW q1);let b2:=tt64 gs (sW q2)
    let b3:=tt64 gs (sW q3);let b4:=tt64 gs (sW q4)
    have htupl : (s0,s1,s2,s3,s4) ∈ lam5List:=by
      have heq:=sortByKey_map_eq lM g3 g4 g6 g7 g5
      change (s0,s1,s2,s3,s4)=sort5 (lM g3) (lM g4) (lM g6) (lM g7) (lM g5) at heq
      rw [hg3_mask,hg6_mask,hg7_mask] at heq
      rw [heq];exact hlam5_mem
    have hbpure : ∀ q ∈ Ag,tt64 gs (sW q) ∈ pOs ∧
        (tt64 gs (sW q)&&&rR1 (lM q))=rR1 (lM q):=fun q hq=>by
      obtain ⟨hlt,hnot⟩:=hsnU (Finset.mem_filter.mp hq).1
      exact ⟨hWp hWa0 _ hlt hnot,hsr1 q hq⟩
    have hB_eq_5 : ∀ (u : Fin 10) (bit : ℕ),
        (∀ q,(((lM q&&&bit) != 0)=true ↔ rU u q)) →
        ((if (s4&&&bit) != 0 then b4 else ALL64) &&&
         (if (s3&&&bit) != 0 then b3 else ALL64) &&&
         (if (s2&&&bit) != 0 then b2 else ALL64) &&&
         (if (s1&&&bit) != 0 then b1 else ALL64) &&&
         (if (s0&&&bit) != 0 then b0 else ALL64))=Bo u:=by
      intro u bit hbit
      apply Nat.eq_of_testBit_eq;intro i
      by_cases hi : i < 64
      · apply Bool.eq_iff_iff.mpr
        rw [hB_tb u i hi]
        have hterm : ∀ q,((if (lM q&&&bit) != 0 then tt64 gs (sW q) else ALL64).testBit i=true ↔
            (rU u q → vl gs (pt64 i) (sW q)=true)):=by
          intro q
          by_cases hc : ((lM q&&&bit) != 0)=true
          · rw [if_pos hc,tbT64];simp [hi,(hbit q).mp hc]
          · rw [if_neg hc,ALL64_testBit i,decide_eq_true hi];exact ⟨fun _ h=>(hc ((hbit q).mpr h)).elim,fun _=>rfl⟩
        simp only [Nat.testBit_and,Bool.and_eq_true,s0,s1,s2,s3,s4,b0,b1,b2,b3,b4,hterm]
        constructor
        · rintro ⟨⟨⟨⟨h4',h3'⟩,h2'⟩,h1'⟩,h0'⟩ q hq hru
          rcases (hq_mem_A q).mp hq with rfl | rfl | rfl | rfl | rfl
          · exact h0' hru
          · exact h1' hru
          · exact h2' hru
          · exact h3' hru
          · exact h4' hru
        · intro h
          exact ⟨⟨⟨⟨h q4 hq4A,h q3 hq3A⟩,h q2 hq2A⟩,h q1 hq1A⟩,h q0 hq0A⟩
      · have hA0 : ALL64.testBit i=false:=by rw [ALL64_testBit i];simp [hi]
        have hB0 : (Bo u).testBit i=false:=by rw [show Bo u=landMask _ from rfl,tbLM];simp [hi]
        have h0f : (if (s0&&&bit) != 0 then b0 else ALL64).testBit i=false:=by
          split_ifs
          · rw [tbT64];simp [hi]
          · exact hA0
        rw [Nat.testBit_and,h0f,Bool.and_false,hB0]
    have hfin3 : (((if (s4&&&1) != 0 then b4 else ALL64)&&&(if (s3&&&1) != 0 then b3 else ALL64) &&&
        (if (s2&&&1) != 0 then b2 else ALL64)&&&(if (s1&&&1) != 0 then b1 else ALL64) &&&
        (if (s0&&&1) != 0 then b0 else ALL64))&&&R0_3)=0:=by
      rw [hB_eq_5 3 1 (fun q=>(hlmb q).1)];exact hB_R0.1
    have hfin4 : (((if (s4&&&2) != 0 then b4 else ALL64)&&&(if (s3&&&2) != 0 then b3 else ALL64) &&&
        (if (s2&&&2) != 0 then b2 else ALL64)&&&(if (s1&&&2) != 0 then b1 else ALL64) &&&
        (if (s0&&&2) != 0 then b0 else ALL64))&&&R0_4)=0:=by
      rw [hB_eq_5 4 2 (fun q=>(hlmb q).2.1)];exact hB_R0.2.1
    have hfin6 : (((if (s4&&&4) != 0 then b4 else ALL64)&&&(if (s3&&&4) != 0 then b3 else ALL64) &&&
        (if (s2&&&4) != 0 then b2 else ALL64)&&&(if (s1&&&4) != 0 then b1 else ALL64) &&&
        (if (s0&&&4) != 0 then b0 else ALL64))&&&R0_6)=0:=by
      rw [hB_eq_5 6 4 (fun q=>(hlmb q).2.2.1)];exact hB_R0.2.2.1
    have hfin7 : (((if (s4&&&8) != 0 then b4 else ALL64)&&&(if (s3&&&8) != 0 then b3 else ALL64) &&&
        (if (s2&&&8) != 0 then b2 else ALL64)&&&(if (s1&&&8) != 0 then b1 else ALL64) &&&
        (if (s0&&&8) != 0 then b0 else ALL64))&&&R0_7)=0:=by
      rw [hB_eq_5 7 8 (fun q=>(hlmb q).2.2.2)];exact hB_R0.2.2.2
    exact kill_AW0_aU5 (s0:=s0) (s1:=s1) (s2:=s2) (s3:=s3) (s4:=s4)
      (b0:=b0) (b1:=b1) (b2:=b2) (b3:=b3) (b4:=b4) (zs:=Sl.map zo)
      htupl (hbpure q0 hq0A) (hbpure q1 hq1A) (hbpure q2 hq2A) (hbpure q3 hq3A) (hbpure q4 hq4A)
      hfin3 hfin4 hfin6 hfin7
      (fun z hz=>by
        obtain ⟨s,hs,rfl⟩:=List.mem_map.mp hz
        have hsS : s ∈ Sg:=Finset.mem_toList.mp hs
        obtain ⟨hlt,hnot⟩:=hsnU (Finset.mem_filter.mp hsS).1
        let sub : ℕ :=
          (if rS s q0 then 1 else 0) |||
          (if rS s q1 then 2 else 0) |||
          (if rS s q2 then 4 else 0) |||
          (if rS s q3 then 8 else 0) |||
          (if rS s q4 then 16 else 0)
        have hsp:=sub5_props (decide (rS s q0)) (decide (rS s q1))
          (decide (rS s q2)) (decide (rS s q3)) (decide (rS s q4))
        have hsub_eq : sub=((if decide (rS s q0) then 1 else 0)|||(if decide (rS s q1) then 2 else 0) |||
            (if decide (rS s q2) then 4 else 0)|||(if decide (rS s q3) then 8 else 0) |||
            (if decide (rS s q4) then 16 else 0)):=by simp [sub]
        dsimp only at hsp;rw [← hsub_eq] at hsp
        have hsub_lt : sub < 32:=hsp.1
        have hsub_bit : ∀ (k : ℕ),k < 5 →
            ((((sub>>>k)&&&1) != 0)=true ↔ rS s (sorted.getD k g3)):=by
          intro k hk
          rcases k with _ | _ | _ | _ | _ | k
          · rw [hsp.2.1];simp [q0]
          · rw [hsp.2.2.1];simp [q1]
          · rw [hsp.2.2.2.1];simp [q2]
          · rw [hsp.2.2.2.2.1];simp [q3]
          · rw [hsp.2.2.2.2.2.1];simp [q4]
          · omega
        have hsub_and :
            (((sub&&&1) != 0)=true ↔ rS s q0) ∧
            (((sub&&&2) != 0)=true ↔ rS s q1) ∧
            (((sub&&&4) != 0)=true ↔ rS s q2) ∧
            (((sub&&&8) != 0)=true ↔ rS s q3) ∧
            (((sub&&&16) != 0)=true ↔ rS s q4):=by
          rw [hsp.2.2.2.2.2.2.1,hsp.2.2.2.2.2.2.2.1,hsp.2.2.2.2.2.2.2.2.1,
              hsp.2.2.2.2.2.2.2.2.2.1,hsp.2.2.2.2.2.2.2.2.2.2]
          simp
        have hsub_valid : sub ∈ vS5 s0 s1 s2 s3 s4:=by
          unfold vS5
          refine List.mem_filter.mpr ⟨List.mem_range.mpr hsub_lt,?_⟩
          rw [List.all_eq_true];intro i hi
          rw [List.all_eq_true];intro j hj
          obtain ⟨hir,hib⟩:=List.mem_filter.mp hi
          obtain ⟨hjr,hjb⟩:=List.mem_filter.mp hj
          have hi5 : i < 5:=List.mem_range.mp hir
          have hj5 : j < 5:=List.mem_range.mp hjr
          have hri:=(hsub_bit i hi5).mp hib
          have hrj:=(hsub_bit j hj5).mp hjb
          obtain ⟨hs',hqi,_,rsqi⟩:=hri
          obtain ⟨_,hqj,_,rsqj⟩:=hrj
          have hss_get : ∀ k < 5,([s0,s1,s2,s3,s4] : List ℕ).getD k 0=lM (sorted.getD k g3):=by
            intro k hk;rcases k with _ | _ | _ | _ | _ | k<;>[rfl;rfl;rfl;rfl;rfl;omega]
          rw [hss_get i hi5,hss_get j hj5]
          unfold nested
          rcases uLam (hUi (hS_sub hsS)).2 rsqi rsqj with rij | rji
          · have heq:=hlsp hqi hqj rij;simp only [Bool.or_eq_true,beq_iff_eq];exact Or.inl heq
          · have heq:=hlsp hqj hqi rji;rw [bac] at heq;simp only [Bool.or_eq_true,beq_iff_eq];exact Or.inr heq
        have hF_eq_cm : Fo s=cM5 sub b0 b1 b2 b3 b4:=by
          apply Nat.eq_of_testBit_eq;intro i
          have h64 : ∀ j < 64,ALL64.testBit j=true:=fun j hj=>by rw [ALL64_testBit j];simp [hj]
          have hcm_tb : ∀ j < 64,(cM5 sub b0 b1 b2 b3 b4).testBit j=true ↔
              (rS s q0 → vl gs (pt64 j) (sW q0)=true) ∧
              (rS s q1 → vl gs (pt64 j) (sW q1)=true) ∧
              (rS s q2 → vl gs (pt64 j) (sW q2)=true) ∧
              (rS s q3 → vl gs (pt64 j) (sW q3)=true) ∧
              (rS s q4 → vl gs (pt64 j) (sW q4)=true):=by
            intro j hj
            unfold cM5;dsimp only
            have hstep : ∀ (f : ℕ) (cond : Bool) (b : ℕ) (P : Prop),
                (cond=true ↔ P) →
                ((if cond=true then f&&&b else f).testBit j=true ↔
                  f.testBit j=true ∧ (P → b.testBit j=true)):=by
              intro f cond b P hc
              cases cond
              · simp only [Bool.false_eq_true,↓reduceIte];exact ⟨fun h=>⟨h,fun hp=>by have:=hc.mpr hp;cases this⟩,fun h=>h.1⟩
              · simp [Nat.testBit_and,hc.mp rfl]
            rw [hstep _ _ _ _ hsub_and.2.2.2.2,hstep _ _ _ _ hsub_and.2.2.2.1,
                hstep _ _ _ _ hsub_and.2.2.1,hstep _ _ _ _ hsub_and.2.1]
            have h0 : ((if (sub&&&1) != 0 then b0 else ALL64).testBit j=true ↔
                (rS s q0 → b0.testBit j=true)):=by
              cases h0c : ((sub&&&1) != 0)
              · simp only [Bool.false_eq_true,↓reduceIte,h64 j hj];exact ⟨fun _ hp=>(by have:=hsub_and.1.mpr hp;rw [h0c] at this;cases this),fun _=>trivial⟩
              · simp [hsub_and.1.mp h0c]
            rw [h0]
            simp only [b0,b1,b2,b3,b4,tbT64,hj,decide_true,Bool.true_and]
            exact ⟨fun h=>⟨h.1.1.1.1,h.1.1.1.2,h.1.1.2,h.1.2,h.2⟩,
              fun ⟨h0',h1',h2',h3',h4'⟩=>⟨⟨⟨⟨h0',h1'⟩,h2'⟩,h3'⟩,h4'⟩⟩
          by_cases hi : i < 64
          · apply Bool.eq_iff_iff.mpr
            rw [hF_tb s i hi,hcm_tb i hi]
            constructor
            · intro h;exact ⟨h q0 hq0A,h q1 hq1A,h q2 hq2A,h q3 hq3A,h q4 hq4A⟩
            · rintro ⟨h0,h1,h2,h3',h4'⟩ q hq hrs
              rcases (hq_mem_A q).mp hq with rfl | rfl | rfl | rfl | rfl
              · exact h0 hrs
              · exact h1 hrs
              · exact h2 hrs
              · exact h3' hrs
              · exact h4' hrs
          · have h1 : (Fo s).testBit i=false:=by rw [show Fo s=landMask _ from rfl,tbLM];simp [hi]
            have h2 : (cM5 sub b0 b1 b2 b3 b4).testBit i=false:=by
              have hA0f : ALL64.testBit i=false:=by rw [ALL64_testBit i];simp [hi]
              unfold cM5;dsimp only
              have h0f : (if (sub&&&1) != 0 then b0 else ALL64).testBit i=false:=by
                split_ifs
                · rw [tbT64];simp [hi]
                · exact hA0f
              have hstepf : ∀ (f : ℕ) (cond : Bool) (b : ℕ),f.testBit i=false →
                  (if cond=true then f&&&b else f).testBit i=false:=by
                intro f cond b hf;split_ifs<;>simp [Nat.testBit_and,hf]
              exact hstepf _ _ _ (hstepf _ _ _ (hstepf _ _ _ (hstepf _ _ _ h0f)))
            rw [h1,h2]
        exact ⟨hz_safe s hsS,tt64 gs (sW s),sub,hWp hWa0 _ hlt hnot,hsub_valid,by
          show zo s=tt64 gs (sW s)&&&cM5 sub b0 b1 b2 b3 b4
          rw [← hF_eq_cm]⟩)
      hz_cov
  have hWfa : Wo.filter (· < gs.length)=Wo:=by
    ext p;simp only [Finset.mem_filter,and_iff_left_iff_imp]
    intro hp;exact Finset.mem_range.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp hp).1).1
  by_cases hOW3 : Wo.card ≤ 3
  · have hsim15 : ∀ k ≤ gs.length,
        ∃ S : List ℕ,S.Pairwise (· < ·) ∧ (∀ w ∈ S,V15 w) ∧ ACl S ∧
          (∀ w < 10 + k,∀ hw : w < 10 + gs.length,¬ inU ⟨w,hw⟩ → proj15 (tt64 gs w) ∈ S) ∧
          (∀ T,Reach15 (Wo.card - (Wo.filter (· < k)).card) S T → Reach15 Wo.card C0_15W T):=by
      intro k
      induction k with
      | zero =>
        intro _
        obtain ⟨hP0,hV0,hC0⟩:=C0_15W_props
        refine ⟨C0_15W,hP0,hV0,hC0,?_,?_⟩
        · intro w hw10 hw hnot
          have hb:=hbtz w hw10 hw hnot
          simpa [List.elem_eq_mem] using List.all_eq_true.mp proj_base_mem.1 (tt64 gs w) hb
        · intro T hT
          have hf0 : (Wo.filter (· < 0)).card=0:=by
            rw [Finset.card_eq_zero,Finset.filter_eq_empty_iff];intro p _;omega
          rw [hf0,Nat.sub_zero] at hT;exact hT
      | succ k ih =>
        intro hk
        obtain ⟨S,hP,hV,hC,hmem,hcont⟩:=ih (by omega)
        have hsub_le : (Wo.filter (· < k + 1)).card ≤ Wo.card:=Finset.card_le_card (Finset.filter_subset ..)
        by_cases hkO : k ∈ Wo
        · have hfilt_eq : Wo.filter (· < k + 1)=insert k (Wo.filter (· < k)):=by
            ext p;simp only [Finset.mem_filter,Finset.mem_insert]
            constructor
            · rintro ⟨hp,hlt⟩
              by_cases hpk : p=k
              · exact Or.inl hpk
              · exact Or.inr ⟨hp,by omega⟩
            · rintro (rfl | ⟨hp,hlt⟩)
              · exact ⟨hkO,by omega⟩
              · exact ⟨hp,by omega⟩
          have hcard_inc : (Wo.filter (· < k + 1)).card=(Wo.filter (· < k)).card + 1:=by
            rw [hfilt_eq,Finset.card_insert_of_notMem (by simp)]
          obtain ⟨hkW,g,hgk,hgor⟩:=Finset.mem_filter.mp hkO
          obtain ⟨_,ia,ib,hia,hib,_,hgin⟩:=cmG hcl hmono distinct hgk
          have hnot_k : ¬ inU ⟨10 + k,by omega⟩:=fun h =>
            (Finset.mem_sdiff.mp hkW).2 (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),by omega,h⟩)
          have hnia : ¬ inU ⟨ia,by omega⟩:=fun h=>hnot_k (uMem h ⟨k,g,hgk,rfl,by rw [hgin];simp⟩)
          have hnib : ¬ inU ⟨ib,by omega⟩:=fun h=>hnot_k (uMem h ⟨k,g,hgk,rfl,by rw [hgin];simp⟩)
          have hpa : proj15 (tt64 gs ia) ∈ S:=hmem ia hia (by omega) hnia
          have hpb : proj15 (tt64 gs ib) ∈ S:=hmem ib hib (by omega) hnib
          let o:=wOr (proj15 (tt64 gs ia)) (proj15 (tt64 gs ib))
          have hoV : V15 o:=v15o (hV _ hpa) (hV _ hpb)
          have hgk_eq : gs[k]?=some ⟨GateOp.or,[ia,ib]⟩:=by
            rw [hgk];congr 1;cases g;simp at hgor hgin;exact congrArg₂ Gate.mk hgor hgin
          refine ⟨aOW S o,pwAOW hP o,?_,acAOW hC o,?_,?_⟩
          · intro w hw;rw [mAOW] at hw
            rcases hw with hwS | rfl | ⟨x,hx,rfl⟩
            · exact hV w hwS
            · exact hoV
            · exact v15a (hV x hx) hoV
          · intro w hwlt hw hnot
            by_cases hwk : w=10 + k
            · subst hwk;rw [tt64_gate_or hcl hgk_eq,p15o,mAOW];exact Or.inr (Or.inl rfl)
            · rw [mAOW];exact Or.inl (hmem w (by omega) hw hnot)
          · intro T hT
            apply hcont T
            have hsub_eq : Wo.card - (Wo.filter (· < k)).card =
                (Wo.card - (Wo.filter (· < k + 1)).card) + 1:=by omega
            rw [hsub_eq]
            exact Or.inr ⟨_,hpa,_,hpb,hT⟩
        · have hfilt_eq : Wo.filter (· < k + 1)=Wo.filter (· < k):=by
            ext p;simp only [Finset.mem_filter]
            constructor
            · rintro ⟨hp,hlt⟩;exact ⟨hp,by have : p ≠ k:=fun e=>hkO (e ▸ hp);omega⟩
            · rintro ⟨hp,hlt⟩;exact ⟨hp,by omega⟩
          refine ⟨S,hP,hV,hC,?_,fun T hT=>hcont T (by rwa [hfilt_eq] at hT)⟩
          intro w hwlt hw hnot
          by_cases hwk : w=10 + k
          · subst hwk
            have hkW : k ∈ Wg:=Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr (by omega),fun h=>hnot (hUi h).2⟩
            have hgk : gs[k]?=some (gs[k]'(by omega)):=List.getElem?_eq_getElem (by omega)
            obtain ⟨hop,ia,ib,hia,hib,_,hgin⟩:=cmG hcl hmono distinct hgk
            have hand : (gs[k]'(by omega)).op=GateOp.and:=by
              rcases hop with hand | hor
              · exact hand
              · exact (hkO (Finset.mem_filter.mpr ⟨hkW,_,hgk,hor⟩)).elim
            have hnia : ¬ inU ⟨ia,by omega⟩:=fun h=>hnot (uMem h ⟨k,_,hgk,rfl,by rw [hgin];simp⟩)
            have hnib : ¬ inU ⟨ib,by omega⟩:=fun h=>hnot (uMem h ⟨k,_,hgk,rfl,by rw [hgin];simp⟩)
            have hgk_eq : gs[k]?=some ⟨GateOp.and,[ia,ib]⟩:=by
              rw [hgk];congr 1;cases hgx : gs[k]'(by omega);simp [hgx] at hand hgin;exact congrArg₂ Gate.mk hand hgin
            rw [tt64_gate_and hcl hgk_eq,p15a]
            exact hC _ (hmem ia hia (by omega) hnia) _ (hmem ib hib (by omega) hnib)
          · exact hmem w (by omega) hw hnot
    obtain ⟨T,_,hVT,hCT,hmemT,hcontT⟩:=hsim15 gs.length (le_refl _)
    have hsw_memT : ∀ q ∈ Ag,proj15 (tt64 gs (sW q)) ∈ T:=fun q hq=>by
      obtain ⟨hlt,hnot⟩:=hsnU (Finset.mem_filter.mp hq).1
      exact hmemT (sW q) hlt hlt hnot
    have hB_memT : ∀ u g,g ∈ Ag → rU u g → proj15 (Bo u) ∈ T:=by
      intro u g hgA hrug
      apply p15LM hCT
      · intro hnil
        have hm : tt64 gs (sW g) ∈ (Aau u).map (fun q=>tt64 gs (sW q)) :=
          List.mem_map.mpr ⟨g,List.mem_filter.mpr ⟨Finset.mem_toList.mpr hgA,decide_eq_true hrug⟩,rfl⟩
        rw [hnil] at hm;cases hm
      · intro x hx;obtain ⟨q,_,rfl⟩:=List.mem_map.mp hx;exact tt64_and_ALL64 gs (sW q)
      · intro x hx;obtain ⟨q,hqf,rfl⟩:=List.mem_map.mp hx
        exact hsw_memT q (Finset.mem_toList.mp (List.mem_filter.mp hqf).1)
    have hB6_T:=hB_memT 6 g6 hg6A ((hlmb g6).2.2.1.mp (by rw [hg6_mask];decide))
    have hB7_T:=hB_memT 7 g7 hg7A ((hlmb g7).2.2.2.mp (by rw [hg7_mask];decide))
    have hB3_T:=hB_memT 3 g3 hg3A ((hlmb g3).1.mp (by rw [hg3_mask];decide))
    have hgoalT : lb15B (st15 T)=0:=(s15G hVT hCT).mpr
      ⟨⟨_,hB6_T,p15B6 hB_R1.2.2.1 hB_R0.2.2.1⟩,
       ⟨_,hB7_T,p15B7 hB_R1.2.2.2 hB_R0.2.2.2⟩,
       ⟨_,hB3_T,p15B3 hB_R1.1 hB_R0.1⟩⟩
    have hr_W : Reach15 Wo.card C0_15W T :=
      hcontT T (by rw [hWfa,Nat.sub_self];exact ⟨rfl,hgoalT⟩)
    have hlb3 : 3 ≤ Wo.card:=by
      have hlb:=lb15R Wo.card C0_15W T C0_15W_props.2.1 C0_15W_props.2.2 hr_W
      rw [proj_base_mem.2.2] at hlb;exact hlb
    have hr3 : Reach15 3 C0_15W T:=reach15_mono hOW3 hr_W
    have hpop1 : ∀ z ∈ Sl.map zo,pop4 (edgesOf z) ≤ 1:=by
      intro z hz
      obtain ⟨s,hs,rfl⟩:=List.mem_map.mp hz
      have hsS : s ∈ Sg:=Finset.mem_toList.mp hs
      obtain ⟨hlt,hnot⟩:=hsnU (Finset.mem_filter.mp hsS).1
      have hzT : proj15 (zo s) ∈ T :=
        p15aLM hCT (tt64 gs (sW s)) _
          (tt64_and_ALL64 gs (sW s)) (hmemT _ hlt hlt hnot)
          (fun x hx=>by obtain ⟨q,_,rfl⟩:=List.mem_map.mp hx;exact tt64_and_ALL64 gs (sW q))
          (fun x hx=>by obtain ⟨q,hqf,rfl⟩:=List.mem_map.mp hx;exact hsw_memT q (Finset.mem_toList.mp (List.mem_filter.mp hqf).1))
      obtain ⟨hl0,he4,he3,_,_⟩:=pSZ (hz_safe s hsS)
      have hle1:=kill_OW3 hr3 (proj15 (zo s)) hzT hl0 he4
      rwa [he3] at hle1
    have hS_ge4 : 4 ≤ Sg.card:=by
      have hp:=foldl_edges_pop_le (Sl.map zo) hpop1
      rw [hz_cov,List.length_map,Finset.length_toList] at hp
      have hp15 : pop4 15=4:=by decide
      omega
    exact hk1 (by omega) (by omega)
  · by_cases hC1 : Wa.card ≤ 1 ∧ Ag.card=4
    · exact hk1 hC1.1 hC1.2
    · by_cases hC2 : Wa.card=0 ∧ Ag.card=5
      · exact hk0 hC2.1 hC2.2
      · have hOW4 : Wo.card=4:=by omega
        have hS1 : Sg.card=1:=by omega
        obtain ⟨s0,hs0_eq⟩:=Finset.card_eq_one.mp hS1
        have hs0S : s0 ∈ Sg:=by rw [hs0_eq];simp
        have hSlist_eq : Sl=[s0]:=by
          have hlen1 : Sl.length=1:=by rw [Finset.length_toList];exact hS1
          rcases h : Sl with _ | ⟨x,_ | rest⟩
          · rw [h] at hlen1;simp at hlen1
          · have hx : x ∈ Sg:=Finset.mem_toList.mp (show x ∈ Sl by rw [h];simp)
            rw [hs0_eq,Finset.mem_singleton] at hx;subst hx;rfl
          · rw [h] at hlen1;simp at hlen1
        have hz0_e15 : edgesOf (zo s0)=15:=by
          rw [hSlist_eq] at hz_cov;simpa [bo0l] using hz_cov
        have hsim14 : ∀ k ≤ gs.length,
            ∃ S : List ℕ,S.Pairwise (· < ·) ∧ (∀ w ∈ S,V14 w) ∧ ACl S ∧
              (∀ w < 10 + k,∀ hw : w < 10 + gs.length,¬ inU ⟨w,hw⟩ → proj14 (tt64 gs w) ∈ S) ∧
              (Reach14 (Wo.card - (Wo.filter (· < k)).card) S → Reach14 Wo.card C0W):=by
          intro k
          induction k with
          | zero =>
            intro _
            obtain ⟨hP0,hV0,hC0⟩:=C0W_props
            refine ⟨C0W,hP0,hV0,hC0,?_,?_⟩
            · intro w hw10 hw hnot
              have hb:=hbtz w hw10 hw hnot
              simpa [List.elem_eq_mem] using List.all_eq_true.mp proj_base_mem.2.1 (tt64 gs w) hb
            · intro hT
              have hf0 : (Wo.filter (· < 0)).card=0:=by
                rw [Finset.card_eq_zero,Finset.filter_eq_empty_iff];intro p _;omega
              rw [hf0,Nat.sub_zero] at hT;exact hT
          | succ k ih =>
            intro hk
            obtain ⟨S,hP,hV,hC,hmem,hcont⟩:=ih (by omega)
            have hsub_le : (Wo.filter (· < k + 1)).card ≤ Wo.card:=Finset.card_le_card (Finset.filter_subset ..)
            by_cases hkO : k ∈ Wo
            · have hfilt_eq : Wo.filter (· < k + 1)=insert k (Wo.filter (· < k)):=by
                ext p;simp only [Finset.mem_filter,Finset.mem_insert]
                constructor
                · rintro ⟨hp,hlt⟩
                  by_cases hpk : p=k
                  · exact Or.inl hpk
                  · exact Or.inr ⟨hp,by omega⟩
                · rintro (rfl | ⟨hp,hlt⟩)
                  · exact ⟨hkO,by omega⟩
                  · exact ⟨hp,by omega⟩
              have hcard_inc : (Wo.filter (· < k + 1)).card=(Wo.filter (· < k)).card + 1:=by
                rw [hfilt_eq,Finset.card_insert_of_notMem (by simp)]
              obtain ⟨hkW,g,hgk,hgor⟩:=Finset.mem_filter.mp hkO
              obtain ⟨_,ia,ib,hia,hib,_,hgin⟩:=cmG hcl hmono distinct hgk
              have hnot_k : ¬ inU ⟨10 + k,by omega⟩:=fun h =>
                (Finset.mem_sdiff.mp hkW).2 (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),by omega,h⟩)
              have hnia : ¬ inU ⟨ia,by omega⟩:=fun h=>hnot_k (uMem h ⟨k,g,hgk,rfl,by rw [hgin];simp⟩)
              have hnib : ¬ inU ⟨ib,by omega⟩:=fun h=>hnot_k (uMem h ⟨k,g,hgk,rfl,by rw [hgin];simp⟩)
              have hpa : proj14 (tt64 gs ia) ∈ S:=hmem ia hia (by omega) hnia
              have hpb : proj14 (tt64 gs ib) ∈ S:=hmem ib hib (by omega) hnib
              let o:=wOr (proj14 (tt64 gs ia)) (proj14 (tt64 gs ib))
              have hoV : V14 o:=v14o (hV _ hpa) (hV _ hpb)
              have hgk_eq : gs[k]?=some ⟨GateOp.or,[ia,ib]⟩:=by
                rw [hgk];congr 1;cases g;simp at hgor hgin;exact congrArg₂ Gate.mk hgor hgin
              refine ⟨aOW S o,pwAOW hP o,?_,acAOW hC o,?_,?_⟩
              · intro w hw;rw [mAOW] at hw
                rcases hw with hwS | rfl | ⟨x,hx,rfl⟩
                · exact hV w hwS
                · exact hoV
                · exact v14a (hV x hx) hoV
              · intro w hwlt hw hnot
                by_cases hwk : w=10 + k
                · subst hwk;rw [tt64_gate_or hcl hgk_eq,p14o,mAOW];exact Or.inr (Or.inl rfl)
                · rw [mAOW];exact Or.inl (hmem w (by omega) hw hnot)
              · intro hT
                apply hcont
                have hsub_eq : Wo.card - (Wo.filter (· < k)).card =
                    (Wo.card - (Wo.filter (· < k + 1)).card) + 1:=by omega
                rw [hsub_eq]
                exact Or.inr ⟨_,hpa,_,hpb,hT⟩
            · have hfilt_eq : Wo.filter (· < k + 1)=Wo.filter (· < k):=by
                ext p;simp only [Finset.mem_filter]
                constructor
                · rintro ⟨hp,hlt⟩;exact ⟨hp,by have : p ≠ k:=fun e=>hkO (e ▸ hp);omega⟩
                · rintro ⟨hp,hlt⟩;exact ⟨hp,by omega⟩
              refine ⟨S,hP,hV,hC,?_,fun hT=>hcont (by rwa [hfilt_eq] at hT)⟩
              intro w hwlt hw hnot
              by_cases hwk : w=10 + k
              · subst hwk
                have hkW : k ∈ Wg:=Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr (by omega),fun h=>hnot (hUi h).2⟩
                have hgk : gs[k]?=some (gs[k]'(by omega)):=List.getElem?_eq_getElem (by omega)
                obtain ⟨hop,ia,ib,hia,hib,_,hgin⟩:=cmG hcl hmono distinct hgk
                have hand : (gs[k]'(by omega)).op=GateOp.and:=by
                  rcases hop with hand | hor
                  · exact hand
                  · exact (hkO (Finset.mem_filter.mpr ⟨hkW,_,hgk,hor⟩)).elim
                have hnia : ¬ inU ⟨ia,by omega⟩:=fun h=>hnot (uMem h ⟨k,_,hgk,rfl,by rw [hgin];simp⟩)
                have hnib : ¬ inU ⟨ib,by omega⟩:=fun h=>hnot (uMem h ⟨k,_,hgk,rfl,by rw [hgin];simp⟩)
                have hgk_eq : gs[k]?=some ⟨GateOp.and,[ia,ib]⟩:=by
                  rw [hgk];congr 1;cases hgx : gs[k]'(by omega);simp [hgx] at hand hgin;exact congrArg₂ Gate.mk hand hgin
                rw [tt64_gate_and hcl hgk_eq,p14a]
                exact hC _ (hmem ia hia (by omega) hnia) _ (hmem ib hib (by omega) hnib)
              · exact hmem w (by omega) hw hnot
        obtain ⟨T,_,hVT,hCT,hmemT,hcontT⟩:=hsim14 gs.length (le_refl _)
        have hsw_memT : ∀ q ∈ Ag,proj14 (tt64 gs (sW q)) ∈ T:=fun q hq=>by
          obtain ⟨hlt,hnot⟩:=hsnU (Finset.mem_filter.mp hq).1
          exact hmemT (sW q) hlt hlt hnot
        have hB_memT : ∀ u g,g ∈ Ag → rU u g → proj14 (Bo u) ∈ T:=by
          intro u g hgA hrug
          apply p14LM hCT
          · intro hnil
            have hm : tt64 gs (sW g) ∈ (Aau u).map (fun q=>tt64 gs (sW q)) :=
              List.mem_map.mpr ⟨g,List.mem_filter.mpr ⟨Finset.mem_toList.mpr hgA,decide_eq_true hrug⟩,rfl⟩
            rw [hnil] at hm;cases hm
          · intro x hx;obtain ⟨q,_,rfl⟩:=List.mem_map.mp hx;exact tt64_and_ALL64 gs (sW q)
          · intro x hx;obtain ⟨q,hqf,rfl⟩:=List.mem_map.mp hx
            exact hsw_memT q (Finset.mem_toList.mp (List.mem_filter.mp hqf).1)
        obtain ⟨hlt0,hnot0⟩:=hsnU (Finset.mem_filter.mp hs0S).1
        have hz0T : proj14 (zo s0) ∈ T :=
          p14aLM hCT (tt64 gs (sW s0)) _
            (tt64_and_ALL64 gs (sW s0)) (hmemT _ hlt0 hlt0 hnot0)
            (fun x hx=>by obtain ⟨q,_,rfl⟩:=List.mem_map.mp hx;exact tt64_and_ALL64 gs (sW q))
            (fun x hx=>by obtain ⟨q,hqf,rfl⟩:=List.mem_map.mp hx;exact hsw_memT q (Finset.mem_toList.mp (List.mem_filter.mp hqf).1))
        obtain ⟨_,_,_,hl0_14,he4_14⟩:=pSZ (hz_safe s0 hs0S)
        have hgoalT : lb14B (st14 T)=0:=(s14G hVT hCT).mpr
          ⟨⟨_,hB_memT 6 g6 hg6A ((hlmb g6).2.2.1.mp (by rw [hg6_mask];decide)),p14B6 hB_R1.2.2.1 hB_R0.2.2.1⟩,
           ⟨_,hB_memT 7 g7 hg7A ((hlmb g7).2.2.2.mp (by rw [hg7_mask];decide)),p14B7 hB_R1.2.2.2 hB_R0.2.2.2⟩,
           ⟨_,hB_memT 3 g3 hg3A ((hlmb g3).1.mp (by rw [hg3_mask];decide)),p14B3 hB_R1.1 hB_R0.1⟩,
           ⟨_,hz0T,he4_14.trans hz0_e15,hl0_14⟩⟩
        have hr4 : Reach14 4 C0W:=by
          have:=hcontT (by rw [hWfa,Nat.sub_self];exact hgoalT)
          rwa [hOW4] at this
        exact kill_OW4 hr4
end S91
end PEqualNP.Outside.L_meta_4369

theorem PEqualNP.Outside.L_meta_4369 : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); have x2 : (Fin (9 : ℕ) → Bool) → List Bool := fun (x2 : Fin (9 : ℕ) → Bool) => List.ofFn x2 ++ [x2 (0 : Fin (9 : ℕ)) || x2 (3 : Fin (9 : ℕ))]; have x3 : PEqualNP.CircuitLowerBounds.GateOp → List ℕ := fun (x3 : PEqualNP.CircuitLowerBounds.GateOp) => if x3.eval [] = Bool.true then [(3 : ℕ), (9 : ℕ), (30 : ℕ), (39 : ℕ), (49 : ℕ)] else [(2 : ℕ), (4 : ℕ), (8 : ℕ), (31 : ℕ), (34 : ℕ), (35 : ℕ)]; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit),   have x5 : List ℕ := x4.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates;   have x6 : ℕ := (List.filter (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.op.eval [Bool.false] && !x6.op.eval [Bool.true]) x4.gates).length;   PEqualNP.MetaComplexity.FanInTwo x4 → x4.size = (14 : ℕ) → (∀ x9 ∈ x5, x9 ≤ (24 : ℕ)) → (∀ x10 < (24 : ℕ), x10 ∈ x5) → (9 : ℕ) + x6 + ∑ x11 ∈ Finset.range (24 : ℕ), (List.count x11 x5 - (1 : ℕ)) ≤ (14 : ℕ) → (2 : ℕ) ≤ List.count (9 : ℕ) x5 → (∀ (x13 : Fin (9 : ℕ)), ∃ (x14 : Fin (9 : ℕ) → Bool), x4.eval (List.ofFn x14 ++ [x14 x13]) ≠ x1 x14) → ∀ (x14 : Finset ℕ), x14.card + x6 ≤ (4 : ℕ) → (∀ x16 ∈ x4.gates, ∀ (x18 : Fin (9 : ℕ)) (x19 : Fin (10 : ℕ)), x16.inputs = [↑x18, ↑x19] ∨ x16.inputs = [↑x19, ↑x18] → x16.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x16.op = PEqualNP.CircuitLowerBounds.GateOp.or → (10 : ℕ) * ↑x18 + ↑x19 ∉ x3 x16.op → ↑x18 ∈ x14) → ({ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [(0 : ℕ), (3 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } ∈ x4.gates ∨ { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [(3 : ℕ), (0 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } ∈ x4.gates → (0 : ℕ) ∈ x14 ∨ (3 : ℕ) ∈ x14) → ∃ (x18 : Fin (9 : ℕ) → Bool), x4.eval (x2 x18) ≠ x1 x18 := by
  intro x1 x2 x3 x4 x5 x6 hfin hsz hbound hused hbudg h9 hdiff x14 _ _ _
  have hf : ∀ x : Fin 9 → Bool, x1 x = PEqualNP.Outside.L_meta_4369.S91.fTarget x := by
    intro x
    simp only [x1, PEqualNP.Outside.L_meta_4369.S91.fTarget, List.any_cons, List.any_nil,
      Bool.or_assoc, Bool.or_false]
    rfl
  by_contra hcomp
  push Not at hcomp
  obtain ⟨gs, hcl, out, live, hmono, hlen, hnd, hcomp', h3, h4, h6, h7⟩ :=
    PEqualNP.Outside.L_meta_4369.S91.reduce_to_mono_3467 x4 hfin hsz
      ⟨hbound _ (List.mem_cons_self ..), fun g hg i hi =>
        hbound _ (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨g, hg, hi⟩))⟩
      hused hbudg h9 (fun p => (hdiff p).imp fun x hx => by rwa [hf] at hx)
      (fun x => (hcomp x).trans (hf x))
  exact PEqualNP.Outside.L_meta_4369.S91.bomb2_impossible gs hcl out live hmono hlen hnd hcomp' h3 h4 h6 h7
