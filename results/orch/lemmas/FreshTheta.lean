import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1031.FreshTheta

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt2 (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt2 gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt2 gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt2 _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj


def W {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  val C (List.ofFn x) w

lemma W_raw {n : ℕ} (C : Circuit) (x : Fin n → Bool) (v : Fin n) : W C x v = x v := by
  unfold W
  rw [val_input (n:=n) (by simp) v.isLt]
  simp [List.getD_eq_getElem?_getD]

lemma W_binary {n : ℕ} (C : Circuit) (x : Fin n → Bool) {k s t : ℕ} {op : GateOp}
    (he : C.gates[k]? = some ⟨op,[s,t]⟩) (hs : s < n+k) (ht : t < n+k) :
    W C x (n+k) = op.eval [W C x s,W C x t] := by
  obtain ⟨hk,hg⟩ := List.getElem?_eq_some_iff.mp he
  unfold W
  rw [val_gate (n:=n) (by simp) hk, gateAt_eq hk, hg]
  simp [hs, ht]

def EdgeStep (n : ℕ) (C : Circuit) (u v : ℕ) : Prop :=
  u < v ∧ ∃ k g, v = n+k ∧ C.gates[k]? = some g ∧ u ∈ g.inputs

def pairInput {n : ℕ} (u v : Fin n) (i : Fin n) : Bool := decide (i=u ∨ i=v)

def Owns {n : ℕ} (C : Circuit) (k : ℕ) (u v : Fin n) : Prop :=
  W C (pairInput u v) (n+k) = true ∧ ∀ j g,
    C.gates[j]? = some g → g.op = GateOp.and →
    Relation.TransGen (EdgeStep n C) (n+j) (n+k) → W C (pairInput u v) (n+j)=false

lemma reach_lt {n : ℕ} {C : Circuit} {u v : ℕ}
    (h : Relation.TransGen (EdgeStep n C) u v) : u < v := by
  induction h with
  | single h => exact h.1
  | tail _ h ih => exact ih.trans h.1

lemma reach_last {n : ℕ} {C : Circuit} {u v : ℕ} (h : Relation.TransGen (EdgeStep n C) u v) :
    ∃ w, (u=w ∨ Relation.TransGen (EdgeStep n C) u w) ∧ EdgeStep n C w v := by
  cases h with
  | single h => exact ⟨u,Or.inl rfl,h⟩
  | tail hg hw => exact ⟨_,Or.inr hg,hw⟩

lemma last_input {n : ℕ} {C : Circuit} {u k : ℕ} {g : Gate} (hg : C.gates[k]? = some g)
    (h : Relation.TransGen (EdgeStep n C) u (n+k)) :
    ∃ w ∈ g.inputs, u=w ∨ Relation.TransGen (EdgeStep n C) u w := by
  obtain ⟨w,hw,_,i,g',hi,hg',hin⟩ := reach_last h
  have hik : i=k := by omega
  subst i
  have hgg : g'=g := Option.some.inj (hg'.symm.trans hg)
  subst g'
  exact ⟨w,hin,hw⟩

lemma from_or_bound {n : ℕ} {C : Circuit} {j k guard : ℕ} {g : Gate} {inputs : List ℕ}
    (hj : C.gates[j]? = some g) (hja : g.op = GateOp.and)
    (hk : C.gates[k]? = some ⟨GateOp.or,inputs⟩) (hbound : ∀ x ∈ inputs, x ≤ n+guard)
    (h : n+j=n+k ∨ Relation.TransGen (EdgeStep n C) (n+j) (n+k)) : j ≤ guard := by
  rcases h with h | h
  · have he : j=k := by omega
    subst j
    have hgg : g=⟨GateOp.or,inputs⟩ := Option.some.inj (hj.symm.trans hk)
    rw [hgg] at hja
    cases hja
  · obtain ⟨w,hw,he | hpath⟩ := last_input hk h
    · have hw' := hbound w hw
      omega
    · have hw' := hbound w hw
      have := reach_lt hpath
      omega

def OrPrefix (C : Circuit) (upTo : ℕ) : Prop :=
  ∀ k < upTo, ∀ g, C.gates[k]? = some g → g.op = GateOp.or

lemma prefix_and_ge {C : Circuit} {t j : ℕ} {g : Gate} (hor : OrPrefix C t)
    (hj : C.gates[j]?=some g) (hop : g.op=GateOp.and) : t ≤ j := by
  by_contra! h
  have h' := hor j h g hj
  rw [hop] at h'
  cases h'

lemma new_product_value {n : ℕ} (C : Circuit) {guard l r k : ℕ} (p q b : Fin n)
    (hl : C.gates[l]?=some ⟨GateOp.or,[p.val,n+guard]⟩)
    (hr : C.gates[r]?=some ⟨GateOp.or,[q.val,b.val]⟩)
    (hk : C.gates[k]?=some ⟨GateOp.and,[n+l,n+r]⟩) (hgl : guard<l) (hlk : l<k) (hrk : r<k)
    (x : Fin n → Bool) :
    W C x (n+k) = ((x p || W C x (n+guard)) && (x q || x b)) := by
  rw [W_binary C x hk (by omega) (by omega),
    W_binary C x hl (by have := p.isLt; omega) (by omega),
    W_binary C x hr (by have := q.isLt; omega) (by have := b.isLt; omega)]
  simp [GateOp.eval, W_raw]

lemma new_product_ancestor {n : ℕ} (C : Circuit) {guard l r k j : ℕ} {g : Gate}
    (p q b : Fin n) (hor : OrPrefix C guard)
    (hl : C.gates[l]?=some ⟨GateOp.or,[p.val,n+guard]⟩)
    (hr : C.gates[r]?=some ⟨GateOp.or,[q.val,b.val]⟩)
    (hk : C.gates[k]?=some ⟨GateOp.and,[n+l,n+r]⟩)
    (hj : C.gates[j]?=some g) (hja : g.op=GateOp.and)
    (hpath : Relation.TransGen (EdgeStep n C) (n+j) (n+k)) : j=guard := by
  have hlo := prefix_and_ge hor hj hja
  obtain ⟨w,hw,hw'⟩ := last_input hk hpath
  change w∈[n+l,n+r] at hw
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl
  · have hhi : j ≤ guard := from_or_bound hj hja hl (by
      intro v hv
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
      rcases hv with rfl | rfl
      · have := p.isLt
        omega
      · rfl) hw'
    omega
  · have hhi : j ≤ guard := from_or_bound hj hja hr (by
      intro v hv
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
      rcases hv with rfl | rfl
      · have := q.isLt
        omega
      · have := b.isLt
        omega) hw'
    omega

lemma guard_path {n : ℕ} (C : Circuit) {guard l r k : ℕ} (p : Fin n)
    (hl : C.gates[l]?=some ⟨GateOp.or,[p.val,n+guard]⟩)
    (hk : C.gates[k]?=some ⟨GateOp.and,[n+l,n+r]⟩) (hgl : guard<l) (hlk : l<k) :
    Relation.TransGen (EdgeStep n C) (n+guard) (n+k) :=
  (Relation.TransGen.single (r := EdgeStep n C) (b:=n+l)
    ⟨by omega,l,_,rfl,hl,by simp⟩).tail ⟨by omega,k,_,rfl,hk,by simp⟩

lemma moved_guard_value {n : ℕ} (C : Circuit) (a : Fin n) {U t : ℕ}
    (ht : C.gates[t]?=some (Gate.mk GateOp.and [a.val,U])) (hU : U < n+t) (x : Fin n → Bool) :
    W C x (n+t) = (x a && W C x U) := by
  rw [W_binary C x ht (by have := a.isLt; omega) hU]
  simp [GateOp.eval,W_raw]

lemma moved_guard_ownership {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) (a : Fin n)
    {U t : ℕ} (ht : C.gates[t]?=some (Gate.mk GateOp.and [a.val,U])) (hU : U < n+t)
    (hor : OrPrefix C t) (hw : ∃ w, G.Adj a w ∧ W C (pairInput a w) U=true) :
    (∃ u v, G.Adj u v ∧ Owns C t u v) ∧
      ∀ u v, G.Adj u v → Owns C t u v → u=a ∨ v=a := by
  obtain ⟨w,haw,hw⟩ := hw
  constructor
  · refine ⟨a,w,haw,?_,?_⟩
    · rw [moved_guard_value C a ht hU,hw]
      simp [pairInput]
    · intro j g hj hg hpath
      have hjt := prefix_and_ge hor hj hg
      have := reach_lt hpath
      omega
  · intro u v _ ho
    have hv := ho.1
    rw [moved_guard_value C a ht hU] at hv
    simp only [Bool.and_eq_true, pairInput, decide_eq_true_eq] at hv
    exact hv.1.imp Eq.symm Eq.symm

lemma moved_product_ownership {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) (a b p q : Fin n)
    {U t l r k : ℕ} (ht : C.gates[t]?=some (Gate.mk GateOp.and [a.val,U])) (hU : U < n+t)
    (hor : OrPrefix C t) (hl : C.gates[l]?=some ⟨GateOp.or,[p.val,n+t]⟩)
    (hr : C.gates[r]?=some ⟨GateOp.or,[q.val,b.val]⟩)
    (hk : C.gates[k]?=some ⟨GateOp.and,[n+l,n+r]⟩) (htl : t<l) (hlk : l<k)
    (hrk : r<k) (hpq : G.Adj p q) (hap : a≠p) (haq : a≠q) :
    (∃ u v, G.Adj u v ∧ Owns C k u v) ∧
      ∀ u v, G.Adj u v → Owns C k u v → u=p ∨ v=p := by
  have hguard : W C (pairInput p q) (n+t)=false := by
    simp [moved_guard_value C a ht hU,pairInput,hap,haq]
  constructor
  · refine ⟨p,q,hpq,?_,?_⟩
    · rw [new_product_value C p q b hl hr hk htl hlk hrk,hguard]
      simp [pairInput]
    · intro j g hj hg hpath
      obtain rfl := new_product_ancestor C p q b hor hl hr hk hj hg hpath
      exact hguard
  · intro u v _ ho
    have hfalse := ho.2 t _ ht rfl (guard_path C p hl hk htl hlk)
    have hv := ho.1
    rw [new_product_value C p q b hl hr hk htl hlk hrk,hfalse] at hv
    simp only [Bool.or_false, Bool.and_eq_true, pairInput, decide_eq_true_eq] at hv
    exact hv.1.imp Eq.symm Eq.symm

lemma relocate_product (U a b p q : Bool) (hp : p=true → U=true) :
    (U && ((p || a) && (q || b))) = ((p || (a && U)) && (q || b)) := by
  cases U <;> cases a <;> cases b <;> cases p <;> cases q <;> simp_all

lemma relocate_many {I : Type*} (rows : List I) (p q : I → Bool) (U a b : Bool)
    (hp : ∀ i∈rows, p i=true → U=true) :
    (U && rows.any (fun i => (p i || a) && (q i || b))) =
      rows.any (fun i => (p i || (a && U)) && (q i || b)) := by
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true,List.any_eq_true]
  constructor
  · rintro ⟨hU,i,hi,he⟩
    refine ⟨i,hi,?_⟩
    simpa [hU] using he
  · rintro ⟨i,hi,he⟩
    have h := Bool.and_eq_true_iff.mpr he
    rw [← relocate_product U a b (p i) (q i) (hp i hi)] at h
    obtain ⟨hU,hval⟩ := Bool.and_eq_true_iff.mp h
    exact ⟨hU,i,hi,Bool.and_eq_true_iff.mp hval⟩

def gateWire {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (j : ℕ) : Bool := W ⟨gs,0⟩ x j

lemma gateWire_prefix {n : ℕ} (gs hs : List Gate) (x : Fin n → Bool) (u : ℕ)
    (hu : u < n+gs.length) : gateWire (gs++hs) x u = gateWire gs x u := by
  change (((gs++hs).foldl stepWire (List.ofFn x)).getD u false) = _
  rw [List.foldl_append]
  apply foldl_getD_lt2
  simpa [foldl_length] using hu

lemma gateWire_snoc {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (op : GateOp) (s t : ℕ)
    (hs : s<n+gs.length) (ht : t<n+gs.length) :
    gateWire (gs++[⟨op,[s,t]⟩]) x (n+gs.length) = op.eval [gateWire gs x s,gateWire gs x t] := by
  let g : Gate := ⟨op,[s,t]⟩
  have h : (gs++[g])[gs.length]?=some g := by simp
  have he := W_binary (C:=⟨gs++[g],0⟩) x h hs ht
  change gateWire (gs++[g]) x (n+gs.length) = op.eval [gateWire gs x s,gateWire gs x t]
  change gateWire (gs++[g]) x (n+gs.length) =
    op.eval [gateWire (gs++[g]) x s,gateWire (gs++[g]) x t] at he
  rwa [gateWire_prefix gs [g] x s hs,gateWire_prefix gs [g] x t ht] at he

def block {n : ℕ} (gs : List Gate) (aWire : ℕ) (b p q : Fin n) : List Gate :=
  gs ++ [⟨GateOp.or,[p.val,aWire]⟩,⟨GateOp.or,[q.val,b.val]⟩,
    ⟨GateOp.and,[n+gs.length,n+gs.length+1]⟩]

lemma block_len {n : ℕ} (gs : List Gate) (aw : ℕ) (b p q : Fin n) :
    (block gs aw b p q).length=gs.length+3 := by simp [block]

lemma block_eval {n : ℕ} (gs : List Gate) (aw : ℕ) (b p q : Fin n) (hwa : aw<n+gs.length)
    (x : Fin n → Bool) :
    gateWire (block gs aw b p q) x (n+gs.length+2) =
      ((x p || gateWire gs x aw) && (x q || x b)) := by
  let C : Circuit := ⟨block gs aw b p q,0⟩
  have hl : C.gates[gs.length]? = some ⟨GateOp.or,[p.val,aw]⟩ := by
    simp [C,block]
  have hr : C.gates[gs.length+1]? = some ⟨GateOp.or,[q.val,b.val]⟩ := by
    simp [C,block]
  have hk : C.gates[gs.length+2]? = some ⟨GateOp.and,[n+gs.length,n+(gs.length+1)]⟩ := by
    simp [C,block,Nat.add_assoc]
  change W C x (n+gs.length+2) = _
  rw [show n+gs.length+2 = n+(gs.length+2) by omega,
    W_binary C x hk (by omega) (by omega),
    W_binary C x hl (by have := p.isLt; omega) hwa,
    W_binary C x hr (by have := q.isLt; omega) (by have := b.isLt; omega)]
  have haw : W C x aw = gateWire gs x aw := gateWire_prefix gs _ x aw hwa
  simp [GateOp.eval,W_raw,haw]

def addBlock {n : ℕ} (gs : List Gate) (aw : ℕ) (b p q : Fin n) : List Gate :=
  block gs aw b p q ++ [⟨GateOp.or,[n+gs.length-1,n+gs.length+2]⟩]

lemma addBlock_len {n : ℕ} (gs : List Gate) (aw : ℕ) (b p q : Fin n) :
    (addBlock gs aw b p q).length=gs.length+4 := by simp [addBlock,block_len]

lemma addBlock_eval {n : ℕ} (gs : List Gate) (aw : ℕ) (b p q : Fin n) (ha : aw<n+gs.length)
    (x : Fin n → Bool) :
    gateWire (addBlock gs aw b p q) x (n+(addBlock gs aw b p q).length-1) =
      (gateWire gs x (n+gs.length-1) || ((x p || gateWire gs x aw) && (x q || x b))) := by
  have hpre : n+gs.length-1 < n+gs.length := by have := b.isLt; omega
  have hlen := block_len gs aw b p q
  rw [show n+(addBlock gs aw b p q).length-1=n+(block gs aw b p q).length by
    rw [addBlock_len,hlen]; omega]
  unfold addBlock
  rw [gateWire_snoc (block gs aw b p q) x GateOp.or _ _ (by omega) (by omega),
    block_eval gs aw b p q ha x]
  have ho : gateWire (block gs aw b p q) x (n+gs.length-1) = gateWire gs x (n+gs.length-1) :=
    gateWire_prefix gs _ x _ hpre
  simp [GateOp.eval,ho]

def foldBlocks {n : ℕ} (aw : ℕ) (b : Fin n) : List (Fin n × Fin n) → List Gate → List Gate
  | [], gs => gs
  | (p,q)::ps,gs => foldBlocks aw b ps (addBlock gs aw b p q)

lemma foldBlocks_len {n : ℕ} (aw : ℕ) (b : Fin n) (ps : List (Fin n × Fin n)) (gs : List Gate) :
    (foldBlocks aw b ps gs).length=gs.length+4*ps.length := by
  induction ps generalizing gs with
  | nil => simp [foldBlocks]
  | cons pq ps ih =>
    rcases pq with ⟨p,q⟩
    rw [foldBlocks,ih,addBlock_len,List.length_cons]
    omega

def branchValue {n : ℕ} (x : Fin n → Bool) (A : Bool) (b : Fin n) (pq : Fin n × Fin n) : Bool :=
  (x pq.1 || A) && (x pq.2 || x b)

lemma foldBlocks_eval {n : ℕ} (aw : ℕ) (b : Fin n) (ps : List (Fin n × Fin n))
    (gs : List Gate) (ha : aw<n+gs.length) (x : Fin n → Bool) :
    gateWire (foldBlocks aw b ps gs) x (n+(foldBlocks aw b ps gs).length-1) =
      (gateWire gs x (n+gs.length-1) || ps.any (branchValue x (gateWire gs x aw) b)) := by
  induction ps generalizing gs with
  | nil => simp [foldBlocks]
  | cons pq ps ih =>
    rcases pq with ⟨p,q⟩
    have hlen := addBlock_len gs aw b p q
    have ext1 : gateWire (addBlock gs aw b p q) x aw = gateWire gs x aw := by
      rw [addBlock,gateWire_prefix (block gs aw b p q) _ x aw (by rw [block_len]; omega)]
      exact gateWire_prefix gs _ x aw ha
    rw [foldBlocks,ih _ (by omega),addBlock_eval gs aw b p q ha x,ext1]
    simp [branchValue,Bool.or_assoc]

def family {n : ℕ} (gs : List Gate) (aw : ℕ) (b p q : Fin n) (ps : List (Fin n × Fin n)) :
    List Gate := foldBlocks aw b ps (block gs aw b p q)

lemma family_len {n : ℕ} (gs : List Gate) (aw : ℕ) (b p q : Fin n) (ps : List (Fin n × Fin n)) :
    (family gs aw b p q ps).length=gs.length+3+4*ps.length := by
  rw [family,foldBlocks_len,block_len]

lemma family_eval {n : ℕ} (gs : List Gate) (aw : ℕ) (b p q : Fin n) (ps : List (Fin n × Fin n))
    (ha : aw<n+gs.length) (x : Fin n → Bool) :
    gateWire (family gs aw b p q ps) x (n+(family gs aw b p q ps).length-1) =
      ((p,q)::ps).any (branchValue x (gateWire gs x aw) b) := by
  rw [family,foldBlocks_eval aw b ps _ (by rw [block_len]; omega) x]
  have ha' : gateWire (block gs aw b p q) x aw = gateWire gs x aw := gateWire_prefix gs _ x aw ha
  have hlast : n+(block gs aw b p q).length-1=n+gs.length+2 := by rw [block_len]; omega
  rw [ha',hlast,block_eval gs aw b p q ha x]
  rfl

lemma family_prefix {n : ℕ} (gs : List Gate) (aw : ℕ) (b p q : Fin n) (ps : List (Fin n × Fin n)) :
    ∃ rest, family gs aw b p q ps = gs++rest := by
  have hfold (ss : List (Fin n × Fin n)) (hs : List Gate) :
      ∃ tail, foldBlocks aw b ss hs = hs++tail := by
    induction ss generalizing hs with
    | nil => exact ⟨[],by simp [foldBlocks]⟩
    | cons pq' ss' ih =>
      rcases pq' with ⟨p',q'⟩
      obtain ⟨tail,he⟩ := ih (addBlock hs aw b p' q')
      rw [foldBlocks,he]
      unfold addBlock block
      simp only [List.append_assoc]
      exact ⟨_,rfl⟩
  obtain ⟨tail,he⟩ := hfold ps (block gs aw b p q)
  rw [family,he]
  unfold block
  rw [List.append_assoc]
  exact ⟨_,rfl⟩

def oldGates {n : ℕ} (gs : List Gate) (U : ℕ) (a b p q : Fin n) (ps : List (Fin n × Fin n)) :
    List Gate :=
  let body := family gs a.val b p q ps
  body++[Gate.mk GateOp.and [U,n+body.length-1]]

def newGates {n : ℕ} (gs : List Gate) (U : ℕ) (a b p q : Fin n) (ps : List (Fin n × Fin n)) :
    List Gate :=
  family (gs++[Gate.mk GateOp.and [a.val,U]]) (n+gs.length) b p q ps

def lastCircuit (n : ℕ) (gs : List Gate) : Circuit := ⟨gs,n+gs.length-1⟩

lemma relocation_size {n : ℕ} (gs : List Gate) (U : ℕ) (a b p q : Fin n)
    (ps : List (Fin n × Fin n)) :
    (lastCircuit n (newGates gs U a b p q ps)).size =
      (lastCircuit n (oldGates gs U a b p q ps)).size := by
  simp [Circuit.size,lastCircuit,oldGates,newGates,family_len]
  omega

lemma relocation_eval {n : ℕ} (gs : List Gate) (U : ℕ) (a b p q : Fin n)
    (ps : List (Fin n × Fin n)) (hU : U<n+gs.length)
    (hfeed : ∀ pq ∈ (p,q)::ps, ∀ x : Fin n → Bool, x pq.1=true → gateWire gs x U=true)
    (x : Fin n → Bool) :
    (lastCircuit n (oldGates gs U a b p q ps)).eval (List.ofFn x) =
      (lastCircuit n (newGates gs U a b p q ps)).eval (List.ofFn x) := by
  let body := family gs a.val b p q ps
  have hbody : body.length=gs.length+3+4*ps.length := family_len gs a.val b p q ps
  have ha : a.val < n+gs.length := by have := a.isLt; omega
  have hnew : n+gs.length < n+(gs++[Gate.mk GateOp.and [a.val,U]]).length := by simp
  change gateWire (body++[Gate.mk GateOp.and [U,n+body.length-1]]) x
    (n+(body++[Gate.mk GateOp.and [U,n+body.length-1]]).length-1) =
    gateWire (newGates gs U a b p q ps) x (n+(newGates gs U a b p q ps).length-1)
  rw [show n+(body++[Gate.mk GateOp.and [U,n+body.length-1]]).length-1=n+body.length by simp,
    gateWire_snoc _ _ _ _ _ (by omega) (by omega)]
  have hu' : gateWire body x U=gateWire gs x U := by
    obtain ⟨tail,he⟩ := family_prefix gs a.val b p q ps
    dsimp [body]
    rw [he,gateWire_prefix gs tail x U hU]
  rw [hu',show gateWire body x (n+body.length-1) = _ from family_eval gs _ b p q ps ha x,
    newGates,family_eval _ (n+gs.length) b p q ps hnew x,gateWire_snoc gs x GateOp.and _ _ ha hU]
  have har : gateWire gs x a.val=x a := W_raw ⟨gs,0⟩ x a
  simp only [GateOp.eval,List.all_cons,List.all_nil,id_eq,Bool.and_true,har]
  exact relocate_many _ (fun z => x z.1) (fun z => x z.2) (gateWire gs x U) (x a) (x b)
    (fun z hz => hfeed z hz x)

def RowShape {n : ℕ} (gs : List Gate) (t : ℕ) (b p q : Fin n) (k : ℕ) : Prop :=
  ∃ l r, gs[l]?=some ⟨GateOp.or,[p.val,n+t]⟩ ∧ gs[r]?=some ⟨GateOp.or,[q.val,b.val]⟩ ∧
    gs[k]?=some ⟨GateOp.and,[n+l,n+r]⟩ ∧ t<l ∧ l<k ∧ r<k

def AllAnd {n : ℕ} (gs : List Gate) (t : ℕ) (b : Fin n) (ok : Fin n → Fin n → Prop) : Prop :=
  ∀ k g, gs[k]?=some g → g.op=GateOp.and → k=t ∨ ∃ p q, ok p q ∧ RowShape gs t b p q k

lemma lookup_append {gs : List Gate} {k : ℕ} {g : Gate} (hg : gs[k]?=some g) (rest : List Gate) :
    (gs++rest)[k]?=some g := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hg).choose,hg]

lemma rowShape_append {n : ℕ} {gs : List Gate} {t k : ℕ} {b p q : Fin n}
    (h : RowShape gs t b p q k) (rest : List Gate) : RowShape (gs++rest) t b p q k := by
  obtain ⟨l,r,hl,hr,hk,h1,h2,h3⟩ := h
  exact ⟨l,r,lookup_append hl rest,lookup_append hr rest,lookup_append hk rest,h1,h2,h3⟩

lemma allAnd_old {n : ℕ} {gs : List Gate} {t : ℕ} {b : Fin n} {ok : Fin n → Fin n → Prop}
    (ha : AllAnd gs t b ok) (rest : List Gate) {k : ℕ} (hlt : k < gs.length) {g : Gate}
    (hg : (gs++rest)[k]?=some g) (hop : g.op=GateOp.and) :
    k=t ∨ ∃ p q, ok p q ∧ RowShape (gs++rest) t b p q k := by
  rw [List.getElem?_append_left hlt] at hg
  rcases ha k g hg hop with h | ⟨p,q,hpq,hs⟩
  · exact Or.inl h
  · exact Or.inr ⟨p,q,hpq,rowShape_append hs rest⟩

lemma block_shape {n : ℕ} (gs : List Gate) (t : ℕ) (b p q : Fin n) (ht : t<gs.length) :
    RowShape (block gs (n+t) b p q) t b p q (gs.length+2) := by
  refine ⟨gs.length,gs.length+1,?_,?_,?_,ht,by omega,by omega⟩
  · simp [block]
  · simp [block]
  · simp [block,Nat.add_assoc]

lemma allAnd_block {n : ℕ} (gs : List Gate) (t : ℕ) (b p q : Fin n)
    {ok : Fin n → Fin n → Prop} (ha : AllAnd gs t b ok) (ht : t<gs.length) (hpq : ok p q) :
    AllAnd (block gs (n+t) b p q) t b ok := by
  intro k g hg hop
  by_cases hlt : k<gs.length
  · exact allAnd_old ha _ hlt hg hop
  obtain ⟨l,r,hl,hr,hk,_,_,_⟩ := block_shape gs t b p q ht
  have hb := (List.getElem?_eq_some_iff.mp hg).choose
  rw [block_len] at hb
  have hcases : k=gs.length ∨ k=gs.length+1 ∨ k=gs.length+2 := by omega
  rcases hcases with he | he | he
  · subst k
    have hgg : g=⟨GateOp.or,[p.val,n+t]⟩ := by simpa [block] using hg.symm
    rw [hgg] at hop
    cases hop
  · subst k
    have hgg : g=⟨GateOp.or,[q.val,b.val]⟩ := by simpa [block] using hg.symm
    rw [hgg] at hop
    cases hop
  · subst k
    exact Or.inr ⟨p,q,hpq,block_shape gs t b p q ht⟩

lemma allAnd_or {n : ℕ} (gs : List Gate) (t : ℕ) (b : Fin n) {ok : Fin n → Fin n → Prop}
    (ha : AllAnd gs t b ok) (s u : ℕ) : AllAnd (gs++[⟨GateOp.or,[s,u]⟩]) t b ok := by
  intro k g hg hop
  by_cases hlt : k<gs.length
  · exact allAnd_old ha _ hlt hg hop
  have hb := (List.getElem?_eq_some_iff.mp hg).choose
  simp only [List.length_append,List.length_singleton] at hb
  have he : k=gs.length := by omega
  subst k
  have hgg : g=⟨GateOp.or,[s,u]⟩ := by simpa using hg.symm
  rw [hgg] at hop
  cases hop

lemma allAnd_fold {n : ℕ} (t : ℕ) (b : Fin n) (ps : List (Fin n × Fin n))
    {ok : Fin n → Fin n → Prop} (hps : ∀ z ∈ ps, ok z.1 z.2)
    (gs : List Gate) (ha : AllAnd gs t b ok) (ht : t<gs.length) :
    AllAnd (foldBlocks (n+t) b ps gs) t b ok := by
  induction ps generalizing gs with
  | nil => exact ha
  | cons pq ps ih =>
    rcases pq with ⟨p,q⟩
    rw [foldBlocks]
    apply ih (fun z hz => hps z (List.mem_cons_of_mem _ hz))
    · exact allAnd_or _ t b (allAnd_block gs t b p q ha ht (hps (p,q) (by simp))) _ _
    · rw [addBlock_len]
      omega

lemma new_allAnd {n : ℕ} (gs : List Gate) (U : ℕ) (a b p q : Fin n)
    (ps : List (Fin n × Fin n)) {ok : Fin n → Fin n → Prop}
    (hps : ∀ z ∈ (p,q)::ps, ok z.1 z.2) (hor : ∀ g ∈ gs, g.op=GateOp.or) :
    AllAnd (newGates gs U a b p q ps) gs.length b ok := by
  let pre : List Gate := gs++[Gate.mk GateOp.and [a.val,U]]
  have hpre : AllAnd pre gs.length b ok := by
    intro j g hj hg
    have hb := (List.getElem?_eq_some_iff.mp hj).choose
    by_cases hlt : j<gs.length
    · have hbefore : gs[j]?=some g := by
        simpa only [pre,List.getElem?_append_left hlt] using hj
      have h := hor g (List.mem_of_getElem? hbefore)
      rw [hg] at h
      cases h
    · left
      simp [pre] at hb
      omega
  have ht : gs.length<pre.length := by simp [pre]
  change AllAnd (foldBlocks (n+gs.length) b ps (block pre (n+gs.length) b p q)) gs.length b ok
  apply allAnd_fold gs.length b ps (fun z hz => hps z (List.mem_cons_of_mem _ hz))
  · exact allAnd_block pre gs.length b p q hpre ht (hps (p,q) (by simp))
  · rw [block_len]
    omega

lemma new_full_profile {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate) (U : ℕ)
    (a b p q : Fin n) (ps : List (Fin n × Fin n))
    (hU : U<n+gs.length) (hor : ∀ g∈gs, g.op=GateOp.or)
    (hps : ∀ z ∈ (p,q)::ps, G.Adj z.1 z.2 ∧ a≠z.1 ∧ a≠z.2)
    (hw : ∃ w, G.Adj a w ∧ gateWire gs (pairInput a w) U=true) :
    let C := lastCircuit n (newGates gs U a b p q ps)
    ∀ k g, C.gates[k]?=some g → g.op=GateOp.and → ∃ c : Fin n,
      (∃ u v, G.Adj u v ∧ Owns C k u v) ∧
      ∀ u v, G.Adj u v → Owns C k u v → u=c ∨ v=c := by
  let C := lastCircuit n (newGates gs U a b p q ps)
  change ∀ (k : ℕ) (g : Gate), C.gates[k]?=some g → g.op=GateOp.and → _
  let guard : Gate := Gate.mk GateOp.and [a.val,U]
  have hpre : ∃ rest, C.gates=(gs++[guard])++rest :=
    family_prefix (gs++[guard]) (n+gs.length) b p q ps
  obtain ⟨rest,he⟩ := hpre
  have htg : C.gates[gs.length]?=some guard := by
    rw [he]
    exact lookup_append (by simp) rest
  have hold : OrPrefix C gs.length := by
    intro j hj g hg
    rw [he,List.append_assoc,List.getElem?_append_left hj] at hg
    exact hor g (List.mem_of_getElem? hg)
  have hUU (x : Fin n → Bool) : W C x U=gateWire gs x U := by
    change gateWire C.gates x U=_
    rw [he,List.append_assoc,gateWire_prefix gs _ x U hU]
  intro k g hg hop
  rcases new_allAnd gs U a b p q ps (ok:=fun i j => G.Adj i j ∧ a≠i ∧ a≠j) hps hor k g hg hop with ht | ⟨i,j,hij,hs⟩
  · subst k
    refine ⟨a,moved_guard_ownership G C a htg hU hold ?_⟩
    obtain ⟨v,hav,hv⟩ := hw
    exact ⟨v,hav,(hUU _).trans hv⟩
  · obtain ⟨l,r,hl,hr,hk,htl,hlk,hrk⟩ := hs
    exact ⟨i,moved_product_ownership G C a b i j htg hU hold hl hr hk htl hlk hrk
      hij.1 hij.2.1 hij.2.2⟩

def Legal (gs : List Gate) : Prop :=
  ∀ g∈gs, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2

lemma legal_append {s t : List Gate} (hs : Legal s) (ht : Legal t) : Legal (s++t) := by
  intro g hg
  rcases List.mem_append.mp hg with h | h
  · exact hs g h
  · exact ht g h

lemma legal_one (op : GateOp) (h : op=GateOp.and ∨ op=GateOp.or) (w v : ℕ) :
    Legal [⟨op,[w,v]⟩] := by
  intro g hg
  obtain rfl : g=⟨op,[w,v]⟩ := by simpa using hg
  exact ⟨h,by simp⟩

lemma legal_block {n : ℕ} (gs : List Gate) (aw : ℕ) (b p q : Fin n) (hs : Legal gs) :
    Legal (block gs aw b p q) := by
  apply legal_append hs
  intro g hg
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl <;> simp

lemma legal_family {n : ℕ} (gs : List Gate) (aw : ℕ) (b p q : Fin n) (ps : List (Fin n × Fin n))
    (hs : Legal gs) : Legal (family gs aw b p q ps) := by
  have hfold (l : List (Fin n × Fin n)) (g : List Gate) (hg : Legal g) :
      Legal (foldBlocks aw b l g) := by
    induction l generalizing g with
    | nil => exact hg
    | cons pq l ih =>
      rcases pq with ⟨p',q'⟩
      exact ih _ (legal_append (legal_block g aw b p' q' hg) (legal_one _ (Or.inr rfl) _ _))
  exact hfold _ _ (legal_block gs aw b p q hs)

lemma relocation_legal {n : ℕ} (gs : List Gate) (U : ℕ) (a b p q : Fin n)
    (ps : List (Fin n × Fin n)) (hs : Legal gs) :
    Legal (oldGates gs U a b p q ps) ∧ Legal (newGates gs U a b p q ps) :=
  ⟨legal_append (legal_family gs a.val b p q ps hs) (legal_one _ (Or.inl rfl) _ _),
    legal_family _ _ b p q ps (legal_append hs (legal_one _ (Or.inl rfl) _ _))⟩

lemma left_port_equal_iff (p a U : Bool) :
    (p || a) = (p || (a && U)) ↔ (a=true → p=true ∨ U=true) := by
  cases p <;> cases a <;> cases U <;> decide

lemma left_port_all_edges {n : ℕ} (G : SimpleGraph (Fin n)) (U : (Fin n → Bool) → Bool)
    (a p : Fin n) (hU : ∀ u v, G.Adj u v → (u=a ∨ v=a) → U (pairInput u v)=true)
    (u v : Fin n) (he : G.Adj u v) :
    (pairInput u v p || pairInput u v a) = (pairInput u v p || (pairInput u v a && U (pairInput u v))) := by
  apply (left_port_equal_iff _ _ _).2
  intro h
  simp only [pairInput,decide_eq_true_eq] at h
  exact Or.inr (hU u v he (h.imp Eq.symm Eq.symm))

end PEqualNP.Outside.L_meta_1031.FreshTheta
