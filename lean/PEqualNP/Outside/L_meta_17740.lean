import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17740

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Relation

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs rest : List Gate) (w : List Bool) :
    wiresFrom (gs ++ rest) w = wiresFrom rest (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    change wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = _
    rw [ht]; simp

theorem wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem prefix_val (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def val {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (wiresFrom C.gates (List.ofFn x)).getD i false

theorem val_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
    val C x i.val = x i := by
  rw [val, prefix_val _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
  simp

theorem val_beyond {n : ℕ} (C : Circuit) (x : Fin n → Bool) {i : ℕ}
    (hi : n + C.gates.length ≤ i) : val C x i = false := by
  rw [val, List.getD_eq_default _ _ (by simpa [wiresFrom_length] using hi)]

def operand {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j i : ℕ) : Bool :=
  if i < j then val C x i else false

theorem val_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) {p : ℕ} {g : Gate}
    (hp : C.gates[p]? = some g) :
    val C x (n+p) = g.op.eval (g.inputs.map (operand C x (n+p))) := by
  obtain ⟨hb, heq⟩ := List.getElem?_eq_some_iff.1 hp
  have hsplit : C.gates = (C.gates.take p ++ [g]) ++ C.gates.drop (p+1) := by
    conv_lhs => rw [← List.take_append_drop (p+1) C.gates]
    rw [List.take_succ_eq_append_getElem hb, heq]
  let w := wiresFrom (C.gates.take p) (List.ofFn x)
  have hw : w.length = n+p := by
    simp [w, wiresFrom_length, List.length_take, Nat.min_eq_left hb.le]
  have hread (i : ℕ) : w.getD i false = operand C x (n+p) i := by
    by_cases hi : i < n+p
    · have hv : val C x i = w.getD i false := by
        unfold val
        conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
        exact prefix_val _ w i (hw.symm ▸ hi)
      simp only [operand, ite_eq_left hi, hv]
    · rw [operand, ite_eq_right hi, List.getD_eq_default _ _ (by omega)]
  have he : (g.inputs.map fun i => w.getD i false) = g.inputs.map (operand C x (n+p)) :=
    List.map_congr_left fun i _ => hread i
  unfold val
  conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
  change (wiresFrom (C.gates.drop (p+1))
    (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD (n+p) false = _
  rw [prefix_val _ _ _ (by simp [hw]), ← hw, he]
  simp [hw]

def Next (n : ℕ) (C : Circuit) (a b : ℕ) : Prop :=
  a < b ∧ ∃ p g, C.gates[p]? = some g ∧ b = n+p ∧ a ∈ g.inputs

def Live (n : ℕ) (C : Circuit) (i : ℕ) : Prop :=
  ReflTransGen (Next n C) i C.output

def LNext (n : ℕ) (C : Circuit) (a b : ℕ) : Prop := Next n C a b ∧ Live n C b

def Trace (n : ℕ) (C : Circuit) (P : ℕ → Prop) (i j : ℕ) : Prop :=
  ReflTransGen (fun a b => P a ∧ LNext n C a b) i j

theorem next_le {n : ℕ} {C : Circuit} {a b : ℕ} (h : ReflTransGen (Next n C) a b) :
    a ≤ b := by
  induction h with
  | refl => exact le_rfl
  | tail _ h ih => exact ih.trans h.1.le

theorem trace_le {n : ℕ} {C : Circuit} {P : ℕ → Prop} {a b : ℕ}
    (h : Trace n C P a b) : a ≤ b := by
  induction h with
  | refl => exact le_rfl
  | tail _ h ih => exact ih.trans h.2.1.1.le

theorem live_before {n : ℕ} {C : Circuit} {a b : ℕ} (hn : Next n C a b) (h : Live n C b) :
    Live n C a := (ReflTransGen.single hn).trans h

theorem trace_start {n : ℕ} {C : Circuit} {P : ℕ → Prop} {a b : ℕ}
    (h : Trace n C P a b) (hb : P b) : P a := by
  rcases h.cases_head with rfl | ⟨_, hs, _⟩
  · exact hb
  · exact hs.1

theorem align {n : ℕ} {C : Circuit} {P Q : ℕ → Prop} {v b : ℕ}
    (p : Trace n C P v b)
    (unique : ∀ a j j', a < b → P a → LNext n C a j → LNext n C a j' → j = j') :
    ∀ d, Trace n C Q v d → (d < b ∧ P d) ∨ Trace n C Q b d := by
  induction p using ReflTransGen.head_induction_on with
  | refl =>
    intro d q
    exact Or.inr q
  | head hp pt ih =>
    intro d q
    have hlt := hp.2.1.1.trans_le (trace_le pt)
    rcases q.cases_head with rfl | ⟨j, hq, qt⟩
    · exact Or.inl ⟨hlt, hp.1⟩
    · have e := unique _ _ _ hlt hp.1 hp.2 hq.2
      subst j
      exact ih _ qt

theorem difference {n : ℕ} (C : Circuit) (x y : Fin n → Bool) :
    ∀ j, Live n C j → val C x j ≠ val C y j →
      ∃ i : Fin n, x i ≠ y i ∧ Trace n C (fun a => val C x a ≠ val C y a) i.val j := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj hd
    by_cases hin : j < n
    · let i : Fin n := ⟨j,hin⟩
      exact ⟨i, by simpa only [← val_input C x i, ← val_input C y i] using hd, .refl⟩
    have hb : j < n+C.gates.length := by
      by_contra! he
      exact hd ((val_beyond C x he).trans (val_beyond C y he).symm)
    obtain ⟨p, hp, rfl⟩ : ∃ p, p < C.gates.length ∧ j = n+p := ⟨j-n, by omega, by omega⟩
    let g := C.gates[p]
    have hg : C.gates[p]? = some g := List.getElem?_eq_some_iff.2 ⟨hp, rfl⟩
    have hdiff : ∃ i ∈ g.inputs, i < n+p ∧ val C x i ≠ val C y i := by
      by_contra! hn
      apply hd
      rw [val_gate C x hg, val_gate C y hg]
      apply congrArg _
      apply List.map_congr_left
      intro i hi
      by_cases hj : i < n+p
      · simp [operand, hj, hn i hi hj]
      · simp [operand, hj]
    obtain ⟨a, ha, hlt, ha'⟩ := hdiff
    have hs : Next n C a (n+p) := ⟨hlt,p,g,hg,rfl,ha⟩
    obtain ⟨i, hi, hpath⟩ := ih a hlt (live_before hs hj) ha'
    exact ⟨i, hi, hpath.tail ⟨ha',hs,hj⟩⟩

end PEqualNP.Outside.L_meta_17740


namespace PEqualNP.Outside.L_meta_17740

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Relation

variable {n : ℕ} {C : Circuit}

theorem acts_mono (hC : Monotone2 C) {x y : Fin n → Bool}
    (hxy : ∀ i, x i = true → y i = true) :
    ∀ j, val C x j = true → val C y j = true := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj
    by_cases hin : j < n
    · let i : Fin n := ⟨j, hin⟩
      simpa only [← val_input C x i, ← val_input C y i] using hxy i (by
        simpa only [← val_input C x i] using hj)
    by_cases hgt : n + C.gates.length ≤ j
    · rw [val_beyond C x hgt] at hj
      contradiction
    obtain ⟨p, hp, rfl⟩ : ∃ p, p < C.gates.length ∧ j = n+p := ⟨j-n, by omega, by omega⟩
    let g := C.gates[p]
    have hg : C.gates[p]? = some g := List.getElem?_eq_some_iff.2 ⟨hp, rfl⟩
    have hgate := (hC g (List.mem_of_getElem? hg)).1
    have hm (a : ℕ) : operand C x (n+p) a = true → operand C y (n+p) a = true := by
      by_cases ha : a < n+p
      · simp only [operand, ite_eq_left ha]
        exact ih a ha
      · simp [operand, ha]
    rw [val_gate C x hg] at hj
    rw [val_gate C y hg]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hgate
    rcases hgate with h | h
    · simp only [h, GateOp.eval, List.all_map, Function.comp_apply, id, List.all_eq_true] at hj ⊢
      exact fun a ha => hm a (hj a ha)
    · simp only [h, GateOp.eval, List.any_map, Function.comp_apply, id, List.any_eq_true] at hj ⊢
      obtain ⟨a, ha, he⟩ := hj
      exact ⟨a, ha, hm a he⟩

def point (s : Finset (Fin n)) (i : Fin n) : Bool := decide (i ∈ s)

theorem point_mono {s t : Finset (Fin n)} (h : s ⊆ t) :
    ∀ i, point s i = true → point t i = true := by
  intro i hi
  simpa only [point, decide_eq_true_eq] using h (by simpa only [point, decide_eq_true_eq] using hi)

theorem point_insert {s : Finset (Fin n)} {v u : Fin n} (h : u ≠ v) :
    point (insert v s) u = point s u := by simp [point, h]

def Carries (C : Circuit) (v : Fin n) (a : ℕ) : Prop :=
  val C (point {v}) a ≠ val C (point (∅ : Finset (Fin n))) a

theorem carries_iff (hC : Monotone2 C) {v : Fin n} {a : ℕ} :
    Carries C v a ↔
      val C (point {v}) a = true ∧ val C (point (∅ : Finset (Fin n))) a = false := by
  have hm := acts_mono hC (point_mono (Finset.empty_subset {v})) a
  unfold Carries
  cases ha : val C (point {v}) a <;>
    cases hb : val C (point (∅ : Finset (Fin n))) a <;> simp_all

theorem singleton_path {v : Fin n} {a : ℕ} (ha : Live n C a) (hd : Carries C v a) :
    Trace n C (Carries C v) v.val a := by
  obtain ⟨i, hi, hpath⟩ := difference C (point {v}) (point ∅) a ha hd
  have e : i = v := by
    by_contra h
    exact hi (by simp [point, h])
  exact e ▸ hpath

theorem influence {v : Fin n} {P : ℕ → Prop} {b j : ℕ} {x y : Fin n → Bool}
    (path : Trace n C P v.val b)
    (unique : ∀ a k k', a < b → P a → LNext n C a k → LNext n C a k' → k = k')
    (agrees : ∀ i, i ≠ v → x i = y i) (hj : Live n C j) (hd : val C x j ≠ val C y j) :
    (j < b ∧ P j) ∨ (b ≤ j ∧ val C x b ≠ val C y b) := by
  obtain ⟨i, hi, trace⟩ := difference C x y j hj hd
  have e : i = v := by
    by_contra h
    exact hi (agrees i h)
  subst i
  rcases align path unique j trace with ha | hb
  · exact Or.inl ha
  · exact Or.inr ⟨trace_le hb, trace_start hb hd⟩

noncomputable def readers (n : ℕ) (C : Circuit) (a : ℕ) : Finset ℕ :=
  open Classical in (Finset.range (n+C.gates.length)).filter (fun b => LNext n C a b)

theorem next_in_range {a b : ℕ} (h : Next n C a b) : b < n+C.gates.length := by
  obtain ⟨_,p,g,hg,rfl,_⟩ := h
  exact Nat.add_lt_add_left (List.getElem?_eq_some_iff.1 hg).1 n

theorem mem_readers {a b : ℕ} : b ∈ readers n C a ↔ LNext n C a b := by
  classical
  unfold readers
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨And.right, fun h => ⟨next_in_range h.1, h⟩⟩

def Branch (n : ℕ) (C : Circuit) (a : ℕ) : Prop := 2 ≤ (readers n C a).card

theorem nonbranch_unique {a j j' : ℕ} (h : ¬ Branch n C a)
    (hj : LNext n C a j) (hj' : LNext n C a j') : j = j' := by
  apply Finset.card_le_one_iff.1 (show (readers n C a).card ≤ 1 from by
    unfold Branch at h; omega) (mem_readers.2 hj) (mem_readers.2 hj')

def Eligible (C : Circuit) (v : Fin n) : Prop := ∃ b, Live n C b ∧ Carries C v b ∧ Branch n C b

noncomputable def firstBranch (C : Circuit) (v : Fin n) (h : Eligible C v) : ℕ := by
  classical exact Nat.find h

theorem firstBranch_spec (v : Fin n) (h : Eligible C v) :
    Live n C (firstBranch C v h) ∧ Carries C v (firstBranch C v h) ∧ Branch n C (firstBranch C v h) := by
  classical exact Nat.find_spec h

theorem firstBranch_unique (v : Fin n) (h : Eligible C v) :
    ∀ a j j', a < firstBranch C v h → Carries C v a → LNext n C a j → LNext n C a j' → j = j' := by
  classical
  intro a j j' hl hc hj hj'
  apply nonbranch_unique _ hj hj'
  intro hb
  exact (Nat.not_le_of_gt hl) (Nat.find_min' h ⟨live_before hj.1 hj.2,hc,hb⟩)

theorem no_eligible_unique {v : Fin n} (h : ¬ Eligible C v) :
    ∀ a j j', Carries C v a → LNext n C a j → LNext n C a j' → j = j' := by
  intro a j j' hc hj hj'
  exact nonbranch_unique (fun hb => h ⟨a,live_before hj.1 hj.2,hc,hb⟩) hj hj'

end PEqualNP.Outside.L_meta_17740

namespace PEqualNP.Outside.L_meta_17740

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Relation

variable {n : ℕ} {C : Circuit}

def Loc (C : Circuit) (U : Fin n → Prop) (adj : Fin n → Fin n → Prop) : Prop :=
  (∀ v, ¬ adj v v) ∧ (∀ v w, adj v w → adj w v) ∧
  (∀ v w, U v → U w → adj v w → val C (point {v,w}) C.output = true) ∧
  (∀ v w, U v → U w → ¬ adj v w → val C (point {v,w}) C.output = false) ∧
  n ≤ C.output ∧ C.output < n + C.gates.length

variable {U : Fin n → Prop} {adj : Fin n → Fin n → Prop}

theorem single_quiet (he : Loc C U adj) {v : Fin n} (hv : U v) :
    val C (point {v}) C.output = false := by
  obtain ⟨irr, _, _, neg, _, _⟩ := he
  have h := neg v v hv hv (irr v)
  simpa using h

theorem pair_iff (he : Loc C U adj) {v w : Fin n} (hv : U v) (hw : U w) :
    val C (point {v,w}) C.output = true ↔ adj v w := by
  obtain ⟨_, _, pos, neg, _, _⟩ := he
  constructor
  · intro h
    by_contra hn
    rw [neg v w hv hw hn] at h
    contradiction
  · exact pos v w hv hw

theorem two_inputs {l : List ℕ} {a b : ℕ} (ha : a ∈ l) (hb : b ∈ l) (hne : a ≠ b)
    (hl : l.length ≤ 2) :
    ∀ i ∈ l, i = a ∨ i = b := by
  have hsub : ({a,b} : Finset ℕ) ⊆ l.toFinset := by
    intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact List.mem_toFinset.mpr ha
    · exact List.mem_toFinset.mpr hb
  have hcard : l.toFinset.card ≤ ({a,b} : Finset ℕ).card := by
    simpa [hne] using l.toFinset_card_le.trans hl
  have hEq := Finset.eq_of_subset_of_card_le hsub hcard
  intro i hi
  have hm : i ∈ ({a,b} : Finset ℕ) := hEq.symm ▸ (List.mem_toFinset.mpr hi)
  simpa using hm

theorem carries_separate (hC : Monotone2 C) {v w : Fin n} {a : ℕ}
    (h1 : val C (point {v}) a = true) (h0 : val C (point {w}) a = false) :
    Carries C v a ∧ ¬ Carries C w a := by
  have hb : val C (point (∅ : Finset (Fin n))) a = false := by
    rw [← Bool.not_eq_true]
    intro hc
    have hh := acts_mono hC (point_mono (Finset.empty_subset {w})) a hc
    rw [h0] at hh
    contradiction
  rw [carries_iff hC,carries_iff hC]
  simp [h1,h0,hb]

theorem meeting_gate (hC : Monotone2 C) (he : Loc C U adj) {v w : Fin n}
    (hUv : U v) (hUw : U w) (hvw : adj v w) :
    ∃ p g a b, C.gates[p]? = some g ∧ g.op = GateOp.and ∧ Live n C (n+p) ∧
      LNext n C a (n+p) ∧ LNext n C b (n+p) ∧
      Carries C v a ∧ ¬ Carries C w a ∧ Carries C w b ∧ ¬ Carries C v b ∧
      (∀ i ∈ g.inputs, i = a ∨ i = b) := by
  classical
  let P (i : ℕ) := Live n C i ∧ val C (point {v,w}) i = true ∧
    val C (point {v}) i = false ∧ val C (point {w}) i = false
  have hex : ∃ i, P i :=
    ⟨C.output, .refl, (pair_iff he hUv hUw).2 hvw, single_quiet he hUv, single_quiet he hUw⟩
  let j := Nat.find hex
  have hj : P j := Nat.find_spec hex
  have earlier (i : ℕ) (hlt : i < j) (hl : Live n C i)
      (htrue : val C (point {v,w}) i = true) :
      val C (point {v}) i = true ∨ val C (point {w}) i = true := by
    by_contra! h
    have h' : P i := ⟨hl, htrue, by simpa using h.1, by simpa using h.2⟩
    exact (Nat.not_le_of_gt hlt) (Nat.find_min' hex h')
  have hge : n ≤ j := by
    by_contra! hh
    let i : Fin n := ⟨j,hh⟩
    obtain ⟨_,ht,hv,hw⟩ := hj
    rw [show j = i.val from rfl,val_input] at ht hv hw
    simp only [point,decide_eq_true_eq,Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with h | h
    · simp [point,h] at hv
    · simp [point,h] at hw
  have hlt : j < n+C.gates.length := by
    by_contra! hh
    have ht := hj.2.1
    rw [val_beyond C _ hh] at ht
    contradiction
  let p := j-n
  have hp : p < C.gates.length := by dsimp [p]; omega
  have ep : n+p = j := by dsimp [p]; omega
  let g := C.gates[p]
  have hg : C.gates[p]? = some g := List.getElem?_eq_some_iff.2 ⟨hp,rfl⟩
  have hl := hC g (List.mem_of_getElem? hg)
  have hh : Live n C (n+p) := ep ▸ hj.1
  have hs1 : val C (point {v,w}) (n+p) = true := ep ▸ hj.2.1
  have hs2 : val C (point {v}) (n+p) = false := ep ▸ hj.2.2.1
  have hs3 : val C (point {w}) (n+p) = false := ep ▸ hj.2.2.2
  have reads (i : ℕ) (hi : i < n+p) (hm : i ∈ g.inputs) : LNext n C i (n+p) :=
    ⟨⟨hi,p,g,hg,rfl,hm⟩,hh⟩
  have hAnd : g.op = GateOp.and := by
    rcases hl.1 with h | h
    · exact h
    have hop : g.op = GateOp.or := h
    simp only [val_gate C _ hg, hop, GateOp.eval, List.any_map, Function.comp_apply, id,
      List.any_eq_true] at hs1
    obtain ⟨i,hi,ht⟩ := hs1
    have hi' : i < n+p := by
      by_contra hh'
      simp [operand,hh'] at ht
    have ht' : val C (point {v,w}) i = true := by simpa [operand,hi'] using ht
    rcases earlier i (ep ▸ hi') (live_before (reads i hi' hi).1 hh) ht' with hV | hW
    · have hs := hs2
      rw [← Bool.not_eq_true, val_gate C _ hg,hop,GateOp.eval,List.any_map,List.any_eq_true] at hs
      exact (hs ⟨i,hi,by simpa [operand,hi'] using hV⟩).elim
    · have hs := hs3
      rw [← Bool.not_eq_true, val_gate C _ hg,hop,GateOp.eval,List.any_map,List.any_eq_true] at hs
      exact (hs ⟨i,hi,by simpa [operand,hi'] using hW⟩).elim
  have hAll : ∀ i ∈ g.inputs, operand C (point {v,w}) (n+p) i = true := by
    simpa [val_gate C _ hg,hAnd,GateOp.eval,List.all_eq_true] using hs1
  have hFalse (x : Fin n → Bool) (hX : val C x (n+p) = false) :
      ∃ i ∈ g.inputs, operand C x (n+p) i = false := by
    by_contra! h
    have ht : val C x (n+p) = true := by
      rw [val_gate C _ hg,hAnd,GateOp.eval,List.all_map,List.all_eq_true]
      intro i hi
      simpa using h i hi
    rw [hX] at ht
    contradiction
  obtain ⟨a,ha,hwa⟩ := hFalse _ hs3
  obtain ⟨b,hb,hvb⟩ := hFalse _ hs2
  have before (i : ℕ) (h : i ∈ g.inputs) : i < n+p := by
    by_contra hi
    have hX := hAll i h
    simp [operand,hi] at hX
  have ha' := before a ha
  have hb' := before b hb
  rw [operand,ite_eq_left ha'] at hwa
  rw [operand,ite_eq_left hb'] at hvb
  have near (i : ℕ) (h : i ∈ g.inputs) :
      val C (point {v}) i = true ∨ val C (point {w}) i = true := by
    have hi := before i h
    apply earlier i (ep ▸ hi) (live_before (reads i hi h).1 hh)
    simpa [operand,hi] using hAll i h
  have hva := (near a ha).resolve_right (by rw [hwa]; decide)
  have hwb := (near b hb).resolve_left (by rw [hvb]; decide)
  have hne : a ≠ b := fun e => Bool.noConfusion (hva.symm.trans (e ▸ hvb))
  exact ⟨p,g,a,b,hg,hAnd,hh,reads a ha' ha,reads b hb' hb,
    (carries_separate hC hva hwa).1,(carries_separate hC hva hwa).2,
    (carries_separate hC hwb hvb).1,(carries_separate hC hwb hvb).2,
    two_inputs ha hb hne hl.2⟩

theorem covers_edge (hC : Monotone2 C) (he : Loc C U adj) {v w a₀ b₀ : Fin n}
    (hUv : U v) (hUw : U w) (hUa : U a₀) (hUb : U b₀)
    (hvw : adj v w) (ha₀ : adj v a₀) (hb₀ : adj w b₀) (hind : ¬ adj a₀ b₀) :
    Eligible C v ∨ Eligible C w := by
  by_contra! bad
  obtain ⟨p,g,a,b,hg,hAnd,hj,ha,hb,hva,hwa,hwb,hvb,hs⟩ := meeting_gate hC he hUv hUw hvw
  have pathV : Trace n C (Carries C v) v.val (n+p) :=
    (singleton_path (live_before ha.1 ha.2) hva).tail ⟨hva,ha⟩
  have pathW : Trace n C (Carries C w) w.val (n+p) :=
    (singleton_path (live_before hb.1 hb.2) hwb).tail ⟨hwb,hb⟩
  have uniqueV : ∀ k j j', k < n+p → Carries C v k → LNext n C k j → LNext n C k j' → j=j' :=
    fun k j j' _ => no_eligible_unique bad.1 k j j'
  have uniqueW : ∀ k j j', k < n+p → Carries C w k → LNext n C k j → LNext n C k j' → j=j' :=
    fun k j j' _ => no_eligible_unique bad.2 k j j'
  let S : Finset (Fin n) := {a₀,b₀}
  let x := point S
  let y := point (insert v S)
  let z := point (insert w S)
  have hzero : val C x C.output = false := he.2.2.2.1 a₀ b₀ hUa hUb hind
  have hY : val C y C.output = true :=
    acts_mono hC (point_mono (by intro i hi; simp only [Finset.mem_insert, Finset.mem_singleton, S] at hi ⊢; tauto)) _
      (he.2.2.1 v a₀ hUv hUa ha₀)
  have hZ : val C z C.output = true :=
    acts_mono hC (point_mono (by intro i hi; simp only [Finset.mem_insert, Finset.mem_singleton, S] at hi ⊢; tauto)) _
      (he.2.2.1 w b₀ hUw hUb hb₀)
  have jout := next_le hj
  have hvj := influence pathV uniqueV (fun _ hi => (point_insert hi).symm) ReflTransGen.refl (show val C x C.output ≠ val C y C.output from by rw [hzero,hY]; decide)
  have hwj := influence pathW uniqueW (fun _ hi => (point_insert hi).symm) ReflTransGen.refl (show val C x C.output ≠ val C z C.output from by rw [hzero,hZ]; decide)
  have hdiffV := (hvj.resolve_left (fun h => (Nat.not_lt_of_ge jout) h.1)).2
  have hdiffW := (hwj.resolve_left (fun h => (Nat.not_lt_of_ge jout) h.1)).2
  have hX : val C x (n+p) = false := by
    rw [← Bool.not_eq_true]
    intro htrue
    exact hdiffV (htrue.trans (acts_mono hC (point_mono (Finset.subset_insert _ _)) _ htrue).symm)
  have hyj : val C y (n+p) = true := by
    rw [hX] at hdiffV
    simpa using hdiffV.symm
  have hzj : val C z (n+p) = true := by
    rw [hX] at hdiffW
    simpa using hdiffW.symm
  have hAX : val C x a = val C z a := by
    by_contra h
    rcases influence pathW uniqueW (fun _ hi => (point_insert hi).symm) (live_before ha.1 ha.2) h with h' | h'
    · exact hwa h'.2
    · exact (Nat.not_le_of_gt ha.1.1) h'.1
  have hBX : val C x b = val C y b := by
    by_contra h
    rcases influence pathV uniqueV (fun _ hi => (point_insert hi).symm) (live_before hb.1 hb.2) h with h' | h'
    · exact hvb h'.2
    · exact (Nat.not_le_of_gt hb.1.1) h'.1
  have hYall : ∀ i ∈ g.inputs, operand C y (n+p) i = true := by
    simpa [val_gate C _ hg,hAnd,GateOp.eval,List.all_eq_true] using hyj
  have hZall : ∀ i ∈ g.inputs, operand C z (n+p) i = true := by
    simpa [val_gate C _ hg,hAnd,GateOp.eval,List.all_eq_true] using hzj
  have hin (i : ℕ) : LNext n C i (n+p) → i ∈ g.inputs := by
    rintro ⟨⟨_,k,g',he',hk,hmem⟩,_⟩
    have e : k=p := by omega
    subst k
    rw [hg] at he'
    cases he'
    exact hmem
  have hxA := hZall a (hin a ha)
  have hxB := hYall b (hin b hb)
  rw [operand,ite_eq_left ha.1.1,← hAX] at hxA
  rw [operand,ite_eq_left hb.1.1,← hBX] at hxB
  have hs' : val C x (n+p) = true := by
    rw [val_gate C _ hg,hAnd,GateOp.eval,List.all_map,List.all_eq_true]
    intro i hi
    rcases hs i hi with rfl | rfl
    · simpa [Function.comp_apply,operand,ha.1.1] using hxA
    · simpa [Function.comp_apply,operand,hb.1.1] using hxB
  rw [hX] at hs'
  contradiction

theorem value_at_branch {v : Fin n} {x y : Fin n → Bool} (hv : Eligible C v)
    (agrees : ∀ i, i ≠ v → x i = y i)
    (hb : val C x (firstBranch C v hv) = val C y (firstBranch C v hv)) :
    val C x C.output = val C y C.output := by
  by_contra h
  have spec := firstBranch_spec v hv
  have path := singleton_path spec.1 spec.2.1
  rcases influence path (firstBranch_unique v hv) agrees ReflTransGen.refl h with bad | bad
  · exact (Nat.not_lt_of_ge (next_le spec.1)) bad.1
  · exact bad.2 hb

theorem branch_injective (hC : Monotone2 C) (he : Loc C U adj)
    (htwins : ∀ v w : Fin n, U v → U w → v ≠ w → ¬ adj v w →
      ∃ u : Fin n, U u ∧ ¬ (adj v u ↔ adj w u))
    {v w : Fin n} (hUv : U v) (hUw : U w) (hv : Eligible C v) (hw : Eligible C w)
    (h : firstBranch C v hv = firstBranch C w hw) : v = w := by
  classical
  by_contra hne
  let b := firstBranch C v hv
  have hw_b : firstBranch C w hw = b := h.symm
  have hvtrue : val C (point {v}) b = true :=
    (carries_iff hC).1 (firstBranch_spec v hv).2.1 |>.1
  have hwtrue : val C (point {w}) b = true := by
    rw [← hw_b]
    exact (carries_iff hC).1 (firstBranch_spec w hw).2.1 |>.1
  by_cases hadj : adj v w
  · have hbig : val C (point (insert w ({v} : Finset (Fin n)))) b = true :=
      acts_mono hC (point_mono (Finset.subset_insert _ _)) b hvtrue
    have eq := value_at_branch hw
      (x := point {v}) (y := point (insert w ({v} : Finset (Fin n))))
      (fun _ hi => (point_insert hi).symm) (by rw [hw_b,hvtrue,hbig])
    have hy : val C (point (insert w ({v} : Finset (Fin n)))) C.output = true :=
      (pair_iff he hUw hUv).2 (he.2.1 v w hadj)
    rw [single_quiet he hUv,hy] at eq
    contradiction
  obtain ⟨u,hUu,hu⟩ := htwins v w hUv hUw hne hadj
  have hx : val C (point {v,u}) b = true := acts_mono hC
    (point_mono (by simp)) b hvtrue
  have hy : val C (point {w,u}) b = true := acts_mono hC
    (point_mono (by simp)) b hwtrue
  have hxyz : val C (point (insert w ({v,u} : Finset (Fin n)))) b = true :=
    acts_mono hC (point_mono (Finset.subset_insert _ _)) b hx
  have hEq : (insert w ({v,u} : Finset (Fin n))) = insert v {w,u} :=
    Finset.insert_comm _ _ _
  have e1 := value_at_branch hw
    (x := point {v,u}) (y := point (insert w ({v,u} : Finset (Fin n))))
    (fun _ hi => (point_insert hi).symm) (by rw [hw_b,hx,hxyz])
  have e2 := value_at_branch hv
    (x := point {w,u}) (y := point (insert v ({w,u} : Finset (Fin n))))
    (fun _ hi => (point_insert hi).symm) (by rw [← hEq]; exact hy.trans hxyz.symm)
  have e : val C (point {v,u}) C.output = val C (point {w,u}) C.output :=
    e1.trans (by rw [hEq,e2])
  apply hu
  rw [← pair_iff he hUv hUu, ← pair_iff he hUw hUu, e]

noncomputable def living (n : ℕ) (C : Circuit) : Finset ℕ :=
  open Classical in (Finset.range (n+C.gates.length)).filter (Live n C)

theorem mem_living {w : ℕ} : w ∈ living n C ↔ w < n+C.gates.length ∧ Live n C w := by
  classical
  simp [living]

theorem input_live (he : Loc C U adj) {v u : Fin n} (hUv : U v) (hUu : U u) (hvu : adj v u) :
    Live n C v.val := by
  have hx : val C (point {u}) C.output = false := single_quiet he hUu
  have hy : val C (point {v,u}) C.output = true := (pair_iff he hUv hUu).2 hvu
  obtain ⟨i,hi,trace⟩ := difference C (point {u}) (point {v,u}) C.output ReflTransGen.refl
    (by rw [hx,hy]; decide)
  have ei : i=v := by
    by_contra h
    exact hi ((point_insert h).symm)
  subst i
  rcases trace.cases_head with h | ⟨b,hb,_⟩
  · rw [h]
    exact .refl
  · exact live_before hb.2.1 hb.2.2

theorem live_readers_nonempty {a : ℕ} (ha : Live n C a) (hneq : a ≠ C.output) :
    (readers n C a).Nonempty := by
  rcases ha.cases_head with h | ⟨b,hb,hpath⟩
  · exact (hneq h).elim
  · exact ⟨b,mem_readers.2 ⟨hb,hpath⟩⟩

theorem readers_filter (a : ℕ) :
    open Classical in readers n C a = (living n C).filter (fun b => LNext n C a b) := by
  classical
  ext b
  simp only [mem_readers,Finset.mem_filter,mem_living]
  exact ⟨fun h => ⟨⟨next_in_range h.1,h.2⟩,h⟩, And.right⟩

theorem incoming_bound {j : ℕ} (hC : Monotone2 C) (hj : j ∈ living n C) :
    open Classical in ((living n C).filter fun i => LNext n C i j).card ≤ if j<n then 0 else 2 := by
  classical
  by_cases hi : j < n
  · rw [ite_eq_left hi]
    apply Nat.le_of_eq
    rw [Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.2
    intro i hm
    obtain ⟨_,⟨_,p,g,hg,hp,_⟩,_⟩ := Finset.mem_filter.mp hm
    omega
  rw [ite_eq_right hi]
  have hj' := (mem_living.1 hj).1
  let p := j-n
  have hp : p < C.gates.length := by dsimp [p]; omega
  have he : j=n+p := by dsimp [p]; omega
  let g := C.gates[p]
  have hg : C.gates[p]? = some g := List.getElem?_eq_some_iff.2 ⟨hp,rfl⟩
  have hsub : ((living n C).filter fun i => LNext n C i j) ⊆ g.inputs.toFinset := by
    intro a ha
    obtain ⟨_,⟨_,q,g',hg',hq,hm⟩,_⟩ := Finset.mem_filter.1 ha
    have ep : p=q := by omega
    subst q
    rw [hg] at hg'
    cases hg'
    exact List.mem_toFinset.2 hm
  exact (Finset.card_le_card hsub).trans (g.inputs.toFinset_card_le.trans
    (hC g (List.mem_of_getElem? hg)).2)

noncomputable def liveGates (n : ℕ) (C : Circuit) : Finset ℕ :=
  (living n C).filter (fun a => ¬ a < n)

theorem branch_budget (hC : Monotone2 C) (he : Loc C U adj) (Uf : Finset (Fin n))
    (hU : ∀ v ∈ Uf, U v) (hdegree : ∀ v ∈ Uf, ∃ u, U u ∧ adj v u) :
    open Classical in
      Uf.card + ((living n C).filter (Branch n C)).card ≤ (liveGates n C).card + 1 := by
  classical
  have ho : C.output ∈ living n C := mem_living.2 ⟨he.2.2.2.2.2, ReflTransGen.refl⟩
  let W := living n C
  let S := W.filter (fun a => ¬ a < n)
  let I := W.filter (fun a => a < n)
  let B := W.filter (Branch n C)
  let R := W.erase C.output
  have hI : Uf.card ≤ I.card := by
    apply Finset.card_le_card_of_injOn (fun v : Fin n => v.val)
    · intro v hv
      obtain ⟨u,hu,hvu⟩ := hdegree v hv
      exact Finset.mem_filter.2 ⟨mem_living.2 ⟨Nat.lt_add_right _ v.isLt, input_live he (hU v hv) hu hvu⟩, v.isLt⟩
    · intro a _ b _ hab
      exact Fin.ext hab
  have hW : W.card = I.card + S.card := by
    have := Finset.card_filter_add_card_filter_not (s := W) (fun a => a < n)
    exact this.symm
  have hR : R.card + 1 = W.card := by
    dsimp [R]
    have h := Finset.card_erase_add_one ho
    exact h
  have hoNone : ¬ Branch n C C.output := by
    intro h
    have hgt : 0 < (readers n C C.output).card := by unfold Branch at h; omega
    obtain ⟨b,hb⟩ := Finset.card_pos.1 hgt
    have hs := mem_readers.1 hb
    exact (Nat.not_lt_of_ge (next_le hs.2)) hs.1.1
  have hlow : R.card+B.card ≤ ∑ a ∈ W, (readers n C a).card := by
    have eR : (∑ a ∈ W, (if a=C.output then 0 else 1 : ℕ)) = R.card := by
      calc
        _ = ∑ a ∈ W, (if a≠C.output then 1 else 0 : ℕ) := by
          apply Finset.sum_congr rfl
          intro a _
          by_cases h : a=C.output <;> simp [h]
        _ = R.card := by rw [← Finset.sum_filter]; simp [R,Finset.filter_ne']
    have eB : (∑ a ∈ W, (if Branch n C a then 1 else 0 : ℕ)) = B.card := by
      rw [← Finset.sum_filter]
      simp [B]
    rw [← eR,← eB,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro a ha
    have hl := (mem_living.1 ha).2
    by_cases heq : a=C.output
    · subst a
      simp [hoNone]
    · by_cases hb : Branch n C a
      · have hb' : 2 ≤ (readers n C a).card := hb
        simpa [heq,hb] using hb'
      · simpa [heq,hb] using Nat.succ_le_of_lt (Finset.card_pos.2 (live_readers_nonempty hl heq))
  have hcomm :
      (∑ a ∈ W, (readers n C a).card) =
        ∑ j ∈ W, (W.filter fun a => LNext n C a j).card := by
    simp_rw [readers_filter,Finset.card_eq_sum_ones,Finset.sum_filter]
    exact Finset.sum_comm
  have hupp : (∑ j ∈ W, (W.filter fun a => LNext n C a j).card) ≤ 2*S.card := by
    have H : (∑ j ∈ W, (W.filter fun a => LNext n C a j).card) ≤
        ∑ j ∈ W, (if j<n then 0 else 2 : ℕ) :=
      Finset.sum_le_sum fun j hj => incoming_bound hC hj
    have e : (∑ j ∈ W, (if j<n then 0 else 2 : ℕ)) = 2*S.card := by
      simp [S,Finset.sum_ite, Nat.mul_comm]
    exact H.trans_eq e
  rw [hcomm] at hlow
  change Uf.card+B.card ≤ S.card+1
  omega

theorem cone_bound (hC : Monotone2 C) (he : Loc C U adj) (Uf : Finset (Fin n))
    (hU : ∀ v ∈ Uf, U v) (hdegree : ∀ v ∈ Uf, ∃ u, U u ∧ adj v u)
    (htwins : ∀ v w : Fin n, U v → U w → v ≠ w → ¬ adj v w →
      ∃ u : Fin n, U u ∧ ¬ (adj v u ↔ adj w u))
    (hcert : ∀ v w : Fin n, U v → U w → adj v w →
      ∃ a b : Fin n, U a ∧ U b ∧ adj v a ∧ adj w b ∧ ¬ adj a b)
    (t : ℕ) (mv mw : Fin t → Fin n)
    (hm : ∀ i, U (mv i) ∧ U (mw i) ∧ adj (mv i) (mw i))
    (hinj : ∀ i j, (mv i = mv j ∨ mv i = mw j ∨ mw i = mv j ∨ mw i = mw j) → i = j) :
    Uf.card + t ≤ (liveGates n C).card + 1 := by
  classical
  have hel (i : Fin t) : Eligible C (mv i) ∨ Eligible C (mw i) := by
    obtain ⟨h1,h2,h3⟩ := hm i
    obtain ⟨a,b,ha,hb,hva,hwb,hab⟩ := hcert _ _ h1 h2 h3
    exact covers_edge hC he h1 h2 ha hb h3 hva hwb hab
  let e (i : Fin t) : Fin n := if Eligible C (mv i) then mv i else mw i
  have hee (i : Fin t) : Eligible C (e i) := by
    by_cases h : Eligible C (mv i)
    · simp [e,h]
    · simpa [e,h] using (hel i).resolve_left h
  have hUe (i : Fin t) : U (e i) := by
    by_cases h : Eligible C (mv i)
    · simpa [e,h] using (hm i).1
    · simpa [e,h] using (hm i).2.1
  have hecase (i : Fin t) : e i = mv i ∨ e i = mw i := by
    by_cases h : Eligible C (mv i)
    · left; simp [e,h]
    · right; simp [e,h]
  let B := (living n C).filter (Branch n C)
  let f (i : Fin t) : ℕ := firstBranch C (e i) (hee i)
  have hcap : (Finset.univ : Finset (Fin t)).card ≤ B.card := by
    apply Finset.card_le_card_of_injOn f
    · intro i _
      have hb := firstBranch_spec (e i) (hee i)
      have hlt := (next_le hb.1).trans_lt he.2.2.2.2.2
      exact Finset.mem_filter.2 ⟨mem_living.2 ⟨hlt,hb.1⟩,hb.2.2⟩
    · intro i _ j _ hij
      have hev : e i = e j := branch_injective hC he htwins (hUe i) (hUe j) (hee i) (hee j) hij
      apply hinj
      rcases hecase i with h1 | h1 <;> rcases hecase j with h2 | h2 <;> rw [h1,h2] at hev <;> tauto
  rw [Finset.card_univ, Fintype.card_fin] at hcap
  have hbudget := branch_budget hC he Uf hU hdegree
  exact (Nat.add_le_add_left hcap _).trans hbudget

end PEqualNP.Outside.L_meta_17740

namespace PEqualNP.Outside.L_meta_17740

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.SplitCount PEqualNP.TopForm PEqualNP.BlindGate
open Relation

theorem cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

theorem cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

theorem inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

theorem inCone_trans (n : ℕ) (C : Circuit) (a k : ℕ) (hak : InCone n C a k) :
    ∀ j, InCone n C k j → InCone n C a j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k2, hk2, hin, h3 | h3⟩ := h
    · subst h3
      rw [inCone_iff]
      exact ⟨h0, k, hk2, hin, Or.inr hak⟩
    · rw [inCone_iff]
      exact ⟨h0, k2, hk2, hin, Or.inr (ih k2 hk2 h3)⟩

theorem reach_cone {n : ℕ} (C : Circuit) (q : ℕ) (hout : C.output = n + q) :
    ∀ a, Live n C a → ∀ i, a = n + i → (i = q ∨ InCone n C i q) := by
  intro a ha
  unfold Live at ha
  induction ha using ReflTransGen.head_induction_on with
  | refl => intro i hi; left; omega
  | head hn _ ih =>
    intro i hi
    obtain ⟨hlt, p, g, hg, hc, hmem⟩ := hn
    have hd : InCone n C i p := by
      rw [inCone_iff]
      refine ⟨(List.getElem?_eq_some_iff.1 hg).1, i, by omega, ?_, Or.inl rfl⟩
      have hga : gateAt C p = g := by
        unfold gateAt
        simp [List.getD_eq_getElem?_getD, hg]
      rw [hga, ← hi]
      exact hmem
    rcases ih p hc with h | h
    · subst h
      right
      exact hd
    · right
      exact inCone_trans n C i p hd q h

theorem live_card (C : Circuit) (o : ℕ) (ho26 : 26 ≤ o) (ho : o < 90) :
    ∃ T : Finset ℕ, T.card = (liveGates 26 (⟨C.gates, o⟩ : Circuit)).card ∧
      ∀ g ∈ T, g < 64 ∧ InConeOrSelf 26 C g (o - 26) := by
  classical
  refine ⟨(liveGates 26 (⟨C.gates, o⟩ : Circuit)).image (fun w => w - 26), ?_, ?_⟩
  · apply Finset.card_image_of_injOn
    intro x hx y hy hxy
    have h1 := (Finset.mem_filter.1 hx).2
    have h2 := (Finset.mem_filter.1 hy).2
    simp only at hxy
    omega
  · intro g hg
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hg
    obtain ⟨hw1, hw2⟩ := Finset.mem_filter.1 hw
    have hlive := (mem_living.1 hw1).2
    have hle : w ≤ o := next_le hlive
    refine ⟨by omega, ?_⟩
    have h := reach_cone (n := 26) (⟨C.gates, o⟩ : Circuit) (o - 26)
      (show o = 26 + (o - 26) by omega) w hlive (w - 26) (by omega)
    exact h

abbrev E (p l : Fin 13) : Prop := p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9

abbrev hit (x : Fin 26 → Bool) : Prop :=
  ∃ p l : Fin 13, E p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true

def incB (p l : ℕ) : Bool :=
  (p + 13 - l) % 13 == 0 || (p + 13 - l) % 13 == 1 || (p + 13 - l) % 13 == 3 ||
    (p + 13 - l) % 13 == 9

def adjB (v w : Fin 26) : Bool :=
  (decide (v.val < 13) && decide (13 ≤ w.val) && incB v.val (w.val - 13)) ||
    (decide (w.val < 13) && decide (13 ≤ v.val) && incB w.val (v.val - 13))

abbrev adj (v w : Fin 26) : Prop := adjB v w = true

def inUa (v : Fin 26) : Bool :=
  !(v.val == 0 || v.val == 1 || v.val == 3 || v.val == 9 || v.val == 13)

def inUb (v : Fin 26) : Bool := !(v.val == 13)

def allF (f : Fin 26 → Bool) : Bool := (List.finRange 26).all f

def anyF (f : Fin 26 → Bool) : Bool := (List.finRange 26).any f

theorem allF_spec {f : Fin 26 → Bool} (h : allF f = true) (v : Fin 26) : f v = true := by
  unfold allF at h
  rw [List.all_eq_true] at h
  exact h v (List.mem_finRange v)

theorem anyF_spec {f : Fin 26 → Bool} (h : anyF f = true) : ∃ v : Fin 26, f v = true := by
  unfold anyF at h
  rw [List.any_eq_true] at h
  obtain ⟨v, _, hv⟩ := h
  exact ⟨v, hv⟩

theorem E_adj : ∀ p l : Fin 13, E p l → adjB (Fin.castAdd 13 p) (Fin.natAdd 13 l) = true := by
  decide +kernel

theorem adj_E_aux : ∀ v w : Fin 26, decide (v.val < 13) && decide (13 ≤ w.val) && incB v.val (w.val - 13) = true →
    ∃ p l : Fin 13, E p l ∧ v = Fin.castAdd 13 p ∧ w = Fin.natAdd 13 l := by
  decide +kernel

theorem adj_E {v w : Fin 26} (h : adjB v w = true) :
    ∃ p l : Fin 13, E p l ∧ ((v = Fin.castAdd 13 p ∧ w = Fin.natAdd 13 l) ∨
      (w = Fin.castAdd 13 p ∧ v = Fin.natAdd 13 l)) := by
  unfold adjB at h
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · obtain ⟨p, l, hE, h1, h2⟩ := adj_E_aux v w h
    exact ⟨p, l, hE, Or.inl ⟨h1, h2⟩⟩
  · obtain ⟨p, l, hE, h1, h2⟩ := adj_E_aux w v h
    exact ⟨p, l, hE, Or.inr ⟨h1, h2⟩⟩

theorem adj_irr : ∀ v : Fin 26, ¬ adj v v := by decide +kernel

theorem adj_sym : ∀ v w : Fin 26, adjB v w = adjB w v := by decide +kernel

theorem hit_of_adj {z : Fin 26 → Bool} {v w : Fin 26} (h : adjB v w = true)
    (hv : z v = true) (hw : z w = true) : hit z := by
  obtain ⟨p, l, hE, h1 | h1⟩ := adj_E h
  · exact ⟨p, l, hE, h1.1 ▸ hv, h1.2 ▸ hw⟩
  · exact ⟨p, l, hE, h1.1 ▸ hw, h1.2 ▸ hv⟩

theorem quiet (S : Finset (Fin 26)) (hS : ∀ u ∈ S, ∀ v ∈ S, adjB u v = false) :
    ¬ hit (point S) := by
  rintro ⟨p, l, hE, hp, hl⟩
  have h1 : Fin.castAdd 13 p ∈ S := by simpa [point] using hp
  have h2 : Fin.natAdd 13 l ∈ S := by simpa [point] using hl
  have := hS _ h1 _ h2
  rw [E_adj p l hE] at this
  contradiction

theorem maximal_above (S : Finset (Fin 26)) (hS : ∀ u ∈ S, ∀ v ∈ S, adjB u v = false) :
    ∃ z : Fin 26 → Bool, Maximal (fun x => ¬ hit x) z ∧ ∀ i ∈ S, z i = true := by
  obtain ⟨z, hle, hz⟩ := Finite.exists_le_maximal (p := fun t : Fin 26 → Bool => ¬ hit t) (quiet S hS)
  refine ⟨z, hz, ?_⟩
  intro i hi
  have h1 : point S i = true := by simp [point, hi]
  exact Bool.eq_true_of_true_le (h1 ▸ hle i)

theorem val_eq (C : Circuit) (o : ℕ) (x : Fin 26 → Bool) (w : ℕ) :
    val (⟨C.gates, o⟩ : Circuit) x w = wireValue C 26 x w := rfl

theorem pos_wire (C : Circuit) (o : ℕ)
    (hedge : ∀ p l : Fin 13, E p l → wireValue C 26
      (fun i : Fin 26 => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)) o = true)
    (v w : Fin 26) (h : adj v w) :
    val (⟨C.gates, o⟩ : Circuit) (point {v, w}) o = true := by
  rw [val_eq]
  obtain ⟨p, l, hE, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := adj_E h
  · have e : point ({v, w} : Finset (Fin 26)) =
        fun i : Fin 26 => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l) := by
      funext i
      simp [point, h1, h2]
    rw [e]
    exact hedge p l hE
  · have e : point ({v, w} : Finset (Fin 26)) =
        fun i : Fin 26 => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l) := by
      funext i
      simp [point, h1, h2, or_comm]
    rw [e]
    exact hedge p l hE

theorem neg_wire (C : Circuit) (o : ℕ) (hM : Monotone2 (⟨C.gates, o⟩ : Circuit))
    (S : Finset (Fin 26)) (hS : ∀ u ∈ S, ∀ v ∈ S, adjB u v = false)
    (hz : ∀ z : Fin 26 → Bool, Maximal (fun x => ¬ hit x) z → (∀ i ∈ S, z i = true) →
      wireValue C 26 z o = false)
    (T : Finset (Fin 26)) (hT : T ⊆ S) :
    val (⟨C.gates, o⟩ : Circuit) (point T) o = false := by
  obtain ⟨z, hmax, hzS⟩ := maximal_above S hS
  have hf := hz z hmax hzS
  rw [← Bool.not_eq_true]
  intro ht
  have := acts_mono hM (x := point T) (y := z) (by
    intro i hi
    apply hzS i
    apply hT
    simpa [point] using hi) o ht
  rw [val_eq, hf] at this
  contradiction

theorem wire_ge (C : Circuit) (o : ℕ)
    (hedge : ∀ p l : Fin 13, E p l → wireValue C 26
      (fun i : Fin 26 => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)) o = true) :
    26 ≤ o := by
  by_contra hlt
  have hlt' : o < 26 := by omega
  let i : Fin 26 := ⟨o, hlt'⟩
  have key (x : Fin 26 → Bool) : wireValue C 26 x o = x i := by
    rw [← val_eq C 0]
    exact val_input _ x i
  have h0 := hedge 0 0 (Or.inl rfl)
  have h1 := hedge 1 1 (Or.inl rfl)
  rw [key] at h0 h1
  simp only [decide_eq_true_eq] at h0 h1
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rw [h0] at h1 <;>
    exact absurd h1 (by decide)

def UaF : Finset (Fin 26) := Finset.univ.filter (fun v => inUa v = true)

def UbF : Finset (Fin 26) := Finset.univ.filter (fun v => inUb v = true)

theorem UaF_card : UaF.card = 21 := by decide +kernel

theorem UbF_card : UbF.card = 25 := by decide +kernel

theorem degA : allF (fun v => !inUa v || anyF (fun u => inUa u && adjB v u)) = true := by
  decide +kernel

theorem degB : allF (fun v => !inUb v || anyF (fun u => inUb u && adjB v u)) = true := by
  decide +kernel

theorem twA : allF (fun v => allF (fun w => !inUa v || !inUa w || decide (v = w) || adjB v w ||
    anyF (fun u => inUa u && (adjB v u != adjB w u)))) = true := by
  decide +kernel

theorem twB : allF (fun v => allF (fun w => !inUb v || !inUb w || decide (v = w) || adjB v w ||
    anyF (fun u => inUb u && (adjB v u != adjB w u)))) = true := by
  decide +kernel

theorem certA : allF (fun v => allF (fun w => !inUa v || !inUa w || !adjB v w ||
    anyF (fun a => anyF (fun b => inUa a && inUa b && adjB v a && adjB w b && !adjB a b)))) = true := by
  decide +kernel

theorem certB : allF (fun v => allF (fun w => !inUb v || !inUb w || !adjB v w ||
    anyF (fun a => anyF (fun b => inUb a && inUb b && adjB v a && adjB w b && !adjB a b)))) = true := by
  decide +kernel

theorem ua13 : allF (fun v => !inUa v || (!adjB v 13 && !adjB 13 v)) = true := by
  decide +kernel

theorem pickq : allF (fun v => allF (fun w => !inUb v || !inUb w ||
    anyF (fun q => adjB q 13 && !adjB v q && !adjB q v && !adjB w q && !adjB q w))) = true := by
  decide +kernel

def mvA (i : Fin 9) : Fin 26 := ([2, 4, 5, 6, 7, 8, 10, 11, 12] : List (Fin 26)).getD i.val 0

def mwA (i : Fin 9) : Fin 26 := ([15, 17, 18, 19, 20, 21, 23, 24, 25] : List (Fin 26)).getD i.val 0

def mvB (i : Fin 12) : Fin 26 := ⟨i.val + 1, by omega⟩

def mwB (i : Fin 12) : Fin 26 := ⟨i.val + 14, by omega⟩

theorem hmA : ∀ i : Fin 9, inUa (mvA i) = true ∧ inUa (mwA i) = true ∧ adjB (mvA i) (mwA i) = true := by
  decide +kernel

theorem hmB : ∀ i : Fin 12, inUb (mvB i) = true ∧ inUb (mwB i) = true ∧ adjB (mvB i) (mwB i) = true := by
  decide +kernel

theorem hinjA : ∀ i j : Fin 9, (mvA i = mvA j ∨ mvA i = mwA j ∨ mwA i = mvA j ∨ mwA i = mwA j) → i = j := by
  decide +kernel

theorem hinjB : ∀ i j : Fin 12, (mvB i = mvB j ∨ mvB i = mwB j ∨ mwB i = mvB j ∨ mwB i = mwB j) → i = j := by
  decide +kernel

end PEqualNP.Outside.L_meta_17740

namespace PEqualNP.Outside.L_meta_17740

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.SplitCount PEqualNP.TopForm PEqualNP.BlindGate
open Relation

theorem ff {b : Bool} (h1 : b = false) (h2 : b = true) : False :=
  Bool.false_ne_true (h1.symm.trans h2)

theorem cone_size (C : Circuit) (o : ℕ) (hM : Monotone2 (⟨C.gates, o⟩ : Circuit))
    (inU : Fin 26 → Bool) (Uf : Finset (Fin 26)) (hUf : ∀ v ∈ Uf, inU v = true)
    (ho26 : 26 ≤ o) (ho : o < 90) (hlen : C.gates.length = 65)
    (hpos : ∀ v w : Fin 26, adj v w → val (⟨C.gates, o⟩ : Circuit) (point {v, w}) o = true)
    (hneg : ∀ v w : Fin 26, inU v = true → inU w = true → ¬ adj v w →
      val (⟨C.gates, o⟩ : Circuit) (point {v, w}) o = false)
    (hdeg : allF (fun v => !inU v || anyF (fun u => inU u && adjB v u)) = true)
    (htw : allF (fun v => allF (fun w => !inU v || !inU w || decide (v = w) || adjB v w ||
      anyF (fun u => inU u && (adjB v u != adjB w u)))) = true)
    (hcert : allF (fun v => allF (fun w => !inU v || !inU w || !adjB v w ||
      anyF (fun a => anyF (fun b => inU a && inU b && adjB v a && adjB w b && !adjB a b)))) = true)
    (t : ℕ) (mv mw : Fin t → Fin 26)
    (hm : ∀ i, inU (mv i) = true ∧ inU (mw i) = true ∧ adjB (mv i) (mw i) = true)
    (hinj : ∀ i j, (mv i = mv j ∨ mv i = mw j ∨ mw i = mv j ∨ mw i = mw j) → i = j) :
    ∃ T : Finset ℕ, Uf.card + t ≤ T.card + 1 ∧
      ∀ g ∈ T, g < 64 ∧ InConeOrSelf 26 C g (o - 26) := by
  have he : Loc (⟨C.gates, o⟩ : Circuit) (fun v : Fin 26 => inU v = true) adj := by
    refine ⟨adj_irr, ?_, ?_, ?_, ho26, ?_⟩
    · intro v w h
      show adjB w v = true
      rw [← adj_sym v w]
      exact h
    · intro v w _ _ h
      exact hpos v w h
    · intro v w hv hw h
      exact hneg v w hv hw h
    · show o < 26 + C.gates.length
      omega
  have hb := cone_bound hM he Uf hUf
    (by
      intro v hv
      have h := allF_spec hdeg v
      simp only [Bool.or_eq_true, Bool.not_eq_true'] at h
      rcases h with h | h
      · exact (ff h (hUf v hv)).elim
      · obtain ⟨u, hu⟩ := anyF_spec h
        simp only [Bool.and_eq_true] at hu
        exact ⟨u, hu.1, hu.2⟩)
    (by
      intro v w hv hw hne hadj
      have h := allF_spec (allF_spec htw v) w
      simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
      rcases h with (((h | h) | h) | h) | h
      · exact (ff h hv).elim
      · exact (ff h hw).elim
      · exact (hne h).elim
      · exact (hadj h).elim
      · obtain ⟨u, hu⟩ := anyF_spec h
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hu
        exact ⟨u, hu.1, fun hiff => hu.2 (Bool.eq_iff_iff.2 hiff)⟩)
    (by
      intro v w hv hw hadj
      have h := allF_spec (allF_spec hcert v) w
      simp only [Bool.or_eq_true, Bool.not_eq_true'] at h
      rcases h with ((h | h) | h) | h
      · exact (ff h hv).elim
      · exact (ff h hw).elim
      · exact (ff h hadj).elim
      · obtain ⟨a, ha⟩ := anyF_spec h
        obtain ⟨b, hb⟩ := anyF_spec ha
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hb
        exact ⟨a, b, hb.1.1.1.1, hb.1.1.1.2, hb.1.1.2, hb.1.2, fun hc => ff hb.2 hc⟩)
    t mv mw hm hinj
  obtain ⟨T, hT, hTc⟩ := live_card C o ho26 ho
  exact ⟨T, by rw [hT]; exact hb, hTc⟩

theorem main (C : Circuit) (a b : ℕ) (hsize : C.size = 65) (hao : IsAO2 26 C)
    (hgate : C.gates[64]? = some ⟨GateOp.and, [a, b]⟩)
    (hedge : ∀ p l : Fin 13, E p l →
      wireValue C 26 (fun i : Fin 26 => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)) a = true ∧
      wireValue C 26 (fun i : Fin 26 => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)) b = true)
    (hneg : ∀ z : Fin 26 → Bool, Maximal (fun x => ¬ hit x) z →
      wireValue C 26 z (if z 13 = true then a else b) = false)
    (hdisj : ¬ ∃ g < 64, 26 ≤ a ∧ 26 ≤ b ∧ InConeOrSelf 26 C g (a - 26) ∧
      InConeOrSelf 26 C g (b - 26)) : False := by
  have hlen : C.gates.length = 65 := hsize
  have hM (o : ℕ) : Monotone2 (⟨C.gates, o⟩ : Circuit) := by
    intro g hg
    refine ⟨?_, le_of_eq (hao.2.2 g hg)⟩
    rcases hao.1 g hg with h | h <;> simp [h]
  have hga : gateAt C 64 = ⟨GateOp.and, [a, b]⟩ := by
    unfold gateAt
    simp [List.getD_eq_getElem?_getD, hgate]
  have hback := hao.2.1 64 (by omega)
  rw [hga] at hback
  have ha90 : a < 90 := hback a (by simp)
  have hb90 : b < 90 := hback b (by simp)
  have ha26 : 26 ≤ a := wire_ge C a (fun p l h => (hedge p l h).1)
  have hb26 : 26 ≤ b := wire_ge C b (fun p l h => (hedge p l h).2)
  have nf {v w : Fin 26} (h : ¬ adj v w) : adjB v w = false := Bool.eq_false_iff.2 h
  obtain ⟨TA, hTA, hTAc⟩ := cone_size C a (hM a) inUa UaF
    (fun v hv => (Finset.mem_filter.1 hv).2) ha26 ha90 hlen
    (fun v w h => pos_wire C a (fun p l h => (hedge p l h).1) v w h)
    (by
      intro v w hv hw hadj
      have f1 := nf hadj
      have f2 : adjB w v = false := by rw [← adj_sym v w]; exact f1
      have f3 := nf (adj_irr v)
      have f4 := nf (adj_irr w)
      have f5 := nf (adj_irr 13)
      have hv13 := allF_spec ua13 v
      have hw13 := allF_spec ua13 w
      simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true] at hv13 hw13
      have hv13' := hv13.resolve_left (fun h => ff h hv)
      have hw13' := hw13.resolve_left (fun h => ff h hw)
      have g1 := hv13'.1
      have g2 := hv13'.2
      have g3 := hw13'.1
      have g4 := hw13'.2
      refine neg_wire C a (hM a) {v, w, 13} ?_ ?_ {v, w} ?_
      · intro u hu x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu hx
        rcases hu with rfl | rfl | rfl <;> rcases hx with rfl | rfl | rfl <;> assumption
      · intro z hmax hzS
        have h13 : z 13 = true := hzS 13 (by simp)
        have := hneg z hmax
        rw [ite_eq_left h13] at this
        exact this
      · exact Finset.insert_subset_insert v
          (Finset.singleton_subset_iff.2 (Finset.mem_insert_self w _)))
    degA twA certA 9 mvA mwA hmA hinjA
  obtain ⟨TB, hTB, hTBc⟩ := cone_size C b (hM b) inUb UbF
    (fun v hv => (Finset.mem_filter.1 hv).2) hb26 hb90 hlen
    (fun v w h => pos_wire C b (fun p l h => (hedge p l h).2) v w h)
    (by
      intro v w hv hw hadj
      have f1 := nf hadj
      have f2 : adjB w v = false := by rw [← adj_sym v w]; exact f1
      have f3 := nf (adj_irr v)
      have f4 := nf (adj_irr w)
      have hq := allF_spec (allF_spec pickq v) w
      simp only [Bool.or_eq_true, Bool.not_eq_true'] at hq
      rcases hq with (hq | hq) | hq
      · exact (ff hq hv).elim
      · exact (ff hq hw).elim
      obtain ⟨q, hq⟩ := anyF_spec hq
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hq
      obtain ⟨⟨⟨⟨q13, g1⟩, g2⟩, g3⟩, g4⟩ := hq
      have f5 := nf (adj_irr q)
      refine neg_wire C b (hM b) {v, w, q} ?_ ?_ {v, w} ?_
      · intro u hu x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu hx
        rcases hu with rfl | rfl | rfl <;> rcases hx with rfl | rfl | rfl <;> assumption
      · intro z hmax hzS
        have h13 : ¬ z 13 = true := by
          intro h13
          exact hmax.1 (hit_of_adj q13 (hzS q (by simp)) h13)
        have := hneg z hmax
        rw [ite_eq_right h13] at this
        exact this
      · exact Finset.insert_subset_insert v
          (Finset.singleton_subset_iff.2 (Finset.mem_insert_self w _)))
    degB twB certB 12 mvB mwB hmB hinjB
  rw [UaF_card] at hTA
  rw [UbF_card] at hTB
  have hd : Disjoint TA TB := by
    rw [Finset.disjoint_left]
    intro g hgA hgB
    exact hdisj ⟨g, (hTAc g hgA).1, ha26, hb26, (hTAc g hgA).2, (hTBc g hgB).2⟩
  have hsub : TA ∪ TB ⊆ Finset.range 64 := by
    intro g hg
    rcases Finset.mem_union.1 hg with h | h
    · exact Finset.mem_range.2 (hTAc g h).1
    · exact Finset.mem_range.2 (hTBc g h).1
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hd, Finset.card_range] at hc
  omega

end PEqualNP.Outside.L_meta_17740

theorem PEqualNP.Outside.L_meta_17740 : have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : (Fin (26 : ℕ) → Bool) → Prop := fun (x2 : Fin (26 : ℕ) → Bool) => ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), x1 x3 x4 ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),   x3.size = (65 : ℕ) →     PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 →       (∀ x8 ∈ x3.gates, x8.inputs.Nodup) →         x3.output = (90 : ℕ) →           x3.gates[(64 : ℕ)]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x4, x5] : PEqualNP.CircuitLowerBounds.Gate } →             (∀ (x11 x12 : Fin (13 : ℕ)),                 x1 x11 x12 →                   have x14 : Fin (26 : ℕ) → Bool := fun (x14 : Fin (26 : ℕ)) => Decidable.decide (x14 = Fin.castAdd (13 : ℕ) x11 ∨ x14 = Fin.natAdd (13 : ℕ) x12);                   PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x14 x4 = Bool.true ∧ PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x14 x5 = Bool.true) →               (∀ (x12 : Fin (26 : ℕ) → Bool), Maximal (fun (x13 : Fin (26 : ℕ) → Bool) => ¬x2 x13) x12 → PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x12 (if x12 (13 : Fin (26 : ℕ)) = Bool.true then x4 else x5) = Bool.false) → (¬∃ x13 < (64 : ℕ), (26 : ℕ) ≤ x4 ∧ (26 : ℕ) ≤ x5 ∧ PEqualNP.SplitCount.InConeOrSelf (26 : ℕ) x3 x13 (x4 - (26 : ℕ)) ∧ PEqualNP.SplitCount.InConeOrSelf (26 : ℕ) x3 x13 (x5 - (26 : ℕ))) → ∃ (x14 : PEqualNP.CircuitLowerBounds.Circuit) (x15 : ℕ) (x16 : ℕ), x14.size ≤ (63 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) x14 ∧ (∀ x17 ∈ x14.gates, x17.inputs.Nodup) ∧ x15 ≠ x16 ∧ x15 < (26 : ℕ) + x14.size ∧ x16 < (26 : ℕ) + x14.size ∧ ∀ (x17 : Fin (26 : ℕ) → Bool), PEqualNP.BlindGate.wireValue x14 (26 : ℕ) x17 x15 = PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x17 x4 ∧ PEqualNP.BlindGate.wireValue x14 (26 : ℕ) x17 x16 = PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x17 x5 := by
  intro x1 x2 C a b h1 h2 _ _ h5 h6 h7 h8
  exact (PEqualNP.Outside.L_meta_17740.main C a b h1 h2 h5 h6 h7 h8).elim
