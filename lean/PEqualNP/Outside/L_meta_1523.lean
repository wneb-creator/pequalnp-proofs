import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1523_aux
open PEqualNP.CircuitLowerBounds

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
    rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then value C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then value C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

lemma gate_inputs {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : ℕ) (hn : n ≤ w) (hw : w < n + C.size) :
    ∃ P : Finset ℕ, P.card ≤ 2 ∧ (∀ r ∈ P, r < w) ∧
      ∀ (x y : Fin n → Bool), (∀ r ∈ P, value C x r = true → value C y r = true) →
        value C x w = true → value C y w = true := by
  let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
  obtain ⟨hop, hlen⟩ := hG g (List.getElem_mem _)
  let P := g.inputs.toFinset.filter (· < w)
  refine ⟨P, (Finset.card_filter_le _ _).trans ((List.toFinset_card_le g.inputs).trans hlen), ?_, ?_⟩
  · exact fun r hr => (Finset.mem_filter.mp hr).2
  · intro x y hxy hx
    have step (r) (hr : r ∈ g.inputs) :
        (if r < w then value C x r else false) = true →
        (if r < w then value C y r else false) = true := by
      by_cases h : r < w
      · simpa [h] using hxy r (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr,h⟩)
      · simp [h]
    have form (z : Fin n → Bool) :
        value C z w = g.op.eval (g.inputs.map fun r => if r < w then value C z r else false) :=
      gate_value C z w hn hw
    rw [form x] at hx
    rw [form y]
    rcases hop with hop|hop
    · simp only [hop, GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at hx ⊢
      intro b hb
      obtain ⟨r,hr,rfl⟩ := hb
      exact step r hr (hx _ ⟨r,hr,rfl⟩)
    · simp only [hop, GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hx ⊢
      obtain ⟨b,⟨r,hr,rfl⟩,hv⟩ := hx
      exact ⟨_, ⟨r,hr,rfl⟩, step r hr hv⟩

lemma value_mono {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using hxy p
    by_cases hw : w < n + C.size
    · obtain ⟨P, _, hP, hstep⟩ := gate_inputs C hG w (by omega) hw
      exact hstep x y fun r hr => ih r (hP r hr)
    · simp [missing_value C x w (by omega)]


abbrev V := Fin 13

def line (s : V) : Finset V := {s,s+1,s+3,s+9}
def extra (s p : V) : Finset V :=
  if p ∈ ({0,1,3} : Finset V) then ∅ else
    if 0 ∈ line s then {1} else if 1 ∈ line s then {3} else {0}
def pos (s p : V) (v : V) := decide (v=p ∨ v ∈ extra s p)
def neg (s : V) (v : V) := decide (v ∉ line s)
def dom (x : V → Bool) : Prop :=
  (∃ v ∈ ({0,1,3} : Finset V), x v = true) ∨ ∃ s : V, ∀ v : V, x v = false → v ∈ line s

def marker (s : V) : V := if 0∈line s then 1 else if 1∈line s then 3 else 0

theorem extra_form (s p : V) : extra s p =
    if p∈({0,1,3} : Finset V) then ∅ else {marker s} := by
  unfold extra marker
  split_ifs <;> rfl

theorem marker_mem (s : V) : marker s ∈ ({0,1,3} : Finset V) := by
  unfold marker
  split_ifs <;> simp

theorem marker_off : ∀ s : V, s≠0 → marker s ∉ line s := by decide
theorem marker_apart : ∀ s t : V, s≠0 → t≠0 → s≠t →
    ¬ (marker s∈line t ∧ marker t∈line s) := by decide

theorem geometry : ∀ s : V, s ≠ 0 → ∀ p ∈ line s, extra s p ∩ line s = ∅ ∧ dom (pos s p) := by
  intro s hs p _
  by_cases h : p∈({0,1,3} : Finset V)
  · have small : extra s p = ∅ := by simp [extra_form,h]
    exact ⟨by simp [small],Or.inl ⟨p,h,by simp [pos]⟩⟩
  · have small : extra s p = {marker s} := by simp [extra_form,h]
    refine ⟨?_,Or.inl ⟨marker s,marker_mem s,by simp [pos,small]⟩⟩
    exact Finset.eq_empty_iff_forall_notMem.mpr fun q hq => by
      obtain ⟨hm,hl⟩ := Finset.mem_inter.mp hq
      have eq : q=marker s := Finset.mem_singleton.mp (small ▸ hm)
      exact marker_off s hs (eq ▸ hl)

theorem pos_hot (s p : V) : ∃ v ∈ ({0,1,3} : Finset V), pos s p v=true := by
  by_cases hp : p∈({0,1,3} : Finset V)
  · exact ⟨p,hp,by simp [pos]⟩
  · exact ⟨marker s,marker_mem s,by simp [pos,extra_form,hp]⟩

theorem separated : ∀ s t : V, s ≠ 0 → t ≠ 0 → s ≠ t →
    ¬ ((∃ p ∈ line s \ line t, (extra s p ∩ line t).Nonempty) ∧
       (∃ p ∈ line t \ line s, (extra t p ∩ line s).Nonempty)) := by
  intro s t hs ht ne h
  have hit (a b : V) (ex : ∃ p∈line a \ line b, (extra a p ∩ line b).Nonempty) :
      marker a∈line b := by
    obtain ⟨p,_,q,hq⟩ := ex
    obtain ⟨ha,hb⟩ := Finset.mem_inter.mp hq
    by_cases hp : p∈({0,1,3} : Finset V)
    · simp [extra_form,hp] at ha
    · have eq : q=marker a := by simpa [extra_form,hp] using ha
      simpa [eq] using hb
  exact marker_apart s t hs ht ne ⟨hit s t h.1,hit t s h.2⟩

theorem lineCard : ∀ s : V, (line s).card = 4 := by decide
theorem lineMeet : ∀ s t : V, s ≠ t → (line s ∩ line t).card ≤ 1 := by decide

abbrev Good (C : Circuit) := ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

def covered (C : Circuit) (s : V) (w : ℕ) : Finset V :=
  (line s).filter (fun p => value C (pos s p) w = true)

def orOp : GateOp → Bool | .or => true | _ => false

theorem orOp_only (op : GateOp) (h : orOp op = true) : op = GateOp.or := by
  cases op <;> simp_all [orOp]

def orAt (C : Circuit) (j : ℕ) : Bool :=
  match C.gates[j]? with
  | some g => orOp g.op
  | none => false

def marked (C : Circuit) (s : V) : Finset ℕ :=
  (Finset.range C.size).filter fun j => orAt C j = true ∧
    value C (neg s) (13+j) = false ∧ 2 ≤ (covered C s (13+j)).card

theorem bounds (C : Circuit) (s : V) (hs : s ≠ 0) (w : ℕ)
    (hf : value C (neg s) w = false) (hc : 2 ≤ (covered C s w).card) :
    13 ≤ w ∧ w < 13+C.size := by
  constructor
  · by_contra! hw
    let v : V := ⟨w,hw⟩
    have vm : v ∈ line s := by
      change value C (neg s) v = false at hf
      simpa [input_value,neg] using hf
    have sub : covered C s w ⊆ {v} := by
      intro p hp
      obtain ⟨hm,hv⟩ := Finset.mem_filter.mp hp
      change value C (pos s p) v = true at hv
      have dis := (geometry s hs p hm).1
      have rule : v=p ∨ v∈extra s p := by simpa [input_value,pos] using hv
      rcases rule with e|e
      · simp [e]
      · have bad := Finset.mem_inter.mpr ⟨e,vm⟩
        rw [dis] at bad
        exact (Finset.notMem_empty v bad).elim
    have := Finset.card_le_card sub
    simp at this
    omega
  · by_contra! h
    have no : covered C s w = ∅ := by ext p; simp [covered,missing_value C _ w h]
    simp [no] at hc

def charged (C : Circuit) (s : V) : Finset ℕ := (marked C s).image (13+·)

theorem parents (C : Circuit) (hG : Good C) (s : V) (hs : s≠0) (w : ℕ)
    (hf : value C (neg s) w=false) (hc : 2≤(covered C s w).card) :
    ∃ Q : Finset ℕ, (∀ r∈Q, r<w ∧ value C (neg s) r=false) ∧
      covered C s w ⊆ Q.biUnion (covered C s) ∧ Q.card ≤ if w∈charged C s then 2 else 1 := by
  classical
  obtain ⟨lo,hi⟩ := bounds C s hs w hf hc
  let j := w-13
  have hj : j<C.gates.length := by unfold j Circuit.size at *; omega
  have ew : 13+j=w := by unfold j; omega
  let g := C.gates[j]
  have atg : C.gates[j]? = some g := List.getElem?_eq_getElem hj
  have eqv (x : V → Bool) :
      value C x w = g.op.eval (g.inputs.map fun r => if r<w then value C x r else false) :=
    gate_value C x w lo hi
  obtain ⟨op,hl⟩ := hG g (List.getElem_mem _)
  rcases op with op|op
  · have allTrue (x : V → Bool) (h : value C x w=true) (r : ℕ) (hr : r∈g.inputs) :
        (if r<w then value C x r else false) = true := by
      rw [eqv x,op] at h
      simpa only [GateOp.eval,List.all_map,List.all_eq_true,Function.comp_apply,id_eq] using
        ((List.all_eq_true.mp h) _ (List.mem_map.mpr ⟨r,hr,rfl⟩))
    have someFalse : ∃ r∈g.inputs, (if r<w then value C (neg s) r else false) = false := by
      by_contra! bad
      have yes : value C (neg s) w = true := by
        rw [eqv,op]
        simp only [GateOp.eval,List.all_eq_true,List.mem_map,id_eq]
        rintro b ⟨r,hr,rfl⟩
        exact Bool.eq_true_of_not_eq_false (bad r hr)
      simp [hf] at yes
    obtain ⟨r,hr,hrf⟩ := someFalse
    obtain ⟨p,hp⟩ := Finset.card_pos.mp (show 0<(covered C s w).card by omega)
    have tt := allTrue _ (Finset.mem_filter.mp hp).2 r hr
    have earlier : r<w := by by_contra he; simp [he] at tt
    refine ⟨{r},?_,?_,?_⟩
    · intro u hu
      obtain rfl := Finset.mem_singleton.mp hu
      exact ⟨earlier,by simpa [earlier] using hrf⟩
    · intro q hq
      obtain ⟨hm,hv⟩ := Finset.mem_filter.mp hq
      exact Finset.mem_biUnion.mpr ⟨r,by simp,Finset.mem_filter.mpr ⟨hm,by simpa [earlier] using allTrue _ hv r hr⟩⟩
    · split <;> simp
  · have markedJ : j∈marked C s := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr hj,?_⟩
      simp [orAt,orOp,atg,op,ew,hf,hc]
    have cost : w∈charged C s := Finset.mem_image.mpr ⟨j,markedJ,ew⟩
    let Q := g.inputs.toFinset.filter (·<w)
    refine ⟨Q,?_,?_,?_⟩
    · intro r hr
      obtain ⟨hm,early⟩ := Finset.mem_filter.mp hr
      refine ⟨early,?_⟩
      by_contra! yes
      have out : value C (neg s) w=true := by
        rw [eqv,op]
        apply List.any_eq_true.mpr
        exact ⟨_,List.mem_map.mpr ⟨r,List.mem_toFinset.mp hm,rfl⟩,by simpa [early] using yes⟩
      simp [hf] at out
    · intro p hp
      obtain ⟨hm,tr⟩ := Finset.mem_filter.mp hp
      rw [eqv,op] at tr
      obtain ⟨b,hm',yes⟩ := List.any_eq_true.mp tr
      obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hm'
      change (if r<w then value C (pos s p) r else false)=true at yes
      have early : r<w := by by_contra no; simp [no] at yes
      exact Finset.mem_biUnion.mpr ⟨r,Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr,early⟩,
        Finset.mem_filter.mpr ⟨hm,by simpa [early] using yes⟩⟩
    · simpa [cost] using (Finset.card_filter_le _ _).trans ((List.toFinset_card_le g.inputs).trans hl)


theorem frontier {α : Type*} [DecidableEq α] (S : ℕ → Finset α) (G : Finset ℕ)
    (usable : ℕ → Prop)
    (step : ∀ w, usable w → 2 ≤ (S w).card →
      ∃ Q : Finset ℕ, (∀ r∈Q, r<w ∧ usable r) ∧ S w ⊆ Q.biUnion S ∧
        Q.card ≤ if w∈G then 2 else 1)
    (t : ℕ) (F : Finset ℕ) (good : ∀ w∈F, usable w)
    (early : ∀ w∈F, 2≤(S w).card → w<t) :
    (F.biUnion S).card ≤ F.card + (G.filter (·<t)).card := by
  classical
  induction t generalizing F with
  | zero =>
    have small : ∀ w∈F, (S w).card ≤ 1 := by
      intro w hw
      by_contra! big
      exact Nat.not_lt_zero _ (early w hw big)
    simpa using Finset.card_biUnion_le_card_mul F S 1 small
  | succ t ih =>
    by_cases expand : t∈F ∧ 2≤(S t).card
    · obtain ⟨Q,valid,cover,budget⟩ := step t (good t expand.1) expand.2
      let R := F.erase t ∪ Q
      have validR : ∀ r∈R, usable r := by
        intro r hr
        rcases Finset.mem_union.mp hr with hr|hr
        · exact good r (Finset.mem_of_mem_erase hr)
        · exact (valid r hr).2
      have earlyR : ∀ r∈R, 2≤(S r).card → r<t := by
        intro r hr big
        rcases Finset.mem_union.mp hr with hr|hr
        · obtain ⟨ne,mem⟩ := Finset.mem_erase.mp hr
          have := early r mem big
          omega
        · exact (valid r hr).1
      have sub : F.biUnion S ⊆ R.biUnion S := by
        intro x hx
        obtain ⟨r,hr,hx⟩ := Finset.mem_biUnion.mp hx
        by_cases eq : r=t
        · subst r
          obtain ⟨v,hv,hx⟩ := Finset.mem_biUnion.mp (cover hx)
          exact Finset.mem_biUnion.mpr ⟨v,Finset.mem_union_right _ hv,hx⟩
        · exact Finset.mem_biUnion.mpr ⟨r,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨eq,hr⟩),hx⟩
      have c1 := Finset.card_le_card sub
      have c2 := ih R validR earlyR
      have c3 := Finset.card_union_le (F.erase t) Q
      change R.card ≤ _ at c3
      have c4 := Finset.card_erase_add_one expand.1
      by_cases paid : t∈G
      · have e : G.filter (·<t+1) = insert t (G.filter (·<t)) := by
          ext w
          simp only [Finset.mem_filter,Finset.mem_insert]
          constructor
          · rintro ⟨hg,hw⟩
            by_cases h : w=t
            · exact Or.inl h
            · exact Or.inr ⟨hg,by omega⟩
          · rintro (rfl|⟨hg,hw⟩)
            · exact ⟨paid,by omega⟩
            · exact ⟨hg,by omega⟩
        rw [e,Finset.card_insert_of_notMem (by simp)]
        simp [paid] at budget
        omega
      · have le := Finset.card_le_card (show G.filter (·<t) ⊆ G.filter (·<t+1) from
          fun w hw => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw).1,by have := (Finset.mem_filter.mp hw).2;omega⟩)
        simp [paid] at budget
        omega
    · have E : ∀ w∈F, 2≤(S w).card → w<t := by
        intro w hw big
        have := early w hw big
        by_contra! bad
        have e : w=t := by omega
        exact expand (e ▸ ⟨hw,big⟩)
      have le := Finset.card_le_card (show G.filter (·<t) ⊆ G.filter (·<t+1) from
        fun w hw => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw).1,by have := (Finset.mem_filter.mp hw).2;omega⟩)
      have := ih F good E
      omega


theorem countLine (C : Circuit) (hG : Good C) (o : V → ℕ)
    (evalOn : ∀ s x, dom x → value C x (o s) = decide (∃ p ∈ line s, x p=true))
    (s : V) (hs : s ≠ 0) : 3 ≤ (marked C s).card := by
  classical
  have hn : dom (neg s) := Or.inr ⟨s,fun p h => by simpa [neg] using h⟩
  have off : value C (neg s) (o s)=false := by rw [evalOn s _ hn]; simp [neg]
  have full : covered C s (o s) = line s := by
    apply Finset.filter_eq_self.mpr
    intro p hp
    rw [evalOn s _ (geometry s hs p hp).2]
    exact decide_eq_true ⟨p,hp,by simp [pos]⟩
  have bound := frontier (covered C s) (charged C s) (fun w => value C (neg s) w=false)
    (parents C hG s hs) (o s+1) {o s}
    (by intro w hw; simpa only [Finset.mem_singleton.mp hw] using off)
    (by intro w hw _; rw [Finset.mem_singleton.mp hw]; omega)
  simp only [Finset.singleton_biUnion,full,lineCard,Finset.card_singleton] at bound
  have h1 := Finset.card_filter_le (charged C s) (·<o s+1)
  have h2 := Finset.card_image_le (s := marked C s) (f := (13+·))
  change (charged C s).card ≤ _ at h2
  omega

theorem hitOther (C : Circuit) (hG : Good C) (s t : V) (ne : s≠t) (w : ℕ)
    (large : 2≤(covered C s w).card) (off : value C (neg t) w=false) :
    ∃ p ∈ line s \ line t, (extra s p ∩ line t).Nonempty := by
  classical
  have ex : ∃ p∈covered C s w, p∉line t := by
    by_contra! all
    have sub : covered C s w ⊆ line s ∩ line t :=
      fun p hp => Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hp).1,all p hp⟩
    have a := Finset.card_le_card sub
    have b := lineMeet s t ne
    omega
  obtain ⟨p,hp,pt⟩ := ex
  obtain ⟨ps,tr⟩ := Finset.mem_filter.mp hp
  refine ⟨p,Finset.mem_sdiff.mpr ⟨ps,pt⟩,?_⟩
  by_contra no
  have le (v : V) (hv : pos s p v=true) : neg t v=true := by
    have h : v=p ∨ v∈extra s p := of_decide_eq_true hv
    apply decide_eq_true
    intro inside
    rcases h with rfl|h
    · exact pt inside
    · exact no ⟨v,Finset.mem_inter.mpr ⟨h,inside⟩⟩
  have := value_mono C hG _ _ le w tr
  simp [off] at this

def owners (C : Circuit) (s : V) : Finset (Fin C.size) :=
  Finset.univ.filter fun j => j.val ∈ marked C s

theorem owners_size (C : Circuit) (s : V) : (owners C s).card = (marked C s).card := by
  have eq : (owners C s).image Fin.val = marked C s := by
    ext j
    constructor
    · intro h
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp h
      exact (Finset.mem_filter.mp ha).2
    · intro h
      have lt := Finset.mem_range.mp (Finset.mem_filter.mp h).1
      exact Finset.mem_image.mpr ⟨⟨j,lt⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩,rfl⟩
  rw [← eq,Finset.card_image_of_injective _ Fin.val_injective]

theorem owners_disjoint (C : Circuit) (hG : Good C) (s t : V) (hs : s≠0) (ht : t≠0) (ne : s≠t) :
    Disjoint (owners C s) (owners C t) := by
  apply Finset.disjoint_left.mpr
  intro j js jt
  have a := (Finset.mem_filter.mp ((Finset.mem_filter.mp js).2)).2
  have b := (Finset.mem_filter.mp ((Finset.mem_filter.mp jt).2)).2
  exact separated s t hs ht ne ⟨hitOther C hG s t ne _ a.2.2 b.2.1,
    hitOther C hG t s ne.symm _ b.2.2 a.2.1⟩

theorem owners_spec (C : Circuit) (s : V) (j : Fin C.size) (hj : j∈owners C s) :
    (C.gates.get j).op=GateOp.or ∧ value C (neg s) (13+j.val)=false := by
  have a := (Finset.mem_filter.mp ((Finset.mem_filter.mp hj).2)).2
  refine ⟨?_,a.2.1⟩
  have lookup : C.gates[j.val]? = some (C.gates.get j) := by
    rw [List.getElem?_eq_getElem j.isLt]
    rfl
  apply orOp_only
  have e : orAt C j.val = true := a.1
  unfold orAt at e
  rw [lookup] at e
  exact e

theorem selectOwners {β : Type*} [DecidableEq β] (B : V → Finset β)
    (enough : ∀ s : V, s≠0 → 3≤(B s).card)
    (sep : ∀ s t : V, s≠0 → t≠0 → s≠t → Disjoint (B s) (B t)) :
    ∃ (K : Finset β) (f : β → V), K.card=36 ∧ (∀ j∈K, f j≠0 ∧ j∈B (f j)) ∧
      ∀ s : V, s≠0 → (K.filter fun j => f j=s).card=3 := by
  classical
  have pick (s : V) : ∃ A ⊆ B s, s≠0 → A.card=3 := by
    by_cases hs : s=0
    · exact ⟨∅,Finset.empty_subset _,fun no => (no hs).elim⟩
    · obtain ⟨A,hA,sz⟩ := Finset.exists_subset_card_eq (enough s hs)
      exact ⟨A,hA,fun _ => sz⟩
  choose A incl size using pick
  let R : Finset V := Finset.univ.erase 0
  have nonzero {s : V} : s∈R ↔ s≠0 := by simp [R]
  have dis : (R : Set V).PairwiseDisjoint A := by
    intro s hs t ht ne
    exact Finset.disjoint_left.mpr fun j js jt => Finset.disjoint_left.mp
      (sep s t (nonzero.mp hs) (nonzero.mp ht) ne) (incl s js) (incl t jt)
  let K := R.biUnion A
  let f (j : β) : V := if h : j∈K then (Finset.mem_biUnion.mp (show j∈R.biUnion A from h)).choose else 0
  have assigned (j : β) (hj : j∈K) : f j∈R ∧ j∈A (f j) := by
    simpa only [f,dite_eq_left hj] using (Finset.mem_biUnion.mp (show j∈R.biUnion A from hj)).choose_spec
  have cardR : R.card=12 := by decide
  refine ⟨K,f,?_,fun j hj => ⟨nonzero.mp (assigned j hj).1,incl _ (assigned j hj).2⟩,?_⟩
  · calc
      K.card = ∑ s∈R, (A s).card := Finset.card_biUnion dis
      _ = ∑ _s∈R, (3 : ℕ) := Finset.sum_congr rfl (fun s hs => size s (nonzero.mp hs))
      _ = 36 := by simp [cardR]
  · intro s hs
    have eq : K.filter (fun j => f j=s) = A s := by
      ext j
      constructor
      · intro h
        obtain ⟨mem,tag⟩ := Finset.mem_filter.mp h
        simpa only [← tag] using (assigned j mem).2
      · intro mem
        have hj : j∈K := Finset.mem_biUnion.mpr ⟨s,nonzero.mpr hs,mem⟩
        refine Finset.mem_filter.mpr ⟨hj,?_⟩
        by_contra ne
        exact Finset.disjoint_left.mp (dis (assigned j hj).1 (nonzero.mpr hs) ne) (assigned j hj).2 mem
    rw [eq,size s hs]

end PEqualNP.Outside.L_meta_1523_aux

open PEqualNP.Outside.L_meta_1523_aux in

theorem PEqualNP.Outside.L_meta_1523 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    (∀ s : Fin 13, s ≠ 0 → ∀ p ∈ L s, (if p ∈ ({0, 1, 3} : Finset (Fin 13)) then (∅ : Finset (Fin 13)) else if (0 : Fin 13) ∈ L s then {1} else if (1 : Fin 13) ∈ L s then {3} else {0}) ∩ L s = ∅ ∧
      ((∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), (fun v : Fin 13 => decide (v = p ∨ v ∈ (if p ∈ ({0, 1, 3} : Finset (Fin 13)) then (∅ : Finset (Fin 13)) else if (0 : Fin 13) ∈ L s then {1} else if (1 : Fin 13) ∈ L s then {3} else {0}))) v = true) ∨ ∃ s : Fin 13, ∀ v : Fin 13, (fun v : Fin 13 => decide (v = p ∨ v ∈ (if p ∈ ({0, 1, 3} : Finset (Fin 13)) then (∅ : Finset (Fin 13)) else if (0 : Fin 13) ∈ L s then {1} else if (1 : Fin 13) ∈ L s then {3} else {0}))) v = false → v ∈ L s)) ∧
    (∀ s s' : Fin 13, s ≠ 0 → s' ≠ 0 → s ≠ s' →
      ¬ ((∃ p ∈ L s \ L s', ((if p ∈ ({0, 1, 3} : Finset (Fin 13)) then (∅ : Finset (Fin 13)) else if (0 : Fin 13) ∈ L s then {1} else if (1 : Fin 13) ∈ L s then {3} else {0}) ∩ L s').Nonempty) ∧ (∃ p ∈ L s' \ L s, ((if p ∈ ({0, 1, 3} : Finset (Fin 13)) then (∅ : Finset (Fin 13)) else if (0 : Fin 13) ∈ L s' then {1} else if (1 : Fin 13) ∈ L s' then {3} else {0}) ∩ L s).Nonempty))) ∧
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin 13 → ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
    (∀ (t : Fin 13) (x : Fin 13 → Bool), ((∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), x v = true) ∨ ∃ s : Fin 13, ∀ v : Fin 13, x v = false → v ∈ L s) →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    ∃ (K : Finset (Fin gates.length)) (f : Fin gates.length → Fin 13), K.card = 36 ∧
      (∀ g ∈ K, (gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ f g ≠ 0 ∧
        PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (g : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L (f g)))) = false) ∧
      (∀ s : Fin 13, s ≠ 0 → (K.filter (fun g => f g = s)).card = 3) ∧
      (∀ g ∈ K, ¬ ∀ s : Fin 13, s ≠ 0 →
        PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (g : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L s))) = true) := by
  intro L hL
  have eq : L = line := funext hL
  subst L
  refine ⟨?_,separated,?_⟩
  · intro s hs p hp
    exact ⟨(geometry s hs p hp).1,Or.inl (pos_hot s p)⟩
  intro gates o hg he
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨gates,0⟩
  have good : Good C := hg
  have computes : ∀ s x, dom x → value C x (o s) = decide (∃ p∈line s, x p=true) := he
  obtain ⟨K,f,size,mem,fibers⟩ := selectOwners (owners C)
    (fun s hs => by rw [owners_size]; exact countLine C good o computes s hs)
    (owners_disjoint C good)
  refine ⟨K,f,size,?_,fibers,?_⟩
  · intro j hj
    obtain ⟨hs,own⟩ := mem j hj
    obtain ⟨op,off⟩ := owners_spec C _ _ own
    exact ⟨op,hs,off⟩
  · intro j hj all
    obtain ⟨hs,own⟩ := mem j hj
    have off := (owners_spec C _ _ own).2
    have on : value C (neg (f j)) (13+j.val)=true := all (f j) hs
    simp [off] at on
