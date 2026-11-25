import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1031.FreshMixed

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


abbrev Quad := Fin 2 → Fin 2 → Bool

abbrev PureQ (q : Quad) : Prop :=
  (∀ i j, q i j = q i 0) ∨ (∀ i j, q i j = q 0 j)

def diagQ : Quad := fun i j => decide (i = j)
def p4Q : Quad := fun i j => decide (i = 1 ∨ j = 0)
def zeroQ : Quad := fun _ _ => false
def oneQ : Quad := fun _ _ => true

lemma zeroPure : PureQ zeroQ := Or.inl (fun _ _ => rfl)
lemma onePure : PureQ oneQ := Or.inl (fun _ _ => rfl)
lemma diagMix : ¬ PureQ diagQ := by decide
lemma p4Mix : ¬ PureQ p4Q := by decide

def qEval (op : GateOp) (l : List Quad) : Quad :=
  fun i j => op.eval (l.map fun q => q i j)

def otherQ (i : Fin 2) : Fin 2 := if i=0 then 1 else 0

lemma otherQ_ne (i : Fin 2) : i ≠ otherQ i := by fin_cases i <;> decide

lemma pureDiagElim (op : Bool) (p q : Quad) (hp : PureQ p)
    (h : qEval (if op then GateOp.and else GateOp.or) [p,q] = diagQ) : q = diagQ := by
  cases op with
  | false =>
    have hz (i j : Fin 2) (hij : i ≠ j) : p i j = false := by
      have hq := congrFun (congrFun h i) j
      simp [qEval, GateOp.eval, diagQ, hij] at hq
      exact hq.1
    have hx (i j : Fin 2) : p i j = false := by
      rcases hp with hr | hc
      · rw [hr i j, ← hr i (otherQ i)]
        exact hz i _ (otherQ_ne i)
      · rw [hc i j, ← hc (otherQ j) j]
        exact hz _ j (Ne.symm (otherQ_ne j))
    funext i j
    simpa [qEval, GateOp.eval, hx] using congrFun (congrFun h i) j
  | true =>
    have hz (i : Fin 2) : p i i = true := by
      have hq := congrFun (congrFun h i) i
      simp [qEval, GateOp.eval, diagQ] at hq
      exact hq.1
    have hx (i j : Fin 2) : p i j = true := by
      rcases hp with hr | hc
      · rw [hr i j, ← hr i i]
        exact hz _
      · rw [hc i j, ← hc j j]
        exact hz _
    funext i j
    simpa [qEval, GateOp.eval, hx] using congrFun (congrFun h i) j

lemma diagTwo (op : Bool) (p q : Quad)
    (h : qEval (if op then GateOp.and else GateOp.or) [p,q] = diagQ)
    (hp : p ≠ diagQ) (hq : q ≠ diagQ) : ¬PureQ p ∧ ¬PureQ q ∧ p ≠ q := by
  have hcomm : qEval (if op then GateOp.and else GateOp.or) [q,p] =
      qEval (if op then GateOp.and else GateOp.or) [p,q] := by
    funext i j
    cases op <;> simp [qEval, GateOp.eval, Bool.and_comm, Bool.or_comm]
  refine ⟨fun hs => hq (pureDiagElim op p q hs h),
    fun hs => hp (pureDiagElim op q p hs (hcomm.trans h)), ?_⟩
  rintro rfl
  apply hp
  have hid : qEval (if op then GateOp.and else GateOp.or) [p,p] = p := by
    funext i j
    cases op <;> simp [qEval, GateOp.eval]
  exact hid.symm.trans h

lemma qZero (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) :
    PureQ (qEval op []) := by
  rcases hop with rfl | rfl <;> exact Or.inl (fun _ _ => rfl)

lemma qOne (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (q : Quad) :
    qEval op [q] = q := by
  rcases hop with rfl | rfl <;> ext i j <;> simp [qEval, GateOp.eval]

lemma diagBirth {op : GateOp} {l : List Quad} (hop : op = GateOp.and ∨ op = GateOp.or)
    (hlen : l.length ≤ 2) (hno : ∀ q ∈ l, q ≠ diagQ) (hv : qEval op l = diagQ) :
    ∃ p ∈ l, ∃ q ∈ l, ¬PureQ p ∧ ¬PureQ q ∧ p ≠ q := by
  rcases l with _ | ⟨p, l⟩
  · exact (diagMix (hv ▸ qZero op hop)).elim
  rcases l with _ | ⟨q, l⟩
  · exact (hno p (by simp) ((qOne op hop p).symm.trans hv)).elim
  have hl : l = [] := by simpa using hlen
  subst l
  refine ⟨p, by simp, q, by simp, ?_⟩
  rcases hop with rfl | rfl
  · exact diagTwo true p q hv (hno p (by simp)) (hno q (by simp))
  · exact diagTwo false p q hv (hno p (by simp)) (hno q (by simp))

lemma oneReader {op : GateOp} {l : List Quad} (hop : op = GateOp.and ∨ op = GateOp.or)
    (hlen : l.length ≤ 2) (hmem : oneQ ∈ l) :
    PureQ (qEval op l) ∨ qEval op l ∈ l := by
  rcases l with _ | ⟨p, l⟩
  · simp at hmem
  rcases l with _ | ⟨q, l⟩
  · exact Or.inr (by simp [qOne op hop p])
  have hl : l = [] := by simpa using hlen
  subst l
  rcases List.mem_cons.mp hmem with h | h
  · subst p
    rcases hop with rfl | rfl
    · right
      have hq : qEval GateOp.and [oneQ, q] = q := by ext i j; simp [qEval, GateOp.eval, oneQ]
      simp [hq]
    · exact Or.inl (by left; intro i j; simp [qEval, GateOp.eval, oneQ])
  · obtain rfl : oneQ = q := by simpa using h
    rcases hop with rfl | rfl
    · right
      have hp : qEval GateOp.and [p, oneQ] = p := by ext i j; simp [qEval, GateOp.eval, oneQ]
      simp [hp]
    · exact Or.inl (by left; intro i j; simp [qEval, GateOp.eval, oneQ])

def wireQ {n : ℕ} (C : Circuit) (x : Fin 2 → Fin 2 → Fin n → Bool) (u : ℕ) : Quad :=
  fun i j => val C (List.ofFn (x i j)) u

def srcQ {n : ℕ} (C : Circuit) (x : Fin 2 → Fin 2 → Fin n → Bool) (k u : ℕ) : Quad :=
  if u < n + k then wireQ C x u else zeroQ

lemma gateQ {n : ℕ} (C : Circuit) (x : Fin 2 → Fin 2 → Fin n → Bool) {k : ℕ}
    (hk : k < C.size) : wireQ C x (n+k) =
      qEval (gateAt C k).op ((gateAt C k).inputs.map (srcQ C x k)) := by
  funext i j
  rw [show wireQ C x (n+k) i j = _ from
    val_gate (n := n) (C := C) (x := List.ofFn (x i j)) (by simp) hk]
  simp only [qEval, List.map_map]
  congr 1
  apply List.map_congr_left
  intro u _
  by_cases hu : u < n+k <;> simp [srcQ, hu, wireQ, zeroQ]

lemma srcQ_old {n : ℕ} {C : Circuit} {x : Fin 2 → Fin 2 → Fin n → Bool} {k : ℕ}
    {q : Quad} (h : q ∈ (gateAt C k).inputs.map (srcQ C x k)) (hm : ¬ PureQ q) :
    ∃ u < n+k, wireQ C x u = q := by
  obtain ⟨u, _, rfl⟩ := List.mem_map.mp h
  by_cases hu : u < n+k
  · exact ⟨u, hu, by simp [srcQ, hu]⟩
  · exact (hm (by simpa [srcQ, hu] using zeroPure)).elim

lemma before_gate {n : ℕ} (C : Circuit) (x : Fin 2 → Fin 2 → Fin n → Bool)
    (hraw : ∀ i : Fin n, PureQ (fun a b => x a b i))
    {u : ℕ} (hm : ¬ PureQ (wireQ C x u)) : n ≤ u ∧ u < n + C.size := by
  constructor
  · by_contra! hu
    apply hm
    have he : wireQ C x u = fun a b => x a b ⟨u, hu⟩ := by
      ext a b
      rw [wireQ, val_input (n := n) (by simp) hu]
      simp [List.getD_eq_getElem?_getD, hu]
    rw [he]
    exact hraw _
  · by_contra! hu
    apply hm
    have he : wireQ C x u = zeroQ := by
      ext a b
      exact val_ge (C := C) (n := n) (by simp) hu
    rw [he]
    exact zeroPure

abbrev AO2 (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

def oldReader {n : ℕ} (C : Circuit) (x : Fin 2 → Fin 2 → Fin n → Bool) (r : ℕ) : Prop :=
  PureQ (wireQ C x (n+r)) ∨ ∃ u < n+r, wireQ C x u = wireQ C x (n+r)

lemma actual_reader {n : ℕ} (C : Circuit) (x : Fin 2 → Fin 2 → Fin n → Bool)
    (ha : AO2 C) {r s : ℕ} (hr : r < C.size) (hs : s < n+r)
    (hmem : s ∈ (gateAt C r).inputs) (hone : wireQ C x s = oneQ) : oldReader C x r := by
  obtain ⟨hop, hlen⟩ := ha _ (gateAt_mem hr)
  have hsr : oneQ ∈ (gateAt C r).inputs.map (srcQ C x r) :=
    List.mem_map.mpr ⟨s, hmem, by simp [srcQ, hs, hone]⟩
  have hb := oneReader hop (by simpa using hlen) hsr
  rw [← gateQ C x hr] at hb
  rcases hb with h | h
  · exact Or.inl h
  · by_cases hp : PureQ (wireQ C x (n+r))
    · exact Or.inl hp
    · exact Or.inr (srcQ_old h hp)

def pool (C : Circuit) (S : Finset ℕ) : Finset ℕ :=
  Finset.range C.size \ S

lemma mixed_index {n : ℕ} (C : Circuit) (x : Fin 2 → Fin 2 → Fin n → Bool)
    (hraw : ∀ i : Fin n, PureQ (fun a b => x a b i)) (S : Finset ℕ)
    (hS : ∀ k ∈ S, PureQ (wireQ C x (n+k))) {r : ℕ} (hread : oldReader C x r)
    {q : Quad} (hm : ¬ PureQ q) (hex : ∃ u, wireQ C x u = q) :
    ∃ k ∈ pool C S, k ≠ r ∧ wireQ C x (n+k) = q := by
  classical
  let u := Nat.find hex
  have hu : wireQ C x u = q := Nat.find_spec hex
  have huMix : ¬PureQ (wireQ C x u) := hu ▸ hm
  obtain ⟨hlo, hhi⟩ := before_gate C x hraw huMix
  let k := u - n
  have hk : n+k = u := by dsimp [k]; omega
  refine ⟨k, Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩, ?_, hk ▸ hu⟩
  · intro hs
    exact huMix (hk ▸ hS k hs)
  · intro heq
    unfold oldReader at hread
    rw [← heq, hk] at hread
    rcases hread with h | ⟨v, hv, he⟩
    · exact huMix h
    · exact Nat.find_min hex hv (he.trans hu)

lemma diag_witnesses {n : ℕ} (C : Circuit) (x : Fin 2 → Fin 2 → Fin n → Bool)
    (ha : AO2 C) (hraw : ∀ i : Fin n, PureQ (fun a b => x a b i))
    (hex : ∃ u, wireQ C x u = diagQ) :
    ∃ p q : Quad, ¬ PureQ p ∧ ¬ PureQ q ∧ p ≠ q ∧ p ≠ diagQ ∧ q ≠ diagQ ∧
      (∃ u, wireQ C x u = p) ∧ (∃ u, wireQ C x u = q) := by
  classical
  let u := Nat.find hex
  have hu : wireQ C x u = diagQ := Nat.find_spec hex
  obtain ⟨hlo, hhi⟩ := before_gate C x hraw (hu ▸ diagMix)
  let k := u - n
  have hk : n+k = u := by dsimp [k]; omega
  have hks : k < C.size := by omega
  obtain ⟨hop, hlen⟩ := ha _ (gateAt_mem hks)
  have hdiag := (gateQ C x hks).symm.trans (hk ▸ hu)
  have hno (a : Quad) (ha' : a ∈ (gateAt C k).inputs.map (srcQ C x k)) : a ≠ diagQ := by
    rintro rfl
    obtain ⟨v, hv, he⟩ := srcQ_old ha' diagMix
    exact Nat.find_min hex (by rwa [hk] at hv) he
  obtain ⟨p, hp, q, hq, hm, hn, hpq⟩ := diagBirth hop (by simpa using hlen) hno hdiag
  obtain ⟨v, _, hv⟩ := srcQ_old hp hm
  obtain ⟨w, _, hw⟩ := srcQ_old hq hn
  exact ⟨p,q,hm,hn,hpq,hno p hp,hno q hq,⟨v,hv⟩,⟨w,hw⟩⟩

lemma mixed_output_cost {n : ℕ} (C : Circuit) (x : Fin 2 → Fin 2 → Fin n → Bool)
    (ha : AO2 C) (hraw : ∀ i : Fin n, PureQ (fun a b => x a b i))
    (S : Finset ℕ) (hS : ∀ k ∈ S, PureQ (wireQ C x (n+k))) {r s : ℕ}
    (hr : r < C.size) (hrS : r ∉ S) (hs : s < n+r) (hm : s ∈ (gateAt C r).inputs)
    (hone : wireQ C x s = oneQ)
    (hout : ¬ PureQ (fun a b => C.eval (List.ofFn (x a b)))) :
    2 ≤ (pool C S).card := by
  obtain ⟨k,hk,hkr,_⟩ := mixed_index C x hraw S hS (actual_reader C x ha hr hs hm hone)
    hout ⟨C.output,rfl⟩
  have hrr : r ∈ pool C S := Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr hr,hrS⟩
  have hsub : ({k,r} : Finset ℕ) ⊆ pool C S := by
    simp [Finset.insert_subset_iff, Finset.singleton_subset_iff, hk, hrr]
  simpa [hkr] using Finset.card_le_card hsub

lemma diagonal_output_cost {n : ℕ} (C : Circuit) (x : Fin 2 → Fin 2 → Fin n → Bool)
    (ha : AO2 C) (hraw : ∀ i : Fin n, PureQ (fun a b => x a b i))
    (S : Finset ℕ) (hS : ∀ k ∈ S, PureQ (wireQ C x (n+k))) {r s : ℕ}
    (hr : r < C.size) (hrS : r ∉ S) (hs : s < n+r) (hm : s ∈ (gateAt C r).inputs)
    (hone : wireQ C x s = oneQ)
    (hout : ∀ a b, C.eval (List.ofFn (x a b)) = decide (a=b)) :
    4 ≤ (pool C S).card := by
  classical
  have hd : ∃ u, wireQ C x u = diagQ := ⟨C.output,funext (fun i => funext (hout i))⟩
  obtain ⟨p,q,hp,hq,hpq,hpd,hqd,hexp,hexq⟩ := diag_witnesses C x ha hraw hd
  have hread := actual_reader C x ha hr hs hm hone
  obtain ⟨i,hi,hir,hei⟩ := mixed_index C x hraw S hS hread hp hexp
  obtain ⟨j,hj,hjr,hej⟩ := mixed_index C x hraw S hS hread hq hexq
  obtain ⟨k,hk,hkr,hek⟩ := mixed_index C x hraw S hS hread diagMix hd
  have hij : i ≠ j := by rintro rfl; exact hpq (hei.symm.trans hej)
  have hik : i ≠ k := by rintro rfl; exact hpd (hei.symm.trans hek)
  have hjk : j ≠ k := by rintro rfl; exact hqd (hej.symm.trans hek)
  have hrr : r ∈ pool C S := Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr hr,hrS⟩
  have hsub : ({i,j,k,r} : Finset ℕ) ⊆ pool C S := by
    simp [Finset.insert_subset_iff, Finset.singleton_subset_iff, hi, hj, hk, hrr]
  simpa [hij,hik,hir,hjk,hjr,hkr] using Finset.card_le_card hsub

def crossInput {n : ℕ} (left right : Fin 2 → Fin n) (a b : Fin 2) (v : Fin n) : Bool :=
  decide (v = left a ∨ v = right b)

lemma cross_raw_pure {n : ℕ} (left right : Fin 2 → Fin n) (hs : ∀ a b, left a ≠ right b)
    (v : Fin n) : PureQ (fun a b => crossInput left right a b v) := by
  by_cases h : ∃ a, v = left a
  · obtain ⟨a,rfl⟩ := h
    left
    intro i j
    simp [crossInput, hs]
  · right
    have hn (a) : v ≠ left a := fun he => h ⟨a, he⟩
    intro i j
    simp [crossInput, hn]

lemma p4_output_cost {n : ℕ} (C : Circuit) (left right : Fin 2 → Fin n)
    (hsep : ∀ a b, left a ≠ right b) (ha : AO2 C) (S : Finset ℕ)
    (hS : ∀ k ∈ S, PureQ (wireQ C (crossInput left right) (n+k))) {r t : ℕ}
    (hr : r < C.size) (hrS : r ∉ S) (ht : t < r) (hm : n+t ∈ (gateAt C r).inputs)
    (hone : wireQ C (crossInput left right) (n+t) = oneQ)
    (hout : ∀ a b, C.eval (List.ofFn (crossInput left right a b)) = p4Q a b) :
    2 ≤ (pool C S).card := by
  apply mixed_output_cost C _ ha (cross_raw_pure left right hsep) S hS hr hrS
    (Nat.add_lt_add_left ht n) hm hone
  have he := funext fun a => funext (hout a)
  exact he ▸ p4Mix

lemma matching_output_cost {n : ℕ} (C : Circuit) (left right : Fin 2 → Fin n)
    (hsep : ∀ a b, left a ≠ right b) (ha : AO2 C) (S : Finset ℕ)
    (hS : ∀ k ∈ S, PureQ (wireQ C (crossInput left right) (n+k))) {r t : ℕ}
    (hr : r < C.size) (hrS : r ∉ S) (ht : t < r) (hm : n+t ∈ (gateAt C r).inputs)
    (hone : wireQ C (crossInput left right) (n+t) = oneQ)
    (hout : ∀ a b, C.eval (List.ofFn (crossInput left right a b)) = decide (a=b)) :
    4 ≤ (pool C S).card :=
  diagonal_output_cost C _ ha (cross_raw_pure left right hsep) S hS hr hrS
    (Nat.add_lt_add_left ht n) hm hone hout

def ClosedInputs {n : ℕ} (C : Circuit) (T : Set ℕ) : Prop :=
  ∀ k < C.size, n+k ∈ T → ∀ i ∈ (gateAt C k).inputs, i < n+k → i ∈ T

lemma closed_eval_eq {n : ℕ} (C : Circuit) (T : Set ℕ) (ht : ClosedInputs (n := n) C T)
    (x y : Fin n → Bool) (hraw : ∀ i : Fin n, i.val ∈ T → x i = y i) :
    ∀ u ∈ T, val C (List.ofFn x) u = val C (List.ofFn y) u := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hu
    by_cases hi : u < n
    · rw [val_input (n:=n) (by simp) hi, val_input (n:=n) (by simp) hi]
      simpa [List.getD_eq_getElem?_getD,hi] using hraw ⟨u,hi⟩ hu
    by_cases hbound : n + C.size ≤ u
    · rw [val_ge (n:=n) (by simp) hbound, val_ge (n:=n) (by simp) hbound]
    let k := u - n
    have hk : n+k=u := by dsimp [k]; omega
    have hks : k < C.size := by omega
    rw [← hk] at hu ⊢
    rw [val_gate (n:=n) (by simp) hks, val_gate (n:=n) (by simp) hks]
    congr 1
    apply List.map_congr_left
    intro i him
    by_cases hv : i < n+k
    · simpa [hv] using ih i (by omega) (ht k hks hu i him hv)
    · simp [hv]

lemma separated_cones_pure {n : ℕ} (C : Circuit) (x : Fin 2 → Fin 2 → Fin n → Bool)
    (T U : Set ℕ) (hT : ClosedInputs (n:=n) C T) (hU : ClosedInputs (n:=n) C U)
    (hr : ∀ i : Fin n, i.val ∈ T → ∀ a b, x a b i = x a 0 i)
    (hc : ∀ i : Fin n, i.val ∈ U → ∀ a b, x a b i = x 0 b i)
    {s : ℕ} (hone : wireQ C x s = oneQ) (v : ℕ) (hv : v ∈ T ∨ v ∈ U ∨ v=s) :
    PureQ (wireQ C x v) := by
  rcases hv with h | h | rfl
  · exact Or.inl (fun a b => closed_eval_eq C T hT _ _ (fun i hi => hr i hi a b) v h)
  · exact Or.inr (fun a b => closed_eval_eq C U hU _ _ (fun i hi => hc i hi a b) v h)
  · exact hone ▸ onePure

def sharpSource : List Gate :=
  [⟨GateOp.or, [0,2]⟩, ⟨GateOp.or, [1,3]⟩, ⟨GateOp.and, [4,5]⟩]

def sharpP4 : Circuit :=
  ⟨sharpSource ++ [⟨GateOp.or, [1,2]⟩, ⟨GateOp.and, [6,7]⟩], 8⟩

def sharpMatching : Circuit :=
  ⟨sharpSource ++ [⟨GateOp.or, [0,3]⟩, ⟨GateOp.or, [1,2]⟩, ⟨GateOp.and, [7,8]⟩,
    ⟨GateOp.and, [6,9]⟩], 10⟩

def sharpInput := crossInput (n:=4) ![0,2] ![1,3]

lemma sharp_P4_profile : (∀ a b, sharpP4.eval (List.ofFn (sharpInput a b)) = p4Q a b) ∧
    (pool sharpP4 {0,1,2}).card = 2 ∧ (∀ a b, wireQ sharpP4 sharpInput 6 a b = true) ∧
    6 ∈ (gateAt sharpP4 4).inputs := by decide

lemma sharp_matching_profile :
    (∀ a b, sharpMatching.eval (List.ofFn (sharpInput a b)) = decide (a=b)) ∧
    (pool sharpMatching {0,1,2}).card = 4 ∧ (∀ a b, wireQ sharpMatching sharpInput 6 a b = true) ∧
    6 ∈ (gateAt sharpMatching 6).inputs := by decide

end PEqualNP.Outside.L_meta_1031.FreshMixed
