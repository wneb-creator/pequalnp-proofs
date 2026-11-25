import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_4799

abbrev Op := Fin 3
abbrev Spec := Op × ℕ × ℕ
abbrev Instr := ℕ × Spec
abbrev Trace := List Instr
abbrev State := ℕ → Bool

def get {α : Type} (ag og : α → α → α) (ng : α → α) (s : ℕ → α) (g : Spec) : α :=
  if g.1 = 0 then ag (s g.2.1) (s g.2.2)
  else if g.1 = 1 then og (s g.2.1) (s g.2.2)
  else ng (s g.2.1)

def args (g : Spec) : List ℕ :=
  if g.1 = 2 then [g.2.1] else [g.2.1, g.2.2]

def keys (p : Trace) : Finset ℕ := (p.map Prod.fst).toFinset
def uses (p : Trace) : List ℕ := p.flatMap (args ∘ Prod.snd)
def stock (p : Trace) (out : ℕ) : List ℕ := uses p ++ [out]
def base : Finset ℕ := Finset.range 8

def ok (s : Finset ℕ) : Trace → Prop
  | [] => True
  | g :: p => g.1 ∉ s ∧ (∀ i ∈ args g.2, i ∈ s) ∧ ok (insert g.1 s) p

def value : State → Spec → Bool := get (· && ·) (· || ·) (! ·)
def step (s : State) (g : Instr) : State := Function.update s g.1 (value s g.2)
def run (s : State) (p : Trace) : State := p.foldl step s

def initial (x : State) (i : ℕ) : Bool :=
  if i = 0 then false else if i = 1 then true else if i < 8 then x i else false

def cycle (x : State) : Bool :=
  x 2 && x 3 || x 2 && x 5 || x 3 && x 6 || x 4 && x 6 || x 5 && x 7 || x 4 && x 7

def computes (p : Trace) (out : ℕ) : Prop := ∀ x, run (initial x) p out = cycle x

lemma op_cases (o : Op) : o = 0 ∨ o = 1 ∨ o = 2 := by decide +revert

lemma arg_first (g : Spec) : g.2.1 ∈ args g := by
  unfold args
  split <;> simp

lemma arg_second (g : Spec) (h : g.1 ≠ 2) : g.2.2 ∈ args g := by
  simp [args, h]

lemma valueCongr (g : Spec) (u v : State) (h : ∀ i ∈ args g, u i = v i) :
    value u g = value v g := by
  have l := h _ (arg_first g)
  rcases op_cases g.1 with op | op | op
  · have r := h _ (arg_second g (by simp [op]))
    simp [value, get, op, l, r]
  · have r := h _ (arg_second g (by simp [op]))
    simp [value, get, op, l, r]
  · simp [value, get, op, l]

lemma okAppend (s : Finset ℕ) (p q : Trace) :
    ok s (p ++ q) ↔ ok s p ∧ ok (s ∪ keys p) q := by
  induction p generalizing s with
  | nil => simp [ok, keys]
  | cons g p ih =>
    have hkey : insert g.1 s ∪ keys p = s ∪ keys (g :: p) := by
      ext i
      simp [keys]
    simp only [List.cons_append, ok, ih, hkey]
    tauto

lemma noWrite (p : Trace) (s : Finset ℕ) (okp : ok s p) {i : ℕ} (hi : i ∈ s) : i ∉ keys p := by
  induction p generalizing s with
  | nil => simp [keys]
  | cons g p ih =>
    have h : i ≠ g.1 := fun e => okp.1 (e ▸ hi)
    have t := ih (insert g.1 s) okp.2.2 (Finset.mem_insert_of_mem hi)
    simpa [keys, h] using t

lemma cardKeys (p : Trace) (s : Finset ℕ) (okp : ok s p) : (keys p).card = p.length := by
  induction p generalizing s with
  | nil => simp [keys]
  | cons g p ih =>
    have miss := noWrite p (insert g.1 s) okp.2.2 (Finset.mem_insert_self _ _)
    have e : keys (g :: p) = insert g.1 (keys p) := by simp [keys]
    simp [e, Finset.card_insert_of_notMem miss, ih _ okp.2.2]

lemma ignores (p : Trace) (u v : State) (k : ℕ) (eq : ∀ i ≠ k, u i = v i)
    (noRead : k ∉ uses p) : ∀ j ≠ k, run u p j = run v p j := by
  induction p generalizing u v with
  | nil => exact eq
  | cons g p ih =>
    simp only [uses, List.flatMap_cons, Function.comp_apply, List.mem_append, not_or] at noRead
    have ev : value u g.2 = value v g.2 := valueCongr _ _ _ fun a ha =>
      eq a fun e => noRead.1 (e ▸ ha)
    apply ih _ _ _ noRead.2
    intro i hi
    by_cases e : i = g.1
    · simp [step, e, ev]
    · simpa only [step, Function.update_of_ne e] using eq i hi

lemma readMono (g : Spec) (u v : State) (bin : g.1 ≠ 2)
    (h : ∀ i ∈ args g, u i ≤ v i) : value u g ≤ value v g := by
  have l := h _ (arg_first g)
  have r := h _ (arg_second g bin)
  rcases op_cases g.1 with op | op | op
  · simp only [value, get, op, ite_true]
    revert l r
    cases u g.2.1 <;> cases v g.2.1 <;> cases u g.2.2 <;> cases v g.2.2 <;> decide
  · have n : (1 : Op) ≠ 0 := by decide
    simp only [value, get, op, n, ite_false, ite_true]
    revert l r
    cases u g.2.1 <;> cases v g.2.1 <;> cases u g.2.2 <;> cases v g.2.2 <;> decide
  · contradiction

lemma ignoresMono (p : Trace) (u v : State) (k : ℕ) (le : ∀ i ≠ k, u i ≤ v i)
    (noRead : k ∉ uses p) (bin : ∀ g ∈ p, g.2.1 ≠ 2) :
    ∀ j ≠ k, run u p j ≤ run v p j := by
  induction p generalizing u v with
  | nil => exact le
  | cons g p ih =>
    simp only [uses, List.flatMap_cons, Function.comp_apply, List.mem_append, not_or] at noRead
    have ev : value u g.2 ≤ value v g.2 := readMono _ _ _ (bin g (by simp)) fun a ha =>
      le a fun e => noRead.1 (e ▸ ha)
    apply ih _ _ _ noRead.2 (fun h hh => bin h (by simp [hh]))
    intro i hi
    by_cases e : i = g.1
    · simpa [step, e] using ev
    · simpa only [step, Function.update_of_ne e] using le i hi

def rewire (k a i : ℕ) : ℕ := if i = k then a else i
def redirect (k a : ℕ) (g : Instr) : Instr :=
  (g.1, g.2.1, rewire k a g.2.2.1, rewire k a g.2.2.2)

lemma redirectArgs (g : Instr) (k a : ℕ) :
    args (redirect k a g).2 = (args g.2).map (rewire k a) := by
  unfold args redirect
  split <;> rfl

lemma redirectKeys (p : Trace) (k a : ℕ) : keys (p.map (redirect k a)) = keys p := by
  simp [keys, List.map_map, redirect, Function.comp_def]

lemma redirectValue (g : Instr) (k a : ℕ) (s : State) :
    value s (redirect k a g).2 = value (s ∘ rewire k a) g.2 := rfl

lemma redirectMem (s t : Finset ℕ) (k a : ℕ) (h : s ⊆ t) (ha : a ∈ t)
    (j : ℕ) (hj : j ∈ insert k s) : rewire k a j ∈ t := by
  by_cases e : j = k
  · simp [rewire, e, ha]
  · simpa [rewire, e] using h ((Finset.mem_insert.mp hj).resolve_left e)

lemma redirectGood (p : Trace) (s : Finset ℕ) (k a : ℕ) (ha : a ∈ s)
    (hp : ok (insert k s) p) : ok s (p.map (redirect k a)) := by
  induction p generalizing s with
  | nil => trivial
  | cons g p ih =>
    have fresh : g.1 ∉ s := fun h => hp.1 (Finset.mem_insert_of_mem h)
    have wr : ∀ j ∈ args (redirect k a g).2, j ∈ s := by
      intro j hj
      rw [redirectArgs] at hj
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
      exact redirectMem s s k a (fun _ h => h) ha i (hp.2.1 i hi)
    refine ⟨fresh, wr, ih (insert g.1 s) (Finset.mem_insert_of_mem ha) ?_⟩
    rw [Finset.insert_comm]
    exact hp.2.2

lemma ignoreGood (p : Trace) (s : Finset ℕ) (k : ℕ) (hp : ok (insert k s) p)
    (nk : k ∉ uses p) : ok s p := by
  induction p generalizing s with
  | nil => trivial
  | cons g p ih =>
    simp only [uses, List.flatMap_cons, Function.comp_apply, List.mem_append, not_or] at nk
    refine ⟨fun h => hp.1 (Finset.mem_insert_of_mem h), ?_, ih (insert g.1 s) ?_ nk.2⟩
    · intro i hi
      exact (Finset.mem_insert.mp (hp.2.1 i hi)).resolve_left (fun e => nk.1 (e ▸ hi))
    · rw [Finset.insert_comm]
      exact hp.2.2

lemma runRedirect (p : Trace) (s : State) (k a : ℕ) (nk : k ∉ keys p) (na : a ∉ keys p) :
    run (s ∘ rewire k a) p = run s (p.map (redirect k a)) ∘ rewire k a := by
  induction p generalizing s with
  | nil => rfl
  | cons g p ih =>
    simp only [keys, List.map_cons, List.toFinset_cons, Finset.mem_insert, not_or] at nk na
    have e : step (s ∘ rewire k a) g = step s (redirect k a g) ∘ rewire k a := by
      funext j
      have f : rewire k a j = g.1 ↔ j = g.1 := by
        by_cases h : j = k
        · simp [rewire, h, nk.1, na.1]
        · simp [rewire, h]
      by_cases h : j = g.1
      · have r : rewire k a j = g.1 := f.mpr h
        change Function.update (s ∘ rewire k a) g.1 (value (s ∘ rewire k a) g.2) j =
          Function.update s g.1 (value s (redirect k a g).2) (rewire k a j)
        rw [r, Function.update_self, redirectValue]
        rw [h, Function.update_self]
      · have r : rewire k a j ≠ g.1 := fun H => h (f.mp H)
        simp [step, redirect, Function.update_of_ne h, Function.update_of_ne r]
    simpa only [run, List.foldl_cons, List.map_cons, e] using ih (step s (redirect k a g)) nk.2 na.2

def addr (n j : ℕ) : ℕ := if j < n then j + 2 else 0

def spec (n : ℕ) (g : Gate) : Spec :=
  match g.op with
  | .and => (0, (g.inputs[0]?).elim 1 (addr n), (g.inputs[1]?).elim 1 (addr n))
  | .or => (1, (g.inputs[0]?).elim 0 (addr n), (g.inputs[1]?).elim 0 (addr n))
  | .not => (2, (g.inputs[0]?).elim 0 (addr n), 0)
  | _ => (1, 0, 0)

def encode (n : ℕ) : List Gate → Trace
  | [] => []
  | g :: gs => (n + 2, spec n g) :: encode (n + 1) gs

def eligible (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

def bitsOn (s : State) (w : List Bool) : Prop :=
  s 0 = false ∧ s 1 = true ∧ ∀ i < w.length, s (i + 2) = w.getD i false

lemma addrRange (n j : ℕ) : addr n j ∈ Finset.range (n + 2) := by
  simp only [Finset.mem_range, addr]
  split <;> omega

lemma specRange (n : ℕ) (g : Gate) : ∀ i ∈ args (spec n g), i ∈ Finset.range (n + 2) := by
  intro i hi
  have default0 : 0 ∈ Finset.range (n + 2) := by simp
  have default1 : 1 ∈ Finset.range (n + 2) := Finset.mem_range.mpr (by omega)
  have h0 (z : Option ℕ) : z.elim 0 (addr n) ∈ Finset.range (n + 2) := by
    cases z with
    | none => exact default0
    | some j => exact addrRange n j
  have h1 (z : Option ℕ) : z.elim 1 (addr n) ∈ Finset.range (n + 2) := by
    cases z with
    | none => exact default1
    | some j => exact addrRange n j
  rcases g with ⟨op, ins⟩
  cases op <;> simp [spec, args] at hi
  all_goals rcases hi with rfl | rfl <;> first | exact h0 _ | exact h1 _ | exact default0

lemma encodeGood (n : ℕ) (gs : List Gate) : ok (Finset.range (n + 2)) (encode n gs) := by
  induction gs generalizing n with
  | nil => trivial
  | cons g gs ih =>
    have hset : insert (n + 2) (Finset.range (n + 2)) = Finset.range (n + 1 + 2) := by
      rw [← Finset.range_add_one]
    exact ⟨by simp, specRange n g, by rw [hset]; exact ih _⟩

lemma encodeLength (n : ℕ) (gs : List Gate) : (encode n gs).length = gs.length := by
  induction gs generalizing n with
  | nil => rfl
  | cons g gs ih => simp [encode, ih]

lemma encodeFinal (n : ℕ) (gs : List Gate) :
    Finset.range (n + 2) ∪ keys (encode n gs) = Finset.range (n + gs.length + 2) := by
  induction gs generalizing n with
  | nil => simp [encode, keys]
  | cons g gs ih =>
    have hkey : keys (encode n (g :: gs)) = insert (n + 2) (keys (encode (n+1) gs)) := by
      simp [encode, keys]
    rw [hkey, Finset.union_insert, ← Finset.insert_union, ← Finset.range_add_one]
    have hn : n + 2 + 1 = n + 1 + 2 := by omega
    rw [hn, ih]
    congr 1
    simp only [List.length_cons]
    omega

lemma addrValue (s : State) (w : List Bool) (h : bitsOn s w) (j : ℕ) :
    s (addr w.length j) = w.getD j false := by
  by_cases e : j < w.length
  · simpa [addr, e] using h.2.2 j e
  · simp [addr, e, h.1]

lemma specEval (s : State) (w : List Bool) (g : Gate) (h : bitsOn s w) (hg : eligible g) :
    value s (spec w.length g) = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  rcases g with ⟨op, ins⟩
  obtain ⟨allowed, len⟩ := hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at allowed
  rcases allowed with rfl | rfl | rfl <;> rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c,more⟩⟩⟩
  all_goals
    first
    | solve | simp at len
    | simp [spec, value, get, h.1, h.2.1, addrValue s w h, GateOp.eval]

def appendGate (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma replay (s : State) (w : List Bool) (gs : List Gate) (h : bitsOn s w)
    (hg : ∀ g ∈ gs, eligible g) :
    bitsOn (run s (encode w.length gs)) (gs.foldl appendGate w) := by
  induction gs generalizing s w with
  | nil => exact h
  | cons g gs ih =>
    have len : (appendGate w g).length = w.length + 1 := by simp [appendGate]
    have ev := specEval s w g h (hg g (by simp))
    let t : State := step s (w.length + 2, spec w.length g)
    have on : bitsOn t (appendGate w g) := by
      refine ⟨?_, ?_, ?_⟩
      · simpa [t, step, Function.update_of_ne (by omega : 0 ≠ w.length + 2)] using h.1
      · simpa [t, step, Function.update_of_ne (by omega : 1 ≠ w.length + 2)] using h.2.1
      · intro i hi
        by_cases e : i < w.length
        · have ne : i + 2 ≠ w.length + 2 := by omega
          rw [show t (i + 2) = s (i + 2) by simp [t, step, Function.update_of_ne ne]]
          rw [h.2.2 _ e]
          exact (List.getD_append _ _ _ _ e).symm
        · have eq : i = w.length := by rw [len] at hi; omega
          subst i
          simp [t, step, ev, appendGate]
    have rest := ih t (appendGate w g) on (fun q hq => hg q (by simp [hq]))
    simpa only [List.foldl_cons, encode, run, len] using rest

lemma foldLength (gs : List Gate) (w : List Bool) :
    (gs.foldl appendGate w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [appendGate]
    omega

lemma fromCircuit (C : Circuit) (fan : FanInTwo C)
    (fit : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = cycle (fun i => x ⟨(i-2)%6, by omega⟩)) :
    ∃ p out, p.length = C.size ∧ ok base p ∧ out ∈ base ∪ keys p ∧ computes p out := by
  let n := 6 + C.gates.length
  let o := addr n C.output
  refine ⟨encode 6 C.gates, o, encodeLength _ _, encodeGood _ _, ?_, ?_⟩
  · rw [base, show (8 : ℕ) = 6 + 2 by decide, encodeFinal]
    exact addrRange n C.output
  · intro x
    let y : Fin 6 → Bool := fun i => x (i.val + 2)
    let w := List.ofFn y
    have lengthW : w.length = 6 := List.length_ofFn
    have initialOn : bitsOn (initial x) w := by
      refine ⟨rfl, rfl, ?_⟩
      intro j hj
      rw [List.getD_eq_getElem _ _ hj]
      change initial x (j+2) = (List.ofFn y)[j]
      rw [List.getElem_ofFn]
      have lt : j + 2 < 8 := by omega
      simp [initial, y, show j+2 ≠ 1 by omega, lt]
    have endOn := replay (initial x) w C.gates initialOn fan
    rw [lengthW] at endOn
    have len : (C.gates.foldl appendGate w).length = n := by rw [foldLength, lengthW]
    change run (initial x) (encode 6 C.gates) o = cycle x
    have main := addrValue _ _ endOn C.output
    rw [len] at main
    rw [main]
    exact fit y

def shortest (p : Trace) : Prop :=
  ∀ q o, ok base q → o ∈ base ∪ keys q → computes q o → p.length ≤ q.length

lemma existsShortest (p : Trace) (o : ℕ) (hp : ok base p) (ho : o ∈ base ∪ keys p)
    (hc : computes p o) :
    ∃ q out, q.length ≤ p.length ∧ ok base q ∧ out ∈ base ∪ keys q ∧ computes q out ∧ shortest q := by
  classical
  let fits (n : ℕ) := ∃ (q : Trace) (out : ℕ), q.length = n ∧
    ok base q ∧ out ∈ base ∪ keys q ∧ computes q out
  have ex : ∃ n, fits n := ⟨p.length, p, o, rfl, hp, ho, hc⟩
  obtain ⟨q, out, qlen, hq, hout, fit⟩ := Nat.find_spec ex
  refine ⟨q, out, qlen.symm ▸ Nat.find_min' ex ⟨p, o, rfl, hp, ho, hc⟩, hq, hout, fit, ?_⟩
  intro v j hv hj hfit
  rw [qlen]
  exact Nat.find_min' ex ⟨v, j, rfl, hv, hj, hfit⟩

lemma keysAppend (p q : Trace) : keys (p ++ q) = keys p ∪ keys q := by
  simp [keys, List.toFinset_append]

lemma keysCons (g : Instr) (p : Trace) : keys (g :: p) = insert g.1 (keys p) := by
  simp [keys]

lemma usesAppend (p q : Trace) : uses (p ++ q) = uses p ++ uses q := by
  simp [uses, List.flatMap_append]

lemma usesCons (g : Instr) (p : Trace) : uses (g :: p) = args g.2 ++ uses p := by rfl

lemma runAppend (s : State) (p q : Trace) : run s (p ++ q) = run (run s p) q := by
  exact List.foldl_append

lemma runCons (s : State) (g : Instr) (p : Trace) : run s (g :: p) = run (step s g) p := by rfl

lemma liveKeys (p : Trace) (o : ℕ) (hp : ok base p) (ho : o ∈ base ∪ keys p)
    (fit : computes p o) (min : shortest p) : ∀ k ∈ keys p, k ∈ stock p o := by
  intro k hk
  by_contra dead
  obtain ⟨g, hg, hkey⟩ := List.mem_map.mp (List.mem_toFinset.mp hk)
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hg
  subst k
  let s := base ∪ keys pre
  obtain ⟨hpre, hs⟩ := (okAppend base pre (g :: post)).mp hp
  have htail : ok (insert g.1 s) post := hs.2.2
  have outNe : o ≠ g.1 := by
    intro e
    exact dead (by simp [stock, e])
  have notRead : g.1 ∉ uses post := by
    intro hg
    exact dead (by simp [stock, usesAppend, usesCons, hg])
  have keepOut : o ∈ base ∪ keys (pre ++ post) := by
    simp only [keysAppend, keysCons, Finset.mem_union, Finset.mem_insert] at ho ⊢
    tauto
  have small := min (pre ++ post) o ((okAppend _ _ _).mpr ⟨hpre, ignoreGood post s g.1 htail notRead⟩)
    keepOut (by
      intro x
      have q := fit x
      rw [runAppend, runCons] at q
      rw [runAppend, ← q]
      apply ignores post _ _ g.1 (fun i hi => ?_) notRead o outNe
      simp [step, Function.update_of_ne hi])
  simp at small

lemma firstCanReplace (g : Instr) (p : Trace) (o a : ℕ) (hp : ok base (g :: p))
    (ho : o ∈ base ∪ keys (g :: p)) (fit : computes (g :: p) o) (min : shortest (g :: p))
    (ha : a ∈ base) (hvalue : ∀ x, value (initial x) g.2 = initial x a) : False := by
  have out : rewire g.1 a o ∈ base ∪ keys (p.map (redirect g.1 a)) := by
    apply redirectMem (base ∪ keys p) (base ∪ keys (p.map (redirect g.1 a)))
    · simp only [redirectKeys]; exact fun _ h => h
    · exact Finset.mem_union_left _ ha
    · rwa [keysCons, Finset.union_insert] at ho
  have smaller := min (p.map (redirect g.1 a)) (rewire g.1 a o)
    (redirectGood p base g.1 a ha hp.2.2) out (by
      intro x
      have before : step (initial x) g = initial x ∘ rewire g.1 a := by
        funext i
        by_cases j : i = g.1
        · simp [step, j, rewire, hvalue]
        · simp [step, rewire, j]
      have eq := runRedirect p (initial x) g.1 a
        (noWrite p _ hp.2.2 (Finset.mem_insert_self _ _))
        (noWrite p _ hp.2.2 (Finset.mem_insert_of_mem ha))
      have orig := fit x
      rw [runCons, before, eq] at orig
      exact orig)
  simp at smaller

def raw : Finset ℕ := {2,3,4,5,6,7}

lemma rawRange {j : ℕ} : j ∈ raw ↔ 2 ≤ j ∧ j < 8 := by
  simp [raw]
  omega

lemma rawBase : raw ⊆ base := fun _ h => Finset.mem_range.mpr (rawRange.mp h).2

lemma initRaw (x : State) {i : ℕ} (h : i ∈ raw) : initial x i = x i := by
  obtain ⟨b, t⟩ := rawRange.mp h
  simp [initial, show i ≠ 0 by omega, show i ≠ 1 by omega, t]

lemma firstShape (g : Instr) (p : Trace) (o : ℕ) (hp : ok base (g :: p))
    (ho : o ∈ base ∪ keys (g :: p)) (fit : computes (g :: p) o) (min : shortest (g :: p)) :
    g.2.2.1 ∈ raw ∧ (g.2.1 ≠ 2 → g.2.2.2 ∈ raw ∧ g.2.2.1 ≠ g.2.2.2) := by
  have impossible (a : ℕ) := firstCanReplace g p o a hp ho fit min
  have aAvail : g.2.2.1 ∈ base := hp.2.1 _ (arg_first g.2)
  have bAvail (h : g.2.1 ≠ 2) : g.2.2.2 ∈ base := hp.2.1 _ (arg_second g.2 h)
  have rawOr (j : ℕ) (hj : j ∈ base) : j ∈ raw ∨ j = 0 ∨ j = 1 := by
    rw [rawRange]
    have lt := Finset.mem_range.mp hj
    omega
  have zero : 0 ∈ base := by decide
  have one : 1 ∈ base := by decide
  have h (op : g.2.1 = 0) : g.2.2.1 ∈ raw ∧ g.2.2.2 ∈ raw ∧ g.2.2.1 ≠ g.2.2.2 := by
    have bv := bAvail (by simp [op])
    refine ⟨?_, ?_, ?_⟩
    · rcases rawOr _ aAvail with yes | z | t
      · exact yes
      · exact False.elim (impossible 0 zero (by intro x; simp [value, get, op, z, initial]))
      · exact False.elim (impossible _ bv (by intro x; simp [value, get, op, t, initial]))
    · rcases rawOr _ bv with yes | z | t
      · exact yes
      · exact False.elim (impossible 0 zero (by intro x; simp [value, get, op, z, initial]))
      · exact False.elim (impossible _ aAvail (by intro x; simp [value, get, op, t, initial]))
    · intro e
      exact impossible _ aAvail (by intro x; simp [value, get, op, e])
  have j (op : g.2.1 = 1) : g.2.2.1 ∈ raw ∧ g.2.2.2 ∈ raw ∧ g.2.2.1 ≠ g.2.2.2 := by
    have bv := bAvail (by simp [op])
    refine ⟨?_, ?_, ?_⟩
    · rcases rawOr _ aAvail with yes | z | t
      · exact yes
      · exact False.elim (impossible _ bv (by intro x; simp [value, get, op, z, initial]))
      · exact False.elim (impossible 1 one (by intro x; simp [value, get, op, t, initial]))
    · rcases rawOr _ bv with yes | z | t
      · exact yes
      · exact False.elim (impossible _ aAvail (by intro x; simp [value, get, op, z, initial]))
      · exact False.elim (impossible 1 one (by intro x; simp [value, get, op, t, initial]))
    · intro e
      exact impossible _ aAvail (by intro x; simp [value, get, op, e])
  rcases op_cases g.2.1 with op | op | op
  · exact ⟨(h op).1, fun _ => (h op).2⟩
  · exact ⟨(j op).1, fun _ => (j op).2⟩
  · refine ⟨?_, fun e => (e op).elim⟩
    rcases rawOr _ aAvail with yes | z | t
    · exact yes
    · exact False.elim (impossible 1 one (by intro x; simp [value, get, op, z, initial]))
    · exact False.elim (impossible 0 zero (by intro x; simp [value, get, op, t, initial]))

def row (r : Fin 64) : State := fun i => r.val.testBit (i - 2)

def cofactorRow (i j : Fin 6) (b : Bool) : Fin 64 :=
  let rows : List (Fin 64) := if b then
    [0, 2, 6, 8, 24, 34, 1, 0, 5, 24, 16, 33, 17, 34, 0, 24, 16, 32,
     1, 34, 5, 0, 17, 32, 5, 2, 4, 10, 0, 34, 5, 6, 4, 8, 24, 0]
  else
    [0, 8, 2, 2, 2, 2, 16, 0, 1, 1, 1, 1, 16, 16, 0, 16, 32, 16,
     32, 1, 1, 0, 1, 1, 2, 4, 2, 2, 0, 2, 4, 4, 8, 4, 4, 0]
  rows.getD (6 * i.val + j.val) 0

set_option maxRecDepth 10000 in
lemma allCofactors : ∀ i j : Fin 6, i ≠ j → ∀ b : Bool,
    let r := cofactorRow i j b
    row r (j.val + 2) = b ∧
      cycle (Function.update (row r) (i.val + 2) false) = false ∧
      cycle (Function.update (row r) (i.val + 2) true) = true := by decide

lemma cofactor (a b : ℕ) (ha : a ∈ raw) (hb : b ∈ raw) (ne : a ≠ b) (c : Bool) :
    ∃ u v : State, u a = false ∧ v a = true ∧ u b = c ∧ v b = c ∧
      (∀ i ≠ a, u i = v i) ∧ cycle u = false ∧ cycle v = true := by
  have al := rawRange.mp ha
  have bl := rawRange.mp hb
  let i : Fin 6 := ⟨a - 2, by omega⟩
  let j : Fin 6 := ⟨b - 2, by omega⟩
  have ai : i.val + 2 = a := by dsimp [i]; omega
  have bj : j.val + 2 = b := by dsimp [j]; omega
  have e : i ≠ j := by
    intro h
    exact ne (ai.symm.trans (h ▸ bj))
  let r := cofactorRow i j c
  obtain ⟨hb, h0, h1⟩ := allCofactors i j e c
  rw [bj] at hb
  rw [ai] at h0 h1
  refine ⟨Function.update (row r) a false, Function.update (row r) a true, ?_, ?_, ?_, ?_, ?_, h0, h1⟩
  · simp
  · simp
  · simpa only [Function.update_of_ne (Ne.symm ne)] using hb
  · simpa only [Function.update_of_ne (Ne.symm ne)] using hb
  · intro k hk
    simp only [Function.update_of_ne hk]

lemma sensitive (a : ℕ) (ha : a ∈ raw) :
    ∃ u v : State, u a = false ∧ v a = true ∧ (∀ i ≠ a, u i = v i) ∧
      cycle u = false ∧ cycle v = true := by
  let b : ℕ := if a = 2 then 3 else 2
  have hb : b ∈ raw := by unfold b; split <;> decide
  have ne : a ≠ b := by unfold b; split <;> omega
  obtain ⟨u, v, l, r, _, _, h, f, t⟩ := cofactor a b ha hb ne false
  exact ⟨u, v, l, r, h, f, t⟩

lemma initialAgree {a : ℕ} {u v : State} (same : ∀ i ≠ a, u i = v i) :
    ∀ i ≠ a, initial u i = initial v i := by
  intro i hi
  simp [initial, same i hi]

lemma liveRaw (p : Trace) (o : ℕ) (fit : computes p o) : ∀ j ∈ raw, j ∈ stock p o := by
  intro j h
  by_contra missing
  simp only [stock, List.mem_append, List.mem_singleton, not_or] at missing
  obtain ⟨u, v, _, _, agree, f, t⟩ := sensitive j h
  have eq := ignores p _ _ j (initialAgree agree) missing.1 o (Ne.symm missing.2)
  rw [fit u, fit v, f, t] at eq
  contradiction

lemma exceptAfter (g : Instr) {u v : State} {a : ℕ} (agree : ∀ i ≠ a, u i = v i)
    (eq : value (initial u) g.2 = value (initial v) g.2) :
    ∀ i ≠ a, step (initial u) g i = step (initial v) g i := by
  intro i hi
  by_cases h : i = g.1
  · simp [step, h, eq]
  · simpa only [step, Function.update_of_ne h] using initialAgree agree i hi

lemma remaining (g : Instr) (p : Trace) (o a : ℕ) (ha : a ∈ args g.2)
    (once : (stock (g :: p) o).count a ≤ 1) : a ∉ uses p ∧ o ≠ a := by
  have split : stock (g :: p) o = args g.2 ++ stock p o := by
    simp only [stock, usesCons, List.append_assoc]
  have haveA := List.count_pos_iff.mpr ha
  rw [split, List.count_append] at once
  have dead : a ∉ stock p o := by
    intro live
    have h := List.count_pos_iff.mpr live
    omega
  simp only [stock, List.mem_append, List.mem_singleton, not_or] at dead
  exact ⟨dead.1, Ne.symm dead.2⟩

lemma binaryRepeats (g : Instr) (p : Trace) (o a b : ℕ) (ha : a ∈ raw) (hb : b ∈ raw)
    (ne : a ≠ b) (op : g.2.1 ≠ 2)
    (positions : (g.2.2.1 = a ∧ g.2.2.2 = b) ∨ (g.2.2.1 = b ∧ g.2.2.2 = a))
    (fit : computes (g :: p) o) : 2 ≤ (stock (g :: p) o).count a := by
  by_contra! few
  have harg : a ∈ args g.2 := by rcases positions with ⟨l,r⟩ | ⟨l,r⟩ <;> simp [args, op, l, r]
  obtain ⟨noRead, outNe⟩ := remaining g p o a harg (by omega)
  let c := decide (g.2.1 = 1)
  obtain ⟨u, v, _, _, ub, vb, agree, zero, one⟩ := cofactor a b ha hb ne c
  have ub' := (initRaw u hb).trans ub
  have vb' := (initRaw v hb).trans vb
  have eq : value (initial u) g.2 = value (initial v) g.2 := by
    rcases op_cases g.2.1 with eq | eq | eq
    · rcases positions with ⟨l,r⟩ | ⟨l,r⟩ <;> simp [value, get, eq, l, r, ub', vb', c]
    · rcases positions with ⟨l,r⟩ | ⟨l,r⟩ <;> simp [value, get, eq, l, r, ub', vb', c]
    · contradiction
  have result := ignores p _ _ a (exceptAfter g agree eq) noRead o outNe
  rw [← runCons, ← runCons, fit u, fit v, zero, one] at result
  contradiction

lemma notRepeats (g : Instr) (p : Trace) (o : ℕ) (ha : g.2.2.1 ∈ raw)
    (op : g.2.1 = 2) (tail : ∀ h ∈ p, h.2.1 ≠ 2) (fit : computes (g :: p) o) :
    2 ≤ (stock (g :: p) o).count g.2.2.1 := by
  by_contra! few
  obtain ⟨noRead, outNe⟩ := remaining g p o g.2.2.1 (arg_first g.2) (by omega)
  obtain ⟨u, v, u0, v1, agree, zero, one⟩ := sensitive g.2.2.1 ha
  have ineq : value (initial v) g.2 ≤ value (initial u) g.2 := by
    simp [value, get, op, initRaw u ha, initRaw v ha, u0, v1]
  have stepOrder : ∀ i ≠ g.2.2.1, step (initial v) g i ≤ step (initial u) g i := by
    intro i hi
    by_cases h : i = g.1
    · simpa [step, h] using ineq
    · simp only [step, Function.update_of_ne h]
      rw [initialAgree agree i hi]
  have result := ignoresMono p _ _ g.2.2.1 stepOrder noRead tail o outNe
  rw [← runCons, ← runCons, fit v, fit u, one, zero] at result
  exact (by decide : ¬ true ≤ false) result

def negs (p : Trace) : ℕ := (p.filter fun g => g.2.1 == 2).length

lemma negsZero (p : Trace) (h : negs p = 0) : ∀ g ∈ p, g.2.1 ≠ 2 := by
  intro g hg eq
  have e : g ∈ p.filter (fun g => g.2.1 == 2) := by simp [hg, eq]
  have len : p.filter (fun g => g.2.1 == 2) = [] := List.length_eq_zero_iff.mp h
  rw [len] at e
  contradiction

lemma stockLength (p : Trace) (o : ℕ) : (stock p o).length + negs p = 2 * p.length + 1 := by
  induction p with
  | nil => rfl
  | cons g p ih =>
    by_cases h : g.2.1 = 2 <;>
      simp [stock, usesCons, args, negs, h] at ih ⊢ <;> omega

lemma negsCons (g : Instr) (p : Trace) (h : g.2.1 = 2) : negs (g :: p) = negs p + 1 := by
  simp [negs, h]

def surplus (p : Trace) (o j : ℕ) : ℕ := (stock p o).count j - 1

lemma countAtMost (xs : List ℕ) (s : Finset ℕ) : ∑ j ∈ s, xs.count j ≤ xs.length := by
  let m : Multiset ℕ := xs
  have cap : (∑ j ∈ s, m.count j) ≤ m.card := by
    calc
      (∑ j ∈ s, m.count j) ≤ ∑ j ∈ s ∪ m.toFinset, m.count j :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun _ _ _ => Nat.zero_le _)
      _ = m.card := Multiset.sum_count_eq_card (fun j h => Finset.mem_union_right _ (Multiset.mem_toFinset.mpr h))
  simpa only [m, Multiset.coe_count, Multiset.coe_card] using cap

lemma budget (p : Trace) (o : ℕ) (hp : ok base p) (ho : o ∈ base ∪ keys p)
    (fit : computes p o) (min : shortest p) (small : p.length ≤ 7) :
    5 ≤ p.length ∧ negs p + (∑ j ∈ raw ∪ keys p, surplus p o j) ≤ 2 := by
  let s := raw ∪ keys p
  have disj : Disjoint raw (keys p) := Finset.disjoint_left.mpr fun j hj => noWrite p base hp (rawBase hj)
  have rawCard : raw.card = 6 := by decide
  have card : s.card = 6 + p.length := by
    dsimp only [s]
    rw [Finset.card_union_of_disjoint disj, rawCard, cardKeys p base hp]
  have pos (j : ℕ) (hj : j ∈ s) : 0 < (stock p o).count j := by
    apply List.count_pos_iff.mpr
    rcases Finset.mem_union.mp hj with h | h
    · exact liveRaw p o fit j h
    · exact liveKeys p o hp ho fit min j h
  have total : (∑ j ∈ s, surplus p o j) + s.card = ∑ j ∈ s, (stock p o).count j := by
    have cardSum : (∑ _j ∈ s, (1 : ℕ)) = s.card := by simp
    rw [← cardSum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have h := pos j hj
    unfold surplus
    omega
  have cap := countAtMost (stock p o) s
  have len := stockLength p o
  rw [card] at total
  change 5 ≤ p.length ∧ negs p + (∑ j ∈ s, surplus p o j) ≤ 2
  omega

lemma onePart (s : Finset ℕ) (f : ℕ → ℕ) (i : ℕ) (hi : i ∈ s) :
    f i ≤ ∑ j ∈ s, f j := by
  have sub : {i} ⊆ s := Finset.singleton_subset_iff.mpr hi
  simpa using Finset.sum_le_sum_of_subset_of_nonneg (f := f) sub (fun _ _ _ => Nat.zero_le _)

lemma twoParts (s : Finset ℕ) (f : ℕ → ℕ) (i j : ℕ) (hi : i ∈ s) (hj : j ∈ s) (ne : i ≠ j) :
    f i + f j ≤ ∑ k ∈ s, f k := by
  have sub : {i,j} ⊆ s := by intro k hk; simp at hk; rcases hk with rfl | rfl <;> assumption
  simpa [Finset.sum_insert, ne] using
    Finset.sum_le_sum_of_subset_of_nonneg (f := f) sub (fun _ _ _ => Nat.zero_le _)

lemma threeParts (s : Finset ℕ) (f : ℕ → ℕ) (i j t : ℕ) (hi : i ∈ s) (hj : j ∈ s) (ht : t ∈ s)
    (ij : i ≠ j) (it : i ≠ t) (jt : j ≠ t) : f i + f j + f t ≤ ∑ k ∈ s, f k := by
  have sub : {i,j,t} ⊆ s := by
    intro k hk
    simp at hk
    rcases hk with rfl | rfl | rfl <;> assumption
  simpa [Finset.sum_insert, ij, it, jt, Nat.add_assoc] using
    Finset.sum_le_sum_of_subset_of_nonneg (f := f) sub (fun _ _ _ => Nat.zero_le _)

lemma unshared (p : Trace) (o : ℕ) (hp : ok base p) (ho : o ∈ base ∪ keys p)
    (fit : computes p o) (min : shortest p) (small : p.length ≤ 7) :
    ∀ k ∈ keys p, (stock p o).count k ≤ 1 := by
  have ⟨len, remainingBudget⟩ := budget p o hp ho fit min small
  cases p with
  | nil => simp at len
  | cons g p =>
    let full := g :: p
    let s := raw ∪ keys full
    let f := surplus full o
    change negs full + (∑ j ∈ s, f j) ≤ 2 at remainingBudget
    intro k hk
    by_contra! many
    have hk' : k ∈ s := Finset.mem_union_right _ hk
    have fk : 1 ≤ f k := by dsimp [f, surplus, full]; omega
    obtain ⟨ha, more⟩ := firstShape g p o hp ho fit min
    let a := g.2.2.1
    have ha' : a ∈ s := Finset.mem_union_left _ ha
    have ak : a ≠ k := by
      intro e
      have hk'' : a ∈ keys full := by rwa [e]
      exact noWrite full base hp (rawBase ha) hk''
    by_cases hn : g.2.1 = 2
    · have negsFull : negs full = negs p + 1 := negsCons g p hn
      by_cases only : negs p = 0
      · have aa := notRepeats g p o ha hn (negsZero p only) fit
        have fa : 1 ≤ f a := by dsimp [f, a, surplus, full]; omega
        have sums := twoParts s f a k ha' hk' ak
        omega
      · have sums := onePart s f k hk'
        omega
    · obtain ⟨hb, ne⟩ := more hn
      let b := g.2.2.2
      have hb' : b ∈ s := Finset.mem_union_left _ hb
      have bk : b ≠ k := by
        intro e
        have hk'' : b ∈ keys full := by rwa [e]
        exact noWrite full base hp (rawBase hb) hk''
      have aa := binaryRepeats g p o a b ha hb ne hn (Or.inl ⟨rfl, rfl⟩) fit
      have bb := binaryRepeats g p o b a hb ha (Ne.symm ne) hn (Or.inr ⟨rfl, rfl⟩) fit
      have fa : 1 ≤ f a := by dsimp [f, surplus, full]; omega
      have fb : 1 ≤ f b := by dsimp [f, surplus, full]; omega
      have sums := threeParts s f a b k ha' hb' hk' ne ak bk
      omega

lemma singlePairs (p : Trace) (o : ℕ) (hp : ok base p) (ho : o ∈ base ∪ keys p)
    (fit : computes p o) (min : shortest p) (small : p.length ≤ 7) :
    let x := (stock p o).count
    (x 2 ≤ 1 ∧ x 3 ≤ 1) ∨ (x 4 ≤ 1 ∧ x 6 ≤ 1) ∨ (x 5 ≤ 1 ∧ x 7 ≤ 1) := by
  have ⟨_, cap⟩ := budget p o hp ho fit min small
  have less : (∑ j ∈ raw, surplus p o j) ≤ ∑ j ∈ raw ∪ keys p, surplus p o j :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun _ _ _ => Nat.zero_le _)
  have sumCap : (∑ j ∈ raw, surplus p o j) ≤ 2 := by omega
  simp [raw, Finset.sum_insert, surplus] at sumCap
  dsimp only
  omega

abbrev Formula := DMFormula 8

def flip : Formula → Formula
  | .lit i b => .lit i (!b)
  | .and l r => .or (flip l) (flip r)
  | .or l r => .and (flip l) (flip r)

def occ (i : Fin 8) : Formula → ℕ
  | .lit j _ => if i = j then 1 else 0
  | .and l r => occ i l + occ i r
  | .or l r => occ i l + occ i r

lemma flipOcc (i : Fin 8) (f : Formula) : occ i (flip f) = occ i f := by
  induction f <;> simp [flip, occ, *]

lemma flipEval (x : Fin 8 → Bool) (f : Formula) : (flip f).eval x = !(f.eval x) := by
  induction f with
  | lit i b => cases b <;> simp [flip, DMFormula.eval]
  | and l r hl hr => simp [flip, DMFormula.eval, hl, hr, Bool.not_and]
  | or l r hl hr => simp [flip, DMFormula.eval, hl, hr, Bool.not_or]

abbrev FState := ℕ → Formula

def fget : FState → Spec → Formula := get DMFormula.and DMFormula.or flip
def fstep (s : FState) (g : Instr) : FState := Function.update s g.1 (fget s g.2)
def expand (s : FState) (p : Trace) : FState := p.foldl fstep s

lemma fgetEval (g : Spec) (s : FState) (x : Fin 8 → Bool) :
    (fget s g).eval x = value (fun j => (s j).eval x) g := by
  unfold fget value get
  split
  · rfl
  · split
    · rfl
    · exact flipEval x _

lemma fstepEval (g : Instr) (s : FState) (x : Fin 8 → Bool) :
    (fun j => (fstep s g j).eval x) = step (fun j => (s j).eval x) g := by
  funext j
  by_cases e : j = g.1
  · simp [fstep, step, e, fgetEval]
  · simp [fstep, step, Function.update_of_ne e]

lemma expandEval (s : FState) (p : Trace) (x : Fin 8 → Bool) :
    (fun j => (expand s p j).eval x) = run (fun j => (s j).eval x) p := by
  induction p generalizing s with
  | nil => rfl
  | cons g p ih =>
    simp only [expand, run, List.foldl_cons] at ih ⊢
    rw [ih, fstepEval]

def initFormula : FState := fun j => .lit (if h : j < 8 then ⟨j,h⟩ else 0) true

lemma initFormulaEval (x : State) :
    (fun j => (initFormula j).eval (fun i => initial x i.val)) = initial x := by
  funext j
  by_cases h : j < 8
  · simp [initFormula, DMFormula.eval, h]
  · simp [initFormula, DMFormula.eval, initial, h, show j ≠ 0 by omega, show j ≠ 1 by omega]

lemma expansionFits (p : Trace) (o : ℕ) (fit : computes p o) (x : State) :
    (expand initFormula p o).eval (fun i => initial x i.val) = cycle x := by
  have eq := congrFun (expandEval initFormula p (fun i => initial x i.val)) o
  rw [initFormulaEval] at eq
  exact eq.trans (fit x)

def weight (xs : List ℕ) (f : ℕ → ℕ) : ℕ := (xs.map f).sum

lemma weightAppend (xs ys : List ℕ) (f : ℕ → ℕ) : weight (xs ++ ys) f = weight xs f + weight ys f := by
  simp [weight]

lemma weightChange (xs : List ℕ) (f g : ℕ → ℕ) (i : ℕ) (eq : ∀ j ≠ i, g j = f j) :
    weight xs g ≤ weight xs f + xs.count i * g i := by
  induction xs with
  | nil => simp [weight]
  | cons j xs ih =>
    by_cases h : j = i
    · subst j
      simp [weight, List.count_cons, Nat.add_mul] at ih ⊢
      omega
    · simp [weight, List.count_cons, h, Ne.symm h, eq j h] at ih ⊢
      omega

lemma fgetCount (i : Fin 8) (s : FState) (g : Spec) :
    occ i (fget s g) = weight (args g) (fun j => occ i (s j)) := by
  rcases op_cases g.1 with op | op | op <;> simp [fget, get, args, op, weight, occ, flipOcc]

lemma expandCount (p : Trace) (o : ℕ) (s : FState) (i : Fin 8)
    (once : ∀ j ∈ keys p, (stock p o).count j ≤ 1) :
    occ i (expand s p o) ≤ weight (stock p o) (fun j => occ i (s j)) := by
  induction p generalizing s with
  | nil => simp [stock, uses, expand, weight]
  | cons g p ih =>
    have split : stock (g :: p) o = args g.2 ++ stock p o := by simp [stock, usesCons, List.append_assoc]
    have bound (j : ℕ) (hj : j ∈ keys (g :: p)) : (stock p o).count j ≤ 1 := by
      have le := once j hj
      rw [split, List.count_append] at le
      omega
    have tail : ∀ j ∈ keys p, (stock p o).count j ≤ 1 := fun j h =>
      bound j (by simpa [keysCons] using (Finset.mem_insert_of_mem h : j ∈ insert g.1 (keys p)))
    have atGate : (stock p o).count g.1 ≤ 1 := bound _ (by simp [keysCons])
    have changed := weightChange (stock p o) (fun j => occ i (s j)) (fun j => occ i (fstep s g j)) g.1
      (fun j h => by simp [fstep, Function.update_of_ne h])
    have newSize : occ i (fstep s g g.1) = weight (args g.2) (fun j => occ i (s j)) := by
      simp [fstep, fgetCount]
    have sub := Nat.mul_le_mul_right (occ i (fstep s g g.1)) atGate
    rw [Nat.one_mul, newSize] at sub
    rw [newSize] at changed
    calc
      occ i (expand s (g :: p) o) = occ i (expand (fstep s g) p o) := rfl
      _ ≤ weight (stock p o) (fun j => occ i (fstep s g j)) := ih _ tail
      _ ≤ weight (stock (g :: p) o) (fun j => occ i (s j)) := by
        rw [split, weightAppend]
        omega

lemma initFormulaCount (i : Fin 8) (hi : i.val ≠ 0) (j : ℕ) :
    occ i (initFormula j) = if j = i.val then 1 else 0 := by
  by_cases h : j < 8
  · have e : i = (⟨j,h⟩ : Fin 8) ↔ j = i.val := by
      rw [← Fin.val_inj]
      exact eq_comm
    simp [initFormula, h, occ, e]
  · have e : i ≠ 0 := fun e => hi (congrArg Fin.val e)
    have ne : j ≠ i.val := by have p := i.isLt; omega
    simp [initFormula, occ, h, e, ne]

lemma weightCount (xs : List ℕ) (i : ℕ) : weight xs (fun j => if j = i then 1 else 0) = xs.count i := by
  induction xs with
  | nil => rfl
  | cons j xs ih =>
    simp only [weight, List.map_cons, List.sum_cons, List.count_cons] at ih ⊢
    rw [ih]
    by_cases h : j = i
    · simp [h, Nat.add_comm]
    · simp [h, Ne.symm h]

lemma formulaReads (p : Trace) (o : ℕ) (once : ∀ j ∈ keys p, (stock p o).count j ≤ 1) (i : Fin 8)
    (hi : i.val ≠ 0) : occ i (expand initFormula p o) ≤ (stock p o).count i.val := by
  have h := expandCount p o initFormula i once
  have e : (fun j => occ i (initFormula j)) = fun j => if j = i.val then 1 else 0 := funext (initFormulaCount i hi)
  rwa [e, weightCount] at h

abbrev FInput := Fin 8 → Bool
abbrev Table := Bool → Bool → Bool

def probe (x : FInput) (i j : Fin 8) (a b : Bool) : FInput :=
  Function.update (Function.update x i a) j b

def table (l : Formula) (x : FInput) (i j : Fin 8) : Table :=
  fun a b => l.eval (probe x i j a b)

lemma evalAbsent (l : Formula) (i : Fin 8) (absent : occ i l = 0) (u v : FInput)
    (agree : ∀ j ≠ i, u j = v j) : l.eval u = l.eval v := by
  induction l with
  | lit j b =>
    have ne : j ≠ i := by intro h; subst j; simp [occ] at absent
    simp [DMFormula.eval, agree j ne]
  | and l r ihl ihr =>
    simp only [occ] at absent
    simp [DMFormula.eval, ihl (by omega), ihr (by omega)]
  | or l r ihl ihr =>
    simp only [occ] at absent
    simp [DMFormula.eval, ihl (by omega), ihr (by omega)]

lemma tableLeft (l : Formula) (x : FInput) (i j : Fin 8) (h : occ i l = 0) (a a' b : Bool) :
    table l x i j a b = table l x i j a' b := by
  apply evalAbsent l i h
  intro k ne
  by_cases eq : k = j
  · simp [probe, eq]
  · simp [probe, Function.update_of_ne eq, Function.update_of_ne ne]

lemma tableRight (l : Formula) (x : FInput) (i j : Fin 8) (h : occ j l = 0) (a b b' : Bool) :
    table l x i j a b = table l x i j a b' := by
  apply evalAbsent l j h
  intro k ne
  simp only [probe, Function.update_of_ne ne]

def connect (isAnd a b : Bool) : Bool := if isAnd then a && b else a || b

lemma connectComm (isAnd a b : Bool) : connect isAnd a b = connect isAnd b a := by
  cases isAnd <;> simp [connect, Bool.and_comm, Bool.or_comm]

lemma dropConstant (op c : Bool) (right expected : Table) (off : expected false false = false)
    (on : expected true true = true) (fit : ∀ a b, connect op c (right a b) = expected a b) :
    ∀ a b, right a b = expected a b := by
  cases op <;> cases c
  · simpa [connect] using fit
  · have h := fit false false
    rw [off] at h
    simp [connect] at h
  · have h := fit true true
    rw [on] at h
    simp [connect] at h
  · simpa [connect] using fit

lemma dropSide (op : Bool) (l r : Formula) (x : FInput) (i j : Fin 8)
    (li : occ i l = 0) (lj : occ j l = 0) (expected : Table) (off : expected false false = false)
    (on : expected true true = true)
    (fit : ∀ a b, connect op (table l x i j a b) (table r x i j a b) = expected a b) :
    ∀ a b, table r x i j a b = expected a b := by
  apply dropConstant op (table l x i j false false) _ expected off on
  intro a b
  simpa only [tableLeft l x i j li a false b, tableRight l x i j lj false b false] using fit a b

lemma splitAnd (l r : Table) (left : ∀ a a' b, l a b = l a' b) (right : ∀ a b b', r a b = r a b')
    (fit : ∀ a b, (l a b && r a b) = (a || b)) : False := by
  have a := (Bool.and_eq_true_iff.mp (fit true false)).1
  have b := (Bool.and_eq_true_iff.mp (fit false true)).2
  rw [left true false false] at a
  rw [right false true false] at b
  have z := fit false false
  rw [a,b] at z
  contradiction

lemma splitOr (l r : Table) (left : ∀ a a' b, l a b = l a' b) (right : ∀ a b b', r a b = r a b')
    (fit : ∀ a b, (l a b || r a b) = (a && b)) : False := by
  have a := (Bool.or_eq_false_iff.mp (fit false true)).1
  have b := (Bool.or_eq_false_iff.mp (fit true false)).2
  rw [left false true true] at a
  rw [right true false true] at b
  have z := fit true true
  rw [a,b] at z
  contradiction

def Switch (f : Formula) (i j : Fin 8) (x y : FInput) : Prop :=
  (∀ a b, table f x i j a b = (a && b)) ∧ (∀ a b, table f y i j a b = (a || b))

lemma switchNode (op : Bool) (l r : Formula) (i j : Fin 8) (x y : FInput)
    (ihl : occ i l ≤ 1 → occ j l ≤ 1 → Switch l i j x y → False)
    (ihr : occ i r ≤ 1 → occ j r ≤ 1 → Switch r i j x y → False)
    (mi : occ i l + occ i r ≤ 1) (mj : occ j l + occ j r ≤ 1)
    (meet : ∀ a b, connect op (table l x i j a b) (table r x i j a b) = (a && b))
    (join : ∀ a b, connect op (table l y i j a b) (table r y i j a b) = (a || b)) : False := by
  have strip (a b : Formula) (ai : occ i a = 0) (aj : occ j a = 0)
      (hm : ∀ p q, connect op (table a x i j p q) (table b x i j p q) = (p && q))
      (hj : ∀ p q, connect op (table a y i j p q) (table b y i j p q) = (p || q)) : Switch b i j x y := by
    exact ⟨dropSide op a b x i j ai aj (· && ·) rfl rfl hm,
      dropSide op a b y i j ai aj (· || ·) rfl rfl hj⟩
  have separate (a b : Formula) (ai : occ i a = 0) (bj : occ j b = 0)
      (hm : ∀ p q, connect op (table a x i j p q) (table b x i j p q) = (p && q))
      (hj : ∀ p q, connect op (table a y i j p q) (table b y i j p q) = (p || q)) : False := by
    cases op
    · exact splitOr _ _ (tableLeft a x i j ai) (tableRight b x i j bj) hm
    · exact splitAnd _ _ (tableLeft a y i j ai) (tableRight b y i j bj) hj
  have meet' a b := (connectComm op (table r x i j a b) (table l x i j a b)).trans (meet a b)
  have join' a b := (connectComm op (table r y i j a b) (table l y i j a b)).trans (join a b)
  by_cases li : occ i l = 0 <;> by_cases lj : occ j l = 0
  · exact ihr (by omega) (by omega) (strip l r li lj meet join)
  · exact separate l r li (by omega) meet join
  · exact separate r l (by omega) lj meet' join'
  · exact ihl (by omega) (by omega) (strip r l (by omega) (by omega) meet' join')

lemma formulaSwitch (f : Formula) (i j : Fin 8) (ne : i ≠ j) (x y : FInput)
    (mi : occ i f ≤ 1) (mj : occ j f ≤ 1) (h : Switch f i j x y) : False := by
  induction f with
  | lit k s =>
    by_cases e : k = i
    · have zero : occ j (DMFormula.lit k s) = 0 := by simp [occ, e, Ne.symm ne]
      have eq := tableRight (.lit k s) x i j zero true false true
      rw [h.1 true false, h.1 true true] at eq
      contradiction
    · have zero : occ i (DMFormula.lit k s) = 0 := by simp [occ, Ne.symm e]
      have eq := tableLeft (.lit k s) x i j zero false true true
      rw [h.1 false true, h.1 true true] at eq
      contradiction
  | and l r ihl ihr => exact switchNode true l r i j x y ihl ihr mi mj h.1 h.2
  | or l r ihl ihr => exact switchNode false l r i j x y ihl ihr mi mj h.1 h.2

def maskPair (t : Fin 64) (i j : Fin 8) (a b : Bool) : State :=
  Function.update (Function.update (row t) i.val a) j.val b

lemma maskProbe (t : Fin 64) (i j : Fin 8) (hi : i.val ∈ raw) (hj : j.val ∈ raw)
    (ne : i ≠ j) (a b : Bool) :
    (fun k : Fin 8 => initial (maskPair t i j a b) k.val) =
      probe (fun k : Fin 8 => initial (row t) k.val) i j a b := by
  funext k
  have distinct : i.val ≠ j.val := fun h => ne (Fin.val_injective h)
  by_cases e : k = j
  · subst k
    rw [initRaw _ hj]
    simp [maskPair, probe]
  · have e' : k.val ≠ j.val := fun h => e (Fin.val_injective h)
    by_cases f : k = i
    · subst k
      rw [initRaw _ hi]
      simp [probe, maskPair, Function.update_of_ne ne, Function.update_of_ne distinct]
    · have f' : k.val ≠ i.val := fun h => f (Fin.val_injective h)
      simp [probe, maskPair, Function.update_of_ne e, Function.update_of_ne f, initial,
        Function.update_of_ne e', Function.update_of_ne f']

lemma forbidPair (f : Formula) (fit : ∀ x : State, f.eval (fun i => initial x i.val) = cycle x)
    (i j : Fin 8) (hi : i.val ∈ raw) (hj : j.val ∈ raw) (ne : i ≠ j)
    (seed : Fin 64)
    (meet : ∀ a b, cycle (maskPair 0 i j a b) = (a && b))
    (join : ∀ a b, cycle (maskPair seed i j a b) = (a || b))
    (mi : occ i f ≤ 1) (mj : occ j f ≤ 1) : False := by
  apply formulaSwitch f i j ne (fun k => initial (row 0) k.val) (fun k => initial (row seed) k.val) mi mj
  constructor
  · intro a b
    have eq := fit (maskPair 0 i j a b)
    rw [maskProbe 0 i j hi hj ne a b] at eq
    exact eq.trans (meet a b)
  · intro a b
    have eq := fit (maskPair seed i j a b)
    rw [maskProbe seed i j hi hj ne a b] at eq
    exact eq.trans (join a b)

lemma structuralBound (C : Circuit) (fan : FanInTwo C)
    (fit : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = cycle (fun i => x ⟨(i-2)%6, by omega⟩)) :
    8 ≤ C.size := by
  by_contra! small
  obtain ⟨initialTrace, initialOut, length, well, inScope, fitTrace⟩ := fromCircuit C fan fit
  obtain ⟨p, o, le, good, out, computes, min⟩ := existsShortest initialTrace initialOut well inScope fitTrace
  have short : p.length ≤ 7 := by omega
  have once := unshared p o good out computes min short
  let f := expand initFormula p o
  have fFit := expansionFits p o computes
  have fReads (i : Fin 8) (hi : i.val ≠ 0) (le : (stock p o).count i.val ≤ 1) : occ i f ≤ 1 :=
    (formulaReads p o once i hi).trans le
  rcases singlePairs p o good out computes min short with ⟨l,r⟩ | ⟨l,r⟩ | ⟨l,r⟩
  · exact forbidPair f fFit 2 3 (by decide) (by decide) (by decide) 24 (by decide) (by decide)
      (fReads 2 (by decide) l) (fReads 3 (by decide) r)
  · exact forbidPair f fFit 4 6 (by decide) (by decide) (by decide) 34 (by decide) (by decide)
      (fReads 4 (by decide) l) (fReads 6 (by decide) r)
  · exact forbidPair f fFit 5 7 (by decide) (by decide) (by decide) 5 (by decide) (by decide)
      (fReads 5 (by decide) l) (fReads 7 (by decide) r)

def wstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wfold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl wstep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp [wstep]; omega

lemma wgetD_lt {α : Type} (l r : List α) (i : ℕ) (d : α) (hi : i < l.length) :
    (l ++ r).getD i d = l.getD i d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma wgetD_snoc {α : Type} (l : List α) (a d : α) :
    (l ++ [a]).getD l.length d = a := by
  rw [List.getD_append_right _ _ _ _ (le_refl _)]
  simp

lemma wgetD_ge {α : Type} (l : List α) (i : ℕ) (d : α) (hi : l.length ≤ i) :
    l.getD i d = d := List.getD_eq_default _ _ hi

lemma wgetD_snoc' {α : Type} (l : List α) (a d : α) (i : ℕ) :
    (l ++ [a]).getD i d = if i < l.length then l.getD i d else if i = l.length then a else d := by
  split_ifs with h1 h2
  · exact wgetD_lt _ _ _ _ h1
  · subst h2; exact wgetD_snoc _ _ _
  · exact wgetD_ge _ _ _ (by simp; omega)

def cval (nw : List Bool) : Bool ⊕ ℕ → Bool
  | Sum.inl c => c
  | Sum.inr k => nw.getD k false

def red : GateOp → List (Bool ⊕ ℕ) → Option (Bool ⊕ ℕ)
  | GateOp.not, [] => some (Sum.inl true)
  | GateOp.not, Sum.inl c :: _ => some (Sum.inl (!c))
  | GateOp.and, [] => some (Sum.inl true)
  | GateOp.and, [s] => some s
  | GateOp.and, [Sum.inl c, s] => some (if c then s else Sum.inl false)
  | GateOp.and, [Sum.inr k, Sum.inl c] => some (if c then Sum.inr k else Sum.inl false)
  | GateOp.or, [] => some (Sum.inl false)
  | GateOp.or, [s] => some s
  | GateOp.or, [Sum.inl c, s] => some (if c then Sum.inl true else s)
  | GateOp.or, [Sum.inr k, Sum.inl c] => some (if c then Sum.inl true else Sum.inr k)
  | _, _ => none

def okOp (op : GateOp) : Prop := op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)

lemma okOp_cases {op : GateOp} (h : okOp op) : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not := by
  simpa [okOp] using h

lemma red_some (op : GateOp) (ms : List (Bool ⊕ ℕ)) (r : Bool ⊕ ℕ) (nw : List Bool)
    (h : red op ms = some r) : cval nw r = op.eval (ms.map (cval nw)) := by
  rcases ms with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · cases op <;> simp [red] at h <;> subst h <;> rfl
  · cases op <;> rcases a with a | a <;> simp [red] at h <;> subst h <;>
      simp [GateOp.eval, cval]
  · cases op <;> rcases a with a | a <;> rcases b with b | b <;> simp [red] at h <;>
      (try cases a) <;> (try cases b) <;> simp at h <;> subst h <;> simp [GateOp.eval, cval]
  · cases op <;> rcases a with a | a <;> simp [red] at h <;> subst h <;> simp [GateOp.eval, cval]

lemma red_none (op : GateOp) (ms : List (Bool ⊕ ℕ)) (nw : List Bool)
    (hop : okOp op) (hl : ms.length ≤ 2) (h : red op ms = none) :
    op.eval ((ms.filterMap Sum.getRight?).map fun k => nw.getD k false) =
      op.eval (ms.map (cval nw)) := by
  rcases okOp_cases hop with rfl | rfl | rfl
  · rcases ms with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · simp [red] at h
    · simp [red] at h
    · rcases a with a | a <;> rcases b with b | b <;> simp [red] at h
      simp [GateOp.eval, cval]
    · simp at hl
  · rcases ms with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · simp [red] at h
    · simp [red] at h
    · rcases a with a | a <;> rcases b with b | b <;> simp [red] at h
      simp [GateOp.eval, cval]
    · simp at hl
  · rcases ms with _ | ⟨a, l⟩
    · simp [red] at h
    · rcases a with a | a
      · simp [red] at h
      · simp [GateOp.eval, cval, List.filterMap_cons]

lemma red_mem (op : GateOp) (ms : List (Bool ⊕ ℕ)) (k : ℕ)
    (h : red op ms = some (Sum.inr k)) : Sum.inr k ∈ ms := by
  rcases ms with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · cases op <;> simp [red] at h
  · cases op <;> rcases a with a | a <;> simp [red] at h <;> simp [h]
  · cases op <;> rcases a with a | a <;> rcases b with b | b <;> simp [red] at h <;>
      (try cases a) <;> (try cases b) <;> simp_all
  · cases op <;> rcases a with a | a <;> simp [red] at h

def estep (n : ℕ) (st : List Gate × List (Bool ⊕ ℕ)) (g : Gate) :
    List Gate × List (Bool ⊕ ℕ) :=
  match red g.op (g.inputs.map fun i => st.2.getD i (Sum.inl false)) with
  | some r => (st.1, st.2 ++ [r])
  | none => (st.1 ++ [⟨g.op, (g.inputs.map fun i => st.2.getD i (Sum.inl false)).filterMap
      Sum.getRight?⟩], st.2 ++ [Sum.inr (n + st.1.length)])

def fanOk (g : Gate) : Prop := okOp g.op ∧ g.inputs.length ≤ 2

lemma estep_fan (n : ℕ) (gs : List Gate) (acc : List Gate) (env : List (Bool ⊕ ℕ))
    (hacc : ∀ g ∈ acc, fanOk g) (hgs : ∀ g ∈ gs, fanOk g) :
    ∀ g ∈ (gs.foldl (estep n) (acc, env)).1, fanOk g := by
  induction gs generalizing acc env with
  | nil => exact hacc
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hg := hgs g (by simp)
    have hgs' : ∀ g' ∈ gs, fanOk g' := fun g' h' => hgs g' (by simp [h'])
    unfold estep
    split
    · exact ih _ _ hacc hgs'
    · apply ih _ _ _ hgs'
      intro u hu
      simp only [List.mem_append, List.mem_singleton] at hu
      rcases hu with hu | rfl
      · exact hacc u hu
      · refine ⟨hg.1, ?_⟩
        have := List.length_filterMap_le Sum.getRight?
          (g.inputs.map fun i => env.getD i (Sum.inl false))
        simp only [List.length_map] at this
        exact this.trans hg.2

lemma estep_correct (n : ℕ) (x0 : List Bool) (hx0 : x0.length = n) :
    ∀ (gs acc : List Gate) (env : List (Bool ⊕ ℕ)) (oldW : List Bool),
    (∀ g ∈ gs, fanOk g) → env.length = oldW.length →
    (∀ i k, env.getD i (Sum.inl false) = Sum.inr k → k < n + acc.length) →
    (∀ i, cval (acc.foldl wstep x0) (env.getD i (Sum.inl false)) = oldW.getD i false) →
    ∀ i, cval ((gs.foldl (estep n) (acc, env)).1.foldl wstep x0)
        ((gs.foldl (estep n) (acc, env)).2.getD i (Sum.inl false)) =
      (gs.foldl wstep oldW).getD i false := by
  intro gs
  induction gs with
  | nil => intro acc env oldW _ _ _ hinv; exact hinv
  | cons g gs ih =>
    intro acc env oldW hfan hlen hbnd hinv
    have hg := hfan g (by simp)
    have hgs' : ∀ g' ∈ gs, fanOk g' := fun g' h' => hfan g' (by simp [h'])
    simp only [List.foldl_cons]
    let newW := acc.foldl wstep x0
    have hnewW : newW.length = n + acc.length := by simp [newW, wfold_length, hx0]
    let ms := g.inputs.map fun i => env.getD i (Sum.inl false)
    have hms : g.inputs.map (fun i => oldW.getD i false) = ms.map (cval newW) := by
      simp only [ms, List.map_map]
      apply List.map_congr_left
      intro k _
      exact (hinv k).symm
    have hval : (wstep oldW g).getD oldW.length false =
        g.op.eval (ms.map (cval newW)) := by
      rw [wstep, wgetD_snoc, hms]
    unfold estep
    split
    · rename_i r hr
      apply ih acc (env ++ [r]) (wstep oldW g) hgs'
      · simp [wstep, hlen]
      · intro i k hk
        rw [wgetD_snoc'] at hk
        split_ifs at hk with h1 h2
        · exact hbnd i k hk
        · subst hk
          have hm := red_mem _ _ _ hr
          simp only [ms, List.mem_map] at hm
          obtain ⟨j, _, hj⟩ := hm
          have := hbnd j k hj
          omega
      · intro i
        rw [wgetD_snoc', wstep, wgetD_snoc']
        rw [← hlen]
        split_ifs with h1 h2
        · exact hinv i
        · rw [red_some _ _ _ newW hr]; exact hms.symm ▸ rfl
        · rfl
    · rename_i hr
      let g' : Gate := ⟨g.op, ms.filterMap Sum.getRight?⟩
      have hfold : (acc ++ [g']).foldl wstep x0 = wstep newW g' := by
        simp [newW, List.foldl_append]
      have hg'val : (wstep newW g').getD newW.length false = g.op.eval (ms.map (cval newW)) := by
        rw [wstep, wgetD_snoc]
        exact red_none g.op ms newW hg.1 (by simpa [ms] using hg.2) hr
      apply ih (acc ++ [g']) (env ++ [Sum.inr (n + acc.length)]) (wstep oldW g) hgs'
      · simp [wstep, hlen]
      · intro i k hk
        rw [wgetD_snoc'] at hk
        simp only [List.length_append, List.length_singleton]
        split_ifs at hk with h1 h2
        · have := hbnd i k hk; omega
        · cases hk; omega
      · intro i
        change cval ((acc ++ [g']).foldl wstep x0) _ = _
        rw [hfold, wgetD_snoc']
        rw [show wstep oldW g = oldW ++ [g.op.eval (g.inputs.map fun i => oldW.getD i false)]
          from rfl, wgetD_snoc']
        rw [← hlen]
        split_ifs with h1 h2
        · rw [← hinv i]
          rcases he : env.getD i (Sum.inl false) with c | k
          · rfl
          · have := hbnd i k he
            simp only [cval]
            exact wgetD_lt _ _ _ _ (by omega)
        · simp only [cval]
          rw [← hnewW]
          refine hg'val.trans (hval.symm.trans ?_)
          rw [wstep, wgetD_snoc]
        · rfl

def hit (h : Gate) : Bool :=
  match h.op with
  | GateOp.not => decide (h.inputs.head? = some 0) || decide (h.inputs.head? = some 3)
  | _ => h.inputs.contains 0 || h.inputs.contains 3

lemma red_hit (op : GateOp) (ms : List (Bool ⊕ ℕ)) (hop : okOp op) (hl : ms.length ≤ 2)
    (hn : op = GateOp.not → ∃ c t, ms = Sum.inl c :: t)
    (ho : op ≠ GateOp.not → ∃ c, Sum.inl c ∈ ms) : red op ms ≠ none := by
  rcases okOp_cases hop with rfl | rfl | rfl
  · obtain ⟨c, hc⟩ := ho (fun h => GateOp.noConfusion h)
    rcases ms with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp at hc
    · simp [red]
    · rcases a with a | a <;> rcases b with b | b <;> simp [red] at hc ⊢
    · simp at hl
  · obtain ⟨c, hc⟩ := ho (fun h => GateOp.noConfusion h)
    rcases ms with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp at hc
    · simp [red]
    · rcases a with a | a <;> rcases b with b | b <;> simp [red] at hc ⊢
    · simp at hl
  · obtain ⟨c, t, rfl⟩ := hn rfl
    simp [red]

lemma estep_size (n : ℕ) : ∀ (gs acc : List Gate) (env : List (Bool ⊕ ℕ)),
    (∀ g ∈ gs, fanOk g) →
    (∀ z, (z = 0 ∨ z = 3) → z < env.length ∧ ∃ c, env.getD z (Sum.inl false) = Sum.inl c) →
    (gs.foldl (estep n) (acc, env)).1.length + (gs.filter hit).length ≤ acc.length + gs.length := by
  intro gs
  induction gs with
  | nil => intro acc env _ _; simp
  | cons g gs ih =>
    intro acc env hfan hz
    have hg := hfan g (by simp)
    have hgs' : ∀ g' ∈ gs, fanOk g' := fun g' h' => hfan g' (by simp [h'])
    have hz' : ∀ r : Bool ⊕ ℕ, ∀ z, (z = 0 ∨ z = 3) → z < (env ++ [r]).length ∧
        ∃ c, (env ++ [r]).getD z (Sum.inl false) = Sum.inl c := by
      intro r z hzz
      obtain ⟨h1, h2⟩ := hz z hzz
      refine ⟨by simp; omega, ?_⟩
      rw [wgetD_lt _ _ _ _ h1]; exact h2
    simp only [List.foldl_cons, List.filter_cons, List.length_cons]
    let ms := g.inputs.map fun i => env.getD i (Sum.inl false)
    rcases hr : red g.op ms with _ | r
    · have e1 : estep n (acc, env) g = (acc ++ [⟨g.op, ms.filterMap Sum.getRight?⟩],
          env ++ [Sum.inr (n + acc.length)]) := by
        simp only [estep]; rw [show (g.inputs.map fun i => env.getD i (Sum.inl false)) = ms from rfl, hr]
      rw [e1]
      have := ih (acc ++ [⟨g.op, ms.filterMap Sum.getRight?⟩]) (env ++ [Sum.inr (n + acc.length)]) hgs' (hz' _)
      simp only [List.length_append, List.length_singleton] at this
      have hh : hit g = false := by
        by_contra hc
        simp only [Bool.not_eq_false] at hc
        apply red_hit g.op ms hg.1 (by simpa [ms] using hg.2) _ _ hr
        · intro hop
          simp only [hit, hop] at hc
          rcases hi : g.inputs with _ | ⟨i, t⟩
          · simp [hi] at hc
          · simp only [hi, List.head?_cons, Option.some.injEq, Bool.or_eq_true,
              decide_eq_true_eq] at hc
            have hi' : i = 0 ∨ i = 3 := hc
            obtain ⟨c, hc'⟩ := (hz i hi').2
            refine ⟨c, t.map fun i => env.getD i (Sum.inl false), ?_⟩
            show g.inputs.map _ = _
            rw [hi, List.map_cons, hc']
        · intro hop
          have hc2 : 0 ∈ g.inputs ∨ 3 ∈ g.inputs := by
            revert hc
            unfold hit
            split
            · rename_i heq; exact absurd heq hop
            · simp
          rcases hc2 with hm | hm
          · obtain ⟨c, hc'⟩ := (hz 0 (Or.inl rfl)).2
            exact ⟨c, List.mem_map.mpr ⟨0, hm, hc'⟩⟩
          · obtain ⟨c, hc'⟩ := (hz 3 (Or.inr rfl)).2
            exact ⟨c, List.mem_map.mpr ⟨3, hm, hc'⟩⟩
      simp only [hh, Bool.false_eq_true, ite_false]
      omega
    · have e1 : estep n (acc, env) g = (acc, env ++ [r]) := by
        simp only [estep]; rw [show (g.inputs.map fun i => env.getD i (Sum.inl false)) = ms from rfl, hr]
      rw [e1]
      have := ih acc (env ++ [r]) hgs' (hz' r)
      split
      · simp only [List.length_cons]; omega
      · omega

def edge (a b : ℕ) (g h : Gate) : Prop :=
  g.op = h.op ∧ List.Forall₂ (fun i j => j = i + 1 ∨ j = 0 ∧ (i = a ∨ i = b)) g.inputs h.inputs

def P2 (g : Gate) : Bool := g.op.eval [true, false] && g.inputs.contains 2

lemma f2_mem {R : ℕ → ℕ → Prop} : ∀ {l1 l2 : List ℕ}, List.Forall₂ R l1 l2 →
    ∀ i ∈ l1, ∃ j ∈ l2, R i j := by
  intro l1 l2 h
  induction h with
  | nil => simp
  | cons hab _ ih =>
    intro i hi
    simp only [List.mem_cons] at hi
    rcases hi with rfl | hi
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨j, hj, hr⟩ := ih i hi
      exact ⟨j, List.mem_cons_of_mem _ hj, hr⟩

lemma f2_map (a b : ℕ) : ∀ {l1 l2 : List ℕ},
    List.Forall₂ (fun i j => j = i + 1 ∨ j = 0 ∧ (i = a ∨ i = b)) l1 l2 → 0 ∉ l2 →
    l2 = l1.map (· + 1) := by
  intro l1 l2 h
  induction h with
  | nil => simp
  | cons hab _ ih =>
    intro h0
    simp only [List.mem_cons, not_or] at h0
    rcases hab with hab | hab
    · rw [List.map_cons, ih h0.2, hab]
    · exact absurd hab.1 (Ne.symm h0.1)

lemma f2_fan {R : Gate → Gate → Prop} {F : Gate → Prop} : ∀ {l1 l2 : List Gate},
    List.Forall₂ R l1 l2 → (∀ g ∈ l1, F g) → List.Forall₂ (fun g h => F g ∧ R g h) l1 l2 := by
  intro l1 l2 h
  induction h with
  | nil => intro _; exact List.Forall₂.nil
  | cons hab _ ih =>
    intro hf
    exact List.Forall₂.cons ⟨hf _ List.mem_cons_self, hab⟩
      (ih fun g hg => hf g (List.mem_cons_of_mem _ hg))

lemma cnt_le {R : Gate → Gate → Prop} {P Q : Gate → Bool} : ∀ {l1 l2 : List Gate},
    List.Forall₂ R l1 l2 → (∀ g h, R g h → P g = true → Q h = true) →
    (l1.filter P).length ≤ (l2.filter Q).length := by
  intro l1 l2 h
  induction h with
  | nil => intro _; simp
  | @cons g h' t1 t2 hab _ ih =>
    intro hPQ
    have := ih hPQ
    simp only [List.filter_cons]
    by_cases hp : P g = true
    · simp [hp, hPQ g h' hab hp]; omega
    · simp only [Bool.not_eq_true] at hp
      simp only [hp]
      by_cases hq : Q h' = true <;> simp [hq] <;> omega

lemma cnt_lt {R : Gate → Gate → Prop} {P Q : Gate → Bool} : ∀ {l1 l2 : List Gate},
    List.Forall₂ R l1 l2 → (∀ g h, R g h → P g = true → Q h = true) →
    ¬ List.Forall₂ (fun g h => R g h ∧ (P g = true ∨ Q h = false)) l1 l2 →
    (l1.filter P).length + 1 ≤ (l2.filter Q).length := by
  intro l1 l2 h
  induction h with
  | nil => intro _ hn; exact absurd List.Forall₂.nil hn
  | @cons g h' t1 t2 hab ht ih =>
    intro hPQ hn
    simp only [List.filter_cons]
    by_cases hp : P g = true
    · have hq := hPQ g h' hab hp
      have hn' : ¬ List.Forall₂ (fun g h => R g h ∧ (P g = true ∨ Q h = false)) t1 t2 :=
        fun hc => hn (List.Forall₂.cons ⟨hab, Or.inl hp⟩ hc)
      have := ih hPQ hn'
      simp [hp, hq]; omega
    · simp only [Bool.not_eq_true] at hp
      simp only [hp]
      by_cases hq : Q h' = true
      · have := cnt_le ht hPQ
        simp [hq]; omega
      · simp only [Bool.not_eq_true] at hq
        have hn' : ¬ List.Forall₂ (fun g h => R g h ∧ (P g = true ∨ Q h = false)) t1 t2 :=
          fun hc => hn (List.Forall₂.cons ⟨hab, Or.inr hq⟩ hc)
        have := ih hPQ hn'
        simp [hq]; omega

lemma P2_or (g : Gate) (hf : fanOk g) (hp : P2 g = true) : g.op = GateOp.or ∧ 2 ∈ g.inputs := by
  simp only [P2, Bool.and_eq_true, List.contains_eq_mem, decide_eq_true_eq] at hp
  refine ⟨?_, hp.2⟩
  rcases okOp_cases hf.1 with h | h | h <;> rw [h] at hp ⊢ <;> simp [GateOp.eval] at hp ⊢

lemma P2_hit (a b : ℕ) (g h : Gate) (hr : fanOk g ∧ edge a b g h) (hp : P2 g = true) :
    hit h = true := by
  obtain ⟨hor, h2⟩ := P2_or g hr.1 hp
  obtain ⟨j, hj, hj'⟩ := f2_mem hr.2.2 2 h2
  have hop : h.op = GateOp.or := hr.2.1 ▸ hor
  simp only [hit, hop, Bool.or_eq_true, List.contains_eq_mem, decide_eq_true_eq]
  rcases hj' with rfl | ⟨rfl, _⟩
  · exact Or.inr hj
  · exact Or.inl hj

lemma sim_val (a b : ℕ) (g h : Gate) (wC : List Bool) (hw : wC.getD 2 false = true)
    (hr : (fanOk g ∧ edge a b g h) ∧ (P2 g = true ∨ hit h = false)) :
    h.op.eval (h.inputs.map fun i => (true :: wC).getD i false) =
      g.op.eval (g.inputs.map fun i => wC.getD i false) := by
  obtain ⟨⟨hf, hop, hin⟩, hph⟩ := hr
  rcases hph with hp | hh
  · obtain ⟨hor, h2⟩ := P2_or g hf hp
    obtain ⟨j, hj, hj'⟩ := f2_mem hin 2 h2
    rw [← hop, hor]
    simp only [GateOp.eval, List.any_map]
    have e1 : g.inputs.any (fun i => wC.getD i false) = true :=
      List.any_eq_true.mpr ⟨2, h2, by simpa using hw⟩
    have e2 : h.inputs.any (fun i => (true :: wC).getD i false) = true := by
      refine List.any_eq_true.mpr ⟨j, hj, ?_⟩
      rcases hj' with rfl | ⟨rfl, _⟩
      · simpa using hw
      · simp
    simp only [Function.comp_def, id] at e1 e2 ⊢
    rw [e1, e2]
  · by_cases hn : h.op = GateOp.not
    · simp only [hit, hn, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hh
      rw [hop, hn]
      simp only [GateOp.eval]
      generalize g.inputs = l1 at hin ⊢
      generalize h.inputs = l2 at hin hh ⊢
      rcases hin with _ | ⟨hij, _⟩
      · rfl
      · rename_i i j _ _
        rcases hij with rfl | ⟨rfl, _⟩
        · simp
        · simp at hh
    · have h0 : 0 ∉ h.inputs := by
        intro hm
        have : hit h = true := by
          revert hm
          unfold hit
          split
          · rename_i heq; exact absurd heq hn
          · simp only [Bool.or_eq_true, List.contains_eq_mem, decide_eq_true_eq]; exact fun hm => Or.inl hm
        rw [this] at hh; exact absurd hh (by decide)
      rw [f2_map a b hin h0, ← hop, List.map_map]
      congr 1

lemma sim (a b : ℕ) : ∀ {gs hs : List Gate},
    List.Forall₂ (fun g h => (fanOk g ∧ edge a b g h) ∧ (P2 g = true ∨ hit h = false)) gs hs →
    ∀ wC : List Bool, 3 ≤ wC.length → wC.getD 2 false = true →
    hs.foldl wstep (true :: wC) = true :: gs.foldl wstep wC := by
  intro gs hs H
  induction H with
  | nil => intro _ _ _; rfl
  | @cons g h t1 t2 hab _ ih =>
    intro wC hl hw
    simp only [List.foldl_cons]
    have e : wstep (true :: wC) h = true :: wstep wC g := by
      simp only [wstep, List.cons_append]
      rw [sim_val a b g h wC hw hab]
    rw [e]
    apply ih
    · simp [wstep]; omega
    · rw [wstep, wgetD_lt _ _ _ _ (by omega)]; exact hw

lemma fan_fan (C : Circuit) (h : FanInTwo C) : ∀ g ∈ C.gates, fanOk g := h

lemma edge_fan (a b : ℕ) : ∀ {l1 l2 : List Gate}, List.Forall₂ (edge a b) l1 l2 →
    (∀ g ∈ l1, fanOk g) → ∀ h ∈ l2, fanOk h := by
  intro l1 l2 H
  induction H with
  | nil => simp
  | @cons g h t1 t2 hab _ ih =>
    intro hf u hu
    simp only [List.mem_cons] at hu
    rcases hu with rfl | hu
    · obtain ⟨h1, h2⟩ := hf g List.mem_cons_self
      exact ⟨hab.1 ▸ h1, hab.2.length_eq ▸ h2⟩
    · exact ih (fun v hv => hf v (List.mem_cons_of_mem _ hv)) u hu

lemma cyc8 : ∀ E : Circuit, FanInTwo E → (∀ (x3 : Fin (6 : ℕ) → Bool), E.eval (List.ofFn x3) = (x3 (0 : Fin (6 : ℕ)) && x3 (1 : Fin (6 : ℕ)) || x3 (0 : Fin (6 : ℕ)) && x3 (3 : Fin (6 : ℕ)) || x3 (1 : Fin (6 : ℕ)) && x3 (4 : Fin (6 : ℕ)) || x3 (2 : Fin (6 : ℕ)) && x3 (4 : Fin (6 : ℕ)) || x3 (3 : Fin (6 : ℕ)) && x3 (5 : Fin (6 : ℕ)) || x3 (2 : Fin (6 : ℕ)) && x3 (5 : Fin (6 : ℕ)))) → 8 ≤ E.size :=
  structuralBound

end PEqualNP.Outside.L_meta_4799

open PEqualNP.Outside.L_meta_4799

theorem PEqualNP.Outside.L_meta_4799 : have x1 : (Fin (7 : ℕ) → Bool) → Bool := fun (x1 : Fin (7 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (4 : ℕ), (15 : ℕ), (26 : ℕ), (35 : ℕ), (46 : ℕ), (36 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (7 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (7 : ℕ) (x2 % (10 : ℕ))); ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size = (11 : ℕ) → PEqualNP.MetaComplexity.circuitFun (7 : ℕ) x2 = x1 → List.Forall₂ (fun (x9 x10 : PEqualNP.CircuitLowerBounds.Gate) => x9.op = x10.op ∧ List.Forall₂ (fun (x11 x12 : ℕ) => x12 = x11 + (1 : ℕ) ∨ x12 = (0 : ℕ) ∧ (x11 = x4 ∨ x11 = x5)) x9.inputs x10.inputs) x2.gates x3.gates → (∀ (x10 : Fin (7 : ℕ) → Bool), (x3.wires (Bool.true :: List.ofFn x10)).getD (x2.output + (1 : ℕ)) Bool.false = (x1 x10 || x10 (2 : Fin (7 : ℕ)))) → (List.filter (fun (x11 : PEqualNP.CircuitLowerBounds.Gate) => x11.op.eval [Bool.true, Bool.false] && x11.inputs.contains (2 : ℕ)) x2.gates).length = (3 : ℕ) → False := by
  intro f C D a b fan size base edits modified three
  have hE : List.Forall₂ (edge a b) C.gates D.gates := edits
  have hR := f2_fan hE (fan_fan C fan)
  have hcnt : (C.gates.filter P2).length + 1 ≤ (D.gates.filter hit).length := by
    refine cnt_lt hR (fun g h hr hp => P2_hit a b g h hr hp) ?_
    intro H
    let a0 : Fin 7 → Bool := fun i => decide (i = 2)
    have hs := sim a b H (List.ofFn a0) (by simp) (by decide)
    have hm := modified a0
    change (D.gates.foldl wstep (true :: List.ofFn a0)).getD (C.output + 1) false = _ at hm
    rw [hs] at hm
    have hb := congrFun base a0
    change (C.gates.foldl wstep (List.ofFn a0)).getD C.output false = _ at hb
    simp only [List.getD_cons_succ] at hm
    rw [hb] at hm
    revert hm
    dsimp only [f, a0]
    decide
  have h3 : (C.gates.filter PEqualNP.Outside.L_meta_4799.P2).length = 3 := three
  have hsizeD : D.gates.length = 11 := hE.length_eq ▸ size
  have hfanD := PEqualNP.Outside.L_meta_4799.edge_fan a b hE (PEqualNP.Outside.L_meta_4799.fan_fan C fan)
  let env0 : List (Bool ⊕ ℕ) := [Sum.inl true, Sum.inr 0, Sum.inr 1, Sum.inl false,
    Sum.inr 2, Sum.inr 3, Sum.inr 4, Sum.inr 5]
  let res := D.gates.foldl (estep 6) ([], env0)
  have hsz := estep_size 6 D.gates [] env0 hfanD (by
    intro z hz
    rcases hz with rfl | rfl
    · exact ⟨by decide, true, rfl⟩
    · exact ⟨by decide, false, rfl⟩)
  let lift (y : Fin 6 → Bool) : Fin 7 → Bool := ![y 0, y 1, false, y 2, y 3, y 4, y 5]
  let cyc (x3 : Fin 6 → Bool) : Bool := (x3 (0 : Fin (6 : ℕ)) && x3 (1 : Fin (6 : ℕ)) || x3 (0 : Fin (6 : ℕ)) && x3 (3 : Fin (6 : ℕ)) || x3 (1 : Fin (6 : ℕ)) && x3 (4 : Fin (6 : ℕ)) || x3 (2 : Fin (6 : ℕ)) && x3 (4 : Fin (6 : ℕ)) || x3 (3 : Fin (6 : ℕ)) && x3 (5 : Fin (6 : ℕ)) || x3 (2 : Fin (6 : ℕ)) && x3 (5 : Fin (6 : ℕ)))
  have geometry : ∀ y : Fin 6 → Bool, (f (lift y) || lift y 2) = cyc y := by
    dsimp only [f, lift, cyc]
    decide +kernel
  have hval : ∀ y : Fin 6 → Bool,
      cval (res.1.foldl wstep (List.ofFn y)) (res.2.getD (C.output + 1) (Sum.inl false)) = cyc y := by
    intro y
    have hc := estep_correct 6 (List.ofFn y) (by simp) D.gates [] env0
      (true :: List.ofFn (lift y)) hfanD (by simp [env0]) (by
        intro i k hk
        match i, hk with
        | 1, hk => cases hk; decide
        | 2, hk => cases hk; decide
        | 4, hk => cases hk; decide
        | 5, hk => cases hk; decide
        | 6, hk => cases hk; decide
        | 7, hk => cases hk; decide
        | 0, hk => cases hk
        | 3, hk => cases hk
        | i + 8, hk => simp [env0] at hk) (by
        intro i
        match i with
        | 0 => rfl
        | 1 => rfl
        | 2 => rfl
        | 3 => rfl
        | 4 => rfl
        | 5 => rfl
        | 6 => rfl
        | 7 => rfl
        | i + 8 => simp [env0, cval]) (C.output + 1)
    rw [hc, ← geometry y, ← modified (lift y)]
    rfl
  rcases ho : res.2.getD (C.output + 1) (Sum.inl false) with c | k
  · have h1 := hval (fun _ => false)
    have h2 := hval ![true, true, false, false, false, false]
    rw [ho] at h1 h2
    simp only [cval] at h1 h2
    rw [h1] at h2
    revert h2
    dsimp only [cyc]
    decide
  · let E : Circuit := ⟨res.1, k⟩
    have hfanE : FanInTwo E := estep_fan 6 D.gates [] env0 (by simp) hfanD
    have hEval : ∀ y : Fin 6 → Bool, E.eval (List.ofFn y) = cyc y := by
      intro y
      have := hval y
      rw [ho] at this
      exact this
    have h8 := cyc8 E hfanE hEval
    change 8 ≤ (D.gates.foldl (estep 6) ([], env0)).1.length at h8
    simp only [List.length_nil] at hsz
    omega
