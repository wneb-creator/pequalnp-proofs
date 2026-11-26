import PEqualNP.Defs

-- Reference-table lemmas and gate emitter adapted from k-sandhu’s L_meta_7073.
namespace PEqualNP.Outside.L_meta_17794_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Each original wire becomes a constant or a reference to a new wire.
abbrev Ref := Bool ⊕ ℕ

def fixed : Ref := .inl false

def value (w : List Bool) : Ref → Bool
  | .inl b => b
  | .inr i => w.getD i false

def valid (n : ℕ) : Ref → Prop
  | .inl _ => True
  | .inr i => i < n

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

lemma run_append (gs hs : List Gate) (w : List Bool) :
    run (gs ++ hs) w = run hs (run gs w) :=
  List.foldl_append

lemma run_length (gs : List Gate) (w : List Bool) : (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (step w g)).length = w.length + (g :: gs).length
    rw [ih]
    simp [step]
    omega

lemma run_prefix (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (step w g)).getD i false = _
    rw [ih _ (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi

lemma getD_last {α : Type} (l : List α) (a d : α) :
    (l ++ [a]).getD l.length d = a := by
  rw [List.getD_append_right _ _ _ _ (Nat.le_refl _)]
  simp

def good (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

def width (op : GateOp) : ℕ := if op.eval [true] = true then 2 else 1

def binary (op : GateOp) (neutral : Bool) (n : ℕ) (a b : Ref) : Ref × List Gate :=
  match a, b with
  | .inl c, _ => (if c = neutral then b else .inl c, [])
  | _, .inl c => (if c = neutral then a else .inl c, [])
  | .inr i, .inr j => (.inr n, [⟨op, [i, j]⟩])

def emit (op : GateOp) (n : ℕ) (rs : List Ref) : Ref × List Gate :=
  match op, rs with
  | .not, [] => (.inl true, [])
  | .not, .inl b :: _ => (.inl (!b), [])
  | .not, .inr i :: _ => (.inr n, [⟨.not, [i]⟩])
  | .and, [] => (.inl true, [])
  | .or, [] => (.inl false, [])
  | .and, [a] | .or, [a] => (a, [])
  | .and, a :: b :: _ => binary .and true n a b
  | .or, a :: b :: _ => binary .or false n a b
  | _, _ => (fixed, [])

lemma emit_ok (op : GateOp) (n : ℕ) (rs : List Ref)
    (hop : op = .and ∨ op = .or ∨ op = .not) (hl : rs.length ≤ 2) :
    let e := emit op n rs
    e.2.length ≤ 1 ∧ (∀ g ∈ e.2, good g) ∧
      (∀ b : Bool, Sum.inl b ∈ rs.take (width op) → e.2 = []) ∧
      ∀ w : List Bool, w.length = n → (∀ r ∈ rs, valid n r) →
        valid (run e.2 w).length e.1 ∧
          value (run e.2 w) e.1 = op.eval (rs.map (value w)) := by
  dsimp only
  rcases rs with _ | ⟨a, _ | ⟨b, _ | ⟨c, cs⟩⟩⟩
  · rcases hop with rfl | rfl | rfl <;> simp [emit, valid, value, GateOp.eval]
  · rcases hop with rfl | rfl | rfl
    · simp [emit, run, GateOp.eval]
      intro w hw
      simp [hw]
    · simp [emit, run, GateOp.eval]
      intro w hw
      simp [hw]
    · rcases a with a | a
      · simp [emit, valid, value, GateOp.eval]
      · simp [emit, width, run, step, good, valid, value, GateOp.eval, -List.getD_eq_getElem?_getD]
        intro w hw
        simp [← hw, getD_last, -List.getD_eq_getElem?_getD]
  · rcases hop with rfl | rfl | rfl
    · rcases a with (a | a) <;> rcases b with (b | b) <;>
        (try cases (show Bool from a)) <;> (try cases (show Bool from b)) <;>
        simp [emit, binary, width, run, step, good, valid, value, GateOp.eval,
          -List.getD_eq_getElem?_getD] <;>
        intro w hw <;> simp [← hw, getD_last, -List.getD_eq_getElem?_getD]
    · rcases a with (a | a) <;> rcases b with (b | b) <;>
        (try cases (show Bool from a)) <;> (try cases (show Bool from b)) <;>
        simp [emit, binary, width, run, step, good, valid, value, GateOp.eval,
          -List.getD_eq_getElem?_getD] <;>
        intro w hw <;> simp [← hw, getD_last, -List.getD_eq_getElem?_getD]
    · rcases a with a | a
      · simp [emit, valid, value, GateOp.eval]
      · simp [emit, width, run, step, good, valid, value, GateOp.eval, -List.getD_eq_getElem?_getD]
        intro w hw
        simp [← hw, getD_last, -List.getD_eq_getElem?_getD]
  · simp at hl

def read (refs : List Ref) (i : ℕ) : Ref := refs.getD i fixed

-- The reference table recovers every original wire and only points to available new wires.
def related (refs : List Ref) (w old : List Bool) : Prop :=
  old = refs.map (value w) ∧ ∀ r ∈ refs, valid w.length r

lemma read_value {refs : List Ref} {w old : List Bool} (h : related refs w old) (i : ℕ) :
    value w (read refs i) = old.getD i false := by
  rw [h.1]
  exact (List.getD_map refs fixed (value w)).symm

lemma read_valid {refs : List Ref} {w old : List Bool} (h : related refs w old) (i : ℕ) :
    valid w.length (read refs i) := by
  by_cases hi : i < refs.length
  · rw [read, List.getD_eq_getElem _ _ hi]
    exact h.2 _ (List.getElem_mem _)
  · rw [read, List.getD_eq_default _ _ (by omega)]
    trivial

lemma related_extend {refs : List Ref} {w old : List Bool} (h : related refs w old)
    (extra : List Gate) (r : Ref) (b : Bool) (hv : valid (run extra w).length r)
    (he : value (run extra w) r = b) :
    related (refs ++ [r]) (run extra w) (old ++ [b]) := by
  have same : refs.map (value (run extra w)) = refs.map (value w) := by
    apply List.map_congr_left
    intro q hq
    rcases q with c | i
    · rfl
    · exact run_prefix _ _ _ (h.2 _ hq)
  constructor
  · rw [List.map_append, same, ← h.1]
    simp [he]
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · have hqv := h.2 q hq
      cases q with
      | inl c => trivial
      | inr i =>
        change i < w.length at hqv
        change i < (run extra w).length
        rw [run_length]
        omega
    · simpa using (List.mem_singleton.mp hq ▸ hv : valid (run extra w).length q)

-- The emitter, its semantics, and the reference-table invariant come from L_meta_7073.
-- This pass allows arbitrary input substitutions, including true constants.
theorem compile (gs : List Gate) (hg : ∀ g ∈ gs, good g) (refs : List Ref) (n : ℕ) :
    ∃ (out : List Gate) (outRefs : List Ref), (∀ g ∈ out, good g) ∧ out.length ≤ gs.length ∧
      ∀ w old, w.length = n → related refs w old →
        related outRefs (run out w) (run gs old) := by
  induction gs generalizing refs n with
  | nil => exact ⟨[],refs,by simp,by simp,fun _ _ _ h => h⟩
  | cons g gs ih =>
    have hg' := hg g (by simp)
    let rs := g.inputs.map (read refs)
    let e := emit g.op n rs
    have he := emit_ok g.op n rs (by simpa [Set.mem_insert_iff] using hg'.1)
      (by simpa [rs] using hg'.2)
    let nextRefs := refs ++ [e.1]
    obtain ⟨tail, outRefs, htail, hsize, correct⟩ :=
      ih (fun h hm => hg h (by simp [hm])) nextRefs (n + e.2.length)
    refine ⟨e.2 ++ tail, outRefs, ?_, ?_, ?_⟩
    · intro h hm
      exact (List.mem_append.mp hm).elim (he.2.1 h) (htail h)
    · have one : e.2.length ≤ 1 := he.1
      simp only [List.length_append,List.length_cons]
      omega
    · intro w old hw hr
      have hv : ∀ r ∈ rs, valid n r := by
        intro r hr'
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp hr'
        rw [← hw]
        exact read_valid hr i
      obtain ⟨hv', he'⟩ := he.2.2.2 w hw hv
      have hm : rs.map (value w) = g.inputs.map (fun i => old.getD i false) := by
        dsimp only [rs]
        rw [List.map_map]
        exact List.map_congr_left (fun i _ => read_value hr i)
      rw [hm] at he'
      rw [run_append]
      change related outRefs (run tail (run e.2 w)) (run gs (step old g))
      exact correct _ _ (by rw [run_length,hw]) (related_extend hr _ _ _ hv' he')

def inputRef {n : ℕ} (v : Bool) : Fin (n+1) → Ref :=
  Fin.lastCases (.inl v) (fun i : Fin n => .inr i.val)

theorem evalInput {n : ℕ} (x : Fin n → Bool) (v : Bool) (i : Fin (n+1)) :
    value (List.ofFn x) (inputRef v i) = Fin.lastCases v x i := by
  induction i using Fin.lastCases with
  | last => simp [inputRef,value]
  | cast i => simp [inputRef,value,List.getD_eq_getElem?_getD]

theorem validInput {n : ℕ} (v : Bool) (i : Fin (n+1)) : valid n (inputRef v i) := by
  induction i using Fin.lastCases with
  | last => simp [inputRef,valid]
  | cast i => simp [inputRef,valid]

theorem bound (n : ℕ) (C : Circuit) (p : Equiv.Perm (Fin (n+1))) (v : Bool)
    (hf : FanInTwo C) : ∃ D : Circuit, FanInTwo D ∧ D.size ≤ max 1 C.size ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn ((Fin.lastCases v x) ∘ p)) := by
  let seed := List.ofFn (fun i => inputRef v (p i))
  obtain ⟨out,refs,hgood,hsize,hcorr⟩ := compile C.gates hf seed n
  let r := read refs C.output
  have hval (x : Fin n → Bool) : value (run out (List.ofFn x)) r =
      C.eval (List.ofFn ((Fin.lastCases v x) ∘ p)) := by
    apply read_value
    apply hcorr _ _ (by simp)
    constructor
    · simp only [seed,List.map_ofFn]
      congr 1
      funext i
      exact (evalInput x v (p i)).symm
    · rintro a ha
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
      simpa using validInput v (p i)
  cases hr : r with
  | inr idx =>
    exact ⟨⟨out,idx⟩,hgood,hsize.trans (Nat.le_max_right _ _),
      fun x => by
        change (run out (List.ofFn x)).getD idx false = _
        simpa only [hr,value] using hval x⟩
  | inl b =>
    let op := if b then GateOp.and else GateOp.or
    let D : Circuit := ⟨[⟨op,[]⟩],n⟩
    refine ⟨D,?_,Nat.le_max_left _ _,?_⟩
    · intro g hg
      have e : g = ⟨op,[]⟩ := by simpa [D] using hg
      subst g
      cases b <;> simp [op]
    · intro x
      rw [← hval x, hr]
      cases b <;> simp [D,op,Circuit.eval,Circuit.wires,GateOp.eval,value,List.getD_eq_getElem?_getD]

end PEqualNP.Outside.L_meta_17794_aux

theorem PEqualNP.Outside.L_meta_17794 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Equiv.Perm (Fin (x1 + (1 : ℕ)))) (x4 : Bool), PEqualNP.MetaComplexity.FanInTwo x2 → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x6 ∧ x6.size ≤ Max.max (1 : ℕ) x2.size ∧ ∀ (x7 : Fin x1 → Bool), x6.eval (List.ofFn x7) = x2.eval (List.ofFn ((fun (x8 : Fin (x1 + (1 : ℕ))) => Fin.lastCases x4 x7 x8) ∘ ⇑x3)) := PEqualNP.Outside.L_meta_17794_aux.bound
