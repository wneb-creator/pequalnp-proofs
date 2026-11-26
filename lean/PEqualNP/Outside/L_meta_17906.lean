import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17906

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm

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

def allowed (g : Gate) : Prop := g.op = .and ∨ g.op = .or

def binaryGate (g : Gate) : Prop := allowed g ∧ g.inputs.length = 2

def back (n : ℕ) (gs : List Gate) : Prop :=
  ∀ j (hj : j < gs.length), ∀ i ∈ gs[j].inputs, i < n + j

lemma back_append {n : ℕ} {a b : List Gate} (ha : back n a)
    (hb : back (n + a.length) b) : back n (a ++ b) := by
  intro j hj i hi
  by_cases h : j < a.length
  · rw [List.getElem_append_left h] at hi
    exact ha j h i hi
  · rw [List.getElem_append_right (by omega)] at hi
    have hb' := hb (j - a.length) (by simp at hj; omega) i hi
    omega

def binary (op : GateOp) (neutral : Bool) (n : ℕ) (a b : Ref) : Ref × List Gate :=
  match a, b with
  | .inl c, _ => (if c = neutral then b else .inl c, [])
  | _, .inl c => (if c = neutral then a else .inl c, [])
  | .inr i, .inr j => (.inr n, [⟨op, [i, j]⟩])

def emit (op : GateOp) (n : ℕ) (rs : List Ref) : Ref × List Gate :=
  match op, rs with
  | .and, [] => (.inl true, [])
  | .or, [] => (.inl false, [])
  | .and, [a] | .or, [a] => (a, [])
  | .and, a :: b :: _ => binary .and true n a b
  | .or, a :: b :: _ => binary .or false n a b
  | _, _ => (fixed, [])

lemma emit_ok (op : GateOp) (n : ℕ) (rs : List Ref)
    (hop : op = .and ∨ op = .or) (hl : rs.length ≤ 2)
    (hv : ∀ r ∈ rs, valid n r) :
    let e := emit op n rs
    e.2.length ≤ 1 ∧ (rs = [] → e.2 = []) ∧ (∀ g ∈ e.2, binaryGate g) ∧
      back n e.2 ∧
      ∀ w : List Bool, w.length = n →
        valid (run e.2 w).length e.1 ∧
          value (run e.2 w) e.1 = op.eval (rs.map (value w)) := by
  dsimp only
  rcases rs with _ | ⟨a, _ | ⟨b, _ | ⟨c, cs⟩⟩⟩
  · rcases hop with rfl | rfl <;> simp [emit, back, valid, value, GateOp.eval]
  · rcases hop with rfl | rfl
    · simpa [emit, back, run, GateOp.eval] using
        (fun (w : List Bool) (hw : w.length = n) => hw.symm ▸ hv a (by simp))
    · simpa [emit, back, run, GateOp.eval] using
        (fun (w : List Bool) (hw : w.length = n) => hw.symm ▸ hv a (by simp))
  · have ha := hv a (by simp)
    have hb := hv b (by simp)
    rcases hop with rfl | rfl <;>
      rcases a with (a | a) <;> rcases b with (b | b) <;>
      (try cases (show Bool from a)) <;> (try cases (show Bool from b)) <;>
      simp_all [emit, binary, run, step, binaryGate, allowed, back, valid, value, GateOp.eval,
        -List.getD_eq_getElem?_getD] <;>
      intro w hw <;> simp [← hw, getD_last, -List.getD_eq_getElem?_getD]
  · simp at hl

def read (refs : List Ref) (i : ℕ) : Ref := refs.getD i fixed

def related (refs : List Ref) (w old : List Bool) : Prop :=
  old = refs.map (value w) ∧ ∀ r ∈ refs, valid w.length r

lemma read_value {refs : List Ref} {w old : List Bool} (h : related refs w old) (i : ℕ) :
    value w (read refs i) = old.getD i false := by
  rw [h.1]
  exact (List.getD_map refs fixed (value w)).symm

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

lemma table_valid {refs : List Ref} {n : ℕ} (h : ∀ r ∈ refs, valid n r) (i : ℕ) :
    valid n (read refs i) := by
  by_cases hi : i < refs.length
  · rw [read, List.getD_eq_getElem _ _ hi]
    exact h _ (List.getElem_mem _)
  · rw [read, List.getD_eq_default _ _ (by omega)]
    trivial

lemma sweep (gs : List Gate) (hg : ∀ g ∈ gs, allowed g ∧ g.inputs.length ≤ 2)
    (refs : List Ref) (n : ℕ) (hvalid : ∀ r ∈ refs, valid n r) :
    ∃ (out : List Gate) (outRefs : List Ref),
      (∀ g ∈ out, binaryGate g) ∧ back n out ∧ out.length ≤ gs.length ∧
      ((∃ g ∈ gs, g.inputs = []) → out.length < gs.length) ∧
      ∀ w old, w.length = n → related refs w old →
        related outRefs (run out w) (run gs old) := by
  induction gs generalizing refs n with
  | nil => exact ⟨[], refs, by simp, by simp [back], by simp, by simp, fun _ _ _ h => h⟩
  | cons g gs ih =>
    have hg' := hg g (by simp)
    let rs := g.inputs.map (read refs)
    let e := emit g.op n rs
    have hv : ∀ r ∈ rs, valid n r := by
      intro r hr
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hr
      exact table_valid hvalid i
    obtain ⟨hlen, hzero, hgood, hback, heval⟩ :
        e.2.length ≤ 1 ∧ (rs = [] → e.2 = []) ∧ (∀ g ∈ e.2, binaryGate g) ∧
        back n e.2 ∧ ∀ w : List Bool, w.length = n →
          valid (run e.2 w).length e.1 ∧
            value (run e.2 w) e.1 = g.op.eval (rs.map (value w)) :=
      emit_ok g.op n rs hg'.1 (by simpa [rs] using hg'.2) hv
    have heValid : valid (n + e.2.length) e.1 := by
      obtain ⟨h, _⟩ := heval (List.replicate n false) (by simp)
      simpa [run_length] using h
    obtain ⟨tail, outRefs, htail, htback, hsize, hstrict, hcorrect⟩ :=
      ih (fun g hg₀ => hg g (by simp [hg₀])) (refs ++ [e.1]) (n + e.2.length) (by
        intro r hr
        rcases List.mem_append.mp hr with hr | hr
        · have h := hvalid r hr
          cases r with
          | inl _ => trivial
          | inr i => exact Nat.lt_of_lt_of_le h (Nat.le_add_right _ _)
        · rwa [List.mem_singleton.mp hr])
    refine ⟨e.2 ++ tail, outRefs, ?_, back_append hback htback, ?_, ?_, ?_⟩
    · intro g hg
      exact (List.mem_append.mp hg).elim (hgood g) (htail g)
    · simp only [List.length_append, List.length_cons]
      omega
    · rintro ⟨a, ha, hnil⟩
      rcases List.mem_cons.mp ha with rfl | ha
      · have hz := hzero (by simp [rs, hnil])
        simp [hz]
        omega
      · have hs := hstrict ⟨a, ha, hnil⟩
        simp only [List.length_append, List.length_cons]
        omega
    · intro w old hw hr
      obtain ⟨hv', he'⟩ := heval w hw
      have hm : rs.map (value w) = g.inputs.map (fun i => old.getD i false) := by
        dsimp only [rs]
        rw [List.map_map]
        exact List.map_congr_left (fun i _ => read_value hr i)
      rw [hm] at he'
      rw [run_append]
      change related outRefs (run tail (run e.2 w)) (run gs (step old g))
      exact hcorrect _ _ (by rw [run_length, hw]) (related_extend hr _ _ _ hv' he')

lemma ofFn_getD {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    (List.ofFn x).getD i false = if h : i < n then x ⟨i, h⟩ else false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  split_ifs <;> rfl

lemma gateAt_get {C : Circuit} {j : ℕ} (h : j < C.gates.length) :
    gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ h

lemma normalize {n : ℕ} (C : Circuit) (hM : Monotone2 C)
    (hnc : ∃ x y : Fin n → Bool, C.eval (List.ofFn x) ≠ C.eval (List.ofFn y)) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size ≤ C.size ∧
      ((∃ g ∈ C.gates, g.inputs = []) → D.size < C.size) ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x) := by
  let refs : List Ref := List.ofFn (fun i : Fin n => .inr i.val)
  have hr : ∀ r ∈ refs, valid n r := by
    intro r h
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp h
    exact i.isLt
  obtain ⟨gs, rs, hgood, hb, hsz, hlt, heval⟩ :=
    sweep C.gates (fun g hg => ⟨by simpa [allowed] using (hM g hg).1, (hM g hg).2⟩) refs n hr
  have hv (x : Fin n → Bool) : value (run gs (List.ofFn x)) (read rs C.output) =
      C.eval (List.ofFn x) := by
    have hinit : related refs (List.ofFn x) (List.ofFn x) := by
      refine ⟨?_, by simpa using hr⟩
      simp only [refs, List.map_ofFn]
      congr 1
      funext i
      simp [value, i.isLt]
    exact read_value (heval _ _ (by simp) hinit) C.output
  cases ho : read rs C.output with
  | inl b =>
    obtain ⟨x, y, hne⟩ := hnc
    exact (hne ((hv x).symm.trans ((congrArg (value (run gs (List.ofFn x))) ho).trans
      ((congrArg (value (run gs (List.ofFn y))) ho).symm.trans (hv y))))).elim
  | inr i =>
    refine ⟨⟨gs, i⟩, ⟨fun g hg => (hgood g hg).1, ?_, fun g hg => (hgood g hg).2⟩,
      hsz, hlt, ?_⟩
    · intro j hj k hk
      rw [gateAt_get hj] at hk
      exact hb j hj k hk
    · intro x
      rw [ho] at hv
      exact hv x

end PEqualNP.Outside.L_meta_17906

open PEqualNP.GenericRejection PEqualNP.HeptadCover

theorem PEqualNP.Outside.L_meta_17906 : (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → PEqualNP.GenericRejection.ComputesIncidence PEqualNP.HeptadCover.singerLines3 x1 → ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x4 ∧ PEqualNP.GenericRejection.ComputesIncidence PEqualNP.HeptadCover.singerLines3 x4 ∧ x4.size ≤ x1.size) := by
  intro C hmono hinc
  have inputs (X Y : Finset (Fin 13)) :
      ∃ x : Fin 26 → Bool, List.ofFn x = incidenceInput X Y := by
    let w := incidenceInput X Y
    have hlen : w.length = 26 := by simp [w, incidenceInput]
    have h : ∃ x : Fin w.length → Bool, List.ofFn x = w := ⟨w.get, List.ofFn_get w⟩
    rwa [hlen] at h
  obtain ⟨off, hoff⟩ := inputs ∅ ∅
  obtain ⟨onPair, hpair⟩ := inputs {0} {0}
  have hne : C.eval (List.ofFn off) ≠ C.eval (List.ofFn onPair) := by
    rw [hoff, hpair, hinc, hinc]
    decide
  obtain ⟨D, hAO, hsize, _, heq⟩ := L_meta_17906.normalize C hmono ⟨off, onPair, hne⟩
  refine ⟨D, hAO, ?_, hsize⟩
  intro X Y
  obtain ⟨x, hx⟩ := inputs X Y
  rw [← hinc X Y, ← hx, heq]
