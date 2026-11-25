import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3457_aux.GateDrop

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

def zeroGate : Gate := ⟨.or, []⟩

def cut (C : Circuit) (j : ℕ) : Circuit :=
  ⟨C.gates.set j zeroGate, C.output⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def WLe (a b : List Bool) : Prop :=
  a.length = b.length ∧ ∀ i, a.getD i false = true → b.getD i false = true

lemma getD_set (gs : List Gate) (j k : ℕ) :
    (gs.set j zeroGate).getD k zeroGate =
      if k = j then zeroGate else gs.getD k zeroGate := by
  induction gs generalizing j k with
  | nil => simp
  | cons g gs ih =>
    cases j <;> cases k <;> simp
    simpa only [List.getD_eq_getElem?_getD] using ih _ _

lemma mem_set (gs : List Gate) (j : ℕ) (g : Gate)
    (h : g ∈ gs.set j zeroGate) : g = zeroGate ∨ g ∈ gs := by
  induction gs generalizing j with
  | nil => simp at h
  | cons a gs ih =>
    cases j with
    | zero =>
      simp only [List.set_cons_zero, List.mem_cons] at h
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)
    | succ j =>
      simp only [List.set_cons_succ, List.mem_cons] at h
      rcases h with rfl | h
      · exact Or.inr (List.mem_cons_self)
      · rcases ih j h with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)

lemma cut_mono (C : Circuit) (j : ℕ) (h : Monotone2 C) : Monotone2 (cut C j) := by
  intro g hg
  rcases mem_set C.gates j g hg with rfl | hg
  · simp [zeroGate]
  · exact h g hg

lemma cut_size (C : Circuit) (j : ℕ) : (cut C j).size = C.size := by
  simp [cut, Circuit.size]

lemma cut_back (n : ℕ) (C : Circuit) (j : ℕ) (h : ReadsBack n C) :
    ReadsBack n (cut C j) := by
  intro k hk i hi
  change i ∈ ((C.gates.set j zeroGate).getD k zeroGate).inputs at hi
  rw [getD_set] at hi
  by_cases heq : k = j
  · simp [heq, zeroGate] at hi
  · rw [if_neg heq] at hi
    exact h k (by simpa [cut] using hk) i hi

lemma cut_gate (C : Circuit) (j : ℕ) : gateAt (cut C j) j = zeroGate := by
  change (C.gates.set j zeroGate).getD j zeroGate = zeroGate
  rw [getD_set, if_pos rfl]

lemma append_le (a b : List Bool) (u v : Bool) (h : WLe a b)
    (huv : u = true → v = true) : WLe (a ++ [u]) (b ++ [v]) := by
  have hlen : a.length = b.length := h.1
  refine ⟨by simp [hlen], ?_⟩
  intro i hi
  by_cases hit : i < a.length
  · rw [List.getD_append a [u] false i hit] at hi
    rw [List.getD_append b [v] false i (by omega)]
    exact h.2 i hi
  · rw [List.getD_append_right a [u] false i (by omega)] at hi
    rw [List.getD_append_right b [v] false i (by omega), ← h.1]
    cases hs : i - a.length with
    | zero => simpa [hs] using huv (by simpa [hs] using hi)
    | succ q => simp [hs] at hi

lemma gate_le (g : Gate) (a b : List Bool)
    (hop : g.op = .and ∨ g.op = .or) (h : WLe a b) :
    g.op.eval (g.inputs.map fun i => a.getD i false) = true →
      g.op.eval (g.inputs.map fun i => b.getD i false) = true := by
  rcases hop with hop | hop
  · simp only [hop, GateOp.eval, List.all_map, Function.comp_def, id_eq]
    intro hg
    exact List.all_eq_true.mpr fun i hi => h.2 i (List.all_eq_true.mp hg i hi)
  · simp only [hop, GateOp.eval, List.any_map, Function.comp_def, id_eq]
    intro hg
    obtain ⟨i, hi, ht⟩ := List.any_eq_true.mp hg
    exact List.any_eq_true.mpr ⟨i, hi, h.2 i ht⟩

lemma fold_le (gs : List Gate) (a b : List Bool)
    (hmono : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) (h : WLe a b) :
    WLe (gs.foldl step a) (gs.foldl step b) := by
  induction gs generalizing a b with
  | nil => exact h
  | cons g gs ih =>
    simp only [List.foldl_cons]
    apply ih _ _ (fun q hq => hmono q (List.mem_cons_of_mem _ hq))
    exact append_le a b _ _ h (gate_le g a b (hmono g (List.mem_cons_self)) h)

lemma fold_length (gs : List Gate) (a : List Bool) :
    (gs.foldl step a).length = a.length + gs.length := by
  induction gs generalizing a with
  | nil => simp
  | cons g gs ih => simp [List.foldl_cons, ih, step, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

lemma fold_read (gs : List Gate) (a : List Bool) (i : ℕ) (hi : i < a.length) :
    (gs.foldl step a).getD i false = a.getD i false := by
  induction gs generalizing a with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (step a g) (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi

lemma fold_head (g : Gate) (gs : List Gate) (a : List Bool) :
    ((g :: gs).foldl step a).getD a.length false =
      g.op.eval (g.inputs.map fun i => a.getD i false) := by
  rw [List.foldl_cons, fold_read gs (step a g) a.length (by simp [step])]
  simp [step, List.getD_eq_getElem?_getD]

lemma fold_cut_le (gs : List Gate) (j : ℕ) (a : List Bool)
    (hmono : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) :
    WLe ((gs.set j zeroGate).foldl step a) (gs.foldl step a) := by
  induction gs generalizing j a with
  | nil => exact ⟨rfl, fun _ h => h⟩
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [List.set_cons_zero, List.foldl_cons]
      apply fold_le gs _ _ (fun q hq => hmono q (List.mem_cons_of_mem _ hq))
      apply append_le a a _ _ ⟨rfl, fun _ h => h⟩
      simp [zeroGate, GateOp.eval]
    | succ j =>
      simp only [List.set_cons_succ, List.foldl_cons]
      exact ih j (step a g) (fun q hq => hmono q (List.mem_cons_of_mem _ hq))

lemma fold_cut_eq (gs : List Gate) (j : ℕ) (a : List Bool)
    (hj : j < gs.length)
    (hoff : (gs.foldl step a).getD (a.length + j) false = false) :
    (gs.set j zeroGate).foldl step a = gs.foldl step a := by
  induction gs generalizing j a with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [Nat.add_zero] at hoff
      rw [fold_head] at hoff
      simp only [List.set_cons_zero, List.foldl_cons]
      have heq : step a zeroGate = step a g := by
        change a ++ [false] = a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)]
        rw [hoff]
      rw [heq]
    | succ j =>
      simp only [List.set_cons_succ, List.foldl_cons]
      apply ih j (step a g) (by simpa using hj)
      simpa only [List.foldl_cons, step, List.length_append, List.length_singleton,
        Nat.add_assoc, Nat.add_comm 1 j] using hoff

lemma wires_cut_le (C : Circuit) (j : ℕ) (a : List Bool) (hc : Monotone2 C) :
    WLe ((cut C j).wires a) (C.wires a) :=
  fold_cut_le C.gates j a (fun g hg => (hc g hg).1)

lemma wires_cut_eq (C : Circuit) (j : ℕ) (a : List Bool)
    (hj : j < C.gates.length) (hoff : (C.wires a).getD (a.length + j) false = false) :
    (cut C j).wires a = C.wires a := fold_cut_eq C.gates j a hj hoff

lemma input_le (n : ℕ) (x y : Fin n → Bool)
    (h : ∀ i, x i = true → y i = true) : WLe (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp, ?_⟩
  intro i hi
  by_cases hit : i < n
  · have hx : x ⟨i, hit⟩ = true := by
      simpa [List.getD_eq_getElem?_getD, hit] using hi
    simpa [List.getD_eq_getElem?_getD, hit] using h ⟨i, hit⟩ hx
  · simp [List.getD_eq_getElem?_getD, hit] at hi

lemma eval_mono (n : ℕ) (C : Circuit) (hc : Monotone2 C)
    (x y : Fin n → Bool) (h : ∀ i, x i = true → y i = true) :
    C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true :=
  (fold_le C.gates _ _ (fun g hg => (hc g hg).1) (input_le n x y h)).2 C.output

lemma bool_eq (a b : Bool) (h : (a = true ↔ b = true)) : a = b := by
  cases a <;> cases b <;> simp_all

lemma cut_preserves_generated {ι : Type*} (n : ℕ) (C : Circuit) (j : ℕ)
    (tests : ι → Fin n → Bool) (hc : Monotone2 C) (hj : j < C.gates.length)
    (spec : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
      ∃ t : ι, ∀ i, tests t i = true → x i = true)
    (hoff : ∀ t : ι, (C.wires (List.ofFn (tests t))).getD (n + j) false = false) :
    circuitFun n (cut C j) = circuitFun n C := by
  funext x
  apply bool_eq
  constructor
  · exact (wires_cut_le C j (List.ofFn x) hc).2 C.output
  · intro hx
    obtain ⟨t, ht⟩ := (spec x).mp hx
    have hcpos : C.eval (List.ofFn (tests t)) = true :=
      (spec (tests t)).mpr ⟨t, fun _ h => h⟩
    have hdpos : (cut C j).eval (List.ofFn (tests t)) = true := by
      change ((cut C j).wires (List.ofFn (tests t))).getD C.output false = true
      rw [wires_cut_eq C j _ hj (by simpa using hoff t)]
      exact hcpos
    exact eval_mono n (cut C j) (cut_mono C j hc) (tests t) x ht hdpos

lemma cut_preserves_zero (C : Circuit) (j : ℕ) (a : List Bool) (w : ℕ)
    (hc : Monotone2 C) (hoff : (C.wires a).getD w false = false) :
    ((cut C j).wires a).getD w false = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have h' := (wires_cut_le C j a hc).2 w h
  have bad : (false : Bool) = true := hoff.symm.trans h'
  cases bad

lemma erase_unused_positive {ι : Type*} (n : ℕ) (C : Circuit) (j : ℕ)
    (tests : ι → Fin n → Bool) (hc : Monotone2 C) (hb : ReadsBack n C)
    (hj : j < C.gates.length)
    (spec : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
      ∃ t : ι, ∀ i, tests t i = true → x i = true)
    (hoff : ∀ t : ι, (C.wires (List.ofFn (tests t))).getD (n + j) false = false) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧ D.size = C.size ∧
      circuitFun n D = circuitFun n C ∧ (gateAt D j).op = .or ∧
      (∀ a : List Bool, ∀ w : ℕ, (C.wires a).getD w false = false →
        (D.wires a).getD w false = false) := by
  refine ⟨cut C j, cut_mono C j hc, cut_back n C j hb, cut_size C j,
    cut_preserves_generated n C j tests hc hj spec hoff, ?_, ?_⟩
  · rw [cut_gate]
    rfl
  · intro a w h
    exact cut_preserves_zero C j a w hc h

lemma cut_and_inherited (C : Circuit) (j k : ℕ)
    (h : (gateAt (cut C j) k).op = .and) : (gateAt C k).op = .and := by
  change ((C.gates.set j zeroGate).getD k zeroGate).op = .and at h
  rw [getD_set] at h
  by_cases heq : k = j
  · simp [heq, zeroGate] at h
  · simpa [heq, gateAt, zeroGate, List.getD_eq_getElem?_getD] using h

lemma cut_incidence (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (j : ℕ) (hc : Monotone2 C) (hj : j < C.gates.length)
    (spec : ∀ x : Fin (N + N) → Bool, circuitFun (N + N) C x = true ↔
      ∃ p l : Fin N, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true)
    (hoff : ∀ p l : Fin N, I p l →
      (C.wires (List.ofFn (fun k : Fin (N + N) =>
        decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)))).getD (N + N + j) false = false) :
    circuitFun (N + N) (cut C j) = circuitFun (N + N) C := by
  let tests : {e : Fin N × Fin N // I e.1 e.2} → Fin (N + N) → Bool :=
    fun e k => decide (k = Fin.castAdd N e.val.1 ∨ k = Fin.natAdd N e.val.2)
  apply cut_preserves_generated (N + N) C j tests hc hj
  · intro x
    constructor
    · intro hx
      obtain ⟨p, l, he, hp, hl⟩ := (spec x).mp hx
      refine ⟨⟨(p, l), he⟩, ?_⟩
      intro k hk
      have hpair : k = Fin.castAdd N p ∨ k = Fin.natAdd N l :=
        of_decide_eq_true hk
      rcases hpair with rfl | rfl
      · exact hp
      · exact hl
    · rintro ⟨e, he⟩
      apply (spec x).mpr
      exact ⟨e.val.1, e.val.2, e.property,
        he _ (by simp [tests]), he _ (by simp [tests])⟩
  · intro e
    exact hoff e.val.1 e.val.2 e.property

noncomputable def andIndices (C : Circuit) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter fun j => (gateAt C j).op = .and

lemma mem_andIndices (C : Circuit) (j : ℕ) :
    j ∈ andIndices C ↔ j < C.gates.length ∧ (gateAt C j).op = .and := by
  classical
  simp [andIndices]

lemma cut_and_count (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (hand : (gateAt C j).op = .and) :
    (andIndices (cut C j)).card < (andIndices C).card := by
  classical
  have sub : andIndices (cut C j) ⊆ andIndices C := by
    intro k hk
    obtain ⟨hklen, hkop⟩ := (mem_andIndices (cut C j) k).mp hk
    exact (mem_andIndices C k).mpr
      ⟨by simpa [cut] using hklen, cut_and_inherited C j k hkop⟩
  have ne : andIndices (cut C j) ≠ andIndices C := by
    intro heq
    have hjmem : j ∈ andIndices (cut C j) := by
      rw [heq]
      exact (mem_andIndices C j).mpr ⟨hj, hand⟩
    have hbad := ((mem_andIndices (cut C j) j).mp hjmem).2
    rw [cut_gate] at hbad
    cases hbad
  exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨sub, ne⟩)

lemma normalize_useful {ι : Type*} (n : ℕ) (tests : ι → Fin n → Bool)
    (C : Circuit) (hc : Monotone2 C) (hb : ReadsBack n C)
    (spec : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
      ∃ t : ι, ∀ i, tests t i = true → x i = true) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧ D.size = C.size ∧
      circuitFun n D = circuitFun n C ∧
      (∀ a : List Bool, ∀ w : ℕ, (C.wires a).getD w false = false →
        (D.wires a).getD w false = false) ∧
      (∀ j, (gateAt D j).op = .and → (gateAt C j).op = .and) ∧
      ∀ j < D.gates.length, (gateAt D j).op = .and →
        ∃ t : ι, (D.wires (List.ofFn (tests t))).getD (n + j) false = true := by
  classical
  have main : ∀ m : ℕ, ∀ C : Circuit, (andIndices C).card = m →
      Monotone2 C → ReadsBack n C →
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
        ∃ t : ι, ∀ i, tests t i = true → x i = true) →
      ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧ D.size = C.size ∧
        circuitFun n D = circuitFun n C ∧
        (∀ a : List Bool, ∀ w : ℕ, (C.wires a).getD w false = false →
          (D.wires a).getD w false = false) ∧
        (∀ j, (gateAt D j).op = .and → (gateAt C j).op = .and) ∧
        ∀ j < D.gates.length, (gateAt D j).op = .and →
          ∃ t : ι, (D.wires (List.ofFn (tests t))).getD (n + j) false = true := by
    intro m
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      intro C hcard hc hb spec
      by_cases useful : ∀ j < C.gates.length, (gateAt C j).op = .and →
          ∃ t : ι, (C.wires (List.ofFn (tests t))).getD (n + j) false = true
      · exact ⟨C, hc, hb, rfl, rfl, fun _ _ h => h, fun _ h => h, useful⟩
      · push_neg at useful
        obtain ⟨j, hj, hand, off⟩ := useful
        have hoff : ∀ t : ι,
            (C.wires (List.ofFn (tests t))).getD (n + j) false = false :=
          fun t => Bool.eq_false_iff.mpr (off t)
        have hfun := cut_preserves_generated n C j tests hc hj spec hoff
        have hsmall : (andIndices (cut C j)).card < m := by
          rw [← hcard]
          exact cut_and_count C j hj hand
        have hspec : ∀ x : Fin n → Bool, (cut C j).eval (List.ofFn x) = true ↔
            ∃ t : ι, ∀ i, tests t i = true → x i = true := by
          intro x
          change circuitFun n (cut C j) x = true ↔ _
          rw [hfun]
          exact spec x
        obtain ⟨D, hDm, hDb, hDs, hDf, hDz, hDa, hDu⟩ :=
          ih _ hsmall (cut C j) rfl (cut_mono C j hc) (cut_back n C j hb) hspec
        refine ⟨D, hDm, hDb, hDs.trans (cut_size C j), hDf.trans hfun, ?_, ?_, hDu⟩
        · intro a w hw
          exact hDz a w (cut_preserves_zero C j a w hc hw)
        · intro k hk
          exact cut_and_inherited C j k (hDa k hk)
  exact main _ C rfl hc hb spec

lemma normalize_incidence_useful (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (hc : Monotone2 C) (hb : ReadsBack (N + N) C)
    (spec : ∀ x : Fin (N + N) → Bool, circuitFun (N + N) C x = true ↔
      ∃ p l : Fin N, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true)
    (single : ∀ j < C.gates.length, (gateAt C j).op = .and →
      ∀ v : Fin (N + N),
        (C.wires (List.ofFn (fun k => decide (k = v)))).getD (N + N + j) false = false) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack (N + N) D ∧ D.size = C.size ∧
      circuitFun (N + N) D = circuitFun (N + N) C ∧
      (∀ j < D.gates.length, (gateAt D j).op = .and →
        ∀ v : Fin (N + N),
          (D.wires (List.ofFn (fun k => decide (k = v)))).getD (N + N + j) false = false) ∧
      (∀ a : List Bool, ∀ w : ℕ, (C.wires a).getD w false = false →
        (D.wires a).getD w false = false) ∧
      ∀ j < D.gates.length, (gateAt D j).op = .and →
        ∃ p l : Fin N, I p l ∧
          (D.wires (List.ofFn (fun k : Fin (N + N) =>
            decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)))).getD
              (N + N + j) false = true := by
  let tests : {e : Fin N × Fin N // I e.1 e.2} → Fin (N + N) → Bool :=
    fun e k => decide (k = Fin.castAdd N e.val.1 ∨ k = Fin.natAdd N e.val.2)
  have hspec : ∀ x : Fin (N + N) → Bool, C.eval (List.ofFn x) = true ↔
      ∃ t, ∀ i, tests t i = true → x i = true := by
    intro x
    constructor
    · intro hx
      obtain ⟨p, l, he, hp, hl⟩ := (spec x).mp hx
      refine ⟨⟨(p, l), he⟩, ?_⟩
      intro k hk
      have hpair : k = Fin.castAdd N p ∨ k = Fin.natAdd N l := of_decide_eq_true hk
      rcases hpair with rfl | rfl
      · exact hp
      · exact hl
    · rintro ⟨e, he⟩
      exact (spec x).mpr ⟨e.val.1, e.val.2, e.property,
        he _ (by simp [tests]), he _ (by simp [tests])⟩
  obtain ⟨D, hDm, hDb, hDs, hDf, hDz, hDa, hDu⟩ :=
    normalize_useful (N + N) tests C hc hb hspec
  refine ⟨D, hDm, hDb, hDs, hDf, ?_, hDz, ?_⟩
  · intro j hj hand v
    have hjC : j < C.gates.length := by
      have hlength : D.gates.length = C.gates.length := hDs
      omega
    exact hDz _ _ (single j hjC (hDa j hand) v)
  · intro j hj hand
    obtain ⟨e, he⟩ := hDu j hj hand
    exact ⟨e.val.1, e.val.2, e.property, he⟩

def replace (C : Circuit) (j : ℕ) (g : Gate) : Circuit :=
  ⟨C.gates.set j g, C.output⟩

lemma getD_replace (gs : List Gate) (j : ℕ) (g : Gate) (k : ℕ)
    (hj : j < gs.length) :
    (gs.set j g).getD k zeroGate = if k = j then g else gs.getD k zeroGate := by
  induction gs generalizing j k with
  | nil => simp at hj
  | cons a gs ih =>
    cases j <;> cases k <;> simp
    simpa only [List.getD_eq_getElem?_getD] using ih _ _ (by simpa using hj)

lemma mem_replace (gs : List Gate) (j : ℕ) (g q : Gate)
    (h : q ∈ gs.set j g) : q = g ∨ q ∈ gs := by
  induction gs generalizing j with
  | nil => simp at h
  | cons a gs ih =>
    cases j with
    | zero =>
      simp only [List.set_cons_zero, List.mem_cons] at h
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)
    | succ j =>
      simp only [List.set_cons_succ, List.mem_cons] at h
      rcases h with rfl | h
      · exact Or.inr List.mem_cons_self
      · rcases ih j h with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)

lemma replace_mono (C : Circuit) (j : ℕ) (g : Gate) (h : Monotone2 C)
    (hg : (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) :
    Monotone2 (replace C j g) := by
  intro q hq
  rcases mem_replace C.gates j g q hq with rfl | hq
  · exact hg
  · exact h q hq

lemma replace_size (C : Circuit) (j : ℕ) (g : Gate) :
    (replace C j g).size = C.size := by
  simp [replace, Circuit.size]

lemma replace_back (n : ℕ) (C : Circuit) (j : ℕ) (g : Gate)
    (hj : j < C.gates.length) (h : ReadsBack n C)
    (hg : ∀ i ∈ g.inputs, i < n + j) : ReadsBack n (replace C j g) := by
  intro k hk i hi
  change i ∈ ((C.gates.set j g).getD k zeroGate).inputs at hi
  rw [getD_replace _ _ _ _ hj] at hi
  by_cases heq : k = j
  · subst k
    simp only [ite_true] at hi
    exact hg i hi
  · rw [if_neg heq] at hi
    exact h k (by simpa [replace] using hk) i hi

lemma replace_gate (C : Circuit) (j : ℕ) (g : Gate) (hj : j < C.gates.length) :
    gateAt (replace C j g) j = g := by
  change (C.gates.set j g).getD j zeroGate = g
  rw [getD_replace _ _ _ _ hj, if_pos rfl]

lemma fold_replace_le (gs : List Gate) (j : ℕ) (g : Gate) (a : List Bool)
    (hj : j < gs.length)
    (hmono : ∀ q ∈ gs, q.op = .and ∨ q.op = .or)
    (happrox : g.op.eval (g.inputs.map fun i => ((gs.take j).foldl step a).getD i false) = true →
      (gs.foldl step a).getD (a.length + j) false = true) :
    WLe ((gs.set j g).foldl step a) (gs.foldl step a) := by
  induction gs generalizing j a with
  | nil => simp at hj
  | cons q gs ih =>
    cases j with
    | zero =>
      simp only [List.take_zero, List.foldl_nil, Nat.add_zero] at happrox
      rw [fold_head] at happrox
      simp only [List.set_cons_zero, List.foldl_cons]
      apply fold_le gs _ _ (fun r hr => hmono r (List.mem_cons_of_mem _ hr))
      exact append_le a a _ _ ⟨rfl, fun _ h => h⟩ happrox
    | succ j =>
      simp only [List.set_cons_succ, List.foldl_cons]
      apply ih j (step a q) (by simpa using hj)
        (fun r hr => hmono r (List.mem_cons_of_mem _ hr))
      simpa only [List.take_succ_cons, List.foldl_cons, step,
        List.length_append, List.length_singleton, Nat.add_assoc,
        Nat.add_comm 1 j] using happrox

lemma fold_replace_eq (gs : List Gate) (j : ℕ) (g : Gate) (a : List Bool)
    (hj : j < gs.length)
    (heq : g.op.eval (g.inputs.map fun i => ((gs.take j).foldl step a).getD i false) =
      (gs.foldl step a).getD (a.length + j) false) :
    (gs.set j g).foldl step a = gs.foldl step a := by
  induction gs generalizing j a with
  | nil => simp at hj
  | cons q gs ih =>
    cases j with
    | zero =>
      simp only [List.take_zero, List.foldl_nil, Nat.add_zero] at heq
      rw [fold_head] at heq
      simp only [List.set_cons_zero, List.foldl_cons]
      have hs : step a g = step a q := by
        unfold step
        rw [heq]
      rw [hs]
    | succ j =>
      simp only [List.set_cons_succ, List.foldl_cons]
      apply ih j (step a q) (by simpa using hj)
      simpa only [List.take_succ_cons, List.foldl_cons, step,
        List.length_append, List.length_singleton, Nat.add_assoc,
        Nat.add_comm 1 j] using heq

def pairGate {n : ℕ} (p q : Fin n) : Gate := ⟨.and, [p.val, q.val]⟩

def pairInput {n : ℕ} (p q : Fin n) : Fin n → Bool :=
  fun k => decide (k = p ∨ k = q)

lemma pairGate_prefix (n : ℕ) (gs : List Gate) (p q : Fin n) (x : Fin n → Bool) :
    (pairGate p q).op.eval ((pairGate p q).inputs.map fun i =>
      (gs.foldl step (List.ofFn x)).getD i false) = (x p && x q) := by
  simp only [pairGate, GateOp.eval, List.map_cons, List.map_nil,
    List.all_cons, List.all_nil, id_eq, Bool.and_true]
  rw [fold_read gs _ p.val (by simpa using p.isLt),
    fold_read gs _ q.val (by simpa using q.isLt)]
  simp [List.getD_eq_getElem?_getD]

lemma pair_below_wire (n : ℕ) (C : Circuit) (j : ℕ) (p q : Fin n)
    (hc : Monotone2 C)
    (hseed : (C.wires (List.ofFn (pairInput p q))).getD (n + j) false = true)
    (x : Fin n → Bool) (hx : (x p && x q) = true) :
    (C.wires (List.ofFn x)).getD (n + j) false = true := by
  have hboth : x p = true ∧ x q = true := by simpa using hx
  obtain ⟨hp, hq⟩ := hboth
  apply (fold_le C.gates _ _ (fun g hg => (hc g hg).1)
    (input_le n (pairInput p q) x ?_)).2 (n + j) hseed
  intro k hk
  have hpair : k = p ∨ k = q := of_decide_eq_true hk
  rcases hpair with rfl | rfl
  · exact hp
  · exact hq

lemma wires_pair_le (n : ℕ) (C : Circuit) (j : ℕ) (p q : Fin n)
    (hc : Monotone2 C) (hj : j < C.gates.length)
    (hseed : (C.wires (List.ofFn (pairInput p q))).getD (n + j) false = true)
    (x : Fin n → Bool) :
    WLe ((replace C j (pairGate p q)).wires (List.ofFn x)) (C.wires (List.ofFn x)) := by
  apply fold_replace_le C.gates j (pairGate p q) (List.ofFn x) hj
    (fun g hg => (hc g hg).1)
  rw [pairGate_prefix, List.length_ofFn]
  exact pair_below_wire n C j p q hc hseed x

lemma pair_replacement_preserves {ι : Type*} (n : ℕ) (C : Circuit) (j : ℕ)
    (p q : Fin n) (tests : ι → Fin n → Bool) (hc : Monotone2 C)
    (hj : j < C.gates.length)
    (spec : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
      ∃ t : ι, ∀ i, tests t i = true → x i = true)
    (hseed : (C.wires (List.ofFn (pairInput p q))).getD (n + j) false = true)
    (hmatch : ∀ t : ι, (C.wires (List.ofFn (tests t))).getD (n + j) false =
      (tests t p && tests t q)) :
    circuitFun n (replace C j (pairGate p q)) = circuitFun n C := by
  have hmono : Monotone2 (replace C j (pairGate p q)) :=
    replace_mono C j _ hc (by simp [pairGate])
  funext x
  apply bool_eq
  constructor
  · exact (wires_pair_le n C j p q hc hj hseed x).2 C.output
  · intro hx
    obtain ⟨t, ht⟩ := (spec x).mp hx
    have hcpos : C.eval (List.ofFn (tests t)) = true :=
      (spec (tests t)).mpr ⟨t, fun _ h => h⟩
    have heq : (replace C j (pairGate p q)).wires (List.ofFn (tests t)) =
        C.wires (List.ofFn (tests t)) := by
      apply fold_replace_eq C.gates j (pairGate p q) _ hj
      rw [pairGate_prefix, List.length_ofFn]
      exact (hmatch t).symm
    have hdpos : (replace C j (pairGate p q)).eval (List.ofFn (tests t)) = true := by
      change ((replace C j (pairGate p q)).wires (List.ofFn (tests t))).getD C.output false = true
      rw [heq]
      exact hcpos
    exact eval_mono n _ hmono (tests t) x ht hdpos

lemma pair_replacement_zero (n : ℕ) (C : Circuit) (j : ℕ) (p q : Fin n)
    (hc : Monotone2 C) (hj : j < C.gates.length)
    (hseed : (C.wires (List.ofFn (pairInput p q))).getD (n + j) false = true)
    (x : Fin n → Bool) (w : ℕ)
    (hoff : (C.wires (List.ofFn x)).getD w false = false) :
    ((replace C j (pairGate p q)).wires (List.ofFn x)).getD w false = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have h' := (wires_pair_le n C j p q hc hj hseed x).2 w h
  have bad : (false : Bool) = true := hoff.symm.trans h'
  cases bad

lemma pair_replacement {ι : Type*} (n : ℕ) (C : Circuit) (j : ℕ)
    (p q : Fin n) (tests : ι → Fin n → Bool) (hc : Monotone2 C)
    (hb : ReadsBack n C) (hj : j < C.gates.length)
    (spec : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
      ∃ t : ι, ∀ i, tests t i = true → x i = true)
    (hseed : (C.wires (List.ofFn (pairInput p q))).getD (n + j) false = true)
    (hmatch : ∀ t : ι, (C.wires (List.ofFn (tests t))).getD (n + j) false =
      (tests t p && tests t q)) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧ D.size = C.size ∧
      circuitFun n D = circuitFun n C ∧ gateAt D j = pairGate p q ∧
      (∀ x : Fin n → Bool, ∀ w : ℕ, (C.wires (List.ofFn x)).getD w false = false →
        (D.wires (List.ofFn x)).getD w false = false) := by
  refine ⟨replace C j (pairGate p q), replace_mono C j _ hc (by simp [pairGate]),
    replace_back n C j _ hj hb ?_, replace_size C j _,
    pair_replacement_preserves n C j p q tests hc hj spec hseed hmatch,
    replace_gate C j _ hj, ?_⟩
  · intro i hi
    have hip : i = p.val ∨ i = q.val := by simpa [pairGate] using hi
    rcases hip with rfl | rfl <;> omega
  · intro x w hw
    exact pair_replacement_zero n C j p q hc hj hseed x w hw

lemma fold_replace_slot (gs : List Gate) (j : ℕ) (g : Gate) (a : List Bool)
    (hj : j < gs.length) :
    ((gs.set j g).foldl step a).getD (a.length + j) false =
      g.op.eval (g.inputs.map fun i => ((gs.take j).foldl step a).getD i false) := by
  induction gs generalizing j a with
  | nil => simp at hj
  | cons q gs ih =>
    cases j with
    | zero =>
      simpa only [List.set_cons_zero, List.take_zero, List.foldl_nil, Nat.add_zero]
        using fold_head g gs a
    | succ j =>
      simp only [List.set_cons_succ, List.take_succ_cons, List.foldl_cons]
      simpa only [step, List.length_append, List.length_singleton, Nat.add_assoc,
        Nat.add_comm 1 j] using ih j (step a q) (by simpa using hj)

lemma pair_replacement_slot (n : ℕ) (C : Circuit) (j : ℕ) (p q : Fin n)
    (hj : j < C.gates.length) (x : Fin n → Bool) :
    ((replace C j (pairGate p q)).wires (List.ofFn x)).getD (n + j) false =
      (x p && x q) := by
  have h := fold_replace_slot C.gates j (pairGate p q) (List.ofFn x) hj
  rw [pairGate_prefix, List.length_ofFn] at h
  exact h

lemma pair_and_inherited (n : ℕ) (C : Circuit) (j : ℕ) (p q : Fin n)
    (hj : j < C.gates.length) (hand : (gateAt C j).op = .and)
    (k : ℕ) (hk : (gateAt (replace C j (pairGate p q)) k).op = .and) :
    (gateAt C k).op = .and := by
  change ((C.gates.set j (pairGate p q)).getD k zeroGate).op = .and at hk
  rw [getD_replace _ _ _ _ hj] at hk
  by_cases heq : k = j
  · subst k
    exact hand
  · simpa [heq, gateAt, zeroGate, List.getD_eq_getElem?_getD] using hk

lemma cross_pair_eq_true (N : ℕ) (p l r s : Fin N) :
    ((pairInput (Fin.castAdd N r) (Fin.natAdd N s)) (Fin.castAdd N p) &&
      (pairInput (Fin.castAdd N r) (Fin.natAdd N s)) (Fin.natAdd N l)) = true ↔
      p = r ∧ l = s := by
  constructor
  · intro h
    have hboth :
        (pairInput (Fin.castAdd N r) (Fin.natAdd N s)) (Fin.castAdd N p) = true ∧
        (pairInput (Fin.castAdd N r) (Fin.natAdd N s)) (Fin.natAdd N l) = true := by
      simpa using h
    obtain ⟨hp, hl⟩ := hboth
    have hp' : Fin.castAdd N p = Fin.castAdd N r ∨
        Fin.castAdd N p = Fin.natAdd N s := of_decide_eq_true hp
    have hl' : Fin.natAdd N l = Fin.castAdd N r ∨
        Fin.natAdd N l = Fin.natAdd N s := of_decide_eq_true hl
    constructor
    · rcases hp' with hp' | hp'
      · exact Fin.ext (congrArg (fun z : Fin (N + N) => z.val) hp')
      · have hv := congrArg Fin.val hp'
        change p.val = N + s.val at hv
        omega
    · rcases hl' with hl' | hl'
      · have hv := congrArg Fin.val hl'
        change N + l.val = r.val at hv
        omega
      · have hv := congrArg Fin.val hl'
        change N + l.val = N + s.val at hv
        exact Fin.ext (by omega)
  · rintro ⟨rfl, rfl⟩
    simp [pairInput]

lemma repair_single_incident_edge (N : ℕ) (I : Fin N → Fin N → Prop)
    [DecidableRel I] (C : Circuit) (j : ℕ) (p l : Fin N)
    (hc : Monotone2 C) (hb : ReadsBack (N + N) C)
    (hj : j < C.gates.length) (hand : (gateAt C j).op = .and) (hI : I p l)
    (spec : ∀ x : Fin (N + N) → Bool, circuitFun (N + N) C x = true ↔
      ∃ r s : Fin N, I r s ∧ x (Fin.castAdd N r) = true ∧ x (Fin.natAdd N s) = true)
    (single : ∀ k < C.gates.length, (gateAt C k).op = .and →
      ∀ v : Fin (N + N),
        (C.wires (List.ofFn (fun a => decide (a = v)))).getD (N + N + k) false = false)
    (hseed : (C.wires (List.ofFn (pairInput (Fin.castAdd N p) (Fin.natAdd N l)))).getD
      (N + N + j) false = true)
    (honly : ∀ r s : Fin N, I r s →
      (C.wires (List.ofFn (pairInput (Fin.castAdd N r) (Fin.natAdd N s)))).getD
        (N + N + j) false = true → r = p ∧ s = l) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack (N + N) D ∧ D.size = C.size ∧
      circuitFun (N + N) D = circuitFun (N + N) C ∧
      (∀ k < D.gates.length, (gateAt D k).op = .and →
        ∀ v : Fin (N + N),
          (D.wires (List.ofFn (fun a => decide (a = v)))).getD (N + N + k) false = false) ∧
      (∀ r s : Fin N, ¬ I r s →
        (D.wires (List.ofFn (pairInput (Fin.castAdd N r) (Fin.natAdd N s)))).getD
          (N + N + j) false = false) ∧
      (∀ x : Fin (N + N) → Bool, ∀ w : ℕ,
        (C.wires (List.ofFn x)).getD w false = false →
          (D.wires (List.ofFn x)).getD w false = false) := by
  let tests : {e : Fin N × Fin N // I e.1 e.2} → Fin (N + N) → Bool :=
    fun e => pairInput (Fin.castAdd N e.val.1) (Fin.natAdd N e.val.2)
  have hspec : ∀ x : Fin (N + N) → Bool, C.eval (List.ofFn x) = true ↔
      ∃ t, ∀ i, tests t i = true → x i = true := by
    intro x
    constructor
    · intro hx
      obtain ⟨r, s, he, hr, hs⟩ := (spec x).mp hx
      refine ⟨⟨(r, s), he⟩, ?_⟩
      intro k hk
      have hpair : k = Fin.castAdd N r ∨ k = Fin.natAdd N s := of_decide_eq_true hk
      rcases hpair with rfl | rfl
      · exact hr
      · exact hs
    · rintro ⟨e, he⟩
      exact (spec x).mpr ⟨e.val.1, e.val.2, e.property,
        he _ (by simp [tests, pairInput]), he _ (by simp [tests, pairInput])⟩
  have hmatch : ∀ e, (C.wires (List.ofFn (tests e))).getD (N + N + j) false =
      (tests e (Fin.castAdd N p) && tests e (Fin.natAdd N l)) := by
    intro e
    apply bool_eq
    constructor
    · intro he
      obtain ⟨hp, hl⟩ := honly e.val.1 e.val.2 e.property he
      exact (cross_pair_eq_true N p l e.val.1 e.val.2).mpr ⟨hp.symm, hl.symm⟩
    · intro he
      obtain ⟨hp, hl⟩ := (cross_pair_eq_true N p l e.val.1 e.val.2).mp he
      have heq : tests e = pairInput (Fin.castAdd N p) (Fin.natAdd N l) := by
        simp only [tests, ← hp, ← hl]
      rw [heq]
      exact hseed
  let D := replace C j (pairGate (Fin.castAdd N p) (Fin.natAdd N l))
  have hDm : Monotone2 D := replace_mono C j _ hc (by simp [pairGate])
  have hDb : ReadsBack (N + N) D := by
    apply replace_back (N + N) C j _ hj hb
    intro i hi
    have hip : i = (Fin.castAdd N p).val ∨ i = (Fin.natAdd N l).val := by
      simpa [pairGate] using hi
    rcases hip with rfl | rfl <;> omega
  have hzero : ∀ x : Fin (N + N) → Bool, ∀ w : ℕ,
      (C.wires (List.ofFn x)).getD w false = false →
        (D.wires (List.ofFn x)).getD w false = false :=
    pair_replacement_zero (N + N) C j _ _ hc hj hseed
  refine ⟨D, hDm, hDb, replace_size C j _,
    pair_replacement_preserves (N + N) C j _ _ tests hc hj hspec hseed hmatch,
    ?_, ?_, hzero⟩
  · intro k hk hkop v
    have hkC : k < C.gates.length := by simpa [D, replace] using hk
    exact hzero _ _ (single k hkC
      (pair_and_inherited (N + N) C j _ _ hj hand k hkop) v)
  · intro r s hn
    rw [pair_replacement_slot (N + N) C j _ _ hj]
    apply Bool.eq_false_iff.mpr
    intro ht
    obtain ⟨hp, hl⟩ := (cross_pair_eq_true N p l r s).mp ht
    exact hn (by simpa [← hp, ← hl] using hI)

end PEqualNP.Outside.L_meta_3457_aux.GateDrop
