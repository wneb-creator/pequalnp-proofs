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

end PEqualNP.Outside.L_meta_3457_aux.GateDrop
