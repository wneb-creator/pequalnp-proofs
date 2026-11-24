import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3451

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def decStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma decEvalMono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ)
    (f f' : ℕ → Bool) (h : ∀ i, f i = true → f' i = true) :
    op.eval (l.map f) = true → op.eval (l.map f') = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
    intro H x hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact h i (H (f i) ⟨i, hi, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
    rintro ⟨x, ⟨i, hi, rfl⟩, hx⟩
    exact ⟨f' i, ⟨i, hi, rfl⟩, h i hx⟩

lemma decFoldMono (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ a b : List Bool, a.length = b.length →
      (∀ i, a.getD i false = true → b.getD i false = true) →
      ∀ i, (gs.foldl decStep a).getD i false = true →
        (gs.foldl decStep b).getD i false = true := by
  induction gs with
  | nil => intro a b _ h; exact h
  | cons g gs ih =>
    intro a b hl h
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    · simp [decStep, hl]
    · intro i hi
      unfold decStep at hi ⊢
      by_cases hia : i < a.length
      · rw [List.getD_append _ _ _ _ hia] at hi
        rw [List.getD_append _ _ _ _ (by omega)]
        exact h i hi
      · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
        rw [List.getD_append_right _ _ _ _ (by omega)]
        rw [← hl]
        by_cases he : i - a.length = 0
        · rw [he] at hi ⊢
          simp only [List.getD_cons_zero] at hi ⊢
          exact decEvalMono g.op (hgs g List.mem_cons_self) _ _ _ (fun k => h k) hi
        · obtain ⟨m, hm⟩ : ∃ m, i - a.length = m + 1 := ⟨i - a.length - 1, by omega⟩
          rw [hm] at hi
          simp at hi

lemma decWireMono (n : ℕ) (C : Circuit) (hC : Monotone2 C)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true) (w : ℕ) :
    (C.wires (List.ofFn x)).getD w false = true →
      (C.wires (List.ofFn y)).getD w false = true := by
  refine decFoldMono C.gates (fun g hg => (hC g hg).1) _ _ (by simp) ?_ w
  intro i hi
  by_cases hin : i < n
  · rw [List.getD_eq_getElem _ _ (by simpa using hin), List.getElem_ofFn] at hi ⊢
    exact hxy ⟨i, hin⟩ hi
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
    cases hi

lemma lcFoldPrefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, gs.foldl decStep w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (decStep w g)
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    rw [List.foldl_cons, ht]
    simp [decStep]

lemma lcLength (gs : List Gate) (w : List Bool) :
    (gs.foldl decStep w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := lcFoldPrefix gs w
  rw [ht]; simp [hl]

lemma lcRead (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (gs.foldl decStep w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := lcFoldPrefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma lcGateValue (pre post : List Gate) (g : Gate) (w : List Bool) :
    ((pre ++ g :: post).foldl decStep w).getD (w.length + pre.length) false =
      g.op.eval (g.inputs.map fun i => (pre.foldl decStep w).getD i false) := by
  rw [List.foldl_append, List.foldl_cons]
  rw [lcRead _ _ _ (by simp [decStep, lcLength])]
  change ((pre.foldl decStep w) ++
    [g.op.eval (g.inputs.map fun i => (pre.foldl decStep w).getD i false)]).getD
      (w.length + pre.length) false = _
  rw [← lcLength pre w]
  simp

lemma lcSnocMono (w : List Bool) (a b : Bool) (hab : a = true → b = true) :
    ∀ i, (w ++ [a]).getD i false = true → (w ++ [b]).getD i false = true := by
  intro i hi
  by_cases h : i < w.length
  · rw [List.getD_append _ _ _ _ h] at hi ⊢
    exact hi
  · rw [List.getD_append_right _ _ _ _ (by omega)] at hi ⊢
    cases he : i - w.length with
    | zero => simpa [he] using hab (by simpa [he] using hi)
    | succ k => simp [he] at hi

lemma lcGetDReplace (pre post : List Gate) (g r d : Gate) (k : ℕ)
    (hk : k ≠ pre.length) : (pre ++ r :: post).getD k d = (pre ++ g :: post).getD k d := by
  by_cases h : k < pre.length
  · rw [List.getD_append _ _ _ _ h, List.getD_append _ _ _ _ h]
  · rw [List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by omega)]
    obtain ⟨a, ha⟩ : ∃ a, k - pre.length = a + 1 := ⟨k - pre.length - 1, by omega⟩
    simp [ha]

def lcPair (N : ℕ) (p l : Fin N) : Fin (N + N) → Bool :=
  fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)

lemma lcPairLe (N : ℕ) (p l : Fin N) (z : Fin (N + N) → Bool)
    (hp : z (Fin.castAdd N p) = true) (hl : z (Fin.natAdd N l) = true) :
    ∀ k, lcPair N p l k = true → z k = true := by
  intro k hk
  rcases of_decide_eq_true hk with rfl | rfl <;> assumption

lemma lcPairTrue (N : ℕ) (p l : Fin N) :
    lcPair N p l (Fin.castAdd N p) = true ∧ lcPair N p l (Fin.natAdd N l) = true := by
  simp [lcPair]

lemma lcPairCompleteness (N : ℕ) (I : Fin N → Fin N → Prop) (C D : Circuit)
    (hC : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
    (hD : Monotone2 D)
    (hle : ∀ z : Fin (N + N) → Bool,
      circuitFun (N + N) D z = true → circuitFun (N + N) C z = true)
    (heq : ∀ p l : Fin N, I p l →
      circuitFun (N + N) D (lcPair N p l) = circuitFun (N + N) C (lcPair N p l)) :
    ∀ z : Fin (N + N) → Bool, circuitFun (N + N) D z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true := by
  intro z
  constructor
  · intro hz
    exact (hC z).mp (hle z hz)
  · rintro ⟨p, l, hpl, hp, hl⟩
    have hpair : circuitFun (N + N) D (lcPair N p l) = true := by
      rw [heq p l hpl]
      exact (hC _).mpr ⟨p, l, hpl, (lcPairTrue N p l).1, (lcPairTrue N p l).2⟩
    exact decWireMono (N + N) D hD _ z (lcPairLe N p l z hp hl) D.output hpair

lemma lcReplacement (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (pre post : List Gate) (g r : Gate) (hsplit : C.gates = pre ++ g :: post)
    (hmono : Monotone2 C) (hreads : ReadsBack (N + N) C)
    (hfun : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
    (hrop : r.op = GateOp.and ∨ r.op = GateOp.or) (hrsize : r.inputs.length ≤ 2)
    (hrread : ∀ a ∈ r.inputs, a < N + N + pre.length)
    (hrle : ∀ z : Fin (N + N) → Bool,
      r.op.eval (r.inputs.map fun i => (pre.foldl decStep (List.ofFn z)).getD i false) = true →
      g.op.eval (g.inputs.map fun i => (pre.foldl decStep (List.ofFn z)).getD i false) = true)
    (hreq : ∀ p l : Fin N, I p l →
      r.op.eval (r.inputs.map fun i => (pre.foldl decStep (List.ofFn (lcPair N p l))).getD i false) =
      g.op.eval (g.inputs.map fun i => (pre.foldl decStep (List.ofFn (lcPair N p l))).getD i false)) :
    let D : Circuit := ⟨pre ++ r :: post, C.output⟩
    Monotone2 D ∧ ReadsBack (N + N) D ∧ D.size = C.size ∧
      (∀ z : Fin (N + N) → Bool, ∀ i,
        (D.wires (List.ofFn z)).getD i false = true → (C.wires (List.ofFn z)).getD i false = true) ∧
      (∀ p l : Fin N, I p l → D.wires (List.ofFn (lcPair N p l)) = C.wires (List.ofFn (lcPair N p l))) ∧
      (∀ z : Fin (N + N) → Bool, circuitFun (N + N) D z = true ↔
        ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) := by
  intro D
  have hm : Monotone2 D := by
    intro a ha
    change a ∈ pre ++ r :: post at ha
    simp only [List.mem_append, List.mem_cons] at ha
    rcases ha with ha | rfl | ha
    · exact hmono a (by rw [hsplit]; simp [ha])
    · exact ⟨hrop, hrsize⟩
    · exact hmono a (by rw [hsplit]; simp [ha])
  have hr : ReadsBack (N + N) D := by
    intro k hk a ha
    by_cases he : k = pre.length
    · subst k
      have har : a ∈ r.inputs := by simpa [gateAt, D] using ha
      exact hrread a har
    · have hg := lcGetDReplace pre post g r ⟨GateOp.or, []⟩ k he
      have hak : a ∈ (gateAt C k).inputs := by
        change a ∈ ((pre ++ r :: post).getD k ⟨GateOp.or, []⟩).inputs at ha
        rw [hg] at ha
        simpa only [gateAt, hsplit] using ha
      exact hreads k (by simpa [hsplit, D] using hk) a hak
  have hle : ∀ z : Fin (N + N) → Bool, ∀ i,
      (D.wires (List.ofFn z)).getD i false = true → (C.wires (List.ofFn z)).getD i false = true := by
    intro z
    change ∀ i, ((pre ++ r :: post).foldl decStep (List.ofFn z)).getD i false = true →
      (C.gates.foldl decStep (List.ofFn z)).getD i false = true
    rw [hsplit, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_cons]
    apply decFoldMono post (fun a ha => (hmono a (by rw [hsplit]; simp [ha])).1)
    · simp [decStep]
    · exact lcSnocMono _ _ _ (hrle z)
  have heq : ∀ p l : Fin N, I p l →
      D.wires (List.ofFn (lcPair N p l)) = C.wires (List.ofFn (lcPair N p l)) := by
    intro p l hpl
    change (pre ++ r :: post).foldl decStep _ = C.gates.foldl decStep _
    rw [hsplit, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_cons]
    simp only [decStep, hreq p l hpl]
  refine ⟨hm, hr, by simp [Circuit.size, hsplit, D], hle, heq, ?_⟩
  apply lcPairCompleteness N I C D hfun hm (fun z => hle z C.output)
  intro p l hpl
  exact congrArg (fun ws : List Bool => ws.getD C.output false) (heq p l hpl)


def lcImproves (N : ℕ) (I : Fin N → Fin N → Prop) (C D : Circuit) : Prop :=
  Monotone2 D ∧ ReadsBack (N + N) D ∧ D.size = C.size ∧
    (∀ z : Fin (N + N) → Bool, ∀ i,
      (D.wires (List.ofFn z)).getD i false = true → (C.wires (List.ofFn z)).getD i false = true) ∧
    (∀ p l : Fin N, I p l → D.wires (List.ofFn (lcPair N p l)) = C.wires (List.ofFn (lcPair N p l))) ∧
    (∀ z : Fin (N + N) → Bool, circuitFun (N + N) D z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)

lemma lcCircuitGate (n : ℕ) (C : Circuit) (pre post : List Gate) (g : Gate)
    (hsplit : C.gates = pre ++ g :: post) (z : Fin n → Bool) :
    (C.wires (List.ofFn z)).getD (n + pre.length) false =
      g.op.eval (g.inputs.map fun i => (pre.foldl decStep (List.ofFn z)).getD i false) := by
  change (C.gates.foldl decStep (List.ofFn z)).getD (n + pre.length) false = _
  rw [hsplit]
  simpa only [List.length_ofFn] using lcGateValue pre post g (List.ofFn z)

lemma lcZeroSupport (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (pre post : List Gate) (g : Gate) (hsplit : C.gates = pre ++ g :: post)
    (hmono : Monotone2 C) (hreads : ReadsBack (N + N) C)
    (hfun : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
    (hnone : ∀ p l : Fin N, I p l →
      (C.wires (List.ofFn (lcPair N p l))).getD (N + N + pre.length) false = false) :
    ∃ D : Circuit, lcImproves N I C D ∧
      (gateAt D pre.length).op = GateOp.or ∧
      (∀ z : Fin (N + N) → Bool, (D.wires (List.ofFn z)).getD (N + N + pre.length) false = false) := by
  let r : Gate := ⟨GateOp.or, []⟩
  let D : Circuit := ⟨pre ++ r :: post, C.output⟩
  refine ⟨D, ?_, ?_, ?_⟩
  · exact lcReplacement N I C pre post g r hsplit hmono hreads hfun (Or.inr rfl)
      (by simp [r]) (by simp [r]) (by simp [r, GateOp.eval]) (by
        intro p l hpl
        rw [← lcCircuitGate (N + N) C pre post g hsplit, hnone p l hpl]
        rfl)
  · simp [gateAt, D, r]
  · intro z
    rw [lcCircuitGate (N + N) D pre post r rfl]
    rfl

lemma lcPairPoint (N : ℕ) (p l p' : Fin N) :
    lcPair N p l (Fin.castAdd N p') = true ↔ p' = p := by
  have hcross : Fin.castAdd N p' ≠ Fin.natAdd N l := by
    intro h
    have hh := congrArg Fin.val h
    change p'.val = N + l.val at hh
    omega
  constructor
  · intro hx
    rcases of_decide_eq_true hx with h | h
    · exact Fin.ext (congrArg (fun k : Fin (N + N) => k.val) h)
    · exact (hcross h).elim
  · intro h; subst p'; exact decide_eq_true (Or.inl rfl)

lemma lcPairLine (N : ℕ) (p l l' : Fin N) :
    lcPair N p l (Fin.natAdd N l') = true ↔ l' = l := by
  have hcross : Fin.natAdd N l' ≠ Fin.castAdd N p := by
    intro h
    have hh := congrArg Fin.val h
    change N + l'.val = p.val at hh
    omega
  constructor
  · intro hx
    rcases of_decide_eq_true hx with h | h
    · exact (hcross h).elim
    · apply Fin.ext
      have hh := congrArg (fun k : Fin (N + N) => k.val) h
      change N + l'.val = N + l.val at hh
      omega
  · intro h; subst l'; exact decide_eq_true (Or.inr rfl)

lemma lcGetDOfFn {n : ℕ} (z : Fin n → Bool) (i : Fin n) :
    (List.ofFn z).getD i.val false = z i := by simp

lemma lcRawPairEval (N : ℕ) (pre : List Gate) (p l : Fin N) (z : Fin (N + N) → Bool) :
    GateOp.and.eval ([p.val, N + l.val].map fun i =>
      (pre.foldl decStep (List.ofFn z)).getD i false) =
      (z (Fin.castAdd N p) && z (Fin.natAdd N l)) := by
  have hp : (pre.foldl decStep (List.ofFn z)).getD p.val false = z (Fin.castAdd N p) := by
    rw [lcRead _ _ _ (by simp only [List.length_ofFn]; omega)]
    exact lcGetDOfFn z (Fin.castAdd N p)
  have hl : (pre.foldl decStep (List.ofFn z)).getD (N + l.val) false = z (Fin.natAdd N l) := by
    rw [lcRead _ _ _ (by simp only [List.length_ofFn]; omega)]
    exact lcGetDOfFn z (Fin.natAdd N l)
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
  rw [hp, hl]

lemma lcOneSupport (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (pre post : List Gate) (g : Gate) (hsplit : C.gates = pre ++ g :: post)
    (hmono : Monotone2 C) (hreads : ReadsBack (N + N) C)
    (hfun : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
    (p0 l0 : Fin N) (hI : I p0 l0)
    (haccept : (C.wires (List.ofFn (lcPair N p0 l0))).getD (N + N + pre.length) false = true)
    (honly : ∀ p l : Fin N, I p l →
      (C.wires (List.ofFn (lcPair N p l))).getD (N + N + pre.length) false = true →
        p = p0 ∧ l = l0) :
    ∃ D : Circuit, lcImproves N I C D ∧
      (gateAt D pre.length).op = GateOp.and ∧
      (∀ z : Fin (N + N) → Bool,
        (D.wires (List.ofFn z)).getD (N + N + pre.length) false = true →
        ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) := by
  let r : Gate := ⟨GateOp.and, [p0.val, N + l0.val]⟩
  let D : Circuit := ⟨pre ++ r :: post, C.output⟩
  refine ⟨D, ?_, ?_, ?_⟩
  · apply lcReplacement N I C pre post g r hsplit hmono hreads hfun (Or.inl rfl)
    · simp [r]
    · intro a ha
      simp only [r, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl <;> omega
    · intro z hz
      change GateOp.and.eval _ = true at hz
      rw [lcRawPairEval] at hz
      simp only [Bool.and_eq_true] at hz
      rw [← lcCircuitGate (N + N) C pre post g hsplit]
      exact decWireMono (N + N) C hmono _ z (lcPairLe N p0 l0 z hz.1 hz.2)
        (N + N + pre.length) haccept
    · intro p l hpl
      change GateOp.and.eval _ = _
      rw [lcRawPairEval, ← lcCircuitGate (N + N) C pre post g hsplit,
        Bool.eq_iff_iff, Bool.and_eq_true, lcPairPoint, lcPairLine]
      constructor
      · rintro ⟨rfl, rfl⟩
        exact haccept
      · intro ht
        obtain ⟨hp, hl⟩ := honly p l hpl ht
        exact ⟨hp.symm, hl.symm⟩
  · simp [gateAt, D, r]
  · intro z hz
    rw [lcCircuitGate (N + N) D pre post r rfl] at hz
    change GateOp.and.eval _ = true at hz
    rw [lcRawPairEval] at hz
    simp only [Bool.and_eq_true] at hz
    exact ⟨p0, l0, hI, hz.1, hz.2⟩

lemma lcStarEval (N : ℕ) (pre : List Gate) (p : Fin N) (w : ℕ)
    (z : Fin (N + N) → Bool) :
    GateOp.and.eval ([p.val, w].map fun i =>
      (pre.foldl decStep (List.ofFn z)).getD i false) =
      (z (Fin.castAdd N p) && (pre.foldl decStep (List.ofFn z)).getD w false) := by
  have hp : (pre.foldl decStep (List.ofFn z)).getD p.val false = z (Fin.castAdd N p) := by
    rw [lcRead _ _ _ (by simp only [List.length_ofFn]; omega)]
    exact lcGetDOfFn z (Fin.castAdd N p)
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
    id_eq, Bool.and_true, hp]

lemma lcStarSupport (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (pre post : List Gate) (g : Gate) (hsplit : C.gates = pre ++ g :: post)
    (hmono : Monotone2 C) (hreads : ReadsBack (N + N) C)
    (hfun : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
    (p0 : Fin N) (w : ℕ) (hw : w < N + N + pre.length)
    (hstar : ∀ p l : Fin N, I p l →
      (C.wires (List.ofFn (lcPair N p l))).getD (N + N + pre.length) false = true → p = p0)
    (hwire : ∀ z : Fin (N + N) → Bool,
      (pre.foldl decStep (List.ofFn z)).getD w false = true ↔
      ∃ l : Fin N, I p0 l ∧
        (C.wires (List.ofFn (lcPair N p0 l))).getD (N + N + pre.length) false = true ∧
        z (Fin.natAdd N l) = true) :
    ∃ D : Circuit, lcImproves N I C D ∧
      (gateAt D pre.length).op = GateOp.and ∧
      (∀ z : Fin (N + N) → Bool,
        (D.wires (List.ofFn z)).getD (N + N + pre.length) false = true →
        ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) := by
  let r : Gate := ⟨GateOp.and, [p0.val, w]⟩
  let D : Circuit := ⟨pre ++ r :: post, C.output⟩
  have hle : ∀ z : Fin (N + N) → Bool,
      r.op.eval (r.inputs.map fun i => (pre.foldl decStep (List.ofFn z)).getD i false) = true →
      g.op.eval (g.inputs.map fun i => (pre.foldl decStep (List.ofFn z)).getD i false) = true := by
    intro z hz
    change GateOp.and.eval _ = true at hz
    rw [lcStarEval, Bool.and_eq_true] at hz
    obtain ⟨l, _, haccept, hl⟩ := (hwire z).mp hz.2
    rw [← lcCircuitGate (N + N) C pre post g hsplit]
    exact decWireMono (N + N) C hmono _ z (lcPairLe N p0 l z hz.1 hl)
      (N + N + pre.length) haccept
  refine ⟨D, ?_, ?_, ?_⟩
  · apply lcReplacement N I C pre post g r hsplit hmono hreads hfun (Or.inl rfl)
    · simp [r]
    · intro a ha
      simp only [r, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl <;> omega
    · exact hle
    · intro p l hpl
      rw [Bool.eq_iff_iff]
      constructor
      · exact hle _
      · intro ht
        have haccept : (C.wires (List.ofFn (lcPair N p l))).getD
            (N + N + pre.length) false = true := by
          rw [lcCircuitGate (N + N) C pre post g hsplit]
          exact ht
        have hp := hstar p l hpl haccept
        subst p
        change GateOp.and.eval _ = true
        rw [lcStarEval, Bool.and_eq_true]
        exact ⟨(lcPairTrue N p0 l).1,
          (hwire _).mpr ⟨l, hpl, haccept, (lcPairTrue N p0 l).2⟩⟩
  · simp [gateAt, D, r]
  · intro z hz
    rw [lcCircuitGate (N + N) D pre post r rfl] at hz
    change GateOp.and.eval _ = true at hz
    rw [lcStarEval, Bool.and_eq_true] at hz
    obtain ⟨l, hpl, _, hl⟩ := (hwire z).mp hz.2
    exact ⟨p0, l, hpl, hz.1, hl⟩

end PEqualNP.Outside.L_meta_3451
