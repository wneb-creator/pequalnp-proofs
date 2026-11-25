import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1896_aux.OrSignature

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def gateValue (g : Gate) (w : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def step (w : List Bool) (g : Gate) : List Bool := w ++ [gateValue g w]

def isOr (g : Gate) : Bool :=
  match g.op with
  | .or => true
  | _ => false

def trace : List Gate → List Bool → List Bool
  | [], _ => []
  | g :: gs, w =>
    if isOr g then w.getD (g.inputs.headD 0) false :: trace gs (step w g)
    else trace gs (step w g)

def relation (x y z : List Bool) : Prop :=
  x.length = y.length ∧ x.length = z.length ∧
    ∀ i, x.getD i false = true → y.getD i false = true → z.getD i false = true

lemma trace_length (gs : List Gate) (w : List Bool) :
    (trace gs w).length = gs.countP isOr := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    cases h : isOr g <;> simp [trace, h, ih]

lemma or_preserve (a b c d e f : Bool)
    (he : a = true → c = true → e = true)
    (hf : b = true → d = true → f = true) (same : a = c) :
    (a || b) = true → (c || d) = true → (e || f) = true := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> simp_all

lemma gate_preserve (x y z : List Bool) (h : relation x y z) (g : Gate)
    (hm : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (same : isOr g = true →
      x.getD (g.inputs.headD 0) false = y.getD (g.inputs.headD 0) false) :
    gateValue g x = true → gateValue g y = true → gateValue g z = true := by
  obtain ⟨op, args⟩ := g
  rcases hm with ⟨hop, hlen⟩
  change op = GateOp.and ∨ op = GateOp.or at hop
  rcases hop with rfl | rfl
  · simp only [gateValue, GateOp.eval, List.all_eq_true, List.mem_map]
    intro hx hy
    rintro b ⟨i, hi, rfl⟩
    exact h.2.2 i (hx _ ⟨i, hi, rfl⟩) (hy _ ⟨i, hi, rfl⟩)
  · cases args with
    | nil => simp [gateValue, GateOp.eval]
    | cons i tail =>
      cases tail with
      | nil => simpa [gateValue, GateOp.eval] using h.2.2 i
      | cons j rest =>
        cases rest with
        | cons k rest => simp at hlen
        | nil =>
          simpa [gateValue, GateOp.eval] using
            or_preserve (x.getD i false) (x.getD j false)
              (y.getD i false) (y.getD j false) (z.getD i false) (z.getD j false)
              (h.2.2 i) (h.2.2 j) (same rfl)

lemma relation_step (x y z : List Bool) (h : relation x y z) (g : Gate)
    (hg : gateValue g x = true → gateValue g y = true → gateValue g z = true) :
    relation (step x g) (step y g) (step z g) := by
  refine ⟨by simp [step, h.1], by simp [step, h.2.1], ?_⟩
  intro i hx hy
  by_cases hi : i < x.length
  · have hj : i < y.length := h.1 ▸ hi
    have hk : i < z.length := h.2.1 ▸ hi
    simp only [step, List.getD_append _ _ _ _ hi,
      List.getD_append _ _ _ _ hj, List.getD_append _ _ _ _ hk] at hx hy ⊢
    exact h.2.2 i hx hy
  · by_cases he : i = x.length
    · subst i
      have hx' : gateValue g x = true := by
        simpa [step, List.getD_eq_getElem?_getD] using hx
      have hy' : gateValue g y = true := by
        simpa [step, h.1, List.getD_eq_getElem?_getD] using hy
      simpa [step, h.2.1, List.getD_eq_getElem?_getD] using hg hx' hy'
    · have hlarge : x.length + 1 ≤ i := by omega
      have hlarge' : (step x g).length ≤ i := by simpa [step] using hlarge
      have : (step x g).getD i false = false := List.getD_eq_default _ _ hlarge'
      simp_all

lemma preserve (gs : List Gate)
    (mono : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧
      g.inputs.length ≤ 2) (x y z : List Bool) (h : relation x y z)
    (same : trace gs x = trace gs y) :
    relation (gs.foldl step x) (gs.foldl step y) (gs.foldl step z) := by
  induction gs generalizing x y z with
  | nil => exact h
  | cons g gs ih =>
    have tail : trace gs (step x g) = trace gs (step y g) := by
      cases ho : isOr g <;> simp_all [trace]
    have first : isOr g = true →
        x.getD (g.inputs.headD 0) false = y.getD (g.inputs.headD 0) false := by
      intro ho
      simp only [trace, ho, ↓reduceIte, List.cons.injEq] at same
      exact same.1
    exact ih (fun k hk => mono k (by simp [hk])) _ _ _
      (relation_step x y z h g (gate_preserve x y z h g (mono g (by simp)) first)) tail

def signature (gs : List Gate) (x : List Bool) : Fin (gs.countP isOr) → Bool :=
  fun i => (trace gs x).getD i.val false

lemma signature_eq (gs : List Gate) (x y : List Bool)
    (same : signature gs x = signature gs y) : trace gs x = trace gs y := by
  apply List.ext_getElem
  · rw [trace_length, trace_length]
  · intro i hi hj
    have hk : i < gs.countP isOr := by simpa [trace_length] using hi
    have he := congrFun same ⟨i, hk⟩
    simpa [signature, List.getD_eq_getElem, hi, hj] using he

lemma or_count_filter (gs : List Gate) :
    (Finset.univ.filter (fun i : Fin gs.length => isOr (gs.get i) = true)).card =
      gs.countP isOr := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    show (Finset.univ.filter
      (fun i : Fin (gs.length + 1) => isOr ((g :: gs).get i) = true)).card = _
    rw [Fin.card_filter_univ_succ]
    simp only [List.countP_cons]
    split_ifs with h₁ h₂ h₂
    · simpa using ih
    · exact absurd h₁ h₂
    · exact absurd h₂ h₁
    · simpa using ih

lemma or_count (gs : List Gate) :
    {i : Fin gs.length | (gs.get i).op = GateOp.or}.ncard = gs.countP isOr := by
  have he : {i : Fin gs.length | (gs.get i).op = GateOp.or} =
      ↑(Finset.univ.filter (fun i : Fin gs.length => isOr (gs.get i) = true)) := by
    ext i
    simp only [Set.mem_ofPred_eq, Finset.coe_filter, Finset.mem_univ, true_and]
    unfold isOr
    cases (gs.get i).op <;> simp
  rw [he, Set.ncard_coe_finset, or_count_filter]

lemma accepted_card_bound {α : Type} [Fintype α] {n : ℕ}
    (C : Circuit) (mono : Monotone2 C) (points : α → Fin n → Bool)
    (yes : ∀ a, circuitFun n C (points a) = true)
    (separate : ∀ a b, a ≠ b →
      circuitFun n C (fun i => points a i && points b i) = false) :
    Fintype.card α ≤ 2 ^ C.gates.countP isOr := by
  have inj : Function.Injective (fun a => signature C.gates (List.ofFn (points a))) := by
    intro a b he
    by_contra hab
    have rel : relation (List.ofFn (points a)) (List.ofFn (points b))
        (List.ofFn fun i => points a i && points b i) := by
      refine ⟨by simp, by simp, ?_⟩
      intro i ha hb
      by_cases hi : i < n
      · simp [List.getD_eq_getElem?_getD, hi] at ha hb ⊢
        exact ⟨ha, hb⟩
      · simp [List.getD_eq_getElem?_getD, hi] at ha
    have hall := preserve C.gates mono _ _ _ rel (signature_eq _ _ _ he)
    have hit := hall.2.2 C.output (yes a) (yes b)
    have miss := separate a b hab
    change circuitFun n C (fun i => points a i && points b i) = true at hit
    rw [miss] at hit
    cases hit
  simpa using Fintype.card_le_of_injective _ inj

lemma accepted_card_bound_ncard {α : Type} [Fintype α] {n : ℕ}
    (C : Circuit) (mono : Monotone2 C) (points : α → Fin n → Bool)
    (yes : ∀ a, circuitFun n C (points a) = true)
    (separate : ∀ a b, a ≠ b →
      circuitFun n C (fun i => points a i && points b i) = false) :
    Fintype.card α ≤
      2 ^ {i : Fin C.gates.length | (C.gates.get i).op = GateOp.or}.ncard := by
  rw [or_count]
  exact accepted_card_bound C mono points yes separate

lemma circuit_true_mono {n : ℕ} (C : Circuit) (mono : Monotone2 C)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true) :
    circuitFun n C x = true → circuitFun n C y = true := by
  have rel : relation (List.ofFn x) (List.ofFn x) (List.ofFn y) := by
    refine ⟨rfl, by simp, ?_⟩
    intro i hx _
    by_cases hi : i < n
    · simp [List.getD_eq_getElem?_getD, hi] at hx ⊢
      exact hxy ⟨i, hi⟩ hx
    · simp [List.getD_eq_getElem?_getD, hi] at hx
  intro hx
  exact (preserve C.gates mono _ _ _ rel rfl).2.2 C.output hx hx

end PEqualNP.Outside.L_meta_1896_aux.OrSignature
