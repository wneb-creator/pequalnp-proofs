import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2590.EssentialPruning

open PEqualNP.CircuitLowerBounds

def Correct {α : Type} (P N : α → Prop) (f : α → Bool) : Prop :=
  (∀ x, P x → f x = true) ∧ (∀ x, N x → f x = false)

def Impure {α : Type} (N : α → Prop) (f : α → Bool) : Prop :=
  ∃ x, N x ∧ f x = true

lemma impure_mono {α : Type} {N : α → Prop} {f g : α → Bool}
    (hfg : f ≤ g) (hf : Impure N f) : Impure N g := by
  obtain ⟨x, hx, hxf⟩ := hf
  exact ⟨x, hx, hfg x hxf⟩

lemma not_impure_of_false_negatives {α : Type} {N : α → Prop} {f : α → Bool}
    (hf : ∀ x, N x → f x = false) : ¬ Impure N f := by
  rintro ⟨x, hx, hxf⟩
  rw [hf x hx] at hxf
  cases hxf

def Bad {α : Type} (P N : α → Prop) (f : α → Bool) : Prop :=
  (∃ x, N x ∧ f x = true) ∧
    ∃ x y, P x ∧ P y ∧ x ≠ y ∧ f x = true ∧ f y = true

lemma bad_mono {α : Type} {P N : α → Prop} {f g : α → Bool}
    (hfg : f ≤ g) (hf : Bad P N f) : Bad P N g := by
  obtain ⟨⟨z, hz, hzf⟩, x, y, hx, hy, hxy, hxf, hyf⟩ := hf
  exact ⟨⟨z, hz, hfg z hzf⟩, x, y, hx, hy, hxy, hfg x hxf, hfg y hyf⟩

lemma not_bad_of_false_negatives {α : Type} {P N : α → Prop} {f : α → Bool}
    (hf : ∀ x, N x → f x = false) : ¬ Bad P N f := by
  rintro ⟨⟨x, hx, hxf⟩, _⟩
  rw [hf x hx] at hxf
  cases hxf

lemma true_after_replacement (f : Bool → Bool) (hf : Monotone f)
    (old replacement : Bool) (hold : f old = true)
    (hcover : f false = false → replacement = true) :
    f replacement = true := by
  cases hz : f false with
  | false =>
      have hr := hcover hz
      simpa only [hr] using hf (Bool.le_true old) hold
  | true => exact hf (Bool.false_le replacement) hz

lemma context_replacement {α ι : Type} (P N : α → Prop)
    (context : α → Bool → ι → Bool) (out : ι)
    (hcontext : ∀ x, Monotone (context x)) (old replacement : α → Bool)
    (hshrink : replacement ≤ old)
    (hold : Correct P N (fun x => context x (old x) out))
    (hcover : ∀ x, P x → context x false out = false → replacement x = true) :
    Correct P N (fun x => context x (replacement x) out) ∧
      ∀ x, context x (replacement x) ≤ context x (old x) := by
  refine ⟨⟨?_, ?_⟩, fun x => hcontext x (hshrink x)⟩
  · intro x hx
    exact true_after_replacement (fun b => context x b out)
      (fun _ _ h => hcontext x h out) (old x) (replacement x)
      (hold.1 x hx) (hcover x hx)
  · intro x hx
    have hle := hcontext x (hshrink x) out
    have hzero : context x (old x) out = false := hold.2 x hx
    rw [hzero] at hle
    exact le_antisymm hle (Bool.false_le _)

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def WireLE (a b : List Bool) : Prop :=
  ∀ i, a.getD i false = true → b.getD i false = true

lemma gate_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l : List ℕ) (f f' : ℕ → Bool) (h : ∀ i, f i = true → f' i = true) :
    op.eval (l.map f) = true → op.eval (l.map f') = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
    intro H x hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact h i (H (f i) ⟨i, hi, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
    rintro ⟨x, ⟨i, hi, rfl⟩, hx⟩
    exact ⟨f' i, ⟨i, hi, rfl⟩, h i hx⟩

lemma fold_mono (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ a b : List Bool, a.length = b.length → WireLE a b →
      WireLE (gs.foldl step a) (gs.foldl step b) := by
  induction gs with
  | nil => intro a b _ h; exact h
  | cons g gs ih =>
    intro a b hl h
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    · simp [step, hl]
    · intro i hi
      unfold step at hi ⊢
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
          exact gate_eval_mono g.op (hgs g List.mem_cons_self) _ _ _ (fun k => h k) hi
        · obtain ⟨m, hm⟩ : ∃ m, i - a.length = m + 1 := ⟨i - a.length - 1, by omega⟩
          rw [hm] at hi
          simp at hi

lemma append_singleton_mono (p : List Bool) {a b : Bool} (hab : a ≤ b) :
    WireLE (p ++ [a]) (p ++ [b]) := by
  intro i hi
  by_cases hip : i < p.length
  · rw [List.getD_append _ _ _ _ hip] at hi ⊢
    exact hi
  · rw [List.getD_append_right _ _ _ _ (by omega)] at hi ⊢
    cases he : i - p.length with
    | zero =>
        simp only [he, List.getD_cons_zero] at hi ⊢
        exact hab hi
    | succ j => simp [he] at hi

def suffixContext {α : Type} (gs : List Gate) (initial : α → List Bool)
    (x : α) (value : Bool) (wire : ℕ) : Bool :=
  (gs.foldl step (initial x ++ [value])).getD wire false

lemma suffixContext_mono {α : Type} (gs : List Gate) (initial : α → List Bool)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) (x : α) :
    Monotone (suffixContext gs initial x) := by
  intro a b hab
  exact fold_mono gs hgs (initial x ++ [a]) (initial x ++ [b])
    (by simp) (append_singleton_mono (initial x) hab)

lemma fold_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
      simp only [List.foldl_cons]
      rw [ih (step w g) (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hi

lemma suffixContext_override {α : Type} (gs : List Gate) (initial : α → List Bool)
    (x : α) (value : Bool) :
    suffixContext gs initial x value (initial x).length = value := by
  unfold suffixContext
  rw [fold_getD_lt gs _ _ (by simp)]
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp

def edgeTerm {n : ℕ} (u v : Fin n) (x : Fin n → Bool) : Bool := x u && x v

lemma pairInput_le {n : ℕ} {u v : Fin n} {x : Fin n → Bool}
    (h : edgeTerm u v x = true) : PEqualNP.EdgeOwnership.pairInput u v ≤ x := by
  have hh : x u = true ∧ x v = true := by
    simpa only [edgeTerm, Bool.and_eq_true] using h
  obtain ⟨hu, hv⟩ := hh
  intro w hw
  change decide (w = u ∨ w = v) = true at hw
  rcases of_decide_eq_true hw with rfl | rfl
  · exact hu
  · exact hv

lemma edgeTerm_le_gate {n : ℕ} (u v : Fin n)
    (gate : (Fin n → Bool) → Bool) (hgate : Monotone gate)
    (hpair : gate (PEqualNP.EdgeOwnership.pairInput u v) = true) :
    edgeTerm u v ≤ gate := by
  intro x hx
  exact hgate (pairInput_le hx) hpair

lemma raw_edge_replacement {n : ℕ} (u v : Fin n)
    (P N : (Fin n → Bool) → Prop) (gs : List Gate)
    (initial : (Fin n → Bool) → List Bool) (out : ℕ)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (gate : (Fin n → Bool) → Bool) (hgate : Monotone gate)
    (hpair : gate (PEqualNP.EdgeOwnership.pairInput u v) = true)
    (hold : Correct P N (fun x => suffixContext gs initial x (gate x) out))
    (hessential : ∀ x, P x → suffixContext gs initial x false out = false →
      edgeTerm u v x = true) :
    Correct P N (fun x => suffixContext gs initial x (edgeTerm u v x) out) ∧
      ∀ x, suffixContext gs initial x (edgeTerm u v x) ≤
        suffixContext gs initial x (gate x) := by
  exact context_replacement P N (suffixContext gs initial) out
    (suffixContext_mono gs initial hgs) gate (edgeTerm u v)
    (edgeTerm_le_gate u v gate hgate hpair) hold hessential

noncomputable def badGateSet {α ι : Type} [DecidableEq ι]
    (P N : α → Prop) (andGates : Finset ι) (values : ι → α → Bool) : Finset ι := by
  classical
  exact andGates.filter fun i => Bad P N (values i)

lemma badGateSet_subset {α ι : Type} [DecidableEq ι]
    (P N : α → Prop) (andGates : Finset ι) (new old : ι → α → Bool)
    (hshrink : ∀ i, new i ≤ old i) :
    badGateSet P N andGates new ⊆ badGateSet P N andGates old := by
  classical
  intro i hi
  simp only [badGateSet, Finset.mem_filter] at hi ⊢
  exact ⟨hi.1, bad_mono (hshrink i) hi.2⟩

lemma bad_count_strictly_decreases {α ι : Type} [DecidableEq ι]
    (P N : α → Prop) (andGates : Finset ι) (new old : ι → α → Bool)
    (hshrink : ∀ i, new i ≤ old i) (j : ι) (hj : j ∈ andGates)
    (hold : Bad P N (old j)) (hnew : ¬ Bad P N (new j)) :
    (badGateSet P N andGates new).card < (badGateSet P N andGates old).card := by
  classical
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨badGateSet_subset P N andGates new old hshrink, ?_⟩
  intro heq
  have hm : j ∈ badGateSet P N andGates old := by
    simp only [badGateSet, Finset.mem_filter]
    exact ⟨hj, hold⟩
  rw [← heq] at hm
  exact hnew (Finset.mem_filter.mp hm).2

noncomputable def impureGateSet {α ι : Type} [DecidableEq ι]
    (N : α → Prop) (gates : Finset ι) (values : ι → α → Bool) : Finset ι := by
  classical
  exact gates.filter fun i => Impure N (values i)

lemma impureGateSet_subset {α ι : Type} [DecidableEq ι]
    (N : α → Prop) (gates : Finset ι) (new old : ι → α → Bool)
    (hshrink : ∀ i, new i ≤ old i) :
    impureGateSet N gates new ⊆ impureGateSet N gates old := by
  classical
  intro i hi
  simp only [impureGateSet, Finset.mem_filter] at hi ⊢
  exact ⟨hi.1, impure_mono (hshrink i) hi.2⟩

lemma impure_count_strictly_decreases {α ι : Type} [DecidableEq ι]
    (N : α → Prop) (gates : Finset ι) (new old : ι → α → Bool)
    (hshrink : ∀ i, new i ≤ old i) (j : ι) (hj : j ∈ gates)
    (hold : Impure N (old j)) (hnew : ¬ Impure N (new j)) :
    (impureGateSet N gates new).card < (impureGateSet N gates old).card := by
  classical
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨impureGateSet_subset N gates new old hshrink, ?_⟩
  intro heq
  have hm : j ∈ impureGateSet N gates old := by
    simp only [impureGateSet, Finset.mem_filter]
    exact ⟨hj, hold⟩
  rw [← heq] at hm
  exact hnew (Finset.mem_filter.mp hm).2

lemma raw_edge_replacement_improves {n : ℕ} (u v : Fin n)
    (P N : (Fin n → Bool) → Prop) (gs : List Gate)
    (initial : (Fin n → Bool) → List Bool) (out slot : ℕ)
    (hslot : ∀ x, (initial x).length = slot)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (gate : (Fin n → Bool) → Bool) (hgate : Monotone gate)
    (hpair : gate (PEqualNP.EdgeOwnership.pairInput u v) = true)
    (hold : Correct P N (fun x => suffixContext gs initial x (gate x) out))
    (hessential : ∀ x, P x → suffixContext gs initial x false out = false →
      edgeTerm u v x = true)
    (hpure : ∀ x, N x → edgeTerm u v x = false)
    (andGates : Finset ℕ) (hand : slot ∈ andGates) (hbad : Bad P N gate) :
    Correct P N (fun x => suffixContext gs initial x (edgeTerm u v x) out) ∧
      (∀ x, suffixContext gs initial x (edgeTerm u v x) ≤
        suffixContext gs initial x (gate x)) ∧
      (badGateSet P N andGates
        (fun i x => suffixContext gs initial x (edgeTerm u v x) i)).card <
      (badGateSet P N andGates
        (fun i x => suffixContext gs initial x (gate x) i)).card := by
  have hr := raw_edge_replacement u v P N gs initial out hgs gate hgate hpair hold hessential
  refine ⟨hr.1, hr.2, ?_⟩
  apply bad_count_strictly_decreases P N andGates _ _
    (fun i x => hr.2 x i) slot hand
  · have heq : (fun x => suffixContext gs initial x (gate x) slot) = gate := by
      funext x
      rw [← hslot x]
      exact suffixContext_override gs initial x (gate x)
    rw [heq]
    exact hbad
  · apply not_bad_of_false_negatives
    intro x hx
    rw [← hslot x, suffixContext_override]
    exact hpure x hx

lemma raw_edge_replacement_improves_impurity {n : ℕ} (u v : Fin n)
    (P N : (Fin n → Bool) → Prop) (gs : List Gate)
    (initial : (Fin n → Bool) → List Bool) (out slot : ℕ)
    (hslot : ∀ x, (initial x).length = slot)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (gate : (Fin n → Bool) → Bool) (hgate : Monotone gate)
    (hpair : gate (PEqualNP.EdgeOwnership.pairInput u v) = true)
    (hold : Correct P N (fun x => suffixContext gs initial x (gate x) out))
    (hessential : ∀ x, P x → suffixContext gs initial x false out = false →
      edgeTerm u v x = true)
    (hpure : ∀ x, N x → edgeTerm u v x = false)
    (gates : Finset ℕ) (hmem : slot ∈ gates) (himpure : Impure N gate) :
    Correct P N (fun x => suffixContext gs initial x (edgeTerm u v x) out) ∧
      (∀ x, suffixContext gs initial x (edgeTerm u v x) ≤
        suffixContext gs initial x (gate x)) ∧
      (impureGateSet N gates
        (fun i x => suffixContext gs initial x (edgeTerm u v x) i)).card <
      (impureGateSet N gates
        (fun i x => suffixContext gs initial x (gate x) i)).card := by
  have hr := raw_edge_replacement u v P N gs initial out hgs gate hgate hpair hold hessential
  refine ⟨hr.1, hr.2, ?_⟩
  apply impure_count_strictly_decreases N gates _ _
    (fun i x => hr.2 x i) slot hmem
  · have heq : (fun x => suffixContext gs initial x (gate x) slot) = gate := by
      funext x
      rw [← hslot x]
      exact suffixContext_override gs initial x (gate x)
    rw [heq]
    exact himpure
  · apply not_impure_of_false_negatives
    intro x hx
    rw [← hslot x, suffixContext_override]
    exact hpure x hx

end PEqualNP.Outside.L_meta_2590.EssentialPruning
