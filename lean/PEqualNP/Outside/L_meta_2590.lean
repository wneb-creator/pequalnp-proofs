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

open PEqualNP.MetaComplexity

def splice (pre : List Gate) (g : Gate) (post : List Gate) (out : ℕ) : Circuit :=
  { gates := pre ++ g :: post, output := out }

def prefixValues (n : ℕ) (pre : List Gate) (x : Fin n → Bool) : List Bool :=
  pre.foldl step (List.ofFn x)

def selectedValue (n : ℕ) (pre : List Gate) (g : Gate) (x : Fin n → Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => (prefixValues n pre x).getD i false)

def wireValues (n : ℕ) (C : Circuit) (wire : ℕ) (x : Fin n → Bool) : Bool :=
  (C.wires (List.ofFn x)).getD wire false

noncomputable def circuitImpurity {n : ℕ} (N : (Fin n → Bool) → Prop)
    (C : Circuit) : ℕ :=
  (impureGateSet N (Finset.Ico n (n + C.size)) (wireValues n C)).card

lemma splice_size (pre : List Gate) (oldGate newGate : Gate)
    (post : List Gate) (out : ℕ) :
    (splice pre newGate post out).size = (splice pre oldGate post out).size := by
  simp [splice, Circuit.size]

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp [step, Nat.add_comm, Nat.add_left_comm]

lemma prefixValues_length {n : ℕ} (pre : List Gate) (x : Fin n → Bool) :
    (prefixValues n pre x).length = n + pre.length := by
  simp [prefixValues, fold_length]

lemma prefixValues_input {n : ℕ} (pre : List Gate) (x : Fin n → Bool) (u : Fin n) :
    (prefixValues n pre x).getD u.val false = x u := by
  unfold prefixValues
  rw [fold_getD_lt pre _ _ (by simp)]
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

lemma ofFn_wireLE {n : ℕ} {x y : Fin n → Bool} (hxy : x ≤ y) :
    WireLE (List.ofFn x) (List.ofFn y) := by
  intro i hi
  by_cases hil : i < n
  · rw [List.getD_eq_getElem _ _ (by simpa using hil), List.getElem_ofFn] at hi ⊢
    exact hxy ⟨i, hil⟩ hi
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hil)] at hi
    cases hi

lemma selectedValue_mono {n : ℕ} (pre : List Gate) (g : Gate)
    (hpre : ∀ h ∈ pre, h.op = GateOp.and ∨ h.op = GateOp.or)
    (hg : g.op = GateOp.and ∨ g.op = GateOp.or) :
    Monotone (selectedValue n pre g) := by
  intro x y hxy
  exact gate_eval_mono g.op hg _ _ _
    (fold_mono pre hpre (List.ofFn x) (List.ofFn y) (by simp) (ofFn_wireLE hxy))

lemma mono_gate_op {C : Circuit} (hC : Monotone2 C) (g : Gate) (hg : g ∈ C.gates) :
    g.op = GateOp.and ∨ g.op = GateOp.or := by
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (hC g hg).1

lemma selectedValue_mono_of_splice {n : ℕ} (pre : List Gate) (g : Gate)
    (post : List Gate) (out : ℕ) (hC : Monotone2 (splice pre g post out)) :
    Monotone (selectedValue n pre g) := by
  apply selectedValue_mono
  · intro h hh
    exact mono_gate_op hC h (List.mem_append_left _ hh)
  · exact mono_gate_op hC g (List.mem_append_right _ List.mem_cons_self)

lemma splice_monotone2 (pre : List Gate) (oldGate newGate : Gate)
    (post : List Gate) (out : ℕ) (hC : Monotone2 (splice pre oldGate post out))
    (hnew : newGate.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧
      newGate.inputs.length ≤ 2) : Monotone2 (splice pre newGate post out) := by
  intro g hg
  change g ∈ pre ++ newGate :: post at hg
  rcases List.mem_append.mp hg with hg | hg
  · exact hC g (List.mem_append_left _ hg)
  · rcases List.mem_cons.mp hg with rfl | hg
    · exact hnew
    · exact hC g (List.mem_append_right _ (List.mem_cons_of_mem _ hg))

lemma splice_wireValues (n : ℕ) (pre : List Gate) (g : Gate)
    (post : List Gate) (out : ℕ) :
    wireValues n (splice pre g post out) =
      fun i x => suffixContext post (prefixValues n pre) x (selectedValue n pre g x) i := by
  funext i x
  change ((pre ++ g :: post).foldl step (List.ofFn x)).getD i false =
    (post.foldl step (prefixValues n pre x ++ [selectedValue n pre g x])).getD i false
  rw [List.foldl_append, List.foldl_cons]
  rfl

lemma splice_circuitFun (n : ℕ) (pre : List Gate) (g : Gate)
    (post : List Gate) (out : ℕ) :
    circuitFun n (splice pre g post out) =
      fun x => suffixContext post (prefixValues n pre) x (selectedValue n pre g x) out := by
  exact congrFun (splice_wireValues n pre g post out) out

lemma splice_selected_wire (n : ℕ) (pre : List Gate) (g : Gate)
    (post : List Gate) (out : ℕ) :
    wireValues n (splice pre g post out) (n + pre.length) = selectedValue n pre g := by
  rw [splice_wireValues]
  funext x
  rw [← prefixValues_length pre x]
  exact suffixContext_override post (prefixValues n pre) x (selectedValue n pre g x)

def rawEdgeGate {n : ℕ} (u v : Fin n) : Gate :=
  { op := GateOp.and, inputs := [u.val, v.val] }

lemma rawEdgeGate_value {n : ℕ} (pre : List Gate) (u v : Fin n) :
    selectedValue n pre (rawEdgeGate u v) = edgeTerm u v := by
  funext x
  change ((prefixValues n pre x).getD u.val false &&
    ((prefixValues n pre x).getD v.val false && true)) = edgeTerm u v x
  rw [prefixValues_input, prefixValues_input]
  simp [edgeTerm]

def falseGate (wire : ℕ) : Gate :=
  { op := GateOp.and, inputs := [wire, wire] }

lemma falseGate_value {n : ℕ} (pre : List Gate) :
    selectedValue n pre (falseGate (n + pre.length)) = fun _ => false := by
  funext x
  have hz : (prefixValues n pre x).getD (n + pre.length) false = false :=
    List.getD_eq_default _ _ (by rw [prefixValues_length])
  change ((prefixValues n pre x).getD (n + pre.length) false &&
    ((prefixValues n pre x).getD (n + pre.length) false && true)) = false
  rw [hz]
  rfl

lemma selected_slot_mem (n : ℕ) (pre : List Gate) (g : Gate)
    (post : List Gate) (out : ℕ) :
    n + pre.length ∈ Finset.Ico n (n + (splice pre g post out).size) := by
  simp only [Finset.mem_Ico, splice, Circuit.size, List.length_append, List.length_cons]
  omega

def CircuitImprovement {n : ℕ} (P N : (Fin n → Bool) → Prop)
    (old new : Circuit) : Prop :=
  new.size = old.size ∧ Monotone2 new ∧ Correct P N (circuitFun n new) ∧
    (∀ i, wireValues n new i ≤ wireValues n old i) ∧
    circuitImpurity N new < circuitImpurity N old

lemma circuit_replacement_improves_impurity {n : ℕ}
    (P N : (Fin n → Bool) → Prop) (pre : List Gate) (oldGate newGate : Gate)
    (post : List Gate) (out : ℕ) (hC : Monotone2 (splice pre oldGate post out))
    (hnew : newGate.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧
      newGate.inputs.length ≤ 2)
    (hshrink : selectedValue n pre newGate ≤ selectedValue n pre oldGate)
    (hold : Correct P N (circuitFun n (splice pre oldGate post out)))
    (hessential : ∀ x, P x → suffixContext post (prefixValues n pre) x false out = false →
      selectedValue n pre newGate x = true)
    (hpure : ∀ x, N x → selectedValue n pre newGate x = false)
    (himpure : Impure N (selectedValue n pre oldGate)) :
    CircuitImprovement P N (splice pre oldGate post out) (splice pre newGate post out) := by
  have hpost : ∀ g ∈ post, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    exact mono_gate_op hC g (List.mem_append_right _ (List.mem_cons_of_mem _ hg))
  have hold' : Correct P N (fun x => suffixContext post (prefixValues n pre) x
      (selectedValue n pre oldGate x) out) := by
    simpa only [splice_circuitFun] using hold
  have hr := context_replacement P N (suffixContext post (prefixValues n pre)) out
    (suffixContext_mono post (prefixValues n pre) hpost)
    (selectedValue n pre oldGate) (selectedValue n pre newGate) hshrink hold' hessential
  have hs : ∀ i, wireValues n (splice pre newGate post out) i ≤
      wireValues n (splice pre oldGate post out) i := by
    intro i x hx
    rw [splice_wireValues] at hx ⊢
    exact hr.2 x i hx
  refine ⟨splice_size pre oldGate newGate post out,
    splice_monotone2 pre oldGate newGate post out hC hnew, ?_, hs, ?_⟩
  · simpa only [splice_circuitFun] using hr.1
  · unfold circuitImpurity
    rw [splice_size pre oldGate newGate post out]
    apply impure_count_strictly_decreases N _ _ _ hs (n + pre.length)
      (selected_slot_mem n pre oldGate post out)
    · rw [splice_selected_wire]
      exact himpure
    · rw [splice_selected_wire]
      exact not_impure_of_false_negatives hpure

lemma circuit_raw_edge_replacement {n : ℕ} (u v : Fin n)
    (P N : (Fin n → Bool) → Prop) (pre : List Gate) (oldGate : Gate)
    (post : List Gate) (out : ℕ) (hC : Monotone2 (splice pre oldGate post out))
    (hpair : selectedValue n pre oldGate (PEqualNP.EdgeOwnership.pairInput u v) = true)
    (hold : Correct P N (circuitFun n (splice pre oldGate post out)))
    (hessential : ∀ x, P x → suffixContext post (prefixValues n pre) x false out = false →
      edgeTerm u v x = true)
    (hpure : ∀ x, N x → edgeTerm u v x = false)
    (himpure : Impure N (selectedValue n pre oldGate)) :
    CircuitImprovement P N (splice pre oldGate post out)
      (splice pre (rawEdgeGate u v) post out) := by
  apply circuit_replacement_improves_impurity P N pre oldGate (rawEdgeGate u v) post out hC
  · simp [rawEdgeGate]
  · rw [rawEdgeGate_value]
    exact edgeTerm_le_gate u v (selectedValue n pre oldGate)
      (selectedValue_mono_of_splice pre oldGate post out hC) hpair
  · exact hold
  · simpa only [rawEdgeGate_value] using hessential
  · simpa only [rawEdgeGate_value] using hpure
  · exact himpure

lemma circuit_false_replacement {n : ℕ}
    (P N : (Fin n → Bool) → Prop) (pre : List Gate) (oldGate : Gate)
    (post : List Gate) (out : ℕ) (hC : Monotone2 (splice pre oldGate post out))
    (hold : Correct P N (circuitFun n (splice pre oldGate post out)))
    (hzero : ∀ x, P x → suffixContext post (prefixValues n pre) x false out = true)
    (himpure : Impure N (selectedValue n pre oldGate)) :
    CircuitImprovement P N (splice pre oldGate post out)
      (splice pre (falseGate (n + pre.length)) post out) := by
  apply circuit_replacement_improves_impurity P N pre oldGate
    (falseGate (n + pre.length)) post out hC
  · simp [falseGate]
  · rw [falseGate_value]
    exact fun x => Bool.false_le _
  · exact hold
  · intro x hx hz
    rw [hzero x hx] at hz
    cases hz
  · intro x hx
    rw [falseGate_value]
  · exact himpure

lemma circuit_split (C : Circuit) (j : Fin C.gates.length) :
    C = splice (C.gates.take j.val) (C.gates.get j)
      (C.gates.drop (j.val + 1)) C.output := by
  have hs : C.gates = C.gates.take j.val ++ C.gates.get j :: C.gates.drop (j.val + 1) := by
    conv_lhs => rw [← List.take_append_drop j.val C.gates]
    congr 1
    exact List.drop_eq_getElem_cons j.isLt
  cases C with
  | mk gates out => exact congrArg (fun gs => Circuit.mk gs out) hs

lemma exists_minimum_nat_measure {α : Type} (S : α → Prop) (measure : α → ℕ)
    (hex : ∃ a, S a) : ∃ a, S a ∧ ∀ b, S b → measure a ≤ measure b := by
  classical
  let Attained : ℕ → Prop := fun n => ∃ a, S a ∧ measure a = n
  have hnat : ∃ n, Attained n := by
    obtain ⟨a, ha⟩ := hex
    exact ⟨measure a, a, ha, rfl⟩
  obtain ⟨a, ha, hmeasure⟩ := Nat.find_spec hnat
  refine ⟨a, ha, ?_⟩
  intro b hb
  rw [hmeasure]
  exact Nat.find_min' hnat ⟨b, hb, rfl⟩

def BoundarySolution {n : ℕ} (P N : (Fin n → Bool) → Prop) (k : ℕ)
    (C : Circuit) : Prop := Monotone2 C ∧ C.size ≤ k ∧ Correct P N (circuitFun n C)

lemma exists_bounded_minimum_impurity {n : ℕ} (P N : (Fin n → Bool) → Prop)
    (k : ℕ) (hex : ∃ C, BoundarySolution P N k C) :
    ∃ C, BoundarySolution P N k C ∧
      ∀ D, BoundarySolution P N k D → circuitImpurity N C ≤ circuitImpurity N D :=
  exists_minimum_nat_measure (BoundarySolution P N k) (circuitImpurity N) hex

lemma minimal_impurity_two_essential {n : ℕ} (P N : (Fin n → Bool) → Prop)
    (hpositive : ∀ x, P x → ∃ u v : Fin n,
      x = PEqualNP.EdgeOwnership.pairInput u v ∧ ∀ y, N y → edgeTerm u v y = false)
    (pre : List Gate) (g : Gate) (post : List Gate) (out : ℕ)
    (hC : Monotone2 (splice pre g post out))
    (hcorrect : Correct P N (circuitFun n (splice pre g post out)))
    (hminimal : ∀ D, Monotone2 D → D.size = (splice pre g post out).size →
      Correct P N (circuitFun n D) →
        circuitImpurity N (splice pre g post out) ≤ circuitImpurity N D)
    (himpure : Impure N (selectedValue n pre g)) :
    ∃ x y, P x ∧ P y ∧ x ≠ y ∧
      suffixContext post (prefixValues n pre) x false out = false ∧
      suffixContext post (prefixValues n pre) y false out = false := by
  classical
  by_contra htwo
  by_cases hex : ∃ x, P x ∧ suffixContext post (prefixValues n pre) x false out = false
  · obtain ⟨x, hx, hzero⟩ := hex
    obtain ⟨u, v, hxeq, hpure⟩ := hpositive x hx
    have hgateX : selectedValue n pre g x = true := by
      cases hv : selectedValue n pre g x with
      | false =>
          have ho : suffixContext post (prefixValues n pre) x
              (selectedValue n pre g x) out = true := by
            simpa only [splice_circuitFun] using hcorrect.1 x hx
          rw [hv, hzero] at ho
          cases ho
      | true => rfl
    have hpair : selectedValue n pre g (PEqualNP.EdgeOwnership.pairInput u v) = true := by
      simpa only [hxeq] using hgateX
    have hcover : ∀ y, P y → suffixContext post (prefixValues n pre) y false out = false →
        edgeTerm u v y = true := by
      intro y hy hyzero
      have hyx : y = x := by
        by_contra hne
        exact htwo ⟨x, y, hx, hy, Ne.symm hne, hzero, hyzero⟩
      rw [hyx, hxeq]
      simp [edgeTerm, PEqualNP.EdgeOwnership.pairInput]
    have hi := circuit_raw_edge_replacement u v P N pre g post out
      hC hpair hcorrect hcover hpure himpure
    have hle := hminimal _ hi.2.1 hi.1 hi.2.2.1
    exact Nat.not_lt_of_ge hle hi.2.2.2.2
  · have hzero : ∀ x, P x → suffixContext post (prefixValues n pre) x false out = true := by
      intro x hx
      cases hv : suffixContext post (prefixValues n pre) x false out with
      | false => exact False.elim (hex ⟨x, hx, hv⟩)
      | true => rfl
    have hi := circuit_false_replacement P N pre g post out hC hcorrect hzero himpure
    have hle := hminimal _ hi.2.1 hi.1 hi.2.2.1
    exact Nat.not_lt_of_ge hle hi.2.2.2.2

lemma exists_bounded_essential_impurity {n : ℕ} (P N : (Fin n → Bool) → Prop)
    (hpositive : ∀ x, P x → ∃ u v : Fin n,
      x = PEqualNP.EdgeOwnership.pairInput u v ∧ ∀ y, N y → edgeTerm u v y = false)
    (k : ℕ) (hex : ∃ C, BoundarySolution P N k C) :
    ∃ C, BoundarySolution P N k C ∧
      ∀ pre g post out, C = splice pre g post out → Impure N (selectedValue n pre g) →
        ∃ x y, P x ∧ P y ∧ x ≠ y ∧
          suffixContext post (prefixValues n pre) x false out = false ∧
          suffixContext post (prefixValues n pre) y false out = false := by
  obtain ⟨C, hC, hminimal⟩ := exists_bounded_minimum_impurity P N k hex
  refine ⟨C, hC, ?_⟩
  intro pre g post out heq himpure
  apply minimal_impurity_two_essential P N hpositive pre g post out
  · simpa only [← heq] using hC.1
  · simpa only [← heq] using hC.2.2
  · intro D hD hsize hcorrect
    rw [← heq] at hsize ⊢
    exact hminimal D ⟨hD, hsize.trans_le hC.2.1, hcorrect⟩
  · exact himpure

def edgeFunction {n : ℕ} (edges : List (Fin n × Fin n)) (x : Fin n → Bool) : Bool :=
  edges.any fun e => x e.1 && x e.2

def EdgePositive {n : ℕ} (edges : List (Fin n × Fin n)) (x : Fin n → Bool) : Prop :=
  ∃ e ∈ edges, x = PEqualNP.EdgeOwnership.pairInput e.1 e.2

def EdgeNegative {n : ℕ} (edges : List (Fin n × Fin n)) (x : Fin n → Bool) : Prop :=
  edgeFunction edges x = false

lemma edgeFunction_true_iff {n : ℕ} (edges : List (Fin n × Fin n)) (x : Fin n → Bool) :
    edgeFunction edges x = true ↔ ∃ e ∈ edges, edgeTerm e.1 e.2 x = true := by
  simp [edgeFunction, edgeTerm, List.any_eq_true]

lemma edgeFunction_term_le {n : ℕ} (edges : List (Fin n × Fin n))
    (e : Fin n × Fin n) (he : e ∈ edges) : edgeTerm e.1 e.2 ≤ edgeFunction edges := by
  intro x hx
  exact (edgeFunction_true_iff edges x).mpr ⟨e, he, hx⟩

lemma edgeTerm_pairInput {n : ℕ} (u v : Fin n) :
    edgeTerm u v (PEqualNP.EdgeOwnership.pairInput u v) = true := by
  simp [edgeTerm, PEqualNP.EdgeOwnership.pairInput]

lemma edgeFunction_positive {n : ℕ} (edges : List (Fin n × Fin n))
    (x : Fin n → Bool) (hx : EdgePositive edges x) : edgeFunction edges x = true := by
  obtain ⟨e, he, rfl⟩ := hx
  exact edgeFunction_term_le edges e he _ (edgeTerm_pairInput e.1 e.2)

lemma edgeFunction_mono {n : ℕ} (edges : List (Fin n × Fin n)) :
    Monotone (edgeFunction edges) := by
  intro x y hxy hx
  obtain ⟨e, he, hterm⟩ := (edgeFunction_true_iff edges x).mp hx
  exact (edgeFunction_true_iff edges y).mpr
    ⟨e, he, (inf_le_inf (hxy e.1) (hxy e.2)) hterm⟩

lemma edge_positive_pair_pure {n : ℕ} (edges : List (Fin n × Fin n)) :
    ∀ x, EdgePositive edges x → ∃ u v : Fin n,
      x = PEqualNP.EdgeOwnership.pairInput u v ∧
        ∀ y, EdgeNegative edges y → edgeTerm u v y = false := by
  rintro x ⟨e, he, hxeq⟩
  refine ⟨e.1, e.2, hxeq, ?_⟩
  intro y hy
  have hle := edgeFunction_term_le edges e he y
  change edgeFunction edges y = false at hy
  rw [hy] at hle
  exact le_antisymm hle (Bool.false_le _)

lemma circuitFun_mono (n : ℕ) (C : Circuit) (hC : Monotone2 C) :
    Monotone (circuitFun n C) := by
  intro x y hxy
  exact fold_mono C.gates (fun g hg => mono_gate_op hC g hg)
    (List.ofFn x) (List.ofFn y) (by simp) (ofFn_wireLE hxy) C.output

lemma edge_correct_iff {n : ℕ} (edges : List (Fin n × Fin n))
    (f : (Fin n → Bool) → Bool) (hf : Monotone f) :
    Correct (EdgePositive edges) (EdgeNegative edges) f ↔ f = edgeFunction edges := by
  constructor
  · intro hcorrect
    funext x
    cases hvalue : edgeFunction edges x with
    | false => exact hcorrect.2 x hvalue
    | true =>
        obtain ⟨e, he, hterm⟩ := (edgeFunction_true_iff edges x).mp hvalue
        exact hf (pairInput_le hterm) (hcorrect.1 _ ⟨e, he, rfl⟩)
  · intro heq
    rw [heq]
    exact ⟨edgeFunction_positive edges, fun _ h => h⟩

lemma edge_circuit_correct_iff {n : ℕ} (edges : List (Fin n × Fin n))
    (C : Circuit) (hC : Monotone2 C) :
    Correct (EdgePositive edges) (EdgeNegative edges) (circuitFun n C) ↔
      circuitFun n C = edgeFunction edges :=
  edge_correct_iff edges (circuitFun n C) (circuitFun_mono n C hC)

def HasEssentialEdgePairs {n : ℕ} (edges : List (Fin n × Fin n)) (C : Circuit) : Prop :=
  ∀ pre g post out, C = splice pre g post out →
    Impure (EdgeNegative edges) (selectedValue n pre g) →
      ∃ e₁ ∈ edges, ∃ e₂ ∈ edges,
        PEqualNP.EdgeOwnership.pairInput e₁.1 e₁.2 ≠
          PEqualNP.EdgeOwnership.pairInput e₂.1 e₂.2 ∧
        suffixContext post (prefixValues n pre)
          (PEqualNP.EdgeOwnership.pairInput e₁.1 e₁.2) false out = false ∧
        suffixContext post (prefixValues n pre)
          (PEqualNP.EdgeOwnership.pairInput e₂.1 e₂.2) false out = false

lemma normalize_edge_circuit {n : ℕ} (edges : List (Fin n × Fin n))
    (C : Circuit) (hC : Monotone2 C) (hcorrect : circuitFun n C = edgeFunction edges) :
    ∃ D, Monotone2 D ∧ D.size ≤ C.size ∧ circuitFun n D = edgeFunction edges ∧
      HasEssentialEdgePairs edges D := by
  have hex : ∃ D, BoundarySolution (EdgePositive edges) (EdgeNegative edges) C.size D :=
    ⟨C, hC, le_rfl, (edge_circuit_correct_iff edges C hC).mpr hcorrect⟩
  obtain ⟨D, hD, hessential⟩ := exists_bounded_essential_impurity
    (EdgePositive edges) (EdgeNegative edges) (edge_positive_pair_pure edges) C.size hex
  refine ⟨D, hD.1, hD.2.1, (edge_circuit_correct_iff edges D hD.1).mp hD.2.2, ?_⟩
  intro pre g post out heq himpure
  obtain ⟨x, y, hx, hy, hne, hzeroX, hzeroY⟩ := hessential pre g post out heq himpure
  obtain ⟨e₁, he₁, hxeq⟩ := hx
  obtain ⟨e₂, he₂, hyeq⟩ := hy
  refine ⟨e₁, he₁, e₂, he₂, ?_, ?_, ?_⟩
  · simpa only [hxeq, hyeq] using hne
  · simpa only [hxeq] using hzeroX
  · simpa only [hyeq] using hzeroY

lemma normalize_edge_circuit_bounded {n : ℕ} (edges : List (Fin n × Fin n))
    (k : ℕ) (C : Circuit) (hC : Monotone2 C) (hsize : C.size ≤ k)
    (hcorrect : circuitFun n C = edgeFunction edges) :
    ∃ D, Monotone2 D ∧ D.size ≤ k ∧ circuitFun n D = edgeFunction edges ∧
      HasEssentialEdgePairs edges D := by
  obtain ⟨D, hD, hbound, hfun, hpairs⟩ := normalize_edge_circuit edges C hC hcorrect
  exact ⟨D, hD, hbound.trans hsize, hfun, hpairs⟩

def petersenEdges : List (Fin 10 × Fin 10) :=
  [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)]

lemma petersen_edgeFunction_eq_posted :
    edgeFunction petersenEdges = (fun (x5 : Fin (10 : ℕ) → Bool) => x5 (0 : Fin (10 : ℕ)) && x5 (1 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (3 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (4 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (0 : Fin (10 : ℕ)) || x5 (0 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (5 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (7 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (9 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (6 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (8 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ))) := by
  funext x
  simp [edgeFunction, petersenEdges, Bool.or_assoc]

lemma exists_size_minimal_essential_impurity {n : ℕ} (P N : (Fin n → Bool) → Prop)
    (hpositive : ∀ x, P x → ∃ u v : Fin n,
      x = PEqualNP.EdgeOwnership.pairInput u v ∧ ∀ y, N y → edgeTerm u v y = false)
    (k : ℕ) (hex : ∃ C, BoundarySolution P N k C) :
    ∃ C, BoundarySolution P N k C ∧
      (∀ D, BoundarySolution P N k D → C.size ≤ D.size) ∧
      ∀ pre g post out, C = splice pre g post out → Impure N (selectedValue n pre g) →
        ∃ x y, P x ∧ P y ∧ x ≠ y ∧
          suffixContext post (prefixValues n pre) x false out = false ∧
          suffixContext post (prefixValues n pre) y false out = false := by
  obtain ⟨C₀, hC₀, hsize₀⟩ :=
    exists_minimum_nat_measure (BoundarySolution P N k) Circuit.size hex
  obtain ⟨C, hC, himpurity⟩ := exists_minimum_nat_measure
    (fun D => BoundarySolution P N k D ∧ D.size = C₀.size)
    (circuitImpurity N) ⟨C₀, hC₀, rfl⟩
  refine ⟨C, hC.1, ?_, ?_⟩
  · intro D hD
    rw [hC.2]
    exact hsize₀ D hD
  · intro pre g post out heq himpure
    apply minimal_impurity_two_essential P N hpositive pre g post out
    · simpa only [← heq] using hC.1.1
    · simpa only [← heq] using hC.1.2.2
    · intro D hD hsize hcorrect
      rw [← heq] at hsize ⊢
      exact himpurity D ⟨⟨hD, hsize.trans_le hC.1.2.1, hcorrect⟩, hsize.trans hC.2⟩
    · exact himpure

lemma normalize_edge_circuit_size_minimal {n : ℕ} (edges : List (Fin n × Fin n))
    (k : ℕ) (C : Circuit) (hC : Monotone2 C) (hsize : C.size ≤ k)
    (hcorrect : circuitFun n C = edgeFunction edges) :
    ∃ D, Monotone2 D ∧ D.size ≤ k ∧ circuitFun n D = edgeFunction edges ∧
      (∀ F, Monotone2 F → F.size ≤ k → circuitFun n F = edgeFunction edges →
        D.size ≤ F.size) ∧ HasEssentialEdgePairs edges D := by
  have hex : ∃ D, BoundarySolution (EdgePositive edges) (EdgeNegative edges) k D :=
    ⟨C, hC, hsize, (edge_circuit_correct_iff edges C hC).mpr hcorrect⟩
  obtain ⟨D, hD, hminimal, hessential⟩ := exists_size_minimal_essential_impurity
    (EdgePositive edges) (EdgeNegative edges) (edge_positive_pair_pure edges) k hex
  refine ⟨D, hD.1, hD.2.1, (edge_circuit_correct_iff edges D hD.1).mp hD.2.2, ?_, ?_⟩
  · intro F hF hFsize hFfun
    exact hminimal F ⟨hF, hFsize, (edge_circuit_correct_iff edges F hF).mpr hFfun⟩
  · intro pre g post out heq himpure
    obtain ⟨x, y, hx, hy, hne, hzeroX, hzeroY⟩ := hessential pre g post out heq himpure
    obtain ⟨e₁, he₁, hxeq⟩ := hx
    obtain ⟨e₂, he₂, hyeq⟩ := hy
    refine ⟨e₁, he₁, e₂, he₂, ?_, ?_, ?_⟩
    · simpa only [hxeq, hyeq] using hne
    · simpa only [hxeq] using hzeroX
    · simpa only [hyeq] using hzeroY

def inputOfMask (m : ℕ) : Fin 10 → Bool := fun i => m.testBit i.val

def maximalNegativeMasks : List ℕ :=
  [50, 69, 104, 116, 138, 201, 208, 276, 385, 402, 521, 548, 554, 770, 773]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma maximalNegativeMasks_false :
    ∀ m ∈ maximalNegativeMasks, edgeFunction petersenEdges (inputOfMask m) = false := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma maximalNegativeMasks_cover :
    ∀ x : Fin 10 → Bool, edgeFunction petersenEdges x = false →
      (maximalNegativeMasks.any fun m => decide (x ≤ inputOfMask m)) = true := by
  decide

lemma negative_below_maximal {x : Fin 10 → Bool}
    (hx : edgeFunction petersenEdges x = false) :
    ∃ m ∈ maximalNegativeMasks, x ≤ inputOfMask m := by
  simpa only [List.any_eq_true, decide_eq_true_eq] using maximalNegativeMasks_cover x hx

lemma petersen_impure_iff_maximal (f : (Fin 10 → Bool) → Bool) (hf : Monotone f) :
    Impure (EdgeNegative petersenEdges) f ↔
      ∃ m ∈ maximalNegativeMasks, f (inputOfMask m) = true := by
  constructor
  · rintro ⟨x, hx, hfx⟩
    obtain ⟨m, hm, hxm⟩ := negative_below_maximal hx
    exact ⟨m, hm, hf hxm hfx⟩
  · rintro ⟨m, hm, hfm⟩
    exact ⟨inputOfMask m, maximalNegativeMasks_false m hm, hfm⟩

lemma petersen_boundary30_iff (f : (Fin 10 → Bool) → Bool) (hf : Monotone f) :
    ((∀ e ∈ petersenEdges, f (PEqualNP.EdgeOwnership.pairInput e.1 e.2) = true) ∧
      ∀ m ∈ maximalNegativeMasks, f (inputOfMask m) = false) ↔
        f = edgeFunction petersenEdges := by
  rw [← edge_correct_iff petersenEdges f hf]
  constructor
  · rintro ⟨hp, hn⟩
    constructor
    · rintro x ⟨e, he, rfl⟩
      exact hp e he
    · intro x hx
      obtain ⟨m, hm, hxm⟩ := negative_below_maximal hx
      have hle := hf hxm
      rw [hn m hm] at hle
      exact le_antisymm hle (Bool.false_le _)
  · rintro ⟨hp, hn⟩
    exact ⟨fun e he => hp _ ⟨e, he, rfl⟩,
      fun m hm => hn _ (maximalNegativeMasks_false m hm)⟩

lemma selectedValue_impure_iff_maximal (pre : List Gate) (g : Gate)
    (post : List Gate) (out : ℕ) (hC : Monotone2 (splice pre g post out)) :
    Impure (EdgeNegative petersenEdges) (selectedValue 10 pre g) ↔
      ∃ m ∈ maximalNegativeMasks, selectedValue 10 pre g (inputOfMask m) = true :=
  petersen_impure_iff_maximal _ (selectedValue_mono_of_splice pre g post out hC)

-- Circuit normalization and wire counting, adapted from L_meta_971.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def gop : Bool → Bool → Bool → Bool
  | true, a, b => a && b
  | false, a, b => a || b

@[local simp] lemma gop_true (a b : Bool) : gop true a b = (a && b) := rfl

@[local simp] lemma gop_false (a b : Bool) : gop false a b = (a || b) := rfl

abbrev Dag := List (Bool × ℕ × ℕ)

def tag (D : Dag) (j : ℕ) : Bool := (D.getD j (false, 0, 0)).1

def opA (D : Dag) (j : ℕ) : ℕ := (D.getD j (false, 0, 0)).2.1

def opB (D : Dag) (j : ℕ) : ℕ := (D.getD j (false, 0, 0)).2.2

def wstep (w : List Bool) (g : Bool × ℕ × ℕ) : List Bool :=
  w ++ [gop g.1 (w.getD g.2.1 false) (w.getD g.2.2 false)]

def wl (D : Dag) (w : List Bool) : List Bool := D.foldl wstep w

def val (D : Dag) {n : ℕ} (x : Fin n → Bool) (w : ℕ) : Bool :=
  (wl D (List.ofFn x)).getD w false

def Strict (n : ℕ) (D : Dag) : Prop :=
  ∀ j, j < D.length → opA D j < n + j ∧ opB D j < n + j ∧ opA D j ≠ opB D j

def readers (D : Dag) (w : ℕ) : Finset ℕ :=
  (Finset.range D.length).filter (fun j => opA D j = w ∨ opB D j = w)

def fanout (D : Dag) (w : ℕ) : ℕ := (readers D w).card

def Live (n : ℕ) (D : Dag) : Prop := ∀ w, w + 1 < n + D.length → 1 ≤ fanout D w

def StrictLive (n : ℕ) (D : Dag) : Prop := Strict n D ∧ Live n D ∧ D ≠ []

def outW (n : ℕ) (D : Dag) : ℕ := n + D.length - 1

def single {n : ℕ} (v : Fin n) : Fin n → Bool := fun i => decide (i = v)

def supp (n : ℕ) (D : Dag) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun v => val D (single v) w = true)

def surplusOn (D : Dag) (K : Finset ℕ) : ℕ := ∑ w ∈ K, (fanout D w - 1)

def inner (n : ℕ) (D : Dag) : Finset ℕ := Finset.range (n + D.length - 1)

def totalSurplus (n : ℕ) (D : Dag) : ℕ := surplusOn D (inner n D)

def Bplus (n : ℕ) (D : Dag) : ℕ :=
  surplusOn D ((inner n D).filter (fun w => (supp n D w).Nonempty))

def Bzero (n : ℕ) (D : Dag) : ℕ :=
  surplusOn D ((inner n D).filter (fun w => ¬ (supp n D w).Nonempty))

def branchW (n : ℕ) (D : Dag) : Finset ℕ :=
  (Finset.range (n + D.length)).filter (fun w => 2 ≤ fanout D w)

def eligSet (n : ℕ) (D : Dag) : Finset (Fin n) := (branchW n D).biUnion (supp n D)

def ineligSet (n : ℕ) (D : Dag) : Finset (Fin n) := Finset.univ \ eligSet n D

def units (n : ℕ) (D : Dag) : Finset (Σ _ : ℕ, ℕ) :=
  (inner n D).sigma (fun w => Finset.range (fanout D w - 1))

def unitsPlus (n : ℕ) (D : Dag) : Finset (Σ _ : ℕ, ℕ) :=
  (units n D).filter (fun u => (supp n D u.1).Nonempty)

def arcs (D : Dag) : Finset (ℕ × Bool) := Finset.range D.length ×ˢ Finset.univ

def src (D : Dag) (e : ℕ × Bool) : ℕ := if e.2 = true then opB D e.1 else opA D e.1

def exitArcs (n : ℕ) (D : Dag) (K : Finset ℕ) : Finset (ℕ × Bool) :=
  (arcs D).filter (fun e => src D e ∈ K ∧ n + e.1 ∉ K)

def merges (n : ℕ) (D : Dag) (K : Finset ℕ) : Finset ℕ :=
  (Finset.range D.length).filter (fun j => n + j ∈ K ∧ opA D j ∈ K ∧ opB D j ∈ K)

def sources (n : ℕ) (K : Finset ℕ) : Finset ℕ := K.filter (fun w => w < n)

def carrierT (n : ℕ) (D : Dag) (T : Finset (Fin n)) : Finset ℕ :=
  (Finset.range (n + D.length)).filter (fun w => (supp n D w ∩ T).Nonempty)

def carrierDiff (n : ℕ) (D : Dag) (x y : Fin n) : Finset ℕ :=
  (Finset.range (n + D.length)).filter (fun w => x ∈ supp n D w ∧ y ∉ supp n D w)

def PureBranch (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Prop :=
  ∀ v ∈ eligSet n D, 2 ≤ fanout D (b v) ∧ supp n D (b v) = {v}

def reservedUnits (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (eligSet n D).image (fun v => (⟨b v, 0⟩ : Σ _ : ℕ, ℕ))

def residualUnits (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  unitsPlus n D \ reservedUnits n D b

lemma tag_eq (D : Dag) (j : ℕ) (h : j < D.length) : tag D j = (D[j]).1 := by
  simp [tag, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

lemma opA_eq (D : Dag) (j : ℕ) (h : j < D.length) : opA D j = (D[j]).2.1 := by
  simp [opA, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

lemma opB_eq (D : Dag) (j : ℕ) (h : j < D.length) : opB D j = (D[j]).2.2 := by
  simp [opB, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

lemma wl_cons (g : Bool × ℕ × ℕ) (D : Dag) (w : List Bool) :
    wl (g :: D) w = wl D (wstep w g) := rfl

lemma wl_append (D E : Dag) (w : List Bool) : wl (D ++ E) w = wl E (wl D w) := by
  simp [wl, List.foldl_append]

lemma wstep_length (w : List Bool) (g : Bool × ℕ × ℕ) : (wstep w g).length = w.length + 1 := by
  simp [wstep]

lemma wl_length (D : Dag) : ∀ w : List Bool, (wl D w).length = w.length + D.length := by
  induction D with
  | nil => intro w; simp [wl]
  | cons g D ih => intro w; rw [wl_cons, ih, wstep_length]; simp; omega

lemma wstep_getD_lt (w : List Bool) (g : Bool × ℕ × ℕ) (i : ℕ) (h : i < w.length) :
    (wstep w g).getD i false = w.getD i false := by
  simp [wstep, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma wl_getD_lt (D : Dag) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wl D w).getD i false = w.getD i false := by
  induction D with
  | nil => intro w i _; rfl
  | cons g D ih =>
    intro w i h
    rw [wl_cons, ih _ _ (by rw [wstep_length]; omega), wstep_getD_lt _ _ _ h]

lemma getD_ge (w : List Bool) (i : ℕ) (h : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

lemma wstep_getD_last (w : List Bool) (g : Bool × ℕ × ℕ) :
    (wstep w g).getD w.length false = gop g.1 (w.getD g.2.1 false) (w.getD g.2.2 false) := by
  simp [wstep, List.getD_eq_getElem?_getD]

lemma wl_getD_gate (D : Dag) (w : List Bool) (j : ℕ) (hj : j < D.length) :
    (wl D w).getD (w.length + j) false =
      gop (tag D j) ((wl (D.take j) w).getD (opA D j) false)
        ((wl (D.take j) w).getD (opB D j) false) := by
  have hsplit : D = D.take j ++ D[j] :: D.drop (j + 1) := by simp
  have hlen : (wl (D.take j) w).length = w.length + j := by
    rw [wl_length, List.length_take]; omega
  rw [tag_eq D j hj, opA_eq D j hj, opB_eq D j hj]
  conv_lhs => rw [hsplit, wl_append, wl_cons]
  rw [wl_getD_lt _ _ _ (by rw [wstep_length, hlen]; omega), ← hlen, wstep_getD_last]

lemma wl_take_getD (D : Dag) (w : List Bool) (j i : ℕ) (hi : i < w.length + j)
    (hj : j ≤ D.length) :
    (wl (D.take j) w).getD i false = (wl D w).getD i false := by
  have hsplit : D = D.take j ++ D.drop j := by simp
  have hlen : (wl (D.take j) w).length = w.length + j := by
    rw [wl_length, List.length_take]; omega
  conv_rhs => rw [hsplit, wl_append]
  rw [wl_getD_lt (D.drop j) (wl (D.take j) w) i (by rw [hlen]; exact hi)]

lemma val_input (D : Dag) {n : ℕ} (x : Fin n → Bool) (i : ℕ) (h : i < n) :
    val D x i = x ⟨i, h⟩ := by
  unfold val
  rw [wl_getD_lt _ _ _ (by simpa using h)]
  simp [List.getD_eq_getElem?_getD, h]

lemma val_ge (D : Dag) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (h : n + D.length ≤ w) :
    val D x w = false := by
  unfold val
  exact getD_ge _ _ (by rw [wl_length]; simpa using h)

lemma val_take (D : Dag) {n : ℕ} (x : Fin n → Bool) (k w : ℕ) (hw : w < n + k)
    (hk : k ≤ D.length) : val (D.take k) x w = val D x w := by
  unfold val
  exact wl_take_getD D _ k w (by simpa using hw) hk

lemma val_gate {n : ℕ} {D : Dag} (hS : Strict n D) (x : Fin n → Bool) (j : ℕ)
    (hj : j < D.length) :
    val D x (n + j) = gop (tag D j) (val D x (opA D j)) (val D x (opB D j)) := by
  obtain ⟨ha, hb, -⟩ := hS j hj
  have h := wl_getD_gate D (List.ofFn x) j hj
  simp only [List.length_ofFn] at h
  unfold val
  rw [h, wl_take_getD D _ j _ (by simpa using ha) hj.le,
    wl_take_getD D _ j _ (by simpa using hb) hj.le]

lemma val_unique {n : ℕ} {D : Dag} (hS : Strict n D) (x : Fin n → Bool) (f : ℕ → Bool)
    (hin : ∀ i (h : i < n), f i = x ⟨i, h⟩)
    (hg : ∀ j, j < D.length → f (n + j) = gop (tag D j) (f (opA D j)) (f (opB D j))) :
    ∀ w, w < n + D.length → val D x w = f w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hn : w < n
    · rw [val_input D x w hn, hin w hn]
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < D.length := by omega
      obtain ⟨ha, hb, -⟩ := hS j hj
      rw [val_gate hS x j hj, hg j hj, ih _ ha (by omega), ih _ hb (by omega)]

abbrev Ref := Bool ⊕ ℕ

def refVal (W : List Bool) : Ref → Bool
  | Sum.inl b => b
  | Sum.inr k => W.getD k false

def na_look (m : List Ref) (i : ℕ) : Ref := m.getD i (Sum.inl false)

def na_comb (t : Bool) : Ref → Ref → Ref ⊕ (ℕ × ℕ)
  | Sum.inl a, r => Sum.inl (if a = t then r else Sum.inl a)
  | Sum.inr i, Sum.inl b => Sum.inl (if b = t then Sum.inr i else Sum.inl b)
  | Sum.inr i, Sum.inr j => if i = j then Sum.inl (Sum.inr i) else Sum.inr (i, j)

def na_isAnd : GateOp → Bool
  | GateOp.and => true
  | _ => false

def na_step (n : ℕ) (st : List Ref × Dag) (g : Gate) : List Ref × Dag :=
  match g.inputs with
  | [] => (st.1 ++ [Sum.inl (na_isAnd g.op)], st.2)
  | [a] => (st.1 ++ [na_look st.1 a], st.2)
  | a :: b :: _ =>
    match na_comb (na_isAnd g.op) (na_look st.1 a) (na_look st.1 b) with
    | Sum.inl r => (st.1 ++ [r], st.2)
    | Sum.inr p => (st.1 ++ [Sum.inr (n + st.2.length)], st.2 ++ [(na_isAnd g.op, p.1, p.2)])

def na_ok (B : ℕ) : Ref → Prop
  | Sum.inl _ => True
  | Sum.inr k => k < B

def na_Good (n : ℕ) (st : List Ref × Dag) : Prop :=
  Strict n st.2 ∧ ∀ r ∈ st.1, na_ok (n + st.2.length) r

lemma na_ok_mono {B B' : ℕ} (h : B ≤ B') (r : Ref) (hr : na_ok B r) : na_ok B' r := by
  rcases r with b | k
  · trivial
  · exact lt_of_lt_of_le hr h

lemma na_look_val (W : List Bool) (m : List Ref) (i : ℕ) :
    refVal W (na_look m i) = (m.map (refVal W)).getD i false := by
  simp only [na_look, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases m[i]? <;> rfl

lemma na_look_ok (B : ℕ) (m : List Ref) (hm : ∀ r ∈ m, na_ok B r) (i : ℕ) :
    na_ok B (na_look m i) := by
  simp only [na_look, List.getD_eq_getElem?_getD]
  rcases h : m[i]? with _ | r
  · trivial
  · exact hm r (List.mem_of_getElem? h)

lemma na_refVal_wstep (W : List Bool) (g : Bool × ℕ × ℕ) (r : Ref) (hr : na_ok W.length r) :
    refVal (wstep W g) r = refVal W r := by
  rcases r with b | k
  · rfl
  · exact wstep_getD_lt W g k hr

lemma na_comb_inl (t : Bool) (W : List Bool) (a b r : Ref) (h : na_comb t a b = Sum.inl r) :
    refVal W r = gop t (refVal W a) (refVal W b) := by
  rcases a with a | i
  · simp only [na_comb, Sum.inl.injEq] at h
    subst h
    cases t <;> cases a <;> simp [refVal]
  · rcases b with b | j
    · simp only [na_comb, Sum.inl.injEq] at h
      subst h
      cases t <;> cases b <;> simp [refVal]
    · simp only [na_comb] at h
      split_ifs at h with hij
      simp only [Sum.inl.injEq] at h
      subst h; subst hij
      cases t <;> simp [refVal]

lemma na_comb_ok (B : ℕ) (t : Bool) (a b r : Ref) (ha : na_ok B a) (hb : na_ok B b)
    (h : na_comb t a b = Sum.inl r) : na_ok B r := by
  rcases a with a | i
  · simp only [na_comb, Sum.inl.injEq] at h
    subst h; split_ifs
    · exact hb
    · trivial
  · rcases b with b | j
    · simp only [na_comb, Sum.inl.injEq] at h
      subst h; split_ifs
      · exact ha
      · trivial
    · simp only [na_comb] at h
      split_ifs at h
      simp only [Sum.inl.injEq] at h
      subst h; exact ha

lemma na_comb_inr (t : Bool) (a b : Ref) (p : ℕ × ℕ) (h : na_comb t a b = Sum.inr p) :
    a = Sum.inr p.1 ∧ b = Sum.inr p.2 ∧ p.1 ≠ p.2 := by
  rcases a with a | i
  · simp [na_comb] at h
  · rcases b with b | j
    · simp [na_comb] at h
    · simp only [na_comb] at h
      split_ifs at h with hij
      cases h
      exact ⟨rfl, rfl, hij⟩

lemma na_eval0 (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) :
    op.eval [] = na_isAnd op := by
  rcases hop with rfl | rfl <;> rfl

lemma na_eval1 (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) (u : Bool) :
    op.eval [u] = u := by
  rcases hop with rfl | rfl <;> simp [GateOp.eval]

lemma na_eval2 (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (u v : Bool) : op.eval [u, v] = gop (na_isAnd op) u v := by
  rcases hop with rfl | rfl <;> simp [GateOp.eval, na_isAnd]

lemma na_getD_append_lt (D E : Dag) (k : ℕ) (h : k < D.length) :
    (D ++ E).getD k (false, 0, 0) = D.getD k (false, 0, 0) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma na_getD_snoc (D : Dag) (g : Bool × ℕ × ℕ) :
    (D ++ [g]).getD D.length (false, 0, 0) = g := by
  simp [List.getD_eq_getElem?_getD]

lemma na_strict_snoc {n : ℕ} {D : Dag} (hS : Strict n D) (t : Bool) (i j : ℕ)
    (hi : i < n + D.length) (hj : j < n + D.length) (hij : i ≠ j) :
    Strict n (D ++ [(t, i, j)]) := by
  intro k hk
  simp only [List.length_append, List.length_singleton] at hk
  by_cases hk' : k < D.length
  · simp only [opA, opB, na_getD_append_lt D _ k hk']
    exact hS k hk'
  · have hkD : k = D.length := by omega
    subst hkD
    simp only [opA, opB, na_getD_snoc]
    exact ⟨hi, hj, hij⟩

lemma na_strict_take {n : ℕ} {D : Dag} (hS : Strict n D) (k : ℕ) : Strict n (D.take k) := by
  intro j hj
  simp only [List.length_take] at hj
  have hj1 : j < k := by omega
  have hj2 : j < D.length := by omega
  have e : (D.take k).getD j (false, 0, 0) = D.getD j (false, 0, 0) := by
    simp [List.getD_eq_getElem?_getD, hj1]
  simp only [opA, opB, e]
  exact hS j hj2

lemma na_step_spec (n : ℕ) (st : List Ref × Dag) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : na_Good n st) :
    na_Good n (na_step n st g) ∧ (na_step n st g).2.length ≤ st.2.length + 1 ∧
    ∀ (x : Fin n → Bool) (w : List Bool), st.1.map (refVal (wl st.2 (List.ofFn x))) = w →
      (na_step n st g).1.map (refVal (wl (na_step n st g).2 (List.ofFn x))) =
        w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] := by
  obtain ⟨m, D⟩ := st
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  obtain ⟨hS, hok⟩ := h
  dsimp only at hS hok hop hlen ⊢
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · refine ⟨⟨hS, ?_⟩, by simp [na_step], fun x w hw => ?_⟩
    · intro r hr
      simp only [na_step, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact hok r hr
      · trivial
    · subst hw
      simp only [na_step, List.map_append, List.map_cons, List.map_nil, refVal, na_eval0 op hop]
  · refine ⟨⟨hS, ?_⟩, by simp [na_step], fun x w hw => ?_⟩
    · intro r hr
      simp only [na_step, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact hok r hr
      · exact na_look_ok _ m hok a
    · subst hw
      simp only [na_step, List.map_append, List.map_cons, List.map_nil, na_eval1 op hop,
        na_look_val]
  · have hla := na_look_ok _ m hok a
    have hlb := na_look_ok _ m hok b
    rcases hc : na_comb (na_isAnd op) (na_look m a) (na_look m b) with r | p
    · refine ⟨⟨by simpa only [na_step, hc] using hS, ?_⟩, by simp [na_step, hc],
        fun x w hw => ?_⟩
      · intro r' hr
        simp only [na_step, hc, List.mem_append, List.mem_singleton] at hr ⊢
        rcases hr with hr | rfl
        · exact hok r' hr
        · exact na_comb_ok _ _ _ _ _ hla hlb hc
      · subst hw
        simp only [na_step, hc, List.map_append, List.map_cons, List.map_nil, na_eval2 op hop,
          na_comb_inl _ (wl D (List.ofFn x)) _ _ _ hc, na_look_val]
    · obtain ⟨ea, eb, hne⟩ := na_comb_inr _ _ _ _ hc
      rw [ea] at hla
      rw [eb] at hlb
      have hS' := na_strict_snoc hS (na_isAnd op) p.1 p.2 hla hlb hne
      refine ⟨⟨by simpa only [na_step, hc] using hS', ?_⟩, by simp [na_step, hc],
        fun x w hw => ?_⟩
      · intro r' hr
        simp only [na_step, hc, List.mem_append, List.mem_singleton, List.length_append,
          List.length_singleton] at hr ⊢
        rcases hr with hr | rfl
        · exact na_ok_mono (by omega) r' (hok r' hr)
        · show n + D.length < n + (D.length + 1)
          omega
      · subst hw
        have hWlen : (wl D (List.ofFn x)).length = n + D.length := by
          rw [wl_length, List.length_ofFn]
        have hW' : wl (D ++ [(na_isAnd op, p.1, p.2)]) (List.ofFn x) =
            wstep (wl D (List.ofFn x)) (na_isAnd op, p.1, p.2) := by
          rw [wl_append]; rfl
        have h1 : m.map (refVal (wstep (wl D (List.ofFn x)) (na_isAnd op, p.1, p.2))) =
            m.map (refVal (wl D (List.ofFn x))) :=
          List.map_congr_left (fun r hr => na_refVal_wstep _ _ r (by rw [hWlen]; exact hok r hr))
        have h2 : (wstep (wl D (List.ofFn x)) (na_isAnd op, p.1, p.2)).getD (n + D.length) false =
            gop (na_isAnd op) ((m.map (refVal (wl D (List.ofFn x)))).getD a false)
              ((m.map (refVal (wl D (List.ofFn x)))).getD b false) := by
          rw [← hWlen, wstep_getD_last, ← na_look_val, ← na_look_val, ea, eb]; rfl
        simp only [na_step, hc, hW', List.map_append, List.map_cons, List.map_nil, h1, refVal,
          h2, na_eval2 op hop]
  · simp at hlen

lemma na_fold_spec (n : ℕ) (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ st : List Ref × Dag, na_Good n st →
      na_Good n (gs.foldl (na_step n) st) ∧
      (gs.foldl (na_step n) st).2.length ≤ st.2.length + gs.length ∧
      ∀ (x : Fin n → Bool) (w : List Bool), st.1.map (refVal (wl st.2 (List.ofFn x))) = w →
        (gs.foldl (na_step n) st).1.map
            (refVal (wl (gs.foldl (na_step n) st).2 (List.ofFn x))) =
          gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w := by
  induction gs with
  | nil => intro st h; exact ⟨h, by simp, fun x w hw => hw⟩
  | cons g gs ih =>
    intro st h
    obtain ⟨h1, h2, h3⟩ := na_step_spec n st g (hgs g (by simp)) h
    obtain ⟨i1, i2, i3⟩ := ih (fun g' hg' => hgs g' (by simp [hg'])) _ h1
    refine ⟨i1, ?_, fun x w hw => ?_⟩
    · simp only [List.foldl_cons, List.length_cons]; omega
    · simp only [List.foldl_cons]; exact i3 x _ (h3 x w hw)

lemma na_init (n : ℕ) (x : Fin n → Bool) :
    ((List.range n).map Sum.inr).map (refVal (wl ([] : Dag) (List.ofFn x))) = List.ofFn x := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp [refVal, wl, List.getD_eq_getElem?_getD, h1]

lemma exists_strict_of_monotone2 {n : ℕ} (C : Circuit) (hmono : Monotone2 C) :
    (∃ b : Bool, ∀ x : Fin n → Bool, C.eval (List.ofFn x) = b) ∨
    (∃ i : Fin n, ∀ x : Fin n → Bool, C.eval (List.ofFn x) = x i) ∨
    (∃ D : Dag, Strict n D ∧ D ≠ [] ∧ D.length ≤ C.size ∧
      ∀ x : Fin n → Bool, val D x (outW n D) = C.eval (List.ofFn x)) := by
  have h0 : na_Good n ((List.range n).map Sum.inr, ([] : Dag)) := by
    refine ⟨fun j hj => absurd hj (by simp), fun r hr => ?_⟩
    simp only [List.mem_map, List.mem_range] at hr
    obtain ⟨k, hk, rfl⟩ := hr
    simpa [na_ok] using hk
  obtain ⟨⟨hS, hok⟩, hlen, hsem⟩ := na_fold_spec n C.gates hmono _ h0
  generalize C.gates.foldl (na_step n) ((List.range n).map Sum.inr, ([] : Dag)) = st
    at hS hok hlen hsem
  obtain ⟨m, D⟩ := st
  dsimp only at hS hok hlen hsem
  have hev : ∀ x : Fin n → Bool,
      C.eval (List.ofFn x) = refVal (wl D (List.ofFn x)) (na_look m C.output) := by
    intro x
    rw [na_look_val, hsem x (List.ofFn x) (na_init n x)]
    rfl
  have hk := na_look_ok _ m hok C.output
  rcases hr : na_look m C.output with b | k
  · exact Or.inl ⟨b, fun x => by rw [hev x, hr]; rfl⟩
  · rw [hr] at hk
    have hk' : k < n + D.length := hk
    by_cases hkn : k < n
    · exact Or.inr (Or.inl ⟨⟨k, hkn⟩, fun x => by rw [hev x, hr]; exact val_input D x k hkn⟩)
    · have hl : (D.take (k - n + 1)).length = k - n + 1 := by
        rw [List.length_take]; omega
      refine Or.inr (Or.inr ⟨D.take (k - n + 1), na_strict_take hS _, ?_, ?_, fun x => ?_⟩)
      · intro h
        rw [h] at hl
        simp at hl
      · rw [hl]
        simp only [List.length_nil, Nat.zero_add] at hlen
        unfold Circuit.size
        omega
      · have ho : outW n (D.take (k - n + 1)) = k := by unfold outW; rw [hl]; omega
        rw [ho, val_take D x (k - n + 1) k (by omega) (by omega), hev x, hr]
        rfl

lemma na_no_reader {D : Dag} {w : ℕ} (h : fanout D w = 0) (j : ℕ) (hj : j < D.length) :
    opA D j ≠ w ∧ opB D j ≠ w := by
  unfold fanout readers at h
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h
  have := h (Finset.mem_range.mpr hj)
  tauto

def na_sh (c a : ℕ) : ℕ := if c < a then a - 1 else a

def na_up (c w : ℕ) : ℕ := if w < c then w else w + 1

def na_del (n j : ℕ) (D : Dag) : Dag :=
  (D.eraseIdx j).map (fun g => (g.1, na_sh (n + j) g.2.1, na_sh (n + j) g.2.2))

lemma na_del_length (n j : ℕ) (D : Dag) (hj : j < D.length) :
    (na_del n j D).length = D.length - 1 := by
  simp [na_del, List.length_eraseIdx, hj]

lemma na_del_ops (n j : ℕ) (D : Dag) (k : ℕ) (hk : na_up j k < D.length) :
    tag (na_del n j D) k = tag D (na_up j k) ∧
    opA (na_del n j D) k = na_sh (n + j) (opA D (na_up j k)) ∧
    opB (na_del n j D) k = na_sh (n + j) (opB D (na_up j k)) := by
  have e : (na_del n j D).getD k (false, 0, 0) =
      ((D.getD (na_up j k) (false, 0, 0)).1, na_sh (n + j) (D.getD (na_up j k) (false, 0, 0)).2.1,
        na_sh (n + j) (D.getD (na_up j k) (false, 0, 0)).2.2) := by
    simp only [na_del, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eraseIdx]
    unfold na_up at hk ⊢
    split_ifs at hk ⊢ <;> simp [List.getElem?_eq_getElem hk]
  unfold tag opA opB
  rw [e]
  exact ⟨rfl, rfl, rfl⟩

lemma na_del_strict {n : ℕ} {D : Dag} (hS : Strict n D) (j : ℕ) (hj : j < D.length)
    (hf : fanout D (n + j) = 0) : Strict n (na_del n j D) := by
  intro k hk
  rw [na_del_length n j D hj] at hk
  have hk' : na_up j k < D.length := by unfold na_up; split_ifs <;> omega
  have hk2 : (k < j ∧ na_up j k = k) ∨ (j ≤ k ∧ na_up j k = k + 1) := by
    unfold na_up; split_ifs <;> omega
  obtain ⟨ha, hb, hab⟩ := hS _ hk'
  obtain ⟨ra, rb⟩ := na_no_reader hf _ hk'
  obtain ⟨-, ea, eb⟩ := na_del_ops n j D k hk'
  rw [ea, eb]
  generalize na_up j k = k' at *
  generalize opA D k' = a at *
  generalize opB D k' = b at *
  refine ⟨?_, ?_, ?_⟩ <;> unfold na_sh <;> split_ifs <;> omega

lemma na_del_val {n : ℕ} {D : Dag} (hS : Strict n D) (j : ℕ) (hj : j < D.length)
    (hf : fanout D (n + j) = 0) (x : Fin n → Bool) (w : ℕ) (hw : w < n + (D.length - 1)) :
    val (na_del n j D) x w = val D x (na_up (n + j) w) := by
  refine val_unique (na_del_strict hS j hj hf) x (fun u => val D x (na_up (n + j) u))
    (fun i hi => ?_) (fun k hk => ?_) w (by rw [na_del_length n j D hj]; exact hw)
  · have e : na_up (n + j) i = i := by unfold na_up; split_ifs <;> omega
    show val D x (na_up (n + j) i) = x ⟨i, hi⟩
    rw [e]; exact val_input D x i hi
  · rw [na_del_length n j D hj] at hk
    have hk' : na_up j k < D.length := by unfold na_up; split_ifs <;> omega
    obtain ⟨et, ea, eb⟩ := na_del_ops n j D k hk'
    obtain ⟨ra, rb⟩ := na_no_reader hf _ hk'
    have e1 : na_up (n + j) (n + k) = n + na_up j k := by unfold na_up; split_ifs <;> omega
    have e2 : ∀ a, a ≠ n + j → na_up (n + j) (na_sh (n + j) a) = a := by
      intro a ha; unfold na_up na_sh; split_ifs <;> omega
    show val D x (na_up (n + j) (n + k)) = gop (tag (na_del n j D) k)
      (val D x (na_up (n + j) (opA (na_del n j D) k)))
      (val D x (na_up (n + j) (opB (na_del n j D) k)))
    rw [e1, et, ea, eb, e2 _ ra, e2 _ rb]
    exact val_gate hS x _ hk'

lemma na_live_aux {n : ℕ} (F : (Fin n → Bool) → Bool)
    (hess : ∀ i : Fin n, ∃ x y : Fin n → Bool, (∀ k, k ≠ i → x k = y k) ∧ F x ≠ F y) :
    ∀ (s : ℕ) (D : Dag), D.length = s → Strict n D → D ≠ [] →
      (∀ x : Fin n → Bool, val D x (outW n D) = F x) →
      ∃ D' : Dag, StrictLive n D' ∧ D'.length ≤ s ∧
        ∀ x : Fin n → Bool, val D' x (outW n D') = F x := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro D hlen hS hne hD
    have hpos : 0 < D.length := List.length_pos_iff.mpr hne
    by_cases hL : Live n D
    · exact ⟨D, ⟨hS, hL, hne⟩, hlen.le, hD⟩
    · obtain ⟨w, hw, hf0⟩ : ∃ w, w + 1 < n + D.length ∧ fanout D w = 0 := by
        by_contra hcon
        exact hL (fun w hw => by
          by_contra h0
          exact hcon ⟨w, hw, by omega⟩)
      by_cases hwn : w < n
      · exfalso
        obtain ⟨x, y, hxy, hFne⟩ := hess ⟨w, hwn⟩
        apply hFne
        rw [← hD x, ← hD y]
        have hout : outW n D ≠ w := by unfold outW; omega
        have key := val_unique hS y (fun u => if u = w then y ⟨w, hwn⟩ else val D x u)
          (fun i hi => by
            by_cases hiw : i = w
            · subst hiw; simp
            · simp only [hiw, ite_false]
              rw [val_input D x i hi]
              exact hxy ⟨i, hi⟩ (fun h => hiw (congrArg Fin.val h)))
          (fun j hj => by
            obtain ⟨ha, hb⟩ := na_no_reader hf0 j hj
            have hnj : n + j ≠ w := by omega
            simp only [hnj, ha, hb, ite_false]
            exact val_gate hS x j hj)
          (outW n D) (by unfold outW; omega)
        simp only [hout, ite_false] at key
        exact key.symm
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < D.length := by omega
        have hl := na_del_length n j D hj
        obtain ⟨D', h1, h2, h3⟩ := ih (D.length - 1) (by omega) (na_del n j D) hl
          (na_del_strict hS j hj hf0)
          (fun h => by rw [h] at hl; simp at hl; omega)
          (fun x => by
            have ho : outW n (na_del n j D) = n + (D.length - 1) - 1 := by unfold outW; rw [hl]
            have hu : na_up (n + j) (n + (D.length - 1) - 1) = outW n D := by
              unfold na_up outW; split_ifs <;> omega
            rw [ho, na_del_val hS j hj hf0 x _ (by omega), hu]
            exact hD x)
        exact ⟨D', h1, by omega, h3⟩

lemma exists_strictLive_of_strict {n : ℕ} (F : (Fin n → Bool) → Bool)
    (hess : ∀ i : Fin n, ∃ x y : Fin n → Bool, (∀ k, k ≠ i → x k = y k) ∧ F x ≠ F y)
    (D : Dag) (hS : Strict n D) (hne : D ≠ [])
    (hD : ∀ x : Fin n → Bool, val D x (outW n D) = F x) :
    ∃ D' : Dag, StrictLive n D' ∧ D'.length ≤ D.length ∧
      ∀ x : Fin n → Bool, val D' x (outW n D') = F x :=
  na_live_aux F hess D.length D rfl hS hne hD

lemma normalize_strictLive {n : ℕ} (C : Circuit) (hmono : Monotone2 C)
    (hnc : ∀ b : Bool, ∃ x : Fin n → Bool, C.eval (List.ofFn x) ≠ b)
    (hnp : ∀ i : Fin n, ∃ x : Fin n → Bool, C.eval (List.ofFn x) ≠ x i)
    (hess : ∀ i : Fin n, ∃ x y : Fin n → Bool, (∀ k, k ≠ i → x k = y k) ∧
      C.eval (List.ofFn x) ≠ C.eval (List.ofFn y)) :
    ∃ D : Dag, StrictLive n D ∧ D.length ≤ C.size ∧
      ∀ x : Fin n → Bool, val D x (outW n D) = C.eval (List.ofFn x) := by
  rcases exists_strict_of_monotone2 (n := n) C hmono with
    ⟨b, hb⟩ | ⟨i, hi⟩ | ⟨D, hS, hne, hlen, hD⟩
  · obtain ⟨x, hx⟩ := hnc b
    exact absurd (hb x) hx
  · obtain ⟨x, hx⟩ := hnp i
    exact absurd (hi x) hx
  · obtain ⟨D', h1, h2, h3⟩ :=
      exists_strictLive_of_strict (fun x => C.eval (List.ofFn x)) hess D hS hne hD
    exact ⟨D', h1, by omega, h3⟩

section SurplusFlow

variable {n : ℕ} {D : Dag}

lemma sb_mem_inner {w : ℕ} : w ∈ inner n D ↔ w + 1 < n + D.length := by
  unfold inner; rw [Finset.mem_range]; omega

lemma sb_src_false (j : ℕ) : src D (j, false) = opA D j := by simp [src]

lemma sb_src_true (j : ℕ) : src D (j, true) = opB D j := by simp [src]

lemma fanout_eq_zero_of_ge (hS : Strict n D) (w : ℕ) (h : n + D.length ≤ w + 1) :
    fanout D w = 0 := by
  unfold fanout readers
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro j hj
  have hj2 := Finset.mem_range.mp hj
  have := hS j hj2
  omega

lemma lt_of_fanout_pos (hS : Strict n D) {w : ℕ} (h : 1 ≤ fanout D w) :
    w + 1 < n + D.length := by
  by_contra hc
  have := fanout_eq_zero_of_ge hS w (by omega)
  omega

lemma sb_card_arcs_filter (P : ℕ × Bool → Prop) [DecidablePred P] :
    ((arcs D).filter P).card = ∑ j ∈ Finset.range D.length,
      ((if P (j, false) then 1 else 0) + (if P (j, true) then 1 else 0)) := by
  rw [Finset.card_filter, arcs, Finset.sum_product]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Fintype.sum_bool, add_comm]

lemma sb_card_arcs : (arcs D).card = 2 * D.length := by
  simp [arcs, Finset.card_product, Nat.mul_comm]

lemma sb_src_lt (hS : Strict n D) (e : ℕ × Bool) (he : e ∈ arcs D) :
    src D e + 1 < n + D.length := by
  obtain ⟨j, c⟩ := e
  have hj : j < D.length := by simpa [arcs] using he
  have := hS j hj
  cases c
  · rw [sb_src_false]; omega
  · rw [sb_src_true]; omega

lemma sb_fanout_arcs (hS : Strict n D) (w : ℕ) :
    fanout D w = ((arcs D).filter (fun e => src D e = w)).card := by
  rw [sb_card_arcs_filter, fanout, readers, Finset.card_filter]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have := (hS j (Finset.mem_range.mp hj)).2.2
  rw [sb_src_false, sb_src_true]
  split_ifs <;> omega

lemma sb_sum_fanout_eq (hS : Strict n D) (K : Finset ℕ) :
    ∑ w ∈ K, fanout D w = ((arcs D).filter (fun e => src D e ∈ K)).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := src D)
    (s := (arcs D).filter (fun e => src D e ∈ K)) (t := K)
    (fun e he => Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp he)).2)]
  refine Finset.sum_congr rfl (fun w hw => ?_)
  rw [sb_fanout_arcs hS, Finset.filter_filter]
  congr 1
  ext e
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨he, rfl⟩; exact ⟨he, hw, rfl⟩
  · rintro ⟨he, -, h⟩; exact ⟨he, h⟩

lemma sb_surplus_add_card {K : Finset ℕ} (hL : ∀ w ∈ K, 1 ≤ fanout D w) :
    surplusOn D K + K.card = ∑ w ∈ K, fanout D w := by
  rw [surplusOn, Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun w hw => Nat.sub_add_cancel (hL w hw))

lemma surplus_identity (h : StrictLive n D) : totalSurplus n D + n = D.length + 1 := by
  obtain ⟨hS, hL, hne⟩ := h
  have hpos : 0 < D.length := List.length_pos_iff.mpr hne
  have h1 : surplusOn D (inner n D) + (inner n D).card = ∑ w ∈ inner n D, fanout D w :=
    sb_surplus_add_card (fun w hw => hL w (sb_mem_inner.mp hw))
  have h2 : ∑ w ∈ inner n D, fanout D w = 2 * D.length := by
    rw [sb_sum_fanout_eq hS, Finset.filter_true_of_mem, sb_card_arcs]
    intro e he
    exact sb_mem_inner.mpr (sb_src_lt hS e he)
  have h3 : (inner n D).card = n + D.length - 1 := Finset.card_range _
  unfold totalSurplus
  omega

lemma totalSurplus_split (n : ℕ) (D : Dag) : totalSurplus n D = Bplus n D + Bzero n D := by
  unfold totalSurplus Bplus Bzero surplusOn
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

lemma live_reaches_out (h : StrictLive n D) (w : ℕ) (hw : w < n + D.length) :
    Relation.ReflTransGen (fun a b => b < n + D.length ∧ n ≤ b ∧
      (opA D (b - n) = a ∨ opB D (b - n) = a)) w (outW n D) := by
  obtain ⟨hS, hL, -⟩ := h
  generalize hk : n + D.length - w = k
  induction k using Nat.strong_induction_on generalizing w with
  | _ k ih =>
    by_cases hlast : w + 1 = n + D.length
    · have hw2 : w = outW n D := by unfold outW; omega
      rw [hw2]
    · obtain ⟨j, hj⟩ := Finset.card_pos.mp (hL w (by omega))
      simp only [readers, Finset.mem_filter, Finset.mem_range] at hj
      have hs := hS j hj.1
      refine Relation.ReflTransGen.head (b := n + j) ⟨by omega, by omega, ?_⟩
        (ih (n + D.length - (n + j)) (by omega) (n + j) (by omega) rfl)
      simpa using hj.2

lemma mem_supp {v : Fin n} {w : ℕ} : v ∈ supp n D w ↔ val D (single v) w = true := by
  simp [supp]

lemma val_mono (hS : Strict n D) (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true)
    (w : ℕ) : val D x w = true → val D y w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · rw [val_input D x w hn, val_input D y w hn]; exact hxy _
    · by_cases hw : w < n + D.length
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < D.length := by omega
        obtain ⟨ha, hb, -⟩ := hS j hj
        rw [val_gate hS x j hj, val_gate hS y j hj]
        have h1 := ih _ ha
        have h2 := ih _ hb
        cases tag D j <;>
          simp only [gop_true, gop_false, Bool.and_eq_true, Bool.or_eq_true] <;> tauto
      · rw [val_ge D x w (by omega)]; simp

lemma supp_input (D : Dag) (i : Fin n) : supp n D i.val = {i} := by
  ext v
  rw [mem_supp, val_input D (single v) i.val i.isLt]
  simp [single, eq_comm]

lemma supp_ge (D : Dag) (w : ℕ) (h : n + D.length ≤ w) : supp n D w = ∅ := by
  ext v
  simp [mem_supp, val_ge D (single v) w h]

lemma supp_gate (hS : Strict n D) (j : ℕ) (hj : j < D.length) :
    supp n D (n + j) = if tag D j = true then supp n D (opA D j) ∩ supp n D (opB D j)
      else supp n D (opA D j) ∪ supp n D (opB D j) := by
  ext v
  rw [mem_supp, val_gate hS _ j hj]
  cases tag D j <;> simp [mem_supp]

lemma carrier_flow (h : StrictLive n D) (K : Finset ℕ) (hK : K ⊆ inner n D)
    (hpred : ∀ j, j < D.length → n + j ∈ K → opA D j ∈ K ∨ opB D j ∈ K) :
    (exitArcs n D K).card + (merges n D K).card = (sources n K).card + surplusOn D K := by
  obtain ⟨hS, hL, -⟩ := h
  have hKlt : ∀ w ∈ K, w + 1 < n + D.length := fun w hw => sb_mem_inner.mp (hK hw)
  have h1 : surplusOn D K + K.card = ((arcs D).filter (fun e => src D e ∈ K)).card := by
    rw [← sb_sum_fanout_eq hS, sb_surplus_add_card (fun w hw => hL w (hKlt w hw))]
  have h2 := Finset.card_filter_add_card_filter_not
    (s := (arcs D).filter (fun e => src D e ∈ K)) (fun e : ℕ × Bool => n + e.1 ∈ K)
  rw [Finset.filter_filter, Finset.filter_filter] at h2
  have h3 : ((arcs D).filter (fun e => src D e ∈ K ∧ n + e.1 ∈ K)).card =
      ((Finset.range D.length).filter (fun j => n + j ∈ K)).card + (merges n D K).card := by
    rw [sb_card_arcs_filter, merges, Finset.card_filter, Finset.card_filter,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have := hpred j (Finset.mem_range.mp hj)
    rw [sb_src_false, sb_src_true]
    by_cases hj2 : n + j ∈ K <;> by_cases ha : opA D j ∈ K <;> by_cases hb : opB D j ∈ K <;>
      simp_all
  have h4 : K.card = (sources n K).card +
      ((Finset.range D.length).filter (fun j => n + j ∈ K)).card := by
    rw [← Finset.card_filter_add_card_filter_not (s := K) (fun w => w < n), sources]
    congr 1
    have himg : K.filter (fun w => ¬ w < n) =
        ((Finset.range D.length).filter (fun j => n + j ∈ K)).image (fun j => n + j) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range]
      constructor
      · rintro ⟨hw, hn⟩
        have := hKlt w hw
        exact ⟨w - n, ⟨by omega, by rwa [Nat.add_sub_cancel' (by omega)]⟩, by omega⟩
      · rintro ⟨j, ⟨-, hj⟩, rfl⟩
        exact ⟨hj, by omega⟩
    rw [himg, Finset.card_image_of_injective _ (add_right_injective n)]
  unfold exitArcs
  omega

lemma sb_carrierT_sub (T : Finset (Fin n))
    (hout : supp n D (outW n D) ∩ T = ∅) : carrierT n D T ⊆ inner n D := by
  intro w hw
  simp only [carrierT, Finset.mem_filter, Finset.mem_range] at hw
  rw [sb_mem_inner]
  by_contra hc
  have hw2 : w = outW n D := by unfold outW; omega
  rw [hw2, hout] at hw
  exact Finset.not_nonempty_empty hw.2

lemma sb_sources_carrierT (D : Dag) (T : Finset (Fin n)) :
    (sources n (carrierT n D T)).card = T.card := by
  have himg : sources n (carrierT n D T) = T.image (fun v : Fin n => v.val) := by
    ext w
    simp only [sources, carrierT, Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨⟨-, v, hv⟩, hw⟩
      have hs : supp n D w = {⟨w, hw⟩} := supp_input D ⟨w, hw⟩
      rw [hs, Finset.mem_inter, Finset.mem_singleton] at hv
      exact ⟨v, hv.2, by rw [hv.1]⟩
    · rintro ⟨v, hv, rfl⟩
      refine ⟨⟨by have := v.isLt; omega, v, ?_⟩, v.isLt⟩
      rw [supp_input]; simp [hv]
  rw [himg, Finset.card_image_of_injective _ Fin.val_injective]

lemma carrier_flow_union (h : StrictLive n D) (T : Finset (Fin n))
    (hout : supp n D (outW n D) ∩ T = ∅) :
    (exitArcs n D (carrierT n D T)).card + (merges n D (carrierT n D T)).card =
      T.card + surplusOn D (carrierT n D T) := by
  rw [← sb_sources_carrierT D T]
  refine carrier_flow h _ (sb_carrierT_sub T hout) (fun j hj hK => ?_)
  obtain ⟨ha, hb, -⟩ := h.1 j hj
  simp only [carrierT, Finset.mem_filter, Finset.mem_range] at hK ⊢
  obtain ⟨v, hv⟩ := hK.2
  rw [Finset.mem_inter, supp_gate h.1 j hj] at hv
  split_ifs at hv with ht
  · rw [Finset.mem_inter] at hv
    exact Or.inl ⟨by omega, v, Finset.mem_inter.mpr ⟨hv.1.1, hv.2⟩⟩
  · rw [Finset.mem_union] at hv
    rcases hv.1 with h1 | h1
    · exact Or.inl ⟨by omega, v, Finset.mem_inter.mpr ⟨h1, hv.2⟩⟩
    · exact Or.inr ⟨by omega, v, Finset.mem_inter.mpr ⟨h1, hv.2⟩⟩

lemma carrier_flow_diff (h : StrictLive n D) (x y : Fin n) (hxy : x ≠ y)
    (hout : x ∉ supp n D (outW n D)) :
    (exitArcs n D (carrierDiff n D x y)).card + (merges n D (carrierDiff n D x y)).card =
      1 + surplusOn D (carrierDiff n D x y) := by
  have hsub : carrierDiff n D x y ⊆ inner n D := by
    intro w hw
    simp only [carrierDiff, Finset.mem_filter, Finset.mem_range] at hw
    rw [sb_mem_inner]
    by_contra hc
    have hw2 : w = outW n D := by unfold outW; omega
    rw [hw2] at hw
    exact hout hw.2.1
  have hsrc : sources n (carrierDiff n D x y) = {x.val} := by
    ext w
    simp only [sources, carrierDiff, Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨-, hx, -⟩, hw⟩
      have hs : supp n D w = {⟨w, hw⟩} := supp_input D ⟨w, hw⟩
      rw [hs, Finset.mem_singleton] at hx
      rw [hx]
    · rintro rfl
      refine ⟨⟨by have := x.isLt; omega, ?_, ?_⟩, x.isLt⟩
      · rw [supp_input]; exact Finset.mem_singleton_self x
      · rw [supp_input, Finset.mem_singleton]; exact fun hc => hxy hc.symm
  have hfl := carrier_flow h _ hsub (fun j hj hK => ?_)
  · rw [hsrc, Finset.card_singleton] at hfl; exact hfl
  · obtain ⟨ha, hb, -⟩ := h.1 j hj
    simp only [carrierDiff, Finset.mem_filter, Finset.mem_range] at hK ⊢
    obtain ⟨-, hx, hy⟩ := hK
    rw [supp_gate h.1 j hj] at hx hy
    split_ifs at hx hy with ht
    · rw [Finset.mem_inter] at hx hy
      by_cases hya : y ∈ supp n D (opA D j)
      · exact Or.inr ⟨by omega, hx.2, fun hc => hy ⟨hya, hc⟩⟩
      · exact Or.inl ⟨by omega, hx.1, hya⟩
    · rw [Finset.mem_union] at hx hy
      rcases hx with h1 | h1
      · exact Or.inl ⟨by omega, h1, fun hc => hy (Or.inl hc)⟩
      · exact Or.inr ⟨by omega, h1, fun hc => hy (Or.inr hc)⟩

lemma mem_units {u : Σ _ : ℕ, ℕ} :
    u ∈ units n D ↔ u.1 ∈ inner n D ∧ u.2 + 1 < fanout D u.1 := by
  rw [units, Finset.mem_sigma, Finset.mem_range]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩

lemma sb_card_units_filter (n : ℕ) (D : Dag) (p : ℕ → Prop) [DecidablePred p] :
    ((units n D).filter (fun u => p u.1)).card = surplusOn D ((inner n D).filter p) := by
  have hs : (units n D).filter (fun u => p u.1) =
      ((inner n D).filter p).sigma (fun w => Finset.range (fanout D w - 1)) := by
    ext u; simp only [units, Finset.mem_filter, Finset.mem_sigma]; tauto
  rw [hs, Finset.card_sigma, surplusOn]
  simp

lemma card_unitsPlus (n : ℕ) (D : Dag) : (unitsPlus n D).card = Bplus n D := by
  unfold unitsPlus Bplus
  exact sb_card_units_filter n D (fun w => (supp n D w).Nonempty)

lemma mem_eligSet {v : Fin n} :
    v ∈ eligSet n D ↔ ∃ w, 2 ≤ fanout D w ∧ v ∈ supp n D w := by
  simp only [eligSet, branchW, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨w, ⟨-, h2⟩, hv⟩; exact ⟨w, h2, hv⟩
  · rintro ⟨w, h2, hv⟩
    refine ⟨w, ⟨?_, h2⟩, hv⟩
    by_contra hc
    rw [supp_ge D w (by omega)] at hv
    exact Finset.notMem_empty v hv

lemma mem_ineligSet {v : Fin n} :
    v ∈ ineligSet n D ↔ ∀ w, v ∈ supp n D w → fanout D w ≤ 1 := by
  rw [ineligSet, Finset.mem_sdiff, mem_eligSet]
  constructor
  · rintro ⟨-, h⟩ w hw
    by_contra hc
    exact h ⟨w, by omega, hw⟩
  · intro h
    refine ⟨Finset.mem_univ v, ?_⟩
    rintro ⟨w, hw, hv⟩
    have := h w hv
    omega

lemma sb_singleton_inter_nonempty {v : Fin n} {T : Finset (Fin n)} :
    (({v} : Finset (Fin n)) ∩ T).Nonempty ↔ v ∈ T := by
  constructor
  · rintro ⟨u, hu⟩
    rw [Finset.mem_inter, Finset.mem_singleton] at hu
    exact hu.1 ▸ hu.2
  · intro h
    exact ⟨v, Finset.mem_inter.mpr ⟨Finset.mem_singleton_self v, h⟩⟩

lemma sb_reserved_inj (b : Fin n → ℕ) (hb : PureBranch n D b) :
    Set.InjOn (fun v => (⟨b v, 0⟩ : Σ _ : ℕ, ℕ)) (eligSet n D : Set (Fin n)) := by
  intro v hv v2 hv2 he
  have hbv : b v = b v2 := congrArg Sigma.fst he
  have h1 := (hb v hv).2
  rw [hbv, (hb v2 hv2).2] at h1
  exact (Finset.singleton_injective h1).symm

lemma reserved_subset (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b) :
    reservedUnits n D b ⊆ unitsPlus n D := by
  intro u hu
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨h2, hs⟩ := hb v hv
  have h1 : 1 ≤ fanout D (b v) := by omega
  rw [unitsPlus, Finset.mem_filter, mem_units]
  refine ⟨⟨sb_mem_inner.mpr (lt_of_fanout_pos hS h1), ?_⟩, ?_⟩
  · show 0 + 1 < fanout D (b v)
    omega
  · show (supp n D (b v)).Nonempty
    rw [hs]; exact Finset.singleton_nonempty v

lemma card_reserved (b : Fin n → ℕ) (hb : PureBranch n D b) :
    (reservedUnits n D b).card = (eligSet n D).card :=
  Finset.card_image_of_injOn (sb_reserved_inj b hb)

lemma elig_le_Bplus (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b) :
    (eligSet n D).card ≤ Bplus n D := by
  rw [← card_reserved b hb, ← card_unitsPlus]
  exact Finset.card_le_card (reserved_subset hS b hb)

lemma card_residual (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b) :
    (residualUnits n D b).card + (eligSet n D).card = Bplus n D := by
  rw [← card_reserved b hb, ← card_unitsPlus]
  exact Finset.card_sdiff_add_card_eq_card (reserved_subset hS b hb)

lemma surplus_carrierT_eq (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b)
    (T : Finset (Fin n)) :
    surplusOn D (carrierT n D T) = (T ∩ eligSet n D).card +
      ((residualUnits n D b).filter (fun u => (supp n D u.1 ∩ T).Nonempty)).card := by
  have h1 : surplusOn D (carrierT n D T) =
      ((units n D).filter (fun u => (supp n D u.1 ∩ T).Nonempty)).card := by
    rw [sb_card_units_filter n D (fun w => (supp n D w ∩ T).Nonempty)]
    symm
    refine Finset.sum_subset (fun w hw => ?_) (fun w hw hnot => ?_)
    · rw [Finset.mem_filter] at hw
      have := sb_mem_inner.mp hw.1
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hw.2⟩
    · rw [carrierT, Finset.mem_filter] at hw
      have hni : w ∉ inner n D := fun hc => hnot (Finset.mem_filter.mpr ⟨hc, hw.2⟩)
      rw [sb_mem_inner] at hni
      simp [fanout_eq_zero_of_ge hS w (by omega)]
  have h2 : (units n D).filter (fun u => (supp n D u.1 ∩ T).Nonempty) =
      (reservedUnits n D b).filter (fun u => (supp n D u.1 ∩ T).Nonempty) ∪
        (residualUnits n D b).filter (fun u => (supp n D u.1 ∩ T).Nonempty) := by
    ext u
    have hsub := reserved_subset hS b hb
    simp only [residualUnits, unitsPlus, Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · intro hu
      by_cases hr : u ∈ reservedUnits n D b
      · exact Or.inl ⟨hr, hu.2⟩
      · exact Or.inr ⟨⟨⟨hu.1, hu.2.mono Finset.inter_subset_left⟩, hr⟩, hu.2⟩
    · rintro (hu | hu)
      · exact ⟨(Finset.mem_filter.mp (hsub hu.1)).1, hu.2⟩
      · exact ⟨hu.1.1.1, hu.2⟩
  have h3 : Disjoint ((reservedUnits n D b).filter (fun u => (supp n D u.1 ∩ T).Nonempty))
      ((residualUnits n D b).filter (fun u => (supp n D u.1 ∩ T).Nonempty)) :=
    Finset.disjoint_filter_filter Finset.disjoint_sdiff
  have h4 : (reservedUnits n D b).filter (fun u => (supp n D u.1 ∩ T).Nonempty) =
      (T ∩ eligSet n D).image (fun v => (⟨b v, 0⟩ : Σ _ : ℕ, ℕ)) := by
    rw [reservedUnits, Finset.filter_image]
    congr 1
    ext v
    simp only [Finset.mem_filter, Finset.mem_inter]
    constructor
    · rintro ⟨hv, hne⟩
      rw [(hb v hv).2, sb_singleton_inter_nonempty] at hne
      exact ⟨hne, hv⟩
    · rintro ⟨hT, hv⟩
      refine ⟨hv, ?_⟩
      rw [(hb v hv).2, sb_singleton_inter_nonempty]
      exact hT
  rw [h1, h2, Finset.card_union_of_disjoint h3, h4,
    Finset.card_image_of_injOn ((sb_reserved_inj b hb).mono
      (Finset.coe_subset.mpr Finset.inter_subset_right))]

lemma surplus_carrierT_le (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b)
    (T : Finset (Fin n)) :
    surplusOn D (carrierT n D T) + (eligSet n D).card ≤
      (T ∩ eligSet n D).card + Bplus n D := by
  have h1 := surplus_carrierT_eq hS b hb T
  have h2 := card_residual hS b hb
  have h3 := Finset.card_filter_le (residualUnits n D b)
    (fun u => (supp n D u.1 ∩ T).Nonempty)
  omega

end SurplusFlow

def liftP {n : ℕ} (σ : Equiv.Perm (Fin n)) (w : ℕ) : ℕ :=
  if h : w < n then (σ ⟨w, h⟩).val else w

def relabel {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) : Dag :=
  D.map (fun g => (g.1, liftP σ g.2.1, liftP σ g.2.2))

lemma tr_liftP_lt {n : ℕ} (σ : Equiv.Perm (Fin n)) {w : ℕ} (h : w < n) :
    liftP σ w = (σ ⟨w, h⟩).val := by
  simp [liftP, h]

lemma tr_liftP_ge {n : ℕ} (σ : Equiv.Perm (Fin n)) {w : ℕ} (h : n ≤ w) : liftP σ w = w := by
  simp [liftP, Nat.not_lt.mpr h]

lemma tr_liftP_lt_iff {n : ℕ} (σ : Equiv.Perm (Fin n)) {m : ℕ} (hm : n ≤ m) (w : ℕ) :
    liftP σ w < m ↔ w < m := by
  by_cases h : w < n
  · rw [tr_liftP_lt σ h]
    have := (σ ⟨w, h⟩).isLt
    constructor <;> intro <;> omega
  · rw [tr_liftP_ge σ (Nat.not_lt.mp h)]

lemma liftP_inv {n : ℕ} (σ : Equiv.Perm (Fin n)) (w : ℕ) : liftP σ⁻¹ (liftP σ w) = w := by
  by_cases h : w < n
  · rw [tr_liftP_lt σ h, tr_liftP_lt σ⁻¹ (σ ⟨w, h⟩).isLt]; simp
  · rw [tr_liftP_ge σ (Nat.not_lt.mp h), tr_liftP_ge σ⁻¹ (Nat.not_lt.mp h)]

lemma tr_liftP_inv' {n : ℕ} (σ : Equiv.Perm (Fin n)) (w : ℕ) : liftP σ (liftP σ⁻¹ w) = w := by
  simpa using liftP_inv σ⁻¹ w

lemma tr_liftP_inj {n : ℕ} (σ : Equiv.Perm (Fin n)) {a b : ℕ} :
    liftP σ a = liftP σ b ↔ a = b := by
  refine ⟨fun h => ?_, congrArg _⟩
  have := congrArg (liftP σ⁻¹) h
  rwa [liftP_inv, liftP_inv] at this

lemma relabel_length {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) :
    (relabel σ D).length = D.length := by
  simp [relabel]

lemma tr_tag {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) (j : ℕ) (hj : j < D.length) :
    tag (relabel σ D) j = tag D j := by
  rw [tag_eq _ j (by rw [relabel_length]; exact hj), tag_eq D j hj]; simp [relabel]

lemma tr_opA {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) (j : ℕ) (hj : j < D.length) :
    opA (relabel σ D) j = liftP σ (opA D j) := by
  rw [opA_eq _ j (by rw [relabel_length]; exact hj), opA_eq D j hj]; simp [relabel]

lemma tr_opB {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) (j : ℕ) (hj : j < D.length) :
    opB (relabel σ D) j = liftP σ (opB D j) := by
  rw [opB_eq _ j (by rw [relabel_length]; exact hj), opB_eq D j hj]; simp [relabel]

lemma relabel_strict {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) :
    Strict n (relabel σ D) := by
  intro j hj
  rw [relabel_length] at hj
  obtain ⟨ha, hb, hab⟩ := hS j hj
  rw [tr_opA σ D j hj, tr_opB σ D j hj]
  exact ⟨(tr_liftP_lt_iff σ (Nat.le_add_right n j) _).mpr ha,
    (tr_liftP_lt_iff σ (Nat.le_add_right n j) _).mpr hb, fun h => hab ((tr_liftP_inj σ).mp h)⟩

lemma relabel_val {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D)
    (x : Fin n → Bool) (w : ℕ) :
    val (relabel σ D) x (liftP σ w) = val D (fun i => x (σ i)) w := by
  by_cases hw : w < n + D.length
  · refine (val_unique (relabel_strict σ hS) x
      (fun w' => val D (fun i => x (σ i)) (liftP σ⁻¹ w')) ?_ ?_ (liftP σ w) ?_).trans ?_
    · intro i hi
      show val D (fun i => x (σ i)) (liftP σ⁻¹ i) = x ⟨i, hi⟩
      rw [tr_liftP_lt σ⁻¹ hi, val_input D _ _ (σ⁻¹ ⟨i, hi⟩).isLt]
      simp
    · intro j hj
      rw [relabel_length] at hj
      show val D (fun i => x (σ i)) (liftP σ⁻¹ (n + j)) =
        gop (tag (relabel σ D) j) (val D (fun i => x (σ i)) (liftP σ⁻¹ (opA (relabel σ D) j)))
          (val D (fun i => x (σ i)) (liftP σ⁻¹ (opB (relabel σ D) j)))
      rw [tr_liftP_ge σ⁻¹ (Nat.le_add_right n j), tr_tag σ D j hj, tr_opA σ D j hj,
        tr_opB σ D j hj, liftP_inv, liftP_inv, val_gate hS _ j hj]
    · rw [relabel_length]; exact (tr_liftP_lt_iff σ (Nat.le_add_right _ _) w).mpr hw
    · show val D (fun i => x (σ i)) (liftP σ⁻¹ (liftP σ w)) = _
      rw [liftP_inv]
  · have hw' := Nat.not_lt.mp hw
    rw [tr_liftP_ge σ (le_trans (Nat.le_add_right _ _) hw'),
      val_ge _ _ _ (by rw [relabel_length]; exact hw'), val_ge _ _ _ hw']

lemma relabel_fanout {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) (w : ℕ) :
    fanout (relabel σ D) (liftP σ w) = fanout D w := by
  unfold fanout readers
  rw [relabel_length]
  congr 1
  apply Finset.filter_congr
  intro j hj
  have hj' := Finset.mem_range.mp hj
  rw [tr_opA σ D j hj', tr_opB σ D j hj', tr_liftP_inj, tr_liftP_inj]

lemma relabel_live {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hL : Live n D) :
    Live n (relabel σ D) := by
  rcases eq_or_ne D [] with rfl | hne
  · exact hL
  · intro w' hw'
    rw [relabel_length] at hw'
    have hpos := List.length_pos_iff.mpr hne
    rw [← tr_liftP_inv' σ w', relabel_fanout]
    apply hL
    by_cases h : w' < n
    · have := (tr_liftP_lt_iff σ⁻¹ le_rfl w').mpr h
      omega
    · rw [tr_liftP_ge σ⁻¹ (Nat.not_lt.mp h)]; exact hw'

lemma relabel_strictLive {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (h : StrictLive n D) :
    StrictLive n (relabel σ D) :=
  ⟨relabel_strict σ h.1, relabel_live σ h.2.1, by simpa [relabel] using h.2.2⟩

lemma relabel_out {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) (hne : D ≠ [])
    (x : Fin n → Bool) :
    val (relabel σ D) x (outW n (relabel σ D)) = val D (fun i => x (σ i)) (outW n D) := by
  have hpos := List.length_pos_iff.mpr hne
  have e : outW n (relabel σ D) = liftP σ (outW n D) := by
    rw [tr_liftP_ge σ (by unfold outW; omega)]; simp [outW, relabel_length]
  rw [e, relabel_val σ hS]

lemma tr_single_comp {n : ℕ} (σ : Equiv.Perm (Fin n)) (v : Fin n) :
    (fun i => single v (σ i)) = single (σ⁻¹ v) := by
  funext i
  simp only [single, decide_eq_decide]
  constructor
  · intro h; rw [← h]; simp
  · intro h; rw [h]; simp

lemma relabel_supp {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) (w : ℕ) :
    supp n (relabel σ D) (liftP σ w) = (supp n D w).image σ := by
  ext v
  simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  rw [relabel_val σ hS, tr_single_comp]
  constructor
  · intro h; exact ⟨σ⁻¹ v, h, by simp⟩
  · rintro ⟨a, ha, rfl⟩; simpa using ha

lemma relabel_eligSet {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) :
    eligSet n (relabel σ D) = (eligSet n D).image σ := by
  ext v
  simp only [eligSet, Finset.mem_biUnion, Finset.mem_image, branchW, Finset.mem_filter,
    Finset.mem_range]
  constructor
  · rintro ⟨w', ⟨hw', hf⟩, hv⟩
    obtain ⟨w, rfl⟩ : ∃ w, w' = liftP σ w := ⟨liftP σ⁻¹ w', (tr_liftP_inv' σ w').symm⟩
    rw [relabel_supp σ hS, Finset.mem_image] at hv
    obtain ⟨a, ha, rfl⟩ := hv
    rw [relabel_fanout] at hf
    rw [relabel_length, tr_liftP_lt_iff σ (Nat.le_add_right _ _)] at hw'
    exact ⟨a, ⟨w, ⟨hw', hf⟩, ha⟩, rfl⟩
  · rintro ⟨a, ⟨w, ⟨hw, hf⟩, ha⟩, rfl⟩
    refine ⟨liftP σ w, ⟨?_, ?_⟩, ?_⟩
    · rw [relabel_length]; exact (tr_liftP_lt_iff σ (Nat.le_add_right _ _) w).mpr hw
    · rw [relabel_fanout]; exact hf
    · rw [relabel_supp σ hS]; exact Finset.mem_image_of_mem _ ha

lemma relabel_ineligSet {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) :
    ineligSet n (relabel σ D) = (ineligSet n D).image σ := by
  ext v
  simp only [ineligSet, relabel_eligSet σ hS, Finset.mem_sdiff, Finset.mem_univ, true_and,
    Finset.mem_image]
  constructor
  · intro h
    exact ⟨σ⁻¹ v, fun hm => h ⟨σ⁻¹ v, hm, by simp⟩, by simp⟩
  · rintro ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    exact ha (σ.injective hab ▸ hb)

lemma inelig_card_add (n : ℕ) (D : Dag) : (ineligSet n D).card + (eligSet n D).card = n := by
  have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (eligSet n D))
  rw [Finset.card_univ, Fintype.card_fin] at h
  exact h

def sem_Edge {n : ℕ} (G : Fin n → Fin n → Prop) (x : Fin n → Bool) : Prop :=
  ∃ u v : Fin n, G u v ∧ x u = true ∧ x v = true

def sem_Comp (n : ℕ) (G : Fin n → Fin n → Prop) (D : Dag) : Prop :=
  ∀ x : Fin n → Bool, val D x (outW n D) = true ↔ sem_Edge G x

def sem_Gr {n : ℕ} (G : Fin n → Fin n → Prop) : Prop :=
  (∀ u v, G u v → G v u) ∧ (∀ u, ¬ G u u) ∧ (∀ v w, v ≠ w → ∃ z, G v z ∧ ¬ G w z) ∧
    (∀ u v, ∃ a, G u a ∧ a ≠ v)

def sem_step (n : ℕ) (D : Dag) (a b : ℕ) : Prop :=
  b < n + D.length ∧ n ≤ b ∧ (opA D (b - n) = a ∨ opB D (b - n) = a)

def sem_two {n : ℕ} (u z : Fin n) : Fin n → Bool := fun i => decide (i = u) || decide (i = z)

def sem_ins {n : ℕ} (v : Fin n) (x : Fin n → Bool) : Fin n → Bool := fun i => decide (i = v) || x i

def sem_ind {n : ℕ} (A : Finset (Fin n)) : Fin n → Bool := fun i => decide (i ∈ A)

lemma sem_rtg_mono {α : Type} {r p : α → α → Prop} (h : ∀ a b, r a b → p a b) {a b : α}
    (hab : Relation.ReflTransGen r a b) : Relation.ReflTransGen p a b := by
  induction hab with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.tail ih (h _ _ hbc)

section SemCore

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

lemma sem_ins_agree (v : Fin n) (x : Fin n → Bool) : ∀ k, k ≠ v → x k = sem_ins v x k := by
  intro k hk; simp [sem_ins, hk]

lemma sem_ins_self (v : Fin n) (x : Fin n → Bool) : sem_ins v x v = true := by simp [sem_ins]

lemma sem_ins_ge (v : Fin n) (x : Fin n → Bool) : ∀ i, x i = true → sem_ins v x i = true := by
  intro i hi; simp [sem_ins, hi]

lemma sem_single_le {x : Fin n → Bool} {u : Fin n} (hu : x u = true) :
    ∀ i, single u i = true → x i = true := by
  intro i hi
  simp only [single, decide_eq_true_eq] at hi
  rw [hi]; exact hu

lemma sem_val_of_supp (hS : Strict n D) {u : Fin n} {w : ℕ} (hu : u ∈ supp n D w)
    {x : Fin n → Bool} (hx : x u = true) : val D x w = true :=
  val_mono hS (single u) x (sem_single_le hx) w (mem_supp.mp hu)

lemma sem_supp_lt {v : Fin n} {w : ℕ} (hv : v ∈ supp n D w) : w < n + D.length := by
  by_contra hc
  rw [supp_ge D w (by omega)] at hv
  exact Finset.notMem_empty v hv

lemma sem_supp_and (hS : Strict n D) {j : ℕ} (hj : j < D.length) (ht : tag D j = true) :
    supp n D (n + j) = supp n D (opA D j) ∩ supp n D (opB D j) := by
  rw [supp_gate hS j hj]; simp [ht]

lemma sem_supp_or (hS : Strict n D) {j : ℕ} (hj : j < D.length) (ht : tag D j = false) :
    supp n D (n + j) = supp n D (opA D j) ∪ supp n D (opB D j) := by
  rw [supp_gate hS j hj]; simp [ht]

lemma sem_supp_and_sub (hS : Strict n D) {j : ℕ} (hj : j < D.length) (ht : tag D j = true)
    (s : Bool) : supp n D (n + j) ⊆ supp n D (src D (j, s)) := by
  rw [sem_supp_and hS hj ht]
  cases s
  · rw [sb_src_false]; exact Finset.inter_subset_left
  · rw [sb_src_true]; exact Finset.inter_subset_right

lemma sem_src_lt (hS : Strict n D) {j : ℕ} (hj : j < D.length) (s : Bool) :
    src D (j, s) < n + j := by
  obtain ⟨ha, hb, -⟩ := hS j hj
  cases s
  · rw [sb_src_false]; exact ha
  · rw [sb_src_true]; exact hb

lemma sem_src_ne (hS : Strict n D) {j : ℕ} (hj : j < D.length) (s : Bool) :
    src D (j, s) ≠ src D (j, !s) := by
  obtain ⟨-, -, hne⟩ := hS j hj
  cases s
  · simpa [src] using hne
  · simpa [src] using hne.symm

lemma sem_step_src {j : ℕ} (hj : j < D.length) (s : Bool) :
    sem_step n D (src D (j, s)) (n + j) := by
  refine ⟨by omega, by omega, ?_⟩
  rw [Nat.add_sub_cancel_left]
  cases s
  · exact Or.inl (sb_src_false j).symm
  · exact Or.inr (sb_src_true j).symm

lemma sem_step_iff {a b : ℕ} : sem_step n D a b ↔
    ∃ j s, j < D.length ∧ b = n + j ∧ src D (j, s) = a := by
  constructor
  · rintro ⟨h1, h2, h3 | h3⟩
    · exact ⟨b - n, false, by omega, by omega, by rw [sb_src_false]; exact h3⟩
    · exact ⟨b - n, true, by omega, by omega, by rw [sb_src_true]; exact h3⟩
  · rintro ⟨j, s, hj, rfl, rfl⟩
    refine ⟨by omega, by omega, ?_⟩
    rw [Nat.add_sub_cancel_left]
    cases s
    · exact Or.inl (sb_src_false j).symm
    · exact Or.inr (sb_src_true j).symm

lemma sem_step_lt (hS : Strict n D) {a b : ℕ} (h : sem_step n D a b) : a < b := by
  obtain ⟨h1, h2, h3⟩ := h
  have := hS (b - n) (by omega)
  omega

lemma sem_step_reader {a c : ℕ} (h : sem_step n D a c) : c - n ∈ readers D a := by
  unfold readers
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨by have := h.1; have := h.2.1; omega, h.2.2⟩

lemma sem_step_fanout {a c : ℕ} (h : sem_step n D a c) : 1 ≤ fanout D a :=
  Finset.card_pos.mpr ⟨_, sem_step_reader h⟩

lemma sem_step_unique {a c c' : ℕ} (h1 : sem_step n D a c) (h2 : sem_step n D a c')
    (hf : fanout D a = 1) : c = c' := by
  have m1 := sem_step_reader h1
  have m2 := sem_step_reader h2
  obtain ⟨r, hr⟩ := Finset.card_eq_one.mp (show (readers D a).card = 1 from hf)
  rw [hr, Finset.mem_singleton] at m1 m2
  have := h1.2.1
  have := h2.2.1
  omega

lemma sem_changed_path (hS : Strict n D) (x y : Fin n → Bool) (v : Fin n)
    (hxy : ∀ k, k ≠ v → x k = y k) (w : ℕ) (hw : val D x w ≠ val D y w) :
    Relation.ReflTransGen (fun a b => sem_step n D a b ∧ val D x b ≠ val D y b) v.val w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · rw [val_input D x w hn, val_input D y w hn] at hw
      have hwv : (⟨w, hn⟩ : Fin n) = v := by
        by_contra hc; exact hw (hxy _ hc)
      rw [← hwv]
    · by_cases hlt : w < n + D.length
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < D.length := by omega
        obtain ⟨ha, hb, -⟩ := hS j hj
        have hg := hw
        rw [val_gate hS x j hj, val_gate hS y j hj] at hg
        by_cases h1 : val D x (opA D j) = val D y (opA D j)
        · have h2 : val D x (opB D j) ≠ val D y (opB D j) := by
            intro h2; apply hg; rw [h1, h2]
          exact Relation.ReflTransGen.tail (ih _ hb h2)
            ⟨⟨hlt, by omega, Or.inr (by rw [Nat.add_sub_cancel_left])⟩, hw⟩
        · exact Relation.ReflTransGen.tail (ih _ ha h1)
            ⟨⟨hlt, by omega, Or.inl (by rw [Nat.add_sub_cancel_left])⟩, hw⟩
      · exfalso; apply hw; rw [val_ge D x w (by omega), val_ge D y w (by omega)]

def sem_Dom (n : ℕ) (D : Dag) (b v : ℕ) : Prop :=
  b = v ∨ ¬ Relation.ReflTransGen (fun a c => sem_step n D a c ∧ c ≠ b) v (outW n D)

lemma sem_dom_eq (hS : Strict n D) (x y : Fin n → Bool) (v : Fin n)
    (hxy : ∀ k, k ≠ v → x k = y k) (b : ℕ) (hdom : sem_Dom n D b v.val)
    (hb : val D x b = val D y b) : val D x (outW n D) = val D y (outW n D) := by
  by_contra hne
  rcases hdom with rfl | hdom
  · rw [val_input D x _ v.isLt, val_input D y _ v.isLt] at hb
    have hxy2 : x = y := by
      funext k
      by_cases hk : k = v
      · rw [hk]; exact hb
      · exact hxy k hk
    exact hne (by rw [hxy2])
  · exact hdom (sem_rtg_mono
      (fun a c h => ⟨h.1, fun hc => h.2 (by rw [hc]; exact hb)⟩)
      (sem_changed_path hS x y v hxy _ hne))

def sem_Chain (n : ℕ) (D : Dag) (a b : ℕ) : Prop :=
  Relation.ReflTransGen (fun a c => sem_step n D a c ∧ fanout D a = 1) a b

lemma sem_chain_dom (hS : Strict n D) {v b : ℕ} (h : sem_Chain n D v b) :
    sem_Dom n D b v := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact Or.inl rfl
  | @head a c hstep _ ih =>
    by_cases hba : b = a
    · exact Or.inl hba
    · right
      intro hp
      rcases Relation.ReflTransGen.cases_head hp with heq | ⟨c', hs, hrest⟩
      · have h0 := fanout_eq_zero_of_ge hS a (by rw [heq]; unfold outW; omega)
        have h1 := hstep.2
        omega
      · have hcc : c = c' := sem_step_unique hstep.1 hs.1 hstep.2
        subst hcc
        rcases ih with rfl | ih
        · exact hs.2 rfl
        · exact ih hrest

lemma sem_carrier_chain (hS : Strict n D) (v : Fin n) : ∀ w, v ∈ supp n D w →
    (∀ u, u < w → v ∈ supp n D u → fanout D u ≤ 1) → sem_Chain n D v.val w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv hlow
    by_cases hn : w < n
    · have hs : supp n D w = {⟨w, hn⟩} := supp_input D ⟨w, hn⟩
      rw [hs, Finset.mem_singleton] at hv
      rw [hv]; exact Relation.ReflTransGen.refl
    · have hlt := sem_supp_lt hv
      obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < D.length := by omega
      have key : ∀ s : Bool, v ∈ supp n D (src D (j, s)) → sem_Chain n D v.val (n + j) := by
        intro s hva
        have hstep : sem_step n D (src D (j, s)) (n + j) := sem_step_src hj s
        have hlt' := sem_src_lt hS hj s
        have h1 := sem_step_fanout hstep
        have h2 := hlow _ hlt' hva
        exact Relation.ReflTransGen.tail (ih _ hlt' hva (fun u hu => hlow u (by omega)))
          ⟨hstep, by omega⟩
      rw [supp_gate hS j hj] at hv
      split_ifs at hv with ht
      · exact key false (by rw [sb_src_false]; exact (Finset.mem_inter.mp hv).1)
      · rcases Finset.mem_union.mp hv with h1 | h1
        · exact key false (by rw [sb_src_false]; exact h1)
        · exact key true (by rw [sb_src_true]; exact h1)

lemma sem_single_no_edge (hG : sem_Gr G) (v : Fin n) : ¬ sem_Edge G (single v) := by
  rintro ⟨a, c, hac, ha, hc⟩
  simp only [single, decide_eq_true_eq] at ha hc
  rw [ha, hc] at hac
  exact hG.2.1 _ hac

lemma sem_two_edge {u v : Fin n} (huv : G u v) : sem_Edge G (sem_two u v) :=
  ⟨u, v, huv, by simp [sem_two], by simp [sem_two]⟩

lemma sem_supp_out (hG : sem_Gr G) (hC : sem_Comp n G D) : supp n D (outW n D) = ∅ :=
  Finset.eq_empty_iff_forall_notMem.2
    (fun v hv => sem_single_no_edge hG v ((hC _).1 (mem_supp.1 hv)))

lemma sem_dom_pure (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) (v : Fin n)
    (b : ℕ) (hdom : sem_Dom n D b v.val) : supp n D b ⊆ {v} := by
  intro u hu
  rw [Finset.mem_singleton]
  by_contra huv
  obtain ⟨hsym, hirr, hsep, -⟩ := hG
  obtain ⟨z, hvz, huz⟩ := hsep v u (Ne.symm huv)
  have hxb : val D (sem_two u z) b = true := sem_val_of_supp hS hu (by simp [sem_two])
  have hyb : val D (sem_ins v (sem_two u z)) b = true :=
    sem_val_of_supp hS hu (by simp [sem_ins, sem_two])
  have hout := sem_dom_eq hS _ _ v (sem_ins_agree v (sem_two u z)) b hdom (by rw [hxb, hyb])
  have h1 : ¬ sem_Edge G (sem_two u z) := by
    rintro ⟨a, c, hac, ha, hc⟩
    simp only [sem_two, Bool.or_eq_true, decide_eq_true_eq] at ha hc
    rcases ha with ha | ha <;> rcases hc with hc | hc <;> rw [ha, hc] at hac
    · exact hirr _ hac
    · exact huz hac
    · exact huz (hsym _ _ hac)
    · exact hirr _ hac
  have h2 : sem_Edge G (sem_ins v (sem_two u z)) :=
    ⟨v, z, hvz, sem_ins_self v _, by simp [sem_ins, sem_two]⟩
  have h3 := (hC _).mpr h2
  rw [← hout] at h3
  exact h1 ((hC _).mp h3)

lemma sem_first_branch (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) (v : Fin n)
    (hv : v ∈ eligSet n D) :
    ∃ b, 2 ≤ fanout D b ∧ supp n D b = {v} ∧ sem_Chain n D v.val b := by
  classical
  have hex : ∃ w, 2 ≤ fanout D w ∧ v ∈ supp n D w := mem_eligSet.mp hv
  obtain ⟨h1, h2⟩ := Nat.find_spec hex
  have hch : sem_Chain n D v.val (Nat.find hex) :=
    sem_carrier_chain hS v _ h2 (fun u hu huv => by
      have := Nat.find_min hex hu
      by_contra hc
      exact this ⟨by omega, huv⟩)
  exact ⟨Nat.find hex, h1, Finset.Subset.antisymm
    (sem_dom_pure hG hS hC v _ (sem_chain_dom hS hch)) (Finset.singleton_subset_iff.mpr h2), hch⟩

def sem_FirstBranch (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Prop :=
  ∀ v ∈ eligSet n D, 2 ≤ fanout D (b v) ∧ supp n D (b v) = {v} ∧ sem_Chain n D v.val (b v)

lemma sem_exists_firstBranch (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) :
    ∃ b : Fin n → ℕ, sem_FirstBranch n D b := by
  classical
  have h : ∀ v : Fin n, ∃ b, v ∈ eligSet n D →
      2 ≤ fanout D b ∧ supp n D b = {v} ∧ sem_Chain n D v.val b := by
    intro v
    by_cases hv : v ∈ eligSet n D
    · obtain ⟨b, hb⟩ := sem_first_branch hG hS hC v hv
      exact ⟨b, fun _ => hb⟩
    · exact ⟨0, fun h => absurd h hv⟩
  choose b hb using h
  exact ⟨b, fun v hv => hb v hv⟩

lemma sem_firstBranch_pure {b : Fin n → ℕ} (hb : sem_FirstBranch n D b) : PureBranch n D b :=
  fun v hv => ⟨(hb v hv).1, (hb v hv).2.1⟩

lemma sem_exists_pureBranch (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) :
    ∃ b : Fin n → ℕ, PureBranch n D b := by
  obtain ⟨b, hb⟩ := sem_exists_firstBranch hG hS hC
  exact ⟨b, sem_firstBranch_pure hb⟩

lemma sem_mem_inelig {v : Fin n} : v ∈ ineligSet n D ↔ v ∉ eligSet n D := by
  simp [ineligSet]

lemma sem_inelig_chain (hS : Strict n D) {v : Fin n} (hv : v ∈ ineligSet n D) {w : ℕ}
    (hw : v ∈ supp n D w) : sem_Chain n D v.val w :=
  sem_carrier_chain hS v w hw (fun u _ hu => mem_ineligSet.mp hv u hu)

lemma sem_inelig_pure (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) {v : Fin n}
    (hv : v ∈ ineligSet n D) {w : ℕ} (hw : v ∈ supp n D w) : supp n D w = {v} :=
  Finset.Subset.antisymm (sem_dom_pure hG hS hC v w (sem_chain_dom hS (sem_inelig_chain hS hv hw)))
    (Finset.singleton_subset_iff.mpr hw)

lemma sem_mem_carrier1 {v : Fin n} {w : ℕ} : w ∈ carrierT n D {v} ↔ v ∈ supp n D w := by
  simp only [carrierT, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨-, u, hu⟩
    rw [Finset.mem_inter, Finset.mem_singleton] at hu
    exact hu.2 ▸ hu.1
  · intro h
    exact ⟨sem_supp_lt h, v, Finset.mem_inter.mpr ⟨h, Finset.mem_singleton_self v⟩⟩

lemma sem_mem_exit1 {v : Fin n} {e : ℕ × Bool} : e ∈ exitArcs n D (carrierT n D {v}) ↔
    e.1 < D.length ∧ v ∈ supp n D (src D e) ∧ v ∉ supp n D (n + e.1) := by
  simp only [exitArcs, arcs, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
    Finset.mem_univ, and_true, sem_mem_carrier1]

lemma sem_inelig_surplus {v : Fin n} (hv : v ∈ ineligSet n D) :
    surplusOn D (carrierT n D {v}) = 0 := by
  unfold surplusOn
  refine Finset.sum_eq_zero (fun w hw => ?_)
  have := mem_ineligSet.mp hv w (sem_mem_carrier1.mp hw)
  omega

lemma sem_joint_meeting (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    {u v : Fin n} (huv : G u v) :
    ∃ j, j < D.length ∧ tag D j = true ∧ val D (sem_two u v) (n + j) = true ∧
      u ∉ supp n D (n + j) ∧ v ∉ supp n D (n + j) ∧
      ∃ s : Bool, u ∈ supp n D (src D (j, s)) ∧ v ∉ supp n D (src D (j, s)) ∧
        v ∈ supp n D (src D (j, !s)) ∧ u ∉ supp n D (src D (j, !s)) := by
  classical
  have hex : ∃ w, val D (sem_two u v) w = true ∧ u ∉ supp n D w ∧ v ∉ supp n D w :=
    ⟨outW n D, (hC _).2 (sem_two_edge huv), by rw [sem_supp_out hG hC]; simp,
      by rw [sem_supp_out hG hC]; simp⟩
  obtain ⟨hw1, hw2, hw3⟩ := Nat.find_spec hex
  have hmin : ∀ a, a < Nat.find hex → val D (sem_two u v) a = true →
      u ∈ supp n D a ∨ v ∈ supp n D a := by
    intro a ha hva
    by_contra hc
    rw [not_or] at hc
    exact Nat.find_min hex ha ⟨hva, hc.1, hc.2⟩
  generalize Nat.find hex = w at hw1 hw2 hw3 hmin
  have hlt : w < n + D.length := by
    by_contra hc
    rw [val_ge D _ w (by omega)] at hw1
    exact Bool.false_ne_true hw1
  have hn : n ≤ w := by
    by_contra hc
    have hc' : w < n := by omega
    rw [val_input D _ w hc'] at hw1
    have hs : supp n D w = {⟨w, hc'⟩} := supp_input D ⟨w, hc'⟩
    rw [hs, Finset.mem_singleton] at hw2 hw3
    simp only [sem_two, Bool.or_eq_true, decide_eq_true_eq] at hw1
    rcases hw1 with h | h
    · exact hw2 h.symm
    · exact hw3 h.symm
  obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
  have hj : j < D.length := by omega
  obtain ⟨ha, hb, -⟩ := hS j hj
  have hval := hw1
  rw [val_gate hS _ j hj] at hw1
  rw [supp_gate hS j hj] at hw2 hw3
  cases ht : tag D j
  · exfalso
    rw [ht] at hw1 hw2 hw3
    simp only [gop_false, Bool.or_eq_true] at hw1
    simp only [Bool.false_eq_true, ite_false, Finset.mem_union, not_or] at hw2 hw3
    rcases hw1 with h | h
    · rcases hmin _ ha h with h' | h'
      · exact hw2.1 h'
      · exact hw3.1 h'
    · rcases hmin _ hb h with h' | h'
      · exact hw2.2 h'
      · exact hw3.2 h'
  · rw [ht] at hw1 hw2 hw3
    simp only [gop_true, Bool.and_eq_true] at hw1
    simp only [ite_true, Finset.mem_inter, not_and] at hw2 hw3
    have hsupp : u ∉ supp n D (n + j) ∧ v ∉ supp n D (n + j) := by
      rw [sem_supp_and hS hj ht]
      simp only [Finset.mem_inter, not_and]
      exact ⟨hw2, hw3⟩
    refine ⟨j, hj, ht, hval, hsupp.1, hsupp.2, ?_⟩
    rcases hmin _ ha hw1.1 with hA | hA
    · have hB : u ∉ supp n D (opB D j) := hw2 hA
      have hBv : v ∈ supp n D (opB D j) := (hmin _ hb hw1.2).resolve_left hB
      exact ⟨false, by simpa [src] using hA, by simpa [src] using fun h => hw3 h hBv,
        by simpa [src] using hBv, by simpa [src] using hB⟩
    · have hB : v ∉ supp n D (opB D j) := hw3 hA
      have hBu : u ∈ supp n D (opB D j) := (hmin _ hb hw1.2).resolve_right hB
      exact ⟨true, by simpa [src] using hBu, by simpa [src] using hB,
        by simpa [src] using hA, by simpa [src] using fun h => hw2 h hBu⟩

lemma sem_inelig_consumer (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    {v : Fin n} (hv : v ∈ ineligSet n D) :
    ∃ e : ℕ × Bool, e.1 < D.length ∧ tag D e.1 = true ∧ supp n D (src D e) = {v} ∧
      supp n D (n + e.1) = ∅ ∧ (∀ a, G v a → a ∈ supp n D (src D (e.1, !e.2))) ∧
      exitArcs n D (carrierT n D {v}) = {e} ∧ merges n D (carrierT n D {v}) = ∅ := by
  have hS := h.1
  have hfl := carrier_flow_union h {v} (by rw [sem_supp_out hG hC]; simp)
  rw [sem_inelig_surplus hv, Finset.card_singleton] at hfl
  have hmeet : ∀ a, G v a → ∃ j s, j < D.length ∧ tag D j = true ∧
      (j, s) ∈ exitArcs n D (carrierT n D {v}) ∧ a ∈ supp n D (src D (j, !s)) := by
    intro a hva
    obtain ⟨j, hj, ht, -, hju, -, s, h1, -, h3, -⟩ := sem_joint_meeting hG hS hC hva
    exact ⟨j, s, hj, ht, sem_mem_exit1.mpr ⟨hj, h1, hju⟩, h3⟩
  obtain ⟨a0, ha0, -⟩ := hG.2.2.2 v v
  obtain ⟨j0, s0, hj0, ht0, hm0, -⟩ := hmeet a0 ha0
  have hcard : (exitArcs n D (carrierT n D {v})).card = 1 := by
    have := Finset.card_pos.mpr ⟨_, hm0⟩
    omega
  have hmer : merges n D (carrierT n D {v}) = ∅ := Finset.card_eq_zero.mp (by omega)
  obtain ⟨e, he⟩ := Finset.card_eq_one.mp hcard
  rw [he, Finset.mem_singleton] at hm0
  subst hm0
  have hsrc : supp n D (src D (j0, s0)) = {v} :=
    sem_inelig_pure hG hS hC hv
      (sem_mem_exit1.mp (by rw [he]; exact Finset.mem_singleton_self _)).2.1
  have hnot : v ∉ supp n D (n + j0) :=
    (sem_mem_exit1.mp (by rw [he]; exact Finset.mem_singleton_self _)).2.2
  refine ⟨(j0, s0), hj0, ht0, hsrc, ?_, ?_, he, hmer⟩
  · refine Finset.eq_empty_of_forall_notMem (fun x hx => ?_)
    have hx2 := sem_supp_and_sub hS hj0 ht0 s0 hx
    rw [hsrc, Finset.mem_singleton] at hx2
    exact hnot (hx2 ▸ hx)
  · intro a hva
    obtain ⟨j, s, -, -, hm, ha⟩ := hmeet a hva
    rw [he, Finset.mem_singleton] at hm
    rw [Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    exact ha

lemma sem_elig_cover (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    {u v : Fin n} (huv : G u v) : u ∈ eligSet n D ∨ v ∈ eligSet n D := by
  by_contra hc
  rw [not_or] at hc
  obtain ⟨eu, -, -, -, -, hnu, hxu, -⟩ := sem_inelig_consumer hG h hC (sem_mem_inelig.mpr hc.1)
  obtain ⟨ev, -, -, hsv, -, -, hxv, -⟩ := sem_inelig_consumer hG h hC (sem_mem_inelig.mpr hc.2)
  obtain ⟨j, hj, -, -, hju, hjv, s, h1, -, h3, -⟩ := sem_joint_meeting hG h.1 hC huv
  have m1 : (j, s) ∈ exitArcs n D (carrierT n D {u}) := sem_mem_exit1.mpr ⟨hj, h1, hju⟩
  have m2 : (j, !s) ∈ exitArcs n D (carrierT n D {v}) := sem_mem_exit1.mpr ⟨hj, h3, hjv⟩
  rw [hxu, Finset.mem_singleton] at m1
  rw [hxv, Finset.mem_singleton] at m2
  subst m1
  subst m2
  obtain ⟨a, hua, hav⟩ := hG.2.2.2 u v
  have h5 : a ∈ supp n D (src D (j, !s)) := hnu a hua
  rw [hsv, Finset.mem_singleton] at h5
  exact hav h5

lemma sem_ind_no_edge {A : Finset (Fin n)} (hA : ∀ a ∈ A, ∀ b ∈ A, ¬ G a b) :
    ¬ sem_Edge G (sem_ind A) := by
  rintro ⟨a, c, hac, ha, hc⟩
  simp only [sem_ind, decide_eq_true_eq] at ha hc
  exact hA a ha c hc hac

lemma sem_exposure (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    (A : Finset (Fin n)) (hA : ∀ a ∈ A, ∀ b ∈ A, ¬ G a b) (x : Fin n)
    (hnb : ∃ a ∈ A, G x a) :
    ∃ j s, j < D.length ∧ tag D j = true ∧ x ∈ supp n D (src D (j, s)) ∧
      x ∉ supp n D (n + j) ∧ Disjoint (supp n D (src D (j, s))) A := by
  by_contra hcon
  have hmask : ∀ j s, j < D.length → tag D j = true → x ∈ supp n D (src D (j, s)) →
      x ∉ supp n D (n + j) → val D (sem_ind A) (src D (j, s)) = true ∧
        val D (sem_ins x (sem_ind A)) (src D (j, s)) = true := by
    intro j s hj ht h1 h2
    have hnd : ¬ Disjoint (supp n D (src D (j, s))) A :=
      fun hd => hcon ⟨j, s, hj, ht, h1, h2, hd⟩
    rw [Finset.not_disjoint_iff] at hnd
    obtain ⟨a, ha1, ha2⟩ := hnd
    exact ⟨sem_val_of_supp hS ha1 (by simp [sem_ind, ha2]),
      sem_val_of_supp hS ha1 (by simp [sem_ins, sem_ind, ha2])⟩
  have key : ∀ w, x ∉ supp n D w → val D (sem_ind A) w = val D (sem_ins x (sem_ind A)) w := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw
      by_cases hn : w < n
      · rw [val_input D _ w hn, val_input D _ w hn]
        have hs : supp n D w = {⟨w, hn⟩} := supp_input D ⟨w, hn⟩
        rw [hs, Finset.mem_singleton] at hw
        exact sem_ins_agree x _ _ (fun hc => hw hc.symm)
      · by_cases hlt : w < n + D.length
        · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
          have hj : j < D.length := by omega
          obtain ⟨ha, hb, -⟩ := hS j hj
          rw [val_gate hS _ j hj, val_gate hS _ j hj]
          cases ht : tag D j
          · rw [sem_supp_or hS hj ht, Finset.mem_union, not_or] at hw
            rw [ih _ ha hw.1, ih _ hb hw.2]
          · have hw2 := hw
            rw [sem_supp_and hS hj ht, Finset.mem_inter, not_and] at hw2
            by_cases hxa : x ∈ supp n D (opA D j)
            · have h1 := hmask j false hj ht (by rw [sb_src_false]; exact hxa) hw
              rw [sb_src_false] at h1
              rw [ih _ hb (hw2 hxa), h1.1, h1.2]
            · by_cases hxb : x ∈ supp n D (opB D j)
              · have h1 := hmask j true hj ht (by rw [sb_src_true]; exact hxb) hw
                rw [sb_src_true] at h1
                rw [ih _ ha hxa, h1.1, h1.2]
              · rw [ih _ ha hxa, ih _ hb hxb]
        · rw [val_ge D _ w (by omega), val_ge D _ w (by omega)]
  have hout := key (outW n D) (by rw [sem_supp_out hG hC]; exact Finset.notMem_empty x)
  obtain ⟨a, ha, hxa⟩ := hnb
  have h2 : sem_Edge G (sem_ins x (sem_ind A)) :=
    ⟨x, a, hxa, sem_ins_self x _, by simp [sem_ins, sem_ind, ha]⟩
  have h3 := (hC _).mpr h2
  rw [← hout] at h3
  exact sem_ind_no_edge hA ((hC _).mp h3)

lemma sem_first_mask (hS : Strict n D) (T M : Finset (Fin n)) (hM : 2 ≤ M.card) (w : ℕ)
    (hw : supp n D w ∩ T = M) :
    ∃ j, j < D.length ∧ n + j ≤ w ∧ supp n D (n + j) ∩ T = M ∧
      j ∈ merges n D (carrierT n D T) ∧ (∀ u, u < n + j → supp n D u ∩ T ≠ M) ∧
      ((tag D j = true ∧ M ⊂ supp n D (opA D j) ∩ T ∧ M ⊂ supp n D (opB D j) ∩ T) ∨
        (tag D j = false ∧ supp n D (opA D j) ∩ T ⊂ M ∧ supp n D (opB D j) ∩ T ⊂ M ∧
          (supp n D (opA D j) ∩ T) ∪ (supp n D (opB D j) ∩ T) = M ∧
          (supp n D (opA D j) ∩ T).Nonempty ∧ (supp n D (opB D j) ∩ T).Nonempty)) := by
  classical
  have hex : ∃ u, supp n D u ∩ T = M := ⟨w, hw⟩
  have hle : Nat.find hex ≤ w := Nat.find_min' hex hw
  have hmin : ∀ u, u < Nat.find hex → supp n D u ∩ T ≠ M := fun u hu => Nat.find_min hex hu
  have hspec := Nat.find_spec hex
  generalize Nat.find hex = f at hle hmin hspec
  have hMne : M.Nonempty := Finset.card_pos.mp (by omega)
  have hmem : ∀ {u : ℕ}, (supp n D u ∩ T).Nonempty → u ∈ carrierT n D T := by
    intro u hu
    obtain ⟨v, hv⟩ := hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
      (sem_supp_lt (Finset.mem_inter.mp hv).1), v, hv⟩
  have hflt : f < n + D.length := by
    obtain ⟨v, hv⟩ := hMne
    rw [← hspec] at hv
    exact sem_supp_lt (Finset.mem_inter.mp hv).1
  have hfn : n ≤ f := by
    by_contra hc
    have hc' : f < n := by omega
    have hs : supp n D f = {⟨f, hc'⟩} := supp_input D ⟨f, hc'⟩
    have h1 : M.card ≤ 1 := by
      rw [← hspec, hs]
      exact (Finset.card_le_card Finset.inter_subset_left).trans (by simp)
    omega
  obtain ⟨j, rfl⟩ : ∃ j, f = n + j := ⟨f - n, by omega⟩
  have hj : j < D.length := by omega
  obtain ⟨ha, hb, -⟩ := hS j hj
  have hna := hmin _ ha
  have hnb := hmin _ hb
  refine ⟨j, hj, hle, hspec, ?_, hmin, ?_⟩
  · have hAB : (supp n D (opA D j) ∩ T).Nonempty ∧ (supp n D (opB D j) ∩ T).Nonempty := by
      cases ht : tag D j
      · rw [sem_supp_or hS hj ht, Finset.union_inter_distrib_right] at hspec
        constructor
        · rw [Finset.nonempty_iff_ne_empty]
          intro he
          rw [he, Finset.empty_union] at hspec
          exact hnb hspec
        · rw [Finset.nonempty_iff_ne_empty]
          intro he
          rw [he, Finset.union_empty] at hspec
          exact hna hspec
      · rw [sem_supp_and hS hj ht] at hspec
        obtain ⟨v, hv⟩ := hMne
        rw [← hspec] at hv
        simp only [Finset.mem_inter] at hv
        exact ⟨⟨v, Finset.mem_inter.mpr ⟨hv.1.1, hv.2⟩⟩, ⟨v, Finset.mem_inter.mpr ⟨hv.1.2, hv.2⟩⟩⟩
    rw [merges, Finset.mem_filter, Finset.mem_range]
    exact ⟨hj, hmem (by rw [hspec]; exact hMne), hmem hAB.1, hmem hAB.2⟩
  · cases ht : tag D j
    · right
      rw [sem_supp_or hS hj ht, Finset.union_inter_distrib_right] at hspec
      have hsa : supp n D (opA D j) ∩ T ⊆ M := by rw [← hspec]; exact Finset.subset_union_left
      have hsb : supp n D (opB D j) ∩ T ⊆ M := by rw [← hspec]; exact Finset.subset_union_right
      refine ⟨rfl, Finset.ssubset_iff_subset_ne.mpr ⟨hsa, hna⟩,
        Finset.ssubset_iff_subset_ne.mpr ⟨hsb, hnb⟩, hspec, ?_, ?_⟩
      · rw [Finset.nonempty_iff_ne_empty]
        intro he
        rw [he, Finset.empty_union] at hspec
        exact hnb hspec
      · rw [Finset.nonempty_iff_ne_empty]
        intro he
        rw [he, Finset.union_empty] at hspec
        exact hna hspec
    · left
      rw [sem_supp_and hS hj ht] at hspec
      have hsa : M ⊆ supp n D (opA D j) ∩ T := by
        rw [← hspec]
        intro v hv
        simp only [Finset.mem_inter] at hv ⊢
        exact ⟨hv.1.1, hv.2⟩
      have hsb : M ⊆ supp n D (opB D j) ∩ T := by
        rw [← hspec]
        intro v hv
        simp only [Finset.mem_inter] at hv ⊢
        exact ⟨hv.1.2, hv.2⟩
      exact ⟨rfl, Finset.ssubset_iff_subset_ne.mpr ⟨hsa, Ne.symm hna⟩,
        Finset.ssubset_iff_subset_ne.mpr ⟨hsb, Ne.symm hnb⟩⟩

end SemCore


variable {n : ℕ} {D : Dag}

lemma carrier_flow_lower (h : StrictLive n D) (K : Finset ℕ) (hK : K ⊆ inner n D)
    : (sources n K).card + surplusOn D K ≤
      (exitArcs n D K).card + (merges n D K).card := by
  obtain ⟨hS, hL, -⟩ := h
  have hKlt : ∀ w ∈ K, w + 1 < n + D.length := fun w hw => sb_mem_inner.mp (hK hw)
  have h1 : surplusOn D K + K.card = ((arcs D).filter (fun e => src D e ∈ K)).card := by
    rw [← sb_sum_fanout_eq hS, sb_surplus_add_card (fun w hw => hL w (hKlt w hw))]
  have h2 := Finset.card_filter_add_card_filter_not
    (s := (arcs D).filter (fun e => src D e ∈ K)) (fun e : ℕ × Bool => n + e.1 ∈ K)
  rw [Finset.filter_filter, Finset.filter_filter] at h2
  have h3 : ((arcs D).filter (fun e => src D e ∈ K ∧ n + e.1 ∈ K)).card ≤
      ((Finset.range D.length).filter (fun j => n + j ∈ K)).card + (merges n D K).card := by
    rw [sb_card_arcs_filter, merges, Finset.card_filter, Finset.card_filter,
      ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun j hj => ?_)
    rw [sb_src_false, sb_src_true]
    by_cases hj2 : n + j ∈ K <;> by_cases ha : opA D j ∈ K <;> by_cases hb : opB D j ∈ K <;>
      simp_all
  have h4 : K.card = (sources n K).card +
      ((Finset.range D.length).filter (fun j => n + j ∈ K)).card := by
    rw [← Finset.card_filter_add_card_filter_not (s := K) (fun w => w < n), sources]
    congr 1
    have himg : K.filter (fun w => ¬ w < n) =
        ((Finset.range D.length).filter (fun j => n + j ∈ K)).image (fun j => n + j) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range]
      constructor
      · rintro ⟨hw, hn⟩
        have := hKlt w hw
        exact ⟨w - n, ⟨by omega, by rwa [Nat.add_sub_cancel' (by omega)]⟩, by omega⟩
      · rintro ⟨j, ⟨-, hj⟩, rfl⟩
        exact ⟨hj, by omega⟩
    rw [himg, Finset.card_image_of_injective _ (add_right_injective n)]
  unfold exitArcs
  omega

def copyBoundary (n : ℕ) (D : Dag) (K : Finset ℕ) : Finset ℕ :=
  (Finset.range D.length).filter (fun j =>
    (opA D j ∈ K ∧ opB D j ∈ K) ∨
    ((opA D j ∈ K ∨ opB D j ∈ K) ∧ n + j ∉ K))

lemma source_surplus_le_copyBoundary (h : StrictLive n D) (K : Finset ℕ)
    (hK : K ⊆ inner n D)
    (hclosed : ∀ j < D.length, opA D j ∈ K → opB D j ∈ K → n + j ∈ K) :
    (sources n K).card + surplusOn D K ≤ (copyBoundary n D K).card := by
  have hp (a : ℕ × Bool) (ha : a ∈ exitArcs n D K) :
      a.1 < D.length ∧ src D a ∈ K ∧ n + a.1 ∉ K := by
    obtain ⟨ha, hs, ho⟩ := Finset.mem_filter.mp ha
    exact ⟨Finset.mem_range.mp (Finset.mem_product.mp ha).1, hs, ho⟩
  have hinj : Set.InjOn Prod.fst (↑(exitArcs n D K) : Set (ℕ × Bool)) := by
    rintro ⟨j,s⟩ ha ⟨k,t⟩ hb he
    change j = k at he
    subst k
    obtain ⟨hj, hsa, hoa⟩ := hp _ ha
    obtain ⟨_, hsb, _⟩ := hp _ hb
    cases s <;> cases t
    · rfl
    · exact (hoa (hclosed j hj (by simpa [src] using hsa) (by simpa [src] using hsb))).elim
    · exact (hoa (hclosed j hj (by simpa [src] using hsb) (by simpa [src] using hsa))).elim
    · rfl
  have hdis : Disjoint ((exitArcs n D K).image Prod.fst) (merges n D K) := by
    rw [Finset.disjoint_left]
    intro j he hm
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    exact (hp a ha).2.2 (Finset.mem_filter.mp hm).2.1
  have hsub : (exitArcs n D K).image Prod.fst ∪ merges n D K ⊆ copyBoundary n D K := by
    intro j hj
    rw [copyBoundary, Finset.mem_filter, Finset.mem_range]
    rcases Finset.mem_union.mp hj with he | hm
    · obtain ⟨⟨k,s⟩, hs, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨hk, ha, ho⟩ := hp _ hs
      refine ⟨hk, Or.inr ⟨?_, ho⟩⟩
      cases s
      · exact Or.inl (by simpa [src] using ha)
      · exact Or.inr (by simpa [src] using ha)
    · obtain ⟨hj, _, ha, hb⟩ := Finset.mem_filter.mp hm
      exact ⟨Finset.mem_range.mp hj, Or.inl ⟨ha, hb⟩⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis, Finset.card_image_of_injOn hinj] at hc
  have hf := carrier_flow_lower h K hK
  omega

lemma source_le_copyBoundary (h : StrictLive n D) (K : Finset ℕ)
    (hK : K ⊆ inner n D)
    (hclosed : ∀ j < D.length, opA D j ∈ K → opB D j ∈ K → n + j ∈ K) :
    (sources n K).card ≤ (copyBoundary n D K).card := by
  have hh := source_surplus_le_copyBoundary h K hK hclosed
  omega

noncomputable def zeroWires {n : ℕ} {α : Type} (D : Dag)
    (rows : α → Fin n → Bool) : Finset ℕ := by
  classical
  exact (Finset.range (n + D.length)).filter (fun w => ∀ r, val D (rows r) w = false)

noncomputable def rowCopies {n : ℕ} {α : Type} (D : Dag)
    (rows : α → Fin n → Bool) : Finset ℕ := by
  classical
  exact (Finset.range D.length).filter (fun j =>
    ∃ w < n + j, ∀ r, val D (rows r) (n + j) = val D (rows r) w)

lemma mem_zeroWires {n : ℕ} {α : Type} {D : Dag} {rows : α → Fin n → Bool} {w : ℕ} :
    w ∈ zeroWires D rows ↔ w < n + D.length ∧ ∀ r, val D (rows r) w = false := by
  classical
  simp [zeroWires]

lemma true_support_on_rows {n : ℕ} {α : Type} {D : Dag}
    (hS : Strict n D) (rows : α → Fin n → Bool) {v : Fin n}
    (hv : ∀ r, rows r v = true) {w : ℕ} (hw : v ∈ supp n D w) :
    ∀ r, val D (rows r) w = true := by
  intro r
  apply val_mono hS (single v) (rows r) _ w (mem_supp.mp hw)
  intro u hu
  have huv : u = v := by simpa [single] using hu
  simpa only [huv] using hv r

lemma copies_from_zero_sources_and_true_ands {n : ℕ} {α : Type} {D : Dag}
    (h : StrictLive n D) (rows : α → Fin n → Bool)
    (hout : ∃ r, val D (rows r) (outW n D) = true)
    (I : Finset (Fin n)) (hI : ∀ i ∈ I, ∀ r, rows r i = false)
    (A : Finset ℕ) (hA : ∀ j ∈ A, j < D.length ∧ tag D j = true ∧
      ((∀ r, val D (rows r) (opA D j) = true) ∨
       (∀ r, val D (rows r) (opB D j) = true))) :
    I.card + A.card ≤ (rowCopies D rows).card := by
  classical
  let K := zeroWires D rows
  obtain ⟨r0, hr0⟩ := hout
  have hK : K ⊆ inner n D := by
    intro w hw
    obtain ⟨hw, hz⟩ := mem_zeroWires.mp hw
    apply sb_mem_inner.mpr
    by_contra hnot
    have heq : w = outW n D := by unfold outW; omega
    have hh := hz r0
    rw [heq, hr0] at hh
    contradiction
  have hclosed : ∀ j < D.length, opA D j ∈ K → opB D j ∈ K → n + j ∈ K := by
    intro j hj ha hb
    refine mem_zeroWires.mpr ⟨by omega, ?_⟩
    intro r
    rw [val_gate h.1 _ j hj, (mem_zeroWires.mp ha).2 r, (mem_zeroWires.mp hb).2 r]
    cases tag D j <;> rfl
  have hsource : I.card ≤ (sources n K).card := by
    have hs : I.image Fin.val ⊆ sources n K := by
      intro w hw
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
      refine Finset.mem_filter.mpr ⟨mem_zeroWires.mpr ⟨by omega, ?_⟩, i.isLt⟩
      intro r
      rw [val_input D _ i.val i.isLt]
      exact hI i hi r
    have hc := Finset.card_le_card hs
    simpa only [Finset.card_image_of_injective _ Fin.val_injective] using hc
  have hboundary := source_le_copyBoundary h K hK hclosed
  have hbc : copyBoundary n D K ⊆ rowCopies D rows := by
    intro j hj
    obtain ⟨hj, hcase⟩ := Finset.mem_filter.mp hj
    have hjlt := Finset.mem_range.mp hj
    obtain ⟨ha, hb, _⟩ := h.1 j hjlt
    refine Finset.mem_filter.mpr ⟨hj, ?_⟩
    rcases hcase with ⟨hka, hkb⟩ | ⟨hk, hko⟩
    · refine ⟨opA D j, ha, ?_⟩
      intro r
      rw [val_gate h.1 _ j hjlt, (mem_zeroWires.mp hka).2 r, (mem_zeroWires.mp hkb).2 r]
      cases tag D j <;> rfl
    · have hop : tag D j = false := by
        cases ht : tag D j with
        | false => rfl
        | true =>
            exfalso
            apply hko
            refine mem_zeroWires.mpr ⟨by omega, ?_⟩
            intro r
            rw [val_gate h.1 _ j hjlt, ht, gop_true]
            rcases hk with hk | hk
            · rw [(mem_zeroWires.mp hk).2 r]; rfl
            · rw [(mem_zeroWires.mp hk).2 r]; simp
      rcases hk with hk | hk
      · refine ⟨opB D j, hb, ?_⟩
        intro r
        rw [val_gate h.1 _ j hjlt, hop, gop_false, (mem_zeroWires.mp hk).2 r]
        rfl
      · refine ⟨opA D j, ha, ?_⟩
        intro r
        rw [val_gate h.1 _ j hjlt, hop, gop_false, (mem_zeroWires.mp hk).2 r]
        simp
  have hac : A ⊆ rowCopies D rows := by
    intro j hj
    obtain ⟨hlt, hop, ht⟩ := hA j hj
    obtain ⟨ha, hb, _⟩ := h.1 j hlt
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, ?_⟩
    rcases ht with ht | ht
    · refine ⟨opB D j, hb, ?_⟩
      intro r
      rw [val_gate h.1 _ j hlt, hop, gop_true, ht r]
      rfl
    · refine ⟨opA D j, ha, ?_⟩
      intro r
      rw [val_gate h.1 _ j hlt, hop, gop_true, ht r]
      simp
  have hdis : Disjoint (copyBoundary n D K) A := by
    rw [Finset.disjoint_left]
    intro j hj ha
    obtain ⟨hlt, hop, ht⟩ := hA j ha
    obtain ⟨_, hcase⟩ := Finset.mem_filter.mp hj
    rcases hcase with ⟨hka, hkb⟩ | ⟨hk, hko⟩
    · rcases ht with ht | ht
      · have hh := (mem_zeroWires.mp hka).2 r0; rw [ht r0] at hh; contradiction
      · have hh := (mem_zeroWires.mp hkb).2 r0; rw [ht r0] at hh; contradiction
    · apply hko
      refine mem_zeroWires.mpr ⟨by omega, ?_⟩
      intro r
      rw [val_gate h.1 _ j hlt, hop, gop_true]
      rcases hk with hk | hk
      · rw [(mem_zeroWires.mp hk).2 r]; rfl
      · rw [(mem_zeroWires.mp hk).2 r]; simp
  have hc := Finset.card_le_card (Finset.union_subset hbc hac)
  rw [Finset.card_union_of_disjoint hdis] at hc
  omega

lemma copies_from_star_ports {n : ℕ} {α : Type} {D : Dag}
    (h : StrictLive n D) (rows : α → Fin n → Bool)
    (hout : ∃ r, val D (rows r) (outW n D) = true)
    (I : Finset (Fin n)) (hI : ∀ i ∈ I, ∀ r, rows r i = false)
    (z : Fin n) (hz : ∀ r, rows r z = true)
    (pos : Fin n → ℕ × Bool)
    (hpos : ∀ i ∈ I, (pos i).1 < D.length ∧ tag D (pos i).1 = true ∧
      z ∈ supp n D (src D (pos i)) ∧
      supp n D (src D ((pos i).1, !(pos i).2)) = {i}) :
    2 * I.card ≤ (rowCopies D rows).card := by
  classical
  have hinj : Set.InjOn (fun i => (pos i).1) (↑I : Set (Fin n)) := by
    intro i hi j hj heq
    change (pos i).1 = (pos j).1 at heq
    by_cases hs : (pos i).2 = (pos j).2
    · have he : pos i = pos j := Prod.ext heq hs
      have hh := (hpos i hi).2.2.2
      rw [he, (hpos j hj).2.2.2] at hh
      exact (Finset.singleton_injective hh).symm
    · have he : src D (pos i) = src D ((pos j).1, !(pos j).2) := by
        unfold src
        rw [heq]
        cases ha : (pos i).2 <;> cases hb : (pos j).2 <;> simp_all
      have hh := (hpos i hi).2.2.1
      rw [he, (hpos j hj).2.2.2, Finset.mem_singleton] at hh
      obtain ⟨r, _⟩ := hout
      have hf := hI j hj r
      rw [← hh, hz r] at hf
      contradiction
  let A := I.image (fun i => (pos i).1)
  have hA : ∀ j ∈ A, j < D.length ∧ tag D j = true ∧
      ((∀ r, val D (rows r) (opA D j) = true) ∨
       (∀ r, val D (rows r) (opB D j) = true)) := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨hlt, hop, hzi, _⟩ := hpos i hi
    have ht := true_support_on_rows h.1 rows hz hzi
    refine ⟨hlt, hop, ?_⟩
    cases hs : (pos i).2
    · exact Or.inl (by simpa [src, hs] using ht)
    · exact Or.inr (by simpa [src, hs] using ht)
  have hc := copies_from_zero_sources_and_true_ands h rows hout I hI A hA
  have hcard : A.card = I.card := Finset.card_image_of_injOn hinj
  omega

section NeighborhoodPrerequisites

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

def sem_W (n : ℕ) (D : Dag) (x : Fin n) : Finset (ℕ × Bool) := exitArcs n D (carrierT n D {x})

lemma sem_mem_W {x : Fin n} {e : ℕ × Bool} : e ∈ sem_W n D x ↔
    e.1 < D.length ∧ x ∈ supp n D (src D e) ∧ x ∉ supp n D (n + e.1) := sem_mem_exit1

lemma sem_W_and (hS : Strict n D) {x : Fin n} {e : ℕ × Bool} (he : e ∈ sem_W n D x) :
    tag D e.1 = true := by
  obtain ⟨hj, h1, h2⟩ := sem_mem_W.mp he
  by_contra ht
  rw [Bool.not_eq_true] at ht
  apply h2
  rw [sem_supp_or hS hj ht, Finset.mem_union]
  obtain ⟨j, s⟩ := e
  cases s
  · left; simpa [src] using h1
  · right; simpa [src] using h1

lemma sem_dom_split (hS : Strict n D) (hC : sem_Comp n G D) (x : Fin n → Bool) (v : Fin n)
    (b : ℕ) (hdom : sem_Dom n D b v.val) (h0 : ¬ sem_Edge G x) (h1 : sem_Edge G (sem_ins v x)) :
    val D x b = false ∧ val D (sem_ins v x) b = true := by
  have hne : val D x b ≠ val D (sem_ins v x) b := by
    intro heq
    have h2 := sem_dom_eq hS x _ v (sem_ins_agree v x) b hdom heq
    exact h0 ((hC x).mp (by rw [h2]; exact (hC _).mpr h1))
  have hmono := val_mono hS x (sem_ins v x) (sem_ins_ge v x) b
  cases hx : val D x b
  · refine ⟨rfl, ?_⟩
    cases hy : val D (sem_ins v x) b
    · exact absurd (hx.trans hy.symm) hne
    · rfl
  · exact absurd (hx.trans (hmono hx).symm) hne

lemma sem_branch_empty (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) {i : Fin n}
    (hi : i ∈ ineligSet n D) {b : ℕ} (hch : sem_Chain n D i.val b) (hf : 2 ≤ fanout D b) :
    supp n D b = ∅ := by
  have hsub := sem_dom_pure hG hS hC i b (sem_chain_dom hS hch)
  refine Finset.eq_empty_of_forall_notMem (fun x hx => ?_)
  have h1 := hsub hx
  rw [Finset.mem_singleton] at h1
  have h2 := mem_ineligSet.mp hi b (h1 ▸ hx)
  omega

lemma sem_path_chain {a t : ℕ} (hp : Relation.ReflTransGen (sem_step n D) a t) :
    sem_Chain n D a t ∨ ∃ b, sem_Chain n D a b ∧ 2 ≤ fanout D b := by
  induction hp using Relation.ReflTransGen.head_induction_on with
  | refl => exact Or.inl Relation.ReflTransGen.refl
  | @head a a' hstep _ ih =>
    by_cases hf : fanout D a = 1
    · rcases ih with h1 | ⟨b, h1, h2⟩
      · exact Or.inl (Relation.ReflTransGen.head ⟨hstep, hf⟩ h1)
      · exact Or.inr ⟨b, Relation.ReflTransGen.head ⟨hstep, hf⟩ h1, h2⟩
    · have := sem_step_fanout hstep
      exact Or.inr ⟨a, Relation.ReflTransGen.refl, by omega⟩

lemma sem_bzero_mem (hS : Strict n D) {b : ℕ} (hf : 2 ≤ fanout D b) (he : supp n D b = ∅) :
    b ∈ (inner n D).filter (fun w => ¬ (supp n D w).Nonempty) :=
  Finset.mem_filter.mpr ⟨sb_mem_inner.mpr (lt_of_fanout_pos hS (w := b) (by omega)),
    by rw [he]; exact Finset.not_nonempty_empty⟩

lemma sem_bzero_branch (hS : Strict n D) (hB0 : Bzero n D = 0) {b : ℕ} (hf : 2 ≤ fanout D b) :
    (supp n D b).Nonempty := by
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  have h1 : fanout D b - 1 ≤ ∑ w ∈ (inner n D).filter (fun w => ¬ (supp n D w).Nonempty),
      (fanout D w - 1) :=
    Finset.single_le_sum (f := fun w => fanout D w - 1) (fun _ _ => Nat.zero_le _)
      (sem_bzero_mem hS hf hne)
  unfold Bzero surplusOn at hB0
  omega

lemma sem_noempty_unique (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (hB0 : Bzero n D = 0) {i : Fin n} (hi : i ∈ ineligSet n D) {w : ℕ}
    (hp : Relation.ReflTransGen (sem_step n D) i.val w) : sem_Chain n D i.val w := by
  rcases sem_path_chain hp with h1 | ⟨b, h1, h2⟩
  · exact h1
  · have h3 := sem_bzero_branch h.1 hB0 h2
    rw [sem_branch_empty hG h.1 hC hi h1 h2] at h3
    exact absurd h3 Finset.not_nonempty_empty

def k4_Pos (n : ℕ) (G : Fin n → Fin n → Prop) (D : Dag) (pos : Fin n → ℕ × Bool) : Prop :=
  (∀ i ∈ ineligSet n D, (pos i).1 < D.length ∧ supp n D (n + (pos i).1) = ∅ ∧
    (∀ a, G i a → a ∈ supp n D (src D (pos i))) ∧
    supp n D (src D ((pos i).1, !(pos i).2)) = {i}) ∧
  ∀ i ∈ ineligSet n D, ∀ i' ∈ ineligSet n D, pos i = pos i' → i = i'

lemma k4_assigned (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D) :
    ∃ pos : Fin n → ℕ × Bool, k4_Pos n G D pos := by
  classical
  have hex : ∀ i : Fin n, ∃ e : ℕ × Bool, i ∈ ineligSet n D → (e.1 < D.length ∧
      supp n D (n + e.1) = ∅ ∧ (∀ a, G i a → a ∈ supp n D (src D e)) ∧
      supp n D (src D (e.1, !e.2)) = {i}) := by
    intro i
    by_cases hi : i ∈ ineligSet n D
    · obtain ⟨e, h1, -, h3, h4, h5, -, -⟩ := sem_inelig_consumer hG h hC hi
      exact ⟨(e.1, !e.2), fun _ => ⟨h1, h4, h5, by simpa using h3⟩⟩
    · exact ⟨(0, false), fun hc => absurd hc hi⟩
  choose pos hpos using hex
  refine ⟨pos, hpos, fun i hi i' hi' he => ?_⟩
  have h1 := (hpos i hi).2.2.2
  rw [he, (hpos i' hi').2.2.2] at h1
  exact (Finset.singleton_injective h1).symm

abbrev V := Fin 10

def neighbors (v : V) : Nat :=
  [50, 69, 138, 276, 521, 385, 770, 548, 104, 208].getD v.val 0

abbrev adj (u v : V) : Prop := (neighbors u).testBit v.val = true

lemma graph_ok : sem_Gr adj := by
  unfold sem_Gr
  decide +kernel

end NeighborhoodPrerequisites

lemma false_input_reaches {n : ℕ} {D : Dag} (hS : Strict n D) (x : Fin n → Bool) :
    ∀ w, w < n + D.length → val D x w = false →
      ∃ i : Fin n, x i = false ∧ Relation.ReflTransGen (sem_step n D) i.val w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
      intro hw hv
      by_cases hn : w < n
      · refine ⟨⟨w, hn⟩, ?_, Relation.ReflTransGen.refl⟩
        simpa only [val_input D x w hn] using hv
      · let j := w - n
        have hwj : w = n + j := by omega
        have hj : j < D.length := by omega
        obtain ⟨ha, hb, _⟩ := hS j hj
        have hop : val D x (opA D j) = false ∨ val D x (opB D j) = false := by
          rw [hwj, val_gate hS x j hj] at hv
          cases ht : tag D j
          · rw [ht, gop_false, Bool.or_eq_false_iff] at hv
            exact Or.inl hv.1
          · rw [ht, gop_true, Bool.and_eq_false_iff] at hv
            exact hv
        rcases hop with hop | hop
        · obtain ⟨i, hxi, hp⟩ := ih (opA D j) (by omega) (by omega) hop
          refine ⟨i, hxi, ?_⟩
          rw [hwj]
          exact Relation.ReflTransGen.tail hp (by simpa [src] using sem_step_src (n := n) hj false)
        · obtain ⟨i, hxi, hp⟩ := ih (opB D j) (by omega) (by omega) hop
          refine ⟨i, hxi, ?_⟩
          rw [hwj]
          exact Relation.ReflTransGen.tail hp (by simpa [src] using sem_step_src (n := n) hj true)

lemma ineligible_reachable_no_neighbor_support {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}
    (hG : sem_Gr G) (h : StrictLive n D) (hc : sem_Comp n G D)
    (hz : Bzero n D = 0) {i z : Fin n} (hi : i ∈ ineligSet n D) (hiz : G i z)
    {w : ℕ} (hp : Relation.ReflTransGen (sem_step n D) i.val w) :
    z ∉ supp n D w := by
  have hchain := sem_noempty_unique hG h hc hz hi hp
  have he : sem_Edge G (sem_ins i (single z)) :=
    ⟨i, z, hiz, sem_ins_self i _, by simp [sem_ins, single]⟩
  have hv := (sem_dom_split h.1 hc (single z) i w (sem_chain_dom h.1 hchain)
    (sem_single_no_edge hG z) he).1
  intro hmem
  have hh := mem_supp.mp hmem
  rw [hv] at hh
  contradiction

lemma zero_boundary_no_neighbor_support {n : ℕ} {α : Type}
    {G : Fin n → Fin n → Prop} {D : Dag}
    (hG : sem_Gr G) (h : StrictLive n D) (hc : sem_Comp n G D)
    (hz : Bzero n D = 0) (rows : α → Fin n → Bool)
    (I : Finset (Fin n)) (hI : I ⊆ ineligSet n D)
    (r0 : α) (hr0 : ∀ i, rows r0 i = false → i ∈ I)
    (z : Fin n) (hIz : ∀ i ∈ I, G i z) :
    ∀ j ∈ copyBoundary n D (zeroWires D rows), z ∉ supp n D (n + j) := by
  intro j hj
  obtain ⟨hj, hcase⟩ := Finset.mem_filter.mp hj
  have hjlt := Finset.mem_range.mp hj
  have hp : opA D j ∈ zeroWires D rows ∨ opB D j ∈ zeroWires D rows := by
    rcases hcase with hh | hh
    · exact Or.inl hh.1
    · exact hh.1
  have hcand {w : ℕ} (hw : w ∈ zeroWires D rows)
      (hstep : sem_step n D w (n + j)) : z ∉ supp n D (n + j) := by
    obtain ⟨hwlt, hwzero⟩ := mem_zeroWires.mp hw
    obtain ⟨i, hif, hip⟩ := false_input_reaches h.1 (rows r0) w hwlt (hwzero r0)
    have hi := hr0 i hif
    exact ineligible_reachable_no_neighbor_support hG h hc hz (hI hi) (hIz i hi)
      (Relation.ReflTransGen.tail hip hstep)
  rcases hp with hp | hp
  · exact hcand hp (by simpa [src] using sem_step_src (n := n) hjlt false)
  · exact hcand hp (by simpa [src] using sem_step_src (n := n) hjlt true)

noncomputable def centerGates {n : ℕ} (D : Dag) (z : Fin n) : Finset ℕ := by
  classical
  exact (Finset.range D.length).filter (fun j => z ∈ supp n D (n + j))

lemma zero_boundary_copies {n : ℕ} {α : Type} {D : Dag}
    (hS : Strict n D) (rows : α → Fin n → Bool) :
    copyBoundary n D (zeroWires D rows) ⊆ rowCopies D rows := by
  classical
  intro j hj
  obtain ⟨hj, hcase⟩ := Finset.mem_filter.mp hj
  have hjlt := Finset.mem_range.mp hj
  obtain ⟨ha, hb, _⟩ := hS j hjlt
  refine Finset.mem_filter.mpr ⟨hj, ?_⟩
  rcases hcase with ⟨hka, hkb⟩ | ⟨hk, hko⟩
  · refine ⟨opA D j, ha, ?_⟩
    intro r
    rw [val_gate hS _ j hjlt, (mem_zeroWires.mp hka).2 r, (mem_zeroWires.mp hkb).2 r]
    cases tag D j <;> rfl
  · have hop : tag D j = false := by
      cases ht : tag D j with
      | false => rfl
      | true =>
          exfalso
          apply hko
          refine mem_zeroWires.mpr ⟨by omega, ?_⟩
          intro r
          rw [val_gate hS _ j hjlt, ht, gop_true]
          rcases hk with hk | hk
          · rw [(mem_zeroWires.mp hk).2 r]; rfl
          · rw [(mem_zeroWires.mp hk).2 r]; simp
    rcases hk with hk | hk
    · refine ⟨opB D j, hb, ?_⟩
      intro r
      rw [val_gate hS _ j hjlt, hop, gop_false, (mem_zeroWires.mp hk).2 r]
      rfl
    · refine ⟨opA D j, ha, ?_⟩
      intro r
      rw [val_gate hS _ j hjlt, hop, gop_false, (mem_zeroWires.mp hk).2 r]
      simp

lemma copies_plus_center_gates {n : ℕ} {α : Type}
    {G : Fin n → Fin n → Prop} {D : Dag}
    (hG : sem_Gr G) (h : StrictLive n D) (hc : sem_Comp n G D)
    (hz : Bzero n D = 0) (rows : α → Fin n → Bool)
    (hout : ∃ r, val D (rows r) (outW n D) = true)
    (I : Finset (Fin n)) (hI : I ⊆ ineligSet n D)
    (hIf : ∀ i ∈ I, ∀ r, rows r i = false)
    (r0 : α) (hr0 : ∀ i, rows r0 i = false → i ∈ I)
    (z : Fin n) (hIz : ∀ i ∈ I, G i z) (hzr : ∀ r, rows r z = true)
    (A : Finset ℕ) (hA : ∀ j ∈ A, j < D.length ∧ tag D j = true ∧
      ((∀ r, val D (rows r) (opA D j) = true) ∨
       (∀ r, val D (rows r) (opB D j) = true)) ∧ z ∉ supp n D (n + j)) :
    I.card + A.card + (centerGates D z).card ≤ (rowCopies D rows).card := by
  classical
  let K := zeroWires D rows
  let Z := copyBoundary n D K
  let B := centerGates D z
  obtain ⟨rp, hrp⟩ := hout
  have hK : K ⊆ inner n D := by
    intro w hw
    obtain ⟨hw, hv⟩ := mem_zeroWires.mp hw
    apply sb_mem_inner.mpr
    by_contra hn
    have heq : w = outW n D := by unfold outW; omega
    have hh := hv rp
    rw [heq, hrp] at hh
    contradiction
  have hclosed : ∀ j < D.length, opA D j ∈ K → opB D j ∈ K → n + j ∈ K := by
    intro j hj ha hb
    refine mem_zeroWires.mpr ⟨by omega, ?_⟩
    intro r
    rw [val_gate h.1 _ j hj, (mem_zeroWires.mp ha).2 r, (mem_zeroWires.mp hb).2 r]
    cases tag D j <;> rfl
  have hsource : I.card ≤ (sources n K).card := by
    have hs : I.image Fin.val ⊆ sources n K := by
      intro w hw
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
      refine Finset.mem_filter.mpr ⟨mem_zeroWires.mpr ⟨by omega, ?_⟩, i.isLt⟩
      intro r
      rw [val_input D _ i.val i.isLt]
      exact hIf i hi r
    have hh := Finset.card_le_card hs
    simpa only [Finset.card_image_of_injective _ Fin.val_injective] using hh
  have hIZ : I.card ≤ Z.card := hsource.trans (source_le_copyBoundary h K hK hclosed)
  have hZC : Z ⊆ rowCopies D rows := zero_boundary_copies h.1 rows
  have hAC : A ⊆ rowCopies D rows := by
    intro j hj
    obtain ⟨hlt, hop, ht, _⟩ := hA j hj
    obtain ⟨ha, hb, _⟩ := h.1 j hlt
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, ?_⟩
    rcases ht with ht | ht
    · refine ⟨opB D j, hb, ?_⟩
      intro r
      rw [val_gate h.1 _ j hlt, hop, gop_true, ht r]; rfl
    · refine ⟨opA D j, ha, ?_⟩
      intro r
      rw [val_gate h.1 _ j hlt, hop, gop_true, ht r]; simp
  have hBC : B ⊆ rowCopies D rows := by
    intro j hj
    obtain ⟨hj, hzs⟩ := Finset.mem_filter.mp hj
    refine Finset.mem_filter.mpr ⟨hj, z.val, by omega, ?_⟩
    intro r
    rw [true_support_on_rows h.1 rows hzr hzs r, val_input D _ z.val z.isLt, hzr r]
  have hZA : Disjoint Z A := by
    rw [Finset.disjoint_left]
    intro j hj ha
    obtain ⟨hlt, hop, ht, _⟩ := hA j ha
    obtain ⟨_, hcase⟩ := Finset.mem_filter.mp hj
    rcases hcase with ⟨hka, hkb⟩ | ⟨hk, hko⟩
    · rcases ht with ht | ht
      · have hh := (mem_zeroWires.mp hka).2 rp; rw [ht rp] at hh; contradiction
      · have hh := (mem_zeroWires.mp hkb).2 rp; rw [ht rp] at hh; contradiction
    · apply hko
      refine mem_zeroWires.mpr ⟨by omega, ?_⟩
      intro r
      rw [val_gate h.1 _ j hlt, hop, gop_true]
      rcases hk with hk | hk
      · rw [(mem_zeroWires.mp hk).2 r]; rfl
      · rw [(mem_zeroWires.mp hk).2 r]; simp
  have hZB : Disjoint Z B := by
    rw [Finset.disjoint_left]
    intro j hj hb
    exact zero_boundary_no_neighbor_support hG h hc hz rows I hI r0 hr0 z hIz j hj
      (Finset.mem_filter.mp hb).2
  have hAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro j ha hb
    exact (hA j ha).2.2.2 (Finset.mem_filter.mp hb).2
  have hU : (Z ∪ A) ∪ B ⊆ rowCopies D rows :=
    Finset.union_subset (Finset.union_subset hZC hAC) hBC
  have hcard := Finset.card_le_card hU
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hZB, hAB⟩),
    Finset.card_union_of_disjoint hZA] at hcard
  change I.card + A.card + B.card ≤ _
  omega

lemma copies_from_ineligible_neighbors {n : ℕ} {α : Type}
    {G : Fin n → Fin n → Prop} {D : Dag}
    (hG : sem_Gr G) (h : StrictLive n D) (hc : sem_Comp n G D)
    (rows : α → Fin n → Bool) (hout : ∃ r, val D (rows r) (outW n D) = true)
    (I : Finset (Fin n)) (hI : I ⊆ ineligSet n D)
    (hIf : ∀ i ∈ I, ∀ r, rows r i = false)
    (z : Fin n) (hIz : ∀ i ∈ I, G i z) (hzr : ∀ r, rows r z = true) :
    2 * I.card ≤ (rowCopies D rows).card := by
  obtain ⟨pos, hpos⟩ := k4_assigned hG h hc
  apply copies_from_star_ports h rows hout I hIf z hzr pos
  intro i hi
  obtain ⟨hlt, hempty, hnb, hsingle⟩ := hpos.1 i (hI hi)
  have hzi := hnb z (hIz i hi)
  refine ⟨hlt, ?_, hzi, hsingle⟩
  apply sem_W_and h.1 (x := z)
  refine sem_mem_W.mpr ⟨hlt, hzi, ?_⟩
  rw [hempty]
  exact Finset.notMem_empty z

lemma copies_from_ineligible_neighbors_and_center {n : ℕ} {α : Type}
    {G : Fin n → Fin n → Prop} {D : Dag}
    (hG : sem_Gr G) (h : StrictLive n D) (hc : sem_Comp n G D)
    (hz : Bzero n D = 0) (rows : α → Fin n → Bool)
    (hout : ∃ r, val D (rows r) (outW n D) = true)
    (I : Finset (Fin n)) (hI : I ⊆ ineligSet n D)
    (hIf : ∀ i ∈ I, ∀ r, rows r i = false)
    (r0 : α) (hr0 : ∀ i, rows r0 i = false → i ∈ I)
    (z : Fin n) (hIz : ∀ i ∈ I, G i z) (hzr : ∀ r, rows r z = true) :
    2 * I.card + (centerGates D z).card ≤ (rowCopies D rows).card := by
  classical
  obtain ⟨pos, hpos⟩ := k4_assigned hG h hc
  have hinj : Set.InjOn (fun i => (pos i).1) (↑I : Set (Fin n)) := by
    intro i hi j hj heq
    change (pos i).1 = (pos j).1 at heq
    by_cases hs : (pos i).2 = (pos j).2
    · exact hpos.2 i (hI hi) j (hI hj) (Prod.ext heq hs)
    · have he : src D (pos i) = src D ((pos j).1, !(pos j).2) := by
        unfold src
        rw [heq]
        cases ha : (pos i).2 <;> cases hb : (pos j).2 <;> simp_all
      have hh := (hpos.1 i (hI hi)).2.2.1 z (hIz i hi)
      rw [he, (hpos.1 j (hI hj)).2.2.2, Finset.mem_singleton] at hh
      have hjz := hIz j hj
      rw [hh] at hjz
      exact (hG.2.1 j hjz).elim
  let A := I.image (fun i => (pos i).1)
  have hA : ∀ j ∈ A, j < D.length ∧ tag D j = true ∧
      ((∀ r, val D (rows r) (opA D j) = true) ∨
       (∀ r, val D (rows r) (opB D j) = true)) ∧ z ∉ supp n D (n + j) := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨hlt, hempty, hnb, _⟩ := hpos.1 i (hI hi)
    have hzi := hnb z (hIz i hi)
    have hzn : z ∉ supp n D (n + (pos i).1) := by rw [hempty]; exact Finset.notMem_empty z
    have hop := sem_W_and h.1 (sem_mem_W.mpr ⟨hlt, hzi, hzn⟩)
    have ht := true_support_on_rows h.1 rows hzr hzi
    refine ⟨hlt, hop, ?_, hzn⟩
    cases hs : (pos i).2
    · exact Or.inl (by simpa [src, hs] using ht)
    · exact Or.inr (by simpa [src, hs] using ht)
  have hh := copies_plus_center_gates hG h hc hz rows hout I hI hIf r0 hr0 z hIz hzr A hA
  have hcard : A.card = I.card := Finset.card_image_of_injOn hinj
  omega

def neighborhoodResidualRows (x : Fin 6 → Bool) (v : Fin 10) : Bool :=
  match v.val with
  | 0 => true
  | 2 => x 0
  | 8 => x 1
  | 9 => x 2
  | 3 => x 3
  | 7 => x 4
  | 6 => x 5
  | _ => false

def residualC6 (x : Fin 6 → Bool) : Bool :=
  x 0 && x 3 || x 0 && x 4 || x 1 && x 3 || x 1 && x 5 ||
    x 2 && x 4 || x 2 && x 5

def neighborhoodI : Finset (Fin 10) := {1, 4, 5}

lemma neighborhood_rows_false (x : Fin 6 → Bool) :
    ∀ i ∈ neighborhoodI, neighborhoodResidualRows x i = false := by
  intro i hi
  simp only [neighborhoodI, Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl <;> rfl

lemma neighborhood_rows_top (v : Fin 10) :
    neighborhoodResidualRows (fun _ => true) v = false ↔ v ∈ neighborhoodI := by
  fin_cases v <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma neighborhood_residual_edges : ∀ x : Fin 6 → Bool,
    sem_Edge adj (neighborhoodResidualRows x) ↔ residualC6 x = true := by
  unfold sem_Edge
  decide +kernel

lemma neighborhood_residual_correct {D : Dag} (hc : sem_Comp 10 adj D)
    (x : Fin 6 → Bool) :
    val D (neighborhoodResidualRows x) (outW 10 D) = residualC6 x := by
  apply Bool.eq_iff_iff.mpr
  exact (hc _).trans (neighborhood_residual_edges x)

lemma neighborhood_six_copies {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (hi : neighborhoodI ⊆ ineligSet 10 D) :
    6 ≤ (rowCopies D neighborhoodResidualRows).card := by
  have hout : ∃ x, val D (neighborhoodResidualRows x) (outW 10 D) = true :=
    ⟨fun _ => true, neighborhood_residual_correct hc _⟩
  have hh := copies_from_ineligible_neighbors graph_ok h hc neighborhoodResidualRows
    hout neighborhoodI hi (fun i hi x => neighborhood_rows_false x i hi) (0 : Fin 10)
    (by decide +kernel) (fun _ => rfl)
  have hcard : neighborhoodI.card = 3 := by decide
  omega

lemma neighborhood_six_plus_center_copies {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (hz : Bzero 10 D = 0)
    (hi : neighborhoodI ⊆ ineligSet 10 D) :
    6 + (centerGates D (0 : Fin 10)).card ≤ (rowCopies D neighborhoodResidualRows).card := by
  have hout : ∃ x, val D (neighborhoodResidualRows x) (outW 10 D) = true :=
    ⟨fun _ => true, neighborhood_residual_correct hc _⟩
  have hh := copies_from_ineligible_neighbors_and_center graph_ok h hc hz
    neighborhoodResidualRows hout neighborhoodI hi (fun i hi x => neighborhood_rows_false x i hi)
    (fun _ => true) (fun i hi => (neighborhood_rows_top i).mp hi) (0 : Fin 10)
    (by decide +kernel) (fun _ => rfl)
  have hcard : neighborhoodI.card = 3 := by decide
  omega

lemma petersen_adj_iff : ∀ u v : Fin 10,
    adj u v ↔ (u, v) ∈ petersenEdges ∨ (v, u) ∈ petersenEdges := by
  decide +kernel

lemma petersen_semEdge_iff (x : Fin 10 → Bool) :
    sem_Edge adj x ↔ edgeFunction petersenEdges x = true := by
  rw [edgeFunction_true_iff]
  constructor
  · rintro ⟨u, v, huv, hu, hv⟩
    rcases (petersen_adj_iff u v).mp huv with h | h
    · exact ⟨(u, v), h, by simp [edgeTerm, hu, hv]⟩
    · exact ⟨(v, u), h, by simp [edgeTerm, hu, hv]⟩
  · rintro ⟨⟨u, v⟩, huv, h⟩
    have hh : x u = true ∧ x v = true := by simpa [edgeTerm] using h
    exact ⟨u, v, (petersen_adj_iff u v).mpr (Or.inl huv), hh.1, hh.2⟩

lemma support_exit_on_path {n : ℕ} {D : Dag} {z : Fin n} {w : ℕ}
    (hp : Relation.ReflTransGen (sem_step n D) z.val w) (hw : z ∉ supp n D w) :
    ∃ e ∈ sem_W n D z, Relation.ReflTransGen (sem_step n D) (n + e.1) w := by
  revert hw
  induction hp with
  | refl =>
      intro hz
      rw [supp_input] at hz
      exact (hz (Finset.mem_singleton_self z)).elim
  | @tail a b hp hs ih =>
      intro hb
      by_cases ha : z ∈ supp n D a
      · obtain ⟨j, s, hj, rfl, hsrc⟩ := sem_step_iff.mp hs
        refine ⟨(j, s), sem_mem_W.mpr ⟨hj, ?_, hb⟩, Relation.ReflTransGen.refl⟩
        simpa only [hsrc] using ha
      · obtain ⟨e, he, hep⟩ := ih ha
        exact ⟨e, he, Relation.ReflTransGen.tail hep hs⟩

lemma center_exits_reachable_from_neighbors {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}
    (hG : sem_Gr G) (h : StrictLive n D) (hc : sem_Comp n G D)
    (I : Finset (Fin n)) (hI : I ⊆ ineligSet n D) (z : Fin n)
    (hIz : ∀ i ∈ I, G i z) (hW : (sem_W n D z).card = I.card) :
    ∀ e ∈ sem_W n D z, ∃ i ∈ I,
      Relation.ReflTransGen (sem_step n D) i.val (n + e.1) := by
  classical
  obtain ⟨pos, hpos⟩ := k4_assigned hG h hc
  have hinj : Set.InjOn pos (↑I : Set (Fin n)) :=
    fun i hi j hj he => hpos.2 i (hI hi) j (hI hj) he
  have hsub : I.image pos ⊆ sem_W n D z := by
    intro e he
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hj, hempty, hnb, _⟩ := hpos.1 i (hI hi)
    refine sem_mem_W.mpr ⟨hj, hnb z (hIz i hi), ?_⟩
    rw [hempty]
    exact Finset.notMem_empty z
  have heq : I.image pos = sem_W n D z :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hW, Finset.card_image_of_injOn hinj])
  intro e he
  rw [← heq] at he
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨hj, _, _, hsingle⟩ := hpos.1 i (hI hi)
  have hmem : i ∈ supp n D (src D ((pos i).1, !(pos i).2)) := by
    rw [hsingle]
    exact Finset.mem_singleton_self i
  have hchain := sem_inelig_chain h.1 (hI hi) hmem
  have hp := sem_rtg_mono (fun _ _ hh => hh.1) hchain
  exact ⟨i, hi, Relation.ReflTransGen.tail hp (sem_step_src hj _)⟩

lemma center_ancestor_no_center_path {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}
    (hG : sem_Gr G) (h : StrictLive n D) (hc : sem_Comp n G D) (hz : Bzero n D = 0)
    (I : Finset (Fin n)) (hI : I ⊆ ineligSet n D) (z : Fin n)
    (hIz : ∀ i ∈ I, G i z) (hW : (sem_W n D z).card = I.card)
    {w v : ℕ} (hwv : Relation.ReflTransGen (sem_step n D) w v)
    (hv : z ∈ supp n D v) (hw : z ∉ supp n D w) :
    ¬ Relation.ReflTransGen (sem_step n D) z.val w := by
  intro hp
  obtain ⟨e, he, hew⟩ := support_exit_on_path hp hw
  obtain ⟨i, hi, hie⟩ := center_exits_reachable_from_neighbors hG h hc I hI z hIz hW e he
  exact ineligible_reachable_no_neighbor_support hG h hc hz (hI hi) (hIz i hi)
    (hie.trans (hew.trans hwv)) hv

lemma value_eq_if_ancestors_agree {n : ℕ} {D : Dag} (hS : Strict n D)
    (x y : Fin n → Bool) : ∀ w,
      (∀ i : Fin n, Relation.ReflTransGen (sem_step n D) i.val w → x i = y i) →
      val D x w = val D y w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
      intro hagree
      by_cases hn : w < n
      · rw [val_input D x w hn, val_input D y w hn]
        exact hagree ⟨w, hn⟩ Relation.ReflTransGen.refl
      · by_cases hw : w < n + D.length
        · let j := w - n
          have hwj : w = n + j := by omega
          have hj : j < D.length := by omega
          obtain ⟨ha, hb, _⟩ := hS j hj
          have hsa : sem_step n D (opA D j) (n + j) :=
            by simpa [src] using sem_step_src (n := n) hj false
          have hsb : sem_step n D (opB D j) (n + j) :=
            by simpa [src] using sem_step_src (n := n) hj true
          have hea := ih (opA D j) (by omega) (fun i hp => hagree i
            (by rw [hwj]; exact Relation.ReflTransGen.tail hp hsa))
          have heb := ih (opB D j) (by omega) (fun i hp => hagree i
            (by rw [hwj]; exact Relation.ReflTransGen.tail hp hsb))
          rw [hwj, val_gate hS x j hj, val_gate hS y j hj, hea, heb]
        · rw [val_ge D x w (by omega), val_ge D y w (by omega)]

lemma center_ancestor_independent {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}
    (hG : sem_Gr G) (h : StrictLive n D) (hc : sem_Comp n G D) (hz : Bzero n D = 0)
    (I : Finset (Fin n)) (hI : I ⊆ ineligSet n D) (z : Fin n)
    (hIz : ∀ i ∈ I, G i z) (hW : (sem_W n D z).card = I.card)
    {w v : ℕ} (hwv : Relation.ReflTransGen (sem_step n D) w v)
    (hv : z ∈ supp n D v) (hw : z ∉ supp n D w)
    (x y : Fin n → Bool) (hxy : ∀ i, i ∉ insert z I → x i = y i) :
    val D x w = val D y w := by
  classical
  apply value_eq_if_ancestors_agree h.1 x y w
  intro i hip
  apply hxy i
  intro hi
  rcases Finset.mem_insert.mp hi with hiz | hi
  · subst i
    exact center_ancestor_no_center_path hG h hc hz I hI z hIz hW hwv hv hw hip
  · exact ineligible_reachable_no_neighbor_support hG h hc hz (hI hi) (hIz i hi)
      (hip.trans hwv) hv

def petersenResidualProjection (x : Fin 10 → Bool) (v : Fin 6) : Bool :=
  match v.val with
  | 0 => x 2
  | 1 => x 8
  | 2 => x 9
  | 3 => x 3
  | 4 => x 7
  | _ => x 6

lemma residual_projection_agrees (x : Fin 10 → Bool) (i : Fin 10)
    (hi : i ∉ insert 0 neighborhoodI) :
    x i = neighborhoodResidualRows (petersenResidualProjection x) i := by
  fin_cases i <;> simp_all [neighborhoodResidualRows, petersenResidualProjection, neighborhoodI]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma residual_projection_edge : ∀ x : Fin 10 → Bool,
    residualC6 (petersenResidualProjection x) = true → sem_Edge adj x := by
  unfold sem_Edge
  decide +kernel

lemma residual_pure_ancestor_globally_pure {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 adj D) (hz : Bzero 10 D = 0)
    (hi : neighborhoodI ⊆ ineligSet 10 D) (hW : (sem_W 10 D (0 : Fin 10)).card = 3)
    {w v : ℕ} (hwv : Relation.ReflTransGen (sem_step 10 D) w v)
    (hv : (0 : Fin 10) ∈ supp 10 D v) (hw : (0 : Fin 10) ∉ supp 10 D w)
    (hpure : ∀ x : Fin 6 → Bool,
      val D (neighborhoodResidualRows x) w = true → residualC6 x = true) :
    ∀ x : Fin 10 → Bool, val D x w = true → sem_Edge adj x := by
  intro x hx
  have hW' : (sem_W 10 D (0 : Fin 10)).card = neighborhoodI.card := by
    rw [hW]; rfl
  have heq := center_ancestor_independent graph_ok h hc hz neighborhoodI hi (0 : Fin 10)
    (by decide +kernel) hW' hwv hv hw x
    (neighborhoodResidualRows (petersenResidualProjection x)) (residual_projection_agrees x)
  rw [heq] at hx
  exact residual_projection_edge x (hpure _ hx)

def outerCycleInput (x : Fin 10 → Bool) : Fin 6 → Bool :=
  ![x 2, x 8, x 9, x 3, x 7, x 6]

lemma petersen_star_decomposition (x : Fin 10 → Bool) :
    edgeFunction petersenEdges x = (
      residualC6 (outerCycleInput x) ||
      x 1 && (x 0 || (x 2 || x 6)) ||
      x 4 && (x 0 || (x 3 || x 9)) ||
      x 5 && (x 0 || (x 7 || x 8))) := by
  simp [edgeFunction, petersenEdges, residualC6, outerCycleInput,
    Bool.and_or_distrib_left, Bool.or_assoc, Bool.or_left_comm,
    Bool.or_comm, Bool.and_comm]

lemma noisy_pair_eq_of_cycle_false (p q f : Bool)
    (hlower : p ≤ q) (hupper : q ≤ (p || f)) (hf : f = false) : q = p := by
  rw [hf, Bool.or_false] at hupper
  exact le_antisymm hupper hlower

lemma petersen_multioutput_lift
    (Paf Pbe Pcd : (Fin 6 → Bool) → Bool)
    (haf : ∀ y, (y 0 || y 5) ≤ Paf y ∧ Paf y ≤ ((y 0 || y 5) || residualC6 y))
    (hbe : ∀ y, (y 1 || y 4) ≤ Pbe y ∧ Pbe y ≤ ((y 1 || y 4) || residualC6 y))
    (hcd : ∀ y, (y 2 || y 3) ≤ Pcd y ∧ Pcd y ≤ ((y 2 || y 3) || residualC6 y))
    (x : Fin 10 → Bool) :
    (residualC6 (outerCycleInput x) ||
      x 1 && (x 0 || Paf (outerCycleInput x)) ||
      x 4 && (x 0 || Pcd (outerCycleInput x)) ||
      x 5 && (x 0 || Pbe (outerCycleInput x))) =
        edgeFunction petersenEdges x := by
  rw [petersen_star_decomposition]
  cases hf : residualC6 (outerCycleInput x) with
  | true => simp
  | false =>
      have ha := noisy_pair_eq_of_cycle_false _ _ _
        (haf (outerCycleInput x)).1 (haf (outerCycleInput x)).2 hf
      have hb := noisy_pair_eq_of_cycle_false _ _ _
        (hbe (outerCycleInput x)).1 (hbe (outerCycleInput x)).2 hf
      have hc := noisy_pair_eq_of_cycle_false _ _ _
        (hcd (outerCycleInput x)).1 (hcd (outerCycleInput x)).2 hf
      rw [ha, hb, hc]
      simp [outerCycleInput, Bool.or_comm]

lemma zero_wire_support_subset {n : ℕ} {α : Type} {D : Dag}
    (hS : Strict n D) (rows : α → Fin n → Bool)
    (I : Finset (Fin n)) (r : α) (hr : ∀ v, v ∉ I → rows r v = true)
    {w : ℕ} (hw : w ∈ zeroWires D rows) : supp n D w ⊆ I := by
  intro v hv
  by_contra hvi
  have hvtrue := hr v hvi
  have hwtrue : val D (rows r) w = true := by
    apply val_mono hS (single v) (rows r) _ w (mem_supp.mp hv)
    intro u hu
    have huv : u = v := by simpa [single] using hu
    simpa only [huv] using hvtrue
  have hwfalse := (mem_zeroWires.mp hw).2 r
  rw [hwtrue] at hwfalse
  contradiction

lemma earlier_wire_not_first_support {n : ℕ} {D : Dag} {j : ℕ}
    {S : Finset (Fin n)} (hcard : 2 ≤ S.card)
    (hfirst : ∀ k < j, supp n D (n + k) ≠ S) :
    ∀ w < n + j, supp n D w ≠ S := by
  intro w hw heq
  by_cases hn : w < n
  · have hc : S.card = 1 := by
      rw [← heq]
      change (supp n D (⟨w, hn⟩ : Fin n).val).card = 1
      rw [supp_input]
      simp
    omega
  · have hh := hfirst (w - n) (by omega)
    apply hh
    simpa only [Nat.add_sub_of_le (Nat.le_of_not_gt hn)] using heq

lemma first_support_gate_no_zero_input {n : ℕ} {α : Type} {D : Dag}
    (hS : Strict n D) (rows : α → Fin n → Bool)
    (I : Finset (Fin n)) (r : α) (hr : ∀ v, v ∉ I → rows r v = true)
    {j : ℕ} (hj : j < D.length) {S : Finset (Fin n)}
    (hcard : 2 ≤ S.card) (hdis : Disjoint S I)
    (hs : supp n D (n + j) = S)
    (hfirst : ∀ k < j, supp n D (n + k) ≠ S) :
    opA D j ∉ zeroWires D rows ∧ opB D j ∉ zeroWires D rows := by
  have hearly := earlier_wire_not_first_support hcard hfirst
  obtain ⟨ha, hb, _⟩ := hS j hj
  have hnotzero : n + j ∉ zeroWires D rows := by
    intro hz
    have hsub := zero_wire_support_subset hS rows I r hr hz
    rw [hs] at hsub
    have hempty : S = ∅ := by
      ext v
      simp only [Finset.notMem_empty, iff_false]
      intro hv
      exact Finset.disjoint_left.mp hdis hv (hsub hv)
    simp [hempty] at hcard
  have hg := supp_gate hS j hj
  rw [hs] at hg
  have hor_empty : tag D j = false →
      ∀ w, w ∈ zeroWires D rows → supp n D w ⊆ S → supp n D w = ∅ := by
    intro _ w hw hwS
    have hwI := zero_wire_support_subset hS rows I r hr hw
    ext v
    simp only [Finset.notMem_empty, iff_false]
    intro hv
    exact Finset.disjoint_left.mp hdis (hwS hv) (hwI hv)
  cases hop : tag D j with
  | true =>
      constructor <;> intro hz <;> apply hnotzero
      · refine mem_zeroWires.mpr ⟨by omega, ?_⟩
        intro t
        rw [val_gate hS _ j hj, hop, gop_true, (mem_zeroWires.mp hz).2 t]
        rfl
      · refine mem_zeroWires.mpr ⟨by omega, ?_⟩
        intro t
        rw [val_gate hS _ j hj, hop, gop_true, (mem_zeroWires.mp hz).2 t]
        simp
  | false =>
      simp only [hop, Bool.false_eq_true, ↓reduceIte] at hg
      constructor
      · intro hz
        have hsub : supp n D (opA D j) ⊆ S := by rw [hg]; exact Finset.subset_union_left
        have he := hor_empty hop _ hz hsub
        have hbS : supp n D (opB D j) = S := by simpa [he] using hg.symm
        exact hearly _ hb hbS
      · intro hz
        have hsub : supp n D (opB D j) ⊆ S := by rw [hg]; exact Finset.subset_union_right
        have he := hor_empty hop _ hz hsub
        have haS : supp n D (opA D j) = S := by simpa [he] using hg.symm
        exact hearly _ ha haS

lemma first_support_gate_not_copyBoundary {n : ℕ} {α : Type} {D : Dag}
    (hS : Strict n D) (rows : α → Fin n → Bool)
    (I : Finset (Fin n)) (r : α) (hr : ∀ v, v ∉ I → rows r v = true)
    {j : ℕ} (hj : j < D.length) {S : Finset (Fin n)}
    (hcard : 2 ≤ S.card) (hdis : Disjoint S I)
    (hs : supp n D (n + j) = S)
    (hfirst : ∀ k < j, supp n D (n + k) ≠ S) :
    j ∉ copyBoundary n D (zeroWires D rows) := by
  obtain ⟨ha, hb⟩ := first_support_gate_no_zero_input hS rows I r hr hj hcard hdis hs hfirst
  intro hjb
  have hcase := (Finset.mem_filter.mp hjb).2
  rcases hcase with ⟨hza, _⟩ | ⟨hza | hzb, _⟩
  · exact ha hza
  · exact ha hza
  · exact hb hzb

end PEqualNP.Outside.L_meta_2590.EssentialPruning
