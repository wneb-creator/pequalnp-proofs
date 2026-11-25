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

end PEqualNP.Outside.L_meta_2590.EssentialPruning
