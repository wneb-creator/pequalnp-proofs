import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583_aux.SemanticFrontier

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

lemma prime_below {n : ℕ} (C : Circuit) (x : Fin n → Bool)
    (hx : circuitFun n C x = true) :
    ∃ S : Finset (Fin n), IsPrimeImplicant n C S ∧
      ∀ i ∈ S, x i = true := by
  classical
  let X : Finset (Fin n) := Finset.univ.filter fun i => x i = true
  have hX : setInput X = x := by
    funext i
    cases hi : x i <;> simp [setInput, X, hi]
  have hex : ∃ k : ℕ, ∃ S : Finset (Fin n),
      S ⊆ X ∧ circuitFun n C (setInput S) = true ∧ S.card = k :=
    ⟨X.card, X, Finset.Subset.refl _, by simpa [hX] using hx, rfl⟩
  obtain ⟨S, hSX, hS, hcard⟩ := Nat.find_spec hex
  refine ⟨S, ⟨hS, ?_⟩, ?_⟩
  · intro T hT
    have hproper : T ⊂ S := Finset.mem_ssubsets.mp hT
    by_contra hfalse
    have htrue : circuitFun n C (setInput T) = true := by
      cases h : circuitFun n C (setInput T) <;> simp_all
    have hmin : Nat.find hex ≤ T.card :=
      Nat.find_min' hex ⟨T, hproper.1.trans hSX, htrue, rfl⟩
    have hlt := Finset.card_lt_card hproper
    omega
  · intro i hi
    exact (Finset.mem_filter.mp (hSX hi)).2

lemma lower_agrees_on_primes {n : ℕ} (C : Circuit)
    (f : (Fin n → Bool) → Bool) (hmono : Monotone f)
    (hle : ∀ x, f x ≤ circuitFun n C x)
    (hprime : ∀ S, IsPrimeImplicant n C S → f (setInput S) = true) :
    f = circuitFun n C := by
  funext x
  apply le_antisymm (hle x)
  by_cases hx : circuitFun n C x = true
  · obtain ⟨S, hS, hsub⟩ := prime_below C x hx
    have hi : setInput S ≤ x := by
      intro i
      by_cases hmem : i ∈ S
      · simp [setInput, hmem, hsub i hmem]
      · simp [setInput, hmem]
    have h := hmono hi
    simpa only [hprime S hS, hx] using h
  · have hfalse : circuitFun n C x = false := by
      cases h : circuitFun n C x <;> simp_all
    rw [hfalse]
    exact bot_le

end PEqualNP.Outside.L_meta_2583_aux.SemanticFrontier

namespace PEqualNP.Outside.L_meta_2583_aux.SemanticFrontierDual

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

lemma maximal_false_above {n : ℕ} (C : Circuit) (x : Fin n → Bool)
    (hx : circuitFun n C x = false) :
    ∃ T : Finset (Fin n), x ≤ setInput T ∧
      circuitFun n C (setInput T) = false ∧
      ∀ U : Finset (Fin n), T ⊂ U → circuitFun n C (setInput U) = true := by
  classical
  let X : Finset (Fin n) := Finset.univ.filter fun i => x i = true
  have hX : setInput X = x := by
    funext i
    cases hi : x i <;> simp [setInput, X, hi]
  have hex : ∃ k : ℕ, ∃ T : Finset (Fin n),
      X ⊆ T ∧ circuitFun n C (setInput T) = false ∧ n - T.card = k :=
    ⟨n - X.card, X, Finset.Subset.refl _, by simpa [hX] using hx, rfl⟩
  obtain ⟨T, hXT, hT, hcard⟩ := Nat.find_spec hex
  refine ⟨T, ?_, hT, ?_⟩
  · intro i
    by_cases hi : x i = true
    · have hmem : i ∈ T := hXT (by simp [X, hi])
      simp [setInput, hmem, hi]
    · have hfalse : x i = false := by cases h : x i <;> simp_all
      simp [hfalse]
  · intro U hproper
    by_contra htrue
    have hfalse : circuitFun n C (setInput U) = false := by
      cases h : circuitFun n C (setInput U) <;> simp_all
    have hmin : Nat.find hex ≤ n - U.card :=
      Nat.find_min' hex ⟨U, hXT.trans hproper.1, hfalse, rfl⟩
    have hlt := Finset.card_lt_card hproper
    have hbound : U.card ≤ n := by simpa using Finset.card_le_univ U
    omega

lemma upper_agrees_on_maximal_false {n : ℕ} (C : Circuit)
    (f : (Fin n → Bool) → Bool) (hmono : Monotone f)
    (hle : ∀ x, circuitFun n C x ≤ f x)
    (hmax : ∀ T : Finset (Fin n), circuitFun n C (setInput T) = false →
      (∀ U : Finset (Fin n), T ⊂ U → circuitFun n C (setInput U) = true) →
      f (setInput T) = false) :
    f = circuitFun n C := by
  funext x
  apply le_antisymm ?_ (hle x)
  by_cases hx : circuitFun n C x = false
  · obtain ⟨T, hsub, hT, hU⟩ := maximal_false_above C x hx
    have h := hmono hsub
    simpa only [hmax T hT hU, hx] using h
  · have htrue : circuitFun n C x = true := by
      cases h : circuitFun n C x <;> simp_all
    rw [htrue]
    exact le_top

end PEqualNP.Outside.L_meta_2583_aux.SemanticFrontierDual

namespace PEqualNP.Outside.L_meta_2583_aux.ForcedGateSemantics

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

def forcedEval (n : ℕ) (pre post : List Gate) (b : Bool) (out : ℕ)
    (x : Fin n → Bool) : Bool :=
  (run post (run pre (List.ofFn x) ++ [b])).getD out false

lemma getD_le {xs ys : List Bool} (h : List.Forall₂ (· ≤ ·) xs ys) (i : ℕ) :
    xs.getD i false ≤ ys.getD i false := by
  induction h generalizing i with
  | nil => simp
  | cons hab h ih =>
    cases i with
    | zero => simpa using hab
    | succ i => simpa using ih i

lemma and_mono : ∀ a b c d : Bool, a ≤ b → c ≤ d →
    (a && c) ≤ (b && d) := by decide

lemma or_mono : ∀ a b c d : Bool, a ≤ b → c ≤ d →
    (a || c) ≤ (b || d) := by decide

lemma all_le {xs ys : List Bool} (h : List.Forall₂ (· ≤ ·) xs ys) :
    xs.all id ≤ ys.all id := by
  induction h with
  | nil => simp
  | cons hab h ih =>
    simpa only [List.all_cons, id_eq] using and_mono _ _ _ _ hab ih

lemma any_le {xs ys : List Bool} (h : List.Forall₂ (· ≤ ·) xs ys) :
    xs.any id ≤ ys.any id := by
  induction h with
  | nil => simp
  | cons hab h ih =>
    simpa only [List.any_cons, id_eq] using or_mono _ _ _ _ hab ih

lemma snoc_le {xs ys : List Bool} (h : List.Forall₂ (· ≤ ·) xs ys)
    {a b : Bool} (hab : a ≤ b) :
    List.Forall₂ (· ≤ ·) (xs ++ [a]) (ys ++ [b]) := by
  induction h with
  | nil => exact .cons hab .nil
  | cons hxy h ih => exact .cons hxy ih

lemma op_le (g : Gate) (hg : g.op = .and ∨ g.op = .or)
    {xs ys : List Bool} (h : List.Forall₂ (· ≤ ·) xs ys) :
    g.op.eval (g.inputs.map fun i => xs.getD i false) ≤
      g.op.eval (g.inputs.map fun i => ys.getD i false) := by
  have hm : List.Forall₂ (· ≤ ·) (g.inputs.map fun i => xs.getD i false)
      (g.inputs.map fun i => ys.getD i false) := by
    induction g.inputs with
    | nil => exact .nil
    | cons i is ih => exact .cons (getD_le h i) ih
  rcases hg with hg | hg
  · simpa [hg, GateOp.eval] using all_le hm
  · simpa [hg, GateOp.eval] using any_le hm

lemma step_le (g : Gate) (hg : g.op = .and ∨ g.op = .or)
    {xs ys : List Bool} (h : List.Forall₂ (· ≤ ·) xs ys) :
    List.Forall₂ (· ≤ ·) (step xs g) (step ys g) :=
  snoc_le h (op_le g hg h)

lemma run_le (gs : List Gate) (hk : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    {xs ys : List Bool} (h : List.Forall₂ (· ≤ ·) xs ys) :
    List.Forall₂ (· ≤ ·) (run gs xs) (run gs ys) := by
  induction gs generalizing xs ys with
  | nil => exact h
  | cons g gs ih =>
    exact ih (fun g' hg' => hk g' (by simp [hg']))
      (step_le g (hk g (by simp)) h)

lemma ofFn_le {n : ℕ} (x y : Fin n → Bool) (h : x ≤ y) :
    List.Forall₂ (· ≤ ·) (List.ofFn x) (List.ofFn y) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ]
    exact .cons (h 0) (ih _ _ (fun i => h i.succ))

lemma forced_monotone (n : ℕ) (pre post : List Gate) (b : Bool) (out : ℕ)
    (hp : ∀ g ∈ pre, g.op = .and ∨ g.op = .or)
    (hs : ∀ g ∈ post, g.op = .and ∨ g.op = .or) :
    Monotone (forcedEval n pre post b out) := by
  intro x y hxy
  exact getD_le (run_le post hs
    (snoc_le (run_le pre hp (ofFn_le x y hxy)) le_rfl)) out

lemma forced_agrees (n : ℕ) (pre post : List Gate) (g : Gate) (b : Bool)
    (out : ℕ) (x : Fin n → Bool)
    (hv : g.op.eval (g.inputs.map fun i =>
      (run pre (List.ofFn x)).getD i false) = b) :
    forcedEval n pre post b out x =
      circuitFun n ⟨pre ++ g :: post, out⟩ x := by
  simp only [forcedEval, circuitFun, Circuit.eval, Circuit.wires,
    List.foldl_append, List.foldl_cons]
  change _ = (run post (step (run pre (List.ofFn x)) g)).getD out false
  rw [step, hv]

lemma forced_false_le (n : ℕ) (pre post : List Gate) (g : Gate) (out : ℕ)
    (hs : ∀ g' ∈ post, g'.op = .and ∨ g'.op = .or)
    (x : Fin n → Bool) :
    forcedEval n pre post false out x ≤
      circuitFun n ⟨pre ++ g :: post, out⟩ x := by
  have hsame : List.Forall₂ (· ≤ ·) (run pre (List.ofFn x))
      (run pre (List.ofFn x)) := List.forall₂_refl _
  have h := getD_le (run_le post hs (snoc_le hsame
    (show false ≤ g.op.eval (g.inputs.map fun i =>
      (run pre (List.ofFn x)).getD i false) from bot_le))) out
  simp only [circuitFun, Circuit.eval, Circuit.wires, List.foldl_append, List.foldl_cons]
  change _ ≤ (run post (step (run pre (List.ofFn x)) g)).getD out false
  exact h

lemma le_forced_true (n : ℕ) (pre post : List Gate) (g : Gate) (out : ℕ)
    (hs : ∀ g' ∈ post, g'.op = .and ∨ g'.op = .or)
    (x : Fin n → Bool) :
    circuitFun n ⟨pre ++ g :: post, out⟩ x ≤
      forcedEval n pre post true out x := by
  have hsame : List.Forall₂ (· ≤ ·) (run pre (List.ofFn x))
      (run pre (List.ofFn x)) := List.forall₂_refl _
  have h := getD_le (run_le post hs (snoc_le hsame
    (show g.op.eval (g.inputs.map fun i =>
      (run pre (List.ofFn x)).getD i false) ≤ true from le_top))) out
  simp only [circuitFun, Circuit.eval, Circuit.wires, List.foldl_append, List.foldl_cons]
  change (run post (step (run pre (List.ofFn x)) g)).getD out false ≤ _
  exact h

end PEqualNP.Outside.L_meta_2583_aux.ForcedGateSemantics

namespace PEqualNP.Outside.L_meta_2583_aux.GatePruningSemantics

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK
open PEqualNP.Outside.L_meta_2583_aux.ForcedGateSemantics

lemma force_false_preserves (n : ℕ) (pre post : List Gate) (g : Gate) (out : ℕ)
    (hp : ∀ g' ∈ pre, g'.op = .and ∨ g'.op = .or)
    (hs : ∀ g' ∈ post, g'.op = .and ∨ g'.op = .or)
    (hzero : ∀ S : Finset (Fin n),
      IsPrimeImplicant n ⟨pre ++ g :: post, out⟩ S →
      g.op.eval (g.inputs.map fun i =>
        (run pre (List.ofFn (setInput S))).getD i false) = false) :
    forcedEval n pre post false out =
      circuitFun n ⟨pre ++ g :: post, out⟩ := by
  refine SemanticFrontier.lower_agrees_on_primes _ _
    (forced_monotone n pre post false out hp hs)
    (forced_false_le n pre post g out hs) ?_
  intro S hS
  rw [forced_agrees n pre post g false out (setInput S) (hzero S hS)]
  exact hS.1

lemma force_true_preserves (n : ℕ) (pre post : List Gate) (g : Gate) (out : ℕ)
    (hp : ∀ g' ∈ pre, g'.op = .and ∨ g'.op = .or)
    (hs : ∀ g' ∈ post, g'.op = .and ∨ g'.op = .or)
    (hone : ∀ T : Finset (Fin n),
      circuitFun n ⟨pre ++ g :: post, out⟩ (setInput T) = false →
      (∀ U : Finset (Fin n), T ⊂ U →
        circuitFun n ⟨pre ++ g :: post, out⟩ (setInput U) = true) →
      g.op.eval (g.inputs.map fun i =>
        (run pre (List.ofFn (setInput T))).getD i false) = true) :
    forcedEval n pre post true out =
      circuitFun n ⟨pre ++ g :: post, out⟩ := by
  refine SemanticFrontierDual.upper_agrees_on_maximal_false _ _
    (forced_monotone n pre post true out hp hs)
    (le_forced_true n pre post g out hs) ?_
  intro T hT hmax
  rw [forced_agrees n pre post g true out (setInput T) (hone T hT hmax)]
  exact hT

lemma force_false_sensitive (n : ℕ) (pre post : List Gate) (g : Gate) (out : ℕ)
    (hp : ∀ g' ∈ pre, g'.op = .and ∨ g'.op = .or)
    (hs : ∀ g' ∈ post, g'.op = .and ∨ g'.op = .or)
    (hne : forcedEval n pre post false out ≠
      circuitFun n ⟨pre ++ g :: post, out⟩) :
    ∃ S : Finset (Fin n), IsPrimeImplicant n ⟨pre ++ g :: post, out⟩ S ∧
      forcedEval n pre post false out (setInput S) = false := by
  classical
  by_contra h
  push_neg at h
  apply hne
  refine SemanticFrontier.lower_agrees_on_primes _ _
    (forced_monotone n pre post false out hp hs)
    (forced_false_le n pre post g out hs) ?_
  intro S hS
  have hne' := h S hS
  cases he : forcedEval n pre post false out (setInput S) <;> simp_all

lemma force_true_sensitive (n : ℕ) (pre post : List Gate) (g : Gate) (out : ℕ)
    (hp : ∀ g' ∈ pre, g'.op = .and ∨ g'.op = .or)
    (hs : ∀ g' ∈ post, g'.op = .and ∨ g'.op = .or)
    (hne : forcedEval n pre post true out ≠
      circuitFun n ⟨pre ++ g :: post, out⟩) :
    ∃ T : Finset (Fin n),
      circuitFun n ⟨pre ++ g :: post, out⟩ (setInput T) = false ∧
      (∀ U : Finset (Fin n), T ⊂ U →
        circuitFun n ⟨pre ++ g :: post, out⟩ (setInput U) = true) ∧
      forcedEval n pre post true out (setInput T) = true := by
  classical
  by_contra h
  push_neg at h
  apply hne
  refine SemanticFrontierDual.upper_agrees_on_maximal_false _ _
    (forced_monotone n pre post true out hp hs)
    (le_forced_true n pre post g out hs) ?_
  intro T hT hmax
  have hne' := h T hT hmax
  cases he : forcedEval n pre post true out (setInput T) <;> simp_all

end PEqualNP.Outside.L_meta_2583_aux.GatePruningSemantics
