import Compression

namespace PEqualNP.Outside.L_meta_2592_aux.SharedSecondReader

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_2592_aux.FirstMerge
open PEqualNP.Outside.L_meta_2592_aux.FirstOrigin
open PEqualNP.Outside.L_meta_2592_aux.Restriction
open PEqualNP.Outside.L_meta_2592_aux.Compression

def ThreeInFiber (code : Bool → Bool → Bool) : Prop :=
  ∃ a b c : Bool × Bool, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
    code a.1 a.2 = code b.1 b.2 ∧ code a.1 a.2 = code c.1 c.2

lemma signed_and_or_fiber : ∀ join sa sb : Bool,
    ThreeInFiber (fun a b => if join then (a != sa) || (b != sb)
      else (a != sa) && (b != sb)) := by
  unfold ThreeInFiber
  decide

lemma no_pair_two_codes (u v : Fin 10) (hne : u ≠ v)
    (first second : Bool → Bool → Bool) (fiber : ThreeInFiber first) :
    ∃ a b : Fin 10 → Bool,
      (∀ i, i ≠ u → i ≠ v → a i = b i) ∧
      first (a u) (a v) = first (b u) (b v) ∧
      second (a u) (a v) = second (b u) (b v) ∧ petersen a ≠ petersen b := by
  by_contra! hf
  have depends (w : Fin 10) (a b : Bool × Bool)
      (sameFirst : first a.1 a.2 = first b.1 b.2)
      (sameSecond : second a.1 a.2 = second b.1 b.2) :
      petersen (probe u v w a.1 a.2) = petersen (probe u v w b.1 b.2) := by
    apply hf (probe u v w a.1 a.2) (probe u v w b.1 b.2)
    · intro i hi hj
      simp [probe, hi, hj]
    · simpa [probe, hne.symm] using sameFirst
    · simpa [probe, hne.symm] using sameSecond
  obtain ⟨p, hp⟩ := left_probe u v hne
  obtain ⟨q, hq⟩ := right_probe u v hne
  have inject (a b : Bool × Bool)
      (sameFirst : first a.1 a.2 = first b.1 b.2)
      (sameSecond : second a.1 a.2 = second b.1 b.2) : a = b := by
    apply Prod.ext
    · simpa only [hp] using depends p a b sameFirst sameSecond
    · simpa only [hq] using depends q a b sameFirst sameSecond
  obtain ⟨a, b, c, hab, hac, hbc, fab, fac⟩ := fiber
  have ab : second a.1 a.2 ≠ second b.1 b.2 := fun same => hab (inject a b fab same)
  have ac : second a.1 a.2 ≠ second c.1 c.2 := fun same => hac (inject a c fac same)
  have bc : second b.1 b.2 ≠ second c.1 c.2 :=
    fun same => hbc (inject b c (fab.symm.trans fac) same)
  have pigeonhole : ∀ a b c : Bool, a ≠ b → a ≠ c → b ≠ c → False := by decide
  exact pigeonhole _ _ _ ab ac bc

lemma two_charged_gaps (origins : List (Option ℕ)) (v : ℕ)
    (pre mid post : List Gate) (g h : Gate)
    (budget : cutCost origins v (pre ++ g :: (mid ++ h :: post)) ≤ 2)
    (first : cutCharge (pre.foldl originStep origins) v g = 1)
    (second : cutCharge ((pre ++ g :: mid).foldl originStep origins) v h = 1) :
    cutCost origins v pre = 0 ∧
    cutCost (originStep (pre.foldl originStep origins) g) v mid = 0 ∧
    cutCost (originStep (mid.foldl originStep (originStep (pre.foldl originStep origins) g)) h)
      v post = 0 := by
  simp only [List.foldl_append, List.foldl_cons] at second
  rw [cutCost_append] at budget
  simp only [cutCost, first] at budget
  rw [cutCost_append] at budget
  simp only [cutCost, second] at budget
  omega

lemma agree_binary_step (origins : List (Option ℕ)) (u v : ℕ)
    (a b : List Bool) (g : Gate) (flag : isNotGate g.op = false)
    (agree : AgreeOutside origins u v a b)
    (same : g.op.eval (g.inputs.map fun i => a.getD i false) =
      g.op.eval (g.inputs.map fun i => b.getD i false)) :
    AgreeOutside (originStep origins g) u v (gateStep a g) (gateStep b g) := by
  have none : gateOrigin origins g = none := by
    cases op : g.op <;> simp [gateOrigin, op]
    simp [isNotGate, op] at flag
  simpa only [originStep, none, gateStep] using agree_snoc origins u v a b _ _ agree same

theorem no_shared_second_reader (C : Circuit) (pre mid post : List Gate) (g h : Gate)
    (split : C.gates = pre ++ g :: (mid ++ h :: post))
    (gFlag : isNotGate g.op = false) (hFlag : isNotGate h.op = false)
    (u v : Fin 10) (hne : u ≠ v) (first second : Bool → Bool → Bool)
    (fiber : ThreeInFiber first)
    (firstFactor : ∀ x : Fin 10 → Bool,
      g.op.eval (g.inputs.map fun i => (pre.foldl gateStep (List.ofFn x)).getD i false) =
        first (x u) (x v))
    (secondFactor : ∀ x : Fin 10 → Bool,
      h.op.eval (h.inputs.map fun i => ((pre ++ g :: mid).foldl gateStep (List.ofFn x)).getD i false) =
        second (x u) (x v))
    (gReadU : readsOrigin (pre.foldl originStep (List.ofFn fun i : Fin 10 => some i.val)) u.val g = true)
    (gReadV : readsOrigin (pre.foldl originStep (List.ofFn fun i : Fin 10 => some i.val)) v.val g = true)
    (hReadU : readsOrigin ((pre ++ g :: mid).foldl originStep
      (List.ofFn fun i : Fin 10 => some i.val)) u.val h = true)
    (hReadV : readsOrigin ((pre ++ g :: mid).foldl originStep
      (List.ofFn fun i : Fin 10 => some i.val)) v.val h = true)
    (costU : cutCost (List.ofFn fun i : Fin 10 => some i.val) u.val C.gates ≤ 2)
    (costV : cutCost (List.ofFn fun i : Fin 10 => some i.val) v.val C.gates ≤ 2)
    (correct : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersen x) : False := by
  obtain ⟨a, b, initial, firstSame, secondSame, different⟩ :=
    no_pair_two_codes u v hne first second fiber
  let origins := List.ofFn fun i : Fin 10 => some i.val
  have gapsU := two_charged_gaps origins u.val pre mid post g h
    (by dsimp only [origins]; rw [← split]; exact costU)
    (by simp only [origins, cutCharge, gFlag, gReadU, Bool.false_eq_true, Bool.true_eq, ↓reduceIte])
    (by simp only [origins, cutCharge, hFlag, hReadU, Bool.false_eq_true, Bool.true_eq, ↓reduceIte])
  have gapsV := two_charged_gaps origins v.val pre mid post g h
    (by dsimp only [origins]; rw [← split]; exact costV)
    (by simp only [origins, cutCharge, gFlag, gReadV, Bool.false_eq_true, Bool.true_eq, ↓reduceIte])
    (by simp only [origins, cutCharge, hFlag, hReadV, Bool.false_eq_true, Bool.true_eq, ↓reduceIte])
  have preAgree := agree_tail origins u.val v.val (List.ofFn a) (List.ofFn b) pre
    (agreeOutside_initial 10 u v a b initial) gapsU.1 gapsV.1
  have firstEqual : g.op.eval (g.inputs.map fun i => (pre.foldl gateStep (List.ofFn a)).getD i false) =
      g.op.eval (g.inputs.map fun i => (pre.foldl gateStep (List.ofFn b)).getD i false) := by
    rw [firstFactor, firstFactor, firstSame]
  have firstAgree := agree_binary_step _ u.val v.val _ _ g gFlag preAgree firstEqual
  have midAgree := agree_tail _ u.val v.val _ _ mid firstAgree gapsU.2.1 gapsV.2.1
  have secondEqual : h.op.eval (h.inputs.map fun i =>
      (mid.foldl gateStep (gateStep (pre.foldl gateStep (List.ofFn a)) g)).getD i false) =
      h.op.eval (h.inputs.map fun i =>
      (mid.foldl gateStep (gateStep (pre.foldl gateStep (List.ofFn b)) g)).getD i false) := by
    have eq : h.op.eval (h.inputs.map fun i =>
        ((pre ++ g :: mid).foldl gateStep (List.ofFn a)).getD i false) =
        h.op.eval (h.inputs.map fun i =>
        ((pre ++ g :: mid).foldl gateStep (List.ofFn b)).getD i false) := by
      rw [secondFactor, secondFactor, secondSame]
    simpa only [List.foldl_append, List.foldl_cons] using eq
  have secondAgree := agree_binary_step _ u.val v.val _ _ h hFlag midAgree secondEqual
  have final := agree_tail _ u.val v.val _ _ post secondAgree gapsU.2.2 gapsV.2.2
  have originsFull : C.gates.foldl originStep origins =
      post.foldl originStep (originStep (mid.foldl originStep
        (originStep (pre.foldl originStep origins) g)) h) := by
    rw [split, List.foldl_append, List.foldl_cons, List.foldl_append, List.foldl_cons]
  have wiresFull (x : Fin 10 → Bool) : C.wires (List.ofFn x) =
      post.foldl gateStep (gateStep (mid.foldl gateStep
        (gateStep (pre.foldl gateStep (List.ofFn x)) g)) h) := by
    change C.gates.foldl gateStep (List.ofFn x) = _
    rw [split, List.foldl_append, List.foldl_cons, List.foldl_append, List.foldl_cons]
  rw [← originsFull, ← wiresFull a, ← wiresFull b] at final
  have outNone := output_origin_none C correct
  have eq := final.2.2 C.output (by rw [outNone]; simp) (by rw [outNone]; simp)
  change C.eval (List.ofFn a) = C.eval (List.ofFn b) at eq
  rw [correct, correct] at eq
  exact different eq

end PEqualNP.Outside.L_meta_2592_aux.SharedSecondReader
