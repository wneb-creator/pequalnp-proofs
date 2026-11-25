import PEqualNP.Defs

open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_1904_941 :
  (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
  (∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a) →
  (∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) →
  ∀ (pre post : List PEqualNP.CircuitLowerBounds.Gate)
    (g : PEqualNP.CircuitLowerBounds.Gate) (out : ℕ),
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨pre ++ g :: post, out⟩
  let Z : PEqualNP.CircuitLowerBounds.Circuit := ⟨pre ++ ⟨.or, []⟩ :: post, out⟩
  let F := PEqualNP.MetaComplexity.NestedCover.graphFun G ∅
  let J := PEqualNP.TopForm.junk G
  let E := fun a b : Fin n => G.Adj a b ∧
    PEqualNP.MetaComplexity.circuitFun n Z (PEqualNP.EdgeOwnership.pairInput a b) = false
  PEqualNP.MetaComplexity.IsMinimalMonoCircuit n C →
  PEqualNP.MetaComplexity.circuitFun n C = F →
  pre.length ∈ J C → (∀ i ∈ J C, pre.length ≤ i) →
  (∃ c u v, u ≠ v ∧ E c u ∧ E c v ∧ ∀ a b, E a b → a = c ∨ b = c) →
  ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.circuitFun n D = F ∧
    D.size ≤ C.size ∧ (J D).card < (J C).card) →
  (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
  (∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a) →
  (∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) →
  ∀ (pre post : List PEqualNP.CircuitLowerBounds.Gate)
    (g : PEqualNP.CircuitLowerBounds.Gate) (out : ℕ),
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨pre ++ g :: post, out⟩
  let Z : PEqualNP.CircuitLowerBounds.Circuit := ⟨pre ++ ⟨.or, []⟩ :: post, out⟩
  let F := PEqualNP.MetaComplexity.NestedCover.graphFun G ∅
  let J := PEqualNP.TopForm.junk G
  let E := fun a b : Fin n => G.Adj a b ∧
    PEqualNP.MetaComplexity.circuitFun n Z (PEqualNP.EdgeOwnership.pairInput a b) = false
  PEqualNP.MetaComplexity.IsMinimalMonoCircuit n C →
  PEqualNP.MetaComplexity.circuitFun n C = F →
  pre.length ∈ J C → (∀ i ∈ J C, pre.length ≤ i) →
  (∃ a b c d, E a b ∧ E c d ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d) →
  ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.circuitFun n D = F ∧
    D.size ≤ C.size ∧ (J D).card < (J C).card) →
  ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj], (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) → (∀ (x5 x6 x7 x8 : Fin x1), x2.Adj x5 x6 → x2.Adj x6 x7 → x2.Adj x7 x8 → x2.Adj x8 x5 → x5 = x7 ∨ x6 = x8) → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 ∧ (∀ (x7 : Fin x1 → Bool), x6.eval (List.ofFn x7) = Decidable.decide (∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9 ∧ x7 x8 = Bool.true ∧ x7 x9 = Bool.true)) ∧ (∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → (∀ (x9 : Fin x1 → Bool), x7.eval (List.ofFn x9) = Decidable.decide (∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11 ∧ x9 x10 = Bool.true ∧ x9 x11 = Bool.true)) → x6.size ≤ x7.size) ∧ ∀ (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate), x6.gates[x7]? = Option.some x8 → x8.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x11 : Fin x1 → Bool), (x6.wires (List.ofFn x11)).getD (x1 + x7) Bool.false = Bool.true → ∃ (x13 : Fin x1) (x14 : Fin x1), x2.Adj x13 x14 ∧ x11 x13 = Bool.true ∧ x11 x14 = Bool.true := by
  intro star_child disjoint_child
  classical
  have gateAndEq (xs : List Bool) : GateOp.and.eval xs = xs.all id := rfl
  have gateOrEq (xs : List Bool) : GateOp.or.eval xs = xs.any id := rfl
  have circuitWiresEq (C : Circuit) (x : List Bool) : C.wires x =
      C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x := rfl
  have circuitEvalEq (C : Circuit) (x : List Bool) :
      C.eval x = (C.wires x).getD C.output false := rfl
  have circuitSizeEq (C : Circuit) : C.size = C.gates.length := rfl
  have pairInputEq {n : Nat} (u v : Fin n) :
      PEqualNP.EdgeOwnership.pairInput u v = fun w => decide (w = u ∨ w = v) := rfl
  have circuitFunEq (n : Nat) (C : Circuit) :
      circuitFun n C = fun x => C.eval (List.ofFn x) := rfl
  have gateAtEq (C : Circuit) (j : Nat) :
      gateAt C j = C.gates.getD j ⟨GateOp.or, []⟩ := rfl
  have graphFunEq {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (A : Finset (Fin n)) : graphFun G A = fun x =>
        decide (∃ a ∈ A, x a = true) ||
          decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) := rfl
  have monotoneEq (C : Circuit) : Monotone2 C ↔
      ∀ g ∈ C.gates, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧
        g.inputs.length ≤ 2 := Iff.rfl
  have exists_minimizer {α : Type} (P : α → Prop) (measure : α → ℕ)
      (hex : ∃ a, P a) : ∃ a, P a ∧ ∀ b, P b → measure a ≤ measure b := by
    classical
    have h : ∃ k, ∃ a, P a ∧ measure a = k := by
      obtain ⟨a, ha⟩ := hex
      exact ⟨measure a, a, ha, rfl⟩
    obtain ⟨a, ha, hm⟩ := Nat.find_spec h
    refine ⟨a, ha, ?_⟩
    intro b hb
    rw [hm]
    exact Nat.find_min' h ⟨b, hb, rfl⟩

  let Correct {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit) : Prop :=
    Monotone2 C ∧ ∀ x : Fin n → Bool,
      C.eval (List.ofFn x) = decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)

  let dirtySet {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit) : Finset ℕ := by
    classical
    exact (Finset.range C.size).filter (PEqualNP.CleanedNonEdge.IsDirtyAnd n G C)

  have exists_extremal {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (hex : ∃ C, Correct G C) :
      ∃ C, Correct G C ∧
        (∀ D, Correct G D → C.size ≤ D.size) ∧
        ∀ D, Correct G D → D.size ≤ C.size →
          (dirtySet G C).card ≤ (dirtySet G D).card := by
    classical
    obtain ⟨C, hC, hmin⟩ := exists_minimizer (Correct G) Circuit.size hex
    obtain ⟨D, ⟨hD, hsize⟩, hdirty⟩ := exists_minimizer
      (fun D => Correct G D ∧ D.size ≤ C.size)
      (fun D => (dirtySet G D).card) ⟨C, hC, le_rfl⟩
    refine ⟨D, hD, fun E hE => hsize.trans (hmin E hE), ?_⟩
    intro E hE hED
    exact hdirty E ⟨hE, hED.trans hsize⟩

  let Repair_step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  let Repair_run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl Repair_step w

  let Repair_WireLE (v w : List Bool) : Prop :=
    ∀ i, v.getD i false = true → w.getD i false = true

  have Repair_run_length (gs : List Gate) (w : List Bool) :
      (Repair_run gs w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp [Repair_run]
    | cons g gs ih =>
      change (Repair_run gs (Repair_step w g)).length = _
      rw [ih]
      simp [Repair_step]
      omega

  have Repair_append_bit_le {v w : List Bool} (hlen : v.length = w.length)
      (hle : Repair_WireLE v w) {a b : Bool} (hab : a = true → b = true) :
      Repair_WireLE (v ++ [a]) (w ++ [b]) := by
    intro i hi
    by_cases hlt : i < v.length
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt] at hi
      have hlt' : i < w.length := hlen ▸ hlt
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt']
      exact hle i hi
    · have hv : v.length ≤ i := by omega
      have hw : w.length ≤ i := by omega
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hv] at hi
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hw]
      rw [← hlen]
      cases hidx : i - v.length with
      | zero => simpa [hidx] using hab (by simpa [hidx] using hi)
      | succ k => simp [hidx] at hi

  have Repair_gate_eval_le (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
      {v w : List Bool} (hle : Repair_WireLE v w) :
      g.op.eval (g.inputs.map fun i => v.getD i false) = true →
        g.op.eval (g.inputs.map fun i => w.getD i false) = true := by
    rcases hop with hop | hop
    · rw [hop]
      simp only [gateAndEq, gateOrEq, List.all_eq_true, List.mem_map, forall_exists_index,
        and_imp, forall_apply_eq_imp_iff₂]
      intro hv i hi
      exact hle i (hv i hi)
    · rw [hop]
      simp only [gateAndEq, gateOrEq, List.any_eq_true, List.mem_map]
      rintro ⟨b, ⟨i, hi, rfl⟩, hb⟩
      exact ⟨w.getD i false, ⟨i, hi, rfl⟩, hle i hb⟩

  have Repair_run_le (gs : List Gate)
      (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
      {v w : List Bool} (hlen : v.length = w.length) (hle : Repair_WireLE v w) :
      Repair_WireLE (Repair_run gs v) (Repair_run gs w) := by
    induction gs generalizing v w with
    | nil => exact hle
    | cons g gs ih =>
      apply ih (fun g hg => hmono g (List.mem_cons_of_mem _ hg))
      · simp [Repair_step, hlen]
      · exact Repair_append_bit_le hlen hle (Repair_gate_eval_le g (hmono g (by simp)) hle)

  have Repair_ofFn_le {n : ℕ} {x y : Fin n → Bool}
      (hxy : ∀ i, x i = true → y i = true) : Repair_WireLE (List.ofFn x) (List.ofFn y) := by
    intro i hi
    by_cases hin : i < n
    · simpa [List.getD_eq_getElem?_getD, hin] using hxy ⟨i, hin⟩
        (by simpa [List.getD_eq_getElem?_getD, hin] using hi)
    · simp [List.getD_eq_getElem?_getD, hin] at hi

  have Repair_patch_le (pre post : List Gate) (g h : Gate) (out : ℕ) (x : List Bool)
      (hpost : ∀ q ∈ post, q.op = GateOp.and ∨ q.op = GateOp.or)
      (hgate : h.op.eval (h.inputs.map fun i => (Repair_run pre x).getD i false) = true →
        g.op.eval (g.inputs.map fun i => (Repair_run pre x).getD i false) = true) :
      Repair_WireLE (({gates := pre ++ h :: post, output := out} : Circuit).wires x)
        (({gates := pre ++ g :: post, output := out} : Circuit).wires x) := by
    change Repair_WireLE (Repair_run (pre ++ h :: post) x) (Repair_run (pre ++ g :: post) x)
    simp only [Repair_run, List.foldl_append, List.foldl_cons]
    apply Repair_run_le post hpost
    · simp [Repair_step]
    · exact Repair_append_bit_le rfl (fun _ hi => hi) hgate

  let Repair_hit {n} (G : SimpleGraph (Fin n)) (x : Fin n → Bool) :=
    ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true

  let Repair_mask {n} (S : Finset (Fin n)) (u : Fin n) := decide (u ∈ S)

  have Repair_zero_critical_replacement {n : ℕ} (G : SimpleGraph (Fin n))
      (gate : (Fin n → Bool) → Bool)
      (tail : (Fin n → Bool) → Bool → Bool)
      (mono : ∀ x y : Fin n → Bool, ∀ p q : Bool,
        (∀ i, x i = true → y i = true) → (p = true → q = true) →
        tail x p = true → tail y q = true)
      (correct : ∀ x, tail x (gate x) = true ↔ Repair_hit G x)
      (survives : ∀ u v, G.Adj u v → tail (Repair_mask {u,v}) false = true) :
      ∀ x, tail x false = true ↔ Repair_hit G x := by
    intro x
    constructor
    · intro h
      exact (correct x).mp (mono x x false (gate x) (fun _ h => h)
        (by simp) h)
    · rintro ⟨u,v,uv,hu,hv⟩
      apply mono (Repair_mask {u,v}) x false false ?_ (fun h => h) (survives u v uv)
      intro i hi
      simp only [Repair_mask, decide_eq_true_eq, Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · exact hu
      · exact hv

  have Repair_single_critical_replacement {n : ℕ} (G : SimpleGraph (Fin n))
      (gate : (Fin n → Bool) → Bool)
      (tail : (Fin n → Bool) → Bool → Bool)
      (gate_mono : ∀ x y : Fin n → Bool,
        (∀ i, x i = true → y i = true) → gate x = true → gate y = true)
      (tail_mono : ∀ x y : Fin n → Bool, ∀ p q : Bool,
        (∀ i, x i = true → y i = true) → (p = true → q = true) →
        tail x p = true → tail y q = true)
      (correct : ∀ x, tail x (gate x) = true ↔ Repair_hit G x)
      (a b : Fin n) (edge : G.Adj a b)
      (essential : tail (Repair_mask {a,b}) false = false)
      (unique : ∀ u v, G.Adj u v → tail (Repair_mask {u,v}) false = false →
        (u = a ∧ v = b) ∨ (u = b ∧ v = a)) :
      (∀ x, (x a && x b) = true → gate x = true) ∧
      (∀ x, tail x (x a && x b) = true ↔ Repair_hit G x) := by
    have pair_on : gate (Repair_mask {a,b}) = true := by
      have yes := (correct (Repair_mask {a,b})).mpr
        ⟨a,b,edge,by simp [Repair_mask],by simp [Repair_mask]⟩
      cases h : gate (Repair_mask {a,b})
      · rw [h,essential] at yes
        contradiction
      · rfl
    have dominated : ∀ x, (x a && x b) = true → gate x = true := by
      intro x hx
      obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp hx
      apply gate_mono (Repair_mask {a,b}) x ?_ pair_on
      intro i hi
      simp only [Repair_mask, decide_eq_true_eq, Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · exact ha
      · exact hb
    refine ⟨dominated,?_⟩
    intro x
    constructor
    · intro h
      exact (correct x).mp (tail_mono x x (x a && x b) (gate x)
        (fun _ h => h) (dominated x) h)
    · rintro ⟨u,v,uv,hu,hv⟩
      have sub : ∀ i, Repair_mask {u,v} i = true → x i = true := by
        intro i hi
        simp only [Repair_mask, decide_eq_true_eq, Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with rfl | rfl
        · exact hu
        · exact hv
      cases survive : tail (Repair_mask {u,v}) false with
      | true =>
        exact tail_mono (Repair_mask {u,v}) x false (x a && x b) sub (by simp) survive
      | false =>
        have active : (x a && x b) = true := by
          rcases unique u v uv survive with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [hu,hv]
        have yes := (correct (Repair_mask {u,v})).mpr
          ⟨u,v,uv,by simp [Repair_mask],by simp [Repair_mask]⟩
        exact tail_mono (Repair_mask {u,v}) x (gate (Repair_mask {u,v})) (x a && x b)
          sub (fun _ => active) yes

  let Repair_patchCircuit (pre post : List Gate) (g : Gate) (out : ℕ) : Circuit :=
    ⟨pre ++ g :: post, out⟩

  let Repair_gatePrefix {n : ℕ} (pre : List Gate) (g : Gate) (x : Fin n → Bool) : Bool :=
    g.op.eval (g.inputs.map fun i => (Repair_run pre (List.ofFn x)).getD i false)

  let Repair_gateContext {n : ℕ} (pre post : List Gate) (out : ℕ)
      (x : Fin n → Bool) (p : Bool) : Bool :=
    (Repair_run post (Repair_run pre (List.ofFn x) ++ [p])).getD out false

  have Repair_run_old_read (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (Repair_run gs w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      change (Repair_run gs (Repair_step w g)).getD i false = _
      rw [ih _ (by simp [Repair_step]; omega)]
      exact List.getD_append _ _ _ _ hi

  have Repair_run_input {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : Fin n) :
      (Repair_run gs (List.ofFn x)).getD i false = x i := by
    rw [Repair_run_old_read gs _ _ (by simp)]
    simp [List.getD_eq_getElem?_getD]

  have Repair_gateContext_orig {n : ℕ} (pre post : List Gate) (g : Gate) (out : ℕ)
      (x : Fin n → Bool) :
      Repair_gateContext pre post out x (Repair_gatePrefix pre g x) =
        (Repair_patchCircuit pre post g out).eval (List.ofFn x) := by
    simp only [Repair_gateContext,Repair_gatePrefix,Repair_patchCircuit,circuitEvalEq,circuitWiresEq,
      Repair_run,List.foldl_append,List.foldl_cons]
    rfl

  have Repair_gateContext_zero {n : ℕ} (pre post : List Gate) (out : ℕ)
      (x : Fin n → Bool) :
      Repair_gateContext pre post out x false =
        (Repair_patchCircuit pre post ⟨.or,[]⟩ out).eval (List.ofFn x) := by
    exact Repair_gateContext_orig pre post ⟨.or,[]⟩ out x

  have Repair_gatePrefix_edge {n : ℕ} (pre : List Gate) (a b : Fin n) (x : Fin n → Bool) :
      Repair_gatePrefix pre ⟨.and,[a.val,b.val]⟩ x = (x a && x b) := by
    simp only [Repair_gatePrefix,gateAndEq, gateOrEq,List.map_cons,List.map_nil,List.all_cons,
      List.all_nil,id_eq,Bool.and_true]
    rw [Repair_run_input pre x a,Repair_run_input pre x b]

  have Repair_gateContext_edge {n : ℕ} (pre post : List Gate) (out : ℕ) (a b : Fin n)
      (x : Fin n → Bool) :
      Repair_gateContext pre post out x (x a && x b) =
        (Repair_patchCircuit pre post ⟨.and,[a.val,b.val]⟩ out).eval (List.ofFn x) := by
    rw [←Repair_gatePrefix_edge pre a b x]
    exact Repair_gateContext_orig pre post ⟨.and,[a.val,b.val]⟩ out x

  have Repair_gateContext_mono {n : ℕ} (pre post : List Gate) (out : ℕ)
      (hpre : ∀ g ∈ pre, g.op = GateOp.and ∨ g.op = GateOp.or)
      (hpost : ∀ g ∈ post, g.op = GateOp.and ∨ g.op = GateOp.or)
      (x y : Fin n → Bool) (p q : Bool)
      (hxy : ∀ i, x i = true → y i = true) (hpq : p = true → q = true) :
      Repair_gateContext pre post out x p = true → Repair_gateContext pre post out y q = true := by
    apply Repair_run_le post hpost (by simp [Repair_run_length]) _ out
    exact Repair_append_bit_le (by simp [Repair_run_length])
      (Repair_run_le pre hpre (by simp) (Repair_ofFn_le hxy)) hpq

  have Repair_gatePrefix_mono {n : ℕ} (pre : List Gate) (g : Gate)
      (hpre : ∀ g ∈ pre, g.op = GateOp.and ∨ g.op = GateOp.or)
      (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
      (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true) :
      Repair_gatePrefix pre g x = true → Repair_gatePrefix pre g y = true := by
    exact Repair_gate_eval_le g hg (Repair_run_le pre hpre (by simp) (Repair_ofFn_le hxy))

  have Repair_patch_mono (pre post : List Gate) (g h : Gate) (out : ℕ)
      (hc : Monotone2 (Repair_patchCircuit pre post g out))
      (hh : (h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2) :
      Monotone2 (Repair_patchCircuit pre post h out) := by
    intro q hq
    change q ∈ pre ++ h :: post at hq
    rcases List.mem_append.mp hq with hp | hpost
    · exact hc q (List.mem_append_left _ hp)
    · rcases List.mem_cons.mp hpost with rfl | ht
      · exact hh
      · exact hc q (List.mem_append_right _ (List.mem_cons_of_mem _ ht))

  have Repair_single_edge_circuit_repair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (pre post : List Gate) (g : Gate) (out : ℕ)
      (hc : Monotone2 (Repair_patchCircuit pre post g out))
      (correct : ∀ x : Fin n → Bool,
        (Repair_patchCircuit pre post g out).eval (List.ofFn x) = true ↔ Repair_hit G x)
      (a b : Fin n) (edge : G.Adj a b)
      (essential : (Repair_patchCircuit pre post ⟨.or,[]⟩ out).eval
        (List.ofFn (Repair_mask {a,b})) = false)
      (unique : ∀ u v, G.Adj u v →
        (Repair_patchCircuit pre post ⟨.or,[]⟩ out).eval (List.ofFn (Repair_mask {u,v})) = false →
        (u = a ∧ v = b) ∨ (u = b ∧ v = a)) :
      let C := Repair_patchCircuit pre post g out
      let D := Repair_patchCircuit pre post ⟨.and,[a.val,b.val]⟩ out
      Monotone2 D ∧ D.size = C.size ∧
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = true ↔ Repair_hit G x) ∧
      (∀ x : Fin n → Bool, Repair_WireLE (D.wires (List.ofFn x)) (C.wires (List.ofFn x))) := by
    dsimp only
    have hpre : ∀ q ∈ pre, q.op = GateOp.and ∨ q.op = GateOp.or := by
      intro q hq
      exact (hc q (List.mem_append_left _ hq)).1
    have hpost : ∀ q ∈ post, q.op = GateOp.and ∨ q.op = GateOp.or := by
      intro q hq
      exact (hc q (List.mem_append_right _ (List.mem_cons_of_mem _ hq))).1
    have hg : g.op = GateOp.and ∨ g.op = GateOp.or :=
      (hc g (List.mem_append_right _ List.mem_cons_self)).1
    obtain ⟨dom,works⟩ := Repair_single_critical_replacement G (Repair_gatePrefix pre g)
      (Repair_gateContext pre post out) (Repair_gatePrefix_mono pre g hpre hg)
      (Repair_gateContext_mono pre post out hpre hpost)
      (fun x => by simpa only [Repair_gateContext_orig] using correct x)
      a b edge (by simpa only [Repair_gateContext_zero] using essential)
      (fun u v huv hzero => unique u v huv (by simpa only [Repair_gateContext_zero] using hzero))
    refine ⟨Repair_patch_mono pre post g _ out hc ⟨Or.inl rfl,by simp⟩,?_,?_,?_⟩
    · simp [Repair_patchCircuit,circuitSizeEq]
    · intro x
      simpa only [Repair_gateContext_edge] using works x
    · intro x
      apply Repair_patch_le pre post g ⟨.and,[a.val,b.val]⟩ out (List.ofFn x) hpost
      change Repair_gatePrefix pre ⟨.and,[a.val,b.val]⟩ x = true → Repair_gatePrefix pre g x = true
      simpa only [Repair_gatePrefix_edge] using dom x

  have Repair_patch_wire_value {n : ℕ} (pre post : List Gate) (g : Gate) (out : ℕ)
      (x : Fin n → Bool) :
      ((Repair_patchCircuit pre post g out).wires (List.ofFn x)).getD (n + pre.length) false =
        Repair_gatePrefix pre g x := by
    change (Repair_run (pre ++ g :: post) (List.ofFn x)).getD (n + pre.length) false = _
    simp only [Repair_run,List.foldl_append,List.foldl_cons]
    change (Repair_run post (Repair_run pre (List.ofFn x) ++ [Repair_gatePrefix pre g x])).getD
      (n + pre.length) false = _
    have hlen : (Repair_run pre (List.ofFn x)).length = n + pre.length := by simp [Repair_run_length]
    rw [Repair_run_old_read post _ _ (by simp [hlen])]
    rw [List.getD_append_right _ _ _ _ (by omega),hlen,Nat.sub_self]
    rfl

  have Repair_repaired_gate_safe {n : ℕ} (G : SimpleGraph (Fin n))
      (pre post : List Gate) (out : ℕ) (a b : Fin n) (edge : G.Adj a b)
      (x : Fin n → Bool) :
      ((Repair_patchCircuit pre post ⟨.and,[a.val,b.val]⟩ out).wires
        (List.ofFn x)).getD (n + pre.length) false = true → Repair_hit G x := by
    rw [Repair_patch_wire_value,Repair_gatePrefix_edge]
    intro h
    obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp h
    exact ⟨a,b,edge,ha,hb⟩

  have Repair_zero_edge_circuit_repair {n : ℕ} (G : SimpleGraph (Fin n))
      (pre post : List Gate) (g : Gate) (out : ℕ)
      (hc : Monotone2 (Repair_patchCircuit pre post g out))
      (correct : ∀ x : Fin n → Bool,
        (Repair_patchCircuit pre post g out).eval (List.ofFn x) = true ↔ Repair_hit G x)
      (survives : ∀ u v, G.Adj u v →
        (Repair_patchCircuit pre post ⟨.or,[]⟩ out).eval (List.ofFn (Repair_mask {u,v})) = true) :
      let C := Repair_patchCircuit pre post g out
      let D := Repair_patchCircuit pre post ⟨.or,[]⟩ out
      Monotone2 D ∧ D.size = C.size ∧
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = true ↔ Repair_hit G x) ∧
      (∀ x : Fin n → Bool, Repair_WireLE (D.wires (List.ofFn x)) (C.wires (List.ofFn x))) ∧
      (∀ x : Fin n → Bool, (D.wires (List.ofFn x)).getD (n + pre.length) false = false) := by
    dsimp only
    have hpre : ∀ q ∈ pre, q.op = GateOp.and ∨ q.op = GateOp.or := by
      intro q hq
      exact (hc q (List.mem_append_left _ hq)).1
    have hpost : ∀ q ∈ post, q.op = GateOp.and ∨ q.op = GateOp.or := by
      intro q hq
      exact (hc q (List.mem_append_right _ (List.mem_cons_of_mem _ hq))).1
    have works := Repair_zero_critical_replacement G (Repair_gatePrefix pre g) (Repair_gateContext pre post out)
      (Repair_gateContext_mono pre post out hpre hpost)
      (fun x => by simpa only [Repair_gateContext_orig] using correct x)
      (fun u v huv => by simpa only [Repair_gateContext_zero] using survives u v huv)
    refine ⟨Repair_patch_mono pre post g _ out hc ⟨Or.inr rfl,by simp⟩,?_,?_,?_,?_⟩
    · simp [Repair_patchCircuit,circuitSizeEq]
    · intro x
      simpa only [Repair_gateContext_zero] using works x
    · intro x
      apply Repair_patch_le pre post g ⟨.or,[]⟩ out (List.ofFn x) hpost
      simp [gateAndEq, gateOrEq]
    · intro x
      rw [Repair_patch_wire_value]
      rfl

  have Repair_single_edge_circuit_repair_safe {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (pre post : List Gate) (g : Gate) (out : ℕ)
      (hc : Monotone2 (Repair_patchCircuit pre post g out))
      (correct : ∀ x : Fin n → Bool,
        (Repair_patchCircuit pre post g out).eval (List.ofFn x) = true ↔ Repair_hit G x)
      (a b : Fin n) (edge : G.Adj a b)
      (essential : (Repair_patchCircuit pre post ⟨.or,[]⟩ out).eval
        (List.ofFn (Repair_mask {a,b})) = false)
      (unique : ∀ u v, G.Adj u v →
        (Repair_patchCircuit pre post ⟨.or,[]⟩ out).eval (List.ofFn (Repair_mask {u,v})) = false →
        (u = a ∧ v = b) ∨ (u = b ∧ v = a)) :
      let C := Repair_patchCircuit pre post g out
      let D := Repair_patchCircuit pre post ⟨.and,[a.val,b.val]⟩ out
      Monotone2 D ∧ D.size = C.size ∧
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = true ↔ Repair_hit G x) ∧
      (∀ x : Fin n → Bool, Repair_WireLE (D.wires (List.ofFn x)) (C.wires (List.ofFn x))) ∧
      (∀ x : Fin n → Bool, (D.wires (List.ofFn x)).getD (n + pre.length) false = true → Repair_hit G x) := by
    obtain ⟨hm,hs,he,hl⟩ := Repair_single_edge_circuit_repair G pre post g out hc correct a b edge essential unique
    exact ⟨hm,hs,he,hl,Repair_repaired_gate_safe G pre post out a b edge⟩

  have Construction_junk_subset_of_pointwise_decrease {n : ℕ} (G : SimpleGraph (Fin n))
      [DecidableRel G.Adj] (C D : Circuit) (hsize : D.size ≤ C.size)
      (hops : ∀ j, j < D.size → (gateAt D j).op = GateOp.and →
        (gateAt C j).op = GateOp.and)
      (hval : ∀ j, j < D.size → ∀ x : Fin n → Bool,
        graphFun G ∅ x = false → gateVal n D j x = true → gateVal n C j x = true) :
      TopForm.junk G D ⊆ TopForm.junk G C := by
    intro j hj
    have hd : IsDirtyAnd n G D j := (Finset.mem_filter.mp hj).2
    obtain ⟨hop, hj, x, hx, hf⟩ := hd
    have hjD : j < D.size := hj
    have hjC : j < C.gates.length := lt_of_lt_of_le hjD hsize
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjC,
      hops j hjD hop, hjC, x, hval j hjD x hf hx, hf⟩

  have Construction_junk_ssubset_of_pointwise_repair {n : ℕ} (G : SimpleGraph (Fin n))
      [DecidableRel G.Adj] (C D : Circuit) (hsize : D.size ≤ C.size)
      (hops : ∀ j, j < D.size → (gateAt D j).op = GateOp.and →
        (gateAt C j).op = GateOp.and)
      (hval : ∀ j, j < D.size → ∀ x : Fin n → Bool,
        graphFun G ∅ x = false → gateVal n D j x = true → gateVal n C j x = true)
      (j : ℕ) (hdirty : IsDirtyAnd n G C j) (hclean : TopForm.BelowF G D j) :
      TopForm.junk G D ⊂ TopForm.junk G C := by
    classical
    refine Finset.ssubset_iff_subset_ne.mpr
      ⟨Construction_junk_subset_of_pointwise_decrease G C D hsize hops hval, ?_⟩
    intro heq
    have hj : j ∈ TopForm.junk G C := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hdirty.2.1, hdirty⟩
    rw [← heq] at hj
    have hd := (Finset.mem_filter.mp hj).2
    obtain ⟨x, hx, hf⟩ := hd.2.2
    have ht := hclean x hx
    rw [hf] at ht
    cases ht

  have Construction_gateAt_patch_op (pre post : List Gate) (g h : Gate) (out : ℕ)
      (hop : h.op = GateOp.and → g.op = GateOp.and) (j : ℕ) :
      (gateAt ⟨pre ++ h :: post, out⟩ j).op = GateOp.and →
        (gateAt ⟨pre ++ g :: post, out⟩ j).op = GateOp.and := by
    by_cases hj : j < pre.length
    · simp only [gateAtEq, List.getD_append _ _ _ _ hj]
      exact id
    · have hj' : pre.length ≤ j := Nat.le_of_not_gt hj
      simp only [gateAtEq, List.getD_append_right _ _ _ _ hj']
      by_cases heq : j - pre.length = 0
      · simp only [heq, List.getD_cons_zero]
        exact hop
      · obtain ⟨k, hk⟩ : ∃ k, j - pre.length = k + 1 :=
          ⟨j - pre.length - 1, by omega⟩
        simp only [hk, List.getD_cons_succ]
        exact id

  have Construction_junk_patch_ssubset {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (pre post : List Gate) (g h : Gate) (out : ℕ)
      (hop : h.op = GateOp.and → g.op = GateOp.and)
      (hval : ∀ j, j < pre.length + 1 + post.length → ∀ x : Fin n → Bool,
        graphFun G ∅ x = false →
        gateVal n ⟨pre ++ h :: post, out⟩ j x = true →
        gateVal n ⟨pre ++ g :: post, out⟩ j x = true)
      (hdirty : IsDirtyAnd n G ⟨pre ++ g :: post, out⟩ pre.length)
      (hclean : TopForm.BelowF G ⟨pre ++ h :: post, out⟩ pre.length) :
      TopForm.junk G ⟨pre ++ h :: post, out⟩ ⊂
        TopForm.junk G ⟨pre ++ g :: post, out⟩ := by
    apply Construction_junk_ssubset_of_pointwise_repair G _ _
      (by simp [circuitSizeEq])
      (fun j _ => Construction_gateAt_patch_op pre post g h out hop j)
      (fun j hj => hval j (by simpa [circuitSizeEq, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hj)) pre.length hdirty hclean

  let CriticalEdge {n : ℕ} (G : SimpleGraph (Fin n))
      (pre post : List Gate) (out : ℕ) (a b : Fin n) : Prop :=
    G.Adj a b ∧ (Repair_patchCircuit pre post ⟨.or, []⟩ out).eval
      (List.ofFn (Repair_mask {a,b})) = false

  have dirtySet_eq_junk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit) : dirtySet G C = PEqualNP.TopForm.junk G C := rfl

  have dirty_extremal_no_clean_patch {n : ℕ} (G : SimpleGraph (Fin n))
      [DecidableRel G.Adj] (pre post : List Gate) (g h : Gate) (out : ℕ)
      (hmin : ∀ D, Correct G D → D.size ≤ (Repair_patchCircuit pre post g out).size →
        (dirtySet G (Repair_patchCircuit pre post g out)).card ≤ (dirtySet G D).card)
      (hD : Correct G (Repair_patchCircuit pre post h out))
      (hdown : ∀ x : Fin n → Bool,
        Repair_WireLE ((Repair_patchCircuit pre post h out).wires (List.ofFn x))
          ((Repair_patchCircuit pre post g out).wires (List.ofFn x)))
      (hbad : PEqualNP.CleanedNonEdge.IsDirtyAnd n G
        (Repair_patchCircuit pre post g out) pre.length)
      (hsafe : ∀ x : Fin n → Bool,
        ((Repair_patchCircuit pre post h out).wires (List.ofFn x)).getD
          (n + pre.length) false = true → Repair_hit G x) : False := by
    have hg : g.op = GateOp.and := by
      have h := hbad.1
      simpa [gateAtEq, Repair_patchCircuit,
        List.getD_eq_getElem?_getD] using h
    have hclean : PEqualNP.TopForm.BelowF G (Repair_patchCircuit pre post h out)
        pre.length := by
      intro x hx
      have hit := hsafe x hx
      rw [graphFunEq]
      simpa [Repair_hit] using hit
    have hsub := Construction_junk_patch_ssubset G pre post g h out (fun _ => hg)
      (fun j _ x _ => hdown x (n+j)) hbad hclean
    have hlt := Finset.card_lt_card hsub
    have hle := hmin (Repair_patchCircuit pre post h out) hD
      (by simp [Repair_patchCircuit, circuitSizeEq])
    rw [dirtySet_eq_junk, dirtySet_eq_junk] at hle
    exact Nat.not_lt_of_ge hle hlt

  have dirty_extremal_two_critical_edges {n : ℕ} (G : SimpleGraph (Fin n))
      [DecidableRel G.Adj] (pre post : List Gate) (g : Gate) (out : ℕ)
      (hc : Correct G (Repair_patchCircuit pre post g out))
      (hmin : ∀ D, Correct G D → D.size ≤ (Repair_patchCircuit pre post g out).size →
        (dirtySet G (Repair_patchCircuit pre post g out)).card ≤ (dirtySet G D).card)
      (hbad : PEqualNP.CleanedNonEdge.IsDirtyAnd n G
        (Repair_patchCircuit pre post g out) pre.length) :
      ∃ a b c d, CriticalEdge G pre post out a b ∧ CriticalEdge G pre post out c d ∧
        ¬ ((c = a ∧ d = b) ∨ (c = b ∧ d = a)) := by
    classical
    have correct : ∀ y : Fin n → Bool,
        (Repair_patchCircuit pre post g out).eval (List.ofFn y) = true ↔ Repair_hit G y := by
      intro y
      rw [hc.2 y]
      exact decide_eq_true_iff
    have impossible (h : Gate) (hm : Monotone2 (Repair_patchCircuit pre post h out))
        (hf : ∀ y : Fin n → Bool,
          (Repair_patchCircuit pre post h out).eval (List.ofFn y) = true ↔ Repair_hit G y)
        (hv : ∀ y : Fin n → Bool,
          Repair_WireLE ((Repair_patchCircuit pre post h out).wires (List.ofFn y))
            ((Repair_patchCircuit pre post g out).wires (List.ofFn y)))
        (hsafe : ∀ y : Fin n → Bool,
          ((Repair_patchCircuit pre post h out).wires (List.ofFn y)).getD
            (n + pre.length) false = true → Repair_hit G y) : False := by
      apply dirty_extremal_no_clean_patch G pre post g h out hmin _ hv hbad hsafe
      refine ⟨hm, ?_⟩
      intro y
      apply Bool.eq_iff_iff.mpr
      rw [decide_eq_true_iff]
      exact hf y
    by_cases hex : ∃ a b, CriticalEdge G pre post out a b
    · obtain ⟨a, b, hab⟩ := hex
      by_cases htwo : ∃ c d, CriticalEdge G pre post out c d ∧
          ¬ ((c = a ∧ d = b) ∨ (c = b ∧ d = a))
      · obtain ⟨c, d, hcd, hne⟩ := htwo
        exact ⟨a, b, c, d, hab, hcd, hne⟩
      · have unique : ∀ u v, G.Adj u v →
            (Repair_patchCircuit pre post ⟨.or, []⟩ out).eval
              (List.ofFn (Repair_mask {u,v})) = false →
            (u = a ∧ v = b) ∨ (u = b ∧ v = a) := by
          intro u v huv hz
          by_contra hne
          exact htwo ⟨u, v, ⟨huv, hz⟩, hne⟩
        obtain ⟨hm, _, hf, hv, hs⟩ := Repair_single_edge_circuit_repair_safe G
          pre post g out hc.1 correct a b hab.1 hab.2 unique
        exact False.elim (impossible _ hm hf hv hs)
    · have survives : ∀ u v, G.Adj u v →
          (Repair_patchCircuit pre post ⟨.or, []⟩ out).eval
            (List.ofFn (Repair_mask {u,v})) = true := by
        intro u v huv
        cases hz : (Repair_patchCircuit pre post ⟨.or, []⟩ out).eval
            (List.ofFn (Repair_mask {u,v})) with
        | false => exact False.elim (hex ⟨u, v, huv, hz⟩)
        | true => rfl
      obtain ⟨hm, _, hf, hv, hz⟩ := Repair_zero_edge_circuit_repair G
        pre post g out hc.1 correct survives
      apply False.elim
      apply impossible _ hm hf hv
      intro y hy
      rw [hz y] at hy
      cases hy

  have touching_two_edges_contains_center {V : Type} (G : SimpleGraph V)
      (htri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
      (a b c u v : V) (hab : G.Adj a b) (hac : G.Adj a c) (hbc : b ≠ c)
      (huv : G.Adj u v)
      (h₁ : (u = a ∨ v = a) ∨ (u = b ∨ v = b))
      (h₂ : (u = a ∨ v = a) ∨ (u = c ∨ v = c)) : u = a ∨ v = a := by
    classical
    by_contra h
    rcases h₁.resolve_left h with hub | hvb
    · rcases h₂.resolve_left h with huc | hvc
      · exact hbc (hub.symm.trans huc)
      · subst u
        subst v
        exact htri a b c hab huv hac.symm
    · rcases h₂.resolve_left h with huc | hvc
      · subst u
        subst v
        exact htri a b c hab huv.symm hac.symm
      · exact hbc (hvb.symm.trans hvc)

  have edge_family_star_or_disjoint {V : Type} (G : SimpleGraph V)
      (htri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
      (P : V → V → Prop) (hP : ∀ a b, P a b → G.Adj a b)
      (hex : ∃ a b, P a b) :
      (∃ v, ∀ a b, P a b → a = v ∨ b = v) ∨
        ∃ a b c d, P a b ∧ P c d ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d := by
    classical
    by_cases hd : ∃ a b c d, P a b ∧ P c d ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d
    · exact Or.inr hd
    left
    have meet (a b c d : V) (hab : P a b) (hcd : P c d) :
        (c = a ∨ d = a) ∨ (c = b ∨ d = b) := by
      by_contra h
      push Not at h
      exact hd ⟨a,b,c,d,hab,hcd,Ne.symm h.1.1,Ne.symm h.1.2,
        Ne.symm h.2.1,Ne.symm h.2.2⟩
    obtain ⟨a,b,hab⟩ := hex
    by_cases ha : ∀ c d, P c d → c = a ∨ d = a
    · exact ⟨a,ha⟩
    push Not at ha
    obtain ⟨c,d,hcd,hca,hda⟩ := ha
    have hb : c = b ∨ d = b := (meet a b c d hab hcd).resolve_left
      (not_or.mpr ⟨hca,hda⟩)
    refine ⟨b, ?_⟩
    intro u v huv
    have h₁ : (u = b ∨ v = b) ∨ (u = a ∨ v = a) :=
      (meet a b u v hab huv).symm
    rcases hb with hcb | hdb
    · subst c
      exact touching_two_edges_contains_center G htri b a d u v
        (hP a b hab).symm (hP b d hcd) (Ne.symm hda) (hP u v huv)
        h₁ (meet b d u v hcd huv)
    · subst d
      exact touching_two_edges_contains_center G htri b a c u v
        (hP a b hab).symm (hP c b hcd).symm (Ne.symm hca) (hP u v huv)
        h₁ (meet c b u v hcd huv).symm

  have exists_first_dirty_split {n : ℕ} (G : SimpleGraph (Fin n))
      [DecidableRel G.Adj] (C : Circuit)
      (hex : ∃ j, PEqualNP.CleanedNonEdge.IsDirtyAnd n G C j) :
      ∃ pre g post, C.gates = pre ++ g :: post ∧ g.op = GateOp.and ∧
        PEqualNP.CleanedNonEdge.IsDirtyAnd n G C pre.length ∧
        ∀ i < pre.length, ¬ PEqualNP.CleanedNonEdge.IsDirtyAnd n G C i := by
    classical
    let j := Nat.find hex
    have hbad : PEqualNP.CleanedNonEdge.IsDirtyAnd n G C j := Nat.find_spec hex
    have hj : j < C.gates.length := hbad.2.1
    let pre := C.gates.take j
    let g := C.gates[j]
    let post := C.gates.drop (j+1)
    have hlen : pre.length = j := by simp [pre, Nat.min_eq_left hj.le]
    have hsplit : C.gates = pre ++ g :: post := by
      dsimp [pre, g, post]
      rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
    refine ⟨pre, g, post, hsplit, ?_, hlen.symm ▸ hbad, ?_⟩
    · have h := hbad.1
      simpa [gateAtEq, g,
        List.getD_eq_getElem?_getD, hj] using h
    · intro i hi
      apply Nat.find_min hex
      change i < j
      omega

  have correct_minimal_mono {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit) (hc : Correct G C) (hmin : ∀ D, Correct G D → C.size ≤ D.size) :
      IsMinimalMonoCircuit n C := by
    refine ⟨hc.1, ?_⟩
    intro D hd heq
    apply hmin D
    refine ⟨hd, ?_⟩
    intro x
    exact (congrFun heq x).trans (hc.2 x)

  have and_safe_of_no_dirty {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit) (h : ∀ j, ¬ PEqualNP.CleanedNonEdge.IsDirtyAnd n G C j)
      (j : ℕ) (g : Gate) (hjg : C.gates[j]? = some g) (hg : g.op = GateOp.and)
      (x : Fin n → Bool)
      (hx : (C.wires (List.ofFn x)).getD (n+j) false = true) :
      ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true := by
    classical
    by_contra hbad
    obtain ⟨hj, hget⟩ := List.getElem?_eq_some_iff.mp hjg
    apply h j
    refine ⟨?_, hj, x, hx, ?_⟩
    · simpa [gateAtEq,
        List.getD_eq_getElem?_getD, hjg] using hg
    · rw [graphFunEq]
      simp [hbad]

  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  let run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

  have run_length (gs : List Gate) (w : List Bool) :
      (run gs w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp [run]
    | cons g gs ih =>
      change (run gs (step w g)).length = _
      rw [ih]
      simp [step]
      omega

  have run_old_read (gs : List Gate) (w : List Bool) (i : Nat) (hi : i < w.length) :
      (run gs w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      change (run gs (step w g)).getD i false = _
      rw [ih _ (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hi

  have run_input {n : Nat} (gs : List Gate) (x : Fin n → Bool) (i : Fin n) :
      (run gs (List.ofFn x)).getD i false = x i := by
    rw [run_old_read gs _ _ (by simp)]
    simp [List.getD_eq_getElem?_getD]

  have exists_edges {n : Nat} (es : List (Fin n × Fin n)) :
      ∃ C : Circuit, Monotone2 C ∧ C.output < n + C.gates.length ∧
        ∀ x : Fin n → Bool,
          C.eval (List.ofFn x) = es.any (fun e => x e.1 && x e.2) := by
    induction es with
    | nil =>
      refine ⟨⟨[⟨.or, []⟩], n⟩, ?_, by simp, ?_⟩
      · simp [monotoneEq]
      · intro x
        simp [circuitEvalEq, circuitWiresEq, gateAndEq, gateOrEq]
    | cons e es ih =>
      obtain ⟨C, hmono, hout, heval⟩ := ih
      let k := n + C.gates.length
      let a : Gate := ⟨.and, [e.1.val,e.2.val]⟩
      let b : Gate := ⟨.or, [C.output,k]⟩
      let D : Circuit := ⟨C.gates ++ [a,b], k+1⟩
      refine ⟨D, ?_, ?_, ?_⟩
      · intro g hg
        change g ∈ C.gates ++ [a,b] at hg
        rcases List.mem_append.mp hg with hg | hg
        · exact hmono g hg
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
          rcases hg with rfl | rfl <;> simp [a,b]
      · simp [D,k]
        omega
      · intro x
        let w := run C.gates (List.ofFn x)
        have hlen : w.length = k := by simp [w, run_length, k]
        have h1 : w.getD e.1.val false = x e.1 := run_input C.gates x e.1
        have h2 : w.getD e.2.val false = x e.2 := run_input C.gates x e.2
        have ho : C.output < w.length := by simpa [hlen,k] using hout
        have he : D.eval (List.ofFn x) = (C.eval (List.ofFn x) || (x e.1 && x e.2)) := by
          change (run (C.gates ++ [a,b]) (List.ofFn x)).getD (k+1) false = _
          rw [show run (C.gates ++ [a,b]) (List.ofFn x) = run [a,b] w from List.foldl_append]
          change (step (step w a) b).getD (k+1) false = _
          have ha : step w a = w ++ [x e.1 && x e.2] := by
            simp only [step,a,List.map_cons,List.map_nil,gateAndEq, gateOrEq,List.all_cons,
              List.all_nil,Bool.and_true]
            rw [h1,h2]
            rfl
          rw [ha]
          have hr : (w ++ [x e.1 && x e.2]).getD C.output false = w.getD C.output false :=
            List.getD_append _ _ _ _ ho
          have hn : (w ++ [x e.1 && x e.2]).getD k false = (x e.1 && x e.2) := by
            rw [List.getD_append_right _ _ _ _ (by omega)]
            simp [hlen]
          simp only [step,b,gateAndEq, gateOrEq,List.map_cons,List.map_nil,List.any_cons,List.any_nil,
            Bool.or_false,hr,hn]
          rw [List.getD_append_right _ _ _ _ (by simp [hlen])]
          simp [hlen]
          rfl
        rw [he,heval]
        simp [Bool.or_comm]

  have exists_correct {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
      ∃ C : Circuit, Monotone2 C ∧ ∀ x : Fin n → Bool,
        C.eval (List.ofFn x) = decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) := by
    classical
    let E := (Finset.univ : Finset (Fin n × Fin n)).filter (fun e => G.Adj e.1 e.2)
    obtain ⟨C, hm, _, he⟩ := exists_edges E.toList
    refine ⟨C,hm,?_⟩
    intro x
    rw [he]
    apply Bool.eq_iff_iff.mpr
    simp [E]

  intro n G inst htri hquad
  obtain ⟨⟨gs, out⟩, hc, hmin, hcount⟩ := exists_extremal G (exists_correct G)
  have clean : ∀ j, ¬ PEqualNP.CleanedNonEdge.IsDirtyAnd n G ⟨gs, out⟩ j := by
    intro j hj
    obtain ⟨pre, g, post, hsplit, _, hbad, hbefore⟩ :=
      exists_first_dirty_split G ⟨gs, out⟩ ⟨j, hj⟩
    change gs = pre ++ g :: post at hsplit
    subst gs
    have hm : IsMinimalMonoCircuit n ⟨pre ++ g :: post, out⟩ :=
      correct_minimal_mono G _ hc hmin
    have hf : circuitFun n ⟨pre ++ g :: post, out⟩ = graphFun G ∅ := by
      funext x
      rw [circuitFunEq, graphFunEq]
      simpa using hc.2 x
    have hjmem : pre.length ∈ PEqualNP.TopForm.junk G ⟨pre ++ g :: post, out⟩ :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hbad.2.1, hbad⟩
    have hjleast : ∀ i ∈ PEqualNP.TopForm.junk G ⟨pre ++ g :: post, out⟩,
        pre.length ≤ i := by
      intro i hi
      by_contra hlt
      exact hbefore i (Nat.lt_of_not_ge hlt) (Finset.mem_filter.mp hi).2
    obtain ⟨a, b, d, e, hab, hde, hne⟩ :=
      dirty_extremal_two_critical_edges G pre post g out hc hcount hbad
    have hpair (u v : Fin n) : Repair_mask {u,v} = PEqualNP.EdgeOwnership.pairInput u v := by
      funext w
      simp [Repair_mask, pairInputEq]
    have hsymm (u v : Fin n) (h : CriticalEdge G pre post out u v) :
        CriticalEdge G pre post out v u := by
      refine ⟨h.1.symm, ?_⟩
      simpa only [Finset.pair_comm] using h.2
    have repaired : ∃ D : Circuit,
        Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧
        D.size ≤ (⟨pre ++ g :: post, out⟩ : Circuit).size ∧
        (PEqualNP.TopForm.junk G D).card <
          (PEqualNP.TopForm.junk G ⟨pre ++ g :: post, out⟩).card := by
      rcases edge_family_star_or_disjoint G htri (CriticalEdge G pre post out)
        (fun _ _ h => h.1) ⟨a, b, hab⟩ with hstar | hdisjoint
      · obtain ⟨c, hcenter⟩ := hstar
        have orient (u v : Fin n) (h : CriticalEdge G pre post out u v) :
            ∃ w, CriticalEdge G pre post out c w ∧
              ((u = c ∧ v = w) ∨ (u = w ∧ v = c)) := by
          rcases hcenter u v h with hu | hv
          · exact ⟨v, hu ▸ h, Or.inl ⟨hu, rfl⟩⟩
          · exact ⟨u, hv ▸ hsymm u v h, Or.inr ⟨rfl, hv⟩⟩
        obtain ⟨u, hcu, hu⟩ := orient a b hab
        obtain ⟨v, hcv, hv⟩ := orient d e hde
        have huv : u ≠ v := by
          intro huv
          apply hne
          rcases hu with hu | hu
          · rcases hv with hv | hv
            · exact Or.inl ⟨hv.1.trans hu.1.symm, hv.2.trans (huv.symm.trans hu.2.symm)⟩
            · exact Or.inr ⟨hv.1.trans (huv.symm.trans hu.2.symm), hv.2.trans hu.1.symm⟩
          · rcases hv with hv | hv
            · exact Or.inr ⟨hv.1.trans hu.2.symm, hv.2.trans (huv.symm.trans hu.1.symm)⟩
            · exact Or.inl ⟨hv.1.trans (huv.symm.trans hu.1.symm), hv.2.trans hu.2.symm⟩
        apply star_child n G htri hquad pre post g out hm hf hjmem hjleast
        have witness : ∃ c u v, u ≠ v ∧ CriticalEdge G pre post out c u ∧
            CriticalEdge G pre post out c v ∧
            ∀ a b, CriticalEdge G pre post out a b → a = c ∨ b = c :=
          ⟨c, u, v, huv, hcu, hcv, hcenter⟩
        simpa only [CriticalEdge, Repair_patchCircuit, circuitFunEq, hpair] using witness
      · apply disjoint_child n G htri hquad pre post g out hm hf hjmem hjleast
        simpa only [CriticalEdge, Repair_patchCircuit, circuitFunEq, hpair] using hdisjoint
    obtain ⟨D, hd, heq, hsize, hless⟩ := repaired
    have hcorrect : Correct G D := by
      refine ⟨hd, ?_⟩
      intro x
      have h := congrFun heq x
      rw [circuitFunEq, graphFunEq] at h
      simpa using h
    have hle := hcount D hcorrect hsize
    rw [dirtySet_eq_junk, dirtySet_eq_junk] at hle
    exact Nat.not_lt_of_ge hle hless
  refine ⟨⟨gs, out⟩, hc.1, hc.2, ?_, ?_⟩
  · intro D hd he
    exact hmin D ⟨hd, he⟩
  · exact and_safe_of_no_dirty G ⟨gs, out⟩ clean
