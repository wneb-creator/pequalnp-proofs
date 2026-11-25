import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1904_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

def WireLE (v w : List Bool) : Prop :=
  ∀ i, v.getD i false = true → w.getD i false = true

lemma run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (step w g)).length = _
    rw [ih]
    simp [step]
    omega

lemma append_bit_le {v w : List Bool} (hlen : v.length = w.length)
    (hle : WireLE v w) {a b : Bool} (hab : a = true → b = true) :
    WireLE (v ++ [a]) (w ++ [b]) := by
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

lemma gate_eval_le (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    {v w : List Bool} (hle : WireLE v w) :
    g.op.eval (g.inputs.map fun i => v.getD i false) = true →
      g.op.eval (g.inputs.map fun i => w.getD i false) = true := by
  rcases hop with hop | hop
  · rw [hop]
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, forall_exists_index,
      and_imp, forall_apply_eq_imp_iff₂]
    intro hv i hi
    exact hle i (hv i hi)
  · rw [hop]
    simp only [GateOp.eval, List.any_eq_true, List.mem_map]
    rintro ⟨b, ⟨i, hi, rfl⟩, hb⟩
    exact ⟨w.getD i false, ⟨i, hi, rfl⟩, hle i hb⟩

lemma run_le (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    {v w : List Bool} (hlen : v.length = w.length) (hle : WireLE v w) :
    WireLE (run gs v) (run gs w) := by
  induction gs generalizing v w with
  | nil => exact hle
  | cons g gs ih =>
    apply ih (fun g hg => hmono g (List.mem_cons_of_mem _ hg))
    · simp [step, hlen]
    · exact append_bit_le hlen hle (gate_eval_le g (hmono g (by simp)) hle)

lemma ofFn_le {n : ℕ} {x y : Fin n → Bool}
    (hxy : ∀ i, x i = true → y i = true) : WireLE (List.ofFn x) (List.ofFn y) := by
  intro i hi
  by_cases hin : i < n
  · simpa [List.getD_eq_getElem?_getD, hin] using hxy ⟨i, hin⟩
      (by simpa [List.getD_eq_getElem?_getD, hin] using hi)
  · simp [List.getD_eq_getElem?_getD, hin] at hi

lemma wires_mono {n : ℕ} {C : Circuit} (hC : Monotone2 C)
    {x y : Fin n → Bool} (hxy : ∀ i, x i = true → y i = true) :
    WireLE (C.wires (List.ofFn x)) (C.wires (List.ofFn y)) := by
  apply run_le C.gates
  · intro g hg
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (hC g hg).1
  · simp
  · exact ofFn_le hxy

lemma edge_pair_extension {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {C D : Circuit} (hD : Monotone2 D)
    (hC : ∀ x : Fin n → Bool, C.eval (List.ofFn x) =
      decide (∃ a b : Fin n, G.Adj a b ∧ x a = true ∧ x b = true))
    (hle : ∀ x : Fin n → Bool, D.eval (List.ofFn x) = true → C.eval (List.ofFn x) = true)
    (hpairs : ∀ a b : Fin n, G.Adj a b →
      D.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput a b)) = true) :
    ∀ x : Fin n → Bool, D.eval (List.ofFn x) =
      decide (∃ a b : Fin n, G.Adj a b ∧ x a = true ∧ x b = true) := by
  intro x
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_iff]
  constructor
  · intro hx
    exact of_decide_eq_true ((hC x).symm.trans (hle x hx))
  · rintro ⟨a, b, hab, ha, hb⟩
    apply wires_mono hD (y := x) (x := PEqualNP.EdgeOwnership.pairInput a b)
      (fun i hi => ?_) D.output (hpairs a b hab)
    have hi' : i = a ∨ i = b := of_decide_eq_true hi
    rcases hi' with rfl | rfl
    · exact ha
    · exact hb

lemma patch_le (pre post : List Gate) (g h : Gate) (out : ℕ) (x : List Bool)
    (hpost : ∀ q ∈ post, q.op = GateOp.and ∨ q.op = GateOp.or)
    (hgate : h.op.eval (h.inputs.map fun i => (run pre x).getD i false) = true →
      g.op.eval (g.inputs.map fun i => (run pre x).getD i false) = true) :
    WireLE (({gates := pre ++ h :: post, output := out} : Circuit).wires x)
      (({gates := pre ++ g :: post, output := out} : Circuit).wires x) := by
  change WireLE (run (pre ++ h :: post) x) (run (pre ++ g :: post) x)
  simp only [run, List.foldl_append, List.foldl_cons]
  apply run_le post hpost
  · simp [step]
  · exact append_bit_le rfl (fun _ hi => hi) hgate

lemma patch_agree (pre post : List Gate) (g h : Gate) (out : ℕ) (x : List Bool)
    (hgate : h.op.eval (h.inputs.map fun i => (run pre x).getD i false) =
      g.op.eval (g.inputs.map fun i => (run pre x).getD i false)) :
    ({gates := pre ++ h :: post, output := out} : Circuit).wires x =
      ({gates := pre ++ g :: post, output := out} : Circuit).wires x := by
  change run (pre ++ h :: post) x = run (pre ++ g :: post) x
  simp only [run, List.foldl_append, List.foldl_cons, step]
  change post.foldl step (run pre x ++ [_]) = post.foldl step (run pre x ++ [_])
  dsimp only [run] at hgate
  rw [hgate]


def hit {n} (G : SimpleGraph (Fin n)) (x : Fin n → Bool) :=
  ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true

def mask {n} (S : Finset (Fin n)) (u : Fin n) := decide (u ∈ S)

lemma zero_critical_replacement {n : ℕ} (G : SimpleGraph (Fin n))
    (gate : (Fin n → Bool) → Bool)
    (tail : (Fin n → Bool) → Bool → Bool)
    (mono : ∀ x y : Fin n → Bool, ∀ p q : Bool,
      (∀ i, x i = true → y i = true) → (p = true → q = true) →
      tail x p = true → tail y q = true)
    (correct : ∀ x, tail x (gate x) = true ↔ hit G x)
    (survives : ∀ u v, G.Adj u v → tail (mask {u,v}) false = true) :
    ∀ x, tail x false = true ↔ hit G x := by
  intro x
  constructor
  · intro h
    exact (correct x).mp (mono x x false (gate x) (fun _ h => h)
      (by simp) h)
  · rintro ⟨u,v,uv,hu,hv⟩
    apply mono (mask {u,v}) x false false ?_ (fun h => h) (survives u v uv)
    intro i hi
    simp only [mask, decide_eq_true_eq, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact hu
    · exact hv

lemma single_critical_replacement {n : ℕ} (G : SimpleGraph (Fin n))
    (gate : (Fin n → Bool) → Bool)
    (tail : (Fin n → Bool) → Bool → Bool)
    (gate_mono : ∀ x y : Fin n → Bool,
      (∀ i, x i = true → y i = true) → gate x = true → gate y = true)
    (tail_mono : ∀ x y : Fin n → Bool, ∀ p q : Bool,
      (∀ i, x i = true → y i = true) → (p = true → q = true) →
      tail x p = true → tail y q = true)
    (correct : ∀ x, tail x (gate x) = true ↔ hit G x)
    (a b : Fin n) (edge : G.Adj a b)
    (essential : tail (mask {a,b}) false = false)
    (unique : ∀ u v, G.Adj u v → tail (mask {u,v}) false = false →
      (u = a ∧ v = b) ∨ (u = b ∧ v = a)) :
    (∀ x, (x a && x b) = true → gate x = true) ∧
    (∀ x, tail x (x a && x b) = true ↔ hit G x) := by
  have pair_on : gate (mask {a,b}) = true := by
    have yes := (correct (mask {a,b})).mpr
      ⟨a,b,edge,by simp [mask],by simp [mask]⟩
    cases h : gate (mask {a,b})
    · rw [h,essential] at yes
      contradiction
    · rfl
  have dominated : ∀ x, (x a && x b) = true → gate x = true := by
    intro x hx
    obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp hx
    apply gate_mono (mask {a,b}) x ?_ pair_on
    intro i hi
    simp only [mask, decide_eq_true_eq, Finset.mem_insert, Finset.mem_singleton] at hi
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
    have sub : ∀ i, mask {u,v} i = true → x i = true := by
      intro i hi
      simp only [mask, decide_eq_true_eq, Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · exact hu
      · exact hv
    cases survive : tail (mask {u,v}) false with
    | true =>
      exact tail_mono (mask {u,v}) x false (x a && x b) sub (by simp) survive
    | false =>
      have active : (x a && x b) = true := by
        rcases unique u v uv survive with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [hu,hv]
      have yes := (correct (mask {u,v})).mpr
        ⟨u,v,uv,by simp [mask],by simp [mask]⟩
      exact tail_mono (mask {u,v}) x (gate (mask {u,v})) (x a && x b)
        sub (fun _ => active) yes

def patchCircuit (pre post : List Gate) (g : Gate) (out : ℕ) : Circuit :=
  ⟨pre ++ g :: post, out⟩

def gatePrefix {n : ℕ} (pre : List Gate) (g : Gate) (x : Fin n → Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => (run pre (List.ofFn x)).getD i false)

def gateContext {n : ℕ} (pre post : List Gate) (out : ℕ)
    (x : Fin n → Bool) (p : Bool) : Bool :=
  (run post (run pre (List.ofFn x) ++ [p])).getD out false

lemma run_old_read (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (step w g)).getD i false = _
    rw [ih _ (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi

lemma run_input {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : Fin n) :
    (run gs (List.ofFn x)).getD i false = x i := by
  rw [run_old_read gs _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD]

lemma gateContext_orig {n : ℕ} (pre post : List Gate) (g : Gate) (out : ℕ)
    (x : Fin n → Bool) :
    gateContext pre post out x (gatePrefix pre g x) =
      (patchCircuit pre post g out).eval (List.ofFn x) := by
  simp only [gateContext,gatePrefix,patchCircuit,Circuit.eval,Circuit.wires,
    run,List.foldl_append,List.foldl_cons]
  rfl

lemma gateContext_zero {n : ℕ} (pre post : List Gate) (out : ℕ)
    (x : Fin n → Bool) :
    gateContext pre post out x false =
      (patchCircuit pre post ⟨.or,[]⟩ out).eval (List.ofFn x) := by
  exact gateContext_orig pre post ⟨.or,[]⟩ out x

lemma gatePrefix_edge {n : ℕ} (pre : List Gate) (a b : Fin n) (x : Fin n → Bool) :
    gatePrefix pre ⟨.and,[a.val,b.val]⟩ x = (x a && x b) := by
  simp only [gatePrefix,GateOp.eval,List.map_cons,List.map_nil,List.all_cons,
    List.all_nil,id_eq,Bool.and_true]
  rw [run_input pre x a,run_input pre x b]

lemma gateContext_edge {n : ℕ} (pre post : List Gate) (out : ℕ) (a b : Fin n)
    (x : Fin n → Bool) :
    gateContext pre post out x (x a && x b) =
      (patchCircuit pre post ⟨.and,[a.val,b.val]⟩ out).eval (List.ofFn x) := by
  rw [←gatePrefix_edge pre a b x]
  exact gateContext_orig pre post ⟨.and,[a.val,b.val]⟩ out x

lemma gateContext_mono {n : ℕ} (pre post : List Gate) (out : ℕ)
    (hpre : ∀ g ∈ pre, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hpost : ∀ g ∈ post, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (p q : Bool)
    (hxy : ∀ i, x i = true → y i = true) (hpq : p = true → q = true) :
    gateContext pre post out x p = true → gateContext pre post out y q = true := by
  apply run_le post hpost (by simp [run_length]) _ out
  exact append_bit_le (by simp [run_length])
    (run_le pre hpre (by simp) (ofFn_le hxy)) hpq

lemma gatePrefix_mono {n : ℕ} (pre : List Gate) (g : Gate)
    (hpre : ∀ g ∈ pre, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true) :
    gatePrefix pre g x = true → gatePrefix pre g y = true := by
  exact gate_eval_le g hg (run_le pre hpre (by simp) (ofFn_le hxy))

lemma patch_mono (pre post : List Gate) (g h : Gate) (out : ℕ)
    (hc : Monotone2 (patchCircuit pre post g out))
    (hh : (h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2) :
    Monotone2 (patchCircuit pre post h out) := by
  intro q hq
  change q ∈ pre ++ h :: post at hq
  rcases List.mem_append.mp hq with hp | hpost
  · exact hc q (List.mem_append_left _ hp)
  · rcases List.mem_cons.mp hpost with rfl | ht
    · exact hh
    · exact hc q (List.mem_append_right _ (List.mem_cons_of_mem _ ht))

lemma single_edge_circuit_repair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (pre post : List Gate) (g : Gate) (out : ℕ)
    (hc : Monotone2 (patchCircuit pre post g out))
    (correct : ∀ x : Fin n → Bool,
      (patchCircuit pre post g out).eval (List.ofFn x) = true ↔ hit G x)
    (a b : Fin n) (edge : G.Adj a b)
    (essential : (patchCircuit pre post ⟨.or,[]⟩ out).eval
      (List.ofFn (mask {a,b})) = false)
    (unique : ∀ u v, G.Adj u v →
      (patchCircuit pre post ⟨.or,[]⟩ out).eval (List.ofFn (mask {u,v})) = false →
      (u = a ∧ v = b) ∨ (u = b ∧ v = a)) :
    let C := patchCircuit pre post g out
    let D := patchCircuit pre post ⟨.and,[a.val,b.val]⟩ out
    Monotone2 D ∧ D.size = C.size ∧
    (∀ x : Fin n → Bool, D.eval (List.ofFn x) = true ↔ hit G x) ∧
    (∀ x : Fin n → Bool, WireLE (D.wires (List.ofFn x)) (C.wires (List.ofFn x))) := by
  dsimp only
  have hpre : ∀ q ∈ pre, q.op = GateOp.and ∨ q.op = GateOp.or := by
    intro q hq
    exact (hc q (List.mem_append_left _ hq)).1
  have hpost : ∀ q ∈ post, q.op = GateOp.and ∨ q.op = GateOp.or := by
    intro q hq
    exact (hc q (List.mem_append_right _ (List.mem_cons_of_mem _ hq))).1
  have hg : g.op = GateOp.and ∨ g.op = GateOp.or :=
    (hc g (List.mem_append_right _ List.mem_cons_self)).1
  obtain ⟨dom,works⟩ := single_critical_replacement G (gatePrefix pre g)
    (gateContext pre post out) (gatePrefix_mono pre g hpre hg)
    (gateContext_mono pre post out hpre hpost)
    (fun x => by simpa only [gateContext_orig] using correct x)
    a b edge (by simpa only [gateContext_zero] using essential)
    (fun u v huv hzero => unique u v huv (by simpa only [gateContext_zero] using hzero))
  refine ⟨patch_mono pre post g _ out hc ⟨Or.inl rfl,by simp⟩,?_,?_,?_⟩
  · simp [patchCircuit,Circuit.size]
  · intro x
    simpa only [gateContext_edge] using works x
  · intro x
    apply patch_le pre post g ⟨.and,[a.val,b.val]⟩ out (List.ofFn x) hpost
    change gatePrefix pre ⟨.and,[a.val,b.val]⟩ x = true → gatePrefix pre g x = true
    simpa only [gatePrefix_edge] using dom x

lemma patch_wire_value {n : ℕ} (pre post : List Gate) (g : Gate) (out : ℕ)
    (x : Fin n → Bool) :
    ((patchCircuit pre post g out).wires (List.ofFn x)).getD (n + pre.length) false =
      gatePrefix pre g x := by
  change (run (pre ++ g :: post) (List.ofFn x)).getD (n + pre.length) false = _
  simp only [run,List.foldl_append,List.foldl_cons]
  change (run post (run pre (List.ofFn x) ++ [gatePrefix pre g x])).getD
    (n + pre.length) false = _
  have hlen : (run pre (List.ofFn x)).length = n + pre.length := by simp [run_length]
  rw [run_old_read post _ _ (by simp [hlen])]
  rw [List.getD_append_right _ _ _ _ (by omega),hlen,Nat.sub_self]
  rfl

lemma repaired_gate_safe {n : ℕ} (G : SimpleGraph (Fin n))
    (pre post : List Gate) (out : ℕ) (a b : Fin n) (edge : G.Adj a b)
    (x : Fin n → Bool) :
    ((patchCircuit pre post ⟨.and,[a.val,b.val]⟩ out).wires
      (List.ofFn x)).getD (n + pre.length) false = true → hit G x := by
  rw [patch_wire_value,gatePrefix_edge]
  intro h
  obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp h
  exact ⟨a,b,edge,ha,hb⟩

lemma zero_edge_circuit_repair {n : ℕ} (G : SimpleGraph (Fin n))
    (pre post : List Gate) (g : Gate) (out : ℕ)
    (hc : Monotone2 (patchCircuit pre post g out))
    (correct : ∀ x : Fin n → Bool,
      (patchCircuit pre post g out).eval (List.ofFn x) = true ↔ hit G x)
    (survives : ∀ u v, G.Adj u v →
      (patchCircuit pre post ⟨.or,[]⟩ out).eval (List.ofFn (mask {u,v})) = true) :
    let C := patchCircuit pre post g out
    let D := patchCircuit pre post ⟨.or,[]⟩ out
    Monotone2 D ∧ D.size = C.size ∧
    (∀ x : Fin n → Bool, D.eval (List.ofFn x) = true ↔ hit G x) ∧
    (∀ x : Fin n → Bool, WireLE (D.wires (List.ofFn x)) (C.wires (List.ofFn x))) ∧
    (∀ x : Fin n → Bool, (D.wires (List.ofFn x)).getD (n + pre.length) false = false) := by
  dsimp only
  have hpre : ∀ q ∈ pre, q.op = GateOp.and ∨ q.op = GateOp.or := by
    intro q hq
    exact (hc q (List.mem_append_left _ hq)).1
  have hpost : ∀ q ∈ post, q.op = GateOp.and ∨ q.op = GateOp.or := by
    intro q hq
    exact (hc q (List.mem_append_right _ (List.mem_cons_of_mem _ hq))).1
  have works := zero_critical_replacement G (gatePrefix pre g) (gateContext pre post out)
    (gateContext_mono pre post out hpre hpost)
    (fun x => by simpa only [gateContext_orig] using correct x)
    (fun u v huv => by simpa only [gateContext_zero] using survives u v huv)
  refine ⟨patch_mono pre post g _ out hc ⟨Or.inr rfl,by simp⟩,?_,?_,?_,?_⟩
  · simp [patchCircuit,Circuit.size]
  · intro x
    simpa only [gateContext_zero] using works x
  · intro x
    apply patch_le pre post g ⟨.or,[]⟩ out (List.ofFn x) hpost
    simp [GateOp.eval]
  · intro x
    rw [patch_wire_value]
    rfl

lemma single_edge_circuit_repair_safe {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (pre post : List Gate) (g : Gate) (out : ℕ)
    (hc : Monotone2 (patchCircuit pre post g out))
    (correct : ∀ x : Fin n → Bool,
      (patchCircuit pre post g out).eval (List.ofFn x) = true ↔ hit G x)
    (a b : Fin n) (edge : G.Adj a b)
    (essential : (patchCircuit pre post ⟨.or,[]⟩ out).eval
      (List.ofFn (mask {a,b})) = false)
    (unique : ∀ u v, G.Adj u v →
      (patchCircuit pre post ⟨.or,[]⟩ out).eval (List.ofFn (mask {u,v})) = false →
      (u = a ∧ v = b) ∨ (u = b ∧ v = a)) :
    let C := patchCircuit pre post g out
    let D := patchCircuit pre post ⟨.and,[a.val,b.val]⟩ out
    Monotone2 D ∧ D.size = C.size ∧
    (∀ x : Fin n → Bool, D.eval (List.ofFn x) = true ↔ hit G x) ∧
    (∀ x : Fin n → Bool, WireLE (D.wires (List.ofFn x)) (C.wires (List.ofFn x))) ∧
    (∀ x : Fin n → Bool, (D.wires (List.ofFn x)).getD (n + pre.length) false = true → hit G x) := by
  obtain ⟨hm,hs,he,hl⟩ := single_edge_circuit_repair G pre post g out hc correct a b edge essential unique
  exact ⟨hm,hs,he,hl,repaired_gate_safe G pre post out a b edge⟩

lemma critical_gate_repair {n : ℕ} (G : SimpleGraph (Fin n))
    (pre post : List Gate) (g h : Gate) (out : ℕ)
    (hc : Monotone2 (patchCircuit pre post g out))
    (hh : (h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2)
    (correct : ∀ x : Fin n → Bool,
      (patchCircuit pre post g out).eval (List.ofFn x) = true ↔ hit G x)
    (dominated : ∀ x : Fin n → Bool, gatePrefix pre h x = true → gatePrefix pre g x = true)
    (critical : ∀ u v, G.Adj u v →
      (patchCircuit pre post ⟨.or,[]⟩ out).eval (List.ofFn (mask {u,v})) = false →
        gatePrefix pre h (mask {u,v}) = true) :
    let C := patchCircuit pre post g out
    let D := patchCircuit pre post h out
    Monotone2 D ∧ D.size = C.size ∧
    (∀ x : Fin n → Bool, D.eval (List.ofFn x) = true ↔ hit G x) ∧
    (∀ x : Fin n → Bool, WireLE (D.wires (List.ofFn x)) (C.wires (List.ofFn x))) := by
  dsimp only
  have hD := patch_mono pre post g h out hc hh
  have hpost : ∀ q ∈ post, q.op = GateOp.and ∨ q.op = GateOp.or := by
    intro q hq
    exact (hc q (List.mem_append_right _ (List.mem_cons_of_mem _ hq))).1
  have pointwise (x : Fin n → Bool) :
      WireLE ((patchCircuit pre post h out).wires (List.ofFn x))
        ((patchCircuit pre post g out).wires (List.ofFn x)) :=
    patch_le pre post g h out (List.ofFn x) hpost (dominated x)
  have edges (u v : Fin n) (huv : G.Adj u v) :
      (patchCircuit pre post h out).eval (List.ofFn (mask {u,v})) = true := by
    cases hz : (patchCircuit pre post ⟨.or,[]⟩ out).eval (List.ofFn (mask {u,v})) with
    | false =>
      have hon := critical u v huv hz
      have gon := dominated _ hon
      have same := patch_agree pre post g h out (List.ofFn (mask {u,v})) (hon.trans gon.symm)
      change (patchCircuit pre post h out).wires (List.ofFn (mask {u,v})) =
        (patchCircuit pre post g out).wires (List.ofFn (mask {u,v})) at same
      change ((patchCircuit pre post h out).wires (List.ofFn (mask {u,v}))).getD out false = true
      rw [same]
      exact (correct _).mpr ⟨u,v,huv,by simp [mask],by simp [mask]⟩
    | true =>
      have low : WireLE
          ((patchCircuit pre post ⟨.or,[]⟩ out).wires (List.ofFn (mask {u,v})))
          ((patchCircuit pre post h out).wires (List.ofFn (mask {u,v}))) :=
        patch_le pre post h ⟨.or,[]⟩ out (List.ofFn (mask {u,v})) hpost (by simp [GateOp.eval])
      exact low out hz
  refine ⟨hD,by simp [patchCircuit,Circuit.size],?_,pointwise⟩
  intro x
  constructor
  · intro hx
    exact (correct x).mp (pointwise x out hx)
  · rintro ⟨u,v,huv,hu,hv⟩
    apply wires_mono hD (x := mask {u,v}) (y := x) ?_ out (edges u v huv)
    intro i hi
    simp only [mask,decide_eq_true_eq,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact hu
    · exact hv

lemma critical_gate_repair_safe {n : ℕ} (G : SimpleGraph (Fin n))
    (pre post : List Gate) (g h : Gate) (out : ℕ)
    (hc : Monotone2 (patchCircuit pre post g out))
    (hh : (h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2)
    (correct : ∀ x : Fin n → Bool,
      (patchCircuit pre post g out).eval (List.ofFn x) = true ↔ hit G x)
    (dominated : ∀ x : Fin n → Bool, gatePrefix pre h x = true → gatePrefix pre g x = true)
    (critical : ∀ u v, G.Adj u v →
      (patchCircuit pre post ⟨.or,[]⟩ out).eval (List.ofFn (mask {u,v})) = false →
        gatePrefix pre h (mask {u,v}) = true)
    (safe : ∀ x : Fin n → Bool, gatePrefix pre h x = true → hit G x) :
    let C := patchCircuit pre post g out
    let D := patchCircuit pre post h out
    Monotone2 D ∧ D.size = C.size ∧
    (∀ x : Fin n → Bool, D.eval (List.ofFn x) = true ↔ hit G x) ∧
    (∀ x : Fin n → Bool, WireLE (D.wires (List.ofFn x)) (C.wires (List.ofFn x))) ∧
    (∀ x : Fin n → Bool, (D.wires (List.ofFn x)).getD (n + pre.length) false = true → hit G x) := by
  obtain ⟨hm,hs,he,hl⟩ := critical_gate_repair G pre post g h out hc hh correct dominated critical
  refine ⟨hm,hs,he,hl,?_⟩
  intro x
  simpa only [patch_wire_value] using safe x


lemma patch_get_ne (pre post : List Gate) (g h : Gate) (out k : ℕ)
    (hk : k ≠ pre.length) :
    (patchCircuit pre post h out).gates[k]? =
      (patchCircuit pre post g out).gates[k]? := by
  change (pre ++ h :: post)[k]? = (pre ++ g :: post)[k]?
  by_cases hlt : k < pre.length
  · rw [List.getElem?_append_left hlt, List.getElem?_append_left hlt]
  · have hle : pre.length ≤ k := by omega
    rw [List.getElem?_append_right hle, List.getElem?_append_right hle]
    obtain ⟨j, hj⟩ : ∃ j, k - pre.length = j + 1 := ⟨k - pre.length - 1, by omega⟩
    rw [hj]
    rfl

lemma patch_get_self (pre post : List Gate) (g : Gate) (out : ℕ) :
    (patchCircuit pre post g out).gates[pre.length]? = some g := by
  change (pre ++ g :: post)[pre.length]? = some g
  simp

lemma patch_preserves_safe {n : ℕ} (G : SimpleGraph (Fin n))
    (pre post : List Gate) (g h : Gate) (out : ℕ)
    (hdecrease : ∀ x : Fin n → Bool,
      WireLE ((patchCircuit pre post h out).wires (List.ofFn x))
        ((patchCircuit pre post g out).wires (List.ofFn x)))
    (hsafe : ∀ x : Fin n → Bool,
      ((patchCircuit pre post h out).wires (List.ofFn x)).getD (n + pre.length) false = true →
        hit G x)
    (k : ℕ)
    (hold : ∀ q : Gate, (patchCircuit pre post g out).gates[k]? = some q →
      q.op = GateOp.and → ∀ x : Fin n → Bool,
        ((patchCircuit pre post g out).wires (List.ofFn x)).getD (n + k) false = true → hit G x) :
    ∀ q : Gate, (patchCircuit pre post h out).gates[k]? = some q →
      q.op = GateOp.and → ∀ x : Fin n → Bool,
        ((patchCircuit pre post h out).wires (List.ofFn x)).getD (n + k) false = true → hit G x := by
  intro q hq hop x hx
  by_cases hk : k = pre.length
  · subst k
    exact hsafe x hx
  · exact hold q ((patch_get_ne pre post g h out k hk).symm.trans hq) hop x
      (hdecrease x (n + k) hx)


namespace ContextRectangle

open PEqualNP.EdgeOwnership

def PositiveMono {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true

lemma pair_true_iff {n : ℕ} {a b i : Fin n} :
    pairInput a b i = true ↔ i = a ∨ i = b := by
  simp [pairInput]

lemma cross_adj {n : ℕ} (G : SimpleGraph (Fin n))
    (p q : (Fin n → Bool) → Bool) (hp : PositiveMono p) (hq : PositiveMono q)
    (hsafe : ∀ x, p x = true → q x = true →
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
    {a b : Fin n} (ha : p (pairInput a a) = true)
    (hb : q (pairInput b b) = true) : G.Adj a b := by
  have hpa : p (pairInput a b) = true := hp _ _ (by
    intro i hi
    have hia : i = a := by simpa [pairInput] using hi
    subst i
    simp [pairInput]) ha
  have hqb : q (pairInput a b) = true := hq _ _ (by
    intro i hi
    have hib : i = b := by simpa [pairInput] using hi
    subst i
    simp [pairInput]) hb
  obtain ⟨u, v, huv, hu, hv⟩ := hsafe _ hpa hqb
  rcases pair_true_iff.mp hu with rfl | rfl <;>
    rcases pair_true_iff.mp hv with rfl | rfl
  · exact False.elim (G.irrefl huv)
  · exact huv
  · exact huv.symm
  · exact False.elim (G.irrefl huv)

lemma cross_has_singleton_side {n : ℕ} (G : SimpleGraph (Fin n))
    (hc4 : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d)
    (S T : Fin n → Prop) (hcross : ∀ a b, S a → T b → G.Adj a b) :
    (∀ a b, S a → S b → a = b) ∨ (∀ a b, T a → T b → a = b) := by
  classical
  by_cases hs : ∀ a b, S a → S b → a = b
  · exact Or.inl hs
  · right
    push Not at hs
    obtain ⟨a, c, ha, hc, hac⟩ := hs
    intro b d hb hd
    rcases hc4 a b c d (hcross _ _ ha hb) (hcross _ _ hc hb).symm
      (hcross _ _ hc hd) (hcross _ _ ha hd).symm with heq | heq
    · exact False.elim (hac heq)
    · exact heq

lemma cross_side_independent {n : ℕ} (G : SimpleGraph (Fin n))
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → ¬G.Adj c a)
    (S T : Fin n → Prop) (hcross : ∀ a b, S a → T b → G.Adj a b)
    (ht : ∃ t, T t) : ∀ a b, S a → S b → ¬ G.Adj a b := by
  obtain ⟨t, ht⟩ := ht
  intro a b ha hb hab
  exact htri a b t hab (hcross _ _ hb ht) (hcross _ _ ha ht).symm

lemma singleton_support_star {n : ℕ} (G : SimpleGraph (Fin n))
    (hc4 : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d)
    (p q : (Fin n → Bool) → Bool) (hp : PositiveMono p) (hq : PositiveMono q)
    (hsafe : ∀ x, p x = true → q x = true →
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) :
    (∀ a b, p (pairInput a a) = true → p (pairInput b b) = true → a = b) ∨
    (∀ a b, q (pairInput a a) = true → q (pairInput b b) = true → a = b) := by
  exact cross_has_singleton_side G hc4 _ _ (fun a b ha hb => cross_adj G p q hp hq hsafe ha hb)

end ContextRectangle

lemma circuit_context_rectangle {n : ℕ} (G : SimpleGraph (Fin n))
    (hc4 : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d)
    (pre post : List Gate) (g : Gate) (out : ℕ)
    (hc : Monotone2 (patchCircuit pre post g out))
    (correct : ∀ x : Fin n → Bool,
      (patchCircuit pre post g out).eval (List.ofFn x) = true ↔ hit G x) :
    (∀ a b : Fin n,
      gatePrefix pre g (PEqualNP.EdgeOwnership.pairInput a a) = true →
      gatePrefix pre g (PEqualNP.EdgeOwnership.pairInput b b) = true → a = b) ∨
    (∀ a b : Fin n,
      gateContext pre post out (PEqualNP.EdgeOwnership.pairInput a a) true = true →
      gateContext pre post out (PEqualNP.EdgeOwnership.pairInput b b) true = true → a = b) := by
  have hpre : ∀ q ∈ pre, q.op = GateOp.and ∨ q.op = GateOp.or := by
    intro q hq
    exact (hc q (List.mem_append_left _ hq)).1
  have hpost : ∀ q ∈ post, q.op = GateOp.and ∨ q.op = GateOp.or := by
    intro q hq
    exact (hc q (List.mem_append_right _ (List.mem_cons_of_mem _ hq))).1
  have hg : g.op = GateOp.and ∨ g.op = GateOp.or :=
    (hc g (List.mem_append_right _ List.mem_cons_self)).1
  apply ContextRectangle.singleton_support_star G hc4 (gatePrefix pre g)
    (fun x => gateContext pre post out x true)
    (gatePrefix_mono pre g hpre hg)
    (fun x y hxy => gateContext_mono pre post out hpre hpost x y true true hxy (fun h => h))
  intro x hp hq
  apply (correct x).mp
  rw [← gateContext_orig pre post g out x, hp]
  exact hq

end PEqualNP.Outside.L_meta_1904_aux
