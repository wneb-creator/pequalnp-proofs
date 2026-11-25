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


namespace FreeClauses

open PEqualNP.EdgeOwnership

def Represents {n : ℕ} {I : Type*} (G : SimpleGraph (Fin n))
    (S : I → Finset (Fin n)) : Prop :=
  ∀ x : Fin n → Bool,
    (∀ i, ∃ v ∈ S i, x v = true) ↔
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true

lemma clause_covers_edge {n : ℕ} {I : Type*} (G : SimpleGraph (Fin n))
    (S : I → Finset (Fin n)) (hrep : Represents G S) (i : I)
    {a b : Fin n} (hab : G.Adj a b) : a ∈ S i ∨ b ∈ S i := by
  have he : ∃ u v, G.Adj u v ∧ pairInput a b u = true ∧ pairInput a b v = true :=
    ⟨a, b, hab, by simp [pairInput], by simp [pairInput]⟩
  obtain ⟨v, hv, hvab⟩ := (hrep (pairInput a b)).mpr he i
  have hvab' : v = a ∨ v = b := by simpa [pairInput] using hvab
  rcases hvab' with rfl | rfl
  · exact Or.inl hv
  · exact Or.inr hv

lemma pair_edge_of_represents {n : ℕ} {I : Type*} (G : SimpleGraph (Fin n))
    (S : I → Finset (Fin n)) (hrep : Represents G S) {a b : Fin n}
    (hhit : ∀ i, a ∈ S i ∨ b ∈ S i) : G.Adj a b := by
  have hsat : ∀ i, ∃ v ∈ S i, pairInput a b v = true := by
    intro i
    rcases hhit i with ha | hb
    · exact ⟨a, ha, by simp [pairInput]⟩
    · exact ⟨b, hb, by simp [pairInput]⟩
  obtain ⟨u, v, huv, hu, hv⟩ := (hrep (pairInput a b)).mp hsat
  have hu' : u = a ∨ u = b := by simpa [pairInput] using hu
  have hv' : v = a ∨ v = b := by simpa [pairInput] using hv
  rcases hu' with rfl | rfl <;> rcases hv' with rfl | rfl
  · exact False.elim (G.irrefl huv)
  · exact huv
  · exact huv.symm
  · exact False.elim (G.irrefl huv)

lemma three_walk_closes {n : ℕ} {I : Type*} (G : SimpleGraph (Fin n))
    (S : I → Finset (Fin n)) (hrep : Represents G S)
    (hind : ∀ i u, u ∈ S i → ∀ v, v ∈ S i → ¬G.Adj u v)
    {a b c d : Fin n} (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) :
    G.Adj a d := by
  apply pair_edge_of_represents G S hrep
  intro i
  rcases clause_covers_edge G S hrep i hab with ha | hb
  · exact Or.inl ha
  · rcases clause_covers_edge G S hrep i hcd with hc | hd
    · exact False.elim (hind i b hb c hc hbc)
    · exact Or.inr hd

lemma three_walk_repeats {n : ℕ} {I : Type*} (G : SimpleGraph (Fin n))
    (S : I → Finset (Fin n)) (hrep : Represents G S)
    (hind : ∀ i u, u ∈ S i → ∀ v, v ∈ S i → ¬G.Adj u v)
    (hc4 : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d)
    {a b c d : Fin n} (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) :
    a = c ∨ b = d := by
  exact hc4 a b c d hab hbc hcd (three_walk_closes G S hrep hind hab hbc hcd).symm

lemma every_edge_has_leaf_endpoint {n : ℕ} {I : Type*} (G : SimpleGraph (Fin n))
    (S : I → Finset (Fin n)) (hrep : Represents G S)
    (hind : ∀ i u, u ∈ S i → ∀ v, v ∈ S i → ¬G.Adj u v)
    (hc4 : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d)
    {a b : Fin n} (hab : G.Adj a b) :
    (∀ c, G.Adj a c → c = b) ∨ (∀ c, G.Adj b c → c = a) := by
  classical
  by_cases ha : ∀ c, G.Adj a c → c = b
  · exact Or.inl ha
  · right
    push Not at ha
    obtain ⟨c, hac, hcb⟩ := ha
    intro d hbd
    rcases three_walk_repeats G S hrep hind hc4 hac.symm hab hbd with heq | heq
    · exact False.elim (hcb heq)
    · exact heq.symm

def selection {n k : ℕ} (a b : Fin k → Fin n) (s : Fin k → Bool) : Fin n → Bool :=
  fun v => decide (∃ j, v = if s j then a j else b j)

lemma selection_selected {n k : ℕ} (a b : Fin k → Fin n) (s : Fin k → Bool)
    (j : Fin k) : selection a b s (if s j then a j else b j) = true := by
  simp only [selection, decide_eq_true_iff]
  exact ⟨j, rfl⟩

lemma clause_count_of_independent_selections {n k : ℕ} {I : Type*} [Fintype I]
    (G : SimpleGraph (Fin n)) (S : I → Finset (Fin n)) (hrep : Represents G S)
    (a b : Fin k → Fin n) (hedge : ∀ j, G.Adj (a j) (b j))
    (hind : ∀ s : Fin k → Bool, ¬ ∃ u v,
      G.Adj u v ∧ selection a b s u = true ∧ selection a b s v = true) :
    2 ^ k ≤ Fintype.card I := by
  classical
  have hmiss : ∀ s : Fin k → Bool, ∃ i, ¬ ∃ v ∈ S i, selection a b s v = true := by
    intro s
    have h : ¬ ∀ i, ∃ v ∈ S i, selection a b s v = true := by
      intro hsat
      exact hind s ((hrep _).mp hsat)
    exact not_forall.mp h
  let miss : (Fin k → Bool) → I := fun s => Classical.choose (hmiss s)
  have missing : ∀ s, ¬ ∃ v ∈ S (miss s), selection a b s v = true :=
    fun s => Classical.choose_spec (hmiss s)
  have hinj : Function.Injective miss := by
    intro s t heq
    funext j
    have hcross := clause_covers_edge G S hrep (miss s) (hedge j)
    have contradiction (hs : s j = false) (ht : t j = true) : False := by
      rcases hcross with ha | hb
      · have htmem : a j ∈ S (miss t) := by rw [← heq]; exact ha
        exact missing t ⟨a j, htmem, by simpa [ht] using selection_selected a b t j⟩
      · exact missing s ⟨b j, hb, by simpa [hs] using selection_selected a b s j⟩
    have contradiction' (hs : s j = true) (ht : t j = false) : False := by
      rcases hcross with ha | hb
      · exact missing s ⟨a j, ha, by simpa [hs] using selection_selected a b s j⟩
      · have htmem : b j ∈ S (miss t) := by rw [← heq]; exact hb
        exact missing t ⟨b j, htmem, by simpa [ht] using selection_selected a b t j⟩
    cases hs : s j <;> cases ht : t j
    · rfl
    · exact False.elim (contradiction hs ht)
    · exact False.elim (contradiction' hs ht)
    · rfl
  have hc := Fintype.card_le_of_injective miss hinj
  simpa only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using hc

lemma clause_count_of_induced_matching {n k : ℕ} {I : Type*} [Fintype I]
    (G : SimpleGraph (Fin n)) (S : I → Finset (Fin n)) (hrep : Represents G S)
    (a b : Fin k → Fin n) (hedge : ∀ j, G.Adj (a j) (b j))
    (hmatching : ∀ i j (s t : Bool),
      G.Adj (if s then a i else b i) (if t then a j else b j) → i = j ∧ s ≠ t) :
    2 ^ k ≤ Fintype.card I := by
  apply clause_count_of_independent_selections G S hrep a b hedge
  intro s hbad
  obtain ⟨u, v, huv, hu, hv⟩ := hbad
  have hu' : ∃ i, u = if s i then a i else b i := by
    simpa only [selection, decide_eq_true_iff] using hu
  have hv' : ∃ j, v = if s j then a j else b j := by
    simpa only [selection, decide_eq_true_iff] using hv
  obtain ⟨i, rfl⟩ := hu'
  obtain ⟨j, rfl⟩ := hv'
  obtain ⟨hij, hne⟩ := hmatching i j (s i) (s j) huv
  subst j
  exact hne rfl

end FreeClauses





namespace StarCoverMatching

open PEqualNP.MetaComplexity.NestedCover

lemma min_cover_outside_neighbor {n : ℕ} (G : SimpleGraph (Fin n))
    (T : Finset (Fin n)) (hT : IsMinCover G T) {a : Fin n} (ha : a ∈ T) :
    ∃ b, G.Adj a b ∧ b ∉ T := by
  classical
  by_contra hn
  push Not at hn
  have hcover : G.IsVertexCover (T.erase a : Set (Fin n)) := by
    intro u v huv
    change u ∈ T.erase a ∨ v ∈ T.erase a
    by_cases hua : u = a
    · subst u
      right
      exact Finset.mem_erase.mpr ⟨G.ne_of_adj huv.symm, hn v huv⟩
    · by_cases hva : v = a
      · subst v
        left
        exact Finset.mem_erase.mpr ⟨G.ne_of_adj huv, hn u huv.symm⟩
      · rcases hT.1 huv with hu | hv
        · exact Or.inl (Finset.mem_erase.mpr ⟨hua, hu⟩)
        · exact Or.inr (Finset.mem_erase.mpr ⟨hva, hv⟩)
  have hle := hT.2 (T.erase a) hcover
  have hlt := Finset.card_erase_lt_of_mem ha
  omega

lemma min_cover_independent {n : ℕ} (G : SimpleGraph (Fin n))
    (hstar : ∀ a b, G.Adj a b →
      (∀ c, G.Adj a c → c = b) ∨ (∀ c, G.Adj b c → c = a))
    (T : Finset (Fin n)) (hT : IsMinCover G T) :
    ∀ a ∈ T, ∀ b ∈ T, ¬G.Adj a b := by
  intro a ha b hb hab
  rcases hstar a b hab with hleaf | hleaf
  · obtain ⟨c, hac, hc⟩ := min_cover_outside_neighbor G T hT ha
    exact hc ((hleaf c hac) ▸ hb)
  · obtain ⟨c, hbc, hc⟩ := min_cover_outside_neighbor G T hT hb
    exact hc ((hleaf c hbc) ▸ ha)

lemma min_cover_not_two_leaves {n : ℕ} (G : SimpleGraph (Fin n))
    (T : Finset (Fin n)) (hT : IsMinCover G T)
    {a c b : Fin n} (ha : a ∈ T) (hc : c ∈ T) (hac : a ≠ c)
    (hb : b ∉ T) (haleaf : ∀ d, G.Adj a d → d = b)
    (hcleaf : ∀ d, G.Adj c d → d = b) : False := by
  classical
  let U := insert b ((T.erase a).erase c)
  have hcover : G.IsVertexCover (U : Set (Fin n)) := by
    intro u v huv
    change u ∈ U ∨ v ∈ U
    rcases hT.1 huv with hu | hv
    · by_cases hua : u = a
      · subst u
        right
        simp [U, haleaf v huv]
      · by_cases huc : u = c
        · subst u
          right
          simp [U, hcleaf v huv]
        · left
          exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr
            ⟨huc, Finset.mem_erase.mpr ⟨hua, hu⟩⟩)
    · by_cases hva : v = a
      · subst v
        left
        simp [U, haleaf u huv.symm]
      · by_cases hvc : v = c
        · subst v
          left
          simp [U, hcleaf u huv.symm]
        · right
          exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr
            ⟨hvc, Finset.mem_erase.mpr ⟨hva, hv⟩⟩)
  have hca : c ∈ T.erase a := Finset.mem_erase.mpr ⟨hac.symm, hc⟩
  have hcpos : 0 < (T.erase a).card := Finset.card_pos.mpr ⟨c, hca⟩
  have hcarda := Finset.card_erase_of_mem ha
  have hcardc := Finset.card_erase_of_mem hca
  have hb' : b ∉ (T.erase a).erase c := by simp [Finset.mem_erase, hb]
  have hcardU : U.card = ((T.erase a).erase c).card + 1 :=
    Finset.card_insert_of_notMem hb'
  have hle := hT.2 U hcover
  omega

lemma min_cover_leaf_neighbor {n : ℕ} (G : SimpleGraph (Fin n))
    (hstar : ∀ a b, G.Adj a b →
      (∀ c, G.Adj a c → c = b) ∨ (∀ c, G.Adj b c → c = a))
    (T : Finset (Fin n)) (hT : IsMinCover G T) {a : Fin n} (ha : a ∈ T) :
    ∃ b, G.Adj a b ∧ b ∉ T ∧ ∀ c, G.Adj b c → c = a := by
  classical
  obtain ⟨b, hab, hb⟩ := min_cover_outside_neighbor G T hT ha
  refine ⟨b, hab, hb, ?_⟩
  by_contra hnb
  push Not at hnb
  obtain ⟨c, hbc, hca⟩ := hnb
  have hc : c ∈ T := (hT.1 hbc).resolve_left hb
  have haleaf : ∀ d, G.Adj a d → d = b := by
    rcases hstar a b hab with h | h
    · exact h
    · exact False.elim (hca (h c hbc))
  have hcleaf : ∀ d, G.Adj c d → d = b := by
    rcases hstar b c hbc with h | h
    · exact False.elim (hca (h a hab.symm).symm)
    · exact h
  exact min_cover_not_two_leaves G T hT ha hc hca.symm hb haleaf hcleaf

lemma induced_matching_of_min_cover {n : ℕ} (G : SimpleGraph (Fin n))
    (hstar : ∀ a b, G.Adj a b →
      (∀ c, G.Adj a c → c = b) ∨ (∀ c, G.Adj b c → c = a))
    (T : Finset (Fin n)) (hT : IsMinCover G T) :
    ∃ a b : Fin T.card → Fin n,
      (∀ j, G.Adj (a j) (b j)) ∧
      ∀ i j (s t : Bool),
        G.Adj (if s then a i else b i) (if t then a j else b j) →
          i = j ∧ s ≠ t := by
  classical
  let a : Fin T.card → Fin n := T.orderEmbOfFin rfl
  have ha : ∀ i, a i ∈ T := fun i => T.orderEmbOfFin_mem rfl i
  have hinj : Function.Injective a := (T.orderEmbOfFin rfl).injective
  have hex : ∀ i : Fin T.card, ∃ b,
      G.Adj (a i) b ∧ b ∉ T ∧ ∀ c, G.Adj b c → c = a i :=
    fun i => min_cover_leaf_neighbor G hstar T hT (ha i)
  let b : Fin T.card → Fin n := fun i => Classical.choose (hex i)
  have hspec : ∀ i, G.Adj (a i) (b i) ∧ b i ∉ T ∧
      ∀ c, G.Adj (b i) c → c = a i := fun i => Classical.choose_spec (hex i)
  refine ⟨a, b, fun i => (hspec i).1, ?_⟩
  intro i j s t hij
  cases s <;> cases t
  · change G.Adj (b i) (b j) at hij
    have hmem : b j ∈ T := by rw [(hspec i).2.2 (b j) hij]; exact ha i
    exact False.elim ((hspec j).2.1 hmem)
  · change G.Adj (b i) (a j) at hij
    exact ⟨hinj ((hspec i).2.2 (a j) hij).symm, by decide⟩
  · change G.Adj (a i) (b j) at hij
    exact ⟨hinj ((hspec j).2.2 (a i) hij.symm), by decide⟩
  · change G.Adj (a i) (a j) at hij
    exact False.elim (min_cover_independent G hstar T hT _ (ha i) _ (ha j) hij)

end StarCoverMatching

namespace FreeClauses

lemma clause_count_of_min_cover {n : ℕ} {I : Type*} [Fintype I]
    (G : SimpleGraph (Fin n)) (S : I → Finset (Fin n)) (hrep : Represents G S)
    (hind : ∀ i u, u ∈ S i → ∀ v, v ∈ S i → ¬G.Adj u v)
    (hc4 : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d)
    (T : Finset (Fin n)) (hT : PEqualNP.MetaComplexity.NestedCover.IsMinCover G T) :
    2 ^ T.card ≤ Fintype.card I := by
  obtain ⟨a, b, hedge, hmatching⟩ := StarCoverMatching.induced_matching_of_min_cover G
    (fun _ _ hab => every_edge_has_leaf_endpoint G S hrep hind hc4 hab) T hT
  exact clause_count_of_induced_matching G S hrep a b hedge hmatching

lemma twice_cover_sub_one_le_clauses_sub_one {n : ℕ} {I : Type*} [Fintype I]
    (G : SimpleGraph (Fin n)) (S : I → Finset (Fin n)) (hrep : Represents G S)
    (hind : ∀ i u, u ∈ S i → ∀ v, v ∈ S i → ¬G.Adj u v)
    (hc4 : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d)
    (T : Finset (Fin n)) (hT : PEqualNP.MetaComplexity.NestedCover.IsMinCover G T) :
    2 * T.card - 1 ≤ Fintype.card I - 1 := by
  have hpow := Nat.mul_le_pow (by decide : 2 ≠ 1) T.card
  have hcount := clause_count_of_min_cover G S hrep hind hc4 T hT
  omega

end FreeClauses

namespace AndClauses

open PEqualNP.CircuitLowerBounds

variable {n : ℕ}

lemma getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

/-- The support of a gate: the union of the supports of the wires it reads. -/
def gateSupp (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

lemma mem_foldr_union (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

lemma mem_gateSupp (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

/-- The supports of all wires, starting from the supports `L` of the wires present. -/
def suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

/-- The supports of the input wires: input `i` has support `{i}`. -/
def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

def Cnt (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

lemma cnt_inputs : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

lemma cnt_step (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ g.inputs.toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

lemma cnt_suppsFrom (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, g.inputs.length ≤ 2) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self) h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

def AndSemantics (x : Fin n → Bool) (L : List (Finset (Fin n)))
    (w wy : List Bool) : Prop :=
  L.length = w.length ∧ w.length = wy.length ∧
    ∀ j : ℕ, wy.getD j false = true →
      (w.getD j false = true ↔ ∀ i ∈ L.getD j ∅, x i = true)

lemma andSemantics_inputs (x y : Fin n → Bool) :
    AndSemantics x (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps],by simp,?_⟩
  intro j hj
  by_cases hjn : j < n
  · simp [inputSupps,hjn]
  · simp [List.getD_eq_getElem?_getD,hjn] at hj

lemma andSemantics_run (x : Fin n → Bool) (gs : List Gate)
    (hand : ∀ g ∈ gs, g.op = GateOp.and) :
    ∀ (L : List (Finset (Fin n))) (w wy : List Bool), AndSemantics x L w wy →
      AndSemantics x (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs wy) := by
  induction gs with
  | nil => intro L w wy h; exact h
  | cons g gs ih =>
    intro L w wy h
    obtain ⟨h1,h2,h3⟩ := h
    apply ih (fun g' hg' => hand g' (List.mem_cons_of_mem _ hg'))
      (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (wy ++ [g.op.eval (g.inputs.map fun i => wy.getD i false)])
    refine ⟨by simp [h1],by simp [h2],?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst j
      rw [h1,h2,getD_snoc_eq] at hj
      rw [getD_snoc_eq,h1,getD_snoc_eq]
      have hop := hand g List.mem_cons_self
      have all_y : ∀ a ∈ g.inputs, wy.getD a false = true := by
        simpa [hop,GateOp.eval] using hj
      have all_x : g.op.eval (g.inputs.map fun i => w.getD i false) = true ↔
          ∀ a ∈ g.inputs, w.getD a false = true := by simp [hop,GateOp.eval]
      rw [all_x]
      constructor
      · intro hx i hi
        obtain ⟨a,ha,hia⟩ := (mem_gateSupp L g i).mp hi
        exact (h3 a (all_y a ha)).mp (hx a ha) i hia
      · intro hx a ha
        apply (h3 a (all_y a ha)).mpr
        intro i hi
        exact hx i ((mem_gateSupp L g i).mpr ⟨a,ha,hi⟩)
    · rw [getD_snoc_ne _ _ _ _ (by omega)] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega),getD_snoc_ne _ _ _ _ hjl]
      exact h3 j hj

lemma and_output_support (m : ℕ) (C : Circuit)
    (hand : ∀ g ∈ C.gates, g.op = GateOp.and)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (nonzero : ∃ y : Fin m → Bool, C.eval (List.ofFn y) = true) :
    ∃ R : Finset (Fin m), R.card ≤ C.size + 1 ∧
      ∀ x : Fin m → Bool, C.eval (List.ofFn x) = true ↔ ∀ i ∈ R, x i = true := by
  obtain ⟨y,hy⟩ := nonzero
  let R := (suppsFrom C.gates (inputSupps m)).getD C.output ∅
  refine ⟨R,?_,?_⟩
  · have bound := cnt_suppsFrom C.gates 0 (inputSupps m) hfan cnt_inputs {C.output}
    simpa only [Finset.singleton_biUnion,Finset.card_singleton,zero_add,Circuit.size] using bound
  · intro x
    exact (andSemantics_run x C.gates hand _ _ _ (andSemantics_inputs x y)).2.2 C.output hy

def clauseInput {n m : ℕ} (S : Fin m → Finset (Fin n)) (x : Fin n → Bool) : Fin m → Bool :=
  fun i => decide (∃ v ∈ S i, x v = true)

lemma selected_clauses_represent {n m : ℕ} (G : SimpleGraph (Fin n))
    (S : Fin m → Finset (Fin n)) (C : Circuit)
    (hand : ∀ g ∈ C.gates, g.op = GateOp.and)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (correct : ∀ x : Fin n → Bool,
      C.eval (List.ofFn (clauseInput S x)) = true ↔
        ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
    (nonempty : ∃ u v, G.Adj u v) :
    ∃ R : Finset (Fin m), R.card ≤ C.size + 1 ∧
      FreeClauses.Represents G (fun i : {i : Fin m // i ∈ R} => S i.val) := by
  obtain ⟨a,b,hab⟩ := nonempty
  have nonzero : ∃ y : Fin m → Bool, C.eval (List.ofFn y) = true := by
    refine ⟨clauseInput S (PEqualNP.EdgeOwnership.pairInput a b),(correct _).mpr ?_⟩
    exact ⟨a,b,hab,by simp [PEqualNP.EdgeOwnership.pairInput],by simp [PEqualNP.EdgeOwnership.pairInput]⟩
  obtain ⟨R,bound,repr⟩ := and_output_support m C hand hfan nonzero
  refine ⟨R,bound,?_⟩
  intro x
  constructor
  · intro clauses
    apply (correct x).mp
    apply (repr _).mpr
    intro i hi
    exact decide_eq_true (clauses ⟨i,hi⟩)
  · intro edge
    have all := (repr _).mp ((correct x).mpr edge)
    intro i
    exact of_decide_eq_true (all i.val i.property)

lemma and_gate_bound_of_induced_matching {n m k : ℕ} (G : SimpleGraph (Fin n))
    (S : Fin m → Finset (Fin n)) (C : Circuit)
    (hand : ∀ g ∈ C.gates, g.op = GateOp.and)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (correct : ∀ x : Fin n → Bool,
      C.eval (List.ofFn (clauseInput S x)) = true ↔
        ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
    (nonempty : ∃ u v, G.Adj u v)
    (a b : Fin k → Fin n) (hedge : ∀ j, G.Adj (a j) (b j))
    (hmatching : ∀ i j (s t : Bool),
      G.Adj (if s then a i else b i) (if t then a j else b j) → i = j ∧ s ≠ t) :
    2 ^ k ≤ C.size + 1 := by
  obtain ⟨R,bound,repr⟩ := selected_clauses_represent G S C hand hfan correct nonempty
  have lower := FreeClauses.clause_count_of_induced_matching G
    (fun i : {i : Fin m // i ∈ R} => S i.val) repr a b hedge hmatching
  have lower' : 2 ^ k ≤ R.card := by simpa using lower
  exact lower'.trans bound

lemma and_gate_bound_sub_one {n m k : ℕ} (G : SimpleGraph (Fin n))
    (S : Fin m → Finset (Fin n)) (C : Circuit)
    (hand : ∀ g ∈ C.gates, g.op = GateOp.and)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (correct : ∀ x : Fin n → Bool,
      C.eval (List.ofFn (clauseInput S x)) = true ↔
        ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
    (nonempty : ∃ u v, G.Adj u v)
    (a b : Fin k → Fin n) (hedge : ∀ j, G.Adj (a j) (b j))
    (hmatching : ∀ i j (s t : Bool),
      G.Adj (if s then a i else b i) (if t then a j else b j) → i = j ∧ s ≠ t) :
    2 ^ k - 1 ≤ C.size := by
  have := and_gate_bound_of_induced_matching G S C hand hfan correct nonempty a b hedge hmatching
  omega

end AndClauses

namespace AndClauses

lemma and_gate_bound_of_min_cover {n m : ℕ} (G : SimpleGraph (Fin n))
    (S : Fin m → Finset (Fin n)) (C : Circuit)
    (hand : ∀ g ∈ C.gates, g.op = GateOp.and)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (correct : ∀ x : Fin n → Bool,
      C.eval (List.ofFn (clauseInput S x)) = true ↔
        ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
    (nonempty : ∃ u v, G.Adj u v)
    (hind : ∀ i u, u ∈ S i → ∀ v, v ∈ S i → ¬G.Adj u v)
    (hc4 : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d)
    (T : Finset (Fin n)) (hT : PEqualNP.MetaComplexity.NestedCover.IsMinCover G T) :
    2 ^ T.card - 1 ≤ C.size := by
  obtain ⟨R, bound, repr⟩ := selected_clauses_represent G S C hand hfan correct nonempty
  have lower := FreeClauses.clause_count_of_min_cover G
    (fun i : {i : Fin m // i ∈ R} => S i.val) repr
    (fun i u hu v hv => hind i.val u hu v hv) hc4 T hT
  have lower' : 2 ^ T.card ≤ R.card := by simpa using lower
  omega

lemma twice_cover_sub_one_le_and_gates {n m : ℕ} (G : SimpleGraph (Fin n))
    (S : Fin m → Finset (Fin n)) (C : Circuit)
    (hand : ∀ g ∈ C.gates, g.op = GateOp.and)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (correct : ∀ x : Fin n → Bool,
      C.eval (List.ofFn (clauseInput S x)) = true ↔
        ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
    (nonempty : ∃ u v, G.Adj u v)
    (hind : ∀ i u, u ∈ S i → ∀ v, v ∈ S i → ¬G.Adj u v)
    (hc4 : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d)
    (T : Finset (Fin n)) (hT : PEqualNP.MetaComplexity.NestedCover.IsMinCover G T) :
    2 * T.card - 1 ≤ C.size := by
  have lower := and_gate_bound_of_min_cover G S C hand hfan correct nonempty hind hc4 T hT
  exact (Nat.sub_le_sub_right (Nat.mul_le_pow (by decide : 2 ≠ 1) T.card) 1).trans lower

end AndClauses


namespace PackingClauses

open PEqualNP.Outside.L_meta_1904_aux.FreeClauses

lemma missing_singleton_clause {n : ℕ} {I : Type*}
    (G : SimpleGraph (Fin n)) (S : I → Finset (Fin n)) (hrep : Represents G S)
    (c : Fin n) : ∃ i, c ∉ S i := by
  classical
  have hn : ¬ ∀ i, c ∈ S i := by
    intro h
    exact G.irrefl (pair_edge_of_represents G S hrep (fun i => Or.inl (h i)))
  exact not_forall.mp hn

lemma every_vertex_has_at_most_one_neighbor {n : ℕ} {I : Type*}
    (G : SimpleGraph (Fin n)) (S : I → Finset (Fin n)) (hrep : Represents G S)
    (hpacking : ∀ i c u v, u ∈ S i → v ∈ S i → G.Adj c u → G.Adj c v → u = v) :
    ∀ c u v, G.Adj c u → G.Adj c v → u = v := by
  intro c u v hcu hcv
  obtain ⟨i, hci⟩ := missing_singleton_clause G S hrep c
  have hui : u ∈ S i := (clause_covers_edge G S hrep i hcu).resolve_left hci
  have hvi : v ∈ S i := (clause_covers_edge G S hrep i hcv).resolve_left hci
  exact hpacking i c u v hui hvi hcu hcv

lemma clause_count_of_min_cover {n : ℕ} {I : Type*} [Fintype I]
    (G : SimpleGraph (Fin n)) (S : I → Finset (Fin n)) (hrep : Represents G S)
    (hpacking : ∀ i c u v, u ∈ S i → v ∈ S i → G.Adj c u → G.Adj c v → u = v)
    (T : Finset (Fin n)) (hT : PEqualNP.MetaComplexity.NestedCover.IsMinCover G T) :
    2 ^ T.card ≤ Fintype.card I := by
  have hdegree := every_vertex_has_at_most_one_neighbor G S hrep hpacking
  obtain ⟨a, b, hedge, hmatching⟩ := StarCoverMatching.induced_matching_of_min_cover G
    (fun a b hab => Or.inl (fun c hac => hdegree a c b hac hab)) T hT
  exact clause_count_of_induced_matching G S hrep a b hedge hmatching

lemma twice_cover_sub_one_le_clauses_sub_one {n : ℕ} {I : Type*} [Fintype I]
    (G : SimpleGraph (Fin n)) (S : I → Finset (Fin n)) (hrep : Represents G S)
    (hpacking : ∀ i c u v, u ∈ S i → v ∈ S i → G.Adj c u → G.Adj c v → u = v)
    (T : Finset (Fin n)) (hT : PEqualNP.MetaComplexity.NestedCover.IsMinCover G T) :
    2 * T.card - 1 ≤ Fintype.card I - 1 := by
  have hpow := Nat.mul_le_pow (by decide : 2 ≠ 1) T.card
  have hcount := clause_count_of_min_cover G S hrep hpacking T hT
  omega

end PackingClauses

namespace AndClauses

lemma packing_and_circuit_degree {n m : ℕ} (G : SimpleGraph (Fin n))
    (S : Fin m → Finset (Fin n)) (C : Circuit)
    (hand : ∀ g ∈ C.gates, g.op = GateOp.and)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (correct : ∀ x : Fin n → Bool,
      C.eval (List.ofFn (clauseInput S x)) = true ↔
        ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
    (nonempty : ∃ u v, G.Adj u v)
    (hpacking : ∀ i c u v, u ∈ S i → v ∈ S i → G.Adj c u → G.Adj c v → u = v) :
    ∀ c u v, G.Adj c u → G.Adj c v → u = v := by
  obtain ⟨R, _, repr⟩ := selected_clauses_represent G S C hand hfan correct nonempty
  exact PackingClauses.every_vertex_has_at_most_one_neighbor G
    (fun i : {i : Fin m // i ∈ R} => S i.val) repr
    (fun i c u v hu hv hcu hcv => hpacking i.val c u v hu hv hcu hcv)

lemma packing_circuit_has_or {n m : ℕ} (G : SimpleGraph (Fin n))
    (S : Fin m → Finset (Fin n)) (C : Circuit) (hC : Monotone2 C)
    (correct : ∀ x : Fin n → Bool,
      C.eval (List.ofFn (clauseInput S x)) = true ↔
        ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
    (hpacking : ∀ i c u v, u ∈ S i → v ∈ S i → G.Adj c u → G.Adj c v → u = v)
    (c u v : Fin n) (hcu : G.Adj c u) (hcv : G.Adj c v) (huv : u ≠ v) :
    ∃ g ∈ C.gates, g.op = GateOp.or := by
  classical
  by_contra hnone
  have hand : ∀ g ∈ C.gates, g.op = GateOp.and := by
    intro g hg
    exact ((hC g hg).1 : g.op = GateOp.and ∨ g.op = GateOp.or).resolve_right
      (fun hop => hnone ⟨g, hg, hop⟩)
  exact huv (packing_and_circuit_degree G S C hand (fun g hg => (hC g hg).2)
    correct ⟨c, u, hcu⟩ hpacking c u v hcu hcv)

end AndClauses


namespace StarCoverMatching

open PEqualNP.MetaComplexity.NestedCover

lemma edge_count_eq_min_cover {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hdegree : ∀ c u v, G.Adj c u → G.Adj c v → u = v)
    (T : Finset (Fin n)) (hT : IsMinCover G T) : G.edgeFinset.card = T.card := by
  classical
  have hex : ∀ a : T, ∃ b, G.Adj a.val b ∧ b ∉ T :=
    fun a => min_cover_outside_neighbor G T hT a.property
  let b : T → Fin n := fun a => Classical.choose (hex a)
  have hb : ∀ a : T, G.Adj a.val (b a) ∧ b a ∉ T :=
    fun a => Classical.choose_spec (hex a)
  symm
  refine Finset.card_bij (fun a ha => s(a, b ⟨a, ha⟩)) ?_ ?_ ?_
  · intro a ha
    simpa using (hb ⟨a, ha⟩).1
  · intro a ha c hc heq
    rcases Sym2.eq_iff.mp heq with ⟨hac, _⟩ | ⟨hac, _⟩
    · exact hac
    · exact False.elim ((hb ⟨c, hc⟩).2 (hac ▸ ha))
  · intro e he
    obtain ⟨⟨u, v⟩, rfl⟩ := Sym2.mk_surjective e
    have huv : G.Adj u v := by simpa using he
    rcases hT.1 huv with hu | hv
    · have hbv : b ⟨u, hu⟩ = v := hdegree u _ v (hb ⟨u, hu⟩).1 huv
      exact ⟨u, hu, by rw [hbv]; rfl⟩
    · have hbu : b ⟨v, hv⟩ = u := hdegree v _ u (hb ⟨v, hv⟩).1 huv.symm
      exact ⟨v, hv, by rw [hbu]; exact Sym2.eq_swap⟩

end StarCoverMatching

namespace AndClauses

lemma packing_and_circuit_star_budget {n m : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (S : Fin m → Finset (Fin n)) (C : Circuit)
    (hand : ∀ g ∈ C.gates, g.op = GateOp.and)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (correct : ∀ x : Fin n → Bool,
      C.eval (List.ofFn (clauseInput S x)) = true ↔
        ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
    (nonempty : ∃ u v, G.Adj u v)
    (hpacking : ∀ i c u v, u ∈ S i → v ∈ S i → G.Adj c u → G.Adj c v → u = v)
    (T : Finset (Fin n)) (hT : PEqualNP.MetaComplexity.NestedCover.IsMinCover G T) :
    G.edgeFinset.card + T.card - 1 ≤ C.size := by
  obtain ⟨R, bound, repr⟩ := selected_clauses_represent G S C hand hfan correct nonempty
  have lower := PackingClauses.clause_count_of_min_cover G
    (fun i : {i : Fin m // i ∈ R} => S i.val) repr
    (fun i c u v hu hv hcu hcv => hpacking i.val c u v hu hv hcu hcv) T hT
  have lower' : 2 ^ T.card ≤ R.card := by simpa using lower
  have hdeg := packing_and_circuit_degree G S C hand hfan correct nonempty hpacking
  have hcard := StarCoverMatching.edge_count_eq_min_cover G hdeg T hT
  have hpow := Nat.mul_le_pow (by decide : 2 ≠ 1) T.card
  omega

end AndClauses



namespace HelperSupport

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

variable {n : ℕ}

lemma getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

/-- The support of a gate: the union of the supports of the wires it reads. -/
def gateSupp (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

lemma mem_foldr_union (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

lemma mem_gateSupp (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

/-- The supports of all wires, starting from the supports `L` of the wires present. -/
def suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

/-- The supports of the input wires: input `i` has support `{i}`. -/
def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

/-- Wire lists `w`, `w'` (for the inputs `x`, `y`) agree on every wire whose support `x` and
  `y` agree on. -/
def Agree (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

lemma agree_wiresFrom (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

lemma agree_inputs (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

/-- Any set `W` of wires has a joint support of size at most `t + |W|`. -/
def Cnt (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

lemma cnt_inputs : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

lemma cnt_step (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ g.inputs.toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

lemma cnt_suppsFrom (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, g.inputs.length ≤ 2) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self) h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this


def SeenInputs (L : List (Finset (Fin n))) (gs : List Gate) : Prop :=
  ∀ w : ℕ, ∀ i : Fin n, i ∈ L.getD w ∅ →
    w = i.val ∨ ∃ g ∈ gs, i.val ∈ g.inputs

lemma seen_inputs : SeenInputs (inputSupps n) [] := by
  intro w i hi
  by_cases hw : w < n
  · have hiw : i = ⟨w,hw⟩ := by simpa [inputSupps,hw] using hi
    exact Or.inl (congrArg Fin.val hiw).symm
  · simp [inputSupps,hw] at hi

lemma seen_step (L : List (Finset (Fin n))) (gs : List Gate) (g : Gate)
    (hseen : SeenInputs L gs) : SeenInputs (L ++ [gateSupp L g]) (gs ++ [g]) := by
  intro w i hi
  by_cases hw : w = L.length
  · subst w
    rw [getD_snoc_eq] at hi
    obtain ⟨a,ha,hia⟩ := (mem_gateSupp L g i).mp hi
    rcases hseen a i hia with heq | ⟨q,hq,hinput⟩
    · right
      exact ⟨g,by simp,heq ▸ ha⟩
    · exact Or.inr ⟨q,List.mem_append_left _ hq,hinput⟩
  · rw [getD_snoc_ne _ _ _ _ hw] at hi
    rcases hseen w i hi with heq | ⟨q,hq,hinput⟩
    · exact Or.inl heq
    · exact Or.inr ⟨q,List.mem_append_left _ hq,hinput⟩

lemma seen_suppsFrom (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (pre : List Gate), SeenInputs L pre →
      SeenInputs (suppsFrom gs L) (pre ++ gs) := by
  induction gs with
  | nil => intro L pre h; simpa [suppsFrom] using h
  | cons g gs ih =>
    intro L pre h
    have hnext := ih (L ++ [gateSupp L g]) (pre ++ [g]) (seen_step L pre g h)
    simpa [suppsFrom,List.foldl_cons,List.append_assoc] using hnext

lemma output_support (m : ℕ) (C : Circuit)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    ∃ R : Finset (Fin m), R.card ≤ C.size + 1 ∧
      (∀ x y : Fin m → Bool, (∀ i ∈ R, x i = y i) →
        C.eval (List.ofFn x) = C.eval (List.ofFn y)) ∧
      ∀ i ∈ R, C.output = i.val ∨ ∃ g ∈ C.gates, i.val ∈ g.inputs := by
  let R := (suppsFrom C.gates (inputSupps m)).getD C.output ∅
  refine ⟨R,?_,?_,?_⟩
  · have bound := cnt_suppsFrom C.gates 0 (inputSupps m) hfan cnt_inputs {C.output}
    simpa only [Finset.singleton_biUnion,Finset.card_singleton,zero_add,Circuit.size] using bound
  · intro x y hxy
    exact (agree_wiresFrom x y C.gates _ _ _ (agree_inputs x y)).2.2 C.output hxy
  · intro i hi
    have hseen := seen_suppsFrom C.gates (inputSupps m) [] seen_inputs
    exact hseen C.output i hi

end HelperSupport

namespace HelperSupport

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma output_support_mono (m : ℕ) (C : Circuit) (hC : Monotone2 C) :
    ∃ R : Finset (Fin m), R.card ≤ C.size + 1 ∧
      ∀ x y : Fin m → Bool, (∀ i ∈ R, x i = true → y i = true) →
        C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true := by
  classical
  obtain ⟨R,hcard,hagree,_⟩ := output_support m C (fun g hg => (hC g hg).2)
  refine ⟨R,hcard,?_⟩
  intro x y hxy hx
  let z : Fin m → Bool := fun i => if i ∈ R then y i else x i
  have hxz : ∀ i, x i = true → z i = true := by
    intro i hi
    by_cases hiR : i ∈ R
    · simpa [z,hiR] using hxy i hiR hi
    · simpa [z,hiR] using hi
  have hz : C.eval (List.ofFn z) = true := wires_mono hC hxz C.output hx
  have heq : C.eval (List.ofFn z) = C.eval (List.ofFn y) :=
    hagree z y (fun i hi => by simp [z,hi])
  exact heq ▸ hz

lemma output_support_separates (m : ℕ) (C : Circuit) (hC : Monotone2 C) :
    ∃ R : Finset (Fin m), R.card ≤ C.size + 1 ∧
      ∀ x y : Fin m → Bool, C.eval (List.ofFn x) = true →
        C.eval (List.ofFn y) = false → ∃ i ∈ R, x i = true ∧ y i = false := by
  classical
  obtain ⟨R,hcard,hmono⟩ := output_support_mono m C hC
  refine ⟨R,hcard,?_⟩
  intro x y hx hy
  by_contra h
  have hxy : ∀ i ∈ R, x i = true → y i = true := by
    intro i hi hxi
    cases hyi : y i
    · exact False.elim (h ⟨i,hi,hxi,hyi⟩)
    · rfl
  have := hmono x y hxy hx
  rw [hy] at this
  contradiction

end HelperSupport

namespace MatchingCapacity

variable {I : Type*} [DecidableEq I]

def source (S : Finset (I × Bool)) (x : I × Bool → Bool) : Bool :=
  decide (∃ p ∈ S, x p = true)

def edgeInput (i : I) : I × Bool → Bool :=
  fun p => decide (p.1 = i)

def transversalInput (a : I → Bool) : I × Bool → Bool :=
  fun p => decide (p.2 = a p.1)

def rows (S : Finset (I × Bool)) : Finset I := S.image Prod.fst

lemma source_edge_true (S : Finset (I × Bool)) (i : I) :
    source S (edgeInput i) = true ↔ i ∈ rows S := by
  simp [source, edgeInput, rows, Finset.mem_image]

variable [Fintype I]

def avoiding (S : Finset (I × Bool)) : Finset (I → Bool) :=
  Finset.univ.filter (fun a => ∀ p ∈ S, p.2 ≠ a p.1)

def separations (S : Finset (I × Bool)) : Finset (I × (I → Bool)) :=
  Finset.univ.filter (fun p =>
    source S (edgeInput p.1) = true ∧ source S (transversalInput p.2) = false)

lemma source_transversal_false (S : Finset (I × Bool)) (a : I → Bool) :
    source S (transversalInput a) = false ↔ a ∈ avoiding S := by
  constructor
  · intro hf
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro p hp heq
    have ht : source S (transversalInput a) = true := by
      simp only [source, decide_eq_true_iff]
      exact ⟨p, hp, by simp [transversalInput, heq]⟩
    simp [hf] at ht
  · intro ha
    apply Bool.eq_false_iff.mpr
    intro ht
    have hex : ∃ p ∈ S, transversalInput a p = true := of_decide_eq_true ht
    obtain ⟨p, hp, ht⟩ := hex
    exact (Finset.mem_filter.mp ha).2 p hp (by simpa [transversalInput] using ht)

lemma separations_eq_product (S : Finset (I × Bool)) :
    separations S = rows S ×ˢ avoiding S := by
  ext p
  simp only [separations, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_product]
  exact and_congr (source_edge_true S p.1) (source_transversal_false S p.2)

lemma avoiding_card_le (S : Finset (I × Bool)) :
    (avoiding S).card ≤ 2 ^ (Finset.univ \ rows S).card := by
  classical
  let U : Finset I := Finset.univ \ rows S
  let f : ↥(avoiding S) → (↥U → Bool) := fun a i => a.val i.val
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ rows S
    · obtain ⟨p, hp, hpi⟩ := Finset.mem_image.mp hi
      have ha : p.2 ≠ a.val i := by
        simpa only [hpi] using (Finset.mem_filter.mp a.property).2 p hp
      have hb : p.2 ≠ b.val i := by
        simpa only [hpi] using (Finset.mem_filter.mp b.property).2 p hp
      cases hpa : p.2 <;> cases hai : a.val i <;> cases hbi : b.val i <;> simp_all
    · have hiU : i ∈ U := by simp [U, hi]
      exact congrFun hab ⟨i, hiU⟩
  have hcard := Fintype.card_le_of_injective f hf
  change (avoiding S).card ≤ 2 ^ U.card
  simpa only [Fintype.card_coe, Fintype.card_fun, Fintype.card_bool] using hcard

lemma twice_separations_card_le (S : Finset (I × Bool)) :
    2 * (separations S).card ≤ 2 ^ Fintype.card I := by
  classical
  let r := (rows S).card
  let u := (Finset.univ \ rows S).card
  have hsum : r + u = Fintype.card I := by
    have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (rows S))
    simpa [r, u, Nat.add_comm] using h
  have hneg : (avoiding S).card ≤ 2 ^ u := avoiding_card_le S
  rw [separations_eq_product, Finset.card_product]
  change 2 * (r * (avoiding S).card) ≤ _
  calc
    2 * (r * (avoiding S).card) = (2 * r) * (avoiding S).card := by ac_rfl
    _ ≤ (2 * r) * 2 ^ u := Nat.mul_le_mul_left _ hneg
    _ ≤ 2 ^ r * 2 ^ u := Nat.mul_le_mul_right _ (Nat.mul_le_pow (by decide : 2 ≠ 1) r)
    _ = 2 ^ (r + u) := (Nat.pow_add 2 r u).symm
    _ = 2 ^ Fintype.card I := by rw [hsum]

end MatchingCapacity

namespace SeparationCounting

lemma separation_union_bound {P N M : Type*} [Fintype P] [Fintype N]
    (R : Finset M) (Sep : M → Finset (P × N)) (B : ℕ)
    (covered : ∀ p : P × N, ∃ i ∈ R, p ∈ Sep i)
    (capacity : ∀ i ∈ R, 2 * (Sep i).card ≤ B) :
    2 * (Fintype.card P * Fintype.card N) ≤ R.card * B := by
  classical
  have cover : (Finset.univ : Finset (P × N)) ⊆ R.biUnion Sep := by
    intro p _
    obtain ⟨i,hi,hp⟩ := covered p
    exact Finset.mem_biUnion.mpr ⟨i,hi,hp⟩
  have count : Fintype.card P * Fintype.card N ≤ ∑ i ∈ R, (Sep i).card := by
    have bound := (Finset.card_le_card cover).trans (Finset.card_biUnion_le)
    simpa only [Finset.card_univ,Fintype.card_prod] using bound
  calc
    2 * (Fintype.card P * Fintype.card N) ≤ 2 * (∑ i ∈ R, (Sep i).card) :=
      Nat.mul_le_mul_left 2 count
    _ = ∑ i ∈ R, 2 * (Sep i).card := Finset.mul_sum ..
    _ ≤ ∑ _i ∈ R, B := Finset.sum_le_sum capacity
    _ = R.card * B := by simp

lemma separation_card_bound {P N M : Type*} [Fintype P] [Fintype N]
    (R : Finset M) (Sep : M → Finset (P × N))
    (covered : ∀ p : P × N, ∃ i ∈ R, p ∈ Sep i)
    (capacity : ∀ i ∈ R, 2 * (Sep i).card ≤ Fintype.card N)
    (nonempty : 0 < Fintype.card N) :
    2 * Fintype.card P ≤ R.card := by
  have bound := separation_union_bound R Sep (Fintype.card N) covered capacity
  have product : (2 * Fintype.card P) * Fintype.card N ≤ R.card * Fintype.card N := by
    simpa only [Nat.mul_assoc] using bound
  exact Nat.le_of_mul_le_mul_right product nonempty

end SeparationCounting

namespace MatchingLower

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

variable {I : Type*} [Fintype I] [DecidableEq I] {m : ℕ}

def input (S : Fin m → Finset (I × Bool)) (K : Finset (Fin m))
    (x : I × Bool → Bool) (r : Fin m) : Bool :=
  decide (r ∈ K) || MatchingCapacity.source (S r) x

def target (x : I × Bool → Bool) : Bool :=
  decide (∃ i, x (i,false) = true ∧ x (i,true) = true)

lemma target_edge (i : I) : target (MatchingCapacity.edgeInput i) = true := by
  apply decide_eq_true
  exact ⟨i,by simp [MatchingCapacity.edgeInput],by simp [MatchingCapacity.edgeInput]⟩

omit [DecidableEq I] in
lemma target_transversal (a : I → Bool) :
    target (MatchingCapacity.transversalInput a) = false := by
  simp [target,MatchingCapacity.transversalInput]

lemma input_separation (S : Fin m → Finset (I × Bool)) (K : Finset (Fin m))
    (r : Fin m) (i : I) (a : I → Bool)
    (hp : input S K (MatchingCapacity.edgeInput i) r = true)
    (hn : input S K (MatchingCapacity.transversalInput a) r = false) :
    r ∉ K ∧ (i,a) ∈ MatchingCapacity.separations (S r) := by
  have hK : r ∉ K := by
    intro hr
    simp [input,hr] at hn
  refine ⟨hK,?_⟩
  simp only [input,hK,decide_false,Bool.false_or] at hp hn
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp,hn⟩

lemma separation_cover (S : Fin m → Finset (I × Bool)) (K : Finset (Fin m))
    (C : Circuit) (hC : Monotone2 C)
    (correct : ∀ x : I × Bool → Bool, C.eval (List.ofFn (input S K x)) = target x) :
    ∃ R : Finset (Fin m), R.card ≤ C.size + 1 ∧
      ∀ p : I × (I → Bool), ∃ r ∈ R,
        p ∈ (if r ∈ K then ∅ else MatchingCapacity.separations (S r)) := by
  classical
  obtain ⟨R,hcard,hsep⟩ := HelperSupport.output_support_separates m C hC
  refine ⟨R,hcard,?_⟩
  intro p
  obtain ⟨r,hr,hp,hn⟩ := hsep (input S K (MatchingCapacity.edgeInput p.1))
    (input S K (MatchingCapacity.transversalInput p.2))
    (by rw [correct,target_edge]) (by rw [correct,target_transversal])
  obtain ⟨hK,hmem⟩ := input_separation S K r p.1 p.2 hp hn
  exact ⟨r,hr,by simpa [hK] using hmem⟩

/-- Free OR clauses and free constants cannot lower the paid binary monotone gate
  count below the usual bound for a matching. -/
lemma paid_gate_lower_bound (S : Fin m → Finset (I × Bool)) (K : Finset (Fin m))
    (C : Circuit) (hC : Monotone2 C)
    (correct : ∀ x : I × Bool → Bool, C.eval (List.ofFn (input S K x)) = target x) :
    2 * Fintype.card I ≤ C.size + 1 := by
  classical
  obtain ⟨R,hcard,hcover⟩ := separation_cover S K C hC correct
  apply le_trans (SeparationCounting.separation_card_bound R
    (fun r => if r ∈ K then ∅ else MatchingCapacity.separations (S r)) hcover ?_ ?_) hcard
  · intro r _
    by_cases hr : r ∈ K
    · simp [hr]
    · simpa [hr,Fintype.card_fun] using MatchingCapacity.twice_separations_card_le (S r)
  · simp

end MatchingLower

end PEqualNP.Outside.L_meta_1904_aux
