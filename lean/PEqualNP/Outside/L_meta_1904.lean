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


namespace InducedMatchingRestriction

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

variable {n m k : ℕ}

def graphInput (S : Fin m → Finset (Fin n)) (K : Finset (Fin m))
    (x : Fin n → Bool) (r : Fin m) : Bool :=
  decide (r ∈ K) || decide (∃ v ∈ S r, x v = true)

def liftInput (e : Fin k × Bool → Fin n) (x : Fin k × Bool → Bool) : Fin n → Bool :=
  fun v => decide (∃ p, e p = v ∧ x p = true)

def pullback (e : Fin k × Bool → Fin n) (S : Finset (Fin n)) :
    Finset (Fin k × Bool) := Finset.univ.filter (fun p => e p ∈ S)

lemma source_pullback (e : Fin k × Bool → Fin n) (S : Finset (Fin n))
    (x : Fin k × Bool → Bool) :
    decide (∃ v ∈ S, liftInput e x v = true) = MatchingCapacity.source (pullback e S) x := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_iff, MatchingCapacity.source, pullback,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨v,hv,hx⟩
    obtain ⟨p,hpv,hp⟩ := of_decide_eq_true hx
    exact ⟨p,hpv ▸ hv,hp⟩
  · rintro ⟨p,hp,hx⟩
    exact ⟨e p,hp,decide_eq_true ⟨p,rfl,hx⟩⟩

lemma graphInput_pullback (e : Fin k × Bool → Fin n)
    (S : Fin m → Finset (Fin n)) (K : Finset (Fin m)) (x : Fin k × Bool → Bool) :
    graphInput S K (liftInput e x) = MatchingLower.input (fun r => pullback e (S r)) K x := by
  funext r
  simp only [graphInput,MatchingLower.input,source_pullback]

lemma edge_target (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (e : Fin k × Bool → Fin n)
    (hmatch : ∀ i j (s t : Bool), G.Adj (e (i,s)) (e (j,t)) ↔ i = j ∧ s ≠ t)
    (x : Fin k × Bool → Bool) :
    decide (∃ u v, G.Adj u v ∧ liftInput e x u = true ∧ liftInput e x v = true) =
      MatchingLower.target x := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_iff,MatchingLower.target]
  constructor
  · rintro ⟨u,v,huv,hu,hv⟩
    obtain ⟨⟨i,s⟩,rfl,hp⟩ := of_decide_eq_true hu
    obtain ⟨⟨j,t⟩,rfl,hq⟩ := of_decide_eq_true hv
    obtain ⟨rfl,hst⟩ := (hmatch i j s t).mp huv
    cases s <;> cases t
    · exact False.elim (hst rfl)
    · exact ⟨i,hp,hq⟩
    · exact ⟨i,hq,hp⟩
    · exact False.elim (hst rfl)
  · rintro ⟨i,hi0,hi1⟩
    refine ⟨e (i,false),e (i,true),(hmatch i i false true).mpr ⟨rfl,by decide⟩,?_,?_⟩
    · exact decide_eq_true ⟨(i,false),rfl,hi0⟩
    · exact decide_eq_true ⟨(i,true),rfl,hi1⟩

lemma paid_gate_lower_bound (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Fin m → Finset (Fin n)) (K : Finset (Fin m)) (C : Circuit) (hC : Monotone2 C)
    (correct : ∀ x : Fin n → Bool, C.eval (List.ofFn (graphInput S K x)) =
      decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true))
    (e : Fin k × Bool → Fin n)
    (hmatch : ∀ i j (s t : Bool), G.Adj (e (i,s)) (e (j,t)) ↔ i = j ∧ s ≠ t) :
    2 * k ≤ C.size + 1 := by
  have hrestricted : ∀ x : Fin k × Bool → Bool,
      C.eval (List.ofFn (MatchingLower.input (fun r => pullback e (S r)) K x)) =
        MatchingLower.target x := by
    intro x
    rw [←graphInput_pullback e S K x,correct,edge_target G e hmatch x]
  simpa only [Fintype.card_fin] using
    MatchingLower.paid_gate_lower_bound (fun r => pullback e (S r)) K C hC hrestricted

lemma lower_bound_of_induced_matching (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Fin m → Finset (Fin n)) (K : Finset (Fin m)) (C : Circuit) (hC : Monotone2 C)
    (correct : ∀ x : Fin n → Bool, C.eval (List.ofFn (graphInput S K x)) =
      decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true))
    (a b : Fin k → Fin n) (hedge : ∀ i, G.Adj (a i) (b i))
    (hmatching : ∀ i j (s t : Bool),
      G.Adj (if s then a i else b i) (if t then a j else b j) → i = j ∧ s ≠ t) :
    2 * k ≤ C.size + 1 := by
  apply paid_gate_lower_bound G S K C hC correct (fun p => if p.2 then a p.1 else b p.1)
  intro i j s t
  constructor
  · exact hmatching i j s t
  · rintro ⟨rfl,hst⟩
    cases s <;> cases t
    · exact False.elim (hst rfl)
    · exact (hedge i).symm
    · exact hedge i
    · exact False.elim (hst rfl)

end InducedMatchingRestriction


namespace TwoSingletonRepair

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma gatePrefix_or {n : ℕ} (pre : List Gate) (u w : Fin n) (x : Fin n → Bool) :
    gatePrefix pre ⟨.or, [u.val, w.val]⟩ x = (x u || x w) := by
  simp only [gatePrefix, GateOp.eval, List.map_cons, List.map_nil, List.any_cons,
    List.any_nil, id_eq, Bool.or_false]
  rw [run_input pre x u, run_input pre x w]

lemma two_singleton_circuit_repair {n : ℕ} (G : SimpleGraph (Fin n))
    (pre post : List Gate) (g : Gate) (out : ℕ)
    (hc : Monotone2 (patchCircuit pre post g out))
    (correct : ∀ x : Fin n → Bool,
      (patchCircuit pre post g out).eval (List.ofFn x) = true ↔ hit G x)
    (u w : Fin n)
    (hu : gatePrefix pre g (mask {u}) = true)
    (hw : gatePrefix pre g (mask {w}) = true)
    (critical : ∀ a b, G.Adj a b →
      (patchCircuit pre post ⟨.or, []⟩ out).eval (List.ofFn (mask {a, b})) = false →
        a = u ∨ b = u ∨ a = w ∨ b = w) :
    let C := patchCircuit pre post g out
    let D := patchCircuit pre post ⟨.or, [u.val, w.val]⟩ out
    Monotone2 D ∧ D.size = C.size ∧
    (∀ x : Fin n → Bool, D.eval (List.ofFn x) = true ↔ hit G x) ∧
    (∀ x : Fin n → Bool, WireLE (D.wires (List.ofFn x)) (C.wires (List.ofFn x))) ∧
    D.gates[pre.length]? = some ⟨.or, [u.val, w.val]⟩ := by
  dsimp only
  have hpre : ∀ q ∈ pre, q.op = GateOp.and ∨ q.op = GateOp.or := by
    intro q hq
    exact (hc q (List.mem_append_left _ hq)).1
  have hg : g.op = GateOp.and ∨ g.op = GateOp.or :=
    (hc g (List.mem_append_right _ List.mem_cons_self)).1
  have dominated : ∀ x : Fin n → Bool,
      gatePrefix pre ⟨.or, [u.val, w.val]⟩ x = true → gatePrefix pre g x = true := by
    intro x hx
    rw [gatePrefix_or] at hx
    simp only [Bool.or_eq_true] at hx
    rcases hx with hxu | hxw
    · apply gatePrefix_mono pre g hpre hg (mask {u}) x ?_ hu
      intro i hi
      have hiu : i = u := by simpa [mask] using hi
      subst i
      exact hxu
    · apply gatePrefix_mono pre g hpre hg (mask {w}) x ?_ hw
      intro i hi
      have hiw : i = w := by simpa [mask] using hi
      subst i
      exact hxw
  have keeps : ∀ a b, G.Adj a b →
      (patchCircuit pre post ⟨.or, []⟩ out).eval (List.ofFn (mask {a, b})) = false →
        gatePrefix pre ⟨.or, [u.val, w.val]⟩ (mask {a, b}) = true := by
    intro a b hab hz
    rw [gatePrefix_or]
    rcases critical a b hab hz with rfl | rfl | rfl | rfl <;> simp [mask]
  obtain ⟨hm, hs, he, hl⟩ := critical_gate_repair G pre post g
    ⟨.or, [u.val, w.val]⟩ out hc ⟨Or.inr rfl, by simp⟩ correct dominated keeps
  exact ⟨hm, hs, he, hl, by simp [patchCircuit]⟩

end TwoSingletonRepair



namespace OverlapAndCover

lemma rectangular_relation_star {X Y : Type*} (R : X → Y → Prop)
    (rectangle : ∀ a b c d, R a b → R c d → R a d)
    (noSquare : ∀ a c b d, R a b → R c b → R c d → R a d → a = c ∨ b = d) :
    (∀ a b, ¬R a b) ∨
      (∃ a₀, ∀ a b, R a b → a = a₀) ∨ (∃ b₀, ∀ a b, R a b → b = b₀) := by
  classical
  by_cases nonempty : ∃ a b, R a b
  · obtain ⟨a₀,b₀,base⟩ := nonempty
    by_cases sameLeft : ∀ a, R a b₀ → a = a₀
    · exact Or.inr (Or.inl ⟨a₀,fun a b hab => sameLeft a (rectangle a b a₀ b₀ hab base)⟩)
    · push Not at sameLeft
      obtain ⟨a₁,other,different⟩ := sameLeft
      refine Or.inr (Or.inr ⟨b₀,?_⟩)
      intro a b hab
      rcases noSquare a₀ a₁ b₀ b base other
          (rectangle a₁ b₀ a b other hab) (rectangle a₀ b₀ a b base hab) with ha | hb
      · exact False.elim (different ha.symm)
      · exact hb.symm
  · exact Or.inl (fun a b hab => nonempty ⟨a,b,hab⟩)

lemma cover_of_rectangular_cross {I X Y : Type*} [Fintype I]
    (G : SimpleGraph (I ⊕ (X ⊕ Y)))
    (noLeft : ∀ a b : X, ¬G.Adj (Sum.inr (Sum.inl a)) (Sum.inr (Sum.inl b)))
    (noRight : ∀ a b : Y, ¬G.Adj (Sum.inr (Sum.inr a)) (Sum.inr (Sum.inr b)))
    (rectangle : ∀ a b c d, G.Adj (Sum.inr (Sum.inl a)) (Sum.inr (Sum.inr b)) →
      G.Adj (Sum.inr (Sum.inl c)) (Sum.inr (Sum.inr d)) →
      G.Adj (Sum.inr (Sum.inl a)) (Sum.inr (Sum.inr d)))
    (noSquare : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) :
    ∃ T : Finset (I ⊕ (X ⊕ Y)), T.card ≤ Fintype.card I + 1 ∧
      ∀ a b, G.Adj a b → a ∈ T ∨ b ∈ T := by
  classical
  let R (a : X) (b : Y) := G.Adj (Sum.inr (Sum.inl a)) (Sum.inr (Sum.inr b))
  have noSquareR : ∀ a c b d, R a b → R c b → R c d → R a d → a = c ∨ b = d := by
    intro a c b d hab hcb hcd had
    have result := noSquare (Sum.inr (Sum.inl a)) (Sum.inr (Sum.inr b))
      (Sum.inr (Sum.inl c)) (Sum.inr (Sum.inr d)) hab hcb.symm hcd had.symm
    simpa only [Sum.inr.injEq,Sum.inl.injEq] using result
  have crosses : ∃ W : Finset (I ⊕ (X ⊕ Y)), W.card ≤ 1 ∧
      ∀ a b, R a b → Sum.inr (Sum.inl a) ∈ W ∨ Sum.inr (Sum.inr b) ∈ W := by
    rcases rectangular_relation_star R rectangle noSquareR with empty | ⟨a₀,left⟩ | ⟨b₀,right⟩
    · exact ⟨∅,by simp,fun a b hab => False.elim (empty a b hab)⟩
    · refine ⟨{Sum.inr (Sum.inl a₀)},by simp,?_⟩
      intro a b hab
      exact Or.inl (by simp [left a b hab])
    · refine ⟨{Sum.inr (Sum.inr b₀)},by simp,?_⟩
      intro a b hab
      exact Or.inr (by simp [right a b hab])
  obtain ⟨W,small,crosses⟩ := crosses
  let shared : Finset (I ⊕ (X ⊕ Y)) := Finset.univ.image Sum.inl
  have sharedBound : shared.card ≤ Fintype.card I := by
    exact (Finset.card_image_le).trans_eq Finset.card_univ
  refine ⟨shared ∪ W,?_,?_⟩
  · have bound := Finset.card_union_le shared W
    omega
  · intro a b hab
    cases a with
    | inl i => exact Or.inl (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩))
    | inr a =>
      cases b with
      | inl i => exact Or.inr (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩))
      | inr b =>
        cases a with
        | inl a =>
          cases b with
          | inl b => exact False.elim (noLeft a b hab)
          | inr b =>
            rcases crosses a b hab with ha | hb
            · exact Or.inl (Finset.mem_union_right _ ha)
            · exact Or.inr (Finset.mem_union_right _ hb)
        | inr a =>
          cases b with
          | inl b =>
            rcases crosses b a hab.symm with hb | ha
            · exact Or.inr (Finset.mem_union_right _ hb)
            · exact Or.inl (Finset.mem_union_right _ ha)
          | inr b => exact False.elim (noRight a b hab)

def pairInput {V : Type*} [DecidableEq V] (a b : V) (v : V) : Bool := decide (v = a ∨ v = b)

def unitInput {V : Type*} [DecidableEq V] (a : V) (v : V) : Bool := decide (v = a)

lemma pair_edge_iff {V : Type*} [DecidableEq V] (G : SimpleGraph V) (a b : V) :
    (∃ u v, G.Adj u v ∧ pairInput a b u = true ∧ pairInput a b v = true) ↔ G.Adj a b := by
  constructor
  · rintro ⟨u,v,huv,hu,hv⟩
    have hu' : u = a ∨ u = b := of_decide_eq_true hu
    have hv' : v = a ∨ v = b := of_decide_eq_true hv
    rcases hu' with rfl | rfl <;> rcases hv' with rfl | rfl
    · exact False.elim (G.irrefl huv)
    · exact huv
    · exact huv.symm
    · exact False.elim (G.irrefl huv)
  · intro hab
    exact ⟨a,b,hab,by simp [pairInput],by simp [pairInput]⟩

lemma and_factor_cover {I X Y : Type*} [Fintype I]
    (G : SimpleGraph (I ⊕ (X ⊕ Y)))
    (L : (I → Bool) → (X → Bool) → Bool)
    (R : (I → Bool) → (Y → Bool) → Bool)
    (leftZero : L (fun _ => false) (fun _ => false) = false)
    (rightZero : R (fun _ => false) (fun _ => false) = false)
    (correct : ∀ x : I ⊕ (X ⊕ Y) → Bool,
      (L (fun i => x (Sum.inl i)) (fun a => x (Sum.inr (Sum.inl a))) &&
        R (fun i => x (Sum.inl i)) (fun b => x (Sum.inr (Sum.inr b)))) = true ↔
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
    (noSquare : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) :
    ∃ T : Finset (I ⊕ (X ⊕ Y)), T.card ≤ Fintype.card I + 1 ∧
      ∀ a b, G.Adj a b → a ∈ T ∨ b ∈ T := by
  classical
  have noLeft (a b : X) : ¬G.Adj (Sum.inr (Sum.inl a)) (Sum.inr (Sum.inl b)) := by
    intro hab
    have yes := (correct (pairInput (Sum.inr (Sum.inl a)) (Sum.inr (Sum.inl b)))).mpr
      ((pair_edge_iff G _ _).mpr hab)
    simp [pairInput,rightZero] at yes
  have noRight (a b : Y) : ¬G.Adj (Sum.inr (Sum.inr a)) (Sum.inr (Sum.inr b)) := by
    intro hab
    have yes := (correct (pairInput (Sum.inr (Sum.inr a)) (Sum.inr (Sum.inr b)))).mpr
      ((pair_edge_iff G _ _).mpr hab)
    simp [pairInput,leftZero] at yes
  have cross (a : X) (b : Y) :
      G.Adj (Sum.inr (Sum.inl a)) (Sum.inr (Sum.inr b)) ↔
        L (fun _ => false) (unitInput a) = true ∧ R (fun _ => false) (unitInput b) = true := by
    have h := correct (pairInput (Sum.inr (Sum.inl a)) (Sum.inr (Sum.inr b)))
    rw [pair_edge_iff] at h
    change G.Adj (Sum.inr (Sum.inl a)) (Sum.inr (Sum.inr b)) ↔
      L (fun _ => false) (fun a' => decide (a' = a)) = true ∧
      R (fun _ => false) (fun b' => decide (b' = b)) = true
    simpa [pairInput] using h.symm
  apply cover_of_rectangular_cross G noLeft noRight ?_ noSquare
  intro a b c d hab hcd
  exact (cross a d).mpr ⟨((cross a b).mp hab).1,((cross c d).mp hcd).2⟩

lemma one_shared_vertex_cover {X Y : Type*}
    (G : SimpleGraph (Unit ⊕ (X ⊕ Y)))
    (L : (Unit → Bool) → (X → Bool) → Bool)
    (R : (Unit → Bool) → (Y → Bool) → Bool)
    (leftZero : L (fun _ => false) (fun _ => false) = false)
    (rightZero : R (fun _ => false) (fun _ => false) = false)
    (correct : ∀ x : Unit ⊕ (X ⊕ Y) → Bool,
      (L (fun i => x (Sum.inl i)) (fun a => x (Sum.inr (Sum.inl a))) &&
        R (fun i => x (Sum.inl i)) (fun b => x (Sum.inr (Sum.inr b)))) = true ↔
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
    (noSquare : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) :
    ∃ T : Finset (Unit ⊕ (X ⊕ Y)), T.card ≤ 2 ∧
      ∀ a b, G.Adj a b → a ∈ T ∨ b ∈ T := by
  simpa using and_factor_cover G L R leftZero rightZero correct noSquare

end OverlapAndCover

namespace OverlapAndCover

/-- If the left factor ignores `b` and the right factor ignores `a`,
    every neighbor of `a` is adjacent to every neighbor of `b`. -/
lemma ignored_vertices_neighborhood_rectangle {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (L R : (V → Bool) → Bool) (a b : V)
    (correct : ∀ x, (L x && R x) = true ↔
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
    (ignoresLeft : ∀ x, L (Function.update x b true) = L x)
    (ignoresRight : ∀ x, R (Function.update x a true) = R x)
    {c d : V} (hac : G.Adj a c) (hbd : G.Adj b d) : G.Adj c d := by
  have leftPositive : L (pairInput c d) = true := by
    have positive := (correct (Function.update (pairInput c d) b true)).mpr
      ⟨b,d,hbd,by simp,by
        by_cases h : d = b
        · subst d; simp
        · simp [Function.update_of_ne h,pairInput]⟩
    have value : L (Function.update (pairInput c d) b true) = true ∧
        R (Function.update (pairInput c d) b true) = true := by simpa using positive
    simpa only [ignoresLeft] using value.1
  have rightPositive : R (pairInput c d) = true := by
    have positive := (correct (Function.update (pairInput c d) a true)).mpr
      ⟨a,c,hac,by simp,by
        by_cases h : c = a
        · subst c; simp
        · simp [Function.update_of_ne h,pairInput]⟩
    have value : L (Function.update (pairInput c d) a true) = true ∧
        R (Function.update (pairInput c d) a true) = true := by simpa using positive
    simpa only [ignoresRight] using value.2
  exact (pair_edge_iff G c d).mp ((correct (pairInput c d)).mp
    (by simp [leftPositive,rightPositive]))

/-- An edge between variables invisible to the opposite AND factors
    has a leaf endpoint whenever the graph has no four-cycle. -/
lemma ignored_edge_has_leaf {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (L R : (V → Bool) → Bool) (a b : V)
    (correct : ∀ x, (L x && R x) = true ↔
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
    (ignoresLeft : ∀ x, L (Function.update x b true) = L x)
    (ignoresRight : ∀ x, R (Function.update x a true) = R x)
    (noSquare : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d)
    (hab : G.Adj a b) :
    (∀ c, G.Adj a c → c = b) ∨ (∀ d, G.Adj b d → d = a) := by
  classical
  by_cases leftLeaf : ∀ c, G.Adj a c → c = b
  · exact Or.inl leftLeaf
  · push Not at leftLeaf
    obtain ⟨c,hac,hcb⟩ := leftLeaf
    refine Or.inr ?_
    intro d hbd
    have hcd := ignored_vertices_neighborhood_rectangle G L R a b
      correct ignoresLeft ignoresRight hac hbd
    rcases noSquare a b d c hab hbd hcd.symm hac.symm with had | hbc
    · exact had.symm
    · exact False.elim (hcb hbc.symm)

/-- No finiteness, monotonicity, or zero-preservation hypotheses are needed:
    exact AND factorization alone makes a private cross-edge incident to a leaf. -/
lemma private_cross_edge_has_leaf {I X Y : Type*}
    (G : SimpleGraph (I ⊕ (X ⊕ Y)))
    (L : (I → Bool) → (X → Bool) → Bool)
    (R : (I → Bool) → (Y → Bool) → Bool)
    (correct : ∀ x : I ⊕ (X ⊕ Y) → Bool,
      (L (fun i => x (Sum.inl i)) (fun a => x (Sum.inr (Sum.inl a))) &&
        R (fun i => x (Sum.inl i)) (fun b => x (Sum.inr (Sum.inr b)))) = true ↔
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
    (noSquare : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d)
    (a : X) (b : Y) (hab : G.Adj (Sum.inr (Sum.inl a)) (Sum.inr (Sum.inr b))) :
    (∀ c, G.Adj (Sum.inr (Sum.inl a)) c → c = Sum.inr (Sum.inr b)) ∨
    (∀ d, G.Adj (Sum.inr (Sum.inr b)) d → d = Sum.inr (Sum.inl a)) := by
  classical
  apply ignored_edge_has_leaf G
    (fun x => L (fun i => x (Sum.inl i)) (fun a => x (Sum.inr (Sum.inl a))))
    (fun x => R (fun i => x (Sum.inl i)) (fun b => x (Sum.inr (Sum.inr b))))
    (Sum.inr (Sum.inl a)) (Sum.inr (Sum.inr b)) correct ?_ ?_ noSquare hab
  · intro x
    simp [Function.update]
  · intro x
    simp [Function.update]


/-- In a graph without leaf vertices, every edge of a zero-preserving
    factorization touches the shared block. Isolated vertices are allowed. -/
lemma shared_block_covers_of_no_leaves {I X Y : Type*}
    (G : SimpleGraph (I ⊕ (X ⊕ Y)))
    (L : (I → Bool) → (X → Bool) → Bool)
    (R : (I → Bool) → (Y → Bool) → Bool)
    (leftZero : L (fun _ => false) (fun _ => false) = false)
    (rightZero : R (fun _ => false) (fun _ => false) = false)
    (correct : ∀ x : I ⊕ (X ⊕ Y) → Bool,
      (L (fun i => x (Sum.inl i)) (fun a => x (Sum.inr (Sum.inl a))) &&
        R (fun i => x (Sum.inl i)) (fun b => x (Sum.inr (Sum.inr b)))) = true ↔
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
    (noSquare : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d)
    (noLeaves : ∀ a b, G.Adj a b → ∃ c, G.Adj a c ∧ c ≠ b) :
    ∀ a b, G.Adj a b → (∃ i, a = Sum.inl i) ∨ (∃ i, b = Sum.inl i) := by
  classical
  have noCross (a : X) (b : Y) : ¬G.Adj (Sum.inr (Sum.inl a)) (Sum.inr (Sum.inr b)) := by
    intro hab
    rcases private_cross_edge_has_leaf G L R correct noSquare a b hab with left | right
    · obtain ⟨c,hac,hcb⟩ := noLeaves _ _ hab
      exact hcb (left c hac)
    · obtain ⟨d,hbd,hda⟩ := noLeaves _ _ hab.symm
      exact hda (right d hbd)
  intro a b hab
  cases a with
  | inl i => exact Or.inl ⟨i,rfl⟩
  | inr a =>
    cases b with
    | inl i => exact Or.inr ⟨i,rfl⟩
    | inr b =>
      cases a with
      | inl a =>
        cases b with
        | inl b =>
          have yes := (correct (pairInput (Sum.inr (Sum.inl a)) (Sum.inr (Sum.inl b)))).mpr
            ((pair_edge_iff G _ _).mpr hab)
          simp [pairInput,rightZero] at yes
        | inr b => exact False.elim (noCross a b hab)
      | inr a =>
        cases b with
        | inl b => exact False.elim (noCross b a hab.symm)
        | inr b =>
          have yes := (correct (pairInput (Sum.inr (Sum.inr a)) (Sum.inr (Sum.inr b)))).mpr
            ((pair_edge_iff G _ _).mpr hab)
          simp [pairInput,leftZero] at yes

lemma and_factor_cover_of_no_leaves {I X Y : Type*} [Fintype I]
    (G : SimpleGraph (I ⊕ (X ⊕ Y)))
    (L : (I → Bool) → (X → Bool) → Bool)
    (R : (I → Bool) → (Y → Bool) → Bool)
    (leftZero : L (fun _ => false) (fun _ => false) = false)
    (rightZero : R (fun _ => false) (fun _ => false) = false)
    (correct : ∀ x : I ⊕ (X ⊕ Y) → Bool,
      (L (fun i => x (Sum.inl i)) (fun a => x (Sum.inr (Sum.inl a))) &&
        R (fun i => x (Sum.inl i)) (fun b => x (Sum.inr (Sum.inr b)))) = true ↔
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
    (noSquare : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d)
    (noLeaves : ∀ a b, G.Adj a b → ∃ c, G.Adj a c ∧ c ≠ b) :
    ∃ T : Finset (I ⊕ (X ⊕ Y)), T.card ≤ Fintype.card I ∧
      ∀ a b, G.Adj a b → a ∈ T ∨ b ∈ T := by
  classical
  refine ⟨Finset.univ.image Sum.inl,?_,?_⟩
  · exact Finset.card_image_le.trans_eq Finset.card_univ
  · intro a b hab
    rcases shared_block_covers_of_no_leaves G L R leftZero rightZero correct noSquare noLeaves
      a b hab with ⟨i,rfl⟩ | ⟨i,rfl⟩
    · exact Or.inl (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
    · exact Or.inr (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)


/-- Private variables on opposite sides of an OR factorization cannot be adjacent. -/
lemma ignored_vertices_or_not_adjacent {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (L R : (V → Bool) → Bool) (a b : V)
    (correct : ∀ x, (L x || R x) = true ↔
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
    (ignoresLeft : ∀ x, L (Function.update x b true) = L x)
    (ignoresRight : ∀ x, R (Function.update x a true) = R x) : ¬G.Adj a b := by
  have singletonFalse (v : V) : L (pairInput v v) = false ∧ R (pairInput v v) = false := by
    have bad : ¬(L (pairInput v v) || R (pairInput v v)) = true := by
      intro yes
      exact G.irrefl ((pair_edge_iff G v v).mp ((correct (pairInput v v)).mp yes))
    cases hL : L (pairInput v v) <;> cases hR : R (pairInput v v) <;> simp_all
  have updateLeft : Function.update (pairInput a a) b true = pairInput a b := by
    funext v
    by_cases h : v = b <;> simp [Function.update,pairInput,h]
  have updateRight : Function.update (pairInput b b) a true = pairInput a b := by
    funext v
    by_cases h : v = a <;> simp [Function.update,pairInput,h]
  have leftFalse : L (pairInput a b) = false := by
    rw [←updateLeft,ignoresLeft]
    exact (singletonFalse a).1
  have rightFalse : R (pairInput a b) = false := by
    rw [←updateRight,ignoresRight]
    exact (singletonFalse b).2
  intro hab
  have yes := (correct (pairInput a b)).mpr ((pair_edge_iff G a b).mpr hab)
  simp [leftFalse,rightFalse] at yes

end OverlapAndCover

namespace PathRepair

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def oldValue (a b c d e : Bool) : Bool :=
  (b || d) && (c || (((a || e) && (e || b)) && (a || d)))

def newValue (a b c d e : Bool) : Bool :=
  (b && (a || c)) || (d && (c || e))

lemma five_gate_identity (a b c d e : Bool) : oldValue a b c d e = newValue a b c d e := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> rfl

lemma new_ands_safe {X : Type*} (a b c d e : X → Bool) (P : X → Prop)
    (hsafe : ∀ x, oldValue (a x) (b x) (c x) (d x) (e x) = true → P x) :
    (∀ x, (b x && (a x || c x)) = true → P x) ∧
    (∀ x, (d x && (c x || e x)) = true → P x) := by
  constructor
  · intro x hx
    apply hsafe x
    rw [five_gate_identity]
    simp only [newValue, Bool.or_eq_true]
    exact Or.inl hx
  · intro x hx
    apply hsafe x
    rw [five_gate_identity]
    simp only [newValue, Bool.or_eq_true]
    exact Or.inr hx

end PathRepair

namespace PathRepair

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def oldBlock {m : ℕ} (b c d ae eb ad : Fin m) : Circuit :=
  ⟨[⟨.or, [b.val, d.val]⟩,
    ⟨.and, [ae.val, eb.val]⟩,
    ⟨.and, [m + 1, ad.val]⟩,
    ⟨.or, [c.val, m + 2]⟩,
    ⟨.and, [m, m + 3]⟩], m + 4⟩

def newBlock {m : ℕ} (a b c d e : Fin m) : Circuit :=
  ⟨[⟨.or, [a.val, c.val]⟩,
    ⟨.and, [b.val, m]⟩,
    ⟨.or, [c.val, e.val]⟩,
    ⟨.and, [d.val, m + 2]⟩,
    ⟨.or, [m + 1, m + 3]⟩], m + 4⟩

lemma oldBlock_eval {m : ℕ} (b c d ae eb ad : Fin m) (x : Fin m → Bool) :
    (oldBlock b c d ae eb ad).eval (List.ofFn x) =
      ((x b || x d) && (x c || ((x ae && x eb) && x ad))) := by
  have hlen : (List.ofFn x).length = m := List.length_ofFn
  simp (disch := omega) [hlen, oldBlock, Circuit.eval, Circuit.wires, GateOp.eval,
    List.getD_eq_getElem?_getD, List.getElem?_append_left, List.getElem?_append_right]
  rfl

lemma newBlock_eval {m : ℕ} (a b c d e : Fin m) (x : Fin m → Bool) :
    (newBlock a b c d e).eval (List.ofFn x) =
      newValue (x a) (x b) (x c) (x d) (x e) := by
  have hlen : (List.ofFn x).length = m := List.length_ofFn
  simp (disch := omega) [hlen, newBlock, Circuit.eval, Circuit.wires, GateOp.eval, newValue,
    List.getD_eq_getElem?_getD, List.getElem?_append_left, List.getElem?_append_right]
  rfl

lemma blocks_agree {m : ℕ} (a b c d e ae eb ad : Fin m) (x : Fin m → Bool)
    (hae : x ae = (x a || x e)) (heb : x eb = (x e || x b))
    (had : x ad = (x a || x d)) :
    (oldBlock b c d ae eb ad).eval (List.ofFn x) =
      (newBlock a b c d e).eval (List.ofFn x) := by
  rw [oldBlock_eval, newBlock_eval, hae, heb, had]
  exact five_gate_identity (x a) (x b) (x c) (x d) (x e)

lemma oldBlock_size {m : ℕ} (b c d ae eb ad : Fin m) :
    (oldBlock b c d ae eb ad).size = 5 := rfl

lemma newBlock_size {m : ℕ} (a b c d e : Fin m) :
    (newBlock a b c d e).size = 5 := rfl

lemma oldBlock_monotone {m : ℕ} (b c d ae eb ad : Fin m) :
    Monotone2 (oldBlock b c d ae eb ad) := by
  simp [Monotone2, oldBlock]

lemma newBlock_monotone {m : ℕ} (a b c d e : Fin m) :
    Monotone2 (newBlock a b c d e) := by
  simp [Monotone2, newBlock]

lemma newBlock_and_left {m : ℕ} (a b c d e : Fin m) (x : Fin m → Bool) :
    ((newBlock a b c d e).wires (List.ofFn x)).getD (m + 1) false =
      (x b && (x a || x c)) := by
  have hlen : (List.ofFn x).length = m := List.length_ofFn
  simp (disch := omega) [hlen, newBlock, Circuit.wires, GateOp.eval,
    List.getD_eq_getElem?_getD, List.getElem?_append_left, List.getElem?_append_right]
  rfl

lemma newBlock_and_right {m : ℕ} (a b c d e : Fin m) (x : Fin m → Bool) :
    ((newBlock a b c d e).wires (List.ofFn x)).getD (m + 3) false =
      (x d && (x c || x e)) := by
  have hlen : (List.ofFn x).length = m := List.length_ofFn
  simp (disch := omega) [hlen, newBlock, Circuit.wires, GateOp.eval,
    List.getD_eq_getElem?_getD, List.getElem?_append_left, List.getElem?_append_right]
  rfl

lemma newBlock_and_safety {m : ℕ} (a b c d e ae eb ad : Fin m) (x : Fin m → Bool)
    (hae : x ae = (x a || x e)) (heb : x eb = (x e || x b))
    (had : x ad = (x a || x d)) (P : Prop)
    (hsafe : (oldBlock b c d ae eb ad).eval (List.ofFn x) = true → P) :
    (((newBlock a b c d e).wires (List.ofFn x)).getD (m + 1) false = true → P) ∧
    (((newBlock a b c d e).wires (List.ofFn x)).getD (m + 3) false = true → P) := by
  have hnew : (newBlock a b c d e).eval (List.ofFn x) = true → P :=
    fun hx => hsafe ((blocks_agree a b c d e ae eb ad x hae heb had).trans hx)
  constructor
  · intro hx
    apply hnew
    rw [newBlock_eval]
    simp only [newValue, Bool.or_eq_true]
    exact Or.inl (by simpa only [newBlock_and_left] using hx)
  · intro hx
    apply hnew
    rw [newBlock_eval]
    simp only [newValue, Bool.or_eq_true]
    exact Or.inr (by simpa only [newBlock_and_right] using hx)

lemma newBlock_and_indices {m : ℕ} (a b c d e : Fin m) (j : ℕ) (g : Gate)
    (hj : (newBlock a b c d e).gates[j]? = some g) (hop : g.op = GateOp.and) :
    j = 1 ∨ j = 3 := by
  have hjlt : j < 5 := by
    have h := (List.getElem?_eq_some_iff.mp hj).choose
    simpa [newBlock] using h
  interval_cases j <;> simp [newBlock] at hj <;> subst g <;> simp_all

lemma newBlock_all_ands_safe {m : ℕ} (a b c d e ae eb ad : Fin m) (x : Fin m → Bool)
    (hae : x ae = (x a || x e)) (heb : x eb = (x e || x b))
    (had : x ad = (x a || x d)) (P : Prop)
    (hsafe : (oldBlock b c d ae eb ad).eval (List.ofFn x) = true → P) :
    ∀ j g, (newBlock a b c d e).gates[j]? = some g → g.op = GateOp.and →
      ((newBlock a b c d e).wires (List.ofFn x)).getD (m + j) false = true → P := by
  intro j g hj hop
  rcases newBlock_and_indices a b c d e j g hj hop with rfl | rfl
  · exact (newBlock_and_safety a b c d e ae eb ad x hae heb had P hsafe).1
  · exact (newBlock_and_safety a b c d e ae eb ad x hae heb had P hsafe).2

end PathRepair



namespace OverlapAndCover

/-- Oppositely ignored vertices cannot both have two distinct neighbors. -/
lemma ignored_vertices_one_neighborhood_small {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (L R : (V → Bool) → Bool) (a b : V)
    (correct : ∀ x, (L x && R x) = true ↔
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
    (ignoresLeft : ∀ x, L (Function.update x b true) = L x)
    (ignoresRight : ∀ x, R (Function.update x a true) = R x)
    (noSquare : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) :
    (∀ c d, G.Adj a c → G.Adj a d → c = d) ∨
      (∀ c d, G.Adj b c → G.Adj b d → c = d) := by
  classical
  by_cases small : ∀ c d, G.Adj a c → G.Adj a d → c = d
  · exact Or.inl small
  · push Not at small
    obtain ⟨c,d,hac,had,hcd⟩ := small
    refine Or.inr ?_
    intro u v hbu hbv
    have rectangle {c d : V} (hac : G.Adj a c) (hbd : G.Adj b d) : G.Adj c d :=
      ignored_vertices_neighborhood_rectangle G L R a b
        correct ignoresLeft ignoresRight hac hbd
    rcases noSquare c u d v (rectangle hac hbu) (rectangle had hbu).symm
      (rectangle had hbv) (rectangle hac hbv).symm with same | same
    · exact False.elim (hcd same)
    · exact same

lemma ignored_vertices_one_isolated_of_no_leaves {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (L R : (V → Bool) → Bool) (a b : V)
    (correct : ∀ x, (L x && R x) = true ↔
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
    (ignoresLeft : ∀ x, L (Function.update x b true) = L x)
    (ignoresRight : ∀ x, R (Function.update x a true) = R x)
    (noSquare : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d)
    (noLeaves : ∀ a b, G.Adj a b → ∃ c, G.Adj a c ∧ c ≠ b) :
    (∀ c, ¬G.Adj a c) ∨ (∀ d, ¬G.Adj b d) := by
  rcases ignored_vertices_one_neighborhood_small G L R a b correct
    ignoresLeft ignoresRight noSquare with small | small
  · refine Or.inl ?_
    intro c hac
    obtain ⟨d,had,hdc⟩ := noLeaves _ _ hac
    exact hdc (small d c had hac)
  · refine Or.inr ?_
    intro c hbc
    obtain ⟨d,hbd,hdc⟩ := noLeaves _ _ hbc
    exact hdc (small d c hbd hbc)


/-- For two families ignored by opposite factors, one entire family has
    at most one neighbor in total. -/
lemma ignored_families_one_neighborhood_small {V A B : Type*} [DecidableEq V]
    (G : SimpleGraph V) (L R : (V → Bool) → Bool) (a : A → V) (b : B → V)
    (correct : ∀ x, (L x && R x) = true ↔
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
    (ignoresLeft : ∀ j x, L (Function.update x (b j) true) = L x)
    (ignoresRight : ∀ i x, R (Function.update x (a i) true) = R x)
    (noSquare : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) :
    (∀ i j c d, G.Adj (a i) c → G.Adj (a j) d → c = d) ∨
      (∀ i j c d, G.Adj (b i) c → G.Adj (b j) d → c = d) := by
  classical
  by_cases small : ∀ i j c d, G.Adj (a i) c → G.Adj (a j) d → c = d
  · exact Or.inl small
  · push Not at small
    obtain ⟨i,j,c,d,hic,hjd,hcd⟩ := small
    refine Or.inr ?_
    intro k l u v hku hlv
    have rectangle (i : A) (j : B) {c d : V}
        (hic : G.Adj (a i) c) (hjd : G.Adj (b j) d) : G.Adj c d :=
      ignored_vertices_neighborhood_rectangle G L R (a i) (b j)
        correct (ignoresLeft j) (ignoresRight i) hic hjd
    rcases noSquare c u d v (rectangle i k hic hku) (rectangle j k hjd hku).symm
      (rectangle j l hjd hlv) (rectangle i l hic hlv).symm with same | same
    · exact False.elim (hcd same)
    · exact same

lemma ignored_families_one_isolated_of_no_leaves {V A B : Type*} [DecidableEq V]
    (G : SimpleGraph V) (L R : (V → Bool) → Bool) (a : A → V) (b : B → V)
    (correct : ∀ x, (L x && R x) = true ↔
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
    (ignoresLeft : ∀ j x, L (Function.update x (b j) true) = L x)
    (ignoresRight : ∀ i x, R (Function.update x (a i) true) = R x)
    (noSquare : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d)
    (noLeaves : ∀ a b, G.Adj a b → ∃ c, G.Adj a c ∧ c ≠ b) :
    (∀ i c, ¬G.Adj (a i) c) ∨ (∀ j d, ¬G.Adj (b j) d) := by
  rcases ignored_families_one_neighborhood_small G L R a b correct
    ignoresLeft ignoresRight noSquare with small | small
  · refine Or.inl ?_
    intro i c hic
    obtain ⟨d,hid,hdc⟩ := noLeaves _ _ hic
    exact hdc (small i i d c hid hic)
  · refine Or.inr ?_
    intro i c hic
    obtain ⟨d,hid,hdc⟩ := noLeaves _ _ hic
    exact hdc (small i i d c hid hic)

lemma private_neighborhoods_one_small {I X Y : Type*}
    (G : SimpleGraph (I ⊕ (X ⊕ Y)))
    (L : (I → Bool) → (X → Bool) → Bool)
    (R : (I → Bool) → (Y → Bool) → Bool)
    (correct : ∀ x : I ⊕ (X ⊕ Y) → Bool,
      (L (fun i => x (Sum.inl i)) (fun a => x (Sum.inr (Sum.inl a))) &&
        R (fun i => x (Sum.inl i)) (fun b => x (Sum.inr (Sum.inr b)))) = true ↔
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
    (noSquare : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) :
    (∀ a b : X, ∀ c d, G.Adj (Sum.inr (Sum.inl a)) c →
      G.Adj (Sum.inr (Sum.inl b)) d → c = d) ∨
    (∀ a b : Y, ∀ c d, G.Adj (Sum.inr (Sum.inr a)) c →
      G.Adj (Sum.inr (Sum.inr b)) d → c = d) := by
  classical
  apply ignored_families_one_neighborhood_small G
    (fun x => L (fun i => x (Sum.inl i)) (fun a => x (Sum.inr (Sum.inl a))))
    (fun x => R (fun i => x (Sum.inl i)) (fun b => x (Sum.inr (Sum.inr b))))
    (fun a => Sum.inr (Sum.inl a)) (fun b => Sum.inr (Sum.inr b)) correct ?_ ?_ noSquare
  · intro j x
    simp [Function.update]
  · intro i x
    simp [Function.update]

lemma private_side_isolated_of_no_leaves {I X Y : Type*}
    (G : SimpleGraph (I ⊕ (X ⊕ Y)))
    (L : (I → Bool) → (X → Bool) → Bool)
    (R : (I → Bool) → (Y → Bool) → Bool)
    (correct : ∀ x : I ⊕ (X ⊕ Y) → Bool,
      (L (fun i => x (Sum.inl i)) (fun a => x (Sum.inr (Sum.inl a))) &&
        R (fun i => x (Sum.inl i)) (fun b => x (Sum.inr (Sum.inr b)))) = true ↔
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
    (noSquare : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d)
    (noLeaves : ∀ a b, G.Adj a b → ∃ c, G.Adj a c ∧ c ≠ b) :
    (∀ a : X, ∀ c, ¬G.Adj (Sum.inr (Sum.inl a)) c) ∨
      (∀ b : Y, ∀ d, ¬G.Adj (Sum.inr (Sum.inr b)) d) := by
  rcases private_neighborhoods_one_small G L R correct noSquare with small | small
  · refine Or.inl ?_
    intro a c hac
    obtain ⟨d,had,hdc⟩ := noLeaves _ _ hac
    exact hdc (small a a d c had hac)
  · refine Or.inr ?_
    intro b c hbc
    obtain ⟨d,hbd,hdc⟩ := noLeaves _ _ hbc
    exact hdc (small b b d c hbd hbc)

end OverlapAndCover

namespace OverlapAndCover

/-- In a C4-free graph without leaves, one AND factor genuinely depends on
    every nonisolated vertex. Dependence is witnessed by a change on insertion. -/
lemma and_factor_one_depends_on_all_nonisolated {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (L R : (V → Bool) → Bool)
    (correct : ∀ x, (L x && R x) = true ↔
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
    (noSquare : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d)
    (noLeaves : ∀ a b, G.Adj a b → ∃ c, G.Adj a c ∧ c ≠ b) :
    (∀ v, (∃ u, G.Adj v u) → ∃ x, L (Function.update x v true) ≠ L x) ∨
      (∀ v, (∃ u, G.Adj v u) → ∃ x, R (Function.update x v true) ≠ R x) := by
  classical
  by_cases allLeft : ∀ v, (∃ u, G.Adj v u) → ∃ x, L (Function.update x v true) ≠ L x
  · exact Or.inl allLeft
  · push Not at allLeft
    obtain ⟨b,activeB,ignoresLeft⟩ := allLeft
    refine Or.inr ?_
    intro a activeA
    by_contra noDependence
    push Not at noDependence
    rcases ignored_vertices_one_isolated_of_no_leaves G L R a b correct
      ignoresLeft noDependence noSquare noLeaves with isolatedA | isolatedB
    · obtain ⟨c,hac⟩ := activeA
      exact isolatedA c hac
    · obtain ⟨d,hbd⟩ := activeB
      exact isolatedB d hbd

end OverlapAndCover

namespace BlockSubstitution

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def AgreeOutside (B : Finset ℕ) (v w : List Bool) : Prop :=
  ∀ i, i ∉ B → v.getD i false = w.getD i false

lemma append_agree_outside (B : Finset ℕ) (v w : List Bool) (a b : Bool)
    (hlen : v.length = w.length) (hab : a = b) (h : AgreeOutside B v w) :
    AgreeOutside B (v ++ [a]) (w ++ [b]) := by
  intro i hi
  by_cases hil : i < v.length
  · rw [List.getD_append _ _ _ _ hil, List.getD_append _ _ _ _ (by omega)]
    exact h i hi
  · by_cases hie : i = v.length
    · have hiew : i = w.length := hie.trans hlen
      rw [hie, List.getD_append_right _ _ _ _ (by omega), Nat.sub_self]
      rw [← hie, hiew, List.getD_append_right _ _ _ _ (by omega), Nat.sub_self]
      simpa using hab
    · rw [List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by simp; omega)]

lemma run_agree_outside (B : Finset ℕ) (gs : List Gate)
    (v w : List Bool) (hlen : v.length = w.length)
    (havoid : ∀ g ∈ gs, ∀ i ∈ g.inputs, i ∉ B)
    (h : AgreeOutside B v w) : AgreeOutside B (run gs v) (run gs w) := by
  induction gs generalizing v w with
  | nil => exact h
  | cons g gs ih =>
    have hmap : g.inputs.map (fun i => v.getD i false) =
        g.inputs.map (fun i => w.getD i false) := by
      apply List.map_congr_left
      intro i hi
      exact h i (havoid g List.mem_cons_self i hi)
    have hstep : AgreeOutside B (step v g) (step w g) := by
      apply append_agree_outside B v w _ _ hlen (congrArg g.op.eval hmap) h
    exact ih (step v g) (step w g) (by simp [step, hlen])
      (fun q hq => havoid q (List.mem_cons_of_mem _ hq)) hstep

def internalWires (m : ℕ) : Finset ℕ := {m, m + 1, m + 2, m + 3}

lemma five_block_agree_outside (m : ℕ) (C D : Circuit)
    (hC : C.size = 5) (hD : D.size = 5)
    (x : List Bool) (hx : x.length = m)
    (hlast : (C.wires x).getD (m + 4) false = (D.wires x).getD (m + 4) false) :
    AgreeOutside (internalWires m) (C.wires x) (D.wires x) := by
  have hclen : (C.wires x).length = m + 5 := by
    change (run C.gates x).length = _
    rw [run_length, hx]
    exact congrArg (m + ·) hC
  have hdlen : (D.wires x).length = m + 5 := by
    change (run D.gates x).length = _
    rw [run_length, hx]
    exact congrArg (m + ·) hD
  intro i hi
  by_cases him : i < m
  · change (run C.gates x).getD i false = (run D.gates x).getD i false
    rw [run_old_read _ _ _ (by omega), run_old_read _ _ _ (by omega)]
  · by_cases hiend : i < m + 5
    · have hnot : i ≠ m ∧ i ≠ m + 1 ∧ i ≠ m + 2 ∧ i ≠ m + 3 := by
        simpa [internalWires] using hi
      have hieq : i = m + 4 := by omega
      simpa only [hieq] using hlast
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]

lemma append_suffix_eval_eq (B : Finset ℕ) (C D : Circuit)
    (post : List Gate) (out : ℕ) (x : List Bool)
    (hlen : (C.wires x).length = (D.wires x).length)
    (hagree : AgreeOutside B (C.wires x) (D.wires x))
    (hpost : ∀ g ∈ post, ∀ i ∈ g.inputs, i ∉ B)
    (hout : out ∉ B) :
    (⟨C.gates ++ post, out⟩ : Circuit).eval x =
      (⟨D.gates ++ post, out⟩ : Circuit).eval x := by
  have h := run_agree_outside B post (C.wires x) (D.wires x) hlen hpost hagree out hout
  change (run (C.gates ++ post) x).getD out false =
    (run (D.gates ++ post) x).getD out false
  change (run post (run C.gates x)).getD out false =
    (run post (run D.gates x)).getD out false at h
  simpa only [run, List.foldl_append] using h

lemma path_blocks_suffix_eq {m : ℕ} (a b c d e ae eb ad : Fin m) (x : Fin m → Bool)
    (hae : x ae = (x a || x e)) (heb : x eb = (x e || x b))
    (had : x ad = (x a || x d)) (post : List Gate) (out : ℕ)
    (hpost : ∀ g ∈ post, ∀ i ∈ g.inputs, i ∉ internalWires m)
    (hout : out ∉ internalWires m) :
    (⟨(PathRepair.oldBlock b c d ae eb ad).gates ++ post, out⟩ : Circuit).eval
        (List.ofFn x) =
      (⟨(PathRepair.newBlock a b c d e).gates ++ post, out⟩ : Circuit).eval
        (List.ofFn x) := by
  have hlast : ((PathRepair.oldBlock b c d ae eb ad).wires (List.ofFn x)).getD (m + 4) false =
      ((PathRepair.newBlock a b c d e).wires (List.ofFn x)).getD (m + 4) false :=
    PathRepair.blocks_agree a b c d e ae eb ad x hae heb had
  apply append_suffix_eval_eq (internalWires m)
    (PathRepair.oldBlock b c d ae eb ad) (PathRepair.newBlock a b c d e) post out
    (List.ofFn x) _ _ hpost hout
  · change (run _ _).length = (run _ _).length
    simp [run_length, PathRepair.oldBlock, PathRepair.newBlock]
  · exact five_block_agree_outside m _ _ (PathRepair.oldBlock_size ..)
      (PathRepair.newBlock_size ..) _ List.length_ofFn hlast

end BlockSubstitution



namespace SeparateAndBound

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity OverlapAndCover

lemma support_is_cover {n : ℕ} (G : SimpleGraph (Fin n))
    (f : (Fin n → Bool) → Bool) (S : Finset (Fin n))
    (zero : f (fun _ => false) = false)
    (edges : ∀ u v, G.Adj u v → f (pairInput u v) = true)
    (support : ∀ x y, (∀ i ∈ S, x i = y i) → f x = f y) :
    G.IsVertexCover (S : Set (Fin n)) := by
  intro u v huv
  change u ∈ S ∨ v ∈ S
  by_contra hn
  push Not at hn
  have hz := support (pairInput u v) (fun _ => false) (by
    intro i hi
    have hiu : i ≠ u := fun h => hn.1 (h ▸ hi)
    have hiv : i ≠ v := fun h => hn.2 (h ▸ hi)
    simp [pairInput, hiu, hiv])
  rw [edges u v huv, zero] at hz
  contradiction

lemma support_card_of_depends {n : ℕ} (f : (Fin n → Bool) → Bool)
    (S : Finset (Fin n))
    (support : ∀ x y, (∀ i ∈ S, x i = y i) → f x = f y)
    (depends : ∀ v, ∃ x, f (Function.update x v true) ≠ f x) : n ≤ S.card := by
  have all : ∀ v, v ∈ S := by
    intro v
    by_contra hv
    obtain ⟨x, hx⟩ := depends v
    apply hx (support _ _ ?_)
    intro i hi
    have hiv : i ≠ v := fun e => hv (e ▸ hi)
    simp [Function.update, hiv]
  have heq : S = Finset.univ := Finset.eq_univ_of_forall all
  simp [heq]

/-- The costs are those of two separately given circuits; shared gates are counted
    in each branch in which they occur. No monotonicity assumption is needed. -/
lemma separate_and_lower_bound {n : ℕ} (G : SimpleGraph (Fin n))
    (C₁ C₂ : Circuit)
    (fan₁ : ∀ g ∈ C₁.gates, g.inputs.length ≤ 2)
    (fan₂ : ∀ g ∈ C₂.gates, g.inputs.length ≤ 2)
    (zero₁ : C₁.eval (List.ofFn (fun _ : Fin n => false)) = false)
    (zero₂ : C₂.eval (List.ofFn (fun _ : Fin n => false)) = false)
    (correct : ∀ x : Fin n → Bool,
      (C₁.eval (List.ofFn x) && C₂.eval (List.ofFn x)) = true ↔
        ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
    (noSquare : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d →
      G.Adj d a → a = c ∨ b = d)
    (noLeaves : ∀ a b, G.Adj a b → ∃ c, G.Adj a c ∧ c ≠ b)
    (noIsolated : ∀ v, ∃ u, G.Adj v u) :
    ∃ T : Finset (Fin n), G.IsVertexCover (T : Set (Fin n)) ∧
      n + T.card ≤ C₁.size + C₂.size + 2 := by
  obtain ⟨S₁, bound₁, support₁, _⟩ := HelperSupport.output_support n C₁ fan₁
  obtain ⟨S₂, bound₂, support₂, _⟩ := HelperSupport.output_support n C₂ fan₂
  have edges : ∀ u v, G.Adj u v →
      C₁.eval (List.ofFn (pairInput u v)) = true ∧
        C₂.eval (List.ofFn (pairInput u v)) = true := by
    intro u v huv
    exact Bool.and_eq_true_iff.mp ((correct _).mpr ((pair_edge_iff G u v).mpr huv))
  rcases and_factor_one_depends_on_all_nonisolated G
    (fun x => C₁.eval (List.ofFn x)) (fun x => C₂.eval (List.ofFn x))
    correct noSquare noLeaves with left | right
  · have hn := support_card_of_depends _ S₁ support₁ (fun v => left v (noIsolated v))
    refine ⟨S₂, support_is_cover G _ S₂ zero₂ (fun u v h => (edges u v h).2) support₂, ?_⟩
    omega
  · have hn := support_card_of_depends _ S₂ support₂ (fun v => right v (noIsolated v))
    refine ⟨S₁, support_is_cover G _ S₁ zero₁ (fun u v h => (edges u v h).1) support₁, ?_⟩
    omega

end SeparateAndBound

namespace TaggedBoundary

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity HelperSupport

variable {n : ℕ}

/-- Adding a boundary wire costs no selected gate. Label freshness is unnecessary. -/
lemma cnt_boundary (t : ℕ) (L : List (Finset (Fin n))) (b : Fin n)
    (h : Cnt t L) : Cnt t (L ++ [{b}]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [{b}]).getD j ∅) ⊆
        (W.erase L.length).biUnion (fun j => L.getD j ∅) ∪ {b} := by
      intro i hi
      obtain ⟨j, hj, hij⟩ := Finset.mem_biUnion.mp hi
      by_cases heq : j = L.length
      · subst j
        exact Finset.mem_union_right _ (by simpa only [getD_snoc_eq] using hij)
      · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
          ⟨j, Finset.mem_erase.mpr ⟨heq, hj⟩, by
            simpa only [getD_snoc_ne _ _ _ _ heq] using hij⟩)
    have hcard := Finset.card_le_card hsub
    have hunion := Finset.card_union_le
      ((W.erase L.length).biUnion fun j => L.getD j ∅) {b}
    have hold := h (W.erase L.length)
    have herase := Finset.card_erase_of_mem hW
    have hpos : 0 < W.card := Finset.card_pos.mpr ⟨_, hW⟩
    simp only [Finset.card_singleton] at hunion
    omega
  · have heq : (W.biUnion fun j => (L ++ [{b}]).getD j ∅) =
        W.biUnion (fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    exact h W

lemma cnt_singletons (labels : List (Fin n)) :
    Cnt 0 (labels.map fun b => ({b} : Finset (Fin n))) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases labels[j]? <;> simp

/-- Selected gates expand their input frontiers; other gates stop at their label.
    Missing and forward wire reads have empty frontier, matching circuit defaults. -/
def boundaryFrom (gs : List (Bool × Gate × Fin n)) (L : List (Finset (Fin n))) :
    List (Finset (Fin n)) :=
  gs.foldl (fun L q => L ++ [if q.1 then gateSupp L q.2.1 else {q.2.2}]) L

def selectedCount (gs : List (Bool × Gate × Fin n)) : ℕ :=
  (gs.filter fun q => q.1).length

lemma cnt_boundaryFrom (gs : List (Bool × Gate × Fin n)) :
    ∀ (t : ℕ) (L : List (Finset (Fin n))),
      (∀ q ∈ gs, q.1 = true → q.2.1.inputs.length ≤ 2) → Cnt t L →
      Cnt (t + selectedCount gs) (boundaryFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; simpa [selectedCount, boundaryFrom] using h
  | cons q qs ih =>
    intro t L hfan h
    have htail : ∀ r ∈ qs, r.1 = true → r.2.1.inputs.length ≤ 2 :=
      fun r hr => hfan r (List.mem_cons_of_mem _ hr)
    cases hq : q.1 with
    | false =>
      have hi := ih t (L ++ [{q.2.2}]) htail (cnt_boundary t L q.2.2 h)
      simpa [selectedCount, boundaryFrom, hq, List.foldl_cons] using hi
    | true =>
      have hi := ih (t + 1) (L ++ [gateSupp L q.2.1]) htail
        (cnt_step t L q.2.1 (hfan q List.mem_cons_self hq) h)
      simpa [selectedCount, boundaryFrom, hq, List.foldl_cons,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hi

/-- The exact recursively computed boundary of one output has at most one more
    distinct label than there are selected gates in the traversed list. -/
lemma output_boundary_card (labels : List (Fin n))
    (gs : List (Bool × Gate × Fin n)) (out : ℕ)
    (hfan : ∀ q ∈ gs, q.1 = true → q.2.1.inputs.length ≤ 2) :
    ((boundaryFrom gs (labels.map fun b => ({b} : Finset (Fin n)))).getD out ∅).card ≤
      selectedCount gs + 1 := by
  have h := cnt_boundaryFrom gs 0 _ hfan (cnt_singletons labels) {out}
  simpa only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] using h

end TaggedBoundary



namespace SelectedExtraction

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

lemma wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

lemma getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp


abbrev Acc := List ℕ × List Gate

def remapGate (F : ℕ) (ρ : List ℕ) (g : Gate) : Gate :=
  ⟨g.op,g.inputs.map fun i => ρ.getD i F⟩

def extractStep (B F : ℕ) (keep : ℕ → Bool) (acc : Acc) (g : Gate) : Acc :=
  if keep acc.1.length then
    (acc.1 ++ [B + acc.2.length],acc.2 ++ [remapGate F acc.1 g])
  else (acc.1 ++ [acc.1.length],acc.2)

def extract (B F : ℕ) (keep : ℕ → Bool) (gs : List Gate) (acc : Acc) : Acc :=
  gs.foldl (extractStep B F keep) acc

def Inv (B F : ℕ) (y w : List Bool) (acc : Acc) : Prop :=
  acc.1.length = w.length ∧
    (∀ i < acc.1.length, acc.1.getD i F < B + acc.2.length) ∧
    ∀ i, (wiresFrom acc.2 y).getD (acc.1.getD i F) false = w.getD i false

lemma inv_extend (B F : ℕ) (y w : List Bool) (ρ : List ℕ) (gs : List Gate)
    (r : ℕ) (v : Bool) (hlen : ρ.length = w.length) (hy : y.length = B)
    (hvalid : ∀ i < ρ.length, ρ.getD i F < B + gs.length)
    (hread : ∀ i < ρ.length, (wiresFrom gs y).getD (ρ.getD i F) false = w.getD i false)
    (hr : r < B + gs.length)
    (hv : (wiresFrom gs y).getD r false = v)
    (hF : B + gs.length ≤ F) : Inv B F y (w ++ [v]) (ρ ++ [r],gs) := by
  refine ⟨by simp [hlen],?_,?_⟩
  · intro i hi
    by_cases h : i < ρ.length
    · rw [List.getD_append _ _ _ _ h]
      exact hvalid i h
    · have e : i = ρ.length := by simp only [List.length_append,List.length_singleton] at hi; omega
      subst i
      simpa using hr
  · intro i
    change (wiresFrom gs y).getD ((ρ ++ [r]).getD i F) false = (w ++ [v]).getD i false
    by_cases h : i < ρ.length
    · rw [List.getD_append _ _ _ _ h,List.getD_append _ _ _ _ (by omega)]
      exact hread i h
    · by_cases e : i = ρ.length
      · subst i
        rw [getD_snoc_eq,hlen,getD_snoc_eq]
        exact hv
      · have hm : (ρ ++ [r]).getD i F = F := List.getD_eq_default _ _ (by simp;omega)
        rw [hm]
        have hn : (wiresFrom gs y).getD F false = false :=
          List.getD_eq_default _ _ (by rw [length_wiresFrom,hy];exact hF)
        rw [hn,List.getD_eq_default _ _ (by simp;omega)]

lemma step_sound (B F : ℕ) (keep : ℕ → Bool) (y w : List Bool) (acc : Acc) (g : Gate)
    (hy : y.length = B) (hwidth : w.length < B)
    (hcap : B + acc.2.length + 1 ≤ F) (h : Inv B F y w acc)
    (boundary : keep w.length = false →
      y.getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false)) :
    Inv B F y (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (extractStep B F keep acc g) := by
  obtain ⟨hlen,hvalid,hread⟩ := h
  have heval : (remapGate F acc.1 g).op.eval
      ((remapGate F acc.1 g).inputs.map fun i => (wiresFrom acc.2 y).getD i false) =
      g.op.eval (g.inputs.map fun i => w.getD i false) := by
    simp only [remapGate,List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    exact hread i
  cases hk : keep acc.1.length with
  | false =>
    simp only [extractStep,hk,Bool.false_eq_true,↓reduceIte]
    apply inv_extend B F y w acc.1 acc.2 acc.1.length _ hlen hy hvalid
      (fun i _ => hread i) (by omega) ?_ (by omega)
    rw [getD_wiresFrom _ _ _ (by omega),hlen]
    exact boundary (by simpa [hlen] using hk)
  | true =>
    simp only [extractStep,hk,↓reduceIte]
    have hnew : wiresFrom (acc.2 ++ [remapGate F acc.1 g]) y =
        wiresFrom acc.2 y ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] := by
      rw [wiresFrom_append]
      change wiresFrom acc.2 y ++ [_] = _
      rw [heval]
    apply inv_extend B F y w acc.1 (acc.2 ++ [remapGate F acc.1 g])
      (B + acc.2.length) _ hlen hy ?_ ?_ (by simp) ?_ (by simp;omega)
    · intro i hi
      have := hvalid i hi
      simp only [List.length_append,List.length_singleton]
      omega
    · intro i hi
      rw [hnew,List.getD_append _ _ _ _ (by rw [length_wiresFrom,hy];exact hvalid i hi)]
      exact hread i
    · rw [hnew,←show (wiresFrom acc.2 y).length = B + acc.2.length by rw [length_wiresFrom,hy]]
      exact getD_snoc_eq _ _ _


lemma extract_sound (B F : ℕ) (keep : ℕ → Bool) (y : List Bool) (hy : y.length = B)
    (gs : List Gate) : ∀ (w : List Bool) (acc : Acc),
    w.length + gs.length ≤ B → B + acc.2.length + gs.length ≤ F →
    (∀ i < (wiresFrom gs w).length, keep i = false →
      y.getD i false = (wiresFrom gs w).getD i false) →
    Inv B F y w acc → Inv B F y (wiresFrom gs w) (extract B F keep gs acc) := by
  induction gs with
  | nil => intro w acc _ _ _ h; exact h
  | cons g gs ih =>
    intro w acc hwidth hcap boundary h
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    have hnew : Inv B F y (w ++ [v]) (extractStep B F keep acc g) := by
      apply step_sound B F keep y w acc g hy (by simp at hwidth;omega) (by simp at hcap;omega) h
      intro hk
      have hb := boundary w.length (by rw [length_wiresFrom];simp) hk
      change y.getD w.length false = v
      change y.getD w.length false = (wiresFrom gs (w ++ [v])).getD w.length false at hb
      rw [getD_wiresFrom _ _ _ (by simp),getD_snoc_eq] at hb
      exact hb
    apply ih (w ++ [v]) (extractStep B F keep acc g) (by simp at hwidth ⊢;omega) ?_ boundary hnew
    simp only [extractStep]
    split <;> simp at hcap ⊢ <;> omega

/-- Extracted paid gates and remapping of every original wire. -/
def compiled (n : ℕ) (C : Circuit) (keep : ℕ → Bool) : Acc :=
  extract (n + C.size) (n + C.size + C.size) keep C.gates (List.range n,[])

def extracted (n : ℕ) (C : Circuit) (keep : ℕ → Bool) : Circuit :=
  ⟨(compiled n C keep).2,(compiled n C keep).1.getD C.output (n + C.size + C.size)⟩

lemma initial_inv (n B F : ℕ) (C : Circuit) (x y : List Bool)
    (hx : x.length = n) (hy : y.length = B) (hn : n ≤ B) (hF : B ≤ F)
    (boundary : ∀ i < n, y.getD i false = (C.wires x).getD i false) :
    Inv B F y x (List.range n,[]) := by
  refine ⟨by simpa using hx.symm,?_,?_⟩
  · intro i hi
    have hi' : i < n := by simpa using hi
    simpa [List.getD_eq_getElem?_getD,hi'] using (show i < B from lt_of_lt_of_le hi' hn)
  · intro i
    change y.getD ((List.range n).getD i F) false = x.getD i false
    by_cases hi : i < n
    · have hm : (List.range n).getD i F = i := by simp [List.getD_eq_getElem?_getD,hi]
      rw [hm,boundary i hi]
      exact getD_wiresFrom C.gates x i (by omega)
    · have hm : (List.range n).getD i F = F := List.getD_eq_default _ _ (by simp;omega)
      have hyF : y.getD F false = false := List.getD_eq_default _ _ (by omega)
      have hxi : x.getD i false = false := List.getD_eq_default _ _ (by omega)
      rw [hm,hyF,hxi]

/-- Boundary slots for selected wires are unrestricted. Every primary input and
    every unselected gate output is supplied with its original value. -/
lemma extracted_correct (n : ℕ) (C : Circuit) (keep : ℕ → Bool) (x y : List Bool)
    (hx : x.length = n) (hy : y.length = n + C.size)
    (boundary : ∀ i < n + C.size, i < n ∨ keep i = false →
      y.getD i false = (C.wires x).getD i false) :
    (extracted n C keep).eval y = C.eval x := by
  have hinit := initial_inv n (n + C.size) (n + C.size + C.size) C x y hx hy
    (by omega) (by omega) (fun i hi => boundary i (by omega) (Or.inl hi))
  have h := extract_sound (n + C.size) (n + C.size + C.size) keep y hy C.gates
    x (List.range n,[]) (by simp [hx,Circuit.size]) (by simp [Circuit.size])
    (by intro i hi hk;exact boundary i (by simpa [length_wiresFrom,hx,Circuit.size] using hi) (Or.inr hk)) hinit
  exact h.2.2 C.output

end SelectedExtraction
namespace SelectedExtraction

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma extractStep_map_length (B F : ℕ) (keep : ℕ → Bool) (acc : Acc) (g : Gate) :
    (extractStep B F keep acc g).1.length = acc.1.length + 1 := by
  simp only [extractStep]
  split <;> simp

lemma extract_map_length (B F : ℕ) (keep : ℕ → Bool) (gs : List Gate) :
    ∀ acc : Acc, (extract B F keep gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; rfl
  | cons g gs ih =>
    intro acc
    change (extract B F keep gs (extractStep B F keep acc g)).1.length = _
    rw [ih,extractStep_map_length]
    simp only [List.length_cons]
    omega

lemma extract_paid_length (B F : ℕ) (keep : ℕ → Bool) (gs : List Gate) :
    ∀ acc : Acc, (extract B F keep gs acc).2.length = acc.2.length +
      ((List.range' acc.1.length gs.length).filter keep).length := by
  induction gs with
  | nil => intro acc; simp [extract]
  | cons g gs ih =>
    intro acc
    change (extract B F keep gs (extractStep B F keep acc g)).2.length = _
    rw [ih,extractStep_map_length]
    simp only [List.length_cons,List.range'_succ,List.filter_cons]
    cases hk : keep acc.1.length <;> simp [extractStep,hk,Nat.add_assoc,Nat.add_comm]

lemma extract_paid_le (B F : ℕ) (keep : ℕ → Bool) (gs : List Gate) (acc : Acc) :
    (extract B F keep gs acc).2.length ≤ acc.2.length + gs.length := by
  rw [extract_paid_length]
  have h := List.length_filter_le keep (List.range' acc.1.length gs.length)
  simpa using Nat.add_le_add_left h acc.2.length

lemma extract_mono (B F : ℕ) (keep : ℕ → Bool) (gs : List Gate) :
    ∀ acc : Acc,
    (∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    (∀ g ∈ acc.2, g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    ∀ g ∈ (extract B F keep gs acc).2,
      g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction gs with
  | nil => intro acc _ ha; exact ha
  | cons g gs ih =>
    intro acc hg ha
    apply ih (extractStep B F keep acc g) (fun h hh => hg h (List.mem_cons_of_mem g hh))
    intro h hh
    cases hk : keep acc.1.length with
    | false =>
      simp only [extractStep,hk,Bool.false_eq_true,↓reduceIte] at hh
      exact ha h hh
    | true =>
      simp only [extractStep,hk,↓reduceIte,List.mem_append,List.mem_singleton] at hh
      rcases hh with hh | hh
      · exact ha h hh
      · subst h
        simpa only [remapGate,List.length_map] using hg g (List.mem_cons_self)

lemma extracted_monotone2 (n : ℕ) (C : Circuit) (keep : ℕ → Bool) (hC : Monotone2 C) :
    Monotone2 (extracted n C keep) := by
  exact extract_mono (n + C.size) (n + C.size + C.size) keep C.gates
    (List.range n,[]) hC (by simp)

lemma extracted_size (n : ℕ) (C : Circuit) (keep : ℕ → Bool) :
    (extracted n C keep).size = ((List.range' n C.size).filter keep).length := by
  unfold Circuit.size extracted compiled
  rw [extract_paid_length]
  simp only [List.length_nil,List.length_range,Nat.zero_add]

lemma extracted_size_le (n : ℕ) (C : Circuit) (keep : ℕ → Bool) :
    (extracted n C keep).size ≤ C.size := by
  rw [extracted_size]
  have h := List.length_filter_le keep (List.range' n C.size)
  simpa using h

lemma selected_range_length (n s : ℕ) (M : Finset ℕ) (hM : ∀ j ∈ M, j < s) :
    ((List.range' n s).filter fun i => decide (n ≤ i ∧ i - n ∈ M)).length = M.card := by
  have hfilter : (List.range' n s).filter (fun i => decide (n ≤ i ∧ i - n ∈ M)) =
      ((List.range s).filter fun j => decide (j ∈ M)).map (fun j => n + j) := by
    rw [List.range'_eq_map_range,List.filter_map]
    congr 1
    apply List.filter_congr
    intro j _
    simp
  rw [hfilter,List.length_map]
  rw [←List.toFinset_card_of_nodup ((List.nodup_range).filter _)]
  congr 1
  ext j
  simp only [List.mem_toFinset,List.mem_filter,List.mem_range,decide_eq_true_eq]
  exact ⟨fun h => h.2,fun h => ⟨hM j h,h⟩⟩

lemma extracted_size_of_subset (n : ℕ) (C : Circuit) (M : Finset ℕ)
    (hM : ∀ j ∈ M, j < C.size) :
    (extracted n C (fun i => decide (n ≤ i ∧ i - n ∈ M))).size = M.card := by
  rw [extracted_size]
  exact selected_range_length n C.size M hM

end SelectedExtraction

namespace SelectedExtraction

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def ReadsNeeded (keep : ℕ → Bool) (P : ℕ → Prop) : ℕ → List Gate → Prop
  | _,[] => True
  | j,g :: gs => (keep j = true → ∀ i ∈ g.inputs, i < j → P i) ∧ ReadsNeeded keep P (j + 1) gs

def InvOn (P : ℕ → Prop) (B F : ℕ) (y w : List Bool) (acc : Acc) : Prop :=
  acc.1.length = w.length ∧
    (∀ i < acc.1.length, acc.1.getD i F < B + acc.2.length) ∧
    ∀ i, P i → (wiresFrom acc.2 y).getD (acc.1.getD i F) false = w.getD i false

lemma inv_extend_on (P : ℕ → Prop) (B F : ℕ) (y w : List Bool) (ρ : List ℕ) (gs : List Gate)
    (r : ℕ) (v : Bool) (hlen : ρ.length = w.length) (hy : y.length = B)
    (hvalid : ∀ i < ρ.length, ρ.getD i F < B + gs.length)
    (hread : ∀ i < ρ.length, P i → (wiresFrom gs y).getD (ρ.getD i F) false = w.getD i false)
    (hr : r < B + gs.length)
    (hv : P ρ.length → (wiresFrom gs y).getD r false = v)
    (hF : B + gs.length ≤ F) : InvOn P B F y (w ++ [v]) (ρ ++ [r],gs) := by
  refine ⟨by simp [hlen],?_,?_⟩
  · intro i hi
    by_cases h : i < ρ.length
    · rw [List.getD_append _ _ _ _ h]
      exact hvalid i h
    · have e : i = ρ.length := by simp only [List.length_append,List.length_singleton] at hi; omega
      subst i
      simpa using hr
  · intro i hP
    change (wiresFrom gs y).getD ((ρ ++ [r]).getD i F) false = (w ++ [v]).getD i false
    by_cases h : i < ρ.length
    · rw [List.getD_append _ _ _ _ h,List.getD_append _ _ _ _ (by omega)]
      exact hread i h hP
    · by_cases e : i = ρ.length
      · subst i
        rw [getD_snoc_eq,hlen,getD_snoc_eq]
        exact hv hP
      · have hm : (ρ ++ [r]).getD i F = F := List.getD_eq_default _ _ (by simp;omega)
        have hn : (wiresFrom gs y).getD F false = false :=
          List.getD_eq_default _ _ (by rw [length_wiresFrom,hy];exact hF)
        rw [hm,hn,List.getD_eq_default _ _ (by simp;omega)]

lemma step_sound_on (P : ℕ → Prop) (B F : ℕ) (keep : ℕ → Bool) (y w : List Bool) (acc : Acc) (g : Gate)
    (hy : y.length = B) (hwidth : w.length < B)
    (hcap : B + acc.2.length + 1 ≤ F) (h : InvOn P B F y w acc)
    (reads : keep w.length = true → ∀ i ∈ g.inputs, i < w.length → P i)
    (boundary : P w.length → keep w.length = false →
      y.getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false)) :
    InvOn P B F y (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (extractStep B F keep acc g) := by
  obtain ⟨hlen,hvalid,hread⟩ := h
  cases hk : keep acc.1.length with
  | false =>
    simp only [extractStep,hk,Bool.false_eq_true,↓reduceIte]
    apply inv_extend_on P B F y w acc.1 acc.2 acc.1.length _ hlen hy hvalid
      (fun i _ => hread i) (by omega) ?_ (by omega)
    intro hP
    rw [getD_wiresFrom _ _ _ (by omega),hlen]
    exact boundary (by simpa [hlen] using hP) (by simpa [hlen] using hk)
  | true =>
    have heval : (remapGate F acc.1 g).op.eval
        ((remapGate F acc.1 g).inputs.map fun i => (wiresFrom acc.2 y).getD i false) =
        g.op.eval (g.inputs.map fun i => w.getD i false) := by
      simp only [remapGate,List.map_map]
      congr 1
      apply List.map_congr_left
      intro i hi
      change (wiresFrom acc.2 y).getD (acc.1.getD i F) false = w.getD i false
      by_cases hlt : i < w.length
      · exact hread i (reads (by simpa [hlen] using hk) i hi hlt)
      · have hm : acc.1.getD i F = F := List.getD_eq_default _ _ (by omega)
        have hn : (wiresFrom acc.2 y).getD F false = false :=
          List.getD_eq_default _ _ (by rw [length_wiresFrom,hy];omega)
        rw [hm,hn,List.getD_eq_default _ _ (by omega)]
    simp only [extractStep,hk,↓reduceIte]
    have hnew : wiresFrom (acc.2 ++ [remapGate F acc.1 g]) y =
        wiresFrom acc.2 y ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] := by
      rw [wiresFrom_append]
      change wiresFrom acc.2 y ++ [_] = _
      rw [heval]
    apply inv_extend_on P B F y w acc.1 (acc.2 ++ [remapGate F acc.1 g])
      (B + acc.2.length) _ hlen hy ?_ ?_ (by simp) ?_ (by simp;omega)
    · intro i hi
      have := hvalid i hi
      simp only [List.length_append,List.length_singleton]
      omega
    · intro i hi hP
      rw [hnew,List.getD_append _ _ _ _ (by rw [length_wiresFrom,hy];exact hvalid i hi)]
      exact hread i hP
    · intro _
      rw [hnew,←show (wiresFrom acc.2 y).length = B + acc.2.length by rw [length_wiresFrom,hy]]
      exact getD_snoc_eq _ _ _

lemma extract_sound_on (P : ℕ → Prop) (B F : ℕ) (keep : ℕ → Bool) (y : List Bool) (hy : y.length = B)
    (gs : List Gate) : ∀ (w : List Bool) (acc : Acc),
    w.length + gs.length ≤ B → B + acc.2.length + gs.length ≤ F →
    ReadsNeeded keep P w.length gs →
    (∀ i < (wiresFrom gs w).length, P i → keep i = false →
      y.getD i false = (wiresFrom gs w).getD i false) →
    InvOn P B F y w acc → InvOn P B F y (wiresFrom gs w) (extract B F keep gs acc) := by
  induction gs with
  | nil => intro w acc _ _ _ _ h; exact h
  | cons g gs ih =>
    intro w acc hwidth hcap reads boundary h
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    have hnew : InvOn P B F y (w ++ [v]) (extractStep B F keep acc g) := by
      apply step_sound_on P B F keep y w acc g hy (by simp at hwidth;omega) (by simp at hcap;omega) h reads.1
      intro hP hk
      have hb := boundary w.length (by rw [length_wiresFrom];simp) hP hk
      change y.getD w.length false = v
      change y.getD w.length false = (wiresFrom gs (w ++ [v])).getD w.length false at hb
      rw [getD_wiresFrom _ _ _ (by simp),getD_snoc_eq] at hb
      exact hb
    apply ih (w ++ [v]) (extractStep B F keep acc g) (by simp at hwidth ⊢;omega) ?_
      (by simpa using reads.2) boundary hnew
    simp only [extractStep]
    split <;> simp at hcap ⊢ <;> omega

lemma initial_inv_on (P : ℕ → Prop) (n B F : ℕ) (C : Circuit) (x y : List Bool)
    (hx : x.length = n) (hy : y.length = B) (hn : n ≤ B) (hF : B ≤ F)
    (boundary : ∀ i < n, P i → y.getD i false = (C.wires x).getD i false) :
    InvOn P B F y x (List.range n,[]) := by
  refine ⟨by simpa using hx.symm,?_,?_⟩
  · intro i hi
    have hi' : i < n := by simpa using hi
    simpa [List.getD_eq_getElem?_getD,hi'] using (show i < B from lt_of_lt_of_le hi' hn)
  · intro i hP
    change y.getD ((List.range n).getD i F) false = x.getD i false
    by_cases hi : i < n
    · have hm : (List.range n).getD i F = i := by simp [List.getD_eq_getElem?_getD,hi]
      rw [hm,boundary i hi hP]
      exact getD_wiresFrom C.gates x i (by omega)
    · have hm : (List.range n).getD i F = F := List.getD_eq_default _ _ (by simp;omega)
      have hyF : y.getD F false = false := List.getD_eq_default _ _ (by omega)
      have hxi : x.getD i false = false := List.getD_eq_default _ _ (by omega)
      rw [hm,hyF,hxi]

/-- Only needed primary and unselected boundary slots must be correct;
    every other boundary slot may be assigned arbitrarily. -/
lemma extracted_correct_on (P : ℕ → Prop) (n : ℕ) (C : Circuit) (keep : ℕ → Bool) (x y : List Bool)
    (hx : x.length = n) (hy : y.length = n + C.size)
    (reads : ReadsNeeded keep P n C.gates) (outputNeeded : P C.output)
    (boundary : ∀ i < n + C.size, P i → i < n ∨ keep i = false →
      y.getD i false = (C.wires x).getD i false) :
    (extracted n C keep).eval y = C.eval x := by
  have hinit := initial_inv_on P n (n + C.size) (n + C.size + C.size) C x y hx hy
    (by omega) (by omega) (fun i hi hP => boundary i (by omega) hP (Or.inl hi))
  have h := extract_sound_on P (n + C.size) (n + C.size + C.size) keep y hy C.gates
    x (List.range n,[]) (by simp [hx,Circuit.size]) (by simp [Circuit.size])
    (by simpa [hx] using reads)
    (by intro i hi hP hk;exact boundary i (by simpa [length_wiresFrom,hx,Circuit.size] using hi) hP (Or.inr hk)) hinit
  exact h.2.2 C.output outputNeeded


lemma readsNeeded_of_prefix (keep : ℕ → Bool) (P : ℕ → Prop) (gs : List Gate) :
    ∀ n, (∀ pre g post, gs = pre ++ g :: post → keep (n + pre.length) = true →
      ∀ i ∈ g.inputs, i < n + pre.length → P i) → ReadsNeeded keep P n gs := by
  induction gs with
  | nil => intro n _; trivial
  | cons g gs ih =>
    intro n h
    constructor
    · simpa using h [] g gs rfl
    · apply ih (n + 1)
      intro pre q post he hk i hi hlt
      have hs : g :: gs = (g :: pre) ++ q :: post := by simp [he]
      have hlen : n + (g :: pre).length = n + 1 + pre.length := by simp;omega
      exact h (g :: pre) q post hs (by rw [hlen];exact hk) i hi (by rw [hlen];exact hlt)

/-- Exactly the output and valid earlier references of selected gates.
    Future references are omitted because their gate-time value is false. -/
def Needed (n : ℕ) (C : Circuit) (keep : ℕ → Bool) (i : ℕ) : Prop :=
  i = C.output ∨ ∃ pre g post, C.gates = pre ++ g :: post ∧
    keep (n + pre.length) = true ∧ i ∈ g.inputs ∧ i < n + pre.length

lemma needed_reads (n : ℕ) (C : Circuit) (keep : ℕ → Bool) :
    ReadsNeeded keep (Needed n C keep) n C.gates := by
  apply readsNeeded_of_prefix
  intro pre g post he hk i hi hlt
  exact Or.inr ⟨pre,g,post,he,hk,hi,hlt⟩

lemma extracted_correct_needed (n : ℕ) (C : Circuit) (keep : ℕ → Bool) (x y : List Bool)
    (hx : x.length = n) (hy : y.length = n + C.size)
    (boundary : ∀ i < n + C.size, Needed n C keep i → i < n ∨ keep i = false →
      y.getD i false = (C.wires x).getD i false) :
    (extracted n C keep).eval y = C.eval x := by
  exact extracted_correct_on (Needed n C keep) n C keep x y hx hy
    (needed_reads n C keep) (Or.inl rfl) boundary

/-- Conditional exact-cost extraction. The boundary may vary arbitrarily with
    the underlying input; only actually needed primary/unselected slots constrain it. -/
lemma selected_subcircuit (n : ℕ) (C : Circuit) (M : Finset ℕ)
    (hM : ∀ j ∈ M, j < C.size) (hC : Monotone2 C) :
    ∃ D : Circuit, Monotone2 D ∧ D.size = M.card ∧
      ∀ x y : List Bool, x.length = n → y.length = n + C.size →
      (∀ i < n + C.size,
        Needed n C (fun j => decide (n ≤ j ∧ j - n ∈ M)) i →
        i < n ∨ i - n ∉ M → y.getD i false = (C.wires x).getD i false) →
      D.eval y = C.eval x := by
  let keep : ℕ → Bool := fun i => decide (n ≤ i ∧ i - n ∈ M)
  refine ⟨extracted n C keep,extracted_monotone2 n C keep hC,
    extracted_size_of_subset n C M hM,?_⟩
  intro x y hx hy boundary
  apply extracted_correct_needed n C keep x y hx hy
  intro i hi hn hb
  apply boundary i hi hn
  rcases hb with hb | hb
  · exact Or.inl hb
  · by_cases h : i < n
    · exact Or.inl h
    · right
      have hk : ¬(n ≤ i ∧ i - n ∈ M) := of_decide_eq_false hb
      intro hm
      exact hk ⟨by omega,hm⟩

end SelectedExtraction

namespace SelectedExtraction

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- Charge only the selected gates when all needed boundary signals are ORs
    of matching variables or constants. Unused boundary slots impose no condition. -/
lemma selected_matching_lower_bound {I : Type*} [Fintype I] [DecidableEq I]
    (n : ℕ) (C : Circuit) (M : Finset ℕ)
    (hM : ∀ j ∈ M, j < C.size) (hC : Monotone2 C)
    (original : (I × Bool → Bool) → Fin n → Bool)
    (S : Fin (n + C.size) → Finset (I × Bool)) (K : Finset (Fin (n + C.size)))
    (correct : ∀ x, C.eval (List.ofFn (original x)) = MatchingLower.target x)
    (boundary : ∀ x i, i < n + C.size →
      Needed n C (fun j => decide (n ≤ j ∧ j - n ∈ M)) i →
      i < n ∨ i - n ∉ M →
      (List.ofFn (MatchingLower.input S K x)).getD i false =
        (C.wires (List.ofFn (original x))).getD i false) :
    2 * Fintype.card I ≤ M.card + 1 := by
  obtain ⟨D,hD,hsize,heval⟩ := selected_subcircuit n C M hM hC
  have restricted : ∀ x,
      D.eval (List.ofFn (MatchingLower.input S K x)) = MatchingLower.target x := by
    intro x
    rw [heval _ _ (by simp) (by simp) (boundary x),correct]
  simpa only [hsize] using MatchingLower.paid_gate_lower_bound S K D hD restricted

end SelectedExtraction

namespace CircuitPlug

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

lemma wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

lemma getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp



/-- Invalid boundary sources are permanently false. Old paid wires are shifted. -/
def rename (B p s : ℕ) (ρ : Fin B → ℕ) (i : ℕ) : ℕ :=
  if h : i < B then if ρ ⟨i,h⟩ < p then ρ ⟨i,h⟩ else p + s else p + (i - B)

def renameGate (B p s : ℕ) (ρ : Fin B → ℕ) (g : Gate) : Gate :=
  ⟨g.op,g.inputs.map (rename B p s ρ)⟩

def plug (B p : ℕ) (D : Circuit) (ρ : Fin B → ℕ) : Circuit :=
  ⟨D.gates.map (renameGate B p D.size ρ),rename B p D.size ρ D.output⟩

lemma rename_new (B p s k : ℕ) (ρ : Fin B → ℕ) :
    rename B p s ρ (B + k) = p + k := by
  simp [rename]

lemma rename_ne_new (B p s k : ℕ) (ρ : Fin B → ℕ) (hk : k < s)
    (i : ℕ) (hi : i ≠ B + k) : rename B p s ρ i ≠ p + k := by
  unfold rename
  split_ifs with h hρ
  · omega
  · omega
  · omega

lemma rename_step (B p s k : ℕ) (ρ : Fin B → ℕ) (old new : List Bool) (v : Bool)
    (hold : old.length = B + k) (hnew : new.length = p + k) (hk : k < s)
    (h : ∀ i, new.getD (rename B p s ρ i) false = old.getD i false) :
    ∀ i, (new ++ [v]).getD (rename B p s ρ i) false = (old ++ [v]).getD i false := by
  intro i
  by_cases hi : i = B + k
  · subst i
    rw [rename_new,←hnew,←hold,getD_snoc_eq,getD_snoc_eq]
  · rw [getD_snoc_ne _ _ _ _ (by rw [hnew];exact rename_ne_new B p s k ρ hk i hi),
      getD_snoc_ne _ _ _ _ (by omega)]
    exact h i

lemma rename_run (B p s : ℕ) (ρ : Fin B → ℕ) (gs : List Gate) :
    ∀ (k : ℕ) (old new : List Bool), old.length = B + k → new.length = p + k →
    k + gs.length ≤ s →
    (∀ i, new.getD (rename B p s ρ i) false = old.getD i false) →
    ∀ i, (wiresFrom (gs.map (renameGate B p s ρ)) new).getD (rename B p s ρ i) false =
      (wiresFrom gs old).getD i false := by
  induction gs with
  | nil => intro k old new _ _ _ h; exact h
  | cons g gs ih =>
    intro k old new hold hnew hcap h
    have heval : (renameGate B p s ρ g).op.eval
        ((renameGate B p s ρ g).inputs.map fun i => new.getD i false) =
        g.op.eval (g.inputs.map fun i => old.getD i false) := by
      simp only [renameGate,List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact h i
    let v := g.op.eval (g.inputs.map fun i => old.getD i false)
    change ∀ i, (wiresFrom (gs.map (renameGate B p s ρ))
        (new ++ [(renameGate B p s ρ g).op.eval
          ((renameGate B p s ρ g).inputs.map fun i => new.getD i false)])).getD
        (rename B p s ρ i) false = (wiresFrom gs (old ++ [v])).getD i false
    rw [heval]
    exact ih (k + 1) (old ++ [v]) (new ++ [v]) (by simp [hold];omega)
      (by simp [hnew];omega) (by simp at hcap;omega)
      (rename_step B p s k ρ old new v hold hnew (by simp at hcap;omega) h)

lemma rename_initial (B p s : ℕ) (ρ : Fin B → ℕ) (w : List Bool) (hw : w.length = p) :
    ∀ i, w.getD (rename B p s ρ i) false =
      (List.ofFn (fun j : Fin B => w.getD (ρ j) false)).getD i false := by
  intro i
  by_cases hi : i < B
  · have oldValue : (List.ofFn (fun j : Fin B => w.getD (ρ j) false)).getD i false =
        w.getD (ρ ⟨i,hi⟩) false := by simp [List.getD_eq_getElem?_getD,hi]
    rw [oldValue]
    simp only [rename,hi,↓reduceDIte]
    split_ifs with hρ
    · rfl
    · rw [List.getD_eq_default _ _ (by omega),List.getD_eq_default _ _ (by omega)]
  · have oldFalse : (List.ofFn (fun j : Fin B => w.getD (ρ j) false)).getD i false = false :=
      List.getD_eq_default _ _ (by simp;omega)
    rw [oldFalse]
    simp only [rename,hi,↓reduceDIte]
    exact List.getD_eq_default _ _ (by omega)

lemma plug_correct (B p : ℕ) (D : Circuit) (ρ : Fin B → ℕ) (w : List Bool)
    (hw : w.length = p) :
    (plug B p D ρ).eval w = D.eval (List.ofFn fun i : Fin B => w.getD (ρ i) false) := by
  exact rename_run B p D.size ρ D.gates 0 (List.ofFn fun i : Fin B => w.getD (ρ i) false) w
    (by simp) (by simpa using hw) (by simp [Circuit.size]) (rename_initial B p D.size ρ w hw) D.output

end CircuitPlug
namespace CircuitPlug

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma plug_size (B p : ℕ) (D : Circuit) (ρ : Fin B → ℕ) :
    (plug B p D ρ).size = D.size := by
  simp [plug,Circuit.size]

lemma plug_monotone2 (B p : ℕ) (D : Circuit) (ρ : Fin B → ℕ) (hD : Monotone2 D) :
    Monotone2 (plug B p D ρ) := by
  intro g hg
  obtain ⟨h,hh,rfl⟩ := List.mem_map.mp hg
  simpa only [renameGate,List.length_map] using hD h hh

/-- Append after earlier gates; their designated output is unused. -/
def plugCircuit (n : ℕ) (P : Circuit) (B : ℕ) (D : Circuit) (ρ : Fin B → ℕ) : Circuit :=
  ⟨P.gates ++ (plug B (n + P.size) D ρ).gates,(plug B (n + P.size) D ρ).output⟩

lemma plugCircuit_wires (n : ℕ) (P : Circuit) (B : ℕ) (D : Circuit) (ρ : Fin B → ℕ)
    (x : List Bool) :
    (plugCircuit n P B D ρ).wires x = (plug B (n + P.size) D ρ).wires (P.wires x) := by
  change wiresFrom (P.gates ++ (plug B (n + P.size) D ρ).gates) x =
    wiresFrom (plug B (n + P.size) D ρ).gates (wiresFrom P.gates x)
  exact wiresFrom_append _ _ _

lemma plugCircuit_correct (n : ℕ) (P : Circuit) (B : ℕ) (D : Circuit) (ρ : Fin B → ℕ)
    (x : List Bool) (hx : x.length = n) :
    (plugCircuit n P B D ρ).eval x =
      D.eval (List.ofFn fun i : Fin B => (P.wires x).getD (ρ i) false) := by
  have hw : (P.wires x).length = n + P.size := by
    rw [wires_eq,length_wiresFrom,hx]
    rfl
  change ((plugCircuit n P B D ρ).wires x).getD (plug B (n + P.size) D ρ).output false = _
  rw [plugCircuit_wires]
  exact plug_correct B (n + P.size) D ρ (P.wires x) hw

lemma plugCircuit_size (n : ℕ) (P : Circuit) (B : ℕ) (D : Circuit) (ρ : Fin B → ℕ) :
    (plugCircuit n P B D ρ).size = P.size + D.size := by
  simp [plugCircuit,plug,Circuit.size]

lemma plugCircuit_monotone2 (n : ℕ) (P : Circuit) (B : ℕ) (D : Circuit) (ρ : Fin B → ℕ)
    (hP : Monotone2 P) (hD : Monotone2 D) : Monotone2 (plugCircuit n P B D ρ) := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact hP g hg
  · exact plug_monotone2 B (n + P.size) D ρ hD g hg

end CircuitPlug


namespace SelectedExtraction

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- Extract the selected gates and plug them after existing gates.
    No graph decomposition or special boundary form is inferred here. -/
lemma selected_subcircuit_after_prefix (n : ℕ) (C : Circuit) (M : Finset ℕ)
    (hM : ∀ j ∈ M, j < C.size) (hC : Monotone2 C)
    (P : Circuit) (hP : Monotone2 P) (ρ : Fin (n + C.size) → ℕ)
    (boundary : ∀ x : Fin n → Bool, ∀ i (hi : i < n + C.size),
      Needed n C (fun j => decide (n ≤ j ∧ j - n ∈ M)) i →
      i < n ∨ i - n ∉ M →
      (P.wires (List.ofFn x)).getD (ρ ⟨i,hi⟩) false =
        (C.wires (List.ofFn x)).getD i false) :
    ∃ E : Circuit, Monotone2 E ∧ E.size = P.size + M.card ∧
      ∀ x : Fin n → Bool, E.eval (List.ofFn x) = C.eval (List.ofFn x) := by
  obtain ⟨D,hD,hsize,correct⟩ := selected_subcircuit n C M hM hC
  refine ⟨CircuitPlug.plugCircuit n P (n + C.size) D ρ,
    CircuitPlug.plugCircuit_monotone2 n P (n + C.size) D ρ hP hD,?_,?_⟩
  · rw [CircuitPlug.plugCircuit_size,hsize]
  · intro x
    rw [CircuitPlug.plugCircuit_correct n P (n + C.size) D ρ (List.ofFn x) (by simp)]
    apply correct (List.ofFn x)
      (List.ofFn fun i : Fin (n + C.size) => (P.wires (List.ofFn x)).getD (ρ i) false)
      (by simp) (by simp)
    intro i hi hn hb
    have h := boundary x i hi hn hb
    simpa [List.getD_eq_getElem?_getD,hi] using h

end SelectedExtraction

namespace MatchingLower

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

variable {I : Type*} [Fintype I] [DecidableEq I] {m : ℕ}

/-- Only matching-edge positives and transversal negatives are used in the cover. -/
lemma separation_cover_on_tests (S : Fin m → Finset (I × Bool)) (K : Finset (Fin m))
    (C : Circuit) (hC : Monotone2 C)
    (positive : ∀ i, C.eval (List.ofFn (input S K (MatchingCapacity.edgeInput i))) = true)
    (negative : ∀ a, C.eval (List.ofFn (input S K (MatchingCapacity.transversalInput a))) = false) :
    ∃ R : Finset (Fin m), R.card ≤ C.size + 1 ∧
      ∀ p : I × (I → Bool), ∃ r ∈ R,
        p ∈ (if r ∈ K then ∅ else MatchingCapacity.separations (S r)) := by
  classical
  obtain ⟨R, hcard, hsep⟩ := HelperSupport.output_support_separates m C hC
  refine ⟨R, hcard, ?_⟩
  intro p
  obtain ⟨r, hr, hp, hn⟩ := hsep (input S K (MatchingCapacity.edgeInput p.1))
    (input S K (MatchingCapacity.transversalInput p.2)) (positive p.1) (negative p.2)
  obtain ⟨hK, hmem⟩ := input_separation S K r p.1 p.2 hp hn
  exact ⟨r, hr, by simpa [hK] using hmem⟩

/-- The bound needs output assumptions only on the two matching test families. -/
lemma paid_gate_lower_bound_on_tests (S : Fin m → Finset (I × Bool)) (K : Finset (Fin m))
    (C : Circuit) (hC : Monotone2 C)
    (positive : ∀ i, C.eval (List.ofFn (input S K (MatchingCapacity.edgeInput i))) = true)
    (negative : ∀ a, C.eval (List.ofFn (input S K (MatchingCapacity.transversalInput a))) = false) :
    2 * Fintype.card I ≤ C.size + 1 := by
  classical
  obtain ⟨R, hcard, hcover⟩ := separation_cover_on_tests S K C hC positive negative
  apply le_trans (SeparationCounting.separation_card_bound R
    (fun r => if r ∈ K then ∅ else MatchingCapacity.separations (S r)) hcover ?_ ?_) hcard
  · intro r _
    by_cases hr : r ∈ K
    · simp [hr]
    · simpa [hr, Fintype.card_fun] using MatchingCapacity.twice_separations_card_le (S r)
  · simp

end MatchingLower

namespace SelectedExtraction

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- Exact-cost extraction only needs boundary agreement on matching-edge positives
    and transversal negatives; all other original assignments are unconstrained. -/
lemma selected_matching_lower_bound_on_tests {I : Type*} [Fintype I] [DecidableEq I]
    (n : ℕ) (C : Circuit) (M : Finset ℕ)
    (hM : ∀ j ∈ M, j < C.size) (hC : Monotone2 C)
    (original : (I × Bool → Bool) → Fin n → Bool)
    (S : Fin (n + C.size) → Finset (I × Bool)) (K : Finset (Fin (n + C.size)))
    (positive : ∀ e, C.eval (List.ofFn (original (MatchingCapacity.edgeInput e))) = true)
    (negative : ∀ a, C.eval (List.ofFn (original (MatchingCapacity.transversalInput a))) = false)
    (positiveBoundary : ∀ e i, i < n + C.size →
      Needed n C (fun j => decide (n ≤ j ∧ j - n ∈ M)) i →
      i < n ∨ i - n ∉ M →
      (List.ofFn (MatchingLower.input S K (MatchingCapacity.edgeInput e))).getD i false =
        (C.wires (List.ofFn (original (MatchingCapacity.edgeInput e)))).getD i false)
    (negativeBoundary : ∀ a i, i < n + C.size →
      Needed n C (fun j => decide (n ≤ j ∧ j - n ∈ M)) i →
      i < n ∨ i - n ∉ M →
      (List.ofFn (MatchingLower.input S K (MatchingCapacity.transversalInput a))).getD i false =
        (C.wires (List.ofFn (original (MatchingCapacity.transversalInput a)))).getD i false) :
    2 * Fintype.card I ≤ M.card + 1 := by
  obtain ⟨D, hD, hsize, heval⟩ := selected_subcircuit n C M hM hC
  have pos : ∀ e, D.eval
      (List.ofFn (MatchingLower.input S K (MatchingCapacity.edgeInput e))) = true := by
    intro e
    rw [heval _ _ (by simp) (by simp) (positiveBoundary e), positive]
  have neg : ∀ a, D.eval
      (List.ofFn (MatchingLower.input S K (MatchingCapacity.transversalInput a))) = false := by
    intro a
    rw [heval _ _ (by simp) (by simp) (negativeBoundary a), negative]
  simpa only [hsize] using MatchingLower.paid_gate_lower_bound_on_tests S K D hD pos neg

end SelectedExtraction

end PEqualNP.Outside.L_meta_1904_aux
