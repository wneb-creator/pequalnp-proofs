import PEqualNP.Defs

-- Partial checkpoint for L-meta-2448.
-- Minimum existence and ownership obstructions only; the posted star-profile conclusion is unproved.


namespace PEqualNP.Outside.L_meta_2448_aux.Existence
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

theorem wf_append (a b : List Gate) (w : List Bool) : wf (a ++ b) w = wf b (wf a w) := by
  simp [wf, List.foldl_append]

def build (n : ℕ) : List (Fin n × Fin n) → List Gate
  | [] => [⟨GateOp.or, []⟩]
  | e :: es => build n es ++ [⟨GateOp.and, [(e.1 : ℕ), (e.2 : ℕ)]⟩,
      ⟨GateOp.or, [n + 2 * es.length, n + 2 * es.length + 1]⟩]

theorem build_len (n : ℕ) : ∀ E : List (Fin n × Fin n), (build n E).length = 1 + 2 * E.length := by
  intro E
  induction E with
  | nil => rfl
  | cons e es ih => simp [build, ih]; omega

theorem build_mono (n : ℕ) : ∀ E : List (Fin n × Fin n), ∀ g ∈ build n E,
    g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro E
  induction E with
  | nil => intro g hg; simp [build] at hg; subst hg; simp
  | cons e es ih =>
    intro g hg
    simp only [build, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with hg | rfl | rfl
    · exact ih g hg
    · simp
    · simp

theorem build_val (n : ℕ) (x : Fin n → Bool) : ∀ E : List (Fin n × Fin n),
    (wf (build n E) (List.ofFn x)).getD (n + 2 * E.length) false
      = E.any (fun e => x e.1 && x e.2) := by
  intro E
  induction E with
  | nil =>
    show ((List.ofFn x) ++ [GateOp.eval GateOp.or ([].map fun i => (List.ofFn x).getD i false)]).getD (n + 2 * 0) false = _
    have := getD_snoc_eq (List.ofFn x) (GateOp.eval GateOp.or ([].map fun i => (List.ofFn x).getD i false))
    rw [List.length_ofFn] at this
    rw [Nat.mul_zero, Nat.add_zero, this]
    rfl
  | cons e es ih =>
    have hlen : (wf (build n es) (List.ofFn x)).length = n + 2 * es.length + 1 := by
      rw [wf_len, build_len, List.length_ofFn]; omega
    have h1 : (wf (build n es) (List.ofFn x)).getD (e.1 : ℕ) false = x e.1 := by
      rw [wf_keep _ _ _ (by simp)]; simp
    have h2 : (wf (build n es) (List.ofFn x)).getD (e.2 : ℕ) false = x e.2 := by
      rw [wf_keep _ _ _ (by simp)]; simp
    show (wf (build n es ++ [⟨GateOp.and, [(e.1 : ℕ), (e.2 : ℕ)]⟩,
      ⟨GateOp.or, [n + 2 * es.length, n + 2 * es.length + 1]⟩]) (List.ofFn x)).getD
        (n + 2 * (es.length + 1)) false = _
    rw [wf_append]
    generalize hW : wf (build n es) (List.ofFn x) = W at *
    show ((W ++ [GateOp.eval GateOp.and ([(e.1 : ℕ), (e.2 : ℕ)].map fun i => W.getD i false)]) ++
      [GateOp.eval GateOp.or ([n + 2 * es.length, n + 2 * es.length + 1].map fun i =>
        (W ++ [GateOp.eval GateOp.and ([(e.1 : ℕ), (e.2 : ℕ)].map fun i => W.getD i false)]).getD i false)]).getD
        (n + 2 * (es.length + 1)) false = _
    have e3 : n + 2 * (es.length + 1) = (W ++ [GateOp.eval GateOp.and ([(e.1 : ℕ), (e.2 : ℕ)].map fun i => W.getD i false)]).length := by
      simp [hlen]; omega
    rw [e3, getD_snoc_eq]
    have e4 : n + 2 * es.length + 1 = W.length := by omega
    simp only [List.map_cons, List.map_nil]
    rw [getD_snoc_lt _ _ _ (by omega : n + 2 * es.length < W.length), e4, getD_snoc_eq, ih, h1, h2]
    simp [GateOp.eval, Bool.or_comm]


lemma graph_minimal_exists : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj], ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x4 ∧ PEqualNP.MetaComplexity.circuitFun x1 x4 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ := by
  classical
  intro n G _
  have hex : ∃ s : ℕ, ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧
      PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧ D.size = s := by
    let E : List (Fin n × Fin n) :=
      ((List.finRange n).product (List.finRange n)).filter (fun e => decide (G.Adj e.1 e.2))
    refine ⟨_, ⟨build n E, n + 2 * E.length⟩, build_mono n E, ?_, rfl⟩
    funext x
    show (wf (build n E) (List.ofFn x)).getD (n + 2 * E.length) false = _
    rw [build_val, Bool.eq_iff_iff]
    simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, List.any_eq_true, Bool.and_eq_true,
      Bool.or_eq_true, decide_eq_true_eq, Finset.notMem_empty, false_and, exists_false, false_or]
    constructor
    · rintro ⟨e, he, h1, h2⟩
      have := (List.mem_filter.mp he).2
      exact ⟨e.1, e.2, by simpa using this, h1, h2⟩
    · rintro ⟨u, v, huv, h1, h2⟩
      exact ⟨(u, v), List.mem_filter.mpr ⟨by simp [List.pair_mem_product], by simpa using huv⟩, h1, h2⟩
  obtain ⟨D, hD, hf, hs⟩ := Nat.find_spec hex
  refine ⟨D, ⟨hD, ?_⟩, hf⟩
  intro D' hD' hf'
  rw [hs]
  exact Nat.find_min' hex ⟨D', hD', hf'.trans hf, rfl⟩

lemma minimal_size_eq (n : ℕ) (C D : Circuit)
    (hC : PEqualNP.MetaComplexity.IsMinimalMonoCircuit n C)
    (hD : PEqualNP.MetaComplexity.IsMinimalMonoCircuit n D)
    (hf : PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.circuitFun n D) :
    C.size = D.size := by
  exact Nat.le_antisymm (hC.2 D hD.1 hf.symm) (hD.2 C hC.1 hf)

lemma minimal_transfer (n : ℕ) (C D : Circuit)
    (hC : PEqualNP.MetaComplexity.IsMinimalMonoCircuit n C)
    (hD : PEqualNP.MetaComplexity.Monotone2 D)
    (hf : PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.circuitFun n C)
    (hsize : D.size ≤ C.size) :
    PEqualNP.MetaComplexity.IsMinimalMonoCircuit n D := by
  refine ⟨hD, ?_⟩
  intro E hE hEf
  exact hsize.trans (hC.2 E hE (hEf.trans hf))

end PEqualNP.Outside.L_meta_2448_aux.Existence


namespace PEqualNP.Outside.L_meta_2448_aux

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

lemma intersecting_edge_family {V : Type} (G : SimpleGraph V) (R : V → V → Prop)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hsub : ∀ a b, R a b → G.Adj a b)
    (hmeet : ∀ a b c d, R a b → R c d → a = c ∨ a = d ∨ b = c ∨ b = d) :
    (∀ a b, ¬ R a b) ∨ ∃ c, ∀ a b, R a b → a = c ∨ b = c := by
  classical
  by_cases hempty : ∀ a b, ¬ R a b
  · exact Or.inl hempty
  right
  push_neg at hempty
  obtain ⟨a, b, hab⟩ := hempty
  by_cases ha : ∀ u v, R u v → u = a ∨ v = a
  · exact ⟨a, ha⟩
  push_neg at ha
  obtain ⟨p, q, hpq, hpa, hqa⟩ := ha
  have hbpq : p = b ∨ q = b := by
    have h := hmeet p q a b hpq hab
    tauto
  have hext : ∃ w, w ≠ a ∧ G.Adj b w ∧
      ∀ u v, R u v → u = b ∨ v = b ∨ u = w ∨ v = w := by
    rcases hbpq with rfl | rfl
    · refine ⟨q, hqa, hsub _ _ hpq, ?_⟩
      intro u v huv
      have h := hmeet u v p q huv hpq
      tauto
    · refine ⟨p, hpa, (hsub _ _ hpq).symm, ?_⟩
      intro u v huv
      have h := hmeet u v p q huv hpq
      tauto
  obtain ⟨w, hwa, hbw, hmeetw⟩ := hext
  refine ⟨b, ?_⟩
  intro u v huv
  by_contra hn
  push_neg at hn
  have huva : u = a ∨ v = a := by
    have h := hmeet u v a b huv hab
    tauto
  have huvw : u = w ∨ v = w := by
    have h := hmeetw u v huv
    tauto
  have hwaAdj : G.Adj w a := by
    rcases huva with h | h
    · subst u
      have hvw : v = w := huvw.resolve_left (Ne.symm hwa)
      simpa [hvw] using (hsub _ _ huv).symm
    · subst v
      have huw : u = w := huvw.resolve_right (Ne.symm hwa)
      simpa [huw] using hsub _ _ huv
  exact htri a b w (hsub _ _ hab) hbw hwaAdj

def OwnedEdgesIntersect (n : Nat) (G : SimpleGraph (Fin n)) (C : Circuit) : Prop :=
  ∀ j u v p q, G.Adj u v → G.Adj p q →
    Owns n C j u v → Owns n C j p q → u = p ∨ u = q ∨ v = p ∨ v = q

lemma star_iff_owned_edges_intersect (n : Nat) (G : SimpleGraph (Fin n)) (C : Circuit)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a) :
    HasStarProfile n G C ↔ OwnedEdgesIntersect n G C := by
  constructor
  · intro hstar j u v p q huv hpq hown hown'
    rcases hstar j hown.1 hown.2.1 with hempty | ⟨c, hc⟩
    · exact (hempty u v huv hown).elim
    have h1 := hc u v huv hown
    have h2 := hc p q hpq hown'
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> aesop
  · intro hmeet j hj hop
    have h := intersecting_edge_family G
      (fun u v => G.Adj u v ∧ Owns n C j u v) htri
      (fun _ _ h => h.1)
      (fun u v p q h1 h2 => hmeet j u v p q h1.1 h2.1 h1.2 h2.2)
    rcases h with hempty | ⟨c, hc⟩
    · left
      intro u v huv hown
      exact hempty u v ⟨huv, hown⟩
    · right
      exact ⟨c, fun u v huv hown => hc u v ⟨huv, hown⟩⟩

lemma nonstar_disjoint_owned_edges (n : Nat) (G : SimpleGraph (Fin n)) (C : Circuit)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hstar : ¬ HasStarProfile n G C) :
    ∃ j u v p q, G.Adj u v ∧ G.Adj p q ∧
      Owns n C j u v ∧ Owns n C j p q ∧
      u ≠ p ∧ u ≠ q ∧ v ≠ p ∧ v ≠ q := by
  classical
  rw [star_iff_owned_edges_intersect n G C htri] at hstar
  unfold OwnedEdgesIntersect at hstar
  push_neg at hstar
  exact hstar

end PEqualNP.Outside.L_meta_2448_aux


namespace PEqualNP.Outside.L_meta_2448_aux.PairSound

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq_foldl, foldl_stepWire_length, List.length_ofFn]

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

def W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma W_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then W n C x i else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gj := by rw [gateAt_eq C k hk]; exact hgj
  rw [hga]
  let w0 := pre.foldl stepWire (List.ofFn x)
  have hw0_len : w0.length = n + k := by
    simp [w0, foldl_stepWire_length, hpre_len]
  have hCj : W n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [foldl_stepWire_getD_lt post (stepWire w0 gj) (n + k) (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < n + k
  · simp only [hi, ↓reduceIte]
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append]
    exact (foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact getD_ge_length w0 i (by omega)

lemma W_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    W n C x u = x ⟨u, hu⟩ := by
  simp only [W]
  rw [wires_eq_foldl, foldl_stepWire_getD_lt C.gates (List.ofFn x) u (by simpa using hu)]
  simp [List.getD_eq_getElem?_getD, hu]

lemma W_or (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (a b : ℕ) (hin : (gateAt C k).inputs = [a, b])
    (ha : a < n + k) (hb : b < n + k) :
    W n C x (n + k) = (W n C x a || W n C x b) := by
  rw [W_gate n C x k hk, hop, hin]
  simp [GateOp.eval, ha, hb]

lemma W_and (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.and) (a b : ℕ) (hin : (gateAt C k).inputs = [a, b])
    (ha : a < n + k) (hb : b < n + k) :
    W n C x (n + k) = (W n C x a && W n C x b) := by
  rw [W_gate n C x k hk, hop, hin]
  simp [GateOp.eval, ha, hb]

open PEqualNP.EdgeOwnership in
lemma coneFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

open PEqualNP.EdgeOwnership in
lemma coneStep_getD_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
    (coneStep n cs g).getD cs.length [] =
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) []) := by
  simp [coneStep, List.getD_eq_getElem?_getD]

open PEqualNP.EdgeOwnership in
lemma coneStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (coneStep n cs g).getD m [] = cs.getD m [] := by
  simp [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

open PEqualNP.EdgeOwnership in
lemma coneFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (coneStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (coneStep n cs g) (by simp [coneStep]; omega)]
    exact coneStep_getD_lt n cs g k hk

open PEqualNP.EdgeOwnership in
lemma inCone_iff (n : ℕ) (C : Circuit) (i k : ℕ) (hk : k < C.gates.length) :
    InCone n C i k ↔ ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧
      (i = w - n ∨ InCone n C i (w - n)) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : cones n C = post.foldl (coneStep n) (coneStep n (pre.foldl (coneStep n) []) gk) := by
    simp only [cones]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (coneStep n) []).length = k := by
    rw [coneFold_length]; simp [hpre_len]
  have hl1 : (coneStep n (pre.foldl (coneStep n) []) gk).length = k + 1 := by
    simp [coneStep, hl0]
  have h1 : (cones n C).getD k [] =
      (gk.inputs.filter (fun w => decide (n ≤ w ∧ w < n + k))).flatMap
        (fun w => (w - n) :: (pre.foldl (coneStep n) []).getD (w - n) []) := by
    rw [hc, coneFold_getD_lt n post _ k (by omega)]
    have h := coneStep_getD_last n (pre.foldl (coneStep n) []) gk
    rw [hl0] at h
    exact h
  have h2 : ∀ m, m < k → (cones n C).getD m [] = (pre.foldl (coneStep n) []).getD m [] := by
    intro m hm
    rw [hc, coneFold_getD_lt n post _ m (by omega)]
    exact coneStep_getD_lt n _ gk m (by omega)
  unfold InCone
  rw [h1]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hw, hn, hlt⟩, h⟩
    refine ⟨w, hw, hn, hlt, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [h2 (w - n) (by omega)]
      exact h
  · rintro ⟨w, hw, hn, hlt, h⟩
    refine ⟨w, ⟨hw, hn, hlt⟩, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [← h2 (w - n) (by omega)]
      exact h


lemma ite_true_iff (c : Prop) [Decidable c] (b : Bool) :
    (if c then b else false) = true ↔ c ∧ b = true := by
  by_cases h : c <;> simp [h]

lemma W_and_iff (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.and) :
    W n C x (n + k) = true ↔ ∀ w ∈ (gateAt C k).inputs, w < n + k ∧ W n C x w = true := by
  rw [W_gate n C x k hk, hop]
  simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
  constructor
  · intro h w hw
    exact (ite_true_iff _ _).mp (h _ ⟨w, hw, rfl⟩)
  · rintro h b ⟨w, hw, rfl⟩
    exact (ite_true_iff _ _).mpr (h w hw)

lemma W_or_iff (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) :
    W n C x (n + k) = true ↔ ∃ w ∈ (gateAt C k).inputs, w < n + k ∧ W n C x w = true := by
  rw [W_gate n C x k hk, hop]
  simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
  constructor
  · rintro ⟨b, ⟨w, hw, rfl⟩, h⟩
    exact ⟨w, hw, (ite_true_iff _ _).mp h⟩
  · rintro ⟨w, hw, h⟩
    exact ⟨_, ⟨w, hw, rfl⟩, (ite_true_iff _ _).mpr h⟩

open PEqualNP.EdgeOwnership in
lemma inCone_lt (n : ℕ) (C : Circuit) :
    ∀ k, k < C.gates.length → ∀ i, InCone n C i k → i < k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk i hi
    obtain ⟨w, _, hn, hlt, h⟩ := (inCone_iff n C i k hk).mp hi
    rcases h with h | h
    · omega
    · have := ih (w - n) (by omega) (by omega) i h
      omega

lemma gate_mono2 (C : Circuit) (hM : Monotone2 C) (k : ℕ) (hk : k < C.gates.length) :
    ((gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) ∧
      (gateAt C k).inputs.length ≤ 2 := by
  have hg := hM (C.gates[k]) (List.getElem_mem hk)
  rw [← gateAt_eq C k hk] at hg
  have h1 := hg.1
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
  exact ⟨h1, hg.2⟩

def Dom (n : ℕ) (C : Circuit) (t : Fin n) (w : ℕ) : Prop :=
  ∀ y : Fin n → Bool, y t = true → W n C y w = true

open PEqualNP.EdgeOwnership in
lemma descent (n : ℕ) (C : Circuit) (hM : Monotone2 C) (x : Fin n → Bool) :
    ∀ k, k < C.gates.length → W n C x (n + k) = true →
      (gateAt C k).op = GateOp.and ∨
      (∃ i, InCone n C i k ∧ (gateAt C i).op = GateOp.and ∧ W n C x (n + i) = true) ∨
      (∃ u : Fin n, x u = true ∧ Dom n C u (n + k)) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk hx
    rcases (gate_mono2 C hM k hk).1 with hop | hop
    · exact Or.inl hop
    · obtain ⟨w, hw, hlt, hwx⟩ := (W_or_iff n C x k hk hop).mp hx
      by_cases hwn : w < n
      · right; right
        refine ⟨⟨w, hwn⟩, ?_, ?_⟩
        · rw [← W_input n C x w hwn]; exact hwx
        · intro y hy
          refine (W_or_iff n C y k hk hop).mpr ⟨w, hw, hlt, ?_⟩
          rw [W_input n C y w hwn]; exact hy
      · obtain ⟨k', rfl⟩ : ∃ k', w = n + k' := ⟨w - n, by omega⟩
        have he : n + k' - n = k' := by omega
        rcases ih k' (by omega) (by omega) hwx with h | ⟨i, hi, hia, hix⟩ | ⟨u, hu, hdom⟩
        · right; left
          exact ⟨k', (inCone_iff n C k' k hk).mpr ⟨n + k', hw, by omega, hlt, Or.inl (by omega)⟩,
            h, hwx⟩
        · right; left
          exact ⟨i, (inCone_iff n C i k hk).mpr
            ⟨n + k', hw, by omega, hlt, Or.inr (by rw [he]; exact hi)⟩, hia, hix⟩
        · right; right
          exact ⟨u, hu, fun y hy => (W_or_iff n C y k hk hop).mpr ⟨n + k', hw, hlt, hdom y hy⟩⟩

open PEqualNP.EdgeOwnership in
lemma owns_dom (n : ℕ) (C : Circuit) (hM : Monotone2 C) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) (p q : Fin n) (ho : Owns n C j p q) :
    ∀ w ∈ (gateAt C j).inputs, w < n + j ∧ (Dom n C p w ∨ Dom n C q w) := by
  obtain ⟨_, _, hval, hno⟩ := ho
  intro w hw
  have hval' : W n C (pairInput p q) (n + j) = true := hval
  obtain ⟨hlt, hwx⟩ := (W_and_iff n C _ j hj hop).mp hval' w hw
  refine ⟨hlt, ?_⟩
  by_cases hwn : w < n
  · rw [W_input n C _ w hwn] at hwx
    have h' : (⟨w, hwn⟩ : Fin n) = p ∨ (⟨w, hwn⟩ : Fin n) = q := of_decide_eq_true hwx
    rcases h' with h | h
    · left
      intro y hy
      rw [W_input n C y w hwn, h]; exact hy
    · right
      intro y hy
      rw [W_input n C y w hwn, h]; exact hy
  · obtain ⟨k', rfl⟩ : ∃ k', w = n + k' := ⟨w - n, by omega⟩
    have he : n + k' - n = k' := by omega
    have hk'j : k' < j := by omega
    have hc : InCone n C k' j :=
      (inCone_iff n C k' j hj).mpr ⟨n + k', hw, by omega, hlt, Or.inl (by omega)⟩
    rcases descent n C hM (pairInput p q) k' (by omega) hwx with h | ⟨i, hi, hia, hix⟩ | ⟨t, ht, hdom⟩
    · have hf : W n C (pairInput p q) (n + k') = false := hno k' hk'j hc h
      rw [hwx] at hf
      exact absurd hf (by simp)
    · have hc2 : InCone n C i j := (inCone_iff n C i j hj).mpr
        ⟨n + k', hw, by omega, hlt, Or.inr (by rw [he]; exact hi)⟩
      have hij := inCone_lt n C j hj i hc2
      have hf : W n C (pairInput p q) (n + i) = false := hno i hij hc2 hia
      rw [hix] at hf
      exact absurd hf (by simp)
    · have h' : t = p ∨ t = q := of_decide_eq_true ht
      rcases h' with h | h
      · left; rw [← h]; exact hdom
      · right; rw [← h]; exact hdom

open PEqualNP.EdgeOwnership in
lemma dom_adj (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (j : ℕ)
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and)
    (hsound : ∀ u v : Fin n, gateVal n C j (pairInput u v) = true → G.Adj u v)
    (s t : Fin n)
    (h : ∀ w ∈ (gateAt C j).inputs, w < n + j ∧ (Dom n C s w ∨ Dom n C t w)) :
    G.Adj s t := by
  have hs : pairInput s t s = true := by simp [pairInput]
  have ht : pairInput s t t = true := by simp [pairInput]
  have hv : W n C (pairInput s t) (n + j) = true :=
    (W_and_iff n C _ j hj hop).mpr (fun w hw => ⟨(h w hw).1,
      (h w hw).2.elim (fun d => d (pairInput s t) hs) (fun d => d (pairInput s t) ht)⟩)
  exact hsound s t hv

open PEqualNP.EdgeOwnership in
theorem pair_sound_star : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → ∀ j : ℕ, j < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ u v : Fin n, PEqualNP.EdgeOwnership.gateVal n C j (PEqualNP.EdgeOwnership.pairInput u v) = true → G.Adj u v) → (∀ u v : Fin n, G.Adj u v → ¬ PEqualNP.EdgeOwnership.Owns n C j u v) ∨ ∃ s : Fin n, ∀ p q : Fin n, G.Adj p q → PEqualNP.EdgeOwnership.Owns n C j p q → p = s ∨ q = s := by
  intro n G _ h4 C hM j hj hop hsound
  by_cases hown : ∀ u v : Fin n, G.Adj u v → ¬ Owns n C j u v
  · exact Or.inl hown
  right
  push_neg at hown
  obtain ⟨u0, v0, _, hown0⟩ := hown
  have F1 := owns_dom n C hM j hj hop
  have F3 := dom_adj n G C j hj hop hsound
  have hlen := (gate_mono2 C hM j hj).2
  have hF0 := F1 u0 v0 hown0
  rcases hin : (gateAt C j).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩
  · have hadj := F3 u0 u0 (by rw [hin]; intro w hw; simp at hw)
    exact absurd rfl hadj.ne
  · have h1 := hF0 a (by rw [hin]; simp)
    rcases h1.2 with d | d
    · have hadj := F3 u0 u0 (by
        rw [hin]; intro w hw
        have hwa : w = a := by simpa using hw
        rw [hwa]; exact ⟨h1.1, Or.inl d⟩)
      exact absurd rfl hadj.ne
    · have hadj := F3 v0 v0 (by
        rw [hin]; intro w hw
        have hwa : w = a := by simpa using hw
        rw [hwa]; exact ⟨h1.1, Or.inl d⟩)
      exact absurd rfl hadj.ne
  · have hlta : a < n + j := (hF0 a (by rw [hin]; simp)).1
    have hltb : b < n + j := (hF0 b (by rw [hin]; simp)).1
    have hbip : ∀ s t, Dom n C s a → Dom n C t b → G.Adj s t := by
      intro s t da db
      refine F3 s t ?_
      rw [hin]; intro w hw
      have hwab : w = a ∨ w = b := by simpa using hw
      rcases hwab with hwa | hwb
      · rw [hwa]; exact ⟨hlta, Or.inl da⟩
      · rw [hwb]; exact ⟨hltb, Or.inr db⟩
    have hloop : ∀ t, Dom n C t a → Dom n C t b → False :=
      fun t da db => absurd rfl (hbip t t da db).ne
    have hA : ∀ p q, Owns n C j p q →
        (Dom n C p a ∧ Dom n C q b) ∨ (Dom n C q a ∧ Dom n C p b) := by
      intro p q ho
      have h1 := F1 p q ho a (by rw [hin]; simp)
      have h2 := F1 p q ho b (by rw [hin]; simp)
      rcases h1.2 with pa | qa <;> rcases h2.2 with pb | qb
      · exact (hloop p pa pb).elim
      · exact Or.inl ⟨pa, qb⟩
      · exact Or.inr ⟨qa, pb⟩
      · exact (hloop q qa qb).elim
    by_cases hAs : ∀ s s', Dom n C s a → Dom n C s' a → s = s'
    · obtain ⟨s0, hs0⟩ : ∃ s0, Dom n C s0 a := by
        rcases hA u0 v0 hown0 with h | h
        · exact ⟨u0, h.1⟩
        · exact ⟨v0, h.1⟩
      refine ⟨s0, fun p q _ ho => ?_⟩
      rcases hA p q ho with h | h
      · exact Or.inl (hAs p s0 h.1 hs0)
      · exact Or.inr (hAs q s0 h.1 hs0)
    · push_neg at hAs
      obtain ⟨a1, a2, ha1, ha2, hne⟩ := hAs
      have hBs : ∀ t t', Dom n C t b → Dom n C t' b → t = t' := by
        intro t t' ht ht'
        by_contra hne'
        exact h4 a1 t a2 t' hne hne' ⟨hbip a1 t ha1 ht, (hbip a2 t ha2 ht).symm,
          hbip a2 t' ha2 ht', (hbip a1 t' ha1 ht').symm⟩
      obtain ⟨s0, hs0⟩ : ∃ s0, Dom n C s0 b := by
        rcases hA u0 v0 hown0 with h | h
        · exact ⟨v0, h.2⟩
        · exact ⟨u0, h.2⟩
      refine ⟨s0, fun p q _ ho => ?_⟩
      rcases hA p q ho with h | h
      · exact Or.inr (hBs q s0 h.2 hs0)
      · exact Or.inl (hBs p s0 h.2 hs0)
  · have hl : (a :: b :: c :: r).length ≤ 2 := hin ▸ hlen
    simp only [List.length_cons] at hl
    omega


open PEqualNP.EdgeOwnership

lemma star_profile_of_pair_sound (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬(G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (C : Circuit) (hM : Monotone2 C)
    (hpair : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∀ u v : Fin n, gateVal n C j (pairInput u v) = true → G.Adj u v) :
    HasStarProfile n G C := by
  intro j hj hop
  exact pair_sound_star n G hfour C hM j hj hop (hpair j hj hop)

lemma bad_pair_of_not_star (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬(G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (C : Circuit) (hM : Monotone2 C) (hbad : ¬ HasStarProfile n G C) :
    ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧
      ∃ u v : Fin n, ¬G.Adj u v ∧ gateVal n C j (pairInput u v) = true := by
  classical
  by_contra hn
  apply hbad
  apply star_profile_of_pair_sound n G hfour C hM
  intro j hj hop u v hv
  by_contra hadj
  exact hn ⟨j, hj, hop, u, v, hadj, hv⟩

end PEqualNP.Outside.L_meta_2448_aux.PairSound


namespace PEqualNP.Outside.L_meta_2448_aux.StarExistence

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_2448_aux.Existence

lemma and_reads_input (n : ℕ) (C : Circuit) (j : ℕ) (u : Fin n)
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and)
    (hu : u.val ∈ (gateAt C j).inputs) (x : Fin n → Bool)
    (hx : gateVal n C j x = true) : x u = true := by
  let pre := C.gates.take j
  let post := C.gates.drop (j + 1)
  let g := C.gates[j]'hj
  have hpre : pre.length = j := by
    simp [pre, Nat.min_eq_left (Nat.le_of_lt hj)]
  have hga : gateAt C j = g := by
    simp [gateAt, g, List.getD_eq_getElem?_getD, hj]
  have hgs : C.gates = (pre ++ [g]) ++ post := by
    dsimp [pre, post, g]
    rw [List.append_assoc]
    change C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1)
    rw [List.cons_getElem_drop_succ, List.take_append_drop]
  let W := wf pre (List.ofFn x)
  have hW : W.length = n + j := by
    dsimp [W]
    rw [wf_len, List.length_ofFn, hpre]
  have hval : gateVal n C j x =
      g.op.eval (g.inputs.map fun i => W.getD i false) := by
    change (wf C.gates (List.ofFn x)).getD (n + j) false = _
    rw [hgs, wf_prefix (pre ++ [g]) post (List.ofFn x) (n + j)
      (by simp [hpre]), wf_snoc]
    change (W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)]).getD
      (n + j) false = _
    rw [← hW, getD_snoc_eq]
  rw [hga] at hop hu
  rw [hval, hop] at hx
  change (g.inputs.map fun i => W.getD i false).all id = true at hx
  have hraw := List.all_eq_true.mp hx _ (List.mem_map.mpr ⟨u.val, hu, rfl⟩)
  have hinput : W.getD u.val false = x u := by
    dsimp [W]
    rw [wf_keep _ _ _ (by simp)]
    simp
  rw [hinput] at hraw
  exact hraw

lemma raw_ands_star (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit)
    (hraw : ∀ g ∈ C.gates, g.op = GateOp.and →
      ∃ u : Fin n, u.val ∈ g.inputs) : HasStarProfile n G C := by
  intro j hj hop
  have hmem : gateAt C j ∈ C.gates := by
    have he : gateAt C j = C.gates[j]'hj := by
      simp [gateAt, List.getD_eq_getElem?_getD, hj]
    rw [he]
    exact List.getElem_mem hj
  obtain ⟨u, hu⟩ := hraw (gateAt C j) hmem hop
  right
  refine ⟨u, ?_⟩
  intro a b _hab hown
  have h := and_reads_input n C j u hj hop hu (pairInput a b) hown.2.2.1
  have he : u = a ∨ u = b := of_decide_eq_true h
  exact he.imp Eq.symm Eq.symm

lemma build_and_raw (n : ℕ) : ∀ E : List (Fin n × Fin n),
    ∀ g ∈ build n E, g.op = GateOp.and → ∃ u : Fin n, u.val ∈ g.inputs := by
  intro E
  induction E with
  | nil =>
    intro g hg hop
    simp only [build, List.mem_cons, List.not_mem_nil, or_false] at hg
    subst g
    cases hop
  | cons e es ih =>
    intro g hg hop
    simp only [build, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with hg | rfl | rfl
    · exact ih g hg hop
    · exact ⟨e.1, by simp⟩
    · cases hop

lemma build_profile (n : ℕ) (G : SimpleGraph (Fin n)) (E : List (Fin n × Fin n)) :
    HasStarProfile n G ⟨build n E, n + 2 * E.length⟩ := by
  apply raw_ands_star
  exact build_and_raw n E

lemma graph_star_exists (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    ∃ C : Circuit, Monotone2 C ∧ circuitFun n C = graphFun G ∅ ∧ HasStarProfile n G C := by
  classical
  let E : List (Fin n × Fin n) :=
    ((List.finRange n).product (List.finRange n)).filter (fun e => decide (G.Adj e.1 e.2))
  refine ⟨⟨build n E, n + 2 * E.length⟩, build_mono n E, ?_, build_profile n G E⟩
  funext x
  show (wf (build n E) (List.ofFn x)).getD (n + 2 * E.length) false = _
  rw [build_val, Bool.eq_iff_iff]
  simp only [graphFun, List.any_eq_true, Bool.and_eq_true,
    Bool.or_eq_true, decide_eq_true_eq, Finset.notMem_empty, false_and, exists_false, false_or]
  constructor
  · rintro ⟨e, he, h1, h2⟩
    have := (List.mem_filter.mp he).2
    exact ⟨e.1, e.2, by simpa using this, h1, h2⟩
  · rintro ⟨u, v, huv, h1, h2⟩
    exact ⟨(u, v), List.mem_filter.mpr ⟨by simp [List.pair_mem_product], by simpa using huv⟩, h1, h2⟩

lemma star_minimal_exists (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    ∃ C : Circuit, Monotone2 C ∧ circuitFun n C = graphFun G ∅ ∧ HasStarProfile n G C ∧
      ∀ D : Circuit, Monotone2 D → circuitFun n D = graphFun G ∅ →
        HasStarProfile n G D → C.size ≤ D.size := by
  classical
  obtain ⟨C, hC, hCf, hCs⟩ := graph_star_exists n G
  have hex : ∃ s : ℕ, ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧
      HasStarProfile n G D ∧ D.size = s := ⟨C.size, C, hC, hCf, hCs, rfl⟩
  obtain ⟨D, hD, hDf, hDs, hs⟩ := Nat.find_spec hex
  refine ⟨D, hD, hDf, hDs, ?_⟩
  intro E hE hEf hEs
  rw [hs]
  exact Nat.find_min' hex ⟨E, hE, hEf, hEs, rfl⟩

end PEqualNP.Outside.L_meta_2448_aux.StarExistence


namespace PEqualNP.Outside.L_meta_2448_aux.EdgePruning

open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

lemma graph_true_iff (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by
  simp [graphFun]

lemma pair_below (n : ℕ) (x : Fin n → Bool) (u v : Fin n)
    (hu : x u = true) (hv : x v = true) :
    ∀ w, pairInput u v w = true → x w = true := by
  intro w hw
  have he : w = u ∨ w = v := of_decide_eq_true hw
  rcases he with rfl | rfl
  · exact hu
  · exact hv

theorem exact_of_decreasing_and_edge_preserving (n : ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (f h : (Fin n → Bool) → Bool)
    (hmono : ∀ x y, (∀ v, x v = true → y v = true) → h x = true → h y = true)
    (hcorrect : f = graphFun G ∅)
    (hdecrease : ∀ x, h x = true → f x = true)
    (hedges : ∀ u v : Fin n, G.Adj u v → h (pairInput u v) = f (pairInput u v)) :
    h = graphFun G ∅ := by
  funext x
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hx
    rw [← hcorrect]
    exact hdecrease x hx
  · intro hx
    obtain ⟨u, v, huv, hu, hv⟩ := (graph_true_iff n G x).mp hx
    have hp : h (pairInput u v) = true := by
      rw [hedges u v huv, hcorrect]
      apply (graph_true_iff n G (pairInput u v)).mpr
      exact ⟨u, v, huv, by simp [pairInput], by simp [pairInput]⟩
    exact hmono (pairInput u v) x (pair_below n x u v hu hv) hp

end PEqualNP.Outside.L_meta_2448_aux.EdgePruning


namespace PEqualNP.Outside.L_meta_2448_aux.EdgeContext

open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_2448_aux.EdgePruning

lemma graph_pair_true_adj (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v : Fin n) (h : graphFun G ∅ (pairInput u v) = true) : G.Adj u v := by
  obtain ⟨a, b, hab, ha, hb⟩ := (graph_true_iff n G (pairInput u v)).mp h
  have ha' : a = u ∨ a = v := of_decide_eq_true ha
  have hb' : b = u ∨ b = v := of_decide_eq_true hb
  rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
  · exact (hab.ne rfl).elim
  · exact hab
  · exact hab.symm
  · exact (hab.ne rfl).elim

theorem context_rejects_singletons (n : ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj]
    (htri : ∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬G.Adj c a)
    (f k : (Fin n → Bool) → Bool)
    (fm : ∀ x y, (∀ z, x z = true → y z = true) → f x = true → f y = true)
    (km : ∀ x y, (∀ z, x z = true → y z = true) → k x = true → k y = true)
    (sound : ∀ x, f x = true → k x = true → graphFun G ∅ x = true)
    (u v : Fin n) (huv : G.Adj u v)
    (hu : f (pairInput u u) = true) (hv : f (pairInput v v) = true) :
    ∀ w : Fin n, k (pairInput w w) = false := by
  intro w
  cases hc : k (pairInput w w) with
  | false => rfl
  | true =>
    have adjacent (a : Fin n) (ha : f (pairInput a a) = true) : G.Adj a w := by
      have hfa : f (pairInput a w) = true := fm _ _
        (pair_below n (pairInput a w) a a (by simp [pairInput]) (by simp [pairInput])) ha
      have hkw : k (pairInput a w) = true := km _ _
        (pair_below n (pairInput a w) w w (by simp [pairInput]) (by simp [pairInput])) hc
      exact graph_pair_true_adj n G a w (sound _ hfa hkw)
    exact (htri u v w huv (adjacent v hv) (adjacent u hu).symm).elim

end PEqualNP.Outside.L_meta_2448_aux.EdgeContext


namespace PEqualNP.Outside.L_meta_2448_aux.PrivateExchange

lemma product_with_literal_context (a b A B : Bool)
    (ha : a = true → A = true) (hb : b = true → B = true) :
    ((A && B) && (a || b)) = ((a && B) || (b && A)) := by
  cases a <;> cases b <;> cases A <;> cases B <;> simp_all

lemma shared_literal_absorption (a A B : Bool) :
    ((a || A) && (a || B)) = (a || (A && B)) := by
  cases a <;> cases A <;> cases B <;> rfl

lemma path_four_identity (a b c d : Bool) :
    (((a || c) && (b || d)) && (b || c)) =
      ((b && (a || c)) || (c && (b || d))) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

end PEqualNP.Outside.L_meta_2448_aux.PrivateExchange


namespace PEqualNP.Outside.L_meta_2448_aux.LinearCleanup

variable {α : Type*}

def Hit (S : Set α) (x : α → Prop) : Prop := ∃ v ∈ S, x v

def Edge (G : SimpleGraph α) (x : α → Prop) : Prop :=
  ∃ u v, G.Adj u v ∧ x u ∧ x v

def Product (A B : Set α) (x : α → Prop) : Prop := Hit A x ∧ Hit B x

def Cleanup (A B T : Set α) (x : α → Prop) : Prop := Product A B x ∧ Hit T x

def Reduced (A B T : Set α) (x : α → Prop) : Prop :=
  (Hit (A ∩ T) x ∧ Hit B x) ∨ (Hit (B ∩ T) x ∧ Hit A x)

def Centers (G : SimpleGraph α) (A B : Set α) : Set α :=
  {a | a ∈ A ∧ ∀ b ∈ B, G.Adj a b}

def PairSound (G : SimpleGraph α) (A B T : Set α) : Prop :=
  ∀ s t, Cleanup A B T (fun v => v = s ∨ v = t) → G.Adj s t

lemma edge_pair_iff (G : SimpleGraph α) (s t : α) :
    Edge G (fun v => v = s ∨ v = t) ↔ G.Adj s t := by
  constructor
  · rintro ⟨u, v, huv, hu, hv⟩
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact (huv.ne rfl).elim
    · exact huv
    · exact huv.symm
    · exact (huv.ne rfl).elim
  · intro h
    exact ⟨s, t, h, Or.inl rfl, Or.inr rfl⟩

lemma reduced_le_cleanup (A B T : Set α) (x : α → Prop) :
    Reduced A B T x → Cleanup A B T x := by
  rintro (⟨⟨a, ha, hax⟩, hb⟩ | ⟨⟨b, hb, hbx⟩, ha⟩)
  · exact ⟨⟨⟨a, ha.1, hax⟩, hb⟩, ⟨a, ha.2, hax⟩⟩
  · exact ⟨⟨ha, ⟨b, hb.1, hbx⟩⟩, ⟨b, hb.2, hbx⟩⟩

lemma cleanup_pair_reduced (A B T : Set α) (hdis : Disjoint A B) (s t : α) :
    Cleanup A B T (fun v => v = s ∨ v = t) ↔
      Reduced A B T (fun v => v = s ∨ v = t) := by
  constructor
  · rintro ⟨⟨⟨a, ha, hax⟩, ⟨b, hb, hbx⟩⟩, c, hc, hcx⟩
    have hab : a ≠ b := by
      intro heq
      subst b
      exact Set.disjoint_left.mp hdis ha hb
    have hca : c = a ∨ c = b := by
      rcases hax with rfl | rfl <;> rcases hbx with rfl | rfl
      · exact (hab rfl).elim
      · exact hcx
      · exact hcx.symm
      · exact (hab rfl).elim
    rcases hca with hca | hcb
    · exact Or.inl ⟨⟨a, ⟨ha, hca ▸ hc⟩, hax⟩, ⟨b, hb, hbx⟩⟩
    · exact Or.inr ⟨⟨b, ⟨hb, hcb ▸ hc⟩, hbx⟩, ⟨a, ha, hax⟩⟩
  · exact reduced_le_cleanup A B T _

lemma sound_context_left (G : SimpleGraph α) (A B T : Set α)
    (hsound : PairSound G A B T) :
    A ∩ T ⊆ Centers G A B := by
  intro a ha
  refine ⟨ha.1, ?_⟩
  intro b hb
  apply hsound a b
  exact ⟨⟨⟨a, ha.1, Or.inl rfl⟩, ⟨b, hb, Or.inr rfl⟩⟩,
    ⟨a, ha.2, Or.inl rfl⟩⟩

lemma sound_context_right (G : SimpleGraph α) (A B T : Set α)
    (hsound : PairSound G A B T) :
    B ∩ T ⊆ Centers G B A := by
  intro b hb
  refine ⟨hb.1, ?_⟩
  intro a ha
  apply hsound b a
  exact ⟨⟨⟨a, ha, Or.inr rfl⟩, ⟨b, hb.1, Or.inl rfl⟩⟩,
    ⟨b, hb.2, Or.inl rfl⟩⟩

lemma centers_subsingleton (G : SimpleGraph α) (A B : Set α)
    (hfour : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d →
      G.Adj d a → a = c ∨ b = d)
    (b d : α) (hb : b ∈ B) (hd : d ∈ B) (hbd : b ≠ d) :
    (Centers G A B).Subsingleton := by
  intro a ha c hc
  rcases hfour a b c d (ha.2 b hb) (hc.2 b hb).symm
    (hc.2 d hd) (ha.2 d hd).symm with hac | hbd'
  · exact hac
  · exact (hbd hbd').elim

theorem shared_linear_cleanup (G : SimpleGraph α) (A B : Set α)
    (hdis : Disjoint A B)
    (hfour : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d →
      G.Adj d a → a = c ∨ b = d)
    (a c b d : α) (ha : a ∈ A) (hc : c ∈ A) (hac : a ≠ c)
    (hb : b ∈ B) (hd : d ∈ B) (hbd : b ≠ d) :
    (Centers G A B).Subsingleton ∧ (Centers G B A).Subsingleton ∧
      ∀ T : Set α, PairSound G A B T →
        A ∩ T ⊆ Centers G A B ∧ B ∩ T ⊆ Centers G B A ∧
        (∀ x, Reduced A B T x → Cleanup A B T x) ∧
        ∀ s t, Cleanup A B T (fun v => v = s ∨ v = t) ↔
          Reduced A B T (fun v => v = s ∨ v = t) := by
  refine ⟨centers_subsingleton G A B hfour b d hb hd hbd,
    centers_subsingleton G B A hfour a c ha hc hac, ?_⟩
  intro T hsound
  exact ⟨sound_context_left G A B T hsound, sound_context_right G A B T hsound,
    reduced_le_cleanup A B T, cleanup_pair_reduced A B T hdis⟩

lemma reduced_sound (G : SimpleGraph α) (A B T : Set α)
    (hsound : PairSound G A B T) (x : α → Prop) :
    Reduced A B T x → Edge G x := by
  rintro (⟨⟨a, ha, hax⟩, b, hb, hbx⟩ | ⟨⟨b, hb, hbx⟩, a, ha, hax⟩)
  · exact ⟨a, b, (sound_context_left G A B T hsound ha).2 b hb, hax, hbx⟩
  · exact ⟨b, a, (sound_context_right G A B T hsound hb).2 a ha, hbx, hax⟩

end PEqualNP.Outside.L_meta_2448_aux.LinearCleanup


namespace PEqualNP.Outside.L_meta_2448_aux.TwoCenterRepair

open PEqualNP.Outside.L_meta_2448_aux.LinearCleanup

variable {α : Type*}

def Repair (A B : Set α) (c d : α) (x : α → Prop) : Prop :=
  (x c ∧ Hit B x) ∨ (x d ∧ Hit A x)

lemma repair_mono (A B : Set α) (c d : α) (x y : α → Prop)
    (hxy : ∀ v, x v → y v) : Repair A B c d x → Repair A B c d y := by
  rintro (⟨hc, b, hb, hbx⟩ | ⟨hd, a, ha, hax⟩)
  · exact Or.inl ⟨hxy c hc, b, hb, hxy b hbx⟩
  · exact Or.inr ⟨hxy d hd, a, ha, hxy a hax⟩

lemma disjoint_of_centers (G : SimpleGraph α) (A B : Set α) (c d : α)
    (htri : ∀ a b e, G.Adj a b → G.Adj b e → ¬G.Adj e a)
    (hc : c ∈ Centers G A B) (hd : d ∈ Centers G B A) : Disjoint A B := by
  apply Set.disjoint_left.mpr
  intro v hvA hvB
  exact htri c d v (hc.2 d hd.1) (hd.2 v hvA) (hc.2 v hvB).symm

lemma cross_edge_centered (G : SimpleGraph α) (A B : Set α) (c d : α)
    (hfour : ∀ a b e f, G.Adj a b → G.Adj b e → G.Adj e f →
      G.Adj f a → a = e ∨ b = f)
    (hc : c ∈ Centers G A B) (hd : d ∈ Centers G B A)
    (a b : α) (ha : a ∈ A) (hb : b ∈ B) (hab : G.Adj a b) : a = c ∨ b = d := by
  rcases hfour c b a d (hc.2 b hb) hab.symm (hd.2 a ha).symm
    (hc.2 d hd.1).symm with hca | hbd
  · exact Or.inl hca.symm
  · exact Or.inr hbd

lemma repair_le_product (G : SimpleGraph α) (A B : Set α) (c d : α)
    (hc : c ∈ Centers G A B) (hd : d ∈ Centers G B A) (x : α → Prop) :
    Repair A B c d x → Product A B x := by
  rintro (⟨hcx, hb⟩ | ⟨hdx, ha⟩)
  · exact ⟨⟨c, hc.1, hcx⟩, hb⟩
  · exact ⟨ha, ⟨d, hd.1, hdx⟩⟩

lemma repair_sound (G : SimpleGraph α) (A B : Set α) (c d : α)
    (hc : c ∈ Centers G A B) (hd : d ∈ Centers G B A) (x : α → Prop) :
    Repair A B c d x → Edge G x := by
  rintro (⟨hcx, b, hb, hbx⟩ | ⟨hdx, a, ha, hax⟩)
  · exact ⟨c, b, hc.2 b hb, hcx, hbx⟩
  · exact ⟨d, a, hd.2 a ha, hdx, hax⟩

lemma repair_preserves_edges (G : SimpleGraph α) (A B : Set α) (c d : α)
    (hdis : Disjoint A B)
    (hfour : ∀ a b e f, G.Adj a b → G.Adj b e → G.Adj e f →
      G.Adj f a → a = e ∨ b = f)
    (hc : c ∈ Centers G A B) (hd : d ∈ Centers G B A)
    (s t : α) (hst : G.Adj s t) :
    Product A B (fun v => v = s ∨ v = t) ↔
      Repair A B c d (fun v => v = s ∨ v = t) := by
  constructor
  · rintro ⟨⟨a, ha, hax⟩, ⟨b, hb, hbx⟩⟩
    have hab : a ≠ b := by
      intro heq
      subst b
      exact Set.disjoint_left.mp hdis ha hb
    have hedge : G.Adj a b := by
      rcases hax with rfl | rfl <;> rcases hbx with rfl | rfl
      · exact (hab rfl).elim
      · exact hst
      · exact hst.symm
      · exact (hab rfl).elim
    rcases cross_edge_centered G A B c d hfour hc hd a b ha hb hedge with hac | hbd
    · exact Or.inl ⟨hac ▸ hax, b, hb, hbx⟩
    · exact Or.inr ⟨hbd ▸ hbx, a, ha, hax⟩
  · exact repair_le_product G A B c d hc hd _

theorem cofactor_repair (G : SimpleGraph α) (A B : Set α) (c d : α)
    (hdis : Disjoint A B)
    (hfour : ∀ a b e f, G.Adj a b → G.Adj b e → G.Adj e f →
      G.Adj f a → a = e ∨ b = f)
    (hc : c ∈ Centers G A B) (hd : d ∈ Centers G B A)
    (R K : (α → Prop) → Prop)
    (hR : ∀ x y, (∀ v, x v → y v) → R x → R y)
    (hF : ∀ x, Edge G x ↔ R x ∨ (Product A B x ∧ K x)) :
    ∀ x, Edge G x ↔ R x ∨ Repair A B c d x := by
  intro x
  constructor
  · rintro ⟨s, t, hst, hsx, htx⟩
    have hxy : ∀ v, (v = s ∨ v = t) → x v := by
      intro v hv
      rcases hv with rfl | rfl
      · exact hsx
      · exact htx
    have he := (edge_pair_iff G s t).mpr hst
    rcases (hF _).mp he with hr | ⟨hp, _⟩
    · exact Or.inl (hR _ x hxy hr)
    · exact Or.inr (repair_mono A B c d _ x hxy
        ((repair_preserves_edges G A B c d hdis hfour hc hd s t hst).mp hp))
  · rintro (hr | hh)
    · exact (hF x).mpr (Or.inl hr)
    · exact repair_sound G A B c d hc hd x hh

end PEqualNP.Outside.L_meta_2448_aux.TwoCenterRepair
