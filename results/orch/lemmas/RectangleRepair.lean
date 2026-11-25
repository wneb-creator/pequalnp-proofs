import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2448_aux.ExternalRepair

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

lemma wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

lemma wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

lemma wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

lemma getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

lemma eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (U V : List Bool) (h : ∀ i, U.getD i false = true → V.getD i false = true) :
    op.eval (ins.map fun i => U.getD i false) = true →
    op.eval (ins.map fun i => V.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun hall i hi => h i (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, hv⟩ => ⟨i, hi, h i hv⟩

lemma ofFn_mono (n : ℕ) (x y : Fin n → Bool) (hxy : ∀ v : Fin n, x v = true → y v = true)
    (w : ℕ) : (List.ofFn x).getD w false = true → (List.ofFn y).getD w false = true := by
  by_cases hw : w < n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, dite_true, Option.getD_some]
    exact hxy ⟨w, hw⟩
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp


lemma mono2 (gs : List Gate)
    (hleg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ U V : List Bool, U.length = V.length →
      (∀ i, U.getD i false = true → V.getD i false = true) →
      ∀ i, (wf gs U).getD i false = true → (wf gs V).getD i false = true := by
  induction gs with
  | nil => intro U V _ h i; exact h i
  | cons g gs ih =>
    intro U V hlen h i
    have hg := (hleg g (by simp)).1
    have := ih (fun g' hg' => hleg g' (by simp [hg']))
      (U ++ [g.op.eval (g.inputs.map fun i => U.getD i false)])
      (V ++ [g.op.eval (g.inputs.map fun i => V.getD i false)]) (by simp [hlen]) (by
        intro t
        rcases Nat.lt_trichotomy t U.length with ht | ht | ht
        · rw [getD_snoc_lt _ _ _ ht, getD_snoc_lt _ _ _ (by omega)]; exact h t
        · subst ht
          rw [getD_snoc_eq]
          have e2 := getD_snoc_eq V (g.op.eval (g.inputs.map fun i => V.getD i false))
          rw [← hlen] at e2
          rw [e2]
          exact eval_mono g.op hg g.inputs U V h
        · rw [getD_snoc_gt _ _ _ ht]; intro hf; exact absurd hf (by simp)) i
    simpa [wf] using this

lemma wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

lemma wf_append (a b : List Gate) (w : List Bool) : wf (a ++ b) w = wf b (wf a w) := by
  simp [wf, List.foldl_append]

lemma wf_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wf (g :: gs) w = wf gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover

lemma gate_val_eq (n j : ℕ) (C : Circuit) (hj : j < C.gates.length)
    (x : Fin n → Bool) :
    gateVal n C j x = C.gates[j].op.eval (C.gates[j].inputs.map fun i =>
      (wf (C.gates.take j) (List.ofFn x)).getD i false) := by
  change (wf C.gates (List.ofFn x)).getD (n+j) false = _
  have hs : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j+1) := by
    have hs : C.gates.set j C.gates[j] =
        C.gates.take j ++ C.gates[j] :: C.gates.drop (j+1) := by
      rw [List.set_eq_take_append_cons_drop]
      simp [hj]
    simpa using hs
  conv_lhs => rw [hs]
  rw [wf_append, wf_cons]
  have hl : (wf (C.gates.take j) (List.ofFn x)).length = n+j := by
    simp [wf_len, List.length_take, Nat.min_eq_left hj.le]
  rw [wf_keep _ _ _ (by simp [hl]), ← hl, getD_snoc_eq]

lemma circuit_mono (n : ℕ) (C : Circuit) (hm : Monotone2 C)
    (x y : Fin n → Bool) (hxy : ∀ v, x v = true → y v = true) :
    circuitFun n C x = true → circuitFun n C y = true := by
  apply mono2 C.gates
  · intro g hg
    simpa using hm g hg
  · simp
  · exact ofFn_mono n x y hxy

lemma graph_sandwich (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D : Circuit) (hm : Monotone2 D)
    (hbelow : ∀ x : Fin n → Bool, circuitFun n D x = true → graphFun G ∅ x = true)
    (hedges : ∀ u v : Fin n, G.Adj u v → circuitFun n D (pairInput u v) = true) :
    circuitFun n D = graphFun G ∅ := by
  funext x
  apply Bool.eq_iff_iff.mpr
  refine ⟨hbelow x, ?_⟩
  intro hx
  obtain ⟨u, v, huv, hu, hv⟩ : ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
    simpa [graphFun] using hx
  apply circuit_mono n D hm (pairInput u v) x _ (hedges u v huv)
  intro w hw
  have h : w = u ∨ w = v := of_decide_eq_true hw
  rcases h with rfl | rfl
  · exact hu
  · exact hv

lemma graph_rewrite (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C D : Circuit) (hm : Monotone2 D) (hC : circuitFun n C = graphFun G ∅)
    (hdown : ∀ x : Fin n → Bool, circuitFun n D x = true → circuitFun n C x = true)
    (hedges : ∀ u v : Fin n, G.Adj u v → circuitFun n D (pairInput u v) = true) :
    circuitFun n D = circuitFun n C := by
  rw [hC]
  apply graph_sandwich n G D hm _ hedges
  intro x hx
  rw [← hC]
  exact hdown x hx

set_option maxHeartbeats 800000 in
lemma gate_semantic_le (n : ℕ) (C D : Circuit) (hm : Monotone2 C)
    (hlen : D.gates.length = C.gates.length) (hout : D.output = C.output)
    (x : Fin n → Bool)
    (hexc : ∀ k (hk : k < C.gates.length), D.gates[k] ≠ C.gates[k] →
      gateVal n D k x = true → gateVal n C k x = true) :
    circuitFun n D x = true → circuitFun n C x = true := by
  classical
  have hall : ∀ k, k ≤ C.gates.length → ∀ w,
      (wf (D.gates.take k) (List.ofFn x)).getD w false = true →
      (wf (C.gates.take k) (List.ofFn x)).getD w false = true := by
    intro k
    induction k with
    | zero => intro _ _; exact id
    | succ k ih =>
      intro hk w
      have hkC : k < C.gates.length := by omega
      have hkD : k < D.gates.length := by omega
      have ih := ih (by omega)
      have hlC : (wf (C.gates.take k) (List.ofFn x)).length = n+k := by
        simp [wf_len, List.length_take, Nat.min_eq_left hkC.le]
      have hlD : (wf (D.gates.take k) (List.ofFn x)).length = n+k := by
        simp [wf_len, List.length_take, Nat.min_eq_left hkD.le]
      have hval : D.gates[k].op.eval (D.gates[k].inputs.map fun i =>
          (wf (D.gates.take k) (List.ofFn x)).getD i false) = true →
          C.gates[k].op.eval (C.gates[k].inputs.map fun i =>
          (wf (C.gates.take k) (List.ofFn x)).getD i false) = true := by
        by_cases heq : D.gates[k] = C.gates[k]
        · rw [heq]
          apply eval_mono
          · exact (hm C.gates[k] (List.getElem_mem _)).1
          · exact ih
        · have hh := hexc k hkC heq
          rw [gate_val_eq n k D hkD, gate_val_eq n k C hkC] at hh
          exact hh
      rw [List.take_succ_eq_append_getElem hkD, List.take_succ_eq_append_getElem hkC,
        wf_snoc, wf_snoc]
      rcases Nat.lt_trichotomy w (n+k) with hw | hw | hw
      · rw [getD_snoc_lt _ _ _ (by omega), getD_snoc_lt _ _ _ (by omega)]
        exact ih w
      · rw [hw, ← hlD, getD_snoc_eq, hlD, ← hlC, getD_snoc_eq]
        exact hval
      · rw [getD_snoc_gt _ _ _ (by omega)]
        simp
  have he := hall C.gates.length (by rfl) C.output
  rw [← hlen, List.take_length, hlen, List.take_length] at he
  change (wf D.gates (List.ofFn x)).getD D.output false = true → _
  rw [hout]
  exact he

lemma binary_gate_value (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (op : GateOp) (u v : ℕ) (hgate : C.gates[j] = ⟨op,[u,v]⟩)
    (hu : u < n+j) (hv : v < n+j) (x : Fin n → Bool) :
    gateVal n C j x = op.eval [(C.wires (List.ofFn x)).getD u false,
      (C.wires (List.ofFn x)).getD v false] := by
  rw [gate_val_eq n j C hj, hgate]
  simp only [List.map_cons, List.map_nil]
  rw [← wire_take C.gates (List.ofFn x) j u (by simpa using hu) hj.le,
    ← wire_take C.gates (List.ofFn x) j v (by simpa using hv) hj.le]
  rfl

set_option maxHeartbeats 800000 in
lemma external_reader_repair (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C D : Circuit) (hmC : Monotone2 C) (hmD : Monotone2 D)
    (hC : circuitFun n C = graphFun G ∅)
    (hlen : D.gates.length = C.gates.length) (hout : D.output = C.output)
    (g h t : ℕ) (hgt : g < t) (hht : h < t) (ht : t < C.gates.length)
    (hCt : C.gates[t] = ⟨GateOp.and, [n+g,n+h]⟩)
    (hDt : D.gates[t] = ⟨GateOp.or, [n+g,n+h]⟩)
    (hkeep : ∀ k (hk : k < C.gates.length), k ≠ g → k ≠ h → k ≠ t →
      D.gates[k] = C.gates[k])
    (hcleang : ∀ x : Fin n → Bool, gateVal n D g x = true → graphFun G ∅ x = true)
    (hcleanh : ∀ x : Fin n → Bool, gateVal n D h x = true → graphFun G ∅ x = true)
    (hcover : ∀ u v : Fin n, G.Adj u v →
      (gateVal n C g (pairInput u v) = true ∨ gateVal n C h (pairInput u v) = true) →
      gateVal n D g (pairInput u v) = true ∨ gateVal n D h (pairInput u v) = true)
    (hreach : ∀ x : Fin n → Bool, gateVal n D t x = true → circuitFun n D x = true) :
    circuitFun n D = graphFun G ∅ := by
  have htD : t < D.gates.length := by omega
  have evalC : ∀ x : Fin n → Bool,
      gateVal n C t x = (gateVal n C g x && gateVal n C h x) := by
    intro x
    rw [binary_gate_value n C t ht GateOp.and (n+g) (n+h) hCt (by omega) (by omega)]
    simp [GateOp.eval, gateVal]
  have evalD : ∀ x : Fin n → Bool,
      gateVal n D t x = (gateVal n D g x || gateVal n D h x) := by
    intro x
    rw [binary_gate_value n D t htD GateOp.or (n+g) (n+h) hDt (by omega) (by omega)]
    simp [GateOp.eval, gateVal]
  apply graph_sandwich n G D hmD
  · intro x hx
    by_contra hf
    have hc : circuitFun n C x = true := by
      apply gate_semantic_le n C D hmC hlen hout x ?_ hx
      intro k hk hneq hDk
      by_cases hkg : k = g
      · subst k; exact (hf (hcleang x hDk)).elim
      by_cases hkh : k = h
      · subst k; exact (hf (hcleanh x hDk)).elim
      by_cases hkt : k = t
      · subst k
        rw [evalD, Bool.or_eq_true] at hDk
        rcases hDk with hd | hd
        · exact (hf (hcleang x hd)).elim
        · exact (hf (hcleanh x hd)).elim
      · exact (hneq (hkeep k hk hkg hkh hkt)).elim
    rw [hC] at hc
    exact hf hc
  · intro u v huv
    let x := pairInput u v
    by_cases hactive : gateVal n C g x = true ∨ gateVal n C h x = true
    · apply hreach x
      rw [evalD, Bool.or_eq_true]
      exact hcover u v huv hactive
    · have hg0 : gateVal n C g x = false := Bool.eq_false_iff.mpr (fun h => hactive (Or.inl h))
      have hh0 : gateVal n C h x = false := Bool.eq_false_iff.mpr (fun h => hactive (Or.inr h))
      have ht0 : gateVal n C t x = false := by rw [evalC, hg0]; rfl
      have hCx : circuitFun n C x = true := by
        rw [hC]
        simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
          Bool.false_or, decide_eq_true_eq]
        exact ⟨u, v, huv, by simp [x, pairInput], by simp [x, pairInput]⟩
      apply gate_semantic_le n D C hmD hlen.symm hout.symm x ?_ hCx
      intro k hk hneq hCk
      have hkC : k < C.gates.length := by omega
      by_cases hkg : k = g
      · subst k; rw [hg0] at hCk; contradiction
      by_cases hkh : k = h
      · subst k; rw [hh0] at hCk; contradiction
      by_cases hkt : k = t
      · subst k; rw [ht0] at hCk; contradiction
      · exact (hneq (hkeep k hkC hkg hkh hkt).symm).elim

end PEqualNP.Outside.L_meta_2448_aux.ExternalRepair


namespace PEqualNP.Outside.L_meta_2448_aux.FourVertexGeometry

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover

lemma cross_cases {V : Type*} (G : SimpleGraph V)
    (htriangle : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hfour : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d)
    (a b c d : V) (hab : G.Adj a b) (hcd : G.Adj c d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    (¬ G.Adj a d ∧ ¬ G.Adj b c ∧ ¬ G.Adj a c ∧ ¬ G.Adj b d) ∨
    (G.Adj a d ∧ ¬ G.Adj b c ∧ ¬ G.Adj a c ∧ ¬ G.Adj b d) ∨
    (¬ G.Adj a d ∧ G.Adj b c ∧ ¬ G.Adj a c ∧ ¬ G.Adj b d) ∨
    (¬ G.Adj a d ∧ ¬ G.Adj b c ∧ G.Adj a c ∧ ¬ G.Adj b d) ∨
    (¬ G.Adj a d ∧ ¬ G.Adj b c ∧ ¬ G.Adj a c ∧ G.Adj b d) := by
  classical
  by_cases ead : G.Adj a d
  · have nbc : ¬ G.Adj b c := by
      intro ebc
      exact (hfour a d c b ead hcd.symm ebc.symm hab.symm).elim hac hbd.symm
    have nac : ¬ G.Adj a c := fun eac => htriangle a c d eac hcd ead.symm
    have nbd : ¬ G.Adj b d := fun ebd => htriangle a b d hab ebd ead.symm
    exact Or.inr (Or.inl ⟨ead, nbc, nac, nbd⟩)
  · by_cases ebc : G.Adj b c
    · have nac : ¬ G.Adj a c := fun eac => htriangle a b c hab ebc eac.symm
      have nbd : ¬ G.Adj b d := fun ebd => htriangle b c d ebc hcd ebd.symm
      exact Or.inr (Or.inr (Or.inl ⟨ead, ebc, nac, nbd⟩))
    · by_cases eac : G.Adj a c
      · have nbd : ¬ G.Adj b d := by
          intro ebd
          exact (hfour a c d b eac hcd ebd.symm hab.symm).elim had hbc.symm
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ead, ebc, eac, nbd⟩)))
      · by_cases ebd : G.Adj b d
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨ead, ebc, eac, ebd⟩)))
        · exact Or.inl ⟨ead, ebc, eac, ebd⟩

def chosenEdges {V : Type*} (k : Fin 5) (a b c d : V) : List (V × V) :=
  match k.val with
  | 1 => [(a,b), (a,d), (c,d)]
  | 2 => [(a,b), (b,c), (c,d)]
  | 3 => [(a,b), (a,c), (c,d)]
  | 4 => [(a,b), (b,d), (c,d)]
  | _ => [(a,b), (c,d)]

def repairLeft (k : Fin 5) (a b c d : Bool) : Bool :=
  match k.val with
  | 1 => a && (b || d)
  | 2 => c && (b || d)
  | 3 => c && d
  | _ => a && b

def repairRight (k : Fin 5) (a b c d : Bool) : Bool :=
  match k.val with
  | 2 => a && b
  | 3 => a && (b || c)
  | 4 => d && (b || c)
  | _ => c && d

lemma repair_left_below_rectangle : ∀ (k : Fin 5) (a b c d : Bool),
    repairLeft k a b c d = true → ((a || c) && (b || d)) = true := by decide

lemma repair_right_below_rectangle : ∀ (k : Fin 5) (a b c d : Bool),
    repairRight k a b c d = true → ((a || d) && (b || c)) = true := by decide

lemma repair_output_edges {V : Type*} (k : Fin 5) (a b c d : V) (x : V → Bool) :
    (repairLeft k (x a) (x b) (x c) (x d) ||
      repairRight k (x a) (x b) (x c) (x d)) = true ↔
    ∃ u v, (u,v) ∈ chosenEdges k a b c d ∧ x u = true ∧ x v = true := by
  fin_cases k <;>
    simp [repairLeft, repairRight, chosenEdges, Bool.or_eq_true, Bool.and_eq_true,
      and_assoc, or_and_right, exists_or] <;>
    tauto

lemma chosen_edges_characterization {V : Type*} (G : SimpleGraph V)
    (a b c d : V) (hab : G.Adj a b) (hcd : G.Adj c d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (k : Fin 5)
    (ead : G.Adj a d ↔ k = 1) (ebc : G.Adj b c ↔ k = 2)
    (eac : G.Adj a c ↔ k = 3) (ebd : G.Adj b d ↔ k = 4) :
    (∀ u v, (u,v) ∈ chosenEdges k a b c d → G.Adj u v) ∧
    ∀ u v, G.Adj u v →
      (u = a ∨ u = b ∨ u = c ∨ u = d) →
      (v = a ∨ v = b ∨ v = c ∨ v = d) →
      (u,v) ∈ chosenEdges k a b c d ∨ (v,u) ∈ chosenEdges k a b c d := by
  have hba := hab.symm
  have hdc := hcd.symm
  have ead' : G.Adj d a ↔ k = 1 := ⟨fun h => ead.mp h.symm, fun h => (ead.mpr h).symm⟩
  have ebc' : G.Adj c b ↔ k = 2 := ⟨fun h => ebc.mp h.symm, fun h => (ebc.mpr h).symm⟩
  have eac' : G.Adj c a ↔ k = 3 := ⟨fun h => eac.mp h.symm, fun h => (eac.mpr h).symm⟩
  have ebd' : G.Adj d b ↔ k = 4 := ⟨fun h => ebd.mp h.symm, fun h => (ebd.mpr h).symm⟩
  constructor
  · intro u v huv
    fin_cases k <;> simp_all [chosenEdges] <;> aesop
  · intro u v huv hu hv
    rcases hu with rfl | rfl | rfl | rfl <;>
      rcases hv with rfl | rfl | rfl | rfl <;>
      fin_cases k <;> simp_all [chosenEdges]

lemma four_vertex_cover {V : Type*} (G : SimpleGraph V)
    (htriangle : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hfour : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d)
    (a b c d : V) (hab : G.Adj a b) (hcd : G.Adj c d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    ∃ k : Fin 5, (∀ u v, (u,v) ∈ chosenEdges k a b c d → G.Adj u v) ∧
    ∀ u v, G.Adj u v →
      (u = a ∨ u = b ∨ u = c ∨ u = d) →
      (v = a ∨ v = b ∨ v = c ∨ v = d) →
      (u,v) ∈ chosenEdges k a b c d ∨ (v,u) ∈ chosenEdges k a b c d := by
  rcases cross_cases G htriangle hfour a b c d hab hcd hac had hbc hbd with
    h | h | h | h | h
  · refine ⟨0, chosen_edges_characterization G a b c d hab hcd hac had hbc hbd 0 ?_ ?_ ?_ ?_⟩ <;>
      simp_all
  · refine ⟨1, chosen_edges_characterization G a b c d hab hcd hac had hbc hbd 1 ?_ ?_ ?_ ?_⟩ <;>
      simp_all
  · refine ⟨2, chosen_edges_characterization G a b c d hab hcd hac had hbc hbd 2 ?_ ?_ ?_ ?_⟩ <;>
      simp_all
  · refine ⟨3, chosen_edges_characterization G a b c d hab hcd hac had hbc hbd 3 ?_ ?_ ?_ ?_⟩ <;>
      simp_all
  · refine ⟨4, chosen_edges_characterization G a b c d hab hcd hac had hbc hbd 4 ?_ ?_ ?_ ?_⟩ <;>
      simp_all

lemma pair_members {V : Type*} (Q : V → Prop) (u v p q : V)
    (hp : p = u ∨ p = v) (hq : q = u ∨ q = v) (hne : p ≠ q)
    (hpQ : Q p) (hqQ : Q q) : Q u ∧ Q v := by
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;> simp_all

lemma active_pair_members (n : ℕ) (a b c d u v : Fin n)
    (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d)
    (hactive : (((pairInput u v a || pairInput u v c) &&
      (pairInput u v b || pairInput u v d)) ||
      ((pairInput u v a || pairInput u v d) &&
      (pairInput u v b || pairInput u v c))) = true) :
    (u = a ∨ u = b ∨ u = c ∨ u = d) ∧
      (v = a ∨ v = b ∨ v = c ∨ v = d) := by
  let Q (w : Fin n) := w = a ∨ w = b ∨ w = c ∨ w = d
  have haQ : Q a := by simp [Q]
  have hbQ : Q b := by simp [Q]
  have hcQ : Q c := by simp [Q]
  have hdQ : Q d := by simp [Q]
  simp only [Bool.or_eq_true, Bool.and_eq_true, pairInput, decide_eq_true_eq] at hactive
  rcases hactive with ⟨ha | hc, hb | hd⟩ | ⟨ha | hd, hb | hc⟩
  · exact pair_members Q u v a b ha hb hab haQ hbQ
  · exact pair_members Q u v a d ha hd had haQ hdQ
  · exact pair_members Q u v c b hc hb hbc.symm hcQ hbQ
  · exact pair_members Q u v c d hc hd hcd hcQ hdQ
  · exact pair_members Q u v a b ha hb hab haQ hbQ
  · exact pair_members Q u v a c ha hc hac haQ hcQ
  · exact pair_members Q u v d b hd hb hbd.symm hdQ hbQ
  · exact pair_members Q u v d c hd hc hcd.symm hdQ hcQ

lemma repair_choice (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (htriangle : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hfour : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d)
    (a b c d : Fin n) (hab : G.Adj a b) (hcd : G.Adj c d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    ∃ k : Fin 5,
      (∀ x : Fin n → Bool, repairLeft k (x a) (x b) (x c) (x d) = true →
        graphFun G ∅ x = true) ∧
      (∀ x : Fin n → Bool, repairRight k (x a) (x b) (x c) (x d) = true →
        graphFun G ∅ x = true) ∧
      ∀ u v : Fin n, G.Adj u v →
        (((pairInput u v a || pairInput u v c) &&
          (pairInput u v b || pairInput u v d)) ||
          ((pairInput u v a || pairInput u v d) &&
          (pairInput u v b || pairInput u v c))) = true →
        (repairLeft k (pairInput u v a) (pairInput u v b) (pairInput u v c) (pairInput u v d) ||
          repairRight k (pairInput u v a) (pairInput u v b) (pairInput u v c) (pairInput u v d)) = true := by
  obtain ⟨k, hgood, hcover⟩ := four_vertex_cover G htriangle hfour a b c d hab hcd hac had hbc hbd
  have clean : ∀ x : Fin n → Bool,
      (repairLeft k (x a) (x b) (x c) (x d) || repairRight k (x a) (x b) (x c) (x d)) = true →
      graphFun G ∅ x = true := by
    intro x hx
    obtain ⟨u, v, huv, hu, hv⟩ := (repair_output_edges k a b c d x).mp hx
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq]
    exact ⟨u, v, hgood u v huv, hu, hv⟩
  refine ⟨k, ?_, ?_, ?_⟩
  · intro x hx
    exact clean x (by simp only [hx, Bool.true_or])
  · intro x hx
    exact clean x (by simp only [hx, Bool.or_true])
  · intro u v huv hactive
    obtain ⟨hu, hv⟩ := active_pair_members n a b c d u v hab.ne hcd.ne hac had hbc hbd hactive
    apply (repair_output_edges k a b c d (pairInput u v)).mpr
    rcases hcover u v huv hu hv with he | he
    · exact ⟨u, v, he, by simp [pairInput], by simp [pairInput]⟩
    · exact ⟨v, u, he, by simp [pairInput], by simp [pairInput]⟩

end PEqualNP.Outside.L_meta_2448_aux.FourVertexGeometry

namespace PEqualNP.Outside.L_meta_2448_aux.RectangleRepair

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_2448_aux.ExternalRepair
open PEqualNP.Outside.L_meta_2448_aux.FourVertexGeometry

def leftGate (n q : ℕ) (a b c d : Fin n) (k : Fin 5) : Gate :=
  match k.val with
  | 1 => ⟨.and, [a.val,n+q]⟩
  | 2 => ⟨.and, [c.val,n+q]⟩
  | 3 => ⟨.and, [c.val,d.val]⟩
  | _ => ⟨.and, [a.val,b.val]⟩

def rightGate (n s : ℕ) (a b c d : Fin n) (k : Fin 5) : Gate :=
  match k.val with
  | 2 => ⟨.and, [a.val,b.val]⟩
  | 3 => ⟨.and, [a.val,n+s]⟩
  | 4 => ⟨.and, [d.val,n+s]⟩
  | _ => ⟨.and, [c.val,d.val]⟩

def repairCircuit (n : ℕ) (C : Circuit) (g h t q s : ℕ)
    (a b c d : Fin n) (k : Fin 5) : Circuit :=
  ⟨((C.gates.set g (leftGate n q a b c d k)).set h (rightGate n s a b c d k)).set t
    ⟨.or, [n+g,n+h]⟩, C.output⟩

lemma set_model (n : ℕ) (C : Circuit) (j : ℕ) (r : Gate)
    (hC : PEqualNP.TopForm.IsAO2 n C)
    (hrop : r.op = GateOp.and ∨ r.op = GateOp.or) (hrlen : r.inputs.length = 2)
    (hrback : ∀ w ∈ r.inputs, w < n+j) :
    PEqualNP.TopForm.IsAO2 n ⟨C.gates.set j r, C.output⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    rcases List.mem_or_eq_of_mem_set hz with hz | rfl
    · exact hC.1 z hz
    · exact hrop
  · intro k hk w hw
    have hkC : k < C.gates.length := by simpa using hk
    have he : gateAt ⟨C.gates.set j r, C.output⟩ k =
        if j = k then r else gateAt C k := by
      unfold gateAt
      rw [List.getD_eq_getElem _ _ hk, List.getElem_set,
        List.getD_eq_getElem _ _ hkC]
    rw [he] at hw
    by_cases hjk : j = k
    · subst j
      exact hrback w (by simpa using hw)
    · exact hC.2.1 k hkC w (by simpa [hjk] using hw)
  · intro z hz
    rcases List.mem_or_eq_of_mem_set hz with hz | rfl
    · exact hC.2.2 z hz
    · exact hrlen

lemma repair_model (n : ℕ) (C : Circuit) (g h t q s : ℕ)
    (a b c d : Fin n) (k : Fin 5) (hC : PEqualNP.TopForm.IsAO2 n C)
    (hgt : g < t) (hht : h < t) (hqg : q < g) (hsh : s < h) :
    PEqualNP.TopForm.IsAO2 n (repairCircuit n C g h t q s a b c d k) := by
  have hL : (leftGate n q a b c d k).op = GateOp.and := by fin_cases k <;> rfl
  have hR : (rightGate n s a b c d k).op = GateOp.and := by fin_cases k <;> rfl
  have hl : (leftGate n q a b c d k).inputs.length = 2 := by fin_cases k <;> rfl
  have hr : (rightGate n s a b c d k).inputs.length = 2 := by fin_cases k <;> rfl
  have hlb : ∀ w ∈ (leftGate n q a b c d k).inputs, w < n+g := by
    fin_cases k <;> simp only [leftGate, List.mem_cons, List.not_mem_nil, or_false] <;>
      intro w hw <;> rcases hw with rfl | rfl
    all_goals have := a.isLt; have := b.isLt; have := c.isLt; have := d.isLt; omega
  have hrb : ∀ w ∈ (rightGate n s a b c d k).inputs, w < n+h := by
    fin_cases k <;> simp only [rightGate, List.mem_cons, List.not_mem_nil, or_false] <;>
      intro w hw <;> rcases hw with rfl | rfl
    all_goals have := a.isLt; have := b.isLt; have := c.isLt; have := d.isLt; omega
  have h1 := set_model n C g (leftGate n q a b c d k) hC (Or.inl hL) hl hlb
  have h2 := set_model n ⟨C.gates.set g (leftGate n q a b c d k), C.output⟩ h
    (rightGate n s a b c d k) h1 (Or.inl hR) hr hrb
  apply set_model n _ t ⟨GateOp.or,[n+g,n+h]⟩ h2 (Or.inr rfl) rfl
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl <;> omega

set_option maxHeartbeats 1600000 in
lemma repair_values (n : ℕ) (C : Circuit) (g h t q s : ℕ)
    (a b c d : Fin n) (k : Fin 5) (hgh : g < h) (hht : h < t)
    (ht : t < C.gates.length) (hqg : q < g) (hsh : s < h) (hsg : s ≠ g)
    (hQ : C.gates[q] = ⟨GateOp.or, [b.val,d.val]⟩)
    (hS : C.gates[s] = ⟨GateOp.or, [b.val,c.val]⟩) :
    let D := repairCircuit n C g h t q s a b c d k
    (∀ x : Fin n → Bool, gateVal n D g x = repairLeft k (x a) (x b) (x c) (x d)) ∧
    (∀ x : Fin n → Bool, gateVal n D h x = repairRight k (x a) (x b) (x c) (x d)) := by
  let D := repairCircuit n C g h t q s a b c d k
  have hlen : D.gates.length = C.gates.length := by simp [D, repairCircuit]
  have hgD : g < D.gates.length := by omega
  have hhD : h < D.gates.length := by omega
  have hqD : q < D.gates.length := by omega
  have hsD : s < D.gates.length := by omega
  have hDg : D.gates[g] = leftGate n q a b c d k := by
    simp [D, repairCircuit, show t ≠ g by omega, show h ≠ g by omega]
  have hDh : D.gates[h] = rightGate n s a b c d k := by
    simp [D, repairCircuit, show t ≠ h by omega]
  have hDq : D.gates[q] = ⟨GateOp.or, [b.val,d.val]⟩ := by
    simp [D, repairCircuit, show t ≠ q by omega, show h ≠ q by omega,
      show g ≠ q by omega, hQ]
  have hDs : D.gates[s] = ⟨GateOp.or, [b.val,c.val]⟩ := by
    simp [D, repairCircuit, show t ≠ s by omega, show h ≠ s by omega,
      Ne.symm hsg, hS]
  have hinput : ∀ (x : Fin n → Bool) (gs : List Gate) (i : Fin n),
      (wf gs (List.ofFn x)).getD i.val false = x i := by
    intro x gs i
    rw [wf_keep _ _ _ (by simp)]
    simp [List.getD_eq_getElem?_getD, i.isLt]
  have evalQ : ∀ x : Fin n → Bool, gateVal n D q x = (x b || x d) := by
    intro x
    rw [gate_val_eq n q D hqD, hDq]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons,
      List.any_nil, id_eq, Bool.or_false, hinput]
  have evalS : ∀ x : Fin n → Bool, gateVal n D s x = (x b || x c) := by
    intro x
    rw [gate_val_eq n s D hsD, hDs]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons,
      List.any_nil, id_eq, Bool.or_false, hinput]
  constructor
  · intro x
    have pq : (wf (D.gates.take g) (List.ofFn x)).getD (n+q) false = (x b || x d) := by
      rw [← wire_take D.gates (List.ofFn x) g (n+q) (by simp; omega) hgD.le]
      exact evalQ x
    rw [gate_val_eq n g D hgD, hDg]
    fin_cases k <;> simp only [leftGate, repairLeft, GateOp.eval, List.map_cons,
      List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true, hinput, pq]
  · intro x
    have ps : (wf (D.gates.take h) (List.ofFn x)).getD (n+s) false = (x b || x c) := by
      rw [← wire_take D.gates (List.ofFn x) h (n+s) (by simp; omega) hhD.le]
      exact evalS x
    rw [gate_val_eq n h D hhD, hDh]
    fin_cases k <;> simp only [rightGate, repairRight, GateOp.eval, List.map_cons,
      List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true, hinput, ps]

set_option maxHeartbeats 1600000 in
lemma two_rectangle_component (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (htriangle : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hfour : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d)
    (C : Circuit) (hmC : Monotone2 C) (hC : circuitFun n C = graphFun G ∅)
    (g h t q s : ℕ) (a b c d : Fin n)
    (hgh : g < h) (hht : h < t) (ht : t < C.gates.length)
    (hqg : q < g) (hsh : s < h) (hsg : s ≠ g)
    (hQ : C.gates[q] = ⟨GateOp.or, [b.val,d.val]⟩)
    (hS : C.gates[s] = ⟨GateOp.or, [b.val,c.val]⟩)
    (hCt : C.gates[t] = ⟨GateOp.and, [n+g,n+h]⟩)
    (hgfun : ∀ x : Fin n → Bool, gateVal n C g x = ((x a || x c) && (x b || x d)))
    (hhfun : ∀ x : Fin n → Bool, gateVal n C h x = ((x a || x d) && (x b || x c)))
    (hab : G.Adj a b) (hcd : G.Adj c d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hreach : ∀ (k : Fin 5) (x : Fin n → Bool),
      gateVal n (repairCircuit n C g h t q s a b c d k) t x = true →
      circuitFun n (repairCircuit n C g h t q s a b c d k) x = true) :
    ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧ D.size = C.size ∧
      (∀ x : Fin n → Bool, gateVal n D g x = true → graphFun G ∅ x = true) ∧
      (∀ x : Fin n → Bool, gateVal n D h x = true → graphFun G ∅ x = true) := by
  classical
  obtain ⟨k, hcleanL, hcleanR, hcover⟩ := repair_choice n G htriangle hfour a b c d
    hab hcd hac had hbc hbd
  let D := repairCircuit n C g h t q s a b c d k
  have hlen : D.gates.length = C.gates.length := by simp [D, repairCircuit]
  have htD : t < D.gates.length := by omega
  have hDm : Monotone2 D := by
    intro z hz
    rcases List.mem_or_eq_of_mem_set hz with hz | rfl
    · rcases List.mem_or_eq_of_mem_set hz with hz | rfl
      · rcases List.mem_or_eq_of_mem_set hz with hz | rfl
        · exact hmC z hz
        · fin_cases k <;> simp [leftGate]
      · fin_cases k <;> simp [rightGate]
    · simp
  obtain ⟨evalg, evalh⟩ := repair_values n C g h t q s a b c d k hgh hht ht hqg hsh hsg hQ hS
  have hcleang : ∀ x : Fin n → Bool, gateVal n D g x = true → graphFun G ∅ x = true := by
    intro x hx
    exact hcleanL x ((evalg x).symm.trans hx)
  have hcleanh : ∀ x : Fin n → Bool, gateVal n D h x = true → graphFun G ∅ x = true := by
    intro x hx
    exact hcleanR x ((evalh x).symm.trans hx)
  refine ⟨D, hDm, ?_, by simp [D, repairCircuit, Circuit.size], hcleang, hcleanh⟩
  apply external_reader_repair n G C D hmC hDm hC hlen rfl g h t (by omega) hht ht hCt
  · simp [D, repairCircuit]
  · intro i hi hig hih hit
    simp [D, repairCircuit, Ne.symm hig, Ne.symm hih, Ne.symm hit]
  · exact hcleang
  · exact hcleanh
  · intro u v huv hvold
    rw [evalg, evalh]
    rw [hgfun, hhfun] at hvold
    have hc := hcover u v huv (by simpa only [Bool.or_eq_true] using hvold)
    simpa only [Bool.or_eq_true] using hc
  · exact hreach k

end PEqualNP.Outside.L_meta_2448_aux.RectangleRepair
