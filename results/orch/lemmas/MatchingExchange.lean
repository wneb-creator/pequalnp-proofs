import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2448_aux.MatchingExchange

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

open PEqualNP.EdgeOwnership

lemma matching_identity (a b c d : Bool) :
    (((a || c) && (b || d)) && ((a || d) && (b || c))) =
      ((a && b) || (c && d)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

set_option maxHeartbeats 800000 in
lemma closed_pair_exchange (n : ℕ) (C D : Circuit) (g h t : ℕ)
    (a b c d : Fin n) (hlen : D.gates.length = C.gates.length)
    (hgt : g < t) (hht : h < t) (_hgh : g ≠ h) (ht : t < C.gates.length)
    (hDg : D.gates[g] = ⟨GateOp.and, [a.val,b.val]⟩)
    (hDh : D.gates[h] = ⟨GateOp.and, [c.val,d.val]⟩)
    (hDt : D.gates[t] = ⟨GateOp.or, [n+g,n+h]⟩)
    (hCt : C.gates[t] = ⟨GateOp.and, [n+g,n+h]⟩)
    (hkeep : ∀ k (hk : k < C.gates.length), k ≠ g → k ≠ h → k ≠ t →
      D.gates[k] = C.gates[k])
    (hread : ∀ k (hk : k < C.gates.length), k ≠ t →
      n + g ∉ C.gates[k].inputs ∧ n + h ∉ C.gates[k].inputs)
    (hout : D.output = C.output) (hog : C.output ≠ n+g) (hoh : C.output ≠ n+h)
    (hpair : ∀ x : Fin n → Bool,
      (gateVal n C g x && gateVal n C h x) = ((x a && x b) || (x c && x d))) :
    circuitFun n D = circuitFun n C := by
  funext x
  have hgC : g < C.gates.length := by omega
  have hhC : h < C.gates.length := by omega
  have hgD : g < D.gates.length := by omega
  have hhD : h < D.gates.length := by omega
  have htD : t < D.gates.length := by omega
  have hinput : ∀ (gs : List Gate) (i : Fin n),
      (wf gs (List.ofFn x)).getD i.val false = x i := by
    intro gs i
    rw [wf_keep _ _ _ (by simp)]
    simp [List.getD_eq_getElem?_getD, i.isLt]
  have hall : ∀ k, k ≤ C.gates.length →
      (∀ w, w ≠ n+g → w ≠ n+h →
        (wf (D.gates.take k) (List.ofFn x)).getD w false =
        (wf (C.gates.take k) (List.ofFn x)).getD w false) ∧
      (g < k → (wf (D.gates.take k) (List.ofFn x)).getD (n+g) false = (x a && x b)) ∧
      (h < k → (wf (D.gates.take k) (List.ofFn x)).getD (n+h) false = (x c && x d)) := by
    intro k
    induction k with
    | zero => intro hk; exact ⟨fun _ _ _ => rfl, by omega, by omega⟩
    | succ k ih =>
      intro hk
      have hkC : k < C.gates.length := by omega
      have hkD : k < D.gates.length := by omega
      obtain ⟨ihw, ihg, ihh⟩ := ih (by omega)
      have hlC : (wf (C.gates.take k) (List.ofFn x)).length = n+k := by
        simp [wf_len, List.length_take, Nat.min_eq_left hkC.le]
      have hlD : (wf (D.gates.take k) (List.ofFn x)).length = n+k := by
        simp [wf_len, List.length_take, Nat.min_eq_left hkD.le]
      have hval : k ≠ g → k ≠ h →
          D.gates[k].op.eval (D.gates[k].inputs.map fun i =>
            (wf (D.gates.take k) (List.ofFn x)).getD i false) =
          C.gates[k].op.eval (C.gates[k].inputs.map fun i =>
            (wf (C.gates.take k) (List.ofFn x)).getD i false) := by
        intro hkg hkh
        by_cases hkt : k = t
        · subst k
          rw [hDt, hCt]
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons,
            List.any_nil, List.all_cons, List.all_nil, id_eq, Bool.or_false, Bool.and_true]
          rw [ihg hgt, ihh hht]
          have eg := wire_take C.gates (List.ofFn x) t (n+g)
            (by simp; omega) (by omega)
          have eh := wire_take C.gates (List.ofFn x) t (n+h)
            (by simp; omega) (by omega)
          rw [← eg, ← eh]
          exact (hpair x).symm
        · rw [hkeep k hkC hkg hkh hkt]
          congr 1
          apply List.map_congr_left
          intro i hi
          exact ihw i (fun e => (hread k hkC hkt).1 (e ▸ hi))
            (fun e => (hread k hkC hkt).2 (e ▸ hi))
      rw [List.take_succ_eq_append_getElem hkD, List.take_succ_eq_append_getElem hkC,
        wf_snoc, wf_snoc]
      refine ⟨?_, ?_, ?_⟩
      · intro w hwg hwh
        rcases Nat.lt_trichotomy w (n+k) with hw | hw | hw
        · rw [getD_snoc_lt _ _ _ (by omega), getD_snoc_lt _ _ _ (by omega)]
          exact ihw w hwg hwh
        · rw [hw, ← hlD, getD_snoc_eq, hlD, ← hlC, getD_snoc_eq]
          exact hval (by omega) (by omega)
        · rw [getD_snoc_gt _ _ _ (by omega), getD_snoc_gt _ _ _ (by omega)]
      · intro hgk
        by_cases hg : g < k
        · rw [getD_snoc_lt _ _ _ (by omega)]
          exact ihg hg
        · have hg : g = k := by omega
          subst k
          rw [← hlD, getD_snoc_eq, hDg]
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
            List.all_nil, id_eq, Bool.and_true, hinput]
      · intro hhk
        by_cases hh : h < k
        · rw [getD_snoc_lt _ _ _ (by omega)]
          exact ihh hh
        · have hh : h = k := by omega
          subst k
          rw [← hlD, getD_snoc_eq, hDh]
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
            List.all_nil, id_eq, Bool.and_true, hinput]
  have he := (hall C.gates.length (by rfl)).1 C.output hog hoh
  rw [← hlen, List.take_length, hlen, List.take_length] at he
  change (wf D.gates (List.ofFn x)).getD D.output false = _
  rw [hout]
  exact he

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

set_option maxHeartbeats 800000 in
lemma repair_two_rectangles (n : ℕ) (C : Circuit) (hm : Monotone2 C)
    (g h t : ℕ) (a b c d : Fin n)
    (hgt : g < t) (hht : h < t) (hgh : g ≠ h) (ht : t < C.gates.length)
    (hCt : C.gates[t] = ⟨GateOp.and, [n+g,n+h]⟩)
    (hread : ∀ k (hk : k < C.gates.length), k ≠ t →
      n + g ∉ C.gates[k].inputs ∧ n + h ∉ C.gates[k].inputs)
    (hog : C.output ≠ n+g) (hoh : C.output ≠ n+h)
    (hgfun : ∀ x : Fin n → Bool,
      gateVal n C g x = ((x a || x c) && (x b || x d)))
    (hhfun : ∀ x : Fin n → Bool,
      gateVal n C h x = ((x a || x d) && (x b || x c))) :
    let D : Circuit := ⟨((C.gates.set g ⟨GateOp.and, [a.val,b.val]⟩).set h
      ⟨GateOp.and, [c.val,d.val]⟩).set t ⟨GateOp.or, [n+g,n+h]⟩, C.output⟩
    Monotone2 D ∧ circuitFun n D = circuitFun n C ∧ D.size = C.size ∧
      (∀ u v : Fin n, gateVal n D g (pairInput u v) = true → u = a ∨ v = a) ∧
      (∀ u v : Fin n, gateVal n D h (pairInput u v) = true → u = c ∨ v = c) := by
  classical
  dsimp only
  let D : Circuit := ⟨((C.gates.set g ⟨GateOp.and, [a.val,b.val]⟩).set h
    ⟨GateOp.and, [c.val,d.val]⟩).set t ⟨GateOp.or, [n+g,n+h]⟩, C.output⟩
  have hgC : g < C.gates.length := by omega
  have hhC : h < C.gates.length := by omega
  have hlen : D.gates.length = C.gates.length := by simp [D]
  have hgD : g < D.gates.length := by omega
  have hhD : h < D.gates.length := by omega
  have htD : t < D.gates.length := by omega
  have hDg : D.gates[g] = ⟨GateOp.and, [a.val,b.val]⟩ := by
    simp [D, List.getElem_set, Ne.symm hgh, show t ≠ g by omega]
  have hDh : D.gates[h] = ⟨GateOp.and, [c.val,d.val]⟩ := by
    simp [D, List.getElem_set, show t ≠ h by omega]
  have hDt : D.gates[t] = ⟨GateOp.or, [n+g,n+h]⟩ := by simp [D]
  have hDm : Monotone2 D := by
    intro k hk
    rcases List.mem_or_eq_of_mem_set hk with hk | rfl
    · rcases List.mem_or_eq_of_mem_set hk with hk | rfl
      · rcases List.mem_or_eq_of_mem_set hk with hk | rfl
        · exact hm k hk
        · simp
      · simp
    · simp
  have hfun : circuitFun n D = circuitFun n C := by
    apply closed_pair_exchange n C D g h t a b c d hlen hgt hht hgh ht hDg hDh hDt hCt
    · intro k hk hkg hkh hkt
      simp [D, List.getElem_set, Ne.symm hkg, Ne.symm hkh, Ne.symm hkt]
    · exact hread
    · rfl
    · exact hog
    · exact hoh
    · intro x
      rw [hgfun, hhfun]
      exact matching_identity _ _ _ _
  have hinput : ∀ (x : Fin n → Bool) (gs : List Gate) (i : Fin n),
      (wf gs (List.ofFn x)).getD i.val false = x i := by
    intro x gs i
    rw [wf_keep _ _ _ (by simp)]
    simp [List.getD_eq_getElem?_getD, i.isLt]
  refine ⟨hDm, hfun, by simp [Circuit.size], ?_, ?_⟩
  · intro u v h
    rw [gate_val_eq n g D hgD, hDg] at h
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
      List.all_nil, id_eq, Bool.and_true, hinput, Bool.and_eq_true] at h
    have ha : a = u ∨ a = v := of_decide_eq_true h.1
    exact ha.imp Eq.symm Eq.symm
  · intro u v hp
    rw [gate_val_eq n h D hhD, hDh] at hp
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
      List.all_nil, id_eq, Bool.and_true, hinput, Bool.and_eq_true] at hp
    have hc : c = u ∨ c = v := of_decide_eq_true hp.1
    exact hc.imp Eq.symm Eq.symm

end PEqualNP.Outside.L_meta_2448_aux.MatchingExchange
