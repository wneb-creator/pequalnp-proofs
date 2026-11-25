import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

namespace PEqualNP.Outside.L_meta_1772.SingleEdge

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_ext (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    obtain ⟨t, ht, hl⟩ := ih (w ++ [v])
    refine ⟨v :: t, ?_, by simp [hl]⟩
    have hstep : wiresFrom (g :: gs) w = wiresFrom gs (w ++ [v]) := rfl
    rw [hstep, ht]
    simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_ext gs w
  rw [ht, List.length_append, hl]

lemma getD_wiresFrom_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_ext gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma getD_wiresFrom_take (gs : List Gate) (w : List Bool) (k i : ℕ) (hk : k ≤ gs.length) :
    (wiresFrom (gs.take k) w).getD i false =
      if i < w.length + k then (wiresFrom gs w).getD i false else false := by
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left hk]
  split_ifs with hi
  · have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
    conv_rhs => rw [hsplit, wiresFrom_append]
    exact (getD_wiresFrom_lt (gs.drop k) (wiresFrom (gs.take k) w) i (by omega)).symm
  · rw [List.getD_eq_default]
    omega

lemma getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp

lemma getD_wiresFrom_gate (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length) :
    (wiresFrom gs w).getD (w.length + k) false =
      (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
        if i < w.length + k then (wiresFrom gs w).getD i false else false) := by
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    have h1 := (List.take_append_drop k gs).symm
    rw [List.drop_eq_getElem_cons hk] at h1
    exact h1
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left (Nat.le_of_lt hk)]
  have heq : wiresFrom gs w =
      wiresFrom (gs.drop (k + 1))
        (wiresFrom (gs.take k) w ++
          [(gs[k]).op.eval ((gs[k]).inputs.map fun i => (wiresFrom (gs.take k) w).getD i false)]) := by
    conv_lhs => rw [hsplit, wiresFrom_append]
    rfl
  rw [heq, getD_wiresFrom_lt]
  · conv_lhs => rw [← hlen, getD_snoc_eq]
    congr 1
    apply List.map_congr_left
    intro i _
    rw [getD_wiresFrom_take gs w k i (Nat.le_of_lt hk), heq]
  · rw [List.length_append, hlen]; simp


lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]
def wv {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (wiresFrom gs (List.ofFn x)).getD w false

lemma wv_in {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (w : ℕ) (h : w < n) :
    wv gs x w = x ⟨w, h⟩ := by
  unfold wv
  rw [getD_wiresFrom_lt _ _ _ (by simpa using h)]
  simp [List.getD_eq_getElem?_getD, h]

lemma wv_out {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (w : ℕ) (h : n + gs.length ≤ w) :
    wv gs x w = false := by
  unfold wv
  rw [List.getD_eq_default]
  rw [length_wiresFrom]
  simpa using h

lemma wv_gate {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (k : ℕ) (g : Gate)
    (hg : gs[k]? = some g) (hrb : ∀ i ∈ g.inputs, i < n + k) :
    wv gs x (n + k) = g.op.eval (g.inputs.map (wv gs x)) := by
  obtain ⟨hk, rfl⟩ := List.getElem?_eq_some_iff.1 hg
  have h := getD_wiresFrom_gate gs (List.ofFn x) k hk
  simp only [List.length_ofFn] at h
  unfold wv
  rw [h]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [ite_eq_left (hrb i hi)]

def AO (n : ℕ) (gs : List Gate) : Prop :=
  ∀ k g, gs[k]? = some g → (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
    ∃ a b, g.inputs = [a, b] ∧ a < n + k ∧ b < n + k

lemma ao_of (n : ℕ) (C : Circuit) (h : IsAO2 n C) : AO n C.gates := by
  obtain ⟨h1, h2, h3⟩ := h
  intro k g hg
  obtain ⟨hk, rfl⟩ := List.getElem?_eq_some_iff.1 hg
  have hmem : C.gates[k] ∈ C.gates := List.getElem_mem hk
  refine ⟨h1 _ hmem, ?_⟩
  obtain ⟨a, b, hab⟩ := List.length_eq_two.1 (h3 _ hmem)
  have hr := h2 k hk
  rw [gateAt_eq C k hk, hab] at hr
  exact ⟨a, b, hab, hr a (by simp), hr b (by simp)⟩

lemma ao_to (n : ℕ) (gs : List Gate) (o : ℕ) (h : AO n gs) : IsAO2 n ⟨gs, o⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hg
    exact (h k g hk).1
  · intro j hj i hi
    have hj' : j < gs.length := hj
    rw [gateAt_eq ⟨gs, o⟩ j hj] at hi
    obtain ⟨_, a, b, hab, ha, hb⟩ := h j gs[j] (List.getElem?_eq_getElem hj')
    change i ∈ (gs[j]).inputs at hi
    rw [hab] at hi
    simp at hi
    rcases hi with rfl | rfl
    · exact ha
    · exact hb
  · intro g hg
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hg
    obtain ⟨_, a, b, hab, _, _⟩ := h k g hk
    simp [hab]

lemma wv_and {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (k a b : ℕ)
    (hg : gs[k]? = some ⟨GateOp.and, [a, b]⟩) (ha : a < n + k) (hb : b < n + k) :
    wv gs x (n + k) = (wv gs x a && wv gs x b) := by
  rw [wv_gate gs x k _ hg (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption)]
  simp [GateOp.eval]

lemma wv_or {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (k a b : ℕ)
    (hg : gs[k]? = some ⟨GateOp.or, [a, b]⟩) (ha : a < n + k) (hb : b < n + k) :
    wv gs x (n + k) = (wv gs x a || wv gs x b) := by
  rw [wv_gate gs x k _ hg (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption)]
  simp [GateOp.eval]

lemma same_off {n : ℕ} (A B : List Gate) (h : ℕ) (x : Fin n → Bool)
    (hA : AO n A) (hlen : A.length = B.length)
    (hd : ∀ k, k ≠ h → A[k]? = B[k]?) :
    ∀ w, w ≠ n + h →
      (w < n + h ∨ ∀ (k : ℕ) (g : Gate), A[k]? = some g → n + h ∈ g.inputs → wv A x (n + h) = wv B x (n + h)) →
      wv A x w = wv B x w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hne hor
    by_cases hw : w < n
    · rw [wv_in A x w hw, wv_in B x w hw]
    · by_cases hw2 : w < n + A.length
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < A.length := by omega
        have hkh : k ≠ h := by omega
        have hgA : A[k]? = some A[k] := List.getElem?_eq_getElem hk
        have hgB : B[k]? = some A[k] := by rw [← hd k hkh]; exact hgA
        obtain ⟨_, a, b, hab, ha, hb⟩ := hA k _ hgA
        have hrb : ∀ i ∈ (A[k]).inputs, i < n + k := by
          intro i hi; rw [hab] at hi; simp at hi; rcases hi with rfl | rfl <;> assumption
        rw [wv_gate A x k _ hgA hrb, wv_gate B x k _ hgB hrb]
        congr 1
        apply List.map_congr_left
        intro i hi
        by_cases hih : i = n + h
        · rcases hor with hlt | hall
          · have := hrb i hi; omega
          · rw [hih]; exact hall k _ hgA (hih ▸ hi)
        · apply ih i (hrb i hi) hih
          rcases hor with hlt | hall
          · left; have := hrb i hi; omega
          · right; exact hall
      · rw [wv_out A x w (by omega), wv_out B x w (by omega)]

lemma all_mono (l : List ℕ) (p q : ℕ → Bool) (h : ∀ i ∈ l, p i = true → q i = true) :
    (l.map p).all id = true → (l.map q).all id = true := by
  simp only [List.all_map, List.all_eq_true, Function.comp, id]
  intro hp i hi
  exact h i hi (hp i hi)

lemma any_mono (l : List ℕ) (p q : ℕ → Bool) (h : ∀ i ∈ l, p i = true → q i = true) :
    (l.map p).any id = true → (l.map q).any id = true := by
  simp only [List.any_map, List.any_eq_true, Function.comp, id]
  rintro ⟨i, hi, hp⟩
  exact ⟨i, hi, h i hi hp⟩

lemma mono_off {n : ℕ} (A B : List Gate) (h : ℕ) (x : Fin n → Bool)
    (hA : AO n A) (hlen : A.length = B.length)
    (hd : ∀ k, k ≠ h → A[k]? = B[k]?)
    (hh : wv A x (n + h) = true → wv B x (n + h) = true) :
    ∀ w, wv A x w = true → wv B x w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hw : w < n
    · rw [wv_in A x w hw, wv_in B x w hw]; exact id
    · by_cases hw2 : w < n + A.length
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        by_cases hkh : k = h
        · rw [hkh]; exact hh
        · have hk : k < A.length := by omega
          have hgA : A[k]? = some A[k] := List.getElem?_eq_getElem hk
          have hgB : B[k]? = some A[k] := by rw [← hd k hkh]; exact hgA
          obtain ⟨hop, a, b, hab, ha, hb⟩ := hA k _ hgA
          have hrb : ∀ i ∈ (A[k]).inputs, i < n + k := by
            intro i hi; rw [hab] at hi; simp at hi; rcases hi with rfl | rfl <;> assumption
          rw [wv_gate A x k _ hgA hrb, wv_gate B x k _ hgB hrb]
          rcases hop with hop | hop <;> rw [hop]
          · exact all_mono _ _ _ (fun i hi => ih i (hrb i hi))
          · exact any_mono _ _ _ (fun i hi => ih i (hrb i hi))
      · rw [wv_out A x w (by omega)]; intro hc; cases hc


lemma wv_mono {n : ℕ} (A : List Gate) (hA : AO n A) (x y : Fin n → Bool)
    (hxy : ∀ i, x i = true → y i = true) :
    ∀ w, wv A x w = true → wv A y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hw : w < n
    · rw [wv_in A x w hw, wv_in A y w hw]
      exact hxy _
    · by_cases hw2 : w < n + A.length
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < A.length := by omega
        have hg : A[k]? = some A[k] := List.getElem?_eq_getElem hk
        obtain ⟨hop, a, b, hab, ha, hb⟩ := hA k _ hg
        have hrb : ∀ i ∈ (A[k]).inputs, i < n + k := by
          intro i hi
          rw [hab] at hi
          simp at hi
          rcases hi with rfl | rfl <;> assumption
        rw [wv_gate A x k _ hg hrb, wv_gate A y k _ hg hrb]
        rcases hop with hop | hop <;> rw [hop]
        · exact all_mono _ _ _ (fun i hi => ih i (hrb i hi))
        · exact any_mono _ _ _ (fun i hi => ih i (hrb i hi))
      · rw [wv_out A x w (by omega)]
        intro hc
        cases hc

def edgePatch {n : ℕ} (C : Circuit) (j : ℕ) (u v : Fin n) : Circuit :=
  ⟨C.gates.set j ⟨GateOp.and, [u.val, v.val]⟩, C.output⟩

lemma edgePatch_ao {n : ℕ} (C : Circuit) (j : ℕ) (u v : Fin n)
    (hA : AO n C.gates) : AO n (edgePatch C j u v).gates := by
  intro k g hg
  change (C.gates.set j ⟨GateOp.and, [u.val, v.val]⟩)[k]? = some g at hg
  by_cases hk : k = j
  · subst hk
    by_cases hlt : k < C.gates.length
    · rw [List.getElem?_set_self hlt] at hg
      cases hg
      exact ⟨Or.inl rfl, u.val, v.val, rfl, by omega, by omega⟩
    · rw [List.getElem?_eq_none (by simpa using hlt)] at hg
      cases hg
  · rw [List.getElem?_set_ne (Ne.symm hk)] at hg
    exact hA k g hg

lemma edgePatch_value {n : ℕ} (C : Circuit) (j : ℕ) (u v : Fin n)
    (hj : j < C.gates.length) (x : Fin n → Bool) :
    wv (edgePatch C j u v).gates x (n + j) = (x u && x v) := by
  change wv (C.gates.set j ⟨GateOp.and, [u.val, v.val]⟩) x (n + j) = (x u && x v)
  rw [wv_and _ x j u.val v.val (List.getElem?_set_self hj) (by omega) (by omega)]
  rw [wv_in _ x u.val u.isLt, wv_in _ x v.val v.isLt]

lemma pair_le_input {n : ℕ} (u v : Fin n) (x : Fin n → Bool)
    (hu : x u = true) (hv : x v = true) :
    ∀ i, pairInput u v i = true → x i = true := by
  intro i hi
  simp only [pairInput, decide_eq_true_eq] at hi
  rcases hi with rfl | rfl <;> assumption

lemma graph_pair_true {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v : Fin n) (huv : G.Adj u v) : graphFun G ∅ (pairInput u v) = true := by
  simp only [graphFun]
  apply Bool.or_eq_true_eq_eq_true_or_eq_true _ _ ▸ Or.inr ?_
  simp only [decide_eq_true_eq]
  exact ⟨u, v, huv, by simp [pairInput], by simp [pairInput]⟩

lemma single_edge_cleanup {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (j : ℕ) (u v : Fin n) (hao : IsAO2 n C)
    (hj : j < C.gates.length) (huv : G.Adj u v)
    (hcorrect : circuitFun n C = graphFun G ∅)
    (hpairs : ∀ s t : Fin n, G.Adj s t →
      gateVal n C j (pairInput s t) = (pairInput s t u && pairInput s t v)) :
    IsAO2 n (edgePatch C j u v) ∧
      (edgePatch C j u v).size = C.size ∧
      circuitFun n (edgePatch C j u v) = graphFun G ∅ ∧
      BelowF G (edgePatch C j u v) j ∧
      ∀ k (x : Fin n → Bool), gateVal n (edgePatch C j u v) k x = true →
        gateVal n C k x = true := by
  let D := edgePatch C j u v
  have hA := ao_of n C hao
  have hB : AO n D.gates := edgePatch_ao C j u v hA
  have hlen : C.gates.length = D.gates.length := by simp [D, edgePatch]
  have hd : ∀ k, k ≠ j → C.gates[k]? = D.gates[k]? := by
    intro k hk
    simp only [D, edgePatch, List.getElem?_set_ne (Ne.symm hk)]
  have huvGate : wv C.gates (pairInput u v) (n + j) = true := by
    have h := hpairs u v huv
    simpa [gateVal, Circuit.wires, wv, wiresFrom, pairInput] using h
  have hgLower (x : Fin n → Bool) : wv D.gates x (n + j) = true →
      wv C.gates x (n + j) = true := by
    rw [edgePatch_value C j u v hj x]
    rw [Bool.and_eq_true_eq_eq_true_and_eq_true]
    rintro ⟨hxu, hxv⟩
    exact wv_mono C.gates hA (pairInput u v) x (pair_le_input u v x hxu hxv)
      (n + j) huvGate
  have allLower (x : Fin n → Bool) (w : ℕ) :
      wv D.gates x w = true → wv C.gates x w = true :=
    mono_off D.gates C.gates j x hB hlen.symm (fun k hk => (hd k hk).symm) (hgLower x) w
  have edgeEqual (s t : Fin n) (hst : G.Adj s t) (w : ℕ) :
      wv D.gates (pairInput s t) w = wv C.gates (pairInput s t) w := by
    have heq : wv C.gates (pairInput s t) (n + j) =
        wv D.gates (pairInput s t) (n + j) := by
      rw [edgePatch_value C j u v hj]
      exact hpairs s t hst
    by_cases hw : w = n + j
    · subst hw
      exact heq.symm
    · exact (same_off C.gates D.gates j (pairInput s t) hA hlen hd w hw
        (Or.inr (fun _ _ _ _ => heq))).symm
  have upper (x : Fin n → Bool) : circuitFun n D x = true → graphFun G ∅ x = true := by
    intro hx
    have old := allLower x C.output hx
    change circuitFun n C x = true at old
    simpa only [hcorrect] using old
  have lower (x : Fin n → Bool) : graphFun G ∅ x = true → circuitFun n D x = true := by
    intro hx
    simp [graphFun] at hx
    obtain ⟨s, t, hst, hxs, hxt⟩ := hx
    have old : wv C.gates (pairInput s t) C.output = true := by
      change circuitFun n C (pairInput s t) = true
      rw [hcorrect]
      exact graph_pair_true G s t hst
    have fresh : wv D.gates (pairInput s t) D.output = true := by
      change wv D.gates (pairInput s t) C.output = true
      rw [edgeEqual s t hst]
      exact old
    exact wv_mono D.gates hB (pairInput s t) x (pair_le_input s t x hxs hxt) D.output fresh
  refine ⟨ao_to n D.gates D.output hB, by simp [edgePatch, Circuit.size], ?_, ?_, ?_⟩
  · funext x
    cases hdx : circuitFun n D x <;> cases hfx : graphFun G ∅ x <;> simp_all
  · intro x hx
    change wv D.gates x (n + j) = true at hx
    rw [edgePatch_value C j u v hj x, Bool.and_eq_true_eq_eq_true_and_eq_true] at hx
    simp only [graphFun]
    apply Bool.or_eq_true_eq_eq_true_or_eq_true _ _ ▸ Or.inr ?_
    simp only [decide_eq_true_eq]
    exact ⟨u, v, huv, hx.1, hx.2⟩
  · intro k x hx
    exact allLower x (n + k) hx

end PEqualNP.Outside.L_meta_1772.SingleEdge
