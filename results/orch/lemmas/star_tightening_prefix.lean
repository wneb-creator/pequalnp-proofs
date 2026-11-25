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
lemma coneFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma coneStep_getD_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
    (coneStep n cs g).getD cs.length [] =
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) []) := by
  simp [coneStep, List.getD_eq_getElem?_getD]

lemma coneStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (coneStep n cs g).getD m [] = cs.getD m [] := by
  simp [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

lemma coneFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (coneStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (coneStep n cs g) (by simp [coneStep]; omega)]
    exact coneStep_getD_lt n cs g k hk

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

lemma edgePatch_gate_at {n : ℕ} (C : Circuit) (j : ℕ) (u v : Fin n)
    (hj : j < C.gates.length) : gateAt (edgePatch C j u v) j = ⟨GateOp.and, [u.val, v.val]⟩ := by
  simp [edgePatch, gateAt, List.getD_eq_getElem?_getD, List.getElem?_set_self hj]

lemma edgePatch_gate_ne {n : ℕ} (C : Circuit) (j : ℕ) (u v : Fin n)
    (k : ℕ) (hk : k ≠ j) : gateAt (edgePatch C j u v) k = gateAt C k := by
  simp only [edgePatch, gateAt, List.getD_eq_getElem?_getD,
    List.getElem?_set_ne (Ne.symm hk)]

lemma edgePatch_op {n : ℕ} (C : Circuit) (j : ℕ) (u v : Fin n)
    (hj : j < C.gates.length) (hand : (gateAt C j).op = GateOp.and) (k : ℕ) :
    (gateAt (edgePatch C j u v) k).op = (gateAt C k).op := by
  by_cases hk : k = j
  · subst k
    rw [edgePatch_gate_at C j u v hj, hand]
  · rw [edgePatch_gate_ne C j u v k hk]

lemma edgePatch_no_cone {n : ℕ} (C : Circuit) (j : ℕ) (u v : Fin n)
    (hj : j < C.gates.length) (i : ℕ) : ¬InCone n (edgePatch C j u v) i j := by
  intro hc
  have hj' : j < (edgePatch C j u v).gates.length := by simpa [edgePatch] using hj
  obtain ⟨w, hw, hn, _, _⟩ := (inCone_iff n (edgePatch C j u v) i j hj').mp hc
  rw [edgePatch_gate_at C j u v hj] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl <;> omega

lemma edgePatch_cone_sub {n : ℕ} (C : Circuit) (j : ℕ) (u v : Fin n)
    (hj : j < C.gates.length) :
    ∀ k < C.gates.length, ∀ i, InCone n (edgePatch C j u v) i k → InCone n C i k := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hk i hc
    by_cases hkj : k = j
    · subst k
      exact (edgePatch_no_cone C j u v hj i hc).elim
    · have hk' : k < (edgePatch C j u v).gates.length := by simpa [edgePatch] using hk
      obtain ⟨w, hw, hn, hwk, hc⟩ :=
        (inCone_iff n (edgePatch C j u v) i k hk').mp hc
      rw [edgePatch_gate_ne C j u v k hkj] at hw
      apply (inCone_iff n C i k hk).mpr
      refine ⟨w, hw, hn, hwk, ?_⟩
      rcases hc with hiw | hc
      · exact Or.inl hiw
      · exact Or.inr (ih (w - n) (by omega) (by omega) i hc)

lemma edgePatch_pair_gate_eq {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (j : ℕ) (u v : Fin n) (hao : IsAO2 n C) (hj : j < C.gates.length)
    (hpairs : ∀ s t : Fin n, G.Adj s t →
      gateVal n C j (pairInput s t) = (pairInput s t u && pairInput s t v))
    (s t : Fin n) (hst : G.Adj s t) (k : ℕ) :
    gateVal n (edgePatch C j u v) k (pairInput s t) = gateVal n C k (pairInput s t) := by
  let D := edgePatch C j u v
  have hlen : C.gates.length = D.gates.length := by simp [D, edgePatch]
  have hd : ∀ l, l ≠ j → C.gates[l]? = D.gates[l]? := by
    intro l hl
    simp only [D, edgePatch, List.getElem?_set_ne (Ne.symm hl)]
  have heq : wv C.gates (pairInput s t) (n + j) =
      wv D.gates (pairInput s t) (n + j) := by
    rw [edgePatch_value C j u v hj]
    exact hpairs s t hst
  change wv D.gates (pairInput s t) (n + k) = wv C.gates (pairInput s t) (n + k)
  by_cases hkj : k = j
  · subst hkj
    exact heq.symm
  · exact (same_off C.gates D.gates j (pairInput s t) (ao_of n C hao) hlen hd
      (n + k) (by omega) (Or.inr (fun _ _ _ _ => heq))).symm

lemma edgePatch_preserves_owns {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (j : ℕ) (u v : Fin n) (hao : IsAO2 n C) (hj : j < C.gates.length)
    (hand : (gateAt C j).op = GateOp.and)
    (hpairs : ∀ s t : Fin n, G.Adj s t →
      gateVal n C j (pairInput s t) = (pairInput s t u && pairInput s t v))
    (s t : Fin n) (hst : G.Adj s t) (k : ℕ) (hk : Owns n C k s t) :
    Owns n (edgePatch C j u v) k s t := by
  refine ⟨by simpa [edgePatch] using hk.1, ?_, ?_, ?_⟩
  · rw [edgePatch_op C j u v hj hand k]
    exact hk.2.1
  · rw [edgePatch_pair_gate_eq G C j u v hao hj hpairs s t hst k]
    exact hk.2.2.1
  · intro i hi hc ha
    rw [edgePatch_pair_gate_eq G C j u v hao hj hpairs s t hst i]
    apply hk.2.2.2 i hi (edgePatch_cone_sub C j u v hj k hk.1 i hc)
    rw [edgePatch_op C j u v hj hand i] at ha
    exact ha

lemma edgePatch_owns {n : ℕ} (C : Circuit) (j : ℕ) (u v : Fin n)
    (hj : j < C.gates.length) : Owns n (edgePatch C j u v) j u v := by
  refine ⟨by simpa [edgePatch] using hj, ?_, ?_, ?_⟩
  · rw [edgePatch_gate_at C j u v hj]
  · change wv (edgePatch C j u v).gates (pairInput u v) (n + j) = true
    rw [edgePatch_value C j u v hj]
    simp [pairInput]
  · intro i hi hc ha
    exact (edgePatch_no_cone C j u v hj i hc).elim

def badGateSet {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) : Set ℕ :=
  {k | k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧
    ∀ s t, G.Adj s t → ¬Owns n C k s t}

lemma edgePatch_bad_count_lt {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (j : ℕ) (u v : Fin n) (hao : IsAO2 n C) (hj : j < C.gates.length)
    (hand : (gateAt C j).op = GateOp.and) (huv : G.Adj u v)
    (hbad : ∀ s t, G.Adj s t → ¬Owns n C j s t)
    (hpairs : ∀ s t : Fin n, G.Adj s t →
      gateVal n C j (pairInput s t) = (pairInput s t u && pairInput s t v)) :
    (badGateSet G (edgePatch C j u v)).ncard < (badGateSet G C).ncard := by
  have hsub : badGateSet G (edgePatch C j u v) ⊆ badGateSet G C := by
    intro k hk
    obtain ⟨hkb, hka, hkn⟩ := hk
    refine ⟨by simpa [edgePatch] using hkb, ?_, ?_⟩
    · rw [←edgePatch_op C j u v hj hand k]
      exact hka
    · intro s t hst hown
      exact hkn s t hst (edgePatch_preserves_owns G C j u v hao hj hand hpairs s t hst k hown)
  have hstrict : badGateSet G (edgePatch C j u v) ⊂ badGateSet G C := by
    apply Set.ssubset_iff_subset_ne.mpr
    refine ⟨hsub, ?_⟩
    intro heq
    have hcj : j ∈ badGateSet G C := ⟨hj, hand, hbad⟩
    have hdj : j ∈ badGateSet G (edgePatch C j u v) := heq.symm ▸ hcj
    exact hdj.2.2 u v huv (edgePatch_owns C j u v hj)
  refine Set.ncard_lt_ncard hstrict ?_
  apply (Finset.finite_toSet (Finset.range C.gates.length)).subset
  intro k hk
  exact Finset.mem_range.mpr hk.1

lemma single_edge_bad_repair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (j : ℕ) (u v : Fin n) (hao : IsAO2 n C) (hj : j < C.gates.length)
    (hand : (gateAt C j).op = GateOp.and) (huv : G.Adj u v)
    (hcorrect : circuitFun n C = graphFun G ∅)
    (hbad : ∀ s t, G.Adj s t → ¬Owns n C j s t)
    (hpairs : ∀ s t : Fin n, G.Adj s t →
      gateVal n C j (pairInput s t) = (pairInput s t u && pairInput s t v)) :
    ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧
      D.size ≤ C.size ∧ (badGateSet G D).ncard < (badGateSet G C).ncard := by
  obtain ⟨hAO, hsize, heq, _, _⟩ := single_edge_cleanup G C j u v hao hj huv hcorrect hpairs
  refine ⟨edgePatch C j u v, ?_, heq, hsize.le,
    edgePatch_bad_count_lt G C j u v hao hj hand huv hbad hpairs⟩
  intro g hg
  refine ⟨hAO.1 g hg, ?_⟩
  exact (hAO.2.2 g hg).le

end PEqualNP.Outside.L_meta_1772.SingleEdge

namespace PEqualNP.Outside.L_meta_1772.SingleEdgeTopform

open PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_1772.SingleEdge

lemma mem_junk_iff {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} {j : ℕ} :
    j ∈ junk G C ↔ j < C.gates.length ∧ IsDirtyAnd n G C j := by
  unfold junk gatesWhere
  rw [Finset.mem_filter, Finset.mem_range]

lemma belowF_iff_not_junk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (i : ℕ) (hi : i < C.gates.length)
    (hand : (gateAt C i).op = GateOp.and) : BelowF G C i ↔ i ∉ junk G C := by
  constructor
  · intro hs hj
    obtain ⟨_, _, _, x, hx, hf⟩ := mem_junk_iff.mp hj
    have := hs x hx
    simp_all
  · intro hj x hx
    cases hf : graphFun G ∅ x
    · exact False.elim (hj (mem_junk_iff.mpr ⟨hi, hand, hi, x, hx, hf⟩))
    · rfl

lemma edgePatch_junk_subset {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (j : ℕ) (u v : Fin n) (hj : j < C.gates.length)
    (hand : (gateAt C j).op = GateOp.and)
    (hdown : ∀ i (x : Fin n → Bool), gateVal n (edgePatch C j u v) i x = true →
      gateVal n C i x = true) : junk G (edgePatch C j u v) ⊆ junk G C := by
  intro i hi
  obtain ⟨hib, hia, _, x, hx, hf⟩ := mem_junk_iff.mp hi
  have hib' : i < C.gates.length := by simpa [edgePatch] using hib
  refine mem_junk_iff.mpr ⟨hib', ?_, hib', x, hdown i x hx, hf⟩
  rwa [edgePatch_op C j u v hj hand i] at hia

lemma edgePatch_preserves_topform {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (j : ℕ) (u v : Fin n)
    (hj : j < C.gates.length) (hand : (gateAt C j).op = GateOp.and)
    (hTop : TopForm G C) (hJ : junk G (edgePatch C j u v) = junk G C) :
    TopForm G (edgePatch C j u v) := by
  intro i hi k hk hiAnd hiSafe hkAnd hcone
  have hi' : i < C.gates.length := by simpa [edgePatch] using hi
  have hk' : k < C.gates.length := by simpa [edgePatch] using hk
  have hiAnd' : (gateAt C i).op = GateOp.and := by
    rwa [edgePatch_op C j u v hj hand i] at hiAnd
  have hkAnd' : (gateAt C k).op = GateOp.and := by
    rwa [edgePatch_op C j u v hj hand k] at hkAnd
  have hiNot : i ∉ junk G (edgePatch C j u v) :=
    (belowF_iff_not_junk G (edgePatch C j u v) i hi hiAnd).mp hiSafe
  rw [hJ] at hiNot
  have hiSafe' := (belowF_iff_not_junk G C i hi' hiAnd').mpr hiNot
  exact hTop i hi' k hk' hiAnd' hiSafe' hkAnd'
    (edgePatch_cone_sub C j u v hj k hk' i hcone)

lemma single_edge_topform_repair {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (j : ℕ) (u v : Fin n)
    (hao : IsAO2 n C) (hj : j < C.gates.length)
    (hand : (gateAt C j).op = GateOp.and) (huv : G.Adj u v)
    (hcorrect : circuitFun n C = graphFun G ∅) (hTop : TopForm G C)
    (hcanonJ : ∀ D : Circuit, Monotone2 D → circuitFun n D = graphFun G ∅ →
      D.size ≤ C.size → (junk G C).card ≤ (junk G D).card)
    (hbad : ∀ s t, G.Adj s t → ¬Owns n C j s t)
    (hpairs : ∀ s t : Fin n, G.Adj s t →
      gateVal n C j (pairInput s t) = (pairInput s t u && pairInput s t v)) :
    ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧
      D.size ≤ C.size ∧ TopForm G D ∧ junk G D = junk G C ∧
      (badGateSet G D).ncard < (badGateSet G C).ncard := by
  obtain ⟨hAO, hsize, heq, _, hdown⟩ :=
    single_edge_cleanup G C j u v hao hj huv hcorrect hpairs
  have hMono : Monotone2 (edgePatch C j u v) := by
    intro g hg
    exact ⟨hAO.1 g hg, (hAO.2.2 g hg).le⟩
  have hsub := edgePatch_junk_subset G C j u v hj hand hdown
  have hJ : junk G (edgePatch C j u v) = junk G C :=
    Finset.eq_of_subset_of_card_le hsub (hcanonJ _ hMono heq hsize.le)
  exact ⟨edgePatch C j u v, hMono, heq, hsize.le,
    edgePatch_preserves_topform G C j u v hj hand hTop hJ, hJ,
    edgePatch_bad_count_lt G C j u v hao hj hand huv hbad hpairs⟩

lemma canonical_excludes_single_edge_bad {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (j : ℕ) (u v : Fin n)
    (hao : IsAO2 n C) (hj : j < C.gates.length)
    (hand : (gateAt C j).op = GateOp.and) (huv : G.Adj u v)
    (hcorrect : circuitFun n C = graphFun G ∅) (hTop : TopForm G C)
    (hcanonJ : ∀ D : Circuit, Monotone2 D → circuitFun n D = graphFun G ∅ →
      D.size ≤ C.size → (junk G C).card ≤ (junk G D).card)
    (hcanonB : ∀ D : Circuit, Monotone2 D → circuitFun n D = graphFun G ∅ →
      D.size ≤ C.size → TopForm G D → (junk G D).card ≤ (junk G C).card →
      (badGateSet G C).ncard ≤ (badGateSet G D).ncard)
    (hbad : ∀ s t, G.Adj s t → ¬Owns n C j s t)
    (hpairs : ∀ s t : Fin n, G.Adj s t →
      gateVal n C j (pairInput s t) = (pairInput s t u && pairInput s t v)) : False := by
  obtain ⟨D, hD, hDF, hsize, hDT, hDJ, hdrop⟩ :=
    single_edge_topform_repair G C j u v hao hj hand huv hcorrect hTop hcanonJ hbad hpairs
  exact (Nat.not_lt_of_ge (hcanonB D hD hDF hsize hDT (by rw [hDJ]))) hdrop

end PEqualNP.Outside.L_meta_1772.SingleEdgeTopform

namespace PEqualNP.Outside.L_meta_1772.SingleEdgeSignature

open PEqualNP.Outside.L_meta_1772.SingleEdge
open PEqualNP.Outside.L_meta_1772.SingleEdgeTopform

lemma pairInput_swap {n : ℕ} (u v : Fin n) : pairInput v u = pairInput u v := by
  funext w
  simp [pairInput, or_comm]

lemma pair_product_iff {n : ℕ} {s t u v : Fin n} (huv : u ≠ v) :
    (pairInput s t u && pairInput s t v) = true ↔
      (s = u ∧ t = v) ∨ (s = v ∧ t = u) := by
  simp only [Bool.and_eq_true_eq_eq_true_and_eq_true, pairInput, decide_eq_true_eq]
  constructor
  · rintro ⟨hu | hu, hv | hv⟩
    · exact False.elim (huv (hu.trans hv.symm))
    · exact Or.inl ⟨hu.symm, hv.symm⟩
    · exact Or.inr ⟨hv.symm, hu.symm⟩
    · exact False.elim (huv (hu.trans hv.symm))
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) <;> simp

lemma signature_or_second_edge {n : ℕ} (G : SimpleGraph (Fin n))
    (C : Circuit) (j : ℕ) (u v : Fin n) (huv : G.Adj u v)
    (htrue : gateVal n C j (pairInput u v) = true) :
    (∀ s t : Fin n, G.Adj s t →
      gateVal n C j (pairInput s t) = (pairInput s t u && pairInput s t v)) ∨
    ∃ s t : Fin n, G.Adj s t ∧ gateVal n C j (pairInput s t) = true ∧
      ¬ ((s = u ∧ t = v) ∨ (s = v ∧ t = u)) := by
  classical
  by_cases hsecond : ∃ s t : Fin n, G.Adj s t ∧
      gateVal n C j (pairInput s t) = true ∧
      ¬ ((s = u ∧ t = v) ∨ (s = v ∧ t = u))
  · exact Or.inr hsecond
  left
  have hne : u ≠ v := fun h => G.irrefl (h ▸ huv)
  intro s t hst
  by_cases hgate : gateVal n C j (pairInput s t) = true
  · have hor : (s = u ∧ t = v) ∨ (s = v ∧ t = u) := by
      by_contra hnot
      exact hsecond ⟨s,t,hst,hgate,hnot⟩
    exact hgate.trans ((pair_product_iff hne).mpr hor).symm
  · cases hp : (pairInput s t u && pairInput s t v)
    · cases hg : gateVal n C j (pairInput s t) <;> simp_all
    · have hor := (pair_product_iff hne).mp hp
      rcases hor with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact False.elim (hgate htrue)
      · rw [pairInput_swap] at hgate
        exact False.elim (hgate htrue)

lemma canonical_bad_has_second_edge {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (j : ℕ) (u v : Fin n)
    (hao : IsAO2 n C) (hj : j < C.gates.length)
    (hand : (gateAt C j).op = GateOp.and) (huv : G.Adj u v)
    (hcorrect : circuitFun n C = graphFun G ∅) (hTop : TopForm G C)
    (hcanonJ : ∀ D : Circuit, Monotone2 D → circuitFun n D = graphFun G ∅ →
      D.size ≤ C.size → (junk G C).card ≤ (junk G D).card)
    (hcanonB : ∀ D : Circuit, Monotone2 D → circuitFun n D = graphFun G ∅ →
      D.size ≤ C.size → TopForm G D → (junk G D).card ≤ (junk G C).card →
      (badGateSet G C).ncard ≤ (badGateSet G D).ncard)
    (hbad : ∀ s t, G.Adj s t → ¬Owns n C j s t)
    (htrue : gateVal n C j (pairInput u v) = true) :
    ∃ s t : Fin n, G.Adj s t ∧ gateVal n C j (pairInput s t) = true ∧
      ¬ ((s = u ∧ t = v) ∨ (s = v ∧ t = u)) := by
  rcases signature_or_second_edge G C j u v huv htrue with hpairs | hsecond
  · exact False.elim (canonical_excludes_single_edge_bad G C j u v hao hj hand huv
      hcorrect hTop hcanonJ hcanonB hbad hpairs)
  · exact hsecond

end PEqualNP.Outside.L_meta_1772.SingleEdgeSignature


namespace PEqualNP.Outside.L_meta_1772_aux.starTighten

open PEqualNP.Outside.L_meta_1772.SingleEdge
open PEqualNP.Outside.L_meta_1772.SingleEdgeTopform

def clamp {n : ℕ} (C : Circuit) (j : ℕ) (a : Fin n) (q : ℕ) : Circuit :=
  ⟨C.gates.set j ⟨GateOp.and, [a.val,q]⟩, C.output⟩

lemma clamp_at {n : ℕ} (C : Circuit) (j : ℕ) (a : Fin n) (q : ℕ)
    (hj : j < C.gates.length) : gateAt (clamp C j a q) j = ⟨GateOp.and,[a.val,q]⟩ := by
  simp [clamp,gateAt,List.getD_eq_getElem?_getD,List.getElem?_set_self hj]

lemma clamp_ne {n : ℕ} (C : Circuit) (j : ℕ) (a : Fin n) (q k : ℕ)
    (hk : k ≠ j) : gateAt (clamp C j a q) k = gateAt C k := by
  simp only [clamp,gateAt,List.getD_eq_getElem?_getD,List.getElem?_set_ne (Ne.symm hk)]

lemma clamp_ao {n : ℕ} (C : Circuit) (j : ℕ) (a : Fin n) (q : ℕ)
    (hA : AO n C.gates) (hq : q < n+j) : AO n (clamp C j a q).gates := by
  intro k g hg
  change (C.gates.set j ⟨GateOp.and,[a.val,q]⟩)[k]? = some g at hg
  by_cases hk : k = j
  · subst k
    by_cases hlt : j < C.gates.length
    · rw [List.getElem?_set_self hlt] at hg
      cases hg
      exact ⟨Or.inl rfl,a.val,q,rfl,by omega,hq⟩
    · rw [List.getElem?_eq_none (by simpa using hlt)] at hg
      cases hg
  · rw [List.getElem?_set_ne (Ne.symm hk)] at hg
    exact hA k g hg

lemma clamp_prefix {n : ℕ} (C : Circuit) (j : ℕ) (a : Fin n) (q : ℕ)
    (hA : AO n C.gates) (x : Fin n → Bool) (w : ℕ) (hw : w < n+j) :
    wv (clamp C j a q).gates x w = wv C.gates x w := by
  exact (same_off C.gates (clamp C j a q).gates j x hA
    (by simp [clamp]) (fun k hk => by simp [clamp,List.getElem?_set_ne (Ne.symm hk)])
    w (by omega) (Or.inl hw)).symm

lemma clamp_value {n : ℕ} (C : Circuit) (j : ℕ) (a : Fin n) (q : ℕ)
    (hA : AO n C.gates) (hj : j < C.gates.length) (hq : q < n+j) (x : Fin n → Bool) :
    wv (clamp C j a q).gates x (n+j) = (x a && wv C.gates x q) := by
  change wv (C.gates.set j ⟨GateOp.and,[a.val,q]⟩) x (n+j) = _
  rw [wv_and _ x j a.val q (List.getElem?_set_self hj) (by omega) hq]
  rw [wv_in _ x a.val a.isLt]
  change (x a && wv (clamp C j a q).gates x q) = _
  rw [clamp_prefix C j a q hA x q hq]

lemma clamp_op {n : ℕ} (C : Circuit) (j : ℕ) (a : Fin n) (q : ℕ)
    (hj : j<C.gates.length) (hand : (gateAt C j).op=GateOp.and) (k : ℕ) :
    (gateAt (clamp C j a q) k).op=(gateAt C k).op := by
  by_cases hk : k=j
  · subst k; rw [clamp_at C j a q hj,hand]
  · rw [clamp_ne C j a q k hk]

lemma clamp_cone {n : ℕ} (C : Circuit) (j : ℕ) (a : Fin n) (p q : ℕ)
    (hj : j<C.gates.length) (hgate : gateAt C j=⟨GateOp.and,[p,q]⟩) :
    ∀ k<C.gates.length, ∀ i, InCone n (clamp C j a q) i k → InCone n C i k := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hk i hc
    have hk' : k<(clamp C j a q).gates.length := by simpa [clamp] using hk
    obtain ⟨w,hw,hn,hwk,hc⟩ := (inCone_iff n (clamp C j a q) i k hk').mp hc
    have hwOld : w ∈ (gateAt C k).inputs := by
      by_cases hkj : k=j
      · subst k
        rw [clamp_at C j a q hj] at hw
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
        rcases hw with rfl | rfl
        · omega
        · rw [hgate]; simp
      · rwa [clamp_ne C j a q k hkj] at hw
    apply (inCone_iff n C i k hk).mpr
    refine ⟨w,hwOld,hn,hwk,?_⟩
    rcases hc with hiw | hc
    · exact Or.inl hiw
    · exact Or.inr (ih (w-n) (by omega) (by omega) i hc)

lemma clamp_semantics {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (j : ℕ) (a : Fin n) (p q : ℕ)
    (hao : IsAO2 n C) (hj : j<C.gates.length)
    (hgate : gateAt C j=⟨GateOp.and,[p,q]⟩)
    (hsingle : wv C.gates (pairInput a a) p=true)
    (hstar : ∀ u v, G.Adj u v → gateVal n C j (pairInput u v)=true → a=u ∨ a=v)
    (hcorrect : circuitFun n C=graphFun G ∅) :
    IsAO2 n (clamp C j a q) ∧ circuitFun n (clamp C j a q)=graphFun G ∅ ∧
    (∀ (x : Fin n → Bool) (w : ℕ), wv (clamp C j a q).gates x w=true → wv C.gates x w=true) ∧
    (∀ u v, G.Adj u v → ∀ w,
      wv (clamp C j a q).gates (pairInput u v) w=wv C.gates (pairInput u v) w) := by
  let D := clamp C j a q
  have hA := ao_of n C hao
  have hpq := hao.2.1 j hj
  rw [hgate] at hpq
  have hp : p<n+j := hpq p (by simp)
  have hq : q<n+j := hpq q (by simp)
  have hg : C.gates[j]?=some ⟨GateOp.and,[p,q]⟩ := by
    rw [List.getElem?_eq_getElem hj]
    congr 1
    rw [←gateAt_eq C j hj,hgate]
  have hB := clamp_ao C j a q hA hq
  have hlen : C.gates.length=D.gates.length := by simp [D,clamp]
  have hd : ∀ k, k≠j → C.gates[k]?=D.gates[k]? := by
    intro k hk
    simp [D,clamp,List.getElem?_set_ne (Ne.symm hk)]
  have hpSingle (x : Fin n → Bool) (hx : x a=true) : wv C.gates x p=true := by
    apply wv_mono C.gates hA (pairInput a a) x ?_ p hsingle
    exact pair_le_input a a x hx hx
  have down (x : Fin n → Bool) : wv D.gates x (n+j)=true → wv C.gates x (n+j)=true := by
    rw [clamp_value C j a q hA hj hq x,wv_and C.gates x j p q hg hp hq]
    simp only [Bool.and_eq_true]
    exact fun hx => ⟨hpSingle x hx.1,hx.2⟩
  have allDown (x : Fin n → Bool) (w : ℕ) : wv D.gates x w=true → wv C.gates x w=true :=
    mono_off D.gates C.gates j x hB hlen.symm (fun k hk => (hd k hk).symm) (down x) w
  have pairs (u v : Fin n) (huv : G.Adj u v) (w : ℕ) :
      wv D.gates (pairInput u v) w=wv C.gates (pairInput u v) w := by
    have heq : wv C.gates (pairInput u v) (n+j)=wv D.gates (pairInput u v) (n+j) := by
      apply Bool.eq_iff_iff.mpr
      constructor
      · intro hold
        have ha := hstar u v huv hold
        have hqa : wv C.gates (pairInput u v) q=true := by
          rw [wv_and C.gates _ j p q hg hp hq] at hold
          exact (Bool.and_eq_true_eq_eq_true_and_eq_true _ _ ▸ hold).2
        rw [clamp_value C j a q hA hj hq]
        simp [pairInput,ha,hqa]
      · exact down _
    by_cases hw : w=n+j
    · subst w; exact heq.symm
    · exact (same_off C.gates D.gates j _ hA hlen hd w hw
        (Or.inr (fun _ _ _ _ => heq))).symm
  have hD := ao_to n D.gates D.output hB
  refine ⟨hD,?_,allDown,pairs⟩
  have up (x : Fin n → Bool) : circuitFun n D x=true → graphFun G ∅ x=true := by
    intro hx
    have old := allDown x C.output hx
    change circuitFun n C x=true at old
    simpa only [hcorrect] using old
  have low (x : Fin n → Bool) : graphFun G ∅ x=true → circuitFun n D x=true := by
    intro hx
    simp [graphFun] at hx
    obtain ⟨u,v,huv,hu,hv⟩ := hx
    have old : wv C.gates (pairInput u v) C.output=true := by
      change circuitFun n C (pairInput u v)=true
      rw [hcorrect]
      exact graph_pair_true G u v huv
    have fresh : wv D.gates (pairInput u v) D.output=true := by
      change wv D.gates (pairInput u v) C.output=true
      rw [pairs u v huv]
      exact old
    exact wv_mono D.gates hB (pairInput u v) x (pair_le_input u v x hu hv) D.output fresh
  funext x
  cases hd : circuitFun n D x <;> cases hf : graphFun G ∅ x <;> simp_all

end PEqualNP.Outside.L_meta_1772_aux.starTighten
