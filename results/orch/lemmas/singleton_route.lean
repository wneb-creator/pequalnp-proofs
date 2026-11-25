import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1772_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

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

lemma inCone_lt (n : ℕ) (C : Circuit) : ∀ k, k < C.gates.length → ∀ i, InCone n C i k → i < k := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hk i h
    obtain ⟨w, hw, hn, hlt, h | h⟩ := (inCone_iff n C i k hk).1 h
    · omega
    · have := ih (w - n) (by omega) (by omega) i h
      omega

lemma inCone_trans (n : ℕ) (C : Circuit) :
    ∀ k, k < C.gates.length → ∀ i j, InCone n C i j → InCone n C j k → InCone n C i k := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hk i j hij hjk
    obtain ⟨w, hw, hn, hlt, h | h⟩ := (inCone_iff n C j k hk).mp hjk
    · apply (inCone_iff n C i k hk).mpr
      exact ⟨w, hw, hn, hlt, Or.inr (h ▸ hij)⟩
    · apply (inCone_iff n C i k hk).mpr
      exact ⟨w, hw, hn, hlt, Or.inr (ih (w - n) (by omega) (by omega) i j hij h)⟩

lemma owned_ancestor (n : ℕ) (C : Circuit) (u v : Fin n) :
    ∀ j, j < C.gates.length → (gateAt C j).op = GateOp.and →
      gateVal n C j (pairInput u v) = true →
      ∃ i, (i = j ∨ InCone n C i j) ∧ Owns n C i u v := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj hand hval
    by_cases hown : Owns n C j u v
    · exact ⟨j, Or.inl rfl, hown⟩
    · have hex : ∃ i, i < j ∧ InCone n C i j ∧
          (gateAt C i).op = GateOp.and ∧ gateVal n C i (pairInput u v) = true := by
        by_contra hn
        apply hown
        refine ⟨hj, hand, hval, ?_⟩
        intro i hi hc ha
        cases hv : gateVal n C i (pairInput u v)
        · rfl
        · exact False.elim (hn ⟨i, hi, hc, ha, hv⟩)
      obtain ⟨i, hi, hc, ha, hv⟩ := hex
      obtain ⟨k, hk, hko⟩ := ih i hi (by omega) ha hv
      refine ⟨k, Or.inr ?_, hko⟩
      rcases hk with rfl | hki
      · exact hc
      · exact inCone_trans n C j hj k i hki hc

lemma nonowning_true_has_owning_ancestor (n : ℕ) (C : Circuit) (j : ℕ)
    (u v : Fin n) (hj : j < C.gates.length) (hand : (gateAt C j).op = GateOp.and)
    (hval : gateVal n C j (pairInput u v) = true) (hno : ¬ Owns n C j u v) :
    ∃ i, i < j ∧ InCone n C i j ∧ Owns n C i u v := by
  obtain ⟨i, hi, ho⟩ := owned_ancestor n C u v j hj hand hval
  rcases hi with rfl | hi
  · exact (hno ho).elim
  · exact ⟨i, inCone_lt n C j hj i hi, hi, ho⟩

end PEqualNP.Outside.L_meta_1772_aux

namespace PEqualNP.Outside.L_meta_1772_aux.singleton

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
  PEqualNP.TopForm PEqualNP.CleanedNonEdge

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

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

lemma gate_mono (n : ℕ) (C : Circuit) (hM : Monotone2 C)
    (x y : Fin n → Bool) (hxy : ∀ v, x v = true → y v = true) (j : ℕ) :
    gateVal n C j x = true → gateVal n C j y = true := by
  apply mono2 C.gates (fun g hg => ?_) (List.ofFn x) (List.ofFn y)
    (by simp) (ofFn_mono n x y hxy) (n+j)
  exact hM g hg

lemma own_ancestor_singleton_false (n : ℕ) (C : Circuit) (hM : Monotone2 C)
    (j : ℕ) (u v : Fin n) (ho : Owns n C j u v)
    (i : ℕ) (hi : i < j) (hc : InCone n C i j) (ha : (gateAt C i).op = GateOp.and) :
    gateVal n C i (pairInput u u) = false ∧ gateVal n C i (pairInput v v) = false := by
  have hf := ho.2.2.2 i hi hc ha
  constructor
  · cases hs : gateVal n C i (pairInput u u)
    · rfl
    · have ht := gate_mono n C hM (pairInput u u) (pairInput u v) (by
        intro w hw
        simp only [pairInput, decide_eq_true_eq, or_self] at hw
        subst w
        simp [pairInput]) i hs
      rw [hf] at ht
      cases ht
  · cases hs : gateVal n C i (pairInput v v)
    · rfl
    · have ht := gate_mono n C hM (pairInput v v) (pairInput u v) (by
        intro w hw
        simp only [pairInput, decide_eq_true_eq, or_self] at hw
        subst w
        simp [pairInput]) i hs
      rw [hf] at ht
      cases ht

lemma topform_bad_has_dirty_owner (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ht : TopForm G C) (j : ℕ) (hj : j < C.gates.length)
    (ha : (gateAt C j).op = GateOp.and) (u v : Fin n)
    (hv : gateVal n C j (pairInput u v) = true) (ho : ¬ Owns n C j u v) :
    ∃ i, i < j ∧ InCone n C i j ∧ Owns n C i u v ∧ IsDirtyAnd n G C i := by
  classical
  obtain ⟨i, hi, hc, hio⟩ := nonowning_true_has_owning_ancestor n C j u v hj ha hv ho
  have hn : ¬ BelowF G C i := fun hb => ht i (hi.trans hj) j hj hio.2.1 hb ha hc
  have he : ∃ x : Fin n → Bool, gateVal n C i x = true ∧ graphFun G ∅ x = false := by
    simpa only [BelowF, not_forall, not_imp, Bool.not_eq_true, exists_prop] using hn
  obtain ⟨x, hxi, hxG⟩ := he
  exact ⟨i, hi, hc, hio, hio.2.1, hi.trans hj, x, hxi, hxG⟩

end PEqualNP.Outside.L_meta_1772_aux.singleton
