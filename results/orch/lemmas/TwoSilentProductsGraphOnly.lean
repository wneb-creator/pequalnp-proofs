import PEqualNP.Outside.L_meta_2448

namespace PEqualNP.Outside.L_meta_2448_aux.inputBound

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover


def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

lemma dep (n : ℕ) (C : Circuit) (hR : ∀ j < C.gates.length, (gateAt C j).inputs.length ≤ 2) :
    ∀ k, k ≤ C.gates.length → ∀ W : Finset ℕ, (∀ w ∈ W, w < n + k) →
      ∃ T : Finset (Fin n), T.card ≤ k + W.card ∧
        ∀ x y : Fin n → Bool, (∀ i ∈ T, x i = y i) →
          ∀ w ∈ W, val C (List.ofFn x) w = val C (List.ofFn y) w := by
  intro k
  induction k with
  | zero =>
    intro _ W hW
    refine ⟨Finset.univ.filter (fun i : Fin n => (i : ℕ) ∈ W), ?_, ?_⟩
    · rw [Nat.zero_add, ← Finset.card_image_of_injective _ Fin.val_injective]
      apply Finset.card_le_card
      intro a ha
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 ha
      exact (Finset.mem_filter.1 hi).2
    · intro x y h w hw
      have hw' : w < n := by simpa using hW w hw
      have e : ∀ z : Fin n → Bool, (List.ofFn z).getD w false = z ⟨w, hw'⟩ := by
        intro z; simp [List.getD_eq_getElem?_getD, hw']
      rw [val_input (by simp) hw', val_input (by simp) hw', e, e]
      exact h ⟨w, hw'⟩ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hw⟩)
  | succ k ih =>
    intro hk W hW
    by_cases hmem : n + k ∈ W
    · obtain ⟨W2, hW2⟩ : ∃ W2 : Finset ℕ, W2 = W.erase (n + k) ∪
          ((gateAt C k).inputs.filter (fun i => i < n + k)).toFinset := ⟨_, rfl⟩
      have hlt2 : ∀ w ∈ W2, w < n + k := by
        intro w hw
        rw [hW2] at hw
        rcases Finset.mem_union.1 hw with h | h
        · have h1 := hW w (Finset.mem_of_mem_erase h)
          have h2 := Finset.ne_of_mem_erase h
          omega
        · simp at h; exact h.2
      have hs1 : ∀ w ∈ W, w ≠ n + k → w ∈ W2 := by
        intro w hw hne
        rw [hW2]
        exact Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hne, hw⟩)
      have hs2 : ∀ i ∈ (gateAt C k).inputs, i < n + k → i ∈ W2 := by
        intro i hi hlt
        rw [hW2]
        exact Finset.mem_union_right _ (by simp [hi, hlt])
      have hc : W2.card + 1 ≤ W.card + 2 := by
        rw [hW2]
        have h1 := Finset.card_union_le (W.erase (n + k))
          ((gateAt C k).inputs.filter (fun i => i < n + k)).toFinset
        have h2 : ((gateAt C k).inputs.filter (fun i => i < n + k)).toFinset.card ≤ 2 :=
          (List.toFinset_card_le _).trans
            ((List.length_filter_le _ _).trans (hR k (by omega)))
        have h3 := Finset.card_erase_of_mem hmem
        have h4 : 0 < W.card := Finset.card_pos.2 ⟨_, hmem⟩
        omega
      obtain ⟨T, hT, hdep⟩ := ih (by omega) W2 hlt2
      refine ⟨T, by omega, ?_⟩
      intro x y h w hw
      by_cases hwk : w = n + k
      · rw [hwk, val_gate (by simp) (by omega), val_gate (by simp) (by omega)]
        congr 1
        apply List.map_congr_left
        intro i hi
        by_cases hlt : i < n + k
        · simp only [ite_eq_left hlt]
          exact hdep x y h i (hs2 i hi hlt)
        · simp only [ite_eq_right hlt]
      · exact hdep x y h w (hs1 w hw hwk)
    · obtain ⟨T, hT, hdep⟩ := ih (by omega) W (by
        intro w hw
        have h1 := hW w hw
        have h2 : w ≠ n + k := fun h => hmem (h ▸ hw)
        omega)
      exact ⟨T, by omega, hdep⟩

lemma main (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h2 : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hF : PEqualNP.MetaComplexity.circuitFun n C = graphFun G ∅) :
    G.support.ncard ≤ C.size + 1 := by
  obtain ⟨T, hT, hdep⟩ : ∃ T : Finset (Fin n), T.card ≤ C.gates.length + 1 ∧
      ∀ x y : Fin n → Bool, (∀ i ∈ T, x i = y i) →
        val C (List.ofFn x) C.output = val C (List.ofFn y) C.output := by
    by_cases ho : C.output < n + C.gates.length
    · obtain ⟨T, hT, hdep⟩ := dep n C (fun j hj => h2 _ (gateAt_mem hj)) C.gates.length le_rfl
        {C.output} (by simpa using ho)
      exact ⟨T, by simpa using hT, fun x y h => hdep x y h _ (by simp)⟩
    · exact ⟨∅, by simp, fun x y _ => by
        rw [val_ge (n := n) (by simp) (by omega), val_ge (n := n) (by simp) (by omega)]⟩
  have hsub : G.support ⊆ (T : Set (Fin n)) := by
    intro v hv
    obtain ⟨u, huv⟩ := (SimpleGraph.mem_support G).1 hv
    by_contra hvT
    have e := hdep (fun w => decide (w = u ∨ w = v)) (fun w => decide (w = u)) (by
      intro i hi
      have hne : i ≠ v := fun h => hvT (h ▸ hi)
      simp [hne])
    have fx : val C (List.ofFn (fun w => decide (w = u ∨ w = v))) C.output =
        graphFun G ∅ (fun w => decide (w = u ∨ w = v)) :=
      congrFun hF (fun w => decide (w = u ∨ w = v))
    have fy : val C (List.ofFn (fun w => decide (w = u))) C.output =
        graphFun G ∅ (fun w => decide (w = u)) :=
      congrFun hF (fun w => decide (w = u))
    have t1 : graphFun G ∅ (fun w => decide (w = u ∨ w = v)) = true := by
      unfold graphFun
      rw [Bool.or_eq_true]
      right
      rw [decide_eq_true_iff]
      exact ⟨v, u, huv, by simp, by simp⟩
    have t2 : graphFun G ∅ (fun w => decide (w = u)) = false := by
      unfold graphFun
      rw [Bool.or_eq_false_iff]
      refine ⟨by simp, ?_⟩
      rw [decide_eq_false_iff_not]
      rintro ⟨a, b, hab, ha, hb⟩
      have ha' : a = u := by simpa using ha
      have hb' : b = u := by simpa using hb
      exact hab.ne (ha'.trans hb'.symm)
    rw [fx, fy, t1, t2] at e
    cases e
  calc G.support.ncard ≤ (T : Set (Fin n)).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet T)
    _ = T.card := Set.ncard_coe_finset T
    _ ≤ C.size + 1 := hT

end PEqualNP.Outside.L_meta_2448_aux.inputBound

namespace PEqualNP.Outside.L_meta_2448_aux.twoSilentProducts

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm

def Cross {n : ℕ} (L R : Finset (Fin n)) (u v : Fin n) : Prop :=
  (u ∈ L ∧ v ∈ R) ∨ (v ∈ L ∧ u ∈ R)

lemma cross_mem {n : ℕ} {L R : Finset (Fin n)} {u v : Fin n}
    (h : Cross L R u v) : u ∈ L ∪ R ∧ v ∈ L ∪ R := by
  unfold Cross at h
  simp only [Finset.mem_union]
  tauto

lemma star_forest_cover_budget {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (K : Finset (Fin n))
    (hc : ∀ u v, G.Adj u v → u ∈ K ∨ v ∈ K)
    (hi : ∀ u ∈ K, ∀ v ∈ K, ¬ G.Adj u v)
    (hl : ∀ u, u ∉ K → ∀ v w, G.Adj u v → G.Adj u w → v = w)
    (ha : ∀ u ∈ K, u ∈ G.support) :
    G.edgeFinset.card + K.card ≤ G.support.ncard := by
  classical
  have hex : ∀ e ∈ G.edgeFinset, ∃ u, ∃ v,
      u ∉ K ∧ v ∈ K ∧ G.Adj u v ∧ e = s(u, v) := by
    intro e he
    induction e using Sym2.ind with
    | _ u v =>
      have huv : G.Adj u v := SimpleGraph.mem_edgeFinset.mp he
      rcases hc u v huv with hu | hv
      · exact ⟨v, u, fun hv => hi u hu v hv huv, hu, huv.symm, Sym2.eq_swap⟩
      · exact ⟨u, v, fun hu => hi u hu v hv huv, hv, huv, rfl⟩
  let leaf : {e // e ∈ G.edgeFinset} → Fin n := fun e => (hex e.val e.property).choose
  have hp : ∀ e : {e // e ∈ G.edgeFinset}, ∃ v,
      leaf e ∉ K ∧ v ∈ K ∧ G.Adj (leaf e) v ∧ e.val = s(leaf e, v) := by
    intro e
    exact (hex e.val e.property).choose_spec
  have hinj : Set.InjOn leaf (G.edgeFinset.attach : Set {e // e ∈ G.edgeFinset}) := by
    intro e1 _ e2 _ he
    obtain ⟨v1, h1, _, ha1, hv1⟩ := hp e1
    obtain ⟨v2, _, _, ha2, hv2⟩ := hp e2
    have hv : v1 = v2 := hl (leaf e1) h1 v1 v2 ha1 (he ▸ ha2)
    apply Subtype.ext
    rw [hv1, hv2, he, hv]
  let L := G.edgeFinset.attach.image leaf
  have hcard : L.card = G.edgeFinset.card := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_attach]
  have hd : Disjoint K L := by
    apply Finset.disjoint_left.mpr
    intro u hu hL
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hL
    exact (hp e).choose_spec.1 hu
  have hs : ((K ∪ L : Finset (Fin n)) : Set (Fin n)) ⊆ G.support := by
    intro u hu
    rcases Finset.mem_union.mp hu with huK | huL
    · exact ha u huK
    · obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp huL
      obtain ⟨v, _, _, huv, _⟩ := hp e
      exact huv.mem_support_left
  have hn := Set.ncard_le_ncard hs (Set.toFinite G.support)
  rw [Set.ncard_coe_finset, Finset.card_union_of_disjoint hd, hcard] at hn
  omega

lemma biclique_cover {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (L R : Finset (Fin n))
    (hedge : ∀ u ∈ L, ∀ v ∈ R, G.Adj u v) :
    ∃ K : Finset (Fin n), K ⊆ L ∪ R ∧ K.card ≤ 1 ∧
      (∀ u ∈ K, u ∈ G.support) ∧
      ∀ u v, Cross L R u v → u ∈ K ∨ v ∈ K := by
  classical
  by_cases hL : L.Nonempty
  · by_cases hR : R.Nonempty
    · have hsmall : L.card ≤ 1 ∨ R.card ≤ 1 := by
        by_contra! h
        obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp h.1
        have hs : R ⊆ Finset.univ.filter (fun w => G.Adj u w ∧ G.Adj v w) := by
          intro w hw
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hedge u hu w hw, hedge v hv w hw⟩
        have hcard := Finset.card_le_card hs
        have hfour := h4 u v huv
        omega
      rcases hsmall with hsmall | hsmall
      · obtain ⟨u, hLu⟩ := Finset.card_eq_one.mp (le_antisymm hsmall (Finset.card_pos.mpr hL))
        obtain ⟨v, hv⟩ := hR
        refine ⟨{u}, ?_, by simp, ?_, ?_⟩
        · intro w hw
          rw [Finset.mem_singleton] at hw
          subst w
          apply Finset.mem_union_left
          rw [hLu]
          simp
        · intro w hw
          rw [Finset.mem_singleton] at hw
          subst w
          exact (hedge u (by rw [hLu]; simp) v hv).mem_support_left
        · intro a b hab
          simp only [Cross, hLu, Finset.mem_singleton] at hab ⊢
          tauto
      · obtain ⟨v, hRv⟩ := Finset.card_eq_one.mp (le_antisymm hsmall (Finset.card_pos.mpr hR))
        obtain ⟨u, hu⟩ := hL
        refine ⟨{v}, ?_, by simp, ?_, ?_⟩
        · intro w hw
          rw [Finset.mem_singleton] at hw
          subst w
          apply Finset.mem_union_right
          rw [hRv]
          simp
        · intro w hw
          rw [Finset.mem_singleton] at hw
          subst w
          exact (hedge u hu v (by rw [hRv]; simp)).mem_support_right
        · intro a b hab
          simp only [Cross, hRv, Finset.mem_singleton] at hab ⊢
          tauto
    · refine ⟨∅, by simp, by simp, by simp, ?_⟩
      have he : R = ∅ := Finset.not_nonempty_iff_eq_empty.mp hR
      simp [Cross, he]
  · refine ⟨∅, by simp, by simp, by simp, ?_⟩
    have he : L = ∅ := Finset.not_nonempty_iff_eq_empty.mp hL
    simp [Cross, he]

lemma two_disjoint_bicliques_budget {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (A B C D : Finset (Fin n))
    (hd : Disjoint (A ∪ B) (C ∪ D))
    (hedge : ∀ u v, G.Adj u v ↔ Cross A B u v ∨ Cross C D u v) :
    ∃ K : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ K ∨ v ∈ K) ∧
      G.edgeFinset.card + K.card ≤ G.support.ncard := by
  classical
  obtain ⟨K1, hs1, hc1, ha1, he1⟩ := biclique_cover G h4 A B
    (fun u hu v hv => (hedge u v).mpr (Or.inl (Or.inl ⟨hu, hv⟩)))
  obtain ⟨K2, hs2, hc2, ha2, he2⟩ := biclique_cover G h4 C D
    (fun u hu v hv => (hedge u v).mpr (Or.inr (Or.inl ⟨hu, hv⟩)))
  have sep : ∀ u, u ∈ A ∪ B → u ∈ C ∪ D → False := Finset.disjoint_left.mp hd
  have k1 (u : Fin n) (hu : u ∈ A ∪ B) (hk : u ∈ K1 ∪ K2) : u ∈ K1 := by
    rcases Finset.mem_union.mp hk with hk | hk
    · exact hk
    · exact (sep u hu (hs2 hk)).elim
  have k2 (u : Fin n) (hu : u ∈ C ∪ D) (hk : u ∈ K1 ∪ K2) : u ∈ K2 := by
    rcases Finset.mem_union.mp hk with hk | hk
    · exact (sep u (hs1 hk) hu).elim
    · exact hk
  have hcov : ∀ u v, G.Adj u v → u ∈ K1 ∪ K2 ∨ v ∈ K1 ∪ K2 := by
    intro u v huv
    rcases (hedge u v).mp huv with h | h
    · rcases he1 u v h with h | h
      · exact Or.inl (Finset.mem_union_left _ h)
      · exact Or.inr (Finset.mem_union_left _ h)
    · rcases he2 u v h with h | h
      · exact Or.inl (Finset.mem_union_right _ h)
      · exact Or.inr (Finset.mem_union_right _ h)
  refine ⟨K1 ∪ K2, hcov, star_forest_cover_budget G (K1 ∪ K2) hcov ?_ ?_ ?_⟩
  · intro u hu v hv huv
    have heq : u = v := by
      rcases (hedge u v).mp huv with h | h
      · exact Finset.card_le_one.mp hc1 u (k1 u (cross_mem h).1 hu) v (k1 v (cross_mem h).2 hv)
      · exact Finset.card_le_one.mp hc2 u (k2 u (cross_mem h).1 hu) v (k2 v (cross_mem h).2 hv)
    exact huv.ne heq
  · intro u hu v w huv huw
    have hv : v ∈ K1 ∪ K2 := (hcov u v huv).resolve_left hu
    have hw : w ∈ K1 ∪ K2 := (hcov u w huw).resolve_left hu
    rcases (hedge u v).mp huv with h1 | h1
    · rcases (hedge u w).mp huw with h2 | h2
      · exact Finset.card_le_one.mp hc1 v (k1 v (cross_mem h1).2 hv) w (k1 w (cross_mem h2).2 hw)
      · exact (sep u (cross_mem h1).1 (cross_mem h2).1).elim
    · rcases (hedge u w).mp huw with h2 | h2
      · exact (sep u (cross_mem h2).1 (cross_mem h1).1).elim
      · exact Finset.card_le_one.mp hc2 v (k2 v (cross_mem h1).2 hv) w (k2 w (cross_mem h2).2 hw)
  · intro u hu
    rcases Finset.mem_union.mp hu with h | h
    · exact ha1 u h
    · exact ha2 u h

set_option maxHeartbeats 4000000 in
lemma four_sides_budget {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (P Q R S : Finset (Fin n))
    (hPQ : Disjoint P Q) (hRS : Disjoint R S)
    (hedge : ∀ u v, G.Adj u v ↔
      (u ∈ P ∨ v ∈ P) ∧ (u ∈ Q ∨ v ∈ Q) ∧ (u ∈ R ∨ v ∈ R) ∧ (u ∈ S ∨ v ∈ S)) :
    ∃ K : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ K ∨ v ∈ K) ∧
      G.edgeFinset.card + K.card ≤ G.support.ncard := by
  have hpq : ∀ u, u ∈ P → u ∈ Q → False := Finset.disjoint_left.mp hPQ
  have hrs : ∀ u, u ∈ R → u ∈ S → False := Finset.disjoint_left.mp hRS
  apply two_disjoint_bicliques_budget G h4 (P ∩ R) (Q ∩ S) (P ∩ S) (Q ∩ R)
  · apply Finset.disjoint_left.mpr
    intro u h1 h2
    simp only [Finset.mem_union, Finset.mem_inter] at h1 h2
    have hPQu := hpq u
    have hRSu := hrs u
    tauto
  · intro u v
    rw [hedge]
    simp only [Cross, Finset.mem_inter]
    have hPQu := hpq u
    have hPQv := hpq v
    have hRSu := hrs u
    have hRSv := hrs v
    tauto

lemma exists_minimum_star_of_four_sides {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (P Q R S : Finset (Fin n))
    (hPQ : Disjoint P Q) (hRS : Disjoint R S)
    (hedge : ∀ u v, G.Adj u v ↔
      (u ∈ P ∨ v ∈ P) ∧ (u ∈ Q ∨ v ∈ Q) ∧ (u ∈ R ∨ v ∈ R) ∧ (u ∈ S ∨ v ∈ S)) :
    ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧
      (∀ E : Circuit, Monotone2 E → circuitFun n E = graphFun G ∅ → D.size ≤ E.size) ∧
      HasStarProfile n G D := by
  classical
  obtain ⟨K, hK, hbudget⟩ := four_sides_budget G h4 P Q R S hPQ hRS hedge
  by_cases hE : G.edgeFinset.Nonempty
  · have hcover : ∀ e ∈ G.edgeFinset, ∃ u ∈ K, u ∈ e := by
      intro e he
      induction e using Sym2.ind with
      | _ u v =>
        rcases hK u v (SimpleGraph.mem_edgeFinset.mp he) with hu | hv
        · exact ⟨u, hu, Sym2.mem_mk_left _ _⟩
        · exact ⟨v, hv, Sym2.mem_mk_right _ _⟩
    obtain ⟨D, hD, hDf, hDs, hDsize⟩ :=
      PEqualNP.Outside.L_meta_2448.StarCoverPrototype.star_cover_witness G hE K hcover
    refine ⟨D, hD, hDf, ?_, hDs⟩
    intro E hmono hEf
    have hsupport := PEqualNP.Outside.L_meta_2448_aux.inputBound.main n G E
      (fun g hg => (hmono g hg).2) hEf
    omega
  · exact PEqualNP.Outside.L_meta_2448_aux.oneJunkStar.empty_graph_star_minimum G
      (Finset.not_nonempty_iff_eq_empty.mp hE)

end PEqualNP.Outside.L_meta_2448_aux.twoSilentProducts
