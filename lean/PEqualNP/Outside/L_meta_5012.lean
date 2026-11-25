import PEqualNP.Defs
import Mathlib.Tactic.Tauto
import Mathlib.Order.Preorder.Finite

namespace PEqualNP.Outside.L_meta_5012

open PEqualNP.EdgeOwnership

def setOr {n : ℕ} (A : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∃ a ∈ A, x a = true)

def tripleCore {n : ℕ} (A B D : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  (setOr (A ∩ D) x && setOr B x) || (setOr A x && setOr (B ∩ D) x)

lemma setOr_pair {n : ℕ} (A : Finset (Fin n)) (u v : Fin n) :
    setOr A (pairInput u v) = decide (u ∈ A ∨ v ∈ A) := by
  simp [setOr, pairInput, and_or_left, exists_or]

lemma tripleCore_le {n : ℕ} (A B D : Finset (Fin n)) (x : Fin n → Bool)
    (h : tripleCore A B D x = true) :
    setOr A x && setOr B x && setOr D x = true := by
  simp only [tripleCore, Bool.or_eq_true, Bool.and_eq_true, setOr,
    decide_eq_true_eq, Finset.mem_inter] at h ⊢
  rcases h with ⟨⟨a, ⟨ha, hd⟩, hx⟩, hb⟩ | ⟨ha, ⟨b, ⟨hb, hd⟩, hx⟩⟩
  · exact ⟨⟨⟨a, ha, hx⟩, hb⟩, ⟨a, hd, hx⟩⟩
  · exact ⟨⟨ha, ⟨b, hb, hx⟩⟩, ⟨b, hd, hx⟩⟩

lemma tripleCore_pair {n : ℕ} (A B D : Finset (Fin n)) (hAB : Disjoint A B)
    (u v : Fin n) :
    tripleCore A B D (pairInput u v) =
      (setOr A (pairInput u v) && setOr B (pairInput u v) &&
        setOr D (pairInput u v)) := by
  have hu : ¬ (u ∈ A ∧ u ∈ B) := fun h => Finset.disjoint_left.mp hAB h.1 h.2
  have hv : ¬ (v ∈ A ∧ v ∈ B) := fun h => Finset.disjoint_left.mp hAB h.1 h.2
  apply Bool.eq_iff_iff.mpr
  simp only [tripleCore, Bool.or_eq_true, Bool.and_eq_true, setOr_pair,
    decide_eq_true_eq, Finset.mem_inter]
  tauto

lemma tripleCore_eq_of_subset {n : ℕ} (A B D : Finset (Fin n))
    (hD : D ⊆ A ∪ B) (x : Fin n → Bool) :
    tripleCore A B D x = (setOr A x && setOr B x && setOr D x) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · exact tripleCore_le A B D x
  · intro h
    simp only [Bool.and_eq_true, setOr, decide_eq_true_eq] at h
    obtain ⟨⟨ha, hb⟩, d, hd, hx⟩ := h
    simp only [tripleCore, Bool.or_eq_true, Bool.and_eq_true, setOr,
      decide_eq_true_eq, Finset.mem_inter]
    rcases Finset.mem_union.mp (hD hd) with hda | hdb
    · exact Or.inl ⟨⟨d, ⟨hda, hd⟩, hx⟩, hb⟩
    · exact Or.inr ⟨ha, ⟨d, ⟨hdb, hd⟩, hx⟩⟩

lemma projected_or_cost {n : ℕ} (A B D : Finset (Fin n)) (hAB : Disjoint A B)
    (ha : (A ∩ D).Nonempty) (hb : (B ∩ D).Nonempty) :
    ((A ∩ D).card - 1) + ((B ∩ D).card - 1) + 1 ≤ D.card - 1 := by
  have hd : Disjoint (A ∩ D) (B ∩ D) :=
    hAB.mono Finset.inter_subset_left Finset.inter_subset_left
  have hs : (A ∩ D) ∪ (B ∩ D) ⊆ D := by
    intro a h
    rcases Finset.mem_union.mp h with h | h <;> exact (Finset.mem_inter.mp h).2
  have hc := Finset.card_le_card hs
  rw [Finset.card_union_of_disjoint hd] at hc
  have hca := Finset.card_pos.mpr ha
  have hcb := Finset.card_pos.mpr hb
  omega

def Increasing {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x y, (∀ v, x v = true → y v = true) → f x = true → f y = true

lemma graph_eq_of_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (f : (Fin n → Bool) → Bool) (hf : Increasing f)
    (hbelow : ∀ x, f x = true → PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true)
    (hpairs : ∀ u v, G.Adj u v → f (pairInput u v) = true) :
    f = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
  funext x
  apply Bool.eq_iff_iff.mpr
  refine ⟨hbelow x, ?_⟩
  intro h
  simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, Finset.notMem_empty,
    false_and, exists_false, decide_false, Bool.false_or, decide_eq_true_eq] at h
  obtain ⟨u, v, huv, hu, hv⟩ := h
  apply hf (pairInput u v) x ?_ (hpairs u v huv)
  intro w hw
  simp only [pairInput, decide_eq_true_eq] at hw
  rcases hw with rfl | rfl
  · exact hu
  · exact hv

lemma context_replacement {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (context : (Fin n → Bool) → Bool → Bool) (H K : (Fin n → Bool) → Bool)
    (hcontext : ∀ x y b c, (∀ v, x v = true → y v = true) →
      (b = true → c = true) → context x b = true → context y c = true)
    (hK : Increasing K) (hKH : ∀ x, K x = true → H x = true)
    (hpairs : ∀ u v, G.Adj u v → K (pairInput u v) = H (pairInput u v))
    (hF : ∀ x, context x (H x) = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x) :
    (fun x => context x (K x)) = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
  apply graph_eq_of_pair G
  · intro x y hxy hx
    exact hcontext x y (K x) (K y) hxy (hK x y hxy) hx
  · intro x hx
    rw [← hF x]
    exact hcontext x x (K x) (H x) (fun _ => id) (hKH x) hx
  · intro u v huv
    rw [hpairs u v huv, hF]
    simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, Bool.or_eq_true,
      decide_eq_true_eq]
    right
    exact ⟨u, v, huv, by simp [pairInput], by simp [pairInput]⟩

lemma clean_context_below {α : Type*} (F H K : α → Bool) (context : α → Bool → Bool)
    (hcontext : ∀ x b c, (b = true → c = true) →
      context x b = true → context x c = true)
    (hK : ∀ x, K x = true → F x = true)
    (hOld : ∀ x, context x (H x) = true → F x = true) :
    ∀ x, context x (K x) = true → F x = true := by
  intro x hx
  by_cases hk : K x = true
  · exact hK x hk
  · apply hOld x
    exact hcontext x (K x) (H x) (fun h => (hk h).elim) hx

lemma clean_critical_replacement {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (context : (Fin n → Bool) → Bool → Bool) (H K : (Fin n → Bool) → Bool)
    (hcontext : ∀ x y b c, (∀ v, x v = true → y v = true) →
      (b = true → c = true) → context x b = true → context y c = true)
    (hKmono : Increasing K)
    (hKclean : ∀ x, K x = true → PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true)
    (hcritical : ∀ u v, G.Adj u v → context (pairInput u v) false = false →
      K (pairInput u v) = true)
    (hF : ∀ x, context x (H x) = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x) :
    (fun x => context x (K x)) = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
  apply graph_eq_of_pair G
  · intro x y hxy hx
    exact hcontext x y (K x) (K y) hxy (hKmono x y hxy) hx
  · exact clean_context_below _ H K context
      (fun x b c => hcontext x x b c (fun _ => id)) hKclean
      (fun x hx => (hF x).symm ▸ hx)
  · intro u v huv
    have hEdge : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ (pairInput u v) = true := by
      simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, Bool.or_eq_true,
        decide_eq_true_eq]
      right
      exact ⟨u, v, huv, by simp [pairInput], by simp [pairInput]⟩
    by_cases hz : context (pairInput u v) false = true
    · exact hcontext _ _ false (K (pairInput u v)) (fun _ => id)
        (fun h => Bool.false_ne_true h |>.elim) hz
    · have hk := hcritical u v huv (Bool.eq_false_iff.mpr hz)
      have hOld : context (pairInput u v) (H (pairInput u v)) = true :=
        (hF (pairInput u v)).trans hEdge
      exact hcontext _ _ (H (pairInput u v)) (K (pairInput u v))
        (fun _ => id) (fun _ => hk) hOld

lemma graph_pair_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v : Fin n) :
    PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, Finset.notMem_empty,
    false_and, exists_false, decide_false, Bool.false_or, decide_eq_true_eq, pairInput]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  · intro h
    exact ⟨u, v, h, Or.inl rfl, Or.inr rfl⟩

lemma shared_raw_critical_filter {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (H : (Fin n → Bool) → Bool) (R S : Finset (Fin n)) (r u v : Fin n)
    (hr : r ∈ R)
    (hclean : ∀ x, ((setOr R x || H x) && setOr S x) = true →
      PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true)
    (hR : setOr R (pairInput u v) = false)
    (hS : setOr S (pairInput u v) = true) :
    r ≠ u ∧ r ≠ v ∧ ∃ w : Fin n, (w = u ∨ w = v) ∧ G.Adj r w ∧
      ∀ x, H x = true → x w = true →
        PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true := by
  have hRu : u ∉ R := by
    intro h
    have ht : setOr R (pairInput u v) = true := by simp [setOr_pair, h]
    exact Bool.false_ne_true (hR.symm.trans ht)
  have hRv : v ∉ R := by
    intro h
    have ht : setOr R (pairInput u v) = true := by simp [setOr_pair, h]
    exact Bool.false_ne_true (hR.symm.trans ht)
  have hs : u ∈ S ∨ v ∈ S := by simpa only [setOr_pair, decide_eq_true_eq] using hS
  obtain ⟨w, hw, hwS⟩ : ∃ w, (w = u ∨ w = v) ∧ w ∈ S := by
    rcases hs with hs | hs
    · exact ⟨u, Or.inl rfl, hs⟩
    · exact ⟨v, Or.inr rfl, hs⟩
  refine ⟨fun h => hRu (h ▸ hr), fun h => hRv (h ▸ hr), w, hw, ?_, ?_⟩
  · apply (graph_pair_iff G r w).mp
    apply hclean (pairInput r w)
    have h1 : setOr R (pairInput r w) = true := by simp [setOr_pair, hr]
    have h2 : setOr S (pairInput r w) = true := by simp [setOr_pair, hwS]
    simp [h1, h2]
  · intro x hx hxw
    apply hclean x
    have hs : setOr S x = true := by
      simpa only [setOr, decide_eq_true_eq] using (show ∃ w ∈ S, x w = true from ⟨w, hwS, hxw⟩)
    simp [hx, hs]

end PEqualNP.Outside.L_meta_5012


namespace PEqualNP.Outside.L_meta_5012.Structural

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

-- Circuit evaluation and OR reachability follow L_meta_1490 and L_meta_4901.
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
lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [ite_eq_right hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [ite_eq_left hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h'; exact ⟨hlt, h'⟩
    · rw [ite_eq_right hlt] at h'; cases h'
  · intro h i hi
    rw [ite_eq_left (h i hi).1]; exact (h i hi).2
lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

lemma gateVal_eq_val (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    PEqualNP.EdgeOwnership.gateVal n C j x = val C (List.ofFn x) (n + j) := rfl

-- Erasing an unread gate gives a smaller circuit, as in L_meta_7696.
def shiftW (n k w : ℕ) : ℕ :=
  if w < n + k then w else w - 1

def unshiftW (n k w : ℕ) : ℕ :=
  if w < n + k then w else w + 1

def unshiftG (k j : ℕ) : ℕ :=
  if j < k then j else j + 1

def shiftGate (n k : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (shiftW n k)⟩

def delDead (n k : ℕ) (C : Circuit) : Circuit :=
  ⟨(C.gates.eraseIdx k).map (shiftGate n k), shiftW n k C.output⟩

lemma unshiftW_shiftW (n k w : ℕ) (hne : w ≠ n + k) :
    unshiftW n k (shiftW n k w) = w := by
  unfold unshiftW shiftW
  split_ifs <;> omega


lemma delDead_size (n k : ℕ) (C : Circuit) (hk : k < C.size) :
    (delDead n k C).size + 1 = C.size := by
  unfold Circuit.size at hk ⊢
  unfold delDead
  simp only [List.length_map, List.length_eraseIdx_of_lt hk]
  omega

lemma delDead_length (n k : ℕ) (C : Circuit) (hk : k < C.gates.length) :
    (delDead n k C).gates.length = C.gates.length - 1 := by
  simp [delDead, List.length_eraseIdx_of_lt hk]

lemma delDead_gateAt (n k : ℕ) (C : Circuit) (hk : k < C.gates.length)
    (j : ℕ) (hj : j < (delDead n k C).gates.length) :
    gateAt (delDead n k C) j = shiftGate n k (gateAt C (unshiftG k j)) := by
  have hj_lt : j < C.gates.length - 1 := by
    rw [← delDead_length n k C hk]; exact hj
  have hj_e : j < (C.gates.eraseIdx k).length := by
    rw [List.length_eraseIdx_of_lt hk]; exact hj_lt
  rw [gateAt_eq hj]
  simp only [delDead, List.getElem_map, unshiftG]
  split_ifs with hjk
  · rw [List.getElem_eraseIdx_of_lt hj_e hjk, gateAt_eq (C := C) (j := j) (by omega)]
  · rw [List.getElem_eraseIdx_of_ge hj_e (by omega), gateAt_eq (C := C) (j := j + 1) (by omega)]


lemma delDead_readsBack (n k : ℕ) (C : Circuit) (hRB : ReadsBack n C)
    (hk : k < C.gates.length) (hno : ∀ j < C.gates.length, n + k ∉ (gateAt C j).inputs) :
    ReadsBack n (delDead n k C) := by
  intro j hj w' hw'
  rw [delDead_gateAt n k C hk j hj] at hw'
  simp only [shiftGate, List.mem_map] at hw'
  obtain ⟨w, hw, rfl⟩ := hw'
  have hj_len : j < C.gates.length - 1 := by
    rw [← delDead_length n k C hk]; exact hj
  have hj0_lt : unshiftG k j < C.gates.length := by
    unfold unshiftG; split_ifs <;> omega
  have hw_lt : w < n + unshiftG k j := hRB (unshiftG k j) hj0_lt w hw
  have hw_ne : w ≠ n + k := fun heq => hno (unshiftG k j) hj0_lt (heq ▸ hw)
  unfold shiftW
  unfold unshiftG at hw_lt
  split_ifs at hw_lt ⊢ <;> omega


def evalStep {α : Type} (d0 : α) (evalG : GateOp → List α → α) (acc : List α) (g : Gate) :
    List α :=
  acc ++ [evalG g.op (g.inputs.map fun i => acc.getD i d0)]

lemma foldl_evalStep_length {α : Type} (d0 : α) (evalG : GateOp → List α → α)
    (gs : List Gate) (acc : List α) :
    (gs.foldl (evalStep d0 evalG) acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, evalStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_evalStep_prefix {α : Type} (d0 : α) (evalG : GateOp → List α → α)
    (gs : List Gate) (acc : List α) (w : ℕ) (hw : w < acc.length) :
    (gs.foldl (evalStep d0 evalG) acc).getD w d0 = acc.getD w d0 := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    have hw' : w < (evalStep d0 evalG acc g).length := by
      simp only [evalStep, List.length_append, List.length_singleton]
      omega
    rw [List.foldl_cons, ih (evalStep d0 evalG acc g) hw']
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    simp only [evalStep, List.getElem?_append_left hw]

lemma foldl_evalStep_gate {α : Type} (d0 : α) (evalG : GateOp → List α → α)
    (n : ℕ) (C : Circuit) (init : List α) (hinit : init.length = n)
    (hRB : ReadsBack n C) (j : ℕ) (hj : j < C.gates.length) :
    (C.gates.foldl (evalStep d0 evalG) init).getD (n + j) d0 =
      evalG (gateAt C j).op
        ((gateAt C j).inputs.map fun u => (C.gates.foldl (evalStep d0 evalG) init).getD u d0) := by
  have hsplit : C.gates = C.gates.take j ++ [C.gates[j]] ++ C.gates.drop (j + 1) := by
    have h1 := List.take_append_drop j C.gates
    have h2 : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    simp only [List.append_assoc, List.singleton_append, h1]
  set acc := (C.gates.take j).foldl (evalStep d0 evalG) init with hacc
  have hacc_len : acc.length = n + j := by
    rw [hacc, foldl_evalStep_length, hinit, List.length_take]
    omega
  have hpref : ∀ u < n + j,
      (C.gates.foldl (evalStep d0 evalG) init).getD u d0 = acc.getD u d0 := by
    intro u hu
    conv_lhs => rw [← List.take_append_drop j C.gates]
    rw [List.foldl_append, ← hacc]
    exact foldl_evalStep_prefix d0 evalG (C.gates.drop j) acc u (by omega)
  have hval : (C.gates.foldl (evalStep d0 evalG) init).getD (n + j) d0 =
      evalG C.gates[j].op (C.gates[j].inputs.map fun u => acc.getD u d0) := by
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_append, ← hacc, List.foldl_cons, List.foldl_nil]
    have hlen : n + j < (evalStep d0 evalG acc C.gates[j]).length := by
      simp only [evalStep, List.length_append, List.length_singleton]
      omega
    rw [foldl_evalStep_prefix d0 evalG (C.gates.drop (j + 1)) (evalStep d0 evalG acc C.gates[j])
      (n + j) hlen]
    rw [List.getD_eq_getElem?_getD]
    simp only [evalStep, List.getElem?_append_right (by omega : acc.length ≤ n + j),
      hacc_len, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  rw [hval, gateAt_eq hj]
  congr 1
  apply List.map_congr_left
  intro u hu
  rw [← gateAt_eq hj] at hu
  exact (hpref u (hRB j hj u hu)).symm

lemma delDead_evalStep_eq {α : Type} (d0 : α) (evalG : GateOp → List α → α)
    (n k : ℕ) (C : Circuit) (init : List α) (hinit : init.length = n)
    (hRB : ReadsBack n C) (hk : k < C.gates.length)
    (hno : ∀ j < C.gates.length, n + k ∉ (gateAt C j).inputs) :
    ∀ w : ℕ,
      ((delDead n k C).gates.foldl (evalStep d0 evalG) init).getD w d0 =
        (C.gates.foldl (evalStep d0 evalG) init).getD (unshiftW n k w) d0 := by
  have hRB' : ReadsBack n (delDead n k C) := delDead_readsBack n k C hRB hk hno
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw_oob : n + (delDead n k C).gates.length ≤ w
    · have hlen' : ((delDead n k C).gates.foldl (evalStep d0 evalG) init).length =
          n + (delDead n k C).gates.length := by
        rw [foldl_evalStep_length, hinit]
      have hlen : (C.gates.foldl (evalStep d0 evalG) init).length = n + C.gates.length := by
        rw [foldl_evalStep_length, hinit]
      have hdl := delDead_length n k C hk
      have huw : n + C.gates.length ≤ unshiftW n k w := by
        unfold unshiftW; split_ifs <;> omega
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
    · push Not at hw_oob
      by_cases hwn : w < n
      · have huw : unshiftW n k w = w := by unfold unshiftW; split_ifs <;> omega
        rw [huw]
        rw [foldl_evalStep_prefix d0 evalG (delDead n k C).gates init w (by omega)]
        rw [foldl_evalStep_prefix d0 evalG C.gates init w (by omega)]
      · set j := w - n with hj_def
        have hw_eq : w = n + j := by omega
        have hj_lt : j < (delDead n k C).gates.length := by omega
        have hdl := delDead_length n k C hk
        have hj0_lt : unshiftG k j < C.gates.length := by
          unfold unshiftG; split_ifs <;> omega
        have huw : unshiftW n k (n + j) = n + unshiftG k j := by
          unfold unshiftW unshiftG; split_ifs <;> omega
        rw [hw_eq, huw]
        rw [foldl_evalStep_gate d0 evalG n (delDead n k C) init hinit hRB' j hj_lt]
        rw [foldl_evalStep_gate d0 evalG n C init hinit hRB (unshiftG k j) hj0_lt]
        rw [delDead_gateAt n k C hk j hj_lt]
        simp only [shiftGate, List.map_map]
        congr 1
        apply List.map_congr_left
        intro u hu
        have hu_lt : shiftW n k u < n + j := by
          have hmem : shiftW n k u ∈ (gateAt (delDead n k C) j).inputs := by
            rw [delDead_gateAt n k C hk j hj_lt]
            simp only [shiftGate, List.mem_map]
            exact ⟨u, hu, rfl⟩
          exact hRB' j hj_lt (shiftW n k u) hmem
        have hu_ne : u ≠ n + k := fun heq => hno (unshiftG k j) hj0_lt (heq ▸ hu)
        simp only [Function.comp_apply]
        rw [ih (shiftW n k u) (by omega), unshiftW_shiftW n k u hu_ne]

lemma delDead_wires_eq (n k : ℕ) (C : Circuit) (l : List Bool) (hl : l.length = n)
    (hRB : ReadsBack n C) (hk : k < C.gates.length)
    (hno : ∀ j < C.gates.length, n + k ∉ (gateAt C j).inputs) (w : ℕ) :
    ((delDead n k C).wires l).getD w false = (C.wires l).getD (unshiftW n k w) false :=
  delDead_evalStep_eq false GateOp.eval n k C l hl hRB hk hno w

private lemma delDead_ao2 {n k : ℕ} {C : Circuit} (h : IsAO2 n C)
    (hk : k < C.gates.length)
    (hno : ∀ j < C.gates.length, n + k ∉ (gateAt C j).inputs) :
    IsAO2 n (delDead n k C) := by
  have mapped : ∀ g ∈ (delDead n k C).gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
    intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    have hm := List.mem_of_mem_eraseIdx hg'
    exact ⟨h.1 g' hm, by simp [shiftGate, h.2.2 g' hm]⟩
  exact ⟨fun g hg => (mapped g hg).1, delDead_readsBack n k C h.2.1 hk hno,
    fun g hg => (mapped g hg).2⟩

private def IsSmallest (n : ℕ) (C : Circuit) : Prop :=
  ∀ D : Circuit, IsAO2 n D → circuitFun n D = circuitFun n C → C.size ≤ D.size

private lemma reader {n k : ℕ} {C : Circuit} (h : IsAO2 n C) (hmin : IsSmallest n C)
    (hk : k < C.gates.length) (hout : C.output ≠ n + k) :
    ∃ j < C.gates.length, n + k ∈ (gateAt C j).inputs := by
  by_contra hnot
  have hno : ∀ j < C.gates.length, n + k ∉ (gateAt C j).inputs :=
    fun j hj hj' => hnot ⟨j, hj, hj'⟩
  have heq : circuitFun n (delDead n k C) = circuitFun n C := by
    funext x
    unfold circuitFun Circuit.eval
    rw [delDead_wires_eq n k C _ List.length_ofFn h.2.1 hk hno]
    change (C.wires (List.ofFn x)).getD (unshiftW n k (shiftW n k C.output)) false = _
    rw [unshiftW_shiftW n k C.output hout]
  have hle := hmin _ (delDead_ao2 h hk hno) heq
  have hsize := delDead_size n k C hk
  omega

def OrStep (n : ℕ) (C : Circuit) (w w' : ℕ) : Prop :=
  ∃ k, k < C.gates.length ∧ w = n + k ∧ (gateAt C k).op = GateOp.or ∧
    w' ∈ (gateAt C k).inputs ∧ w' < n + k

lemma orStep_up {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') (hv : val C x w' = true) :
    val C x w = true := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hv
  | head hstep _ ih =>
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (val_or hx hk hop).mpr ⟨_, hin, hlt, ih⟩

lemma or_trace {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) :
    ∀ w : ℕ, val C x w = true →
      ∃ w', Relation.ReflTransGen (OrStep n C) w w' ∧ val C x w' = true ∧
        (w' < n ∨ ∃ h, h < C.gates.length ∧ w' = n + h ∧ (gateAt C h).op ≠ GateOp.or) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < n
    · exact ⟨w, Relation.ReflTransGen.refl, hv, Or.inl hw⟩
    · by_cases hlen : n + C.gates.length ≤ w
      · rw [val_ge hx hlen] at hv; cases hv
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        by_cases hop : (gateAt C k).op = GateOp.or
        · obtain ⟨i, hin, hlt, hi⟩ := (val_or hx hk hop).mp hv
          obtain ⟨w', hr, hv', hw'⟩ := ih i hlt hi
          exact ⟨w', Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hin, hlt⟩ hr, hv', hw'⟩
        · exact ⟨n + k, Relation.ReflTransGen.refl, hv, Or.inr ⟨k, hk, rfl, hop⟩⟩

lemma pairInput_left {n : ℕ} (u v : Fin n) : pairInput u v u = true := by
  simp [pairInput]

lemma pairInput_right {n : ℕ} (u v : Fin n) : pairInput u v v = true := by
  simp [pairInput]

lemma pairInput_true {n : ℕ} (u v w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by
  simp [pairInput]

lemma graphFun_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq, pairInput_true]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  · intro h
    exact ⟨u, v, h, Or.inl rfl, Or.inr rfl⟩
lemma operand_trace {n : ℕ} {C : Circuit} (u v : Fin n) (p : ℕ)
    (hv : val C (List.ofFn (pairInput u v)) p = true) :
    (∃ t : Fin n, (t = u ∨ t = v) ∧ Relation.ReflTransGen (OrStep n C) p t.val) ∨
    (∃ h, h < C.gates.length ∧ (gateAt C h).op ≠ GateOp.or ∧
      Relation.ReflTransGen (OrStep n C) p (n + h) ∧
      val C (List.ofFn (pairInput u v)) (n + h) = true) := by
  obtain ⟨w', hr, hv', hw'⟩ := or_trace (n := n) (C := C) (x := List.ofFn (pairInput u v))
    (by simp) p hv
  rcases hw' with hlt | ⟨h, hh, rfl, hop⟩
  · left
    refine ⟨⟨w', hlt⟩, ?_, hr⟩
    have h1 := val_ofFn C (pairInput u v) ⟨w', hlt⟩
    rw [show (⟨w', hlt⟩ : Fin n).val = w' from rfl, hv'] at h1
    exact (pairInput_true u v _).mp h1.symm
  · right
    exact ⟨h, hh, hop, hr, hv'⟩

lemma reach_var_val {n : ℕ} {C : Circuit} (x : Fin n → Bool) (p : ℕ) (t : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p t.val) (ht : x t = true) :
    val C (List.ofFn x) p = true :=
  orStep_up (n := n) (by simp) hr (by rw [val_ofFn]; exact ht)
lemma edge_trace {n : ℕ} (G : SimpleGraph (Fin n)) {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hF : ∀ u v : Fin n, F (pairInput u v) = true → G.Adj u v)
    (hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = F x)
    (u v : Fin n) (huv : F (pairInput u v) = true) :
    ∃ a, a < C.gates.length ∧ (gateAt C a).op ≠ GateOp.or ∧
      Relation.ReflTransGen (OrStep n C) C.output (n + a) ∧
      val C (List.ofFn (pairInput u v)) (n + a) = true := by
  rcases operand_trace (C := C) u v C.output (by rw [hout]; exact huv) with
    ⟨t, _, hr⟩ | h
  · exfalso
    have h1 := reach_var_val (pairInput t t) _ t hr (pairInput_left t t)
    rw [hout] at h1
    exact G.irrefl (hF t t h1)
  · exact h

lemma below_of_reach {n : ℕ} {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = F x) (a : ℕ)
    (hr : Relation.ReflTransGen (OrStep n C) C.output (n + a)) (x : Fin n → Bool)
    (hv : val C (List.ofFn x) (n + a) = true) : F x = true := by
  rw [← hout]
  exact orStep_up (n := n) (by simp) hr hv
lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

lemma orStep_le {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') : w' ≤ w := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact le_rfl
  | head hstep _ ih =>
    obtain ⟨k, _, rfl, _, _, hlt⟩ := hstep
    omega

lemma orStep_cone {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') :
    ∀ k h', w = n + k → w' = n + h' → h' = k ∨ InCone n C h' k := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => intro k h' h1 h2; left; omega
  | @head a c hstep hrest ih =>
    intro k h' h1 h2
    obtain ⟨k0, hk0, e, _, hin, hlt⟩ := hstep
    have hk : k0 = k := by omega
    subst hk
    have hle := orStep_le hrest
    obtain ⟨k1, hk1⟩ : ∃ k1, c = n + k1 := ⟨c - n, by omega⟩
    subst hk1
    right
    rw [inCone_iff]
    exact ⟨hk0, k1, by omega, hin, ih k1 h' rfl h2⟩

lemma operand_cone {n : ℕ} {C : Circuit} {a p h : ℕ} (ha : a < C.gates.length)
    (hin : p ∈ (gateAt C a).inputs) (hp : p < n + a)
    (hr : Relation.ReflTransGen (OrStep n C) p (n + h)) : InCone n C h a := by
  have hle := orStep_le hr
  obtain ⟨k1, rfl⟩ : ∃ k1, p = n + k1 := ⟨p - n, by omega⟩
  rw [inCone_iff]
  exact ⟨ha, k1, by omega, hin, orStep_cone hr k1 h rfl rfl⟩
lemma orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (orStep n) []).length = gs.length := by
      rw [orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (orStep n (gs.foldl (orStep n) []) g).getD k [] =
          (gs.foldl (orStep n) []).getD k [] := by
      intro k hk
      simp only [orStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, h3⟩
        refine ⟨by simp; omega, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
      · rintro ⟨_, h3⟩
        refine ⟨h, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · rw [key (w - n) (by omega)] at h3
          exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      by_cases hop : g.op = GateOp.or
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
          · exact ⟨by simp, Or.inl h3⟩
          · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_singleton]
        constructor
        · intro h3
          exact ⟨by simp, Or.inl h3⟩
        · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
          · exact h3
          · exact (hop hop2).elim
    · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
        simp only [orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
  have h := orSets_char n C.gates g k
  unfold OrReaches orSets gateAt
  have e : n + k - n = k := by omega
  rw [e, h]
  constructor
  · rintro ⟨_, hk, h3⟩
    refine ⟨hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
  · rintro ⟨hk, h3⟩
    refine ⟨by omega, hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩

lemma reach_orReaches {n : ℕ} {C : Circuit} {w w2 : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w2) :
    ∀ g, w2 = n + g → g < C.gates.length → OrReaches n C w g := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro g h1 hg
    subst h1
    exact (orReaches_iff n C g g).mpr ⟨hg, Or.inl rfl⟩
  | @head a c hstep hrest ih =>
    intro g h1 hg
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (orReaches_iff n C k g).mpr ⟨hk, Or.inr ⟨hop, c, hin, hlt, ih g h1 hg⟩⟩

lemma orReaches_reach {n : ℕ} {C : Circuit} (g : ℕ) :
    ∀ w, OrReaches n C w g →
      Relation.ReflTransGen (OrStep n C) w (n + g) ∧ g < C.gates.length := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    have hnw : n ≤ w := h.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k g).mp h
    rcases h3 with rfl | ⟨hop, i, hi, hlt, hr⟩
    · exact ⟨Relation.ReflTransGen.refl, hk⟩
    · obtain ⟨hr2, hg⟩ := ih i hlt hr
      exact ⟨Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hi, hlt⟩ hr2, hg⟩

lemma mem_orIn_reach {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hu : u ∈ PEqualNP.TopForm.orIn n C p) :
    Relation.ReflTransGen (OrStep n C) p u.val := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  rcases hu with h | ⟨k, hk, hr, hop, hin⟩
  · rw [h]
  · exact (orReaches_reach k p hr).1.tail ⟨k, hk, rfl, hop, hin, by omega⟩

lemma reach_mem_orIn {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p u.val) :
    u ∈ PEqualNP.TopForm.orIn n C p := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases Relation.ReflTransGen.cases_tail hr with h | ⟨c, hpc, hstep⟩
  · exact Or.inl h
  · obtain ⟨k, hk, rfl, hop, hin, _⟩ := hstep
    exact Or.inr ⟨k, hk, reach_orReaches hpc k rfl hk, hop, hin⟩

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

theorem topData {a : ℕ} (ha : a ∈ tops G C) :
    a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧ BelowF G C a := by
  simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using ha
theorem junkData {a : ℕ} (ha : a ∈ junk G C) :
    a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧
      ∃ x : Fin n → Bool, gateVal n C a x = true ∧ graphFun G ∅ x = false := by
  rcases Finset.mem_filter.mp ha with ⟨hr, hop, hal, hd⟩
  exact ⟨hal, hop, hd⟩
theorem binaryInputs (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) :
    ∃ p q, (gateAt C a).inputs = [p, q] :=
  List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem ha))
theorem opndMem (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
    opnd C a b ∈ (gateAt C a).inputs := by
  obtain ⟨p, q, hpq⟩ := binaryInputs hAO ha
  fin_cases b <;> simp [opnd, hpq]
theorem opndBound (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
    opnd C a b < n + a :=
  hAO.2.1 a ha _ (opndMem hAO ha b)
theorem andValBoth (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and) (x : Fin n → Bool) :
    gateVal n C a x = true ↔
      val C (List.ofFn x) (opnd C a 0) = true ∧
      val C (List.ofFn x) (opnd C a 1) = true := by
  rw [gateVal_eq_val, val_and (n := n) (by simp) ha hop]
  constructor
  · intro h
    exact ⟨(h _ (opndMem hAO ha 0)).2, (h _ (opndMem hAO ha 1)).2⟩
  · intro h i hi
    refine ⟨hAO.2.1 a ha i hi, ?_⟩
    obtain ⟨p, q, hpq⟩ := binaryInputs hAO ha
    rcases List.mem_cons.mp (hpq ▸ hi) with rfl | hq
    · simpa [opnd, hpq] using h.1
    · have e : i = q := List.mem_singleton.mp hq
      subst i
      simpa [opnd, hpq] using h.2
theorem andValOperands (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and) (x : Fin n → Bool) :
    gateVal n C a x = true ↔ ∀ b : Fin 2, val C (List.ofFn x) (opnd C a b) = true := by
  rw [andValBoth hAO ha hop]
  constructor
  · intro h b
    fin_cases b
    · exact h.1
    · exact h.2
  · intro h
    exact ⟨h 0, h 1⟩
theorem operandReachCone (hAO : IsAO2 n C) {a h : ℕ} (ha : a < C.gates.length)
    {b : Fin 2} (hr : OrReaches n C (opnd C a b) h) :
    InCone n C h a :=
  operand_cone ha (opndMem hAO ha b) (opndBound hAO ha b)
    (orReaches_reach h _ hr).1
theorem operandOrAndJunk (hAO : IsAO2 n C) (hT : TopForm G C) {a h : ℕ}
    (ha : a < C.gates.length) (hop : (gateAt C a).op = GateOp.and)
    {b : Fin 2} (hr : OrReaches n C (opnd C a b) h)
    (hh : (gateAt C h).op = GateOp.and) : h ∈ junk G C := by
  have hlen := (orReaches_reach h _ hr).2
  have hnb : ¬ BelowF G C h :=
    fun hb => hT h hlen a ha hh hb hop (operandReachCone hAO ha hr)
  have hdirty : ∃ x : Fin n → Bool, gateVal n C h x = true ∧ graphFun G ∅ x = false := by
    by_contra hne
    apply hnb
    intro x hx
    by_contra hf
    exact hne ⟨x, hx, Bool.eq_false_iff.mpr hf⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlen, hh, hlen, hdirty⟩
theorem inputsAsOpnd (hAO : IsAO2 n C) {m z : ℕ} (hm : m < C.gates.length)
    (hz : z ∈ (gateAt C m).inputs) : ∃ b : Fin 2, z = opnd C m b := by
  obtain ⟨p, q, hpq⟩ := binaryInputs hAO hm
  rcases List.mem_cons.mp (hpq ▸ hz) with rfl | hq
  · exact ⟨0, by simp [opnd, hpq]⟩
  · have e : z = q := List.mem_singleton.mp hq
    exact ⟨1, by simpa [opnd, hpq] using e⟩
lemma sideVal {a : ℕ} {b : Fin 2} {x : Fin n → Bool} {t : Fin n}
    (ht : t ∈ side (n := n) C a b) (hx : x t = true) :
    val C (List.ofFn x) (opnd C a b) = true :=
  reach_var_val x _ t (mem_orIn_reach t ht) hx

lemma andFromInputs (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and) {x : Fin n → Bool}
    {u v : Fin n} (hu : u ∈ side (n := n) C a 0) (hv : v ∈ side (n := n) C a 1)
    (xu : x u = true) (xv : x v = true) : gateVal n C a x = true :=
  (andValBoth hAO ha hop x).mpr ⟨sideVal hu xu, sideVal hv xv⟩

lemma topAdj (hAO : IsAO2 n C) {a : ℕ} (ha : a ∈ tops G C)
    {u v : Fin n} (hu : u ∈ side (n := n) C a 0) (hv : v ∈ side (n := n) C a 1) :
    G.Adj u v := by
  obtain ⟨hl, ho, hb⟩ := topData ha
  exact (graphFun_pair G u v).mp
    (hb _ (andFromInputs hAO hl ho hu hv (pairInput_left u v) (pairInput_right u v)))

lemma acceptedTop (hL : IsLeastAO G C) {u v : Fin n} (hadj : G.Adj u v) :
    ∃ a ∈ tops G C, gateVal n C a (pairInput u v) = true := by
  have hout (x : Fin n → Bool) : val C (List.ofFn x) C.output = graphFun G ∅ x :=
    congrFun hL.2.1 x
  obtain ⟨a, hl, ho, hr, hv⟩ :=
    edge_trace G (graphFun G ∅) (fun k l => (graphFun_pair G k l).mp)
      hout u v ((graphFun_pair G u v).mpr hadj)
  have hand := (hL.1.1 _ (gateAt_mem hl)).resolve_right ho
  have hb : BelowF G C a := fun x hx =>
    below_of_reach (graphFun G ∅) hout a hr x (gateVal_eq_val n C a x ▸ hx)
  refine ⟨a, ?_, hv⟩
  simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using
    And.intro hl (And.intro hand hb)

lemma operandSupport (hAO : IsAO2 n C) (hT : TopForm G C) {a : ℕ}
    (ha : a < C.gates.length) (ho : (gateAt C a).op = GateOp.and) {b : Fin 2}
    {u v : Fin n} (h : val C (List.ofFn (pairInput u v)) (opnd C a b) = true) :
    (∃ t ∈ side (n := n) C a b, t = u ∨ t = v) ∨
      ∃ j ∈ junk G C, OrReaches n C (opnd C a b) j ∧
        gateVal n C j (pairInput u v) = true := by
  rcases operand_trace (C := C) u v _ h with ⟨t, ht, hr⟩ | ⟨j, hj, hn, hr, hv⟩
  · exact .inl ⟨t, reach_mem_orIn t hr, ht⟩
  · have hr' := reach_orReaches hr j rfl hj
    exact .inr ⟨j, operandOrAndJunk hAO hT ha ho hr'
      ((hAO.1 _ (gateAt_mem hj)).resolve_right hn), hr', hv⟩


lemma andRawEmpty {j : ℕ} (hj : (gateAt C j).op = GateOp.and) :
    orIn n C (n + j) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hv
  rcases hv with he | ⟨k, _, hr, ho, _⟩
  · have := v.isLt
    omega
  · rcases (orReaches_iff n C j k).mp hr with ⟨_, he | ⟨hof, _⟩⟩
    · subst k
      rw [hj] at ho
      cases ho
    · rw [hj] at hof
      cases hof

lemma lastOrBefore {j w : ℕ} (hr : Relation.ReflTransGen (OrStep n C) w (n + j)) :
    w = n + j ∨ ∃ m, m < C.gates.length ∧ (gateAt C m).op = GateOp.or ∧
      n + j ∈ (gateAt C m).inputs ∧ n + j < n + m ∧
      Relation.ReflTransGen (OrStep n C) w (n + m) := by
  rcases Relation.ReflTransGen.cases_tail hr with eq | ⟨z, hz, hstep⟩
  · exact .inl eq.symm
  · obtain ⟨m, hm, rfl, ho, hi, hb⟩ := hstep
    exact .inr ⟨m, hm, ho, hi, hb, hz⟩

lemma residualTrace (hL : IsLeastAO G C) (hT : TopForm G C) {u v : Fin n}
    (he : s(u,v) ∈ Ustar G C) :
    ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ j ∈ junk G C,
      OrReaches n C (opnd C a b) j ∧ gateVal n C j (pairInput u v) = true := by
  obtain ⟨adj, miss⟩ := Finset.mem_sdiff.mp he
  have adj' : G.Adj u v := SimpleGraph.mem_edgeFinset.mp adj
  obtain ⟨a, ha, hv⟩ := acceptedTop hL adj'
  obtain ⟨hl, ho, _⟩ := topData ha
  have h := (andValOperands hL.1 hl ho _).mp hv
  rcases operandSupport hL.1 hT hl ho (b := 0) (h 0) with ⟨x, hx, hex⟩ | ⟨j, hj, hr, hjv⟩
  · rcases operandSupport hL.1 hT hl ho (b := 1) (h 1) with ⟨y, hy, hey⟩ | ⟨j, hj, hr, hjv⟩
    · have hxy : x ≠ y := (topAdj hL.1 ha hx hy).ne
      apply (miss ?_).elim
      unfold starEdges
      refine Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image.mpr
        ⟨(x,y), Finset.mem_product.mpr ⟨hx,hy⟩, ?_⟩⟩
      rcases hex with rfl | rfl <;> rcases hey with rfl | rfl
      · exact (hxy rfl).elim
      · rfl
      · exact Sym2.eq_swap
      · exact (hxy rfl).elim
    · exact ⟨a, ha, 1, j, hj, hr, hjv⟩
  · exact ⟨a, ha, 0, j, hj, hr, hjv⟩

lemma readData {j k : ℕ} (h : k ∈ readers n C j) :
    k < C.gates.length ∧ n + j ∈ (gateAt C k).inputs := by
  simpa only [readers, Finset.mem_filter, Finset.mem_range] using h

lemma readLt (hAO : IsAO2 n C) {j k : ℕ} (h : k ∈ readers n C j) : j < k := by
  have hlt := hAO.2.1 k (readData h).1 _ (readData h).2
  omega

lemma junkNotBelow {j : ℕ} (hj : j ∈ junk G C) : ¬ BelowF G C j := by
  obtain ⟨_, _, x, hx, hf⟩ := junkData hj
  intro h
  exact Bool.false_ne_true (hf.symm.trans (h x hx))

lemma leastRead (hL : IsLeastAO G C) {j : ℕ} (hj : j < C.gates.length)
    (hd : ¬ BelowF G C j) : (readers n C j).Nonempty := by
  have hout : C.output ≠ n + j := by
    intro heq
    apply hd
    intro x hx
    have h : val C (List.ofFn x) C.output = graphFun G ∅ x := congrFun hL.2.1 x
    rw [heq] at h
    exact h.symm.trans hx
  obtain ⟨k, hk, hin⟩ := reader hL.1
    (fun D hD heq => hL.2.2 D hD (heq.trans hL.2.1)) hj hout
  exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hin⟩⟩

lemma emptySide {a : ℕ} (ha : a ∈ tops G C) {b : Fin 2}
    (h : side (n := n) C a b = ∅) : a ∈ centreless G C := by
  apply Finset.mem_filter.mpr
  refine ⟨ha, ?_⟩
  fin_cases b
  · exact Or.inl h
  · exact Or.inr h

-- A reader of a dirty gate with no input in its OR closure consumes one of the two budgets.
lemma classifyReader (hAO : IsAO2 n C) (hE : centreless G C = ∅) {j k : ℕ}
    (hd : ¬ BelowF G C j) (hz : orIn n C (n + j) = ∅) (hr : k ∈ readers n C j) :
    k ∈ junk G C ∨ k ∈ orN G C \ lam G C := by
  obtain ⟨hk, hin⟩ := readData hr
  obtain ⟨b, hb⟩ := inputsAsOpnd hAO hk hin
  have hs : side (n := n) C k b = ∅ := by
    change orIn n C (opnd C k b) = ∅
    rwa [← hb]
  rcases hAO.1 _ (gateAt_mem hk) with hand | hor
  · left
    have hnb : ¬ BelowF G C k := by
      intro hbelow
      have ht : k ∈ tops G C := by
        simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using
          And.intro hk (And.intro hand hbelow)
      have hcen := emptySide ht hs
      rw [hE] at hcen
      exact Finset.notMem_empty _ hcen
    have hw : ∃ x : Fin n → Bool, gateVal n C k x = true ∧ graphFun G ∅ x = false := by
      by_contra hnone
      apply hnb
      intro x hx
      by_contra hf
      exact hnone ⟨x, hx, Bool.eq_false_iff.mpr hf⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hand, hk, hw⟩
  · right
    have hnb : ¬ BelowF G C k := by
      intro hbelow
      apply hd
      intro x hx
      exact hbelow x ((val_or (n := n) (by simp) hk hor).mpr
        ⟨_, hin, hAO.2.1 k hk _ hin, hx⟩)
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · simpa only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] using
        And.intro hk (And.intro hor hnb)
    · intro hlam
      obtain ⟨_, h0, h1, _⟩ := Finset.mem_filter.mp hlam
      have hn : (orIn n C (opnd C k b)).Nonempty := by
        fin_cases b
        · exact h0
        · exact h1
      rw [← hb, hz] at hn
      exact Finset.not_nonempty_empty hn

lemma orEmpty {m : ℕ} (h : ∀ w ∈ (gateAt C m).inputs, orIn n C w = ∅) :
    orIn n C (n + m) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u hu
  rcases Relation.ReflTransGen.cases_head (mem_orIn_reach u hu) with he | ⟨w, hw, tail⟩
  · have := u.isLt
    omega
  · obtain ⟨k, _, he, _, hi, _⟩ := hw
    have e : k = m := by omega
    subst k
    have hu' := reach_mem_orIn u tail
    rw [h w hi] at hu'
    exact Finset.notMem_empty _ hu'

lemma twoInputs (hAO : IsAO2 n C) {m p q : ℕ} (hm : m < C.gates.length)
    (hpq : p ≠ q) (hp : p ∈ (gateAt C m).inputs) (hq : q ∈ (gateAt C m).inputs)
    {w : ℕ} (hw : w ∈ (gateAt C m).inputs) : w = p ∨ w = q := by
  obtain ⟨r, s, hrs⟩ := binaryInputs hAO hm
  simp only [hrs, List.mem_cons, List.not_mem_nil, or_false] at hp hq hw
  omega

lemma dichotomy (hL : IsLeastAO G C) (hT : TopForm G C) (hJ : (junk G C).card = 2) :
    2 ≤ 2 * (centreless G C).card + (orN G C \ lam G C).card ∨
      ∃ a b m : ℕ, junk G C = {a, b} ∧ InCone n C a b ∧ centreless G C = ∅ ∧
        readers n C a = {b} ∧ readers n C b = {m} ∧ orN G C \ lam G C = {m} ∧
        ∀ u v : Fin n, s(u, v) ∈ Ustar G C →
          gateVal n C a (pairInput u v) = true ∧ gateVal n C b (pairInput u v) = true := by
  by_cases h : 2 ≤ 2 * (centreless G C).card + (orN G C \ lam G C).card
  · exact Or.inl h
  right
  have hE : centreless G C = ∅ := Finset.card_eq_zero.mp (by omega)
  have hSmall : (orN G C \ lam G C).card ≤ 1 := by omega
  obtain ⟨a, b, hab, hPair⟩ : ∃ a b : ℕ, a < b ∧ junk G C = {a, b} := by
    obtain ⟨i, j, hij, he⟩ := Finset.card_eq_two.mp hJ
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · exact ⟨i, j, hlt, he⟩
    · exact ⟨j, i, hlt, he.trans (Finset.pair_comm _ _)⟩
  have ha : a ∈ junk G C := by simp [hPair]
  have hb : b ∈ junk G C := by simp [hPair]
  have noLaterJunk {k : ℕ} (hk : k ∈ junk G C) (hlt : b < k) : False := by
    simp only [hPair, Finset.mem_insert, Finset.mem_singleton] at hk
    omega
  have junkReader {j k : ℕ} (hj : j ∈ junk G C) (hr : k ∈ readers n C j) :
      k ∈ junk G C ∨ k ∈ orN G C \ lam G C :=
    classifyReader hL.1 hE (junkNotBelow hj) (andRawEmpty (junkData hj).2.1) hr
  obtain ⟨m, hbm⟩ := leastRead hL (junkData hb).1 (junkNotBelow hb)
  have hbmLt := readLt hL.1 hbm
  have hm := (junkReader hb hbm).resolve_left (fun hk => noLaterJunk hk hbmLt)
  have mUnique {k : ℕ} (hk : k ∈ orN G C \ lam G C) : k = m :=
    Finset.card_le_one.mp hSmall k hk m hm
  have hM : orN G C \ lam G C = {m} := by
    ext k
    exact ⟨fun hk => Finset.mem_singleton.mpr (mUnique hk),
      fun hk => Finset.mem_singleton.mp hk ▸ hm⟩
  have hB : readers n C b = {m} := by
    ext k
    refine ⟨fun hk => Finset.mem_singleton.mpr (mUnique ?_),
      fun hk => Finset.mem_singleton.mp hk ▸ hbm⟩
    exact (junkReader hb hk).resolve_left (fun hj => noLaterJunk hj (readLt hL.1 hk))
  have noAM (ham : m ∈ readers n C a) : False := by
    have hmData : m < C.gates.length ∧ (gateAt C m).op = GateOp.or ∧ ¬ BelowF G C m := by
      simpa only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] using (Finset.mem_sdiff.mp hm).1
    have hmEmpty : orIn n C (n + m) = ∅ := by
      apply orEmpty
      intro w hw
      rcases twoInputs hL.1 hmData.1 (show n + a ≠ n + b by omega)
          (readData ham).2 (readData hbm).2 hw with rfl | rfl
      · exact andRawEmpty (junkData ha).2.1
      · exact andRawEmpty (junkData hb).2.1
    obtain ⟨k, hmk⟩ := leastRead hL hmData.1 hmData.2.2
    have hmkLt := readLt hL.1 hmk
    rcases classifyReader hL.1 hE hmData.2.2 hmEmpty hmk with hk | hk
    · exact noLaterJunk hk (hbmLt.trans hmkLt)
    · have := mUnique hk
      omega
  have aRead {k : ℕ} (hk : k ∈ readers n C a) : k = b := by
    rcases junkReader ha hk with hj | hj
    · have hlt := readLt hL.1 hk
      simp only [hPair, Finset.mem_insert, Finset.mem_singleton] at hj
      omega
    · exact (noAM (mUnique hj ▸ hk)).elim
  obtain ⟨k, hak⟩ := leastRead hL (junkData ha).1 (junkNotBelow ha)
  have habRead : b ∈ readers n C a := aRead hak ▸ hak
  have hA : readers n C a = {b} := by
    ext i
    exact ⟨fun hi => Finset.mem_singleton.mpr (aRead hi),
      fun hi => Finset.mem_singleton.mp hi ▸ habRead⟩
  have habCone : InCone n C a b := (inCone_iff n C a b).mpr
    ⟨(readData habRead).1, a, hab, (readData habRead).2, Or.inl rfl⟩
  refine ⟨a, b, m, hPair, habCone, hE, hA, hB, hM, ?_⟩
  intro u v he
  obtain ⟨t, ht, d, j, hj, path, hv⟩ := residualTrace hL hT he
  have hjb : j = b := by
    simp only [hPair, Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with h | h
    · exfalso
      subst j
      rcases lastOrBefore (orReaches_reach a _ path).1 with heq | ⟨r, hr, hop, hin, _, _⟩
      · have hs : side (n := n) C t d = ∅ := by
          change orIn n C (opnd C t d) = ∅
          rw [heq]
          exact andRawEmpty (junkData ha).2.1
        have hbad := emptySide ht hs
        rw [hE] at hbad
        exact Finset.notMem_empty _ hbad
      · have hr' : r ∈ readers n C a := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hr, hin⟩
        rw [aRead hr', (junkData hb).2.1] at hop
        cases hop
    · exact h
  subst j
  have haVal := (val_and (n := n) (by simp) (junkData hb).1 (junkData hb).2.1).mp hv
    (n + a) (readData habRead).2
  exact ⟨haVal.2, hv⟩

end PEqualNP.Outside.L_meta_5012.Structural

namespace PEqualNP.Outside.L_meta_5012.Trace

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open PEqualNP.Outside.L_meta_5012.Structural
open PEqualNP.Outside.L_meta_5012

def cut (C : Circuit) (h : ℕ) : Circuit :=
  { C with gates := C.gates.set h ⟨GateOp.or, []⟩ }

lemma cut_len (C : Circuit) (h : ℕ) : (cut C h).gates.length = C.gates.length := by
  simp [cut]

lemma cut_gate_same (C : Circuit) (h j : ℕ) (hne : j ≠ h) :
    gateAt (cut C h) j = gateAt C j := by
  simp [cut, gateAt, List.getD_eq_getElem?_getD, hne.symm]

lemma cut_gate_zero (C : Circuit) (h : ℕ) (hh : h < C.gates.length) :
    gateAt (cut C h) h = ⟨GateOp.or, []⟩ := by
  simp [cut, gateAt, List.getD_eq_getElem?_getD, hh]

lemma cut_h_false {n : ℕ} (C : Circuit) (h : ℕ) (hh : h < C.gates.length)
    (x : Fin n → Bool) : gateVal n (cut C h) h x = false := by
  rw [gateVal_eq_val, val_gate (n := n) (by simp) (by simpa [cut_len] using hh), cut_gate_zero C h hh]
  rfl

lemma cut_orStep {n : ℕ} (C : Circuit) (h : ℕ)
    (hhop : (gateAt C h).op = GateOp.and) (w w' : ℕ) :
    OrStep n (cut C h) w w' ↔ OrStep n C w w' := by
  constructor
  · rintro ⟨j, hj, hw, ho, hin, hlt⟩
    have hjC : j < C.gates.length := by simpa [cut_len] using hj
    have hjh : j ≠ h := by
      intro heq
      subst j
      rw [cut_gate_zero C h hjC] at hin
      exact List.not_mem_nil hin
    rw [cut_gate_same C h j hjh] at ho hin
    exact ⟨j, hjC, hw, ho, hin, hlt⟩
  · rintro ⟨j, hj, hw, ho, hin, hlt⟩
    have hjh : j ≠ h := by
      intro heq
      subst j
      rw [hhop] at ho
      cases ho
    refine ⟨j, by simpa [cut_len] using hj, hw, ?_, ?_, hlt⟩
    · rwa [cut_gate_same C h j hjh]
    · rwa [cut_gate_same C h j hjh]

lemma cut_orPath {n : ℕ} (C : Circuit) (h : ℕ)
    (hhop : (gateAt C h).op = GateOp.and) (w w' : ℕ) :
    Relation.ReflTransGen (OrStep n (cut C h)) w w' ↔
      Relation.ReflTransGen (OrStep n C) w w' := by
  constructor
  · intro hpath
    induction hpath using Relation.ReflTransGen.head_induction_on with
    | refl => exact .refl
    | head hs _ ih => exact .head ((cut_orStep C h hhop _ _).mp hs) ih
  · intro hpath
    induction hpath using Relation.ReflTransGen.head_induction_on with
    | refl => exact .refl
    | head hs _ ih => exact .head ((cut_orStep C h hhop _ _).mpr hs) ih

lemma top_no_inner_reach {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g h : ℕ) (_hAO : IsAO2 n C)
    (hcen : centreless G C = ∅) (hg : g ∈ junk G C) (hh : h ∈ junk G C)
    (hread : readers n C g = {h}) {a : ℕ} (ha : a ∈ tops G C) (b : Fin 2) :
    ¬ OrReaches n C (opnd C a b) g := by
  intro hpath
  rcases lastOrBefore (orReaches_reach g _ hpath).1 with heq | ⟨j, hj, ho, hin, _, _⟩
  · have hside : side (n := n) C a b = ∅ := by
      change orIn n C (opnd C a b) = ∅
      rw [heq]
      exact andRawEmpty (junkData hg).2.1
    have hbad := emptySide ha hside
    rw [hcen] at hbad
    exact Finset.notMem_empty _ hbad
  · have hreader : j ∈ readers n C g :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hin⟩
    rw [hread, Finset.mem_singleton] at hreader
    subst j
    rw [(junkData hh).2.1] at ho
    cases ho

lemma top_operand_raw_outer {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g h : ℕ) (hAO : IsAO2 n C) (hT : TopForm G C)
    (hcen : centreless G C = ∅) (hJ : junk G C = {g, h})
    (hread : readers n C g = {h}) {a : ℕ} (ha : a ∈ tops G C)
    (b : Fin 2) (x : Fin n → Bool) :
    val C (List.ofFn x) (opnd C a b) = true ↔
      setOr (side (n := n) C a b) x = true ∨
      OrReaches n C (opnd C a b) h ∧ gateVal n C h x = true := by
  have hg : g ∈ junk G C := by simp [hJ]
  have hh : h ∈ junk G C := by simp [hJ]
  constructor
  · intro hv
    obtain ⟨w, hp, hw, hwi | ⟨j, hj, heq, hjo⟩⟩ := or_trace (n := n) (C := C) (by simp) _ hv
    · left
      apply decide_eq_true
      refine ⟨⟨w, hwi⟩, reach_mem_orIn ⟨w, hwi⟩ hp, ?_⟩
      exact (val_ofFn C x ⟨w, hwi⟩).symm.trans hw
    · subst w
      have hor := reach_orReaches hp j rfl hj
      have hand := (hAO.1 _ (gateAt_mem hj)).resolve_right hjo
      have hjunk := operandOrAndJunk hAO hT (topData ha).1 (topData ha).2.1 hor hand
      simp only [hJ, Finset.mem_insert, Finset.mem_singleton] at hjunk
      rcases hjunk with he | he
      · rw [he] at hor
        exact False.elim (top_no_inner_reach G C g h hAO hcen hg hh hread ha b hor)
      · rw [he] at hor hw
        exact Or.inr ⟨hor, hw⟩
  · rintro (hraw | ⟨hp, hhval⟩)
    · obtain ⟨v, hv, hxv⟩ := of_decide_eq_true hraw
      exact sideVal hv hxv
    · exact orStep_up (n := n) (by simp) (orReaches_reach h _ hp).1 hhval

lemma cut_top_operand_raw {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g h : ℕ) (hAO : IsAO2 n C) (hT : TopForm G C)
    (hcen : centreless G C = ∅) (hJ : junk G C = {g, h})
    (hread : readers n C g = {h}) {a : ℕ} (ha : a ∈ tops G C)
    (b : Fin 2) (x : Fin n → Bool) :
    val (cut C h) (List.ofFn x) (opnd C a b) = true ↔
      setOr (side (n := n) C a b) x = true := by
  have hg : g ∈ junk G C := by simp [hJ]
  have hh : h ∈ junk G C := by simp [hJ]
  have hhop := (junkData hh).2.1
  constructor
  · intro hv
    obtain ⟨w, hp, hw, hwi | ⟨j, hj, heq, hjo⟩⟩ :=
      or_trace (n := n) (C := cut C h) (by simp) _ hv
    · apply decide_eq_true
      have hpC := (cut_orPath C h hhop _ _).mp hp
      refine ⟨⟨w, hwi⟩, reach_mem_orIn ⟨w, hwi⟩ hpC, ?_⟩
      exact (val_ofFn (cut C h) x ⟨w, hwi⟩).symm.trans hw
    · subst w
      have hjC : j < C.gates.length := by simpa [cut_len] using hj
      have hjh : j ≠ h := by
        intro he
        subst j
        rw [cut_gate_zero C h hjC] at hjo
        exact hjo rfl
      rw [cut_gate_same C h j hjh] at hjo
      have hor := reach_orReaches ((cut_orPath C h hhop _ _).mp hp) j rfl hjC
      have hand := (hAO.1 _ (gateAt_mem hjC)).resolve_right hjo
      have hjunk := operandOrAndJunk hAO hT (topData ha).1 (topData ha).2.1 hor hand
      simp only [hJ, Finset.mem_insert, Finset.mem_singleton] at hjunk
      rcases hjunk with he | he
      · subst j
        exact False.elim (top_no_inner_reach G C g h hAO hcen hg hh hread ha b hor)
      · exact False.elim (hjh he)
  · intro hraw
    obtain ⟨v, hv, hxv⟩ := of_decide_eq_true hraw
    have hp := (cut_orPath C h hhop _ _).mpr (mem_orIn_reach v hv)
    apply orStep_up (n := n) (by simp) hp
    simpa only [val_ofFn] using hxv

lemma raw_reader_nonempty {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g h m : ℕ) (hL : IsLeastAO G C)
    (hcen : centreless G C = ∅) (hJ : junk G C = {g, h}) (hgh : g < h)
    (hread : readers n C h = {m}) (hbudget : orN G C \ lam G C = {m}) :
    (orIn n C (n + m)).Nonempty := by
  have hmread : m ∈ readers n C h := by simp [hread]
  have hhm := readLt hL.1 hmread
  have hmbudget : m ∈ orN G C \ lam G C := by simp [hbudget]
  have hmdata : m < C.gates.length ∧ (gateAt C m).op = GateOp.or ∧ ¬ BelowF G C m := by
    simpa only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] using
      (Finset.mem_sdiff.mp hmbudget).1
  by_contra hnone
  have hempty := Finset.not_nonempty_iff_eq_empty.mp hnone
  obtain ⟨j, hjread⟩ := leastRead hL hmdata.1 hmdata.2.2
  have hmj := readLt hL.1 hjread
  rcases classifyReader hL.1 hcen hmdata.2.2 hempty hjread with hj | hj
  · simp only [hJ, Finset.mem_insert, Finset.mem_singleton] at hj
    omega
  · rw [hbudget, Finset.mem_singleton] at hj
    omega

lemma top_reach_contains_raw {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h m : ℕ) (hcen : centreless G C = ∅) (hh : h ∈ junk G C)
    (hread : readers n C h = {m}) (r : Fin n) (hr : r ∈ orIn n C (n + m))
    {a : ℕ} (ha : a ∈ tops G C) (b : Fin 2)
    (hpath : OrReaches n C (opnd C a b) h) : r ∈ side (n := n) C a b := by
  rcases lastOrBefore (orReaches_reach h _ hpath).1 with heq | ⟨j, hj, _, hin, _, hp⟩
  · have hside : side (n := n) C a b = ∅ := by
      change orIn n C (opnd C a b) = ∅
      rw [heq]
      exact andRawEmpty (junkData hh).2.1
    have hbad := emptySide ha hside
    rw [hcen] at hbad
    exact False.elim (Finset.notMem_empty _ hbad)
  · have hjread : j ∈ readers n C h :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hin⟩
    rw [hread, Finset.mem_singleton] at hjread
    rw [hjread] at hp
    exact reach_mem_orIn r (hp.trans (mem_orIn_reach r hr))

lemma cut_critical_top {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : ℕ) (hL : IsLeastAO G C) (hh : h ∈ junk G C)
    (u v : Fin n) (huv : G.Adj u v)
    (hcut : circuitFun n (cut C h) (pairInput u v) = false) :
    ∃ a ∈ tops G C, gateVal n C a (pairInput u v) = true ∧
      gateVal n (cut C h) a (pairInput u v) = false := by
  have hout (x : Fin n → Bool) : val C (List.ofFn x) C.output = graphFun G ∅ x :=
    congrFun hL.2.1 x
  obtain ⟨a, ha, hna, hp, hva⟩ := edge_trace G (graphFun G ∅)
    (fun p q => (graphFun_pair G p q).mp) hout u v ((graphFun_pair G u v).mpr huv)
  have hand := (hL.1.1 _ (gateAt_mem ha)).resolve_right hna
  have hbelow : BelowF G C a := fun x hx =>
    below_of_reach (graphFun G ∅) hout a hp x hx
  have hat : a ∈ tops G C := by
    simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using
      And.intro ha (And.intro hand hbelow)
  refine ⟨a, hat, hva, Bool.eq_false_iff.mpr ?_⟩
  intro hnew
  have hpnew := (cut_orPath C h (junkData hh).2.1 _ _).mpr hp
  have houtnew := orStep_up (n := n) (by simp) hpnew hnew
  change val (cut C h) (List.ofFn (pairInput u v)) C.output = false at hcut
  exact Bool.false_ne_true (hcut.symm.trans houtnew)

lemma cut_top_of_raws {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g h : ℕ) (hAO : IsAO2 n C) (hT : TopForm G C)
    (hcen : centreless G C = ∅) (hJ : junk G C = {g, h})
    (hread : readers n C g = {h}) {a : ℕ} (ha : a ∈ tops G C)
    (x : Fin n → Bool) (hraw : ∀ b : Fin 2, setOr (side (n := n) C a b) x = true) :
    gateVal n (cut C h) a x = true := by
  have hh : h ∈ junk G C := by simp [hJ]
  have hah : a ≠ h := by
    intro he
    rw [he] at ha
    exact junkNotBelow hh (topData ha).2.2
  have hareal := (topData ha).1
  have hacut : a < (cut C h).gates.length := by simpa [cut_len] using hareal
  have haand : (gateAt (cut C h) a).op = GateOp.and := by
    rw [cut_gate_same C h a hah]
    exact (topData ha).2.1
  rw [gateVal_eq_val, val_and (n := n) (by simp) hacut haand]
  intro i hi
  rw [cut_gate_same C h a hah] at hi
  obtain ⟨b, hb⟩ := inputsAsOpnd hAO hareal hi
  refine ⟨hAO.2.1 a hareal i hi, ?_⟩
  rw [hb]
  exact (cut_top_operand_raw G C g h hAO hT hcen hJ hread ha b x).mpr (hraw b)

lemma top_product_below {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g h : ℕ) (hAO : IsAO2 n C) (hT : TopForm G C)
    (hcen : centreless G C = ∅) (hJ : junk G C = {g, h})
    (hread : readers n C g = {h}) {a : ℕ} (ha : a ∈ tops G C)
    (b : Fin 2) (hreach : OrReaches n C (opnd C a b) h) :
    ∀ x, ((setOr (side (n := n) C a b) x || gateVal n C h x) &&
      setOr (side (n := n) C a (1 - b)) x) = true → graphFun G ∅ x = true := by
  intro x hx
  simp only [Bool.and_eq_true, Bool.or_eq_true] at hx
  obtain ⟨hb, ho⟩ := hx
  have hvb : val C (List.ofFn x) (opnd C a b) = true := by
    apply (top_operand_raw_outer G C g h hAO hT hcen hJ hread ha b x).mpr
    rcases hb with hraw | hh
    · exact Or.inl hraw
    · exact Or.inr ⟨hreach, hh⟩
  have hvo : val C (List.ofFn x) (opnd C a (1 - b)) = true :=
    (top_operand_raw_outer G C g h hAO hT hcen hJ hread ha (1 - b) x).mpr (Or.inl ho)
  apply (topData ha).2.2 x
  apply (andValOperands hAO (topData ha).1 (topData ha).2.1 x).mpr
  intro q
  fin_cases b <;> fin_cases q
  · exact hvb
  · exact hvo
  · exact hvo
  · exact hvb

lemma critical_top_side {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g h m : ℕ) (hAO : IsAO2 n C) (hT : TopForm G C)
    (hcen : centreless G C = ∅) (hJ : junk G C = {g, h})
    (hreadg : readers n C g = {h}) (hreadh : readers n C h = {m})
    (r : Fin n) (hr : r ∈ orIn n C (n + m))
    {a : ℕ} (ha : a ∈ tops G C) (u v : Fin n)
    (hval : gateVal n C a (pairInput u v) = true)
    (hcut : gateVal n (cut C h) a (pairInput u v) = false) :
    ∃ b : Fin 2, OrReaches n C (opnd C a b) h ∧
      setOr (side (n := n) C a b) (pairInput u v) = false ∧
      setOr (side (n := n) C a (1 - b)) (pairInput u v) = true := by
  have hh : h ∈ junk G C := by simp [hJ]
  have haval := (andValOperands hAO (topData ha).1 (topData ha).2.1 _).mp hval
  have hs0 := (top_operand_raw_outer G C g h hAO hT hcen hJ hreadg ha 0 _).mp (haval 0)
  have hs1 := (top_operand_raw_outer G C g h hAO hT hcen hJ hreadg ha 1 _).mp (haval 1)
  have not_raw_both : ¬ (setOr (side (n := n) C a 0) (pairInput u v) = true ∧
      setOr (side (n := n) C a 1) (pairInput u v) = true) := by
    rintro ⟨h0, h1⟩
    have hnew := cut_top_of_raws G C g h hAO hT hcen hJ hreadg ha (pairInput u v)
      (fun b => by fin_cases b; exact h0; exact h1)
    exact Bool.false_ne_true (hcut.symm.trans hnew)
  have not_reach_both : ¬ (OrReaches n C (opnd C a 0) h ∧
      OrReaches n C (opnd C a 1) h) := by
    rintro ⟨h0, h1⟩
    have hr0 := top_reach_contains_raw G C h m hcen hh hreadh r hr ha 0 h0
    have hr1 := top_reach_contains_raw G C h m hcen hh hreadh r hr ha 1 h1
    exact G.loopless.irrefl r (topAdj hAO ha hr0 hr1)
  rcases hs0 with h0 | ⟨hp0, _⟩
  · have hn1 : setOr (side (n := n) C a 1) (pairInput u v) ≠ true :=
      fun h1 => not_raw_both ⟨h0, h1⟩
    obtain ⟨hp1, _⟩ := hs1.resolve_left hn1
    exact ⟨1, hp1, Bool.eq_false_iff.mpr hn1, h0⟩
  · rcases hs1 with h1 | ⟨hp1, _⟩
    · have hn0 : setOr (side (n := n) C a 0) (pairInput u v) ≠ true :=
        fun h0 => not_raw_both ⟨h0, h1⟩
      exact ⟨0, hp0, Bool.eq_false_iff.mpr hn0, h1⟩
    · exact False.elim (not_reach_both ⟨hp0, hp1⟩)

lemma fixed_raw_critical_filter {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g h m : ℕ) (hL : IsLeastAO G C) (hT : TopForm G C)
    (hcen : centreless G C = ∅) (hJ : junk G C = {g, h})
    (hreadg : readers n C g = {h}) (hreadh : readers n C h = {m})
    (r : Fin n) (hr : r ∈ orIn n C (n + m))
    (u v : Fin n) (huv : G.Adj u v)
    (hcut : circuitFun n (cut C h) (pairInput u v) = false) :
    r ≠ u ∧ r ≠ v ∧ ∃ w : Fin n, (w = u ∨ w = v) ∧ G.Adj r w ∧
      ∀ x, gateVal n C h x = true → x w = true → graphFun G ∅ x = true := by
  have hh : h ∈ junk G C := by simp [hJ]
  obtain ⟨a, ha, hval, hzero⟩ := cut_critical_top G C h hL hh u v huv hcut
  obtain ⟨b, hp, hraw, hother⟩ := critical_top_side G C g h m hL.1 hT hcen hJ
    hreadg hreadh r hr ha u v hval hzero
  have hrside := top_reach_contains_raw G C h m hcen hh hreadh r hr ha b hp
  exact shared_raw_critical_filter G (gateVal n C h)
    (side (n := n) C a b) (side (n := n) C a (1 - b)) r u v hrside
    (top_product_below G C g h hL.1 hT hcen hJ hreadg ha b hp) hraw hother

lemma tight_raw_critical_filter {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g h m : ℕ) (hL : IsLeastAO G C) (hT : TopForm G C)
    (hcen : centreless G C = ∅) (hJ : junk G C = {g, h}) (hgh : g < h)
    (hreadg : readers n C g = {h}) (hreadh : readers n C h = {m})
    (hbudget : orN G C \ lam G C = {m}) :
    ∃ r ∈ orIn n C (n + m), ∀ u v : Fin n, G.Adj u v →
      circuitFun n (cut C h) (pairInput u v) = false →
      r ≠ u ∧ r ≠ v ∧ ∃ w : Fin n, (w = u ∨ w = v) ∧ G.Adj r w ∧
        ∀ x, gateVal n C h x = true → x w = true → graphFun G ∅ x = true := by
  obtain ⟨r, hr⟩ := raw_reader_nonempty G C g h m hL hcen hJ hgh hreadh hbudget
  exact ⟨r, hr, fun u v huv hcut =>
    fixed_raw_critical_filter G C g h m hL hT hcen hJ hreadg hreadh r hr u v huv hcut⟩

lemma critical_outer_true {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g h : ℕ) (hL : IsLeastAO G C) (hT : TopForm G C)
    (hcen : centreless G C = ∅) (hJ : junk G C = {g, h})
    (hreadg : readers n C g = {h}) (u v : Fin n) (huv : G.Adj u v)
    (hcut : circuitFun n (cut C h) (pairInput u v) = false) :
    gateVal n C h (pairInput u v) = true := by
  have hh : h ∈ junk G C := by simp [hJ]
  obtain ⟨a, ha, hval, hzero⟩ := cut_critical_top G C h hL hh u v huv hcut
  have haval := (andValOperands hL.1 (topData ha).1 (topData ha).2.1 _).mp hval
  have hs0 := (top_operand_raw_outer G C g h hL.1 hT hcen hJ hreadg ha 0 _).mp (haval 0)
  have hs1 := (top_operand_raw_outer G C g h hL.1 hT hcen hJ hreadg ha 1 _).mp (haval 1)
  rcases hs0 with h0 | ⟨_, hv⟩
  · rcases hs1 with h1 | ⟨_, hv⟩
    · have hnew := cut_top_of_raws G C g h hL.1 hT hcen hJ hreadg ha (pairInput u v)
        (fun b => by fin_cases b; exact h0; exact h1)
      exact False.elim (Bool.false_ne_true (hzero.symm.trans hnew))
    · exact hv
  · exact hv

end PEqualNP.Outside.L_meta_5012.Trace


namespace PEqualNP.Outside.L_meta_5012.Geometry

open PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def hit {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∃ v ∈ S, x v = true)

def triple {n : ℕ} (A B C : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  hit A x && (hit B x && hit C x)

def clean {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B C : Finset (Fin n)) (w : Fin n) : Prop :=
  ∀ x, x w = true → triple A B C x = true → graphFun G ∅ x = true

lemma triple_true {n : ℕ} (A B C : Finset (Fin n)) (x : Fin n → Bool) :
    triple A B C x = true ↔
      (∃ a ∈ A, x a = true) ∧ (∃ b ∈ B, x b = true) ∧ (∃ c ∈ C, x c = true) := by
  simp [triple, hit]

lemma graph_true {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
  simp [graphFun]

lemma graph_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a b : Fin n) : graphFun G ∅ (pairInput a b) = true ↔ G.Adj a b := by
  rw [graph_true]
  constructor
  · rintro ⟨u, v, huv, hu, hv⟩
    simp only [pairInput, decide_eq_true_eq] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact False.elim (G.loopless.irrefl _ huv)
    · exact huv
    · exact huv.symm
    · exact False.elim (G.loopless.irrefl _ huv)
  · intro hab
    exact ⟨a, b, hab, by simp [pairInput], by simp [pairInput]⟩

lemma row_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B C : Finset (Fin n)) (d : Fin n) (hd : d ∈ A ∩ C) :
    clean G A B C d ↔ ∀ b ∈ B, G.Adj d b := by
  obtain ⟨hdA, hdC⟩ := Finset.mem_inter.mp hd
  constructor
  · intro h b hb
    apply (graph_pair G d b).mp
    apply h (pairInput d b) (by simp [pairInput])
    apply (triple_true A B C _).mpr
    exact ⟨⟨d, hdA, by simp [pairInput]⟩,
      ⟨b, hb, by simp [pairInput]⟩, ⟨d, hdC, by simp [pairInput]⟩⟩
  · intro h x hxd hx
    obtain ⟨_, ⟨b, hb, hxb⟩, _⟩ := (triple_true A B C x).mp hx
    exact (graph_true G x).mpr ⟨d, b, h b hb, hxd, hxb⟩

lemma column_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B C : Finset (Fin n))
    (hno : ∀ a ∈ A, ∀ c ∈ C, ¬ G.Adj a c)
    (b : Fin n) (hb : b ∈ B) :
    clean G A B C b ↔ (∀ a ∈ A, G.Adj b a) ∨ (∀ c ∈ C, G.Adj b c) := by
  constructor
  · intro h
    have hp : ∀ a ∈ A, ∀ c ∈ C, G.Adj b a ∨ G.Adj b c := by
      intro a ha c hc
      let x : Fin n → Bool := fun t => decide (t = b ∨ t = a ∨ t = c)
      have hx : triple A B C x = true := by
        apply (triple_true A B C x).mpr
        exact ⟨⟨a, ha, by simp [x]⟩, ⟨b, hb, by simp [x]⟩, ⟨c, hc, by simp [x]⟩⟩
      obtain ⟨u, v, huv, hu, hv⟩ := (graph_true G x).mp (h x (by simp [x]) hx)
      simp only [x, decide_eq_true_eq] at hu hv
      rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
      · exact False.elim (G.loopless.irrefl _ huv)
      · exact Or.inl huv
      · exact Or.inr huv
      · exact Or.inl huv.symm
      · exact False.elim (G.loopless.irrefl _ huv)
      · exact False.elim (hno _ ha _ hc huv)
      · exact Or.inr huv.symm
      · exact False.elim (hno _ ha _ hc huv.symm)
      · exact False.elim (G.loopless.irrefl _ huv)
    classical
    by_cases hA : ∀ a ∈ A, G.Adj b a
    · exact Or.inl hA
    · right
      intro c hc
      by_contra hbc
      exact hA (fun a ha => (hp a ha c hc).resolve_right hbc)
  · rintro (hA | hC) x hxb hx
    · obtain ⟨⟨a, ha, hxa⟩, _, _⟩ := (triple_true A B C x).mp hx
      exact (graph_true G x).mpr ⟨b, a, hA a ha, hxb, hxa⟩
    · obtain ⟨_, _, c, hc, hxc⟩ := (triple_true A B C x).mp hx
      exact (graph_true G x).mpr ⟨b, c, hC c hc, hxb, hxc⟩

lemma no_edges_of_color {n : ℕ} (G : SimpleGraph (Fin n))
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (A C : Finset (Fin n)) (hcolor : ∀ a ∈ A, ∀ c ∈ C, s a = s c) :
    ∀ a ∈ A, ∀ c ∈ C, ¬ G.Adj a c := by
  intro a ha c hc hac
  exact hbip a c hac (hcolor a ha c hc)

lemma universal_card_le_one {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (S T : Finset (Fin n)) (hT : 2 ≤ T.card)
    (hadj : ∀ a ∈ S, ∀ b ∈ T, G.Adj a b) : S.card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  by_contra hab
  have hsub : T ⊆ Finset.univ.filter (fun w => G.Adj a w ∧ G.Adj b w) := by
    intro w hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj a ha w hw, hadj b hb w hw⟩
  have hle := Finset.card_le_card hsub
  have hone := h4 a b hab
  omega

def rows {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B C : Finset (Fin n)) : Finset (Fin n) :=
  (A ∩ C).filter fun d => ∀ b ∈ B, G.Adj d b

def columns {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B C : Finset (Fin n)) : Finset (Fin n) :=
  B.filter fun b => (∀ a ∈ A, G.Adj b a) ∨ (∀ c ∈ C, G.Adj b c)

lemma rows_card_le_one {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (A B C : Finset (Fin n)) (hB : 2 ≤ B.card) :
    (rows G A B C).card ≤ 1 := by
  apply universal_card_le_one G h4 (rows G A B C) B hB
  intro d hd b hb
  exact (Finset.mem_filter.mp hd).2 b hb

lemma columns_card_le_one {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (A B C : Finset (Fin n)) (hD : 2 ≤ (A ∩ C).card) :
    (columns G A B C).card ≤ 1 := by
  apply universal_card_le_one G h4 (columns G A B C) (A ∩ C) hD
  intro b hb d hd
  obtain ⟨hdA, hdC⟩ := Finset.mem_inter.mp hd
  rcases (Finset.mem_filter.mp hb).2 with hA | hC
  · exact hA d hdA
  · exact hC d hdC

lemma useful_cross_star {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B C : Finset (Fin n)) (hno : ∀ a ∈ A, ∀ c ∈ C, ¬ G.Adj a c)
    (d b : Fin n) (hd : d ∈ A ∩ C) (hb : b ∈ B)
    (huse : clean G A B C d ∨ clean G A B C b) :
    d ∈ rows G A B C ∨ b ∈ columns G A B C := by
  rcases huse with h | h
  · exact Or.inl (Finset.mem_filter.mpr ⟨hd, (row_iff G A B C d hd).mp h⟩)
  · exact Or.inr (Finset.mem_filter.mpr ⟨hb, (column_iff G A B C hno b hb).mp h⟩)

lemma common_neighbor_unique {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (a b u v : Fin n) (hab : a ≠ b)
    (hau : G.Adj a u) (hbu : G.Adj b u) (hav : G.Adj a v) (hbv : G.Adj b v) : u = v := by
  exact Finset.card_le_one.mp (h4 a b hab) u
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hau, hbu⟩) v
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hav, hbv⟩)

lemma common_neighbor_color {n : ℕ} (G : SimpleGraph (Fin n))
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (r u v : Fin n) (hru : G.Adj r u) (hrv : G.Adj r v) : s u = s v := by
  have h1 := hbip r u hru
  have h2 := hbip r v hrv
  cases hr : s r <;> cases hu : s u <;> cases hv : s v <;> simp_all

lemma common_raw_reader_star {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : NoFourCycle G) (A B C : Finset (Fin n))
    (hAB : ∀ a ∈ A, ∀ b ∈ B, s a ≠ s b)
    (hAC : ∀ a ∈ A, ∀ c ∈ C, s a = s c)
    (E : Finset (Fin n × Fin n)) (hEn : E.Nonempty)
    (hE : ∀ p ∈ E, p.1 ∈ A ∩ C ∧ p.2 ∈ B)
    (r : Fin n) (hne : ∀ p ∈ E, r ≠ p.1 ∧ r ≠ p.2)
    (hfilter : ∀ p ∈ E,
      (clean G A B C p.1 ∧ G.Adj r p.1) ∨
      (clean G A B C p.2 ∧ G.Adj r p.2)) :
    ∃ (v : Fin n) (S : Finset (Fin n)), (S = A ∨ S = B ∨ S = C) ∧
      (∀ z ∈ S, G.Adj v z) ∧
      ∀ p ∈ E, (p.1 = v ∧ p.2 ∈ S) ∨ (p.2 = v ∧ p.1 ∈ S) := by
  obtain ⟨⟨d0, b0⟩, he0⟩ := hEn
  obtain ⟨hd0, hb0⟩ := hE (d0, b0) he0
  obtain ⟨hrd0, hrb0⟩ := hne (d0, b0) he0
  have hno := no_edges_of_color G s hbip A C hAC
  rcases hfilter (d0, b0) he0 with ⟨hclean0, hadj0⟩ | ⟨hclean0, hadj0⟩
  · have hall : ∀ p ∈ E, clean G A B C p.1 ∧ G.Adj r p.1 := by
      intro p hp
      rcases hfilter p hp with h | ⟨hclean, hadj⟩
      · exact h
      · have heq := common_neighbor_color G s hbip r d0 p.2 hadj0 hadj
        exact False.elim (hAB d0 (Finset.mem_inter.mp hd0).1 p.2 (hE p hp).2 heq)
    have huniv := (row_iff G A B C d0 hd0).mp hclean0
    refine ⟨d0, B, Or.inr (Or.inl rfl), huniv, ?_⟩
    intro p hp
    obtain ⟨hd, hb⟩ := hE p hp
    obtain ⟨hclean, hadj⟩ := hall p hp
    have hunivp := (row_iff G A B C p.1 hd).mp hclean
    have heq := common_neighbor_unique G h4 r b0 p.1 d0 hrb0
      hadj (hunivp b0 hb0).symm hadj0 (huniv b0 hb0).symm
    exact Or.inl ⟨heq, hb⟩
  · have hall : ∀ p ∈ E, clean G A B C p.2 ∧ G.Adj r p.2 := by
      intro p hp
      rcases hfilter p hp with ⟨hclean, hadj⟩ | h
      · have heq := common_neighbor_color G s hbip r p.1 b0 hadj hadj0
        exact False.elim (hAB p.1 (Finset.mem_inter.mp (hE p hp).1).1 b0 hb0 heq)
      · exact h
    have huniv0 := (column_iff G A B C hno b0 hb0).mp hclean0
    have heq : ∀ p ∈ E, p.2 = b0 := by
      intro p hp
      obtain ⟨hclean, hadj⟩ := hall p hp
      have hunivp := (column_iff G A B C hno p.2 (hE p hp).2).mp hclean
      have hp_d : G.Adj p.2 d0 := by
        rcases hunivp with hA | hC
        · exact hA d0 (Finset.mem_inter.mp hd0).1
        · exact hC d0 (Finset.mem_inter.mp hd0).2
      have h0_d : G.Adj b0 d0 := by
        rcases huniv0 with hA | hC
        · exact hA d0 (Finset.mem_inter.mp hd0).1
        · exact hC d0 (Finset.mem_inter.mp hd0).2
      exact common_neighbor_unique G h4 r d0 p.2 b0 hrd0
        hadj hp_d.symm hadj0 h0_d.symm
    rcases huniv0 with hA | hC
    · refine ⟨b0, A, Or.inl rfl, hA, ?_⟩
      intro p hp
      exact Or.inr ⟨heq p hp, (Finset.mem_inter.mp (hE p hp).1).1⟩
    · refine ⟨b0, C, Or.inr (Or.inr rfl), hC, ?_⟩
      intro p hp
      exact Or.inr ⟨heq p hp, (Finset.mem_inter.mp (hE p hp).1).2⟩

def clauseClean {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Fin k → Finset (Fin n)) (w : Fin n) : Prop :=
  ∀ x : Fin n → Bool, x w = true →
    (∀ i, ∃ a ∈ S i, x a = true) → graphFun G ∅ x = true

lemma bool_same_away (u v w : Bool) (hu : u ≠ w) (hv : v ≠ w) : u = v := by
  cases u <;> cases v <;> cases w <;> simp_all

lemma monochrome_filter_universal {n k : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (S : Fin k → Finset (Fin n)) (t : Fin k → Bool)
    (hmono : ∀ i, ∀ a ∈ S i, s a = t i)
    (d w : Fin n) (hdw : s d ≠ s w)
    (hpair : ∀ i, d ∈ S i ∨ w ∈ S i)
    (hclean : clauseClean G S w) :
    ∃ i, t i ≠ s w ∧ ∀ a ∈ S i, G.Adj w a := by
  classical
  by_contra hnone
  let x : Fin n → Bool := fun a => decide (a = w ∨ (s a ≠ s w ∧ ¬ G.Adj w a))
  have hw : x w = true := by simp [x]
  have hhit : ∀ i, ∃ a ∈ S i, x a = true := by
    intro i
    by_cases hi : t i = s w
    · have hwi : w ∈ S i := by
        rcases hpair i with hd | hw
        · exact False.elim (hdw ((hmono i d hd).trans hi))
        · exact hw
      exact ⟨w, hwi, hw⟩
    · by_contra hmiss
      have huni : ∀ a ∈ S i, G.Adj w a := by
        intro a ha
        by_contra hwa
        have hax : x a = true := by
          apply decide_eq_true
          exact Or.inr ⟨by rw [hmono i a ha]; exact hi, hwa⟩
        exact hmiss ⟨a, ha, hax⟩
      exact hnone ⟨i, hi, huni⟩
  obtain ⟨u, v, huv, hu, hv⟩ := (graph_true G x).mp (hclean x hw hhit)
  simp only [x, decide_eq_true_eq] at hu hv
  rcases hu with hu | ⟨huc, hun⟩
  · subst u
    rcases hv with hv | ⟨hvc, hvn⟩
    · subst v
      exact G.loopless.irrefl w huv
    · exact hvn huv
  · rcases hv with hv | ⟨hvc, hvn⟩
    · subst v
      exact hun huv.symm
    · exact hbip u v huv (bool_same_away (s u) (s v) (s w) huc hvc)

lemma monochrome_common_reader_star {n k : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : NoFourCycle G)
    (S : Fin k → Finset (Fin n)) (t : Fin k → Bool)
    (hmono : ∀ i, ∀ a ∈ S i, s a = t i)
    (R : Fin n → Fin n → Prop) (hRn : ∃ d w, R d w)
    (hcolor : ∀ d w, R d w → s d ≠ s w)
    (hpair : ∀ d w, R d w → ∀ i, d ∈ S i ∨ w ∈ S i)
    (hclean : ∀ d w, R d w → clauseClean G S w)
    (r : Fin n) (hraw : ∀ d w, R d w → G.Adj r w)
    (hne : ∀ d w, R d w → r ≠ d) :
    ∃ (v : Fin n) (i : Fin k), (∀ a ∈ S i, G.Adj v a) ∧
      ∀ d w, R d w → w = v ∧ d ∈ S i := by
  obtain ⟨d0, w0, h0⟩ := hRn
  obtain ⟨i0, hi0, huniv0⟩ := monochrome_filter_universal G s hbip S t hmono
    d0 w0 (hcolor d0 w0 h0) (hpair d0 w0 h0) (hclean d0 w0 h0)
  have hd0 : d0 ∈ S i0 := by
    rcases hpair d0 w0 h0 i0 with h | h
    · exact h
    · exact False.elim (hi0 (hmono i0 w0 h).symm)
  refine ⟨w0, i0, huniv0, ?_⟩
  intro d w h
  have hsame := common_neighbor_color G s hbip r w w0 (hraw d w h) (hraw d0 w0 h0)
  obtain ⟨i, hi, huniv⟩ := monochrome_filter_universal G s hbip S t hmono
    d w (hcolor d w h) (hpair d w h) (hclean d w h)
  have hd0i : d0 ∈ S i := by
    rcases hpair d0 w0 h0 i with hh | hh
    · exact hh
    · exact False.elim (hi ((hmono i w0 hh).symm.trans hsame.symm))
  have hww0 := common_neighbor_unique G h4 r d0 w w0 (hne d0 w0 h0)
    (hraw d w h) (huniv d0 hd0i).symm (hraw d0 w0 h0) (huniv0 d0 hd0).symm
  refine ⟨hww0, ?_⟩
  rcases hpair d w h i0 with hh | hh
  · exact hh
  · exact False.elim (hi0 ((hmono i0 w hh).symm.trans hsame))

lemma monochrome_unoriented_star {n k : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : NoFourCycle G)
    (S : Fin k → Finset (Fin n)) (t : Fin k → Bool)
    (hmono : ∀ i, ∀ a ∈ S i, s a = t i)
    (E : Finset (Fin n × Fin n)) (hEn : E.Nonempty)
    (hadj : ∀ p ∈ E, G.Adj p.1 p.2)
    (hpair : ∀ p ∈ E, ∀ i, p.1 ∈ S i ∨ p.2 ∈ S i)
    (r : Fin n) (hne : ∀ p ∈ E, r ≠ p.1 ∧ r ≠ p.2)
    (hfilter : ∀ p ∈ E,
      (clauseClean G S p.1 ∧ G.Adj r p.1) ∨
      (clauseClean G S p.2 ∧ G.Adj r p.2)) :
    ∃ (v : Fin n) (i : Fin k), (∀ a ∈ S i, G.Adj v a) ∧
      ∀ p ∈ E, (p.1 = v ∧ p.2 ∈ S i) ∨ (p.2 = v ∧ p.1 ∈ S i) := by
  let R : Fin n → Fin n → Prop := fun d w =>
    ((d, w) ∈ E ∨ (w, d) ∈ E) ∧ clauseClean G S w ∧ G.Adj r w
  have hRn : ∃ d w, R d w := by
    obtain ⟨⟨d, w⟩, h⟩ := hEn
    rcases hfilter (d, w) h with ⟨hc, hr⟩ | ⟨hc, hr⟩
    · exact ⟨w, d, Or.inr h, hc, hr⟩
    · exact ⟨d, w, Or.inl h, hc, hr⟩
  have hcolR : ∀ d w, R d w → s d ≠ s w := by
    intro d w h
    rcases h.1 with h | h
    · exact hbip d w (hadj (d, w) h)
    · exact hbip d w (hadj (w, d) h).symm
  have hpR : ∀ d w, R d w → ∀ i, d ∈ S i ∨ w ∈ S i := by
    intro d w h i
    rcases h.1 with h | h
    · exact hpair (d, w) h i
    · exact (hpair (w, d) h i).symm
  have hnR : ∀ d w, R d w → r ≠ d := by
    intro d w h
    rcases h.1 with h | h
    · exact (hne (d, w) h).1
    · exact (hne (w, d) h).2
  obtain ⟨v, i, hu, hv⟩ := monochrome_common_reader_star G s hbip h4 S t hmono R hRn
    hcolR hpR (fun _ _ h => h.2.1) r (fun _ _ h => h.2.2) hnR
  refine ⟨v, i, hu, ?_⟩
  intro p hp
  rcases hfilter p hp with ⟨hc, hr⟩ | ⟨hc, hr⟩
  · exact Or.inl (hv p.2 p.1 ⟨Or.inr hp, hc, hr⟩)
  · exact Or.inr (hv p.1 p.2 ⟨Or.inl hp, hc, hr⟩)

end PEqualNP.Outside.L_meta_5012.Geometry

namespace PEqualNP.Outside.L_meta_5012

namespace Semantics

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

open PEqualNP.CleanedNonEdge in
lemma orFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

open PEqualNP.CleanedNonEdge in
lemma orStep_mem_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) (x : ℕ) :
    x ∈ (orStep n cs g).getD cs.length [] ↔ x = cs.length ∨ (g.op = GateOp.or ∧
      ∃ w ∈ g.inputs, n ≤ w ∧ w < n + cs.length ∧ x ∈ cs.getD (w - n) []) := by
  by_cases h : g.op = GateOp.or
  · simp only [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl, h,
      ↓reduceIte, true_and, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some,
      List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro (h1 | ⟨w, ⟨hw, hn, hlt⟩, hx⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, hw, hn, hlt, hx⟩
    · rintro (h1 | ⟨w, hw, hn, hlt, hx⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, ⟨hw, hn, hlt⟩, hx⟩
  · simp [orStep, List.getD_eq_getElem?_getD, h]

open PEqualNP.CleanedNonEdge in
lemma orStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (orStep n cs g).getD m [] = cs.getD m [] := by
  simp [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

open PEqualNP.CleanedNonEdge in
lemma orFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (orStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (orStep n cs g) (by simp [orStep]; omega)]
    exact orStep_getD_lt n cs g k hk

open PEqualNP.CleanedNonEdge in
lemma orSets_mem_iff (n : ℕ) (C : Circuit) (k x : ℕ) (hk : k < C.gates.length) :
    x ∈ (orSets n C).getD k [] ↔ x = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧ x ∈ (orSets n C).getD (w - n) []) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : orSets n C = post.foldl (orStep n) (orStep n (pre.foldl (orStep n) []) gk) := by
    simp only [orSets]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (orStep n) []).length = k := by
    rw [orFold_length]; simp [hpre_len]
  have hl1 : (orStep n (pre.foldl (orStep n) []) gk).length = k + 1 := by
    simp [orStep, hl0]
  have h1 : (orSets n C).getD k [] = (orStep n (pre.foldl (orStep n) []) gk).getD k [] := by
    rw [hc, orFold_getD_lt n post _ k (by omega)]
  have h2 : ∀ m, m < k → (orSets n C).getD m [] = (pre.foldl (orStep n) []).getD m [] := by
    intro m hm
    rw [hc, orFold_getD_lt n post _ m (by omega)]
    exact orStep_getD_lt n _ gk m (by omega)
  have h3 := orStep_mem_last n (pre.foldl (orStep n) []) gk x
  rw [hl0] at h3
  rw [h1, h3]
  constructor
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [h2 (w - n) (by omega)]; exact hx⟩
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [← h2 (w - n) (by omega)]; exact hx⟩


lemma W_or (n : ℕ) (C : Circuit) (x : Fin n → Bool) (r : ℕ) (hr : r < C.gates.length)
    (hop : (gateAt C r).op = GateOp.or) (i : ℕ) (hi : i ∈ (gateAt C r).inputs)
    (hlt : i < n + r) (hv : W n C x i = true) : W n C x (n + r) = true := by
  rw [W_gate n C x r hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  exact ⟨i, hi, by rw [if_pos hlt]; exact hv⟩

open PEqualNP.CleanedNonEdge in
lemma reach_val (n : ℕ) (C : Circuit) (x : Fin n → Bool) (g : ℕ)
    (hv : W n C x (n + g) = true) :
    ∀ k, k < C.gates.length → g ∈ (orSets n C).getD k [] → W n C x (n + k) = true := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk hmem
    rcases (orSets_mem_iff n C k g hk).mp hmem with h | ⟨hop, w, hw, hn, hlt, hx⟩
    · rw [← h]; exact hv
    · have h3 := ih (w - n) (by omega) (by omega) hx
      have e : n + (w - n) = w := by omega
      rw [e] at h3
      exact W_or n C x k hk hop w hw hlt h3

open PEqualNP.CleanedNonEdge in
lemma reach_up (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w g : ℕ)
    (h : OrReaches n C w g) (hv : W n C x (n + g) = true) : W n C x w = true := by
  obtain ⟨hn, hmem⟩ := h
  by_cases hk : w - n < C.gates.length
  · have h3 := reach_val n C x g hv (w - n) hk hmem
    have e : n + (w - n) = w := by omega
    rw [e] at h3
    exact h3
  · exfalso
    have hlen : (orSets n C).length = C.gates.length := by
      unfold orSets; rw [orFold_length]; simp
    have hge : (orSets n C).length ≤ w - n := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge] at hmem
    simp at hmem

lemma mem_filter_gen {α : Type} (p : α → Prop) (d : DecidablePred p) (s : Finset α) (a : α)
    (h : a ∈ @Finset.filter α p d s) : p a :=
  ((@Finset.mem_filter α p d s a).mp h).2

lemma side_val (n : ℕ) (C : Circuit) (x : Fin n → Bool) (j : ℕ) (b : Fin 2) (i : Fin n)
    (hi : i ∈ PEqualNP.TopForm.side (n := n) C j b) (hx : x i = true) :
    W n C x (PEqualNP.TopForm.opnd C j b) = true := by
  unfold PEqualNP.TopForm.side PEqualNP.TopForm.orIn at hi
  have hi2 := mem_filter_gen _ _ _ _ hi
  rcases hi2 with h | ⟨k, hk, hreach, hop, hin⟩
  · rw [← h, W_input n C x i.val i.isLt]; exact hx
  · have hk1 : W n C x (n + k) = true := by
      apply W_or n C x k hk hop i.val hin (by have := i.isLt; omega)
      rw [W_input n C x i.val i.isLt]; exact hx
    exact reach_up n C x _ k hreach hk1

open PEqualNP.EdgeOwnership in
lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

open PEqualNP.EdgeOwnership in
lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

open PEqualNP.EdgeOwnership in
lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3


lemma gateAt_mem' (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq C j hj]; exact List.getElem_mem hj

open PEqualNP.EdgeOwnership in
lemma inCone_lt (n : ℕ) (C : Circuit) : ∀ j i, InCone n C i j → i < j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro i h
    obtain ⟨_, k, hk, _, h3⟩ := (inCone_iff n C i j).mp h
    rcases h3 with h3 | h3
    · omega
    · have := ih k hk i h3; omega

open PEqualNP.CleanedNonEdge in
lemma orReach_trans (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (w : ℕ) (hw : w ∈ (gateAt C k).inputs)
    (hlt : w < n + k) (g : ℕ) (h : OrReaches n C w g) : OrReaches n C (n + k) g := by
  obtain ⟨hn, hmem⟩ := h
  refine ⟨by omega, ?_⟩
  have e : n + k - n = k := by omega
  rw [e]
  exact (orSets_mem_iff n C k g hk).mpr (Or.inr ⟨hop, w, hw, hn, hlt, hmem⟩)

open PEqualNP.CleanedNonEdge in
lemma orReach_self (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    OrReaches n C (n + k) k := by
  refine ⟨by omega, ?_⟩
  have e : n + k - n = k := by omega
  rw [e]
  exact (orSets_mem_iff n C k k hk).mpr (Or.inl rfl)

lemma orIn_mem (n : ℕ) (C : Circuit) (w : ℕ) (i : Fin n) :
    i ∈ PEqualNP.TopForm.orIn n C w ↔ ((i : ℕ) = w ∨ ∃ k < C.gates.length,
      PEqualNP.CleanedNonEdge.OrReaches n C w k ∧ (gateAt C k).op = GateOp.or ∧
        (i : ℕ) ∈ (gateAt C k).inputs) := by
  unfold PEqualNP.TopForm.orIn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

open PEqualNP.CleanedNonEdge in
lemma down (n : ℕ) (C : Circuit) (x : Fin n → Bool)
    (hAO : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) :
    ∀ w, W n C x w = true → (∃ i : Fin n, i ∈ PEqualNP.TopForm.orIn n C w ∧ x i = true) ∨
      ∃ k, k < C.gates.length ∧ OrReaches n C w k ∧ (gateAt C k).op = GateOp.and ∧
        W n C x (n + k) = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hwn : w < n
    · left
      refine ⟨⟨w, hwn⟩, (orIn_mem n C w _).mpr (Or.inl rfl), ?_⟩
      rw [← W_input n C x w hwn]; exact hv
    · by_cases hk : w - n < C.gates.length
      · have hw : w = n + (w - n) := by omega
        set k := w - n with hkdef
        rcases hAO k hk with hop | hop
        · right
          refine ⟨k, hk, ?_, hop, ?_⟩
          · rw [hw]; exact orReach_self n C k hk
          · rw [← hw]; exact hv
        · have hv2 := hv
          rw [hw, W_gate n C x k hk, hop] at hv2
          simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq] at hv2
          obtain ⟨i, hi, hiv⟩ := hv2
          split_ifs at hiv with hlt
          rcases ih i (by omega) hiv with ⟨j, hj, hxj⟩ | ⟨k', hk', hr, hop', hv'⟩
          · left
            refine ⟨j, ?_, hxj⟩
            rw [orIn_mem] at hj ⊢
            right
            rcases hj with hj | ⟨k'', hk'', hr, hop'', hin⟩
            · refine ⟨k, hk, ?_, hop, ?_⟩
              · rw [hw]; exact orReach_self n C k hk
              · rw [hj]; exact hi
            · refine ⟨k'', hk'', ?_, hop'', hin⟩
              rw [hw]; exact orReach_trans n C k hk hop i hi hlt k'' hr
          · right
            refine ⟨k', hk', ?_, hop', hv'⟩
            rw [hw]; exact orReach_trans n C k hk hop i hi hlt k' hr
      · exfalso
        have hl := wires_length n C x
        have : W n C x w = false := getD_ge_length _ w (by omega)
        rw [this] at hv; exact Bool.false_ne_true hv

open PEqualNP.EdgeOwnership in
lemma orSets_cone (n : ℕ) (C : Circuit) : ∀ m, m < C.gates.length → ∀ k,
    k ∈ (PEqualNP.CleanedNonEdge.orSets n C).getD m [] → k = m ∨ InCone n C k m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm k hk
    rcases (orSets_mem_iff n C m k hm).mp hk with h | ⟨_, w, hw, hn, hlt, hx⟩
    · exact Or.inl h
    · right
      have h2 := ih (w - n) (by omega) (by omega) k hx
      have e : n + (w - n) = w := by omega
      exact (inCone_iff n C k m).mpr ⟨hm, w - n, by omega, by rw [e]; exact hw, h2⟩

open PEqualNP.EdgeOwnership in
lemma reach_cone (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (o : ℕ)
    (ho : o ∈ (gateAt C j).inputs) (hlt : o < n + j) (k : ℕ)
    (h : PEqualNP.CleanedNonEdge.OrReaches n C o k) : InCone n C k j := by
  obtain ⟨hn, hmem⟩ := h
  have h2 := orSets_cone n C (o - n) (by omega) k hmem
  have e : n + (o - n) = o := by omega
  exact (inCone_iff n C k j).mpr ⟨hj, o - n, by omega, by rw [e]; exact ho, h2⟩

lemma firstTwoJunkSemantics : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : ℕ), PEqualNP.TopForm.IsAO2 x1 x4 → PEqualNP.TopForm.TopForm x2 x4 → x5 ∈ PEqualNP.TopForm.junk x2 x4 → x6 ∈ PEqualNP.TopForm.junk x2 x4 → x5 < x6 → (∀ x12 ∈ PEqualNP.TopForm.junk x2 x4, x12 < x6 → x12 = x5) → ∀ x13 ∈ [x5, x6], ∀ (x15 : Fin x1 → Bool), PEqualNP.ReadTwo.wval x4 x15 (x1 + x13) = Bool.true ↔ ∀ (x16 : Fin (2 : ℕ)), (∃ x17 ∈ PEqualNP.TopForm.side x4 x13 x16, x15 x17 = Bool.true) ∨ x13 = x6 ∧ PEqualNP.CleanedNonEdge.OrReaches x1 x4 (PEqualNP.TopForm.opnd x4 x13 x16) x5 ∧ PEqualNP.ReadTwo.wval x4 x15 (x1 + x5) = Bool.true := by
  intro n G _ C x5 x6 hAO hTF h5 h6 h56 hmin x13 hx13 x
  have hWeq : ∀ u, PEqualNP.ReadTwo.wval C x u = W n C x u := fun u => rfl
  simp only [hWeq]
  have hjunk : ∀ j, j ∈ PEqualNP.TopForm.junk G C ↔ j < C.gates.length ∧
      PEqualNP.CleanedNonEdge.IsDirtyAnd n G C j := by
    intro j
    unfold PEqualNP.TopForm.junk PEqualNP.TopForm.gatesWhere
    rw [Finset.mem_filter, Finset.mem_range]
  have hx13' : x13 = x5 ∨ x13 = x6 := by simpa using hx13
  have hj13 : x13 ∈ PEqualNP.TopForm.junk G C := by
    rcases hx13' with h | h <;> rw [h] <;> assumption
  have hle : x13 ≤ x6 := by rcases hx13' with h | h <;> omega
  obtain ⟨hlen13, hop13, _⟩ := (hjunk x13).mp hj13
  obtain ⟨hAOo, hRB, hAO2⟩ := hAO
  have hops : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or :=
    fun k hk => hAOo _ (gateAt_mem' C k hk)
  have hlen2 : (gateAt C x13).inputs.length = 2 := hAO2 _ (gateAt_mem' C x13 hlen13)
  have hopnd_mem : ∀ b : Fin 2, PEqualNP.TopForm.opnd C x13 b ∈ (gateAt C x13).inputs := by
    intro b
    unfold PEqualNP.TopForm.opnd
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    exact List.getElem_mem _
  have hin_opnd : ∀ i ∈ (gateAt C x13).inputs, ∃ b : Fin 2, i = PEqualNP.TopForm.opnd C x13 b := by
    intro i hi
    obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hi
    refine ⟨⟨p, by omega⟩, ?_⟩
    unfold PEqualNP.TopForm.opnd
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp]
    rfl
  constructor
  · intro hv b
    have hv2 := hv
    rw [W_gate n C x x13 hlen13, hop13] at hv2
    simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq] at hv2
    have hob := hv2 _ (hopnd_mem b)
    have hlt := hRB x13 hlen13 _ (hopnd_mem b)
    rw [if_pos hlt] at hob
    rcases down n C x hops _ hob with ⟨i, hi, hxi⟩ | ⟨k, hk, hr, hopk, hvk⟩
    · exact Or.inl ⟨i, hi, hxi⟩
    · right
      have hcone := reach_cone n C x13 hlen13 _ (hopnd_mem b) hlt k hr
      have hnb : ¬ PEqualNP.TopForm.BelowF G C k := fun hb => hTF k hk x13 hlen13 hopk hb hop13 hcone
      have hex : ∃ y : Fin n → Bool, PEqualNP.EdgeOwnership.gateVal n C k y = true ∧
          PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ y = false := by
        by_contra hc
        apply hnb
        intro y hy
        by_contra hf
        exact hc ⟨y, hy, Bool.eq_false_iff.mpr hf⟩
      have hkj : k ∈ PEqualNP.TopForm.junk G C := by
        rw [hjunk]
        obtain ⟨y, hy1, hy2⟩ := hex
        exact ⟨hk, hopk, hk, y, hy1, hy2⟩
      have hklt := inCone_lt n C x13 k hcone
      have hk5 := hmin k hkj (by omega)
      subst hk5
      rcases hx13' with h | h
      · omega
      · exact ⟨h, hr, hvk⟩
  · intro h
    rw [W_gate n C x x13 hlen13, hop13]
    simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro i hi
    rw [if_pos (hRB x13 hlen13 i hi)]
    obtain ⟨b, rfl⟩ := hin_opnd i hi
    rcases h b with ⟨j, hj, hxj⟩ | ⟨_, hr, hv5⟩
    · exact side_val n C x x13 b j hj hxj
    · exact reach_up n C x _ x5 hr hv5

end Semantics

namespace Boundary

lemma monotone_eq_of_extreme_values {α : Type*} [Preorder α] [Finite α]
    (f g : α → Bool) (hf : Monotone f)
    (hmin : ∀ x, Minimal (fun y => g y = true) x → f x = true)
    (hmax : ∀ x, Maximal (fun y => g y = false) x → f x = false) :
    f = g := by
  funext x
  cases hx : g x with
  | false =>
    obtain ⟨y, hxy, hy⟩ :=
      (Set.toFinite {y | g y = false}).exists_le_maximal hx
    have h := hf hxy
    rw [hmax y hy] at h
    cases hfx : f x <;> simp_all
    exact (by decide : ¬ (true : Bool) ≤ false) h
  | true =>
    obtain ⟨y, hyx, hy⟩ :=
      Set.Finite.exists_le_maximal (α := αᵒᵈ)
        (s := {y | g y = true}) (Set.toFinite _) hx
    have h := hf hyx
    rw [hmin y hy] at h
    cases hfx : f x <;> simp_all
    exact (by decide : ¬ (true : Bool) ≤ false) h

lemma bad_value_iff_maximal {α : Type*} [Preorder α] [Finite α]
    (f g : α → Bool) (hf : Monotone f) :
    (∃ x, f x = true ∧ g x = false) ↔
      ∃ x, Maximal (fun y => g y = false) x ∧ f x = true := by
  constructor
  · rintro ⟨x, hfx, hgx⟩
    obtain ⟨y, hxy, hy⟩ :=
      (Set.toFinite {y | g y = false}).exists_le_maximal hgx
    refine ⟨y, hy, ?_⟩
    have h := hf hxy
    rw [hfx] at h
    cases hfy : f y <;> simp_all
    exact (by decide : ¬ (true : Bool) ≤ false) h
  · rintro ⟨x, hx, hfx⟩
    exact ⟨x, hfx, hx.1⟩

open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

lemma graphFun_eq_of_boundary {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (f : (Fin n → Bool) → Bool) (hf : Monotone f)
    (hpos : ∀ u v, G.Adj u v → f (pairInput u v) = true)
    (hneg : ∀ x, Maximal (fun y => graphFun G ∅ y = false) x → f x = false) :
    f = graphFun G ∅ := by
  apply monotone_eq_of_extreme_values f (graphFun G ∅) hf
  · intro x hx
    have hxtrue := hx.1
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq] at hxtrue
    obtain ⟨u, v, huv, hu, hv⟩ := hxtrue
    have hpair : pairInput u v ≤ x := by
      intro w
      cases hw : pairInput u v w with
      | false => simp
      | true =>
        have hwuv : w = u ∨ w = v := by simpa [pairInput] using hw
        rcases hwuv with rfl | rfl
        · simp [hu]
        · simp [hv]
    have h := hf hpair
    rw [hpos u v huv] at h
    cases hfx : f x <;> simp_all
    exact (by decide : ¬ (true : Bool) ≤ false) h
  · exact hneg

end Boundary

namespace Color

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
  PEqualNP.Outside.L_meta_5012.Semantics

lemma orIn_val {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (i : Fin n)
    (hi : i ∈ orIn n C w) (hx : x i = true) : W n C x w = true := by
  rcases (orIn_mem n C w i).mp hi with h | ⟨k, hk, hreach, hop, hin⟩
  · rw [← h, W_input n C x i.val i.isLt]
    exact hx
  · apply reach_up n C x w k hreach
    apply W_or n C x k hk hop i.val hin (by have := i.isLt; omega)
    rw [W_input n C x i.val i.isLt]
    exact hx

lemma graphFun_pair_adj {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v : Fin n) (h : graphFun G ∅ (pairInput u v) = true) : G.Adj u v := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq] at h
  obtain ⟨a, b, hab, ha, hb⟩ := h
  have ha' : a = u ∨ a = v := by simpa [pairInput] using ha
  have hb' : b = u ∨ b = v := by simpa [pairInput] using hb
  rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
  · exact (G.irrefl hab).elim
  · exact hab
  · exact hab.symm
  · exact (G.irrefl hab).elim

lemma and_true_of_operands {n : ℕ} (C : Circuit) (hAO : IsAO2 n C)
    (a : ℕ) (ha : a < C.gates.length) (hop : (gateAt C a).op = GateOp.and)
    (x : Fin n → Bool) (h0 : W n C x (opnd C a 0) = true)
    (h1 : W n C x (opnd C a 1) = true) : W n C x (n + a) = true := by
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem' C a ha))
  have hp : p < n + a := hAO.2.1 a ha p (by rw [hin]; simp)
  have hq : q < n + a := hAO.2.1 a ha q (by rw [hin]; simp)
  have e0 : opnd C a 0 = p := by simp [opnd, hin]
  have e1 : opnd C a 1 = q := by simp [opnd, hin]
  rw [e0] at h0
  rw [e1] at h1
  rw [W_gate n C x a ha, hop, hin]
  simp [GateOp.eval, hp, hq, h0, h1]

lemma lam_has_common_neighbor {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C)
    (k : ℕ) (hk : k ∈ lam G C) :
    ∃ c : Fin n, ∀ u ∈ orIn n C (n + k), G.Adj u c := by
  classical
  obtain ⟨_, _, _, a, ha, b, hc, hr⟩ := Finset.mem_filter.mp hk
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hc
  refine ⟨c, ?_⟩
  intro u hu
  have huval : W n C (pairInput u c) (n + k) = true :=
    orIn_val C _ _ u hu (by simp [pairInput])
  have hbval : W n C (pairInput u c) (opnd C a b) = true :=
    reach_up n C _ _ k hr huval
  have hcside : c ∈ side (n := n) C a (1 - b) := by rw [hc]; simp
  have hcval : W n C (pairInput u c) (opnd C a (1 - b)) = true :=
    side_val n C _ a (1 - b) c hcside (by simp [pairInput])
  have htop := ha
  simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at htop
  obtain ⟨haN', hop, hbelow⟩ := htop
  apply graphFun_pair_adj G u c
  apply hbelow
  change W n C (pairInput u c) (n + a) = true
  have hb : b = 0 ∨ b = 1 := by omega
  rcases hb with rfl | rfl
  · exact and_true_of_operands C hAO a haN' hop _ hbval hcval
  · exact and_true_of_operands C hAO a haN' hop _ hcval hbval

lemma lam_monochromatic {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C) (s : Fin n → Bool)
    (hs : ∀ u v, G.Adj u v → s u ≠ s v) (k : ℕ) (hk : k ∈ lam G C) :
    ∀ u ∈ orIn n C (n + k), ∀ v ∈ orIn n C (n + k), s u = s v := by
  obtain ⟨c, hc⟩ := lam_has_common_neighbor G C hAO k hk
  intro u hu v hv
  have huc := hs u c (hc u hu)
  have hvc := hs v c (hc v hv)
  cases hsu : s u <;> cases hsv : s v <;> cases hsc : s c <;> simp_all

lemma tight_earlier_or_monochromatic {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C) (s : Fin n → Bool)
    (hs : ∀ u v, G.Adj u v → s u ≠ s v) (m : ℕ)
    (htight : orN G C \ lam G C = {m}) (k : ℕ) (hkm : k < m)
    (hk : k ∈ orN G C) :
    ∀ u ∈ orIn n C (n + k), ∀ v ∈ orIn n C (n + k), s u = s v := by
  apply lam_monochromatic G C hAO s hs k
  by_contra hn
  have hm : k ∈ orN G C \ lam G C := Finset.mem_sdiff.mpr ⟨hk, hn⟩
  rw [htight, Finset.mem_singleton] at hm
  omega

end Color
end PEqualNP.Outside.L_meta_5012


namespace PEqualNP.Outside.L_meta_5012.Patch

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
  PEqualNP.CleanedNonEdge PEqualNP.TopForm

def gateBit (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def stepWire (w : List Bool) (g : Gate) : List Bool := w ++ [gateBit w g]

def WiresLE (w z : List Bool) : Prop :=
  w.length = z.length ∧ ∀ i, w.getD i false = true → z.getD i false = true

def IsMonoGate (g : Gate) : Prop := g.op = GateOp.and ∨ g.op = GateOp.or

lemma monoGate_of_mem {C : Circuit} (hC : Monotone2 C) {g : Gate} (hg : g ∈ C.gates) :
    IsMonoGate g := by
  simpa [IsMonoGate] using (hC g hg).1

lemma bit_mono {w z : List Bool} (h : WiresLE w z) {g : Gate} (hg : IsMonoGate g)
    (hw : gateBit w g = true) : gateBit z g = true := by
  rcases hg with hop | hop
  · simp only [gateBit, hop, GateOp.eval, List.all_map, List.all_eq_true,
      Function.comp_apply, id_eq] at hw ⊢
    exact fun i hi => h.2 i (hw i hi)
  · simp only [gateBit, hop, GateOp.eval, List.any_map, List.any_eq_true,
      Function.comp_apply, id_eq] at hw ⊢
    obtain ⟨i, hi, hv⟩ := hw
    exact ⟨i, hi, h.2 i hv⟩

lemma append_mono {w z : List Bool} {a b : Bool} (h : WiresLE w z)
    (hab : a = true → b = true) : WiresLE (w ++ [a]) (z ++ [b]) := by
  refine ⟨by simp [h.1], ?_⟩
  intro i hi
  rw [List.getD_eq_getElem?_getD] at hi ⊢
  by_cases hlt : i < w.length
  · rw [List.getElem?_append_left hlt] at hi
    rw [List.getElem?_append_left (by rwa [← h.1])]
    simpa only [List.getD_eq_getElem?_getD] using h.2 i
      (by simpa only [List.getD_eq_getElem?_getD] using hi)
  · rw [List.getElem?_append_right (Nat.le_of_not_gt hlt)] at hi
    rw [List.getElem?_append_right (by rw [← h.1]; omega), ← h.1]
    cases hd : i - w.length with
    | zero =>
      simp only [hd, List.getElem?_cons_zero, Option.getD_some] at hi ⊢
      exact hab hi
    | succ k => simp [hd] at hi

lemma fold_mono (gs : List Gate) (hg : ∀ g ∈ gs, IsMonoGate g)
    {w z : List Bool} (h : WiresLE w z) :
    WiresLE (gs.foldl stepWire w) (gs.foldl stepWire z) := by
  induction gs generalizing w z with
  | nil => exact h
  | cons g gs ih =>
    exact ih (fun k hk => hg k (List.mem_cons_of_mem _ hk))
      (append_mono h (bit_mono h (hg g (by simp))))

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma fold_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (stepWire w g) (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma ofFn_getD {n : ℕ} (x : Fin n → Bool) (u : Fin n) :
    (List.ofFn x).getD u.val false = x u := by
  simp [List.getD_eq_getElem?_getD]

lemma ofFn_mono {n : ℕ} {x y : Fin n → Bool} (h : ∀ u, x u = true → y u = true) :
    WiresLE (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp, ?_⟩
  intro i hi
  by_cases hlt : i < n
  · rw [ofFn_getD y ⟨i, hlt⟩]
    exact h ⟨i, hlt⟩ (by simpa only [ofFn_getD x ⟨i, hlt⟩] using hi)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hlt)] at hi
    cases hi

def patch (C : Circuit) (j : ℕ) (g : Gate) : Circuit := ⟨C.gates.set j g, C.output⟩

def earlierWires (C : Circuit) (j : ℕ) (w : List Bool) : List Bool :=
  (C.gates.take j).foldl stepWire w

def off : Gate := ⟨GateOp.or, []⟩

def edgeGate {n : ℕ} (u v : Fin n) : Gate := ⟨GateOp.and, [u.val, v.val]⟩

lemma off_bit (w : List Bool) : gateBit w off = false := rfl

lemma edge_bit {n : ℕ} (C : Circuit) (j : ℕ) (x : Fin n → Bool) (u v : Fin n) :
    gateBit (earlierWires C j (List.ofFn x)) (edgeGate u v) = (x u && x v) := by
  simp only [gateBit, edgeGate, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
    List.all_nil, id_eq, Bool.and_true]
  unfold earlierWires
  rw [fold_getD_lt _ _ _ (by simp), fold_getD_lt _ _ _ (by simp),
    ofFn_getD, ofFn_getD]

lemma wires_patch {C : Circuit} {j : ℕ} (hj : j < C.gates.length) (g : Gate) (w : List Bool) :
    (patch C j g).wires w = (C.gates.drop (j + 1)).foldl stepWire (stepWire (earlierWires C j w) g) := by
  change (C.gates.set j g).foldl stepWire w = _
  rw [List.set_eq_take_append_cons_drop, ite_eq_left hj, List.foldl_append, List.foldl_cons]
  rfl

lemma original_patch {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    patch C j C.gates[j] = C := by
  cases C with
  | mk gates output =>
    change Circuit.mk (gates.set j gates[j]) output = Circuit.mk gates output
    congr 1
    exact List.set_getElem_self hj

lemma patch_mono {C : Circuit} (hC : Monotone2 C) {j : ℕ} (hj : j < C.gates.length)
    (g h : Gate) (w : List Bool)
    (hbit : gateBit (earlierWires C j w) g = true → gateBit (earlierWires C j w) h = true) :
    WiresLE ((patch C j g).wires w) ((patch C j h).wires w) := by
  rw [wires_patch hj, wires_patch hj]
  apply fold_mono _ (fun k hk => monoGate_of_mem hC (List.mem_of_mem_drop hk))
  exact append_mono ⟨rfl, fun _ h => h⟩ hbit

lemma patch_bit {n : ℕ} {C : Circuit} {j : ℕ} (hj : j < C.gates.length)
    (g : Gate) (x : Fin n → Bool) :
    gateVal n (patch C j g) j x = gateBit (earlierWires C j (List.ofFn x)) g := by
  have hlen : (earlierWires C j (List.ofFn x)).length = n + j := by
    unfold earlierWires
    rw [fold_length]
    simp [Nat.min_eq_left (Nat.le_of_lt hj)]
  unfold gateVal
  rw [wires_patch hj, fold_getD_lt _ _ _ (by simp [stepWire, hlen]), ← hlen]
  simp [stepWire, List.getD_eq_getElem?_getD]

lemma patch_isMono {C : Circuit} (hC : Monotone2 C) {j : ℕ} {g : Gate}
    (hg : IsMonoGate g) (hlen : g.inputs.length ≤ 2) : Monotone2 (patch C j g) := by
  intro k hk
  change k ∈ C.gates.set j g at hk
  rcases List.mem_or_eq_of_mem_set hk with hk | rfl
  · exact hC k hk
  · exact ⟨by simpa [IsMonoGate] using hg, hlen⟩

lemma gateAt_patch_ne (C : Circuit) (j k : ℕ) (g : Gate) (hne : j ≠ k) :
    gateAt (patch C j g) k = gateAt C k := by
  simp [patch, gateAt, List.getD_eq_getElem?_getD, List.getElem?_set_ne hne]

lemma graph_true {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
  simp [graphFun]

lemma pair_le {n : ℕ} {x : Fin n → Bool} {u v : Fin n}
    (hu : x u = true) (hv : x v = true) (k : Fin n) :
    pairInput u v k = true → x k = true := by
  simp only [pairInput, decide_eq_true_eq]
  rintro (rfl | rfl)
  · exact hu
  · exact hv

lemma circuit_mono {n : ℕ} {C : Circuit} (hC : Monotone2 C) {x y : Fin n → Bool}
    (hxy : ∀ u, x u = true → y u = true) :
    circuitFun n C x = true → circuitFun n C y = true :=
  (fold_mono C.gates (fun _ hg => monoGate_of_mem hC hg) (ofFn_mono hxy)).2 C.output

lemma mem_junk {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {j : ℕ} :
    j ∈ junk G C ↔ j < C.gates.length ∧ IsDirtyAnd n G C j := by
  unfold junk gatesWhere
  rw [Finset.mem_filter, Finset.mem_range]

lemma ao_mono {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) : Monotone2 C := by
  intro r hr
  exact ⟨by simpa using hAO.1 r hr, (hAO.2.2 r hr).le⟩

lemma patch_gate_ao {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) (r : Gate)
    (hrop : IsMonoGate r) (hrlen : r.inputs.length = 2)
    (hrback : ∀ i ∈ r.inputs, i < n + j) : IsAO2 n (patch C j r) := by
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    rcases List.mem_or_eq_of_mem_set hq with hq | rfl
    · exact hAO.1 q hq
    · exact hrop
  · intro k hk i hi
    have hkc : k < C.gates.length := by simpa [patch] using hk
    by_cases h : j = k
    · subst k
      have he : gateAt (patch C j r) j = r := by
        simp [gateAt, patch, List.getD_eq_getElem?_getD, hj]
      rw [he] at hi
      exact hrback i hi
    · rw [gateAt_patch_ne C j k r h] at hi
      exact hAO.2.1 k hkc i hi
  · intro q hq
    rcases List.mem_or_eq_of_mem_set hq with hq | rfl
    · exact hAO.2.2 q hq
    · exact hrlen

lemma patch_edge_ao {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) (u v : Fin n) :
    IsAO2 n (patch C j (edgeGate u v)) := by
  apply patch_gate_ao hAO hj
  · exact Or.inl rfl
  · rfl
  · intro i hi
    simp only [edgeGate, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact lt_of_lt_of_le u.isLt (Nat.le_add_right _ _)
    · exact lt_of_lt_of_le v.isLt (Nat.le_add_right _ _)

lemma gateVal_patch_before {n : ℕ} {C : Circuit} {j k : ℕ}
    (hj : j < C.gates.length) (hkj : k < j) (r : Gate) (x : Fin n → Bool) :
    gateVal n (patch C j r) k x = gateVal n C k x := by
  have hlen : (earlierWires C j (List.ofFn x)).length = n + j := by
    unfold earlierWires
    rw [fold_length]
    simp [Nat.min_eq_left hj.le]
  have hp (r : Gate) : gateVal n (patch C j r) k x =
      (earlierWires C j (List.ofFn x)).getD (n + k) false := by
    unfold gateVal
    rw [wires_patch hj, fold_getD_lt _ _ _ (by simp [stepWire, hlen]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (show n + k < (earlierWires C j (List.ofFn x)).length by omega)]
  rw [hp, ← hp C.gates[j], original_patch hj]

lemma repair_clean_gate {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (j : ℕ) (hAO : IsAO2 n C)
    (hF : circuitFun n C = graphFun G ∅) (hj : j < C.gates.length)
    (r : Gate) (hrop : IsMonoGate r) (hrlen : r.inputs.length = 2)
    (hrback : ∀ i ∈ r.inputs, i < n + j)
    (clean : ∀ x : Fin n → Bool,
      gateBit (earlierWires C j (List.ofFn x)) r = true → graphFun G ∅ x = true)
    (critical : ∀ a b, G.Adj a b → circuitFun n (patch C j off) (pairInput a b) = false →
      gateBit (earlierWires C j (List.ofFn (pairInput a b))) r = true) :
    let D := patch C j r
    IsAO2 n D ∧ circuitFun n D = graphFun G ∅ ∧ D.size = C.size ∧
      junk G D ⊆ junk G C ∧ j ∉ junk G D ∧
      (∀ k < j, k ∈ junk G C → k ∈ junk G D) := by
  have hC := ao_mono hAO
  let dropped := patch C j off
  let D := patch C j r
  have haoD : IsAO2 n D := patch_gate_ao hAO hj r hrop hrlen hrback
  have hmono : Monotone2 D := ao_mono haoD
  have hdom (x : Fin n → Bool) (hxG : graphFun G ∅ x = false) :
      WiresLE (D.wires (List.ofFn x)) (C.wires (List.ofFn x)) := by
    rw [← original_patch hj]
    apply patch_mono hC hj
    intro hx
    have hh := clean x hx
    rw [hxG] at hh
    cases hh
  have hlow (x : Fin n → Bool) :
      circuitFun n dropped x = true → circuitFun n D x = true := by
    exact (patch_mono hC hj off r (List.ofFn x)
      (by simp [off_bit])).2 C.output
  have allEdges (a b : Fin n) (hab : G.Adj a b) : circuitFun n D (pairInput a b) = true := by
    cases hcut : circuitFun n dropped (pairInput a b) with
    | true => exact hlow _ hcut
    | false =>
      have hle := patch_mono hC hj C.gates[j] r (List.ofFn (pairInput a b))
        (fun _ => critical a b hab hcut)
      rw [original_patch hj] at hle
      apply hle.2 C.output
      change circuitFun n C (pairInput a b) = true
      rw [hF]
      exact (graph_true G (pairInput a b)).mpr
        ⟨a, b, hab, by simp [pairInput], by simp [pairInput]⟩
  have hcompute : circuitFun n D = graphFun G ∅ := by
    funext x
    cases hG : graphFun G ∅ x with
    | true =>
      obtain ⟨a, b, hab, ha, hb⟩ := (graph_true G x).mp hG
      exact circuit_mono hmono (pair_le ha hb) (allEdges a b hab)
    | false =>
      cases hD : circuitFun n D x with
      | false => rfl
      | true =>
        have hout : circuitFun n C x = true := (hdom x hG).2 C.output hD
        rw [hF, hG] at hout
        cases hout
  have hlen : D.gates.length = C.gates.length := List.length_set
  have hclean : j ∉ junk G D := by
    intro h
    obtain ⟨x, hx, hxG⟩ := (mem_junk.mp h).2.2.2
    change gateVal n (patch C j r) j x = true at hx
    rw [patch_bit hj] at hx
    have hh := clean x hx
    rw [hxG] at hh
    cases hh
  have hsub : junk G D ⊆ junk G C := by
    intro k hk
    have hne : j ≠ k := fun he => hclean (he.symm ▸ hk)
    obtain ⟨hklen, hkop, _, x, hx, hxG⟩ := mem_junk.mp hk
    have hkc : k < C.gates.length := hlen ▸ hklen
    have hcop : (gateAt C k).op = GateOp.and := by
      rwa [show gateAt D k = gateAt C k from gateAt_patch_ne C j k r hne] at hkop
    exact mem_junk.mpr ⟨hkc, hcop, hkc, x, (hdom x hxG).2 (n + k) hx, hxG⟩
  refine ⟨haoD, hcompute, hlen, hsub, hclean, ?_⟩
  intro k hkj hk
  obtain ⟨hklen, hkop, _, x, hx, hxG⟩ := mem_junk.mp hk
  apply mem_junk.mpr
  refine ⟨by simpa [patch] using hklen, ?_, by simpa [patch] using hklen, x, ?_, hxG⟩
  · rw [gateAt_patch_ne C j k r (by omega)]
    exact hkop
  · rwa [gateVal_patch_before hj hkj]

lemma repair_unique_edge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (j : ℕ) (hAO : IsAO2 n C)
    (hF : circuitFun n C = graphFun G ∅) (hjunk : j ∈ junk G C)
    (u v : Fin n) (huv : G.Adj u v)
    (unique : ∀ a b, G.Adj a b → circuitFun n (patch C j off) (pairInput a b) = false →
      pairInput a b = pairInput u v) :
    let D := patch C j (edgeGate u v)
    IsAO2 n D ∧ circuitFun n D = graphFun G ∅ ∧ D.size = C.size ∧
      junk G D ⊆ junk G C ∧ j ∉ junk G D ∧
      (∀ k < j, k ∈ junk G C → k ∈ junk G D) := by
  apply repair_clean_gate G C j hAO hF (mem_junk.mp hjunk).1
  · exact Or.inl rfl
  · rfl
  · intro i hi
    simp only [edgeGate, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact lt_of_lt_of_le u.isLt (Nat.le_add_right _ _)
    · exact lt_of_lt_of_le v.isLt (Nat.le_add_right _ _)
  · intro x hx
    rw [edge_bit, Bool.and_eq_true] at hx
    exact (graph_true G x).mpr ⟨u, v, huv, hx.1, hx.2⟩
  · intro a b hab hlost
    rw [unique a b hab hlost, edge_bit]
    simp [pairInput]

lemma no_clean_later_replacement
    (rungOne : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit) (s : Fin n → Bool),
      (∀ u v, G.Adj u v → s u ≠ s v) → NoFourCycle G → IsLeastAO G C →
        (junk G C).card ≠ 1)
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : NoFourCycle G) (hL : IsLeastAO G C) (g h : ℕ)
    (hgh : g < h) (hJ : junk G C = {g, h})
    (r : Gate) (hrop : IsMonoGate r) (hrlen : r.inputs.length = 2)
    (hrback : ∀ i ∈ r.inputs, i < n + h)
    (clean : ∀ x : Fin n → Bool,
      gateBit (earlierWires C h (List.ofFn x)) r = true → graphFun G ∅ x = true)
    (critical : ∀ a b, G.Adj a b → circuitFun n (patch C h off) (pairInput a b) = false →
      gateBit (earlierWires C h (List.ofFn (pairInput a b))) r = true) : False := by
  have hgJ : g ∈ junk G C := by simp [hJ]
  have hhJ : h ∈ junk G C := by simp [hJ]
  obtain ⟨hAO, hF, hsize, hsub, hclean, hbefore⟩ :=
    repair_clean_gate G C h hL.1 hL.2.1 (mem_junk.mp hhJ).1 r hrop hrlen hrback clean critical
  let D := patch C h r
  have hDL : IsLeastAO G D := by
    refine ⟨hAO, hF, ?_⟩
    intro E hE hEF
    rw [hsize]
    exact hL.2.2 E hE hEF
  have hDJ : junk G D = {g} := by
    apply Finset.ext
    intro k
    constructor
    · intro hk
      have hkC := hsub hk
      rw [hJ] at hkC
      simp only [Finset.mem_insert, Finset.mem_singleton] at hkC
      rcases hkC with rfl | rfl
      · simp
      · exact False.elim (hclean hk)
    · intro hk
      have heq : k = g := Finset.mem_singleton.mp hk
      subst k
      exact hbefore g hgh hgJ
  apply rungOne n G D s hcol h4 hDL
  rw [hDJ]
  exact Finset.card_singleton g

lemma earlier_read_eq_wireVal {n : ℕ} {C : Circuit} {j w : ℕ}
    (hj : j < C.gates.length) (hw : w < n + j) (x : Fin n → Bool) :
    (earlierWires C j (List.ofFn x)).getD w false = wireVal n C w x := by
  have hlen : (earlierWires C j (List.ofFn x)).length = n + j := by
    unfold earlierWires
    rw [fold_length]
    simp [Nat.min_eq_left hj.le]
  calc
    (earlierWires C j (List.ofFn x)).getD w false =
        ((patch C j C.gates[j]).wires (List.ofFn x)).getD w false := by
      rw [wires_patch hj, fold_getD_lt _ _ _ (by simp [stepWire, hlen]; omega)]
      simp [stepWire, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (show w < (earlierWires C j (List.ofFn x)).length by omega)]
    _ = wireVal n C w x := by rw [original_patch hj]; rfl

def rawStarGate {n : ℕ} (u : Fin n) (w : ℕ) : Gate := ⟨GateOp.and, [u.val, w]⟩

lemma rawStar_bit {n : ℕ} {C : Circuit} {j w : ℕ}
    (hj : j < C.gates.length) (hw : w < n + j) (x : Fin n → Bool) (u : Fin n) :
    gateBit (earlierWires C j (List.ofFn x)) (rawStarGate u w) =
      (x u && wireVal n C w x) := by
  simp only [gateBit, rawStarGate, GateOp.eval, List.map_cons, List.map_nil,
    List.all_cons, List.all_nil, id_eq, Bool.and_true]
  rw [earlier_read_eq_wireVal hj hw]
  unfold earlierWires
  rw [fold_getD_lt _ _ _ (by simp), ofFn_getD]

lemma no_clean_later_star
    (rungOne : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit) (s : Fin n → Bool),
      (∀ u v, G.Adj u v → s u ≠ s v) → NoFourCycle G → IsLeastAO G C →
        (junk G C).card ≠ 1)
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : NoFourCycle G) (hL : IsLeastAO G C) (g h : ℕ)
    (hgh : g < h) (hJ : junk G C = {g, h}) (u : Fin n) (w : ℕ) (hw : w < n + h)
    (clean : ∀ x : Fin n → Bool,
      x u = true → wireVal n C w x = true → graphFun G ∅ x = true)
    (critical : ∀ a b, G.Adj a b → circuitFun n (patch C h off) (pairInput a b) = false →
      pairInput a b u = true ∧ wireVal n C w (pairInput a b) = true) : False := by
  have hhJ : h ∈ junk G C := by simp [hJ]
  have hh := (mem_junk.mp hhJ).1
  apply no_clean_later_replacement rungOne G C s hcol h4 hL g h hgh hJ (rawStarGate u w)
  · exact Or.inl rfl
  · rfl
  · intro i hi
    simp only [rawStarGate, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact lt_of_lt_of_le u.isLt (Nat.le_add_right _ _)
    · exact hw
  · intro x hx
    rw [rawStar_bit hh hw, Bool.and_eq_true] at hx
    exact clean x hx.1 hx.2
  · intro a b hab hlost
    rw [rawStar_bit hh hw, Bool.and_eq_true]
    exact critical a b hab hlost

lemma no_unique_later_edge
    (rungOne : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit) (s : Fin n → Bool),
      (∀ u v, G.Adj u v → s u ≠ s v) → NoFourCycle G → IsLeastAO G C →
        (junk G C).card ≠ 1)
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : NoFourCycle G) (hL : IsLeastAO G C) (g h : ℕ)
    (hgh : g < h) (hJ : junk G C = {g, h}) (u v : Fin n) (huv : G.Adj u v)
    (unique : ∀ a b, G.Adj a b → circuitFun n (patch C h off) (pairInput a b) = false →
      pairInput a b = pairInput u v) : False := by
  have hgJ : g ∈ junk G C := by simp [hJ]
  have hhJ : h ∈ junk G C := by simp [hJ]
  obtain ⟨hAO, hF, hsize, hsub, hclean, hbefore⟩ :=
    repair_unique_edge G C h hL.1 hL.2.1 hhJ u v huv unique
  let D := patch C h (edgeGate u v)
  have hDL : IsLeastAO G D := by
    refine ⟨hAO, hF, ?_⟩
    intro E hE hEF
    rw [hsize]
    exact hL.2.2 E hE hEF
  have hDJ : junk G D = {g} := by
    apply Finset.ext
    intro k
    constructor
    · intro hk
      have hkC := hsub hk
      rw [hJ] at hkC
      simp only [Finset.mem_insert, Finset.mem_singleton] at hkC
      rcases hkC with rfl | rfl
      · simp
      · exact False.elim (hclean hk)
    · intro hk
      have heq : k = g := Finset.mem_singleton.mp hk
      subst k
      exact hbefore g hgh hgJ
  apply rungOne n G D s hcol h4 hDL
  rw [hDJ]
  exact Finset.card_singleton g

lemma least_nonempty_graph {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (j : ℕ) (hj : j ∈ junk G C) :
    ∃ u v, G.Adj u v := by
  classical
  by_contra hn
  push Not at hn
  let D : Circuit := ⟨[], n⟩
  have hD : IsAO2 n D := by
    simp [IsAO2, AndOrOnly, ReadsBack, D]
  have hDF : circuitFun n D = graphFun G ∅ := by
    funext x
    simp [circuitFun, Circuit.eval, Circuit.wires, D, graphFun, hn,
      List.getD_eq_getElem?_getD]
  have hsize := hL.2.2 D hD hDF
  have hjlen := (mem_junk.mp hj).1
  simp only [Circuit.size, D, List.length_nil] at hsize
  omega

lemma later_has_two_essential_edges
    (rungOne : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit) (s : Fin n → Bool),
      (∀ u v, G.Adj u v → s u ≠ s v) → NoFourCycle G → IsLeastAO G C →
        (junk G C).card ≠ 1)
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : NoFourCycle G) (hL : IsLeastAO G C) (g h : ℕ)
    (hgh : g < h) (hJ : junk G C = {g, h}) :
    ∃ u v a b : Fin n, G.Adj u v ∧ G.Adj a b ∧
      circuitFun n (patch C h off) (pairInput u v) = false ∧
      circuitFun n (patch C h off) (pairInput a b) = false ∧
      pairInput u v ≠ pairInput a b := by
  classical
  have choose_other (u v : Fin n) (huv : G.Adj u v) :
      ∃ a b : Fin n, G.Adj a b ∧
        circuitFun n (patch C h off) (pairInput a b) = false ∧
        pairInput a b ≠ pairInput u v := by
    by_contra hn
    push Not at hn
    exact no_unique_later_edge rungOne G C s hcol h4 hL g h hgh hJ u v huv hn
  have hgJ : g ∈ junk G C := by simp [hJ]
  obtain ⟨u, v, huv⟩ := least_nonempty_graph G C hL g hgJ
  obtain ⟨a, b, hab, hlab, _⟩ := choose_other u v huv
  obtain ⟨c, d, hcd, hlcd, hne⟩ := choose_other a b hab
  exact ⟨a, b, c, d, hab, hcd, hlab, hlcd, hne.symm⟩

end PEqualNP.Outside.L_meta_5012.Patch
namespace PEqualNP.Outside.L_meta_5012.NoDeadPatch

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
  PEqualNP.TopForm PEqualNP.Outside.L_meta_5012.Patch

lemma no_clean_star_sole_reader {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hL : IsLeastAO G C) (g h : ℕ)
    (hgh : g < h) (hgJ : g ∈ junk G C) (hhJ : h ∈ junk G C)
    (hread : readers n C g = {h}) (u : Fin n) (w : ℕ)
    (hw : w < n + h) (hwg : w ≠ n + g)
    (clean : ∀ x : Fin n → Bool,
      x u = true → wireVal n C w x = true → graphFun G ∅ x = true)
    (critical : ∀ a b, G.Adj a b → circuitFun n (patch C h off) (pairInput a b) = false →
      pairInput a b u = true ∧ wireVal n C w (pairInput a b) = true) : False := by
  have hh : h < C.gates.length := (mem_junk.mp hhJ).1
  have hrback : ∀ i ∈ (rawStarGate u w).inputs, i < n + h := by
    intro i hi
    simp only [rawStarGate, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact lt_of_lt_of_le u.isLt (Nat.le_add_right _ _)
    · exact hw
  have hc : ∀ x : Fin n → Bool,
      gateBit (earlierWires C h (List.ofFn x)) (rawStarGate u w) = true → graphFun G ∅ x = true := by
    intro x hx
    rw [rawStar_bit hh hw, Bool.and_eq_true] at hx
    exact clean x hx.1 hx.2
  have hp : ∀ a b, G.Adj a b → circuitFun n (patch C h off) (pairInput a b) = false →
      gateBit (earlierWires C h (List.ofFn (pairInput a b))) (rawStarGate u w) = true := by
    intro a b hab hz
    rw [rawStar_bit hh hw, Bool.and_eq_true]
    exact critical a b hab hz
  obtain ⟨hAO, hF, hsize, _, _, hbefore⟩ := repair_clean_gate G C h hL.1 hL.2.1 hh
    (rawStarGate u w) (Or.inl rfl) rfl hrback hc hp
  let D := patch C h (rawStarGate u w)
  have hDL : IsLeastAO G D := by
    refine ⟨hAO, hF, ?_⟩
    intro F hFAO hFF
    rw [hsize]
    exact hL.2.2 F hFAO hFF
  have hgD : g ∈ junk G D := hbefore g hgh hgJ
  have hlen : D.gates.length = C.gates.length := by simp [D, patch]
  obtain ⟨k, hk⟩ := PEqualNP.Outside.L_meta_5012.Structural.leastRead hDL
    (PEqualNP.Outside.L_meta_5012.Structural.junkData hgD).1
    (PEqualNP.Outside.L_meta_5012.Structural.junkNotBelow hgD)
  have hkd := Finset.mem_filter.mp hk
  have hkin : n + g ∈ (gateAt D k).inputs := hkd.2
  by_cases hkh : k = h
  · subst k
    have heq : gateAt D h = rawStarGate u w := by
      simp [D, patch, gateAt, List.getD_eq_getElem?_getD, hh]
    rw [heq] at hkin
    simp only [rawStarGate, List.mem_cons, List.not_mem_nil, or_false] at hkin
    rcases hkin with hn | hn
    · have := u.isLt
      omega
    · exact hwg hn.symm
  · have heq : gateAt D k = gateAt C k := gateAt_patch_ne C h k (rawStarGate u w) (Ne.symm hkh)
    rw [heq] at hkin
    have hkC : k ∈ readers n C g := by
      apply Finset.mem_filter.mpr
      refine ⟨?_, hkin⟩
      simpa only [hlen] using hkd.1
    rw [hread, Finset.mem_singleton] at hkC
    exact hkh hkC

end PEqualNP.Outside.L_meta_5012.NoDeadPatch

namespace PEqualNP.Outside.L_meta_5012.Tight

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open PEqualNP.Outside.L_meta_5012.Structural PEqualNP.Outside.L_meta_5012 PEqualNP.Outside.L_meta_5012.Trace

def PureWire (n : ℕ) (C : Circuit) (w : ℕ) : Prop :=
  ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → ¬ OrReaches n C w j

lemma pure_wire_value {n : ℕ} (C : Circuit) (hAO : IsAO2 n C) (w : ℕ)
    (hpure : PureWire n C w) (x : Fin n → Bool) :
    val C (List.ofFn x) w = setOr (orIn n C w) x := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hv
    obtain ⟨z, hp, hz, hzi | ⟨j, hj, heq, hjo⟩⟩ := or_trace (n := n) (C := C) (by simp) w hv
    · apply decide_eq_true
      exact ⟨⟨z, hzi⟩, reach_mem_orIn ⟨z, hzi⟩ hp, (val_ofFn C x ⟨z, hzi⟩).symm.trans hz⟩
    · subst z
      have hreach := reach_orReaches hp j rfl hj
      have hand := (hAO.1 _ (gateAt_mem hj)).resolve_right hjo
      exact False.elim (hpure j hj hand hreach)
  · intro hs
    obtain ⟨a, ha, hxa⟩ := of_decide_eq_true hs
    exact orStep_up (n := n) (by simp) (mem_orIn_reach a ha) ((val_ofFn C x a).trans hxa)

lemma inner_operand_pure {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g h : ℕ) (hAO : IsAO2 n C) (hT : TopForm G C)
    (hJ : junk G C = {g, h}) (hgh : g < h) (b : Fin 2) :
    PureWire n C (opnd C g b) := by
  have hg : g ∈ junk G C := by simp [hJ]
  intro j hj hja hreach
  have hjunk := operandOrAndJunk hAO hT (junkData hg).1 (junkData hg).2.1 hreach hja
  have hle := orStep_le (orReaches_reach j _ hreach).1
  have hb := opndBound hAO (junkData hg).1 b
  simp only [hJ, Finset.mem_insert, Finset.mem_singleton] at hjunk
  omega

lemma outer_other_pure {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g h : ℕ) (hAO : IsAO2 n C) (hT : TopForm G C)
    (hJ : junk G C = {g, h}) (hreadg : readers n C g = {h})
    (b : Fin 2) (hne : opnd C h b ≠ n + g) : PureWire n C (opnd C h b) := by
  have hh : h ∈ junk G C := by simp [hJ]
  intro j hj hja hreach
  have hjunk := operandOrAndJunk hAO hT (junkData hh).1 (junkData hh).2.1 hreach hja
  simp only [hJ, Finset.mem_insert, Finset.mem_singleton] at hjunk
  rcases hjunk with he | he
  · rw [he] at hreach
    rcases lastOrBefore (orReaches_reach g _ hreach).1 with heq | ⟨k, hk, ho, hin, _, _⟩
    · exact hne heq
    · have hkr : k ∈ readers n C g := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hin⟩
      rw [hreadg, Finset.mem_singleton] at hkr
      rw [hkr, (junkData hh).2.1] at ho
      cases ho
  · have hle := orStep_le (orReaches_reach j _ hreach).1
    have hb := opndBound hAO (junkData hh).1 b
    omega

lemma pure_wire_monochromatic {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (s : Fin n → Bool)
    (hcol : ∀ u v, G.Adj u v → s u ≠ s v) (m : ℕ)
    (hbudget : orN G C \ lam G C = {m}) (hm : m < C.gates.length)
    (w : ℕ) (hw : w < n + m) (hpure : PureWire n C w) :
    ∃ t : Bool, ∀ a ∈ orIn n C w, s a = t := by
  classical
  by_cases hs : (orIn n C w).Nonempty
  · obtain ⟨a, ha⟩ := hs
    refine ⟨s a, ?_⟩
    intro b hb
    by_cases hwi : w < n
    · have eqval : ∀ v ∈ orIn n C w, v.val = w := by
        intro v hv
        simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hv
        rcases hv with hv | ⟨j, _, hreach, _⟩
        · exact hv
        · have hn := hreach.1
          omega
      have heq : b = a := Fin.ext ((eqval b hb).trans (eqval a ha).symm)
      exact congrArg s heq
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hjm : j < m := by omega
      have hj : j < C.gates.length := by omega
      have hor : (gateAt C j).op = GateOp.or := by
        rcases hAO.1 _ (gateAt_mem hj) with hand | hor
        · exact False.elim (hpure j hj hand ((orReaches_iff n C j j).mpr ⟨hj, Or.inl rfl⟩))
        · exact hor
      have hnb : ¬ BelowF G C j := by
        intro hbelow
        have hval : gateVal n C j (pairInput a a) = true :=
          orStep_up (n := n) (by simp) (mem_orIn_reach a ha)
            ((val_ofFn C (pairInput a a) a).trans (by simp [pairInput]))
        have hadj := (graph_pair_iff G a a).mp (hbelow _ hval)
        exact G.loopless.irrefl a hadj
      have hjN : j ∈ orN G C := by
        simpa only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] using
          And.intro hj (And.intro hor hnb)
      exact Color.tight_earlier_or_monochromatic G C hAO s hcol m hbudget j hjm hjN b hb a ha
  · exact ⟨false, fun a ha => False.elim (hs ⟨a, ha⟩)⟩

lemma tight_three_factors {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g h : ℕ) (hAO : IsAO2 n C) (hT : TopForm G C)
    (hJ : junk G C = {g, h}) (hgh : g < h) (hreadg : readers n C g = {h}) :
    ∃ W : Fin 3 → ℕ,
      (∀ i, W i < n + h ∧ W i ≠ n + g ∧ PureWire n C (W i)) ∧
      ∀ x : Fin n → Bool, gateVal n C h x = true ↔
        ∀ i, setOr (orIn n C (W i)) x = true := by
  have hg : g ∈ junk G C := by simp [hJ]
  have hh : h ∈ junk G C := by simp [hJ]
  have hgr : g < C.gates.length := (junkData hg).1
  have hhr : h < C.gates.length := (junkData hh).1
  have hread : h ∈ readers n C g := by simp [hreadg]
  obtain ⟨b, hb⟩ := inputsAsOpnd hAO hhr (readData hread).2
  have hb' : opnd C h b = n + g := hb.symm
  let w0 := opnd C g 0
  let w1 := opnd C g 1
  let q := opnd C h (1 - b)
  let w2 := if q = n + g then w0 else q
  let W : Fin 3 → ℕ := fun i => if i = 0 then w0 else if i = 1 then w1 else w2
  have hw0 := opndBound hAO hgr 0
  have hw1 := opndBound hAO hgr 1
  have hq := opndBound hAO hhr (1 - b)
  have hp0 : PureWire n C w0 := inner_operand_pure G C g h hAO hT hJ hgh 0
  have hp1 : PureWire n C w1 := inner_operand_pure G C g h hAO hT hJ hgh 1
  have hw2 : w2 < n + h ∧ w2 ≠ n + g ∧ PureWire n C w2 := by
    by_cases he : q = n + g
    · simp only [w2, if_pos he]
      exact ⟨by dsimp [w0]; omega, by dsimp [w0]; omega, hp0⟩
    · simp only [w2, if_neg he]
      exact ⟨hq, he, outer_other_pure G C g h hAO hT hJ hreadg (1 - b) he⟩
  have hW : ∀ i, W i < n + h ∧ W i ≠ n + g ∧ PureWire n C (W i) := by
    intro i
    fin_cases i
    · simpa [W] using (show w0 < n + h ∧ w0 ≠ n + g ∧ PureWire n C w0 from
        ⟨by dsimp [w0]; omega, by dsimp [w0]; omega, hp0⟩)
    · simpa [W] using (show w1 < n + h ∧ w1 ≠ n + g ∧ PureWire n C w1 from
        ⟨by dsimp [w1]; omega, by dsimp [w1]; omega, hp1⟩)
    · simpa [W] using hw2
  refine ⟨W, hW, ?_⟩
  intro x
  have hgval : gateVal n C g x = true ↔
      val C (List.ofFn x) w0 = true ∧ val C (List.ofFn x) w1 = true :=
    andValBoth hAO hgr (junkData hg).2.1 x
  have hhval : gateVal n C h x = true ↔
      gateVal n C g x = true ∧ val C (List.ofFn x) q = true := by
    rw [andValBoth hAO hhr (junkData hh).2.1 x]
    have hbcase : b = 0 ∨ b = 1 := by omega
    rcases hbcase with rfl | rfl
    · change (_ ∧ _) ↔ (_ ∧ _)
      rw [hb']
      rfl
    · change (_ ∧ _) ↔ (_ ∧ _)
      rw [hb']
      exact and_comm
  have hWval : (∀ i, setOr (orIn n C (W i)) x = true) ↔
      (val C (List.ofFn x) w0 = true ∧ val C (List.ofFn x) w1 = true ∧
        val C (List.ofFn x) w2 = true) := by
    constructor
    · intro hi
      have h0 := (pure_wire_value C hAO (W 0) (hW 0).2.2 x).trans (hi 0)
      have h1 := (pure_wire_value C hAO (W 1) (hW 1).2.2 x).trans (hi 1)
      have h2 := (pure_wire_value C hAO (W 2) (hW 2).2.2 x).trans (hi 2)
      exact ⟨by simpa [W] using h0, by simpa [W] using h1, by simpa [W] using h2⟩
    · rintro ⟨h0, h1, h2⟩ i
      rw [← pure_wire_value C hAO (W i) (hW i).2.2 x]
      fin_cases i
      · simpa [W] using h0
      · simpa [W] using h1
      · simpa [W] using h2
  rw [hWval, hhval]
  by_cases he : q = n + g
  · simp only [w2, if_pos he, he]
    change (gateVal n C g x = true ∧ gateVal n C g x = true) ↔ _
    rw [and_self, hgval]
    tauto
  · simp only [w2, if_neg he]
    rw [hgval]
    tauto

lemma tight_clean_star {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool)
    (hcol : ∀ u v, G.Adj u v → s u ≠ s v) (h4 : NoFourCycle G)
    (g h m : ℕ) (hL : IsLeastAO G C) (hT : TopForm G C)
    (hcen : centreless G C = ∅) (hJ : junk G C = {g, h}) (hgh : g < h)
    (hreadg : readers n C g = {h}) (hreadh : readers n C h = {m})
    (hbudget : orN G C \ lam G C = {m}) :
    ∃ (u : Fin n) (w : ℕ), w < n + h ∧ w ≠ n + g ∧
      (∀ x : Fin n → Bool, x u = true → wireVal n C w x = true → graphFun G ∅ x = true) ∧
      ∀ a b, G.Adj a b → circuitFun n (cut C h) (pairInput a b) = false →
        pairInput a b u = true ∧ wireVal n C w (pairInput a b) = true := by
  classical
  let E : Finset (Fin n × Fin n) := Finset.univ.filter fun p =>
    G.Adj p.1 p.2 ∧ circuitFun n (cut C h) (pairInput p.1 p.2) = false
  have hEmem (a b : Fin n) : (a, b) ∈ E ↔
      G.Adj a b ∧ circuitFun n (cut C h) (pairInput a b) = false := by
    simp [E]
  by_cases hEn : E.Nonempty
  · obtain ⟨W, hW, hsem⟩ := tight_three_factors G C g h hL.1 hT hJ hgh hreadg
    have hmread : m ∈ readers n C h := by simp [hreadh]
    have hhm := readLt hL.1 hmread
    have hm := (readData hmread).1
    let S : Fin 3 → Finset (Fin n) := fun i => orIn n C (W i)
    have hcolors : ∀ i : Fin 3, ∃ c : Bool, ∀ a ∈ S i, s a = c := by
      intro i
      exact pure_wire_monochromatic G C hL.1 s hcol m hbudget hm (W i)
        (by have := (hW i).1; omega) (hW i).2.2
    let t : Fin 3 → Bool := fun i => Classical.choose (hcolors i)
    have ht : ∀ i, ∀ a ∈ S i, s a = t i := fun i => Classical.choose_spec (hcolors i)
    obtain ⟨r, hr, hfilters⟩ := tight_raw_critical_filter G C g h m hL hT hcen hJ hgh
      hreadg hreadh hbudget
    have hadj : ∀ p ∈ E, G.Adj p.1 p.2 := by
      intro p hp
      exact (Finset.mem_filter.mp hp).2.1
    have hcutE : ∀ p ∈ E, circuitFun n (cut C h) (pairInput p.1 p.2) = false := by
      intro p hp
      exact (Finset.mem_filter.mp hp).2.2
    have hpairs : ∀ p ∈ E, ∀ i, p.1 ∈ S i ∨ p.2 ∈ S i := by
      intro p hp i
      have hhval := critical_outer_true G C g h hL hT hcen hJ hreadg p.1 p.2
        (hadj p hp) (hcutE p hp)
      have hs := (hsem (pairInput p.1 p.2)).mp hhval i
      simpa only [setOr_pair, decide_eq_true_eq] using hs
    have hne : ∀ p ∈ E, r ≠ p.1 ∧ r ≠ p.2 := by
      intro p hp
      have hf := hfilters p.1 p.2 (hadj p hp) (hcutE p hp)
      exact ⟨hf.1, hf.2.1⟩
    have hfilt : ∀ p ∈ E,
        (PEqualNP.Outside.L_meta_5012.Geometry.clauseClean G S p.1 ∧ G.Adj r p.1) ∨
        (PEqualNP.Outside.L_meta_5012.Geometry.clauseClean G S p.2 ∧ G.Adj r p.2) := by
      intro p hp
      obtain ⟨_, _, w, hw, hrw, hcw⟩ := hfilters p.1 p.2 (hadj p hp) (hcutE p hp)
      have hcs : PEqualNP.Outside.L_meta_5012.Geometry.clauseClean G S w := by
        intro x hxw hhit
        apply hcw x ?_ hxw
        apply (hsem x).mpr
        intro i
        exact decide_eq_true (hhit i)
      rcases hw with he | he
      · rw [he] at hcs hrw
        exact Or.inl ⟨hcs, hrw⟩
      · rw [he] at hcs hrw
        exact Or.inr ⟨hcs, hrw⟩
    obtain ⟨v, i, huniv, hcover⟩ := PEqualNP.Outside.L_meta_5012.Geometry.monochrome_unoriented_star
      G s hcol h4 S t ht E hEn hadj hpairs r hne hfilt
    refine ⟨v, W i, (hW i).1, (hW i).2.1, ?_, ?_⟩
    · intro x hxv hxw
      have hraw : setOr (S i) x = true :=
        (pure_wire_value C hL.1 (W i) (hW i).2.2 x).symm.trans hxw
      obtain ⟨a, ha, hxa⟩ := of_decide_eq_true hraw
      exact (PEqualNP.Outside.L_meta_5012.Geometry.graph_true G x).mpr ⟨v, a, huniv a ha, hxv, hxa⟩
    · intro a b hab hzero
      have hp : (a, b) ∈ E := (hEmem a b).mpr ⟨hab, hzero⟩
      obtain he | he := hcover (a, b) hp
      · obtain ⟨hav, hb⟩ := he
        refine ⟨decide_eq_true (Or.inl hav.symm), ?_⟩
        change val C (List.ofFn (pairInput a b)) (W i) = true
        rw [pure_wire_value C hL.1 (W i) (hW i).2.2 _, setOr_pair]
        exact decide_eq_true (Or.inr hb)
      · obtain ⟨hbv, ha⟩ := he
        refine ⟨decide_eq_true (Or.inr hbv.symm), ?_⟩
        change val C (List.ofFn (pairInput a b)) (W i) = true
        rw [pure_wire_value C hL.1 (W i) (hW i).2.2 _, setOr_pair]
        exact decide_eq_true (Or.inl ha)
  · have hg : g ∈ junk G C := by simp [hJ]
    obtain ⟨u, v, huv⟩ := PEqualNP.Outside.L_meta_5012.Patch.least_nonempty_graph G C hL g hg
    refine ⟨u, v.val, by have := v.isLt; omega, by have := v.isLt; omega, ?_, ?_⟩
    · intro x hxu hxv
      change val C (List.ofFn x) v.val = true at hxv
      rw [val_ofFn C x v] at hxv
      exact (PEqualNP.Outside.L_meta_5012.Geometry.graph_true G x).mpr ⟨u, v, huv, hxu, hxv⟩
    · intro a b hab hz
      exact False.elim (hEn ⟨(a, b), (hEmem a b).mpr ⟨hab, hz⟩⟩)

lemma tight_exception_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool)
    (hcol : ∀ u v, G.Adj u v → s u ≠ s v) (h4 : NoFourCycle G)
    (g h m : ℕ) (hL : IsLeastAO G C) (hT : TopForm G C)
    (hcen : centreless G C = ∅) (hJ : junk G C = {g, h}) (hgh : g < h)
    (hreadg : readers n C g = {h}) (hreadh : readers n C h = {m})
    (hbudget : orN G C \ lam G C = {m}) : False := by
  obtain ⟨u, w, hw, hwg, hclean, hcritical⟩ := tight_clean_star G C s hcol h4 g h m
    hL hT hcen hJ hgh hreadg hreadh hbudget
  exact NoDeadPatch.no_clean_star_sole_reader G C hL g h hgh (by simp [hJ])
    (by simp [hJ]) hreadg u w hw hwg hclean hcritical

end PEqualNP.Outside.L_meta_5012.Tight

namespace PEqualNP.Outside.L_meta_5012

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

lemma two_junk_resource_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool)
    (hcol : ∀ u v, G.Adj u v → s u ≠ s v) (h4 : NoFourCycle G)
    (hL : IsLeastAO G C) (hT : TopForm G C) (hJ : (junk G C).card = 2) :
    2 ≤ 2 * (centreless G C).card + (orN G C \ lam G C).card := by
  rcases Structural.dichotomy hL hT hJ with hbound |
    ⟨g, h, m, hJ, _, hcen, hreadg, hreadh, hbudget, _⟩
  · exact hbound
  · have hgh : g < h := Structural.readLt hL.1 (by simp [hreadg])
    exact False.elim (Tight.tight_exception_false G C s hcol h4 g h m
      hL hT hcen hJ hgh hreadg hreadh hbudget)

end PEqualNP.Outside.L_meta_5012

namespace PEqualNP.Outside.L_meta_5012

open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover

def clauseProduct {n k : ℕ} (S : Fin k → Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∀ i, ∃ a ∈ S i, x a = true)

lemma common_raw_clean_replacement {n k : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : PEqualNP.TopForm.NoFourCycle G)
    (S : Fin k → Finset (Fin n)) (t : Fin k → Bool)
    (hmono : ∀ i, ∀ a ∈ S i, s a = t i)
    (context : (Fin n → Bool) → Bool → Bool)
    (hcontext : ∀ x y b c, (∀ v, x v = true → y v = true) →
      (b = true → c = true) → context x b = true → context y c = true)
    (hF : ∀ x, context x (clauseProduct S x) = graphFun G ∅ x)
    (E : Finset (Fin n × Fin n)) (hEn : E.Nonempty)
    (hadj : ∀ p ∈ E, G.Adj p.1 p.2)
    (hcut : ∀ p ∈ E, context (pairInput p.1 p.2) false = false)
    (hcover : ∀ u v, G.Adj u v → context (pairInput u v) false = false → (u, v) ∈ E)
    (r : Fin n)
    (hshared : ∀ p ∈ E, ∃ R T : Finset (Fin n), r ∈ R ∧
      (∀ x, ((setOr R x || clauseProduct S x) && setOr T x) = true → graphFun G ∅ x = true) ∧
      setOr R (pairInput p.1 p.2) = false ∧ setOr T (pairInput p.1 p.2) = true) :
    ∃ (v : Fin n) (i : Fin k), (∀ a ∈ S i, G.Adj v a) ∧
      (fun x => context x (x v && setOr (S i) x)) = graphFun G ∅ := by
  have hH : ∀ p ∈ E, clauseProduct S (pairInput p.1 p.2) = true := by
    intro p hp
    have he := (hF (pairInput p.1 p.2)).trans ((graph_pair_iff G p.1 p.2).mpr (hadj p hp))
    cases h : clauseProduct S (pairInput p.1 p.2)
    · rw [h, hcut p hp] at he
      cases he
    · rfl
  have hpair : ∀ p ∈ E, ∀ i, p.1 ∈ S i ∨ p.2 ∈ S i := by
    intro p hp i
    have hh := (decide_eq_true_eq.mp (hH p hp)) i
    obtain ⟨a, ha, hx⟩ := hh
    simp only [pairInput, decide_eq_true_eq] at hx
    rcases hx with rfl | rfl
    · exact Or.inl ha
    · exact Or.inr ha
  have hdata : ∀ p ∈ E, r ≠ p.1 ∧ r ≠ p.2 ∧
      ((Geometry.clauseClean G S p.1 ∧ G.Adj r p.1) ∨
        (Geometry.clauseClean G S p.2 ∧ G.Adj r p.2)) := by
    intro p hp
    obtain ⟨R, T, hr, hclean, hR, hT⟩ := hshared p hp
    obtain ⟨h1, h2, w, hw, hadjw, hcw⟩ :=
      shared_raw_critical_filter G (clauseProduct S) R T r p.1 p.2 hr hclean hR hT
    have hc : Geometry.clauseClean G S w := by
      intro x hx hh
      exact hcw x (decide_eq_true hh) hx
    refine ⟨h1, h2, ?_⟩
    rcases hw with rfl | rfl
    · exact Or.inl ⟨hc, hadjw⟩
    · exact Or.inr ⟨hc, hadjw⟩
  obtain ⟨v, i, hu, hc⟩ := Geometry.monochrome_unoriented_star G s hbip h4 S t hmono
    E hEn hadj hpair r (fun p hp => ⟨(hdata p hp).1, (hdata p hp).2.1⟩)
    (fun p hp => (hdata p hp).2.2)
  refine ⟨v, i, hu, ?_⟩
  apply clean_critical_replacement G context (clauseProduct S) (fun x => x v && setOr (S i) x)
    hcontext ?_ ?_ ?_ hF
  · intro x y hxy hx
    simp only [Bool.and_eq_true, setOr, decide_eq_true_eq] at hx ⊢
    obtain ⟨hv, a, ha, hax⟩ := hx
    exact ⟨hxy v hv, a, ha, hxy a hax⟩
  · intro x hx
    simp only [Bool.and_eq_true, setOr, decide_eq_true_eq] at hx
    obtain ⟨hv, a, ha, hax⟩ := hx
    exact (Geometry.graph_true G x).mpr ⟨v, a, hu a ha, hv, hax⟩
  · intro u w huw hzero
    rcases hc (u, w) (hcover u w huw hzero) with ⟨h, hm⟩ | ⟨h, hm⟩
    · dsimp at h hm
      subst u
      simp [pairInput, setOr_pair, hm]
    · dsimp at h hm
      subst w
      simp [pairInput, setOr_pair, hm]

end PEqualNP.Outside.L_meta_5012

namespace PEqualNP.Outside.L_meta_5012.OrSplit

noncomputable def twoCost {α : Type*} [DecidableEq α] (A B : Finset α) : ℕ :=
  (A ∪ B).card - if Disjoint A B then 2 else 1

lemma partition_disjoint {α : Type*} [DecidableEq α]
    (A B : Finset α) (p : α → Prop) [DecidablePred p] :
    Disjoint A B ↔
      Disjoint (A.filter p) (B.filter p) ∧
      Disjoint (A.filter fun a => ¬ p a) (B.filter fun a => ¬ p a) := by
  constructor
  · intro h
    exact ⟨h.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _),
      h.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)⟩
  · rintro ⟨hp, hn⟩
    apply Finset.disjoint_left.mpr
    intro a ha hb
    by_cases h : p a
    · exact Finset.disjoint_left.mp hp (Finset.mem_filter.mpr ⟨ha, h⟩)
        (Finset.mem_filter.mpr ⟨hb, h⟩)
    · exact Finset.disjoint_left.mp hn (Finset.mem_filter.mpr ⟨ha, h⟩)
        (Finset.mem_filter.mpr ⟨hb, h⟩)

lemma partition_union_card {α : Type*} [DecidableEq α]
    (A B : Finset α) (p : α → Prop) [DecidablePred p] :
    ((A.filter p) ∪ (B.filter p)).card +
      ((A.filter fun a => ¬ p a) ∪ (B.filter fun a => ¬ p a)).card =
      (A ∪ B).card := by
  have hp : (A.filter p) ∪ (B.filter p) = (A ∪ B).filter p := by
    ext a
    simp only [Finset.mem_union, Finset.mem_filter]
    tauto
  have hn : (A.filter fun a => ¬ p a) ∪ (B.filter fun a => ¬ p a) =
      (A ∪ B).filter fun a => ¬ p a := by
    ext a
    simp only [Finset.mem_union, Finset.mem_filter]
    tauto
  rw [hp, hn]
  exact Finset.card_filter_add_card_filter_not p

lemma two_nonempty_union_card {α : Type*} [DecidableEq α]
    (A B : Finset α) (hA : A.Nonempty) (hB : B.Nonempty) :
    (if Disjoint A B then 2 else 1) ≤ (A ∪ B).card := by
  classical
  have ha := Finset.card_pos.mpr hA
  have hb := Finset.card_pos.mpr hB
  split_ifs with hd
  · rw [Finset.card_union_of_disjoint hd]
    omega
  · have hle := Finset.card_le_card (show A ⊆ A ∪ B from Finset.subset_union_left)
    omega

lemma split_two_outputs_save_one {α : Type*} [DecidableEq α]
    (A B : Finset α) (p : α → Prop) [DecidablePred p]
    (hAp : (A.filter p).Nonempty) (hBp : (B.filter p).Nonempty)
    (hAn : (A.filter fun a => ¬ p a).Nonempty)
    (hBn : (B.filter fun a => ¬ p a).Nonempty) :
    twoCost (A.filter p) (B.filter p) +
      twoCost (A.filter fun a => ¬ p a) (B.filter fun a => ¬ p a) + 1 ≤
      twoCost A B := by
  classical
  have hc := partition_union_card A B p
  have hdp := two_nonempty_union_card (A.filter p) (B.filter p) hAp hBp
  have hdn := two_nonempty_union_card (A.filter fun a => ¬ p a)
    (B.filter fun a => ¬ p a) hAn hBn
  have he := partition_disjoint A B p
  by_cases hp : Disjoint (A.filter p) (B.filter p) <;>
    by_cases hn : Disjoint (A.filter fun a => ¬ p a) (B.filter fun a => ¬ p a)
  all_goals simp only [hp, hn, and_true, and_false, iff_true, iff_false] at he
  all_goals simp only [twoCost, hp, hn, he, ite_true, ite_false] at hdp hdn ⊢
  all_goals omega

lemma split_two_outputs_of_network_bound {α : Type*} [DecidableEq α]
    (A B : Finset α) (p : α → Prop) [DecidablePred p]
    (hAp : (A.filter p).Nonempty) (hBp : (B.filter p).Nonempty)
    (hAn : (A.filter fun a => ¬ p a).Nonempty)
    (hBn : (B.filter fun a => ¬ p a).Nonempty)
    (C : ℕ) (hC : (A ∪ B).card ≤ C + if Disjoint A B then 2 else 1) :
    twoCost (A.filter p) (B.filter p) +
      twoCost (A.filter fun a => ¬ p a) (B.filter fun a => ¬ p a) + 1 ≤ C := by
  have h := split_two_outputs_save_one A B p hAp hBp hAn hBn
  have hc : twoCost A B ≤ C := by
    unfold twoCost
    omega
  exact h.trans hc


def available {α : Type*} [DecidableEq α] (L : List (Finset α)) (A : Finset α) : Prop :=
  A.card = 1 ∨ A ∈ L

def valid {α : Type*} [DecidableEq α] : List (Finset α) → Prop
  | [] => True
  | C :: L => valid L ∧ ∃ A B, available L A ∧ available L B ∧ C = A ∪ B

lemma available_mono {α : Type*} [DecidableEq α] (L K : List (Finset α))
    (hLK : L ⊆ K) (A : Finset α) (hA : available L A) : available K A := by
  rcases hA with h | h
  · exact Or.inl h
  · exact Or.inr (hLK h)

lemma extend_union {α : Type*} [DecidableEq α] (L : List (Finset α))
    (hL : valid L) (A T : Finset α) (hA : available L A) :
    ∃ K : List (Finset α), valid K ∧ available K (A ∪ T) ∧ L ⊆ K ∧
      K.length ≤ L.length + T.card := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    exact ⟨L, hL, by simpa using hA, fun _ h => h, by simp⟩
  | @insert a T ha ih =>
    obtain ⟨K, hK, hAT, hLK, hlen⟩ := ih
    refine ⟨(A ∪ insert a T) :: K, ?_, ?_, ?_, ?_⟩
    · refine ⟨hK, A ∪ T, {a}, hAT, Or.inl (by simp), ?_⟩
      ext b
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    · exact Or.inr (List.mem_cons_self ..)
    · intro X hX
      exact List.mem_cons_of_mem _ (hLK hX)
    · simp only [List.length_cons, Finset.card_insert_of_notMem ha]
      omega

lemma extend_to {α : Type*} [DecidableEq α] (L : List (Finset α))
    (hL : valid L) (A B : Finset α) (hA : available L A) (hAB : A ⊆ B) :
    ∃ K : List (Finset α), valid K ∧ available K B ∧ L ⊆ K ∧
      K.length ≤ L.length + (B \ A).card := by
  obtain ⟨K, hK, hAK, hLK, hlen⟩ := extend_union L hL A (B \ A) hA
  have he : A ∪ (B \ A) = B := by
    ext a
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro (h | ⟨h, _⟩)
      · exact hAB h
      · exact h
    · intro h
      by_cases ha : a ∈ A
      · exact Or.inl ha
      · exact Or.inr ⟨h, ha⟩
  exact ⟨K, hK, he ▸ hAK, hLK, hlen⟩

lemma build_one {α : Type*} [DecidableEq α] (L : List (Finset α))
    (hL : valid L) (A : Finset α) (hA : A.Nonempty) :
    ∃ K : List (Finset α), valid K ∧ available K A ∧ L ⊆ K ∧
      K.length ≤ L.length + (A.card - 1) := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨K, hK, hAK, hLK, hlen⟩ :=
    extend_union L hL {a} (A.erase a) (Or.inl (by simp))
  have he : ({a} : Finset α) ∪ A.erase a = A := by
    ext b
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_erase]
    constructor
    · rintro (rfl | ⟨_, h⟩)
      · exact ha
      · exact h
    · intro h
      by_cases hh : b = a
      · exact Or.inl hh
      · exact Or.inr ⟨hh, h⟩
  refine ⟨K, hK, he ▸ hAK, hLK, ?_⟩
  simpa only [Finset.card_erase_of_mem ha] using hlen

lemma build_two {α : Type*} [DecidableEq α] (L : List (Finset α))
    (hL : valid L) (A B : Finset α) (hA : A.Nonempty) (hB : B.Nonempty) :
    ∃ K : List (Finset α), valid K ∧ available K A ∧ available K B ∧ L ⊆ K ∧
      K.length ≤ L.length + twoCost A B := by
  classical
  by_cases hd : Disjoint A B
  · obtain ⟨K, hK, hKA, hLK, hlenK⟩ := build_one L hL A hA
    obtain ⟨J, hJ, hJB, hKJ, hlenJ⟩ := build_one K hK B hB
    refine ⟨J, hJ, available_mono K J hKJ A hKA, hJB,
      fun _ h => hKJ (hLK h), ?_⟩
    have hca := Finset.card_pos.mpr hA
    have hcb := Finset.card_pos.mpr hB
    rw [twoCost, ite_eq_left hd, Finset.card_union_of_disjoint hd]
    omega
  · have hI : (A ∩ B).Nonempty := by
      by_contra hI
      apply hd
      apply Finset.disjoint_left.mpr
      intro a ha hb
      exact hI ⟨a, Finset.mem_inter.mpr ⟨ha, hb⟩⟩
    obtain ⟨K, hK, hKI, hLK, hlenK⟩ := build_one L hL (A ∩ B) hI
    obtain ⟨J, hJ, hJA, hKJ, hlenJ⟩ :=
      extend_to K hK (A ∩ B) A hKI Finset.inter_subset_left
    obtain ⟨M, hM, hMB, hJM, hlenM⟩ :=
      extend_to J hJ (A ∩ B) B (available_mono K J hKJ (A ∩ B) hKI)
        Finset.inter_subset_right
    refine ⟨M, hM, available_mono J M hJM A hJA, hMB,
      fun _ h => hJM (hKJ (hLK h)), ?_⟩
    have hci := Finset.card_pos.mpr hI
    have hca := Finset.card_sdiff_add_card_eq_card (show A ∩ B ⊆ A from Finset.inter_subset_left)
    have hcb := Finset.card_sdiff_add_card_eq_card (show A ∩ B ⊆ B from Finset.inter_subset_right)
    have hcu := Finset.card_union_add_card_inter A B
    rw [twoCost, ite_eq_right hd]
    omega

lemma split_program {α : Type*} [DecidableEq α]
    (A B : Finset α) (p : α → Prop) [DecidablePred p]
    (hAp : (A.filter p).Nonempty) (hBp : (B.filter p).Nonempty)
    (hAn : (A.filter fun a => ¬ p a).Nonempty)
    (hBn : (B.filter fun a => ¬ p a).Nonempty) :
    ∃ K : List (Finset α), valid K ∧
      available K (A.filter p) ∧ available K (B.filter p) ∧
      available K (A.filter fun a => ¬ p a) ∧
      available K (B.filter fun a => ¬ p a) ∧
      K.length + 1 ≤ twoCost A B := by
  obtain ⟨L, hL, hAL, hBL, _, hlenL⟩ := build_two [] True.intro
    (A.filter p) (B.filter p) hAp hBp
  obtain ⟨K, hK, hAK, hBK, hLK, hlenK⟩ := build_two L hL
    (A.filter fun a => ¬ p a) (B.filter fun a => ¬ p a) hAn hBn
  refine ⟨K, hK, available_mono L K hLK _ hAL, available_mono L K hLK _ hBL,
    hAK, hBK, ?_⟩
  have hsave := split_two_outputs_save_one A B p hAp hBp hAn hBn
  simp only [List.length_nil, Nat.zero_add] at hlenL
  omega

lemma split_program_of_network_bound {α : Type*} [DecidableEq α]
    (A B : Finset α) (p : α → Prop) [DecidablePred p]
    (hAp : (A.filter p).Nonempty) (hBp : (B.filter p).Nonempty)
    (hAn : (A.filter fun a => ¬ p a).Nonempty)
    (hBn : (B.filter fun a => ¬ p a).Nonempty)
    (C : ℕ) (hC : (A ∪ B).card ≤ C + if Disjoint A B then 2 else 1) :
    ∃ K : List (Finset α), valid K ∧
      available K (A.filter p) ∧ available K (B.filter p) ∧
      available K (A.filter fun a => ¬ p a) ∧
      available K (B.filter fun a => ¬ p a) ∧ K.length + 1 ≤ C := by
  obtain ⟨K, hK, hApK, hBpK, hAnK, hBnK, hlen⟩ :=
    split_program A B p hAp hBp hAn hBn
  refine ⟨K, hK, hApK, hBpK, hAnK, hBnK, ?_⟩
  have hc : twoCost A B ≤ C := by
    unfold twoCost
    omega
  exact hlen.trans hc

def sources {α : Type*} [DecidableEq α] (F : Finset (Finset α)) : Finset α :=
  F.biUnion id

def overlaps {α : Type*} [DecidableEq α] (F : Finset (Finset α)) : Prop :=
  ∃ X ∈ F, ∃ Y ∈ F, X ≠ Y ∧ ∃ a, a ∈ X ∧ a ∈ Y

lemma expand_sources {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (C A B : Finset α) (hC : C ∈ F) (he : C = A ∪ B) :
    sources (insert A (insert B (F.erase C))) = sources F := by
  ext a
  simp only [sources, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_erase, id_eq]
  constructor
  · rintro ⟨X, rfl | rfl | ⟨hXC, hXF⟩, ha⟩
    · exact ⟨C, hC, he.symm ▸ Finset.mem_union_left B ha⟩
    · exact ⟨C, hC, he.symm ▸ Finset.mem_union_right A ha⟩
    · exact ⟨X, hXF, ha⟩
  · rintro ⟨X, hXF, ha⟩
    by_cases hXC : X = C
    · subst X
      rw [he] at ha
      rcases Finset.mem_union.mp ha with h | h
      · exact ⟨A, Or.inl rfl, h⟩
      · exact ⟨B, Or.inr (Or.inl rfl), h⟩
    · exact ⟨X, Or.inr (Or.inr ⟨hXC, hXF⟩), ha⟩

lemma expand_card {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (C A B : Finset α) (hC : C ∈ F) :
    (insert A (insert B (F.erase C))).card ≤ F.card + 1 := by
  have h1 := Finset.card_insert_le A (insert B (F.erase C))
  have h2 := Finset.card_insert_le B (F.erase C)
  have h3 := Finset.card_erase_add_one hC
  omega

lemma expand_overlap {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (C A B : Finset α) (hC : C ∈ F) (he : C = A ∪ B)
    (hF : overlaps F) :
    overlaps (insert A (insert B (F.erase C))) ∨
      (insert A (insert B (F.erase C))).card ≤ F.card := by
  classical
  by_cases hA : A ∈ F.erase C
  · right
    have h1 := Finset.card_insert_le B (F.erase C)
    have h2 := Finset.card_erase_add_one hC
    have h3 : insert A (insert B (F.erase C)) = insert B (F.erase C) :=
      Finset.insert_eq_of_mem (Finset.mem_insert_of_mem hA)
    rw [h3]
    omega
  by_cases hB : B ∈ F.erase C
  · right
    rw [Finset.insert_eq_of_mem hB]
    have h1 := Finset.card_insert_le A (F.erase C)
    have h2 := Finset.card_erase_add_one hC
    omega
  by_cases hAB : A = B
  · right
    subst B
    rw [Finset.insert_idem]
    have h1 := Finset.card_insert_le A (F.erase C)
    have h2 := Finset.card_erase_add_one hC
    omega
  left
  obtain ⟨X, hX, Y, hY, hXY, a, haX, haY⟩ := hF
  by_cases hXC : X = C
  · subst X
    have hYD : Y ∈ F.erase C := Finset.mem_erase.mpr ⟨Ne.symm hXY, hY⟩
    have hYN : Y ∈ insert A (insert B (F.erase C)) :=
      Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hYD)
    have hAY : A ≠ Y := fun h => hA (h.symm ▸ hYD)
    have hBY : B ≠ Y := fun h => hB (h.symm ▸ hYD)
    rw [he] at haX
    rcases Finset.mem_union.mp haX with ha | hb
    · exact ⟨A, Finset.mem_insert_self .., Y, hYN, hAY, a, ha, haY⟩
    · exact ⟨B, Finset.mem_insert_of_mem (Finset.mem_insert_self ..),
        Y, hYN, hBY, a, hb, haY⟩
  by_cases hYC : Y = C
  · subst Y
    have hXD : X ∈ F.erase C := Finset.mem_erase.mpr ⟨hXC, hX⟩
    have hXN : X ∈ insert A (insert B (F.erase C)) :=
      Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hXD)
    have hAX : A ≠ X := fun h => hA (h.symm ▸ hXD)
    have hBX : B ≠ X := fun h => hB (h.symm ▸ hXD)
    rw [he] at haY
    rcases Finset.mem_union.mp haY with ha | hb
    · exact ⟨A, Finset.mem_insert_self .., X, hXN, hAX, a, ha, haX⟩
    · exact ⟨B, Finset.mem_insert_of_mem (Finset.mem_insert_self ..),
        X, hXN, hBX, a, hb, haX⟩
  · exact ⟨X, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨hXC, hX⟩)),
      Y, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨hYC, hY⟩)), hXY, a, haX, haY⟩

lemma family_bound {α : Type*} [DecidableEq α] (L : List (Finset α))
    (hL : valid L) (F : Finset (Finset α)) (hav : ∀ A ∈ F, available L A) :
    (sources F).card ≤ L.length + F.card ∧
      (overlaps F → (sources F).card + 1 ≤ L.length + F.card) := by
  classical
  induction L generalizing F with
  | nil =>
    have hcard : ∀ A ∈ F, A.card = 1 := by
      intro A hA
      rcases hav A hA with h | h
      · exact h
      · cases h
    have hu : (sources F).card ≤ F.card := by
      calc
        (sources F).card ≤ F.sum (fun A => A.card) := Finset.card_biUnion_le
        _ = F.card := by
          simpa using (Finset.sum_congr rfl hcard : F.sum (fun A => A.card) = F.sum (fun _ => 1))
    refine ⟨by simpa using hu, ?_⟩
    intro hov
    obtain ⟨X, hX, Y, hY, hXY, a, haX, haY⟩ := hov
    obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp (hcard X hX)
    obtain ⟨y, rfl⟩ := Finset.card_eq_one.mp (hcard Y hY)
    simp only [Finset.mem_singleton] at haX haY
    have hxy : x = y := haX.symm.trans haY
    exact False.elim (hXY (congrArg (fun z => ({z} : Finset α)) hxy))
  | cons C L ih =>
    obtain ⟨hL, A, B, hA, hB, he⟩ := hL
    by_cases hCF : C ∈ F
    · let N : Finset (Finset α) := insert A (insert B (F.erase C))
      have havN : ∀ X ∈ N, available L X := by
        intro X hX
        rcases Finset.mem_insert.mp hX with rfl | hX
        · exact hA
        rcases Finset.mem_insert.mp hX with rfl | hX
        · exact hB
        obtain ⟨hXC, hXF⟩ := Finset.mem_erase.mp hX
        rcases hav X hXF with h | h
        · exact Or.inl h
        · rcases List.mem_cons.mp h with h | h
          · exact False.elim (hXC h)
          · exact Or.inr h
      obtain ⟨hbase, hstrong⟩ := ih hL N havN
      have hsource : sources N = sources F := expand_sources F C A B hCF he
      rw [hsource] at hbase hstrong
      have hcard : N.card ≤ F.card + 1 := expand_card F C A B hCF
      simp only [List.length_cons]
      refine ⟨by omega, ?_⟩
      intro hov
      rcases expand_overlap F C A B hCF he hov with hnew | hsmall
      · have h := hstrong hnew
        omega
      · have hsmall : N.card ≤ F.card := hsmall
        omega
    · have havF : ∀ X ∈ F, available L X := by
        intro X hX
        rcases hav X hX with h | h
        · exact Or.inl h
        · rcases List.mem_cons.mp h with h | h
          · exact False.elim (hCF (h ▸ hX))
          · exact Or.inr h
      obtain ⟨hbase, _⟩ := ih hL F havF
      simp only [List.length_cons]
      exact ⟨by omega, fun _ => by omega⟩

lemma network_source_bound {α : Type*} [DecidableEq α] (L : List (Finset α))
    (hL : valid L) (A B : Finset α) (hA : available L A) (hB : available L B) :
    (A ∪ B).card ≤ L.length + if Disjoint A B then 2 else 1 := by
  classical
  let F : Finset (Finset α) := {A, B}
  have hav : ∀ X ∈ F, available L X := by
    intro X hX
    simp only [F, Finset.mem_insert, Finset.mem_singleton] at hX
    rcases hX with rfl | rfl
    · exact hA
    · exact hB
  obtain ⟨hbase, hstrong⟩ := family_bound L hL F hav
  have hsource : sources F = A ∪ B := by
    ext a
    simp [sources, F]
  rw [hsource] at hbase hstrong
  have hcard : F.card ≤ 2 := by
    exact Finset.card_le_two
  by_cases hd : Disjoint A B
  · rw [ite_eq_left hd]
    omega
  · rw [ite_eq_right hd]
    by_cases heq : A = B
    · have hcard1 : F.card = 1 := by simp [F, heq]
      omega
    · have hcommon : ∃ a, a ∈ A ∧ a ∈ B := by
        by_contra h
        apply hd
        apply Finset.disjoint_left.mpr
        intro a ha hb
        exact h ⟨a, ha, hb⟩
      have hov : overlaps F :=
        ⟨A, by simp [F], B, by simp [F], heq, hcommon⟩
      have h := hstrong hov
      omega

lemma twoCost_le_program {α : Type*} [DecidableEq α] (L : List (Finset α))
    (hL : valid L) (A B : Finset α) (hA : available L A) (hB : available L B) :
    twoCost A B ≤ L.length := by
  have h := network_source_bound L hL A B hA hB
  unfold twoCost
  omega

lemma split_program_strictly_smaller {α : Type*} [DecidableEq α]
    (L : List (Finset α)) (hL : valid L) (A B : Finset α)
    (hA : available L A) (hB : available L B)
    (p : α → Prop) [DecidablePred p]
    (hAp : (A.filter p).Nonempty) (hBp : (B.filter p).Nonempty)
    (hAn : (A.filter fun a => ¬ p a).Nonempty)
    (hBn : (B.filter fun a => ¬ p a).Nonempty) :
    ∃ K : List (Finset α), valid K ∧
      available K (A.filter p) ∧ available K (B.filter p) ∧
      available K (A.filter fun a => ¬ p a) ∧
      available K (B.filter fun a => ¬ p a) ∧ K.length < L.length := by
  obtain ⟨K, hK, hApK, hBpK, hAnK, hBnK, hlen⟩ :=
    split_program A B p hAp hBp hAn hBn
  refine ⟨K, hK, hApK, hBpK, hAnK, hBnK, ?_⟩
  have hcost := twoCost_le_program L hL A B hA hB
  omega

def pureSupport {α : Type*} (p : α → Prop) (A : Finset α) : Prop :=
  (∀ a ∈ A, p a) ∨ (∀ a ∈ A, ¬ p a)

noncomputable def pureFilter {α : Type*} (p : α → Prop) (L : List (Finset α)) : List (Finset α) := by
  classical
  exact L.filter fun A => decide (pureSupport p A)

lemma pureSupport_mono {α : Type*} (p : α → Prop) (A B : Finset α)
    (hAB : A ⊆ B) (hB : pureSupport p B) : pureSupport p A := by
  rcases hB with h | h
  · exact Or.inl (fun a ha => h a (hAB ha))
  · exact Or.inr (fun a ha => h a (hAB ha))

lemma pureSupport_singleton {α : Type*} [DecidableEq α]
    (p : α → Prop) (a : α) : pureSupport p {a} := by
  classical
  by_cases h : p a
  · exact Or.inl (by simpa using h)
  · exact Or.inr (by simpa using h)

lemma available_filter_pure {α : Type*} [DecidableEq α]
    (p : α → Prop) [DecidablePred p] (L : List (Finset α)) (A : Finset α)
    (hA : available L A) (hp : pureSupport p A) :
    available (pureFilter p L) A := by
  classical
  rcases hA with h | h
  · exact Or.inl h
  · exact Or.inr (List.mem_filter.mpr ⟨h, decide_eq_true hp⟩)

lemma filter_pure_valid {α : Type*} [DecidableEq α]
    (p : α → Prop) [DecidablePred p] (L : List (Finset α)) (hL : valid L) :
    valid (pureFilter p L) := by
  classical
  induction L with
  | nil => trivial
  | cons C L ih =>
    obtain ⟨hL, A, B, hA, hB, he⟩ := hL
    by_cases hp : pureSupport p C
    · simp only [pureFilter, List.filter_cons, decide_eq_true hp, ↓reduceIte]
      have ha : pureSupport p A := pureSupport_mono p A C (by rw [he]; exact Finset.subset_union_left) hp
      have hb : pureSupport p B := pureSupport_mono p B C (by rw [he]; exact Finset.subset_union_right) hp
      exact ⟨ih hL, A, B, available_filter_pure p L A hA ha,
        available_filter_pure p L B hB hb, he⟩
    · simpa only [pureFilter, List.filter_cons, decide_eq_false hp, Bool.false_eq_true, ↓reduceIte] using ih hL

lemma mixed_not_pure {α : Type*} (p : α → Prop) (M : Finset α)
    (hmixed : (∃ a ∈ M, p a) ∧ ∃ b ∈ M, ¬ p b) : ¬ pureSupport p M := by
  obtain ⟨⟨a, ha, hpa⟩, b, hb, hpb⟩ := hmixed
  rintro (h | h)
  · exact hpb (h b hb)
  · exact h a ha hpa

lemma filter_pure_length_lt {α : Type*} [DecidableEq α]
    (p : α → Prop) [DecidablePred p] (L : List (Finset α)) (M : Finset α)
    (hM : available L M)
    (hmixed : (∃ a ∈ M, p a) ∧ ∃ b ∈ M, ¬ p b) :
    (pureFilter p L).length < L.length := by
  classical
  have hnp : ¬ pureSupport p M := mixed_not_pure p M hmixed
  have hm : M ∈ L := by
    rcases hM with h | h
    · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h
      exact False.elim (hnp (pureSupport_singleton p a))
    · exact h
  apply List.length_filter_lt_length_iff_exists.mpr
  exact ⟨M, hm, by simpa using hnp⟩

lemma pure_outputs_with_mixed_lower_bound {α : Type*} [DecidableEq α]
    (p : α → Prop) [DecidablePred p] (L : List (Finset α)) (hL : valid L)
    (A B M : Finset α) (hA : available L A) (hB : available L B)
    (hM : available L M) (hAn : A.Nonempty) (hBn : B.Nonempty)
    (hAp : ∀ a ∈ A, p a) (hBnP : ∀ b ∈ B, ¬ p b)
    (hmixed : (∃ a ∈ M, p a) ∧ ∃ b ∈ M, ¬ p b) :
    (A ∪ B).card ≤ L.length + 1 := by
  classical
  let K := pureFilter p L
  have hK : valid K := filter_pure_valid p L hL
  have hAK : available K A := available_filter_pure p L A hA (Or.inl hAp)
  have hBK : available K B := available_filter_pure p L B hB (Or.inr hBnP)
  have hcost := twoCost_le_program K hK A B hAK hBK
  have hlt : K.length < L.length := filter_pure_length_lt p L M hM hmixed
  have hd : Disjoint A B := Finset.disjoint_left.mpr (fun a ha hb => hBnP a hb (hAp a ha))
  have hmin := two_nonempty_union_card A B hAn hBn
  simp only [twoCost, ite_eq_left hd] at hcost
  simp only [ite_eq_left hd] at hmin
  omega

end PEqualNP.Outside.L_meta_5012.OrSplit
