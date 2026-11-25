import PEqualNP.Defs
import Mathlib.Data.List.Induction
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

namespace PEqualNP.Outside.L_meta_5012.MixedOuter
open PEqualNP.MetaComplexity
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.CleanedNonEdge PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_5012.Structural PEqualNP.Outside.L_meta_5012
open PEqualNP.Outside.L_meta_5012.Patch

def Frontier {n : ℕ} (C : Circuit) (x : Fin n → Bool) (f : ℕ → Bool) : Prop :=
  (∀ i : Fin n, f i.val = x i) ∧
  (∀ w, n + C.gates.length ≤ w → f w = false) ∧
  ∀ j, j < C.gates.length → (gateAt C j).op = GateOp.or →
    (f (n+j) = true ↔ ∃ w ∈ (gateAt C j).inputs, w < n+j ∧ f w = true)

lemma original_frontier {n : ℕ} (C : Circuit) (x : Fin n → Bool) :
    Frontier C x (val C (List.ofFn x)) := by
  refine ⟨val_ofFn C x, ?_, ?_⟩
  · intro w hw
    exact val_ge (by simp) hw
  · intro j hj hop
    exact val_or (by simp) hj hop

lemma frontier_trace {n : ℕ} {C : Circuit} {x : Fin n → Bool} {f : ℕ → Bool}
    (hf : Frontier C x f) : ∀ w, f w = true →
      ∃ v, Relation.ReflTransGen (OrStep n C) w v ∧ f v = true ∧
        (v < n ∨ ∃ j, j < C.gates.length ∧ v = n+j ∧ (gateAt C j).op ≠ GateOp.or) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hinput : w < n
    · exact ⟨w, .refl, hw, Or.inl hinput⟩
    · by_cases hout : n + C.gates.length ≤ w
      · rw [hf.2.1 w hout] at hw
        cases hw
      · obtain ⟨j, rfl⟩ : ∃ j, w = n+j := ⟨w-n, by omega⟩
        have hj : j < C.gates.length := by omega
        by_cases hop : (gateAt C j).op = GateOp.or
        · obtain ⟨i, hi, hlt, hfi⟩ := (hf.2.2 j hj hop).mp hw
          obtain ⟨v, hp, hv, hterm⟩ := ih i hlt hfi
          exact ⟨v, .head ⟨j, hj, rfl, hop, hi, hlt⟩ hp, hv, hterm⟩
        · exact ⟨n+j, .refl, hw, Or.inr ⟨j, hj, rfl, hop⟩⟩

lemma frontier_up {n : ℕ} {C : Circuit} {x : Fin n → Bool} {f : ℕ → Bool}
    (hf : Frontier C x f) {w v : ℕ} (hp : Relation.ReflTransGen (OrStep n C) w v)
    (hv : f v = true) : f w = true := by
  induction hp using Relation.ReflTransGen.head_induction_on with
  | refl => exact hv
  | head hs _ ih =>
    obtain ⟨j, hj, rfl, hop, hin, hlt⟩ := hs
    exact (hf.2.2 j hj hop).mpr ⟨_, hin, hlt, ih⟩

lemma frontier_wire {n : ℕ} {C : Circuit} {x : Fin n → Bool} {f : ℕ → Bool}
    (hAO : IsAO2 n C) (hf : Frontier C x f) (w : ℕ) :
    f w = true ↔ (∃ i ∈ orIn n C w, x i = true) ∨
      ∃ j, j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧
        OrReaches n C w j ∧ f (n+j) = true := by
  constructor
  · intro hw
    obtain ⟨v, hp, hv, ht⟩ := frontier_trace hf w hw
    rcases ht with hlt | ⟨j, hj, rfl, hop⟩
    · left
      exact ⟨⟨v,hlt⟩, reach_mem_orIn ⟨v,hlt⟩ hp, (hf.1 ⟨v,hlt⟩).symm.trans hv⟩
    · right
      have hand := (hAO.1 _ (gateAt_mem hj)).resolve_right hop
      exact ⟨j, hj, hand, reach_orReaches hp j rfl hj, hv⟩
  · rintro (⟨i, hi, hxi⟩ | ⟨j, hj, hop, hp, hv⟩)
    · exact frontier_up hf (mem_orIn_reach i hi) ((hf.1 i).trans hxi)
    · exact frontier_up hf (orReaches_reach j _ hp).1 hv

lemma frontier_operand {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) (hT : TopForm G C) (g h : ℕ)
    (hJ : junk G C = {g,h}) {a : ℕ} (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and) {x : Fin n → Bool} {f : ℕ → Bool}
    (hf : Frontier C x f) (b : Fin 2) :
    f (opnd C a b) = true ↔ setOr (side C a b) x = true ∨
      (OrReaches n C (opnd C a b) g ∧ f (n+g) = true) ∨
      (OrReaches n C (opnd C a b) h ∧ f (n+h) = true) := by
  rw [frontier_wire hAO hf]
  constructor
  · rintro (hr | ⟨j, hj, hand, hp, hv⟩)
    · exact Or.inl (decide_eq_true hr)
    · have hmem := operandOrAndJunk hAO hT ha hop hp hand
      simp only [hJ, Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with rfl | rfl
      · exact Or.inr (Or.inl ⟨hp,hv⟩)
      · exact Or.inr (Or.inr ⟨hp,hv⟩)
  · rintro (hr | ⟨hp,hv⟩ | ⟨hp,hv⟩)
    · exact Or.inl (of_decide_eq_true hr)
    · have hg : g ∈ junk G C := by simp [hJ]
      exact Or.inr ⟨g, (junkData hg).1, (junkData hg).2.1, hp,hv⟩
    · have hh : h ∈ junk G C := by simp [hJ]
      exact Or.inr ⟨h, (junkData hh).1, (junkData hh).2.1, hp,hv⟩

lemma output_transfer {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) {x : Fin n → Bool} {f f' : ℕ → Bool}
    (hf : Frontier C x f) (hf' : Frontier C x f')
    (htops : ∀ a ∈ tops G C, f (n+a) = true → f' (n+a) = true)
    (hout : f C.output = true) : f' C.output = true := by
  obtain ⟨v, hp, hv, ht⟩ := frontier_trace hf C.output hout
  rcases ht with hinput | ⟨a, ha, rfl, hnotor⟩
  · have hsingle := reach_var_val (pairInput ⟨v,hinput⟩ ⟨v,hinput⟩) C.output ⟨v,hinput⟩ hp
      (pairInput_left _ _)
    change circuitFun n C (pairInput ⟨v,hinput⟩ ⟨v,hinput⟩) = true at hsingle
    rw [hL.2.1] at hsingle
    exact False.elim (G.irrefl ((graphFun_pair G _ _).mp hsingle))
  · have hand := (hL.1.1 _ (gateAt_mem ha)).resolve_right hnotor
    have hbelow : BelowF G C a := by
      intro y hy
      exact below_of_reach (graphFun G ∅) (fun y => congrFun hL.2.1 y) a hp y hy
    have hatop : a ∈ tops G C := by
      simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using And.intro ha (And.intro hand hbelow)
    exact frontier_up hf' hp (htops a hatop hv)

def fullColor {n : ℕ} (s : Fin n → Bool) (c : Bool) : Fin n → Bool :=
  fun v => decide (s v = c)

lemma fullColor_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hcol : ∀u v, G.Adj u v → s u ≠ s v) (c : Bool) :
    graphFun G ∅ (fullColor s c) = false := by
  apply Bool.eq_false_iff.mpr
  intro ht
  obtain ⟨u,v,huv,hu,hv⟩ := (Geometry.graph_true G _).mp ht
  exact hcol u v huv ((of_decide_eq_true hu).trans (of_decide_eq_true hv).symm)

lemma opposite_frontier_excludes_outer {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) (s : Fin n → Bool)
    (hcol : ∀u v, G.Adj u v → s u ≠ s v) (h : ℕ)
    (hboth : ∀c, gateVal n C h (fullColor s c) = true)
    {a : ℕ} (ha : a ∈ tops G C) {b d : Fin 2} (hbd : b ≠ d)
    (hreach : OrReaches n C (opnd C a b) h) :
    side (n := n) C a d = ∅ ∧ ¬OrReaches n C (opnd C a d) h := by
  have hav := topData ha
  have clean (x : Fin n → Bool)
      (hb : val C (List.ofFn x) (opnd C a b) = true)
      (hd : val C (List.ofFn x) (opnd C a d) = true) : graphFun G ∅ x = true := by
    apply hav.2.2 x
    apply (andValOperands hAO hav.1 hav.2.1 x).mpr
    intro i
    have hi : i=b ∨ i=d := by omega
    rcases hi with rfl | rfl <;> assumption
  constructor
  · apply Finset.eq_empty_iff_forall_notMem.mpr
    intro u hu
    have hh := hboth (s u)
    have hb := orStep_up (n := n) (by simp) (orReaches_reach h _ hreach).1 hh
    have hd := reach_var_val (fullColor s (s u)) _ u (mem_orIn_reach u hu) (by simp [fullColor])
    have hf := clean _ hb hd
    rw [fullColor_false G s hcol] at hf
    cases hf
  · intro hdreach
    have hh := hboth false
    have hb := orStep_up (n := n) (by simp) (orReaches_reach h _ hreach).1 hh
    have hd := orStep_up (n := n) (by simp) (orReaches_reach h _ hdreach).1 hh
    have hf := clean _ hb hd
    rw [fullColor_false G s hcol] at hf
    cases hf

lemma top_product_transfer {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) (hT : TopForm G C) (g h : ℕ)
    (hJ : junk G C = {g,h}) (s : Fin n → Bool)
    (hcol : ∀u v, G.Adj u v → s u ≠ s v)
    (hboth : ∀c, gateVal n C h (fullColor s c) = true)
    {a : ℕ} (ha : a ∈ tops G C) {x : Fin n → Bool} {f f' : ℕ → Bool}
    (hf : Frontier C x f) (hf' : Frontier C x f')
    (hg : f (n+g) = f' (n+g)) (hh : f (n+g) = true → f (n+h) = f' (n+h))
    (hprod : ∀b : Fin 2, f (opnd C a b) = true) :
    ∀b : Fin 2, f' (opnd C a b) = true := by
  intro b
  have hav := topData ha
  apply (frontier_operand G hAO hT g h hJ hav.1 hav.2.1 hf' b).mpr
  rcases (frontier_operand G hAO hT g h hJ hav.1 hav.2.1 hf b).mp (hprod b) with hr | hrg | hrh
  · exact Or.inl hr
  · exact Or.inr (Or.inl ⟨hrg.1, hg.symm.trans hrg.2⟩)
  · let d : Fin 2 := ⟨1-b.val, by omega⟩
    have hbd : b ≠ d := by
      intro he
      have hv := congrArg Fin.val he
      dsimp [d] at hv
      omega
    obtain ⟨hempty, hnot⟩ := opposite_frontier_excludes_outer G hAO s hcol h hboth ha hbd hrh.1
    have hgv : f (n+g) = true := by
      rcases (frontier_operand G hAO hT g h hJ hav.1 hav.2.1 hf d).mp (hprod d) with hr | hrg | hrh
      · simp [hempty, setOr] at hr
      · exact hrg.2
      · exact (hnot hrh.1).elim
    exact Or.inr (Or.inr ⟨hrh.1, (hh hgv).symm.trans hrh.2⟩)

def aliasGate (q : ℕ) : Gate := ⟨GateOp.or, [q,q]⟩

lemma alias_gateAt {C : Circuit} {h : ℕ} (hh : h < C.gates.length) (q : ℕ) :
    gateAt (patch C h (aliasGate q)) h = aliasGate q := by
  simp [gateAt, patch, List.getD_eq_getElem?_getD, hh]

lemma alias_before {n : ℕ} {C : Circuit} {h w : ℕ} (hh : h < C.gates.length)
    (hw : w < n+h) (q : ℕ) (x : Fin n → Bool) :
    val (patch C h (aliasGate q)) (List.ofFn x) w = val C (List.ofFn x) w := by
  by_cases hwn : w < n
  · rw [val_input (by simp) hwn, val_input (by simp) hwn]
  · obtain ⟨j, rfl⟩ : ∃j,w=n+j := ⟨w-n,by omega⟩
    exact gateVal_patch_before hh (by omega) _ x

lemma alias_at {n : ℕ} {C : Circuit} {h q : ℕ} (hh : h < C.gates.length)
    (hq : q < n+h) (x : Fin n → Bool) :
    val (patch C h (aliasGate q)) (List.ofFn x) (n+h) = val C (List.ofFn x) q := by
  have hd : h < (patch C h (aliasGate q)).gates.length := by simpa [patch] using hh
  rw [val_gate (by simp) hd, alias_gateAt hh]
  simp only [aliasGate, GateOp.eval, List.map_cons, List.map_nil, List.any_cons,
    List.any_nil, Bool.or_false, Bool.or_self, ite_eq_left hq]
  exact alias_before hh hq q x

lemma alias_frontier {n : ℕ} {C : Circuit} {h : ℕ}
    (hop : (gateAt C h).op = GateOp.and) (q : ℕ) (x : Fin n → Bool) :
    Frontier C x (val (patch C h (aliasGate q)) (List.ofFn x)) := by
  refine ⟨val_ofFn _ x, ?_, ?_⟩
  · intro w hw
    apply val_ge (n := n) (by simp)
    simpa [patch] using hw
  · intro j hj hor
    have hne : h ≠ j := by rintro rfl; rw [hop] at hor; cases hor
    have hd : j < (patch C h (aliasGate q)).gates.length := by simpa [patch] using hj
    have he := gateAt_patch_ne C h j (aliasGate q) hne
    simpa only [he] using val_or (n := n) (C := patch C h (aliasGate q))
      (x := List.ofFn x) (by simp) hd (by rw [he]; exact hor)

lemma alias_absorption {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {g h : ℕ}
    (hh : h < C.gates.length) (hhand : (gateAt C h).op = GateOp.and)
    (b d : Fin 2) (hbd : b ≠ d) (hreach : OrReaches n C (opnd C h b) g)
    (x : Fin n → Bool) (hg : gateVal n C g x = true) :
    gateVal n C h x = val C (List.ofFn x) (opnd C h d) := by
  have hb : val C (List.ofFn x) (opnd C h b) = true :=
    orStep_up (n := n) (by simp) (orReaches_reach g _ hreach).1 hg
  apply Bool.eq_iff_iff.mpr
  rw [andValOperands hAO hh hhand x]
  constructor
  · intro hv; exact hv d
  · intro hd i
    have hi : i=b ∨ i=d := by omega
    rcases hi with rfl | rfl <;> assumption

lemma alias_top_equal {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) (hT : TopForm G C) (g h : ℕ)
    (hJ : junk G C = {g,h}) (hgh : g<h) (s : Fin n → Bool)
    (hcol : ∀u v, G.Adj u v → s u ≠ s v)
    (hboth : ∀c, gateVal n C h (fullColor s c) = true)
    (b d : Fin 2) (hbd : b ≠ d) (hreach : OrReaches n C (opnd C h b) g)
    {a : ℕ} (ha : a ∈ tops G C) (x : Fin n → Bool) :
    gateVal n (patch C h (aliasGate (opnd C h d))) a x = gateVal n C a x := by
  have hj : h ∈ junk G C := by simp [hJ]
  have hh := (junkData hj).1
  have hhand := (junkData hj).2.1
  have hav := topData ha
  have hne : h ≠ a := by
    rintro rfl
    exact junkNotBelow hj hav.2.2
  let q := opnd C h d
  let D := patch C h (aliasGate q)
  have hq : q < n+h := opndBound hAO hh d
  have hf := original_frontier C x
  have hf' := alias_frontier hhand q x
  have hg : val C (List.ofFn x) (n+g) = val D (List.ofFn x) (n+g) :=
    (alias_before hh (by omega) q x).symm
  have hhv : val C (List.ofFn x) (n+g) = true →
      val C (List.ofFn x) (n+h) = val D (List.ofFn x) (n+h) := by
    intro hgv
    exact (alias_absorption hAO hh hhand b d hbd hreach x hgv).trans (alias_at hh hq x).symm
  have hDA : IsAO2 n D := patch_gate_ao hAO hh (aliasGate q) (Or.inr rfl) rfl (by
    intro w hw
    simp only [aliasGate, List.mem_cons, List.not_mem_nil, or_false, or_self] at hw
    simpa [hw] using hq)
  have hDlen : a < D.gates.length := by simpa [D,patch] using hav.1
  have hDgate : gateAt D a = gateAt C a := gateAt_patch_ne C h a _ hne
  have hDop : (gateAt D a).op = GateOp.and := by rw [hDgate]; exact hav.2.1
  have hDoperand : ∀i : Fin 2, opnd D a i = opnd C a i := by
    intro i; simp only [opnd, hDgate]
  apply Bool.eq_iff_iff.mpr
  rw [andValOperands hDA hDlen hDop x, andValOperands hAO hav.1 hav.2.1 x]
  simp only [hDoperand]
  constructor
  · intro hv
    exact top_product_transfer G hAO hT g h hJ s hcol hboth ha hf' hf hg.symm
      (fun hgv => (hhv (hg.trans hgv)).symm) hv
  · intro hv
    exact top_product_transfer G hAO hT g h hJ s hcol hboth ha hf hf' hg hhv hv

lemma alias_ao {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {h : ℕ}
    (hh : h < C.gates.length) (d : Fin 2) :
    IsAO2 n (patch C h (aliasGate (opnd C h d))) := by
  apply patch_gate_ao hAO hh _ (Or.inr rfl) rfl
  intro w hw
  simp only [aliasGate, List.mem_cons, List.not_mem_nil, or_false, or_self] at hw
  subst w
  exact opndBound hAO hh d

lemma alias_correct {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) (hT : TopForm G C) (g h : ℕ)
    (hJ : junk G C = {g,h}) (hgh : g<h) (s : Fin n → Bool)
    (hcol : ∀u v, G.Adj u v → s u ≠ s v)
    (hboth : ∀c, gateVal n C h (fullColor s c) = true)
    (b d : Fin 2) (hbd : b ≠ d) (hreach : OrReaches n C (opnd C h b) g) :
    circuitFun n (patch C h (aliasGate (opnd C h d))) = graphFun G ∅ := by
  have hj : h ∈ junk G C := by simp [hJ]
  let D := patch C h (aliasGate (opnd C h d))
  have hEq (a : ℕ) (ha : a ∈ tops G C) (x : Fin n → Bool) :
      gateVal n D a x = gateVal n C a x :=
    alias_top_equal G hL.1 hT g h hJ hgh s hcol hboth b d hbd hreach ha x
  have hout : circuitFun n D = circuitFun n C := by
    funext x
    have hf := original_frontier C x
    have hf' := alias_frontier (junkData hj).2.1 (opnd C h d) x
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro hv
      exact output_transfer G hL hf' hf (fun a ha hval => (hEq a ha x).symm.trans hval) hv
    · intro hv
      exact output_transfer G hL hf hf' (fun a ha hval => (hEq a ha x).trans hval) hv
  exact hout.trans hL.2.1

lemma alias_junk_exact {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) (hT : TopForm G C) (g h : ℕ)
    (hJ : junk G C = {g,h}) (hgh : g<h) (s : Fin n → Bool)
    (hcol : ∀u v, G.Adj u v → s u ≠ s v)
    (hboth : ∀c, gateVal n C h (fullColor s c) = true)
    (b d : Fin 2) (hbd : b ≠ d) (hreach : OrReaches n C (opnd C h b) g) :
    junk G (patch C h (aliasGate (opnd C h d))) = {g} := by
  classical
  have hgJ : g ∈ junk G C := by simp [hJ]
  have hhJ : h ∈ junk G C := by simp [hJ]
  have hh := (junkData hhJ).1
  let D := patch C h (aliasGate (opnd C h d))
  apply Finset.ext
  intro k
  constructor
  · intro hk
    have hkd := junkData hk
    have hklen : k < C.gates.length := by simpa [patch] using hkd.1
    have hne : h ≠ k := by
      rintro rfl
      rw [alias_gateAt hh] at hkd
      cases hkd.2.1
    have hgate := gateAt_patch_ne C h k (aliasGate (opnd C h d)) hne
    have hand : (gateAt C k).op = GateOp.and := by rw [hgate] at hkd; exact hkd.2.1
    have hnot : ¬BelowF G C k := by
      intro hbelow
      have htop : k ∈ tops G C := by
        simpa only [tops,gatesWhere,Finset.mem_filter,Finset.mem_range] using
          And.intro hklen (And.intro hand hbelow)
      obtain ⟨x,hx,hfalse⟩ := hkd.2.2
      have heq := alias_top_equal G hAO hT g h hJ hgh s hcol hboth b d hbd hreach htop x
      have htrue := hbelow x (heq.symm.trans hx)
      rw [hfalse] at htrue
      cases htrue
    have hdirty : ∃x : Fin n → Bool, gateVal n C k x = true ∧ graphFun G ∅ x = false := by
      by_contra hnone
      apply hnot
      intro x hx
      by_contra hfalse
      exact hnone ⟨x,hx,Bool.eq_false_iff.mpr hfalse⟩
    have hkJ : k ∈ junk G C := by
      exact mem_junk.mpr ⟨hklen,hand,hklen,hdirty⟩
    simp only [hJ,Finset.mem_insert,Finset.mem_singleton] at hkJ
    rcases hkJ with rfl | rfl
    · simp
    · exact (hne rfl).elim
  · intro hk
    have heq := Finset.mem_singleton.mp hk
    subst k
    obtain ⟨x,hx,hfalse⟩ := (junkData hgJ).2.2
    apply mem_junk.mpr
    refine ⟨by simpa [patch] using (junkData hgJ).1, ?_, ?_, x, ?_, hfalse⟩
    · rw [gateAt_patch_ne C h g _ (by omega)]
      exact (junkData hgJ).2.1
    · simpa [patch] using (junkData hgJ).1
    · rw [gateVal_patch_before hh hgh]
      exact hx

lemma no_both_colors_of_reaches {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (noOne : ∀D : Circuit, IsLeastAO G D → (junk G D).card ≠ 1)
    {C : Circuit} (hL : IsLeastAO G C) (hT : TopForm G C) (g h : ℕ)
    (hJ : junk G C = {g,h}) (hgh : g<h) (s : Fin n → Bool)
    (hcol : ∀u v, G.Adj u v → s u ≠ s v)
    (hboth : ∀c, gateVal n C h (fullColor s c) = true)
    (b : Fin 2) (hreach : OrReaches n C (opnd C h b) g) : False := by
  have hhJ : h ∈ junk G C := by simp [hJ]
  have hh := (junkData hhJ).1
  let d : Fin 2 := ⟨1-b.val,by omega⟩
  have hbd : b ≠ d := by
    intro he
    have hv := congrArg Fin.val he
    dsimp [d] at hv
    omega
  let D := patch C h (aliasGate (opnd C h d))
  have hDL : IsLeastAO G D := by
    refine ⟨alias_ao hL.1 hh d, alias_correct G hL hT g h hJ hgh s hcol hboth b d hbd hreach, ?_⟩
    intro E hEAO hEF
    have hmin := hL.2.2 E hEAO hEF
    simpa [D,patch,Circuit.size] using hmin
  apply noOne D hDL
  rw [alias_junk_exact G hL.1 hT g h hJ hgh s hcol hboth b d hbd hreach]
  exact Finset.card_singleton g

end PEqualNP.Outside.L_meta_5012.MixedOuter

namespace PEqualNP.Outside.L_meta_5012.PathCompression

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
  PEqualNP.Outside.L_meta_5012.Structural

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

lemma inCone_lt {i j : ℕ} (hc : InCone n C i j) : i < j := by
  have go : ∀ j i, InCone n C i j → i < j := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro i hc
      obtain ⟨_, k, hkj, _, hi⟩ := (inCone_iff n C i j).mp hc
      rcases hi with rfl | hi
      · exact hkj
      · exact (ih k hkj i hi).trans hkj
  exact go j i hc

lemma inCone_trans {i j k : ℕ} (hij : InCone n C i j) (hjk : InCone n C j k) :
    InCone n C i k := by
  have go : ∀ k j, InCone n C j k → InCone n C i j → InCone n C i k := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro j hjk hij
      obtain ⟨hk, t, htk, htin, hjt⟩ := (inCone_iff n C j k).mp hjk
      apply (inCone_iff n C i k).mpr
      refine ⟨hk, t, htk, htin, Or.inr ?_⟩
      rcases hjt with rfl | hjt
      · exact hij
      · exact ih t htk j hjt hij
  exact go k j hjk hij

lemma junk_spec {a : ℕ} (ha : a ∈ junk G C) :
    a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧
      ∃ x : Fin n → Bool, gateVal n C a x = true ∧ graphFun G ∅ x = false := by
  simp only [junk, gatesWhere, Finset.mem_filter, Finset.mem_range] at ha
  exact ⟨ha.1, ha.2.1, ha.2.2.2⟩

lemma and_ancestor_junk (hTop : TopForm G C) {a k : ℕ}
    (ha : a < C.gates.length) (hand : (gateAt C a).op = GateOp.and)
    (hk : k < C.gates.length) (hkand : (gateAt C k).op = GateOp.and)
    (hc : InCone n C k a) : k ∈ junk G C := by
  have hnb : ¬ BelowF G C k := fun hb => hTop k hk a ha hkand hb hand hc
  have hd : IsDirtyAnd n G C k := by
    unfold IsDirtyAnd IsDirty
    refine ⟨hkand, hk, ?_⟩
    by_contra he
    apply hnb
    intro x hx
    by_contra hf
    exact he ⟨x, hx, Bool.eq_false_iff.mpr hf⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hd⟩

lemma opnd_mem (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
    opnd C a b ∈ (gateAt C a).inputs := by
  have hlen := hAO.2.2 _ (gateAt_mem ha)
  unfold opnd
  have hb : b.val < (gateAt C a).inputs.length := by omega
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb, Option.getD_some]
  exact List.getElem_mem hb

lemma opnd_lt (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
    opnd C a b < n + a := hAO.2.1 a ha _ (opnd_mem hAO ha b)

lemma mem_inputs_iff_opnd (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) (w : ℕ) :
    w ∈ (gateAt C a).inputs ↔ ∃ b : Fin 2, opnd C a b = w := by
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem ha))
  constructor
  · intro hw
    rw [hin] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact ⟨0, by simp [opnd, hin]⟩
    · exact ⟨1, by simp [opnd, hin]⟩
  · rintro ⟨b, rfl⟩
    exact opnd_mem hAO ha b

lemma upper_reaches (hAO : IsAO2 n C) (hTop : TopForm G C) {g h : ℕ}
    (hj : junk G C = {g, h}) (cone : InCone n C g h) :
    ∃ b : Fin 2, OrReaches n C (opnd C h b) g := by
  have hgm : g ∈ junk G C := by rw [hj]; simp
  have hhm : h ∈ junk G C := by rw [hj]; simp
  obtain ⟨hg, hgand, _⟩ := junk_spec hgm
  obtain ⟨hh, hhand, _⟩ := junk_spec hhm
  have only_g : ∀ k, InCone n C k h → (gateAt C k).op ≠ GateOp.or → k = g := by
    intro k hkh hnor
    have hkh' := inCone_lt hkh
    have hk : k < C.gates.length := by omega
    have hkand : (gateAt C k).op = GateOp.and := by
      rcases hAO.1 _ (gateAt_mem hk) with hand | hor
      · exact hand
      · exact (hnor hor).elim
    have hkj := and_ancestor_junk hTop hh hhand hk hkand hkh
    have hc : k = g ∨ k = h := by simpa [hj] using hkj
    omega
  have go : ∀ k, InCone n C k h → (g = k ∨ InCone n C g k) →
      OrReaches n C (n + k) g := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hkh hgk
      rcases hgk with rfl | hgk
      · exact (orReaches_iff n C g g).mpr ⟨hg, Or.inl rfl⟩
      · have hgk' := inCone_lt hgk
        have hkor : (gateAt C k).op = GateOp.or := by
          by_contra hnor
          have hkg := only_g k hkh hnor
          omega
        obtain ⟨hk, t, htk, htin, hgt⟩ := (inCone_iff n C g k).mp hgk
        have htkc : InCone n C t k :=
          (inCone_iff n C t k).mpr ⟨hk, t, htk, htin, Or.inl rfl⟩
        have hth := inCone_trans htkc hkh
        exact (orReaches_iff n C k g).mpr
          ⟨hk, Or.inr ⟨hkor, n + t, htin, by omega, ih t htk hth hgt⟩⟩
  obtain ⟨_, k, hkh, hkin, hgk⟩ := (inCone_iff n C g h).mp cone
  have hkc : InCone n C k h := (inCone_iff n C k h).mpr ⟨hh, k, hkh, hkin, Or.inl rfl⟩
  obtain ⟨b, hb⟩ := (mem_inputs_iff_opnd hAO hh (n + k)).mp hkin
  refine ⟨b, ?_⟩
  rw [hb]
  exact go k hkc hgk

end PEqualNP.Outside.L_meta_5012.PathCompression

namespace PEqualNP.Outside.L_meta_5012.MixedOuter
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.Outside.L_meta_5012

lemma no_both_colors_nested {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (noOne : ∀D : Circuit, IsLeastAO G D → (junk G D).card ≠ 1)
    {C : Circuit} (hL : IsLeastAO G C) (hT : TopForm G C) (g h : ℕ)
    (hJ : junk G C = {g,h}) (hgh : g<h) (hcone : InCone n C g h)
    (s : Fin n → Bool) (hcol : ∀u v, G.Adj u v → s u ≠ s v)
    (hboth : ∀c, gateVal n C h (fullColor s c) = true) : False := by
  obtain ⟨b,hb⟩ := PathCompression.upper_reaches hL.1 hT hJ hcone
  exact no_both_colors_of_reaches G noOne hL hT g h hJ hgh s hcol hboth b hb

end PEqualNP.Outside.L_meta_5012.MixedOuter

namespace PEqualNP.Outside.L_meta_5012.OrSplit

def indexedProgram {α : Type*} (S : ℕ → Finset α) (k : ℕ) : List (Finset α) :=
  (List.range k).reverse.map S

lemma indexedProgram_available {α : Type*} [DecidableEq α]
    (S : ℕ → Finset α) (k i : ℕ) (hi : i < k) : available (indexedProgram S k) (S i) := by
  exact Or.inr (List.mem_map.mpr ⟨i, by simpa using hi, rfl⟩)

lemma indexedProgram_length {α : Type*} (S : ℕ → Finset α) (k : ℕ) :
    (indexedProgram S k).length = k := by
  simp [indexedProgram]

lemma indexedProgram_valid {α : Type*} [DecidableEq α]
    (S : ℕ → Finset α) (k : ℕ)
    (hdeps : ∀ i < k, ∃ A B : Finset α,
      (A.card = 1 ∨ ∃ j < i, A = S j) ∧
      (B.card = 1 ∨ ∃ j < i, B = S j) ∧ S i = A ∪ B) :
    valid (indexedProgram S k) := by
  induction k with
  | zero => trivial
  | succ k ih =>
    have hprev := ih (fun i hi => hdeps i (by omega))
    obtain ⟨A, B, hA, hB, he⟩ := hdeps k (by omega)
    have ha : available (indexedProgram S k) A := by
      rcases hA with h | ⟨j, hj, rfl⟩
      · exact Or.inl h
      · exact indexedProgram_available S k j hj
    have hb : available (indexedProgram S k) B := by
      rcases hB with h | ⟨j, hj, rfl⟩
      · exact Or.inl h
      · exact indexedProgram_available S k j hj
    have hform : indexedProgram S (k + 1) = S k :: indexedProgram S k := by
      simp [indexedProgram, List.range_succ, List.reverse_append]
    rw [hform]
    exact ⟨hprev, A, B, ha, hb, he⟩

lemma indexedProgram_source_bound {α : Type*} [DecidableEq α]
    (S : ℕ → Finset α) (k : ℕ)
    (hdeps : ∀ i < k, ∃ A B : Finset α,
      (A.card = 1 ∨ ∃ j < i, A = S j) ∧
      (B.card = 1 ∨ ∃ j < i, B = S j) ∧ S i = A ∪ B)
    (a b : ℕ) (ha : a < k) (hb : b < k) :
    twoCost (S a) (S b) ≤ k := by
  have h := twoCost_le_program (indexedProgram S k) (indexedProgram_valid S k hdeps)
    (S a) (S b) (indexedProgram_available S k a ha) (indexedProgram_available S k b hb)
  simpa only [indexedProgram_length] using h

def regionProgram {α : Type*} (S : ℕ → Finset α) (I : List ℕ) : List (Finset α) :=
  I.reverse.map S

lemma regionProgram_available {α : Type*} [DecidableEq α]
    (S : ℕ → Finset α) (I : List ℕ) (i : ℕ) (hi : i ∈ I) :
    available (regionProgram S I) (S i) := by
  exact Or.inr (List.mem_map.mpr ⟨i, by simpa using hi, rfl⟩)

lemma regionProgram_length {α : Type*} (S : ℕ → Finset α) (I : List ℕ) :
    (regionProgram S I).length = I.length := by
  simp [regionProgram]

lemma regionProgram_valid {α : Type*} [DecidableEq α]
    (S : ℕ → Finset α) (I : List ℕ) (hsort : I.Pairwise (· < ·))
    (hdeps : ∀ i ∈ I, ∃ A B : Finset α,
      (A.card = 1 ∨ ∃ j ∈ I, j < i ∧ A = S j) ∧
      (B.card = 1 ∨ ∃ j ∈ I, j < i ∧ B = S j) ∧ S i = A ∪ B) :
    valid (regionProgram S I) := by
  induction I using List.reverseRec with
  | nil => trivial
  | append_singleton I i ih =>
    have hsortI : I.Pairwise (· < ·) := (List.pairwise_append.mp hsort).1
    have hbefore : ∀ j ∈ I, j < i := by
      intro j hj
      exact List.Pairwise.rel_of_mem_append hsort hj (by simp)
    have earlier_mem : ∀ j q, j ∈ I → q ∈ I ++ [i] → q < j → q ∈ I := by
      intro j q hj hq hqj
      rcases List.mem_append.mp hq with hq | hq
      · exact hq
      · simp only [List.mem_singleton] at hq
        subst q
        have hji := hbefore j hj
        omega
    have hdepsI : ∀ j ∈ I, ∃ A B : Finset α,
        (A.card = 1 ∨ ∃ q ∈ I, q < j ∧ A = S q) ∧
        (B.card = 1 ∨ ∃ q ∈ I, q < j ∧ B = S q) ∧ S j = A ∪ B := by
      intro j hj
      obtain ⟨A, B, hA, hB, he⟩ := hdeps j (List.mem_append_left _ hj)
      refine ⟨A, B, ?_, ?_, he⟩
      · rcases hA with h | ⟨q, hq, hqj, heq⟩
        · exact Or.inl h
        · exact Or.inr ⟨q, earlier_mem j q hj hq hqj, hqj, heq⟩
      · rcases hB with h | ⟨q, hq, hqj, heq⟩
        · exact Or.inl h
        · exact Or.inr ⟨q, earlier_mem j q hj hq hqj, hqj, heq⟩
    have hprev := ih hsortI hdepsI
    obtain ⟨A, B, hA, hB, he⟩ := hdeps i (by simp)
    have hchild : ∀ X : Finset α,
        (X.card = 1 ∨ ∃ j ∈ I ++ [i], j < i ∧ X = S j) →
        available (regionProgram S I) X := by
      intro X hX
      rcases hX with h | ⟨j, hj, hji, rfl⟩
      · exact Or.inl h
      · apply regionProgram_available S I j
        rcases List.mem_append.mp hj with hj | hj
        · exact hj
        · simp only [List.mem_singleton] at hj
          omega
    have hform : regionProgram S (I ++ [i]) = S i :: regionProgram S I := by
      simp [regionProgram, List.reverse_append]
    rw [hform]
    exact ⟨hprev, A, B, hchild A hA, hchild B hB, he⟩

lemma regionProgram_source_bound {α : Type*} [DecidableEq α]
    (S : ℕ → Finset α) (I : List ℕ) (hsort : I.Pairwise (· < ·))
    (hdeps : ∀ i ∈ I, ∃ A B : Finset α,
      (A.card = 1 ∨ ∃ j ∈ I, j < i ∧ A = S j) ∧
      (B.card = 1 ∨ ∃ j ∈ I, j < i ∧ B = S j) ∧ S i = A ∪ B)
    (a b : ℕ) (ha : a ∈ I) (hb : b ∈ I) :
    twoCost (S a) (S b) ≤ I.length := by
  have h := twoCost_le_program (regionProgram S I) (regionProgram_valid S I hsort hdeps)
    (S a) (S b) (regionProgram_available S I a ha) (regionProgram_available S I b hb)
  simpa only [regionProgram_length] using h

end PEqualNP.Outside.L_meta_5012.OrSplit

namespace PEqualNP.Outside.L_meta_5012.PureCnfSemantic

open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def Covers {n : ℕ} (G : SimpleGraph (Fin n)) (K : Finset (Fin n)) : Prop :=
  ∀ u v : Fin n, G.Adj u v → u ∈ K ∨ v ∈ K

def InclusionMinimalCover {n : ℕ} (G : SimpleGraph (Fin n))
    (K : Finset (Fin n)) : Prop :=
  Covers G K ∧ ∀ J : Finset (Fin n), J ⊆ K → Covers G J → K ⊆ J

def rawOr {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∃ v ∈ S, x v = true)

def cnf {n k : ℕ} (S : Fin k → Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∀ i : Fin k, rawOr (S i) x = true)

lemma cnf_true {n k : ℕ} (S : Fin k → Finset (Fin n)) (x : Fin n → Bool) :
    cnf S x = true ↔ ∀ i : Fin k, ∃ v ∈ S i, x v = true := by
  simp [cnf, rawOr]

lemma clauses_cover {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Fin k → Finset (Fin n)) (h : graphFun G ∅ = cnf S) (i : Fin k) :
    Covers G (S i) := by
  intro u v huv
  have hF : graphFun G ∅ (pairInput u v) = true := by
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq]
    exact ⟨u, v, huv, by simp [pairInput], by simp [pairInput]⟩
  have hC : cnf S (pairInput u v) = true := (congrFun h _).symm.trans hF
  obtain ⟨w, hw, hval⟩ := (cnf_true S _).mp hC i
  have hwuv : w = u ∨ w = v := by simpa [pairInput] using hval
  rcases hwuv with rfl | rfl
  · exact Or.inl hw
  · exact Or.inr hw

lemma complement_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (K : Finset (Fin n)) (hK : Covers G K) :
    graphFun G ∅ (fun v => decide (v ∉ K)) = false := by
  apply Bool.eq_false_iff.mpr
  intro hF
  have hEdge : ∃ u v : Fin n, G.Adj u v ∧ u ∉ K ∧ v ∉ K := by
    simpa [graphFun] using hF
  obtain ⟨u, v, huv, hu, hv⟩ := hEdge
  rcases hK u v huv with h | h
  · exact hu h
  · exact hv h

lemma clause_subset_of_cover {n k : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (S : Fin k → Finset (Fin n))
    (h : graphFun G ∅ = cnf S) (K : Finset (Fin n)) (hK : Covers G K) :
    ∃ i : Fin k, S i ⊆ K := by
  classical
  let x : Fin n → Bool := fun v => decide (v ∉ K)
  have hfalse : graphFun G ∅ x = false := complement_false G K hK
  have hnot : ¬ ∀ i : Fin k, ∃ v ∈ S i, x v = true := by
    intro hall
    have htrue : graphFun G ∅ x = true :=
      (congrFun h x).trans ((cnf_true S x).mpr hall)
    rw [hfalse] at htrue
    contradiction
  obtain ⟨i, hi⟩ := Classical.not_forall.mp hnot
  refine ⟨i, ?_⟩
  intro v hv
  by_contra hvK
  exact hi ⟨v, hv, by simp [x, hvK]⟩

lemma minimal_cover_occurs {n k : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (S : Fin k → Finset (Fin n))
    (h : graphFun G ∅ = cnf S) (K : Finset (Fin n))
    (hK : InclusionMinimalCover G K) : ∃ i : Fin k, S i = K := by
  obtain ⟨i, hi⟩ := clause_subset_of_cover G S h K hK.1
  exact ⟨i, Finset.Subset.antisymm hi (hK.2 (S i) hi (clauses_cover G S h i))⟩

lemma cover_iff_contains_clause {n k : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (S : Fin k → Finset (Fin n))
    (h : graphFun G ∅ = cnf S) (K : Finset (Fin n)) :
    Covers G K ↔ ∃ i : Fin k, S i ⊆ K := by
  constructor
  · exact clause_subset_of_cover G S h K
  · rintro ⟨i, hi⟩ u v huv
    exact (clauses_cover G S h i u v huv).imp (fun hv => hi hv) (fun hv => hi hv)

lemma minimal_cover_family_card_le {n k : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (S : Fin k → Finset (Fin n))
    (h : graphFun G ∅ = cnf S) (T : Finset (Finset (Fin n)))
    (hT : ∀ K ∈ T, InclusionMinimalCover G K) : T.card ≤ k := by
  classical
  have hsub : T ⊆ Finset.univ.image S := by
    intro K hK
    obtain ⟨i, hi⟩ := minimal_cover_occurs G S h K (hT K hK)
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩
  calc
    T.card ≤ (Finset.univ.image S).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_image_le
    _ = k := by simp

lemma color_minimal_cover {n : ℕ} (G : SimpleGraph (Fin n)) (s : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (hnoniso : ∀ u, ∃ v, G.Adj u v) (b : Bool) :
    InclusionMinimalCover G (Finset.univ.filter fun w => s w = b) := by
  constructor
  · intro u v huv
    have hne := hbip u v huv
    cases hsu : s u <;> cases hsv : s v <;> cases b <;> simp_all
  · intro K hK hcover u hu
    obtain ⟨v, huv⟩ := hnoniso u
    rcases hcover u v huv with hku | hkv
    · exact hku
    · have hsu : s u = b := (Finset.mem_filter.mp hu).2
      have hsv : s v = b := (Finset.mem_filter.mp (hK hkv)).2
      exact (hbip u v huv (hsu.trans hsv.symm)).elim

lemma color_class_occurs {n k : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (S : Fin k → Finset (Fin n))
    (h : graphFun G ∅ = cnf S) (s : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (hnoniso : ∀ u, ∃ v, G.Adj u v) (b : Bool) :
    ∃ i : Fin k, S i = Finset.univ.filter (fun w => s w = b) :=
  minimal_cover_occurs G S h _ (color_minimal_cover G s hbip hnoniso b)

lemma both_colors_occur {n k : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (S : Fin k → Finset (Fin n))
    (h : graphFun G ∅ = cnf S) (s : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (hnoniso : ∀ u, ∃ v, G.Adj u v) :
    ∃ i j : Fin k, S i = Finset.univ.filter (fun w => s w = false) ∧
      S j = Finset.univ.filter (fun w => s w = true) := by
  obtain ⟨i, hi⟩ := color_class_occurs G S h s hbip hnoniso false
  obtain ⟨j, hj⟩ := color_class_occurs G S h s hbip hnoniso true
  exact ⟨i, j, hi, hj⟩

lemma cover_has_color_of_ne_other {n : ℕ} (G : SimpleGraph (Fin n))
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (hnoniso : ∀ u, ∃ v, G.Adj u v) (K : Finset (Fin n))
    (hK : Covers G K) (b : Bool)
    (hne : K ≠ Finset.univ.filter (fun w => s w = !b)) :
    ∃ v ∈ K, s v = b := by
  classical
  by_contra hno
  have hsub : K ⊆ Finset.univ.filter (fun w => s w = !b) := by
    intro v hv
    have hvb : s v ≠ b := fun h => hno ⟨v, hv, h⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    cases hvs : s v <;> cases b <;> simp_all
  apply hne
  exact Finset.Subset.antisymm hsub
    ((color_minimal_cover G s hbip hnoniso (!b)).2 K hsub hK)

lemma non_color_cover_is_mixed {n : ℕ} (G : SimpleGraph (Fin n))
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (hnoniso : ∀ u, ∃ v, G.Adj u v) (K : Finset (Fin n))
    (hK : Covers G K)
    (hL : K ≠ Finset.univ.filter (fun w => s w = false))
    (hR : K ≠ Finset.univ.filter (fun w => s w = true)) :
    (∃ u ∈ K, s u = false) ∧ (∃ v ∈ K, s v = true) := by
  exact ⟨cover_has_color_of_ne_other G s hbip hnoniso K hK false hR,
    cover_has_color_of_ne_other G s hbip hnoniso K hK true hL⟩

end PEqualNP.Outside.L_meta_5012.PureCnfSemantic

namespace PEqualNP.Outside.L_meta_5012.DominatedNested

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.EdgeOwnership
open PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_5012.Structural

lemma reached_value {n : ℕ} {C : Circuit} {w g : ℕ} (x : Fin n → Bool)
    (hr : OrReaches n C w g) (hv : gateVal n C g x = true) :
    val C (List.ofFn x) w = true := by
  apply orStep_up (n := n) (by simp) (orReaches_reach g w hr).1
  simpa only [gateVal_eq_val] using hv

lemma double_reach_dominates {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {g h : ℕ} (hh : h < C.gates.length) (hop : (gateAt C h).op = GateOp.and)
    (hr : ∀ b : Fin 2, OrReaches n C (opnd C h b) g) :
    ∀ x, gateVal n C g x = true → gateVal n C h x = true := by
  intro x hx
  apply (andValOperands hAO hh hop x).mpr
  intro b
  exact reached_value x (hr b) hx

lemma no_opposite_of_dominates {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] {C : Circuit} (hAO : IsAO2 n C)
    {g h : ℕ} (hg : g ∈ junk G C)
    (hdom : ∀ x, gateVal n C g x = true → gateVal n C h x = true)
    {a : ℕ} (ha : a ∈ tops G C) (b : Fin 2)
    (hrg : OrReaches n C (opnd C a b) g)
    (hrh : OrReaches n C (opnd C a (1-b)) h) : False := by
  obtain ⟨x, hx, hfalse⟩ := (junkData hg).2.2
  have hhx := hdom x hx
  obtain ⟨hal, hao, hbelow⟩ := topData ha
  have hat : gateVal n C a x = true := by
    apply (andValOperands hAO hal hao x).mpr
    intro d
    have hd : d = b ∨ d = 1-b := by fin_cases b <;> fin_cases d <;> decide
    rcases hd with rfl | rfl
    · exact reached_value x hrg hx
    · exact reached_value x hrh hhx
  have ht := hbelow x hat
  rw [hfalse] at ht
  contradiction

lemma no_opposite_of_double_reach {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] {C : Circuit} (hAO : IsAO2 n C)
    {g h : ℕ} (hg : g ∈ junk G C) (hh : h ∈ junk G C)
    (hr : ∀ b : Fin 2, OrReaches n C (opnd C h b) g)
    {a : ℕ} (ha : a ∈ tops G C) (b : Fin 2)
    (hrg : OrReaches n C (opnd C a b) g)
    (hrh : OrReaches n C (opnd C a (1-b)) h) : False :=
  no_opposite_of_dominates G hAO hg
    (double_reach_dominates hAO (junkData hh).1 (junkData hh).2.1 hr) ha b hrg hrh

end PEqualNP.Outside.L_meta_5012.DominatedNested

namespace PEqualNP.Outside.L_meta_5012.MixedLowerClassification
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open PEqualNP.Outside.L_meta_5012.Structural PEqualNP.Outside.L_meta_5012.Tight

def colorInput {n : ℕ} (s : Fin n → Bool) (c : Bool) : Fin n → Bool :=
  fun v => decide (s v = c)

lemma lower_raw_hits_both_colors {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hT : TopForm G C) (g h : ℕ)
    (hJ : junk G C = {g,h}) (hgh : g<h) (s : Fin n → Bool)
    (hgboth : ∀c, gateVal n C g (colorInput s c) = true) :
    ∀b : Fin 2, ∀c : Bool, ∃u ∈ side C g b, s u = c := by
  have hgJ : g ∈ junk G C := by simp [hJ]
  intro b c
  have hv := (andValOperands hAO (junkData hgJ).1 (junkData hgJ).2.1 _).mp (hgboth c) b
  rw [pure_wire_value C hAO _ (inner_operand_pure G C g h hAO hT hJ hgh b)] at hv
  obtain ⟨u,hu,huc⟩ := of_decide_eq_true hv
  exact ⟨u,hu,of_decide_eq_true huc⟩

lemma opposite_operand_classification {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hT : TopForm G C) (g h : ℕ)
    (hJ : junk G C = {g,h}) (s : Fin n → Bool)
    (hgboth : ∀c, gateVal n C g (colorInput s c) = true)
    (c : Bool) (hhfalse : gateVal n C h (colorInput s c) = false)
    (b d : Fin 2) (hbd : b ≠ d) (hreach : OrReaches n C (opnd C h b) g) :
    PureWire n C (opnd C h d) ∧
    (side (n := n) C h d).Nonempty ∧
    (∀u ∈ side (n := n) C h d, s u = !c) ∧
    gateVal n C h (colorInput s (!c)) = true := by
  have hhJ : h ∈ junk G C := by simp [hJ]
  have hh := (junkData hhJ).1
  have hhand := (junkData hhJ).2.1
  have hbtrue (k : Bool) : val C (List.ofFn (colorInput s k)) (opnd C h b) = true :=
    orStep_up (n := n) (by simp) (orReaches_reach g _ hreach).1 (hgboth k)
  have hdfalse : val C (List.ofFn (colorInput s c)) (opnd C h d) = false := by
    apply Bool.eq_false_iff.mpr
    intro hdtrue
    have hhtrue : gateVal n C h (colorInput s c) = true := by
      apply (andValOperands hAO hh hhand _).mpr
      intro i
      have hi : i=b ∨ i=d := by omega
      rcases hi with rfl | rfl
      · exact hbtrue c
      · exact hdtrue
    rw [hhfalse] at hhtrue
    cases hhtrue
  have hpure : PureWire n C (opnd C h d) := by
    intro j hj hja hr
    have hjunk := operandOrAndJunk hAO hT hh hhand hr hja
    simp only [hJ,Finset.mem_insert,Finset.mem_singleton] at hjunk
    rcases hjunk with he | he
    · subst j
      have hv := orStep_up (n := n) (by simp) (orReaches_reach g _ hr).1 (hgboth c)
      rw [hdfalse] at hv
      cases hv
    · subst j
      have hcone := operandReachCone hAO hh hr
      have hlt := Semantics.inCone_lt n C h h hcone
      omega
  have hmono : ∀u ∈ side (n := n) C h d, s u = !c := by
    intro u hu
    have hne : s u ≠ c := by
      intro heq
      have hv := reach_var_val (colorInput s c) _ u (mem_orIn_reach u hu)
        (by simp [colorInput,heq])
      rw [hdfalse] at hv
      cases hv
    cases hsu : s u <;> cases c <;> simp_all
  have hnonempty : (side (n := n) C h d).Nonempty := by
    obtain ⟨x,hx,_⟩ := (junkData hhJ).2.2
    have hv := (andValOperands hAO hh hhand x).mp hx d
    rw [pure_wire_value C hAO _ hpure] at hv
    obtain ⟨u,hu,_⟩ := of_decide_eq_true hv
    exact ⟨u,hu⟩
  refine ⟨hpure,hnonempty,hmono,?_⟩
  apply (andValOperands hAO hh hhand _).mpr
  intro i
  have hi : i=b ∨ i=d := by omega
  rcases hi with rfl | rfl
  · exact hbtrue (!c)
  · obtain ⟨u,hu⟩ := hnonempty
    exact reach_var_val (colorInput s (!c)) _ u (mem_orIn_reach u hu)
      (by simp [colorInput,hmono u hu])

lemma wire_all_true {n : ℕ} (C : Circuit) (hAO : IsAO2 n C) :
    ∀w, w < n+C.gates.length → val C (List.ofFn (fun _ : Fin n => true)) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hwn : w<n
    · exact val_ofFn C (fun _ : Fin n => true) ⟨w,hwn⟩
    · obtain ⟨j,rfl⟩ : ∃j,w=n+j := ⟨w-n,by omega⟩
      have hj : j<C.gates.length := by omega
      rcases hAO.1 _ (gateAt_mem hj) with hand | hor
      · apply (val_and (n := n) (by simp) hj hand).mpr
        intro i hi
        have hib := hAO.2.1 j hj i hi
        exact ⟨hib,ih i hib (by omega)⟩
      · obtain ⟨p,q,hpq⟩ := binaryInputs hAO hj
        have hp : p ∈ (gateAt C j).inputs := by simp [hpq]
        have hpb := hAO.2.1 j hj p hp
        exact (val_or (n := n) (by simp) hj hor).mpr ⟨p,hp,hpb,ih p hpb (by omega)⟩

lemma colorInput_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hcol : ∀u v, G.Adj u v → s u ≠ s v) (c : Bool) :
    graphFun G ∅ (colorInput s c) = false := by
  apply Bool.eq_false_iff.mpr
  intro ht
  obtain ⟨u,v,huv,hu,hv⟩ := (Geometry.graph_true G _).mp ht
  exact hcol u v huv ((of_decide_eq_true hu).trans (of_decide_eq_true hv).symm)

lemma no_top_operand_both_colors {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hT : TopForm G C)
    (s : Fin n → Bool) (hcol : ∀u v, G.Adj u v → s u ≠ s v)
    (hJcolor : ∀j ∈ junk G C, ∃c, gateVal n C j (colorInput s c) = true)
    {a : ℕ} (ha : a ∈ tops G C) (b : Fin 2)
    (hboth : ∀c, val C (List.ofFn (colorInput s c)) (opnd C a b) = true) : False := by
  have hav := topData ha
  let d : Fin 2 := ⟨1-b.val,by omega⟩
  have hbd : b ≠ d := by
    intro he
    have hv := congrArg Fin.val he
    dsimp [d] at hv
    omega
  have hdtrue := wire_all_true C hAO (opnd C a d)
    (lt_of_lt_of_le (opndBound hAO hav.1 d) (by omega))
  have hops : ∀j<C.gates.length, (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or :=
    fun j hj => hAO.1 _ (gateAt_mem hj)
  have hcolor : ∃c, val C (List.ofFn (colorInput s c)) (opnd C a d) = true := by
    rcases Semantics.down n C (fun _ => true) hops _ hdtrue with
      ⟨u,hu,_⟩ | ⟨j,hj,hr,hand,_⟩
    · exact ⟨s u,reach_var_val (colorInput s (s u)) _ u (mem_orIn_reach u hu)
        (by simp [colorInput])⟩
    · have hjunk := operandOrAndJunk hAO hT hav.1 hav.2.1 hr hand
      obtain ⟨c,hc⟩ := hJcolor j hjunk
      exact ⟨c,orStep_up (n := n) (by simp) (orReaches_reach j _ hr).1 hc⟩
  obtain ⟨c,hdc⟩ := hcolor
  have hatrue : gateVal n C a (colorInput s c) = true := by
    apply (andValOperands hAO hav.1 hav.2.1 _).mpr
    intro i
    have hi : i=b ∨ i=d := by omega
    rcases hi with rfl | rfl
    · exact hboth c
    · exact hdc
  have hf := hav.2.2 _ hatrue
  rw [colorInput_false G s hcol] at hf
  cases hf

lemma no_both_color_gate_reaches_top {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hT : TopForm G C)
    (s : Fin n → Bool) (hcol : ∀u v, G.Adj u v → s u ≠ s v)
    (hJcolor : ∀j ∈ junk G C, ∃c, gateVal n C j (colorInput s c) = true)
    (k : ℕ) (hkcolor : ∀c, gateVal n C k (colorInput s c) = true)
    {a : ℕ} (ha : a ∈ tops G C) (b : Fin 2)
    (hr : OrReaches n C (opnd C a b) k) : False := by
  apply no_top_operand_both_colors G C hAO hT s hcol hJcolor ha b
  intro c
  exact orStep_up (n := n) (by simp) (orReaches_reach k _ hr).1 (hkcolor c)

lemma no_top_reaches_lower {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hT : TopForm G C) (g h : ℕ)
    (hJ : junk G C = {g,h}) (s : Fin n → Bool)
    (hcol : ∀u v, G.Adj u v → s u ≠ s v)
    (hgboth : ∀c, gateVal n C g (colorInput s c) = true)
    (c : Bool) (hhcolor : gateVal n C h (colorInput s c) = true)
    {a : ℕ} (ha : a ∈ tops G C) (b : Fin 2)
    (hr : OrReaches n C (opnd C a b) g) : False := by
  apply no_both_color_gate_reaches_top G C hAO hT s hcol ?_ g hgboth ha b hr
  intro j hj
  simp only [hJ,Finset.mem_insert,Finset.mem_singleton] at hj
  rcases hj with rfl | rfl
  · exact ⟨false,hgboth false⟩
  · exact ⟨c,hhcolor⟩

end PEqualNP.Outside.L_meta_5012.MixedLowerClassification

namespace PEqualNP.Outside.L_meta_5012.Splice

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover


def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

lemma run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

lemma getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

lemma run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

lemma run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

lemma run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_prefix gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at']
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)


def Ok (n : ℕ) (gs : List Gate) : Prop :=
  ∀ j (hj : j < gs.length), ∃ o s t, gs[j] = ⟨o, [s, t]⟩ ∧ (o = GateOp.and ∨ o = GateOp.or) ∧
    s < n + j ∧ t < n + j

lemma ok_snoc {n : ℕ} {gs : List Gate} (h : Ok n gs) {o : GateOp} {s t : ℕ}
    (ho : o = GateOp.and ∨ o = GateOp.or) (hs : s < n + gs.length) (ht : t < n + gs.length) :
    Ok n (gs ++ [⟨o, [s, t]⟩]) := by
  intro j hj
  by_cases hlt : j < gs.length
  · rw [List.getElem_append_left hlt]; exact h j hlt
  · have : j = gs.length := by simp at hj; omega
    subst this
    exact ⟨o, s, t, by simp, ho, hs, ht⟩

open Classical in
noncomputable def dc (n : ℕ) (F : (Fin n → Bool) → Bool) (gs : List Gate) : ℕ :=
  ((Finset.range gs.length).filter fun i => (gs.getD i ⟨GateOp.or, []⟩).op = GateOp.and ∧
    ∃ x : Fin n → Bool, (run gs (List.ofFn x)).getD (n + i) false = true ∧ F x = false).card

open Classical in
lemma dc_snoc (n : ℕ) (F : (Fin n → Bool) → Bool) (gs : List Gate) (g : Gate) :
    dc n F (gs ++ [g]) ≤ dc n F gs + if g.op = GateOp.and ∧
      ∃ x : Fin n → Bool, (run (gs ++ [g]) (List.ofFn x)).getD (n + gs.length) false = true ∧
        F x = false then 1 else 0 := by
  unfold dc
  rw [List.length_append, List.length_singleton, Finset.range_add_one, Finset.filter_insert]
  have e : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
    simp [List.getD_eq_getElem?_getD]
  rw [e]
  have h1 : ((Finset.range gs.length).filter fun i =>
      ((gs ++ [g]).getD i ⟨GateOp.or, []⟩).op = GateOp.and ∧ ∃ x : Fin n → Bool,
        (run (gs ++ [g]) (List.ofFn x)).getD (n + i) false = true ∧ F x = false) =
      (Finset.range gs.length).filter fun i =>
      (gs.getD i ⟨GateOp.or, []⟩).op = GateOp.and ∧ ∃ x : Fin n → Bool,
        (run gs (List.ofFn x)).getD (n + i) false = true ∧ F x = false := by
    refine Finset.filter_congr fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    rw [getD_ltz _ _ _ _ hi']
    refine and_congr_right fun _ => exists_congr fun x => ?_
    rw [run_prefix gs [g] _ _ (by simp; omega)]
  rw [h1]
  split_ifs with h
  · exact (Finset.card_insert_le _ _)
  · simp


def Maps (n p : ℕ) (M : Finset ℕ) (gs : List Gate) (m : ℕ → ℕ)
    (V : (Fin n → Bool) → ℕ → Bool) : Prop :=
  ∀ w < n + p, (w < n ∨ w - n ∉ M) → m w < n + gs.length ∧
    ∀ x : Fin n → Bool, (run gs (List.ofFn x)).getD (m w) false = V x w

def Keeps (n p : ℕ) (Del : Finset ℕ) (gs : List Gate) (m : ℕ → ℕ)
    (op : ℕ → GateOp) : Prop :=
  ∀ j < p, j ∉ Del → ∃ k < gs.length, m (n + j) = n + k ∧
    (gs.getD k ⟨GateOp.or, []⟩).op = op j

lemma append_getD {α : Type} (z : α) (gs hs : List α) (k : ℕ) (hk : k < gs.length) :
    (gs ++ hs).getD k z = gs.getD k z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

lemma next_value (n : ℕ) (gs : List Gate) (o : GateOp) (a b : ℕ)
    (x : Fin n → Bool) :
    (run (gs ++ [⟨o, [a, b]⟩]) (List.ofFn x)).getD (n + gs.length) false =
      o.eval [(run gs (List.ofFn x)).getD a false,
        (run gs (List.ofFn x)).getD b false] := by
  rw [run_snoc]
  have heq : n + gs.length = (run gs (List.ofFn x)).length := by simp [run_length]
  rw [heq, getD_at]
  rfl

open Classical in
lemma build_splice
    (n N h r : ℕ) (M : Finset ℕ) (hnotM : h ∉ M)
    (op : ℕ → GateOp) (a b : ℕ → ℕ)
    (V : (Fin n → Bool) → ℕ → Bool) (F : (Fin n → Bool) → Bool)
    (hin : ∀ x w, w < n → V x w = (List.ofFn x).getD w false)
    (hop : ∀ j < N, op j = GateOp.and ∨ op j = GateOp.or)
    (hback : ∀ j < N, a j < n + j ∧ b j < n + j)
    (havoid : ∀ j < N, j ∉ insert h M →
      (a j < n ∨ a j - n ∉ M) ∧ (b j < n ∨ b j - n ∉ M))
    (hval : ∀ j < N, j ∉ insert h M → ∀ x,
      V x (n + j) = (op j).eval [V x (a j), V x (b j)])
    (block : ∀ (gs : List Gate) (m : ℕ → ℕ), Ok n gs → Maps n h M gs m V →
      ∃ (hs : List Gate) (o : ℕ), Ok n (gs ++ hs) ∧ hs.length ≤ r ∧
        o < n + (gs ++ hs).length ∧
        (∀ x : Fin n → Bool, (run (gs ++ hs) (List.ofFn x)).getD o false = V x (n + h)) ∧
        dc n F (gs ++ hs) ≤ dc n F gs) :
    ∀ p, p ≤ N → ∃ (gs : List Gate) (m : ℕ → ℕ),
      Ok n gs ∧ Maps n p M gs m V ∧ Keeps n p (insert h M) gs m op ∧
      gs.length + ((Finset.range p).filter (· ∈ insert h M)).card ≤
        p + (if h < p then r else 0) ∧
      dc n F gs ≤ ((Finset.range p).filter fun j => j ∉ insert h M ∧ op j = GateOp.and ∧
        ∃ x : Fin n → Bool, V x (n + j) = true ∧ F x = false).card := by
  classical
  intro p
  induction p with
  | zero =>
    intro _
    refine ⟨[], id, ?_, ?_, ?_, ?_, ?_⟩
    · intro j hj; simp at hj
    · intro w hw _
      refine ⟨by simpa using hw, fun x => ?_⟩
      exact (hin x w (by simpa using hw)).symm
    · intro j hj; omega
    · simp
    · simp [dc]
  | succ p ih =>
    intro hpN
    obtain ⟨gs, m, hok, hm, hkeep, hlen, hdirty⟩ := ih (by omega)
    have hp : p < N := by omega
    suffices hh : ∃ (hs : List Gate) (o : ℕ), Ok n (gs ++ hs) ∧
        (p ∉ M → o < n + (gs ++ hs).length) ∧
        (p ∉ M → ∀ x : Fin n → Bool,
          (run (gs ++ hs) (List.ofFn x)).getD o false = V x (n + p)) ∧
        (p ∉ insert h M → ∃ k < (gs ++ hs).length, o = n + k ∧
          ((gs ++ hs).getD k ⟨GateOp.or, []⟩).op = op p) ∧
        hs.length + (if p ∈ insert h M then 1 else 0) ≤ 1 + (if p = h then r else 0) ∧
        dc n F (gs ++ hs) ≤ dc n F gs +
          if p ∉ insert h M ∧ op p = GateOp.and ∧
            ∃ x : Fin n → Bool, V x (n + p) = true ∧ F x = false then 1 else 0 by
      obtain ⟨hs, o, h1, h2, h3, h4, h5, h6⟩ := hh
      refine ⟨gs ++ hs, Function.update m (n + p) o, h1, ?_, ?_, ?_, ?_⟩
      · intro w hw hvalid
        by_cases hwp : w = n + p
        · subst w
          rw [Function.update_self]
          have hpm : p ∉ M := by simpa using hvalid
          exact ⟨h2 hpm, h3 hpm⟩
        · rw [Function.update_of_ne hwp]
          obtain ⟨hbound, hvalue⟩ := hm w (by omega) hvalid
          refine ⟨by simp; omega, fun x => ?_⟩
          rw [run_prefix gs hs _ _ (by simpa using hbound)]
          exact hvalue x
      · intro j hj hjDel
        by_cases hjp : j = p
        · subst j
          rw [Function.update_self]
          exact h4 hjDel
        · obtain ⟨k, hk, heq, hopk⟩ := hkeep j (by omega) hjDel
          refine ⟨k, by simp; omega, ?_, ?_⟩
          · rw [Function.update_of_ne (by omega)]
            exact heq
          · rw [append_getD _ _ _ _ hk]
            exact hopk
      · rw [List.length_append, Finset.range_add_one, Finset.filter_insert]
        by_cases hDel : p ∈ insert h M
        · rw [ite_eq_left hDel, Finset.card_insert_of_notMem (by simp)]
          rw [ite_eq_left hDel] at h5
          by_cases hph : p = h
          · subst p
            simp only [lt_self_iff_false, ↓reduceIte, Nat.lt_succ_self] at hlen ⊢
            simp only [↓reduceIte] at h5
            omega
          · have hei : (h < p + 1) ↔ h < p := by omega
            simp only [ite_eq_right hph] at h5
            simp only [hei]
            omega
        · rw [ite_eq_right hDel]
          rw [ite_eq_right hDel] at h5
          have hph : p ≠ h := by intro heq; apply hDel; simp [heq]
          have hei : (h < p + 1) ↔ h < p := by omega
          simp only [ite_eq_right hph] at h5
          simp only [hei]
          omega
      · rw [Finset.range_add_one, Finset.filter_insert]
        split_ifs at h6 ⊢ with hj
        · rw [Finset.card_insert_of_notMem (by simp)]
          omega
        · omega
    by_cases hpM : p ∈ M
    · refine ⟨[], 0, by simpa using hok, fun h => False.elim (h hpM),
        fun h => False.elim (h hpM), ?_, ?_, ?_⟩
      · intro h; exact False.elim (h (Finset.mem_insert_of_mem hpM))
      · have hph : p ≠ h := by intro heq; subst p; exact hnotM hpM
        simp [hpM, hph]
      · simp [hpM]
    by_cases hph : p = h
    · subst p
      obtain ⟨hs, o, hb1, hb2, hb3, hb4, hb5⟩ := block gs m hok hm
      refine ⟨hs, o, hb1, fun _ => hb3, fun _ => hb4, ?_, ?_, ?_⟩
      · simp
      · simp; omega
      · simpa using hb5
    have hpDel : p ∉ insert h M := by simp [hph, hpM]
    obtain ⟨hap, hbp⟩ := hback p hp
    obtain ⟨haValid, hbValid⟩ := havoid p hp hpDel
    obtain ⟨haBound, haValue⟩ := hm (a p) hap haValid
    obtain ⟨hbBound, hbValue⟩ := hm (b p) hbp hbValid
    let g : Gate := ⟨op p, [m (a p), m (b p)]⟩
    have hnew : ∀ x : Fin n → Bool,
        (run (gs ++ [g]) (List.ofFn x)).getD (n + gs.length) false = V x (n + p) := by
      intro x
      rw [next_value, haValue x, hbValue x]
      exact (hval p hp hpDel x).symm
    refine ⟨[g], n + gs.length, ok_snoc hok (hop p hp) haBound hbBound, ?_, ?_, ?_, ?_, ?_⟩
    · intro _; simp
    · intro _; exact hnew
    · intro _
      refine ⟨gs.length, by simp, rfl, ?_⟩
      simp [g, List.getD_eq_getElem?_getD]
    · simp [hpDel, hph]
    · have hd := dc_snoc n F gs g
      have heq : (g.op = GateOp.and ∧ ∃ x : Fin n → Bool,
          (run (gs ++ [g]) (List.ofFn x)).getD (n + gs.length) false = true ∧ F x = false) ↔
          (p ∉ insert h M ∧ op p = GateOp.and ∧
            ∃ x : Fin n → Bool, V x (n + p) = true ∧ F x = false) := by
        simp only [g, hnew, hpDel, not_false_eq_true, true_and]
      rw [if_congr heq rfl rfl] at hd
      exact hd

lemma ok_isAO2 (n : ℕ) (gs : List Gate) (out : ℕ) (hok : Ok n gs) :
    PEqualNP.TopForm.IsAO2 n ⟨gs, out⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    obtain ⟨o, a, b, heq, hop, _, _⟩ := hok j hj
    simpa [heq] using hop
  · intro j hj w hw
    obtain ⟨o, a, b, heq, _, ha, hb⟩ := hok j hj
    have hgate : gateAt (⟨gs, out⟩ : Circuit) j = ⟨o, [a, b]⟩ := by
      change gs.getD j _ = _
      rw [List.getD_eq_getElem _ _ hj]
      exact heq
    rw [hgate] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact ha
    · exact hb
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    obtain ⟨o, a, b, heq, _, _, _⟩ := hok j hj
    simp [heq]

lemma isAO2_ok (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C) :
    Ok n C.gates := by
  intro j hj
  have heq : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
  have hmem : gateAt C j ∈ C.gates := by rw [heq]; exact List.getElem_mem hj
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (hC.2.2 _ hmem)
  refine ⟨(gateAt C j).op, a, b, ?_, hC.1 _ hmem, ?_, ?_⟩
  · rw [← heq]
    have hgate : ∀ (g : Gate), g.inputs = [a, b] → g = ⟨g.op, [a, b]⟩ := by
      intro g hg; cases g; cases hg; rfl
    exact hgate _ hab
  · exact hC.2.1 j hj a (by rw [hab]; simp)
  · exact hC.2.1 j hj b (by rw [hab]; simp)

lemma dc_eq_junk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (gs : List Gate) (out : ℕ) :
    dc n (graphFun G ∅) gs = (PEqualNP.TopForm.junk G ⟨gs, out⟩).card := by
  classical
  unfold dc PEqualNP.TopForm.junk PEqualNP.TopForm.gatesWhere
  congr 1
  apply Finset.filter_congr
  intro j hj
  have hj' : j < gs.length := Finset.mem_range.mp hj
  simp only [PEqualNP.CleanedNonEdge.IsDirtyAnd, PEqualNP.CleanedNonEdge.IsDirty,
    gateAt, PEqualNP.EdgeOwnership.gateVal, Circuit.wires, run, hj', true_and]

lemma dc_append_clean (n : ℕ) (F : (Fin n → Bool) → Bool) (gs hs : List Gate)
    (hclean : ∀ j, gs.length ≤ j → j < (gs ++ hs).length →
      ((gs ++ hs).getD j ⟨GateOp.or, []⟩).op = GateOp.and →
      ∀ x : Fin n → Bool,
        (run (gs ++ hs) (List.ofFn x)).getD (n + j) false = true → F x = true) :
    dc n F (gs ++ hs) = dc n F gs := by
  classical
  unfold dc
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  by_cases hj : j < gs.length
  · have hlong : j < (gs ++ hs).length := by simp; omega
    rw [append_getD _ _ _ _ hj]
    simp only [hj, hlong, true_and]
    refine and_congr_right fun _ => exists_congr fun x => ?_
    rw [run_prefix gs hs _ _ (by simp; omega)]
  · constructor
    · rintro ⟨hjlong, hop, x, hx, hFx⟩
      have ht := hclean j (by omega) hjlong hop x hx
      rw [hFx] at ht
      cases ht
    · rintro ⟨hj', _⟩
      exact False.elim (hj hj')

lemma kept_dirty {n p h : ℕ} {M : Finset ℕ} {gs : List Gate} {m : ℕ → ℕ}
    {V : (Fin n → Bool) → ℕ → Bool} {op : ℕ → GateOp}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (out : ℕ)
    (hm : Maps n p M gs m V) (hk : Keeps n p (insert h M) gs m op)
    (g : ℕ) (hg : g < p) (hgkeep : g ∉ insert h M) (hop : op g = GateOp.and)
    (hdirty : ∃ x : Fin n → Bool, V x (n + g) = true ∧ graphFun G ∅ x = false) :
    (PEqualNP.TopForm.junk G ⟨gs, out⟩).Nonempty := by
  classical
  obtain ⟨k, hklen, hmap, hkop⟩ := hk g hg hgkeep
  have hgM : g ∉ M := fun hm' => hgkeep (Finset.mem_insert_of_mem hm')
  have hv := (hm (n + g) (by omega) (Or.inr (by simpa using hgM))).2
  obtain ⟨x, hx, hFx⟩ := hdirty
  refine ⟨k, ?_⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr hklen, ?_⟩
  change (gs.getD k ⟨GateOp.or, []⟩).op = GateOp.and ∧
    k < gs.length ∧ ∃ x, (run gs (List.ofFn x)).getD (n + k) false = true ∧ graphFun G ∅ x = false
  refine ⟨?_, hklen, x, ?_, hFx⟩
  · exact hkop.trans hop
  · rw [← hmap, hv x]
    exact hx

open Classical in
lemma splice_complete
    (n N h r : ℕ) (M : Finset ℕ) (hnotM : h ∉ M) (hh : h < N)
    (hM : M ⊆ Finset.range N) (out : ℕ) (hout : out < n + N)
    (houtM : out < n ∨ out - n ∉ M)
    (op : ℕ → GateOp) (a b : ℕ → ℕ)
    (V : (Fin n → Bool) → ℕ → Bool)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hin : ∀ x w, w < n → V x w = (List.ofFn x).getD w false)
    (hop : ∀ j < N, op j = GateOp.and ∨ op j = GateOp.or)
    (hback : ∀ j < N, a j < n + j ∧ b j < n + j)
    (havoid : ∀ j < N, j ∉ insert h M →
      (a j < n ∨ a j - n ∉ M) ∧ (b j < n ∨ b j - n ∉ M))
    (hval : ∀ j < N, j ∉ insert h M → ∀ x,
      V x (n + j) = (op j).eval [V x (a j), V x (b j)])
    (houtput : ∀ x, V x out = graphFun G ∅ x)
    (block : ∀ (gs : List Gate) (m : ℕ → ℕ), Ok n gs → Maps n h M gs m V →
      ∃ (hs : List Gate) (o : ℕ), Ok n (gs ++ hs) ∧ hs.length ≤ r ∧
        o < n + (gs ++ hs).length ∧
        (∀ x : Fin n → Bool, (run (gs ++ hs) (List.ofFn x)).getD o false = V x (n + h)) ∧
        dc n (graphFun G ∅) (gs ++ hs) ≤ dc n (graphFun G ∅) gs) :
    ∃ (D : Circuit) (m : ℕ → ℕ), PEqualNP.TopForm.IsAO2 n D ∧
      circuitFun n D = graphFun G ∅ ∧
      Maps n N M D.gates m V ∧ Keeps n N (insert h M) D.gates m op ∧
      D.size + M.card + 1 ≤ N + r ∧
      (PEqualNP.TopForm.junk G D).card ≤ ((Finset.range N).filter fun j =>
        j ∉ insert h M ∧ op j = GateOp.and ∧
        ∃ x : Fin n → Bool, V x (n + j) = true ∧ graphFun G ∅ x = false).card := by
  obtain ⟨gs, m, hok, hm, hk, hlen, hdc⟩ :=
    build_splice n N h r M hnotM op a b V (graphFun G ∅)
      hin hop hback havoid hval block N le_rfl
  have hDel : ((Finset.range N).filter (· ∈ insert h M)) = insert h M := by
    ext j
    simp only [Finset.mem_filter]
    constructor
    · exact And.right
    · intro hj
      refine ⟨?_, hj⟩
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact Finset.mem_range.mpr hh
      · exact hM hj
  rw [hDel, Finset.card_insert_of_notMem hnotM, ite_eq_left hh] at hlen
  refine ⟨⟨gs, m out⟩, m, ok_isAO2 n gs (m out) hok, ?_, hm, hk, ?_, ?_⟩
  · funext x
    exact ((hm out hout houtM).2 x).trans (houtput x)
  · simpa only [Circuit.size, Nat.add_assoc] using hlen
  · rwa [dc_eq_junk G gs (m out)] at hdc

end PEqualNP.Outside.L_meta_5012.Splice

namespace PEqualNP.Outside.L_meta_5012.Alias

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.Outside.L_meta_5012.Splice

lemma ok_set_alias (n : ℕ) (gs : List Gate) (hok : Ok n gs)
    (j w : ℕ) (hw : w < n + j) :
    Ok n (gs.set j ⟨GateOp.or, [w, w]⟩) := by
  intro k hk
  have hk' : k < gs.length := by simpa using hk
  by_cases hkj : k = j
  · subst k
    refine ⟨GateOp.or, w, w, ?_, Or.inr rfl, hw, hw⟩
    simp
  · obtain ⟨o, a, b, hg, ho, ha, hb⟩ := hok k hk'
    refine ⟨o, a, b, ?_, ho, ha, hb⟩
    rw [List.getElem_set_ne (fun h => hkj h.symm)]
    exact hg

lemma gate_pair {n : ℕ} {C : Circuit} (h : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
    C.gates[j] = gateAt C j ∧ (gateAt C j).inputs = [opnd C j 0, opnd C j 1] ∧
    opnd C j 0 < n + j ∧ opnd C j 1 < n + j ∧
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) := by
  have e : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
  have hm : gateAt C j ∈ C.gates := by rw [e]; exact List.getElem_mem hj
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (h.2.2 _ hm)
  have ea : opnd C j 0 = a := by unfold opnd; rw [hab]; rfl
  have eb : opnd C j 1 = b := by unfold opnd; rw [hab]; rfl
  refine ⟨e.symm, by rw [hab, ea, eb], ?_, ?_, h.1 _ hm⟩
  · rw [ea]; exact h.2.1 j hj a (by rw [hab]; simp)
  · rw [eb]; exact h.2.1 j hj b (by rw [hab]; simp)

lemma gate_value {n : ℕ} {C : Circuit} (h : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length)
    (x : Fin n → Bool) :
    (run C.gates (List.ofFn x)).getD (n + j) false =
      (gateAt C j).op.eval [(run C.gates (List.ofFn x)).getD (opnd C j 0) false,
        (run C.gates (List.ofFn x)).getD (opnd C j 1) false] := by
  obtain ⟨heq, hin, ha, hb, _⟩ := gate_pair h hj
  have hh := run_gate C.gates (List.ofFn x) j hj
  rw [List.length_ofFn, heq, hin] at hh
  simpa [ha, hb] using hh

lemma least_output_valid {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (j : ℕ) (hj : j < C.gates.length) :
    C.output < n + C.gates.length := by
  by_contra hn
  have hfalse : ∀ x : Fin n → Bool, circuitFun n C x = false := by
    intro x
    apply List.getD_eq_default
    change (run C.gates (List.ofFn x)).length ≤ C.output
    rw [run_length, List.length_ofFn]
    omega
  let D : Circuit := ⟨[], n⟩
  have hD : IsAO2 n D := by simp [IsAO2, PEqualNP.EdgeOwnership.AndOrOnly, ReadsBack, D]
  have hDF : circuitFun n D = graphFun G ∅ := by
    funext x
    rw [← hL.2.1, hfalse]
    simp [D, circuitFun, Circuit.eval, Circuit.wires, List.getD_eq_getElem?_getD]
  have hs := hL.2.2 D hD hDF
  simp only [Circuit.size, D, List.length_nil] at hs
  omega

lemma least_patch_alias_impossible {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : IsLeastAO G C) (e w : ℕ) (he : e < C.gates.length) (hw : w < n + e)
    (hpatch : circuitFun n ⟨C.gates.set e ⟨GateOp.or, [w, w]⟩, C.output⟩ = graphFun G ∅) :
    False := by
  classical
  let P : Circuit := ⟨C.gates.set e ⟨GateOp.or, [w, w]⟩, C.output⟩
  have hP : IsAO2 n P := ok_isAO2 n P.gates P.output
    (ok_set_alias n C.gates (isAO2_ok n C hL.1) e w hw)
  have hlen : P.gates.length = C.gates.length := List.length_set
  have heP : e < P.gates.length := by rwa [hlen]
  let V : (Fin n → Bool) → ℕ → Bool := fun x v => (run P.gates (List.ofFn x)).getD v false
  let op : ℕ → GateOp := fun j => (gateAt P j).op
  let a : ℕ → ℕ := fun j => opnd P j 0
  let b : ℕ → ℕ := fun j => opnd P j 1
  have hin : ∀ x v, v < n → V x v = (List.ofFn x).getD v false := by
    intro x v hv
    exact run_input P.gates (List.ofFn x) v (by simpa using hv)
  have hop : ∀ j < P.gates.length, op j = GateOp.and ∨ op j = GateOp.or := by
    intro j hj
    exact (gate_pair hP hj).2.2.2.2
  have hback : ∀ j < P.gates.length, a j < n + j ∧ b j < n + j := by
    intro j hj
    exact ⟨(gate_pair hP hj).2.2.1, (gate_pair hP hj).2.2.2.1⟩
  have hval : ∀ j < P.gates.length, j ∉ insert e (∅ : Finset ℕ) → ∀ x,
      V x (n + j) = (op j).eval [V x (a j), V x (b j)] := by
    intro j hj _ x
    exact gate_value hP hj x
  have hgate : gateAt P e = ⟨GateOp.or, [w, w]⟩ := by
    simp [P, gateAt, List.getD_eq_getElem?_getD, he]
  have hVe : ∀ x, V x (n + e) = V x w := by
    intro x
    have hh := gate_value hP heP x
    simpa [V, opnd, hgate, GateOp.eval] using hh
  obtain ⟨D, m, hDAO, hDF, _, _, hsize, _⟩ :=
    splice_complete n P.gates.length e 0 ∅ (by simp) heP (by simp) P.output
      (by simpa only [P, List.length_set] using least_output_valid G C hL e he)
      (Or.inr (by simp)) op a b V G hin hop hback (by simp) hval
      (fun x => congrFun hpatch x) (by
        intro gs m hok hm
        have hmW := hm w hw (Or.inr (by simp))
        refine ⟨[], m w, by simpa using hok, by simp, by simpa using hmW.1, ?_, by simp⟩
        intro x
        simpa using (hmW.2 x).trans (hVe x).symm)
  have hmin := hL.2.2 D hDAO hDF
  simp only [Finset.card_empty, Nat.add_zero, hlen] at hsize
  change C.gates.length ≤ D.gates.length at hmin
  change D.gates.length + 1 ≤ C.gates.length at hsize
  omega

end PEqualNP.Outside.L_meta_5012.Alias

namespace PEqualNP.Outside.L_meta_5012.CriticalEdge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

lemma run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  exact PEqualNP.Outside.L_meta_5012.Structural.foldl_length gs x

lemma getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]


lemma run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

lemma run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  exact PEqualNP.Outside.L_meta_5012.Structural.foldl_getD_lt gs x i hi

lemma run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  intro j hj
  exact PEqualNP.Outside.L_meta_5012.Structural.foldl_getD_gate gs x j hj

def u (n : ℕ) (A : ℕ → Bool) (a b : ℕ → ℕ) (Del : Finset ℕ) (L : ℕ → List ℕ) (x : List Bool)
    (w : ℕ) : Bool :=
  if w < n then x.getD w false
  else if w - n ∈ Del then false
  else if A (w - n) = true then
    ((if _h : a (w - n) < w then u n A a b Del L x (a (w - n)) else false) ||
      (L (w - n)).any (fun t => x.getD t false)) &&
    (if _h : b (w - n) < w then u n A a b Del L x (b (w - n)) else false)
  else
    (if _h : a (w - n) < w then u n A a b Del L x (a (w - n)) else false) ||
    (if _h : b (w - n) < w then u n A a b Del L x (b (w - n)) else false)
termination_by w

section Evaluation1
variable {n : ℕ} {A : ℕ → Bool} {a b : ℕ → ℕ} {Del : Finset ℕ} {L : ℕ → List ℕ} {x : List Bool}

lemma u_in {w : ℕ} (h : w < n) : u n A a b Del L x w = x.getD w false := by
  rw [u, if_pos h]

lemma u_del {j : ℕ} (h : j ∈ Del) : u n A a b Del L x (n + j) = false := by
  rw [u, if_neg (by omega), Nat.add_sub_cancel_left, if_pos h]

lemma u_and {j : ℕ} (h : j ∉ Del) (hA : A j = true) (ha : a j < n + j) (hb : b j < n + j) :
    u n A a b Del L x (n + j) = ((u n A a b Del L x (a j) ||
      (L j).any (fun t => x.getD t false)) && u n A a b Del L x (b j)) := by
  rw [u, if_neg (by omega), Nat.add_sub_cancel_left, if_neg h, if_pos hA, dif_pos ha, dif_pos hb]

lemma u_or {j : ℕ} (h : j ∉ Del) (hA : A j = false) (ha : a j < n + j) (hb : b j < n + j) :
    u n A a b Del L x (n + j) = (u n A a b Del L x (a j) || u n A a b Del L x (b j)) := by
  rw [u, if_neg (by omega), Nat.add_sub_cancel_left, if_neg h, if_neg (by simp [hA]), dif_pos ha,
    dif_pos hb]
end Evaluation1

def Ok (n : ℕ) (gs : List Gate) : Prop :=
  ∀ j (hj : j < gs.length), ∃ o s t, gs[j] = ⟨o, [s, t]⟩ ∧ (o = GateOp.and ∨ o = GateOp.or) ∧
    s < n + j ∧ t < n + j

lemma ok_snoc {n : ℕ} {gs : List Gate} (h : Ok n gs) {o : GateOp} {s t : ℕ}
    (ho : o = GateOp.and ∨ o = GateOp.or) (hs : s < n + gs.length) (ht : t < n + gs.length) :
    Ok n (gs ++ [⟨o, [s, t]⟩]) := by
  intro j hj
  by_cases hlt : j < gs.length
  · rw [List.getElem_append_left hlt]; exact h j hlt
  · have : j = gs.length := by simp at hj; omega
    subst this
    exact ⟨o, s, t, by simp, ho, hs, ht⟩

open Classical in
noncomputable def dc (n : ℕ) (F : (Fin n → Bool) → Bool) (gs : List Gate) : ℕ :=
  ((Finset.range gs.length).filter fun i => (gs.getD i ⟨GateOp.or, []⟩).op = GateOp.and ∧
    ∃ x : Fin n → Bool, (run gs (List.ofFn x)).getD (n + i) false = true ∧ F x = false).card

open Classical in
lemma dc_snoc (n : ℕ) (F : (Fin n → Bool) → Bool) (gs : List Gate) (g : Gate) :
    dc n F (gs ++ [g]) ≤ dc n F gs + if g.op = GateOp.and ∧
      ∃ x : Fin n → Bool, (run (gs ++ [g]) (List.ofFn x)).getD (n + gs.length) false = true ∧
        F x = false then 1 else 0 := by
  unfold dc
  rw [List.length_append, List.length_singleton, Finset.range_add_one, Finset.filter_insert]
  have e : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
    simp [List.getD_eq_getElem?_getD]
  rw [e]
  have h1 : ((Finset.range gs.length).filter fun i =>
      ((gs ++ [g]).getD i ⟨GateOp.or, []⟩).op = GateOp.and ∧ ∃ x : Fin n → Bool,
        (run (gs ++ [g]) (List.ofFn x)).getD (n + i) false = true ∧ F x = false) =
      (Finset.range gs.length).filter fun i =>
      (gs.getD i ⟨GateOp.or, []⟩).op = GateOp.and ∧ ∃ x : Fin n → Bool,
        (run gs (List.ofFn x)).getD (n + i) false = true ∧ F x = false := by
    refine Finset.filter_congr fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    rw [getD_ltz _ _ _ _ hi']
    refine and_congr_right fun _ => exists_congr fun x => ?_
    rw [run_prefix gs [g] _ _ (by simp; omega)]
  rw [h1]
  split_ifs with h
  · exact (Finset.card_insert_le _ _)
  · simp

def ov (gs : List Gate) (x : List Bool) (o : Option ℕ) : Bool :=
  match o with
  | none => false
  | some w => (run gs x).getD w false

lemma ov_ext (gs hs : List Gate) (x : List Bool) (o : Option ℕ)
    (h : ∀ w, o = some w → w < x.length + gs.length) : ov (gs ++ hs) x o = ov gs x o := by
  cases o with
  | none => rfl
  | some w => exact run_prefix gs hs x w (h w rfl)

lemma ov_new (gs : List Gate) (n : ℕ) (x : List Bool) (hx : x.length = n) (o : GateOp) (s t : ℕ)
    (hs : s < n + gs.length) (ht : t < n + gs.length) :
    ov (gs ++ [⟨o, [s, t]⟩]) x (some (n + gs.length)) =
      o.eval [(run gs x).getD s false, (run gs x).getD t false] := by
  unfold ov
  simp only
  rw [run_snoc]
  have : n + gs.length = (run gs x).length := by rw [run_length, hx]
  rw [this, getD_at]
  rfl

lemma chain (n : ℕ) (F : (Fin n → Bool) → Bool) : ∀ (l : List ℕ), (∀ t ∈ l, t < n) →
    ∀ (gs : List Gate), Ok n gs → ∀ o : Option ℕ, (∀ w, o = some w → w < n + gs.length) →
    ∃ (hs : List Gate) (o' : Option ℕ), Ok n (gs ++ hs) ∧ hs.length ≤ l.length ∧
      dc n F (gs ++ hs) ≤ dc n F gs ∧ (∀ w, o' = some w → w < n + (gs ++ hs).length) ∧
      ∀ x : Fin n → Bool, ov (gs ++ hs) (List.ofFn x) o' =
        (ov gs (List.ofFn x) o || l.any (fun t => (List.ofFn x).getD t false)) := by
  intro l
  induction l with
  | nil =>
    intro _ gs hgs o ho
    exact ⟨[], o, by simpa using hgs, by simp, by simp, by simpa using ho, by simp⟩
  | cons t l ih =>
    intro hl gs hgs o ho
    have ht : t < n := hl t (by simp)
    have hl' : ∀ t ∈ l, t < n := fun s hs => hl s (by simp [hs])
    cases o with
    | none =>
      obtain ⟨hs, o', h1, h2, h3, h4, h5⟩ := ih hl' gs hgs (some t) (by
        intro w hw; cases hw; omega)
      refine ⟨hs, o', h1, by simp; omega, h3, h4, fun x => ?_⟩
      rw [h5 x]
      have : ov gs (List.ofFn x) (some t) = (List.ofFn x).getD t false :=
        run_input _ _ _ (by simpa using ht)
      rw [this]; simp [ov]
    | some w =>
      have hw := ho w rfl
      obtain ⟨hs, o', h1, h2, h3, h4, h5⟩ := ih hl' (gs ++ [⟨GateOp.or, [w, t]⟩])
        (ok_snoc hgs (Or.inr rfl) hw (by omega)) (some (n + gs.length)) (by
          intro w hw; cases hw; simp)
      refine ⟨⟨GateOp.or, [w, t]⟩ :: hs, o', by simpa using h1, by simp; omega, ?_,
        by simpa using h4, fun x => ?_⟩
      · have := dc_snoc n F gs ⟨GateOp.or, [w, t]⟩
        rw [if_neg (by simp)] at this
        have e : gs ++ ⟨GateOp.or, [w, t]⟩ :: hs = gs ++ [⟨GateOp.or, [w, t]⟩] ++ hs := by simp
        rw [e]; omega
      · have e : gs ++ ⟨GateOp.or, [w, t]⟩ :: hs = gs ++ [⟨GateOp.or, [w, t]⟩] ++ hs := by simp
        rw [e, h5 x, ov_new gs n _ (by simp) _ _ _ hw (by omega)]
        rw [run_input gs (List.ofFn x) t (by simpa using ht)]
        simp [ov, GateOp.eval, Bool.or_assoc]

open Classical in
lemma build (n : ℕ) (A : ℕ → Bool) (a b : ℕ → ℕ) (Del R : Finset ℕ) (L : ℕ → List ℕ)
    (F : (Fin n → Bool) → Bool) (hL : ∀ j, ∀ t ∈ L j, t < n)
    (hR : ∀ j ∈ R, A j = false ∧ j ∉ Del ∧ ∃ d ∈ Del, d < j ∧ (a j = n + d ∨ b j = n + d)) :
    ∀ p, (∀ j < p, a j < n + j ∧ b j < n + j) →
    ∃ (gs : List Gate) (m : ℕ → Option ℕ), Ok n gs ∧
      (∀ w < n + p, (∀ w', m w = some w' → w' < n + gs.length) ∧
        ∀ x : Fin n → Bool, ov gs (List.ofFn x) (m w) = u n A a b Del L (List.ofFn x) w) ∧
      (∀ d ∈ Del, d < p → m (n + d) = none) ∧
      gs.length + ((Finset.range p).filter (· ∈ Del)).card +
        ((Finset.range p).filter (· ∈ R)).card ≤ p + ∑ j ∈ Finset.range p, (L j).length ∧
      dc n F gs ≤ ((Finset.range p).filter fun j => A j = true ∧ j ∉ Del ∧
        ∃ x : Fin n → Bool, u n A a b Del L (List.ofFn x) (n + j) = true ∧ F x = false).card := by
  intro p
  induction p with
  | zero =>
    intro _
    refine ⟨[], fun w => some w, by intro j hj; simp at hj, ?_, by simp, by simp, by simp [dc]⟩
    intro w hw
    refine ⟨by intro w' h; cases h; simpa using hw, fun x => ?_⟩
    rw [u_in (by omega)]; rfl
  | succ p ih =>
    intro hab
    obtain ⟨gs, m, hok, hm, hd, hc, hj⟩ := ih fun j hj => hab j (by omega)
    obtain ⟨hap, hbp⟩ := hab p (by omega)
    suffices hh : ∃ (hs : List Gate) (o : Option ℕ), Ok n (gs ++ hs) ∧
        (∀ w, o = some w → w < n + (gs ++ hs).length) ∧ (p ∈ Del → o = none) ∧
        (∀ x : Fin n → Bool, ov (gs ++ hs) (List.ofFn x) o =
          u n A a b Del L (List.ofFn x) (n + p)) ∧
        hs.length + (if p ∈ Del then 1 else 0) + (if p ∈ R then 1 else 0) ≤ 1 + (L p).length ∧
        dc n F (gs ++ hs) ≤ dc n F gs + if A p = true ∧ p ∉ Del ∧ ∃ x : Fin n → Bool,
          u n A a b Del L (List.ofFn x) (n + p) = true ∧ F x = false then 1 else 0 by
      obtain ⟨hs, o, h1, h2, h3, h4, h5, h6⟩ := hh
      refine ⟨gs ++ hs, Function.update m (n + p) o, h1, ?_, ?_, ?_, ?_⟩
      · intro w hw
        by_cases hwp : w = n + p
        · subst hwp; rw [Function.update_self]; exact ⟨h2, h4⟩
        · rw [Function.update_of_ne hwp]
          obtain ⟨q1, q2⟩ := hm w (by omega)
          refine ⟨fun w' hw' => by have := q1 w' hw'; simp; omega, fun x => ?_⟩
          rw [ov_ext gs hs _ _ (by simpa using q1), q2]
      · intro d hdd hdp
        by_cases hdp' : d = p
        · subst hdp'; rw [Function.update_self]; exact h3 hdd
        · rw [Function.update_of_ne (by omega)]; exact hd d hdd (by omega)
      · rw [Finset.range_add_one, Finset.filter_insert, Finset.filter_insert,
          Finset.sum_insert (by simp), List.length_append]
        split_ifs at h5 ⊢ with q1 q2 q2 <;>
          (try rw [Finset.card_insert_of_notMem (by simp)]) <;>
          (try rw [Finset.card_insert_of_notMem (by simp)]) <;> omega
      · rw [Finset.range_add_one, Finset.filter_insert]
        split_ifs at h6 ⊢ with q1
        · rw [Finset.card_insert_of_notMem (by simp)]; omega
        · omega
    by_cases hpd : p ∈ Del
    · have hpR : p ∉ R := fun h => (hR p h).2.1 hpd
      refine ⟨[], none, by simpa using hok, by simp, fun _ => rfl, fun x => ?_, ?_, by simp⟩
      · rw [u_del hpd]; rfl
      · rw [if_pos hpd, if_neg hpR]; simp
    obtain ⟨a1, a2⟩ := hm (a p) hap
    obtain ⟨b1, b2⟩ := hm (b p) hbp
    cases hA : A p with
    | false =>
      have hu := fun x : Fin n → Bool => u_or (L := L) (x := List.ofFn x) hpd hA hap hbp
      rcases ha0 : m (a p) with _ | s
      · refine ⟨[], m (b p), by simpa using hok, by simpa using b1, fun h => absurd h hpd,
          fun x => ?_, ?_, by simp⟩
        · rw [hu x, ← a2 x, ← b2 x, ha0]; simp [ov]
        · rw [if_neg hpd]; split_ifs <;> simp
      rcases hb0 : m (b p) with _ | t
      · refine ⟨[], m (a p), by simpa using hok, by simpa using a1, fun h => absurd h hpd,
          fun x => ?_, ?_, by simp⟩
        · rw [hu x, ← a2 x, ← b2 x, hb0]; simp [ov]
        · rw [if_neg hpd]; split_ifs <;> simp
      have hpR : p ∉ R := by
        intro h
        obtain ⟨_, _, d, hd1, hd2, hd3⟩ := hR p h
        have := hd d hd1 hd2
        rcases hd3 with h | h
        · rw [h, this] at ha0; cases ha0
        · rw [h, this] at hb0; cases hb0
      have hs := a1 s ha0
      have ht := b1 t hb0
      refine ⟨[⟨GateOp.or, [s, t]⟩], some (n + gs.length), ok_snoc hok (Or.inr rfl) hs ht,
        by intro w hw; cases hw; simp, fun h => absurd h hpd, fun x => ?_, ?_, ?_⟩
      · rw [ov_new gs n _ (by simp) _ _ _ hs ht, hu x, ← a2 x, ← b2 x, ha0, hb0]
        simp [ov, GateOp.eval]
      · rw [if_neg hpd, if_neg hpR]; simp
      · have := dc_snoc n F gs ⟨GateOp.or, [s, t]⟩
        rw [if_neg (by simp)] at this
        omega
    | true =>
      have hu := fun x : Fin n → Bool => u_and (L := L) (x := List.ofFn x) hpd hA hap hbp
      have hpR : p ∉ R := fun h => by rw [(hR p h).1] at hA; cases hA
      obtain ⟨hs, o', c1, c2, c3, c4, c5⟩ := chain n F (L p) (hL p) gs hok (m (a p)) a1
      rcases ho : o' with _ | s
      · refine ⟨hs, none, c1, by simp, fun _ => rfl, fun x => ?_, ?_, by omega⟩
        · have := c5 x
          rw [ho, a2 x] at this
          rw [hu x, ← this]; simp [ov]
        · rw [if_neg hpd, if_neg hpR]; omega
      rcases hb0 : m (b p) with _ | t
      · refine ⟨hs, none, c1, by simp, fun _ => rfl, fun x => ?_, ?_, by omega⟩
        · have := b2 x
          rw [hb0] at this
          rw [hu x, ← this]; simp [ov]
        · rw [if_neg hpd, if_neg hpR]; omega
      have hs' := c4 s ho
      have ht : t < n + (gs ++ hs).length := by have := b1 t hb0; simp; omega
      have hval : ∀ x : Fin n → Bool, ov (gs ++ hs ++ [⟨GateOp.and, [s, t]⟩]) (List.ofFn x)
          (some (n + (gs ++ hs).length)) = u n A a b Del L (List.ofFn x) (n + p) := by
        intro x
        rw [ov_new (gs ++ hs) n _ (by simp) _ _ _ hs' ht, hu x, ← a2 x, ← b2 x, ← c5 x, ho, hb0,
          ← ov_ext gs hs (List.ofFn x) (some t) (by intro w hw; cases hw; simpa using b1 t hb0)]
        simp [ov, GateOp.eval]
      refine ⟨hs ++ [⟨GateOp.and, [s, t]⟩], some (n + (gs ++ hs).length), ?_, ?_,
        fun h => absurd h hpd, fun x => ?_, ?_, ?_⟩
      · rw [← List.append_assoc]; exact ok_snoc c1 (Or.inl rfl) hs' ht
      · intro w hw; cases hw; simp
      · rw [← List.append_assoc]; exact hval x
      · rw [if_neg hpd, if_neg hpR]; simp; omega
      · rw [← List.append_assoc]
        have := dc_snoc n F (gs ++ hs) ⟨GateOp.and, [s, t]⟩
        have e : ((⟨GateOp.and, [s, t]⟩ : Gate).op = GateOp.and ∧ ∃ x : Fin n → Bool,
            (run (gs ++ hs ++ [⟨GateOp.and, [s, t]⟩]) (List.ofFn x)).getD
              (n + (gs ++ hs).length) false = true ∧ F x = false) ↔
            (true = true ∧ p ∉ Del ∧ ∃ x : Fin n → Bool,
              u n A a b Del L (List.ofFn x) (n + p) = true ∧ F x = false) := by
          refine ⟨fun h => ⟨rfl, hpd, ?_⟩, fun h => ⟨rfl, ?_⟩⟩
          · obtain ⟨x, h1, h2⟩ := h.2
            exact ⟨x, by rw [← hval x]; exact h1, h2⟩
          · obtain ⟨x, h1, h2⟩ := h.2.2
            exact ⟨x, by rw [← hval x] at h1; exact h1, h2⟩
        rw [if_congr e rfl rfl] at this
        omega

lemma gf {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ p q, G.Adj p q ∧ x p = true ∧ x q = true := by
  simp [graphFun]

lemma gD {n : ℕ} (x : Fin n → Bool) (p : Fin n) : (List.ofFn x).getD p.val false = x p := by
  simp [List.getD_eq_getElem?_getD]

lemma u_mono {n N : ℕ} {A : ℕ → Bool} {a b : ℕ → ℕ} {Del : Finset ℕ} {L : ℕ → List ℕ}
    (hab : ∀ j < N, a j < n + j ∧ b j < n + j) (x y : List Bool)
    (h : ∀ t, x.getD t false = true → y.getD t false = true) :
    ∀ w < n + N, u n A a b Del L x w = true → u n A a b Del L y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hx
    by_cases h9 : w < n
    · rw [u_in h9] at hx ⊢; exact h _ hx
    obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
    obtain ⟨ha, hb⟩ := hab j (by omega)
    by_cases hd : j ∈ Del
    · rw [u_del hd] at hx; cases hx
    have ia := ih (a j) ha (by omega)
    have ib := ih (b j) hb (by omega)
    cases hA : A j with
    | true =>
      rw [u_and hd hA ha hb, Bool.and_eq_true, Bool.or_eq_true] at hx ⊢
      refine ⟨?_, ib hx.2⟩
      rcases hx.1 with h1 | h1
      · exact Or.inl (ia h1)
      · right
        rw [List.any_eq_true] at h1 ⊢
        obtain ⟨t, h2, h3⟩ := h1
        exact ⟨t, h2, h t h3⟩
    | false =>
      rw [u_or hd hA ha hb, Bool.or_eq_true] at hx ⊢
      rcases hx with h1 | h1
      · exact Or.inl (ia h1)
      · exact Or.inr (ib h1)

lemma gate2 {n : ℕ} {C : Circuit} (h : TopForm.IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
    C.gates[j] = gateAt C j ∧ (gateAt C j).inputs = [TopForm.opnd C j 0, TopForm.opnd C j 1] ∧
    TopForm.opnd C j 0 < n + j ∧ TopForm.opnd C j 1 < n + j ∧
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) := by
  have e : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
  have hm : gateAt C j ∈ C.gates := by rw [e]; exact List.getElem_mem hj
  have hl := h.2.2 _ hm
  obtain ⟨s, t, hst⟩ := List.length_eq_two.1 hl
  have hb := h.2.1 j hj
  rw [hst] at hb
  have e0 : TopForm.opnd C j 0 = s := by unfold TopForm.opnd; rw [hst]; rfl
  have e1 : TopForm.opnd C j 1 = t := by unfold TopForm.opnd; rw [hst]; rfl
  refine ⟨e.symm, by rw [hst, e0, e1], by rw [e0]; exact hb s (by simp),
    by rw [e1]; exact hb t (by simp), h.1 _ hm⟩



lemma gDv {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (List.ofFn x).getD w false = x ⟨w, hw⟩ := gD x ⟨w, hw⟩
lemma ok_ao {n : ℕ} {gs : List Gate} {w : ℕ} (hok : Ok n gs) : TopForm.IsAO2 n ⟨gs, w⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hq
    obtain ⟨o', s', t', h1, h2, _⟩ := hok i hi
    rw [h1]; exact h2
  · intro j hj i hi
    obtain ⟨o', s', t', h1, h2, h3, h4⟩ := hok j hj
    have e1 : gateAt ⟨gs, w⟩ j = gs[j] := List.getD_eq_getElem _ _ hj
    rw [e1, h1] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> assumption
  · intro q hq
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hq
    obtain ⟨o', s', t', h1, h2, _⟩ := hok i hi
    rw [h1]; rfl

open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

def isAnd (C : Circuit) (j : ℕ) : Bool :=
  match (gateAt C j).op with
  | .and => true
  | _ => false

def val (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (run C.gates (List.ofFn x)).getD w false

def cutVal (n : ℕ) (C : Circuit) (Del : Finset ℕ) (x : Fin n → Bool) (w : ℕ) : Bool :=
  u n (isAnd C) (fun j => opnd C j 0) (fun j => opnd C j 1) Del (fun _ => []) (List.ofFn x) w

lemma val_in {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val n C x w = (List.ofFn x).getD w false := by
  exact run_input C.gates (List.ofFn x) w (by simpa using hw)

lemma val_rec {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (x : Fin n → Bool) (j : ℕ)
    (hj : j < C.gates.length) :
    val n C x (n + j) = if isAnd C j = true then
      val n C x (opnd C j 0) && val n C x (opnd C j 1)
    else val n C x (opnd C j 0) || val n C x (opnd C j 1) := by
  obtain ⟨heq, hin, ha, hb, hop⟩ := gate2 hC hj
  have hr := run_gate C.gates (List.ofFn x) j hj
  rw [List.length_ofFn, heq, hin] at hr
  rcases hop with hop | hop
  · simp only [val, hr, hop, List.map_cons, List.map_nil, if_pos ha, if_pos hb]
    simp [isAnd, hop, GateOp.eval]
  · simp only [val, hr, hop, List.map_cons, List.map_nil, if_pos ha, if_pos hb]
    simp [isAnd, hop, GateOp.eval]

lemma cutVal_le {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (Del : Finset ℕ)
    (x : Fin n → Bool) :
    ∀ w < n + C.gates.length, cutVal n C Del x w = true → val n C x w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw h
    by_cases hin : w < n
    · simpa only [cutVal, u_in hin, val_in C x w hin] using h
    obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
    have hj : j < C.gates.length := by omega
    obtain ⟨_, _, ha, hb, _⟩ := gate2 hC hj
    by_cases hd : j ∈ Del
    · simp only [cutVal, u_del hd] at h
      cases h
    rw [val_rec C hC x j hj]
    cases hA : isAnd C j with
    | false =>
      simp only [hA, Bool.false_eq_true, ↓reduceIte]
      rw [cutVal, u_or hd hA ha hb, Bool.or_eq_true] at h
      rcases h with h | h
      · rw [Bool.or_eq_true]; exact Or.inl (ih _ ha (by omega) h)
      · rw [Bool.or_eq_true]; exact Or.inr (ih _ hb (by omega) h)
    | true =>
      simp only [hA, ↓reduceIte]
      rw [cutVal, u_and hd hA ha hb] at h
      simp only [List.any_nil, Bool.or_false, Bool.and_eq_true] at h
      rw [Bool.and_eq_true]; exact ⟨ih _ ha (by omega) h.1, ih _ hb (by omega) h.2⟩

lemma cutVal_eq_of_zero {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (j : ℕ)
    (x : Fin n → Bool) (hz : val n C x (n + j) = false) :
    ∀ w < n + C.gates.length, cutVal n C {j} x w = val n C x w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hin : w < n
    · simp only [cutVal, u_in hin, val_in C x w hin]
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have hk : k < C.gates.length := by omega
    obtain ⟨_, _, ha, hb, _⟩ := gate2 hC hk
    by_cases hd : k ∈ ({j} : Finset ℕ)
    · have hkj : k = j := Finset.mem_singleton.mp hd
      subst k
      rw [cutVal, u_del (Finset.mem_singleton_self j), hz]
    rw [val_rec C hC x k hk]
    have ia := ih (opnd C k 0) ha (by omega)
    have ib := ih (opnd C k 1) hb (by omega)
    cases hA : isAnd C k with
    | false =>
      simp only [hA, Bool.false_eq_true, ↓reduceIte]
      rw [cutVal, u_or hd hA ha hb]
      exact congrArg₂ Bool.or ia ib
    | true =>
      simp only [hA, ↓reduceIte]
      rw [cutVal, u_and hd hA ha hb]
      simp only [List.any_nil, Bool.or_false]
      exact congrArg₂ Bool.and ia ib

lemma cutVal_mono {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (Del : Finset ℕ)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true)
    (w : ℕ) (hw : w < n + C.gates.length) :
    cutVal n C Del x w = true → cutVal n C Del y w = true := by
  have hab : ∀ j < C.gates.length, opnd C j 0 < n + j ∧ opnd C j 1 < n + j := by
    intro j hj
    exact ⟨(gate2 hC hj).2.2.1, (gate2 hC hj).2.2.2.1⟩
  have hget : ∀ t, (List.ofFn x).getD t false = true → (List.ofFn y).getD t false = true := by
    intro t ht
    by_cases ht' : t < n
    · rw [gDv y t ht']
      exact hxy ⟨t, ht'⟩ (by simpa only [gDv x t ht'] using ht)
    · have : (List.ofFn x).getD t false = false :=
        List.getD_eq_default _ _ (by simp; omega)
      rw [this] at ht
      cases ht
  exact u_mono hab (List.ofFn x) (List.ofFn y) hget w hw

lemma val_out {n : ℕ} (C : Circuit) (x : Fin n → Bool) :
    val n C x C.output = circuitFun n C x := rfl

lemma output_lt {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hF : circuitFun n C = graphFun G ∅) (hE : G.edgeFinset.Nonempty) :
    C.output < n + C.gates.length := by
  have hE' : ∃ p q, G.Adj p q := by
    obtain ⟨e, he⟩ := hE
    induction e using Sym2.ind with
    | _ p q => exact ⟨p, q, by simpa using he⟩
  obtain ⟨p, q, hpq⟩ := hE'
  have htrue : val n C (fun _ => true) C.output = true := by
    rw [val_out, hF]
    exact (gf G _).mpr ⟨p, q, hpq, rfl, rfl⟩
  by_contra h
  have hfalse : val n C (fun _ => true) C.output = false :=
    List.getD_eq_default _ _ (by rw [run_length, List.length_ofFn]; omega)
  rw [hfalse] at htrue
  cases htrue

lemma compile_cut {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (j : ℕ)
    (hj : j < C.gates.length) (hout : C.output < n + C.gates.length) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size < C.size ∧
      ∀ x : Fin n → Bool, circuitFun n D x = cutVal n C {j} x C.output := by
  obtain ⟨gs, m, hok, hm, _, hsize, _⟩ := build n (isAnd C)
    (fun k => opnd C k 0) (fun k => opnd C k 1) {j} ∅ (fun _ => [])
    (fun _ => false) (by simp) (by simp) C.gates.length
    (fun k hk => ⟨(gate2 hC hk).2.2.1, (gate2 hC hk).2.2.2.1⟩)
  have hcard : ((Finset.range C.gates.length).filter (· ∈ ({j} : Finset ℕ))).card = 1 := by
    have : (Finset.range C.gates.length).filter (· ∈ ({j} : Finset ℕ)) = {j} := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      omega
    rw [this]
    simp
  simp only [hcard, Finset.notMem_empty, Finset.filter_false, Finset.card_empty,
    Nat.add_zero, List.length_nil, Finset.sum_const_zero] at hsize
  rcases hm C.output hout with ⟨hbound, heq⟩
  cases ho : m C.output with
  | none =>
    refine ⟨⟨gs, n + gs.length⟩, ok_ao hok, by simp only [Circuit.size]; omega, ?_⟩
    intro x
    have hfalse : (run gs (List.ofFn x)).getD (n + gs.length) false = false :=
      List.getD_eq_default _ _ (by rw [run_length, List.length_ofFn])
    change (run gs (List.ofFn x)).getD (n + gs.length) false = _
    rw [hfalse]
    have hh := heq x
    simpa only [ho, ov, cutVal] using hh
  | some w =>
    refine ⟨⟨gs, w⟩, ok_ao hok, by simp only [Circuit.size]; omega, ?_⟩
    intro x
    change (run gs (List.ofFn x)).getD w false = _
    have hh := heq x
    simpa only [ho, ov, cutVal] using hh

lemma least_gate_critical {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hE : G.edgeFinset.Nonempty) (j : ℕ)
    (hj : j < C.gates.length) :
    ∃ p q : Fin n, G.Adj p q ∧ cutVal n C {j} (pairInput p q) C.output = false := by
  have hout := output_lt G C hL.2.1 hE
  by_contra h
  push Not at h
  have hF : ∀ x : Fin n → Bool, cutVal n C {j} x C.output = graphFun G ∅ x := by
    intro x
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro hx
      have hval := cutVal_le C hL.1 {j} x C.output hout hx
      rwa [val_out, hL.2.1] at hval
    · intro hx
      obtain ⟨p, q, hpq, hp, hq⟩ := (gf G x).mp hx
      have hedge : cutVal n C {j} (pairInput p q) C.output = true := by
        cases ht : cutVal n C {j} (pairInput p q) C.output
        · exact (h p q hpq ht).elim
        · rfl
      apply cutVal_mono C hL.1 {j} (pairInput p q) x ?_ C.output hout hedge
      intro i hi
      have : i = p ∨ i = q := by simpa [pairInput] using hi
      rcases this with rfl | rfl <;> assumption
  obtain ⟨D, hAO, hsize, heq⟩ := compile_cut C hL.1 j hj hout
  have hDF : circuitFun n D = graphFun G ∅ := funext fun x => (heq x).trans (hF x)
  have hmin := hL.2.2 D hAO hDF
  omega



lemma cutVal_eq_set {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (j : ℕ)
    (x : Fin n → Bool) :
    ∀ w < n + C.gates.length,
      cutVal n C {j} x w =
        (run (C.gates.set j ⟨GateOp.or, []⟩) (List.ofFn x)).getD w false := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hin : w < n
    · rw [cutVal, u_in hin, run_input _ _ w (by simpa using hin)]
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have hk : k < C.gates.length := by omega
    have hk' : k < (C.gates.set j ⟨GateOp.or, []⟩).length := by simpa using hk
    have hrec := run_gate (C.gates.set j ⟨GateOp.or, []⟩) (List.ofFn x) k hk'
    rw [List.length_ofFn] at hrec
    by_cases hkj : k = j
    · subst k
      rw [cutVal, u_del (Finset.mem_singleton_self j), hrec]
      simp [GateOp.eval]
    have hnot : k ∉ ({j} : Finset ℕ) := by simpa using hkj
    have hgt : (C.gates.set j ⟨GateOp.or, []⟩)[k] = C.gates[k] := by
      simp [List.getElem_set, hkj, Ne.symm hkj]
    obtain ⟨heq, hinp, ha, hb, hop⟩ := gate2 hC hk
    rw [hgt, heq, hinp] at hrec
    simp only [List.map_cons, List.map_nil, if_pos ha, if_pos hb] at hrec
    have ia := ih (opnd C k 0) ha (by omega)
    have ib := ih (opnd C k 1) hb (by omega)
    rcases hop with hop | hop
    · have hA : isAnd C k = true := by simp [isAnd, hop]
      rw [cutVal, u_and hnot hA ha hb, hrec, hop]
      simp only [List.any_nil, Bool.or_false, GateOp.eval, List.all_cons, List.all_nil,
        Bool.and_true, id_eq]
      exact congrArg₂ Bool.and ia ib
    · have hA : isAnd C k = false := by simp [isAnd, hop]
      rw [cutVal, u_or hnot hA ha hb, hrec, hop]
      simp only [GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq]
      exact congrArg₂ Bool.or ia ib

lemma least_gate_critical_edge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hE : G.edgeFinset.Nonempty) (j : ℕ)
    (hj : j < C.gates.length) :
    ∃ p q : Fin n, G.Adj p q ∧ gateVal n C j (pairInput p q) = true ∧
      circuitFun n ⟨C.gates.set j ⟨GateOp.or, []⟩, C.output⟩ (pairInput p q) = false := by
  obtain ⟨p, q, hpq, hcut⟩ := least_gate_critical G C hL hE j hj
  have hkill : circuitFun n ⟨C.gates.set j ⟨GateOp.or, []⟩, C.output⟩ (pairInput p q) = false := by
    change (run (C.gates.set j ⟨GateOp.or, []⟩) (List.ofFn (pairInput p q))).getD C.output false = false
    rw [← cutVal_eq_set C hL.1 j (pairInput p q) C.output (output_lt G C hL.2.1 hE)]
    exact hcut
  refine ⟨p, q, hpq, ?_, hkill⟩
  cases hz : gateVal n C j (pairInput p q) with
  | true => rfl
  | false =>
    have heq := cutVal_eq_of_zero C hL.1 j (pairInput p q) hz C.output
      (output_lt G C hL.2.1 hE)
    rw [hcut, val_out, hL.2.1] at heq
    have hf : graphFun G ∅ (pairInput p q) = true :=
      (gf G _).mpr ⟨p, q, hpq, by simp [pairInput], by simp [pairInput]⟩
    rw [hf] at heq
    cases heq

lemma least_nonempty_of_gate {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (j : ℕ) (hj : j < C.gates.length) :
    G.edgeFinset.Nonempty := by
  by_contra hempty
  have hempty : G.edgeFinset = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
  have hadj : ∀ p q : Fin n, ¬ G.Adj p q := by
    intro p q hpq
    have he : s(p, q) ∈ G.edgeFinset := by simpa using hpq
    rw [hempty] at he
    exact Finset.notMem_empty _ he
  let D : Circuit := ⟨[], n⟩
  have hAO : IsAO2 n D := by
    simp [IsAO2, AndOrOnly, ReadsBack, D]
  have hF : circuitFun n D = graphFun G ∅ := by
    funext x
    have hfalse : graphFun G ∅ x = false := by
      cases hx : graphFun G ∅ x with
      | false => rfl
      | true =>
        obtain ⟨p, q, hpq, _, _⟩ := (gf G x).mp hx
        exact (hadj p q hpq).elim
    rw [hfalse]
    simp [circuitFun, D, Circuit.eval, Circuit.wires, List.getD_eq_getElem?_getD]
  have hsize := hL.2.2 D hAO hF
  simp only [Circuit.size, D, List.length_nil] at hsize
  omega

lemma least_gate_critical_edge_of_least {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hL : IsLeastAO G C) (j : ℕ)
    (hj : j < C.gates.length) :
    ∃ p q : Fin n, G.Adj p q ∧ gateVal n C j (pairInput p q) = true ∧
      circuitFun n ⟨C.gates.set j ⟨GateOp.or, []⟩, C.output⟩ (pairInput p q) = false := by
  exact least_gate_critical_edge G C hL (least_nonempty_of_gate G C hL j hj) j hj


end PEqualNP.Outside.L_meta_5012.CriticalEdge

namespace PEqualNP.Outside.L_meta_5012.GuardedAlias
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open PEqualNP.Outside.L_meta_5012.Structural PEqualNP.Outside.L_meta_5012.Tight
open PEqualNP.Outside.L_meta_5012.Patch PEqualNP.Outside.L_meta_5012.MixedOuter

lemma frontier_pure_value {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {x : Fin n → Bool} {f : ℕ → Bool} (hf : Frontier C x f)
    (w : ℕ) (hpure : PureWire n C w) : f w = setOr (orIn n C w) x := by
  apply Bool.eq_iff_iff.mpr
  rw [frontier_wire hAO hf]
  constructor
  · rintro (hr | ⟨j,hj,hand,hr,_⟩)
    · exact decide_eq_true hr
    · exact (hpure j hj hand hr).elim
  · intro hr
    exact Or.inl (of_decide_eq_true hr)

lemma and_eq_other {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {g : ℕ}
    (hg : g<C.gates.length) (hand : (gateAt C g).op=GateOp.and)
    (b d : Fin 2) (hbd : b≠d) (x : Fin n → Bool)
    (hb : val C (List.ofFn x) (opnd C g b)=true) :
    gateVal n C g x = val C (List.ofFn x) (opnd C g d) := by
  apply Bool.eq_iff_iff.mpr
  rw [andValOperands hAO hg hand]
  constructor
  · intro hv; exact hv d
  · intro hd i
    have hi : i=b ∨ i=d := by omega
    rcases hi with rfl | rfl <;> assumption

lemma upper_unchanged {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) (hT : TopForm G C) (g h : ℕ)
    (hJ : junk G C={g,h}) (hgh : g<h)
    (bg dg dh : Fin 2) (hgd : bg≠dg)
    (hpure : PureWire n C (opnd C h dh))
    (guard : ∀x : Fin n → Bool, val C (List.ofFn x) (opnd C h dh)=true →
      val C (List.ofFn x) (opnd C g bg)=true)
    (x : Fin n → Bool) :
    gateVal n (patch C g (aliasGate (opnd C g dg))) h x = gateVal n C h x := by
  have hgJ : g ∈ junk G C := by simp [hJ]
  have hhJ : h ∈ junk G C := by simp [hJ]
  have hgg := (junkData hgJ).1
  have hhh := (junkData hhJ).1
  have hgand := (junkData hgJ).2.1
  have hhand := (junkData hhJ).2.1
  let D := patch C g (aliasGate (opnd C g dg))
  have hDA : IsAO2 n D := alias_ao hAO hgg dg
  have hDlen : h<D.gates.length := by simpa [D,patch] using hhh
  have hDgate : gateAt D h=gateAt C h := gateAt_patch_ne C g h _ (by omega)
  have hDop : (gateAt D h).op=GateOp.and := by rw [hDgate]; exact hhand
  have hDoperand : ∀i : Fin 2, opnd D h i=opnd C h i := by intro i; simp only [opnd,hDgate]
  have hf := original_frontier C x
  have hfD := alias_frontier hgand (opnd C g dg) x
  have hQeq : val D (List.ofFn x) (opnd C h dh)=val C (List.ofFn x) (opnd C h dh) :=
    (frontier_pure_value hAO hfD _ hpure).trans (pure_wire_value C hAO _ hpure x).symm
  have hgEq (hq : val C (List.ofFn x) (opnd C h dh)=true) :
      val D (List.ofFn x) (n+g)=val C (List.ofFn x) (n+g) :=
    (alias_at hgg (opndBound hAO hgg dg) x).trans
      (and_eq_other hAO hgg hgand bg dg hgd x (guard x hq)).symm
  have hno (i : Fin 2) : ¬OrReaches n C (opnd C h i) h := by
    intro hr
    have hc := operandReachCone hAO hhh hr
    have := Semantics.inCone_lt n C h h hc
    omega
  have hoper (hq : val C (List.ofFn x) (opnd C h dh)=true) (i : Fin 2) :
      val D (List.ofFn x) (opnd C h i)=true ↔ val C (List.ofFn x) (opnd C h i)=true := by
    rw [frontier_operand G hAO hT g h hJ hhh hhand hfD i,
      frontier_operand G hAO hT g h hJ hhh hhand hf i]
    have he := hgEq hq
    dsimp only [D] at he
    simp only [hno i,false_and,or_false,he]
  apply Bool.eq_iff_iff.mpr
  rw [andValOperands hDA hDlen hDop, andValOperands hAO hhh hhand]
  simp only [hDoperand]
  constructor
  · intro hv i
    have hq := hQeq.symm.trans (hv dh)
    exact (hoper hq i).mp (hv i)
  · intro hv i
    exact (hoper (hv dh) i).mpr (hv i)

lemma top_unchanged {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) (hT : TopForm G C) (g h : ℕ)
    (hJ : junk G C={g,h}) (hgh : g<h)
    (bg dg dh : Fin 2) (hgd : bg≠dg)
    (hpure : PureWire n C (opnd C h dh))
    (guard : ∀x : Fin n → Bool, val C (List.ofFn x) (opnd C h dh)=true →
      val C (List.ofFn x) (opnd C g bg)=true)
    (noTop : ∀a ∈ tops G C, ∀b : Fin 2, ¬OrReaches n C (opnd C a b) g)
    {a : ℕ} (ha : a ∈ tops G C) (x : Fin n → Bool) :
    gateVal n (patch C g (aliasGate (opnd C g dg))) a x = gateVal n C a x := by
  have hgJ : g ∈ junk G C := by simp [hJ]
  have hgg := (junkData hgJ).1
  have hgand := (junkData hgJ).2.1
  have hav := topData ha
  have hne : g≠a := by rintro rfl; exact junkNotBelow hgJ hav.2.2
  let D := patch C g (aliasGate (opnd C g dg))
  have hDA : IsAO2 n D := alias_ao hAO hgg dg
  have hDlen : a<D.gates.length := by simpa [D,patch] using hav.1
  have hDgate : gateAt D a=gateAt C a := gateAt_patch_ne C g a _ hne
  have hDop : (gateAt D a).op=GateOp.and := by rw [hDgate]; exact hav.2.1
  have hDoperand : ∀i : Fin 2, opnd D a i=opnd C a i := by intro i; simp only [opnd,hDgate]
  have hf := original_frontier C x
  have hfD := alias_frontier hgand (opnd C g dg) x
  have hhEq := upper_unchanged G hAO hT g h hJ hgh bg dg dh hgd hpure guard x
  have hoper (i : Fin 2) :
      val D (List.ofFn x) (opnd C a i)=true ↔ val C (List.ofFn x) (opnd C a i)=true := by
    rw [frontier_operand G hAO hT g h hJ hav.1 hav.2.1 hfD i,
      frontier_operand G hAO hT g h hJ hav.1 hav.2.1 hf i]
    change val (patch C g (aliasGate (opnd C g dg))) (List.ofFn x) (n+h)=val C (List.ofFn x) (n+h) at hhEq
    simp only [noTop a ha i,false_and,false_or,hhEq]
  apply Bool.eq_iff_iff.mpr
  rw [andValOperands hDA hDlen hDop,andValOperands hAO hav.1 hav.2.1]
  simp only [hDoperand]
  exact forall_congr' hoper

lemma output_unchanged {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) (hT : TopForm G C) (g h : ℕ)
    (hJ : junk G C={g,h}) (hgh : g<h)
    (bg dg dh : Fin 2) (hgd : bg≠dg)
    (hpure : PureWire n C (opnd C h dh))
    (guard : ∀x : Fin n → Bool, val C (List.ofFn x) (opnd C h dh)=true →
      val C (List.ofFn x) (opnd C g bg)=true)
    (noTop : ∀a ∈ tops G C, ∀b : Fin 2, ¬OrReaches n C (opnd C a b) g) :
    circuitFun n (patch C g (aliasGate (opnd C g dg)))=graphFun G ∅ := by
  have hgJ : g ∈ junk G C := by simp [hJ]
  let D := patch C g (aliasGate (opnd C g dg))
  have hEq (a : ℕ) (ha : a ∈ tops G C) (x : Fin n → Bool) :
      gateVal n D a x=gateVal n C a x :=
    top_unchanged G hL.1 hT g h hJ hgh bg dg dh hgd hpure guard noTop ha x
  have hout : circuitFun n D=circuitFun n C := by
    funext x
    have hf := original_frontier C x
    have hfD := alias_frontier (junkData hgJ).2.1 (opnd C g dg) x
    apply Bool.eq_iff_iff.mpr
    constructor
    · exact output_transfer G hL hfD hf (fun a ha hv => (hEq a ha x).symm.trans hv)
    · exact output_transfer G hL hf hfD (fun a ha hv => (hEq a ha x).trans hv)
  exact hout.trans hL.2.1

lemma junk_exact {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) (hT : TopForm G C) (g h : ℕ)
    (hJ : junk G C={g,h}) (hgh : g<h)
    (bg dg dh : Fin 2) (hgd : bg≠dg)
    (hpure : PureWire n C (opnd C h dh))
    (guard : ∀x : Fin n → Bool, val C (List.ofFn x) (opnd C h dh)=true →
      val C (List.ofFn x) (opnd C g bg)=true)
    (noTop : ∀a ∈ tops G C, ∀b : Fin 2, ¬OrReaches n C (opnd C a b) g) :
    junk G (patch C g (aliasGate (opnd C g dg)))={h} := by
  classical
  have hgJ : g ∈ junk G C := by simp [hJ]
  have hhJ : h ∈ junk G C := by simp [hJ]
  have hgg := (junkData hgJ).1
  let D := patch C g (aliasGate (opnd C g dg))
  apply Finset.ext
  intro k
  constructor
  · intro hk
    have hkd := junkData hk
    have hklen : k<C.gates.length := by simpa [patch] using hkd.1
    have hne : g≠k := by
      rintro rfl
      rw [alias_gateAt hgg] at hkd
      cases hkd.2.1
    have hgate := gateAt_patch_ne C g k (aliasGate (opnd C g dg)) hne
    have hand : (gateAt C k).op=GateOp.and := by rw [hgate] at hkd; exact hkd.2.1
    have hnot : ¬BelowF G C k := by
      intro hbelow
      have htop : k ∈ tops G C := by
        simpa only [tops,gatesWhere,Finset.mem_filter,Finset.mem_range] using And.intro hklen (And.intro hand hbelow)
      obtain ⟨x,hx,hfalse⟩ := hkd.2.2
      have heq := top_unchanged G hAO hT g h hJ hgh bg dg dh hgd hpure guard noTop htop x
      have ht := hbelow x (heq.symm.trans hx)
      rw [hfalse] at ht
      cases ht
    have hdirty : ∃x : Fin n → Bool, gateVal n C k x=true ∧ graphFun G ∅ x=false := by
      by_contra hnone
      apply hnot
      intro x hx
      by_contra hfalse
      exact hnone ⟨x,hx,Bool.eq_false_iff.mpr hfalse⟩
    have hkJ : k ∈ junk G C := mem_junk.mpr ⟨hklen,hand,hklen,hdirty⟩
    simp only [hJ,Finset.mem_insert,Finset.mem_singleton] at hkJ
    rcases hkJ with he | he
    · exact (hne he.symm).elim
    · exact Finset.mem_singleton.mpr he
  · intro hk
    have he := Finset.mem_singleton.mp hk
    subst k
    obtain ⟨x,hx,hfalse⟩ := (junkData hhJ).2.2
    apply mem_junk.mpr
    refine ⟨by simpa [patch] using (junkData hhJ).1, ?_, ?_, x, ?_, hfalse⟩
    · rw [gateAt_patch_ne C g h _ (by omega)]
      exact (junkData hhJ).2.1
    · simpa [patch] using (junkData hhJ).1
    · exact (upper_unchanged G hAO hT g h hJ hgh bg dg dh hgd hpure guard x).trans hx

lemma no_guarded_lower_alias {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (noOne : ∀D : Circuit, IsLeastAO G D → (junk G D).card≠1)
    {C : Circuit} (hL : IsLeastAO G C) (hT : TopForm G C) (g h : ℕ)
    (hJ : junk G C={g,h}) (hgh : g<h)
    (bg dg dh : Fin 2) (hgd : bg≠dg)
    (hpure : PureWire n C (opnd C h dh))
    (guard : ∀x : Fin n → Bool, val C (List.ofFn x) (opnd C h dh)=true →
      val C (List.ofFn x) (opnd C g bg)=true)
    (noTop : ∀a ∈ tops G C, ∀b : Fin 2, ¬OrReaches n C (opnd C a b) g) : False := by
  have hgJ : g ∈ junk G C := by simp [hJ]
  let D := patch C g (aliasGate (opnd C g dg))
  have hDL : IsLeastAO G D := by
    refine ⟨alias_ao hL.1 (junkData hgJ).1 dg,
      output_unchanged G hL hT g h hJ hgh bg dg dh hgd hpure guard noTop, ?_⟩
    intro E hEAO hEF
    simpa [D,patch,Circuit.size] using hL.2.2 E hEAO hEF
  apply noOne D hDL
  rw [junk_exact G hL.1 hT g h hJ hgh bg dg dh hgd hpure guard noTop]
  exact Finset.card_singleton h

lemma no_raw_guarded_lower_alias {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (noOne : ∀D : Circuit, IsLeastAO G D → (junk G D).card≠1)
    {C : Circuit} (hL : IsLeastAO G C) (hT : TopForm G C) (g h : ℕ)
    (hJ : junk G C={g,h}) (hgh : g<h)
    (bg dg dh : Fin 2) (hgd : bg≠dg)
    (hpure : PureWire n C (opnd C h dh))
    (hsub : side (n := n) C h dh ⊆ side C g bg)
    (noTop : ∀a ∈ tops G C, ∀b : Fin 2, ¬OrReaches n C (opnd C a b) g) : False := by
  apply no_guarded_lower_alias G noOne hL hT g h hJ hgh bg dg dh hgd hpure ?_ noTop
  intro x hq
  rw [pure_wire_value C hL.1 _ hpure] at hq
  obtain ⟨u,hu,hxu⟩ := of_decide_eq_true hq
  exact reach_var_val x _ u (mem_orIn_reach u (hsub hu)) hxu

end PEqualNP.Outside.L_meta_5012.GuardedAlias



namespace PEqualNP.Outside.L_meta_5012.GuardedAlias
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open PEqualNP.Outside.L_meta_5012.MixedLowerClassification

lemma no_color_raw_containment {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (noOne : ∀D : Circuit, IsLeastAO G D → (junk G D).card≠1)
    {C : Circuit} (hL : IsLeastAO G C) (hT : TopForm G C) (g h : ℕ)
    (hJ : junk G C={g,h}) (hgh : g<h)
    (s : Fin n → Bool) (hcol : ∀u v, G.Adj u v → s u≠s v)
    (hgboth : ∀c, gateVal n C g (colorInput s c)=true)
    (c : Bool) (hhfalse : gateVal n C h (colorInput s c)=false)
    (bg bh dh : Fin 2) (hbd : bh≠dh) (hreach : OrReaches n C (opnd C h bh) g)
    (hsub : side (n := n) C h dh ⊆ side C g bg) : False := by
  obtain ⟨hpure,_,_,hhcolor⟩ := opposite_operand_classification G C hL.1 hT g h hJ s hgboth c hhfalse bh dh hbd hreach
  have noTop : ∀a ∈ tops G C, ∀b : Fin 2, ¬OrReaches n C (opnd C a b) g := by
    intro a ha b hr
    exact no_top_reaches_lower G C hL.1 hT g h hJ s hcol hgboth (!c) hhcolor ha b hr
  let dg : Fin 2 := ⟨1-bg.val,by omega⟩
  have hgd : bg≠dg := by
    intro he
    have hv := congrArg Fin.val he
    dsimp [dg] at hv
    omega
  exact no_raw_guarded_lower_alias G noOne hL hT g h hJ hgh bg dg dh hgd hpure hsub noTop

end PEqualNP.Outside.L_meta_5012.GuardedAlias

namespace PEqualNP.Outside.L_meta_5012.AliasClosures
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open PEqualNP.Outside.L_meta_5012.Structural PEqualNP.Outside.L_meta_5012.Tight
open PEqualNP.Outside.L_meta_5012.MixedLowerClassification

lemma no_guarded_lower_alias {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) (hT : TopForm G C) (g h : ℕ)
    (hJ : junk G C={g,h}) (hgh : g<h)
    (bg dg dh : Fin 2) (hgd : bg≠dg)
    (hpure : PureWire n C (opnd C h dh))
    (guard : ∀x : Fin n → Bool, val C (List.ofFn x) (opnd C h dh)=true →
      val C (List.ofFn x) (opnd C g bg)=true)
    (noTop : ∀a ∈ tops G C, ∀b : Fin 2, ¬OrReaches n C (opnd C a b) g) : False := by
  have hgJ : g ∈ junk G C := by simp [hJ]
  exact Alias.least_patch_alias_impossible G C hL g (opnd C g dg) (junkData hgJ).1
    (opndBound hL.1 (junkData hgJ).1 dg)
    (GuardedAlias.output_unchanged G hL hT g h hJ hgh bg dg dh hgd hpure guard noTop)

lemma no_color_raw_containment {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) (hT : TopForm G C) (g h : ℕ)
    (hJ : junk G C={g,h}) (hgh : g<h)
    (s : Fin n → Bool) (hcol : ∀u v, G.Adj u v → s u≠s v)
    (hgboth : ∀c, gateVal n C g (colorInput s c)=true)
    (c : Bool) (hhfalse : gateVal n C h (colorInput s c)=false)
    (bg bh dh : Fin 2) (hbd : bh≠dh) (hreach : OrReaches n C (opnd C h bh) g)
    (hsub : side (n := n) C h dh ⊆ side C g bg) : False := by
  obtain ⟨hpure,_,_,hhcolor⟩ := opposite_operand_classification G C hL.1 hT g h hJ s hgboth c hhfalse bh dh hbd hreach
  have noTop : ∀a ∈ tops G C, ∀b : Fin 2, ¬OrReaches n C (opnd C a b) g := by
    intro a ha b hr
    exact no_top_reaches_lower G C hL.1 hT g h hJ s hcol hgboth (!c) hhcolor ha b hr
  let dg : Fin 2 := ⟨1-bg.val,by omega⟩
  have hgd : bg≠dg := by
    intro he
    have hv := congrArg Fin.val he
    dsimp [dg] at hv
    omega
  apply no_guarded_lower_alias G hL hT g h hJ hgh bg dg dh hgd hpure ?_ noTop
  intro x hq
  rw [pure_wire_value C hL.1 _ hpure] at hq
  obtain ⟨u,hu,hxu⟩ := of_decide_eq_true hq
  exact reach_var_val x _ u (mem_orIn_reach u (hsub hu)) hxu

lemma no_both_colors_nested {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) (hT : TopForm G C) (g h : ℕ)
    (hJ : junk G C={g,h}) (hgh : g<h) (hcone : InCone n C g h)
    (s : Fin n → Bool) (hcol : ∀u v, G.Adj u v → s u≠s v)
    (hboth : ∀c, gateVal n C h (MixedOuter.fullColor s c)=true) : False := by
  have hhJ : h ∈ junk G C := by simp [hJ]
  obtain ⟨b,hb⟩ := PathCompression.upper_reaches hL.1 hT hJ hcone
  let d : Fin 2 := ⟨1-b.val,by omega⟩
  have hbd : b≠d := by
    intro he
    have hv := congrArg Fin.val he
    dsimp [d] at hv
    omega
  exact Alias.least_patch_alias_impossible G C hL h (opnd C h d) (junkData hhJ).1
    (opndBound hL.1 (junkData hhJ).1 d)
    (MixedOuter.alias_correct G hL hT g h hJ hgh s hcol hboth b d hbd hb)

end PEqualNP.Outside.L_meta_5012.AliasClosures

namespace PEqualNP.Outside.L_meta_5012.NestedFactorization
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open PEqualNP.Outside.L_meta_5012.Structural PEqualNP.Outside.L_meta_5012.Tight

lemma upper_factorization {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hT : TopForm G C) (g h : ℕ)
    (hJ : junk G C = {g,h}) (hgh : g<h)
    (b d : Fin 2) (hbd : b ≠ d) (hreach : OrReaches n C (opnd C h b) g)
    (hpure : PureWire n C (opnd C h d)) (x : Fin n → Bool) :
    gateVal n C h x =
      ((setOr (side C h b) x || gateVal n C g x) && setOr (side C h d) x) := by
  have hg : g ∈ junk G C := by simp [hJ]
  have hh : h ∈ junk G C := by simp [hJ]
  have hmin : ∀j ∈ junk G C, j<h → j=g := by
    intro j hj hjlt
    simp only [hJ,Finset.mem_insert,Finset.mem_singleton] at hj
    omega
  have hs := Semantics.firstTwoJunkSemantics n G C g h hAO hT hg hh hgh hmin h
    (by simp) x
  change (gateVal n C h x = true ↔ ∀i : Fin 2,
    (∃u ∈ side C h i, x u = true) ∨
      h=h ∧ OrReaches n C (opnd C h i) g ∧ gateVal n C g x = true) at hs
  have hnot := hpure g (junkData hg).1 (junkData hg).2.1
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true,Bool.or_eq_true]
  constructor
  · intro hv
    have hf := hs.mp hv
    constructor
    · rcases hf b with hr | ⟨_,_,hgv⟩
      · exact Or.inl (decide_eq_true hr)
      · exact Or.inr hgv
    · rcases hf d with hr | ⟨_,hr,_⟩
      · exact decide_eq_true hr
      · exact (hnot hr).elim
  · rintro ⟨hpb,hpd⟩
    apply hs.mpr
    intro i
    have hi : i=b ∨ i=d := by omega
    rcases hi with rfl | rfl
    · rcases hpb with hpb | hgv
      · exact Or.inl (of_decide_eq_true hpb)
      · exact Or.inr ⟨rfl,hreach,hgv⟩
    · exact Or.inl (of_decide_eq_true hpd)

end PEqualNP.Outside.L_meta_5012.NestedFactorization

namespace PEqualNP.Outside.L_meta_5012.MixedExitPrivacy

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open PEqualNP.Outside.L_meta_5012.Structural
open PEqualNP.Outside.L_meta_5012.MixedLowerClassification

noncomputable def bothColorGates {n : ℕ} (C : Circuit) (s : Fin n → Bool) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter fun e =>
    ∀ c : Bool, gateVal n C e (colorInput s c) = true

lemma bothColorGates_data {n : ℕ} (C : Circuit) (s : Fin n → Bool) (e : ℕ) :
    e ∈ bothColorGates C s ↔
      e < C.gates.length ∧ ∀ c : Bool, gateVal n C e (colorInput s c) = true := by
  classical
  simp only [bothColorGates, Finset.mem_filter, Finset.mem_range]

lemma bothColor_not_below {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool)
    (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (e : ℕ) (he : e ∈ bothColorGates C s) : ¬ BelowF G C e := by
  intro hbelow
  have h := hbelow (colorInput s false) (((bothColorGates_data C s e).mp he).2 false)
  rw [colorInput_false G s hcol] at h
  cases h

lemma bothColor_or_reader {n : ℕ} (C : Circuit) (hAO : IsAO2 n C)
    (s : Fin n → Bool) (e : ℕ) (he : e ∈ bothColorGates C s)
    (j : ℕ) (hj : j < C.gates.length) (hor : (gateAt C j).op = GateOp.or)
    (hread : n + e ∈ (gateAt C j).inputs) : j ∈ bothColorGates C s := by
  apply (bothColorGates_data C s j).mpr
  refine ⟨hj, ?_⟩
  intro c
  rw [gateVal_eq_val]
  apply (val_or (n := n) (by simp) hj hor).mpr
  refine ⟨n + e, hread, hAO.2.1 j hj _ hread, ?_⟩
  exact ((bothColorGates_data C s e).mp he).2 c

lemma bothColor_and_reader_junk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hT : TopForm G C)
    (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (hJcolor : ∀ j ∈ junk G C, ∃ c, gateVal n C j (colorInput s c) = true)
    (e : ℕ) (he : e ∈ bothColorGates C s)
    (j : ℕ) (hj : j < C.gates.length) (hand : (gateAt C j).op = GateOp.and)
    (hread : n + e ∈ (gateAt C j).inputs) : j ∈ junk G C := by
  classical
  have hnb : ¬ BelowF G C j := by
    intro hbelow
    have htop : j ∈ tops G C := by
      simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range]
      exact ⟨hj, hand, hbelow⟩
    obtain ⟨b, hb⟩ := inputsAsOpnd hAO hj hread
    apply no_top_operand_both_colors G C hAO hT s hcol hJcolor htop b
    intro c
    rw [← hb]
    exact ((bothColorGates_data C s e).mp he).2 c
  have hdirty : ∃ x : Fin n → Bool,
      gateVal n C j x = true ∧ graphFun G ∅ x = false := by
    by_contra hn
    apply hnb
    intro x hx
    by_contra hf
    exact hn ⟨x, hx, Bool.eq_false_iff.mpr hf⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hand, hj, hdirty⟩

lemma direct_exit_privacy {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hT : TopForm G C)
    (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (g h : ℕ) (hJ : junk G C = {g, h})
    (hgboth : ∀ c, gateVal n C g (colorInput s c) = true)
    (hhsome : ∃ c, gateVal n C h (colorInput s c) = true)
    (e : ℕ) (he : e ∈ bothColorGates C s)
    (j : ℕ) (hread : j ∈ readers n C e) :
    j ∈ bothColorGates C s ∨ j = h := by
  have hgJ : g ∈ junk G C := by simp [hJ]
  have hgM : g ∈ bothColorGates C s :=
    (bothColorGates_data C s g).mpr ⟨(junkData hgJ).1, hgboth⟩
  have hJcolor : ∀ j ∈ junk G C, ∃ c, gateVal n C j (colorInput s c) = true := by
    intro j hj
    simp only [hJ, Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl
    · exact ⟨false, hgboth false⟩
    · exact hhsome
  obtain ⟨hj, hinput⟩ := readData hread
  rcases hAO.1 _ (gateAt_mem hj) with hand | hor
  · have hjJ := bothColor_and_reader_junk G C hAO hT s hcol hJcolor e he j hj hand hinput
    simp only [hJ, Finset.mem_insert, Finset.mem_singleton] at hjJ
    rcases hjJ with rfl | rfl
    · exact Or.inl hgM
    · exact Or.inr rfl
  · exact Or.inl (bothColor_or_reader C hAO s e he j hj hor hinput)

lemma all_bothColor_before_upper {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hT : TopForm G C)
    (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (g h : ℕ) (hJ : junk G C = {g, h})
    (hgboth : ∀ c, gateVal n C g (colorInput s c) = true)
    (hhsome : ∃ c, gateVal n C h (colorInput s c) = true) :
    ∀ e ∈ bothColorGates C s, e < h := by
  intro e he
  let M := bothColorGates C s
  have hMn : M.Nonempty := ⟨e, he⟩
  let m := M.max' hMn
  have hm : m ∈ bothColorGates C s := Finset.max'_mem M hMn
  have hem : e ≤ m := Finset.le_max' M e he
  obtain ⟨j, hj⟩ := leastRead hL ((bothColorGates_data C s m).mp hm).1
    (bothColor_not_below G C s hcol m hm)
  have hmj := readLt hL.1 hj
  rcases direct_exit_privacy G C hL.1 hT s hcol g h hJ hgboth hhsome m hm j hj with hjM | rfl
  · have hjm : j ≤ m := Finset.le_max' M j hjM
    omega
  · omega

lemma upper_not_bothColor {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hT : TopForm G C)
    (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (g h : ℕ) (hJ : junk G C = {g, h})
    (hgboth : ∀ c, gateVal n C g (colorInput s c) = true)
    (hhsome : ∃ c, gateVal n C h (colorInput s c) = true) :
    h ∉ bothColorGates C s ∧ ¬ (∀ c, gateVal n C h (colorInput s c) = true) ∧ g < h := by
  have hbefore := all_bothColor_before_upper G C hL hT s hcol g h hJ hgboth hhsome
  have hnot : h ∉ bothColorGates C s := fun hh => Nat.lt_irrefl h (hbefore h hh)
  have hgJ : g ∈ junk G C := by simp [hJ]
  have hhJ : h ∈ junk G C := by simp [hJ]
  refine ⟨hnot, ?_, hbefore g ((bothColorGates_data C s g).mpr ⟨(junkData hgJ).1, hgboth⟩)⟩
  intro hboth
  exact hnot ((bothColorGates_data C s h).mpr ⟨(junkData hhJ).1, hboth⟩)

lemma bothColor_not_output {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hcompute : circuitFun n C = graphFun G ∅)
    (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (e : ℕ) (he : e ∈ bothColorGates C s) : C.output ≠ n + e := by
  intro hout
  have h : val C (List.ofFn (colorInput s false)) C.output = graphFun G ∅ (colorInput s false) :=
    congrFun hcompute (colorInput s false)
  rw [hout] at h
  have ht := ((bothColorGates_data C s e).mp he).2 false
  have hf := h.symm.trans ht
  rw [colorInput_false G s hcol] at hf
  cases hf

lemma bothColor_and_junk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (e : ℕ) (he : e ∈ bothColorGates C s) (hand : (gateAt C e).op = GateOp.and) :
    e ∈ junk G C := by
  have hed := (bothColorGates_data C s e).mp he
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hed.1, hand, hed.1,
    colorInput s false, hed.2 false, colorInput_false G s hcol false⟩

lemma only_lower_and_in_region {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hT : TopForm G C)
    (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (g h : ℕ) (hJ : junk G C = {g, h})
    (hgboth : ∀ c, gateVal n C g (colorInput s c) = true)
    (hhsome : ∃ c, gateVal n C h (colorInput s c) = true)
    (e : ℕ) (he : e ∈ bothColorGates C s) (hand : (gateAt C e).op = GateOp.and) : e = g := by
  have hjunk := bothColor_and_junk G C s hcol e he hand
  simp only [hJ, Finset.mem_insert, Finset.mem_singleton] at hjunk
  rcases hjunk with heg | heh
  · exact heg
  · exact False.elim ((upper_not_bothColor G C hL hT s hcol g h hJ hgboth hhsome).1 (heh ▸ he))

lemma all_bothColor_ancestors_upper {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hT : TopForm G C)
    (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (g h : ℕ) (hJ : junk G C = {g, h})
    (hgboth : ∀ c, gateVal n C g (colorInput s c) = true)
    (hhsome : ∃ c, gateVal n C h (colorInput s c) = true) :
    ∀ e ∈ bothColorGates C s, InCone n C e h := by
  have hbefore := all_bothColor_before_upper G C hL hT s hcol g h hJ hgboth hhsome
  have go : ∀ d e, h - e = d → e ∈ bothColorGates C s → InCone n C e h := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro e hed he
      obtain ⟨j, hj⟩ := leastRead hL ((bothColorGates_data C s e).mp he).1
        (bothColor_not_below G C s hcol e he)
      have hej := readLt hL.1 hj
      have hcone : InCone n C e j :=
        (inCone_iff n C e j).mpr ⟨(readData hj).1, e, hej, (readData hj).2, Or.inl rfl⟩
      rcases direct_exit_privacy G C hL.1 hT s hcol g h hJ hgboth hhsome e he j hj with hjM | rfl
      · have hjh := hbefore j hjM
        have hmeasure : h - j < d := by omega
        exact PEqualNP.Outside.L_meta_5012.PathCompression.inCone_trans hcone
          (ih (h - j) hmeasure j rfl hjM)
      · exact hcone
  intro e he
  exact go (h - e) e rfl he

lemma nested_upper_some_color {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hT : TopForm G C)
    (g h : ℕ) (hJ : junk G C = {g, h}) (hcone : InCone n C g h)
    (s : Fin n → Bool) (hgboth : ∀ c, gateVal n C g (colorInput s c) = true) :
    ∃ c, gateVal n C h (colorInput s c) = true := by
  obtain ⟨b, hreach⟩ := PEqualNP.Outside.L_meta_5012.PathCompression.upper_reaches hAO hT hJ hcone
  by_cases hf : gateVal n C h (colorInput s false) = true
  · exact ⟨false, hf⟩
  · let d : Fin 2 := ⟨1 - b.val, by omega⟩
    have hbd : b ≠ d := by
      intro he
      have hv := congrArg Fin.val he
      dsimp [d] at hv
      omega
    have hclass := opposite_operand_classification G C hAO hT g h hJ s hgboth false
      (Bool.eq_false_iff.mpr hf) b d hbd hreach
    exact ⟨true, by simpa using hclass.2.2.2⟩

lemma nested_region_structure {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hT : TopForm G C)
    (g h : ℕ) (hJ : junk G C = {g, h}) (hcone : InCone n C g h)
    (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (hgboth : ∀ c, gateVal n C g (colorInput s c) = true) :
    h ∉ bothColorGates C s ∧ g < h ∧
      ∀ e ∈ bothColorGates C s, e < h ∧ InCone n C e h ∧ C.output ≠ n + e ∧
        ((gateAt C e).op = GateOp.and → e = g) ∧
        ∀ j ∈ readers n C e, j ∈ bothColorGates C s ∨ j = h := by
  have hhsome := nested_upper_some_color G C hL.1 hT g h hJ hcone s hgboth
  have hupper := upper_not_bothColor G C hL hT s hcol g h hJ hgboth hhsome
  refine ⟨hupper.1, hupper.2.2, ?_⟩
  intro e he
  refine ⟨all_bothColor_before_upper G C hL hT s hcol g h hJ hgboth hhsome e he,
    all_bothColor_ancestors_upper G C hL hT s hcol g h hJ hgboth hhsome e he,
    bothColor_not_output G C hL.2.1 s hcol e he,
    only_lower_and_in_region G C hL hT s hcol g h hJ hgboth hhsome e he, ?_⟩
  intro j hj
  exact direct_exit_privacy G C hL.1 hT s hcol g h hJ hgboth hhsome e he j hj

end PEqualNP.Outside.L_meta_5012.MixedExitPrivacy
