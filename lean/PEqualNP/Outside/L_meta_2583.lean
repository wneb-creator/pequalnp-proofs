import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583

lemma eq_of_boolean_boundary {α : Type*} [PartialOrder α] [Finite α]
    (f g : α → Bool) (hf : Monotone f)
    (hmin : ∀ x, Minimal (fun y => g y = true) x → f x = true)
    (hmax : ∀ x, Maximal (fun y => g y = false) x → f x = false) :
    f = g := by
  funext x
  cases hg : g x with
  | false =>
      obtain ⟨z, hxz, hz⟩ := Finite.exists_le_maximal (p := fun y => g y = false) (a := x) hg
      have hle := hf hxz
      have hzero := hmax z hz
      cases hfx : f x <;> simp_all [Bool.le_iff_imp]
  | true =>
      obtain ⟨y, hyx, hy⟩ := Finite.exists_le_maximal (α := OrderDual α) (p := fun y => g y = true) (a := x) hg
      have hle := hf hyx
      have hone := hmin y hy
      cases hfx : f x <;> simp_all [Bool.le_iff_imp]

lemma graph_boundary_complete {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (f : (Fin n → Bool) → Bool) (hf : Monotone f)
    (hedge : ∀ u v, G.Adj u v → f (fun w => decide (w = u ∨ w = v)) = true)
    (hind : ∀ x, Maximal
      (fun y : Fin n → Bool => ∀ u v, G.Adj u v → ¬ (y u = true ∧ y v = true)) x →
      f x = false) :
    f = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
  funext x
  by_cases hx : ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true
  · obtain ⟨u, v, huv, hxu, hxv⟩ := hx
    have hpair : (fun w => decide (w = u ∨ w = v)) ≤ x := by
      intro w
      by_cases hw : w = u ∨ w = v
      · rcases hw with rfl | rfl <;> simp_all
      · simp [hw]
    have hle := hf hpair
    have hyes := hedge u v huv
    have hfx : f x = true := by
      cases hfx : f x <;> simp_all [Bool.le_iff_imp]
    simp only [hfx, PEqualNP.MetaComplexity.NestedCover.graphFun]
    simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or]
    simpa using (show (∃ a b, G.Adj a b ∧ x a = true ∧ x b = true) from ⟨u, v, huv, hxu, hxv⟩)
  · have hix : ∀ u v, G.Adj u v → ¬ (x u = true ∧ x v = true) := by
      intro u v huv h
      exact hx ⟨u, v, huv, h⟩
    obtain ⟨z, hxz, hz⟩ := Finite.exists_le_maximal (p := fun y : Fin n → Bool => ∀ u v, G.Adj u v → ¬ (y u = true ∧ y v = true)) (a := x) hix
    have hle := hf hxz
    have hzero := hind z hz
    have hfx : f x = false := by
      cases hfx : f x <;> simp_all [Bool.le_iff_imp]
    simp [hfx, PEqualNP.MetaComplexity.NestedCover.graphFun, hx]

namespace DominanceErase

open PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

lemma getD_snoc (w : List Bool) (x : Bool) (i : ℕ) :
    (w ++ [x]).getD i false =
      if i < w.length then w.getD i false else if i = w.length then x else false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append]
  split_ifs with h1 h2
  · rfl
  · subst h2; simp
  · have : 1 ≤ i - w.length := by omega
    rw [List.getElem?_eq_none (by simpa using this)]; rfl

lemma getD_big (w : List Bool) (i : ℕ) (h : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

lemma fold_len (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [List.foldl_cons, ih, step]; omega

lemma fold_stab (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    simp only [step, getD_snoc, if_pos h]

lemma op_mono (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (b : Bool) (f g : ℕ → Bool) (l : List ℕ) (h : ∀ i, f i = b → g i = b) :
    op.eval (l.map f) = b → op.eval (l.map g) = b := by
  rcases hop with rfl | rfl
  · cases b <;> simp only [GateOp.eval, List.all_map, List.all_eq_true,
      List.all_eq_false, Function.comp, id, Bool.not_eq_true]
    · exact fun ⟨x, hx, H⟩ => ⟨x, hx, h x H⟩
    · exact fun H x hx => h x (H x hx)
  · cases b <;> simp only [GateOp.eval, List.any_map, List.any_eq_true,
      List.any_eq_false, Function.comp, id, Bool.not_eq_true]
    · exact fun H x hx => h x (H x hx)
    · exact fun ⟨x, hx, H⟩ => ⟨x, hx, h x H⟩

lemma main_fold (n m p : ℕ) (b : Bool) (B : List Gate)
    (hB : ∀ g ∈ B, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) (w w' : List Bool)
    (hl : w.length = w'.length + 1) (hm : n + m ≤ w'.length)
    (hp : p < n + m ∨ w'.length + B.length ≤ p)
    (hI : ∀ i, w.getD i false = b → w'.getD (eraseRedirect n m p i) false = b) :
    ∀ i, (B.foldl step w).getD i false = b →
      ((B.map (fun g => (⟨g.op, g.inputs.map (eraseRedirect n m p)⟩ : Gate))).foldl step
        w').getD (eraseRedirect n m p i) false = b := by
  induction B generalizing w w' with
  | nil => simpa using hI
  | cons g B ih =>
    simp only [List.map_cons, List.foldl_cons]
    have hg := hB g (by simp)
    simp only [List.length_cons] at hp
    apply ih (fun g' hg' => hB g' (by simp [hg']))
    · simp [step, hl]
    · simp [step]; omega
    · simp [step]; omega
    · intro i
      simp only [step, getD_snoc, List.map_map]
      have hx := op_mono g.op hg b (fun i => w.getD i false)
        (fun i => w'.getD (eraseRedirect n m p i) false) g.inputs hI
      have hIi := hI i
      obtain ⟨r, hr⟩ : ∃ r, r = eraseRedirect n m p i := ⟨_, rfl⟩
      rw [← hr] at hIi ⊢
      unfold eraseRedirect at hr
      by_cases h1 : i < w.length
      · rw [if_pos h1]
        intro hb
        have h3 := hIi hb
        by_cases hr1 : r < w'.length
        · rw [if_pos hr1]; exact h3
        · have h4 : w'.length < r := by split_ifs at hr <;> omega
          rw [if_neg hr1, if_neg (by omega)]
          rw [getD_big _ _ (by omega)] at h3
          exact h3
      · rw [if_neg h1]
        by_cases h2 : i = w.length
        · rw [if_pos h2]
          intro hb
          have h3 := hx hb
          have h4 : r = w'.length := by split_ifs at hr <;> omega
          rw [if_neg (by omega), if_pos h4]
          exact h3
        · have h4 : w'.length < r := by split_ifs at hr <;> omega
          rw [if_neg h2, if_neg (by omega), if_neg (by omega)]
          exact id

lemma erase_main : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x2 →     x3 < x2.size →       x4 < x1 + x3 ∨ x4 = x1 + x2.size →         have x8 : PEqualNP.CircuitLowerBounds.Circuit := PEqualNP.CircuitMoves.eraseGate x1 x2 x3 x4;         PEqualNP.MetaComplexity.Monotone2 x8 ∧ x8.size + (1 : ℕ) = x2.size ∧ ∀ (x9 : List Bool), x9.length = x1 → ∀ (x11 : Bool), (PEqualNP.LowMerge.wireVal x2 x9 (x1 + x3) = x11 → PEqualNP.LowMerge.wireVal x2 x9 x4 = x11) → ∀ (x13 : ℕ), PEqualNP.LowMerge.wireVal x2 x9 x13 = x11 → PEqualNP.LowMerge.wireVal x8 x9 (PEqualNP.CircuitMoves.eraseRedirect x1 x3 x4 x13) = x11 := by
  intro n C m p hM hm hp
  have hm' : m < C.gates.length := hm
  have hsize : C.size = C.gates.length := rfl
  have hsplit : C.gates = C.gates.take m ++ C.gates[m] :: C.gates.drop (m + 1) := by simp
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [eraseGate, if_pos hm', List.mem_append, List.mem_map] at hg
    rcases hg with hg | ⟨g', hg', rfl⟩
    · exact hM g (List.mem_of_mem_take hg)
    · have := hM g' (List.mem_of_mem_drop hg')
      exact ⟨this.1, by simpa using this.2⟩
  · simp only [eraseGate, if_pos hm', Circuit.size, List.length_append, List.length_take,
      List.length_map, List.length_drop]
    omega
  · intro x hx b hyp i
    simp only [PEqualNP.LowMerge.wireVal, wires_eq] at hyp ⊢
    have key : C.gates.foldl step x = (C.gates.drop (m + 1)).foldl step
        (step ((C.gates.take m).foldl step x) C.gates[m]) := by
      conv_lhs => rw [hsplit]
      rw [List.foldl_append, List.foldl_cons]
    rw [key] at hyp ⊢
    simp only [eraseGate, if_pos hm']
    rw [List.foldl_append]
    have hWA : (List.foldl step x (List.take m C.gates)).length = n + m := by
      rw [fold_len, hx, List.length_take]; omega
    have hdl : (C.gates.drop (m + 1)).length = C.gates.length - (m + 1) := by simp
    apply main_fold n m p b _ (fun g hg => (hM g (List.mem_of_mem_drop hg)).1)
    · simp [step]
    · omega
    · rw [hWA, hdl]; rcases hp with hp | hp
      · left; exact hp
      · right; rw [hp, hsize]; omega
    · intro j
      generalize hWAd : List.foldl step x (List.take m C.gates) = WA at *
      rw [fold_stab _ _ _ (by simp [step]; omega)] at hyp
      unfold eraseRedirect
      by_cases h1 : j = n + m
      · subst h1; rw [if_pos rfl]
        intro hb
        have h2 := hyp hb
        rcases hp with hp | hp
        · rw [fold_stab _ _ _ (by simp [step]; omega)] at h2
          simp only [step, getD_snoc, hWA, if_pos hp] at h2; exact h2
        · rw [getD_big _ _ (by rw [fold_len]; simp [step]; omega)] at h2
          rw [getD_big _ _ (by omega)]; exact h2
      · rw [if_neg h1]
        simp only [step, getD_snoc, hWA]
        by_cases h3 : j < n + m
        · rw [if_pos h3, if_neg (by omega)]; exact id
        · rw [if_neg h3, if_neg h1, if_pos (by omega), getD_big _ _ (by omega)]; exact id

open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.LowMerge

lemma ao_to_mono {n : ℕ} {C : Circuit} (h : IsAO2 n C) : Monotone2 C := by
  intro g hg
  exact ⟨h.1 g hg, by rw [h.2.2 g hg]⟩

lemma erase_ao {n : ℕ} {C : Circuit} {m p : ℕ}
    (hAO : IsAO2 n C) (hm : m < C.size) (hp : p < n + m) :
    IsAO2 n (eraseGate n C m p) := by
  have hm' : m < C.gates.length := hm
  have hR := hAO.2.1
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [eraseGate, if_pos hm', List.mem_append, List.mem_map] at hg
    rcases hg with hg | ⟨g', hg', rfl⟩
    · exact hAO.1 g (List.mem_of_mem_take hg)
    · exact hAO.1 g' (List.mem_of_mem_drop hg')
  · intro j hj i hi
    simp only [eraseGate, if_pos hm', List.length_append, List.length_take,
      List.length_map, List.length_drop] at hj
    simp only [gateAt, eraseGate, if_pos hm', List.getD_eq_getElem?_getD] at hi
    by_cases hjm : j < m
    · rw [List.getElem?_append_left (by simp; omega)] at hi
      have := hR j (by omega) i
      simp only [gateAt, List.getD_eq_getElem?_getD] at this
      rw [List.getElem?_take, if_pos hjm] at hi
      exact this hi
    · rw [List.getElem?_append_right (by simp; omega)] at hi
      have hlen : (List.take m C.gates).length = m := by simp; omega
      rw [hlen, List.getElem?_map, List.getElem?_drop,
        List.getElem?_eq_getElem (by omega)] at hi
      simp only [Option.map_some, Option.getD_some, List.mem_map] at hi
      obtain ⟨i', hi', rfl⟩ := hi
      have := hR (m + 1 + (j - m)) (by omega) i'
      simp only [gateAt, List.getD_eq_getElem?_getD] at this
      rw [List.getElem?_eq_getElem (by omega)] at this
      have := this hi'
      unfold eraseRedirect
      split_ifs <;> omega
  · intro g hg
    simp only [eraseGate, if_pos hm', List.mem_append, List.mem_map] at hg
    rcases hg with hg | ⟨g', hg', rfl⟩
    · exact hAO.2.2 g (List.mem_of_mem_take hg)
    · simpa using hAO.2.2 g' (List.mem_of_mem_drop hg')

lemma fold_preserves_true (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w z : List Bool) (hlen : w.length = z.length)
    (hval : ∀ i, w.getD i false = true → z.getD i false = true) :
    ∀ i, (gs.foldl step w).getD i false = true →
      (gs.foldl step z).getD i false = true := by
  induction gs generalizing w z with
  | nil => exact hval
  | cons g gs ih =>
      simp only [List.foldl_cons]
      apply ih (fun g' hg' => hgs g' (by simp [hg']))
      · simp [step, hlen]
      · intro i hi
        have hgate := op_mono g.op (hgs g (by simp)) true
          (fun j => w.getD j false) (fun j => z.getD j false) g.inputs hval
        simp only [step, getD_snoc, hlen] at hi ⊢
        split_ifs at hi ⊢ with hlt heq
        · exact hval i hi
        · exact hgate hi

lemma circuitFun_monotone {n : ℕ} {C : Circuit} (hAO : AndOrOnly C) :
    Monotone (circuitFun n C) := by
  intro x y hxy
  apply Bool.le_iff_imp.mpr
  change (C.gates.foldl step (List.ofFn x)).getD C.output false = true →
    (C.gates.foldl step (List.ofFn y)).getD C.output false = true
  apply fold_preserves_true C.gates hAO _ _ (by simp)
  intro i hi
  by_cases hin : i < n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hin, Option.getD_some] at hi ⊢
    exact Bool.le_iff_imp.mp (hxy ⟨i, hin⟩) hi
  · simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hin] at hi

lemma dominance_erase {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (m p : ℕ) (hAO : IsAO2 n C)
    (hF : circuitFun n C = graphFun G ∅) (hm : m < C.size) (hp : p < n + m)
    (hedge : ∀ u v, G.Adj u v →
      wireVal C (List.ofFn (fun w => decide (w = u ∨ w = v))) (n + m) ≤
      wireVal C (List.ofFn (fun w => decide (w = u ∨ w = v))) p)
    (hind : ∀ x, Maximal
      (fun y : Fin n → Bool => ∀ u v, G.Adj u v → ¬ (y u = true ∧ y v = true)) x →
      wireVal C (List.ofFn x) p ≤ wireVal C (List.ofFn x) (n + m)) :
    IsAO2 n (eraseGate n C m p) ∧
    (eraseGate n C m p).size + 1 = C.size ∧
    circuitFun n (eraseGate n C m p) = graphFun G ∅ := by
  have hm' : m < C.gates.length := hm
  have hAO' := erase_ao hAO hm hp
  obtain ⟨_, hsize, hsim⟩ := erase_main n C m p (ao_to_mono hAO) hm (Or.inl hp)
  refine ⟨hAO', hsize, ?_⟩
  apply PEqualNP.Outside.L_meta_2583.graph_boundary_complete G _ (circuitFun_monotone hAO'.1)
  · intro u v huv
    let x : Fin n → Bool := fun w => decide (w = u ∨ w = v)
    have hsource : circuitFun n C x = true := by
      rw [hF]
      simp only [graphFun]
      have hx : ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true := by
        exact ⟨u, v, huv, by simp [x], by simp [x]⟩
      simp [hx]
    have hpres := hsim (List.ofFn x) (by simp) true
      (Bool.le_iff_imp.mp (hedge u v huv)) C.output hsource
    simpa only [circuitFun, Circuit.eval, wireVal, eraseGate, if_pos hm'] using hpres
  · intro x hx
    have hsource : circuitFun n C x = false := by
      rw [hF]
      have hno : ¬ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
        rintro ⟨u, v, huv, hxu, hxv⟩
        exact hx.1 u v huv ⟨hxu, hxv⟩
      simp [graphFun, hno]
    have hgate : wireVal C (List.ofFn x) (n + m) = false →
        wireVal C (List.ofFn x) p = false := by
      intro hzero
      have hle := hind x hx
      cases hpval : wireVal C (List.ofFn x) p <;> simp_all [Bool.le_iff_imp]
    have hpres := hsim (List.ofFn x) (by simp) false hgate C.output hsource
    simpa only [circuitFun, Circuit.eval, wireVal, eraseGate, if_pos hm'] using hpres

lemma least_no_dominance {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hleast : IsLeastAO G C) (m p : ℕ) (hm : m < C.size) (hp : p < n + m) :
    ¬ ((∀ u v, G.Adj u v →
      wireVal C (List.ofFn (fun w => decide (w = u ∨ w = v))) (n + m) ≤
      wireVal C (List.ofFn (fun w => decide (w = u ∨ w = v))) p) ∧
    (∀ x, Maximal
      (fun y : Fin n → Bool => ∀ u v, G.Adj u v → ¬ (y u = true ∧ y v = true)) x →
      wireVal C (List.ofFn x) p ≤ wireVal C (List.ofFn x) (n + m))) := by
  rintro ⟨hedge, hind⟩
  obtain ⟨hAO, hsize, hF⟩ := dominance_erase G C m p hleast.1 hleast.2.1 hm hp hedge hind
  have hmin := hleast.2.2 _ hAO hF
  omega

end DominanceErase


def fanoIncidence (p l : Fin 7) : Prop :=
  (p.val, l.val) ∈ ({(0, 1), (0, 3), (0, 5), (1, 0), (1, 3), (1, 4),
    (2, 2), (2, 3), (2, 6), (3, 0), (3, 1), (3, 2), (4, 1), (4, 4),
    (4, 6), (5, 0), (5, 5), (5, 6), (6, 2), (6, 4), (6, 5)} : Finset (ℕ × ℕ))

def fano_decidable : DecidableRel fanoIncidence := by
  intro p l
  unfold fanoIncidence
  infer_instance

lemma fano_column_cardinality :
    letI := fano_decidable
    ∀ l : Fin 7, (Finset.univ.filter (fun p => fanoIncidence p l)).card = 2 + 1 := by
  decide

lemma fano_unique_line :
    ∀ p p' : Fin 7, p ≠ p' → ∃! l : Fin 7, fanoIncidence p l ∧ fanoIncidence p' l := by
  letI := fano_decidable
  unfold ExistsUnique
  decide


end PEqualNP.Outside.L_meta_2583
