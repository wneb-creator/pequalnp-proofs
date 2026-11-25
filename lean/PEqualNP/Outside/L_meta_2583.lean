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



def pg3SatIncidence (p l : Fin 13) : Prop :=
  (p.val, l.val) ∈ ({(0, 1), (0, 4), (0, 7), (0, 10),
    (1, 0), (1, 4), (1, 5), (1, 6),
    (2, 3), (2, 4), (2, 9), (2, 11),
    (3, 2), (3, 4), (3, 8), (3, 12),
    (4, 0), (4, 1), (4, 2), (4, 3),
    (5, 1), (5, 6), (5, 9), (5, 12),
    (6, 1), (6, 5), (6, 8), (6, 11),
    (7, 0), (7, 10), (7, 11), (7, 12),
    (8, 3), (8, 6), (8, 8), (8, 10),
    (9, 2), (9, 5), (9, 9), (9, 10),
    (10, 0), (10, 7), (10, 8), (10, 9),
    (11, 2), (11, 6), (11, 7), (11, 11),
    (12, 3), (12, 5), (12, 7), (12, 12)} : Finset (ℕ × ℕ))

def pg3SatDecidable : DecidableRel pg3SatIncidence := by
  intro p l
  unfold pg3SatIncidence
  infer_instance

set_option maxRecDepth 8192 in
lemma pg3Sat_column_cardinality :
    letI := pg3SatDecidable
    ∀ l : Fin 13, (Finset.univ.filter (fun p => pg3SatIncidence p l)).card = 3 + 1 := by
  decide +kernel

set_option maxRecDepth 8192 in
lemma pg3Sat_unique_line :
    ∀ p p' : Fin 13, p ≠ p' → ∃! l : Fin 13, pg3SatIncidence p l ∧ pg3SatIncidence p' l := by
  letI := pg3SatDecidable
  unfold ExistsUnique
  decide

def pg3StochasticIncidence (p l : Fin 13) : Prop :=
  (p.val, l.val) ∈ ({(0, 9), (0, 10), (0, 11), (0, 12),
    (1, 2), (1, 5), (1, 8), (1, 9),
    (2, 1), (2, 4), (2, 7), (2, 9),
    (3, 6), (3, 7), (3, 8), (3, 12),
    (4, 2), (4, 4), (4, 6), (4, 11),
    (5, 1), (5, 5), (5, 6), (5, 10),
    (6, 3), (6, 4), (6, 5), (6, 12),
    (7, 2), (7, 3), (7, 7), (7, 10),
    (8, 1), (8, 3), (8, 8), (8, 11),
    (9, 0), (9, 1), (9, 2), (9, 12),
    (10, 0), (10, 5), (10, 7), (10, 11),
    (11, 0), (11, 4), (11, 8), (11, 10),
    (12, 0), (12, 3), (12, 6), (12, 9)} : Finset (ℕ × ℕ))

def pg3StochasticDecidable : DecidableRel pg3StochasticIncidence := by
  intro p l
  unfold pg3StochasticIncidence
  infer_instance

set_option maxRecDepth 8192 in
lemma pg3Stochastic_column_cardinality :
    letI := pg3StochasticDecidable
    ∀ l : Fin 13, (Finset.univ.filter (fun p => pg3StochasticIncidence p l)).card = 3 + 1 := by
  decide +kernel

set_option maxRecDepth 8192 in
lemma pg3Stochastic_unique_line :
    ∀ p p' : Fin 13, p ≠ p' → ∃! l : Fin 13, pg3StochasticIncidence p l ∧ pg3StochasticIncidence p' l := by
  letI := pg3StochasticDecidable
  unfold ExistsUnique
  decide

def pg3StochasticToSat (p : Fin 13) : Fin 13 :=
  ([4, 5, 6, 7, 8, 9, 10, 11, 12, 1, 2, 3, 0] : List (Fin 13)).getD p.val 0

lemma pg3StochasticToSat_bijective : Function.Bijective pg3StochasticToSat := by
  decide +kernel

set_option maxRecDepth 8192 in
lemma pg3OrdersAgree : ∀ p l : Fin 13,
    pg3StochasticIncidence p l ↔
      pg3SatIncidence (pg3StochasticToSat p) (pg3StochasticToSat l) := by
  letI := pg3SatDecidable
  letI := pg3StochasticDecidable
  decide

lemma pg3_order_parameters : 2 ≤ (3 : ℕ) ∧ 13 = 3 ^ 2 + 3 + 1 := by
  decide +kernel



def pg3CyclicIncidence (p l : Fin 13) : Prop :=
  p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9

def pg3SatPointToCyclic (p : Fin 13) : Fin 13 :=
  ([0, 1, 3, 9, 2, 8, 12, 4, 5, 7, 10, 6, 11] : List (Fin 13)).getD p.val 0

lemma pg3SatPointToCyclic_bijective : Function.Bijective pg3SatPointToCyclic := by
  decide +kernel

def pg3SatLineToCyclic (p : Fin 13) : Fin 13 :=
  ([1, 12, 6, 2, 0, 11, 5, 10, 9, 7, 4, 3, 8] : List (Fin 13)).getD p.val 0

lemma pg3SatLineToCyclic_bijective : Function.Bijective pg3SatLineToCyclic := by
  decide +kernel

set_option maxRecDepth 8192 in
lemma pg3SatCyclicAgree : ∀ p l : Fin 13,
    pg3SatIncidence p l ↔
      pg3CyclicIncidence (pg3SatPointToCyclic p) (pg3SatLineToCyclic l) := by
  letI := pg3SatDecidable
  unfold pg3CyclicIncidence
  decide

lemma pg3CyclicDifference : ∀ p l : Fin 13,
    pg3CyclicIncidence p l ↔ p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) := by
  unfold pg3CyclicIncidence
  decide +kernel


def incidenceEnvelope {m n : ℕ} (I : Fin m → Fin n → Prop) [DecidableRel I]
    (S : Finset (Fin m)) : Fin (m + n) → Bool :=
  Fin.addCases (fun p => decide (p ∈ S)) (fun l => decide (∀ p ∈ S, ¬ I p l))

lemma incidence_envelope_complete {m n : ℕ} (I : Fin m → Fin n → Prop) [DecidableRel I]
    (f : (Fin (m + n) → Bool) → Bool) (hf : Monotone f)
    (hpos : ∀ p l, I p l →
      f (fun z => decide (z = Fin.castAdd n p ∨ z = Fin.natAdd m l)) = true)
    (hneg : ∀ S : Finset (Fin m), f (incidenceEnvelope I S) = false) :
    ∀ x, f x = decide (∃ p l, I p l ∧ x (Fin.castAdd n p) = true ∧
      x (Fin.natAdd m l) = true) := by
  intro x
  by_cases hx : ∃ p l, I p l ∧ x (Fin.castAdd n p) = true ∧ x (Fin.natAdd m l) = true
  · obtain ⟨p, l, hpl, hp, hl⟩ := hx
    have hpair : (fun z => decide (z = Fin.castAdd n p ∨ z = Fin.natAdd m l)) ≤ x := by
      intro z
      by_cases hz : z = Fin.castAdd n p ∨ z = Fin.natAdd m l
      · rcases hz with rfl | rfl <;> simp_all
      · simp [hz]
    have htrue : f x = true := Bool.le_iff_imp.mp (hf hpair) (hpos p l hpl)
    simp [htrue]
    exact ⟨p, l, hpl, hp, hl⟩
  · let S : Finset (Fin m) := Finset.univ.filter fun p => x (Fin.castAdd n p) = true
    have hS (p : Fin m) : p ∈ S ↔ x (Fin.castAdd n p) = true := by simp [S]
    have henv : x ≤ incidenceEnvelope I S := by
      intro z
      refine Fin.addCases (fun p => ?_) (fun l => ?_) z
      · simp [incidenceEnvelope, hS]
      · apply Bool.le_iff_imp.mpr
        intro hl
        simp only [incidenceEnvelope, Fin.addCases_right, decide_eq_true_eq]
        intro p hp hpl
        exact hx ⟨p, l, hpl, (hS p).mp hp, hl⟩
    have hle := hf henv
    have hzero := hneg S
    have hfalse : f x = false := by
      cases hfx : f x <;> simp_all [Bool.le_iff_imp]
    simp [hfalse, hx]


lemma circuit_incidence_envelope_complete {m n : ℕ}
    (I : Fin m → Fin n → Prop) [DecidableRel I]
    (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hAO : PEqualNP.TopForm.IsAO2 (m + n) C)
    (hpos : ∀ p l, I p l →
      PEqualNP.MetaComplexity.circuitFun (m + n) C
        (fun z => decide (z = Fin.castAdd n p ∨ z = Fin.natAdd m l)) = true)
    (hneg : ∀ S : Finset (Fin m),
      PEqualNP.MetaComplexity.circuitFun (m + n) C (incidenceEnvelope I S) = false) :
    ∀ x, PEqualNP.MetaComplexity.circuitFun (m + n) C x =
      decide (∃ p l, I p l ∧ x (Fin.castAdd n p) = true ∧ x (Fin.natAdd m l) = true) := by
  exact incidence_envelope_complete I _ (DominanceErase.circuitFun_monotone hAO.1) hpos hneg

namespace InputRelabel

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

def wireMap {n : ℕ} (σ : Fin n → Fin n) (i : ℕ) : ℕ :=
  if h : i < n then (σ ⟨i, h⟩).val else i

def gateMap {n : ℕ} (σ : Fin n → Fin n) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wireMap σ)⟩

def relabel {n : ℕ} (σ : Fin n → Fin n) (C : Circuit) : Circuit :=
  ⟨C.gates.map (gateMap σ), wireMap σ C.output⟩

lemma wireMap_ge {n : ℕ} (σ : Fin n → Fin n) {i : ℕ} (h : n ≤ i) :
    wireMap σ i = i := by simp [wireMap, Nat.not_lt.mpr h]

lemma wireMap_lt {n : ℕ} (σ : Fin n → Fin n) {i : ℕ} (h : i < n) :
    wireMap σ i < n := by
  rw [wireMap, dif_pos h]
  exact (σ ⟨i, h⟩).isLt

lemma size_eq {n : ℕ} (σ : Fin n → Fin n) (C : Circuit) :
    (relabel σ C).size = C.size := by simp [relabel, Circuit.size]

lemma op_list_eq {n : ℕ} (σ : Fin n → Fin n) (C : Circuit) :
    (relabel σ C).gates.map Gate.op = C.gates.map Gate.op := by
  simp [relabel, gateMap, List.map_map]

lemma op_count_eq {n : ℕ} (σ : Fin n → Fin n) (C : Circuit) (op : GateOp) :
    Set.ncard {j : Fin (relabel σ C).gates.length |
      ((relabel σ C).gates.get j).op = op} =
    Set.ncard {j : Fin C.gates.length | (C.gates.get j).op = op} := by
  refine Set.ncard_congr
    (fun j _ => (⟨j.val, by simpa [relabel] using j.isLt⟩ : Fin C.gates.length)) ?_ ?_ ?_
  · intro j hj
    have hjlt : j.val < C.gates.length := by simpa [relabel] using j.isLt
    change ((relabel σ C).gates[j.val]'j.isLt).op = op at hj
    change (C.gates[j.val]'hjlt).op = op
    simpa only [relabel, List.getElem_map, gateMap] using hj
  · intro a b ha hb hab
    apply Fin.ext
    exact congrArg (fun z : Fin C.gates.length => z.val) hab
  · intro j hj
    let k : Fin (relabel σ C).gates.length := ⟨j.val, by simpa [relabel] using j.isLt⟩
    refine ⟨k, ?_, ?_⟩
    · change ((relabel σ C).gates[k.val]'k.isLt).op = op
      change (C.gates[j.val]'j.isLt).op = op at hj
      simpa only [relabel, List.getElem_map, gateMap, k] using hj
    · apply Fin.ext
      rfl

lemma monotone2 {n : ℕ} (σ : Fin n → Fin n) {C : Circuit} (hC : Monotone2 C) :
    Monotone2 (relabel σ C) := by
  intro g hg
  obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
  obtain ⟨hop, hlen⟩ := hC g' hg'
  exact ⟨hop, by simpa [gateMap] using hlen⟩

lemma isAO2 {n : ℕ} (σ : Fin n → Fin n) {C : Circuit} (hC : IsAO2 n C) :
    IsAO2 n (relabel σ C) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    exact hC.1 g' hg'
  · intro j hj i hi
    have hj' : j < C.gates.length := by simpa [relabel] using hj
    simp only [gateAt, relabel, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hj', Option.map_some, Option.getD_some, gateMap,
      List.mem_map] at hi
    obtain ⟨k, hk, rfl⟩ := hi
    have hk' : k < n + j := hC.2.1 j hj' k (by
      simpa only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj',
        Option.getD_some] using hk)
    by_cases hkn : k < n
    · have := wireMap_lt σ hkn
      omega
    · rw [wireMap_ge σ (by omega)]
      exact hk'
  · intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    simpa [gateMap] using hC.2.2 g' hg'

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma fold_map {n : ℕ} (σ : Fin n → Fin n) (gs : List Gate) :
    ∀ w w' : List Bool, w.length = w'.length → n ≤ w.length →
    (∀ i, w'.getD (wireMap σ i) false = w.getD i false) →
    ∀ i, ((gs.map (gateMap σ)).foldl step w').getD (wireMap σ i) false =
      (gs.foldl step w).getD i false := by
  induction gs with
  | nil => intro w w' _ _ h i; exact h i
  | cons g gs ih =>
    intro w w' hl hn h i
    simp only [List.map_cons, List.foldl_cons]
    apply ih
    · simp [step, hl]
    · simp [step]; omega
    · intro j
      have hv : g.op.eval ((g.inputs.map (wireMap σ)).map fun i => w'.getD i false) =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        rw [List.map_map]
        congr 1
        apply List.map_congr_left
        intro a _
        exact h a
      simp only [step, gateMap]
      rw [hv]
      rcases Nat.lt_trichotomy j w.length with hj | hj | hj
      · have hj' : wireMap σ j < w'.length := by
          by_cases h' : j < n
          · have := wireMap_lt σ h'; omega
          · rw [wireMap_ge σ (by omega)]; omega
        have e := h j
        simp only [List.getD_eq_getElem?_getD] at e ⊢
        rw [List.getElem?_append_left hj', List.getElem?_append_left hj]
        exact e
      · subst hj
        rw [wireMap_ge σ hn]
        simp [List.getD_eq_getElem?_getD, hl]
      · rw [wireMap_ge σ (by omega)]
        rw [List.getD_eq_default _ _ (by simp; omega),
          List.getD_eq_default _ _ (by simp; omega)]

lemma circuitFun_eq {n : ℕ} (σ : Fin n → Fin n) (C : Circuit) (y : Fin n → Bool) :
    circuitFun n (relabel σ C) y = circuitFun n C (fun i => y (σ i)) := by
  change ((C.gates.map (gateMap σ)).foldl step (List.ofFn y)).getD
      (wireMap σ C.output) false =
    (C.gates.foldl step (List.ofFn fun i => y (σ i))).getD C.output false
  apply fold_map σ C.gates _ _ (by simp) (by simp)
  intro i
  by_cases hi : i < n
  · simp [wireMap, hi, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  · rw [wireMap_ge σ (by omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]

def blockMap {m n : ℕ} (σ : Fin m → Fin m) (τ : Fin n → Fin n) :
    Fin (m + n) → Fin (m + n) :=
  Fin.addCases (fun p => Fin.castAdd n (σ p)) (fun l => Fin.natAdd m (τ l))

lemma incidence_transport {m n : ℕ} (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n))
    (I J : Fin m → Fin n → Prop) [DecidableRel I] [DecidableRel J]
    (hI : ∀ p l, I p l ↔ J (σ p) (τ l)) (C : Circuit)
    (hC : ∀ x, circuitFun (m + n) C x = decide
      (∃ p l, I p l ∧ x (Fin.castAdd n p) = true ∧ x (Fin.natAdd m l) = true)) :
    ∀ y, circuitFun (m + n) (relabel (blockMap σ τ) C) y = decide
      (∃ p l, J p l ∧ y (Fin.castAdd n p) = true ∧ y (Fin.natAdd m l) = true) := by
  intro y
  rw [circuitFun_eq, hC]
  apply decide_eq_decide.mpr
  constructor
  · rintro ⟨p, l, hpl, hp, hl⟩
    exact ⟨σ p, τ l, (hI p l).mp hpl,
      by simpa [blockMap] using hp, by simpa [blockMap] using hl⟩
  · rintro ⟨p, l, hpl, hp, hl⟩
    obtain ⟨p', rfl⟩ := σ.surjective p
    obtain ⟨l', rfl⟩ := τ.surjective l
    exact ⟨p', l', (hI p' l').mpr hpl,
      by simpa [blockMap] using hp, by simpa [blockMap] using hl⟩

lemma incidence_transport_exists {m n : ℕ}
    (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n))
    (I J : Fin m → Fin n → Prop) [DecidableRel I] [DecidableRel J]
    (hI : ∀ p l, I p l ↔ J (σ p) (τ l)) (C : Circuit) (hAO : IsAO2 (m + n) C)
    (hC : ∀ x, circuitFun (m + n) C x = decide
      (∃ p l, I p l ∧ x (Fin.castAdd n p) = true ∧ x (Fin.natAdd m l) = true)) :
    ∃ D : Circuit, IsAO2 (m + n) D ∧ D.size = C.size ∧
      (∀ y, circuitFun (m + n) D y = decide
        (∃ p l, J p l ∧ y (Fin.castAdd n p) = true ∧ y (Fin.natAdd m l) = true)) ∧
      ∀ op : GateOp,
        Set.ncard {j : Fin D.gates.length | (D.gates.get j).op = op} =
        Set.ncard {j : Fin C.gates.length | (C.gates.get j).op = op} := by
  exact ⟨relabel (blockMap σ τ) C, isAO2 _ hAO, size_eq _ _,
    incidence_transport σ τ I J hI C hC, op_count_eq _ _⟩

end InputRelabel

namespace AndCrossing

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_len (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepW]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepW w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepW w g).length := by simp [stepW]; omega
    rw [ih (stepW w g) hlt]
    simp [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_char (gs : List Gate) (w : List Bool) :
    ∀ j, j < gs.length → (gs.foldl stepW w).getD (w.length + j) false =
      (gs.getD j ⟨GateOp.or, []⟩).op.eval ((gs.getD j ⟨GateOp.or, []⟩).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepW w).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen := foldl_len gs w
    simp only [List.length_append, List.length_singleton] at hj
    have key : ∀ i, i < w.length + gs.length →
        (stepW (gs.foldl stepW w) g).getD i false = (gs.foldl stepW w).getD i false := by
      intro i hi
      simp only [stepW, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_or_ge j gs.length with h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [e1, key _ (by omega), ih j h]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [key i (by omega)]
      · rfl
    · have hj' : j = gs.length := by omega
      subst hj'
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      have e2 : (stepW (gs.foldl stepW w) g).getD (w.length + gs.length) false =
          g.op.eval (g.inputs.map fun i => (gs.foldl stepW w).getD i false) := by
        simp only [stepW, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [key i hi]
      · simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by omega)]
        rfl

def wv (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepW x := rfl

lemma wv_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    wv n C x w = x ⟨w, hw⟩ := by
  unfold wv
  rw [wires_eq, foldl_getD_lt _ _ _ (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

lemma wv_rec (n : ℕ) (C : Circuit) (x : Fin n → Bool)
    (hC : ReadsBack n C) (j : ℕ) (hj : j < C.gates.length) :
    wv n C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (wv n C x)) := by
  have h := foldl_char C.gates (List.ofFn x) j hj
  simp only [List.length_ofFn] at h
  unfold wv gateAt
  rw [wires_eq, h]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [ite_eq_left (hC j hj i hi)]

lemma wv_missing (n : ℕ) (C : Circuit) (x : Fin n → Bool)
    (w : ℕ) (hw : n + C.gates.length ≤ w) : wv n C x w = false := by
  have hlen : (C.wires (List.ofFn x)).length = n + C.gates.length := by
    rw [wires_eq, foldl_len, List.length_ofFn]
  unfold wv
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_none (by omega)]
  rfl

lemma gate_mem (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k ∈ C.gates := by
  unfold gateAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  exact List.getElem_mem hk

lemma inputs_two (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (k : ℕ) (hk : k < C.gates.length) :
    (gateAt C k).inputs = [opnd C k 0, opnd C k 1] := by
  obtain ⟨a, b, hin⟩ := List.length_eq_two.mp (hAO.2.2 _ (gate_mem C k hk))
  simp [opnd, hin]

lemma opnd_back (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (k : ℕ) (hk : k < C.gates.length) (b : Fin 2) : opnd C k b < n + k := by
  apply hAO.2.1 k hk
  rw [inputs_two n C hAO k hk]
  fin_cases b <;> simp


def Crosses (n : ℕ) (C : Circuit) (x y : Fin n → Bool) (k : ℕ) : Prop :=
  (wv n C x (opnd C k 0) = true ∧ wv n C x (opnd C k 1) = false ∧
   wv n C y (opnd C k 0) = false ∧ wv n C y (opnd C k 1) = true) ∨
  (wv n C x (opnd C k 0) = false ∧ wv n C x (opnd C k 1) = true ∧
   wv n C y (opnd C k 0) = true ∧ wv n C y (opnd C k 1) = false)

lemma and_false_common (a b c d : Bool)
    (hx : (a && b) = false) (hy : (c && d) = false)
    (hno : ¬ ((a = true ∧ b = false ∧ c = false ∧ d = true) ∨
              (a = false ∧ b = true ∧ c = true ∧ d = false))) :
    (a = false ∧ c = false) ∨ (b = false ∧ d = false) := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

lemma false_join_of_no_crossing (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (r : ℕ) (hr : r ≤ C.gates.length) (x y : Fin n → Bool)
    (hno : ∀ k < r, (gateAt C k).op = GateOp.and → ¬ Crosses n C x y k) :
    ∀ w, w < n + r → wv n C x w = false → wv n C y w = false →
      wv n C (fun i => x i || y i) w = false := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hx hy
    by_cases hwn : w < n
    · rw [wv_input n C x w hwn] at hx
      rw [wv_input n C y w hwn] at hy
      rw [wv_input n C _ w hwn]
      simp [hx, hy]
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hkr : k < r := by omega
      have hk : k < C.gates.length := by omega
      have ha := opnd_back n C hAO k hk 0
      have hb := opnd_back n C hAO k hk 1
      rw [wv_rec n C x hAO.2.1 k hk, inputs_two n C hAO k hk] at hx
      rw [wv_rec n C y hAO.2.1 k hk, inputs_two n C hAO k hk] at hy
      rw [wv_rec n C _ hAO.2.1 k hk, inputs_two n C hAO k hk]
      rcases hAO.1 _ (gate_mem C k hk) with hop | hop
      · have hcommon := and_false_common
          (wv n C x (opnd C k 0)) (wv n C x (opnd C k 1))
          (wv n C y (opnd C k 0)) (wv n C y (opnd C k 1))
          (by simpa [hop, GateOp.eval] using hx)
          (by simpa [hop, GateOp.eval] using hy)
          (hno k hkr hop)
        rcases hcommon with ⟨hx0, hy0⟩ | ⟨hx1, hy1⟩
        · have hj := ih _ ha (by omega) hx0 hy0
          simp [hop, GateOp.eval, hj]
        · have hj := ih _ hb (by omega) hx1 hy1
          simp [hop, GateOp.eval, hj]
      · have hxx : wv n C x (opnd C k 0) = false ∧
            wv n C x (opnd C k 1) = false := by simpa [hop, GateOp.eval] using hx
        have hyy : wv n C y (opnd C k 0) = false ∧
            wv n C y (opnd C k 1) = false := by simpa [hop, GateOp.eval] using hy
        have hj0 := ih _ ha (by omega) hxx.1 hyy.1
        have hj1 := ih _ hb (by omega) hxx.2 hyy.2
        simp [hop, GateOp.eval, hj0, hj1]

lemma crossing_of_join_true (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (x y : Fin n → Bool)
    (hx : circuitFun n C x = false) (hy : circuitFun n C y = false)
    (hjoin : circuitFun n C (fun i => x i || y i) = true) :
    ∃ k < C.gates.length, (gateAt C k).op = GateOp.and ∧ Crosses n C x y k := by
  classical
  change wv n C x C.output = false at hx
  change wv n C y C.output = false at hy
  change wv n C (fun i => x i || y i) C.output = true at hjoin
  have hout : C.output < n + C.gates.length := by
    by_contra h
    have hf := wv_missing n C (fun i => x i || y i) C.output (by omega)
    rw [hjoin] at hf
    cases hf
  by_contra hcross
  have hno : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ Crosses n C x y k := by
    intro k hk hop h
    exact hcross ⟨k, hk, hop, h⟩
  have hf := false_join_of_no_crossing n C hAO C.gates.length le_rfl x y hno
    C.output hout hx hy
  rw [hjoin] at hf
  cases hf

def isAnd (C : Circuit) (k : ℕ) : Bool :=
  match (gateAt C k).op with
  | GateOp.and => true
  | _ => false

def andSet (C : Circuit) : Finset ℕ :=
  (Finset.range C.gates.length).filter (fun k => isAnd C k = true)

lemma false_family_bound {α : Type} [Fintype α]
    (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (f : α → Fin n → Bool)
    (hfalse : ∀ a, circuitFun n C (f a) = false)
    (hjoin : ∀ a b, a ≠ b → circuitFun n C (fun i => f a i || f b i) = true) :
    Fintype.card α ≤ 2 ^ (andSet C).card := by
  classical
  let sig : α → ((andSet C) → Bool) := fun a k => wv n C (f a) (opnd C k.val 0)
  have hinj : Function.Injective sig := by
    intro a b hab
    by_contra hne
    obtain ⟨k, hk, hop, hc⟩ := crossing_of_join_true n C hAO (f a) (f b)
      (hfalse a) (hfalse b) (hjoin a b hne)
    have hkA : k ∈ andSet C := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_range.mpr hk, by simp [isAnd, hop]⟩
    have heq : wv n C (f a) (opnd C k 0) = wv n C (f b) (opnd C k 0) :=
      congrFun hab ⟨k, hkA⟩
    rcases hc with h | h
    · rw [h.1, h.2.2.1] at heq
      cases heq
    · rw [h.1, h.2.2.1] at heq
      cases heq
  have hcard := Fintype.card_le_of_injective sig hinj
  simpa only [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe] using hcard

def coreEdges : Finset (Fin 12 × Fin 8) :=
  {(0, 0), (0, 3), (0, 6), (1, 3), (1, 4), (1, 5),
   (2, 2), (2, 3), (3, 1), (3, 3), (3, 7), (4, 0),
   (4, 1), (4, 2), (5, 0), (5, 5), (6, 0), (6, 4),
   (6, 7), (7, 2), (7, 5), (7, 7), (8, 1), (8, 4),
   (9, 6), (9, 7), (10, 1), (10, 5), (10, 6),
   (11, 2), (11, 4), (11, 6)}

def coreNeighbors : Fin 20 → Finset (Fin 20) :=
  ![{12, 15, 18},
    {15, 16, 17},
    {14, 15},
    {13, 15, 19},
    {12, 13, 14},
    {12, 17},
    {12, 16, 19},
    {14, 17, 19},
    {13, 16},
    {18, 19},
    {13, 17, 18},
    {14, 16, 18},
    {0, 4, 5, 6},
    {3, 4, 8, 10},
    {2, 4, 7, 11},
    {0, 1, 2, 3},
    {1, 6, 8, 11},
    {1, 5, 7, 10},
    {0, 9, 10, 11},
    {3, 6, 7, 9}]

def coreFalseRows : Finset (Finset (Fin 20)) :=
  {{0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11},
   {1, 2, 3, 7, 8, 9, 10, 11, 12},
   {0, 1, 2, 5, 6, 7, 9, 11, 13},
   {1, 2, 7, 9, 11, 12, 13},
   {0, 1, 3, 5, 6, 8, 9, 10, 14},
   {1, 3, 8, 9, 10, 12, 14},
   {0, 1, 5, 6, 9, 13, 14},
   {1, 9, 12, 13, 14},
   {4, 5, 6, 7, 8, 9, 10, 11, 15},
   {7, 8, 9, 10, 11, 12, 15},
   {5, 6, 7, 9, 11, 13, 15},
   {7, 9, 11, 12, 13, 15},
   {5, 6, 8, 9, 10, 14, 15},
   {8, 9, 10, 12, 14, 15},
   {5, 6, 9, 13, 14, 15},
   {0, 2, 3, 4, 5, 7, 9, 10, 16},
   {2, 3, 7, 9, 10, 12, 16},
   {0, 2, 5, 7, 9, 13, 16},
   {2, 7, 9, 12, 13, 16},
   {0, 3, 5, 9, 10, 14, 16},
   {3, 9, 10, 12, 14, 16},
   {0, 5, 9, 13, 14, 16},
   {4, 5, 7, 9, 10, 15, 16},
   {7, 9, 10, 12, 15, 16},
   {5, 7, 9, 13, 15, 16},
   {7, 9, 12, 13, 15, 16},
   {5, 9, 10, 14, 15, 16},
   {9, 10, 12, 14, 15, 16},
   {5, 9, 13, 14, 15, 16},
   {0, 2, 3, 4, 6, 8, 9, 11, 17},
   {2, 3, 8, 9, 11, 12, 17},
   {0, 2, 6, 9, 11, 13, 17},
   {2, 9, 11, 12, 13, 17},
   {0, 3, 6, 8, 9, 14, 17},
   {3, 8, 9, 12, 14, 17},
   {0, 6, 9, 13, 14, 17},
   {4, 6, 8, 9, 11, 15, 17},
   {8, 9, 11, 12, 15, 17},
   {6, 9, 11, 13, 15, 17},
   {9, 11, 12, 13, 15, 17},
   {6, 8, 9, 14, 15, 17},
   {8, 9, 12, 14, 15, 17},
   {6, 9, 13, 14, 15, 17},
   {0, 2, 3, 4, 9, 16, 17},
   {2, 3, 9, 12, 16, 17},
   {0, 2, 9, 13, 16, 17},
   {2, 9, 12, 13, 16, 17},
   {0, 3, 9, 14, 16, 17},
   {3, 9, 12, 14, 16, 17},
   {0, 9, 13, 14, 16, 17},
   {4, 9, 15, 16, 17},
   {9, 12, 13, 14, 15, 16, 17},
   {1, 2, 3, 4, 5, 6, 7, 8, 18},
   {1, 2, 3, 7, 8, 12, 18},
   {1, 2, 5, 6, 7, 13, 18},
   {1, 2, 7, 12, 13, 18},
   {1, 3, 5, 6, 8, 14, 18},
   {1, 3, 8, 12, 14, 18},
   {1, 5, 6, 13, 14, 18},
   {4, 5, 6, 7, 8, 15, 18},
   {7, 8, 12, 15, 18},
   {5, 6, 7, 13, 15, 18},
   {5, 6, 8, 14, 15, 18},
   {5, 6, 13, 14, 15, 18},
   {2, 3, 4, 5, 7, 16, 18},
   {2, 3, 7, 12, 16, 18},
   {2, 5, 7, 13, 16, 18},
   {2, 7, 12, 13, 16, 18},
   {3, 5, 14, 16, 18},
   {4, 5, 7, 15, 16, 18},
   {5, 7, 13, 15, 16, 18},
   {7, 12, 13, 15, 16, 18},
   {2, 3, 4, 6, 8, 17, 18},
   {2, 3, 8, 12, 17, 18},
   {2, 6, 13, 17, 18},
   {3, 6, 8, 14, 17, 18},
   {3, 8, 12, 14, 17, 18},
   {4, 6, 8, 15, 17, 18},
   {6, 8, 14, 15, 17, 18},
   {6, 13, 14, 15, 17, 18},
   {2, 3, 4, 16, 17, 18},
   {2, 3, 12, 16, 17, 18},
   {3, 12, 14, 16, 17, 18},
   {0, 1, 2, 4, 5, 8, 10, 11, 19},
   {1, 2, 8, 10, 11, 12, 19},
   {0, 1, 2, 5, 11, 13, 19},
   {1, 2, 11, 12, 13, 19},
   {0, 1, 5, 8, 10, 14, 19},
   {1, 8, 10, 12, 14, 19},
   {0, 1, 5, 13, 14, 19},
   {4, 5, 8, 10, 11, 15, 19},
   {8, 10, 11, 12, 15, 19},
   {5, 11, 13, 15, 19},
   {5, 8, 10, 14, 15, 19},
   {8, 10, 12, 14, 15, 19},
   {0, 2, 4, 5, 10, 16, 19},
   {2, 10, 12, 16, 19},
   {0, 2, 5, 13, 16, 19},
   {0, 5, 10, 14, 16, 19},
   {0, 5, 13, 14, 16, 19},
   {4, 5, 10, 15, 16, 19},
   {5, 10, 14, 15, 16, 19},
   {10, 12, 14, 15, 16, 19},
   {0, 2, 4, 8, 11, 17, 19},
   {2, 8, 11, 12, 17, 19},
   {0, 2, 11, 13, 17, 19},
   {2, 11, 12, 13, 17, 19},
   {0, 8, 14, 17, 19},
   {4, 8, 11, 15, 17, 19},
   {8, 11, 12, 15, 17, 19},
   {11, 12, 13, 15, 17, 19},
   {0, 2, 4, 16, 17, 19},
   {0, 2, 13, 16, 17, 19},
   {0, 13, 14, 16, 17, 19},
   {1, 2, 4, 5, 8, 18, 19},
   {1, 2, 8, 12, 18, 19},
   {1, 2, 5, 13, 18, 19},
   {1, 2, 12, 13, 18, 19},
   {1, 5, 8, 14, 18, 19},
   {1, 8, 12, 14, 18, 19},
   {1, 5, 13, 14, 18, 19},
   {1, 12, 13, 14, 18, 19},
   {4, 5, 8, 15, 18, 19},
   {5, 8, 14, 15, 18, 19},
   {2, 4, 5, 16, 18, 19},
   {2, 5, 13, 16, 18, 19},
   {4, 5, 15, 16, 18, 19},
   {5, 13, 14, 15, 16, 18, 19},
   {2, 4, 8, 17, 18, 19}}


def coreGraph (x : Fin 20 → Bool) : Bool :=
  decide (∃ i j : Fin 20, j ∈ coreNeighbors i ∧ x i = true ∧ x j = true)

def rowInput (S : Finset (Fin 20)) : Fin 20 → Bool := fun i => decide (i ∈ S)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
lemma coreFalseRows_card : coreFalseRows.card = 129 := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
lemma coreRowsFalse : ∀ S : coreFalseRows, coreGraph (rowInput S.val) = false := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
lemma coreRowsClosed : ∀ S : coreFalseRows, ∀ i : Fin 20,
    i ∉ S.val → (coreNeighbors i ∩ S.val).Nonempty := by
  decide +kernel

lemma coreRowsJoin (S T : coreFalseRows) (hne : S ≠ T) :
    coreGraph (fun i => rowInput S.val i || rowInput T.val i) = true := by
  classical
  unfold coreGraph
  rw [decide_eq_true_eq]
  by_cases hST : S.val ⊆ T.val
  · have hTS : ¬ T.val ⊆ S.val := by
      intro hTS
      apply hne
      exact Subtype.ext (Finset.Subset.antisymm hST hTS)
    obtain ⟨i, hiT, hiS⟩ := Finset.not_subset.mp hTS
    obtain ⟨j, hj⟩ := coreRowsClosed S i hiS
    obtain ⟨hjN, hjS⟩ := Finset.mem_inter.mp hj
    exact ⟨i, j, hjN, by simp [rowInput, hiT], by simp [rowInput, hjS]⟩
  · obtain ⟨i, hiS, hiT⟩ := Finset.not_subset.mp hST
    obtain ⟨j, hj⟩ := coreRowsClosed T i hiT
    obtain ⟨hjN, hjT⟩ := Finset.mem_inter.mp hj
    exact ⟨i, j, hjN, by simp [rowInput, hiS], by simp [rowInput, hjT]⟩

lemma neighbors_ll : ∀ p q : Fin 12,
    Fin.castAdd 8 q ∉ coreNeighbors (Fin.castAdd 8 p) := by decide +kernel

lemma neighbors_lr : ∀ (p : Fin 12) (l : Fin 8),
    Fin.natAdd 12 l ∈ coreNeighbors (Fin.castAdd 8 p) ↔ (p, l) ∈ coreEdges := by
  decide +kernel

lemma neighbors_rl : ∀ (p : Fin 12) (l : Fin 8),
    Fin.castAdd 8 p ∈ coreNeighbors (Fin.natAdd 12 l) ↔ (p, l) ∈ coreEdges := by
  decide +kernel

lemma neighbors_rr : ∀ l k : Fin 8,
    Fin.natAdd 12 k ∉ coreNeighbors (Fin.natAdd 12 l) := by decide +kernel

lemma coreGraph_eq_incidence (x : Fin 20 → Bool) :
    coreGraph x = decide (∃ p : Fin 12, ∃ l : Fin 8, (p, l) ∈ coreEdges ∧
      x (Fin.castAdd 8 p) = true ∧ x (Fin.natAdd 12 l) = true) := by
  unfold coreGraph
  congr 1
  apply propext
  constructor
  · rintro ⟨i, j, hij, hi, hj⟩
    cases i using (Fin.addCases (m := 12) (n := 8)) <;>
      cases j using (Fin.addCases (m := 12) (n := 8))
    · exact False.elim (neighbors_ll _ _ hij)
    · exact ⟨_, _, (neighbors_lr _ _).mp hij, hi, hj⟩
    · exact ⟨_, _, (neighbors_rl _ _).mp hij, hj, hi⟩
    · exact False.elim (neighbors_rr _ _ hij)
  · rintro ⟨p, l, he, hp, hl⟩
    exact ⟨Fin.castAdd 8 p, Fin.natAdd 12 l, (neighbors_lr p l).mpr he, hp, hl⟩

theorem core_and_at_least_eight (C : Circuit) (hAO : IsAO2 20 C)
    (hfun : ∀ x : Fin 20 → Bool, circuitFun 20 C x =
      decide (∃ p : Fin 12, ∃ l : Fin 8, (p, l) ∈ coreEdges ∧
        x (Fin.castAdd 8 p) = true ∧ x (Fin.natAdd 12 l) = true)) :
    8 ≤ (andSet C).card := by
  have hcompute (x : Fin 20 → Bool) : circuitFun 20 C x = coreGraph x := by
    rw [hfun, coreGraph_eq_incidence]
  have hc := false_family_bound 20 C hAO (fun S : coreFalseRows => rowInput S.val)
    (fun S => by rw [hcompute]; exact coreRowsFalse S)
    (fun S T hne => by rw [hcompute]; exact coreRowsJoin S T hne)
  have hb : 129 ≤ 2 ^ (andSet C).card := by
    simpa only [Fintype.card_coe, coreFalseRows_card] using hc
  by_contra h
  have hle : (andSet C).card ≤ 7 := by omega
  have hp : 2 ^ (andSet C).card ≤ 2 ^ 7 :=
    (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mpr hle
  norm_num at hp
  omega

end AndCrossing

end PEqualNP.Outside.L_meta_2583
