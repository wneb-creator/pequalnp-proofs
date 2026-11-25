import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4970_aux.MergeCharge

def mergeLabel {α : Type*} (f : α → Nat) (a b : Nat) : α → Nat :=
  fun x => if f x = b then a else f x

def Monochromatic {α : Type*} (f : α → Nat) (S : Finset α) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, f x = f y

theorem merge_preserves {α : Type*} (f : α → Nat) (a b : Nat) (S : Finset α)
    (h : Monochromatic f S) : Monochromatic (mergeLabel f a b) S := by
  intro x hx y hy
  simp only [mergeLabel, h x hx y hy]

theorem merge_union {α : Type*} [DecidableEq α] (f : α → Nat) (A B : Finset α)
    (x y : α) (hx : x ∈ A) (hy : y ∈ B)
    (hA : Monochromatic f A) (hB : Monochromatic f B) :
    Monochromatic (mergeLabel f (f x) (f y)) (A ∪ B) := by
  have hval : ∀ z ∈ A ∪ B, mergeLabel f (f x) (f y) z = f x := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · rw [mergeLabel, hA z hz x hx]
      split_ifs <;> rfl
    · simp [mergeLabel, hB z hz y hy]
  intro u hu v hv
  exact (hval u hu).trans (hval v hv).symm

theorem merge_card {α : Type*} [DecidableEq α] (f : α → Nat)
    (S : Finset α) (a b : Nat) :
    (S.image f).card ≤ (S.image (mergeLabel f a b)).card + 1 := by
  have hs : S.image f ⊆ insert b (S.image (mergeLabel f a b)) := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    by_cases he : f x = b
    · simp [he]
    · apply Finset.mem_insert_of_mem
      exact Finset.mem_image.mpr ⟨x, hx, by simp [mergeLabel, he]⟩
  exact (Finset.card_le_card hs).trans (Finset.card_insert_le _ _)

def mergeList {α : Type*} : List (Nat × Nat) → (α → Nat) → (α → Nat)
  | [], f => f
  | (a,b) :: es, f => mergeList es (mergeLabel f a b)

theorem mergeList_card {α : Type*} [DecidableEq α] (es : List (Nat × Nat))
    (f : α → Nat) (S : Finset α) :
    (S.image f).card ≤ (S.image (mergeList es f)).card + es.length := by
  induction es generalizing f with
  | nil => simp [mergeList]
  | cons e es ih =>
    have h1 := merge_card f S e.1 e.2
    have h2 := ih (mergeLabel f e.1 e.2)
    simp only [mergeList, List.length_cons]
    omega

theorem connected_cost {n : Nat} (S : Finset (Fin n)) (es : List (Nat × Nat))
    (h : Monochromatic (mergeList es Fin.val) S) : S.card ≤ es.length + 1 := by
  by_cases hn : S.Nonempty
  · obtain ⟨x, hx⟩ := hn
    have hs : S.image (mergeList es Fin.val) ⊆ {mergeList es Fin.val x} := by
      intro z hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_singleton.mpr (h y hy x hx)
    have hcard : (S.image (mergeList es Fin.val)).card ≤ 1 := by
      simpa using Finset.card_le_card hs
    have hb := mergeList_card es Fin.val S
    rw [Finset.card_image_of_injective _ Fin.val_injective] at hb
    omega
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp [he]

end PEqualNP.Outside.L_meta_4970_aux.MergeCharge

namespace PEqualNP.Outside.L_meta_4970_aux.OrCharge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4970_aux.MergeCharge

def scan {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α) : List α :=
  gs.foldl (fun w g => w ++ [step w g]) w

lemma scan_cons {α : Type} (step : List α → Gate → α) (g : Gate) (gs : List Gate) (w : List α) :
    scan step (g :: gs) w = scan step gs (w ++ [step w g]) := rfl

lemma scan_append {α : Type} (step : List α → Gate → α) (gs hs : List Gate) (w : List α) :
    scan step (gs ++ hs) w = scan step hs (scan step gs w) := by
  simp [scan, List.foldl_append]

lemma scan_length {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α) :
    (scan step gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [scan_cons, ih]
    simp
    omega

lemma scan_prefix {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α)
    (d : α) (i : ℕ) (hi : i < w.length) :
    (scan step gs w).getD i d = w.getD i d := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [scan_cons, ih _ (by simp; omega)]
    exact List.getD_append _ _ _ _ hi

lemma scan_gate {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α)
    (d : α) (j : ℕ) (hj : j < gs.length)
    (hstep : ∀ p p' : List α, (∀ i < w.length + j, p.getD i d = p'.getD i d) →
      step p gs[j] = step p' gs[j]) :
    (scan step gs w).getD (w.length + j) d = step (scan step gs w) gs[j] := by
  let pre := scan step (gs.take j) w
  have hp : pre.length = w.length + j := by
    simp [pre, scan_length, Nat.min_eq_left hj.le]
  have hs : scan step gs w = scan step (gs[j] :: gs.drop (j + 1)) pre := by
    have hsplit := List.take_append_drop j gs
    conv_lhs => rw [← hsplit, scan_append, List.drop_eq_getElem_cons hj]
  have hpre : ∀ i < w.length + j, (scan step gs w).getD i d = pre.getD i d := by
    intro i hi
    rw [hs]
    exact scan_prefix step (gs[j] :: gs.drop (j + 1)) pre d i (by omega)
  have hres : (scan step gs w).getD (w.length + j) d = step pre gs[j] := by
    rw [hs, scan_cons, scan_prefix step (gs.drop (j + 1)) (pre ++ [step pre gs[j]]) d (w.length + j) (by simp [hp])]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    have hsub : w.length + j - pre.length = 0 := by omega
    rw [hsub]
    simp only [List.getD_cons_zero]
  rw [hres]
  exact hstep pre (scan step gs w) (fun i hi => (hpre i hi).symm)

def boolStep (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

lemma wires_eq_scan (C : Circuit) (x : List Bool) :
    C.wires x = scan boolStep C.gates x := rfl

lemma list_eq_two {l : List ℕ} (hl : l.length = 2) : l = [l.getD 0 0, l.getD 1 0] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;> simp at hl ⊢

lemma gateAt_eq_getElem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt, hj]

lemma ao2_gate_props {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
    (gateAt C j).inputs = [opnd C j 0, opnd C j 1] ∧
    opnd C j 0 < n + j ∧ opnd C j 1 < n + j := by
  have hmem : C.gates[j] ∈ C.gates := List.getElem_mem hj
  have hop : (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or := by
    rw [gateAt_eq_getElem hj]
    exact hAO2.1 C.gates[j] hmem
  have hlen : (gateAt C j).inputs.length = 2 := by
    rw [gateAt_eq_getElem hj]
    exact hAO2.2.2 C.gates[j] hmem
  have hin : (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
    simpa [opnd] using list_eq_two hlen
  have hrb := hAO2.2.1 j hj
  have h0 : opnd C j 0 < n + j := hrb (opnd C j 0) (by rw [hin]; simp)
  have h1 : opnd C j 1 < n + j := hrb (opnd C j 1) (by rw [hin]; simp)
  exact ⟨hop, hin, h0, h1⟩

def wireVal (n : ℕ) (C : Circuit) (w : ℕ) (x : Fin n → Bool) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma wireVal_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq_scan, scan_length, List.length_ofFn]

lemma wireVal_ge (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : n + C.gates.length ≤ w) :
    wireVal n C w x = false := by
  rw [wireVal, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [wireVal_length]; exact hw)]
  rfl

lemma wireVal_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    wireVal n C i x = x ⟨i, hi⟩ := by
  rw [wireVal, wires_eq_scan, scan_prefix boolStep C.gates (List.ofFn x) false i (by simp [hi])]
  rw [List.getD_eq_getElem _ _ (by simp [hi]), List.getElem_ofFn]

lemma wireVal_gate {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) :
    wireVal n C (n + j) x = boolStep (C.wires (List.ofFn x)) C.gates[j] := by
  rw [wireVal, wires_eq_scan]
  have hlen : (List.ofFn x).length = n := List.length_ofFn
  have h := scan_gate boolStep C.gates (List.ofFn x) false j hj (by
    intro q1 q2 hq
    simp only [boolStep]
    have hrb := hAO2.2.1 j hj
    have hcongr : C.gates[j].inputs.map (fun i => q1.getD i false) =
        C.gates[j].inputs.map (fun i => q2.getD i false) := by
      apply List.map_congr_left
      intro i hi
      apply hq
      rw [hlen]
      exact hrb i (by rw [gateAt_eq_getElem hj]; exact hi)
    rw [hcongr])
  simpa only [hlen] using h

lemma wireVal_or {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) :
    wireVal n C (n + j) x = (wireVal n C (opnd C j 0) x || wireVal n C (opnd C j 1) x) := by
  rw [wireVal_gate hAO2 x hj]
  have ⟨_, hin, _, _⟩ := ao2_gate_props hAO2 hj
  rw [gateAt_eq_getElem hj] at hop hin
  simp [boolStep, hop, hin, GateOp.eval, wireVal]

lemma wireVal_and {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) :
    wireVal n C (n + j) x = (wireVal n C (opnd C j 0) x && wireVal n C (opnd C j 1) x) := by
  rw [wireVal_gate hAO2 x hj]
  have ⟨_, hin, _, _⟩ := ao2_gate_props hAO2 hj
  rw [gateAt_eq_getElem hj] at hop hin
  simp [boolStep, hop, hin, GateOp.eval, wireVal]

lemma scan_bool_mono (gs : List Gate) (hAO : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (lx ly : List Bool) (hlen : lx.length = ly.length)
    (hle : ∀ i, lx.getD i false = true → ly.getD i false = true) :
    (scan boolStep gs lx).length = (scan boolStep gs ly).length ∧
      ∀ w, (scan boolStep gs lx).getD w false = true → (scan boolStep gs ly).getD w false = true := by
  induction gs generalizing lx ly with
  | nil => exact ⟨hlen, hle⟩
  | cons g gs ih =>
    have hg : g.op = GateOp.and ∨ g.op = GateOp.or := hAO g (by simp)
    have hgs : ∀ g' ∈ gs, g'.op = GateOp.and ∨ g'.op = GateOp.or := fun g' hg' => hAO g' (by simp [hg'])
    have hstep : boolStep lx g = true → boolStep ly g = true := by
      intro h
      rcases hg with hop | hop
      · simp only [boolStep, hop, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply] at h ⊢
        intro i hi
        exact hle i (h i hi)
      · simp only [boolStep, hop, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply] at h ⊢
        rcases h with ⟨i, hi, hit⟩
        exact ⟨i, hi, hle i hit⟩
    have hlen' : (lx ++ [boolStep lx g]).length = (ly ++ [boolStep ly g]).length := by
      simp [hlen]
    have hle' : ∀ i, (lx ++ [boolStep lx g]).getD i false = true →
        (ly ++ [boolStep ly g]).getD i false = true := by
      intro i hi
      by_cases hil : i < lx.length
      · rw [List.getD_append _ _ _ _ hil] at hi
        rw [List.getD_append _ _ _ _ (by omega)]
        exact hle i hi
      · by_cases heq : i = lx.length
        · subst heq
          rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero] at hi
          rw [hlen, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
          exact hstep hi
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)] at hi
          simp at hi
    exact ih hgs (lx ++ [boolStep lx g]) (ly ++ [boolStep ly g]) hlen' hle'

lemma wireVal_mono {n : ℕ} {C : Circuit} (hAO : AndOrOnly C) {x y : Fin n → Bool}
    (hxy : ∀ i : Fin n, x i = true → y i = true) (w : ℕ) :
    wireVal n C w x = true → wireVal n C w y = true := by
  have hle : ∀ i, (List.ofFn x).getD i false = true → (List.ofFn y).getD i false = true := by
    intro i hi
    by_cases hin : i < n
    · rw [List.getD_eq_getElem _ _ (by simp [hin]), List.getElem_ofFn] at hi ⊢
      exact hxy ⟨i, hin⟩ hi
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)] at hi
      simp at hi
  exact (scan_bool_mono C.gates hAO (List.ofFn x) (List.ofFn y) (by simp) hle).2 w

noncomputable section BS

open Finset Classical

def Clean {n : ℕ} (S : Finset (Fin n)) (g : (Fin n → Bool) → Bool) : Prop :=
  ∀ x, g x = true → ∃ a ∈ S, x a = true

def single {n : ℕ} (a : Fin n) : Fin n → Bool := fun v => decide (v = a)

def Tset {n : ℕ} (g : (Fin n → Bool) → Bool) : Finset (Fin n) :=
  univ.filter fun a => g (single a) = true

lemma mem_Tset {n : ℕ} {g : (Fin n → Bool) → Bool} {a : Fin n} :
    a ∈ Tset g ↔ g (single a) = true := by
  simp [Tset]

lemma Clean.Tset_subset {n : ℕ} {S : Finset (Fin n)} {g : (Fin n → Bool) → Bool}
    (h : Clean S g) : Tset g ⊆ S := by
  intro a ha
  obtain ⟨b, hb, hx⟩ := h _ (mem_Tset.mp ha)
  have : b = a := by simpa [single] using hx
  exact this ▸ hb

variable {n : ℕ} {C : Circuit}

lemma wv_or (hA : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (x : Fin n → Bool) :
    wireVal n C (n + j) x = true ↔
      wireVal n C (opnd C j 0) x = true ∨ wireVal n C (opnd C j 1) x = true := by
  rw [wireVal_or hA x hj hop, Bool.or_eq_true]

lemma wv_and (hA : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) (x : Fin n → Bool) :
    wireVal n C (n + j) x = true ↔
      wireVal n C (opnd C j 0) x = true ∧ wireVal n C (opnd C j 1) x = true := by
  rw [wireVal_and hA x hj hop, Bool.and_eq_true]

lemma or_clean (hA : IsAO2 n C) {S : Finset (Fin n)} {j : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hc : Clean S (wireVal n C (n + j))) :
    Clean S (wireVal n C (opnd C j 0)) ∧ Clean S (wireVal n C (opnd C j 1)) :=
  ⟨fun x hx => hc x ((wv_or hA hj hop x).mpr (Or.inl hx)),
    fun x hx => hc x ((wv_or hA hj hop x).mpr (Or.inr hx))⟩

lemma and_clean (hA : IsAO2 n C) {S : Finset (Fin n)} {j : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) (hc : Clean S (wireVal n C (n + j))) :
    Clean S (wireVal n C (opnd C j 0)) ∨ Clean S (wireVal n C (opnd C j 1)) := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  simp only [Clean, not_forall] at h1 h2
  obtain ⟨x1, hx1, n1⟩ := h1
  obtain ⟨x2, hx2, n2⟩ := h2
  have l1 : ∀ i : Fin n, x1 i = true → (fun v => x1 v || x2 v) i = true :=
    fun v hv => by simp [hv]
  have l2 : ∀ i : Fin n, x2 i = true → (fun v => x1 v || x2 v) i = true :=
    fun v hv => by simp [hv]
  obtain ⟨a, ha, hxa⟩ := hc (fun v => x1 v || x2 v) ((wv_and hA hj hop _).mpr
    ⟨wireVal_mono hA.1 l1 _ hx1, wireVal_mono hA.1 l2 _ hx2⟩)
  simp only [Bool.or_eq_true] at hxa
  rcases hxa with h' | h'
  · exact n1 ⟨a, ha, h'⟩
  · exact n2 ⟨a, ha, h'⟩

lemma T_or (hA : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) :
    Tset (wireVal n C (n + j)) ⊆
      Tset (wireVal n C (opnd C j 0)) ∪ Tset (wireVal n C (opnd C j 1)) := by
  intro a ha
  rw [mem_union, mem_Tset, mem_Tset]
  exact (wv_or hA hj hop _).mp (mem_Tset.mp ha)

lemma T_and_left (hA : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) :
    Tset (wireVal n C (n + j)) ⊆ Tset (wireVal n C (opnd C j 0)) :=
  fun _ ha => mem_Tset.mpr ((wv_and hA hj hop _).mp (mem_Tset.mp ha)).1

lemma T_and_right (hA : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) :
    Tset (wireVal n C (n + j)) ⊆ Tset (wireVal n C (opnd C j 1)) :=
  fun _ ha => mem_Tset.mpr ((wv_and hA hj hop _).mp (mem_Tset.mp ha)).2

lemma two_is_gate {w : ℕ} (h2 : 2 ≤ (Tset (wireVal n C w)).card) :
    ∃ j, j < C.gates.length ∧ w = n + j := by
  by_cases h1 : w < n
  · exfalso
    have hsub : Tset (wireVal n C w) ⊆ {⟨w, h1⟩} := by
      intro a ha
      have h := mem_Tset.mp ha
      rw [wireVal_input n C _ w h1] at h
      simp only [single, decide_eq_true_eq] at h
      exact mem_singleton.mpr h.symm
    have := card_le_card hsub
    simp at this
    omega
  · by_cases h3 : n + C.gates.length ≤ w
    · exfalso
      have he : Tset (wireVal n C w) = ∅ := by
        ext a
        simp [mem_Tset, wireVal_ge n C _ w h3]
      rw [he] at h2
      simp at h2
    · exact ⟨w - n, by omega, by omega⟩


end BS

open Finset Classical

lemma mono_subset {α : Type*} {f : α → Nat} {A B : Finset α}
    (hf : Monochromatic f B) (hAB : A ⊆ B) : Monochromatic f A :=
  fun x hx y hy => hf x (hAB hx) y (hAB hy)

lemma mono_small {α : Type*} [DecidableEq α] (f : α → Nat) (A : Finset α)
    (hA : A.card ≤ 1) : Monochromatic f A := by
  intro x hx y hy
  exact congrArg f (Finset.card_le_one.mp hA x hx y hy)

lemma mergeList_append {α : Type*} (es ts : List (Nat × Nat)) (f : α → Nat) :
    mergeList (es ++ ts) f = mergeList ts (mergeList es f) := by
  induction es generalizing f with
  | nil => rfl
  | cons e es ih => simpa only [List.cons_append, mergeList] using ih (mergeLabel f e.1 e.2)

noncomputable def charged {n : Nat} (C : Circuit) (S : Finset (Fin n)) (k : Nat) : Finset Nat := by
  classical
  exact (range k).filter fun j => (gateAt C j).op = GateOp.or ∧
    Clean S (wireVal n C (n + j)) ∧ 2 ≤ (Tset (wireVal n C (n + j))).card

lemma charged_card_succ {n : Nat} (C : Circuit) (S : Finset (Fin n)) (k : Nat) :
    (charged C S (k + 1)).card = (charged C S k).card +
      if (gateAt C k).op = GateOp.or ∧ Clean S (wireVal n C (n + k)) ∧
        2 ≤ (Tset (wireVal n C (n + k))).card then 1 else 0 := by
  classical
  by_cases h : (gateAt C k).op = GateOp.or ∧ Clean S (wireVal n C (n + k)) ∧
    2 ≤ (Tset (wireVal n C (n + k))).card
  · simp [charged, Finset.range_add_one, Finset.filter_insert, h]
  · simp [charged, Finset.range_add_one, Finset.filter_insert, h]

theorem labels_exist {n : Nat} {C : Circuit} (hA : IsAO2 n C) (S : Finset (Fin n))
    (k : Nat) (hk : k ≤ C.gates.length) :
    ∃ es : List (Nat × Nat), es.length ≤ (charged C S k).card ∧
      ∀ w < n + k, Clean S (wireVal n C w) →
        Monochromatic (mergeList es Fin.val) (Tset (wireVal n C w)) := by
  classical
  induction k with
  | zero =>
    refine ⟨[], by simp [charged], ?_⟩
    intro w hw hc
    apply mono_small
    apply Finset.card_le_one.mpr
    intro a ha b hb
    have ea := mem_Tset.mp ha
    have eb := mem_Tset.mp hb
    rw [wireVal_input n C _ w (by omega)] at ea eb
    have ea' : (⟨w, by omega⟩ : Fin n) = a := of_decide_eq_true ea
    have eb' : (⟨w, by omega⟩ : Fin n) = b := of_decide_eq_true eb
    exact ea'.symm.trans eb'
  | succ k ih =>
    obtain ⟨es, hes, hm⟩ := ih (by omega)
    have hj : k < C.gates.length := by omega
    obtain ⟨hop, _, h0, h1⟩ := ao2_gate_props hA hj
    have extend (ts : List (Nat × Nat))
        (hold : ∀ w < n + k, Clean S (wireVal n C w) →
          Monochromatic (mergeList ts Fin.val) (Tset (wireVal n C w)))
        (hnew : Clean S (wireVal n C (n + k)) →
          Monochromatic (mergeList ts Fin.val) (Tset (wireVal n C (n + k)))) :
        ∀ w < n + (k + 1), Clean S (wireVal n C w) →
          Monochromatic (mergeList ts Fin.val) (Tset (wireVal n C w)) := by
      intro w hw hc
      by_cases he : w < n + k
      · exact hold w he hc
      · have heq : w = n + k := by omega
        subst w
        exact hnew hc
    by_cases hgood : (gateAt C k).op = GateOp.or ∧ Clean S (wireVal n C (n + k)) ∧
        2 ≤ (Tset (wireVal n C (n + k))).card
    · obtain ⟨hor, hc, hlarge⟩ := hgood
      obtain ⟨cl, cr⟩ := or_clean hA hj hor hc
      have ml := hm _ h0 cl
      have mr := hm _ h1 cr
      have hcount : (charged C S (k + 1)).card = (charged C S k).card + 1 := by
        rw [charged_card_succ]
        simp [hor, hc, hlarge]
      by_cases hl : (Tset (wireVal n C (opnd C k 0))).Nonempty
      · by_cases hr : (Tset (wireVal n C (opnd C k 1))).Nonempty
        · obtain ⟨a, ha⟩ := hl
          obtain ⟨b, hb⟩ := hr
          let f : Fin n → Nat := mergeList es Fin.val
          let ts := es ++ [(f a, f b)]
          have hts : mergeList ts Fin.val = mergeLabel f (f a) (f b) := by
            simp [ts, mergeList_append, mergeList, f]
          refine ⟨ts, ?_, extend ts ?_ ?_⟩
          · simp only [ts, List.length_append, List.length_cons, List.length_nil]
            omega
          · intro w hw hc'
            rw [hts]
            exact merge_preserves f (f a) (f b) _ (hm w hw hc')
          · intro _
            rw [hts]
            exact mono_subset (merge_union f _ _ a b ha hb ml mr) (T_or hA hj hor)
        · refine ⟨es, by omega, extend es hm ?_⟩
          intro _
          apply mono_subset ml
          have he : Tset (wireVal n C (opnd C k 1)) = ∅ := not_nonempty_iff_eq_empty.mp hr
          simpa [he] using T_or hA hj hor
      · refine ⟨es, by omega, extend es hm ?_⟩
        intro _
        apply mono_subset mr
        have he : Tset (wireVal n C (opnd C k 0)) = ∅ := not_nonempty_iff_eq_empty.mp hl
        simpa [he] using T_or hA hj hor
    · have hcount : (charged C S (k + 1)).card = (charged C S k).card := by
        rw [charged_card_succ]
        simp [hgood]
      refine ⟨es, by omega, extend es hm ?_⟩
      intro hc
      rcases hop with hand | hor
      · rcases and_clean hA hj hand hc with cl | cr
        · exact mono_subset (hm _ h0 cl) (T_and_left hA hj hand)
        · exact mono_subset (hm _ h1 cr) (T_and_right hA hj hand)
      · apply mono_small
        have : ¬ 2 ≤ (Tset (wireVal n C (n + k))).card := fun h => hgood ⟨hor, hc, h⟩
        omega

theorem component_charge {n : Nat} {C : Circuit} (hA : IsAO2 n C) (S : Finset (Fin n)) :
    ∃ f : Fin n → Nat,
      S.card ≤ (S.image f).card + (charged C S C.gates.length).card ∧
      ∀ w < n + C.gates.length, Clean S (wireVal n C w) →
        Monochromatic f (Tset (wireVal n C w)) := by
  obtain ⟨es, hes, hm⟩ := labels_exist hA S C.gates.length le_rfl
  refine ⟨mergeList es Fin.val, ?_, hm⟩
  have h := mergeList_card es Fin.val S
  rw [Finset.card_image_of_injective _ Fin.val_injective] at h
  omega

lemma charged_disjoint {n : Nat} {C : Circuit} {κ : Type*} [Fintype κ]
    (S : κ → Finset (Fin n))
    (hdisj : ∀ c c', c ≠ c' → (S c ∩ S c').card ≤ 1) :
    ∀ c ∈ (univ : Finset κ), ∀ c' ∈ (univ : Finset κ), c ≠ c' →
      Disjoint (charged C (S c) C.gates.length) (charged C (S c') C.gates.length) := by
  classical
  intro c _ c' _ hne
  rw [Finset.disjoint_left]
  intro j hj hj'
  obtain ⟨_, _, hc, hlarge⟩ := Finset.mem_filter.mp hj
  obtain ⟨_, _, hc', _⟩ := Finset.mem_filter.mp hj'
  have hs : Tset (wireVal n C (n + j)) ⊆ S c ∩ S c' :=
    fun a ha => mem_inter.mpr ⟨hc.Tset_subset ha, hc'.Tset_subset ha⟩
  have h1 := card_le_card hs
  have h2 := hdisj c c' hne
  omega

noncomputable def orGates (C : Circuit) : Finset Nat :=
  (range C.gates.length).filter fun j => (gateAt C j).op = GateOp.or

lemma sum_charged_le {n : Nat} {C : Circuit} {κ : Type*} [Fintype κ]
    (S : κ → Finset (Fin n))
    (hdisj : ∀ c c', c ≠ c' → (S c ∩ S c').card ≤ 1) :
    ∑ c, (charged C (S c) C.gates.length).card ≤ (orGates C).card := by
  classical
  rw [← card_biUnion (charged_disjoint S hdisj)]
  apply card_le_card
  intro j hj
  obtain ⟨c, _, hc⟩ := mem_biUnion.mp hj
  obtain ⟨hr, hor, _⟩ := mem_filter.mp hc
  exact mem_filter.mpr ⟨hr, hor⟩

theorem family_component_charge {n : Nat} {C : Circuit} (hA : IsAO2 n C)
    {κ : Type*} [Fintype κ] (S : κ → Finset (Fin n))
    (hdisj : ∀ c c', c ≠ c' → (S c ∩ S c').card ≤ 1) :
    ∃ f : κ → Fin n → Nat,
      (∀ c, ∀ w < n + C.gates.length, Clean (S c) (wireVal n C w) →
        Monochromatic (f c) (Tset (wireVal n C w))) ∧
      ∑ c, (S c).card ≤ (∑ c, ((S c).image (f c)).card) + (orGates C).card := by
  classical
  choose f hc hm using fun c => component_charge hA (S c)
  refine ⟨f, hm, ?_⟩
  calc ∑ c, (S c).card
      ≤ ∑ c, (((S c).image (f c)).card + (charged C (S c) C.gates.length).card) :=
        sum_le_sum fun c _ => hc c
    _ = (∑ c, ((S c).image (f c)).card) + ∑ c, (charged C (S c) C.gates.length).card :=
      sum_add_distrib
    _ ≤ (∑ c, ((S c).image (f c)).card) + (orGates C).card :=
      Nat.add_le_add_left (sum_charged_le S hdisj) _

lemma pure_or_tset {n : Nat} (g : (Fin n → Bool) → Bool) (Q : Finset (Fin n))
    (hg : ∀ x, g x = decide (∃ i ∈ Q, x i = true)) : Tset g = Q := by
  classical
  ext i
  rw [mem_Tset, hg]
  simp [single]

lemma pure_or_clean {n : Nat} (g : (Fin n → Bool) → Bool) (Q S : Finset (Fin n))
    (hQS : Q ⊆ S) (hg : ∀ x, g x = decide (∃ i ∈ Q, x i = true)) : Clean S g := by
  intro x hx
  rw [hg] at hx
  obtain ⟨i, hi, hxi⟩ := of_decide_eq_true hx
  exact ⟨i, hQS hi, hxi⟩

end PEqualNP.Outside.L_meta_4970_aux.OrCharge
