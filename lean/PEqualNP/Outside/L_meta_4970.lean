import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4970.SemanticSupport

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.BlindGate

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (U V : List Bool) (h : ∀ i, U.getD i false = true → V.getD i false = true) :
    op.eval (ins.map fun i => U.getD i false) = true →
    op.eval (ins.map fun i => V.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun hall i hi => h i (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, hv⟩ => ⟨i, hi, h i hv⟩

theorem ofFn_mono (n : ℕ) (x y : Fin n → Bool) (hxy : ∀ v : Fin n, x v = true → y v = true)
    (w : ℕ) : (List.ofFn x).getD w false = true → (List.ofFn y).getD w false = true := by
  by_cases hw : w < n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, dite_true, Option.getD_some]
    exact hxy ⟨w, hw⟩
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp


theorem mono2 (gs : List Gate)
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

lemma wire_mono (n : ℕ) (C : Circuit) (hC : IsAO2 n C) (w : ℕ) :
    Monotone (fun x : Fin n → Bool => wireValue C n x w) := by
  intro x y hxy
  change (wf C.gates (List.ofFn x)).getD w false ≤ (wf C.gates (List.ofFn y)).getD w false
  rw [Bool.le_iff_imp]
  refine mono2 C.gates (fun g hg => ⟨hC.1 g hg, le_of_eq (hC.2.2 g hg)⟩)
    _ _ (by simp) ?_ w
  intro i
  apply ofFn_mono n x y _ i
  intro v hv
  exact (Bool.le_iff_imp.mp (hxy v)) hv

lemma support_of_false_complement (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (S : Finset (Fin n)) (w : ℕ)
    (hz : wireValue C n (fun i => decide (i ∉ S)) w = false) :
    (Finset.univ.filter fun i : Fin n =>
      wireValue C n (fun k => decide (k = i)) w = true) ⊆ S := by
  intro i hi
  by_contra hn
  have hx : (fun k : Fin n => decide (k = i)) ≤ (fun k => decide (k ∉ S)) := by
    intro k
    rw [Bool.le_iff_imp]
    intro hk
    have hki : k = i := of_decide_eq_true hk
    subst k
    exact decide_eq_true hn
  have hm := wire_mono n C hC w hx
  have hit : wireValue C n (fun k => decide (k = i)) w = true :=
    (Finset.mem_filter.mp hi).2
  dsimp only at hm
  rw [hit, hz] at hm
  exact Bool.false_ne_true ((Bool.le_iff_imp.mp hm) rfl)

lemma below_disjunction_iff (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (S : Finset (Fin n)) (w : ℕ) :
    wireValue C n (fun i => decide (i ∉ S)) w = false ↔
    ∀ x : Fin n → Bool, wireValue C n x w = true → ∃ i ∈ S, x i = true := by
  constructor
  · intro hz x hx
    by_contra hn
    have hle : x ≤ (fun i => decide (i ∉ S)) := by
      intro i
      rw [Bool.le_iff_imp]
      intro hi
      exact decide_eq_true (fun his => hn ⟨i, his, hi⟩)
    have hm := wire_mono n C hC w hle
    dsimp only at hm
    rw [hx, hz] at hm
    exact Bool.false_ne_true ((Bool.le_iff_imp.mp hm) rfl)
  · intro h
    cases he : wireValue C n (fun i => decide (i ∉ S)) w
    · rfl
    · obtain ⟨i, his, hi⟩ := h _ he
      have hin : i ∉ S := of_decide_eq_true hi
      exact False.elim (hin his)

end PEqualNP.Outside.L_meta_4970.SemanticSupport

namespace PEqualNP.Outside.L_meta_4970.SupportAccounting

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.CircuitMoves

def wireStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_wireStep_length (gs : List Gate) (acc : List Bool) :
    (gs.foldl wireStep acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, wireStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_wireStep_prefix (gs : List Gate) (acc : List Bool) (w : ℕ) (hw : w < acc.length) :
    (gs.foldl wireStep acc).getD w false = acc.getD w false := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    have hw' : w < (wireStep acc g).length := by
      simp only [wireStep, List.length_append, List.length_singleton]
      omega
    rw [List.foldl_cons, ih (wireStep acc g) hw']
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    simp only [wireStep, List.getElem?_append_left hw]

lemma gateAt_eq_getElem (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    gateAt C k = C.gates[k] := by
  unfold gateAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  rfl

lemma wireValue_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    PEqualNP.BlindGate.wireValue C n x w = x ⟨w, hw⟩ := by
  unfold PEqualNP.BlindGate.wireValue Circuit.wires
  have hw' : w < (List.ofFn x).length := by simp [hw]
  have h1 := foldl_wireStep_prefix C.gates (List.ofFn x) w hw'
  change (C.gates.foldl wireStep (List.ofFn x)).getD w false = x ⟨w, hw⟩
  rw [h1, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hw']
  simp

lemma wireValue_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ)
    (hk : k < C.gates.length) (hRB : ReadsBack n C) :
    PEqualNP.BlindGate.wireValue C n x (n + k) =
      (gateAt C k).op.eval ((gateAt C k).inputs.map fun u => PEqualNP.BlindGate.wireValue C n x u) := by
  have hsplit : C.gates = C.gates.take k ++ [C.gates[k]] ++ C.gates.drop (k + 1) := by
    have h1 := List.take_append_drop k C.gates
    have h2 : C.gates.drop k = C.gates[k] :: C.gates.drop (k + 1) := List.drop_eq_getElem_cons hk
    rw [h2] at h1
    simp only [List.append_assoc, List.singleton_append, h1]
  set acc := (C.gates.take k).foldl wireStep (List.ofFn x) with hacc
  have hacc_len : acc.length = n + k := by
    rw [hacc, foldl_wireStep_length, List.length_ofFn, List.length_take]
    omega
  have hpref : ∀ u < n + k, PEqualNP.BlindGate.wireValue C n x u = acc.getD u false := by
    intro u hu
    unfold PEqualNP.BlindGate.wireValue Circuit.wires
    change (C.gates.foldl wireStep (List.ofFn x)).getD u false = acc.getD u false
    conv_lhs => rw [← List.take_append_drop k C.gates]
    rw [List.foldl_append, ← hacc]
    exact foldl_wireStep_prefix (C.gates.drop k) acc u (by omega)
  have hval : PEqualNP.BlindGate.wireValue C n x (n + k) =
      C.gates[k].op.eval (C.gates[k].inputs.map fun u => acc.getD u false) := by
    unfold PEqualNP.BlindGate.wireValue Circuit.wires
    change (C.gates.foldl wireStep (List.ofFn x)).getD (n + k) false = _
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_append, ← hacc, List.foldl_cons, List.foldl_nil]
    have hlen : n + k < (wireStep acc C.gates[k]).length := by
      simp only [wireStep, List.length_append, List.length_singleton]
      omega
    rw [foldl_wireStep_prefix (C.gates.drop (k + 1)) (wireStep acc C.gates[k]) (n + k) hlen]
    rw [List.getD_eq_getElem?_getD]
    simp only [wireStep, List.getElem?_append_right (by omega : acc.length ≤ n + k),
      hacc_len, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  rw [hval, gateAt_eq_getElem C k hk]
  congr 1
  apply List.map_congr_left
  intro u hu
  rw [← gateAt_eq_getElem C k hk] at hu
  exact (hpref u (hRB k hk u hu)).symm

lemma list_eq_two {α : Type} {l : List α} (h : l.length = 2) : ∃ a b, l = [a, b] := by
  cases l with
  | nil => simp at h
  | cons a t =>
    cases t with
    | nil => simp at h
    | cons b t2 =>
      cases t2 with
      | nil => exact ⟨a, b, rfl⟩
      | cons _ _ => simp at h

lemma gate_inputs_two (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (j : ℕ) (hj : j < C.gates.length) :
    ∃ a b, (gateAt C j).inputs = [a, b] ∧ a < n + j ∧ b < n + j := by
  have hlen : (gateAt C j).inputs.length = 2 := by
    rw [gateAt_eq_getElem C j hj]
    exact hAO.2.2 C.gates[j] (List.getElem_mem hj)
  rcases list_eq_two hlen with ⟨a, b, hab⟩
  refine ⟨a, b, hab, ?_, ?_⟩
  · exact hAO.2.1 j hj a (by simp [hab])
  · exact hAO.2.1 j hj b (by simp [hab])

lemma wireValue_and_pair (n : ℕ) (C : Circuit) (hRB : ReadsBack n C)
    (j a b : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and)
    (hin : (gateAt C j).inputs = [a, b]) (x : Fin n → Bool) :
    PEqualNP.BlindGate.wireValue C n x (n + j) =
      (PEqualNP.BlindGate.wireValue C n x a && PEqualNP.BlindGate.wireValue C n x b) := by
  rw [wireValue_gate n C x j hj hRB, hop, hin]
  simp [GateOp.eval]

lemma wireValue_or_pair (n : ℕ) (C : Circuit) (hRB : ReadsBack n C)
    (j a b : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or)
    (hin : (gateAt C j).inputs = [a, b]) (x : Fin n → Bool) :
    PEqualNP.BlindGate.wireValue C n x (n + j) =
      (PEqualNP.BlindGate.wireValue C n x a || PEqualNP.BlindGate.wireValue C n x b) := by
  rw [wireValue_gate n C x j hj hRB, hop, hin]
  simp [GateOp.eval]

lemma merge_pass_bound {α : Type*} [DecidableEq α]
    (f : ℕ → Finset α) (M : Finset ℕ)
    (hBase : ∀ w, w ∉ M → (f w).card ≤ 1 ∨ ∃ a < w, f w ⊆ f a)
    (hStep : ∀ m ∈ M, f m = ∅ ∨ (∃ a < m, f m ⊆ f a) ∨ (∃ a < m, ∃ b < m, f m ⊆ f a ∪ f b)) :
    ∀ B : ℕ, ∀ R : Finset ℕ, (∀ r ∈ R, r < B) →
      (R.biUnion f).card ≤ R.card + (M.filter (· < B)).card := by
  intro B
  induction B with
  | zero =>
    intro R hR
    have hRe : R = ∅ := by
      ext r; simp only [Finset.notMem_empty, iff_false]
      intro hr; have := hR r hr; omega
    subst hRe; simp
  | succ B ih =>
    intro R hR
    have hMsub : (M.filter (· < B)).card ≤ (M.filter (· < B + 1)).card := by
      apply Finset.card_le_card
      intro x hx
      simp only [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, by omega⟩
    by_cases hBR : B ∈ R
    · let R0 := R.erase B
      have hR0lt : ∀ r ∈ R0, r < B := by
        intro r hr
        have hr1 := Finset.mem_erase.mp hr
        have hr2 := hR r hr1.2
        omega
      have hR0card : R0.card + 1 = R.card := Finset.card_erase_add_one hBR
      have hRins : R = insert B R0 := (Finset.insert_erase hBR).symm
      by_cases hBM : B ∈ M
      · have hMfilt : (M.filter (· < B + 1)).card = (M.filter (· < B)).card + 1 := by
          have heq : M.filter (· < B + 1) = insert B (M.filter (· < B)) := by
            ext x
            simp only [Finset.mem_filter, Finset.mem_insert]
            constructor
            · rintro ⟨hxM, hxlt⟩
              by_cases hxB : x = B
              · exact Or.inl hxB
              · exact Or.inr ⟨hxM, by omega⟩
            · rintro (rfl | ⟨hxM, hxlt⟩)
              · exact ⟨hBM, by omega⟩
              · exact ⟨hxM, by omega⟩
          rw [heq, Finset.card_insert_of_notMem]
          simp
        rcases hStep B hBM with hEmpty | ⟨a, haB, hfa⟩ | ⟨a, haB, b, hbB, hfab⟩
        · have hsub : R.biUnion f ⊆ R0.biUnion f := by
            rw [hRins, Finset.biUnion_insert, hEmpty, Finset.empty_union]
          have h1 := Finset.card_le_card hsub
          have h2 := ih R0 hR0lt
          omega
        · let R' := insert a R0
          have hR'lt : ∀ r ∈ R', r < B := by
            intro r hr
            rcases Finset.mem_insert.mp hr with rfl | hr0
            · exact haB
            · exact hR0lt r hr0
          have hsub : R.biUnion f ⊆ R'.biUnion f := by
            rw [hRins, Finset.biUnion_insert, Finset.biUnion_insert]
            exact Finset.union_subset_union_left hfa
          have h1 := Finset.card_le_card hsub
          have h2 := ih R' hR'lt
          have h3 : R'.card ≤ R0.card + 1 := Finset.card_insert_le a R0
          omega
        · let R' := insert a (insert b R0)
          have hR'lt : ∀ r ∈ R', r < B := by
            intro r hr
            rcases Finset.mem_insert.mp hr with rfl | hr1
            · exact haB
            · rcases Finset.mem_insert.mp hr1 with rfl | hr0
              · exact hbB
              · exact hR0lt r hr0
          have hsub : R.biUnion f ⊆ R'.biUnion f := by
            rw [hRins, Finset.biUnion_insert, Finset.biUnion_insert, Finset.biUnion_insert,
              ← Finset.union_assoc]
            exact Finset.union_subset_union_left hfab
          have h1 := Finset.card_le_card hsub
          have h2 := ih R' hR'lt
          have h3 : R'.card ≤ (insert b R0).card + 1 := Finset.card_insert_le a (insert b R0)
          have h4 : (insert b R0).card ≤ R0.card + 1 := Finset.card_insert_le b R0
          omega
      · rcases hBase B hBM with hBcard | ⟨a, haB, hfa⟩
        · have h1 : (R.biUnion f).card ≤ (f B).card + (R0.biUnion f).card := by
            rw [hRins, Finset.biUnion_insert]
            exact Finset.card_union_le _ _
          have h2 := ih R0 hR0lt
          omega
        · let R' := insert a R0
          have hR'lt : ∀ r ∈ R', r < B := by
            intro r hr
            rcases Finset.mem_insert.mp hr with rfl | hr0
            · exact haB
            · exact hR0lt r hr0
          have hsub : R.biUnion f ⊆ R'.biUnion f := by
            rw [hRins, Finset.biUnion_insert, Finset.biUnion_insert]
            exact Finset.union_subset_union_left hfa
          have h1 := Finset.card_le_card hsub
          have h2 := ih R' hR'lt
          have h3 : R'.card ≤ R0.card + 1 := Finset.card_insert_le a R0
          omega
    · have hRlt : ∀ r ∈ R, r < B := by
        intro r hr
        have h1 := hR r hr
        have hne : r ≠ B := fun he => hBR (he ▸ hr)
        omega
      have h2 := ih R hRlt
      omega


def singleSupport (n : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i =>
    PEqualNP.BlindGate.wireValue C n (fun k => decide (k = i)) w = true

def outside (n : ℕ) (S : Finset (Fin n)) : Fin n → Bool :=
  fun i => decide (i ∉ S)

def good (n : ℕ) (C : Circuit) (S : Finset (Fin n)) (w : ℕ) : Prop :=
  w < n + C.gates.length ∧ PEqualNP.BlindGate.wireValue C n (outside n S) w = false

noncomputable def restrainedSupport (n : ℕ) (C : Circuit) (S : Finset (Fin n)) (w : ℕ) : Finset (Fin n) := by
  classical
  exact if good n C S w then singleSupport n C w else ∅

noncomputable def charged (n : ℕ) (C : Circuit) (S : Finset (Fin n)) : Finset ℕ := by
  classical
  exact (Finset.range (n + C.gates.length)).filter fun w =>
    n ≤ w ∧ good n C S w ∧ (gateAt C (w - n)).op = GateOp.or ∧
      1 < (singleSupport n C w).card

lemma singleSupport_input (n : ℕ) (C : Circuit) (w : ℕ) (hw : w < n) :
    singleSupport n C w = {⟨w, hw⟩} := by
  ext i
  simp [singleSupport, wireValue_input n C _ w hw, eq_comm]

lemma singleSupport_and (n : ℕ) (C : Circuit) (hRB : ReadsBack n C)
    (j a b : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) (hin : (gateAt C j).inputs = [a, b]) :
    singleSupport n C (n + j) = singleSupport n C a ∩ singleSupport n C b := by
  ext i
  simp [singleSupport, wireValue_and_pair n C hRB j a b hj hop hin]

lemma singleSupport_or (n : ℕ) (C : Circuit) (hRB : ReadsBack n C)
    (j a b : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hin : (gateAt C j).inputs = [a, b]) :
    singleSupport n C (n + j) = singleSupport n C a ∪ singleSupport n C b := by
  ext i
  simp [singleSupport, wireValue_or_pair n C hRB j a b hj hop hin]

lemma restrained_or (n : ℕ) (C : Circuit) (S : Finset (Fin n)) (hAO : IsAO2 n C)
    (j a b : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hin : (gateAt C j).inputs = [a, b])
    (ha : a < n + j) (hb : b < n + j) (hg : good n C S (n + j)) :
    restrainedSupport n C S (n + j) =
      restrainedSupport n C S a ∪ restrainedSupport n C S b := by
  have hval := hg.2
  rw [wireValue_or_pair n C hAO.2.1 j a b hj hop hin] at hval
  have hab : PEqualNP.BlindGate.wireValue C n (outside n S) a = false ∧
      PEqualNP.BlindGate.wireValue C n (outside n S) b = false := by
    simpa only [Bool.or_eq_false_iff] using hval
  have hga : good n C S a := ⟨by omega, hab.1⟩
  have hgb : good n C S b := ⟨by omega, hab.2⟩
  simp only [restrainedSupport, hg, hga, hgb, ↓reduceIte]
  exact singleSupport_or n C hAO.2.1 j a b hj hop hin

lemma restrained_and_pass (n : ℕ) (C : Circuit) (S : Finset (Fin n))
    (hAO : IsAO2 n C) (j a b : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) (hin : (gateAt C j).inputs = [a, b])
    (ha : a < n + j) (hb : b < n + j) (hg : good n C S (n + j)) :
    ∃ u < n + j, restrainedSupport n C S (n + j) ⊆ restrainedSupport n C S u := by
  have hval := hg.2
  rw [wireValue_and_pair n C hAO.2.1 j a b hj hop hin] at hval
  have hab : PEqualNP.BlindGate.wireValue C n (outside n S) a = false ∨
      PEqualNP.BlindGate.wireValue C n (outside n S) b = false := by
    simpa only [Bool.and_eq_false_iff] using hval
  rcases hab with hfa | hfb
  · have hga : good n C S a := ⟨by omega, hfa⟩
    refine ⟨a, ha, ?_⟩
    simp only [restrainedSupport, hg, hga, ↓reduceIte]
    rw [singleSupport_and n C hAO.2.1 j a b hj hop hin]
    exact Finset.inter_subset_left
  · have hgb : good n C S b := ⟨by omega, hfb⟩
    refine ⟨b, hb, ?_⟩
    simp only [restrainedSupport, hg, hgb, ↓reduceIte]
    rw [singleSupport_and n C hAO.2.1 j a b hj hop hin]
    exact Finset.inter_subset_right

lemma support_budget (n : ℕ) (C : Circuit) (S : Finset (Fin n))
    (hAO : IsAO2 n C) (R : Finset ℕ) (hR : ∀ w ∈ R, good n C S w) :
    (R.biUnion (singleSupport n C)).card ≤ R.card + (charged n C S).card := by
  classical
  let f := restrainedSupport n C S
  let M := charged n C S
  have hBase : ∀ w, w ∉ M → (f w).card ≤ 1 ∨ ∃ a < w, f w ⊆ f a := by
    intro w hw
    by_cases hg : good n C S w
    · by_cases hn : w < n
      · left
        simp [f, restrainedSupport, hg, singleSupport_input n C w hn]
      · by_cases hsmall : (singleSupport n C w).card ≤ 1
        · left
          simpa [f, restrainedSupport, hg] using hsmall
        · right
          let j := w - n
          have hwj : w = n + j := by omega
          have hj : j < C.gates.length := by have := hg.1; omega
          obtain ⟨a, b, hin, ha, hb⟩ := gate_inputs_two n C hAO j hj
          have hop := hAO.1 (gateAt C j)
            (by rw [gateAt_eq_getElem C j hj]; exact List.getElem_mem hj)
          rcases hop with hand | hor
          · rw [hwj] at hg ⊢
            exact restrained_and_pass n C S hAO j a b hj hand hin ha hb hg
          · exfalso
            apply hw
            exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hg.1, by omega, hg, hor,
              by omega⟩
    · left
      simp [f, restrainedSupport, hg]
  have hStep : ∀ w ∈ M, f w = ∅ ∨ (∃ a < w, f w ⊆ f a) ∨
      (∃ a < w, ∃ b < w, f w ⊆ f a ∪ f b) := by
    intro w hw
    obtain ⟨hwB, hn, hg, hor, hsize⟩ := Finset.mem_filter.mp hw
    let j := w - n
    have hwj : w = n + j := by omega
    have hj : j < C.gates.length := by have := hg.1; omega
    obtain ⟨a, b, hin, ha, hb⟩ := gate_inputs_two n C hAO j hj
    refine Or.inr (Or.inr ⟨a, by omega, b, by omega, ?_⟩)
    rw [hwj] at hg ⊢
    exact (restrained_or n C S hAO j a b hj hor hin ha hb hg).le
  have hm := merge_pass_bound f M hBase hStep (n + C.gates.length) R
    (fun w hw => (hR w hw).1)
  have heq : R.biUnion f = R.biUnion (singleSupport n C) := by
    apply Finset.biUnion_congr rfl
    intro w hw
    simp [f, restrainedSupport, hR w hw]
  rw [heq] at hm
  exact hm.trans (Nat.add_le_add_left (Finset.card_filter_le M _) R.card)


lemma charged_subset (n : ℕ) (C : Circuit) (S : Finset (Fin n)) (hAO : IsAO2 n C)
    (w : ℕ) (hw : w ∈ charged n C S) : singleSupport n C w ⊆ S := by
  classical
  have hg := (Finset.mem_filter.mp hw).2.2.1
  exact SemanticSupport.support_of_false_complement n C hAO S w hg.2

lemma pure_or_support (n : ℕ) (C : Circuit) (w : ℕ) (Q : Finset (Fin n))
    (h : ∀ x : Fin n → Bool, PEqualNP.BlindGate.wireValue C n x w =
      decide (∃ i ∈ Q, x i = true)) : singleSupport n C w = Q := by
  ext i
  simp [singleSupport, h, eq_comm]

lemma pure_or_good (n : ℕ) (C : Circuit) (w : ℕ) (Q S : Finset (Fin n))
    (hw : w < n + C.gates.length) (hQS : Q ⊆ S)
    (h : ∀ x : Fin n → Bool, PEqualNP.BlindGate.wireValue C n x w =
      decide (∃ i ∈ Q, x i = true)) : good n C S w := by
  refine ⟨hw, ?_⟩
  rw [h]
  apply decide_eq_false
  rintro ⟨i, hi, hx⟩
  exact (of_decide_eq_true hx) (hQS hi)

lemma pure_or_budget (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (w : ℕ) (Q S : Finset (Fin n)) (hw : w < n + C.gates.length) (hQS : Q ⊆ S)
    (h : ∀ x : Fin n → Bool, PEqualNP.BlindGate.wireValue C n x w =
      decide (∃ i ∈ Q, x i = true)) : Q.card ≤ 1 + (charged n C S).card := by
  have hm := support_budget n C S hAO {w} (by
    intro u hu
    have : u = w := Finset.mem_singleton.mp hu
    subst u
    exact pure_or_good n C w Q S hw hQS h)
  simpa [pure_or_support n C w Q h] using hm

noncomputable def orWires (n : ℕ) (C : Circuit) : Finset ℕ := by
  classical
  exact (Finset.Ico n (n + C.gates.length)).filter fun w =>
    (gateAt C (w - n)).op = GateOp.or

lemma charged_subset_orWires (n : ℕ) (C : Circuit) (S : Finset (Fin n)) :
    charged n C S ⊆ orWires n C := by
  classical
  intro w hw
  obtain ⟨hbound, hn, hg, hop, hsize⟩ := Finset.mem_filter.mp hw
  exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hn, hg.1⟩, hop⟩

lemma charged_disjoint (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (S T : Finset (Fin n)) (hST : (S ∩ T).card ≤ 1) :
    Disjoint (charged n C S) (charged n C T) := by
  classical
  apply Finset.disjoint_left.mpr
  intro w hwS hwT
  have hS := charged_subset n C S hAO w hwS
  have hT := charged_subset n C T hAO w hwT
  have hsub : singleSupport n C w ⊆ S ∩ T := by
    intro i hi
    exact Finset.mem_inter.mpr ⟨hS hi, hT hi⟩
  have hc := Finset.card_le_card hsub
  have hlarge := (Finset.mem_filter.mp hwS).2.2.2.2
  omega

lemma support_family_budget {α : Type*} (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (A : Finset α) (S : α → Finset (Fin n)) (R : α → Finset ℕ)
    (hR : ∀ a ∈ A, ∀ w ∈ R a, good n C (S a) w)
    (hsep : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → (S a ∩ S b).card ≤ 1) :
    (∑ a ∈ A, ((R a).biUnion (singleSupport n C)).card) ≤
      (∑ a ∈ A, (R a).card) + (orWires n C).card := by
  classical
  have hdis : Set.PairwiseDisjoint (A : Set α) (fun a => charged n C (S a)) := by
    intro a ha b hb hab
    exact charged_disjoint n C hAO (S a) (S b) (hsep a ha b hb hab)
  have hcharge : (∑ a ∈ A, (charged n C (S a)).card) ≤ (orWires n C).card := by
    rw [← Finset.card_biUnion hdis]
    apply Finset.card_le_card
    intro w hw
    obtain ⟨a, ha, hwa⟩ := Finset.mem_biUnion.mp hw
    exact charged_subset_orWires n C (S a) hwa
  calc
    _ ≤ ∑ a ∈ A, ((R a).card + (charged n C (S a)).card) := by
      apply Finset.sum_le_sum
      intro a ha
      exact support_budget n C (S a) hAO (R a) (hR a ha)
    _ = (∑ a ∈ A, (R a).card) + (∑ a ∈ A, (charged n C (S a)).card) :=
      Finset.sum_add_distrib
    _ ≤ _ := Nat.add_le_add_left hcharge _

end PEqualNP.Outside.L_meta_4970.SupportAccounting

namespace PEqualNP.Outside.L_meta_4970_aux

open Finset

def lineOr {p l : Nat} (Q : Finset (Fin l)) (x : Fin (p + l) → Bool) : Bool :=
  decide (∃ b ∈ Q, x (Fin.natAdd p b) = true)

def pointOr {p l : Nat} (P : Finset (Fin p)) (x : Fin (p + l) → Bool) : Bool :=
  decide (∃ a ∈ P, x (Fin.castAdd l a) = true)

theorem lineOr_unique {p l : Nat} {Q R : Finset (Fin l)}
    (h : ∀ x : Fin (p + l) → Bool, lineOr Q x = lineOr R x) : Q = R := by
  ext b
  have hh := h (fun i => decide (i = Fin.natAdd p b))
  have hi : ∀ b' : Fin l, Fin.natAdd p b' = Fin.natAdd p b ↔ b' = b := by
    intro b'
    constructor
    · intro he
      apply Fin.ext
      exact Nat.add_left_cancel (congrArg Fin.val he)
    · rintro rfl; rfl
  simpa [lineOr, hi] using hh

theorem pointOr_unique {p l : Nat} {P R : Finset (Fin p)}
    (h : ∀ x : Fin (p + l) → Bool, pointOr P x = pointOr R x) : P = R := by
  ext a
  have hh := h (fun i => decide (i = Fin.castAdd l a))
  have hi : ∀ a' : Fin p, Fin.castAdd l a' = Fin.castAdd l a ↔ a' = a := by
    intro a'
    constructor
    · intro he
      exact Fin.ext (congrArg (fun i : Fin (p + l) => i.val) he)
    · rintro rfl; rfl
  simpa [pointOr, hi] using hh

theorem different_colours_ne {p l : Nat} {P : Finset (Fin p)} {Q : Finset (Fin l)}
    (hP : P.Nonempty) : ¬ (∀ x : Fin (p + l) → Bool, pointOr P x = lineOr Q x) := by
  intro h
  obtain ⟨a, ha⟩ := hP
  let x : Fin (p + l) → Bool := fun i => decide (i = Fin.castAdd l a)
  have hp : pointOr P x = true := by
    simp only [pointOr, decide_eq_true_eq]
    exact ⟨a, ha, by simp [x]⟩
  have hq : lineOr Q x = false := by
    simp only [lineOr, decide_eq_false_iff_not]
    rintro ⟨b, _, hb⟩
    have hba : Fin.natAdd p b = Fin.castAdd l a := by simpa [x] using hb
    have hv := congrArg Fin.val hba
    have ha' := a.isLt
    simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
    omega
  have hh := h x
  rw [hp, hq] at hh
  cases hh

theorem star_centre_unique {p l : Nat} {E : Finset (Fin p × Fin l)}
    (hE : ∀ a a' : Fin p, ∀ b b' : Fin l, a ≠ a' → b ≠ b' →
      ¬ ((a,b) ∈ E ∧ (a,b') ∈ E ∧ (a',b) ∈ E ∧ (a',b') ∈ E))
    {a a' : Fin p} {Q : Finset (Fin l)} (hQ : 2 ≤ Q.card)
    (ha : ∀ b ∈ Q, (a,b) ∈ E) (ha' : ∀ b ∈ Q, (a',b) ∈ E) : a = a' := by
  by_contra haa
  obtain ⟨b, hb, b', hb', hbb⟩ := Finset.one_lt_card.mp (by omega : 1 < Q.card)
  exact hE a a' b b' haa hbb ⟨ha b hb, ha b' hb', ha' b hb, ha' b' hb'⟩

theorem one_wire_one_point_centre {p l : Nat} {E : Finset (Fin p × Fin l)}
    (hE : ∀ a a' : Fin p, ∀ b b' : Fin l, a ≠ a' → b ≠ b' →
      ¬ ((a,b) ∈ E ∧ (a,b') ∈ E ∧ (a',b) ∈ E ∧ (a',b') ∈ E))
    {a a' : Fin p} {Q R : Finset (Fin l)} (hQ : 2 ≤ Q.card)
    (ha : ∀ b ∈ Q, (a,b) ∈ E) (ha' : ∀ b ∈ R, (a',b) ∈ E)
    (h : ∀ x : Fin (p + l) → Bool, lineOr Q x = lineOr R x) : a = a' := by
  have hQR := lineOr_unique h
  subst R
  exact star_centre_unique hE hQ ha ha'

end PEqualNP.Outside.L_meta_4970_aux

namespace PEqualNP.Outside.L_meta_4970_aux

open Finset

theorem serving_edge_assignment {p l : Nat} (E : Finset (Fin p × Fin l))
    (pointServes lineServes : Fin p × Fin l → Prop)
    (hserve : ∀ e ∈ E, pointServes e ∨ lineServes e) :
    ∃ owner : Fin p × Fin l → Fin (p + l),
      (∀ e ∈ E,
        (owner e = Fin.castAdd l e.1 ∧ pointServes e) ∨
        (owner e = Fin.natAdd p e.2 ∧ lineServes e)) ∧
      (∀ a b, (a,b) ∈ E →
        Fin.castAdd l a ∈ E.image owner ∨ Fin.natAdd p b ∈ E.image owner) ∧
      (∀ v ∈ E.image owner, (E.filter (fun e => owner e = v)).Nonempty) ∧
      E.card + (E.image owner).card =
        ∑ v ∈ E.image owner, ((E.filter (fun e => owner e = v)).card + 1) := by
  classical
  let owner : Fin p × Fin l → Fin (p + l) :=
    fun e => if pointServes e then Fin.castAdd l e.1 else Fin.natAdd p e.2
  have ho : ∀ e ∈ E,
      (owner e = Fin.castAdd l e.1 ∧ pointServes e) ∨
      (owner e = Fin.natAdd p e.2 ∧ lineServes e) := by
    intro e he
    by_cases hs : pointServes e
    · exact Or.inl ⟨by simp [owner, hs], hs⟩
    · exact Or.inr ⟨by simp [owner, hs], (hserve e he).resolve_left hs⟩
  refine ⟨owner, ho, ?_, ?_, ?_⟩
  · intro a b he
    have hm : owner (a,b) ∈ E.image owner := Finset.mem_image.mpr ⟨(a,b), he, rfl⟩
    rcases ho (a,b) he with ⟨hh, _⟩ | ⟨hh, _⟩
    · exact Or.inl (hh ▸ hm)
    · exact Or.inr (hh ▸ hm)
  · intro v hv
    obtain ⟨e, he, hev⟩ := Finset.mem_image.mp hv
    exact ⟨e, Finset.mem_filter.mpr ⟨he, hev⟩⟩
  · have hcard := Finset.card_eq_sum_card_image owner E
    rw [Finset.sum_add_distrib]
    simpa only [Finset.sum_const_nat, Nat.mul_one] using
      congrArg (fun k => k + (E.image owner).card) hcard

end PEqualNP.Outside.L_meta_4970_aux

namespace PEqualNP.Outside.L_meta_4970_aux

def neighbours {p l : Nat} (E : Finset (Fin p × Fin l)) (v : Fin (p + l)) :
    Finset (Fin (p + l)) :=
  Fin.addCases
    (fun a => (Finset.univ.filter fun b => (a, b) ∈ E).image (Fin.natAdd p))
    (fun b => (Finset.univ.filter fun a => (a, b) ∈ E).image (Fin.castAdd l)) v

theorem neighbours_left {p l : Nat} (E : Finset (Fin p × Fin l)) (a : Fin p) :
    neighbours E (Fin.castAdd l a) =
      (Finset.univ.filter fun b => (a, b) ∈ E).image (Fin.natAdd p) := by
  simp [neighbours]

theorem neighbours_right {p l : Nat} (E : Finset (Fin p × Fin l)) (b : Fin l) :
    neighbours E (Fin.natAdd p b) =
      (Finset.univ.filter fun a => (a, b) ∈ E).image (Fin.castAdd l) := by
  simp [neighbours]

theorem left_right_ne {p l : Nat} (a : Fin p) (b : Fin l) :
    Fin.castAdd l a ≠ Fin.natAdd p b := by
  intro h
  have he := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at he
  omega

theorem neighbours_inter_card {p l : Nat} (E : Finset (Fin p × Fin l))
    (hfour : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (u v : Fin (p + l)) (hne : u ≠ v) :
    (neighbours E u ∩ neighbours E v).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  obtain ⟨hxu, hxv⟩ := Finset.mem_inter.mp hx
  obtain ⟨hyu, hyv⟩ := Finset.mem_inter.mp hy
  revert hne hxu hxv hyu hyv
  refine Fin.addCases (fun a => ?_) (fun b => ?_) u
  · refine Fin.addCases (fun a' => ?_) (fun b' => ?_) v
    · intro hne hxu hxv hyu hyv
      rw [neighbours_left] at hxu hxv hyu hyv
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hxu
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hyu
      obtain ⟨c', hc', hec⟩ := Finset.mem_image.mp hxv
      obtain ⟨d', hd', hed⟩ := Finset.mem_image.mp hyv
      have ec : c' = c := by
        apply Fin.ext
        have h := congrArg Fin.val hec
        simp only [Fin.val_natAdd] at h
        omega
      have ed : d' = d := by
        apply Fin.ext
        have h := congrArg Fin.val hed
        simp only [Fin.val_natAdd] at h
        omega
      subst c' d'
      have e : c = d := by
        by_contra hcd
        exact hfour a a' c d (fun h => hne (congrArg (Fin.castAdd l) h)) hcd
          ⟨(Finset.mem_filter.mp hc).2, (Finset.mem_filter.mp hd).2,
            (Finset.mem_filter.mp hc').2, (Finset.mem_filter.mp hd').2⟩
      exact congrArg (Fin.natAdd p) e
    · intro _ hxu hxv _ _
      rw [neighbours_left] at hxu
      rw [neighbours_right] at hxv
      obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hxu
      obtain ⟨d, -, hd⟩ := Finset.mem_image.mp hxv
      exact (left_right_ne d c hd).elim
  · refine Fin.addCases (fun a' => ?_) (fun b' => ?_) v
    · intro _ hxu hxv _ _
      rw [neighbours_right] at hxu
      rw [neighbours_left] at hxv
      obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hxu
      obtain ⟨d, -, hd⟩ := Finset.mem_image.mp hxv
      exact (left_right_ne c d hd.symm).elim
    · intro hne hxu hxv hyu hyv
      rw [neighbours_right] at hxu hxv hyu hyv
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hxu
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hyu
      obtain ⟨c', hc', hec⟩ := Finset.mem_image.mp hxv
      obtain ⟨d', hd', hed⟩ := Finset.mem_image.mp hyv
      have ec : c' = c := Fin.ext (congrArg (fun z : Fin (p + l) => z.val) hec)
      have ed : d' = d := Fin.ext (congrArg (fun z : Fin (p + l) => z.val) hed)
      subst c' d'
      have e : c = d := by
        by_contra hcd
        exact hfour c d b b' hcd (fun h => hne (congrArg (Fin.natAdd p) h))
          ⟨(Finset.mem_filter.mp hc).2, (Finset.mem_filter.mp hc').2,
            (Finset.mem_filter.mp hd).2, (Finset.mem_filter.mp hd').2⟩
      exact congrArg (Fin.castAdd l) e

end PEqualNP.Outside.L_meta_4970_aux

namespace PEqualNP.Outside.L_meta_4970.EssentialSupport

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wiresLength (gs : List Gate) (x : List Bool) :
    (gs.foldl step x).length = x.length+gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp
  | append_singleton gs g ih => simp [List.foldl_append,step,ih,Nat.add_assoc]

theorem wireSnoc (w : List Bool) (b : Bool) (i : ℕ) :
    (w ++ [b]).getD i false = if i = w.length then b else w.getD i false := by
  rcases lt_trichotomy i w.length with h|rfl|h
  · simp [List.getD_eq_getElem?_getD,List.getElem?_append_left h,h.ne]
  · simp [List.getD_eq_getElem?_getD]
  · have h1 : w.length ≤ i := by omega
    have h2 : (w ++ [b]).length ≤ i := by simp; omega
    simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none h1,List.getElem?_eq_none h2,h.ne']

theorem smallSupport (n : ℕ) (gs : List Gate)
    (arity : ∀ g ∈ gs, g.inputs.length ≤ 2) (S : Finset ℕ) :
    ∃ T : Finset ℕ, T.card ≤ S.card + gs.length ∧
      ∀ x y : List Bool, x.length = n → y.length = n →
      (∀ i ∈ T, x.getD i false = y.getD i false) →
      ∀ i ∈ S, (gs.foldl step x).getD i false = (gs.foldl step y).getD i false := by
  induction gs using List.reverseRecOn generalizing S with
  | nil => exact ⟨S,by simp,fun _ _ _ _ same => same⟩
  | append_singleton gs g ih =>
    have prior : ∀ a ∈ gs, a.inputs.length ≤ 2 :=
      fun a ha => arity a (List.mem_append_left _ ha)
    have fan : g.inputs.length ≤ 2 := arity g (List.mem_append_right _ (List.mem_singleton_self _))
    let w := n+gs.length
    let U := if w ∈ S then S.erase w ∪ g.inputs.toFinset else S
    have small : U.card ≤ S.card+1 := by
      dsimp only [U]
      split_ifs with used
      · have h1 := Finset.card_union_le (S.erase w) g.inputs.toFinset
        have h2 := Finset.card_erase_add_one used
        have h3 := List.toFinset_card_le (l := g.inputs)
        omega
      · omega
    obtain ⟨T,bound,works⟩ := ih prior U
    refine ⟨T,by simp only [List.length_append,List.length_singleton]; omega,?_⟩
    intro x y hx hy equal i iq
    have X := (wiresLength gs x).trans (by rw [hx])
    have Y := (wiresLength gs y).trans (by rw [hy])
    change (gs.foldl step x).length = w at X
    change (gs.foldl step y).length = w at Y
    have old := works x y hx hy equal
    simp only [List.foldl_append,List.foldl_cons,List.foldl_nil,step,wireSnoc,X,Y]
    by_cases atNew : i = w
    · have used : w ∈ S := atNew ▸ iq
      rw [ite_eq_left atNew,ite_eq_left atNew]
      congr 1
      apply List.map_congr_left
      intro j jRead
      apply old
      dsimp only [U]
      rw [ite_eq_left used]
      exact Finset.mem_union_right _ (List.mem_toFinset.mpr jRead)
    · rw [ite_eq_right atNew,ite_eq_right atNew]
      apply old
      dsimp only [U]
      split_ifs
      · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨atNew,iq⟩)
      · exact iq


lemma essential_bound (n : ℕ) (C : Circuit) (hfan : FanInTwo C)
    (S : Finset (Fin n))
    (hess : ∀ i ∈ S, ∃ x y : Fin n → Bool,
      (∀ k, k ≠ i → x k = y k) ∧ circuitFun n C x ≠ circuitFun n C y) :
    S.card ≤ C.size + 1 := by
  classical
  obtain ⟨T, hT, hworks⟩ := smallSupport n C.gates (fun g hg => (hfan g hg).2) {C.output}
  have hsub : S.image Fin.val ⊆ T := by
    intro j hj
    obtain ⟨i, his, rfl⟩ := Finset.mem_image.mp hj
    by_contra hn
    obtain ⟨x, y, hxy, hne⟩ := hess i his
    apply hne
    have heq := hworks (List.ofFn x) (List.ofFn y) (by simp) (by simp) ?_ C.output (by simp)
    · exact heq
    · intro k hk
      by_cases hkn : k < n
      · have hki : (⟨k, hkn⟩ : Fin n) ≠ i := by
          intro h
          apply hn
          simpa only [← h] using hk
        simpa only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hkn,
          dite_true, Option.getD_some] using hxy ⟨k, hkn⟩ hki
      · rw [List.getD_eq_default _ _ (by simp; omega),
          List.getD_eq_default _ _ (by simp; omega)]
  have hc := Finset.card_le_card hsub
  have himage : (S.image Fin.val).card = S.card :=
    Finset.card_image_of_injective S Fin.val_injective
  rw [himage] at hc
  simp only [Finset.card_singleton] at hT
  change S.card ≤ C.gates.length + 1
  omega

lemma left_ne_right {p l : ℕ} (a : Fin p) (b : Fin l) :
    Fin.castAdd l a ≠ Fin.natAdd p b := by
  intro h
  have := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at this
  omega

lemma edge_input_essential (p l : ℕ) (E : Finset (Fin p × Fin l))
    (C : Circuit)
    (hcomp : ∀ x : Fin (p + l) → Bool, circuitFun (p + l) C x =
      decide (∃ a b, (a, b) ∈ E ∧ x (Fin.castAdd l a) = true ∧
        x (Fin.natAdd p b) = true))
    (a : Fin p) (b : Fin l) (hab : (a, b) ∈ E) :
    (∃ x y : Fin (p + l) → Bool,
      (∀ k, k ≠ Fin.castAdd l a → x k = y k) ∧
      circuitFun (p + l) C x ≠ circuitFun (p + l) C y) ∧
    (∃ x y : Fin (p + l) → Bool,
      (∀ k, k ≠ Fin.natAdd p b → x k = y k) ∧
      circuitFun (p + l) C x ≠ circuitFun (p + l) C y) := by
  classical
  let x : Fin (p + l) → Bool := fun k => decide (k = Fin.castAdd l a ∨ k = Fin.natAdd p b)
  have hx : circuitFun (p + l) C x = true := by
    rw [hcomp]
    exact decide_eq_true ⟨a, b, hab, by simp [x], by simp [x]⟩
  constructor
  · let y : Fin (p + l) → Bool := fun k => decide (k = Fin.natAdd p b)
    refine ⟨x, y, ?_, ?_⟩
    · intro k hk
      simp [x, y, hk]
    · have hy : circuitFun (p + l) C y = false := by
        rw [hcomp]
        apply decide_eq_false
        rintro ⟨a', b', he, ha, hb⟩
        exact left_ne_right a' b (of_decide_eq_true ha)
      rw [hx, hy]
      decide
  · let y : Fin (p + l) → Bool := fun k => decide (k = Fin.castAdd l a)
    refine ⟨x, y, ?_, ?_⟩
    · intro k hk
      simp [x, y, hk]
    · have hy : circuitFun (p + l) C y = false := by
        rw [hcomp]
        apply decide_eq_false
        rintro ⟨a', b', he, ha, hb⟩
        exact left_ne_right a b' (of_decide_eq_true hb).symm
      rw [hx, hy]
      decide

def active (p l : ℕ) (E : Finset (Fin p × Fin l)) : Finset (Fin (p + l)) :=
  E.image (fun e => Fin.castAdd l e.1) ∪ E.image (fun e => Fin.natAdd p e.2)

lemma active_bound (p l : ℕ) (E : Finset (Fin p × Fin l))
    (C : Circuit) (hfan : FanInTwo C)
    (hcomp : ∀ x : Fin (p + l) → Bool, circuitFun (p + l) C x =
      decide (∃ a b, (a, b) ∈ E ∧ x (Fin.castAdd l a) = true ∧
        x (Fin.natAdd p b) = true)) :
    (active p l E).card ≤ C.size + 1 := by
  apply essential_bound (p + l) C hfan
  intro i hi
  rcases Finset.mem_union.mp hi with hi | hi
  · obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hi
    exact (edge_input_essential p l E C hcomp a b hab).1
  · obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hi
    exact (edge_input_essential p l E C hcomp a b hab).2

lemma active_parts_disjoint (p l : ℕ) (E : Finset (Fin p × Fin l)) :
    Disjoint (E.image fun e => Fin.castAdd l e.1)
      (E.image fun e => Fin.natAdd p e.2) := by
  apply Finset.disjoint_left.mpr
  intro v hv hv'
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨f, hf, hfe⟩ := Finset.mem_image.mp hv'
  exact left_ne_right e.1 f.2 hfe.symm

lemma active_card_left_star (p l : ℕ) (E : Finset (Fin p × Fin l))
    (hne : E.Nonempty) (a : Fin p) (hstar : ∀ e ∈ E, e.1 = a) :
    (active p l E).card = E.card + 1 := by
  classical
  have hleft : E.image (fun e => Fin.castAdd l e.1) = {Fin.castAdd l a} := by
    ext v
    constructor
    · intro hv
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hv
      simp [hstar e he]
    · intro hv
      have hv : v = Fin.castAdd l a := Finset.mem_singleton.mp hv
      obtain ⟨e, he⟩ := hne
      exact Finset.mem_image.mpr ⟨e, he, by rw [hstar e he, hv]⟩
  have hright : (E.image fun e => Fin.natAdd p e.2).card = E.card := by
    apply Finset.card_image_of_injOn
    intro e he f hf hef
    apply Prod.ext
    · exact (hstar e he).trans (hstar f hf).symm
    · apply Fin.ext
      have hval := congrArg Fin.val hef
      simp only [Fin.val_natAdd] at hval
      omega
  rw [active, Finset.card_union_of_disjoint (active_parts_disjoint p l E), hleft,
    Finset.card_singleton, hright]
  omega

lemma active_card_right_star (p l : ℕ) (E : Finset (Fin p × Fin l))
    (hne : E.Nonempty) (b : Fin l) (hstar : ∀ e ∈ E, e.2 = b) :
    (active p l E).card = E.card + 1 := by
  classical
  have hright : E.image (fun e => Fin.natAdd p e.2) = {Fin.natAdd p b} := by
    ext v
    constructor
    · intro hv
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hv
      simp [hstar e he]
    · intro hv
      have hv : v = Fin.natAdd p b := Finset.mem_singleton.mp hv
      obtain ⟨e, he⟩ := hne
      exact Finset.mem_image.mpr ⟨e, he, by rw [hstar e he, hv]⟩
  have hleft : (E.image fun e => Fin.castAdd l e.1).card = E.card := by
    apply Finset.card_image_of_injOn
    intro e he f hf hef
    apply Prod.ext
    · apply Fin.ext
      exact congrArg (fun z : Fin (p + l) => z.val) hef
    · exact (hstar e he).trans (hstar f hf).symm
  rw [active, Finset.card_union_of_disjoint (active_parts_disjoint p l E), hright,
    Finset.card_singleton, hleft]

lemma star_cover_bound (p l : ℕ) (E : Finset (Fin p × Fin l))
    (C : Circuit) (hfan : FanInTwo C)
    (hcomp : ∀ x : Fin (p + l) → Bool, circuitFun (p + l) C x =
      decide (∃ a b, (a, b) ∈ E ∧ x (Fin.castAdd l a) = true ∧
        x (Fin.natAdd p b) = true))
    (hstar : (∃ a : Fin p, ∀ e ∈ E, e.1 = a) ∨
      (∃ b : Fin l, ∀ e ∈ E, e.2 = b)) :
    ∃ S : Finset (Fin (p + l)),
      (∀ a b, (a, b) ∈ E → Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧
      E.card + S.card ≤ C.size + 1 := by
  classical
  by_cases hne : E.Nonempty
  · have hb := active_bound p l E C hfan hcomp
    rcases hstar with ⟨a, ha⟩ | ⟨b, hb'⟩
    · refine ⟨{Fin.castAdd l a}, ?_, ?_⟩
      · intro a' b hab
        left
        exact Finset.mem_singleton.mpr (congrArg (Fin.castAdd l) (ha (a', b) hab))
      · simpa only [Finset.card_singleton, active_card_left_star p l E hne a ha] using hb
    · refine ⟨{Fin.natAdd p b}, ?_, ?_⟩
      · intro a b' hab
        right
        exact Finset.mem_singleton.mpr (congrArg (Fin.natAdd p) (hb' (a, b') hab))
      · simpa only [Finset.card_singleton, active_card_right_star p l E hne b hb'] using hb
  · have he : E = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    refine ⟨∅, ?_, ?_⟩
    · simp [he]
    · simp [he]

lemma small_side_cover_bound (p l : ℕ) (E : Finset (Fin p × Fin l))
    (C : Circuit) (hfan : FanInTwo C)
    (hcomp : ∀ x : Fin (p + l) → Bool, circuitFun (p + l) C x =
      decide (∃ a b, (a, b) ∈ E ∧ x (Fin.castAdd l a) = true ∧
        x (Fin.natAdd p b) = true))
    (hsmall : p ≤ 1 ∨ l ≤ 1) :
    ∃ S : Finset (Fin (p + l)),
      (∀ a b, (a, b) ∈ E → Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧
      E.card + S.card ≤ C.size + 1 := by
  classical
  by_cases hne : E.Nonempty
  · obtain ⟨e, he⟩ := hne
    apply star_cover_bound p l E C hfan hcomp
    rcases hsmall with hp | hl
    · left
      refine ⟨e.1, fun f hf => ?_⟩
      apply Fin.ext
      omega
    · right
      refine ⟨e.2, fun f hf => ?_⟩
      apply Fin.ext
      omega
  · have he : E = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    refine ⟨∅, ?_, ?_⟩
    · simp [he]
    · simp [he]

end PEqualNP.Outside.L_meta_4970.EssentialSupport
