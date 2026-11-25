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


lemma charged_family_card_le {α : Type*} (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (A : Finset α) (S : α → Finset (Fin n))
    (hsep : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → (S a ∩ S b).card ≤ 1) :
    (∑ a ∈ A, (charged n C (S a)).card) ≤ (orWires n C).card := by
  classical
  have hdis : Set.PairwiseDisjoint (A : Set α) (fun a => charged n C (S a)) := by
    intro a ha b hb hab
    exact charged_disjoint n C hAO (S a) (S b) (hsep a ha b hb hab)
  rw [← Finset.card_biUnion hdis]
  apply Finset.card_le_card
  intro w hw
  obtain ⟨a, ha, hwa⟩ := Finset.mem_biUnion.mp hw
  exact charged_subset_orWires n C (S a) hwa

lemma self_charged_family_budget {α : Type*} (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (A : Finset α) (S : α → Finset (Fin n))
    (hsep : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → (S a ∩ S b).card ≤ 1) :
    (∑ a ∈ A, ((charged n C (S a)).biUnion (singleSupport n C)).card) ≤
      2 * (orWires n C).card := by
  classical
  have hgood : ∀ a ∈ A, ∀ w ∈ charged n C (S a), good n C (S a) w := by
    intro a ha w hw
    exact (Finset.mem_filter.mp hw).2.2.1
  have hb := support_family_budget n C hAO A S (fun a => charged n C (S a)) hgood hsep
  have hc := charged_family_card_le n C hAO A S hsep
  omega

end PEqualNP.Outside.L_meta_4970.SupportAccounting
