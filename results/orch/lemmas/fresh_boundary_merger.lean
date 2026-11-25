import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583.Mergers

lemma frontier_bound {V : Type} [DecidableEq V] (supp : ℕ → Finset V) (merges : Finset ℕ)
    (hstep : ∀ w, 1 < (supp w).card →
      (∃ a < w, supp w ⊆ supp a) ∨
      (w ∈ merges ∧ ∃ a < w, ∃ b < w, supp w ⊆ supp a ∪ supp b)) :
    ∀ (k : ℕ) (F : Finset ℕ), F ⊆ Finset.range k →
      (F.biUnion supp).card ≤ F.card + (merges ∩ Finset.range k).card := by
  intro k
  induction k with
  | zero =>
    intro F hF
    have hz : F = ∅ := by simpa using hF
    simp [hz]
  | succ k ih =>
    intro F hF
    have hrest : F.erase k ⊆ Finset.range k := by
      intro i hi
      have hne := (Finset.mem_erase.mp hi).1
      have hlt := Finset.mem_range.mp (hF (Finset.mem_of_mem_erase hi))
      exact Finset.mem_range.mpr (by omega)
    have hmon : (merges ∩ Finset.range k).card ≤ (merges ∩ Finset.range (k + 1)).card :=
      Finset.card_le_card (by
        intro i hi
        obtain ⟨him, hir⟩ := Finset.mem_inter.mp hi
        exact Finset.mem_inter.mpr ⟨him, Finset.mem_range.mpr ((Finset.mem_range.mp hir).trans (Nat.lt_succ_self k))⟩)
    by_cases hk : k ∈ F
    · have hnum := Finset.card_erase_add_one hk
      have hun : F.biUnion supp = supp k ∪ (F.erase k).biUnion supp := by
        conv_lhs => rw [← Finset.insert_erase hk, Finset.biUnion_insert]
      by_cases hs : (supp k).card ≤ 1
      · rw [hun]
        have hcard := Finset.card_union_le (supp k) ((F.erase k).biUnion supp)
        have hf := ih (F.erase k) hrest
        omega
      · rcases hstep k (by omega) with ⟨a, ha, hka⟩ | ⟨hm, a, ha, b, hb, hkab⟩
        · have hnext : insert a (F.erase k) ⊆ Finset.range k :=
            Finset.insert_subset (Finset.mem_range.mpr ha) hrest
          have hinc : F.biUnion supp ⊆ (insert a (F.erase k)).biUnion supp := by
            rw [hun, Finset.biUnion_insert]
            exact Finset.union_subset_union hka (by rfl)
          have hcard := Finset.card_le_card hinc
          have hcount := Finset.card_insert_le a (F.erase k)
          have hf := ih _ hnext
          omega
        · have hnext : insert a (insert b (F.erase k)) ⊆ Finset.range k :=
            Finset.insert_subset (Finset.mem_range.mpr ha)
              (Finset.insert_subset (Finset.mem_range.mpr hb) hrest)
          have hinc : F.biUnion supp ⊆ (insert a (insert b (F.erase k))).biUnion supp := by
            rw [hun, Finset.biUnion_insert, Finset.biUnion_insert, ← Finset.union_assoc]
            exact Finset.union_subset_union hkab (by rfl)
          have hcard := Finset.card_le_card hinc
          have hcounta := Finset.card_insert_le a (insert b (F.erase k))
          have hcountb := Finset.card_insert_le b (F.erase k)
          have hf := ih _ hnext
          have hin : merges ∩ Finset.range (k + 1) = insert k (merges ∩ Finset.range k) := by
            ext i
            by_cases heq : i = k
            · subst i
              simp [hm]
            · have hi : i < k + 1 ↔ i < k := by omega
              simp [heq, hi]
          have hnumM : (merges ∩ Finset.range (k + 1)).card =
              (merges ∩ Finset.range k).card + 1 := by simp [hin]
          omega
    · have hprev : F ⊆ Finset.range k := by simpa [Finset.erase_eq_of_notMem hk] using hrest
      exact (ih F hprev).trans (by omega)

lemma wire_merger_bound {V : Type} [DecidableEq V] (supp : ℕ → Finset V) (merges : Finset ℕ)
    (hstep : ∀ w, 1 < (supp w).card →
      (∃ a < w, supp w ⊆ supp a) ∨
      (w ∈ merges ∧ ∃ a < w, ∃ b < w, supp w ⊆ supp a ∪ supp b)) (out : ℕ) :
    (supp out).card ≤ merges.card + 1 := by
  have h := frontier_bound supp merges hstep (out + 1) {out} (by simp)
  have hle : (merges ∩ Finset.range (out + 1)).card ≤ merges.card :=
    Finset.card_le_card Finset.inter_subset_left
  simp only [Finset.singleton_biUnion, Finset.card_singleton] at h
  omega

end PEqualNP.Outside.L_meta_2583.Mergers

namespace PEqualNP.Outside.L_meta_2583.Normalization

open PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves PEqualNP.TopForm
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def evalGates (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma evalGates_length (gs : List Gate) (w : List Bool) :
    (evalGates gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [evalGates]
  | cons g gs ih =>
    simp only [evalGates, List.foldl_cons] at ih ⊢
    rw [ih]
    simp
    omega

lemma evalGates_append (gs1 gs2 : List Gate) (w : List Bool) :
    evalGates (gs1 ++ gs2) w = evalGates gs2 (evalGates gs1 w) := by
  simp [evalGates, List.foldl_append]

lemma evalGates_getD_lt (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < w.length) :
    (evalGates gs w).getD k false = w.getD k false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [evalGates, List.foldl_cons] at ih ⊢
    have hk' : k < (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).length := by
      simp
      omega
    rw [ih _ hk']
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

lemma evalGates_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (evalGates gs w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i => (evalGates (gs.take j) w).getD i false) := by
  have hsplit : gs = gs.take j ++ [gs[j]] ++ gs.drop (j + 1) := by
    have h1 := List.take_append_drop j gs
    have h2 : gs.drop j = gs[j] :: gs.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    simp
  conv_lhs => rw [hsplit]
  rw [evalGates_append, evalGates_append]
  set w1 := evalGates (gs.take j) w
  have hw1 : w1.length = w.length + j := by
    rw [evalGates_length, List.length_take]
    omega
  have hlt : w.length + j < (evalGates [gs[j]] w1).length := by
    rw [evalGates_length, hw1]
    simp
  rw [evalGates_getD_lt _ _ _ hlt]
  simp only [evalGates, List.foldl_cons, List.foldl_nil]
  rw [← hw1]
  simp [List.getD_eq_getElem?_getD]

lemma gateAt_eq_getElem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma wires_getD_gate (n : ℕ) (C : Circuit) (hRB : ReadsBack n C)
    (x : List Bool) (hx : x.length = n) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (n + j) false =
      (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i => (C.wires x).getD i false) := by
  change (evalGates C.gates x).getD (n + j) false = _
  have h1 := evalGates_getD_gate C.gates x j hj
  rw [hx] at h1
  rw [h1]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi_lt : i < n + j := by
    have := hRB j hj i
    rw [gateAt_eq_getElem C j hj] at this
    exact this hi
  have hlen : (evalGates (C.gates.take j) x).length = n + j := by
    rw [evalGates_length, hx, List.length_take]
    omega
  have hsplit : C.gates = C.gates.take j ++ C.gates.drop j := (List.take_append_drop j C.gates).symm
  symm
  change (evalGates C.gates x).getD i false = (evalGates (C.gates.take j) x).getD i false
  conv_lhs => rw [hsplit, evalGates_append]
  exact evalGates_getD_lt (C.gates.drop j) (evalGates (C.gates.take j) x) i (by omega)


end PEqualNP.Outside.L_meta_2583.Normalization

namespace PEqualNP.Outside.L_meta_2583.BoundaryMerger

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
  PEqualNP.Outside.L_meta_2583.Normalization PEqualNP.Outside.L_meta_2583.Mergers

lemma wires_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
    (C.wires (List.ofFn x)).getD i false = x i := by
  change (evalGates C.gates (List.ofFn x)).getD i false = _
  rw [evalGates_getD_lt C.gates (List.ofFn x) i (by simpa using i.isLt)]
  simp [List.getD_eq_getElem?_getD]


def wire {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

def labels {n m : ℕ} (C : Circuit) (z : Fin n → Bool) (tests : Fin m → Fin n → Bool)
    (w : ℕ) : Finset (Fin m) :=
  if w < n + C.gates.length ∧ wire C z w = false then
    Finset.univ.filter fun i => wire C (tests i) w = true
  else ∅

noncomputable def mergingWires {n m : ℕ} (C : Circuit) (z : Fin n → Bool)
    (tests : Fin m → Fin n → Bool) : Finset ℕ := by
  classical
  exact (Finset.range (n + C.gates.length)).filter fun w =>
    n ≤ w ∧ (gateAt C (w - n)).op = GateOp.or ∧ 1 < (labels C z tests w).card

lemma mem_labels {n m : ℕ} (C : Circuit) (z : Fin n → Bool)
    (tests : Fin m → Fin n → Bool) (w : ℕ) (i : Fin m) :
    i ∈ labels C z tests w ↔
      w < n + C.gates.length ∧ wire C z w = false ∧ wire C (tests i) w = true := by
  by_cases h : w < n + C.gates.length ∧ wire C z w = false
  · simp [labels, h, h.1, h.2]
  · simp only [labels, h, ↓reduceIte, Finset.notMem_empty, false_iff]
    tauto

lemma two_inputs {C : Circuit} {n j : ℕ} (hAO : IsAO2 n C) (hj : j < C.gates.length) :
    ∃ a b, (C.gates[j]).inputs = [a, b] := by
  have hlen := hAO.2.2 _ (List.getElem_mem hj)
  cases h : (C.gates[j]).inputs with
  | nil => simp [h] at hlen
  | cons a rest =>
    cases rest with
    | nil => simp [h] at hlen
    | cons b rest =>
      cases rest with
      | nil => exact ⟨a, b, rfl⟩
      | cons c rest => simp [h] at hlen

lemma labels_step {n m : ℕ} (C : Circuit) (hAO : IsAO2 n C)
    (z : Fin n → Bool) (tests : Fin m → Fin n → Bool)
    (hinput : ∀ i : Fin n, z i = false →
      (Finset.univ.filter (fun t : Fin m => tests t i = true)).card ≤ 1)
    (w : ℕ) (hlarge : 1 < (labels C z tests w).card) :
    (∃ a < w, labels C z tests w ⊆ labels C z tests a) ∨
    (w ∈ mergingWires C z tests ∧ ∃ a < w, ∃ b < w,
      labels C z tests w ⊆ labels C z tests a ∪ labels C z tests b) := by
  classical
  have hsafe : w < n + C.gates.length ∧ wire C z w = false := by
    by_contra h
    simp [labels, h] at hlarge
  have hnw : n ≤ w := by
    by_contra! h
    let i : Fin n := ⟨w, h⟩
    have he (x : Fin n → Bool) : wire C x w = x i := wires_input n C x i
    have hsubset : labels C z tests w ⊆ Finset.univ.filter (fun t : Fin m => tests t i = true) := by
      intro t ht
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (he _).symm.trans ((mem_labels _ _ _ _ _).mp ht).2.2⟩
    have hcard := Finset.card_le_card hsubset
    have hl := hinput i ((he z).symm.trans hsafe.2)
    omega
  let j := w - n
  have hw : w = n + j := by dsimp [j]; omega
  have hj : j < C.gates.length := by omega
  obtain ⟨a, b, hab⟩ := two_inputs hAO hj
  have hpar := hAO.2.1 j hj
  rw [gateAt_eq_getElem C j hj, hab] at hpar
  have ha : a < w := hw ▸ hpar a (by simp)
  have hb : b < w := hw ▸ hpar b (by simp)
  have he (x : Fin n → Bool) : wire C x w =
      (C.gates[j]).op.eval [wire C x a, wire C x b] := by
    unfold wire
    rw [hw, wires_getD_gate n C hAO.2.1 _ List.length_ofFn j hj, hab]
    rfl
  rcases hAO.1 _ (List.getElem_mem hj) with hAnd | hOr
  · have hzero : wire C z a = false ∨ wire C z b = false := by
      have hz := hsafe.2
      rw [he, hAnd] at hz
      cases ha0 : wire C z a <;> cases hb0 : wire C z b <;> simp_all [GateOp.eval]
    left
    rcases hzero with hz | hz
    · refine ⟨a, ha, ?_⟩
      intro t ht
      obtain ⟨_, _, htrue⟩ := (mem_labels _ _ _ _ _).mp ht
      rw [he, hAnd] at htrue
      exact (mem_labels _ _ _ _ _).mpr ⟨ha.trans hsafe.1, hz, (by simpa [GateOp.eval] using htrue : wire C (tests t) a = true ∧ wire C (tests t) b = true).1⟩
    · refine ⟨b, hb, ?_⟩
      intro t ht
      obtain ⟨_, _, htrue⟩ := (mem_labels _ _ _ _ _).mp ht
      rw [he, hAnd] at htrue
      exact (mem_labels _ _ _ _ _).mpr ⟨hb.trans hsafe.1, hz, (by simpa [GateOp.eval] using htrue : wire C (tests t) a = true ∧ wire C (tests t) b = true).2⟩
  · have hzero : wire C z a = false ∧ wire C z b = false := by
      have hz := hsafe.2
      rw [he, hOr] at hz
      simpa [GateOp.eval] using hz
    right
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hsafe.1, hnw, ?_, hlarge⟩, a, ha, b, hb, ?_⟩
    · change (gateAt C j).op = GateOp.or
      rwa [gateAt_eq_getElem C j hj]
    · intro t ht
      obtain ⟨_, _, htrue⟩ := (mem_labels _ _ _ _ _).mp ht
      rw [he, hOr] at htrue
      have hpos : wire C (tests t) a = true ∨ wire C (tests t) b = true := by simpa [GateOp.eval] using htrue
      rcases hpos with ht | ht
      · exact Finset.mem_union_left _ ((mem_labels _ _ _ _ _).mpr ⟨ha.trans hsafe.1, hzero.1, ht⟩)
      · exact Finset.mem_union_right _ ((mem_labels _ _ _ _ _).mpr ⟨hb.trans hsafe.1, hzero.2, ht⟩)

lemma boundary_merger_bound {n m : ℕ} (C : Circuit) (hAO : IsAO2 n C)
    (z : Fin n → Bool) (tests : Fin m → Fin n → Bool)
    (hinput : ∀ i : Fin n, z i = false →
      (Finset.univ.filter (fun t : Fin m => tests t i = true)).card ≤ 1) (w : ℕ) :
    (labels C z tests w).card ≤ (mergingWires C z tests).card + 1 :=
  wire_merger_bound _ _ (labels_step C hAO z tests hinput) w

end PEqualNP.Outside.L_meta_2583.BoundaryMerger
