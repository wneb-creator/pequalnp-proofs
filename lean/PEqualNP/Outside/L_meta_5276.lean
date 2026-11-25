import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5276

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.HeptadCover

lemma foldl_append_spec {α β : Type} (f : List α → β → α) :
    ∀ (l : List β) (acc : List α),
      (l.foldl (fun w b => w ++ [f w b]) acc).length = acc.length + l.length ∧
      (∀ i < acc.length, (l.foldl (fun w b => w ++ [f w b]) acc)[i]? = acc[i]?) ∧
      (∀ (j : ℕ) (b : β), l[j]? = some b →
        (l.foldl (fun w b => w ++ [f w b]) acc)[acc.length + j]? =
          some (f ((l.take j).foldl (fun w x => w ++ [f w x]) acc) b)) := by
  intro l
  induction l with
  | nil =>
    intro acc
    refine ⟨by simp, fun i _ => rfl, fun j b h => by simp at h⟩
  | cons a t ih =>
    intro acc
    have h1 := ih (acc ++ [f acc a])
    refine ⟨?_, ?_, ?_⟩
    · rw [List.foldl_cons, h1.1, List.length_append, List.length_singleton, List.length_cons]
      omega
    · intro i hi
      simp only [List.foldl_cons]
      have hi' : i < (acc ++ [f acc a]).length := by simp; omega
      rw [h1.2.1 i hi', List.getElem?_append_left hi]
    · intro j b hj
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        subst hj
        simp only [List.foldl_cons, Nat.add_zero, List.take_zero, List.foldl_nil]
        have hi' : acc.length < (acc ++ [f acc a]).length := by simp
        rw [h1.2.1 acc.length hi', List.getElem?_append_right (le_refl _)]
        simp
      | succ j' =>
        simp only [List.getElem?_cons_succ] at hj
        simp only [List.foldl_cons, List.take_succ_cons]
        have hstep := h1.2.2 j' b hj
        simp only [List.length_append, List.length_singleton] at hstep
        have heq : acc.length + (j' + 1) = acc.length + 1 + j' := by omega
        rw [heq]
        exact hstep

lemma foldl_append_take_getD {α β : Type} (f : List α → β → α) (d : α)
    (l : List β) (acc : List α) (k i : ℕ) (hi : i < acc.length + k) (hk : k ≤ l.length) :
    ((l.take k).foldl (fun w x => w ++ [f w x]) acc).getD i d =
      (l.foldl (fun w x => w ++ [f w x]) acc).getD i d := by
  have hsplit : l = l.take k ++ l.drop k := (List.take_append_drop k l).symm
  conv_rhs => rw [hsplit, List.foldl_append]
  have hlen : ((l.take k).foldl (fun w x => w ++ [f w x]) acc).length = acc.length + k := by
    rw [(foldl_append_spec f (l.take k) acc).1, List.length_take, Nat.min_eq_left hk]
  have hget := (foldl_append_spec f (l.drop k) ((l.take k).foldl (fun w x => w ++ [f w x]) acc)).2.1 i (by omega)
  simp only [List.getD_eq_getElem?_getD, hget]

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := by
  unfold Circuit.wires
  exact (foldl_append_spec (fun w g => g.op.eval (g.inputs.map fun k => w.getD k false)) C.gates x).1

lemma wires_getD_input (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false := by
  unfold Circuit.wires
  have hget := (foldl_append_spec (fun w g => g.op.eval (g.inputs.map fun k => w.getD k false)) C.gates x).2.1 i hi
  rw [List.getD_eq_getElem?_getD, hget, List.getD_eq_getElem?_getD]

lemma isAO2_inputs (C : Circuit) (hAO : IsAO2 26 C) (j : ℕ) (hj : j < C.gates.length) :
    (gateAt C j).inputs = [opnd C j 0, opnd C j 1] ∧
    opnd C j 0 < 26 + j ∧ opnd C j 1 < 26 + j ∧
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) := by
  have hget : C.gates[j]? = some (gateAt C j) := by
    simp only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  have hmem : gateAt C j ∈ C.gates := List.mem_of_getElem? hget
  have hlen : (gateAt C j).inputs.length = 2 := hAO.2.2 (gateAt C j) hmem
  rcases h_eq : (gateAt C j).inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
  · simp [h_eq] at hlen
  · simp [h_eq] at hlen
  · have ha : opnd C j 0 = a := by simp [opnd, h_eq]
    have hb : opnd C j 1 = b := by simp [opnd, h_eq]
    have hrb := hAO.2.1 j hj
    have hrb0 : a < 26 + j := hrb a (by rw [h_eq]; simp)
    have hrb1 : b < 26 + j := hrb b (by rw [h_eq]; simp)
    have hop := hAO.1 (gateAt C j) hmem
    exact ⟨by rw [ha, hb], by omega, by omega, hop⟩
  · simp [h_eq] at hlen

lemma wires_getD_or (C : Circuit) (hAO : IsAO2 26 C) (x : List Bool) (hx : x.length = 26)
    (j : ℕ) (hj : j < C.gates.length) (hor : (gateAt C j).op = GateOp.or) :
    (C.wires x).getD (26 + j) false =
      ((C.wires x).getD (opnd C j 0) false || (C.wires x).getD (opnd C j 1) false) := by
  obtain ⟨hin, h0, h1, _⟩ := isAO2_inputs C hAO j hj
  have hget : C.gates[j]? = some (gateAt C j) := by
    simp only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  unfold Circuit.wires
  have hstep := (foldl_append_spec (fun w g => g.op.eval (g.inputs.map fun k => w.getD k false)) C.gates x).2.2 j (gateAt C j) hget
  rw [hx] at hstep
  rw [List.getD_eq_getElem?_getD, hstep, Option.getD_some, hor, hin]
  simp only [List.map_cons, List.map_nil]
  have ht0 := foldl_append_take_getD (fun w g => g.op.eval (g.inputs.map fun k => w.getD k false)) false C.gates x j (opnd C j 0) (by omega) (by omega)
  have ht1 := foldl_append_take_getD (fun w g => g.op.eval (g.inputs.map fun k => w.getD k false)) false C.gates x j (opnd C j 1) (by omega) (by omega)
  rw [ht0, ht1]
  simp only [GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq]

def qInput (Q : Finset (Fin 13)) : List Bool :=
  (List.ofFn fun p : Fin 13 => decide (p ∈ Q)) ++
    (List.ofFn fun l : Fin 13 => decide (l ∈ missLines singerLines3 Q))

lemma qInput_length (Q : Finset (Fin 13)) : (qInput Q).length = 26 := by
  simp [qInput]

def baseQ : Finset (Fin 13) := {0, 1, 2, 5}

def shiftQ (d : Fin 13) : Finset (Fin 13) := baseQ.image (· + d)

lemma shiftQ_mem_quadrangles (d : Fin 13) : shiftQ d ∈ quadrangles singerLines3 := by
  unfold quadrangles
  rw [Finset.mem_filter, Finset.mem_powersetCard]
  refine ⟨⟨Finset.subset_univ _, ?_⟩, ?_⟩
  · revert d; decide
  · revert d; decide

lemma point_in_shiftQ (p : Fin 13) : p ∈ shiftQ p := by
  revert p
  decide

lemma line_in_missLines_shiftQ (l : Fin 13) : l ∈ missLines singerLines3 (shiftQ (l - 3)) := by
  revert l
  decide

lemma exists_quadrangle_true_at_input (w : ℕ) (hw : w < 26) :
    ∃ Q ∈ quadrangles singerLines3, (qInput Q).getD w false = true := by
  by_cases h13 : w < 13
  · refine ⟨shiftQ ⟨w, h13⟩, shiftQ_mem_quadrangles ⟨w, h13⟩, ?_⟩
    rw [qInput, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [h13]), List.getElem?_ofFn]
    simp [h13, point_in_shiftQ ⟨w, h13⟩]
  · have hsub : w - 13 < 13 := by omega
    refine ⟨shiftQ (⟨w - 13, hsub⟩ - 3), shiftQ_mem_quadrangles _, ?_⟩
    rw [qInput, List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega)]
    simp only [List.length_ofFn, List.getElem?_ofFn, hsub, dite_true, Option.getD_some, decide_eq_true_eq]
    exact line_in_missLines_shiftQ ⟨w - 13, hsub⟩

def orClos (C : Circuit) (hAO : IsAO2 26 C) (w : ℕ) : Finset ℕ × Finset ℕ :=
  if h1 : 26 ≤ w then
    if h2 : w - 26 < C.gates.length then
      match (gateAt C (w - 26)).op with
      | GateOp.or =>
        have hlt0 : opnd C (w - 26) 0 < w := by
          have := (isAO2_inputs C hAO (w - 26) h2).2.1; omega
        have hlt1 : opnd C (w - 26) 1 < w := by
          have := (isAO2_inputs C hAO (w - 26) h2).2.2.1; omega
        let p0 := orClos C hAO (opnd C (w - 26) 0)
        let p1 := orClos C hAO (opnd C (w - 26) 1)
        (insert (w - 26) (p0.1 ∪ p1.1), p0.2 ∪ p1.2)
      | _ => (∅, {w})
    else (∅, ∅)
  else (∅, {w})
termination_by w

lemma orClos_spec (C : Circuit) (hAO : IsAO2 26 C) :
    ∀ w < 26 + C.gates.length,
      let T := (orClos C hAO w).1
      let L := (orClos C hAO w).2
      (∀ t ∈ T, t < C.gates.length ∧ (gateAt C t).op = GateOp.or ∧ 26 + t ≤ w) ∧
      (∀ u ∈ L, u < 26 ∨ ∃ k < C.gates.length, u = 26 + k ∧ (gateAt C k).op = GateOp.and) ∧
      (∀ x : List Bool, x.length = 26 →
        ((C.wires x).getD w false = true ↔ ∃ u ∈ L, (C.wires x).getD u false = true)) ∧
      ((T = ∅ ∧ L = {w}) ∨
        (26 ≤ w ∧ w - 26 ∈ T ∧
          ∀ u ∈ L ∪ (T.erase (w - 26)).image (26 + ·),
            ∃ t ∈ T, u = opnd C t 0 ∨ u = opnd C t 1)) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    unfold orClos
    by_cases h1 : 26 ≤ w
    · have h2 : w - 26 < C.gates.length := by omega
      rw [dif_pos h1, dif_pos h2]
      dsimp only
      have hweq : 26 + (w - 26) = w := by omega
      obtain ⟨_, hlt0, hlt1, hop⟩ := isAO2_inputs C hAO (w - 26) h2
      rcases hop with hand | hor
      · rw [hand]
        dsimp only
        refine ⟨fun t ht => by simp at ht, ?_, ?_, Or.inl ⟨rfl, rfl⟩⟩
        · intro u hu
          simp only [Finset.mem_singleton] at hu
          exact Or.inr ⟨w - 26, h2, by omega, hand⟩
        · intro x _
          simp
      · rw [hor]
        dsimp only
        have ih0 := ih (opnd C (w - 26) 0) (by omega) (by omega)
        have ih1 := ih (opnd C (w - 26) 1) (by omega) (by omega)
        set p0 := orClos C hAO (opnd C (w - 26) 0)
        set p1 := orClos C hAO (opnd C (w - 26) 1)
        refine ⟨?_, ?_, ?_, Or.inr ⟨h1, Finset.mem_insert_self _ _, ?_⟩⟩
        · intro t ht
          rcases Finset.mem_insert.1 ht with rfl | ht'
          · exact ⟨h2, hor, by omega⟩
          · rcases Finset.mem_union.1 ht' with ht0 | ht1
            · obtain ⟨a, b, c⟩ := ih0.1 t ht0
              exact ⟨a, b, by omega⟩
            · obtain ⟨a, b, c⟩ := ih1.1 t ht1
              exact ⟨a, b, by omega⟩
        · intro u hu
          rcases Finset.mem_union.1 hu with hu0 | hu1
          · exact ih0.2.1 u hu0
          · exact ih1.2.1 u hu1
        · intro x hx
          have hval := wires_getD_or C hAO x hx (w - 26) h2 hor
          rw [hweq] at hval
          rw [hval, Bool.or_eq_true, ih0.2.2.1 x hx, ih1.2.2.1 x hx]
          constructor
          · rintro (⟨u, hu, hux⟩ | ⟨u, hu, hux⟩)
            · exact ⟨u, Finset.mem_union_left _ hu, hux⟩
            · exact ⟨u, Finset.mem_union_right _ hu, hux⟩
          · rintro ⟨u, hu, hux⟩
            rcases Finset.mem_union.1 hu with hu0 | hu1
            · exact Or.inl ⟨u, hu0, hux⟩
            · exact Or.inr ⟨u, hu1, hux⟩
        · intro u hu
          have hsub0 : ∀ v ∈ p0.2 ∪ p0.1.image (26 + ·),
              ∃ t ∈ insert (w - 26) (p0.1 ∪ p1.1), v = opnd C t 0 ∨ v = opnd C t 1 := by
            intro v hv
            rcases ih0.2.2.2 with ⟨he0, hl0⟩ | ⟨hge0, hroot0, hcov0⟩
            · rw [he0, hl0] at hv
              simp only [Finset.image_empty, Finset.union_empty, Finset.mem_singleton] at hv
              exact ⟨w - 26, Finset.mem_insert_self _ _, Or.inl hv⟩
            · by_cases hveq : v = opnd C (w - 26) 0
              · exact ⟨w - 26, Finset.mem_insert_self _ _, Or.inl hveq⟩
              · have hv' : v ∈ p0.2 ∪ (p0.1.erase (opnd C (w - 26) 0 - 26)).image (26 + ·) := by
                  rcases Finset.mem_union.1 hv with hvL | hvT
                  · exact Finset.mem_union_left _ hvL
                  · refine Finset.mem_union_right _ ?_
                    rcases Finset.mem_image.1 hvT with ⟨t, ht, rfl⟩
                    exact Finset.mem_image.2 ⟨t, Finset.mem_erase.2 ⟨by omega, ht⟩, rfl⟩
                obtain ⟨t, ht, hvt⟩ := hcov0 v hv'
                exact ⟨t, Finset.mem_insert_of_mem (Finset.mem_union_left _ ht), hvt⟩
          have hsub1 : ∀ v ∈ p1.2 ∪ p1.1.image (26 + ·),
              ∃ t ∈ insert (w - 26) (p0.1 ∪ p1.1), v = opnd C t 0 ∨ v = opnd C t 1 := by
            intro v hv
            rcases ih1.2.2.2 with ⟨he1, hl1⟩ | ⟨hge1, hroot1, hcov1⟩
            · rw [he1, hl1] at hv
              simp only [Finset.image_empty, Finset.union_empty, Finset.mem_singleton] at hv
              exact ⟨w - 26, Finset.mem_insert_self _ _, Or.inr hv⟩
            · by_cases hveq : v = opnd C (w - 26) 1
              · exact ⟨w - 26, Finset.mem_insert_self _ _, Or.inr hveq⟩
              · have hv' : v ∈ p1.2 ∪ (p1.1.erase (opnd C (w - 26) 1 - 26)).image (26 + ·) := by
                  rcases Finset.mem_union.1 hv with hvL | hvT
                  · exact Finset.mem_union_left _ hvL
                  · refine Finset.mem_union_right _ ?_
                    rcases Finset.mem_image.1 hvT with ⟨t, ht, rfl⟩
                    exact Finset.mem_image.2 ⟨t, Finset.mem_erase.2 ⟨by omega, ht⟩, rfl⟩
                obtain ⟨t, ht, hvt⟩ := hcov1 v hv'
                exact ⟨t, Finset.mem_insert_of_mem (Finset.mem_union_right _ ht), hvt⟩
          rcases Finset.mem_union.1 hu with huL | huT
          · rcases Finset.mem_union.1 huL with hu0 | hu1
            · exact hsub0 u (Finset.mem_union_left _ hu0)
            · exact hsub1 u (Finset.mem_union_left _ hu1)
          · rcases Finset.mem_image.1 huT with ⟨t, ht, rfl⟩
            have hne := (Finset.mem_erase.1 ht).1
            have ht' := (Finset.mem_erase.1 ht).2
            rcases Finset.mem_insert.1 ht' with rfl | ht01
            · exact absurd rfl hne
            · rcases Finset.mem_union.1 ht01 with ht0 | ht1
              · exact hsub0 (26 + t) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ ht0))
              · exact hsub1 (26 + t) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ ht1))
    · rw [dif_neg h1]
      dsimp only
      refine ⟨fun t ht => by simp at ht, ?_, ?_, Or.inl ⟨rfl, rfl⟩⟩
      · intro u hu
        simp only [Finset.mem_singleton] at hu
        exact Or.inl (by omega)
      · intro x _
        simp

lemma orClos_card_le (C : Circuit) (hAO : IsAO2 26 C) (w : ℕ) (hw : w < 26 + C.gates.length) :
    (orClos C hAO w).2.card ≤ (orClos C hAO w).1.card + 1 := by
  have hspec := orClos_spec C hAO w hw
  set T := (orClos C hAO w).1
  set L := (orClos C hAO w).2
  rcases hspec.2.2.2 with ⟨hT, hL⟩ | ⟨hge, hroot, hcov⟩
  · rw [hT, hL]; simp
  · have hdisj : Disjoint L ((T.erase (w - 26)).image (26 + ·)) := by
      rw [Finset.disjoint_left]
      intro u huL huT
      rcases Finset.mem_image.1 huT with ⟨t, ht, rfl⟩
      have hor := (hspec.1 t (Finset.mem_of_mem_erase ht)).2.1
      rcases hspec.2.1 (26 + t) huL with hlt | ⟨k, _, heq, hand⟩
      · omega
      · have htk : k = t := by omega
        subst htk
        rw [hor] at hand
        cases hand
    have hsub : L ∪ (T.erase (w - 26)).image (26 + ·) ⊆
        T.biUnion (fun t => ({opnd C t 0, opnd C t 1} : Finset ℕ)) := by
      intro u hu
      obtain ⟨t, ht, hvt⟩ := hcov u hu
      refine Finset.mem_biUnion.2 ⟨t, ht, ?_⟩
      rcases hvt with rfl | rfl <;> simp
    have hcard_union : (L ∪ (T.erase (w - 26)).image (26 + ·)).card = L.card + (T.card - 1) := by
      rw [Finset.card_union_of_disjoint hdisj,
          Finset.card_image_of_injective _ (fun a b h => by omega),
          Finset.card_erase_of_mem hroot]
    have hcard_bi : (T.biUnion (fun t => ({opnd C t 0, opnd C t 1} : Finset ℕ))).card ≤ 2 * T.card := by
      calc (T.biUnion (fun t => ({opnd C t 0, opnd C t 1} : Finset ℕ))).card
          ≤ ∑ t ∈ T, ({opnd C t 0, opnd C t 1} : Finset ℕ).card := Finset.card_biUnion_le
        _ ≤ ∑ _t ∈ T, 2 := Finset.sum_le_sum fun _ _ => Finset.card_le_two
        _ = 2 * T.card := by simp [Nat.mul_comm]
    have hle := Finset.card_le_card hsub
    have hTpos : 1 ≤ T.card := Finset.card_pos.2 ⟨w - 26, hroot⟩
    omega

end PEqualNP.Outside.L_meta_5276

theorem PEqualNP.Outside.L_meta_5276 :
    have x1 : Finset (Fin (13 : ℕ)) → List Bool := fun (x1 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (x2 ∈ x1)) ++ List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (x2 ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x1); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x2 → (∀ x4 ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3, x2.eval (x1 x4) = Bool.false) → (∃ (x5 : List Bool), x5.length = (26 : ℕ) ∧ x2.eval x5 = Bool.true) → ∃ (x6 : Finset ℕ), (∀ x7 ∈ x6, x7 < x2.size ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∀ x9 ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3, (x2.wires (x1 x9)).getD ((26 : ℕ) + x7) Bool.false = Bool.false) ∧ (2 : ℕ) * x6.card ≤ x2.size + (1 : ℕ) ∧ ∀ (x7 : List Bool), x7.length = (26 : ℕ) → (x2.eval x7 = Bool.true ↔ ∃ x9 ∈ x6, (x2.wires x7).getD ((26 : ℕ) + x9) Bool.false = Bool.true) := by
  intro x1 C hAO hquad ⟨x5, hx5len, hx5true⟩
  have hout_lt : C.output < 26 + C.gates.length := by
    by_contra hge
    have hlen : (C.wires x5).length = 26 + C.gates.length := by
      rw [PEqualNP.Outside.L_meta_5276.wires_length, hx5len]
    have hdef : C.eval x5 = false := by
      unfold PEqualNP.CircuitLowerBounds.Circuit.eval
      exact List.getD_eq_default _ _ (by omega)
    rw [hdef] at hx5true
    cases hx5true
  have hspec := PEqualNP.Outside.L_meta_5276.orClos_spec C hAO C.output hout_lt
  set T := (PEqualNP.Outside.L_meta_5276.orClos C hAO C.output).1
  set L := (PEqualNP.Outside.L_meta_5276.orClos C hAO C.output).2
  have hno_inp : ∀ u ∈ L, 26 ≤ u := by
    intro u hu
    by_contra hlt
    obtain ⟨Q, hQ, hQu⟩ := PEqualNP.Outside.L_meta_5276.exists_quadrangle_true_at_input u (by omega)
    have hwire : (C.wires (PEqualNP.Outside.L_meta_5276.qInput Q)).getD u false = true := by
      rw [PEqualNP.Outside.L_meta_5276.wires_getD_input C _ u (by rw [PEqualNP.Outside.L_meta_5276.qInput_length]; omega)]
      exact hQu
    have hev : C.eval (PEqualNP.Outside.L_meta_5276.qInput Q) = true :=
      (hspec.2.2.1 _ (PEqualNP.Outside.L_meta_5276.qInput_length Q)).2 ⟨u, hu, hwire⟩
    have hf : C.eval (PEqualNP.Outside.L_meta_5276.qInput Q) = false := hquad Q hQ
    rw [hf] at hev
    cases hev
  let S : Finset ℕ := L.image (· - 26)
  refine ⟨S, ?_, ?_, ?_⟩
  · intro g hg
    rcases Finset.mem_image.1 hg with ⟨u, hu, rfl⟩
    have hu26 : 26 ≤ u := hno_inp u hu
    rcases hspec.2.1 u hu with hlt | ⟨k, hk, heq, hand⟩
    · omega
    · have hgk : u - 26 = k := by omega
      refine ⟨by simpa [PEqualNP.CircuitLowerBounds.Circuit.size, hgk] using hk, by simpa [hgk] using hand, ?_⟩
      intro Q hQ
      by_contra hne
      have htrue : (C.wires (PEqualNP.Outside.L_meta_5276.qInput Q)).getD (26 + (u - 26)) false = true := by
        cases hval : (C.wires (PEqualNP.Outside.L_meta_5276.qInput Q)).getD (26 + (u - 26)) false
        · exact absurd hval hne
        · rfl
      have htrue' : (C.wires (PEqualNP.Outside.L_meta_5276.qInput Q)).getD u false = true := by
        simpa [Nat.add_sub_of_le hu26] using htrue
      have hev : C.eval (PEqualNP.Outside.L_meta_5276.qInput Q) = true :=
        (hspec.2.2.1 _ (PEqualNP.Outside.L_meta_5276.qInput_length Q)).2 ⟨u, hu, htrue'⟩
      have hf : C.eval (PEqualNP.Outside.L_meta_5276.qInput Q) = false := hquad Q hQ
      rw [hf] at hev
      cases hev
  · have hScard : S.card = L.card := by
      refine Finset.card_image_of_injOn ?_
      intro a ha b hb hab
      have ha26 := hno_inp a ha
      have hb26 := hno_inp b hb
      dsimp only at hab
      omega
    have hLle : L.card ≤ T.card + 1 := PEqualNP.Outside.L_meta_5276.orClos_card_le C hAO C.output hout_lt
    have hdisj : Disjoint S T := by
      rw [Finset.disjoint_left]
      intro g hgS hgT
      rcases Finset.mem_image.1 hgS with ⟨u, hu, rfl⟩
      have hu26 := hno_inp u hu
      have hor := (hspec.1 (u - 26) hgT).2.1
      rcases hspec.2.1 u hu with hlt | ⟨k, _, heq, hand⟩
      · omega
      · have hgk : u - 26 = k := by omega
        rw [hgk, hand] at hor
        cases hor
    have hsub : S ∪ T ⊆ Finset.range C.gates.length := by
      intro g hg
      rw [Finset.mem_range]
      rcases Finset.mem_union.1 hg with hgS | hgT
      · rcases Finset.mem_image.1 hgS with ⟨u, hu, rfl⟩
        have hu26 := hno_inp u hu
        rcases hspec.2.1 u hu with hlt | ⟨k, hk, heq, _⟩
        · omega
        · omega
      · exact (hspec.1 g hgT).1
    have hsum : S.card + T.card ≤ C.gates.length := by
      calc S.card + T.card = (S ∪ T).card := (Finset.card_union_of_disjoint hdisj).symm
        _ ≤ (Finset.range C.gates.length).card := Finset.card_le_card hsub
        _ = C.gates.length := Finset.card_range _
    show 2 * S.card ≤ C.gates.length + 1
    omega
  · intro x hx
    rw [show C.eval x = (C.wires x).getD C.output false from rfl, hspec.2.2.1 x hx]
    constructor
    · rintro ⟨u, hu, hux⟩
      have hu26 := hno_inp u hu
      refine ⟨u - 26, Finset.mem_image_of_mem _ hu, ?_⟩
      simpa [Nat.add_sub_of_le hu26] using hux
    · rintro ⟨g, hg, hgx⟩
      rcases Finset.mem_image.1 hg with ⟨u, hu, rfl⟩
      have hu26 := hno_inp u hu
      refine ⟨u, hu, ?_⟩
      simpa [Nat.add_sub_of_le hu26] using hgx
