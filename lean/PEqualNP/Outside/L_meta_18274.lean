import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18274_aux

open PEqualNP.CircuitLowerBounds

def fw {α : Type} (f : List α → Gate → α) (gs : List Gate) (init : List α) : List α :=
  gs.foldl (fun w g => w ++ [f w g]) init

lemma fw_nil {α : Type} (f : List α → Gate → α) (init : List α) : fw f [] init = init := rfl

lemma fw_cons {α : Type} (f : List α → Gate → α) (g : Gate) (gs : List Gate) (init : List α) :
    fw f (g :: gs) init = fw f gs (init ++ [f init g]) := rfl

lemma fw_append {α : Type} (f : List α → Gate → α) (gs hs : List Gate) (init : List α) :
    fw f (gs ++ hs) init = fw f hs (fw f gs init) := by
  simp [fw, List.foldl_append]

lemma fw_snoc {α : Type} (f : List α → Gate → α) (gs : List Gate) (g : Gate) (init : List α) :
    fw f (gs ++ [g]) init = fw f gs init ++ [f (fw f gs init) g] := by
  rw [fw_append]; rfl

lemma fw_length {α : Type} (f : List α → Gate → α) (gs : List Gate) (init : List α) :
    (fw f gs init).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp [fw_nil]
  | cons g gs ih => rw [fw_cons, ih]; simp; omega

lemma fw_prefix {α : Type} (f : List α → Gate → α) (gs : List Gate) (init : List α) :
    ∃ r, fw f gs init = init ++ r := by
  induction gs generalizing init with
  | nil => exact ⟨[], by simp [fw_nil]⟩
  | cons g gs ih =>
    obtain ⟨r, hr⟩ := ih (init ++ [f init g])
    exact ⟨[f init g] ++ r, by rw [fw_cons, hr]; simp⟩

lemma getD_append_left' {α : Type} (l r : List α) (i : ℕ) (d : α) (h : i < l.length) :
    (l ++ r).getD i d = l.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_take' {α : Type} (l : List α) (m i : ℕ) (d : α) :
    (l.take m).getD i d = if i < m then l.getD i d else d := by
  split_ifs with h
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

lemma fw_take {α : Type} (f : List α → Gate → α) (gs : List Gate) (init : List α) (j : ℕ)
    (hj : j ≤ gs.length) :
    (fw f gs init).take (init.length + j) = fw f (gs.take j) init := by
  have h := List.take_append_drop j gs
  conv_lhs => rw [← h, fw_append]
  obtain ⟨r, hr⟩ := fw_prefix f (gs.drop j) (fw f (gs.take j) init)
  rw [hr]
  have hl : (fw f (gs.take j) init).length = init.length + j := by
    rw [fw_length]; simp; omega
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]

lemma fw_getD_gate {α : Type} (f : List α → Gate → α) (gs : List Gate) (init : List α) (j : ℕ)
    (hj : j < gs.length) (d : α) :
    (fw f gs init).getD (init.length + j) d =
      f ((fw f gs init).take (init.length + j)) gs[j] := by
  rw [fw_take f gs init j hj.le]
  have h : gs = gs.take j ++ [gs[j]] ++ gs.drop (j + 1) := by
    simp
  conv_lhs => rw [h, fw_append, fw_snoc]
  obtain ⟨r, hr⟩ := fw_prefix f (gs.drop (j + 1)) (fw f (gs.take j) init ++ [f (fw f (gs.take j) init) gs[j]])
  rw [hr]
  have hl : (fw f (gs.take j) init).length = init.length + j := by
    rw [fw_length]; simp; omega
  rw [getD_append_left' _ _ _ _ (by simp; omega)]
  simp [List.getD_eq_getElem?_getD, hl]

open PEqualNP.MetaComplexity.NestedCover PEqualNP.ReadTwo

private def evalOne (w : List Bool) (g : Gate) := g.op.eval (g.inputs.map fun i => w.getD i false)

private theorem gate_eq {n : Nat} {C : Circuit} (ao : PEqualNP.TopForm.IsAO2 n C)
    (x : Fin n → Bool) (j : Nat) (hj : j < C.gates.length) :
    wval C x (n+j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (wval C x)) := by
  have h := fw_getD_gate evalOne C.gates (List.ofFn x) j hj false
  simp only [List.length_ofFn] at h
  have hg : gateAt C j = C.gates[j] := by simp [gateAt, List.getD_eq_getElem?_getD, hj]
  change (fw evalOne C.gates (List.ofFn x)).getD (n+j) false = _
  rw [h]
  unfold evalOne
  rw [← hg]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [getD_take', if_pos (ao.2.1 j hj i hi)]
  rfl

open PEqualNP PEqualNP.MetaComplexity
private theorem boundary {E : ℕ → ℕ → Prop} (he : ∀ {a b}, E a b → a < b)
    (Y : ℕ → Bool) {s t : ℕ} (p : Relation.ReflTransGen E s t) (hs : Y s = true) (ht : Y t = false) :
    ∃ a b, s < b ∧ Relation.ReflTransGen E s a ∧ E a b ∧ Relation.ReflTransGen E b t ∧ Y a = true ∧ Y b = false := by
  induction p with
  | refl => simp_all
  | @tail u v pre e ih =>
    cases hu : Y u with
    | false =>
      obtain ⟨a,b,hb,p1,edge,p2,h1,h2⟩ := ih hu
      exact ⟨a,b,hb,p1,edge,p2.tail e,h1,h2⟩
    | true =>
      have le : s ≤ u := by
        clear ih e hu ht
        induction pre with
        | refl => exact le_rfl
        | tail _ ed ih => exact le_trans ih (he ed).le
      exact ⟨u,v,lt_of_le_of_lt le (he e),pre,e,.refl,hu,ht⟩

private theorem crossing : ∀ (n : ℕ) (C : Circuit), TopForm.IsAO2 n C →
      ∀ (x y : Fin n → Bool) (start : ℕ),
      let V := ReadTwo.wval C x
      let Y := ReadTwo.wval C y
      let E := fun a b => ∃ (j : ℕ) (g : Gate), C.gates[j]? = some g ∧
        b = n+j ∧ a ∈ g.inputs ∧ V a = true ∧ V b = true
      Relation.ReflTransGen E start C.output → Y start = true → Y C.output = false →
      ∃ j, start < n+j ∧ Relation.ReflTransGen E start (n+j) ∧ Relation.ReflTransGen E (n+j) C.output ∧
        ReadTwo.isAnd C j ∧ V (n+j) = true ∧
        (∃ a ∈ (NestedCover.gateAt C j).inputs, Y a = true) ∧
        (∃ b ∈ (NestedCover.gateAt C j).inputs, Y b = false) := by
  intro n C ao x y start
  dsimp only
  intro p hstart hend
  let E := fun (a b : ℕ) => ∃ (j : ℕ) (g : Gate), C.gates[j]? = some g ∧
    b = n+j ∧ a ∈ g.inputs ∧ wval C x a = true ∧ wval C x b = true
  have gate {j : ℕ} {g : Gate} (hj : C.gates[j]? = some g) :
      j < C.gates.length ∧ gateAt C j = g := by
    obtain ⟨hl,hg⟩ := List.getElem?_eq_some_iff.mp hj
    exact ⟨hl,by simp [gateAt,List.getD_eq_getElem?_getD,hj]⟩
  have inc {a b} (e : E a b) : a < b := by
    obtain ⟨j,g,hj,rfl,ha,_,_⟩ := e
    apply ao.2.1 j (gate hj).1
    simpa [(gate hj).2] using ha
  obtain ⟨a,b,hb,pre,edge,post,ha,hb'⟩ := boundary (E := E) inc (wval C y) p hstart hend
  obtain ⟨j,g,hj,rfl,hm,_,vx⟩ := edge
  obtain ⟨hl,hg⟩ := gate hj
  have member : g ∈ C.gates := by obtain ⟨i,eq⟩ := List.getElem?_eq_some_iff.mp hj; exact eq ▸ List.getElem_mem ..
  have heq := gate_eq ao y j hl
  rw [hg] at heq
  have op : g.op = .and := by
    rcases ao.1 g member with h|h
    · exact h
    · have anyT : (g.inputs.map (wval C y)).any id = true :=
        List.any_eq_true.mpr ⟨true,List.mem_map.mpr ⟨a,hm,ha⟩,rfl⟩
      simp only [h,GateOp.eval] at heq
      rw [hb', anyT] at heq
      contradiction
  have fv : ∃ u ∈ g.inputs, wval C y u = false := by
    by_contra! h
    have every : (g.inputs.map (wval C y)).all id = true := by
      apply List.all_eq_true.mpr
      intro v hv
      obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hv
      simpa using h u hu
    rw [op] at heq
    change wval C y (n+j) = (g.inputs.map (wval C y)).all id at heq
    rw [hb', every] at heq
    contradiction
  exact ⟨j,hb,pre.tail ⟨j,g,hj,rfl,hm,by assumption,vx⟩,post,⟨hl,hg ▸ op⟩,vx,hg ▸ ⟨a,hm,ha⟩,hg ▸ fv⟩

end PEqualNP.Outside.L_meta_18274_aux

open PEqualNP.Outside.L_meta_18274_aux in
theorem PEqualNP.Outside.L_meta_18274 : (∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsAO2 x1 x2 →     ∀ (x4 x5 : Fin x1 → Bool) (x6 : ℕ),       have x7 : ℕ → Bool := PEqualNP.ReadTwo.wval x2 x4;       have x8 : ℕ → Bool := PEqualNP.ReadTwo.wval x2 x5;       have x9 : ℕ → ℕ → Prop := fun (x9 x10 : ℕ) => ∃ (x11 : ℕ) (x12 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x11]? = Option.some x12 ∧ x10 = x1 + x11 ∧ x9 ∈ x12.inputs ∧ x7 x9 = Bool.true ∧ x7 x10 = Bool.true;       Relation.ReflTransGen x9 x6 x2.output → x8 x6 = Bool.true → x8 x2.output = Bool.false → ∃ (x13 : ℕ), x6 < x1 + x13 ∧ Relation.ReflTransGen x9 x6 (x1 + x13) ∧ Relation.ReflTransGen x9 (x1 + x13) x2.output ∧ PEqualNP.ReadTwo.isAnd x2 x13 ∧ x7 (x1 + x13) = Bool.true ∧ (∃ x14 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x13).inputs, x8 x14 = Bool.true) ∧ ∃ x14 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x13).inputs, x8 x14 = Bool.false) := crossing
