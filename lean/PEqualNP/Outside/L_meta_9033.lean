import Mathlib
import PEqualNP.Defs


namespace PEqualNP.Outside.L_meta_9033_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

private def isAnd : GateOp → Bool
  | GateOp.and => true
  | _ => false

private lemma isAnd_eq_true (op : GateOp) : isAnd op = true ↔ op = GateOp.and := by
  cases op <;> simp [isAnd]

private lemma filter_isAnd_length_eq_card (gs : List Gate) :
    (gs.filter (fun g => isAnd g.op)).length =
      Nat.card {j : Fin gs.length // (gs.get j).op = GateOp.and} := by
  classical
  have hsum : (gs.filter (fun g => isAnd g.op)).length =
      ∑ j : Fin gs.length, if isAnd (gs.get j).op = true then 1 else 0 := by
    induction gs with
    | nil => simp
    | cons g gs ih =>
      simp only [List.get_eq_getElem] at ih ⊢
      change (List.filter (fun g => isAnd g.op) (g :: gs)).length =
          ∑ j : Fin (gs.length + 1), if isAnd ((g :: gs)[j.val]).op = true then 1 else 0
      rw [Fin.sum_univ_succ]
      simp only [List.filter_cons, Fin.val_zero, List.getElem_cons_zero,
        Fin.val_succ, List.getElem_cons_succ, ← ih]
      by_cases hg : isAnd g.op = true <;> simp [hg, Nat.add_comm]
  have hsum' : (∑ j : Fin gs.length, if isAnd (gs.get j).op = true then 1 else 0) =
      ∑ j : Fin gs.length, if (gs.get j).op = GateOp.and then 1 else 0 := by
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [isAnd_eq_true]
  rw [hsum, hsum', Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]

private abbrev Side := Finset (Fin 8) × Finset ℕ

private abbrev GateSpec := Side × Side

private abbrev WireRep := Option Side

private def defSide : Side := (∅, ∅)

private def defRep : WireRep := some defSide

private def defSpec : GateSpec := (defSide, defSide)

private def sideVal (U : Finset (Fin 8)) (gv : List Bool) (s : Side) : Bool :=
  decide ((∃ v ∈ s.1, v ∈ U) ∨ ∃ j ∈ s.2, gv.getD j false = true)

private def repVal (U : Finset (Fin 8)) (gv : List Bool) : WireRep → Bool
  | none => true
  | some s => sideVal U gv s

private def evalStep (U : Finset (Fin 8)) (gv : List Bool) (sp : GateSpec) : List Bool :=
  gv ++ [sideVal U gv sp.1 && sideVal U gv sp.2]

private def evalSpecs (specs : List GateSpec) (U : Finset (Fin 8)) : List Bool :=
  specs.foldl (evalStep U) []

private def SideWF (k : ℕ) (s : Side) : Prop :=
  ∀ j ∈ s.2, j < k

private def RepWF (k : ℕ) : WireRep → Prop
  | none => True
  | some s => SideWF k s

private def SpecsWF (specs : List GateSpec) : Prop :=
  ∀ j < specs.length, SideWF j (specs.getD j defSpec).1 ∧ SideWF j (specs.getD j defSpec).2

private lemma sideWF_mono {k k' : ℕ} (hk : k ≤ k') {s : Side} (h : SideWF k s) : SideWF k' s :=
  fun j hj => lt_of_lt_of_le (h j hj) hk

private lemma repWF_mono {k k' : ℕ} (hk : k ≤ k') {r : WireRep} (h : RepWF k r) : RepWF k' r := by
  cases r with
  | none => trivial
  | some s => exact sideWF_mono hk h

private lemma getD_append_lt {α : Type*} (l : List α) (x d : α) (j : ℕ) (hj : j < l.length) :
    (l ++ [x]).getD j d = l.getD j d := by
  simp [List.getD, List.getElem?_append_left hj]

private lemma getD_append_eq {α : Type*} (l : List α) (x d : α) :
    (l ++ [x]).getD l.length d = x := by
  simp [List.getD]

private lemma getD_append_gt {α : Type*} (l : List α) (x d : α) (j : ℕ) (hj : l.length < j) :
    (l ++ [x]).getD j d = d := by
  have hj' : (l ++ [x]).length ≤ j := by simp; omega
  simp [List.getD, List.getElem?_eq_none hj']

private lemma sideVal_append_of_wf (U : Finset (Fin 8)) (gv : List Bool) (b : Bool) (s : Side)
    (hs : SideWF gv.length s) :
    sideVal U (gv ++ [b]) s = sideVal U gv s := by
  unfold sideVal
  refine decide_eq_decide.mpr ?_
  constructor
  · rintro (h | ⟨j, hj, hgv⟩)
    · exact Or.inl h
    · exact Or.inr ⟨j, hj, by rwa [← getD_append_lt gv b false j (hs j hj)]⟩
  · rintro (h | ⟨j, hj, hgv⟩)
    · exact Or.inl h
    · exact Or.inr ⟨j, hj, by rwa [getD_append_lt gv b false j (hs j hj)]⟩

private lemma repVal_append_of_wf (U : Finset (Fin 8)) (gv : List Bool) (b : Bool) (r : WireRep)
    (hr : RepWF gv.length r) :
    repVal U (gv ++ [b]) r = repVal U gv r := by
  cases r with
  | none => rfl
  | some s => exact sideVal_append_of_wf U gv b s hr

private lemma evalSpecs_length (specs : List GateSpec) (U : Finset (Fin 8)) :
    (evalSpecs specs U).length = specs.length := by
  induction specs using List.reverseRecOn with
  | nil => rfl
  | append_singleton specs sp ih =>
    unfold evalSpecs at ih ⊢
    rw [List.foldl_concat]
    simp [evalStep, ih]

private lemma evalSpecs_concat (specs : List GateSpec) (sp : GateSpec) (U : Finset (Fin 8)) :
    evalSpecs (specs ++ [sp]) U =
      evalSpecs specs U ++ [sideVal U (evalSpecs specs U) sp.1 && sideVal U (evalSpecs specs U) sp.2] := by
  unfold evalSpecs
  rw [List.foldl_concat]
  rfl

private lemma specsWF_init {specs : List GateSpec} {sp : GateSpec} (h : SpecsWF (specs ++ [sp])) :
    SpecsWF specs ∧ SideWF specs.length sp.1 ∧ SideWF specs.length sp.2 := by
  refine ⟨fun j hj => ?_, ?_, ?_⟩
  · have hj' : j < (specs ++ [sp]).length := by simp; omega
    have h1 := h j hj'
    rwa [getD_append_lt specs sp defSpec j hj] at h1
  · have hlt : specs.length < (specs ++ [sp]).length := by simp
    have h1 := (h specs.length hlt).1
    rwa [getD_append_eq] at h1
  · have hlt : specs.length < (specs ++ [sp]).length := by simp
    have h1 := (h specs.length hlt).2
    rwa [getD_append_eq] at h1

private lemma evalSpecs_getD_eq (specs : List GateSpec) (U : Finset (Fin 8)) (hwf : SpecsWF specs)
    (j : ℕ) (hj : j < specs.length) :
    (evalSpecs specs U).getD j false =
      (sideVal U (evalSpecs specs U) (specs.getD j defSpec).1 &&
        sideVal U (evalSpecs specs U) (specs.getD j defSpec).2) := by
  induction specs using List.reverseRecOn generalizing j with
  | nil => simp at hj
  | append_singleton specs sp ih =>
    obtain ⟨hwf0, hwfl, hwfr⟩ := specsWF_init hwf
    rw [evalSpecs_concat]
    have hlen : (evalSpecs specs U).length = specs.length := evalSpecs_length specs U
    simp only [List.length_append, List.length_singleton] at hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
    · rw [getD_append_lt _ _ _ j (hlen ▸ hlt), getD_append_lt specs sp defSpec j hlt]
      have h1 := sideWF_mono (Nat.le_of_lt hlt) (hwf0 j hlt).1
      have h2 := sideWF_mono (Nat.le_of_lt hlt) (hwf0 j hlt).2
      rw [sideVal_append_of_wf U _ _ _ (hlen ▸ h1),
        sideVal_append_of_wf U _ _ _ (hlen ▸ h2)]
      exact ih hwf0 j hlt
    · rw [← hlen, getD_append_eq, hlen, getD_append_eq,
        sideVal_append_of_wf U _ _ _ (hlen ▸ hwfl),
        sideVal_append_of_wf U _ _ _ (hlen ▸ hwfr)]

private def unionTwo : WireRep → WireRep → WireRep
  | none, _ => none
  | _, none => none
  | some (b1, f1), some (b2, f2) => some (b1 ∪ b2, f1 ∪ f2)

private lemma repVal_unionTwo (U : Finset (Fin 8)) (gv : List Bool) (r1 r2 : WireRep) :
    repVal U gv (unionTwo r1 r2) = (repVal U gv r1 || repVal U gv r2) := by
  cases r1 with
  | none => simp [unionTwo, repVal]
  | some s1 =>
    cases r2 with
    | none => simp [unionTwo, repVal]
    | some s2 =>
      rcases s1 with ⟨b1, f1⟩
      rcases s2 with ⟨b2, f2⟩
      simp only [unionTwo, repVal, sideVal]
      rw [Bool.eq_iff_iff, Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq, decide_eq_true_eq]
      constructor
      · rintro (⟨v, hv, hvU⟩ | ⟨j, hj, hgv⟩)
        · rcases Finset.mem_union.mp hv with hv | hv
          · exact Or.inl (Or.inl ⟨v, hv, hvU⟩)
          · exact Or.inr (Or.inl ⟨v, hv, hvU⟩)
        · rcases Finset.mem_union.mp hj with hj | hj
          · exact Or.inl (Or.inr ⟨j, hj, hgv⟩)
          · exact Or.inr (Or.inr ⟨j, hj, hgv⟩)
      · rintro ((⟨v, hv, hvU⟩ | ⟨j, hj, hgv⟩) | (⟨v, hv, hvU⟩ | ⟨j, hj, hgv⟩))
        · exact Or.inl ⟨v, Finset.mem_union_left b2 hv, hvU⟩
        · exact Or.inr ⟨j, Finset.mem_union_left f2 hj, hgv⟩
        · exact Or.inl ⟨v, Finset.mem_union_right b1 hv, hvU⟩
        · exact Or.inr ⟨j, Finset.mem_union_right f1 hj, hgv⟩

private lemma repWF_unionTwo {k : ℕ} {r1 r2 : WireRep} (h1 : RepWF k r1) (h2 : RepWF k r2) :
    RepWF k (unionTwo r1 r2) := by
  cases r1 with
  | none => trivial
  | some s1 =>
    cases r2 with
    | none => trivial
    | some s2 =>
      rcases s1 with ⟨b1, f1⟩
      rcases s2 with ⟨b2, f2⟩
      intro j hj
      rcases Finset.mem_union.mp hj with hj | hj
      · exact h1 j hj
      · exact h2 j hj

private def unionReps (reps : List WireRep) (ins : List ℕ) : WireRep :=
  ins.foldl (fun acc i => unionTwo acc (reps.getD i defRep)) defRep

private lemma repVal_unionReps_aux (U : Finset (Fin 8)) (gv : List Bool) (reps : List WireRep)
    (ins : List ℕ) (acc : WireRep) :
    repVal U gv (ins.foldl (fun a i => unionTwo a (reps.getD i defRep)) acc) =
      (repVal U gv acc || ins.any (fun i => repVal U gv (reps.getD i defRep))) := by
  induction ins generalizing acc with
  | nil => simp
  | cons a ins ih =>
    simp only [List.foldl_cons, List.any_cons]
    rw [ih (unionTwo acc (reps.getD a defRep)), repVal_unionTwo, Bool.or_assoc]

private lemma repVal_defRep (U : Finset (Fin 8)) (gv : List Bool) :
    repVal U gv defRep = false := by
  simp [defRep, defSide, repVal, sideVal]

private lemma repVal_unionReps (U : Finset (Fin 8)) (gv : List Bool) (reps : List WireRep)
    (ins : List ℕ) :
    repVal U gv (unionReps reps ins) = ins.any (fun i => repVal U gv (reps.getD i defRep)) := by
  unfold unionReps
  rw [repVal_unionReps_aux, repVal_defRep, Bool.false_or]

private lemma repWF_defRep (k : ℕ) : RepWF k defRep := by
  intro j hj
  exact absurd hj (Finset.notMem_empty j)

private lemma repWF_unionReps (k : ℕ) (reps : List WireRep) (hreps : ∀ r ∈ reps, RepWF k r)
    (ins : List ℕ) : RepWF k (unionReps reps ins) := by
  have haux : ∀ (l : List ℕ) (acc : WireRep), RepWF k acc →
      RepWF k (l.foldl (fun a i => unionTwo a (reps.getD i defRep)) acc) := by
    intro l
    induction l with
    | nil => intro acc hacc; exact hacc
    | cons a l ih =>
      intro acc hacc
      apply ih
      apply repWF_unionTwo hacc
      by_cases ha : a < reps.length
      · simpa [List.getD, ha] using hreps reps[a] (List.getElem_mem ha)
      · have hge : reps.length ≤ a := Nat.le_of_not_lt ha
        simp only [List.getD, List.getElem?_eq_none hge, Option.getD_none]
        exact repWF_defRep k
  exact haux ins defRep (repWF_defRep k)

private def compileStep (st : List WireRep × List GateSpec) (g : Gate) :
    List WireRep × List GateSpec :=
  match g.op with
  | GateOp.or => (st.1 ++ [unionReps st.1 g.inputs], st.2)
  | GateOp.and =>
    match g.inputs with
    | [] => (st.1 ++ [none], st.2)
    | [a] => (st.1 ++ [st.1.getD a defRep], st.2)
    | a :: b :: _ =>
      match st.1.getD a defRep, st.1.getD b defRep with
      | none, r => (st.1 ++ [r], st.2)
      | l, none => (st.1 ++ [l], st.2)
      | some s1, some s2 => (st.1 ++ [some (∅, {st.2.length})], st.2 ++ [(s1, s2)])
  | _ => (st.1 ++ [defRep], st.2)

private lemma getD_repWF {k : ℕ} {reps : List WireRep} (hreps : ∀ r ∈ reps, RepWF k r) (a : ℕ) :
    RepWF k (reps.getD a defRep) := by
  by_cases ha : a < reps.length
  · simpa [List.getD, ha] using hreps reps[a] (List.getElem_mem ha)
  · have hge : reps.length ≤ a := Nat.le_of_not_lt ha
    simp only [List.getD, List.getElem?_eq_none hge, Option.getD_none]
    exact repWF_defRep k

private lemma compileStep_inv (reps : List WireRep) (specs : List GateSpec)
    (w : Finset (Fin 8) → List Bool) (g : Gate)
    (hg : (g.op = GateOp.and ∧ g.inputs.length ≤ 2) ∨ g.op = GateOp.or)
    (hwf : SpecsWF specs) (hreps : ∀ r ∈ reps, RepWF specs.length r)
    (hlen : ∀ U, (w U).length = reps.length)
    (heq : ∀ U i, repVal U (evalSpecs specs U) (reps.getD i defRep) = (w U).getD i false) :
    let st' := compileStep (reps, specs) g
    let w' := fun U => w U ++ [g.op.eval (g.inputs.map fun i => (w U).getD i false)]
    SpecsWF st'.2 ∧ (∀ r ∈ st'.1, RepWF st'.2.length r) ∧
    (∀ U, (w' U).length = st'.1.length) ∧
    (∀ U i, repVal U (evalSpecs st'.2 U) (st'.1.getD i defRep) = (w' U).getD i false) ∧
    st'.2.length ≤ specs.length + (if isAnd g.op then 1 else 0) := by
  rcases hg with ⟨hop, hlen2⟩ | hop
  · rw [hop]
    rcases hins : g.inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    · simp only [compileStep, GateOp.eval, hop, hins, List.map_nil, List.all_nil, isAnd, ↓reduceIte]
      refine ⟨hwf, ?_, ?_, ?_, Nat.le_add_right _ _⟩
      · intro r hr
        rcases List.mem_append.mp hr with hr | hr
        · exact hreps r hr
        · rw [List.mem_singleton.mp hr]; trivial
      · intro U; simp [hlen U]
      · intro U i
        rcases Nat.lt_trichotomy i reps.length with hlt | rfl | hgt
        · rw [getD_append_lt _ _ _ i hlt, getD_append_lt _ _ _ i (by rw [hlen]; exact hlt)]
          exact heq U i
        · rw [getD_append_eq, ← hlen U, getD_append_eq]
          rfl
        · rw [getD_append_gt _ _ _ i hgt, getD_append_gt _ _ _ i (by rw [hlen]; exact hgt)]
          exact repVal_defRep U _
    · simp only [compileStep, GateOp.eval, hop, hins, List.map_cons, List.map_nil, List.all_cons,
        List.all_nil, id_eq, Bool.and_true, isAnd, ↓reduceIte]
      refine ⟨hwf, ?_, ?_, ?_, Nat.le_add_right _ _⟩
      · intro r hr
        rcases List.mem_append.mp hr with hr | hr
        · exact hreps r hr
        · rw [List.mem_singleton.mp hr]
          exact getD_repWF hreps a
      · intro U; simp [hlen U]
      · intro U i
        rcases Nat.lt_trichotomy i reps.length with hlt | rfl | hgt
        · rw [getD_append_lt _ _ _ i hlt, getD_append_lt _ _ _ i (by rw [hlen]; exact hlt)]
          exact heq U i
        · rw [getD_append_eq, ← hlen U, getD_append_eq]
          exact heq U a
        · rw [getD_append_gt _ _ _ i hgt, getD_append_gt _ _ _ i (by rw [hlen]; exact hgt)]
          exact repVal_defRep U _
    · simp only [compileStep, GateOp.eval, hop, hins, List.map_cons, List.map_nil, List.all_cons,
        List.all_nil, id_eq, Bool.and_true, isAnd, ↓reduceIte]
      have ha_wf : RepWF specs.length (reps.getD a defRep) := getD_repWF hreps a
      have hb_wf : RepWF specs.length (reps.getD b defRep) := getD_repWF hreps b
      cases hra : reps.getD a defRep with
      | none =>
        dsimp only
        have hwa : ∀ U, (w U).getD a false = true := fun U => by
          rw [← heq U a, hra]; rfl
        refine ⟨hwf, ?_, ?_, ?_, Nat.le_add_right _ _⟩
        · intro r hr
          rcases List.mem_append.mp hr with hr | hr
          · exact hreps r hr
          · rw [List.mem_singleton.mp hr]; exact hb_wf
        · intro U; simp [hlen U]
        · intro U i
          rcases Nat.lt_trichotomy i reps.length with hlt | rfl | hgt
          · rw [getD_append_lt _ _ _ i hlt, getD_append_lt _ _ _ i (by rw [hlen]; exact hlt)]
            exact heq U i
          · rw [getD_append_eq, ← hlen U, getD_append_eq, hwa U, Bool.true_and]
            exact heq U b
          · rw [getD_append_gt _ _ _ i hgt, getD_append_gt _ _ _ i (by rw [hlen]; exact hgt)]
            exact repVal_defRep U _
      | some s1 =>
        cases hrb : reps.getD b defRep with
        | none =>
          dsimp only
          have hwb : ∀ U, (w U).getD b false = true := fun U => by
            rw [← heq U b, hrb]; rfl
          refine ⟨hwf, ?_, ?_, ?_, Nat.le_add_right _ _⟩
          · intro r hr
            rcases List.mem_append.mp hr with hr | hr
            · exact hreps r hr
            · rw [List.mem_singleton.mp hr]; rw [← hra]; exact ha_wf
          · intro U; simp [hlen U]
          · intro U i
            rcases Nat.lt_trichotomy i reps.length with hlt | rfl | hgt
            · rw [getD_append_lt _ _ _ i hlt, getD_append_lt _ _ _ i (by rw [hlen]; exact hlt)]
              exact heq U i
            · rw [getD_append_eq, ← hlen U, getD_append_eq, hwb U, Bool.and_true, ← hra]
              exact heq U a
            · rw [getD_append_gt _ _ _ i hgt, getD_append_gt _ _ _ i (by rw [hlen]; exact hgt)]
              exact repVal_defRep U _
        | some s2 =>
          dsimp only
          have hs1 : SideWF specs.length s1 := by rw [hra] at ha_wf; exact ha_wf
          have hs2 : SideWF specs.length s2 := by rw [hrb] at hb_wf; exact hb_wf
          have hwf' : SpecsWF (specs ++ [(s1, s2)]) := by
            intro j hj
            simp only [List.length_append, List.length_singleton] at hj
            rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
            · rw [getD_append_lt specs _ defSpec j hlt]
              exact hwf j hlt
            · rw [getD_append_eq]
              exact ⟨hs1, hs2⟩
          refine ⟨hwf', ?_, ?_, ?_, by simp⟩
          · intro r hr
            rcases List.mem_append.mp hr with hr | hr
            · exact repWF_mono (by simp) (hreps r hr)
            · rw [List.mem_singleton.mp hr]
              intro j hj
              rw [Finset.mem_singleton.mp hj]
              simp
          · intro U; simp [hlen U]
          · intro U i
            have heval : evalSpecs (specs ++ [(s1, s2)]) U =
                evalSpecs specs U ++
                  [sideVal U (evalSpecs specs U) s1 && sideVal U (evalSpecs specs U) s2] :=
              evalSpecs_concat specs (s1, s2) U
            have hspecLen : (evalSpecs specs U).length = specs.length := evalSpecs_length specs U
            rcases Nat.lt_trichotomy i reps.length with hlt | rfl | hgt
            · rw [getD_append_lt _ _ _ i hlt, getD_append_lt _ _ _ i (by rw [hlen]; exact hlt),
                heval, repVal_append_of_wf U _ _ _ (hspecLen ▸ getD_repWF hreps i)]
              exact heq U i
            · rw [getD_append_eq, ← hlen U, getD_append_eq, heval]
              have hva : sideVal U (evalSpecs specs U) s1 = (w U).getD a false := by
                have := heq U a
                rwa [hra] at this
              have hvb : sideVal U (evalSpecs specs U) s2 = (w U).getD b false := by
                have := heq U b
                rwa [hrb] at this
              rw [← hva, ← hvb]
              simp only [repVal, sideVal, Finset.notMem_empty, false_and, exists_false,
                Finset.mem_singleton, exists_eq_left, false_or]
              rw [← hspecLen, getD_append_eq]
              simp
            · rw [getD_append_gt _ _ _ i hgt, getD_append_gt _ _ _ i (by rw [hlen]; exact hgt)]
              exact repVal_defRep U _
    · rw [hins] at hlen2
      simp at hlen2
  · rw [hop]
    simp only [compileStep, GateOp.eval, hop, isAnd, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    refine ⟨hwf, ?_, ?_, ?_, le_rfl⟩
    · intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · exact hreps r hr
      · rw [List.mem_singleton.mp hr]
        exact repWF_unionReps specs.length reps hreps g.inputs
    · intro U; simp [hlen U]
    · intro U i
      rcases Nat.lt_trichotomy i reps.length with hlt | rfl | hgt
      · rw [getD_append_lt _ _ _ i hlt, getD_append_lt _ _ _ i (by rw [hlen]; exact hlt)]
        exact heq U i
      · rw [getD_append_eq, ← hlen U, getD_append_eq, repVal_unionReps]
        rw [List.any_map]
        apply Bool.eq_iff_iff.mpr
        simp only [List.any_eq_true, Function.comp_def, id_eq]
        exact ⟨fun ⟨k, hk, h⟩ => ⟨k, hk, (heq U k) ▸ h⟩,
          fun ⟨k, hk, h⟩ => ⟨k, hk, (heq U k).symm ▸ h⟩⟩
      · rw [getD_append_gt _ _ _ i hgt, getD_append_gt _ _ _ i (by rw [hlen]; exact hgt)]
        exact repVal_defRep U _

private lemma compile_foldl_inv (gs : List Gate)
    (hgates : ∀ g ∈ gs, (g.op = GateOp.and ∧ g.inputs.length ≤ 2) ∨ g.op = GateOp.or)
    (reps : List WireRep) (specs : List GateSpec) (w : Finset (Fin 8) → List Bool)
    (hwf : SpecsWF specs) (hreps : ∀ r ∈ reps, RepWF specs.length r)
    (hlen : ∀ U, (w U).length = reps.length)
    (heq : ∀ U i, repVal U (evalSpecs specs U) (reps.getD i defRep) = (w U).getD i false) :
    let st' := gs.foldl compileStep (reps, specs)
    let w' := fun U => gs.foldl (fun ww g => ww ++ [g.op.eval (g.inputs.map fun i => ww.getD i false)]) (w U)
    SpecsWF st'.2 ∧ (∀ r ∈ st'.1, RepWF st'.2.length r) ∧
    (∀ U, (w' U).length = st'.1.length) ∧
    (∀ U i, repVal U (evalSpecs st'.2 U) (st'.1.getD i defRep) = (w' U).getD i false) ∧
    st'.2.length ≤ specs.length + (gs.filter (fun g => isAnd g.op)).length := by
  induction gs generalizing reps specs w with
  | nil =>
    exact ⟨hwf, hreps, hlen, heq, Nat.le_refl _⟩
  | cons g gs ih =>
    have hg : (g.op = GateOp.and ∧ g.inputs.length ≤ 2) ∨ g.op = GateOp.or :=
      hgates g List.mem_cons_self
    have hrest : ∀ g' ∈ gs, (g'.op = GateOp.and ∧ g'.inputs.length ≤ 2) ∨ g'.op = GateOp.or :=
      fun g' hg' => hgates g' (List.mem_cons_of_mem g hg')
    obtain ⟨hwf1, hreps1, hlen1, heq1, hcnt1⟩ :=
      compileStep_inv reps specs w g hg hwf hreps hlen heq
    obtain ⟨hwf2, hreps2, hlen2, heq2, hcnt2⟩ :=
      ih hrest _ _ _ hwf1 hreps1 hlen1 heq1
    refine ⟨hwf2, hreps2, hlen2, heq2, ?_⟩
    simp only [List.filter_cons]
    cases ha : isAnd g.op <;> simp only [ha, ↓reduceIte, Bool.false_eq_true] at hcnt1 ⊢
    · exact le_trans hcnt2 (by omega)
    · rw [List.length_cons]
      exact le_trans hcnt2 (by omega)

private def toFinSet (k : ℕ) (F : Finset ℕ) : Finset (Fin k) :=
  Finset.univ.filter (fun j : Fin k => j.val ∈ F)

private lemma mem_toFinSet {k : ℕ} {F : Finset ℕ} {j : Fin k} :
    j ∈ toFinSet k F ↔ j.val ∈ F := by
  simp [toFinSet]

private lemma gateVal_eq_evalSpecs_aux (specs : List GateSpec) (hwf : SpecsWF specs)
    (outS : Side) (_hout : SideWF specs.length outS)
    (U : Finset (Fin 8)) :
    let C : AndCountCircuit 8 :=
      { size := specs.length
        leftVars := fun i => (specs.getD i.val defSpec).1.1
        leftGates := fun i => toFinSet specs.length (specs.getD i.val defSpec).1.2
        rightVars := fun i => (specs.getD i.val defSpec).2.1
        rightGates := fun i => toFinSet specs.length (specs.getD i.val defSpec).2.2
        outVars := outS.1
        outGates := toFinSet specs.length outS.2 }
    C.WellFormed ∧ ∀ d (i : Fin C.size), i.val < d → C.gateValFuel U d i = (evalSpecs specs U).getD i.val false := by
  intro C
  have hCwf : C.WellFormed := by
    intro i
    have hsp := hwf i.val i.isLt
    constructor
    · intro j hj
      exact hsp.1 j.val (mem_toFinSet.mp hj)
    · intro j hj
      exact hsp.2 j.val (mem_toFinSet.mp hj)
  refine ⟨hCwf, ?_⟩
  intro d
  induction d with
  | zero => intro i hi; omega
  | succ d ih =>
    intro i hi
    have hsp := hwf i.val i.isLt
    simp only [AndCountCircuit.gateValFuel]
    rw [evalSpecs_getD_eq specs U hwf i.val i.isLt]
    congr 1
    · unfold AndCountCircuit.sideTrue sideVal
      refine decide_eq_decide.mpr ?_
      constructor
      · rintro (h | ⟨j, hj, hji, hgv⟩)
        · exact Or.inl h
        · have hjlt : j.val < d := Nat.lt_of_lt_of_le hji (Nat.lt_succ_iff.mp hi)
          rw [ih j hjlt] at hgv
          exact Or.inr ⟨j.val, mem_toFinSet.mp hj, hgv⟩
      · rintro (h | ⟨j, hj, hgv⟩)
        · exact Or.inl h
        · have hji : j < i.val := hsp.1 j hj
          have hjlt : j < specs.length := Nat.lt_trans hji i.isLt
          refine Or.inr ⟨⟨j, hjlt⟩, mem_toFinSet.mpr hj, hji, ?_⟩
          rw [ih ⟨j, hjlt⟩ (Nat.lt_of_lt_of_le hji (Nat.lt_succ_iff.mp hi))]
          exact hgv
    · unfold AndCountCircuit.sideTrue sideVal
      refine decide_eq_decide.mpr ?_
      constructor
      · rintro (h | ⟨j, hj, hji, hgv⟩)
        · exact Or.inl h
        · have hjlt : j.val < d := Nat.lt_of_lt_of_le hji (Nat.lt_succ_iff.mp hi)
          rw [ih j hjlt] at hgv
          exact Or.inr ⟨j.val, mem_toFinSet.mp hj, hgv⟩
      · rintro (h | ⟨j, hj, hgv⟩)
        · exact Or.inl h
        · have hji : j < i.val := hsp.2 j hj
          have hjlt : j < specs.length := Nat.lt_trans hji i.isLt
          refine Or.inr ⟨⟨j, hjlt⟩, mem_toFinSet.mpr hj, hji, ?_⟩
          rw [ih ⟨j, hjlt⟩ (Nat.lt_of_lt_of_le hji (Nat.lt_succ_iff.mp hi))]
          exact hgv

private def ComputesAdj (C : AndCountCircuit 8) (adj : Fin 8 → Fin 8 → Bool) : Prop :=
  ∀ U : Finset (Fin 8), C.eval U = true ↔ ∃ u ∈ U, ∃ v ∈ U, adj u v = true

private lemma circuit_to_andCount (D : Circuit) (adj : Fin 8 → Fin 8 → Bool)
    (E : List (Fin 8 × Fin 8))
    (hadj : ∀ u v : Fin 8, adj u v = decide ((u, v) ∈ E ∨ (v, u) ∈ E))
    (hgates : ∀ g ∈ D.gates, (g.op = GateOp.and ∧ g.inputs.length ≤ 2) ∨ g.op = GateOp.or)
    (hcard : Nat.card {j : Fin D.gates.length // (D.gates.get j).op = GateOp.and} ≤ 4)
    (hfun : circuitFun 8 D = (fun x : Fin 8 → Bool => E.any (fun p => x p.1 && x p.2))) :
    ∃ C : AndCountCircuit 8, C.WellFormed ∧ C.size ≤ 4 ∧ ComputesAdj C adj := by
  let initReps : List WireRep := List.ofFn (fun v : Fin 8 => some ({v}, (∅ : Finset ℕ)))
  let w0 : Finset (Fin 8) → List Bool := fun U => List.ofFn (fun v : Fin 8 => decide (v ∈ U))
  have hwf0 : SpecsWF ([] : List GateSpec) := fun j hj => by simp at hj
  have hreps0 : ∀ r ∈ initReps, RepWF 0 r := by
    intro r hr
    rcases List.mem_ofFn.mp hr with ⟨v, rfl⟩
    intro j hj
    exact absurd hj (Finset.notMem_empty j)
  have hlen0 : ∀ U, (w0 U).length = initReps.length := fun U => by simp [w0, initReps]
  have heq0 : ∀ U i, repVal U (evalSpecs [] U) (initReps.getD i defRep) = (w0 U).getD i false := by
    intro U i
    by_cases hi : i < 8
    · have hi1 : i < initReps.length := by simp [initReps, hi]
      have hi2 : i < (w0 U).length := by simp [w0, hi]
      simp only [List.getD, List.getElem?_eq_getElem hi1, List.getElem?_eq_getElem hi2,
        Option.getD_some, initReps, w0, List.getElem_ofFn]
      simp [repVal, sideVal]
    · have hi1 : initReps.length ≤ i := by simp [initReps]; omega
      have hi2 : (w0 U).length ≤ i := by simp [w0]; omega
      simp only [List.getD, List.getElem?_eq_none hi1, List.getElem?_eq_none hi2, Option.getD_none]
      exact repVal_defRep U _
  obtain ⟨hwf, hreps, hlen, heq, hsz⟩ :=
    compile_foldl_inv D.gates hgates initReps [] w0 hwf0 hreps0 hlen0 heq0
  let st := D.gates.foldl compileStep (initReps, [])
  have hsz4 : st.2.length ≤ 4 := by
    have hf := filter_isAnd_length_eq_card D.gates
    change st.2.length ≤ ([] : List GateSpec).length + (D.gates.filter (fun g => isAnd g.op)).length at hsz
    simp only [List.length_nil, Nat.zero_add] at hsz
    omega
  have hD_eval : ∀ U : Finset (Fin 8),
      repVal U (evalSpecs st.2 U) (st.1.getD D.output defRep) =
        E.any (fun p => decide (p.1 ∈ U) && decide (p.2 ∈ U)) := by
    intro U
    have h1 := heq U D.output
    change repVal U (evalSpecs st.2 U) (st.1.getD D.output defRep) =
      (D.wires (List.ofFn (fun v : Fin 8 => decide (v ∈ U)))).getD D.output false at h1
    rw [h1]
    have h2 : (D.wires (List.ofFn (fun v : Fin 8 => decide (v ∈ U)))).getD D.output false =
        circuitFun 8 D (fun v : Fin 8 => decide (v ∈ U)) := rfl
    rw [h2, hfun]
  have hnone_false : st.1.getD D.output defRep ≠ none := by
    intro hnone
    have h0 := hD_eval ∅
    rw [hnone] at h0
    simp [repVal] at h0
  cases hrep_out : st.1.getD D.output defRep with
  | none => exact absurd hrep_out hnone_false
  | some outS =>
    have hout_wf : SideWF st.2.length outS := by
      have hr := getD_repWF hreps D.output
      rw [hrep_out] at hr
      exact hr
    let C : AndCountCircuit 8 :=
      { size := st.2.length
        leftVars := fun i => (st.2.getD i.val defSpec).1.1
        leftGates := fun i => toFinSet st.2.length (st.2.getD i.val defSpec).1.2
        rightVars := fun i => (st.2.getD i.val defSpec).2.1
        rightGates := fun i => toFinSet st.2.length (st.2.getD i.val defSpec).2.2
        outVars := outS.1
        outGates := toFinSet st.2.length outS.2 }
    refine ⟨C, ?_, hsz4, ?_⟩
    · exact (gateVal_eq_evalSpecs_aux st.2 hwf outS hout_wf ∅).1
    · intro U
      have haux := gateVal_eq_evalSpecs_aux st.2 hwf outS hout_wf U
      have hgate : ∀ i : Fin C.size, C.gateVal U i = (evalSpecs st.2 U).getD i.val false :=
        fun i => haux.2 st.2.length i i.isLt
      have hCe : C.eval U = E.any (fun p => decide (p.1 ∈ U) && decide (p.2 ∈ U)) := by
        have h3 := hD_eval U
        rw [hrep_out] at h3
        rw [← h3]
        unfold AndCountCircuit.eval repVal sideVal
        refine decide_eq_decide.mpr ?_
        constructor
        · rintro (h | ⟨j, hj, hv⟩)
          · exact Or.inl h
          · rw [hgate j] at hv
            exact Or.inr ⟨j.val, mem_toFinSet.mp hj, hv⟩
        · rintro (h | ⟨j, hj, hv⟩)
          · exact Or.inl h
          · have hjlt : j < st.2.length := hout_wf j hj
            refine Or.inr ⟨⟨j, hjlt⟩, mem_toFinSet.mpr hj, ?_⟩
            rw [hgate ⟨j, hjlt⟩]
            exact hv
      rw [hCe]
      simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨⟨u, v⟩, hpE, huU, hvU⟩
        refine ⟨u, huU, v, hvU, ?_⟩
        rw [hadj u v, decide_eq_true_eq]
        exact Or.inl hpE
      · rintro ⟨u, huU, v, hvU, hadjuv⟩
        rw [hadj u v, decide_eq_true_eq] at hadjuv
        rcases hadjuv with huv | hvu
        · exact ⟨(u, v), huv, huU, hvU⟩
        · exact ⟨(v, u), hvu, hvU, huU⟩

private lemma sideTrue_congr {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v w : Fin k → Bool) (h : ∀ j, j < i → v j = w j) :
    sideTrue U B F i v = sideTrue U B F i w := by
  unfold sideTrue
  refine decide_eq_decide.mpr ?_
  constructor
  · rintro (h1 | ⟨j, hj, hji, hv⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨j, hj, hji, by rw [← h j hji]; exact hv⟩
  · rintro (h1 | ⟨j, hj, hji, hv⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨j, hj, hji, by rw [h j hji]; exact hv⟩

private lemma sideTrue_iff {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v : Fin k → Bool) :
    sideTrue U B F i v = true ↔ ((∃ x ∈ B, x ∈ U) ∨ ∃ j ∈ F, j < i ∧ v j = true) := by
  unfold sideTrue
  exact decide_eq_true_iff

private lemma sideTrue_mono {n k : ℕ} (U U' B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v w : Fin k → Bool) (hU : U ⊆ U') (h : ∀ j, j < i → v j = true → w j = true)
    (hs : sideTrue U B F i v = true) : sideTrue U' B F i w = true := by
  rw [sideTrue_iff] at hs ⊢
  rcases hs with ⟨x, hx, hxU⟩ | ⟨j, hj, hji, hv⟩
  · exact Or.inl ⟨x, hx, hU hxU⟩
  · exact Or.inr ⟨j, hj, hji, h j hji hv⟩

private lemma fuel_succ {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ d : ℕ, ∀ i : Fin C.size, i.val < d →
      gateValFuel C U (d + 1) i = gateValFuel C U d i := by
  intro d
  induction d with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
  | succ d ih =>
    intro i hi
    show (sideTrue U (C.leftVars i) (C.leftGates i) i (gateValFuel C U (d + 1)) &&
        sideTrue U (C.rightVars i) (C.rightGates i) i (gateValFuel C U (d + 1))) =
      (sideTrue U (C.leftVars i) (C.leftGates i) i (gateValFuel C U d) &&
        sideTrue U (C.rightVars i) (C.rightGates i) i (gateValFuel C U d))
    have hc : ∀ j : Fin C.size, j < i → gateValFuel C U (d + 1) j = gateValFuel C U d j := by
      intro j hji
      apply ih
      have : j.val < i.val := hji
      omega
    rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ hc,
      sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ hc]

private lemma gateVal_rec {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal U i = (sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U) &&
      sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateVal U)) :=
  (fuel_succ C U C.size i i.isLt).symm

private lemma gateVal_iff {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal U i = true ↔
      (((∃ x ∈ C.leftVars i, x ∈ U) ∨ ∃ j ∈ C.leftGates i, j < i ∧ C.gateVal U j = true) ∧
       ((∃ x ∈ C.rightVars i, x ∈ U) ∨ ∃ j ∈ C.rightGates i, j < i ∧ C.gateVal U j = true)) := by
  rw [gateVal_rec, Bool.and_eq_true, sideTrue_iff, sideTrue_iff]

private lemma eval_iff {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    C.eval U = true ↔
      ((∃ v ∈ C.outVars, v ∈ U) ∨ ∃ j ∈ C.outGates, C.gateVal U j = true) := by
  unfold AndCountCircuit.eval
  exact decide_eq_true_iff

private lemma fuel_mono {n : ℕ} (C : AndCountCircuit n) (U U' : Finset (Fin n)) (hU : U ⊆ U') :
    ∀ d : ℕ, ∀ i : Fin C.size, gateValFuel C U d i = true → gateValFuel C U' d i = true := by
  intro d
  induction d with
  | zero => intro i h; exact absurd h (by simp [gateValFuel])
  | succ d ih =>
    intro i h
    have h' : (sideTrue U (C.leftVars i) (C.leftGates i) i (gateValFuel C U d) &&
        sideTrue U (C.rightVars i) (C.rightGates i) i (gateValFuel C U d)) = true := h
    show (sideTrue U' (C.leftVars i) (C.leftGates i) i (gateValFuel C U' d) &&
        sideTrue U' (C.rightVars i) (C.rightGates i) i (gateValFuel C U' d)) = true
    rw [Bool.and_eq_true] at h' ⊢
    exact ⟨sideTrue_mono U U' _ _ i _ _ hU (fun j _ => ih j) h'.1,
      sideTrue_mono U U' _ _ i _ _ hU (fun j _ => ih j) h'.2⟩

private lemma gateVal_mono {n : ℕ} (C : AndCountCircuit n) (U U' : Finset (Fin n)) (hU : U ⊆ U')
    (i : Fin C.size) (h : C.gateVal U i = true) : C.gateVal U' i = true :=
  fuel_mono C U U' hU C.size i h

private lemma outVars_empty_adj (C : AndCountCircuit 8) (adj : Fin 8 → Fin 8 → Bool)
    (hirr : ∀ v : Fin 8, adj v v = false) (h : ComputesAdj C adj) : C.outVars = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro v hv
  have h1 : C.eval {v} = true := by
    rw [eval_iff]
    exact Or.inl ⟨v, hv, Finset.mem_singleton_self v⟩
  obtain ⟨a, ha, c, hc, hadj⟩ := (h {v}).1 h1
  rw [Finset.mem_singleton] at ha hc
  rw [ha, hc, hirr v] at hadj
  exact Bool.noConfusion hadj

private lemma eval_iff_of_computes_adj (C : AndCountCircuit 8) (adj : Fin 8 → Fin 8 → Bool)
    (hirr : ∀ v : Fin 8, adj v v = false) (h : ComputesAdj C adj) (U : Finset (Fin 8)) :
    C.eval U = true ↔ ∃ j ∈ C.outGates, C.gateVal U j = true := by
  rw [eval_iff, outVars_empty_adj C adj hirr h]
  constructor
  · rintro (⟨x, hx, _⟩ | h2)
    · exact absurd hx (Finset.notMem_empty x)
    · exact h2
  · exact Or.inr

private def sL {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) (v : Fin n) : Bool :=
  sideTrue {v} (C.leftVars i) (C.leftGates i) i (C.gateVal {v})

private def sR {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) (v : Fin n) : Bool :=
  sideTrue {v} (C.rightVars i) (C.rightGates i) i (C.gateVal {v})

private def normC {n : ℕ} (C : AndCountCircuit n) : AndCountCircuit n where
  size := C.size
  leftVars i := Finset.univ.filter (fun v => sL C i v = true ∧ sR C i v = false)
  leftGates := C.leftGates
  rightVars i := Finset.univ.filter (fun v => sR C i v = true ∧ sL C i v = false)
  rightGates := C.rightGates
  outVars := C.outVars ∪
    Finset.univ.filter (fun v => ∃ j ∈ C.outGates, C.gateVal {v} j = true)
  outGates := C.outGates

private lemma norm_mem_left {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) (x : Fin n) :
    x ∈ (normC C).leftVars i ↔ (sL C i x = true ∧ sR C i x = false) := by
  show x ∈ Finset.univ.filter (fun v => sL C i v = true ∧ sR C i v = false) ↔ _
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ x, h⟩⟩

private lemma norm_mem_right {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) (x : Fin n) :
    x ∈ (normC C).rightVars i ↔ (sR C i x = true ∧ sL C i x = false) := by
  show x ∈ Finset.univ.filter (fun v => sR C i v = true ∧ sL C i v = false) ↔ _
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ x, h⟩⟩

private lemma norm_disjoint {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) :
    Disjoint ((normC C).leftVars i) ((normC C).rightVars i) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  rw [norm_mem_left] at hx
  rw [norm_mem_right] at hx'
  exact Bool.noConfusion (hx.1.symm.trans hx'.2)

private lemma single_gate {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) (v : Fin n) :
    C.gateVal {v} i = true ↔ (sL C i v = true ∧ sR C i v = true) := by
  rw [gateVal_rec, Bool.and_eq_true]
  rfl

private lemma side_split {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size)
    (ih : ∀ j : Fin C.size, j < i →
      (C.gateVal U j = true ↔ (∃ v ∈ U, C.gateVal {v} j = true) ∨ (normC C).gateVal U j = true))
    (B : Finset (Fin n)) (F : Finset (Fin C.size)) :
    sideTrue U B F i (C.gateVal U) = true ↔
      ((∃ v ∈ U, sideTrue {v} B F i (C.gateVal {v}) = true) ∨
        ∃ j ∈ F, j < i ∧ (normC C).gateVal U j = true) := by
  rw [sideTrue_iff]
  constructor
  · rintro (⟨x, hx, hxU⟩ | ⟨j, hj, hji, hv⟩)
    · exact Or.inl ⟨x, hxU, (sideTrue_iff _ _ _ _ _).2
        (Or.inl ⟨x, hx, Finset.mem_singleton_self x⟩)⟩
    · rcases (ih j hji).1 hv with ⟨v, hvU, hg⟩ | hd
      · exact Or.inl ⟨v, hvU, (sideTrue_iff _ _ _ _ _).2 (Or.inr ⟨j, hj, hji, hg⟩)⟩
      · exact Or.inr ⟨j, hj, hji, hd⟩
  · rintro (⟨v, hvU, hs⟩ | ⟨j, hj, hji, hd⟩)
    · rcases (sideTrue_iff _ _ _ _ _).1 hs with ⟨x, hx, hxv⟩ | ⟨j, hj, hji, hg⟩
      · rw [Finset.mem_singleton] at hxv
        exact Or.inl ⟨x, hx, hxv ▸ hvU⟩
      · exact Or.inr ⟨j, hj, hji, gateVal_mono C {v} U
          (Finset.singleton_subset_iff.2 hvU) j hg⟩
    · exact Or.inr ⟨j, hj, hji, (ih j hji).2 (Or.inr hd)⟩

private lemma norm_gate_iff {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) :
    (normC C).gateVal U i = true ↔
      (((∃ x ∈ U, sL C i x = true ∧ sR C i x = false) ∨
          ∃ j ∈ C.leftGates i, j < i ∧ (normC C).gateVal U j = true) ∧
       ((∃ x ∈ U, sR C i x = true ∧ sL C i x = false) ∨
          ∃ j ∈ C.rightGates i, j < i ∧ (normC C).gateVal U j = true)) := by
  have h := gateVal_iff (normC C) U i
  rw [h]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rcases h1 with ⟨x, hx, hxU⟩ | h1
      · exact Or.inl ⟨x, hxU, (norm_mem_left C i x).1 hx⟩
      · exact Or.inr h1
    · rcases h2 with ⟨x, hx, hxU⟩ | h2
      · exact Or.inl ⟨x, hxU, (norm_mem_right C i x).1 hx⟩
      · exact Or.inr h2
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rcases h1 with ⟨x, hxU, hx⟩ | h1
      · exact Or.inl ⟨x, (norm_mem_left C i x).2 hx, hxU⟩
      · exact Or.inr h1
    · rcases h2 with ⟨x, hxU, hx⟩ | h2
      · exact Or.inl ⟨x, (norm_mem_right C i x).2 hx, hxU⟩
      · exact Or.inr h2

private lemma norm_gate {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ i : Fin C.size, (C.gateVal U i = true ↔
      (∃ v ∈ U, C.gateVal {v} i = true) ∨ (normC C).gateVal U i = true) := by
  have key : ∀ m : ℕ, ∀ i : Fin C.size, i.val < m → (C.gateVal U i = true ↔
      (∃ v ∈ U, C.gateVal {v} i = true) ∨ (normC C).gateVal U i = true) := by
    intro m
    induction m with
    | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
    | succ m ih =>
      intro i hi
      have ih' : ∀ j : Fin C.size, j < i → (C.gateVal U j = true ↔
          (∃ v ∈ U, C.gateVal {v} j = true) ∨ (normC C).gateVal U j = true) := by
        intro j hji
        apply ih
        have : j.val < i.val := hji
        omega
      have eL := side_split C U i ih' (C.leftVars i) (C.leftGates i)
      have eR := side_split C U i ih' (C.rightVars i) (C.rightGates i)
      rw [gateVal_rec C U i, Bool.and_eq_true, eL, eR, norm_gate_iff]
      constructor
      · rintro ⟨hl, hr⟩
        by_cases hW : ∃ v ∈ U, C.gateVal {v} i = true
        · exact Or.inl hW
        · refine Or.inr ⟨?_, ?_⟩
          · rcases hl with ⟨v, hvU, hs⟩ | hl
            · refine Or.inl ⟨v, hvU, hs, ?_⟩
              rw [← Bool.not_eq_true]
              intro hs'
              exact hW ⟨v, hvU, (single_gate C i v).2 ⟨hs, hs'⟩⟩
            · exact Or.inr hl
          · rcases hr with ⟨v, hvU, hs⟩ | hr
            · refine Or.inl ⟨v, hvU, hs, ?_⟩
              rw [← Bool.not_eq_true]
              intro hs'
              exact hW ⟨v, hvU, (single_gate C i v).2 ⟨hs', hs⟩⟩
            · exact Or.inr hr
      · rintro (⟨v, hvU, hg⟩ | ⟨hl, hr⟩)
        · have := (single_gate C i v).1 hg
          exact ⟨Or.inl ⟨v, hvU, this.1⟩, Or.inl ⟨v, hvU, this.2⟩⟩
        · refine ⟨?_, ?_⟩
          · rcases hl with ⟨v, hvU, hs, _⟩ | hl
            · exact Or.inl ⟨v, hvU, hs⟩
            · exact Or.inr hl
          · rcases hr with ⟨v, hvU, hs, _⟩ | hr
            · exact Or.inl ⟨v, hvU, hs⟩
            · exact Or.inr hr
  intro i
  exact key (i.val + 1) i (Nat.lt_succ_self _)

private lemma norm_eval {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    (normC C).eval U = C.eval U := by
  rw [Bool.eq_iff_iff, eval_iff, eval_iff]
  have mo : ∀ x, x ∈ (normC C).outVars ↔
      (x ∈ C.outVars ∨ ∃ j ∈ C.outGates, C.gateVal {x} j = true) := by
    intro x
    show x ∈ C.outVars ∪
      Finset.univ.filter (fun v => ∃ j ∈ C.outGates, C.gateVal {v} j = true) ↔ _
    rw [Finset.mem_union, Finset.mem_filter]
    exact ⟨fun h => h.imp id (fun h => h.2), fun h => h.imp id (fun h => ⟨Finset.mem_univ x, h⟩)⟩
  constructor
  · rintro (⟨x, hx, hxU⟩ | ⟨j, hj, hv⟩)
    · rcases (mo x).1 hx with hx | ⟨j, hj, hv⟩
      · exact Or.inl ⟨x, hx, hxU⟩
      · exact Or.inr ⟨j, hj, gateVal_mono C {x} U (Finset.singleton_subset_iff.2 hxU) j hv⟩
    · exact Or.inr ⟨j, hj, (norm_gate C U j).2 (Or.inr hv)⟩
  · rintro (⟨x, hx, hxU⟩ | ⟨j, hj, hv⟩)
    · exact Or.inl ⟨x, (mo x).2 (Or.inl hx), hxU⟩
    · rcases (norm_gate C U j).1 hv with ⟨x, hxU, hg⟩ | hd
      · exact Or.inl ⟨x, (mo x).2 (Or.inr ⟨j, hj, hg⟩), hxU⟩
      · exact Or.inr ⟨j, hj, hd⟩

private lemma exists_norm_adj (C : AndCountCircuit 8) (adj : Fin 8 → Fin 8 → Bool)
    (hirr : ∀ v : Fin 8, adj v v = false) (h : ComputesAdj C adj) :
    ∃ D : AndCountCircuit 8, ComputesAdj D adj ∧ D.size = C.size ∧
      (∀ i, Disjoint (D.leftVars i) (D.rightVars i)) ∧ D.outVars = ∅ := by
  have hc : ComputesAdj (normC C) adj := fun U => by rw [norm_eval]; exact h U
  exact ⟨normC C, hc, rfl, norm_disjoint C, outVars_empty_adj (normC C) adj hirr hc⟩

private lemma first_gate {n : ℕ} (C : AndCountCircuit n) (X : Finset (Fin n)) :
    ∀ i : Fin C.size, C.gateVal X i = true →
      ∃ k : Fin C.size, C.gateVal X k = true ∧ (∃ x ∈ C.leftVars k, x ∈ X) ∧
        (∃ y ∈ C.rightVars k, y ∈ X) := by
  have key : ∀ m : ℕ, ∀ i : Fin C.size, i.val < m → C.gateVal X i = true →
      ∃ k : Fin C.size, C.gateVal X k = true ∧ (∃ x ∈ C.leftVars k, x ∈ X) ∧
        (∃ y ∈ C.rightVars k, y ∈ X) := by
    intro m
    induction m with
    | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
    | succ m ih =>
      intro i hi hv
      have g := (gateVal_iff C X i).1 hv
      have down : ∀ j : Fin C.size, j < i → C.gateVal X j = true →
          ∃ k : Fin C.size, C.gateVal X k = true ∧ (∃ x ∈ C.leftVars k, x ∈ X) ∧
            (∃ y ∈ C.rightVars k, y ∈ X) := by
        intro j hji hjv
        have hlt : j.val < m := by
          have : j.val < i.val := hji
          omega
        exact ih j hlt hjv
      rcases g.1 with hx | ⟨j, _, hji, hjv⟩
      · rcases g.2 with hy | ⟨j, _, hji, hjv⟩
        · exact ⟨i, hv, hx, hy⟩
        · exact down j hji hjv
      · exact down j hji hjv
  intro i
  exact key (i.val + 1) i (Nat.lt_succ_self _)

private lemma wit_gate {n : ℕ} (C : AndCountCircuit n) (I : Finset (Fin n)) (u : Fin n) :
    ∀ m : ℕ, ∀ i : Fin C.size, i.val < m →
      C.gateVal (insert u I) i = true → C.gateVal I i = false →
      ∃ k : Fin C.size, k ≤ i ∧ C.gateVal (insert u I) k = true ∧ C.gateVal I k = false ∧
        ((u ∈ C.leftVars k ∧ Disjoint (C.leftVars k) I) ∨
         (u ∈ C.rightVars k ∧ Disjoint (C.rightVars k) I)) := by
  intro m
  induction m with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi h1 h0
    have side : ∀ (B : Finset (Fin n)) (F : Finset (Fin C.size)),
        ((∃ x ∈ B, x ∈ insert u I) ∨ ∃ j ∈ F, j < i ∧ C.gateVal (insert u I) j = true) →
        ¬ ((∃ x ∈ B, x ∈ I) ∨ ∃ j ∈ F, j < i ∧ C.gateVal I j = true) →
        (u ∈ B ∧ Disjoint B I) ∨
        ∃ j : Fin C.size, j < i ∧ C.gateVal (insert u I) j = true ∧ C.gateVal I j = false := by
      intro B F hT hF
      rcases hT with ⟨x, hx, hxU⟩ | ⟨j, hj, hji, hv⟩
      · rcases Finset.mem_insert.1 hxU with hxu | hxI
        · refine Or.inl ⟨hxu ▸ hx, ?_⟩
          exact Finset.disjoint_left.2 (fun y hy hyI => hF (Or.inl ⟨y, hy, hyI⟩))
        · exact absurd (Or.inl ⟨x, hx, hxI⟩) hF
      · have hjf : C.gateVal I j = false := by
          rw [← Bool.not_eq_true]
          intro hvI
          exact hF (Or.inr ⟨j, hj, hji, hvI⟩)
        exact Or.inr ⟨j, hji, hv, hjf⟩
    have down : (∃ j : Fin C.size, j < i ∧ C.gateVal (insert u I) j = true ∧
        C.gateVal I j = false) →
        ∃ k : Fin C.size, k ≤ i ∧ C.gateVal (insert u I) k = true ∧ C.gateVal I k = false ∧
        ((u ∈ C.leftVars k ∧ Disjoint (C.leftVars k) I) ∨
         (u ∈ C.rightVars k ∧ Disjoint (C.rightVars k) I)) := by
      rintro ⟨j, hji, hv1, hv0⟩
      have hlt : j.val < m := by
        have : j.val < i.val := hji
        omega
      obtain ⟨k, hk, r⟩ := ih j hlt hv1 hv0
      exact ⟨k, le_trans hk (le_of_lt hji), r⟩
    have g1 := (gateVal_iff C (insert u I) i).1 h1
    have g0 : ¬ _ := fun hh => Bool.noConfusion (h0.symm.trans ((gateVal_iff C I i).2 hh))
    by_cases hL : (∃ x ∈ C.leftVars i, x ∈ I) ∨ ∃ j ∈ C.leftGates i, j < i ∧ C.gateVal I j = true
    · have hR : ¬ ((∃ x ∈ C.rightVars i, x ∈ I) ∨
          ∃ j ∈ C.rightGates i, j < i ∧ C.gateVal I j = true) := fun hh => g0 ⟨hL, hh⟩
      rcases side _ _ g1.2 hR with hs | hs
      · exact ⟨i, le_refl i, h1, h0, Or.inr hs⟩
      · exact down hs
    · rcases side _ _ g1.1 hL with hs | hs
      · exact ⟨i, le_refl i, h1, h0, Or.inl hs⟩
      · exact down hs

private lemma wit_adj (C : AndCountCircuit 8) (adj : Fin 8 → Fin 8 → Bool)
    (hirr : ∀ v : Fin 8, adj v v = false) (hC : ComputesAdj C adj)
    (I : Finset (Fin 8)) (hI : ∀ a ∈ I, ∀ c ∈ I, adj a c = false)
    (u x : Fin 8) (hx : x ∈ I) (hux : adj u x = true) :
    ∃ i : Fin C.size, (u ∈ C.leftVars i ∧ Disjoint (C.leftVars i) I) ∨
      (u ∈ C.rightVars i ∧ Disjoint (C.rightVars i) I) := by
  have e1 : C.eval (insert u I) = true :=
    (hC _).2 ⟨u, Finset.mem_insert_self u I, x, Finset.mem_insert_of_mem hx, hux⟩
  obtain ⟨o, ho, hv1⟩ := (eval_iff_of_computes_adj C adj hirr hC _).1 e1
  have hv0 : C.gateVal I o = false := by
    rw [← Bool.not_eq_true]
    intro hv
    have e0 : C.eval I = true := (eval_iff_of_computes_adj C adj hirr hC _).2 ⟨o, ho, hv⟩
    obtain ⟨a, ha, c, hc, hadj⟩ := (hC I).1 e0
    rw [hI a ha c hc] at hadj
    exact Bool.noConfusion hadj
  obtain ⟨k, _, _, _, r⟩ := wit_gate C I u (o.val + 1) o (Nat.lt_succ_self _) hv1 hv0
  exact ⟨k, r⟩

private def sv {n : ℕ} (C : AndCountCircuit n) (X : Finset (Fin n)) (i : Fin C.size) (s : Bool) : Bool :=
  sideTrue X (cond s (C.rightVars i) (C.leftVars i)) (cond s (C.rightGates i) (C.leftGates i)) i
    (C.gateVal X)

private lemma gate_false_iff {n : ℕ} (C : AndCountCircuit n) (X : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal X i = false ↔ (sv C X i false = false ∨ sv C X i true = false) := by
  rw [gateVal_rec, Bool.and_eq_false_iff]
  rfl

private lemma sv_hit {n : ℕ} (C : AndCountCircuit n) (U X : Finset (Fin n)) (hU : U ⊆ X)
    (i : Fin C.size) (s : Bool)
    (h : ¬ Disjoint (cond s (C.rightVars i) (C.leftVars i)) U) : sv C X i s = true := by
  rw [Finset.not_disjoint_iff] at h
  obtain ⟨x, hx, hxU⟩ := h
  exact (sideTrue_iff _ _ _ _ _).2 (Or.inl ⟨x, hx, hU hxU⟩)

private lemma sv_merge {n : ℕ} (C : AndCountCircuit n) (X Y : Finset (Fin n)) (i : Fin C.size)
    (s : Bool) (hX : sv C X i s = false) (hY : sv C Y i s = false)
    (ih : ∀ j : Fin C.size, j < i → C.gateVal X j = false → C.gateVal Y j = false →
      C.gateVal (X ∪ Y) j = false) : sv C (X ∪ Y) i s = false := by
  rw [← Bool.not_eq_true] at hX hY ⊢
  unfold sv at hX hY ⊢
  rw [sideTrue_iff] at hX hY ⊢
  rintro (⟨x, hx, hxU⟩ | ⟨j, hj, hji, hv⟩)
  · rcases Finset.mem_union.1 hxU with h | h
    · exact hX (Or.inl ⟨x, hx, h⟩)
    · exact hY (Or.inl ⟨x, hx, h⟩)
  · have h1 : C.gateVal X j = false := by
      rw [← Bool.not_eq_true]
      exact fun hh => hX (Or.inr ⟨j, hj, hji, hh⟩)
    have h2 : C.gateVal Y j = false := by
      rw [← Bool.not_eq_true]
      exact fun hh => hY (Or.inr ⟨j, hj, hji, hh⟩)
    rw [ih j hji h1 h2] at hv
    exact Bool.noConfusion hv

private noncomputable def codeSide {n : ℕ} (C : AndCountCircuit n) (U X : Finset (Fin n))
    (i : Fin C.size) : Bool :=
  if ¬ Disjoint (C.leftVars i) U then true
  else if ¬ Disjoint (C.rightVars i) U then false
  else sv C X i false

private lemma codeSide_ok {n : ℕ} (C : AndCountCircuit n) (U X : Finset (Fin n)) (hU : U ⊆ X)
    (i : Fin C.size) (h : C.gateVal X i = false) : sv C X i (codeSide C U X i) = false := by
  rw [gate_false_iff] at h
  unfold codeSide
  by_cases hl : ¬ Disjoint (C.leftVars i) U
  · simp only [hl, not_false_eq_true, ↓reduceIte]
    have := sv_hit C U X hU i false hl
    rcases h with h | h
    · rw [this] at h; exact Bool.noConfusion h
    · exact h
  · simp only [not_not.mp hl, not_true_eq_false, ↓reduceIte]
    by_cases hr : ¬ Disjoint (C.rightVars i) U
    · simp only [hr, not_false_eq_true, ↓reduceIte]
      have := sv_hit C U X hU i true hr
      rcases h with h | h
      · exact h
      · rw [this] at h; exact Bool.noConfusion h
    · simp only [not_not.mp hr, not_true_eq_false, ↓reduceIte]
      cases hb : sv C X i false with
      | false => exact hb
      | true =>
        rcases h with h | h
        · rw [hb] at h; exact Bool.noConfusion h
        · exact h

private lemma codeSide_hit {n : ℕ} (C : AndCountCircuit n) (U X Y : Finset (Fin n))
    (i : Fin C.size) (h : ¬ Disjoint (C.leftVars i ∪ C.rightVars i) U) :
    codeSide C U X i = codeSide C U Y i := by
  unfold codeSide
  by_cases hl : ¬ Disjoint (C.leftVars i) U
  · simp only [hl, not_false_eq_true, ↓reduceIte]
  · by_cases hr : ¬ Disjoint (C.rightVars i) U
    · simp only [not_not.mp hl, not_true_eq_false, hr, not_false_eq_true, ↓reduceIte]
    · exfalso
      apply h
      rw [Finset.disjoint_union_left]
      exact ⟨not_not.1 hl, not_not.1 hr⟩

private lemma merge_gate {n : ℕ} (C : AndCountCircuit n) (U X Y : Finset (Fin n)) (hX : U ⊆ X)
    (hY : U ⊆ Y) (hc : ∀ i, codeSide C U X i = codeSide C U Y i) :
    ∀ i : Fin C.size, C.gateVal X i = false → C.gateVal Y i = false →
      C.gateVal (X ∪ Y) i = false := by
  have key : ∀ m : ℕ, ∀ i : Fin C.size, i.val < m → C.gateVal X i = false →
      C.gateVal Y i = false → C.gateVal (X ∪ Y) i = false := by
    intro m
    induction m with
    | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
    | succ m ih =>
      intro i hi h1 h2
      have ih' : ∀ j : Fin C.size, j < i → C.gateVal X j = false → C.gateVal Y j = false →
          C.gateVal (X ∪ Y) j = false := by
        intro j hji
        apply ih
        have : j.val < i.val := hji
        omega
      have c1 := codeSide_ok C U X hX i h1
      have c2 := codeSide_ok C U Y hY i h2
      rw [← hc i] at c2
      have hm := sv_merge C X Y i _ c1 c2 ih'
      rw [gate_false_iff]
      cases hb : codeSide C U X i with
      | false => rw [hb] at hm; exact Or.inl hm
      | true => rw [hb] at hm; exact Or.inr hm
  intro i
  exact key (i.val + 1) i (Nat.lt_succ_self _)

private lemma merge_eval {n : ℕ} (C : AndCountCircuit n) (U X Y : Finset (Fin n)) (hX : U ⊆ X)
    (hY : U ⊆ Y) (hc : ∀ i, codeSide C U X i = codeSide C U Y i)
    (h1 : C.eval X = false) (h2 : C.eval Y = false) : C.eval (X ∪ Y) = false := by
  rw [← Bool.not_eq_true, eval_iff] at h1 h2 ⊢
  rintro (⟨x, hx, hxU⟩ | ⟨j, hj, hv⟩)
  · rcases Finset.mem_union.1 hxU with h | h
    · exact h1 (Or.inl ⟨x, hx, h⟩)
    · exact h2 (Or.inl ⟨x, hx, h⟩)
  · have g1 : C.gateVal X j = false := by
      rw [← Bool.not_eq_true]
      exact fun hh => h1 (Or.inr ⟨j, hj, hh⟩)
    have g2 : C.gateVal Y j = false := by
      rw [← Bool.not_eq_true]
      exact fun hh => h2 (Or.inr ⟨j, hj, hh⟩)
    rw [merge_gate C U X Y hX hY hc j g1 g2] at hv
    exact Bool.noConfusion hv

private lemma proj_count {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) (m : ℕ)
    (M : Fin m → Finset (Fin n)) (hU : ∀ a, U ⊆ M a) (h0 : ∀ a, C.eval (M a) = false)
    (h1 : ∀ a b, a ≠ b → C.eval (M a ∪ M b) = true) :
    m ≤ 2 ^ (Finset.univ.filter
      (fun i : Fin C.size => Disjoint (C.leftVars i ∪ C.rightVars i) U)).card := by
  classical
  let f : Fin m → ({i : Fin C.size // Disjoint (C.leftVars i ∪ C.rightVars i) U} → Bool) :=
    fun a i => codeSide C U (M a) i.1
  have hf : Function.Injective f := by
    intro a b hab
    by_contra hne
    have hc : ∀ i, codeSide C U (M a) i = codeSide C U (M b) i := by
      intro i
      by_cases hi : Disjoint (C.leftVars i ∪ C.rightVars i) U
      · exact congrFun hab ⟨i, hi⟩
      · exact codeSide_hit C U _ _ i hi
    have := merge_eval C U (M a) (M b) (hU a) (hU b) hc (h0 a) (h0 b)
    rw [h1 a b hne] at this
    exact Bool.noConfusion this
  have hcard := Fintype.card_le_of_injective f hf
  rw [Fintype.card_fin, Fintype.card_fun, Fintype.card_bool, Fintype.card_subtype] at hcard
  exact hcard

private def ModelFS (adj : Fin 8 → Fin 8 → Bool) (mis : List (List (Fin 8))) (maxG : Fin 8 → ℕ)
    (W : Fin 8 → Finset (Fin 4 × Bool)) : Prop :=
  (∀ v, (W v).Nonempty ∧ (W v).card ≤ maxG v ∧ ∀ g : Fin 4, ¬ ((g, false) ∈ W v ∧ (g, true) ∈ W v)) ∧
  (∀ u v, adj u v = true → ∃ g b, (g, b) ∈ W u ∧ (g, !b) ∈ W v) ∧
  (∀ I ∈ mis, ∀ u : Fin 8, u ∉ I → ∃ p ∈ W u, ∀ y ∈ I, p ∉ W y)

private def W0 (D : AndCountCircuit 8) (v : Fin 8) : Finset (Fin 4 × Bool) :=
  Finset.univ.filter (fun p : Fin 4 × Bool =>
    if h : p.1.val < D.size then v ∈ cond p.2 (D.rightVars ⟨p.1.val, h⟩) (D.leftVars ⟨p.1.val, h⟩)
    else False)

private lemma mem_W0_left {D : AndCountCircuit 8} {v : Fin 8} {g : Fin 4} :
    (g, false) ∈ W0 D v ↔ ∃ h : g.val < D.size, v ∈ D.leftVars ⟨g.val, h⟩ := by
  simp [W0]

private lemma mem_W0_right {D : AndCountCircuit 8} {v : Fin 8} {g : Fin 4} :
    (g, true) ∈ W0 D v ↔ ∃ h : g.val < D.size, v ∈ D.rightVars ⟨g.val, h⟩ := by
  simp [W0]

private lemma length_filter_finRange {α : Type*} (l : List α) (p : α → Bool) :
    ((List.finRange l.length).filter (fun i => p l[i.val])).length = (l.filter p).length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    change ((List.finRange (t.length + 1)).filter (fun i => p (a :: t)[i.val])).length =
      (List.filter p (a :: t)).length
    rw [List.finRange_succ, List.filter_cons, List.filter_cons]
    simp only [Fin.val_zero, List.getElem_cons_zero, List.filter_map]
    cases ha : p a <;> simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons,
      List.length_map, Function.comp_def, Fin.val_succ, List.getElem_cons_succ, ih]

private lemma modelFS_of_circuit (D : AndCountCircuit 8) (adj : Fin 8 → Fin 8 → Bool)
    (mis : List (List (Fin 8))) (maxG : Fin 8 → ℕ)
    (hsize : D.size ≤ 4) (hcomp : ComputesAdj D adj)
    (hdisj : ∀ i, Disjoint (D.leftVars i) (D.rightVars i)) (_hout : D.outVars = ∅)
    (hirr : ∀ v : Fin 8, adj v v = false)
    (hdeg : ∀ v : Fin 8, ∃ x : Fin 8, adj v x = true)
    (hmis_indep : ∀ I ∈ mis, ∀ a ∈ I, ∀ b ∈ I, adj a b = false)
    (hmis_dom : ∀ I ∈ mis, ∀ u : Fin 8, u ∉ I → ∃ x ∈ I, adj u x = true)
    (hmis_cross : ∀ i j : Fin mis.length, i ≠ j → ∃ u ∈ mis[i.val], ∃ v ∈ mis[j.val], adj u v = true)
    (hcount : ∀ v : Fin 8, maxG v ≤ 3 ∧ 2 ^ (3 - maxG v) < (mis.filter (fun I => I.elem v)).length) :
    ModelFS adj mis maxG (W0 D) := by
  classical
  have hedge : ∀ u v : Fin 8, adj u v = true → ∃ g b, (g, b) ∈ W0 D u ∧ (g, !b) ∈ W0 D v := by
    intro u v huv
    have hev : D.eval {u, v} = true :=
      (hcomp {u, v}).mpr ⟨u, Finset.mem_insert_self _ _, v, Finset.mem_insert_of_mem (Finset.mem_singleton_self _), huv⟩
    obtain ⟨o, _, hgo⟩ := (eval_iff_of_computes_adj D adj hirr hcomp {u, v}).mp hev
    obtain ⟨i, _, ⟨x, hxL, hxuv⟩, ⟨y, hyR, hyuv⟩⟩ := first_gate D {u, v} o hgo
    have hxy : x ≠ y := fun he => (Finset.disjoint_left.mp (hdisj i) hxL) (he ▸ hyR)
    let g : Fin 4 := ⟨i.val, lt_of_lt_of_le i.isLt hsize⟩
    rcases Finset.mem_insert.mp hxuv with rfl | hx_v
    · have hy_v : y = v := by
        rcases Finset.mem_insert.mp hyuv with rfl | h
        · exact absurd rfl hxy
        · exact Finset.mem_singleton.mp h
      subst hy_v
      exact ⟨g, false, mem_W0_left.mpr ⟨i.isLt, hxL⟩, mem_W0_right.mpr ⟨i.isLt, hyR⟩⟩
    · have hx_v' : x = v := Finset.mem_singleton.mp hx_v
      subst hx_v'
      have hy_u : y = u := by
        rcases Finset.mem_insert.mp hyuv with rfl | h
        · rfl
        · exact absurd (Finset.mem_singleton.mp h).symm hxy
      subst hy_u
      exact ⟨g, true, mem_W0_right.mpr ⟨i.isLt, hyR⟩, mem_W0_left.mpr ⟨i.isLt, hxL⟩⟩
  refine ⟨fun v => ⟨?_, ?_, ?_⟩, hedge, ?_⟩
  · obtain ⟨x, hvx⟩ := hdeg v
    obtain ⟨g, b, hmem, _⟩ := hedge v x hvx
    exact ⟨(g, b), hmem⟩
  · let sub := (List.finRange mis.length).filter (fun i => mis[i.val].elem v)
    have hsub_nodup : sub.Nodup := (List.nodup_finRange mis.length).filter _
    let M : Fin sub.length → Finset (Fin 8) := fun a => (mis[sub[a.val].val]).toFinset
    have hU : ∀ a, {v} ⊆ M a := by
      intro a
      rw [Finset.singleton_subset_iff]
      have ha_mem : sub[a.val] ∈ sub := List.getElem_mem a.isLt
      have hfil := (List.mem_filter.mp ha_mem).2
      exact List.mem_toFinset.mpr (List.mem_of_elem_eq_true hfil)
    have h0 : ∀ a, D.eval (M a) = false := by
      intro a
      rw [← Bool.not_eq_true]
      intro ht
      obtain ⟨x, hx, y, hy, hxy⟩ := (hcomp _).mp ht
      have hI := hmis_indep mis[sub[a.val].val] (List.getElem_mem sub[a.val].isLt)
        x (List.mem_toFinset.mp hx) y (List.mem_toFinset.mp hy)
      rw [hxy] at hI
      exact Bool.noConfusion hI
    have h1 : ∀ a b, a ≠ b → D.eval (M a ∪ M b) = true := by
      intro a b hab
      have hne : sub[a.val] ≠ sub[b.val] := by
        intro heq
        have hlt := hsub_nodup.getElem_inj_iff.mp heq
        exact hab (Fin.ext hlt)
      obtain ⟨x, hx, y, hy, hxy⟩ := hmis_cross sub[a.val] sub[b.val] hne
      exact (hcomp _).mpr ⟨x, Finset.mem_union_left _ (List.mem_toFinset.mpr hx),
        y, Finset.mem_union_right _ (List.mem_toFinset.mpr hy), hxy⟩
    have hpc := proj_count D {v} sub.length M hU h0 h1
    let freeG := Finset.univ.filter (fun i : Fin D.size => Disjoint (D.leftVars i ∪ D.rightVars i) {v})
    let usedG := Finset.univ.filter (fun i : Fin D.size => ¬ Disjoint (D.leftVars i ∪ D.rightVars i) {v})
    have hWcard : (W0 D v).card = usedG.card := by
      refine Finset.card_bij (fun p hp => ⟨p.1.val, ?_⟩) ?_ ?_ ?_
      · rcases p with ⟨g, b⟩
        cases b
        · exact (mem_W0_left.mp hp).1
        · exact (mem_W0_right.mp hp).1
      · rintro ⟨g, b⟩ hp
        simp only [usedG, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.disjoint_singleton_right, not_not, Finset.mem_union]
        cases b
        · exact Or.inl (mem_W0_left.mp hp).2
        · exact Or.inr (mem_W0_right.mp hp).2
      · rintro ⟨g1, b1⟩ hp1 ⟨g2, b2⟩ hp2 heq
        have hp1' : g1.val = g2.val := congrArg (fun x : Fin D.size => x.val) heq
        have hg : g1 = g2 := Fin.ext hp1'
        apply Prod.ext hg
        cases b1 <;> cases b2
        · rfl
        · exfalso
          obtain ⟨h1, hL⟩ := mem_W0_left.mp hp1
          obtain ⟨h2, hR⟩ := mem_W0_right.mp hp2
          have heqf : (⟨g2.val, h2⟩ : Fin D.size) = ⟨g1.val, h1⟩ := Fin.ext hp1'.symm
          exact Finset.disjoint_left.mp (hdisj ⟨g1.val, h1⟩) hL (heqf ▸ hR)
        · exfalso
          obtain ⟨h1, hR⟩ := mem_W0_right.mp hp1
          obtain ⟨h2, hL⟩ := mem_W0_left.mp hp2
          have heqf : (⟨g2.val, h2⟩ : Fin D.size) = ⟨g1.val, h1⟩ := Fin.ext hp1'.symm
          exact Finset.disjoint_left.mp (hdisj ⟨g1.val, h1⟩) (heqf ▸ hL) hR
        · rfl
      · intro i hi
        simp only [usedG, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.disjoint_singleton_right, not_not, Finset.mem_union] at hi
        rcases hi with hL | hR
        · refine ⟨(⟨i.val, lt_of_lt_of_le i.isLt hsize⟩, false), ?_, Fin.ext rfl⟩
          exact mem_W0_left.mpr ⟨i.isLt, hL⟩
        · refine ⟨(⟨i.val, lt_of_lt_of_le i.isLt hsize⟩, true), ?_, Fin.ext rfl⟩
          exact mem_W0_right.mpr ⟨i.isLt, hR⟩
    have hsplit : freeG.card + usedG.card = D.size := by
      have h1 : usedG = Finset.univ \ freeG := by
        ext i
        simp [freeG, usedG]
      rw [h1, add_comm, Finset.card_sdiff_add_card_eq_card (Finset.subset_univ freeG),
        Finset.card_univ, Fintype.card_fin]
    have hsub_len : sub.length = (mis.filter (fun I => I.elem v)).length :=
      length_filter_finRange mis (fun I => I.elem v)
    obtain ⟨hmax3, hpow⟩ := hcount v
    rw [← hsub_len] at hpow
    have hpow2 : 2 ^ (3 - maxG v) < 2 ^ freeG.card := lt_of_lt_of_le hpow hpc
    have hlt_exp : 3 - maxG v < freeG.card := (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp hpow2
    omega
  · intro g ⟨hL, hR⟩
    obtain ⟨h1, hvL⟩ := mem_W0_left.mp hL
    obtain ⟨_, hvR⟩ := mem_W0_right.mp hR
    exact Finset.disjoint_left.mp (hdisj ⟨g.val, h1⟩) hvL hvR
  · intro I hI u hu
    obtain ⟨x, hxI, hux⟩ := hmis_dom I hI u hu
    obtain ⟨i, hside⟩ := wit_adj D adj hirr hcomp I.toFinset
      (fun a ha b hb => hmis_indep I hI a (List.mem_toFinset.mp ha) b (List.mem_toFinset.mp hb))
      u x (List.mem_toFinset.mpr hxI) hux
    let g : Fin 4 := ⟨i.val, lt_of_lt_of_le i.isLt hsize⟩
    rcases hside with ⟨huL, hdisjI⟩ | ⟨huR, hdisjI⟩
    · refine ⟨(g, false), mem_W0_left.mpr ⟨i.isLt, huL⟩, fun y hy hmem => ?_⟩
      obtain ⟨_, hyL⟩ := mem_W0_left.mp hmem
      exact Finset.disjoint_left.mp hdisjI hyL (List.mem_toFinset.mpr hy)
    · refine ⟨(g, true), mem_W0_right.mpr ⟨i.isLt, huR⟩, fun y hy hmem => ?_⟩
      obtain ⟨_, hyR⟩ := mem_W0_right.mp hmem
      exact Finset.disjoint_left.mp hdisjI hyR (List.mem_toFinset.mpr hy)

private def swapGate (g0 g : Fin 4) : Fin 4 :=
  if g = 0 then g0 else if g = g0 then 0 else g

private def permGB (g0 : Fin 4) (b0 : Bool) (p : Fin 4 × Bool) : Fin 4 × Bool :=
  (swapGate g0 p.1, if p.1 = g0 then (p.2 != b0) else p.2)

private lemma permGB_self : ∀ (g0 : Fin 4) (b0 : Bool), permGB g0 b0 (g0, b0) = (0, false) := by
  decide

private lemma permGB_inj : ∀ (g0 : Fin 4) (b0 : Bool) (p q : Fin 4 × Bool),
    permGB g0 b0 p = permGB g0 b0 q → p = q := by
  decide

private lemma permGB_flip : ∀ (g0 : Fin 4) (b0 : Bool) (g : Fin 4) (b : Bool),
    (permGB g0 b0 (g, !b)).1 = (permGB g0 b0 (g, b)).1 ∧
    (permGB g0 b0 (g, !b)).2 = !(permGB g0 b0 (g, b)).2 := by
  decide

private lemma permGB_opp_pair : ∀ (g0 : Fin 4) (b0 : Bool) (p q : Fin 4 × Bool) (g : Fin 4),
    permGB g0 b0 p = (g, false) → permGB g0 b0 q = (g, true) → p.1 = q.1 ∧ p.2 = !q.2 := by
  decide

private lemma modelFS_sym (adj : Fin 8 → Fin 8 → Bool) (mis : List (List (Fin 8))) (maxG : Fin 8 → ℕ)
    (W : Fin 8 → Finset (Fin 4 × Bool)) (hW : ModelFS adj mis maxG W)
    (v0 : Fin 8) (hv0 : maxG v0 = 1) :
    ∃ W' : Fin 8 → Finset (Fin 4 × Bool), ModelFS adj mis maxG W' ∧ W' v0 = {((0 : Fin 4), false)} := by
  classical
  have hcard1 : (W v0).card = 1 := by
    have hne := (hW.1 v0).1.card_pos
    have hle := (hW.1 v0).2.1
    omega
  obtain ⟨⟨g0, b0⟩, hv0eq⟩ := Finset.card_eq_one.mp hcard1
  let W' : Fin 8 → Finset (Fin 4 × Bool) := fun v => (W v).image (permGB g0 b0)
  have hinj : Function.Injective (permGB g0 b0) := fun p q h => permGB_inj g0 b0 p q h
  refine ⟨W', ⟨?_, ?_, ?_⟩, ?_⟩
  · intro v
    refine ⟨?_, ?_, ?_⟩
    · obtain ⟨p, hp⟩ := (hW.1 v).1
      exact ⟨permGB g0 b0 p, Finset.mem_image_of_mem _ hp⟩
    · rw [Finset.card_image_of_injective _ hinj]
      exact (hW.1 v).2.1
    · intro g ⟨hp1, hp2⟩
      obtain ⟨p, hp, hpeq⟩ := Finset.mem_image.mp hp1
      obtain ⟨q, hq, hqeq⟩ := Finset.mem_image.mp hp2
      obtain ⟨hg, hb⟩ := permGB_opp_pair g0 b0 p q g hpeq hqeq
      have hpf : (p.1, false) ∈ W v := by
        cases hq2 : q.2
        · have hq' : q = (p.1, false) := Prod.ext hg.symm hq2
          exact hq' ▸ hq
        · rw [hq2] at hb
          have hp' : p = (p.1, false) := Prod.ext rfl hb
          exact hp' ▸ hp
      have hpt : (p.1, true) ∈ W v := by
        cases hq2 : q.2
        · rw [hq2] at hb
          have hp' : p = (p.1, true) := Prod.ext rfl hb
          exact hp' ▸ hp
        · have hq' : q = (p.1, true) := Prod.ext hg.symm hq2
          exact hq' ▸ hq
      exact (hW.1 v).2.2 p.1 ⟨hpf, hpt⟩
  · intro u v huv
    obtain ⟨g, b, hgu, hgv⟩ := hW.2.1 u v huv
    obtain ⟨hf1, hf2⟩ := permGB_flip g0 b0 g b
    refine ⟨(permGB g0 b0 (g, b)).1, (permGB g0 b0 (g, b)).2,
      Finset.mem_image_of_mem _ hgu, ?_⟩
    rw [← hf1, ← hf2]
    exact Finset.mem_image_of_mem _ hgv
  · intro I hI u hu
    obtain ⟨p, hpu, hpI⟩ := hW.2.2 I hI u hu
    refine ⟨permGB g0 b0 p, Finset.mem_image_of_mem _ hpu, fun y hy hmem => ?_⟩
    obtain ⟨q, hq, hqeq⟩ := Finset.mem_image.mp hmem
    rw [permGB_inj g0 b0 q p hqeq] at hq
    exact hpI y hy hq
  · simp only [W', hv0eq, Finset.image_singleton, permGB_self]

private def pack8 (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) : ℕ :=
  (if b0 then 1 else 0) + (if b1 then 2 else 0) + (if b2 then 4 else 0) + (if b3 then 8 else 0) +
  (if b4 then 16 else 0) + (if b5 then 32 else 0) + (if b6 then 64 else 0) + (if b7 then 128 else 0)

private def card8 (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) : ℕ :=
  (if b0 then 1 else 0) + (if b1 then 1 else 0) + (if b2 then 1 else 0) + (if b3 then 1 else 0) +
  (if b4 then 1 else 0) + (if b5 then 1 else 0) + (if b6 then 1 else 0) + (if b7 then 1 else 0)

private def disj8 (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) : Bool :=
  !(b0 && b1) && !(b2 && b3) && !(b4 && b5) && !(b6 && b7)

private def maskOf (S : Finset (Fin 4 × Bool)) : ℕ :=
  pack8 (decide ((0, false) ∈ S)) (decide ((0, true) ∈ S))
        (decide ((1, false) ∈ S)) (decide ((1, true) ∈ S))
        (decide ((2, false) ∈ S)) (decide ((2, true) ∈ S))
        (decide ((3, false) ∈ S)) (decide ((3, true) ∈ S))

private def oppMask (m : ℕ) : ℕ :=
  ((m &&& 85) <<< 1) ||| ((m &&& 170) >>> 1)

private def valid1 : List ℕ :=
  [1, 2, 4, 8, 16, 32, 64, 128]

private def valid2 : List ℕ :=
  [1, 2, 4, 5, 6, 8, 9, 10, 16, 17, 18, 20, 24, 32, 33, 34, 36, 40,
   64, 65, 66, 68, 72, 80, 96, 128, 129, 130, 132, 136, 144, 160]

private def valid3 : List ℕ :=
  [1, 2, 4, 5, 6, 8, 9, 10, 16, 17, 18, 20, 21, 22, 24, 25, 26, 32, 33, 34, 36, 37, 38,
   40, 41, 42, 64, 65, 66, 68, 69, 70, 72, 73, 74, 80, 81, 82, 84, 88, 96, 97, 98, 100,
   104, 128, 129, 130, 132, 133, 134, 136, 137, 138, 144, 145, 146, 148, 152, 160, 161, 162, 164, 168]

private def candsFor (mg : ℕ) : List ℕ :=
  if mg ≤ 1 then valid1 else if mg = 2 then valid2 else valid3

private lemma pack8_lt :
    ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool, pack8 b0 b1 b2 b3 b4 b5 b6 b7 < 256 := by
  decide +kernel

private lemma testBit_pack8 :
    ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool, ∀ (g : Fin 4) (s : Bool),
      (pack8 b0 b1 b2 b3 b4 b5 b6 b7).testBit (2 * g.val + if s then 1 else 0) =
        match g.val, s with
        | 0, false => b0
        | 0, true => b1
        | 1, false => b2
        | 1, true => b3
        | 2, false => b4
        | 2, true => b5
        | _, false => b6
        | _, true => b7 := by
  decide +kernel

private lemma testBit_oppMask :
    ∀ (m : Fin 256) (g : Fin 4) (s : Bool),
      (oppMask m.val).testBit (2 * g.val + if s then 1 else 0) =
        m.val.testBit (2 * g.val + if !s then 1 else 0) := by
  decide +kernel

private lemma pack8_mem_candsFor :
    ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool, ∀ mg : Fin 4,
      1 ≤ card8 b0 b1 b2 b3 b4 b5 b6 b7 →
      card8 b0 b1 b2 b3 b4 b5 b6 b7 ≤ mg.val →
      disj8 b0 b1 b2 b3 b4 b5 b6 b7 = true →
      pack8 b0 b1 b2 b3 b4 b5 b6 b7 ∈ candsFor mg.val := by
  decide +kernel

private lemma maskOf_lt (S : Finset (Fin 4 × Bool)) : maskOf S < 256 :=
  pack8_lt _ _ _ _ _ _ _ _

private lemma testBit_maskOf (S : Finset (Fin 4 × Bool)) (g : Fin 4) (s : Bool) :
    (maskOf S).testBit (2 * g.val + if s then 1 else 0) = decide ((g, s) ∈ S) := by
  unfold maskOf
  rw [testBit_pack8]
  fin_cases g <;> cases s <;> rfl

private lemma maskOf_card (S : Finset (Fin 4 × Bool)) :
    S.card = card8
      (decide ((0, false) ∈ S)) (decide ((0, true) ∈ S))
      (decide ((1, false) ∈ S)) (decide ((1, true) ∈ S))
      (decide ((2, false) ∈ S)) (decide ((2, true) ∈ S))
      (decide ((3, false) ∈ S)) (decide ((3, true) ∈ S)) := by
  have hc : S.card = ∑ p : Fin 4 × Bool, if p ∈ S then 1 else 0 := by
    rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [hc, Fintype.sum_prod_type, Fin.sum_univ_four]
  simp only [Fintype.sum_bool, Fin.isValue, decide_eq_true_eq, card8]
  omega

private lemma maskOf_mem_candsFor (S : Finset (Fin 4 × Bool)) (mg : ℕ) (hmg : mg ≤ 3)
    (hne : S.Nonempty) (hcard : S.card ≤ mg)
    (hdisj : ∀ g : Fin 4, ¬ ((g, false) ∈ S ∧ (g, true) ∈ S)) :
    maskOf S ∈ candsFor mg := by
  have h1 : 1 ≤ S.card := hne.card_pos
  rw [maskOf_card S] at h1 hcard
  have hd : disj8
      (decide (((0 : Fin 4), false) ∈ S)) (decide (((0 : Fin 4), true) ∈ S))
      (decide (((1 : Fin 4), false) ∈ S)) (decide (((1 : Fin 4), true) ∈ S))
      (decide (((2 : Fin 4), false) ∈ S)) (decide (((2 : Fin 4), true) ∈ S))
      (decide (((3 : Fin 4), false) ∈ S)) (decide (((3 : Fin 4), true) ∈ S)) = true := by
    simp only [disj8, Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
      decide_eq_false_iff_not]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · have := hdisj 0; tauto
    · have := hdisj 1; tauto
    · have := hdisj 2; tauto
    · have := hdisj 3; tauto
  exact pack8_mem_candsFor _ _ _ _ _ _ _ _ ⟨mg, by omega⟩ h1 hcard hd

private lemma maskOf_singleton_zero : maskOf {((0 : Fin 4), false)} = 1 := by
  unfold maskOf
  simp [pack8]

private lemma oppMask_and_ne_zero (S1 S2 : Finset (Fin 4 × Bool)) (g : Fin 4) (b : Bool)
    (h1 : (g, b) ∈ S1) (h2 : (g, !b) ∈ S2) :
    (oppMask (maskOf S1) &&& maskOf S2) ≠ 0 := by
  let k := 2 * g.val + if !b then 1 else 0
  have hb1 : (oppMask (maskOf S1)).testBit k = true := by
    have ht := testBit_oppMask ⟨maskOf S1, maskOf_lt S1⟩ g (!b)
    rw [Bool.not_not] at ht
    change (oppMask (maskOf S1)).testBit k = (maskOf S1).testBit (2 * g.val + if b then 1 else 0) at ht
    rw [ht, testBit_maskOf, decide_eq_true_eq]
    exact h1
  have hb2 : (maskOf S2).testBit k = true := by
    rw [testBit_maskOf, decide_eq_true_eq]
    exact h2
  intro hz
  have ht := congrArg (fun z : ℕ => z.testBit k) hz
  rw [Nat.testBit_and, hb1, hb2, Nat.zero_testBit] at ht
  exact Bool.noConfusion ht

private lemma or_ne_of_testBit (m1 m2 k : ℕ) (h1 : m1.testBit k = true) (h2 : m2.testBit k = false) :
    (m1 ||| m2) ≠ m2 := by
  intro heq
  have ht := congrArg (fun z : ℕ => z.testBit k) heq
  rw [Nat.testBit_or, h1, h2] at ht
  exact Bool.noConfusion ht

private def lookupMask (assigned : List (Fin 8 × ℕ)) (v : Fin 8) : Option ℕ :=
  match assigned with
  | [] => none
  | (u, m) :: rest => if u = v then some m else lookupMask rest v

private def checkPair (adj : Fin 8 → Fin 8 → Bool) (v : Fin 8) (m om : ℕ) : List (Fin 8 × ℕ) → Bool
  | [] => true
  | (u, mu) :: rest =>
      (!adj v u || (om &&& mu) != 0) &&
      ((m ||| mu) != mu) &&
      ((mu ||| m) != m) &&
      checkPair adj v m om rest

private def unionOpt (assigned : List (Fin 8 × ℕ)) : List (Fin 8) → Option ℕ
  | [] => some 0
  | y :: ys =>
      match lookupMask assigned y, unionOpt assigned ys with
      | some my, some acc => some (my ||| acc)
      | _, _ => none

private def checkMis (assigned : List (Fin 8 × ℕ)) (I : List (Fin 8)) : Bool :=
  match unionOpt assigned I with
  | none => true
  | some um =>
      assigned.all (fun p => if I.elem p.1 then true else (p.2 ||| um) != um)

private def checkMisAll (mis : List (List (Fin 8))) (assigned : List (Fin 8 × ℕ)) : Bool :=
  mis.all (fun I => checkMis assigned I)

private def dfs (adj : Fin 8 → Fin 8 → Bool) (mis : List (List (Fin 8))) (maxG : Fin 8 → ℕ)
    (assigned : List (Fin 8 × ℕ)) : List (Fin 8) → Bool
  | [] => true
  | v :: rest =>
      let cands := match assigned with
        | [] => [1]
        | _ => candsFor (maxG v)
      cands.any (fun m =>
        let om := oppMask m
        checkPair adj v m om assigned &&
        let assigned2 := (v, m) :: assigned
        checkMisAll mis assigned2 &&
        dfs adj mis maxG assigned2 rest)

private def unionMask (w : Fin 8 → ℕ) (I : List (Fin 8)) : ℕ :=
  I.foldr (fun y acc => w y ||| acc) 0

private lemma testBit_unionMask (w : Fin 8 → ℕ) (I : List (Fin 8)) (k : ℕ) :
    (unionMask w I).testBit k = true ↔ ∃ y ∈ I, (w y).testBit k = true := by
  induction I with
  | nil => simp [unionMask]
  | cons y ys ih =>
    simp only [unionMask, List.foldr_cons, Nat.testBit_or, Bool.or_eq_true, List.mem_cons]
    change ((w y).testBit k = true ∨ (unionMask w ys).testBit k = true) ↔ _
    rw [ih]
    constructor
    · rintro (h | ⟨z, hz, hzk⟩)
      · exact ⟨y, Or.inl rfl, h⟩
      · exact ⟨z, Or.inr hz, hzk⟩
    · rintro ⟨z, rfl | hz, hzk⟩
      · exact Or.inl hzk
      · exact Or.inr ⟨z, hz, hzk⟩

private lemma unionMask_testBit_false (w : Fin 8 → ℕ) (I : List (Fin 8)) (k : ℕ)
    (h : ∀ y ∈ I, (w y).testBit k = false) :
    (unionMask w I).testBit k = false := by
  rw [← Bool.not_eq_true]
  intro ht
  obtain ⟨y, hy, hyk⟩ := (testBit_unionMask w I k).mp ht
  rw [h y hy] at hyk
  exact Bool.noConfusion hyk

private lemma lookupMask_eq_some (w : Fin 8 → ℕ) (assigned : List (Fin 8 × ℕ))
    (hmap : ∀ p ∈ assigned, p.2 = w p.1) (y : Fin 8) (my : ℕ)
    (h : lookupMask assigned y = some my) : my = w y := by
  induction assigned with
  | nil => simp [lookupMask] at h
  | cons p rest ih =>
    rcases p with ⟨u, mu⟩
    simp only [lookupMask] at h
    by_cases huv : u = y
    · simp only [huv, ↓reduceIte, Option.some.injEq] at h
      subst h
      subst huv
      exact hmap (u, mu) List.mem_cons_self
    · simp only [huv, ↓reduceIte] at h
      exact ih (fun q hq => hmap q (List.mem_cons_of_mem _ hq)) h

private lemma unionOpt_eq_some (w : Fin 8 → ℕ) (assigned : List (Fin 8 × ℕ))
    (hmap : ∀ p ∈ assigned, p.2 = w p.1) (I : List (Fin 8)) (um : ℕ)
    (h : unionOpt assigned I = some um) : um = unionMask w I := by
  induction I generalizing um with
  | nil =>
    simp only [unionOpt, Option.some.injEq] at h
    subst h
    rfl
  | cons y ys ih =>
    simp only [unionOpt] at h
    cases hl : lookupMask assigned y with
    | none => simp [hl] at h
    | some my =>
      cases hu : unionOpt assigned ys with
      | none => simp [hl, hu] at h
      | some acc =>
        simp only [hl, hu, Option.some.injEq] at h
        subst h
        rw [lookupMask_eq_some w assigned hmap y my hl, ih acc hu]
        rfl

private lemma checkPair_sound (adj : Fin 8 → Fin 8 → Bool) (mis : List (List (Fin 8)))
    (maxG : Fin 8 → ℕ) (W : Fin 8 → Finset (Fin 4 × Bool)) (hW : ModelFS adj mis maxG W)
    (hmis_sep : ∀ u v : Fin 8, u ≠ v → ∃ I ∈ mis, v ∈ I ∧ u ∉ I)
    (v : Fin 8) (assigned : List (Fin 8 × ℕ))
    (hmap : ∀ p ∈ assigned, p.2 = maskOf (W p.1))
    (hne : ∀ p ∈ assigned, p.1 ≠ v) :
    checkPair adj v (maskOf (W v)) (oppMask (maskOf (W v))) assigned = true := by
  induction assigned with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨u, mu⟩
    have hmu : mu = maskOf (W u) := hmap (u, mu) List.mem_cons_self
    have huv : u ≠ v := hne (u, mu) List.mem_cons_self
    simp only [checkPair, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      bne_iff_ne, ne_eq]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ih (fun q hq => hmap q (List.mem_cons_of_mem _ hq))
      (fun q hq => hne q (List.mem_cons_of_mem _ hq))⟩
    · by_cases hadj : adj v u = true
      · right
        obtain ⟨g, b, hgv, hgu⟩ := hW.2.1 v u hadj
        rw [hmu]
        exact oppMask_and_ne_zero (W v) (W u) g b hgv hgu
      · left
        exact Bool.eq_false_iff.mpr hadj
    · obtain ⟨I, hI, huI, hvI⟩ := hmis_sep v u huv.symm
      obtain ⟨⟨g, s⟩, hgv, hgI⟩ := hW.2.2 I hI v hvI
      have hgu : (g, s) ∉ W u := hgI u huI
      rw [hmu]
      refine or_ne_of_testBit (maskOf (W v)) (maskOf (W u)) (2 * g.val + if s then 1 else 0) ?_ ?_
      · rw [testBit_maskOf, decide_eq_true_eq]; exact hgv
      · rw [testBit_maskOf, decide_eq_false_iff_not]; exact hgu
    · obtain ⟨I, hI, hvI, huI⟩ := hmis_sep u v huv
      obtain ⟨⟨g, s⟩, hgu, hgI⟩ := hW.2.2 I hI u huI
      have hgv : (g, s) ∉ W v := hgI v hvI
      rw [hmu]
      refine or_ne_of_testBit (maskOf (W u)) (maskOf (W v)) (2 * g.val + if s then 1 else 0) ?_ ?_
      · rw [testBit_maskOf, decide_eq_true_eq]; exact hgu
      · rw [testBit_maskOf, decide_eq_false_iff_not]; exact hgv

private lemma checkMisAll_sound (adj : Fin 8 → Fin 8 → Bool) (mis : List (List (Fin 8)))
    (maxG : Fin 8 → ℕ) (W : Fin 8 → Finset (Fin 4 × Bool)) (hW : ModelFS adj mis maxG W)
    (assigned : List (Fin 8 × ℕ)) (hmap : ∀ p ∈ assigned, p.2 = maskOf (W p.1)) :
    checkMisAll mis assigned = true := by
  rw [checkMisAll, List.all_eq_true]
  intro I hI
  unfold checkMis
  cases hu : unionOpt assigned I with
  | none => rfl
  | some um =>
    have hum := unionOpt_eq_some (fun x => maskOf (W x)) assigned hmap I um hu
    rw [List.all_eq_true]
    intro p hp
    cases hel : I.elem p.1 with
    | true => simp
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, bne_iff_ne, ne_eq]
      have hp_not : p.1 ∉ I := fun h => by
        rw [List.elem_eq_true_of_mem h] at hel
        exact Bool.noConfusion hel
      obtain ⟨⟨g, s⟩, hgp, hgI⟩ := hW.2.2 I hI p.1 hp_not
      rw [hmap p hp, hum]
      let k := 2 * g.val + if s then 1 else 0
      refine or_ne_of_testBit (maskOf (W p.1)) (unionMask (fun x => maskOf (W x)) I) k ?_ ?_
      · rw [testBit_maskOf, decide_eq_true_eq]; exact hgp
      · apply unionMask_testBit_false
        intro y hy
        rw [testBit_maskOf, decide_eq_false_iff_not]
        exact hgI y hy

private lemma dfs_sound (adj : Fin 8 → Fin 8 → Bool) (mis : List (List (Fin 8)))
    (maxG : Fin 8 → ℕ) (hmaxG : ∀ v, maxG v ≤ 3)
    (W : Fin 8 → Finset (Fin 4 × Bool)) (hW : ModelFS adj mis maxG W)
    (hmis_sep : ∀ u v : Fin 8, u ≠ v → ∃ I ∈ mis, v ∈ I ∧ u ∉ I)
    (v0 : Fin 8) (hv0 : W v0 = {((0 : Fin 4), false)}) :
    ∀ (rem : List (Fin 8)) (assigned : List (Fin 8 × ℕ)),
      rem.Nodup →
      (∀ p ∈ assigned, p.2 = maskOf (W p.1)) →
      (∀ p ∈ assigned, p.1 ∉ rem) →
      (assigned = [] → ∃ t, rem = v0 :: t) →
      dfs adj mis maxG assigned rem = true := by
  intro rem
  induction rem with
  | nil =>
    intro _ _ _ _ _
    rfl
  | cons v rest ih =>
    intro assigned hnodup hmap hdisj hhead
    simp only [dfs, List.any_eq_true]
    refine ⟨maskOf (W v), ?_, ?_⟩
    · cases assigned with
      | nil =>
        obtain ⟨t, ht⟩ := hhead rfl
        have hvv0 : v = v0 := by injection ht
        rw [hvv0, hv0, maskOf_singleton_zero]
        simp
      | cons _ _ =>
        exact maskOf_mem_candsFor (W v) (maxG v) (hmaxG v) (hW.1 v).1 (hW.1 v).2.1 (hW.1 v).2.2
    · have hne : ∀ p ∈ assigned, p.1 ≠ v := fun p hp heq =>
        hdisj p hp (heq ▸ List.mem_cons_self)
      have hpair : checkPair adj v (maskOf (W v)) (oppMask (maskOf (W v))) assigned = true :=
        checkPair_sound adj mis maxG W hW hmis_sep v assigned hmap hne
      have hmap2 : ∀ p ∈ ((v, maskOf (W v)) :: assigned), p.2 = maskOf (W p.1) := by
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hp'
        · rfl
        · exact hmap p hp'
      have hmis2 : checkMisAll mis ((v, maskOf (W v)) :: assigned) = true :=
        checkMisAll_sound adj mis maxG W hW ((v, maskOf (W v)) :: assigned) hmap2
      have hrest : dfs adj mis maxG ((v, maskOf (W v)) :: assigned) rest = true := by
        apply ih ((v, maskOf (W v)) :: assigned) (List.nodup_cons.mp hnodup).2 hmap2
        · intro p hp
          rcases List.mem_cons.mp hp with rfl | hp'
          · exact (List.nodup_cons.mp hnodup).1
          · exact fun hr => hdisj p hp' (List.mem_cons_of_mem v hr)
        · intro hnil; cases hnil
      rw [Bool.and_eq_true, Bool.and_eq_true]
      exact ⟨hpair, ⟨hmis2, hrest⟩⟩

private lemma no_circuit_of_unsat (adj : Fin 8 → Fin 8 → Bool) (E : List (Fin 8 × Fin 8))
    (mis : List (List (Fin 8))) (maxG : Fin 8 → ℕ) (order : List (Fin 8)) (v0 : Fin 8)
    (hadj : ∀ u v : Fin 8, adj u v = decide ((u, v) ∈ E ∨ (v, u) ∈ E))
    (hirr : ∀ v : Fin 8, adj v v = false)
    (hdeg : ∀ v : Fin 8, ∃ x : Fin 8, adj v x = true)
    (hmis_indep : ∀ I ∈ mis, ∀ a ∈ I, ∀ b ∈ I, adj a b = false)
    (hmis_dom : ∀ I ∈ mis, ∀ u : Fin 8, u ∉ I → ∃ x ∈ I, adj u x = true)
    (hmis_cross : ∀ i j : Fin mis.length, i ≠ j → ∃ u ∈ mis[i.val], ∃ v ∈ mis[j.val], adj u v = true)
    (hmis_sep : ∀ u v : Fin 8, u ≠ v → ∃ I ∈ mis, v ∈ I ∧ u ∉ I)
    (hcount : ∀ v : Fin 8, maxG v ≤ 3 ∧ 2 ^ (3 - maxG v) < (mis.filter (fun I => I.elem v)).length)
    (hnodup : order.Nodup)
    (hhead : ∃ t, order = v0 :: t)
    (hv0max : maxG v0 = 1)
    (hunsat : dfs adj mis maxG [] order = false) :
    ¬ ∃ D : Circuit,
      (∀ g ∈ D.gates, (g.op = GateOp.and ∧ g.inputs.length ≤ 2) ∨ g.op = GateOp.or) ∧
      Nat.card {j : Fin D.gates.length // (D.gates.get j).op = GateOp.and} ≤ 4 ∧
      circuitFun 8 D = (fun x : Fin 8 → Bool => E.any (fun p => x p.1 && x p.2)) := by
  rintro ⟨D, hgates, hcard, hfun⟩
  obtain ⟨C, _, hCsz, hCcomp⟩ := circuit_to_andCount D adj E hadj hgates hcard hfun
  obtain ⟨C', hC'comp, hC'sz, hdisj, hout⟩ := exists_norm_adj C adj hirr hCcomp
  have hW0 : ModelFS adj mis maxG (W0 C') :=
    modelFS_of_circuit C' adj mis maxG (hC'sz ▸ hCsz) hC'comp hdisj hout
      hirr hdeg hmis_indep hmis_dom hmis_cross hcount
  obtain ⟨W', hW', hv0eq⟩ := modelFS_sym adj mis maxG (W0 C') hW0 v0 hv0max
  have htrue := dfs_sound adj mis maxG (fun v => (hcount v).1) W' hW' hmis_sep v0 hv0eq
    order [] hnodup (fun _ h => by simp at h) (fun _ h => by simp at h) (fun _ => hhead)
  rw [hunsat] at htrue
  exact Bool.noConfusion htrue

private def adjOfMask (rows : Fin 8 → ℕ) (u v : Fin 8) : Bool :=
  (rows u).testBit v.val

private def edgesT1 : List (Fin 8 × Fin 8) :=
  [(0, 1), (0, 2), (0, 3), (1, 4), (2, 5), (2, 7), (3, 6), (4, 6), (4, 7), (5, 7), (6, 7)]

private def adjT1 : Fin 8 → Fin 8 → Bool :=
  adjOfMask ![14, 17, 161, 65, 194, 132, 152, 116]

private def misT1 : List (List (Fin 8)) :=
  [[1, 2, 3], [2, 3, 4], [1, 3, 5], [0, 4, 5], [3, 4, 5],
   [1, 2, 6], [0, 5, 6], [1, 5, 6], [0, 7], [1, 3, 7]]

private def maxGT1 : Fin 8 → ℕ :=
  ![2, 1, 2, 1, 2, 1, 2, 3]

private def orderT1 : List (Fin 8) :=
  [1, 0, 4, 3, 2, 5, 6, 7]

private lemma adjT1_eq :
    ∀ u v : Fin 8, adjT1 u v = decide ((u, v) ∈ edgesT1 ∨ (v, u) ∈ edgesT1) := by
  decide +kernel

private lemma dfs_T1 : dfs adjT1 misT1 maxGT1 [] orderT1 = false := by
  decide +kernel

private lemma no_T1 :
    ¬ ∃ D : Circuit,
      (∀ g ∈ D.gates, (g.op = GateOp.and ∧ g.inputs.length ≤ 2) ∨ g.op = GateOp.or) ∧
      Nat.card {j : Fin D.gates.length // (D.gates.get j).op = GateOp.and} ≤ 4 ∧
      circuitFun 8 D = (fun x : Fin 8 → Bool =>
        (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 2 && x 7) ||
        (x 3 && x 6) || (x 4 && x 6) || (x 4 && x 7) || (x 5 && x 7) || (x 6 && x 7)) := by
  have hfun : (fun x : Fin 8 → Bool =>
      (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 2 && x 7) ||
      (x 3 && x 6) || (x 4 && x 6) || (x 4 && x 7) || (x 5 && x 7) || (x 6 && x 7)) =
      (fun x : Fin 8 → Bool => edgesT1.any (fun p => x p.1 && x p.2)) := by
    funext x
    simp only [edgesT1, List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc]
  rw [hfun]
  exact no_circuit_of_unsat adjT1 edgesT1 misT1 maxGT1 orderT1 1 adjT1_eq
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    ⟨[0, 4, 3, 2, 5, 6, 7], rfl⟩ rfl dfs_T1

lemma t1_and_count_ge_five (D : Circuit)
    (hgates : ∀ g ∈ D.gates, (g.op = GateOp.and ∧ g.inputs.length ≤ 2) ∨ g.op = GateOp.or)
    (hfun : circuitFun 8 D = (fun x : Fin 8 → Bool => edgesT1.any (fun p => x p.1 && x p.2))) :
    5 ≤ Nat.card {j : Fin D.gates.length // (D.gates.get j).op = GateOp.and} := by
  have hnot := no_circuit_of_unsat adjT1 edgesT1 misT1 maxGT1 orderT1 1 adjT1_eq
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    ⟨[0, 4, 3, 2, 5, 6, 7], rfl⟩ rfl dfs_T1
  by_contra h
  apply hnot
  exact ⟨D, hgates, by omega, hfun⟩


def sample (k : Fin 40) (v : Fin 8) : Bool :=
  (([1065151898146, 2147418115, 21653750532, 34144976944,
      581968119809, 663661903884, 103293914128, 414195942664] : List Nat).getD v.val 0).testBit k.val

def targetFun (x : Fin 8 → Bool) : Bool :=
  edgesT1.any (fun p => x p.1 && x p.2)

set_option maxHeartbeats 4000000 in
lemma sample_coverage : ∀ x : Fin 8 → Bool,
    (targetFun x = true → ∃ k : Fin 40,
      (36671 : Nat).testBit k.val = true ∧ ∀ v, sample k v = true → x v = true) ∧
    (targetFun x = false → ∃ k : Fin 40,
      (36671 : Nat).testBit k.val = false ∧ ∀ v, x v = true → sample k v = true) := by
  decide +kernel

lemma samples_determine (f : (Fin 8 → Bool) → Bool)
    (hmono : ∀ x y, (∀ v, x v = true → y v = true) → f x = true → f y = true)
    (hsample : ∀ k : Fin 40, f (sample k) = (36671 : Nat).testBit k.val) :
    f = targetFun := by
  funext x
  obtain ⟨hpos, hneg⟩ := sample_coverage x
  cases ht : targetFun x with
  | false =>
      cases hf : f x with
      | false => rfl
      | true =>
          obtain ⟨k, hk, hle⟩ := hneg ht
          have h := hmono x (sample k) hle hf
          rw [hsample, hk] at h
          contradiction
  | true =>
      obtain ⟨k, hk, hle⟩ := hpos ht
      exact hmono (sample k) x hle (by rw [hsample, hk])

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp

lemma gateOp_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l₁ l₂ : List Bool) (hlen : l₁.length = l₂.length)
    (hle : ∀ i, l₁.getD i false = true → l₂.getD i false = true) :
    op.eval l₁ = true → op.eval l₂ = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, id_eq]
    intro h b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      have hi1 : i < l₁.length := by omega
      rw [List.getD_eq_getElem _ _ hi1]
      exact h _ (List.getElem_mem hi1)
    have h2 := hle i h1
    rwa [List.getD_eq_getElem _ _ hi] at h2
  · simp only [GateOp.eval, List.any_eq_true, id_eq]
    rintro ⟨b, hb, rfl⟩
    obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      rw [List.getD_eq_getElem _ _ hi]; exact hbi
    have h2 := hle i h1
    have hi2 : i < l₂.length := by omega
    rw [List.getD_eq_getElem _ _ hi2] at h2
    exact ⟨l₂[i], List.getElem_mem hi2, h2⟩

lemma wiresFrom_mono (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w₁ w₂ : List Bool), w₁.length = w₂.length →
      (∀ i, w₁.getD i false = true → w₂.getD i false = true) →
      ∀ i, (wiresFrom gs w₁).getD i false = true → (wiresFrom gs w₂).getD i false = true := by
  induction gs with
  | nil =>
    intro w₁ w₂ _ hle i hi
    exact hle i hi
  | cons g gs ih =>
    intro w₁ w₂ hlen hle i hi
    have hstep1 : wiresFrom (g :: gs) w₁ =
        wiresFrom gs (w₁ ++ [g.op.eval (g.inputs.map fun j => w₁.getD j false)]) := rfl
    have hstep2 : wiresFrom (g :: gs) w₂ =
        wiresFrom gs (w₂ ++ [g.op.eval (g.inputs.map fun j => w₂.getD j false)]) := rfl
    rw [hstep1] at hi
    rw [hstep2]
    apply ih (fun g' hg' => hmono g' (List.mem_cons_of_mem g hg')) _ _ (by simp [hlen]) _ i hi
    intro j hj
    by_cases hlt : j < w₁.length
    · rw [List.getD_append _ _ _ _ hlt] at hj
      rw [List.getD_append _ _ _ _ (by omega)]
      exact hle j hj
    · by_cases heq : j = w₁.length
      · subst heq
        rw [getD_snoc_eq] at hj
        rw [hlen, getD_snoc_eq]
        exact gateOp_eval_mono g.op (hmono g List.mem_cons_self)
          (g.inputs.map fun k => w₁.getD k false) (g.inputs.map fun k => w₂.getD k false)
          (by simp) (by
            intro t ht
            by_cases ht_lt : t < g.inputs.length
            · rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)] at ht
              rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)]
              simp only [List.getElem_map] at ht ⊢
              exact hle _ ht
            · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt ht_lt)] at ht
              exact Bool.noConfusion ht) hj
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
        exact Bool.noConfusion hj

lemma circuit_mono (D : Circuit)
    (hgates : ∀ g ∈ D.gates, (g.op = GateOp.and ∧ g.inputs.length ≤ 2) ∨ g.op = GateOp.or)
    (x y : Fin 8 → Bool) (hle : ∀ v, x v = true → y v = true)
    (h : circuitFun 8 D x = true) : circuitFun 8 D y = true := by
  have hg : ∀ g ∈ D.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hmem
    exact (hgates g hmem).imp And.left id
  change (wiresFrom D.gates (List.ofFn y)).getD D.output false = true
  refine wiresFrom_mono D.gates hg (List.ofFn x) (List.ofFn y) (by simp) ?_ D.output h
  intro i hi
  by_cases hi8 : i < 8
  · rw [List.getD_eq_getElem _ _ (by simpa using hi8)] at hi ⊢
    simp only [List.getElem_ofFn] at hi ⊢
    exact hle _ hi
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
    exact Bool.noConfusion hi

lemma sample_and_count_ge_five (D : Circuit)
    (hgates : ∀ g ∈ D.gates, (g.op = GateOp.and ∧ g.inputs.length ≤ 2) ∨ g.op = GateOp.or)
    (hsample : ∀ k : Fin 40, circuitFun 8 D (sample k) = (36671 : Nat).testBit k.val) :
    5 ≤ Nat.card {j : Fin D.gates.length // (D.gates.get j).op = GateOp.and} :=
  t1_and_count_ge_five D hgates (samples_determine (circuitFun 8 D) (circuit_mono D hgates) hsample)





def baseValues : List Nat :=
  [2147418115, 663661903884, 34144976944, 728266375360, 21653750532,
   103293914128, 26322415680, 344922804352, 414195942664, 581968119809, 1065151898146]

def allowedInputs : List Nat := [0, 1, 2, 4, 5, 8, 9, 10]

def wireIndex (j : Nat) : Nat :=
  if j < 11 then ([1, 5, 3, 0, 2, 6, 0, 0, 7, 4, 0] : List Nat).getD j 0 else j - 3

lemma initial_lookup : ∀ (j : Fin 11) (k : Fin 40), j.val ∈ allowedInputs →
    wireIndex j.val < 8 ∧
    (List.ofFn (sample k)).getD (wireIndex j.val) false = (baseValues.getD j.val 0).testBit k.val := by
  decide +kernel

def bitWires (n : Nat) (v : Nat → Nat) (k : Fin 40) : List Bool :=
  List.ofFn (sample k) ++ List.ofFn (fun i : Fin n => (v (11 + i.val)).testBit k.val)

lemma bitWires_lookup {n : Nat} (v : Nat → Nat) (k : Fin 40) (j : Nat)
    (hbase : ∀ i : Fin 11, v i.val = baseValues.getD i.val 0)
    (hj : j < 11 + n) (ha : j ∈ allowedInputs ∨ 11 ≤ j) :
    (bitWires n v k).getD (wireIndex j) false = (v j).testBit k.val := by
  by_cases hj11 : j < 11
  · have hmem : j ∈ allowedInputs := ha.resolve_right (by omega)
    obtain ⟨hidx, heq⟩ := initial_lookup ⟨j, hj11⟩ k hmem
    unfold bitWires
    rw [List.getD_append _ _ _ _ (by simpa using hidx), heq, hbase ⟨j, hj11⟩]
  · have hjge : 11 ≤ j := by omega
    simp only [bitWires, wireIndex, if_neg hj11]
    rw [List.getD_append_right _ _ _ _ (by simp; omega)]
    simp only [List.length_ofFn]
    rw [List.getD_eq_getElem _ _ (by simp; omega)]
    simp only [List.getElem_ofFn]
    have he : 11 + (j - 3 - 8) = j := by omega
    rw [he]

def convertedGate {n : Nat} (ops : Fin n → Bool) (a b : Fin n → Nat) (i : Fin n) : Gate :=
  { op := if ops i then GateOp.and else GateOp.or
    inputs := [wireIndex (a i), wireIndex (b i)] }

def convertedGates {n : Nat} (ops : Fin n → Bool) (a b : Fin n → Nat) : List Gate :=
  List.ofFn (convertedGate ops a b)

lemma convertedGates_ops {n : Nat} (ops : Fin n → Bool) (a b : Fin n → Nat) :
    ∀ g ∈ convertedGates ops a b,
      (g.op = GateOp.and ∧ g.inputs.length ≤ 2) ∨ g.op = GateOp.or := by
  intro g hg
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
  cases h : ops i <;> simp [convertedGate, h]

lemma convertedGates_succ {n : Nat} (ops : Fin (n + 1) → Bool) (a b : Fin (n + 1) → Nat) :
    convertedGates ops a b =
      convertedGates (fun i => ops i.castSucc) (fun i => a i.castSucc) (fun i => b i.castSucc) ++
      [convertedGate ops a b (Fin.last n)] := by
  simp only [convertedGates, List.ofFn_succ', List.concat_eq_append]
  rfl

lemma converted_eval {n : Nat} (ops : Fin n → Bool) (a b : Fin n → Nat) (v : Nat → Nat)
    (hbase : ∀ i : Fin 11, v i.val = baseValues.getD i.val 0)
    (ha : ∀ i, a i ∈ allowedInputs ∨ 11 ≤ a i)
    (hb : ∀ i, b i ∈ allowedInputs ∨ 11 ≤ b i)
    (hs : ∀ i, a i < 11 + i.val ∧ b i < 11 + i.val ∧
      v (11 + i.val) = if ops i then v (a i) &&& v (b i) else v (a i) ||| v (b i))
    (k : Fin 40) :
    wiresFrom (convertedGates ops a b) (List.ofFn (sample k)) = bitWires n v k := by
  induction n with
  | zero => simp [convertedGates, wiresFrom, bitWires]
  | succ n ih =>
      rw [convertedGates_succ]
      simp only [wiresFrom, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have he := ih (fun i => ops i.castSucc) (fun i => a i.castSucc) (fun i => b i.castSucc)
        (fun i => ha i.castSucc) (fun i => hb i.castSucc) (fun i => hs i.castSucc)
      simp only [wiresFrom] at he
      rw [he]
      have hsa := (hs (Fin.last n)).1
      have hsb := (hs (Fin.last n)).2.1
      have hsv := (hs (Fin.last n)).2.2
      simp only [Fin.val_last] at hsa hsb hsv
      have hla := bitWires_lookup (n := n) v k (a (Fin.last n)) hbase hsa (ha (Fin.last n))
      have hlb := bitWires_lookup (n := n) v k (b (Fin.last n)) hbase hsb (hb (Fin.last n))
      simp only [convertedGate, List.map_cons, List.map_nil]
      rw [hla, hlb]
      have hbit : (if ops (Fin.last n) then GateOp.and else GateOp.or).eval
          [(v (a (Fin.last n))).testBit k.val, (v (b (Fin.last n))).testBit k.val] =
          (v (11 + n)).testBit k.val := by
        rw [hsv]
        cases h : ops (Fin.last n) <;> simp [h, GateOp.eval, Nat.testBit_and, Nat.testBit_or]
      rw [hbit]
      simp only [bitWires, List.ofFn_succ', List.concat_eq_append, Fin.coe_castSucc, Fin.val_last,
        List.append_assoc]

lemma count_converted {n : Nat} (ops : Fin n → Bool) (a b : Fin n → Nat) :
    Nat.card {j : Fin (convertedGates ops a b).length //
      ((convertedGates ops a b).get j).op = GateOp.and} =
    Nat.card {i : Fin n // ops i = true} := by
  apply Nat.card_congr
  refine (finCongr (by simp [convertedGates])).subtypeEquiv ?_
  intro i
  have hi : i.val < n := by simpa [convertedGates] using i.isLt
  change ((List.ofFn (convertedGate ops a b))[i.val]'(by simpa [convertedGates] using i.isLt)).op = GateOp.and ↔ _
  simp only [List.getElem_ofFn]
  change (if ops ⟨i.val, hi⟩ then GateOp.and else GateOp.or) = GateOp.and ↔ ops ⟨i.val, hi⟩ = true
  cases h : ops ⟨i.val, hi⟩ <;> simp [h]

lemma witness_and_count_ge_five
    (ops : Fin 14 → Bool) (a b : Fin 14 → Fin 33) (v : Nat → Nat)
    (hbase : ∀ i : Fin 11, v i.val = baseValues.getD i.val 0)
    (ha : ∀ i, (a i).val ∈ allowedInputs ∨ 11 ≤ (a i).val)
    (hb : ∀ i, (b i).val ∈ allowedInputs ∨ 11 ≤ (b i).val)
    (hs : ∀ i, (a i).val < 11 + i.val ∧ (b i).val < 11 + i.val ∧
      v (11 + i.val) = if ops i then v (a i).val &&& v (b i).val else v (a i).val ||| v (b i).val)
    (hout : v 24 = 36671) :
    5 ≤ Nat.card {i : Fin 14 // ops i = true} := by
  let D : Circuit := { gates := convertedGates ops (fun i => (a i).val) (fun i => (b i).val), output := 21 }
  have hgates := convertedGates_ops ops (fun i => (a i).val) (fun i => (b i).val)
  have hsample : ∀ k : Fin 40, circuitFun 8 D (sample k) = (36671 : Nat).testBit k.val := by
    intro k
    change (wiresFrom (convertedGates ops (fun i => (a i).val) (fun i => (b i).val))
      (List.ofFn (sample k))).getD 21 false = _
    rw [converted_eval ops (fun i => (a i).val) (fun i => (b i).val) v hbase ha hb hs k]
    have hlookup := bitWires_lookup (n := 14) v k 24 hbase (by decide) (Or.inr (by decide))
    have hidx : wireIndex 24 = 21 := by decide
    rw [hidx, hout] at hlookup
    exact hlookup
  have hcount := sample_and_count_ge_five D hgates hsample
  change 5 ≤ Nat.card {j : Fin (convertedGates ops (fun i => (a i).val) (fun i => (b i).val)).length //
    ((convertedGates ops (fun i => (a i).val) (fun i => (b i).val)).get j).op = GateOp.and} at hcount
  rwa [count_converted] at hcount

namespace OrYF

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity





inductive Meet {X : Type} (B : Set (Set X)) : Set X → Prop
  | atom {f} : f ∈ B → Meet B f
  | top : Meet B Set.univ
  | bot : Meet B ∅
  | inter {f g} : Meet B f → Meet B g → Meet B (f ∩ g)

inductive Run {X : Type} : Set (Set X) → ℕ → Set X → Prop
  | done {B f} : Meet B f → Run B 0 f
  | add {B a b k f} : Meet B a → Meet B b → Run (insert (a ∪ b) B) k f → Run B (k + 1) f

theorem mapMeet {X Y : Type} {B : Set (Set X)} {D : Set (Set Y)} (π : Y → X)
    (atoms : ∀ f ∈ B, Meet D (π ⁻¹' f)) {f} (h : Meet B f) : Meet D (π ⁻¹' f) := by
  induction h with
  | atom hf => exact atoms _ hf
  | top => exact Meet.top
  | bot => exact Meet.bot
  | inter _ _ hi hj => exact hi.inter hj

theorem weaken {X : Type} {B D : Set (Set X)} (hd : B ⊆ D) {f}
    (h : Meet B f) : Meet D f :=
  mapMeet id (fun _ hf => Meet.atom (hd hf)) h

theorem freeMap {X Y : Type} {B : Set (Set X)} {D : Set (Set Y)} (π : Y → X)
    (atoms : ∀ f ∈ B, Meet D (π ⁻¹' f)) {k f} (h : Run B k f) : Run D k (π ⁻¹' f) := by
  induction h generalizing D with
  | done hf => exact Run.done (mapMeet π atoms hf)
  | @add B a b k f ha hb _ ih =>
    apply Run.add (mapMeet π atoms ha) (mapMeet π atoms hb)
    apply ih
    intro g hg
    rcases Set.mem_insert_iff.mp hg with rfl | hg
    · exact Meet.atom (Set.mem_insert _ _)
    · exact weaken (Set.subset_insert _ _) (atoms _ hg)

theorem run_weaken {X : Type} {B D : Set (Set X)} (hd : B ⊆ D) {k f}
    (h : Run B k f) : Run D k f :=
  freeMap id (fun _ hf => Meet.atom (hd hf)) h

theorem run_succ {X : Type} {B : Set (Set X)} {k f} (h : Run B k f) : Run B (k + 1) f :=
  Run.add Meet.bot Meet.bot (run_weaken (Set.subset_insert _ _) h)

def Good {X Y : Type} (π : Y → X) (p q : X) (f : Set X) : Prop :=
  (p ∈ f ↔ q ∈ f) ∨ π ⁻¹' f = ∅

theorem meetGood {X Y : Type} {B : Set (Set X)} {π : Y → X} {p q : X}
    (atoms : ∀ f ∈ B, Good π p q f) {f} (h : Meet B f) : Good π p q f := by
  induction h with
  | atom h => exact atoms _ h
  | top => exact Or.inl Iff.rfl
  | bot => exact Or.inr rfl
  | inter _ _ ih jh =>
    rcases ih with h | h
    · rcases jh with j | j
      · exact Or.inl (and_congr h j)
      · exact Or.inr (by rw [Set.preimage_inter, j, Set.inter_empty])
    · exact Or.inr (by rw [Set.preimage_inter, h, Set.empty_inter])

theorem paidMap {X Y : Type} {B : Set (Set X)} {D : Set (Set Y)}
    (π : Y → X) (p q : X) (atoms : ∀ f ∈ B, Meet D (π ⁻¹' f))
    (good : ∀ f ∈ B, Good π p q f) {k f} (h : Run B k f) (bad : ¬ Good π p q f) :
    ∃ j < k, Run D j (π ⁻¹' f) := by
  classical
  induction h generalizing D with
  | done hf => exact (bad (meetGood good hf)).elim
  | @add B a b k f ha hb tail ih =>
    have aa := mapMeet π atoms ha
    have ab := mapMeet π atoms hb
    by_cases gg : Good π p q (a ∪ b)
    · let D' := insert ((π ⁻¹' a) ∪ (π ⁻¹' b)) D
      have m : ∀ g ∈ insert (a ∪ b) B, Meet D' (π ⁻¹' g) := by
        intro g hg
        rcases Set.mem_insert_iff.mp hg with rfl | hg
        · exact Meet.atom (Set.mem_insert _ _)
        · exact weaken (Set.subset_insert _ _) (atoms _ hg)
      obtain ⟨j, hj, hr⟩ := ih m (fun g hg => (Set.mem_insert_iff.mp hg).elim
        (fun e => e ▸ gg) (good g)) bad
      exact ⟨j + 1, by omega, Run.add aa ab hr⟩
    · have bypass : Meet D (π ⁻¹' (a ∪ b)) := by
        rcases meetGood good ha with h | h
        · rcases meetGood good hb with z | z
          · exact (gg (Or.inl (or_congr h z))).elim
          · simpa [Set.preimage_union, z] using aa
        · simpa [Set.preimage_union, h] using ab
      exact ⟨k, by omega, freeMap π (fun g hg => (Set.mem_insert_iff.mp hg).elim
        (fun e => e ▸ bypass) (atoms g)) tail⟩



def UpClosed {X : Type} (le : X → X → Prop) (f : Set X) : Prop :=
  ∀ x y, le x y → x ∈ f → y ∈ f

theorem meet_upClosed {X : Type} {le : X → X → Prop} {B : Set (Set X)}
    (hB : ∀ x ∈ B, UpClosed le x) {f : Set X} (hf : Meet B f) : UpClosed le f := by
  induction hf with
  | atom hx => exact hB _ hx
  | top => intro _ _ _ _; trivial
  | bot => intro _ _ _ hx; exact hx.elim
  | inter _ _ ih1 ih2 => intro x y hxy ⟨h1, h2⟩; exact ⟨ih1 x y hxy h1, ih2 x y hxy h2⟩

theorem run_upClosed {X : Type} {le : X → X → Prop} {B : Set (Set X)}
    (hB : ∀ x ∈ B, UpClosed le x) {k : ℕ} {f : Set X} (hr : Run B k f) : UpClosed le f := by
  induction hr with
  | done hf => exact meet_upClosed hB hf
  | @add B a b k f ha hb _ ih =>
    apply ih
    intro g hg
    rcases Set.mem_insert_iff.mp hg with rfl | hg
    · intro x y hxy hx
      rcases hx with h1 | h2
      · exact Or.inl (meet_upClosed hB ha x y hxy h1)
      · exact Or.inr (meet_upClosed hB hb x y hxy h2)
    · exact hB g hg

theorem meet_replaceBelow {X : Type} {B D : Set (Set X)} {S : Set X}
    (hmap : ∀ x ∈ B, ∃ x', Meet D x' ∧ x' ⊆ x ∧ x' ∩ S = x ∩ S)
    {f : Set X} (hf : Meet B f) :
    ∃ f', Meet D f' ∧ f' ⊆ f ∧ f' ∩ S = f ∩ S := by
  induction hf with
  | atom hx => exact hmap _ hx
  | top => exact ⟨Set.univ, Meet.top, Set.Subset.rfl, rfl⟩
  | bot => exact ⟨∅, Meet.bot, Set.Subset.rfl, rfl⟩
  | inter _ _ ih1 ih2 =>
    obtain ⟨f1', hm1, hs1, he1⟩ := ih1
    obtain ⟨f2', hm2, hs2, he2⟩ := ih2
    refine ⟨f1' ∩ f2', hm1.inter hm2, Set.inter_subset_inter hs1 hs2, ?_⟩
    ext x
    have h1 := Set.ext_iff.mp he1 x
    have h2 := Set.ext_iff.mp he2 x
    simp only [Set.mem_inter_iff] at h1 h2 ⊢
    tauto

theorem run_replaceBelow {X : Type} {B D : Set (Set X)} {S : Set X}
    (hmap : ∀ x ∈ B, ∃ x', Meet D x' ∧ x' ⊆ x ∧ x' ∩ S = x ∩ S)
    {k : ℕ} {f : Set X} (hr : Run B k f) :
    ∃ f', Run D k f' ∧ f' ⊆ f ∧ f' ∩ S = f ∩ S := by
  induction hr generalizing D with
  | done hf =>
    obtain ⟨f', hm, hs, he⟩ := meet_replaceBelow hmap hf
    exact ⟨f', Run.done hm, hs, he⟩
  | @add B a b k f ha hb _ ih =>
    obtain ⟨a', hma, hsa, hea⟩ := meet_replaceBelow hmap ha
    obtain ⟨b', hmb, hsb, heb⟩ := meet_replaceBelow hmap hb
    let D' := insert (a' ∪ b') D
    have hmap' : ∀ x ∈ insert (a ∪ b) B, ∃ x', Meet D' x' ∧ x' ⊆ x ∧ x' ∩ S = x ∩ S := by
      intro x hx
      rcases Set.mem_insert_iff.mp hx with rfl | hx
      · refine ⟨a' ∪ b', Meet.atom (Set.mem_insert _ _), Set.union_subset_union hsa hsb, ?_⟩
        rw [Set.union_inter_distrib_right, Set.union_inter_distrib_right, hea, heb]
      · obtain ⟨x', hmx, hsx, hex⟩ := hmap x hx
        exact ⟨x', weaken (Set.subset_insert _ _) hmx, hsx, hex⟩
    obtain ⟨f', hrf', hsf', hef'⟩ := ih hmap'
    exact ⟨f', Run.add hma hmb hrf', hsf', hef'⟩

theorem run_replaceBelow_upClosed {X : Type} {le : X → X → Prop}
    {B D : Set (Set X)} {S target : Set X}
    (hSt : S ⊆ target)
    (hclose : ∀ f, UpClosed le f → S ⊆ f → target ⊆ f)
    (hD : ∀ x ∈ D, UpClosed le x)
    (hmap : ∀ x ∈ B, ∃ x', Meet D x' ∧ x' ⊆ x ∧ x' ∩ S = x ∩ S)
    {k : ℕ} (hr : Run B k target) :
    Run D k target := by
  obtain ⟨f', hrf', hsub, heq⟩ := run_replaceBelow hmap hr
  have hup : UpClosed le f' := run_upClosed hD hrf'
  have hSf' : S ⊆ f' := by
    intro x hx
    have : x ∈ target ∩ S := ⟨hSt hx, hx⟩
    rw [← heq] at this
    exact this.1
  have htf' : target ⊆ f' := hclose f' hup hSf'
  have : f' = target := Set.Subset.antisymm hsub htf'
  exact this ▸ hrf'



def mkBitmask : ℕ → (ℕ → Bool) → ℕ
  | 0, _ => 0
  | k + 1, p => if p k then mkBitmask k p ||| (1 <<< k) else mkBitmask k p

theorem testBit_one_shiftLeft (k s : ℕ) : (1 <<< k).testBit s = decide (k = s) := by
  rw [Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow]

theorem testBit_mkBitmask (N : ℕ) (p : ℕ → Bool) (s : ℕ) :
    (mkBitmask N p).testBit s = (decide (s < N) && p s) := by
  induction N with
  | zero => simp [mkBitmask]
  | succ k ih =>
    simp only [mkBitmask]
    split_ifs with hpk
    · rw [Nat.testBit_or, ih, testBit_one_shiftLeft]
      by_cases hlt : s < k
      · have hne : k ≠ s := by omega
        have hlt' : s < k + 1 := by omega
        simp [hlt, hlt', hne]
      · by_cases heq : k = s
        · subst heq; simp [hpk]
        · have hlt' : ¬ (s < k + 1) := by omega
          simp [hlt, hlt', heq]
    · rw [ih]
      by_cases hlt : s < k
      · have hlt' : s < k + 1 := by omega
        simp [hlt, hlt']
      · by_cases heq : k = s
        · subst heq; simp [hpk]
        · have hlt' : ¬ (s < k + 1) := by omega
          simp [hlt, hlt']

theorem mkBitmask_testBit_lt {N : ℕ} {p : ℕ → Bool} {s : ℕ}
    (h : (mkBitmask N p).testBit s = true) : s < N := by
  rw [testBit_mkBitmask, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

def hasEdge (E : List (ℕ × ℕ)) (s : ℕ) : Bool :=
  E.any (fun e => s.testBit e.1 && s.testBit e.2)

theorem hasEdge_eq_true (E : List (ℕ × ℕ)) (s : ℕ) :
    hasEdge E s = true ↔ ∃ e ∈ E, s.testBit e.1 = true ∧ s.testBit e.2 = true := by
  simp [hasEdge]

def univYF (n : ℕ) (F : List (ℕ × ℕ)) : ℕ :=
  mkBitmask (2 ^ n) (fun s => !hasEdge F s)

def ttVarYF (n v maskYF : ℕ) : ℕ :=
  mkBitmask (2 ^ n) (fun s => maskYF.testBit s && s.testBit v)

def rawYF (n : ℕ) (maskYF : ℕ) : List ℕ :=
  (List.range n).map (fun v => ttVarYF n v maskYF)

def edgeTTYF (n : ℕ) (H : List (ℕ × ℕ)) (maskYF : ℕ) : ℕ :=
  mkBitmask (2 ^ n) (fun s => maskYF.testBit s && hasEdge H s)

def edgePtsMaskYF (H : List (ℕ × ℕ)) : ℕ :=
  H.foldl (fun acc e => acc ||| (1 <<< ((1 <<< e.1) ||| (1 <<< e.2)))) 0

def ttNeedYF (n a maskYF : ℕ) : ℕ :=
  mkBitmask (2 ^ n) (fun s => maskYF.testBit s && ((s &&& a) == a))

def masksTTYF (n : ℕ) (H : List (ℕ × ℕ)) (maskYF : ℕ) : List ℕ :=
  (0 :: (List.range n).map (fun v => 1 <<< v) ++
    H.map (fun e => (1 <<< e.1) ||| (1 <<< e.2))).map (fun m => ttNeedYF n m maskYF)

def undirEq (e₁ e₂ : ℕ × ℕ) : Bool :=
  (e₁.1 == e₂.1 && e₁.2 == e₂.2) || (e₁.1 == e₂.2 && e₁.2 == e₂.1)

def ValidState (n : ℕ) (H F : List (ℕ × ℕ)) : Prop :=
  (∀ e ∈ H, e.1 < n ∧ e.2 < n ∧ e.1 ≠ e.2) ∧
  (∀ e ∈ F, e.1 < n ∧ e.2 < n ∧ e.1 ≠ e.2) ∧
  (∀ e ∈ H, ∀ f ∈ F, undirEq e f = false)

def NoDupEdges (H : List (ℕ × ℕ)) : Prop :=
  H.Pairwise (fun e₁ e₂ => undirEq e₁ e₂ = false)

instance (n : ℕ) (H F : List (ℕ × ℕ)) : Decidable (ValidState n H F) := by
  unfold ValidState; infer_instance

instance (H : List (ℕ × ℕ)) : Decidable (NoDupEdges H) := by
  unfold NoDupEdges; infer_instance

theorem testBit_univYF (n : ℕ) (F : List (ℕ × ℕ)) (s : ℕ) :
    (univYF n F).testBit s = (decide (s < 2 ^ n) && !hasEdge F s) :=
  testBit_mkBitmask (2 ^ n) _ s

theorem univYF_testBit_lt {n : ℕ} {F : List (ℕ × ℕ)} {s : ℕ}
    (h : (univYF n F).testBit s = true) : s < 2 ^ n :=
  mkBitmask_testBit_lt h

theorem testBit_ttVarYF {n v maskYF : ℕ} (hM : ∀ s, maskYF.testBit s = true → s < 2 ^ n) (s : ℕ) :
    (ttVarYF n v maskYF).testBit s = (maskYF.testBit s && s.testBit v) := by
  rw [ttVarYF, testBit_mkBitmask]
  by_cases hm : maskYF.testBit s = true
  · simp [hm, hM s hm]
  · simp [hm]

theorem testBit_edgeTTYF {n : ℕ} {H : List (ℕ × ℕ)} {maskYF : ℕ}
    (hM : ∀ s, maskYF.testBit s = true → s < 2 ^ n) (s : ℕ) :
    (edgeTTYF n H maskYF).testBit s = (maskYF.testBit s && hasEdge H s) := by
  rw [edgeTTYF, testBit_mkBitmask]
  by_cases hm : maskYF.testBit s = true
  · simp [hm, hM s hm]
  · simp [hm]

theorem testBit_ttNeedYF {n a maskYF : ℕ}
    (hM : ∀ s, maskYF.testBit s = true → s < 2 ^ n) (s : ℕ) :
    (ttNeedYF n a maskYF).testBit s = (maskYF.testBit s && ((s &&& a) == a)) := by
  rw [ttNeedYF, testBit_mkBitmask]
  by_cases hm : maskYF.testBit s = true
  · simp [hm, hM s hm]
  · simp [hm]

theorem testBit_edgePtsMaskYF_aux (H : List (ℕ × ℕ)) (acc s : ℕ) :
    (H.foldl (fun a e => a ||| (1 <<< ((1 <<< e.1) ||| (1 <<< e.2)))) acc).testBit s =
      (acc.testBit s || H.any (fun e => decide (((1 <<< e.1) ||| (1 <<< e.2)) = s))) := by
  induction H generalizing acc with
  | nil => simp
  | cons e rest ih =>
    simp only [List.foldl_cons, List.any_cons]
    rw [ih, Nat.testBit_or, testBit_one_shiftLeft, Bool.or_assoc]

theorem testBit_edgePtsMaskYF (H : List (ℕ × ℕ)) (s : ℕ) :
    (edgePtsMaskYF H).testBit s = H.any (fun e => decide (((1 <<< e.1) ||| (1 <<< e.2)) = s)) := by
  simpa [edgePtsMaskYF] using testBit_edgePtsMaskYF_aux H 0 s

theorem twoBit_lt_two_pow {n u v : ℕ} (hu : u < n) (hv : v < n) :
    ((1 <<< u) ||| (1 <<< v)) < 2 ^ n := by
  have h1 : (1 <<< u) < 2 ^ n := by
    rw [Nat.shiftLeft_eq, one_mul]; exact Nat.pow_lt_pow_right (by omega) hu
  have h2 : (1 <<< v) < 2 ^ n := by
    rw [Nat.shiftLeft_eq, one_mul]; exact Nat.pow_lt_pow_right (by omega) hv
  exact Nat.or_lt_two_pow h1 h2

theorem oneBit_lt_two_pow {n u : ℕ} (hu : u < n) : (1 <<< u) < 2 ^ n := by
  rw [Nat.shiftLeft_eq, one_mul]; exact Nat.pow_lt_pow_right (by omega) hu

theorem twoBit_testBit (u v w : ℕ) :
    (((1 <<< u) ||| (1 <<< v)).testBit w = true) ↔ w = u ∨ w = v := by
  rw [Nat.testBit_or, testBit_one_shiftLeft, testBit_one_shiftLeft, Bool.or_eq_true,
    decide_eq_true_eq, decide_eq_true_eq]
  tauto

theorem edgePt_mem_univYF {n : ℕ} {H F : List (ℕ × ℕ)} (hv : ValidState n H F)
    {e : ℕ × ℕ} (he : e ∈ H) :
    (univYF n F).testBit ((1 <<< e.1) ||| (1 <<< e.2)) = true := by
  rcases hv with ⟨hH, hF, hdisj⟩
  obtain ⟨hu, hv', hne⟩ := hH e he
  rw [testBit_univYF, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
  refine ⟨twoBit_lt_two_pow hu hv', ?_⟩
  rw [Bool.eq_false_iff]
  intro hf
  rw [hasEdge_eq_true] at hf
  obtain ⟨f, hfmem, hf1, hf2⟩ := hf
  rw [twoBit_testBit] at hf1 hf2
  obtain ⟨_, _, hfne⟩ := hF f hfmem
  have hd := hdisj e he f hfmem
  simp only [undirEq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, beq_eq_false_iff_ne] at hd
  rcases hf1 with h1 | h1 <;> rcases hf2 with h2 | h2
  · exact hfne (h1.trans h2.symm)
  · rcases hd.1 with h | h <;> exact h (by omega)
  · rcases hd.2 with h | h <;> exact h (by omega)
  · exact hfne (h1.trans h2.symm)

theorem edgePt_mem_edgeTTYF {n : ℕ} {H F : List (ℕ × ℕ)} (hv : ValidState n H F)
    {e : ℕ × ℕ} (he : e ∈ H) :
    (edgeTTYF n H (univYF n F)).testBit ((1 <<< e.1) ||| (1 <<< e.2)) = true := by
  rw [testBit_edgeTTYF (fun _ => univYF_testBit_lt), Bool.and_eq_true]
  refine ⟨edgePt_mem_univYF hv he, ?_⟩
  rw [hasEdge_eq_true]
  exact ⟨e, he, (twoBit_testBit _ _ _).mpr (Or.inl rfl), (twoBit_testBit _ _ _).mpr (Or.inr rfl)⟩

theorem edgePtsMask_and_univYF {n : ℕ} {H F : List (ℕ × ℕ)} (hv : ValidState n H F) :
    edgePtsMaskYF H &&& univYF n F = edgePtsMaskYF H := by
  apply Nat.eq_of_testBit_eq
  intro s
  rw [Nat.testBit_and]
  cases h : (edgePtsMaskYF H).testBit s
  · simp
  · rw [testBit_edgePtsMaskYF, List.any_eq_true] at h
    obtain ⟨e, heH, heq⟩ := h
    rw [decide_eq_true_eq] at heq
    rw [← heq, edgePt_mem_univYF hv heH, Bool.true_and]

theorem edgeTTYF_and_univYF (n : ℕ) (H F : List (ℕ × ℕ)) :
    edgeTTYF n H (univYF n F) &&& univYF n F = edgeTTYF n H (univYF n F) := by
  apply Nat.eq_of_testBit_eq
  intro s
  rw [Nat.testBit_and, testBit_edgeTTYF (fun _ => univYF_testBit_lt)]
  cases (univYF n F).testBit s <;> simp

theorem ttVarYF_and_mask {n v M : ℕ} (hM : ∀ s, M.testBit s = true → s < 2 ^ n) :
    ttVarYF n v M &&& M = ttVarYF n v M := by
  apply Nat.eq_of_testBit_eq
  intro s
  rw [Nat.testBit_and, testBit_ttVarYF hM]
  cases M.testBit s <;> simp

theorem ttNeedYF_and_mask {n a M : ℕ} (hM : ∀ s, M.testBit s = true → s < 2 ^ n) :
    ttNeedYF n a M &&& M = ttNeedYF n a M := by
  apply Nat.eq_of_testBit_eq
  intro s
  rw [Nat.testBit_and, testBit_ttNeedYF hM]
  cases M.testBit s <;> simp



abbrev Dom (maskYF : ℕ) := { s : ℕ // maskYF.testBit s = true }

def decM (maskYF : ℕ) (g : ℕ) : Set (Dom maskYF) :=
  { s | g.testBit s.1 = true }

@[simp] theorem mem_decM (maskYF g : ℕ) (s : Dom maskYF) :
    s ∈ decM maskYF g ↔ g.testBit s.1 = true := Iff.rfl

def rawSet (n : ℕ) (F : List (ℕ × ℕ)) : Set (Set (Dom (univYF n F))) :=
  Set.range (fun v : Fin n => decM (univYF n F) (ttVarYF n v.1 (univYF n F)))

def targetSet (n : ℕ) (H F : List (ℕ × ℕ)) : Set (Dom (univYF n F)) :=
  decM (univYF n F) (edgeTTYF n H (univYF n F))

def HasRunYF (n : ℕ) (H F : List (ℕ × ℕ)) (k : ℕ) : Prop :=
  Run (rawSet n F) k (targetSet n H F)

def OrCostLB (n : ℕ) (H F : List (ℕ × ℕ)) (lb : ℕ) : Prop :=
  ∀ k, HasRunYF n H F k → lb ≤ k

theorem decM_zero (M : ℕ) : decM M 0 = ∅ := by
  ext s; simp [decM]

theorem decM_self (M : ℕ) : decM M M = Set.univ := by
  ext ⟨s, hs⟩; simp [decM, hs]

theorem decM_and (M a b : ℕ) : decM M (a &&& b) = decM M a ∩ decM M b := by
  ext s; simp [decM, Nat.testBit_and]

theorem decM_or (M a b : ℕ) : decM M (a ||| b) = decM M a ∪ decM M b := by
  ext s; simp [decM, Nat.testBit_or]

theorem sub_mask_testBit {a M s : ℕ} (h : a &&& M = a) (ha : a.testBit s = true) :
    M.testBit s = true := by
  have := congrArg (fun x => x.testBit s) h
  rw [Nat.testBit_and, ha, Bool.true_and] at this
  exact this

theorem decM_subset_iff {M a b : ℕ} (ha : a &&& M = a) :
    decM M a ⊆ decM M b ↔ a &&& b = a := by
  constructor
  · intro hsub
    apply Nat.eq_of_testBit_eq
    intro s
    rw [Nat.testBit_and]
    cases h : a.testBit s
    · simp
    · have hm : M.testBit s = true := sub_mask_testBit ha h
      have hb : b.testBit s = true := hsub (a := ⟨s, hm⟩) h
      simp [hb]
  · intro heq ⟨s, _⟩ has
    have := congrArg (fun x => x.testBit s) heq
    rw [Nat.testBit_and, has, Bool.true_and] at this
    exact this

theorem decM_inj {M a b : ℕ} (ha : a &&& M = a) (hb : b &&& M = b) :
    decM M a = decM M b ↔ a = b := by
  constructor
  · intro heq
    apply Nat.eq_of_testBit_eq
    intro s
    cases h1 : a.testBit s
    · cases h2 : b.testBit s
      · rfl
      · have hm : M.testBit s = true := sub_mask_testBit hb h2
        have : (⟨s, hm⟩ : Dom M) ∈ decM M a := by rw [heq]; exact h2
        simp [decM, h1] at this
    · have hm : M.testBit s = true := sub_mask_testBit ha h1
      have : (⟨s, hm⟩ : Dom M) ∈ decM M b := by rw [← heq]; exact h1
      exact this.symm
  · intro h; rw [h]

noncomputable def encM (N M : ℕ) (S : Set (Dom M)) : ℕ := by
  classical
  exact mkBitmask N (fun s => if h : M.testBit s = true then decide (⟨s, h⟩ ∈ S) else false)

theorem encM_and_self {N M : ℕ} (S : Set (Dom M)) : encM N M S &&& M = encM N M S := by
  classical
  apply Nat.eq_of_testBit_eq
  intro s
  rw [Nat.testBit_and, encM, testBit_mkBitmask]
  by_cases hm : M.testBit s = true
  · simp [hm]
  · simp [hm]

theorem decM_encM {N M : ℕ} (hM : ∀ s, M.testBit s = true → s < N) (S : Set (Dom M)) :
    decM M (encM N M S) = S := by
  classical
  ext ⟨s, hs⟩
  simp only [decM, encM, testBit_mkBitmask, Set.mem_ofPred_eq]
  simp [hM s hs, hs]

theorem encM_decM {N M g : ℕ} (hM : ∀ s, M.testBit s = true → s < N) (hg : g &&& M = g) :
    encM N M (decM M g) = g :=
  (decM_inj (encM_and_self _) hg).mp (decM_encM hM _)

theorem rawSet_eq_image (n : ℕ) (F : List (ℕ × ℕ)) :
    rawSet n F = decM (univYF n F) '' { x | x ∈ rawYF n (univYF n F) } := by
  ext S
  simp only [rawSet, rawYF, Set.mem_range, Set.mem_image, Set.mem_ofPred_eq, List.mem_map,
    List.mem_range]
  constructor
  · rintro ⟨⟨v, hv⟩, rfl⟩
    exact ⟨ttVarYF n v (univYF n F), ⟨v, hv, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨⟨v, hv⟩, rfl⟩



def isOrGate (g : Gate) : Bool :=
  match g.op with
  | .or => true
  | _ => false

def countOrGates (gs : List Gate) : ℕ :=
  (gs.filter isOrGate).length

def gateStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]

noncomputable def bitOfSet {X : Type} (s : X) (f : Set X) : Bool := by
  classical exact decide (s ∈ f)

theorem bitOfSet_read {X : Type} (s : X) (ws : List (Set X)) (j : ℕ) :
    (ws.map (bitOfSet s)).getD j false = bitOfSet s (ws.getD j ∅) := by
  classical
  by_cases hj : j < ws.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_none (Nat.le_of_not_gt hj),
      bitOfSet]

theorem compileSig {X : Type} (gs : List Gate) (out : ℕ) (B : Set (Set X)) (w : List (Set X))
    (f : Set X)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hw : ∀ z ∈ w, Meet B z)
    (val : ∀ s : X, (gs.foldl gateStep (w.map (bitOfSet s))).getD out false = bitOfSet s f) :
    ∃ k ≤ countOrGates gs, Run B k f := by
  classical
  induction gs generalizing B w with
  | nil =>
    have h : w.getD out ∅ = f := by
      ext s
      have hh := val s
      rw [List.foldl_nil, bitOfSet_read] at hh
      simpa [bitOfSet] using (Bool.eq_iff_iff.mp hh)
    refine ⟨0, by simp [countOrGates], Run.done ?_⟩
    rw [← h]
    by_cases j : out < w.length
    · rw [List.getD_eq_getElem _ _ j]; exact hw _ (List.getElem_mem _)
    · rw [List.getD_eq_default _ _ (by omega)]; exact Meet.bot
  | cons g gs ih =>
    have ok := legal g (by simp)
    have ht : ∀ a ∈ gs, a.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ a.inputs.length ≤ 2 :=
      fun a h => legal _ (by simp [h])
    have rd (j : ℕ) : Meet B (w.getD j ∅) := by
      by_cases hj : j < w.length
      · rw [List.getD_eq_getElem _ _ hj]; exact hw _ (List.getElem_mem _)
      · rw [List.getD_eq_default _ _ (by omega)]; exact Meet.bot
    have handle (z : Set X) (hz : Meet B z ∨ ∃ a b, Meet B a ∧ Meet B b ∧ z = a ∪ b ∧ g.op = .or)
        (step : ∀ s, gateStep (w.map (bitOfSet s)) g = (w ++ [z]).map (bitOfSet s)) :
        ∃ k ≤ countOrGates (g :: gs), Run B k f := by
      have val' s : (gs.foldl gateStep ((w ++ [z]).map (bitOfSet s))).getD out false = bitOfSet s f := by
        simpa only [List.foldl_cons, step] using val s
      rcases hz with free | ⟨a, b, ha, hb, rfl, hop⟩
      · obtain ⟨k, hk, h⟩ := ih B _ ht (fun u hu => by
          rcases List.mem_append.mp hu with hu | hu
          · exact hw _ hu
          · simpa [List.mem_singleton.mp hu] using free) val'
        exact ⟨k, hk.trans (by simp [countOrGates, List.filter_cons]; split <;> simp), h⟩
      · obtain ⟨k, hk, h⟩ := ih (insert (a ∪ b) B) _ ht (fun u hu => by
          rcases List.mem_append.mp hu with hu | hu
          · exact weaken (Set.subset_insert _ _) (hw _ hu)
          · exact Meet.atom (List.mem_singleton.mp hu ▸ Set.mem_insert _ _)) val'
        refine ⟨k + 1, ?_, Run.add ha hb h⟩
        have go : isOrGate g = true := by simp [isOrGate, hop]
        simpa [countOrGates, go] using Nat.succ_le_succ hk
    obtain ⟨op, l⟩ := g
    change (op = .and ∨ op = .or) ∧ l.length ≤ 2 at ok
    obtain ⟨opok, hlen⟩ := ok
    cases l with
    | nil =>
      rcases opok with rfl | rfl
      · apply handle Set.univ (Or.inl Meet.top); intro s; simp [gateStep, GateOp.eval, bitOfSet]
      · apply handle ∅ (Or.inl Meet.bot); intro s; simp [gateStep, GateOp.eval, bitOfSet]
    | cons i l =>
      cases l with
      | nil =>
        rcases opok with rfl | rfl <;> apply handle (w.getD i ∅) (Or.inl (rd i)) <;>
          intro s <;> simp [gateStep, GateOp.eval] <;> cases w[i]? <;> simp [bitOfSet]
      | cons j l =>
        cases l with
        | cons => simp at hlen
        | nil =>
          rcases opok with rfl | rfl
          · apply handle (w.getD i ∅ ∩ w.getD j ∅) (Or.inl ((rd i).inter (rd j)))
            intro s; simp [gateStep, GateOp.eval]; cases w[i]? <;> cases w[j]? <;> simp [bitOfSet]
          · apply handle (w.getD i ∅ ∪ w.getD j ∅) (Or.inr ⟨_, _, rd i, rd j, rfl, rfl⟩)
            intro s; simp [gateStep, GateOp.eval]; cases w[i]? <;> cases w[j]? <;> simp [bitOfSet]

theorem ofCircuitYF {n : ℕ} (H : List (ℕ × ℕ)) (C : Circuit) (hc : Monotone2 C)
    (he : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
      ∃ e ∈ H, ∃ (h1 : e.1 < n) (h2 : e.2 < n), x ⟨e.1, h1⟩ = true ∧ x ⟨e.2, h2⟩ = true)
    (hH : ∀ e ∈ H, e.1 < n ∧ e.2 < n) :
    ∃ k ≤ countOrGates C.gates, HasRunYF n H [] k := by
  classical
  let M := univYF n []
  let w : List (Set (Dom M)) := List.ofFn (fun v : Fin n => decM M (ttVarYF n v.1 M))
  have hw : ∀ z ∈ w, Meet (rawSet n []) z := by
    intro z hz
    obtain ⟨v, rfl⟩ := List.mem_ofFn.mp hz
    exact Meet.atom ⟨v, rfl⟩
  have hval (s : Dom M) :
      (C.gates.foldl gateStep (w.map (bitOfSet s))).getD C.output false =
        bitOfSet s (targetSet n H []) := by
    let x : Fin n → Bool := fun v => s.1.testBit v.1
    have hin : w.map (bitOfSet s) = List.ofFn x := by
      rw [show w = List.ofFn (fun v : Fin n => decM M (ttVarYF n v.1 M)) from rfl, List.map_ofFn]
      apply congrArg List.ofFn
      funext v
      have htb : (ttVarYF n v.1 M).testBit s.1 = s.1.testBit v.1 := by
        rw [testBit_ttVarYF (fun _ => univYF_testBit_lt), s.2, Bool.true_and]
      simp only [Function.comp_apply, bitOfSet, decM, Set.mem_ofPred_eq, htb, x]
      cases s.1.testBit v.1 <;> rfl
    rw [hin]
    change C.eval (List.ofFn x) = _
    apply Bool.eq_iff_iff.mpr
    have het : (edgeTTYF n H M).testBit s.1 = hasEdge H s.1 := by
      rw [testBit_edgeTTYF (fun _ => univYF_testBit_lt), s.2, Bool.true_and]
    change C.eval (List.ofFn x) = true ↔ decide (s ∈ targetSet n H []) = true
    rw [decide_eq_true_eq, he x]
    have hmem : s ∈ targetSet n H [] ↔ ∃ e ∈ H, s.1.testBit e.1 = true ∧ s.1.testBit e.2 = true := by
      change (edgeTTYF n H M).testBit s.1 = true ↔ _
      rw [het, hasEdge_eq_true]
    rw [hmem]
    simp only [x]
    constructor
    · rintro ⟨e, heH, _, _, h1, h2⟩; exact ⟨e, heH, h1, h2⟩
    · rintro ⟨e, heH, h1, h2⟩
      obtain ⟨hu, hv⟩ := hH e heH
      exact ⟨e, heH, hu, hv, h1, h2⟩
  exact compileSig C.gates C.output (rawSet n []) w (targetSet n H []) hc hw hval

theorem countOr_add_countAnd_list (gs : List Gate)
    (hmem : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) :
    (gs.filter (fun g => match g.op with | .and => true | _ => false)).length +
      countOrGates gs = gs.length := by
  induction gs with
  | nil => simp [countOrGates]
  | cons g gs ih =>
    have hg := hmem g (by simp)
    have ih' := ih (fun x hx => hmem x (by simp [hx]))
    rcases hg with h | h <;> simp [countOrGates, isOrGate, h] at ih' ⊢ <;> omega

theorem countOr_add_countAnd (C : Circuit) (hc : Monotone2 C) :
    (C.gates.filter (fun g => match g.op with | .and => true | _ => false)).length +
      countOrGates C.gates = C.size :=
  countOr_add_countAnd_list C.gates (fun g hg => (hc g hg).1)



theorem land_eq (a b : ℕ) : Nat.land a b = a &&& b := rfl
theorem lor_eq (a b : ℕ) : Nat.lor a b = a ||| b := rfl

def isMeetLoop (target : ℕ) : List ℕ → ℕ → ℕ
  | [], acc => acc
  | b :: bs, acc =>
    match Nat.beq (Nat.land target b) target with
    | true => isMeetLoop target bs (Nat.land acc b)
    | false => isMeetLoop target bs acc

def isMeet (univMask : ℕ) (basis : List ℕ) (target : ℕ) : Bool :=
  match Nat.beq target 0 with
  | true => true
  | false => Nat.beq (isMeetLoop target basis univMask) target

def isOnEdges (univMask edgePtsMask : ℕ) (basis : List ℕ) (g : ℕ) : Bool :=
  let eg := Nat.land g edgePtsMask
  let acc := isMeetLoop eg basis univMask
  Nat.beq (Nat.land acc g) acc

theorem isMeetLoop_and_sub {target : ℕ} (bs : List ℕ) (acc : ℕ) :
    isMeetLoop target bs acc &&& acc = isMeetLoop target bs acc := by
  induction bs generalizing acc with
  | nil => simp [isMeetLoop]
  | cons b bs ih =>
    simp only [isMeetLoop]
    cases Nat.beq (Nat.land target b) target
    · exact ih acc
    · have h1 := ih (Nat.land acc b)
      apply Nat.eq_of_testBit_eq; intro s
      have h2 := congrArg (fun x => x.testBit s) h1
      simp only [land_eq, Nat.testBit_and] at h2 ⊢
      revert h2
      cases (isMeetLoop target bs (acc &&& b)).testBit s <;>
        cases acc.testBit s <;> cases b.testBit s <;> decide

theorem isMeetLoop_and_mask {target M : ℕ} (bs : List ℕ) {acc : ℕ} (hacc : acc &&& M = acc) :
    isMeetLoop target bs acc &&& M = isMeetLoop target bs acc := by
  have hsub := isMeetLoop_and_sub (target := target) bs acc
  apply Nat.eq_of_testBit_eq; intro s
  have h1 := congrArg (fun x => x.testBit s) hsub
  have h2 := congrArg (fun x => x.testBit s) hacc
  simp only [Nat.testBit_and] at h1 h2 ⊢
  revert h1 h2
  cases (isMeetLoop target bs acc).testBit s <;>
    cases acc.testBit s <;> cases M.testBit s <;> decide

theorem isMeetLoop_target_sub {target : ℕ} (bs : List ℕ) {acc : ℕ}
    (hacc : target &&& acc = target) :
    target &&& isMeetLoop target bs acc = target := by
  induction bs generalizing acc with
  | nil => exact hacc
  | cons b bs ih =>
    simp only [isMeetLoop]
    cases hb : Nat.beq (Nat.land target b) target
    · exact ih hacc
    · apply ih
      have hb' : target &&& b = target := by simpa [land_eq] using Nat.eq_of_beq_eq_true hb
      rw [land_eq, ← Nat.and_assoc, hacc, hb']

theorem isMeetLoop_mem_meet {M target : ℕ} {B : Set (Set (Dom M))} (bs : List ℕ)
    (hbs : ∀ b ∈ bs, decM M b ∈ B) {acc : ℕ} (hacc : Meet B (decM M acc)) :
    Meet B (decM M (isMeetLoop target bs acc)) := by
  induction bs generalizing acc with
  | nil => exact hacc
  | cons b bs ih =>
    simp only [isMeetLoop]
    cases Nat.beq (Nat.land target b) target
    · exact ih (fun x hx => hbs x (by simp [hx])) hacc
    · apply ih (fun x hx => hbs x (by simp [hx]))
      rw [land_eq, decM_and]
      exact hacc.inter (Meet.atom (hbs b (by simp)))

theorem isMeetLoop_le_factor {M target : ℕ} (bs : List ℕ) {b : ℕ} (hb : b ∈ bs)
    (htb : target &&& b = target) (acc : ℕ) :
    decM M (isMeetLoop target bs acc) ⊆ decM M b := by
  induction bs generalizing acc with
  | nil => simp at hb
  | cons x bs ih =>
    simp only [isMeetLoop]
    rcases List.mem_cons.mp hb with rfl | hb'
    · have hbeq : Nat.beq (Nat.land target b) target = true := by
        simpa [land_eq] using htb
      rw [hbeq]
      have hsub := isMeetLoop_and_sub (target := target) bs (Nat.land acc b)
      intro s hs
      have h1 := congrArg (fun z => z.testBit s.1) hsub
      simp only [land_eq, Nat.testBit_and] at h1
      change (isMeetLoop target bs (acc &&& b)).testBit s.1 = true at hs
      rw [hs, Bool.true_and] at h1
      have h2 : acc.testBit s.1 = true ∧ b.testBit s.1 = true := by
        simpa [Bool.and_eq_true] using h1.symm
      exact h2.2
    · cases Nat.beq (Nat.land target x) target
      · exact ih hb' acc
      · exact ih hb' (Nat.land acc x)

theorem isMeet_iff {M : ℕ} {B : List ℕ} {t : ℕ} (ht : t &&& M = t) :
    isMeet M B t = true ↔ Meet (decM M '' { b | b ∈ B }) (decM M t) := by
  unfold isMeet
  cases h0 : Nat.beq t 0
  · have ht0 : t ≠ 0 := by intro h; subst h; simp at h0
    constructor
    · intro h
      have heq : isMeetLoop t B M = t := Nat.eq_of_beq_eq_true h
      rw [← heq]
      apply isMeetLoop_mem_meet (B := decM M '' { b | b ∈ B }) B (fun b hb => ⟨b, hb, rfl⟩)
      rw [decM_self]; exact Meet.top
    · intro hm
      have hsub_all : ∀ S, Meet (decM M '' { b | b ∈ B }) S → decM M t ⊆ S →
          decM M (isMeetLoop t B M) ⊆ S := by
        intro S hS
        induction hS with
        | atom hmem =>
          rcases hmem with ⟨b, hb, rfl⟩
          intro htb
          exact isMeetLoop_le_factor B hb ((decM_subset_iff ht).mp htb) M
        | top => intro _; exact Set.subset_univ _
        | bot =>
          intro hte
          have : decM M t = decM M 0 := by
            rw [decM_zero]; exact Set.subset_empty_iff.mp hte
          exact (ht0 ((decM_inj ht (by simp)).mp this)).elim
        | inter _ _ ih1 ih2 =>
          intro hsub
          exact Set.subset_inter (ih1 (hsub.trans Set.inter_subset_left))
            (ih2 (hsub.trans Set.inter_subset_right))
      have h1 : decM M (isMeetLoop t B M) ⊆ decM M t := hsub_all _ hm Set.Subset.rfl
      have h2 : decM M t ⊆ decM M (isMeetLoop t B M) :=
        (decM_subset_iff ht).mpr (isMeetLoop_target_sub B ht)
      have heq : isMeetLoop t B M = t :=
        (decM_inj (isMeetLoop_and_mask B (by simp)) ht).mp (Set.Subset.antisymm h1 h2)
      simp [heq]
  · have ht0 : t = 0 := Nat.eq_of_beq_eq_true h0
    subst ht0
    simp [decM_zero, Meet.bot]

theorem isOnEdges_sound {M edgePts g : ℕ} {B : List ℕ}
    (hg : g &&& M = g)
    (hon : isOnEdges M edgePts B g = true) :
    ∃ h : ℕ, h &&& M = h ∧ Meet (decM M '' { b | b ∈ B }) (decM M h) ∧
      decM M h ⊆ decM M g ∧ decM M h ∩ decM M edgePts = decM M g ∩ decM M edgePts := by
  unfold isOnEdges at hon
  set eg := Nat.land g edgePts
  set h := isMeetLoop eg B M
  have hhM : h &&& M = h := isMeetLoop_and_mask B (by simp)
  have hhg : h &&& g = h := by simpa [land_eq] using Nat.eq_of_beq_eq_true hon
  have hegM : eg &&& M = eg := by
    apply Nat.eq_of_testBit_eq; intro s
    have h1 := congrArg (fun x => x.testBit s) hg
    simp only [eg, land_eq, Nat.testBit_and] at h1 ⊢
    revert h1
    cases g.testBit s <;> cases edgePts.testBit s <;> cases M.testBit s <;> decide
  have hegh : eg &&& h = eg := isMeetLoop_target_sub B hegM
  refine ⟨h, hhM, ?_, (decM_subset_iff hhM).mpr hhg, ?_⟩
  · apply isMeetLoop_mem_meet (B := decM M '' { b | b ∈ B }) B (fun b hb => ⟨b, hb, rfl⟩)
    rw [decM_self]; exact Meet.top
  · have hsub1 : decM M h ⊆ decM M g := (decM_subset_iff hhM).mpr hhg
    have hsub2 : decM M g ∩ decM M edgePts ⊆ decM M h := by
      rw [← decM_and]
      exact (decM_subset_iff hegM).mpr hegh
    exact Set.Subset.antisymm (Set.inter_subset_inter_left _ hsub1)
      (Set.subset_inter hsub2 Set.inter_subset_right)



def MeetNat (M : ℕ) (B : List ℕ) (t : ℕ) : Prop :=
  t &&& M = t ∧ isMeet M B t = true

def ValidPrefix (M : ℕ) (B : List ℕ) : List ℕ → Prop
  | [] => True
  | g :: rest =>
    (∃ a b, MeetNat M B a ∧ MeetNat M B b ∧ g = a ||| b) ∧
    ValidPrefix M (B ++ [g]) rest

def RunListFrom (M : ℕ) (B : List ℕ) (target : ℕ) : List ℕ → Prop
  | [] => MeetNat M B target
  | g :: rest =>
    (∃ a b, MeetNat M B a ∧ MeetNat M B b ∧ g = a ||| b) ∧
    RunListFrom M (B ++ [g]) target rest

theorem meetNat_iff {M : ℕ} {B : List ℕ} {t : ℕ} :
    MeetNat M B t ↔ t &&& M = t ∧ Meet (decM M '' { b | b ∈ B }) (decM M t) := by
  constructor
  · rintro ⟨ht, hm⟩; exact ⟨ht, (isMeet_iff ht).mp hm⟩
  · rintro ⟨ht, hm⟩; exact ⟨ht, (isMeet_iff ht).mpr hm⟩

theorem meetNat_weaken {M : ℕ} {B₁ B₂ : List ℕ} (hsub : ∀ x ∈ B₁, x ∈ B₂) {t : ℕ}
    (ht : MeetNat M B₁ t) : MeetNat M B₂ t := by
  rw [meetNat_iff] at ht ⊢
  exact ⟨ht.1, weaken (Set.image_mono (fun x hx => hsub x hx)) ht.2⟩

theorem or_and_mask {a b M : ℕ} (ha : a &&& M = a) (hb : b &&& M = b) :
    (a ||| b) &&& M = a ||| b := by
  apply Nat.eq_of_testBit_eq; intro s
  have h1 := congrArg (fun x => x.testBit s) ha
  have h2 := congrArg (fun x => x.testBit s) hb
  simp only [Nat.testBit_and, Nat.testBit_or] at h1 h2 ⊢
  revert h1 h2
  cases a.testBit s <;> cases b.testBit s <;> cases M.testBit s <;> decide

theorem runListFrom_to_run {M target : ℕ} {B gs : List ℕ}
    (hr : RunListFrom M B target gs) :
    Run (decM M '' { x | x ∈ B }) gs.length (decM M target) := by
  induction gs generalizing B with
  | nil =>
    exact Run.done (meetNat_iff.mp hr).2
  | cons g rest ih =>
    rcases hr with ⟨⟨a, b, ha, hb, rfl⟩, hrest⟩
    have ih' := ih hrest
    have hset : decM M '' { x | x ∈ B ++ [a ||| b] } =
        insert (decM M a ∪ decM M b) (decM M '' { x | x ∈ B }) := by
      ext S
      simp only [Set.mem_image, Set.mem_ofPred_eq, List.mem_append, List.mem_singleton,
        Set.mem_insert_iff]
      constructor
      · rintro ⟨x, hx | rfl, rfl⟩
        · exact Or.inr ⟨x, hx, rfl⟩
        · exact Or.inl (decM_or M a b)
      · rintro (rfl | ⟨x, hx, rfl⟩)
        · exact ⟨a ||| b, Or.inr rfl, decM_or M a b⟩
        · exact ⟨x, Or.inl hx, rfl⟩
    rw [hset] at ih'
    exact Run.add (meetNat_iff.mp ha).2 (meetNat_iff.mp hb).2 ih'

theorem run_to_runListFrom {N M target : ℕ} (hM : ∀ s, M.testBit s = true → s < N)
    (ht : target &&& M = target) {B : List ℕ} {k : ℕ}
    (hr : Run (decM M '' { x | x ∈ B }) k (decM M target)) :
    ∃ gs : List ℕ, gs.length = k ∧ RunListFrom M B target gs := by
  induction k generalizing B with
  | zero =>
    cases hr with
    | done hm => exact ⟨[], rfl, meetNat_iff.mpr ⟨ht, hm⟩⟩
  | succ k ih =>
    cases hr with
    | @add _ a b _ _ ha hb tail =>
      let ea := encM N M a
      let eb := encM N M b
      have hea : ea &&& M = ea := encM_and_self a
      have heb : eb &&& M = eb := encM_and_self b
      have hda : decM M ea = a := decM_encM hM a
      have hdb : decM M eb = b := decM_encM hM b
      have hset : decM M '' { x | x ∈ B ++ [ea ||| eb] } =
          insert (a ∪ b) (decM M '' { x | x ∈ B }) := by
        ext S
        simp only [Set.mem_image, Set.mem_ofPred_eq, List.mem_append, List.mem_singleton,
          Set.mem_insert_iff]
        constructor
        · rintro ⟨x, hx | rfl, rfl⟩
          · exact Or.inr ⟨x, hx, rfl⟩
          · exact Or.inl (by rw [decM_or, hda, hdb])
        · rintro (rfl | ⟨x, hx, rfl⟩)
          · exact ⟨ea ||| eb, Or.inr rfl, by rw [decM_or, hda, hdb]⟩
          · exact ⟨x, Or.inl hx, rfl⟩
      rw [← hset] at tail
      obtain ⟨rest, hlen, hrun⟩ := ih tail
      refine ⟨(ea ||| eb) :: rest, by simp [hlen], ?_, hrun⟩
      exact ⟨ea, eb, meetNat_iff.mpr ⟨hea, hda.symm ▸ ha⟩,
        meetNat_iff.mpr ⟨heb, hdb.symm ▸ hb⟩, rfl⟩

theorem runListFrom_append {M target : ℕ} {B pre suf : List ℕ} :
    RunListFrom M B target (pre ++ suf) ↔
      ValidPrefix M B pre ∧ RunListFrom M (B ++ pre) target suf := by
  induction pre generalizing B with
  | nil => simp [ValidPrefix]
  | cons g rest ih =>
    simp only [List.cons_append, RunListFrom, ValidPrefix]
    rw [ih, List.append_assoc, List.singleton_append]
    tauto

theorem runListFrom_equiv_basis {M target : ℕ} {B₁ B₂ gs : List ℕ}
    (heq : ∀ x, x ∈ B₁ ↔ x ∈ B₂) :
    RunListFrom M B₁ target gs → RunListFrom M B₂ target gs := by
  induction gs generalizing B₁ B₂ with
  | nil => exact meetNat_weaken (fun x hx => (heq x).mp hx)
  | cons g rest ih =>
    rintro ⟨⟨a, b, ha, hb, rfl⟩, hrest⟩
    refine ⟨⟨a, b, meetNat_weaken (fun x hx => (heq x).mp hx) ha,
      meetNat_weaken (fun x hx => (heq x).mp hx) hb, rfl⟩, ?_⟩
    exact ih (fun x => by simp [heq x]) hrest

theorem validPrefix_mem_sub_mask {M : ℕ} {B pre : List ℕ} (hp : ValidPrefix M B pre) :
    ∀ g ∈ pre, g &&& M = g := by
  induction pre generalizing B with
  | nil => intro g hg; simp at hg
  | cons g rest ih =>
    rcases hp with ⟨⟨a, b, ha, hb, rfl⟩, hrest⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact or_and_mask ha.1 hb.1
    · exact ih hrest x hx

theorem validPrefix_to_run {M target : ℕ} {B pre : List ℕ} (hp : ValidPrefix M B pre)
    {k : ℕ} (hr : Run (decM M '' { x | x ∈ B ++ pre }) k (decM M target)) :
    Run (decM M '' { x | x ∈ B }) (pre.length + k) (decM M target) := by
  induction pre generalizing B with
  | nil => simpa using hr
  | cons g rest ih =>
    rcases hp with ⟨⟨a, b, ha, hb, rfl⟩, hrest⟩
    have hr' : Run (decM M '' { x | x ∈ (B ++ [a ||| b]) ++ rest }) k (decM M target) := by
      simpa only [List.append_assoc, List.singleton_append] using hr
    have hr1 := ih hrest hr'
    have hset : decM M '' { x | x ∈ B ++ [a ||| b] } =
        insert (decM M a ∪ decM M b) (decM M '' { x | x ∈ B }) := by
      ext S
      simp only [Set.mem_image, Set.mem_ofPred_eq, List.mem_append, List.mem_singleton,
        Set.mem_insert_iff]
      constructor
      · rintro ⟨x, hx | rfl, rfl⟩
        · exact Or.inr ⟨x, hx, rfl⟩
        · exact Or.inl (decM_or M a b)
      · rintro (rfl | ⟨x, hx, rfl⟩)
        · exact ⟨a ||| b, Or.inr rfl, decM_or M a b⟩
        · exact ⟨x, Or.inl hx, rfl⟩
    rw [hset] at hr1
    rw [List.length_cons, Nat.succ_add]
    exact Run.add (meetNat_iff.mp ha).2 (meetNat_iff.mp hb).2 hr1



theorem exists_lexMin_of_length {P : List ℕ → Prop} :
    ∀ k, (∃ gs, gs.length = k ∧ P gs) →
      ∃ gs, gs.length = k ∧ P gs ∧
        ∀ gs', gs'.length = k → P gs' → ¬ List.Lex (· < ·) gs' gs := by
  classical
  intro k
  induction k generalizing P with
  | zero =>
    rintro ⟨gs, hlen, hp⟩
    cases gs with
    | nil =>
      refine ⟨[], rfl, hp, fun gs' hlen' _ hlex => ?_⟩
      cases gs' with
      | nil => cases hlex
      | cons => simp at hlen'
    | cons => simp at hlen
  | succ k ih =>
    intro hex
    have hQ : ∃ x : ℕ, ∃ tail : List ℕ, tail.length = k ∧ P (x :: tail) := by
      rcases hex with ⟨gs, hlen, hp⟩
      cases gs with
      | nil => simp at hlen
      | cons x tail => exact ⟨x, tail, by simpa using hlen, hp⟩
    let x₀ := Nat.find hQ
    have hx₀ : ∃ tail : List ℕ, tail.length = k ∧ P (x₀ :: tail) := Nat.find_spec hQ
    obtain ⟨tail₀, hlen₀, hp₀, hmin₀⟩ := ih (P := fun t => P (x₀ :: t)) hx₀
    refine ⟨x₀ :: tail₀, by simp [hlen₀], hp₀, fun gs' hlen' hp' hlex => ?_⟩
    cases gs' with
    | nil => simp at hlen'
    | cons x' tail' =>
      cases hlex with
      | rel hlt =>
        exact Nat.find_min hQ hlt ⟨tail', by simpa using hlen', hp'⟩
      | cons hlex' =>
        exact hmin₀ tail' (by simpa using hlen') hp' hlex'

theorem exists_lexMinRun {n bound : ℕ} {H F : List (ℕ × ℕ)}
    (hex : ∃ k ≤ bound, HasRunYF n H F k) :
    ∃ (k : ℕ) (gs : List ℕ), k ≤ bound ∧ gs.length = k ∧
      RunListFrom (univYF n F) (rawYF n (univYF n F)) (edgeTTYF n H (univYF n F)) gs ∧
      (∀ k' < k, ¬ HasRunYF n H F k') ∧
      (∀ gs', gs'.length = k →
        RunListFrom (univYF n F) (rawYF n (univYF n F)) (edgeTTYF n H (univYF n F)) gs' →
        ¬ List.Lex (· < ·) gs' gs) := by
  classical
  have hEx : ∃ k, HasRunYF n H F k := by rcases hex with ⟨k, _, h⟩; exact ⟨k, h⟩
  let k := Nat.find hEx
  have hk_le : k ≤ bound := by
    rcases hex with ⟨k', hk', hr'⟩
    exact (Nat.find_min' hEx hr').trans hk'
  have hk_run : HasRunYF n H F k := Nat.find_spec hEx
  have hk_min : ∀ k' < k, ¬ HasRunYF n H F k' := fun k' hk' => Nat.find_min hEx hk'
  have hr_list : ∃ gs : List ℕ, gs.length = k ∧
      RunListFrom (univYF n F) (rawYF n (univYF n F)) (edgeTTYF n H (univYF n F)) gs := by
    apply run_to_runListFrom (N := 2 ^ n) (fun _ => univYF_testBit_lt) (edgeTTYF_and_univYF n H F)
    simpa only [HasRunYF, rawSet_eq_image, targetSet] using hk_run
  obtain ⟨gs, hlen, hrun, hlex⟩ := exists_lexMin_of_length k hr_list
  exact ⟨k, gs, hk_le, hlen, hrun, hk_min, hlex⟩



def bitLe {M : ℕ} (x y : Dom M) : Prop := x.1 &&& y.1 = x.1

theorem raw_upClosed {n : ℕ} {F : List (ℕ × ℕ)} {r : ℕ}
    (hr : r ∈ rawYF n (univYF n F)) :
    UpClosed (bitLe (M := univYF n F)) (decM (univYF n F) r) := by
  simp only [rawYF, List.mem_map, List.mem_range] at hr
  rcases hr with ⟨v, _, rfl⟩
  intro x y hxy hx
  simp only [decM, Set.mem_ofPred_eq, testBit_ttVarYF (fun _ => univYF_testBit_lt),
    x.2, y.2, Bool.true_and] at hx ⊢
  have := congrArg (fun z => z.testBit v) hxy
  rw [Nat.testBit_and, hx, Bool.true_and] at this
  exact this

theorem validPrefix_upClosed {M : ℕ} {B pre : List ℕ}
    (hB : ∀ r ∈ B, UpClosed (bitLe (M := M)) (decM M r))
    (hp : ValidPrefix M B pre) :
    ∀ x ∈ B ++ pre, UpClosed (bitLe (M := M)) (decM M x) := by
  induction pre generalizing B with
  | nil => simpa using hB
  | cons g rest ih =>
    rcases hp with ⟨⟨a, b, ha, hb, rfl⟩, hrest⟩
    have hB' : ∀ r ∈ B ++ [a ||| b], UpClosed (bitLe (M := M)) (decM M r) := by
      intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · exact hB r hr
      · rw [List.mem_singleton.mp hr, decM_or]
        have ha' : UpClosed (bitLe (M := M)) (decM M a) :=
          meet_upClosed (B := decM M '' { x | x ∈ B })
            (fun S hS => by rcases hS with ⟨x, hx, rfl⟩; exact hB x hx) (meetNat_iff.mp ha).2
        have hb' : UpClosed (bitLe (M := M)) (decM M b) :=
          meet_upClosed (B := decM M '' { x | x ∈ B })
            (fun S hS => by rcases hS with ⟨x, hx, rfl⟩; exact hB x hx) (meetNat_iff.mp hb).2
        intro x y hxy hmem
        rcases hmem with h1 | h2
        · exact Or.inl (ha' x y hxy h1)
        · exact Or.inr (hb' x y hxy h2)
    simpa [List.append_assoc] using ih hB' hrest

theorem edgePts_upClose_target {n : ℕ} {H F : List (ℕ × ℕ)} (hv : ValidState n H F) :
    (decM (univYF n F) (edgePtsMaskYF H) ⊆ targetSet n H F) ∧
    (∀ f : Set (Dom (univYF n F)), UpClosed (bitLe (M := univYF n F)) f →
      decM (univYF n F) (edgePtsMaskYF H) ⊆ f → targetSet n H F ⊆ f) := by
  constructor
  · intro s hs
    simp only [decM, Set.mem_ofPred_eq, testBit_edgePtsMaskYF, List.any_eq_true] at hs
    rcases hs with ⟨e, heH, heq⟩
    rw [decide_eq_true_eq] at heq
    change (edgeTTYF n H (univYF n F)).testBit s.1 = true
    rw [← heq]; exact edgePt_mem_edgeTTYF hv heH
  · intro f hf hsub s hs
    simp only [targetSet, decM, Set.mem_ofPred_eq,
      testBit_edgeTTYF (fun _ => univYF_testBit_lt), s.2, Bool.true_and, hasEdge_eq_true] at hs
    rcases hs with ⟨e, heH, h1, h2⟩
    let ep : ℕ := (1 <<< e.1) ||| (1 <<< e.2)
    have hepM : (univYF n F).testBit ep = true := edgePt_mem_univYF hv heH
    have hepPts : (⟨ep, hepM⟩ : Dom (univYF n F)) ∈ decM (univYF n F) (edgePtsMaskYF H) := by
      simp only [decM, Set.mem_ofPred_eq, testBit_edgePtsMaskYF, List.any_eq_true]
      exact ⟨e, heH, decide_eq_true rfl⟩
    have hle : bitLe (⟨ep, hepM⟩ : Dom (univYF n F)) s := by
      apply Nat.eq_of_testBit_eq; intro w
      rw [Nat.testBit_and]
      by_cases hw : ep.testBit w = true
      · rw [hw, Bool.true_and]
        rcases (twoBit_testBit e.1 e.2 w).mp hw with rfl | rfl
        · exact h1
        · exact h2
      · have hwf : ep.testBit w = false := Bool.eq_false_iff.mpr hw
        simp [hwf]
    exact hf ⟨ep, hepM⟩ s hle (hsub hepPts)

theorem lexMin_not_finished {n : ℕ} {H F : List (ℕ × ℕ)} {pre suf : List ℕ}
    (hrun : RunListFrom (univYF n F) (rawYF n (univYF n F)) (edgeTTYF n H (univYF n F)) (pre ++ suf))
    (hmin : ∀ k' < (pre ++ suf).length, ¬ HasRunYF n H F k')
    (hsuf : suf ≠ []) :
    isMeet (univYF n F) (rawYF n (univYF n F) ++ pre) (edgeTTYF n H (univYF n F)) = false := by
  rw [Bool.eq_false_iff]
  intro hm
  have hp : ValidPrefix (univYF n F) (rawYF n (univYF n F)) pre := (runListFrom_append.mp hrun).1
  have hr : RunListFrom (univYF n F) (rawYF n (univYF n F)) (edgeTTYF n H (univYF n F)) pre := by
    have h := runListFrom_append (M := univYF n F) (target := edgeTTYF n H (univYF n F))
      (B := rawYF n (univYF n F)) (pre := pre) (suf := [])
    rw [List.append_nil] at h
    exact h.mpr ⟨hp, edgeTTYF_and_univYF n H F, hm⟩
  have hr' := runListFrom_to_run hr
  rw [← rawSet_eq_image] at hr'
  have hlt : pre.length < (pre ++ suf).length := by
    cases suf with
    | nil => exact (hsuf rfl).elim
    | cons _ _ => simp
  exact hmin pre.length hlt hr'

theorem lexMin_eliminate_step {n : ℕ} {H F : List (ℕ × ℕ)} {pre suf : List ℕ} {g h : ℕ}
    (hv : ValidState n H F)
    (hrun : RunListFrom (univYF n F) (rawYF n (univYF n F)) (edgeTTYF n H (univYF n F)) (pre ++ g :: suf))
    (hmin : ∀ k' < (pre ++ g :: suf).length, ¬ HasRunYF n H F k')
    (hmh : Meet (decM (univYF n F) '' { x | x ∈ rawYF n (univYF n F) ++ pre }) (decM (univYF n F) h))
    (hsub : decM (univYF n F) h ⊆ decM (univYF n F) g)
    (heq : decM (univYF n F) h ∩ decM (univYF n F) (edgePtsMaskYF H) =
      decM (univYF n F) g ∩ decM (univYF n F) (edgePtsMaskYF H)) : False := by
  set M := univYF n F
  set raw := rawYF n M
  set target := edgeTTYF n H M
  obtain ⟨hp, hstep⟩ := runListFrom_append.mp hrun
  rcases hstep with ⟨_, hsuf⟩
  have hrun_suf : Run (decM M '' { x | x ∈ (raw ++ pre) ++ [g] }) suf.length (targetSet n H F) :=
    runListFrom_to_run hsuf
  have hD_up : ∀ S ∈ decM M '' { x | x ∈ raw ++ pre }, UpClosed (bitLe (M := M)) S := by
    rintro S ⟨x, hx, rfl⟩
    exact validPrefix_upClosed (fun r hr => raw_upClosed hr) hp x hx
  have hmap : ∀ S ∈ decM M '' { x | x ∈ (raw ++ pre) ++ [g] },
      ∃ S', Meet (decM M '' { x | x ∈ raw ++ pre }) S' ∧ S' ⊆ S ∧
        S' ∩ decM M (edgePtsMaskYF H) = S ∩ decM M (edgePtsMaskYF H) := by
    rintro S ⟨x, hx, rfl⟩
    rcases List.mem_append.mp hx with hx | hx
    · exact ⟨decM M x, Meet.atom ⟨x, hx, rfl⟩, Set.Subset.rfl, rfl⟩
    · rw [List.mem_singleton.mp hx]
      exact ⟨decM M h, hmh, hsub, heq⟩
  obtain ⟨hSt, hclose⟩ := edgePts_upClose_target hv
  have hrun_short : Run (decM M '' { x | x ∈ raw ++ pre }) suf.length (targetSet n H F) :=
    run_replaceBelow_upClosed hSt hclose hD_up hmap hrun_suf
  have hrun_full : HasRunYF n H F (pre.length + suf.length) := by
    have := validPrefix_to_run hp hrun_short
    rw [← rawSet_eq_image] at this
    exact this
  have hlt : pre.length + suf.length < (pre ++ g :: suf).length := by simp
  exact hmin _ hlt hrun_full

theorem lexMin_not_onEdges {n : ℕ} {H F : List (ℕ × ℕ)} {pre suf : List ℕ} {g : ℕ}
    (hv : ValidState n H F)
    (hrun : RunListFrom (univYF n F) (rawYF n (univYF n F)) (edgeTTYF n H (univYF n F)) (pre ++ g :: suf))
    (hmin : ∀ k' < (pre ++ g :: suf).length, ¬ HasRunYF n H F k') :
    isOnEdges (univYF n F) (edgePtsMaskYF H) (rawYF n (univYF n F) ++ pre) g = false := by
  rw [Bool.eq_false_iff]
  intro hon
  have hgM : g &&& univYF n F = g := by
    obtain ⟨_, ⟨a, b, ha, hb, rfl⟩, _⟩ := runListFrom_append.mp hrun
    exact or_and_mask ha.1 hb.1
  obtain ⟨h, _, hmh, hsub, heq⟩ := isOnEdges_sound hgM hon
  exact lexMin_eliminate_step hv hrun hmin hmh hsub heq



theorem ttNeedYF_zero {n M : ℕ} (hM : ∀ s, M.testBit s = true → s < 2 ^ n) :
    ttNeedYF n 0 M = M := by
  apply Nat.eq_of_testBit_eq; intro s
  rw [testBit_ttNeedYF hM]; simp

theorem ttNeedYF_oneBit {n v M : ℕ} (hM : ∀ s, M.testBit s = true → s < 2 ^ n) :
    ttNeedYF n (1 <<< v) M = ttVarYF n v M := by
  apply Nat.eq_of_testBit_eq; intro s
  rw [testBit_ttNeedYF hM, testBit_ttVarYF hM]
  have hbit : ((s &&& (1 <<< v)) == (1 <<< v)) = s.testBit v := by
    apply Bool.eq_iff_iff.mpr
    rw [beq_iff_eq]
    constructor
    · intro heq
      have := congrArg (fun z => z.testBit v) heq
      rw [Nat.testBit_and, testBit_one_shiftLeft] at this
      simpa using this
    · intro hs
      apply Nat.eq_of_testBit_eq; intro w
      rw [Nat.testBit_and, testBit_one_shiftLeft]
      by_cases hw : v = w
      · subst hw; simp [hs]
      · simp [hw]
  rw [hbit]

theorem ttNeedYF_or {n a b M : ℕ} (hM : ∀ s, M.testBit s = true → s < 2 ^ n) :
    ttNeedYF n a M &&& ttNeedYF n b M = ttNeedYF n (a ||| b) M := by
  apply Nat.eq_of_testBit_eq; intro s
  rw [Nat.testBit_and, testBit_ttNeedYF hM, testBit_ttNeedYF hM, testBit_ttNeedYF hM]
  cases hm : M.testBit s
  · simp
  · simp only [Bool.true_and]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, beq_iff_eq]
    constructor
    · rintro ⟨ha, hb⟩
      apply Nat.eq_of_testBit_eq; intro w
      have h1 := congrArg (fun z => z.testBit w) ha
      have h2 := congrArg (fun z => z.testBit w) hb
      simp only [Nat.testBit_and, Nat.testBit_or] at h1 h2 ⊢
      revert h1 h2
      cases s.testBit w <;> cases a.testBit w <;> cases b.testBit w <;> decide
    · intro hab
      constructor <;> apply Nat.eq_of_testBit_eq <;> intro w <;>
        (have h := congrArg (fun z => z.testBit w) hab
         simp only [Nat.testBit_and, Nat.testBit_or] at h ⊢
         revert h
         cases s.testBit w <;> cases a.testBit w <;> cases b.testBit w <;> decide)

theorem foldl_land_assoc (xs : List ℕ) (a b : ℕ) :
    xs.foldl Nat.land (a &&& b) = a &&& xs.foldl Nat.land b := by
  induction xs generalizing a b with
  | nil => rfl
  | cons x rest ih =>
    simp only [List.foldl_cons, land_eq]
    rw [Nat.and_assoc, ih a (b &&& x)]

theorem foldl_land_append (xs ys : List ℕ) (M : ℕ) :
    (xs ++ ys).foldl Nat.land M = xs.foldl Nat.land M &&& ys.foldl Nat.land M := by
  rw [List.foldl_append]
  have h1 : xs.foldl Nat.land M = xs.foldl Nat.land M &&& M := by
    induction xs generalizing M with
    | nil => simp
    | cons x rest ih =>
      simp only [List.foldl_cons, land_eq]
      rw [foldl_land_assoc]
      apply Nat.eq_of_testBit_eq; intro s
      simp only [Nat.testBit_and]
      cases M.testBit s <;> cases (rest.foldl Nat.land x).testBit s <;> simp
  conv_lhs => rw [h1]
  exact foldl_land_assoc ys (xs.foldl Nat.land M) M

theorem foldl_land_mem_eq {xs ys : List ℕ} {M : ℕ}
    (heq : ∀ x, x ∈ xs ↔ x ∈ ys) :
    xs.foldl Nat.land M = ys.foldl Nat.land M := by
  have hbit : ∀ (zs : List ℕ) (acc s : ℕ),
      (zs.foldl Nat.land acc).testBit s = true ↔
        acc.testBit s = true ∧ ∀ z ∈ zs, z.testBit s = true := by
    intro zs
    induction zs with
    | nil => intro acc s; simp
    | cons z rest ih =>
      intro acc s
      simp only [List.foldl_cons, land_eq, ih, Nat.testBit_and, Bool.and_eq_true, List.mem_cons]
      constructor
      · rintro ⟨⟨ha, hz⟩, hrest⟩
        exact ⟨ha, fun w hw => hw.elim (fun e => e ▸ hz) (hrest w)⟩
      · rintro ⟨ha, hall⟩
        exact ⟨⟨ha, hall z (Or.inl rfl)⟩, fun w hw => hall w (Or.inr hw)⟩
  apply Nat.eq_of_testBit_eq; intro s
  apply Bool.eq_iff_iff.mpr
  rw [hbit xs M s, hbit ys M s]
  constructor
  · rintro ⟨hM, h⟩; exact ⟨hM, fun z hz => h z ((heq z).mpr hz)⟩
  · rintro ⟨hM, h⟩; exact ⟨hM, fun z hz => h z ((heq z).mp hz)⟩

theorem meet_decompose_nat {n : ℕ} {F : List (ℕ × ℕ)} {pre : List ℕ}
    {S : Set (Dom (univYF n F))}
    (hm : Meet (decM (univYF n F) '' { x | x ∈ rawYF n (univYF n F) ++ pre }) S) :
    S = ∅ ∨ ∃ (rMask : ℕ) (P : List ℕ), (∀ p ∈ P, p ∈ pre) ∧
      S = decM (univYF n F) (ttNeedYF n rMask (univYF n F) &&& P.foldl Nat.land (univYF n F)) := by
  have hM : ∀ s, (univYF n F).testBit s = true → s < 2 ^ n := fun _ => univYF_testBit_lt
  induction hm with
  | atom hx =>
    rcases hx with ⟨y, hy, rfl⟩
    rcases List.mem_append.mp hy with hy | hy
    · simp only [rawYF, List.mem_map, List.mem_range] at hy
      rcases hy with ⟨v, _, rfl⟩
      refine Or.inr ⟨1 <<< v, [], fun _ h => by simp at h, ?_⟩
      simp only [List.foldl_nil, ttNeedYF_oneBit hM, ttVarYF_and_mask hM]
    · refine Or.inr ⟨0, [y], fun p hp => (List.mem_singleton.mp hp) ▸ hy, ?_⟩
      simp only [List.foldl_cons, List.foldl_nil, land_eq, ttNeedYF_zero hM]
      rw [decM_and, decM_and, decM_self, Set.univ_inter, Set.univ_inter]
  | top =>
    refine Or.inr ⟨0, [], fun _ h => by simp at h, ?_⟩
    simp only [List.foldl_nil, ttNeedYF_zero hM, Nat.and_self, decM_self]
  | bot => exact Or.inl rfl
  | inter _ _ ih1 ih2 =>
    rcases ih1 with rfl | ⟨r1, P1, hP1, rfl⟩
    · exact Or.inl (Set.empty_inter _)
    rcases ih2 with rfl | ⟨r2, P2, hP2, rfl⟩
    · exact Or.inl (Set.inter_empty _)
    refine Or.inr ⟨r1 ||| r2, P1 ++ P2, fun p hp => (List.mem_append.mp hp).elim (hP1 p) (hP2 p), ?_⟩
    rw [← decM_and, ← ttNeedYF_or hM, foldl_land_append]
    congr 1
    apply Nat.eq_of_testBit_eq; intro s
    simp only [Nat.testBit_and]
    cases (ttNeedYF n r1 (univYF n F)).testBit s <;> cases (ttNeedYF n r2 (univYF n F)).testBit s <;>
      cases (P1.foldl Nat.land (univYF n F)).testBit s <;>
      cases (P2.foldl Nat.land (univYF n F)).testBit s <;> simp

theorem meetNat_decompose_on_edges {n : ℕ} {H F : List (ℕ × ℕ)} {pre : List ℕ} {x : ℕ}
    (hv : ValidState n H F)
    (hx : MeetNat (univYF n F) (rawYF n (univYF n F) ++ pre) x)
    (hne : x &&& edgePtsMaskYF H ≠ 0) :
    ∃ mt ∈ masksTTYF n H (univYF n F), ∃ P : List ℕ, List.Sublist P pre ∧
      x = mt &&& P.foldl Nat.land (univYF n F) := by
  set M := univYF n F
  have hM : ∀ s, M.testBit s = true → s < 2 ^ n := fun _ => univYF_testBit_lt
  rcases meet_decompose_nat (meetNat_iff.mp hx).2 with hemp | ⟨rMask, P, hP, hS⟩
  · exfalso
    have hx0 : x = 0 := (decM_inj hx.1 (by simp)).mp (by rw [hemp, decM_zero])
    simp [hx0] at hne
  have hxEq : x = ttNeedYF n rMask M &&& P.foldl Nat.land M := by
    apply (decM_inj hx.1 ?_).mp hS
    apply Nat.eq_of_testBit_eq; intro s
    have ht := congrArg (fun z => z.testBit s) (ttNeedYF_and_mask (n := n) (a := rMask) hM)
    simp only [Nat.testBit_and] at ht ⊢
    revert ht
    cases (ttNeedYF n rMask M).testBit s <;> cases (P.foldl Nat.land M).testBit s <;>
      cases M.testBit s <;> decide
  have hexBit : ∃ s, (x &&& edgePtsMaskYF H).testBit s = true := by
    by_contra hall
    push Not at hall
    apply hne
    apply Nat.eq_of_testBit_eq; intro s
    simp only [Nat.zero_testBit]
    exact Bool.eq_false_iff.mpr (hall s)
  obtain ⟨s, hs⟩ := hexBit
  rw [Nat.testBit_and, Bool.and_eq_true, testBit_edgePtsMaskYF, List.any_eq_true] at hs
  obtain ⟨hxs, e, heH, hes⟩ := hs
  rw [decide_eq_true_eq] at hes
  have hneed : (ttNeedYF n rMask M).testBit s = true := by
    rw [hxEq, Nat.testBit_and, Bool.and_eq_true] at hxs; exact hxs.1
  rw [testBit_ttNeedYF hM, Bool.and_eq_true, beq_iff_eq] at hneed
  have hrSub : ∀ w, rMask.testBit w = true → w = e.1 ∨ w = e.2 := by
    intro w hw
    have := congrArg (fun z => z.testBit w) hneed.2
    rw [Nat.testBit_and, hw, Bool.and_true] at this
    rw [← hes] at this
    exact (twoBit_testBit e.1 e.2 w).mp this
  obtain ⟨he1, he2, _⟩ := hv.1 e heH
  have hrMem : ttNeedYF n rMask M ∈ masksTTYF n H M := by
    unfold masksTTYF
    apply List.mem_map.mpr
    refine ⟨rMask, ?_, rfl⟩
    cases hb1 : rMask.testBit e.1 <;> cases hb2 : rMask.testBit e.2
    · have hr0 : rMask = 0 := by
        apply Nat.eq_of_testBit_eq; intro w
        cases hw : rMask.testBit w
        · simp
        · rcases hrSub w hw with rfl | rfl <;> simp_all
      subst hr0; simp
    · have hr2 : rMask = 1 <<< e.2 := by
        apply Nat.eq_of_testBit_eq; intro w
        rw [testBit_one_shiftLeft]
        by_cases hw : e.2 = w
        · subst hw; simp [hb2]
        · simp only [hw, decide_false]
          cases hrw : rMask.testBit w
          · rfl
          · rcases hrSub w hrw with rfl | rfl <;> simp_all
      subst hr2
      simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_map, List.mem_range]
      exact Or.inr (Or.inl ⟨e.2, he2, rfl⟩)
    · have hr1 : rMask = 1 <<< e.1 := by
        apply Nat.eq_of_testBit_eq; intro w
        rw [testBit_one_shiftLeft]
        by_cases hw : e.1 = w
        · subst hw; simp [hb1]
        · simp only [hw, decide_false]
          cases hrw : rMask.testBit w
          · rfl
          · rcases hrSub w hrw with rfl | rfl <;> simp_all
      subst hr1
      simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_map, List.mem_range]
      exact Or.inr (Or.inl ⟨e.1, he1, rfl⟩)
    · have hr12 : rMask = (1 <<< e.1) ||| (1 <<< e.2) := by
        apply Nat.eq_of_testBit_eq; intro w
        rw [Nat.testBit_or, testBit_one_shiftLeft, testBit_one_shiftLeft]
        by_cases hw1 : e.1 = w
        · subst hw1; simp [hb1]
        · by_cases hw2 : e.2 = w
          · subst hw2; simp [hb2]
          · simp only [hw1, hw2, decide_false, Bool.or_false]
            cases hrw : rMask.testBit w
            · rfl
            · rcases hrSub w hrw with rfl | rfl <;> simp_all
      subst hr12
      simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_map]
      exact Or.inr (Or.inr ⟨e, heH, rfl⟩)
  let P' := pre.filter (fun y => P.contains y)
  have hsub : List.Sublist P' pre := List.filter_sublist
  have hPeq : ∀ y, y ∈ P ↔ y ∈ P' := by
    intro y
    simp only [P', List.mem_filter, List.contains_eq_mem, decide_eq_true_eq]
    exact ⟨fun hy => ⟨hP y hy, hy⟩, fun h => h.2⟩
  refine ⟨ttNeedYF n rMask M, hrMem, P', hsub, ?_⟩
  rw [hxEq, foldl_land_mem_eq hPeq]

theorem lexMin_operands {n : ℕ} {H F : List (ℕ × ℕ)} {pre suf : List ℕ} {g : ℕ}
    (hv : ValidState n H F)
    (hrun : RunListFrom (univYF n F) (rawYF n (univYF n F)) (edgeTTYF n H (univYF n F)) (pre ++ g :: suf))
    (hmin : ∀ k' < (pre ++ g :: suf).length, ¬ HasRunYF n H F k') :
    ∃ a b : ℕ, g = a ||| b ∧ a ≠ b ∧
      MeetNat (univYF n F) (rawYF n (univYF n F) ++ pre) a ∧
      MeetNat (univYF n F) (rawYF n (univYF n F) ++ pre) b ∧
      a ≠ 0 ∧ a ≠ univYF n F ∧ a &&& edgePtsMaskYF H ≠ 0 ∧
      b ≠ 0 ∧ b ≠ univYF n F ∧ b &&& edgePtsMaskYF H ≠ 0 := by
  set M := univYF n F
  set raw := rawYF n M
  set ep := edgePtsMaskYF H
  obtain ⟨_, ⟨a, b, ha, hb, hgab⟩, _⟩ := runListFrom_append.mp hrun
  have ha_ep : a &&& ep ≠ 0 := by
    intro h0
    have hsub : decM M b ⊆ decM M g := by
      rw [hgab, decM_or]; exact Set.subset_union_right
    have heq : decM M b ∩ decM M ep = decM M g ∩ decM M ep := by
      rw [hgab, decM_or, Set.union_inter_distrib_right]
      have ha0' : decM M a ∩ decM M ep = ∅ := by rw [← decM_and, h0, decM_zero]
      rw [ha0', Set.empty_union]
    exact lexMin_eliminate_step hv hrun hmin (meetNat_iff.mp hb).2 hsub heq
  have hb_ep : b &&& ep ≠ 0 := by
    intro h0
    have hsub : decM M a ⊆ decM M g := by
      rw [hgab, decM_or]; exact Set.subset_union_left
    have heq : decM M a ∩ decM M ep = decM M g ∩ decM M ep := by
      rw [hgab, decM_or, Set.union_inter_distrib_right]
      have hb0' : decM M b ∩ decM M ep = ∅ := by rw [← decM_and, h0, decM_zero]
      rw [hb0', Set.union_empty]
    exact lexMin_eliminate_step hv hrun hmin (meetNat_iff.mp ha).2 hsub heq
  have ha0 : a ≠ 0 := fun h => ha_ep (by simp [h])
  have hb0 : b ≠ 0 := fun h => hb_ep (by simp [h])
  have haM : a ≠ M := by
    intro h
    have hgm : g = M := by
      rw [hgab, h]
      apply Nat.eq_of_testBit_eq; intro s
      have h1 := congrArg (fun z => z.testBit s) hb.1
      simp only [Nat.testBit_or, Nat.testBit_and] at h1 ⊢
      revert h1
      cases M.testBit s <;> cases b.testBit s <;> decide
    exact lexMin_eliminate_step hv hrun hmin (hgm ▸ decM_self M ▸ Meet.top) Set.Subset.rfl rfl
  have hbM : b ≠ M := by
    intro h
    have hgm : g = M := by
      rw [hgab, h]
      apply Nat.eq_of_testBit_eq; intro s
      have h1 := congrArg (fun z => z.testBit s) ha.1
      simp only [Nat.testBit_or, Nat.testBit_and] at h1 ⊢
      revert h1
      cases M.testBit s <;> cases a.testBit s <;> decide
    exact lexMin_eliminate_step hv hrun hmin (hgm ▸ decM_self M ▸ Meet.top) Set.Subset.rfl rfl
  have hab : a ≠ b := by
    intro h
    have hga : g = a := by rw [hgab, h, Nat.or_self]
    exact lexMin_eliminate_step hv hrun hmin (hga ▸ (meetNat_iff.mp ha).2) Set.Subset.rfl rfl
  exact ⟨a, b, hgab, hab, ha, hb, ha0, haM, ha_ep, hb0, hbM, hb_ep⟩



theorem lex_append_left {α : Type} {r : α → α → Prop} :
    ∀ (pre l₁ l₂ : List α), List.Lex r l₁ l₂ → List.Lex r (pre ++ l₁) (pre ++ l₂)
  | [], _, _, h => h
  | _ :: rest, l₁, l₂, h => List.Lex.cons (lex_append_left rest l₁ l₂ h)

theorem lexMin_commSwap {n : ℕ} {H F : List (ℕ × ℕ)} {pre0 suf : List ℕ} {lastG g a b : ℕ}
    (hrun : RunListFrom (univYF n F) (rawYF n (univYF n F)) (edgeTTYF n H (univYF n F))
      (pre0 ++ lastG :: g :: suf))
    (hlex : ∀ gs', gs'.length = (pre0 ++ lastG :: g :: suf).length →
      RunListFrom (univYF n F) (rawYF n (univYF n F)) (edgeTTYF n H (univYF n F)) gs' →
      ¬ List.Lex (· < ·) gs' (pre0 ++ lastG :: g :: suf))
    (ha : MeetNat (univYF n F) (rawYF n (univYF n F) ++ pre0) a)
    (hb : MeetNat (univYF n F) (rawYF n (univYF n F) ++ pre0) b)
    (hg : g = a ||| b) :
    ¬ (g < lastG) := by
  intro hlt
  set M := univYF n F
  set raw := rawYF n M
  set target := edgeTTYF n H M
  obtain ⟨hp0, ⟨a0, b0, ha0, hb0, hlg⟩, _, hsuf⟩ := runListFrom_append.mp hrun
  let gs' := pre0 ++ g :: lastG :: suf
  have hlen : gs'.length = (pre0 ++ lastG :: g :: suf).length := by simp [gs']
  have hrun' : RunListFrom M raw target gs' := by
    apply runListFrom_append.mpr
    refine ⟨hp0, ⟨a, b, ha, hb, hg⟩, ?_, ?_⟩
    · refine ⟨a0, b0, meetNat_weaken (fun x hx => List.mem_append_left _ hx) ha0,
        meetNat_weaken (fun x hx => List.mem_append_left _ hx) hb0, hlg⟩
    · apply runListFrom_equiv_basis (B₁ := (raw ++ pre0) ++ [lastG] ++ [g]) _ hsuf
      intro x; simp; tauto
  have hl : List.Lex (· < ·) gs' (pre0 ++ lastG :: g :: suf) :=
    lex_append_left pre0 (g :: lastG :: suf) (lastG :: g :: suf) (List.Lex.rel hlt)
  exact hlex gs' hlen hrun' hl



def applyPermLoop (tbl : List ℕ) (f : ℕ) (s : ℕ) (acc : ℕ) : ℕ :=
  match tbl with
  | [] => acc
  | s2 :: rest =>
    let acc' := match f.testBit s with
      | true => Nat.lor acc (1 <<< s2)
      | false => acc
    applyPermLoop rest f (s + 1) acc'

def applyPerm (tbl : List ℕ) (f : ℕ) : ℕ :=
  applyPermLoop tbl f 0 0

theorem applyPermLoop_testBit (tbl : List ℕ) (f s acc y : ℕ) :
    (applyPermLoop tbl f s acc).testBit y = true ↔
      acc.testBit y = true ∨
      ∃ (i : ℕ) (hi : i < tbl.length), tbl[i] = y ∧ f.testBit (s + i) = true := by
  induction tbl generalizing s acc with
  | nil => simp [applyPermLoop]
  | cons s2 rest ih =>
    simp only [applyPermLoop]
    rw [ih]
    have hacc' : (match f.testBit s with
        | true => Nat.lor acc (1 <<< s2)
        | false => acc).testBit y = true ↔
        acc.testBit y = true ∨ (f.testBit s = true ∧ s2 = y) := by
      cases hfs : f.testBit s
      · simp
      · simp only [lor_eq, Nat.testBit_or, testBit_one_shiftLeft, Bool.or_eq_true,
          decide_eq_true_eq, true_and]
    rw [hacc']
    constructor
    · rintro ((ha | ⟨hfs, rfl⟩) | ⟨i, hi, hget, hfi⟩)
      · exact Or.inl ha
      · exact Or.inr ⟨0, by simp, rfl, by simpa using hfs⟩
      · exact Or.inr ⟨i + 1, by simp [hi], by simpa using hget,
          by rwa [show s + (i + 1) = s + 1 + i by omega]⟩
    · rintro (ha | ⟨i, hi, hget, hfi⟩)
      · exact Or.inl (Or.inl ha)
      · cases i with
        | zero => exact Or.inl (Or.inr ⟨by simpa using hfi, by simpa using hget⟩)
        | succ j =>
          exact Or.inr ⟨j, by simpa using hi, by simpa using hget,
            by rwa [show s + 1 + j = s + (j + 1) by omega]⟩

theorem applyPerm_testBit (tbl : List ℕ) (f y : ℕ) :
    (applyPerm tbl f).testBit y = true ↔
      ∃ (i : ℕ) (hi : i < tbl.length), tbl[i] = y ∧ f.testBit i = true := by
  simpa [applyPerm] using applyPermLoop_testBit tbl f 0 0 y

theorem applyPerm_zero (tbl : List ℕ) : applyPerm tbl 0 = 0 := by
  apply Nat.eq_of_testBit_eq; intro y
  apply Bool.eq_iff_iff.mpr
  simp [applyPerm_testBit]

theorem applyPerm_or (tbl : List ℕ) (a b : ℕ) :
    applyPerm tbl (a ||| b) = applyPerm tbl a ||| applyPerm tbl b := by
  apply Nat.eq_of_testBit_eq; intro y
  apply Bool.eq_iff_iff.mpr
  simp only [applyPerm_testBit, Nat.testBit_or, Bool.or_eq_true]
  constructor
  · rintro ⟨i, hi, hget, ha | hb⟩
    · exact Or.inl ⟨i, hi, hget, ha⟩
    · exact Or.inr ⟨i, hi, hget, hb⟩
  · rintro (⟨i, hi, hget, ha⟩ | ⟨i, hi, hget, hb⟩)
    · exact ⟨i, hi, hget, Or.inl ha⟩
    · exact ⟨i, hi, hget, Or.inr hb⟩

theorem applyPerm_and {tbl : List ℕ} (hnd : tbl.Nodup) (a b : ℕ) :
    applyPerm tbl (a &&& b) = applyPerm tbl a &&& applyPerm tbl b := by
  apply Nat.eq_of_testBit_eq; intro y
  apply Bool.eq_iff_iff.mpr
  simp only [applyPerm_testBit, Nat.testBit_and, Bool.and_eq_true]
  constructor
  · rintro ⟨i, hi, hget, ha, hb⟩
    exact ⟨⟨i, hi, hget, ha⟩, ⟨i, hi, hget, hb⟩⟩
  · rintro ⟨⟨i, hi, hgeti, ha⟩, ⟨j, hj, hgetj, hb⟩⟩
    have hij : i = j := (List.Nodup.getElem_inj_iff hnd).mp (hgeti.trans hgetj.symm)
    subst hij
    exact ⟨i, hi, hgeti, ha, hb⟩

def ValidAutTbl (M edgeTT : ℕ) (raw tbl : List ℕ) : Prop :=
  tbl.Nodup ∧ applyPerm tbl M = M ∧ applyPerm tbl edgeTT = edgeTT ∧
    ∀ r ∈ raw, applyPerm tbl r ∈ raw

instance (M edgeTT : ℕ) (raw tbl : List ℕ) : Decidable (ValidAutTbl M edgeTT raw tbl) := by
  unfold ValidAutTbl; infer_instance

theorem applyPerm_isMeetLoop {tbl : List ℕ} (hnd : tbl.Nodup) (M : ℕ)
    {B B' : List ℕ} (hB : ∀ b ∈ B, applyPerm tbl b ∈ B') {t acc : ℕ}
    (hacc : Meet (decM M '' { x | x ∈ B' }) (decM M (applyPerm tbl acc))) :
    Meet (decM M '' { x | x ∈ B' }) (decM M (applyPerm tbl (isMeetLoop t B acc))) := by
  induction B generalizing acc with
  | nil => exact hacc
  | cons b bs ih =>
    simp only [isMeetLoop]
    cases Nat.beq (Nat.land t b) t
    · exact ih (fun x hx => hB x (by simp [hx])) hacc
    · apply ih (fun x hx => hB x (by simp [hx]))
      rw [land_eq, applyPerm_and hnd, decM_and]
      exact hacc.inter (Meet.atom ⟨applyPerm tbl b, hB b (by simp), rfl⟩)

theorem applyPerm_meetNat {tbl : List ℕ} (hnd : tbl.Nodup) {M : ℕ} (hM : applyPerm tbl M = M)
    {B B' : List ℕ} (hB : ∀ b ∈ B, applyPerm tbl b ∈ B') {t : ℕ}
    (ht : MeetNat M B t) : MeetNat M B' (applyPerm tbl t) := by
  have htM : applyPerm tbl t &&& M = applyPerm tbl t := by
    rw [← hM, ← applyPerm_and hnd, ht.1]
  refine ⟨htM, (isMeet_iff htM).mpr ?_⟩
  rcases ht with ⟨_, hmt⟩
  unfold isMeet at hmt
  cases h0 : Nat.beq t 0
  · rw [h0] at hmt
    have heq : isMeetLoop t B M = t := Nat.eq_of_beq_eq_true hmt
    rw [← heq]
    apply applyPerm_isMeetLoop hnd M hB
    rw [hM, decM_self]; exact Meet.top
  · have ht0 : t = 0 := Nat.eq_of_beq_eq_true h0
    subst ht0
    rw [applyPerm_zero, decM_zero]; exact Meet.bot

theorem applyPerm_runListFrom {tbl : List ℕ} (hnd : tbl.Nodup) {M edgeTT : ℕ}
    (hM : applyPerm tbl M = M) (hE : applyPerm tbl edgeTT = edgeTT)
    {B B' gs : List ℕ} (hB : ∀ b ∈ B, applyPerm tbl b ∈ B')
    (hr : RunListFrom M B edgeTT gs) :
    RunListFrom M B' edgeTT (gs.map (applyPerm tbl)) := by
  induction gs generalizing B B' with
  | nil =>
    rw [← hE]
    exact applyPerm_meetNat hnd hM hB hr
  | cons g rest ih =>
    rcases hr with ⟨⟨a, b, ha, hb, rfl⟩, hrest⟩
    refine ⟨⟨applyPerm tbl a, applyPerm tbl b,
      applyPerm_meetNat hnd hM hB ha, applyPerm_meetNat hnd hM hB hb,
      applyPerm_or tbl a b⟩, ?_⟩
    apply ih (B' := B' ++ [applyPerm tbl (a ||| b)]) _ hrest
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_append_left _ (hB x hx)
    · rw [List.mem_singleton.mp hx]; exact List.mem_append_right _ (by simp)

theorem list_map_eq_self {α : Type} {f : α → α} :
    ∀ (l : List α), (∀ x ∈ l, f x = x) → l.map f = l
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.map_cons, h x (by simp), list_map_eq_self xs (fun y hy => h y (by simp [hy]))]

theorem lexMin_autStab {n : ℕ} {H F : List (ℕ × ℕ)} {pre suf tbl : List ℕ} {g : ℕ}
    (haut : ValidAutTbl (univYF n F) (edgeTTYF n H (univYF n F)) (rawYF n (univYF n F)) tbl)
    (hstab : ∀ h ∈ pre, applyPerm tbl h = h)
    (hrun : RunListFrom (univYF n F) (rawYF n (univYF n F)) (edgeTTYF n H (univYF n F))
      (pre ++ g :: suf))
    (hlex : ∀ gs', gs'.length = (pre ++ g :: suf).length →
      RunListFrom (univYF n F) (rawYF n (univYF n F)) (edgeTTYF n H (univYF n F)) gs' →
      ¬ List.Lex (· < ·) gs' (pre ++ g :: suf)) :
    ¬ (applyPerm tbl g < g) := by
  intro hlt
  rcases haut with ⟨hnd, hM, hE, hraw⟩
  let gs' := (pre ++ g :: suf).map (applyPerm tbl)
  have hrun' := applyPerm_runListFrom hnd hM hE hraw hrun
  have hpre_eq : pre.map (applyPerm tbl) = pre := list_map_eq_self pre hstab
  have hgs' : gs' = pre ++ applyPerm tbl g :: suf.map (applyPerm tbl) := by
    simp [gs', hpre_eq]
  have hl : List.Lex (· < ·) gs' (pre ++ g :: suf) := by
    rw [hgs']
    exact lex_append_left pre _ _ (List.Lex.rel hlt)
  exact hlex gs' (by simp [gs']) hrun' hl



theorem validPrefix_weaken_basis {M : ℕ} {B₁ B₂ pre : List ℕ}
    (hsub : ∀ x ∈ B₁, x ∈ B₂) (hp : ValidPrefix M B₁ pre) :
    ValidPrefix M B₂ pre := by
  induction pre generalizing B₁ B₂ with
  | nil => trivial
  | cons g rest ih =>
    rcases hp with ⟨⟨a, b, ha, hb, rfl⟩, hrest⟩
    refine ⟨⟨a, b, meetNat_weaken hsub ha, meetNat_weaken hsub hb, rfl⟩, ?_⟩
    exact ih (fun x hx => by
      rcases List.mem_append.mp hx with hx | hx
      · exact List.mem_append_left _ (hsub x hx)
      · exact List.mem_append_right _ hx) hrest

theorem validPrefix_append {M : ℕ} {B p₁ p₂ : List ℕ} :
    ValidPrefix M B (p₁ ++ p₂) ↔ ValidPrefix M B p₁ ∧ ValidPrefix M (B ++ p₁) p₂ := by
  induction p₁ generalizing B with
  | nil => simp [ValidPrefix]
  | cons g rest ih =>
    simp only [List.cons_append, ValidPrefix]
    rw [ih, List.append_assoc, List.singleton_append]
    tauto

theorem lexMin_birth_lex {n : ℕ} {H F : List (ℕ × ℕ)} {pre suf : List ℕ} {g a b mb t : ℕ}
    (hrun : RunListFrom (univYF n F) (rawYF n (univYF n F)) (edgeTTYF n H (univYF n F))
      (pre ++ g :: suf))
    (hlex : ∀ gs', gs'.length = (pre ++ g :: suf).length →
      RunListFrom (univYF n F) (rawYF n (univYF n F)) (edgeTTYF n H (univYF n F)) gs' →
      ¬ List.Lex (· < ·) gs' (pre ++ g :: suf))
    (hmb : mb ≤ t) (ht : t < pre.length)
    (ha : MeetNat (univYF n F) (rawYF n (univYF n F) ++ pre.take mb) a)
    (hb : MeetNat (univYF n F) (rawYF n (univYF n F) ++ pre.take mb) b)
    (hg : g = a ||| b) :
    ¬ (g < pre[t]) := by
  intro hlt
  set M := univYF n F
  set raw := rawYF n M
  set target := edgeTTYF n H M
  let A := pre.take t
  let B := pre.drop t
  have hpreAB : pre = A ++ B := (List.take_append_drop t pre).symm
  have hBne : B ≠ [] := by
    intro hB
    have hlen := congrArg List.length hpreAB
    simp only [hB, List.append_nil, List.length_take, A] at hlen
    omega
  obtain ⟨bt, Btail, hBeq⟩ := List.exists_cons_of_ne_nil hBne
  have hbt : bt = pre[t] := by
    have h1 : B[0]'(by simp [hBeq]) = pre[t] := by
      simp [B]
    simpa [hBeq] using h1
  have hpre_sub : ∀ x ∈ raw ++ pre.take mb, x ∈ raw ++ A := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_append_left _ hx
    · refine List.mem_append_right _ ?_
      have htake : pre.take mb = (pre.take t).take mb := by
        rw [List.take_take, Nat.min_eq_left hmb]
      rw [htake] at hx
      exact List.mem_of_mem_take hx
  have haA : MeetNat M (raw ++ A) a := meetNat_weaken hpre_sub ha
  have hbA : MeetNat M (raw ++ A) b := meetNat_weaken hpre_sub hb
  obtain ⟨hp_pre, _, hsuf⟩ := runListFrom_append.mp hrun
  rw [hpreAB] at hp_pre
  obtain ⟨hpA, hpB⟩ := validPrefix_append.mp hp_pre
  let gs' := A ++ g :: B ++ suf
  have hlen : gs'.length = (pre ++ g :: suf).length := by
    have := congrArg List.length hpreAB
    simp only [gs', List.length_append, List.length_cons] at this ⊢
    omega
  have hrun' : RunListFrom M raw target gs' := by
    have hgs'_eq : gs' = (A ++ [g] ++ B) ++ suf := by simp [gs', List.append_assoc]
    rw [hgs'_eq]
    apply runListFrom_append.mpr
    constructor
    · rw [validPrefix_append]
      refine ⟨validPrefix_append.mpr ⟨hpA, ⟨a, b, haA, hbA, hg⟩, trivial⟩, ?_⟩
      apply validPrefix_weaken_basis (B₁ := raw ++ A) _ hpB
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact List.mem_append_left _ hx
      · exact List.mem_append_right _ (List.mem_append_left _ hx)
    · apply runListFrom_equiv_basis (B₁ := (raw ++ pre) ++ [g]) _ hsuf
      intro x
      rw [hpreAB]
      simp; tauto
  have hlex' : List.Lex (· < ·) gs' (pre ++ g :: suf) := by
    have h1 : gs' = A ++ (g :: B ++ suf) := by simp [gs']
    have h2 : pre ++ g :: suf = A ++ (bt :: (Btail ++ g :: suf)) := by
      rw [hpreAB, hBeq]; simp [List.append_assoc]
    rw [h1, h2]
    exact lex_append_left A _ _ (List.Lex.rel (hbt.symm ▸ hlt))
  exact hlex gs' hlen hrun' hlex'

theorem lexMin_not_eg_sub {n : ℕ} {H F : List (ℕ × ℕ)} {pre suf : List ℕ} {g a b : ℕ}
    (hv : ValidState n H F)
    (hrun : RunListFrom (univYF n F) (rawYF n (univYF n F)) (edgeTTYF n H (univYF n F))
      (pre ++ g :: suf))
    (hmin : ∀ k' < (pre ++ g :: suf).length, ¬ HasRunYF n H F k')
    (hb : MeetNat (univYF n F) (rawYF n (univYF n F) ++ pre) b)
    (hg : g = a ||| b)
    (hsub : (a &&& edgePtsMaskYF H) &&& (b &&& edgePtsMaskYF H) = a &&& edgePtsMaskYF H) :
    False := by
  set M := univYF n F
  set ep := edgePtsMaskYF H
  have hbg : decM M b ⊆ decM M g := by rw [hg, decM_or]; exact Set.subset_union_right
  have heq : decM M b ∩ decM M ep = decM M g ∩ decM M ep := by
    rw [← decM_and, ← decM_and]
    congr 1
    rw [hg]
    apply Nat.eq_of_testBit_eq; intro s
    have h1 := congrArg (fun z => z.testBit s) hsub
    simp only [Nat.testBit_and, Nat.testBit_or] at h1 ⊢
    revert h1
    cases a.testBit s <;> cases b.testBit s <;> cases ep.testBit s <;> decide
  exact lexMin_eliminate_step hv hrun hmin (meetNat_iff.mp hb).2 hbg heq



theorem baseZeroOneEdgesYF {n : ℕ} {H F : List (ℕ × ℕ)} (h : H.length ≤ 1) :
    OrCostLB n H F (H.length - 1) := by
  intro k _; omega

theorem mkBitmask_lt_two_pow (n : ℕ) (p : ℕ → Bool) : mkBitmask n p < 2 ^ n := by
  induction n with
  | zero => simp [mkBitmask]
  | succ k ih =>
    simp only [mkBitmask]
    have hpow : 2 ^ k < 2 ^ (k + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
    have h1 : mkBitmask k p < 2 ^ (k + 1) := lt_trans ih hpow
    split_ifs
    · exact Nat.or_lt_two_pow h1 (oneBit_lt_two_pow (by omega))
    · exact h1

theorem baseTwoEdgesYF {n : ℕ} {H F : List (ℕ × ℕ)}
    (hv : ValidState n H F) (hnd : NoDupEdges H) (hlen : H.length = 2) :
    OrCostLB n H F 1 := by
  intro k hr
  by_contra hlt
  have hk0 : k = 0 := by omega
  subst hk0
  cases hr with
  | done hm =>
    have hM : ∀ s, (univYF n F).testBit s = true → s < 2 ^ n := fun _ => univYF_testBit_lt
    have hm' : Meet (decM (univYF n F) '' { x | x ∈ rawYF n (univYF n F) ++ [] })
        (targetSet n H F) := by
      simpa only [List.append_nil, ← rawSet_eq_image] using hm
    match H, hlen, hv, hnd, hm' with
    | [e₁, e₂], _, hv, hnd, hm' =>
      have hne12 : undirEq e₁ e₂ = false := by
        simp only [NoDupEdges, List.pairwise_cons, List.mem_singleton, forall_eq] at hnd
        exact hnd.1
      let s₁ := (1 <<< e₁.1) ||| (1 <<< e₁.2)
      let s₂ := (1 <<< e₂.1) ||| (1 <<< e₂.2)
      have hs₁M : (univYF n F).testBit s₁ = true := edgePt_mem_univYF hv (by simp)
      have hs₂M : (univYF n F).testBit s₂ = true := edgePt_mem_univYF hv (by simp)
      have hs₁T : (⟨s₁, hs₁M⟩ : Dom (univYF n F)) ∈ targetSet n [e₁, e₂] F :=
        edgePt_mem_edgeTTYF hv (by simp)
      have hs₂T : (⟨s₂, hs₂M⟩ : Dom (univYF n F)) ∈ targetSet n [e₁, e₂] F :=
        edgePt_mem_edgeTTYF hv (by simp)
      rcases meet_decompose_nat hm' with hemp | ⟨rMask, P, hP, hS⟩
      · rw [hemp] at hs₁T; exact hs₁T
      · have hPnil : P = [] := by
          cases P with
          | nil => rfl
          | cons p _ => exfalso; exact List.not_mem_nil (hP p (by simp))
        subst hPnil
        simp only [List.foldl_nil, ttNeedYF_and_mask hM] at hS
        have hs₁R : s₁ &&& rMask = rMask := by
          rw [hS, mem_decM, testBit_ttNeedYF hM, hs₁M, Bool.true_and, beq_iff_eq] at hs₁T
          exact hs₁T
        have hs₂R : s₂ &&& rMask = rMask := by
          rw [hS, mem_decM, testBit_ttNeedYF hM, hs₂M, Bool.true_and, beq_iff_eq] at hs₂T
          exact hs₂T
        have hrSub1 : ∀ w, rMask.testBit w = true → w = e₁.1 ∨ w = e₁.2 := by
          intro w hw
          have := congrArg (fun z => z.testBit w) hs₁R
          rw [Nat.testBit_and, hw, Bool.and_true] at this
          exact (twoBit_testBit e₁.1 e₁.2 w).mp this
        have hrSub2 : ∀ w, rMask.testBit w = true → w = e₂.1 ∨ w = e₂.2 := by
          intro w hw
          have := congrArg (fun z => z.testBit w) hs₂R
          rw [Nat.testBit_and, hw, Bool.and_true] at this
          exact (twoBit_testBit e₂.1 e₂.2 w).mp this
        have hrAtMostOne : ∀ w₁ w₂, rMask.testBit w₁ = true → rMask.testBit w₂ = true → w₁ = w₂ := by
          intro w₁ w₂ hw₁ hw₂
          by_contra hne
          rcases hrSub1 w₁ hw₁ with rfl | rfl <;> rcases hrSub1 w₂ hw₂ with rfl | rfl
          · exact hne rfl
          · rcases hrSub2 _ hw₁ with h1 | h1 <;> rcases hrSub2 _ hw₂ with h2 | h2
            · exact hne (h1.trans h2.symm)
            · simp [undirEq, h1, h2] at hne12
            · simp [undirEq, h1, h2] at hne12
            · exact hne (h1.trans h2.symm)
          · rcases hrSub2 _ hw₁ with h1 | h1 <;> rcases hrSub2 _ hw₂ with h2 | h2
            · exact hne (h1.trans h2.symm)
            · simp [undirEq, h1, h2] at hne12
            · simp [undirEq, h1, h2] at hne12
            · exact hne (h1.trans h2.symm)
          · exact hne rfl
        have hrLt : rMask < 2 ^ n := by
          have hrEq : rMask = mkBitmask n (fun w => rMask.testBit w) := by
            apply Nat.eq_of_testBit_eq; intro w
            rw [testBit_mkBitmask]
            cases hw : rMask.testBit w
            · simp
            · obtain ⟨he1, he2, _⟩ := hv.1 e₁ (by simp)
              have hwn : w < n := by rcases hrSub1 w hw with rfl | rfl <;> assumption
              simp [hwn]
          rw [hrEq]; exact mkBitmask_lt_two_pow n _
        have hrDom : (univYF n F).testBit rMask = true := by
          rw [testBit_univYF, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
          refine ⟨hrLt, Bool.eq_false_iff.mpr fun hf => ?_⟩
          rw [hasEdge_eq_true] at hf
          obtain ⟨f, hfF, h1, h2⟩ := hf
          exact (hv.2.1 f hfF).2.2 (hrAtMostOne f.1 f.2 h1 h2)
        have hrInNeed : (⟨rMask, hrDom⟩ : Dom (univYF n F)) ∈ targetSet n [e₁, e₂] F := by
          rw [hS, mem_decM, testBit_ttNeedYF hM, hrDom, Bool.true_and, Nat.and_self,
            beq_self_eq_true]
        rw [targetSet, mem_decM, testBit_edgeTTYF hM, hrDom, Bool.true_and,
          hasEdge_eq_true] at hrInNeed
        obtain ⟨e, heH, h1, h2⟩ := hrInNeed
        exact (hv.1 e heH).2.2 (hrAtMostOne e.1 e.2 h1 h2)



def delVertEdges (v : ℕ) (E : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  E.filter (fun e => decide (e.1 ≠ v ∧ e.2 ≠ v))

def degH (H : List (ℕ × ℕ)) (v : ℕ) : ℕ :=
  (H.filter (fun e => decide (e.1 = v ∨ e.2 = v))).length

def eraseBit (n v s : ℕ) : ℕ :=
  mkBitmask n (fun w => s.testBit w && decide (w ≠ v))

theorem testBit_eraseBit {n v s w : ℕ} (hs : s < 2 ^ n) :
    (eraseBit n v s).testBit w = (s.testBit w && decide (w ≠ v)) := by
  rw [eraseBit, testBit_mkBitmask]
  by_cases hlt : w < n
  · simp [hlt]
  · have hsf : s.testBit w = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hs (Nat.pow_le_pow_right (by omega) (by omega)))
    simp [hlt, hsf]

theorem validState_delVert {n v : ℕ} {H F : List (ℕ × ℕ)} (hv : ValidState n H F) :
    ValidState n (delVertEdges v H) (delVertEdges v F) := by
  rcases hv with ⟨hH, hF, hdisj⟩
  refine ⟨fun e he => hH e (List.mem_of_mem_filter he),
    fun f hf => hF f (List.mem_of_mem_filter hf),
    fun e he f hf => hdisj e (List.mem_of_mem_filter he) f (List.mem_of_mem_filter hf)⟩

theorem length_delVert_add_degH (H : List (ℕ × ℕ)) (v : ℕ) :
    (delVertEdges v H).length + degH H v = H.length := by
  unfold delVertEdges degH
  induction H with
  | nil => simp
  | cons e rest ih =>
    simp only [List.filter_cons, List.length_cons]
    by_cases h : e.1 = v ∨ e.2 = v
    · have h1 : decide (e.1 ≠ v ∧ e.2 ≠ v) = false := by
        rw [decide_eq_false_iff_not]; omega
      have h2 : decide (e.1 = v ∨ e.2 = v) = true := decide_eq_true h
      simp only [h1, h2, Bool.false_eq_true, ↓reduceIte, List.length_cons]
      omega
    · have h1 : decide (e.1 ≠ v ∧ e.2 ≠ v) = true := by
        rw [decide_eq_true_eq]; omega
      have h2 : decide (e.1 = v ∨ e.2 = v) = false := decide_eq_false h
      simp only [h1, h2, Bool.false_eq_true, ↓reduceIte, List.length_cons]
      omega

theorem paidVertexYF {n : ℕ} {H F : List (ℕ × ℕ)} {v : ℕ}
    (hv : ValidState n H F)
    (hinc : ∃ e ∈ H, e.1 = v ∨ e.2 = v)
    (hsurv : 1 ≤ (delVertEdges v H).length)
    {k : ℕ} (hr : HasRunYF n H F k) :
    ∃ j < k, HasRunYF n (delVertEdges v H) (delVertEdges v F) j := by
  set H' := delVertEdges v H
  set F' := delVertEdges v F
  have hM' : ∀ s, (univYF n F').testBit s = true → s < 2 ^ n := fun _ => univYF_testBit_lt
  have herase_dom : ∀ s : Dom (univYF n F'), (univYF n F).testBit (eraseBit n v s.1) = true := by
    intro s
    have hslt : s.1 < 2 ^ n := hM' s.1 s.2
    rw [testBit_univYF, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
    refine ⟨mkBitmask_lt_two_pow n _, Bool.eq_false_iff.mpr fun hf => ?_⟩
    rw [hasEdge_eq_true] at hf
    obtain ⟨f, hfF, h1, h2⟩ := hf
    rw [testBit_eraseBit hslt, Bool.and_eq_true, decide_eq_true_eq] at h1 h2
    have hfF' : f ∈ F' := List.mem_filter.mpr ⟨hfF, decide_eq_true ⟨h1.2, h2.2⟩⟩
    have hs2 := s.2
    rw [testBit_univYF, Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff] at hs2
    exact hs2.2 (hasEdge_eq_true F' s.1 |>.mpr ⟨f, hfF', h1.1, h2.1⟩)
  let π : Dom (univYF n F') → Dom (univYF n F) := fun s => ⟨eraseBit n v s.1, herase_dom s⟩
  obtain ⟨e₀, he₀H, he₀v⟩ := hinc
  obtain ⟨he₀1, he₀2, he₀ne⟩ := hv.1 e₀ he₀H
  let u : ℕ := if e₀.1 = v then e₀.2 else e₀.1
  have hu_lt : u < n := by simp only [u]; split_ifs <;> omega
  have hp_eq : (1 <<< u) ||| (1 <<< v) = (1 <<< e₀.1) ||| (1 <<< e₀.2) := by
    simp only [u]; split_ifs with h
    · rw [h, Nat.or_comm]
    · have : e₀.2 = v := he₀v.resolve_left h
      rw [this]
  let p_val : ℕ := (1 <<< e₀.1) ||| (1 <<< e₀.2)
  let q_val : ℕ := 1 <<< u
  have hpM : (univYF n F).testBit p_val = true := edgePt_mem_univYF hv he₀H
  have hqM : (univYF n F).testBit q_val = true := by
    rw [testBit_univYF, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
    refine ⟨oneBit_lt_two_pow hu_lt, Bool.eq_false_iff.mpr fun hf => ?_⟩
    rw [hasEdge_eq_true] at hf
    obtain ⟨f, hfF, h1, h2⟩ := hf
    rw [testBit_one_shiftLeft, decide_eq_true_eq] at h1 h2
    exact (hv.2.1 f hfF).2.2 (h1.symm.trans h2)
  let p : Dom (univYF n F) := ⟨p_val, hpM⟩
  let q : Dom (univYF n F) := ⟨q_val, hqM⟩
  have hatoms : ∀ f ∈ rawSet n F, Meet (rawSet n F') (π ⁻¹' f) := by
    rintro f ⟨w, rfl⟩
    by_cases hw : w.1 = v
    · have hemp : π ⁻¹' decM (univYF n F) (ttVarYF n w.1 (univYF n F)) = ∅ := by
        ext s
        simp only [Set.mem_preimage, mem_decM, testBit_ttVarYF (fun _ => univYF_testBit_lt),
          (π s).2, Bool.true_and, Set.mem_empty_iff_false, iff_false]
        change ¬ (eraseBit n v s.1).testBit w.1 = true
        rw [testBit_eraseBit (hM' s.1 s.2), hw]
        simp
      rw [hemp]; exact Meet.bot
    · have heq : π ⁻¹' decM (univYF n F) (ttVarYF n w.1 (univYF n F)) =
          decM (univYF n F') (ttVarYF n w.1 (univYF n F')) := by
        ext s
        simp only [Set.mem_preimage, mem_decM, testBit_ttVarYF (fun _ => univYF_testBit_lt),
          (π s).2, s.2, Bool.true_and]
        change (eraseBit n v s.1).testBit w.1 = true ↔ s.1.testBit w.1 = true
        rw [testBit_eraseBit (hM' s.1 s.2), decide_eq_true hw, Bool.and_true]
      rw [heq]; exact Meet.atom ⟨w, rfl⟩
  have hgood : ∀ f ∈ rawSet n F, Good π p q f := by
    rintro f ⟨w, rfl⟩
    by_cases hw : w.1 = v
    · right
      ext s
      simp only [Set.mem_preimage, mem_decM, testBit_ttVarYF (fun _ => univYF_testBit_lt),
        (π s).2, Bool.true_and, Set.mem_empty_iff_false, iff_false]
      change ¬ (eraseBit n v s.1).testBit w.1 = true
      rw [testBit_eraseBit (hM' s.1 s.2), hw]
      simp
    · left
      simp only [mem_decM, testBit_ttVarYF (fun _ => univYF_testBit_lt), p.2, q.2, Bool.true_and]
      change p_val.testBit w.1 = true ↔ q_val.testBit w.1 = true
      dsimp only [p_val, q_val]
      rw [← hp_eq, twoBit_testBit, testBit_one_shiftLeft, decide_eq_true_eq]
      constructor
      · rintro (h | h)
        · exact h.symm
        · exact (hw h).elim
      · intro h; exact Or.inl h.symm
  have hpreTarget : π ⁻¹' targetSet n H F = targetSet n H' F' := by
    ext s
    simp only [Set.mem_preimage, targetSet, mem_decM,
      testBit_edgeTTYF (fun _ => univYF_testBit_lt), (π s).2, s.2, Bool.true_and, hasEdge_eq_true]
    constructor
    · rintro ⟨e, heH, h1, h2⟩
      change (eraseBit n v s.1).testBit e.1 = true at h1
      change (eraseBit n v s.1).testBit e.2 = true at h2
      rw [testBit_eraseBit (hM' s.1 s.2), Bool.and_eq_true, decide_eq_true_eq] at h1 h2
      exact ⟨e, List.mem_filter.mpr ⟨heH, decide_eq_true ⟨h1.2, h2.2⟩⟩, h1.1, h2.1⟩
    · rintro ⟨e, heH', h1, h2⟩
      obtain ⟨heH, hne⟩ := List.mem_filter.mp heH'
      rw [decide_eq_true_eq] at hne
      refine ⟨e, heH, ?_, ?_⟩
      · change (eraseBit n v s.1).testBit e.1 = true
        rw [testBit_eraseBit (hM' s.1 s.2), h1, decide_eq_true hne.1]; rfl
      · change (eraseBit n v s.1).testBit e.2 = true
        rw [testBit_eraseBit (hM' s.1 s.2), h2, decide_eq_true hne.2]; rfl
  have hbad : ¬ Good π p q (targetSet n H F) := by
    rintro (hiff | hemp)
    · have hpT : p ∈ targetSet n H F := edgePt_mem_edgeTTYF hv he₀H
      have hqT : q ∈ targetSet n H F := hiff.mp hpT
      rw [targetSet, mem_decM, testBit_edgeTTYF (fun _ => univYF_testBit_lt), q.2, Bool.true_and,
        hasEdge_eq_true] at hqT
      obtain ⟨e, heH, h1, h2⟩ := hqT
      change (1 <<< u).testBit e.1 = true at h1
      change (1 <<< u).testBit e.2 = true at h2
      rw [testBit_one_shiftLeft, decide_eq_true_eq] at h1 h2
      exact (hv.1 e heH).2.2 (h1.symm.trans h2)
    · rw [hpreTarget] at hemp
      have hH'ne : H' ≠ [] := by intro h; simp [h] at hsurv
      obtain ⟨e₁, _, he₁eq⟩ := List.exists_cons_of_ne_nil hH'ne
      have he₁mem : e₁ ∈ H' := by rw [he₁eq]; simp
      have hv' : ValidState n H' F' := validState_delVert hv
      have hs₁M' : (univYF n F').testBit ((1 <<< e₁.1) ||| (1 <<< e₁.2)) = true :=
        edgePt_mem_univYF hv' he₁mem
      have hs₁T' : (⟨(1 <<< e₁.1) ||| (1 <<< e₁.2), hs₁M'⟩ : Dom (univYF n F')) ∈
          targetSet n H' F' :=
        edgePt_mem_edgeTTYF hv' he₁mem
      rw [hemp] at hs₁T'
      exact hs₁T'
  obtain ⟨j, hj, hr'⟩ := paidMap π p q hatoms hgood hr hbad
  rw [hpreTarget] at hr'
  exact ⟨j, hj, hr'⟩

theorem paidLeafYF {n : ℕ} {H F : List (ℕ × ℕ)} {v : ℕ}
    (hv : ValidState n H F) (hdeg : degH H v = 1) (hlen : 2 ≤ H.length)
    (hlb : OrCostLB n (delVertEdges v H) (delVertEdges v F) ((delVertEdges v H).length - 1)) :
    OrCostLB n H F (H.length - 1) := by
  have hlen' : (delVertEdges v H).length + 1 = H.length := by
    have := length_delVert_add_degH H v; omega
  have hinc : ∃ e ∈ H, e.1 = v ∨ e.2 = v := by
    unfold degH at hdeg
    have hne : H.filter (fun e => decide (e.1 = v ∨ e.2 = v)) ≠ [] := by
      intro h; rw [h] at hdeg; simp at hdeg
    obtain ⟨e, _, heq⟩ := List.exists_cons_of_ne_nil hne
    have hmem : e ∈ H.filter (fun e => decide (e.1 = v ∨ e.2 = v)) := by rw [heq]; simp
    obtain ⟨heH, hv'⟩ := List.mem_filter.mp hmem
    exact ⟨e, heH, decide_eq_true_eq.mp hv'⟩
  intro k hr
  obtain ⟨j, hj, hr'⟩ := paidVertexYF hv hinc (by omega) hr
  have h1 := hlb j hr'
  omega



def mapSubLoop (f : List ℕ) (t i acc : ℕ) : ℕ :=
  match f with
  | [] => acc
  | u :: rest =>
    let acc' := match t.testBit i with
      | true => Nat.lor acc (1 <<< u)
      | false => acc
    mapSubLoop rest t (i + 1) acc'

def mapSub (f : List ℕ) (t : ℕ) : ℕ := mapSubLoop f t 0 0

theorem mapSub_testBit (f : List ℕ) (t w : ℕ) :
    (mapSub f t).testBit w = true ↔
      ∃ (i : ℕ) (hi : i < f.length), f[i] = w ∧ t.testBit i = true := by
  have heq : ∀ (l : List ℕ) (i acc : ℕ), mapSubLoop l t i acc = applyPermLoop l t i acc := by
    intro l
    induction l with
    | nil => intro _ _; rfl
    | cons u rest ih =>
      intro i acc
      simp only [mapSubLoop, applyPermLoop]
      exact ih (i + 1) _
  change (mapSubLoop f t 0 0).testBit w = true ↔ _
  rw [heq f 0 0]
  exact applyPerm_testBit f t w

def validEmbed (n : ℕ) (H F : List (ℕ × ℕ)) (n' : ℕ) (H' F' : List (ℕ × ℕ)) (f : List ℕ) : Bool :=
  decide (f.length = n') &&
  decide f.Nodup &&
  f.all (fun x => decide (x < n)) &&
  H.all (fun e => H'.any (fun e' => decide (e'.1 < n' ∧ e'.2 < n') &&
    undirEq e (f.getD e'.1 0, f.getD e'.2 0))) &&
  H'.all (fun e' => decide (e'.1 < n' ∧ e'.2 < n') &&
    H.any (fun e => undirEq e (f.getD e'.1 0, f.getD e'.2 0))) &&
  F.all (fun e => (List.range n').all (fun i => (List.range n').all (fun j =>
    !decide (f.getD i 0 = e.1 ∧ f.getD j 0 = e.2) ||
    F'.any (fun f' => undirEq f' (i, j)))))

theorem undirEq_true_iff (e₁ e₂ : ℕ × ℕ) :
    undirEq e₁ e₂ = true ↔ (e₁.1 = e₂.1 ∧ e₁.2 = e₂.2) ∨ (e₁.1 = e₂.2 ∧ e₁.2 = e₂.1) := by
  simp [undirEq]

theorem mapSub_lt_two_pow {n : ℕ} {f : List ℕ} (hf : ∀ x ∈ f, x < n) (t : ℕ) :
    mapSub f t < 2 ^ n := by
  have heq : mapSub f t = mkBitmask n (fun w => (mapSub f t).testBit w) := by
    apply Nat.eq_of_testBit_eq; intro w
    rw [testBit_mkBitmask]
    cases hw : (mapSub f t).testBit w
    · simp
    · obtain ⟨i, hi, hget, _⟩ := (mapSub_testBit f t w).mp hw
      have hwn : w < n := hget ▸ hf f[i] (List.getElem_mem hi)
      simp [hwn]
  rw [heq]; exact mkBitmask_lt_two_pow n _

theorem embedYF_sound {n n' : ℕ} {H F H' F' : List (ℕ × ℕ)} {f : List ℕ}
    (hemb : validEmbed n H F n' H' F' f = true) :
    ∀ k, HasRunYF n H F k → HasRunYF n' H' F' k := by
  unfold validEmbed at hemb
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.any_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, List.mem_range] at hemb
  obtain ⟨⟨⟨⟨⟨hlen, hnd⟩, hflt⟩, hHdir⟩, hH'dir⟩, hFdir⟩ := hemb
  have hdom : ∀ t : Dom (univYF n' F'), (univYF n F).testBit (mapSub f t.1) = true := by
    intro t
    rw [testBit_univYF, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
    refine ⟨mapSub_lt_two_pow hflt t.1, Bool.eq_false_iff.mpr fun hf => ?_⟩
    rw [hasEdge_eq_true] at hf
    obtain ⟨e, heF, h1, h2⟩ := hf
    obtain ⟨i, hi, hfi, hti⟩ := (mapSub_testBit f t.1 e.1).mp h1
    obtain ⟨j, hj, hfj, htj⟩ := (mapSub_testBit f t.1 e.2).mp h2
    have hi' : i < n' := hlen ▸ hi
    have hj' : j < n' := hlen ▸ hj
    have hgi : f.getD i 0 = e.1 := by rw [List.getD_eq_getElem _ _ hi]; exact hfi
    have hgj : f.getD j 0 = e.2 := by rw [List.getD_eq_getElem _ _ hj]; exact hfj
    rcases hFdir e heF i hi' j hj' with hno | ⟨f', hf'F', hue⟩
    · exact hno ⟨hgi, hgj⟩
    · have ht2 := t.2
      rw [testBit_univYF, Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff] at ht2
      rw [undirEq_true_iff] at hue
      apply ht2.2
      rw [hasEdge_eq_true]
      rcases hue with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
      · exact ⟨f', hf'F', h1'.symm ▸ hti, h2'.symm ▸ htj⟩
      · exact ⟨f', hf'F', h1'.symm ▸ htj, h2'.symm ▸ hti⟩
  let π : Dom (univYF n' F') → Dom (univYF n F) := fun t => ⟨mapSub f t.1, hdom t⟩
  have hatoms : ∀ S ∈ rawSet n F, Meet (rawSet n' F') (π ⁻¹' S) := by
    rintro S ⟨v, rfl⟩
    by_cases hv : ∃ (i : ℕ) (hi : i < f.length), f[i] = v.1
    · obtain ⟨i, hi, hfi⟩ := hv
      have hi' : i < n' := hlen ▸ hi
      have heq : π ⁻¹' decM (univYF n F) (ttVarYF n v.1 (univYF n F)) =
          decM (univYF n' F') (ttVarYF n' i (univYF n' F')) := by
        ext t
        simp only [Set.mem_preimage, mem_decM, testBit_ttVarYF (fun _ => univYF_testBit_lt),
          (π t).2, t.2, Bool.true_and]
        change (mapSub f t.1).testBit v.1 = true ↔ t.1.testBit i = true
        rw [mapSub_testBit]
        constructor
        · rintro ⟨j, hj, hfj, htj⟩
          have hij : j = i := (List.Nodup.getElem_inj_iff hnd).mp (hfj.trans hfi.symm)
          exact hij ▸ htj
        · intro hti; exact ⟨i, hi, hfi, hti⟩
      rw [heq]; exact Meet.atom ⟨⟨i, hi'⟩, rfl⟩
    · have hemp : π ⁻¹' decM (univYF n F) (ttVarYF n v.1 (univYF n F)) = ∅ := by
        ext t
        simp only [Set.mem_preimage, mem_decM, testBit_ttVarYF (fun _ => univYF_testBit_lt),
          (π t).2, Bool.true_and, Set.mem_empty_iff_false, iff_false]
        change ¬ (mapSub f t.1).testBit v.1 = true
        rw [mapSub_testBit]
        rintro ⟨i, hi, hfi, _⟩
        exact hv ⟨i, hi, hfi⟩
      rw [hemp]; exact Meet.bot
  have htarget : π ⁻¹' targetSet n H F = targetSet n' H' F' := by
    ext t
    simp only [Set.mem_preimage, targetSet, mem_decM,
      testBit_edgeTTYF (fun _ => univYF_testBit_lt), (π t).2, t.2, Bool.true_and, hasEdge_eq_true]
    constructor
    · rintro ⟨e, heH, h1, h2⟩
      change (mapSub f t.1).testBit e.1 = true at h1
      change (mapSub f t.1).testBit e.2 = true at h2
      obtain ⟨i, hi, hfi, hti⟩ := (mapSub_testBit f t.1 e.1).mp h1
      obtain ⟨j, hj, hfj, htj⟩ := (mapSub_testBit f t.1 e.2).mp h2
      obtain ⟨e', he'H', ⟨he'1, he'2⟩, hue⟩ := hHdir e heH
      have h1lt : e'.1 < f.length := hlen.symm ▸ he'1
      have h2lt : e'.2 < f.length := hlen.symm ▸ he'2
      rw [List.getD_eq_getElem _ _ h1lt, List.getD_eq_getElem _ _ h2lt, undirEq_true_iff] at hue
      rcases hue with ⟨hu1, hu2⟩ | ⟨hu1, hu2⟩
      · have hi1 : i = e'.1 := (List.Nodup.getElem_inj_iff hnd).mp (hfi.trans hu1)
        have hj2 : j = e'.2 := (List.Nodup.getElem_inj_iff hnd).mp (hfj.trans hu2)
        exact ⟨e', he'H', hi1 ▸ hti, hj2 ▸ htj⟩
      · have hi2 : i = e'.2 := (List.Nodup.getElem_inj_iff hnd).mp (hfi.trans hu1)
        have hj1 : j = e'.1 := (List.Nodup.getElem_inj_iff hnd).mp (hfj.trans hu2)
        exact ⟨e', he'H', hj1 ▸ htj, hi2 ▸ hti⟩
    · rintro ⟨e', he'H', h1, h2⟩
      obtain ⟨⟨he'1, he'2⟩, e, heH, hue⟩ := hH'dir e' he'H'
      have h1lt : e'.1 < f.length := hlen.symm ▸ he'1
      have h2lt : e'.2 < f.length := hlen.symm ▸ he'2
      rw [List.getD_eq_getElem _ _ h1lt, List.getD_eq_getElem _ _ h2lt, undirEq_true_iff] at hue
      refine ⟨e, heH, ?_, ?_⟩
      · change (mapSub f t.1).testBit e.1 = true
        rw [mapSub_testBit]
        rcases hue with ⟨hu1, _⟩ | ⟨hu1, _⟩
        · exact ⟨e'.1, h1lt, hu1.symm, h1⟩
        · exact ⟨e'.2, h2lt, hu1.symm, h2⟩
      · change (mapSub f t.1).testBit e.2 = true
        rw [mapSub_testBit]
        rcases hue with ⟨_, hu2⟩ | ⟨_, hu2⟩
        · exact ⟨e'.2, h2lt, hu2.symm, h2⟩
        · exact ⟨e'.1, h1lt, hu2.symm, h1⟩
  intro k hr
  have hr' := freeMap π hatoms hr
  rwa [htarget] at hr'

def validPeelEmbed (n : ℕ) (H F : List (ℕ × ℕ)) :
    List ℕ → ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → List ℕ → Bool
  | [], n', H', F', f => decide (H.length = H'.length) && validEmbed n H F n' H' F' f
  | v :: rest, n', H', F', f =>
    decide (degH H v = 1 ∧ 2 ≤ H.length) &&
    validPeelEmbed n (delVertEdges v H) (delVertEdges v F) rest n' H' F' f

theorem validPeelEmbed_sound {n : ℕ} {H F : List (ℕ × ℕ)} {peels : List ℕ}
    {n' : ℕ} {H' F' : List (ℕ × ℕ)} {f : List ℕ}
    (hv : ValidState n H F)
    (hok : validPeelEmbed n H F peels n' H' F' f = true)
    (hlb : OrCostLB n' H' F' (H'.length - 1)) :
    OrCostLB n H F (H.length - 1) := by
  induction peels generalizing H F with
  | nil =>
    simp only [validPeelEmbed, Bool.and_eq_true, decide_eq_true_eq] at hok
    rw [hok.1]
    intro k hr
    exact hlb k (embedYF_sound hok.2 k hr)
  | cons v rest ih =>
    simp only [validPeelEmbed, Bool.and_eq_true, decide_eq_true_eq] at hok
    exact paidLeafYF hv hok.1.1 hok.1.2 (ih (validState_delVert hv) hok.2)



def probeOkGate (mc pm h : ℕ) : Bool :=
  let x := Nat.land h pm
  match Nat.beq x 0 with
  | true => true
  | false =>
    match Nat.beq x pm with
    | true => true
    | false => Nat.beq (Nat.land h mc) 0

def evalCutStep (mc : ℕ) (rc : List ℕ) (act : List ℕ) : List ℕ × List ℕ × ℕ :=
  let rec go : List ℕ → List ℕ → List ℕ → ℕ → List ℕ × List ℕ × ℕ
    | [], sb, actRev, sv => (sb, actRev.reverse, sv)
    | g :: rest, sb, actRev, sv =>
      let rg := Nat.land g mc
      match isMeet mc sb rg with
      | true => go rest sb actRev (sv + 1)
      | false => go rest (rg :: sb) (rg :: actRev) sv
  go act rc [] 0

theorem evalCutStep_go_inv {M_prev mc : ℕ} (hmc : mc &&& M_prev = mc)
    {raw_prev rc : List ℕ}
    (hraw : ∀ r ∈ raw_prev, r &&& mc = 0 ∨ r &&& mc ∈ rc) :
    ∀ (rest sb actRev : List ℕ) (sv : ℕ) (done : List ℕ),
      (∀ x ∈ sb, x ∈ rc ++ actRev.reverse) →
      (∀ x ∈ rc ++ actRev.reverse, x ∈ sb) →
      ValidPrefix mc rc actRev.reverse →
      (∀ h ∈ done, MeetNat mc sb (h &&& mc)) →
      ValidPrefix M_prev (raw_prev ++ done) rest →
      let res := evalCutStep.go mc rest sb actRev sv
      res.2.1.length + res.2.2 = actRev.length + sv + rest.length ∧
      ValidPrefix mc rc res.2.1 ∧
      (∀ x ∈ res.1, x ∈ rc ++ res.2.1) ∧
      (∀ x ∈ rc ++ res.2.1, x ∈ res.1) ∧
      (∀ h ∈ done ++ rest, MeetNat mc res.1 (h &&& mc)) := by
  intro rest
  induction rest with
  | nil =>
    intro sb actRev sv done hsb1 hsb2 hvp hdone _
    simp only [evalCutStep.go, List.length_reverse, List.length_nil, add_zero, List.append_nil]
    exact ⟨trivial, hvp, hsb1, hsb2, hdone⟩
  | cons g tail ih =>
    intro sb actRev sv done hsb1 hsb2 hvp hdone hrest_vp
    rcases hrest_vp with ⟨⟨a, b, ha, hb, hgab⟩, htail_vp⟩
    have hrgM : (g &&& mc) &&& mc = g &&& mc := by
      apply Nat.eq_of_testBit_eq; intro s; simp [Nat.testBit_and]
    have hmap_prev : ∀ x ∈ raw_prev ++ done, MeetNat mc sb (x &&& mc) := by
      intro x hx
      have hxM : (x &&& mc) &&& mc = x &&& mc := by
        apply Nat.eq_of_testBit_eq; intro s; simp [Nat.testBit_and]
      rcases List.mem_append.mp hx with hx | hx
      · rcases hraw x hx with h0 | hmem
        · rw [h0]; exact ⟨by simp, by simp [isMeet]⟩
        · exact meetNat_iff.mpr ⟨hxM, Meet.atom ⟨x &&& mc, hsb2 _ (List.mem_append_left _ hmem), rfl⟩⟩
      · exact hdone x hx
    let ι : Dom mc → Dom M_prev := fun s => ⟨s.1, sub_mask_testBit hmc s.2⟩
    have hι_meet : ∀ {t : ℕ}, MeetNat M_prev (raw_prev ++ done) t → MeetNat mc sb (t &&& mc) := by
      intro t ht
      have htM : (t &&& mc) &&& mc = t &&& mc := by
        apply Nat.eq_of_testBit_eq; intro s; simp [Nat.testBit_and]
      refine meetNat_iff.mpr ⟨htM, ?_⟩
      have hpre : ι ⁻¹' decM M_prev t = decM mc (t &&& mc) := by
        ext s; simp [ι, decM, Nat.testBit_and, s.2]
      rw [← hpre]
      apply mapMeet ι _ (meetNat_iff.mp ht).2
      rintro S ⟨x, hx, rfl⟩
      have hpx : ι ⁻¹' decM M_prev x = decM mc (x &&& mc) := by
        ext s; simp [ι, decM, Nat.testBit_and, s.2]
      rw [hpx]
      exact (meetNat_iff.mp (hmap_prev x hx)).2
    have ha_c : MeetNat mc sb (a &&& mc) := hι_meet ha
    have hb_c : MeetNat mc sb (b &&& mc) := hι_meet hb
    have hgab_c : g &&& mc = (a &&& mc) ||| (b &&& mc) := by
      rw [hgab]
      apply Nat.eq_of_testBit_eq; intro s
      simp only [Nat.testBit_and, Nat.testBit_or]
      cases a.testBit s <;> cases b.testBit s <;> cases mc.testBit s <;> decide
    have htail_vp' : ValidPrefix M_prev (raw_prev ++ (done ++ [g])) tail := by
      simpa only [List.append_assoc] using htail_vp
    simp only [evalCutStep.go, land_eq]
    cases hm : isMeet mc sb (g &&& mc)
    · -- not a meet: push `rg = g &&& mc` to `sb` and `actRev`
      have hvp' : ValidPrefix mc rc ((g &&& mc) :: actRev).reverse := by
        rw [List.reverse_cons, validPrefix_append]
        refine ⟨hvp, ⟨a &&& mc, b &&& mc,
          meetNat_weaken hsb1 ha_c, meetNat_weaken hsb1 hb_c, hgab_c⟩, trivial⟩
      have h1 := ih ((g &&& mc) :: sb) ((g &&& mc) :: actRev) sv (done ++ [g])
        (fun x hx => by
          rw [List.reverse_cons]
          rcases List.mem_cons.mp hx with rfl | hx
          · simp
          · have := hsb1 x hx; simp only [List.mem_append] at this ⊢; tauto)
        (fun x hx => by
          rw [List.reverse_cons] at hx
          rcases List.mem_append.mp hx with hx | hx
          · exact List.mem_cons_of_mem _ (hsb2 x (List.mem_append_left _ hx))
          · rcases List.mem_append.mp hx with hx | hx
            · exact List.mem_cons_of_mem _ (hsb2 x (List.mem_append_right _ hx))
            · rw [List.mem_singleton.mp hx]; exact List.mem_cons_self)
        hvp'
        (fun h hh => by
          rcases List.mem_append.mp hh with hh | hh
          · exact meetNat_weaken (fun x hx => List.mem_cons_of_mem _ hx) (hdone h hh)
          · rw [List.mem_singleton.mp hh]
            exact meetNat_iff.mpr ⟨hrgM, Meet.atom ⟨g &&& mc, List.mem_cons_self, rfl⟩⟩)
        htail_vp'
      simpa only [List.length_cons, List.append_assoc, List.singleton_append, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using h1
    · -- is a meet: increment `sv`
      have h1 := ih sb actRev (sv + 1) (done ++ [g]) hsb1 hsb2 hvp
        (fun h hh => by
          rcases List.mem_append.mp hh with hh | hh
          · exact hdone h hh
          · rw [List.mem_singleton.mp hh]; exact ⟨hrgM, hm⟩)
        htail_vp'
      simpa only [List.length_cons, List.append_assoc, List.singleton_append, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using h1

theorem probeOkGate_sound {M_prev mc pm p q : ℕ}
    (hmc : mc &&& M_prev = mc)
    (hpM : M_prev.testBit p = true) (hqM : M_prev.testBit q = true)
    (hp_pm : pm.testBit p = true) (hq_pm : pm.testBit q = true)
    {h : ℕ} (hok : probeOkGate mc pm h = true) :
    Good (fun s : Dom mc => (⟨s.1, sub_mask_testBit hmc s.2⟩ : Dom M_prev))
      ⟨p, hpM⟩ ⟨q, hqM⟩ (decM M_prev h) := by
  unfold probeOkGate at hok
  dsimp only at hok
  cases h0 : Nat.beq (Nat.land h pm) 0
  · rw [h0] at hok
    cases h1 : Nat.beq (Nat.land h pm) pm
    · rw [h1] at hok
      have hmc0 : h &&& mc = 0 := by simpa [land_eq] using Nat.eq_of_beq_eq_true hok
      right
      ext s
      simp only [Set.mem_preimage, decM, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro hs
      have := congrArg (fun z => z.testBit s.1) hmc0
      rw [Nat.testBit_and, hs, s.2] at this
      simp at this
    · have hpm : h &&& pm = pm := by simpa [land_eq] using Nat.eq_of_beq_eq_true h1
      left
      have hp : h.testBit p = true := by
        have := congrArg (fun z => z.testBit p) hpm
        rw [Nat.testBit_and, hp_pm, Bool.and_true] at this; exact this
      have hq : h.testBit q = true := by
        have := congrArg (fun z => z.testBit q) hpm
        rw [Nat.testBit_and, hq_pm, Bool.and_true] at this; exact this
      simp [decM, hp, hq]
  · have hpm0 : h &&& pm = 0 := by simpa [land_eq] using Nat.eq_of_beq_eq_true h0
    left
    have hp : h.testBit p = false := by
      have := congrArg (fun z => z.testBit p) hpm0
      rw [Nat.testBit_and, hp_pm, Bool.and_true, Nat.zero_testBit] at this; exact this
    have hq : h.testBit q = false := by
      have := congrArg (fun z => z.testBit q) hpm0
      rw [Nat.testBit_and, hq_pm, Bool.and_true, Nat.zero_testBit] at this; exact this
    simp [decM, hp, hq]

theorem probeMask_exists_pq {M_prev edgeTT pm : ℕ}
    (hpmM : pm &&& M_prev = pm)
    (hne0 : pm &&& edgeTT ≠ 0)
    (hneP : pm &&& edgeTT ≠ pm) :
    ∃ p q : ℕ, M_prev.testBit p = true ∧ M_prev.testBit q = true ∧
      pm.testBit p = true ∧ pm.testBit q = true ∧
      edgeTT.testBit p = true ∧ edgeTT.testBit q = false := by
  have hexP : ∃ p, (pm &&& edgeTT).testBit p = true := by
    by_contra hall; push Not at hall
    apply hne0; apply Nat.eq_of_testBit_eq; intro s
    simp only [Nat.zero_testBit]; exact Bool.eq_false_iff.mpr (hall s)
  have hexQ : ∃ q, (pm &&& edgeTT).testBit q ≠ pm.testBit q := by
    by_contra hall; push Not at hall
    exact hneP (Nat.eq_of_testBit_eq hall)
  obtain ⟨p, hp⟩ := hexP
  rw [Nat.testBit_and, Bool.and_eq_true] at hp
  obtain ⟨q, hq⟩ := hexQ
  rw [Nat.testBit_and] at hq
  have hqp : pm.testBit q = true := by
    cases h : pm.testBit q
    · simp [h] at hq
    · rfl
  have hqe : edgeTT.testBit q = false := by
    cases h : edgeTT.testBit q
    · rfl
    · simp [hqp, h] at hq
  exact ⟨p, q, sub_mask_testBit hpmM hp.1, sub_mask_testBit hpmM hqp, hp.1, hqp, hp.2, hqe⟩


theorem cutStep_sound {M_prev mc edgeTT : ℕ} {raw_prev rc act_prev pv : List ℕ} {sufLen : ℕ}
    (hmc : mc &&& M_prev = mc)
    (hraw : ∀ r ∈ raw_prev, r &&& mc = 0 ∨ r &&& mc ∈ rc)
    (hvp_prev : ValidPrefix M_prev raw_prev act_prev)
    (hrun_prev : Run (decM M_prev '' { x | x ∈ raw_prev ++ act_prev }) sufLen (decM M_prev edgeTT))
    (hpv_valid : ∀ pm ∈ pv, pm &&& M_prev = pm ∧ pm &&& edgeTT ≠ 0 ∧ pm &&& edgeTT ≠ pm ∧
      edgeTT &&& mc ≠ 0 ∧ ∀ r ∈ raw_prev, probeOkGate mc pm r = true) :
    let res := evalCutStep mc rc act_prev
    let bonus := if pv.any (fun pm => act_prev.all (fun h => probeOkGate mc pm h)) then 1 else 0
    ValidPrefix mc rc res.2.1 ∧
    ∃ sufLen' : ℕ,
      res.2.1.length + sufLen' + res.2.2 + bonus ≤ act_prev.length + sufLen ∧
      Run (decM mc '' { x | x ∈ rc ++ res.2.1 }) sufLen' (decM mc edgeTT) := by
  have hinv := evalCutStep_go_inv hmc hraw act_prev rc [] 0 []
    (fun x hx => by simpa using hx)
    (fun x hx => by simpa using hx)
    trivial
    (fun _ h => by simp at h)
    (by simpa using hvp_prev)
  simp only [List.length_nil, zero_add, List.nil_append] at hinv
  obtain ⟨hlen, hvp_next, hsb1, hsb2, hall_meet⟩ := hinv
  change (evalCutStep mc rc act_prev).2.1.length + (evalCutStep mc rc act_prev).2.2 =
    act_prev.length at hlen
  let ι : Dom mc → Dom M_prev := fun s => ⟨s.1, sub_mask_testBit hmc s.2⟩
  have htarget : ι ⁻¹' decM M_prev edgeTT = decM mc edgeTT := by
    ext s; simp [ι, decM]
  have hatoms : ∀ S ∈ decM M_prev '' { x | x ∈ raw_prev ++ act_prev },
      Meet (decM mc '' { x | x ∈ rc ++ (evalCutStep mc rc act_prev).2.1 }) (ι ⁻¹' S) := by
    rintro S ⟨x, hx, rfl⟩
    have hpre : ι ⁻¹' decM M_prev x = decM mc (x &&& mc) := by
      ext s; simp [ι, decM, Nat.testBit_and, s.2]
    rw [hpre]
    rcases List.mem_append.mp hx with hx | hx
    · rcases hraw x hx with h0 | hmem
      · rw [h0, decM_zero]; exact Meet.bot
      · exact Meet.atom ⟨x &&& mc, List.mem_append_left _ hmem, rfl⟩
    · exact weaken (Set.image_mono (fun y hy => hsb1 y hy)) (meetNat_iff.mp (hall_meet x hx)).2
  dsimp only
  refine ⟨hvp_next, ?_⟩
  split_ifs with hprobe
  · rw [List.any_eq_true] at hprobe
    obtain ⟨pm, hpm_mem, hact_ok⟩ := hprobe
    rw [List.all_eq_true] at hact_ok
    obtain ⟨hpmM, hne0, hneP, hedgemc, hraw_ok⟩ := hpv_valid pm hpm_mem
    obtain ⟨p, q, hpM, hqM, hppm, hqpm, hpe, hqe⟩ := probeMask_exists_pq hpmM hne0 hneP
    have hgood : ∀ S ∈ decM M_prev '' { x | x ∈ raw_prev ++ act_prev },
        Good ι ⟨p, hpM⟩ ⟨q, hqM⟩ S := by
      rintro S ⟨x, hx, rfl⟩
      rcases List.mem_append.mp hx with hx | hx
      · exact probeOkGate_sound hmc hpM hqM hppm hqpm (hraw_ok x hx)
      · exact probeOkGate_sound hmc hpM hqM hppm hqpm (hact_ok x hx)
    have hbad : ¬ Good ι ⟨p, hpM⟩ ⟨q, hqM⟩ (decM M_prev edgeTT) := by
      rintro (hiff | hemp)
      · have : edgeTT.testBit q = true := hiff.mp hpe
        simp [hqe] at this
      · rw [htarget] at hemp
        have hex : ∃ s, (edgeTT &&& mc).testBit s = true := by
          by_contra hall; push Not at hall
          apply hedgemc; apply Nat.eq_of_testBit_eq; intro s
          simp only [Nat.zero_testBit]; exact Bool.eq_false_iff.mpr (hall s)
        obtain ⟨s, hs⟩ := hex
        rw [Nat.testBit_and, Bool.and_eq_true] at hs
        have : (⟨s, hs.2⟩ : Dom mc) ∈ decM mc edgeTT := hs.1
        rw [hemp] at this; exact this
    obtain ⟨j, hj, hr'⟩ := paidMap ι ⟨p, hpM⟩ ⟨q, hqM⟩ hatoms hgood hrun_prev hbad
    rw [htarget] at hr'
    exact ⟨j, by omega, hr'⟩
  · have hr' := freeMap ι hatoms hrun_prev
    rw [htarget] at hr'
    exact ⟨sufLen, by omega, hr'⟩

theorem nat_beq_eq_true_iff (a b : ℕ) : Nat.beq a b = true ↔ a = b :=
  ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl a⟩

theorem nat_blt_eq_true {a b : ℕ} (h : Nat.blt a b = true) : a < b :=
  Nat.le_of_ble_eq_true h

theorem nat_sub_eq (a b : ℕ) : Nat.sub a b = a - b := rfl
theorem nat_div_eq (a b : ℕ) : Nat.div a b = a / b := rfl

theorem nat_beq_eq_false_iff (a b : ℕ) : Nat.beq a b = false ↔ a ≠ b := by
  cases h : Nat.beq a b
  · exact ⟨fun _ heq => by subst heq; simp at h, fun _ => rfl⟩
  · exact ⟨fun hc => (Bool.false_ne_true hc.symm).elim, fun hne => (hne (Nat.eq_of_beq_eq_true h)).elim⟩



structure CutStepData where
  mc : ℕ
  rc : List ℕ
  pv : List ℕ

def ValidCutStep (M_prev edgeTT : ℕ) (raw_prev : List ℕ) (st : CutStepData) : Prop :=
  st.mc &&& M_prev = st.mc ∧
  (∀ r ∈ raw_prev, r &&& st.mc = 0 ∨ r &&& st.mc ∈ st.rc) ∧
  (∀ pm ∈ st.pv, pm &&& M_prev = pm ∧ pm &&& edgeTT ≠ 0 ∧ pm &&& edgeTT ≠ pm ∧
    edgeTT &&& st.mc ≠ 0 ∧ ∀ r ∈ raw_prev, probeOkGate st.mc pm r = true)

def evalCutChain (steps : List CutStepData) (act : List ℕ) : ℕ :=
  match steps with
  | [] => 0
  | st :: rest =>
    let res := evalCutStep st.mc st.rc act
    let bonus := if st.pv.any (fun pm => act.all (fun h => probeOkGate st.mc pm h)) then 1 else 0
    res.2.2 + bonus + evalCutChain rest res.2.1

def ValidCutChain (M edgeTT : ℕ) (raw : List ℕ) : List CutStepData → ℕ → List ℕ → Prop
  | [], M_end, raw_end => M = M_end ∧ raw = raw_end
  | st :: rest, M_end, raw_end =>
    ValidCutStep M edgeTT raw st ∧ ValidCutChain st.mc edgeTT st.rc rest M_end raw_end

theorem cutChain_sound {M edgeTT M_end : ℕ} {raw raw_end : List ℕ}
    (steps : List CutStepData)
    (hvalid : ValidCutChain M edgeTT raw steps M_end raw_end)
    {act : List ℕ} {sufLen : ℕ}
    (hvp : ValidPrefix M raw act)
    (hrun : Run (decM M '' { x | x ∈ raw ++ act }) sufLen (decM M edgeTT)) :
    ∃ k_end : ℕ, k_end + evalCutChain steps act ≤ act.length + sufLen ∧
      Run (decM M_end '' { x | x ∈ raw_end }) k_end (decM M_end edgeTT) := by
  induction steps generalizing M raw act sufLen with
  | nil =>
    rcases hvalid with ⟨rfl, rfl⟩
    refine ⟨act.length + sufLen, by simp [evalCutChain], validPrefix_to_run hvp hrun⟩
  | cons st rest ih =>
    rcases hvalid with ⟨⟨hmc, hraw, hpv⟩, hrest⟩
    have hstep := cutStep_sound hmc hraw hvp hrun hpv
    dsimp only at hstep
    obtain ⟨hvp', sufLen', hbudget, hrun'⟩ := hstep
    obtain ⟨k_end, hle, hrun_end⟩ := ih hrest hvp' hrun'
    refine ⟨k_end, ?_, hrun_end⟩
    simp only [evalCutChain]
    omega

def eraseMask (n vm s : ℕ) : ℕ :=
  mkBitmask n (fun w => s.testBit w && !vm.testBit w)

theorem testBit_eraseMask {n vm s w : ℕ} (hs : s < 2 ^ n) :
    (eraseMask n vm s).testBit w = (s.testBit w && !vm.testBit w) := by
  rw [eraseMask, testBit_mkBitmask]
  by_cases hlt : w < n
  · simp [hlt]
  · have hsf : s.testBit w = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hs (Nat.pow_le_pow_right (by omega) (by omega)))
    simp [hlt, hsf]

theorem cutEnd_to_hasRunYF {n : ℕ} {H F forbAdded : List (ℕ × ℕ)} {delVMask mc_end : ℕ}
    {rc_end : List ℕ} {k_end : ℕ}
    (hmc_spec : ∀ s, mc_end.testBit s = true ↔
      (univYF n (F ++ forbAdded)).testBit s = true ∧ s &&& delVMask = 0)
    (hrc_spec : ∀ r ∈ rc_end, r = 0 ∨ ∃ w < n, r = ttVarYF n w (univYF n F) &&& mc_end)
    (hrun : Run (decM mc_end '' { x | x ∈ rc_end }) k_end (decM mc_end (edgeTTYF n H (univYF n F)))) :
    let H_end := H.filter (fun e => !forbAdded.any (undirEq e) && !delVMask.testBit e.1 && !delVMask.testBit e.2)
    let F_end := (F ++ forbAdded).filter (fun e => !delVMask.testBit e.1 && !delVMask.testBit e.2)
    HasRunYF n H_end F_end k_end := by
  dsimp only
  set H_end := H.filter (fun e => !forbAdded.any (undirEq e) && !delVMask.testBit e.1 && !delVMask.testBit e.2)
  set F_end := (F ++ forbAdded).filter (fun e => !delVMask.testBit e.1 && !delVMask.testBit e.2)
  have hM : ∀ s, (univYF n F).testBit s = true → s < 2 ^ n := fun _ => univYF_testBit_lt
  have hM_end : ∀ s, (univYF n F_end).testBit s = true → s < 2 ^ n := fun _ => univYF_testBit_lt
  have hdom : ∀ s : Dom (univYF n F_end), mc_end.testBit (eraseMask n delVMask s.1) = true := by
    intro s
    have hslt : s.1 < 2 ^ n := hM_end s.1 s.2
    rw [hmc_spec]
    constructor
    · rw [testBit_univYF, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
      refine ⟨mkBitmask_lt_two_pow n _, Bool.eq_false_iff.mpr fun hf => ?_⟩
      rw [hasEdge_eq_true] at hf
      obtain ⟨f, hfmem, h1, h2⟩ := hf
      rw [testBit_eraseMask hslt, Bool.and_eq_true] at h1 h2
      have hfF_end : f ∈ F_end := List.mem_filter.mpr ⟨hfmem, by simp [h1.2, h2.2]⟩
      have hs2 := s.2
      rw [testBit_univYF, Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff] at hs2
      exact hs2.2 (hasEdge_eq_true F_end s.1 |>.mpr ⟨f, hfF_end, h1.1, h2.1⟩)
    · apply Nat.eq_of_testBit_eq; intro w
      rw [Nat.testBit_and, testBit_eraseMask hslt, Nat.zero_testBit]
      cases s.1.testBit w <;> cases delVMask.testBit w <;> decide
  have hmc_sub_M : ∀ s, mc_end.testBit s = true → (univYF n F).testBit s = true := by
    intro s hs
    have h1 := (hmc_spec s).mp hs |>.1
    rw [testBit_univYF, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', Bool.eq_false_iff] at h1
    rw [testBit_univYF, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', Bool.eq_false_iff]
    refine ⟨h1.1, fun hf => h1.2 ?_⟩
    rw [hasEdge_eq_true] at hf ⊢
    obtain ⟨f, hfF, h2, h3⟩ := hf
    exact ⟨f, List.mem_append_left _ hfF, h2, h3⟩
  let π : Dom (univYF n F_end) → Dom mc_end := fun s => ⟨eraseMask n delVMask s.1, hdom s⟩
  have hatoms : ∀ S ∈ decM mc_end '' { x | x ∈ rc_end }, Meet (rawSet n F_end) (π ⁻¹' S) := by
    rintro S ⟨r, hr, rfl⟩
    rcases hrc_spec r hr with rfl | ⟨w, hw, rfl⟩
    · rw [decM_zero, Set.preimage_empty]; exact Meet.bot
    · by_cases hdel : delVMask.testBit w = true
      · have hemp : π ⁻¹' decM mc_end (ttVarYF n w (univYF n F) &&& mc_end) = ∅ := by
          ext s
          simp only [Set.mem_preimage, mem_decM, Nat.testBit_and, (π s).2, Bool.and_true,
            testBit_ttVarYF hM, hmc_sub_M _ (π s).2, Bool.true_and, Set.mem_empty_iff_false, iff_false]
          change ¬ (eraseMask n delVMask s.1).testBit w = true
          rw [testBit_eraseMask (hM_end s.1 s.2), hdel]; simp
        rw [hemp]; exact Meet.bot
      · have hdel' : delVMask.testBit w = false := Bool.eq_false_iff.mpr hdel
        have heq : π ⁻¹' decM mc_end (ttVarYF n w (univYF n F) &&& mc_end) =
            decM (univYF n F_end) (ttVarYF n w (univYF n F_end)) := by
          ext s
          simp only [Set.mem_preimage, mem_decM, Nat.testBit_and, (π s).2, Bool.and_true,
            testBit_ttVarYF hM, testBit_ttVarYF hM_end, hmc_sub_M _ (π s).2, s.2, Bool.true_and]
          change (eraseMask n delVMask s.1).testBit w = true ↔ s.1.testBit w = true
          rw [testBit_eraseMask (hM_end s.1 s.2), hdel']; simp
        rw [heq]; exact Meet.atom ⟨⟨w, hw⟩, rfl⟩
  have htarget : π ⁻¹' decM mc_end (edgeTTYF n H (univYF n F)) = targetSet n H_end F_end := by
    ext s
    have hslt : s.1 < 2 ^ n := hM_end s.1 s.2
    simp only [Set.mem_preimage, targetSet, mem_decM, testBit_edgeTTYF hM,
      testBit_edgeTTYF hM_end, hmc_sub_M _ (π s).2, s.2, Bool.true_and,
      hasEdge_eq_true]
    constructor
    · rintro ⟨e, heH, h1, h2⟩
      change (eraseMask n delVMask s.1).testBit e.1 = true at h1
      change (eraseMask n delVMask s.1).testBit e.2 = true at h2
      rw [testBit_eraseMask hslt, Bool.and_eq_true] at h1 h2
      have hnotForb : forbAdded.any (undirEq e) = false := by
        rw [Bool.eq_false_iff]
        intro hany
        rw [List.any_eq_true] at hany
        obtain ⟨f, hfmem, hue⟩ := hany
        rw [undirEq_true_iff] at hue
        have hfF_end : f ∈ F_end := by
          refine List.mem_filter.mpr ⟨List.mem_append_right _ hfmem, ?_⟩
          rcases hue with ⟨hu1, hu2⟩ | ⟨hu1, hu2⟩ <;>
            simp [← hu1, ← hu2, h1.2, h2.2]
        have hs2 := s.2
        rw [testBit_univYF, Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff] at hs2
        apply hs2.2
        rw [hasEdge_eq_true]
        rcases hue with ⟨hu1, hu2⟩ | ⟨hu1, hu2⟩
        · exact ⟨f, hfF_end, hu1 ▸ h1.1, hu2 ▸ h2.1⟩
        · exact ⟨f, hfF_end, hu2 ▸ h2.1, hu1 ▸ h1.1⟩
      exact ⟨e, List.mem_filter.mpr ⟨heH, by simp [hnotForb, h1.2, h2.2]⟩, h1.1, h2.1⟩
    · rintro ⟨e, heEnd, h1, h2⟩
      obtain ⟨heH, hfilt⟩ := List.mem_filter.mp heEnd
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hfilt
      refine ⟨e, heH, ?_, ?_⟩
      · change (eraseMask n delVMask s.1).testBit e.1 = true
        rw [testBit_eraseMask hslt, h1, hfilt.1.2]; rfl
      · change (eraseMask n delVMask s.1).testBit e.2 = true
        rw [testBit_eraseMask hslt, h2, hfilt.2]; rfl
  have hr' := freeMap π hatoms hrun
  rwa [htarget] at hr'



def noCovPairs (edgePtsMask : ℕ) : List ℕ → Bool
  | [] => true
  | a :: rest => rest.all (fun b => !Nat.beq (Nat.land (Nat.lor a b) edgePtsMask) edgePtsMask) &&
      noCovPairs edgePtsMask rest

theorem noCovPairs_sound {edgePtsMask : ℕ} {l : List ℕ}
    (hok : noCovPairs edgePtsMask l = true) :
    ∀ a ∈ l, ∀ b ∈ l, a ≠ b → ((a ||| b) &&& edgePtsMask) ≠ edgePtsMask := by
  induction l with
  | nil => intro a ha; simp at ha
  | cons x rest ih =>
    simp only [noCovPairs, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true',
      nat_beq_eq_false_iff, land_eq, lor_eq] at hok
    obtain ⟨hhead, htail⟩ := hok
    intro a ha b hb hab
    rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
    · exact (hab rfl).elim
    · exact hhead b hb'
    · rw [Nat.or_comm]; exact hhead a ha'
    · exact ih htail a ha' b hb' hab

theorem termMd_sound {n : ℕ} {H F : List (ℕ × ℕ)} {pre : List ℕ} {g : ℕ}
    (hv : ValidState n H F) (hHne : H ≠ [])
    (hrun : RunListFrom (univYF n F) (rawYF n (univYF n F)) (edgeTTYF n H (univYF n F)) (pre ++ [g]))
    (hmin : ∀ k' < (pre ++ [g]).length, ¬ HasRunYF n H F k')
    {ops : List ℕ}
    (hops : ∀ x, MeetNat (univYF n F) (rawYF n (univYF n F) ++ pre) x →
      x ≠ 0 → x ≠ univYF n F → x &&& edgePtsMaskYF H ≠ 0 → x ∈ ops) :
    let M := univYF n F
    let B := rawYF n M ++ pre
    let edgeTT := edgeTTYF n H M
    let md := isMeetLoop edgeTT B M
    md = edgeTT ∨
    ¬ (noCovPairs (edgePtsMaskYF H) (ops.filter (fun op => Nat.beq (Nat.land op (md ^^^ edgeTT)) 0)) = true) := by
  set M := univYF n F
  set B := rawYF n M ++ pre
  set edgeTT := edgeTTYF n H M
  set ep := edgePtsMaskYF H
  set md := isMeetLoop edgeTT B M
  by_cases hmd : md = edgeTT
  · exact Or.inl hmd
  right
  intro hnocov
  have hnotFin : isMeet M B edgeTT = false :=
    lexMin_not_finished hrun hmin (by simp)
  obtain ⟨a, b, hgab, hab, ha, hb, ha0, haM, haep, hb0, hbM, hbep⟩ :=
    lexMin_operands hv hrun hmin
  have ha_in : a ∈ ops := hops a ha ha0 haM haep
  have hb_in : b ∈ ops := hops b hb hb0 hbM hbep
  obtain ⟨_, _, hend⟩ := runListFrom_append.mp hrun
  have hEdgeNe0 : edgeTT ≠ 0 := by
    obtain ⟨e, _, heq⟩ := List.exists_cons_of_ne_nil hHne
    intro h0
    have hbit := edgePt_mem_edgeTTYF hv (show e ∈ H by rw [heq]; simp)
    rw [show edgeTTYF n H (univYF n F) = edgeTT from rfl, h0] at hbit
    simp at hbit
  have hloop_end : isMeetLoop edgeTT (B ++ [g]) M = edgeTT := by
    have hm := hend.2
    unfold isMeet at hm
    have hb0' : Nat.beq edgeTT 0 = false := (nat_beq_eq_false_iff _ _).mpr hEdgeNe0
    rw [hb0'] at hm
    exact Nat.eq_of_beq_eq_true hm
  have hloop_split : isMeetLoop edgeTT (B ++ [g]) M =
      match Nat.beq (Nat.land edgeTT g) edgeTT with
      | true => md &&& g
      | false => md := by
    have haux : ∀ (l₁ l₂ : List ℕ) (acc : ℕ),
        isMeetLoop edgeTT (l₁ ++ l₂) acc = isMeetLoop edgeTT l₂ (isMeetLoop edgeTT l₁ acc) := by
      intro l₁
      induction l₁ with
      | nil => intro _ _; rfl
      | cons x xs ih =>
        intro l₂ acc
        simp only [List.cons_append, isMeetLoop]
        cases Nat.beq (Nat.land edgeTT x) edgeTT <;> exact ih l₂ _
    rw [haux B [g] M]
    simp only [isMeetLoop, md, land_eq]
  rw [hloop_split] at hloop_end
  have hsub_eg : edgeTT &&& g = edgeTT := by
    cases hbg : Nat.beq (Nat.land edgeTT g) edgeTT
    · rw [hbg] at hloop_end; exact (hmd hloop_end).elim
    · simpa [land_eq] using Nat.eq_of_beq_eq_true hbg
  have hmd_g : md &&& g = edgeTT := by
    have hbg : Nat.beq (Nat.land edgeTT g) edgeTT = true := by simpa [land_eq] using hsub_eg
    rw [hbg] at hloop_end
    exact hloop_end
  have hsub_md : edgeTT &&& md = edgeTT :=
    isMeetLoop_target_sub B (edgeTTYF_and_univYF n H F)
  have hg_bad : g &&& (md ^^^ edgeTT) = 0 := by
    apply Nat.eq_of_testBit_eq; intro s
    have h1 := congrArg (fun z => z.testBit s) hmd_g
    have h2 := congrArg (fun z => z.testBit s) hsub_md
    simp only [Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit] at h1 h2 ⊢
    revert h1 h2
    cases md.testBit s <;> cases edgeTT.testBit s <;> cases g.testBit s <;> decide
  have ha_bad : a &&& (md ^^^ edgeTT) = 0 := by
    apply Nat.eq_of_testBit_eq; intro s
    have h1 := congrArg (fun z => z.testBit s) hg_bad
    simp only [hgab, Nat.testBit_and, Nat.testBit_or, Nat.zero_testBit] at h1 ⊢
    revert h1
    cases a.testBit s <;> cases b.testBit s <;> cases (md ^^^ edgeTT).testBit s <;> decide
  have hb_bad : b &&& (md ^^^ edgeTT) = 0 := by
    apply Nat.eq_of_testBit_eq; intro s
    have h1 := congrArg (fun z => z.testBit s) hg_bad
    simp only [hgab, Nat.testBit_and, Nat.testBit_or, Nat.zero_testBit] at h1 ⊢
    revert h1
    cases a.testBit s <;> cases b.testBit s <;> cases (md ^^^ edgeTT).testBit s <;> decide
  have ha_good : a ∈ ops.filter (fun op => Nat.beq (Nat.land op (md ^^^ edgeTT)) 0) :=
    List.mem_filter.mpr ⟨ha_in, by simp [ha_bad]⟩
  have hb_good : b ∈ ops.filter (fun op => Nat.beq (Nat.land op (md ^^^ edgeTT)) 0) :=
    List.mem_filter.mpr ⟨hb_in, by simp [hb_bad]⟩
  have hcov : (a ||| b) &&& ep = ep := by
    rw [← hgab]
    apply Nat.eq_of_testBit_eq; intro s
    rw [Nat.testBit_and]
    cases hep : ep.testBit s
    · simp
    · have hed : edgeTT.testBit s = true := by
        rw [testBit_edgePtsMaskYF, List.any_eq_true] at hep
        obtain ⟨e, heH, heq⟩ := hep
        rw [decide_eq_true_eq] at heq
        rw [← heq]; exact edgePt_mem_edgeTTYF hv heH
      have hgs : g.testBit s = true := by
        have := congrArg (fun z => z.testBit s) hsub_eg
        rw [Nat.testBit_and, hed, Bool.true_and] at this; exact this
      simp [hgs]
  exact noCovPairs_sound hnocov a ha_good b hb_good hab hcov



structure CutDefData where
  loss : ℕ
  steps : List CutStepData

def checkValidCutStep (M_prev edgeTT : ℕ) (raw_prev : List ℕ) (st : CutStepData) : Bool :=
  Nat.beq (Nat.land st.mc M_prev) st.mc &&
  raw_prev.all (fun r => let r' := Nat.land r st.mc; Nat.beq r' 0 || st.rc.contains r') &&
  st.rc.all (fun r' => raw_prev.any (fun r => Nat.beq r' (Nat.land r st.mc))) &&
  st.pv.all (fun pm =>
    Nat.beq (Nat.land pm M_prev) pm &&
    !Nat.beq (Nat.land pm edgeTT) 0 &&
    !Nat.beq (Nat.land pm edgeTT) pm &&
    !Nat.beq (Nat.land edgeTT st.mc) 0 &&
    raw_prev.all (fun r => probeOkGate st.mc pm r))

def checkValidCutChain (M edgeTT : ℕ) (raw : List ℕ) :
    List CutStepData → ℕ → List ℕ → Bool
  | [], M_end, raw_end => Nat.beq M M_end && decide (raw = raw_end)
  | st :: rest, M_end, raw_end =>
    checkValidCutStep M edgeTT raw st &&
    checkValidCutChain st.mc edgeTT st.rc rest M_end raw_end

def cutEndMask (n : ℕ) (F forbAdded : List (ℕ × ℕ)) (delVMask : ℕ) : ℕ :=
  mkBitmask (2 ^ n) (fun s => (univYF n (F ++ forbAdded)).testBit s && Nat.beq (Nat.land s delVMask) 0)

def cutEndEdges (H forbAdded : List (ℕ × ℕ)) (delVMask : ℕ) : List (ℕ × ℕ) :=
  H.filter (fun e => !forbAdded.any (undirEq e) && !delVMask.testBit e.1 && !delVMask.testBit e.2)

def cutEndForb (F forbAdded : List (ℕ × ℕ)) (delVMask : ℕ) : List (ℕ × ℕ) :=
  (F ++ forbAdded).filter (fun e => !delVMask.testBit e.1 && !delVMask.testBit e.2)

def checkCutValid (n : ℕ) (H F : List (ℕ × ℕ)) (cut : CutDefData)
    (delVMask : ℕ) (forbAdded : List (ℕ × ℕ)) (peels : List ℕ)
    (n_c : ℕ) (H_c F_c : List (ℕ × ℕ)) (f : List ℕ) : Bool :=
  let M := univYF n F
  let raw := rawYF n M
  let edgeTT := edgeTTYF n H M
  let M_end := cutEndMask n F forbAdded delVMask
  let rc_end := match cut.steps.getLast? with | none => raw | some st => st.rc
  let H_end := cutEndEdges H forbAdded delVMask
  let F_end := cutEndForb F forbAdded delVMask
  checkValidCutChain M edgeTT raw cut.steps M_end rc_end &&
  decide (ValidState n H_end F_end) &&
  decide (1 ≤ H_end.length) &&
  decide (H.length ≤ H_end.length + cut.loss) &&
  validPeelEmbed n H_end F_end peels n_c H_c F_c f

theorem checkValidCutStep_sound {M_prev edgeTT : ℕ} {raw_prev : List ℕ} {st : CutStepData}
    (hok : checkValidCutStep M_prev edgeTT raw_prev st = true) :
    ValidCutStep M_prev edgeTT raw_prev st ∧
    (∀ r' ∈ st.rc, ∃ r ∈ raw_prev, r' = r &&& st.mc) := by
  unfold checkValidCutStep at hok
  simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', nat_beq_eq_true_iff, nat_beq_eq_false_iff, land_eq,
    List.contains_eq_mem, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨hmc, hraw⟩, hrc⟩, hpv⟩ := hok
  refine ⟨⟨hmc, hraw, fun pm hpm => ?_⟩, hrc⟩
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hpv pm hpm
  exact ⟨h1, h2, h3, h4, h5⟩

theorem checkValidCutChain_sound {n : ℕ} {F : List (ℕ × ℕ)} {M edgeTT M_end : ℕ}
    {raw raw_end : List ℕ} {steps : List CutStepData}
    (hraw_inv : ∀ r ∈ raw, r = 0 ∨ ∃ w < n, r = ttVarYF n w (univYF n F) &&& M)
    (hok : checkValidCutChain M edgeTT raw steps M_end raw_end = true) :
    ValidCutChain M edgeTT raw steps M_end raw_end ∧
    (∀ r ∈ raw_end, r = 0 ∨ ∃ w < n, r = ttVarYF n w (univYF n F) &&& M_end) := by
  induction steps generalizing M raw with
  | nil =>
    simp only [checkValidCutChain, Bool.and_eq_true, nat_beq_eq_true_iff, decide_eq_true_eq] at hok
    rcases hok with ⟨rfl, rfl⟩
    exact ⟨⟨rfl, rfl⟩, hraw_inv⟩
  | cons st rest ih =>
    simp only [checkValidCutChain, Bool.and_eq_true] at hok
    obtain ⟨hst, hrc_sub⟩ := checkValidCutStep_sound hok.1
    have hraw_next : ∀ r' ∈ st.rc, r' = 0 ∨ ∃ w < n, r' = ttVarYF n w (univYF n F) &&& st.mc := by
      intro r' hr'
      obtain ⟨r, hr, rfl⟩ := hrc_sub r' hr'
      rcases hraw_inv r hr with rfl | ⟨w, hw, rfl⟩
      · exact Or.inl (by simp)
      · refine Or.inr ⟨w, hw, ?_⟩
        rw [Nat.and_assoc, Nat.and_comm M st.mc, hst.1]
    obtain ⟨hchain, hend_inv⟩ := ih hraw_next hok.2
    exact ⟨⟨hst, hchain⟩, hend_inv⟩

theorem cutDef_kills_sound {n : ℕ} {H F : List (ℕ × ℕ)} {cut : CutDefData}
    {delVMask : ℕ} {forbAdded : List (ℕ × ℕ)} {peels : List ℕ}
    {n_c : ℕ} {H_c F_c : List (ℕ × ℕ)} {f : List ℕ}
    (hcut : checkCutValid n H F cut delVMask forbAdded peels n_c H_c F_c f = true)
    (hchild : OrCostLB n_c H_c F_c (H_c.length - 1))
    {pre suf : List ℕ}
    (hrun : RunListFrom (univYF n F) (rawYF n (univYF n F)) (edgeTTYF n H (univYF n F)) (pre ++ suf))
    (hlen : (pre ++ suf).length + 2 ≤ H.length)
    (hkilled : cut.loss ≤ evalCutChain cut.steps pre) :
    False := by
  unfold checkCutValid at hcut
  dsimp only at hcut
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcut
  obtain ⟨⟨⟨⟨hchain_ok, hv_end⟩, hne_end⟩, hloss_le⟩, hpeel_ok⟩ := hcut
  set M := univYF n F
  set raw := rawYF n M
  set edgeTT := edgeTTYF n H M
  set M_end := cutEndMask n F forbAdded delVMask
  set rc_end := match cut.steps.getLast? with | none => raw | some st => st.rc
  have hM : ∀ s, M.testBit s = true → s < 2 ^ n := fun _ => univYF_testBit_lt
  have hraw_inv : ∀ r ∈ raw, r = 0 ∨ ∃ w < n, r = ttVarYF n w M &&& M := by
    intro r hr
    simp only [raw, rawYF, List.mem_map, List.mem_range] at hr
    obtain ⟨w, hw, rfl⟩ := hr
    exact Or.inr ⟨w, hw, (ttVarYF_and_mask hM).symm⟩
  obtain ⟨hchain, hrc_inv⟩ := checkValidCutChain_sound hraw_inv hchain_ok
  obtain ⟨hvp, hsuf⟩ := runListFrom_append.mp hrun
  have hrun_suf : Run (decM M '' { x | x ∈ raw ++ pre }) suf.length (decM M edgeTT) :=
    runListFrom_to_run hsuf
  obtain ⟨k_end, hk_budget, hrun_end⟩ := cutChain_sound cut.steps hchain hvp hrun_suf
  have hmc_spec : ∀ s, M_end.testBit s = true ↔
      (univYF n (F ++ forbAdded)).testBit s = true ∧ s &&& delVMask = 0 := by
    intro s
    simp only [M_end, cutEndMask, testBit_mkBitmask, Bool.and_eq_true, decide_eq_true_eq,
      nat_beq_eq_true_iff, land_eq]
    exact ⟨fun ⟨_, h1, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨univYF_testBit_lt h1, h1, h2⟩⟩
  have hhas_end : HasRunYF n (cutEndEdges H forbAdded delVMask) (cutEndForb F forbAdded delVMask) k_end :=
    cutEnd_to_hasRunYF hmc_spec hrc_inv hrun_end
  have hlb_end : (cutEndEdges H forbAdded delVMask).length - 1 ≤ k_end :=
    validPeelEmbed_sound hv_end hpeel_ok hchild k_end hhas_end
  simp only [List.length_append] at hlen
  omega



def edgeFnList (n : ℕ) (H : List (ℕ × ℕ)) (x : Fin n → Bool) : Bool :=
  H.any (fun e => if h : e.1 < n ∧ e.2 < n then x ⟨e.1, h.1⟩ && x ⟨e.2, h.2⟩ else false)

theorem or_bound_of_eval_eq {n lb : ℕ} {H : List (ℕ × ℕ)} {f : (Fin n → Bool) → Bool}
    (hH : ∀ e ∈ H, e.1 < n ∧ e.2 < n)
    (hf : ∀ x : Fin n → Bool, f x = edgeFnList n H x)
    (hlb : OrCostLB n H [] lb)
    (C : Circuit) (hc : Monotone2 C)
    (he : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x) :
    lb ≤ countOrGates C.gates := by
  have he' : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
      ∃ e ∈ H, ∃ (h1 : e.1 < n) (h2 : e.2 < n), x ⟨e.1, h1⟩ = true ∧ x ⟨e.2, h2⟩ = true := by
    intro x
    rw [he x, hf x, edgeFnList, List.any_eq_true]
    constructor
    · rintro ⟨e, heH, hval⟩
      obtain ⟨h1, h2⟩ := hH e heH
      simp only [h1, h2, and_self, ↓reduceDIte, Bool.and_eq_true] at hval
      exact ⟨e, heH, h1, h2, hval.1, hval.2⟩
    · rintro ⟨e, heH, h1, h2, hx1, hx2⟩
      refine ⟨e, heH, ?_⟩
      simp only [h1, h2, and_self, ↓reduceDIte, Bool.and_eq_true]
      exact ⟨hx1, hx2⟩
  obtain ⟨k, hk, hrun⟩ := ofCircuitYF H C hc he' hH
  exact (hlb k hrun).trans hk

def g0_edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (3, 5), (4, 5)]
def g0_fn (x : Fin 6 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)
theorem g0_fn_eq : ∀ x : Fin 6 → Bool, g0_fn x = edgeFnList 6 g0_edges x := by
  intro x; simp [g0_fn, edgeFnList, g0_edges, Bool.or_assoc]

def g1_edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 4), (5, 6)]
def g1_fn (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)
theorem g1_fn_eq : ∀ x : Fin 7 → Bool, g1_fn x = edgeFnList 7 g1_edges x := by
  intro x; simp [g1_fn, edgeFnList, g1_edges, Bool.or_assoc]

def g2_edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 5), (4, 6)]
def g2_fn (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6)
theorem g2_fn_eq : ∀ x : Fin 7 → Bool, g2_fn x = edgeFnList 7 g2_edges x := by
  intro x; simp [g2_fn, edgeFnList, g2_edges, Bool.or_assoc]

def g3_edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (4, 6)]
def g3_fn (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6)
theorem g3_fn_eq : ∀ x : Fin 7 → Bool, g3_fn x = edgeFnList 7 g3_edges x := by
  intro x; simp [g3_fn, edgeFnList, g3_edges, Bool.or_assoc]

def g4_edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (3, 5), (4, 6)]
def g4_fn (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)
theorem g4_fn_eq : ∀ x : Fin 7 → Bool, g4_fn x = edgeFnList 7 g4_edges x := by
  intro x; simp [g4_fn, edgeFnList, g4_edges, Bool.or_assoc]

def g5_edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (4, 5), (5, 6)]
def g5_fn (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6)
theorem g5_fn_eq : ∀ x : Fin 7 → Bool, g5_fn x = edgeFnList 7 g5_edges x := by
  intro x; simp [g5_fn, edgeFnList, g5_edges, Bool.or_assoc]

def g6_edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (1, 2), (4, 5), (4, 6), (5, 6)]
def g6_fn (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)
theorem g6_fn_eq : ∀ x : Fin 7 → Bool, g6_fn x = edgeFnList 7 g6_edges x := by
  intro x; simp [g6_fn, edgeFnList, g6_edges, Bool.or_assoc]

def g7_edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (1, 4), (2, 5), (3, 6), (4, 5)]
def g7_fn (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5)
theorem g7_fn_eq : ∀ x : Fin 7 → Bool, g7_fn x = edgeFnList 7 g7_edges x := by
  intro x; simp [g7_fn, edgeFnList, g7_edges, Bool.or_assoc]

def g8_edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (1, 3), (2, 4), (3, 5), (4, 6), (5, 6)]
def g8_fn (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)
theorem g8_fn_eq : ∀ x : Fin 7 → Bool, g8_fn x = edgeFnList 7 g8_edges x := by
  intro x; simp [g8_fn, edgeFnList, g8_edges, Bool.or_assoc]

def g9_edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, 2), (3, 4)]
def g9_fn (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4)
theorem g9_fn_eq : ∀ x : Fin 7 → Bool, g9_fn x = edgeFnList 7 g9_edges x := by
  intro x; simp [g9_fn, edgeFnList, g9_edges, Bool.or_assoc]

def g10_edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 6), (3, 4)]
def g10_fn (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6) || (x 3 && x 4)
theorem g10_fn_eq : ∀ x : Fin 7 → Bool, g10_fn x = edgeFnList 7 g10_edges x := by
  intro x; simp [g10_fn, edgeFnList, g10_edges, Bool.or_assoc]

def g11_edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (3, 4), (5, 6)]
def g11_fn (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)
theorem g11_fn_eq : ∀ x : Fin 7 → Bool, g11_fn x = edgeFnList 7 g11_edges x := by
  intro x; simp [g11_fn, edgeFnList, g11_edges, Bool.or_assoc]

def g12_edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (1, 6), (3, 4)]
def g12_fn (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4)
theorem g12_fn_eq : ∀ x : Fin 7 → Bool, g12_fn x = edgeFnList 7 g12_edges x := by
  intro x; simp [g12_fn, edgeFnList, g12_edges, Bool.or_assoc]

def g13_edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (2, 6), (3, 4)]
def g13_fn (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 4)
theorem g13_fn_eq : ∀ x : Fin 7 → Bool, g13_fn x = edgeFnList 7 g13_edges x := by
  intro x; simp [g13_fn, edgeFnList, g13_edges, Bool.or_assoc]

def g14_edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 4), (3, 6)]
def g14_fn (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6)
theorem g14_fn_eq : ∀ x : Fin 7 → Bool, g14_fn x = edgeFnList 7 g14_edges x := by
  intro x; simp [g14_fn, edgeFnList, g14_edges, Bool.or_assoc]

def g15_edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 4), (5, 6)]
def g15_fn (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 5 && x 6)
theorem g15_fn_eq : ∀ x : Fin 7 → Bool, g15_fn x = edgeFnList 7 g15_edges x := by
  intro x; simp [g15_fn, edgeFnList, g15_edges, Bool.or_assoc]

def g16_edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 6), (5, 6)]
def g16_fn (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6) || (x 5 && x 6)
theorem g16_fn_eq : ∀ x : Fin 7 → Bool, g16_fn x = edgeFnList 7 g16_edges x := by
  intro x; simp [g16_fn, edgeFnList, g16_edges, Bool.or_assoc]

def g17_edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 5), (3, 6), (5, 6)]
def g17_fn (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6)
theorem g17_fn_eq : ∀ x : Fin 7 → Bool, g17_fn x = edgeFnList 7 g17_edges x := by
  intro x; simp [g17_fn, edgeFnList, g17_edges, Bool.or_assoc]

def g18_edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (3, 5), (4, 6), (5, 6)]
def g18_fn (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)
theorem g18_fn_eq : ∀ x : Fin 7 → Bool, g18_fn x = edgeFnList 7 g18_edges x := by
  intro x; simp [g18_fn, edgeFnList, g18_edges, Bool.or_assoc]

def g19_edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (2, 5), (3, 6), (4, 6)]
def g19_fn (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6)
theorem g19_fn_eq : ∀ x : Fin 7 → Bool, g19_fn x = edgeFnList 7 g19_edges x := by
  intro x; simp [g19_fn, edgeFnList, g19_edges, Bool.or_assoc]

def g20_edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (3, 6), (4, 5)]
def g20_fn (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5)
theorem g20_fn_eq : ∀ x : Fin 7 → Bool, g20_fn x = edgeFnList 7 g20_edges x := by
  intro x; simp [g20_fn, edgeFnList, g20_edges, Bool.or_assoc]

def g21_edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (3, 6), (5, 6)]
def g21_fn (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6)
theorem g21_fn_eq : ∀ x : Fin 7 → Bool, g21_fn x = edgeFnList 7 g21_edges x := by
  intro x; simp [g21_fn, edgeFnList, g21_edges, Bool.or_assoc]

def g22_edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (4, 5), (5, 6)]
def g22_fn (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5) || (x 5 && x 6)
theorem g22_fn_eq : ∀ x : Fin 7 → Bool, g22_fn x = edgeFnList 7 g22_edges x := by
  intro x; simp [g22_fn, edgeFnList, g22_edges, Bool.or_assoc]

def g23_edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (4, 6), (5, 6)]
def g23_fn (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)
theorem g23_fn_eq : ∀ x : Fin 7 → Bool, g23_fn x = edgeFnList 7 g23_edges x := by
  intro x; simp [g23_fn, edgeFnList, g23_edges, Bool.or_assoc]

def g24_edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (4, 5), (4, 6), (5, 6)]
def g24_fn (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)
theorem g24_fn_eq : ∀ x : Fin 7 → Bool, g24_fn x = edgeFnList 7 g24_edges x := by
  intro x; simp [g24_fn, edgeFnList, g24_edges, Bool.or_assoc]

def g25_edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (1, 4), (2, 5), (3, 6), (4, 5), (4, 6)]
def g25_fn (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 4 && x 6)
theorem g25_fn_eq : ∀ x : Fin 7 → Bool, g25_fn x = edgeFnList 7 g25_edges x := by
  intro x; simp [g25_fn, edgeFnList, g25_edges, Bool.or_assoc]

def g26_edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, 2), (3, 4), (5, 6)]
def g26_fn (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)
theorem g26_fn_eq : ∀ x : Fin 7 → Bool, g26_fn x = edgeFnList 7 g26_edges x := by
  intro x; simp [g26_fn, edgeFnList, g26_edges, Bool.or_assoc]

def g27_edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (1, 6), (3, 4), (5, 6)]
def g27_fn (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4) || (x 5 && x 6)
theorem g27_fn_eq : ∀ x : Fin 7 → Bool, g27_fn x = edgeFnList 7 g27_edges x := by
  intro x; simp [g27_fn, edgeFnList, g27_edges, Bool.or_assoc]

def g28_edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 4), (3, 6), (5, 6)]
def g28_fn (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6) || (x 5 && x 6)
theorem g28_fn_eq : ∀ x : Fin 7 → Bool, g28_fn x = edgeFnList 7 g28_edges x := by
  intro x; simp [g28_fn, edgeFnList, g28_edges, Bool.or_assoc]

def g29_edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (2, 5), (3, 6), (4, 6), (5, 6)]
def g29_fn (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6) || (x 5 && x 6)
theorem g29_fn_eq : ∀ x : Fin 7 → Bool, g29_fn x = edgeFnList 7 g29_edges x := by
  intro x; simp [g29_fn, edgeFnList, g29_edges, Bool.or_assoc]

def g30_edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (3, 6), (4, 5), (5, 6)]
def g30_fn (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 5 && x 6)
theorem g30_fn_eq : ∀ x : Fin 7 → Bool, g30_fn x = edgeFnList 7 g30_edges x := by
  intro x; simp [g30_fn, edgeFnList, g30_edges, Bool.or_assoc]



structure StateDesc where
  n     : Nat
  edges : List (Nat × Nat)
  forb  : List (Nat × Nat)

structure CutSpecData where
  delVMask  : Nat
  forbAdded : List (Nat × Nat)
  peels     : List Nat
  childId   : Nat
  embed     : List Nat

structure GraphCoreSpec where
  graphIdx : Nat
  n        : Nat
  edges    : List (Nat × Nat)
  bound    : Nat
  coreId   : Nat
  peels    : List Nat
  embed    : List Nat

structure ChkStepState where
  mc        : Nat
  sb        : List Nat
  validPv   : List Nat
  tailBonus : Nat

structure ChkCutState where
  need  : Nat
  steps : List ChkStepState

inductive ChkCutStepSpec where
  | v : Nat → List Nat → ChkCutStepSpec
  | e : List (Nat × Nat) → ChkCutStepSpec

mutual
  inductive CertNode where
    | term : CertNode
    | branch : List Nat → List (List Nat) → CertList → CertNode

  inductive CertList where
    | nil : CertList
    | cons : Nat → CertNode → CertList → CertList
end

def chkAll128 : Nat := 0xffffffffffffffffffffffffffffffff

def chkVarOne : Nat → Nat
  | 0 => 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
  | 1 => 0xcccccccccccccccccccccccccccccccc
  | 2 => 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
  | 3 => 0xff00ff00ff00ff00ff00ff00ff00ff00
  | 4 => 0xffff0000ffff0000ffff0000ffff0000
  | 5 => 0xffffffff00000000ffffffff00000000
  | 6 => 0xffffffffffffffff0000000000000000
  | _ => 0

def chkVarZero (v : Nat) : Nat := Nat.xor chkAll128 (chkVarOne v)

def chkForbLoop (acc : Nat) : List (Nat × Nat) → Nat
  | [] => acc
  | (u, v) :: rest =>
    chkForbLoop (Nat.land acc (Nat.xor chkAll128 (Nat.land (chkVarOne u) (chkVarOne v)))) rest

def chkMkRawLoop (maskYF : Nat) : Nat → Nat → List Nat
  | _, 0 => []
  | v, k + 1 => Nat.land maskYF (chkVarOne v) :: chkMkRawLoop maskYF (v + 1) k

def chkMkRaw (n maskYF : Nat) : List Nat := chkMkRawLoop maskYF 0 n

def chkMkEdgeMasks (maskYF : Nat) : List (Nat × Nat) → List Nat
  | [] => []
  | (u, v) :: rest => Nat.land maskYF (Nat.land (chkVarOne u) (chkVarOne v)) :: chkMkEdgeMasks maskYF rest

def chkMkMasksTT (n : Nat) (edges : List (Nat × Nat)) (maskYF : Nat) : List Nat :=
  maskYF :: chkMkRaw n maskYF ++ chkMkEdgeMasks maskYF edges

def chkFilterRc (mc : Nat) : List Nat → List Nat
  | [] => []
  | r :: rest =>
    let r' := Nat.land r mc
    match Nat.beq r' 0 with
    | true => chkFilterRc mc rest
    | false => r' :: chkFilterRc mc rest

def chkMkPv (v : Nat) : List Nat → List Nat
  | [] => []
  | s :: rest =>
    Nat.lor (Nat.pow 2 s) (Nat.pow 2 (Nat.lor s (Nat.pow 2 v))) :: chkMkPv v rest

def chkBuildCutSteps (mPrev : Nat) (rPrev : List Nat) : List ChkCutStepSpec → List CutStepData
  | [] => []
  | .v v ps :: rest =>
    let mc := Nat.land mPrev (chkVarZero v)
    let rc := chkFilterRc mc rPrev
    { mc := mc, rc := rc, pv := chkMkPv v ps } :: chkBuildCutSteps mc rc rest
  | .e es :: rest =>
    let mc := chkForbLoop mPrev es
    let rc := chkFilterRc mc rPrev
    { mc := mc, rc := rc, pv := [] } :: chkBuildCutSteps mc rc rest

def chkMkCuts (maskYF : Nat) (raw : List Nat) : List (Nat × List ChkCutStepSpec) → List CutDefData
  | [] => []
  | (loss, specs) :: rest =>
    { loss := loss, steps := chkBuildCutSteps maskYF raw specs } :: chkMkCuts maskYF raw rest

def chkAppend : List Nat → List Nat → List Nat
  | [], ys => ys
  | x :: xs, ys => x :: chkAppend xs ys

def chkFlatten : List (List Nat) → List Nat
  | [] => []
  | c :: rest => chkAppend c (chkFlatten rest)

def chkMemNat (x : Nat) : List Nat → Bool
  | [] => false
  | y :: rest =>
    match Nat.beq x y with
    | true => true
    | false => chkMemNat x rest

def chkIsMeetLoop (target acc : Nat) : List Nat → Bool
  | [] => Nat.beq acc target
  | b :: rest =>
    match Nat.beq (Nat.land target b) target with
    | true =>
      let acc' := Nat.land acc b
      match Nat.beq acc' target with
      | true => true
      | false => chkIsMeetLoop target acc' rest
    | false => chkIsMeetLoop target acc rest

def chkIsMeet (univMask : Nat) (basis : List Nat) (target : Nat) : Bool :=
  match Nat.beq target 0 with
  | true => true
  | false => chkIsMeetLoop target univMask basis

def chkIsOnEdgesLoop (eg g acc : Nat) : List Nat → Bool
  | [] => Nat.beq (Nat.land acc g) acc
  | b :: rest =>
    match Nat.beq (Nat.land eg b) eg with
    | true =>
      let acc' := Nat.land acc b
      match Nat.beq (Nat.land acc' g) acc' with
      | true => true
      | false => chkIsOnEdgesLoop eg g acc' rest
    | false => chkIsOnEdgesLoop eg g acc rest

def chkProbeOkGate (mc pm h : Nat) : Bool :=
  let x := Nat.land h pm
  match Nat.beq x 0 with
  | true => true
  | false =>
    match Nat.beq x pm with
    | true => true
    | false => Nat.beq (Nat.land h mc) 0

def chkAllProbeOk (mc pm : Nat) : List Nat → Bool
  | [] => true
  | h :: rest =>
    match chkProbeOkGate mc pm h with
    | true => chkAllProbeOk mc pm rest
    | false => false

def chkFilterPv (mc : Nat) (act : List Nat) : List Nat → List Nat
  | [] => []
  | pm :: rest =>
    match chkAllProbeOk mc pm act with
    | true => pm :: chkFilterPv mc act rest
    | false => chkFilterPv mc act rest

def chkAnyProbeOk (mc g : Nat) : List Nat → Bool
  | [] => false
  | pm :: rest =>
    match chkProbeOkGate mc pm g with
    | true => true
    | false => chkAnyProbeOk mc g rest

def chkStepFilterAct (mc : Nat) : List Nat → List Nat → Nat → List Nat → (List Nat × Nat × List Nat)
  | [], sb, sv, actRev => (sb, sv, actRev.reverse)
  | h :: rest, sb, sv, actRev =>
    let rh := Nat.land h mc
    match chkIsMeet mc sb rh with
    | true => chkStepFilterAct mc rest sb (sv + 1) actRev
    | false => chkStepFilterAct mc rest (rh :: sb) sv (rh :: actRev)

def chkPrepSteps : List CutStepData → List Nat → Nat → (Nat × Nat × List ChkStepState)
  | [], _, sv => (sv, 0, [])
  | st :: rest, act, sv =>
    let vp := chkFilterPv st.mc act st.pv
    let (sb, sv', act') := chkStepFilterAct st.mc act st.rc sv []
    let (totSv, tailB, restStates) := chkPrepSteps rest act' sv'
    let myB := match vp with | [] => 0 | _ :: _ => 1
    (totSv, myB + tailB, { mc := st.mc, sb := sb, validPv := vp, tailBonus := tailB } :: restStates)

def chkPrepCutState (cut : CutDefData) (gs : List Nat) : ChkCutState :=
  let (totSv, _, sts) := chkPrepSteps cut.steps gs 0
  { need := Nat.sub cut.loss totSv, steps := sts }

def chkCutKillsAtStep (g need : Nat) : Nat → List ChkStepState → Bool
  | _, [] => Nat.beq need 0
  | 0, st :: _ =>
    let rg := Nat.land g st.mc
    match chkIsMeet st.mc st.sb rg with
    | false => false
    | true =>
      match Nat.ble need (1 + st.tailBonus) with
      | true => true
      | false =>
        match Nat.ble need (2 + st.tailBonus) with
        | true => chkAnyProbeOk st.mc g st.validPv
        | false => false
  | s' + 1, st :: rest =>
    let need' := match st.validPv with
      | [] => need
      | _ :: _ =>
        match chkAnyProbeOk st.mc g st.validPv with
        | true => Nat.sub need 1
        | false => need
    match Nat.beq need' 0 with
    | true => true
    | false => chkCutKillsAtStep (Nat.land g st.mc) need' s' rest

def chkCutKillsWit (cs : ChkCutState) (stepIdx g : Nat) : Bool :=
  match Nat.beq cs.need 0 with
  | true => true
  | false => chkCutKillsAtStep g cs.need stepIdx cs.steps

def chkGetCutState (xs : List ChkCutState) : Nat → ChkCutState
  | 0 => match xs with | c :: _ => c | [] => { need := 1, steps := [] }
  | k + 1 => match xs with | _ :: rest => chkGetCutState rest k | [] => { need := 1, steps := [] }

def chkApplyPermLoop (f acc : Nat) : List Nat → Nat
  | [] => acc
  | m2 :: rest =>
    match Nat.beq f 0 with
    | true => acc
    | false =>
      let acc' := match Nat.beq (Nat.land f 1) 1 with | true => Nat.lor acc m2 | false => acc
      chkApplyPermLoop (Nat.div f 2) acc' rest

def chkApplyPerm (tbl : List Nat) (f : Nat) : Nat :=
  chkApplyPermLoop f 0 tbl

def chkApplyPermList (f : Nat) : List (List Nat) → List Nat
  | [] => []
  | tbl :: rest => chkApplyPerm tbl f :: chkApplyPermList f rest

def chkAnyPermLt (g : Nat) : List Nat → List Nat → Bool
  | p :: ps, q :: qs =>
    match Nat.blt (Nat.lor p q) g with
    | true => true
    | false => chkAnyPermLt g ps qs
  | _, _ => false

def chkFilterStab (g : Nat) : List (List Nat) → List (List Nat)
  | [] => []
  | tbl :: rest =>
    match Nat.beq (chkApplyPerm tbl g) g with
    | true => tbl :: chkFilterStab g rest
    | false => chkFilterStab g rest

def chkGetCut (cuts : List CutDefData) : Nat → CutDefData
  | 0 => match cuts with | c :: _ => c | [] => { loss := 1, steps := [] }
  | k + 1 => match cuts with | _ :: rest => chkGetCut rest k | [] => { loss := 1, steps := [] }

def chkPrepHints (cuts : List CutDefData) (gs : List Nat) : List Nat → List ChkCutState
  | [] => []
  | ci :: rest => chkPrepCutState (chkGetCut cuts ci) gs :: chkPrepHints cuts gs rest

def chkSubsetsStep (g : Nat) : List Nat → List Nat → List Nat
  | [], acc => acc
  | x :: rest, acc => chkSubsetsStep g rest (Nat.land x g :: acc)

def chkAddBirthOps (maskYF edgePtsMask gi birth : Nat) : List Nat → List Nat → List (Nat × Nat × Nat) → (List Nat × List (Nat × Nat × Nat))
  | [], seen, acc => (seen, acc)
  | mt :: rest, seen, acc =>
    let op := Nat.land mt gi
    match Nat.beq op 0 with
    | true => chkAddBirthOps maskYF edgePtsMask gi birth rest seen acc
    | false =>
      match Nat.beq op maskYF with
      | true => chkAddBirthOps maskYF edgePtsMask gi birth rest seen acc
      | false =>
        let eg := Nat.land op edgePtsMask
        match Nat.beq eg 0 with
        | true => chkAddBirthOps maskYF edgePtsMask gi birth rest seen acc
        | false =>
          match chkMemNat op seen with
          | true => chkAddBirthOps maskYF edgePtsMask gi birth rest seen acc
          | false => chkAddBirthOps maskYF edgePtsMask gi birth rest (op :: seen) ((op, eg, birth) :: acc)

def chkAddSubsOps (maskYF edgePtsMask birth : Nat) (masksTT : List Nat) : List Nat → List Nat → List (Nat × Nat × Nat) → (List Nat × List (Nat × Nat × Nat))
  | [], seen, acc => (seen, acc)
  | gi :: rest, seen, acc =>
    let (seen', acc') := chkAddBirthOps maskYF edgePtsMask gi birth masksTT seen acc
    chkAddSubsOps maskYF edgePtsMask birth masksTT rest seen' acc'

def chkGenBirthLoop (maskYF edgePtsMask : Nat) (masksTT : List Nat) (birth : Nat)
    (subs seen : List Nat) (acc : List (Nat × Nat × Nat)) : List Nat → List (Nat × Nat × Nat)
  | [] => acc
  | g :: rest =>
    let newSubs := chkSubsetsStep g subs []
    let (seen', acc') := chkAddSubsOps maskYF edgePtsMask birth masksTT newSubs seen acc
    chkGenBirthLoop maskYF edgePtsMask masksTT (birth + 1) (newSubs ++ subs) seen' acc' rest

def chkGenBirthOps (maskYF edgePtsMask : Nat) (masksTT gs : List Nat) : List (Nat × Nat × Nat) :=
  let (seen0, acc0) := chkAddBirthOps maskYF edgePtsMask maskYF 0 masksTT [] []
  chkGenBirthLoop maskYF edgePtsMask masksTT 1 [maskYF] seen0 acc0 gs

def chkNatMax (a b : Nat) : Nat :=
  match Nat.blt a b with | true => b | false => a

def chkBuildSuffixMax : List Nat → List Nat
  | [] => [0]
  | g :: rest =>
    match chkBuildSuffixMax rest with
    | [] => [g, 0]
    | m :: ms => chkNatMax g m :: m :: ms

def chkGetNat (xs : List Nat) : Nat → Nat
  | 0 => match xs with | x :: _ => x | [] => 0
  | k + 1 => match xs with | _ :: rest => chkGetNat rest k | [] => 0

def chkCheckWitNoStab (maskYF : Nat) (b : List Nat) (hStates : List ChkCutState) (surv : List Nat)
    (eg g w : Nat) : Bool :=
  match w with
  | 0 => chkMemNat g surv
  | 1 => chkIsOnEdgesLoop eg g maskYF b
  | 2 => false
  | w3 + 3 => chkCutKillsWit (chkGetCutState hStates (Nat.div w3 8)) (Nat.land w3 7) g

def chkPairsNoStabInner (maskYF : Nat) (b : List Nat) (hStates : List ChkCutState)
    (surv : List Nat) (oi egi lim : Nat) : List (Nat × Nat × Nat) → List Nat → Option (List Nat)
  | [], wits => some wits
  | (oj, egj, _) :: rest, wits =>
    let eij := Nat.land egi egj
    match Nat.beq eij egi with
    | true => chkPairsNoStabInner maskYF b hStates surv oi egi lim rest wits
    | false =>
      match Nat.beq eij egj with
      | true => chkPairsNoStabInner maskYF b hStates surv oi egi lim rest wits
      | false =>
        let g := Nat.lor oi oj
        let skipLex := match Nat.beq lim 0 with | true => false | false => Nat.blt g lim
        match skipLex with
        | true => chkPairsNoStabInner maskYF b hStates surv oi egi lim rest wits
        | false =>
          match wits with
          | [] => none
          | w :: ws =>
            match chkCheckWitNoStab maskYF b hStates surv (Nat.lor egi egj) g w with
            | true => chkPairsNoStabInner maskYF b hStates surv oi egi lim rest ws
            | false => none

def chkPairsNoStabOuter (maskYF : Nat) (b : List Nat) (hStates : List ChkCutState)
    (surv smax : List Nat) : List (Nat × Nat × Nat) → List Nat → Bool
  | [], _ => true
  | (oi, egi, bi) :: rest, wits =>
    let lim := chkGetNat smax bi
    match chkPairsNoStabInner maskYF b hStates surv oi egi lim rest wits with
    | some wits' => chkPairsNoStabOuter maskYF b hStates surv smax rest wits'
    | none => false

def chkAttachPerms (stab : List (List Nat)) : List (Nat × Nat × Nat) → List (Nat × Nat × Nat × List Nat)
  | [] => []
  | (op, eg, bi) :: rest => (op, eg, bi, chkApplyPermList op stab) :: chkAttachPerms stab rest

def chkCheckWitStab (maskYF : Nat) (b : List Nat) (hStates : List ChkCutState) (surv : List Nat)
    (eg g : Nat) (pi pj : List Nat) (w : Nat) : Bool :=
  match w with
  | 0 => chkMemNat g surv
  | 1 => chkIsOnEdgesLoop eg g maskYF b
  | 2 => chkAnyPermLt g pi pj
  | w3 + 3 => chkCutKillsWit (chkGetCutState hStates (Nat.div w3 8)) (Nat.land w3 7) g

def chkPairsStabInner (maskYF : Nat) (b : List Nat) (hStates : List ChkCutState)
    (surv : List Nat) (oi egi lim : Nat) (pi : List Nat) : List (Nat × Nat × Nat × List Nat) → List Nat → Option (List Nat)
  | [], wits => some wits
  | (oj, egj, _, pj) :: rest, wits =>
    let eij := Nat.land egi egj
    match Nat.beq eij egi with
    | true => chkPairsStabInner maskYF b hStates surv oi egi lim pi rest wits
    | false =>
      match Nat.beq eij egj with
      | true => chkPairsStabInner maskYF b hStates surv oi egi lim pi rest wits
      | false =>
        let g := Nat.lor oi oj
        let skipLex := match Nat.beq lim 0 with | true => false | false => Nat.blt g lim
        match skipLex with
        | true => chkPairsStabInner maskYF b hStates surv oi egi lim pi rest wits
        | false =>
          match wits with
          | [] => none
          | w :: ws =>
            match chkCheckWitStab maskYF b hStates surv (Nat.lor egi egj) g pi pj w with
            | true => chkPairsStabInner maskYF b hStates surv oi egi lim pi rest ws
            | false => none

def chkPairsStabOuter (maskYF : Nat) (b : List Nat) (hStates : List ChkCutState)
    (surv smax : List Nat) : List (Nat × Nat × Nat × List Nat) → List Nat → Bool
  | [], _ => true
  | (oi, egi, bi, pi) :: rest, wits =>
    let lim := chkGetNat smax bi
    match chkPairsStabInner maskYF b hStates surv oi egi lim pi rest wits with
    | some wits' => chkPairsStabOuter maskYF b hStates surv smax rest wits'
    | none => false

def chkCertListGates : CertList → List Nat
  | .nil => []
  | .cons g _ rest => g :: chkCertListGates rest

def chkComputeMd (edgeTT acc : Nat) : List Nat → Nat
  | [] => acc
  | x :: rest =>
    match Nat.beq (Nat.land edgeTT x) edgeTT with
    | true => chkComputeMd edgeTT (Nat.land acc x) rest
    | false => chkComputeMd edgeTT acc rest

def chkFilterGoodOps (bad : Nat) : List (Nat × Nat × Nat) → List Nat
  | [] => []
  | (op, _, _) :: rest =>
    match Nat.beq (Nat.land op bad) 0 with
    | true => op :: chkFilterGoodOps bad rest
    | false => chkFilterGoodOps bad rest

def chkNoCovInner (edgePtsMask a : Nat) : List Nat → Bool
  | [] => true
  | b :: rest =>
    match Nat.beq (Nat.land (Nat.lor a b) edgePtsMask) edgePtsMask with
    | true => false
    | false => chkNoCovInner edgePtsMask a rest

def chkNoCovOuter (edgePtsMask : Nat) : List Nat → Bool
  | [] => true
  | a :: rest =>
    match chkNoCovInner edgePtsMask a rest with
    | true => chkNoCovOuter edgePtsMask rest
    | false => false

def chkCheckTermMd (maskYF edgePtsMask edgeTT : Nat) (raw masksTT gs : List Nat) : Bool :=
  let b := raw ++ gs
  let md := chkComputeMd edgeTT maskYF b
  match Nat.beq md edgeTT with
  | true => false
  | false =>
    let bad := Nat.xor md edgeTT
    let ops := chkGenBirthOps maskYF edgePtsMask masksTT gs
    let good := chkFilterGoodOps bad ops
    chkNoCovOuter edgePtsMask good

def chkCheckLayer (maskYF edgePtsMask edgeTT : Nat) (raw masksTT : List Nat) (cuts : List CutDefData)
    (gs : List Nat) (stab : List (List Nat)) (hints wits surv : List Nat) : Bool :=
  let b := raw ++ gs
  match chkIsMeet maskYF b edgeTT with
  | true => false
  | false =>
    let hStates := chkPrepHints cuts gs hints
    let ops := chkGenBirthOps maskYF edgePtsMask masksTT gs
    let smax := chkBuildSuffixMax gs
    match stab with
    | [] => chkPairsNoStabOuter maskYF b hStates surv smax ops wits
    | _ :: _ =>
      let pops := chkAttachPerms stab ops
      chkPairsStabOuter maskYF b hStates surv smax pops wits

def chkMkAutIdxLoop (perm : List Nat) : Nat → List Nat
  | 0 => [0]
  | k + 1 =>
    let prev := chkMkAutIdxLoop perm k
    let bit := Nat.pow 2 (chkGetNat perm k)
    prev ++ prev.map (fun s => Nat.lor s bit)

def chkMkAutIdxTbls (n : Nat) (perms : List (List Nat)) : List (List Nat) :=
  perms.map (fun p => chkMkAutIdxLoop p n)

def chkMkAutMaskTbls (idxTbls : List (List Nat)) : List (List Nat) :=
  idxTbls.map (fun tbl => tbl.map (fun s => Nat.pow 2 s))

mutual
  def chkCheckNode (maskYF edgePtsMask edgeTT : Nat) (raw masksTT : List Nat) (cuts : List CutDefData)
      (gs : List Nat) (stab : List (List Nat)) : CertNode → Bool
    | .term => chkCheckTermMd maskYF edgePtsMask edgeTT raw masksTT gs
    | .branch hints witsChunks children =>
      match chkCheckLayer maskYF edgePtsMask edgeTT raw masksTT cuts gs stab hints (chkFlatten witsChunks) (chkCertListGates children) with
      | true => chkCheckChildren maskYF edgePtsMask edgeTT raw masksTT cuts gs stab children
      | false => false

  def chkCheckChildren (maskYF edgePtsMask edgeTT : Nat) (raw masksTT : List Nat) (cuts : List CutDefData)
      (gs : List Nat) (stab : List (List Nat)) : CertList → Bool
    | .nil => true
    | .cons g ch rest =>
      match chkCheckNode maskYF edgePtsMask edgeTT raw masksTT cuts (gs ++ [g]) (chkFilterStab g stab) ch with
      | true => chkCheckChildren maskYF edgePtsMask edgeTT raw masksTT cuts gs stab rest
      | false => false
end

mutual
  def certDepthOk (maxD d : ℕ) : CertNode → Bool
    | .term => Nat.ble maxD d
    | .branch _ _ ch => certListDepthOk maxD (d + 1) ch

  def certListDepthOk (maxD d : ℕ) : CertList → Bool
    | .nil => true
    | .cons _ ch rest => certDepthOk maxD d ch && certListDepthOk maxD d rest
end



theorem chkMemNat_iff (x : ℕ) (l : List ℕ) : chkMemNat x l = true ↔ x ∈ l := by
  induction l with
  | nil => simp [chkMemNat]
  | cons y rest ih =>
    simp only [chkMemNat, List.mem_cons]
    cases h : Nat.beq x y
    · simp [ih, (nat_beq_eq_false_iff x y).mp h]
    · simp [Nat.eq_of_beq_eq_true h]

theorem chkIsMeetLoop_eq (target acc : ℕ) (bs : List ℕ) (hsub : target &&& acc = target) :
    chkIsMeetLoop target acc bs = Nat.beq (isMeetLoop target bs acc) target := by
  induction bs generalizing acc with
  | nil => rfl
  | cons b rest ih =>
    simp only [chkIsMeetLoop, isMeetLoop]
    cases hb : Nat.beq (Nat.land target b) target
    · exact ih acc hsub
    · have hb' : target &&& b = target := by simpa [land_eq] using Nat.eq_of_beq_eq_true hb
      have hsub' : target &&& (acc &&& b) = target := by rw [← Nat.and_assoc, hsub, hb']
      dsimp only
      cases heq : Nat.beq (Nat.land acc b) target
      · exact ih (Nat.land acc b) hsub'
      · have hacc' : acc &&& b = target := by simpa [land_eq] using Nat.eq_of_beq_eq_true heq
        have h1 : isMeetLoop target rest (acc &&& b) &&& target = isMeetLoop target rest (acc &&& b) := by
          simpa [hacc'] using isMeetLoop_and_sub (target := target) rest (acc &&& b)
        have h2 : target &&& isMeetLoop target rest (acc &&& b) = target :=
          isMeetLoop_target_sub rest hsub'
        have h3 : isMeetLoop target rest (acc &&& b) = target := by
          rw [← h1, Nat.and_comm, h2]
        simp [h3]

theorem chkIsMeet_eq_isMeet {M t : ℕ} (B : List ℕ) (ht : t &&& M = t) :
    chkIsMeet M B t = isMeet M B t := by
  unfold chkIsMeet isMeet
  cases Nat.beq t 0
  · exact chkIsMeetLoop_eq t M B ht
  · rfl

theorem chkIsOnEdgesLoop_sound (eg g acc : ℕ) (bs : List ℕ)
    (hok : chkIsOnEdgesLoop eg g acc bs = true) :
    isMeetLoop eg bs acc &&& g = isMeetLoop eg bs acc := by
  induction bs generalizing acc with
  | nil =>
    simpa [chkIsOnEdgesLoop, isMeetLoop, land_eq] using Nat.eq_of_beq_eq_true hok
  | cons b rest ih =>
    simp only [chkIsOnEdgesLoop, isMeetLoop] at hok ⊢
    cases hb : Nat.beq (Nat.land eg b) eg
    · rw [hb] at hok; exact ih acc hok
    · rw [hb] at hok
      dsimp only at hok
      cases h1 : Nat.beq (Nat.land (Nat.land acc b) g) (Nat.land acc b)
      · rw [h1] at hok; exact ih (Nat.land acc b) hok
      · have hag : (acc &&& b) &&& g = acc &&& b := by
          simpa [land_eq] using Nat.eq_of_beq_eq_true h1
        have hsub := isMeetLoop_and_sub (target := eg) rest (acc &&& b)
        apply Nat.eq_of_testBit_eq; intro s
        have ha1 := congrArg (fun z => z.testBit s) hsub
        have ha2 := congrArg (fun z => z.testBit s) hag
        simp only [land_eq, Nat.testBit_and] at ha1 ha2 ⊢
        revert ha1 ha2
        cases (isMeetLoop eg rest (acc &&& b)).testBit s <;>
          cases acc.testBit s <;> cases b.testBit s <;> cases g.testBit s <;> decide

theorem chkProbeOkGate_eq (mc pm h : ℕ) : chkProbeOkGate mc pm h = probeOkGate mc pm h := rfl

theorem chkAllProbeOk_iff (mc pm : ℕ) (act : List ℕ) :
    chkAllProbeOk mc pm act = true ↔ act.all (probeOkGate mc pm) = true := by
  induction act with
  | nil => simp [chkAllProbeOk]
  | cons h rest ih =>
    simp only [chkAllProbeOk, List.all_cons, chkProbeOkGate_eq]
    cases probeOkGate mc pm h <;> simp [ih]

theorem chkFilterPv_mem (mc : ℕ) (act pv : List ℕ) (pm : ℕ) :
    pm ∈ chkFilterPv mc act pv ↔ pm ∈ pv ∧ act.all (probeOkGate mc pm) = true := by
  induction pv with
  | nil => simp [chkFilterPv]
  | cons p rest ih =>
    simp only [chkFilterPv, List.mem_cons]
    cases hp : chkAllProbeOk mc p act
    · have hp' : ¬ act.all (probeOkGate mc p) = true := by
        rw [← chkAllProbeOk_iff]; simp [hp]
      simp only [ih]
      constructor
      · rintro ⟨hmem, hall⟩; exact ⟨Or.inr hmem, hall⟩
      · rintro ⟨rfl | hmem, hall⟩
        · exact (hp' hall).elim
        · exact ⟨hmem, hall⟩
    · have hp' : act.all (probeOkGate mc p) = true := (chkAllProbeOk_iff mc p act).mp hp
      simp only [List.mem_cons, ih]
      constructor
      · rintro (rfl | ⟨hmem, hall⟩)
        · exact ⟨Or.inl rfl, hp'⟩
        · exact ⟨Or.inr hmem, hall⟩
      · rintro ⟨rfl | hmem, hall⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨hmem, hall⟩

theorem chkAnyProbeOk_iff (mc g : ℕ) (vp : List ℕ) :
    chkAnyProbeOk mc g vp = true ↔ ∃ pm ∈ vp, probeOkGate mc pm g = true := by
  induction vp with
  | nil => simp [chkAnyProbeOk]
  | cons pm rest ih =>
    simp only [chkAnyProbeOk, chkProbeOkGate_eq, List.mem_cons]
    cases hp : probeOkGate mc pm g
    · simp only [ih]
      constructor
      · rintro ⟨p, hmem, hok⟩; exact ⟨p, Or.inr hmem, hok⟩
      · rintro ⟨p, rfl | hmem, hok⟩
        · simp [hp] at hok
        · exact ⟨p, hmem, hok⟩
    · simp only [true_iff]; exact ⟨pm, Or.inl rfl, hp⟩

theorem chkAnyProbeOk_filterPv_iff (mc g : ℕ) (act pv : List ℕ) :
    chkAnyProbeOk mc g (chkFilterPv mc act pv) = true ↔
      pv.any (fun pm => (act ++ [g]).all (probeOkGate mc pm)) = true := by
  rw [chkAnyProbeOk_iff, List.any_eq_true]
  constructor
  · rintro ⟨pm, hmem, hg⟩
    obtain ⟨hpv, hact⟩ := (chkFilterPv_mem mc act pv pm).mp hmem
    exact ⟨pm, hpv, by simp [hact, hg]⟩
  · rintro ⟨pm, hpv, hall⟩
    simp only [List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hall
    exact ⟨pm, (chkFilterPv_mem mc act pv pm).mpr ⟨hpv, hall.1⟩, hall.2⟩

theorem chkStepFilterAct_eq (mc : ℕ) (act sb : List ℕ) (sv : ℕ) (actRev : List ℕ) :
    chkStepFilterAct mc act sb sv actRev =
      let r := evalCutStep.go mc act sb actRev sv
      (r.1, r.2.2, r.2.1) := by
  induction act generalizing sb sv actRev with
  | nil => rfl
  | cons h rest ih =>
    simp only [chkStepFilterAct, evalCutStep.go]
    have hrh : (Nat.land h mc) &&& mc = Nat.land h mc := by
      apply Nat.eq_of_testBit_eq; intro s; simp [Nat.testBit_and]
    rw [chkIsMeet_eq_isMeet sb hrh]
    cases isMeet mc sb (Nat.land h mc)
    · exact ih (Nat.land h mc :: sb) sv (Nat.land h mc :: actRev)
    · exact ih sb (sv + 1) actRev

theorem evalCutStep_go_sv_add (mc : ℕ) (act sb actRev : List ℕ) (sv k : ℕ) :
    evalCutStep.go mc act sb actRev (sv + k) =
      let r := evalCutStep.go mc act sb actRev sv
      (r.1, r.2.1, r.2.2 + k) := by
  induction act generalizing sb actRev sv with
  | nil => rfl
  | cons h rest ih =>
    simp only [evalCutStep.go]
    cases isMeet mc sb (Nat.land h mc)
    · exact ih (Nat.land h mc :: sb) (Nat.land h mc :: actRev) sv
    · rw [show sv + k + 1 = (sv + 1) + k by omega]
      exact ih sb actRev (sv + 1)

theorem evalCutStep_go_append_singleton (mc : ℕ) (act sb actRev : List ℕ) (sv g : ℕ) :
    evalCutStep.go mc (act ++ [g]) sb actRev sv =
      let r := evalCutStep.go mc act sb actRev sv
      let rg := Nat.land g mc
      match isMeet mc r.1 rg with
      | true => (r.1, r.2.1, r.2.2 + 1)
      | false => (rg :: r.1, r.2.1 ++ [rg], r.2.2) := by
  induction act generalizing sb actRev sv with
  | nil =>
    simp only [List.nil_append, evalCutStep.go]
    cases isMeet mc sb (Nat.land g mc) <;> simp
  | cons h rest ih =>
    simp only [List.cons_append, evalCutStep.go]
    cases isMeet mc sb (Nat.land h mc)
    · exact ih (Nat.land h mc :: sb) (Nat.land h mc :: actRev) sv
    · exact ih sb actRev (sv + 1)

theorem chkPrepSteps_sv_add (steps : List CutStepData) (act : List ℕ) (sv k : ℕ) :
    chkPrepSteps steps act (sv + k) =
      let r := chkPrepSteps steps act sv
      (r.1 + k, r.2.1, r.2.2) := by
  induction steps generalizing act sv with
  | nil => rfl
  | cons st rest ih =>
    simp only [chkPrepSteps, chkStepFilterAct_eq]
    have h1 := evalCutStep_go_sv_add st.mc act st.rc [] sv k
    simp only [h1]
    rw [ih (evalCutStep.go st.mc act st.rc [] sv).2.1 (evalCutStep.go st.mc act st.rc [] sv).2.2]

theorem chkPrepSteps_eval_eq (steps : List CutStepData) (act : List ℕ) :
    evalCutChain steps act = (chkPrepSteps steps act 0).1 + (chkPrepSteps steps act 0).2.1 := by
  induction steps generalizing act with
  | nil => simp [evalCutChain, chkPrepSteps]
  | cons st rest ih =>
    simp only [evalCutChain, chkPrepSteps, chkStepFilterAct_eq]
    set r := evalCutStep.go st.mc act st.rc [] 0
    have hshift : (chkPrepSteps rest r.2.1 r.2.2).1 = (chkPrepSteps rest r.2.1 0).1 + r.2.2 ∧
        (chkPrepSteps rest r.2.1 r.2.2).2.1 = (chkPrepSteps rest r.2.1 0).2.1 := by
      have h := chkPrepSteps_sv_add rest r.2.1 0 r.2.2
      simp only [zero_add] at h
      rw [h]; exact ⟨rfl, rfl⟩
    have hmyB : (if st.pv.any (fun pm => act.all (probeOkGate st.mc pm)) then 1 else 0) =
        match chkFilterPv st.mc act st.pv with | [] => 0 | _ :: _ => 1 := by
      cases hfp : chkFilterPv st.mc act st.pv
      · simp only [ite_eq_right_iff, Nat.one_ne_zero]
        intro hany
        rw [List.any_eq_true] at hany
        obtain ⟨pm, hpm, hall⟩ := hany
        have hmem : pm ∈ chkFilterPv st.mc act st.pv := (chkFilterPv_mem st.mc act st.pv pm).mpr ⟨hpm, hall⟩
        rw [hfp] at hmem; simp at hmem
      · rename_i pm _
        have hmem : pm ∈ chkFilterPv st.mc act st.pv := by rw [hfp]; simp
        obtain ⟨hpv, hall⟩ := (chkFilterPv_mem st.mc act st.pv pm).mp hmem
        have hany : st.pv.any (fun pm => act.all (probeOkGate st.mc pm)) = true :=
          List.any_eq_true.mpr ⟨pm, hpv, hall⟩
        simp [hany]
    have ih' := ih r.2.1
    change r.2.2 + (if st.pv.any (fun pm => act.all (probeOkGate st.mc pm)) then 1 else 0) +
      evalCutChain rest r.2.1 = _
    rw [hmyB, ih', hshift.1, hshift.2]
    omega

theorem evalCutChain_append_ge_totSv (steps : List CutStepData) (act : List ℕ) (g : ℕ) :
    (chkPrepSteps steps act 0).1 ≤ evalCutChain steps (act ++ [g]) := by
  induction steps generalizing act g with
  | nil => simp [chkPrepSteps, evalCutChain]
  | cons st rest ih =>
    simp only [evalCutChain, chkPrepSteps, chkStepFilterAct_eq]
    have hshift : (chkPrepSteps rest (evalCutStep.go st.mc act st.rc [] 0).2.1
        (evalCutStep.go st.mc act st.rc [] 0).2.2).1 =
        (chkPrepSteps rest (evalCutStep.go st.mc act st.rc [] 0).2.1 0).1 +
        (evalCutStep.go st.mc act st.rc [] 0).2.2 := by
      have h := chkPrepSteps_sv_add rest (evalCutStep.go st.mc act st.rc [] 0).2.1 0
        (evalCutStep.go st.mc act st.rc [] 0).2.2
      simp only [zero_add] at h
      rw [h]
    have hstep := evalCutStep_go_append_singleton st.mc act st.rc [] 0 g
    change _ ≤ (evalCutStep.go st.mc (act ++ [g]) st.rc [] 0).2.2 +
      (if st.pv.any (fun pm => (act ++ [g]).all (probeOkGate st.mc pm)) then 1 else 0) +
      evalCutChain rest (evalCutStep.go st.mc (act ++ [g]) st.rc [] 0).2.1
    rw [hstep, hshift]
    dsimp only
    cases hm : isMeet st.mc (evalCutStep.go st.mc act st.rc [] 0).1 (Nat.land g st.mc)
    · dsimp only
      have hrec := ih (evalCutStep.go st.mc act st.rc [] 0).2.1 (Nat.land g st.mc)
      omega
    · dsimp only
      have heq := chkPrepSteps_eval_eq rest (evalCutStep.go st.mc act st.rc [] 0).2.1
      omega

theorem chkCutKillsAtStep_le_one_add_allB (steps : List CutStepData) (act : List ℕ)
    (g need stepIdx : ℕ)
    (hok : chkCutKillsAtStep g need stepIdx (chkPrepSteps steps act 0).2.2 = true) :
    need ≤ 1 + (chkPrepSteps steps act 0).2.1 := by
  induction steps generalizing act g need stepIdx with
  | nil =>
    simp only [chkPrepSteps, chkCutKillsAtStep] at hok ⊢
    have h0 : need = 0 := Nat.eq_of_beq_eq_true hok
    omega
  | cons st rest ih =>
    simp only [chkPrepSteps, chkStepFilterAct_eq] at hok ⊢
    set r := evalCutStep.go st.mc act st.rc [] 0
    have hshift : (chkPrepSteps rest r.2.1 r.2.2).2.1 = (chkPrepSteps rest r.2.1 0).2.1 ∧
        (chkPrepSteps rest r.2.1 r.2.2).2.2 = (chkPrepSteps rest r.2.1 0).2.2 := by
      have h := chkPrepSteps_sv_add rest r.2.1 0 r.2.2
      simp only [zero_add] at h
      rw [h]; exact ⟨rfl, rfl⟩
    rw [hshift.1] at hok ⊢
    rw [hshift.2] at hok
    cases stepIdx with
    | zero =>
      simp only [chkCutKillsAtStep] at hok
      cases hm : chkIsMeet st.mc r.1 (Nat.land g st.mc)
      · rw [hm] at hok; simp at hok
      · rw [hm] at hok
        cases h1 : Nat.ble need (1 + (chkPrepSteps rest r.2.1 0).2.1)
        · rw [h1] at hok
          cases h2 : Nat.ble need (2 + (chkPrepSteps rest r.2.1 0).2.1)
          · rw [h2] at hok; simp at hok
          · rw [h2] at hok
            have hle : need ≤ 2 + (chkPrepSteps rest r.2.1 0).2.1 := Nat.le_of_ble_eq_true h2
            cases hvp : chkFilterPv st.mc act st.pv
            · rw [hvp] at hok; simp [chkAnyProbeOk] at hok
            · dsimp only; omega
        · have hle : need ≤ 1 + (chkPrepSteps rest r.2.1 0).2.1 := Nat.le_of_ble_eq_true h1
          cases chkFilterPv st.mc act st.pv <;> dsimp only <;> omega
    | succ s' =>
      simp only [chkCutKillsAtStep] at hok
      cases hvp : chkFilterPv st.mc act st.pv
      · rw [hvp] at hok; dsimp only at hok ⊢
        cases h0 : Nat.beq need 0
        · rw [h0] at hok
          have := ih r.2.1 (Nat.land g st.mc) need s' hok
          omega
        · have := Nat.eq_of_beq_eq_true h0; omega
      · rw [hvp] at hok; dsimp only at hok ⊢
        cases hp : chkAnyProbeOk st.mc g (chkFilterPv st.mc act st.pv)
        · rw [hvp] at hp; rw [hp] at hok; dsimp only at hok
          cases h0 : Nat.beq need 0
          · rw [h0] at hok
            have := ih r.2.1 (Nat.land g st.mc) need s' hok
            omega
          · have := Nat.eq_of_beq_eq_true h0; omega
        · rw [hvp] at hp; rw [hp] at hok; dsimp only at hok
          cases h0 : Nat.beq (Nat.sub need 1) 0
          · rw [h0] at hok
            have := ih r.2.1 (Nat.land g st.mc) (Nat.sub need 1) s' hok
            rw [nat_sub_eq] at this; omega
          · have := Nat.eq_of_beq_eq_true h0; rw [nat_sub_eq] at this; omega

theorem chkCutKillsAtStep_sound (steps : List CutStepData) (act : List ℕ)
    (g need stepIdx : ℕ)
    (hok : chkCutKillsAtStep g need stepIdx (chkPrepSteps steps act 0).2.2 = true) :
    (chkPrepSteps steps act 0).1 + need ≤ evalCutChain steps (act ++ [g]) := by
  induction steps generalizing act g need stepIdx with
  | nil =>
    simp only [chkPrepSteps, chkCutKillsAtStep, evalCutChain] at hok ⊢
    have := Nat.eq_of_beq_eq_true hok; omega
  | cons st rest ih =>
    simp only [evalCutChain, chkPrepSteps, chkStepFilterAct_eq] at hok ⊢
    have hshift : (chkPrepSteps rest (evalCutStep.go st.mc act st.rc [] 0).2.1
          (evalCutStep.go st.mc act st.rc [] 0).2.2).1 =
        (chkPrepSteps rest (evalCutStep.go st.mc act st.rc [] 0).2.1 0).1 +
          (evalCutStep.go st.mc act st.rc [] 0).2.2 ∧
      (chkPrepSteps rest (evalCutStep.go st.mc act st.rc [] 0).2.1
          (evalCutStep.go st.mc act st.rc [] 0).2.2).2.1 =
        (chkPrepSteps rest (evalCutStep.go st.mc act st.rc [] 0).2.1 0).2.1 ∧
      (chkPrepSteps rest (evalCutStep.go st.mc act st.rc [] 0).2.1
          (evalCutStep.go st.mc act st.rc [] 0).2.2).2.2 =
        (chkPrepSteps rest (evalCutStep.go st.mc act st.rc [] 0).2.1 0).2.2 := by
      have h := chkPrepSteps_sv_add rest (evalCutStep.go st.mc act st.rc [] 0).2.1 0
        (evalCutStep.go st.mc act st.rc [] 0).2.2
      simp only [zero_add] at h
      rw [h]; exact ⟨rfl, rfl, rfl⟩
    rw [hshift.1]
    rw [hshift.2.1, hshift.2.2] at hok
    have hstep := evalCutStep_go_append_singleton st.mc act st.rc [] 0 g
    change _ ≤ (evalCutStep.go st.mc (act ++ [g]) st.rc [] 0).2.2 +
      (if st.pv.any (fun pm => (act ++ [g]).all (probeOkGate st.mc pm)) then 1 else 0) +
      evalCutChain rest (evalCutStep.go st.mc (act ++ [g]) st.rc [] 0).2.1
    rw [hstep]
    set r := evalCutStep.go st.mc act st.rc [] 0
    have hrgM : Nat.land g st.mc &&& st.mc = Nat.land g st.mc := by
      apply Nat.eq_of_testBit_eq; intro s; simp [Nat.testBit_and]
    have hmeet_eq : chkIsMeet st.mc r.1 (Nat.land g st.mc) = isMeet st.mc r.1 (Nat.land g st.mc) :=
      chkIsMeet_eq_isMeet r.1 hrgM
    have hprobe_eq : (st.pv.any (fun pm => (act ++ [g]).all (probeOkGate st.mc pm))) =
        chkAnyProbeOk st.mc g (chkFilterPv st.mc act st.pv) := by
      apply Bool.eq_iff_iff.mpr
      exact (chkAnyProbeOk_filterPv_iff st.mc g act st.pv).symm
    rw [hprobe_eq]
    dsimp only
    cases hm : isMeet st.mc r.1 (Nat.land g st.mc)
    · -- `g` survives step `st`
      dsimp only
      cases stepIdx with
      | zero =>
        simp only [chkCutKillsAtStep, hmeet_eq, hm] at hok
        simp at hok
      | succ s' =>
        simp only [chkCutKillsAtStep] at hok
        have hge := evalCutChain_append_ge_totSv rest r.2.1 (Nat.land g st.mc)
        cases hvp : chkFilterPv st.mc act st.pv
        · rw [hvp] at hok; simp only at hok
          cases h0 : Nat.beq need 0
          · rw [h0] at hok; simp only at hok
            have hrec := ih r.2.1 (Nat.land g st.mc) need s' hok
            omega
          · have := Nat.eq_of_beq_eq_true h0; omega
        · rw [hvp] at hok; simp only at hok
          cases hp : chkAnyProbeOk st.mc g (_ :: _)
          · rw [hp] at hok; simp only at hok
            cases h0 : Nat.beq need 0
            · rw [h0] at hok; simp only at hok
              have hrec := ih r.2.1 (Nat.land g st.mc) need s' hok
              omega
            · have := Nat.eq_of_beq_eq_true h0; omega
          · rw [hp] at hok; simp only at hok
            simp only [↓reduceIte]
            cases h0 : Nat.beq (Nat.sub need 1) 0
            · rw [h0] at hok; simp only at hok
              have hrec := ih r.2.1 (Nat.land g st.mc) (Nat.sub need 1) s' hok
              rw [nat_sub_eq] at hrec; omega
            · have := Nat.eq_of_beq_eq_true h0; rw [nat_sub_eq] at this; omega
    · -- `g` is dropped as `isMeet` at step `st`
      dsimp only
      have hrest_eq := chkPrepSteps_eval_eq rest r.2.1
      rw [hrest_eq]
      cases stepIdx with
      | zero =>
        simp only [chkCutKillsAtStep, hmeet_eq, hm] at hok
        cases h1 : Nat.ble need (1 + (chkPrepSteps rest r.2.1 0).2.1)
        · rw [h1] at hok
          cases h2 : Nat.ble need (2 + (chkPrepSteps rest r.2.1 0).2.1)
          · rw [h2] at hok; simp at hok
          · rw [h2] at hok; simp only at hok
            have hle := Nat.le_of_ble_eq_true h2
            rw [hok]; simp only [↓reduceIte]; omega
        · have hle := Nat.le_of_ble_eq_true h1
          split_ifs <;> omega
      | succ s' =>
        simp only [chkCutKillsAtStep] at hok
        cases hvp : chkFilterPv st.mc act st.pv
        · rw [hvp] at hok; simp only at hok
          cases h0 : Nat.beq need 0
          · rw [h0] at hok; simp only at hok
            have hle := chkCutKillsAtStep_le_one_add_allB rest r.2.1 (Nat.land g st.mc) need s' hok
            simp [chkAnyProbeOk]; omega
          · have := Nat.eq_of_beq_eq_true h0; omega
        · rw [hvp] at hok; simp only at hok
          cases hp : chkAnyProbeOk st.mc g (_ :: _)
          · rw [hp] at hok; simp only at hok
            cases h0 : Nat.beq need 0
            · rw [h0] at hok; simp only at hok
              have hle := chkCutKillsAtStep_le_one_add_allB rest r.2.1 (Nat.land g st.mc) need s' hok
              omega
            · have := Nat.eq_of_beq_eq_true h0; omega
          · rw [hp] at hok; simp only at hok
            simp only [↓reduceIte]
            cases h0 : Nat.beq (Nat.sub need 1) 0
            · rw [h0] at hok; simp only at hok
              have hle := chkCutKillsAtStep_le_one_add_allB rest r.2.1 (Nat.land g st.mc) (Nat.sub need 1) s' hok
              rw [nat_sub_eq] at hle; omega
            · have := Nat.eq_of_beq_eq_true h0; rw [nat_sub_eq] at this; omega

theorem chkCutKillsWit_sound (cut : CutDefData) (gs : List ℕ) (stepIdx g : ℕ)
    (hok : chkCutKillsWit (chkPrepCutState cut gs) stepIdx g = true) :
    cut.loss ≤ evalCutChain cut.steps (gs ++ [g]) := by
  unfold chkCutKillsWit chkPrepCutState at hok
  dsimp only at hok
  cases h0 : Nat.beq (Nat.sub cut.loss (chkPrepSteps cut.steps gs 0).1) 0
  · rw [h0] at hok
    have h1 := chkCutKillsAtStep_sound cut.steps gs g _ stepIdx hok
    rw [nat_sub_eq] at h1; omega
  · have hle : cut.loss ≤ (chkPrepSteps cut.steps gs 0).1 := by
      have := Nat.eq_of_beq_eq_true h0; rw [nat_sub_eq] at this; omega
    exact hle.trans (evalCutChain_append_ge_totSv cut.steps gs g)

theorem chkApplyPermLoop_eq (tbl : List ℕ) (f s acc : ℕ) :
    chkApplyPermLoop (f / 2 ^ s) acc (tbl.map (fun x => Nat.pow 2 x)) =
      applyPermLoop tbl f s acc := by
  induction tbl generalizing s acc with
  | nil => rfl
  | cons s2 rest ih =>
    simp only [List.map_cons, chkApplyPermLoop, applyPermLoop]
    cases h0 : Nat.beq (f / 2 ^ s) 0
    · have hbit : Nat.beq (Nat.land (f / 2 ^ s) 1) 1 = f.testBit s := by
        rw [Nat.testBit, Nat.shiftRight_eq_div_pow, land_eq, Nat.and_comm 1 _, Nat.and_one_is_mod]
        have hlt : (f / 2 ^ s) % 2 < 2 := Nat.mod_lt _ (by omega)
        generalize (f / 2 ^ s) % 2 = m at hlt ⊢
        interval_cases m <;> rfl
      have hpow : Nat.pow 2 s2 = 1 <<< s2 := by rw [Nat.shiftLeft_eq, one_mul]; rfl
      have hdiv : Nat.div (f / 2 ^ s) 2 = f / 2 ^ (s + 1) := by
        rw [nat_div_eq, Nat.div_div_eq_div_mul, Nat.pow_succ]
      rw [hbit, hpow, hdiv]
      cases f.testBit s
      · exact ih (s + 1) acc
      · exact ih (s + 1) (Nat.lor acc (1 <<< s2))
    · have hf0 : f / 2 ^ s = 0 := Nat.eq_of_beq_eq_true h0
      have hzero : ∀ (l : List ℕ) (t a : ℕ), f / 2 ^ t = 0 → applyPermLoop l f t a = a := by
        intro l
        induction l with
        | nil => intro _ _ _; rfl
        | cons x xs ihx =>
          intro t a ht
          simp only [applyPermLoop]
          have htb : f.testBit t = false := by
            rw [Nat.testBit, Nat.shiftRight_eq_div_pow, ht]; rfl
          have ht' : f / 2 ^ (t + 1) = 0 := by
            rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, ht]
          rw [htb]; exact ihx (t + 1) a ht'
      exact (hzero (s2 :: rest) s acc hf0).symm

theorem chkApplyPerm_eq_applyPerm (tbl : List ℕ) (f : ℕ) :
    chkApplyPerm (tbl.map (fun s => Nat.pow 2 s)) f = applyPerm tbl f := by
  simpa [chkApplyPerm, applyPerm] using chkApplyPermLoop_eq tbl f 0 0

theorem chkAnyPermLt_sound (idxTbls : List (List ℕ)) (oi oj : ℕ)
    (hok : chkAnyPermLt (oi ||| oj)
      (chkApplyPermList oi (chkMkAutMaskTbls idxTbls))
      (chkApplyPermList oj (chkMkAutMaskTbls idxTbls)) = true) :
    ∃ tbl ∈ idxTbls, applyPerm tbl (oi ||| oj) < oi ||| oj := by
  induction idxTbls with
  | nil => simp [chkMkAutMaskTbls, chkApplyPermList, chkAnyPermLt] at hok
  | cons tbl rest ih =>
    simp only [chkMkAutMaskTbls, List.map_cons, chkApplyPermList, chkAnyPermLt,
      chkApplyPerm_eq_applyPerm, lor_eq, ← applyPerm_or] at hok
    cases hlt : Nat.blt (applyPerm tbl (oi ||| oj)) (oi ||| oj)
    · rw [hlt] at hok
      obtain ⟨t, ht, h⟩ := ih hok
      exact ⟨t, List.mem_cons_of_mem _ ht, h⟩
    · exact ⟨tbl, List.mem_cons_self, nat_blt_eq_true hlt⟩

theorem chkFilterStab_map (g : ℕ) (idxTbls : List (List ℕ)) :
    chkFilterStab g (chkMkAutMaskTbls idxTbls) =
      chkMkAutMaskTbls (idxTbls.filter (fun tbl => Nat.beq (applyPerm tbl g) g)) := by
  induction idxTbls with
  | nil => rfl
  | cons tbl rest ih =>
    simp only [chkMkAutMaskTbls, List.map_cons, chkFilterStab, chkApplyPerm_eq_applyPerm,
      List.filter_cons]
    cases Nat.beq (applyPerm tbl g) g
    · exact ih
    · dsimp only [chkMkAutMaskTbls] at ih
      rw [ih]; rfl



theorem masksTTYF_meetNat {n : ℕ} {H F : List (ℕ × ℕ)} (hv : ValidState n H F) :
    ∀ mt ∈ masksTTYF n H (univYF n F),
      MeetNat (univYF n F) (rawYF n (univYF n F)) mt := by
  set M := univYF n F
  have hM : ∀ s, M.testBit s = true → s < 2 ^ n := fun _ => univYF_testBit_lt
  intro mt hmt
  unfold masksTTYF at hmt
  simp only [List.cons_append, List.mem_map, List.mem_cons, List.mem_append, List.mem_range] at hmt
  obtain ⟨m, hm, rfl⟩ := hmt
  refine meetNat_iff.mpr ⟨ttNeedYF_and_mask hM, ?_⟩
  rcases hm with rfl | ⟨v, hvlt, rfl⟩ | ⟨e, heH, rfl⟩
  · rw [ttNeedYF_zero hM, decM_self]; exact Meet.top
  · rw [ttNeedYF_oneBit hM]
    exact Meet.atom ⟨ttVarYF n v M, List.mem_map.mpr ⟨v, List.mem_range.mpr hvlt, rfl⟩, rfl⟩
  · obtain ⟨h1, h2, _⟩ := hv.1 e heH
    rw [← ttNeedYF_or hM, ttNeedYF_oneBit hM, ttNeedYF_oneBit hM, decM_and]
    exact (Meet.atom (B := decM M '' { x | x ∈ rawYF n M })
        ⟨ttVarYF n e.1 M, List.mem_map.mpr ⟨e.1, List.mem_range.mpr h1, rfl⟩, rfl⟩).inter
      (Meet.atom (B := decM M '' { x | x ∈ rawYF n M })
        ⟨ttVarYF n e.2 M, List.mem_map.mpr ⟨e.2, List.mem_range.mpr h2, rfl⟩, rfl⟩)

theorem chkSubsetsStep_mem (g : ℕ) (subs acc : List ℕ) (y : ℕ) :
    y ∈ chkSubsetsStep g subs acc ↔ y ∈ acc ∨ ∃ x ∈ subs, y = x &&& g := by
  induction subs generalizing acc with
  | nil => simp [chkSubsetsStep]
  | cons x rest ih =>
    simp only [chkSubsetsStep, ih, List.mem_cons, land_eq]
    constructor
    · rintro ((rfl | hy) | ⟨z, hz, rfl⟩)
      · exact Or.inr ⟨x, Or.inl rfl, rfl⟩
      · exact Or.inl hy
      · exact Or.inr ⟨z, Or.inr hz, rfl⟩
    · rintro (hy | ⟨z, rfl | hz, rfl⟩)
      · exact Or.inl (Or.inr hy)
      · exact Or.inl (Or.inl rfl)
      · exact Or.inr ⟨z, hz, rfl⟩

theorem chkAddBirthOps_inv {M ep gi birth : ℕ} {raw done : List ℕ}
    (hdone_len : birth = done.length)
    (hgi : MeetNat M (raw ++ done) gi)
    (masksTT : List ℕ) (hmasks : ∀ mt ∈ masksTT, MeetNat M raw mt)
    (seen : List ℕ) (acc : List (ℕ × ℕ × ℕ))
    (hacc_inv : ∀ x ∈ acc, x.2.1 = x.1 &&& ep ∧ x.2.2 ≤ birth ∧ MeetNat M (raw ++ done.take x.2.2) x.1)
    (hacc_pw : acc.Pairwise (fun x y => y.2.2 ≤ x.2.2))
    (hseen_acc : ∀ op ∈ seen, ∃ b, (op, op &&& ep, b) ∈ acc) :
    let res := chkAddBirthOps M ep gi birth masksTT seen acc
    (∀ x ∈ res.2, x.2.1 = x.1 &&& ep ∧ x.2.2 ≤ birth ∧ MeetNat M (raw ++ done.take x.2.2) x.1) ∧
    res.2.Pairwise (fun x y => y.2.2 ≤ x.2.2) ∧
    (∀ op ∈ seen, op ∈ res.1) ∧
    (∀ op ∈ res.1, ∃ b, (op, op &&& ep, b) ∈ res.2) ∧
    (∀ mt ∈ masksTT, (mt &&& gi) ≠ 0 → (mt &&& gi) ≠ M → (mt &&& gi) &&& ep ≠ 0 → (mt &&& gi) ∈ res.1) := by
  induction masksTT generalizing seen acc with
  | nil =>
    simp only [chkAddBirthOps, List.not_mem_nil, false_implies, implies_true, and_true]
    exact ⟨hacc_inv, hacc_pw, fun _ h => h, hseen_acc⟩
  | cons mt rest ih =>
    simp only [chkAddBirthOps, land_eq]
    have hmt : MeetNat M raw mt := hmasks mt List.mem_cons_self
    have hrest_m : ∀ m ∈ rest, MeetNat M raw m := fun m hm => hmasks m (List.mem_cons_of_mem _ hm)
    set op := mt &&& gi
    cases h0 : Nat.beq op 0
    · cases hM : Nat.beq op M
      · cases hep : Nat.beq (op &&& ep) 0
        · cases hmem : chkMemNat op seen
          · have hop_meet : MeetNat M (raw ++ done.take birth) op := by
              rw [hdone_len, List.take_length]
              have h1 : MeetNat M (raw ++ done) mt :=
                meetNat_weaken (fun x hx => List.mem_append_left _ hx) hmt
              have hsub : op &&& M = op := by
                apply Nat.eq_of_testBit_eq; intro s
                have ha := congrArg (fun z => z.testBit s) hmt.1
                simp only [op, Nat.testBit_and] at ha ⊢
                revert ha; cases mt.testBit s <;> cases gi.testBit s <;> cases M.testBit s <;> decide
              exact meetNat_iff.mpr ⟨hsub, by rw [decM_and]; exact (meetNat_iff.mp h1).2.inter (meetNat_iff.mp hgi).2⟩
            have hacc_inv' : ∀ x ∈ (op, op &&& ep, birth) :: acc,
                x.2.1 = x.1 &&& ep ∧ x.2.2 ≤ birth ∧ MeetNat M (raw ++ done.take x.2.2) x.1 := by
              intro x hx
              rcases List.mem_cons.mp hx with rfl | hx
              · exact ⟨rfl, le_rfl, hop_meet⟩
              · exact hacc_inv x hx
            have hacc_pw' : ((op, op &&& ep, birth) :: acc).Pairwise (fun x y => y.2.2 ≤ x.2.2) :=
              List.pairwise_cons.mpr ⟨fun y hy => (hacc_inv y hy).2.1, hacc_pw⟩
            have hseen_acc' : ∀ o ∈ op :: seen, ∃ b, (o, o &&& ep, b) ∈ (op, op &&& ep, birth) :: acc := by
              intro o ho
              rcases List.mem_cons.mp ho with rfl | ho
              · exact ⟨birth, List.mem_cons_self⟩
              · obtain ⟨b, hb⟩ := hseen_acc o ho
                exact ⟨b, List.mem_cons_of_mem _ hb⟩
            obtain ⟨i1, i2, i3, i4, i5⟩ := ih hrest_m (op :: seen) ((op, op &&& ep, birth) :: acc)
              hacc_inv' hacc_pw' hseen_acc'
            refine ⟨i1, i2, fun o ho => i3 o (List.mem_cons_of_mem _ ho), i4, fun m hm => ?_⟩
            rcases List.mem_cons.mp hm with rfl | hm
            · intro _ _ _; exact i3 op List.mem_cons_self
            · exact i5 m hm
          · obtain ⟨i1, i2, i3, i4, i5⟩ := ih hrest_m seen acc hacc_inv hacc_pw hseen_acc
            refine ⟨i1, i2, i3, i4, fun m hm => ?_⟩
            rcases List.mem_cons.mp hm with rfl | hm
            · intro _ _ _; exact i3 op ((chkMemNat_iff op seen).mp hmem)
            · exact i5 m hm
        · obtain ⟨i1, i2, i3, i4, i5⟩ := ih hrest_m seen acc hacc_inv hacc_pw hseen_acc
          refine ⟨i1, i2, i3, i4, fun m hm => ?_⟩
          rcases List.mem_cons.mp hm with rfl | hm
          · intro _ _ hne; exact (hne (Nat.eq_of_beq_eq_true hep)).elim
          · exact i5 m hm
      · obtain ⟨i1, i2, i3, i4, i5⟩ := ih hrest_m seen acc hacc_inv hacc_pw hseen_acc
        refine ⟨i1, i2, i3, i4, fun m hm => ?_⟩
        rcases List.mem_cons.mp hm with rfl | hm
        · intro _ hne _; exact (hne (Nat.eq_of_beq_eq_true hM)).elim
        · exact i5 m hm
    · obtain ⟨i1, i2, i3, i4, i5⟩ := ih hrest_m seen acc hacc_inv hacc_pw hseen_acc
      refine ⟨i1, i2, i3, i4, fun m hm => ?_⟩
      rcases List.mem_cons.mp hm with rfl | hm
      · intro hne _ _; exact (hne (Nat.eq_of_beq_eq_true h0)).elim
      · exact i5 m hm

theorem chkAddSubsOps_inv {M ep birth : ℕ} {raw done masksTT : List ℕ}
    (hdone_len : birth = done.length)
    (hmasks : ∀ mt ∈ masksTT, MeetNat M raw mt)
    (newSubs seen : List ℕ) (acc : List (ℕ × ℕ × ℕ))
    (hsubs : ∀ gi ∈ newSubs, MeetNat M (raw ++ done) gi)
    (hacc_inv : ∀ x ∈ acc, x.2.1 = x.1 &&& ep ∧ x.2.2 ≤ birth ∧ MeetNat M (raw ++ done.take x.2.2) x.1)
    (hacc_pw : acc.Pairwise (fun x y => y.2.2 ≤ x.2.2))
    (hseen_acc : ∀ op ∈ seen, ∃ b, (op, op &&& ep, b) ∈ acc) :
    let res := chkAddSubsOps M ep birth masksTT newSubs seen acc
    (∀ x ∈ res.2, x.2.1 = x.1 &&& ep ∧ x.2.2 ≤ birth ∧ MeetNat M (raw ++ done.take x.2.2) x.1) ∧
    res.2.Pairwise (fun x y => y.2.2 ≤ x.2.2) ∧
    (∀ op ∈ seen, op ∈ res.1) ∧
    (∀ op ∈ res.1, ∃ b, (op, op &&& ep, b) ∈ res.2) ∧
    (∀ gi ∈ newSubs, ∀ mt ∈ masksTT, (mt &&& gi) ≠ 0 → (mt &&& gi) ≠ M → (mt &&& gi) &&& ep ≠ 0 → (mt &&& gi) ∈ res.1) := by
  induction newSubs generalizing seen acc with
  | nil =>
    simp only [chkAddSubsOps, List.not_mem_nil, false_implies, implies_true, and_true]
    exact ⟨hacc_inv, hacc_pw, fun _ h => h, hseen_acc⟩
  | cons gi rest ih =>
    simp only [chkAddSubsOps]
    have h1 := chkAddBirthOps_inv hdone_len (hsubs gi List.mem_cons_self) masksTT hmasks seen acc
      hacc_inv hacc_pw hseen_acc
    set r1 := chkAddBirthOps M ep gi birth masksTT seen acc
    obtain ⟨i1, i2, i3, i4, i5⟩ := ih r1.1 r1.2
      (fun g hg => hsubs g (List.mem_cons_of_mem _ hg)) h1.1 h1.2.1 h1.2.2.2.1
    refine ⟨i1, i2, fun o ho => i3 o (h1.2.2.1 o ho), i4, fun g hg mt hmt h0 hM hep => ?_⟩
    rcases List.mem_cons.mp hg with rfl | hg
    · exact i3 (mt &&& g) (h1.2.2.2.2 mt hmt h0 hM hep)
    · exact i5 g hg mt hmt h0 hM hep

theorem sublist_append_singleton {α : Type} {P done : List α} {g : α}
    (h : List.Sublist P (done ++ [g])) :
    List.Sublist P done ∨ ∃ P', List.Sublist P' done ∧ P = P' ++ [g] := by
  induction done generalizing P with
  | nil =>
    simp only [List.nil_append] at h
    cases h with
    | cons _ h' => cases h'; exact Or.inl List.Sublist.slnil
    | cons_cons _ h' => cases h'; exact Or.inr ⟨[], List.Sublist.slnil, rfl⟩
  | cons x xs ih =>
    simp only [List.cons_append] at h
    cases h with
    | cons _ h' =>
      rcases ih h' with h1 | ⟨P', h1, rfl⟩
      · exact Or.inl (List.Sublist.cons x h1)
      · exact Or.inr ⟨P', List.Sublist.cons x h1, rfl⟩
    | cons_cons _ h' =>
      rcases ih h' with h1 | ⟨P', h1, rfl⟩
      · exact Or.inl (List.Sublist.cons_cons x h1)
      · exact Or.inr ⟨x :: P', List.Sublist.cons_cons x h1, rfl⟩

theorem chkGenBirthLoop_inv {M ep : ℕ} {raw masksTT : List ℕ}
    (hmasks : ∀ mt ∈ masksTT, MeetNat M raw mt) :
    ∀ (rest done subs seen : List ℕ) (acc : List (ℕ × ℕ × ℕ)),
      ValidPrefix M (raw ++ done) rest →
      (∀ gi ∈ subs, MeetNat M (raw ++ done) gi) →
      (∀ P : List ℕ, List.Sublist P done → P.foldl Nat.land M ∈ subs) →
      (∀ x ∈ acc, x.2.1 = x.1 &&& ep ∧ x.2.2 ≤ done.length ∧ MeetNat M (raw ++ done.take x.2.2) x.1) →
      acc.Pairwise (fun x y => y.2.2 ≤ x.2.2) →
      (∀ op ∈ seen, ∃ b, (op, op &&& ep, b) ∈ acc) →
      (∀ gi ∈ subs, ∀ mt ∈ masksTT, (mt &&& gi) ≠ 0 → (mt &&& gi) ≠ M → (mt &&& gi) &&& ep ≠ 0 → (mt &&& gi) ∈ seen) →
      let res := chkGenBirthLoop M ep masksTT (done.length + 1) subs seen acc rest
      (∀ x ∈ res, x.2.1 = x.1 &&& ep ∧ x.2.2 ≤ (done ++ rest).length ∧
        MeetNat M (raw ++ (done ++ rest).take x.2.2) x.1) ∧
      res.Pairwise (fun x y => y.2.2 ≤ x.2.2) ∧
      (∀ P : List ℕ, List.Sublist P (done ++ rest) → ∀ mt ∈ masksTT,
        (mt &&& P.foldl Nat.land M) ≠ 0 → (mt &&& P.foldl Nat.land M) ≠ M →
        (mt &&& P.foldl Nat.land M) &&& ep ≠ 0 →
        ∃ b, (mt &&& P.foldl Nat.land M, (mt &&& P.foldl Nat.land M) &&& ep, b) ∈ res) := by
  intro rest
  induction rest with
  | nil =>
    intro done subs seen acc _ _ hsub_P hacc_inv hacc_pw hseen_acc hseen_cov
    simp only [chkGenBirthLoop, List.append_nil]
    exact ⟨hacc_inv, hacc_pw, fun P hP mt hmt h0 hM hep =>
      hseen_acc _ (hseen_cov _ (hsub_P P hP) mt hmt h0 hM hep)⟩
  | cons g tail ih =>
    intro done subs seen acc hvp hsubs hsub_P hacc_inv hacc_pw hseen_acc hseen_cov
    rcases hvp with ⟨⟨a, b, ha, hb, hgab⟩, htail_vp⟩
    have hgM : g &&& M = g := hgab ▸ or_and_mask ha.1 hb.1
    set done' := done ++ [g]
    have hlen' : done'.length = done.length + 1 := by simp [done']
    have hraw_sub : ∀ z ∈ raw ++ done, z ∈ raw ++ done' := by
      intro z hz
      rcases List.mem_append.mp hz with hz | hz
      · exact List.mem_append_left _ hz
      · exact List.mem_append_right _ (List.mem_append_left _ hz)
    set newSubs := chkSubsetsStep g subs []
    have hnewSubs_meet : ∀ gi ∈ newSubs, MeetNat M (raw ++ done') gi := by
      intro gi hgi
      rw [chkSubsetsStep_mem] at hgi
      rcases hgi with hnil | ⟨x, hx, rfl⟩
      · simp at hnil
      · have hx' := meetNat_weaken hraw_sub (hsubs x hx)
        have hsub : (x &&& g) &&& M = x &&& g := by
          apply Nat.eq_of_testBit_eq; intro s
          have h1 := congrArg (fun z => z.testBit s) hgM
          simp only [Nat.testBit_and] at h1 ⊢
          revert h1; cases x.testBit s <;> cases g.testBit s <;> cases M.testBit s <;> decide
        have hg_mem : g ∈ raw ++ done' := by simp [done']
        exact meetNat_iff.mpr ⟨hsub, by rw [decM_and]; exact (meetNat_iff.mp hx').2.inter (Meet.atom ⟨g, hg_mem, rfl⟩)⟩
    have hacc_inv' : ∀ x ∈ acc, x.2.1 = x.1 &&& ep ∧ x.2.2 ≤ done.length + 1 ∧
        MeetNat M (raw ++ done'.take x.2.2) x.1 := by
      intro x hx
      obtain ⟨h1, h2, h3⟩ := hacc_inv x hx
      refine ⟨h1, by omega, ?_⟩
      have htake : done'.take x.2.2 = done.take x.2.2 := by
        simp only [done', List.take_append_of_le_length h2]
      rwa [htake]
    have hadd := chkAddSubsOps_inv hlen'.symm hmasks newSubs seen acc hnewSubs_meet
      hacc_inv' hacc_pw hseen_acc
    set r1 := chkAddSubsOps M ep (done.length + 1) masksTT newSubs seen acc
    have hsubs' : ∀ gi ∈ newSubs ++ subs, MeetNat M (raw ++ done') gi := by
      intro gi hgi
      rcases List.mem_append.mp hgi with hgi | hgi
      · exact hnewSubs_meet gi hgi
      · exact meetNat_weaken hraw_sub (hsubs gi hgi)
    have hsub_P' : ∀ P : List ℕ, List.Sublist P done' → P.foldl Nat.land M ∈ newSubs ++ subs := by
      intro P hP
      rcases sublist_append_singleton hP with h1 | ⟨P', h1, rfl⟩
      · exact List.mem_append_right _ (hsub_P P h1)
      · refine List.mem_append_left _ ?_
        rw [chkSubsetsStep_mem]
        refine Or.inr ⟨P'.foldl Nat.land M, hsub_P P' h1, ?_⟩
        simp [List.foldl_append]
    have hseen_cov' : ∀ gi ∈ newSubs ++ subs, ∀ mt ∈ masksTT,
        (mt &&& gi) ≠ 0 → (mt &&& gi) ≠ M → (mt &&& gi) &&& ep ≠ 0 → (mt &&& gi) ∈ r1.1 := by
      intro gi hgi mt hmt h0 hM hep
      rcases List.mem_append.mp hgi with hgi | hgi
      · exact hadd.2.2.2.2 gi hgi mt hmt h0 hM hep
      · exact hadd.2.2.1 _ (hseen_cov gi hgi mt hmt h0 hM hep)
    have htail_vp' : ValidPrefix M (raw ++ done') tail := by
      simpa only [done', List.append_assoc] using htail_vp
    have hrec := ih done' (newSubs ++ subs) r1.1 r1.2 htail_vp' hsubs' hsub_P'
      (by simpa only [hlen'] using hadd.1) hadd.2.1 hadd.2.2.2.1 hseen_cov'
    simp only [chkGenBirthLoop]
    simpa only [done', hlen', List.append_assoc, List.singleton_append] using hrec

theorem chkGenBirthOps_spec {n : ℕ} {H F : List (ℕ × ℕ)} {gs : List ℕ}
    (hv : ValidState n H F)
    (hvp : ValidPrefix (univYF n F) (rawYF n (univYF n F)) gs) :
    let M := univYF n F
    let ep := edgePtsMaskYF H
    let raw := rawYF n M
    let ops := chkGenBirthOps M ep (masksTTYF n H M) gs
    (∀ x ∈ ops, x.2.1 = x.1 &&& ep ∧ x.2.2 ≤ gs.length ∧ MeetNat M (raw ++ gs.take x.2.2) x.1) ∧
    ops.Pairwise (fun x y => y.2.2 ≤ x.2.2) ∧
    (∀ x : ℕ, MeetNat M (raw ++ gs) x → x ≠ 0 → x ≠ M → x &&& ep ≠ 0 →
      ∃ b, (x, x &&& ep, b) ∈ ops) := by
  set M := univYF n F
  set ep := edgePtsMaskYF H
  set raw := rawYF n M
  set masksTT := masksTTYF n H M
  have hmasks : ∀ mt ∈ masksTT, MeetNat M raw mt := masksTTYF_meetNat hv
  have hM_meet : MeetNat M (raw ++ []) M := by
    refine meetNat_iff.mpr ⟨by simp, ?_⟩
    rw [decM_self]; exact Meet.top
  have h0 := chkAddBirthOps_inv (ep := ep) (done := []) rfl hM_meet masksTT hmasks [] []
    (fun _ h => by simp at h) List.Pairwise.nil (fun _ h => by simp at h)
  set r0 := chkAddBirthOps M ep M 0 masksTT [] []
  have hloop := chkGenBirthLoop_inv hmasks gs [] [M] r0.1 r0.2
    (by simpa using hvp)
    (fun gi hgi => by rw [List.mem_singleton.mp hgi]; exact hM_meet)
    (fun P hP => by cases hP; simp)
    h0.1 h0.2.1 h0.2.2.2.1
    (fun gi hgi mt hmt h0' hM' hep' => by
      obtain rfl := List.mem_singleton.mp hgi; exact h0.2.2.2.2 mt hmt h0' hM' hep')
  simp only [List.length_nil, zero_add, List.nil_append] at hloop
  refine ⟨hloop.1, hloop.2.1, fun x hx h0' hM' hep' => ?_⟩
  obtain ⟨mt, hmt, P, hPsub, rfl⟩ := meetNat_decompose_on_edges hv hx hep'
  exact hloop.2.2 P hPsub mt hmt h0' hM' hep'

theorem chkBuildSuffixMax_nonempty (gs : List ℕ) :
    ∃ m ms, chkBuildSuffixMax gs = m :: ms := by
  induction gs with
  | nil => exact ⟨0, [], rfl⟩
  | cons g rest ih =>
    obtain ⟨m, ms, heq⟩ := ih
    exact ⟨chkNatMax g m, m :: ms, by simp [chkBuildSuffixMax, heq]⟩

theorem chkBuildSuffixMax_spec (gs : List ℕ) (bi g : ℕ)
    (hlim_ne : chkGetNat (chkBuildSuffixMax gs) bi ≠ 0)
    (hlt : g < chkGetNat (chkBuildSuffixMax gs) bi) :
    ∃ t, bi ≤ t ∧ ∃ (ht : t < gs.length), g < gs[t] := by
  induction gs generalizing bi with
  | nil =>
    cases bi with
    | zero => simp [chkBuildSuffixMax, chkGetNat] at hlim_ne
    | succ k => cases k <;> simp [chkBuildSuffixMax, chkGetNat] at hlim_ne
  | cons x rest ih =>
    obtain ⟨m, ms, hsm⟩ := chkBuildSuffixMax_nonempty rest
    have hcons : chkBuildSuffixMax (x :: rest) = chkNatMax x m :: m :: ms := by
      simp [chkBuildSuffixMax, hsm]
    rw [hcons] at hlim_ne hlt
    cases bi with
    | zero =>
      simp only [chkGetNat] at hlim_ne hlt
      unfold chkNatMax at hlt
      cases hxm : Nat.blt x m
      · rw [hxm] at hlt; dsimp only at hlt
        exact ⟨0, le_rfl, by simp, hlt⟩
      · rw [hxm] at hlt; dsimp only at hlt
        have hm0 : m ≠ 0 := by omega
        have hm_eq : chkGetNat (chkBuildSuffixMax rest) 0 = m := by simp [hsm, chkGetNat]
        obtain ⟨t, _, ht, hgt⟩ := ih 0 (hm_eq.symm ▸ hm0) (hm_eq.symm ▸ hlt)
        exact ⟨t + 1, Nat.zero_le _, by simp [ht], by simpa using hgt⟩
    | succ bi' =>
      simp only [chkGetNat] at hlim_ne hlt
      have heq : chkGetNat (m :: ms) bi' = chkGetNat (chkBuildSuffixMax rest) bi' := by rw [hsm]
      rw [heq] at hlim_ne hlt
      obtain ⟨t, hle, ht, hgt⟩ := ih bi' hlim_ne hlt
      exact ⟨t + 1, by omega, by simp [ht], by simpa using hgt⟩



theorem chkComputeMd_eq (edgeTT acc : ℕ) (b : List ℕ) :
    chkComputeMd edgeTT acc b = isMeetLoop edgeTT b acc := by
  induction b generalizing acc with
  | nil => rfl
  | cons x rest ih =>
    simp only [chkComputeMd, isMeetLoop]
    cases Nat.beq (Nat.land edgeTT x) edgeTT <;> exact ih _

theorem chkFilterGoodOps_eq (bad : ℕ) (ops : List (ℕ × ℕ × ℕ)) :
    chkFilterGoodOps bad ops =
      (ops.map Prod.fst).filter (fun op => Nat.beq (Nat.land op bad) 0) := by
  induction ops with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨op, eg, b⟩
    simp only [chkFilterGoodOps, List.map_cons, List.filter_cons]
    cases Nat.beq (Nat.land op bad) 0 <;> simp [ih]

theorem chkNoCovInner_eq (ep a : ℕ) (l : List ℕ) :
    chkNoCovInner ep a l = l.all (fun b => !Nat.beq (Nat.land (Nat.lor a b) ep) ep) := by
  induction l with
  | nil => rfl
  | cons b rest ih =>
    simp only [chkNoCovInner, List.all_cons]
    cases Nat.beq (Nat.land (Nat.lor a b) ep) ep <;> simp [ih]

theorem chkNoCovOuter_eq (ep : ℕ) (l : List ℕ) :
    chkNoCovOuter ep l = noCovPairs ep l := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    simp only [chkNoCovOuter, noCovPairs, chkNoCovInner_eq]
    cases rest.all (fun b => !Nat.beq (Nat.land (Nat.lor a b) ep) ep) <;> simp [ih]

theorem chkCheckTermMd_sound {n : ℕ} {H F : List (ℕ × ℕ)} {pre suf : List ℕ}
    (hv : ValidState n H F) (hHne : H ≠ [])
    (hrun : RunListFrom (univYF n F) (rawYF n (univYF n F)) (edgeTTYF n H (univYF n F)) (pre ++ suf))
    (hmin : ∀ k' < (pre ++ suf).length, ¬ HasRunYF n H F k')
    (hsuf_le : suf.length ≤ 1)
    (hok : chkCheckTermMd (univYF n F) (edgePtsMaskYF H) (edgeTTYF n H (univYF n F))
      (rawYF n (univYF n F)) (masksTTYF n H (univYF n F)) pre = true) :
    False := by
  set M := univYF n F
  set ep := edgePtsMaskYF H
  set edgeTT := edgeTTYF n H M
  set raw := rawYF n M
  unfold chkCheckTermMd at hok
  dsimp only at hok
  rw [chkComputeMd_eq] at hok
  cases hmd : Nat.beq (isMeetLoop edgeTT (raw ++ pre) M) edgeTT
  · rw [hmd] at hok
    have hmd_ne : isMeetLoop edgeTT (raw ++ pre) M ≠ edgeTT := (nat_beq_eq_false_iff _ _).mp hmd
    cases suf with
    | nil =>
      obtain ⟨_, hend⟩ := runListFrom_append.mp hrun
      have hEdgeNe0 : edgeTT ≠ 0 := by
        obtain ⟨e, _, heq⟩ := List.exists_cons_of_ne_nil hHne
        intro h0
        have hbit := edgePt_mem_edgeTTYF hv (show e ∈ H by rw [heq]; simp)
        rw [show edgeTTYF n H (univYF n F) = edgeTT from rfl, h0] at hbit; simp at hbit
      have hm := hend.2
      unfold isMeet at hm
      rw [(nat_beq_eq_false_iff _ _).mpr hEdgeNe0] at hm
      exact hmd_ne (Nat.eq_of_beq_eq_true hm)
    | cons g rest =>
      cases rest with
      | cons => simp at hsuf_le
      | nil =>
        have hvp : ValidPrefix M raw pre := (runListFrom_append.mp hrun).1
        have hops_spec := chkGenBirthOps_spec hv hvp
        have hops_cov : ∀ x, MeetNat M (raw ++ pre) x → x ≠ 0 → x ≠ M → x &&& ep ≠ 0 →
            x ∈ (chkGenBirthOps M ep (masksTTYF n H M) pre).map Prod.fst := by
          intro x hx h0 hM hep
          obtain ⟨b, hb⟩ := hops_spec.2.2 x hx h0 hM hep
          exact List.mem_map.mpr ⟨(x, x &&& ep, b), hb, rfl⟩
        have htm := termMd_sound hv hHne hrun hmin hops_cov
        rcases htm with heq | hnocov
        · exact hmd_ne heq
        · apply hnocov
          rw [← chkNoCovOuter_eq, ← chkFilterGoodOps_eq]
          exact hok
  · rw [hmd] at hok; simp at hok

theorem chkGetCut_mem {cuts : List CutDefData} {ci : ℕ} {gs : List ℕ} {stepIdx g : ℕ}
    (hok : chkCutKillsWit (chkPrepCutState (chkGetCut cuts ci) gs) stepIdx g = true) :
    chkGetCut cuts ci ∈ cuts := by
  induction cuts generalizing ci with
  | nil =>
    cases ci <;> simp [chkGetCut, chkPrepCutState, chkPrepSteps, chkCutKillsWit, chkCutKillsAtStep] at hok
  | cons c rest ih =>
    cases ci with
    | zero => exact List.mem_cons_self
    | succ k => exact List.mem_cons_of_mem _ (ih hok)

theorem chkGetCutState_mem {cuts : List CutDefData} {gs hints : List ℕ} {hi stepIdx g : ℕ}
    (hok : chkCutKillsWit (chkGetCutState (chkPrepHints cuts gs hints) hi) stepIdx g = true) :
    ∃ cut ∈ cuts, chkCutKillsWit (chkPrepCutState cut gs) stepIdx g = true := by
  induction hints generalizing hi with
  | nil =>
    cases hi <;> simp [chkPrepHints, chkGetCutState, chkCutKillsWit, chkCutKillsAtStep] at hok
  | cons ci rest ih =>
    cases hi with
    | zero =>
      simp only [chkPrepHints, chkGetCutState] at hok
      exact ⟨chkGetCut cuts ci, chkGetCut_mem hok, hok⟩
    | succ k =>
      simp only [chkPrepHints, chkGetCutState] at hok
      exact ih hok

theorem chkPairsNoStabInner_sound {maskYF : ℕ} {b : List ℕ} {hStates : List ChkCutState}
    {surv : List ℕ} {oi egi lim : ℕ} {rest : List (ℕ × ℕ × ℕ)} {wits wits' : List ℕ}
    (hok : chkPairsNoStabInner maskYF b hStates surv oi egi lim rest wits = some wits') :
    ∀ x ∈ rest,
      (egi &&& x.2.1 = egi) ∨ (egi &&& x.2.1 = x.2.1) ∨
      (lim ≠ 0 ∧ oi ||| x.1 < lim) ∨
      ∃ w, chkCheckWitNoStab maskYF b hStates surv (egi ||| x.2.1) (oi ||| x.1) w = true := by
  induction rest generalizing wits with
  | nil => intro x hx; simp at hx
  | cons p tail ih =>
    rcases p with ⟨oj, egj, bj⟩
    simp only [chkPairsNoStabInner, land_eq, lor_eq] at hok
    intro x hx
    cases h1 : Nat.beq (egi &&& egj) egi
    · rw [h1] at hok; dsimp only at hok
      cases h2 : Nat.beq (egi &&& egj) egj
      · rw [h2] at hok; dsimp only at hok
        cases hlex : (match Nat.beq lim 0 with | true => false | false => Nat.blt (oi ||| oj) lim)
        · rw [hlex] at hok; dsimp only at hok
          cases wits with
          | nil => simp at hok
          | cons w ws =>
            dsimp only at hok
            cases hw : chkCheckWitNoStab maskYF b hStates surv (egi ||| egj) (oi ||| oj) w
            · rw [hw] at hok; simp at hok
            · rw [hw] at hok; dsimp only at hok
              rcases List.mem_cons.mp hx with rfl | hx
              · exact Or.inr (Or.inr (Or.inr ⟨w, hw⟩))
              · exact ih hok x hx
        · rw [hlex] at hok; dsimp only at hok
          rcases List.mem_cons.mp hx with rfl | hx
          · cases hl0 : Nat.beq lim 0
            · rw [hl0] at hlex; dsimp only at hlex
              exact Or.inr (Or.inr (Or.inl ⟨(nat_beq_eq_false_iff _ _).mp hl0, nat_blt_eq_true hlex⟩))
            · rw [hl0] at hlex; simp at hlex
          · exact ih hok x hx
      · rw [h2] at hok; dsimp only at hok
        rcases List.mem_cons.mp hx with rfl | hx
        · exact Or.inr (Or.inl (Nat.eq_of_beq_eq_true h2))
        · exact ih hok x hx
    · rw [h1] at hok; dsimp only at hok
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Or.inl (Nat.eq_of_beq_eq_true h1)
      · exact ih hok x hx

theorem chkPairsNoStabOuter_sound {maskYF : ℕ} {b : List ℕ} {hStates : List ChkCutState}
    {surv smax : List ℕ} {ops : List (ℕ × ℕ × ℕ)} {wits : List ℕ}
    (hok : chkPairsNoStabOuter maskYF b hStates surv smax ops wits = true)
    (hpw : ops.Pairwise (fun x y => y.2.2 ≤ x.2.2))
    {x y : ℕ × ℕ × ℕ} (hx : x ∈ ops) (hy : y ∈ ops) (hne : x.1 ≠ y.1) :
    ∃ p q : ℕ × ℕ × ℕ, ((p = x ∧ q = y) ∨ (p = y ∧ q = x)) ∧ q.2.2 ≤ p.2.2 ∧
      let lim := chkGetNat smax p.2.2
      ((p.2.1 &&& q.2.1 = p.2.1) ∨ (p.2.1 &&& q.2.1 = q.2.1) ∨
       (lim ≠ 0 ∧ p.1 ||| q.1 < lim) ∨
       ∃ w, chkCheckWitNoStab maskYF b hStates surv (p.2.1 ||| q.2.1) (p.1 ||| q.1) w = true) := by
  induction ops generalizing wits with
  | nil => simp at hx
  | cons z rest ih =>
    rcases z with ⟨oi, egi, bi⟩
    simp only [chkPairsNoStabOuter] at hok
    cases hinner : chkPairsNoStabInner maskYF b hStates surv oi egi (chkGetNat smax bi) rest wits with
    | none => rw [hinner] at hok; simp at hok
    | some wits' =>
      rw [hinner] at hok
      obtain ⟨hhead_pw, htail_pw⟩ := List.pairwise_cons.mp hpw
      rcases List.mem_cons.mp hx with rfl | hx' <;> rcases List.mem_cons.mp hy with rfl | hy'
      · exact (hne rfl).elim
      · exact ⟨(oi, egi, bi), y, Or.inl ⟨rfl, rfl⟩, hhead_pw y hy',
          chkPairsNoStabInner_sound hinner y hy'⟩
      · exact ⟨(oi, egi, bi), x, Or.inr ⟨rfl, rfl⟩, hhead_pw x hx',
          chkPairsNoStabInner_sound hinner x hx'⟩
      · exact ih hok htail_pw hx' hy'

theorem chkPairsStabInner_sound {maskYF : ℕ} {b : List ℕ} {hStates : List ChkCutState}
    {surv : List ℕ} {oi egi lim : ℕ} {pi : List ℕ}
    {rest : List (ℕ × ℕ × ℕ × List ℕ)} {wits wits' : List ℕ}
    (hok : chkPairsStabInner maskYF b hStates surv oi egi lim pi rest wits = some wits') :
    ∀ x ∈ rest,
      (egi &&& x.2.1 = egi) ∨ (egi &&& x.2.1 = x.2.1) ∨
      (lim ≠ 0 ∧ oi ||| x.1 < lim) ∨
      ∃ w, chkCheckWitStab maskYF b hStates surv (egi ||| x.2.1) (oi ||| x.1) pi x.2.2.2 w = true := by
  induction rest generalizing wits with
  | nil => intro x hx; simp at hx
  | cons p tail ih =>
    rcases p with ⟨oj, egj, bj, pj⟩
    simp only [chkPairsStabInner, land_eq, lor_eq] at hok
    intro x hx
    cases h1 : Nat.beq (egi &&& egj) egi
    · rw [h1] at hok; dsimp only at hok
      cases h2 : Nat.beq (egi &&& egj) egj
      · rw [h2] at hok; dsimp only at hok
        cases hlex : (match Nat.beq lim 0 with | true => false | false => Nat.blt (oi ||| oj) lim)
        · rw [hlex] at hok; dsimp only at hok
          cases wits with
          | nil => simp at hok
          | cons w ws =>
            dsimp only at hok
            cases hw : chkCheckWitStab maskYF b hStates surv (egi ||| egj) (oi ||| oj) pi pj w
            · rw [hw] at hok; simp at hok
            · rw [hw] at hok; dsimp only at hok
              rcases List.mem_cons.mp hx with rfl | hx
              · exact Or.inr (Or.inr (Or.inr ⟨w, hw⟩))
              · exact ih hok x hx
        · rw [hlex] at hok; dsimp only at hok
          rcases List.mem_cons.mp hx with rfl | hx
          · cases hl0 : Nat.beq lim 0
            · rw [hl0] at hlex; dsimp only at hlex
              exact Or.inr (Or.inr (Or.inl ⟨(nat_beq_eq_false_iff _ _).mp hl0, nat_blt_eq_true hlex⟩))
            · rw [hl0] at hlex; simp at hlex
          · exact ih hok x hx
      · rw [h2] at hok; dsimp only at hok
        rcases List.mem_cons.mp hx with rfl | hx
        · exact Or.inr (Or.inl (Nat.eq_of_beq_eq_true h2))
        · exact ih hok x hx
    · rw [h1] at hok; dsimp only at hok
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Or.inl (Nat.eq_of_beq_eq_true h1)
      · exact ih hok x hx

theorem chkAttachPerms_eq_map (stab : List (List ℕ)) (ops : List (ℕ × ℕ × ℕ)) :
    chkAttachPerms stab ops = ops.map (fun x => (x.1, x.2.1, x.2.2, chkApplyPermList x.1 stab)) := by
  induction ops with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨op, eg, b⟩
    simp [chkAttachPerms, ih]

theorem chkPairsStabOuter_sound {maskYF : ℕ} {b : List ℕ} {hStates : List ChkCutState}
    {surv smax : List ℕ} {stab : List (List ℕ)} {ops : List (ℕ × ℕ × ℕ)} {wits : List ℕ}
    (hok : chkPairsStabOuter maskYF b hStates surv smax (chkAttachPerms stab ops) wits = true)
    (hpw : ops.Pairwise (fun x y => y.2.2 ≤ x.2.2))
    {x y : ℕ × ℕ × ℕ} (hx : x ∈ ops) (hy : y ∈ ops) (hne : x.1 ≠ y.1) :
    ∃ p q : ℕ × ℕ × ℕ, ((p = x ∧ q = y) ∨ (p = y ∧ q = x)) ∧ q.2.2 ≤ p.2.2 ∧
      let lim := chkGetNat smax p.2.2
      ((p.2.1 &&& q.2.1 = p.2.1) ∨ (p.2.1 &&& q.2.1 = q.2.1) ∨
       (lim ≠ 0 ∧ p.1 ||| q.1 < lim) ∨
       ∃ w, chkCheckWitStab maskYF b hStates surv (p.2.1 ||| q.2.1) (p.1 ||| q.1)
         (chkApplyPermList p.1 stab) (chkApplyPermList q.1 stab) w = true) := by
  induction ops generalizing wits with
  | nil => simp at hx
  | cons z rest ih =>
    rcases z with ⟨oi, egi, bi⟩
    simp only [chkAttachPerms, chkPairsStabOuter] at hok
    cases hinner : chkPairsStabInner maskYF b hStates surv oi egi (chkGetNat smax bi)
        (chkApplyPermList oi stab) (chkAttachPerms stab rest) wits with
    | none => rw [hinner] at hok; simp at hok
    | some wits' =>
      rw [hinner] at hok
      obtain ⟨hhead_pw, htail_pw⟩ := List.pairwise_cons.mp hpw
      have hmem_attach : ∀ u ∈ rest, (u.1, u.2.1, u.2.2, chkApplyPermList u.1 stab) ∈ chkAttachPerms stab rest := by
        intro u hu
        rw [chkAttachPerms_eq_map]
        exact List.mem_map.mpr ⟨u, hu, rfl⟩
      rcases List.mem_cons.mp hx with rfl | hx' <;> rcases List.mem_cons.mp hy with rfl | hy'
      · exact (hne rfl).elim
      · exact ⟨(oi, egi, bi), y, Or.inl ⟨rfl, rfl⟩, hhead_pw y hy',
          chkPairsStabInner_sound hinner _ (hmem_attach y hy')⟩
      · exact ⟨(oi, egi, bi), x, Or.inr ⟨rfl, rfl⟩, hhead_pw x hx',
          chkPairsStabInner_sound hinner _ (hmem_attach x hx')⟩
      · exact ih hok htail_pw hx' hy'

theorem chkCheckLayer_sound {n : ℕ} {H F : List (ℕ × ℕ)} {cuts : List CutDefData}
    {pre suf hints wits surv : List ℕ} {g : ℕ} {stabIdx : List (List ℕ)}
    (hv : ValidState n H F)
    (hcuts : ∀ cut ∈ cuts, ∀ (pre' suf' : List ℕ),
      RunListFrom (univYF n F) (rawYF n (univYF n F)) (edgeTTYF n H (univYF n F)) (pre' ++ suf') →
      (pre' ++ suf').length + 2 ≤ H.length →
      cut.loss ≤ evalCutChain cut.steps pre' → False)
    (hstab_valid : ∀ tbl ∈ stabIdx, ValidAutTbl (univYF n F) (edgeTTYF n H (univYF n F)) (rawYF n (univYF n F)) tbl)
    (hstab_fix : ∀ tbl ∈ stabIdx, ∀ h ∈ pre, applyPerm tbl h = h)
    (hrun : RunListFrom (univYF n F) (rawYF n (univYF n F)) (edgeTTYF n H (univYF n F)) (pre ++ g :: suf))
    (hlen : (pre ++ g :: suf).length + 2 ≤ H.length)
    (hmin : ∀ k' < (pre ++ g :: suf).length, ¬ HasRunYF n H F k')
    (hlex : ∀ gs', gs'.length = (pre ++ g :: suf).length →
      RunListFrom (univYF n F) (rawYF n (univYF n F)) (edgeTTYF n H (univYF n F)) gs' →
      ¬ List.Lex (· < ·) gs' (pre ++ g :: suf))
    (hok : chkCheckLayer (univYF n F) (edgePtsMaskYF H) (edgeTTYF n H (univYF n F))
      (rawYF n (univYF n F)) (masksTTYF n H (univYF n F)) cuts pre
      (chkMkAutMaskTbls stabIdx) hints wits surv = true) :
    g ∈ surv := by
  set M := univYF n F
  set ep := edgePtsMaskYF H
  set edgeTT := edgeTTYF n H M
  set raw := rawYF n M
  set masksTT := masksTTYF n H M
  have hvp : ValidPrefix M raw pre := (runListFrom_append.mp hrun).1
  obtain ⟨a, b, hgab, hab, ha, hb, ha0, haM, haep, hb0, hbM, hbep⟩ := lexMin_operands hv hrun hmin
  have hops := chkGenBirthOps_spec hv hvp
  obtain ⟨ba, hba⟩ := hops.2.2 a ha ha0 haM haep
  obtain ⟨bb, hbb⟩ := hops.2.2 b hb hb0 hbM hbep
  have hdisch : ∀ (p q : ℕ × ℕ × ℕ),
      p ∈ chkGenBirthOps M ep masksTT pre → q ∈ chkGenBirthOps M ep masksTT pre →
      p.1 ||| q.1 = g → q.2.2 ≤ p.2.2 →
      ((p.2.1 &&& q.2.1 = p.2.1) ∨ (p.2.1 &&& q.2.1 = q.2.1) ∨
       (chkGetNat (chkBuildSuffixMax pre) p.2.2 ≠ 0 ∧ p.1 ||| q.1 < chkGetNat (chkBuildSuffixMax pre) p.2.2) ∨
       (chkMemNat g surv = true ∨
        chkIsOnEdgesLoop (p.2.1 ||| q.2.1) g M (raw ++ pre) = true ∨
        (∃ tbl ∈ stabIdx, applyPerm tbl g < g) ∨
        ∃ cut ∈ cuts, cut.loss ≤ evalCutChain cut.steps (pre ++ [g]))) →
      g ∈ surv := by
    intro p q hp hq hpg hqp hcase
    obtain ⟨hpe, hpb, hpM⟩ := hops.1 p hp
    obtain ⟨hqe, hqb, hqM⟩ := hops.1 q hq
    have hq_sub : ∀ z ∈ raw ++ pre.take q.2.2, z ∈ raw ++ pre.take p.2.2 := by
      intro z hz
      rcases List.mem_append.mp hz with hz | hz
      · exact List.mem_append_left _ hz
      · refine List.mem_append_right _ ?_
        have htake : pre.take q.2.2 = (pre.take p.2.2).take q.2.2 := by
          rw [List.take_take, Nat.min_eq_left hqp]
        rw [htake] at hz
        exact List.mem_of_mem_take hz
    have hqM_p : MeetNat M (raw ++ pre.take p.2.2) q.1 := meetNat_weaken hq_sub hqM
    have hqM_full : MeetNat M (raw ++ pre) q.1 :=
      meetNat_weaken (fun z hz => (List.mem_append.mp hz).elim
        (List.mem_append_left _) (fun h => List.mem_append_right _ (List.mem_of_mem_take h))) hqM
    have hpM_full : MeetNat M (raw ++ pre) p.1 :=
      meetNat_weaken (fun z hz => (List.mem_append.mp hz).elim
        (List.mem_append_left _) (fun h => List.mem_append_right _ (List.mem_of_mem_take h))) hpM
    rcases hcase with hsub1 | hsub2 | ⟨hlim0, hlt⟩ | hmem | hon | ⟨tbl, htbl, hltp⟩ | ⟨cut, hcut, hkill⟩
    · rw [hpe, hqe] at hsub1
      exact (lexMin_not_eg_sub hv hrun hmin hqM_full hpg.symm hsub1).elim
    · rw [hpe, hqe, Nat.and_comm] at hsub2
      exact (lexMin_not_eg_sub hv hrun hmin hpM_full (Nat.or_comm _ _ ▸ hpg.symm) hsub2).elim
    · rw [hpg] at hlt
      obtain ⟨t, hpt, htlt, hgt⟩ := chkBuildSuffixMax_spec pre p.2.2 g hlim0 hlt
      exact (lexMin_birth_lex hrun hlex hpt htlt hpM hqM_p hpg.symm hgt).elim
    · exact (chkMemNat_iff g surv).mp hmem
    · exfalso
      have heg_eq : p.2.1 ||| q.2.1 = g &&& ep := by
        rw [hpe, hqe, ← hpg]
        apply Nat.eq_of_testBit_eq; intro s
        simp only [Nat.testBit_and, Nat.testBit_or]
        cases p.1.testBit s <;> cases q.1.testBit s <;> cases ep.testBit s <;> decide
      rw [heg_eq] at hon
      have hon' : isOnEdges M ep (raw ++ pre) g = true := by
        unfold isOnEdges
        rw [nat_beq_eq_true_iff]
        exact chkIsOnEdgesLoop_sound (g &&& ep) g M (raw ++ pre) hon
      have hno : isOnEdges M ep (raw ++ pre) g = false := lexMin_not_onEdges hv hrun hmin
      exact Bool.noConfusion (hon'.symm.trans hno)
    · exact (lexMin_autStab (hstab_valid tbl htbl) (hstab_fix tbl htbl) hrun hlex hltp).elim
    · exfalso
      have hrun' : RunListFrom M raw edgeTT ((pre ++ [g]) ++ suf) := by simpa [List.append_assoc] using hrun
      have hlen' : ((pre ++ [g]) ++ suf).length + 2 ≤ H.length := by simpa [List.append_assoc] using hlen
      exact hcuts cut hcut (pre ++ [g]) suf hrun' hlen' hkill
  unfold chkCheckLayer at hok
  dsimp only at hok
  cases hfin : chkIsMeet M (raw ++ pre) edgeTT
  · rw [hfin] at hok; dsimp only at hok
    cases hst : chkMkAutMaskTbls stabIdx with
    | nil =>
      rw [hst] at hok; dsimp only at hok
      obtain ⟨p, q, hpq, hqp, hres⟩ := chkPairsNoStabOuter_sound hok hops.2.1 hba hbb hab
      have hpg : p.1 ||| q.1 = g := by
        rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hgab.symm
        · rw [Nat.or_comm]; exact hgab.symm
      have hp_mem : p ∈ chkGenBirthOps M ep masksTT pre := by
        rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
      have hq_mem : q ∈ chkGenBirthOps M ep masksTT pre := by
        rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
      apply hdisch p q hp_mem hq_mem hpg hqp
      rcases hres with h1 | h2 | h3 | ⟨w, hw⟩
      · exact Or.inl h1
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr (Or.inl h3))
      · refine Or.inr (Or.inr (Or.inr ?_))
        rw [hpg] at hw
        match w, hw with
        | 0, hw => exact Or.inl hw
        | 1, hw => exact Or.inr (Or.inl hw)
        | 2, hw => simp [chkCheckWitNoStab] at hw
        | w3 + 3, hw =>
          simp only [chkCheckWitNoStab] at hw
          obtain ⟨cut, hcut, hkw⟩ := chkGetCutState_mem hw
          exact Or.inr (Or.inr (Or.inr ⟨cut, hcut, chkCutKillsWit_sound cut pre (Nat.land w3 7) g hkw⟩))
    | cons hd tl =>
      rw [hst] at hok; dsimp only at hok
      rw [← hst] at hok
      obtain ⟨p, q, hpq, hqp, hres⟩ := chkPairsStabOuter_sound hok hops.2.1 hba hbb hab
      have hpg : p.1 ||| q.1 = g := by
        rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hgab.symm
        · rw [Nat.or_comm]; exact hgab.symm
      have hp_mem : p ∈ chkGenBirthOps M ep masksTT pre := by
        rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
      have hq_mem : q ∈ chkGenBirthOps M ep masksTT pre := by
        rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
      apply hdisch p q hp_mem hq_mem hpg hqp
      rcases hres with h1 | h2 | h3 | ⟨w, hw⟩
      · exact Or.inl h1
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr (Or.inl h3))
      · refine Or.inr (Or.inr (Or.inr ?_))
        match w, hw with
        | 0, hw => exact Or.inl (hpg ▸ hw)
        | 1, hw => exact Or.inr (Or.inl (hpg ▸ hw))
        | 2, hw =>
          simp only [chkCheckWitStab] at hw
          obtain ⟨tbl, htbl, hltp⟩ := chkAnyPermLt_sound stabIdx p.1 q.1 hw
          exact Or.inr (Or.inr (Or.inl ⟨tbl, htbl, hpg ▸ hltp⟩))
        | w3 + 3, hw =>
          simp only [chkCheckWitStab] at hw
          rw [hpg] at hw
          obtain ⟨cut, hcut, hkw⟩ := chkGetCutState_mem hw
          exact Or.inr (Or.inr (Or.inr ⟨cut, hcut, chkCutKillsWit_sound cut pre (Nat.land w3 7) g hkw⟩))
  · rw [hfin] at hok; simp at hok

theorem chkCheckNode_sound {n : ℕ} {H F : List (ℕ × ℕ)} {cuts : List CutDefData}
    (hv : ValidState n H F) (h3 : 3 ≤ H.length)
    (hcuts : ∀ cut ∈ cuts, ∀ (pre' suf' : List ℕ),
      RunListFrom (univYF n F) (rawYF n (univYF n F)) (edgeTTYF n H (univYF n F)) (pre' ++ suf') →
      (pre' ++ suf').length + 2 ≤ H.length →
      cut.loss ≤ evalCutChain cut.steps pre' → False) :
    ∀ (node : CertNode) (pre suf : List ℕ) (stabIdx : List (List ℕ)),
      (∀ tbl ∈ stabIdx, ValidAutTbl (univYF n F) (edgeTTYF n H (univYF n F)) (rawYF n (univYF n F)) tbl) →
      (∀ tbl ∈ stabIdx, ∀ h ∈ pre, applyPerm tbl h = h) →
      RunListFrom (univYF n F) (rawYF n (univYF n F)) (edgeTTYF n H (univYF n F)) (pre ++ suf) →
      (pre ++ suf).length + 2 ≤ H.length →
      (∀ k' < (pre ++ suf).length, ¬ HasRunYF n H F k') →
      (∀ gs', gs'.length = (pre ++ suf).length →
        RunListFrom (univYF n F) (rawYF n (univYF n F)) (edgeTTYF n H (univYF n F)) gs' →
        ¬ List.Lex (· < ·) gs' (pre ++ suf)) →
      certDepthOk (H.length - 3) pre.length node = true →
      chkCheckNode (univYF n F) (edgePtsMaskYF H) (edgeTTYF n H (univYF n F))
        (rawYF n (univYF n F)) (masksTTYF n H (univYF n F)) cuts pre
        (chkMkAutMaskTbls stabIdx) node = true →
      False := by
  have hHne : H ≠ [] := by intro h; simp [h] at h3
  intro node
  induction node using CertNode.rec
      (motive_2 := fun ch =>
        ∀ (pre suf : List ℕ) (g : ℕ) (stabIdx : List (List ℕ)),
          (∀ tbl ∈ stabIdx, ValidAutTbl (univYF n F) (edgeTTYF n H (univYF n F)) (rawYF n (univYF n F)) tbl) →
          (∀ tbl ∈ stabIdx, ∀ h ∈ pre, applyPerm tbl h = h) →
          RunListFrom (univYF n F) (rawYF n (univYF n F)) (edgeTTYF n H (univYF n F)) (pre ++ g :: suf) →
          (pre ++ g :: suf).length + 2 ≤ H.length →
          (∀ k' < (pre ++ g :: suf).length, ¬ HasRunYF n H F k') →
          (∀ gs', gs'.length = (pre ++ g :: suf).length →
            RunListFrom (univYF n F) (rawYF n (univYF n F)) (edgeTTYF n H (univYF n F)) gs' →
            ¬ List.Lex (· < ·) gs' (pre ++ g :: suf)) →
          g ∈ chkCertListGates ch →
          certListDepthOk (H.length - 3) (pre.length + 1) ch = true →
          chkCheckChildren (univYF n F) (edgePtsMaskYF H) (edgeTTYF n H (univYF n F))
            (rawYF n (univYF n F)) (masksTTYF n H (univYF n F)) cuts pre
            (chkMkAutMaskTbls stabIdx) ch = true →
          False) with
  | term =>
    intro pre suf stabIdx _ _ hrun hlen hmin _ hdepth hcert
    simp only [certDepthOk] at hdepth
    simp only [chkCheckNode] at hcert
    have hd_ge : H.length - 3 ≤ pre.length := Nat.le_of_ble_eq_true hdepth
    simp only [List.length_append] at hlen
    have hsuf_le : suf.length ≤ 1 := by omega
    exact chkCheckTermMd_sound hv hHne hrun hmin hsuf_le hcert
  | branch hints witsChunks children ih_ch =>
    intro pre suf stabIdx hstab_v hstab_f hrun hlen hmin hlex hdepth hcert
    simp only [certDepthOk] at hdepth
    simp only [chkCheckNode] at hcert
    cases hlay : chkCheckLayer (univYF n F) (edgePtsMaskYF H) (edgeTTYF n H (univYF n F))
        (rawYF n (univYF n F)) (masksTTYF n H (univYF n F)) cuts pre
        (chkMkAutMaskTbls stabIdx) hints (chkFlatten witsChunks) (chkCertListGates children)
    · rw [hlay] at hcert; simp at hcert
    · rw [hlay] at hcert; dsimp only at hcert
      cases suf with
      | nil =>
        obtain ⟨_, hend⟩ := runListFrom_append.mp hrun
        have hm := hend.2
        rw [← chkIsMeet_eq_isMeet _ (edgeTTYF_and_univYF n H F)] at hm
        unfold chkCheckLayer at hlay
        dsimp only at hlay
        rw [hm] at hlay
        simp at hlay
      | cons g suf' =>
        have hg_mem := chkCheckLayer_sound hv hcuts hstab_v hstab_f hrun hlen hmin hlex hlay
        exact ih_ch pre suf' g stabIdx hstab_v hstab_f hrun hlen hmin hlex hg_mem hdepth hcert
  | nil =>
    rename_i pre suf g stabIdx hstab_v hstab_f hrun hlen hmin hlex hmem hdepth hcert
    simp [chkCertListGates] at hmem
  | cons g₀ ch rest ih_node ih_rest =>
    rename_i pre suf g stabIdx hstab_v hstab_f hrun hlen hmin hlex hmem hdepth hcert
    simp only [certListDepthOk, Bool.and_eq_true] at hdepth
    simp only [chkCheckChildren] at hcert
    cases hhead : chkCheckNode (univYF n F) (edgePtsMaskYF H) (edgeTTYF n H (univYF n F))
        (rawYF n (univYF n F)) (masksTTYF n H (univYF n F)) cuts (pre ++ [g₀])
        (chkFilterStab g₀ (chkMkAutMaskTbls stabIdx)) ch
    · rw [hhead] at hcert; simp at hcert
    · rw [hhead] at hcert; dsimp only at hcert
      simp only [chkCertListGates, List.mem_cons] at hmem
      rcases hmem with rfl | hmem'
      · rw [chkFilterStab_map] at hhead
        let stab' := stabIdx.filter (fun tbl => Nat.beq (applyPerm tbl g) g)
        have hstab'_v : ∀ tbl ∈ stab', ValidAutTbl (univYF n F) (edgeTTYF n H (univYF n F))
            (rawYF n (univYF n F)) tbl :=
          fun tbl htbl => hstab_v tbl (List.mem_of_mem_filter htbl)
        have hstab'_f : ∀ tbl ∈ stab', ∀ h ∈ pre ++ [g], applyPerm tbl h = h := by
          intro tbl htbl h hh
          obtain ⟨ht_mem, ht_eq⟩ := List.mem_filter.mp htbl
          rcases List.mem_append.mp hh with hh | hh
          · exact hstab_f tbl ht_mem h hh
          · rw [List.mem_singleton.mp hh]; exact Nat.eq_of_beq_eq_true ht_eq
        have hrun' : RunListFrom (univYF n F) (rawYF n (univYF n F)) (edgeTTYF n H (univYF n F))
            ((pre ++ [g]) ++ suf) := by simpa [List.append_assoc] using hrun
        have hlen' : ((pre ++ [g]) ++ suf).length + 2 ≤ H.length := by
          simpa [List.append_assoc] using hlen
        have hmin' : ∀ k' < ((pre ++ [g]) ++ suf).length, ¬ HasRunYF n H F k' := by
          simpa [List.append_assoc] using hmin
        have hlex' : ∀ gs', gs'.length = ((pre ++ [g]) ++ suf).length →
            RunListFrom (univYF n F) (rawYF n (univYF n F)) (edgeTTYF n H (univYF n F)) gs' →
            ¬ List.Lex (· < ·) gs' ((pre ++ [g]) ++ suf) := by
          simpa [List.append_assoc] using hlex
        have hdepth' : certDepthOk (H.length - 3) (pre ++ [g]).length ch = true := by
          simpa using hdepth.1
        exact ih_node (pre ++ [g]) suf stab' hstab'_v hstab'_f hrun' hlen' hmin' hlex' hdepth' hhead
      · exact ih_rest pre suf g stabIdx hstab_v hstab_f hrun hlen hmin hlex hmem' hdepth.2 hcert


def checkAllCutsValid (n : ℕ) (H F : List (ℕ × ℕ)) (states : List StateDesc) :
    List CutDefData → List CutSpecData → Bool
  | [], [] => true
  | cut :: cuts, spec :: specs =>
    match states[spec.childId]? with
    | none => false
    | some ch =>
      checkCutValid n H F cut spec.delVMask spec.forbAdded spec.peels
        ch.n ch.edges ch.forb spec.embed &&
      checkAllCutsValid n H F states cuts specs
  | _, _ => false

theorem checkAllCutsValid_sound {n : ℕ} {H F : List (ℕ × ℕ)} {states : List StateDesc}
    {cuts : List CutDefData} {specs : List CutSpecData}
    (hok : checkAllCutsValid n H F states cuts specs = true)
    (hchildren : ∀ spec ∈ specs, ∀ ch, states[spec.childId]? = some ch →
      OrCostLB ch.n ch.edges ch.forb (ch.edges.length - 1)) :
    ∀ cut ∈ cuts, ∀ (pre' suf' : List ℕ),
      RunListFrom (univYF n F) (rawYF n (univYF n F)) (edgeTTYF n H (univYF n F)) (pre' ++ suf') →
      (pre' ++ suf').length + 2 ≤ H.length →
      cut.loss ≤ evalCutChain cut.steps pre' → False := by
  induction cuts generalizing specs with
  | nil => intro _ hc; simp at hc
  | cons cut rest ih =>
    cases specs with
    | nil => simp [checkAllCutsValid] at hok
    | cons spec srest =>
      simp only [checkAllCutsValid] at hok
      cases hst : states[spec.childId]? with
      | none => rw [hst] at hok; simp at hok
      | some ch =>
        rw [hst] at hok
        simp only [Bool.and_eq_true] at hok
        intro c hc pre' suf' hrun hlen hkill
        rcases List.mem_cons.mp hc with rfl | hc'
        · exact cutDef_kills_sound hok.1 (hchildren spec List.mem_cons_self ch hst) hrun hlen hkill
        · exact ih hok.2 (fun s hs => hchildren s (List.mem_cons_of_mem _ hs)) c hc' pre' suf' hrun hlen hkill

theorem state_cert_sound {desc : StateDesc} {maskYF edgePts edgeTT : ℕ}
    {raw masksTT : List ℕ} {autIdxTbls auts : List (List ℕ)}
    {cuts : List CutDefData} {specs : List CutSpecData} {states : List StateDesc}
    {cert : CertNode}
    (hv : ValidState desc.n desc.edges desc.forb)
    (h3 : 3 ≤ desc.edges.length)
    (hM : maskYF = univYF desc.n desc.forb)
    (hEp : edgePts = edgePtsMaskYF desc.edges)
    (hEt : edgeTT = edgeTTYF desc.n desc.edges maskYF)
    (hRaw : raw = rawYF desc.n maskYF)
    (hMtt : masksTT = masksTTYF desc.n desc.edges maskYF)
    (hAuts : auts = chkMkAutMaskTbls autIdxTbls)
    (hAutV : ∀ tbl ∈ autIdxTbls, ValidAutTbl maskYF edgeTT raw tbl)
    (hCutsOk : checkAllCutsValid desc.n desc.edges desc.forb states cuts specs = true)
    (hChildren : ∀ spec ∈ specs, ∀ ch, states[spec.childId]? = some ch →
      OrCostLB ch.n ch.edges ch.forb (ch.edges.length - 1))
    (hDepth : certDepthOk (desc.edges.length - 3) 0 cert = true)
    (hCert : chkCheckNode maskYF edgePts edgeTT raw masksTT cuts [] auts cert = true) :
    OrCostLB desc.n desc.edges desc.forb (desc.edges.length - 1) := by
  subst hM hEp hEt hRaw hMtt hAuts
  intro k hr
  by_contra hlt
  have hle : k ≤ desc.edges.length - 2 := by omega
  obtain ⟨k₀, gs, hk₀_le, hlen, hrun, hmin, hlex⟩ :=
    exists_lexMinRun (bound := desc.edges.length - 2) ⟨k, hle, hr⟩
  subst hlen
  have hcuts_kill := checkAllCutsValid_sound hCutsOk hChildren
  exact chkCheckNode_sound hv h3 hcuts_kill cert [] gs autIdxTbls
    hAutV (fun _ _ _ h => by simp at h)
    (by simpa using hrun) (by simp; omega)
    (by simpa using hmin) (by simpa using hlex) hDepth hCert



structure StateCertEntry where
  desc       : StateDesc
  maskYF     : ℕ
  edgePts    : ℕ
  edgeTT     : ℕ
  raw        : List ℕ
  masksTT    : List ℕ
  autIdxTbls : List (List ℕ)
  auts       : List (List ℕ)
  cuts       : List CutDefData
  specs      : List CutSpecData
  cert       : CertNode

def checkAllCutsDAG (n : ℕ) (H F : List (ℕ × ℕ)) (states : List StateDesc) :
    List CutDefData → List CutSpecData → Bool
  | [], [] => true
  | cut :: cuts, spec :: specs =>
    match states[spec.childId]? with
    | none => false
    | some ch =>
      decide (ch.edges.length < H.length) &&
      checkCutValid n H F cut spec.delVMask spec.forbAdded spec.peels
        ch.n ch.edges ch.forb spec.embed &&
      checkAllCutsDAG n H F states cuts specs
  | _, _ => false

theorem checkAllCutsDAG_sound {n : ℕ} {H F : List (ℕ × ℕ)} {states : List StateDesc}
    {cuts : List CutDefData} {specs : List CutSpecData}
    (hok : checkAllCutsDAG n H F states cuts specs = true) :
    checkAllCutsValid n H F states cuts specs = true ∧
    ∀ spec ∈ specs, ∀ ch, states[spec.childId]? = some ch → ch.edges.length < H.length := by
  induction cuts generalizing specs with
  | nil =>
    cases specs with
    | nil => exact ⟨rfl, fun _ h => by simp at h⟩
    | cons _ _ => simp [checkAllCutsDAG] at hok
  | cons cut rest ih =>
    cases specs with
    | nil => simp [checkAllCutsDAG] at hok
    | cons spec srest =>
      simp only [checkAllCutsDAG] at hok
      cases hst : states[spec.childId]? with
      | none => rw [hst] at hok; simp at hok
      | some ch =>
        rw [hst] at hok
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
        obtain ⟨hval, hlt⟩ := ih hok.2
        refine ⟨?_, ?_⟩
        · simp [checkAllCutsValid, hst, hok.1.2, hval]
        · intro s hs ch' hget
          rcases List.mem_cons.mp hs with rfl | hs'
          · rw [hst] at hget; cases hget; exact hok.1.1
          · exact hlt s hs' ch' hget

def checkStateEntryDAG (states : List StateDesc) (e : StateCertEntry) : Bool :=
  if e.desc.edges.length ≤ 1 then true
  else
    decide (ValidState e.desc.n e.desc.edges e.desc.forb) &&
    decide (3 ≤ e.desc.edges.length) &&
    (e.maskYF == univYF e.desc.n e.desc.forb) &&
    (e.edgePts == edgePtsMaskYF e.desc.edges) &&
    (e.edgeTT == edgeTTYF e.desc.n e.desc.edges e.maskYF) &&
    (e.raw == rawYF e.desc.n e.maskYF) &&
    (e.masksTT == masksTTYF e.desc.n e.desc.edges e.maskYF) &&
    (e.auts == chkMkAutMaskTbls e.autIdxTbls) &&
    e.autIdxTbls.all (fun tbl => decide (ValidAutTbl e.maskYF e.edgeTT e.raw tbl)) &&
    checkAllCutsDAG e.desc.n e.desc.edges e.desc.forb states e.cuts e.specs &&
    certDepthOk (e.desc.edges.length - 3) 0 e.cert

theorem allStates_orCostLB (entries : List StateCertEntry)
    (hMeta : ∀ e ∈ entries, checkStateEntryDAG (entries.map StateCertEntry.desc) e = true)
    (hCerts : ∀ e ∈ entries, e.desc.edges.length ≤ 1 ∨
      chkCheckNode e.maskYF e.edgePts e.edgeTT e.raw e.masksTT e.cuts [] e.auts e.cert = true) :
    ∀ (i : ℕ) (ch : StateDesc), (entries.map StateCertEntry.desc)[i]? = some ch →
      OrCostLB ch.n ch.edges ch.forb (ch.edges.length - 1) := by
  have hstrong : ∀ m : ℕ, ∀ e ∈ entries, e.desc.edges.length = m →
      OrCostLB e.desc.n e.desc.edges e.desc.forb (e.desc.edges.length - 1) := by
    intro m
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      intro e he hm
      by_cases h1 : e.desc.edges.length ≤ 1
      · intro k _; omega
      · have hdag := hMeta e he
        simp only [checkStateEntryDAG, h1, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq,
          beq_iff_eq, List.all_eq_true] at hdag
        obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hv, h3⟩, hM⟩, hEp⟩, hEt⟩, hRaw⟩, hMtt⟩, hAuts⟩, hAutV⟩, hCuts⟩, hDepth⟩ := hdag
        obtain ⟨hCutsValid, hCutsLt⟩ := checkAllCutsDAG_sound hCuts
        have hCert := (hCerts e he).resolve_left h1
        have hChildren : ∀ spec ∈ e.specs, ∀ ch,
            (entries.map StateCertEntry.desc)[spec.childId]? = some ch →
            OrCostLB ch.n ch.edges ch.forb (ch.edges.length - 1) := by
          intro spec hspec ch hget
          have hmem : ch ∈ entries.map StateCertEntry.desc := List.mem_of_getElem? hget
          obtain ⟨e', he', rfl⟩ := List.mem_map.mp hmem
          exact ih e'.desc.edges.length (hm ▸ hCutsLt spec hspec e'.desc hget) e' he' rfl
        exact state_cert_sound hv h3 hM hEp hEt hRaw hMtt hAuts hAutV hCutsValid hChildren hDepth hCert
  intro i ch hget
  have hmem : ch ∈ entries.map StateCertEntry.desc := List.mem_of_getElem? hget
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hmem
  exact hstrong e.desc.edges.length e he rfl

def checkGraphCore (states : List StateDesc) (gc : GraphCoreSpec) : Bool :=
  match states[gc.coreId]? with
  | none => false
  | some ch =>
    decide (ValidState gc.n gc.edges []) &&
    validPeelEmbed gc.n gc.edges [] gc.peels ch.n ch.edges ch.forb gc.embed

theorem graphCore_orCostLB {states : List StateDesc} {cores : List GraphCoreSpec}
    (hStates : ∀ (i : ℕ) (ch : StateDesc), states[i]? = some ch →
      OrCostLB ch.n ch.edges ch.forb (ch.edges.length - 1))
    (hCores : cores.all (checkGraphCore states) = true)
    {idx : ℕ} {gc : GraphCoreSpec} (hget : cores[idx]? = some gc) :
    ValidState gc.n gc.edges [] ∧ OrCostLB gc.n gc.edges [] (gc.edges.length - 1) := by
  have hok : checkGraphCore states gc = true :=
    (List.all_eq_true.mp hCores) gc (List.mem_of_getElem? hget)
  simp only [checkGraphCore] at hok
  cases hst : states[gc.coreId]? with
  | none => rw [hst] at hok; simp at hok
  | some ch =>
    rw [hst] at hok
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    exact ⟨hok.1, validPeelEmbed_sound hok.1 hok.2 (hStates gc.coreId ch hst)⟩

theorem graph_or_bound_of_entry {n : ℕ} {H : List (ℕ × ℕ)} {f : (Fin n → Bool) → Bool}
    {states : List StateDesc} {cores : List GraphCoreSpec}
    (hf : ∀ x : Fin n → Bool, f x = edgeFnList n H x)
    (hStates : ∀ (i : ℕ) (ch : StateDesc), states[i]? = some ch →
      OrCostLB ch.n ch.edges ch.forb (ch.edges.length - 1))
    (hCores : cores.all (checkGraphCore states) = true)
    (idx : ℕ) (gc : GraphCoreSpec) (hget : cores[idx]? = some gc)
    (hn : gc.n = n) (hH : gc.edges = H)
    (C : Circuit) (hc : Monotone2 C) (he : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x) :
    H.length - 1 ≤ countOrGates C.gates := by
  obtain ⟨hv, hlb⟩ := graphCore_orCostLB hStates hCores hget
  subst hn hH
  exact or_bound_of_eval_eq (fun e heH => ⟨(hv.1 e heH).1, (hv.1 e heH).2.1⟩) hf hlb C hc he


def s1_desc : StateDesc := ⟨5,[(0,1),(0,4),(1,4),(2,3),(2,4),(3,4)],[]⟩
def s1_maskYF : Nat := 0xffffffff
def s1_edgePts : Nat := 0x1161008
def s1_edgeTT : Nat := 0xfffef888
def s1_raw : List Nat := chkMkRaw 5 s1_maskYF
def s1_masksTT : List Nat := chkMkMasksTT 5 s1_desc.edges s1_maskYF
def s1_autIdxTbls : List (List Nat) := []
def s1_auts : List (List Nat) := []
def s1_cutSpecs : List CutSpecData := [⟨0,[(3,4)],[3,2],2,[0,1,4]⟩,⟨2,[],[0],2,[2,3,4]⟩,⟨3,[],[],2,[2,3,4]⟩,⟨12,[],[],2,[0,1,4]⟩]
def s1_cuts : List CutDefData := chkMkCuts s1_maskYF s1_raw [(1,[.e [(3,4)]]),(2,[.v 1 [9,16]]),(3,[.v 0 [6,16,10],.v 1 [16]]),(3,[.v 2 [10,16],.v 3 [16]])]
def s1_cert : CertNode := .branch [2,3,1,0] [[11,11,19,3,3,27,27,27,11,11,3,3,11,11,11,11,3,3,11,11,11,3,3,19,19,19,3,3,3,3,3,3,3,12,11,19,3,11,19,3,11,3,3]] (.nil)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem cert_ok_1 : chkCheckNode s1_maskYF s1_edgePts s1_edgeTT s1_raw s1_masksTT s1_cuts [] s1_auts s1_cert = true := by decide +kernel

def s2_desc : StateDesc := ⟨3,[(0,1),(0,2),(1,2)],[]⟩
def s2_maskYF : Nat := 0xff
def s2_edgePts : Nat := 0x68
def s2_edgeTT : Nat := 0xe8
def s2_raw : List Nat := chkMkRaw 3 s2_maskYF
def s2_masksTT : List Nat := chkMkMasksTT 3 s2_desc.edges s2_maskYF
def s2_autIdxTbls : List (List Nat) := []
def s2_auts : List (List Nat) := []
def s2_cutSpecs : List CutSpecData := []
def s2_cuts : List CutDefData := chkMkCuts s2_maskYF s2_raw []
def s2_cert : CertNode := .term
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem cert_ok_2 : chkCheckNode s2_maskYF s2_edgePts s2_edgeTT s2_raw s2_masksTT s2_cuts [] s2_auts s2_cert = true := by decide +kernel

def s4_desc : StateDesc := ⟨5,[(0,1),(0,2),(1,3),(2,4),(3,4)],[]⟩
def s4_maskYF : Nat := 0xffffffff
def s4_edgePts : Nat := 0x1100428
def s4_edgeTT : Nat := 0xfff8eca8
def s4_raw : List Nat := chkMkRaw 5 s4_maskYF
def s4_masksTT : List Nat := chkMkMasksTT 5 s4_desc.edges s4_maskYF
def s4_autIdxTbls : List (List Nat) := []
def s4_auts : List (List Nat) := []
def s4_cutSpecs : List CutSpecData := [⟨0,[(2,4)],[2,0,1],17,[3,4]⟩,⟨24,[],[1],17,[0,2]⟩,⟨7,[],[],17,[3,4]⟩]
def s4_cuts : List CutDefData := chkMkCuts s4_maskYF s4_raw [(1,[.e [(2,4)]]),(3,[.v 3 [6,16],.v 4 [6]]),(4,[.v 0 [12,18],.v 1 [12],.v 2 [16]])]
def s4_cert : CertNode := .branch [2,1,0] [[11,11,3,3,11,11,11,11,3,3,19,19,19,3,3,11,11,11,3,3,3,3,3,3,3,11,12,12,3,11,11,3,4,3,3]] (.nil)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem cert_ok_4 : chkCheckNode s4_maskYF s4_edgePts s4_edgeTT s4_raw s4_masksTT s4_cuts [] s4_auts s4_cert = true := by decide +kernel

def s6_desc : StateDesc := ⟨6,[(0,1),(0,2),(1,4),(2,5),(3,4),(3,5),(4,5)],[]⟩
def s6_maskYF : Nat := 0xffffffffffffffff
def s6_edgePts : Nat := 0x1011001040028
def s6_edgeTT : Nat := 0xfffffff8ffeca8a8
def s6_raw : List Nat := chkMkRaw 6 s6_maskYF
def s6_masksTT : List Nat := chkMkMasksTT 6 s6_desc.edges s6_maskYF
def s6_autIdxTbls : List (List Nat) := []
def s6_auts : List (List Nat) := []
def s6_cutSpecs : List CutSpecData := [⟨8,[],[],4,[0,1,2,4,5]⟩,⟨0,[(4,5)],[],18,[0,1,2,3,4,5]⟩,⟨5,[],[1],2,[3,4,5]⟩,⟨44,[],[0],17,[1,4]⟩,⟨7,[],[],2,[3,4,5]⟩,⟨27,[],[],17,[2,5]⟩]
def s6_cuts : List CutDefData := chkMkCuts s6_maskYF s6_raw [(2,[.v 3 [17,32,20]]),(1,[.e [(4,5)]]),(3,[.v 2 [17,32],.v 0 [34]]),(5,[.v 2 [1,32],.v 3 [34],.v 5 [16]]),(4,[.v 1 [9,20,33],.v 0 [20],.v 2 [32]]),(6,[.v 1 [1,20],.v 3 [17,20,32],.v 0 [20],.v 4 [32]])]
def s6_cert : CertNode := .branch [4,0,2,1] [[11,11,19,3,19,3,27,27,27,27,11,11,3,11,3,11,11,11,11,11,3,11,3,11,11,11,11,3,19,3,19,19,19,19,3,3,3,3,3,3,3,19,19,19,19,3,3,3,3,0,11,19,3,20,11,19,3,4,11,3,11,3,19,3]] (.cons 0xffffffffffff0000 (.branch [5,3,1] [[11,3,19,11,3,11,3,4,4,4,12,4,3,11,11,11,3,11,3,11,11,3,11,3,3,3,3,3,3,3,3,3,3,11,3,11,3,5,1]] (.nil)) (.nil))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem cert_ok_6 : chkCheckNode s6_maskYF s6_edgePts s6_edgeTT s6_raw s6_masksTT s6_cuts [] s6_auts s6_cert = true := by decide +kernel

def s13_desc : StateDesc := ⟨7,[(0,1),(0,4),(1,5),(2,4),(2,6),(3,5),(3,6),(4,6),(5,6)],[]⟩
def s13_maskYF : Nat := 0xffffffffffffffffffffffffffffffff
def s13_edgePts : Nat := 0x1000101100000010400120008
def s13_edgeTT : Nat := 0xfffffffffffffff8fffeffccfafa8888
def s13_raw : List Nat := chkMkRaw 7 s13_maskYF
def s13_masksTT : List Nat := chkMkMasksTT 7 s13_desc.edges s13_maskYF
def s13_autIdxTbls : List (List Nat) := chkMkAutIdxTbls 7 [[1,0,3,2,5,4,6]]
def s13_auts : List (List Nat) := chkMkAutMaskTbls s13_autIdxTbls
def s13_cutSpecs : List CutSpecData := [⟨4,[],[],6,[0,1,4,3,5,6]⟩,⟨8,[],[],6,[1,0,5,2,4,6]⟩,⟨0,[(4,6)],[],22,[0,1,2,3,4,5,6]⟩,⟨0,[(5,6)],[],22,[1,0,3,2,5,4,6]⟩,⟨3,[],[],1,[2,4,3,5,6]⟩,⟨17,[(5,6)],[1,2,5],17,[3,6]⟩,⟨20,[(5,6)],[0,1,5],17,[3,6]⟩,⟨84,[],[0,1],17,[3,5]⟩,⟨35,[],[3],2,[2,4,6]⟩,⟨42,[],[0],2,[2,4,6]⟩,⟨21,[],[1],2,[3,5,6]⟩,⟨92,[],[0],17,[1,5]⟩,⟨108,[],[1],17,[0,4]⟩,⟨92,[],[0],17,[1,5]⟩,⟨51,[],[2],17,[3,6]⟩,⟨92,[],[0],17,[1,5]⟩,⟨23,[],[],2,[3,5,6]⟩,⟨23,[],[],2,[3,5,6]⟩,⟨55,[],[],17,[3,6]⟩,⟨55,[],[],17,[3,6]⟩,⟨107,[],[],17,[2,4]⟩,⟨55,[],[],17,[3,6]⟩,⟨110,[],[],17,[0,4]⟩,⟨59,[],[],17,[2,6]⟩,⟨93,[],[],17,[1,5]⟩,⟨124,[],[],17,[0,1]⟩]
def s13_cuts : List CutDefData := chkMkCuts s13_maskYF s13_raw [(2,[.v 2 [26,65]]),(2,[.v 3 [37,65,48]]),(1,[.e [(4,6)]]),(1,[.e [(5,6)]]),(3,[.v 0 [6,48,66],.v 1 [48,36]]),(5,[.e [(5,6)],.v 4 [33],.v 0 [2,66]]),(5,[.e [(5,6)],.v 4 [33],.v 2 [65]]),(6,[.v 2 [65,26,48],.v 4 [],.v 6 [33]]),(5,[.v 0 [66,16,18],.v 1 [48],.v 5 [24]]),(5,[.v 1 [65,48,36],.v 5 [24],.v 3 [64]]),(5,[.v 2 [65,26],.v 4 [33],.v 0 [2]]),(7,[.v 3 [37,66,48,65],.v 2 [65],.v 6 [48],.v 4 [33]]),(7,[.v 3 [36,48],.v 2 [18,65,48,66],.v 6 [48],.v 5 [18]]),(7,[.v 3 [37,48,65,66],.v 4 [64],.v 2 [64],.v 6 [33]]),(7,[.v 4 [33,36],.v 0 [6],.v 1 [32],.v 5 [8]]),(7,[.v 6 [9,37,6,16],.v 2 [26,48],.v 3 [32],.v 4 [33]]),(6,[.v 0 [2,24,48],.v 2 [48,26,64],.v 1 [32],.v 4 [64]]),(6,[.v 1 [48,1],.v 2 [65],.v 0 [16],.v 4 [64]]),(8,[.v 0 [2,24,48],.v 2 [48,66,24],.v 1 [32],.v 5 [24],.v 4 [64]]),(8,[.v 1 [1,36,33],.v 2 [65,48,24],.v 5 [65],.v 0 [24],.v 4 [64]]),(8,[.v 1 [32,65,33],.v 5 [24],.v 3 [64],.v 6 [4],.v 0 [16]]),(8,[.v 2 [],.v 0 [2,48],.v 1 [32],.v 5 [24],.v 4 [64]]),(8,[.v 2 [16,66,48],.v 1 [48,1],.v 3 [32],.v 5 [64],.v 6 [16]]),(8,[.v 4 [33,36],.v 0 [2],.v 1 [32],.v 3 [32],.v 5 [64]]),(8,[.v 4 [36,33],.v 2 [64],.v 6 [33],.v 3 [32],.v 0 [2]]),(8,[.v 6 [],.v 2 [26,48],.v 3 [32],.v 5 [18],.v 4 [1]])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
def s13_cert : CertNode := .branch [0,4,2,1,3] [[19,2,2,2,2,2,2,2,35,2,2,2,2,19,19,3,3,19,11,11,2,19,19,19,19,2,3,3,2,2,2,2,27,27,2,2,2,3,2,2,2,2,27,2,2,2,3,3,3,3,2,3,2,3,3,3,3,3,3,2,3,3,3,11],[2,2,12,2,12,2,11,11,2,2,11,11,11,2,11,2,11,2,0,2,3,2,11,0,2,2,2,2,27,3,12,11,3,2,2,3,3,11]] (.cons 0xffffffffffffffffffff0000ffff0000 (.branch [16,1,2,3,17] [[11,4,3,19,11,11,4,4,35,3,3,27,11,4,35,3,11,3,11,11,11,11,11,11,3,3,11,11,11,11,3,3,27,19,11,11,35,3,3,4,4,4,4,4,36,3,3,3,3,3,3,3,3,3,3,3,3,3,11,35,3,0,11,35],[3,0,1]] (.cons 0xffffffffffffffffffffffffffff0000 (.branch [19,13,2,3] [[11,3,11,11,4,11,11,27,19,4,4,3,6,3,11,11,11,11,11,11,3,4,4,11,4,27,19,11,11,3,12,3,4,4,4,11,3,4,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,5,11,4,27,19,11,11],[4,4,3,3,14,5,11,4,3,3,3,6,1]] (.nil)) (.cons 0xffffffffffffffffffffffff00000000 (.branch [22,11,4,2,3] [[3,11,3,11,11,11,11,11,11,1,3,3,11,11,11,11,11,11,11,11,3,3,3,3,3,3,3,3,3,3,1,3,3,3,3,3,3,3,3,11,4,3,19,11,3,4,19,19,1,1,11,3,4,19,11,3,4,27,11,3,19,27,11,11],[3,3,4,19,19,27,11,3,4,19,3,11,11,0,11,11,35,27,3,3,4,19,19,11,11,11,11,11,11,3,3,3,3,3,3,3,3,1,3,3,3,3,3,3,3,3,4,11,3,19,4,35,27,11,11,3,3,19,19,4,4,11,3,19],[3,19,6,3,19,19,6,3,4,19,6,1]] (.cons 0xfff0fff0fff0fff0fff0ff00f0f00000 (.branch [12,22,4,2,3] [[1,3,1,1,1,11,1,11,11,1,11,11,11,1,3,1,11,11,11,11,11,1,11,11,1,1,1,3,4,4,4,1,19,3,35,27,1,4,19,19,4,4,4,1,4,4,1,1,1,1,4,1,4,4,1,19,35,27,1,1,4,19,19,4],[4,1,1,4,4,1,3,1,1,3,1,3,3,1,3,3,3,1,1,3,3,3,3,3,3,1,3,3,1,1,11,4,1,4,11,4,19,35,27,1,12,19,19,4,4,4,1,4,4,1,1,3,3,4,3,4,4,3,19,35,27,3,3,4],[19,19,4,4,3,3,4,4,4,3,1,3,3,4,3,4,3,1,3,19,3,35,27,1,3,11,4,19,19,4,4,3,4,4,3,3,1,11,11,3,1,4,11,4,3,19,35,27,3,3,1,4,19,19,4,4,3,4,4,1,1,3,3,1],[3,3,1,3,3,3,3,3,3,3,3,3,3,3,3,1,3,3,1,11,11,1,11,11,11,1,11,11,11,3,3,11,11,11,11,11,11,1,11,11,4,4,4,11,4,19,3,35,27,12,19,19,4,4,4,4,4,3,3,3,3,3,3,11],[11,11,11,11,11,1,3,12,11,19,3,11,12,19,19,1,1,3,11,12,19,3,11,12,27,3,11,19,27,3,3,11,11,12,19,19,27,3,11,12,19,1,3,1,3,3,3,3,3,3,1,11,11,11,11,11,1,12,12,35,27,12,12,11],[19,6,11,19,19,6,11,12,19,6,1]] (.nil)) (.nil))) (.nil)))) (.cons 0xffffffffffff0000ffffffffffff0000 (.branch [10,8] [[2,3,2,11,2,2,3,3,2,11,11,2,13,2,0,2,0,3,2,2,2,4,2,3,3,2,2,2,2,13,3,2,2,3,3,2,3,2,2,3,3,3,3,3,2,2,3,3,11,2,4,2,2,3,3,11,2,2,12,2,3,11,2,11],[2,2,3,3,2,11,11,2,2,11,2,2,3,11,0,2,3,2,11,2,3,2,11,11,2,0,2,3,2,11,1]] (.cons 0xfffffffffffff0f0f0f0f0f0f0f0f0f0 (.branch [15,14,9,1,6] [[3,27,19,12,3,27,3,19,11,19,3,11,11,27,1,19,37,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,1,3,3,1,27,3,19,4,1,3,27,3,3,19,11,19,11,27,3,19,4,3,11,11,11,3,3,11,3,11,11,11],[11,11,11,3,11,11,27,19,12,4,3,27,19,11,19,3,4,11,27,19,12,3,3,1,27,3,19,3,3,3,3,27,4,27,11,19,11,19,3,0,3,3,3,3]] (.cons 0xffffffffffffffffffff0000ffff0000 (.branch [21,11,6,9,15] [[4,3,11,4,11,27,4,3,11,11,27,4,27,3,36,3,36,36,21,3,4,11,3,4,1,11,3,27,4,1,11,11,3,3,27,4,27,1,20,3,20,20,4,11,1,4,1,11,27,4,11,11,1,27,4,27,3,20,1,20,1,20,20,3],[3,3,3,1,3,1,3,3,3,3,1,3,3,1,3,3,3,3,3,3,3,3,4,11,3,4,35,4,4,4,35,11,3,27,19,35,11,11,3,3,27,27,35,4,4,3,4,11,3,3,3,11,27,11,11,3,27,27,1,1,11,3,27,4],[11,3,4,1,11,3,27,4,1,11,11,3,3,27,4,27,1,11,3,27,4,3,11,11,11,11,11,11,11,11,3,11,11,11,11,11,11,3,3,11,11,11,11,11,3,11,11,3,1,1,3,3,1,3,3,3,3,3,3,3,3,3,3,3],[3,3,3,3,3,3,4,35,4,4,4,35,11,3,27,19,35,11,11,3,3,27,27,35,4,11,3,27,11,27,35,11,27,27,35,11,27,4,35,35,1]] (.nil)) (.nil))) (.cons 0xffffffffffffaaaaaaaaaaaaaaaaaaaa (.branch [24,20,10,1,5] [[11,27,19,11,27,27,19,3,11,11,5,3,3,27,37,11,1,3,11,27,19,11,1,27,27,19,3,11,3,11,5,14,27,19,11,1,1,11,27,19,11,3,1,27,27,19,3,11,3,11,3,27,12,11,3,3,3,3,3,3,3,3,3,3],[3,3,3,3,3,3,3,3,3,11,11,11,11,11,11,11,3,11,11,11,3,11,3,11,11,11,11,11,27,19,11,21,27,27,19,3,11,5,21,3,27,19,11,27,19,36,36,36,1,27,19,11,5,27,19,5,27,19,11,21,27,3,11,3],[11,5,0,27,19,11,5]] (.cons 0xffffffffffffffffffff0000ffff0000 (.branch [7,5,9,1] [[3,27,3,19,27,3,19,27,27,3,3,19,19,4,5,1,27,3,19,1,3,11,27,12,11,1,19,27,3,19,11,1,27,27,3,3,19,11,19,1,12,12,12,11,3,27,12,19,27,3,19,27,27,3,3,19,19,4,4,1,12,12,12,1],[3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,1,3,3,3,3,3,3,3,3,4,27,12,1,11,19,1,27,3,19,11,1,27,27,3,3,19,19,4,4,12,12,12,27,3,19,4,27,19,27,27,3,19,19,1,1,27],[3,19,4,27,3,4,1,19,27,3,19,4,1,27,27,3,3,19,4,19,1,27,3,19,4,3,27,27,27,27,27,19,27,27,27,3,19,27,27,11,27,27,3,3,19,27,19,27,27,3,27,27,3,13,3,20,12,19,3,12,3,3,13,3],[11,12,27,27,19,12,19,3,3,3,3,3,3,1,20,19,1,27,3,19,11,1,27,27,3,3,19,19,4,5,27,3,19,19,5,27,19,20,27,19,19,20,27,19,5,20,5,1]] (.nil)) (.nil))) (.cons 0xffffffffffffffffffffffffffff0000 (.branch [23,12,4,15] [[11,2,2,2,2,2,2,2,2,3,2,3,2,2,2,2,2,11,11,2,2,12,19,27,11,12,19,27,2,3,11,2,20,3,19,27,2,3,2,12,12,19,2,2,12,2,2,3,2,2,27,3,3,2,2,20,2,12,19,19,2,19,19,2],[3,2,2,19,3,2,19,19,2,2,19,2,19,2,19,1]] (.nil)) (.cons 0xffffffffffffffffffff0000ffff0000 (.branch [18,11,9,2] [[3,4,11,3,4,11,19,3,4,27,11,11,1,19,3,3,4,4,4,4,12,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,11,4,11,19,11,11,4,19,3,1,1,11,4,19,3,11,4,3,11,4,19,3,1],[11,11,4,4,19,3,3,1,11,4,19,3,11,3,11,11,11,11,3,11,11,11,11,11,11,11,3,3,11,11,11,11,3,3,0,11,19,3,4,20,27,11,11,19,3,3,4,4,4,4,4,12,3,3,3,3,3,3,3,3,3,3,3,3],[3,3,3,3,3,11,19,20,11,19,3,20,11,19,3,20,13,1]] (.cons 0xfffffffffffff0f0f0f00000f0f00000 (.branch [25,5,9,1,6] [[1,12,27,1,12,27,19,12,3,27,1,19,12,19,3,4,1,4,1,4,12,1,1,3,3,3,1,3,3,1,3,3,3,3,3,1,3,3,3,3,3,3,1,3,3,1,3,4,27,3,4,27,3,19,4,1,3,27,3,3,19,4,19,1],[4,3,4,4,12,1,27,3,12,1,27,19,12,1,3,27,3,19,12,19,3,4,4,3,4,12,12,3,27,13,27,19,13,3,3,27,19,12,19,3,4,3,4,4,37,3,3,3,3,3,3,1,27,4,3,3,1,3,3,3,27,19,3,27],[19,19,3,27,19,13,3,3,1]] (.nil)) (.nil))) (.nil)))))) (.nil)))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem cert_ok_13 : chkCheckNode s13_maskYF s13_edgePts s13_edgeTT s13_raw s13_masksTT s13_cuts [] s13_auts s13_cert = true := by decide +kernel

def s17_desc : StateDesc := ⟨2,[(0,1)],[]⟩

def s18_desc : StateDesc := ⟨6,[(0,1),(0,2),(1,4),(2,5),(3,4),(3,5)],[(4,5)]⟩
def s18_maskYF : Nat := 0xffffffffffff
def s18_edgePts : Nat := 0x11001040028
def s18_edgeTT : Nat := 0xfff8ffeca8a8
def s18_raw : List Nat := chkMkRaw 6 s18_maskYF
def s18_masksTT : List Nat := chkMkMasksTT 6 s18_desc.edges s18_maskYF
def s18_autIdxTbls : List (List Nat) := []
def s18_auts : List (List Nat) := []
def s18_cutSpecs : List CutSpecData := [⟨0,[(0,2)],[0,1,2,4],17,[3,5]⟩,⟨0,[(3,4)],[3,4,1,0],17,[2,5]⟩,⟨8,[],[4,1,0],17,[2,5]⟩,⟨40,[],[2,0],17,[1,4]⟩,⟨23,[],[],17,[3,5]⟩]
def s18_cuts : List CutDefData := chkMkCuts s18_maskYF s18_raw [(1,[.e [(0,2)]]),(1,[.e [(3,4)]]),(2,[.v 3 [20,17,34]]),(3,[.v 5 [9,4],.v 3 [20]]),(5,[.v 1 [9,20,33],.v 0 [20,12],.v 4 [12],.v 2 [32]])]
def s18_cert : CertNode := .branch [4,3,0,1] [[11,11,3,11,3,11,11,11,11,11,3,19,3,27,27,27,27,3,11,3,11,11,11,11,3,3,3,3,3,3,3,19,19,19,19,3,3,3,3,0,11,11,3,11,12,5,3,4,12,3,4,3,4,3]] (.cons 0xffffffff0000 (.branch [4,3,0,2] [[27,3,11,3,19,3,11,11,27,27,27,3,11,27,3,19,3,11,27,3,4,3,3,3,3,3,3,3,3,3,19,3,6,3,4,1]] (.nil)) (.nil))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem cert_ok_18 : chkCheckNode s18_maskYF s18_edgePts s18_edgeTT s18_raw s18_masksTT s18_cuts [] s18_auts s18_cert = true := by decide +kernel

def s22_desc : StateDesc := ⟨7,[(0,1),(0,4),(1,5),(2,4),(2,6),(3,5),(3,6),(5,6)],[(4,6)]⟩
def s22_maskYF : Nat := 0xffff0000ffffffffffffffffffff
def s22_edgePts : Nat := 0x1000001100000010400120008
def s22_edgeTT : Nat := 0xffff0000fff8fffeffccfafa8888
def s22_raw : List Nat := chkMkRaw 7 s22_maskYF
def s22_masksTT : List Nat := chkMkMasksTT 7 s22_desc.edges s22_maskYF
def s22_autIdxTbls : List (List Nat) := []
def s22_auts : List (List Nat) := []
def s22_cutSpecs : List CutSpecData := [⟨32,[],[1,0,3,4],17,[2,6]⟩,⟨2,[],[0,4,2],2,[3,5,6]⟩,⟨4,[],[4,0,1],2,[3,5,6]⟩,⟨8,[],[],18,[1,0,5,2,4,6]⟩,⟨0,[(5,6)],[],26,[0,1,2,3,4,5,6]⟩,⟨76,[],[4,0],17,[1,5]⟩,⟨84,[],[0,1],17,[3,5]⟩,⟨104,[],[1,0],17,[2,4]⟩,⟨85,[],[1],17,[3,5]⟩,⟨108,[],[1],17,[0,4]⟩,⟨23,[],[],2,[3,5,6]⟩,⟨59,[],[],17,[2,6]⟩,⟨59,[],[],17,[2,6]⟩]
def s22_cuts : List CutDefData := chkMkCuts s22_maskYF s22_raw [(3,[.v 5 [64,26,66]]),(2,[.v 1 [65,48,1]]),(2,[.v 2 [48,66,24,65]]),(2,[.v 3 [37,66,48]]),(1,[.e [(5,6)]]),(5,[.v 2 [16,64],.v 3 [66],.v 6 [32]]),(5,[.v 2 [26,66,48,65],.v 6 [],.v 4 [33]]),(5,[.v 3 [37,66,48,65],.v 5 [64],.v 6 []]),(6,[.v 0 [2,48],.v 4 [],.v 2 [],.v 6 [32]]),(6,[.v 3 [],.v 2 [48,66,65],.v 6 [],.v 5 [2]]),(5,[.v 0 [14,48,24,66],.v 1 [32],.v 4 [36],.v 2 [64]]),(7,[.v 0 [2,24,18],.v 3 [66,48],.v 1 [48],.v 4 [],.v 5 [64]]),(7,[.v 1 [1,36],.v 3 [37,48,64],.v 0 [16],.v 4 [4],.v 5 [64]])]
def s22_cert : CertNode := .branch [10,3,2,4,1] [[11,11,19,19,27,3,3,27,27,27,27,27,11,11,11,11,3,3,11,11,11,11,11,11,11,11,3,3,11,11,11,11,11,19,19,3,3,19,19,19,19,19,19,3,3,19,19,19,19,19,3,3,35,35,35,35,35,3,3,3,3,3,3,3],[3,3,3,3,0,0,11,19,35,3,5,11,19,35,3,11,19,35,3,11,11,3,19,3,3]] (.cons 0xffff0000ffffffffffff00000000 (.branch [12,5,4,10] [[11,3,19,11,11,3,27,3,4,4,4,4,12,4,3,11,11,11,11,3,11,3,11,11,11,3,11,3,3,3,3,3,3,3,3,3,3,3,3,11,27,3,29,11,3,27,1]] (.nil)) (.cons 0xffff0000ffffffff0000ffff0000 (.branch [10,3,2,1,4] [[11,19,3,11,11,19,19,27,3,3,35,11,19,27,3,11,3,11,11,11,11,11,3,3,11,11,11,11,3,3,35,11,11,27,3,3,19,19,19,19,19,19,3,3,3,3,3,3,3,3,3,3,3,3,11,27,3,0,11,27,3,0,1]] (.cons 0xffff0000ffffffffffffffff0000 (.branch [11,6,0] [[11,4,3,19,11,3,19,19,11,11,19,3,3,4,19,4,11,4,3,11,3,11,11,3,19,4,19,19,3,3,11,11,11,11,11,11,3,19,4,11,3,19,19,4,19,11,11,3,3,12,5,4,11,3,3,3,3,3,3,3,3,3,3,3],[3,3,3,3,3,3,5,3,1]] (.nil)) (.cons 0xffff0000ffffffffffff00000000 (.branch [7,6,1,10] [[3,3,3,3,3,3,3,1,3,3,3,3,3,3,3,3,3,3,11,11,11,3,11,11,3,3,1,11,11,11,11,11,11,11,11,3,19,11,27,3,11,19,27,19,1,1,3,11,19,27,3,3,3,0,3,3,12,11,11,19,27,19,3,3],[3,3,3,3,11,11,3,11,11,3,3,1,11,11,11,11,11,3,11,11,19,3,11,19,19,19,3,3,11,11,19,19,19,19,3,11,19,11,27,4,11,27,19,4,11,19,27,4,1]] (.cons 0xfff00000fff0fff0ff00f0f00000 (.branch [9,8,0,4] [[1,3,1,1,1,1,4,4,1,11,27,1,3,1,19,11,11,4,4,1,4,4,1,1,1,3,4,4,1,11,3,27,1,19,11,11,19,4,4,1,4,4,1,1,1,1,1,4,4,1,11,27,1,1,19,11,11,4,4,1,1,4,4,1],[3,1,1,1,3,3,1,3,3,1,1,3,3,3,3,3,3,1,3,3,1,1,4,1,4,4,4,11,27,1,19,11,11,4,4,4,1,4,4,1,1,3,3,3,4,4,3,11,27,3,3,19,11,11,4,4,3,3,4,4,19,3,1,3],[3,3,19,3,1,3,11,3,19,1,3,19,19,11,11,19,19,3,19,19,3,3,1,4,3,1,4,4,4,3,11,27,3,3,1,19,11,11,4,4,3,4,4,1,1,3,1,3,3,1,3,3,3,3,3,3,3,3,3,3,3,1,3,3],[1,4,1,4,4,4,1,11,27,3,3,19,11,11,4,4,4,1,4,4,4,4,4,4,11,3,27,19,11,11,4,4,4,4,4,3,3,3,4,27,4,1,3,19,4,11,3,4,19,11,11,1,1,3,4,6,11,1,3,1,3,3,3,3],[1,4,27,4,1,19,19,19,19,4,11,19,4,11,11,19,4,6,11,19,1]] (.nil)) (.nil))) (.nil)))) (.nil)))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem cert_ok_22 : chkCheckNode s22_maskYF s22_edgePts s22_edgeTT s22_raw s22_masksTT s22_cuts [] s22_auts s22_cert = true := by decide +kernel

def s26_desc : StateDesc := ⟨7,[(0,1),(0,4),(1,5),(2,4),(2,6),(3,5),(3,6)],[(4,6),(5,6)]⟩
def s26_maskYF : Nat := 0xffffffffffffffffffff
def s26_edgePts : Nat := 0x1100000010400120008
def s26_edgeTT : Nat := 0xfff8fffeffccfafa8888
def s26_raw : List Nat := chkMkRaw 7 s26_maskYF
def s26_masksTT : List Nat := chkMkMasksTT 7 s26_desc.edges s26_maskYF
def s26_autIdxTbls : List (List Nat) := []
def s26_auts : List (List Nat) := []
def s26_cutSpecs : List CutSpecData := [⟨0,[(1,5)],[1,0,4,2,5],17,[3,6]⟩,⟨4,[],[4,0,1,5],17,[3,6]⟩,⟨34,[],[0,3,4],17,[2,6]⟩,⟨84,[],[0,1],17,[3,5]⟩,⟨76,[],[4,0],17,[1,5]⟩,⟨55,[],[],17,[3,6]⟩,⟨55,[],[],17,[3,6]⟩]
def s26_cuts : List CutDefData := chkMkCuts s26_maskYF s26_raw [(1,[.e [(1,5)]]),(2,[.v 2 [26,64,48]]),(3,[.v 5 [24,2],.v 1 [65]]),(4,[.v 2 [26,65,48],.v 6 [],.v 4 [1]]),(4,[.v 3 [37,66,48],.v 6 [6],.v 2 [16]]),(6,[.v 0 [14,48,24,66],.v 1 [48],.v 4 [36],.v 5 [8],.v 2 [64]]),(6,[.v 1 [1,36],.v 0 [16],.v 4 [36],.v 5 [],.v 2 [64]])]
def s26_cert : CertNode := .branch [5,4,1,0] [[11,11,11,11,3,3,11,11,11,11,11,11,11,11,3,3,11,11,11,11,11,19,19,3,3,19,19,19,19,19,19,3,3,19,19,19,19,19,3,3,27,27,27,27,27,3,3,3,3,3,3,3,3,3,3,3,0,0,11,19,12,3,5,11],[19,4,3,11,19,4,3,11,11,3,19,3,3]] (.cons 0xffffffffffff00000000 (.branch [6,4,1,5] [[11,3,19,19,3,27,3,11,11,11,11,11,11,3,11,11,19,3,19,3,19,19,11,3,19,3,3,3,3,3,3,3,3,3,3,3,19,27,3,5,19,3,27,1]] (.nil)) (.cons 0xffffffff0000ffff0000 (.branch [3,2,5,4] [[3,19,11,3,3,11,19,19,11,27,3,27,19,3,27,11,11,19,19,3,3,3,3,3,3,19,11,3,3,11,19,19,19,19,3,19,11,11,19,11,27,12,19,4,1]] (.nil)) (.nil)))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem cert_ok_26 : chkCheckNode s26_maskYF s26_edgePts s26_edgeTT s26_raw s26_masksTT s26_cuts [] s26_auts s26_cert = true := by decide +kernel

def allStates : List StateDesc := [s17_desc,s1_desc,s2_desc,s17_desc,s4_desc,s17_desc,s6_desc,s17_desc,s17_desc,s17_desc,s17_desc,s17_desc,s17_desc,s13_desc,s17_desc,s17_desc,s17_desc,s17_desc,s18_desc,s17_desc,s17_desc,s17_desc,s22_desc,s17_desc,s17_desc,s17_desc,s26_desc,s17_desc]
def allGraphCores : List GraphCoreSpec := [
  ⟨28,7,[(0,1),(0,2),(0,3),(0,4),(1,2),(1,5),(3,4),(3,6),(5,6)],12,13,[],[5,6,2,4,1,3,0]⟩
]

def allEntries : List StateCertEntry := [
  ⟨s17_desc, 0, 0, 0, [], [], [], [], [], [], .term⟩,
  ⟨s1_desc, s1_maskYF, s1_edgePts, s1_edgeTT, s1_raw, s1_masksTT, s1_autIdxTbls, s1_auts, s1_cuts, s1_cutSpecs, s1_cert⟩,
  ⟨s2_desc, s2_maskYF, s2_edgePts, s2_edgeTT, s2_raw, s2_masksTT, s2_autIdxTbls, s2_auts, s2_cuts, s2_cutSpecs, s2_cert⟩,
  ⟨s17_desc, 0, 0, 0, [], [], [], [], [], [], .term⟩,
  ⟨s4_desc, s4_maskYF, s4_edgePts, s4_edgeTT, s4_raw, s4_masksTT, s4_autIdxTbls, s4_auts, s4_cuts, s4_cutSpecs, s4_cert⟩,
  ⟨s17_desc, 0, 0, 0, [], [], [], [], [], [], .term⟩,
  ⟨s6_desc, s6_maskYF, s6_edgePts, s6_edgeTT, s6_raw, s6_masksTT, s6_autIdxTbls, s6_auts, s6_cuts, s6_cutSpecs, s6_cert⟩,
  ⟨s17_desc, 0, 0, 0, [], [], [], [], [], [], .term⟩,
  ⟨s17_desc, 0, 0, 0, [], [], [], [], [], [], .term⟩,
  ⟨s17_desc, 0, 0, 0, [], [], [], [], [], [], .term⟩,
  ⟨s17_desc, 0, 0, 0, [], [], [], [], [], [], .term⟩,
  ⟨s17_desc, 0, 0, 0, [], [], [], [], [], [], .term⟩,
  ⟨s17_desc, 0, 0, 0, [], [], [], [], [], [], .term⟩,
  ⟨s13_desc, s13_maskYF, s13_edgePts, s13_edgeTT, s13_raw, s13_masksTT, s13_autIdxTbls, s13_auts, s13_cuts, s13_cutSpecs, s13_cert⟩,
  ⟨s17_desc, 0, 0, 0, [], [], [], [], [], [], .term⟩,
  ⟨s17_desc, 0, 0, 0, [], [], [], [], [], [], .term⟩,
  ⟨s17_desc, 0, 0, 0, [], [], [], [], [], [], .term⟩,
  ⟨s17_desc, 0, 0, 0, [], [], [], [], [], [], .term⟩,
  ⟨s18_desc, s18_maskYF, s18_edgePts, s18_edgeTT, s18_raw, s18_masksTT, s18_autIdxTbls, s18_auts, s18_cuts, s18_cutSpecs, s18_cert⟩,
  ⟨s17_desc, 0, 0, 0, [], [], [], [], [], [], .term⟩,
  ⟨s17_desc, 0, 0, 0, [], [], [], [], [], [], .term⟩,
  ⟨s17_desc, 0, 0, 0, [], [], [], [], [], [], .term⟩,
  ⟨s22_desc, s22_maskYF, s22_edgePts, s22_edgeTT, s22_raw, s22_masksTT, s22_autIdxTbls, s22_auts, s22_cuts, s22_cutSpecs, s22_cert⟩,
  ⟨s17_desc, 0, 0, 0, [], [], [], [], [], [], .term⟩,
  ⟨s17_desc, 0, 0, 0, [], [], [], [], [], [], .term⟩,
  ⟨s17_desc, 0, 0, 0, [], [], [], [], [], [], .term⟩,
  ⟨s26_desc, s26_maskYF, s26_edgePts, s26_edgeTT, s26_raw, s26_masksTT, s26_autIdxTbls, s26_auts, s26_cuts, s26_cutSpecs, s26_cert⟩,
  ⟨s17_desc, 0, 0, 0, [], [], [], [], [], [], .term⟩,
]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem allEntries_meta_bool : allEntries.all (checkStateEntryDAG allStates) = true := by decide +kernel

theorem allEntries_certs : ∀ e ∈ allEntries, e.desc.edges.length ≤ 1 ∨
    chkCheckNode e.maskYF e.edgePts e.edgeTT e.raw e.masksTT e.cuts [] e.auts e.cert = true := by
  intro e he
  simp only [allEntries, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (by decide)
  · exact Or.inr cert_ok_1
  · exact Or.inr cert_ok_2
  · exact Or.inl (by decide)
  · exact Or.inr cert_ok_4
  · exact Or.inl (by decide)
  · exact Or.inr cert_ok_6
  · exact Or.inl (by decide)
  · exact Or.inl (by decide)
  · exact Or.inl (by decide)
  · exact Or.inl (by decide)
  · exact Or.inl (by decide)
  · exact Or.inl (by decide)
  · exact Or.inr cert_ok_13
  · exact Or.inl (by decide)
  · exact Or.inl (by decide)
  · exact Or.inl (by decide)
  · exact Or.inl (by decide)
  · exact Or.inr cert_ok_18
  · exact Or.inl (by decide)
  · exact Or.inl (by decide)
  · exact Or.inl (by decide)
  · exact Or.inr cert_ok_22
  · exact Or.inl (by decide)
  · exact Or.inl (by decide)
  · exact Or.inl (by decide)
  · exact Or.inr cert_ok_26
  · exact Or.inl (by decide)

theorem allStates_lb : ∀ (i : ℕ) (ch : StateDesc), allStates[i]? = some ch →
    OrCostLB ch.n ch.edges ch.forb (ch.edges.length - 1) :=
  allStates_orCostLB allEntries (List.all_eq_true.mp allEntries_meta_bool) allEntries_certs

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem allGraphCores_ok : allGraphCores.all (checkGraphCore allStates) = true := by decide +kernel

end OrYF
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
 theorem g28_or_ge_eight (C : Circuit) (hc : Monotone2 C)
    (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = OrYF.g28_fn x) :
    8 ≤ OrYF.countOrGates C.gates := by
  exact OrYF.graph_or_bound_of_entry OrYF.g28_fn_eq OrYF.allStates_lb
    OrYF.allGraphCores_ok 0 _ rfl rfl rfl C hc he
namespace Pin
open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def Ok (g : Gate) : Prop := (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

abbrev Stat := Sum Bool ℕ

def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | _ => (none, Sum.inl false)

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  all_goals simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or) (hlen : ins.length ≤ 2)
    (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 y) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Sum.inl false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Sum.inl false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

def initStats (n : ℕ) (v : Fin n) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => if i = v then Sum.inl b else Sum.inr i)

theorem inv_init (n : ℕ) (v : Fin n) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn (Function.update y v b)) (initStats n v b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  by_cases hlt : i < n
  · by_cases hv : (⟨i, hlt⟩ : Fin n) = v
    · subst hv
      simp [initStats, hlt, Stat.Valid, Stat.val]
    · simp [initStats, hlt, hv, Stat.Valid, Stat.val, wiresFrom, Function.update_of_ne hv]
  · rw [List.getD_eq_default _ _ (by simp [initStats]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

def isOr : GateOp → Bool
  | .or => true
  | _ => false

def orCount (gs : List Gate) : ℕ := gs.countP (fun g => isOr g.op)

theorem simplify_or_le (op : GateOp) (m : ℕ) (ins : List Stat) :
    orCount (simplify op m ins).1.toList ≤ if isOr op then 1 else 0 := by
  cases op <;> rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;>
    (try cases a) <;> (try cases b) <;>
    simp [simplify, simpAnd, simpOr, orCount, isOr]

theorem simplify_unpinned_eval (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (m : ℕ) (w : List Bool) (ins : List Stat) (vs : List Bool)
    (hlen : ins.length ≤ 2)
    (hr : List.Forall₂ (fun (s : Stat) b => s ≠ Sum.inl false → s.val w = b) ins vs)
    (hkeep : orCount (simplify op m ins).1.toList = if isOr op then 1 else 0)
    (hnf : (simplify op m ins).2 ≠ Sum.inl false) :
    op.eval (ins.map (Stat.val w)) = op.eval vs := by
  rcases hop with rfl | rfl
  all_goals
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · cases hr; rfl
    · cases hr with
      | cons ha ht =>
        cases ht
        cases a with
        | inl a => cases a <;> simp_all [simplify, simpAnd, simpOr, orCount, isOr, Stat.val, GateOp.eval]
        | inr a => simp_all [simplify, simpAnd, simpOr, orCount, isOr, Stat.val, GateOp.eval]
    · cases hr with
      | cons ha ht =>
        cases ht with
        | cons hb htt =>
          cases htt
          rcases a with ca | ia <;> rcases b with cb | ib
          · cases ca <;> cases cb <;>
              simp_all [simplify, simpAnd, simpOr, orCount, isOr, Stat.val, GateOp.eval]
          · cases ca <;>
              simp_all [simplify, simpAnd, simpOr, orCount, isOr, Stat.val, GateOp.eval]
          · cases cb <;>
              simp_all [simplify, simpAnd, simpOr, orCount, isOr, Stat.val, GateOp.eval]
          · simp_all [simplify, simpAnd, simpOr, orCount, isOr, Stat.val, GateOp.eval]
    · simp at hlen
theorem orCount_append (gs hs : List Gate) : orCount (gs ++ hs) = orCount gs + orCount hs := by
  simp [orCount]

theorem orCount_cons (g : Gate) (gs : List Gate) :
    orCount (g :: gs) = (if isOr g.op then 1 else 0) + orCount gs := by
  simp [orCount, List.countP_cons, Nat.add_comm]

theorem elim_or_le (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    orCount (elim n gs acc).2 ≤ orCount acc.2 + orCount gs := by
  induction gs with
  | nil => intro acc; simp [elim, orCount]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 := simplify_or_le g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
    change orCount (elim n gs (elimStep n acc g)).2 ≤ _
    rw [orCount_cons]
    have hstep : orCount (elimStep n acc g).2 = orCount acc.2 +
        orCount (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList := by
      simp only [elimStep, orCount_append]
    rw [hstep] at h1
    omega

def UInv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    ((acc.1.getD i (Sum.inl false)) ≠ Sum.inl false →
      (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 y) = w.getD i false)

theorem uinv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → UInv n y w acc →
      orCount (elim n gs acc).2 = orCount acc.2 + orCount gs →
      UInv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h _; exact h
  | cons g gs ih =>
    intro w acc hok h hcount
    have hle := elim_or_le n gs (elimStep n acc g)
    have hlocal := simplify_or_le g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
    have hcount' : orCount (elim n gs (elimStep n acc g)).2 =
        orCount acc.2 + ((if isOr g.op then 1 else 0) + orCount gs) := by
      simpa only [elim, List.foldl_cons, orCount_cons] using hcount
    have hstep : orCount (elimStep n acc g).2 = orCount acc.2 +
        orCount (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList := by
      simp only [elimStep, orCount_append]
    rw [hstep] at hle
    have hkeep : orCount (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList =
        if isOr g.op then 1 else 0 := by omega
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    · obtain ⟨hl, hi⟩ := h
      set w' := wiresFrom acc.2 y with hw'
      have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
      set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
      have hgok := hok g List.mem_cons_self
      have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
        (by
          intro s hs
          obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
          rw [lw']; exact (hi a).1)
      rw [lw'] at hs
      set r := simplify g.op (n + acc.2.length) ins with hr
      have hrel : List.Forall₂ (fun (s : Stat) b => s ≠ Sum.inl false → s.val w' = b)
          ins (g.inputs.map fun i => w.getD i false) := by
        rw [hins]
        induction g.inputs with
        | nil => exact List.Forall₂.nil
        | cons i is ih => exact List.Forall₂.cons (hi i).2 ih
      have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
        rw [wiresFrom_append]
      obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
      refine ⟨by simp [elimStep, hl], ?_⟩
      intro i
      show ((acc.1 ++ [r.2]).getD i (Sum.inl false)).Valid
          (n + (acc.2 ++ r.1.toList).length) ∧
        (((acc.1 ++ [r.2]).getD i (Sum.inl false)) ≠ Sum.inl false →
          ((acc.1 ++ [r.2]).getD i (Sum.inl false)).val
            (wiresFrom (acc.2 ++ r.1.toList) y) = _)
      rw [hnew, List.length_append, ← Nat.add_assoc]
      by_cases hil : i = acc.1.length
      · subst hil
        rw [getD_snoc_eq, hl, getD_snoc_eq]
        refine ⟨hs.1, ?_⟩
        intro hnf
        rw [hs.2]
        exact simplify_unpinned_eval g.op hgok.1 (n + acc.2.length) w' ins _
          (by simpa [hins] using hgok.2) hrel hkeep hnf
      · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
        refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
        intro hnf
        rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
        exact (hi i).2 hnf
    · rw [hstep]
      omega

theorem uinv_init (n : ℕ) (v : Fin n) (y : Fin n → Bool) :
    UInv n (List.ofFn y) (List.ofFn y) (initStats n v false, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  by_cases hlt : i < n
  · by_cases hv : (⟨i, hlt⟩ : Fin n) = v
    · subst hv
      simp [initStats, hlt, Stat.Valid, Stat.val]
    · simp [initStats, hlt, hv, Stat.Valid, Stat.val, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [initStats]; omega)]
    exact ⟨trivial, by simp⟩

theorem pin_or_strict (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (v : Fin n)
    (hmono : PEqualNP.MetaComplexity.Monotone2 C)
    (hdep : ∃ x : Fin n → Bool,
      C.eval (List.ofFn x) ≠ C.eval (List.ofFn (Function.update x v false)))
    (htrue : ∃ x : Fin n → Bool,
      C.eval (List.ofFn (Function.update x v false)) = true)
    (hfalse : ∃ x : Fin n → Bool,
      C.eval (List.ofFn (Function.update x v false)) = false) :
    ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 D ∧
      orCount D.gates + 1 ≤ orCount C.gates ∧
      ∀ x : Fin n → Bool,
        D.eval (List.ofFn x) = C.eval (List.ofFn (Function.update x v false)) := by
  have hok : ∀ g ∈ C.gates, Ok g := by
    intro g hg
    obtain ⟨h1, h2⟩ := hmono g hg
    refine ⟨?_, h2⟩
    simpa using h1
  set acc := elim n C.gates (initStats n v false, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn (Function.update y v false))) acc := by
    intro y
    exact inv_elim n _ (by simp) C.gates _ _ hok (inv_init n v false y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn y))
        = C.eval (List.ofFn (Function.update y v false)) := by
    intro y
    exact ((hinv y).2 C.output).2
  have hbound : orCount acc.2 ≤ orCount C.gates := by
    simpa only [← hacc, orCount, List.countP_nil, Nat.zero_add] using
      elim_or_le n C.gates (initStats n v false, [])
  have hstrict : orCount acc.2 < orCount C.gates := by
    by_contra hn
    have heq : orCount acc.2 = orCount C.gates := by omega
    obtain ⟨x, hx⟩ := hdep
    have hu : UInv n (List.ofFn x) (wiresFrom C.gates (List.ofFn x)) acc :=
      uinv_elim n _ (by simp) C.gates _ _ hok (uinv_init n v x)
        (by simpa only [← hacc, orCount, List.countP_nil, Nat.zero_add] using heq)
    have hst : acc.1.getD C.output (Sum.inl false) = Sum.inl false := by
      by_contra hh
      have ho := (hu.2 C.output).2 hh
      exact hx (ho.symm.trans (hval x))
    obtain ⟨y, hy⟩ := htrue
    have hv := hval y
    rw [hst] at hv
    simp only [Stat.val] at hv
    exact Bool.false_ne_true (hv.trans hy)
  have hmD : ∀ out : ℕ, PEqualNP.MetaComplexity.Monotone2 ⟨acc.2, out⟩ := by
    intro out g hg
    obtain ⟨h1, h2⟩ := elim_ok n C.gates _ (by simp) g hg
    refine ⟨?_, h2⟩
    rcases h1 with h | h <;> simp [h]
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    cases c with
    | true =>
      exfalso
      obtain ⟨y, hy⟩ := hfalse
      have hv := hval y
      rw [hst] at hv
      simp only [Stat.val] at hv
      exact Bool.false_ne_true (hv.trans hy).symm
    | false =>
      exfalso
      obtain ⟨y, hy⟩ := htrue
      have hv := hval y
      rw [hst] at hv
      simp only [Stat.val] at hv
      exact Bool.false_ne_true (hv.trans hy)
  | inr j =>
    refine ⟨⟨acc.2, j⟩, hmD _, by change orCount acc.2 + 1 ≤ orCount C.gates; omega, ?_⟩
    intro x
    have hv := hval x
    rw [hst] at hv
    exact hv

end Pin
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def rewire {n m : Nat} (rho : Fin n → Fin m) (j : Nat) : Nat :=
  if h : j < n then (rho ⟨j, h⟩).val else m + (j - n)

lemma rewire_lt {n m : Nat} (rho : Fin n → Fin m) (t j : Nat) :
    rewire rho j < m + t ↔ j < n + t := by
  unfold rewire
  split
  · rename_i h
    have := (rho ⟨j, h⟩).isLt
    omega
  · omega

lemma rewire_eq {n m : Nat} (rho : Fin n → Fin m) (t j : Nat) :
    rewire rho j = m + t ↔ j = n + t := by
  unfold rewire
  split
  · rename_i h
    have := (rho ⟨j, h⟩).isLt
    omega
  · omega

def relabelGate {n m : Nat} (rho : Fin n → Fin m) (g : Gate) : Gate :=
  {op := g.op, inputs := g.inputs.map (rewire rho)}

def relabelCircuit {n m : Nat} (rho : Fin n → Fin m) (C : Circuit) : Circuit :=
  {gates := C.gates.map (relabelGate rho), output := rewire rho C.output}

def wireFold (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma getD_snoc_relabel (w : List Bool) (b : Bool) (j : Nat) :
    (w ++ [b]).getD j false =
      if j < w.length then w.getD j false else if j = w.length then b else false := by
  split_ifs with h1 h2
  · exact List.getD_append _ _ _ _ h1
  · subst h2
    simp
  · rw [List.getD_eq_default]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

lemma rewire_append {n m : Nat} (rho : Fin n → Fin m) (t : Nat)
    (wold wnew : List Bool) (b : Bool)
    (hold : wold.length = n + t) (hnew : wnew.length = m + t)
    (hrel : ∀ j, wnew.getD (rewire rho j) false = wold.getD j false) :
    ∀ j, (wnew ++ [b]).getD (rewire rho j) false = (wold ++ [b]).getD j false := by
  intro j
  simp only [getD_snoc_relabel, hold, hnew, rewire_lt, rewire_eq]
  split_ifs <;> simp_all

lemma relabel_eval_gate {n m : Nat} (rho : Fin n → Fin m) (g : Gate)
    (wold wnew : List Bool)
    (hrel : ∀ j, wnew.getD (rewire rho j) false = wold.getD j false) :
    (relabelGate rho g).op.eval ((relabelGate rho g).inputs.map fun i => wnew.getD i false) =
      g.op.eval (g.inputs.map fun i => wold.getD i false) := by
  simp only [relabelGate, List.map_map]
  congr 1
  apply List.map_congr_left
  intro j _
  exact hrel j

lemma relabel_fold {n m : Nat} (rho : Fin n → Fin m) (gs : List Gate) :
    ∀ (t : Nat) (wold wnew : List Bool),
    wold.length = n + t → wnew.length = m + t →
    (∀ j, wnew.getD (rewire rho j) false = wold.getD j false) →
    ∀ j, (wireFold (gs.map (relabelGate rho)) wnew).getD (rewire rho j) false =
      (wireFold gs wold).getD j false := by
  induction gs with
  | nil => intro t wold wnew hold hnew hrel j; exact hrel j
  | cons g gs ih =>
      intro t wold wnew hold hnew hrel j
      simp only [List.map_cons, wireFold, List.foldl_cons]
      rw [relabel_eval_gate rho g wold wnew hrel]
      apply ih (t + 1)
      · simp [hold, Nat.add_assoc]
      · simp [hnew, Nat.add_assoc]
      · exact rewire_append rho t wold wnew _ hold hnew hrel

lemma rewire_input {n m : Nat} (rho : Fin n → Fin m) (x : Fin m → Bool) (j : Nat) :
    (List.ofFn x).getD (rewire rho j) false = (List.ofFn (fun i => x (rho i))).getD j false := by
  by_cases hj : j < n
  · simp only [rewire, dif_pos hj]
    rw [List.getD_eq_getElem _ _ (by simpa using (rho ⟨j, hj⟩).isLt)]
    rw [List.getD_eq_getElem _ _ (by simpa using hj)]
    simp only [List.getElem_ofFn]
  · simp only [rewire, dif_neg hj]
    rw [List.getD_eq_default _ _ (by simp only [List.length_ofFn]; omega)]
    rw [List.getD_eq_default _ _ (by simp only [List.length_ofFn]; omega)]

lemma relabelCircuit_eval {n m : Nat} (rho : Fin n → Fin m) (C : Circuit) (x : Fin m → Bool) :
    (relabelCircuit rho C).eval (List.ofFn x) = C.eval (List.ofFn (fun i => x (rho i))) := by
  exact relabel_fold rho C.gates 0 (List.ofFn (fun i => x (rho i))) (List.ofFn x)
    (by simp) (by simp) (rewire_input rho x) C.output

lemma relabelCircuit_mono {n m : Nat} (rho : Fin n → Fin m) (C : Circuit) (hC : Monotone2 C) :
    Monotone2 (relabelCircuit rho C) := by
  intro g hg
  obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
  simpa [relabelGate] using hC g0 hg0

lemma relabelCircuit_count {n m : Nat} (rho : Fin n → Fin m) (C : Circuit) (p : GateOp → Bool) :
    ((relabelCircuit rho C).gates.filter (fun g => p g.op)).length =
      (C.gates.filter (fun g => p g.op)).length := by
  simp only [relabelCircuit, List.filter_map, List.length_map]
  rfl

def deleteAmap : Fin 8 → Fin 7 := ![5, 0, 1, 6, 4, 2, 3, 0]

def t1Graph (x : Fin 8 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) ||
  (x 2 && x 5) || (x 2 && x 7) || (x 3 && x 6) || (x 4 && x 6) ||
  (x 4 && x 7) || (x 5 && x 7) || (x 6 && x 7)

def g28Graph (x : Fin 7 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) ||
  (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6) || (x 5 && x 6)

lemma deleteA_graph : ∀ x : Fin 7 → Bool,
    t1Graph (Function.update (fun i => x (deleteAmap i)) 1 false) = g28Graph x := by
  decide +kernel

lemma deleteA_circuit (D : Circuit)
    (hD : ∀ x : Fin 8 → Bool, D.eval (List.ofFn x) = t1Graph (Function.update x 1 false)) :
    ∀ x : Fin 7 → Bool, (relabelCircuit deleteAmap D).eval (List.ofFn x) = g28Graph x := by
  intro x
  rw [relabelCircuit_eval, hD, deleteA_graph]


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma or_counts_agree (gs : List Gate) : Pin.orCount gs = OrYF.countOrGates gs := by
  simp only [Pin.orCount, OrYF.countOrGates, List.countP_eq_length_filter]
  rfl

lemma relabel_or_count {n m : Nat} (rho : Fin n → Fin m) (D : Circuit) :
    Pin.orCount (relabelCircuit rho D).gates = Pin.orCount D.gates := by
  simp only [Pin.orCount, List.countP_eq_length_filter]
  exact relabelCircuit_count rho D Pin.isOr

lemma t1_or_count_ge_nine (C : Circuit) (hmono : Monotone2 C)
    (hfun : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = t1Graph x) :
    9 ≤ Pin.orCount C.gates := by
  have hdep : ∃ x : Fin 8 → Bool,
      C.eval (List.ofFn x) ≠ C.eval (List.ofFn (Function.update x 1 false)) := by
    refine ⟨![true, true, false, false, false, false, false, false], ?_⟩
    rw [hfun, hfun]
    decide
  have htrue : ∃ x : Fin 8 → Bool,
      C.eval (List.ofFn (Function.update x 1 false)) = true := by
    refine ⟨![true, false, true, false, false, false, false, false], ?_⟩
    rw [hfun]
    decide
  have hfalse : ∃ x : Fin 8 → Bool,
      C.eval (List.ofFn (Function.update x 1 false)) = false := by
    refine ⟨fun _ => false, ?_⟩
    rw [hfun]
    decide
  obtain ⟨D, hmD, hless, hD⟩ := Pin.pin_or_strict 8 C 1 hmono hdep htrue hfalse
  have hDfun : ∀ x : Fin 8 → Bool, D.eval (List.ofFn x) = t1Graph (Function.update x 1 false) := by
    intro x
    rw [hD, hfun]
  have hseven : ∀ x : Fin 7 → Bool,
      (relabelCircuit deleteAmap D).eval (List.ofFn x) = OrYF.g28_fn x :=
    deleteA_circuit D hDfun
  have h8 := g28_or_ge_eight (relabelCircuit deleteAmap D)
    (relabelCircuit_mono deleteAmap D hmD) hseven
  rw [← or_counts_agree, relabel_or_count] at h8
  omega

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma isOr_eq_true (op : GateOp) : Pin.isOr op = true ↔ op = GateOp.or := by
  cases op <;> simp [Pin.isOr]

lemma filter_isOr_length_eq_card (gs : List Gate) :
    (gs.filter (fun g => Pin.isOr g.op)).length =
      Nat.card {j : Fin gs.length // (gs.get j).op = GateOp.or} := by
  classical
  have hsum : (gs.filter (fun g => Pin.isOr g.op)).length =
      ∑ j : Fin gs.length, if Pin.isOr (gs.get j).op = true then 1 else 0 := by
    induction gs with
    | nil => simp
    | cons g gs ih =>
      simp only [List.get_eq_getElem] at ih ⊢
      change (List.filter (fun g => Pin.isOr g.op) (g :: gs)).length =
          ∑ j : Fin (gs.length + 1), if Pin.isOr ((g :: gs)[j.val]).op = true then 1 else 0
      rw [Fin.sum_univ_succ]
      simp only [List.filter_cons, Fin.val_zero, List.getElem_cons_zero,
        Fin.val_succ, List.getElem_cons_succ, ← ih]
      by_cases hg : Pin.isOr g.op = true <;> simp [hg, Nat.add_comm]
  have hsum' : (∑ j : Fin gs.length, if Pin.isOr (gs.get j).op = true then 1 else 0) =
      ∑ j : Fin gs.length, if (gs.get j).op = GateOp.or then 1 else 0 := by
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [isOr_eq_true]
  rw [hsum, hsum', Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]

lemma count_converted_or {n : Nat} (ops : Fin n → Bool) (a b : Fin n → Nat) :
    Nat.card {j : Fin (convertedGates ops a b).length //
      ((convertedGates ops a b).get j).op = GateOp.or} =
    Nat.card {i : Fin n // ops i = false} := by
  apply Nat.card_congr
  refine (finCongr (by simp [convertedGates])).subtypeEquiv ?_
  intro i
  have hi : i.val < n := by simpa [convertedGates] using i.isLt
  change ((List.ofFn (convertedGate ops a b))[i.val]'(by simpa [convertedGates] using i.isLt)).op = GateOp.or ↔ _
  simp only [List.getElem_ofFn]
  change (if ops ⟨i.val, hi⟩ then GateOp.and else GateOp.or) = GateOp.or ↔ ops ⟨i.val, hi⟩ = false
  cases h : ops ⟨i.val, hi⟩ <;> simp [h]

lemma converted_or_count {n : Nat} (ops : Fin n → Bool) (a b : Fin n → Nat) :
    Pin.orCount (convertedGates ops a b) = Nat.card {i : Fin n // ops i = false} := by
  rw [Pin.orCount, List.countP_eq_length_filter, filter_isOr_length_eq_card, count_converted_or]

lemma witness_or_count_ge_nine
    (ops : Fin 14 → Bool) (a b : Fin 14 → Fin 33) (v : Nat → Nat)
    (hbase : ∀ i : Fin 11, v i.val = baseValues.getD i.val 0)
    (ha : ∀ i, (a i).val ∈ allowedInputs ∨ 11 ≤ (a i).val)
    (hb : ∀ i, (b i).val ∈ allowedInputs ∨ 11 ≤ (b i).val)
    (hs : ∀ i, (a i).val < 11 + i.val ∧ (b i).val < 11 + i.val ∧
      v (11 + i.val) = if ops i then v (a i).val &&& v (b i).val else v (a i).val ||| v (b i).val)
    (hout : v 24 = 36671) :
    9 ≤ Nat.card {i : Fin 14 // ops i = false} := by
  let D : Circuit := { gates := convertedGates ops (fun i => (a i).val) (fun i => (b i).val), output := 21 }
  have hgates := convertedGates_ops ops (fun i => (a i).val) (fun i => (b i).val)
  have hmD : Monotone2 D := by
    intro g hg
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
    cases h : ops i <;> simp [convertedGate, h]
  have hsample : ∀ k : Fin 40, circuitFun 8 D (sample k) = (36671 : Nat).testBit k.val := by
    intro k
    change (wiresFrom (convertedGates ops (fun i => (a i).val) (fun i => (b i).val))
      (List.ofFn (sample k))).getD 21 false = _
    rw [converted_eval ops (fun i => (a i).val) (fun i => (b i).val) v hbase ha hb hs k]
    have hlookup := bitWires_lookup (n := 14) v k 24 hbase (by decide) (Or.inr (by decide))
    have hidx : wireIndex 24 = 21 := by decide
    rw [hidx, hout] at hlookup
    exact hlookup
  have hcompute := samples_determine (circuitFun 8 D) (circuit_mono D hgates) hsample
  have htarget : targetFun = t1Graph := by
    funext x
    simp [targetFun, edgesT1, t1Graph, Bool.or_assoc]
  have hfun : ∀ x : Fin 8 → Bool, D.eval (List.ofFn x) = t1Graph x := by
    intro x
    exact (congrFun hcompute x).trans (congrFun htarget x)
  have h9 := t1_or_count_ge_nine D hmD hfun
  change 9 ≤ Pin.orCount (convertedGates ops (fun i => (a i).val) (fun i => (b i).val)) at h9
  rwa [converted_or_count] at h9

lemma bool_index_counts {n : Nat} (ops : Fin n → Bool) :
    Nat.card {i : Fin n // ops i = true} + Nat.card {i : Fin n // ops i = false} = n := by
  have h := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i : Fin n => ops i = true)
  simpa [Nat.card_eq_fintype_card, Fintype.card_subtype] using h

lemma witness_exact_gate_counts
    (ops : Fin 14 → Bool) (a b : Fin 14 → Fin 33) (v : Nat → Nat)
    (hbase : ∀ i : Fin 11, v i.val = baseValues.getD i.val 0)
    (ha : ∀ i, (a i).val ∈ allowedInputs ∨ 11 ≤ (a i).val)
    (hb : ∀ i, (b i).val ∈ allowedInputs ∨ 11 ≤ (b i).val)
    (hs : ∀ i, (a i).val < 11 + i.val ∧ (b i).val < 11 + i.val ∧
      v (11 + i.val) = if ops i then v (a i).val &&& v (b i).val else v (a i).val ||| v (b i).val)
    (hout : v 24 = 36671) :
    Nat.card {i : Fin 14 // ops i = true} = 5 ∧ Nat.card {i : Fin 14 // ops i = false} = 9 := by
  have hA := witness_and_count_ge_five ops a b v hbase ha hb hs hout
  have hO := witness_or_count_ge_nine ops a b v hbase ha hb hs hout
  have hsum := bool_index_counts ops
  omega

end PEqualNP.Outside.L_meta_9033_aux
