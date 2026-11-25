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

end PEqualNP.Outside.L_meta_9033_aux
