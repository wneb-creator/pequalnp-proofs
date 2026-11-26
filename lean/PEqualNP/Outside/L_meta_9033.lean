import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_9033_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit
private def isAnd : GateOp → Bool
 | GateOp.and => true
 | _ => false
private lemma zaa (op : GateOp) : isAnd op = true ↔ op = GateOp.and := by
 cases op <;> simp [isAnd]
private lemma zab (gs : List Gate) :
  (gs.filter (fun g => isAnd g.op)).length =
   Nat.card {j : Fin gs.length // (gs.get j).op = GateOp.and} := by
 classical
 have yY : (gs.filter (fun g => isAnd g.op)).length =
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
 have vI : (∑ j : Fin gs.length, if isAnd (gs.get j).op = true then 1 else 0) =
   ∑ j : Fin gs.length, if (gs.get j).op = GateOp.and then 1 else 0 := by
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [zaa]
 rw [yY, vI, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
private abbrev Side := Finset (Fin 8) × Finset ℕ
private abbrev zac := Side × Side
private abbrev WireRep := Option Side
private def defSide : Side := (∅, ∅)
private def defRep : WireRep := some defSide
private def defSpec : zac := (defSide, defSide)
private def sideVal (U : Finset (Fin 8)) (gv : List Bool) (s : Side) : Bool :=
 decide ((∃ v ∈ s.1, v ∈ U) ∨ ∃ j ∈ s.2, gv.getD j false = true)
private def repVal (U : Finset (Fin 8)) (gv : List Bool) : WireRep → Bool
 | none => true
 | some s => sideVal U gv s
private def zad (U : Finset (Fin 8)) (gv : List Bool) (sp : zac) : List Bool :=
 gv ++ [sideVal U gv sp.1 && sideVal U gv sp.2]
private def zae (specs : List zac) (U : Finset (Fin 8)) : List Bool :=
 specs.foldl (zad U) []
private def SideWF (k : ℕ) (s : Side) : Prop :=
 ∀ j ∈ s.2, j < k
private def RepWF (k : ℕ) : WireRep → Prop
 | none => True
 | some s => SideWF k s
private def SpecsWF (specs : List zac) : Prop :=
 ∀ j < specs.length, SideWF j (specs.getD j defSpec).1 ∧ SideWF j (specs.getD j defSpec).2
private lemma zaf {k k' : ℕ} (hk : k ≤ k') {s : Side} (h : SideWF k s) : SideWF k' s :=
 fun j hj => lt_of_lt_of_le (h j hj) hk
private lemma zag {k k' : ℕ} (hk : k ≤ k') {r : WireRep} (h : RepWF k r) : RepWF k' r := by
 cases r with
 | none => trivial
 | some s => exact zaf hk h
private lemma zah {α : Type*} (l : List α) (x d : α) (j : ℕ) (hj : j < l.length) :
  (l ++ [x]).getD j d = l.getD j d := by
 simp [List.getD, List.getElem?_append_left hj]
private lemma zai {α : Type*} (l : List α) (x d : α) :
  (l ++ [x]).getD l.length d = x := by
 simp [List.getD]
private lemma zaj {α : Type*} (l : List α) (x d : α) (j : ℕ) (hj : l.length < j) :
  (l ++ [x]).getD j d = d := by
 have hj' : (l ++ [x]).length ≤ j := by simp; omega
 simp [List.getD, List.getElem?_eq_none hj']
private lemma zak (U : Finset (Fin 8)) (gv : List Bool) (b : Bool) (s : Side)
  (hs : SideWF gv.length s) :
  sideVal U (gv ++ [b]) s = sideVal U gv s := by
 unfold sideVal
 refine decide_eq_decide.mpr ?_
 constructor
 ·rintro (h | ⟨j, hj, hgv⟩)
  ·exact Or.inl h
  ·exact Or.inr ⟨j, hj, by rwa [← zah gv b false j (hs j hj)]⟩
 ·rintro (h | ⟨j, hj, hgv⟩)
  ·exact Or.inl h
  ·exact Or.inr ⟨j, hj, by rwa [zah gv b false j (hs j hj)]⟩
private lemma zal (U : Finset (Fin 8)) (gv : List Bool) (b : Bool) (r : WireRep)
  (hr : RepWF gv.length r) :
  repVal U (gv ++ [b]) r = repVal U gv r := by
 cases r with
 | none => rfl
 | some s => exact zak U gv b s hr
private lemma zam (specs : List zac) (U : Finset (Fin 8)) :
  (zae specs U).length = specs.length := by
 induction specs using List.reverseRecOn with
 | nil => rfl
 | append_singleton specs sp ih =>
  unfold zae at ih ⊢
  rw [List.foldl_concat]
  simp [zad, ih]
private lemma zan (specs : List zac) (sp : zac) (U : Finset (Fin 8)) :
  zae (specs ++ [sp]) U =
   zae specs U ++ [sideVal U (zae specs U) sp.1 && sideVal U (zae specs U) sp.2] := by
 unfold zae
 rw [List.foldl_concat]
 rfl
private lemma zao {specs : List zac} {sp : zac} (h : SpecsWF (specs ++ [sp])) :
  SpecsWF specs ∧ SideWF specs.length sp.1 ∧ SideWF specs.length sp.2 := by
 refine ⟨fun j hj => ?_, ?_, ?_⟩
 ·have hj' : j < (specs ++ [sp]).length := by simp; omega
  have h1 := h j hj'
  rwa [zah specs sp defSpec j hj] at h1
 ·have hlt : specs.length < (specs ++ [sp]).length := by simp
  have h1 := (h specs.length hlt).1
  rwa [zai] at h1
 ·have hlt : specs.length < (specs ++ [sp]).length := by simp
  have h1 := (h specs.length hlt).2
  rwa [zai] at h1
private lemma zap (specs : List zac) (U : Finset (Fin 8)) (hwf : SpecsWF specs)
  (j : ℕ) (hj : j < specs.length) :
  (zae specs U).getD j false =
   (sideVal U (zae specs U) (specs.getD j defSpec).1 &&
    sideVal U (zae specs U) (specs.getD j defSpec).2) := by
 induction specs using List.reverseRecOn generalizing j with
 | nil => simp at hj
 | append_singleton specs sp ih =>
  obtain ⟨vL, hwfl, hwfr⟩ := zao hwf
  rw [zan]
  have qe : (zae specs U).length = specs.length := zam specs U
  simp only [List.length_append, List.length_singleton] at hj
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
  ·rw [zah _ _ _ j (qe ▸ hlt), zah specs sp defSpec j hlt]
   have h1 := zaf (Nat.le_of_lt hlt) (vL j hlt).1
   have h2 := zaf (Nat.le_of_lt hlt) (vL j hlt).2
   rw [zak U _ _ _ (qe ▸ h1),
    zak U _ _ _ (qe ▸ h2)]
   exact ih vL j hlt
  ·rw [← qe, zai, qe, zai,
    zak U _ _ _ (qe ▸ hwfl),
    zak U _ _ _ (qe ▸ hwfr)]
private def zaq : WireRep → WireRep → WireRep
 | none, _ => none
 | _, none => none
 | some (b1, f1), some (b2, f2) => some (b1 ∪ b2, f1 ∪ f2)
private lemma zar (U : Finset (Fin 8)) (gv : List Bool) (r1 r2 : WireRep) :
  repVal U gv (zaq r1 r2) = (repVal U gv r1 || repVal U gv r2) := by
 cases r1 with
 | none => simp [zaq, repVal]
 | some s1 =>
  cases r2 with
  | none => simp [zaq, repVal]
  | some s2 =>
   rcases s1 with ⟨b1, f1⟩
   rcases s2 with ⟨b2, f2⟩
   simp only [zaq, repVal, sideVal]
   rw [Bool.eq_iff_iff, Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq, decide_eq_true_eq]
   constructor
   ·rintro (⟨v, hv, hvU⟩ | ⟨j, hj, hgv⟩)
    ·rcases Finset.mem_union.mp hv with hv | hv
     ·exact Or.inl (Or.inl ⟨v, hv, hvU⟩)
     ·exact Or.inr (Or.inl ⟨v, hv, hvU⟩)
    ·rcases Finset.mem_union.mp hj with hj | hj
     ·exact Or.inl (Or.inr ⟨j, hj, hgv⟩)
     ·exact Or.inr (Or.inr ⟨j, hj, hgv⟩)
   ·rintro ((⟨v, hv, hvU⟩ | ⟨j, hj, hgv⟩) | (⟨v, hv, hvU⟩ | ⟨j, hj, hgv⟩))
    ·exact Or.inl ⟨v, Finset.mem_union_left b2 hv, hvU⟩
    ·exact Or.inr ⟨j, Finset.mem_union_left f2 hj, hgv⟩
    ·exact Or.inl ⟨v, Finset.mem_union_right b1 hv, hvU⟩
    ·exact Or.inr ⟨j, Finset.mem_union_right f1 hj, hgv⟩
private lemma zas {k : ℕ} {r1 r2 : WireRep} (h1 : RepWF k r1) (h2 : RepWF k r2) :
  RepWF k (zaq r1 r2) := by
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
   ·exact h1 j hj
   ·exact h2 j hj
private def zat (qy : List WireRep) (ins : List ℕ) : WireRep :=
 ins.foldl (fun acc i => zaq acc (qy.getD i defRep)) defRep
private lemma zau (U : Finset (Fin 8)) (gv : List Bool) (qy : List WireRep)
  (ins : List ℕ) (acc : WireRep) :
  repVal U gv (ins.foldl (fun a i => zaq a (qy.getD i defRep)) acc) =
   (repVal U gv acc || ins.any (fun i => repVal U gv (qy.getD i defRep))) := by
 induction ins generalizing acc with
 | nil => simp
 | cons a ins ih =>
  simp only [List.foldl_cons, List.any_cons]
  rw [ih (zaq acc (qy.getD a defRep)), zar, Bool.or_assoc]
private lemma zav (U : Finset (Fin 8)) (gv : List Bool) :
  repVal U gv defRep = false := by
 simp [defRep, defSide, repVal, sideVal]
private lemma zaw (U : Finset (Fin 8)) (gv : List Bool) (qy : List WireRep)
  (ins : List ℕ) :
  repVal U gv (zat qy ins) = ins.any (fun i => repVal U gv (qy.getD i defRep)) := by
 unfold zat
 rw [zau, zav, Bool.false_or]
private lemma zax (k : ℕ) : RepWF k defRep := by
 intro j hj
 exact absurd hj (Finset.notMem_empty j)
private lemma zay (k : ℕ) (qy : List WireRep) (qU : ∀ r ∈ qy, RepWF k r)
  (ins : List ℕ) : RepWF k (zat qy ins) := by
 have va : ∀ (l : List ℕ) (acc : WireRep), RepWF k acc →
   RepWF k (l.foldl (fun a i => zaq a (qy.getD i defRep)) acc) := by
  intro l
  induction l with
  | nil => intro acc q4; exact q4
  | cons a l ih =>
   intro acc q4
   apply ih
   apply zas q4
   by_cases ha : a < qy.length
   ·simpa [List.getD, ha] using qU qy[a] (List.getElem_mem ha)
   ·have hge : qy.length ≤ a := Nat.le_of_not_lt ha
    simp only [List.getD, List.getElem?_eq_none hge, Option.getD_none]
    exact zax k
 exact va ins defRep (zax k)
private def zaz (st : List WireRep × List zac) (g : Gate) :
  List WireRep × List zac :=
 match g.op with
 | GateOp.or => (st.1 ++ [zat st.1 g.inputs], st.2)
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
private lemma zaA {k : ℕ} {qy : List WireRep} (qU : ∀ r ∈ qy, RepWF k r) (a : ℕ) :
  RepWF k (qy.getD a defRep) := by
 by_cases ha : a < qy.length
 ·simpa [List.getD, ha] using qU qy[a] (List.getElem_mem ha)
 ·have hge : qy.length ≤ a := Nat.le_of_not_lt ha
  simp only [List.getD, List.getElem?_eq_none hge, Option.getD_none]
  exact zax k
private lemma zaB (qy : List WireRep) (specs : List zac)
  (w : Finset (Fin 8) → List Bool) (g : Gate)
  (hg : (g.op = GateOp.and ∧ g.inputs.length ≤ 2) ∨ g.op = GateOp.or)
  (hwf : SpecsWF specs) (qU : ∀ r ∈ qy, RepWF specs.length r)
  (qe : ∀ U, (w U).length = qy.length)
  (heq : ∀ U i, repVal U (zae specs U) (qy.getD i defRep) = (w U).getD i false) :
  let st' := zaz (qy, specs) g
  let w' := fun U => w U ++ [g.op.eval (g.inputs.map fun i => (w U).getD i false)]
  SpecsWF st'.2 ∧ (∀ r ∈ st'.1, RepWF st'.2.length r) ∧
  (∀ U, (w' U).length = st'.1.length) ∧
  (∀ U i, repVal U (zae st'.2 U) (st'.1.getD i defRep) = (w' U).getD i false) ∧
  st'.2.length ≤ specs.length + (if isAnd g.op then 1 else 0) := by
 rcases hg with ⟨hop, hlen2⟩ | hop
 ·rw [hop]
  rcases hins : g.inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
  ·simp only [zaz, GateOp.eval, hop, hins, List.map_nil, List.all_nil, isAnd, ↓reduceIte]
   refine ⟨hwf, ?_, ?_, ?_, Nat.le_add_right _ _⟩
   ·intro r hr
    rcases List.mem_append.mp hr with hr | hr
    ·exact qU r hr
    ·rw [List.mem_singleton.mp hr]; trivial
   ·intro U; simp [qe U]
   ·intro U i
    rcases Nat.lt_trichotomy i qy.length with hlt | rfl | hgt
    ·rw [zah _ _ _ i hlt, zah _ _ _ i (by rw [qe]; exact hlt)]
     exact heq U i
    ·rw [zai, ← qe U, zai]
     rfl
    ·rw [zaj _ _ _ i hgt, zaj _ _ _ i (by rw [qe]; exact hgt)]
     exact zav U _
  ·simp only [zaz, GateOp.eval, hop, hins, List.map_cons, List.map_nil, List.all_cons,
    List.all_nil, id_eq, Bool.and_true, isAnd, ↓reduceIte]
   refine ⟨hwf, ?_, ?_, ?_, Nat.le_add_right _ _⟩
   ·intro r hr
    rcases List.mem_append.mp hr with hr | hr
    ·exact qU r hr
    ·rw [List.mem_singleton.mp hr]
     exact zaA qU a
   ·intro U; simp [qe U]
   ·intro U i
    rcases Nat.lt_trichotomy i qy.length with hlt | rfl | hgt
    ·rw [zah _ _ _ i hlt, zah _ _ _ i (by rw [qe]; exact hlt)]
     exact heq U i
    ·rw [zai, ← qe U, zai]
     exact heq U a
    ·rw [zaj _ _ _ i hgt, zaj _ _ _ i (by rw [qe]; exact hgt)]
     exact zav U _
  ·simp only [zaz, GateOp.eval, hop, hins, List.map_cons, List.map_nil, List.all_cons,
    List.all_nil, id_eq, Bool.and_true, isAnd, ↓reduceIte]
   have y6 : RepWF specs.length (qy.getD a defRep) := zaA qU a
   have vb : RepWF specs.length (qy.getD b defRep) := zaA qU b
   cases hra : qy.getD a defRep with
   | none =>
    dsimp only
    have hwa : ∀ U, (w U).getD a false = true := fun U => by
     rw [← heq U a, hra]; rfl
    refine ⟨hwf, ?_, ?_, ?_, Nat.le_add_right _ _⟩
    ·intro r hr
     rcases List.mem_append.mp hr with hr | hr
     ·exact qU r hr
     ·rw [List.mem_singleton.mp hr]; exact vb
    ·intro U; simp [qe U]
    ·intro U i
     rcases Nat.lt_trichotomy i qy.length with hlt | rfl | hgt
     ·rw [zah _ _ _ i hlt, zah _ _ _ i (by rw [qe]; exact hlt)]
      exact heq U i
     ·rw [zai, ← qe U, zai, hwa U, Bool.true_and]
      exact heq U b
     ·rw [zaj _ _ _ i hgt, zaj _ _ _ i (by rw [qe]; exact hgt)]
      exact zav U _
   | some s1 =>
    cases hrb : qy.getD b defRep with
    | none =>
     dsimp only
     have hwb : ∀ U, (w U).getD b false = true := fun U => by
      rw [← heq U b, hrb]; rfl
     refine ⟨hwf, ?_, ?_, ?_, Nat.le_add_right _ _⟩
     ·intro r hr
      rcases List.mem_append.mp hr with hr | hr
      ·exact qU r hr
      ·rw [List.mem_singleton.mp hr]; rw [← hra]; exact y6
     ·intro U; simp [qe U]
     ·intro U i
      rcases Nat.lt_trichotomy i qy.length with hlt | rfl | hgt
      ·rw [zah _ _ _ i hlt, zah _ _ _ i (by rw [qe]; exact hlt)]
       exact heq U i
      ·rw [zai, ← qe U, zai, hwb U, Bool.and_true, ← hra]
       exact heq U a
      ·rw [zaj _ _ _ i hgt, zaj _ _ _ i (by rw [qe]; exact hgt)]
       exact zav U _
    | some s2 =>
     dsimp only
     have hs1 : SideWF specs.length s1 := by rw [hra] at y6; exact y6
     have hs2 : SideWF specs.length s2 := by rw [hrb] at vb; exact vb
     have tD : SpecsWF (specs ++ [(s1, s2)]) := by
      intro j hj
      simp only [List.length_append, List.length_singleton] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
      ·rw [zah specs _ defSpec j hlt]
       exact hwf j hlt
      ·rw [zai]
       exact ⟨hs1, hs2⟩
     refine ⟨tD, ?_, ?_, ?_, by simp⟩
     ·intro r hr
      rcases List.mem_append.mp hr with hr | hr
      ·exact zag (by simp) (qU r hr)
      ·rw [List.mem_singleton.mp hr]
       intro j hj
       rw [Finset.mem_singleton.mp hj]
       simp
     ·intro U; simp [qe U]
     ·intro U i
      have qH : zae (specs ++ [(s1, s2)]) U =
        zae specs U ++
         [sideVal U (zae specs U) s1 && sideVal U (zae specs U) s2] :=
       zan specs (s1, s2) U
      have xY : (zae specs U).length = specs.length := zam specs U
      rcases Nat.lt_trichotomy i qy.length with hlt | rfl | hgt
      ·rw [zah _ _ _ i hlt, zah _ _ _ i (by rw [qe]; exact hlt),
        qH, zal U _ _ _ (xY ▸ zaA qU i)]
       exact heq U i
      ·rw [zai, ← qe U, zai, qH]
       have hva : sideVal U (zae specs U) s1 = (w U).getD a false := by
        have := heq U a
        rwa [hra] at this
       have hvb : sideVal U (zae specs U) s2 = (w U).getD b false := by
        have := heq U b
        rwa [hrb] at this
       rw [← hva, ← hvb]
       simp only [repVal, sideVal, Finset.notMem_empty, false_and, exists_false,
        Finset.mem_singleton, exists_eq_left, false_or]
       rw [← xY, zai]
       simp
      ·rw [zaj _ _ _ i hgt, zaj _ _ _ i (by rw [qe]; exact hgt)]
       exact zav U _
  ·rw [hins] at hlen2
   simp at hlen2
 ·rw [hop]
  simp only [zaz, GateOp.eval, hop, isAnd, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
  refine ⟨hwf, ?_, ?_, ?_, le_rfl⟩
  ·intro r hr
   rcases List.mem_append.mp hr with hr | hr
   ·exact qU r hr
   ·rw [List.mem_singleton.mp hr]
    exact zay specs.length qy qU g.inputs
  ·intro U; simp [qe U]
  ·intro U i
   rcases Nat.lt_trichotomy i qy.length with hlt | rfl | hgt
   ·rw [zah _ _ _ i hlt, zah _ _ _ i (by rw [qe]; exact hlt)]
    exact heq U i
   ·rw [zai, ← qe U, zai, zaw]
    rw [List.any_map]
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, Function.comp_def, id_eq]
    exact ⟨fun ⟨k, hk, h⟩ => ⟨k, hk, (heq U k) ▸ h⟩,
     fun ⟨k, hk, h⟩ => ⟨k, hk, (heq U k).symm ▸ h⟩⟩
   ·rw [zaj _ _ _ i hgt, zaj _ _ _ i (by rw [qe]; exact hgt)]
    exact zav U _
private lemma zaC (gs : List Gate)
  (qp : ∀ g ∈ gs, (g.op = GateOp.and ∧ g.inputs.length ≤ 2) ∨ g.op = GateOp.or)
  (qy : List WireRep) (specs : List zac) (w : Finset (Fin 8) → List Bool)
  (hwf : SpecsWF specs) (qU : ∀ r ∈ qy, RepWF specs.length r)
  (qe : ∀ U, (w U).length = qy.length)
  (heq : ∀ U i, repVal U (zae specs U) (qy.getD i defRep) = (w U).getD i false) :
  let st' := gs.foldl zaz (qy, specs)
  let w' := fun U => gs.foldl (fun ww g => ww ++ [g.op.eval (g.inputs.map fun i => ww.getD i false)]) (w U)
  SpecsWF st'.2 ∧ (∀ r ∈ st'.1, RepWF st'.2.length r) ∧
  (∀ U, (w' U).length = st'.1.length) ∧
  (∀ U i, repVal U (zae st'.2 U) (st'.1.getD i defRep) = (w' U).getD i false) ∧
  st'.2.length ≤ specs.length + (gs.filter (fun g => isAnd g.op)).length := by
 induction gs generalizing qy specs w with
 | nil =>
  exact ⟨hwf, qU, qe, heq, Nat.le_refl _⟩
 | cons g gs ih =>
  have hg : (g.op = GateOp.and ∧ g.inputs.length ≤ 2) ∨ g.op = GateOp.or :=
   qp g List.mem_cons_self
  have qY : ∀ g' ∈ gs, (g'.op = GateOp.and ∧ g'.inputs.length ≤ 2) ∨ g'.op = GateOp.or :=
   fun g' hg' => qp g' (List.mem_cons_of_mem g hg')
  obtain ⟨hwf1, hreps1, hlen1, heq1, hcnt1⟩ :=
   zaB qy specs w g hg hwf qU qe heq
  obtain ⟨hwf2, hreps2, hlen2, heq2, hcnt2⟩ :=
   ih qY _ _ _ hwf1 hreps1 hlen1 heq1
  refine ⟨hwf2, hreps2, hlen2, heq2, ?_⟩
  simp only [List.filter_cons]
  cases ha : isAnd g.op <;> simp only [ha, ↓reduceIte, Bool.false_eq_true] at hcnt1 ⊢
  ·exact le_trans hcnt2 (by omega)
  ·rw [List.length_cons]
   exact le_trans hcnt2 (by omega)
private def zaD (k : ℕ) (F : Finset ℕ) : Finset (Fin k) :=
 Finset.univ.filter (fun j : Fin k => j.val ∈ F)
private lemma zaE {k : ℕ} {F : Finset ℕ} {j : Fin k} :
  j ∈ zaD k F ↔ j.val ∈ F := by
 simp [zaD]
private lemma zaF (specs : List zac) (hwf : SpecsWF specs)
  (xH : Side) (ub : SideWF specs.length xH)
  (U : Finset (Fin 8)) :
  let C : AndCountCircuit 8 :=
   {size := specs.length
    leftVars := fun i => (specs.getD i.val defSpec).1.1
    leftGates := fun i => zaD specs.length (specs.getD i.val defSpec).1.2
    rightVars := fun i => (specs.getD i.val defSpec).2.1
    rightGates := fun i => zaD specs.length (specs.getD i.val defSpec).2.2
    outVars := xH.1
    outGates := zaD specs.length xH.2 }
  C.WellFormed ∧ ∀ d (i : Fin C.size), i.val < d → C.gateValFuel U d i = (zae specs U).getD i.val false := by
 intro C
 have u8 : C.WellFormed := by
  intro i
  have hsp := hwf i.val i.isLt
  constructor
  ·intro j hj
   exact hsp.1 j.val (zaE.mp hj)
  ·intro j hj
   exact hsp.2 j.val (zaE.mp hj)
 refine ⟨u8, ?_⟩
 intro d
 induction d with
 | zero => intro i hi; omega
 | succ d ih =>
  intro i hi
  have hsp := hwf i.val i.isLt
  simp only [AndCountCircuit.gateValFuel]
  rw [zap specs U hwf i.val i.isLt]
  congr 1
  ·unfold AndCountCircuit.sideTrue sideVal
   refine decide_eq_decide.mpr ?_
   constructor
   ·rintro (h | ⟨j, hj, hji, hgv⟩)
    ·exact Or.inl h
    ·have zx : j.val < d := Nat.lt_of_lt_of_le hji (Nat.lt_succ_iff.mp hi)
     rw [ih j zx] at hgv
     exact Or.inr ⟨j.val, zaE.mp hj, hgv⟩
   ·rintro (h | ⟨j, hj, hgv⟩)
    ·exact Or.inl h
    ·have hji : j < i.val := hsp.1 j hj
     have zx : j < specs.length := Nat.lt_trans hji i.isLt
     refine Or.inr ⟨⟨j, zx⟩, zaE.mpr hj, hji, ?_⟩
     rw [ih ⟨j, zx⟩ (Nat.lt_of_lt_of_le hji (Nat.lt_succ_iff.mp hi))]
     exact hgv
  ·unfold AndCountCircuit.sideTrue sideVal
   refine decide_eq_decide.mpr ?_
   constructor
   ·rintro (h | ⟨j, hj, hji, hgv⟩)
    ·exact Or.inl h
    ·have zx : j.val < d := Nat.lt_of_lt_of_le hji (Nat.lt_succ_iff.mp hi)
     rw [ih j zx] at hgv
     exact Or.inr ⟨j.val, zaE.mp hj, hgv⟩
   ·rintro (h | ⟨j, hj, hgv⟩)
    ·exact Or.inl h
    ·have hji : j < i.val := hsp.2 j hj
     have zx : j < specs.length := Nat.lt_trans hji i.isLt
     refine Or.inr ⟨⟨j, zx⟩, zaE.mpr hj, hji, ?_⟩
     rw [ih ⟨j, zx⟩ (Nat.lt_of_lt_of_le hji (Nat.lt_succ_iff.mp hi))]
     exact hgv
private def zaG (C : AndCountCircuit 8) (adj : Fin 8 → Fin 8 → Bool) : Prop :=
 ∀ U : Finset (Fin 8), C.eval U = true ↔ ∃ u ∈ U, ∃ v ∈ U, adj u v = true
private lemma zaH (k : ℕ) (D : Circuit) (adj : Fin 8 → Fin 8 → Bool)
  (E : List (Fin 8 × Fin 8))
  (z1 : ∀ u v : Fin 8, adj u v = decide ((u, v) ∈ E ∨ (v, u) ∈ E))
  (qp : ∀ g ∈ D.gates, (g.op = GateOp.and ∧ g.inputs.length ≤ 2) ∨ g.op = GateOp.or)
  (z9 : Nat.card {j : Fin D.gates.length // (D.gates.get j).op = GateOp.and} ≤ k)
  (qL : circuitFun 8 D = (fun x : Fin 8 → Bool => E.any (fun p => x p.1 && x p.2))) :
  ∃ C : AndCountCircuit 8, C.WellFormed ∧ C.size ≤ k ∧ zaG C adj := by
 let qN : List WireRep := List.ofFn (fun v : Fin 8 => some ({v}, (∅ : Finset ℕ)))
 let w0 : Finset (Fin 8) → List Bool := fun U => List.ofFn (fun v : Fin 8 => decide (v ∈ U))
 have vL : SpecsWF ([] : List zac) := fun j hj => by simp at hj
 have wZ : ∀ r ∈ qN, RepWF 0 r := by
  intro r hr
  rcases List.mem_ofFn.mp hr with ⟨v, rfl⟩
  intro j hj
  exact absurd hj (Finset.notMem_empty j)
 have uy : ∀ U, (w0 U).length = qN.length := fun U => by simp [w0, qN]
 have tm : ∀ U i, repVal U (zae [] U) (qN.getD i defRep) = (w0 U).getD i false := by
  intro U i
  by_cases hi : i < 8
  ·have hi1 : i < qN.length := by simp [qN, hi]
   have hi2 : i < (w0 U).length := by simp [w0, hi]
   simp only [List.getD, List.getElem?_eq_getElem hi1, List.getElem?_eq_getElem hi2,
    Option.getD_some, qN, w0, List.getElem_ofFn]
   simp [repVal, sideVal]
  ·have hi1 : qN.length ≤ i := by simp [qN]; omega
   have hi2 : (w0 U).length ≤ i := by simp [w0]; omega
   simp only [List.getD, List.getElem?_eq_none hi1, List.getElem?_eq_none hi2, Option.getD_none]
   exact zav U _
 obtain ⟨hwf, qU, qe, heq, hsz⟩ :=
  zaC D.gates qp qN [] w0 vL wZ uy tm
 let st := D.gates.foldl zaz (qN, [])
 have tA : st.2.length ≤ k := by
  have hf := zab D.gates
  change st.2.length ≤ ([] : List zac).length + (D.gates.filter (fun g => isAnd g.op)).length at hsz
  simp only [List.length_nil, Nat.zero_add] at hsz
  omega
 have yx : ∀ U : Finset (Fin 8),
   repVal U (zae st.2 U) (st.1.getD D.output defRep) =
    E.any (fun p => decide (p.1 ∈ U) && decide (p.2 ∈ U)) := by
  intro U
  have h1 := heq U D.output
  change repVal U (zae st.2 U) (st.1.getD D.output defRep) =
   (D.wires (List.ofFn (fun v : Fin 8 => decide (v ∈ U)))).getD D.output false at h1
  rw [h1]
  have h2 : (D.wires (List.ofFn (fun v : Fin 8 => decide (v ∈ U)))).getD D.output false =
    circuitFun 8 D (fun v : Fin 8 => decide (v ∈ U)) := rfl
  rw [h2, qL]
 have xT : st.1.getD D.output defRep ≠ none := by
  intro zC
  have h0 := yx ∅
  rw [zC] at h0
  simp [repVal] at h0
 cases hrep_out : st.1.getD D.output defRep with
 | none => exact absurd hrep_out xT
 | some xH =>
  have xC : SideWF st.2.length xH := by
   have hr := zaA qU D.output
   rw [hrep_out] at hr
   exact hr
  let C : AndCountCircuit 8 :=
   {size := st.2.length
    leftVars := fun i => (st.2.getD i.val defSpec).1.1
    leftGates := fun i => zaD st.2.length (st.2.getD i.val defSpec).1.2
    rightVars := fun i => (st.2.getD i.val defSpec).2.1
    rightGates := fun i => zaD st.2.length (st.2.getD i.val defSpec).2.2
    outVars := xH.1
    outGates := zaD st.2.length xH.2 }
  refine ⟨C, ?_, tA, ?_⟩
  ·exact (zaF st.2 hwf xH xC ∅).1
  ·intro U
   have va := zaF st.2 hwf xH xC U
   have wc : ∀ i : Fin C.size, C.gateVal U i = (zae st.2 U).getD i.val false :=
    fun i => va.2 st.2.length i i.isLt
   have hCe : C.eval U = E.any (fun p => decide (p.1 ∈ U) && decide (p.2 ∈ U)) := by
    have h3 := yx U
    rw [hrep_out] at h3
    rw [← h3]
    unfold AndCountCircuit.eval repVal sideVal
    refine decide_eq_decide.mpr ?_
    constructor
    ·rintro (h | ⟨j, hj, hv⟩)
     ·exact Or.inl h
     ·rw [wc j] at hv
      exact Or.inr ⟨j.val, zaE.mp hj, hv⟩
    ·rintro (h | ⟨j, hj, hv⟩)
     ·exact Or.inl h
     ·have zx : j < st.2.length := xC j hj
      refine Or.inr ⟨⟨j, zx⟩, zaE.mpr hj, ?_⟩
      rw [wc ⟨j, zx⟩]
      exact hv
   rw [hCe]
   simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
   constructor
   ·rintro ⟨⟨u, v⟩, hpE, huU, hvU⟩
    refine ⟨u, huU, v, hvU, ?_⟩
    rw [z1 u v, decide_eq_true_eq]
    exact Or.inl hpE
   ·rintro ⟨u, huU, v, hvU, hadjuv⟩
    rw [z1 u v, decide_eq_true_eq] at hadjuv
    rcases hadjuv with huv | hvu
    ·exact ⟨(u, v), huv, huU, hvU⟩
    ·exact ⟨(v, u), hvu, hvU, huU⟩
private lemma zaI {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
  (v w : Fin k → Bool) (h : ∀ j, j < i → v j = w j) :
  sideTrue U B F i v = sideTrue U B F i w := by
 unfold sideTrue
 refine decide_eq_decide.mpr ?_
 constructor
 ·rintro (h1 | ⟨j, hj, hji, hv⟩)
  ·exact Or.inl h1
  ·exact Or.inr ⟨j, hj, hji, by rw [← h j hji]; exact hv⟩
 ·rintro (h1 | ⟨j, hj, hji, hv⟩)
  ·exact Or.inl h1
  ·exact Or.inr ⟨j, hj, hji, by rw [h j hji]; exact hv⟩
private lemma zaJ {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
  (v : Fin k → Bool) :
  sideTrue U B F i v = true ↔ ((∃ x ∈ B, x ∈ U) ∨ ∃ j ∈ F, j < i ∧ v j = true) := by
 unfold sideTrue
 exact decide_eq_true_iff
private lemma zaK {n k : ℕ} (U U' B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
  (v w : Fin k → Bool) (hU : U ⊆ U') (h : ∀ j, j < i → v j = true → w j = true)
  (hs : sideTrue U B F i v = true) : sideTrue U' B F i w = true := by
 rw [zaJ] at hs ⊢
 rcases hs with ⟨x, hx, hxU⟩ | ⟨j, hj, hji, hv⟩
 ·exact Or.inl ⟨x, hx, hU hxU⟩
 ·exact Or.inr ⟨j, hj, hji, h j hji hv⟩
private lemma zaL {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
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
  rw [zaI U (C.leftVars i) (C.leftGates i) i _ _ hc,
   zaI U (C.rightVars i) (C.rightGates i) i _ _ hc]
private lemma zaM {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) :
  C.gateVal U i = (sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U) &&
   sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateVal U)) :=
 (zaL C U C.size i i.isLt).symm
private lemma zaN {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) :
  C.gateVal U i = true ↔
   (((∃ x ∈ C.leftVars i, x ∈ U) ∨ ∃ j ∈ C.leftGates i, j < i ∧ C.gateVal U j = true) ∧
    ((∃ x ∈ C.rightVars i, x ∈ U) ∨ ∃ j ∈ C.rightGates i, j < i ∧ C.gateVal U j = true)) := by
 rw [zaM, Bool.and_eq_true, zaJ, zaJ]
private lemma zaO {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
  C.eval U = true ↔
   ((∃ v ∈ C.outVars, v ∈ U) ∨ ∃ j ∈ C.outGates, C.gateVal U j = true) := by
 unfold AndCountCircuit.eval
 exact decide_eq_true_iff
private lemma zaP {n : ℕ} (C : AndCountCircuit n) (U U' : Finset (Fin n)) (hU : U ⊆ U') :
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
  exact ⟨zaK U U' _ _ i _ _ hU (fun j _ => ih j) h'.1,
   zaK U U' _ _ i _ _ hU (fun j _ => ih j) h'.2⟩
private lemma zaQ {n : ℕ} (C : AndCountCircuit n) (U U' : Finset (Fin n)) (hU : U ⊆ U')
  (i : Fin C.size) (h : C.gateVal U i = true) : C.gateVal U' i = true :=
 zaP C U U' hU C.size i h
private lemma zaR (C : AndCountCircuit 8) (adj : Fin 8 → Fin 8 → Bool)
  (zQ : ∀ v : Fin 8, adj v v = false) (h : zaG C adj) : C.outVars = ∅ := by
 apply Finset.eq_empty_of_forall_notMem
 intro v hv
 have h1 : C.eval {v} = true := by
  rw [zaO]
  exact Or.inl ⟨v, hv, Finset.mem_singleton_self v⟩
 obtain ⟨a, ha, c, hc, z1⟩ := (h {v}).1 h1
 rw [Finset.mem_singleton] at ha hc
 rw [ha, hc, zQ v] at z1
 exact Bool.noConfusion z1
private lemma zaS (C : AndCountCircuit 8) (adj : Fin 8 → Fin 8 → Bool)
  (zQ : ∀ v : Fin 8, adj v v = false) (h : zaG C adj) (U : Finset (Fin 8)) :
  C.eval U = true ↔ ∃ j ∈ C.outGates, C.gateVal U j = true := by
 rw [zaO, zaR C adj zQ h]
 constructor
 ·rintro (⟨x, hx, _⟩ | h2)
  ·exact absurd hx (Finset.notMem_empty x)
  ·exact h2
 ·exact Or.inr
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
private lemma zaT {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) (x : Fin n) :
  x ∈ (normC C).leftVars i ↔ (sL C i x = true ∧ sR C i x = false) := by
 show x ∈ Finset.univ.filter (fun v => sL C i v = true ∧ sR C i v = false) ↔ _
 rw [Finset.mem_filter]
 exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ x, h⟩⟩
private lemma zaU {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) (x : Fin n) :
  x ∈ (normC C).rightVars i ↔ (sR C i x = true ∧ sL C i x = false) := by
 show x ∈ Finset.univ.filter (fun v => sR C i v = true ∧ sL C i v = false) ↔ _
 rw [Finset.mem_filter]
 exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ x, h⟩⟩
private lemma zaV {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) :
  Disjoint ((normC C).leftVars i) ((normC C).rightVars i) := by
 rw [Finset.disjoint_left]
 intro x hx hx'
 rw [zaT] at hx
 rw [zaU] at hx'
 exact Bool.noConfusion (hx.1.symm.trans hx'.2)
private lemma zaW {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) (v : Fin n) :
  C.gateVal {v} i = true ↔ (sL C i v = true ∧ sR C i v = true) := by
 rw [zaM, Bool.and_eq_true]
 rfl
private lemma zaX {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size)
  (ih : ∀ j : Fin C.size, j < i →
   (C.gateVal U j = true ↔ (∃ v ∈ U, C.gateVal {v} j = true) ∨ (normC C).gateVal U j = true))
  (B : Finset (Fin n)) (F : Finset (Fin C.size)) :
  sideTrue U B F i (C.gateVal U) = true ↔
   ((∃ v ∈ U, sideTrue {v} B F i (C.gateVal {v}) = true) ∨
    ∃ j ∈ F, j < i ∧ (normC C).gateVal U j = true) := by
 rw [zaJ]
 constructor
 ·rintro (⟨x, hx, hxU⟩ | ⟨j, hj, hji, hv⟩)
  ·exact Or.inl ⟨x, hxU, (zaJ _ _ _ _ _).2
    (Or.inl ⟨x, hx, Finset.mem_singleton_self x⟩)⟩
  ·rcases (ih j hji).1 hv with ⟨v, hvU, hg⟩ | hd
   ·exact Or.inl ⟨v, hvU, (zaJ _ _ _ _ _).2 (Or.inr ⟨j, hj, hji, hg⟩)⟩
   ·exact Or.inr ⟨j, hj, hji, hd⟩
 ·rintro (⟨v, hvU, hs⟩ | ⟨j, hj, hji, hd⟩)
  ·rcases (zaJ _ _ _ _ _).1 hs with ⟨x, hx, hxv⟩ | ⟨j, hj, hji, hg⟩
   ·rw [Finset.mem_singleton] at hxv
    exact Or.inl ⟨x, hx, hxv ▸ hvU⟩
   ·exact Or.inr ⟨j, hj, hji, zaQ C {v} U
     (Finset.singleton_subset_iff.2 hvU) j hg⟩
  ·exact Or.inr ⟨j, hj, hji, (ih j hji).2 (Or.inr hd)⟩
private lemma zaY {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) :
  (normC C).gateVal U i = true ↔
   (((∃ x ∈ U, sL C i x = true ∧ sR C i x = false) ∨
     ∃ j ∈ C.leftGates i, j < i ∧ (normC C).gateVal U j = true) ∧
    ((∃ x ∈ U, sR C i x = true ∧ sL C i x = false) ∨
     ∃ j ∈ C.rightGates i, j < i ∧ (normC C).gateVal U j = true)) := by
 have h := zaN (normC C) U i
 rw [h]
 constructor
 ·rintro ⟨h1, h2⟩
  refine ⟨?_, ?_⟩
  ·rcases h1 with ⟨x, hx, hxU⟩ | h1
   ·exact Or.inl ⟨x, hxU, (zaT C i x).1 hx⟩
   ·exact Or.inr h1
  ·rcases h2 with ⟨x, hx, hxU⟩ | h2
   ·exact Or.inl ⟨x, hxU, (zaU C i x).1 hx⟩
   ·exact Or.inr h2
 ·rintro ⟨h1, h2⟩
  refine ⟨?_, ?_⟩
  ·rcases h1 with ⟨x, hxU, hx⟩ | h1
   ·exact Or.inl ⟨x, (zaT C i x).2 hx, hxU⟩
   ·exact Or.inr h1
  ·rcases h2 with ⟨x, hxU, hx⟩ | h2
   ·exact Or.inl ⟨x, (zaU C i x).2 hx, hxU⟩
   ·exact Or.inr h2
private lemma zaZ {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
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
   have eL := zaX C U i ih' (C.leftVars i) (C.leftGates i)
   have eR := zaX C U i ih' (C.rightVars i) (C.rightGates i)
   rw [zaM C U i, Bool.and_eq_true, eL, eR, zaY]
   constructor
   ·rintro ⟨hl, hr⟩
    by_cases hW : ∃ v ∈ U, C.gateVal {v} i = true
    ·exact Or.inl hW
    ·refine Or.inr ⟨?_, ?_⟩
     ·rcases hl with ⟨v, hvU, hs⟩ | hl
      ·refine Or.inl ⟨v, hvU, hs, ?_⟩
       rw [← Bool.not_eq_true]
       intro hs'
       exact hW ⟨v, hvU, (zaW C i v).2 ⟨hs, hs'⟩⟩
      ·exact Or.inr hl
     ·rcases hr with ⟨v, hvU, hs⟩ | hr
      ·refine Or.inl ⟨v, hvU, hs, ?_⟩
       rw [← Bool.not_eq_true]
       intro hs'
       exact hW ⟨v, hvU, (zaW C i v).2 ⟨hs', hs⟩⟩
      ·exact Or.inr hr
   ·rintro (⟨v, hvU, hg⟩ | ⟨hl, hr⟩)
    ·have := (zaW C i v).1 hg
     exact ⟨Or.inl ⟨v, hvU, this.1⟩, Or.inl ⟨v, hvU, this.2⟩⟩
    ·refine ⟨?_, ?_⟩
     ·rcases hl with ⟨v, hvU, hs, _⟩ | hl
      ·exact Or.inl ⟨v, hvU, hs⟩
      ·exact Or.inr hl
     ·rcases hr with ⟨v, hvU, hs, _⟩ | hr
      ·exact Or.inl ⟨v, hvU, hs⟩
      ·exact Or.inr hr
 intro i
 exact key (i.val + 1) i (Nat.lt_succ_self _)
private lemma za0 {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
  (normC C).eval U = C.eval U := by
 rw [Bool.eq_iff_iff, zaO, zaO]
 have mo : ∀ x, x ∈ (normC C).outVars ↔
   (x ∈ C.outVars ∨ ∃ j ∈ C.outGates, C.gateVal {x} j = true) := by
  intro x
  show x ∈ C.outVars ∪
   Finset.univ.filter (fun v => ∃ j ∈ C.outGates, C.gateVal {v} j = true) ↔ _
  rw [Finset.mem_union, Finset.mem_filter]
  exact ⟨fun h => h.imp id (fun h => h.2), fun h => h.imp id (fun h => ⟨Finset.mem_univ x, h⟩)⟩
 constructor
 ·rintro (⟨x, hx, hxU⟩ | ⟨j, hj, hv⟩)
  ·rcases (mo x).1 hx with hx | ⟨j, hj, hv⟩
   ·exact Or.inl ⟨x, hx, hxU⟩
   ·exact Or.inr ⟨j, hj, zaQ C {x} U (Finset.singleton_subset_iff.2 hxU) j hv⟩
  ·exact Or.inr ⟨j, hj, (zaZ C U j).2 (Or.inr hv)⟩
 ·rintro (⟨x, hx, hxU⟩ | ⟨j, hj, hv⟩)
  ·exact Or.inl ⟨x, (mo x).2 (Or.inl hx), hxU⟩
  ·rcases (zaZ C U j).1 hv with ⟨x, hxU, hg⟩ | hd
   ·exact Or.inl ⟨x, (mo x).2 (Or.inr ⟨j, hj, hg⟩), hxU⟩
   ·exact Or.inr ⟨j, hj, hd⟩
private lemma za1 (C : AndCountCircuit 8) (adj : Fin 8 → Fin 8 → Bool)
  (zQ : ∀ v : Fin 8, adj v v = false) (h : zaG C adj) :
  ∃ D : AndCountCircuit 8, zaG D adj ∧ D.size = C.size ∧
   (∀ i, Disjoint (D.leftVars i) (D.rightVars i)) ∧ D.outVars = ∅ := by
 have hc : zaG (normC C) adj := fun U => by rw [za0]; exact h U
 exact ⟨normC C, hc, rfl, zaV C, zaR (normC C) adj zQ hc⟩
private lemma za2 {n : ℕ} (C : AndCountCircuit n) (X : Finset (Fin n)) :
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
   have g := (zaN C X i).1 hv
   have y0 : ∀ j : Fin C.size, j < i → C.gateVal X j = true →
     ∃ k : Fin C.size, C.gateVal X k = true ∧ (∃ x ∈ C.leftVars k, x ∈ X) ∧
      (∃ y ∈ C.rightVars k, y ∈ X) := by
    intro j hji hjv
    have hlt : j.val < m := by
     have : j.val < i.val := hji
     omega
    exact ih j hlt hjv
   rcases g.1 with hx | ⟨j, _, hji, hjv⟩
   ·rcases g.2 with hy | ⟨j, _, hji, hjv⟩
    ·exact ⟨i, hv, hx, hy⟩
    ·exact y0 j hji hjv
   ·exact y0 j hji hjv
 intro i
 exact key (i.val + 1) i (Nat.lt_succ_self _)
private lemma za3 {n : ℕ} (C : AndCountCircuit n) (I : Finset (Fin n)) (u : Fin n) :
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
  have u0 : ∀ (B : Finset (Fin n)) (F : Finset (Fin C.size)),
    ((∃ x ∈ B, x ∈ insert u I) ∨ ∃ j ∈ F, j < i ∧ C.gateVal (insert u I) j = true) →
    ¬ ((∃ x ∈ B, x ∈ I) ∨ ∃ j ∈ F, j < i ∧ C.gateVal I j = true) →
    (u ∈ B ∧ Disjoint B I) ∨
    ∃ j : Fin C.size, j < i ∧ C.gateVal (insert u I) j = true ∧ C.gateVal I j = false := by
   intro B F hT hF
   rcases hT with ⟨x, hx, hxU⟩ | ⟨j, hj, hji, hv⟩
   ·rcases Finset.mem_insert.1 hxU with hxu | hxI
    ·refine Or.inl ⟨hxu ▸ hx, ?_⟩
     exact Finset.disjoint_left.2 (fun y hy hyI => hF (Or.inl ⟨y, hy, hyI⟩))
    ·exact absurd (Or.inl ⟨x, hx, hxI⟩) hF
   ·have hjf : C.gateVal I j = false := by
     rw [← Bool.not_eq_true]
     intro hvI
     exact hF (Or.inr ⟨j, hj, hji, hvI⟩)
    exact Or.inr ⟨j, hji, hv, hjf⟩
  have y0 : (∃ j : Fin C.size, j < i ∧ C.gateVal (insert u I) j = true ∧
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
  have g1 := (zaN C (insert u I) i).1 h1
  have g0 : ¬ _ := fun hh => Bool.noConfusion (h0.symm.trans ((zaN C I i).2 hh))
  by_cases hL : (∃ x ∈ C.leftVars i, x ∈ I) ∨ ∃ j ∈ C.leftGates i, j < i ∧ C.gateVal I j = true
  ·have hR : ¬ ((∃ x ∈ C.rightVars i, x ∈ I) ∨
     ∃ j ∈ C.rightGates i, j < i ∧ C.gateVal I j = true) := fun hh => g0 ⟨hL, hh⟩
   rcases u0 _ _ g1.2 hR with hs | hs
   ·exact ⟨i, le_refl i, h1, h0, Or.inr hs⟩
   ·exact y0 hs
  ·rcases u0 _ _ g1.1 hL with hs | hs
   ·exact ⟨i, le_refl i, h1, h0, Or.inl hs⟩
   ·exact y0 hs
private lemma wit_adj (C : AndCountCircuit 8) (adj : Fin 8 → Fin 8 → Bool)
  (zQ : ∀ v : Fin 8, adj v v = false) (hC : zaG C adj)
  (I : Finset (Fin 8)) (hI : ∀ a ∈ I, ∀ c ∈ I, adj a c = false)
  (u x : Fin 8) (hx : x ∈ I) (hux : adj u x = true) :
  ∃ i : Fin C.size, (u ∈ C.leftVars i ∧ Disjoint (C.leftVars i) I) ∨
   (u ∈ C.rightVars i ∧ Disjoint (C.rightVars i) I) := by
 have e1 : C.eval (insert u I) = true :=
  (hC _).2 ⟨u, Finset.mem_insert_self u I, x, Finset.mem_insert_of_mem hx, hux⟩
 obtain ⟨o, ho, hv1⟩ := (zaS C adj zQ hC _).1 e1
 have hv0 : C.gateVal I o = false := by
  rw [← Bool.not_eq_true]
  intro hv
  have e0 : C.eval I = true := (zaS C adj zQ hC _).2 ⟨o, ho, hv⟩
  obtain ⟨a, ha, c, hc, z1⟩ := (hC I).1 e0
  rw [hI a ha c hc] at z1
  exact Bool.noConfusion z1
 obtain ⟨k, _, _, _, r⟩ := za3 C I u (o.val + 1) o (Nat.lt_succ_self _) hv1 hv0
 exact ⟨k, r⟩
private def sv {n : ℕ} (C : AndCountCircuit n) (X : Finset (Fin n)) (i : Fin C.size) (s : Bool) : Bool :=
 sideTrue X (cond s (C.rightVars i) (C.leftVars i)) (cond s (C.rightGates i) (C.leftGates i)) i
  (C.gateVal X)
private lemma za4 {n : ℕ} (C : AndCountCircuit n) (X : Finset (Fin n)) (i : Fin C.size) :
  C.gateVal X i = false ↔ (sv C X i false = false ∨ sv C X i true = false) := by
 rw [zaM, Bool.and_eq_false_iff]
 rfl
private lemma sv_hit {n : ℕ} (C : AndCountCircuit n) (U X : Finset (Fin n)) (hU : U ⊆ X)
  (i : Fin C.size) (s : Bool)
  (h : ¬ Disjoint (cond s (C.rightVars i) (C.leftVars i)) U) : sv C X i s = true := by
 rw [Finset.not_disjoint_iff] at h
 obtain ⟨x, hx, hxU⟩ := h
 exact (zaJ _ _ _ _ _).2 (Or.inl ⟨x, hx, hU hxU⟩)
private lemma za5 {n : ℕ} (C : AndCountCircuit n) (X Y : Finset (Fin n)) (i : Fin C.size)
  (s : Bool) (hX : sv C X i s = false) (hY : sv C Y i s = false)
  (ih : ∀ j : Fin C.size, j < i → C.gateVal X j = false → C.gateVal Y j = false →
   C.gateVal (X ∪ Y) j = false) : sv C (X ∪ Y) i s = false := by
 rw [← Bool.not_eq_true] at hX hY ⊢
 unfold sv at hX hY ⊢
 rw [zaJ] at hX hY ⊢
 rintro (⟨x, hx, hxU⟩ | ⟨j, hj, hji, hv⟩)
 ·rcases Finset.mem_union.1 hxU with h | h
  ·exact hX (Or.inl ⟨x, hx, h⟩)
  ·exact hY (Or.inl ⟨x, hx, h⟩)
 ·have h1 : C.gateVal X j = false := by
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
private lemma za6 {n : ℕ} (C : AndCountCircuit n) (U X : Finset (Fin n)) (hU : U ⊆ X)
  (i : Fin C.size) (h : C.gateVal X i = false) : sv C X i (codeSide C U X i) = false := by
 rw [za4] at h
 unfold codeSide
 by_cases hl : ¬ Disjoint (C.leftVars i) U
 ·simp only [hl, not_false_eq_true, ↓reduceIte]
  have := sv_hit C U X hU i false hl
  rcases h with h | h
  ·rw [this] at h; exact Bool.noConfusion h
  ·exact h
 ·simp only [not_not.mp hl, not_true_eq_false, ↓reduceIte]
  by_cases hr : ¬ Disjoint (C.rightVars i) U
  ·simp only [hr, not_false_eq_true, ↓reduceIte]
   have := sv_hit C U X hU i true hr
   rcases h with h | h
   ·exact h
   ·rw [this] at h; exact Bool.noConfusion h
  ·simp only [not_not.mp hr, not_true_eq_false, ↓reduceIte]
   cases hb : sv C X i false with
   | false => exact hb
   | true =>
    rcases h with h | h
    ·rw [hb] at h; exact Bool.noConfusion h
    ·exact h
private lemma za7 {n : ℕ} (C : AndCountCircuit n) (U X Y : Finset (Fin n))
  (i : Fin C.size) (h : ¬ Disjoint (C.leftVars i ∪ C.rightVars i) U) :
  codeSide C U X i = codeSide C U Y i := by
 unfold codeSide
 by_cases hl : ¬ Disjoint (C.leftVars i) U
 ·simp only [hl, not_false_eq_true, ↓reduceIte]
 ·by_cases hr : ¬ Disjoint (C.rightVars i) U
  ·simp only [not_not.mp hl, not_true_eq_false, hr, not_false_eq_true, ↓reduceIte]
  ·exfalso
   apply h
   rw [Finset.disjoint_union_left]
   exact ⟨not_not.1 hl, not_not.1 hr⟩
private lemma za8 {n : ℕ} (C : AndCountCircuit n) (U X Y : Finset (Fin n)) (hX : U ⊆ X)
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
   have c1 := za6 C U X hX i h1
   have c2 := za6 C U Y hY i h2
   rw [← hc i] at c2
   have hm := za5 C X Y i _ c1 c2 ih'
   rw [za4]
   cases hb : codeSide C U X i with
   | false => rw [hb] at hm; exact Or.inl hm
   | true => rw [hb] at hm; exact Or.inr hm
 intro i
 exact key (i.val + 1) i (Nat.lt_succ_self _)
private lemma za9 {n : ℕ} (C : AndCountCircuit n) (U X Y : Finset (Fin n)) (hX : U ⊆ X)
  (hY : U ⊆ Y) (hc : ∀ i, codeSide C U X i = codeSide C U Y i)
  (h1 : C.eval X = false) (h2 : C.eval Y = false) : C.eval (X ∪ Y) = false := by
 rw [← Bool.not_eq_true, zaO] at h1 h2 ⊢
 rintro (⟨x, hx, hxU⟩ | ⟨j, hj, hv⟩)
 ·rcases Finset.mem_union.1 hxU with h | h
  ·exact h1 (Or.inl ⟨x, hx, h⟩)
  ·exact h2 (Or.inl ⟨x, hx, h⟩)
 ·have g1 : C.gateVal X j = false := by
   rw [← Bool.not_eq_true]
   exact fun hh => h1 (Or.inr ⟨j, hj, hh⟩)
  have g2 : C.gateVal Y j = false := by
   rw [← Bool.not_eq_true]
   exact fun hh => h2 (Or.inr ⟨j, hj, hh⟩)
  rw [za8 C U X Y hX hY hc j g1 g2] at hv
  exact Bool.noConfusion hv
private lemma zba {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) (m : ℕ)
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
   ·exact congrFun hab ⟨i, hi⟩
   ·exact za7 C U _ _ i hi
  have := za9 C U (M a) (M b) (hU a) (hU b) hc (h0 a) (h0 b)
  rw [h1 a b hne] at this
  exact Bool.noConfusion this
 have z9 := Fintype.card_le_of_injective f hf
 rw [Fintype.card_fin, Fintype.card_fun, Fintype.card_bool, Fintype.card_subtype] at z9
 exact z9
private def ModelFS (adj : Fin 8 → Fin 8 → Bool) (mis : List (List (Fin 8))) (qO : Fin 8 → ℕ)
  (W : Fin 8 → Finset (Fin 4 × Bool)) : Prop :=
 (∀ v, (W v).Nonempty ∧ (W v).card ≤ qO v ∧ ∀ g : Fin 4, ¬ ((g, false) ∈ W v ∧ (g, true) ∈ W v)) ∧
 (∀ u v, adj u v = true → ∃ g b, (g, b) ∈ W u ∧ (g, !b) ∈ W v) ∧
 (∀ I ∈ mis, ∀ u : Fin 8, u ∉ I → ∃ p ∈ W u, ∀ y ∈ I, p ∉ W y)
private def W0 (D : AndCountCircuit 8) (v : Fin 8) : Finset (Fin 4 × Bool) :=
 Finset.univ.filter (fun p : Fin 4 × Bool =>
  if h : p.1.val < D.size then v ∈ cond p.2 (D.rightVars ⟨p.1.val, h⟩) (D.leftVars ⟨p.1.val, h⟩)
  else False)
private lemma zbb {D : AndCountCircuit 8} {v : Fin 8} {g : Fin 4} :
  (g, false) ∈ W0 D v ↔ ∃ h : g.val < D.size, v ∈ D.leftVars ⟨g.val, h⟩ := by
 simp [W0]
private lemma zbc {D : AndCountCircuit 8} {v : Fin 8} {g : Fin 4} :
  (g, true) ∈ W0 D v ↔ ∃ h : g.val < D.size, v ∈ D.rightVars ⟨g.val, h⟩ := by
 simp [W0]
private lemma zbd {α : Type*} (l : List α) (p : α → Bool) :
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
private lemma zbe (D : AndCountCircuit 8) (adj : Fin 8 → Fin 8 → Bool)
  (mis : List (List (Fin 8))) (qO : Fin 8 → ℕ)
  (yD : D.size ≤ 4) (xa : zaG D adj)
  (q3 : ∀ i, Disjoint (D.leftVars i) (D.rightVars i)) (ub : D.outVars = ∅)
  (zQ : ∀ v : Fin 8, adj v v = false)
  (yg : ∀ v : Fin 8, ∃ x : Fin 8, adj v x = true)
  (zv : ∀ I ∈ mis, ∀ a ∈ I, ∀ b ∈ I, adj a b = false)
  (xh : ∀ I ∈ mis, ∀ u : Fin 8, u ∉ I → ∃ x ∈ I, adj u x = true)
  (zO : ∀ i j : Fin mis.length, i ≠ j → ∃ u ∈ mis[i.val], ∃ v ∈ mis[j.val], adj u v = true)
  (qS : ∀ v : Fin 8, qO v ≤ 3 ∧ 2 ^ (3 - qO v) < (mis.filter (fun I => I.elem v)).length) :
  ModelFS adj mis qO (W0 D) := by
 classical
 have wb : ∀ u v : Fin 8, adj u v = true → ∃ g b, (g, b) ∈ W0 D u ∧ (g, !b) ∈ W0 D v := by
  intro u v huv
  have hev : D.eval {u, v} = true :=
   (xa {u, v}).mpr ⟨u, Finset.mem_insert_self _ _, v, Finset.mem_insert_of_mem (Finset.mem_singleton_self _), huv⟩
  obtain ⟨o, _, hgo⟩ := (zaS D adj zQ xa {u, v}).mp hev
  obtain ⟨i, _, ⟨x, hxL, hxuv⟩, ⟨y, hyR, hyuv⟩⟩ := za2 D {u, v} o hgo
  have hxy : x ≠ y := fun he => (Finset.disjoint_left.mp (q3 i) hxL) (he ▸ hyR)
  let g : Fin 4 := ⟨i.val, lt_of_lt_of_le i.isLt yD⟩
  rcases Finset.mem_insert.mp hxuv with rfl | hx_v
  ·have tG : y = v := by
    rcases Finset.mem_insert.mp hyuv with rfl | h
    ·exact absurd rfl hxy
    ·exact Finset.mem_singleton.mp h
   subst tG
   exact ⟨g, false, zbb.mpr ⟨i.isLt, hxL⟩, zbc.mpr ⟨i.isLt, hyR⟩⟩
  ·have uV : x = v := Finset.mem_singleton.mp hx_v
   subst uV
   have tF : y = u := by
    rcases Finset.mem_insert.mp hyuv with rfl | h
    ·rfl
    ·exact absurd (Finset.mem_singleton.mp h).symm hxy
   subst tF
   exact ⟨g, true, zbc.mpr ⟨i.isLt, hyR⟩, zbb.mpr ⟨i.isLt, hxL⟩⟩
 refine ⟨fun v => ⟨?_, ?_, ?_⟩, wb, ?_⟩
 ·obtain ⟨x, hvx⟩ := yg v
  obtain ⟨g, b, qo, _⟩ := wb v x hvx
  exact ⟨(g, b), qo⟩
 ·let sub := (List.finRange mis.length).filter (fun i => mis[i.val].elem v)
  have yu : sub.Nodup := (List.nodup_finRange mis.length).filter _
  let M : Fin sub.length → Finset (Fin 8) := fun a => (mis[sub[a.val].val]).toFinset
  have hU : ∀ a, {v} ⊆ M a := by
   intro a
   rw [Finset.singleton_subset_iff]
   have wu : sub[a.val] ∈ sub := List.getElem_mem a.isLt
   have tr := (List.mem_filter.mp wu).2
   exact List.mem_toFinset.mpr (List.mem_of_elem_eq_true tr)
  have h0 : ∀ a, D.eval (M a) = false := by
   intro a
   rw [← Bool.not_eq_true]
   intro ht
   obtain ⟨x, hx, y, hy, hxy⟩ := (xa _).mp ht
   have hI := zv mis[sub[a.val].val] (List.getElem_mem sub[a.val].isLt)
    x (List.mem_toFinset.mp hx) y (List.mem_toFinset.mp hy)
   rw [hxy] at hI
   exact Bool.noConfusion hI
  have h1 : ∀ a b, a ≠ b → D.eval (M a ∪ M b) = true := by
   intro a b hab
   have hne : sub[a.val] ≠ sub[b.val] := by
    intro heq
    have hlt := yu.getElem_inj_iff.mp heq
    exact hab (Fin.ext hlt)
   obtain ⟨x, hx, y, hy, hxy⟩ := zO sub[a.val] sub[b.val] hne
   exact (xa _).mpr ⟨x, Finset.mem_union_left _ (List.mem_toFinset.mpr hx),
    y, Finset.mem_union_right _ (List.mem_toFinset.mpr hy), hxy⟩
  have hpc := zba D {v} sub.length M hU h0 h1
  let xq := Finset.univ.filter (fun i : Fin D.size => Disjoint (D.leftVars i ∪ D.rightVars i) {v})
  let xv := Finset.univ.filter (fun i : Fin D.size => ¬ Disjoint (D.leftVars i ∪ D.rightVars i) {v})
  have tb : (W0 D v).card = xv.card := by
   refine Finset.card_bij (fun p hp => ⟨p.1.val, ?_⟩) ?_ ?_ ?_
   ·rcases p with ⟨g, b⟩
    cases b
    ·exact (zbb.mp hp).1
    ·exact (zbc.mp hp).1
   ·rintro ⟨g, b⟩ hp
    simp only [xv, Finset.mem_filter, Finset.mem_univ, true_and,
     Finset.disjoint_singleton_right, not_not, Finset.mem_union]
    cases b
    ·exact Or.inl (zbb.mp hp).2
    ·exact Or.inr (zbc.mp hp).2
   ·rintro ⟨g1, b1⟩ hp1 ⟨g2, b2⟩ hp2 heq
    have wU : g1.val = g2.val := congrArg (fun x : Fin D.size => x.val) heq
    have hg : g1 = g2 := Fin.ext wU
    apply Prod.ext hg
    cases b1 <;> cases b2
    ·rfl
    ·exfalso
     obtain ⟨h1, hL⟩ := zbb.mp hp1
     obtain ⟨h2, hR⟩ := zbc.mp hp2
     have wK : (⟨g2.val, h2⟩ : Fin D.size) = ⟨g1.val, h1⟩ := Fin.ext wU.symm
     exact Finset.disjoint_left.mp (q3 ⟨g1.val, h1⟩) hL (wK ▸ hR)
    ·exfalso
     obtain ⟨h1, hR⟩ := zbc.mp hp1
     obtain ⟨h2, hL⟩ := zbb.mp hp2
     have wK : (⟨g2.val, h2⟩ : Fin D.size) = ⟨g1.val, h1⟩ := Fin.ext wU.symm
     exact Finset.disjoint_left.mp (q3 ⟨g1.val, h1⟩) (wK ▸ hL) hR
    ·rfl
   ·intro i hi
    simp only [xv, Finset.mem_filter, Finset.mem_univ, true_and,
     Finset.disjoint_singleton_right, not_not, Finset.mem_union] at hi
    rcases hi with hL | hR
    ·refine ⟨(⟨i.val, lt_of_lt_of_le i.isLt yD⟩, false), ?_, Fin.ext rfl⟩
     exact zbb.mpr ⟨i.isLt, hL⟩
    ·refine ⟨(⟨i.val, lt_of_lt_of_le i.isLt yD⟩, true), ?_, Fin.ext rfl⟩
     exact zbc.mpr ⟨i.isLt, hR⟩
  have xD : xq.card + xv.card = D.size := by
   have h1 : xv = Finset.univ \ xq := by
    ext i
    simp [xq, xv]
   rw [h1, add_comm, Finset.card_sdiff_add_card_eq_card (Finset.subset_univ xq),
    Finset.card_univ, Fintype.card_fin]
  have vH : sub.length = (mis.filter (fun I => I.elem v)).length :=
   zbd mis (fun I => I.elem v)
  obtain ⟨hmax3, yR⟩ := qS v
  rw [← vH] at yR
  have uJ : 2 ^ (3 - qO v) < 2 ^ xq.card := lt_of_lt_of_le yR hpc
  have u3 : 3 - qO v < xq.card := (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp uJ
  omega
 ·intro g ⟨hL, hR⟩
  obtain ⟨h1, hvL⟩ := zbb.mp hL
  obtain ⟨_, hvR⟩ := zbc.mp hR
  exact Finset.disjoint_left.mp (q3 ⟨g.val, h1⟩) hvL hvR
 ·intro I hI u hu
  obtain ⟨x, hxI, hux⟩ := xh I hI u hu
  obtain ⟨i, hside⟩ := wit_adj D adj zQ xa I.toFinset
   (fun a ha b hb => zv I hI a (List.mem_toFinset.mp ha) b (List.mem_toFinset.mp hb))
   u x (List.mem_toFinset.mpr hxI) hux
  let g : Fin 4 := ⟨i.val, lt_of_lt_of_le i.isLt yD⟩
  rcases hside with ⟨huL, hdisjI⟩ | ⟨huR, hdisjI⟩
  ·refine ⟨(g, false), zbb.mpr ⟨i.isLt, huL⟩, fun y hy qo => ?_⟩
   obtain ⟨_, hyL⟩ := zbb.mp qo
   exact Finset.disjoint_left.mp hdisjI hyL (List.mem_toFinset.mpr hy)
  ·refine ⟨(g, true), zbc.mpr ⟨i.isLt, huR⟩, fun y hy qo => ?_⟩
   obtain ⟨_, hyR⟩ := zbc.mp qo
   exact Finset.disjoint_left.mp hdisjI hyR (List.mem_toFinset.mpr hy)
private def zbf (g0 g : Fin 4) : Fin 4 :=
 if g = 0 then g0 else if g = g0 then 0 else g
private def permGB (g0 : Fin 4) (b0 : Bool) (p : Fin 4 × Bool) : Fin 4 × Bool :=
 (zbf g0 p.1, if p.1 = g0 then (p.2 != b0) else p.2)
private lemma zbg : ∀ (g0 : Fin 4) (b0 : Bool), permGB g0 b0 (g0, b0) = (0, false) := by
 decide
private lemma zbh : ∀ (g0 : Fin 4) (b0 : Bool) (p q : Fin 4 × Bool),
  permGB g0 b0 p = permGB g0 b0 q → p = q := by
 decide
private lemma zbi : ∀ (g0 : Fin 4) (b0 : Bool) (g : Fin 4) (b : Bool),
  (permGB g0 b0 (g, !b)).1 = (permGB g0 b0 (g, b)).1 ∧
  (permGB g0 b0 (g, !b)).2 = !(permGB g0 b0 (g, b)).2 := by
 decide
private lemma zbj : ∀ (g0 : Fin 4) (b0 : Bool) (p q : Fin 4 × Bool) (g : Fin 4),
  permGB g0 b0 p = (g, false) → permGB g0 b0 q = (g, true) → p.1 = q.1 ∧ p.2 = !q.2 := by
 decide
private lemma zbk (adj : Fin 8 → Fin 8 → Bool) (mis : List (List (Fin 8))) (qO : Fin 8 → ℕ)
  (W : Fin 8 → Finset (Fin 4 × Bool)) (hW : ModelFS adj mis qO W)
  (v0 : Fin 8) (hv0 : qO v0 = 1) :
  ∃ W' : Fin 8 → Finset (Fin 4 × Bool), ModelFS adj mis qO W' ∧ W' v0 = {((0 : Fin 4), false)} := by
 classical
 have wA : (W v0).card = 1 := by
  have hne := (hW.1 v0).1.card_pos
  have hle := (hW.1 v0).2.1
  omega
 obtain ⟨⟨g0, b0⟩, hv0eq⟩ := Finset.card_eq_one.mp wA
 let W' : Fin 8 → Finset (Fin 4 × Bool) := fun v => (W v).image (permGB g0 b0)
 have vj : Function.Injective (permGB g0 b0) := fun p q h => zbh g0 b0 p q h
 refine ⟨W', ⟨?_, ?_, ?_⟩, ?_⟩
 ·intro v
  refine ⟨?_, ?_, ?_⟩
  ·obtain ⟨p, hp⟩ := (hW.1 v).1
   exact ⟨permGB g0 b0 p, Finset.mem_image_of_mem _ hp⟩
  ·rw [Finset.card_image_of_injective _ vj]
   exact (hW.1 v).2.1
  ·intro g ⟨hp1, hp2⟩
   obtain ⟨p, hp, hpeq⟩ := Finset.mem_image.mp hp1
   obtain ⟨q, hq, hqeq⟩ := Finset.mem_image.mp hp2
   obtain ⟨hg, hb⟩ := zbj g0 b0 p q g hpeq hqeq
   have hpf : (p.1, false) ∈ W v := by
    cases hq2 : q.2
    ·have hq' : q = (p.1, false) := Prod.ext hg.symm hq2
     exact hq' ▸ hq
    ·rw [hq2] at hb
     have hp' : p = (p.1, false) := Prod.ext rfl hb
     exact hp' ▸ hp
   have hpt : (p.1, true) ∈ W v := by
    cases hq2 : q.2
    ·rw [hq2] at hb
     have hp' : p = (p.1, true) := Prod.ext rfl hb
     exact hp' ▸ hp
    ·have hq' : q = (p.1, true) := Prod.ext hg.symm hq2
     exact hq' ▸ hq
   exact (hW.1 v).2.2 p.1 ⟨hpf, hpt⟩
 ·intro u v huv
  obtain ⟨g, b, hgu, hgv⟩ := hW.2.1 u v huv
  obtain ⟨hf1, hf2⟩ := zbi g0 b0 g b
  refine ⟨(permGB g0 b0 (g, b)).1, (permGB g0 b0 (g, b)).2,
   Finset.mem_image_of_mem _ hgu, ?_⟩
  rw [← hf1, ← hf2]
  exact Finset.mem_image_of_mem _ hgv
 ·intro I hI u hu
  obtain ⟨p, hpu, hpI⟩ := hW.2.2 I hI u hu
  refine ⟨permGB g0 b0 p, Finset.mem_image_of_mem _ hpu, fun y hy qo => ?_⟩
  obtain ⟨q, hq, hqeq⟩ := Finset.mem_image.mp qo
  rw [zbh g0 b0 q p hqeq] at hq
  exact hpI y hy hq
 ·simp only [W', hv0eq, Finset.image_singleton, zbg]
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
private def zbl (mg : ℕ) : List ℕ :=
 if mg ≤ 1 then valid1 else if mg = 2 then valid2 else valid3
private lemma zbm :
  ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool, pack8 b0 b1 b2 b3 b4 b5 b6 b7 < 256 := by
 decide +kernel
private lemma zbn :
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
private lemma zbo :
  ∀ (m : Fin 256) (g : Fin 4) (s : Bool),
   (oppMask m.val).testBit (2 * g.val + if s then 1 else 0) =
    m.val.testBit (2 * g.val + if !s then 1 else 0) := by
 decide +kernel
private lemma zbp :
  ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool, ∀ mg : Fin 4,
   1 ≤ card8 b0 b1 b2 b3 b4 b5 b6 b7 →
   card8 b0 b1 b2 b3 b4 b5 b6 b7 ≤ mg.val →
   disj8 b0 b1 b2 b3 b4 b5 b6 b7 = true →
   pack8 b0 b1 b2 b3 b4 b5 b6 b7 ∈ zbl mg.val := by
 decide +kernel
private lemma zbq (S : Finset (Fin 4 × Bool)) : maskOf S < 256 :=
 zbm _ _ _ _ _ _ _ _
private lemma zbr (S : Finset (Fin 4 × Bool)) (g : Fin 4) (s : Bool) :
  (maskOf S).testBit (2 * g.val + if s then 1 else 0) = decide ((g, s) ∈ S) := by
 unfold maskOf
 rw [zbn]
 fin_cases g <;> cases s <;> rfl
private lemma zbs (S : Finset (Fin 4 × Bool)) :
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
private lemma zbt (S : Finset (Fin 4 × Bool)) (mg : ℕ) (hmg : mg ≤ 3)
  (hne : S.Nonempty) (z9 : S.card ≤ mg)
  (q3 : ∀ g : Fin 4, ¬ ((g, false) ∈ S ∧ (g, true) ∈ S)) :
  maskOf S ∈ zbl mg := by
 have h1 : 1 ≤ S.card := hne.card_pos
 rw [zbs S] at h1 z9
 have hd : disj8
   (decide (((0 : Fin 4), false) ∈ S)) (decide (((0 : Fin 4), true) ∈ S))
   (decide (((1 : Fin 4), false) ∈ S)) (decide (((1 : Fin 4), true) ∈ S))
   (decide (((2 : Fin 4), false) ∈ S)) (decide (((2 : Fin 4), true) ∈ S))
   (decide (((3 : Fin 4), false) ∈ S)) (decide (((3 : Fin 4), true) ∈ S)) = true := by
  simp only [disj8, Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
   decide_eq_false_iff_not]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  ·have := q3 0; tauto
  ·have := q3 1; tauto
  ·have := q3 2; tauto
  ·have := q3 3; tauto
 exact zbp _ _ _ _ _ _ _ _ ⟨mg, by omega⟩ h1 z9 hd
private lemma zbu : maskOf {((0 : Fin 4), false)} = 1 := by
 unfold maskOf
 simp [pack8]
private lemma zbv (S1 S2 : Finset (Fin 4 × Bool)) (g : Fin 4) (b : Bool)
  (h1 : (g, b) ∈ S1) (h2 : (g, !b) ∈ S2) :
  (oppMask (maskOf S1) &&& maskOf S2) ≠ 0 := by
 let k := 2 * g.val + if !b then 1 else 0
 have hb1 : (oppMask (maskOf S1)).testBit k = true := by
  have ht := zbo ⟨maskOf S1, zbq S1⟩ g (!b)
  rw [Bool.not_not] at ht
  change (oppMask (maskOf S1)).testBit k = (maskOf S1).testBit (2 * g.val + if b then 1 else 0) at ht
  rw [ht, zbr, decide_eq_true_eq]
  exact h1
 have hb2 : (maskOf S2).testBit k = true := by
  rw [zbr, decide_eq_true_eq]
  exact h2
 intro hz
 have ht := congrArg (fun z : ℕ => z.testBit k) hz
 rw [Nat.testBit_and, hb1, hb2, Nat.zero_testBit] at ht
 exact Bool.noConfusion ht
private lemma zbw (m1 m2 k : ℕ) (h1 : m1.testBit k = true) (h2 : m2.testBit k = false) :
  (m1 ||| m2) ≠ m2 := by
 intro heq
 have ht := congrArg (fun z : ℕ => z.testBit k) heq
 rw [Nat.testBit_or, h1, h2] at ht
 exact Bool.noConfusion ht
private def zbx (qd : List (Fin 8 × ℕ)) (v : Fin 8) : Option ℕ :=
 match qd with
 | [] => none
 | (u, m) :: qa => if u = v then some m else zbx qa v
private def zby (adj : Fin 8 → Fin 8 → Bool) (v : Fin 8) (m om : ℕ) : List (Fin 8 × ℕ) → Bool
 | [] => true
 | (u, mu) :: qa =>
   (!adj v u || (om &&& mu) != 0) &&
   ((m ||| mu) != mu) &&
   ((mu ||| m) != m) &&
   zby adj v m om qa
private def zbz (qd : List (Fin 8 × ℕ)) : List (Fin 8) → Option ℕ
 | [] => some 0
 | y :: ys =>
   match zbx qd y, zbz qd ys with
   | some my, some acc => some (my ||| acc)
   | _, _ => none
private def zbA (qd : List (Fin 8 × ℕ)) (I : List (Fin 8)) : Bool :=
 match zbz qd I with
 | none => true
 | some um =>
   qd.all (fun p => if I.elem p.1 then true else (p.2 ||| um) != um)
private def zbB (mis : List (List (Fin 8))) (qd : List (Fin 8 × ℕ)) : Bool :=
 mis.all (fun I => zbA qd I)
private def dfs (adj : Fin 8 → Fin 8 → Bool) (mis : List (List (Fin 8))) (qO : Fin 8 → ℕ)
  (qd : List (Fin 8 × ℕ)) : List (Fin 8) → Bool
 | [] => true
 | v :: qa =>
   let uc := match qd with
    | [] => [1]
    | _ => zbl (qO v)
   uc.any (fun m =>
    let om := oppMask m
    zby adj v m om qd &&
    let xp := (v, m) :: qd
    zbB mis xp &&
    dfs adj mis qO xp qa)
private def zbC (w : Fin 8 → ℕ) (I : List (Fin 8)) : ℕ :=
 I.foldr (fun y acc => w y ||| acc) 0
private lemma zbD (w : Fin 8 → ℕ) (I : List (Fin 8)) (k : ℕ) :
  (zbC w I).testBit k = true ↔ ∃ y ∈ I, (w y).testBit k = true := by
 induction I with
 | nil => simp [zbC]
 | cons y ys ih =>
  simp only [zbC, List.foldr_cons, Nat.testBit_or, Bool.or_eq_true, List.mem_cons]
  change ((w y).testBit k = true ∨ (zbC w ys).testBit k = true) ↔ _
  rw [ih]
  constructor
  ·rintro (h | ⟨z, hz, hzk⟩)
   ·exact ⟨y, Or.inl rfl, h⟩
   ·exact ⟨z, Or.inr hz, hzk⟩
  ·rintro ⟨z, rfl | hz, hzk⟩
   ·exact Or.inl hzk
   ·exact Or.inr ⟨z, hz, hzk⟩
private lemma zbE (w : Fin 8 → ℕ) (I : List (Fin 8)) (k : ℕ)
  (h : ∀ y ∈ I, (w y).testBit k = false) :
  (zbC w I).testBit k = false := by
 rw [← Bool.not_eq_true]
 intro ht
 obtain ⟨y, hy, hyk⟩ := (zbD w I k).mp ht
 rw [h y hy] at hyk
 exact Bool.noConfusion hyk
private lemma zbF (w : Fin 8 → ℕ) (qd : List (Fin 8 × ℕ))
  (q0 : ∀ p ∈ qd, p.2 = w p.1) (y : Fin 8) (my : ℕ)
  (h : zbx qd y = some my) : my = w y := by
 induction qd with
 | nil => simp [zbx] at h
 | cons p qa ih =>
  rcases p with ⟨u, mu⟩
  simp only [zbx] at h
  by_cases huv : u = y
  ·simp only [huv, ↓reduceIte, Option.some.injEq] at h
   subst h
   subst huv
   exact q0 (u, mu) List.mem_cons_self
  ·simp only [huv, ↓reduceIte] at h
   exact ih (fun q hq => q0 q (List.mem_cons_of_mem _ hq)) h
private lemma zbG (w : Fin 8 → ℕ) (qd : List (Fin 8 × ℕ))
  (q0 : ∀ p ∈ qd, p.2 = w p.1) (I : List (Fin 8)) (um : ℕ)
  (h : zbz qd I = some um) : um = zbC w I := by
 induction I generalizing um with
 | nil =>
  simp only [zbz, Option.some.injEq] at h
  subst h
  rfl
 | cons y ys ih =>
  simp only [zbz] at h
  cases hl : zbx qd y with
  | none => simp [hl] at h
  | some my =>
   cases hu : zbz qd ys with
   | none => simp [hl, hu] at h
   | some acc =>
    simp only [hl, hu, Option.some.injEq] at h
    subst h
    rw [zbF w qd q0 y my hl, ih acc hu]
    rfl
private lemma zbH (adj : Fin 8 → Fin 8 → Bool) (mis : List (List (Fin 8)))
  (qO : Fin 8 → ℕ) (W : Fin 8 → Finset (Fin 4 × Bool)) (hW : ModelFS adj mis qO W)
  (zp : ∀ u v : Fin 8, u ≠ v → ∃ I ∈ mis, v ∈ I ∧ u ∉ I)
  (v : Fin 8) (qd : List (Fin 8 × ℕ))
  (q0 : ∀ p ∈ qd, p.2 = maskOf (W p.1))
  (hne : ∀ p ∈ qd, p.1 ≠ v) :
  zby adj v (maskOf (W v)) (oppMask (maskOf (W v))) qd = true := by
 induction qd with
 | nil => rfl
 | cons p qa ih =>
  rcases p with ⟨u, mu⟩
  have hmu : mu = maskOf (W u) := q0 (u, mu) List.mem_cons_self
  have huv : u ≠ v := hne (u, mu) List.mem_cons_self
  simp only [zby, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
   bne_iff_ne, ne_eq]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ih (fun q hq => q0 q (List.mem_cons_of_mem _ hq))
   (fun q hq => hne q (List.mem_cons_of_mem _ hq))⟩
  ·by_cases z1 : adj v u = true
   ·right
    obtain ⟨g, b, hgv, hgu⟩ := hW.2.1 v u z1
    rw [hmu]
    exact zbv (W v) (W u) g b hgv hgu
   ·left
    exact Bool.eq_false_iff.mpr z1
  ·obtain ⟨I, hI, huI, hvI⟩ := zp v u huv.symm
   obtain ⟨⟨g, s⟩, hgv, hgI⟩ := hW.2.2 I hI v hvI
   have hgu : (g, s) ∉ W u := hgI u huI
   rw [hmu]
   refine zbw (maskOf (W v)) (maskOf (W u)) (2 * g.val + if s then 1 else 0) ?_ ?_
   ·rw [zbr, decide_eq_true_eq]; exact hgv
   ·rw [zbr, decide_eq_false_iff_not]; exact hgu
  ·obtain ⟨I, hI, hvI, huI⟩ := zp u v huv
   obtain ⟨⟨g, s⟩, hgu, hgI⟩ := hW.2.2 I hI u huI
   have hgv : (g, s) ∉ W v := hgI v hvI
   rw [hmu]
   refine zbw (maskOf (W u)) (maskOf (W v)) (2 * g.val + if s then 1 else 0) ?_ ?_
   ·rw [zbr, decide_eq_true_eq]; exact hgu
   ·rw [zbr, decide_eq_false_iff_not]; exact hgv
private lemma zbI (adj : Fin 8 → Fin 8 → Bool) (mis : List (List (Fin 8)))
  (qO : Fin 8 → ℕ) (W : Fin 8 → Finset (Fin 4 × Bool)) (hW : ModelFS adj mis qO W)
  (qd : List (Fin 8 × ℕ)) (q0 : ∀ p ∈ qd, p.2 = maskOf (W p.1)) :
  zbB mis qd = true := by
 rw [zbB, List.all_eq_true]
 intro I hI
 unfold zbA
 cases hu : zbz qd I with
 | none => rfl
 | some um =>
  have hum := zbG (fun x => maskOf (W x)) qd q0 I um hu
  rw [List.all_eq_true]
  intro p hp
  cases hel : I.elem p.1 with
  | true => simp
  | false =>
   simp only [Bool.false_eq_true, ↓reduceIte, bne_iff_ne, ne_eq]
   have wV : p.1 ∉ I := fun h => by
    rw [List.elem_eq_true_of_mem h] at hel
    exact Bool.noConfusion hel
   obtain ⟨⟨g, s⟩, hgp, hgI⟩ := hW.2.2 I hI p.1 wV
   rw [q0 p hp, hum]
   let k := 2 * g.val + if s then 1 else 0
   refine zbw (maskOf (W p.1)) (zbC (fun x => maskOf (W x)) I) k ?_ ?_
   ·rw [zbr, decide_eq_true_eq]; exact hgp
   ·apply zbE
    intro y hy
    rw [zbr, decide_eq_false_iff_not]
    exact hgI y hy
private lemma zbJ (adj : Fin 8 → Fin 8 → Bool) (mis : List (List (Fin 8)))
  (qO : Fin 8 → ℕ) (uB : ∀ v, qO v ≤ 3)
  (W : Fin 8 → Finset (Fin 4 × Bool)) (hW : ModelFS adj mis qO W)
  (zp : ∀ u v : Fin 8, u ≠ v → ∃ I ∈ mis, v ∈ I ∧ u ∉ I)
  (v0 : Fin 8) (hv0 : W v0 = {((0 : Fin 4), false)}) :
  ∀ (rem : List (Fin 8)) (qd : List (Fin 8 × ℕ)),
   rem.Nodup →
   (∀ p ∈ qd, p.2 = maskOf (W p.1)) →
   (∀ p ∈ qd, p.1 ∉ rem) →
   (qd = [] → ∃ t, rem = v0 :: t) →
   dfs adj mis qO qd rem = true := by
 intro rem
 induction rem with
 | nil =>
  intro _ _ _ _ _
  rfl
 | cons v qa ih =>
  intro qd xA q0 q3 zi
  simp only [dfs, List.any_eq_true]
  refine ⟨maskOf (W v), ?_, ?_⟩
  ·cases qd with
   | nil =>
    obtain ⟨t, ht⟩ := zi rfl
    have tC : v = v0 := by injection ht
    rw [tC, hv0, zbu]
    simp
   | cons _ _ =>
    exact zbt (W v) (qO v) (uB v) (hW.1 v).1 (hW.1 v).2.1 (hW.1 v).2.2
  ·have hne : ∀ p ∈ qd, p.1 ≠ v := fun p hp heq =>
    q3 p hp (heq ▸ List.mem_cons_self)
   have uH : zby adj v (maskOf (W v)) (oppMask (maskOf (W v))) qd = true :=
    zbH adj mis qO W hW zp v qd q0 hne
   have we : ∀ p ∈ ((v, maskOf (W v)) :: qd), p.2 = maskOf (W p.1) := by
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp'
    ·rfl
    ·exact q0 p hp'
   have uE : zbB mis ((v, maskOf (W v)) :: qd) = true :=
    zbI adj mis qO W hW ((v, maskOf (W v)) :: qd) we
   have qY : dfs adj mis qO ((v, maskOf (W v)) :: qd) qa = true := by
    apply ih ((v, maskOf (W v)) :: qd) (List.nodup_cons.mp xA).2 we
    ·intro p hp
     rcases List.mem_cons.mp hp with rfl | hp'
     ·exact (List.nodup_cons.mp xA).1
     ·exact fun hr => q3 p hp' (List.mem_cons_of_mem v hr)
    ·intro hnil; cases hnil
   rw [Bool.and_eq_true, Bool.and_eq_true]
   exact ⟨uH, ⟨uE, qY⟩⟩
private lemma zbK (adj : Fin 8 → Fin 8 → Bool) (E : List (Fin 8 × Fin 8))
  (mis : List (List (Fin 8))) (qO : Fin 8 → ℕ) (yH : List (Fin 8)) (v0 : Fin 8)
  (z1 : ∀ u v : Fin 8, adj u v = decide ((u, v) ∈ E ∨ (v, u) ∈ E))
  (zQ : ∀ v : Fin 8, adj v v = false)
  (yg : ∀ v : Fin 8, ∃ x : Fin 8, adj v x = true)
  (zv : ∀ I ∈ mis, ∀ a ∈ I, ∀ b ∈ I, adj a b = false)
  (xh : ∀ I ∈ mis, ∀ u : Fin 8, u ∉ I → ∃ x ∈ I, adj u x = true)
  (zO : ∀ i j : Fin mis.length, i ≠ j → ∃ u ∈ mis[i.val], ∃ v ∈ mis[j.val], adj u v = true)
  (zp : ∀ u v : Fin 8, u ≠ v → ∃ I ∈ mis, v ∈ I ∧ u ∉ I)
  (qS : ∀ v : Fin 8, qO v ≤ 3 ∧ 2 ^ (3 - qO v) < (mis.filter (fun I => I.elem v)).length)
  (xA : yH.Nodup)
  (zi : ∃ t, yH = v0 :: t)
  (w7 : qO v0 = 1)
  (w6 : dfs adj mis qO [] yH = false) :
  ¬ ∃ D : Circuit,
   (∀ g ∈ D.gates, (g.op = GateOp.and ∧ g.inputs.length ≤ 2) ∨ g.op = GateOp.or) ∧
   Nat.card {j : Fin D.gates.length // (D.gates.get j).op = GateOp.and} ≤ 4 ∧
   circuitFun 8 D = (fun x : Fin 8 → Bool => E.any (fun p => x p.1 && x p.2)) := by
 rintro ⟨D, qp, z9, qL⟩
 obtain ⟨C, _, hCsz, hCcomp⟩ := zaH 4 D adj E z1 qp z9 qL
 obtain ⟨C', hC'comp, hC'sz, q3, ql⟩ := za1 C adj zQ hCcomp
 have hW0 : ModelFS adj mis qO (W0 C') :=
  zbe C' adj mis qO (hC'sz ▸ hCsz) hC'comp q3 ql
   zQ yg zv xh zO qS
 obtain ⟨W', hW', hv0eq⟩ := zbk adj mis qO (W0 C') hW0 v0 w7
 have qE := zbJ adj mis qO (fun v => (qS v).1) W' hW' zp v0 hv0eq
  yH [] xA (fun _ h => by simp at h) (fun _ h => by simp at h) (fun _ => zi)
 rw [w6] at qE
 exact Bool.noConfusion qE
private def zbL (tI : Fin 8 → ℕ) (u v : Fin 8) : Bool :=
 (tI u).testBit v.val
private def edgesT1 : List (Fin 8 × Fin 8) :=
 [(0, 1), (0, 2), (0, 3), (1, 4), (2, 5), (2, 7), (3, 6), (4, 6), (4, 7), (5, 7), (6, 7)]
private def adjT1 : Fin 8 → Fin 8 → Bool :=
 zbL ![14, 17, 161, 65, 194, 132, 152, 116]
private def misT1 : List (List (Fin 8)) :=
 [[1, 2, 3], [2, 3, 4], [1, 3, 5], [0, 4, 5], [3, 4, 5],
  [1, 2, 6], [0, 5, 6], [1, 5, 6], [0, 7], [1, 3, 7]]
private def maxGT1 : Fin 8 → ℕ :=
 ![2, 1, 2, 1, 2, 1, 2, 3]
private def orderT1 : List (Fin 8) :=
 [1, 0, 4, 3, 2, 5, 6, 7]
private lemma zbM :
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
 have qL : (fun x : Fin 8 → Bool =>
   (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 2 && x 7) ||
   (x 3 && x 6) || (x 4 && x 6) || (x 4 && x 7) || (x 5 && x 7) || (x 6 && x 7)) =
   (fun x : Fin 8 → Bool => edgesT1.any (fun p => x p.1 && x p.2)) := by
  funext x
  simp only [edgesT1, List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc]
 rw [qL]
 exact zbK adjT1 edgesT1 misT1 maxGT1 orderT1 1 zbM
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
  ⟨[0, 4, 3, 2, 5, 6, 7], rfl⟩ rfl dfs_T1
lemma zbN (D : Circuit)
  (qp : ∀ g ∈ D.gates, (g.op = GateOp.and ∧ g.inputs.length ≤ 2) ∨ g.op = GateOp.or)
  (qL : circuitFun 8 D = (fun x : Fin 8 → Bool => edgesT1.any (fun p => x p.1 && x p.2))) :
  5 ≤ Nat.card {j : Fin D.gates.length // (D.gates.get j).op = GateOp.and} := by
 have tw := zbK adjT1 edgesT1 misT1 maxGT1 orderT1 1 zbM
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
  ⟨[0, 4, 3, 2, 5, 6, 7], rfl⟩ rfl dfs_T1
 by_contra h
 apply tw
 exact ⟨D, qp, by omega, qL⟩
def sample (k : Fin 40) (v : Fin 8) : Bool :=
 (([1065151898146, 2147418115, 21653750532, 34144976944,
   581968119809, 663661903884, 103293914128, 414195942664] : List Nat).getD v.val 0).testBit k.val
def targetFun (x : Fin 8 → Bool) : Bool :=
 edgesT1.any (fun p => x p.1 && x p.2)
set_option maxHeartbeats 4000000 in
lemma zbO : ∀ x : Fin 8 → Bool,
  (targetFun x = true → ∃ k : Fin 40,
   (36671 : Nat).testBit k.val = true ∧ ∀ v, sample k v = true → x v = true) ∧
  (targetFun x = false → ∃ k : Fin 40,
   (36671 : Nat).testBit k.val = false ∧ ∀ v, x v = true → sample k v = true) := by
 decide +kernel
lemma zbP (f : (Fin 8 → Bool) → Bool)
  (qr : ∀ x y, (∀ v, x v = true → y v = true) → f x = true → f y = true)
  (qJ : ∀ k : Fin 40, f (sample k) = (36671 : Nat).testBit k.val) :
  f = targetFun := by
 funext x
 obtain ⟨hpos, xo⟩ := zbO x
 cases ht : targetFun x with
 | false =>
   cases hf : f x with
   | false => rfl
   | true =>
     obtain ⟨k, hk, hle⟩ := xo ht
     have h := qr x (sample k) hle hf
     rw [qJ, hk] at h
     contradiction
 | true =>
   obtain ⟨k, hk, hle⟩ := hpos ht
   exact qr (sample k) x hle (by rw [qJ, hk])
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
 gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w
lemma getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
 simp
lemma zbQ (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
  (l₁ l₂ : List Bool) (qe : l₁.length = l₂.length)
  (hle : ∀ i, l₁.getD i false = true → l₂.getD i false = true) :
  op.eval l₁ = true → op.eval l₂ = true := by
 rcases hop with rfl | rfl
 ·simp only [GateOp.eval, List.all_eq_true, id_eq]
  intro h b hb
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
  have h1 : l₁.getD i false = true := by
   have hi1 : i < l₁.length := by omega
   rw [List.getD_eq_getElem _ _ hi1]
   exact h _ (List.getElem_mem hi1)
  have h2 := hle i h1
  rwa [List.getD_eq_getElem _ _ hi] at h2
 ·simp only [GateOp.eval, List.any_eq_true, id_eq]
  rintro ⟨b, hb, rfl⟩
  obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hb
  have h1 : l₁.getD i false = true := by
   rw [List.getD_eq_getElem _ _ hi]; exact hbi
  have h2 := hle i h1
  have hi2 : i < l₂.length := by omega
  rw [List.getD_eq_getElem _ _ hi2] at h2
  exact ⟨l₂[i], List.getElem_mem hi2, h2⟩
lemma zbR (gs : List Gate)
  (qr : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
  ∀ (w₁ w₂ : List Bool), w₁.length = w₂.length →
   (∀ i, w₁.getD i false = true → w₂.getD i false = true) →
   ∀ i, (wiresFrom gs w₁).getD i false = true → (wiresFrom gs w₂).getD i false = true := by
 induction gs with
 | nil =>
  intro w₁ w₂ _ hle i hi
  exact hle i hi
 | cons g gs ih =>
  intro w₁ w₂ qe hle i hi
  have w2 : wiresFrom (g :: gs) w₁ =
    wiresFrom gs (w₁ ++ [g.op.eval (g.inputs.map fun j => w₁.getD j false)]) := rfl
  have w4 : wiresFrom (g :: gs) w₂ =
    wiresFrom gs (w₂ ++ [g.op.eval (g.inputs.map fun j => w₂.getD j false)]) := rfl
  rw [w2] at hi
  rw [w4]
  apply ih (fun g' hg' => qr g' (List.mem_cons_of_mem g hg')) _ _ (by simp [qe]) _ i hi
  intro j hj
  by_cases hlt : j < w₁.length
  ·rw [List.getD_append _ _ _ _ hlt] at hj
   rw [List.getD_append _ _ _ _ (by omega)]
   exact hle j hj
  ·by_cases heq : j = w₁.length
   ·subst heq
    rw [getD_snoc_eq] at hj
    rw [qe, getD_snoc_eq]
    exact zbQ g.op (qr g List.mem_cons_self)
     (g.inputs.map fun k => w₁.getD k false) (g.inputs.map fun k => w₂.getD k false)
     (by simp) (by
      intro t ht
      by_cases ht_lt : t < g.inputs.length
      ·rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)] at ht
       rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)]
       simp only [List.getElem_map] at ht ⊢
       exact hle _ ht
      ·rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt ht_lt)] at ht
       exact Bool.noConfusion ht) hj
   ·rw [List.getD_eq_default _ _ (by simp; omega)] at hj
    exact Bool.noConfusion hj
lemma zbS (D : Circuit)
  (qp : ∀ g ∈ D.gates, (g.op = GateOp.and ∧ g.inputs.length ≤ 2) ∨ g.op = GateOp.or)
  (x y : Fin 8 → Bool) (hle : ∀ v, x v = true → y v = true)
  (h : circuitFun 8 D x = true) : circuitFun 8 D y = true := by
 have hg : ∀ g ∈ D.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
  intro g qo
  exact (qp g qo).imp And.left id
 change (wiresFrom D.gates (List.ofFn y)).getD D.output false = true
 refine zbR D.gates hg (List.ofFn x) (List.ofFn y) (by simp) ?_ D.output h
 intro i hi
 by_cases hi8 : i < 8
 ·rw [List.getD_eq_getElem _ _ (by simpa using hi8)] at hi ⊢
  simp only [List.getElem_ofFn] at hi ⊢
  exact hle _ hi
 ·rw [List.getD_eq_default _ _ (by simp; omega)] at hi
  exact Bool.noConfusion hi
lemma zbT (D : Circuit)
  (qp : ∀ g ∈ D.gates, (g.op = GateOp.and ∧ g.inputs.length ≤ 2) ∨ g.op = GateOp.or)
  (qJ : ∀ k : Fin 40, circuitFun 8 D (sample k) = (36671 : Nat).testBit k.val) :
  5 ≤ Nat.card {j : Fin D.gates.length // (D.gates.get j).op = GateOp.and} :=
 zbN D qp (zbP (circuitFun 8 D) (zbS D qp) qJ)
def baseValues : List Nat :=
 [2147418115, 663661903884, 34144976944, 728266375360, 21653750532,
  103293914128, 26322415680, 344922804352, 414195942664, 581968119809, 1065151898146]
def allowedInputs : List Nat := [0, 1, 2, 4, 5, 8, 9, 10]
def wireIndex (j : Nat) : Nat :=
 if j < 11 then ([1, 5, 3, 0, 2, 6, 0, 0, 7, 4, 0] : List Nat).getD j 0 else j - 3
lemma zbU : ∀ (j : Fin 11) (k : Fin 40), j.val ∈ allowedInputs →
  wireIndex j.val < 8 ∧
  (List.ofFn (sample k)).getD (wireIndex j.val) false = (baseValues.getD j.val 0).testBit k.val := by
 decide +kernel
def zbV (n : Nat) (v : Nat → Nat) (k : Fin 40) : List Bool :=
 List.ofFn (sample k) ++ List.ofFn (fun i : Fin n => (v (11 + i.val)).testBit k.val)
lemma zbW {n : Nat} (v : Nat → Nat) (k : Fin 40) (j : Nat)
  (qi : ∀ i : Fin 11, v i.val = baseValues.getD i.val 0)
  (hj : j < 11 + n) (ha : j ∈ allowedInputs ∨ 11 ≤ j) :
  (zbV n v k).getD (wireIndex j) false = (v j).testBit k.val := by
 by_cases hj11 : j < 11
 ·have qo : j ∈ allowedInputs := ha.resolve_right (by omega)
  obtain ⟨zk, heq⟩ := zbU ⟨j, hj11⟩ k qo
  unfold zbV
  rw [List.getD_append _ _ _ _ (by simpa using zk), heq, qi ⟨j, hj11⟩]
 ·have tK : 11 ≤ j := by omega
  simp only [zbV, wireIndex, if_neg hj11]
  rw [List.getD_append_right _ _ _ _ (by simp; omega)]
  simp only [List.length_ofFn]
  rw [List.getD_eq_getElem _ _ (by simp; omega)]
  simp only [List.getElem_ofFn]
  have he : 11 + (j - 3 - 8) = j := by omega
  rw [he]
def convertedGate {n : Nat} (ops : Fin n → Bool) (a b : Fin n → Nat) (i : Fin n) : Gate :=
 {op := if ops i then GateOp.and else GateOp.or
  inputs := [wireIndex (a i), wireIndex (b i)] }
def convertedGates {n : Nat} (ops : Fin n → Bool) (a b : Fin n → Nat) : List Gate :=
 List.ofFn (convertedGate ops a b)
lemma zbX {n : Nat} (ops : Fin n → Bool) (a b : Fin n → Nat) :
  ∀ g ∈ convertedGates ops a b,
   (g.op = GateOp.and ∧ g.inputs.length ≤ 2) ∨ g.op = GateOp.or := by
 intro g hg
 obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
 cases h : ops i <;> simp [convertedGate, h]
lemma zbY {n : Nat} (ops : Fin (n + 1) → Bool) (a b : Fin (n + 1) → Nat) :
  convertedGates ops a b =
   convertedGates (fun i => ops i.castSucc) (fun i => a i.castSucc) (fun i => b i.castSucc) ++
   [convertedGate ops a b (Fin.last n)] := by
 simp only [convertedGates, List.ofFn_succ', List.concat_eq_append]
 rfl
lemma zbZ {n : Nat} (ops : Fin n → Bool) (a b : Fin n → Nat) (v : Nat → Nat)
  (qi : ∀ i : Fin 11, v i.val = baseValues.getD i.val 0)
  (ha : ∀ i, a i ∈ allowedInputs ∨ 11 ≤ a i)
  (hb : ∀ i, b i ∈ allowedInputs ∨ 11 ≤ b i)
  (hs : ∀ i, a i < 11 + i.val ∧ b i < 11 + i.val ∧
   v (11 + i.val) = if ops i then v (a i) &&& v (b i) else v (a i) ||| v (b i))
  (k : Fin 40) :
  wiresFrom (convertedGates ops a b) (List.ofFn (sample k)) = zbV n v k := by
 induction n with
 | zero => simp [convertedGates, wiresFrom, zbV]
 | succ n ih =>
   rw [zbY]
   simp only [wiresFrom, List.foldl_append, List.foldl_cons, List.foldl_nil]
   have he := ih (fun i => ops i.castSucc) (fun i => a i.castSucc) (fun i => b i.castSucc)
    (fun i => ha i.castSucc) (fun i => hb i.castSucc) (fun i => hs i.castSucc)
   simp only [wiresFrom] at he
   rw [he]
   have hsa := (hs (Fin.last n)).1
   have hsb := (hs (Fin.last n)).2.1
   have hsv := (hs (Fin.last n)).2.2
   simp only [Fin.val_last] at hsa hsb hsv
   have hla := zbW (n := n) v k (a (Fin.last n)) qi hsa (ha (Fin.last n))
   have hlb := zbW (n := n) v k (b (Fin.last n)) qi hsb (hb (Fin.last n))
   simp only [convertedGate, List.map_cons, List.map_nil]
   rw [hla, hlb]
   have zK : (if ops (Fin.last n) then GateOp.and else GateOp.or).eval
     [(v (a (Fin.last n))).testBit k.val, (v (b (Fin.last n))).testBit k.val] =
     (v (11 + n)).testBit k.val := by
    rw [hsv]
    cases h : ops (Fin.last n) <;> simp [h, GateOp.eval, Nat.testBit_and, Nat.testBit_or]
   rw [zK]
   simp only [zbV, List.ofFn_succ', List.concat_eq_append, Fin.coe_castSucc, Fin.val_last,
    List.append_assoc]
lemma zb0 {n : Nat} (ops : Fin n → Bool) (a b : Fin n → Nat) :
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
  (qi : ∀ i : Fin 11, v i.val = baseValues.getD i.val 0)
  (ha : ∀ i, (a i).val ∈ allowedInputs ∨ 11 ≤ (a i).val)
  (hb : ∀ i, (b i).val ∈ allowedInputs ∨ 11 ≤ (b i).val)
  (hs : ∀ i, (a i).val < 11 + i.val ∧ (b i).val < 11 + i.val ∧
   v (11 + i.val) = if ops i then v (a i).val &&& v (b i).val else v (a i).val ||| v (b i).val)
  (ql : v 24 = 36671) :
  5 ≤ Nat.card {i : Fin 14 // ops i = true} := by
 let D : Circuit := { gates := convertedGates ops (fun i => (a i).val) (fun i => (b i).val), output := 21 }
 have qp := zbX ops (fun i => (a i).val) (fun i => (b i).val)
 have qJ : ∀ k : Fin 40, circuitFun 8 D (sample k) = (36671 : Nat).testBit k.val := by
  intro k
  change (wiresFrom (convertedGates ops (fun i => (a i).val) (fun i => (b i).val))
   (List.ofFn (sample k))).getD 21 false = _
  rw [zbZ ops (fun i => (a i).val) (fun i => (b i).val) v qi ha hb hs k]
  have qI := zbW (n := 14) v k 24 qi (by decide) (Or.inr (by decide))
  have zk : wireIndex 24 = 21 := by decide
  rw [zk, ql] at qI
  exact qI
 have qS := zbT D qp qJ
 change 5 ≤ Nat.card {j : Fin (convertedGates ops (fun i => (a i).val) (fun i => (b i).val)).length //
  ((convertedGates ops (fun i => (a i).val) (fun i => (b i).val)).get j).op = GateOp.and} at qS
 rwa [zb0] at qS
namespace Pin
open PEqualNP.CircuitLowerBounds
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
 gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w
theorem zb1 (gs gs' : List Gate) (w : List Bool) :
  wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
 simp [wiresFrom, List.foldl_append]
theorem zb2 (gs : List Gate) : ∀ w : List Bool,
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
theorem zb3 (gs : List Gate) (w : List Bool) :
  (wiresFrom gs w).length = w.length + gs.length := by
 obtain ⟨t, ht, hl⟩ := zb2 gs w
 rw [ht]; simp [hl]
theorem zb4 {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
  (L ++ [S]).getD j d = L.getD j d := by
 by_cases hj : j < L.length
 ·exact List.getD_append _ _ _ _ hj
 ·rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
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
def zb5 (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
 match op with
 | GateOp.and => simpAnd m ins
 | GateOp.or => simpOr m ins
 | _ => (none, Sum.inl false)
theorem zb6 (op : GateOp) (m : ℕ) (ins : List Stat) :
  ∀ g ∈ (zb5 op m ins).1, Ok g := by
 intro g hg
 cases op <;> simp only [zb5] at hg
 ·rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
   simp [simpAnd] at hg <;> (subst hg; simp [Ok])
 ·rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
   simp [simpOr] at hg <;> (subst hg; simp [Ok])
 all_goals simp at hg
theorem zb7 (op : GateOp) (m : ℕ) (ins : List Stat)
  (hop : op = GateOp.and ∨ op = GateOp.or) (qe : ins.length ≤ 2)
  (hc : ∃ c, Sum.inl c ∈ ins) :
  (zb5 op m ins).1 = none := by
 obtain ⟨c, hc⟩ := hc
 rcases hop with rfl | rfl
 ·rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
   simp_all [zb5, simpAnd]
 ·rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
   simp_all [zb5, simpOr]
theorem zb8 (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
  (w : List Bool) (ins : List Stat) (qe : ins.length ≤ 2)
  (hv : ∀ s ∈ ins, s.Valid w.length) :
  ((zb5 op w.length ins).2).Valid (w.length + (zb5 op w.length ins).1.toList.length) ∧
  ((zb5 op w.length ins).2).val (wiresFrom (zb5 op w.length ins).1.toList w)
   = op.eval (ins.map (Stat.val w)) := by
 rcases hop with rfl | rfl
 ·rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
  ·simp [zb5, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
  ·cases a <;> simp_all [zb5, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
  ·cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
    simp_all [zb5, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
  ·simp at qe
 ·rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
  ·simp [zb5, simpOr, Stat.Valid, Stat.val, GateOp.eval]
  ·cases a <;> simp_all [zb5, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
  ·cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
    simp_all [zb5, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
  ·simp at qe
def zb9 (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
 (acc.1 ++ [(zb5 g.op (n + acc.2.length)
   (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
  acc.2 ++ (zb5 g.op (n + acc.2.length)
   (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)
def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
 gs.foldl (zb9 n) acc
theorem zca {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
 cases o <;> simp
theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
  (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
 induction gs with
 | nil => intro acc h; exact h
 | cons g gs ih =>
  intro acc h
  apply ih (zb9 n acc g)
  intro g' hg'
  rcases List.mem_append.1 hg' with h1 | h1
  ·exact h g' h1
  ·exact zb6 _ _ _ g' (by simpa using h1)
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
theorem zcb (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
  ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
   Inv n y (wiresFrom gs w) (elim n gs acc) := by
 induction gs with
 | nil => intro w acc _ h; exact h
 | cons g gs ih =>
  intro w acc hok h
  apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (zb9 n acc g)
   (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
  obtain ⟨hl, hi⟩ := h
  set w' := wiresFrom acc.2 y with hw'
  have lw' : w'.length = n + acc.2.length := by rw [hw', zb3, hy]
  set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
  have yj := hok g List.mem_cons_self
  have hs := zb8 g.op yj.1 w' ins (by simpa [hins] using yj.2)
   (by
    intro s hs
    obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
    rw [lw']; exact (hi a).1)
  rw [lw'] at hs
  set r := zb5 g.op (n + acc.2.length) ins with hr
  have uS : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
   rw [hins, List.map_map]
   apply List.map_congr_left
   intro a _
   exact (hi a).2
  have xz : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
   rw [zb1]
  obtain ⟨t, ht, htl⟩ := zb2 r.1.toList w'
  refine ⟨by simp [zb9, hl], ?_⟩
  intro i
  show ((acc.1 ++ [r.2]).getD i (Sum.inl false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
   ((acc.1 ++ [r.2]).getD i (Sum.inl false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
  rw [xz, List.length_append, ← Nat.add_assoc]
  by_cases hil : i = acc.1.length
  ·subst hil
   rw [getD_snoc_eq, hl, getD_snoc_eq]
   exact ⟨hs.1, by rw [hs.2, uS]⟩
  ·rw [zb4 _ _ _ _ hil, zb4 _ _ _ _ (by omega)]
   refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
   rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
   exact (hi i).2
def zcc (n : ℕ) (v : Fin n) (b : Bool) : List Stat :=
 List.ofFn (fun i : Fin n => if i = v then Sum.inl b else Sum.inr i)
theorem zcd (n : ℕ) (v : Fin n) (b : Bool) (y : Fin n → Bool) :
  Inv n (List.ofFn y) (List.ofFn (Function.update y v b)) (zcc n v b, []) := by
 refine ⟨by simp [zcc], ?_⟩
 intro i
 by_cases hlt : i < n
 ·by_cases hv : (⟨i, hlt⟩ : Fin n) = v
  ·subst hv
   simp [zcc, hlt, Stat.Valid, Stat.val]
  ·simp [zcc, hlt, hv, Stat.Valid, Stat.val, wiresFrom, Function.update_of_ne hv]
 ·rw [List.getD_eq_default _ _ (by simp [zcc]; omega),
   List.getD_eq_default _ _ (by simp; omega)]
  exact ⟨trivial, rfl⟩
def isOr : GateOp → Bool
 | .or => true
 | _ => false
def orCount (gs : List Gate) : ℕ := gs.countP (fun g => isOr g.op)
theorem zce (op : GateOp) (m : ℕ) (ins : List Stat) :
  orCount (zb5 op m ins).1.toList ≤ if isOr op then 1 else 0 := by
 cases op <;> rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;>
  (try cases a) <;> (try cases b) <;>
  simp [zb5, simpAnd, simpOr, orCount, isOr]
theorem zcf (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
  (m : ℕ) (w : List Bool) (ins : List Stat) (vs : List Bool)
  (qe : ins.length ≤ 2)
  (hr : List.Forall₂ (fun (s : Stat) b => s ≠ Sum.inl false → s.val w = b) ins vs)
  (xP : orCount (zb5 op m ins).1.toList = if isOr op then 1 else 0)
  (hnf : (zb5 op m ins).2 ≠ Sum.inl false) :
  op.eval (ins.map (Stat.val w)) = op.eval vs := by
 rcases hop with rfl | rfl
 all_goals
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  ·cases hr; rfl
  ·cases hr with
   | cons ha ht =>
    cases ht
    cases a with
    | inl a => cases a <;> simp_all [zb5, simpAnd, simpOr, orCount, isOr, Stat.val, GateOp.eval]
    | inr a => simp_all [zb5, simpAnd, simpOr, orCount, isOr, Stat.val, GateOp.eval]
  ·cases hr with
   | cons ha ht =>
    cases ht with
    | cons hb htt =>
     cases htt
     rcases a with ca | ia <;> rcases b with cb | ib
     ·cases ca <;> cases cb <;>
       simp_all [zb5, simpAnd, simpOr, orCount, isOr, Stat.val, GateOp.eval]
     ·cases ca <;>
       simp_all [zb5, simpAnd, simpOr, orCount, isOr, Stat.val, GateOp.eval]
     ·cases cb <;>
       simp_all [zb5, simpAnd, simpOr, orCount, isOr, Stat.val, GateOp.eval]
     ·simp_all [zb5, simpAnd, simpOr, orCount, isOr, Stat.val, GateOp.eval]
  ·simp at qe
theorem zcg (gs hs : List Gate) : orCount (gs ++ hs) = orCount gs + orCount hs := by
 simp [orCount]
theorem zch (g : Gate) (gs : List Gate) :
  orCount (g :: gs) = (if isOr g.op then 1 else 0) + orCount gs := by
 simp [orCount, List.countP_cons, Nat.add_comm]
theorem zci (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
  orCount (elim n gs acc).2 ≤ orCount acc.2 + orCount gs := by
 induction gs with
 | nil => intro acc; simp [elim, orCount]
 | cons g gs ih =>
  intro acc
  have h1 := ih (zb9 n acc g)
  have h2 := zce g.op (n + acc.2.length)
   (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
  change orCount (elim n gs (zb9 n acc g)).2 ≤ _
  rw [zch]
  have qQ : orCount (zb9 n acc g).2 = orCount acc.2 +
    orCount (zb5 g.op (n + acc.2.length)
     (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList := by
   simp only [zb9, zcg]
  rw [qQ] at h1
  omega
def UInv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
 acc.1.length = w.length ∧ ∀ i : ℕ,
  (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
  ((acc.1.getD i (Sum.inl false)) ≠ Sum.inl false →
   (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 y) = w.getD i false)
theorem zcj (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
  ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → UInv n y w acc →
   orCount (elim n gs acc).2 = orCount acc.2 + orCount gs →
   UInv n y (wiresFrom gs w) (elim n gs acc) := by
 induction gs with
 | nil => intro w acc _ h _; exact h
 | cons g gs ih =>
  intro w acc hok h qS
  have hle := zci n gs (zb9 n acc g)
  have xy := zce g.op (n + acc.2.length)
   (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
  have vT : orCount (elim n gs (zb9 n acc g)).2 =
    orCount acc.2 + ((if isOr g.op then 1 else 0) + orCount gs) := by
   simpa only [elim, List.foldl_cons, zch] using qS
  have qQ : orCount (zb9 n acc g).2 = orCount acc.2 +
    orCount (zb5 g.op (n + acc.2.length)
     (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList := by
   simp only [zb9, zcg]
  rw [qQ] at hle
  have xP : orCount (zb5 g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList =
    if isOr g.op then 1 else 0 := by omega
  apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (zb9 n acc g)
   (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
  ·obtain ⟨hl, hi⟩ := h
   set w' := wiresFrom acc.2 y with hw'
   have lw' : w'.length = n + acc.2.length := by rw [hw', zb3, hy]
   set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
   have yj := hok g List.mem_cons_self
   have hs := zb8 g.op yj.1 w' ins (by simpa [hins] using yj.2)
    (by
     intro s hs
     obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
     rw [lw']; exact (hi a).1)
   rw [lw'] at hs
   set r := zb5 g.op (n + acc.2.length) ins with hr
   have xk : List.Forall₂ (fun (s : Stat) b => s ≠ Sum.inl false → s.val w' = b)
     ins (g.inputs.map fun i => w.getD i false) := by
    rw [hins]
    induction g.inputs with
    | nil => exact List.Forall₂.nil
    | cons i is ih => exact List.Forall₂.cons (hi i).2 ih
   have xz : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
    rw [zb1]
   obtain ⟨t, ht, htl⟩ := zb2 r.1.toList w'
   refine ⟨by simp [zb9, hl], ?_⟩
   intro i
   show ((acc.1 ++ [r.2]).getD i (Sum.inl false)).Valid
     (n + (acc.2 ++ r.1.toList).length) ∧
    (((acc.1 ++ [r.2]).getD i (Sum.inl false)) ≠ Sum.inl false →
     ((acc.1 ++ [r.2]).getD i (Sum.inl false)).val
      (wiresFrom (acc.2 ++ r.1.toList) y) = _)
   rw [xz, List.length_append, ← Nat.add_assoc]
   by_cases hil : i = acc.1.length
   ·subst hil
    rw [getD_snoc_eq, hl, getD_snoc_eq]
    refine ⟨hs.1, ?_⟩
    intro hnf
    rw [hs.2]
    exact zcf g.op yj.1 (n + acc.2.length) w' ins _
     (by simpa [hins] using yj.2) xk xP hnf
   ·rw [zb4 _ _ _ _ hil, zb4 _ _ _ _ (by omega)]
    refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
    intro hnf
    rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
    exact (hi i).2 hnf
  ·rw [qQ]
   omega
theorem zck (n : ℕ) (v : Fin n) (y : Fin n → Bool) :
  UInv n (List.ofFn y) (List.ofFn y) (zcc n v false, []) := by
 refine ⟨by simp [zcc], ?_⟩
 intro i
 by_cases hlt : i < n
 ·by_cases hv : (⟨i, hlt⟩ : Fin n) = v
  ·subst hv
   simp [zcc, hlt, Stat.Valid, Stat.val]
  ·simp [zcc, hlt, hv, Stat.Valid, Stat.val, wiresFrom]
 ·rw [List.getD_eq_default _ _ (by simp [zcc]; omega)]
  exact ⟨trivial, by simp⟩
theorem zcl (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (v : Fin n)
  (qr : PEqualNP.MetaComplexity.Monotone2 C)
  (wD : ∃ x : Fin n → Bool,
   C.eval (List.ofFn x) ≠ C.eval (List.ofFn (Function.update x v false)))
  (qE : ∃ x : Fin n → Bool,
   C.eval (List.ofFn (Function.update x v false)) = true)
  (q5 : ∃ x : Fin n → Bool,
   C.eval (List.ofFn (Function.update x v false)) = false) :
  ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
   PEqualNP.MetaComplexity.Monotone2 D ∧
   orCount D.gates + 1 ≤ orCount C.gates ∧
   ∀ x : Fin n → Bool,
    D.eval (List.ofFn x) = C.eval (List.ofFn (Function.update x v false)) := by
 have hok : ∀ g ∈ C.gates, Ok g := by
  intro g hg
  obtain ⟨h1, h2⟩ := qr g hg
  refine ⟨?_, h2⟩
  simpa using h1
 set acc := elim n C.gates (zcc n v false, []) with q4
 have yO : ∀ y : Fin n → Bool,
   Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn (Function.update y v false))) acc := by
  intro y
  exact zcb n _ (by simp) C.gates _ _ hok (zcd n v false y)
 have zl : ∀ y : Fin n → Bool,
   (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn y))
    = C.eval (List.ofFn (Function.update y v false)) := by
  intro y
  exact ((yO y).2 C.output).2
 have wz : orCount acc.2 ≤ orCount C.gates := by
  simpa only [← q4, orCount, List.countP_nil, Nat.zero_add] using
   zci n C.gates (zcc n v false, [])
 have u6 : orCount acc.2 < orCount C.gates := by
  by_contra hn
  have heq : orCount acc.2 = orCount C.gates := by omega
  obtain ⟨x, hx⟩ := wD
  have hu : UInv n (List.ofFn x) (wiresFrom C.gates (List.ofFn x)) acc :=
   zcj n _ (by simp) C.gates _ _ hok (zck n v x)
    (by simpa only [← q4, orCount, List.countP_nil, Nat.zero_add] using heq)
  have hst : acc.1.getD C.output (Sum.inl false) = Sum.inl false := by
   by_contra hh
   have ho := (hu.2 C.output).2 hh
   exact hx (ho.symm.trans (zl x))
  obtain ⟨y, hy⟩ := qE
  have hv := zl y
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
   obtain ⟨y, hy⟩ := q5
   have hv := zl y
   rw [hst] at hv
   simp only [Stat.val] at hv
   exact Bool.false_ne_true (hv.trans hy).symm
  | false =>
   exfalso
   obtain ⟨y, hy⟩ := qE
   have hv := zl y
   rw [hst] at hv
   simp only [Stat.val] at hv
   exact Bool.false_ne_true (hv.trans hy)
 | inr j =>
  refine ⟨⟨acc.2, j⟩, hmD _, by change orCount acc.2 + 1 ≤ orCount C.gates; omega, ?_⟩
  intro x
  have hv := zl x
  rw [hst] at hv
  exact hv
end Pin
namespace OrYF
private def pd (n b z : Nat) : List Nat :=
 List.ofFn (fun i : Fin n => z / b ^ i.val % b)
private def pl (n b z : Nat) (t : List Nat) : List Nat :=
 List.ofFn (fun i : Fin n => t.getD (z / b ^ i.val % b) 0)
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
  (zn : ∀ f ∈ B, Meet D (π ⁻¹' f)) {f} (h : Meet B f) : Meet D (π ⁻¹' f) := by
 induction h with
 | atom hf => exact zn _ hf
 | top => exact Meet.top
 | bot => exact Meet.bot
 | inter _ _ hi hj => exact hi.inter hj
theorem weaken {X : Type} {B D : Set (Set X)} (hd : B ⊆ D) {f}
  (h : Meet B f) : Meet D f :=
 mapMeet id (fun _ hf => Meet.atom (hd hf)) h
theorem freeMap {X Y : Type} {B : Set (Set X)} {D : Set (Set Y)} (π : Y → X)
  (zn : ∀ f ∈ B, Meet D (π ⁻¹' f)) {k f} (h : Run B k f) : Run D k (π ⁻¹' f) := by
 induction h generalizing D with
 | done hf => exact Run.done (mapMeet π zn hf)
 | @add B a b k f ha hb _ ih =>
  apply Run.add (mapMeet π zn ha) (mapMeet π zn hb)
  apply ih
  intro g hg
  rcases Set.mem_insert_iff.mp hg with rfl | hg
  ·exact Meet.atom (Set.mem_insert _ _)
  ·exact weaken (Set.subset_insert _ _) (zn _ hg)
def Good {X Y : Type} (π : Y → X) (p q : X) (f : Set X) : Prop :=
 (p ∈ f ↔ q ∈ f) ∨ π ⁻¹' f = ∅
theorem zcm {X Y : Type} {B : Set (Set X)} {π : Y → X} {p q : X}
  (zn : ∀ f ∈ B, Good π p q f) {f} (h : Meet B f) : Good π p q f := by
 induction h with
 | atom h => exact zn _ h
 | top => exact Or.inl Iff.rfl
 | bot => exact Or.inr rfl
 | inter _ _ ih jh =>
  rcases ih with h | h
  ·rcases jh with j | j
   ·exact Or.inl (and_congr h j)
   ·exact Or.inr (by rw [Set.preimage_inter, j, Set.inter_empty])
  ·exact Or.inr (by rw [Set.preimage_inter, h, Set.empty_inter])
theorem paidMap {X Y : Type} {B : Set (Set X)} {D : Set (Set Y)}
  (π : Y → X) (p q : X) (zn : ∀ f ∈ B, Meet D (π ⁻¹' f))
  (yL : ∀ f ∈ B, Good π p q f) {k f} (h : Run B k f) (bad : ¬ Good π p q f) :
  ∃ j < k, Run D j (π ⁻¹' f) := by
 classical
 induction h generalizing D with
 | done hf => exact (bad (zcm yL hf)).elim
 | @add B a b k f ha hb qb ih =>
  have aa := mapMeet π zn ha
  have ab := mapMeet π zn hb
  by_cases gg : Good π p q (a ∪ b)
  ·let D' := insert ((π ⁻¹' a) ∪ (π ⁻¹' b)) D
   have m : ∀ g ∈ insert (a ∪ b) B, Meet D' (π ⁻¹' g) := by
    intro g hg
    rcases Set.mem_insert_iff.mp hg with rfl | hg
    ·exact Meet.atom (Set.mem_insert _ _)
    ·exact weaken (Set.subset_insert _ _) (zn _ hg)
   obtain ⟨j, hj, hr⟩ := ih m (fun g hg => (Set.mem_insert_iff.mp hg).elim
    (fun e => e ▸ gg) (yL g)) bad
   exact ⟨j + 1, by omega, Run.add aa ab hr⟩
  ·have wo : Meet D (π ⁻¹' (a ∪ b)) := by
    rcases zcm yL ha with h | h
    ·rcases zcm yL hb with z | z
     ·exact (gg (Or.inl (or_congr h z))).elim
     ·simpa [Set.preimage_union, z] using aa
    ·simpa [Set.preimage_union, h] using ab
   exact ⟨k, by omega, freeMap π (fun g hg => (Set.mem_insert_iff.mp hg).elim
    (fun e => e ▸ wo) (zn g)) qb⟩
def zcn {X : Type} (le : X → X → Prop) (f : Set X) : Prop :=
 ∀ x y, le x y → x ∈ f → y ∈ f
theorem zco {X : Type} {le : X → X → Prop} {B : Set (Set X)}
  (hB : ∀ x ∈ B, zcn le x) {f : Set X} (hf : Meet B f) : zcn le f := by
 induction hf with
 | atom hx => exact hB _ hx
 | top => intro _ _ _ _; trivial
 | bot => intro _ _ _ hx; exact hx.elim
 | inter _ _ ih1 ih2 => intro x y hxy ⟨h1, h2⟩; exact ⟨ih1 x y hxy h1, ih2 x y hxy h2⟩
theorem zcp {X : Type} {le : X → X → Prop} {B : Set (Set X)}
  (hB : ∀ x ∈ B, zcn le x) {k : ℕ} {f : Set X} (hr : Run B k f) : zcn le f := by
 induction hr with
 | done hf => exact zco hB hf
 | @add B a b k f ha hb _ ih =>
  apply ih
  intro g hg
  rcases Set.mem_insert_iff.mp hg with rfl | hg
  ·intro x y hxy hx
   rcases hx with h1 | h2
   ·exact Or.inl (zco hB ha x y hxy h1)
   ·exact Or.inr (zco hB hb x y hxy h2)
  ·exact hB g hg
theorem zcq {X : Type} {B D : Set (Set X)} {S : Set X}
  (q0 : ∀ x ∈ B, ∃ x', Meet D x' ∧ x' ⊆ x ∧ x' ∩ S = x ∩ S)
  {f : Set X} (hf : Meet B f) :
  ∃ f', Meet D f' ∧ f' ⊆ f ∧ f' ∩ S = f ∩ S := by
 induction hf with
 | atom hx => exact q0 _ hx
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
theorem zcr {X : Type} {B D : Set (Set X)} {S : Set X}
  (q0 : ∀ x ∈ B, ∃ x', Meet D x' ∧ x' ⊆ x ∧ x' ∩ S = x ∩ S)
  {k : ℕ} {f : Set X} (hr : Run B k f) :
  ∃ f', Run D k f' ∧ f' ⊆ f ∧ f' ∩ S = f ∩ S := by
 induction hr generalizing D with
 | done hf =>
  obtain ⟨f', hm, hs, he⟩ := zcq q0 hf
  exact ⟨f', Run.done hm, hs, he⟩
 | @add B a b k f ha hb _ ih =>
  obtain ⟨a', hma, hsa, hea⟩ := zcq q0 ha
  obtain ⟨b', hmb, hsb, heb⟩ := zcq q0 hb
  let D' := insert (a' ∪ b') D
  have uz : ∀ x ∈ insert (a ∪ b) B, ∃ x', Meet D' x' ∧ x' ⊆ x ∧ x' ∩ S = x ∩ S := by
   intro x hx
   rcases Set.mem_insert_iff.mp hx with rfl | hx
   ·refine ⟨a' ∪ b', Meet.atom (Set.mem_insert _ _), Set.union_subset_union hsa hsb, ?_⟩
    rw [Set.union_inter_distrib_right, Set.union_inter_distrib_right, hea, heb]
   ·obtain ⟨x', hmx, hsx, hex⟩ := q0 x hx
    exact ⟨x', weaken (Set.subset_insert _ _) hmx, hsx, hex⟩
  obtain ⟨f', hrf', hsf', hef'⟩ := ih uz
  exact ⟨f', Run.add hma hmb hrf', hsf', hef'⟩
theorem zcs {X : Type} {le : X → X → Prop}
  {B D : Set (Set X)} {S target : Set X}
  (hSt : S ⊆ target)
  (yd : ∀ f, zcn le f → S ⊆ f → target ⊆ f)
  (hD : ∀ x ∈ D, zcn le x)
  (q0 : ∀ x ∈ B, ∃ x', Meet D x' ∧ x' ⊆ x ∧ x' ∩ S = x ∩ S)
  {k : ℕ} (hr : Run B k target) :
  Run D k target := by
 obtain ⟨f', hrf', qu, heq⟩ := zcr q0 hr
 have hup : zcn le f' := zcp hD hrf'
 have ta : S ⊆ f' := by
  intro x hx
  have : x ∈ target ∩ S := ⟨hSt hx, hx⟩
  rw [← heq] at this
  exact this.1
 have tB : target ⊆ f' := yd f' hup ta
 have : f' = target := Set.Subset.antisymm qu tB
 exact this ▸ hrf'
def zct : ℕ → (ℕ → Bool) → ℕ
 | 0, _ => 0
 | k + 1, p => if p k then zct k p ||| (1 <<< k) else zct k p
theorem zcu (k s : ℕ) : (1 <<< k).testBit s = decide (k = s) := by
 rw [Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow]
theorem zcv (N : ℕ) (p : ℕ → Bool) (s : ℕ) :
  (zct N p).testBit s = (decide (s < N) && p s) := by
 induction N with
 | zero => simp [zct]
 | succ k ih =>
  simp only [zct]
  split_ifs with hpk
  ·rw [Nat.testBit_or, ih, zcu]
   by_cases hlt : s < k
   ·have hne : k ≠ s := by omega
    have yk : s < k + 1 := by omega
    simp [hlt, yk, hne]
   ·by_cases heq : k = s
    ·subst heq; simp [hpk]
    ·have yk : ¬ (s < k + 1) := by omega
     simp [hlt, yk, heq]
  ·rw [ih]
   by_cases hlt : s < k
   ·have yk : s < k + 1 := by omega
    simp [hlt, yk]
   ·by_cases heq : k = s
    ·subst heq; simp [hpk]
    ·have yk : ¬ (s < k + 1) := by omega
     simp [hlt, yk]
theorem zcw {N : ℕ} {p : ℕ → Bool} {s : ℕ}
  (h : (zct N p).testBit s = true) : s < N := by
 rw [zcv, Bool.and_eq_true, decide_eq_true_eq] at h
 exact h.1
def hasEdge (E : List (ℕ × ℕ)) (s : ℕ) : Bool :=
 E.any (fun e => s.testBit e.1 && s.testBit e.2)
theorem zcx (E : List (ℕ × ℕ)) (s : ℕ) :
  hasEdge E s = true ↔ ∃ e ∈ E, s.testBit e.1 = true ∧ s.testBit e.2 = true := by
 simp [hasEdge]
def univYF (n : ℕ) (F : List (ℕ × ℕ)) : ℕ :=
 zct (2 ^ n) (fun s => !hasEdge F s)
def ttVarYF (n v maskYF : ℕ) : ℕ :=
 zct (2 ^ n) (fun s => maskYF.testBit s && s.testBit v)
def rawYF (n : ℕ) (maskYF : ℕ) : List ℕ :=
 (List.range n).map (fun v => ttVarYF n v maskYF)
def zcy (n : ℕ) (H : List (ℕ × ℕ)) (maskYF : ℕ) : ℕ :=
 zct (2 ^ n) (fun s => maskYF.testBit s && hasEdge H s)
def zcz (H : List (ℕ × ℕ)) : ℕ :=
 H.foldl (fun acc e => acc ||| (1 <<< ((1 <<< e.1) ||| (1 <<< e.2)))) 0
def zcA (n a maskYF : ℕ) : ℕ :=
 zct (2 ^ n) (fun s => maskYF.testBit s && ((s &&& a) == a))
def zcB (n : ℕ) (H : List (ℕ × ℕ)) (maskYF : ℕ) : List ℕ :=
 (0 :: (List.range n).map (fun v => 1 <<< v) ++
  H.map (fun e => (1 <<< e.1) ||| (1 <<< e.2))).map (fun m => zcA n m maskYF)
def undirEq (e₁ e₂ : ℕ × ℕ) : Bool :=
 (e₁.1 == e₂.1 && e₁.2 == e₂.2) || (e₁.1 == e₂.2 && e₁.2 == e₂.1)
abbrev zcC (n : ℕ) (H F : List (ℕ × ℕ)) : Prop :=
 (∀ e ∈ H, e.1 < n ∧ e.2 < n ∧ e.1 ≠ e.2) ∧
 (∀ e ∈ F, e.1 < n ∧ e.2 < n ∧ e.1 ≠ e.2) ∧
 (∀ e ∈ H, ∀ f ∈ F, undirEq e f = false)
theorem zcD (n : ℕ) (F : List (ℕ × ℕ)) (s : ℕ) :
  (univYF n F).testBit s = (decide (s < 2 ^ n) && !hasEdge F s) :=
 zcv (2 ^ n) _ s
theorem zcE {n : ℕ} {F : List (ℕ × ℕ)} {s : ℕ}
  (h : (univYF n F).testBit s = true) : s < 2 ^ n :=
 zcw h
theorem zcF {n v maskYF : ℕ} (hM : ∀ s, maskYF.testBit s = true → s < 2 ^ n) (s : ℕ) :
  (ttVarYF n v maskYF).testBit s = (maskYF.testBit s && s.testBit v) := by
 rw [ttVarYF, zcv]
 by_cases hm : maskYF.testBit s = true
 ·simp [hm, hM s hm]
 ·simp [hm]
theorem zcG {n : ℕ} {H : List (ℕ × ℕ)} {maskYF : ℕ}
  (hM : ∀ s, maskYF.testBit s = true → s < 2 ^ n) (s : ℕ) :
  (zcy n H maskYF).testBit s = (maskYF.testBit s && hasEdge H s) := by
 rw [zcy, zcv]
 by_cases hm : maskYF.testBit s = true
 ·simp [hm, hM s hm]
 ·simp [hm]
theorem zcH {n a maskYF : ℕ}
  (hM : ∀ s, maskYF.testBit s = true → s < 2 ^ n) (s : ℕ) :
  (zcA n a maskYF).testBit s = (maskYF.testBit s && ((s &&& a) == a)) := by
 rw [zcA, zcv]
 by_cases hm : maskYF.testBit s = true
 ·simp [hm, hM s hm]
 ·simp [hm]
theorem zcI (H : List (ℕ × ℕ)) (acc s : ℕ) :
  (H.foldl (fun a e => a ||| (1 <<< ((1 <<< e.1) ||| (1 <<< e.2)))) acc).testBit s =
   (acc.testBit s || H.any (fun e => decide (((1 <<< e.1) ||| (1 <<< e.2)) = s))) := by
 induction H generalizing acc with
 | nil => simp
 | cons e qa ih =>
  simp only [List.foldl_cons, List.any_cons]
  rw [ih, Nat.testBit_or, zcu, Bool.or_assoc]
theorem zcJ (H : List (ℕ × ℕ)) (s : ℕ) :
  (zcz H).testBit s = H.any (fun e => decide (((1 <<< e.1) ||| (1 <<< e.2)) = s)) := by
 simpa [zcz] using zcI H 0 s
theorem zcK {n u v : ℕ} (hu : u < n) (hv : v < n) :
  ((1 <<< u) ||| (1 <<< v)) < 2 ^ n := by
 have h1 : (1 <<< u) < 2 ^ n := by
  rw [Nat.shiftLeft_eq, one_mul]; exact Nat.pow_lt_pow_right (by omega) hu
 have h2 : (1 <<< v) < 2 ^ n := by
  rw [Nat.shiftLeft_eq, one_mul]; exact Nat.pow_lt_pow_right (by omega) hv
 exact Nat.or_lt_two_pow h1 h2
theorem zcL {n u : ℕ} (hu : u < n) : (1 <<< u) < 2 ^ n := by
 rw [Nat.shiftLeft_eq, one_mul]; exact Nat.pow_lt_pow_right (by omega) hu
theorem zcM (u v w : ℕ) :
  (((1 <<< u) ||| (1 <<< v)).testBit w = true) ↔ w = u ∨ w = v := by
 rw [Nat.testBit_or, zcu, zcu, Bool.or_eq_true,
  decide_eq_true_eq, decide_eq_true_eq]
 tauto
theorem zcN {n : ℕ} {H F : List (ℕ × ℕ)} (hv : zcC n H F)
  {e : ℕ × ℕ} (he : e ∈ H) :
  (univYF n F).testBit ((1 <<< e.1) ||| (1 <<< e.2)) = true := by
 rcases hv with ⟨hH, hF, q3⟩
 obtain ⟨hu, hv', hne⟩ := hH e he
 rw [zcD, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
 refine ⟨zcK hu hv', ?_⟩
 rw [Bool.eq_false_iff]
 intro hf
 rw [zcx] at hf
 obtain ⟨f, hfmem, hf1, hf2⟩ := hf
 rw [zcM] at hf1 hf2
 obtain ⟨_, _, hfne⟩ := hF f hfmem
 have hd := q3 e he f hfmem
 simp only [undirEq, Bool.or_eq_false_iff, Bool.and_eq_false_iff, beq_eq_false_iff_ne] at hd
 rcases hf1 with h1 | h1 <;> rcases hf2 with h2 | h2
 ·exact hfne (h1.trans h2.symm)
 ·rcases hd.1 with h | h <;> exact h (by omega)
 ·rcases hd.2 with h | h <;> exact h (by omega)
 ·exact hfne (h1.trans h2.symm)
theorem zcO {n : ℕ} {H F : List (ℕ × ℕ)} (hv : zcC n H F)
  {e : ℕ × ℕ} (he : e ∈ H) :
  (zcy n H (univYF n F)).testBit ((1 <<< e.1) ||| (1 <<< e.2)) = true := by
 rw [zcG (fun _ => zcE), Bool.and_eq_true]
 refine ⟨zcN hv he, ?_⟩
 rw [zcx]
 exact ⟨e, he, (zcM _ _ _).mpr (Or.inl rfl), (zcM _ _ _).mpr (Or.inr rfl)⟩
theorem zcP (n : ℕ) (H F : List (ℕ × ℕ)) :
  zcy n H (univYF n F) &&& univYF n F = zcy n H (univYF n F) := by
 apply Nat.eq_of_testBit_eq
 intro s
 rw [Nat.testBit_and, zcG (fun _ => zcE)]
 cases (univYF n F).testBit s <;> simp
theorem zcQ {n v M : ℕ} (hM : ∀ s, M.testBit s = true → s < 2 ^ n) :
  ttVarYF n v M &&& M = ttVarYF n v M := by
 apply Nat.eq_of_testBit_eq
 intro s
 rw [Nat.testBit_and, zcF hM]
 cases M.testBit s <;> simp
theorem zcR {n a M : ℕ} (hM : ∀ s, M.testBit s = true → s < 2 ^ n) :
  zcA n a M &&& M = zcA n a M := by
 apply Nat.eq_of_testBit_eq
 intro s
 rw [Nat.testBit_and, zcH hM]
 cases M.testBit s <;> simp
abbrev Dom (maskYF : ℕ) := { s : ℕ // maskYF.testBit s = true }
def decM (maskYF : ℕ) (g : ℕ) : Set (Dom maskYF) :=
 {s | g.testBit s.1 = true }
@[local simp] theorem mem_decM (maskYF g : ℕ) (s : Dom maskYF) :
  s ∈ decM maskYF g ↔ g.testBit s.1 = true := Iff.rfl
def rawSet (n : ℕ) (F : List (ℕ × ℕ)) : Set (Set (Dom (univYF n F))) :=
 Set.range (fun v : Fin n => decM (univYF n F) (ttVarYF n v.1 (univYF n F)))
def zcS (n : ℕ) (H F : List (ℕ × ℕ)) : Set (Dom (univYF n F)) :=
 decM (univYF n F) (zcy n H (univYF n F))
def zcT (n : ℕ) (H F : List (ℕ × ℕ)) (k : ℕ) : Prop :=
 Run (rawSet n F) k (zcS n H F)
def zcU (n : ℕ) (H F : List (ℕ × ℕ)) (lb : ℕ) : Prop :=
 ∀ k, zcT n H F k → lb ≤ k
theorem zcV (M : ℕ) : decM M 0 = ∅ := by
 ext s; simp [decM]
theorem zcW (M : ℕ) : decM M M = Set.univ := by
 ext ⟨s, hs⟩; simp [decM, hs]
theorem zcX (M a b : ℕ) : decM M (a &&& b) = decM M a ∩ decM M b := by
 ext s; simp [decM, Nat.testBit_and]
theorem decM_or (M a b : ℕ) : decM M (a ||| b) = decM M a ∪ decM M b := by
 ext s; simp [decM, Nat.testBit_or]
theorem zcY {a M s : ℕ} (h : a &&& M = a) (ha : a.testBit s = true) :
  M.testBit s = true := by
 have := congrArg (fun x => x.testBit s) h
 rw [Nat.testBit_and, ha, Bool.true_and] at this
 exact this
theorem zcZ {M a b : ℕ} (ha : a &&& M = a) :
  decM M a ⊆ decM M b ↔ a &&& b = a := by
 constructor
 ·intro qu
  apply Nat.eq_of_testBit_eq
  intro s
  rw [Nat.testBit_and]
  cases h : a.testBit s
  ·simp
  ·have hm : M.testBit s = true := zcY ha h
   have hb : b.testBit s = true := qu (a := ⟨s, hm⟩) h
   simp [hb]
 ·intro heq ⟨s, _⟩ has
  have := congrArg (fun x => x.testBit s) heq
  rw [Nat.testBit_and, has, Bool.true_and] at this
  exact this
theorem zc0 {M a b : ℕ} (ha : a &&& M = a) (hb : b &&& M = b) :
  decM M a = decM M b ↔ a = b := by
 constructor
 ·intro heq
  apply Nat.eq_of_testBit_eq
  intro s
  cases h1 : a.testBit s
  ·cases h2 : b.testBit s
   ·rfl
   ·have hm : M.testBit s = true := zcY hb h2
    have : (⟨s, hm⟩ : Dom M) ∈ decM M a := by rw [heq]; exact h2
    simp [decM, h1] at this
  ·have hm : M.testBit s = true := zcY ha h1
   have : (⟨s, hm⟩ : Dom M) ∈ decM M b := by rw [← heq]; exact h1
   exact this.symm
 ·intro h; rw [h]
noncomputable def encM (N M : ℕ) (S : Set (Dom M)) : ℕ := by
 classical
 exact zct N (fun s => if h : M.testBit s = true then decide (⟨s, h⟩ ∈ S) else false)
theorem zc1 {N M : ℕ} (S : Set (Dom M)) : encM N M S &&& M = encM N M S := by
 classical
 apply Nat.eq_of_testBit_eq
 intro s
 rw [Nat.testBit_and, encM, zcv]
 by_cases hm : M.testBit s = true
 ·simp [hm]
 ·simp [hm]
theorem zc2 {N M : ℕ} (hM : ∀ s, M.testBit s = true → s < N) (S : Set (Dom M)) :
  decM M (encM N M S) = S := by
 classical
 ext ⟨s, hs⟩
 simp only [decM, encM, zcv, Set.mem_ofPred_eq]
 simp [hM s hs, hs]
theorem zc3 (n : ℕ) (F : List (ℕ × ℕ)) :
  rawSet n F = decM (univYF n F) '' { x | x ∈ rawYF n (univYF n F) } := by
 ext S
 simp only [rawSet, rawYF, Set.mem_range, Set.mem_image, Set.mem_ofPred_eq, List.mem_map,
  List.mem_range]
 constructor
 ·rintro ⟨⟨v, hv⟩, rfl⟩
  exact ⟨ttVarYF n v (univYF n F), ⟨v, hv, rfl⟩, rfl⟩
 ·rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
  exact ⟨⟨v, hv⟩, rfl⟩
def zc4 (g : Gate) : Bool :=
 match g.op with
 | .or => true
 | _ => false
def zc5 (gs : List Gate) : ℕ :=
 (gs.filter zc4).length
def zc6 (w : List Bool) (g : Gate) : List Bool :=
 w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]
noncomputable def zc7 {X : Type} (s : X) (f : Set X) : Bool := by
 classical exact decide (s ∈ f)
theorem zc8 {X : Type} (s : X) (ws : List (Set X)) (j : ℕ) :
  (ws.map (zc7 s)).getD j false = zc7 s (ws.getD j ∅) := by
 classical
 by_cases hj : j < ws.length
 ·simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]
 ·simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_none (Nat.le_of_not_gt hj),
   zc7]
theorem zc9 {X : Type} (gs : List Gate) (out : ℕ) (B : Set (Set X)) (w : List (Set X))
  (f : Set X)
  (wk : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
  (hw : ∀ z ∈ w, Meet B z)
  (val : ∀ s : X, (gs.foldl zc6 (w.map (zc7 s))).getD out false = zc7 s f) :
  ∃ k ≤ zc5 gs, Run B k f := by
 classical
 induction gs generalizing B w with
 | nil =>
  have h : w.getD out ∅ = f := by
   ext s
   have hh := val s
   rw [List.foldl_nil, zc8] at hh
   simpa [zc7] using (Bool.eq_iff_iff.mp hh)
  refine ⟨0, by simp [zc5], Run.done ?_⟩
  rw [← h]
  by_cases j : out < w.length
  ·rw [List.getD_eq_getElem _ _ j]; exact hw _ (List.getElem_mem _)
  ·rw [List.getD_eq_default _ _ (by omega)]; exact Meet.bot
 | cons g gs ih =>
  have ok := wk g (by simp)
  have ht : ∀ a ∈ gs, a.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ a.inputs.length ≤ 2 :=
   fun a h => wk _ (by simp [h])
  have rd (j : ℕ) : Meet B (w.getD j ∅) := by
   by_cases hj : j < w.length
   ·rw [List.getD_eq_getElem _ _ hj]; exact hw _ (List.getElem_mem _)
   ·rw [List.getD_eq_default _ _ (by omega)]; exact Meet.bot
  have handle (z : Set X) (hz : Meet B z ∨ ∃ a b, Meet B a ∧ Meet B b ∧ z = a ∪ b ∧ g.op = .or)
    (w9 : ∀ s, zc6 (w.map (zc7 s)) g = (w ++ [z]).map (zc7 s)) :
    ∃ k ≤ zc5 (g :: gs), Run B k f := by
   have val' s : (gs.foldl zc6 ((w ++ [z]).map (zc7 s))).getD out false = zc7 s f := by
    simpa only [List.foldl_cons, w9] using val s
   rcases hz with free | ⟨a, b, ha, hb, rfl, hop⟩
   ·obtain ⟨k, hk, h⟩ := ih B _ ht (fun u hu => by
     rcases List.mem_append.mp hu with hu | hu
     ·exact hw _ hu
     ·simpa [List.mem_singleton.mp hu] using free) val'
    exact ⟨k, hk.trans (by simp [zc5, List.filter_cons]; split <;> simp), h⟩
   ·obtain ⟨k, hk, h⟩ := ih (insert (a ∪ b) B) _ ht (fun u hu => by
     rcases List.mem_append.mp hu with hu | hu
     ·exact weaken (Set.subset_insert _ _) (hw _ hu)
     ·exact Meet.atom (List.mem_singleton.mp hu ▸ Set.mem_insert _ _)) val'
    refine ⟨k + 1, ?_, Run.add ha hb h⟩
    have go : zc4 g = true := by simp [zc4, hop]
    simpa [zc5, go] using Nat.succ_le_succ hk
  obtain ⟨op, l⟩ := g
  change (op = .and ∨ op = .or) ∧ l.length ≤ 2 at ok
  obtain ⟨opok, qe⟩ := ok
  cases l with
  | nil =>
   rcases opok with rfl | rfl
   ·apply handle Set.univ (Or.inl Meet.top); intro s; simp [zc6, GateOp.eval, zc7]
   ·apply handle ∅ (Or.inl Meet.bot); intro s; simp [zc6, GateOp.eval, zc7]
  | cons i l =>
   cases l with
   | nil =>
    rcases opok with rfl | rfl <;> apply handle (w.getD i ∅) (Or.inl (rd i)) <;>
     intro s <;> simp [zc6, GateOp.eval] <;> cases w[i]? <;> simp [zc7]
   | cons j l =>
    cases l with
    | cons => simp at qe
    | nil =>
     rcases opok with rfl | rfl
     ·apply handle (w.getD i ∅ ∩ w.getD j ∅) (Or.inl ((rd i).inter (rd j)))
      intro s; simp [zc6, GateOp.eval]; cases w[i]? <;> cases w[j]? <;> simp [zc7]
     ·apply handle (w.getD i ∅ ∪ w.getD j ∅) (Or.inr ⟨_, _, rd i, rd j, rfl, rfl⟩)
      intro s; simp [zc6, GateOp.eval]; cases w[i]? <;> cases w[j]? <;> simp [zc7]
theorem zda {n : ℕ} (H : List (ℕ × ℕ)) (C : Circuit) (hc : Monotone2 C)
  (he : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
   ∃ e ∈ H, ∃ (h1 : e.1 < n) (h2 : e.2 < n), x ⟨e.1, h1⟩ = true ∧ x ⟨e.2, h2⟩ = true)
  (hH : ∀ e ∈ H, e.1 < n ∧ e.2 < n) :
  ∃ k ≤ zc5 C.gates, zcT n H [] k := by
 classical
 let M := univYF n []
 let w : List (Set (Dom M)) := List.ofFn (fun v : Fin n => decM M (ttVarYF n v.1 M))
 have hw : ∀ z ∈ w, Meet (rawSet n []) z := by
  intro z hz
  obtain ⟨v, rfl⟩ := List.mem_ofFn.mp hz
  exact Meet.atom ⟨v, rfl⟩
 have zl (s : Dom M) :
   (C.gates.foldl zc6 (w.map (zc7 s))).getD C.output false =
    zc7 s (zcS n H []) := by
  let x : Fin n → Bool := fun v => s.1.testBit v.1
  have hin : w.map (zc7 s) = List.ofFn x := by
   rw [show w = List.ofFn (fun v : Fin n => decM M (ttVarYF n v.1 M)) from rfl, List.map_ofFn]
   apply congrArg List.ofFn
   funext v
   have htb : (ttVarYF n v.1 M).testBit s.1 = s.1.testBit v.1 := by
    rw [zcF (fun _ => zcE), s.2, Bool.true_and]
   simp only [Function.comp_apply, zc7, decM, Set.mem_ofPred_eq, htb, x]
   cases s.1.testBit v.1 <;> rfl
  rw [hin]
  change C.eval (List.ofFn x) = _
  apply Bool.eq_iff_iff.mpr
  have het : (zcy n H M).testBit s.1 = hasEdge H s.1 := by
   rw [zcG (fun _ => zcE), s.2, Bool.true_and]
  change C.eval (List.ofFn x) = true ↔ decide (s ∈ zcS n H []) = true
  rw [decide_eq_true_eq, he x]
  have qo : s ∈ zcS n H [] ↔ ∃ e ∈ H, s.1.testBit e.1 = true ∧ s.1.testBit e.2 = true := by
   change (zcy n H M).testBit s.1 = true ↔ _
   rw [het, zcx]
  rw [qo]
  simp only [x]
  constructor
  ·rintro ⟨e, heH, _, _, h1, h2⟩; exact ⟨e, heH, h1, h2⟩
  ·rintro ⟨e, heH, h1, h2⟩
   obtain ⟨hu, hv⟩ := hH e heH
   exact ⟨e, heH, hu, hv, h1, h2⟩
 exact zc9 C.gates C.output (rawSet n []) w (zcS n H []) hc hw zl
theorem land_eq (a b : ℕ) : Nat.land a b = a &&& b := rfl
theorem lor_eq (a b : ℕ) : Nat.lor a b = a ||| b := rfl
def zdb (target : ℕ) : List ℕ → ℕ → ℕ
 | [], acc => acc
 | b :: bs, acc =>
  match Nat.beq (Nat.land target b) target with
  | true => zdb target bs (Nat.land acc b)
  | false => zdb target bs acc
def isMeet (zF : ℕ) (xK : List ℕ) (target : ℕ) : Bool :=
 match Nat.beq target 0 with
 | true => true
 | false => Nat.beq (zdb target xK zF) target
def zdc (zF qc : ℕ) (xK : List ℕ) (g : ℕ) : Bool :=
 let eg := Nat.land g qc
 let acc := zdb eg xK zF
 Nat.beq (Nat.land acc g) acc
theorem zdd {target : ℕ} (bs : List ℕ) (acc : ℕ) :
  zdb target bs acc &&& acc = zdb target bs acc := by
 induction bs generalizing acc with
 | nil => simp [zdb]
 | cons b bs ih =>
  simp only [zdb]
  cases Nat.beq (Nat.land target b) target
  ·exact ih acc
  ·have h1 := ih (Nat.land acc b)
   apply Nat.eq_of_testBit_eq; intro s
   have h2 := congrArg (fun x => x.testBit s) h1
   simp only [land_eq, Nat.testBit_and] at h2 ⊢
   revert h2
   cases (zdb target bs (acc &&& b)).testBit s <;>
    cases acc.testBit s <;> cases b.testBit s <;> decide
theorem zde {target M : ℕ} (bs : List ℕ) {acc : ℕ} (q4 : acc &&& M = acc) :
  zdb target bs acc &&& M = zdb target bs acc := by
 have qu := zdd (target := target) bs acc
 apply Nat.eq_of_testBit_eq; intro s
 have h1 := congrArg (fun x => x.testBit s) qu
 have h2 := congrArg (fun x => x.testBit s) q4
 simp only [Nat.testBit_and] at h1 h2 ⊢
 revert h1 h2
 cases (zdb target bs acc).testBit s <;>
  cases acc.testBit s <;> cases M.testBit s <;> decide
theorem zdf {target : ℕ} (bs : List ℕ) {acc : ℕ}
  (q4 : target &&& acc = target) :
  target &&& zdb target bs acc = target := by
 induction bs generalizing acc with
 | nil => exact q4
 | cons b bs ih =>
  simp only [zdb]
  cases hb : Nat.beq (Nat.land target b) target
  ·exact ih q4
  ·apply ih
   have hb' : target &&& b = target := by simpa [land_eq] using Nat.eq_of_beq_eq_true hb
   rw [land_eq, ← Nat.and_assoc, q4, hb']
theorem zdg {M target : ℕ} {B : Set (Set (Dom M))} (bs : List ℕ)
  (hbs : ∀ b ∈ bs, decM M b ∈ B) {acc : ℕ} (q4 : Meet B (decM M acc)) :
  Meet B (decM M (zdb target bs acc)) := by
 induction bs generalizing acc with
 | nil => exact q4
 | cons b bs ih =>
  simp only [zdb]
  cases Nat.beq (Nat.land target b) target
  ·exact ih (fun x hx => hbs x (by simp [hx])) q4
  ·apply ih (fun x hx => hbs x (by simp [hx]))
   rw [land_eq, zcX]
   exact q4.inter (Meet.atom (hbs b (by simp)))
theorem zdh {M target : ℕ} (bs : List ℕ) {b : ℕ} (hb : b ∈ bs)
  (htb : target &&& b = target) (acc : ℕ) :
  decM M (zdb target bs acc) ⊆ decM M b := by
 induction bs generalizing acc with
 | nil => simp at hb
 | cons x bs ih =>
  simp only [zdb]
  rcases List.mem_cons.mp hb with rfl | hb'
  ·have th : Nat.beq (Nat.land target b) target = true := by
    simpa [land_eq] using htb
   rw [th]
   have qu := zdd (target := target) bs (Nat.land acc b)
   intro s hs
   have h1 := congrArg (fun z => z.testBit s.1) qu
   simp only [land_eq, Nat.testBit_and] at h1
   change (zdb target bs (acc &&& b)).testBit s.1 = true at hs
   rw [hs, Bool.true_and] at h1
   have h2 : acc.testBit s.1 = true ∧ b.testBit s.1 = true := by
    simpa [Bool.and_eq_true] using h1.symm
   exact h2.2
  ·cases Nat.beq (Nat.land target x) target
   ·exact ih hb' acc
   ·exact ih hb' (Nat.land acc x)
theorem zdi {M : ℕ} {B : List ℕ} {t : ℕ} (ht : t &&& M = t) :
  isMeet M B t = true ↔ Meet (decM M '' { b | b ∈ B }) (decM M t) := by
 unfold isMeet
 cases h0 : Nat.beq t 0
 ·have ht0 : t ≠ 0 := by intro h; subst h; simp at h0
  constructor
  ·intro h
   have heq : zdb t B M = t := Nat.eq_of_beq_eq_true h
   rw [← heq]
   apply zdg (B := decM M '' { b | b ∈ B }) B (fun b hb => ⟨b, hb, rfl⟩)
   rw [zcW]; exact Meet.top
  ·intro hm
   have vG : ∀ S, Meet (decM M '' { b | b ∈ B }) S → decM M t ⊆ S →
     decM M (zdb t B M) ⊆ S := by
    intro S hS
    induction hS with
    | atom qo =>
     rcases qo with ⟨b, hb, rfl⟩
     intro htb
     exact zdh B hb ((zcZ ht).mp htb) M
    | top => intro _; exact Set.subset_univ _
    | bot =>
     intro hte
     have : decM M t = decM M 0 := by
      rw [zcV]; exact Set.subset_empty_iff.mp hte
     exact (ht0 ((zc0 ht (by simp)).mp this)).elim
    | inter _ _ ih1 ih2 =>
     intro qu
     exact Set.subset_inter (ih1 (qu.trans Set.inter_subset_left))
      (ih2 (qu.trans Set.inter_subset_right))
   have h1 : decM M (zdb t B M) ⊆ decM M t := vG _ hm Set.Subset.rfl
   have h2 : decM M t ⊆ decM M (zdb t B M) :=
    (zcZ ht).mpr (zdf B ht)
   have heq : zdb t B M = t :=
    (zc0 (zde B (by simp)) ht).mp (Set.Subset.antisymm h1 h2)
   simp [heq]
 ·have ht0 : t = 0 := Nat.eq_of_beq_eq_true h0
  subst ht0
  simp [zcV, Meet.bot]
theorem zdj {M edgePts g : ℕ} {B : List ℕ}
  (hg : g &&& M = g)
  (hon : zdc M edgePts B g = true) :
  ∃ h : ℕ, h &&& M = h ∧ Meet (decM M '' { b | b ∈ B }) (decM M h) ∧
   decM M h ⊆ decM M g ∧ decM M h ∩ decM M edgePts = decM M g ∩ decM M edgePts := by
 unfold zdc at hon
 set eg := Nat.land g edgePts
 set h := zdb eg B M
 have hhM : h &&& M = h := zde B (by simp)
 have hhg : h &&& g = h := by simpa [land_eq] using Nat.eq_of_beq_eq_true hon
 have up : eg &&& M = eg := by
  apply Nat.eq_of_testBit_eq; intro s
  have h1 := congrArg (fun x => x.testBit s) hg
  simp only [eg, land_eq, Nat.testBit_and] at h1 ⊢
  revert h1
  cases g.testBit s <;> cases edgePts.testBit s <;> cases M.testBit s <;> decide
 have tk : eg &&& h = eg := zdf B up
 refine ⟨h, hhM, ?_, (zcZ hhM).mpr hhg, ?_⟩
 ·apply zdg (B := decM M '' { b | b ∈ B }) B (fun b hb => ⟨b, hb, rfl⟩)
  rw [zcW]; exact Meet.top
 ·have yE : decM M h ⊆ decM M g := (zcZ hhM).mpr hhg
  have yF : decM M g ∩ decM M edgePts ⊆ decM M h := by
   rw [← zcX]
   exact (zcZ up).mpr tk
  exact Set.Subset.antisymm (Set.inter_subset_inter_left _ yE)
   (Set.subset_inter yF Set.inter_subset_right)
def MeetNat (M : ℕ) (B : List ℕ) (t : ℕ) : Prop :=
 t &&& M = t ∧ isMeet M B t = true
def zdk (M : ℕ) (B : List ℕ) : List ℕ → Prop
 | [] => True
 | g :: qa =>
  (∃ a b, MeetNat M B a ∧ MeetNat M B b ∧ g = a ||| b) ∧
  zdk M (B ++ [g]) qa
def zdl (M : ℕ) (B : List ℕ) (target : ℕ) : List ℕ → Prop
 | [] => MeetNat M B target
 | g :: qa =>
  (∃ a b, MeetNat M B a ∧ MeetNat M B b ∧ g = a ||| b) ∧
  zdl M (B ++ [g]) target qa
theorem zdm {M : ℕ} {B : List ℕ} {t : ℕ} :
  MeetNat M B t ↔ t &&& M = t ∧ Meet (decM M '' { b | b ∈ B }) (decM M t) := by
 constructor
 ·rintro ⟨ht, hm⟩; exact ⟨ht, (zdi ht).mp hm⟩
 ·rintro ⟨ht, hm⟩; exact ⟨ht, (zdi ht).mpr hm⟩
theorem zdn {M : ℕ} {B₁ B₂ : List ℕ} (qu : ∀ x ∈ B₁, x ∈ B₂) {t : ℕ}
  (ht : MeetNat M B₁ t) : MeetNat M B₂ t := by
 rw [zdm] at ht ⊢
 exact ⟨ht.1, weaken (Set.image_mono (fun x hx => qu x hx)) ht.2⟩
theorem zdo {a b M : ℕ} (ha : a &&& M = a) (hb : b &&& M = b) :
  (a ||| b) &&& M = a ||| b := by
 apply Nat.eq_of_testBit_eq; intro s
 have h1 := congrArg (fun x => x.testBit s) ha
 have h2 := congrArg (fun x => x.testBit s) hb
 simp only [Nat.testBit_and, Nat.testBit_or] at h1 h2 ⊢
 revert h1 h2
 cases a.testBit s <;> cases b.testBit s <;> cases M.testBit s <;> decide
theorem zdp {M target : ℕ} {B gs : List ℕ}
  (hr : zdl M B target gs) :
  Run (decM M '' { x | x ∈ B }) gs.length (decM M target) := by
 induction gs generalizing B with
 | nil =>
  exact Run.done (zdm.mp hr).2
 | cons g qa ih =>
  rcases hr with ⟨⟨a, b, ha, hb, rfl⟩, qY⟩
  have ih' := ih qY
  have vB : decM M '' { x | x ∈ B ++ [a ||| b] } =
    insert (decM M a ∪ decM M b) (decM M '' { x | x ∈ B }) := by
   ext S
   simp only [Set.mem_image, Set.mem_ofPred_eq, List.mem_append, List.mem_singleton,
    Set.mem_insert_iff]
   constructor
   ·rintro ⟨x, hx | rfl, rfl⟩
    ·exact Or.inr ⟨x, hx, rfl⟩
    ·exact Or.inl (decM_or M a b)
   ·rintro (rfl | ⟨x, hx, rfl⟩)
    ·exact ⟨a ||| b, Or.inr rfl, decM_or M a b⟩
    ·exact ⟨x, Or.inl hx, rfl⟩
  rw [vB] at ih'
  exact Run.add (zdm.mp ha).2 (zdm.mp hb).2 ih'
theorem zdq {N M target : ℕ} (hM : ∀ s, M.testBit s = true → s < N)
  (ht : target &&& M = target) {B : List ℕ} {k : ℕ}
  (hr : Run (decM M '' { x | x ∈ B }) k (decM M target)) :
  ∃ gs : List ℕ, gs.length = k ∧ zdl M B target gs := by
 induction k generalizing B with
 | zero =>
  cases hr with
  | done hm => exact ⟨[], rfl, zdm.mpr ⟨ht, hm⟩⟩
 | succ k ih =>
  cases hr with
  | @add _ a b _ _ ha hb qb =>
   let ea := encM N M a
   let eb := encM N M b
   have hea : ea &&& M = ea := zc1 a
   have heb : eb &&& M = eb := zc1 b
   have hda : decM M ea = a := zc2 hM a
   have hdb : decM M eb = b := zc2 hM b
   have vB : decM M '' { x | x ∈ B ++ [ea ||| eb] } =
     insert (a ∪ b) (decM M '' { x | x ∈ B }) := by
    ext S
    simp only [Set.mem_image, Set.mem_ofPred_eq, List.mem_append, List.mem_singleton,
     Set.mem_insert_iff]
    constructor
    ·rintro ⟨x, hx | rfl, rfl⟩
     ·exact Or.inr ⟨x, hx, rfl⟩
     ·exact Or.inl (by rw [decM_or, hda, hdb])
    ·rintro (rfl | ⟨x, hx, rfl⟩)
     ·exact ⟨ea ||| eb, Or.inr rfl, by rw [decM_or, hda, hdb]⟩
     ·exact ⟨x, Or.inl hx, rfl⟩
   rw [← vB] at qb
   obtain ⟨qa, qe, qj⟩ := ih qb
   refine ⟨(ea ||| eb) :: qa, by simp [qe], ?_, qj⟩
   exact ⟨ea, eb, zdm.mpr ⟨hea, hda.symm ▸ ha⟩,
    zdm.mpr ⟨heb, hdb.symm ▸ hb⟩, rfl⟩
theorem zdr {M target : ℕ} {B pre suf : List ℕ} :
  zdl M B target (pre ++ suf) ↔
   zdk M B pre ∧ zdl M (B ++ pre) target suf := by
 induction pre generalizing B with
 | nil => simp [zdk]
 | cons g qa ih =>
  simp only [List.cons_append, zdl, zdk]
  rw [ih, List.append_assoc, List.singleton_append]
  tauto
theorem zds {M target : ℕ} {B₁ B₂ gs : List ℕ}
  (heq : ∀ x, x ∈ B₁ ↔ x ∈ B₂) :
  zdl M B₁ target gs → zdl M B₂ target gs := by
 induction gs generalizing B₁ B₂ with
 | nil => exact zdn (fun x hx => (heq x).mp hx)
 | cons g qa ih =>
  rintro ⟨⟨a, b, ha, hb, rfl⟩, qY⟩
  refine ⟨⟨a, b, zdn (fun x hx => (heq x).mp hx) ha,
   zdn (fun x hx => (heq x).mp hx) hb, rfl⟩, ?_⟩
  exact ih (fun x => by simp [heq x]) qY
theorem zdt {M target : ℕ} {B pre : List ℕ} (hp : zdk M B pre)
  {k : ℕ} (hr : Run (decM M '' { x | x ∈ B ++ pre }) k (decM M target)) :
  Run (decM M '' { x | x ∈ B }) (pre.length + k) (decM M target) := by
 induction pre generalizing B with
 | nil => simpa using hr
 | cons g qa ih =>
  rcases hp with ⟨⟨a, b, ha, hb, rfl⟩, qY⟩
  have hr' : Run (decM M '' { x | x ∈ (B ++ [a ||| b]) ++ qa }) k (decM M target) := by
   simpa only [List.append_assoc, List.singleton_append] using hr
  have hr1 := ih qY hr'
  have vB : decM M '' { x | x ∈ B ++ [a ||| b] } =
    insert (decM M a ∪ decM M b) (decM M '' { x | x ∈ B }) := by
   ext S
   simp only [Set.mem_image, Set.mem_ofPred_eq, List.mem_append, List.mem_singleton,
    Set.mem_insert_iff]
   constructor
   ·rintro ⟨x, hx | rfl, rfl⟩
    ·exact Or.inr ⟨x, hx, rfl⟩
    ·exact Or.inl (decM_or M a b)
   ·rintro (rfl | ⟨x, hx, rfl⟩)
    ·exact ⟨a ||| b, Or.inr rfl, decM_or M a b⟩
    ·exact ⟨x, Or.inl hx, rfl⟩
  rw [vB] at hr1
  rw [List.length_cons, Nat.succ_add]
  exact Run.add (zdm.mp ha).2 (zdm.mp hb).2 hr1
theorem zdu {P : List ℕ → Prop} :
  ∀ k, (∃ gs, gs.length = k ∧ P gs) →
   ∃ gs, gs.length = k ∧ P gs ∧
    ∀ gs', gs'.length = k → P gs' → ¬ List.Lex (·< ·) gs' gs := by
 classical
 intro k
 induction k generalizing P with
 | zero =>
  rintro ⟨gs, qe, hp⟩
  cases gs with
  | nil =>
   refine ⟨[], rfl, hp, fun gs' q9 _ qG => ?_⟩
   cases gs' with
   | nil => cases qG
   | cons => simp at q9
  | cons => simp at qe
 | succ k ih =>
  intro hex
  have hQ : ∃ x : ℕ, ∃ qb : List ℕ, qb.length = k ∧ P (x :: qb) := by
   rcases hex with ⟨gs, qe, hp⟩
   cases gs with
   | nil => simp at qe
   | cons x qb => exact ⟨x, qb, by simpa using qe, hp⟩
  let x₀ := Nat.find hQ
  have hx₀ : ∃ qb : List ℕ, qb.length = k ∧ P (x₀ :: qb) := Nat.find_spec hQ
  obtain ⟨qb₀, qe₀, hp₀, qz₀⟩ := ih (P := fun t => P (x₀ :: t)) hx₀
  refine ⟨x₀ :: qb₀, by simp [qe₀], hp₀, fun gs' q9 hp' qG => ?_⟩
  cases gs' with
  | nil => simp at q9
  | cons x' tail' =>
   cases qG with
   | rel hlt =>
    exact Nat.find_min hQ hlt ⟨tail', by simpa using q9, hp'⟩
   | cons xQ =>
    exact qz₀ tail' (by simpa using q9) hp' xQ
theorem zdv {n bound : ℕ} {H F : List (ℕ × ℕ)}
  (hex : ∃ k ≤ bound, zcT n H F k) :
  ∃ (k : ℕ) (gs : List ℕ), k ≤ bound ∧ gs.length = k ∧
   zdl (univYF n F) (rawYF n (univYF n F)) (zcy n H (univYF n F)) gs ∧
   (∀ k' < k, ¬ zcT n H F k') ∧
   (∀ gs', gs'.length = k →
    zdl (univYF n F) (rawYF n (univYF n F)) (zcy n H (univYF n F)) gs' →
    ¬ List.Lex (·< ·) gs' gs) := by
 classical
 have hEx : ∃ k, zcT n H F k := by rcases hex with ⟨k, _, h⟩; exact ⟨k, h⟩
 let k := Nat.find hEx
 have uw : k ≤ bound := by
  rcases hex with ⟨k', hk', hr'⟩
  exact (Nat.find_min' hEx hr').trans hk'
 have wQ : zcT n H F k := Nat.find_spec hEx
 have wP : ∀ k' < k, ¬ zcT n H F k' := fun k' hk' => Nat.find_min hEx hk'
 have v2 : ∃ gs : List ℕ, gs.length = k ∧
   zdl (univYF n F) (rawYF n (univYF n F)) (zcy n H (univYF n F)) gs := by
  apply zdq (N := 2 ^ n) (fun _ => zcE) (zcP n H F)
  simpa only [zcT, zc3, zcS] using wQ
 obtain ⟨gs, qe, qj, qG⟩ := zdu k v2
 exact ⟨k, gs, uw, qe, qj, wP, qG⟩
def bitLe {M : ℕ} (x y : Dom M) : Prop := x.1 &&& y.1 = x.1
theorem zdw {n : ℕ} {F : List (ℕ × ℕ)} {r : ℕ}
  (hr : r ∈ rawYF n (univYF n F)) :
  zcn (bitLe (M := univYF n F)) (decM (univYF n F) r) := by
 simp only [rawYF, List.mem_map, List.mem_range] at hr
 rcases hr with ⟨v, _, rfl⟩
 intro x y hxy hx
 simp only [decM, Set.mem_ofPred_eq, zcF (fun _ => zcE),
  x.2, y.2, Bool.true_and] at hx ⊢
 have := congrArg (fun z => z.testBit v) hxy
 rw [Nat.testBit_and, hx, Bool.true_and] at this
 exact this
theorem zdx {M : ℕ} {B pre : List ℕ}
  (hB : ∀ r ∈ B, zcn (bitLe (M := M)) (decM M r))
  (hp : zdk M B pre) :
  ∀ x ∈ B ++ pre, zcn (bitLe (M := M)) (decM M x) := by
 induction pre generalizing B with
 | nil => simpa using hB
 | cons g qa ih =>
  rcases hp with ⟨⟨a, b, ha, hb, rfl⟩, qY⟩
  have hB' : ∀ r ∈ B ++ [a ||| b], zcn (bitLe (M := M)) (decM M r) := by
   intro r hr
   rcases List.mem_append.mp hr with hr | hr
   ·exact hB r hr
   ·rw [List.mem_singleton.mp hr, decM_or]
    have ha' : zcn (bitLe (M := M)) (decM M a) :=
     zco (B := decM M '' { x | x ∈ B })
      (fun S hS => by rcases hS with ⟨x, hx, rfl⟩; exact hB x hx) (zdm.mp ha).2
    have hb' : zcn (bitLe (M := M)) (decM M b) :=
     zco (B := decM M '' { x | x ∈ B })
      (fun S hS => by rcases hS with ⟨x, hx, rfl⟩; exact hB x hx) (zdm.mp hb).2
    intro x y hxy qo
    rcases qo with h1 | h2
    ·exact Or.inl (ha' x y hxy h1)
    ·exact Or.inr (hb' x y hxy h2)
  simpa [List.append_assoc] using ih hB' qY
theorem zdy {n : ℕ} {H F : List (ℕ × ℕ)} (hv : zcC n H F) :
  (decM (univYF n F) (zcz H) ⊆ zcS n H F) ∧
  (∀ f : Set (Dom (univYF n F)), zcn (bitLe (M := univYF n F)) f →
   decM (univYF n F) (zcz H) ⊆ f → zcS n H F ⊆ f) := by
 constructor
 ·intro s hs
  simp only [decM, Set.mem_ofPred_eq, zcJ, List.any_eq_true] at hs
  rcases hs with ⟨e, heH, heq⟩
  rw [decide_eq_true_eq] at heq
  change (zcy n H (univYF n F)).testBit s.1 = true
  rw [← heq]; exact zcO hv heH
 ·intro f hf qu s hs
  simp only [zcS, decM, Set.mem_ofPred_eq,
   zcG (fun _ => zcE), s.2, Bool.true_and, zcx] at hs
  rcases hs with ⟨e, heH, h1, h2⟩
  let ep : ℕ := (1 <<< e.1) ||| (1 <<< e.2)
  have wH : (univYF n F).testBit ep = true := zcN hv heH
  have wI : (⟨ep, wH⟩ : Dom (univYF n F)) ∈ decM (univYF n F) (zcz H) := by
   simp only [decM, Set.mem_ofPred_eq, zcJ, List.any_eq_true]
   exact ⟨e, heH, decide_eq_true rfl⟩
  have hle : bitLe (⟨ep, wH⟩ : Dom (univYF n F)) s := by
   apply Nat.eq_of_testBit_eq; intro w
   rw [Nat.testBit_and]
   by_cases hw : ep.testBit w = true
   ·rw [hw, Bool.true_and]
    rcases (zcM e.1 e.2 w).mp hw with rfl | rfl
    ·exact h1
    ·exact h2
   ·have hwf : ep.testBit w = false := Bool.eq_false_iff.mpr hw
    simp [hwf]
  exact hf ⟨ep, wH⟩ s hle (qu wI)
theorem zdz {n : ℕ} {H F : List (ℕ × ℕ)} {pre suf : List ℕ}
  (qj : zdl (univYF n F) (rawYF n (univYF n F)) (zcy n H (univYF n F)) (pre ++ suf))
  (qz : ∀ k' < (pre ++ suf).length, ¬ zcT n H F k')
  (yv : suf ≠ []) :
  isMeet (univYF n F) (rawYF n (univYF n F) ++ pre) (zcy n H (univYF n F)) = false := by
 rw [Bool.eq_false_iff]
 intro hm
 have hp : zdk (univYF n F) (rawYF n (univYF n F)) pre := (zdr.mp qj).1
 have hr : zdl (univYF n F) (rawYF n (univYF n F)) (zcy n H (univYF n F)) pre := by
  have h := zdr (M := univYF n F) (target := zcy n H (univYF n F))
   (B := rawYF n (univYF n F)) (pre := pre) (suf := [])
  rw [List.append_nil] at h
  exact h.mpr ⟨hp, zcP n H F, hm⟩
 have hr' := zdp hr
 rw [← zc3] at hr'
 have hlt : pre.length < (pre ++ suf).length := by
  cases suf with
  | nil => exact (yv rfl).elim
  | cons _ _ => simp
 exact qz pre.length hlt hr'
theorem zdA {n : ℕ} {H F : List (ℕ × ℕ)} {pre suf : List ℕ} {g h : ℕ}
  (hv : zcC n H F)
  (qj : zdl (univYF n F) (rawYF n (univYF n F)) (zcy n H (univYF n F)) (pre ++ g :: suf))
  (qz : ∀ k' < (pre ++ g :: suf).length, ¬ zcT n H F k')
  (hmh : Meet (decM (univYF n F) '' { x | x ∈ rawYF n (univYF n F) ++ pre }) (decM (univYF n F) h))
  (qu : decM (univYF n F) h ⊆ decM (univYF n F) g)
  (heq : decM (univYF n F) h ∩ decM (univYF n F) (zcz H) =
   decM (univYF n F) g ∩ decM (univYF n F) (zcz H)) : False := by
 set M := univYF n F
 set raw := rawYF n M
 set target := zcy n H M
 obtain ⟨hp, qQ⟩ := zdr.mp qj
 rcases qQ with ⟨_, yv⟩
 have xl : Run (decM M '' { x | x ∈ (raw ++ pre) ++ [g] }) suf.length (zcS n H F) :=
  zdp yv
 have ud : ∀ S ∈ decM M '' { x | x ∈ raw ++ pre }, zcn (bitLe (M := M)) S := by
  rintro S ⟨x, hx, rfl⟩
  exact zdx (fun r hr => zdw hr) hp x hx
 have q0 : ∀ S ∈ decM M '' { x | x ∈ (raw ++ pre) ++ [g] },
   ∃ S', Meet (decM M '' { x | x ∈ raw ++ pre }) S' ∧ S' ⊆ S ∧
    S' ∩ decM M (zcz H) = S ∩ decM M (zcz H) := by
  rintro S ⟨x, hx, rfl⟩
  rcases List.mem_append.mp hx with hx | hx
  ·exact ⟨decM M x, Meet.atom ⟨x, hx, rfl⟩, Set.Subset.rfl, rfl⟩
  ·rw [List.mem_singleton.mp hx]
   exact ⟨decM M h, hmh, qu, heq⟩
 obtain ⟨hSt, yd⟩ := zdy hv
 have yp : Run (decM M '' { x | x ∈ raw ++ pre }) suf.length (zcS n H F) :=
  zcs hSt yd ud q0 xl
 have yW : zcT n H F (pre.length + suf.length) := by
  have := zdt hp yp
  rw [← zc3] at this
  exact this
 have hlt : pre.length + suf.length < (pre ++ g :: suf).length := by simp
 exact qz _ hlt yW
theorem zdB {n : ℕ} {H F : List (ℕ × ℕ)} {pre suf : List ℕ} {g : ℕ}
  (hv : zcC n H F)
  (qj : zdl (univYF n F) (rawYF n (univYF n F)) (zcy n H (univYF n F)) (pre ++ g :: suf))
  (qz : ∀ k' < (pre ++ g :: suf).length, ¬ zcT n H F k') :
  zdc (univYF n F) (zcz H) (rawYF n (univYF n F) ++ pre) g = false := by
 rw [Bool.eq_false_iff]
 intro hon
 have hgM : g &&& univYF n F = g := by
  obtain ⟨_, ⟨a, b, ha, hb, rfl⟩, _⟩ := zdr.mp qj
  exact zdo ha.1 hb.1
 obtain ⟨h, _, hmh, qu, heq⟩ := zdj hgM hon
 exact zdA hv qj qz hmh qu heq
theorem zdC {n M : ℕ} (hM : ∀ s, M.testBit s = true → s < 2 ^ n) :
  zcA n 0 M = M := by
 apply Nat.eq_of_testBit_eq; intro s
 rw [zcH hM]; simp
theorem zdD {n v M : ℕ} (hM : ∀ s, M.testBit s = true → s < 2 ^ n) :
  zcA n (1 <<< v) M = ttVarYF n v M := by
 apply Nat.eq_of_testBit_eq; intro s
 rw [zcH hM, zcF hM]
 have zK : ((s &&& (1 <<< v)) == (1 <<< v)) = s.testBit v := by
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq]
  constructor
  ·intro heq
   have := congrArg (fun z => z.testBit v) heq
   rw [Nat.testBit_and, zcu] at this
   simpa using this
  ·intro hs
   apply Nat.eq_of_testBit_eq; intro w
   rw [Nat.testBit_and, zcu]
   by_cases hw : v = w
   ·subst hw; simp [hs]
   ·simp [hw]
 rw [zK]
theorem zdE {n a b M : ℕ} (hM : ∀ s, M.testBit s = true → s < 2 ^ n) :
  zcA n a M &&& zcA n b M = zcA n (a ||| b) M := by
 apply Nat.eq_of_testBit_eq; intro s
 rw [Nat.testBit_and, zcH hM, zcH hM, zcH hM]
 cases hm : M.testBit s
 ·simp
 ·simp only [Bool.true_and]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, beq_iff_eq]
  constructor
  ·rintro ⟨ha, hb⟩
   apply Nat.eq_of_testBit_eq; intro w
   have h1 := congrArg (fun z => z.testBit w) ha
   have h2 := congrArg (fun z => z.testBit w) hb
   simp only [Nat.testBit_and, Nat.testBit_or] at h1 h2 ⊢
   revert h1 h2
   cases s.testBit w <;> cases a.testBit w <;> cases b.testBit w <;> decide
  ·intro hab
   constructor <;> apply Nat.eq_of_testBit_eq <;> intro w <;>
    (have h := congrArg (fun z => z.testBit w) hab
     simp only [Nat.testBit_and, Nat.testBit_or] at h ⊢
     revert h
     cases s.testBit w <;> cases a.testBit w <;> cases b.testBit w <;> decide)
theorem zdF (xs : List ℕ) (a b : ℕ) :
  xs.foldl Nat.land (a &&& b) = a &&& xs.foldl Nat.land b := by
 induction xs generalizing a b with
 | nil => rfl
 | cons x qa ih =>
  simp only [List.foldl_cons, land_eq]
  rw [Nat.and_assoc, ih a (b &&& x)]
theorem zdG (xs ys : List ℕ) (M : ℕ) :
  (xs ++ ys).foldl Nat.land M = xs.foldl Nat.land M &&& ys.foldl Nat.land M := by
 rw [List.foldl_append]
 have h1 : xs.foldl Nat.land M = xs.foldl Nat.land M &&& M := by
  induction xs generalizing M with
  | nil => simp
  | cons x qa ih =>
   simp only [List.foldl_cons, land_eq]
   rw [zdF]
   apply Nat.eq_of_testBit_eq; intro s
   simp only [Nat.testBit_and]
   cases M.testBit s <;> cases (qa.foldl Nat.land x).testBit s <;> simp
 conv_lhs => rw [h1]
 exact zdF ys (xs.foldl Nat.land M) M
theorem zdH {xs ys : List ℕ} {M : ℕ}
  (heq : ∀ x, x ∈ xs ↔ x ∈ ys) :
  xs.foldl Nat.land M = ys.foldl Nat.land M := by
 have zK : ∀ (zs : List ℕ) (acc s : ℕ),
   (zs.foldl Nat.land acc).testBit s = true ↔
    acc.testBit s = true ∧ ∀ z ∈ zs, z.testBit s = true := by
  intro zs
  induction zs with
  | nil => intro acc s; simp
  | cons z qa ih =>
   intro acc s
   simp only [List.foldl_cons, land_eq, ih, Nat.testBit_and, Bool.and_eq_true, List.mem_cons]
   constructor
   ·rintro ⟨⟨ha, hz⟩, qY⟩
    exact ⟨ha, fun w hw => hw.elim (fun e => e ▸ hz) (qY w)⟩
   ·rintro ⟨ha, hall⟩
    exact ⟨⟨ha, hall z (Or.inl rfl)⟩, fun w hw => hall w (Or.inr hw)⟩
 apply Nat.eq_of_testBit_eq; intro s
 apply Bool.eq_iff_iff.mpr
 rw [zK xs M s, zK ys M s]
 constructor
 ·rintro ⟨hM, h⟩; exact ⟨hM, fun z hz => h z ((heq z).mpr hz)⟩
 ·rintro ⟨hM, h⟩; exact ⟨hM, fun z hz => h z ((heq z).mp hz)⟩
theorem zdI {n : ℕ} {F : List (ℕ × ℕ)} {pre : List ℕ}
  {S : Set (Dom (univYF n F))}
  (hm : Meet (decM (univYF n F) '' { x | x ∈ rawYF n (univYF n F) ++ pre }) S) :
  S = ∅ ∨ ∃ (qW : ℕ) (P : List ℕ), (∀ p ∈ P, p ∈ pre) ∧
   S = decM (univYF n F) (zcA n qW (univYF n F) &&& P.foldl Nat.land (univYF n F)) := by
 have hM : ∀ s, (univYF n F).testBit s = true → s < 2 ^ n := fun _ => zcE
 induction hm with
 | atom hx =>
  rcases hx with ⟨y, hy, rfl⟩
  rcases List.mem_append.mp hy with hy | hy
  ·simp only [rawYF, List.mem_map, List.mem_range] at hy
   rcases hy with ⟨v, _, rfl⟩
   refine Or.inr ⟨1 <<< v, [], fun _ h => by simp at h, ?_⟩
   simp only [List.foldl_nil, zdD hM, zcQ hM]
  ·refine Or.inr ⟨0, [y], fun p hp => (List.mem_singleton.mp hp) ▸ hy, ?_⟩
   simp only [List.foldl_cons, List.foldl_nil, land_eq, zdC hM]
   rw [zcX, zcX, zcW, Set.univ_inter, Set.univ_inter]
 | top =>
  refine Or.inr ⟨0, [], fun _ h => by simp at h, ?_⟩
  simp only [List.foldl_nil, zdC hM, Nat.and_self, zcW]
 | bot => exact Or.inl rfl
 | inter _ _ ih1 ih2 =>
  rcases ih1 with rfl | ⟨r1, P1, hP1, rfl⟩
  ·exact Or.inl (Set.empty_inter _)
  rcases ih2 with rfl | ⟨r2, P2, hP2, rfl⟩
  ·exact Or.inl (Set.inter_empty _)
  refine Or.inr ⟨r1 ||| r2, P1 ++ P2, fun p hp => (List.mem_append.mp hp).elim (hP1 p) (hP2 p), ?_⟩
  rw [← zcX, ← zdE hM, zdG]
  congr 1
  apply Nat.eq_of_testBit_eq; intro s
  simp only [Nat.testBit_and]
  cases (zcA n r1 (univYF n F)).testBit s <;> cases (zcA n r2 (univYF n F)).testBit s <;>
   cases (P1.foldl Nat.land (univYF n F)).testBit s <;>
   cases (P2.foldl Nat.land (univYF n F)).testBit s <;> simp
theorem zdJ {n : ℕ} {H F : List (ℕ × ℕ)} {pre : List ℕ} {x : ℕ}
  (hv : zcC n H F)
  (hx : MeetNat (univYF n F) (rawYF n (univYF n F) ++ pre) x)
  (hne : x &&& zcz H ≠ 0) :
  ∃ mt ∈ zcB n H (univYF n F), ∃ P : List ℕ, List.Sublist P pre ∧
   x = mt &&& P.foldl Nat.land (univYF n F) := by
 set M := univYF n F
 have hM : ∀ s, M.testBit s = true → s < 2 ^ n := fun _ => zcE
 rcases zdI (zdm.mp hx).2 with z3 | ⟨qW, P, hP, hS⟩
 ·exfalso
  have hx0 : x = 0 := (zc0 hx.1 (by simp)).mp (by rw [z3, zcV])
  simp [hx0] at hne
 have uU : x = zcA n qW M &&& P.foldl Nat.land M := by
  apply (zc0 hx.1 ?_).mp hS
  apply Nat.eq_of_testBit_eq; intro s
  have ht := congrArg (fun z => z.testBit s) (zcR (n := n) (a := qW) hM)
  simp only [Nat.testBit_and] at ht ⊢
  revert ht
  cases (zcA n qW M).testBit s <;> cases (P.foldl Nat.land M).testBit s <;>
   cases M.testBit s <;> decide
 have wL : ∃ s, (x &&& zcz H).testBit s = true := by
  by_contra hall
  push Not at hall
  apply hne
  apply Nat.eq_of_testBit_eq; intro s
  simp only [Nat.zero_testBit]
  exact Bool.eq_false_iff.mpr (hall s)
 obtain ⟨s, hs⟩ := wL
 rw [Nat.testBit_and, Bool.and_eq_true, zcJ, List.any_eq_true] at hs
 obtain ⟨hxs, e, heH, hes⟩ := hs
 rw [decide_eq_true_eq] at hes
 have wf : (zcA n qW M).testBit s = true := by
  rw [uU, Nat.testBit_and, Bool.and_eq_true] at hxs; exact hxs.1
 rw [zcH hM, Bool.and_eq_true, beq_iff_eq] at wf
 have yC : ∀ w, qW.testBit w = true → w = e.1 ∨ w = e.2 := by
  intro w hw
  have := congrArg (fun z => z.testBit w) wf.2
  rw [Nat.testBit_and, hw, Bool.and_true] at this
  rw [← hes] at this
  exact (zcM e.1 e.2 w).mp this
 obtain ⟨he1, he2, _⟩ := hv.1 e heH
 have uL : zcA n qW M ∈ zcB n H M := by
  unfold zcB
  apply List.mem_map.mpr
  refine ⟨qW, ?_, rfl⟩
  cases hb1 : qW.testBit e.1 <;> cases hb2 : qW.testBit e.2
  ·have hr0 : qW = 0 := by
    apply Nat.eq_of_testBit_eq; intro w
    cases hw : qW.testBit w
    ·simp
    ·rcases yC w hw with rfl | rfl <;> simp_all
   subst hr0; simp
  ·have hr2 : qW = 1 <<< e.2 := by
    apply Nat.eq_of_testBit_eq; intro w
    rw [zcu]
    by_cases hw : e.2 = w
    ·subst hw; simp [hb2]
    ·simp only [hw, decide_false]
     cases hrw : qW.testBit w
     ·rfl
     ·rcases yC w hrw with rfl | rfl <;> simp_all
   subst hr2
   simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_map, List.mem_range]
   exact Or.inr (Or.inl ⟨e.2, he2, rfl⟩)
  ·have hr1 : qW = 1 <<< e.1 := by
    apply Nat.eq_of_testBit_eq; intro w
    rw [zcu]
    by_cases hw : e.1 = w
    ·subst hw; simp [hb1]
    ·simp only [hw, decide_false]
     cases hrw : qW.testBit w
     ·rfl
     ·rcases yC w hrw with rfl | rfl <;> simp_all
   subst hr1
   simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_map, List.mem_range]
   exact Or.inr (Or.inl ⟨e.1, he1, rfl⟩)
  ·have tz : qW = (1 <<< e.1) ||| (1 <<< e.2) := by
    apply Nat.eq_of_testBit_eq; intro w
    rw [Nat.testBit_or, zcu, zcu]
    by_cases hw1 : e.1 = w
    ·subst hw1; simp [hb1]
    ·by_cases hw2 : e.2 = w
     ·subst hw2; simp [hb2]
     ·simp only [hw1, hw2, decide_false, Bool.or_false]
      cases hrw : qW.testBit w
      ·rfl
      ·rcases yC w hrw with rfl | rfl <;> simp_all
   subst tz
   simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_map]
   exact Or.inr (Or.inr ⟨e, heH, rfl⟩)
 let P' := pre.filter (fun y => P.contains y)
 have qu : List.Sublist P' pre := List.filter_sublist
 have u9 : ∀ y, y ∈ P ↔ y ∈ P' := by
  intro y
  simp only [P', List.mem_filter, List.contains_eq_mem, decide_eq_true_eq]
  exact ⟨fun hy => ⟨hP y hy, hy⟩, fun h => h.2⟩
 refine ⟨zcA n qW M, uL, P', qu, ?_⟩
 rw [uU, zdH u9]
theorem zdK {n : ℕ} {H F : List (ℕ × ℕ)} {pre suf : List ℕ} {g : ℕ}
  (hv : zcC n H F)
  (qj : zdl (univYF n F) (rawYF n (univYF n F)) (zcy n H (univYF n F)) (pre ++ g :: suf))
  (qz : ∀ k' < (pre ++ g :: suf).length, ¬ zcT n H F k') :
  ∃ a b : ℕ, g = a ||| b ∧ a ≠ b ∧
   MeetNat (univYF n F) (rawYF n (univYF n F) ++ pre) a ∧
   MeetNat (univYF n F) (rawYF n (univYF n F) ++ pre) b ∧
   a ≠ 0 ∧ a ≠ univYF n F ∧ a &&& zcz H ≠ 0 ∧
   b ≠ 0 ∧ b ≠ univYF n F ∧ b &&& zcz H ≠ 0 := by
 set M := univYF n F
 set raw := rawYF n M
 set ep := zcz H
 obtain ⟨_, ⟨a, b, ha, hb, hgab⟩, _⟩ := zdr.mp qj
 have v8 : a &&& ep ≠ 0 := by
  intro h0
  have qu : decM M b ⊆ decM M g := by
   rw [hgab, decM_or]; exact Set.subset_union_right
  have heq : decM M b ∩ decM M ep = decM M g ∩ decM M ep := by
   rw [hgab, decM_or, Set.union_inter_distrib_right]
   have tc : decM M a ∩ decM M ep = ∅ := by rw [← zcX, h0, zcV]
   rw [tc, Set.empty_union]
  exact zdA hv qj qz (zdm.mp hb).2 qu heq
 have wa : b &&& ep ≠ 0 := by
  intro h0
  have qu : decM M a ⊆ decM M g := by
   rw [hgab, decM_or]; exact Set.subset_union_left
  have heq : decM M a ∩ decM M ep = decM M g ∩ decM M ep := by
   rw [hgab, decM_or, Set.union_inter_distrib_right]
   have wv : decM M b ∩ decM M ep = ∅ := by rw [← zcX, h0, zcV]
   rw [wv, Set.union_empty]
  exact zdA hv qj qz (zdm.mp ha).2 qu heq
 have ha0 : a ≠ 0 := fun h => v8 (by simp [h])
 have hb0 : b ≠ 0 := fun h => wa (by simp [h])
 have haM : a ≠ M := by
  intro h
  have hgm : g = M := by
   rw [hgab, h]
   apply Nat.eq_of_testBit_eq; intro s
   have h1 := congrArg (fun z => z.testBit s) hb.1
   simp only [Nat.testBit_or, Nat.testBit_and] at h1 ⊢
   revert h1
   cases M.testBit s <;> cases b.testBit s <;> decide
  exact zdA hv qj qz (hgm ▸ zcW M ▸ Meet.top) Set.Subset.rfl rfl
 have hbM : b ≠ M := by
  intro h
  have hgm : g = M := by
   rw [hgab, h]
   apply Nat.eq_of_testBit_eq; intro s
   have h1 := congrArg (fun z => z.testBit s) ha.1
   simp only [Nat.testBit_or, Nat.testBit_and] at h1 ⊢
   revert h1
   cases M.testBit s <;> cases a.testBit s <;> decide
  exact zdA hv qj qz (hgm ▸ zcW M ▸ Meet.top) Set.Subset.rfl rfl
 have hab : a ≠ b := by
  intro h
  have hga : g = a := by rw [hgab, h, Nat.or_self]
  exact zdA hv qj qz (hga ▸ (zdm.mp ha).2) Set.Subset.rfl rfl
 exact ⟨a, b, hgab, hab, ha, hb, ha0, haM, v8, hb0, hbM, wa⟩
theorem zdL {α : Type} {r : α → α → Prop} :
  ∀ (pre l₁ l₂ : List α), List.Lex r l₁ l₂ → List.Lex r (pre ++ l₁) (pre ++ l₂)
 | [], _, _, h => h
 | _ :: qa, l₁, l₂, h => List.Lex.cons (zdL qa l₁ l₂ h)
def zdM (tbl : List ℕ) (f : ℕ) (s : ℕ) (acc : ℕ) : ℕ :=
 match tbl with
 | [] => acc
 | s2 :: qa =>
  let zJ := match f.testBit s with
   | true => Nat.lor acc (1 <<< s2)
   | false => acc
  zdM qa f (s + 1) zJ
def zdN (tbl : List ℕ) (f : ℕ) : ℕ :=
 zdM tbl f 0 0
theorem zdO (tbl : List ℕ) (f s acc y : ℕ) :
  (zdM tbl f s acc).testBit y = true ↔
   acc.testBit y = true ∨
   ∃ (i : ℕ) (hi : i < tbl.length), tbl[i] = y ∧ f.testBit (s + i) = true := by
 induction tbl generalizing s acc with
 | nil => simp [zdM]
 | cons s2 qa ih =>
  simp only [zdM]
  rw [ih]
  have y7 : (match f.testBit s with
    | true => Nat.lor acc (1 <<< s2)
    | false => acc).testBit y = true ↔
    acc.testBit y = true ∨ (f.testBit s = true ∧ s2 = y) := by
   cases hfs : f.testBit s
   ·simp
   ·simp only [lor_eq, Nat.testBit_or, zcu, Bool.or_eq_true,
     decide_eq_true_eq, true_and]
  rw [y7]
  constructor
  ·rintro ((ha | ⟨hfs, rfl⟩) | ⟨i, hi, qR, hfi⟩)
   ·exact Or.inl ha
   ·exact Or.inr ⟨0, by simp, rfl, by simpa using hfs⟩
   ·exact Or.inr ⟨i + 1, by simp [hi], by simpa using qR,
     by rwa [show s + (i + 1) = s + 1 + i by omega]⟩
  ·rintro (ha | ⟨i, hi, qR, hfi⟩)
   ·exact Or.inl (Or.inl ha)
   ·cases i with
    | zero => exact Or.inl (Or.inr ⟨by simpa using hfi, by simpa using qR⟩)
    | succ j =>
     exact Or.inr ⟨j, by simpa using hi, by simpa using qR,
      by rwa [show s + 1 + j = s + (j + 1) by omega]⟩
theorem zdP (tbl : List ℕ) (f y : ℕ) :
  (zdN tbl f).testBit y = true ↔
   ∃ (i : ℕ) (hi : i < tbl.length), tbl[i] = y ∧ f.testBit i = true := by
 simpa [zdN] using zdO tbl f 0 0 y
theorem zdQ (tbl : List ℕ) : zdN tbl 0 = 0 := by
 apply Nat.eq_of_testBit_eq; intro y
 apply Bool.eq_iff_iff.mpr
 simp [zdP]
theorem zdR (tbl : List ℕ) (a b : ℕ) :
  zdN tbl (a ||| b) = zdN tbl a ||| zdN tbl b := by
 apply Nat.eq_of_testBit_eq; intro y
 apply Bool.eq_iff_iff.mpr
 simp only [zdP, Nat.testBit_or, Bool.or_eq_true]
 constructor
 ·rintro ⟨i, hi, qR, ha | hb⟩
  ·exact Or.inl ⟨i, hi, qR, ha⟩
  ·exact Or.inr ⟨i, hi, qR, hb⟩
 ·rintro (⟨i, hi, qR, ha⟩ | ⟨i, hi, qR, hb⟩)
  ·exact ⟨i, hi, qR, Or.inl ha⟩
  ·exact ⟨i, hi, qR, Or.inr hb⟩
theorem zdS {tbl : List ℕ} (hnd : tbl.Nodup) (a b : ℕ) :
  zdN tbl (a &&& b) = zdN tbl a &&& zdN tbl b := by
 apply Nat.eq_of_testBit_eq; intro y
 apply Bool.eq_iff_iff.mpr
 simp only [zdP, Nat.testBit_and, Bool.and_eq_true]
 constructor
 ·rintro ⟨i, hi, qR, ha, hb⟩
  exact ⟨⟨i, hi, qR, ha⟩, ⟨i, hi, qR, hb⟩⟩
 ·rintro ⟨⟨i, hi, hgeti, ha⟩, ⟨j, hj, hgetj, hb⟩⟩
  have hij : i = j := (List.Nodup.getElem_inj_iff hnd).mp (hgeti.trans hgetj.symm)
  subst hij
  exact ⟨i, hi, hgeti, ha, hb⟩
abbrev zdT (M edgeTT : ℕ) (raw tbl : List ℕ) : Prop :=
 tbl.Nodup ∧ zdN tbl M = M ∧ zdN tbl edgeTT = edgeTT ∧
  ∀ r ∈ raw, zdN tbl r ∈ raw
theorem zdU {tbl : List ℕ} (hnd : tbl.Nodup) (M : ℕ)
  {B B' : List ℕ} (hB : ∀ b ∈ B, zdN tbl b ∈ B') {t acc : ℕ}
  (q4 : Meet (decM M '' { x | x ∈ B' }) (decM M (zdN tbl acc))) :
  Meet (decM M '' { x | x ∈ B' }) (decM M (zdN tbl (zdb t B acc))) := by
 induction B generalizing acc with
 | nil => exact q4
 | cons b bs ih =>
  simp only [zdb]
  cases Nat.beq (Nat.land t b) t
  ·exact ih (fun x hx => hB x (by simp [hx])) q4
  ·apply ih (fun x hx => hB x (by simp [hx]))
   rw [land_eq, zdS hnd, zcX]
   exact q4.inter (Meet.atom ⟨zdN tbl b, hB b (by simp), rfl⟩)
theorem zdV {tbl : List ℕ} (hnd : tbl.Nodup) {M : ℕ} (hM : zdN tbl M = M)
  {B B' : List ℕ} (hB : ∀ b ∈ B, zdN tbl b ∈ B') {t : ℕ}
  (ht : MeetNat M B t) : MeetNat M B' (zdN tbl t) := by
 have htM : zdN tbl t &&& M = zdN tbl t := by
  rw [← hM, ← zdS hnd, ht.1]
 refine ⟨htM, (zdi htM).mpr ?_⟩
 rcases ht with ⟨_, hmt⟩
 unfold isMeet at hmt
 cases h0 : Nat.beq t 0
 ·rw [h0] at hmt
  have heq : zdb t B M = t := Nat.eq_of_beq_eq_true hmt
  rw [← heq]
  apply zdU hnd M hB
  rw [hM, zcW]; exact Meet.top
 ·have ht0 : t = 0 := Nat.eq_of_beq_eq_true h0
  subst ht0
  rw [zdQ, zcV]; exact Meet.bot
theorem zdW {tbl : List ℕ} (hnd : tbl.Nodup) {M edgeTT : ℕ}
  (hM : zdN tbl M = M) (hE : zdN tbl edgeTT = edgeTT)
  {B B' gs : List ℕ} (hB : ∀ b ∈ B, zdN tbl b ∈ B')
  (hr : zdl M B edgeTT gs) :
  zdl M B' edgeTT (gs.map (zdN tbl)) := by
 induction gs generalizing B B' with
 | nil =>
  rw [← hE]
  exact zdV hnd hM hB hr
 | cons g qa ih =>
  rcases hr with ⟨⟨a, b, ha, hb, rfl⟩, qY⟩
  refine ⟨⟨zdN tbl a, zdN tbl b,
   zdV hnd hM hB ha, zdV hnd hM hB hb,
   zdR tbl a b⟩, ?_⟩
  apply ih (B' := B' ++ [zdN tbl (a ||| b)]) _ qY
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  ·exact List.mem_append_left _ (hB x hx)
  ·rw [List.mem_singleton.mp hx]; exact List.mem_append_right _ (by simp)
theorem zdX {α : Type} {f : α → α} :
  ∀ (l : List α), (∀ x ∈ l, f x = x) → l.map f = l
 | [], _ => rfl
 | x :: xs, h => by
  simp only [List.map_cons, h x (by simp), zdX xs (fun y hy => h y (by simp [hy]))]
theorem zdY {n : ℕ} {H F : List (ℕ × ℕ)} {pre suf tbl : List ℕ} {g : ℕ}
  (tf : zdT (univYF n F) (zcy n H (univYF n F)) (rawYF n (univYF n F)) tbl)
  (uP : ∀ h ∈ pre, zdN tbl h = h)
  (qj : zdl (univYF n F) (rawYF n (univYF n F)) (zcy n H (univYF n F))
   (pre ++ g :: suf))
  (qG : ∀ gs', gs'.length = (pre ++ g :: suf).length →
   zdl (univYF n F) (rawYF n (univYF n F)) (zcy n H (univYF n F)) gs' →
   ¬ List.Lex (·< ·) gs' (pre ++ g :: suf)) :
  ¬ (zdN tbl g < g) := by
 intro hlt
 rcases tf with ⟨hnd, hM, hE, qX⟩
 let gs' := (pre ++ g :: suf).map (zdN tbl)
 have zU := zdW hnd hM hE qX qj
 have v1 : pre.map (zdN tbl) = pre := zdX pre uP
 have ts : gs' = pre ++ zdN tbl g :: suf.map (zdN tbl) := by
  simp [gs', v1]
 have hl : List.Lex (·< ·) gs' (pre ++ g :: suf) := by
  rw [ts]
  exact zdL pre _ _ (List.Lex.rel hlt)
 exact qG gs' (by simp [gs']) zU hl
theorem zdZ {M : ℕ} {B₁ B₂ pre : List ℕ}
  (qu : ∀ x ∈ B₁, x ∈ B₂) (hp : zdk M B₁ pre) :
  zdk M B₂ pre := by
 induction pre generalizing B₁ B₂ with
 | nil => trivial
 | cons g qa ih =>
  rcases hp with ⟨⟨a, b, ha, hb, rfl⟩, qY⟩
  refine ⟨⟨a, b, zdn qu ha, zdn qu hb, rfl⟩, ?_⟩
  exact ih (fun x hx => by
   rcases List.mem_append.mp hx with hx | hx
   ·exact List.mem_append_left _ (qu x hx)
   ·exact List.mem_append_right _ hx) qY
theorem zd0 {M : ℕ} {B p₁ p₂ : List ℕ} :
  zdk M B (p₁ ++ p₂) ↔ zdk M B p₁ ∧ zdk M (B ++ p₁) p₂ := by
 induction p₁ generalizing B with
 | nil => simp [zdk]
 | cons g qa ih =>
  simp only [List.cons_append, zdk]
  rw [ih, List.append_assoc, List.singleton_append]
  tauto
theorem zd1 {n : ℕ} {H F : List (ℕ × ℕ)} {pre suf : List ℕ} {g a b mb t : ℕ}
  (qj : zdl (univYF n F) (rawYF n (univYF n F)) (zcy n H (univYF n F))
   (pre ++ g :: suf))
  (qG : ∀ gs', gs'.length = (pre ++ g :: suf).length →
   zdl (univYF n F) (rawYF n (univYF n F)) (zcy n H (univYF n F)) gs' →
   ¬ List.Lex (·< ·) gs' (pre ++ g :: suf))
  (hmb : mb ≤ t) (ht : t < pre.length)
  (ha : MeetNat (univYF n F) (rawYF n (univYF n F) ++ pre.take mb) a)
  (hb : MeetNat (univYF n F) (rawYF n (univYF n F) ++ pre.take mb) b)
  (hg : g = a ||| b) :
  ¬ (g < pre[t]) := by
 intro hlt
 set M := univYF n F
 set raw := rawYF n M
 set target := zcy n H M
 let A := pre.take t
 let B := pre.drop t
 have xi : pre = A ++ B := (List.take_append_drop t pre).symm
 have u7 : B ≠ [] := by
  intro hB
  have qe := congrArg List.length xi
  simp only [hB, List.append_nil, List.length_take, A] at qe
  omega
 obtain ⟨bt, Btail, hBeq⟩ := List.exists_cons_of_ne_nil u7
 have hbt : bt = pre[t] := by
  have h1 : B[0]'(by simp [hBeq]) = pre[t] := by
   simp [B]
  simpa [hBeq] using h1
 have xU : ∀ x ∈ raw ++ pre.take mb, x ∈ raw ++ A := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  ·exact List.mem_append_left _ hx
  ·refine List.mem_append_right _ ?_
   have x8 : pre.take mb = (pre.take t).take mb := by
    rw [List.take_take, Nat.min_eq_left hmb]
   rw [x8] at hx
   exact List.mem_of_mem_take hx
 have haA : MeetNat M (raw ++ A) a := zdn xU ha
 have hbA : MeetNat M (raw ++ A) b := zdn xU hb
 obtain ⟨hp_pre, _, yv⟩ := zdr.mp qj
 rw [xi] at hp_pre
 obtain ⟨hpA, hpB⟩ := zd0.mp hp_pre
 let gs' := A ++ g :: B ++ suf
 have qe : gs'.length = (pre ++ g :: suf).length := by
  have := congrArg List.length xi
  simp only [gs', List.length_append, List.length_cons] at this ⊢
  omega
 have zU : zdl M raw target gs' := by
  have vX : gs' = (A ++ [g] ++ B) ++ suf := by simp [gs', List.append_assoc]
  rw [vX]
  apply zdr.mpr
  constructor
  ·rw [zd0]
   refine ⟨zd0.mpr ⟨hpA, ⟨a, b, haA, hbA, hg⟩, trivial⟩, ?_⟩
   apply zdZ (B₁ := raw ++ A) _ hpB
   intro x hx
   rcases List.mem_append.mp hx with hx | hx
   ·exact List.mem_append_left _ hx
   ·exact List.mem_append_right _ (List.mem_append_left _ hx)
  ·apply zds (B₁ := (raw ++ pre) ++ [g]) _ yv
   intro x
   rw [xi]
   simp; tauto
 have xQ : List.Lex (·< ·) gs' (pre ++ g :: suf) := by
  have h1 : gs' = A ++ (g :: B ++ suf) := by simp [gs']
  have h2 : pre ++ g :: suf = A ++ (bt :: (Btail ++ g :: suf)) := by
   rw [xi, hBeq]; simp [List.append_assoc]
  rw [h1, h2]
  exact zdL A _ _ (List.Lex.rel (hbt.symm ▸ hlt))
 exact qG gs' qe zU xQ
theorem zd2 {n : ℕ} {H F : List (ℕ × ℕ)} {pre suf : List ℕ} {g a b : ℕ}
  (hv : zcC n H F)
  (qj : zdl (univYF n F) (rawYF n (univYF n F)) (zcy n H (univYF n F))
   (pre ++ g :: suf))
  (qz : ∀ k' < (pre ++ g :: suf).length, ¬ zcT n H F k')
  (hb : MeetNat (univYF n F) (rawYF n (univYF n F) ++ pre) b)
  (hg : g = a ||| b)
  (qu : (a &&& zcz H) &&& (b &&& zcz H) = a &&& zcz H) :
  False := by
 set M := univYF n F
 set ep := zcz H
 have hbg : decM M b ⊆ decM M g := by rw [hg, decM_or]; exact Set.subset_union_right
 have heq : decM M b ∩ decM M ep = decM M g ∩ decM M ep := by
  rw [← zcX, ← zcX]
  congr 1
  rw [hg]
  apply Nat.eq_of_testBit_eq; intro s
  have h1 := congrArg (fun z => z.testBit s) qu
  simp only [Nat.testBit_and, Nat.testBit_or] at h1 ⊢
  revert h1
  cases a.testBit s <;> cases b.testBit s <;> cases ep.testBit s <;> decide
 exact zdA hv qj qz (zdm.mp hb).2 hbg heq
theorem zd3 (n : ℕ) (p : ℕ → Bool) : zct n p < 2 ^ n := by
 induction n with
 | zero => simp [zct]
 | succ k ih =>
  simp only [zct]
  have yR : 2 ^ k < 2 ^ (k + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
  have h1 : zct k p < 2 ^ (k + 1) := lt_trans ih yR
  split_ifs
  ·exact Nat.or_lt_two_pow h1 (zcL (by omega))
  ·exact h1
def zd4 (v : ℕ) (E : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
 E.filter (fun e => decide (e.1 ≠ v ∧ e.2 ≠ v))
def degH (H : List (ℕ × ℕ)) (v : ℕ) : ℕ :=
 (H.filter (fun e => decide (e.1 = v ∨ e.2 = v))).length
def zd5 (n v s : ℕ) : ℕ :=
 zct n (fun w => s.testBit w && decide (w ≠ v))
theorem zd6 {n v s w : ℕ} (hs : s < 2 ^ n) :
  (zd5 n v s).testBit w = (s.testBit w && decide (w ≠ v)) := by
 rw [zd5, zcv]
 by_cases hlt : w < n
 ·simp [hlt]
 ·have hsf : s.testBit w = false :=
   Nat.testBit_lt_two_pow (lt_of_lt_of_le hs (Nat.pow_le_pow_right (by omega) (by omega)))
  simp [hlt, hsf]
theorem zd7 {n v : ℕ} {H F : List (ℕ × ℕ)} (hv : zcC n H F) :
  zcC n (zd4 v H) (zd4 v F) := by
 rcases hv with ⟨hH, hF, q3⟩
 refine ⟨fun e he => hH e (List.mem_of_mem_filter he),
  fun f hf => hF f (List.mem_of_mem_filter hf),
  fun e he f hf => q3 e (List.mem_of_mem_filter he) f (List.mem_of_mem_filter hf)⟩
theorem zd8 (H : List (ℕ × ℕ)) (v : ℕ) :
  (zd4 v H).length + degH H v = H.length := by
 unfold zd4 degH
 induction H with
 | nil => simp
 | cons e qa ih =>
  simp only [List.filter_cons, List.length_cons]
  by_cases h : e.1 = v ∨ e.2 = v
  ·have h1 : decide (e.1 ≠ v ∧ e.2 ≠ v) = false := by
    rw [decide_eq_false_iff_not]; omega
   have h2 : decide (e.1 = v ∨ e.2 = v) = true := decide_eq_true h
   simp only [h1, h2, Bool.false_eq_true, ↓reduceIte, List.length_cons]
   omega
  ·have h1 : decide (e.1 ≠ v ∧ e.2 ≠ v) = true := by
    rw [decide_eq_true_eq]; omega
   have h2 : decide (e.1 = v ∨ e.2 = v) = false := decide_eq_false h
   simp only [h1, h2, Bool.false_eq_true, ↓reduceIte, List.length_cons]
   omega
theorem zd9 {n : ℕ} {H F : List (ℕ × ℕ)} {v : ℕ}
  (hv : zcC n H F)
  (wN : ∃ e ∈ H, e.1 = v ∨ e.2 = v)
  (uQ : 1 ≤ (zd4 v H).length)
  {k : ℕ} (hr : zcT n H F k) :
  ∃ j < k, zcT n (zd4 v H) (zd4 v F) j := by
 set H' := zd4 v H
 set F' := zd4 v F
 have hM' : ∀ s, (univYF n F').testBit s = true → s < 2 ^ n := fun _ => zcE
 have yh : ∀ s : Dom (univYF n F'), (univYF n F).testBit (zd5 n v s.1) = true := by
  intro s
  have xX : s.1 < 2 ^ n := hM' s.1 s.2
  rw [zcD, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
  refine ⟨zd3 n _, Bool.eq_false_iff.mpr fun hf => ?_⟩
  rw [zcx] at hf
  obtain ⟨f, hfF, h1, h2⟩ := hf
  rw [zd6 xX, Bool.and_eq_true, decide_eq_true_eq] at h1 h2
  have tq : f ∈ F' := List.mem_filter.mpr ⟨hfF, decide_eq_true ⟨h1.2, h2.2⟩⟩
  have hs2 := s.2
  rw [zcD, Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff] at hs2
  exact hs2.2 (zcx F' s.1 |>.mpr ⟨f, tq, h1.1, h2.1⟩)
 let π : Dom (univYF n F') → Dom (univYF n F) := fun s => ⟨zd5 n v s.1, yh s⟩
 obtain ⟨e₀, he₀H, he₀v⟩ := wN
 obtain ⟨he₀1, he₀2, he₀ne⟩ := hv.1 e₀ he₀H
 let u : ℕ := if e₀.1 = v then e₀.2 else e₀.1
 have uR : u < n := by simp only [u]; split_ifs <;> omega
 have uG : (1 <<< u) ||| (1 <<< v) = (1 <<< e₀.1) ||| (1 <<< e₀.2) := by
  simp only [u]; split_ifs with h
  ·rw [h, Nat.or_comm]
  ·have : e₀.2 = v := he₀v.resolve_left h
   rw [this]
 let yI : ℕ := (1 <<< e₀.1) ||| (1 <<< e₀.2)
 let yK : ℕ := 1 <<< u
 have hpM : (univYF n F).testBit yI = true := zcN hv he₀H
 have hqM : (univYF n F).testBit yK = true := by
  rw [zcD, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
  refine ⟨zcL uR, Bool.eq_false_iff.mpr fun hf => ?_⟩
  rw [zcx] at hf
  obtain ⟨f, hfF, h1, h2⟩ := hf
  rw [zcu, decide_eq_true_eq] at h1 h2
  exact (hv.2.1 f hfF).2.2 (h1.symm.trans h2)
 let p : Dom (univYF n F) := ⟨yI, hpM⟩
 let q : Dom (univYF n F) := ⟨yK, hqM⟩
 have zA : ∀ f ∈ rawSet n F, Meet (rawSet n F') (π ⁻¹' f) := by
  rintro f ⟨w, rfl⟩
  by_cases hw : w.1 = v
  ·have z3 : π ⁻¹' decM (univYF n F) (ttVarYF n w.1 (univYF n F)) = ∅ := by
    ext s
    simp only [Set.mem_preimage, mem_decM, zcF (fun _ => zcE),
     (π s).2, Bool.true_and, Set.mem_empty_iff_false, iff_false]
    change ¬ (zd5 n v s.1).testBit w.1 = true
    rw [zd6 (hM' s.1 s.2), hw]
    simp
   rw [z3]; exact Meet.bot
  ·have heq : π ⁻¹' decM (univYF n F) (ttVarYF n w.1 (univYF n F)) =
     decM (univYF n F') (ttVarYF n w.1 (univYF n F')) := by
    ext s
    simp only [Set.mem_preimage, mem_decM, zcF (fun _ => zcE),
     (π s).2, s.2, Bool.true_and]
    change (zd5 n v s.1).testBit w.1 = true ↔ s.1.testBit w.1 = true
    rw [zd6 (hM' s.1 s.2), decide_eq_true hw, Bool.and_true]
   rw [heq]; exact Meet.atom ⟨w, rfl⟩
 have xO : ∀ f ∈ rawSet n F, Good π p q f := by
  rintro f ⟨w, rfl⟩
  by_cases hw : w.1 = v
  ·right
   ext s
   simp only [Set.mem_preimage, mem_decM, zcF (fun _ => zcE),
    (π s).2, Bool.true_and, Set.mem_empty_iff_false, iff_false]
   change ¬ (zd5 n v s.1).testBit w.1 = true
   rw [zd6 (hM' s.1 s.2), hw]
   simp
  ·left
   simp only [mem_decM, zcF (fun _ => zcE), p.2, q.2, Bool.true_and]
   change yI.testBit w.1 = true ↔ yK.testBit w.1 = true
   dsimp only [yI, yK]
   rw [← uG, zcM, zcu, decide_eq_true_eq]
   constructor
   ·rintro (h | h)
    ·exact h.symm
    ·exact (hw h).elim
   ·intro h; exact Or.inl h.symm
 have xj : π ⁻¹' zcS n H F = zcS n H' F' := by
  ext s
  simp only [Set.mem_preimage, zcS, mem_decM,
   zcG (fun _ => zcE), (π s).2, s.2, Bool.true_and, zcx]
  constructor
  ·rintro ⟨e, heH, h1, h2⟩
   change (zd5 n v s.1).testBit e.1 = true at h1
   change (zd5 n v s.1).testBit e.2 = true at h2
   rw [zd6 (hM' s.1 s.2), Bool.and_eq_true, decide_eq_true_eq] at h1 h2
   exact ⟨e, List.mem_filter.mpr ⟨heH, decide_eq_true ⟨h1.2, h2.2⟩⟩, h1.1, h2.1⟩
  ·rintro ⟨e, heH', h1, h2⟩
   obtain ⟨heH, hne⟩ := List.mem_filter.mp heH'
   rw [decide_eq_true_eq] at hne
   refine ⟨e, heH, ?_, ?_⟩
   ·change (zd5 n v s.1).testBit e.1 = true
    rw [zd6 (hM' s.1 s.2), h1, decide_eq_true hne.1]; rfl
   ·change (zd5 n v s.1).testBit e.2 = true
    rw [zd6 (hM' s.1 s.2), h2, decide_eq_true hne.2]; rfl
 have vc : ¬ Good π p q (zcS n H F) := by
  rintro (hiff | z3)
  ·have hpT : p ∈ zcS n H F := zcO hv he₀H
   have hqT : q ∈ zcS n H F := hiff.mp hpT
   rw [zcS, mem_decM, zcG (fun _ => zcE), q.2, Bool.true_and,
    zcx] at hqT
   obtain ⟨e, heH, h1, h2⟩ := hqT
   change (1 <<< u).testBit e.1 = true at h1
   change (1 <<< u).testBit e.2 = true at h2
   rw [zcu, decide_eq_true_eq] at h1 h2
   exact (hv.1 e heH).2.2 (h1.symm.trans h2)
  ·rw [xj] at z3
   have uf : H' ≠ [] := by intro h; simp [h] at uQ
   obtain ⟨e₁, _, he₁eq⟩ := List.exists_cons_of_ne_nil uf
   have he₁mem : e₁ ∈ H' := by rw [he₁eq]; simp
   have hv' : zcC n H' F' := zd7 hv
   have hs₁M' : (univYF n F').testBit ((1 <<< e₁.1) ||| (1 <<< e₁.2)) = true :=
    zcN hv' he₁mem
   have hs₁T' : (⟨(1 <<< e₁.1) ||| (1 <<< e₁.2), hs₁M'⟩ : Dom (univYF n F')) ∈
     zcS n H' F' :=
    zcO hv' he₁mem
   rw [z3] at hs₁T'
   exact hs₁T'
 obtain ⟨j, hj, hr'⟩ := paidMap π p q zA xO hr vc
 rw [xj] at hr'
 exact ⟨j, hj, hr'⟩
theorem zea {n : ℕ} {H F : List (ℕ × ℕ)} {v : ℕ}
  (hv : zcC n H F) (yg : degH H v = 1) (qe : 2 ≤ H.length)
  (hlb : zcU n (zd4 v H) (zd4 v F) ((zd4 v H).length - 1)) :
  zcU n H F (H.length - 1) := by
 have q9 : (zd4 v H).length + 1 = H.length := by
  have := zd8 H v; omega
 have wN : ∃ e ∈ H, e.1 = v ∨ e.2 = v := by
  unfold degH at yg
  have hne : H.filter (fun e => decide (e.1 = v ∨ e.2 = v)) ≠ [] := by
   intro h; rw [h] at yg; simp at yg
  obtain ⟨e, _, heq⟩ := List.exists_cons_of_ne_nil hne
  have qo : e ∈ H.filter (fun e => decide (e.1 = v ∨ e.2 = v)) := by rw [heq]; simp
  obtain ⟨heH, hv'⟩ := List.mem_filter.mp qo
  exact ⟨e, heH, decide_eq_true_eq.mp hv'⟩
 intro k hr
 obtain ⟨j, hj, hr'⟩ := zd9 hv wN (by omega) hr
 have h1 := hlb j hr'
 omega
def zeb (f : List ℕ) (t i acc : ℕ) : ℕ :=
 match f with
 | [] => acc
 | u :: qa =>
  let zJ := match t.testBit i with
   | true => Nat.lor acc (1 <<< u)
   | false => acc
  zeb qa t (i + 1) zJ
def mapSub (f : List ℕ) (t : ℕ) : ℕ := zeb f t 0 0
theorem zec (f : List ℕ) (t w : ℕ) :
  (mapSub f t).testBit w = true ↔
   ∃ (i : ℕ) (hi : i < f.length), f[i] = w ∧ t.testBit i = true := by
 have heq : ∀ (l : List ℕ) (i acc : ℕ), zeb l t i acc = zdM l t i acc := by
  intro l
  induction l with
  | nil => intro _ _; rfl
  | cons u qa ih =>
   intro i acc
   simp only [zeb, zdM]
   exact ih (i + 1) _
 change (zeb f t 0 0).testBit w = true ↔ _
 rw [heq f 0 0]
 exact zdP f t w
def zed (n : ℕ) (H F : List (ℕ × ℕ)) (n' : ℕ) (H' F' : List (ℕ × ℕ)) (f : List ℕ) : Bool :=
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
theorem zee (e₁ e₂ : ℕ × ℕ) :
  undirEq e₁ e₂ = true ↔ (e₁.1 = e₂.1 ∧ e₁.2 = e₂.2) ∨ (e₁.1 = e₂.2 ∧ e₁.2 = e₂.1) := by
 simp [undirEq]
theorem zef {n : ℕ} {f : List ℕ} (hf : ∀ x ∈ f, x < n) (t : ℕ) :
  mapSub f t < 2 ^ n := by
 have heq : mapSub f t = zct n (fun w => (mapSub f t).testBit w) := by
  apply Nat.eq_of_testBit_eq; intro w
  rw [zcv]
  cases hw : (mapSub f t).testBit w
  ·simp
  ·obtain ⟨i, hi, qR, _⟩ := (zec f t w).mp hw
   have hwn : w < n := qR ▸ hf f[i] (List.getElem_mem hi)
   simp [hwn]
 rw [heq]; exact zd3 n _
theorem zeg {n n' : ℕ} {H F H' F' : List (ℕ × ℕ)} {f : List ℕ}
  (wG : zed n H F n' H' F' f = true) :
  ∀ k, zcT n H F k → zcT n' H' F' k := by
 unfold zed at wG
 simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.any_eq_true,
  Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, List.mem_range] at wG
 obtain ⟨⟨⟨⟨⟨qe, hnd⟩, hflt⟩, hHdir⟩, hH'dir⟩, hFdir⟩ := wG
 have wE : ∀ t : Dom (univYF n' F'), (univYF n F).testBit (mapSub f t.1) = true := by
  intro t
  rw [zcD, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
  refine ⟨zef hflt t.1, Bool.eq_false_iff.mpr fun hf => ?_⟩
  rw [zcx] at hf
  obtain ⟨e, heF, h1, h2⟩ := hf
  obtain ⟨i, hi, hfi, hti⟩ := (zec f t.1 e.1).mp h1
  obtain ⟨j, hj, hfj, htj⟩ := (zec f t.1 e.2).mp h2
  have hi' : i < n' := qe ▸ hi
  have hj' : j < n' := qe ▸ hj
  have hgi : f.getD i 0 = e.1 := by rw [List.getD_eq_getElem _ _ hi]; exact hfi
  have hgj : f.getD j 0 = e.2 := by rw [List.getD_eq_getElem _ _ hj]; exact hfj
  rcases hFdir e heF i hi' j hj' with hno | ⟨f', hf'F', hue⟩
  ·exact hno ⟨hgi, hgj⟩
  ·have ht2 := t.2
   rw [zcD, Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff] at ht2
   rw [zee] at hue
   apply ht2.2
   rw [zcx]
   rcases hue with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
   ·exact ⟨f', hf'F', h1'.symm ▸ hti, h2'.symm ▸ htj⟩
   ·exact ⟨f', hf'F', h1'.symm ▸ htj, h2'.symm ▸ hti⟩
 let π : Dom (univYF n' F') → Dom (univYF n F) := fun t => ⟨mapSub f t.1, wE t⟩
 have zA : ∀ S ∈ rawSet n F, Meet (rawSet n' F') (π ⁻¹' S) := by
  rintro S ⟨v, rfl⟩
  by_cases hv : ∃ (i : ℕ) (hi : i < f.length), f[i] = v.1
  ·obtain ⟨i, hi, hfi⟩ := hv
   have hi' : i < n' := qe ▸ hi
   have heq : π ⁻¹' decM (univYF n F) (ttVarYF n v.1 (univYF n F)) =
     decM (univYF n' F') (ttVarYF n' i (univYF n' F')) := by
    ext t
    simp only [Set.mem_preimage, mem_decM, zcF (fun _ => zcE),
     (π t).2, t.2, Bool.true_and]
    change (mapSub f t.1).testBit v.1 = true ↔ t.1.testBit i = true
    rw [zec]
    constructor
    ·rintro ⟨j, hj, hfj, htj⟩
     have hij : j = i := (List.Nodup.getElem_inj_iff hnd).mp (hfj.trans hfi.symm)
     exact hij ▸ htj
    ·intro hti; exact ⟨i, hi, hfi, hti⟩
   rw [heq]; exact Meet.atom ⟨⟨i, hi'⟩, rfl⟩
  ·have z3 : π ⁻¹' decM (univYF n F) (ttVarYF n v.1 (univYF n F)) = ∅ := by
    ext t
    simp only [Set.mem_preimage, mem_decM, zcF (fun _ => zcE),
     (π t).2, Bool.true_and, Set.mem_empty_iff_false, iff_false]
    change ¬ (mapSub f t.1).testBit v.1 = true
    rw [zec]
    rintro ⟨i, hi, hfi, _⟩
    exact hv ⟨i, hi, hfi⟩
   rw [z3]; exact Meet.bot
 have qZ : π ⁻¹' zcS n H F = zcS n' H' F' := by
  ext t
  simp only [Set.mem_preimage, zcS, mem_decM,
   zcG (fun _ => zcE), (π t).2, t.2, Bool.true_and, zcx]
  constructor
  ·rintro ⟨e, heH, h1, h2⟩
   change (mapSub f t.1).testBit e.1 = true at h1
   change (mapSub f t.1).testBit e.2 = true at h2
   obtain ⟨i, hi, hfi, hti⟩ := (zec f t.1 e.1).mp h1
   obtain ⟨j, hj, hfj, htj⟩ := (zec f t.1 e.2).mp h2
   obtain ⟨e', he'H', ⟨he'1, he'2⟩, hue⟩ := hHdir e heH
   have y1 : e'.1 < f.length := qe.symm ▸ he'1
   have y2 : e'.2 < f.length := qe.symm ▸ he'2
   rw [List.getD_eq_getElem _ _ y1, List.getD_eq_getElem _ _ y2, zee] at hue
   rcases hue with ⟨hu1, hu2⟩ | ⟨hu1, hu2⟩
   ·have hi1 : i = e'.1 := (List.Nodup.getElem_inj_iff hnd).mp (hfi.trans hu1)
    have hj2 : j = e'.2 := (List.Nodup.getElem_inj_iff hnd).mp (hfj.trans hu2)
    exact ⟨e', he'H', hi1 ▸ hti, hj2 ▸ htj⟩
   ·have hi2 : i = e'.2 := (List.Nodup.getElem_inj_iff hnd).mp (hfi.trans hu1)
    have hj1 : j = e'.1 := (List.Nodup.getElem_inj_iff hnd).mp (hfj.trans hu2)
    exact ⟨e', he'H', hj1 ▸ htj, hi2 ▸ hti⟩
  ·rintro ⟨e', he'H', h1, h2⟩
   obtain ⟨⟨he'1, he'2⟩, e, heH, hue⟩ := hH'dir e' he'H'
   have y1 : e'.1 < f.length := qe.symm ▸ he'1
   have y2 : e'.2 < f.length := qe.symm ▸ he'2
   rw [List.getD_eq_getElem _ _ y1, List.getD_eq_getElem _ _ y2, zee] at hue
   refine ⟨e, heH, ?_, ?_⟩
   ·change (mapSub f t.1).testBit e.1 = true
    rw [zec]
    rcases hue with ⟨hu1, _⟩ | ⟨hu1, _⟩
    ·exact ⟨e'.1, y1, hu1.symm, h1⟩
    ·exact ⟨e'.2, y2, hu1.symm, h2⟩
   ·change (mapSub f t.1).testBit e.2 = true
    rw [zec]
    rcases hue with ⟨_, hu2⟩ | ⟨_, hu2⟩
    ·exact ⟨e'.2, y2, hu2.symm, h2⟩
    ·exact ⟨e'.1, y1, hu2.symm, h1⟩
 intro k hr
 have hr' := freeMap π zA hr
 rwa [qZ] at hr'
def zeh (n : ℕ) (H F : List (ℕ × ℕ)) :
  List ℕ → ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → List ℕ → Bool
 | [], n', H', F', f => decide (H.length = H'.length) && zed n H F n' H' F' f
 | v :: qa, n', H', F', f =>
  decide (degH H v = 1 ∧ 2 ≤ H.length) &&
  zeh n (zd4 v H) (zd4 v F) qa n' H' F' f
theorem zei {n : ℕ} {H F : List (ℕ × ℕ)} {peels : List ℕ}
  {n' : ℕ} {H' F' : List (ℕ × ℕ)} {f : List ℕ}
  (hv : zcC n H F)
  (hok : zeh n H F peels n' H' F' f = true)
  (hlb : zcU n' H' F' (H'.length - 1)) :
  zcU n H F (H.length - 1) := by
 induction peels generalizing H F with
 | nil =>
  simp only [zeh, Bool.and_eq_true, decide_eq_true_eq] at hok
  rw [hok.1]
  intro k hr
  exact hlb k (zeg hok.2 k hr)
 | cons v qa ih =>
  simp only [zeh, Bool.and_eq_true, decide_eq_true_eq] at hok
  exact zea hv hok.1.1 hok.1.2 (ih (zd7 hv) hok.2)
def zej (mc pm h : ℕ) : Bool :=
 let x := Nat.land h pm
 match Nat.beq x 0 with
 | true => true
 | false =>
  match Nat.beq x pm with
  | true => true
  | false => Nat.beq (Nat.land h mc) 0
def zek (mc : ℕ) (rc : List ℕ) (act : List ℕ) : List ℕ × List ℕ × ℕ :=
 let rec go : List ℕ → List ℕ → List ℕ → ℕ → List ℕ × List ℕ × ℕ
  | [], sb, qg, sv => (sb, qg.reverse, sv)
  | g :: qa, sb, qg, sv =>
   let rg := Nat.land g mc
   match isMeet mc sb rg with
   | true => go qa sb qg (sv + 1)
   | false => go qa (rg :: sb) (rg :: qg) sv
 go act rc [] 0
theorem zel {qh mc : ℕ} (hmc : mc &&& qh = mc)
  {qk rc : List ℕ}
  (qX : ∀ r ∈ qk, r &&& mc = 0 ∨ r &&& mc ∈ rc) :
  ∀ (qa sb qg : List ℕ) (sv : ℕ) (done : List ℕ),
   (∀ x ∈ sb, x ∈ rc ++ qg.reverse) →
   (∀ x ∈ rc ++ qg.reverse, x ∈ sb) →
   zdk mc rc qg.reverse →
   (∀ h ∈ done, MeetNat mc sb (h &&& mc)) →
   zdk qh (qk ++ done) qa →
   let res := zek.go mc qa sb qg sv
   res.2.1.length + res.2.2 = qg.length + sv + qa.length ∧
   zdk mc rc res.2.1 ∧
   (∀ x ∈ res.1, x ∈ rc ++ res.2.1) ∧
   (∀ x ∈ rc ++ res.2.1, x ∈ res.1) ∧
   (∀ h ∈ done ++ qa, MeetNat mc res.1 (h &&& mc)) := by
 intro qa
 induction qa with
 | nil =>
  intro sb qg sv done xW yq hvp xN _
  simp only [zek.go, List.length_reverse, List.length_nil, add_zero, List.append_nil]
  exact ⟨trivial, hvp, xW, yq, xN⟩
 | cons g qb ih =>
  intro sb qg sv done xW yq hvp xN vA
  rcases vA with ⟨⟨a, b, ha, hb, hgab⟩, htail_vp⟩
  have v3 : (g &&& mc) &&& mc = g &&& mc := by
   apply Nat.eq_of_testBit_eq; intro s; simp [Nat.testBit_and]
  have yP : ∀ x ∈ qk ++ done, MeetNat mc sb (x &&& mc) := by
   intro x hx
   have hxM : (x &&& mc) &&& mc = x &&& mc := by
    apply Nat.eq_of_testBit_eq; intro s; simp [Nat.testBit_and]
   rcases List.mem_append.mp hx with hx | hx
   ·rcases qX x hx with h0 | qo
    ·rw [h0]; exact ⟨by simp, by simp [isMeet]⟩
    ·exact zdm.mpr ⟨hxM, Meet.atom ⟨x &&& mc, yq _ (List.mem_append_left _ qo), rfl⟩⟩
   ·exact xN x hx
  let ι : Dom mc → Dom qh := fun s => ⟨s.1, zcY hmc s.2⟩
  have hι_meet : ∀ {t : ℕ}, MeetNat qh (qk ++ done) t → MeetNat mc sb (t &&& mc) := by
   intro t ht
   have htM : (t &&& mc) &&& mc = t &&& mc := by
    apply Nat.eq_of_testBit_eq; intro s; simp [Nat.testBit_and]
   refine zdm.mpr ⟨htM, ?_⟩
   have yn : ι ⁻¹' decM qh t = decM mc (t &&& mc) := by
    ext s; simp [ι, decM, Nat.testBit_and, s.2]
   rw [← yn]
   apply mapMeet ι _ (zdm.mp ht).2
   rintro S ⟨x, hx, rfl⟩
   have hpx : ι ⁻¹' decM qh x = decM mc (x &&& mc) := by
    ext s; simp [ι, decM, Nat.testBit_and, s.2]
   rw [hpx]
   exact (zdm.mp (yP x hx)).2
  have td : MeetNat mc sb (a &&& mc) := hι_meet ha
  have tg : MeetNat mc sb (b &&& mc) := hι_meet hb
  have wM : g &&& mc = (a &&& mc) ||| (b &&& mc) := by
   rw [hgab]
   apply Nat.eq_of_testBit_eq; intro s
   simp only [Nat.testBit_and, Nat.testBit_or]
   cases a.testBit s <;> cases b.testBit s <;> cases mc.testBit s <;> decide
  have zI : zdk qh (qk ++ (done ++ [g])) qb := by
   simpa only [List.append_assoc] using htail_vp
  simp only [zek.go, land_eq]
  cases hm : isMeet mc sb (g &&& mc)
  ·-- not a meet: push `rg = g &&& mc` to `sb` and `qg`
   have w8 : zdk mc rc ((g &&& mc) :: qg).reverse := by
    rw [List.reverse_cons, zd0]
    refine ⟨hvp, ⟨a &&& mc, b &&& mc,
     zdn xW td, zdn xW tg, wM⟩, trivial⟩
   have h1 := ih ((g &&& mc) :: sb) ((g &&& mc) :: qg) sv (done ++ [g])
    (fun x hx => by
     rw [List.reverse_cons]
     rcases List.mem_cons.mp hx with rfl | hx
     ·simp
     ·have := xW x hx; simp only [List.mem_append] at this ⊢; tauto)
    (fun x hx => by
     rw [List.reverse_cons] at hx
     rcases List.mem_append.mp hx with hx | hx
     ·exact List.mem_cons_of_mem _ (yq x (List.mem_append_left _ hx))
     ·rcases List.mem_append.mp hx with hx | hx
      ·exact List.mem_cons_of_mem _ (yq x (List.mem_append_right _ hx))
      ·rw [List.mem_singleton.mp hx]; exact List.mem_cons_self)
    w8
    (fun h hh => by
     rcases List.mem_append.mp hh with hh | hh
     ·exact zdn (fun x hx => List.mem_cons_of_mem _ hx) (xN h hh)
     ·rw [List.mem_singleton.mp hh]
      exact zdm.mpr ⟨v3, Meet.atom ⟨g &&& mc, List.mem_cons_self, rfl⟩⟩)
    zI
   simpa only [List.length_cons, List.append_assoc, List.singleton_append, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm] using h1
  ·-- is a meet: increment `sv`
   have h1 := ih sb qg (sv + 1) (done ++ [g]) xW yq hvp
    (fun h hh => by
     rcases List.mem_append.mp hh with hh | hh
     ·exact xN h hh
     ·rw [List.mem_singleton.mp hh]; exact ⟨v3, hm⟩)
    zI
   simpa only [List.length_cons, List.append_assoc, List.singleton_append, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm] using h1
theorem zem {qh mc pm p q : ℕ}
  (hmc : mc &&& qh = mc)
  (hpM : qh.testBit p = true) (hqM : qh.testBit q = true)
  (wg : pm.testBit p = true) (wh : pm.testBit q = true)
  {h : ℕ} (hok : zej mc pm h = true) :
  Good (fun s : Dom mc => (⟨s.1, zcY hmc s.2⟩ : Dom qh))
   ⟨p, hpM⟩ ⟨q, hqM⟩ (decM qh h) := by
 unfold zej at hok
 dsimp only at hok
 cases h0 : Nat.beq (Nat.land h pm) 0
 ·rw [h0] at hok
  cases h1 : Nat.beq (Nat.land h pm) pm
  ·rw [h1] at hok
   have tu : h &&& mc = 0 := by simpa [land_eq] using Nat.eq_of_beq_eq_true hok
   right
   ext s
   simp only [Set.mem_preimage, decM, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
   intro hs
   have := congrArg (fun z => z.testBit s.1) tu
   rw [Nat.testBit_and, hs, s.2] at this
   simp at this
  ·have hpm : h &&& pm = pm := by simpa [land_eq] using Nat.eq_of_beq_eq_true h1
   left
   have hp : h.testBit p = true := by
    have := congrArg (fun z => z.testBit p) hpm
    rw [Nat.testBit_and, wg, Bool.and_true] at this; exact this
   have hq : h.testBit q = true := by
    have := congrArg (fun z => z.testBit q) hpm
    rw [Nat.testBit_and, wh, Bool.and_true] at this; exact this
   simp [decM, hp, hq]
 ·have uI : h &&& pm = 0 := by simpa [land_eq] using Nat.eq_of_beq_eq_true h0
  left
  have hp : h.testBit p = false := by
   have := congrArg (fun z => z.testBit p) uI
   rw [Nat.testBit_and, wg, Bool.and_true, Nat.zero_testBit] at this; exact this
  have hq : h.testBit q = false := by
   have := congrArg (fun z => z.testBit q) uI
   rw [Nat.testBit_and, wh, Bool.and_true, Nat.zero_testBit] at this; exact this
  simp [decM, hp, hq]
theorem zen {qh edgeTT pm : ℕ}
  (vZ : pm &&& qh = pm)
  (wS : pm &&& edgeTT ≠ 0)
  (wT : pm &&& edgeTT ≠ pm) :
  ∃ p q : ℕ, qh.testBit p = true ∧ qh.testBit q = true ∧
   pm.testBit p = true ∧ pm.testBit q = true ∧
   edgeTT.testBit p = true ∧ edgeTT.testBit q = false := by
 have tn : ∃ p, (pm &&& edgeTT).testBit p = true := by
  by_contra hall; push Not at hall
  apply wS; apply Nat.eq_of_testBit_eq; intro s
  simp only [Nat.zero_testBit]; exact Bool.eq_false_iff.mpr (hall s)
 have tp : ∃ q, (pm &&& edgeTT).testBit q ≠ pm.testBit q := by
  by_contra hall; push Not at hall
  exact wT (Nat.eq_of_testBit_eq hall)
 obtain ⟨p, hp⟩ := tn
 rw [Nat.testBit_and, Bool.and_eq_true] at hp
 obtain ⟨q, hq⟩ := tp
 rw [Nat.testBit_and] at hq
 have hqp : pm.testBit q = true := by
  cases h : pm.testBit q
  ·simp [h] at hq
  ·rfl
 have hqe : edgeTT.testBit q = false := by
  cases h : edgeTT.testBit q
  ·rfl
  ·simp [hqp, h] at hq
 exact ⟨p, q, zcY vZ hp.1, zcY vZ hqp, hp.1, hqp, hp.2, hqe⟩
theorem zeo {qh mc edgeTT : ℕ} {qk rc qD pv : List ℕ} {zE : ℕ}
  (hmc : mc &&& qh = mc)
  (qX : ∀ r ∈ qk, r &&& mc = 0 ∨ r &&& mc ∈ rc)
  (vK : zdk qh qk qD)
  (xt : Run (decM qh '' { x | x ∈ qk ++ qD }) zE (decM qh edgeTT))
  (yT : ∀ pm ∈ pv, pm &&& qh = pm ∧ pm &&& edgeTT ≠ 0 ∧ pm &&& edgeTT ≠ pm ∧
   edgeTT &&& mc ≠ 0 ∧ ∀ r ∈ qk, zej mc pm r = true) :
  let res := zek mc rc qD
  let yZ := if pv.any (fun pm => qD.all (fun h => zej mc pm h)) then 1 else 0
  zdk mc rc res.2.1 ∧
  ∃ xJ : ℕ,
   res.2.1.length + xJ + res.2.2 + yZ ≤ qD.length + zE ∧
   Run (decM mc '' { x | x ∈ rc ++ res.2.1 }) xJ (decM mc edgeTT) := by
 have yO := zel hmc qX qD rc [] 0 []
  (fun x hx => by simpa using hx)
  (fun x hx => by simpa using hx)
  trivial
  (fun _ h => by simp at h)
  (by simpa using vK)
 simp only [List.length_nil, zero_add, List.nil_append] at yO
 obtain ⟨qe, hvp_next, xW, yq, hall_meet⟩ := yO
 change (zek mc rc qD).2.1.length + (zek mc rc qD).2.2 =
  qD.length at qe
 let ι : Dom mc → Dom qh := fun s => ⟨s.1, zcY hmc s.2⟩
 have qZ : ι ⁻¹' decM qh edgeTT = decM mc edgeTT := by
  ext s; simp [ι, decM]
 have zA : ∀ S ∈ decM qh '' { x | x ∈ qk ++ qD },
   Meet (decM mc '' { x | x ∈ rc ++ (zek mc rc qD).2.1 }) (ι ⁻¹' S) := by
  rintro S ⟨x, hx, rfl⟩
  have yn : ι ⁻¹' decM qh x = decM mc (x &&& mc) := by
   ext s; simp [ι, decM, Nat.testBit_and, s.2]
  rw [yn]
  rcases List.mem_append.mp hx with hx | hx
  ·rcases qX x hx with h0 | qo
   ·rw [h0, zcV]; exact Meet.bot
   ·exact Meet.atom ⟨x &&& mc, List.mem_append_left _ qo, rfl⟩
  ·exact weaken (Set.image_mono (fun y hy => xW y hy)) (zdm.mp (hall_meet x hx)).2
 dsimp only
 refine ⟨hvp_next, ?_⟩
 split_ifs with hprobe
 ·rw [List.any_eq_true] at hprobe
  obtain ⟨pm, hpm_mem, hact_ok⟩ := hprobe
  rw [List.all_eq_true] at hact_ok
  obtain ⟨vZ, wS, wT, hedgemc, hraw_ok⟩ := yT pm hpm_mem
  obtain ⟨p, q, hpM, hqM, hppm, hqpm, hpe, hqe⟩ := zen vZ wS wT
  have xO : ∀ S ∈ decM qh '' { x | x ∈ qk ++ qD },
    Good ι ⟨p, hpM⟩ ⟨q, hqM⟩ S := by
   rintro S ⟨x, hx, rfl⟩
   rcases List.mem_append.mp hx with hx | hx
   ·exact zem hmc hpM hqM hppm hqpm (hraw_ok x hx)
   ·exact zem hmc hpM hqM hppm hqpm (hact_ok x hx)
  have vc : ¬ Good ι ⟨p, hpM⟩ ⟨q, hqM⟩ (decM qh edgeTT) := by
   rintro (hiff | z3)
   ·have : edgeTT.testBit q = true := hiff.mp hpe
    simp [hqe] at this
   ·rw [qZ] at z3
    have hex : ∃ s, (edgeTT &&& mc).testBit s = true := by
     by_contra hall; push Not at hall
     apply hedgemc; apply Nat.eq_of_testBit_eq; intro s
     simp only [Nat.zero_testBit]; exact Bool.eq_false_iff.mpr (hall s)
    obtain ⟨s, hs⟩ := hex
    rw [Nat.testBit_and, Bool.and_eq_true] at hs
    have : (⟨s, hs.2⟩ : Dom mc) ∈ decM mc edgeTT := hs.1
    rw [z3] at this; exact this
  obtain ⟨j, hj, hr'⟩ := paidMap ι ⟨p, hpM⟩ ⟨q, hqM⟩ zA xO xt vc
  rw [qZ] at hr'
  exact ⟨j, by omega, hr'⟩
 ·have hr' := freeMap ι zA xt
  rw [qZ] at hr'
  exact ⟨zE, by omega, hr'⟩
theorem zep (a b : ℕ) : Nat.beq a b = true ↔ a = b :=
 ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl a⟩
theorem zeq {a b : ℕ} (h : Nat.blt a b = true) : a < b :=
 Nat.le_of_ble_eq_true h
theorem zer (a b : ℕ) : Nat.sub a b = a - b := rfl
theorem zes (a b : ℕ) : Nat.div a b = a / b := rfl
theorem zet (a b : ℕ) : Nat.beq a b = false ↔ a ≠ b := by
 cases h : Nat.beq a b
 ·exact ⟨fun _ heq => by subst heq; simp at h, fun _ => rfl⟩
 ·exact ⟨fun hc => (Bool.false_ne_true hc.symm).elim, fun hne => (hne (Nat.eq_of_beq_eq_true h)).elim⟩
structure zeu where
 mc : ℕ
 rc : List ℕ
 pv : List ℕ
def zev (qh edgeTT : ℕ) (qk : List ℕ) (st : zeu) : Prop :=
 st.mc &&& qh = st.mc ∧
 (∀ r ∈ qk, r &&& st.mc = 0 ∨ r &&& st.mc ∈ st.rc) ∧
 (∀ pm ∈ st.pv, pm &&& qh = pm ∧ pm &&& edgeTT ≠ 0 ∧ pm &&& edgeTT ≠ pm ∧
  edgeTT &&& st.mc ≠ 0 ∧ ∀ r ∈ qk, zej st.mc pm r = true)
def zew (steps : List zeu) (act : List ℕ) : ℕ :=
 match steps with
 | [] => 0
 | st :: qa =>
  let res := zek st.mc st.rc act
  let yZ := if st.pv.any (fun pm => act.all (fun h => zej st.mc pm h)) then 1 else 0
  res.2.2 + yZ + zew qa res.2.1
def zex (M edgeTT : ℕ) (raw : List ℕ) : List zeu → ℕ → List ℕ → Prop
 | [], qT, qK => M = qT ∧ raw = qK
 | st :: qa, qT, qK =>
  zev M edgeTT raw st ∧ zex st.mc edgeTT st.rc qa qT qK
theorem zey {M edgeTT qT : ℕ} {raw qK : List ℕ}
  (steps : List zeu)
  (vJ : zex M edgeTT raw steps qT qK)
  {act : List ℕ} {zE : ℕ}
  (hvp : zdk M raw act)
  (qj : Run (decM M '' { x | x ∈ raw ++ act }) zE (decM M edgeTT)) :
  ∃ zD : ℕ, zD + zew steps act ≤ act.length + zE ∧
   Run (decM qT '' { x | x ∈ qK }) zD (decM qT edgeTT) := by
 induction steps generalizing M raw act zE with
 | nil =>
  rcases vJ with ⟨rfl, rfl⟩
  refine ⟨act.length + zE, by simp [zew], zdt hvp qj⟩
 | cons st qa ih =>
  rcases vJ with ⟨⟨hmc, qX, hpv⟩, qY⟩
  have qQ := zeo hmc qX hvp qj hpv
  dsimp only at qQ
  obtain ⟨w8, xJ, hbudget, zU⟩ := qQ
  obtain ⟨zD, hle, hrun_end⟩ := ih qY w8 zU
  refine ⟨zD, ?_, hrun_end⟩
  simp only [zew]
  omega
def zez (n vm s : ℕ) : ℕ :=
 zct n (fun w => s.testBit w && !vm.testBit w)
theorem zeA {n vm s w : ℕ} (hs : s < 2 ^ n) :
  (zez n vm s).testBit w = (s.testBit w && !vm.testBit w) := by
 rw [zez, zcv]
 by_cases hlt : w < n
 ·simp [hlt]
 ·have hsf : s.testBit w = false :=
   Nat.testBit_lt_two_pow (lt_of_lt_of_le hs (Nat.pow_le_pow_right (by omega) (by omega)))
  simp [hlt, hsf]
theorem zeB {n : ℕ} {H F forbAdded : List (ℕ × ℕ)} {delVMask q6 : ℕ}
  {z7 : List ℕ} {zD : ℕ}
  (zR : ∀ s, q6.testBit s = true ↔
   (univYF n (F ++ forbAdded)).testBit s = true ∧ s &&& delVMask = 0)
  (vx : ∀ r ∈ z7, r = 0 ∨ ∃ w < n, r = ttVarYF n w (univYF n F) &&& q6)
  (qj : Run (decM q6 '' { x | x ∈ z7 }) zD (decM q6 (zcy n H (univYF n F)))) :
  let z8 := H.filter (fun e => !forbAdded.any (undirEq e) && !delVMask.testBit e.1 && !delVMask.testBit e.2)
  let zc := (F ++ forbAdded).filter (fun e => !delVMask.testBit e.1 && !delVMask.testBit e.2)
  zcT n z8 zc zD := by
 dsimp only
 set z8 := H.filter (fun e => !forbAdded.any (undirEq e) && !delVMask.testBit e.1 && !delVMask.testBit e.2)
 set zc := (F ++ forbAdded).filter (fun e => !delVMask.testBit e.1 && !delVMask.testBit e.2)
 have hM : ∀ s, (univYF n F).testBit s = true → s < 2 ^ n := fun _ => zcE
 have zZ : ∀ s, (univYF n zc).testBit s = true → s < 2 ^ n := fun _ => zcE
 have wE : ∀ s : Dom (univYF n zc), q6.testBit (zez n delVMask s.1) = true := by
  intro s
  have xX : s.1 < 2 ^ n := zZ s.1 s.2
  rw [zR]
  constructor
  ·rw [zcD, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
   refine ⟨zd3 n _, Bool.eq_false_iff.mpr fun hf => ?_⟩
   rw [zcx] at hf
   obtain ⟨f, hfmem, h1, h2⟩ := hf
   rw [zeA xX, Bool.and_eq_true] at h1 h2
   have xd : f ∈ zc := List.mem_filter.mpr ⟨hfmem, by simp [h1.2, h2.2]⟩
   have hs2 := s.2
   rw [zcD, Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff] at hs2
   exact hs2.2 (zcx zc s.1 |>.mpr ⟨f, xd, h1.1, h2.1⟩)
  ·apply Nat.eq_of_testBit_eq; intro w
   rw [Nat.testBit_and, zeA xX, Nat.zero_testBit]
   cases s.1.testBit w <;> cases delVMask.testBit w <;> decide
 have z4 : ∀ s, q6.testBit s = true → (univYF n F).testBit s = true := by
  intro s hs
  have h1 := (zR s).mp hs |>.1
  rw [zcD, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', Bool.eq_false_iff] at h1
  rw [zcD, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', Bool.eq_false_iff]
  refine ⟨h1.1, fun hf => h1.2 ?_⟩
  rw [zcx] at hf ⊢
  obtain ⟨f, hfF, h2, h3⟩ := hf
  exact ⟨f, List.mem_append_left _ hfF, h2, h3⟩
 let π : Dom (univYF n zc) → Dom q6 := fun s => ⟨zez n delVMask s.1, wE s⟩
 have zA : ∀ S ∈ decM q6 '' { x | x ∈ z7 }, Meet (rawSet n zc) (π ⁻¹' S) := by
  rintro S ⟨r, hr, rfl⟩
  rcases vx r hr with rfl | ⟨w, hw, rfl⟩
  ·rw [zcV, Set.preimage_empty]; exact Meet.bot
  ·by_cases hdel : delVMask.testBit w = true
   ·have z3 : π ⁻¹' decM q6 (ttVarYF n w (univYF n F) &&& q6) = ∅ := by
     ext s
     simp only [Set.mem_preimage, mem_decM, Nat.testBit_and, (π s).2, Bool.and_true,
      zcF hM, z4 _ (π s).2, Bool.true_and, Set.mem_empty_iff_false, iff_false]
     change ¬ (zez n delVMask s.1).testBit w = true
     rw [zeA (zZ s.1 s.2), hdel]; simp
    rw [z3]; exact Meet.bot
   ·have uo : delVMask.testBit w = false := Bool.eq_false_iff.mpr hdel
    have heq : π ⁻¹' decM q6 (ttVarYF n w (univYF n F) &&& q6) =
      decM (univYF n zc) (ttVarYF n w (univYF n zc)) := by
     ext s
     simp only [Set.mem_preimage, mem_decM, Nat.testBit_and, (π s).2, Bool.and_true,
      zcF hM, zcF zZ, z4 _ (π s).2, s.2, Bool.true_and]
     change (zez n delVMask s.1).testBit w = true ↔ s.1.testBit w = true
     rw [zeA (zZ s.1 s.2), uo]; simp
    rw [heq]; exact Meet.atom ⟨⟨w, hw⟩, rfl⟩
 have qZ : π ⁻¹' decM q6 (zcy n H (univYF n F)) = zcS n z8 zc := by
  ext s
  have xX : s.1 < 2 ^ n := zZ s.1 s.2
  simp only [Set.mem_preimage, zcS, mem_decM, zcG hM,
   zcG zZ, z4 _ (π s).2, s.2, Bool.true_and,
   zcx]
  constructor
  ·rintro ⟨e, heH, h1, h2⟩
   change (zez n delVMask s.1).testBit e.1 = true at h1
   change (zez n delVMask s.1).testBit e.2 = true at h2
   rw [zeA xX, Bool.and_eq_true] at h1 h2
   have vn : forbAdded.any (undirEq e) = false := by
    rw [Bool.eq_false_iff]
    intro yc
    rw [List.any_eq_true] at yc
    obtain ⟨f, hfmem, hue⟩ := yc
    rw [zee] at hue
    have xd : f ∈ zc := by
     refine List.mem_filter.mpr ⟨List.mem_append_right _ hfmem, ?_⟩
     rcases hue with ⟨hu1, hu2⟩ | ⟨hu1, hu2⟩ <;>
      simp [← hu1, ← hu2, h1.2, h2.2]
    have hs2 := s.2
    rw [zcD, Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff] at hs2
    apply hs2.2
    rw [zcx]
    rcases hue with ⟨hu1, hu2⟩ | ⟨hu1, hu2⟩
    ·exact ⟨f, xd, hu1 ▸ h1.1, hu2 ▸ h2.1⟩
    ·exact ⟨f, xd, hu2 ▸ h2.1, hu1 ▸ h1.1⟩
   exact ⟨e, List.mem_filter.mpr ⟨heH, by simp [vn, h1.2, h2.2]⟩, h1.1, h2.1⟩
  ·rintro ⟨e, heEnd, h1, h2⟩
   obtain ⟨heH, hfilt⟩ := List.mem_filter.mp heEnd
   simp only [Bool.and_eq_true, Bool.not_eq_true'] at hfilt
   refine ⟨e, heH, ?_, ?_⟩
   ·change (zez n delVMask s.1).testBit e.1 = true
    rw [zeA xX, h1, hfilt.1.2]; rfl
   ·change (zez n delVMask s.1).testBit e.2 = true
    rw [zeA xX, h2, hfilt.2]; rfl
 have hr' := freeMap π zA qj
 rwa [qZ] at hr'
def zeC (qc : ℕ) : List ℕ → Bool
 | [] => true
 | a :: qa => qa.all (fun b => !Nat.beq (Nat.land (Nat.lor a b) qc) qc) &&
   zeC qc qa
theorem zeD {qc : ℕ} {l : List ℕ}
  (hok : zeC qc l = true) :
  ∀ a ∈ l, ∀ b ∈ l, a ≠ b → ((a ||| b) &&& qc) ≠ qc := by
 induction l with
 | nil => intro a ha; simp at ha
 | cons x qa ih =>
  simp only [zeC, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true',
   zet, land_eq, lor_eq] at hok
  obtain ⟨zi, zf⟩ := hok
  intro a ha b hb hab
  rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
  ·exact (hab rfl).elim
  ·exact zi b hb'
  ·rw [Nat.or_comm]; exact zi a ha'
  ·exact ih zf a ha' b hb' hab
theorem zeE {n : ℕ} {H F : List (ℕ × ℕ)} {pre : List ℕ} {g : ℕ}
  (hv : zcC n H F) (yM : H ≠ [])
  (qj : zdl (univYF n F) (rawYF n (univYF n F)) (zcy n H (univYF n F)) (pre ++ [g]))
  (qz : ∀ k' < (pre ++ [g]).length, ¬ zcT n H F k')
  {ops : List ℕ}
  (xB : ∀ x, MeetNat (univYF n F) (rawYF n (univYF n F) ++ pre) x →
   x ≠ 0 → x ≠ univYF n F → x &&& zcz H ≠ 0 → x ∈ ops) :
  let M := univYF n F
  let B := rawYF n M ++ pre
  let edgeTT := zcy n H M
  let md := zdb edgeTT B M
  md = edgeTT ∨
  ¬ (zeC (zcz H) (ops.filter (fun op => Nat.beq (Nat.land op (md ^^^ edgeTT)) 0)) = true) := by
 set M := univYF n F
 set B := rawYF n M ++ pre
 set edgeTT := zcy n H M
 set ep := zcz H
 set md := zdb edgeTT B M
 by_cases hmd : md = edgeTT
 ·exact Or.inl hmd
 right
 intro yl
 have u4 : isMeet M B edgeTT = false :=
  zdz qj qz (by simp)
 obtain ⟨a, b, hgab, hab, ha, hb, ha0, haM, haep, hb0, hbM, hbep⟩ :=
  zdK hv qj qz
 have uh : a ∈ ops := xB a ha ha0 haM haep
 have ui : b ∈ ops := xB b hb hb0 hbM hbep
 obtain ⟨_, _, hend⟩ := zdr.mp qj
 have xe : edgeTT ≠ 0 := by
  obtain ⟨e, _, heq⟩ := List.exists_cons_of_ne_nil yM
  intro h0
  have zK := zcO hv (show e ∈ H by rw [heq]; simp)
  rw [show zcy n H (univYF n F) = edgeTT from rfl, h0] at zK
  simp at zK
 have zo : zdb edgeTT (B ++ [g]) M = edgeTT := by
  have hm := hend.2
  unfold isMeet at hm
  have wv : Nat.beq edgeTT 0 = false := (zet _ _).mpr xe
  rw [wv] at hm
  exact Nat.eq_of_beq_eq_true hm
 have xR : zdb edgeTT (B ++ [g]) M =
   match Nat.beq (Nat.land edgeTT g) edgeTT with
   | true => md &&& g
   | false => md := by
  have va : ∀ (l₁ l₂ : List ℕ) (acc : ℕ),
    zdb edgeTT (l₁ ++ l₂) acc = zdb edgeTT l₂ (zdb edgeTT l₁ acc) := by
   intro l₁
   induction l₁ with
   | nil => intro _ _; rfl
   | cons x xs ih =>
    intro l₂ acc
    simp only [List.cons_append, zdb]
    cases Nat.beq (Nat.land edgeTT x) edgeTT <;> exact ih l₂ _
  rw [va B [g] M]
  simp only [zdb, md, land_eq]
 rw [xR] at zo
 have yG : edgeTT &&& g = edgeTT := by
  cases hbg : Nat.beq (Nat.land edgeTT g) edgeTT
  ·rw [hbg] at zo; exact (hmd zo).elim
  ·simpa [land_eq] using Nat.eq_of_beq_eq_true hbg
 have uC : md &&& g = edgeTT := by
  have hbg : Nat.beq (Nat.land edgeTT g) edgeTT = true := by simpa [land_eq] using yG
  rw [hbg] at zo
  exact zo
 have v6 : edgeTT &&& md = edgeTT :=
  zdf B (zcP n H F)
 have vh : g &&& (md ^^^ edgeTT) = 0 := by
  apply Nat.eq_of_testBit_eq; intro s
  have h1 := congrArg (fun z => z.testBit s) uC
  have h2 := congrArg (fun z => z.testBit s) v6
  simp only [Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit] at h1 h2 ⊢
  revert h1 h2
  cases md.testBit s <;> cases edgeTT.testBit s <;> cases g.testBit s <;> decide
 have wt : a &&& (md ^^^ edgeTT) = 0 := by
  apply Nat.eq_of_testBit_eq; intro s
  have h1 := congrArg (fun z => z.testBit s) vh
  simp only [hgab, Nat.testBit_and, Nat.testBit_or, Nat.zero_testBit] at h1 ⊢
  revert h1
  cases a.testBit s <;> cases b.testBit s <;> cases (md ^^^ edgeTT).testBit s <;> decide
 have wx : b &&& (md ^^^ edgeTT) = 0 := by
  apply Nat.eq_of_testBit_eq; intro s
  have h1 := congrArg (fun z => z.testBit s) vh
  simp only [hgab, Nat.testBit_and, Nat.testBit_or, Nat.zero_testBit] at h1 ⊢
  revert h1
  cases a.testBit s <;> cases b.testBit s <;> cases (md ^^^ edgeTT).testBit s <;> decide
 have vP : a ∈ ops.filter (fun op => Nat.beq (Nat.land op (md ^^^ edgeTT)) 0) :=
  List.mem_filter.mpr ⟨uh, by simp [wt]⟩
 have vQ : b ∈ ops.filter (fun op => Nat.beq (Nat.land op (md ^^^ edgeTT)) 0) :=
  List.mem_filter.mpr ⟨ui, by simp [wx]⟩
 have ti : (a ||| b) &&& ep = ep := by
  rw [← hgab]
  apply Nat.eq_of_testBit_eq; intro s
  rw [Nat.testBit_and]
  cases hep : ep.testBit s
  ·simp
  ·have hed : edgeTT.testBit s = true := by
    rw [zcJ, List.any_eq_true] at hep
    obtain ⟨e, heH, heq⟩ := hep
    rw [decide_eq_true_eq] at heq
    rw [← heq]; exact zcO hv heH
   have hgs : g.testBit s = true := by
    have := congrArg (fun z => z.testBit s) yG
    rw [Nat.testBit_and, hed, Bool.true_and] at this; exact this
   simp [hgs]
 exact zeD yl a vP b vQ hab ti
structure zeF where
 loss : ℕ
 steps : List zeu
def zeG (qh edgeTT : ℕ) (qk : List ℕ) (st : zeu) : Bool :=
 Nat.beq (Nat.land st.mc qh) st.mc &&
 qk.all (fun r => let r' := Nat.land r st.mc; Nat.beq r' 0 || st.rc.contains r') &&
 st.rc.all (fun r' => qk.any (fun r => Nat.beq r' (Nat.land r st.mc))) &&
 st.pv.all (fun pm =>
  Nat.beq (Nat.land pm qh) pm &&
  !Nat.beq (Nat.land pm edgeTT) 0 &&
  !Nat.beq (Nat.land pm edgeTT) pm &&
  !Nat.beq (Nat.land edgeTT st.mc) 0 &&
  qk.all (fun r => zej st.mc pm r))
def zeH (M edgeTT : ℕ) (raw : List ℕ) :
  List zeu → ℕ → List ℕ → Bool
 | [], qT, qK => Nat.beq M qT && decide (raw = qK)
 | st :: qa, qT, qK =>
  zeG M edgeTT raw st &&
  zeH st.mc edgeTT st.rc qa qT qK
def zeI (n : ℕ) (F forbAdded : List (ℕ × ℕ)) (delVMask : ℕ) : ℕ :=
 zct (2 ^ n) (fun s => (univYF n (F ++ forbAdded)).testBit s && Nat.beq (Nat.land s delVMask) 0)
def zeJ (H forbAdded : List (ℕ × ℕ)) (delVMask : ℕ) : List (ℕ × ℕ) :=
 H.filter (fun e => !forbAdded.any (undirEq e) && !delVMask.testBit e.1 && !delVMask.testBit e.2)
def zeK (F forbAdded : List (ℕ × ℕ)) (delVMask : ℕ) : List (ℕ × ℕ) :=
 (F ++ forbAdded).filter (fun e => !delVMask.testBit e.1 && !delVMask.testBit e.2)
def zeL (n : ℕ) (H F : List (ℕ × ℕ)) (cut : zeF)
  (delVMask : ℕ) (forbAdded : List (ℕ × ℕ)) (peels : List ℕ)
  (n_c : ℕ) (H_c F_c : List (ℕ × ℕ)) (f : List ℕ) : Bool :=
 let M := univYF n F
 let raw := rawYF n M
 let edgeTT := zcy n H M
 let qT := zeI n F forbAdded delVMask
 let z7 := match cut.steps.getLast? with | none => raw | some st => st.rc
 let z8 := zeJ H forbAdded delVMask
 let zc := zeK F forbAdded delVMask
 zeH M edgeTT raw cut.steps qT z7 &&
 decide (zcC n z8 zc) &&
 decide (1 ≤ z8.length) &&
 decide (H.length ≤ z8.length + cut.loss) &&
 zeh n z8 zc peels n_c H_c F_c f
theorem zeM {qh edgeTT : ℕ} {qk : List ℕ} {st : zeu}
  (hok : zeG qh edgeTT qk st = true) :
  zev qh edgeTT qk st ∧
  (∀ r' ∈ st.rc, ∃ r ∈ qk, r' = r &&& st.mc) := by
 unfold zeG at hok
 simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true, Bool.or_eq_true,
  Bool.not_eq_true', zep, zet, land_eq,
  List.contains_eq_mem, decide_eq_true_eq] at hok
 obtain ⟨⟨⟨hmc, qX⟩, hrc⟩, hpv⟩ := hok
 refine ⟨⟨hmc, qX, fun pm hpm => ?_⟩, hrc⟩
 obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hpv pm hpm
 exact ⟨h1, h2, h3, h4, h5⟩
theorem zeN {n : ℕ} {F : List (ℕ × ℕ)} {M edgeTT qT : ℕ}
  {raw qK : List ℕ} {steps : List zeu}
  (zS : ∀ r ∈ raw, r = 0 ∨ ∃ w < n, r = ttVarYF n w (univYF n F) &&& M)
  (hok : zeH M edgeTT raw steps qT qK = true) :
  zex M edgeTT raw steps qT qK ∧
  (∀ r ∈ qK, r = 0 ∨ ∃ w < n, r = ttVarYF n w (univYF n F) &&& qT) := by
 induction steps generalizing M raw with
 | nil =>
  simp only [zeH, Bool.and_eq_true, zep, decide_eq_true_eq] at hok
  rcases hok with ⟨rfl, rfl⟩
  exact ⟨⟨rfl, rfl⟩, zS⟩
 | cons st qa ih =>
  simp only [zeH, Bool.and_eq_true] at hok
  obtain ⟨hst, hrc_sub⟩ := zeM hok.1
  have yU : ∀ r' ∈ st.rc, r' = 0 ∨ ∃ w < n, r' = ttVarYF n w (univYF n F) &&& st.mc := by
   intro r' hr'
   obtain ⟨r, hr, rfl⟩ := hrc_sub r' hr'
   rcases zS r hr with rfl | ⟨w, hw, rfl⟩
   ·exact Or.inl (by simp)
   ·refine Or.inr ⟨w, hw, ?_⟩
    rw [Nat.and_assoc, Nat.and_comm M st.mc, hst.1]
  obtain ⟨hchain, hend_inv⟩ := ih yU hok.2
  exact ⟨⟨hst, hchain⟩, hend_inv⟩
theorem zeO {n : ℕ} {H F : List (ℕ × ℕ)} {cut : zeF}
  {delVMask : ℕ} {forbAdded : List (ℕ × ℕ)} {peels : List ℕ}
  {n_c : ℕ} {H_c F_c : List (ℕ × ℕ)} {f : List ℕ}
  (zw : zeL n H F cut delVMask forbAdded peels n_c H_c F_c f = true)
  (wB : zcU n_c H_c F_c (H_c.length - 1))
  {pre suf : List ℕ}
  (qj : zdl (univYF n F) (rawYF n (univYF n F)) (zcy n H (univYF n F)) (pre ++ suf))
  (qe : (pre ++ suf).length + 2 ≤ H.length)
  (u1 : cut.loss ≤ zew cut.steps pre) :
  False := by
 unfold zeL at zw
 dsimp only at zw
 simp only [Bool.and_eq_true, decide_eq_true_eq] at zw
 obtain ⟨⟨⟨⟨hchain_ok, hv_end⟩, hne_end⟩, hloss_le⟩, hpeel_ok⟩ := zw
 set M := univYF n F
 set raw := rawYF n M
 set edgeTT := zcy n H M
 set qT := zeI n F forbAdded delVMask
 set z7 := match cut.steps.getLast? with | none => raw | some st => st.rc
 have hM : ∀ s, M.testBit s = true → s < 2 ^ n := fun _ => zcE
 have zS : ∀ r ∈ raw, r = 0 ∨ ∃ w < n, r = ttVarYF n w M &&& M := by
  intro r hr
  simp only [raw, rawYF, List.mem_map, List.mem_range] at hr
  obtain ⟨w, hw, rfl⟩ := hr
  exact Or.inr ⟨w, hw, (zcQ hM).symm⟩
 obtain ⟨hchain, hrc_inv⟩ := zeN zS hchain_ok
 obtain ⟨hvp, yv⟩ := zdr.mp qj
 have xl : Run (decM M '' { x | x ∈ raw ++ pre }) suf.length (decM M edgeTT) :=
  zdp yv
 obtain ⟨zD, hk_budget, hrun_end⟩ := zey cut.steps hchain hvp xl
 have zR : ∀ s, qT.testBit s = true ↔
   (univYF n (F ++ forbAdded)).testBit s = true ∧ s &&& delVMask = 0 := by
  intro s
  simp only [qT, zeI, zcv, Bool.and_eq_true, decide_eq_true_eq,
   zep, land_eq]
  exact ⟨fun ⟨_, h1, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨zcE h1, h1, h2⟩⟩
 have vi : zcT n (zeJ H forbAdded delVMask) (zeK F forbAdded delVMask) zD :=
  zeB zR hrc_inv hrun_end
 have u2 : (zeJ H forbAdded delVMask).length - 1 ≤ zD :=
  zei hv_end hpeel_ok wB zD vi
 simp only [List.length_append] at qe
 omega
def zeP (n : ℕ) (H : List (ℕ × ℕ)) (x : Fin n → Bool) : Bool :=
 H.any (fun e => if h : e.1 < n ∧ e.2 < n then x ⟨e.1, h.1⟩ && x ⟨e.2, h.2⟩ else false)
theorem zeQ {n lb : ℕ} {H : List (ℕ × ℕ)} {f : (Fin n → Bool) → Bool}
  (hH : ∀ e ∈ H, e.1 < n ∧ e.2 < n)
  (hf : ∀ x : Fin n → Bool, f x = zeP n H x)
  (hlb : zcU n H [] lb)
  (C : Circuit) (hc : Monotone2 C)
  (he : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x) :
  lb ≤ zc5 C.gates := by
 have he' : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
   ∃ e ∈ H, ∃ (h1 : e.1 < n) (h2 : e.2 < n), x ⟨e.1, h1⟩ = true ∧ x ⟨e.2, h2⟩ = true := by
  intro x
  rw [he x, hf x, zeP, List.any_eq_true]
  constructor
  ·rintro ⟨e, heH, zl⟩
   obtain ⟨h1, h2⟩ := hH e heH
   simp only [h1, h2, and_self, ↓reduceDIte, Bool.and_eq_true] at zl
   exact ⟨e, heH, h1, h2, zl.1, zl.2⟩
  ·rintro ⟨e, heH, h1, h2, hx1, hx2⟩
   refine ⟨e, heH, ?_⟩
   simp only [h1, h2, and_self, ↓reduceDIte, Bool.and_eq_true]
   exact ⟨hx1, hx2⟩
 obtain ⟨k, hk, qj⟩ := zda H C hc he' hH
 exact (hlb k qj).trans hk
def zeR : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (3, 4), (3, 6), (5, 6)]
def g28_fn (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6) || (x 5 && x 6)
theorem zeS : ∀ x : Fin 7 → Bool, g28_fn x = zeP 7 zeR x := by
 intro x; simp [g28_fn, zeP, zeR, Bool.or_assoc]
def zeT : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (2, 5), (3, 6), (4, 6), (5, 6)]
def g29_fn (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6) || (x 5 && x 6)
theorem zeU : ∀ x : Fin 7 → Bool, g29_fn x = zeP 7 zeT x := by
 intro x; simp [g29_fn, zeP, zeT, Bool.or_assoc]
structure zeV where
 n     : Nat
 edges : List (Nat × Nat)
 forb  : List (Nat × Nat)
structure zeW where
 delVMask  : Nat
 forbAdded : List (Nat × Nat)
 peels     : List Nat
 childId   : Nat
 embed     : List Nat
structure zeX where
 graphIdx : Nat
 n        : Nat
 edges    : List (Nat × Nat)
 bound    : Nat
 coreId   : Nat
 peels    : List Nat
 embed    : List Nat
structure zeY where
 mc        : Nat
 sb        : List Nat
 validPv   : List Nat
 tailBonus : Nat
structure zeZ where
 need  : Nat
 steps : List zeY
inductive ze0 where
 | v : Nat → List Nat → ze0
 | e : List (Nat × Nat) → ze0
mutual
 inductive CertNode where
  | term : CertNode
  | branch : List Nat → List (List Nat) → CertList → CertNode
 inductive CertList where
  | nil : CertList
  | cons : Nat → CertNode → CertList → CertList
end
def ze1 : Nat := 0xffffffffffffffffffffffffffffffff
def ze2 : Nat → Nat
 | 0 => 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
 | 1 => 0xcccccccccccccccccccccccccccccccc
 | 2 => 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
 | 3 => 0xff00ff00ff00ff00ff00ff00ff00ff00
 | 4 => 0xffff0000ffff0000ffff0000ffff0000
 | 5 => 0xffffffff00000000ffffffff00000000
 | 6 => 0xffffffffffffffff0000000000000000
 | _ => 0
def ze3 (v : Nat) : Nat := Nat.xor ze1 (ze2 v)
def ze4 (acc : Nat) : List (Nat × Nat) → Nat
 | [] => acc
 | (u, v) :: qa =>
  ze4 (Nat.land acc (Nat.xor ze1 (Nat.land (ze2 u) (ze2 v)))) qa
def ze5 (maskYF : Nat) : Nat → Nat → List Nat
 | _, 0 => []
 | v, k + 1 => Nat.land maskYF (ze2 v) :: ze5 maskYF (v + 1) k
def ze6 (n maskYF : Nat) : List Nat := ze5 maskYF 0 n
def ze7 (maskYF : Nat) : List (Nat × Nat) → List Nat
 | [] => []
 | (u, v) :: qa => Nat.land maskYF (Nat.land (ze2 u) (ze2 v)) :: ze7 maskYF qa
def ze8 (n : Nat) (edges : List (Nat × Nat)) (maskYF : Nat) : List Nat :=
 maskYF :: ze6 n maskYF ++ ze7 maskYF edges
def ze9 (mc : Nat) : List Nat → List Nat
 | [] => []
 | r :: qa =>
  let r' := Nat.land r mc
  match Nat.beq r' 0 with
  | true => ze9 mc qa
  | false => r' :: ze9 mc qa
def chkMkPv (v : Nat) : List Nat → List Nat
 | [] => []
 | s :: qa =>
  Nat.lor (Nat.pow 2 s) (Nat.pow 2 (Nat.lor s (Nat.pow 2 v))) :: chkMkPv v qa
def zfa (wl : Nat) (wn : List Nat) : List ze0 → List zeu
 | [] => []
 | .v v ps :: qa =>
  let mc := Nat.land wl (ze3 v)
  let rc := ze9 mc wn
  {mc := mc, rc := rc, pv := chkMkPv v ps } :: zfa mc rc qa
 | .e es :: qa =>
  let mc := ze4 wl es
  let rc := ze9 mc wn
  {mc := mc, rc := rc, pv := [] } :: zfa mc rc qa
def zfb (maskYF : Nat) (raw : List Nat) : List (Nat × List ze0) → List zeF
 | [] => []
 | (loss, specs) :: qa =>
  {loss := loss, steps := zfa maskYF raw specs } :: zfb maskYF raw qa
def zfc : List Nat → List Nat → List Nat
 | [], ys => ys
 | x :: xs, ys => x :: zfc xs ys
def zfd : List (List Nat) → List Nat
 | [] => []
 | c :: qa => zfc c (zfd qa)
def zfe (x : Nat) : List Nat → Bool
 | [] => false
 | y :: qa =>
  match Nat.beq x y with
  | true => true
  | false => zfe x qa
def zff (target acc : Nat) : List Nat → Bool
 | [] => Nat.beq acc target
 | b :: qa =>
  match Nat.beq (Nat.land target b) target with
  | true =>
   let zJ := Nat.land acc b
   match Nat.beq zJ target with
   | true => true
   | false => zff target zJ qa
  | false => zff target acc qa
def zfg (zF : Nat) (xK : List Nat) (target : Nat) : Bool :=
 match Nat.beq target 0 with
 | true => true
 | false => zff target zF xK
def zfh (eg g acc : Nat) : List Nat → Bool
 | [] => Nat.beq (Nat.land acc g) acc
 | b :: qa =>
  match Nat.beq (Nat.land eg b) eg with
  | true =>
   let zJ := Nat.land acc b
   match Nat.beq (Nat.land zJ g) zJ with
   | true => true
   | false => zfh eg g zJ qa
  | false => zfh eg g acc qa
def zfi (mc pm h : Nat) : Bool :=
 let x := Nat.land h pm
 match Nat.beq x 0 with
 | true => true
 | false =>
  match Nat.beq x pm with
  | true => true
  | false => Nat.beq (Nat.land h mc) 0
def zfj (mc pm : Nat) : List Nat → Bool
 | [] => true
 | h :: qa =>
  match zfi mc pm h with
  | true => zfj mc pm qa
  | false => false
def zfk (mc : Nat) (act : List Nat) : List Nat → List Nat
 | [] => []
 | pm :: qa =>
  match zfj mc pm act with
  | true => pm :: zfk mc act qa
  | false => zfk mc act qa
def zfl (mc g : Nat) : List Nat → Bool
 | [] => false
 | pm :: qa =>
  match zfi mc pm g with
  | true => true
  | false => zfl mc g qa
def zfm (mc : Nat) : List Nat → List Nat → Nat → List Nat → (List Nat × Nat × List Nat)
 | [], sb, sv, qg => (sb, sv, qg.reverse)
 | h :: qa, sb, sv, qg =>
  let rh := Nat.land h mc
  match zfg mc sb rh with
  | true => zfm mc qa sb (sv + 1) qg
  | false => zfm mc qa (rh :: sb) sv (rh :: qg)
def zfn : List zeu → List Nat → Nat → (Nat × Nat × List zeY)
 | [], _, sv => (sv, 0, [])
 | st :: qa, act, sv =>
  let vp := zfk st.mc act st.pv
  let (sb, sv', act') := zfm st.mc act st.rc sv []
  let (totSv, tailB, restStates) := zfn qa act' sv'
  let myB := match vp with | [] => 0 | _ :: _ => 1
  (totSv, myB + tailB, { mc := st.mc, sb := sb, validPv := vp, tailBonus := tailB } :: restStates)
def zfo (cut : zeF) (gs : List Nat) : zeZ :=
 let (totSv, _, sts) := zfn cut.steps gs 0
 {need := Nat.sub cut.loss totSv, steps := sts }
def zfp (g need : Nat) : Nat → List zeY → Bool
 | _, [] => Nat.beq need 0
 | 0, st :: _ =>
  let rg := Nat.land g st.mc
  match zfg st.mc st.sb rg with
  | false => false
  | true =>
   match Nat.ble need (1 + st.tailBonus) with
   | true => true
   | false =>
    match Nat.ble need (2 + st.tailBonus) with
    | true => zfl st.mc g st.validPv
    | false => false
 | s' + 1, st :: qa =>
  let wm := match st.validPv with
   | [] => need
   | _ :: _ =>
    match zfl st.mc g st.validPv with
    | true => Nat.sub need 1
    | false => need
  match Nat.beq wm 0 with
  | true => true
  | false => zfp (Nat.land g st.mc) wm s' qa
def zfq (cs : zeZ) (qt g : Nat) : Bool :=
 match Nat.beq cs.need 0 with
 | true => true
 | false => zfp g cs.need qt cs.steps
def zfr (xs : List zeZ) : Nat → zeZ
 | 0 => match xs with | c :: _ => c | [] => { need := 1, steps := [] }
 | k + 1 => match xs with | _ :: qa => zfr qa k | [] => { need := 1, steps := [] }
def zfs (f acc : Nat) : List Nat → Nat
 | [] => acc
 | m2 :: qa =>
  match Nat.beq f 0 with
  | true => acc
  | false =>
   let zJ := match Nat.beq (Nat.land f 1) 1 with | true => Nat.lor acc m2 | false => acc
   zfs (Nat.div f 2) zJ qa
def zft (tbl : List Nat) (f : Nat) : Nat :=
 zfs f 0 tbl
def zfu (f : Nat) : List (List Nat) → List Nat
 | [] => []
 | tbl :: qa => zft tbl f :: zfu f qa
def zfv (g : Nat) : List Nat → List Nat → Bool
 | p :: ps, q :: qs =>
  match Nat.blt (Nat.lor p q) g with
  | true => true
  | false => zfv g ps qs
 | _, _ => false
def zfw (g : Nat) : List (List Nat) → List (List Nat)
 | [] => []
 | tbl :: qa =>
  match Nat.beq (zft tbl g) g with
  | true => tbl :: zfw g qa
  | false => zfw g qa
def zfx (cuts : List zeF) : Nat → zeF
 | 0 => match cuts with | c :: _ => c | [] => { loss := 1, steps := [] }
 | k + 1 => match cuts with | _ :: qa => zfx qa k | [] => { loss := 1, steps := [] }
def zfy (cuts : List zeF) (gs : List Nat) : List Nat → List zeZ
 | [] => []
 | ci :: qa => zfo (zfx cuts ci) gs :: zfy cuts gs qa
def zfz (g : Nat) : List Nat → List Nat → List Nat
 | [], acc => acc
 | x :: qa, acc => zfz g qa (Nat.land x g :: acc)
def zfA (maskYF qc gi qw : Nat) : List Nat → List Nat → List (Nat × Nat × Nat) → (List Nat × List (Nat × Nat × Nat))
 | [], qA, acc => (qA, acc)
 | mt :: qa, qA, acc =>
  let op := Nat.land mt gi
  match Nat.beq op 0 with
  | true => zfA maskYF qc gi qw qa qA acc
  | false =>
   match Nat.beq op maskYF with
   | true => zfA maskYF qc gi qw qa qA acc
   | false =>
    let eg := Nat.land op qc
    match Nat.beq eg 0 with
    | true => zfA maskYF qc gi qw qa qA acc
    | false =>
     match zfe op qA with
     | true => zfA maskYF qc gi qw qa qA acc
     | false => zfA maskYF qc gi qw qa (op :: qA) ((op, eg, qw) :: acc)
def zfB (maskYF qc qw : Nat) (masksTT : List Nat) : List Nat → List Nat → List (Nat × Nat × Nat) → (List Nat × List (Nat × Nat × Nat))
 | [], qA, acc => (qA, acc)
 | gi :: qa, qA, acc =>
  let (seen', zJ) := zfA maskYF qc gi qw masksTT qA acc
  zfB maskYF qc qw masksTT qa seen' zJ
def zfC (maskYF qc : Nat) (masksTT : List Nat) (qw : Nat)
  (zy qA : List Nat) (acc : List (Nat × Nat × Nat)) : List Nat → List (Nat × Nat × Nat)
 | [] => acc
 | g :: qa =>
  let qB := zfz g zy []
  let (seen', zJ) := zfB maskYF qc qw masksTT qB qA acc
  zfC maskYF qc masksTT (qw + 1) (qB ++ zy) seen' zJ qa
def zfD (maskYF qc : Nat) (masksTT gs : List Nat) : List (Nat × Nat × Nat) :=
 let (seen0, acc0) := zfA maskYF qc maskYF 0 masksTT [] []
 zfC maskYF qc masksTT 1 [maskYF] seen0 acc0 gs
def zfE (a b : Nat) : Nat :=
 match Nat.blt a b with | true => b | false => a
def zfF : List Nat → List Nat
 | [] => [0]
 | g :: qa =>
  match zfF qa with
  | [] => [g, 0]
  | m :: ms => zfE g m :: m :: ms
def zfG (xs : List Nat) : Nat → Nat
 | 0 => match xs with | x :: _ => x | [] => 0
 | k + 1 => match xs with | _ :: qa => zfG qa k | [] => 0
def zfH (maskYF : Nat) (b : List Nat) (qf : List zeZ) (qv : List Nat)
  (eg g w : Nat) : Bool :=
 match w with
 | 0 => zfe g qv
 | 1 => zfh eg g maskYF b
 | 2 => false
 | w3 + 3 => zfq (zfr qf (Nat.div w3 8)) (Nat.land w3 7) g
def zfI (maskYF : Nat) (b : List Nat) (qf : List zeZ)
  (qv : List Nat) (oi egi lim : Nat) : List (Nat × Nat × Nat) → List Nat → Option (List Nat)
 | [], qF => some qF
 | (oj, egj, _) :: qa, qF =>
  let eij := Nat.land egi egj
  match Nat.beq eij egi with
  | true => zfI maskYF b qf qv oi egi lim qa qF
  | false =>
   match Nat.beq eij egj with
   | true => zfI maskYF b qf qv oi egi lim qa qF
   | false =>
    let g := Nat.lor oi oj
    let xI := match Nat.beq lim 0 with | true => false | false => Nat.blt g lim
    match xI with
    | true => zfI maskYF b qf qv oi egi lim qa qF
    | false =>
     match qF with
     | [] => none
     | w :: ws =>
      match zfH maskYF b qf qv (Nat.lor egi egj) g w with
      | true => zfI maskYF b qf qv oi egi lim qa ws
      | false => none
def zfJ (maskYF : Nat) (b : List Nat) (qf : List zeZ)
  (qv zL : List Nat) : List (Nat × Nat × Nat) → List Nat → Bool
 | [], _ => true
 | (oi, egi, bi) :: qa, qF =>
  let lim := zfG zL bi
  match zfI maskYF b qf qv oi egi lim qa qF with
  | some zV => zfJ maskYF b qf qv zL qa zV
  | none => false
def zfK (zg : List (List Nat)) : List (Nat × Nat × Nat) → List (Nat × Nat × Nat × List Nat)
 | [] => []
 | (op, eg, bi) :: qa => (op, eg, bi, zfu op zg) :: zfK zg qa
def zfL (maskYF : Nat) (b : List Nat) (qf : List zeZ) (qv : List Nat)
  (eg g : Nat) (pi pj : List Nat) (w : Nat) : Bool :=
 match w with
 | 0 => zfe g qv
 | 1 => zfh eg g maskYF b
 | 2 => zfv g pi pj
 | w3 + 3 => zfq (zfr qf (Nat.div w3 8)) (Nat.land w3 7) g
def zfM (maskYF : Nat) (b : List Nat) (qf : List zeZ)
  (qv : List Nat) (oi egi lim : Nat) (pi : List Nat) : List (Nat × Nat × Nat × List Nat) → List Nat → Option (List Nat)
 | [], qF => some qF
 | (oj, egj, _, pj) :: qa, qF =>
  let eij := Nat.land egi egj
  match Nat.beq eij egi with
  | true => zfM maskYF b qf qv oi egi lim pi qa qF
  | false =>
   match Nat.beq eij egj with
   | true => zfM maskYF b qf qv oi egi lim pi qa qF
   | false =>
    let g := Nat.lor oi oj
    let xI := match Nat.beq lim 0 with | true => false | false => Nat.blt g lim
    match xI with
    | true => zfM maskYF b qf qv oi egi lim pi qa qF
    | false =>
     match qF with
     | [] => none
     | w :: ws =>
      match zfL maskYF b qf qv (Nat.lor egi egj) g pi pj w with
      | true => zfM maskYF b qf qv oi egi lim pi qa ws
      | false => none
def zfN (maskYF : Nat) (b : List Nat) (qf : List zeZ)
  (qv zL : List Nat) : List (Nat × Nat × Nat × List Nat) → List Nat → Bool
 | [], _ => true
 | (oi, egi, bi, pi) :: qa, qF =>
  let lim := zfG zL bi
  match zfM maskYF b qf qv oi egi lim pi qa qF with
  | some zV => zfN maskYF b qf qv zL qa zV
  | none => false
def zfO : CertList → List Nat
 | .nil => []
 | .cons g _ qa => g :: zfO qa
def zfP (edgeTT acc : Nat) : List Nat → Nat
 | [] => acc
 | x :: qa =>
  match Nat.beq (Nat.land edgeTT x) edgeTT with
  | true => zfP edgeTT (Nat.land acc x) qa
  | false => zfP edgeTT acc qa
def zfQ (bad : Nat) : List (Nat × Nat × Nat) → List Nat
 | [] => []
 | (op, _, _) :: qa =>
  match Nat.beq (Nat.land op bad) 0 with
  | true => op :: zfQ bad qa
  | false => zfQ bad qa
def zfR (qc a : Nat) : List Nat → Bool
 | [] => true
 | b :: qa =>
  match Nat.beq (Nat.land (Nat.lor a b) qc) qc with
  | true => false
  | false => zfR qc a qa
def zfS (qc : Nat) : List Nat → Bool
 | [] => true
 | a :: qa =>
  match zfR qc a qa with
  | true => zfS qc qa
  | false => false
def zfT (maskYF qc edgeTT : Nat) (raw masksTT gs : List Nat) : Bool :=
 let b := raw ++ gs
 let md := zfP edgeTT maskYF b
 match Nat.beq md edgeTT with
 | true => false
 | false =>
  let bad := Nat.xor md edgeTT
  let ops := zfD maskYF qc masksTT gs
  let yL := zfQ bad ops
  zfS qc yL
def zfU (maskYF qc edgeTT : Nat) (raw masksTT : List Nat) (cuts : List zeF)
  (gs : List Nat) (zg : List (List Nat)) (zM qF qv : List Nat) : Bool :=
 let b := raw ++ gs
 match zfg maskYF b edgeTT with
 | true => false
 | false =>
  let qf := zfy cuts gs zM
  let ops := zfD maskYF qc masksTT gs
  let zL := zfF gs
  match zg with
  | [] => zfJ maskYF b qf qv zL ops qF
  | _ :: _ =>
   let tH := zfK zg ops
   zfN maskYF b qf qv zL tH qF
def zfV (uX : List Nat) : Nat → List Nat
 | 0 => [0]
 | k + 1 =>
  let uZ := zfV uX k
  let bit := Nat.pow 2 (zfG uX k)
  uZ ++ uZ.map (fun s => Nat.lor s bit)
def zfW (n : Nat) (uY : List (List Nat)) : List (List Nat) :=
 uY.map (fun p => zfV p n)
def zfX (q7 : List (List Nat)) : List (List Nat) :=
 q7.map (fun tbl => tbl.map (fun s => Nat.pow 2 s))
mutual
 def chkCheckNode (maskYF qc edgeTT : Nat) (raw masksTT : List Nat) (cuts : List zeF)
   (gs : List Nat) (zg : List (List Nat)) : CertNode → Bool
  | .term => zfT maskYF qc edgeTT raw masksTT gs
  | .branch zM witsChunks children =>
   match zfU maskYF qc edgeTT raw masksTT cuts gs zg zM (zfd witsChunks) (zfO children) with
   | true => chkCheckChildren maskYF qc edgeTT raw masksTT cuts gs zg children
   | false => false
 def chkCheckChildren (maskYF qc edgeTT : Nat) (raw masksTT : List Nat) (cuts : List zeF)
   (gs : List Nat) (zg : List (List Nat)) : CertList → Bool
  | .nil => true
  | .cons g ch qa =>
   match chkCheckNode maskYF qc edgeTT raw masksTT cuts (gs ++ [g]) (zfw g zg) ch with
   | true => chkCheckChildren maskYF qc edgeTT raw masksTT cuts gs zg qa
   | false => false
end
mutual
 def certDepthOk (vM d : ℕ) : CertNode → Bool
  | .term => Nat.ble vM d
  | .branch _ _ ch => certListDepthOk vM (d + 1) ch
 def certListDepthOk (vM d : ℕ) : CertList → Bool
  | .nil => true
  | .cons _ ch qa => certDepthOk vM d ch && certListDepthOk vM d qa
end
theorem zfY (x : ℕ) (l : List ℕ) : zfe x l = true ↔ x ∈ l := by
 induction l with
 | nil => simp [zfe]
 | cons y qa ih =>
  simp only [zfe, List.mem_cons]
  cases h : Nat.beq x y
  ·simp [ih, (zet x y).mp h]
  ·simp [Nat.eq_of_beq_eq_true h]
theorem zfZ (target acc : ℕ) (bs : List ℕ) (qu : target &&& acc = target) :
  zff target acc bs = Nat.beq (zdb target bs acc) target := by
 induction bs generalizing acc with
 | nil => rfl
 | cons b qa ih =>
  simp only [zff, zdb]
  cases hb : Nat.beq (Nat.land target b) target
  ·exact ih acc qu
  ·have hb' : target &&& b = target := by simpa [land_eq] using Nat.eq_of_beq_eq_true hb
   have wj : target &&& (acc &&& b) = target := by rw [← Nat.and_assoc, qu, hb']
   dsimp only
   cases heq : Nat.beq (Nat.land acc b) target
   ·exact ih (Nat.land acc b) wj
   ·have y7 : acc &&& b = target := by simpa [land_eq] using Nat.eq_of_beq_eq_true heq
    have h1 : zdb target qa (acc &&& b) &&& target = zdb target qa (acc &&& b) := by
     simpa [y7] using zdd (target := target) qa (acc &&& b)
    have h2 : target &&& zdb target qa (acc &&& b) = target :=
     zdf qa wj
    have h3 : zdb target qa (acc &&& b) = target := by
     rw [← h1, Nat.and_comm, h2]
    simp [h3]
theorem zf0 {M t : ℕ} (B : List ℕ) (ht : t &&& M = t) :
  zfg M B t = isMeet M B t := by
 unfold zfg isMeet
 cases Nat.beq t 0
 ·exact zfZ t M B ht
 ·rfl
theorem zf1 (eg g acc : ℕ) (bs : List ℕ)
  (hok : zfh eg g acc bs = true) :
  zdb eg bs acc &&& g = zdb eg bs acc := by
 induction bs generalizing acc with
 | nil =>
  simpa [zfh, zdb, land_eq] using Nat.eq_of_beq_eq_true hok
 | cons b qa ih =>
  simp only [zfh, zdb] at hok ⊢
  cases hb : Nat.beq (Nat.land eg b) eg
  ·rw [hb] at hok; exact ih acc hok
  ·rw [hb] at hok
   dsimp only at hok
   cases h1 : Nat.beq (Nat.land (Nat.land acc b) g) (Nat.land acc b)
   ·rw [h1] at hok; exact ih (Nat.land acc b) hok
   ·have hag : (acc &&& b) &&& g = acc &&& b := by
     simpa [land_eq] using Nat.eq_of_beq_eq_true h1
    have qu := zdd (target := eg) qa (acc &&& b)
    apply Nat.eq_of_testBit_eq; intro s
    have ha1 := congrArg (fun z => z.testBit s) qu
    have ha2 := congrArg (fun z => z.testBit s) hag
    simp only [land_eq, Nat.testBit_and] at ha1 ha2 ⊢
    revert ha1 ha2
    cases (zdb eg qa (acc &&& b)).testBit s <;>
     cases acc.testBit s <;> cases b.testBit s <;> cases g.testBit s <;> decide
theorem zf2 (mc pm h : ℕ) : zfi mc pm h = zej mc pm h := rfl
theorem zf3 (mc pm : ℕ) (act : List ℕ) :
  zfj mc pm act = true ↔ act.all (zej mc pm) = true := by
 induction act with
 | nil => simp [zfj]
 | cons h qa ih =>
  simp only [zfj, List.all_cons, zf2]
  cases zej mc pm h <;> simp [ih]
theorem zf4 (mc : ℕ) (act pv : List ℕ) (pm : ℕ) :
  pm ∈ zfk mc act pv ↔ pm ∈ pv ∧ act.all (zej mc pm) = true := by
 induction pv with
 | nil => simp [zfk]
 | cons p qa ih =>
  simp only [zfk, List.mem_cons]
  cases hp : zfj mc p act
  ·have hp' : ¬ act.all (zej mc p) = true := by
    rw [← zf3]; simp [hp]
   simp only [ih]
   constructor
   ·rintro ⟨qo, hall⟩; exact ⟨Or.inr qo, hall⟩
   ·rintro ⟨rfl | qo, hall⟩
    ·exact (hp' hall).elim
    ·exact ⟨qo, hall⟩
  ·have hp' : act.all (zej mc p) = true := (zf3 mc p act).mp hp
   simp only [List.mem_cons, ih]
   constructor
   ·rintro (rfl | ⟨qo, hall⟩)
    ·exact ⟨Or.inl rfl, hp'⟩
    ·exact ⟨Or.inr qo, hall⟩
   ·rintro ⟨rfl | qo, hall⟩
    ·exact Or.inl rfl
    ·exact Or.inr ⟨qo, hall⟩
theorem zf5 (mc g : ℕ) (vp : List ℕ) :
  zfl mc g vp = true ↔ ∃ pm ∈ vp, zej mc pm g = true := by
 induction vp with
 | nil => simp [zfl]
 | cons pm qa ih =>
  simp only [zfl, zf2, List.mem_cons]
  cases hp : zej mc pm g
  ·simp only [ih]
   constructor
   ·rintro ⟨p, qo, hok⟩; exact ⟨p, Or.inr qo, hok⟩
   ·rintro ⟨p, rfl | qo, hok⟩
    ·simp [hp] at hok
    ·exact ⟨p, qo, hok⟩
  ·simp only [true_iff]; exact ⟨pm, Or.inl rfl, hp⟩
theorem zf6 (mc g : ℕ) (act pv : List ℕ) :
  zfl mc g (zfk mc act pv) = true ↔
   pv.any (fun pm => (act ++ [g]).all (zej mc pm)) = true := by
 rw [zf5, List.any_eq_true]
 constructor
 ·rintro ⟨pm, qo, hg⟩
  obtain ⟨hpv, hact⟩ := (zf4 mc act pv pm).mp qo
  exact ⟨pm, hpv, by simp [hact, hg]⟩
 ·rintro ⟨pm, hpv, hall⟩
  simp only [List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hall
  exact ⟨pm, (zf4 mc act pv pm).mpr ⟨hpv, hall.1⟩, hall.2⟩
theorem zf7 (mc : ℕ) (act sb : List ℕ) (sv : ℕ) (qg : List ℕ) :
  zfm mc act sb sv qg =
   let r := zek.go mc act sb qg sv
   (r.1, r.2.2, r.2.1) := by
 induction act generalizing sb sv qg with
 | nil => rfl
 | cons h qa ih =>
  simp only [zfm, zek.go]
  have hrh : (Nat.land h mc) &&& mc = Nat.land h mc := by
   apply Nat.eq_of_testBit_eq; intro s; simp [Nat.testBit_and]
  rw [zf0 sb hrh]
  cases isMeet mc sb (Nat.land h mc)
  ·exact ih (Nat.land h mc :: sb) sv (Nat.land h mc :: qg)
  ·exact ih sb (sv + 1) qg
theorem zf8 (mc : ℕ) (act sb qg : List ℕ) (sv k : ℕ) :
  zek.go mc act sb qg (sv + k) =
   let r := zek.go mc act sb qg sv
   (r.1, r.2.1, r.2.2 + k) := by
 induction act generalizing sb qg sv with
 | nil => rfl
 | cons h qa ih =>
  simp only [zek.go]
  cases isMeet mc sb (Nat.land h mc)
  ·exact ih (Nat.land h mc :: sb) (Nat.land h mc :: qg) sv
  ·rw [show sv + k + 1 = (sv + 1) + k by omega]
   exact ih sb qg (sv + 1)
theorem zf9 (mc : ℕ) (act sb qg : List ℕ) (sv g : ℕ) :
  zek.go mc (act ++ [g]) sb qg sv =
   let r := zek.go mc act sb qg sv
   let rg := Nat.land g mc
   match isMeet mc r.1 rg with
   | true => (r.1, r.2.1, r.2.2 + 1)
   | false => (rg :: r.1, r.2.1 ++ [rg], r.2.2) := by
 induction act generalizing sb qg sv with
 | nil =>
  simp only [List.nil_append, zek.go]
  cases isMeet mc sb (Nat.land g mc) <;> simp
 | cons h qa ih =>
  simp only [List.cons_append, zek.go]
  cases isMeet mc sb (Nat.land h mc)
  ·exact ih (Nat.land h mc :: sb) (Nat.land h mc :: qg) sv
  ·exact ih sb qg (sv + 1)
theorem zga (steps : List zeu) (act : List ℕ) (sv k : ℕ) :
  zfn steps act (sv + k) =
   let r := zfn steps act sv
   (r.1 + k, r.2.1, r.2.2) := by
 induction steps generalizing act sv with
 | nil => rfl
 | cons st qa ih =>
  simp only [zfn, zf7]
  have h1 := zf8 st.mc act st.rc [] sv k
  simp only [h1]
  rw [ih (zek.go st.mc act st.rc [] sv).2.1 (zek.go st.mc act st.rc [] sv).2.2]
theorem zgb (steps : List zeu) (act : List ℕ) :
  zew steps act = (zfn steps act 0).1 + (zfn steps act 0).2.1 := by
 induction steps generalizing act with
 | nil => simp [zew, zfn]
 | cons st qa ih =>
  simp only [zew, zfn, zf7]
  set r := zek.go st.mc act st.rc [] 0
  have ze : (zfn qa r.2.1 r.2.2).1 = (zfn qa r.2.1 0).1 + r.2.2 ∧
    (zfn qa r.2.1 r.2.2).2.1 = (zfn qa r.2.1 0).2.1 := by
   have h := zga qa r.2.1 0 r.2.2
   simp only [zero_add] at h
   rw [h]; exact ⟨rfl, rfl⟩
  have tv : (if st.pv.any (fun pm => act.all (zej st.mc pm)) then 1 else 0) =
    match zfk st.mc act st.pv with | [] => 0 | _ :: _ => 1 := by
   cases hfp : zfk st.mc act st.pv
   ·simp only [ite_eq_right_iff, Nat.one_ne_zero]
    intro yc
    rw [List.any_eq_true] at yc
    obtain ⟨pm, hpm, hall⟩ := yc
    have qo : pm ∈ zfk st.mc act st.pv := (zf4 st.mc act st.pv pm).mpr ⟨hpm, hall⟩
    rw [hfp] at qo; simp at qo
   ·rename_i pm _
    have qo : pm ∈ zfk st.mc act st.pv := by rw [hfp]; simp
    obtain ⟨hpv, hall⟩ := (zf4 st.mc act st.pv pm).mp qo
    have yc : st.pv.any (fun pm => act.all (zej st.mc pm)) = true :=
     List.any_eq_true.mpr ⟨pm, hpv, hall⟩
    simp [yc]
  have ih' := ih r.2.1
  change r.2.2 + (if st.pv.any (fun pm => act.all (zej st.mc pm)) then 1 else 0) +
   zew qa r.2.1 = _
  rw [tv, ih', ze.1, ze.2]
  omega
theorem zgc (steps : List zeu) (act : List ℕ) (g : ℕ) :
  (zfn steps act 0).1 ≤ zew steps (act ++ [g]) := by
 induction steps generalizing act g with
 | nil => simp [zfn, zew]
 | cons st qa ih =>
  simp only [zew, zfn, zf7]
  have ze : (zfn qa (zek.go st.mc act st.rc [] 0).2.1
    (zek.go st.mc act st.rc [] 0).2.2).1 =
    (zfn qa (zek.go st.mc act st.rc [] 0).2.1 0).1 +
    (zek.go st.mc act st.rc [] 0).2.2 := by
   have h := zga qa (zek.go st.mc act st.rc [] 0).2.1 0
    (zek.go st.mc act st.rc [] 0).2.2
   simp only [zero_add] at h
   rw [h]
  have qQ := zf9 st.mc act st.rc [] 0 g
  change _ ≤ (zek.go st.mc (act ++ [g]) st.rc [] 0).2.2 +
   (if st.pv.any (fun pm => (act ++ [g]).all (zej st.mc pm)) then 1 else 0) +
   zew qa (zek.go st.mc (act ++ [g]) st.rc [] 0).2.1
  rw [qQ, ze]
  dsimp only
  cases hm : isMeet st.mc (zek.go st.mc act st.rc [] 0).1 (Nat.land g st.mc)
  ·dsimp only
   have yV := ih (zek.go st.mc act st.rc [] 0).2.1 (Nat.land g st.mc)
   omega
  ·dsimp only
   have heq := zgb qa (zek.go st.mc act st.rc [] 0).2.1
   omega
theorem zgd (steps : List zeu) (act : List ℕ)
  (g need qt : ℕ)
  (hok : zfp g need qt (zfn steps act 0).2.2 = true) :
  need ≤ 1 + (zfn steps act 0).2.1 := by
 induction steps generalizing act g need qt with
 | nil =>
  simp only [zfn, zfp] at hok ⊢
  have h0 : need = 0 := Nat.eq_of_beq_eq_true hok
  omega
 | cons st qa ih =>
  simp only [zfn, zf7] at hok ⊢
  set r := zek.go st.mc act st.rc [] 0
  have ze : (zfn qa r.2.1 r.2.2).2.1 = (zfn qa r.2.1 0).2.1 ∧
    (zfn qa r.2.1 r.2.2).2.2 = (zfn qa r.2.1 0).2.2 := by
   have h := zga qa r.2.1 0 r.2.2
   simp only [zero_add] at h
   rw [h]; exact ⟨rfl, rfl⟩
  rw [ze.1] at hok ⊢
  rw [ze.2] at hok
  cases qt with
  | zero =>
   simp only [zfp] at hok
   cases hm : zfg st.mc r.1 (Nat.land g st.mc)
   ·rw [hm] at hok; simp at hok
   ·rw [hm] at hok
    cases h1 : Nat.ble need (1 + (zfn qa r.2.1 0).2.1)
    ·rw [h1] at hok
     cases h2 : Nat.ble need (2 + (zfn qa r.2.1 0).2.1)
     ·rw [h2] at hok; simp at hok
     ·rw [h2] at hok
      have hle : need ≤ 2 + (zfn qa r.2.1 0).2.1 := Nat.le_of_ble_eq_true h2
      cases hvp : zfk st.mc act st.pv
      ·rw [hvp] at hok; simp [zfl] at hok
      ·dsimp only; omega
    ·have hle : need ≤ 1 + (zfn qa r.2.1 0).2.1 := Nat.le_of_ble_eq_true h1
     cases zfk st.mc act st.pv <;> dsimp only <;> omega
  | succ s' =>
   simp only [zfp] at hok
   cases hvp : zfk st.mc act st.pv
   ·rw [hvp] at hok; dsimp only at hok ⊢
    cases h0 : Nat.beq need 0
    ·rw [h0] at hok
     have := ih r.2.1 (Nat.land g st.mc) need s' hok
     omega
    ·have := Nat.eq_of_beq_eq_true h0; omega
   ·rw [hvp] at hok; dsimp only at hok ⊢
    cases hp : zfl st.mc g (zfk st.mc act st.pv)
    ·rw [hvp] at hp; rw [hp] at hok; dsimp only at hok
     cases h0 : Nat.beq need 0
     ·rw [h0] at hok
      have := ih r.2.1 (Nat.land g st.mc) need s' hok
      omega
     ·have := Nat.eq_of_beq_eq_true h0; omega
    ·rw [hvp] at hp; rw [hp] at hok; dsimp only at hok
     cases h0 : Nat.beq (Nat.sub need 1) 0
     ·rw [h0] at hok
      have := ih r.2.1 (Nat.land g st.mc) (Nat.sub need 1) s' hok
      rw [zer] at this; omega
     ·have := Nat.eq_of_beq_eq_true h0; rw [zer] at this; omega
theorem zge (steps : List zeu) (act : List ℕ)
  (g need qt : ℕ)
  (hok : zfp g need qt (zfn steps act 0).2.2 = true) :
  (zfn steps act 0).1 + need ≤ zew steps (act ++ [g]) := by
 induction steps generalizing act g need qt with
 | nil =>
  simp only [zfn, zfp, zew] at hok ⊢
  have := Nat.eq_of_beq_eq_true hok; omega
 | cons st qa ih =>
  simp only [zew, zfn, zf7] at hok ⊢
  have ze : (zfn qa (zek.go st.mc act st.rc [] 0).2.1
     (zek.go st.mc act st.rc [] 0).2.2).1 =
    (zfn qa (zek.go st.mc act st.rc [] 0).2.1 0).1 +
     (zek.go st.mc act st.rc [] 0).2.2 ∧
   (zfn qa (zek.go st.mc act st.rc [] 0).2.1
     (zek.go st.mc act st.rc [] 0).2.2).2.1 =
    (zfn qa (zek.go st.mc act st.rc [] 0).2.1 0).2.1 ∧
   (zfn qa (zek.go st.mc act st.rc [] 0).2.1
     (zek.go st.mc act st.rc [] 0).2.2).2.2 =
    (zfn qa (zek.go st.mc act st.rc [] 0).2.1 0).2.2 := by
   have h := zga qa (zek.go st.mc act st.rc [] 0).2.1 0
    (zek.go st.mc act st.rc [] 0).2.2
   simp only [zero_add] at h
   rw [h]; exact ⟨rfl, rfl, rfl⟩
  rw [ze.1]
  rw [ze.2.1, ze.2.2] at hok
  have qQ := zf9 st.mc act st.rc [] 0 g
  change _ ≤ (zek.go st.mc (act ++ [g]) st.rc [] 0).2.2 +
   (if st.pv.any (fun pm => (act ++ [g]).all (zej st.mc pm)) then 1 else 0) +
   zew qa (zek.go st.mc (act ++ [g]) st.rc [] 0).2.1
  rw [qQ]
  set r := zek.go st.mc act st.rc [] 0
  have v3 : Nat.land g st.mc &&& st.mc = Nat.land g st.mc := by
   apply Nat.eq_of_testBit_eq; intro s; simp [Nat.testBit_and]
  have xS : zfg st.mc r.1 (Nat.land g st.mc) = isMeet st.mc r.1 (Nat.land g st.mc) :=
   zf0 r.1 v3
  have yS : (st.pv.any (fun pm => (act ++ [g]).all (zej st.mc pm))) =
    zfl st.mc g (zfk st.mc act st.pv) := by
   apply Bool.eq_iff_iff.mpr
   exact (zf6 st.mc g act st.pv).symm
  rw [yS]
  dsimp only
  cases hm : isMeet st.mc r.1 (Nat.land g st.mc)
  ·-- `g` survives w9 `st`
   dsimp only
   cases qt with
   | zero =>
    simp only [zfp, xS, hm] at hok
    simp at hok
   | succ s' =>
    simp only [zfp] at hok
    have hge := zgc qa r.2.1 (Nat.land g st.mc)
    cases hvp : zfk st.mc act st.pv
    ·rw [hvp] at hok; simp only at hok
     cases h0 : Nat.beq need 0
     ·rw [h0] at hok; simp only at hok
      have yV := ih r.2.1 (Nat.land g st.mc) need s' hok
      omega
     ·have := Nat.eq_of_beq_eq_true h0; omega
    ·rw [hvp] at hok; simp only at hok
     cases hp : zfl st.mc g (_ :: _)
     ·rw [hp] at hok; simp only at hok
      cases h0 : Nat.beq need 0
      ·rw [h0] at hok; simp only at hok
       have yV := ih r.2.1 (Nat.land g st.mc) need s' hok
       omega
      ·have := Nat.eq_of_beq_eq_true h0; omega
     ·rw [hp] at hok; simp only at hok
      simp only [↓reduceIte]
      cases h0 : Nat.beq (Nat.sub need 1) 0
      ·rw [h0] at hok; simp only at hok
       have yV := ih r.2.1 (Nat.land g st.mc) (Nat.sub need 1) s' hok
       rw [zer] at yV; omega
      ·have := Nat.eq_of_beq_eq_true h0; rw [zer] at this; omega
  ·-- `g` is dropped as `isMeet` at w9 `st`
   dsimp only
   have vz := zgb qa r.2.1
   rw [vz]
   cases qt with
   | zero =>
    simp only [zfp, xS, hm] at hok
    cases h1 : Nat.ble need (1 + (zfn qa r.2.1 0).2.1)
    ·rw [h1] at hok
     cases h2 : Nat.ble need (2 + (zfn qa r.2.1 0).2.1)
     ·rw [h2] at hok; simp at hok
     ·rw [h2] at hok; simp only at hok
      have hle := Nat.le_of_ble_eq_true h2
      rw [hok]; simp only [↓reduceIte]; omega
    ·have hle := Nat.le_of_ble_eq_true h1
     split_ifs <;> omega
   | succ s' =>
    simp only [zfp] at hok
    cases hvp : zfk st.mc act st.pv
    ·rw [hvp] at hok; simp only at hok
     cases h0 : Nat.beq need 0
     ·rw [h0] at hok; simp only at hok
      have hle := zgd qa r.2.1 (Nat.land g st.mc) need s' hok
      simp [zfl]; omega
     ·have := Nat.eq_of_beq_eq_true h0; omega
    ·rw [hvp] at hok; simp only at hok
     cases hp : zfl st.mc g (_ :: _)
     ·rw [hp] at hok; simp only at hok
      cases h0 : Nat.beq need 0
      ·rw [h0] at hok; simp only at hok
       have hle := zgd qa r.2.1 (Nat.land g st.mc) need s' hok
       omega
      ·have := Nat.eq_of_beq_eq_true h0; omega
     ·rw [hp] at hok; simp only at hok
      simp only [↓reduceIte]
      cases h0 : Nat.beq (Nat.sub need 1) 0
      ·rw [h0] at hok; simp only at hok
       have hle := zgd qa r.2.1 (Nat.land g st.mc) (Nat.sub need 1) s' hok
       rw [zer] at hle; omega
      ·have := Nat.eq_of_beq_eq_true h0; rw [zer] at this; omega
theorem zgf (cut : zeF) (gs : List ℕ) (qt g : ℕ)
  (hok : zfq (zfo cut gs) qt g = true) :
  cut.loss ≤ zew cut.steps (gs ++ [g]) := by
 unfold zfq zfo at hok
 dsimp only at hok
 cases h0 : Nat.beq (Nat.sub cut.loss (zfn cut.steps gs 0).1) 0
 ·rw [h0] at hok
  have h1 := zge cut.steps gs g _ qt hok
  rw [zer] at h1; omega
 ·have hle : cut.loss ≤ (zfn cut.steps gs 0).1 := by
   have := Nat.eq_of_beq_eq_true h0; rw [zer] at this; omega
  exact hle.trans (zgc cut.steps gs g)
theorem zgg (tbl : List ℕ) (f s acc : ℕ) :
  zfs (f / 2 ^ s) acc (tbl.map (fun x => Nat.pow 2 x)) =
   zdM tbl f s acc := by
 induction tbl generalizing s acc with
 | nil => rfl
 | cons s2 qa ih =>
  simp only [List.map_cons, zfs, zdM]
  cases h0 : Nat.beq (f / 2 ^ s) 0
  ·have zK : Nat.beq (Nat.land (f / 2 ^ s) 1) 1 = f.testBit s := by
    rw [Nat.testBit, Nat.shiftRight_eq_div_pow, land_eq, Nat.and_comm 1 _, Nat.and_one_is_mod]
    have hlt : (f / 2 ^ s) % 2 < 2 := Nat.mod_lt _ (by omega)
    generalize (f / 2 ^ s) % 2 = m at hlt ⊢
    interval_cases m <;> rfl
   have yR : Nat.pow 2 s2 = 1 <<< s2 := by rw [Nat.shiftLeft_eq, one_mul]; rfl
   have tj : Nat.div (f / 2 ^ s) 2 = f / 2 ^ (s + 1) := by
    rw [zes, Nat.div_div_eq_div_mul, Nat.pow_succ]
   rw [zK, yR, tj]
   cases f.testBit s
   ·exact ih (s + 1) acc
   ·exact ih (s + 1) (Nat.lor acc (1 <<< s2))
  ·have hf0 : f / 2 ^ s = 0 := Nat.eq_of_beq_eq_true h0
   have xu : ∀ (l : List ℕ) (t a : ℕ), f / 2 ^ t = 0 → zdM l f t a = a := by
    intro l
    induction l with
    | nil => intro _ _ _; rfl
    | cons x xs ihx =>
     intro t a ht
     simp only [zdM]
     have htb : f.testBit t = false := by
      rw [Nat.testBit, Nat.shiftRight_eq_div_pow, ht]; rfl
     have ht' : f / 2 ^ (t + 1) = 0 := by
      rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, ht]
     rw [htb]; exact ihx (t + 1) a ht'
   exact (xu (s2 :: qa) s acc hf0).symm
theorem zgh (tbl : List ℕ) (f : ℕ) :
  zft (tbl.map (fun s => Nat.pow 2 s)) f = zdN tbl f := by
 simpa [zft, zdN] using zgg tbl f 0 0
theorem zgi (q7 : List (List ℕ)) (oi oj : ℕ)
  (hok : zfv (oi ||| oj)
   (zfu oi (zfX q7))
   (zfu oj (zfX q7)) = true) :
  ∃ tbl ∈ q7, zdN tbl (oi ||| oj) < oi ||| oj := by
 induction q7 with
 | nil => simp [zfX, zfu, zfv] at hok
 | cons tbl qa ih =>
  simp only [zfX, List.map_cons, zfu, zfv,
   zgh, lor_eq, ← zdR] at hok
  cases hlt : Nat.blt (zdN tbl (oi ||| oj)) (oi ||| oj)
  ·rw [hlt] at hok
   obtain ⟨t, ht, h⟩ := ih hok
   exact ⟨t, List.mem_cons_of_mem _ ht, h⟩
  ·exact ⟨tbl, List.mem_cons_self, zeq hlt⟩
theorem zgj (g : ℕ) (q7 : List (List ℕ)) :
  zfw g (zfX q7) =
   zfX (q7.filter (fun tbl => Nat.beq (zdN tbl g) g)) := by
 induction q7 with
 | nil => rfl
 | cons tbl qa ih =>
  simp only [zfX, List.map_cons, zfw, zgh,
   List.filter_cons]
  cases Nat.beq (zdN tbl g) g
  ·exact ih
  ·dsimp only [zfX] at ih
   rw [ih]; rfl
theorem zgk {n : ℕ} {H F : List (ℕ × ℕ)} (hv : zcC n H F) :
  ∀ mt ∈ zcB n H (univYF n F),
   MeetNat (univYF n F) (rawYF n (univYF n F)) mt := by
 set M := univYF n F
 have hM : ∀ s, M.testBit s = true → s < 2 ^ n := fun _ => zcE
 intro mt hmt
 unfold zcB at hmt
 simp only [List.cons_append, List.mem_map, List.mem_cons, List.mem_append, List.mem_range] at hmt
 obtain ⟨m, hm, rfl⟩ := hmt
 refine zdm.mpr ⟨zcR hM, ?_⟩
 rcases hm with rfl | ⟨v, hvlt, rfl⟩ | ⟨e, heH, rfl⟩
 ·rw [zdC hM, zcW]; exact Meet.top
 ·rw [zdD hM]
  exact Meet.atom ⟨ttVarYF n v M, List.mem_map.mpr ⟨v, List.mem_range.mpr hvlt, rfl⟩, rfl⟩
 ·obtain ⟨h1, h2, _⟩ := hv.1 e heH
  rw [← zdE hM, zdD hM, zdD hM, zcX]
  exact (Meet.atom (B := decM M '' { x | x ∈ rawYF n M })
    ⟨ttVarYF n e.1 M, List.mem_map.mpr ⟨e.1, List.mem_range.mpr h1, rfl⟩, rfl⟩).inter
   (Meet.atom (B := decM M '' { x | x ∈ rawYF n M })
    ⟨ttVarYF n e.2 M, List.mem_map.mpr ⟨e.2, List.mem_range.mpr h2, rfl⟩, rfl⟩)
theorem zgl (g : ℕ) (zy acc : List ℕ) (y : ℕ) :
  y ∈ zfz g zy acc ↔ y ∈ acc ∨ ∃ x ∈ zy, y = x &&& g := by
 induction zy generalizing acc with
 | nil => simp [zfz]
 | cons x qa ih =>
  simp only [zfz, ih, List.mem_cons, land_eq]
  constructor
  ·rintro ((rfl | hy) | ⟨z, hz, rfl⟩)
   ·exact Or.inr ⟨x, Or.inl rfl, rfl⟩
   ·exact Or.inl hy
   ·exact Or.inr ⟨z, Or.inr hz, rfl⟩
  ·rintro (hy | ⟨z, rfl | hz, rfl⟩)
   ·exact Or.inl (Or.inr hy)
   ·exact Or.inl (Or.inl rfl)
   ·exact Or.inr ⟨z, hz, rfl⟩
theorem zgm {M ep gi qw : ℕ} {raw done : List ℕ}
  (z2 : qw = done.length)
  (hgi : MeetNat M (raw ++ done) gi)
  (masksTT : List ℕ) (zu : ∀ mt ∈ masksTT, MeetNat M raw mt)
  (qA : List ℕ) (acc : List (ℕ × ℕ × ℕ))
  (qx : ∀ x ∈ acc, x.2.1 = x.1 &&& ep ∧ x.2.2 ≤ qw ∧ MeetNat M (raw ++ done.take x.2.2) x.1)
  (qP : acc.Pairwise (fun x y => y.2.2 ≤ x.2.2))
  (qq : ∀ op ∈ qA, ∃ b, (op, op &&& ep, b) ∈ acc) :
  let res := zfA M ep gi qw masksTT qA acc
  (∀ x ∈ res.2, x.2.1 = x.1 &&& ep ∧ x.2.2 ≤ qw ∧ MeetNat M (raw ++ done.take x.2.2) x.1) ∧
  res.2.Pairwise (fun x y => y.2.2 ≤ x.2.2) ∧
  (∀ op ∈ qA, op ∈ res.1) ∧
  (∀ op ∈ res.1, ∃ b, (op, op &&& ep, b) ∈ res.2) ∧
  (∀ mt ∈ masksTT, (mt &&& gi) ≠ 0 → (mt &&& gi) ≠ M → (mt &&& gi) &&& ep ≠ 0 → (mt &&& gi) ∈ res.1) := by
 induction masksTT generalizing qA acc with
 | nil =>
  simp only [zfA, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨qx, qP, fun _ h => h, qq⟩
 | cons mt qa ih =>
  simp only [zfA, land_eq]
  have hmt : MeetNat M raw mt := zu mt List.mem_cons_self
  have zT : ∀ m ∈ qa, MeetNat M raw m := fun m hm => zu m (List.mem_cons_of_mem _ hm)
  set op := mt &&& gi
  cases h0 : Nat.beq op 0
  ·cases hM : Nat.beq op M
   ·cases hep : Nat.beq (op &&& ep) 0
    ·cases qo : zfe op qA
     ·have vq : MeetNat M (raw ++ done.take qw) op := by
       rw [z2, List.take_length]
       have h1 : MeetNat M (raw ++ done) mt :=
        zdn (fun x hx => List.mem_append_left _ hx) hmt
       have qu : op &&& M = op := by
        apply Nat.eq_of_testBit_eq; intro s
        have ha := congrArg (fun z => z.testBit s) hmt.1
        simp only [op, Nat.testBit_and] at ha ⊢
        revert ha; cases mt.testBit s <;> cases gi.testBit s <;> cases M.testBit s <;> decide
       exact zdm.mpr ⟨qu, by rw [zcX]; exact (zdm.mp h1).2.inter (zdm.mp hgi).2⟩
      have z0 : ∀ x ∈ (op, op &&& ep, qw) :: acc,
        x.2.1 = x.1 &&& ep ∧ x.2.2 ≤ qw ∧ MeetNat M (raw ++ done.take x.2.2) x.1 := by
       intro x hx
       rcases List.mem_cons.mp hx with rfl | hx
       ·exact ⟨rfl, le_rfl, vq⟩
       ·exact qx x hx
      have y8 : ((op, op &&& ep, qw) :: acc).Pairwise (fun x y => y.2.2 ≤ x.2.2) :=
       List.pairwise_cons.mpr ⟨fun y hy => (qx y hy).2.1, qP⟩
      have yr : ∀ o ∈ op :: qA, ∃ b, (o, o &&& ep, b) ∈ (op, op &&& ep, qw) :: acc := by
       intro o ho
       rcases List.mem_cons.mp ho with rfl | ho
       ·exact ⟨qw, List.mem_cons_self⟩
       ·obtain ⟨b, hb⟩ := qq o ho
        exact ⟨b, List.mem_cons_of_mem _ hb⟩
      obtain ⟨i1, i2, i3, i4, i5⟩ := ih zT (op :: qA) ((op, op &&& ep, qw) :: acc)
       z0 y8 yr
      refine ⟨i1, i2, fun o ho => i3 o (List.mem_cons_of_mem _ ho), i4, fun m hm => ?_⟩
      rcases List.mem_cons.mp hm with rfl | hm
      ·intro _ _ _; exact i3 op List.mem_cons_self
      ·exact i5 m hm
     ·obtain ⟨i1, i2, i3, i4, i5⟩ := ih zT qA acc qx qP qq
      refine ⟨i1, i2, i3, i4, fun m hm => ?_⟩
      rcases List.mem_cons.mp hm with rfl | hm
      ·intro _ _ _; exact i3 op ((zfY op qA).mp qo)
      ·exact i5 m hm
    ·obtain ⟨i1, i2, i3, i4, i5⟩ := ih zT qA acc qx qP qq
     refine ⟨i1, i2, i3, i4, fun m hm => ?_⟩
     rcases List.mem_cons.mp hm with rfl | hm
     ·intro _ _ hne; exact (hne (Nat.eq_of_beq_eq_true hep)).elim
     ·exact i5 m hm
   ·obtain ⟨i1, i2, i3, i4, i5⟩ := ih zT qA acc qx qP qq
    refine ⟨i1, i2, i3, i4, fun m hm => ?_⟩
    rcases List.mem_cons.mp hm with rfl | hm
    ·intro _ hne _; exact (hne (Nat.eq_of_beq_eq_true hM)).elim
    ·exact i5 m hm
  ·obtain ⟨i1, i2, i3, i4, i5⟩ := ih zT qA acc qx qP qq
   refine ⟨i1, i2, i3, i4, fun m hm => ?_⟩
   rcases List.mem_cons.mp hm with rfl | hm
   ·intro hne _ _; exact (hne (Nat.eq_of_beq_eq_true h0)).elim
   ·exact i5 m hm
theorem zgn {M ep qw : ℕ} {raw done masksTT : List ℕ}
  (z2 : qw = done.length)
  (zu : ∀ mt ∈ masksTT, MeetNat M raw mt)
  (qB qA : List ℕ) (acc : List (ℕ × ℕ × ℕ))
  (x0 : ∀ gi ∈ qB, MeetNat M (raw ++ done) gi)
  (qx : ∀ x ∈ acc, x.2.1 = x.1 &&& ep ∧ x.2.2 ≤ qw ∧ MeetNat M (raw ++ done.take x.2.2) x.1)
  (qP : acc.Pairwise (fun x y => y.2.2 ≤ x.2.2))
  (qq : ∀ op ∈ qA, ∃ b, (op, op &&& ep, b) ∈ acc) :
  let res := zfB M ep qw masksTT qB qA acc
  (∀ x ∈ res.2, x.2.1 = x.1 &&& ep ∧ x.2.2 ≤ qw ∧ MeetNat M (raw ++ done.take x.2.2) x.1) ∧
  res.2.Pairwise (fun x y => y.2.2 ≤ x.2.2) ∧
  (∀ op ∈ qA, op ∈ res.1) ∧
  (∀ op ∈ res.1, ∃ b, (op, op &&& ep, b) ∈ res.2) ∧
  (∀ gi ∈ qB, ∀ mt ∈ masksTT, (mt &&& gi) ≠ 0 → (mt &&& gi) ≠ M → (mt &&& gi) &&& ep ≠ 0 → (mt &&& gi) ∈ res.1) := by
 induction qB generalizing qA acc with
 | nil =>
  simp only [zfB, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨qx, qP, fun _ h => h, qq⟩
 | cons gi qa ih =>
  simp only [zfB]
  have h1 := zgm z2 (x0 gi List.mem_cons_self) masksTT zu qA acc
   qx qP qq
  set r1 := zfA M ep gi qw masksTT qA acc
  obtain ⟨i1, i2, i3, i4, i5⟩ := ih r1.1 r1.2
   (fun g hg => x0 g (List.mem_cons_of_mem _ hg)) h1.1 h1.2.1 h1.2.2.2.1
  refine ⟨i1, i2, fun o ho => i3 o (h1.2.2.1 o ho), i4, fun g hg mt hmt h0 hM hep => ?_⟩
  rcases List.mem_cons.mp hg with rfl | hg
  ·exact i3 (mt &&& g) (h1.2.2.2.2 mt hmt h0 hM hep)
  ·exact i5 g hg mt hmt h0 hM hep
theorem zgo {α : Type} {P done : List α} {g : α}
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
   ·exact Or.inl (List.Sublist.cons x h1)
   ·exact Or.inr ⟨P', List.Sublist.cons x h1, rfl⟩
  | cons_cons _ h' =>
   rcases ih h' with h1 | ⟨P', h1, rfl⟩
   ·exact Or.inl (List.Sublist.cons_cons x h1)
   ·exact Or.inr ⟨x :: P', List.Sublist.cons_cons x h1, rfl⟩
theorem zgp {M ep : ℕ} {raw masksTT : List ℕ}
  (zu : ∀ mt ∈ masksTT, MeetNat M raw mt) :
  ∀ (qa done zy qA : List ℕ) (acc : List (ℕ × ℕ × ℕ)),
   zdk M (raw ++ done) qa →
   (∀ gi ∈ zy, MeetNat M (raw ++ done) gi) →
   (∀ P : List ℕ, List.Sublist P done → P.foldl Nat.land M ∈ zy) →
   (∀ x ∈ acc, x.2.1 = x.1 &&& ep ∧ x.2.2 ≤ done.length ∧ MeetNat M (raw ++ done.take x.2.2) x.1) →
   acc.Pairwise (fun x y => y.2.2 ≤ x.2.2) →
   (∀ op ∈ qA, ∃ b, (op, op &&& ep, b) ∈ acc) →
   (∀ gi ∈ zy, ∀ mt ∈ masksTT, (mt &&& gi) ≠ 0 → (mt &&& gi) ≠ M → (mt &&& gi) &&& ep ≠ 0 → (mt &&& gi) ∈ qA) →
   let res := zfC M ep masksTT (done.length + 1) zy qA acc qa
   (∀ x ∈ res, x.2.1 = x.1 &&& ep ∧ x.2.2 ≤ (done ++ qa).length ∧
    MeetNat M (raw ++ (done ++ qa).take x.2.2) x.1) ∧
   res.Pairwise (fun x y => y.2.2 ≤ x.2.2) ∧
   (∀ P : List ℕ, List.Sublist P (done ++ qa) → ∀ mt ∈ masksTT,
    (mt &&& P.foldl Nat.land M) ≠ 0 → (mt &&& P.foldl Nat.land M) ≠ M →
    (mt &&& P.foldl Nat.land M) &&& ep ≠ 0 →
    ∃ b, (mt &&& P.foldl Nat.land M, (mt &&& P.foldl Nat.land M) &&& ep, b) ∈ res) := by
 intro qa
 induction qa with
 | nil =>
  intro done zy qA acc _ _ xF qx qP qq z5
  simp only [zfC, List.append_nil]
  exact ⟨qx, qP, fun P hP mt hmt h0 hM hep =>
   qq _ (z5 _ (xF P hP) mt hmt h0 hM hep)⟩
 | cons g qb ih =>
  intro done zy qA acc hvp x0 xF qx qP qq z5
  rcases hvp with ⟨⟨a, b, ha, hb, hgab⟩, htail_vp⟩
  have hgM : g &&& M = g := hgab ▸ zdo ha.1 hb.1
  set done' := done ++ [g]
  have q9 : done'.length = done.length + 1 := by simp [done']
  have xV : ∀ z ∈ raw ++ done, z ∈ raw ++ done' := by
   intro z hz
   rcases List.mem_append.mp hz with hz | hz
   ·exact List.mem_append_left _ hz
   ·exact List.mem_append_right _ (List.mem_append_left _ hz)
  set qB := zfz g zy []
  have zN : ∀ gi ∈ qB, MeetNat M (raw ++ done') gi := by
   intro gi hgi
   rw [zgl] at hgi
   rcases hgi with hnil | ⟨x, hx, rfl⟩
   ·simp at hnil
   ·have hx' := zdn xV (x0 x hx)
    have qu : (x &&& g) &&& M = x &&& g := by
     apply Nat.eq_of_testBit_eq; intro s
     have h1 := congrArg (fun z => z.testBit s) hgM
     simp only [Nat.testBit_and] at h1 ⊢
     revert h1; cases x.testBit s <;> cases g.testBit s <;> cases M.testBit s <;> decide
    have yi : g ∈ raw ++ done' := by simp [done']
    exact zdm.mpr ⟨qu, by rw [zcX]; exact (zdm.mp hx').2.inter (Meet.atom ⟨g, yi, rfl⟩)⟩
  have z0 : ∀ x ∈ acc, x.2.1 = x.1 &&& ep ∧ x.2.2 ≤ done.length + 1 ∧
    MeetNat M (raw ++ done'.take x.2.2) x.1 := by
   intro x hx
   obtain ⟨h1, h2, h3⟩ := qx x hx
   refine ⟨h1, by omega, ?_⟩
   have x8 : done'.take x.2.2 = done.take x.2.2 := by
    simp only [done', List.take_append_of_le_length h2]
   rwa [x8]
  have y9 := zgn q9.symm zu qB qA acc zN
   z0 qP qq
  set r1 := zfB M ep (done.length + 1) masksTT qB qA acc
  have w5 : ∀ gi ∈ qB ++ zy, MeetNat M (raw ++ done') gi := by
   intro gi hgi
   rcases List.mem_append.mp hgi with hgi | hgi
   ·exact zN gi hgi
   ·exact zdn xV (x0 gi hgi)
  have v5 : ∀ P : List ℕ, List.Sublist P done' → P.foldl Nat.land M ∈ qB ++ zy := by
   intro P hP
   rcases zgo hP with h1 | ⟨P', h1, rfl⟩
   ·exact List.mem_append_right _ (xF P h1)
   ·refine List.mem_append_left _ ?_
    rw [zgl]
    refine Or.inr ⟨P'.foldl Nat.land M, xF P' h1, ?_⟩
    simp [List.foldl_append]
  have yt : ∀ gi ∈ qB ++ zy, ∀ mt ∈ masksTT,
    (mt &&& gi) ≠ 0 → (mt &&& gi) ≠ M → (mt &&& gi) &&& ep ≠ 0 → (mt &&& gi) ∈ r1.1 := by
   intro gi hgi mt hmt h0 hM hep
   rcases List.mem_append.mp hgi with hgi | hgi
   ·exact y9.2.2.2.2 gi hgi mt hmt h0 hM hep
   ·exact y9.2.2.1 _ (z5 gi hgi mt hmt h0 hM hep)
  have zI : zdk M (raw ++ done') qb := by
   simpa only [done', List.append_assoc] using htail_vp
  have yV := ih done' (qB ++ zy) r1.1 r1.2 zI w5 v5
   (by simpa only [q9] using y9.1) y9.2.1 y9.2.2.2.1 yt
  simp only [zfC]
  simpa only [done', q9, List.append_assoc, List.singleton_append] using yV
theorem zgq {n : ℕ} {H F : List (ℕ × ℕ)} {gs : List ℕ}
  (hv : zcC n H F)
  (hvp : zdk (univYF n F) (rawYF n (univYF n F)) gs) :
  let M := univYF n F
  let ep := zcz H
  let raw := rawYF n M
  let ops := zfD M ep (zcB n H M) gs
  (∀ x ∈ ops, x.2.1 = x.1 &&& ep ∧ x.2.2 ≤ gs.length ∧ MeetNat M (raw ++ gs.take x.2.2) x.1) ∧
  ops.Pairwise (fun x y => y.2.2 ≤ x.2.2) ∧
  (∀ x : ℕ, MeetNat M (raw ++ gs) x → x ≠ 0 → x ≠ M → x &&& ep ≠ 0 →
   ∃ b, (x, x &&& ep, b) ∈ ops) := by
 set M := univYF n F
 set ep := zcz H
 set raw := rawYF n M
 set masksTT := zcB n H M
 have zu : ∀ mt ∈ masksTT, MeetNat M raw mt := zgk hv
 have yy : MeetNat M (raw ++ []) M := by
  refine zdm.mpr ⟨by simp, ?_⟩
  rw [zcW]; exact Meet.top
 have h0 := zgm (ep := ep) (done := []) rfl yy masksTT zu [] []
  (fun _ h => by simp at h) List.Pairwise.nil (fun _ h => by simp at h)
 set r0 := zfA M ep M 0 masksTT [] []
 have yB := zgp zu gs [] [M] r0.1 r0.2
  (by simpa using hvp)
  (fun gi hgi => by rw [List.mem_singleton.mp hgi]; exact yy)
  (fun P hP => by cases hP; simp)
  h0.1 h0.2.1 h0.2.2.2.1
  (fun gi hgi mt hmt h0' hM' vV => by
   obtain rfl := List.mem_singleton.mp hgi; exact h0.2.2.2.2 mt hmt h0' hM' vV)
 simp only [List.length_nil, zero_add, List.nil_append] at yB
 refine ⟨yB.1, yB.2.1, fun x hx h0' hM' vV => ?_⟩
 obtain ⟨mt, hmt, P, hPsub, rfl⟩ := zdJ hv hx vV
 exact yB.2.2 P hPsub mt hmt h0' hM' vV
theorem zgr (gs : List ℕ) :
  ∃ m ms, zfF gs = m :: ms := by
 induction gs with
 | nil => exact ⟨0, [], rfl⟩
 | cons g qa ih =>
  obtain ⟨m, ms, heq⟩ := ih
  exact ⟨zfE g m, m :: ms, by simp [zfF, heq]⟩
theorem zgs (gs : List ℕ) (bi g : ℕ)
  (zt : zfG (zfF gs) bi ≠ 0)
  (hlt : g < zfG (zfF gs) bi) :
  ∃ t, bi ≤ t ∧ ∃ (ht : t < gs.length), g < gs[t] := by
 induction gs generalizing bi with
 | nil =>
  cases bi with
  | zero => simp [zfF, zfG] at zt
  | succ k => cases k <;> simp [zfF, zfG] at zt
 | cons x qa ih =>
  obtain ⟨m, ms, hsm⟩ := zgr qa
  have uk : zfF (x :: qa) = zfE x m :: m :: ms := by
   simp [zfF, hsm]
  rw [uk] at zt hlt
  cases bi with
  | zero =>
   simp only [zfG] at zt hlt
   unfold zfE at hlt
   cases hxm : Nat.blt x m
   ·rw [hxm] at hlt; dsimp only at hlt
    exact ⟨0, le_rfl, by simp, hlt⟩
   ·rw [hxm] at hlt; dsimp only at hlt
    have hm0 : m ≠ 0 := by omega
    have wd : zfG (zfF qa) 0 = m := by simp [hsm, zfG]
    obtain ⟨t, _, ht, hgt⟩ := ih 0 (wd.symm ▸ hm0) (wd.symm ▸ hlt)
    exact ⟨t + 1, Nat.zero_le _, by simp [ht], by simpa using hgt⟩
  | succ bi' =>
   simp only [zfG] at zt hlt
   have heq : zfG (m :: ms) bi' = zfG (zfF qa) bi' := by rw [hsm]
   rw [heq] at zt hlt
   obtain ⟨t, hle, ht, hgt⟩ := ih bi' zt hlt
   exact ⟨t + 1, by omega, by simp [ht], by simpa using hgt⟩
theorem zgt (edgeTT acc : ℕ) (b : List ℕ) :
  zfP edgeTT acc b = zdb edgeTT b acc := by
 induction b generalizing acc with
 | nil => rfl
 | cons x qa ih =>
  simp only [zfP, zdb]
  cases Nat.beq (Nat.land edgeTT x) edgeTT <;> exact ih _
theorem zgu (bad : ℕ) (ops : List (ℕ × ℕ × ℕ)) :
  zfQ bad ops =
   (ops.map Prod.fst).filter (fun op => Nat.beq (Nat.land op bad) 0) := by
 induction ops with
 | nil => rfl
 | cons p qa ih =>
  rcases p with ⟨op, eg, b⟩
  simp only [zfQ, List.map_cons, List.filter_cons]
  cases Nat.beq (Nat.land op bad) 0 <;> simp [ih]
theorem zgv (ep a : ℕ) (l : List ℕ) :
  zfR ep a l = l.all (fun b => !Nat.beq (Nat.land (Nat.lor a b) ep) ep) := by
 induction l with
 | nil => rfl
 | cons b qa ih =>
  simp only [zfR, List.all_cons]
  cases Nat.beq (Nat.land (Nat.lor a b) ep) ep <;> simp [ih]
theorem zgw (ep : ℕ) (l : List ℕ) :
  zfS ep l = zeC ep l := by
 induction l with
 | nil => rfl
 | cons a qa ih =>
  simp only [zfS, zeC, zgv]
  cases qa.all (fun b => !Nat.beq (Nat.land (Nat.lor a b) ep) ep) <;> simp [ih]
theorem zgx {n : ℕ} {H F : List (ℕ × ℕ)} {pre suf : List ℕ}
  (hv : zcC n H F) (yM : H ≠ [])
  (qj : zdl (univYF n F) (rawYF n (univYF n F)) (zcy n H (univYF n F)) (pre ++ suf))
  (qz : ∀ k' < (pre ++ suf).length, ¬ zcT n H F k')
  (xG : suf.length ≤ 1)
  (hok : zfT (univYF n F) (zcz H) (zcy n H (univYF n F))
   (rawYF n (univYF n F)) (zcB n H (univYF n F)) pre = true) :
  False := by
 set M := univYF n F
 set ep := zcz H
 set edgeTT := zcy n H M
 set raw := rawYF n M
 unfold zfT at hok
 dsimp only at hok
 rw [zgt] at hok
 cases hmd : Nat.beq (zdb edgeTT (raw ++ pre) M) edgeTT
 ·rw [hmd] at hok
  have vl : zdb edgeTT (raw ++ pre) M ≠ edgeTT := (zet _ _).mp hmd
  cases suf with
  | nil =>
   obtain ⟨_, hend⟩ := zdr.mp qj
   have xe : edgeTT ≠ 0 := by
    obtain ⟨e, _, heq⟩ := List.exists_cons_of_ne_nil yM
    intro h0
    have zK := zcO hv (show e ∈ H by rw [heq]; simp)
    rw [show zcy n H (univYF n F) = edgeTT from rfl, h0] at zK; simp at zK
   have hm := hend.2
   unfold isMeet at hm
   rw [(zet _ _).mpr xe] at hm
   exact vl (Nat.eq_of_beq_eq_true hm)
  | cons g qa =>
   cases qa with
   | cons => simp at xG
   | nil =>
    have hvp : zdk M raw pre := (zdr.mp qj).1
    have yQ := zgq hv hvp
    have vr : ∀ x, MeetNat M (raw ++ pre) x → x ≠ 0 → x ≠ M → x &&& ep ≠ 0 →
      x ∈ (zfD M ep (zcB n H M) pre).map Prod.fst := by
     intro x hx h0 hM hep
     obtain ⟨b, hb⟩ := yQ.2.2 x hx h0 hM hep
     exact List.mem_map.mpr ⟨(x, x &&& ep, b), hb, rfl⟩
    have htm := zeE hv yM qj qz vr
    rcases htm with heq | yl
    ·exact vl heq
    ·apply yl
     rw [← zgw, ← zgu]
     exact hok
 ·rw [hmd] at hok; simp at hok
theorem zgy {cuts : List zeF} {ci : ℕ} {gs : List ℕ} {qt g : ℕ}
  (hok : zfq (zfo (zfx cuts ci) gs) qt g = true) :
  zfx cuts ci ∈ cuts := by
 induction cuts generalizing ci with
 | nil =>
  cases ci <;> simp [zfx, zfo, zfn, zfq, zfp] at hok
 | cons c qa ih =>
  cases ci with
  | zero => exact List.mem_cons_self
  | succ k => exact List.mem_cons_of_mem _ (ih hok)
theorem zgz {cuts : List zeF} {gs zM : List ℕ} {hi qt g : ℕ}
  (hok : zfq (zfr (zfy cuts gs zM) hi) qt g = true) :
  ∃ cut ∈ cuts, zfq (zfo cut gs) qt g = true := by
 induction zM generalizing hi with
 | nil =>
  cases hi <;> simp [zfy, zfr, zfq, zfp] at hok
 | cons ci qa ih =>
  cases hi with
  | zero =>
   simp only [zfy, zfr] at hok
   exact ⟨zfx cuts ci, zgy hok, hok⟩
  | succ k =>
   simp only [zfy, zfr] at hok
   exact ih hok
theorem zgA {maskYF : ℕ} {b : List ℕ} {qf : List zeZ}
  {qv : List ℕ} {oi egi lim : ℕ} {qa : List (ℕ × ℕ × ℕ)} {qF zV : List ℕ}
  (hok : zfI maskYF b qf qv oi egi lim qa qF = some zV) :
  ∀ x ∈ qa,
   (egi &&& x.2.1 = egi) ∨ (egi &&& x.2.1 = x.2.1) ∨
   (lim ≠ 0 ∧ oi ||| x.1 < lim) ∨
   ∃ w, zfH maskYF b qf qv (egi ||| x.2.1) (oi ||| x.1) w = true := by
 induction qa generalizing qF with
 | nil => intro x hx; simp at hx
 | cons p qb ih =>
  rcases p with ⟨oj, egj, bj⟩
  simp only [zfI, land_eq, lor_eq] at hok
  intro x hx
  cases h1 : Nat.beq (egi &&& egj) egi
  ·rw [h1] at hok; dsimp only at hok
   cases h2 : Nat.beq (egi &&& egj) egj
   ·rw [h2] at hok; dsimp only at hok
    cases qG : (match Nat.beq lim 0 with | true => false | false => Nat.blt (oi ||| oj) lim)
    ·rw [qG] at hok; dsimp only at hok
     cases qF with
     | nil => simp at hok
     | cons w ws =>
      dsimp only at hok
      cases hw : zfH maskYF b qf qv (egi ||| egj) (oi ||| oj) w
      ·rw [hw] at hok; simp at hok
      ·rw [hw] at hok; dsimp only at hok
       rcases List.mem_cons.mp hx with rfl | hx
       ·exact Or.inr (Or.inr (Or.inr ⟨w, hw⟩))
       ·exact ih hok x hx
    ·rw [qG] at hok; dsimp only at hok
     rcases List.mem_cons.mp hx with rfl | hx
     ·cases hl0 : Nat.beq lim 0
      ·rw [hl0] at qG; dsimp only at qG
       exact Or.inr (Or.inr (Or.inl ⟨(zet _ _).mp hl0, zeq qG⟩))
      ·rw [hl0] at qG; simp at qG
     ·exact ih hok x hx
   ·rw [h2] at hok; dsimp only at hok
    rcases List.mem_cons.mp hx with rfl | hx
    ·exact Or.inr (Or.inl (Nat.eq_of_beq_eq_true h2))
    ·exact ih hok x hx
  ·rw [h1] at hok; dsimp only at hok
   rcases List.mem_cons.mp hx with rfl | hx
   ·exact Or.inl (Nat.eq_of_beq_eq_true h1)
   ·exact ih hok x hx
theorem zgB {maskYF : ℕ} {b : List ℕ} {qf : List zeZ}
  {qv zL : List ℕ} {ops : List (ℕ × ℕ × ℕ)} {qF : List ℕ}
  (hok : zfJ maskYF b qf qv zL ops qF = true)
  (hpw : ops.Pairwise (fun x y => y.2.2 ≤ x.2.2))
  {x y : ℕ × ℕ × ℕ} (hx : x ∈ ops) (hy : y ∈ ops) (hne : x.1 ≠ y.1) :
  ∃ p q : ℕ × ℕ × ℕ, ((p = x ∧ q = y) ∨ (p = y ∧ q = x)) ∧ q.2.2 ≤ p.2.2 ∧
   let lim := zfG zL p.2.2
   ((p.2.1 &&& q.2.1 = p.2.1) ∨ (p.2.1 &&& q.2.1 = q.2.1) ∨
    (lim ≠ 0 ∧ p.1 ||| q.1 < lim) ∨
    ∃ w, zfH maskYF b qf qv (p.2.1 ||| q.2.1) (p.1 ||| q.1) w = true) := by
 induction ops generalizing qF with
 | nil => simp at hx
 | cons z qa ih =>
  rcases z with ⟨oi, egi, bi⟩
  simp only [zfJ] at hok
  cases hinner : zfI maskYF b qf qv oi egi (zfG zL bi) qa qF with
  | none => rw [hinner] at hok; simp at hok
  | some zV =>
   rw [hinner] at hok
   obtain ⟨hhead_pw, htail_pw⟩ := List.pairwise_cons.mp hpw
   rcases List.mem_cons.mp hx with rfl | hx' <;> rcases List.mem_cons.mp hy with rfl | hy'
   ·exact (hne rfl).elim
   ·exact ⟨(oi, egi, bi), y, Or.inl ⟨rfl, rfl⟩, hhead_pw y hy',
     zgA hinner y hy'⟩
   ·exact ⟨(oi, egi, bi), x, Or.inr ⟨rfl, rfl⟩, hhead_pw x hx',
     zgA hinner x hx'⟩
   ·exact ih hok htail_pw hx' hy'
theorem zgC {maskYF : ℕ} {b : List ℕ} {qf : List zeZ}
  {qv : List ℕ} {oi egi lim : ℕ} {pi : List ℕ}
  {qa : List (ℕ × ℕ × ℕ × List ℕ)} {qF zV : List ℕ}
  (hok : zfM maskYF b qf qv oi egi lim pi qa qF = some zV) :
  ∀ x ∈ qa,
   (egi &&& x.2.1 = egi) ∨ (egi &&& x.2.1 = x.2.1) ∨
   (lim ≠ 0 ∧ oi ||| x.1 < lim) ∨
   ∃ w, zfL maskYF b qf qv (egi ||| x.2.1) (oi ||| x.1) pi x.2.2.2 w = true := by
 induction qa generalizing qF with
 | nil => intro x hx; simp at hx
 | cons p qb ih =>
  rcases p with ⟨oj, egj, bj, pj⟩
  simp only [zfM, land_eq, lor_eq] at hok
  intro x hx
  cases h1 : Nat.beq (egi &&& egj) egi
  ·rw [h1] at hok; dsimp only at hok
   cases h2 : Nat.beq (egi &&& egj) egj
   ·rw [h2] at hok; dsimp only at hok
    cases qG : (match Nat.beq lim 0 with | true => false | false => Nat.blt (oi ||| oj) lim)
    ·rw [qG] at hok; dsimp only at hok
     cases qF with
     | nil => simp at hok
     | cons w ws =>
      dsimp only at hok
      cases hw : zfL maskYF b qf qv (egi ||| egj) (oi ||| oj) pi pj w
      ·rw [hw] at hok; simp at hok
      ·rw [hw] at hok; dsimp only at hok
       rcases List.mem_cons.mp hx with rfl | hx
       ·exact Or.inr (Or.inr (Or.inr ⟨w, hw⟩))
       ·exact ih hok x hx
    ·rw [qG] at hok; dsimp only at hok
     rcases List.mem_cons.mp hx with rfl | hx
     ·cases hl0 : Nat.beq lim 0
      ·rw [hl0] at qG; dsimp only at qG
       exact Or.inr (Or.inr (Or.inl ⟨(zet _ _).mp hl0, zeq qG⟩))
      ·rw [hl0] at qG; simp at qG
     ·exact ih hok x hx
   ·rw [h2] at hok; dsimp only at hok
    rcases List.mem_cons.mp hx with rfl | hx
    ·exact Or.inr (Or.inl (Nat.eq_of_beq_eq_true h2))
    ·exact ih hok x hx
  ·rw [h1] at hok; dsimp only at hok
   rcases List.mem_cons.mp hx with rfl | hx
   ·exact Or.inl (Nat.eq_of_beq_eq_true h1)
   ·exact ih hok x hx
theorem zgD (zg : List (List ℕ)) (ops : List (ℕ × ℕ × ℕ)) :
  zfK zg ops = ops.map (fun x => (x.1, x.2.1, x.2.2, zfu x.1 zg)) := by
 induction ops with
 | nil => rfl
 | cons p qa ih =>
  rcases p with ⟨op, eg, b⟩
  simp [zfK, ih]
theorem zgE {maskYF : ℕ} {b : List ℕ} {qf : List zeZ}
  {qv zL : List ℕ} {zg : List (List ℕ)} {ops : List (ℕ × ℕ × ℕ)} {qF : List ℕ}
  (hok : zfN maskYF b qf qv zL (zfK zg ops) qF = true)
  (hpw : ops.Pairwise (fun x y => y.2.2 ≤ x.2.2))
  {x y : ℕ × ℕ × ℕ} (hx : x ∈ ops) (hy : y ∈ ops) (hne : x.1 ≠ y.1) :
  ∃ p q : ℕ × ℕ × ℕ, ((p = x ∧ q = y) ∨ (p = y ∧ q = x)) ∧ q.2.2 ≤ p.2.2 ∧
   let lim := zfG zL p.2.2
   ((p.2.1 &&& q.2.1 = p.2.1) ∨ (p.2.1 &&& q.2.1 = q.2.1) ∨
    (lim ≠ 0 ∧ p.1 ||| q.1 < lim) ∨
    ∃ w, zfL maskYF b qf qv (p.2.1 ||| q.2.1) (p.1 ||| q.1)
     (zfu p.1 zg) (zfu q.1 zg) w = true) := by
 induction ops generalizing qF with
 | nil => simp at hx
 | cons z qa ih =>
  rcases z with ⟨oi, egi, bi⟩
  simp only [zfK, zfN] at hok
  cases hinner : zfM maskYF b qf qv oi egi (zfG zL bi)
    (zfu oi zg) (zfK zg qa) qF with
  | none => rw [hinner] at hok; simp at hok
  | some zV =>
   rw [hinner] at hok
   obtain ⟨hhead_pw, htail_pw⟩ := List.pairwise_cons.mp hpw
   have xb : ∀ u ∈ qa, (u.1, u.2.1, u.2.2, zfu u.1 zg) ∈ zfK zg qa := by
    intro u hu
    rw [zgD]
    exact List.mem_map.mpr ⟨u, hu, rfl⟩
   rcases List.mem_cons.mp hx with rfl | hx' <;> rcases List.mem_cons.mp hy with rfl | hy'
   ·exact (hne rfl).elim
   ·exact ⟨(oi, egi, bi), y, Or.inl ⟨rfl, rfl⟩, hhead_pw y hy',
     zgC hinner _ (xb y hy')⟩
   ·exact ⟨(oi, egi, bi), x, Or.inr ⟨rfl, rfl⟩, hhead_pw x hx',
     zgC hinner _ (xb x hx')⟩
   ·exact ih hok htail_pw hx' hy'
theorem zgF {n : ℕ} {H F : List (ℕ × ℕ)} {cuts : List zeF}
  {pre suf zM qF qv : List ℕ} {g : ℕ} {qm : List (List ℕ)}
  (hv : zcC n H F)
  (vf : ∀ cut ∈ cuts, ∀ (z6 xc : List ℕ),
   zdl (univYF n F) (rawYF n (univYF n F)) (zcy n H (univYF n F)) (z6 ++ xc) →
   (z6 ++ xc).length + 2 ≤ H.length →
   cut.loss ≤ zew cut.steps z6 → False)
  (xZ : ∀ tbl ∈ qm, zdT (univYF n F) (zcy n H (univYF n F)) (rawYF n (univYF n F)) tbl)
  (yX : ∀ tbl ∈ qm, ∀ h ∈ pre, zdN tbl h = h)
  (qj : zdl (univYF n F) (rawYF n (univYF n F)) (zcy n H (univYF n F)) (pre ++ g :: suf))
  (qe : (pre ++ g :: suf).length + 2 ≤ H.length)
  (qz : ∀ k' < (pre ++ g :: suf).length, ¬ zcT n H F k')
  (qG : ∀ gs', gs'.length = (pre ++ g :: suf).length →
   zdl (univYF n F) (rawYF n (univYF n F)) (zcy n H (univYF n F)) gs' →
   ¬ List.Lex (·< ·) gs' (pre ++ g :: suf))
  (hok : zfU (univYF n F) (zcz H) (zcy n H (univYF n F))
   (rawYF n (univYF n F)) (zcB n H (univYF n F)) cuts pre
   (zfX qm) zM qF qv = true) :
  g ∈ qv := by
 set M := univYF n F
 set ep := zcz H
 set edgeTT := zcy n H M
 set raw := rawYF n M
 set masksTT := zcB n H M
 have hvp : zdk M raw pre := (zdr.mp qj).1
 obtain ⟨a, b, hgab, hab, ha, hb, ha0, haM, haep, hb0, hbM, hbep⟩ := zdK hv qj qz
 have xB := zgq hv hvp
 obtain ⟨ba, hba⟩ := xB.2.2 a ha ha0 haM haep
 obtain ⟨bb, hbb⟩ := xB.2.2 b hb hb0 hbM hbep
 have vg : ∀ (p q : ℕ × ℕ × ℕ),
   p ∈ zfD M ep masksTT pre → q ∈ zfD M ep masksTT pre →
   p.1 ||| q.1 = g → q.2.2 ≤ p.2.2 →
   ((p.2.1 &&& q.2.1 = p.2.1) ∨ (p.2.1 &&& q.2.1 = q.2.1) ∨
    (zfG (zfF pre) p.2.2 ≠ 0 ∧ p.1 ||| q.1 < zfG (zfF pre) p.2.2) ∨
    (zfe g qv = true ∨
    zfh (p.2.1 ||| q.2.1) g M (raw ++ pre) = true ∨
    (∃ tbl ∈ qm, zdN tbl g < g) ∨
    ∃ cut ∈ cuts, cut.loss ≤ zew cut.steps (pre ++ [g]))) →
   g ∈ qv := by
  intro p q hp hq hpg hqp uj
  obtain ⟨hpe, hpb, hpM⟩ := xB.1 p hp
  obtain ⟨hqe, hqb, hqM⟩ := xB.1 q hq
  have wX : ∀ z ∈ raw ++ pre.take q.2.2, z ∈ raw ++ pre.take p.2.2 := by
   intro z hz
   rcases List.mem_append.mp hz with hz | hz
   ·exact List.mem_append_left _ hz
   ·refine List.mem_append_right _ ?_
    have x8 : pre.take q.2.2 = (pre.take p.2.2).take q.2.2 := by
     rw [List.take_take, Nat.min_eq_left hqp]
    rw [x8] at hz
    exact List.mem_of_mem_take hz
  have uK : MeetNat M (raw ++ pre.take p.2.2) q.1 := zdn wX hqM
  have vw : MeetNat M (raw ++ pre) q.1 :=
   zdn (fun z hz => (List.mem_append.mp hz).elim
    (List.mem_append_left _) (fun h => List.mem_append_right _ (List.mem_of_mem_take h))) hqM
  have vv : MeetNat M (raw ++ pre) p.1 :=
   zdn (fun z hz => (List.mem_append.mp hz).elim
    (List.mem_append_left _) (fun h => List.mem_append_right _ (List.mem_of_mem_take h))) hpM
  rcases uj with yE | yF | ⟨hlim0, hlt⟩ | qo | hon | ⟨tbl, x9, hltp⟩ | ⟨cut, zw, yA⟩
  ·rw [hpe, hqe] at yE
   exact (zd2 hv qj qz vw hpg.symm yE).elim
  ·rw [hpe, hqe, Nat.and_comm] at yF
   exact (zd2 hv qj qz vv (Nat.or_comm _ _ ▸ hpg.symm) yF).elim
  ·rw [hpg] at hlt
   obtain ⟨t, hpt, htlt, hgt⟩ := zgs pre p.2.2 g hlim0 hlt
   exact (zd1 qj qG hpt htlt hpM uK hpg.symm hgt).elim
  ·exact (zfY g qv).mp qo
  ·exfalso
   have wF : p.2.1 ||| q.2.1 = g &&& ep := by
    rw [hpe, hqe, ← hpg]
    apply Nat.eq_of_testBit_eq; intro s
    simp only [Nat.testBit_and, Nat.testBit_or]
    cases p.1.testBit s <;> cases q.1.testBit s <;> cases ep.testBit s <;> decide
   rw [wF] at hon
   have tx : zdc M ep (raw ++ pre) g = true := by
    unfold zdc
    rw [zep]
    exact zf1 (g &&& ep) g M (raw ++ pre) hon
   have hno : zdc M ep (raw ++ pre) g = false := zdB hv qj qz
   exact Bool.noConfusion (tx.symm.trans hno)
  ·exact (zdY (xZ tbl x9) (yX tbl x9) qj qG hltp).elim
  ·exfalso
   have zU : zdl M raw edgeTT ((pre ++ [g]) ++ suf) := by simpa [List.append_assoc] using qj
   have q9 : ((pre ++ [g]) ++ suf).length + 2 ≤ H.length := by simpa [List.append_assoc] using qe
   exact vf cut zw (pre ++ [g]) suf zU q9 yA
 unfold zfU at hok
 dsimp only at hok
 cases hfin : zfg M (raw ++ pre) edgeTT
 ·rw [hfin] at hok; dsimp only at hok
  cases hst : zfX qm with
  | nil =>
   rw [hst] at hok; dsimp only at hok
   obtain ⟨p, q, hpq, hqp, hres⟩ := zgB hok xB.2.1 hba hbb hab
   have hpg : p.1 ||| q.1 = g := by
    rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    ·exact hgab.symm
    ·rw [Nat.or_comm]; exact hgab.symm
   have ym : p ∈ zfD M ep masksTT pre := by
    rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
   have yo : q ∈ zfD M ep masksTT pre := by
    rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
   apply vg p q ym yo hpg hqp
   rcases hres with h1 | h2 | h3 | ⟨w, hw⟩
   ·exact Or.inl h1
   ·exact Or.inr (Or.inl h2)
   ·exact Or.inr (Or.inr (Or.inl h3))
   ·refine Or.inr (Or.inr (Or.inr ?_))
    rw [hpg] at hw
    match w, hw with
    | 0, hw => exact Or.inl hw
    | 1, hw => exact Or.inr (Or.inl hw)
    | 2, hw => simp [zfH] at hw
    | w3 + 3, hw =>
     simp only [zfH] at hw
     obtain ⟨cut, zw, hkw⟩ := zgz hw
     exact Or.inr (Or.inr (Or.inr ⟨cut, zw, zgf cut pre (Nat.land w3 7) g hkw⟩))
  | cons hd tl =>
   rw [hst] at hok; dsimp only at hok
   rw [← hst] at hok
   obtain ⟨p, q, hpq, hqp, hres⟩ := zgE hok xB.2.1 hba hbb hab
   have hpg : p.1 ||| q.1 = g := by
    rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    ·exact hgab.symm
    ·rw [Nat.or_comm]; exact hgab.symm
   have ym : p ∈ zfD M ep masksTT pre := by
    rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
   have yo : q ∈ zfD M ep masksTT pre := by
    rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
   apply vg p q ym yo hpg hqp
   rcases hres with h1 | h2 | h3 | ⟨w, hw⟩
   ·exact Or.inl h1
   ·exact Or.inr (Or.inl h2)
   ·exact Or.inr (Or.inr (Or.inl h3))
   ·refine Or.inr (Or.inr (Or.inr ?_))
    match w, hw with
    | 0, hw => exact Or.inl (hpg ▸ hw)
    | 1, hw => exact Or.inr (Or.inl (hpg ▸ hw))
    | 2, hw =>
     simp only [zfL] at hw
     obtain ⟨tbl, x9, hltp⟩ := zgi qm p.1 q.1 hw
     exact Or.inr (Or.inr (Or.inl ⟨tbl, x9, hpg ▸ hltp⟩))
    | w3 + 3, hw =>
     simp only [zfL] at hw
     rw [hpg] at hw
     obtain ⟨cut, zw, hkw⟩ := zgz hw
     exact Or.inr (Or.inr (Or.inr ⟨cut, zw, zgf cut pre (Nat.land w3 7) g hkw⟩))
 ·rw [hfin] at hok; simp at hok
theorem zgG {n : ℕ} {H F : List (ℕ × ℕ)} {cuts : List zeF}
  (hv : zcC n H F) (h3 : 3 ≤ H.length)
  (vf : ∀ cut ∈ cuts, ∀ (z6 xc : List ℕ),
   zdl (univYF n F) (rawYF n (univYF n F)) (zcy n H (univYF n F)) (z6 ++ xc) →
   (z6 ++ xc).length + 2 ≤ H.length →
   cut.loss ≤ zew cut.steps z6 → False) :
  ∀ (v7 : CertNode) (pre suf : List ℕ) (qm : List (List ℕ)),
   (∀ tbl ∈ qm, zdT (univYF n F) (zcy n H (univYF n F)) (rawYF n (univYF n F)) tbl) →
   (∀ tbl ∈ qm, ∀ h ∈ pre, zdN tbl h = h) →
   zdl (univYF n F) (rawYF n (univYF n F)) (zcy n H (univYF n F)) (pre ++ suf) →
   (pre ++ suf).length + 2 ≤ H.length →
   (∀ k' < (pre ++ suf).length, ¬ zcT n H F k') →
   (∀ gs', gs'.length = (pre ++ suf).length →
    zdl (univYF n F) (rawYF n (univYF n F)) (zcy n H (univYF n F)) gs' →
    ¬ List.Lex (·< ·) gs' (pre ++ suf)) →
   certDepthOk (H.length - 3) pre.length v7 = true →
   chkCheckNode (univYF n F) (zcz H) (zcy n H (univYF n F))
    (rawYF n (univYF n F)) (zcB n H (univYF n F)) cuts pre
    (zfX qm) v7 = true →
   False := by
 have yM : H ≠ [] := by intro h; simp [h] at h3
 intro v7
 induction v7 using CertNode.rec
   (motive_2 := fun ch =>
    ∀ (pre suf : List ℕ) (g : ℕ) (qm : List (List ℕ)),
     (∀ tbl ∈ qm, zdT (univYF n F) (zcy n H (univYF n F)) (rawYF n (univYF n F)) tbl) →
     (∀ tbl ∈ qm, ∀ h ∈ pre, zdN tbl h = h) →
     zdl (univYF n F) (rawYF n (univYF n F)) (zcy n H (univYF n F)) (pre ++ g :: suf) →
     (pre ++ g :: suf).length + 2 ≤ H.length →
     (∀ k' < (pre ++ g :: suf).length, ¬ zcT n H F k') →
     (∀ gs', gs'.length = (pre ++ g :: suf).length →
      zdl (univYF n F) (rawYF n (univYF n F)) (zcy n H (univYF n F)) gs' →
      ¬ List.Lex (·< ·) gs' (pre ++ g :: suf)) →
     g ∈ zfO ch →
     certListDepthOk (H.length - 3) (pre.length + 1) ch = true →
     chkCheckChildren (univYF n F) (zcz H) (zcy n H (univYF n F))
      (rawYF n (univYF n F)) (zcB n H (univYF n F)) cuts pre
      (zfX qm) ch = true →
     False) with
 | term =>
  intro pre suf qm _ _ qj qe qz _ zj q8
  simp only [certDepthOk] at zj
  simp only [chkCheckNode] at q8
  have tJ : H.length - 3 ≤ pre.length := Nat.le_of_ble_eq_true zj
  simp only [List.length_append] at qe
  have xG : suf.length ≤ 1 := by omega
  exact zgx hv yM qj qz xG q8
 | branch zM witsChunks children ih_ch =>
  intro pre suf qm zH zG qj qe qz qG zj q8
  simp only [certDepthOk] at zj
  simp only [chkCheckNode] at q8
  cases hlay : zfU (univYF n F) (zcz H) (zcy n H (univYF n F))
    (rawYF n (univYF n F)) (zcB n H (univYF n F)) cuts pre
    (zfX qm) zM (zfd witsChunks) (zfO children)
  ·rw [hlay] at q8; simp at q8
  ·rw [hlay] at q8; dsimp only at q8
   cases suf with
   | nil =>
    obtain ⟨_, hend⟩ := zdr.mp qj
    have hm := hend.2
    rw [← zf0 _ (zcP n H F)] at hm
    unfold zfU at hlay
    dsimp only at hlay
    rw [hm] at hlay
    simp at hlay
   | cons g xc =>
    have yi := zgF hv vf zH zG qj qe qz qG hlay
    exact ih_ch pre xc g qm zH zG qj qe qz qG yi zj q8
 | nil =>
  rename_i pre suf g qm zH zG qj qe qz qG qo zj q8
  simp [zfO] at qo
 | cons g₀ ch qa ih_node ih_rest =>
  rename_i pre suf g qm zH zG qj qe qz qG qo zj q8
  simp only [certListDepthOk, Bool.and_eq_true] at zj
  simp only [chkCheckChildren] at q8
  cases zi : chkCheckNode (univYF n F) (zcz H) (zcy n H (univYF n F))
    (rawYF n (univYF n F)) (zcB n H (univYF n F)) cuts (pre ++ [g₀])
    (zfw g₀ (zfX qm)) ch
  ·rw [zi] at q8; simp at q8
  ·rw [zi] at q8; dsimp only at q8
   simp only [zfO, List.mem_cons] at qo
   rcases qo with rfl | hmem'
   ·rw [zgj] at zi
    let vN := qm.filter (fun tbl => Nat.beq (zdN tbl g) g)
    have vD : ∀ tbl ∈ vN, zdT (univYF n F) (zcy n H (univYF n F))
      (rawYF n (univYF n F)) tbl :=
     fun tbl x9 => zH tbl (List.mem_of_mem_filter x9)
    have vC : ∀ tbl ∈ vN, ∀ h ∈ pre ++ [g], zdN tbl h = h := by
     intro tbl x9 h hh
     obtain ⟨ht_mem, ht_eq⟩ := List.mem_filter.mp x9
     rcases List.mem_append.mp hh with hh | hh
     ·exact zG tbl ht_mem h hh
     ·rw [List.mem_singleton.mp hh]; exact Nat.eq_of_beq_eq_true ht_eq
    have zU : zdl (univYF n F) (rawYF n (univYF n F)) (zcy n H (univYF n F))
      ((pre ++ [g]) ++ suf) := by simpa [List.append_assoc] using qj
    have q9 : ((pre ++ [g]) ++ suf).length + 2 ≤ H.length := by
     simpa [List.append_assoc] using qe
    have uD : ∀ k' < ((pre ++ [g]) ++ suf).length, ¬ zcT n H F k' := by
     simpa [List.append_assoc] using qz
    have xQ : ∀ gs', gs'.length = ((pre ++ [g]) ++ suf).length →
      zdl (univYF n F) (rawYF n (univYF n F)) (zcy n H (univYF n F)) gs' →
      ¬ List.Lex (·< ·) gs' ((pre ++ [g]) ++ suf) := by
     simpa [List.append_assoc] using qG
    have vU : certDepthOk (H.length - 3) (pre ++ [g]).length ch = true := by
     simpa using zj.1
    exact ih_node (pre ++ [g]) suf vN vD vC zU q9 uD xQ vU zi
   ·exact ih_rest pre suf g qm zH zG qj qe qz qG hmem' zj.2 q8
def zgH (n : ℕ) (H F : List (ℕ × ℕ)) (qn : List zeV) :
  List zeF → List zeW → Bool
 | [], [] => true
 | cut :: cuts, za :: specs =>
  match qn[za.childId]? with
  | none => false
  | some ch =>
   zeL n H F cut za.delVMask za.forbAdded za.peels
    ch.n ch.edges ch.forb za.embed &&
   zgH n H F qn cuts specs
 | _, _ => false
theorem zgI {n : ℕ} {H F : List (ℕ × ℕ)} {qn : List zeV}
  {cuts : List zeF} {specs : List zeW}
  (hok : zgH n H F qn cuts specs = true)
  (xr : ∀ za ∈ specs, ∀ ch, qn[za.childId]? = some ch →
   zcU ch.n ch.edges ch.forb (ch.edges.length - 1)) :
  ∀ cut ∈ cuts, ∀ (z6 xc : List ℕ),
   zdl (univYF n F) (rawYF n (univYF n F)) (zcy n H (univYF n F)) (z6 ++ xc) →
   (z6 ++ xc).length + 2 ≤ H.length →
   cut.loss ≤ zew cut.steps z6 → False := by
 induction cuts generalizing specs with
 | nil => intro _ hc; simp at hc
 | cons cut qa ih =>
  cases specs with
  | nil => simp [zgH] at hok
  | cons za srest =>
   simp only [zgH] at hok
   cases hst : qn[za.childId]? with
   | none => rw [hst] at hok; simp at hok
   | some ch =>
    rw [hst] at hok
    simp only [Bool.and_eq_true] at hok
    intro c hc z6 xc qj qe yA
    rcases List.mem_cons.mp hc with rfl | hc'
    ·exact zeO hok.1 (xr za List.mem_cons_self ch hst) qj qe yA
    ·exact ih hok.2 (fun s hs => xr s (List.mem_cons_of_mem _ hs)) c hc' z6 xc qj qe yA
theorem zgJ {desc : zeV} {maskYF edgePts edgeTT : ℕ}
  {raw masksTT : List ℕ} {autIdxTbls auts : List (List ℕ)}
  {cuts : List zeF} {specs : List zeW} {qn : List zeV}
  {cert : CertNode}
  (hv : zcC desc.n desc.edges desc.forb)
  (h3 : 3 ≤ desc.edges.length)
  (hM : maskYF = univYF desc.n desc.forb)
  (hEp : edgePts = zcz desc.edges)
  (hEt : edgeTT = zcy desc.n desc.edges maskYF)
  (wr : raw = rawYF desc.n maskYF)
  (wq : masksTT = zcB desc.n desc.edges maskYF)
  (y4 : auts = zfX autIdxTbls)
  (y3 : ∀ tbl ∈ autIdxTbls, zdT maskYF edgeTT raw tbl)
  (vO : zgH desc.n desc.edges desc.forb qn cuts specs = true)
  (zY : ∀ za ∈ specs, ∀ ch, qn[za.childId]? = some ch →
   zcU ch.n ch.edges ch.forb (ch.edges.length - 1))
  (yb : certDepthOk (desc.edges.length - 3) 0 cert = true)
  (y5 : chkCheckNode maskYF edgePts edgeTT raw masksTT cuts [] auts cert = true) :
  zcU desc.n desc.edges desc.forb (desc.edges.length - 1) := by
 subst hM hEp hEt wr wq y4
 intro k hr
 by_contra hlt
 have hle : k ≤ desc.edges.length - 2 := by omega
 obtain ⟨k₀, gs, hk₀_le, qe, qj, qz, qG⟩ :=
  zdv (bound := desc.edges.length - 2) ⟨k, hle, hr⟩
 subst qe
 have yf := zgI vO zY
 exact zgG hv h3 yf cert [] gs autIdxTbls
  y3 (fun _ _ _ h => by simp at h)
  (by simpa using qj) (by simp; omega)
  (by simpa using qz) (by simpa using qG) yb y5
structure zgK where
 desc       : zeV
 maskYF     : ℕ
 edgePts    : ℕ
 edgeTT     : ℕ
 raw        : List ℕ
 masksTT    : List ℕ
 autIdxTbls : List (List ℕ)
 auts       : List (List ℕ)
 cuts       : List zeF
 specs      : List zeW
 cert       : CertNode
def zgL (n : ℕ) (H F : List (ℕ × ℕ)) (qn : List zeV) :
  List zeF → List zeW → Bool
 | [], [] => true
 | cut :: cuts, za :: specs =>
  match qn[za.childId]? with
  | none => false
  | some ch =>
   decide (ch.edges.length < H.length) &&
   zeL n H F cut za.delVMask za.forbAdded za.peels
    ch.n ch.edges ch.forb za.embed &&
   zgL n H F qn cuts specs
 | _, _ => false
theorem zgM {n : ℕ} {H F : List (ℕ × ℕ)} {qn : List zeV}
  {cuts : List zeF} {specs : List zeW}
  (hok : zgL n H F qn cuts specs = true) :
  zgH n H F qn cuts specs = true ∧
  ∀ za ∈ specs, ∀ ch, qn[za.childId]? = some ch → ch.edges.length < H.length := by
 induction cuts generalizing specs with
 | nil =>
  cases specs with
  | nil => exact ⟨rfl, fun _ h => by simp at h⟩
  | cons _ _ => simp [zgL] at hok
 | cons cut qa ih =>
  cases specs with
  | nil => simp [zgL] at hok
  | cons za srest =>
   simp only [zgL] at hok
   cases hst : qn[za.childId]? with
   | none => rw [hst] at hok; simp at hok
   | some ch =>
    rw [hst] at hok
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨zl, hlt⟩ := ih hok.2
    refine ⟨?_, ?_⟩
    ·simp [zgH, hst, hok.1.2, zl]
    ·intro s hs ch' qR
     rcases List.mem_cons.mp hs with rfl | hs'
     ·rw [hst] at qR; cases qR; exact hok.1.1
     ·exact hlt s hs' ch' qR
def zgN (qn : List zeV) (e : zgK) : Bool :=
 if e.desc.edges.length ≤ 1 then true
 else
  decide (zcC e.desc.n e.desc.edges e.desc.forb) &&
  decide (3 ≤ e.desc.edges.length) &&
  (e.maskYF == univYF e.desc.n e.desc.forb) &&
  (e.edgePts == zcz e.desc.edges) &&
  (e.edgeTT == zcy e.desc.n e.desc.edges e.maskYF) &&
  (e.raw == rawYF e.desc.n e.maskYF) &&
  (e.masksTT == zcB e.desc.n e.desc.edges e.maskYF) &&
  (e.auts == zfX e.autIdxTbls) &&
  e.autIdxTbls.all (fun tbl => decide (zdT e.maskYF e.edgeTT e.raw tbl)) &&
  zgL e.desc.n e.desc.edges e.desc.forb qn e.cuts e.specs &&
  certDepthOk (e.desc.edges.length - 3) 0 e.cert
theorem zgO (zh : List zgK)
  (ug : ∀ e ∈ zh, zgN (zh.map zgK.desc) e = true)
  (wp : ∀ e ∈ zh, e.desc.edges.length ≤ 1 ∨
   chkCheckNode e.maskYF e.edgePts e.edgeTT e.raw e.masksTT e.cuts [] e.auts e.cert = true) :
  ∀ (i : ℕ) (ch : zeV), (zh.map zgK.desc)[i]? = some ch →
   zcU ch.n ch.edges ch.forb (ch.edges.length - 1) := by
 have v4 : ∀ m : ℕ, ∀ e ∈ zh, e.desc.edges.length = m →
   zcU e.desc.n e.desc.edges e.desc.forb (e.desc.edges.length - 1) := by
  intro m
  induction m using Nat.strong_induction_on with
  | ind m ih =>
   intro e he hm
   by_cases h1 : e.desc.edges.length ≤ 1
   ·intro k _; omega
   ·have un := ug e he
    simp only [zgN, h1, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq,
     beq_iff_eq, List.all_eq_true] at un
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hv, h3⟩, hM⟩, hEp⟩, hEt⟩, wr⟩, wq⟩, y4⟩, y3⟩, hCuts⟩, yb⟩ := un
    obtain ⟨hCutsValid, hCutsLt⟩ := zgM hCuts
    have y5 := (wp e he).resolve_left h1
    have zY : ∀ za ∈ e.specs, ∀ ch,
      (zh.map zgK.desc)[za.childId]? = some ch →
      zcU ch.n ch.edges ch.forb (ch.edges.length - 1) := by
     intro za uO ch qR
     have qo : ch ∈ zh.map zgK.desc := List.mem_of_getElem? qR
     obtain ⟨e', he', rfl⟩ := List.mem_map.mp qo
     exact ih e'.desc.edges.length (hm ▸ hCutsLt za uO e'.desc qR) e' he' rfl
    exact zgJ hv h3 hM hEp hEt wr wq y4 y3 hCutsValid zY yb y5
 intro i ch qR
 have qo : ch ∈ zh.map zgK.desc := List.mem_of_getElem? qR
 obtain ⟨e, he, rfl⟩ := List.mem_map.mp qo
 exact v4 e.desc.edges.length e he rfl
def zgP (qn : List zeV) (gc : zeX) : Bool :=
 match qn[gc.coreId]? with
 | none => false
 | some ch =>
  decide (zcC gc.n gc.edges []) &&
  zeh gc.n gc.edges [] gc.peels ch.n ch.edges ch.forb gc.embed
theorem zgQ {qn : List zeV} {xL : List zeX}
  (qf : ∀ (i : ℕ) (ch : zeV), qn[i]? = some ch →
   zcU ch.n ch.edges ch.forb (ch.edges.length - 1))
  (ya : xL.all (zgP qn) = true)
  {idx : ℕ} {gc : zeX} (qR : xL[idx]? = some gc) :
  zcC gc.n gc.edges [] ∧ zcU gc.n gc.edges [] (gc.edges.length - 1) := by
 have hok : zgP qn gc = true :=
  (List.all_eq_true.mp ya) gc (List.mem_of_getElem? qR)
 simp only [zgP] at hok
 cases hst : qn[gc.coreId]? with
 | none => rw [hst] at hok; simp at hok
 | some ch =>
  rw [hst] at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  exact ⟨hok.1, zei hok.1 hok.2 (qf gc.coreId ch hst)⟩
theorem zgR {n : ℕ} {H : List (ℕ × ℕ)} {f : (Fin n → Bool) → Bool}
  {qn : List zeV} {xL : List zeX}
  (hf : ∀ x : Fin n → Bool, f x = zeP n H x)
  (qf : ∀ (i : ℕ) (ch : zeV), qn[i]? = some ch →
   zcU ch.n ch.edges ch.forb (ch.edges.length - 1))
  (ya : xL.all (zgP qn) = true)
  (idx : ℕ) (gc : zeX) (qR : xL[idx]? = some gc)
  (hn : gc.n = n) (hH : gc.edges = H)
  (C : Circuit) (hc : Monotone2 C) (he : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x) :
  H.length - 1 ≤ zc5 C.gates := by
 obtain ⟨hv, hlb⟩ := zgQ qf ya qR
 subst hn hH
 exact zeQ (fun e heH => ⟨(hv.1 e heH).1, (hv.1 e heH).2.1⟩) hf hlb C hc he
def s1_desc : zeV := ⟨5,[(0,1),(0,4),(1,4),(2,3),(2,4),(3,4)],[]⟩
def zgS : Nat := 0xffffffff
def zgT : Nat := 0x1161008
def zgU : Nat := 0xfffef888
def s1_raw : List Nat := ze6 5 zgS
def zgV : List Nat := ze8 5 s1_desc.edges zgS
def zgW : List (List Nat) := []
def s1_auts : List (List Nat) := []
def zgX : List zeW := [⟨0,[(3,4)],[3,2],2,[0,1,4]⟩,⟨2,[],[0],2,[2,3,4]⟩,⟨3,[],[],2,[2,3,4]⟩,⟨12,[],[],2,[0,1,4]⟩]
def s1_cuts : List zeF := zfb zgS s1_raw [(1,[.e [(3,4)]]),(2,[.v 1 [9,16]]),(3,[.v 0 [6,16,10],.v 1 [16]]),(3,[.v 2 [10,16],.v 3 [16]])]
def s1_cert : CertNode := .branch [2,3,1,0] [(pl 43 5 0x1ffee23df008368085a80297 [3,11,19,27,12])] (.nil)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem zgY : chkCheckNode zgS zgT zgU s1_raw zgV s1_cuts [] s1_auts s1_cert = true := by decide +kernel
def s2_desc : zeV := ⟨3,[(0,1),(0,2),(1,2)],[]⟩
def zgZ : Nat := 0xff
def zg0 : Nat := 0x68
def zg1 : Nat := 0xe8
def s2_raw : List Nat := ze6 3 zgZ
def zg2 : List Nat := ze8 3 s2_desc.edges zgZ
def zg3 : List (List Nat) := []
def s2_auts : List (List Nat) := []
def zg4 : List zeW := []
def s2_cuts : List zeF := zfb zgZ s2_raw []
def s2_cert : CertNode := .term
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem zg5 : chkCheckNode zgZ zg0 zg1 s2_raw zg2 s2_cuts [] s2_auts s2_cert = true := by decide +kernel
def s4_desc : zeV := ⟨5,[(0,1),(0,2),(1,3),(2,4),(3,4)],[]⟩
def zg6 : Nat := 0xffffffff
def zg7 : Nat := 0x1100428
def zg8 : Nat := 0xfff8eca8
def s4_raw : List Nat := ze6 5 zg6
def zg9 : List Nat := ze8 5 s4_desc.edges zg6
def zha : List (List Nat) := []
def s4_auts : List (List Nat) := []
def zhb : List zeW := [⟨0,[(2,4)],[2,0,1],17,[3,4]⟩,⟨24,[],[1],17,[0,2]⟩,⟨7,[],[],17,[3,4]⟩]
def s4_cuts : List zeF := zfb zg6 s4_raw [(1,[.e [(2,4)]]),(3,[.v 3 [6,16],.v 4 [6]]),(4,[.v 0 [12,18],.v 1 [12],.v 2 [16]])]
def s4_cert : CertNode := .branch [2,1,0] [(pl 35 5 0x13f6c3b5f66b9316aa6c [3,11,19,12,4])] (.nil)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem zhc : chkCheckNode zg6 zg7 zg8 s4_raw zg9 s4_cuts [] s4_auts s4_cert = true := by decide +kernel
def s6_desc : zeV := ⟨6,[(0,1),(0,2),(1,4),(2,5),(3,4),(3,5),(4,5)],[]⟩
def zhd : Nat := 0xffffffffffffffff
def zhe : Nat := 0x1011001040028
def zhf : Nat := 0xfffffff8ffeca8a8
def s6_raw : List Nat := ze6 6 zhd
def zhg : List Nat := ze8 6 s6_desc.edges zhd
def zhh : List (List Nat) := []
def s6_auts : List (List Nat) := []
def zhi : List zeW := [⟨8,[],[],4,[0,1,2,4,5]⟩,⟨0,[(4,5)],[],18,[0,1,2,3,4,5]⟩,⟨5,[],[1],2,[3,4,5]⟩,⟨44,[],[0],17,[1,4]⟩,⟨7,[],[],2,[3,4,5]⟩,⟨27,[],[],17,[2,5]⟩]
def s6_cuts : List zeF := zfb zhd s6_raw [(2,[.v 3 [17,32,20]]),(1,[.e [(4,5)]]),(3,[.v 2 [17,32],.v 0 [34]]),(5,[.v 2 [1,32],.v 3 [34],.v 5 [16]]),(4,[.v 1 [9,20,33],.v 0 [20],.v 2 [32]]),(6,[.v 1 [1,20],.v 3 [17,20,32],.v 0 [20],.v 4 [32]])]
def s6_cert : CertNode := .branch [4,0,2,1] [(pl 64 7 0x8678df1b24cbc03214cc35f06c9c278f7f1a9f61d566 [3,11,19,27,0,4,20])] (.cons 0xffffffffffff0000 (.branch [5,3,1] [(pd 39 20 0x17ad5ea588c12a2e490b538f17058286a6835494b7)] (.nil)) (.nil))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem zhj : chkCheckNode zhd zhe zhf s6_raw zhg s6_cuts [] s6_auts s6_cert = true := by decide +kernel
def zhk : zeV := ⟨7,[(0,1),(0,4),(1,5),(2,4),(2,6),(3,5),(3,6),(4,6),(5,6)],[]⟩
def zhl : Nat := 0xffffffffffffffffffffffffffffffff
def zhm : Nat := 0x1000101100000010400120008
def zhn : Nat := 0xfffffffffffffff8fffeffccfafa8888
def s13_raw : List Nat := ze6 7 zhl
def zho : List Nat := ze8 7 zhk.edges zhl
def zhp : List (List Nat) := zfW 7 [[1,0,3,2,5,4,6]]
def zhq : List (List Nat) := zfX zhp
def zhr : List zeW := [⟨4,[],[],6,[0,1,4,3,5,6]⟩,⟨8,[],[],6,[1,0,5,2,4,6]⟩,⟨0,[(4,6)],[],22,[0,1,2,3,4,5,6]⟩,⟨0,[(5,6)],[],22,[1,0,3,2,5,4,6]⟩,⟨3,[],[],1,[2,4,3,5,6]⟩,⟨17,[(5,6)],[1,2,5],17,[3,6]⟩,⟨20,[(5,6)],[0,1,5],17,[3,6]⟩,⟨84,[],[0,1],17,[3,5]⟩,⟨35,[],[3],2,[2,4,6]⟩,⟨42,[],[0],2,[2,4,6]⟩,⟨21,[],[1],2,[3,5,6]⟩,⟨92,[],[0],17,[1,5]⟩,⟨108,[],[1],17,[0,4]⟩,⟨92,[],[0],17,[1,5]⟩,⟨51,[],[2],17,[3,6]⟩,⟨92,[],[0],17,[1,5]⟩,⟨23,[],[],2,[3,5,6]⟩,⟨23,[],[],2,[3,5,6]⟩,⟨55,[],[],17,[3,6]⟩,⟨55,[],[],17,[3,6]⟩,⟨107,[],[],17,[2,4]⟩,⟨55,[],[],17,[3,6]⟩,⟨110,[],[],17,[0,4]⟩,⟨59,[],[],17,[2,6]⟩,⟨93,[],[],17,[1,5]⟩,⟨124,[],[],17,[0,1]⟩]
def zhs : List zeF := zfb zhl s13_raw [(2,[.v 2 [26,65]]),(2,[.v 3 [37,65,48]]),(1,[.e [(4,6)]]),(1,[.e [(5,6)]]),(3,[.v 0 [6,48,66],.v 1 [48,36]]),(5,[.e [(5,6)],.v 4 [33],.v 0 [2,66]]),(5,[.e [(5,6)],.v 4 [33],.v 2 [65]]),(6,[.v 2 [65,26,48],.v 4 [],.v 6 [33]]),(5,[.v 0 [66,16,18],.v 1 [48],.v 5 [24]]),(5,[.v 1 [65,48,36],.v 5 [24],.v 3 [64]]),(5,[.v 2 [65,26],.v 4 [33],.v 0 [2]]),(7,[.v 3 [37,66,48,65],.v 2 [65],.v 6 [48],.v 4 [33]]),(7,[.v 3 [36,48],.v 2 [18,65,48,66],.v 6 [48],.v 5 [18]]),(7,[.v 3 [37,48,65,66],.v 4 [64],.v 2 [64],.v 6 [33]]),(7,[.v 4 [33,36],.v 0 [6],.v 1 [32],.v 5 [8]]),(7,[.v 6 [9,37,6,16],.v 2 [26,48],.v 3 [32],.v 4 [33]]),(6,[.v 0 [2,24,48],.v 2 [48,26,64],.v 1 [32],.v 4 [64]]),(6,[.v 1 [48,1],.v 2 [65],.v 0 [16],.v 4 [64]]),(8,[.v 0 [2,24,48],.v 2 [48,66,24],.v 1 [32],.v 5 [24],.v 4 [64]]),(8,[.v 1 [1,36,33],.v 2 [65,48,24],.v 5 [65],.v 0 [24],.v 4 [64]]),(8,[.v 1 [32,65,33],.v 5 [24],.v 3 [64],.v 6 [4],.v 0 [16]]),(8,[.v 2 [],.v 0 [2,48],.v 1 [32],.v 5 [24],.v 4 [64]]),(8,[.v 2 [16,66,48],.v 1 [48,1],.v 3 [32],.v 5 [64],.v 6 [16]]),(8,[.v 4 [33,36],.v 0 [2],.v 1 [32],.v 3 [32],.v 5 [64]]),(8,[.v 4 [36,33],.v 2 [64],.v 6 [33],.v 3 [32],.v 0 [2]]),(8,[.v 6 [],.v 2 [26,48],.v 3 [32],.v 5 [18],.v 4 [1]])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
def zht : CertNode := .branch [0,4,2,1,3] [(pl 64 6 0x171bd0f81aad716d1b9f7160f3080d6212e8e7e502 [2,3,19,11,27,35]),(pl 38 6 0x115ca0022983e9fa5240dd75c [2,11,3,12,0,27])] (.cons 0xffffffffffffffffffff0000ffff0000 (.branch [16,1,2,3,17] [(pl 64 8 0x6706400000000074924032650092402492410d1a03489811 [3,11,4,35,19,27,0,36]),[3,0,1]] (.cons 0xffffffffffffffffffffffffffff0000 (.branch [19,13,2,3] [(pl 64 8 0x25c4680000000000000102921c12e229024924609384a241 [3,11,4,19,27,5,6,12]),(pd 13 15 0xa6e41c3881de)] (.nil)) (.cons 0xffffffffffffffffffffffff00000000 (.branch [22,11,4,2,3] [(pl 64 6 0x97fbcc02748edd0d6271724d59d661d17ccfc430e [3,11,19,1,4,27]),(pl 64 8 0x40b69004cad02c00000380000012492930252712130624c0 [3,11,19,4,27,35,0,1]),(pd 12 20 0xfb16a5b3a79f)] (.cons 0xfff0fff0fff0fff0fff0ff00f0f00000 (.branch [12,22,4,2,3] [(pl 64 7 0x2b73a8fc4901188e42c5062b4a1469cb989b89d258456 [1,4,11,19,3,27,35]),(pl 64 8 0x405cc241004a4524df37351150900800004800804120a44a [3,1,4,19,11,27,35,12]),(pl 64 7 0x3a69a14577207f357a65f6e6c2681e731c1a1e3eea001 [3,4,1,19,11,27,35]),(pl 64 8 0x20000249292ee222922592492012592592c06000000000c0 [3,11,4,1,19,12,27,35]),(pl 64 7 0xa018401fb00628fe391a046bcf1868042271e9306701 [11,3,12,19,1,27,35]),(pd 11 20 0xc906f8dee7b)] (.nil)) (.nil))) (.nil)))) (.cons 0xffffffffffff0000ffffffffffff0000 (.branch [10,8] [(pd 64 14 0xa3023fda240ac719e733f3ec09ec3412d2977afe24d71040c12d32b5a34bc),(pd 31 12 0x169da6a47b9c02b00000da4b2c0a)] (.cons 0xfffffffffffff0f0f0f0f0f0f0f0f0f0 (.branch [15,14,9,1,6] [(pl 64 8 0x2482012454194500c4a83804000000000007519211418c98 [3,11,19,27,1,4,12,37]),(pl 44 8 0xc1145c600083e054cc08a6254c9049 [3,11,19,27,4,12,0,1])] (.cons 0xffffffffffffffffffff0000ffff0000 (.branch [21,11,6,9,15] [(pl 64 8 0x16cb2865c48b50c46d1632c04a16142111f61832d205a281 [3,4,11,27,1,20,36,21]),(pl 64 7 0x29cf2ff56f32461fc06acdbd7575eeafa7739122b8f9c [3,4,11,27,1,35,19]),(pl 64 5 0x613c0fbffb56d7ac8b8551b934e6fdde5ec20 [11,3,1,4,27]),(pl 41 7 0x68be480fffb71ff0115e895379cd4 [3,27,35,11,4,1,19])] (.nil)) (.nil))) (.cons 0xffffffffffffaaaaaaaaaaaaaaaaaaaa (.branch [24,20,10,1,5] [(pl 64 9 0x1b2d6e25bb4814a740faf0dcd1de6fd22629bdc7fc7 [3,11,27,19,1,5,12,14,37]),(pl 64 8 0x20aa1a8d40d7db341a3602d2a1a000041001000001249249 [11,3,27,19,5,21,36,1]),[11,5,0,27,19,11,5]] (.cons 0xffffffffffffffffffff0000ffff0000 (.branch [7,5,9,1] [(pl 64 8 0x8db9b12024422d0adb8690129484656a88429f1202442210 [3,19,27,12,1,11,4,5]),(pl 64 7 0x2b8f4af738551d3a6dd45bdd95322b10bc64758e34b9f [3,27,19,1,4,12,11]),(pl 64 9 0x15edb603f583d98343bf10629b8c3bac845e1c0734e78e9f307 [27,3,19,4,1,12,13,11,20]),(pd 48 28 0x4a3ad385b40d12eac61b33735b601b2b7029afa575917445c7487524b)] (.nil)) (.nil))) (.cons 0xffffffffffffffffffffffffffff0000 (.branch [23,12,4,15] [(pl 64 7 0x98882a623821b356525d0c2d69aa169a1be8d99256ea [2,3,19,12,11,27,20]),(pd 16 20 0x37a1e9743da95c00b)] (.nil)) (.cons 0xffffffffffffffffffff0000ffff0000 (.branch [18,11,9,2] [(pl 64 7 0x76532bd444b059f6227bdcc97f53af073824ec6e06e13 [3,4,11,19,1,12,27]),(pl 64 9 0x13d5f30bab69721b1d1d8b02108050af16554cfc42 [3,11,4,19,0,1,12,20,27]),(pd 18 21 0xa974b202d09b9e9f271)] (.cons 0xfffffffffffff0f0f0f00000f0f00000 (.branch [25,5,9,1,6] [(pl 64 6 0xb5647baa481a0dc4cc819a6e75aa68ca6509fc697 [3,1,4,19,27,12]),(pl 64 8 0x42200500aa0000724111c4068b20d90488e042b8ab0ab241 [3,4,27,12,19,1,13,37]),(pd 9 28 0x61c7b6a597)] (.nil)) (.nil))) (.nil)))))) (.nil)))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem zhu : chkCheckNode zhl zhm zhn s13_raw zho zhs [] zhq zht = true := by decide +kernel
def zhv : zeV := ⟨7,[(0,3),(0,4),(1,3),(1,5),(2,3),(2,6),(4,5),(4,6),(5,6)],[]⟩
def zhw : Nat := 0xffffffffffffffffffffffffffffffff
def zhx : Nat := 0x1000100100001000400021600
def zhy : Nat := 0xfffffffffffffef0fffffeccfeaafe00
def s14_raw : List Nat := ze6 7 zhw
def zhz : List Nat := ze8 7 zhv.edges zhw
def zhA : List (List Nat) := zfW 7 [[0,2,1,3,4,6,5],[1,0,2,3,5,4,6],[1,2,0,3,5,6,4],[2,0,1,3,6,4,5],[2,1,0,3,6,5,4]]
def zhB : List (List Nat) := zfX zhA
def zhC : List zeW := [⟨8,[],[0,1,2],2,[4,5,6]⟩,⟨32,[],[1],4,[0,3,4,2,6]⟩,⟨64,[],[2],4,[0,3,4,1,5]⟩,⟨1,[],[],6,[3,1,2,4,5,6]⟩,⟨2,[],[],6,[3,0,2,5,4,6]⟩,⟨4,[],[],6,[3,0,1,6,4,5]⟩,⟨0,[(4,5)],[],23,[0,1,2,4,5,3,6]⟩,⟨0,[(4,6)],[],23,[0,2,1,4,6,3,5]⟩,⟨0,[(5,6)],[],23,[1,2,0,5,6,3,4]⟩,⟨48,[],[0,1,3],17,[2,6]⟩,⟨48,[],[0,1,3],17,[2,6]⟩,⟨80,[],[0,2,3],17,[1,5]⟩,⟨24,[],[1,2],17,[5,6]⟩,⟨24,[],[1,2],17,[5,6]⟩,⟨40,[],[0,2],17,[4,6]⟩,⟨17,[],[],4,[1,3,5,2,6]⟩,⟨34,[],[],4,[0,3,4,2,6]⟩,⟨17,[],[],4,[1,3,5,2,6]⟩,⟨25,[],[1,2],17,[5,6]⟩,⟨81,[],[2,3],17,[1,5]⟩,⟨112,[],[0,1],17,[2,3]⟩,⟨112,[],[0,1],17,[2,3]⟩,⟨13,[],[1],2,[4,5,6]⟩,⟨14,[],[0],2,[4,5,6]⟩,⟨14,[],[0],2,[4,5,6]⟩,⟨51,[],[3],17,[2,6]⟩,⟨29,[],[1],17,[5,6]⟩,⟨102,[],[3],17,[0,4]⟩,⟨102,[],[3],17,[0,4]⟩,⟨43,[],[2],17,[4,6]⟩,⟨78,[],[0],17,[4,5]⟩,⟨116,[],[0],17,[1,3]⟩,⟨51,[],[3],17,[2,6]⟩,⟨106,[],[],17,[0,4]⟩,⟨92,[],[],17,[1,5]⟩,⟨92,[],[],17,[1,5]⟩,⟨92,[],[],17,[1,5]⟩,⟨89,[],[],17,[1,5]⟩,⟨15,[],[],2,[4,5,6]⟩,⟨15,[],[],2,[4,5,6]⟩,⟨59,[],[],17,[2,6]⟩,⟨93,[],[],17,[1,5]⟩,⟨93,[],[],17,[1,5]⟩,⟨93,[],[],17,[1,5]⟩,⟨93,[],[],17,[1,5]⟩,⟨59,[],[],17,[2,6]⟩,⟨115,[],[],17,[2,3]⟩,⟨59,[],[],17,[2,6]⟩,⟨110,[],[],17,[0,4]⟩,⟨110,[],[],17,[0,4]⟩,⟨110,[],[],17,[0,4]⟩,⟨93,[],[],17,[1,5]⟩,⟨79,[],[],17,[4,5]⟩,⟨93,[],[],17,[1,5]⟩,⟨59,[],[],17,[2,6]⟩,⟨115,[],[],17,[2,3]⟩,⟨93,[],[],17,[1,5]⟩,⟨93,[],[],17,[1,5]⟩,⟨93,[],[],17,[1,5]⟩]
def zhD : List zeF := zfb zhw s14_raw [(3,[.v 3 [18,37,65]]),(3,[.v 5 [24,22,72]]),(3,[.v 6 [40,7,24,20,33]]),(2,[.v 0 [72,22]]),(2,[.v 1 [24,32,8]]),(2,[.v 2 [24,64]]),(1,[.e [(4,5)]]),(1,[.e [(4,6)]]),(1,[.e [(5,6)]]),(5,[.v 4 [40,72,32],.v 5 [2,72]]),(5,[.v 5 [16],.v 4 [65]]),(5,[.v 6 [20,16],.v 4 [40,33]]),(6,[.v 3 [20,18],.v 4 [37,3,32]]),(6,[.v 4 [40,72],.v 3 []]),(6,[.v 5 [24,72],.v 3 []]),(4,[.v 0 [72,18],.v 4 [32]]),(4,[.v 1 [72,32,24,40],.v 5 [72,16,64]]),(4,[.v 4 [40,37,72],.v 0 [8]]),(6,[.v 0 [8],.v 3 [18],.v 4 [36,66]]),(6,[.v 0 [8,16,40,72],.v 4 [],.v 6 [36]]),(6,[.v 4 [],.v 5 [67,72],.v 6 [6]]),(6,[.v 5 [24,72],.v 6 [24],.v 4 []]),(5,[.v 0 [40,18],.v 2 [40,64],.v 3 [18]]),(5,[.v 1 [37,8,24],.v 2 [65],.v 3 [65]]),(5,[.v 2 [64,24,72],.v 1 [33],.v 3 []]),(7,[.v 0 [40,16],.v 1 [40,32,8],.v 4 [40],.v 5 [72]]),(7,[.v 0 [],.v 2 [],.v 4 [40],.v 3 []]),(7,[.v 1 [37,72,24],.v 2 [64],.v 5 [24],.v 6 [24]]),(7,[.v 1 [32,8,24],.v 2 [64,24,40,72],.v 6 [24,40],.v 5 [24]]),(7,[.v 1 [72,37,24,40],.v 5 [72,16],.v 0 [20],.v 3 [20]]),(7,[.v 2 [67,24,40,72],.v 1 [32],.v 6 [24],.v 3 []]),(7,[.v 2 [],.v 6 [24],.v 4 [40],.v 5 []]),(7,[.v 4 [],.v 1 [33,72,40],.v 0 [40],.v 5 [72]]),(8,[.v 1 [32,8,24],.v 5 [24],.v 3 [65],.v 6 [16,5]]),(8,[.v 2 [8],.v 3 [18],.v 4 [3,33],.v 6 [32]]),(8,[.v 2 [65,40,72],.v 6 [32],.v 3 [18],.v 4 [1]]),(8,[.v 6 [4,32],.v 2 [40],.v 3 [18],.v 4 [3]]),(8,[.v 6 [],.v 3 [1,18],.v 0 [16],.v 4 [32]]),(6,[.v 0 [],.v 2 [64,24,72],.v 3 [],.v 1 [32]]),(6,[.v 1 [32,72,40],.v 0 [8],.v 3 [20],.v 2 [64]]),(8,[.v 0 [16,72,24,40],.v 1 [36,24,40,72],.v 5 [24,72],.v 3 [20],.v 4 [64]]),(8,[.v 0 [40,16],.v 2 [8],.v 3 [18],.v 4 [66],.v 6 [32]]),(8,[.v 0 [],.v 2 [],.v 4 [40],.v 3 [],.v 6 [32]]),(8,[.v 0 [22,72,8,24],.v 2 [66,24,72,8],.v 6 [40,24],.v 3 [18],.v 4 [32]]),(8,[.v 0 [20,72,24],.v 6 [4],.v 2 [24,8],.v 3 [18],.v 4 [32]]),(8,[.v 1 [8,36,40],.v 0 [16,40,24],.v 4 [40],.v 3 [36],.v 5 [64]]),(8,[.v 1 [8,72,32],.v 0 [8],.v 4 [72],.v 5 [72],.v 6 [4]]),(8,[.v 1 [],.v 0 [20,72,40,24],.v 5 [24],.v 3 [20],.v 4 [64]]),(8,[.v 1 [8,37,72],.v 2 [8,64,40],.v 3 [65,33],.v 6 [33],.v 5 [16]]),(8,[.v 1 [],.v 2 [],.v 5 [24],.v 3 [],.v 6 [16]]),(8,[.v 1 [33,24],.v 6 [24,4],.v 2 [8],.v 3 [33],.v 5 [16]]),(8,[.v 2 [64,8,72],.v 0 [18,72,40,24],.v 6 [24,40],.v 3 [18],.v 4 [32]]),(8,[.v 2 [],.v 1 [33,24,72,40],.v 6 [40],.v 3 [],.v 0 [16]]),(8,[.v 2 [],.v 6 [],.v 0 [40,16],.v 3 [18],.v 4 [32]]),(8,[.v 4 [72,40],.v 1 [33,8,40],.v 0 [40],.v 3 [36],.v 5 [64]]),(8,[.v 4 [],.v 1 [37,8,40],.v 0 [72,8,40],.v 5 [72],.v 6 [4]]),(8,[.v 4 [40,72],.v 6 [40,4],.v 0 [8,40],.v 2 [40],.v 3 [2]]),(8,[.v 6 [6,33],.v 0 [8,20,40],.v 2 [24,40],.v 3 [18],.v 4 [32]]),(8,[.v 6 [37,22,4],.v 2 [],.v 0 [40],.v 3 [2],.v 4 [32]])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
def zhE : CertNode := .branch [3,4,6,7,8] [(pl 64 6 0x73bffa999648b84ed467405b298dae1b11b7d4500 [2,3,11,19,27,35]),(pl 38 4 0x4106300c00010441881 [2,3,11,0])] (.cons 0xffffffffffff0000ffffffffffff0000 (.branch [15,5,6,1] [(pl 64 8 0xc434812038434886c1209209241028040038282541203708 [2,3,0,11,19,27,1,4])] (.cons 0xffffffffffffff00ff00ff00ff00ff00 (.branch [43,6,27] [(pl 64 8 0x4a334d4001800000c0003213e090128410884f02404a1042 [2,3,4,1,11,19,21,5]),(pl 64 7 0xae513adebbedfbe77d03ed3b30c853e0d238d2dfc97 [2,3,4,19,5,11,20]),(pd 29 12 0x4287b14491071529da378b777b)] (.nil)) (.cons 0xfffffffffffff0f0f0f0f0f0f0f0f0f0 (.branch [44,6,5,2] [(pl 64 8 0x4d02526ec290002000004004c27c0901d64322240901ca43 [2,3,5,19,1,11,27,0]),(pd 51 28 0x3f702172b9dd531ab456646b01086ccd0e0fc824a7bd0cba1479589d76477)] (.cons 0xfffffffffffffff0ff00ff00ff00ff00 (.branch [44,28,6,9] [(pd 64 28 0x1663a19f45aaf0b63347722159db281d31edfe7f53922afeae3386547246726f109aca553c7b6),(pl 64 9 0x824f26ef3fb3a1d76952adb951000c60c07896b02624757 [2,1,3,4,19,12,5,27,28]),(pl 64 8 0x600000600347a212064291109082d204b69685a85a000400 [2,3,27,11,1,12,19,4]),(pl 62 8 0x149900955829207906e04804004000800000810c248249 [3,2,1,4,11,19,6,27])] (.cons 0xfffffffffffffafafaaafaaafaaafaaa (.branch [53,27,6] [(pl 64 6 0x138991a5e3990e2f96769f63f41234382e9df11927 [1,4,5,11,3,19]),(pl 64 6 0x196533dc0385b6a0b398423529d6daebb730cd091b [1,3,11,4,5,19]),(pl 64 5 0x1519e0dc9429247a28abb97a4de3f24a021927 [4,1,3,11,19]),(pl 64 6 0x1692ef8039d91e92c86b49c35c939991f8f5d92ccb [3,4,11,1,5,19]),(pl 64 6 0x1855bee9df0519ff9cf0ab0f1321f309cab4376254 [4,5,3,11,1,19]),(pl 64 6 0x19863449d042d87c19ddd38e3aeaecb3f67a0c575c [3,5,1,11,4,19]),(pd 58 20 0x17357cb8cc80a9489a7996ed5933c3bdb1d0fe005c026593adae2ca10ee449f)] (.nil)) (.nil))) (.cons 0xffaaffaaffaafaaafaaafaaafaaafaaa (.branch [58,23,17,6,0] [(pl 64 6 0x436b6bda4d3fae5089830f78003f002bae4367c02 [19,3,4,11,35,1]),(pl 64 8 0xa1b040ac43040cc08b6081230609924916d7012611491249 [3,19,35,11,4,5,1,27]),(pl 64 8 0x90c40452d04094c4a546e66d02576daa6201025414a350 [19,11,35,3,1,4,0,27]),(pl 51 7 0x22ac859c5676f2665def034f2e625417f05 [3,35,11,19,4,1,27])] (.cons 0xfffffffffffffff0ff00ff00ff00ff00 (.branch [37,1,3] [(pl 64 5 0xd5612748f777cbe4e9d1e8bf4ec7af5be376 [4,3,19,11,1]),(pl 64 5 0x631e96c5c68c90c758cf0a4788612d56e923a [4,3,1,19,11]),(pl 64 5 0xd4f93bb87f03555c16d8f68a56ce46eee594e [3,11,4,19,1]),(pl 64 5 0x613c19aedceffa69fa2c31db38b860cfefdfe [3,11,1,4,19]),(pl 64 5 0xecc6c46e60acac46a75af950804f6f3ad94ad [4,11,3,19,1]),(pl 64 5 0x409c97a8267cfd0b1a7a9e7b52fd250de18 [19,4,3,11,1]),(pl 37 5 0x93e9677db7e697954e1c [3,1,19,4,11])] (.nil)) (.nil))) (.cons 0xffffffffffffffffff00ff00ff00ff00 (.branch [44,33,6] [(pd 64 20 0x3c7ccb37344d8a535a30df7be44ae28e1969933e32320847725bde55644c925a2f21e),(pd 64 20 0x660cf387be52fd19c9396f9d7a65add5d22a5603edf81c5836c479ef3179f418bd2e7),(pl 64 8 0x249209410008002000002001c2c0c903d108703641528252 [2,3,11,1,5,4,14,19]),(pd 30 20 0x30c43bc4188c18f00d07a128b331601f)] (.nil)) (.nil))))) (.cons 0xffffffffffffaaaaaaaaaaaaaaaaaaaa (.branch [57,48,6,10] [(pl 64 7 0x22054718054274f385c2b733448d08e2df44111399ecf [3,4,11,27,1,19,28]),(pl 60 8 0x4c2649d29c0980b80000892424c5289261488a01280 [3,4,11,12,13,19,28,1])] (.nil)) (.cons 0xffffffffffffffffffffffffffff0000 (.branch [43,4] [(pd 58 12 0x19b34a69a1f420c3165fea2e7727d32275e3e74716a3e74a52e6)] (.nil)) (.cons 0xffffffffffffff00ffffffffffffff00 (.branch [51,50,6,3] [(pl 64 7 0x58124fd422bbf665687fbd15d4bcca0589716caf84923 [2,3,27,11,12,19,5]),(pd 25 28 0x1193320a782617bd4f802e28b4f0143)] (.nil)) (.cons 0xffffffffffffffffffff0000ffff0000 (.branch [43,16,6,1,11] [(pl 64 8 0x89804ca9a050edbd40262a0d0c19f604c450000000000000 [3,11,35,27,4,19,1,36]),(pd 31 37 0x13dc6d794ac66cb362cfecfc445bc82f37737254)] (.cons 0xffffffffffffffffffffffff00000000 (.branch [48,20,19] [(pd 64 20 0xea638b4dd334e840cb12a8f59bf37ad36f5e9082158eaa6f635ab2c5998ed068aad40),(pl 64 7 0x22a36a992eb257723263cb0b064a2e21d4a9d53ddf7dd [3,11,1,4,12,19,21]),(pl 64 6 0x1e5910547d0cfae0ece80668d950b2d45207b5312f [3,11,4,19,1,5])] (.nil)) (.nil))) (.cons 0xffffffffffffffffff00ff00ff00ff00 (.branch [43,6,23,2] [(pl 64 9 0x5418d5d418c3b47a51d2f35ae68d4772605992edd54eeff0a8c [2,3,4,19,27,1,11,6,0]),(pl 60 9 0x3bc96dd56d103d79f71c3abd23ffcbee6466e7827c435210 [2,3,19,27,4,6,11,1,20])] (.cons 0xfffffffffffff0f0f000f000f000f000 (.branch [57,33,6] [(pd 64 20 0x58a1d526ecf25d0c0ab5d819ef4c86cbffed07ec8bee49e55f2127db84a178a79a237),(pd 64 20 0x78acfa9ab0032ac8b488d21d4fb64abf78e0b0bf435bb5b0d19472ab62bec5b8212ab),(pd 12 20 0xd735874f92fb)] (.nil)) (.nil))) (.nil))))))))) (.cons 0xffffff00ffffff00ffffff00ffffff00 (.branch [39,8,22,17] [(pl 64 7 0x15664ca933e1951854ff5566cc9c746474eef585f4d3b [2,3,19,20,0,11,27]),(pl 55 8 0x1d9b300008c3040a28c904922404088084c36c1206 [2,3,11,19,0,20,27,1])] (.cons 0xffffff00ffffff00ffffff0000000000 (.branch [25,57,18] [(pd 64 22 0x435b702c236eadd000100ea06dac3f394cfa078042ae66ba8ae3c635ed45f799517aac2),(pd 36 21 0x3d43773df6c3035ce5f5f8ad0e2d8baaa779ef2)] (.cons 0xffffaa00ffffaa00ffffaa00aaaaaa00 (.branch [56,16,18] [(pl 64 6 0xfda27de1e0e21440f57636f80bd3fe698f50819dd [2,3,1,11,4,5]),(pd 64 22 0x622318088331ffb7c4ee71ff7f9e361afdc573e8882adbf2e131c6730f06f8643576af0),(pd 64 22 0x4080ff1b3097d16eda473149e56149d43537a8e75f32d0dbbae8682533efca59897ec10),[2,3,12,6,11,19,1]] (.nil)) (.cons 0xffffaaaaffffaaaaffffaaaaaaaaaaaa (.branch [32,36] [(pl 64 6 0x437bcc240714d2c031f173e3d6e8aa56882205706 [2,1,3,4,11,14]),(pl 64 7 0x897c2eb692da04ba0a02112f0ec94379dacadf88a56eb [2,3,1,5,11,4,14]),(pd 64 14 0x3d20a33e403101bbeb52b49a0b07e6dd3f08d97c7dc932fbd21f0e3e3b124),(pd 57 13 0xd37a9c4adba7146a3f377425646a4c5bd1022fa4550f43e35cec)] (.nil)) (.nil)))) (.cons 0xffffffffffffff00ffffffff00000000 (.branch [46,43,2,18] [(pl 64 8 0x127a6a40326061024e48024940905077148064a0c1 [3,19,11,12,0,5,1,29]),(pd 44 30 0x58bf14a0bdf9bf7ff12287eaa728c664a6b504ac05b30ca46e1d61)] (.cons 0xffffaa00ffffaa00ffffaa00aaaaaa00 (.branch [55,12,2] [(pl 64 6 0x30a0fb4b887a69ea0e2c6adf76ce6c5685af2ea [3,19,1,11,12,4]),(pl 64 7 0x588ffbccb79a86b226573397d298d1d16d9da37433e64 [11,3,1,19,4,12,5]),(pd 64 20 0x188559301557354418f228efa578514814cdc8b8b4fc4eb59e21603ec4c1e6cc4ecfd),(pd 18 20 0x3782c897957457774143)] (.nil)) (.cons 0xffffccccffffccccffffcccccccccccc (.branch [55,43,2] [(pl 64 5 0x10f9cd37980f187f90de7943ea3ec57f54708b [19,4,1,3,11]),(pl 64 5 0x96ebb9818fde194a9125c35774ac996d88bc [19,3,4,1,11]),(pl 64 5 0x645379dd8f2725f5d9f1938b7e4bae31a1bb2 [3,4,19,1,11]),(pl 64 6 0x13ee4136100d3c189e4ab844966152237a94144e99 [19,4,3,11,1,12]),(pl 52 7 0x1c994c11857fdf3ebefc1e410775d71670d85 [3,19,4,11,12,1,6])] (.nil)) (.cons 0xffffaaaaffffaaaaffffaaaaaaaaaaaa (.branch [55,35,12,2] [(pl 64 8 0x68036ab50a364470d13f45051b22385524a5516c2258280 [1,27,19,11,4,3,20,5]),(pl 64 8 0x9300263390cfaa42a94190c275498353a0b201c4e093c42 [27,3,11,1,20,4,19,5]),(pl 64 8 0x44b6012c9241280002000080002176841ada9eb56111c841 [3,19,1,11,27,4,5,20]),(pl 64 7 0x43eb3a7ab8aa52b411368fc14e1d4828f1cbaf2022b25 [27,11,3,19,4,1,5]),(pd 50 28 0x14a15aab2771178b9c9a8ad505464c20e566ae40f8b9fa2e13a31e6e4f1c7)] (.nil)) (.nil))))) (.cons 0xffffffffffffff00ffffffffffffff00 (.branch [51,29,9] [(pl 64 7 0x78c9a2e32a01fb13f8ca364875ae3163406aa9dad6949 [3,11,4,19,12,5,20]),(pd 33 20 0x1679513a5b5e4e6136ee5a70367981879aff)] (.nil)) (.cons 0xffffffffffffffffffffffff00000000 (.branch [45,41,8] [(pd 64 20 0x3d694d3fc6c64b726c6f774b39e31cf2331ab6c13133965f4da0b153f579bfb41981e),(pd 25 12 0x7f80da54f244fdeefacd0b)] (.cons 0xffffaa00ffffaa00ffffaa00aaaaaa00 (.branch [54,41,8] [(pl 64 7 0x42d1b48609066b7b161d158fd96128873309f2bb1a8d1 [2,4,3,1,14,5,19]),(pd 64 20 0xd717cb92d02e7ad26518f9754f94ecb6ad5e4b49cd7e6bea20ba7ffe91b7df433598e),(pd 52 20 0x215cbe09259f1f380483332a1de3ec8e122fee64a9dd3a32888bbbaa)] (.nil)) (.cons 0xffffaaaaffffaaaaffffaaaaaaaaaaaa (.branch [54,34,8] [(pl 64 8 0x21a1808012020084404960e068903a2086889054481d1045 [2,4,1,3,5,12,13,19]),(pd 64 20 0x28ef18ee3a1ce200397c91a7f759f7a3c0adcec64398c9f36c8f1cd14e5e300db3b29),(pl 64 7 0x17ca260f8f934a73ce86b8181a85bee707f8c4b1ead91 [2,3,4,1,12,5,19]),(pd 64 20 0x18823c7e99f3711b88a55bf8da7b70045b992a829c9760eba8cd6fcd4341f9cde0cec)] (.nil)) (.nil)))) (.cons 0xffffffffff00ff00ffffffffff00ff00 (.branch [40,24,54,1] [(pl 64 7 0x412ced8510c99bcf8593fa38ed16c1e6adfa1182ec3 [3,11,4,1,12,19,27]),(pl 64 7 0x215be00489635cd63b45f9b00208a61e0b9915fc157fe [3,11,19,27,4,1,0]),(pl 64 9 0x3a4be3c084e6a2faeeae7f59e8c9a1a2b4f43ec70581297a728 [3,11,19,4,27,0,1,12,23]),(pd 23 28 0x5b4c18d7a15168772f16a5ebfeb)] (.cons 0xffffffffffffffffffffff00ff00ff00 (.branch [40,30,2] [(pl 64 6 0x8c65c0ac0da63957a9ddc94891319c5c3b5386c5e [11,3,4,1,12,19]),(pl 64 5 0x805982ad22ead895f9ab033b3f8f27d9b09df [3,11,19,1,4]),(pl 64 6 0x15ab92ed73dd6e17d233484238b3cb5c2ccbbdc212 [3,4,11,19,1,12]),(pl 64 6 0x40b12c46809e9b5de7baec0507424bcafd12d41b [4,11,3,19,1,5]),(pl 64 8 0x249e1244d0137c24424410000094b3622001800288285cc9 [11,3,4,19,0,1,5,12]),(pl 33 4 0x15c9491800c000000 [3,19,4,1])] (.cons 0xfcfcfcfcfcf0fcf0fcfcfcccfc00fc00 (.branch [52,45,14] [(pl 64 5 0x616fce0e21648f3e9ed2719af7d9d2fc3bff6 [11,4,1,3,19]),(pl 64 4 0x88aa2a2a22a208105543755154550045 [1,4,3,19]),(pl 64 7 0x1a2f9efa022fa9e52874a134d3409565e0de1053e89 [4,3,1,19,12,11,20]),(pl 64 5 0x655b535a9c063cf1e1a16c91390a12068b18a [11,4,3,1,19]),(pl 64 5 0xb76aa5d2fec40c492d3abb1db1e4c59befb96 [4,3,1,19,11]),(pl 64 5 0xc29d11b806c8d5517b892e8a084d9e84b7056 [19,4,3,1,11]),(pl 64 3 0x15971dbf4301b686a6c67f06a1 [3,11,1]),(pd 64 20 0xfc73a6bb34c146efe7638794d9ecb53816d2416f7553580d547b718831f8b13687c4f),(pl 64 5 0xf45afd96bf37980f962dc72bbd69e4278ab5b [12,3,11,19,1]),(pl 64 7 0x12de27420fb2346162cb2e0835e1d2247b655dafffeb0 [3,11,12,19,1,20,5]),(pl 55 6 0x2f57ac11b339de5bc612345d5b605d9ad99d [3,11,12,19,1,5])] (.cons 0xfefefefcfefafef0fefefeccfeaafe00 (.branch [49,26,39,56,21] [(pl 64 3 0x94e59bf95fe4bad31465367b4 [3,1,11]),(pd 64 38 0xe5a876efa66941035576be9b147ae638fd884ba2fe9cf3b4688af309ecfbb20e878628009ed3c964e099),(pl 64 8 0x1d8d40049242248000009000040040040001041040041020 [3,1,4,6,11,14,21,37]),(pl 64 9 0x5789c3aa2cf743890ccf4d95d980595af8c749d156af36383 [11,3,1,6,14,27,4,21,35]),(pl 64 10 0xc95438cb30219af7a8d65e781b384e979b29cfb4756d81323a0 [11,1,3,4,6,37,21,27,14,35]),(pl 64 10 0xab7a2980743e076ff7bb80d4cfbc93f1dce2de3eb607ccd8272 [11,3,1,27,35,6,37,4,21,14]),(pl 64 8 0x24316e6122d220848821e00177005a9396adc6773a90b408 [1,11,4,3,21,27,35,6]),(pl 64 8 0xaa0fa22020800800000090000400400400010410400440db [3,1,27,4,11,6,14,21]),(pd 64 38 0x12f0c65b75f8e52d0e4ad2179efe61f2dbf62b997a06ac0e590d78f4c64e495120eed7ff1a43496ddff3),(pl 64 7 0x79cabcffdc2c5881cf835b35ecc4d3ec7dfa938dfc3fa [35,1,11,3,27,28,36]),(pl 64 5 0x157d17e3c51318d37c0188d19f9966ac1abdf3 [27,3,11,1,4]),(pl 64 7 0x429aa787c5d6a14774378b3113dd5bf9bd1888defe6cf [3,4,11,21,1,27,35]),(pl 64 4 0xa92a8040000000040004000500549ff [3,1,11,4]),(pd 64 38 0x12eefa8515753a071fe4f215f2c0724796abd1acc1e7696c01d498df51be49c7ded2460db0f6c8c70f67),(pl 64 6 0x75fe7ac2cafb986331f4a4798850fc518b9e4f5b9 [4,1,27,3,35,11]),(pl 64 5 0xc4076a99ef1054c594fccedf9e09c0bdb03e2 [4,3,27,35,11]),(pl 64 5 0xc27818c769b17262f34059f1938296d9808fc [4,35,3,27,11]),(pl 64 6 0x1155eca523fb9f1039457b1b6578182cf49df44d33 [4,3,11,27,1,35]),(pl 64 6 0x3ed2f05b32bfabd664685aa3da1ad1dfb3aa9b3e0 [11,3,4,27,1,35]),(pl 64 6 0x212f33b1368f53c178cb863a0f6ccda02a277bdf99 [3,4,11,27,1,35]),(pl 51 6 0xb0288661a6cfcc61bd9a4cc2311969636 [3,11,4,27,35,1])] (.nil)) (.nil))) (.cons 0xfafafaf0fafafaf0fafafa00faaafa00 (.branch [51,40,13] [(pl 64 5 0x646fa8e4fef9dbc31fdb55d6d70a86e13797e [11,4,1,3,19]),(pl 64 5 0xbffad59b182d70da95f593668b9aedaaeef79 [4,1,11,3,19]),(pl 64 5 0x3290bc620c2e293bcea34dbf92f3dc284bc1 [4,3,1,11,19]),(pl 64 7 0x64cafed35f4fcb9739f621148b61b0ed27d92176211f7 [3,1,4,12,19,11,20]),(pl 64 5 0xb96855d133357230b8b293b8d589c1fd3f4e1 [4,3,19,1,11]),(pl 64 5 0x11047e03c71d1d05c0370afa3bb48221db1241 [19,4,3,1,11]),(pl 64 3 0x159724d4402d9aeeda404cf8db [3,11,1]),(pl 64 8 0x900900000000000c0018003049252b78249c4951125151c [3,4,12,1,11,19,0,13]),(pl 64 5 0x66b97d228b207fe4804adbf33d [3,11,12,19,1]),(pl 64 6 0x1c6114968c3ed937897e82b4224312e5f9800c29c [11,12,3,19,1,20]),(pl 64 7 0x3068618d3dee915fb64995ad0d91096926ea3cc [3,11,12,19,1,5,20]),(pl 46 6 0x7142d101e02f25d89bc3be4d8020be [11,12,3,19,1,5])] (.cons 0xfefefefcfefafef0fefefeccfeaafe00 (.branch [42,33,39,21,56] [(pl 64 3 0x1b33568dcea06d1820300b986d [11,3,1]),(pl 64 9 0x5eb050e5f087271936a794e88b89585f780c56a05a68c97cb24 [3,1,6,13,28,4,27,29,35]),(pl 64 4 0x223a90058004040440541209a6142114 [11,3,1,4]),(pl 64 8 0x804000100100100004104100800955c652df18d369c469 [3,1,11,13,6,4,27,35]),(pl 64 9 0x1a49c4a5c7bcc413bbd24cb4a4974c9b2e80c8e322f47493816 [1,3,4,11,13,27,35,21,6]),(pl 64 6 0xe7535b62e83d99ecd5ca28e9587131ad71f30241b [3,1,27,4,11,35]),(pl 64 9 0x371e87e00bfb0ebdc3ce6b4c86e252c2312ad4d9ba64c628ee6 [3,13,11,27,1,4,21,35,6]),(pl 64 8 0xac8d0b00003920004a00004004004100124021008a450240 [11,3,1,35,6,13,21,27]),(pl 64 10 0x158f4c91c288c605c1ac826e5ba1db0b7467e421695485312528 [11,1,3,4,27,28,35,6,13,36]),(pl 64 6 0x15b61dcebfc5fb963c5ca2f372370160a9b511ca5b [27,3,11,1,28,36]),(pl 64 6 0x276855b87a7ff3f88edd40c40cdc8a364497158f7a [35,1,11,3,27,4]),(pl 64 8 0x12be96892012426892d10980c00db0119a046fa34521990 [3,4,11,1,13,27,21,35]),(pl 64 4 0x596900140010100414041250009158ff [11,3,1,4]),(pl 64 12 0xcf431cb15ed6eb63d47805aff283673a74f819001338c5101 [3,1,13,6,29,27,4,20,22,28,35,39]),(pl 64 6 0xb86276dfc53df004d7dfceda84b02e8b162b [4,3,27,35,1,11]),(pl 64 5 0x62bd17adc4832a8d9e962b5b249bff378f074 [4,35,27,3,11]),(pl 64 5 0x1c013b72ab91a92304ccb97dd6002ff65906f [4,3,35,27,11]),(pl 64 6 0x21faa45d99be56da8ab5d09c31f1b2722ea0b34810 [4,3,11,27,1,35]),(pl 64 6 0x1d2960ac77c901ce30d21a37958de1851b27aca093 [3,11,4,27,1,35]),(pl 64 6 0x73a07bc8047401bcaefbd42b412fa3c74fdbe8a36 [4,11,3,27,35,1]),(pl 33 5 0xd5fb46fdcb4fe2bffe1 [3,11,27,35,1])] (.nil)) (.nil))) (.nil)))) (.cons 0xeeeeeecceeaaee00eeeeeecceeaaee00 (.branch [47,38,54,1] [(pl 64 6 0x8a2676d70c4b60890e5ffe40eda6582ac3835dbb2 [1,4,11,3,19,27]),(pl 64 7 0xa4be18f1bd984adaeb738defb80a136991b943c9e951 [1,3,4,19,12,11,27]),(pl 64 6 0x2b2383723b22a2e27290318278eb21f7f124e699f3 [3,19,27,1,11,4]),(pl 64 6 0x3da6b28983f2abf50a8f38b3bf9f1bf0c82a495a [3,11,4,1,19,27]),(pl 64 7 0x70fd796f53074a65dbd9dd2aff12cc8d2b [3,11,12,4,19,27,1]),(pl 64 7 0x49158ce108406fec161dbef1ba7fc88567660fa6fc374 [11,3,12,19,27,1,0]),(pl 64 6 0x199b0643713ff19668b91d62563e7ddaa05da0c30a [3,11,12,19,1,27]),(pd 32 28 0x373adeb26e0c374fa10dc5a3067ae4bf1a54f0)] (.cons 0xffffffffffffffffffffff00ff00ff00 (.branch [40,28,45] [(pl 64 3 0x2afa5f35e167b96c6aae5ba6c1 [1,11,3]),(pl 64 4 0x8a8a88c0a8880550554545500554ff0f [1,4,11,3]),(pl 64 4 0xa8a8820a8881541551515401553fc8ff [1,4,3,11]),(pl 64 5 0x1500bc57d0f2b2c90acbad2910cf21ac71626a [4,3,1,11,12]),(pl 64 4 0x5a99006400404046540463fa07f8f8f8 [11,1,3,12]),(pl 64 6 0x19ff871807df62f618bf121d92974e25461fc0b63a [3,1,11,4,5,12]),(pl 64 4 0x96a40190010101195018fe81fe3e3e38 [11,1,3,12]),(pl 64 6 0x27d07a9d8585235fe1ca607485fca22e3d96a01e5f [3,1,11,4,5,12]),(pd 64 14 0xa418768d7487e802c49d480ec50797a77153a2c14aac3dedfa8d340fb7329),(pl 64 9 0xe6b87ee9e3f7e924726bfd149480c1cc6783e832fa96434f [11,3,12,1,4,5,0,20,21]),(pd 50 14 0x231fba8b2b038aabdc00f7b3c784da7a9fe5d51d27181535)] (.cons 0xfefefefcfefafef0fefefeccfeaafe00 (.branch [40,31,21,13] [(pl 64 6 0x8762084ecff2161875737de18a19e5d090b3ca308 [1,3,11,4,19,27]),(pd 64 29 0x13acc1a94de956c5cf33fe6576fd89ed17649c124c9b0c2290fffa5539a7429720e7f9b560a38a),(pl 64 8 0xc421043f044000a48304cb014814810c00520c1001a13043 [1,11,4,3,19,27,28,21]),(pl 64 8 0x248001200001001001048240041049040201d2b6545d16d5 [3,1,19,28,11,21,4,27]),(pl 64 7 0x149822c3a13543f5a20315a2cd04eaca939a9058023b [3,11,1,28,21,19,27]),(pl 64 3 0x66bde6f10df6c8d3e9dd2bd65 [3,1,11]),(pd 64 29 0xe142c5735ee495a5896ec54490fe28b98b4c9851fed63025db5df60b1b4fc8293f388729eef18),(pl 64 7 0xb8d569f840678ad87674d50402060be574dc83b43e938 [11,3,1,4,28,21,27]),(pl 64 8 0x165da0fa00031f380064248b2059484884882c92122c8248 [11,1,4,3,27,19,28,21]),(pl 64 9 0xdc036a6961be3442fd5a5a60a5b9ac6575ef56f79a8d4d528b [4,3,12,11,19,1,27,28,21]),(pl 64 6 0x16e2ff42993a5f7594ebd494ec3693567716e9129a [19,1,3,11,12,4]),(pl 64 8 0xddd41100889410200108004206024b2130c840844904808b [27,1,11,3,19,4,21,28]),(pl 64 8 0x4800884800004900020100810824d1922c3eca4f2068000 [11,3,28,19,1,4,21,27]),(pl 64 6 0x115781dbda2c388f919a496f95390503ce6b6d7688 [11,1,4,3,19,27]),(pd 64 29 0x52cb1ce169254b3aa7e0cab95a168a378df6b9166ba04d929e458772420db7d6aadf242e880492),(pl 64 8 0x26800000026800008004d00000492492492004d00001f5 [4,3,19,27,1,6,14,21]),(pl 64 5 0x113adf8beeda063fee59c4cee2e60ad5d5afb1 [3,4,11,19,27]),(pl 64 6 0x282d5b6c68a09cdde145cb2f55f49ba6db19977c2 [3,11,4,19,1,27]),(pl 64 6 0xe728ed0d638304f429c1554ee182e47647085c294 [4,3,19,11,1,27]),(pl 64 6 0x8aaf764d3c62c133f2b5a7819ba6f0a1d06c8ff4d [11,3,4,19,1,27]),(pl 22 5 0x113246c0a7262 [19,3,4,27,1])] (.nil)) (.nil))) (.nil))) (.nil)))) (.nil))))))) (.nil)))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem zhF : chkCheckNode zhw zhx zhy s14_raw zhz zhD [] zhB zhE = true := by decide +kernel
def zhG : zeV := ⟨2,[(0,1)],[]⟩
def zhH : zeV := ⟨6,[(0,1),(0,2),(1,4),(2,5),(3,4),(3,5)],[(4,5)]⟩
def zhI : Nat := 0xffffffffffff
def zhJ : Nat := 0x11001040028
def zhK : Nat := 0xfff8ffeca8a8
def s18_raw : List Nat := ze6 6 zhI
def zhL : List Nat := ze8 6 zhH.edges zhI
def zhM : List (List Nat) := []
def zhN : List (List Nat) := []
def zhO : List zeW := [⟨0,[(0,2)],[0,1,2,4],17,[3,5]⟩,⟨0,[(3,4)],[3,4,1,0],17,[2,5]⟩,⟨8,[],[4,1,0],17,[2,5]⟩,⟨40,[],[2,0],17,[1,4]⟩,⟨23,[],[],17,[3,5]⟩]
def zhP : List zeF := zfb zhI s18_raw [(1,[.e [(0,2)]]),(1,[.e [(3,4)]]),(2,[.v 3 [20,17,34]]),(3,[.v 5 [9,4],.v 3 [20]]),(5,[.v 1 [9,20,33],.v 0 [20,12],.v 4 [12],.v 2 [32]])]
def zhQ : CertNode := .branch [4,3,0,1] [(pl 54 8 0x410583d209c000924000002490436d8409248209 [3,11,19,27,4,12,0,5])] (.cons 0xffffffff0000 (.branch [4,3,0,2] [(pd 36 28 0x15efaa30a3971652428df45d1d87a9880debda11a5f)] (.nil)) (.nil))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem zhR : chkCheckNode zhI zhJ zhK s18_raw zhL zhP [] zhN zhQ = true := by decide +kernel
def zhS : zeV := ⟨7,[(0,1),(0,4),(1,5),(2,4),(2,6),(3,5),(3,6),(5,6)],[(4,6)]⟩
def zhT : Nat := 0xffff0000ffffffffffffffffffff
def zhU : Nat := 0x1000001100000010400120008
def zhV : Nat := 0xffff0000fff8fffeffccfafa8888
def s22_raw : List Nat := ze6 7 zhT
def zhW : List Nat := ze8 7 zhS.edges zhT
def zhX : List (List Nat) := []
def zhY : List (List Nat) := []
def zhZ : List zeW := [⟨32,[],[1,0,3,4],17,[2,6]⟩,⟨2,[],[0,4,2],2,[3,5,6]⟩,⟨4,[],[4,0,1],2,[3,5,6]⟩,⟨8,[],[],18,[1,0,5,2,4,6]⟩,⟨0,[(5,6)],[],26,[0,1,2,3,4,5,6]⟩,⟨76,[],[4,0],17,[1,5]⟩,⟨84,[],[0,1],17,[3,5]⟩,⟨104,[],[1,0],17,[2,4]⟩,⟨85,[],[1],17,[3,5]⟩,⟨108,[],[1],17,[0,4]⟩,⟨23,[],[],2,[3,5,6]⟩,⟨59,[],[],17,[2,6]⟩,⟨59,[],[],17,[2,6]⟩]
def zh0 : List zeF := zfb zhT s22_raw [(3,[.v 5 [64,26,66]]),(2,[.v 1 [65,48,1]]),(2,[.v 2 [48,66,24,65]]),(2,[.v 3 [37,66,48]]),(1,[.e [(5,6)]]),(5,[.v 2 [16,64],.v 3 [66],.v 6 [32]]),(5,[.v 2 [26,66,48,65],.v 6 [],.v 4 [33]]),(5,[.v 3 [37,66,48,65],.v 5 [64],.v 6 []]),(6,[.v 0 [2,48],.v 4 [],.v 2 [],.v 6 [32]]),(6,[.v 3 [],.v 2 [48,66,65],.v 6 [],.v 5 [2]]),(5,[.v 0 [14,48,24,66],.v 1 [32],.v 4 [36],.v 2 [64]]),(7,[.v 0 [2,24,18],.v 3 [66,48],.v 1 [48],.v 4 [],.v 5 [64]]),(7,[.v 1 [1,36],.v 3 [37,48,64],.v 0 [16],.v 4 [4],.v 5 [64]])]
def zh1 : CertNode := .branch [10,3,2,4,1] [(pl 64 5 0x14629b434e355369f0eb1e237b1461f0f7 [3,11,19,27,35]),(pl 25 6 0x3b695bbf99a7e00 [3,11,19,35,0,5])] (.cons 0xffff0000ffffffffffff00000000 (.branch [12,5,4,10] [(pd 47 30 0x642313fd0a43bc669d46f3769efc0f8677929e2c55c401cd6779beee9)] (.nil)) (.cons 0xffff0000ffffffff0000ffff0000 (.branch [10,3,2,1,4] [(pl 63 7 0x1b5d83e19c856e1cc062a9edd4cadec7f7659ad541919 [3,11,19,27,0,35,1])] (.cons 0xffff0000ffffffffffffffff0000 (.branch [11,6,0] [(pl 64 6 0x8bc02530bc4cd2c8bd9d3c84675209cd53 [3,11,19,4,5,12]),(pd 9 6 0x2a6e19)] (.nil)) (.cons 0xffff0000ffffffffffff00000000 (.branch [7,6,1,10] [(pl 64 7 0x18dd241dfb870f6dad2266835e93c3519201af65b465 [3,11,19,1,27,0,12]),(pl 49 6 0x5ef13a4c4f4b2ed1216f77ced95a5943 [11,3,19,4,27,1])] (.cons 0xfff00000fff0fff0ff00f0f00000 (.branch [9,8,0,4] [(pl 64 6 0x167d929614552099c2ec65cea0eb8d71ee2faebd2 [1,4,11,3,19,27]),(pl 64 6 0x159c3d30abb4541d0d16456bda69cc3f89f2b2142 [3,1,4,11,19,27]),(pl 64 6 0x335d6dd9f36e57125772c9bea47022349e953658 [3,1,19,4,11,27]),(pl 64 7 0x21fc0960c7351597f6eb5dad2924e5bb21739fc589a3c [4,3,11,1,19,27,6]),(pd 21 28 0x1dfe59bcac330f812a58d0f21)] (.nil)) (.nil))) (.nil)))) (.nil)))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem zh2 : chkCheckNode zhT zhU zhV s22_raw zhW zh0 [] zhY zh1 = true := by decide +kernel
def zh3 : zeV := ⟨7,[(0,3),(0,5),(1,4),(1,5),(2,5),(2,6),(3,6),(4,6)],[(3,4)]⟩
def zh4 : Nat := 0xffffff00ffffff00ffffff00ffffff
def zh5 : Nat := 0x101100000001600040200
def zh6 : Nat := 0xfffffe00fffff000fefefe00ccaa00
def s23_raw : List Nat := ze6 7 zh4
def zh7 : List Nat := ze8 7 zh3.edges zh4
def zh8 : List (List Nat) := zfW 7 [[1,0,2,4,3,5,6]]
def zh9 : List (List Nat) := zfX zh8
def zia : List zeW := [⟨64,[],[2,3,0,4],17,[1,5]⟩,⟨0,[(0,5)],[0,3],4,[1,4,5,6,2]⟩,⟨0,[(4,6)],[4,1],4,[0,3,5,6,2]⟩,⟨2,[],[4],4,[0,3,5,6,2]⟩,⟨4,[],[],18,[5,0,1,6,3,4]⟩,⟨33,[],[1,2,3],17,[4,6]⟩,⟨34,[],[0,2,3],17,[4,6]⟩,⟨36,[],[0,1,3],17,[4,6]⟩,⟨9,[],[],4,[1,4,5,6,2]⟩,⟨9,[],[],4,[1,4,5,6,2]⟩,⟨38,[],[0,3],17,[4,6]⟩,⟨26,[],[0,5],17,[2,6]⟩,⟨26,[],[0,5],17,[2,6]⟩,⟨84,[],[1,3],17,[0,5]⟩,⟨100,[],[0],17,[1,4]⟩,⟨43,[],[2],17,[4,6]⟩,⟨77,[],[4],17,[1,5]⟩,⟨77,[],[4],17,[1,5]⟩,⟨77,[],[4],17,[1,5]⟩,⟨77,[],[4],17,[1,5]⟩,⟨86,[],[3],17,[0,5]⟩,⟨45,[],[1],17,[4,6]⟩,⟨77,[],[4],17,[1,5]⟩,⟨114,[],[],17,[0,3]⟩,⟨58,[],[],17,[2,6]⟩,⟨105,[],[],17,[1,4]⟩,⟨114,[],[],17,[0,3]⟩,⟨101,[],[],17,[1,4]⟩,⟨109,[],[],17,[1,4]⟩,⟨109,[],[],17,[1,4]⟩,⟨118,[],[],17,[0,3]⟩,⟨91,[],[],17,[2,5]⟩,⟨109,[],[],17,[1,4]⟩,⟨109,[],[],17,[1,4]⟩,⟨118,[],[],17,[0,3]⟩,⟨109,[],[],17,[1,4]⟩,⟨59,[],[],17,[2,6]⟩,⟨109,[],[],17,[1,4]⟩,⟨91,[],[],17,[2,5]⟩]
def zib : List zeF := zfb zh4 s23_raw [(3,[.v 6 [7,40,17,48,12,4]]),(1,[.e [(0,5)]]),(1,[.e [(4,6)]]),(2,[.v 1 [21,96]]),(2,[.v 2 [65,40,96]]),(4,[.v 0 [96,12],.v 5 [66,10]]),(4,[.v 5 [66,21,10,65],.v 1 [16]]),(4,[.v 5 [20,67,10],.v 2 [67]]),(3,[.v 0 [14,96],.v 3 []]),(3,[.v 3 [7,96],.v 0 [96]]),(5,[.v 1 [21,40,96],.v 2 [40,65,96],.v 5 [1]]),(5,[.v 1 [17,40],.v 3 [],.v 4 [96]]),(5,[.v 1 [21,96,40],.v 4 [],.v 3 [1]]),(5,[.v 2 [65,40],.v 4 [2],.v 6 [40]]),(6,[.v 2 [67,40,48,96],.v 6 [],.v 5 [10,17]]),(6,[.v 0 [],.v 1 [48,16,32],.v 3 [],.v 5 []]),(6,[.v 0 [96,8,40],.v 2 [66,40],.v 3 [],.v 6 [48]]),(6,[.v 0 [8,32,40],.v 3 [],.v 2 [32],.v 6 [48]]),(6,[.v 0 [96,12],.v 3 [],.v 6 [4],.v 2 [32]]),(6,[.v 2 [],.v 0 [8,96,40],.v 3 [],.v 6 [48]]),(6,[.v 2 [65,40],.v 6 [17],.v 4 [],.v 1 [32]]),(6,[.v 3 [1,66,65],.v 2 [32],.v 0 [32],.v 5 [66]]),(6,[.v 3 [],.v 2 [67,48],.v 6 [],.v 0 [32]]),(7,[.v 1 [16,32,40,48],.v 4 [],.v 5 [65],.v 6 [5,8]]),(7,[.v 1 [21,96,40,48],.v 5 [17,12],.v 4 [],.v 3 [65,1,64]]),(7,[.v 5 [21,10],.v 0 [8],.v 3 [],.v 6 [6,20]]),(7,[.v 5 [66,65],.v 1 [16],.v 4 [],.v 6 [5,12]]),(7,[.v 6 [7,21,17,4,12],.v 0 [14,32,8,48,40],.v 2 [48,40],.v 5 [10]]),(7,[.v 0 [32,14],.v 2 [32,40],.v 3 [],.v 5 [66],.v 6 [16]]),(7,[.v 0 [],.v 3 [],.v 6 [6,16],.v 2 [48],.v 5 [2]]),(7,[.v 1 [40,16],.v 2 [40,65],.v 4 [],.v 5 [65],.v 6 [8]]),(7,[.v 1 [16,32,40,48],.v 4 [],.v 3 [1],.v 6 [],.v 0 [32]]),(7,[.v 2 [],.v 0 [10,96,48,40],.v 3 [],.v 6 [48],.v 5 []]),(7,[.v 2 [64,32,96],.v 0 [8],.v 5 [10],.v 3 [],.v 6 [16]]),(7,[.v 2 [],.v 1 [96,16,40,48],.v 4 [],.v 6 [],.v 5 [1]]),(7,[.v 2 [],.v 3 [],.v 6 [],.v 0 [32,48],.v 5 [2]]),(7,[.v 3 [],.v 4 [7,65,2],.v 0 [32],.v 1 [32],.v 5 [4]]),(7,[.v 3 [],.v 6 [21,6],.v 2 [],.v 0 [48],.v 5 [2]]),(7,[.v 4 [],.v 3 [1,65],.v 0 [],.v 6 [],.v 1 [32]])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
def zic : CertNode := .branch [9,4,3,1,2] [(pl 64 6 0x829d53ed05d88a5ee1e7e3646ef18e38b8d685501 [2,3,11,19,27,35]),(pd 25 20 0x102d04126d79eef9e729fd017a9b)] (.cons 0xffffff00ffffff00ffffff00000000 (.branch [21,6,13] [(pl 64 6 0x4495f48abcd3d11fc50d34a90f7951df205ae5001 [2,3,19,11,12,20]),(pd 13 20 0x1244afbdf14cbf)] (.nil)) (.cons 0xffff0000ffff0000ffff0000ffff00 (.branch [8,4] [(pl 64 5 0x5694acdb77a0035eb05285aefff514d9bfea2 [2,3,11,0,4]),[2,4,11,2,3,1]] (.cons 0xffffff00ffff0000ffffff00000000 (.branch [16,11,4] [(pl 64 6 0x9607da3ea470062e22c851b1e69fd0c0e1e3b0076 [2,3,19,1,11,12]),(pl 64 7 0x114323c6930b198b56b5f5d173902578bfe3bbf344d10 [2,3,19,11,6,12,13]),(pd 20 20 0xda81bbac6db81feb16b68)] (.nil)) (.cons 0xfffff000fffff000f0f0f000f0f0f0 (.branch [18,4,0] [(pl 64 8 0x800800000603c204480a8442828746240488443839202642 [2,3,11,1,4,19,0,6]),(pd 56 20 0xa34a38572debbbf6f38de7d86d386583988f7d5ae802c1978cbd26fded07)] (.cons 0xffffff00fffff000ffffff00000000 (.branch [19,12] [(pd 64 14 0x2052ca217c02c72b87b87fba53526e5ef9b4d6f46d0b6317fb0930c5ca112),(pd 64 14 0x2017099640bab20a974f16cb30228b3d32b90802053e38676f7190f6bd852),(pl 64 6 0x26b3bc459cf90ecee05420f7cf294102dc38e179e [2,3,11,1,4,5]),(pd 49 12 0x468c43527d494bdf463f3179db0fbd0ca236312c2f7b)] (.cons 0xfffffa00fffffa00fafafa00aaaaaa (.branch [35,12,26] [(pd 64 20 0x172ac5f305a8baf3757a45afbb6e9dbbe44de3279917a8f766f13a3471ca936277a299),(pl 64 6 0x1347df9df9aa70492faeda5873530e8c967768e4b6 [1,3,4,11,19,6]),(pl 64 5 0xbc066232a142a6c9ad4df1f5d2962b4195fec [3,1,4,11,19]),(pl 64 8 0x28304a209409115ea96d48d1695418a616c0600d9880181a [3,19,1,11,5,4,6,12]),(pl 64 6 0x19c08cbef2f7e28ffd713a635fa86b2c5917fc5a19 [4,19,3,11,1,12]),(pd 64 20 0xe0ac643c7fc0b41d31b8b6e87ce3b9c41749ad6976cf7afd381736255db3251f63e13),(pd 43 20 0xfefc16670b2b10504f08d4701cb8faf784e89d69c700f3)] (.cons 0xfffffe00fffffc00fefefe00cccccc (.term) (.cons 0xffffff00fffff000ffffff00ffff00 (.term) (.nil)))) (.cons 0xffffff00fffff000ffffff00ffff00 (.branch [27,10,11] [(pl 64 8 0xa00000c00140c430d12040c85024430928082384480c8208 [2,4,1,12,3,5,11,20]),(pd 64 22 0x5f495b49b09c656a7f2b1446e5cd7ff615103fc1e8f1e3c4d83605070debe3bf82990e6),[3,1,2,3,1,2,3]] (.cons 0xfffffa00fffff000fafafa00aaaa00 (.term) (.nil))) (.nil)))) (.cons 0xfffffa00aaaaaa00fafafa00aaaaaa (.branch [37,10,6] [(pl 64 7 0x42ca6c63d669dd9e4bfe17a5e6fd425286abeae55f0e [19,3,11,4,12,5,1]),(pl 64 8 0x5131a1488391a29b106444882da21960000000000000003c [3,4,11,12,19,5,6,1]),(pd 43 20 0x383e5537d49ad9aaf91f531ac18cd03f5e5f0fe8ce00a53)] (.cons 0xffffff00fffff000ffffff00000000 (.branch [34,25,8] [(pl 64 6 0x447ed3aba5ee40515125cdcc9a06039ab839c94 [3,12,11,1,19,4]),(pd 64 21 0x1f874243e3b109a9006ea1c224af9b75902d99176d5b7b7fcaa567179f0a7c878300a3b),(pd 64 21 0x6b8d2b6d72d6cfd801995a7a8a7a66c00b21ed44f99b04bb313d19ff3b7b884a2ebee1),(pd 64 21 0x1250a27d00852c782c9bf05330d64ac0120f0c9db4a38950ab2be6be13dc6d096e1fa34),(pl 64 7 0x2623e91e05c6aa8a7f80c58bf3b383d18c8c4da51670f [3,4,11,19,1,20,12]),(pd 64 21 0xa016de9c833b874a76468c966b92e052926bd41abb6001845e7c690b87d670d19a195a),(pd 21 21 0x1141761ea885c3bc4fed999e)] (.nil)) (.nil))) (.cons 0xffffff00ffff0000ffffff00ffff00 (.branch [27,25,8] [(pl 64 6 0x20c5dd3d5ff70557f10e25e96adf2bd833efa73898 [3,2,1,19,11,20]),(pl 64 7 0xed4400f9664de55c24c930d5ce0c8e3543e0012000aa [2,3,19,11,20,5,0]),(pd 14 20 0x3870f28230bd38f)] (.cons 0xffffff00fffff000ffffff00000000 (.branch [19,26] [(pl 64 6 0x90921c73a16dccb884b5222134b225a82cdfeb4c3 [2,11,12,4,3,1]),(pl 64 6 0x7b2ab5cd6bc02ec99c216fbc5ced9e82d63805adb [1,2,3,4,11,5]),(pd 64 15 0xa48ca227779b62e9f765b48245f87f811302c26690da91e9f2174fb7c58be3),(pd 64 15 0x168f2a5be640e6e725f3ee181518d4a75f3b492df7d990a1b40030b0bb52ef5),(pd 64 13 0xcd0fb1e0f76e3264b43a65c5ed97d83c15fa94fe39e5e7b3da34807e315),(pd 64 13 0xacb9f378b02a6081a8abfc72384fccd2d3c0abb310442dc74fcb1d489e8),(pd 64 12 0xf158fe5f705c94eec28b7b124d0a7e9ff23fadbeb015264c58a2dd4e4)] (.cons 0xfffffa00fffff000fafafa00aaaa00 (.term) (.nil))) (.cons 0xffffff00ffffff00ffffff00000000 (.branch [19,26] [(pl 64 6 0x26c4e610506cba826ceaf85f65bd93f2c34af05d22 [2,11,4,12,3,1]),(pl 64 6 0xea78baf5858f87841e37da122ee48ad4cd3ddc6b6 [3,2,1,4,11,5]),(pd 64 15 0x35937a7965aa5e5e3a5ea2f6ac6ce37e05e094bcb9df678d3be2ba9df5d0f40),(pd 64 15 0x92717f78a68bc4baa23b18b53bc76cbc1c64aceba469c327e2eeb9e1ac1aa1),(pd 64 13 0x6eba5c7869968538d706782f21b9d36e1b7001f1a7fa063a93f195e655e),(pl 64 6 0x74be4871d7228633636cb7396169db84a09d7bc82 [2,4,3,12,1,11]),(pd 12 7 0xe5737710)] (.cons 0xfffffa00fffff000fafafa00aaaa00 (.term) (.nil))) (.nil)))) (.cons 0xffffff00ffffff00ffffff00000000 (.branch [19,26] [(pd 64 15 0x9aea112631857b70ead49c7c93de7cebaeeef876b83fba7b897b7d7f3249ae),(pd 64 15 0xddba532c7d0974e286b9414617cad6afa87adad37a2dfbe7cac2542b7c8812),(pd 64 13 0x938d85aec9a7d64c5a718057c88f2073ab9929128875c3d16e897d09db7),(pd 15 15 0x847390bc0b083a)] (.nil)) (.nil)))))) (.cons 0xffffaa00ffffaa00aaaaaa00aaaaaa (.branch [36,20,3,1] [(pl 64 9 0xea8bb0f0a379d32ff5dd3ce25a75e0d941abd34172ad4f7fd2 [19,3,4,11,27,1,0,5,13]),(pd 63 28 0x17ac21e44b099e57dc88235fa5266c18c2fdb87e8a0c14ee9862b484c0f1302f5e4df31c71c7)] (.cons 0xfffffa00f0f0f000fafafa00f0f0f0 (.branch [29,6,3] [(pl 64 6 0x241f1e805a3a2aeaf06507b37380cc6e6070bed5c3 [11,3,5,4,19,1]),(pl 64 7 0x1d541f3c05d09e3a006fb649a1db20f8303a75e581566 [3,5,11,4,19,6,1]),(pd 22 20 0x18407ada1dc717095a1409ef)] (.nil)) (.cons 0xffffee00cccccc00eeeeee00cccccc (.branch [36,7,0] [(pl 64 6 0x26b3c3c9a229e568c1c99ce52ca1d33a2ebed5fc3 [11,4,3,19,1,12]),(pl 64 7 0x5e4f11bf228eb413dc9c6bd9d390186dace5d94ac49f6 [4,19,3,11,5,12,1]),(pl 58 7 0x24986a84cb9ebc657183a0088e0ca3198398f00 [11,19,4,3,1,5,12])] (.nil)) (.cons 0xffffff00ffff0000ffffff00ffff00 (.branch [24,27,4] [(pl 64 6 0x2d83d96ed7505500140872ed8f9e825e7c5c2ab8c [11,3,19,1,4,12]),(pl 64 7 0xf1e40a2762f542ac60014fe358424d29ea9c0332652 [11,3,19,12,4,1,6]),(pd 12 20 0x8221fc77cdfed)] (.cons 0xffffff00ffffff00ffffff00000000 (.branch [23,27,16] [(pl 64 7 0x18f332ecf06bfc6a41f208c662e1cd2db1aaa72c0eac9 [3,20,11,12,19,4,1]),(pl 64 6 0x453ca95f4cb10ba4b07650e97c9b5c45366b333 [19,3,1,11,4,20]),(pl 64 6 0x1b2b9015d7452ed67406ae02fcfcc0f9e2fb278c7c [12,1,3,11,19,4]),(pl 64 7 0x54c61363658c17f0ed2e3b873ad9f38ca1d0db4abb7e [1,3,12,11,4,19,20]),(pl 64 8 0x5a687cf0822a8c816361e2291484a12028c84884426c5499 [3,19,4,1,11,20,12,0]),(pl 64 8 0xa48b0c96c96c000000000060000000000c9522404a10b7 [3,19,11,1,20,4,6,12]),(pd 24 22 0x91f7d6f67036da5619f308d5c9)] (.cons 0xfffffa00fffff000fafafa00aaaa00 (.term) (.cons 0xfcfcfc00fcfcf000fcfcfc00cccc00 (.term) (.nil)))) (.nil))) (.cons 0xffffff00ffffff00ffffff00000000 (.branch [31,22,5,36] [(pl 64 9 0x37576ff8d6299bcdb31a9e61d0797b250c4deb4b5de7fc1f7c5 [11,3,1,4,19,12,28,0,13]),(pl 64 7 0x15f98291a192741efc155e0c2f5559297e32ade2d9c4 [11,3,1,19,4,12,28]),(pl 64 8 0x4842a200000000000000000266b65006b43337bc81049840 [3,11,19,12,1,4,28,20]),(pd 25 29 0x2800b7335cb1e9b1a9da5dda72f497)] (.cons 0xffffee00ffffee00eeeeee00cccccc (.branch [38,16,18,27] [(pl 64 6 0x2f306d8b74f896f0586385c104c111eeae809e88e [3,1,4,11,27,12]),(pl 64 7 0x85116489a788f9fa70f51637e72898f80ecdbfec6206 [3,11,1,4,27,28,12]),(pl 64 5 0xfe4f7911913454bb98df145724f6f300da747 [3,4,1,11,27]),(pd 64 31 0xc06dbe013a4541f8eafd98ce065d5ee965af6494e806287108d111fd2f229ab1e1636bdb79b77c9),(pl 64 7 0x580135618fb4cbd96de2bb9d8f1deea1e6b86632200db [3,1,4,11,27,0,20]),(pd 64 31 0xdf083b5f2d400b1f5b458a7d0664045c22665fa9939f80917ccfd45977df5245a0c89ca001c4e1e),(pd 17 31 0xd586be4c394218daca89)] (.cons 0xfffffe00f0f0f000fefefe00000000 (.term) (.cons 0xfffffe00f0f0f000fefefe00f0f0f0 (.term) (.nil)))) (.nil))) (.nil)))))) (.cons 0xffffff00ffffff00ffff0000ffff00 (.branch [28] [(pd 56 7 0x20e3ccc3af34e2b9c0310373945de6b6be87ab09)] (.nil)) (.cons 0xffffff00ffff0000ffffff00ffff00 (.branch [33,11,5] [(pl 64 8 0x4120c9813ac3002006000641049009048242060e9004a081 [2,3,19,11,12,0,6,13]),(pd 20 20 0x52df4418acef5a4bf3caab)] (.cons 0xffffaa00ffff0000aaaaaa00aaaa00 (.branch [27,24] [(pl 64 5 0x21105a3b8aee476dfc77cf594a7f551b9fadb [3,4,1,11,12]),(pl 64 6 0x10e07b87d82d103bcc5f38139d81e02764b517b1cd [3,4,11,1,12,14]),(pd 23 15 0xc720c2f46ca5b57582af1a)] (.cons 0xffffff00ffffff00ffffff00000000 (.branch [24,14,11] [(pd 64 22 0x18452f57f4dfa062a44cead4950dd5a4c97abfc008712095bc2831ec276a8201708f9579),(pd 64 21 0x12509e41d2c3d14ac139ab43bc84af212d734ee4eb6e2103deb9a0b7e5988eabfa248ee),(pd 64 21 0xb708a9352bea7a92fe068e954d484929bc13f6fbbf185f1c8e0c6cff39a451c1667c03),(pl 64 7 0x9271e8ff552e84a97a5b0a05ce2120b7d4a3459a2d2b6 [3,11,1,20,4,5,13]),(pd 64 22 0x60a0c9be7304c28de70fbc6e03546dec50166afb23a89310f13b8b557fc109247b9166d),(pd 52 21 0x19c4675117b43a05d3542b1de9844d32d2cd154f63c04cc47369dbfb2)] (.cons 0xfffffa00fffff000fafafa00aaaa00 (.term) (.cons 0xfcfcfc00fcfcf000fcfcfc00cccc00 (.term) (.nil)))) (.nil))) (.cons 0xffffff00ffffff00ffffff00000000 (.branch [17,10] [(pl 64 6 0x20baf044ae204b661d333fd60a303bcc0ea5d7ede [2,3,12,11,1,4]),(pl 64 5 0x13726bf9d45a176353197e7b9aba5579ddeba9 [2,3,12,1,4]),(pd 64 13 0x63f4abbe59f458802cf74af7ca6248aee206f7aa8cc4eec90e65df4b456),(pd 34 12 0x78406ff8f27f170c8946f56b783d1f)] (.cons 0xfafafa00fafaf000fafafa00aaaa00 (.branch [32,15,0] [(pl 64 5 0x51b5650bd46d228aa19360fe58e94ba475b12 [11,1,4,3,19]),(pl 64 6 0xfe7f4e1164eb059cf83015fd06176768a22386794 [3,4,1,11,19,12]),(pl 64 7 0x47661aeef22875091ec8eb3bf0cf0b6a491b2b33992b6 [4,3,19,1,11,12,14]),(pl 64 5 0x9bb7c3aba9328af2980a4c90fe2867dc865ff [4,3,19,11,1]),(pl 64 5 0x61346a0eaff33f8fead4d9660033430107d2a [3,11,1,4,19]),(pl 64 7 0x3d7be2103eb1bf63482ed8e0e6070791e6873e5177374 [3,4,12,11,19,1,0]),(pl 64 6 0x9ad73e3b7ce3b839632d72264e7d892438bc2239 [3,11,12,1,5,19]),(pd 42 20 0x48b2bd6236de163a74ed337cd5f2e7f7dc56094a4a1af)] (.cons 0xfffffa00fffff000fafafa00aaaa00 (.term) (.nil))) (.cons 0xfffff000fffff000f0f0f000000000 (.branch [23,27] [(pl 64 6 0xe7cc44f48a03f9853d6e43cd23b4dac786f75b9df [2,1,12,11,6,5]),(pd 64 13 0x4b97685e0a31aa480f215609e923ab182085bf2d52794109cea39c37039),(pd 64 14 0xc02b1a57978a4efbc6a6b4cf1d48349dbaddb61f867849958834344839e68),(pd 53 14 0x74d4e6eaeadc6a7e634ce6e61dc76f581944dd7ac74fea25f2)] (.cons 0xfffffa00fffff000fafafa00aaaa00 (.term) (.nil))) (.nil)))) (.nil)))) (.cons 0xffffff00ffffff00ffffff00000000 (.branch [17,30] [(pd 64 13 0x716762029c675bf3abd67af12aed36b9f1efef6c9e01f4f36821b7c0934),(pd 49 16 0x1324232f322332332333323333b2b2232222b222223c242cc)] (.cons 0xfffff000fffff000f0f0f000000000 (.branch [16,23] [(pd 64 15 0x967b34d0ff9634bea0ce28c255076724c8f7d43eefb6d966ce2f155d62d851),(pd 64 15 0x9b6f9510f96beda9d53d1c50d3ee686b0f18c51ab7b69fa38fd38d43714a3b),[5,2,3,1]] (.nil)) (.nil))) (.nil)))))))) (.nil)))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem zid : chkCheckNode zh4 zh5 zh6 s23_raw zh7 zib [] zh9 zic = true := by decide +kernel
def zie : zeV := ⟨7,[(0,1),(0,4),(1,5),(2,4),(2,6),(3,5),(3,6)],[(4,6),(5,6)]⟩
def zif : Nat := 0xffffffffffffffffffff
def zig : Nat := 0x1100000010400120008
def zih : Nat := 0xfff8fffeffccfafa8888
def s26_raw : List Nat := ze6 7 zif
def zii : List Nat := ze8 7 zie.edges zif
def zij : List (List Nat) := []
def zik : List (List Nat) := []
def zil : List zeW := [⟨0,[(1,5)],[1,0,4,2,5],17,[3,6]⟩,⟨4,[],[4,0,1,5],17,[3,6]⟩,⟨34,[],[0,3,4],17,[2,6]⟩,⟨84,[],[0,1],17,[3,5]⟩,⟨76,[],[4,0],17,[1,5]⟩,⟨55,[],[],17,[3,6]⟩,⟨55,[],[],17,[3,6]⟩]
def zim : List zeF := zfb zif s26_raw [(1,[.e [(1,5)]]),(2,[.v 2 [26,64,48]]),(3,[.v 5 [24,2],.v 1 [65]]),(4,[.v 2 [26,65,48],.v 6 [],.v 4 [1]]),(4,[.v 3 [37,66,48],.v 6 [6],.v 2 [16]]),(6,[.v 0 [14,48,24,66],.v 1 [48],.v 4 [36],.v 5 [8],.v 2 [64]]),(6,[.v 1 [1,36],.v 0 [16],.v 4 [36],.v 5 [],.v 2 [64]])]
def zin : CertNode := .branch [5,4,1,0] [(pl 64 7 0x326fb05fed45fd6e1858fd3953d6600acd06335f6c273 [3,11,19,27,0,5,12]),(pd 13 20 0x2e894825777fd3)] (.cons 0xffffffffffff00000000 (.branch [6,4,1,5] [(pl 44 6 0x2827df28a0a7351609d6673af5599 [3,11,19,27,1,5])] (.nil)) (.cons 0xffffffff0000ffff0000 (.branch [3,2,5,4] [(pl 45 7 0x36ab0777970c886f6c0fcef12eba6859 [3,19,11,27,1,4,12])] (.nil)) (.nil)))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem zio : chkCheckNode zif zig zih s26_raw zii zim [] zik zin = true := by decide +kernel
def zip : List zeV := [zhG,s1_desc,s2_desc,zhG,s4_desc,zhG,s6_desc,zhG,zhG,zhG,zhG,zhG,zhG,zhk,zhv,zhG,zhG,zhG,zhH,zhG,zhG,zhG,zhS,zh3,zhG,zhG,zie,zhG]
def ziq : List zeX := [
 ⟨28,7,[(0,1),(0,2),(0,3),(0,4),(1,2),(1,5),(3,4),(3,6),(5,6)],12,13,[],[5,6,2,4,1,3,0]⟩,
 ⟨29,7,[(0,1),(0,2),(0,3),(1,2),(1,4),(2,5),(3,6),(4,6),(5,6)],12,14,[],[3,4,5,6,0,1,2]⟩
]
def zir : List zgK := [
 ⟨zhG, 0, 0, 0, [], [], [], [], [], [], .term⟩,
 ⟨s1_desc, zgS, zgT, zgU, s1_raw, zgV, zgW, s1_auts, s1_cuts, zgX, s1_cert⟩,
 ⟨s2_desc, zgZ, zg0, zg1, s2_raw, zg2, zg3, s2_auts, s2_cuts, zg4, s2_cert⟩,
 ⟨zhG, 0, 0, 0, [], [], [], [], [], [], .term⟩,
 ⟨s4_desc, zg6, zg7, zg8, s4_raw, zg9, zha, s4_auts, s4_cuts, zhb, s4_cert⟩,
 ⟨zhG, 0, 0, 0, [], [], [], [], [], [], .term⟩,
 ⟨s6_desc, zhd, zhe, zhf, s6_raw, zhg, zhh, s6_auts, s6_cuts, zhi, s6_cert⟩,
 ⟨zhG, 0, 0, 0, [], [], [], [], [], [], .term⟩,
 ⟨zhG, 0, 0, 0, [], [], [], [], [], [], .term⟩,
 ⟨zhG, 0, 0, 0, [], [], [], [], [], [], .term⟩,
 ⟨zhG, 0, 0, 0, [], [], [], [], [], [], .term⟩,
 ⟨zhG, 0, 0, 0, [], [], [], [], [], [], .term⟩,
 ⟨zhG, 0, 0, 0, [], [], [], [], [], [], .term⟩,
 ⟨zhk, zhl, zhm, zhn, s13_raw, zho, zhp, zhq, zhs, zhr, zht⟩,
 ⟨zhv, zhw, zhx, zhy, s14_raw, zhz, zhA, zhB, zhD, zhC, zhE⟩,
 ⟨zhG, 0, 0, 0, [], [], [], [], [], [], .term⟩,
 ⟨zhG, 0, 0, 0, [], [], [], [], [], [], .term⟩,
 ⟨zhG, 0, 0, 0, [], [], [], [], [], [], .term⟩,
 ⟨zhH, zhI, zhJ, zhK, s18_raw, zhL, zhM, zhN, zhP, zhO, zhQ⟩,
 ⟨zhG, 0, 0, 0, [], [], [], [], [], [], .term⟩,
 ⟨zhG, 0, 0, 0, [], [], [], [], [], [], .term⟩,
 ⟨zhG, 0, 0, 0, [], [], [], [], [], [], .term⟩,
 ⟨zhS, zhT, zhU, zhV, s22_raw, zhW, zhX, zhY, zh0, zhZ, zh1⟩,
 ⟨zh3, zh4, zh5, zh6, s23_raw, zh7, zh8, zh9, zib, zia, zic⟩,
 ⟨zhG, 0, 0, 0, [], [], [], [], [], [], .term⟩,
 ⟨zhG, 0, 0, 0, [], [], [], [], [], [], .term⟩,
 ⟨zie, zif, zig, zih, s26_raw, zii, zij, zik, zim, zil, zin⟩,
 ⟨zhG, 0, 0, 0, [], [], [], [], [], [], .term⟩,
]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem zis : zir.all (zgN zip) = true := by decide +kernel
theorem zit : ∀ e ∈ zir, e.desc.edges.length ≤ 1 ∨
  chkCheckNode e.maskYF e.edgePts e.edgeTT e.raw e.masksTT e.cuts [] e.auts e.cert = true := by
 intro e he
 simp only [zir, List.mem_cons, List.not_mem_nil, or_false] at he
 rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
 ·exact Or.inl (by decide)
 ·exact Or.inr zgY
 ·exact Or.inr zg5
 ·exact Or.inl (by decide)
 ·exact Or.inr zhc
 ·exact Or.inl (by decide)
 ·exact Or.inr zhj
 ·exact Or.inl (by decide)
 ·exact Or.inl (by decide)
 ·exact Or.inl (by decide)
 ·exact Or.inl (by decide)
 ·exact Or.inl (by decide)
 ·exact Or.inl (by decide)
 ·exact Or.inr zhu
 ·exact Or.inr zhF
 ·exact Or.inl (by decide)
 ·exact Or.inl (by decide)
 ·exact Or.inl (by decide)
 ·exact Or.inr zhR
 ·exact Or.inl (by decide)
 ·exact Or.inl (by decide)
 ·exact Or.inl (by decide)
 ·exact Or.inr zh2
 ·exact Or.inr zid
 ·exact Or.inl (by decide)
 ·exact Or.inl (by decide)
 ·exact Or.inr zio
 ·exact Or.inl (by decide)
theorem ziu : ∀ (i : ℕ) (ch : zeV), zip[i]? = some ch →
  zcU ch.n ch.edges ch.forb (ch.edges.length - 1) :=
 zgO zir (List.all_eq_true.mp zis) zit
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem ziv : ziq.all (zgP zip) = true := by decide +kernel
end OrYF
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
theorem g28_or_ge_eight (C : Circuit) (hc : Monotone2 C)
  (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = OrYF.g28_fn x) :
  8 ≤ OrYF.zc5 C.gates := by
 exact OrYF.zgR OrYF.zeS OrYF.ziu
  OrYF.ziv 0 _ rfl rfl rfl C hc he
theorem ziw (C : Circuit) (hc : Monotone2 C)
  (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = OrYF.g29_fn x) :
  8 ≤ OrYF.zc5 C.gates := by
 exact OrYF.zgR OrYF.zeU OrYF.ziu
  OrYF.ziv 1 _ rfl rfl rfl C hc he
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def rewire {n m : Nat} (rho : Fin n → Fin m) (j : Nat) : Nat :=
 if h : j < n then (rho ⟨j, h⟩).val else m + (j - n)
lemma zix {n m : Nat} (rho : Fin n → Fin m) (t j : Nat) :
  rewire rho j < m + t ↔ j < n + t := by
 unfold rewire
 split
 ·rename_i h
  have := (rho ⟨j, h⟩).isLt
  omega
 ·omega
lemma ziy {n m : Nat} (rho : Fin n → Fin m) (t j : Nat) :
  rewire rho j = m + t ↔ j = n + t := by
 unfold rewire
 split
 ·rename_i h
  have := (rho ⟨j, h⟩).isLt
  omega
 ·omega
def ziz {n m : Nat} (rho : Fin n → Fin m) (g : Gate) : Gate :=
 {op := g.op, inputs := g.inputs.map (rewire rho)}
def ziA {n m : Nat} (rho : Fin n → Fin m) (C : Circuit) : Circuit :=
 {gates := C.gates.map (ziz rho), output := rewire rho C.output}
def ziB (gs : List Gate) (w : List Bool) : List Bool :=
 gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w
lemma ziC (w : List Bool) (b : Bool) (j : Nat) :
  (w ++ [b]).getD j false =
   if j < w.length then w.getD j false else if j = w.length then b else false := by
 split_ifs with h1 h2
 ·exact List.getD_append _ _ _ _ h1
 ·subst h2
  simp
 ·rw [List.getD_eq_default]
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega
lemma ziD {n m : Nat} (rho : Fin n → Fin m) (t : Nat)
  (zX zW : List Bool) (b : Bool)
  (vo : zX.length = n + t) (xz : zW.length = m + t)
  (xk : ∀ j, zW.getD (rewire rho j) false = zX.getD j false) :
  ∀ j, (zW ++ [b]).getD (rewire rho j) false = (zX ++ [b]).getD j false := by
 intro j
 simp only [ziC, vo, xz, zix, ziy]
 split_ifs <;> simp_all
lemma ziE {n m : Nat} (rho : Fin n → Fin m) (g : Gate)
  (zX zW : List Bool)
  (xk : ∀ j, zW.getD (rewire rho j) false = zX.getD j false) :
  (ziz rho g).op.eval ((ziz rho g).inputs.map fun i => zW.getD i false) =
   g.op.eval (g.inputs.map fun i => zX.getD i false) := by
 simp only [ziz, List.map_map]
 congr 1
 apply List.map_congr_left
 intro j _
 exact xk j
lemma ziF {n m : Nat} (rho : Fin n → Fin m) (gs : List Gate) :
  ∀ (t : Nat) (zX zW : List Bool),
  zX.length = n + t → zW.length = m + t →
  (∀ j, zW.getD (rewire rho j) false = zX.getD j false) →
  ∀ j, (ziB (gs.map (ziz rho)) zW).getD (rewire rho j) false =
   (ziB gs zX).getD j false := by
 induction gs with
 | nil => intro t zX zW vo xz xk j; exact xk j
 | cons g gs ih =>
   intro t zX zW vo xz xk j
   simp only [List.map_cons, ziB, List.foldl_cons]
   rw [ziE rho g zX zW xk]
   apply ih (t + 1)
   ·simp [vo, Nat.add_assoc]
   ·simp [xz, Nat.add_assoc]
   ·exact ziD rho t zX zW _ vo xz xk
lemma ziG {n m : Nat} (rho : Fin n → Fin m) (x : Fin m → Bool) (j : Nat) :
  (List.ofFn x).getD (rewire rho j) false = (List.ofFn (fun i => x (rho i))).getD j false := by
 by_cases hj : j < n
 ·simp only [rewire, dif_pos hj]
  rw [List.getD_eq_getElem _ _ (by simpa using (rho ⟨j, hj⟩).isLt)]
  rw [List.getD_eq_getElem _ _ (by simpa using hj)]
  simp only [List.getElem_ofFn]
 ·simp only [rewire, dif_neg hj]
  rw [List.getD_eq_default _ _ (by simp only [List.length_ofFn]; omega)]
  rw [List.getD_eq_default _ _ (by simp only [List.length_ofFn]; omega)]
lemma ziH {n m : Nat} (rho : Fin n → Fin m) (C : Circuit) (x : Fin m → Bool) :
  (ziA rho C).eval (List.ofFn x) = C.eval (List.ofFn (fun i => x (rho i))) := by
 exact ziF rho C.gates 0 (List.ofFn (fun i => x (rho i))) (List.ofFn x)
  (by simp) (by simp) (ziG rho x) C.output
lemma ziI {n m : Nat} (rho : Fin n → Fin m) (C : Circuit) (hC : Monotone2 C) :
  Monotone2 (ziA rho C) := by
 intro g hg
 obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
 simpa [ziz] using hC g0 hg0
lemma ziJ {n m : Nat} (rho : Fin n → Fin m) (C : Circuit) (p : GateOp → Bool) :
  ((ziA rho C).gates.filter (fun g => p g.op)).length =
   (C.gates.filter (fun g => p g.op)).length := by
 simp only [ziA, List.filter_map, List.length_map]
 rfl
def ziK : Fin 8 → Fin 7 := ![5, 0, 1, 6, 4, 2, 3, 0]
def t1Graph (x : Fin 8 → Bool) : Bool :=
 (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) ||
 (x 2 && x 5) || (x 2 && x 7) || (x 3 && x 6) || (x 4 && x 6) ||
 (x 4 && x 7) || (x 5 && x 7) || (x 6 && x 7)
def ziL (x : Fin 7 → Bool) : Bool :=
 (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) ||
 (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6) || (x 5 && x 6)
lemma ziM : ∀ x : Fin 7 → Bool,
  t1Graph (Function.update (fun i => x (ziK i)) 1 false) = ziL x := by
 decide +kernel
lemma ziN (D : Circuit)
  (hD : ∀ x : Fin 8 → Bool, D.eval (List.ofFn x) = t1Graph (Function.update x 1 false)) :
  ∀ x : Fin 7 → Bool, (ziA ziK D).eval (List.ofFn x) = ziL x := by
 intro x
 rw [ziH, hD, ziM]
lemma ziO : ∀ u v : Fin 8, u ≠ v → ∃ w : Fin 8,
  t1Graph (fun i => decide (i = v ∨ i = w)) = true ∧
  t1Graph (fun i => decide (i = u ∨ i = w)) = false := by
 decide +kernel
lemma ziP : ∀ u v : Fin 8, u ≠ v → ∃ w : Fin 8,
  t1Graph (Function.update (fun i => decide (i = w)) v true) = true ∧
  t1Graph (Function.update (Function.update (fun i => decide (i = w)) v false) u true) = false := by
 decide +kernel
lemma ziQ (u v : Fin 8) (hne : u ≠ v)
  (qu : ∀ x : Fin 8 → Bool,
   t1Graph (Function.update x v true) = true →
   t1Graph (Function.update (Function.update x v false) u true) = true) : False := by
 obtain ⟨w, hpos, xo⟩ := ziP u v hne
 have h := qu (fun i => decide (i = w)) hpos
 rw [xo] at h
 contradiction
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def ziR : Fin 8 → Fin 7 := ![6, 3, 4, 5, 0, 0, 2, 1]
def ziS : Fin 8 → Fin 7 := ![5, 6, 1, 0, 3, 2, 4, 0]
def ziT (x : Fin 7 → Bool) : Bool :=
 (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) ||
 (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6) || (x 5 && x 6)
lemma ziU : ∀ x : Fin 7 → Bool,
  t1Graph (Function.update (fun i => x (ziR i)) 5 false) = ziT x := by
 decide +kernel
lemma ziV : ∀ x : Fin 7 → Bool,
  t1Graph (Function.update (fun i => x (ziS i)) 3 false) = ziL x := by
 decide +kernel
lemma ziW (D : Circuit)
  (hD : ∀ x : Fin 8 → Bool, D.eval (List.ofFn x) = t1Graph (Function.update x 5 false)) :
  ∀ x : Fin 7 → Bool, (ziA ziR D).eval (List.ofFn x) = ziT x := by
 intro x
 rw [ziH, hD, ziU]
lemma ziX (D : Circuit)
  (hD : ∀ x : Fin 8 → Bool, D.eval (List.ofFn x) = t1Graph (Function.update x 3 false)) :
  ∀ x : Fin 7 → Bool, (ziA ziS D).eval (List.ofFn x) = ziL x := by
 intro x
 rw [ziH, hD, ziV]
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
lemma ziY (gs : List Gate) : Pin.orCount gs = OrYF.zc5 gs := by
 simp only [Pin.orCount, OrYF.zc5, List.countP_eq_length_filter]
 rfl
lemma ziZ {n m : Nat} (rho : Fin n → Fin m) (D : Circuit) :
  Pin.orCount (ziA rho D).gates = Pin.orCount D.gates := by
 simp only [Pin.orCount, List.countP_eq_length_filter]
 exact ziJ rho D Pin.isOr
lemma zi0 (C : Circuit) (qr : Monotone2 C)
  (qL : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = t1Graph x) :
  9 ≤ Pin.orCount C.gates := by
 have wD : ∃ x : Fin 8 → Bool,
   C.eval (List.ofFn x) ≠ C.eval (List.ofFn (Function.update x 1 false)) := by
  refine ⟨![true, true, false, false, false, false, false, false], ?_⟩
  rw [qL, qL]
  decide
 have qE : ∃ x : Fin 8 → Bool,
   C.eval (List.ofFn (Function.update x 1 false)) = true := by
  refine ⟨![true, false, true, false, false, false, false, false], ?_⟩
  rw [qL]
  decide
 have q5 : ∃ x : Fin 8 → Bool,
   C.eval (List.ofFn (Function.update x 1 false)) = false := by
  refine ⟨fun _ => false, ?_⟩
  rw [qL]
  decide
 obtain ⟨D, hmD, hless, hD⟩ := Pin.zcl 8 C 1 qr wD qE q5
 have ue : ∀ x : Fin 8 → Bool, D.eval (List.ofFn x) = t1Graph (Function.update x 1 false) := by
  intro x
  rw [hD, qL]
 have zP : ∀ x : Fin 7 → Bool,
   (ziA ziK D).eval (List.ofFn x) = OrYF.g28_fn x :=
  ziN D ue
 have h8 := g28_or_ge_eight (ziA ziK D)
  (ziI ziK D hmD) zP
 rw [← ziY, ziZ] at h8
 omega
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
lemma zi1 (op : GateOp) : Pin.isOr op = true ↔ op = GateOp.or := by
 cases op <;> simp [Pin.isOr]
lemma zi2 (gs : List Gate) :
  (gs.filter (fun g => Pin.isOr g.op)).length =
   Nat.card {j : Fin gs.length // (gs.get j).op = GateOp.or} := by
 classical
 have yY : (gs.filter (fun g => Pin.isOr g.op)).length =
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
 have vI : (∑ j : Fin gs.length, if Pin.isOr (gs.get j).op = true then 1 else 0) =
   ∑ j : Fin gs.length, if (gs.get j).op = GateOp.or then 1 else 0 := by
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [zi1]
 rw [yY, vI, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
lemma zi3 {n : Nat} (ops : Fin n → Bool) (a b : Fin n → Nat) :
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
lemma zi4 {n : Nat} (ops : Fin n → Bool) (a b : Fin n → Nat) :
  Pin.orCount (convertedGates ops a b) = Nat.card {i : Fin n // ops i = false} := by
 rw [Pin.orCount, List.countP_eq_length_filter, zi2, zi3]
lemma witness_or_count_ge_nine
  (ops : Fin 14 → Bool) (a b : Fin 14 → Fin 33) (v : Nat → Nat)
  (qi : ∀ i : Fin 11, v i.val = baseValues.getD i.val 0)
  (ha : ∀ i, (a i).val ∈ allowedInputs ∨ 11 ≤ (a i).val)
  (hb : ∀ i, (b i).val ∈ allowedInputs ∨ 11 ≤ (b i).val)
  (hs : ∀ i, (a i).val < 11 + i.val ∧ (b i).val < 11 + i.val ∧
   v (11 + i.val) = if ops i then v (a i).val &&& v (b i).val else v (a i).val ||| v (b i).val)
  (ql : v 24 = 36671) :
  9 ≤ Nat.card {i : Fin 14 // ops i = false} := by
 let D : Circuit := { gates := convertedGates ops (fun i => (a i).val) (fun i => (b i).val), output := 21 }
 have qp := zbX ops (fun i => (a i).val) (fun i => (b i).val)
 have hmD : Monotone2 D := by
  intro g hg
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
  cases h : ops i <;> simp [convertedGate, h]
 have qJ : ∀ k : Fin 40, circuitFun 8 D (sample k) = (36671 : Nat).testBit k.val := by
  intro k
  change (wiresFrom (convertedGates ops (fun i => (a i).val) (fun i => (b i).val))
   (List.ofFn (sample k))).getD 21 false = _
  rw [zbZ ops (fun i => (a i).val) (fun i => (b i).val) v qi ha hb hs k]
  have qI := zbW (n := 14) v k 24 qi (by decide) (Or.inr (by decide))
  have zk : wireIndex 24 = 21 := by decide
  rw [zk, ql] at qI
  exact qI
 have zB := zbP (circuitFun 8 D) (zbS D qp) qJ
 have qZ : targetFun = t1Graph := by
  funext x
  simp [targetFun, edgesT1, t1Graph, Bool.or_assoc]
 have qL : ∀ x : Fin 8 → Bool, D.eval (List.ofFn x) = t1Graph x := by
  intro x
  exact (congrFun zB x).trans (congrFun qZ x)
 have h9 := zi0 D hmD qL
 change 9 ≤ Pin.orCount (convertedGates ops (fun i => (a i).val) (fun i => (b i).val)) at h9
 rwa [zi4] at h9
lemma zi5 {n : Nat} (ops : Fin n → Bool) :
  Nat.card {i : Fin n // ops i = true} + Nat.card {i : Fin n // ops i = false} = n := by
 have h := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i : Fin n => ops i = true)
 simpa [Nat.card_eq_fintype_card, Fintype.card_subtype] using h
lemma witness_exact_gate_counts
  (ops : Fin 14 → Bool) (a b : Fin 14 → Fin 33) (v : Nat → Nat)
  (qi : ∀ i : Fin 11, v i.val = baseValues.getD i.val 0)
  (ha : ∀ i, (a i).val ∈ allowedInputs ∨ 11 ≤ (a i).val)
  (hb : ∀ i, (b i).val ∈ allowedInputs ∨ 11 ≤ (b i).val)
  (hs : ∀ i, (a i).val < 11 + i.val ∧ (b i).val < 11 + i.val ∧
   v (11 + i.val) = if ops i then v (a i).val &&& v (b i).val else v (a i).val ||| v (b i).val)
  (ql : v 24 = 36671) :
  Nat.card {i : Fin 14 // ops i = true} = 5 ∧ Nat.card {i : Fin 14 // ops i = false} = 9 := by
 have hA := witness_and_count_ge_five ops a b v qi ha hb hs ql
 have hO := witness_or_count_ge_nine ops a b v qi ha hb hs ql
 have yY := zi5 ops
 omega
namespace Pin
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def opCount (p : GateOp → Bool) (gs : List Gate) : ℕ := gs.countP (fun g => p g.op)
def zi6 (p : GateOp → Bool) (k : ℕ) (gs : List Gate) : ℕ :=
 gs.countP (fun g => p g.op && decide (k ∈ g.inputs))
theorem zi7 (p : GateOp → Bool) (op : GateOp) (m : ℕ) (ins : List Stat) :
  opCount p (zb5 op m ins).1.toList ≤ if p op then 1 else 0 := by
 cases op <;> rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;>
  (try cases a) <;> (try cases b) <;>
  simp [zb5, simpAnd, simpOr, opCount]
theorem zi8 (p : GateOp → Bool) (gs hs : List Gate) :
  opCount p (gs ++ hs) = opCount p gs + opCount p hs := by
 simp [opCount]
theorem zi9 (p : GateOp → Bool) (g : Gate) (gs : List Gate) :
  opCount p (g :: gs) = (if p g.op then 1 else 0) + opCount p gs := by
 simp [opCount, List.countP_cons, Nat.add_comm]
theorem zja (p : GateOp → Bool) (k : ℕ) (g : Gate) (gs : List Gate) :
  zi6 p k (g :: gs) =
   (if p g.op && decide (k ∈ g.inputs) then 1 else 0) + zi6 p k gs := by
 simp [zi6, List.countP_cons, Nat.add_comm]
theorem zjb (p : GateOp → Bool) (n k : ℕ) (b : Bool) (gs : List Gate) :
  ∀ acc : List Stat × List Gate, (∀ g ∈ gs, Ok g) → k < acc.1.length →
   acc.1.getD k (Sum.inl false) = Sum.inl b →
   opCount p (elim n gs acc).2 + zi6 p k gs ≤ opCount p acc.2 + opCount p gs := by
 induction gs with
 | nil => intro acc _ _ _; simp [elim, opCount, zi6]
 | cons g gs ih =>
  intro acc hok hk hc
  have h1 := ih (zb9 n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
   (by simp [zb9]; omega)
   (by simp only [zb9]; rw [zb4 _ _ _ _ (by omega)]; exact hc)
  have qQ : opCount p (zb9 n acc g).2 = opCount p acc.2 +
    opCount p (zb5 g.op (n + acc.2.length)
     (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList := by
   simp only [zb9, zi8]
  rw [qQ] at h1
  change opCount p (elim n gs (zb9 n acc g)).2 + zi6 p k (g :: gs) ≤ _
  rw [zi9, zja]
  by_cases hkg : k ∈ g.inputs
  ·have uF := hok g List.mem_cons_self
   have zC : (zb5 g.op (n + acc.2.length)
     (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
    apply zb7
    ·exact uF.1
    ·simpa using uF.2
    ·exact ⟨b, List.mem_map.2 ⟨k, hkg, hc⟩⟩
   rw [zC] at h1
   simp only [Option.toList_none, show opCount p [] = 0 from rfl, Nat.add_zero] at h1
   simp only [hkg, decide_true, Bool.and_true]
   omega
  ·have xy := zi7 p g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
   simp only [hkg, decide_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
   omega
def isAnd : GateOp → Bool
 | .and => true
 | _ => false
def Corr (t : Bool) (s : Stat) (a b : Bool) : Prop :=
 (s = Sum.inl false → (a = true → t = true) ∧ (b = true → t = true)) ∧
 (s ≠ Sum.inl false → a = b)
set_option maxHeartbeats 4000000 in
theorem zjc (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
  (m : ℕ) (ins : List Stat) (yJ : List (Bool × Bool)) (t yw : Bool)
  (qe : ins.length ≤ 2)
  (hr : List.Forall₂ (fun s p => Corr t s p.1 p.2) ins yJ)
  (wY : yw = true → Sum.inl false ∈ ins)
  (uM : yw = true → (t, t) ∈ yJ)
  (xP : op = GateOp.or → yw = false → orCount (zb5 op m ins).1.toList = 1) :
  Corr t (zb5 op m ins).2 (op.eval (yJ.map Prod.fst))
   (if isAnd op && yw then false else op.eval (yJ.map Prod.snd)) := by
 rcases hop with rfl | rfl
 all_goals
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  ·cases hr
   cases yw <;> cases t <;>
    simp_all [Corr, zb5, simpAnd, simpOr, orCount, isOr, isAnd, GateOp.eval] <;> aesop
  ·cases hr with
   | cons ha ht =>
    cases ht
    rename_i p
    rcases p with ⟨p1, p2⟩
    cases yw <;> cases t <;>
     cases a with
     | inl ca => cases ca <;>
       simp_all [Corr, zb5, simpAnd, simpOr, orCount, isOr, isAnd, GateOp.eval] <;> aesop
     | inr ia =>
       simp_all [Corr, zb5, simpAnd, simpOr, orCount, isOr, isAnd, GateOp.eval] <;> aesop
  ·cases hr with
   | cons ha ht =>
    cases ht with
    | cons hb htt =>
     cases htt
     rename_i p q
     rcases p with ⟨p1, p2⟩
     rcases q with ⟨q1, q2⟩
     cases yw <;> cases t <;>
      rcases a with ca | ia <;> rcases b with cb | ib
     all_goals first
      | (cases ca <;> cases cb <;>
        simp_all [Corr, zb5, simpAnd, simpOr, orCount, isOr, isAnd, GateOp.eval] <;> aesop)
      | (cases ca <;>
        simp_all [Corr, zb5, simpAnd, simpOr, orCount, isOr, isAnd, GateOp.eval] <;> aesop)
      | (cases cb <;>
        simp_all [Corr, zb5, simpAnd, simpOr, orCount, isOr, isAnd, GateOp.eval] <;> aesop)
      | simp_all [Corr, zb5, simpAnd, simpOr, orCount, isOr, isAnd, GateOp.eval] <;> aesop
  ·simp at qe
def zjd (k : ℕ) (g : Gate) : Gate :=
 if isAnd g.op && decide (k ∈ g.inputs) then ⟨GateOp.or, []⟩ else g
theorem zje (k : ℕ) (g : Gate) (w : List Bool) :
  (zjd k g).op.eval ((zjd k g).inputs.map fun i => w.getD i false) =
  if isAnd g.op && decide (k ∈ g.inputs) then false
  else g.op.eval (g.inputs.map fun i => w.getD i false) := by
 cases h1 : isAnd g.op <;> by_cases h2 : k ∈ g.inputs <;>
  simp [zjd, h1, h2, GateOp.eval]
theorem zjf (n k : ℕ) (t : Bool) (gs : List Gate) :
  ∀ (w w' : List Bool) (acc : List Stat × List Gate),
   (∀ g ∈ gs, Ok g) → acc.1.length = w.length → w.length = w'.length →
   (∀ i, Corr t (acc.1.getD i (Sum.inl false)) (w.getD i false) (w'.getD i false)) →
   k < acc.1.length → acc.1.getD k (Sum.inl false) = Sum.inl false →
   w.getD k false = t → w'.getD k false = t →
   orCount (elim n gs acc).2 + zi6 isOr k gs = orCount acc.2 + orCount gs →
   ∀ i, Corr t ((elim n gs acc).1.getD i (Sum.inl false))
    ((wiresFrom gs w).getD i false)
    ((wiresFrom (gs.map (zjd k)) w').getD i false) := by
 induction gs with
 | nil => intro w w' acc _ _ _ h _ _ _ _ _ i; exact h i
 | cons g gs ih =>
  intro w w' acc hok qe q9 hc hk vE qX wi qS
  have qQ : orCount (zb9 n acc g).2 = orCount acc.2 +
    orCount (zb5 g.op (n + acc.2.length)
     (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList := by
   simp only [zb9, zcg]
  have vF : (zb9 n acc g).1.getD k (Sum.inl false) = Sum.inl false := by
   simp only [zb9]
   rw [zb4 _ _ _ _ (by omega)]
   exact vE
  have hk' : k < (zb9 n acc g).1.length := by simp only [zb9, List.length_append, List.length_singleton]; omega
  have zf : orCount (elim n gs (zb9 n acc g)).2 + zi6 isOr k gs ≤
    orCount (zb9 n acc g).2 + orCount gs :=
   zjb isOr n k false gs (zb9 n acc g)
    (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) hk' vF
  rw [qQ] at zf
  have xy := zce g.op (n + acc.2.length)
   (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
  have ua : orCount (zb5 g.op (n + acc.2.length)
     (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList +
    (if isOr g.op && decide (k ∈ g.inputs) then 1 else 0) ≤
    if isOr g.op then 1 else 0 := by
   by_cases hkg : k ∈ g.inputs
   ·have zC : (zb5 g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
     apply zb7
     ·exact (hok g List.mem_cons_self).1
     ·simpa using (hok g List.mem_cons_self).2
     ·exact ⟨false, List.mem_map.2 ⟨k, hkg, vE⟩⟩
    rw [zC]
    simp [orCount, hkg]
   ·simpa [hkg] using xy
  have vT : orCount (elim n gs (zb9 n acc g)).2 +
    ((if isOr g.op && decide (k ∈ g.inputs) then 1 else 0) + zi6 isOr k gs) =
    orCount acc.2 + ((if isOr g.op then 1 else 0) + orCount gs) := by
   simpa only [elim, List.foldl_cons, zch, zja] using qS
  have vd : orCount (zb5 g.op (n + acc.2.length)
     (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList +
    (if isOr g.op && decide (k ∈ g.inputs) then 1 else 0) =
    if isOr g.op then 1 else 0 := by omega
  have xP : g.op = GateOp.or → decide (k ∈ g.inputs) = false →
    orCount (zb5 g.op (n + acc.2.length)
     (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList = 1 := by
   intro hop zb
   simpa [hop, zb, isOr] using vd
  have xk : List.Forall₂ (fun s p => Corr t s p.1 p.2)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
    (g.inputs.map fun i => (w.getD i false, w'.getD i false)) := by
   induction g.inputs with
   | nil => exact List.Forall₂.nil
   | cons i is ih => exact List.Forall₂.cons (hc i) ih
  have xM := zjc g.op (hok g List.mem_cons_self).1 (n + acc.2.length)
   (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
   (g.inputs.map fun i => (w.getD i false, w'.getD i false)) t (decide (k ∈ g.inputs))
   (by simpa using (hok g List.mem_cons_self).2) xk
   (by intro h; exact List.mem_map.2 ⟨k, of_decide_eq_true h, vE⟩)
   (by intro h; exact List.mem_map.2 ⟨k, of_decide_eq_true h, Prod.ext qX wi⟩) xP
  simp only [List.map_map, Function.comp_def] at xM
  rw [← zje k g w'] at xM
  apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
   (w' ++ [(zjd k g).op.eval
    ((zjd k g).inputs.map fun i => w'.getD i false)]) (zb9 n acc g)
   (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
  ·simp [zb9, qe]
  ·simp [q9]
  ·intro i
   change Corr t ((acc.1 ++ [_]).getD i (Sum.inl false))
    ((w ++ [_]).getD i false) ((w' ++ [_]).getD i false)
   by_cases hi : i = acc.1.length
   ·subst hi
    rw [getD_snoc_eq, qe, getD_snoc_eq, q9, getD_snoc_eq]
    exact xM
   ·rw [zb4 _ _ _ _ hi, zb4 _ _ _ _ (by omega),
     zb4 _ _ _ _ (by omega)]
    exact hc i
  ·exact hk'
  ·exact vF
  ·rw [zb4 _ _ _ _ (by omega)]; exact qX
  ·rw [zb4 _ _ _ _ (by omega)]; exact wi
  ·rw [qQ]; omega
theorem zjg (n : ℕ) (v : Fin n) (x : Fin n → Bool) :
  ∀ i, Corr (x v) ((zcc n v false).getD i (Sum.inl false))
   ((List.ofFn x).getD i false) ((List.ofFn x).getD i false) := by
 intro i
 by_cases hi : i < n
 ·by_cases hv : (⟨i, hi⟩ : Fin n) = v
  ·subst hv
   simp [zcc, hi, Corr]
  ·simp [zcc, hi, hv, Corr]
 ·have hs : (zcc n v false).getD i (Sum.inl false) = Sum.inl false :=
   List.getD_eq_default _ _ (by simp only [zcc, List.length_ofFn]; omega)
  have hx : (List.ofFn x).getD i false = false :=
   List.getD_eq_default _ _ (by simp only [List.length_ofFn]; omega)
  rw [hs, hx]
  simp [Corr]
theorem zjh (k : ℕ) (g : Gate) (h : Ok g) : Ok (zjd k g) := by
 cases h1 : isAnd g.op <;> by_cases h2 : k ∈ g.inputs
 all_goals simp [zjd, h1, h2, Ok] at * <;> assumption
theorem zji (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (v : Fin n)
  (qr : PEqualNP.MetaComplexity.Monotone2 C)
  (qE : ∃ x : Fin n → Bool,
   C.eval (List.ofFn (Function.update x v false)) = true)
  (heq : orCount (elim n C.gates (zcc n v false, [])).2 +
    zi6 isOr v.val C.gates = orCount C.gates) :
  PEqualNP.MetaComplexity.Monotone2 ⟨C.gates.map (zjd v.val), C.output⟩ ∧
  ∀ x : Fin n → Bool,
   (⟨C.gates.map (zjd v.val), C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit).eval
    (List.ofFn x) = C.eval (List.ofFn x) := by
 have hok : ∀ g ∈ C.gates, Ok g := by
  intro g hg
  obtain ⟨h1, h2⟩ := qr g hg
  exact ⟨by simpa using h1, h2⟩
 set acc := elim n C.gates (zcc n v false, []) with q4
 have hst : acc.1.getD C.output (Sum.inl false) ≠ Sum.inl false := by
  intro hh
  obtain ⟨y, hy⟩ := qE
  have yO := zcb n (List.ofFn y) (by simp) C.gates _ _ hok (zcd n v false y)
  have hv := (yO.2 C.output).2
  change (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn y)) =
   C.eval (List.ofFn (Function.update y v false)) at hv
  rw [hh] at hv
  exact Bool.false_ne_true (hv.trans hy)
 refine ⟨?_, ?_⟩
 ·intro g hg
  obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
  obtain ⟨hop, qe⟩ := zjh v.val g' (hok g' hg')
  exact ⟨by simpa using hop, qe⟩
 ·intro x
  have xM := zjf n v.val (x v) C.gates (List.ofFn x) (List.ofFn x)
   (zcc n v false, []) hok (by simp [zcc]) rfl (zjg n v x)
   (by simp [zcc]) (by simp [zcc]) (by simp) (by simp)
   (by simpa only [orCount, List.countP_nil, Nat.zero_add] using heq)
  have h := (xM C.output).2 hst
  exact h.symm
theorem zjj (k : ℕ) (gs : List Gate) :
  opCount isAnd (gs.map (zjd k)) + zi6 isAnd k gs = opCount isAnd gs := by
 induction gs with
 | nil => simp [opCount, zi6]
 | cons g gs ih =>
  rw [List.map_cons, zi9, zi9, zja]
  by_cases zb : k ∈ g.inputs
  ·cases hop : g.op <;> simp [zjd, hop, isAnd, zb] <;> omega
  ·simp [zjd, zb]
   omega
theorem zjk (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (v : Fin n)
  (qr : PEqualNP.MetaComplexity.Monotone2 C)
  (qE : ∃ x : Fin n → Bool,
   C.eval (List.ofFn (Function.update x v false)) = true)
  (qz : ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
   PEqualNP.MetaComplexity.Monotone2 D →
   (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) →
   opCount isAnd C.gates ≤ opCount isAnd D.gates)
  (u5 : 0 < zi6 isAnd v.val C.gates) :
  orCount (elim n C.gates (zcc n v false, [])).2 +
   zi6 isOr v.val C.gates + 1 ≤ orCount C.gates := by
 have hok : ∀ g ∈ C.gates, Ok g := by
  intro g hg
  obtain ⟨h1, h2⟩ := qr g hg
  exact ⟨by simpa using h1, h2⟩
 have hle : orCount (elim n C.gates (zcc n v false, [])).2 +
   zi6 isOr v.val C.gates ≤ orCount C.gates := by
  simpa only [opCount, orCount, List.countP_nil, Nat.zero_add] using
   zjb isOr n v.val false C.gates (zcc n v false, []) hok
    (by simp [zcc]) (by simp [zcc])
 by_contra hn
 have heq : orCount (elim n C.gates (zcc n v false, [])).2 +
   zi6 isOr v.val C.gates = orCount C.gates := by omega
 obtain ⟨hm, he⟩ := zji n C v qr qE heq
 have wR := qz ⟨C.gates.map (zjd v.val), C.output⟩ hm he
 have qS := zjj v.val C.gates
 change opCount isAnd C.gates ≤ opCount isAnd (C.gates.map (zjd v.val)) at wR
 omega
theorem zjl (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (v : Fin n) (b : ℕ)
  (qr : PEqualNP.MetaComplexity.Monotone2 C)
  (qE : ∃ x : Fin n → Bool,
   C.eval (List.ofFn (Function.update x v false)) = true)
  (q5 : ∃ x : Fin n → Bool,
   C.eval (List.ofFn (Function.update x v false)) = false)
  (qz : ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
   PEqualNP.MetaComplexity.Monotone2 D →
   (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) →
   opCount isAnd C.gates ≤ opCount isAnd D.gates)
  (ye : ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
   PEqualNP.MetaComplexity.Monotone2 D →
   (∀ x : Fin n → Bool,
    D.eval (List.ofFn x) = C.eval (List.ofFn (Function.update x v false))) →
   opCount isAnd C.gates ≤ opCount isAnd D.gates + 1)
  (ve : ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
   PEqualNP.MetaComplexity.Monotone2 D →
   (∀ x : Fin n → Bool,
    D.eval (List.ofFn x) = C.eval (List.ofFn (Function.update x v false))) →
   b ≤ orCount D.gates) :
  zi6 isAnd v.val C.gates + zi6 isOr v.val C.gates + b ≤ orCount C.gates := by
 have hok : ∀ g ∈ C.gates, Ok g := by
  intro g hg
  obtain ⟨h1, h2⟩ := qr g hg
  exact ⟨by simpa using h1, h2⟩
 set acc := elim n C.gates (zcc n v false, []) with q4
 have zl : ∀ y : Fin n → Bool,
   (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn y)) =
    C.eval (List.ofFn (Function.update y v false)) := by
  intro y
  exact ((zcb n (List.ofFn y) (by simp) C.gates _ _ hok
   (zcd n v false y)).2 C.output).2
 have hmD : ∀ out : ℕ, PEqualNP.MetaComplexity.Monotone2 ⟨acc.2, out⟩ := by
  intro out g hg
  obtain ⟨h1, h2⟩ := elim_ok n C.gates _ (by simp) g hg
  exact ⟨by simpa using h1, h2⟩
 have ql : ∃ j, acc.1.getD C.output (Sum.inl false) = Sum.inr j := by
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inr j => exact ⟨j, rfl⟩
  | inl c =>
   cases c with
   | false =>
    obtain ⟨y, hy⟩ := qE
    have hv := zl y
    rw [hst] at hv
    exact False.elim (Bool.false_ne_true (hv.trans hy))
   | true =>
    obtain ⟨y, hy⟩ := q5
    have hv := zl y
    rw [hst] at hv
    exact False.elim (Bool.false_ne_true (hv.trans hy).symm)
 obtain ⟨j, hj⟩ := ql
 have he : ∀ y : Fin n → Bool,
   (⟨acc.2, j⟩ : PEqualNP.CircuitLowerBounds.Circuit).eval (List.ofFn y) =
   C.eval (List.ofFn (Function.update y v false)) := by
  intro y
  have hv := zl y
  rw [hj] at hv
  exact hv
 have ha := ye ⟨acc.2, j⟩ (hmD _) he
 have hb := ve ⟨acc.2, j⟩ (hmD _) he
 change opCount isAnd C.gates ≤ opCount isAnd acc.2 + 1 at ha
 change b ≤ orCount acc.2 at hb
 have ha' : opCount isAnd acc.2 + zi6 isAnd v.val C.gates ≤ opCount isAnd C.gates := by
  simpa only [← q4, opCount, orCount, List.countP_nil, Nat.zero_add] using
   zjb isAnd n v.val false C.gates (zcc n v false, []) hok
    (by simp [zcc]) (by simp [zcc])
 have hr : zi6 isAnd v.val C.gates ≤ 1 := by omega
 by_cases xu : zi6 isAnd v.val C.gates = 0
 ·have ho : orCount acc.2 + zi6 isOr v.val C.gates ≤ orCount C.gates := by
   simpa only [← q4, opCount, orCount, List.countP_nil, Nat.zero_add] using
    zjb isOr n v.val false C.gates (zcc n v false, []) hok
     (by simp [zcc]) (by simp [zcc])
  omega
 ·have ho := zjk n C v qr qE qz (by omega)
  rw [← q4] at ho
  omega
end Pin
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
lemma zjm (k : ℕ) (gs : List Gate)
  (hok : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
  Pin.zi6 Pin.isAnd k gs + Pin.zi6 Pin.isOr k gs =
   gs.countP (fun g => decide (k ∈ g.inputs)) := by
 induction gs with
 | nil => simp [Pin.zi6]
 | cons g gs ih =>
  have hg := hok g List.mem_cons_self
  have ht := ih (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
  rw [Pin.zja, Pin.zja, List.countP_cons]
  rcases hg with hg | hg <;> by_cases hr : k ∈ g.inputs <;>
   simp [hg, hr, Pin.isAnd, Pin.isOr] <;> omega
lemma zjn {α : Type} (p : α → Bool) (xs : List α) :
  xs.countP p = Nat.card {i : Fin xs.length // p (xs.get i) = true} := by
 classical
 have yY : xs.countP p = ∑ i : Fin xs.length, if p (xs.get i) = true then 1 else 0 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
   simp only [List.get_eq_getElem] at ih ⊢
   change List.countP p (x :: xs) =
    ∑ i : Fin (xs.length + 1), if p ((x :: xs)[i.val]) = true then 1 else 0
   rw [Fin.sum_univ_succ, List.countP_cons]
   simp only [Fin.val_zero, List.getElem_cons_zero, Fin.val_succ, List.getElem_cons_succ, ← ih]
   by_cases h : p x = true <;> simp [h, Nat.add_comm]
 rw [yY, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
lemma zjo : ∀ r : Fin 11, r.val ∈ allowedInputs → wireIndex r.val < 8 := by
 decide +kernel
lemma zjp : ∀ r s : Fin 11,
  r.val ∈ allowedInputs → s.val ∈ allowedInputs → wireIndex r.val = wireIndex s.val → r = s := by
 decide +kernel
lemma zjq (r : Fin 11) (hr : r.val ∈ allowedInputs) (j : ℕ)
  (hj : j ∈ allowedInputs ∨ 11 ≤ j) : wireIndex j = wireIndex r.val ↔ j = r.val := by
 constructor
 ·intro heq
  by_cases zx : j < 11
  ·have uv : j ∈ allowedInputs := hj.resolve_right (by omega)
   exact congrArg Fin.val (zjp ⟨j, zx⟩ r uv hr heq)
  ·have hb := zjo r hr
   have zk : wireIndex j = j - 3 := by simp [wireIndex, zx]
   rw [zk] at heq
   omega
 ·intro h; rw [h]
lemma zjr {n : ℕ} (ops : Fin n → Bool) (a b : Fin n → ℕ)
  (r : Fin 11) (hr : r.val ∈ allowedInputs)
  (ha : ∀ i, a i ∈ allowedInputs ∨ 11 ≤ a i)
  (hb : ∀ i, b i ∈ allowedInputs ∨ 11 ≤ b i) :
  (convertedGates ops a b).countP (fun g => decide (wireIndex r.val ∈ g.inputs)) =
   Nat.card {i : Fin n // a i = r.val ∨ b i = r.val} := by
 rw [zjn]
 apply Nat.card_congr
 refine (finCongr (by simp [convertedGates])).subtypeEquiv ?_
 intro i
 have hi : i.val < n := by simpa [convertedGates] using i.isLt
 change decide (wireIndex r.val ∈ ((List.ofFn (convertedGate ops a b))[i.val]'_).inputs) = true ↔ _
 simp only [List.getElem_ofFn, decide_eq_true_eq, convertedGate, List.mem_cons, List.not_mem_nil, or_false]
 have h1 := zjq r hr (a ⟨i.val, hi⟩) (ha ⟨i.val, hi⟩)
 have h2 := zjq r hr (b ⟨i.val, hi⟩) (hb ⟨i.val, hi⟩)
 cases i
 simpa only [eq_comm, finCongr_apply_mk] using h1.or h2
lemma zjs {n : ℕ} (ops : Fin n → Bool) (a b : Fin n → ℕ)
  (r : Fin 11) (hr : r.val ∈ allowedInputs)
  (ha : ∀ i, a i ∈ allowedInputs ∨ 11 ≤ a i)
  (hb : ∀ i, b i ∈ allowedInputs ∨ 11 ≤ b i)
  (xn : Pin.zi6 Pin.isAnd (wireIndex r.val) (convertedGates ops a b) +
   Pin.zi6 Pin.isOr (wireIndex r.val) (convertedGates ops a b) ≤ 1) :
  Nat.card {i : Fin n // a i = r.val ∨ b i = r.val} ≤ 1 := by
 have h := zjm (wireIndex r.val) (convertedGates ops a b)
  (by
   intro g hg
   exact (zbX ops a b g hg).imp And.left id)
 rw [h, zjr ops a b r hr ha hb] at xn
 exact xn
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def zjt : Fin 8 → List (Fin 8) :=
 ![[1, 2, 3], [0, 4], [0, 5, 7], [0, 6], [1, 6, 7], [2, 7], [3, 4, 7], [2, 4, 5, 6]]
lemma zju : ∀ (v : Fin 8) (x : Fin 8 → Bool),
  targetFun x = (targetFun (Function.update x v false) || (x v && (zjt v).any x)) := by
 decide +kernel
lemma zjv : ∀ v : Fin 8,
  targetFun (Function.update (fun _ => true) v false) = true := by
 decide +kernel
lemma zjw (gs : List Gate) : ∀ w : List Bool,
  ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
 induction gs with
 | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
 | cons g gs ih =>
  intro w
  obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
  refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
  have : wiresFrom (g :: gs) w
    = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
  rw [this, ht]
  simp
lemma zjx (D : Circuit) (x : Fin 8 → Bool) :
  (D.wires (List.ofFn x)).length = 8 + D.gates.length := by
 obtain ⟨t, ht, hl⟩ := zjw D.gates (List.ofFn x)
 change (wiresFrom D.gates (List.ofFn x)).length = _
 rw [ht]
 simp only [List.length_append, List.length_ofFn, hl]
lemma zjy (D : Circuit) (x : Fin 8 → Bool) (i : Fin 8) :
  (D.wires (List.ofFn x)).getD i.val false = x i := by
 obtain ⟨t, ht, hl⟩ := zjw D.gates (List.ofFn x)
 change (wiresFrom D.gates (List.ofFn x)).getD i.val false = _
 rw [ht, List.getD_append _ _ _ _ (by simpa using i.isLt)]
 rw [List.getD_eq_getElem _ _ (by simpa using i.isLt)]
 simp only [List.getElem_ofFn]
def zjz (D : Circuit) (v : Fin 8) : Circuit :=
 {gates := D.gates ++
   [{op := GateOp.or, inputs := (zjt v).map Fin.val},
    {op := GateOp.and, inputs := [v.val, 8 + D.gates.length]},
    {op := GateOp.or, inputs := [D.output, 9 + D.gates.length]}]
  output := 10 + D.gates.length }
lemma zjA (D : Circuit) (v : Fin 8) (ql : D.output < 8 + D.gates.length)
  (x : Fin 8 → Bool) :
  (zjz D v).eval (List.ofFn x) = (D.eval (List.ofFn x) || (x v && (zjt v).any x)) := by
 let w := D.wires (List.ofFn x)
 have uT : w.length = 8 + D.gates.length := zjx D x
 have xx : ∀ i : Fin 8, w.getD i.val false = x i := zjy D x
 have q0 : ((zjt v).map Fin.val).map (fun i => w.getD i false) = (zjt v).map x := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro i _
  exact xx i
 have hv : v.val < w.length := by have := v.isLt; omega
 have ho : D.output < w.length := by omega
 have us : 8 + D.gates.length = w.length := uT.symm
 have ut : 9 + D.gates.length = w.length + 1 := by omega
 have uu : 10 + D.gates.length = w.length + 2 := by omega
 change (List.foldl (fun (acc : List Bool) (g : Gate) => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)])
  (List.ofFn x) (zjz D v).gates).getD (zjz D v).output false = _
 simp only [zjz, List.foldl_append, List.foldl_cons, List.foldl_nil]
 change (List.foldl (fun (acc : List Bool) (g : Gate) => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w
  [{op := GateOp.or, inputs := (zjt v).map Fin.val},
   {op := GateOp.and, inputs := [v.val, 8 + D.gates.length]},
   {op := GateOp.or, inputs := [D.output, 9 + D.gates.length]}]).getD
    (10 + D.gates.length) false = _
 simp only [List.foldl_cons, List.foldl_nil, q0, GateOp.eval, List.any_map, List.map_cons,
  List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true, List.any_cons, List.any_nil,
  Bool.or_false]
 rw [us, ut, uu]
 simp only [List.getD_append _ _ _ _ hv, List.getD_append _ _ _ _ ho,
  List.getD_append, List.length_append, List.length_singleton]
 simp [List.getD_append, List.getD_eq_getElem, hv, ho, xx, Circuit.eval, w, zjx]
 change ((w ++ [(zjt v).any x, w.getD v.val false && (zjt v).any x]).getD D.output false ||
  (w.getD v.val false && (zjt v).any x)) =
  (w.getD D.output false || (x v && (zjt v).any x))
 rw [List.getD_append _ _ _ _ ho, xx]
lemma zjB (D : Circuit) (v : Fin 8) (hm : Monotone2 D)
  (qL : ∀ x : Fin 8 → Bool, D.eval (List.ofFn x) = targetFun (Function.update x v false)) :
  4 ≤ Nat.card {j : Fin D.gates.length // (D.gates.get j).op = GateOp.and} := by
 have ql : D.output < 8 + D.gates.length := by
  by_contra h
  have he := qL (fun _ => true)
  rw [zjv] at he
  unfold Circuit.eval at he
  rw [List.getD_eq_default _ _ (by rw [zjx]; omega)] at he
  contradiction
 have zz : ∀ g ∈ (zjz D v).gates,
   (g.op = GateOp.and ∧ g.inputs.length ≤ 2) ∨ g.op = GateOp.or := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  ·obtain ⟨hop, qe⟩ := hm g hg
   simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
   exact hop.elim (fun h => Or.inl ⟨h, qe⟩) Or.inr
  ·simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
   rcases hg with rfl | rfl | rfl <;> simp
 have heq : circuitFun 8 (zjz D v) = targetFun := by
  funext x
  change (zjz D v).eval (List.ofFn x) = _
  rw [zjA D v ql x, qL, ← zju]
 have hge := zbN (zjz D v) zz heq
 rw [← zab] at hge
 have qS : ((zjz D v).gates.filter (fun g => isAnd g.op)).length =
   (D.gates.filter (fun g => isAnd g.op)).length + 1 := by
  simp [zjz, isAnd, List.filter_append]
 rw [qS, zab] at hge
 omega
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
lemma zjC (C : Circuit) (v : Fin 8)
  (hv : v = 1 ∨ v = 5 ∨ v = 3) (qr : Monotone2 C)
  (qL : ∀ x : Fin 8 → Bool,
   C.eval (List.ofFn x) = t1Graph (Function.update x v false)) :
  8 ≤ Pin.orCount C.gates := by
 rcases hv with rfl | rfl | rfl
 ·have zP : ∀ x : Fin 7 → Bool,
    (ziA ziK C).eval (List.ofFn x) = OrYF.g28_fn x :=
   ziN C qL
  have h8 := g28_or_ge_eight (ziA ziK C)
   (ziI ziK C qr) zP
  rwa [← ziY, ziZ] at h8
 ·have zP : ∀ x : Fin 7 → Bool,
    (ziA ziR C).eval (List.ofFn x) = OrYF.g29_fn x :=
   ziW C qL
  have h8 := ziw (ziA ziR C)
   (ziI ziR C qr) zP
  rwa [← ziY, ziZ] at h8
 ·have zP : ∀ x : Fin 7 → Bool,
    (ziA ziS C).eval (List.ofFn x) = OrYF.g28_fn x :=
   ziX C qL
  have h8 := g28_or_ge_eight (ziA ziS C)
   (ziI ziS C qr) zP
  rwa [← ziY, ziZ] at h8
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
lemma zjD (gs : List Gate) :
  Pin.opCount Pin.isAnd gs = Nat.card {j : Fin gs.length // (gs.get j).op = GateOp.and} := by
 rw [Pin.opCount, List.countP_eq_length_filter]
 change (gs.filter (fun g => isAnd g.op)).length = _
 exact zab gs
lemma zjE (C : Circuit) (qr : Monotone2 C)
  (qL : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = targetFun x)
  (xf : Nat.card {j : Fin C.gates.length // (C.gates.get j).op = GateOp.and} = 5)
  (hor : Pin.orCount C.gates = 9)
  (v : Fin 8) (hv : v = 1 ∨ v = 5 ∨ v = 3) :
  Pin.zi6 Pin.isAnd v.val C.gates + Pin.zi6 Pin.isOr v.val C.gates ≤ 1 := by
 have qZ : targetFun = t1Graph := by
  funext x
  simp [targetFun, edgesT1, t1Graph, Bool.or_assoc]
 have qE : ∃ x : Fin 8 → Bool,
   C.eval (List.ofFn (Function.update x v false)) = true := by
  refine ⟨fun _ => true, ?_⟩
  rw [qL, zjv]
 have q5 : ∃ x : Fin 8 → Bool,
   C.eval (List.ofFn (Function.update x v false)) = false := by
  refine ⟨fun _ => false, ?_⟩
  rw [qL]
  have hz : Function.update (fun _ : Fin 8 => false) v false = fun _ => false := by
   funext i
   by_cases hi : i = v <;> simp [hi]
  rw [hz]
  decide
 have qz : ∀ D : Circuit, Monotone2 D →
   (∀ x : Fin 8 → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) →
   Pin.opCount Pin.isAnd C.gates ≤ Pin.opCount Pin.isAnd D.gates := by
  intro D hm he
  have zz : ∀ g ∈ D.gates,
    (g.op = GateOp.and ∧ g.inputs.length ≤ 2) ∨ g.op = GateOp.or := by
   intro g hg
   obtain ⟨hop, qe⟩ := hm g hg
   simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
   exact hop.elim (fun h => Or.inl ⟨h, qe⟩) Or.inr
  have hf : circuitFun 8 D = targetFun := by
   funext x
   exact (he x).trans (qL x)
  have h5 := zbN D zz hf
  rw [zjD, zjD, xf]
  exact h5
 have ye : ∀ D : Circuit, Monotone2 D →
   (∀ x : Fin 8 → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn (Function.update x v false))) →
   Pin.opCount Pin.isAnd C.gates ≤ Pin.opCount Pin.isAnd D.gates + 1 := by
  intro D hm he
  have hf : ∀ x : Fin 8 → Bool,
    D.eval (List.ofFn x) = targetFun (Function.update x v false) := by
   intro x
   rw [he, qL]
  have h4 := zjB D v hm hf
  rw [zjD, zjD, xf]
  omega
 have ve : ∀ D : Circuit, Monotone2 D →
   (∀ x : Fin 8 → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn (Function.update x v false))) →
   8 ≤ Pin.orCount D.gates := by
  intro D hm he
  apply zjC D v hv hm
  intro x
  rw [he, qL, qZ]
 have hr := Pin.zjl 8 C v 8 qr qE q5 qz ye ve
 rw [hor] at hr
 omega
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
lemma witness_reader_cap
  (ops : Fin 14 → Bool) (a b : Fin 14 → Fin 33) (zm : Nat → Nat)
  (qi : ∀ i : Fin 11, zm i.val = baseValues.getD i.val 0)
  (ha : ∀ i, (a i).val ∈ allowedInputs ∨ 11 ≤ (a i).val)
  (hb : ∀ i, (b i).val ∈ allowedInputs ∨ 11 ≤ (b i).val)
  (hs : ∀ i, (a i).val < 11 + i.val ∧ (b i).val < 11 + i.val ∧
   zm (11 + i.val) = if ops i then zm (a i).val &&& zm (b i).val
    else zm (a i).val ||| zm (b i).val)
  (ql : zm 24 = 36671) (r : Fin 3) :
  Nat.card {i : Fin 14 // (a i).val = r.val ∨ (b i).val = r.val} ≤ 1 := by
 let D : Circuit :=
  {gates := convertedGates ops (fun i => (a i).val) (fun i => (b i).val), output := 21 }
 have qp := zbX ops (fun i => (a i).val) (fun i => (b i).val)
 have hmD : Monotone2 D := by
  intro g hg
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
  cases h : ops i <;> simp [convertedGate, h]
 have qJ : ∀ k : Fin 40, circuitFun 8 D (sample k) = (36671 : Nat).testBit k.val := by
  intro k
  change (wiresFrom (convertedGates ops (fun i => (a i).val) (fun i => (b i).val))
   (List.ofFn (sample k))).getD 21 false = _
  rw [zbZ ops (fun i => (a i).val) (fun i => (b i).val) zm qi ha hb hs k]
  have qI := zbW (n := 14) zm k 24 qi (by decide) (Or.inr (by decide))
  have zk : wireIndex 24 = 21 := by decide
  rw [zk, ql] at qI
  exact qI
 have zB := zbP (circuitFun 8 D) (zbS D qp) qJ
 have qL : ∀ x : Fin 8 → Bool, D.eval (List.ofFn x) = targetFun x := fun x => congrFun zB x
 obtain ⟨ha5, ho9⟩ := witness_exact_gate_counts ops a b zm qi ha hb hs ql
 have xf : Nat.card {j : Fin D.gates.length // (D.gates.get j).op = GateOp.and} = 5 := by
  change Nat.card {j : Fin (convertedGates ops (fun i => (a i).val) (fun i => (b i).val)).length //
   ((convertedGates ops (fun i => (a i).val) (fun i => (b i).val)).get j).op = GateOp.and} = 5
  rw [zb0]
  exact ha5
 have hor : Pin.orCount D.gates = 9 := by
  change Pin.orCount (convertedGates ops (fun i => (a i).val) (fun i => (b i).val)) = 9
  rw [zi4]
  exact ho9
 let raw : Fin 11 := ⟨r.val, by omega⟩
 have hr : raw.val ∈ allowedInputs := by
  fin_cases r <;> simp [raw, allowedInputs]
 let w : Fin 8 := ⟨wireIndex raw.val, zjo raw hr⟩
 have hw : w = 1 ∨ w = 5 ∨ w = 3 := by
  fin_cases r <;> simp [w, raw, wireIndex, Fin.ext_iff]
 have xn := zjE D hmD qL xf hor w hw
 exact zjs ops (fun i => (a i).val) (fun i => (b i).val) raw hr ha hb xn
namespace Pin
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def readerSetCount (p : GateOp → Bool) (K : Finset ℕ) (gs : List Gate) : ℕ :=
 gs.countP (fun g => p g.op && decide (∃ k ∈ K, k ∈ g.inputs))
lemma zjF (p : GateOp → Bool) (K : Finset ℕ) (g : Gate) (gs : List Gate) :
  readerSetCount p K (g :: gs) =
   (if p g.op && decide (∃ k ∈ K, k ∈ g.inputs) then 1 else 0) + readerSetCount p K gs := by
 simp [readerSetCount, List.countP_cons, Nat.add_comm]
theorem zjG (p : GateOp → Bool) (n : ℕ) (K : Finset ℕ) (gs : List Gate) :
  ∀ acc : List Stat × List Gate, (∀ g ∈ gs, Ok g) →
   (∀ k ∈ K, k < acc.1.length ∧ ∃ b, acc.1.getD k (Sum.inl false) = Sum.inl b) →
   opCount p (elim n gs acc).2 + readerSetCount p K gs ≤ opCount p acc.2 + opCount p gs := by
 induction gs with
 | nil => intro acc _ _; simp [elim, opCount, readerSetCount]
 | cons g gs ih =>
  intro acc hok xw
  have vS : ∀ k ∈ K, k < (zb9 n acc g).1.length ∧
    ∃ b, (zb9 n acc g).1.getD k (Sum.inl false) = Sum.inl b := by
   intro k hk
   obtain ⟨wz, b, hb⟩ := xw k hk
   refine ⟨by simp only [zb9, List.length_append, List.length_singleton]; omega, b, ?_⟩
   simp only [zb9]
   rw [zb4 _ _ _ _ (by omega)]
   exact hb
  have h1 := ih (zb9 n acc g)
   (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) vS
  have qQ : opCount p (zb9 n acc g).2 = opCount p acc.2 +
    opCount p (zb5 g.op (n + acc.2.length)
     (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList := by
   simp only [zb9, zi8]
  rw [qQ] at h1
  change opCount p (elim n gs (zb9 n acc g)).2 + readerSetCount p K (g :: gs) ≤ _
  rw [zi9, zjF]
  by_cases hkg : ∃ k ∈ K, k ∈ g.inputs
  ·obtain ⟨k, hk, zb⟩ := hkg
   obtain ⟨_, b, hb⟩ := xw k hk
   have zC : (zb5 g.op (n + acc.2.length)
     (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
    apply zb7
    ·exact (hok g List.mem_cons_self).1
    ·simpa using (hok g List.mem_cons_self).2
    ·exact ⟨b, List.mem_map.2 ⟨k, zb, hb⟩⟩
   rw [zC] at h1
   simp only [Option.toList_none, show opCount p [] = 0 from rfl, Nat.add_zero] at h1
   have hex : ∃ k ∈ K, k ∈ g.inputs := ⟨k, hk, zb⟩
   simp only [hex, decide_true, Bool.and_true]
   omega
  ·have xy := zi7 p g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
   simp only [hkg, decide_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
   omega
def zjH (n : ℕ) (K : Finset ℕ) : List Stat :=
 List.ofFn (fun i : Fin n => if i.val ∈ K then Sum.inl false else Sum.inr i.val)
def pinSetInput {n : ℕ} (K : Finset ℕ) (x : Fin n → Bool) (i : Fin n) : Bool :=
 if i.val ∈ K then false else x i
lemma zjI (n : ℕ) (K : Finset ℕ) (x : Fin n → Bool) :
  Inv n (List.ofFn x) (List.ofFn (pinSetInput K x)) (zjH n K, []) := by
 refine ⟨by simp [zjH], ?_⟩
 intro i
 by_cases hi : i < n
 ·by_cases hk : i ∈ K
  ·simp [zjH, pinSetInput, hi, hk, Stat.Valid, Stat.val]
  ·simp [zjH, pinSetInput, hi, hk, Stat.Valid, Stat.val, wiresFrom]
 ·rw [List.getD_eq_default _ _ (by simp [zjH]; omega),
   List.getD_eq_default _ _ (by simp; omega)]
  exact ⟨trivial, rfl⟩
theorem pinSetCircuit (p : GateOp → Bool) (n : ℕ) (K : Finset ℕ)
  (hK : ∀ k ∈ K, k < n) (C : Circuit) (qr : Monotone2 C)
  (q5 : ∃ x : Fin n → Bool, C.eval (List.ofFn (pinSetInput K x)) = false) :
  ∃ D : Circuit, Monotone2 D ∧
   opCount p D.gates + readerSetCount p K C.gates ≤ opCount p C.gates ∧
   ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn (pinSetInput K x)) := by
 have hok : ∀ g ∈ C.gates, Ok g := by
  intro g hg
  obtain ⟨h1, h2⟩ := qr g hg
  exact ⟨by simpa using h1, h2⟩
 set acc := elim n C.gates (zjH n K, []) with q4
 have zl : ∀ y : Fin n → Bool,
   (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn y)) =
    C.eval (List.ofFn (pinSetInput K y)) := by
  intro y
  exact ((zcb n (List.ofFn y) (by simp) C.gates _ _ hok
   (zjI n K y)).2 C.output).2
 have vR : opCount p acc.2 + readerSetCount p K C.gates ≤ opCount p C.gates := by
  have xw : ∀ k ∈ K, k < (zjH n K).length ∧
    ∃ b, (zjH n K).getD k (Sum.inl false) = Sum.inl b := by
   intro k hk
   have hkn := hK k hk
   refine ⟨by simpa [zjH] using hkn, false, ?_⟩
   simp [zjH, hkn, hk]
  simpa only [← q4, show opCount p [] = 0 from rfl, Nat.zero_add] using
   zjG p n K C.gates (zjH n K, []) hok xw
 have hmD : ∀ out : ℕ, Monotone2 ⟨acc.2, out⟩ := by
  intro out g hg
  obtain ⟨h1, h2⟩ := elim_ok n C.gates _ (by simp) g hg
  exact ⟨by simpa using h1, h2⟩
 cases hst : acc.1.getD C.output (Sum.inl false) with
 | inl c =>
  cases c with
  | true =>
   exfalso
   obtain ⟨y, hy⟩ := q5
   have hv := zl y
   rw [hst] at hv
   exact Bool.false_ne_true (hv.trans hy).symm
  | false =>
   refine ⟨⟨acc.2, n + acc.2.length⟩, hmD _, vR, ?_⟩
   intro x
   rw [← zl x, hst]
   show (wiresFrom acc.2 (List.ofFn x)).getD (n + acc.2.length) false = false
   rw [List.getD_eq_default _ _ (by rw [zb3]; simp)]
 | inr j =>
  refine ⟨⟨acc.2, j⟩, hmD _, vR, ?_⟩
  intro x
  have hv := zl x
  rw [hst] at hv
  exact hv
end Pin
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit
private def zjJ : List (Fin 8 × Fin 8) :=
 [(0, 2), (2, 7), (4, 6), (4, 7), (6, 7)]
private def zjK (u v : Fin 8) : Bool :=
 decide ((u, v) ∈ zjJ ∨ (v, u) ∈ zjJ)
private def zjL : Fin 5 → Finset (Fin 8) :=
 ![{2, 6}, {2, 4}, {6, 0}, {7, 0}, {4, 0}]
lemma coreT1_and_count_ge_three (D : Circuit)
  (qp : ∀ g ∈ D.gates, (g.op = GateOp.and ∧ g.inputs.length ≤ 2) ∨ g.op = GateOp.or)
  (qL : circuitFun 8 D = (fun x : Fin 8 → Bool => zjJ.any (fun p => x p.1 && x p.2))) :
  3 ≤ Nat.card {j : Fin D.gates.length // (D.gates.get j).op = GateOp.and} := by
 by_contra qS
 have w1 : Nat.card {j : Fin D.gates.length // (D.gates.get j).op = GateOp.and} ≤ 2 := by omega
 obtain ⟨C, _, hCsz, xa⟩ := zaH 2 D zjK zjJ (fun _ _ => rfl) qp w1 qL
 have tt : ∀ a : Fin 5, ¬ ∃ u ∈ zjL a, ∃ v ∈ zjL a, zjK u v = true := by decide
 have wC : ∀ a b : Fin 5, a ≠ b → ∃ u ∈ zjL a ∪ zjL b,
   ∃ v ∈ zjL a ∪ zjL b, zjK u v = true := by decide
 have hz : ∀ a : Fin 5, C.eval (zjL a) = false := by
  intro a
  apply Bool.eq_false_iff.mpr
  intro ht
  exact tt a ((xa _).mp ht)
 have ho : ∀ a b : Fin 5, a ≠ b → C.eval (zjL a ∪ zjL b) = true := by
  intro a b hab
  exact (xa _).mpr (wC a b hab)
 have hc := zba C ∅ 5 zjL (fun _ => Finset.empty_subset _) hz ho
 simp only [Finset.disjoint_empty_right, Finset.filter_true,
  Finset.card_univ, Fintype.card_fin] at hc
 have hp : 2 ^ C.size ≤ 4 := by
  have hp := Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hCsz
  norm_num at hp ⊢
  exact hp
 omega
lemma zjM (gs : List Gate) :
  Pin.opCount Pin.isAnd gs = Nat.card {j : Fin gs.length // (gs.get j).op = GateOp.and} := by
 rw [Pin.opCount, List.countP_eq_length_filter]
 change (gs.filter (fun g => isAnd g.op)).length = _
 exact zab gs
lemma t1_abc_and_reader_count_le_two (C : Circuit) (qr : Monotone2 C)
  (qL : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = targetFun x)
  (xf : Nat.card {j : Fin C.gates.length // (C.gates.get j).op = GateOp.and} = 5) :
  Pin.readerSetCount Pin.isAnd {1, 3, 5} C.gates ≤ 2 := by
 have q5 : ∃ x : Fin 8 → Bool,
   C.eval (List.ofFn (Pin.pinSetInput {1, 3, 5} x)) = false := by
  refine ⟨fun _ => false, ?_⟩
  rw [qL]
  decide +kernel
 obtain ⟨D, hmD, vR, qH⟩ := Pin.pinSetCircuit Pin.isAnd 8 {1, 3, 5}
  (by decide) C qr q5
 have zz : ∀ g ∈ D.gates,
   (g.op = GateOp.and ∧ g.inputs.length ≤ 2) ∨ g.op = GateOp.or := by
  intro g hg
  obtain ⟨hop, qe⟩ := hmD g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  exact hop.elim (fun h => Or.inl ⟨h, qe⟩) Or.inr
 have ty : ∀ x : Fin 8 → Bool, targetFun (Pin.pinSetInput {1, 3, 5} x) =
   zjJ.any (fun p => x p.1 && x p.2) := by
  decide +kernel
 have ul : circuitFun 8 D =
   (fun x : Fin 8 → Bool => zjJ.any (fun p => x p.1 && x p.2)) := by
  funext x
  exact (qH x).trans ((qL _).trans (ty x))
 have h3 := coreT1_and_count_ge_three D zz ul
 rw [zjM, zjM, xf] at vR
 omega
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
lemma converted_abc_and_reader_count (ops : Fin 14 → Bool) (a b : Fin 14 → Fin 33) :
  Pin.readerSetCount Pin.isAnd {1, 3, 5}
   (convertedGates ops (fun i => (a i).val) (fun i => (b i).val)) =
  Nat.card {i : Fin 14 // ops i = true ∧ ((a i).val < 3 ∨ (b i).val < 3)} := by
 rw [Pin.readerSetCount, zjn]
 apply Nat.card_congr
 refine (finCongr (by simp [convertedGates])).subtypeEquiv ?_
 intro i
 have hi : i.val < 14 := by simpa [convertedGates] using i.isLt
 change (Pin.isAnd ((List.ofFn (convertedGate ops (fun i => (a i).val)
  (fun i => (b i).val)))[i.val]'_).op &&
  decide (∃ k ∈ ({1, 3, 5} : Finset Nat), k ∈ ((List.ofFn (convertedGate ops
   (fun i => (a i).val) (fun i => (b i).val)))[i.val]'_).inputs)) = true ↔ _
 simp only [List.getElem_ofFn, convertedGate]
 have vW : ∀ (op : Bool) (a b : Fin 33),
   (Pin.isAnd (if op then GateOp.and else GateOp.or) &&
    decide (∃ k ∈ ({1, 3, 5} : Finset Nat), k ∈ [wireIndex a.val, wireIndex b.val])) = true ↔
   op = true ∧ (a.val < 3 ∨ b.val < 3) := by decide +kernel
 cases i
 simpa only [finCongr_apply_mk] using vW (ops ⟨_,hi⟩) (a ⟨_,hi⟩) (b ⟨_,hi⟩)
lemma witness_abc_and_reader_count_le_two
  (ops : Fin 14 → Bool) (a b : Fin 14 → Fin 33) (v : Nat → Nat)
  (qi : ∀ i : Fin 11, v i.val = baseValues.getD i.val 0)
  (ha : ∀ i, (a i).val ∈ allowedInputs ∨ 11 ≤ (a i).val)
  (hb : ∀ i, (b i).val ∈ allowedInputs ∨ 11 ≤ (b i).val)
  (hs : ∀ i, (a i).val < 11 + i.val ∧ (b i).val < 11 + i.val ∧
   v (11 + i.val) = if ops i then v (a i).val &&& v (b i).val else v (a i).val ||| v (b i).val)
  (ql : v 24 = 36671)
  (xf : Nat.card {i : Fin 14 // ops i = true} = 5) :
  Nat.card {i : Fin 14 // ops i = true ∧ ((a i).val < 3 ∨ (b i).val < 3)} ≤ 2 := by
 let D : Circuit := { gates := convertedGates ops (fun i => (a i).val) (fun i => (b i).val), output := 21 }
 have qp := zbX ops (fun i => (a i).val) (fun i => (b i).val)
 have hm : Monotone2 D := by
  intro g hg
  rcases qp g hg with ⟨hop,qe⟩ | hop
  ·exact ⟨by simp [hop],qe⟩
  ·refine ⟨by simp [hop],?_⟩
   obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hg
   simp [convertedGate]
 have qJ : ∀ k : Fin 40, circuitFun 8 D (sample k) = (36671 : Nat).testBit k.val := by
  intro k
  change (wiresFrom (convertedGates ops (fun i => (a i).val) (fun i => (b i).val))
   (List.ofFn (sample k))).getD 21 false = _
  rw [zbZ ops (fun i => (a i).val) (fun i => (b i).val) v qi ha hb hs k]
  have qI := zbW (n := 14) v k 24 qi (by decide) (Or.inr (by decide))
  have zk : wireIndex 24 = 21 := by decide
  rw [zk, ql] at qI
  exact qI
 have hf : ∀ x : Fin 8 → Bool, D.eval (List.ofFn x) = targetFun x := by
  have h := zbP (circuitFun 8 D) (zbS D qp) qJ
  intro x
  exact congrFun h x
 have hd : Nat.card {j : Fin D.gates.length // (D.gates.get j).op = GateOp.and} = 5 := by
  change Nat.card {j : Fin (convertedGates ops (fun i => (a i).val) (fun i => (b i).val)).length //
   ((convertedGates ops (fun i => (a i).val) (fun i => (b i).val)).get j).op = GateOp.and} = 5
  rwa [zb0]
 have hc := t1_abc_and_reader_count_le_two D hm hf hd
 change Pin.readerSetCount Pin.isAnd {1,3,5}
  (convertedGates ops (fun i => (a i).val) (fun i => (b i).val)) ≤ 2 at hc
 rwa [converted_abc_and_reader_count] at hc
namespace UniqueReader
def zjN (op x y : Bool) : Bool := if op then x && y else x || y
lemma zjO
  {n k v : Nat} (p : Fin k) (a b : Fin k → Nat) (op : Fin k → Bool)
  (w₀ w₁ : Nat → Bool)
  (ha : ∀ j, a j < n + j.val) (hb : ∀ j, b j < n + j.val)
  (qX : ∀ i, i < n → i ≠ v → w₀ i = w₁ i)
  (qV : ∀ j, j ≠ p → a j ≠ v ∧ b j ≠ v)
  (qH₀ : ∀ j, w₀ (n + j.val) = zjN (op j) (w₀ (a j)) (w₀ (b j)))
  (qH₁ : ∀ j, w₁ (n + j.val) = zjN (op j) (w₁ (a j)) (w₁ (b j))) :
  ∀ i, i < n + k → i ≠ v →
   (n + p.val ≤ i → w₀ (n + p.val) = w₁ (n + p.val)) → w₀ i = w₁ i := by
 intro i
 induction i using Nat.strong_induction_on with
 | ind i ih =>
  intro hi hiv hp
  by_cases hin : i < n
  ·exact qX i hin hiv
  ·let j : Fin k := ⟨i - n, by omega⟩
   have hij : i = n + j.val := by dsimp [j]; omega
   by_cases hjp : j = p
   ·have hip : i = n + p.val := hij.trans (congrArg (fun q : Fin k => n + q.val) hjp)
    rw [hip]
    exact hp (by omega)
   ·obtain ⟨hav, hbv⟩ := qV j hjp
    have hea : w₀ (a j) = w₁ (a j) :=
     ih (a j) (by simpa [← hij] using ha j) (by have := ha j; omega) hav
      (fun h => hp (by have := ha j; omega))
    have heb : w₀ (b j) = w₁ (b j) :=
     ih (b j) (by simpa [← hij] using hb j) (by have := hb j; omega) hbv
      (fun h => hp (by have := hb j; omega))
    rw [hij, qH₀, qH₁, hea, heb]
lemma zjP
  {n k v out : Nat} (p : Fin k) (a b : Fin k → Nat) (op : Fin k → Bool)
  (w₀ w₁ : Nat → Bool)
  (ha : ∀ j, a j < n + j.val) (hb : ∀ j, b j < n + j.val)
  (qX : ∀ i, i < n → i ≠ v → w₀ i = w₁ i)
  (qV : ∀ j, j ≠ p → a j ≠ v ∧ b j ≠ v)
  (qH₀ : ∀ j, w₀ (n + j.val) = zjN (op j) (w₀ (a j)) (w₀ (b j)))
  (qH₁ : ∀ j, w₁ (n + j.val) = zjN (op j) (w₁ (a j)) (w₁ (b j)))
  (zd : a p = v) (qM : b p ≠ v)
  (hv₀ : w₀ v = false) (hv₁ : w₁ v = true)
  (ql : out < n + k) (vu : out ≠ v) (ur : w₀ out ≠ w₁ out) :
  w₀ (b p) = op p := by
 have hu : w₀ (b p) = w₁ (b p) :=
  zjO p a b op w₀ w₁ ha hb qX qV qH₀ qH₁
   (b p) (by have := hb p; have := p.isLt; omega) qM
   (fun h => by have := hb p; omega)
 have hg : w₀ (n + p.val) ≠ w₁ (n + p.val) := by
  intro heq
  exact ur (zjO p a b op w₀ w₁ ha hb qX qV qH₀ qH₁
   out ql vu (fun _ => heq))
 rw [qH₀, qH₁, zd, hv₀, hv₁, ← hu] at hg
 cases hop : op p <;> cases huval : w₀ (b p) <;> simp_all [zjN]
lemma zjQ
  {n k v out : Nat} (p : Fin k) (a b : Fin k → Nat) (op : Fin k → Bool)
  (w₀ w₁ : Nat → Bool)
  (ha : ∀ j, a j < n + j.val) (hb : ∀ j, b j < n + j.val)
  (qX : ∀ i, i < n → i ≠ v → w₀ i = w₁ i)
  (qV : ∀ j, j ≠ p → a j ≠ v ∧ b j ≠ v)
  (qH₀ : ∀ j, w₀ (n + j.val) = zjN (op j) (w₀ (a j)) (w₀ (b j)))
  (qH₁ : ∀ j, w₁ (n + j.val) = zjN (op j) (w₁ (a j)) (w₁ (b j)))
  (zd : a p = v) (qM : b p ≠ v)
  (ql : out < n + k) (vu : out ≠ v) (uN : w₀ (b p) ≠ op p) :
  w₀ out = w₁ out := by
 have hu : w₀ (b p) = w₁ (b p) :=
  zjO p a b op w₀ w₁ ha hb qX qV qH₀ qH₁
   (b p) (by have := hb p; have := p.isLt; omega) qM
   (fun h => by have := hb p; omega)
 apply zjO p a b op w₀ w₁ ha hb qX qV qH₀ qH₁ out ql vu
 intro _
 rw [qH₀, qH₁, zd, ← hu]
 cases hop : op p <;> cases huval : w₀ (b p) <;> simp_all [zjN]
end UniqueReader
namespace RawGraph
def zjR : List (Nat × Nat) :=
 [(0, 6), (0, 7), (1, 3), (1, 5), (2, 4), (2, 7),
  (3, 5), (3, 7), (4, 5), (4, 6), (5, 6)]
def graph (s : Fin 256) : Bool :=
 zjR.any (fun e => s.val.testBit e.1 && s.val.testBit e.2)
def single (v : Fin 8) : Fin 256 :=
 ([1, 2, 4, 8, 16, 32, 64, 128] : List (Fin 256)).getD v.val 0
def addBit (s : Fin 256) (v : Fin 8) : Fin 256 :=
 ⟨(s.val ||| 2 ^ v.val) % 256, Nat.mod_lt _ (by decide)⟩
def zjS (s t : Fin 256) : Prop :=
 ∀ i : Fin 8, s.val.testBit i.val = true → t.val.testBit i.val = true
def zjT (u : Fin 256 → Bool) : Prop :=
 ∀ s t, zjS s t → u s = true → u t = true
def witness (v y : Fin 8) : Fin 256 :=
 (([
  [0, 66, 68, 72, 144, 160, 64, 128],
  [9, 0, 12, 8, 24, 32, 72, 160],
  [17, 18, 0, 24, 16, 160, 192, 128],
  [3, 2, 6, 0, 18, 32, 66, 128],
  [5, 6, 4, 12, 0, 32, 64, 160],
  [3, 2, 6, 8, 16, 0, 64, 130],
  [1, 3, 5, 9, 16, 32, 0, 144],
  [1, 3, 4, 8, 17, 33, 68, 0]] : List (List (Fin 256))).getD v.val []).getD y.val 0
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma zjU : ∀ v y : Fin 8, v ≠ y →
  (witness v y).val.testBit y.val = true ∧
  (witness v y).val.testBit v.val = false ∧
  zjS (single y) (witness v y) ∧
  graph (witness v y) = false ∧ graph (addBit (witness v y) v) = true := by
 unfold zjS
 decide +kernel
lemma zjV (v y : Fin 8) (h : v ≠ y) :
  ∃ s : Fin 256, s.val.testBit y.val = true ∧ s.val.testBit v.val = false ∧
   zjS (single y) s ∧ graph s = false ∧ graph (addBit s v) = true := by
 exact ⟨witness v y, zjU v y h⟩
lemma zjW (u : Fin 256 → Bool) (v y : Fin 8)
  (hne : v ≠ y) (qr : zjT u)
  (xE : ∀ s, u s = true → graph s = graph (addBit s v)) :
  u (single y) = false := by
 obtain ⟨s, _, _, qu, q5, qE⟩ := zjV v y hne
 cases hu : u (single y) with
 | false => rfl
 | true =>
   have hs : u s = true := qr (single y) s qu hu
   have heq : graph s = graph (addBit s v) := xE s hs
   have bad : (false : Bool) = true := q5.symm.trans (heq.trans qE)
   cases bad
lemma zjX : ∀ v : Fin 8, addBit (0 : Fin 256) v = single v := by
 decide +kernel
lemma zjY (u : Fin 256 → Bool) (v : Fin 8)
  (xu : u 0 = false) (zr : ∀ s, u (addBit s v) = u s) :
  u (single v) = false := by
 rw [← zjX v, zr, xu]
lemma zjZ (u : Fin 256 → Bool) (v : Fin 8)
  (qr : zjT u)
  (xE : ∀ s, u s = true → graph s = graph (addBit s v))
  (xu : u 0 = false) (zr : ∀ s, u (addBit s v) = u s) :
  ∀ y : Fin 8, u (single y) = false := by
 intro y
 by_cases h : v = y
 ·subst y
  exact zjY u v xu zr
 ·exact zjW u v y h qr xE
end RawGraph
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
lemma zj0 (gs : List Gate) (w : List Bool) (j : Nat) (hj : j < w.length) :
  (wiresFrom gs w).getD j false = w.getD j false := by
 obtain ⟨t, ht, _⟩ := zjw gs w
 rw [ht, List.getD_append _ _ _ _ hj]
lemma zj1 (gs : List Gate) (w : List Bool)
  (hc : ∀ i : Fin gs.length, ∀ j ∈ (gs.get i).inputs, j < w.length + i.val) :
  ∀ i : Fin gs.length, (wiresFrom gs w).getD (w.length + i.val) false =
   (gs.get i).op.eval ((gs.get i).inputs.map fun j => (wiresFrom gs w).getD j false) := by
 induction gs generalizing w with
 | nil => intro i; exact Fin.elim0 i
 | cons g gs ih =>
  intro i
  let t := g.op.eval (g.inputs.map fun j => w.getD j false)
  let w' := w ++ [t]
  have he : wiresFrom (g :: gs) w = wiresFrom gs w' := rfl
  have hl : w'.length = w.length + 1 := by simp [w']
  refine Fin.cases ?_ (fun j => ?_) i
  ·simp only [Fin.val_zero, Nat.add_zero, List.get_eq_getElem, List.getElem_cons_zero]
   rw [he, zj0 gs w' w.length (by rw [hl]; omega)]
   have q0 : g.inputs.map (fun j => (wiresFrom gs w').getD j false) =
     g.inputs.map (fun j => w.getD j false) := by
    apply List.map_congr_left
    intro j hj
    have hb := hc 0 j hj
    simp only [Fin.val_zero, Nat.add_zero] at hb
    rw [zj0 gs w' j (by rw [hl]; omega), List.getD_append _ _ _ _ hb]
   rw [q0]
   simp [w', t]
  ·have zf : ∀ i : Fin gs.length, ∀ j ∈ (gs.get i).inputs, j < w'.length + i.val := by
    intro i j hj
    have h := hc i.succ j hj
    simpa only [Fin.val_succ, hl, Nat.add_assoc, Nat.add_comm 1] using h
   have h := ih w' zf j
   simpa only [Fin.val_succ, List.get_eq_getElem, List.getElem_cons_succ, he, hl, Nat.add_assoc, Nat.add_comm 1] using h
lemma zj2 {j i : Nat} (ha : j ∈ allowedInputs ∨ 11 ≤ j) (hj : j < 11 + i) :
  wireIndex j < 8 + i := by
 by_cases h : j < 11
 ·have hm := ha.resolve_right (by omega)
  have hb := (zbU ⟨j,h⟩ 0 hm).1
  change wireIndex j < 8 at hb
  omega
 ·simp only [wireIndex, if_neg h]
  omega
lemma zj3 {n : Nat} (ops : Fin n → Bool) (a b : Fin n → Nat)
  (ha : ∀ i, a i ∈ allowedInputs ∨ 11 ≤ a i)
  (hb : ∀ i, b i ∈ allowedInputs ∨ 11 ≤ b i)
  (hc : ∀ i, a i < 11 + i.val ∧ b i < 11 + i.val) :
  ∀ i : Fin (convertedGates ops a b).length,
   ∀ j ∈ ((convertedGates ops a b).get i).inputs, j < 8 + i.val := by
 intro i j hj
 have hi : i.val < n := by simpa [convertedGates] using i.isLt
 change j ∈ ((List.ofFn (convertedGate ops a b))[i.val]' (by simpa [convertedGates] using i.isLt)).inputs at hj
 simp only [List.getElem_ofFn, convertedGate, List.mem_cons, List.not_mem_nil, or_false] at hj
 rcases hj with rfl | rfl
 ·exact zj2 (ha ⟨i.val, hi⟩) (hc ⟨i.val, hi⟩).1
 ·exact zj2 (hb ⟨i.val, hi⟩) (hc ⟨i.val, hi⟩).2
def rawIndex (j : Nat) : Nat :=
 ([0,1,2,0,3,4,0,0,5,6,7] : List Nat).getD j 0
def zj4 (s : Fin 256) (t : Fin 8) : Bool :=
 s.val.testBit ((![7,0,3,2,6,1,4,5] : Fin 8 → Nat) t)
def semanticWire {n : Nat} (ops : Fin n → Bool) (a b : Fin n → Nat)
  (s : Fin 256) (j : Nat) : Bool :=
 if j < 11 then if j ∈ allowedInputs then s.val.testBit (rawIndex j) else false
 else (wiresFrom (convertedGates ops a b) (List.ofFn (zj4 s))).getD (wireIndex j) false
lemma zj5 {n : Nat} (ops : Fin n → Bool) (a b : Fin n → Nat)
  (s : Fin 256) (j : Nat) (hj : j ∈ allowedInputs ∨ 11 ≤ j) :
  semanticWire ops a b s j =
   (wiresFrom (convertedGates ops a b) (List.ofFn (zj4 s))).getD (wireIndex j) false := by
 by_cases h : j < 11
 ·have hm : j ∈ allowedInputs := hj.resolve_right (by omega)
  have he : ∀ (j : Fin 11) (s : Fin 256), j.val ∈ allowedInputs →
    (List.ofFn (zj4 s)).getD (wireIndex j.val) false = s.val.testBit (rawIndex j.val) := by
   decide +kernel
  have hb := (zbU ⟨j,h⟩ 0 hm).1
  rw [zj0 _ _ _ (by simpa using hb), he ⟨j,h⟩ s hm]
  simp [semanticWire, h, hm]
 ·simp only [semanticWire, if_neg h]
lemma semanticWire_eval {n : Nat} (ops : Fin n → Bool) (a b : Fin n → Nat)
  (ha : ∀ i, a i ∈ allowedInputs ∨ 11 ≤ a i)
  (hb : ∀ i, b i ∈ allowedInputs ∨ 11 ≤ b i)
  (hc : ∀ i, a i < 11 + i.val ∧ b i < 11 + i.val) (s : Fin 256) (i : Fin n) :
  semanticWire ops a b s (11 + i.val) =
   UniqueReader.zjN (ops i) (semanticWire ops a b s (a i)) (semanticWire ops a b s (b i)) := by
 rw [zj5 ops a b s _ (Or.inr (by omega)),
  zj5 ops a b s _ (ha i), zj5 ops a b s _ (hb i)]
 have hi : i.val < (convertedGates ops a b).length := by simpa [convertedGates] using i.isLt
 have h := zj1 (convertedGates ops a b) (List.ofFn (zj4 s))
  (by simpa using zj3 ops a b ha hb hc) ⟨i.val, hi⟩
 simp only [List.length_ofFn, convertedGates, List.get_eq_getElem, List.getElem_ofFn,
  convertedGate, List.map_cons, List.map_nil] at h
 have hid : wireIndex (11 + i.val) = 8 + i.val := by
  simp only [wireIndex, show ¬11 + i.val < 11 by omega, ite_false]
  omega
 rw [hid]
 cases hop : ops i <;> simpa [convertedGates, hop, UniqueReader.zjN, GateOp.eval] using h
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def originalIndex (t : Fin 8) : Nat := ![0,1,2,4,5,8,9,10] t
lemma zj6 : ∀ s : Fin 256, targetFun (zj4 s) = RawGraph.graph s := by
 decide +kernel
lemma zj7 : ∀ (s : Fin 256) (t : Fin 8) (j : Fin 11),
  j.val ≠ originalIndex t →
  (if j.val ∈ allowedInputs then s.val.testBit (rawIndex j.val) else false) =
  (if j.val ∈ allowedInputs then (RawGraph.addBit s t).val.testBit (rawIndex j.val) else false) := by
 decide +kernel
lemma zj8 {n : Nat} (ops : Fin n → Bool) (a b : Fin n → Nat)
  (s : Fin 256) (t : Fin 8) (j : Nat) (hj : j < 11) (hne : j ≠ originalIndex t) :
  semanticWire ops a b s j = semanticWire ops a b (RawGraph.addBit s t) j := by
 simp only [semanticWire, if_pos hj]
 exact zj7 s t ⟨j,hj⟩ hne
lemma zj9 {n : Nat} (ops : Fin n → Bool) (a b : Fin n → Nat) (j : Nat) :
  RawGraph.zjT (fun s => semanticWire ops a b s j) := by
 intro s t qu qE
 by_cases hj : j < 11
 ·simp only [semanticWire, if_pos hj] at qE ⊢
  by_cases hm : j ∈ allowedInputs
  ·simp only [if_pos hm] at qE ⊢
   have hi : rawIndex j < 8 := by
    have hh : ∀ r : Fin 11, rawIndex r.val < 8 := by decide +kernel
    exact hh ⟨j,hj⟩
   exact qu ⟨rawIndex j,hi⟩ qE
  ·simp only [if_neg hm] at qE
   contradiction
 ·simp only [semanticWire, if_neg hj] at qE ⊢
  apply zbR (convertedGates ops a b) (fun g hg => (zbX ops a b g hg).imp And.left id)
   (List.ofFn (zj4 s)) (List.ofFn (zj4 t)) (by simp) ?_ (wireIndex j) qE
  intro k hk
  by_cases hk8 : k < 8
  ·rw [List.getD_eq_getElem _ _ (by simpa using hk8)] at hk ⊢
   simp only [List.getElem_ofFn, zj4] at hk ⊢
   have zk : ∀ r : Fin 8, (![7,0,3,2,6,1,4,5] : Fin 8 → Nat) r < 8 := by decide +kernel
   exact qu ⟨_,zk ⟨k,hk8⟩⟩ hk
  ·rw [List.getD_eq_default _ _ (by simp; omega)] at hk
   exact Bool.noConfusion hk
lemma zka {n : Nat} (ops : Fin n → Bool) (a b : Fin n → Nat)
  (ha : ∀ i, a i ∈ allowedInputs ∨ 11 ≤ a i)
  (hb : ∀ i, b i ∈ allowedInputs ∨ 11 ≤ b i)
  (hc : ∀ i, a i < 11 + i.val ∧ b i < 11 + i.val) :
  ∀ j < 11 + n, semanticWire ops a b 0 j = false := by
 intro j
 induction j using Nat.strong_induction_on with
 | ind j ih =>
  intro hj
  by_cases hlow : j < 11
  ·simp [semanticWire, hlow]
  ·let i : Fin n := ⟨j-11, by omega⟩
   have he : j = 11 + i.val := by dsimp [i]; omega
   rw [he, semanticWire_eval ops a b ha hb hc]
   have hea : semanticWire ops a b 0 (a i) = false :=
    ih (a i) (by have := (hc i).1; omega) (by have := (hc i).1; omega)
   have heb : semanticWire ops a b 0 (b i) = false :=
    ih (b i) (by have := (hc i).2; omega) (by have := (hc i).2; omega)
   rw [hea, heb]
   cases ops i <;> rfl
lemma zkb {n : Nat} (ops : Fin n → Bool) (a b : Fin n → Nat)
  (ha : ∀ i, a i ∈ allowedInputs ∨ 11 ≤ a i)
  (hb : ∀ i, b i ∈ allowedInputs ∨ 11 ≤ b i)
  (hc : ∀ i, a i < 11 + i.val ∧ b i < 11 + i.val)
  (p : Fin n) (t : Fin 8) (ql : ∀ s, semanticWire ops a b s (10+n) = RawGraph.graph s)
  (hp : ops p = false) (zd : a p = originalIndex t) (qM : b p ≠ originalIndex t)
  (qV : ∀ j, j ≠ p → a j ≠ originalIndex t ∧ b j ≠ originalIndex t) :
  ∀ y : Fin 8, semanticWire ops a b (RawGraph.single y) (b p) = false := by
 apply RawGraph.zjZ (fun s => semanticWire ops a b s (b p)) t
 ·exact zj9 ops a b (b p)
 ·intro s hs
  have hv : originalIndex t < 11 := by
   have h : ∀ t : Fin 8, originalIndex t < 11 := by decide +kernel
   exact h t
  have he := UniqueReader.zjQ p a b ops
   (semanticWire ops a b s) (semanticWire ops a b (RawGraph.addBit s t))
   (fun i => (hc i).1) (fun i => (hc i).2)
   (fun j hj hne => zj8 ops a b s t j hj hne) qV
   (semanticWire_eval ops a b ha hb hc s) (semanticWire_eval ops a b ha hb hc (RawGraph.addBit s t))
   zd qM (out := 10+n) (by omega) (by have := p.isLt; omega) (by rw [hs,hp]; decide)
  simpa only [ql] using he
 ·exact zka ops a b ha hb hc (b p) (by have := (hc p).2; have := p.isLt; omega)
 ·intro s
  symm
  exact UniqueReader.zjO p a b ops
   (semanticWire ops a b s) (semanticWire ops a b (RawGraph.addBit s t))
   (fun i => (hc i).1) (fun i => (hc i).2)
   (fun j hj hne => zj8 ops a b s t j hj hne) qV
   (semanticWire_eval ops a b ha hb hc s) (semanticWire_eval ops a b ha hb hc (RawGraph.addBit s t))
   (b p) (by have := (hc p).2; have := p.isLt; omega) qM
   (fun hh => by have := (hc p).2; omega)
lemma witness_semantic_output
  (ops : Fin 14 → Bool) (a b : Fin 14 → Fin 33) (v : Nat → Nat)
  (qi : ∀ i : Fin 11, v i.val = baseValues.getD i.val 0)
  (ha : ∀ i, (a i).val ∈ allowedInputs ∨ 11 ≤ (a i).val)
  (hb : ∀ i, (b i).val ∈ allowedInputs ∨ 11 ≤ (b i).val)
  (hs : ∀ i, (a i).val < 11 + i.val ∧ (b i).val < 11 + i.val ∧
   v (11 + i.val) = if ops i then v (a i).val &&& v (b i).val else v (a i).val ||| v (b i).val)
  (ql : v 24 = 36671) :
  ∀ s, semanticWire ops (fun i => (a i).val) (fun i => (b i).val) s 24 = RawGraph.graph s := by
 let D : Circuit := { gates := convertedGates ops (fun i => (a i).val) (fun i => (b i).val), output := 21 }
 have qp := zbX ops (fun i => (a i).val) (fun i => (b i).val)
 have qJ : ∀ k : Fin 40, circuitFun 8 D (sample k) = (36671 : Nat).testBit k.val := by
  intro k
  change (wiresFrom (convertedGates ops (fun i => (a i).val) (fun i => (b i).val))
   (List.ofFn (sample k))).getD 21 false = _
  rw [zbZ ops (fun i => (a i).val) (fun i => (b i).val) v qi ha hb hs k]
  have qI := zbW (n := 14) v k 24 qi (by decide) (Or.inr (by decide))
  have zk : wireIndex 24 = 21 := by decide
  rw [zk, ql] at qI
  exact qI
 have zB := zbP (circuitFun 8 D) (zbS D qp) qJ
 intro s
 have h := congrFun zB (zj4 s)
 exact h.trans (zj6 s)
lemma witness_sole_or_singletons
  (ops : Fin 14 → Bool) (a b : Fin 14 → Fin 33) (v : Nat → Nat)
  (qi : ∀ i : Fin 11, v i.val = baseValues.getD i.val 0)
  (ha : ∀ i, (a i).val ∈ allowedInputs ∨ 11 ≤ (a i).val)
  (hb : ∀ i, (b i).val ∈ allowedInputs ∨ 11 ≤ (b i).val)
  (hs : ∀ i, (a i).val < 11 + i.val ∧ (b i).val < 11 + i.val ∧
   v (11 + i.val) = if ops i then v (a i).val &&& v (b i).val else v (a i).val ||| v (b i).val)
  (ql : v 24 = 36671) (p : Fin 14) (t : Fin 8)
  (hp : ops p = false) (zd : (a p).val = originalIndex t) (qM : (b p).val ≠ originalIndex t)
  (qV : ∀ j, j ≠ p → (a j).val ≠ originalIndex t ∧ (b j).val ≠ originalIndex t) :
  ∀ y : Fin 8, semanticWire ops (fun i => (a i).val) (fun i => (b i).val)
   (RawGraph.single y) (b p).val = false := by
 exact zkb ops (fun i => (a i).val) (fun i => (b i).val) ha hb
  (fun i => ⟨(hs i).1,(hs i).2.1⟩) p t
  (witness_semantic_output ops a b v qi ha hb hs ql) hp zd qM qV
lemma semantic_singletons_force_computed {n : Nat} (ops : Fin n → Bool) (a b : Fin n → Nat)
  (j : Nat) (hj : j ∈ allowedInputs ∨ 11 ≤ j)
  (hz : ∀ y : Fin 8, semanticWire ops a b (RawGraph.single y) j = false) :
  11 ≤ j := by
 by_contra hn
 have zx : j < 11 := by omega
 have hm : j ∈ allowedInputs := hj.resolve_right hn
 have hr : ∀ j : Fin 11, j.val ∈ allowedInputs →
   ∃ y : Fin 8, (RawGraph.single y).val.testBit (rawIndex j.val) = true := by
  decide +kernel
 obtain ⟨y,hy⟩ := hr ⟨j,zx⟩ hm
 have h := hz y
 simp only [semanticWire, if_pos zx, if_pos hm] at h
 rw [hy] at h
 contradiction
lemma zkc : ∀ t : Fin 8, ∃ s : Fin 256,
  RawGraph.graph s ≠ RawGraph.graph (RawGraph.addBit s t) := by
 decide +kernel
set_option maxHeartbeats 1000000 in
lemma zkd (ops : Fin 14 → Bool) (a b : Fin 14 → Nat)
  (ha : ∀ i, a i ∈ allowedInputs ∨ 11 ≤ a i)
  (hb : ∀ i, b i ∈ allowedInputs ∨ 11 ≤ b i)
  (hc : ∀ i, a i < 11 + i.val ∧ b i < 11 + i.val)
  (ql : ∀ s, semanticWire ops a b s 24 = RawGraph.graph s) (t : Fin 8) :
  ∃ p, a p = originalIndex t ∨ b p = originalIndex t := by
 by_contra hn
 have zC : ∀ j : Fin 14, a j ≠ originalIndex t ∧ b j ≠ originalIndex t := by
  intro j
  exact ⟨fun h => hn ⟨j,Or.inl h⟩, fun h => hn ⟨j,Or.inr h⟩⟩
 obtain ⟨s,hs⟩ := zkc t
 have hag := UniqueReader.zjO (0 : Fin 14) a b ops
  (semanticWire ops a b s) (semanticWire ops a b (RawGraph.addBit s t))
  (fun i => (hc i).1) (fun i => (hc i).2)
  (fun j hj hne => zj8 ops a b s t j hj hne)
  (fun j _ => zC j)
  (semanticWire_eval ops a b ha hb hc s)
  (semanticWire_eval ops a b ha hb hc (RawGraph.addBit s t))
 have zd := hag (a 0) (by have := (hc 0).1; omega) (zC 0).1
  (fun hh => by have := (hc 0).1; simp only [Fin.val_zero] at *; omega)
 have qM := hag (b 0) (by have := (hc 0).2; omega) (zC 0).2
  (fun hh => by have := (hc 0).2; simp only [Fin.val_zero] at *; omega)
 have hp : semanticWire ops a b s 11 = semanticWire ops a b (RawGraph.addBit s t) 11 := by
  have h0 := semanticWire_eval ops a b ha hb hc s (0 : Fin 14)
  have h1 := semanticWire_eval ops a b ha hb hc (RawGraph.addBit s t) (0 : Fin 14)
  rw [zd, qM] at h0
  simpa only [Fin.val_zero, Nat.add_zero] using h0.trans h1.symm
 have hv : originalIndex t < 11 := by
  have h : ∀ t : Fin 8, originalIndex t < 11 := by decide +kernel
  exact h t
 apply hs
 simpa only [ql] using hag 24 (by decide) (by omega) (fun _ => hp)
lemma zke (ops : Fin 14 → Bool) (a b : Fin 14 → Nat)
  (ha : ∀ i, a i ∈ allowedInputs ∨ 11 ≤ a i)
  (hb : ∀ i, b i ∈ allowedInputs ∨ 11 ≤ b i)
  (hc : ∀ i, a i < 11 + i.val ∧ b i < 11 + i.val)
  (ql : ∀ s, semanticWire ops a b s 24 = RawGraph.graph s) (t : Fin 8)
  (xn : Nat.card {p : Fin 14 // a p = originalIndex t ∨ b p = originalIndex t} ≤ 1) :
  ∃ p, (a p = originalIndex t ∨ b p = originalIndex t) ∧
   ∀ j, j ≠ p → a j ≠ originalIndex t ∧ b j ≠ originalIndex t := by
 obtain ⟨p,hp⟩ := zkd ops a b ha hb hc ql t
 haveI : Subsingleton {p : Fin 14 // a p = originalIndex t ∨ b p = originalIndex t} :=
  Finite.card_le_one_iff_subsingleton.mp xn
 refine ⟨p,hp,?_⟩
 intro j hne
 have he : (a j = originalIndex t ∨ b j = originalIndex t) → j = p := by
  intro hj
  exact congrArg Subtype.val (Subsingleton.elim (⟨j,hj⟩ : {q : Fin 14 // a q = originalIndex t ∨ b q = originalIndex t}) ⟨p,hp⟩)
 exact ⟨fun hj => hne (he (Or.inl hj)), fun hj => hne (he (Or.inr hj))⟩
lemma witness_raw_reader_unique
  (ops : Fin 14 → Bool) (a b : Fin 14 → Fin 33) (v : Nat → Nat)
  (qi : ∀ i : Fin 11, v i.val = baseValues.getD i.val 0)
  (ha : ∀ i, (a i).val ∈ allowedInputs ∨ 11 ≤ (a i).val)
  (hb : ∀ i, (b i).val ∈ allowedInputs ∨ 11 ≤ (b i).val)
  (hs : ∀ i, (a i).val < 11 + i.val ∧ (b i).val < 11 + i.val ∧
   v (11 + i.val) = if ops i then v (a i).val &&& v (b i).val else v (a i).val ||| v (b i).val)
  (ql : v 24 = 36671) (r : Fin 3)
  (xn : Nat.card {i : Fin 14 // (a i).val = r.val ∨ (b i).val = r.val} ≤ 1) :
  ∃ p, ((a p).val = r.val ∨ (b p).val = r.val) ∧
   ∀ j, j ≠ p → (a j).val ≠ r.val ∧ (b j).val ≠ r.val := by
 let t : Fin 8 := ⟨r.val,by omega⟩
 have zk : originalIndex t = r.val := by
  have h : ∀ q : Fin 3, originalIndex ⟨q.val,Nat.lt_trans q.isLt (by decide)⟩ = q.val := by decide +kernel
  exact h r
 have h := zke ops (fun i => (a i).val) (fun i => (b i).val) ha hb
  (fun i => ⟨(hs i).1,(hs i).2.1⟩)
  (witness_semantic_output ops a b v qi ha hb hs ql) t (by simpa only [zk] using xn)
 simpa only [zk] using h
lemma zkf : ∀ t : Fin 8,
  originalIndex t < 11 ∧ originalIndex t ∈ allowedInputs ∧ rawIndex (originalIndex t) = t.val := by
 decide +kernel
lemma zkg : ∀ t u : Fin 8, t ≠ u → originalIndex t ≠ originalIndex u := by
 decide +kernel
lemma zkh {n : Nat} (ops : Fin n → Bool) (a b : Fin n → Nat)
  (s : Fin 256) (t : Fin 8) :
  semanticWire ops a b s (originalIndex t) = s.val.testBit t.val := by
 obtain ⟨hl,hm,hr⟩ := zkf t
 simp only [semanticWire,if_pos hl,if_pos hm,hr]
lemma zki : ∀ t u : Fin 8, t ≠ u → ∃ s : Fin 256,
  s.val.testBit u.val = false ∧ RawGraph.graph s = false ∧
   RawGraph.graph (RawGraph.addBit s t) = true := by
 decide +kernel
lemma zkj {n : Nat} (ops : Fin n → Bool) (a b : Fin n → Nat)
  (ha : ∀ i, a i ∈ allowedInputs ∨ 11 ≤ a i)
  (hb : ∀ i, b i ∈ allowedInputs ∨ 11 ≤ b i)
  (hc : ∀ i, a i < 11 + i.val ∧ b i < 11 + i.val)
  (ql : ∀ s, semanticWire ops a b s (10+n) = RawGraph.graph s)
  (p : Fin n) (t u : Fin 8) (hne : t ≠ u)
  (hp : ops p = true) (zd : a p = originalIndex t) (qM : b p = originalIndex u)
  (qV : ∀ j, j ≠ p → a j ≠ originalIndex t ∧ b j ≠ originalIndex t) : False := by
 obtain ⟨s,zK,xo,hpos⟩ := zki t u hne
 have hv : originalIndex t < 11 := (zkf t).1
 have uA : b p ≠ originalIndex t := by
  rw [qM]
  exact zkg u t hne.symm
 have uN : semanticWire ops a b s (b p) ≠ ops p := by
  rw [qM,zkh,zK,hp]
  decide
 have h := UniqueReader.zjQ p a b ops
  (semanticWire ops a b s) (semanticWire ops a b (RawGraph.addBit s t))
  (fun i => (hc i).1) (fun i => (hc i).2)
  (fun j hj hne => zj8 ops a b s t j hj hne) qV
  (semanticWire_eval ops a b ha hb hc s) (semanticWire_eval ops a b ha hb hc (RawGraph.addBit s t))
  zd uA (out := 10+n) (by omega) (by have := p.isLt; omega) uN
 rw [ql,ql,xo,hpos] at h
 contradiction
lemma witness_sole_and_no_raw_mate
  (ops : Fin 14 → Bool) (a b : Fin 14 → Fin 33) (v : Nat → Nat)
  (qi : ∀ i : Fin 11, v i.val = baseValues.getD i.val 0)
  (ha : ∀ i, (a i).val ∈ allowedInputs ∨ 11 ≤ (a i).val)
  (hb : ∀ i, (b i).val ∈ allowedInputs ∨ 11 ≤ (b i).val)
  (hs : ∀ i, (a i).val < 11 + i.val ∧ (b i).val < 11 + i.val ∧
   v (11 + i.val) = if ops i then v (a i).val &&& v (b i).val else v (a i).val ||| v (b i).val)
  (ql : v 24 = 36671) (p : Fin 14) (t u : Fin 8) (hne : t ≠ u)
  (hp : ops p = true) (zd : (a p).val = originalIndex t) (qM : (b p).val = originalIndex u)
  (qV : ∀ j, j ≠ p → (a j).val ≠ originalIndex t ∧ (b j).val ≠ originalIndex t) : False := by
 exact zkj ops (fun i => (a i).val) (fun i => (b i).val) ha hb
  (fun i => ⟨(hs i).1,(hs i).2.1⟩) (witness_semantic_output ops a b v qi ha hb hs ql)
  p t u hne hp zd qM qV
lemma selectedReaders_injective {ι κ : Type} (a b : ι → ℕ)
  (raw : κ → ℕ) (qC : κ → ι) (qX : Function.Injective raw)
  (zb : ∀ t, a (qC t) = raw t ∨ b (qC t) = raw t)
  (yz : ∀ t u, t ≠ u → a (qC t) = raw t →
   b (qC t) = raw u → False) : Function.Injective qC := by
 intro t u h
 by_contra hne
 have hu := zb u
 rw [← h] at hu
 rcases zb t with ht | ht <;> rcases hu with hu | hu
 ·exact hne (qX (ht.symm.trans hu))
 ·exact yz t u hne ht hu
 ·exact yz u t (fun h => hne h.symm) (by rw [← h]; exact hu) (by rw [← h]; exact ht)
 ·exact hne (qX (ht.symm.trans hu))
lemma witness_sole_and_readers_injective {κ : Type}
  (ops : Fin 14 → Bool) (a b : Fin 14 → Fin 33) (v : Nat → Nat)
  (qi : ∀ i : Fin 11, v i.val = baseValues.getD i.val 0)
  (ha : ∀ i, (a i).val ∈ allowedInputs ∨ 11 ≤ (a i).val)
  (hb : ∀ i, (b i).val ∈ allowedInputs ∨ 11 ≤ (b i).val)
  (hs : ∀ i, (a i).val < 11 + i.val ∧ (b i).val < 11 + i.val ∧
   v (11 + i.val) = if ops i then v (a i).val &&& v (b i).val else v (a i).val ||| v (b i).val)
  (ql : v 24 = 36671)
  (raw : κ → Fin 8) (qC : κ → Fin 14) (qX : Function.Injective raw)
  (zb : ∀ t, (a (qC t)).val = originalIndex (raw t) ∨
   (b (qC t)).val = originalIndex (raw t))
  (xf : ∀ t, ops (qC t) = true)
  (qV : ∀ t j, j ≠ qC t →
   (a j).val ≠ originalIndex (raw t) ∧ (b j).val ≠ originalIndex (raw t)) :
  Function.Injective qC := by
 apply selectedReaders_injective (fun i => (a i).val) (fun i => (b i).val)
  (fun t => originalIndex (raw t)) qC
 ·intro t u h
  apply qX
  by_contra hne
  exact zkg (raw t) (raw u) hne h
 ·exact zb
 ·intro t u hne zd qM
  exact witness_sole_and_no_raw_mate ops a b v qi ha hb hs ql
   (qC t) (raw t) (raw u) (fun h => hne (qX h))
   (xf t) zd qM (qV t)
lemma witness_some_abc_or_reader_of_caps
  (ops : Fin 14 → Bool) (a b : Fin 14 → Fin 33) (v : Nat → Nat)
  (qi : ∀ i : Fin 11, v i.val = baseValues.getD i.val 0)
  (ha : ∀ i, (a i).val ∈ allowedInputs ∨ 11 ≤ (a i).val)
  (hb : ∀ i, (b i).val ∈ allowedInputs ∨ 11 ≤ (b i).val)
  (hs : ∀ i, (a i).val < 11 + i.val ∧ (b i).val < 11 + i.val ∧
   v (11 + i.val) = if ops i then v (a i).val &&& v (b i).val else v (a i).val ||| v (b i).val)
  (ql : v 24 = 36671)
  (xf : Nat.card {i : Fin 14 // ops i = true} = 5)
  (xn : ∀ r : Fin 3, Nat.card {i : Fin 14 // (a i).val = r.val ∨ (b i).val = r.val} ≤ 1) :
  ∃ r : Fin 3, ∃ p : Fin 14,
   ((a p).val = r.val ∨ (b p).val = r.val) ∧ ops p = false := by
 classical
 have vy := fun r => witness_raw_reader_unique ops a b v qi ha hb hs ql r (xn r)
 choose qC zb qV using vy
 by_contra hn
 have v9 : ∀ r, ops (qC r) = true := by
  intro r
  cases h : ops (qC r) with
  | true => rfl
  | false => exact False.elim (hn ⟨r,qC r,zb r,h⟩)
 let raw : Fin 3 → Fin 8 := fun r => ⟨r.val,Nat.lt_trans r.isLt (by decide)⟩
 have zk : ∀ r, originalIndex (raw r) = r.val := by
  change ∀ r : Fin 3, originalIndex ⟨r.val,Nat.lt_trans r.isLt (by decide)⟩ = r.val
  decide +kernel
 have qX : Function.Injective raw := by
  intro r s h
  apply Fin.ext
  exact congrArg (fun q : Fin 8 => q.val) h
 have vj := witness_sole_and_readers_injective ops a b v qi ha hb hs ql raw qC qX
  (fun r => by simpa only [zk] using zb r) v9
  (fun r j hne => by simpa only [zk] using qV r j hne)
 let f : Fin 3 → {i : Fin 14 // ops i = true ∧ ((a i).val < 3 ∨ (b i).val < 3)} :=
  fun r => ⟨qC r,v9 r,by
   rcases zb r with hl | hr
   ·exact Or.inl (hl ▸ r.isLt)
   ·exact Or.inr (hr ▸ r.isLt)⟩
 have hf : Function.Injective f := by
  intro r s h
  exact vj (congrArg Subtype.val h)
 have h3 : 3 ≤ Nat.card {i : Fin 14 // ops i = true ∧ ((a i).val < 3 ∨ (b i).val < 3)} := by
  have hc := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_fin, Nat.card_eq_fintype_card] using hc
 have h2 := witness_abc_and_reader_count_le_two ops a b v qi ha hb hs ql xf
 omega
lemma witness_some_abc_or_reader
  (ops : Fin 14 → Bool) (a b : Fin 14 → Fin 33) (v : Nat → Nat)
  (qi : ∀ i : Fin 11, v i.val = baseValues.getD i.val 0)
  (ha : ∀ i, (a i).val ∈ allowedInputs ∨ 11 ≤ (a i).val)
  (hb : ∀ i, (b i).val ∈ allowedInputs ∨ 11 ≤ (b i).val)
  (hs : ∀ i, (a i).val < 11 + i.val ∧ (b i).val < 11 + i.val ∧
   v (11 + i.val) = if ops i then v (a i).val &&& v (b i).val else v (a i).val ||| v (b i).val)
  (ql : v 24 = 36671) :
  ∃ r : Fin 3, ∃ p : Fin 14,
   ((a p).val = r.val ∨ (b p).val = r.val) ∧ ops p = false := by
 exact witness_some_abc_or_reader_of_caps ops a b v qi ha hb hs ql
  (witness_exact_gate_counts ops a b v qi ha hb hs ql).1
  (witness_reader_cap ops a b v qi ha hb hs ql)
namespace CleanMate
def MaskEq (q a b : Nat) : Prop := a ||| q = b ||| q
lemma maskEq_refl (q a : Nat) : MaskEq q a a := rfl
lemma maskEq_bit {q a b k : Nat} (h : MaskEq q a b)
  (hq : q.testBit k = false) : a.testBit k = b.testBit k := by
 have hh := congrArg (fun x : Nat => x.testBit k) h
 simpa only [Nat.testBit_or, hq, Bool.or_false] using hh
lemma maskEq_and {q a b c d : Nat} (hab : MaskEq q a b)
  (hcd : MaskEq q c d) : MaskEq q (a &&& c) (b &&& d) := by
 apply Nat.eq_of_testBit_eq
 intro k
 have h1 := congrArg (fun x : Nat => x.testBit k) hab
 have h2 := congrArg (fun x : Nat => x.testBit k) hcd
 simp only [Nat.testBit_or, Nat.testBit_and] at h1 h2 ⊢
 cases hq : q.testBit k <;> simp_all
lemma maskEq_or {q a b c d : Nat} (hab : MaskEq q a b)
  (hcd : MaskEq q c d) : MaskEq q (a ||| c) (b ||| d) := by
 apply Nat.eq_of_testBit_eq
 intro k
 have h1 := congrArg (fun x : Nat => x.testBit k) hab
 have h2 := congrArg (fun x : Nat => x.testBit k) hcd
 simp only [Nat.testBit_or] at h1 h2 ⊢
 cases hq : q.testBit k <;> simp_all
lemma maskEq_bypass (q a : Nat) : MaskEq q (a ||| q) a := by
 apply Nat.eq_of_testBit_eq
 intro k
 simp only [Nat.testBit_or]
 cases a.testBit k <;> cases q.testBit k <;> rfl
lemma join_clean {q t : Nat} (h : q &&& t = q) : t ||| q = t := by
 apply Nat.eq_of_testBit_eq
 intro k
 have hh := congrArg (fun x : Nat => x.testBit k) h
 simp only [Nat.testBit_and, Nat.testBit_or] at hh ⊢
 cases hq : q.testBit k <;> cases ht : t.testBit k <;> simp_all
lemma clean_bit_false {q t k : Nat} (h : q &&& t = q)
  (ht : t.testBit k = false) : q.testBit k = false := by
 have hh := congrArg (fun x : Nat => x.testBit k) h
 simpa only [Nat.testBit_and, ht, Bool.and_false] using hh.symm
def gateValue (op : Bool) (a b : Nat) : Nat :=
 if op then a &&& b else a ||| b
lemma gateValue_maskEq {q a b c d : Nat} (op : Bool)
  (hab : MaskEq q a b) (hcd : MaskEq q c d) :
  MaskEq q (gateValue op a c) (gateValue op b d) := by
 cases op
 ·exact maskEq_or hab hcd
 ·exact maskEq_and hab hcd
def run (n : Nat) (gs : List (Bool × Nat × Nat)) (w : Nat → Nat) : Nat → Nat :=
 match gs with
 | [] => w
 | (op, a, b) :: qa =>
   run (n + 1) qa (Function.update w n (gateValue op (w a) (w b)))
lemma run_maskEq {q : Nat} (gs : List (Bool × Nat × Nat)) (n : Nat)
  (w w' : Nat → Nat) (hw : ∀ i, MaskEq q (w i) (w' i)) :
  ∀ i, MaskEq q (run n gs w i) (run n gs w' i) := by
 induction gs generalizing n w w' with
 | nil => exact hw
 | cons g qa ih =>
   rcases g with ⟨op, a, b⟩
   apply ih
   intro i
   by_cases hi : i = n
   ·subst i
    simp only [Function.update_self]
    exact gateValue_maskEq op (hw a) (hw b)
   ·simp only [Function.update_of_ne hi]
    exact hw i
lemma bypass_maskEq {q a : Nat} (gs : List (Bool × Nat × Nat)) (n g : Nat)
  (w : Nat → Nat) (hg : w g = a ||| q) :
  ∀ i, MaskEq q (run n gs w i) (run n gs (Function.update w g a) i) := by
 apply run_maskEq
 intro i
 by_cases hi : i = g
 ·subst i
  simp only [Function.update_self, hg]
  exact maskEq_bypass q a
 ·simp only [Function.update_of_ne hi]
  exact maskEq_refl q (w i)
lemma target_high_bit (i : Fin 24) : (36671 : Nat).testBit (16 + i.val) = false := by
 revert i
 decide +kernel
def CausalFrom (n : Nat) : List (Bool × Nat × Nat) → Prop
 | [] => True
 | (_, a, b) :: qa => a < n ∧ b < n ∧ CausalFrom (n + 1) qa
def rho (cut u j : Nat) : Nat :=
 if j < cut then j else if j = cut then u else j - 1
def rename (f : Nat → Nat) (gs : List (Bool × Nat × Nat)) : List (Bool × Nat × Nat) :=
 gs.map (fun g => (g.1, f g.2.1, f g.2.2))
lemma rho_lt {cut u n j : Nat} (hu : u < cut) (zw : cut < n) (hj : j < n) :
  rho cut u j < n - 1 := by
 unfold rho
 split_ifs <;> omega
lemma rho_before {cut u j : Nat} (hj : j < cut) : rho cut u j = j := by
 simp only [rho, hj, ↓reduceIte]
lemma rho_cut (cut u : Nat) : rho cut u cut = u := by
 simp only [rho, lt_self_iff_false, ↓reduceIte]
lemma rho_after {cut u j : Nat} (hj : cut < j) : rho cut u j = j - 1 := by
 simp only [rho, show ¬j < cut by omega, show j ≠ cut by omega, ↓reduceIte]
lemma run_append (pre qb : List (Bool × Nat × Nat)) (n : Nat) (w : Nat → Nat) :
  run n (pre ++ qb) w = run (n + pre.length) qb (run n pre w) := by
 induction pre generalizing n w with
 | nil => simp only [List.nil_append, List.length_nil, Nat.add_zero, run]
 | cons g qa ih =>
   rcases g with ⟨op, a, b⟩
   simp only [List.cons_append, run, List.length_cons]
   rw [ih]
   congr 1 <;> omega
lemma run_preserves_below (gs : List (Bool × Nat × Nat)) (n j : Nat)
  (w : Nat → Nat) (hj : j < n) : run n gs w j = w j := by
 induction gs generalizing n w with
 | nil => rfl
 | cons g qa ih =>
   rcases g with ⟨op, a, b⟩
   simp only [run]
   rw [ih (n + 1) _ (by omega), Function.update_of_ne (by omega : j ≠ n)]
lemma renamed_tail_causal {cut u : Nat} (hu : u < cut)
  (gs : List (Bool × Nat × Nat)) (n : Nat) (zw : cut < n)
  (hc : CausalFrom n gs) : CausalFrom (n - 1) (rename (rho cut u) gs) := by
 induction gs generalizing n with
 | nil => trivial
 | cons g qa ih =>
   rcases g with ⟨op, a, b⟩
   obtain ⟨ha, hb, hr⟩ := hc
   change rho cut u a < n - 1 ∧ rho cut u b < n - 1 ∧
    CausalFrom (n - 1 + 1) (rename (rho cut u) qa)
   refine ⟨rho_lt hu zw ha, rho_lt hu zw hb, ?_⟩
   have hh := ih (n + 1) (by omega) hr
   convert hh using 1 <;> omega
lemma renamed_tail_eval {cut u : Nat} (hu : u < cut)
  (gs : List (Bool × Nat × Nat)) (n : Nat) (zw : cut < n)
  (hc : CausalFrom n gs) (w w' : Nat → Nat)
  (hw : ∀ j < n, w j = w' (rho cut u j)) :
  ∀ j < n + gs.length, run n gs w j =
   run (n - 1) (rename (rho cut u) gs) w' (rho cut u j) := by
 induction gs generalizing n w w' with
 | nil => simpa only [run, rename, List.map_nil, List.length_nil, Nat.add_zero] using hw
 | cons g qa ih =>
   rcases g with ⟨op, a, b⟩
   obtain ⟨ha, hb, hr⟩ := hc
   have hn : 0 < n := by omega
   let z := gateValue op (w a) (w b)
   have hz : gateValue op (w' (rho cut u a)) (w' (rho cut u b)) = z := by
    rw [← hw a ha, ← hw b hb]
   have tE : ∀ j < n + 1,
     Function.update w n z j = Function.update w' (n - 1) z (rho cut u j) := by
    intro j hj
    by_cases hjn : j = n
    ·subst j
     rw [rho_after zw, Function.update_self, Function.update_self]
    ·have hlt : j < n := by omega
     rw [Function.update_of_ne hjn,
      Function.update_of_ne (by have := rho_lt hu zw hlt; omega)]
     exact hw j hlt
   have hi := ih (n + 1) (by omega) hr
    (Function.update w n z) (Function.update w' (n - 1) z) tE
   intro j hj
   have hj' : j < n + 1 + qa.length := by simp only [List.length_cons] at hj; omega
   specialize hi j hj'
   simpa only [run, rename, List.map_cons, hz, Nat.add_sub_cancel,
    show n - 1 + 1 = n by omega] using hi
lemma erased_start_eq {cut u : Nat} (hu : u < cut) (w : Nat → Nat) :
  ∀ j < cut + 1, Function.update w cut (w u) j = w (rho cut u j) := by
 intro j hj
 by_cases heq : j = cut
 ·subst j
  rw [Function.update_self, rho_cut]
 ·have hlt : j < cut := by omega
  rw [Function.update_of_ne heq, rho_before hlt]
lemma erased_tail_maskEq {cut h u : Nat} (hu : u < cut)
  (qb : List (Bool × Nat × Nat)) (hc : CausalFrom (cut + 1) qb)
  (w : Nat → Nat) :
  ∀ j < cut + 1 + qb.length,
   MaskEq (w h)
    (run (cut + 1) qb (Function.update w cut (w h ||| w u)) j)
    (run cut (rename (rho cut u) qb) w (rho cut u j)) := by
 intro j hj
 have he := renamed_tail_eval hu qb (cut + 1) (by omega) hc
  (Function.update w cut (w u)) w (erased_start_eq hu w) j hj
 have hm := bypass_maskEq (q := w h) (a := w u) qb (cut + 1) cut
  (Function.update w cut (w h ||| w u)) (by simp only [Function.update_self, Nat.or_comm]) j
 have hup : Function.update (Function.update w cut (w h ||| w u)) cut (w u) =
   Function.update w cut (w u) := by
  funext i
  by_cases hi : i = cut
  ·subst i
   simp only [Function.update_self]
  ·simp only [Function.update_of_ne hi]
 rw [hup] at hm
 simpa only [Nat.add_sub_cancel] using he ▸ hm
lemma erased_tail_recover {cut h u out t : Nat} (hu : u < cut)
  (qb : List (Bool × Nat × Nat)) (hc : CausalFrom (cut + 1) qb)
  (w : Nat → Nat) (ql : out < cut + 1 + qb.length)
  (ht : run (cut + 1) qb (Function.update w cut (w h ||| w u)) out = t)
  (hq : w h &&& t = w h) :
  run cut (rename (rho cut u) qb) w (rho cut u out) ||| w h = t := by
 have hm := erased_tail_maskEq (h := h) hu qb hc w out ql
 change run (cut + 1) qb (Function.update w cut (w h ||| w u)) out ||| w h = _ at hm
 rw [ht, join_clean hq] at hm
 exact hm.symm
lemma causal_append (pre qb : List (Bool × Nat × Nat)) (n : Nat) :
  CausalFrom n (pre ++ qb) ↔ CausalFrom n pre ∧ CausalFrom (n + pre.length) qb := by
 induction pre generalizing n with
 | nil => simp only [List.nil_append, List.length_nil, Nat.add_zero, CausalFrom, true_and]
 | cons g qa ih =>
   rcases g with ⟨op, a, b⟩
   simp only [List.cons_append, CausalFrom, List.length_cons, ih]
   have heq : n + 1 + qa.length = n + (qa.length + 1) := by omega
   rw [heq]
   tauto
def normalized (n : Nat) (pre : List (Bool × Nat × Nat)) (h u : Nat)
  (qb : List (Bool × Nat × Nat)) (out : Nat) : List (Bool × Nat × Nat) :=
 pre ++ (rename (rho (n + pre.length) u) qb ++ [(false, h, rho (n + pre.length) u out)])
lemma normalized_length (n : Nat) (pre : List (Bool × Nat × Nat)) (h u : Nat)
  (qb : List (Bool × Nat × Nat)) (out : Nat) :
  (normalized n pre h u qb out).length = (pre ++ (false, h, u) :: qb).length := by
 simp only [normalized, rename, List.length_append, List.length_map,
  List.length_cons, List.length_nil]
lemma normalized_causal (n : Nat) (pre : List (Bool × Nat × Nat)) (h u : Nat)
  (qb : List (Bool × Nat × Nat)) (out : Nat)
  (hc : CausalFrom n (pre ++ (false, h, u) :: qb))
  (ql : out < n + (pre ++ (false, h, u) :: qb).length) :
  CausalFrom n (normalized n pre h u qb out) := by
 rw [causal_append] at hc
 obtain ⟨yn, hh, hu, zf⟩ := hc
 unfold normalized
 rw [causal_append, causal_append]
 refine ⟨yn, ?_, ?_⟩
 ·simpa only [Nat.add_sub_cancel] using renamed_tail_causal hu qb (n + pre.length + 1) (by omega) zf
 ·change h < n + pre.length + (rename (rho (n + pre.length) u) qb).length ∧
   rho (n + pre.length) u out < n + pre.length + (rename (rho (n + pre.length) u) qb).length ∧ True
  simp only [rename, List.length_map]
  refine ⟨by omega, ?_, trivial⟩
  have he := rho_lt (j := out) hu (n := n + pre.length + 1 + qb.length) (by omega) (by simp only [List.length_append, List.length_cons] at ql; omega)
  omega
lemma normalized_output (n : Nat) (pre : List (Bool × Nat × Nat)) (h u : Nat)
  (qb : List (Bool × Nat × Nat)) (out t : Nat) (w : Nat → Nat)
  (hc : CausalFrom n (pre ++ (false, h, u) :: qb))
  (ql : out < n + (pre ++ (false, h, u) :: qb).length)
  (ht : run n (pre ++ (false, h, u) :: qb) w out = t)
  (hq : (run n pre w h) &&& t = run n pre w h) :
  run n (normalized n pre h u qb out) w (n + pre.length + qb.length) = t := by
 rw [causal_append] at hc
 obtain ⟨_, hh, hu, zf⟩ := hc
 rw [run_append] at ht
 change run (n + pre.length + 1) qb
  (Function.update (run n pre w) (n + pre.length)
   (run n pre w h ||| run n pre w u)) out = t at ht
 have ho : out < n + pre.length + 1 + qb.length := by
  simp only [List.length_append, List.length_cons] at ql
  omega
 have hr := erased_tail_recover hu qb zf (run n pre w) ho ht hq
 have hp := run_preserves_below (rename (rho (n + pre.length) u) qb)
  (n + pre.length) h (run n pre w) hh
 unfold normalized
 rw [run_append, run_append]
 simp only [rename, List.length_map, run, Function.update_self, gateValue, Bool.false_eq_true, ↓reduceIte]
 change (run (n + pre.length) (rename (rho (n + pre.length) u) qb) (run n pre w) h) |||
  (run (n + pre.length) (rename (rho (n + pre.length) u) qb) (run n pre w) (rho (n + pre.length) u out)) = t
 rw [hp, Nat.or_comm]
 exact hr
lemma normalized_wire_maskEq (n : Nat) (pre : List (Bool × Nat × Nat)) (h u : Nat)
  (qb : List (Bool × Nat × Nat)) (out : Nat) (w : Nat → Nat)
  (hc : CausalFrom n (pre ++ (false, h, u) :: qb)) :
  ∀ j < n + (pre ++ (false, h, u) :: qb).length,
   MaskEq (run n pre w h) (run n (pre ++ (false, h, u) :: qb) w j)
    (run n (normalized n pre h u qb out) w (rho (n + pre.length) u j)) := by
 rw [causal_append] at hc
 obtain ⟨_, _, hu, zf⟩ := hc
 intro j hj
 have hj' : j < n + pre.length + 1 + qb.length := by
  simp only [List.length_append, List.length_cons] at hj
  omega
 have hm := erased_tail_maskEq (h := h) hu qb zf (run n pre w) j hj'
 have hjr : rho (n + pre.length) u j < n + pre.length + qb.length := by
  have he := rho_lt hu (n := n + pre.length + 1 + qb.length) (by omega) hj'
  omega
 rw [run_append]
 change MaskEq (run n pre w h)
  (run (n + pre.length + 1) qb
   (Function.update (run n pre w) (n + pre.length)
    (run n pre w h ||| run n pre w u)) j) _
 unfold normalized
 rw [run_append, run_append]
 simp only [rename, List.length_map]
 rw [run_preserves_below _ _ _ _ hjr]
 exact hm
lemma normalized_false_bit (n : Nat) (pre : List (Bool × Nat × Nat)) (h u : Nat)
  (qb : List (Bool × Nat × Nat)) (out t k : Nat) (w : Nat → Nat)
  (hc : CausalFrom n (pre ++ (false, h, u) :: qb))
  (hq : (run n pre w h) &&& t = run n pre w h) (ht : t.testBit k = false) :
  ∀ j < n + (pre ++ (false, h, u) :: qb).length,
   (run n (pre ++ (false, h, u) :: qb) w j).testBit k =
    (run n (normalized n pre h u qb out) w (rho (n + pre.length) u j)).testBit k := by
 intro j hj
 exact maskEq_bit (normalized_wire_maskEq n pre h u qb out w hc j hj) (clean_bit_false hq ht)
def opAt : List (Bool × Nat × Nat) → Nat → Bool
 | [], _ => false
 | g :: _, 0 => g.1
 | _ :: qa, j + 1 => opAt qa j
lemma opAt_append_before (pre qb : List (Bool × Nat × Nat)) (j : Nat)
  (hj : j < pre.length) : opAt (pre ++ qb) j = opAt pre j := by
 induction pre generalizing j with
 | nil => simp at hj
 | cons g qa ih =>
   cases j with
   | zero => rfl
   | succ j =>
     change opAt (qa ++ qb) j = opAt qa j
     exact ih j (by simpa using hj)
lemma opAt_append_shift (pre qb : List (Bool × Nat × Nat)) (j : Nat) :
  opAt (pre ++ qb) (pre.length + j) = opAt qb j := by
 induction pre with
 | nil => simp only [List.nil_append, List.length_nil, Nat.zero_add]
 | cons g qa ih =>
   simpa only [List.cons_append, List.length_cons, Nat.succ_add, opAt] using ih
lemma opAt_rename (f : Nat → Nat) (gs : List (Bool × Nat × Nat)) (j : Nat) :
  opAt (rename f gs) j = opAt gs j := by
 induction gs generalizing j with
 | nil => rfl
 | cons g qa ih =>
   cases j with
   | zero => rfl
   | succ j => exact ih j
def gateShift (i j : Nat) : Nat := if j < i then j else j - 1
lemma normalized_op_before (n : Nat) (pre : List (Bool × Nat × Nat)) (h u : Nat)
  (qb : List (Bool × Nat × Nat)) (out j : Nat) (hj : j < pre.length) :
  opAt (normalized n pre h u qb out) j = opAt (pre ++ (false, h, u) :: qb) j := by
 unfold normalized
 rw [opAt_append_before _ _ _ hj, opAt_append_before _ _ _ hj]
lemma normalized_op_after (n : Nat) (pre : List (Bool × Nat × Nat)) (h u : Nat)
  (qb : List (Bool × Nat × Nat)) (out j : Nat) (hj : j < qb.length) :
  opAt (normalized n pre h u qb out) (pre.length + j) =
   opAt (pre ++ (false, h, u) :: qb) (pre.length + (j + 1)) := by
 unfold normalized
 rw [opAt_append_shift, opAt_append_shift]
 change opAt (rename (rho (n + pre.length) u) qb ++ [(false, h, rho (n + pre.length) u out)]) j = opAt qb j
 rw [opAt_append_before _ _ _ (by simpa only [rename, List.length_map] using hj), opAt_rename]
lemma and_index_ne (pre qb : List (Bool × Nat × Nat)) (h u j : Nat)
  (hop : opAt (pre ++ (false, h, u) :: qb) j = true) : j ≠ pre.length := by
 intro hj
 subst j
 have he := opAt_append_shift pre ((false, h, u) :: qb) 0
 simp only [Nat.add_zero, opAt] at he
 rw [he] at hop
 contradiction
lemma normalized_and_index (n : Nat) (pre : List (Bool × Nat × Nat)) (h u : Nat)
  (qb : List (Bool × Nat × Nat)) (out j : Nat)
  (hj : j < (pre ++ (false, h, u) :: qb).length)
  (hop : opAt (pre ++ (false, h, u) :: qb) j = true) :
  gateShift pre.length j < pre.length + qb.length ∧
  opAt (normalized n pre h u qb out) (gateShift pre.length j) = true ∧
  rho (n + pre.length) u (n + j) = n + gateShift pre.length j := by
 have hne := and_index_ne pre qb h u j hop
 by_cases hbefore : j < pre.length
 ·simp only [gateShift, hbefore, ↓reduceIte]
  refine ⟨by omega, ?_, ?_⟩
  ·rw [normalized_op_before n pre h u qb out j hbefore]
   exact hop
  ·rw [rho_before (by omega)]
 ·have te : pre.length < j := by omega
  have hk : j - (pre.length + 1) < qb.length := by
   simp only [List.length_append, List.length_cons] at hj
   omega
  have vY := normalized_op_after n pre h u qb out (j - (pre.length + 1)) hk
  have heq : pre.length + (j - (pre.length + 1) + 1) = j := by omega
  have wJ : pre.length + (j - (pre.length + 1)) = j - 1 := by omega
  rw [heq, wJ, hop] at vY
  simp only [gateShift, hbefore, ↓reduceIte]
  refine ⟨by omega, vY, ?_⟩
  rw [rho_after (by omega)]
  omega
lemma gateShift_injective_away {i j k : Nat} (hj : j ≠ i) (hk : k ≠ i)
  (heq : gateShift i j = gateShift i k) : j = k := by
 unfold gateShift at heq
 split_ifs at heq <;> omega
lemma normalized_and_false_bit (n : Nat) (pre : List (Bool × Nat × Nat)) (h u : Nat)
  (qb : List (Bool × Nat × Nat)) (out t k j : Nat) (w : Nat → Nat)
  (hc : CausalFrom n (pre ++ (false, h, u) :: qb))
  (hq : (run n pre w h) &&& t = run n pre w h) (ht : t.testBit k = false)
  (hj : j < (pre ++ (false, h, u) :: qb).length)
  (hop : opAt (pre ++ (false, h, u) :: qb) j = true) :
  gateShift pre.length j < pre.length + qb.length ∧
  opAt (normalized n pre h u qb out) (gateShift pre.length j) = true ∧
  (run n (pre ++ (false, h, u) :: qb) w (n + j)).testBit k =
   (run n (normalized n pre h u qb out) w (n + gateShift pre.length j)).testBit k := by
 obtain ⟨hb, ho, hr⟩ := normalized_and_index n pre h u qb out j hj hop
 refine ⟨hb, ho, ?_⟩
 have he := normalized_false_bit n pre h u qb out t k w hc hq ht (n + j) (by omega)
 rwa [hr] at he
def orWeight (neg : Nat) : Nat → List (Bool × Nat × Nat) → (Nat → Nat) → Nat
 | _, [], _ => 0
 | n, g :: gs, v => (if g.1 then 0 else v n &&& neg) + orWeight neg (n + 1) gs v
def orCost (neg n : Nat) (gs : List (Bool × Nat × Nat)) (w : Nat → Nat) : Nat :=
 orWeight neg n gs (run n gs w)
lemma orWeight_append (neg n : Nat) (pre qb : List (Bool × Nat × Nat)) (v : Nat → Nat) :
  orWeight neg n (pre ++ qb) v =
   orWeight neg n pre v + orWeight neg (n + pre.length) qb v := by
 induction pre generalizing n with
 | nil => simp [orWeight]
 | cons g pre ih =>
   simp only [List.cons_append, orWeight, List.length_cons]
   rw [ih]
   simp only [Nat.add_assoc, Nat.add_comm 1]
lemma orWeight_rename (neg n m : Nat) (gs : List (Bool × Nat × Nat))
  (f : Nat → Nat) (v v' : Nat → Nat)
  (hv : ∀ i < gs.length, v (n + i) &&& neg = v' (m + i) &&& neg) :
  orWeight neg n gs v = orWeight neg m (rename f gs) v' := by
 induction gs generalizing n m with
 | nil => rfl
 | cons g gs ih =>
   have zi := hv 0 (by simp)
   simp only [Nat.add_zero] at zi
   have zf : ∀ i < gs.length, v (n + 1 + i) &&& neg = v' (m + 1 + i) &&& neg := by
    intro i hi
    have h := hv (i + 1) (by simpa using Nat.succ_lt_succ hi)
    simpa only [Nat.add_assoc, Nat.add_comm 1] using h
   simp only [rename, List.map_cons, orWeight]
   rw [zi, ih (n + 1) (m + 1) zf]
   rfl
lemma orWeight_values (neg n : Nat) (gs : List (Bool × Nat × Nat)) (v v' : Nat → Nat)
  (hv : ∀ i < gs.length, v (n + i) &&& neg = v' (n + i) &&& neg) :
  orWeight neg n gs v = orWeight neg n gs v' := by
 simpa [rename] using
  orWeight_rename neg n n gs id v v' hv
lemma maskEq_and_mask {q a b neg : Nat} (h : MaskEq q a b) (hq : q &&& neg = 0) :
  a &&& neg = b &&& neg := by
 apply Nat.eq_of_testBit_eq
 intro i
 have hc := congrArg (fun x : Nat => x.testBit i) hq
 simp only [Nat.testBit_and] at hc
 cases hn : neg.testBit i with
 | false => simp only [Nat.testBit_and, hn, Bool.and_false]
 | true =>
   have hqf : q.testBit i = false := by simpa [hn] using hc
   simpa only [Nat.testBit_and, hn, Bool.and_true] using maskEq_bit h hqf
lemma clean_mask_zero {q t neg : Nat} (hq : q &&& t = q) (ht : t &&& neg = 0) :
  q &&& neg = 0 := by
 calc
  q &&& neg = (q &&& t) &&& neg := by rw [hq]
  _ = q &&& (t &&& neg) := Nat.and_assoc q t neg
  _ = 0 := by rw [ht, Nat.and_zero]
lemma and_mask_ne_zero {a neg k : Nat} (ha : a.testBit k = true)
  (hn : neg.testBit k = true) : a &&& neg ≠ 0 := by
 intro he
 have hh := congrArg (fun x : Nat => x.testBit k) he
 simpa [Nat.testBit_and, ha, hn] using hh
lemma normalized_orCost (neg n : Nat) (pre : List (Bool × Nat × Nat)) (h u : Nat)
  (qb : List (Bool × Nat × Nat)) (out t : Nat) (w : Nat → Nat)
  (hc : CausalFrom n (pre ++ (false, h, u) :: qb))
  (ql : out < n + (pre ++ (false, h, u) :: qb).length)
  (ht : run n (pre ++ (false, h, u) :: qb) w out = t)
  (hq : run n pre w h &&& t = run n pre w h)
  (xo : t &&& neg = 0) :
  orCost neg n (pre ++ (false, h, u) :: qb) w =
   orCost neg n (normalized n pre h u qb out) w +
    (run n (pre ++ (false, h, u) :: qb) w (n + pre.length) &&& neg) := by
 let v := run n (pre ++ (false, h, u) :: qb) w
 let v' := run n (normalized n pre h u qb out) w
 have zq : run n pre w h &&& neg = 0 := clean_mask_zero hq xo
 have vk : ∀ j < n + (pre ++ (false, h, u) :: qb).length,
   v j &&& neg = v' (rho (n + pre.length) u j) &&& neg := by
  intro j hj
  exact maskEq_and_mask (normalized_wire_maskEq n pre h u qb out w hc j hj) zq
 have yn : orWeight neg n pre v = orWeight neg n pre v' := by
  apply orWeight_values
  intro i hi
  have he := vk (n + i) (by simp only [List.length_append, List.length_cons]; omega)
  rw [rho_before (by omega)] at he
  exact he
 have zf : orWeight neg (n + pre.length + 1) qb v =
   orWeight neg (n + pre.length) (rename (rho (n + pre.length) u) qb) v' := by
  apply orWeight_rename
  intro i hi
  have he := vk (n + pre.length + 1 + i)
   (by simp only [List.length_append, List.length_cons]; omega)
  rw [rho_after (by omega)] at he
  convert he using 1 <;> congr 2 <;> omega
 have ht' : v' (n + pre.length + qb.length) = t :=
  normalized_output n pre h u qb out t w hc ql ht hq
 have ux : orWeight neg (n + pre.length + (rename (rho (n + pre.length) u) qb).length)
   [(false, h, rho (n + pre.length) u out)] v' = 0 := by
  simp only [orWeight, Bool.false_eq_true, ↓reduceIte, Nat.add_zero, rename, List.length_map]
  rw [ht', xo]
 change orWeight neg n (pre ++ (false, h, u) :: qb) v =
  orWeight neg n (pre ++ (rename (rho (n + pre.length) u) qb ++
   [(false, h, rho (n + pre.length) u out)])) v' + (v (n + pre.length) &&& neg)
 rw [orWeight_append, orWeight_append, orWeight_append, ux]
 change orWeight neg n pre v +
   ((v (n + pre.length) &&& neg) + orWeight neg (n + pre.length + 1) qb v) =
  (orWeight neg n pre v' +
   (orWeight neg (n + pre.length) (rename (rho (n + pre.length) u) qb) v' + 0)) +
   (v (n + pre.length) &&& neg)
 rw [yn, zf]
 omega
lemma normalized_orCost_strict (neg n : Nat) (pre : List (Bool × Nat × Nat)) (h u : Nat)
  (qb : List (Bool × Nat × Nat)) (out t : Nat) (w : Nat → Nat)
  (hc : CausalFrom n (pre ++ (false, h, u) :: qb))
  (ql : out < n + (pre ++ (false, h, u) :: qb).length)
  (ht : run n (pre ++ (false, h, u) :: qb) w out = t)
  (hq : run n pre w h &&& t = run n pre w h)
  (xo : t &&& neg = 0)
  (xg : run n (pre ++ (false, h, u) :: qb) w (n + pre.length) &&& neg ≠ 0) :
  orCost neg n (normalized n pre h u qb out) w <
   orCost neg n (pre ++ (false, h, u) :: qb) w := by
 have he := normalized_orCost neg n pre h u qb out t w hc ql ht hq xo
 omega
lemma swap_or_run (n : Nat) (pre : List (Bool × Nat × Nat)) (h u : Nat)
  (qb : List (Bool × Nat × Nat)) (w : Nat → Nat) :
  run n (pre ++ (false, h, u) :: qb) w =
   run n (pre ++ (false, u, h) :: qb) w := by
 rw [run_append, run_append]
 simp only [run, gateValue, Bool.false_eq_true, ↓reduceIte]
 rw [Nat.or_comm (run n pre w h) (run n pre w u)]
lemma swap_orWeight (neg n : Nat) (pre : List (Bool × Nat × Nat)) (h u : Nat)
  (qb : List (Bool × Nat × Nat)) (v : Nat → Nat) :
  orWeight neg n (pre ++ (false, h, u) :: qb) v =
   orWeight neg n (pre ++ (false, u, h) :: qb) v := by
 rw [orWeight_append, orWeight_append]
 rfl
lemma swap_orCost (neg n : Nat) (pre : List (Bool × Nat × Nat)) (h u : Nat)
  (qb : List (Bool × Nat × Nat)) (w : Nat → Nat) :
  orCost neg n (pre ++ (false, h, u) :: qb) w =
   orCost neg n (pre ++ (false, u, h) :: qb) w := by
 unfold orCost
 rw [swap_or_run]
 exact swap_orWeight neg n pre h u qb _
lemma swap_or_opAt (pre : List (Bool × Nat × Nat)) (h u : Nat)
  (qb : List (Bool × Nat × Nat)) (j : Nat) :
  opAt (pre ++ (false, h, u) :: qb) j =
   opAt (pre ++ (false, u, h) :: qb) j := by
 induction pre generalizing j with
 | nil => cases j <;> rfl
 | cons g pre ih =>
   cases j with
   | zero => rfl
   | succ j => exact ih j
lemma swap_or_causal (n : Nat) (pre : List (Bool × Nat × Nat)) (h u : Nat)
  (qb : List (Bool × Nat × Nat)) :
  CausalFrom n (pre ++ (false, h, u) :: qb) ↔
   CausalFrom n (pre ++ (false, u, h) :: qb) := by
 rw [causal_append, causal_append]
 change (_ ∧ h < _ ∧ u < _ ∧ _) ↔ (_ ∧ u < _ ∧ h < _ ∧ _)
 tauto
lemma gateValue_mask_closed (op : Bool) (a b xm : Nat)
  (ha : a &&& xm = a) (hb : b &&& xm = b) :
  gateValue op a b &&& xm = gateValue op a b := by
 apply Nat.eq_of_testBit_eq
 intro i
 have h1 := congrArg (fun x : Nat => x.testBit i) ha
 have h2 := congrArg (fun x : Nat => x.testBit i) hb
 cases op <;> simp only [gateValue, Bool.false_eq_true, ↓reduceIte,
  Nat.testBit_and, Nat.testBit_or] at h1 h2 ⊢ <;>
  cases hA : a.testBit i <;> cases hB : b.testBit i <;>
   cases hM : xm.testBit i <;> simp_all
lemma run_mask_closed (xm n : Nat) (gs : List (Bool × Nat × Nat)) (w : Nat → Nat)
  (hw : ∀ j, w j &&& xm = w j) :
  ∀ j, run n gs w j &&& xm = run n gs w j := by
 induction gs generalizing n w with
 | nil => exact hw
 | cons g gs ih =>
   rcases g with ⟨op, a, b⟩
   apply ih
   intro j
   by_cases hj : j = n
   ·subst j
    simp only [Function.update_self]
    exact gateValue_mask_closed op (w a) (w b) xm (hw a) (hw b)
   ·simp only [Function.update_of_ne hj]
    exact hw j
lemma masked_clean_iff (a target neg xm : Nat)
  (ha : a &&& xm = a) (wW : target ||| neg = xm)
  (yN : target &&& neg = 0) :
  a &&& neg = 0 ↔ a &&& target = a := by
 constructor
 ·intro zq
  apply Nat.eq_of_testBit_eq
  intro i
  have h1 := congrArg (fun x : Nat => x.testBit i) ha
  have h2 := congrArg (fun x : Nat => x.testBit i) wW
  have h3 := congrArg (fun x : Nat => x.testBit i) zq
  simp only [Nat.testBit_and, Nat.testBit_or] at h1 h2 h3 ⊢
  cases hA : a.testBit i <;> cases hT : target.testBit i <;>
   cases hN : neg.testBit i <;> simp_all
 ·intro zq
  exact clean_mask_zero zq yN
def ValidSource (j : Nat) : Prop := j ∈ allowedInputs ∨ 11 ≤ j
def SourcesValid (gs : List (Bool × Nat × Nat)) : Prop :=
 ∀ g ∈ gs, ValidSource g.2.1 ∧ ValidSource g.2.2
def initialValues (j : Nat) : Nat := baseValues.getD j 0
def DirtyPair (gs : List (Bool × Nat × Nat)) : Prop :=
 ∃ i < gs.length, ∃ j < gs.length, i ≠ j ∧ opAt gs i = true ∧ opAt gs j = true ∧
  (∃ k : Fin 24, (run 11 gs initialValues (11+i)).testBit (16+k.val) = true) ∧
  (∃ k : Fin 24, (run 11 gs initialValues (11+j)).testBit (16+k.val) = true)
def Good (gs : List (Bool × Nat × Nat)) : Prop :=
 gs.length = 14 ∧ CausalFrom 11 gs ∧ SourcesValid gs ∧
  run 11 gs initialValues 24 = 36671 ∧ DirtyPair gs
lemma rho_validSource {cut u j : Nat} (zw : 11 ≤ cut)
  (hu : ValidSource u) (hj : ValidSource j) : ValidSource (rho cut u j) := by
 unfold rho
 split_ifs
 ·exact hj
 ·exact hu
 ·exact Or.inr (by omega)
lemma sourcesValid_append (pre qb : List (Bool × Nat × Nat)) :
  SourcesValid (pre ++ qb) ↔ SourcesValid pre ∧ SourcesValid qb := by
 constructor
 ·intro h
  exact ⟨fun g hg => h g (List.mem_append_left _ hg),fun g hg => h g (List.mem_append_right _ hg)⟩
 ·rintro ⟨hp,ht⟩ g hg
  rcases List.mem_append.mp hg with hg | hg
  ·exact hp g hg
  ·exact ht g hg
lemma normalized_sourcesValid (pre : List (Bool × Nat × Nat)) (h u : Nat)
  (qb : List (Bool × Nat × Nat))
  (hs : SourcesValid (pre ++ (false,h,u) :: qb)) :
  SourcesValid (normalized 11 pre h u qb 24) := by
 have hp := (sourcesValid_append pre _).mp hs
 have hh := hp.2 (false,h,u) List.mem_cons_self
 have ht : SourcesValid qb := fun g hg => hp.2 g (List.mem_cons_of_mem _ hg)
 unfold normalized
 apply (sourcesValid_append _ _).mpr
 refine ⟨hp.1, (sourcesValid_append _ _).mpr ⟨?_,?_⟩⟩
 ·intro g hg
  change g ∈ qb.map (fun g => (g.1,rho (11+pre.length) u g.2.1,rho (11+pre.length) u g.2.2)) at hg
  obtain ⟨g0,hg0,rfl⟩ := List.mem_map.mp hg
  exact ⟨rho_validSource (by omega) hh.2 (ht g0 hg0).1,
   rho_validSource (by omega) hh.2 (ht g0 hg0).2⟩
 ·intro g hg
  simp only [List.mem_singleton] at hg
  subst g
  exact ⟨hh.1,rho_validSource (by omega) hh.2 (Or.inr (by decide))⟩
lemma normalized_dirtyPair (pre : List (Bool × Nat × Nat)) (h u : Nat)
  (qb : List (Bool × Nat × Nat))
  (hc : CausalFrom 11 (pre ++ (false,h,u) :: qb))
  (hd : DirtyPair (pre ++ (false,h,u) :: qb))
  (hq : run 11 pre initialValues h &&& 36671 = run 11 pre initialValues h) :
  DirtyPair (normalized 11 pre h u qb 24) := by
 obtain ⟨i,hi,j,hj,hne,hopi,hopj,⟨ki,hki⟩,⟨kj,hkj⟩⟩ := hd
 have hbi := normalized_and_index 11 pre h u qb 24 i hi hopi
 have hbj := normalized_and_index 11 pre h u qb 24 j hj hopj
 refine ⟨gateShift pre.length i,?_,gateShift pre.length j,?_,?_,hbi.2.1,hbj.2.1,?_,?_⟩
 ·simp only [normalized,List.length_append,rename,List.length_map,List.length_singleton]
  omega
 ·simp only [normalized,List.length_append,rename,List.length_map,List.length_singleton]
  omega
 ·intro heq
  exact hne (gateShift_injective_away (and_index_ne pre qb h u i hopi)
   (and_index_ne pre qb h u j hopj) heq)
 ·refine ⟨ki,?_⟩
  have he := (normalized_and_false_bit 11 pre h u qb 24 36671 (16+ki.val) i initialValues
   hc hq (target_high_bit ki) hi hopi).2.2
  exact he ▸ hki
 ·refine ⟨kj,?_⟩
  have he := (normalized_and_false_bit 11 pre h u qb 24 36671 (16+kj.val) j initialValues
   hc hq (target_high_bit kj) hj hopj).2.2
  exact he ▸ hkj
lemma normalized_good (pre : List (Bool × Nat × Nat)) (h u : Nat)
  (qb : List (Bool × Nat × Nat))
  (hg : Good (pre ++ (false,h,u) :: qb))
  (hq : run 11 pre initialValues h &&& 36671 = run 11 pre initialValues h) :
  Good (normalized 11 pre h u qb 24) := by
 obtain ⟨qe,hc,hs,ql,hd⟩ := hg
 have vt : 24 < 11 + (pre ++ (false,h,u) :: qb).length := by omega
 refine ⟨(normalized_length 11 pre h u qb 24).trans qe,
  normalized_causal 11 pre h u qb 24 hc vt,
  normalized_sourcesValid pre h u qb hs,?_, normalized_dirtyPair pre h u qb hc hd hq⟩
 have he := normalized_output 11 pre h u qb 24 36671 initialValues hc vt ql hq
 have wO : 11+pre.length+qb.length=24 := by
  simp only [List.length_append,List.length_cons] at qe
  omega
 rwa [wO] at he
def negativeMask : Nat := 1099511591104
def Cost (gs : List (Bool × Nat × Nat)) : Nat := orCost negativeMask 11 gs initialValues
def Minimal (gs : List (Bool × Nat × Nat)) : Prop :=
 Good gs ∧ ∀ hs, Good hs → Cost gs ≤ Cost hs
lemma exists_minimal_good (hex : ∃ gs, Good gs) : ∃ gs, Minimal gs := by
 classical
 have uq : ∃ n : Nat, ∃ gs, Good gs ∧ Cost gs = n := by
  obtain ⟨gs,hg⟩ := hex
  exact ⟨Cost gs,gs,hg,rfl⟩
 obtain ⟨gs,hg,hcost⟩ := Nat.find_spec uq
 refine ⟨gs,hg,?_⟩
 intro hs hh
 have he := Nat.find_min' uq (show ∃ gs, Good gs ∧ Cost gs = Cost hs from ⟨hs,hh,rfl⟩)
 rwa [← hcost] at he
lemma minimal_no_clean_left (pre : List (Bool × Nat × Nat)) (h u : Nat)
  (qb : List (Bool × Nat × Nat))
  (hm : Minimal (pre ++ (false,h,u) :: qb))
  (hq : run 11 pre initialValues h &&& 36671 = run 11 pre initialValues h) :
  run 11 (pre ++ (false,h,u) :: qb) initialValues (11+pre.length) &&& negativeMask = 0 := by
 by_contra hn
 have hg := normalized_good pre h u qb hm.1 hq
 have hle := hm.2 _ hg
 have hs := normalized_orCost_strict negativeMask 11 pre h u qb 24 36671 initialValues hm.1.2.1
  (by have := hm.1.1; omega) hm.1.2.2.2.1 hq (by decide) hn
 change Cost (normalized 11 pre h u qb 24) < Cost (pre ++ (false,h,u) :: qb) at hs
 omega
lemma sourcesValid_cons (g : Bool × Nat × Nat) (gs : List (Bool × Nat × Nat)) :
  SourcesValid (g::gs) ↔ ValidSource g.2.1 ∧ ValidSource g.2.2 ∧ SourcesValid gs := by
 constructor
 ·intro h
  exact ⟨(h g List.mem_cons_self).1,(h g List.mem_cons_self).2,
   fun x hx => h x (List.mem_cons_of_mem _ hx)⟩
 ·rintro ⟨ha,hb,ht⟩ x hx
  rcases List.mem_cons.mp hx with rfl | hx
  ·exact ⟨ha,hb⟩
  ·exact ht x hx
lemma swap_or_sourcesValid (pre : List (Bool × Nat × Nat)) (h u : Nat)
  (qb : List (Bool × Nat × Nat)) :
  SourcesValid (pre++(false,h,u)::qb) ↔ SourcesValid (pre++(false,u,h)::qb) := by
 rw [sourcesValid_append,sourcesValid_append,sourcesValid_cons,sourcesValid_cons]
 tauto
lemma swap_or_dirtyPair (pre : List (Bool × Nat × Nat)) (h u : Nat)
  (qb : List (Bool × Nat × Nat)) (hd : DirtyPair (pre++(false,h,u)::qb)) :
  DirtyPair (pre++(false,u,h)::qb) := by
 obtain ⟨i,hi,j,hj,hne,hoi,hoj,⟨ki,hki⟩,⟨kj,hkj⟩⟩ := hd
 have hv := swap_or_run 11 pre h u qb initialValues
 refine ⟨i,by simpa using hi,j,by simpa using hj,hne,?_,?_,⟨ki,?_⟩,⟨kj,?_⟩⟩
 ·exact (swap_or_opAt pre h u qb i).symm.trans hoi
 ·exact (swap_or_opAt pre h u qb j).symm.trans hoj
 ·simpa only [hv] using hki
 ·simpa only [hv] using hkj
lemma swap_or_good (pre : List (Bool × Nat × Nat)) (h u : Nat)
  (qb : List (Bool × Nat × Nat)) (hg : Good (pre++(false,h,u)::qb)) :
  Good (pre++(false,u,h)::qb) := by
 obtain ⟨hl,hc,hs,ho,hd⟩ := hg
 exact ⟨by simpa using hl,(swap_or_causal 11 pre h u qb).mp hc,
  (swap_or_sourcesValid pre h u qb).mp hs,
  by simpa only [swap_or_run 11 pre h u qb initialValues] using ho,
  swap_or_dirtyPair pre h u qb hd⟩
lemma swap_or_minimal (pre : List (Bool × Nat × Nat)) (h u : Nat)
  (qb : List (Bool × Nat × Nat)) (hm : Minimal (pre++(false,h,u)::qb)) :
  Minimal (pre++(false,u,h)::qb) := by
 refine ⟨swap_or_good pre h u qb hm.1,?_⟩
 intro gs hg
 have he := swap_orCost negativeMask 11 pre h u qb initialValues
 change Cost (pre++(false,h,u)::qb) = Cost (pre++(false,u,h)::qb) at he
 rw [←he]
 exact hm.2 gs hg
lemma initial_mask_closed : ∀ j, initialValues j &&& 1099511627775 = initialValues j := by
 intro j
 by_cases hj : j<11
 ·have hf : ∀ j : Fin 11, initialValues j.val &&& 1099511627775 = initialValues j.val := by decide +kernel
  exact hf ⟨j,hj⟩
 ·simp only [initialValues]
  rw [List.getD_eq_default _ _ (by change 11 ≤ j; omega)]
  simp
lemma run_clean_iff (gs : List (Bool × Nat × Nat)) (j : Nat) :
  run 11 gs initialValues j &&& negativeMask = 0 ↔
  run 11 gs initialValues j &&& 36671 = run 11 gs initialValues j := by
 exact masked_clean_iff _ 36671 negativeMask 1099511627775
  (run_mask_closed 1099511627775 11 gs initialValues initial_mask_closed j) (by decide) (by decide)
lemma minimal_or_clean_left (pre : List (Bool × Nat × Nat)) (h u : Nat)
  (qb : List (Bool × Nat × Nat))
  (hm : Minimal (pre++(false,h,u)::qb))
  (hq : run 11 pre initialValues h &&& 36671 = run 11 pre initialValues h) :
  run 11 (pre++(false,h,u)::qb) initialValues (11+pre.length) &&& 36671 =
   run 11 (pre++(false,h,u)::qb) initialValues (11+pre.length) :=
 (run_clean_iff _ _).mp (minimal_no_clean_left pre h u qb hm hq)
lemma minimal_or_clean_right (pre : List (Bool × Nat × Nat)) (h u : Nat)
  (qb : List (Bool × Nat × Nat))
  (hm : Minimal (pre++(false,h,u)::qb))
  (hq : run 11 pre initialValues u &&& 36671 = run 11 pre initialValues u) :
  run 11 (pre++(false,h,u)::qb) initialValues (11+pre.length) &&& 36671 =
   run 11 (pre++(false,h,u)::qb) initialValues (11+pre.length) := by
 have he := minimal_or_clean_left pre u h qb (swap_or_minimal pre h u qb hm) hq
 simpa only [←swap_or_run 11 pre h u qb initialValues] using he
lemma run_prefix_source (pre : List (Bool × Nat × Nat)) (g : Bool × Nat × Nat)
  (qb : List (Bool × Nat × Nat)) (j : Nat) (hj : j < 11+pre.length) :
  run 11 (pre++g::qb) initialValues j = run 11 pre initialValues j := by
 rw [run_append]
 exact run_preserves_below _ _ _ _ hj
lemma minimal_no_clean_to_dirty (pre : List (Bool × Nat × Nat)) (h u : Nat)
  (qb : List (Bool × Nat × Nat))
  (hm : Minimal (pre++(false,h,u)::qb))
  (hq : (run 11 (pre++(false,h,u)::qb) initialValues h &&& 36671 =
    run 11 (pre++(false,h,u)::qb) initialValues h) ∨
   (run 11 (pre++(false,h,u)::qb) initialValues u &&& 36671 =
    run 11 (pre++(false,h,u)::qb) initialValues u)) :
  run 11 (pre++(false,h,u)::qb) initialValues (11+pre.length) &&& 36671 =
   run 11 (pre++(false,h,u)::qb) initialValues (11+pre.length) := by
 have hc := (causal_append pre _ 11).mp hm.1.2.1
 rcases hq with hh | hu
 ·rw [run_prefix_source pre (false,h,u) qb h hc.2.1] at hh
  exact minimal_or_clean_left pre h u qb hm hh
 ·rw [run_prefix_source pre (false,h,u) qb u hc.2.2.1] at hu
  exact minimal_or_clean_right pre h u qb hm hu
lemma causal_iff_get (gs : List (Bool × Nat × Nat)) (n : ℕ) :
  CausalFrom n gs ↔ ∀ i : Fin gs.length,
   (gs.get i).2.1 < n + i.val ∧ (gs.get i).2.2 < n + i.val := by
 induction gs generalizing n with
 | nil => simp [CausalFrom]
 | cons g gs ih =>
  rcases g with ⟨op, a, b⟩
  constructor
  ·rintro ⟨ha, hb, ht⟩ i
   refine Fin.cases ?_ (fun j => ?_) i
   ·simpa using And.intro ha hb
   ·have h := (ih (n + 1)).mp ht j
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  ·intro h
   have h0 := h 0
   refine ⟨by simpa using h0.1, by simpa using h0.2, (ih (n + 1)).mpr ?_⟩
   intro j
   have ht := h j.succ
   simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht
lemma causal_get (gs : List (Bool × Nat × Nat)) (n : ℕ) (hc : CausalFrom n gs)
  (i : Fin gs.length) :
  (gs.get i).2.1 < n + i.val ∧ (gs.get i).2.2 < n + i.val :=
 (causal_iff_get gs n).mp hc i
lemma opAt_get (gs : List (Bool × Nat × Nat)) (i : Fin gs.length) :
  opAt gs i.val = (gs.get i).1 := by
 induction gs with
 | nil => exact Fin.elim0 i
 | cons g gs ih =>
  refine Fin.cases ?_ (fun j => ?_) i
  ·rfl
  ·exact ih j
lemma run_gate_equations (gs : List (Bool × Nat × Nat)) (n : ℕ)
  (w : ℕ → ℕ) (hc : CausalFrom n gs) (i : Fin gs.length) :
  run n gs w (n + i.val) = gateValue (gs.get i).1
   (run n gs w (gs.get i).2.1) (run n gs w (gs.get i).2.2) := by
 induction gs generalizing n w with
 | nil => exact Fin.elim0 i
 | cons g gs ih =>
  rcases g with ⟨op, a, b⟩
  obtain ⟨ha, hb, ht⟩ := hc
  refine Fin.cases ?_ (fun j => ?_) i
  ·change run (n + 1) gs (Function.update w n (gateValue op (w a) (w b))) n =
    gateValue op (run n ((op,a,b)::gs) w a) (run n ((op,a,b)::gs) w b)
   rw [run_preserves_below _ n a w ha, run_preserves_below _ n b w hb,
    run_preserves_below gs (n + 1) n _ (by omega), Function.update_self]
  ·have h := ih (n + 1) (Function.update w n (gateValue op (w a) (w b))) ht j
   simpa [run, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
lemma run_eq_given (gs : List (Bool × Nat × Nat)) (n : ℕ)
  (w v : ℕ → ℕ) (hc : CausalFrom n gs)
  (qi : ∀ j < n, w j = v j)
  (heq : ∀ i : Fin gs.length, v (n + i.val) =
   gateValue (gs.get i).1 (v (gs.get i).2.1) (v (gs.get i).2.2)) :
  ∀ j < n + gs.length, run n gs w j = v j := by
 induction gs generalizing n w with
 | nil => simpa [run] using qi
 | cons g gs ih =>
  rcases g with ⟨op, a, b⟩
  obtain ⟨ha, hb, ht⟩ := hc
  have h0 : v n = gateValue op (v a) (v b) := by simpa using heq 0
  have hz : gateValue op (w a) (w b) = v n := by
   rw [qi a ha, qi b hb]
   exact h0.symm
  have wy : ∀ j < n + 1,
    Function.update w n (gateValue op (w a) (w b)) j = v j := by
   intro j hj
   by_cases he : j = n
   ·subst j
    simpa using hz
   ·rw [Function.update_of_ne he]
    exact qi j (by omega)
  have wJ : ∀ i : Fin gs.length, v (n + 1 + i.val) =
    gateValue (gs.get i).1 (v (gs.get i).2.1) (v (gs.get i).2.2) := by
   intro i
   have h := heq i.succ
   simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  intro j hj
  have h := ih (n + 1) (Function.update w n (gateValue op (w a) (w b))) ht wy wJ j
   (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hj)
  exact h
def indexedList {n : ℕ} (ops : Fin n → Bool) (a b : Fin n → Fin 33) : List (Bool × Nat × Nat) :=
 List.ofFn (fun i => (ops i, (a i).val, (b i).val))
lemma indexedList_get {n : ℕ} (ops : Fin n → Bool) (a b : Fin n → Fin 33)
  (i : Fin (indexedList ops a b).length) :
  (indexedList ops a b).get i =
   (ops ⟨i.val, by simpa [indexedList] using i.isLt⟩,
    (a ⟨i.val, by simpa [indexedList] using i.isLt⟩).val,
    (b ⟨i.val, by simpa [indexedList] using i.isLt⟩).val) := by
 have hi : i.val < n := by simpa [indexedList] using i.isLt
 have hf : i.val < (List.ofFn (fun j => (ops j, (a j).val, (b j).val))).length := by
  simpa only [List.length_ofFn] using hi
 change (List.ofFn (fun j => (ops j, (a j).val, (b j).val)))[i.val]'hf = _
 rw [List.getElem_ofFn]
lemma indexedList_opAt {n : ℕ} (ops : Fin n → Bool) (a b : Fin n → Fin 33) (i : Fin n) :
  opAt (indexedList ops a b) i.val = ops i := by
 have hi : i.val < (indexedList ops a b).length := by simpa [indexedList] using i.isLt
 rw [opAt_get _ ⟨i.val, hi⟩]
 simp [indexedList]
def IndexedDirty (ops : Fin 14 → Bool) (v : ℕ → ℕ) : Prop :=
 ∃ i j : Fin 14, i ≠ j ∧ ops i = true ∧ ops j = true ∧
  (∃ k : Fin 24, (v (11 + i.val)).testBit (16 + k.val) = true) ∧
  (∃ k : Fin 24, (v (11 + j.val)).testBit (16 + k.val) = true)
def IndexedWitness (ops : Fin 14 → Bool) (a b : Fin 14 → Fin 33) (v : ℕ → ℕ) : Prop :=
 (∀ i : Fin 11, v i.val = baseValues.getD i.val 0) ∧
 (∀ i, (a i).val ∈ allowedInputs ∨ 11 ≤ (a i).val) ∧
 (∀ i, (b i).val ∈ allowedInputs ∨ 11 ≤ (b i).val) ∧
 (∀ i, (a i).val < 11 + i.val ∧ (b i).val < 11 + i.val ∧
  v (11 + i.val) = if ops i then v (a i).val &&& v (b i).val else v (a i).val ||| v (b i).val) ∧
 v 24 = 36671 ∧ IndexedDirty ops v
lemma indexedWitness_good (ops : Fin 14 → Bool) (a b : Fin 14 → Fin 33) (v : ℕ → ℕ)
  (hw : IndexedWitness ops a b v) : Good (indexedList ops a b) := by
 obtain ⟨qi, ha, hb, hs, ql, hd⟩ := hw
 have hc : CausalFrom 11 (indexedList ops a b) := by
  apply (causal_iff_get _ _).mpr
  intro i
  have hi : i.val < 14 := by simpa [indexedList] using i.isLt
  have h := hs ⟨i.val, hi⟩
  rw [indexedList_get]
  exact And.intro h.1 h.2.1
 have hv : SourcesValid (indexedList ops a b) := by
  intro g hg
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
  exact ⟨ha i, hb i⟩
 have qj : ∀ j < 25, run 11 (indexedList ops a b) initialValues j = v j := by
  have h := run_eq_given (indexedList ops a b) 11 initialValues v hc ?_ ?_
  ·simpa [indexedList] using h
  ·intro j hj
   exact (qi ⟨j, hj⟩).symm
  ·intro i
   have hi : i.val < 14 := by simpa [indexedList] using i.isLt
   have h := (hs ⟨i.val, hi⟩).2.2
   rw [indexedList_get]
   exact h
 refine ⟨by simp [indexedList], hc, hv, (qj 24 (by decide)).trans ql, ?_⟩
 obtain ⟨i, j, hne, hip, hjp, ⟨ki, hki⟩, ⟨kj, hkj⟩⟩ := hd
 refine ⟨i.val, by simpa [indexedList] using i.isLt,
  j.val, by simpa [indexedList] using j.isLt,
  (fun h => hne (Fin.ext h)), ?_, ?_, ?_, ?_⟩
 ·simpa only [indexedList_opAt] using hip
 ·simpa only [indexedList_opAt] using hjp
 ·refine ⟨ki, ?_⟩
  rw [qj (11 + i.val) (by have := i.isLt; omega)]
  exact hki
 ·refine ⟨kj, ?_⟩
  rw [qj (11 + j.val) (by have := j.isLt; omega)]
  exact hkj
lemma good_indexed_witness (ops : Fin 14 → Bool) (a b : Fin 14 → Fin 33)
  (hg : Good (indexedList ops a b)) : ∃ v : ℕ → ℕ, IndexedWitness ops a b v := by
 obtain ⟨qe, hc, hv, ql, hd⟩ := hg
 let v : ℕ → ℕ := run 11 (indexedList ops a b) initialValues
 refine ⟨v, ?_, ?_, ?_, ?_, ql, ?_⟩
 ·intro i
  change run 11 (indexedList ops a b) initialValues i.val = _
  rw [run_preserves_below _ 11 i.val _ i.isLt]
  rfl
 ·intro i
  have hi : (ops i, (a i).val, (b i).val) ∈ indexedList ops a b := List.mem_ofFn.mpr ⟨i, rfl⟩
  exact (hv _ hi).1
 ·intro i
  have hi : (ops i, (a i).val, (b i).val) ∈ indexedList ops a b := List.mem_ofFn.mpr ⟨i, rfl⟩
  exact (hv _ hi).2
 ·intro i
  let j : Fin (indexedList ops a b).length := ⟨i.val, by simpa [indexedList] using i.isLt⟩
  have hcb := causal_get (indexedList ops a b) 11 hc j
  have he := run_gate_equations (indexedList ops a b) 11 initialValues hc j
  refine ⟨?_, ?_, ?_⟩
  ·simpa only [indexedList, List.get_eq_getElem, List.getElem_ofFn, j] using hcb.1
  ·simpa only [indexedList, List.get_eq_getElem, List.getElem_ofFn, j] using hcb.2
  ·simpa only [indexedList, List.get_eq_getElem, List.getElem_ofFn, j, v, gateValue] using he
 ·obtain ⟨i, hi, j, hj, hne, hip, hjp, ⟨ki, hki⟩, ⟨kj, hkj⟩⟩ := hd
  let ii : Fin 14 := ⟨i, by simpa [indexedList] using hi⟩
  let jj : Fin 14 := ⟨j, by simpa [indexedList] using hj⟩
  refine ⟨ii, jj, ?_, ?_, ?_, ?_, ?_⟩
  ·exact fun h => hne (congrArg Fin.val h)
  ·have h : opAt (indexedList ops a b) ii.val = true := hip
   simpa only [indexedList_opAt] using h
  ·have h : opAt (indexedList ops a b) jj.val = true := hjp
   simpa only [indexedList_opAt] using h
  ·exact ⟨ki, hki⟩
  ·exact ⟨kj, hkj⟩
lemma good_indexed_iff (ops : Fin 14 → Bool) (a b : Fin 14 → Fin 33) :
  Good (indexedList ops a b) ↔ ∃ v : ℕ → ℕ, IndexedWitness ops a b v := by
 constructor
 ·exact good_indexed_witness ops a b
 ·rintro ⟨v, hv⟩
  exact indexedWitness_good ops a b v hv
lemma good_iff_indexedWitness (gs : List (Bool × Nat × Nat)) :
  Good gs ↔ ∃ (ops : Fin 14 → Bool) (a b : Fin 14 → Fin 33) (v : ℕ → ℕ),
   indexedList ops a b = gs ∧ IndexedWitness ops a b v := by
 constructor
 ·intro hg
  let ix (i : Fin 14) : Fin gs.length := ⟨i.val, by rw [hg.1]; exact i.isLt⟩
  let ops (i : Fin 14) : Bool := (gs.get (ix i)).1
  have ha (i : Fin 14) : (gs.get (ix i)).2.1 < 33 := by
   have h := causal_get gs 11 hg.2.1 (ix i)
   change (gs.get (ix i)).2.1 < 11 + i.val ∧ (gs.get (ix i)).2.2 < 11 + i.val at h
   have hi := i.isLt
   omega
  have hb (i : Fin 14) : (gs.get (ix i)).2.2 < 33 := by
   have h := causal_get gs 11 hg.2.1 (ix i)
   change (gs.get (ix i)).2.1 < 11 + i.val ∧ (gs.get (ix i)).2.2 < 11 + i.val at h
   have hi := i.isLt
   omega
  let a (i : Fin 14) : Fin 33 := ⟨(gs.get (ix i)).2.1, ha i⟩
  let b (i : Fin 14) : Fin 33 := ⟨(gs.get (ix i)).2.2, hb i⟩
  have heq : indexedList ops a b = gs := by
   apply List.ext_getElem
   ·simp [indexedList, hg.1]
   ·intro i hi hj
    simp only [indexedList, List.getElem_ofFn, ops, a, b, ix, List.get_eq_getElem, Prod.eta]
  have xO : Good (indexedList ops a b) := by rw [heq]; exact hg
  obtain ⟨v, hv⟩ := good_indexed_witness ops a b xO
  exact ⟨ops, a, b, v, heq, hv⟩
 ·rintro ⟨ops, a, b, v, rfl, hv⟩
  exact indexedWitness_good ops a b v hv
lemma indexedDirty_iff_card (ops : Fin 14 → Bool) (v : ℕ → ℕ) :
  IndexedDirty ops v ↔ 2 ≤ Nat.card {i : Fin 14 // ops i = true ∧
   ∃ k : Fin 24, (v (11 + i.val)).testBit (16 + k.val) = true} := by
 classical
 rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
 rw [show (2 : ℕ) = Nat.succ 1 by rfl, Nat.succ_le_iff, Finset.one_lt_card]
 simp only [Finset.mem_filter, Finset.mem_univ, true_and]
 constructor
 ·rintro ⟨i, j, hne, hi, hj, di, dj⟩
  exact ⟨i, ⟨hi, di⟩, j, ⟨hj, dj⟩, hne⟩
 ·rintro ⟨i, ⟨hi, di⟩, j, ⟨hj, dj⟩, hne⟩
  exact ⟨i, j, hne, hi, hj, di, dj⟩
lemma minimal_no_clean_index (gs : List (Bool × Nat × Nat)) (hm : Minimal gs)
  (i : Fin gs.length) (hop : (gs.get i).1 = false)
  (zq : (run 11 gs initialValues (gs.get i).2.1 &&& 36671 =
    run 11 gs initialValues (gs.get i).2.1) ∨
   (run 11 gs initialValues (gs.get i).2.2 &&& 36671 =
    run 11 gs initialValues (gs.get i).2.2)) :
  run 11 gs initialValues (11 + i.val) &&& 36671 =
   run 11 gs initialValues (11 + i.val) := by
 let pre := gs.take i.val
 let qb := gs.drop (i.val + 1)
 have hg : gs.get i = (false, (gs.get i).2.1, (gs.get i).2.2) := Prod.ext hop rfl
 have xD : pre ++ (false, (gs.get i).2.1, (gs.get i).2.2) :: qb = gs := by
  have h := List.take_append_drop i.val gs
  rw [List.drop_eq_getElem_cons i.isLt] at h
  change pre ++ gs.get i :: qb = gs at h
  rw [hg] at h
  exact h
 have hm' : Minimal (pre ++ (false, (gs.get i).2.1, (gs.get i).2.2) :: qb) := by
  rw [xD]
  exact hm
 have hq : (run 11 (pre ++ (false, (gs.get i).2.1, (gs.get i).2.2) :: qb)
    initialValues (gs.get i).2.1 &&& 36671 =
   run 11 (pre ++ (false, (gs.get i).2.1, (gs.get i).2.2) :: qb)
    initialValues (gs.get i).2.1) ∨
  (run 11 (pre ++ (false, (gs.get i).2.1, (gs.get i).2.2) :: qb)
    initialValues (gs.get i).2.2 &&& 36671 =
   run 11 (pre ++ (false, (gs.get i).2.1, (gs.get i).2.2) :: qb)
    initialValues (gs.get i).2.2) := by
  simpa only [xD] using zq
 have h := minimal_no_clean_to_dirty pre (gs.get i).2.1 (gs.get i).2.2 qb hm' hq
 have qe : pre.length = i.val := by
  simp only [pre, List.length_take, Nat.min_eq_left (Nat.le_of_lt i.isLt)]
 simpa only [xD, qe] using h
lemma indexedWitness_run_eq (ops : Fin 14 → Bool) (a b : Fin 14 → Fin 33)
  (v : ℕ → ℕ) (hw : IndexedWitness ops a b v) :
  ∀ j < 25, run 11 (indexedList ops a b) initialValues j = v j := by
 have hc := (indexedWitness_good ops a b v hw).2.1
 have h := run_eq_given (indexedList ops a b) 11 initialValues v hc ?_ ?_
 ·have qe : (indexedList ops a b).length = 14 := by simp only [indexedList, List.length_ofFn]
  simpa only [qe] using h
 ·intro j hj
  exact (hw.1 ⟨j, hj⟩).symm
 ·intro i
  rw [indexedList_get]
  exact (hw.2.2.2.1 ⟨i.val, by simpa only [indexedList, List.length_ofFn] using i.isLt⟩).2.2
lemma exists_indexed_normal_of_good (hex : ∃ gs, Good gs) :
  ∃ (ops : Fin 14 → Bool) (a b : Fin 14 → Fin 33) (v : ℕ → ℕ),
   IndexedWitness ops a b v ∧
   ∀ i, ops i = false →
    ((v (a i).val &&& 36671 = v (a i).val) ∨
     (v (b i).val &&& 36671 = v (b i).val)) →
    v (11 + i.val) &&& 36671 = v (11 + i.val) := by
 obtain ⟨gs, hm⟩ := exists_minimal_good hex
 obtain ⟨ops, a, b, v, hlist, hw⟩ := (good_iff_indexedWitness gs).mp hm.1
 refine ⟨ops, a, b, v, hw, ?_⟩
 have hm' : Minimal (indexedList ops a b) := by rw [hlist]; exact hm
 have qj := indexedWitness_run_eq ops a b v hw
 intro i hop zq
 let j : Fin (indexedList ops a b).length :=
  ⟨i.val, by simpa only [indexedList, List.length_ofFn] using i.isLt⟩
 have qR : (indexedList ops a b).get j = (ops i, (a i).val, (b i).val) :=
  indexedList_get ops a b j
 have vY : ((indexedList ops a b).get j).1 = false := by rw [qR]; exact hop
 have hsa : (a i).val < 25 := by have := (hw.2.2.2.1 i).1; have := i.isLt; omega
 have hsb : (b i).val < 25 := by have := (hw.2.2.2.1 i).2.1; have := i.isLt; omega
 have hso : 11 + i.val < 25 := by have := i.isLt; omega
 have hn := minimal_no_clean_index (indexedList ops a b) hm' j vY
 rw [qR] at hn
 change ((run 11 (indexedList ops a b) initialValues (a i).val &&& 36671 =
   run 11 (indexedList ops a b) initialValues (a i).val) ∨
  (run 11 (indexedList ops a b) initialValues (b i).val &&& 36671 =
   run 11 (indexedList ops a b) initialValues (b i).val)) →
  run 11 (indexedList ops a b) initialValues (11 + i.val) &&& 36671 =
   run 11 (indexedList ops a b) initialValues (11 + i.val) at hn
 rw [qj (a i).val hsa, qj (b i).val hsb, qj (11 + i.val) hso] at hn
 exact hn zq
lemma normalize_indexed_witness (ops : Fin 14 → Bool) (a b : Fin 14 → Fin 33)
  (v : ℕ → ℕ) (hw : IndexedWitness ops a b v) :
  ∃ (uW : Fin 14 → Bool) (a' b' : Fin 14 → Fin 33) (v' : ℕ → ℕ),
   IndexedWitness uW a' b' v' ∧
   ∀ i, uW i = false →
    ((v' (a' i).val &&& 36671 = v' (a' i).val) ∨
     (v' (b' i).val &&& 36671 = v' (b' i).val)) →
    v' (11 + i.val) &&& 36671 = v' (11 + i.val) :=
 exists_indexed_normal_of_good ⟨indexedList ops a b, indexedWitness_good ops a b v hw⟩
lemma posted_witness_normalizes
  (hex : ∃ (x1 : Fin (14 : ℕ) → Bool) (x2 : Fin (14 : ℕ) → Fin (33 : ℕ)) (x3 : Fin (14 : ℕ) → Fin (33 : ℕ)) (x4 : ℕ → ℕ) (x5 : Fin (2 : ℕ) → Fin (14 : ℕ)) (x6 : Fin (2 : ℕ) → Fin (24 : ℕ)), (∀ (x7 : Fin (11 : ℕ)), x4 ↑x7 = [(2147418115 : ℕ), (663661903884 : ℕ), (34144976944 : ℕ), (728266375360 : ℕ), (21653750532 : ℕ), (103293914128 : ℕ), (26322415680 : ℕ), (344922804352 : ℕ), (414195942664 : ℕ), (581968119809 : ℕ), (1065151898146 : ℕ)].getD ↑x7 (0 : ℕ)) ∧ (∀ (x7 : Fin (14 : ℕ)), ↑(x2 x7) ∈ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (4 : ℕ), (5 : ℕ), (8 : ℕ), (9 : ℕ), (10 : ℕ)] ∨ (11 : ℕ) ≤ ↑(x2 x7)) ∧ (∀ (x7 : Fin (14 : ℕ)), ↑(x3 x7) ∈ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (4 : ℕ), (5 : ℕ), (8 : ℕ), (9 : ℕ), (10 : ℕ)] ∨ (11 : ℕ) ≤ ↑(x3 x7)) ∧ (∀ (x7 : Fin (14 : ℕ)), ↑(x2 x7) < (11 : ℕ) + ↑x7 ∧ ↑(x3 x7) < (11 : ℕ) + ↑x7 ∧ x4 ((11 : ℕ) + ↑x7) = if x1 x7 = Bool.true then x4 ↑(x2 x7) &&& x4 ↑(x3 x7) else x4 ↑(x2 x7) ||| x4 ↑(x3 x7)) ∧ x4 (24 : ℕ) = (36671 : ℕ) ∧ Function.Injective x5 ∧ ∀ (x7 : Fin (2 : ℕ)), x1 (x5 x7) = Bool.true ∧ (x4 ((11 : ℕ) + ↑(x5 x7))).testBit ((16 : ℕ) + ↑(x6 x7)) = Bool.true) :
  ∃ (ops : Fin 14 → Bool) (a b : Fin 14 → Fin 33) (v : ℕ → ℕ),
   IndexedWitness ops a b v ∧
   ∀ i, ops i = false →
    ((v (a i).val &&& 36671 = v (a i).val) ∨
     (v (b i).val &&& 36671 = v (b i).val)) →
    v (11 + i.val) &&& 36671 = v (11 + i.val) := by
 obtain ⟨ops, a, b, v, pick, bit, qi, ha, hb, qQ, ql, vj, xg⟩ := hex
 apply normalize_indexed_witness ops a b v
 refine ⟨qi, ha, hb, ?_, ql, ?_⟩
 ·intro i
  exact qQ i
 ·refine ⟨pick 0, pick 1, ?_, (xg 0).1, (xg 1).1,
   ⟨bit 0, (xg 0).2⟩, ⟨bit 1, (xg 1).2⟩⟩
  intro heq
  have vc := vj heq
  exact (by decide : (0 : Fin 2) ≠ 1) vc
end CleanMate
end PEqualNP.Outside.L_meta_9033_aux
