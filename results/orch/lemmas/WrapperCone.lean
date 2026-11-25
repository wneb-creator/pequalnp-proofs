import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2962_aux.StrictLeaf

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadK

lemma foldl_snoc_prefix {α β : Type _} (F : List α → β → α) (gs : List β) (init : List α) :
    init <+: gs.foldl (fun R g => R ++ [F R g]) init := by
  induction gs generalizing init with
  | nil => exact List.prefix_refl _
  | cons g gs ih => exact (List.prefix_append init [F init g]).trans (ih _)

lemma foldl_snoc_length {α β : Type _} (F : List α → β → α) (gs : List β) (init : List α) :
    (gs.foldl (fun R g => R ++ [F R g]) init).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp
  | cons g gs ih => simp [ih]; omega

lemma getD_of_prefix {α : Type _} {P L : List α} (h : P <+: L) {i : ℕ} (hi : i < P.length)
    (d : α) : L.getD i d = P.getD i d := by
  obtain ⟨t, rfl⟩ := h
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_snoc_init {α : Type _} (G : List α → Gate → α) (d : α) (init : List α)
    (gs : List Gate) (i : ℕ) (hi : i < init.length) :
    (gs.foldl (fun R g => R ++ [G (g.inputs.map fun i => R.getD i d) g]) init).getD i d
      = init.getD i d :=
  getD_of_prefix (foldl_snoc_prefix (fun R g => G (g.inputs.map fun i => R.getD i d) g) _ _) hi d

lemma foldl_snoc_beyond {α : Type _} (G : List α → Gate → α) (d : α) (init : List α)
    (gs : List Gate) (i : ℕ) (hi : init.length + gs.length ≤ i) :
    (gs.foldl (fun R g => R ++ [G (g.inputs.map fun i => R.getD i d) g]) init).getD i d = d := by
  apply List.getD_eq_default
  rw [foldl_snoc_length (fun R g => G (g.inputs.map fun i => R.getD i d) g)]
  exact hi

lemma foldl_snoc_gate {α : Type _} (G : List α → Gate → α) (d : α) (init : List α)
    (gs : List Gate) (j : ℕ) (hj : j < gs.length)
    (hrb : ∀ i ∈ gs[j].inputs, i < init.length + j) :
    (gs.foldl (fun R g => R ++ [G (g.inputs.map fun i => R.getD i d) g]) init).getD
        (init.length + j) d
      = G (gs[j].inputs.map fun i =>
          (gs.foldl (fun R g => R ++ [G (g.inputs.map fun i => R.getD i d) g]) init).getD i d)
          gs[j] := by
  have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by simp
  set P := (gs.take j).foldl (fun R g => R ++ [G (g.inputs.map fun i => R.getD i d) g]) init
    with hP
  have hPl : P.length = init.length + j := by
    rw [hP, foldl_snoc_length (fun R g => G (g.inputs.map fun i => R.getD i d) g)]
    simp; omega
  have hpre : (P ++ [G (gs[j].inputs.map fun i => P.getD i d) gs[j]]) <+:
      gs.foldl (fun R g => R ++ [G (g.inputs.map fun i => R.getD i d) g]) init := by
    conv_rhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
    exact foldl_snoc_prefix (fun R g => G (g.inputs.map fun i => R.getD i d) g) _ _
  have hpre2 := (List.prefix_append P _).trans hpre
  rw [getD_of_prefix hpre (by simp; omega)]
  have e1 : (P ++ [G (gs[j].inputs.map fun i => P.getD i d) gs[j]]).getD (init.length + j) d
      = G (gs[j].inputs.map fun i => P.getD i d) gs[j] := by
    rw [← hPl]; simp
  rw [e1]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [getD_of_prefix hpre2 (by rw [hPl]; exact hrb i hi)]




def rvG (S : List ℕ) (k : ℕ) (ins : List (List (List ℕ))) (g : Gate) : List (List ℕ) :=
  match g.op with
  | GateOp.or => ins.foldl (fun acc A => A.foldl insertNew acc) []
  | GateOp.and => ins.foldl (andStep k) [S.map fun _ => 0]
  | _ => []

lemma rv_eq (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) :
    readVectors C n S k = C.gates.foldl
      (fun R g => R ++ [rvG S k (g.inputs.map fun i => R.getD i []) g])
      ((List.range n).map (leafVectors S k)) := rfl

lemma wires_eq (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl
      (fun R g => R ++ [(fun ins (g : Gate) => g.op.eval ins) (g.inputs.map fun i => R.getD i false) g])
      x := rfl

lemma gateAt_eq (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]


section Wires
variable (C : Circuit) (n : ℕ)
abbrev W (x : Fin n → Bool) (i : ℕ) : Bool := (C.wires (List.ofFn x)).getD i false

lemma W_input (x : Fin n → Bool) (i : ℕ) (hi : i < n) : W C n x i = x ⟨i, hi⟩ := by
  unfold W
  rw [wires_eq, foldl_snoc_init (fun ins (g : Gate) => g.op.eval ins) false _ _ _ (by simpa using hi)]
  simp [List.getD_eq_getElem?_getD, hi]

lemma W_gate (x : Fin n → Bool) (j : ℕ) (hj : j < C.gates.length)
    (hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j) :
    W C n x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (W C n x)) := by
  unfold W
  rw [gateAt_eq C j hj] at hrb ⊢
  have := foldl_snoc_gate (fun ins (g : Gate) => g.op.eval ins) false (List.ofFn x) C.gates j hj
    (by simpa using hrb)
  simp only [List.length_ofFn] at this
  rw [wires_eq, this]

end Wires

lemma mem_insertNew {B : List (List ℕ)} {v a : List ℕ} :
    v ∈ insertNew B a ↔ v ∈ B ∨ v = a := by
  unfold insertNew
  split_ifs with h
  · constructor
    · exact Or.inl
    · rintro (h' | rfl) <;> assumption
  · simp

lemma mem_foldl_insertNew (l acc : List (List ℕ)) (v : List ℕ) :
    v ∈ l.foldl insertNew acc ↔ v ∈ acc ∨ v ∈ l := by
  induction l generalizing acc with
  | nil => simp
  | cons a l ih => rw [List.foldl_cons, ih, mem_insertNew]; simp; tauto

lemma mem_orFold (ins : List (List (List ℕ))) (acc : List (List ℕ)) (v : List ℕ) :
    v ∈ ins.foldl (fun acc A => A.foldl insertNew acc) acc ↔ v ∈ acc ∨ ∃ B ∈ ins, v ∈ B := by
  induction ins generalizing acc with
  | nil => simp
  | cons B ins ih => rw [List.foldl_cons, ih, mem_foldl_insertNew]; simp; tauto

lemma mem_andStep (k : ℕ) (P Q : List (List ℕ)) (v : List ℕ) :
    v ∈ andStep k P Q ↔ ∃ a ∈ P, ∃ b ∈ Q, v = capAdd k a b := by
  unfold andStep
  rw [mem_foldl_insertNew]
  simp only [List.not_mem_nil, false_or, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨a, ha, b, hb, rfl⟩


section Basic

variable (n : ℕ) (C : Circuit)


def Step (a b : ℕ) : Prop := ∃ g < C.gates.length, a = n + g ∧ b ∈ (gateAt C g).inputs


abbrev Reach : ℕ → ℕ → Prop := Relation.ReflTransGen (Step n C)

lemma foldl_snoc_split {α β : Type _} (F : List α → β → α) (gs : List β) (init : List α)
    (j : ℕ) (hj : j < gs.length) (d : α) :
    (gs.foldl (fun R g => R ++ [F R g]) init).getD (init.length + j) d
      = F ((gs.take j).foldl (fun R g => R ++ [F R g]) init) gs[j] ∧
    ((gs.take j).foldl (fun R g => R ++ [F R g]) init) <+:
      gs.foldl (fun R g => R ++ [F R g]) init ∧
    ((gs.take j).foldl (fun R g => R ++ [F R g]) init).length = init.length + j := by
  have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by simp
  set P := (gs.take j).foldl (fun R g => R ++ [F R g]) init with hP
  have hPl : P.length = init.length + j := by
    rw [hP, foldl_snoc_length F]; simp; omega
  have hpre : (P ++ [F P gs[j]]) <+: gs.foldl (fun R g => R ++ [F R g]) init := by
    conv_rhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
    exact foldl_snoc_prefix F _ _
  refine ⟨?_, (List.prefix_append P _).trans hpre, hPl⟩
  rw [getD_of_prefix hpre (by simp; omega), ← hPl]
  simp


def coneF (cs : List (List ℕ)) (g : Gate) : List ℕ :=
  (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
    (fun w => (w - n) :: cs.getD (w - n) [])

lemma cones_eq : cones n C = C.gates.foldl (fun R g => R ++ [coneF n R g]) [] := rfl

lemma flatMap_congr' {α β : Type _} {l : List α} {f g : α → List β}
    (h : ∀ a ∈ l, f a = g a) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons]
    rw [h a (by simp), ih (fun b hb => h b (by simp [hb]))]

lemma cone_getD {j : ℕ} (hj : j < C.gates.length) :
    (cones n C).getD j [] = ((gateAt C j).inputs.filter
      (fun w => decide (n ≤ w ∧ w < n + j))).flatMap (fun w => (w - n) :: (cones n C).getD (w - n) []) := by
  obtain ⟨h1, h2, h3⟩ := foldl_snoc_split (coneF n) C.gates [] j hj []
  simp only [List.length_nil, zero_add] at h1 h3
  rw [← cones_eq] at h1 h2
  generalize (C.gates.take j).foldl (fun R g => R ++ [coneF n R g]) [] = P at h1 h2 h3
  rw [h1, gateAt_eq C j hj]
  unfold coneF
  rw [h3]
  apply flatMap_congr'
  intro w hw
  rw [List.mem_filter] at hw
  have : w - n < j := by simp at hw; omega
  rw [getD_of_prefix h2 (by rw [h3]; exact this)]

lemma inCone_iff (hrb : ReadsBack n C) {i j : ℕ} (hj : j < C.gates.length) :
    InCone n C i j ↔ ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ (w - n = i ∨ InCone n C i (w - n)) := by
  unfold InCone
  rw [cone_getD n C hj]
  constructor
  · intro h
    obtain ⟨w, hw, hi⟩ := List.mem_flatMap.1 h
    rw [List.mem_filter] at hw
    simp only [decide_eq_true_eq] at hw
    rcases List.mem_cons.1 hi with h' | h'
    · exact ⟨w, hw.1, hw.2.1, Or.inl h'.symm⟩
    · exact ⟨w, hw.1, hw.2.1, Or.inr h'⟩
  · rintro ⟨w, hw, hnw, h⟩
    refine List.mem_flatMap.2 ⟨w, List.mem_filter.2 ⟨hw, ?_⟩, ?_⟩
    · simp only [decide_eq_true_eq]; exact ⟨hnw, hrb j hj w hw⟩
    · rcases h with h | h
      · exact List.mem_cons.2 (Or.inl h.symm)
      · exact List.mem_cons.2 (Or.inr h)

lemma inCone_iff_trans (hrb : ReadsBack n C) (i : ℕ) :
    ∀ j, j < C.gates.length → (InCone n C i j ↔ Relation.TransGen (Step n C) (n + j) (n + i)) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro hj
  rw [inCone_iff n C hrb hj]
  constructor
  · rintro ⟨w, hw, hnw, h⟩
    have hwl : w < n + j := hrb j hj w hw
    have hst : Step n C (n + j) w := ⟨j, hj, rfl, hw⟩
    rcases h with h | h
    · have : w = n + i := by omega
      subst this
      exact Relation.TransGen.single hst
    · have hlt : w - n < j := by omega
      have := (ih (w - n) hlt (by omega)).1 h
      have hw' : n + (w - n) = w := by omega
      rw [hw'] at this
      exact Relation.TransGen.head hst this
  · intro h
    obtain ⟨c, ⟨g, hg, hjg, hc⟩, hr⟩ := Relation.TransGen.head'_iff.1 h
    have hgj : g = j := by omega
    subst hgj
    have hcl : c < n + g := hrb g hg c hc
    rcases Relation.ReflTransGen.cases_head hr with hci | ⟨d, ⟨g', hg', hcg', _⟩, hr'⟩
    · exact ⟨c, hc, by omega, Or.inl (by omega)⟩
    · refine ⟨c, hc, by omega, Or.inr ?_⟩
      have hlt : c - n < g := by omega
      refine (ih (c - n) hlt (by omega)).2 ?_
      have hcn : n + (c - n) = c := by omega
      rw [hcn]
      exact Relation.TransGen.head' ⟨g', hg', hcg', by assumption⟩ hr'

lemma mem_coneSet (hrb : ReadsBack n C) {j : ℕ} (hj : j < C.gates.length) (g : ℕ) :
    g ∈ PEqualNP.Core.coneSet n C j ↔ g < C.gates.length ∧ Reach n C (n + j) (n + g) := by
  unfold PEqualNP.Core.coneSet
  rw [Finset.mem_insert, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro (rfl | ⟨hg, hc⟩)
    · exact ⟨hj, Relation.ReflTransGen.refl⟩
    · exact ⟨hg, ((inCone_iff_trans n C hrb g j hj).1 hc).to_reflTransGen⟩
  · rintro ⟨hg, hr⟩
    rcases Relation.reflTransGen_iff_eq_or_transGen.1 hr with h | h
    · left; omega
    · right; exact ⟨hg, (inCone_iff_trans n C hrb g j hj).2 h⟩

lemma reach_le (hrb : ReadsBack n C) {a b : ℕ} (h : Reach n C a b) : b ≤ a := by
  induction h with
  | refl => exact le_refl _
  | tail _ hst ih =>
    obtain ⟨g, hg, rfl, hc⟩ := hst
    have := hrb g hg _ hc
    omega

end Basic
end PEqualNP.Outside.L_meta_2962_aux.StrictLeaf

namespace PEqualNP.Outside.L_meta_2962_aux.WrapperCone

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Core
open PEqualNP.Outside.L_meta_2962_aux.StrictLeaf

lemma gateAt_append (C : Circuit) (gs : List Gate) (o j : ℕ) (hj : j < C.gates.length) :
    gateAt { gates := C.gates ++ gs, output := o } j = gateAt C j := by
  simp [gateAt, List.getD, List.getElem?_append_left hj]

lemma step_append (n : ℕ) (C : Circuit) (gs : List Gate) (o : ℕ) {a b : ℕ}
    (h : Step n C a b) : Step n { gates := C.gates ++ gs, output := o } a b := by
  obtain ⟨g, hg, hga, hgb⟩ := h
  refine ⟨g, by simp; omega, hga, ?_⟩
  simpa only [gateAt_append C gs o g hg] using hgb

lemma reach_append (n : ℕ) (C : Circuit) (gs : List Gate) (o : ℕ) {a b : ℕ}
    (h : Reach n C a b) : Reach n { gates := C.gates ++ gs, output := o } a b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail h hs ih => exact ih.tail (step_append n C gs o hs)

lemma inCone_append_reader (n : ℕ) (C : Circuit) (gs : List Gate) (o r i : ℕ)
    (hrb : ReadsBack n { gates := C.gates ++ gs, output := o })
    (hr : r < (C.gates ++ gs).length)
    (hread : C.output ∈ (gateAt { gates := C.gates ++ gs, output := o } r).inputs)
    (hpath : Reach n C C.output (n + i)) :
    InCone n { gates := C.gates ++ gs, output := o } i r := by
  apply (inCone_iff_trans n _ hrb i r hr).2
  exact Relation.TransGen.head' ⟨r, hr, rfl, hread⟩ (reach_append n C gs o hpath)

lemma inCone_lt {n : ℕ} {C : Circuit} (hrb : ReadsBack n C) {i j : ℕ}
    (hj : j < C.gates.length) (h : InCone n C i j) : i < j := by
  obtain ⟨w, ⟨g, hg, heq, hread⟩, hpath⟩ :=
    Relation.TransGen.head'_iff.mp ((inCone_iff_trans n C hrb i j hj).mp h)
  have hgj : g = j := by omega
  subst g
  have hw := hrb j hj w hread
  have hi := reach_le n C hrb hpath
  omega

lemma maximalCores_eq_singleton_final {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {C : Circuit} (hrb : ReadsBack n C) (r : ℕ)
    (hlen : C.gates.length = r + 1) (hcore : IsCore G C r)
    (hall : ∀ i < r, InCone n C i r) : maximalCores G C = {r} := by
  ext i
  simp only [maximalCores, gatesWhere, Finset.mem_filter, Finset.mem_range,
    IsMaximalCore, Finset.mem_singleton]
  constructor
  · intro hi
    by_contra hne
    have hir : i < r := by omega
    exact hi.2.2 r hcore.1 hcore (hall i hir)
  · rintro rfl
    refine ⟨hcore.1, hcore, ?_⟩
    intro j hj _ hcone
    have hlt := inCone_lt hrb hj hcone
    omega

lemma coneSet_eq_range_final {n : ℕ} {C : Circuit} (r : ℕ)
    (hlen : C.gates.length = r + 1) (hall : ∀ i < r, InCone n C i r) :
    coneSet n C r = Finset.range C.gates.length := by
  ext i
  simp only [coneSet, Finset.mem_insert, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro (rfl | hi) <;> omega
  · intro hi
    by_cases hieq : i = r
    · exact Or.inl hieq
    · exact Or.inr ⟨hi, hall i (by omega)⟩

end PEqualNP.Outside.L_meta_2962_aux.WrapperCone
