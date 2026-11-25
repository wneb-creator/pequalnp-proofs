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


section AO

variable {n : ℕ} {C : Circuit}

lemma list_two {l : List ℕ} (h : l.length = 2) : l = [l.getD 0 0, l.getD 1 0] := by
  match l, h with
  | [a, b], _ => rfl

lemma ao_inputs (hC : IsAO2 n C) {g : ℕ} (hg : g < C.gates.length) :
    (gateAt C g).inputs = [opnd C g 0, opnd C g 1] := by
  have hl : (gateAt C g).inputs.length = 2 := by
    rw [gateAt_eq C g hg]; exact hC.2.2 _ (List.getElem_mem hg)
  exact list_two hl

lemma ao_op (hC : IsAO2 n C) {g : ℕ} (hg : g < C.gates.length) :
    (gateAt C g).op = GateOp.and ∨ (gateAt C g).op = GateOp.or := by
  rw [gateAt_eq C g hg]; exact hC.1 _ (List.getElem_mem hg)

lemma opnd_mem (hC : IsAO2 n C) {g : ℕ} (hg : g < C.gates.length) (b : Fin 2) :
    opnd C g b ∈ (gateAt C g).inputs := by
  rw [ao_inputs hC hg]; fin_cases b <;> simp

lemma opnd_lt (hC : IsAO2 n C) {g : ℕ} (hg : g < C.gates.length) (b : Fin 2) :
    opnd C g b < n + g := hC.2.1 g hg _ (opnd_mem hC hg b)

lemma step_opnd (hC : IsAO2 n C) {g : ℕ} (hg : g < C.gates.length) (b : Fin 2) :
    Step n C (n + g) (opnd C g b) := ⟨g, hg, rfl, opnd_mem hC hg b⟩

lemma step_inv (hC : IsAO2 n C) {a c : ℕ} (h : Step n C a c) :
    ∃ g < C.gates.length, a = n + g ∧ ∃ b : Fin 2, c = opnd C g b := by
  obtain ⟨g, hg, rfl, hc⟩ := h
  rw [ao_inputs hC hg] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with hc | hc
  · exact ⟨g, hg, rfl, 0, hc⟩
  · exact ⟨g, hg, rfl, 1, hc⟩

variable {j : ℕ}

lemma K_lt (hC : IsAO2 n C) (hj : j < C.gates.length) {g : ℕ}
    (hK : g ∈ PEqualNP.Core.coneSet n C j) : g < C.gates.length :=
  ((mem_coneSet n C hC.2.1 hj g).1 hK).1

lemma K_reach (hC : IsAO2 n C) (hj : j < C.gates.length) {g g' : ℕ}
    (hK : g ∈ PEqualNP.Core.coneSet n C j) (hr : Reach n C (n + g) (n + g'))
    (hg' : g' < C.gates.length) : g' ∈ PEqualNP.Core.coneSet n C j := by
  rw [mem_coneSet n C hC.2.1 hj] at hK ⊢
  exact ⟨hg', hK.2.trans hr⟩

lemma K_opnd (hC : IsAO2 n C) (hj : j < C.gates.length) {g : ℕ}
    (hK : g ∈ PEqualNP.Core.coneSet n C j) (b : Fin 2) (hge : n ≤ opnd C g b) :
    opnd C g b - n ∈ PEqualNP.Core.coneSet n C j ∧ opnd C g b - n < g := by
  have hg := K_lt hC hj hK
  have hlt := opnd_lt hC hg b
  refine ⟨K_reach hC hj hK ?_ (by omega), by omega⟩
  have : n + (opnd C g b - n) = opnd C g b := by omega
  rw [this]
  exact Relation.ReflTransGen.single (step_opnd hC hg b)

lemma K_cover (hC : IsAO2 n C) (hj : j < C.gates.length) {g : ℕ}
    (hK : g ∈ PEqualNP.Core.coneSet n C j) (hne : g ≠ j) :
    ∃ h ∈ PEqualNP.Core.coneSet n C j, ∃ b : Fin 2, opnd C h b = n + g := by
  have hr := ((mem_coneSet n C hC.2.1 hj g).1 hK).2
  rcases Relation.reflTransGen_iff_eq_or_transGen.1 hr with h | h
  · exact absurd (by omega) hne
  · obtain ⟨c, hrc, hst⟩ := Relation.TransGen.tail'_iff.1 h
    obtain ⟨h', hh', rfl, b, hb⟩ := step_inv hC hst
    refine ⟨h', ?_, b, hb.symm⟩
    rw [mem_coneSet n C hC.2.1 hj]
    exact ⟨hh', hrc⟩


def slots (n : ℕ) (C : Circuit) (j : ℕ) : Finset (ℕ × Fin 2) :=
  PEqualNP.Core.coneSet n C j ×ˢ (Finset.univ : Finset (Fin 2))


def slotW (C : Circuit) (p : ℕ × Fin 2) : ℕ := opnd C p.1 p.2


lemma below_named (hC : IsAO2 n C) (hj : j < C.gates.length) {g : ℕ}
    (hK : g ∈ PEqualNP.Core.coneSet n C j) (β : Fin 2) {z : ℕ}
    (hr : Reach n C (opnd C g β) z) (hz : z ≠ opnd C g β) :
    ∃ h ∈ PEqualNP.Core.coneSet n C j, ∃ b : Fin 2, opnd C h b = z ∧
      Reach n C (opnd C g β) (n + h) := by
  rcases Relation.reflTransGen_iff_eq_or_transGen.1 hr with h | h
  · exact absurd h hz
  · obtain ⟨c, hrc, hst⟩ := Relation.TransGen.tail'_iff.1 h
    obtain ⟨h', hh', rfl, b, hb⟩ := step_inv hC hst
    refine ⟨h', K_reach hC hj hK ?_ hh', b, hb.symm, hrc⟩
    exact Relation.ReflTransGen.head (step_opnd hC (K_lt hC hj hK) β) hrc


lemma no_common (hC : IsAO2 n C) (hj : j < C.gates.length)
    (hinj : Set.InjOn (slotW C) (slots n C j)) {g : ℕ}
    (hK : g ∈ PEqualNP.Core.coneSet n C j) {x : ℕ} (hx : x < n + C.gates.length)
    (h0 : Reach n C (opnd C g 0) x) (h1 : Reach n C (opnd C g 1) x) : False := by
  classical
  have hrb := hC.2.1
  have hg := K_lt hC hj hK
  have hsl : ∀ h ∈ PEqualNP.Core.coneSet n C j, ∀ b : Fin 2, ((h, b) : ℕ × Fin 2) ∈ slots n C j :=
    fun h hh b => Finset.mem_product.2 ⟨hh, Finset.mem_univ _⟩
  have inj : ∀ h ∈ PEqualNP.Core.coneSet n C j, ∀ b : Fin 2, ∀ h' ∈ PEqualNP.Core.coneSet n C j,
      ∀ b' : Fin 2, opnd C h b = opnd C h' b' → h = h' ∧ b = b' := by
    intro h hh b h' hh' b' he
    have := hinj (hsl h hh b) (hsl h' hh' b') he
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  set Z := (Finset.range (n + C.gates.length)).filter
    (fun z => Reach n C (opnd C g 0) z ∧ Reach n C (opnd C g 1) z) with hZ
  have hxZ : x ∈ Z := Finset.mem_filter.2 ⟨Finset.mem_range.2 hx, h0, h1⟩
  obtain ⟨z, hzZ, hmax⟩ := Finset.exists_max_image Z id ⟨x, hxZ⟩
  rw [Finset.mem_filter] at hzZ
  obtain ⟨_, hz0, hz1⟩ := hzZ
  have hl0 := opnd_lt hC hg 0
  have hl1 := opnd_lt hC hg 1
  by_cases ha : z = opnd C g 0
  · by_cases hab : opnd C g 1 = opnd C g 0
    · have := (inj g hK 1 g hK 0 hab).2
      exact absurd this (by decide)
    · have hzb : z ≠ opnd C g 1 := fun h => hab (h ▸ ha)
      obtain ⟨h, hh, b, hb, hr⟩ := below_named hC hj hK 1 hz1 hzb
      obtain ⟨rfl, rfl⟩ := inj h hh b g hK 0 (hb.trans ha)
      have := reach_le n C hrb hr
      omega
  · by_cases hb' : z = opnd C g 1
    · obtain ⟨h, hh, b, hb, hr⟩ := below_named hC hj hK 0 hz0 ha
      obtain ⟨rfl, rfl⟩ := inj h hh b g hK 1 (hb.trans hb')
      have := reach_le n C hrb hr
      omega
    · obtain ⟨h1', hh1, b1, hb1, hr1⟩ := below_named hC hj hK 0 hz0 ha
      obtain ⟨h2', hh2, b2, hb2, hr2⟩ := below_named hC hj hK 1 hz1 hb'
      obtain ⟨rfl, rfl⟩ := inj h1' hh1 b1 h2' hh2 b2 (hb1.trans hb2.symm)
      have hlt1 := K_lt hC hj hh1
      have hin : n + h1' ∈ Z := Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hr1, hr2⟩
      have := hmax _ hin
      have := opnd_lt hC hlt1 b1
      simp only [id] at *
      omega

end AO


section Vectors

variable {n : ℕ} {C : Circuit}


abbrev AV (n : ℕ) (C : Circuit) (k : ℕ) (S : List ℕ) (x : ℕ) : List (List ℕ) :=
  (readVectors C n S k).getD x []

lemma AV_input (k : ℕ) (S : List ℕ) (x : ℕ) (hx : x < n) :
    AV n C k S x = leafVectors S k x := by
  unfold AV
  rw [rv_eq, foldl_snoc_init _ _ _ _ _ (by simpa using hx)]
  simp [List.getD_eq_getElem?_getD, hx]

lemma AV_gate (k : ℕ) (S : List ℕ) (j : ℕ) (hj : j < C.gates.length)
    (hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j) :
    AV n C k S (n + j) = rvG S k ((gateAt C j).inputs.map (AV n C k S)) (gateAt C j) := by
  unfold AV
  rw [gateAt_eq C j hj] at hrb ⊢
  have := foldl_snoc_gate (rvG S k) [] ((List.range n).map (leafVectors S k)) C.gates j hj
    (by simpa using hrb)
  simp only [List.length_map, List.length_range] at this
  rw [rv_eq, this]

lemma capAdd_le (k : ℕ) (u v : List ℕ) (i : ℕ) :
    (capAdd k u v).getD i 0 ≤ u.getD i 0 + v.getD i 0 := by
  unfold capAdd
  simp only [List.getD_eq_getElem?_getD, List.getElem?_zipWith]
  cases u[i]? <;> cases v[i]? <;> simp

lemma leaf_getD (p q w i : ℕ) (v : List ℕ) (hv : v ∈ leafVectors [p, q] 1 w) :
    v.getD i 0 ≤ 1 ∧ (v.getD i 0 ≠ 0 → [p, q].getD i 0 = w) := by
  unfold leafVectors at hv
  split_ifs at hv
  · simp only [List.mem_singleton] at hv
    subst hv
    rcases i with _ | _ | i
    · by_cases h : p = w <;> simp [h]
    · by_cases h : q = w <;> simp [h]
    · simp
  · simp at hv

lemma leaf_ne (p q w : ℕ) (hw : w = p ∨ w = q) : leafVectors [p, q] 1 w ≠ [] := by
  unfold leafVectors
  rw [ite_eq_left (by simp; tauto)]
  simp


lemma mem_rvG_or (S : List ℕ) (k : ℕ) (A B : List (List ℕ)) (g : Gate) (hg : g.op = GateOp.or)
    (v : List ℕ) : v ∈ rvG S k [A, B] g ↔ v ∈ A ∨ v ∈ B := by
  unfold rvG
  rw [hg]
  simp only
  rw [mem_orFold]
  simp

lemma mem_rvG_and (S : List ℕ) (k : ℕ) (A B : List (List ℕ)) (g : Gate) (hg : g.op = GateOp.and)
    (v : List ℕ) : v ∈ rvG S k [A, B] g ↔
      ∃ a ∈ A, ∃ b ∈ B, v = capAdd k (capAdd k (S.map fun _ => 0) a) b := by
  unfold rvG
  rw [hg]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [mem_andStep]
  constructor
  · rintro ⟨c, hc, b, hb, rfl⟩
    rw [mem_andStep] at hc
    obtain ⟨z, hz, a, ha, rfl⟩ := hc
    simp only [List.mem_singleton] at hz
    subst hz
    exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨_, (mem_andStep _ _ _ _).2 ⟨_, List.mem_singleton_self _, a, ha, rfl⟩, b, hb, rfl⟩

lemma zero_getD (S : List ℕ) (i : ℕ) : (S.map fun _ => 0).getD i 0 = 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases S[i]? <;> simp

lemma and_getD_le (k : ℕ) (S : List ℕ) (a b : List ℕ) (i : ℕ) :
    (capAdd k (capAdd k (S.map fun _ => 0) a) b).getD i 0 ≤ a.getD i 0 + b.getD i 0 := by
  have h1 := capAdd_le k (capAdd k (S.map fun _ => 0) a) b i
  have h2 := capAdd_le k (S.map fun _ => 0) a i
  rw [zero_getD] at h2
  omega

lemma gate_vec (hC : IsAO2 n C) (k : ℕ) (S : List ℕ) {g : ℕ} (hg : g < C.gates.length) (v : List ℕ) :
    v ∈ AV n C k S (n + g) ↔
      ((gateAt C g).op = GateOp.or ∧ (v ∈ AV n C k S (opnd C g 0) ∨ v ∈ AV n C k S (opnd C g 1))) ∨
      ((gateAt C g).op = GateOp.and ∧ ∃ a ∈ AV n C k S (opnd C g 0), ∃ b ∈ AV n C k S (opnd C g 1),
        v = capAdd k (capAdd k (S.map fun _ => 0) a) b) := by
  rw [AV_gate k S g hg (hC.2.1 g hg), ao_inputs hC hg]
  simp only [List.map_cons, List.map_nil]
  rcases ao_op hC hg with h | h
  · rw [mem_rvG_and _ _ _ _ _ h]; simp [h]
  · rw [mem_rvG_or _ _ _ _ _ h]; simp [h]


lemma vec_reach (hC : IsAO2 n C) (p q : ℕ) (i : ℕ) :
    ∀ w, ∀ v ∈ AV n C 1 [p, q] w, v.getD i 0 ≠ 0 → Reach n C w ([p, q].getD i 0) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro v hv hne
  by_cases hwn : w < n
  · rw [AV_input 1 _ w hwn] at hv
    rw [(leaf_getD p q w i v hv).2 hne]
  · by_cases hwl : w < n + C.gates.length
    · obtain ⟨g, rfl⟩ : ∃ g, w = n + g := ⟨w - n, by omega⟩
      have hg : g < C.gates.length := by omega
      rcases (gate_vec hC 1 _ hg v).1 hv with ⟨_, h | h⟩ | ⟨_, a, ha, b, hb, rfl⟩
      · exact Relation.ReflTransGen.head (step_opnd hC hg 0)
          (ih _ (opnd_lt hC hg 0) v h hne)
      · exact Relation.ReflTransGen.head (step_opnd hC hg 1)
          (ih _ (opnd_lt hC hg 1) v h hne)
      · have := and_getD_le 1 [p, q] a b i
        by_cases ha0 : a.getD i 0 = 0
        · exact Relation.ReflTransGen.head (step_opnd hC hg 1)
            (ih _ (opnd_lt hC hg 1) b hb (by omega))
        · exact Relation.ReflTransGen.head (step_opnd hC hg 0)
            (ih _ (opnd_lt hC hg 0) a ha ha0)
    · have : AV n C 1 [p, q] w = [] := by
        unfold AV
        rw [rv_eq, foldl_snoc_beyond _ _ _ _ _ (by simp; omega)]
      rw [this] at hv
      simp at hv


lemma vec_ne (hC : IsAO2 n C) (u v : Fin n) :
    ∀ w, w < n + C.gates.length → W C n (pairInput u v) w = true →
      AV n C 1 [u.val, v.val] w ≠ [] := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro hwl hW
  by_cases hwn : w < n
  · rw [AV_input 1 _ w hwn]
    rw [W_input C n _ w hwn] at hW
    unfold pairInput at hW
    simp only [decide_eq_true_eq] at hW
    apply leaf_ne
    rcases hW with h | h
    · left; rw [← h]
    · right; rw [← h]
  · obtain ⟨g, rfl⟩ : ∃ g, w = n + g := ⟨w - n, by omega⟩
    have hg : g < C.gates.length := by omega
    rw [W_gate C n _ g hg (hC.2.1 g hg), ao_inputs hC hg] at hW
    have l0 := opnd_lt hC hg 0
    have l1 := opnd_lt hC hg 1
    rcases ao_op hC hg with h | h
    · rw [h] at hW
      simp [GateOp.eval] at hW
      obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ (ih _ l0 (by omega) hW.1)
      obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil _ (ih _ l1 (by omega) hW.2)
      exact List.ne_nil_of_mem ((gate_vec hC 1 _ hg _).2 (Or.inr ⟨h, a, ha, b, hb, rfl⟩))
    · rw [h] at hW
      simp [GateOp.eval] at hW
      rcases hW with hW | hW
      · obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ (ih _ l0 (by omega) hW)
        exact List.ne_nil_of_mem ((gate_vec hC 1 _ hg _).2 (Or.inl ⟨h, Or.inl ha⟩))
      · obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ (ih _ l1 (by omega) hW)
        exact List.ne_nil_of_mem ((gate_vec hC 1 _ hg _).2 (Or.inl ⟨h, Or.inr ha⟩))


lemma vec_le_one (hC : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length)
    (hinj : Set.InjOn (slotW C) (slots n C j)) (p q : ℕ) (hp : p < n) (hq : q < n) :
    ∀ g ∈ PEqualNP.Core.coneSet n C j, ∀ v ∈ AV n C 1 [p, q] (n + g), ∀ i, v.getD i 0 ≤ 1 := by
  intro g
  induction g using Nat.strong_induction_on with
  | _ g ih =>
  intro hK v hv i
  have hg := K_lt hC hj hK
  have hop : ∀ b : Fin 2, ∀ v ∈ AV n C 1 [p, q] (opnd C g b), v.getD i 0 ≤ 1 := by
    intro b v hv
    by_cases hn : opnd C g b < n
    · rw [AV_input 1 _ _ hn] at hv
      exact (leaf_getD p q _ i v hv).1
    · obtain ⟨hK', hlt⟩ := K_opnd hC hj hK b (by omega)
      have he : n + (opnd C g b - n) = opnd C g b := by omega
      rw [← he] at hv
      exact ih _ hlt hK' v hv i
  rcases (gate_vec hC 1 _ hg v).1 hv with ⟨_, h | h⟩ | ⟨_, a, ha, b, hb, rfl⟩
  · exact hop 0 v h
  · exact hop 1 v h
  · have hle := and_getD_le 1 [p, q] a b i
    have ha1 := hop 0 a ha
    have hb1 := hop 1 b hb
    by_cases ha0 : a.getD i 0 = 0
    · omega
    · by_cases hb0 : b.getD i 0 = 0
      · omega
      · exfalso
        have hx : [p, q].getD i 0 < n + C.gates.length := by
          rcases i with _ | _ | i <;> simp <;> omega
        exact no_common hC hj hinj hK hx (vec_reach hC p q i _ a ha ha0)
          (vec_reach hC p q i _ b hb hb0)

end Vectors


end PEqualNP.Outside.L_meta_2962_aux.StrictLeaf

namespace PEqualNP.Outside.L_meta_2962_aux.ReadVectorSupport

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadK PEqualNP.SplitCount
open PEqualNP.Outside.L_meta_2962_aux.StrictLeaf

lemma pair_vec_shape {n : ℕ} {C : Circuit} (hC : IsAO2 n C) (p q : ℕ) :
    ∀ w, w < n + C.gates.length → ∀ a ∈ AV n C 1 [p, q] w,
      ∃ a₀ a₁ : ℕ, a = [a₀, a₁] := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro hw a ha
  by_cases hn : w < n
  · rw [AV_input 1 _ w hn] at ha
    unfold leafVectors at ha
    split_ifs at ha with hmem
    · simp only [List.mem_singleton] at ha
      subst a
      simp only [List.map_cons, List.map_nil]
      exact ⟨_, _, rfl⟩
    · simp at ha
  · obtain ⟨g, rfl⟩ : ∃ g, w = n + g := ⟨w - n, by omega⟩
    have hg : g < C.gates.length := by omega
    have l0 := opnd_lt hC hg 0
    have l1 := opnd_lt hC hg 1
    rcases (gate_vec hC 1 [p, q] hg a).1 ha with ⟨_, h | h⟩ | ⟨_, a', ha', b, hb, rfl⟩
    · exact ih _ l0 (by omega) _ h
    · exact ih _ l1 (by omega) _ h
    · obtain ⟨a₀, a₁, rfl⟩ := ih _ l0 (by omega) a' ha'
      obtain ⟨b₀, b₁, rfl⟩ := ih _ l1 (by omega) b hb
      simp only [List.map_cons, List.map_nil, capAdd, List.zipWith_cons_cons, List.zipWith_nil_left]
      exact ⟨_, _, rfl⟩

lemma pair_vec_sound {n : ℕ} {C : Circuit} (hC : IsAO2 n C) (u v : Fin n)
    (x : Fin n → Bool) :
    ∀ w, w < n + C.gates.length → ∀ a ∈ AV n C 1 [u.val, v.val] w,
      (a.getD 0 0 ≠ 0 → x u = true) →
      (a.getD 1 0 ≠ 0 → x v = true) → W C n x w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro hw a ha hu hv
  by_cases hn : w < n
  · rw [AV_input 1 _ w hn] at ha
    unfold leafVectors at ha
    split_ifs at ha with hmem
    · simp only [List.mem_singleton] at ha
      subst a
      rw [W_input C n _ w hn]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with heq | heq
      · have hfin : (⟨w, hn⟩ : Fin n) = u := Fin.ext heq
        rw [hfin]
        apply hu
        simp [heq]
      · have hfin : (⟨w, hn⟩ : Fin n) = v := Fin.ext heq
        rw [hfin]
        apply hv
        simp [heq]
    · simp at ha
  · obtain ⟨g, rfl⟩ : ∃ g, w = n + g := ⟨w - n, by omega⟩
    have hg : g < C.gates.length := by omega
    have l0 := opnd_lt hC hg 0
    have l1 := opnd_lt hC hg 1
    rw [W_gate C n x g hg (hC.2.1 g hg), ao_inputs hC hg]
    rcases (gate_vec hC 1 [u.val, v.val] hg a).1 ha with ⟨hop, h | h⟩ | ⟨hop, a', ha', b, hb, rfl⟩
    · rw [hop]
      simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
        Bool.or_false, Bool.or_eq_true, id_eq]
      exact Or.inl (ih _ l0 (by omega) _ h hu hv)
    · rw [hop]
      simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
        Bool.or_false, Bool.or_eq_true, id_eq]
      exact Or.inr (ih _ l1 (by omega) _ h hu hv)
    · obtain ⟨a₀, a₁, rfl⟩ := pair_vec_shape hC u.val v.val _ (by omega) a' ha'
      obtain ⟨b₀, b₁, rfl⟩ := pair_vec_shape hC u.val v.val _ (by omega) b hb
      simp only [capAdd, List.map_cons, List.map_nil, List.zipWith_cons_cons,
        List.zipWith_nil_left, List.getD_cons_zero, List.getD_cons_succ] at hu hv
      have ha₀ : a₀ ≠ 0 → x u = true := fun h => hu (by omega)
      have ha₁ : a₁ ≠ 0 → x v = true := fun h => hv (by omega)
      have hb₀ : b₀ ≠ 0 → x u = true := fun h => hu (by omega)
      have hb₁ : b₁ ≠ 0 → x v = true := fun h => hv (by omega)
      have hleft := ih _ l0 (by omega) _ ha' (by simpa using ha₀) (by simpa using ha₁)
      have hright := ih _ l1 (by omega) _ hb (by simpa using hb₀) (by simpa using hb₁)
      rw [hop]
      simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
        Bool.and_true, Bool.and_eq_true, id_eq]
      exact ⟨hleft, hright⟩

lemma pair_vec_zero_left {n : ℕ} {C : Circuit} (hC : IsAO2 n C) (u v : Fin n)
    {w : ℕ} (hw : w < n + C.gates.length) {a : List ℕ}
    (ha : a ∈ AV n C 1 [u.val, v.val] w) (hz : a.getD 0 0 = 0) :
    W C n (unitInput v) w = true := by
  apply pair_vec_sound hC u v (unitInput v) w hw a ha
  · intro h
    exact (h hz).elim
  · intro h
    simp [unitInput]

lemma pair_vec_zero_right {n : ℕ} {C : Circuit} (hC : IsAO2 n C) (u v : Fin n)
    {w : ℕ} (hw : w < n + C.gates.length) {a : List ℕ}
    (ha : a ∈ AV n C 1 [u.val, v.val] w) (hz : a.getD 1 0 = 0) :
    W C n (unitInput u) w = true := by
  apply pair_vec_sound hC u v (unitInput u) w hw a ha
  · intro h
    simp [unitInput]
  · intro h
    exact (h hz).elim

lemma graph_unit_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (z : Fin n) :
    graphFun G ∅ (unitInput z) = false := by
  cases hf : graphFun G ∅ (unitInput z) with
  | false => rfl
  | true =>
    have h : ∃ u v : Fin n, G.Adj u v ∧ unitInput z u = true ∧ unitInput z v = true := by
      simpa [graphFun] using hf
    obtain ⟨u, v, hadj, hu, hv⟩ := h
    simp only [unitInput, decide_eq_true_eq] at hu hv
    subst hu
    subst hv
    exact (G.ne_of_adj hadj rfl).elim

lemma below_pair_vec_pos {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hC : IsAO2 n C) (u v : Fin n) {w : ℕ}
    (hw : w < n + C.gates.length)
    (hbelow : ∀ x : Fin n → Bool, W C n x w = true → graphFun G ∅ x = true)
    {a : List ℕ} (ha : a ∈ AV n C 1 [u.val, v.val] w) :
    0 < a.getD 0 0 ∧ 0 < a.getD 1 0 := by
  constructor
  · by_contra h
    have hz : a.getD 0 0 = 0 := by omega
    have hf := hbelow (unitInput v) (pair_vec_zero_left hC u v hw ha hz)
    rw [graph_unit_false] at hf
    cases hf
  · by_contra h
    have hz : a.getD 1 0 = 0 := by omega
    have hf := hbelow (unitInput u) (pair_vec_zero_right hC u v hw ha hz)
    rw [graph_unit_false] at hf
    cases hf

end PEqualNP.Outside.L_meta_2962_aux.ReadVectorSupport

namespace PEqualNP.Outside.L_meta_2962_aux.WrapperVectors

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadK
open PEqualNP.Outside.L_meta_2962_aux.StrictLeaf

lemma AV_append (n : ℕ) (C : Circuit) (gs : List Gate) (o k w : ℕ) (S : List ℕ)
    (hw : w < n + C.gates.length) :
    AV n { gates := C.gates ++ gs, output := o } k S w = AV n C k S w := by
  unfold AV
  rw [rv_eq, rv_eq]
  simp only [List.foldl_append]
  apply getD_of_prefix
  · exact foldl_snoc_prefix (fun R g => rvG S k (g.inputs.map fun i => R.getD i []) g) gs _
  · simpa only [foldl_snoc_length, List.length_map, List.length_range] using hw

lemma pair_sum_repeats (a₀ a₁ b₀ b₁ : ℕ)
    (ha : 0 < a₀ ∨ 0 < a₁) (hb₀ : 0 < b₀) (hb₁ : 0 < b₁) :
    (capAdd 1 (capAdd 1 [0, 0] [a₀, a₁]) [b₀, b₁]).all
      (fun c => decide (c ≤ 1)) = false := by
  simp only [capAdd, List.zipWith_cons_cons, List.zipWith_nil_left, Nat.zero_add]
  rcases ha with ha | ha
  · have h : min (min a₀ 2 + b₀) 2 = 2 := by omega
    simp [h]
  · have h : min (min a₁ 2 + b₁) 2 = 2 := by omega
    simp [h]

lemma or_and_vector_repeats (p q x : ℕ) (F : List (List ℕ)) (gOr gAnd : Gate)
    (hOr : gOr.op = GateOp.or) (hAnd : gAnd.op = GateOp.and)
    (hshape : ∀ b ∈ F, ∃ b₀ b₁, b = [b₀, b₁])
    (hpos : ∀ b ∈ F, 0 < b.getD 0 0 ∧ 0 < b.getD 1 0)
    (v : List ℕ)
    (hv : v ∈ rvG [p, q] 1
      [rvG [p, q] 1 [F, leafVectors [p, q] 1 x] gOr, F] gAnd) :
    v.all (fun c => decide (c ≤ 1)) = false := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_rvG_and _ _ _ _ _ hAnd _).mp hv
  obtain ⟨b₀, b₁, rfl⟩ := hshape b hb
  have hbp := hpos [b₀, b₁] hb
  simp only [List.getD_cons_zero, List.getD_cons_succ] at hbp
  rcases (mem_rvG_or _ _ _ _ _ hOr _).mp ha with ha | ha
  · obtain ⟨a₀, a₁, rfl⟩ := hshape a ha
    have hap := hpos [a₀, a₁] ha
    simp only [List.getD_cons_zero, List.getD_cons_succ] at hap
    simpa only [List.map_cons, List.map_nil] using
      pair_sum_repeats a₀ a₁ b₀ b₁ (Or.inl hap.1) hbp.1 hbp.2
  · unfold leafVectors at ha
    split_ifs at ha with hx
    · simp only [List.mem_singleton] at ha
      subst a
      have hx' : x = p ∨ x = q := by simpa using hx
      rcases hx' with hx | hx
      · subst x
        simpa using pair_sum_repeats 1 (if q = p then 1 else 0) b₀ b₁
          (Or.inl (by omega)) hbp.1 hbp.2
      · subst x
        simpa using pair_sum_repeats (if p = q then 1 else 0) 1 b₀ b₁
          (Or.inr (by omega)) hbp.1 hbp.2
    · simp at ha

end PEqualNP.Outside.L_meta_2962_aux.WrapperVectors

namespace PEqualNP.Outside.L_meta_2962_aux.StrictLeaf

open PEqualNP.CircuitLowerBounds PEqualNP.ReadK

lemma AV_snoc (n : ℕ) (C : Circuit) (g : Gate) (o k : ℕ) (S : List ℕ) :
    AV n { gates := C.gates ++ [g], output := o } k S (n + C.gates.length) =
      rvG S k (g.inputs.map (AV n C k S)) g := by
  let R := readVectors C n S k
  have hlen : R.length = n + C.gates.length := by
    dsimp [R]
    rw [rv_eq, foldl_snoc_length]
    simp
  unfold AV
  rw [rv_eq]
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
  change (R ++ [rvG S k (g.inputs.map fun i => R.getD i []) g]).getD
      (n + C.gates.length) [] = rvG S k (g.inputs.map fun i => R.getD i []) g
  rw [← hlen]
  simp [List.getD]

end PEqualNP.Outside.L_meta_2962_aux.StrictLeaf

namespace PEqualNP.Outside.L_meta_2962_aux.WrapperReadTwice

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadK
open PEqualNP.Outside.L_meta_2962_aux.StrictLeaf
  PEqualNP.Outside.L_meta_2962_aux.ReadVectorSupport
  PEqualNP.Outside.L_meta_2962_aux.WrapperVectors

def pairWrapper (n : ℕ) (C : Circuit) (w z o : ℕ) : Circuit :=
  { gates := C.gates ++ [{ op := GateOp.or, inputs := [w, z] },
      { op := GateOp.and, inputs := [n + C.gates.length, w] }], output := o }

lemma wrapper_AV (n : ℕ) (C : Circuit) (w o p q : ℕ) (z : Fin n)
    (hw : w < n + C.gates.length) :
    AV n (pairWrapper n C w z.val o) 1 [p, q] (n + C.gates.length + 1) =
      rvG [p, q] 1
        [rvG [p, q] 1 [AV n C 1 [p, q] w, leafVectors [p, q] 1 z.val]
          { op := GateOp.or, inputs := [w, z.val] }, AV n C 1 [p, q] w]
        { op := GateOp.and, inputs := [n + C.gates.length, w] } := by
  let gOr : Gate := { op := GateOp.or, inputs := [w, z.val] }
  let gAnd : Gate := { op := GateOp.and, inputs := [n + C.gates.length, w] }
  let C₁ : Circuit := { gates := C.gates ++ [gOr], output := o }
  have hlen : C₁.gates.length = C.gates.length + 1 := by simp [C₁]
  have hform : pairWrapper n C w z.val o =
      { gates := C₁.gates ++ [gAnd], output := o } := by
    simp [pairWrapper, C₁, gOr, gAnd, List.append_assoc]
  rw [hform, Nat.add_assoc, ← hlen, AV_snoc]
  change rvG [p, q] 1
    [AV n C₁ 1 [p, q] (n + C.gates.length), AV n C₁ 1 [p, q] w] gAnd = _
  have hq := AV_snoc n C gOr o 1 [p, q]
  change AV n C₁ 1 [p, q] (n + C.gates.length) = _ at hq
  rw [hq]
  change rvG [p, q] 1
    [rvG [p, q] 1 [AV n C 1 [p, q] w, AV n C 1 [p, q] z.val] gOr,
      AV n C₁ 1 [p, q] w] gAnd = _
  rw [AV_input 1 _ z.val z.isLt]
  have hold := AV_append n C [gOr] o 1 w [p, q] hw
  change AV n C₁ 1 [p, q] w = _ at hold
  rw [hold]

lemma wrapper_readTwice {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hC : IsAO2 n C) (w o : ℕ) (z u v : Fin n)
    (hw : w < n + C.gates.length)
    (hbelow : ∀ x : Fin n → Bool, W C n x w = true → graphFun G ∅ x = true) :
    Core.ReadTwiceAt n (pairWrapper n C w z.val o) (C.gates.length + 1) u v := by
  have hvectors : ∀ a ∈ AV n (pairWrapper n C w z.val o) 1 [u.val, v.val]
      (n + C.gates.length + 1), a.all (fun c => decide (c ≤ 1)) = false := by
    intro a ha
    rw [wrapper_AV n C w o u.val v.val z hw] at ha
    exact or_and_vector_repeats u.val v.val z.val _ _ _ rfl rfl
      (pair_vec_shape hC u.val v.val w hw)
      (fun a ha => below_pair_vec_pos hC u v hw hbelow ha) a ha
  unfold Core.ReadTwiceAt readsAtMost
  change (AV n (pairWrapper n C w z.val o) 1 [u.val, v.val]
    (n + (C.gates.length + 1))).any (fun a => a.all (fun c => decide (c ≤ 1))) = false
  rw [← Nat.add_assoc]
  apply List.any_eq_false.mpr
  intro a ha
  rw [hvectors a ha]
  decide

end PEqualNP.Outside.L_meta_2962_aux.WrapperReadTwice


namespace PEqualNP.Outside.L_meta_2962.AbsorbWrapper

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadTwo PEqualNP.Core PEqualNP.SplitCount

def wrap {n : ℕ} (C : Circuit) (v : Fin n) : Circuit :=
  ⟨C.gates ++ [⟨.or, [C.output, v.val]⟩,
    ⟨.and, [n + C.gates.length, C.output]⟩], n + C.gates.length + 1⟩

lemma fold_length (gs : List Gate) (acc : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) acc).length =
      acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih => simp only [List.foldl_cons, ih, List.length_append,
      List.length_cons, List.length_nil]; omega

lemma fold_prefix (gs : List Gate) (acc : List Bool) (i : ℕ) (hi : i < acc.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) acc).getD i false =
      acc.getD i false := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih _ (by simp only [List.length_append, List.length_singleton]; omega)]
    simp [List.getD, List.getElem?_append_left hi]

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := fold_length _ _

lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (v : Fin n) :
    wval C x v.val = x v := by
  unfold wval Circuit.wires
  rw [fold_prefix _ _ _ (by simp)]
  simp [List.getD]

lemma prefix_value {n : ℕ} (C : Circuit) (v : Fin n) (x : Fin n → Bool)
    (i : ℕ) (hi : i < n + C.gates.length) :
    wval (wrap C v) x i = wval C x i := by
  unfold wval wrap Circuit.wires
  rw [List.foldl_append]
  apply fold_prefix
  simpa only [fold_length, List.length_ofFn] using hi

lemma wires_wrap {n : ℕ} (C : Circuit) (v : Fin n) (x : Fin n → Bool)
    (hout : C.output < n + C.gates.length) :
    (wrap C v).wires (List.ofFn x) = C.wires (List.ofFn x) ++
      [circuitFun n C x || x v, circuitFun n C x] := by
  have hlen := wires_length C (List.ofFn x)
  simp only [List.length_ofFn] at hlen
  have hv := input_value C x v
  unfold wval at hv
  have ho : (C.wires (List.ofFn x)).getD C.output false = circuitFun n C x := rfl
  have hop : ((C.wires (List.ofFn x)) ++ [circuitFun n C x || x v]).getD C.output false =
      circuitFun n C x := by
    simpa [List.getD, List.getElem?_append_left (by omega : C.output <
      (C.wires (List.ofFn x)).length)] using ho
  have hqp : ((C.wires (List.ofFn x)) ++ [circuitFun n C x || x v]).getD
      (n + C.gates.length) false = (circuitFun n C x || x v) := by
    rw [← hlen]
    cases circuitFun n C x <;> cases x v <;> simp [List.getD]
  change (C.gates ++ ([⟨.or, [C.output, v.val]⟩,
      ⟨.and, [n + C.gates.length, C.output]⟩] : List Gate)).foldl
      (fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (List.ofFn x) = _
  rw [List.foldl_append]
  change ([⟨.or, [C.output, v.val]⟩, ⟨.and, [n + C.gates.length, C.output]⟩] : List Gate).foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (C.wires (List.ofFn x)) = _
  simp only [List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil,
    GateOp.eval, List.any_cons, List.any_nil, List.all_cons, List.all_nil,
    Bool.or_false, Bool.and_true, ho, hv]
  change (C.wires (List.ofFn x) ++ [circuitFun n C x || x v]) ++
      [((C.wires (List.ofFn x) ++ [circuitFun n C x || x v]).getD
        (n + C.gates.length) false) &&
       ((C.wires (List.ofFn x) ++ [circuitFun n C x || x v]).getD C.output false)] = _
  rw [hqp, hop]
  cases circuitFun n C x <;> cases x v <;> simp

lemma correct {n : ℕ} (C : Circuit) (v : Fin n)
    (hout : C.output < n + C.gates.length) :
    circuitFun n (wrap C v) = circuitFun n C := by
  funext x
  unfold circuitFun Circuit.eval
  rw [wires_wrap C v x hout]
  simp [wrap, List.getD, wires_length, circuitFun, Circuit.eval]

lemma q_value {n : ℕ} (C : Circuit) (v : Fin n) (x : Fin n → Bool)
    (hout : C.output < n + C.gates.length) :
    gateVal n (wrap C v) C.gates.length x = (circuitFun n C x || x v) := by
  unfold gateVal
  rw [wires_wrap C v x hout]
  cases circuitFun n C x <;> cases x v <;> simp [List.getD, wires_length]

lemma r_value {n : ℕ} (C : Circuit) (v : Fin n) (x : Fin n → Bool)
    (hout : C.output < n + C.gates.length) :
    gateVal n (wrap C v) (C.gates.length + 1) x = circuitFun n C x := by
  change circuitFun n (wrap C v) x = circuitFun n C x
  rw [correct C v hout]

lemma gate_prefix {n : ℕ} (C : Circuit) (v : Fin n) {j : ℕ} (hj : j < C.gates.length) :
    gateAt (wrap C v) j = gateAt C j := by
  simp [gateAt, wrap, List.getD, List.getElem?_append_left hj]

lemma gate_q {n : ℕ} (C : Circuit) (v : Fin n) :
    gateAt (wrap C v) C.gates.length = ⟨.or, [C.output, v.val]⟩ := by
  unfold gateAt wrap
  simp only
  unfold List.getD
  rw [List.getElem?_append_right (Nat.le_refl _)]
  simp

lemma gate_r {n : ℕ} (C : Circuit) (v : Fin n) :
    gateAt (wrap C v) (C.gates.length + 1) = ⟨.and, [n + C.gates.length, C.output]⟩ := by
  unfold gateAt wrap
  simp only
  unfold List.getD
  rw [List.getElem?_append_right (by omega)]
  simp

lemma ao2 {n : ℕ} (C : Circuit) (v : Fin n) (hAO : IsAO2 n C)
    (hout : C.output < n + C.gates.length) : IsAO2 n (wrap C v) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hAO.1 g hg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl <;> simp
  · intro j hj i hi
    by_cases old : j < C.gates.length
    · rw [gate_prefix C v old] at hi
      exact hAO.2.1 j old i hi
    · have hj' : j = C.gates.length ∨ j = C.gates.length + 1 := by
        simp only [wrap, List.length_append, List.length_cons, List.length_nil] at hj
        omega
      rcases hj' with rfl | rfl
      · rw [gate_q] at hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · exact hout
        · have := v.isLt; omega
      · rw [gate_r] at hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl <;> omega
  · intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hAO.2.2 g hg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl <;> rfl

lemma edge_truth {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by
  simp [graphFun]

lemma graph_unit_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n) :
    graphFun G ∅ (unitInput v) = false := by
  cases hf : graphFun G ∅ (unitInput v) with
  | false => rfl
  | true =>
    rw [edge_truth] at hf
    rcases hf with ⟨u, w, hadj, hu, hw⟩
    simp only [unitInput, decide_eq_true_eq] at hu hw
    subst hu; subst hw
    exact (G.ne_of_adj hadj rfl).elim

lemma r_below {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (v : Fin n) (hout : C.output < n + C.gates.length)
    (hcorrect : circuitFun n C = graphFun G ∅) :
    BelowF G (wrap C v) (C.gates.length + 1) := by
  intro x hx
  rwa [r_value C v x hout, hcorrect] at hx

lemma q_not_below {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (v : Fin n) (hout : C.output < n + C.gates.length)
    (hcorrect : circuitFun n C = graphFun G ∅) :
    ¬ BelowF G (wrap C v) C.gates.length := by
  intro h
  have hq : gateVal n (wrap C v) C.gates.length (unitInput v) = true := by
    rw [q_value C v _ hout, hcorrect, graph_unit_false]
    simp [unitInput]
  have hf := h (unitInput v) hq
  rw [graph_unit_false] at hf
  cases hf

lemma gamma_all {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (v : Fin n) (hout : C.output < n + C.gates.length)
    (hcorrect : circuitFun n C = graphFun G ∅) :
    gammaE G (wrap C v) (C.gates.length + 1) = G.edgeFinset := by
  apply Finset.ext
  intro e
  refine Sym2.inductionOn e ?_
  intro u w
  simp only [gammaE, Finset.mem_filter]
  constructor
  · exact And.left
  · intro hedge
    refine ⟨hedge, u, w, rfl, ?_⟩
    rw [r_value C v _ hout, hcorrect]
    apply (edge_truth _).mpr
    exact ⟨u, w, by simpa using hedge, by simp [pairInput], by simp [pairInput]⟩

end PEqualNP.Outside.L_meta_2962.AbsorbWrapper

namespace PEqualNP.Outside.L_meta_2962.AbsorbWrapper

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Core
open PEqualNP.Outside.L_meta_2962_aux.StrictLeaf
  PEqualNP.Outside.L_meta_2962_aux.WrapperReadTwice

lemma isCore {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (z : Fin n) (hAO : IsAO2 n C)
    (hout : C.output < n + C.gates.length)
    (hcorrect : circuitFun n C = graphFun G ∅)
    (hne : ∃ u v : Fin n, G.Adj u v) :
    Core.IsCore G (wrap C z) (C.gates.length + 1) := by
  obtain ⟨u, v, huv⟩ := hne
  have hr : gateVal n (wrap C z) (C.gates.length + 1) (pairInput u v) = true := by
    rw [r_value C z _ hout, hcorrect]
    apply (edge_truth _).mpr
    exact ⟨u, v, huv, by simp [pairInput], by simp [pairInput]⟩
  refine ⟨by simp [wrap], ⟨r_below G C z hout hcorrect, ⟨pairInput u v, hr⟩⟩, ?_,
    u, v, huv, hr, ?_⟩
  · intro h
    apply q_not_below G C z hout hcorrect
    have hq := h.1.2.1
    simpa only [opnd, gate_r, Fin.val_zero, List.getD_cons_zero, Nat.add_sub_cancel_left] using hq
  · have hb : ∀ x : Fin n → Bool, W C n x C.output = true → graphFun G ∅ x = true := by
      intro x hx
      change circuitFun n C x = true at hx
      rwa [hcorrect] at hx
    exact wrapper_readTwice hAO C.output (n + C.gates.length + 1) z u v hout hb

end PEqualNP.Outside.L_meta_2962.AbsorbWrapper
