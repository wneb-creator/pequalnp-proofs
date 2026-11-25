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


namespace PEqualNP.Outside.L_meta_2962.CoreStructure

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Core PEqualNP.SplitCount PEqualNP.ReadTwo

lemma foldl_wires_len (gs : List Gate) (acc : List Bool) :
    (gs.foldl (fun w gt => w ++ [gt.op.eval (gt.inputs.map fun i => w.getD i false)]) acc).length =
      acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons gt rest ih =>
    simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_wires_getD_lt (gs : List Gate) (acc : List Bool) (i : ℕ) (hi : i < acc.length) :
    (gs.foldl (fun w gt => w ++ [gt.op.eval (gt.inputs.map fun idx => w.getD idx false)]) acc).getD i false =
      acc.getD i false := by
  induction gs generalizing acc with
  | nil => rfl
  | cons gt rest ih =>
    simp only [List.foldl_cons]
    have hlt : i < (acc ++ [gt.op.eval (gt.inputs.map fun idx => acc.getD idx false)]).length := by
      simp only [List.length_append, List.length_singleton]
      omega
    rw [ih _ hlt]
    simp [List.getD, List.getElem?_append_left hi]

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := by
  unfold Circuit.wires
  exact foldl_wires_len C.gates x

lemma wval_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    wval C x i = x ⟨i, hi⟩ := by
  unfold wval Circuit.wires
  have hlen : i < (List.ofFn x).length := by simpa using hi
  rw [foldl_wires_getD_lt C.gates (List.ofFn x) i hlen]
  simp [List.getD, hi]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j ∈ C.gates := by
  unfold gateAt
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj

lemma gate_inputs_eq {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
    (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
  have hlen : (gateAt C j).inputs.length = 2 := hAO.2.2 (gateAt C j) (gateAt_mem hj)
  unfold opnd
  cases hl : (gateAt C j).inputs with
  | nil => simp [hl] at hlen
  | cons a l =>
    cases l with
    | nil => simp [hl] at hlen
    | cons b l' =>
      cases l' with
      | nil => simp [hl]
      | cons c l'' => simp [hl] at hlen

lemma opnd_mem {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b ∈ (gateAt C j).inputs := by
  rw [gate_inputs_eq hAO hj]
  fin_cases b <;> simp

lemma opnd_lt {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b < n + j :=
  hAO.2.1 j hj (opnd C j b) (opnd_mem hAO hj b)

lemma wval_gate_eval {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) :
    wval C x (n + j) = (gateAt C j).op.eval [wval C x (opnd C j 0), wval C x (opnd C j 1)] := by
  unfold wval Circuit.wires
  have hsplit : C.gates = C.gates.take j ++ gateAt C j :: C.gates.drop (j + 1) := by
    have hg : gateAt C j = C.gates[j] := by
      unfold gateAt
      exact List.getD_eq_getElem _ _ hj
    rw [hg]
    simpa using (List.take_append_drop j C.gates).symm.trans (by
      congr 1
      exact (List.cons_getElem_drop_succ (h := hj)).symm)
  set step : List Bool → Gate → List Bool :=
    fun w gt => w ++ [gt.op.eval (gt.inputs.map fun i => w.getD i false)]
  set pre := (C.gates.take j).foldl step (List.ofFn x)
  have hpre_len : pre.length = n + j := by
    have h1 := foldl_wires_len (C.gates.take j) (List.ofFn x)
    simp only [List.length_ofFn, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)] at h1
    exact h1
  have h_eq : C.gates.foldl step (List.ofFn x) =
      (C.gates.drop (j + 1)).foldl step (step pre (gateAt C j)) := by
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  have h_pre_get : ∀ i < n + j, (C.gates.foldl step (List.ofFn x)).getD i false = pre.getD i false := by
    intro i hi
    rw [h_eq]
    have hi1 : i < (step pre (gateAt C j)).length := by
      simp only [step, List.length_append, List.length_singleton, hpre_len]
      omega
    rw [foldl_wires_getD_lt _ _ i hi1]
    simp only [step]
    have hi2 : i < pre.length := by omega
    simp [List.getD, List.getElem?_append_left hi2]
  have h_nj : (C.gates.foldl step (List.ofFn x)).getD (n + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => pre.getD i false) := by
    rw [h_eq]
    have hlt : n + j < (step pre (gateAt C j)).length := by
      simp only [step, List.length_append, List.length_singleton, hpre_len]
      omega
    rw [foldl_wires_getD_lt _ _ (n + j) hlt]
    simp only [step]
    have hle : pre.length ≤ n + j := by omega
    simp [List.getD, List.getElem?_append_right hle, hpre_len]
  rw [h_nj, gate_inputs_eq hAO hj]
  have h0 := h_pre_get (opnd C j 0) (opnd_lt hAO hj 0)
  have h1 := h_pre_get (opnd C j 1) (opnd_lt hAO hj 1)
  simp only [List.map_cons, List.map_nil, ← h0, ← h1]

lemma wval_gate_and {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) :
    wval C x (n + j) = (wval C x (opnd C j 0) && wval C x (opnd C j 1)) := by
  rw [wval_gate_eval hAO x hj, hop]
  simp [GateOp.eval]

lemma wval_gate_or {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) :
    wval C x (n + j) = (wval C x (opnd C j 0) || wval C x (opnd C j 1)) := by
  rw [wval_gate_eval hAO x hj, hop]
  simp [GateOp.eval]

lemma wval_ge_len {n : ℕ} (C : Circuit) (x : Fin n → Bool) {w : ℕ} (hw : n + C.gates.length ≤ w) :
    wval C x w = false := by
  unfold wval
  have hlen : (C.wires (List.ofFn x)).length ≤ w := by
    rw [wires_length, List.length_ofFn]
    exact hw
  exact List.getD_eq_default _ _ hlen

lemma wval_allTrue {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) :
    ∀ w < n + C.gates.length, wval C (fun _ : Fin n => true) w = true := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw
    by_cases hlt : w < n
    · rw [wval_input C _ w hlt]
    · have hj : w - n < C.gates.length := by omega
      have hwn : w = n + (w - n) := by omega
      rw [hwn]
      have h0 : opnd C (w - n) 0 < w := by
        have := opnd_lt hAO hj 0
        omega
      have h1 : opnd C (w - n) 1 < w := by
        have := opnd_lt hAO hj 1
        omega
      have hv0 := ih (opnd C (w - n) 0) h0 (by omega)
      have hv1 := ih (opnd C (w - n) 1) h1 (by omega)
      rcases hAO.1 (gateAt C (w - n)) (gateAt_mem hj) with hop | hop
      · rw [wval_gate_and hAO _ hj hop, hv0, hv1]; rfl
      · rw [wval_gate_or hAO _ hj hop, hv0, hv1]; rfl

lemma graphFun_iff {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by
  simp [graphFun]

lemma graphFun_unitInput_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n) :
    graphFun G ∅ (unitInput v) = false := by
  cases hf : graphFun G ∅ (unitInput v) with
  | false => rfl
  | true =>
    rw [graphFun_iff] at hf
    rcases hf with ⟨u, w, hadj, hu, hw⟩
    simp only [unitInput, decide_eq_true_eq] at hu hw
    subst hu; subst hw
    exact (G.ne_of_adj hadj rfl).elim

def WireBelowF {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (w : ℕ) : Prop :=
  ∀ x : Fin n → Bool, wval C x w = true → graphFun G ∅ x = true

lemma not_wireBelowF_input {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    {w : ℕ} (hw : w < n) : ¬ WireBelowF G C w := by
  intro h
  have h1 : wval C (unitInput ⟨w, hw⟩) w = true := by
    rw [wval_input C _ w hw]
    simp [unitInput]
  have h2 := h (unitInput ⟨w, hw⟩) h1
  rw [graphFun_unitInput_false] at h2
  cases h2

lemma wireBelowF_gate_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (k : ℕ) :
    WireBelowF G C (n + k) ↔ BelowF G C k := Iff.rfl

lemma core_op_and {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hc : PEqualNP.Core.IsCore G C j) :
    (gateAt C j).op = GateOp.and := by
  rcases hAO.1 _ (gateAt_mem hc.1) with h | h
  · exact h
  · exfalso
    apply hc.2.2.1
    have hj := hc.1
    have hop (b : Fin 2) : PEqualNP.Core.IsImpOperand G C (opnd C j b) := by
      have hb := opnd_lt hAO hc.1 b
      have below : WireBelowF G C (opnd C j b) := by
        intro x hx
        apply hc.2.1.1 x
        change wval C x (n + j) = true
        rw [wval_gate_or hAO x hc.1 h]
        apply Bool.or_eq_true_iff.mpr
        fin_cases b
        · exact Or.inl hx
        · exact Or.inr hx
      have hbn : n ≤ opnd C j b := by
        by_contra hh
        exact not_wireBelowF_input G C (by omega) below
      refine ⟨hbn, ?_, ?_⟩
      · change BelowF G C (opnd C j b - n)
        rw [← wireBelowF_gate_iff, Nat.add_sub_of_le hbn]
        exact below
      · refine ⟨fun _ => true, ?_⟩
        change wval C (fun _ => true) (n + (opnd C j b - n)) = true
        rw [Nat.add_sub_of_le hbn]
        exact wval_allTrue hAO _ (by omega)
    exact ⟨hop 0, hop 1⟩

lemma maximal_core_op_and {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) {j : ℕ}
    (hj : j ∈ PEqualNP.Core.maximalCores G C) :
    (gateAt C j).op = GateOp.and := by
  exact core_op_and hAO ((Finset.mem_filter.mp hj).2.1)

end PEqualNP.Outside.L_meta_2962.CoreStructure

namespace PEqualNP.Outside.L_meta_2962_aux.CoreAndCharge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadK PEqualNP.SplitCount
open PEqualNP.Outside.L_meta_2962_aux.StrictLeaf

def unitVec {n : ℕ} (u v z : Fin n) : List ℕ :=
  [if u = z then 1 else 0, if v = z then 1 else 0]

lemma pure_or_witness {n : ℕ} {C : Circuit} (hC : IsAO2 n C) (u v : Fin n) :
    ∀ w, w < n + C.gates.length →
      (∀ g, g < C.gates.length → Reach n C w (n + g) →
        (gateAt C g).op = GateOp.or) →
      W C n (pairInput u v) w = true →
      ∃ z : Fin n, (z = u ∨ z = v) ∧ W C n (unitInput z) w = true ∧
        unitVec u v z ∈ AV n C 1 [u.val, v.val] w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro hw hOR htrue
  by_cases hn : w < n
  · rw [W_input C n _ w hn] at htrue
    have hz : (⟨w, hn⟩ : Fin n) = u ∨ (⟨w, hn⟩ : Fin n) = v := by
      simpa only [pairInput, decide_eq_true_eq] using htrue
    refine ⟨⟨w, hn⟩, hz, ?_, ?_⟩
    · rw [W_input C n _ w hn]; simp [unitInput]
    · rw [AV_input 1 _ w hn]
      have hmem : w ∈ [u.val, v.val] := by
        rcases hz with hz | hz
        · simp [← hz]
        · simp [← hz]
      simp [leafVectors, hmem, unitVec, Fin.ext_iff]
  · obtain ⟨g, rfl⟩ : ∃ g, w = n + g := ⟨w - n, by omega⟩
    have hg : g < C.gates.length := by omega
    have hop := hOR g hg Relation.ReflTransGen.refl
    rw [W_gate C n _ g hg (hC.2.1 g hg), ao_inputs hC hg, hop] at htrue
    simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
      Bool.or_false, Bool.or_eq_true] at htrue
    obtain ⟨b, hb⟩ : ∃ b : Fin 2, W C n (pairInput u v) (opnd C g b) = true := by
      rcases htrue with h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
    have hlt := opnd_lt hC hg b
    obtain ⟨z, hz, hzu, hzv⟩ := ih _ hlt (by omega)
      (fun i hi hr => hOR i hi (Relation.ReflTransGen.head (step_opnd hC hg b) hr)) hb
    refine ⟨z, hz, ?_, ?_⟩
    · rw [W_gate C n _ g hg (hC.2.1 g hg), ao_inputs hC hg, hop]
      simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
        Bool.or_false, Bool.or_eq_true, id_eq]
      fin_cases b
      · exact Or.inl hzu
      · exact Or.inr hzu
    · apply (gate_vec hC 1 _ hg _).2
      refine Or.inl ⟨hop, ?_⟩
      fin_cases b
      · exact Or.inl hzv
      · exact Or.inr hzv

lemma core_has_and_ancestor {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hC : IsAO2 n C) {j : ℕ} (hc : PEqualNP.Core.IsCore G C j) :
    ∃ g ∈ PEqualNP.Core.coneSet n C j, g ≠ j ∧ (gateAt C g).op = GateOp.and := by
  classical
  by_contra hnone
  push_neg at hnone
  have hj := hc.1
  have hjK : j ∈ PEqualNP.Core.coneSet n C j := Finset.mem_insert_self _ _
  have hjand := PEqualNP.Outside.L_meta_2962.CoreStructure.core_op_and hC hc
  obtain ⟨u, v, huv, hacc, htwice⟩ := hc.2.2.2
  have hor (b : Fin 2) (g : ℕ) (hg : g < C.gates.length)
      (hr : Reach n C (opnd C j b) (n + g)) : (gateAt C g).op = GateOp.or := by
    have hle := reach_le n C hC.2.1 hr
    have hlt := opnd_lt hC hj b
    have hne : g ≠ j := by omega
    have hgK := K_reach hC hj hjK
      (Relation.ReflTransGen.head (step_opnd hC hj b) hr) hg
    rcases ao_op hC hg with h | h
    · exact (hnone g hgK hne h).elim
    · exact h
  have hacc' : W C n (pairInput u v) (opnd C j 0) = true ∧
      W C n (pairInput u v) (opnd C j 1) = true := by
    change W C n (pairInput u v) (n + j) = true at hacc
    rw [W_gate C n _ j hj (hC.2.1 j hj), ao_inputs hC hj, hjand] at hacc
    simpa [GateOp.eval] using hacc
  obtain ⟨z₀, hz₀, ht₀, hv₀⟩ := pure_or_witness hC u v (opnd C j 0)
    (lt_trans (opnd_lt hC hj 0) (Nat.add_lt_add_left hj n)) (hor 0) hacc'.1
  obtain ⟨z₁, hz₁, ht₁, hv₁⟩ := pure_or_witness hC u v (opnd C j 1)
    (lt_trans (opnd_lt hC hj 1) (Nat.add_lt_add_left hj n)) (hor 1) hacc'.2
  have hneq : z₀ ≠ z₁ := by
    intro heq
    subst z₁
    have hroot : gateVal n C j (unitInput z₀) = true := by
      change W C n (unitInput z₀) (n + j) = true
      rw [W_gate C n _ j hj (hC.2.1 j hj), ao_inputs hC hj, hjand]
      simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
        Bool.and_true, Bool.and_eq_true, id_eq]
      exact ⟨ht₀, ht₁⟩
    have hf := hc.2.1.1 _ hroot
    rw [PEqualNP.Outside.L_meta_2962.CoreStructure.graphFun_unitInput_false] at hf
    cases hf
  have hvec : [1, 1] ∈ AV n C 1 [u.val, v.val] (n + j) := by
    apply (gate_vec hC 1 _ hj _).2
    refine Or.inr ⟨hjand, unitVec u v z₀, hv₀, unitVec u v z₁, hv₁, ?_⟩
    have huvne : u ≠ v := G.ne_of_adj huv
    rcases hz₀ with rfl | rfl <;> rcases hz₁ with rfl | rfl
    · exact (hneq rfl).elim
    · simp [unitVec, huvne, Ne.symm huvne, capAdd]
    · simp [unitVec, huvne, Ne.symm huvne, capAdd]
    · exact (hneq rfl).elim
  have hread : readsAtMost (PEqualNP.Core.atGate n C j) n [u.val, v.val] 1 = true := by
    unfold readsAtMost
    rw [List.any_eq_true]
    exact ⟨[1, 1], hvec, by decide⟩
  unfold PEqualNP.Core.ReadTwiceAt at htwice
  rw [hread] at htwice
  cases htwice

lemma core_two_and_gates {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hC : IsAO2 n C) {j : ℕ} (hc : PEqualNP.Core.IsCore G C j) :
    letI : DecidablePred (fun g => (gateAt C g).op = GateOp.and) := Classical.decPred _
    2 ≤ ((PEqualNP.Core.coneSet n C j).filter
      (fun g => (gateAt C g).op = GateOp.and)).card := by
  classical
  obtain ⟨g, hg, hne, hand⟩ := core_has_and_ancestor hC hc
  have hjand := PEqualNP.Outside.L_meta_2962.CoreStructure.core_op_and hC hc
  have hsub : ({g, j} : Finset ℕ) ⊆ (PEqualNP.Core.coneSet n C j).filter
      (fun i => (gateAt C i).op = GateOp.and) := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨hg, hand⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_insert_self _ _, hjand⟩
  have hcard := Finset.card_le_card hsub
  simpa [hne] using hcard

lemma maximal_cores_and_charge {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hC : IsAO2 n C) (hne : (PEqualNP.Core.maximalCores G C).Nonempty) :
    letI : DecidablePred (fun g => (gateAt C g).op = GateOp.and) := Classical.decPred _
    (PEqualNP.Core.maximalCores G C).card + 1 ≤
      (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)).filter
        (fun g => (gateAt C g).op = GateOp.and)).card := by
  classical
  obtain ⟨j, hj⟩ := hne
  have hjcore : PEqualNP.Core.IsCore G C j := (Finset.mem_filter.mp hj).2.1
  obtain ⟨g, hg, hgj, hgand⟩ := core_has_and_ancestor hC hjcore
  have hgn : g ∉ PEqualNP.Core.maximalCores G C := by
    intro hgm
    have hmax : PEqualNP.Core.IsMaximalCore G C g := (Finset.mem_filter.mp hgm).2
    apply hmax.2 j hjcore.1 hjcore
    rcases Finset.mem_insert.mp hg with h | h
    · exact (hgj h).elim
    · exact (Finset.mem_filter.mp h).2
  have hsub : insert g (PEqualNP.Core.maximalCores G C) ⊆
      ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)).filter
        (fun i => (gateAt C i).op = GateOp.and) := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨j, hj, hg⟩, hgand⟩
    · refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_insert_self _ _⟩
      · exact PEqualNP.Outside.L_meta_2962.CoreStructure.maximal_core_op_and hC hi
  have hcard := Finset.card_le_card hsub
  simpa [hgn] using hcard

end PEqualNP.Outside.L_meta_2962_aux.CoreAndCharge
